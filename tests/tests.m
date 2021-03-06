freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: tests.m (functions for testing examples)

   05/26/20: Added a test for the unitary mass formula.
             Changed default value of decomposition to be true.

   05/11/20: Modified the tests to use Orbits for k > 1

   05/08/20: Modified testExample to test for eigenvalues in the same universe
             (so each embedding is checked for carrying all the eigenvalues)

   05/04/20: Fixed a bug when testing over finite coefficient fields 

   04/03/20: renamed from unitary-tests.m
 
 ***************************************************************************/

import "examples.m" : AlgebraicModularFormsExamples;
import "../io/path.m" : path;
import "../neighbors/genus-CN1.m" : OrthogonalMass, UnitaryMass;
import "../neighbors/inv-CN1.m" : Invariant;
import "../lattice_db/nipp_parse.m" : parseNippFile, NippToForm;

forward testExample;
forward testUnitaryMassFormula;
forward testRamaTornaria9;

intrinsic AlgebraicModularFormsTests(: num_primes := 0,
				       use_existing := false,
				       orbits := true,
				       useLLL := true,
				       decomposition := true) ->
	  SeqEnum[ModFrmAlg], SeqEnum
{Run all tests on the examples we have so far. Can limit the number of primes for which Hecke operators are computed by setting num_primes.}

  // Testing the unitary mass formula
  testUnitaryMassFormula();
  // Testing Example 9 from Rama Tornaria - non-lift paramodular form.
  testRamaTornaria9();
  all_spaces := [];
  all_timings := [];
  for example in AlgebraicModularFormsExamples do
      // testing that we obtain the correct results
      M, timings := testExample(example : num_primes := num_primes,
					  use_existing := use_existing,
					  orbits := orbits,
					  useLLL := useLLL,
					  decomposition := decomposition);
      // saving to a file
      fname := Sprintf("Example_%o.dat", example`name);
      Save(M, fname : Overwrite := true);
      // loading from the file and verifying we get the same object
      M2 := AlgebraicModularForms(fname);
      assert M eq M2;
      Append(~all_spaces, M);
      Append(~all_timings, timings);
  end for;

  return all_spaces, all_timings;
end intrinsic;

function testHeckeOperators(M, example, ps, N, useLLL, orbits)
    timings := [];
    for k in [1..#example`evs[1]] do
	Ts_k := [];
	timings_k := [];
	
	for i in [1..N] do
	    p := ps[i];
	    printf "Computing T(p,%o), (N(p) = %o) ...\n", k, Norm(p);
	    t := Cputime();
	    // maybe should restrict Orbits to k eq 1 - ? check why !?
	    Append(~Ts_k, HeckeOperator(M, p, k : BeCareful := false,
						  Estimate := true,
						  UseLLL := useLLL,
						  Orbits := orbits
				       ));
	    timing := Cputime() - t;
	    printf "took %o seconds.\n", timing;
	    Append(~timings_k, timing);
	    if (#example`timing ge i) and (timing ne 0) then
		ratio := example`timing[i] / timing;
		printf "this should take %o times the time.\n", ratio;
	    end if;
	end for;
	print "Done.";

	// Verify that these operators commute with each other.
	assert &and[ A*B eq B*A : A,B in Ts_k ];
	Append(~timings, timings_k);
    end for;
    return timings;
end function;

procedure test_evs(example, evs, keys, N)
    for j in [1..#example`evs] do
	found := false;
	for i in [1..#evs] do
	    ev_calc := [evs[i][keys[idx]] : idx in [1..#keys]];
	    F1 := FieldOfFractions(Universe(ev_calc[1]));
	    if not IsFinite(F1) then
		F1 := AbsoluteField(F1);
		zeta := PrimitiveElement(F1);
	    end if;
	    lens := [Minimum(N, #example`evs[j][k]) : k in keys];
	    ev := [example`evs[j][keys[idx]][1..lens[idx]] :
		   idx in [1..#keys]];
	    ev_calc := [ev_calc[idx][1..lens[idx]] : idx in [1..#keys]];
	    F2 := FieldOfFractions(Universe(ev[1]));
	    
	    if IsFinite(F1) then
		assert IsFinite(F2);
		L := GF(LCM(#F1, #F2));
		if IsPrimeField(F1) then
		    embs := [hom<F1->L|>];
		else
		    roots := [x[1] : x in Roots(MinimalPolynomial(F1.1), L)];
		    embs := [hom<F1 -> L | r> : r in roots];
		end if;
	    else
		assert not IsFinite(F2);
		F2 := AbsoluteField(F2);
		L := CompositeFields(F1, F2)[1];
		if Type(F1) eq FldRat then
		    embs := [hom<F1 -> L | >];
		else
		    roots := [x[1] : x in Roots(MinimalPolynomial(zeta), L)];
		    embs := [hom<F1 -> L | r> : r in roots];
		end if;
	    end if;
	    ev_L := [[L!y : y in x] : x in ev];
	    is_compat := exists(emb){emb : emb in embs |
				     [[emb(y) : y in x] : x in ev_calc] eq
				     ev_L};
	    
	    // we found compatible j, so we can go to the next i
	    if is_compat then
		found := true;
		break;
	    end if;
	end for;
	// There should have been at least one compatible j
	assert found;
    end for;
end procedure;

// !!! TODO: What is the Sturm type bound for this space?
function testDecomposition(M, example, ps, N, useLLL, orbits :
			   sturm_bound := 10)
    
    D := Decomposition(M, sturm_bound : Estimate := true,
					UseLLL := useLLL,
					Orbits := orbits);
    eigenforms := HeckeEigenforms(M);
    evs := [* *];
    RR := RealField();
    timings := [RR | 0 : i in [1..#example`evs[1]]];
    for f in eigenforms do
	if f`IsEigenform then
	    evs_f := [];
	    for dim in [1..#example`evs[1]] do
		t := Cputime();
		Append(~evs_f, HeckeEigensystem(f, dim : Precision := ps[1..N],
							 Estimate := true,
							 UseLLL := useLLL,
							 Orbits := orbits));
		timings[dim] +:= Cputime() - t;
	    end for;
	    Append(~evs, evs_f);
	end if;
    end for;
/*
  evs := [* [HeckeEigensystem(f, dim : prec := ps[N]) :
  dim in [1..#example`evs[1]] :
  f in eigenforms | f`IsEigenform *];
*/
    return eigenforms, evs, timings;
end function;

function testExample(example : num_primes := 0, use_existing := false,
			       orbits := true, useLLL := true,
			       decomposition := true)
    fname := Sprintf("Example_%o.dat", example`name);
    if use_existing and FileExists(path() cat fname) then
	M := AlgebraicModularForms(fname);
    else
	if example`group eq "Unitary" then
	    M := UnitaryModularForms(example`field, example`inner_form,
				     example`weight, example`coeff_char);
	elif example`group eq "Orthogonal" then
	    M := OrthogonalModularForms(example`field, example`inner_form,
					example`weight, example`coeff_char);
	else
	    error "The group type %o is currently not supported!";
	end if;
    end if;
    printf "Testing example of %o\n", M;
    
    printf "Computing genus representatives... ";
    _ := Representatives(Genus(M));
    print "Done.";
    printf "Found %o genus reps.\n\n", #Representatives(Genus(M));

    assert #Representatives(Genus(M)) eq example`genus;

    if num_primes eq 0 then
	N := #example`norm_p;
    else
	N := num_primes;
    end if;
    
    print "Computing T(p) Hecke operators...";
    
    ps := [Factorization(ideal<Integers(BaseRing(M))|n>)[1][1] :
	   n in example`norm_p];
    
    if decomposition then
	eigenforms, evs, timings := testDecomposition(M, example, ps, N,
						      useLLL, orbits :
						      sturm_bound := 10);
	keys := [1..#example`evs[1]];
    else
	timings := testHeckeOperators(M, example, ps, N, useLLL, orbits);
	keys := Keys(M`Hecke`Ts);
	keys := Sort([ x : x in keys ]);
	// Compute eigenforms associated to this space of modular forms.
	eigenforms := HeckeEigenforms(M);
	
	evs := [* [HeckeEigensystem(f, dim) : dim in keys] :
	    f in eigenforms | f`IsEigenform *];  
    end if;

    print "Displaying all Hecke eigensystems...";
    for f in eigenforms do
	print "---------------";
	DisplayHeckeEigensystem(f : Verbose := false);
    end for;

    // Check that the eigenvalues agree with the papers
  
    test_evs(example, evs, keys, N);

    return M, timings;
end function;


procedure testUnitaryMassFormula()
    for d in [1,2,3,7,11] do
	F := QuadraticField(-d);
	M := UnitaryModularForms(F,2);
	reps := Representatives(Genus(M));
	mass := &+[#AutomorphismGroup(r)^(-1) : r in reps];
	assert mass eq UnitaryMass(F,2);
    end for;
end procedure;

procedure testRamaTornaria9()
    A := SymmetricMatrix([1,1/2,1,0,0,1,0,0,0,2,-1/2,-1/2,0,-1/2,3]);
    G := OrthogonalGroup(A);
    W := TrivialRepresentation(GL(5,Rationals()), Rationals());
    level := IdentityMatrix(Rationals(),5);
    M := AlgebraicModularForms(G, W, level);
    D := Decomposition(M, 100);
    eigenforms := HeckeEigenforms(M);
    reps := Representatives(Genus(M));
    weights := [#AutomorphismGroup(rep)^(-1) : rep in reps];
    invs := [Invariant(rep) : rep in reps];
    thetas := [* &+[weights[i]*f`vec[i] *
		    PowerSeriesRing(BaseRing(f`vec))!invs[i]
		  : i in [1..#reps]] : f in eigenforms *];
    assert exists(i){i : i in [1..#thetas] | IsEmpty(Coefficients(thetas[i]))};
    f := eigenforms[i];
    lpolys := LPolynomials(f : Precision := 5);
    lpolys := [lpolys[p] : p in [2,3,5]];
    x := Universe(lpolys).1;
    assert lpolys[1] eq 64*x^4 + 56*x^3 + 24*x^2 + 7*x + 1;
    assert lpolys[2] eq 729*x^4 + 81*x^3 + 3*x^2 + 3*x + 1;
    assert lpolys[3] eq 15625*x^4 - 375*x^3 + 85*x^2 - 3*x + 1;
end procedure;

function my_eval(f, x, y)
  coeffs := [Evaluate(c, x) : c in Eltseq(f)];
  return &+[coeffs[i]*y^(i-1) : i in [1..#coeffs]];
end function;

function my_facAlgExtSqrf(F)
   K<alpha> := BaseRing(F);
   QQ := BaseRing(K); // That should be the rationals, maybe as a number field
   Q_y<y> := PolynomialRing(QQ);
   Q_yx<x> := PolynomialRing(Q_y);
   F_y := Q_yx![Eltseq(c) : c in Eltseq(F)];
   Q_x<x> := PolynomialRing(QQ);
   Q_xy<y> := PolynomialRing(Q_x);
   F_y := my_eval(F_y, y, x);
   mipo := Evaluate(MinimalPolynomial(alpha), y);
   mipo *:= Denominator(mipo);
   shift := 0;
   k := 0;
   count := 0;
   shiftBuf := false;
   f := F_y * Denominator(F_y);
   factors := [];
   tmp := [f];
   repeat
     tmp2 := [];
     for iter in tmp do
       oldF := iter * Denominator(iter);
       if (shift eq 0) then
	 f := oldF;
       else
	 /*
	 coeffs := [Evaluate(c, y-shift*alpha) : c in Eltseq(oldF)];
         f := &+[coeffs[i]*y^(i-1) : i in [1..#coeffs]];
	 */
         // f := my_eval(oldF, alpha, y-shift*alpha);
         f := my_eval(oldF, x-shift*y, y);
         f *:= Denominator(f);
       end if;
       norm := Resultant(mipo, f);
       normFactors := Factorization(norm);
       if (#normFactors ge 1) and (normFactors[1][1] in QQ) then
         normFactors := normFactors[2..#normFactors];
       end if;
       if (#normFactors eq 1) and (normFactors[1][2] eq 1) then
	  Append(~factors, oldF);
          continue;
       end if;
       if #normFactors ge 1 then
         i := normFactors[1];
       end if;
       shiftBuf := false;
       if not ((#normFactors eq 2) and (Degree(i[1]) le Degree(f))) then
         if shift ne 0 then
	   buf := f;
         else
	   buf := oldF;
         end if;
         shiftBuf := true;
       else
         buf := oldF;	   
       end if;
       count := 0;
       for i in normFactors do
	 if shiftBuf then
	   factor := Gcd(buf, i[1]);
         else
	   if shift eq 0 then
      	     factor := Gcd(buf, i[1]);
           else
	     /*
	     coeffs := [Evaluate(c, y+shift*alpha) : c in Eltseq(i[1])];
             ev := &+[coeffs[i]*y^(i-1) : i in [1..#coeffs]];
	     */
	     // factor := Gcd(buf, my_eval(i[1], alpha, y+shift*alpha));
	     factor := Gcd(buf, (i[1])(x+shift*y));
           end if;
	 end if;
         buf div:= factor;
         if shiftBuf then
	   if shift ne 0 then
		    //factor := my_eval(factor, alpha, y+shift*alpha);
	     factor := factor(x+shift*y);
	   end if;
	 end if;
         if (i[2] eq 1) or (Degree(factor) eq 1) then
	   Append(~factors, factor);
         else
           Append(~tmp2, factor);
	 end if;
         if buf in QQ then
	   break;
         end if;
         count +:= 1;
         if ((#normFactors - 1) eq count) then
	   if shiftBuf then
	     if normFactors[#normFactors][2] eq 1 then
			   // Append(~factors, my_eval(buf, alpha, y+shift*alpha));
	       Append(~factors, my_eval(buf, x+shift*y, y));
             else
	       //Append(~tmp2, my_eval(buf, alpha, y+shift*alpha));
	       Append(~tmp2, my_eval(buf, x+shift*y, y));
	     end if;
	   else
	     if normFactors[#normFactors][2] eq 1 then
               Append(~factors, buf);
             else
	       Append(~tmp2, buf);
	     end if;  
	   end if;
           buf := 1;
           break;
	 end if;
       end for;
     end for;
     k +:= 1;
     if (shift eq 0) then
       shift +:= 1;
       k := 1;
     end if;
     if (k eq 2) then
       shift := -shift;
     end if;
     if (k eq 3) then
       shift := -shift;
       shift +:= 1;
       k := 1;
     end if;
     tmp := tmp2;
   until IsEmpty(tmp);
   K_x<x> := Parent(F);
   return [my_eval(f, x, alpha) : f in factors];
end function;

function my_facAlgExt(f)
  res := [];
  sqfree_fac := SquareFreeFactorization(f);
  for fa in sqfree_fac do
    f, a := Explode(fa);
    f_fac := my_facAlgExtSqrf(f);
    res cat:= [<g, a> : g in f_fac];
  end for;
  return res;
end function;

function get_nonlifts(lpolys, disc, prec)
  nonlift_idxs := [];
  for idx in [1..#lpolys] do
    lpolys_f := lpolys[idx];
    // This is sometimes problematic, when the base field is large
    // magma might crash, e.g. disc = 229, genus = 1
    // nonlift := &or[IsIrreducible(lpolys_f[p]) : p in PrimesUpTo(prec)
    //		    | disc mod p ne 0];
    nonlift := false;
    primes := [p : p in PrimesUpTo(prec) | disc mod p ne 0];
    for p in primes do
      if Type(BaseRing(lpolys_f[p])) eq FldRat then
         fac := Factorization(lpolys_f[p]);
      else
         fac := my_facAlgExt(lpolys_f[p]);
      end if;
      is_irred := (#fac eq 1) and (fac[1][2] eq 1);
      nonlift or:= is_irred;
    end for;
    if nonlift then
      Append(~nonlift_idxs, idx);
    end if;
  end for;
  return nonlift_idxs;
end function;

// In order to find out interesting things
// Right now focus on disc le 256
// wt is a pair [k,j] for Paramodular P_{k,j}
procedure get_lpolys(table_idx, nipp_idx, wt : prec := 10, Estimate := false)
  nipp_maxs := [0,256,270,300,322,345,400,440,480,500,513];
  nipp_fname := Sprintf("lattice_db/nipp%o-%o.txt",
			  nipp_maxs[table_idx]+1, nipp_maxs[table_idx+1]);
  nipp := parseNippFile(nipp_fname);
  disc := nipp[nipp_idx]`D;
  g := nipp[nipp_idx]`genus;
  A := NippToForm(nipp[nipp_idx]);
  // G := SpecialOrthogonalGroup(A);
  // std := StandardRepresentation(GL(5, Rationals()));
  k,j := Explode(wt);
//sym_j := SymmetricRepresentation(std, j);
//alt := AlternatingRepresentation(std, 2);
// sym_k_3 := SymmetricRepresentation(alt, k-3);
// W := TensorProduct(sym_j, sym_k_3);
  G := OrthogonalGroup(A);
  W := HighestWeightRepresentation(G,[k+j-3, k-3]); 
// M := AlgebraicModularForms(G, W);
  M := AlgebraicModularForms(G, W);
// D := Decomposition(M, 100);
  fs := HeckeEigenforms(M : Estimate := Estimate);
  lpolys := [LPolynomials(f : Estimate := Estimate,
			  Precision := prec) : f in fs];
  nonlift_idxs := get_nonlifts(lpolys, disc, prec);
  id_str := Sprintf("lpolys_%o_disc_%o_genus_%o_wt_%o_idx_%o.amf",
		  prec, disc, g, wt, nipp_idx);
  if not IsEmpty(nonlift_idxs) then
    nonlift_str := "nonlifts" cat &cat [Sprintf("_%o", i) : i in nonlift_idxs];
  else
    nonlift_str := "";
  end if;
  fname := id_str cat nonlift_str; 
  Save(M, fname);
end procedure;

function my_sum(seq)
  if IsEmpty(seq) then return 0; end if;
  return &+seq;
end function;

// d is a divisor of disc, and we tensor with the corresponding spinor norm
function get_nonlift_dimension(disc, wts)
  nipp_maxs := [0,256,270,300,322,345,400,440,480,500,513];
  assert exists(table_idx){i : i in [1..#nipp_maxs-1] | nipp_maxs[i+1] ge disc};
  nipp_fname := Sprintf("lattice_db/nipp%o-%o.txt",
			  nipp_maxs[table_idx]+1, nipp_maxs[table_idx+1]);
  nipp := parseNippFile(nipp_fname);
  assert exists(nipp_idx){i : i in [1..#nipp] | nipp[i]`D eq disc};
  A := NippToForm(nipp[nipp_idx]);
  G := OrthogonalGroup(A);
  res := [* *];
  for wt in wts do
    k,j := Explode(wt);
    W := HighestWeightRepresentation(G,[k+j-3, k-3]);
    for d in Divisors(disc) do
        spin := SpinorNormRepresentation(G, d);
        W_spin := TensorProduct(W, spin);
        M := AlgebraicModularForms(G, W_spin);
        fs := HeckeEigenforms(M);
        lpolys := [LPolynomials(f : Precision := 10) : f in fs];
        nonlifts := get_nonlifts(lpolys, disc, 10);
// we return the actual orbits, as it might shed more light
// dim := my_sum([Degree(BaseRing(fs[i]`vec)) : i in nonlifts]);
        dim := [Degree(BaseRing(fs[i]`vec)) : i in nonlifts];
        Append(~res, <wt, d, dim>);
    end for;
  end for;
  return res;
end function;

procedure testLSeries(disc, wts, prec)
  nipp_maxs := [0,256,270,300,322,345,400,440,480,500,513];
  assert exists(table_idx){i : i in [1..#nipp_maxs-1] | nipp_maxs[i+1] ge disc};
  nipp_fname := Sprintf("lattice_db/nipp%o-%o.txt",
			  nipp_maxs[table_idx]+1, nipp_maxs[table_idx+1]);
  nipp := parseNippFile(nipp_fname);
  assert exists(nipp_idx){i : i in [1..#nipp] | nipp[i]`D eq disc};
  A := NippToForm(nipp[nipp_idx]);
  G := OrthogonalGroup(A);
  for wt in wts do
    k,j := Explode(wt);
    W := HighestWeightRepresentation(G,[k+j-3, k-3]);
    for d in Divisors(disc) do
        spin := SpinorNormRepresentation(G, d);
        W_spin := TensorProduct(W, spin);
        M := AlgebraicModularForms(G, W_spin);
        fs := HeckeEigenforms(M);
        lpolys := [LPolynomials(f : Precision := 10) : f in fs];
        nonlifts := get_nonlifts(lpolys, disc, 10);
        for idx in nonlifts do
	  f := fs[idx];
          lser := LSeries(f : Precision := prec);
          assert CFENew(lser) eq 0;
	end for;
    end for;
  end for;
end procedure;

function analyticConductor(k, j)
  return (j+7)*(j+9)*(2*k+j+3)*(2*k+j+5)/16;
end function;

function getWeightsByAnalyticConductor(N_an)
  // This is another possiblity
  // max_j := 2*Floor(N_an^(1/4)) - 7;
  // for j in [0..max_j] do
  //end for;
  j := 0;
  // The JL transfer only works for weight ge 3 
  k := 3;
  cur_cond := analyticConductor(k, j);
  res := [];
  while cur_cond le N_an do
    while cur_cond le N_an do
      Append(~res, [k,j]);
      k +:= 1;
      cur_cond := analyticConductor(k, j);
    end while;
    k := 3;
    // We only consider even j
    j +:= 2;
    cur_cond := analyticConductor(k, j);
  end while;
  return res;
end function;

// Should change this, right now only works for small discs (up to 256)
// and slowly
function get_nipp_idx(disc, nipp)
  return [idx : idx in [1..#nipp] | nipp[idx]`D eq disc][1];
end function;

function get_last_nipp_idx(disc, nipp)
  idxs := [idx : idx in [1..#nipp] | nipp[idx]`D eq disc];
  if IsEmpty(idxs) then return 0; end if;
  return idxs[#idxs];
end function;

function get_nipp_table_idx(disc, nipp_maxs)
  table_idx := 1;
  while nipp_maxs[table_idx+1] lt disc do
      table_idx +:= 1;
      if table_idx ge #nipp_maxs then
	 error "This size of lattices is not yet supported!";
      end if;
  end while;
  return table_idx;
end function;

function getBoxByAnalyticConductor(N_an)
  weights := getWeightsByAnalyticConductor(N_an);
  nipp_maxs := [0,256,270,300,322,345,400,440,480,500,513];
  max_max := Floor(N_an / analyticConductor(3, 0));
  num_tables := get_nipp_table_idx(max_max, nipp_maxs);
  nipp_fnames := [Sprintf("lattice_db/nipp%o-%o.txt",
			  nipp_maxs[i]+1, nipp_maxs[i+1])
		     : i in [1..num_tables]];
  nipps := [parseNippFile(fname) : fname in nipp_fnames];
  nipp_lens := [#nipp : nipp in nipps];
  res := [];
  for w in weights do
     max_N := Floor(N_an / analyticConductor(w[1], w[2]));
     // last index with this disc
     table_idx := get_nipp_table_idx(max_N, nipp_maxs);
     nipp := nipps[table_idx];
     max_idx := get_last_nipp_idx(max_N, nipp);
     if max_idx ge 1 then
       Append(~res, <w, table_idx, max_idx>);
     end if;
  end for;
  return res, nipp_lens;
end function;

// This is needed due to unexplained magma crashes
function createBatchFile(tid, idx, k, j)
  fname := Sprintf("batch_files/lpolys_single_%o_%o_%o_%o.m", tid, idx, k, j);
  f := Open(fname, "w");
  output_str := "AttachSpec(\"spec\");\n";
  output_str cat:= "import \"tests/tests.m\" : get_lpolys;\n";
  output_str cat:= "time0 := Cputime();\n";
  output_str cat:= Sprintf("get_lpolys(%o, %o, [%o, %o]);\n", tid, idx, k, j);
  output_str cat:= "printf \"elapsed: %%o\\n\", Cputime()-time0;\n";
  output_str cat:= "exit;\n";
  fprintf f, output_str;
  delete f;
  return fname;
end function;

function get_lpolys_batch(N_an)
  vprintf AlgebraicModularForms, 2:
    "Calculating boxes...";
  boxes, nipp_lens := getBoxByAnalyticConductor(N_an);
  cmds := [];
  vprintf AlgebraicModularForms, 2:
    "Done!\nPreparing batch files....\n";
  for box in boxes do
     k := box[1][1];
     j := box[1][2];
     table_idx := box[2];
     max_idx := box[3];
     vprintf AlgebraicModularForms, 2:
	 "k = %o, j = %o, table_idx = %o, max_idx = %o...\n",
	 k, j, table_idx, max_idx;
     for tid in [1..table_idx] do
       if tid eq table_idx then
	 mid := max_idx;
       else
         mid := nipp_lens[tid];
       end if;
       for idx in [1..mid] do
	 fname := createBatchFile(tid, idx, k, j);
         // magma_cmd := Sprintf("magma -b " cat fname);
         // Append(~cmds, magma_cmd);
         Append(~cmds, fname);
       end for;
	    // we abandon this method due to unexplained magma crashes
	    // cmd := Sprintf("./lpolys_batch.sh 1 %o %o %o", box[2],
	    //	   box[1][1], box[1][2]);
	    //System(cmd);
     end for;
  end for;
  vprintf AlgebraicModularForms, 2: "Done!\n";
  return cmds;
end function;

procedure prepareBatchFile(N_an)
  cmds := get_lpolys_batch(N_an);
  fname := Sprintf("batch_files/lpolys_box_%o.sh", N_an);
  f := Open(fname, "w");
  output_str := "#!/bin/bash\n";
  all_cmds := &cat[ "\"" cat cmd cat "\" \\ \n" : cmd in cmds];  
  output_str cat:= "PROCESSES_TO_RUN=(" cat all_cmds cat ")\n";
  output_str cat:= "for i in ${PROCESSES_TO_RUN[@]}; do\n";
  output_str cat:= "\t magma -b ${i%%/*}/./${i##*/} > ${i}.log 2>&1 &\n";
  output_str cat:= "done\n";
// output_str cat:= "wait\n";
  fprintf f, output_str;
  delete f;
  chmod_cmd := Sprintf("chmod +x %o", fname);
  System(chmod_cmd);
  // we will run it from outside
  // System("./" cat fname);
end procedure;

procedure LaunchCommands(cmds)
  vprintf AlgebraicModularForms, 2:
    "Done! Launching %o commands.", #cmds;
  for cmd in cmds do
    System(cmd);
  end for;
end procedure;

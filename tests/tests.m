freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
                
                                                                            
   FILE: tests.m (functions for testing examples)

   05/26/20: Added a test for the unitary mass formula.
             Changed default value of decomposition to be true.

   05/11/20: Modified the tests to use Orbits for k > 1

   05/08/20: Modified testExample to test for eigenvalues in the same universe
             (so each embedding is checked for carrying all the eigenvalues)

   05/04/20: Fixed a bug when testing over finite coefficient fields 

   04/03/20: renamed from unitary-tests.m
 
 ***************************************************************************/

// Here we list the intrinsics that this file defines
// AlgebraicModularFormsTests() -> SeqEnum, SeqEnum

// imports

import "examples.m" : AlgebraicModularFormsExamples;
import "../io/path.m" : path;
import "../neighbors/genus-CN1.m" : OrthogonalMass, UnitaryMass;
import "../neighbors/inv-CN1.m" : Invariant;
import "../representation/representation.m" : nu;
import "../utils/helper.m" : my_facAlgExt;

forward testExample;
forward testUnitaryMassFormula;
forward testRamaTornaria9;
forward testCMF492aa;
forward testDiscriminant2;
forward testRank8Disc45;
forward testRank4Root3Disc1;

intrinsic AlgebraicModularFormsTests(: NumPrimes := 0,
				       UseExisting := false,
				       Orbits := true,
				       UseLLL := true,
				       Decomposition := true,
				       LowMemory := false ) ->
	  SeqEnum[ModFrmAlg], SeqEnum
{Run all tests on the examples we have so far. Can limit the number of primes for which Hecke operators are computed by setting Num_primes.}

  // Testing the classical modular form 49.2.a.a.
  testCMF492aa();
  // Testing John's question about discriminant 2
  testDiscriminant2();
  // Testing Dan's example of a rank 8 lattice with discriminant 45
  testRank8Disc45();
  // Testing Dan's example of a rank 4 lattice over Q(rt3)
  testRank4Root3Disc1();
  // Testing the unitary mass formula
  testUnitaryMassFormula();
  // Testing Example 9 from Rama Tornaria - non-lift paramodular form.
  testRamaTornaria9();
  all_spaces := [];
  all_timings := [];
  for example in AlgebraicModularFormsExamples do
      // testing that we obtain the correct results
      M, timings := testExample(example : NumPrimes := NumPrimes,
					  UseExisting := UseExisting,
					  Orbits := Orbits,
					  UseLLL := UseLLL,
				          Decomposition := Decomposition,
				          LowMemory := LowMemory);
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

function testHeckeOperators(M, example, ps, N :
			    UseLLL := true, Orbits := true, LowMemory := false)
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
						  UseLLL := UseLLL,
					          Orbits := Orbits,
					          LowMemory := LowMemory
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

function testDecomposition(M, example, ps, N : UseLLL := true,  Orbits := true)
    
    D := Decomposition(M : Estimate := true,
		           UseLLL := UseLLL,
		           Orbits := Orbits);
    eigenforms := HeckeEigenforms(M);
    evs := [* *];
    RR := RealField();
    timings := [[RR | 0 : j in [1..N]]
		   : i in [1..#example`evs[1]]];
    for f in eigenforms do
	if f`IsEigenform then
	    evs_f := [];
	    for dim in [1..#example`evs[1]] do
                for j in [1..N] do
		  t := Cputime();
		  evs_j := HeckeEigensystem(f, dim : Precision := ps[1..j],
							 Estimate := true,
							 UseLLL := UseLLL,
					                 Orbits := Orbits);
		  timings[dim][j] +:= Cputime() - t;
                end for;
		Append(~evs_f, evs_j);
	    end for;
	    Append(~evs, evs_f);
	end if;
    end for;
    return eigenforms, evs, timings;
end function;

function testExample(example : NumPrimes := 0, UseExisting := false,
			       Orbits := true, UseLLL := true,
		               Decomposition := true, LowMemory := false)
    fname := Sprintf("Example_%o.dat", example`name);
    if UseExisting and FileExists(path() cat fname : ShowErrors := false) then
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

    if NumPrimes eq 0 then
	N := #example`norm_p;
    else
	N := NumPrimes;
    end if;
    
    print "Computing T(p) Hecke operators...";
    
    ps := [Factorization(ideal<Integers(BaseRing(M))|n>)[1][1] :
	   n in example`norm_p];
    
    if Decomposition then
        eigenforms, evs, timings := testDecomposition(M, example, ps, N : 
						      UseLLL := UseLLL,
						      Orbits := Orbits);
	keys := [1..#example`evs[1]];
    else
        timings := testHeckeOperators(M, example, ps, N : 
				      UseLLL := UseLLL,
				      Orbits := Orbits,
				      LowMemory := LowMemory);
	keys := Keys(M`Hecke`Ts);
	keys := Sort([ x : x in keys ]);
	// Compute eigenforms associated to this space of modular forms.
	eigenforms := HeckeEigenforms(M);
	
        evs := [* [HeckeEigensystem(f, dim
				    : Precision := ps[1..N]) : dim in keys]
		   : f in eigenforms | f`IsEigenform *];  
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
    A := SymmetricMatrix([2,1,2,0,0,2,0,0,0,4,-1,-1,0,-1,6]);
    G := OrthogonalGroup(A);
    W := TrivialRepresentation(GL(5,Rationals()), Rationals());
    level := IdentityMatrix(Rationals(),5);
    M := AlgebraicModularForms(G, W, level);
    D := Decomposition(M);
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



// Checks which fs are nonlifts using irreduciblity of the lpolynomials
// The number of lpolynomials checked is prec.
// The odds that even one of them is reducible by chance are slim
// But we're doing 2 to make sure.
function get_nonlifts(fs, disc : prec := 2, Estimate := false, Orbits := true,
		      LowMemory := false, ThetaPrec := 25)
  // This is just for checking irreducibility
  primes := [];
  p := 2;
  for i in [1..prec] do  
    while (disc mod p eq 0) do
      p := NextPrime(p);
    end while;
    Append(~primes, p);
    p := NextPrime(p);
  end for;
  lpolys := [LPolynomials(f : Estimate := Estimate,
			  Precision := primes,
			  Orbits := Orbits,
			  LowMemory := LowMemory,
			  ThetaPrec := ThetaPrec) : f in fs];
  nonlift_idxs := [];
  for idx in [1..#lpolys] do
    lpolys_f := lpolys[idx];
    // This is sometimes problematic, when the base field is large
    // magma might crash, e.g. disc = 229, genus = 1
    // nonlift := &or[IsIrreducible(lpolys_f[p]) : p in PrimesUpTo(prec)
    //		    | disc mod p ne 0];
    nonlift := false;
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
procedure get_lpolys(table_idx, nipp_idx, wt : prec := 10, Estimate := false,
		     Orbits := true,
		     LowMemory := false, ThetaPrec := 25)
  A, disc, g := QuinaryQuadraticLattices(table_idx, nipp_idx)[1];
  k,j := Explode(wt);
  G := OrthogonalGroup(A);
  W := HighestWeightRepresentation(G,[k+j-3, k-3]); 
  M := AlgebraicModularForms(G, W);
  fs := HeckeEigenforms(M : Estimate := Estimate);
  nonlift_idxs := get_nonlifts(fs, disc : Estimate := Estimate, Orbits := Orbits,
			       LowMemory := LowMemory, ThetaPrec := ThetaPrec);
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

// d is a divisor of disc, and we tensor with the corresponding spinor norm
function get_nonlift_dimension(disc, wts)
  A := QuinaryQuadraticLattices(disc)[1][1];
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
        nonlifts := get_nonlifts(fs, disc);
        dim := [Degree(BaseRing(fs[i]`vec)) : i in nonlifts];
        Append(~res, <wt, d, dim>);
    end for;
  end for;
  return res;
end function;

procedure testLSeries(disc, wts, prec : Orbits := true,
		      LowMemory := false, ThetaPrec := 25)
  A := QuinaryQuadraticLattices(disc)[1][1];
  G := OrthogonalGroup(A);
  for wt in wts do
    k,j := Explode(wt);
    W := HighestWeightRepresentation(G,[k+j-3, k-3]);
    for d in Divisors(disc) do
        spin := SpinorNormRepresentation(G, d);
        W_spin := TensorProduct(W, spin);
        M := AlgebraicModularForms(G, W_spin);
        fs := HeckeEigenforms(M : Orbits := Orbits,
			      LowMemory := LowMemory, ThetaPrec := ThetaPrec);
        nonlifts := get_nonlifts(fs, disc : Orbits := Orbits,
				 LowMemory := LowMemory,
			 ThetaPrec := ThetaPrec);
        printf "For wt = %o, d = %o there are %o nonlifts. The dimensions of their Galois orbits are %o.\n", wt, d, #nonlifts, [Degree(BaseRing(fs[idx]`vec)) : idx in nonlifts]; 
        for idx in nonlifts do
	  f := fs[idx];
          lser := LSeries(f : Precision := prec,
		Orbits := Orbits, LowMemory := LowMemory,
		ThetaPrec := ThetaPrec);
          assert CFENew(lser) eq 0;
	end for;
    end for;
  end for;
end procedure;

procedure testRamaTornariaTable3ANTS()
  ps := [5,61];
  disc := &*ps;
  divs := Divisors(disc);
  dims := [[[8,9,13],[],[1],[1,1,8,13]],[[1,1,1,1,3,6,8,13],[1,1],[1],[8,13]]];
  kers := [{1},{2,3,4,5,7}];
  traces := [[[[1,-21,12,-28,-10],
	     [57,119,69,505,1338],
	     [73,129,455,647,1660]],
	    [],
	    [[-4,-12,-4,9,-13]],
	    [[-2,2,-2,-19,21],
	     [2,-6,10,-3,29],
	     [3,-27,-6,-58,-54],
	     [81,157,325,669,1652]]],
	   [[[2,14,25,62,164],
	     [-7,-3,28,-9,-4],
	     [-2,2,-2,-19,21],
	     [2,-6,10,-3,29],
	     [-10,12,-20,-3,239],
	     [29,59,314,309,612],
	     [3,-27,-6,-58,-54],
	     [81,157,325,669,1652]],
	    [[-7,-3,-22,-9,-4],
	     [-4,-12,-4,9,-13]],
	    [[-6,-4,-20,13,-23]],			   
	    [[1,-21,12,-28,-10],
	     [73,129,455,647,1660]]]
	   ];
			     
  genera := QuinaryQuadraticLattices(disc);
  for lat_idx in [1,2] do
    vprintf AlgebraicModularForms, 1 : "testing lattice no. %o...\n", lat_idx;
    A := genera[lat_idx][1];
    G := OrthogonalGroup(A);
    for div_idx in [1..#divs] do
      d := divs[div_idx];
      vprintf AlgebraicModularForms, 1 : "testing d = %o...\n", d;
      vprintf AlgebraicModularForms, 1 : "checking dimensions...\n";
      spin := SpinorNormRepresentation(G, d);
      M := AlgebraicModularForms(G, spin);
      fs := HeckeEigenforms(M);
      if (d eq 1) then 
        cusps := [f : f in fs | not f`IsEisenstein];
      else
        cusps := fs;
      end if;
      f_dims := [Degree(BaseRing(f`vec)) : f in cusps];
      assert f_dims eq dims[lat_idx][div_idx];
      if d eq 1 then
        vprintf AlgebraicModularForms, 1 : "checking ker(theta)...\n";
        reps := Representatives(Genus(M));
        weights := [#AutomorphismGroup(rep)^(-1) : rep in reps];
        invs := [Invariant(rep) : rep in reps];
        thetas := [* &+[weights[i]*f`vec[i] *
		    PowerSeriesRing(BaseRing(f`vec))!invs[i]
		  : i in [1..#reps]] : f in cusps *];
        ker := {i : i in [1..#thetas] | IsEmpty(Coefficients(thetas[i]))};
        assert ker eq kers[lat_idx];
      end if;
      vprintf AlgebraicModularForms, 1 : "checking traces...\n";
      for dim in Set(f_dims) do
	 dim_idxs := [idx : idx in [1..#cusps] | f_dims[idx] eq dim];
         dim_traces := Set([]);
         for f_idx in dim_idxs do
	  f := cusps[f_idx];
	  evs, primes := HeckeEigensystem(f,1 : Precision := 11);
          bad_primes := [i : i in [1..#primes] | Norm(primes[i]) in ps];
          for idx in bad_primes do
	    evs[idx] +:= 1;
            if (d mod Norm(primes[idx]) eq 0) then
	      // eps_p := WittInvariant(Module(M), primes[idx]);
              evs[idx] *:= nu(disc, Norm(primes[idx]));
            end if;
          end for;
          tr_evs := [Trace(ev) : ev in evs];
          Include(~dim_traces, tr_evs);
        end for;
        tr_idxs := [idx : idx in [1..#dims[lat_idx][div_idx]]
			| dims[lat_idx][div_idx][idx] eq dim];
        dim_tr_test := Set([traces[lat_idx][div_idx][idx] : idx in tr_idxs]);
        assert dim_traces eq dim_tr_test;
     end for;
    end for;
  end for;
end procedure;

procedure testRamaTornariaTable1ANTS()
  traces_1 := [-8,-10,-4,-14,-22,-4,-47,-12,41,50,-504,-102,174,30,42,156,-252,472,106,-481,-744,927,-632,-297,2,-992,-1222,1436,-954,19,516,-258, 1080, 1030, -974, -1119, 1152, 108, -2707, -182, 2568, -2804, -3035, 583, 2276, 6754, 360, 3569, -3346, 2220, -2780, -3878, -819, 6112, -5343, -808, 3592, 2954, -8334, -2942, 6360, -856, 3548, -6322, -9443, 108, 1596, -2129, 1856, 480, 1704, 4601, 6298, -4998, 7706, -18293, 5316, 4324, -4679, -3476, -910, 3552, -4878, 15213, -6909, -7130, 12908, -4005, -7334, -77, 12248, 6447, -14197, 1960, 3288];

  traces_2 := [10,11,-44,-9,-67,-158,260,41,-198,-187,2744,-730,800,442,-5052];

  disc := 167;
  A := QuinaryQuadraticLattices(disc)[1][1];
  G := OrthogonalGroup(A);
  d := 167;
  spin := SpinorNormRepresentation(G, d);
  M := AlgebraicModularForms(G, spin);
  fs := HeckeEigenforms(M);
  assert #fs eq 1;
  f := fs[1];
  evs1 := HeckeEigensystem(f, 1 : Precision := 500);
  evs2 := HeckeEigensystem(f, 2 : Precision := 50);
  assert traces_1 eq evs1;
  assert traces_2 eq evs2;
  lser := LSeries(f : Precision := 30);
  assert CFENew(lser) lt 10^(-30);
end procedure;

procedure testCMF492aa()
  Q := SymmetricMatrix([6,1,6,1,-1,20]);
  G := OrthogonalGroup(Q);
  L := IdentityMatrix(Rationals(),3);
  M := AlgebraicModularForms(G, HighestWeightRepresentation(G,[0]), L);
  fs := HeckeEigenforms(M);
  f := fs[2];
  evs := HeckeEigensystem(f, 1 : Precision := 100);
  cfs := [Coefficient(qExpansion(CuspForms(49).1,100),p) : p in PrimesUpTo(100)];
  assert evs eq cfs;
end procedure;

procedure testDiscriminant2()
  T := Matrix([[2,0,0,0,1],[0,2,0,0,1],[0,0,2,1,1],[0,0,1,2,0],[1,1,1,0,2]]);
  L := LatticeWithGram(T);
  Lambda := LatticeFromLat(L);
  assert Discriminant(Lambda) eq FractionalIdeal(2);
  assert Norm(Discriminant(Lambda)) eq 2;
end procedure;

procedure testRank8Disc45()
  mat := [ 2, 1, -1, -1, 1, -1, -1, -1, 1, 2, -1, -1, 1, -1, 0, 0, -1,
-1, 2, 1, -1, 1, 1, 1, -1, -1, 1, 2, -1, 1, 1, 1, 1, 1, -1, -1, 2, -1,
-1, -1, -1, -1, 1, 1, -1, 2, 1, 1, -1, 0, 1, 1, -1, 1, 4, 1, -1, 0, 1,
1, -1, 1, 1, 4 ];
  Q := Matrix(Rationals(),8,8, mat);
  G := OrthogonalGroup(Q);
  W := HighestWeightRepresentation(G, [0]);
  L := IdentityMatrix(Rationals(),8);
  M := AlgebraicModularForms(G, W, L);
  assert Dimension(M) eq 4;
end procedure;

procedure testRank4Root3Disc1()
  K<rt3>:=QuadraticField(3);
  mat:=[2,rt3,rt3,2];
  Q:=DiagonalJoin(Matrix(K,2,2,mat),Matrix(K,2,2,mat));
  L:=IdentityMatrix(K,#Rows(Q));
  G:=OrthogonalGroup(Q);
  W:=HighestWeightRepresentation(G,[0,0,0,0]);
  M:=AlgebraicModularForms(G,W,L:GramFactor:=2);
  E:=HeckeEigenforms(M);
  pol:=LPolynomial(E[1],Factorization(2*Integers(K))[1][1],#Rows(Q));
  _<x> := Parent(pol);
  assert pol eq 16*x^4 - 36*x^3 + 28*x^2 - 9*x + 1;
end procedure;

procedure testRank8Root3Disc1()
  K<rt3>:=QuadraticField(3);
  mat:=Matrix(K,2,2,[2,rt3,rt3,2]);
  Q := DirectSum([mat : i in [1..4]]);
  L:=IdentityMatrix(K,#Rows(Q));
  G:=OrthogonalGroup(Q);
  W:=HighestWeightRepresentation(G,[0,0,0,0]);
  M:=AlgebraicModularForms(G,W,L:GramFactor:=2);
  E:=HeckeEigenforms(M);
  pol:=LPolynomial(E[1],Factorization(2*Integers(K))[1][1],#Rows(Q));
  _<x> := Parent(pol);
end procedure;

// !! TODO - add tests for SetGenus and SetAutomorphismGroups






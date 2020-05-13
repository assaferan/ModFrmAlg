freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: tests.m (functions for testing examples)

   05/11/20: Modified the tests to use Orbits for k > 1

   05/08/20: Modified testExample to test for eigenvalues in the same universe
             (so each embedding is checked for carrying all the eigenvalues)

   05/04/20: Fixed a bug when testing over finite coefficient fields 

   04/03/20: renamed from unitary-tests.m
 
 ***************************************************************************/

import "examples.m" : AlgebraicModularFormsExamples;
import "../io/path.m" : path;

forward testExample;

intrinsic AlgebraicModularFormsTests(: num_primes := 0,
				       use_existing := false,
				       orbits := true,
				       useLLL := true,
				       decomposition := false) ->
	  SeqEnum[ModFrmAlg], SeqEnum
{Run all tests on the examples we have so far. Can limit the number of primes for which Hecke operators are computed by setting num_primes.}

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
    
    D := Decomposition(M, sturm_bound : estimate := true,
					useLLL := useLLL,
					orbits := orbits);
    eigenforms := HeckeEigenforms(M);
    evs := [* *];
    RR := RealField();
    timings := [RR | 0 : i in [1..#example`evs[1]]];
    for f in eigenforms do
	if f`IsEigenform then
	    evs_f := [];
	    for dim in [1..#example`evs[1]] do
		t := Cputime();
		Append(~evs_f, HeckeEigensystem(f, dim : prec := ps[1..N],
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
			       decomposition := false)
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
    
    printf "Computing T(p) Hecke operators... ";
    
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

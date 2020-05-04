freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: tests.m (functions for testing examples)

   04/03/20: renamed from unitary-tests.m
 
 ***************************************************************************/

import "examples.m" : AlgebraicModularFormsExamples;
import "../io/path.m" : path;

forward testExample;

intrinsic AlgebraicModularFormsTests(: num_primes := 0,
				       use_existing := false) -> ModFrmAlg
{Run all tests on the examples we have so far. Can limit the number of primes for which Hecke operators are computed by setting num_primes.}

  for example in AlgebraicModularFormsExamples do
      // testing that we obtain the correct results
      M := testExample(example : num_primes := num_primes,
				 use_existing := use_existing);
      // saving to a file
      fname := Sprintf("Example_%o.dat", example`name);
      Save(M, fname : Overwrite := true);
      // loading from the file and verifying we get the same object
      M2 := AlgebraicModularForms(fname);
      assert M eq M2;
  end for;

  return M;
end intrinsic;

function testExample(example : num_primes := 0, use_existing := false)
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

    for k in [1..#example`evs[1]] do
	Ts_k := [];
    
	for i in [1..N] do
	    p := ps[i];
	    printf "Computing T(p,%o), (N(p) = %o) ...\n", k, Norm(p);
	    t := Cputime();
	    Append(~Ts_k, HeckeOperator(M, p, k : BeCareful := false,
						  Estimate := true,
						  UseLLL := true,
						  Orbits := (k eq 1)));
	    timing := Cputime() - t;
	    printf "took %o seconds.\n", timing;
	    if (#example`timing ge i) and (timing ne 0) then
		ratio := example`timing[i] / timing;
		printf "this should take %o times the time.\n", ratio;
	    end if;
	end for;
	print "Done.";

	// Verify that these operators commute with each other.
	assert &and[ A*B eq B*A : A,B in Ts_k ];
    end for;

    // Compute eigenforms associated to this space of modular forms.
    eigenforms := HeckeEigenforms(M);

    print "Displaying all Hecke eigensystems...";
    for f in eigenforms do
	print "---------------";
	DisplayHeckeEigensystem(f : Verbose := false);
    end for;

    // Check that it agrees with John and Matthew's paper
    keys := Keys(M`Hecke`Ts);
    keys := Sort([ x : x in keys ]);

    evs := [[HeckeEigensystem(f, dim) : dim in keys] :
	    f in eigenforms | f`IsEigenform];  

    for i in [1..#example`evs] do
	for k in keys do
	    len := Minimum(N, #example`evs[i][k]); 
	    ev_calc := evs[i][k][1..len];
	    ev := example`evs[i][k][1..len];
	    
	    // the field of definition might be different,
	    // so we check if there is some embedding under which
	    // all the eigenvalues coincide
	    
	    F1 := FieldOfFractions(Parent(ev_calc[1]));
	    assert &and[IsIsomorphic(F1, FieldOfFractions(Parent(x))) :
		    x in ev_calc];
	    F2 := FieldOfFractions(Parent(ev[1]));
	    if IsFinite(F1) then
		assert IsFinite(F2);
		L := GF(LCM(#F1, #F2));
		embs := [hom<F1->L|>];
	    else
		assert not IsFinite(F2);
		F1 := AbsoluteField(F1);
		F2 := AbsoluteField(F2);
		L := Compositum(F1, F2);
		if Type(F1) eq FldRat then
		    embs := [hom<F1 -> L | >];
		else
		    zeta := PrimitiveElement(F1);
		    roots := [x[1] : x in Roots(MinimalPolynomial(zeta), L)];
		    embs := [hom<F1 -> L | r> : r in roots];
		end if;
	    end if;

	    // This is what we wanted to do, but because different
	    // eigenvalues have different parents, we can't
	    /*
	    assert exists(emb){emb : emb in embs |
			       [emb(x) : x in ev_calc] eq [x : x in ev]};
	   */
	    assert &and[exists(emb) {emb : emb in embs |
				     emb(ev_calc[i]) eq ev[i]} : i in [1..N]];
	end for;
    end for;

    return M;
end function;

//freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: tests.m (functions for testing examples)

   04/03/20: renamed from unitary-tests.m
 
 ***************************************************************************/

import "examples.m" : Example_7_2,
       Example_7_3,
       Example_7_4,
       Example_7_4_W_2_0,
       Example_7_4_W_2_2,
       Example_7_4_W_3_1,
       Example_7_4_W_3_3,
       Example_7_4_W_4_0,
       Example_7_5,
       Example_7_6;

forward testExample;

intrinsic ModularFormTests() -> ModFrmAlg
{.}
  M := [];
  // we're cutting down the number of primes until we have
// a more efficient implementation
  // ??? Maybe move this construction to examples.m and assign names to
  // examples (in the record structure)
  examples := [ Example_7_2,
		Example_7_3,
		Example_7_4,
		Example_7_4_W_2_0,
		Example_7_4_W_2_2,
		Example_7_4_W_3_1,
		Example_7_4_W_3_3,
		Example_7_4_W_4_0,
		Example_7_5,
		Example_7_6];

  for example in examples do
      Append(~M, testExample(example : num_primes := 3));
  end for;

  return M;
end intrinsic;

function testExample(example : num_primes := 0)
    if example`group eq "Unitary" then
	M := UnitaryModularForms(example`field, example`inner_form,
				 example`weight, example`coeff_char);
    elif example`group eq "Orthogonal" then
	M := OrthogonalModularForms(example`field, example`inner_form,
				    example`weight, example`coeff_char);
    else
	error "The group type %o is currently not supported!";
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
				       Orbits := (k eq 1)));
	    timing := Cputime() - t;
	    printf "took %o seconds.\n", timing;
	    if (#example`timing ge i) then
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

    evs := [[HeckeEigensystem(f, dim) : dim in keys] : f in eigenforms];  

    for i in [1..#evs] do
	for k in keys do
	    ev_calc := evs[i][k];
	    ev := example`evs[i][k][1..N];
	    // the field of definition might be different,
	    // so we check if there is some embedding under which
	    // all the eigenvalues coincide
	    F := AbsoluteField(Parent(ev_calc[1]));
	    L := Compositum(AbsoluteField(FieldOfFractions(Parent(ev[1]))), F);
	    zeta := PrimitiveElement(F);
	    roots := [x[1] : x in Roots(MinimalPolynomial(zeta), L)];
	    embs := [hom<Parent(ev_calc[1]) -> L | r> : r in roots];
	    assert exists(emb){emb : emb in embs |
			       [emb(x) : x in ev_calc] eq [x : x in ev]};
	end for;
    end for;

    return M;
end function;

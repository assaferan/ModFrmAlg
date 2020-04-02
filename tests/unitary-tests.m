//freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: unitary-tests.m (functions for testing examples)

   04/02/20: Replaced the construction in the test by the new
             UnitaryModularForms constructor.

   03/26/20: added documentation

   03/26/20: fixed the testing of eigenvalues to handle the case when 
             the fields of definition are different.

   03/26/20: added the example for weight (3,3)

   03/22/20: Added weights to the testing

   03/21/20: Changed testUnitaryExample to be a local procedure,
             and wrote UnitaryModularFormTests to run all examples.

   03/16/20: Added timing data into the testing.

 
 ***************************************************************************/

import "unitary-examples.m" :
			    UnitaryExample_7_2,
       UnitaryExample_7_2_W_2_0,
       UnitaryExample_7_2_W_2_2,
       UnitaryExample_7_2_W_3_1,
       UnitaryExample_7_2_W_3_3,
       UnitaryExample_7_2_W_4_0,
       UnitaryExample_7_3,
       UnitaryExample_7_4;

forward testUnitaryExample;

intrinsic UnitaryModularFormTests() -> ModFrmAlg
{.}
  M := [];
  // we're cutting down the number of primes until we have
// a more efficient implementation

  testUnitaryExample(~M, UnitaryExample_7_2 : num_primes := 3);
  testUnitaryExample(~M, UnitaryExample_7_2_W_2_0 : num_primes := 3);
  testUnitaryExample(~M, UnitaryExample_7_2_W_2_2 : num_primes := 3);
  testUnitaryExample(~M, UnitaryExample_7_2_W_3_1 : num_primes := 3);
  testUnitaryExample(~M, UnitaryExample_7_2_W_3_3 : num_primes := 3);
  testUnitaryExample(~M, UnitaryExample_7_2_W_4_0 : num_primes := 3);
  testUnitaryExample(~M, UnitaryExample_7_4 : num_primes := 3);

  return M;
end intrinsic;

procedure testUnitaryExample(~answers, example : num_primes := 0) 
    M := UnitaryModularForms(example`field, 3,
                             example`weight, example`coeff_char);
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
    Ts1 := [];
    
    for i in [1..N] do
	p := ps[i];
	printf "Computing T(p), (N(p) = %o) ...\n", Norm(p);
	t := Cputime();
	Append(~Ts1, HeckeOperator(M, p : BeCareful := false));
	timing := Cputime() - t;
	printf "took %o seconds.\n", timing;
	if (#example`timing ge i) then
	    ratio := example`timing[i] / timing;
	    printf "this should take %o times the time.\n", ratio;
	end if;
    end for;
    print "Done.";

    // Verify that these operators commute with each other.
    assert &and[ A*B eq B*A : A,B in Ts1 ];

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
	ev_calc := evs[i][1];
	ev := example`evs[i][1..N];
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
//    assert evs eq [[ev[1..N]] : ev in example`evs];

    Append(~answers, M);
    
    print "\nYou can save the data we just computed using the Save intrinsic.";
    printf "\tFor example -->\tSave(M[%o], \"savefile\")\n", #answers;
    
    print "You can then load this data from disk using the Load intrinsic.";
    print "\tFor example -->\tM := Load(\"savefile\");";
    
end procedure;

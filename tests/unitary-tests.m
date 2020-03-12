// testing an example as in unitary-examples.m

import "unitary-examples.m" : UnitaryExample_7_2, UnitaryExample_7_4;

intrinsic UnitaryModularFormTests()
{.}
  // we're cutting down the number of primes until we have
  // a more efficient implementation
  testUnitaryExample(UnitaryExample_7_2);
  testUnitaryExample(UnitaryExample_7_4);
end intrinsic;

intrinsic testUnitaryExample(example::Rec : num_primes := 0)
{.}
    K := example`field;
    innerForm := IdentityMatrix(K,3);
    M := UnitaryModularForms(innerForm);
    
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
	ratio := example`timing[i] / timing;
	printf "this should take %o times the time.\n", ratio;
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

    assert evs eq [[example`a[1..N]],[example`b[1..N]]];

    print "\nYou can save the data we just computed using the Save intrinsic.";
    print "\tFor example -->\tSave(M, \"savefile\");\n";
    print "You can then load this data from disk using the Load intrinsic.";
    print "\tFor example -->\tM := Load(\"savefile\");";

end intrinsic;

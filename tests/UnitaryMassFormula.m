procedure testUnitaryMassFormula()
    printf "Testing the unitary mass formula for rank 2 and d=";
    for d in [1,2,3,7,11] do
	printf "%o ", d;
	F := QuadraticField(-d);
	M := UnitaryModularForms(F,2);
	reps := Representatives(Genus(M));
	mass := &+[#AutomorphismGroup(r)^(-1) : r in reps];
	assert mass eq UnitaryMass(F,2);
    end for;
end procedure;

testUnitaryMassFormula();

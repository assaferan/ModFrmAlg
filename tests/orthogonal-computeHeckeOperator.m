SetDebugOnError(true);
SetHelpUseExternalBrowser(false);

// Attach the appropriate specification file.
AttachSpec("spec");

// This is hardly the right thing to do,
// but I still don't know how to construct O_{n} as a group of Lie type (!?)
// Instead, we just construct a non-semisimple group of type "B1",
// using the fact that the code just checks for semisimplicity at the moment.

O5 := GroupOfLieType("B2 T1", Rationals());

// Construct an inner form with discriminant 61.
innerForm := Matrix([
	[ 4,-1,1,-1,2 ],
	[ -1,6,-1,0,-2 ],
	[ 1,-1,2,-2,1 ],
	[ -1,0,-2,6,3 ],
	[ 2,-2,1,3,6 ] ]);

// Construct the space of algebraic modular forms associated to the standard
//  lattice with respect to the quadratic space with the specified inner form.
M := AlgebraicModularForms(O5, innerForm);

// Compute the genus representatives for M. We don't really need to do this,
//  since this will automatically get called if we try to compute Hecke
//  operators.
printf "Computing genus representatives... ";
_ := Representatives(Genus(M));
print "Done.";
printf "Found %o genus reps.\n\n", #Representatives(Genus(M));

// Compute T(2), T(3), and T(5) Hecke operators.
printf "Computing T(p) Hecke operators... ";
Ts1 := [ HeckeOperator(M, p : BeCareful := false) : p in PrimesUpTo(5) ];
print "Done.";

// Verify that these operators commute with each other.
assert &and[ A*B eq B*A : A,B in Ts1 ];

// Compute T(2^2), T(3^2), and T(5^2) Hecke operators.
printf "Computing T(p^2) Hecke operators... ";
Ts2 := [ HeckeOperator(M, p, 2 : BeCareful := false) : p in PrimesUpTo(5) ];
print "Done.\n";

// Verify that these operators also commute with each other.
assert &and[ A*B eq B*A : A,B in Ts2 ];

// Compute eigenforms associated to this space of modular forms.
eigenforms := HeckeEigenforms(M);
print "Displaying all Hecke eigensystems...";
for f in eigenforms do
	print "---------------";
	DisplayHeckeEigensystem(f : Verbose := false);
end for;

print "\nYou can save the data we just computed using the Save intrinsic.";
print "\tFor example -->\tSave(M, \"savefile\");\n";
print "You can then load this data from disk using the Load intrinsic.";
print "\tFor example -->\tM := Load(\"savefile\");";


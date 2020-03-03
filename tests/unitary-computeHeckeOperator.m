// Attach the appropriate specification file.
AttachSpec("spec");

// This is hardly the right thing to do,
// but I still don't know how to construct U_{n} as a group of Lie type (!?)
// Instead, we just construct SU_3,
// using the fact that the code at the moment does the same for both.
RSU3 := TwistedRootDatum("A2" : Twist := 2);

// This is Example 7.4 from Matthew and John's paper
K := CyclotomicField(7);
gal := AutomorphismGroup(K);
_ := exists(g){g : g in gal | Order(g) eq 2};
alpha := FieldAutomorphism(K, g);
F := FixedField(alpha);

SU3 := TwistedGroupOfLieType(RSU3, F, K);

innerForm := IdentityMatrix(K,3);

// Construct the space of algebraic modular forms associated to the standard
//  lattice with respect to the quadratic space with the specified inner form.
M := AlgebraicModularForms(SU3, innerForm);

// Compute the genus representatives for M. We don't really need to do this,
//  since this will automatically get called if we try to compute Hecke
//  operators.
printf "Computing genus representatives... ";
_ := Representatives(Genus(M));
print "Done.";
printf "Found %o genus reps.\n\n", #Representatives(Genus(M));

// Compute T(2), T(3), and T(5) Hecke operators.
printf "Computing T(p) Hecke operators... ";
norm_ps := [29, 43, 71, 113, 127, 197, 211, 239, 281];
ps := [Factorization(ideal<Integers(BaseRing(M))|n>)[1][1] : n in norm_ps];
Ts1 := [];
for p in ps do
  printf "Computing T(%o), (N(%o) = %o) ...\n", p, p, Norm(p);
  t := Cputime();
  Append(~Ts1, HeckeOperator(M, p : BeCareful := false));
  printf "took %o seconds.\n", Cputime() - t;
end for;
print "Done.";

// Verify that these operators commute with each other.
assert &and[ A*B eq B*A : A,B in Ts1 ];

// This part (Hecke operators at p^2) is not yet implemented

/*
// Compute T(2^2), T(3^2), and T(5^2) Hecke operators.
printf "Computing T(p^2) Hecke operators... ";
Ts2 := [ HeckeOperator(M, p, 2 : BeCareful := false) : p in PrimesUpTo(5) ];
print "Done.\n";

// Verify that these operators also commute with each other.
assert &and[ A*B eq B*A : A,B in Ts2 ];

*/

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


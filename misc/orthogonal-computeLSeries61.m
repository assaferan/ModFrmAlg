// This script load precompuated data from a file, computes the Euler factors,
//  computes Dirichlet cofficients, and L-series.

AttachSpec("spec");

// Load a 5-variable quadratic form with discriminant 61 from disk.
M := Load("O5/5-61");

// Display the inner form for this space.
printf "Inner form of discriminant %o\n", Norm(Discriminant(M`L));
GramMatrix(M`genus`Representative);
print "";

// Retrieves a special Hecke eigenform which belongs in the kernel of the
//  theta series map.
f := ThetaKernel(M)[1];

// The appropriate polynomial ring.
Z<x> := PolynomialRing(BaseRing(f`vec));

// Display the Euler factors.
print "Euler factors:";
for p in PrimesUpTo(31) do
	printf "\tL_%o(x) -->\t%o\n", p, Polynomial(EulerFactor(f, p));
end for;

// Computes and displays as many Dirichlet coefficients as possible.
dirichlet := DirichletCoefficients(f);
printf "\nThe first %o Dirichlet coefficients of the L-series associated to this form:\n",
	#dirichlet;
dirichlet;

// Compute the L-series associated to this eigenform.
L := LSeries(f);
printf "\nCheckFunctionalEquation(L) = %o\n", CheckFunctionalEquation(L);


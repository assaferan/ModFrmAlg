// This is Example 4.11 from the paper, a continuation of Example 3.3
Q := SymmetricMatrix([6,0,2,-4,-1,12,3,1,6,12]);
M := OrthogonalModularForms(Q);
Dimension(M);
/*
9
*/
#Representatives(Genus(M));
/*
9
*/
T2 := HeckeOperator(M,2);
T2;
/*
[0 0 2 0 1 1 0 0 0]
[0 3 0 1 1 0 0 0 0]
[3 0 1 1 0 0 0 0 1]
[0 3 2 2 2 2 1 0 0]
[3 3 0 2 2 0 0 1 1]
[3 0 0 2 0 2 2 0 1]
[0 0 0 1 0 2 3 1 1]
[0 0 0 0 1 0 1 5 1]
[0 0 4 0 2 2 2 2 4]
*/
// computing the eigenforms
vs := HeckeEigenforms(M);
// Note that theline above computes the Galois orbits, so we have 3 forms
#vs;
/*
3
*/

// This character will be useful here
chi := KroneckerCharacter(193);

// verifying that the first eigenvector is the Eisenstein eigenvector
// with eigenvalues 1 + p + p^2 + chi(p)*p
assert &and[HeckeEigenvalue(vs[1],p) eq 1 + p + p^2 + chi(p)*p : p in PrimesUpTo(20)];

// and L-polynomial (1-chi(p)*p^(1-s))*(1-p^(-s))*(1-p^(1-s))*(1-p^(2-s))
assert &and[LPolynomial(vs[1],p) eq (1-x)*(1-p*x)*(1-p^2*x)*(chi(p)-p*x) : p in PrimesUpTo(20)];

// This is the form with LMFDB label 193.2.b.a
f := Newforms(ModularForms(chi))[1][1];

// we first fix an embedding to identify the fields of definition
L := Parent(Coefficient(f,1));
K<alpha> := Parent(HeckeEigenvalue(vs[3],2));
rts := Roots(MinimalPolynomial(alpha), L);
h := hom<K -> L | rts[1][1]>;

// we now verify that lambda_p = a_p^2 + p*(1-chi(p))
for p in PrimesUpTo(20) do
    ap := Coefficient(f,p);
    lambda_p := HeckeEigenvalue(vs[3],p);
    assert ap^2 + p*(1-chi(p)) eq h(lambda_p);
end for;

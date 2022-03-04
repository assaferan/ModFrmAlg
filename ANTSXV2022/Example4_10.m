// This is Example 4.9 from the paper, a continuation of Example 3.2.
AttachSpec("../ModFrmAlg.spec");
// A gram matrix representing the genus 
Q := SymmetricMatrix([2,0,2,0,1,34,1,0,0,34]);
// Creating the space of orthogonal modular forms
M := OrthogonalModularForms(LatticeWithGram(Q));
Dimension(M);
/*
13
*/
#Representatives(Genus(M));
/*
13
*/
T2 := HeckeOperator(M,2);
T2;
/*
[1 1 1 0 0 0 0 0 0 0 0 0 0]
[4 2 0 1 0 0 0 0 0 1 0 0 0]
[4 0 0 2 1 1 0 0 0 0 0 0 0]
[0 2 4 1 0 0 1 0 0 1 0 0 1]
[0 0 2 0 1 0 0 1 0 1 1 0 1]
[0 0 2 0 0 1 0 0 1 1 0 1 1]
[0 0 0 1 0 0 2 0 0 1 0 0 2]
[0 0 0 0 1 0 0 4 0 0 2 0 0]
[0 0 0 0 0 1 0 0 4 0 0 2 0]
[0 4 0 2 2 2 2 0 0 2 1 1 0]
[0 0 0 0 2 0 0 4 0 1 3 0 2]
[0 0 0 0 0 2 0 0 4 1 0 3 2]
[0 0 0 2 2 2 4 0 0 0 2 2 0]
*/
// finidng the eigenforms
vs := HeckeEigenforms(M);
// choosing the one with Hecke eigenvalue -1 at 2
assert exists(v){v : v in vs | HeckeEigenvalue(v,2) eq -1};
// first few eigenvalues 
evs := HeckeEigensystem(v,1 : Precision := 20);
evs;
/*
[ -1, -1, -1, -1, 1, -1, 4, 29 ]
*/

// Verifying that lambda_p = a_p b_p = a_p bar(a_p) = Norm(a_p)
f1 := Newforms(ModularForms(67))[3][1];
assert &and[HeckeEigenvalue(v,p) eq Norm(Coefficient(f1,p)) : p in PrimesUpTo(20)];

// verifying that the L-polynomial of this vector is the Rankin-Selberg associated to f1 \otimes f2
for p in PrimesUpTo(20) do
    ap := Coefficient(f1,p);
    // This is the Rankin-Selberg L-polynomial
    lpoly := 1 - Norm(ap)*x + (-2*p^2 + p*(Trace(ap)^2-2*Norm(ap)))*x^2-p^2*Norm(ap)*x^3+p^4*x^4;
    assert lpoly eq LPolynomial(v,p);
end for;

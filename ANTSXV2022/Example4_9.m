// This is Example 4.9 from the paper, a continuation of Example 3.1.
AttachSpec("../ModFrmAlg.spec");
// A gram matrix representing the genus 
Q := SymmetricMatrix([2,0,4,1,1,10,1,2,1,20]);
// Creating the space of orthogonal modular forms
M := OrthogonalModularForms(LatticeWithGram(Q));
// The gram matrices of representatives of the genus
Lambdas := [GramMatrix(ZLattice(r)) : r in Representatives(Genus(M))];
Lambdas;
/*
[
    [ 2  0  1  1]
    [ 0  4  1  2]
    [ 1  1 10  1]
    [ 1  2  1 20],

    [ 2  1  1  2]
    [ 1 28 12 44]
    [ 1 12  8 21]
    [ 2 44 21 80],

    [14 13  7  4]
    [13 16  2  4]
    [ 7  2 10  1]
    [ 4  4  1 20],

    [10  3  2 12]
    [ 3  4  1  2]
    [ 2  1 10  1]
    [12  2  1 20]
]
*/
// The first few HeckeOperators
Tp1 := [HeckeOperator(M,p) : p in PrimesUpTo(10)];
Tp1;
/*
[
    [1 1 1 1]
    [2 4 0 2]
    [2 0 4 2]
    [4 4 4 4],

    [4 1 1 2]
    [2 9 0 3]
    [2 0 9 3]
    [8 6 6 8],

    [ 4  4  4  4]
    [ 8 10  6  8]
    [ 8  6 10  8]
    [16 16 16 16],

    [ 4  9  9  6]
    [18 13 12 15]
    [18 12 13 15]
    [24 30 30 28]
]
*/
// The eigenvectors
v := HeckeEigenforms(M);
v;
/*
[*
    Eisenstein eigenform given in coordinates by
    (1 1 1 1),
    Cuspidal eigenform given in coordinates by
    ( 0  1 -1  0),
    Cuspidal eigenform given in coordinates by
    (   1 -1/2 -1/2  1/4),
    Cuspidal eigenform given in coordinates by
    (   1  1/4  1/4 -1/2)
*]
*/
// The first few eigenvalues of each
evs := [HeckeEigensystem(vec,1 : Precision := 10) :  vec in v];
evs;
/*
[
    [ 9, 16, 36, 64 ],
    [ 4, 9, 4, 1 ],
    [ 0, 4, 0, -8 ],
    [ 0, 1, 0, 1 ]
]
*/

// verifying that for v1, we have eigenvalues (1+p)^2
assert &and[HeckeEigenvalue(v[1],p) eq (1+p)^2 : p in PrimesUpTo(20)];

// verifying that for v1, the L-polynomial is (1-p^(-s))(1-p^(1-s))^2(1-p^(2-s))
_<x> := Parent(LPolynomial(v[1],2));
assert &and[LPolynomial(v[1],p) eq (1-x)*(1-p*x)^2*(1-p^2*x) : p in PrimesUpTo(20)];

// Here the default Precision is 25, but can be set using the optional
// parameter Precision, e.g.
// f2 := Theta1(v[2] : Precision := 100);

f2 := Theta1(v[2]);
f3 := Theta1(v[4]);
f2;
/*
q - 2*q^2 - 3*q^3 + 2*q^4 - 2*q^5 + 6*q^6 - q^7 + 6*q^9 + 4*q^10 - 5*q^11 - 
    6*q^12 - 2*q^13 + 2*q^14 + 6*q^15 - 4*q^16 - 12*q^18 - 4*q^20 + 3*q^21 + 
    10*q^22 + 2*q^23 + O(q^25)
*/

// verifying that f2 is the form with LMFDB label 37.2.a.a 
assert qExpansion(Newforms(ModularForms(37))[1][1],25) eq f2;

f3;
/*
q + q^3 - 2*q^4 - q^7 - 2*q^9 + 3*q^11 - 2*q^12 - 4*q^13 + 4*q^16 + 6*q^17 + 
    2*q^19 - q^21 + 6*q^23 + O(q^25)
*/

// verifying that f3 is the form with LMFDB label 37.2.a.b
assert qExpansion(Newforms(ModularForms(37))[2][1],25) eq f3;

// verifying that the eigenvalues are the squares of the eigenvalues of the forms
assert &and[HeckeEigenvalue(v[2],p) eq Coefficient(f2,p)^2 : p in PrimesUpTo(20)];
assert &and[HeckeEigenvalue(v[4],p) eq Coefficient(f3,p)^2 : p in PrimesUpTo(20)];

// verifying that the L-Polynomials of the vectors are the Rankin-Selberg L-functions associated to f2 and f3
assert &and[LPolynomial(v[2],p) eq (1-p*x)^2*(1-(Coefficient(f2,p)^2-2*p)*x+p^2*x^2) : p in PrimesUpTo(20)];
assert &and[LPolynomial(v[4],p) eq (1-p*x)^2*(1-(Coefficient(f3,p)^2-2*p)*x+p^2*x^2) : p in PrimesUpTo(20)];

// verifying that lambda_p = a_p*(1+p) between eigenvalues of vs[3] and eigenvalues of f3
assert &and[HeckeEigenvalue(v[3],p) eq Coefficient(f3,p)*(p+1) : p in PrimesUpTo(20)];

// verifying that the L-Polynomials of vs[3] is the Rankin-Selberg L-functions associated to E2 and f3
assert &and[(1-Coefficient(f3,p)*x+p*x^2)*(1-p*Coefficient(f3,p)*x+p^3*x^2) eq LPolynomial(v[3],p) : p in PrimesUpTo(20)];

exit;

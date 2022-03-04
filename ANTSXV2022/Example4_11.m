// This is Example 4.11 from the paper, a continuation of Example 3.3
AttachSpec("../ModFrmAlg.spec");
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
_<x> := Parent(LPolynomial(vs[1],2));
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

// verify also that the L-polynmoial is coming from the Doi-Naganuma lift
_<x> := Parent(LPolynomial(vs[3],2));
assert &and[LPolynomial(vs[3],p) eq
	    (1-p*x)*(chi(p)-p*x)*(1 - (HeckeEigenvalue(vs[3],p)-(1+chi(p))*p)*x + p^2*x^2) : p in PrimesUpTo(20)];

// We turn to the remaining eigenvector
evs := HeckeEigensystem(vs[2], 1 : Precision := 10);
evs;
/*
[ -4, -4, 1, -2, -4, 1, -17, -14 ]
*/

// we create the corresponding Hilbert cusp form, with LMFDB label 2.2.193-1.1.a
K := QuadraticField(193);
ZK := Integers(K);
f := Eigenforms(HilbertCuspForms(K, 1*ZK, [2,2]))[1];
f_evs := [[HeckeEigenvalue(f, P) : P in PrimeIdealsOverPrime(K,p)] : p in PrimesUpTo(10)];
_<alpha> := Universe(f_evs[1]);
assert (2*alpha-1)^2 eq 17;
f_evs;
/*
[
    [
        alpha,
        -alpha + 1
    ],
    [
        -alpha + 1,
        alpha
    ],
    [
        1
    ],
    [
        alpha + 1,
        -alpha + 2
    ]
]
*/

// We verify that lambda_p = a_p a_p_bar at split primes and a_p at inert primes
assert &and[HeckeEigenvalue(vs[2],p) eq &*[HeckeEigenvalue(f,P)
					   : P in PrimeIdealsOverPrime(K,p)] : p in PrimesUpTo(20)];

// We next verify that the L-polynomial is the Asai L-polynomial
for p in PrimesUpTo(20) do
    prod := &*[HeckeEigenvalue(f,P) : P in PrimeIdealsOverPrime(K,p)];
    sum := &+[HeckeEigenvalue(f,P) : P in PrimeIdealsOverPrime(K,p)];
    prod := Rationals()!prod;
    sum := Rationals()!sum;
    if chi(p) eq 1 then
	// p is split
	
	// This is the polynomial at split primes
	asai := 1 - prod*x + p*(sum^2-2*prod-2*p)*x^2-p^2*prod*x^3 + p^4*x^4;
    else
	// This is the polynomial at inert primes
	asai := (1-p*x)*(-1-p*x)*(1-prod*x+p^2*x^2);
    end if;
    assert asai eq LPolynomial(vs[2],p);
end for;

exit;

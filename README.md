# ModFrmAlg
 Algebraic Modular Forms

A package for computing algebraic modular forms.
Load it using AttachSpec("ModFrmAlg.spec");

Currently supports orthogonal groups and unitary groups over number fields.
Can input any representation as a weight, and there is some support for constructing highest weight representations (see HighestWeightRepresentation(G, lambda)).
Supports also different levels. Levels can be input as a matrix describing the lattice. 

Here is a simple usage example.

// loading the package
AttachSpec("ModFrmAlg.spec");

QQ := Rationals();
// setting up several weights (representations) and quadratic forms
std_reps := AssociativeArray();
forms := AssociativeArray();
std_reps[3] := StandardRepresentation(GL(3,QQ));
std_reps[5] := StandardRepresentation(GL(5,QQ));
forms[3] := [2*IdentityMatrix(QQ,3),
	  SymmetricMatrix(QQ, [2,0,2,1,0,6]),
	  SymmetricMatrix(QQ, [4,-1,4,-1,0,12]) // Alok Shukla's example
	  ];
forms[5] := [
	  2*IdentityMatrix(QQ,5),
	  SymmetricMatrix(QQ, [2,0,2,0,0,2,0,0,0,2,1,0,0,0,6]),
	  SymmetricMatrix(QQ, [2,0,2,0,0,2,0,1,0,2,1,0,0,0,6])
];
// choosing a form
A := forms[5][2];
// Constructing a group and a representation
G := SpecialOrthogonalGroup(A);
W := SymmetricRepresentation(std_reps[5], 2);
// Constructing the space of algebraic modular forms
M := AlgebraicModularForms(G,W);
Dimension(M);
eigenforms := HeckeEigenforms(M);
prec := 20;
// The eigenvalues of the Hecke operators T_{p,1} 
evs := [* HeckeEigensystem(f,1 : Precision := prec) :  f in eigenforms *];
// The L-polynomials of these modular forms
lpolys := [* LPolynomials(f : Precision := prec) : f in eigenforms *];
// Factorization of the L-polynomials
lps :=  [* [Factorization(lp[p]) : p in PrimesUpTo(prec)] : lp in lpolys *];
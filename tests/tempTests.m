SetDebugOnError(true);
SetHelpUseExternalBrowser(false);
AttachSpec("spec");

if assigned AlgebraicModularFormsExamples then
    delete AlgebraicModularFormsExamples;
end if;

if assigned testExample then
    delete testExample;
end if;

if assigned normalizeField then
    delete normalizeField;
end if;

import "tests/examples.m" : AlgebraicModularFormsExamples;
import "tests/tests.m" : testExample;
import "modfrmalg/modfrmalg.m" : normalizeField;
import "neighbors/hecke-CN1.m" : processNeighborWeight,
       HeckeOperatorCN1,
       HeckeOperatorCN1Sparse,
       printEstimate;
import "neighbors/inv-CN1.m" : Invariant;
import "neighbors/neighbor-CN1.m" : BuildNeighborProc,
       SkipToNeighbor,
       BuildNeighbor,
       LiftSubspace,
       GetNextNeighbor;

import "neighbors/genus-CN1.m" : OrthogonalMass, UnitaryMass;
import "lattice/lattice.m" : GuessMaxDet;

function inspect(M : prec := 20)
    Dimension(M);
    if IsZero(Dimension(M)) then return [* *]; end if;
    D := Decomposition(M,100);
    eigenforms := HeckeEigenforms(M);
    evs := [* HeckeEigensystem(f,1 : prec := prec) :  f in eigenforms *];
    lpolys := [* LPolynomials(f : prec := prec) : f in eigenforms *];
    return evs, lpolys;
end function;

QQ := Rationals();
std_reps := AssociativeArray();
forms := AssociativeArray();
std_reps[3] := StandardRepresentation(GL(3,QQ));
std_reps[5] := StandardRepresentation(GL(5,QQ));
forms[3] := [IdentityMatrix(QQ,3),
	  SymmetricMatrix(QQ, [1,0,1,1/2,0,3]),
	  SymmetricMatrix(QQ, [2,-1/2,2,-1/2,0,6]) // Alok Shukla's example
	  ];
forms[5] := [
	  IdentityMatrix(QQ,5),
	  SymmetricMatrix(QQ, [1,0,1,0,0,1,0,0,0,1,1/2,0,0,0,3]),
	  SymmetricMatrix(QQ, [1,0,1,0,0,1,0,1/2,0,1,1/2,0,0,0,3])
];
// understand which of these examples is suitable to become a test
/*
for dim in [3,5] do
    for A in forms[dim] do
	A;
	G := SpecialOrthogonalGroup(A);
	// maybe should make k depend on the dimension
	for k in [0..6] do
	    k;
	    W := SymmetricRepresentation(std_reps[dim],k);
	    //	M := OrthogonalModularForms(A, W);
	    M := AlgebraicModularForms(G, W);
	    inspect(M);
	end for;
    end for;
end for;
*/

M, timing := AlgebraicModularFormsTests(:num_primes := 3,
					 decomposition := true);

A := forms[5][2];
G := SpecialOrthogonalGroup(A);
W := SymmetricRepresentation(std_reps[5], 2);
M := AlgebraicModularForms(G,W);
inspect(M : prec := 4);

// This code is for checking the image of the Galois representation
// Later put it in a relevant place

function getGaloisImage(L_p, l, psi, fp_hom)
    a := Coefficients(L_p);
    K := Universe(a);
    K_x<x> := Parent(L_p);
    _, phi := IsSquare(a[1]/a[5]);
    a := [a[2]/a[5], a[3]/a[5]];
    zero := MatrixRing(K,2)!0;
    A := CompanionMatrix(x^2);
    B := zero;
    B[2,2] := -phi^(-2);
    C := zero;
    C[1,1] := phi^3;
    C[1,2] := phi * a[1];
    D := zero;
    D[1,2] := -phi^(-1) * a[2];
    D[2,1] := phi;
    D[2,2] := -phi^(-1) * a[1];
    // This is a symplectic similtude matrix
    // (with the correct similitiude factor)
    // with characteristic polynomial L_p
    mat := BlockMatrix([[A,B],[C,D]]);
    mat_mod_l := GL(4,l)!mat;
    g := (mat_mod_l @@ fp_hom) @ psi;
    return g;
end function;

function getGaloisImages(lpolys, l)
    a := PrimitiveElement(GF(l));
    zero := MatrixRing(GF(l),2)!0;
    one := MatrixRing(GF(l),2)!1;
    Q := BlockMatrix([[a*one, zero], [zero, one]]);
    CSp_4_l := sub<GL(4,l)|Sp(4,l),Q>;
    fp_grp, fp_hom := FPGroup(CSp_4_l);
    csp_4, psi := PermutationGroup(fp_grp);
    return [getGaloisImage(L_p, l, psi, fp_hom) : L_p in lpolys];
end function;

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

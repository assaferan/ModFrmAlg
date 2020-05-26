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

function inspect(M)
    Dimension(M);
    if IsZero(Dimension(M)) then return [* *]; end if;
    D := Decomposition(M,10);
    eigenforms := HeckeEigenforms(M);
    evs := [* HeckeEigensystem(f,1 : prec := 20) :  f in eigenforms *];
    return evs;
end function;

QQ := Rationals();
V := StandardRepresentation(GL(3,QQ));
forms := [IdentityMatrix(QQ,3), SymmetricMatrix(QQ, [1,0,1,1/2,0,3])];
for A in forms do
    A;
    SO_3 := SpecialOrthogonalGroup(A);
    for k in [0..6] do
	k;
	W := SymmetricRepresentation(V,k);
	//	M := OrthogonalModularForms(A, W);
	M := AlgebraicModularForms(SO_3, W);
	inspect(M);
    end for;
end for;

M, timing := AlgebraicModularFormsTests(:num_primes := 3,
					 decomposition := true);

/*
upTo := 0;
genList := [ Module(M) ];
invs := AssociativeArray();
invs[Invariant(Module(M))] := [ < Module(M), 1 > ];
repeat
    // Increment norm by 10.
    upTo +:= 10;

    // Compute a list of primes which do not divide the
    //  discriminant of the lattice.
    ps := [ p : p in PrimesUpTo(upTo, BaseRing(M)) |
	    Gcd(Integers()!Norm(Discriminant(Module(M))),
		Norm(p)) eq 1 ];
until #ps ne 0;
idx := 1;
p := ps[idx];
isoList := genList;
isoIdx := 1;
BeCareful := true;
nProc := BuildNeighborProc(isoList[isoIdx], p, 1
			: BeCareful := BeCareful);
*/

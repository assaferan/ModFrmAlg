SetDebugOnError(true);
SetHelpUseExternalBrowser(false);
AttachSpec("spec");
// This was done to test timings - Orbits + UseLLL is almost always the fastest
// (lost only in examples 3 and 7 to Orbits without LLL, and by a small margin)
/*
M, timing := AlgebraicModularFormsTests(:num_primes := 3,
					 Orbits := false,
					 UseLLL := false);
M, timing_orbits := AlgebraicModularFormsTests(:num_primes := 3,
						Orbits := true,
						UseLLL := false);
M, timing_use_lll := AlgebraicModularFormsTests(:num_primes := 3,
						 Orbits := false,
						 UseLLL := true);
M, timing_orbits_lll := AlgebraicModularFormsTests(:num_primes := 3,
						    Orbits := true,
						    UseLLL := true);
*/

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
       HeckeOperatorCN1Sparse;
import "neighbors/inv-CN1.m" : Invariant;
import "neighbors/neighbor-CN1.m" : BuildNeighborProc,
       SkipToNeighbor,
       BuildNeighbor;

// SetVerbose("AlgebraicModularForms",2);
examples := AlgebraicModularFormsExamples;
QQ := Rationals();
F := SymmetricMatrix(QQ, [4,-1,4,-1,0,12]);
SO_3 := SpecialOrthogonalGroup(F);
V := StandardRepresentation(GL(3,QQ));
M := AlgebraicModularForms(SO_3, V);
/*
mat := IdentityMatrix(QQ,5);
mat := 2*IdentityMatrix(QQ,5);
mat[5,5] := 6;
mat[1,5] := 1;
mat[5,1] := 1;
mat[2,4] := 1;
mat[4,2] := 1;
SO5 := SpecialOrthogonalGroup(mat);
V := StandardRepresentation(GL(5,QQ));
W := SymmetricRepresentation(V,2);
M := AlgebraicModularForms(SO5, W);
printf "Dimension(M) = %o\n", Dimension(M);
T2 := HeckeOperator(M,2 : Estimate := true);
eigenforms := HeckeEigenforms(M);
evs := [* HeckeEigensystem(f) : f in eigenforms *];
assert exists(i){i : i in [1..#evs]  | (4*evs[i][1]+13)^2 eq 5};
f := eigenforms[i];
*/
/*
example := examples[7];
M := UnitaryModularForms(example`field, example`inner_form,
			 example`weight, example`coeff_char);
d := Dimension(M);
p := 2;
T := HeckeOperator(M, p : Estimate := true);
eigenforms := HeckeEigenforms(M);
f := eigenforms[1];
t0 := Cputime();
evs, ps := HeckeEigensystem(f, 1 : prec := 30);
t1 := Cputime();
T := HeckeOperator(M, 11 : Estimate := true);
t2 := Cputime();
T := HeckeOperator(M, 23 : Estimate := true);
t3 := Cputime();
T := HeckeOperator(M, 29 : Estimate := true);
t4 := Cputime();
printf "f took %o, T11 took %o, T23 took %o, T29 took %o",
       t1-t0, t2-t1, t3-t2, t4-t3;
*/

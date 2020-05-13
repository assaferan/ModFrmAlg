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
       HeckeOperatorCN1Sparse,
       printEstimate;
import "neighbors/inv-CN1.m" : Invariant;
import "neighbors/neighbor-CN1.m" : BuildNeighborProc,
       SkipToNeighbor,
       BuildNeighbor,
       LiftSubspace,
       GetNextNeighbor;


M, timing := AlgebraicModularFormsTests(:num_primes := 3,
					 decomposition := true);

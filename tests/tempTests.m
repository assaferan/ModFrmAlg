SetDebugOnError(true);
SetHelpUseExternalBrowser(false);
AttachSpec("spec");
//AlgebraicModularFormsTests(:num_primes := 3);

import "tests/examples.m" : AlgebraicModularFormsExamples;
import "tests/tests.m" : testExample;
examples := AlgebraicModularFormsExamples;
example := examples[10];
M := testExample(example : num_primes := 3);
fname := Sprintf("Example_%o.dat", example`name);
Save(M, fname : Overwrite := true);
// loading from the file and verifying we get the same object
M2 := AlgebraicModularForms(fname);
assert M eq M2;

// Testing an inert prime
// p := Factorization(ideal<Integers(BaseRing(M)) | 3>)[1][1];
/*
HeckeOperator(M, 3 ,1 : BeCareful := false, Estimate := true);
M := UnitaryModularForms(QuadraticField(-7),4);
HeckeOperator(M, 3 ,1 : BeCareful := false, Estimate := true);
*/
/*
fname := Sprintf("Example_%o.dat", example`name);
Save(M, fname : Overwrite := true);
M2 := AlgebraicModularForms(fname);
*/

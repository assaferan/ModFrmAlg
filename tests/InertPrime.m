import "examples/examples.m" : AlgebraicModularFormsExamples;
import "examples/TestExamples.m" : testExampleTimingsSaveAndLoad;

// testing an inert prime
example := AlgebraicModularFormsExamples[3];
M := testExampleTimingsSaveAndLoad(example : NumPrimes := 3);
T2 := HeckeOperator(M,2);
T3 := HeckeOperator(M,3);
assert T2*T3 eq T3*T2;

import "examples/examples.m" : AlgebraicModularFormsExamples;
import "examples/TestExamples.m" : testExampleTimingsSaveAndLoad;

testExampleTimingsSaveAndLoad(AlgebraicModularFormsExamples[6] : LowMemory, NumPrimes := 5);

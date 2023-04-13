import "examples/examples.m" : AlgebraicModularFormsExamples;
import "examples/TestExamples.m" : testExampleTimingsSaveAndLoad;

testExampleTimingsSaveAndLoad(AlgebraicModularFormsExamples[8] : LowMemory, NumPrimes := 10);

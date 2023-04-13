import "examples/examples.m" : AlgebraicModularFormsExamples;
import "examples/TestExamples.m" : testExampleTimingsSaveAndLoad;

testExampleTimingsSaveAndLoad(AlgebraicModularFormsExamples[10] : LowMemory, NumPrimes := 5);

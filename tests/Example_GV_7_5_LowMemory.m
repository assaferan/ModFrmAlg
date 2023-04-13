import "examples/examples.m" : AlgebraicModularFormsExamples;
import "examples/TestExamples.m" : testExampleTimingsSaveAndLoad;

// We limit the number of primes to verify to save time running the test
testExampleTimingsSaveAndLoad(AlgebraicModularFormsExamples[9] : LowMemory, NumPrimes := 5);

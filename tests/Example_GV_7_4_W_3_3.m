import "examples/examples.m" : AlgebraicModularFormsExamples;
import "examples/TestExamples.m" : testExampleTimingsSaveAndLoad;

// In order to save some time, we limit the number of primes here
testExampleTimingsSaveAndLoad(AlgebraicModularFormsExamples[7] : NumPrimes := 10);

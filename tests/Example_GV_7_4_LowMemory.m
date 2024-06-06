import "examples/examples.m" : AlgebraicModularFormsExamples;
import "examples/TestExamples.m" : testExampleTimingsSaveAndLoad;

SetVerbose("AlgebraicModularForms", 2);
testExampleTimingsSaveAndLoad(AlgebraicModularFormsExamples[3] : LowMemory, NumPrimes := 10);

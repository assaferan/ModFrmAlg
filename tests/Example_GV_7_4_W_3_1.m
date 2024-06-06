import "examples/examples.m" : AlgebraicModularFormsExamples;
import "examples/TestExamples.m" : testExampleTimingsSaveAndLoad;

SetVerbose("AlgebraicModularForms", 2);
testExampleTimingsSaveAndLoad(AlgebraicModularFormsExamples[6] : NumPrimes := 10);

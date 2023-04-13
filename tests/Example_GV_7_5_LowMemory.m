import "examples/examples.m" : AlgebraicModularFormsExamples;
import "examples/TestExamples.m" : testExampleTimingsSaveAndLoad;

testExampleTimingsSaveAndLoad(AlgebraicModularFormsExamples[9] : LowMemory);

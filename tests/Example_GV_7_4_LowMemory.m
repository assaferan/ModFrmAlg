import "examples/examples.m" : AlgebraicModularFormsExamples;
import "examples/TestExamples.m" : testExampleTimingsSaveAndLoad;

testExampleTimingsSaveAndLoad(AlgebraicModularFormsExamples[3] : LowMemory);

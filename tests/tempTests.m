SetDebugOnError(true);
SetHelpUseExternalBrowser(false);
AttachSpec("spec");
AlgebraicModularFormsTests(:num_primes := 3);

import "tests/examples.m" : AlgebraicModularFormsExamples;
import "tests/tests.m" : testExample;
examples := AlgebraicModularFormsExamples;
/*
example := examples[1];
M := testExample(example : num_primes := 3);
fname := Sprintf("Example_%o.dat", example`name);
Save(M, fname : Overwrite := true);
M2 := AlgebraicModularForms(fname);

M eq M2;
*/
/*
ps := [Factorization(ideal<Integers(BaseRing(M))|n>)[1][1] :
	   n in examples[7]`norm_p];

    for k in [1..2] do
	Ts_k := [];
    
	for i in [1..3] do
	    p := ps[i];
	    printf "Computing T(p,%o), (N(p) = %o) ...\n", k, Norm(p);
	    t := Cputime();
	    Append(~Ts_k, HeckeOperator(M, p, k : BeCareful := false,
						  Estimate := true,
						  UseLLL := true,
						  Orbits := (k eq 1)));
	    timing := Cputime() - t;
	    printf "took %o seconds.\n", timing;
	end for;
	print "Done.";

	// Verify that these operators commute with each other.
	assert &and[ A*B eq B*A : A,B in Ts_k ];
    end for;
*/
/*
for i in [1..2] do
    M := testExample(examples[i] : num_primes := 3);
    fname := Sprintf("Example_%o.dat", examples[i]`name);
    Save(M, fname : Overwrite := true);
    // loading from the file and verifying we get the same object
    M2 := AlgebraicModularForms(fname);
    assert M eq M2;
end for;
*/
/*
QQ := Rationals();
W := StandardRepresentation(GL(3,QQ));
W := SymmetricRepresentation(W, 2);
M := OrthogonalModularForms(2*IdentityMatrix(QQ,3), W);
HeckeOperator(M,2);
*/
// Testing an inert prime
// p := Factorization(ideal<Integers(BaseRing(M)) | 3>)[1][1];
/*
HeckeOperator(M, 3 ,1 : BeCareful := false, Estimate := true);
M := UnitaryModularForms(QuadraticField(-7),4);
HeckeOperator(M, 3 ,1 : BeCareful := false, Estimate := true);
*/
/*
fname := Sprintf("Example_%o.dat", example`name);
Save(M, fname : Overwrite := true);
M2 := AlgebraicModularForms(fname);
*/

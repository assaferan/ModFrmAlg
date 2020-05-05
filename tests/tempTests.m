SetDebugOnError(true);
SetHelpUseExternalBrowser(false);
AttachSpec("spec");
// AlgebraicModularFormsTests(:num_primes := 3);

if assigned AlgebraicModularFormsExamples then
    delete AlgebraicModularFormsExamples;
end if;

if assigned testExample then
    delete testExample;
end if;

if assigned normalizeField then
    delete normalizeField;
end if;

import "tests/examples.m" : AlgebraicModularFormsExamples;
import "tests/tests.m" : testExample;
import "modfrmalg/modfrmalg.m" : normalizeField;
import "neighbors/hecke-CN1.m" : processNeighborWeight, HeckeOperatorCN1;
import "neighbors/inv-CN1.m" : Invariant;
import "neighbors/neighbor-CN1.m" : BuildNeighborProc,
       SkipToNeighbor,
       BuildNeighbor;

print "Hello!";

examples := AlgebraicModularFormsExamples;
example := examples[7];
M := UnitaryModularForms(example`field, example`inner_form,
			 example`weight, example`coeff_char);
d := Dimension(M);
p := 2;
pR := Factorization(ideal<Integers(BaseRing(M)) | p>)[1][1];
k := 1;
reps := Representatives(Genus(M));
hecke := [ [ [* M`W!0 : hh in M`H*] : vec_idx in [1..Dimension(h)]] : h in M`H];
isoms := [ [ [* [] : hh in M`H*] : vec_idx in [1..Dimension(h)]] : h in M`H];
invs := M`genus`RepresentativesAssoc;
Q := ReflexiveSpace(Module(M));
n := Dimension(Q);
fullCount := #M`H * NumberOfNeighbors(M, pR, k);

function get_orbit_contrib1(orbit, nProc, psi, gens_modp, Aut,
			    gens, n, Q, M, invs, idx, B)
    nProc := SkipToNeighbor(nProc, Basis(orbit[1]));

    mat_gen_seq := [[
			   gens[Index(gens_modp, Eltseq(Aut.Abs(i)))]^Sign(i) :
			   i in Eltseq((B*g*B^(-1))@@psi)] :
		    g in orbit[2]];
    mat_lifts := [IsEmpty(seq) select GL(n,BaseRing(Q))!1 else
		  &*seq : seq in mat_gen_seq];

    w := &+[Matrix(getMatrixAction(M`W, Transpose(M`W`G!g))) :
	    g in mat_lifts];

    hecke := [ [ [* M`W!0 : hh in M`H*] : vec_idx in [1..Dimension(h)]] :
	       h in M`H];
    
    processNeighborWeight(~nProc, invs, ~hecke, idx, M`H: weight := w);
    return hecke;
end function;

function get_orbit_contrib2(orbit, nProc, psi, gens_modp, Aut,
			    gens, n, Q, M, invs, idx, B)
    hecke := [ [ [* M`W!0 : hh in M`H*] : vec_idx in [1..Dimension(h)]] :
	       h in M`H];
    for gamma in orbit[2] do
	iso_gens := [ b * B * gamma * B^(-1) : b in Basis(orbit[1])];
	nProc := SkipToNeighbor(nProc, iso_gens);
	processNeighborWeight(~nProc, invs, ~hecke, idx, M`H);
    end for;
    return hecke;
end function;

for idx in [1..#M`H] do
    L := reps[idx];
    nProc := BuildNeighborProc(L, pR, k);
    V := nProc`L`Vpp[pR]`V;
    F := BaseRing(V);
    G := AutomorphismGroup(L);
    BeCareful := true;
    gens := [PullUp(Matrix(g), L, L :BeCareful := BeCareful):g in Generators(G)];
    pMaximalBasis :=ChangeRing(L`pMaximal[nProc`pR][2], BaseRing(Q));
    conj_gens := [pMaximalBasis * g * pMaximalBasis^(-1) :g in gens];
    gens_modp := [[L`Vpp[pR]`proj_pR(x) : x in Eltseq(g)]: g in conj_gens];
    Aut := sub<GL(n, F) | gens_modp>;
    fp_aut, psi := FPGroup(Aut);
    isoOrbits := IsotropicOrbits(V, Aut, k);
    B := Transpose(V`Basis);
    for orb_idx in [1..#isoOrbits] do
	orbit := isoOrbits[orb_idx];
	contrib1 := get_orbit_contrib1(orbit, nProc, psi, gens_modp, Aut,
				       gens, n, Q, M, invs, idx, B);
	contrib2 := get_orbit_contrib2(orbit, nProc, psi, gens_modp, Aut,
				       gens, n, Q, M, invs, idx, B);
	assert contrib1 eq contrib2;
    end for;
end for;

h := HeckeOperatorCN1(M, pR, 1
			  : BeCareful := false,
			    UseLLL := false,
			    Estimate := true,
			    Orbits := true);

/*
QQ := Rationals();
n := 5;
innerForm := 2 * IdentityMatrix(QQ,n);
// innerForm := examples[1]`inner_form;
K := normalizeField(BaseRing(innerForm));
n := Nrows(innerForm);
V := StandardRepresentation(GL(n,K));
W := SymmetricRepresentation(V,2);
// Why is this not working?
//SO_n := SpecialOrthogonalGroup(ChangeRing(innerForm, K));
O_n := OrthogonalGroup(ChangeRing(innerForm, K));
M := AlgebraicModularForms(O_n, W);
Dimension(M);
*/
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
	   n in examples[1]`norm_p];

    for k in [1..2] do
	Ts_k := [];
    
	for i in [1..3] do
	    p := ps[i];
	    printf "Computing T(p,%o), (N(p) = %o) ...\n", k, Norm(p);
	    t := Cputime();
	    Append(~Ts_k, HeckeOperator(M, p, k : BeCareful := false,
						  Estimate := true,
						  UseLLL := false,
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

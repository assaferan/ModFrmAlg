SetDebugOnError(true);
SetHelpUseExternalBrowser(false);
AttachSpec("spec");
// This was done to test timings - Orbits + UseLLL is almost always the fastest
// (lost only in examples 3 and 7 to Orbits without LLL, and by a small margin)
/*
M, timing := AlgebraicModularFormsTests(:num_primes := 3,
					 Orbits := false,
					 UseLLL := false);
M, timing_orbits := AlgebraicModularFormsTests(:num_primes := 3,
						Orbits := true,
						UseLLL := false);
M, timing_use_lll := AlgebraicModularFormsTests(:num_primes := 3,
						 Orbits := false,
						 UseLLL := true);
M, timing_orbits_lll := AlgebraicModularFormsTests(:num_primes := 3,
						    Orbits := true,
						    UseLLL := true);
*/

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
import "neighbors/hecke-CN1.m" : processNeighborWeight,
       HeckeOperatorCN1,
       HeckeOperatorCN1Sparse,
       printEstimate;
import "neighbors/inv-CN1.m" : Invariant;
import "neighbors/neighbor-CN1.m" : BuildNeighborProc,
       SkipToNeighbor,
       BuildNeighbor,
       LiftSubspace,
       GetNextNeighbor;

example := AlgebraicModularFormsExamples[2];
M := OrthogonalModularForms(example`field, example`inner_form,
			    example`weight, example`coeff_char);

pR := ideal<Integers(BaseRing(M))|2>;
/*
idx := 1;
reps := Representatives(Genus(M));
L := reps[idx];
k := 2;
BeCareful := true;
nProc := BuildNeighborProc(L, pR, k
			   : BeCareful := BeCareful);
V := nProc`L`Vpp[pR]`V;

// The base field.
F := BaseRing(V);

// The automorphism group restricted to the affine space.
G := AutomorphismGroup(L);
	    
gens := [PullUp(Matrix(g), L, L :
		BeCareful := BeCareful) :
	 g in Generators(G)];

Q := ReflexiveSpace(Module(M));
n := Dimension(Q);

pMaximalBasis :=
    ChangeRing(L`pMaximal[nProc`pR][2], BaseRing(Q));

conj_gens := [pMaximalBasis * g * pMaximalBasis^(-1) :
	      g in gens];
	
gens_modp := [[L`Vpp[pR]`proj_pR(x) : x in Eltseq(g)]
	      : g in conj_gens];
	
Aut := sub<GL(n, F) | gens_modp>;
G := Aut;
list := AllIsotropicSubspaces(V, k);

*/

HeckeOperator(M, 2, 2 : Orbits := true, Estimate := true);
HeckeOperator(M, 2, 2 : Orbits := false, Force := true, Estimate := true);
/*
HeckeOperator(M, pR, 1);


function HeckeOperatorCN1Debug(M, pR, k
			  : BeCareful := false,
			    UseLLL := true,
			    Estimate := true)
    
    // The genus representatives.
    reps := Representatives(Genus(M));

    hecke := [ [ [* M`W!0 : hh in M`H*] : vec_idx in [1..Dimension(h)]] :
	       h in M`H];

    hecke_orbits := [ [ [* M`W!0 : hh in M`H*] : vec_idx in [1..Dimension(h)]] :
	       h in M`H];

    // Keeping track of the gamma_i_j
    //  isom := [ [[] : h1 in H] : h2 in H ];

    // An associative array indexed by a specified invariant of an isometry
    //  class. This data structure allows us to bypass a number of isometry
    //  tests by filtering out those isometry classes whose invariant
    //  differs from the one specified.
    invs := M`genus`RepresentativesAssoc;

    Q := ReflexiveSpace(Module(M));
    n := Dimension(Q);

    fullCount := #M`H * NumberOfNeighbors(M, pR, k);
    count := 0;
    elapsed := 0;
    start := Realtime();
	
    for idx in [1..#M`H] do
	// The current isometry class under consideration.
	L := reps[idx];

	// Build neighboring procedure for this lattice.
	nProc := BuildNeighborProc(L, pR, k
				   : BeCareful := BeCareful);

	if GetVerbose("AlgebraicModularForms") ge 1 then
	    printf "Computing %o%o-neighbors for isometry class "
		   cat "representative #%o...\n", pR,
		   k eq 1 select "" else "^" cat IntegerToString(k),
		   idx;
	end if;

	// The affine vector space.
	V := nProc`L`Vpp[pR]`V;

	// The base field.
	F := BaseRing(V);

	// The automorphism group restricted to the affine space.
	G := AutomorphismGroup(L);
	    
	gens := [PullUp(Matrix(g), L, L :
			BeCareful := BeCareful) :
		 g in Generators(G)];

	pMaximalBasis :=
	    ChangeRing(L`pMaximal[nProc`pR][2], BaseRing(Q));

	conj_gens := [pMaximalBasis * g * pMaximalBasis^(-1) :
		      g in gens];
	
	gens_modp := [[L`Vpp[pR]`proj_pR(x) : x in Eltseq(g)]
		      : g in conj_gens];
	
	Aut := sub<GL(n, F) | gens_modp>;
	fp_aut, psi := FPGroup(Aut);
	
	// The isotropic orbit data.
	isoOrbits := IsotropicOrbits(V, Aut, k);
	B := Transpose(V`Basis);

	total_num := &+[#orbit[2] : orbit in isoOrbits];
*/
	/*
	assert total_num eq
	       NumberOfNeighbors(M, pR, k);
        */
	/*
	for orbit in isoOrbits do
	    skew0 := Zero(MatrixRing(F,k));
	    // Skip to the neighbor associated to this orbit.
	    SkipToNeighbor(~nProc, [b : b in Basis(orbit[1])], skew0);
	    iso_subspace := nProc`isoSubspace;
	    mat_gen_seq := [[
				   gens[Index(gens_modp, Eltseq(Aut.Abs(i)))]^Sign(i) :
				   i in Eltseq(g@@psi)] :
			    g in orbit[2]];
	    mat_lifts := [IsEmpty(seq) select GL(n,BaseRing(Q))!1 else
			  &*seq : seq in mat_gen_seq];
	    
	    w := &+[Matrix(getMatrixAction(M`W, Transpose(M`W`G!g))) :
		    g in mat_lifts];
	    
	    cnt := 0;
	    repeat
		if nProc`skewDim gt 0 then
		    skew := nProc`skew;
		else
		    skew := Zero(MatrixRing(F,k));
		end if;
		
		for g in orbit[2] do
		    
		    SkipToNeighbor(~nProc,
				   [b*B*g*B^(-1) :
				    b in Basis(orbit[1])], skew);
		    processNeighborWeight(~nProc, invs, ~hecke, idx, M`H :
				      BeCareful := BeCareful,
				      UseLLL := UseLLL,
				      special := IsSpecialOrthogonal(M));
		end for;
		SkipToNeighbor(~nProc, [b : b in Basis(orbit[1])],skew);

		processNeighborWeight(~nProc, invs, ~hecke_orbits, idx, M`H:
				  BeCareful := BeCareful,
				  UseLLL := UseLLL,
				  weight := w,
				  special := IsSpecialOrthogonal(M));
		
		assert hecke eq hecke_orbits;
		GetNextNeighbor(~nProc);
		cnt +:= 1;
	    until (nProc`skewDim eq 0) or (nProc`skew eq skew0);
	    assert cnt eq (#F)^(k*(k-1) div 2);
	    
	    if Estimate then
		printEstimate(start, ~count, ~elapsed,
			      fullCount, pR, k :
			      increment := #orbit[2]);
	    end if;
	end for;
    end for;

    iota := [h`embedding : h in M`H];
   
    mats := [[[Eltseq(hecke[space_idx][vec_idx][idx]@@iota[idx]) :
		      vec_idx in [1..Dimension(M`H[space_idx])]] :
	      space_idx in [1..#M`H]] : idx in [1..#M`H]];

    vert_blocks := [&cat mat : mat in mats];

    empty_operator := MatrixAlgebra(BaseRing(M),0)![];
    
    if IsEmpty(vert_blocks) then return empty_operator; end if;
    if IsEmpty(vert_blocks[1]) then return empty_operator; end if;
    
    vert_mats := [* Matrix(blk) : blk in vert_blocks |
		  not IsEmpty(blk[1]) *];

    if IsEmpty(vert_mats) then return empty_operator; end if;

    // would have done a one liner, but there are universe issues
    ret := vert_mats[1];
    for idx in [2..#vert_mats] do
	ret := HorizontalJoin(ret, vert_mats[idx]);
    end for;
    
    return ret;
end function;

SetVerbose("AlgebraicModularForms", 2);
HeckeOperatorCN1Debug(M, pR, 1);
HeckeOperatorCN1Debug(M, pR, 2);
*/

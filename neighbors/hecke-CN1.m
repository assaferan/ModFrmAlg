//freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: hecke-CN1.m (Implementation for computing Hecke matrices)

   03/26/20: Added some verbose print outs for debugging and profiling.
             Moved the calculation of the space from the Hecke operator
             computation to the initialization of the space.
             Made some modifications to enable weight spaces over rings
             other than QQ (e.g. finite fields)

   03/11/20: Modified HeckeOperatorTrivialWeightCN1 to have an optional
             parameter invoking the orbit method.
   	     Added the procedure processNeighbor, for better readability 
             and modularity of the code, towards introducing orbits

   03/10/20: started editing this file to add Unitary forms
 
 ***************************************************************************/

// imports

import "inv-CN1.m" : Invariant;
import "neighbor-CN1.m" : BuildNeighborProc, BuildNeighbor,
	GetNextNeighbor, SkipToNeighbor;

procedure processNeighbor(~nProc, invs, ~hecke, idx :
			  BeCareful := true, weight := 1)
    // Build the neighbor lattice corresponding to the
    //  current state of nProc.
    nLat := BuildNeighbor(nProc : BeCareful := BeCareful);

    // Compute the invariant of the neighbor lattice.
    inv := Invariant(nLat);

    // Retrieve the array of isometry classes matching this
    //  invariant.
    array := invs[inv];

    // Isometry testing is only necessary if the array has
    //  length larger than 1.
    if #array ne 1 then
	// Flag to determine whether an isometry class
	//  was actually found. This is a failsafe.
	found := false;
	
	for j in [1..#array] do
	    // Check for isometry.
	    iso := IsIsometric(nLat, array[j][1]);
	    
	    // If isometric, flag as found,
	    //  increment Hecke matrix, and move on.
	    if iso then
		found := true;
		hecke[array[j][2]][idx] +:= weight;
		continue;
	    end if;
	end for;

	// Verify that the neighbor was indeed isometric
	//  to something in our list.
	assert found;
    else
	// Array length is one, and therefore conclude
	//  that nLat is isometric to the only entry in
	//  the array.
	hecke[array[1][2]][idx] +:= weight;
    end if;
    
    // Update nProc in preparation for the next neighbor
    //  lattice.
    nProc := GetNextNeighbor(nProc
			     : BeCareful := BeCareful);
end procedure;

// TODO: Add estimate functionality (mirror the implementation in hecke-QQ.m).
function HeckeOperatorTrivialWeightCN1(M, pR, k
				       : BeCareful := true,
				         Estimate := false,
				         Orbits := false)
	// The genus representatives.
	reps := Representatives(Genus(M));

	// The dimension of the Hecke matrix.
	dim := #reps;

	// Initialize the Hecke matrix.
	hecke := Zero(MatrixRing(Integers(), dim));

	// An associative array indexed by a specified invariant of an isometry
	//  class. This data structure allows us to bypass a number of isometry
	//  tests by filtering out those isometry classes whose invariant
	//  differs from the one specified.
	invs := M`genus`RepresentativesAssoc;

	Q := ReflexiveSpace(Module(M));
	n := Dimension(Q);

	for idx in [1..dim] do
		// The current isometry class under consideration.
		L := reps[idx];

		// Build neighboring procedure for this lattice.
		nProc := BuildNeighborProc(L, pR, k
			: BeCareful := BeCareful);

		if Orbits then
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

		    gens := [pMaximalBasis * g * pMaximalBasis^(-1) :
			     g in gens];

		    gens_modp := [[L`Vpp[pR]`proj_pR(x) : x in Eltseq(g)]
				  : g in gens];
		 
		    Aut := sub<GL(n, F) | gens_modp>;

		    // The isotropic orbit data.
		    isoOrbits := IsotropicOrbits(V, Aut, k);

		    for orbit in isoOrbits do
			// Skip to the neighbor associated to this orbit.
			nProc := SkipToNeighbor(nProc, Basis(orbit[1]));
			processNeighbor(~nProc, invs, ~hecke, idx :
					BeCareful := BeCareful,
					weight := orbit[2]);
		    end for;
		else
		    while nProc`isoSubspace ne [] do
			processNeighbor(~nProc, invs, ~hecke, idx :
				    BeCareful := BeCareful);
		    end while;
		end if;
	end for;

	return hecke;
end function;

procedure processNeighborDebug(~nProc, invs, ~iso_classes :
			  BeCareful := true)
    // Build the neighbor lattice corresponding to the
    //  current state of nProc.
    nLat := BuildNeighbor(nProc : BeCareful := BeCareful);

    // Compute the invariant of the neighbor lattice.
    inv := Invariant(nLat);

    // Retrieve the array of isometry classes matching this
    //  invariant.
    array := invs[inv];

    // Isometry testing is only necessary if the array has
    //  length larger than 1.
    if #array ne 1 then
	// Flag to determine whether an isometry class
	//  was actually found. This is a failsafe.
	found := false;
	
	for j in [1..#array] do
	    // Check for isometry.
	    iso := IsIsometric(nLat, array[j][1]);
	    
	    // If isometric, flag as found,
 	    //  increment Hecke matrix, and move on.
	    if iso then
		found := true;
		iso_classes[nProc`isoSubspace] :=  array[j][2];
		continue;
	    end if;
	end for;

	// Verify that the neighbor was indeed isometric
	//  to something in our list.
	assert found;
    else
	// Array length is one, and therefore conclude
	//  that nLat is isometric to the only entry in
	//  the array.
	iso_classes[nProc`isoSubspace] := array[1][2];
    end if;
    
    // Update nProc in preparation for the next neighbor
    //  lattice.
    nProc := GetNextNeighbor(nProc
			     : BeCareful := BeCareful);
end procedure;

// idx is i from the paper

procedure processNeighborWeight(~nProc, invs, ~hecke,
				idx, H :
				BeCareful := true, weight := 1)
    // Build the neighbor lattice corresponding to the
    //  current state of nProc.
    nLat := BuildNeighbor(nProc : BeCareful := BeCareful);

    if GetVerbose("AlgebraicModularForms") ge 2 then
	printf "Processing neighbor corresponding to isotropic subspace ";
	printf "indexed by %o.\n", nProc`isoSubspace;
	if GetVerbose("AlgebraicModularForms") ge 3 then
	    printf "Lattice is %o\n", nLat;
	end if;
    end if;

    // Compute the invariant of the neighbor lattice.
    inv := Invariant(nLat);

    // Retrieve the array of isometry classes matching this
    //  invariant.
    array := invs[inv];

    // Flag to determine whether an isometry class
    //  was actually found. This is a failsafe.
    found := false;

    iota := H[idx]`embedding;
    
    W := Codomain(iota);
    
    for j in [1..#array] do
	// Check for isometry.
	iso, g := IsIsometric(nLat, array[j][1]);

	// If isometric, flag as found,
	//  increment Hecke matrix, and move on.
	if iso then
	    space_idx := array[j][2];
	    
	    if GetVerbose("AlgebraicModularForms") ge 2 then
		printf "Neighbor is isometric to genus %o.\n", space_idx;
	    end if;
	    
	    // calculating gamma_i_j, for i = idx, j the index of the
	    // p-neighbor (nLat), and j* = space_idx 
	    g_pulled := Transpose(PullUp(Matrix(g), nLat, array[j][1] :
			   BeCareful := BeCareful));
	    gg := W`G!ChangeRing(g_pulled, BaseRing(W`G));

	    if GetVerbose("AlgebraicModularForms") ge 2 then
		print "Updating the Hecke operator...";
	    end if;
	    
	    found := true;
	    iota := H[space_idx]`embedding;
	    for vec_idx in [1..Dimension(H[space_idx])] do
	    	vec := gg * (iota(H[space_idx].vec_idx));
		hecke[space_idx][vec_idx][idx] +:= weight * vec;
	    end for;
	    break;
	end if;
    end for;

    // Verify that the neighbor was indeed isometric
    //  to something in our list.
    assert found;
  
    // Update nProc in preparation for the next neighbor
    //  lattice.
    nProc := GetNextNeighbor(nProc
			     : BeCareful := BeCareful);
end procedure;

function HeckeOperatorCN1(M, pR, k
			  : BeCareful := true,
			    Estimate := false,
			    Orbits := false)
    /*
    // The genus representatives.
    reps := Representatives(Genus(M));

    if GetVerbose("AlgebraicModularForms") ge 2 then
	print "Calculating the automorphism groups Gamma_i...";
    end if;
    gamma_reps := [AutomorphismGroup(r) : r in reps];

    gammas := [sub<W`G| [Transpose(PullUp(Matrix(g), reps[i], reps[i] :
				BeCareful := BeCareful)) :
		       g in Generators(gamma_reps[i])]> : i in [1..#reps]];

    if GetVerbose("AlgebraicModularForms") ge 2 then
	printf "The sizes of the automorphism groups are %o.\n",
	       [#x : x in gammas];
	printf "Computing the fixed subspaces ";
	print "(space of algebraic modular forms)";
    end if;

    // !!! TODO : This should only be computed once.
    
    H := [FixedSubspace(gamma, W) : gamma in gammas];

    if GetVerbose("AlgebraicModularForms") ge 2 then	
	printf "Obtained spaces of dimensions %o.\n",
	       [Dimension(h) : h in H];
    end if;
*/
    hecke := [ [ [* M`W!0 : hh in M`H*] : vec_idx in [1..Dimension(h)]] :
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

    for idx in [1..#M`H] do
	if GetVerbose("AlgebraicModularForms") ge 2 then	
	    printf "Going over p-neighbors of genus rep. no. %o...\n",
		   idx;
	end if;
	// The current isometry class under consideration.
	L := reps[idx];

	// Build neighboring procedure for this lattice.
	nProc := BuildNeighborProc(L, pR, k
				   : BeCareful := BeCareful);

	if Orbits then
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

	    gens := [pMaximalBasis * g * pMaximalBasis^(-1) :
		     g in gens];

	    gens_modp := [[L`Vpp[pR]`proj_pR(x) : x in Eltseq(g)]
			  : g in gens];
		 
	    Aut := sub<GL(n, F) | gens_modp>;

	    // The isotropic orbit data.
	    isoOrbits := IsotropicOrbits(V, Aut, k);

	    for orbit in isoOrbits do
		// Skip to the neighbor associated to this orbit.
		nProc := SkipToNeighbor(nProc, Basis(orbit[1]));
		processNeighborWeight(~nProc, invs, ~hecke, idx, M`H:
					BeCareful := BeCareful,
					weight := orbit[2]);
	    end for;
	else
	    while nProc`isoSubspace ne [] do
		processNeighborWeight(~nProc, invs, ~hecke, idx, M`H :
				      BeCareful := BeCareful);
	    end while;
	end if;
    end for;

    iota := [h`embedding : h in M`H];
   
    mats := [[[Eltseq(hecke[space_idx][vec_idx][idx]@@iota[idx]) :
		      vec_idx in [1..Dimension(M`H[space_idx])]] :
	      space_idx in [1..#M`H]] : idx in [1..#M`H]];

    vert_blocks := [&cat mat : mat in mats];

    vert_mats := [* Matrix(blk) : blk in vert_blocks |
		  not IsEmpty(blk[1]) *];

    if IsEmpty(vert_mats) then return []; end if;

    // would have done a one liner, but there are universe issues
    ret := vert_mats[1];
    for idx in [2..#vert_mats] do
	ret := HorizontalJoin(ret, vert_mats[idx]);
    end for;
    
    return ret;
end function;

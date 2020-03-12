//freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: hecke-CN1.m (Implementation for computing Hecke matrices)

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

		    // something is wrong here - we get different invariant
		    // for things in the same orbit!!!
		    
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

//freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: genus-CN1.m (implementation file for genus computations)

   Implementation file for computing p-neighbors for genus computations

   03/06/20: added the procedure checkNextNeighbor, for easier debugging and flow

   02/28/20: started editing this file to add Unitary forms
 
 ***************************************************************************/

// imports

import "../modfrmalg/modfrmalg.m" : ModFrmAlgInit;
import "neighbor-CN1.m" : BuildNeighborProc, BuildNeighbor, GetNextNeighbor;
import "inv-CN1.m" : Invariant;

// functions

procedure checkNextNeighbor(nProc, buildNeighbor, ~invs, ~isoList
			   : BeCareful := true)

    // Compute the neighbor according to the current state
    //  of the neighbor procedure.
    nLat := buildNeighbor(nProc : BeCareful := BeCareful);

    // A specified invariant of the neighbor lattice.
    inv := Invariant(nLat);

    // If this invariaint is defined for the array, we need
    //  to potentially check for isometry.
    if IsDefined(invs, inv) then
       // Retrieve the array for this invariant.
       array := invs[inv];

       // Flag whether we found the right class.
       found := false;
       for i in [1..#array] do
	 // Check for isometry.
	 iso := IsIsometric(array[i][1], nLat);

         // Skip ahead if an isometry is found.
	 if iso then
	    found := true;
	    continue;
	 end if;
       end for;

       // If no isometry found, add it to the list.
       if not found then
         Append(~invs[inv], < nLat, #isoList+1 >);
	 Append(~isoList, nLat);
       end if;
    else
       invs[inv] := [ < nLat, #isoList+1 > ];
       Append(~isoList, nLat);
    end if;

end procedure;

function computeGenusRepsAt(p, isoList, invs
		: BeCareful := true, Force := false)
	// The index of the current isometry class being considered.
	isoIdx := 1;

	repeat
		// Build the neighbor procedure for the current lattice.
		nProc := BuildNeighborProc(isoList[isoIdx], p, 1
			: BeCareful := BeCareful);

		repeat
		        checkNextNeighbor(nProc, BuildNeighbor,
					   ~invs, ~isoList);
			// Move on to the next neighbor lattice.
			nProc := GetNextNeighbor(nProc
				: BeCareful := BeCareful);
		until nProc`isoSubspace eq [];

		// Move on to the next genus representative.
		isoIdx +:= 1;
	until isoIdx gt #isoList;

	return isoList, invs;
end function;

procedure computeGenusRepsCN1(M : BeCareful := true, Force := false)
	// Do not compute the genus representatives if they've already been
	//  computed and we aren't forcing a recomputation.
	if not Force and assigned M`genus then return; end if;

	// An upper bound for the norm of the primes at which we seek to
	//  compute genus reps.
	upTo := 0;

	// The list of genus representatives. We initialize this list with
	//  the standard lattice with respect to our inner form.
	genList := [ Module(M) ];

	// Initialize the associative array hashed by an invariant. This will
	//  allow us to reduce the number of isometry tests required to
	//  determine equivalence.
	invs := AssociativeArray();
	invs[Invariant(Module(M))] := [ < Module(M), 1 > ];

	repeat
		repeat
			// Increment norm by 10.
			upTo +:= 10;

			// Compute a list of primes which do not divide the
			//  discriminant of the lattice.
			ps := [ p : p in PrimesUpTo(upTo, BaseRing(M)) |
				Gcd(Integers()!Norm(Discriminant(Module(M))),
					Norm(p)) eq 1 ];
		until #ps ne 0;

		idx := 1;
		repeat
			// Compute genus representatives at a specific prime.
			genList, invs := computeGenusRepsAt(
				ps[idx], genList, invs
				: BeCareful := BeCareful, Force := Force);

			// Move to the next prime.
			idx +:= 1;
		until true;
	until true;
	// TODO: Replace the last two until statements with the appropriate
	//  conditions to check the mass formula to see if we need to compute
	//  genus representatives at multiple primes.

	// Assign the genus symbol for the space of algebraic modular forms.
	M`genus := New(GenusSym);
	M`genus`Representative := M`L;
	M`genus`Representatives := genList;
	M`genus`RepresentativesAssoc := invs;
end procedure;

function sortGenusCN1(genus)
	// An empty associative array.
	invs := AssociativeArray();

	// An ordered list of genus representatives;
	lats := Representatives(genus);

	for i in [1..#lats] do
		// Compute the invariant associated to this genus rep.
		inv := Invariant(lats[i]);

		// Assign an empty list to the invariant hash if it hasn't been
		//  assigned yet.
		if not IsDefined(invs, inv) then invs[inv] := []; end if;

		// Add to list.
		Append(~invs[inv], < lats[i], i >);
	end for;

	// Assign the representatives associated array.
	genus`RepresentativesAssoc := invs;

	return genus;
end function;


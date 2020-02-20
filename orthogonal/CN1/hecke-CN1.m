// Implementation for computing Hecke matrices over the rationals.

import "inv-CN1.m" : Invariant;
import "neighbor-CN1.m" : BuildNeighborProc, BuildNeighbor,
	GetNextNeighbor;

// TODO: Add estimate functionality (mirror the implementation in hecke-QQ.m).
function HeckeOperatorTrivialWeightCN1(M, pR, k
		: BeCareful := true, Estimate := false)
	// The genus representatives.
	reps := Representatives(Genus(M));

	// The dimension of the Hecke matrix.
	dim := #reps;

	// Initilize the Hecke matrix.
	hecke := Zero(MatrixRing(Integers(), dim));

	// An associative array indexed by a specified invariant of an isometry
	//  class. This data structure allows us to bypass a number of isometry
	//  tests by filtering out those isometry classes whose invariant
	//  differs from the one specified.
	invs := M`genus`RepresentativesAssoc;

	for idx in [1..dim] do
		// The current isometry class under consideration.
		L := reps[idx];

		// Build neighboring procedure for this lattice.
		nProc := BuildNeighborProc(L, pR, k
			: BeCareful := BeCareful);

		while nProc`isoSubspace ne [] do
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
						hecke[array[j][2]][idx] +:= 1;
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
				hecke[array[1][2]][idx] +:= 1;
			end if;

			// Update nProc in preparation for the next neighbor
			//  lattice.
			nProc := GetNextNeighbor(nProc
				: BeCareful := BeCareful);
		end while;
	end for;

	return hecke;
end function;


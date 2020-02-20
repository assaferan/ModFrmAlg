// Implementation for computing Hecke matrices over the rationals.

import "inv-QQ.m" : Invariant;
import "neighbor-QQ.m" : BuildNeighborProc, BuildNeighbor,
	GetNextNeighbor, SkipToNeighbor;

function HeckeOperatorTrivialWeightQQ(M, p, k
		: BeCareful := true, Estimate := false, UseLLL := true)
	// The representatives of the genus.
	reps := Representatives(Genus(M));

	// Determine the underlying isogeny type.
	Special := IsSpecialOrthogonal(M);

	// The dimension of the Hecke matrix.
	dim := #reps;

	// Initilize the Hecke matrix.
	hecke := Zero(MatrixRing(Integers(), dim));

	// An associative array indexed by a specified invariant of an isometry
	//  class. This data structure allows us to bypass a number of isometry
	//  tests by filtering out those isometry classes whose invariant
	//  differs from the one specified.
	invs := M`genus`RepresentativesAssoc;

	// The dimension of the quadratic space.
	n := Dimension(QuadraticSpace(Module(M)));

	// TODO: Adapt `NumberOfNeighbors' routine to count isotropic subspaces
	//  for bad primes.

	// Routine for estimating the amount of time it will take to compute
	//  this Hecke operator.
	if Estimate then
		count := 0;
		fullCount := dim * NumberOfNeighbors(M, p, k);
		start := Realtime();
	end if;

	for idx in [1..dim] do
		// The current isometry class under consideration.
		L := reps[idx];

		// Build neighboring procedure for this lattice.
		nProc := BuildNeighborProc(L, p, k : BeCareful := BeCareful);

		while nProc`isoSubspace ne [] do
			// Build the neighbor lattice corresponding to the
			//  current state of nProc.
			nLat := BuildNeighbor(nProc
				: BeCareful := BeCareful, UseLLL := UseLLL,
					Special := Special);

			// Increment counter.
			if Estimate then count +:= 1; end if;

			// Compute the invariant for this neighbor lattice.
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
					iso := IsIsometric(M,nLat,array[j][1]);

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

			if Estimate and count mod 100000 eq 300 then
				// Elapsed real time.
				elapsed := Realtime() - start;

				// Seconds per neighbor computation.
				t := RealField()!(elapsed / count);

				// Number of neighbors left to compute.
				remaining := fullCount - count;

				// Estimate time remaining (in seconds).
				estimate := t * remaining;

				// Minutes remaining.
				mins := Floor(estimate / 60);

				// Seconds (modulo minutes) remaining.
				secs := Floor(estimate - mins*60);

				// Hours remaining.
				hours := Floor(mins / 60);

				// Minutes (modulo hours) remaining.
				mins -:= hours * 60;

				// Days remaining.
				days := Floor(hours / 24);

				// Hours (modulo days) remaining.
				hours -:= days * 24;

				// Display estimate.
				printf "Estimated time remaining:" cat
					" %od %oh %om %os\n",
					days, hours, mins, secs;
			end if;

			// Update nProc in preparation for the next neighbor
			//  lattice.
			nProc := GetNextNeighbor(nProc
				: BeCareful := BeCareful);
		end while;
	end for;

	return hecke;
end function;

function HeckeOperatorTrivialWeightViaOrbits(M, p, k
		: BeCareful := true, Estimate := false, UseLLL := true)
	// The representatives of the genus.
	reps := Representatives(Genus(M));

	// Determine the underlying isogeny type.
	Special := IsSpecialOrthogonal(M);

	// The dimension of the Hecke matrix.
	dim := #reps;

	// Initilize the Hecke matrix.
	hecke := Zero(MatrixRing(Integers(), dim));

	// An associative array indexed by a specified invariant of an isometry
	//  class. This data structure allows us to bypass a number of isometry
	//  tests by filtering out those isometry classes whose invariant
	//  differs from the one specified.
	invs := M`genus`RepresentativesAssoc;

	// The dimension of the quadratic space.
	n := Dimension(QuadraticSpace(Module(M)));

	for idx in [1..dim] do
		// The current isometry class under consideration.
		L := reps[idx];

		// Build neighboring procedure for this lattice.
		nProc := BuildNeighborProc(L, p, k : BeCareful := BeCareful);

		// The affine vector space.
		V := nProc`L`Vpp[p]`V;

		// The base field.
		F := BaseRing(V);

		// The automorphism group restricted to the affine space.
		Aut := ChangeRing(AutomorphismGroup(reps[idx]),F);

		// The isotropic orbit data.
		isoOrbits := Orbits(V, Aut);

		for orbit in isoOrbits do
			// Skip to the neighbor associated to this orbit.
			nProc := SkipToNeighbor(nProc, Basis(orbit[1])[1]);

			// Build the neighbor lattice corresponding to the
			//  current state of nProc.
			nLat := BuildNeighbor(nProc
				: BeCareful := BeCareful, UseLLL := UseLLL,
					Special := Special);

			// Compute the invariant for this neighbor lattice.
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
					iso := IsIsometric(M,nLat,array[j][1]);

					// If isometric, flag as found,
					//  increment Hecke matrix, and move on.
					if iso then
						found := true;
						hecke[array[j][2]][idx]
							+:= orbit[2];
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
				hecke[array[1][2]][idx] +:= orbit[2];
			end if;

			// Update nProc in preparation for the next neighbor
			//  lattice.
			nProc := GetNextNeighbor(nProc
				: BeCareful := BeCareful);
		end for;
	end for;

	return hecke;
end function;


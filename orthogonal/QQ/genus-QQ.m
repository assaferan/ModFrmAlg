// All genus-related computations.

import "../../structure/modfrmalg.m" : ModFrmAlgInit;
import "inv-QQ.m" : Invariant;
import "neighbor-QQ.m" : BuildNeighborProc, BuildNeighbor,
	GetNextNeighbor, SkipToNeighbor;

/* Experimental. */
intrinsic Mass1(M::ModFrmAlg) -> FldRatElt
{ Computes the mass formula using local data. }
	require M`L`quadSpace`dim eq 3: "Must be ternary for now...";
	mat := ChangeRing(M`L`quadSpace`innerForm, Integers());
	disc := Norm(Discriminant(M`L));
	ps := PrimeFactors(disc);

	function loc(p)
		w := WittInvariant(mat, p) * HilbertSymbol(-1, -disc, p);
		ord := Valuation(disc, p) mod 2;
		if ord eq 1 then return (p + w) / 2; end if;
		return w eq 1 select 1 else (p-1)/2;
	end function;

	return &*[ loc(p) : p in ps ] / 12;
end intrinsic;

/* Experimental. */
intrinsic Mass2(M::ModFrmAlg) -> FldRatElt
{ Computes the mass formula using local data. }
	require M`L`quadSpace`dim eq 3: "Must be ternary for now...";
	_ := GenusReps(M);
	return 2 * &+[ 1 / #AutomorphismGroup(L) 
		: L in M`genus`Representatives ];
end intrinsic;

function computeGenusRepsViaOrbitsAt(p, isoList, invs, M : BeCareful := true,
		Force := false);
	// The index of the current isometry class being considered.
	isoIdx := 1;

	// Determine the underlying isogeny type.
	Special := IsSpecialOrthogonal(M);

	repeat
		// Build the neighbor procedure for the current lattice.
		nProc := BuildNeighborProc(isoList[isoIdx], p, 1
			: BeCareful := BeCareful);

		// The quadratic space.
		V := nProc`L`Vpp[p]`V;

		// The affine field.
		F := BaseRing(V);

		// The automoprhism group of our lattice.
		Aut := ChangeRing(AutomorphismGroup(isoList[isoIdx]), F);

		// Function used for computing norm.
		function norm(v)
			v := Matrix(v);
			if Characteristic(F) ne 2 then
				return (v * V`GramMatrix * Transpose(v))[1,1];
			else
				return Evaluate(V`Q, Eltseq(v));
			end if;
		end function;

		// The isotropic orbit data.
		isoOrbits := Orbits(V, Aut);

		// The isotropic orbit index.
		idx := 1;

		repeat
			// Assign the next isotropic subspace.
			nProc := SkipToNeighbor(nProc,
				Basis(isoOrbits[idx][1])[1]
					: BeCareful := BeCareful);

			// Compute the neighbor according to the current state
			//  of the neighbor procedure.
			nLat := BuildNeighbor(nProc
				: BeCareful := BeCareful, Special := Special);

			// A special invariant of the neighbor lattice.
			inv := Invariant(nLat);

			// If the invariant exists in the array, we may need
			//  to do some isometry testing.
			if IsDefined(invs, inv) then
				// Retrive the array for this invariant.
				array := invs[inv];

				// Flag whether we found the array.
				found := false;

				for i in [1..#array] do
					// Check for isometry.
					iso := IsIsometric(M,array[i][1],nLat);

					// Skip ahead if an isometry is found.
					if iso then
						found := true;
						continue;
					end if;
				end for;

				// If no isometry is found, add it to the list.
				if not found then
					Append(~invs[inv],
						< nLat, #isoList+1 >);
					Append(~isoList, nLat);
				end if;
			else
				// Invariant was not found, add it to the list.
				invs[inv] := [ < nLat, #isoList+1 > ];
				Append(~isoList, nLat);
			end if;

			// Increment the isotropic orbit index.
			idx +:= 1;
		until idx gt #isoOrbits;

		isoIdx +:= 1;
	until isoIdx gt #isoList;

	return isoList, invs;
end function;

function computeGenusRepsAt(p, isoList, invs, M
		: BeCareful := true, Force := false)
	// The index of the current isometry class being considered.
	isoIdx := 1;

	// Determine the underlying isogeny type.
	Special := IsSpecialOrthogonal(M);

	repeat
		// Build the neighbor procedure for the current lattice.
		nProc := BuildNeighborProc(isoList[isoIdx], p, 1
			: BeCareful := BeCareful);

		repeat
			// Compute the neighbor according to the current state
			//  of the neighbor procedure.
			nLat := BuildNeighbor(nProc
				: BeCareful := BeCareful, Special := Special);

			// A specific invariant of the neighbor lattice.
			inv := Invariant(nLat);

			// If the invariant exists in the array, we may need
			//  to do some isometry testing.
			if IsDefined(invs, inv) then
				// Retrive the array for this invariant.
				array := invs[inv];

				// Flag whether we found the array.
				found := false;

				for i in [1..#array] do
					// Check for isometry.
					iso := IsIsometric(M,array[i][1],nLat);

					// Skip ahead if an isometry is found.
					if iso then
						found := true;
						continue;
					end if;
				end for;

				// If no isometry is found, add it to the list.
				if not found then
					Append(~invs[inv],
						< nLat, #isoList+1 >);
					Append(~isoList, nLat);
				end if;
			else
				// Invariant was not found, add it to the list.
				invs[inv] := [ < nLat, #isoList+1 > ];
				Append(~isoList, nLat);
			end if;

			// Move on to the next neighbor lattice.
			nProc := GetNextNeighbor(nProc
				: BeCareful := BeCareful);
		until nProc`isoSubspace eq [];

		// Move on to the next isometry class.
		isoIdx +:= 1;
	until isoIdx gt #isoList;

	return isoList, invs;
end function;

procedure computeGenusRepsQQ(M : BeCareful := true, Force := false,
		Orbits := false)
	// Do not compute anything if we aren't required to.
	if not Force and assigned M`genus then return; end if;

	// An upper bound for the norm of the primes at which we seek to
	//  compute genus reps.
	upTo := 0;

	// The underlying quadratic space.
	Q := QuadraticSpace(Module(M));

	// The dimension.
	dim := Dimension(Q);

	// The standard basis for the initial lattice.
	basis := Id(MatrixRing(Rationals(), dim));

	// The inner form.
	gram := ChangeRing(InnerForm(Q), Rationals());

	// The defining lattice as a native Lat.
	L := ZLattice(Module(M));

	// The list of genus representatives. We initialize this list with
	//  the lattice used to define the space of algebraic modular forms.
	genList := [ LLL(ZLattice(Module(M))) ];

	// Initialize the associaitive array hashed by an invariant. This will
	//  allow us to reduced the number of isometry tests required to
	//  determine equivalence.
	invs := AssociativeArray();
	invs[Invariant(L)] := [ < L, 1 > ];

	// Determine the primes required to compute all genus representatives.
	//  This routine takes the spinor genus into consideration to determine
	//  those primes.
	ps := CriticalPrimes(Module(M));

	if #ps eq 0 then
		repeat
			// Increment norm by 10.
			upTo +:= 10;

			// Compute a list of primes which do not divide the
			//  discriminant of the lattice.
			ps := [ p : p in PrimesUpTo(upTo) | Gcd(p, Integers()!
				Norm(Discriminant(Module(M)))) eq 1 ];
		until #ps ne 0;

		// If there were no critical primes found, we will just choose
		//  the smallest prime coprime to the discriminant.
		ps := [ ps[1] ];
	else
		// Since we're in the rational case, we just need the prime
		//  number.
		ps := [ Norm(p) : p in ps ];
	end if;

	// Compute the neighbors for each prime in our list of primes.
	for p in ps do
		if Orbits then
			// Compute genus representatives at a specific
			//   prime using the line orbit method.
			genList, invs := computeGenusRepsViaOrbitsAt(
				p, genList, invs, M
				: BeCareful := BeCareful,
					Force := Force);
		else
			// Compute genus representatives at a specific
			//  prime.
			genList, invs := computeGenusRepsAt(
				p, genList, invs, M
				: BeCareful := BeCareful,
					Force := Force);
		end if;
	end for;

	// Assign the rational genus symbol for this space.
	M`genus := New(GenusSym);
	M`genus`Representative := genList[1];
	M`genus`Representatives := genList;
	M`genus`RepresentativesAssoc := invs;
end procedure;

function sortGenusQQ(genus)
	// An empty associative array.
	invs := AssociativeArray();

	// An ordered list of genus representatives.
	lats := genus`Representatives;

	for i in [1..#lats] do
		// Compute the invariant associated to this genus rep.
		inv := Invariant(lats[i]);

		// Assign an empty list to the invariant hash if it hasn't been
		//  assigned yet.
		if not IsDefined(invs, inv) then invs[inv] := []; end if;

		// Add to list.
		Append(~invs[inv], < lats[i], i >);
	end for;

	// Assign the representative associative array.
	genus`RepresentativesAssoc := invs;

	return genus;
end function;


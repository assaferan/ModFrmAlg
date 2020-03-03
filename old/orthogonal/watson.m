// At the moment - this file is not being used as it causes
// crashes when loading the library more than once

// Watson transformation

import "lattice.m" : pMaximalGram;

intrinsic Watson(L::ModDedLat, pR::RngOrdIdl : BeCareful := true) -> ModDedLat
{ Compute the Watson transformation at a prime. }
	// Make sure that the specificed ideal is prime.
	require IsPrime(pR) : "Specified ideal must be prime.";

	// Get the residue class field and its associated projection map.
	Fp, map := ResidueClassField(pR);

	// Make sure that the specified prime is odd.
	// TODO: Allow for computing the Watson transformation at even primes.
	require Characteristic(Fp) ne 2 : "Specified prime must be odd.";

	// Backup copy of the original lattice.
	originalL := L;

	// The base ring.
	R := BaseRing(L);

	// The global quadratic space.
	Q := QuadraticSpace(L);

	// The base field of the quadratic space.
	F := BaseRing(Q);

	// Retrieve the Gram matrix and the basis for this Gram matrix.
	pMaxGram, pMaxBasis := pMaximalGram(L, pR);

	// Retrieve the p-standard Gram matrix as well as the p-standard basis.
	V := BuildQuadraticSpace(map(pMaxGram));

	// Dimension of the affine quadratic space.
	n := Dimension(V);

	// If there is no radical, Watson acts trivially.
	if V`RadDim eq 0 then return L; end if;

	// If the entire space is the radical, return the unaltered lattice.
	if V`RadDim ne n then
		// Basis of the affine radical in the original coordinate basis.
		radBasis := [ Transpose(V`Basis)[i] : i in [n-V`RadDim+1..n] ];

		// Pull this basis back to the global vector space.
		radBasis := [ Vector(vec @@ map) : vec in radBasis ];

		// Express this radical basis in terms of the pMaximal basis.
		radBasis := [ &+[ vec[i] * pMaxBasis[i] : i in [1..n] ]
			: vec in radBasis ];

		if BeCareful then
			// The preimage of the radical basis as a matrix.
			rad := Matrix(radBasis);

			// The global Gram matrix associated to the radical.
			temp := rad * InnerForm(Q) * Transpose(rad);

			// The projected Gram matrix of the radical.
			temp := map(temp);

			// Verify that the Gram matrix is indeed zero.
			assert &and[ e eq 0 : e in Eltseq(temp) ];

			// Make sure that these vectors belong to the lattice.
			assert &and[ vec in Module(L) : vec in radBasis ];
		end if;

		// Basis for the Hermite Normal Form in the appropriate ring.
		basis := Matrix(radBasis cat [ pb[2] : pb in PseudoBasis(L) ]);

		// Ideals for the Hermite Normal Form.
		idls := [ 1*R^^#radBasis ] cat
			[ pR * pb[1] : pb in PseudoBasis(L) ];

		// Compute the Watson transformed lattice.
		L := LatticeWithPseudobasis(Q,
			HermiteForm(PseudoMatrix(idls, basis)));

		// The pMaximal Gram matrix and its associated basis.
		pMaxGram, pMaxBasis := pMaximalGram(L, pR);
	end if;

	// A uniformizing element of pR.
	pi := SafeUniformizer(pR);

	// Divide the pMaximal Gram matrix by the uniformizer over the field.
	pMaxGram := ChangeRing(pMaxGram, F) / pi;

	// Scale the pMaximal Gram matrix so that it is integral.
	repeat
		// Determine the bad elements, if any.
		bad := [ e : e in Eltseq(pMaxGram) | Denominator(e) ne 1 ];

		// If there are bad elements, clear denominators.
		if #bad ne 0 then
			pMaxGram *:= Denominator(bad[1]);
		end if;
	until #bad eq 0;

	// Push the pMaximal Gram back down to the base ring.
	pMaxGram := ChangeRing(pMaxGram, R);

	// Compute the affine quadratic space.
	V := BuildQuadraticSpace(map(pMaxGram));

	if V`RadDim eq 0 then
		print "No radical. This shouldn't be happening...";
		assert false;
	elif V`RadDim eq n then
		// NOTE: the radical is the entire affine space, so the Watson
		//  transformation is simply (1/p)*L.

		// The pseudobasis.
		psBasis := PseudoBasis(L);

		// The basis.
		basis := Matrix([ pb[2] : pb in psBasis ]);

		// The ideals scaled by pR^-1;
		idls := [ pR^-1 * pb[1] : pb in psBasis ];

		// The Watson transformed lattice.
		L := LatticeWithBasis(Q, basis, idls);

		// Return it.
		return L;
	end if;

	// The radical basis in the original coordinates.
	radBasis := [ Transpose(V`Basis)[i] : i in [n-V`RadDim+1..n] ];

	// The p-radical in original coordinates.
	radBasis := [ Vector(vec @@ map) : vec in radBasis ];

	// The p-radical in terms of the pMaximal basis.
	radBasis := [ &+[ vec[i] * pMaxBasis[i] : i in [1..n] ]
		: vec in radBasis ];

	// Verify that each vector belongs to the original lattice L.
	assert &and[ vec in Module(L) : vec in radBasis ];

	// Prepare the basis for Hermite Normal Form.
	basis := Matrix(radBasis cat [ pb[2] : pb in PseudoBasis(L) ]);

	// Prepare the ideals for Hermite Normal Form. Normally we'd scale the
	//  radical basis by 1*R and the rest by pR, but since the Watson
	//  transformation is defined to be the pR^-1 scale of the second
	//  iteration, we scale as follows...
	idls := [ (pR^-1)^^#radBasis ] cat [ pb[1] : pb in PseudoBasis(L) ];

	// Compute the Watson transformation.
	L := LatticeWithPseudobasis(Q, HermiteForm(PseudoMatrix(idls, basis)));

	return L;
end intrinsic;

intrinsic Watson(L::Lat, p::RngIntElt : BeCareful := true) -> ModDedLat
{ Compute the Watson transformation at a prime. }
	return Watson(LatticeFromLat(L), p);
end intrinsic;

intrinsic Watson(M::ModFrmAlg, pR::RngOrdIdl : BeCareful := true)
	-> ModDedLat
{ Compute the Watson transformation at a prime. }
	return Watson(Module(M), pR : BeCareful := BeCareful);
end intrinsic;

intrinsic Watson(L::ModDedLat, p::RngIntElt : BeCareful := true)
	-> ModDedLat
{ Compute the Watson transformation at a prime. }
	return Watson(L, ideal< BaseRing(L) | p > : BeCareful := BeCareful);
end intrinsic;

intrinsic Watson(M::ModFrmAlg, p::RngIntElt : BeCareful := true)
	-> ModDedLat
{ Compute the Watson transformation at a prime. }
	return Watson(Module(M), p : BeCareful := BeCareful);
end intrinsic;

intrinsic Watson(M::ModFrmAlg, pR::RngOrdIdl : BeCareful := true)
	-> ModDedLat
{ Compute the Watson transformation at a prime. }
	return Watson(Module(M), pR : BeCareful := BeCareful);
end intrinsic;


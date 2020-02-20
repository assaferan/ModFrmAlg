// The intention of this script is to compute the spinor norm of a lattice at
//  a specified prime ideal. The spinor norm is a subgroup of the square class
//  group K_p^\ast / (K_p^\ast)^2, represented as a GF(2)-vector space V of the
//  appropriate dimension. Associated to this vector space, we also have a map
//  V -> K which sends vectors in V to elements of K which represent the square
//  classes. The structure of the vector space is such that the last ordered
//  basis vector (0 .. 0 1) represents the square class associated to the
//  primitive element of the prime ideal.

forward MakeGoodBONG, IsInA, HasPropertyA, G_function;

function getSpinorNorm(L, pR)
	// Retrieve the local squares group, as well as the map g : V -> R.
	V, g := LocalSquareGroup(pR);

	// The dimension of V, this indicates that the square class group has
	//  precisely 2^dim elements, i.e. the square class group is isomorphic
	//  to (Z/2Z)^dim.
	dim := Dimension(V);

	// All vectors representing elements in the local square group having
	//  pR-adic order equal to zero.
	units := sub< V | [ V.i : i in [1..dim-1] ] >;

	// The residue class field at this prime.
	F := ResidueClassField(pR);

	if Characteristic(F) ne 2 then
		// Retrieve the Jordan constituents as well as the order of the
		//  pR-adic orders of each constituent.
		cons, ords := JordanDecomp(L, pR);

		// If any of the Jordan constituents have dimension two or
		//  higher, then we get one of two spinor norms: the adic units
		//  or the full local square group. If the parity of the
		//  pR-adic orders of each constituent are the same, then we
		//  get the units; otherwise, we get the full group.

		// TODO: Confirm the validity of this statement. Something
		//  seems amiss here...
		if &or[ #con ge 2 : con in cons ] then
			if #{ ord mod 2 : ord in ords } lt 2 then
				return units, true;
			else
				return V, false;
			end if;
		end if;

		// We are now in the rare case where each Jordan constituent is
		//  one-dimensional, and must be handled separately from the
		//  previous case.

		// The inner form of the underlying quadratic space.
		M := InnerForm(QuadraticSpace(L));

		// The norms of each one-dimensional constituent.
		norms := [ (Matrix(con[1]) * M * Transpose(Matrix(con[1])))[1,1]
			: con in cons ];

		// The pairwise product of each of the norms provides a
		//  generator for the spinor subgroup.
		gens := [ norms[i] * norms[j] : i, j in [1..#norms] | i lt j ];

		// Pulling back these generators into the vector space V, we
		//  can then use these generators to build the spinor norm
		//  subgroup.
		vecs := [ x @@ g : x in gens ];

		// Build the spinor norm subgroup from these vectors.
		spin := sub< V | vecs >;
	else
		// Build a basis of norm generators (BONG) for the local
		//  lattice at the specified prime.
		BONG := MakeGoodBONG(L, pR);

		// The quotient of adjacent norm generators.
		quos := [ BONG[i+1] / BONG[i] : i in [1..#BONG-1] ];

		// The pR-adic orders of each element in the BONG.
		ords := [ Valuation(BONG[i], pR) : i in [1..#BONG] ];

		// Check whether this lattice has property A according to Beli,
		//  Definition 7, pg. 148.
		if not HasPropertyA(L, pR) then
			// The spinor norm for this lattice is either the adic
			//  units or the entire group. We will now determine
			//  which case we fall into. We will utilize Beli,
			//  Theorem 3, pg. 181 to do so.

			// The ramification index of the prime ideal.
			e := RamificationIndex(pR);

			for quo in quos do
				// The generators of the image of G.
				basis := Basis(G_function(quo, pR, V, g));

				// If a primitive element appears in the image
				//  of G(quo), then we must have the full
				//  local square class group.
				if &or[ x[dim] ne 0 : x in basis ] then
					return V, false;
				end if;
			end for;

			// We have now met condition (i) from Theorem 3
			//  from Beli.

			// We now check condition (ii), noting that &and[] is
			//  true by definition.
			if &and[ ((ords[i+1] - ords[i]) div 2) mod 2 eq e mod 2
				: i in [1..dim-2] | ords[i] eq ords[i+2] ] then
					return units, true;
			end if;

			return V, false;
		end if;

		// We now assume that L has property A according to Beli, hence
		//  the Jordan decomposition is a maximal norm splitting. This
		//  makes certain things a bit easier.

		// Build the part of the spinor norm which is provided by the
		//  quotient of adjacent norm generators. See Beli, Theorem 1,
		//  pg. 159.
		span := &+[ G_function(quo, pR, V, g) : quo in quos ];

		// Compute the value of alpha, according to Beli, Theorem 1.
		alpha := Min([ Floor((ords[i+2] - ords[i]) / 2)
			: i in [1..#BONG-2] ]);

		// A primitive element of pR.
		pi := PrimitiveElement(pR);

		// Compute the spinor norm according to Beli.
		spin := span + sub< V | (1 + pi^alpha) @@ g >;
	end if;

	// Return the spin group as well as a flag indicating whether this is
	//  the full subgroup of pR-adic units.
	return spin, spin eq units;
end function;

intrinsic SpinorNorm_2(L::ModDedLat, pR::RngOrdIdl) -> ModTupFld, BoolElt
{ Computes the spinor norm of L at the prime pR as a subgroup of a GF(2)-vector
space (as described in the header to this file. }
	// Ensure that the specified ideal is prime.
	require IsPrime(pR): "The specified ideal must be prime.";

	// The base ring.
	R := BaseRing(L);

	// Ensure that the base ring of the lattice is the same as that of the
	//  specified prime ideal.
	require R eq Order(pR): "The base ring of the lattice does not match the order of the ideal.";

	// Check whether the SpinorNorm attribute has been assigned.
	if assigned L`SpinorNorm then
		// If so, check whether we've computed it at this prime yet.
		if IsDefined(L`SpinorNorm, pR) then
			// Recover the data, and return it.
			temp := L`SpinorNorm[pR];
			return temp[1], temp[2];
		end if;
	end if;

	// Compute the spinor norm for this lattice at this prime.
	spin, exactlyUnits := getSpinorNorm(L, pR);

	// If the SpinorNorm attribute not yet assigned, create it.
	if not assigned L`SpinorNorm then
		L`SpinorNorm := AssociativeArray();
	end if;

	// Save the spinor norm for future usage.
	L`SpinorNorm[pR] := < spin, exactlyUnits >;

	return spin, exactlyUnits;
end intrinsic;

intrinsic SpinorNorm_2(M::ModFrmAlg, pR::RngOrdIdl) -> ModTupFld, BoolElt
{ Computes the spinor norm of L at the prime pR as a subgroup of a GF(2)-vector
space (as described in the header to this file. }
	return SpinorNorm_2(Module(M), pR);
end intrinsic;

intrinsic SpinorNorm_2(L::ModDedLat, pR::RngInt) -> ModTupFld, BoolElt
{ Computes the spinor norm of L at the prime pR as a subgroup of a GF(2)-vector
space (as described in the header to this file. }
	return SpinorNorm_2(L, ideal< BaseRing(L) | Norm(pR) >);
end intrinsic;

intrinsic SpinorNorm_2(M::ModFrmAlg, pR::RngInt) -> ModTupFld, BoolElt
{ Computes the spinor norm of L at the prime pR as a subgroup of a GF(2)-vector
space (as described in the header to this file. }
	return SpinorNorm_2(Module(M), ideal< BaseRing(Module(M)) | Norm(pR) >);
end intrinsic;

intrinsic SpinorNorm_2(L::ModDedLat, p::RngIntElt) -> ModTupFld, BoolElt
{ Computes the spinor norm of L at the prime pR as a subgroup of a GF(2)-vector
space (as described in the header to this file. }
	return SpinorNorm_2(L, ideal< BaseRing(L) | p >);
end intrinsic;

intrinsic SpinorNorm_2(M::ModFrmAlg, p::RngIntElt) -> ModTupFld, BoolElt
{ Computes the spinor norm of L at the prime pR as a subgroup of a GF(2)-vector
space (as described in the header to this file. }
	return SpinorNorm_2(Module(M), ideal< BaseRing(Module(M)) | p >);
end intrinsic;

// This function calculates a "good BONG" for the lattice L considered locally
//  at the prime pR. See Beli for a definition of a BONG.
function MakeGoodBONG(L, pR)
	// Sanity check. Being terse here since this is for internal use only.
	assert Order(pR) eq BaseRing(L) and IsPrime(pR) and Minimum(pR) eq 2;

	// Retrieve a maximal norm splitting for the local lattice at pR.
	bases, ords := JordanDecomp(L, pR : MaxSplit := true);

	// Confirm that this is, indeed, a maximal norm splitting. See Beli,
	//  pg. 148 for the definition of maximal norm splitting used here.
	assert &and[ ords[i] le ords[i+1] : i in [1..#ords-1] ];

	// The inner form for the quadratic space.
	M := InnerForm(QuadraticSpace(L));

	// The Gram matrices for each individual block of the maximal splitting.
	Gs := [* Matrix(b) * M * Transpose(Matrix(b)) : b in bases *];

	// The bases of norm generators as a sequence of elements.
	BONG := [];

	for i in [1..#Gs] do
		// The Gram matrix under consideration during this iteration.
		G := Gs[i];

		if Nrows(G) eq 1 then
			// One-dimensional lattices have norm generators given
			//  by (half) the only element of its Gram matrix.
			Append(~BONG, G[1,1] / 2);
		else
			if Valuation(G[1,1] / 2, pR) eq ords[i] then
				// The norm of the first basis vector.
				n := G[1,1] / 2;

				// Append the BONG for this binary lattice.
				BONG cat:= [ n, Determinant(G) / n ];

				// Skip the rest of this iteration.
				continue;
			elif Valuation(G[2,2] / 2, pR) eq ords[i] then
				// The first basis vector is not a norm
				//  generator, but the second one is, so we
				//  swap the bases.
				bases[i] := [ bases[i][2], bases[i][1] ];
			else
				// Neither basis vector is a norm generator,
				//  so add the second to the first so that the
				//  updated first basis is a norm generator.
				bases[i][1] +:= bases[i][2];
			end if;

			// The basis matrix.
			B := Matrix(bases[i]);

			// The Gram matrix for the updated binary lattice.
			G := B * M * Transpose(B);

			// The norm of the first basis vector.
			n := G[1,1] / 2;

			// Verify that the first basis is a norm generator.
			assert Valuation(n, pR) eq ords[i];

			// Append the BONG for this binary lattice.
			BONG cat:= [ n, Determinant(G) / n ];
		end if;
	end for;

	// Verify that this is a good BONG (see Beli, Definition 9).
	assert &and[ Valuation(BONG[i], pR) le Valuation(BONG[i+2], pR)
		: i in [1..Dimension(L)-2] ];

	return BONG;
end function;

// This function determines whether an element a belongs to the set A, as
//  defined by Beli, Lemma 3.5, pg. 134.
function IsInA(a, pR)
	// We only consider nonzero elements of the order of pR.
	assert not IsZero(a);

	// Sanity checks.
	assert IsPrime(pR);

	// Coerce the specified element in the order.
	ok, a := IsCoercible(NumberField(Order(pR)), a);
	assert ok;

	// The ramification index of the prime ideal.
	e := RamificationIndex(pR);

	// The quadratic defect of -a.
	defect := QuadraticDefect_2(-a, pR);

	// The element -a is not a square, and its defect ideal is not the full
	//  local ring.
	if Type(defect) ne Infty and defect ge 0 then
		return true;
	// The element -a is a square, and the quadratic defect of a
	elif Type(defect) eq Infty and QuadraticDefect_2(a, pR) ge -2 * e then
		return true;
	end if;

	return false;
end function;

// This function determines whether a local lattice L at pR has "property A" as
//  defined by Beli, Definition 7, pg. 148.
function HasPropertyA(L, pR)
	// Get the Jordan decomposition of L at pR.
	cons, ords := JordanDecomp(L, pR);

	// The lattice has "property A" if and only if all of the Jordan
	//  constituents are unary or binary lattices.
	return &and[ #con le 2 : con in cons ];
end function;

// Determines the elements x of the underlying number field for which (a,x)_pR,
//  the Hilbert symbol at pR, is equal to one, i.e. we are computing the kernel
//  of the Hilbert symbol (a,.)_pR.
function N_function(a, pR, V, g)
	// If the element a is a square, then we return the entire space.
	if Type(QuadraticDefect_2(a, pR)) eq Infty then return V; end if;

	// The dimension of V.
	dim := Dimension(V);

	// Compute the Hilbert symbols for each local square class.
	hilbert := [ HilbertSymbol(a, V.i @ g, pR) : i in [1..dim] ];

	// The basis elements in V corresponding to the local square class
	//  with Hilbert symbol equal to one.
	gens := { V.i : i in [1..dim] | hilbert[i] eq 1 };

	// Retrieve the first basis vector for which the Hilbert symbol is
	//  equal to -1. Note that we are guaranteed that this basis vector
	//  exists since we know that a is a non-square by the first line of
	//  this function.
	j := Min([ i : i in [1..dim] | hilbert[i] eq -1 ]);

	// We must also consider the product (hence addition in V) of those
	//  pairwise distinct elements which have Hilbert symbols equal to -1.
	gens join:= { V.i + V.j : i in [1..dim] | hilbert[i] eq -1 and i ne j };

	// Build and return the subspace generated by the elements we found.
	return sub< V | gens >;
end function;

// Determines the image of G as a subspace of the local square group. The
//  function G is defined in Beli, Definition 4, pg. 136.
function G_function(a, pR, V, g)
	// The dimension of V.
	dim := Dimension(V);

	// The local square classes with zero pR-adic order.
	units := sub< V | [ V.i : i in [1..dim-1] ] >;

	// The square class representatives with zero pR-adic order.
	U := [ g(v) : v in units ];

	// If the element a is not in the set A, return N(-a) according to Beli.
	if not IsInA(a, pR) then return N_function(-a, pR, V, g); end if;

	// If the element belongs to the same square class as -1/4, then G(a)
	//  is precisely the pR-adic units.
	if (-1/4) @@ g eq a @@ g then return units; end if;

	// The pR-adic order of a, here we're using notation from Beli.
	R := Valuation(a, pR);

	// The ramification degree of the specified prime ideal.
	e := RamificationDegree(pR);

	// Case (i) from Beli.
	if R gt 4 * e then return sub< V | a @@ g >; end if;

	// The quadratic defect of -a.
	d := RelativeQuadraticDefect_2(-a, pR);
	d;

	// A primitive element of the prime ideal.
	pi := PrimitiveElement(pR);

	// This is part II from Beli.
	if 2 * e lt R and R le 4 * e then
		// The span of the preimage of a in V.
		spanA := sub< V | a @@ g >;

		if d le 2 * e - R / 2 then // This is case (ii) from Beli.
			// Another span we must consider based upon case (ii).
			spanB := sub< V | (1 + pi^(R + d - 2 * e)) @@ g >;

			// Return the appropriate space for case (ii).
			return (spanA + spanB) meet N_function(-a, pR, V, g);
		end if;

		// We are now in case (iii) from Beli.

		// Note that R must now be even, since if it were odd, then d
		//  would be zero, hence the if-statement would have been
		//  executed.

		// Another span we must consider based upon case (iii).
		spanB := sub< V | (1 + pi^(R div 2)) @@ g >;

		// Return the appropriate space for case (iii).
		return spanA + spanB;
	end if;

	// This is part III from Beli.
	if R le 2 * e then
		// This is case (iv) from Beli.
		if d le e - R / 2 then return N_function(-a, pR, V, g); end if;

		// This is case (v) from Beli.
		if e - R / 2 lt d and d le 3 * e / 2 - R / 4 then
			// The span of the appropriate space for this case.
			span := sub< V | (1 + pi^((R div 2) + d - e)) @@ g >;

			// Return the appropriate space for case (v).
			return span meet N_function(-a, pR, V, g);
		end if;

		// We are now in case (vi) from Beli.

		// Verify that the defect we computed satisfies the appropriate
		//  condition.
		assert d gt 3 * e / 2 - R / 4;

		// Return the appropriate space for case (vi).
		return sub< V | (1 + pi^(e - Floor(e / 2 - R / 4))) @@ g >;
	end if;

	// This never happens.
	assert false;

	// Gotta keep Magma happy!
	return V;
end function;


// Implementation of lattice routines.

intrinsic Print(lat::ModDedLat) {}
	Module(lat);
end intrinsic;

intrinsic 'eq'(lat1::ModDedLat, lat2::ModDedLat) -> BoolElt
{ Determine whether two lattices are equal. }
	return QuadraticSpace(lat1) eq QuadraticSpace(lat2) and
		Module(lat1) eq Module(lat2);
end intrinsic;

intrinsic QuadraticSpace(L::ModDedLat) -> QuadSpace
{ Returns the quadratic space of the lattice. }
	return L`quadSpace;
end intrinsic;

intrinsic Module(L::ModDedLat) -> ModDed
{ Returns the underlying module associated to this structure. }
	return L`Module;
end intrinsic;

intrinsic PseudoBasis(L::ModDedLat) -> SeqEnum
{ Returns the pseudobasis for the underlying module structure. }
	return L`psBasis;
end intrinsic;

intrinsic BaseRing(L::ModDedLat) -> RngOrd
{ Returns the base ring of the lattice. }
	return L`R;
end intrinsic;

intrinsic StandardLattice(quadSpace::QuadSpace) -> ModDedLat
{ Builds the standard lattice for the given quadratic space. }
	// Return the standard lattice for this space if it has already been
	//  computed.
	if assigned quadSpace`stdLat then return quadSpace`stdLat; end if;

	// The standard basis.
	basis := Id(MatrixRing(BaseRing(quadSpace), Dimension(quadSpace)));

	// Build the standard lattice.
	L := LatticeWithBasis(quadSpace, basis);

	// Assign the ZLattice.
	L`ZLattice := ZLattice(L : Standard := true);

	return L;
end intrinsic;

intrinsic LatticeWithBasis(quadSpace::QuadSpace, basis::AlgMatElt) -> ModDedLat
{ Construct the lattice with the specified basis given by the rows of the
matrix provided. }
	// Make sure that the base ring of the quadratic space and the base
	//  ring of the supplied basis agree.
	require quadSpace`F eq BaseRing(basis): "The base rings do not match.";

	// Initialize the internal lattice structure.
	lat := New(ModDedLat);

	// Assign the specified lattice.
	lat`Module := Module(Rows(basis));

	// Assign the base field.
	lat`F := BaseRing(quadSpace);

	// Assign the base ring.
	lat`R := Integers(lat`F);

	// Assign the pseudobasis if we're over a number field.
	lat`psBasis := PseudoBasis(Module(lat));

	// Assign the ambient quadrstice space.
	lat`quadSpace := quadSpace;

	// Assign an empty associative array.
	lat`Vpp := AssociativeArray();

	// Assign an empty associative array.
	lat`Jordan := AssociativeArray();

	return lat;
end intrinsic;

intrinsic LatticeFromLat(L::Lat) -> ModDedLat
{ Builds a ModDedLat structure from a native Lat structure. }
	// The inner form.
	innerForm := InnerProductMatrix(L);

	// The ambient quadratic space.
	Q := AmbientQuadraticSpace(innerForm);

	// The basis for the lattice.
	basis := ChangeRing(Matrix(Basis(L)), BaseRing(Q));

	// Build the lattice and return it.
	return LatticeWithBasis(Q, basis);
end intrinsic;

intrinsic Dimension(L::ModDedLat) -> RngIntElt
{ The dimension of the lattice. }
	return Dimension(QuadraticSpace(L));
end intrinsic;

intrinsic LatticeWithBasis(
	quadSpace::QuadSpace, basis::AlgMatElt[FldOrd], idls::SeqEnum)
		-> ModDedLat
{ Builds a lattice in an ambient quadratic space with the specified basis and
coefficient ideals. }
	// The dimension.
	dim := Dimension(quadSpace);

	// Initialize the lattice data.
	lat := New(ModDedLat);

	// Assign the basic properties.
	lat`quadSpace := quadSpace;
	lat`F := BaseRing(quadSpace);
	lat`R := Integers(lat`F);

	// Build the lattice.
	lat`Module := Module(PseudoMatrix(idls, basis));

	// The pseudobasis.
	lat`psBasis := PseudoBasis(lat`Module);

	// The associative array of affine quadratic spaces.
	lat`Vpp := AssociativeArray();

	// The associative array of Jordan decompositions.
	lat`Jordan := AssociativeArray();

	return lat;
end intrinsic;

intrinsic LatticeWithPseudobasis(quadSpace::QuadSpace, pmat::PMat) -> ModDedLat
{ Construct the lattice given a pseudomatrix. }
	// Build the module.
	module := Module(pmat);

	// Extract the basis.
	basis := Matrix(Basis(module));

	// Extract the coefficient ideals.
	idls := [ pb[1] : pb in PseudoBasis(module) ];

	return LatticeWithBasis(quadSpace, basis, idls);
end intrinsic;

intrinsic ZLattice(lat::ModDedLat : Standard := false) -> Lat
{ Push the lattice down to the integers. }
	// If we've already computed the ZLattice, return it.
	if assigned lat`ZLattice then return lat`ZLattice; end if;

	// Construct an R-basis for the lattice as a Z-module.
	basisR := &cat[ [ x*pb[2] : x in Basis(pb[1]) ]
		: pb in PseudoBasis(Module(lat)) ];

	// Construct a Z-basis for the lattice as a Z-module.
	basisZ := Matrix([ &cat[ Eltseq(e) : e in Eltseq(b) ] : b in basisR ]);

	if Standard then
		// Build lattice as a Z-module in a rational quadratic space.
		lat`ZLattice := LatticeWithBasis(basisZ);

		// Assign the bases for this lattice.
		lat`ZLattice`basisR := basisR;
		lat`ZLattice`basisZ := basisZ;

		// Compute the auxiliary forms.
		auxForms := AuxForms(lat : Standard := Standard);

		// Assign the ambient inner form associated to this lattice.
		gram := auxForms[1];
	else
		// Assign the ambient inner form associated to this lattice.
		gram := lat`quadSpace`stdLat`ZLattice`auxForms[1];
	end if;

	// Construct the ZLattice with basis in the correct quadratic space.
	lat`ZLattice := LatticeWithBasis(basisZ, ChangeRing(gram, Rationals()));

	// Assign the bases for the ZLattice.
	lat`ZLattice`basisR := basisR;
	lat`ZLattice`basisZ := basisZ;

	if Standard then
		lat`ZLattice`auxForms := AuxForms(lat : Standard := Standard);
	end if;

	return lat`ZLattice;
end intrinsic;

intrinsic AuxForms(lat::ModDedLat : Standard := false) -> SeqEnum
{ Compute the auxiliary forms associated to this lattice. }
	// Assign the ZLattice attribute if not yet assigned.
	if not assigned lat`ZLattice then
		lat`ZLattice := ZLattice(lat : Standard := Standard);
	end if;

	// As long as this isn't intended to become a standard lattice, return
	//  the auxiliary forms if they've already been computed.
	if not Standard and assigned lat`ZLattice`auxForms then
		return lat`ZLattice`auxForms;
	end if;

	// The base ring.
	R := BaseRing(lat);

	// The quadratic space associated to this lattice.
	Q := QuadraticSpace(lat);

	// The dimension.
	dim := Dimension(QuadraticSpace(lat));

	// The degree of the field extension.
	deg := Degree(BaseRing(Q));

	// The inner form of the ambient quadratic space.
	M := InnerForm(Q);

	// The basis for the lattice over the rationals.
	basis := ZLattice(lat)`basisR;

	// Compute a sequence of auxiliary pairings used to compute isometry
	//  of lattices over number field.
	phis := [ Matrix(deg*dim, deg*dim,
		[ Trace((Matrix(z*x) * M * Transpose(Matrix(y)))[1,1])
			: x,y in basis ]) : z in Basis(R) ];

	// Make sure that the lattice was pushed down to an integral one, and
	//  that the first bilinear pairing is symmetric and positive definite.
	try
		phis := [ ChangeRing(phi, Integers()) : phi in phis ];
		assert IsSymmetric(phis[1]);
		assert IsPositiveDefinite(phis[1]);
	catch e
		require false: "Auxiliary forms are not of the correct form!";
	end try;

	return phis;
end intrinsic;

intrinsic Discriminant(lat::Lat) -> RngInt
{ Compute the discriminant ideal of the lattice. }
	// The dimension.
	dim := Dimension(lat);

	// Correction factor.
	factor := dim mod 2 eq 1 select 2 else 1;

	// The determinant of the lattice.
	det := Determinant(lat);

	return ideal< Integers() | det / factor >;
end intrinsic;

function pMaximalGram(L, pR : BeCareful := true)
	if assigned L`pMaximal then
		// If the p-maximal data has been assigned, return it.
		if IsDefined(L`pMaximal, pR) then
			return L`pMaximal[pR][1], L`pMaximal[pR][2];
		end if;
	else
		// If it consists of an empty array, create it.
		L`pMaximal := AssociativeArray();
	end if;

	// The coefficient ideals for this lattice.
	idls := [ pb[1] : pb in PseudoBasis(Module(L)) ];

	// The pseudobasis vectors.
	basis := Basis(Module(L));

	// Find a p-maximal basis.
	vecs := [];
	for i in [1..#idls] do
		// The generators of the coefficient ideal.
		gens := Generators(idls[i]);

		// Randomly choose a p-maximal vector.
		repeat
			vec := &+[ g * (Random(11) - 5)
				: g in gens ] * basis[i];
		until not vec in pR * Module(L);

		// Verify that the vectors were chosen properly.
		if BeCareful then
			assert vec in Module(L) and not vec in pR * Module(L);
		end if;

		// Add this vector to the list.
		Append(~vecs, vec);
	end for;

	// The matrix of basis vectors.
	basis := Matrix(vecs);

	// The Gram matrix for the ambient quadratic space.
	gram := basis * InnerForm(QuadraticSpace(L)) * Transpose(basis);

	// Store the p-maximal basis for future use.
	L`pMaximal[pR] := < ChangeRing(gram, BaseRing(L)), Matrix(vecs) >;

	// Return the Gram matrix and the basis.
	return L`pMaximal[pR][1], L`pMaximal[pR][2];
end function;

intrinsic Level(lat::ModDedLat) -> RngOrdFracIdl
{ Compute the level of the lattice. }
	// If the level has been computed, return it.
	if assigned lat`Level then return lat`Level; end if;

	// The coefficient ideals of the dual.
	idls := [ pb[1]^-1 : pb in PseudoBasis(Module(lat)) ];

	// The basis of the current lattice.
	basis := Matrix(Basis(Module(lat)));

	// The Gram matrix of the dual lattice.
	gram := (basis * InnerForm(QuadraticSpace(lat)) * Transpose(basis))^-1;

	// The dimension.
	dim := Nrows(gram);

	// Compute the level of the lattice.
	lat`Level := (&+[ idls[i]^2 * gram[i,i] / 2 : i in [1..dim ] ] +
		&+[ idls[i] * idls[j] * gram[i,j]
			: i,j in [1..dim] | i lt j ])^-1;

	// Return it.
	return lat`Level;
end intrinsic;

intrinsic Divisor(lat::ModDedLat) -> RngOrdFracIdl
{ Compute the divisor ideal of the lattice. }
	// The coefficient ideals.
	idls := [ pb[1] : pb in PseudoBasis(Module(lat)) ];

	// The rank of the lattice.
	dim := #idls;

	// This is only implemented for ternary lattices.
	require dim eq 3: "Only implemented for ternary lattices.";

	// The underlying basis for the vector space.
	basis := Matrix(Basis(Module(lat)));

	// The Gram matrix of the underlying basis.
	gram := basis * InnerForm(QuadraticSpace(lat)) * Transpose(basis);

	// Values of the Gram matrix for easy reference.
	a := gram[1,1] / 2; b := gram[2,2] / 2; c := gram[3,3] / 2;
	r := gram[2,3]; s := gram[1,3]; t := gram[1,2];

	// The (i,j)-cofactor ideals.
	A11 := (idls[2] * idls[3])^2 * (4*b*c - r^2);
	A12 := idls[1] * idls[2] * idls[3]^2 * (2*c*t - r*s);
	A13 := idls[1] * idls[2]^2 * idls[3] * (r*t - 2*b*s);
	A22 := (idls[1] * idls[3])^2 * (4*a*c - s^2);
	A23 := idls[1]^2 * idls[2] * idls[3] * (2*a*r - s*t);
	A33 := (idls[1] * idls[2])^2 * (4*a*b - t^2);

	// Return the divisor ideal.
	return A11 + A22 + A33 + 2*A12 + 2*A13 + 2*A23;
end intrinsic;

intrinsic Norm(lat::ModDedLat) -> RngOrdFracIdl
{ Compute the norm of the lattice. }
	// If the norm has already been computed, return it.
	if assigned lat`Norm then return lat`Norm; end if;

	// The coefficient ideals.
	idls := [ pb[1] : pb in PseudoBasis(Module(lat)) ];

	// The underlying basis for the vector space.
	basis := Matrix(Basis(Module(lat)));

	// The Gram matrix for this basis.
	gram := basis * InnerForm(QuadraticSpace(lat)) * Transpose(basis);

	// The dimension.
	dim := Nrows(gram);

	// Compute the norm ideal for the lattice.
	lat`Norm := &+[ idls[i]^2 * gram[i,i] / 2 : i in [1..dim] ] +
		&+[ idls[i] * idls[j] * gram[i,j] : i,j in [1..dim] | i lt j ];

	// Return the norm.
	return lat`Norm;
end intrinsic;

intrinsic Scale(lat::ModDedLat) -> RngOrdFracIdl
{ Compute the scale of the lattice. }
	// Return the scale if it has already been computed.
	if assigned lat`Scale then return lat`Scale; end if;

	// Extract the coefficient ideals.
	idls := [ pb[1] : pb in PseudoBasis(Module(lat)) ];

	// The underlying basis for lattice.
	basis := Matrix(Basis(Module(lat)));

	// The Gram matrix for the underlying basis.
	gram := basis * InnerForm(QuadraticSpace(lat)) * Transpose(basis);

	// The dimension of the vector space.
	dim := Nrows(basis);

	// Compute the scale of the lattice.
	lat`Scale := &+[
		gram[i,j] * idls[i] * idls[j] : i,j in [1..dim] | i le j];

	// Return the scale.
	return lat`Scale;
end intrinsic;

intrinsic Discriminant(lat::ModDedLat) -> RngOrdFracIdl
{ Compute the discriminant of the lattice. }
	// Return the discriminant if it's already been computed.
	if assigned lat`Discriminant then return lat`Discriminant; end if;

	// The inner form of the ambient quadratic space.
	M := InnerForm(QuadraticSpace(lat));

	// Retrieve the basis matrix for this lattice.
	B := ChangeRing(Matrix(Basis(Module(lat))), BaseRing(M));

	// The determinant of the inner form of this lattice.
	det := Determinant(M) * Determinant(B)^2;

	// Return the discriminant depending on the parity of the dimension.
	if Dimension(QuadraticSpace(lat)) mod 2 eq 1 then
		det /:= 2;
	end if;

	// Assign the discriminant.
	lat`Discriminant := det * SteinitzClass(Module(lat))^2;

	return lat`Discriminant;
end intrinsic;

intrinsic IntersectionLattice(lat1::ModDedLat, lat2::ModDedLat) -> ModDedLat
{ Computes the intersection lattice of the two specified lattices. }
	// Make sure both lattices belong to the same ambient quadratic space.
	require QuadraticSpace(lat1) eq QuadraticSpace(lat2):
		"Both lattices must belong to the same quadratic space.";

	return LatticeWithPseudobasis(
		QuadraticSpace(lat1),
		PseudoMatrix(Module(lat1) meet Module(lat2)));
end intrinsic;

intrinsic Index(lat1::ModDedLat, lat2::ModDedLat) -> RngOrdFracIdl
{ Compute the index of Pi in Lambda. }
	// Ensure both lattices reside in the same ambient quadratic space.
	require QuadraticSpace(lat1) eq QuadraticSpace(lat2):
		"Both lattices must belong to the same quadratic space.";

	// Compute discriminants.
	disc1 := Discriminant(lat1);
	disc2 := Discriminant(lat2);

	// The quotient of the two discriminants.
	quo := disc2 / disc1;

	// Make sure this is an integral ideal.
	assert Denominator(quo) eq 1;

	// Compute the square root.
	sq, root := IsSquare(quo);

	// Make sure the square root is valid.
	assert sq;

	return root;
end intrinsic;

intrinsic IsIsometric(M::ModFrmAlg, lat1::Lat, lat2::Lat) -> BoolElt
{ Determines whether the two specified lattices are isometric. }
	// Check for isometry.
	iso, f := IsIsometric(lat1, lat2);

	// If not isometric, immediately return.
	if not iso then return false; end if;

	// If isogeny type is SO, then we require proper isometry.
	if IsSpecialOrthogonal(M) and Determinant(f) eq -1 then
		// Look at the generators of the automorphism group of the
		//  first lattice.
		gens := Generators(AutomorphismGroup(lat1));

		// If any of the generators have determinant -1, then we can
		//  compose f and g in such a way to produce a proper isometry.
		for g in gens do
			if Determinant(g) eq -1 then
				return true;
			end if;
		end for;

		// Same as above.
		gens := Generators(AutomorphismGroup(lat2));
		for g in gens do
			if Determinant(g) eq -1 then
				return true;
			end if;
		end for;

		// No generators of determinant -1 found, therefore these two
		//  lattices are not properly isometric.
		return false;
	end if;

	return iso;
end intrinsic;

intrinsic IsIsometric(lat1::ModDedLat, lat2::ModDedLat) -> BoolElt
{ Determines whether the two specified lattices are isometric. }
	// Verify that both lattices reside in the same quadratic space.
	require QuadraticSpace(lat1) eq QuadraticSpace(lat2):
		"Both lattices must belong to the same quadratic space.";

	// Retrive the ZLattices for each lattice.
	L1 := ZLattice(lat1);
	L2 := ZLattice(lat2);

	// Check for isometry.
	iso, f := IsIsometric(L1, AuxForms(lat1), L2, AuxForms(lat2));

	return iso;
end intrinsic;

intrinsic AutomorphismGroup(lat::ModDedLat) -> SeqEnum
{ Computes the automorphism group of the specified lattice. }
	// Return the automorphism group if it has already been computed.
	if assigned lat`AutomorphismGroup then
		return lat`AutomorphismGroup;
	end if;

	// Compute the automorphism group of this lattice.
	aut := AutomorphismGroup(ZLattice(lat), AuxForms(lat));

	// Save it for further use.
	lat`AutomorphismGroup := aut;

	return lat`AutomorphismGroup;
end intrinsic;

intrinsic IsFree(L::ModDedLat) -> BoolElt
{ Determines whether the lattice is a free lattice or not. }
	// The pseudobasis for the lattice.
	psBasis := PseudoBasis(L);

	// The lattice is free if and only if the product of its coefficient
	//  ideals is principal.
	value := IsPrincipal(&*[ pb[1] : pb in psBasis ]);

	// Return value.
	return value;
end intrinsic;

intrinsic FreeBasis(L::ModDedLat) -> SeqEnum
{ Computes and returns a basis for a free lattice. }
	// Require the lattice to be free.
	require IsFree(L): "Lattice must be free.";

	// The quadratic space.
	Q := QuadraticSpace(L);

	// The pseudobasis for the lattice.
	psBasis := PseudoBasis(L);

	// Extract the bases and coefficient ideals.
	idls := [ pb[1] : pb in psBasis ];
	basis := [ pb[2] : pb in psBasis ];

	// Dimension of the lattice.
	dim := Dimension(L);

	for i in [1..dim-1] do
		// Determine whether the current coefficient ideal is principal.
		check, elt := IsPrincipal(idls[i]);	

		// If principal, then scale the basis with the generator.
		if check then
			idls[i] /:= idls[i];
			basis[i] *:= elt;
			continue;
		end if;

		// Convert the coefficient ideals into integral ideals.
		aa := Denominator(idls[i]); A := aa * idls[i];
		bb := Denominator(idls[i+1]); B := bb * idls[i+1];
		assert IsIntegral(A) and IsIntegral(B);

		// Generators of idls[i].
		gs := Generators(A);

		// Find elements according to Cohen's Proposition 1.3.12.
		repeat
			repeat x := Random(5); y := Random(5);
			until x ne 0 and y ne 0;
			a := x * gs[1] + y * gs[2];
		until IsIntegral(a * idls[i]^-1) and
			Factorization(a*A^-1 + B) eq [];

		// Construct a matrix so that we can apply HNF.
		C := Matrix([ Eltseq(x) : x in Basis(a*A^-1) cat Basis(B) ]);
		C := ChangeRing(C, Integers());

		// Perform an HNF.
		H, U := HermiteForm(C);

		// Verify that the top half of H is the identity matrix.
		assert Submatrix(H,[1..#gs],[1..#gs]) eq 1;

		// Find elements e and f following Cohen Algorithm 1.3.2.
		X := Submatrix(U, [1..1], [1..#gs]);
		AA := Matrix([ Eltseq(x) : x in Basis(a*A^-1) ]);
		AA := ChangeRing(AA, Integers());
		e := Order(A) ! Eltseq(X * AA);
		f := 1 - e;

		// Verify that the elements we chose are in the correct ideals.
		assert e in a * A^-1 and f in B;

		// Coefficients according to Cohen's Proposition 1.3.12.
		b := f / bb;
		c := (Order(B)!(-1)) * bb;
		d := e / a;

		// Verify that these elements belong the correct ideals.
		assert a*d - b*c eq 1;
		assert a in idls[i];
		assert b in idls[i+1];
		assert c in idls[i+1]^-1;
		assert d in idls[i]^-1;

		// The new bases and coefficient ideals.
		vec1 := a * basis[i] + b * basis[i+1];
		vec2 := c * basis[i] + d * basis[i+1];
		basis[i] := vec1;
		basis[i+1] := vec2;
		idls[i+1] *:= idls[i];
		idls[i] /:= idls[i];
	end for;

	// Confirm that the last ideal is principal.
	check, elt := IsPrincipal(idls[#idls]);
	assert check;

	// Update the last basis element.
	basis[#idls] *:= elt;

	assert LatticeWithBasis(Q, Matrix(basis)) eq L;

	return basis;
end intrinsic;

/* Experimental. Deprecated */
intrinsic ChangeLocallyAt(L::Lat, M::Lat, p::RngIntElt) -> Lat
{ Change the lattice L locally at p with respect to the lattice M. }
	// Make sure both lattices are the same dimension.
	require Dimension(L) eq Dimension(M):
		"The dimensions of the lattices must agree.";

	require InnerProductMatrix(L) eq InnerProductMatrix(M):
		"Lattices must come from the same quadratic space.";

	// The dimension.
	dim := Dimension(L);

	// Compute the intersection lattice.
	intLat := L meet M;

	// Determine the quotient group (a finite abelian group).
	tempG, tempMap := quo< L | intLat >;

	// Compute the exponent of the quotient group.
	e := Exponent(tempG);

	// Compute the scaled lattice that we will work with.
	scaledLat := e * M;

	// Verify that scaling M by the exponent lands in L.
	assert scaledLat subset L;

	// Determine the quotient group.
	G, map := quo< L | scaledLat >;

	// Compute the complement to the p-primary component of G.
	H := Complement(G, pPrimaryComponent(G, p));

	// We will construct a lattice from the span of these vectors.
	vecs := [ x @@ map : x in Generators(H) ] cat Basis(scaledLat);

	// Make sure all vectors belong to L.
	assert &and[ vec in L : vec in vecs ];

	// We're going to need to scale the vectors so we can apply HNF.
	denom1 := BasisDenominator(scaledLat);
	denom2 := BasisDenominator(L);

	// Scale vectors.
	vecs := [ ChangeRing(denom1 * denom2 * x, Integers()) : x in vecs ];

	// Compute the Hermite Normal form of these vectors.
	H, U := HermiteForm(Matrix(vecs));

	// The basis of the target lattice spanned by vecs.
	basis := Matrix(
		[ ChangeRing(H[i], Rationals()) / e / denom1 : i in [1..dim] ]);

	// Build the specified lattice we're looking for.
	return LatticeWithBasis(basis,
		ChangeRing(InnerProductMatrix(L), Rationals()));
end intrinsic;


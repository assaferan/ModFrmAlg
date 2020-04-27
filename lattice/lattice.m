freeze;
/****-*-magma-******a********************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                             Eran Assaf                                 
                                                                            
   FILE: lattice.m

   Implementation file for lattice routines

   04/27/2020 : Modified AutomorphismGroup to work also for SO 
   	      	(parameter special)
                Fixed bug in IsIsometric when special = true.
                Removed restriction of positive-definite, as now we also use
                this module for construction of indefinite groups.

   04/24/2020 : Modified default values of BeCareful to be false.
                Modified IsIsometric to have a parameter, indicating a special 
		isometry.
 
   04/20/2020 : Modified LatticeWithBasis to handle bases given as a nonsquare 
                matrix, and fixed a bug in PullUp.

   03/05/2020 : Created this file as a copy of the one from othogonal package.
                Replaced quadratic spaces by reflexive spaces.
                Added a GramMatrix intrinsic, as it repeats in many places.
                Made appropriate adjustments to discriminant, auxiliary forms, 
                and Gram matrix for the unitary case.
 
 ***************************************************************************/

///////////////////////////////////////////////////////////////////
//                                                               //
//    ModDedLat: The lattice in a Dedekind module object.        //
//                                                               //
///////////////////////////////////////////////////////////////////

declare type ModDedLat;
declare attributes ModDedLat:
	// The lattice.
	Module,

	// The base ring.
	R,

	// The base field.
	F,

	// The pseudobasis (only used when not over the rationals).
	psBasis,

        // The ambient reflexive space
        rfxSpace,
  
	// The discriminant ideal.
	Discriminant,

	// The p-maximal basis is not strictly-speaking a basis for the lattice,
	//  but instead a basis for the completed lattice at p. This is used to
	//  compute the affine reflexive space and thereby compute isotropic
	//  lines, etc.
	pMaximal,

	// The lattice pushed down to the integers. This is the same as L if
	//  and only if the base field is the rationals.
	ZLattice,

	// The automorphism group as a lattice over Z.
	AutomorphismGroup,

	// The scale of the lattice.
	Scale,

	// The norm of the lattice.
	Norm,

	// The level of the lattice.
	Level,

	// An associative array storing reflexive spaces modulo primes.
	Vpp,

	// Jordan decomposition of the lattice at a prime.
	Jordan,

	// The spinor norms as specified prime ideals.
	SpinorNorm;

// adding some attributes to the existing lattice type Lat.

declare attributes Lat:
	// The auxiliary forms associated to this lattice.
	auxForms,

	// The basis of the lattice with coefficients in R.
	basisR,

	// The basis of the lattice with coefficients in Z.
	basisZ,

	// An associative array storing quadratic spaces modulo primes
	Vpp;

// Implementation of lattice routines.

intrinsic Parent(lat::ModDedLat) {}
  PowerStructure(ModDedLat);
end intrinsic;

// print

intrinsic Print(lat::ModDedLat) {}
	Module(lat);
end intrinsic;

// boolean operators

intrinsic 'eq'(lat1::ModDedLat, lat2::ModDedLat) -> BoolElt
{ Determine whether two lattices are equal. }
	return ReflexiveSpace(lat1) eq ReflexiveSpace(lat2) and
		Module(lat1) eq Module(lat2);
end intrinsic;

// access

intrinsic ReflexiveSpace(L::ModDedLat) -> RfxSpace
{ Returns the reflexive space of the lattice. }
	return L`rfxSpace;
end intrinsic;

intrinsic AmbientSpace(L::ModDedLat) -> RfxSpace
{ Returns the ambient reflexive space of the lattice. }
        return L`rfxSpace;
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

intrinsic StandardLattice(rfxSpace::RfxSpace) -> ModDedLat
{ Builds the standard lattice for the given reflexive space. }
	// Return the standard lattice for this space if it has already been
	//  computed.
	if assigned rfxSpace`stdLat then return rfxSpace`stdLat; end if;

	// The standard basis.
	basis := Id(MatrixRing(BaseRing(rfxSpace), Dimension(rfxSpace)));
	
	// Build the standard lattice.
	L := LatticeWithBasis(rfxSpace, basis);
	
	require IsIntegral(Discriminant(L)) :
		"Standard Lattice is not integral for reflexive space!" ; 

	// Assign the ZLattice.
	L`ZLattice := ZLattice(L : Standard := true);

	return L;
end intrinsic;

intrinsic LatticeWithBasis(rfxSpace::RfxSpace, basis::Mtrx) -> ModDedLat
{ Construct the lattice with the specified basis given by the rows of the
matrix provided. }
	// Make sure that the base ring of the reflexive space and the base
	//  ring of the supplied basis agree.
	require rfxSpace`F eq BaseRing(basis): "The base rings do not match.";

	// Initialize the internal lattice structure.
	lat := New(ModDedLat);

	// Assign the specified lattice.
	lat`Module := Module(Rows(basis));

	// Assign the base field.
	lat`F := BaseRing(rfxSpace);

	// Assign the base ring.
	lat`R := Integers(lat`F);

	// Assign the pseudobasis if we're over a number field.
	lat`psBasis := PseudoBasis(Module(lat));

	// Assign the ambient reflexive space.
	lat`rfxSpace := rfxSpace;

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

	// The ambient reflexive space.
	Q := AmbientReflexiveSpace(innerForm);

	// The basis for the lattice.
	basis := ChangeRing(Matrix(Basis(L)), BaseRing(Q));

	// Build the lattice and return it.
	return LatticeWithBasis(Q, basis);
end intrinsic;

intrinsic Dimension(L::ModDedLat) -> RngIntElt
{ The dimension of the lattice. }
	return Dimension(ReflexiveSpace(L));
end intrinsic;

intrinsic LatticeWithBasis(
	rfxSpace::RfxSpace, basis::AlgMatElt[Fld], idls::SeqEnum)
		-> ModDedLat
{ Builds a lattice in an ambient reflexive space with the specified basis and
coefficient ideals. }
	// The dimension.
	dim := Dimension(rfxSpace);

	// Initialize the lattice data.
	lat := New(ModDedLat);

	// Assign the basic properties.
	lat`rfxSpace := rfxSpace;
	lat`F := BaseRing(rfxSpace);
	lat`R := Integers(lat`F);

	// Build the lattice.
	lat`Module := Module(PseudoMatrix(idls, basis));

	// The pseudobasis.
	lat`psBasis := PseudoBasis(lat`Module);

	// The associative array of affine reflexive spaces.
	lat`Vpp := AssociativeArray();

	// The associative array of Jordan decompositions.
	lat`Jordan := AssociativeArray();

	return lat;
end intrinsic;

intrinsic LatticeWithPseudobasis(rfxSpace::RfxSpace, pmat::PMat) -> ModDedLat
{ Construct the lattice given a pseudomatrix. }
	// Build the module.
	module := Module(pmat);

	// Extract the basis.
	basis := Matrix(Basis(module));

	// Extract the coefficient ideals.
	idls := [ pb[1] : pb in PseudoBasis(module) ];

	return LatticeWithBasis(rfxSpace, basis, idls);
end intrinsic;

intrinsic ZLattice(lat::ModDedLat : Standard := false) -> Lat
{ Push the lattice down to the integers. }
	// If we've already computed the ZLattice, return it.
	if assigned lat`ZLattice then return lat`ZLattice; end if;

        V := VectorSpace(ReflexiveSpace(lat));

	// Construct an R-basis for the lattice as a Z-module.
        basisR := &cat[ [ V!(x*pb[2]) : x in Basis(pb[1]) ]
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
		gram := lat`rfxSpace`stdLat`ZLattice`auxForms[1];
	end if;

	// Construct the ZLattice with basis in the correct quadratic space.
	lat`ZLattice := LatticeWithBasis(basisZ, ChangeRing(gram, Rationals())
					: CheckPositive := false);

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

	// The reflexive space associated to this lattice.
	V := ReflexiveSpace(lat);

	// The dimension.
	dim := Dimension(ReflexiveSpace(lat));

	// The degree of the field extension.
	deg := Degree(BaseRing(V));

	// The inner form of the ambient reflexive space.
        M := InnerForm(V);
        alpha := Involution(V);

	// The basis for the lattice over the rationals.
	basis := ZLattice(lat)`basisR;
        conj_basis := [alpha(b) : b in basis];

	// Compute a sequence of auxiliary pairings used to compute isometry
	//  of lattices over number field.
	phis := [ Matrix(deg*dim, deg*dim,
		[ Trace((Matrix(z*x) * M * Transpose(Matrix(y)))[1,1])
		    : x in basis, y in conj_basis ]) : z in Basis(R) ];

	// Make sure that the lattice was pushed down to an integral one, and
	//  that the first bilinear pairing is symmetric and positive definite.
	try
		phis := [ ChangeRing(phi, Integers()) : phi in phis ];
		assert IsSymmetric(phis[1]);
		// We are now using this function also to construct groups
		// corresponding to non-definite forms
		// assert IsPositiveDefinite(phis[1]);
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

function pMaximalGram(L, pR : BeCareful := false, given_coeffs := [])
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
		    if IsEmpty(given_coeffs) then
			coeffs := [Random(11) - 5 : g in gens];
		    else
			coeffs := given_coeffs[i];
		    end if;

                        vec := &+[ gens[j] * coeffs[j] :
					 j in [1..#gens]] * basis[i];
		until not vec in pR * Module(L);
		// for debugging
		if GetVerbose("AlgebraicModularForms") ge 3 then
		    printf "coeffs = %o\n", coeffs;
		end if;
		// Verify that the vectors were chosen properly.
		if BeCareful then
			assert vec in Module(L) and not vec in pR * Module(L);
		end if;

		// Add this vector to the list.
		Append(~vecs, vec);
	end for;

        gram := GramMatrix(L, vecs);

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

        gram := GramMatrix(lat, Basis(Module(lat)))^(-1);

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

        gram := GramMatrix(lat, Basis(Module(lat)));

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

        gram := GramMatrix(lat, Basis(Module(lat)));

	// The dimension.
	dim := Nrows(gram);

	// Compute the norm ideal for the lattice.
	lat`Norm := &+[ idls[i]^2 * gram[i,i] / 2 : i in [1..dim] ] +
		&+[ idls[i] * idls[j] * gram[i,j] : i,j in [1..dim] | i lt j ];

	// Return the norm.
	return lat`Norm;
end intrinsic;

intrinsic GramMatrix(lat::ModDedLat, vecs::SeqEnum[ModTupFldElt]) -> AlgMatElt
{.}
  // The underlying basis for lattice.
  basis := Matrix(vecs);

  // The involution of the reflexive space
  alpha := Involution(ReflexiveSpace(lat));

  F := BaseField(alpha);

  basis := ChangeRing(basis, F);

  // The Gram matrix for the underlying basis.
  gram := basis * InnerForm(ReflexiveSpace(lat)) *
    Transpose(alpha(basis));

  return gram;
end intrinsic;

intrinsic Scale(lat::ModDedLat) -> RngOrdFracIdl
{ Compute the scale of the lattice. }
	// Return the scale if it has already been computed.
	if assigned lat`Scale then return lat`Scale; end if;

	// Extract the coefficient ideals.
	idls := [ pb[1] : pb in PseudoBasis(Module(lat)) ];

        gram := GramMatrix(lat, Basis(Module(lat)));

	// The dimension of the vector space.
	dim := Nrows(gram);

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

	// The inner form of the ambient reflexive space.
	M := InnerForm(ReflexiveSpace(lat));

        // The involution of the ambient reflexive space
        alpha := Involution(ReflexiveSpace(lat));

	// Retrieve the basis matrix for this lattice.
	B := ChangeRing(Matrix(Basis(Module(lat))), BaseRing(M));

	// The determinant of the inner form of this lattice.
        det := Determinant(M) * Determinant(B) * alpha(Determinant(B));

	// Return the discriminant depending on the parity of the dimension.
        if IsIdentity(alpha) and
	   (Dimension(ReflexiveSpace(lat)) mod 2 eq 1) then
		det /:= 2;
	end if;

	// Assign the discriminant.
        steinitz :=  SteinitzClass(Module(lat));
        lat`Discriminant := det * steinitz * alpha(steinitz);

	return lat`Discriminant;
end intrinsic;

intrinsic IntersectionLattice(lat1::ModDedLat, lat2::ModDedLat) -> ModDedLat
{ Computes the intersection lattice of the two specified lattices. }
	// Make sure both lattices belong to the same ambient reflexive space.
	require ReflexiveSpace(lat1) eq ReflexiveSpace(lat2):
		"Both lattices must belong to the same reflexive space.";

	return LatticeWithPseudobasis(
		ReflexiveSpace(lat1),
		PseudoMatrix(Module(lat1) meet Module(lat2)));
end intrinsic;

intrinsic Index(lat1::ModDedLat, lat2::ModDedLat) -> RngOrdFracIdl
{ Compute the index of Pi in Lambda. }
	// Ensure both lattices reside in the same ambient reflexive space.
	require ReflexiveSpace(lat1) eq ReflexiveSpace(lat2):
		"Both lattices must belong to the same reflexive space.";

        index :=  &*ElementaryDivisors(Module(lat1), Module(lat2));

        // Make sure this is an integral ideal
        assert Denominator(index) eq 1;

        return index;

        // old code - good for orthogonal case only

	// Compute discriminants.
	disc1 := Discriminant(lat1);
	disc2 := Discriminant(lat2);

	// The quotient of the two discriminants.
	quo := disc2 / disc1;

	// Make sure this is an integral ideal.
	assert Denominator(quo) eq 1;

        // Problem - quo is a square only in the quadratic case.
        // In the unitary case, it is of the form I * alpha(I)
        // and one cannot use only quo to determine I

	// Compute the square root.
	sq, root := IsSquare(quo);

	// Make sure the square root is valid.
	assert sq;

	return root;
end intrinsic;

intrinsic IsIsometric(lat1::ModDedLat, lat2::ModDedLat :
		      special := false, BeCareful := false) -> BoolElt, Mtrx
{ Determines whether the two specified lattices are isometric. }
	// Verify that both lattices reside in the same reflexive space.
	require ReflexiveSpace(lat1) eq ReflexiveSpace(lat2):
		"Both lattices must belong to the same reflexive space.";

	// Retrieve the ZLattices for each lattice.
	L1 := ZLattice(lat1);
	L2 := ZLattice(lat2);

	// Check for isometry.
	iso, f := IsIsometric(L1, AuxForms(lat1), L2, AuxForms(lat2));

	if not iso then return false, _; end if;
	
	// f := PullUp(Matrix(f), lat1, lat2 : BeCareful := BeCareful);

	// Currently, this only works for SO, where det in -1,1
	if special and Determinant(f) eq -1 then
	    // Look at the generators of the automorphism group of the
	    //  first lattice.
	    gens := Generators(AutomorphismGroup(lat1));

	    // If any of the generators have determinant -1, then we can
	    //  compose f and g in such a way to produce a proper isometry.
	    for g in gens do
		if Determinant(g) eq -1 then
		    return true,
			   PullUp(Matrix(g*f), lat1, lat2 :
				  BeCareful := BeCareful);
		end if;
	    end for;

	    // Same as above.
	    gens := Generators(AutomorphismGroup(lat2));
	    for g in gens do
		if Determinant(g) eq -1 then
		    return true,
			   PullUp(Matrix(f*g), lat1, lat2 :
				  BeCareful := BeCareful);
		end if;
	    end for;

	    // No generators of determinant -1 found, therefore these two
	    //  lattices are not properly isometric.
	    return false, _;
	end if;
	
	return iso, PullUp(Matrix(f), lat1, lat2 : BeCareful := BeCareful);
end intrinsic;

intrinsic AutomorphismGroup(lat::ModDedLat : Special := false) -> SeqEnum
{ Computes the automorphism group of the specified lattice. }
        if Special then
	    aut := AutomorphismGroup(lat);
	    return sub<aut |[x : x in aut | Determinant(x) eq 1]>;
	end if;

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

	// The reflexive space.
	V := ReflexiveSpace(L);

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

	assert LatticeWithBasis(V, Matrix(basis)) eq L;

	return basis;
end intrinsic;

intrinsic PullUp(g::AlgMatElt, Lambda::ModDedLat, Pi::ModDedLat :
		 BeCareful := false) -> AlgMatElt
  {Takes an isometry g : Pi -> Lambda and reexpresses it as an L-linear map gV : V -> V.}

  LambdaZZ := ZLattice(Lambda);
  LambdaZZAuxForms := AuxForms(Lambda);
  PiZZ := ZLattice(Pi);
  PiZZAuxForms := AuxForms(Pi);   
  BL := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Rows(LambdaZZ`basisZ)]);
  BP := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Rows(PiZZ`basisZ)]);
  m := Dimension(Lambda);
  V := VectorSpace(AmbientSpace(Lambda));
  L := BaseField(V);
  d := Degree(L);
  rows := [];
  for i in [1..m] do
    v := Vector(&cat[Eltseq(x) : x in Eltseq(V.i)]);
    rowQ := Eltseq(v*BP^-1*(Parent(BL)!g)*BL);
    rowL := Vector([L!rowQ[j*d+1..(j+1)*d] : j in [0..m-1]]); 
    Append(~rows,rowL);
  end for;
  
  ans := Matrix(rows);
  
  if BeCareful then
    alpha := Involution(ReflexiveSpace(Lambda));
    print "gV maps Pi into Lambda?", &and[ChangeRing(x,L)*ans in Module(Lambda) :
					x in PiZZ`basisR];
    print "gV respects the inner product?", InnerProductMatrix(V) eq ans*InnerProductMatrix(V)*alpha(Transpose(ans));
  end if;
  
  return ans;
end intrinsic;

// functions for p-adic completion and p-adic lattices

declare type RngPadIdl;
declare attributes RngPadIdl :
		   // the ring
		   R,
		   generator;

intrinsic Ideal(R::RngPad, t::.) -> RngPadIdl
{.}
  if Type(t) ne SeqEnum then t := [t]; end if;
  pi := UniformizingElement(R);
  val := Minimum([Valuation(R!x) : x in t]);
  I := New(RngPadIdl);
  I`R := R;
  I`generator := pi^val;
  return I;
end intrinsic;

intrinsic Generators(I::RngPadIdl) -> SeqEnum[RngPadElt]
{.}
  return [I`generator];
end intrinsic;

intrinsic Print(I::RngPadIdl)
{.}
  printf "Ideal of %o generated by %o", I`R, I`generator;
end intrinsic;

intrinsic '#'(I::RngPadIdl) -> RngIntElt
{.}
  k := ResidueClassField(I`R);
  v := Valuation(I`generator);
  return (#(I`R) / (#k)^v);
end intrinsic;

declare type ModPad[ModTupFldElt];
declare attributes ModPad :
		   // the base ring
		   R,
	// the field of fractions
	F,
	// basis
	basis;

intrinsic Module(R::RngPad, n::RngIntElt) -> ModPad
{Create the free module R^n where R is a p-adic ring.}
  M := New(ModPad);
  M`R := R;
  M`F := FieldOfFractions(R);
  M`basis := Rows(IdentityMatrix(M`F, n));
  
  return M;
end intrinsic;

intrinsic pAdicModule(S::SeqEnum[ModTupFldElt]) -> ModPad
{Create a module from the sequence of ModElts with entries in the p-adic ring or its field of fractions. The elements of the resulting module will be the linear combinations of the ModElts.}
  M := New(ModPad);
  M`F := FieldOfFractions(BaseRing(Universe(S)));
  M`R := Integers(M`F);
  M`basis := S;

  return M;
end intrinsic;

intrinsic Print(L::ModPad)
{.}
  printf "Module over %o generated by: ", L`R;
  for b in L`basis do
    printf "\n%o", b;
  end for;
end intrinsic;

intrinsic '.'(L::ModPad, n::RngIntElt) -> ModTupFldElt
{.}	     
  return L`basis[n];
end intrinsic;

intrinsic 'in'(v::ModTupFldElt, L::ModPad) -> BoolElt
{.}
  B := Matrix(L`basis);
  coeffs := v * B^(-1);
  return &and [c in L`R : c in Eltseq(coeffs)];
end intrinsic;

intrinsic ChangeRing(L::ModPad, R::RngPad) -> ModPad
{.}
  F := FieldOfFractions(R);
  return pAdicModule([ChangeRing(b, F) : b in L`basis]);
end intrinsic;

intrinsic DirectSum(Ls::SeqEnum[ModPad]) -> ModPad
{.}
  return pAdicModule(Rows(DirectSum([Matrix(L`basis) : L in Ls])));
end intrinsic;

intrinsic 'subset'(L1::ModPad, L2::ModPad) -> BoolElt
{.}
  return &and [b in L2 : b in L1`basis];
end intrinsic;

intrinsic 'eq'(L1::ModPad, L2::ModPad) -> BoolElt
{.}
  return (L1 subset L2) and (L2 subset L1);
end intrinsic;

intrinsic Complete(L::ModDed, p::RngOrdIdl) -> ModPad
{Compute the completion of the lattice L at the prime p}
//    if Type(L) eq ModDedLat then L := Module(L); end if;
    psb := PseudoBasis(L);
    idls := [x[1] : x in psb];
    basis := [x[2] : x in psb];
    R := FieldOfFractions(BaseRing(L));
    R_p, comp_p := Completion(R,p);
    pi := UniformizingElement(R_p);
    val_idls_p := [ Minimum([Valuation(comp_p(g)) :
			     g in Generators(I)]) : I in idls];
    basis_p := [Vector([comp_p(x) : x in Eltseq(vec)]) :
		vec in basis];
    basis_p := [pi^(val_idls_p[i]) * basis_p[i] :
		i in [1..#basis_p]];
    return pAdicModule(basis_p);
end intrinsic;

intrinsic Complete(L::ModDedLat, p::RngOrdIdl) -> ModPad
{.}
  return Complete(Module(L),p);	  
end intrinsic;

function pAdicLatticeAtSplitPrime(L,p)
    R := Integers(BaseRing(L));
    Ps := [fac[1] : fac in Factorization(ideal<R|p>)];
    L_p := [Complete(L, P) : P in Ps];
    ZZ_p := pAdicRing(p);
    L_p_pAdic := [ChangeRing(Lambda, ZZ_p) : Lambda in L_p];
    return DirectSum(L_p_pAdic);
end function;

function get_hecke_representatives(p)
    reps := [ DiagonalMatrix([p,1,1]) ];
    reps cat:= [ Matrix([[1,r,0],[0,p,0],[0,0,1]]) : r in [0..p-1]];
    reps cat:= [ Matrix([[1,0,r],[0,1,s],[0,0,p]]) : r,s in [0..p-1]];
    // The transposition is to get left cosets: KpK = U p_j K
    ret := [Transpose(r) : r in reps];
    // Checking they are indeed distinct representatives
    QQ := Rationals();
    ZZ := Integers();
    reps := [MatrixAlgebra(QQ,3)!x : x in ret];
    num := &+[r^(-1)*s in MatrixAlgebra(ZZ,3) select 1 else 0 :
	      r,s in reps];
    assert num eq #reps;
    return ret;
end function;

function foo()
    QQ_2 := pAdicField(2);
    K := QuadraticField(-7);
    innerForm := IdentityMatrix(K,3);
    M := UnitaryModularForms(innerForm);
    reps := Representatives(Genus(M));
    // This came from looking at the isotropic subspace,
    // and the elementary divisors in split form - generalize later
    x := Matrix([[1,1,1],[1,1,0],[0,1,1]]);
    // the image of omega in QQ_2 (alpha is the valuation 1 element)
    alpha := (1-SquareRoot(QQ_2!(-7)))/2;
    alphabar := 1-alpha;
    mat := Transpose(x) * DiagonalMatrix([alpha/alphabar,1,1]);
    x_hat := Transpose(mat);
    // verifying that x_hat * (Lambda_0)_2 = Lambda_2
    tt := DirectSum([x_hat, Transpose(x_hat)^(-1)]);
    assert pAdicModule(Rows(tt)) eq pAdicLatticeAtSplitPrime(reps[2],2);
    return x_hat;
end function;
	     

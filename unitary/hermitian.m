// Implementation of ambient quadratic spaces.

intrinsic Print(H::HermSpace) {}
	K := BaseRing(H`V);
	H`V;
end intrinsic;

intrinsic 'eq'(H1::HermSpace, H2::HermSpace) -> BoolElt
{ Determine whether two hermitian spaces are equal. }
	return H1`V cmpeq H2`V and
		InnerProductMatrix(H1`V) eq InnerProductMatrix(H2`V);
end intrinsic;

intrinsic Dimension(hermSpace::HermSpace) -> RngIntElt
{ Returns the dimension of the hermitian space. }
	return hermSpace`dim;
end intrinsic;

intrinsic BaseRing(hermSpace::HermSpace) -> FldOrd
{ Returns the base field of the hermitian space. }
	return hermSpace`F;
end intrinsic;

intrinsic InnerForm(hermSpace::HermSpace) -> AlgMatElt
{ Returns the inner form associated to the hermitian space. }
	return hermSpace`innerForm;
end intrinsic;

intrinsic Diagonal(hermSpace::HermSpace) -> AlgMatElt
{ Returns the coefficients of the diagonalized form. }
	return hermSpace`Diagonal;
end intrinsic;

intrinsic IsDefinite(hermSpace::HermSpace) -> AlgMatElt
{ Returns whether this space is totally positive definite. }
	return hermSpace`Definite;
end intrinsic;

// !!! Stopped here - should change the way we build stuff
// Wants to get L and F directly
// Should be able to get any involution algebra

intrinsic AmbientHermitianSpace(innerForm::AlgMatElt) -> HermSpace
{ Builds the ambient hermitian space data structure. }
	// Initialize a new hermitian space data structre.
	hermSpace := New(HermSpace);

	// The base ring.
	R := BaseRing(innerForm);

	// Determine field of fractions.
	if IsField(R) then
		if R cmpeq Rationals() then
			R := RationalsAsNumberField();
		end if;

		// Make sure we're dealing with a number field.
		require IsNumberField(R):
			"Base ring must be a number field or number ring.";

		// The maximal order of our number field.
		R := Integers(R);
	elif R cmpeq Integers() then
		// Convert to a maximal order format.
		R := Integers(RationalsAsNumberField());
	end if;

	// The field of fractions of the maximal order of our number field.
	L := FieldOfFractions(R);
// At the moment we assume that L was constructed as an extension of F
// If this is not the case, we need some extra data to identify the correct subfield (there might be more than one)
        F := BaseField(L);

	// Coerce the inner form into the appropriate field.
	innerForm := ChangeRing(innerForm, L);

	// Assign base field and base ring.
	hermSpace`F := F;
	hermSpace`R := R;
	quadSpace`deg := Degree(F);
	quadSpace`classNo := ClassNumber(F);

	// Assign the inner form to the quadratic space.
	quadSpace`innerForm := innerForm;

	// Diagonalize the inner form.
	quadSpace`Diagonal, quadSpace`DiagonalBasis :=
		OrthogonalizeGram(innerForm);

	// The diagonal entries.
	quadSpace`Diagonal := Diagonal(quadSpace`Diagonal);

	// Determine whether this space is totally positive definite.
	quadSpace`Definite := IsTotallyReal(F) and
		&and[ IsTotallyPositive(d) : d in quadSpace`Diagonal ];

	// Assign the quadratic space.
	quadSpace`V := QuadraticSpace(innerForm / 2);

	// Assign the quadratic form.
	quadSpace`Q := QuadraticForm(innerForm) / 2;

	// Assign the dimension.
	quadSpace`dim := Nrows(innerForm);

	// Assign the standard lattice for this quadratic space.
	quadSpace`stdLat := StandardLattice(quadSpace);

	return quadSpace;
end intrinsic;


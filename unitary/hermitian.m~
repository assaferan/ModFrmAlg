// Implementation of ambient quadratic spaces.

intrinsic Print(Q::QuadSpace) {}
	K := BaseRing(Q`V);
	Q`V;
end intrinsic;

intrinsic 'eq'(Q1::QuadSpace, Q2::QuadSpace) -> BoolElt
{ Determine whether two quadratic spaces are equal. }
	return Q1`V cmpeq Q2`V and
		InnerProductMatrix(Q1`V) eq InnerProductMatrix(Q2`V);
end intrinsic;

intrinsic Dimension(quadSpace::QuadSpace) -> RngIntElt
{ Returns the dimension of the quadratic space. }
	return quadSpace`dim;
end intrinsic;

intrinsic BaseRing(quadSpace::QuadSpace) -> FldOrd
{ Returns the base field of the quadratic space. }
	return quadSpace`F;
end intrinsic;

intrinsic InnerForm(quadSpace::QuadSpace) -> AlgMatElt
{ Returns the inner form associated to the quadratic space. }
	return quadSpace`innerForm;
end intrinsic;

intrinsic Diagonal(quadSpace::QuadSpace) -> AlgMatElt
{ Returns the coefficients of the diagonalized form. }
	return quadSpace`Diagonal;
end intrinsic;

intrinsic IsDefinite(quadSpace::QuadSpace) -> AlgMatElt
{ Returns whether this space is totally positive definite. }
	return quadSpace`Definite;
end intrinsic;

intrinsic AmbientQuadraticSpace(innerForm::AlgMatElt) -> QuadSpace
{ Builds the ambient quadratic space data structure. }
	// Initialize a new quadratic space data structre.
	quadSpace := New(QuadSpace);

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
		// Covnert to a maximal order format.
		R := Integers(RationalsAsNumberField());
	end if;

	// The field of fractions of the maximal order of our number field.
	F := FieldOfFractions(R);

	// Coerce the inner form into the appropriate field.
	innerForm := ChangeRing(innerForm, F);

	// Assign base field and base ring.
	quadSpace`F := F;
	quadSpace`R := R;
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


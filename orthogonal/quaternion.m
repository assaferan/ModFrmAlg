// Quaternion Algebra stuff for ternary quadratic forms.

/*** WORK IN PROGRESS ***/

intrinsic QuaternionAlgebra(M::ModFrmAlg) -> AlgQuat
{ Returns a quaternion algebra associated to a ternary quadratic space. }
	return QuaternionAlgebra(QuadraticSpace(Module(M)));
end intrinsic;

intrinsic QuaternionAlgebra(quadSpace::QuadSpace) -> AlgQuat
{ Returns a quaternion algebra of the ternary quadratic space. }
	// Return the quaternion algebra if already computed.
	if assigned quadSpace`QuaternionAlgebra then
		return quadSpace`QuaternionAlgebra;
	end if;

	// The dimension of the quadratic space.
	dim := Dimension(quadSpace);

	// Verify that this space is ternary.
	require dim eq 3: "Underlying quadratic space must be ternary.";

	// The base field.
	F := BaseRing(quadSpace);

	// The inner form associated to this quadratic space.
	innerForm := InnerForm(quadSpace);

	// Some helpful coefficients.
	b := innerForm[2,2] / 2;
	c := innerForm[3,3] / 2;
	r := innerForm[2,3];
	D := Determinant(innerForm) / 2;

	// Compute the quaternion algebra associated to this quadratic space.
	quat := QuaternionAlgebra(F, r^2-4*b*c, -c*D);

	// Return an `optimized' isomorphic copy of the quaternion algebra.
	quat := OptimizedRepresentation(quat);

	// Assign the quaternion algebra to the space of modular forms.
	quadSpace`QuaternionAlgebra := quat;

	return quat;
end intrinsic;

function constructOrder(gram)
	// Some convenient local variables.
	a := gram[1,1] / 2;
	b := gram[2,2] / 2;
	c := gram[3,3] / 2;
	r := gram[2,3];
	s := gram[1,3];
	t := gram[1,2];
	D := Determinant(gram)/2;

	// The quaternion algebra associated to the quadratic space in which
	//  this lattice lives.
	Q := QuaternionAlgebra(BaseRing(gram), r^2-4*b*c, -c*D);

	// Construct the basis of the corresponding order.
	a0 := 1;
	a1 := (Q.1 + r)/2;
	a2 := (Q.2 + c*t - s*(r - a1)) * Q.1^-1;
	a3 := (s - a2) * (r - a1) / c;

	// Verify that the basis elements have the correct trace and norm.
	assert Trace(a1) eq r and Norm(a1) eq b*c;
	assert Trace(a2) eq s and Norm(a2) eq a*c;
	assert Trace(a3) eq t and Norm(a3) eq a*b;

	// Return basis.
	return [ a0, a1, a2, a3 ];
end function;

intrinsic Order(M::ModFrmAlg) -> AlgAssVOrd
{ The order associated to the specified ternary lattice used to construct the
space of algebraic modular forms. }
	return Order(Module(M));
end intrinsic;

intrinsic Order(L::ModDedLat) -> AlgAssVOrd, AlgQuat
{ The order associated to the specified ternary lattice. }
	// The quadratic space associated to this space.
	quad := QuadraticSpace(L);

	// Require the lattice to be ternary.
	require Dimension(quad) eq 3: "Lattice must be ternary.";

	// Require that the lattice be free.
	require IsFree(L): "Lattice must be free.";

	// Retrieve a basis for this lattice.
	basis := Matrix(FreeBasis(L));

	// The Gram matrix associated to this free lattice.
	gram := basis * InnerForm(quad) * Transpose(basis);

	// Construct and return the corresponding order.
	return Order(constructOrder(gram));
end intrinsic;

intrinsic Order(L::Lat) -> AlgAssVOrd, AlgQuat
{ The order associated to the specified ternary lattice. }
	require Dimension(L) eq 3: "Lattice must be ternary";

	// The Gram matrix associated to this lattice.
	gram := ChangeRing(GramMatrix(L), Rationals());

	// Construct and return the corresponding order.
	return QuaternionOrder(constructOrder(gram));
end intrinsic;

intrinsic QuatHeckeOperator(L::Lat, n::RngIntElt) -> Assoc, SeqEnum
{ Computes the n-th quaternion Hecke operator for the lattice L. }
	// The order associated to the specified lattice.
	O := Order(L);

	// All right ideal classes associated to the order O.
	Is := RightIdealClasses(O);

	// A "matrix" of lattices.
	Ls := [* [* I * Conjugate(J) : J in Is *] : I in Is *];

	lats := [ [ Discriminant(LatticeWithGram(GramMatrix(Ls[i][j]) / Norm(Ls[i][j]))) : j in [1..#Is] ] : i in [1..#Is] ];
	lats;

	// The theta series associated to each 
	thetas := [* [* ThetaSeries(LatticeWithGram(ReducedGramMatrix(Ls[i][j])
		/ Norm(Ls[i][j])), n : ExponentConstant := 1/2) : j in [1..#Is]
			*] : i in [1..#Is] *];

	// The size of the unit group of each left order.
	Us := [ #Units(LeftOrder(I)) : I in Is ];

	// Build an empty associative array.
	Ts := AssociativeArray();

	// Populate the array with each of the Hecke operators.
	for k in [1..n] do
		mat := Matrix([ [ Coefficient(thetas[i][j], k) / Us[j]
			: j in [1..#Is] ] : i in [1..#Is] ]);
		Ts[k] := Transpose(ChangeRing(mat, Integers()));
	end for;

	// Return the associative array.
	return Ts, Is;
end intrinsic;


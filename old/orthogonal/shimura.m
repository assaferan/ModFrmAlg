// A simple script that returns the Shimura lift of the theta series of a
//  ternary quadratic form.

intrinsic ShimuraLift(L::Lat) -> Lat
{ Returns the Shimura lift of a ternary quadratic form. }
	// Make sure the dimension of the lattice is 3.
	require Dimension(L) eq 3: "Dimension must be precisely equal to 3.";

	// Get the Gram matrix.
	gram := GramMatrix(L);

	// Convenient shortcuts.
	a := gram[1,1] / 2;
	b := gram[2,2] / 2;
	c := gram[3,3] / 2;
	u := gram[2,3];
	v := gram[1,3];
	w := gram[1,2];

	// The associated quaternary Gram matrix.
	mat := Zero(MatrixRing(Integers(), 4));
	mat[1,1] := 1;
	mat[1,2] := u;
	mat[1,3] := v;
	mat[1,4] := w;
	mat[2,2] := b*c;
	mat[2,3] := u*v-c*w;
	mat[2,4] := u*w-b*v;
	mat[3,3] := a*c;
	mat[3,4] := v*w-a*u;
	mat[4,4] := a*b;
	mat +:= Transpose(mat);
	mat := ChangeRing(mat, Integers());

	return LatticeWithGram(mat);
end intrinsic;

intrinsic ClassNumber(Q::AlgQuat) -> RngIntElt
{ Returns the class number of the quaternion algebra. }
	require IsDefinite(Q): "Quaternion algebra must be definite.";
	ps := PrimeFactors(Discriminant(Q));
	ps := [ p : p in ps | p ne 2 ];
	return &*[ p-1 : p in ps ] / 12 +
		&*[ 1 - LegendreSymbol(-4,p) : p in ps ] / 4 +
		&*[ 1 - LegendreSymbol(-3,p) : p in ps ] / 3;
end intrinsic;

intrinsic QuaternionAlgebra(M::ModFrmAlg) -> SeqEnum
{ Constructs the quaternion algebra associated to this space. }
	if not assigned M`genus then _ := GenusReps(M); end if;
	require Dimension(M`genus`Representative) eq 3:
		"Dimension must be precisely equal to 3.";
	gram := GramMatrix(M`genus`Representative);
	D := Determinant(gram) / 2;
	b := gram[2,2] / 2;
	c := gram[3,3] / 2;
	u := gram[2,3];
	return QuaternionAlgebra(Rationals(), u^2 - 4*b*c, -c*D);
end intrinsic;

intrinsic RamifiedPlaces(M::ModFrmAlg) -> SeqEnum
{ Determines which places ramify in the quaternion algebra associated to the
space of algebraic modular forms. }
	Q := QuaternionAlgebra(M);
	places, _ := RamifiedPlaces(Q);
	return places;
end intrinsic;

intrinsic Level(f::ModFrmAlgElt) -> RngIntElt
{ Predicts the level at which the newform associated to a Hecke eigenform
will occur. }
	require f`IsEigenform: "Supplied element must be a Hecke eigenform.";
	disc := Discriminant(f`M`L);
	require IsSquarefree(disc): "Discriminant must be squarefree.";

	level := 1;

	ram := RamifiedPlaces(f`M);
	ram := [ ideal< f`M`L`R | Norm(p) > : p in ram ];

	fac := Factorization(disc);
	fac := [ ideal< f`M`L`R | Norm(p[1]) > : p in fac ];

	for p in fac do
		_ := HeckeOperator(f`M, p);
		eig := HeckeEigenvalues(f, p)[1][2] + 1;
		if (eig eq 1 and p in ram) or (eig eq -1 and not p in ram) then
			level *:= Norm(p);
		end if;
	end for;

	return level;
end intrinsic;


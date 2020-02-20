// Given a number field K, maximal order R, and a finite place pR sub R,
//  this script computes the quotient group K_p^* / (K_p^*)^2 as a GF(2) vector
//  space V, as well as a map m : V -> K. The codomain of this map provides
//  elements of K which represent the distinct square classes of the quotient.

declare attributes RngOrd:
	SquareClasses;

intrinsic LocalSquareGroup(pR::RngOrdIdl) -> ModFld, Map
{ Given a prime ideal pR in a number field K, this returns a vector space over
GF(2) isomorphic to K_p^\ast / (K_p^\ast)^2, as well as a map representing the
isomorphism, whose image contains representatives of each square class. }
	// Ensure that the specified ideal is prime.
	require IsPrime(pR): "The specified ideal must be prime.";

	// The order.
	R := Order(pR);

	// Check if the SquareClasses attribute has been assigned.
	if assigned R`SquareClasses then
		// If so, check whether we've computed the local square class
		//  group for this prime.
		if IsDefined(R`SquareClasses, pR) then
			// If so, recover it, and return it.
			g := R`SquareClasses[pR];
			return Domain(g), g;
		end if;
	end if;

	// The number field.
	K := NumberField(R);

	// Determine the residue class field for this prime, as well as the
	//  projection map proj : R -> F.
	F, proj := ResidueClassField(pR);

	// A primitive element of the prime ideal. This is an element generates
	//  the local maximal ideal pR_p.
	pi := PrimitiveElement(pR);

	if Characteristic(F) ne 2 then
		// In odd characteristic, the residue class field always
		//  contains a nonsquare element. Find one, then pull it back
		//  to the order.
		e := Nonsquare(F) @@ proj;

		// In odd characteristic, the local square class group is
		//  always the Klein-4 group, so let's build a two-dimensional
		//  vector space over GF(2) to represent it.
		V := VectorSpace(GF(2), 2);

		// Build the map representing the square class group in such a
		//  way that it also provides representatitves of each square
		//  class in its codomain.
		m := map< V -> K |
			// The map.
			x :-> (x[1] eq 0 select 1 else e) *
				(x[2] eq 0 select 1 else pi),
			// The inverse map.
			y :-> [ IsSquare((y / pi^v) @@ proj) select 0 else 1,
				v ] where v := Valuation(y, pR) >;
	else
		// The ramification degree of the local field over the base
		//  field. This is also equal to the order of the element 2.
		e := RamificationDegree(pR);

		// The inertial degree of this prime.
		f := Valuation(#F, 2);

		// The number of Z/2Z factors in the decomposition of the local
		//  squares group as an abelian group. See O'Meara 63:9.
		dim := f * e + 2;

		// Build a GF(2)-vector space of the appropriate dimension.
		V := VectorSpace(GF(2), dim);

		// TODO: Figure out why what follows works.

		I := pR^(2 * e + 1);
		Q, h := quo< R | I >;
		U, g := UnitGroup(Q);
		M, i := quo< U | 2 * U >;
		assert #M eq 2 ^ (dim - 1);
		piinv := WeakApproximation([pR], [-1]);

		function SquareRepNice(x, p, piinv)
			x *:= Denominator(x)^2;
			v := Valuation(x, p);
			assert v ge 0 and IsEven(v);
			if v ne 0 then x *:= piinv^v; end if;
			return Order(p) !x;
		end function;

		m := map< V -> K |
			x :-> ((M!ChangeUniverse(Eltseq(x)[1..dim-1], Integers())) @@ i @ g @@ h) * (x[dim] eq 0 select 1 else pi),
			y :-> Append(Eltseq(SquareRepNice(y * pi^v, pR, piinv) @@ g @ i), v) where v := Valuation(y, pR) mod 2 >;
	end if;

	// If we have not yet assigned the SquareClasses attribute to the
	//  current order, create it as an associative array.
	if not assigned R`SquareClasses then
		R`SquareClasses := AssociativeArray();
	end if;

	// Store the square classes data for future use.
	R`SquareClasses[pR] := m;

	return V, m;
end intrinsic;

intrinsic LocalSquareGroup(pR::RngInt) -> ModFld, Map
{ Given a prime ideal pR over the rationals, this returns a vector space over
GF(2) isomorphic to QQ_p^\ast / (QQ_p^\ast)^2, as well as a map representing the
isomorphism, whose image contains representatives of each square class. }
	// The integers as an order where the rationals are considered as a
	//  number field.
	R := Integers(RationalsAsNumberField());

	// Call the master routine for computing local square classes.
	return LocalSquareGroup(ideal< R | Norm(pR) >);
end intrinsic;

intrinsic LocalSquareGroup(p::RngIntElt) -> ModFld, Map
{ Given a rational prime integer p, this returns a vector space over GF(2)
isomorphic to QQ_p^\ast / (QQ_p^\ast)^2, as well as a map representing the
isomorphism, whose image contains representatives of each square class. }
	// Build an ideal from the element and pass it as a parameter.
	return LocalSquareGroup(ideal< Integers() | p >);
end intrinsic;

intrinsic RelativeQuadraticDefect_2(a::RngElt, pR::RngOrdIdl) -> RngIntElt
{ Computes the relative quadratic defect of a locally at pR. }
	// The quadratic defect of a locally at pR.
	d := QuadraticDefect_2(a, pR);

	return Type(d) eq Infty select Infinity() else d - Valuation(a, pR);
end intrinsic;

intrinsic QuadraticDefect_2(a::RngElt, pR::RngOrdIdl) -> RngIntElt {}
	// Ensure that the specified ideal is actually prime.
	require IsPrime(pR): "The specified ideal must be prime.";

	// The order associated to our prime ideal.
	R := Order(pR);

	// The number field.
	K := NumberField(R);

	// Verify that the element is coercible into the number field, then
	//  coerce it if so.
	ok, a := IsCoercible(K, a);
	require ok: "The first argument must be an element of (or coercible into) the order of the second argument.";

	// If the element is zero, then the pR-adic order of the quadratic
	//  defect is infinite (i.e. the quadratic defect is the zero ideal).
	if IsZero(a) then return Infinity(); end if;

	// The pR-adic order of the element a.
	v := Valuation(a, pR);

	// The trivial quadratic defect.
	if v mod 2 eq 1 then return v; end if;

	// A primitive element of the specified prime ideal.
	pi := PrimitiveElement(pR);

	// Divide out all powers of the primitive element from a, so that a
	//  now belongs to the pR-adic unit group.
	a /:= pi^v;

	// Make sure that a now has zero pR-adic order.
	assert Valuation(a, pR) eq 0;

	// Get the residue class field as well as the map projection map,
	//  proj : R -> F.
	F, proj := ResidueClassField(pR);

	// Determine whether this is a square in the residue class field.
	ok, s := IsSquare(a @ proj);

	if Characteristic(F) ne 2 then
		// If the field is non-dyadic and this element is a square in
		//  the residue class field, then it is a square in the local
		//  field (this is Hensel's lemma), hence the quadratic defect
		//  is the zero ideal; otherwise, the order of the ideal is
		//  equal to the p-adic order of the original element.
		//  See O'Meara, pg. 160.
		return ok select Infinity() else v;
	end if;

	// In even characteristic, all elements in the residue class field are
	//  squares.
	assert ok;

	// Modify our element in such a way that a equiv 1 mod pR.
	a /:= (s @@ proj)^2;

	// The p-adic order of a - 1.
	w := Valuation(a - 1, pR);

	// Confirm that a equiv 1 mod pR.
	assert w ge 1;

	// The p-adic order of 4*R_pR provides an upper bound upon the nonzero
	//  quadratic defects via the Local Squares Theorem (see O'Meara 63:2).
	max := 2 * Valuation(R!2, pR);

	while w lt max and IsEven(w) do
		// Find an element such that its residue is the square root of
		//  the element a (or epsilon_1 from O'Meara 63:2).
		delta_1 := SquareRoot(proj((a - 1) / pi^w)) @@ proj;

		// Express the element a as a square, then divide it out in
		//  such a way that a equiv 1 mod pR henceforth.
		a /:= (1 + delta_1 * pi^(w div 2))^2;

		// Update the p-adic order of a - 1.
		w := Valuation(a - 1, pR);
	end while;

	// Determine the p-adic order of the quadratic defect.
	if w gt max then
		return Infinity();
	elif w eq max then
		// Build the minimal polynomial of the element a (or epsilon
		//  from O'Meara 63:3).
		f := Polynomial([ F | ((a - 1) / 4) @ proj, 1, 1 ]);

		// This is the statement of O'Meara 63:3.
		return IsIrreducible(f) select v + w else Infinity();
	else
		// This is the statement of O'Meara 63:5.
		return v + w;
	end if;
end intrinsic;

intrinsic QuadraticDefect_2(a::RngElt, pR::RngInt) -> RngIntElt {}
	// The integers as an order of the rationals as a number field.
	K := RationalsAsNumberField();

	// Pay it forward.
	return QuadraticDefect_2(K!a, ideal< Integers(K) | Norm(pR) >);
end intrinsic;

intrinsic QuadraticDefect_2(a::RngElt, p::RngIntElt) -> RngIntElt {}
	return QuadraticDefect_2(a, ideal< Integers() | p >);
end intrinsic;


// Code adapted from Kirschmer's code for genus enumeration.

declare attributes RngOrd:
	SquareClasses;

declare attributes ModDedLat:
	M, MM, RCG, homRCG, ListOfPrimes;

function MapIntoClassGroupInternal(L, a, p)
	assert assigned(L`RCG);
	assert assigned(L`homRCG);
	assert assigned(L`M);
	assert assigned(L`MM);
	assert assigned(L`ListOfPrimes);

	if not (p in L`ListOfPrimes) then return (p^Valuation(a, p)) @@ L`homRCG; end if;

	result := Identity(L`RCG);

	F := Parent(a);
	R := Integers(F);

	IP := InfinitePlaces(F);
	error if not &and[IsReal(a) : a in IP], "Base field not totally real.";

	ListOfPrimes := L`ListOfPrimes;

	a_idele := [q eq p select Integers(F)!a else Integers(F)!1 : q in ListOfPrimes];
	t := a_idele;
	a_idele_inf := [1 : i in IP];
	i := Index(ListOfPrimes, p);

	if (p in ListOfPrimes) and (Valuation(a, p) gt 0) then
		assert (Valuation(a_idele[i], ListOfPrimes[i]) eq 1);
		s := WeakApproximation(ListOfPrimes, [-Valuation(a_idele[i], ListOfPrimes[i]) : i in [1..#ListOfPrimes]]);
		for j in [1..#a_idele] do
			a_idele[j] := R!quo< R | L`MM[j] > ! (a_idele[j]*s);
		end for;

		assert &and[Valuation(a_idele[i], ListOfPrimes[i]) eq 0 : i in [1..#ListOfPrimes]];
	else s := F!1;
	end if;

	for i in [1..#L`MM] do assert Valuation(L`MM[i], ListOfPrimes[i]) gt 0; end for;

	el := CRT(a_idele, L`MM);

	a_idele_inf := [];
	el := InverseMod(el, L`M);

	for j in [1..#IP] do
		if (Evaluate(el * s, IP[j]) lt 0) then
			a_idele_inf[j] := -1;
		else
			a_idele_inf[j] := 1;
		end if;
	end for;

	el2 := CRT(L`M, [1..#IP], R!1, a_idele_inf);

	assert &and[IsOne(quo< R | L`MM[k] > ! (s * el * el2 * t[k])) : k in [1..#t]];
	assert IsTotallyPositive(s * el * el2);


	g := (p^Valuation(a, p) * s * el * el2) @@ L`homRCG;

	return g;
end function;

intrinsic MapIntoClassGroup(L::ModDedLat, p::RngOrdIdl) -> GrpAbElt {}
	require Order(p) cmpeq BaseRing(L): "Incompatible arguments.";
	return MapIntoClassGroupInternal(L, NumberField(BaseRing(L))!UniformizingElement(p), p);
end intrinsic;

intrinsic CriticalPrimes(L::ModDedLat) -> SeqEnum
{ Returns a list of primes which will allow us to enumerate the entire genus. }
	// The number field.
	K := BaseRing(QuadraticSpace(L));

	// The order.
	R := BaseRing(L);

	// The discriminant ideal of the lattice.
	disc := Discriminant(L);

	// The factorization of the discriminant ideal.
	fac := Factorization(disc);

	// The prime ideals dividing discriminant ideal.
	idls := [ f[1] : f in fac ];

	// Initialize spinor norm data used to compute the critical primes.
	ListOfPrimes := [];
	ListOfHoms := [* *];
	ListOfSpinorNorms := [* *];
	CriticalPrimes := [];
	Gens := [];

	for P in idls do
		// Get the local multiplicative group modulo squares.
		V, g := LocalMultiplicativeGroupModSquares(P);

		// Retrieve the spinor norm as well, and check whether this
		//  is exactly equal to the unit group.
		Spinors, exact := SpinorNorm(L, P);

		if not exact then
			Append(~ListOfPrimes, P);
			Append(~ListOfHoms, g);
			Append(~ListOfSpinorNorms, Spinors);

			b := Basis(Spinors);
			Gens cat:= [ < a @ g, P > : a in b ];
			assert &and[ Valuation(gg, P) in {0,1}
				: gg in [ a @ g : a in b ] ];
		end if;
	end for;

	L`M := 1 * Integers(K);
	L`MM := [];
	L`ListOfPrimes := ListOfPrimes;

	for i in [1..#ListOfPrimes] do
		p := ListOfPrimes[i];
		e_p := Valuation(R!2, p);
		L`M *:= p^(1 + 2 * e_p);
		Append(~L`MM, p^(1 + 2 * e_p));
	end for;

	// Compute the ray class group for this lattice.
	L`RCG, L`homRCG := RayClassGroup(L`M, [1..Signature(K)]);

	ClassSubgroupGens := [];
	ClassSubgroup := sub< L`RCG | 2 * L`RCG >;

	for g in Gens do
		h := MapIntoClassGroupInternal(L, g[1], g[2]);
		Append(~ClassSubgroupGens, h);
		ClassSubgroup := sub< L`RCG | ClassSubgroupGens, 2 * L`RCG >;
	end for;

	MySubgroup := ClassSubgroup;

	maxnorm := Maximum({ Norm(p) : p in idls });
	GoodPrimes := [ p : p in PrimesUpTo(maxnorm, K : coprime_to := &*idls)];
	p_ind := 1;

	while #MySubgroup lt #L`RCG do
		while p_ind gt #GoodPrimes do
			maxnorm := NextPrime(maxnorm);
			GoodPrimes := [ p : p in PrimesUpTo(maxnorm, K : coprime_to := &*idls) ];
		end while;
		p := GoodPrimes[p_ind];

		h := MapIntoClassGroup(L, p);
		oldsize := #MySubgroup;
		Append(~ClassSubgroupGens, h);
		MySubgroup := sub< L`RCG | ClassSubgroupGens, 2 * L`RCG >;

		if #MySubgroup gt oldsize then
			Append(~CriticalPrimes, p);
		end if;

		p_ind +:= 1;
	end while;

	FactorGroup, FactorGroupHom := quo< L`RCG | ClassSubgroup >;

	if #CriticalPrimes eq 0 then
		
	end if;

	return CriticalPrimes;
end intrinsic;

intrinsic UnitSquareClassReps(P::RngOrdIdl) -> [] {}
	V, h := LocalMultiplicativeGroupModSquares(P);
	U := sub< V | [ V.i : i in [1..Dimension(V) - 1] ] >;
	return [ u @ h : u in U ];
end intrinsic;

intrinsic QuadraticDefect(a::RngElt, p::RngOrdIdl) -> RngIntElt {}
	// Ensure that the specified ideal is prime.
	require IsPrime(p): "The specified ideal must be prime.";

	// Verify that the first parameter is compatible with the specified
	//  prime.
	ok, a := IsCoercible(NumberField(Order(p)), a);
	require ok: "The first argument must be an element of the order of the second.";

	// If the element is zero, the defect is infinity by definition.
	if IsZero(a) then return Infinity(); end if;

	// Get the valuation of this element in the local field.
	v := Valuation(a, p);

	// A primitive element of this prime.
	pi := PrimitiveElement(p);

	// Divide out all powers of the prime from the specified element. This
	//  should now be a unit in the local number ring.
	a /:= pi^v;

	// The residue class field of the prime in its order.
	k, h := ResidueClassField(p);

	// Is this element a square in the residue class field?
	ok, s := IsSquare(h(a));

	if Minimum(p) ne 2 then
		// If the prime is odd, return infinity by definition if it
		//  is a square in the residue field, otherwise, return the
		//  valuation if it is not.
		return ok select Infinity() else v;
	end if;

	assert ok; // Since we're in an even prime, everything is a square.

	// We're going to make sure a has the form 1 + eps*pi^w.

	// Pull the square root of our specified unit back to the base ring,
	//  then square it in the field.
	a /:= (s @@ h)^2;

	// Determine the valuation of our unit after subtracting 1.
	w := Valuation(a - 1, p);

	// Sanity check via the Local Squares Theorem.
	assert w ge 1;

	// Twice the ramification index of 2.
	ee := 2 * Valuation(Order(p) ! 2, p);

	// If 1 < w < 2e is even, we can lift again (see O'Meara 63:2).
	while w lt ee and IsEven(w) do
		// Divide out all powers of pi from a-1, and find the square
		//  root in the residue field.
		s := SquareRoot(h((a - 1) / pi^w));

		// Update the element by pulling back this square root to the
		//  order, multiplying it by half the order, and adding 1 back.
		a /:= (1 + (s @@ h) * pi^(w div 2))^2;

		// Update the valuation.
		w := Valuation(a - 1, p);
	end while;

	// O'Meara 63:3 (w == ee) and 63:5 (ww < ee).
	if w gt ee then return Infinity();
	elif w eq ee then
		f := Polynomial([ k | ((a - 1) / 4) @ h, 1, 1 ]);
		return IsIrreducible(f) select Infinity() else v + w;
	else
		return v + w;
	end if;
end intrinsic;

intrinsic QuadraticDefect(a::FldRatElt, p::RngIntElt) -> RngIntElt {}
	// Ensure that the second argument is a prime element.
	require p ge 2 and IsPrime(p): "The second argument must be a prime.";

	// If the element is zero, return infinity by definition.
	if IsZero(a) then return Infinity(); end if;

	// The valuation of a in QQ_p.
	v := Valuation(a, p);

	// The defect for elements with odd valuations is always the valuation.
	if IsOdd(v) then return v; end if;

	// Turn this element into a unit in Z_p by dividing out all powers of p.
	a /:= p^v;

	// Turn this into an integer while preserving the square class.
	a := Numerator(a) * Denominator(a);

	// Handle the case when p is odd.
	if p ne 2 then
		return KroneckerSymbol(a, p) eq 1 select Infinity() else v;
	end if;

	// Handle the case when p eq 2.
	return case< a mod 8 | 1: Infinity(), 5: v + 2, default: v + 1 >;
end intrinsic;

intrinsic QuadraticDefect(a::RngIntElt, p::RngIntElt) -> RngIntElt {}
	return QuadraticDefect(a / 1, p);
end intrinsic;

function IsInA(a, p)
	e := Valuation(Order(p)!2, p);
	if (Type(QuadraticDefect(-a, p)) ne Infty) and (QuadraticDefect(-a, p) ge 0) then return true; end if;
	if (Type(QuadraticDefect(-a, p)) eq Infty) and (Valuation(a, p) ge -2*e) then return true; end if;
	return false;
end function;

intrinsic RelativeQuadraticDefect(a::RngElt, p::RngOrdIdl) -> RngIntElt {}
	q := QuadraticDefect(a, p);
	return q eq Infinity() select Infinity() else q - Valuation(a, p);
end intrinsic;

function N_function(a, b, g, p)
	V := Parent(b);
	if QuadraticDefect(a, p) eq Infinity() then return V; end if;
	B := Basis(V);

	preimages := V!0;
	for i in [1..#B] do
		b := B[i];
		preim := b @ g;
		preimages[i] := HilbertSymbol(a, preim, p) eq 1 select 0 else 1;
	end for;

	KernelGenerators := {B[i] : i in [1..#B] | preimages[i] eq 0};
	j := Min({ i : i in [1..#B] | preimages[i] eq 1});
	KernelGenerators join:= {B[i] + B[j] : i in [1..#B] | (preimages[i] eq 1) and (i ne j)};

	return sub<V | KernelGenerators >;
end function;

function G_function(a, V, g, p)
	U := UnitSquareClassReps(p);
	assert U[1] eq 1;

	e := Valuation(Order(p)!2, p);
	R := Valuation(a, p);
	d := RelativeQuadraticDefect(-a, p);
	pi := UniformizingElement(p);

	// ???
	if (R mod 2) eq 1 then d := 0; end if;

	if not IsInA(a, p) then
		return N_function(-a, (-a) @@ g, g, p);
	elif ((-1/4) @@ g eq a @@ g) then
		return sub< V | [ V.i : i in [1..Dimension(V) - 1] ] >;
	elif (R gt 4*e) then
		return sub<V| a@@g>;
	elif (2 * e lt R) and (R le 4 * e) then
		if (d le 2 * e - R / 2) then
			return (sub<V | (a@@g)> + sub<V|(1+pi^(R+d-2*e))@@g>) meet N_function(-a, (-a)@@g, g, p);
		else
			assert GF(2)!R eq 0;
			return (sub<V|(a@@g)> + sub<V|(1 + pi^(R/2))@@g>);
		end if;
	elif (R le 2*e) then
		if (d le e - R/2) then
			return N_function(-a, (-a)@@g, g, p);
		elif (e -R/2 lt d) and (d le 3*e/2 - R/4) then
			assert R mod 2 eq 0;
			return N_function(-a, (-a)@@g, g, p) meet sub<V|(1+pi^(IntegerRing()!(R/2) + d - e))@@g>;
		else
			return sub<V|(1+pi^(e-(Floor(e/2-R/4))))@@g>;
		end if;
	end if;
end function;

intrinsic SpinorNorm(L::ModDedLat, P::RngOrdIdl) -> ModTupFld, BoolElt
{ Compute the spinor norm of the lattice at a specified prime ideal. We also
return a flag indicating whether the spinor norm is exactly equal to the
units. }
	// Ensure that the specified ideal is a prime ideal.
	require IsPrime(P): "The specified ideal must be prime.";

	// Retrieve the local multipliactive group modulo squares.
	V, g := LocalMultiplicativeGroupModSquares(P);

	// The ramification degree of 2 in this prime ideal.
	e := Valuation(BaseRing(L) ! 2, P);

	// All but the last basis vector of the vector space V represents the
	//  entire unit group.
	exactlyUnits := sub< V | [ V.i : i in [1..Dimension(V) - 1] ] >;

	if Minimum(P) ne 2 then
		// Retrieve the Jordan constituents as well as the order of the
		//  valuation in the decomposition.
		cons, ords := JordanDecomp(L, P);

		// TODO: Try to understand what is happening here.
		for con in [ basis : basis in cons | #basis ge 2 ] do
			if #{ ord mod 2 : ord in ords } lt 2 then
				// All but the last basis vector of V.
				vecs := [ V.i : i in [1..Dimension(V) - 1] ];

				return sub< V | vecs >, true;
			else
				return V, false;
			end if;
		end for;

		// We now handle the case where all Jordan constituents are
		//  one-dimensional.

		// The inner form of the underlying quadratic space.
		M := InnerForm(QuadraticSpace(L));

		// The norm of each one-dimensional constituent.
		norms := [ (Matrix(con[1]) * M * Transpose(Matrix(con[1])))[1,1]
			: con in cons ];

		// The generators of the norm.
		normGens := [ norms[i] * norms[j]
			: i,j in [1..#norms] | i lt j ];

		// The vectors (in V) which generate the spinor norm.
		vecGens := [ x @@ g : x in normGens ];

		// Build the subspace of V corresponding to the spinor norm.
		spinNorm := sub< V | vecGens >;

		return spinNorm, spinNorm eq exactlyUnits;
	else
		// Initialize the subspace that will indicate spinor norm.
		spinNorm := sub< V | 0 >;

		// Get the "BONG".
		BONG := MakeGoodBONG(L, P);

		// Verify that this is a good "BONG".
		require IsGoodBONG(BONG, P): "Not a `good' BONG... whatever that means.";

		for i in [2..Dimension(L)] do
			spinNorm +:= G_function(BONG[i] / BONG[i-1], V, g, P);
		end for;

		if exists{ i : i in [1..Dimension(L)-2] | GF(2)!(Valuation(BONG[i+2], P) - Valuation(BONG[i], P)) eq 0} then
			alpha := IntegerRing()!Minimum({(Valuation(BONG[i+2], P) - Valuation(BONG[i], P))/2 : i in [1..Dimension(L)-2] | GF(2)!(Valuation(BONG[i+2], P) - Valuation(BONG[i],P)) eq 0});
			Uniformizer := UniformizingElement(P);
			spinNorm +:= sub< V | (1 + Uniformizer^alpha) @@ g >;
		end if;
	end if;

	return spinNorm, spinNorm eq sub< V | [V.i : i in [1..Dimension(L)-1]]>;
end intrinsic;

function SquareRepNice(x, p, piinv)
	x *:= Denominator(x)^2;
	v := Valuation(x, p);
	assert v ge 0 and IsEven(v);
	if v ne 0 then x *:= piinv^v; end if;
	return Order(p) ! x;
end function;

intrinsic LocalMultiplicativeGroupModSquares(p::RngIntElt) -> ModFld, Map
{ Given a prime ideal over some number field K, this returns a vector space
over GF(2) isomorphic to K_p^\ast/(K_p^\ast)^2 and a map representing the
isomorphism. }
	// Build the prime ideal with domain a number field.
	P := ideal< Integers(RationalsAsNumberField()) | p >;

	// Pay it forward.
	return LocalMultiplicativeGroupModSquares(P);
end intrinsic;

intrinsic LocalMultiplicativeGroupModSquares(P::RngOrdIdl) -> ModFld, Map
{ Given a prime ideal over some number field K, this returns a vector space
over GF(2) isomorphic to K_p^\ast/(K_p^\ast)^2 and a map representing the
isomorphism. }
	// Ensure that the specified ideal is prime.
	require IsPrime(P): "The ideal must be prime.";

	// Extract the order from the prime provided.
	R := Order(P);

	// The number field within the specified prime lives.
	K := NumberField(R);

	if Minimum(P) ne 2 then
		// A primitive element of the prime ideal.
		pi := PrimitiveElement(P);

		// The residue class field as well as a map h : K -> k.
		k, h := ResidueClassField(P);

		// Retrieve a nonsquare element from the residue class field
		//  and pull it back to the number field.
		e := Nonsquare(k) @@ h;

		// Build a two-dimensional vector space over GF(2).
		V := VectorSpace(GF(2), 2);

		m := map< V -> K |
			x :-> (x[1] eq 0 select 1 else e) *
				(x[2] eq 0 select 1 else pi),
			y :-> [ IsSquare((y / pi^v) @ h) select 0 else 1, v ]
				where v := Valuation(y, P) >;

		return V, m;
	else
		// If we haven't already computed the square classes for this
		//  ring, let's create an assocative array to store them for
		//  future use.
		if not assigned R`SquareClasses then
			R`SquareClasses := AssociativeArray();
		end if;

		// Attempt to retrieve the square classes for this prime from
		//  the associated array.
		ok, m := IsDefined(R`SquareClasses, P);

		// If defined, return the vector space and map pairing.
		if ok then return Domain(m), m; end if;

		// Ensure that this even prime ideal is defined in such a way
		//  that it is associated to an absolute order.
		if not IsAbsoluteOrder(R) then
			P := AbsoluteOrder(R) !! P;
		end if;

		// A primitive element of the prime ideal.
		pi := PrimitiveElement(P);

		// The ramification degree of this prime ideal.
		e := RamificationDegree(P);

		// The dimension of the vector GF(2) vector space that we will
		//  associate to this prime ideal.
		dim := Valuation(Norm(P), 2) * e + 2;

		// The vector space associated to this quotient group.
		V := VectorSpace(GF(2), dim);

		// Build an ideal of the specified power of the prime.
		I := P^(2 * e + 1);

		// ...and then build it's quotient ring and map.
		Q, h := quo< Order(I) | I >;

		// Retrieve the unit group of the quotient.
		U, g := UnitGroup(Q);

		// Build the unit group modulo the additive squares.
		M, i := quo< U | 2 * U >;

		// Ensure that the size of this quotient is half that of the
		//  underlying vector space.
		assert #M eq 2 ^ (dim - 1);

		// Use weak approximation to find an element which approximates
		//  the inverse of the primitive element.
		piinv := WeakApproximation([P], [-1]);

		// Build the map for this even prime.
		// TODO: Try to understand what the hell they are doing here.
		m := map< V -> K |
			x :-> ((M!ChangeUniverse(Eltseq(x)[1..dim-1], Integers())) @@i @ g @@ h) * (x[dim] eq 0 select 1 else pi),
			y :-> Append(Eltseq(SquareRepNice(y * pi^v, P, piinv) @@ g @ i), v) where v := Valuation(y, P) mod 2 >;

		// Return the vector space and associated map.
		return V, m;
	end if;
end intrinsic;

intrinsic MakeGoodBONG(L::ModDedLat, P::RngOrdIdl) -> []
{ Returns a good BONG of L at a dyadic prime P, as defined by C. Beli. }
	// Ensure that the specified ideal is compatible with the lattice.
	require Order(P) cmpeq BaseRing(L): "Incompatible base rings.";

	// Ensure that the specified ideal is prime.
	require IsPrime(P): "Specified ideal must be prime.";

	// Ensure that the prime is even.
	require Minimum(P) eq 2: "Specified prime must be even.";

	// Recover the maximal Jordan splitting at the specified prime.
	bases, ords := JordanDecomp(L, P : MaxSplit := true);

	// The inner form.
	innerForm := InnerForm(QuadraticSpace(L));

	// The full basis matrix.
	JJ := Matrix(&cat bases);

	// The individual Gram matrices associated to each block.
	G := [* Matrix(b) * innerForm * Transpose(Matrix(b)) : b in bases *];

	R := BaseRing(L);

	BONG := [];
	pi := UniformizingElement(P);
	for i in [1..#G] do
		GG := G[i];
		if Nrows(GG) eq 2 then
			BONG cat:=[ GG[1,1], Determinant(GG) / GG[1,1] ];
		elif Nrows(GG) eq 1 then
			Append(~BONG, GG[1,1]);
		else
			assert false;
		end if;
	end for;

	return BONG;
end intrinsic;

intrinsic IsGoodBONG(BONG::[], P::RngOrdIdl) -> BoolElt {}
	return &and[Valuation(BONG[i], P) le Valuation(BONG[i+2], P) : i in [1..#BONG-2]];
end intrinsic;


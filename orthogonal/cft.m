// This script contains a routine for computing "critical primes" associated to
//  a lattice. Critical primes are those primes necessary to enumerate the full
//  set of genus representatives for a lattice. This is determined by computing
//  the spinor class field, and then identifying prime ideals belonging to each
//  ray class. To do this, we utilize the spinor norms and other routines which
//  can be found in spinornorm.m and localsquares.m.

declare type PrimeData;
declare attributes PrimeData:
	pR, g, spinorNorm, factor;

declare attributes ModDedLat:
	primeData, Ray, ClassSubgroup, FactorGroup, FactorGroupHom;

function MapIntoClassGroupInternal(L, a, pR)
	// The identity element of the ray class group for this lattice.
	result := Identity(L`RCG);

	// The number field.
	K := Parent(a);

	// The order.
	R := Integers(K);

	// The infinite places of this number field.
	inf := InfinitePlaces(K);

	// The list of prime ideals under consideration.
	primes := [ data`pR : data in L`primeData ];

	// The index of pR in this set of prime ideals, if it exists. Note that
	//  the value of i will be zero, if pR is not contained in this list.
	i := Index(primes, pR);

	// Build an idele representing the prime data we collected via the
	//  spinor norms at bad primes.
	a_idele := [ R!(data`pR eq pR select a else 1) : data in L`primeData ];

	if i ne 0 and Valuation(a, pR) gt 0 then
		// Confirm that the element in the pR-th position of the idele
		//  is a primitive element.
		assert Valuation(a_idele[i], pR) eq 1;

		// The negative adic orders of each non-unit element for which
		//  this idele is defined.
		ords := [ -Valuation(a_idele[j], primes[j])
			: j in [1..#primes] ];

		// Obtain an element via weak approximation which satisfies the
		//  conditions set forth by the idele.
		s := WeakApproximation(primes, ords);

		for j in [1..#a_idele] do
			// The quotient group for the current prime factor.
			quot := quo< R | L`primeData[j]`factor >;

			// Multiply by an element so that each component of the
			//  idele is an adic unit. Then interpret it as an
			//  element of the quotient, and pull it back to R.
			a_idele[j] := R!quot!(a_idele[j] * s);

			// Verify that this element is an adic unit.
			assert Valuation(a_idele[j], primes[j]) eq 0;
		end for;
	else
		// If the specified prime is not represented in the idele,
		//  we may choose s to be simply 1.
		s := K!1;
	end if;

	// We will now find an element of the number field which is 1 mod the
	//  ray, and such that it is totally positive.

	// Use the Chinese Remainder Theorem to find an element which is
	//  congruent to a_idele[j] modulo the j-th ray factor.
	el := CRT(a_idele, [ data`factor : data in L`primeData ]);

	// Invert this element in the quotient of the ray.
	el := InverseMod(el, L`Ray);

	// Determine the sign of el * s at the j-th infinite place.
	a_idele_inf := [ Evaluate(el * s, inf[j]) lt 0 select -1 else 1
		: j in [1..#inf] ];

	// Use the Chinese Remainder Theorem again to find an element which is
	//  congruent to 1 modulo the ray, and which has the same sign as el at
	//  each infinite place.
	el2 := CRT(L`Ray, [1..#inf], R!1, a_idele_inf);

	// Confirm that we have found a totally positive element.
	assert IsTotallyPositive(s * el * el2);

	// Return an ideal.
	//  TODO: Figure out what this ideal means.
	return (pR^Valuation(a, pR) * s * el * el2) @@ L`homRCG;
end function;

intrinsic CriticalPrimes_2(L::ModDedLat) -> SeqEnum
{ Computes critical primes necessary to enumerate the full set of genus
representatives of a lattice via neighboring. }
	// The number field.
	K := BaseRing(QuadraticSpace(L));

	// The order.
	R := BaseRing(L);

	// The discriminant of the lattice.
	disc := Discriminant(L);

	// The distinct primes dividing the discriminant ideal.
	badPrimes := [ data[1] : data in Factorization(disc) ];

	// This will be a list of elements representing each square class
	//  generating the spinor norm in K_pR, where pR is given by the second
	//  parameter.
	gens := [];

	// A list of primes where the spinor norm is not the unit group.
	primeData := [* *];

	for pR in badPrimes do
		// Compute the local square class group at each bad prime.
		V, g := LocalSquareGroup(pR);

		// Compute the local spin group at this prime, and determine
		//  whether it represents the entire pR-adic unit group.
		spin, exact := SpinorNorm_2(L, pR);

		if not exact then
			// A basis for the local spinor norm group.
			basis := Basis(spin);

			// Map each basis generator into the local field.
			elts := [ x @ g : x in basis ];

			// Verify that each element is either a pR-adic unit,
			//  or a primtive element.
			assert &and[ Valuation(x, pR) in {0,1} : x in elts ];

			// Add a generator the local spin class to the list.
			gens cat:= [ < x, pR > : x in elts ];

			// Build a new object to store data associated to this
			//  prime ideal, then populate it's attributes.
			temp := New(PrimeData);
			temp`pR := pR;
			temp`factor := pR^(1 + 2 * RamificationIndex(pR));
			temp`g := g;
			temp`spinorNorm := spin;

			// Add this prime to the list.
			Append(~primeData, temp);
		end if;
	end for;

	// Update the prime data for this lattice.
	L`primeData := primeData;

	// Build the ray for the spinor class field.
	L`Ray := #primeData eq 0 select 1 * R else
		&*[ data`factor : data in primeData ];

	// Build the ray class group for this ray.
	L`RCG, L`homRCG := RayClassGroup(L`Ray, [1..Signature(K)]);

	// What follows is basically copy/pasted from Kirschmer/Lorch's code,
	//  as I really don't understand precisely what is going on.

	classSubgroupGens := [];
	classSubgroup := sub< L`RCG | 2 * L`RCG >;
	for g in gens do
		h := MapIntoClassGroupInternal(L, g[1], g[2]);
		Append(~classSubgroupGens, h);
		classSubgroup := sub< L`RCG | classSubgroupGens, 2 * L`RCG >;
	end for;
	L`ClassSubgroup := classSubgroup;

	MySubgroup := classSubgroup;
	CriticalPrimes := [];
	maxnorm := Maximum([ Norm(q) : q in badPrimes ]);
	goodPrimes := [ p : p in PrimesUpTo(maxnorm, K : coprime_to := disc) ];

	p_ind := 1;
	while #MySubgroup lt #L`RCG do
		while p_ind gt #goodPrimes do
			maxnorm := NextPrime(maxnorm);
			goodPrimes := [ p : p in PrimesUpTo(maxnorm, K :
				coprime_to := disc) ];
		end while;
		pR := goodPrimes[p_ind];
		h := MapIntoClassGroupInternal(L, K!PrimitiveElement(pR), pR);
		oldsize := #MySubgroup;
		Append(~classSubgroupGens, h);
		MySubgroup := sub< L`RCG | classSubgroupGens, 2 * L`RCG >;

		if #MySubgroup gt oldsize then
			Append(~CriticalPrimes, pR);
		end if;

		p_ind +:= 1;
	end while;

	L`FactorGroup, L`FactorGroupHom := quo< L`RCG | classSubgroup >;

	return CriticalPrimes, #L`FactorGroup;
end intrinsic;

intrinsic CriticalPrimes_2(M::ModFrmAlg) -> SeqEnum
{ Computes critical primes necessary to enumerate th full set of genus
representatives of a lattice via neighboring. }
	return CriticalPrimes_2(Module(M));
end intrinsic;


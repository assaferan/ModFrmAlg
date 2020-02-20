// This script is used to compute data related to L-functions.

intrinsic EulerFactor(f::ModFrmAlgElt, p::RngIntElt) -> SeqEnum
{ Returns the Euler factor of an eigenform at a specific prime. }
	return EulerFactor(f, ideal< f`M`L`R | p >);
end intrinsic;

intrinsic EulerFactor(f::ModFrmAlgElt, pR::RngOrdIdl) -> SeqEnum
{ Returns the Euler factor of an eigenform at a specific prime. }
	// Make sure that the modular form is an eigenform.
	if not f`IsEigenform then return []; end if;

	// Make sure we're dealing with algebraic modular forms defined over
	//  the rationals.
	// TODO: Remove and/or relax this restriction.
	require f`M`L`quadSpace`deg eq 1:
		"Euler factors only implemented for rational forms.";

	// Retrieve the list of Hecke eigenvalues.
	eigs := HeckeEigenvalues(f, pR);

	// Base ring in which to coerce coefficients.
	R := BaseRing(f`vec);

	// The norm of the prime ideal.
	p := Norm(pR);

	// We will handle these on a case-by-case basis until we can generalize
	//  this construction.
	if f`M`L`quadSpace`dim eq 5 then
		// If no eigenvalues are returned or more than one returned,
		//  just bail out.
		// TODO: Improve the logic here just in case someone
		//  accidentally computed a T(p^3) operator for some reason,
		//  even though they are always zero operators.
		if #eigs eq 0 or #eigs gt 2 then return []; end if;

		// Handle the case where both eigenvalues are known.
		if #eigs eq 2 then
			eigs := [ R!data[2] : data in eigs ];
			return [ 1, -eigs[1], p*eigs[2]+p^3+p,
				-eigs[1]*p^3, p^6 ];
		end if;

		// If the eigenvalue returned isn't associated to T(p), bail.
		if eigs[1][1] ne 1 then return []; end if;

		// The eigenvalue associated to T(p).
		eig := eigs[1][2];

		// Distinguish good primes from bad primes.
		if Norm(Discriminant(f`M`L)) mod p eq 0 then
			return [ 1, -(eig+1-2*p), p*(eig+1-p+p^2), -p^4 ];
		else
			return [ 1, -eig ];
		end if;
	elif f`M`L`quadSpace`dim eq 3 then
		if #eigs eq 0 then return []; end if;

		if Norm(Discriminant(f`M`L)) mod p eq 0 then
			return [ 1, -eigs[1][2]-1 ];
		else
			return [ 1, -eigs[1][2], p ];
		end if;
	end if;

	// Any case not yet handled just returns an empty list.
	return [];
end intrinsic;

intrinsic DirichletCoefficients(f::ModFrmAlgElt, twist::RngIntElt
	: Precision := 0) -> SeqEnum
{ Computes as many Dirichlet coefficients as possible. }
	// Verify that this is an eigenform.
	if not f`IsEigenform then return []; end if;

	// Make sure the space of algebraic forms was defined on the rationals.
	require f`M`L`quadSpace`deg eq 1:
		"Only implemented for forms coming from the rationals.";

	// Make sure we're requesting a valid quadratic twist.
	require twist ne 0: "Cannot twist by zero.";

	if Precision le 0 then
		// The Hecke operator types which have been computed.
		keys := Keys(f`M`Hecke`Ts);
		keys := [ x : x in keys ];

		// Prime ideals at which Hecke operators have been computed.
		Ps := {};
		for k in keys do Ps join:= Keys(f`M`Hecke`Ts[k]); end for;
		Ps := Sort([ x : x in Ps ], func<x,y | Norm(y)-Norm(x) >);

		// Twice the largest prime for which a Hecke operator has been
		//  computed.
		upTo := Norm(Ps[1]) * 2;
	else
		// Set upTo variable to the desired precision.
		upTo := Integers()!Precision;
	end if;

	// The base ring of the eigenspace.
	K := BaseRing(f`vec);

	// The power series ring.
	R := PowerSeriesRing(K);

	// An associative array of the power series expansion of the inverted
	//  Euler factors.
	coeffs := AssociativeArray();

	// A list of all primes up to the specified precision.
	Ps := PrimesUpTo(upTo);

	for p in Ps do
		// Determine the largest power exceeding the precision we seek.
		pow := 0; repeat pow +:= 1; until p^pow gt upTo;

		// The requested Euler factor.
		euler := EulerFactor(f, p);

		if #euler eq 0 then
			// Reassign the value of upTo.
			upTo := p-1;

			// Display a warning only if precision is not set to
			//  the default value.
			if Precision gt 0 then
				print "WARNING: Unable to compute Dirichlet" cat
					" coefficients to desired precision.";
				printf "Truncating to %o coefficients.\n", upTo;
				print "If you want more coefficients, you'll"
					cat " need to compute more Hecke"
					cat " operators.";
			end if;

			// Exit the for-loop.
			break;
		end if;

		// The coefficients of the inverted Euler factor.
		coeffs[p] := Coefficients(1 / R!euler);
	end for;

	// The list of Dirichlet coefficients.
	dirichlet := [];

	for n in [1..upTo] do
		val := 1;

		// Factorize the current integer.
		facs := Factorization(n);

		// Iteratively compute the coefficient at this integer.
		for fac in facs do
			if fac[2]+1 gt #coeffs[fac[1]] then
				c := 0;
			else
				c := coeffs[fac[1]][fac[2]+1];
			end if;
			//val *:= coeffs[fac[1]][fac[2]+1];
			val *:= c;
		end for;

		// Add value to the list.
		Append(~dirichlet, K!val);
	end for;

	// The conductor.
	cond := Norm(Discriminant(f`M`L));

	// A correction factor at bad primes.
	for p in PrimeFactors(cond) do
		if p le #dirichlet then
			if IsInThetaKernel(f) then
				dirichlet[p] +:= 1;
			end if;
		end if;
	end for;

	// If we request a 
	if twist ne 1 then
		// Retrieve the quadratic character.
		chi := KroneckerCharacter(twist);

		// Twist the Dirichlet coefficients.
		return [ Evaluate(chi, n) * dirichlet[n]
			: n in [1..#dirichlet] ];
	end if;

	return dirichlet;
end intrinsic;

intrinsic DirichletCoefficients(f::ModFrmAlgElt : Precision := 0) -> SeqEnum
{ Computes the twisted Dirichlet coefficients. }
	// Retrieve and return the untwisted Dirichlet coefficients.
	return DirichletCoefficients(f, 1 : Precision := Precision);
end intrinsic;

// TODO: Adjust the possible twists. The L-series doesn't quite match up in
//  some cases.
intrinsic LSeries(f::ModFrmAlgElt, twist::RngIntElt : Precision := 0) -> LSer
{ Computes the L-series of the eigenform. }
	// Make sure this is an eigenform.
	require f`IsEigenform: "Can only compute L-series for eigenforms.";

	// Make sure the base field is the rationals... for now.
	require f`M`L`quadSpace`deg eq 1:
		"Base field of definition must be the rationals.";

	// Make sure we're requesting a valid quadratic twist.
	require twist ne 0: "Cannot twist by zero.";

	// The discriminant of the form.
	disc := Norm(Discriminant(f`M`L));

	// Make sure that the conductor/discriminant is prime... for now.
	//require IsPrime(disc): "Conductor must be prime... for now.";

	// The dimension of the quadratic space.
	dim := f`M`L`quadSpace`dim;

	// Assign the conductor of the L-series.
	if twist ne 1 and dim eq 3 then
		// The quadratic character we're twisting by.
		chi := KroneckerCharacter(twist);

		// The appropriate conductor.
		conductor := disc * Conductor(chi)^2;
	else
		// The conductor is the same as the discriminant.
		// TODO: This isn't always true, but since we're dealing with
		//  prime discriminants (for now), this is correct.
		conductor := disc;

		// Default the twist to nontwist.
		twist := 1;
	end if;

	// Retrieve the Dirichlet coefficients.
	dirichlet := DirichletCoefficients(f, twist : Precision := Precision);

	// Determine the sign of the functional equation.
	sign := JacobiSymbol(twist, disc);

	// Reverse the sign if we're computing an imaginary twist.
	// TODO: Verify that this is correct. Not entirely sure, but it seems
	//  to work.
	if twist lt 0 then sign := -sign; end if;

	if sign eq 0 then
		require false:
			"WARNING: The twist and discriminant are not coprime.";
	end if;

	// Handle dimensions on a case-by-case basis for now.
	if dim eq 5 then
		// Assign poles.
		poles := IsInThetaKernel(f) select [] else [3];

		// Return the appropriate L-series.
		return LSeries(4, [-1,0,0,1], conductor, dirichlet
			: Sign := sign, Poles := poles);
	elif dim eq 3 then
		return LSeries(2, [0,1], conductor, dirichlet
			: Sign := sign);
	end if;

	return [];
end intrinsic;

intrinsic LSeries(f::ModFrmAlgElt : Precision := 0) -> LSer
{ Compute the L-series of the twisted eigenform. }
	return LSeries(f, 1 : Precision := Precision);
end intrinsic;

intrinsic IsInThetaKernel(f::ModFrmAlgElt) -> BoolElt
{ Determines whether the linear combination of theta series associated to this
vector vanishes. }
	// If this has already been computed, return the result.
	if assigned f`IsInThetaKernel then return f`IsInThetaKernel; end if;

	// If theta series haven't been assigned, assign them.
	if not assigned f`M`genus`ThetaSeries then
		// An array for storing the ordered list of theta series.
		array := [];

		for i in [1..#f`M`genus`Representatives] do
			// Assign the appropriate lattice depending on the
			//  degree of the field extension we're over.
			if f`M`L`quadSpace`deg eq 1 then
				L := f`M`genus`Representatives[i];
			else
				L := ZLattice(f`M`genus`Representatives[i]);
			end if;

			// Add theta series to the array.
			Append(~array, ThetaSeries(L, 25));
		end for;

		// Assign theta series for these genus representatives.
		f`M`genus`ThetaSeries := array;
	end if;

	// Retrieve the theta series as a matrix over th correct base ring.
	thetas := f`M`genus`ThetaSeries;
	thetas := [ [ Coefficient(theta, 2*i) : i in [0..12] ]
		: theta in thetas ];
	thetas := ChangeRing(Matrix(thetas), BaseRing(f`vec));

	// The resulting vector.
	result := Matrix(f`vec) * thetas;

	// Store this result in memory so we don't have to recompute later.
	f`IsInThetaKernel := &and[ x eq 0 : x in Eltseq(result) ];

	return f`IsInThetaKernel;
end intrinsic;

intrinsic ThetaKernel(M::ModFrmAlg) -> SeqEnum
{ Finds all eigenforms of M whose theta series vanish. }
	// Retrieve Hecke eigenforms.
	eigenforms := HeckeEigenforms(M);

	return [ e : e in eigenforms | IsInThetaKernel(e) ];
end intrinsic;


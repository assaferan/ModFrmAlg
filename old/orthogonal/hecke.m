// Generic implementations of the Hecke operators.

import "../structure/modfrmalg.m" : ModFrmAlgInit;
import "QQ/hecke-QQ.m" : HeckeOperatorTrivialWeightQQ,
	HeckeOperatorTrivialWeightViaOrbits;
import "QQ/hecke-fast-QQ.m": HeckeOperatorTrivialWeightFastQQ;
import "CN1/hecke-CN1.m" : HeckeOperatorTrivialWeightCN1;

intrinsic SetHeckeOperator(
	M::ModFrmAlg, T::AlgMatElt, pR::RngOrdIdl, k::RngIntElt)
{ Sets the k-th order Hecke operator at the specified prime for this form. }
	// If assocative array does not exist for this dimension, create one.
	if not IsDefined(M`Hecke`Ts, k) then
		M`Hecke`Ts[k] := AssociativeArray();
	end if;

	// Assign Hecke matrix.
	M`Hecke`Ts[k][pR] := T;
end intrinsic;

intrinsic SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, pR:RngOrdIdl)
{ Sets the 1-st order Hecke operator at the specified prime for this form. }
	SetHeckeOperator(M, T, pR, 1);
end intrinsic;

intrinsic SetHeckeOperator(
	M::ModFrmAlg, T::AlgMatElt, pR::RngInt, k::RngIntElt)
{ Sets the k-th order Hecke operator at the specified prime for this form. }
	SetHeckeOperator(M, T, ideal< BaseRing(Module(M)) | Norm(pR) >, k);
end intrinsic;

intrinsic SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, pR::RngInt)
{ Sets the 1-st order Hecke operator at the specified prime for this form. }
	SetHeckeOperator(M, T, pR, 1);
end intrinsic;

intrinsic SetHeckeOperator(
	M::ModFrmAlg, T::AlgMatElt, p::RngIntElt, k::RngIntElt)
{ Sets the k-th order Hecke operator at the specified prime for this form. }
	SetHeckeOperator(M, T, ideal< Integers() | p >, k);
end intrinsic;

intrinsic SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, p::RngIntElt)
{ Sets the 1-st order Hecke operator at the specified prime for this form. }
	SetHeckeOperator(M, T, p, 1);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt
	: BeCareful := true, Force := false, Estimate := false, UseLLL := true,
		Fast := false, Orbits := false) -> AlgMatElt
{ Computes the requested Hecke operator. }
	// Initialize the space of algebraic modular forms, if needed.
	ModFrmAlgInit(M : Orbits := Orbits);

	// Verify that the supplied ideal is prime.
	require IsPrime(pR): "Provided ideal must be prime.";

	// If the orders don't agree, check to see if their field of fractions
	//  are isomorphic. If so, convert the ideal passed as an argument to
	//  an ideal in terms of the number ring given by the appropriate ring.
	if Order(pR) ne BaseRing(Module(M)) then
		// Assign fields of fractions.
		K1 := FieldOfFractions(Order(pR));
		K2 := FieldOfFractions(BaseRing(Module(M)));

		// Check for isomorphism.
		isom, map := IsIsomorphic(K1, K2);

		// If they are isomorphic, reassign the provided prime ideal.
		require isom: "Incompatible base rings.";

		// Assign the new prime ideal.
		pR := ideal< BaseRing(Module(M))
			| [ map(x) : x in Basis(pR) ] >;
	end if;

	// Look for the requested Hecke operator.
	ok, Ts := IsDefined(M`Hecke`Ts, k);
	if ok and not Force then
		ok, T := IsDefined(Ts, pR);
		if ok then return T; end if;
	end if;

	// Choose the appropriate routine for computing Hecke operators.
	if Degree(BaseRing(M)) eq 1 then
		if Orbits then
			hecke := HeckeOperatorTrivialWeightViaOrbits(M,
				Norm(pR), k : BeCareful := BeCareful,
				Estimate := Estimate, UseLLL := UseLLL);
		elif Fast and #HeckeOperators(M) ne 0 then
			hecke := HeckeOperatorTrivialWeightFastQQ(M, Norm(pR), k
				: BeCareful := BeCareful, Estimate := Estimate,
					UseLLL := UseLLL);
		else
			hecke := HeckeOperatorTrivialWeightQQ(M, Norm(pR), k
				: BeCareful := BeCareful, Estimate := Estimate,
					UseLLL := UseLLL);
		end if;
	else
		hecke := HeckeOperatorTrivialWeightCN1(M, pR, k
			: BeCareful := BeCareful, Estimate := Estimate);
	end if;

	// Sets the Hecke operator in the internal data structure for this
	//  algebraic modular form.
	SetHeckeOperator(M, hecke, pR, k);

	// Returns the computed Hecke operator.
	return hecke;
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngOrdIdl
	: BeCareful := true, Force := false, Estimate := false, UseLLL := true,
		Fast := false, Orbits := false) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1. }
	return HeckeOperator(M, pR, 1
		: BeCareful := BeCareful, Force := Force, Estimate := Estimate,
			UseLLL := UseLLL, Fast := Fast, Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngInt, k::RngIntElt
	: BeCareful := true, Force := false, Estimate := false, UseLLL := true,
		Fast := false, Orbits := false) -> AlgMatElt
{ Computes the requested Hecke operator, under the assumption that the base
number field is the rationals. }
	// Make sure that the base ring of the number field is the rationals.
	require Degree(BaseRing(M)) eq 1: "Base ring must be the rationals.";

	return HeckeOperator(M, ideal< BaseRing(Module(M)) | Norm(pR) >, k
		: BeCareful := BeCareful, Force := Force, Estimate := Estimate,
			UseLLL := UseLLL, Fast := Fast, Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngInt
	: BeCareful := true, Force := false, Estimate := false, UseLLL := true,
		Fast := false, Orbits := false) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1, under the
assumption that the base number field is the rationals. }
	return HeckeOperator(M, ideal< BaseRing(Module(M)) | Norm(pR) >, 1
		: BeCareful := BeCareful, Force := Force, Estimate := Estimate,
			UseLLL := UseLLL, Fast := Fast, Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, p::RngIntElt, k::RngIntElt
	: BeCareful := true, Force := false, Estimate := false, UseLLL := true,
		Fast := false, Orbits := false) -> AlgMatElt
{ Computes the requested Hecke operator under the assumption that the base
number field is the rationals. }
	return HeckeOperator(M, ideal< Integers() | p >, k
		: BeCareful := BeCareful, Force := Force, Estimate := Estimate,
			UseLLL := UseLLL, Fast := Fast, Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, p::RngIntElt
	: BeCareful := true, Force := false, Estimate := false, UseLLL := true,
		Fast := false, Orbits := false) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1, under the
assumption that the base number field is the rationals. }
	return HeckeOperator(M, ideal< Integers() | p >, 1
		: BeCareful := BeCareful, Force := Force, Estimate := Estimate,
			UseLLL := UseLLL, Fast := Fast, Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperators(M::ModFrmAlg, k::RngIntElt) -> SeqEnum, SeqEnum
{ Returns an ordered list of Hecke operators computed so far along with an
ordered list of ideals to which they belong. }
	// Check whether any matrices have been computed for this dimension.
	if not IsDefined(M`Hecke`Ts, k) then return [], []; end if;

	// Retrieve the ideals of those matrices that have been computed.
	idls := Keys(M`Hecke`Ts[k]);
	idls := Sort([ x : x in idls ], func<x,y | Norm(x)-Norm(y) >);

	return [ M`Hecke`Ts[k][x] : x in idls ], idls;
end intrinsic;

intrinsic HeckeOperators(M::ModFrmAlg) -> SeqEnum, SeqEnum
{ Returns an ordered list of Hecke operators computed so far along with an
ordered list of ideals to which they belong. }
	return HeckeOperators(M, 1);
end intrinsic;


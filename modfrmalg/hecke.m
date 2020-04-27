freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: hecke.m (class for Hecke Operators data on spaces of algebraic
                  modular forms)

   Class for managing the Hecke operators on a space of algebraic 
   modular forms.

   04/27/20: Changed default value of BeCareful to false.
             Modified to not use LLL when group is SO.

   04/16/20: Added the parameter UseLLL, and modified the Hecke Operator so that
             HeckeOperator(T,p) will always compute the Hecke operator at a
             prime above p.

   03/29/20: Fixed a bug in HeckeOperator - when needed to identify base
             rings of ideal and ModFrmAlg, the resulting ideal was not prime
             Now uses Generators(pR) instead of Basis(pR)

   03/26/20: Modified to use the orbit method only for one-dimensional
             representations, until we get it to work in higher dimensions.

   03/11/20: Modified to use the orbit method.

   03/10/20: started from the orthogonal modular forms structure
 
 ***************************************************************************/

//imports

import "modfrmalg.m" : ModFrmAlgInit;
import "../neighbors/hecke-CN1.m" : HeckeOperatorCN1;

// Data structure

declare type ModHecke;
declare attributes ModHecke:
	// A list of Hecke matrices.
	Ts,

	// Hecke Eigenforms.
	Eigenforms,

	// A shortcut to the Eisenstein series.
	EisensteinSeries;

// set methods

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

// get (computation) methods

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := false,
			  UseLLL := true,
			  Fast := false,
			  Orbits := false) -> AlgMatElt
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
		       | [ map(x) : x in Generators(pR) ] >;
	end if;

	// Look for the requested Hecke operator.
	ok, Ts := IsDefined(M`Hecke`Ts, k);
	if ok and not Force then
		ok, T := IsDefined(Ts, pR);
		if ok then return T; end if;
	end if;

	// Choose the appropriate routine for computing Hecke operators.
	// Right now, in this version, we do not choose, but use always the same
	// function.

	// !!! Right now, when the weight is non-trivial, the orbit method
	// fails - have to check why. Meanwhile this is our temporary fix

	if (Dimension(M`W) gt 1) then
	    use_orbits := false;
	else
	    use_orbits := Orbits;
	end if;

	// Currently LLL doesn't seem to work for SO
	if UseLLL and not IsSpecialOrthogonal(M) then
	    use_LLL := true;
	else
	    use_LLL := false;
	end if;
	
        hecke := HeckeOperatorCN1(M, pR, k
				  : BeCareful := BeCareful,
				    UseLLL := use_LLL,
				    Estimate := Estimate,
				    Orbits := use_orbits);

	// Sets the Hecke operator in the internal data structure for this
	//  algebraic modular form.
	SetHeckeOperator(M, hecke, pR, k);

	// Returns the computed Hecke operator.
	return hecke;
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngOrdIdl
			: BeCareful := false,
			  Force := false,
			  Estimate := false,
			  UseLLL := true,
			  Fast := false,
			  Orbits := true) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1. }
	return HeckeOperator(M, pR, 1
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Fast := Fast,
			       Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngInt, k::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := false,
			  UseLLL := true,
			  Fast := false,
			  Orbits := false) -> AlgMatElt
{ Computes the requested Hecke operator, under the assumption that the base
number field is the rationals. }
	// Make sure that the base ring of the number field is the rationals.
//	require Degree(BaseRing(M)) eq 1: "Base ring must be the rationals.";

        p := Factorization(ideal< BaseRing(Module(M)) | pR >)[1][1];
	return HeckeOperator(M, p, k
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Fast := Fast,
			       Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngInt
			: BeCareful := false,
			  Force := false,
			  Estimate := false,
			  UseLLL := true,
			  Fast := false,
			  Orbits := true) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1, under the
									  assumption that the base number field is the rationals. }

	return HeckeOperator(M, pR, 1
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Fast := Fast,
			       Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, p::RngIntElt, k::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := false,
			  UseLLL := true,
			  Fast := false,
			  Orbits := false) -> AlgMatElt
{ Computes the requested Hecke operator under the assumption that the base
number field is the rationals. }
        pR := Factorization(ideal< BaseRing(Module(M)) | p >)[1][1];
        return HeckeOperator(M, pR, k
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Fast := Fast,
			       Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, p::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := false,
			  UseLLL := true,
			  Fast := false,
			  Orbits := true) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1, under the
assumption that the base number field is the rationals. }
	return HeckeOperator(M, p, 1
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Fast := Fast,
			       Orbits := Orbits);
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


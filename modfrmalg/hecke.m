freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: hecke.m (class for Hecke Operators data on spaces of algebraic
                  modular forms)

   Class for managing the Hecke operators on a space of algebraic 
   modular forms.

   05/27/20: Changed default values to use orbits and estimate, but not
             use LLL, as it doesn't work well with SO(n)

   05/26/20: Modified the bad modulus, as discriminant might be 2-integral

   05/08/20: Added the attribute decomposition for future use.

   05/04/20: Modified HeckeOperator to use orbits if instructed to, 
             now that it actually works!

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
import "../neighbors/hecke-CN1.m" : HeckeOperatorCN1,
                                    HeckeOperatorCN1Sparse,
                                    HeckeOperatorAndGenusCN1;

// Data structure

declare type ModHecke;
declare attributes ModHecke:

	// decomposition to irreducible spaces for the Hecke algebra
	decomposition,
	
	// images of the standard basis vectors by Hecke operators
	standard_images,
	
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

	// Assign Hecke images of standard basis vectors
	if not assigned M`Hecke`standard_images then
	    M`Hecke`standard_images :=
		[AssociativeArray() : i in [1..Dimension(M)]];
	end if;
	for i in [1..Dimension(M)] do
	    if not IsDefined(M`Hecke`standard_images[i], k) then
		M`Hecke`standard_images[i][k] := AssociativeArray();
	    end if;
	    M`Hecke`standard_images[i][k][pR] := Transpose(T)[i];
	end for;
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
			  Estimate := true,
			  UseLLL := true,
			  Fast := false,
			  Orbits := true) -> AlgMatElt
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
				    Orbits := Orbits);

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
			  Estimate := true,
			  UseLLL := false,
			  Fast := false,
			  Orbits := true) -> AlgMatElt
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
			  Estimate := true,
			  UseLLL := false,
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

function SparseRepresentation(M, v)
// Sparse representation of vector v.
   sp := [];
   v  := Eltseq(v);
   i := 1;
   space_start := 1;
   for space_idx in [1..#M`H] do
       for vec_idx in [1..Dimension(M`H[space_idx])] do
	   if v[i] ne 0 then
               Append(~sp, <v[i],space_idx,space_start>);
	   end if;
	   i +:= 1;
       end for;
       space_start := i;
   end for;
 
   return sp;
end function;

intrinsic HeckeImages(M::ModFrmAlg, i::RngIntElt,
				       n::RngIntElt, k::RngIntElt :
		      BeCareful := false,
		      Estimate := true,
		      Orbits := true,
		      UseLLL := false) -> SeqEnum
{The images of the ith standard basis vector
 under the Hecke operators Tp^k for p good prime, such that Norm(p)<=n
These are computed using sparse methods that don't
require computing the full Hecke operator.}  
   assert 1 le i and i le Dimension(M);
   if not assigned M`Hecke`standard_images then
       M`Hecke`standard_images :=
	   [AssociativeArray() : j in [1..Dimension(M)]];
   end if;
   s := SparseRepresentation(M, VectorSpace(M).i);
   space_idx := s[1][2];
   start_idx := s[1][3];
   end_idx := start_idx + Dimension(M`H[space_idx]) - 1;
   assert start_idx le i and i le end_idx;
   // Due to the nature of the computation, we compute an entire block together
   if not IsDefined(M`Hecke`standard_images[i], k) then
       for j in [start_idx..end_idx] do
	   M`Hecke`standard_images[j][k] := AssociativeArray();
       end for;
   end if;
   // !!! TODO : maybe should restrict to one of each relevant norm
   // also lift split restriction when we fix handling that case
   /*
   ps := [ p : p in PrimesUpTo(n, BaseRing(M)) |
	   Gcd(Integers()!Norm(Discriminant(Module(M))),
	       Norm(p)) eq 1 and IsSplit(p)];
  */
   // bad_modulus := Numerator(Norm(Discriminant(Module(M))));
   ps := [Factorization(Integers(BaseRing(M)) !! p)[1][1] :
	  //	  p in PrimesUpTo(n, Rationals() : coprime_to := bad_modulus)];
	  p in PrimesUpTo(n, Rationals())];
   if SpaceType(AmbientSpace(Module(M))) eq "Hermitian" then
       alpha := Involution(ReflexiveSpace(Module(M)));
       // F := FixedField(alpha);
       // ZZ_F := Integers(F);
       // ps := [p : p in ps | IsSplit(p)];
       ps := [p : p in ps | alpha(p) ne p];
   end if;
   // generate more images..
   new_ps := [p : p in ps | p notin Keys(M`Hecke`standard_images[i][k])];
   for p in new_ps do
       sp_hec := HeckeOperatorCN1Sparse(M, p, k, s : BeCareful := BeCareful,
						     Estimate := Estimate,
						     Orbits := Orbits,
						     UseLLL := UseLLL);
       sp_mat := sp_hec[space_idx];
       for j in [start_idx..end_idx] do
	   M`Hecke`standard_images[j][k][p] :=
	       Transpose(sp_mat)[j-start_idx+1];
       end for;
   end for;
   return M`Hecke`standard_images[i][k];       
end intrinsic;


intrinsic HeckeImages(M::ModFrmAlg, i::RngIntElt,
				       ps::SeqEnum, k::RngIntElt :
		      BeCareful := false,
		      Estimate := true,
		      Orbits := true,
		      UseLLL := false) -> SeqEnum
{The images of the ith standard basis vector
 under the Hecke operators Tp^k for p good prime, such that Norm(p)<=n
These are computed using sparse methods that don't
require computing the full Hecke operator.}  
   assert 1 le i and i le Dimension(M);
   if not assigned M`Hecke`standard_images then
       M`Hecke`standard_images :=
	   [AssociativeArray() : j in [1..Dimension(M)]];
   end if;
   s := SparseRepresentation(M, VectorSpace(M).i);
   space_idx := s[1][2];
   start_idx := s[1][3];
   end_idx := start_idx + Dimension(M`H[space_idx]) - 1;
   assert start_idx le i and i le end_idx;
   // Due to the nature of the computation, we compute an entire block together
   if not IsDefined(M`Hecke`standard_images[i], k) then
       for j in [start_idx..end_idx] do
	   M`Hecke`standard_images[j][k] := AssociativeArray();
       end for;
   end if;
   
   new_ps := [p : p in ps | p notin Keys(M`Hecke`standard_images[i][k])];
   for p in new_ps do
       sp_hec := HeckeOperatorCN1Sparse(M, p, k, s : BeCareful := BeCareful,
						     Estimate := Estimate,
						     Orbits := Orbits,
						     UseLLL := UseLLL);
       sp_mat := sp_hec[space_idx];
       for j in [start_idx..end_idx] do
	   M`Hecke`standard_images[j][k][p] :=
	       Transpose(sp_mat)[j-start_idx+1];
       end for;
   end for;

   return M`Hecke`standard_images[i][k];       
end intrinsic;


intrinsic HeckeOperatorAndGenus(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := true,
			  UseLLL := true,
			  Fast := false,
			  Orbits := true) -> AlgMatElt
{ Computes the requested Hecke operator. }

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

	// Currently LLL doesn't seem to work for SO
	if UseLLL and not IsSpecialOrthogonal(M) then
	    use_LLL := true;
	else
	    use_LLL := false;
	end if;

        hecke := [];
        HeckeOperatorAndGenusCN1(~M, pR, k, ~hecke
				  : BeCareful := BeCareful,
				    UseLLL := use_LLL,
				    Estimate := Estimate,
				    Orbits := Orbits);

	// Sets the Hecke operator in the internal data structure for this
	//  algebraic modular form.
	SetHeckeOperator(M, hecke, pR, k);

	// Returns the computed Hecke operator.
	return hecke;
end intrinsic;

intrinsic HeckeOperatorAndGenus(M::ModFrmAlg, pR::RngOrdIdl
			: BeCareful := false,
			  Force := false,
			  Estimate := false,
			  UseLLL := true,
			  Fast := false,
			  Orbits := true) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1. }
	return HeckeOperatorAndGenus(M, pR, 1
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Fast := Fast,
			       Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperatorAndGenus(M::ModFrmAlg, pR::RngInt, k::RngIntElt
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
	return HeckeOperatorAndGenus(M, p, k
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Fast := Fast,
			       Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperatorAndGenus(M::ModFrmAlg, p::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := true,
			  UseLLL := false,
			  Fast := false,
			  Orbits := true) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1, under the
assumption that the base number field is the rationals. }
	return HeckeOperatorAndGenus(M, p, 1
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Fast := Fast,
			       Orbits := Orbits);
end intrinsic;

intrinsic HeckeOperatorAndGenus(M::ModFrmAlg, p::RngIntElt, k::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := true,
			  UseLLL := false,
			  Fast := false,
			  Orbits := true) -> AlgMatElt
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

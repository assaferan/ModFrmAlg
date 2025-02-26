freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                     
                  E. Assaf, M. Greenberg, J. Hein, J. Voight
         using lattices over number fields by M. Kirschmer and D. Lorch        
                                                                            
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
b

   03/26/20: Modified to use the orbit method only for one-dimensional
             representations, until we get it to work in higher dimensions.

   03/11/20: Modified to use the orbit method.

   03/10/20: started from the orthogonal modular forms structure
 
 ***************************************************************************/

// Here are the intrinsics this file defines
// SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, pR::RngOrdIdl, k::RngIntElt)
// SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, pR:RngOrdIdl)
// SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, pR::RngInt, k::RngIntElt)
// SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, pR::RngInt)
// SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, p::RngIntElt, k::RngIntElt)
// SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, p::RngIntElt)
// HeckeOperator(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt) -> AlgMatElt
// HeckeOperator(M::ModFrmAlg, pR::RngOrdIdl) -> AlgMatElt
// HeckeOperator(M::ModFrmAlg, pR::RngInt, k::RngIntElt) -> AlgMatElt
// HeckeOperator(M::ModFrmAlg, pR::RngInt) -> AlgMatElt
// HeckeOperator(M::ModFrmAlg, p::RngIntElt, k::RngIntElt) -> AlgMatElt
// HeckeOperator(M::ModFrmAlg, p::RngIntElt) -> AlgMatElt
// HeckeOperators(M::ModFrmAlg, k::RngIntElt) -> SeqEnum, SeqEnum
// HeckeOperators(M::ModFrmAlg) -> SeqEnum, SeqEnum
// HeckeImages(M::ModFrmAlg, i::RngIntElt, n::RngIntElt, k::RngIntElt) -> SeqEnum
// HeckeImages(M::ModFrmAlg, i::RngIntElt, ps::SeqEnum, k::RngIntElt) -> SeqEnum
// HeckeOperatorAndGenus(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt) -> AlgMatElt
// HeckeOperatorAndGenus(M::ModFrmAlg, pR::RngOrdIdl) -> AlgMatElt
// HeckeOperatorAndGenus(M::ModFrmAlg, pR::RngInt, k::RngIntElt) -> AlgMatElt
// HeckeOperatorAndGenus(M::ModFrmAlg, p::RngIntElt) -> AlgMatElt
// HeckeOperatorAndGenus(M::ModFrmAlg, p::RngIntElt, k::RngIntElt) -> AlgMatElt

//imports

import "modfrmalg.m" : ModFrmAlgInit;
import "../neighbors/hecke-CN1.m" : HeckeOperatorCN1,
                                    HeckeOperatorCN1Sparse;

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

// We use this function for several intrinsic interfaces below
procedure internalSetHecke(~M, T, pR, k)

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
end procedure;

intrinsic SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, pR::RngOrdIdl,
			   k::RngIntElt)
{ Sets the k-th order Hecke operator at the specified prime for this form. }
  internalSetHecke(~M, T, pR, k);
end intrinsic;

intrinsic SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, pR::RngOrdIdl)
{ Sets the 1-st order Hecke operator at the specified prime for this form. }
  SetHeckeOperator(M, T, pR, 1);
end intrinsic;

intrinsic SetHeckeOperator(
			   M::ModFrmAlg, T::AlgMatElt, pR::RngInt, k::RngIntElt)
{ Sets the k-th order Hecke operator at the specified prime for this form. }
  internalSetHecke(~M, T, pR, k);
end intrinsic;

intrinsic SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, pR::RngInt)
{ Sets the 1-st order Hecke operator at the specified prime for this form. }
  SetHeckeOperator(M, T, pR, 1);
end intrinsic;

intrinsic SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt,
					    p::RngIntElt, k::RngIntElt)
{ Sets the k-th order Hecke operator at the specified prime for this form. }
  SetHeckeOperator(M, T, ideal< Integers() | p >, k);
end intrinsic;

intrinsic SetHeckeOperator(M::ModFrmAlg, T::AlgMatElt, p::RngIntElt)
{ Sets the 1-st order Hecke operator at the specified prime for this form. }
  SetHeckeOperator(M, T, p, 1);
end intrinsic;

// get (computation) methods

// internal function for several of the interfaces below
function internalHecke(M, pR, k, BeCareful, Force, Estimate, UseLLL, Orbits,
		       ComputeGenus, LowMemory, ThetaPrec)
    // at the moment we are still having trouble computing the Hecke operators at inert primes above 2
  if ((not IsOrthogonal(M)) and IsInert(pR)) then
      assert IsOdd(Norm(Norm(pR)));
  end if;
  // Initialize the space of algebraic modular forms, if needed.
  if not ComputeGenus then
    ModFrmAlgInit(M : BeCareful := BeCareful,
		  Orbits := Orbits, LowMemory := LowMemory);
  end if;

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
     error if not isom, "The number field of the prime ideal should be isomorphic to the field of definition of M.\n";

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

  hecke := HeckeOperatorCN1(M, pR, k : BeCareful := BeCareful,
			    UseLLL := use_LLL, Estimate := Estimate,
			    Orbits := Orbits, ComputeGenus := ComputeGenus,
			    LowMemory := LowMemory, ThetaPrec := ThetaPrec);

  // Sets the Hecke operator in the internal data structure for this
  //  algebraic modular form.
  // At the moment we don't save the plus operator
  SetHeckeOperator(M, hecke, pR, k);

  // Returns the computed Hecke operator.
  return hecke;
end function;

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := true,
			  UseLLL := true,
			  Orbits := true,
			  ComputeGenus := false,
			  LowMemory := false,
			  ThetaPrec := 25) -> AlgMatElt
{ Computes the requested Hecke operator. }
  // Verify that the supplied ideal is prime.
  require IsPrime(pR): "Provided ideal must be prime.";
  return internalHecke(M, pR, k, BeCareful, Force, Estimate, UseLLL, Orbits,
		       ComputeGenus, LowMemory, ThetaPrec);
end intrinsic;

intrinsic PerestroikaOperator(M::ModFrmAlg, pR::RngOrdIdl
			      : BeCareful := false,
			      Force := false,
			      Estimate := true,
			      UseLLL := true,
			      Orbits := true,
			      ComputeGenus := false,
			      LowMemory := false,
			      ThetaPrec := 25) -> AlgMatElt
{Computes the Perestroika Hecke operator.}
  // TOOD : Should we check that V splits at p ?
  // Verify that the supplied ideal is prime.
  require IsPrime(pR): "Provided ideal must be prime.";
  require IsOrthogonal(M): "Perestroika operator only exists for orthogonal groups.";
  n := Rank(Module(M));
  require IsEven(n) : "Perestroika operator only exists in even rank.";
  return internalHecke(M, pR, 0, BeCareful, Force, Estimate, UseLLL, Orbits,
		       ComputeGenus, LowMemory, ThetaPrec);
end intrinsic;

intrinsic PlusOperator(M::ModFrmAlg, pR::RngOrdIdl
			      : BeCareful := false,
			      Force := false,
			      Estimate := true,
			      UseLLL := true,
			      Orbits := true,
			      ComputeGenus := false,
			      LowMemory := false,
			      ThetaPrec := 25) -> AlgMatElt
{Computes the Plus Hecke operator.}
  // TOOD : Should we check that V splits at p ?
  // Verify that the supplied ideal is prime.
  require IsPrime(pR): "Provided ideal must be prime.";
  require IsSpecialOrthogonal(M): "Plus operator only exists for special orthogonal groups.";
  n := Rank(Module(M));
  require IsEven(n) : "Plus operator only exists in even rank.";
  return internalHecke(M, pR, -1, BeCareful, Force, Estimate, UseLLL, Orbits,
		       ComputeGenus, LowMemory, ThetaPrec);
end intrinsic;
			      

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngOrdIdl
			: BeCareful := false,
			  Force := false,
			  Estimate := true,
			  UseLLL := true,
			  Orbits := true,
			  LowMemory := false,
			  ComputeGenus := false,
			  ThetaPrec := 25) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1. }
	return HeckeOperator(M, pR, 1
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Orbits := Orbits,
			       LowMemory := LowMemory,
			       ComputeGenus := ComputeGenus,
			       ThetaPrec := ThetaPrec);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngInt, k::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := true,
			  UseLLL := true,
			  Orbits := true,
			  LowMemory := false,
			  ComputeGenus := false,
			  ThetaPrec := 25) -> AlgMatElt
{ Computes the requested Hecke operator, under the assumption that the base
number field is the rationals. }
  // Verify that the supplied ideal is prime.
  require IsPrime(pR): "Provided ideal must be prime.";
  return internalHecke(M, pR, k, BeCareful, Force, Estimate, UseLLL, Orbits,
		       ComputeGenus, LowMemory, ThetaPrec);
end intrinsic;

intrinsic PerestroikaOperator(M::ModFrmAlg, pR::RngInt
			      : BeCareful := false,
			      Force := false,
			      Estimate := true,
			      UseLLL := true,
			      Orbits := true,
			      ComputeGenus := false,
			      LowMemory := false,
			      ThetaPrec := 25) -> AlgMatElt
{Computes the Perestroika Hecke operator, under the assumption that the base
number field is the rationals. }
  // TOOD : Should we check that V splits at p ?
  // Verify that the supplied ideal is prime.
  require IsPrime(pR): "Provided ideal must be prime.";
  require IsOrthogonal(M): "Perestroika operator only exists for orthogonal groups.";
  n := Rank(Module(M));
  require IsEven(n) : "Perestroika operator only exists in even rank.";
  
  return internalHecke(M, pR, 0, BeCareful, Force, Estimate, UseLLL, Orbits,
		       ComputeGenus, LowMemory, ThetaPrec);
end intrinsic;

intrinsic PlusOperator(M::ModFrmAlg, pR::RngInt
			      : BeCareful := false,
			      Force := false,
			      Estimate := true,
			      UseLLL := true,
			      Orbits := true,
			      ComputeGenus := false,
			      LowMemory := false,
			      ThetaPrec := 25) -> AlgMatElt
{Computes the Plus Hecke operator, under the assumption that the base
number field is the rationals. }
  // TOOD : Should we check that V splits at p ?
  // Verify that the supplied ideal is prime.
  require IsPrime(pR): "Provided ideal must be prime.";
  require IsSpecialOrthogonal(M): "Plus operator only exists for special orthogonal groups.";
  n := Rank(Module(M));
  require IsEven(n) : "Plus operator only exists in even rank.";
  
  return internalHecke(M, pR, -1, BeCareful, Force, Estimate, UseLLL, Orbits,
		       ComputeGenus, LowMemory, ThetaPrec);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, pR::RngInt
			: BeCareful := false,
			  Force := false,
			  Estimate := true,
			  UseLLL := true,
			  Orbits := true,
			  LowMemory := false,
			  ComputeGenus := false,
			  ThetaPrec := 25) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1, under the
									  assumption that the base number field is the rationals. }

	return HeckeOperator(M, pR, 1
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Orbits := Orbits,
			       LowMemory := LowMemory,
			       ComputeGenus := ComputeGenus,
			       ThetaPrec := ThetaPrec);
end intrinsic;

intrinsic HeckeOperator(M::ModFrmAlg, p::RngIntElt, k::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := true,
			  UseLLL := false,
			  Orbits := true,
			  LowMemory := false,
			  ComputeGenus := false,
			  ThetaPrec := 25) -> AlgMatElt
{ Computes a Hecke operator at a prime above p. }
        pR := Factorization(ideal< BaseRing(Module(M)) | p >)[1][1];
        return HeckeOperator(M, pR, k
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Orbits := Orbits,
			       LowMemory := LowMemory,
			       ComputeGenus := ComputeGenus,
			       ThetaPrec := ThetaPrec);
end intrinsic;

intrinsic PerestroikaOperator(M::ModFrmAlg, p::RngIntElt
			      : BeCareful := false,
			      Force := false,
			      Estimate := true,
			      UseLLL := true,
			      Orbits := true,
			      ComputeGenus := false,
			      LowMemory := false,
			      ThetaPrec := 25) -> AlgMatElt
{Computes the Perestroika Hecke operator, at a prime above p.}
  pR := Factorization(ideal< BaseRing(Module(M)) | p >)[1][1];
  return PerestroikaOperator(M, pR
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Orbits := Orbits,
			       LowMemory := LowMemory,
			       ComputeGenus := ComputeGenus,
			       ThetaPrec := ThetaPrec);
end intrinsic;

intrinsic PlusOperator(M::ModFrmAlg, p::RngIntElt
			      : BeCareful := false,
			      Force := false,
			      Estimate := true,
			      UseLLL := true,
			      Orbits := true,
			      ComputeGenus := false,
			      LowMemory := false,
			      ThetaPrec := 25) -> AlgMatElt
{Computes the Plus Hecke operator, at a prime above p.}
  pR := Factorization(ideal< BaseRing(Module(M)) | p >)[1][1];
  return PlusOperator(M, pR
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Orbits := Orbits,
			       LowMemory := LowMemory,
			       ComputeGenus := ComputeGenus,
			       ThetaPrec := ThetaPrec);
end intrinsic;


intrinsic HeckeOperator(M::ModFrmAlg, p::RngIntElt
			: BeCareful := false,
			  Force := false,
			  Estimate := true,
			  UseLLL := false,
			  Orbits := true,
			  LowMemory := false,
			  ComputeGenus := false,
			  ThetaPrec := 25) -> AlgMatElt
{ Computes the requested Hecke operator with isotropic dimension 1, under the
assumption that the base number field is the rationals. }
	return HeckeOperator(M, p, 1
			     : BeCareful := BeCareful,
			       Force := Force,
			       Estimate := Estimate,
			       UseLLL := UseLLL,
			       Orbits := Orbits,
			       LowMemory := LowMemory,
			       ComputeGenus := ComputeGenus,
			       ThetaPrec := ThetaPrec);
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

// This will be used for both versions of HeckeImages
function internalHeckeImages(M, i, prec, k, BeCareful,
			     Estimate, Orbits, UseLLL,
			     LowMemory, ThetaPrec)
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
   if Type(prec) eq RngIntElt then
     Precision :=  PrimesUpTo(prec, Rationals());
   else
     Precision := prec; 
   end if;
   R := Integers(BaseRing(M));
   if Type(R) eq RngInt then
     ps := [ideal<R|p> : p in Precision];
   else
     ps := [Factorization(R !! p)[1][1] : p in Precision];
   end if;  
   if SpaceType(AmbientSpace(Module(M))) eq "Hermitian" then
       alpha := Involution(ReflexiveSpace(Module(M)));
       // taking only split primes (do we really need to?). 
       ps := [p : p in ps | alpha(p) ne p];
   end if;
   // generate more images..
   new_ps := [p : p in ps | p notin Keys(M`Hecke`standard_images[i][k])];

   // initialize the invariants
    
   invs := HeckeInitializeInvs(M, ThetaPrec);

   for p in new_ps do
       sp_hec := HeckeOperatorCN1Sparse(M, p, k, s, invs :
					  BeCareful := BeCareful,
					  Estimate := Estimate,
					  Orbits := Orbits,
					  UseLLL := UseLLL,
					  LowMemory := LowMemory,
					  ThetaPrec := ThetaPrec);
       sp_mat := sp_hec[space_idx];
       for j in [start_idx..end_idx] do
	   M`Hecke`standard_images[j][k][p] :=
	       Transpose(sp_mat)[j-start_idx+1];
       end for;
   end for;
   return M`Hecke`standard_images[i][k];  
end function;

intrinsic HeckeImages(M::ModFrmAlg, i::RngIntElt,
				       n::RngIntElt, k::RngIntElt :
		      BeCareful := false,
		      Estimate := true,
		      Orbits := true,
		      UseLLL := false,
		      LowMemory := false,
		      ThetaPrec := 25) -> SeqEnum
{The images of the ith standard basis vector
 under the Hecke operators Tp^k for p good prime, such that Norm(p)<=n
These are computed using sparse methods that don't
require computing the full Hecke operator.}  
  return internalHeckeImages(M, i, n, k, BeCareful,
			     Estimate, Orbits, UseLLL,
			     LowMemory, ThetaPrec);
end intrinsic;


intrinsic HeckeImages(M::ModFrmAlg, i::RngIntElt,
				       ps::SeqEnum, k::RngIntElt :
		      BeCareful := false,
		      Estimate := true,
		      Orbits := true,
		      UseLLL := false,
		      LowMemory := false,
		      ThetaPrec := 25) -> SeqEnum
{The images of the ith standard basis vector
 under the Hecke operators Tp^k for p good prime, such that Norm(p)<=n
These are computed using sparse methods that don't
require computing the full Hecke operator.}  
  return internalHeckeImages(M, i, ps, k, BeCareful,
			     Estimate, Orbits, UseLLL,
			     LowMemory, ThetaPrec);   
end intrinsic;

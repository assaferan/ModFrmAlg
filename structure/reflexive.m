//freeze;
/****-*-magma-******a********************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                             Eran Assaf                                 
                                                                            
   FILE: reflexive.m

   Implementation file for ambient reflexive space

   03/05/2020 : Added orthogonalization of matrix and creation of bilinear form
   03/03/2020 : Started this file as a copy of quadratic spaces
 
 ***************************************************************************/

// imports

import "../fieldaut.m" : getFieldAutomorphism;
import "../unitary/stdbasis.m" : ReflexiveForm, OrthogonalizeForm;

///////////////////////////////////////////////////////////////////
//                                                               //
//    RfxSpace: The reflexive space object.                      //
//                                                               //
///////////////////////////////////////////////////////////////////

// Implementation of ambient reflexive spaces.

declare type RfxSpace;
declare attributes RfxSpace:
	// The base field.
	F,

        // The associated automorphism of the base field
        // (involution for unitary)
        aut,

        // The type of the reflexive space (symplectic, hermitian or symmetric)
        type,
  
	// The base number ring.
	R,

	// The degree of the field extension.
	deg,

	// Class number of the field extension.
	classNo,

	// The inner form.
	innerForm,

	// The reflexive space as a vector space.
	V,

	// The reflexive form as a multinomial.
	Q,

	// The dimension.
	dim,

	// The quaternion algebras associated to this space (ternary only).
	QuaternionAlgebra,

	// Whether the form is definite or not.
	Definite,

	// The diagonalized Gram matrix over the field of fractions.
	Diagonal,

	// The basis for the diagonalized Gram matrix.
	DiagonalBasis,

	// The standard lattice for this reflexive space.
	stdLat;

declare type RfxSpaceAff;
declare attributes RfxSpaceAff:
	// The reflexive space.
	V,

	// The prime ideal.
	pR,

	// A uniformizing element of pR.
	pElt,

	// The finite field.
	F,

	// The characteristic.
	ch,
  
	// The quotient modulo pR^2.
	quot,

	// The projection map modulo pR.
	proj_pR,

        // The involution induced on pR
        inv_pR,

	// The projection map modulo pR^2.
	proj_pR2,

        // The involution induced on pR2
        inv_pR2,

	// Gram matrix modulo pR^2.
	quotGram,

	// The form modulo pR^2.
	Q_pR2;

// printing

intrinsic Print(R::RfxSpace) {}
	K := BaseRing(R`V);
	R`V;
end intrinsic;

// boolean operators

intrinsic 'eq'(R1::RfxSpace, R2::RfxSpace) -> BoolElt
{ Determine whether two quadratic spaces are equal. }
	return R1`V cmpeq R2`V and
		InnerProductMatrix(R1`V) eq InnerProductMatrix(R2`V);
end intrinsic;

// access

intrinsic BaseField(rfxSpace::RfxSpace) -> Fld
{Returns the field over which the space is defined. }
  return rfxSpace`F;
end intrinsic;

intrinsic VectorSpace(rfxSpace::RfxSpace) -> ModTupFld
{Returns the underlying vector space.}
  return rfxSpace`V;
end intrinsic;

intrinsic Dimension(rfxSpace::RfxSpace) -> RngIntElt
{ Returns the dimension of the reflexive space. }
	return rfxSpace`dim;
end intrinsic;

intrinsic BaseRing(rfxSpace::RfxSpace) -> FldOrd
{ Returns the base field of the reflexive space. }
	return rfxSpace`F;
end intrinsic;

intrinsic InnerForm(rfxSpace::RfxSpace) -> AlgMatElt
{ Returns the inner form associated to the reflexive space. }
	return rfxSpace`innerForm;
end intrinsic;

intrinsic Diagonal(rfxSpace::RfxSpace) -> AlgMatElt
{ Returns the coefficients of the diagonalized form. }
	return rfxSpace`Diagonal;
end intrinsic;

intrinsic IsDefinite(rfxSpace::RfxSpace) -> AlgMatElt
{ Returns whether this space is totally positive definite. }
	return rfxSpace`Definite;
end intrinsic;

intrinsic Involution(rfxSpace::RfxSpace) -> FldAut
{.}
  return rfxSpace`aut;
end intrinsic;

intrinsic SpaceType(rfxSpace::RfxSpace) -> MonStgElt
{.}
  if not assigned rfxSpace`type then
    alpha := Involution(rfxSpace);
    M := InnerForm(rfxSpace);
    if (Order(alpha) eq 2) then
      rfxSpace`type := "Hermitian";
    else if IsIdentity(alpha) then
      if Transpose(M) eq M then
         rfxSpace`type := "Symmetric";
      else if Transpose(M) eq -M then
         rfxSpace`type := "Alternating";
      else
         error "%o does not represent a reflexive form.\n", M;
      end if;
      end if;
    else
     error "%o is not an involution!", alpha;
    end if;
    end if;
  end if;
  return rfxSpace`type;
end intrinsic;

// Figure out what to really do here.
intrinsic AmbientReflexiveSpace(innerForm::AlgMatElt) -> RfxSpace
{ Builds the ambient bilinear reflexive space data structure. }
  // The base ring.
  R := BaseRing(innerForm);

  // The field of fractions of the maximal order of our number field.
  F := FieldOfFractions(R);

  alpha := FieldAutomorphism(F, AutomorphismGroup(F)!1);

  return AmbientReflexiveSpace(innerForm, alpha);
end intrinsic;

intrinsic AmbientReflexiveSpace(innerForm::AlgMatElt, alpha::FldAut) -> RfxSpace
{ Builds the ambient reflexive space data structure. }

  // The base ring.
  R := BaseRing(innerForm);

  // Determine field of fractions.
  if IsField(R) then
    if R cmpeq Rationals() then
      R := RationalsAsNumberField();
    end if;

    // Make sure we're dealing with a number field.
    require IsNumberField(R):
      "Base ring must be a number field or number ring.";
    // The maximal order of our number field.
    R := Integers(R);
  elif R cmpeq Integers() then
  // Convert to a maximal order format.
    R := Integers(RationalsAsNumberField());
  end if;

  // The field of fractions of the maximal order of our number field.
  F := FieldOfFractions(R);

	// Initialize a new reflexive space data structre.
	rfxSpace := New(RfxSpace);

//        F := BaseField(alpha);
        alpha := FieldAutomorphism(F, Automorphism(alpha));

	// Coerce the inner form into the appropriate field.
	innerForm := ChangeRing(innerForm, F);

	// Assign base field and base ring.
	rfxSpace`F := F;
        rfxSpace`R := Integers(F);
	rfxSpace`deg := Degree(F);
	rfxSpace`classNo := ClassNumber(F);

        // Assign automorphism
        rfxSpace`aut := alpha;

        require Order(alpha) le 2 :
	  "Automorphism must be either an involution or the identity";

        require (IsIdentity(alpha) and
		 Transpose(innerForm) in [innerForm, -innerForm]) or
        (Order(alpha) eq 2 and Transpose(alpha(innerForm)) eq innerForm ) :
		"Form is not reflexive";

	// Assign the inner form to the reflexive space.
        rfxSpace`innerForm := innerForm;

	// Diagonalize the inner form.
	rfxSpace`Diagonal, rfxSpace`DiagonalBasis :=
	  //		OrthogonalizeGram(innerForm);
	  OrthogonalizeForm(innerForm, alpha);

	// The diagonal entries.
	rfxSpace`Diagonal := Diagonal(rfxSpace`Diagonal);

	// Determine whether this space is totally positive definite.
	rfxSpace`Definite := IsTotallyReal(F) and
		&and[ IsTotallyPositive(d) : d in rfxSpace`Diagonal ];

	// Assign the reflexive space.
        if SpaceType(rfxSpace) eq "Symmetric" then
	  rfxSpace`V := QuadraticSpace(innerForm / 2);
        else if SpaceType(rfxSpace) eq "Alternating" then
          rfxSpace`V := SymplecticSpace(innerForm);
        else if SpaceType(rfxSpace) eq "Hermitian" then
	  rfxSpace`V := UnitarySpace(innerForm, Automorphism(alpha));
        else
	  require false : "Form is not reflexive";
        end if;
        end if;
        end if;

	// Assign the reflexive form.
        rfxSpace`Q := ReflexiveForm(innerForm, alpha);

        if SpaceType(rfxSpace) eq "Symmetric" then
           rfxSpace`Q := QuadraticForm(innerForm) / 2;
        end if;

	// Assign the dimension.
	rfxSpace`dim := Nrows(innerForm);

	// Assign the standard lattice for this reflexive space.
	rfxSpace`stdLat := StandardLattice(rfxSpace);

	return rfxSpace;
end intrinsic;

// freeze;
/****-*-magma-******a********************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                             Eran Assaf                                 
                                                                            
   FILE: hermitian.m (Implementation of hermitian spaces over algebras with involution)

   Implementation file for hermitian spaces over algebras with involution (e.g. quaternions and octonions)

   04/04/2023 : Started this file as a copy of reflexive spaces
 
 ***************************************************************************/

///////////////////////////////////////////////////////////////////
//                                                               //
//    HermSpace: The hermitian space object.                      //
//                                                               //
///////////////////////////////////////////////////////////////////

declare type HermSpace;
declare attributes HermSpace:
	// The base algebra.
	B,

        // The associated automorphism (involution) of the base algebra
        aut,
  
	// The base order
	O,

	// The degree of the field extension.
	deg,

	// Class number of the field extension.
	classNo,

	// The inner form.
	innerForm,

	// The hermitian space as a vector space.
	V,

	// The hermitian form as a multinomial.
	Q,

	// The dimension.
	dim,

	// Whether the form is definite or not.
	Definite,

	// The diagonalized Gram matrix over the field of fractions.
	Diagonal,

	// The basis for the diagonalized Gram matrix.
	DiagonalBasis,

	// The standard lattice for this hermitian space.
	stdLat;

// Note: optimally one would use the same declaration to wrap
// both and have only different functionality in each case.
// However, this is a reincarnation of quadratic spaces which
// were implemented in this way.

///////////////////////////////////////////////////////////////////
//                                                               //
//    HermSpaceAff: The affine reflexive space object.            //
//                                                               //
///////////////////////////////////////////////////////////////////

declare type HermSpaceAff;
declare attributes HermSpaceAff:
	// The hermitian space.
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
	Q_pR2,

	// The splitting type of pR
	// Important for lifting modulo pR^2
	splitting_type;

// printing

intrinsic Print(R::HermSpace, level::MonStgElt)
{}
  printf "hermitian space of dimension %o over %o", Rank(R`V), R`B;
end intrinsic;

// boolean operators

intrinsic 'eq'(R1::HermSpace, R2::HermSpace) -> BoolElt
{ Determine whether two quadratic spaces are equal. }
	return R1`V cmpeq R2`V and
		InnerProductMatrix(R1`V) eq InnerProductMatrix(R2`V);
end intrinsic;

// access

intrinsic BaseAlgebra(hSpace::HermSpace) -> AlgGen
{Returns the algebra over which the space is defined. }
  return hSpace`B;
end intrinsic;

intrinsic VectorSpace(hSpace::HermSpace) -> ModTupFld
{Returns the underlying vector space.}
  return hSpace`V;
end intrinsic;

intrinsic Dimension(hSpace::HermSpace) -> RngIntElt
{ Returns the dimension of the hermitian space. }
  return hSpace`dim;
end intrinsic;

// !! TODO - needs to define an order in general algebras
intrinsic BaseOrder(hSpace::HermSpace) -> AlgGenOrd
{ Returns the base field of the hermitian space. }
  return hSpace`O;
end intrinsic;

intrinsic InnerForm(hSpace::HermSpace) -> AlgMatElt
{ Returns the inner form associated to the hermitian space. }
  return hSpace`innerForm;
end intrinsic;

intrinsic Diagonal(hSpace::HermSpace) -> AlgMatElt
{ Returns the coefficients of the diagonalized form. }
  return hSpace`Diagonal;
end intrinsic;

// !! TODO - needs to define a matrix over a general algebra
// In the Octonion case, we only really use 1x1 matrices.
intrinsic IsDefinite(hSpace::HermSpace) -> AlgMatElt
{ Returns whether this space is totally positive definite. }
  return hSpace`Definite;
end intrinsic;

intrinsic Involution(hSpace::HermSpace) -> FldAut
{.}
  return hSpace`aut;
end intrinsic;

// Figure out what to really do here.
intrinsic AmbientHermitianSpace(innerForm::AlgMatElt) -> HermSpace
{ Builds the ambient hermitian space data structure. }
  // The base order.
  O := BaseRing(innerForm);

  // The algebra of the order
  if Type(O) eq RngOrd then
      B := FieldOfFractions(O);
  else
      B := Algebra(O);
  end if;

  // This doesn't work for finite fields or algebras
  //  alpha := FieldAutomorphism(F, AutomorphismGroup(F)!1);
  alpha := IdentityAutomorphism(B);

  return AmbientHermitianSpace(innerForm, alpha);
end intrinsic;

intrinsic AmbientHermitianSpace(innerForm::AlgMatElt, alpha::AlgAut) -> HermSpace
{ Builds the ambient hermitian space data structure. }

  // The base ring.
  R := BaseRing(innerForm);

  // if we're in the case of a split etale algebra (GL_n(D))

  if Type(R) eq AlgAss then
      alpha := AlgebraAutomorphism(R, Automorphism(alpha));
      B := BaseRing(R);
      require IsField(B) and Dimension(R) eq 2 :
		"Base ring must be an etale quadratic extension of a field"; 
      
  else

      // Determine field of fractions.
      if ISA(Type(R), Fld) then

	  // Make sure we're dealing with a number field.
	  if  IsNumberField(R) or (Type(R) eq FldOrd) or Type(R) eq FldRat then
	      // The maximal order of our number field.
	      R := Integers(R);
	  end if;

      end if;

      // The algebra of the order
      if Type(R) eq RngOrd then
	  B := FieldOfFractions(R);
      else
	  B := Algebra(R);
      end if;
      
      alpha := AlgebraAutomorphism(B, Automorphism(alpha));

      // Coerce the inner form into the appropriate field.
      innerForm := ChangeRing(innerForm, B);
  end if;

  // Initialize a new reflexive space data structre.
  hSpace := New(HermSpace);

  // Assign base field and base ring.
  hSpace`B := B;
  if Type(B) in [FldNum, FldOrd, FldCyc, FldQuad, FldRat] then
      hSpace`R := Integers(B);
      hSpace`classNo := ClassNumber(AbsoluteField(B));
  end if;
  
  hSpace`deg := Degree(B);

  // Assign automorphism
  hSpace`aut := alpha;
  
  require Order(alpha) le 2 :
	"Automorphism must be either an involution or the identity";

  require (IsIdentity(alpha) and
	   Transpose(innerForm) in [innerForm, -innerForm]) or
          (Order(alpha) eq 2 and Transpose(alpha(innerForm)) eq innerForm ) :
	"Form is not reflexive";

  // Assign the inner form to the reflexive space.
  hSpace`innerForm := innerForm;

  // Diagonalize the inner form.
  hSpace`Diagonal, hSpace`DiagonalBasis := OrthogonalizeForm(innerForm, alpha);

  // The diagonal entries.
  hSpace`Diagonal := Diagonal(hSpace`Diagonal);

  F0 := FixedField(alpha);

  if Type(B) in [FldNum, FldOrd, FldCyc, FldQuad, FldRat] then
      // Determine whether this space is totally positive definite.
      hSpace`Definite := IsTotallyReal(F0) and
			   &and[ IsTotallyPositive(F0!d) :
				 d in hSpace`Diagonal ];
  end if;

  // Assign the underlying vector space.
  hSpace`V := RSpace(B, Nrows(innerForm));
  
  // Assign the reflexive form.
  hSpace`Q := HermitianForm(innerForm, alpha);

  // Assign the dimension.
  hSpace`dim := Nrows(innerForm);

  // Assign the standard lattice for this reflexive space.
  if Type(B) in [FldNum, FldOrd, FldCyc, FldQuad, FldRat] then
      hSpace`stdLat := StandardLattice(hSpace);
  end if;
  
  return hSpace;
end intrinsic;

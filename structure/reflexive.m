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

intrinsic Type(rfxSpace::RfxSpace) -> MonStgElt
{.}
  if not assigned rfxSpace`type then
    alpha := Involution(rfxSpace);
    M := InnerForm(rfxSpace);
    if (Order(alpha) eq 2) then
      rfxSpace`type := "Hermitian";
    else if IsIdentity(alpha) then
      if Transpose(M) eq M then
         rfxSpace`type := "symmetric";
      else if Transpose(M) eq -M then
         rfxSpace`type := "alternating";
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
intrinsic AmbientReflexiveSpace(innerForm::AlgMatElt :
				Hermitian := false) -> RfxSpace
{ Builds the ambient bilinear reflexive space data structure. }
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
  // Covnert to a maximal order format.
    R := Integers(RationalsAsNumberField());
  end if;

  // The field of fractions of the maximal order of our number field.
  F := FieldOfFractions(R);

  if Hermitian then
    inv_exists, a := HasComplexConjugate(R`ArithmeticField);
    require inv_exists :
      "Base field of form does not admit complex conjugation!";
    alpha := getFieldAutomorphism(F,a);
  else
    alpha := FieldAutomorphism(F, AutomorphismGroup(F)!1);
  end if;

  return AmbientReflexiveSpace(innerForm, alpha);
end intrinsic;

function OrthogonalizeForm(M, alpha)

  MS := Parent(M);
  n := Degree(MS);
  one := MS!1;
  T := one;

  for i in [1..n] do
    if M[i,i] eq 0 then
      for j in [i+1..n] do
        if M[i,j] ne 0 then
          tmp := one;
          if M[i,j] + M [j,j] eq 0 then
	    tmp[j,i] := -1;
          else
	    tmp[j,i] := 1;
          end if;
          T := T * tmp;
          M := tmp * M * alpha(Transpose(tmp));
          break;
	end if;
      end for;
    end if;

    tmp := one;
    for j in [i+1..n] do
      if M[i,j] ne 0 then
        tmp[i,j] := -M[i,j] / M[i,i];
      end if;
    end for;
    M := tmp * M * alpha(Transpose(tmp));
    T := T * tmp;
  end for;
  return M,T;
end function;

function getForm(M, alpha)
  MS := Parent(M);
  n := Degree(MS);
  R := PolynomialRing(BaseRing(M), 2*n);
  x_names := ["x" cat IntegerToString(i) : i in [1..n]];
  y_names := ["y" cat IntegerToString(i) : i in [1..n]];
  if Order(alpha) ne 1 then
    y_names := [var cat "bar" : var in y_names];
  end if;
  names := x_names cat y_names;
  AssignNames(~R, names);
  x := Vector([R.i : i in [1..n]]);
  y := Vector([R.(n+i) : i in [1..n]]);
  
  return (x*ChangeRing(M,R), y);
end function;

intrinsic AmbientReflexiveSpace(innerForm::AlgMatElt, alpha::FldAut) -> RfxSpace
{ Builds the ambient reflexive space data structure. }
	// Initialize a new reflexive space data structre.
	rfxSpace := New(RfxSpace);

        F := BaseField(alpha);

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
        if Type(rfxSpace) eq "Symmetric" then
	  rfxSpace`V := QuadraticSpace(innerForm);
        else if Type(rfxSpace) eq "Alternating" then
          rfxSpace`V := SymplecticSpace(innerForm);
        else if Type(rfxSpace) eq "Hermitian" then
	  rfxSpace`V := UnitarySpace(innerForm, Automorphism(alpha));
        end if;
        end if;
        end if;

	// Assign the reflexive form.
        rfxSpace`Q := getForm(innerForm, alpha);

	// Assign the dimension.
	rfxSpace`dim := Nrows(innerForm);

	// Assign the standard lattice for this reflexive space.
	rfxSpace`stdLat := StandardLattice(rfxSpace);

	return rfxSpace;
end intrinsic;


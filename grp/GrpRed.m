freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         

                                                                            
   FILE: GrpRed.m (Reductive Group object)

   I've grown weary of trying to use GrpLie...

   05/04/20: Added support in non-semisimple lie groups

   04/27/20: Fixed bug in constructor of orthogonal group from dimension.
             Added constructors for the special orthogonal group.

   04/23/20: File created.
 
 ***************************************************************************/

// Here we list the intrinsics that this file defines
// ReductiveGroup(G0::GrpLie, Comp::Grp) -> GrpRed
// ReductiveGroup(group_data::List) -> GrpRed
// SymplecticGroup(symp::RfxSpace) -> GrpRed
// SymplecticGroup(innerForm::AlgMatElt) -> GrpRed
// SymplecticGroup(n::RngIntElt, F::Fld) -> GrpRed
// OrthogonalGroup(quad::RfxSpace) -> GrpRed
// OrthogonalGroup(innerForm::AlgMatElt) -> GrpRed
// OrthogonalGroup(n::RngIntElt, F::Fld) -> GrpRed
// SpecialOrthogonalGroup(quad::RfxSpace) -> GrpRed
// SpecialOrthogonalGroup(innerForm::AlgMatElt) -> GrpRed
// SpecialOrthogonalGroup(n::RngIntElt, F::Fld) -> GrpRed
// UnitaryGroup(hermit::RfxSpace) -> GrpRed
// UnitaryGroup(innerForm::AlgMatElt) -> GrpRed
// UnitaryGroup(n::RngIntElt, F::Fld) -> GrpRed
// ConnectedComponent(G::GrpRed) -> GrpRed
// ComponentGroup(G::GrpRed) -> GrpRed
// SplittingField(G::GrpRed) -> Fld
// DefinitionField(G::GrpRed) -> Fld
// CartanName(G::GrpRed) -> MonStgElt
// InnerForm(G::GrpRed, i::RngIntElt) -> RfxSpace
// InnerForms(G::GrpRed) -> SeqEnum
// Dimension(G::GrpRed) -> RngIntElt
// Rank(G::GrpRed) -> RngIntElt
// IsConnected(G::GrpRed) -> BoolElt
// IsOrthogonal(G::GrpRed) -> BoolElt
// IsSymplectic(G::GrpRed) -> BoolElt
// IsUnitary(G::GrpRed) -> BoolElt
// IsSpecialOrthogonal(G::GrpRed) -> BoolElt
// IsCompact(G::GrpRed) -> BoolElt
// Print(G::GrpRed, level::MonStgElt)
// Parent(g::GrpRedElt) -> GrpRed
// IsCoercible(G::GrpRed, g::.) -> Bool, GrpRedElt
// Print(g::GrpRedElt, level::MonStgElt)
// '*'(g1::GrpRedElt, g2::GrpRedElt) -> GrpRedElt
// '^'(g::GrpRedElt, n::RngIntElt) -> GrpRedElt
// GeneralLinearAlgberaicGroup(n::RngIntElt, k::Fld) -> GrpRed
// LinearAlgebraicGroup(I::SeqEnum[RngMPolElt]) -> GrpRed
// CoordinateRing(G::GrpRed) -> RngMPolRes
// SpecialLinearAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
// MultiplicativeAlgebraicGroup(k::Fld) -> GrpRed
// AdditiveAlgebraicGroup(k::Fld) -> GrpRed
// BilinearAlgebraicGroup(S::AlgMatElt[Fld]) -> GrpRed
// SymplecticAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
// OrthogonalAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
// SpecialOrthogonalAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
// SplitOrthogonalAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
// SplitSpecialOrthogonalAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
// DiagonalMatricesAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
// UpperTriangularMatricesAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
// UpperTriangularUnipotentMatricesAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
// Eltseq(g::GrpRedElt) -> SeqEnum
// IdentityComponent(G::GrpRed) -> GrpRed
// 'eq'(G1::GrpRed, G2::GrpRed) -> BoolElt
// Centralizer(G::GrpRed, S::SeqEnum[GrpRedElt]) -> GrpRed
// Centralizer(G::GrpRed, g::GrpRedElt) -> GrpRed
// Normalizer(G::GrpRed, S::SeqEnum[GrpRedElt]) -> GrpRed
// IsCommutative(G::GrpRed) -> BoolElt
// IsAbelian(G::GrpRed) -> BoolElt
// LieAlgebra(G::GrpRed) -> AlgMatLie
// IsSemisimple(G::GrpRed) -> BoolElt
// IsDiagonalizable(G::GrpRed) -> BoolElt
// IsTorus(G::GrpRed) -> BoolElt
// IsSolvable(G::GrpRed) -> BoolElt
// ChangeRing(G::GrpRed, R::Rng) -> GrpRed

// imports

// !! TODO - fix this terrible patch

import "/Applications/Magma/package/LieThry/Root/RootDtm.m" : rootDatum;


///////////////////////////////////////////////////////////////////
//                                                               //
//    RedGrp: The reductive group object.                        //
//                                                               //
//    At the moment we assume the connected component is         //
//    reductive, that the extensions is split and furthermore,   //
//    that the semidirect product is actually direct.            //
//                                                               //
///////////////////////////////////////////////////////////////////

declare type GrpRed[GrpRedElt];
declare attributes GrpRed:
	// the connected component - GrpLie
	G0,
	// the component group - a finite group
	Comp,
	// The inner forms for the different components
	// We use that becasue TwistedGroupOfLieType doesn't work very well
	// In general, inner forms could be presented as reflexive spaces
        InnerForms,
        // assuming it is a subgroup of GL(n,k)
        k,
        n,
        // generators of the vanishing ideal
        I,
        // in case this group has a special name
        name; 

declare attributes GrpRedElt:
        // the reductive group containing it
        parent,
        // the matrix representing the element.
        elt;


// !!! TODO : Add Weil restrictiond (G could be a product of Weil restrictions)

forward SplitReflexiveSpace;

// constructors
intrinsic ReductiveGroup(G0::GrpLie, Comp::Grp : InnerForms := []) -> GrpRed
{Construct the algebraic group whose connected component is G0,
 with component group Comp, such that G = G0 x Comp.
InnerForms is a list of inner forms, listing for each non-toroidal factor
the inner form over the base field.}

  G := New(GrpRed);

  G`G0 := G0;
  G`Comp := Comp;

  // Create corresponding reflexive spaces for the split case
  if IsEmpty(InnerForms) then
      ds := DirectSumDecomposition(AdjointVersion(RootDatum(G`G0)));
      cartans := [CartanName(r) : r in ds];
      types := [<c[1], StringToInteger(c[2..#c])> : c in cartans];
      InnerForms := [SplitReflexiveSpace(t[1], t[2], DefRing(G0)) : t in types];
  end if;
  G`InnerForms := InnerForms;

  return G;
  
end intrinsic;

// constructor from io output

forward extract_root_datum;

intrinsic ReductiveGroup(group_data::List) -> GrpRed
{.}
  // An associative array which stores the appropriate meta data.
  group_array := AssociativeArray();

  //  Store meta data.
  for entry in group_data do group_array[entry[1]] := entry[2]; end for;	

  root_datum := extract_root_datum(group_array["ROOT_DATUM"]);
  base_field := group_array["BASE_FIELD"];
  G0 := GroupOfLieType(root_datum, base_field);

  comp := group_array["COMP_GROUP"];
  innerForms := group_array["INNER_FORMS"];

  return ReductiveGroup(G0, comp : InnerForms := innerForms);

end intrinsic;

// constructors for special groups

// symplectic

function build_symplectic(symp)
  F := BaseRing(symp);
  n := Dimension(symp);
  Sp_n := GroupOfLieType(StandardRootDatum("C", n div 2), F);
  comp := CyclicGroup(1); 
  return ReductiveGroup(Sp_n, comp : InnerForms := [symp]);
end function;

intrinsic SymplecticGroup(symp::RfxSpace) -> GrpRed
{Construct the symplectic group associated to the symplectic space.}
  return build_symplectic(symp);
end intrinsic;

intrinsic SymplecticGroup(innerForm::AlgMatElt[Fld]) -> GrpRed
{Construct the symplectic group associated to the specified alternating form.}
  return SymplecticGroup(AmbientReflexiveSpace(innerForm));
end intrinsic;

intrinsic SymplecticGroup(n::RngIntElt, F::Fld) -> GrpRed
{Construct the symplectic group of dimension n over F.}
  require IsEven(n) : "n must be even.";
  return SymplecticGroup(SplitReflexiveSpace("C", n div 2, F));
end intrinsic;

// orthogonal

function build_orthogonal(quad, special)
  F := BaseRing(quad);
  n := Dimension(quad);
  cartan_type := (n mod 2 eq 1) select "B" else "D";
  SO_n := GroupOfLieType(StandardRootDatum(cartan_type, n div 2), F);
  comp := CyclicGroup(special select 1 else 2); 
  return ReductiveGroup(SO_n, comp : InnerForms := [quad]);
end function;

intrinsic OrthogonalGroup(quad::RfxSpace) -> GrpRed
{Construct the orthogonal group associated to the quadratic space.}
  return build_orthogonal(quad, false);
end intrinsic;

intrinsic OrthogonalGroup(innerForm::AlgMatElt[Fld]) -> GrpRed
{Construct the orthogonal group preserving the specified symmetric form.}
  return OrthogonalGroup(AmbientReflexiveSpace(innerForm));
end intrinsic;

intrinsic OrthogonalGroup(innerForm::AlgMatElt[Rng]) -> GrpRed
{Construct the orthogonal group preserving the specified symmetric form.}
  return OrthogonalGroup(ChangeRing(innerForm,
				    FieldOfFractions(BaseRing(innerForm))));
end intrinsic;

intrinsic OrthogonalGroup(n::RngIntElt, F::Fld) -> GrpRed
{Construct the split orthogonal group of dimension n over F}
  cartan_type := (n mod 2 eq 1) select "B" else "D";	  
  return OrthogonalGroup(SplitReflexiveSpace(cartan_type, n div 2, F));
end intrinsic;

intrinsic SpecialOrthogonalGroup(quad::RfxSpace) -> GrpRed
{Construct the special orthogonal group associated to the quadratic space.}
  return build_orthogonal(quad, true);
end intrinsic;

intrinsic SpecialOrthogonalGroup(innerForm::AlgMatElt[Fld]) -> GrpRed
{Construct the special orthogonal group preserving the specified symmetric form.}
  return SpecialOrthogonalGroup(AmbientReflexiveSpace(innerForm));
end intrinsic;

intrinsic SpecialOrthogonalGroup(n::RngIntElt, F::Fld) -> GrpRed
{Construct the split special orthogonal group of dimension n over F}
  cartan_type := (n mod 2 eq 1) select "B" else "D";	  
  return SpecialOrthogonalGroup(SplitReflexiveSpace(cartan_type, n div 2, F));
end intrinsic;

// unitary

intrinsic UnitaryGroup(hermit::RfxSpace) -> GrpRed
{Construct the Unitary group associated to the hermitian space.}
  F := FixedField(Involution(hermit));
  n := Dimension(hermit);
  GL_n := GroupOfLieType(StandardRootDatum("A", n-1), F);
  return ReductiveGroup(GL_n, CyclicGroup(1) : InnerForms := [hermit]);
end intrinsic;

intrinsic UnitaryGroup(innerForm::AlgMatElt[Fld]) -> GrpRed
{Construct the unitary group preserving the specified hermitian form.}
  K := BaseRing(innerForm);
  require Type(K) ne FldRat : "The form should be over a CM field.";
  _, cc := HasComplexConjugate(K);
  alpha := FieldAutomorphism(K, cc);
  
  return UnitaryGroup(AmbientReflexiveSpace(innerForm, alpha));
end intrinsic;

intrinsic UnitaryGroup(n::RngIntElt, F::Fld) -> GrpRed
{Construct the unitary group with respect to the standard hermitian form.}
  return UnitaryGroup(IdentityMatrix(F,n));
end intrinsic;

// access

intrinsic ConnectedComponent(G::GrpRed) -> GrpRed
{Return the connected component of the algebraic group.}
  return ReductiveGroup(G`G0, TrivialSubgroup(G`Comp));
end intrinsic;

intrinsic ComponentGroup(G::GrpRed) -> GrpRed
{Return the component group.}
  return ReductiveGroup(GroupOfLieType(TrivialRootDatum(), DefRing(G`G0)),
			G`Comp); 
end intrinsic;

intrinsic SplittingField(G::GrpRed) -> Fld
{Return the field over which G splits.}
  if IsEmpty(G`InnerForms) then
      return BaseRing(G`G0);
  else
      F := BaseRing(G`InnerForms[1]);
      for idx in [2..#G`InnerForms] do
	  F := Compositum(F, BaseRing(G`InnerForms[idx]));
      end for;
      return F;
  end if;
end intrinsic;

intrinsic DefinitionField(G::GrpRed) -> Fld
{Return the field of definition of G.}
  return DefRing(G`G0);
end intrinsic;

intrinsic CartanName(G::GrpRed) -> MonStgElt
{Return a string concatenating the Cartan types of all simple factors and tori
of the connected component of G.}	
  return CartanName(G`G0);
end intrinsic;

intrinsic InnerForm(G::GrpRed, i::RngIntElt) -> RfxSpace
{Returns the inner form corresponding to the i-th simple factor.}
  return G`InnerForms[i];
end intrinsic;

intrinsic InnerForms(G::GrpRed) -> SeqEnum
{Returns the inner forms defining the simple factors of G.}
  return G`InnerForms;
end intrinsic;

intrinsic Dimension(G::GrpRed) -> RngIntElt
{Returns n such that G embeds into GL_n through the representation by the
		   forms given.}
  return &+[Dimension(V) : V in G`InnerForms];
end intrinsic;

intrinsic Rank(G::GrpRed) -> RngIntElt
{}
  return Dimension(LieAlgebra(G));
end intrinsic;

// booleans

intrinsic IsConnected(G::GrpRed) -> BoolElt
{.}
  if not assigned G`Comp then
    A := AffineSpace(Universe(G`I));
    return IsIrreducible(Scheme(A, G`I));
  end if;
  return IsTrivial(G`Comp);
end intrinsic;

intrinsic IsOrthogonal(G::GrpRed) -> BoolElt
{.}
  R := RootDatum(G`G0);
 
  name := CartanName(R);
  cartan_type := name[1];

  return (cartan_type in ["B","D"]);
end intrinsic;

intrinsic IsSymplectic(G::GrpRed) -> BoolElt
{.}
  R := RootDatum(G`G0);
 
  name := CartanName(R);
  cartan_type := name[1];

  return (cartan_type eq "C");
end intrinsic;

intrinsic IsUnitary(G::GrpRed) -> BoolElt
{.}
  R := RootDatum(G`G0);
  
  name := CartanName(R);
  cartan_type := name[1];

  return (cartan_type eq "A");
end intrinsic;

intrinsic IsSpecialOrthogonal(G::GrpRed) -> BoolElt
{.}
  return IsOrthogonal(G) and IsConnected(G) and IsAdjoint(G`G0);
end intrinsic;

intrinsic IsCompact(G::GrpRed) -> BoolElt
{Checks whether G is a compact form. Only relevant for
groups defined over number fields}

  require Type(DefRing(G`G0)) in
	[FldRat, FldCyc, FldQuad, FldNum, FldOrd] :
	"Group must be defined over a number field";

  return IsTotallyReal(DefRing(G`G0)) and
       &and[IsDefinite(V) : V in G`InnerForms];
end intrinsic;

// print

forward build_root_data;

intrinsic Print(G::GrpRed, level::MonStgElt)
{Print the reductive group G.}
  if level eq "Magma" then
      group_data := [* *];
      Append(~group_data, < "ROOT_DATUM", build_root_data(RootDatum(G`G0)) >);
      Append(~group_data, < "BASE_FIELD", DefinitionField(G) >);
      Append(~group_data, < "COMP_GROUP", G`Comp >);
      Append(~group_data, < "INNER_FORMS", InnerForms(G) >);
      printf "ReductiveGroup(%m)", group_data;
  elif assigned G`name then
      printf "%o", G`name;
  else	
      if IsSpecialOrthogonal(G) then
         printf "special orthogonal group of %o", InnerForm(G,1);
      elif IsOrthogonal(G) then
	printf "orthogonal group of %o", InnerForm(G,1);
      elif IsUnitary(G) then
	printf "unitary group of %o", InnerForm(G,1);
      else
        printf "reductive group with connected component %o", G`G0;
        if level ne "Minimal" then
	  printf ", and component group %o", G`Comp;
        end if;
      end if;
      if level eq "Maximal" then
	  printf ", with inner forms %o", InnerForms(G);
      end if;
  end if;
end intrinsic;

// helper functions  

function SplitReflexiveSpace(t, n, F)
    case t:
    when "A":
	L := DirectSum(Algebra(F,F), Algebra(F,F));
	alpha := FieldAutomorphism(L);
	return AmbientReflexiveSpace(IdentityMatrix(L,n+1), alpha);
    when "B":
	I_n := IdentityMatrix(F,n);
	I_1 := IdentityMatrix(F,1);
	M := DirectSum(I_1, BlockMatrix([[0,I_n],[I_n,0]]));
	return AmbientReflexiveSpace(M);
    when "C":
        I_n := IdentityMatrix(F, n);
	M := BlockMatrix([[0,I_n],[-I_n,0]]);
	return AmbientReflexiveSpace(M);
    when "D":
        I_n := IdentityMatrix(F, n);
	M := BlockMatrix([[0,I_n],[I_n,0]]);
	return AmbientReflexiveSpace(M);
    else
	// !!! TODO : add these by using non-associative algebras
	error "At the moment we do not support Cartan types E,F,G!";
    end case;
end function;

function build_root_data(root_datum)
    root_data := [*
		  < "SIMPLE_ROOTS", root_datum`SimpleRoots >,
		  < "SIMPLE_COROOTS", root_datum`SimpleCoroots >,
		  < "SIGNS", root_datum`ExtraspecialSigns >,
		  < "TYPE", Sprintf("%o", root_datum`Type) >
		  *];

    return root_data;
end function;

function extract_root_datum(root_data)
    root_array := AssociativeArray();

    // Store meta data.
    for entry in root_data do root_array[entry[1]] := entry[2]; end for;

    A := root_array["SIMPLE_ROOTS"];
    B := root_array["SIMPLE_COROOTS"];
    Signs := root_array["SIGNS"];
    type := eval root_array["TYPE"];

    rank := Nrows(A);  dim := Ncols(A);
    F := CoveringStructure(BaseRing(A), Rationals());
    F := CoveringStructure(BaseRing(B), F);
    A := Matrix(F,A);
    B := Matrix(F,B);
    C := Matrix( A*Transpose(B) );
    is_c,newC := IsCoercible( MatrixAlgebra(Integers(),rank), C);
    if is_c then C := newC; end if;

    R := rootDatum( A, B, C, type, Signs);

    return R;
end function;

function build_elt(G,g)
  g_G := New(GrpRedElt);
  g_G`elt := g;
  g_G`parent := G;
  return g_G;
end function;

intrinsic Parent(g::GrpRedElt) -> GrpRed
{}
  return g`parent;
end intrinsic;

// Coercion
intrinsic IsCoercible(G::GrpRed, g::.) -> Bool, GrpRedElt
{.}
  // Here we should check that g satisfies the requirements to be in the
  //   group
  // Currently asserts only a single component in the product
  if not assigned G`InnerForms then
    n := G`n;
    k := G`k;
  else
    V := InnerForm(G,1);
    n := Dimension(V);
    k := BaseRing(V);
  end if;
  is_coer, g_Q := IsCoercible(GL(n,k), g);
  if not is_coer then
    return false, "cannot coerce element to an invertible matrix";
  end if;
  if not assigned G`InnerForms then
    for f in G`I do
       if not IsZero(Evaluate(f, Eltseq(g_Q) cat [Determinant(g_Q)^(-1)])) then
         return false, "element does not lie in group";
       end if;
    end for;
    return true, build_elt(G, g_Q);
  end if;
  Q := InnerForm(V);
  alpha := Involution(V);
/*
  is_coer, g_Q := IsCoercible(ChangeRing(Parent(g), BaseRing(Q)), g_Q);
  if not is_coer then
    return false, _;
  end if;
*/
  if IsSpecialOrthogonal(G) and not IsOne(Determinant(g_Q)) then
    return false, "element does not lie in group";
  end if;
  if Transpose(alpha(g_Q))*Q*g_Q eq Q then
    return true, build_elt(G, g_Q);
  else
    return false, "element does not lie in group";
  end if;
end intrinsic;

intrinsic 'eq'(G1::GrpRed, G2::GrpRed) -> BoolElt
{}
  return (G1`k eq G2`k) and (G1`n eq G2`n) and (G1`I eq G2`I);
end intrinsic;

intrinsic ChangeRing(G::GrpRed, R::Rng) -> GrpRed
{.}
  return ReductiveGroup(ChangeRing(G`G0, R), G`Comp :
			InnerForms := [ChangeRing(Q, R) : Q in InnerForms(G)]);
end intrinsic;

intrinsic Print(g::GrpRedElt, level::MonStgElt)
{}
  printf "%o", g`elt;
end intrinsic;

intrinsic '*'(g1::GrpRedElt, g2::GrpRedElt) -> GrpRedElt
{}
  require Parent(g1) eq Parent(g2) : "elements do not belong to the same group";
  G := Parent(g1);
  return build_elt(G, g1`elt*g2`elt);
end intrinsic;

intrinsic '^'(g::GrpRedElt, n::RngIntElt) -> GrpRedElt
{}
  return build_elt(Parent(g), g`elt^n);
end intrinsic;

intrinsic Eltseq(g::GrpRedElt) -> SeqEnum
{.}
  return Eltseq(g`elt);
end intrinsic;

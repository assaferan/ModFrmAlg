freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: GrpRed.m (Reductive Group object)

   I've grown weary of trying to use GrpLie...

   04/23/20: File created.
 
 ***************************************************************************/

// imports

// !!! TODO : change to go to magma's location
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

declare type GrpRed;
declare attributes GrpRed:
	// the connected component - GrpLie
	G0,
	// the component group - a finite group
	Comp,
	// The inner forms for the different components
	// We use that becasue TwistedGroupOfLieType doesn't work very well
	// In general, inner forms could be presented as reflexive spaces
	InnerForms;


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
      ds := DirectSumDecomposition(RootDatum(G`G0));
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

// orthogonal

intrinsic OrthogonalGroup(quad::RfxSpace) -> GrpRed
{Construct the orthogonal group associated to the quadratic space.}
  F := BaseRing(quad);
  n := Dimension(quad);
  cartan_type := (n mod 2 eq 1) select "B" else "D";
  SO_n := GroupOfLieType(StandardRootDatum(cartan_type, n div 2), F);
  return ReductiveGroup(SO_n, CyclicGroup(2) : InnerForms := [quad]);
end intrinsic;

intrinsic OrthogonalGroup(innerForm::AlgMatElt[Fld]) -> GrpRed
{Construct the orthogonal group preserving the specified symmetric form.}
  return OrthogonalGroup(AmbientReflexiveSpace(innerForm));
end intrinsic;

intrinsic OrthogonalGroup(n::RngIntElt, F::Fld) -> GrpRed
{Construct the split orthogonal group of dimension n over F}
  cartan_type := (n mod 2 eq 1) select "B" else "D";	  
  return OrthogonalGroup(SplitReflexiveSpace(cartan_type, n, F));
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
// booleans

intrinsic IsConnected(G::GrpRed) -> BoolElt
{.}
  return IsTrivial(G`Comp);
end intrinsic;

intrinsic IsOrthogonal(G::GrpRed) -> BoolElt
{.}
  R := RootDatum(G`G0);
  if not IsIrreducible(R) then return false; end if;
  name := CartanName(R);
  cartan_type := name[1];

  return (cartan_type in ["B","D"]);
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
  // !!! TODO : add magma level printing to ease on save-load.
  if level eq "Magma" then
      group_data := [* *];
      Append(~group_data, < "ROOT_DATUM", build_root_data(RootDatum(G`G0)) >);
      Append(~group_data, < "BASE_FIELD", DefinitionField(G) >);
      Append(~group_data, < "COMP_GROUP", G`Comp >);
      Append(~group_data, < "INNER_FORMS", InnerForms(G) >);
      printf "ReductiveGroup(%m)", group_data;
  else
      printf "Reductive group with connected component %o", G`G0;
      if level ne "Minimal" then
	  printf ", and component group %o", G`Comp;
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
	I_n := IdentityMatrix(F);
	M := BlockMatrix([[0,I_n],[-I_n,0]]);
	return AmbientReflexiveSpace(M);
    when "D":
	I_n := IdentityMatrix(F);
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

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

// imports

// !!! TODO : Fix this terrible patch

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
  if not assigned G`InnerForms and IsTorus(G) then
    return Dimension(LieAlgebra(G));
  end if;
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

intrinsic GeneralLinearAlgberaicGroup(n::RngIntElt, k::Fld) -> GrpRed
{Constructs GL(n) over k as an algebraic group}
  require n gt 0 : "n must be positive.";
  ret := New(GrpRed);
  ret`k := k;
  ret`n := n;
  R := PolynomialRing(k, n^2+1);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  AssignNames(~R, &cat var_names cat ["det_inv"]);
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  det := Determinant(x);
  det_inv := R.(n^2+1);
  I := ideal<R | det*det_inv-1>;
  ret`I := [det*det_inv-1];
  ret`name := "general linear group";
  if n eq 1 then
    ret`name := Sprintf("multiplicative group over %o", k);
  else
    ret`name := Sprintf("GL(%o,%o)", n, k);
  end if;
  return ret;
end intrinsic;

intrinsic LinearAlgebraicGroup(I::SeqEnum[RngMPolElt]) -> GrpRed
{Constructs the linear algebraic group defined as a closed subgroup of GL(n) via the ideal I.}
  require not IsEmpty(I) : "I need to be a nonepmty sequence of polynomials";
  ret := New(GrpRed);
  R := Universe(I);
  N := Rank(R);
  is_sqr, n := IsSquare(N);
  if is_sqr then
    S := PolynomialRing(BaseRing(R), n^2+1);
    h := hom<R->S | [S.i : i in [1..N]]>; 
    I := [h(f) : f in I];
    R := S;
  end if;
  if not is_sqr then
    is_sqr, n := IsSquare(N-1);
  end if;
  require is_sqr : "polynomials should have either n^2 variables for the matrix enries or n^2+1, where the last is det^(-1)";
  ret`n := n;
  ret`k := BaseRing(R);
  ret`I := I;
  return ret;
end intrinsic;

intrinsic CoordinateRing(G::GrpRed) -> RngMPolRes
{The corresponding polynomial ring.}
  R := Universe(G`I);
  return quo<R | G`I>;
end intrinsic;

intrinsic SpecialLinearAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
{Constructs SL(n) over k as an algebraic group.}
  ret := GeneralLinearAlgberaicGroup(n,k);
  R := Universe(ret`I);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  det := Determinant(x);
  ret`I cat:= [det - 1];
  ret`name := Sprintf("SL(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic MultiplicativeAlgebraicGroup(k::Fld) -> GrpRed
{Constructs the multiplicative group of the field k as an algebraic group.}
  return GeneralLinearAlgberaicGroup(1, k);
end intrinsic;

intrinsic AdditiveAlgebraicGroup(k::Fld) -> GrpRed
{Constructs the additive group of the field k as an algebraic group.}
  ret := SpecialLinearAlgebraicGroup(2, k);
  R := Universe(ret`I);
  n := 2;
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret`I cat:= [x[1][1]-1, x[2][1], x[2][2]-1];
  ret`name := Sprintf("additive group over %o", k);
  return ret;
end intrinsic;

intrinsic BilinearAlgebraicGroup(S::AlgMatElt[Fld]) -> GrpRed
{Constructs the algebraic group of matrices X s.t. X^t*S*X = S}
  k := BaseRing(S);
  n := Degree(Parent(S));
  ret := GeneralLinearAlgberaicGroup(n,k);
  R := Universe(ret`I);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret`I cat:= Eltseq(Transpose(x)*S*x-S);
  ret`name := Sprintf("algebraic group of matrices preserving a bilinear form of rank %o over %o", n, k); 
  return ret;
end intrinsic;

intrinsic SymplecticAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
{Constructs the standard symplectic group of degree n over k, Sp(n), as an algebraic group.}
  require IsEven(n) : "n must be even for Sp(n) to exist.";
  m := n div 2;
  one := IdentityMatrix(k, m);
  zero := 0 * one;
  S := BlockMatrix([[zero, one], [-one, zero]]);
  ret := BilinearAlgebraicGroup(S);
  ret`name := Sprintf("Sp(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic OrthogonalAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
{Constructs the standard orthogonal group of degree n over k, O(n), as an algebraic group.}
  if Characteristic(k) ne 2 then
    ret := BilinearAlgebraicGroup(IdentityMatrix(k,n));
    ret`name := Sprintf("O(%o, %o)", n, k);
    return ret;
  else
    return SplitOrthogonalAlgebraicGroup(n,k);    
  end if;
end intrinsic;

intrinsic SpecialOrthogonalAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
{Constructs the standard orthogonal group of degree n over k, O(n), as an algebraic group.}
  ret := OrthogonalAlgebraicGroup(n, k) meet SpecialLinearAlgebraicGroup(n,k);
  ret`name := Sprintf("SO(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic 'meet'(G1::GrpRed, G2::GrpRed) -> GrpRed
{}
  require G1`k eq G2`k and G1`n eq G2`n : "groups are not subgroups of the same amtric group";
  ret := New(GrpRed);
  ret`k := G1`k;
  ret`n := G1`n;
  R1 := Universe(G1`I);
  R2 := Universe(G2`I);
  h := hom<R1 -> R2 | GeneratorsSequence(R2)>;
  ret`I := [h(f) : f in G1`I] cat G2`I;
  ret`name := Sprintf("intersection of %o and %o", G1, G2);
  return ret;
end intrinsic;

intrinsic SplitOrthogonalAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
{Constructs the standard orthogonal group of degree n over k, O(n), as an algebraic group.}
  m := n div 2;
  one := IdentityMatrix(k, m);
  zero := 0 * one;
  if Characteristic(k) ne 2 then
     S := BlockMatrix([[zero, one], [one, zero]]);
     if IsOdd(m) then 
       S := DirectSum(S, IdentityMatrix(k,1));
     end if;
     ret := BilinearAlgebraicGroup(S);
  else
     T := BlockMatrix([[zero, one], [zero, zero]]);
     if IsOdd(m) then
       T := DirectSum(T, IdentityMatrix(k,1));
     end if;
     ret := GeneralLinearAlgberaicGroup(n,k);
     R := Universe(ret`I);
     var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
     x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
     mat := x*T*Transpose(x)+x;
     skew := Eltseq(Transpose(mat)+mat) cat Diagonal(mat);
     ret`I cat:= skew;
  end if;
  ret`name := Sprintf("split O(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic SplitSpecialOrthogonalAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
{Constructs the standard orthogonal group of degree n over k, O(n), as an algebraic group.}
  ret := SplitOrthogonalAlgebraicGroup(n, k) meet SpecialLinearAlgebraicGroup(n,k);
  ret`name := Sprintf("split SO(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic DiagonalMatricesAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
{Constructs the group of diagonal matrices in GL(n,k).}
  ret := GeneralLinearAlgberaicGroup(n,k);
  R := Universe(ret`I);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret`I cat:= [x[i][j] : i,j in [1..n] | i ne j];
  ret`name := Sprintf("diagonal matrices in GL(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic UpperTriangularMatricesAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
{Constructs the group of diagonal matrices in GL(n,k).}
  ret := GeneralLinearAlgberaicGroup(n,k);
  R := Universe(ret`I);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret`I cat:= [x[i][j] : i,j in [1..n] | i gt j];
  ret`name := Sprintf("upper triangular matrices in GL(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic UpperTriangularUnipotentMatricesAlgebraicGroup(n::RngIntElt, k::Fld) -> GrpRed
{Constructs the group of diagonal matrices in GL(n,k).}
  ret := GeneralLinearAlgberaicGroup(n,k);
  R := Universe(ret`I);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret`I cat:= [x[i][j] : i,j in [1..n] | i gt j];
  ret`I cat:= [x[i][i]-1 : i in [1..n]];
  ret`name := Sprintf("upper triangular unipotent matrices in GL(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic Eltseq(g::GrpRedElt) -> SeqEnum
{}
  return Eltseq(g`elt);
end intrinsic;

intrinsic IdentityComponent(G::GrpRed) -> GrpRed
{returns the identity component of G.}
  A := AffineSpace(Universe(G`I));
  S := Scheme(A, G`I);
  S_irr := IrreducibleComponents(S);
  one := S!(Eltseq(G!1) cat[1]);
  assert exists(S0){s : s in S_irr | one in s};
  ret := LinearAlgebraicGroup(DefiningPolynomials(S0));
  ret`name := Sprintf("identity component of %o", G`name);
  return ret;
end intrinsic;

intrinsic 'eq'(G1::GrpRed, G2::GrpRed) -> BoolElt
{}
  return (G1`k eq G2`k) and (G1`n eq G2`n) and (G1`I eq G2`I);
end intrinsic;

intrinsic Centralizer(G::GrpRed, S::SeqEnum[GrpRedElt]) -> GrpRed
{}
  ret := New(GrpRed);
  ret`k := G`k;
  ret`n := G`n;
  ret`I := G`I;
  R := Universe(ret`I);
  n := G`n;
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  S_R := [ChangeRing(s`elt, R) : s in S];
  ret`I cat:= &cat[Eltseq(x*s-s*x) : s in S_R];
  ret`name := Sprintf("centralizer of %o in %o", S, G);
  return ret;
end intrinsic;

intrinsic Centralizer(G::GrpRed, g::GrpRedElt) -> GrpRed
{}
  return Centralizer(G, [g]);
end intrinsic;

intrinsic Normalizer(G::GrpRed, S::SeqEnum[GrpRedElt]) -> GrpRed
{}
  ret := New(GrpRed);
  ret`k := G`k;
  ret`n := G`n;
  ret`I := G`I;
  n := G`n;
  R := Universe(G`I);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  S_R := [ChangeRing(s`elt, R) : s in S];
  polys := [Eltseq(x*s1-s2*x) : s1, s2 in S_R];
  prod_polys := [&*p : p in CartesianProduct(polys)];
  ret`I cat:= prod_polys;
  ret`name := Sprintf("normalizer of %o in %o", S, G);
  return ret;
end intrinsic;

intrinsic IsCommutative(G::GrpRed) -> BoolElt
{}
  n := G`n;
  k := G`k;
  RxR := PolynomialRing(k, 2*(n^2+1));
  I := [Evaluate(f, [RxR.i : i in [1..n^2+1]]) : f in G`I];
  I cat:= [Evaluate(f, [RxR.(n^2+1+i) : i in [1..n^2+1]]) : f in G`I];
  RxR_I := quo<RxR | I>;
  x_var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  y_var_names := [[Sprintf("y_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[RxR_I.(Index(&cat x_var_names, x_var_names[i][j]))
		     : j in [1..n]]: i in [1..n]]);
  y := Matrix([[RxR_I.(n^2+1+Index(&cat y_var_names, y_var_names[i][j]))
		      : j in [1..n]]: i in [1..n]]);
  return x*y eq y*x;
end intrinsic;

intrinsic IsAbelian(G::GrpRed) -> BoolElt
{}
  return IsCommutative(G);
end intrinsic;

intrinsic LieAlgebra(G::GrpRed) -> AlgMatLie
{returns the Lie algebra associated to G.}
  n := G`n;
  k := G`k;
  I := G`I;
  gln := MatrixLieAlgebra(Rationals(), n);
  R := Universe(I);
  A := AffineSpace(R);
  S := Scheme(A,I);
  one := S!(Eltseq(G!1) cat[1]);
  // see if it works - if not we can differentiate the relations in I manually
  lie_G := TangentSpace(S, one);
  tau := Translation(lie_G, one);
  fs := Generators(Ideal(tau(lie_G)));
  rels := Matrix([[Coefficient(f, R.i, 1) : i in [1..n^2+1]] : f in fs]);
  rels := ChangeRing(rels, k);
  basis := Basis(Kernel(Transpose(rels)));
  return sub<gln | [gln!(Eltseq(b)[1..n^2]) : b in basis]>;
end intrinsic;

intrinsic IsSemisimple(G::GrpRed) -> BoolElt
{}
  return IsSemisimple(LieAlgebra(G));
end intrinsic;

intrinsic IsDiagonalizable(G::GrpRed) -> BoolElt
{}
  return IsAbelian(G) and &and[IsSemisimple(b) : b in Basis(LieAlgebra(G))];
end intrinsic;

intrinsic IsTorus(G::GrpRed) -> BoolElt
{}
  return IsConnected(G) and IsDiagonalizable(G);
end intrinsic;

intrinsic IsSolvable(G::GrpRed) -> BoolElt
{}
  return IsSolvable(LieAlgebra(G));
end intrinsic;

//====================
//
// ALGEBRAIC MODULAR FORMS


//
// This file contains the basic structures and hackobj nonsense for the ModFrmAlg package.
//
// Matthew Greenberg and John Voight, 2012
//
//====================

declare attributes ModTupRng:
  almost_basis;       // If M=I_1*a_1 + ... + I_n*a_n and
                      // b_i is in I_i-I_i^2, then almost_basis is
                      // [b_1*a_1, ..., b_n*a_n].
		      // This doesn't work for I_i not prime.

declare attributes ModTupFld:
  Quadraticity,       // "Orthogonal", "Hermitian", etc.
  QSpaceBasis,        // A basis of V as a Q-vector space 
  QSpaceBasisMatrix,  // The matrix of QSpaceBasis pushed down to Q
  AuxForms,           // The auxilliary forms that define V as an L-space
  ScalarMultQMats;    // Matrices of multiplication by elements of the basis of the base field of V 

declare attributes ModDed:   
                      // = Lambda
  AmbientSpace,       // Lambda's ambient L-space
  Discriminant,       // Discriminant
  Dual,               // Dual lattice  
  ModDedZZ_F,         // The Hermitian lattice Lambda, pushed down to ZZ_F 
  ModDedZZ_FBasis,    // Basis for LambdaZZ.
  ModDedZZ_FAuxForms, // The auxiliary forms which define LambdaZZ as a module over ZZ_F.

  QuadraticSpace,     // 
  Lattice,            // = Lattice(Lambda) = LambdaZZ, the lattice pushed down to ZZ, of type Lat.
  LatticeZZBasis,     // Basis for LambdaZZ.
  LatticeZZBasisConj, // Componentwise complex conjugate of LambdaZZ.
  LatticeAuxForms,    // The auxiliary forms which define LambdaZZ as a module over ZZ_F.
  LatticeAutomorphismGroup,
                      // = LatticeAutomorphismGroup(Lambda), the automorphism group of LambdaZZ.
  ParentModFrmAlg,    // = M

  Discriminant,       // = Discriminant(Lambda), the discriminant ideal of Lambda.

  ppStandardBases,    // Cached standard bases.  
  almost_basis;

declare attributes ModFrmAlg:

  BaseField, // Field over which the group is defined
  HermitianExtensionField, // Extension field for unitary groups
  SplittingField,  // These should be the same 
  CartanName,
  Rank,
  LieGroupOverSplittingField,
  Weight,
  WeightModule,
  IsFull,
  IsCuspidal,
  IsEisenstein,
  SplittingMap,
  QuadraticSpace,
  MotherLattice;

//=======
//
// Hackobj nonsense
//
//=======

intrinsic HackobjPrintModFrmAlg(M::ModFrmAlg, level::MonStgElt)
{}
  F := BaseField(M);

  if IsCuspidal(M) then
    printf "Cuspidal subspace ";
  elif IsEisenstein(M) then
    printf "Eisenstein subspace ";
  else
    printf "Space ";
  end if;

  printf "of algebraic modular forms over the group ";
  cname := CartanName(M);
  if cname[1] eq "A" then
    printf "SU(%o) ", Rank(M)+1;
  elif cname[1] eq "B" then
    printf "SO(%o) ", 2*Rank(M)+1;
  elif cname[1] eq "D" then
    printf "SO(%o) ", 2*Rank(M);
  end if;
  printf "with Cartan name ";
  printf CartanName(M);
  printf " over \n   %o", BaseField(M);
  if CartanName(M)[1] eq "A" then
    printf "\n   relative to the field %o", M`HermitianExtensionField;
  end if;
  printf "\n   Weight: %o", Weight(M);
  printf "\n   Splitting field: %o", SplittingField(M);
  if assigned M`Dimension then
    printf "\n   Dimension: %o", Dimension(M);
  end if;
end intrinsic;

intrinsic HackobjCoerceModFrmAlg(M::ModFrmAlg, x::.) -> BoolElt, .
{}
  if Type(x) eq ModFrmAlgElt and Parent(x) cmpeq M then
    return true, x;
  end if;
  return false;
end intrinsic;

intrinsic HackobjInModFrmAlg(x::., M::ModFrmAlg) -> BoolElt
{}
  if Type(x) ne ModFrmAlgElt then
    return false, "The first argument should be a ModFrmAlgElt";
  else
    return Parent(x) eq M;
  end if;
end intrinsic;

intrinsic HackobjParentModFrmAlgElt(f::.) -> ModFrmAlg
{}
  return f`Parent;
end intrinsic;

intrinsic HackobjPrintModFrmAlgElt(f::.)
{}
  printf "Element of ";
  HackobjPrintModFrmAlg(Parent(f));
end intrinsic;

intrinsic HackobjCoerceModFrmAlgElt(f::ModFrmAlgElt, x::.) -> BoolElt, .
{}
  return false;
end intrinsic;

intrinsic HackobjInModFrmAlgElt(x::., f::ModFrmAlgElt) -> BoolElt
{}
  return false;
end intrinsic;



//=======
//
// Creation
//
//=======

function get_rational_lattice(L : H := 1)
  O_E := BaseRing(L);
  E := FieldOfFractions(O_E);
  aut := Automorphisms(E);
  B_L := Basis(L);
  B_E := Basis(O_E);
  dim := #B_L;
  if (H eq 1) then H := IdentityMatrix(E, dim); end if;
  deg := #B_E;
  nvars := dim*deg;
  E_X := PolynomialRing(E, nvars);
  BLX := [ChangeRing(v, E_X) : v in B_L];
  vecs := [ &+ [(&+[ a(B_E[j]) * E_X.((i-1)*deg + j) :
	    j in [1..deg] ])*BLX[i]  : i in [1..dim]] : a in aut];
  norm_form := InnerProduct(vecs[1]*ChangeRing(H, E_X), vecs[2]);
  coefs := &cat [[MonomialCoefficient(norm_form, E_X.i * E_X.j) :
			       j in [i..nvars]] : i in [1..nvars]];
  A := UpperTriangularMatrix(coefs);
  Q := ChangeRing((A + Transpose(A))/2, Rationals());
  Q_lat := LatticeWithGram(Q);
  return Q_lat;
end function;

function InitAn(F, n, L);
  assert n ge 1;

  M := HackobjCreateRaw(ModFrmAlg);
  M`BaseField := F;
  M`HermitianExtensionField := L;

  k := L;   // Only works because assumed to be in the split case
  M`SplittingField := k;  
  M`CartanName := "A" cat IntegerToString(n);
  M`Rank := n;

  G := GroupOfLieType(M`CartanName, k : Isogeny := "SC");
  M`LieGroupOverSplittingField := G;
  M`Weight := TrivialRepresentation(G);
  M`WeightModule := VectorSpace(Codomain(M`Weight));

  M`IsFull := true;
  M`IsCuspidal := false;
  M`IsEisenstein := false;

  mn := StandardRepresentation(G);
  M`SplittingMap := Inverse(mn);

  // This is not correct: we need to take the restriction of scalars down to F.
  V := QuadraticSpace(IdentityMatrix(L, n+1));
  M`QuadraticSpace := V;
  Lambda := Module(PseudoMatrix(IdentityMatrix(Integers(L), n+1)));
  Lambda`ParentModFrmAlg := M;
  Lambda`QuadraticSpace := V;
  M`MotherLattice := Lambda;
  M`L := Lambda;

/*
  Lambda := Module(PseudoMatrix(IdentityMatrix(Integers(L), n+1)));
  M`L := get_rational_lattice(Lambda);
  V := QuadraticSpace(IdentityMatrix(Rationals(), (n+1)*Degree(L)));
// This is what we really want but is not working at the moment -
// Figure out why
// V := AmbientQuadraticSpace(InnerProductMatrix(M`L));
  M`QuadraticSpace := V;
  M`MotherLattice := Lambda;
  Lambda`ParentModFrmAlg := M;
  Lambda`QuadraticSpace := V;
*/
  return M;
end function;

function InitBnDn(V,Lambda);
  M := HackobjCreateRaw(ModFrmAlg);
  F := BaseField(V);
  M`BaseField := F;

  // TODO: Compute a splitting field
  k := ext<F | Polynomial([1,0,1])>;
  M`SplittingField := k;

  m := Dimension(V);
  n := Floor(m/2);
  if m mod 2 eq 1 then
    M`CartanName := "B" cat IntegerToString(n);
  else
    M`CartanName := "D" cat IntegerToString(n);
  end if;
  M`Rank := n;

  G := GroupOfLieType(M`CartanName, k : Isogeny := "SC");
  M`LieGroupOverSplittingField := G;
  M`Weight := TrivialRepresentation(G);
  M`WeightModule := VectorSpace(Codomain(M`Weight));

  M`IsFull := true;
  M`IsCuspidal := false;
  M`IsEisenstein := false;

  mn := StandardRepresentation(G);
  M`SplittingMap := Inverse(mn);

  M`QuadraticSpace := V;
  if Lambda cmpeq [] then
    Lambda := Module(PseudoMatrix(IdentityMatrix(Integers(F), m)));
  end if;
  Lambda`ParentModFrmAlg := M;
  Lambda`QuadraticSpace := V;
  M`MotherLattice := Lambda;

  return M;
end function;




intrinsic AlgebraicModularForms(F::FldNum, L::FldNum, s::MonStgElt) -> ModFrmAlg
  {The space of algebraic modular forms over the split unitary group U(n+1) of type s = "An"
   relative to the CM extension L over F.}

  require s[1] eq "A" : "When a Hermitian field extension is specified, must be of type An.";
  n := StringToInteger(s[2..#s]);

  require IsAbsoluteField(F) : "The base field F must be an absolute extension of the rationals.";
  require IsTotallyReal(F) : "The base field F must be totally real.";
  require BaseField(L) eq F : "L must be an extension of F.";
  require Degree(L) eq 2 : "L must be a quadratic extension of F.";
  require Signature(AbsoluteField(L)) eq 0 : "L must be a CM extension of F.";

  return InitAn(F, n, L);
end intrinsic;

intrinsic UnitaryModularForms(F::FldNum, L::FldNum, m::RngIntElt) -> ModFrmAlg
  {The space of algebraic modular forms over the split unitary group U(m) of type "A(m-1)"
   relative to the CM extension L over F.}

  require IsAbsoluteField(F) : "The base field F must be an absolute extension of the rationals.";
  require IsTotallyReal(F) : "The base field F must be totally real.";
  require BaseField(L) eq F : "L must be an extension of F.";
  require Degree(L) eq 2 : "L must be a quadratic extension of F.";
  require Signature(AbsoluteField(L)) eq 0 : "L must be a CM extension of F.";

  return InitAn(F, m-1, L);
end intrinsic;

intrinsic AlgebraicModularForms(V::ModTupRng, s::MonStgElt : Lambda := []) -> ModFrmAlg
  {The space of algebraic modular forms over the orthogonal group SO(V) over F of type s = "Bn" or "Dn" and lattice Lambda.}

  require IsTotallyReal(BaseField(V)) : "The base field F must be totally real.";
  require s[1] in ["B","D"] : "s must be Bn or Dn.";

  n := StringToInteger(s[2..#s]);
  m := Dimension(V);

  require m ge 3 : "Must have n >= 1";

  if m mod 2 eq 1 then
    require s[1] eq "B" and m eq 2*n+1 : "dim(V) = 2*n+1 is type Bn.";
  else
    require s[1] eq "D" and m eq 2*n : "dim(V) = 2*n is type Dn.";
  end if;

  return InitBnDn(V, Lambda);
end intrinsic;

intrinsic OrthogonalModularForms(V::ModTupRng : Lambda := []) -> ModFrmAlg
  {The space of algebraic modular forms over the orthogonal group SO(V) over F and lattice Lambda.}

  require IsTotallyReal(BaseField(V)) : "The base field F must be totally real.";
  require Dimension(V) ge 3 : "Must have n >= 1";
  
  return InitBnDn(V, Lambda);
end intrinsic;


intrinsic AlgebraicModularForms(QQ::FldRat, L::FldNum, s::MonStgElt) -> ModFrmAlg
  {The space of algebraic modular forms over the split unitary group U(n+1) of type s = "An"
   relative to the CM extension L over QQ.}

  require s[1] eq "A" : "When a Hermitian field extension is specified, must be of type An.";
  n := StringToInteger(s[2..#s]);

  require BaseField(L) eq QQ : "L must be an extension of QQ.";
  require Degree(L) eq 2 : "L must be a quadratic extension of QQ.";
  require Signature(L) eq 0 : "L must be a CM extension of QQ.";

  return InitAn(QQ, n, L);
end intrinsic;

intrinsic UnitaryModularForms(QQ::FldRat, L::FldNum, m::RngIntElt) -> ModFrmAlg
  {The space of algebraic modular forms over the split unitary group U(m) of type "A(m-1)"
   relative to the CM extension L over QQ.}

  require BaseField(L) eq QQ : "L must be an extension of QQ.";
  require Degree(L) eq 2 : "L must be a quadratic extension of QQ.";
  require Signature(L) eq 0 : "L must be a CM extension of QQ.";

  return InitAn(QQ, m-1, L);
end intrinsic;

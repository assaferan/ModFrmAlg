// Redoing the reductive group as an affine group scheme,
// to provide a better framework
// and more generality
// Elements of the group scheme G are elements of G(k), where k is the base ring.

freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J. Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         

                                                                            
   FILE: grpSch.m (Group Scheme object)

   04/16/21: File created.
 
 ***************************************************************************/

// Here we list the intrinsics that this file defines

declare type GrpSch[GrpSchElt];
declare attributes GrpSch:
        // assuming it is a subgroup of GL(n,k)
        k,
        n,
        // generators of the vanishing ideal
        I,
        // in case this group has a special name
  name,
  S,
  inv,
  m,
  e; 

declare attributes GrpSchElt:
        // the reductive group containing it
        parent,
        // the matrix representing the element.
        elt;

declare type MapGrpSch : Map;
declare attributes MapGrpSch:
  // the map of schemes
  phi;

intrinsic GeneralLinearAlgebraicGroup(n::RngIntElt, k::Rng) -> GrpSch
{Constructs GL(n) over k as an algebraic group}
  require n gt 0 : "n must be positive.";
/*
  ret := New(GrpSch);
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
*/
  R := PolynomialRing(k, n^2+1);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  AssignNames(~R, &cat var_names cat ["det_inv"]);
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  det := Determinant(x);
  det_inv := R.(n^2+1);
  A := AffineSpace(R);
  G := Scheme(A, det_inv*det-1);
  RR := PolynomialRing(k, 2*(n^2+1));
  AA<[y]> := AffineSpace(RR);
  polys := [Evaluate(det_inv*det-1, y[(n^2+1)*i+1..(n^2+1)*(i+1)]) : i in [0..1]];
  GG := Scheme(AA, polys);
  x1 := Matrix([[RR.(Index(&cat var_names, var_names[i][j]))
		   : j in [1..n]]: i in [1..n]]);
  x2 := Matrix([[RR.(n^2+1+Index(&cat var_names, var_names[i][j]))
		   : j in [1..n]]: i in [1..n]]);
  m := map<GG -> G | Eltseq(x1*x2) cat [y[n^2+1]*y[2*(n^2+1)]]>;
  inv := map<G -> G | Eltseq(det_inv*Adjoint(x)) cat [det]>;
  // Working with spec k does weird things
  A1<x> := AffineSpace(k, 1);
  pt := Scheme(A1, [x]);
//  pt := Spec(k);
  e := map<pt -> G | Eltseq(IdentityMatrix(k,n)) cat [1]>;
  ret := GroupScheme(m, inv, e);
  if n eq 1 then
    ret`name := Sprintf("multiplicative group over %o", k);
  else
    ret`name := Sprintf("GL(%o,%o)", n, k);
  end if;
  return ret;
end intrinsic;

intrinsic LinearAlgebraicGroup(I::SeqEnum[RngMPolElt]) -> GrpSch
{Constructs the linear algebraic group defined as a closed subgroup of GL(n) via the ideal I.}
  require not IsEmpty(I) : "I need to be a nonepmty sequence of polynomials";
  ret := New(GrpSch);
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

intrinsic CoordinateRing(G::GrpSch) -> RngMPolRes
{The corresponding polynomial ring.}
  R := Universe(G`I);
  return quo<R | G`I>;
end intrinsic;

intrinsic Print(G::GrpSch, level::MonStgElt)
{Print the group scheme G.}
  if level eq "Magma" then
      // !! TODO - Complete this part
  elif assigned G`name then
      printf "%o", G`name;
  else
    printf "group scheme with underlying scheme %o", G`S;
  end if;
end intrinsic;

intrinsic SpecialLinearAlgebraicGroup(n::RngIntElt, k::Rng) -> GrpSch
{Constructs SL(n) over k as an algebraic group.}
/*
  ret := GeneralLinearAlgberaicGroup(n,k);
  R := Universe(ret`I);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  det := Determinant(x);
  ret`I cat:= [det - 1];
  ret`name := Sprintf("SL(%o, %o)", n, k);
*/
  R<[z]> := PolynomialRing(k, n^2);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  det := Determinant(x);
  A := AffineSpace(R);
  G := Scheme(A, det-1);
  RR := PolynomialRing(k, 2*n^2);
  AA<[y]> := AffineSpace(RR);
  polys := [Evaluate(det-1, y[n^2*i+1..n^2*(i+1)]) : i in [0..1]];
  GG := Scheme(AA, polys);
  x1 := Matrix([[RR.(Index(&cat var_names, var_names[i][j]))
		   : j in [1..n]]: i in [1..n]]);
  x2 := Matrix([[RR.(n^2+Index(&cat var_names, var_names[i][j]))
		   : j in [1..n]]: i in [1..n]]);
  m := map<GG -> G | Eltseq(x1*x2)>;
  inv := map<G -> G | Eltseq(Adjoint(x))>;
  A1<x> := AffineSpace(k, 1);
  pt := Scheme(A1, [x]);
//  pt := Spec(k);
  e := map<pt -> G | Eltseq(IdentityMatrix(k,n))>;
  AssignNames(~G, &cat var_names);
  ret := GroupScheme(m, inv, e);
  ret`name := Sprintf("SL(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic MultiplicativeAlgebraicGroup(k::Rng) -> GrpSch
{Constructs the multiplicative group of the field k as an algebraic group.}
  return GeneralLinearAlgebraicGroup(1, k);
end intrinsic;

intrinsic AdditiveAlgebraicGroup(k::Rng) -> GrpSch
{Constructs the additive group of the field k as an algebraic group.}
/*
  ret := SpecialLinearAlgebraicGroup(2, k);
  R := Universe(ret`I);
  n := 2;
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret`I cat:= [x[1][1]-1, x[2][1], x[2][2]-1];
  ret`name := Sprintf("additive group over %o", k);
  return ret;
*/
  R := PolynomialRing(k,1);
  G<x> := AffineSpace(R);
  RR := PolynomialRing(k, 2);
  GG<[y]> := AffineSpace(RR);
  m := map<GG -> G | [y[1] + y[2]]>;
  inv := map<G -> G | [-x]>;
  A1<x> := AffineSpace(k, 1);
  pt := Scheme(A1, [x]);
  e := map<pt -> G | [0] >;
  ret := GroupScheme(m, inv, e);
  ret`name := Sprintf("additive group over %o", k);
  return ret;
end intrinsic;

intrinsic BilinearAlgebraicGroup(S::AlgMatElt[Rng]) -> GrpSch
{Constructs the algebraic group of matrices X s.t. X^t*S*X = S}
  k := BaseRing(S);
  n := Degree(Parent(S));
  gl_n := GeneralLinearAlgebraicGroup(n,k);
  R := CoordinateRing(Scheme(gl_n));
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret := sub<gl_n | Eltseq(Transpose(x)*S*x-S)>;
  ret`name := Sprintf("algebraic group of matrices preserving a bilinear form of rank %o over %o", n, k); 
  return ret;
end intrinsic;

intrinsic SymplecticAlgebraicGroup(n::RngIntElt, k::Rng) -> GrpSch
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

intrinsic OrthogonalAlgebraicGroup(n::RngIntElt, k::Rng) -> GrpSch
{Constructs the standard orthogonal group of degree n over k, O(n), as an algebraic group.}
  if Characteristic(k) ne 2 then
    ret := BilinearAlgebraicGroup(IdentityMatrix(k,n));
    ret`name := Sprintf("O(%o, %o)", n, k);
    return ret;
  else
    return SplitOrthogonalAlgebraicGroup(n,k);    
  end if;
end intrinsic;

intrinsic SpecialOrthogonalAlgebraicGroup(n::RngIntElt, k::Rng) -> GrpSch
{Constructs the standard orthogonal group of degree n over k, O(n), as an algebraic group.}
  ret := OrthogonalAlgebraicGroup(n, k) meet SpecialLinearAlgebraicGroup(n,k);
  ret`name := Sprintf("SO(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic 'meet'(G1::GrpSch, G2::GrpSch) -> GrpSch
{.}
/*
  require G1`k eq G2`k and G1`n eq G2`n : "groups are not subgroups of the same matrix group";
  ret := New(GrpSch);
  ret`k := G1`k;
  ret`n := G1`n;
  R1 := Universe(G1`I);
  R2 := Universe(G2`I);
  h := hom<R1 -> R2 | GeneratorsSequence(R2)>;
  ret`I := [h(f) : f in G1`I] cat G2`I;
*/
  ret := sub<G1 | G1`S meet G2`S>;
  ret`name := Sprintf("intersection of %o and %o", G1, G2);
  return ret;
end intrinsic;

intrinsic SplitOrthogonalAlgebraicGroup(n::RngIntElt, k::Rng) -> GrpSch
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
     ret := GeneralLinearAlgebraicGroup(n,k);
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

intrinsic SplitSpecialOrthogonalAlgebraicGroup(n::RngIntElt, k::Rng) -> GrpSch
{Constructs the standard orthogonal group of degree n over k, O(n), as an algebraic group.}
  ret := SplitOrthogonalAlgebraicGroup(n, k) meet SpecialLinearAlgebraicGroup(n,k);
  ret`name := Sprintf("split SO(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic DiagonalMatricesAlgebraicGroup(n::RngIntElt, k::Rng) -> GrpSch
{Constructs the group of diagonal matrices in GL(n,k).}
  ret := GeneralLinearAlgebraicGroup(n,k);
  R := Universe(ret`I);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret`I cat:= [x[i][j] : i,j in [1..n] | i ne j];
  ret`name := Sprintf("diagonal matrices in GL(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic UpperTriangularMatricesAlgebraicGroup(n::RngIntElt, k::Rng) -> GrpSch
{Constructs the group of diagonal matrices in GL(n,k).}
  ret := GeneralLinearAlgebraicGroup(n,k);
  R := Universe(ret`I);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret`I cat:= [x[i][j] : i,j in [1..n] | i gt j];
  ret`name := Sprintf("upper triangular matrices in GL(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic UpperTriangularUnipotentMatricesAlgebraicGroup(n::RngIntElt,
							 k::Rng) -> GrpSch
{Constructs the group of diagonal matrices in GL(n,k).}
  ret := GeneralLinearAlgebraicGroup(n,k);
  R := Universe(ret`I);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret`I cat:= [x[i][j] : i,j in [1..n] | i gt j];
  ret`I cat:= [x[i][i]-1 : i in [1..n]];
  ret`name := Sprintf("upper triangular unipotent matrices in GL(%o, %o)", n, k);
  return ret;
end intrinsic;

intrinsic Eltseq(g::GrpSchElt) -> SeqEnum
{.}
  return Eltseq(g`elt);
end intrinsic;

intrinsic Print(g::GrpSchElt, level::MonStgElt)
{}
  printf "%o", g`elt;
end intrinsic;

function build_elt(G,g)
  g_G := New(GrpSchElt);
  g_G`elt := g;
  g_G`parent := G;
  return g_G;
end function;

intrinsic Parent(g::GrpSchElt) -> GrpSch
{}
  return g`parent;
end intrinsic;

// Coercion
intrinsic IsCoercible(G::GrpSch, g::.) -> Bool, GrpSchElt
{.}
  // Here we should check that g satisfies the requirements to be in the
  //   group
  n := G`n;
  k := G`k;
  
  is_coer, g_Q := IsCoercible(GL(n,k), g);
  if not is_coer then
    return false, "cannot coerce element to an invertible matrix";
  end if;

  for f in G`I do
    if not IsZero(Evaluate(f, Eltseq(g_Q) cat [Determinant(g_Q)^(-1)])) then
      return false, "element does not lie in group";
    end if;
  end for;

  return true, build_elt(G, g_Q);
end intrinsic;

intrinsic '*'(g1::GrpSchElt, g2::GrpSchElt) -> GrpSchElt
{}
  require Parent(g1) eq Parent(g2) : "elements do not belong to the same group";
  G := Parent(g1);
  return build_elt(G, g1`elt*g2`elt);
end intrinsic;

intrinsic '^'(g::GrpSchElt, n::RngIntElt) -> GrpSchElt
{}
  return build_elt(Parent(g), g`elt^n);
end intrinsic;

intrinsic IdentityComponent(G::GrpSch) -> GrpSch
{returns the identity component of G.}
//  A := AffineSpace(Universe(G`I));
//  S := Scheme(A, G`I);
  S := G`S;
  S_irr := IrreducibleComponents(S);
//  one := S!(Eltseq(G!1) cat[1]);
  one := S!DefiningPolynomials(G`e);
  assert exists(S0){s : s in S_irr | one in s};
//  ret := LinearAlgebraicGroup(DefiningPolynomials(S0));
  inv0 := map<S0 -> S0 | DefiningPolynomials(G`inv)>;
  e0 := map<Domain(G`e) -> S0 | DefiningPolynomials(G`e)>;
  AA<[x]> := AmbientSpace(Domain(G`m));
  n := Dimension(AmbientSpace(S));
  S0_S0 := Scheme(AA, [Evaluate(p, x[n*i+1..n*(i+1)])
			: p in DefiningPolynomials(S0), i in [0..1]]);
  m0 := map<S0_S0 -> S0 | DefiningPolynomials(G`m)>;
  // We could construct the object without checking here. 
  ret := GroupScheme(m0, inv0, e0);
  ret`name := Sprintf("identity component of %o", G`name);
  return ret;
end intrinsic;

intrinsic 'eq'(G1::GrpSch, G2::GrpSch) -> BoolElt
{}
  return (G1`k eq G2`k) and (G1`n eq G2`n) and (G1`I eq G2`I);
end intrinsic;

intrinsic Centralizer(G::GrpSch, S::SeqEnum[GrpSchElt]) -> GrpSch
{}
  ret := New(GrpSch);
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

intrinsic Centralizer(G::GrpSch, g::GrpSchElt) -> GrpSch
{}
  return Centralizer(G, [g]);
end intrinsic;

intrinsic Normalizer(G::GrpSch, S::SeqEnum[GrpSchElt]) -> GrpSch
{}
  ret := New(GrpSch);
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

intrinsic IsCommutative(G::GrpSch) -> BoolElt
{}
/*
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
*/
  GG<[x]> := Domain(G`m);
  n := #x div 2;
  t := map<GG -> GG | x[n+1..2*n] cat x[1..n]>;
  return t*G`m eq G`m;
end intrinsic;

intrinsic IsAbelian(G::GrpSch) -> BoolElt
{}
  return IsCommutative(G);
end intrinsic;

intrinsic LieAlgebra(G::GrpSch) -> AlgMatLie
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

intrinsic IsSemisimple(G::GrpSch) -> BoolElt
{}
  return IsSemisimple(LieAlgebra(G));
end intrinsic;

intrinsic IsDiagonalizable(G::GrpSch) -> BoolElt
{}
  return IsAbelian(G) and &and[IsSemisimple(b) : b in Basis(LieAlgebra(G))];
end intrinsic;

intrinsic IsTorus(G::GrpSch) -> BoolElt
{}
  return IsConnected(G) and IsDiagonalizable(G);
end intrinsic;

intrinsic IsSolvable(G::GrpSch) -> BoolElt
{}
  return IsSolvable(LieAlgebra(G));
end intrinsic;

intrinsic MuAlgebraicGroup(n::RngIntElt, k::Rng) -> GrpSch
{.}
/*
  ret := GeneralLinearAlgebraicGroup(1, k);
  R := Universe(ret`I);
  n := 1;
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		 : j in [1..n]]: i in [1..n]]);
  ret`I cat:= [x[1][1]^n-1];
*/
  R<x> := PolynomialRing(k, 1);
  A := AffineSpace(R);
  G<x> := Scheme(A, x^n - 1);
  RR := PolynomialRing(k,2);
  AA<[y]> := AffineSpace(RR);
  GG := Scheme(AA, [y[1]^n-1, y[2]^n-1]);
  A1<x> := AffineSpace(k, 1);
  pt := Scheme(A1, [x]);
//  pt := Spec(k);
  m := map<GG -> G | [y[1]*y[2]] >;
  inv := map<G -> G | [x^(n-1)]>;
  e := map<pt -> G | [1]>;
  ret := GroupScheme(m, inv, e);
  ret`name := Sprintf("mu_%o", n);
  return ret;
end intrinsic;

intrinsic SplittingField(G::GrpSch) -> Fld
{Return the field over which G splits.}
  return G`k;
end intrinsic;

intrinsic BaseRing(G::GrpSch) -> Rng
{Return the field of definition of G.}
  return BaseRing(G`S);
end intrinsic;

function checkGroupAxioms(m, inv, e)
  if not ( IsRegular(m) and IsRegular(inv) and IsRegular(e)) then
    return false, "Regularity";
  end if;
  G := Domain(inv);
  k := BaseRing(G);
  pt := Domain(e);
  if (G ne Codomain(inv)) or (G ne Codomain(m))
     or (G ne Codomain(e)) then
    return false, "Domains do not match";
  end if;

  A := AmbientSpace(G);
  // Direct Product is not defined over arbitrary rings
  // This works when A is affine. what if it is projective?
  n := Dimension(A);
  AAA<[x]> := AffineSpace(k, 3*n);
  polys := &cat[[Evaluate(p, x[n*i+1..n*(i+1)]) : p in DefiningPolynomials(G)]
		: i in [0..2]];
  GGG := Scheme(AAA, polys);
  GG := Domain(m);
  pi_1 := map<GGG -> G | x[1..n]>;
  pi_3 := map<GGG -> G | x[2*n+1..3*n]>;
  pi_12 := map<GGG -> GG | x[1..2*n]>;
  pi_23 := map<GGG -> GG | x[n+1..3*n]>;
  m_x_id := map<GGG -> GG | DefiningPolynomials(pi_12*m)
    cat DefiningPolynomials(pi_3)>;
  id_x_m := map<GGG -> GG | DefiningPolynomials(pi_1)
    cat DefiningPolynomials(pi_23*m)>;
  if m_x_id*m ne id_x_m*m then
    return false, "Associativity";
  end if;

  A := AmbientSpace(G);
  z := GeneratorsSequence(CoordinateRing(A));
  e_polys := [Universe(z) | p : p in DefiningPolynomials(e)];
  e_x_id := map< G -> GG | e_polys cat z>;
  id_x_e := map< G -> GG | z cat e_polys>;
  id := map<G -> G | z>;
  if (id_x_e*m ne id) or (e_x_id*m ne id) then
    return false, "Unit";
  end if;

  inv_x_id := map<G -> GG | DefiningPolynomials(inv)
    cat DefiningPolynomials(id)>;
  id_x_inv := map<G -> GG | DefiningPolynomials(id)
    cat DefiningPolynomials(inv)>;
  // rho is the structure map
  // we assume here that pt is Speck[x]/x
  rho := map<G -> pt| [0] >;

  if (id_x_inv*m ne rho*e) or (inv_x_id*m ne rho*e) then
    return false, "Inverse";
  end if;

  return true, _;
end function;

intrinsic GroupScheme(m::MapSch, inv::MapSch, e::MapSch) -> GrpSch
{.}
  is_grp, why := checkGroupAxioms(m, inv, e);
  require is_grp : "Group axioms are not satisfied: %o.", why;
  G := New(GrpSch);
  G`S := Domain(inv);
  G`m := m;
  G`inv := inv;
  G`e := e;
  return G;
end intrinsic;

intrinsic BaseChange(G::GrpSch, k::Rng) -> GrpSch
{.}
  H := New(GrpSch);
  H`S := BaseChange(G`S, k);
  U := ChangeRing(Universe(DefiningPolynomials(G`inv)), k);
  H`inv := map<H`S -> H`S | [U | ChangeRing(p, k)
				: p in DefiningPolynomials(G`inv)]>;
  U := ChangeRing(Universe(DefiningPolynomials(G`e)), k);
  A1<x> := AffineSpace(k, 1);
  pt := Scheme(A1, [x]);
  H`e := map<pt -> H`S | [U | ChangeRing(p, k)
				: p in DefiningPolynomials(G`e)]>;
  U := ChangeRing(Universe(DefiningPolynomials(G`m)), k);
  H`m := map<BaseChange(Domain(G`m), k) -> H`S | [U | ChangeRing(p, k)
				: p in DefiningPolynomials(G`m)]>;
  return H;
end intrinsic;

intrinsic ChangeRing(G::GrpSch, k::Rng) -> GrpSch
{.}
  return BaseChange(G, k);
end intrinsic;


intrinsic HomConstr(G::GrpSch, H::GrpSch, t::. : Check := true) -> Map
{.}
  phi := map<G`S -> H`S | t>;
  if Check then
    GG<[x]> := Domain(G`m);
    n := #x div 2;
    HH := Domain(H`m);
    pi_1 := map<GG -> G`S | x[1..n]>;
    pi_2 := map<GG -> G`S | x[n+1..2*n]>;
    phi_2 := map<GG -> HH | DefiningPolynomials(pi_1*phi)
      cat DefiningPolynomials(pi_2*phi)>;
    require phi_2*H`m eq G`m*phi :
       "Polynomials do not define a group homomorphism.";
  end if;
/*
  ret := New(MapGrpSch);
  ret`phi := phi;
*/
  return phi;
end intrinsic;

intrinsic SubConstructor(G::GrpSch, t::.) -> GrpSch, Map
{.}
  assert #t eq 1;
  S := t[1];
  if Type(S) eq RngMPolElt then
    S := [S];
  end if;
  if ExtendedType(S) eq SeqEnum[RngMPolElt] then
    S := Scheme(Scheme(G), S);
  end if;
  assert Type(S) eq Sch;

  inv := map<S -> AmbientSpace(S) | DefiningPolynomials(G`inv)>;
  require Image(inv) subset S : "subscheme is not closed under inverse.";
  inv := map<S -> S | DefiningPolynomials(G`inv)>;
  e := map<Domain(G`e) -> AmbientSpace(S) | DefiningPolynomials(G`e)>;
  require Image(e) subset S : "subscheme does not contain the identity.";
  e := map<Domain(G`e) -> S | DefiningPolynomials(G`e)>;
  AA<[x]> := AmbientSpace(Domain(G`m));
  n := Dimension(AmbientSpace(G`S));
  S_S := Scheme(AA, [Evaluate(p, x[n*i+1..n*(i+1)])
			: p in DefiningPolynomials(S), i in [0..1]]);
  m := map<S_S -> AmbientSpace(S) | DefiningPolynomials(G`m)>;
  require Image(m) subset S : "subscheme is not closed under multiplication.";
  m := map<S_S -> S | DefiningPolynomials(G`m)>;
  
  return GroupScheme(m, inv, e), _;
end intrinsic;

intrinsic ReducedSubgroup(G::GrpSch) -> GrpSch
{.}
  return sub<G | ReducedSubscheme(G`S)>;
end intrinsic;

intrinsic Scheme(G::GrpSch) -> Sch
{.}
  return G`S;
end intrinsic;

intrinsic DirectProduct(G::SeqEnum[GrpSch]) -> GrpSch
{.}
  ret := G[1];
  for i in [2..#G] do
    ret := DirectProduct(ret, G[i]);
  end for;
  return ret;
end intrinsic;

intrinsic DirectProduct(G::GrpSch, n::RngIntElt) -> GrpSch
{.}
  return DirectProduct([G : i in [1..n]]);
end intrinsic;

intrinsic DirectProduct(G::GrpSch, H::GrpSch) -> GrpSch
{.}
  k := BaseRing(G);
  assert k eq BaseRing(H);
  A_G := AmbientSpace(G`S);
  A_H := AmbientSpace(H`S);
  n_G := Dimension(A_G);
  n_H := Dimension(A_H);
  n := n_G + n_H;

  A_GH<[x]> := AffineSpace(k, n);
  polys_G := [Evaluate(p, x[1..n_G]) : p in DefiningPolynomials(G`S)];
  polys_H := [Evaluate(p, x[n_G+1..n]) : p in DefiningPolynomials(H`S)];
  G_H := Scheme(A_GH, polys_G cat polys_H);

  inv_polys_G := [Evaluate(p, x[1..n_G]) : p in DefiningPolynomials(G`inv)];
  inv_polys_H := [Evaluate(p, x[n_G+1..n]) : p in DefiningPolynomials(H`inv)];

  inv := map<G_H -> G_H | inv_polys_G cat inv_polys_H>;

  A1<x> := AffineSpace(k, 1);
  pt := Scheme(A1, [x]);
  U := CoordinateRing(pt);

  e_polys_G := [U | p : p in DefiningPolynomials(G`e)];
  e_polys_H := [U | p : p in DefiningPolynomials(H`e)];

  e := map<pt -> G_H | e_polys_G cat e_polys_H>;

  AA<[x]> := AffineSpace(k, 2*n);
  G_H_G_H := Scheme(AA, [Evaluate(p, x[n*i+1..n*(i+1)])
			: p in DefiningPolynomials(G_H), i in [0..1]]);
  m_polys_G := [Evaluate(p, x[1..n_G] cat x[n+1..n+n_G])
		 : p in DefiningPolynomials(G`m)];
  m_polys_H := [Evaluate(p, x[n_G+1..n] cat x[n+n_G+1..2*n])
		 : p in DefiningPolynomials(H`m)];
  m := map<G_H_G_H -> G_H | m_polys_G cat m_polys_H>;
  ret := GroupScheme(m, inv, e);
  ret`name := Sprintf("Direct Product of %o and %o", G, H);
  return ret;
end intrinsic;

intrinsic IsReduced(G::GrpSch) -> BoolElt
{.}
  return IsReduced(Scheme(G));
end intrinsic;

intrinsic IsSmooth(G::GrpSch) -> BoolElt
{.}
  return IsReduced(G);
end intrinsic;

intrinsic AssignNames(~G::GrpSch, x::SeqEnum[MonStgElt])
{.}
//  printf "x = %o", x;
  AssignNames(~G`S, x);
end intrinsic;

intrinsic Name(G::GrpSch, i::RngIntElt) -> MonStgElt
{.}
  return Name(G`S, i);
end intrinsic;

intrinsic Hash(G::GrpSch) -> RngIntElt
{.}
  return Hash(G`S);
end intrinsic;

intrinsic Dimension(G::GrpSch) -> RngIntElt
{.}
  return Dimension(Scheme(G));
end intrinsic;

intrinsic IsConnected(G::GrpSch) -> BoolElt
{.}
  return IsIrreducible(Scheme(G));
end intrinsic;

intrinsic IsIrreducible(G::GrpSch) -> BoolElt
{.}
  return IsIrreducible(Scheme(G));
end intrinsic;

intrinsic NumberOfNames(G::GrpSch) -> RngIntElt
{.}
  return NumberOfNames(Scheme(G));
end intrinsic;

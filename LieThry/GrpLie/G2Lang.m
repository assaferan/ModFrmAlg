freeze;

/*
  Lang's theorem for G2(q)

  March 2022 Don Taylor

  $Id: G2Lang.m 65607 2022-03-23 01:35:45Z allan $
*/

import "ClassicalLang.m" : langGL_R, langGL_D;

createMatrix := function(extvec,n)
  d := Ncols(extvec);
  error if Binomial(n,3) ne d,"Vector does not lie in the exterior cube";
  pp := [[i,j] : i,j in [1..n]];
  tt := [[i,j,k] : k in [j+1..n], j in [i+1..n-1], i in [1..n-2]];
  F := BaseField(Parent(extvec));
  inv := Eltseq(extvec);
  M := KMatrixSpace(F,#pp,#tt);
  S := M!0;
  for c -> t in tt do
    i, j, k := Explode(t);
    for r -> pq in pp do
      p, q := Explode(pq);
      x := 0;
      case q :
        when i :
          if p lt j then
            x := inv[Index(tt,[p,j,k])];
          elif k lt p then
            x := inv[Index(tt,[j,k,p])];
          elif j lt p and p lt k then
            x := -inv[Index(tt,[j,p,k])];
          end if;
        when j :
          if p lt i then
            x := -inv[Index(tt,[p,i,k])];
          elif k lt p then
            x := -inv[Index(tt,[i,k,p])];
          elif i lt p and p lt k then
            x := inv[Index(tt,[i,p,k])];
          end if;
        when k :
          if p lt i then
            x := inv[Index(tt,[p,i,j])];
          elif j lt p then
            x := inv[Index(tt,[i,j,p])];
          elif i lt p and p lt j then
            x := -inv[Index(tt,[i,p,j])];
          end if;
      end case;
      S[r,c] := x;
    end for;
  end for;
  return S;
end function;


//==============================================================================
intrinsic IsInG2(G :: GrpMat, x :: GrpMatElt ) -> BoolElt
{Is x in the matrix group G of type G2?}
  K := BaseRing(G);
  p := Characteristic(K);
  ok, tp := LieType(G,p);
  require ok and tp[1] eq "G" and tp[2] eq 2: "G should be a group of type G2";
  if #K lt 5 or Degree(G) eq 6 then return (x in G); end if;
  require Degree(G) eq 7: "representation degree of G must be 7";
  require Nrows(x) eq 7: "matrix must be 7 by 7";
  V := VectorSpace(K,35);
  xi := V.12 - 2*V.13 - 2*V.19 + V.21 - V.26;
  if forall{ g : g in Generators(G) | xi*ExteriorPower(Matrix(g),3) eq xi } then
    return xi*ExteriorPower(Matrix(x),3) eq xi;
  end if;
  E := &meet[ Eigenspace(ExteriorPower(Matrix(g),3),1) : g in Generators(G) ];
  error if Dimension(E) ne 1, "cannot find an invariant 3-vector";
  xi := E.1;
  return xi*ExteriorPower(Matrix(x),3) eq xi;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic MyChevalleyBasis( L :: AlgLie : AssumeAlmostSimple := false) 
   -> SeqEnum, SeqEnum, SeqEnum
{ A Chevalley basis for the Lie algebra L }
  if assigned L`ChevalleyBasis then
    cb := L`ChevalleyBasis;
    return cb[1], cb[2], cb[3];
  end if;
  K := BaseRing(L);
  H := SplitToralSubalgebra(L);
  return ChevalleyBasis(L, H : AssumeAlmostSimple := AssumeAlmostSimple);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic G2Lang(c::GrpMatElt[FldFin], q::RngIntElt : Al := "Random") -> AlgMatElt
{ Return a such that c = a^-F *a , where F is the standard
  Frobenius endomorphism for q and c belongs to a group of type G2}
  k := GF(q);
  K := BaseRing(c);
  ok, p, e := IsPrimePower(q);
  require ok: "q must be a power of a prime";
  require p ne 2: "not implemented in characteristic 2";
  require Nrows(c) eq 7: "c must be a 7 by 7 matrix";
  require q mod Characteristic(K) eq 0: "base field of c incompatible with q";

  std3vector := func< E | E.12 - 2*E.13 - 2*E.19 + E.21 - E.26 >;
  E0 := VectorSpace(K,35);
  xi0 := std3vector(E0);
  require xi0*ExteriorPower(Matrix(c),3) eq xi0: 
    "c must belong to the standard copy of a group of type G2";

  A := MatrixAlgebra(k,7);
  U := MatrixLieAlgebra(k,7);

  frameMatrix := function(xi)
    X := createMatrix(xi,7);
    K0 := KernelMatrix(X);
    MLA := sub< U | [ A!Eltseq(K0[i]) : i in [1..Nrows(K0)] ] >;
    LA, phi := LieAlgebra(MLA);
    pos, neg, _ := MyChevalleyBasis(LA : AssumeAlmostSimple);
    epos := [ x@@phi : x in pos ];
    eneg := [ x@@phi : x in neg ];
    E := &meet[ Eigenspace(e,0) : e in epos];
    F := BaseRing(E);
    w1 := E.1;
    w2 := w1*eneg[1];
    w3 := w2*eneg[2];
    w4 := w3*eneg[1];
    w5 := w4*eneg[1]; // should we divide by 2?
    w6 := w5*eneg[2];
    w7 := w6*eneg[1];
    return Matrix(F,7,7,[w1,w2,w3,w4,w5,w6,w7]);
  end function;

  a := (Al eq "Random") select langGL_R(c,q) else langGL_D(c,q);
  assert FrobeniusImage(a,e)^-1*a eq c;
  L := BaseRing(a);

  E2 := VectorSpace(L,35);
  xi2 := std3vector(E2);
  xi3 := xi2*ExteriorPower(a,3)^-1;

  xi4 := ChangeRing(xi3,k);

  E1 := VectorSpace(k,35);
  xi1 := std3vector(E1);
  b1 := frameMatrix(xi1);
  b2 := frameMatrix(xi4);
  b := b2^-1*b1;
  s := b^-1*a;

  eta := xi2*ExteriorPower(s,3);
  d := Depth(xi2);
  lambda := eta[d]/xi2[d];
  if lambda ne L!1 then 
    assert exists(zeta){ zeta : zeta in k | zeta^3 eq lambda };
    s := zeta^-1*s;
  end if;

  return s;

end intrinsic;
//------------------------------------------------------------------------------


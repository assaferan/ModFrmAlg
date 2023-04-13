freeze;

/*
  Extracted from Weights.tex by MagmaCode 2.1 on Thu Oct  3 00:37:33 2019
 
  Highest weight code for groups of Lie type

  October 2019 Don Taylor

  $Id: Weights.m 59661 2019-10-11 06:13:02Z don $
*/

declare attributes Map: ContravariantForm, WeightFrame;
declare verbose Weights, 3;


//==============================================================================
intrinsic TheWeightSpaces( Q::SeqEnum[AlgMatElt] : U := BaseModule(Universe(Q)) )
      -> SeqEnum[SeqEnum], SeqEnum[PowModTupRng]
{The common eigenspaces of a sequence of commuting matrices}
  A := Universe( Q );
  k := BaseRing( A );
  V := BaseModule( A );

  K := (k cmpeq Rationals() or ISA(Type(k),FldAlg))
    select SplittingField( [ CharacteristicPolynomial(M) : M in Q ] )
      else SplittingField( { CharacteristicPolynomial(M) : M in Q } );

  if k ne K then
    Q := [ ChangeRing(M,K) : M in Q ];
    U := ChangeRing(U,K);
    V := ChangeRing(V,K);
  end if;

    restriction := func< M, S | Solution(T,T*M) where T is Matrix(Basis(S)),
          func< v | &+[ v[i]*V!(S.i) : i in [1..Dimension(S)] ] > >;

  spaces := [* U *];
  eigvals := [ [] ];
  for M in Q do
    spaces_ := [* *];
    eigvals_ := [];
    for i := 1 to #spaces do
      ev := eigvals[i];
      X, h := restriction(M,spaces[i]);
      for e in Eigenvalues(X) do
        Append(~spaces_,
          sub<V| [h(b) : b in Basis(Eigenspace(X,e[1]))]>);
        Append(~eigvals_, ev cat [e[1]]);
      end for;
    end for;
    spaces := spaces_;
    eigvals := eigvals_;
  end for;
  return eigvals, spaces;
end intrinsic;
//------------------------------------------------------------------------------

steinbergSymbol := function(G)
  R := RootDatum(G);
  tp := CartanName(R);
  twist := TwistingDegree(R);
  ttp := IntegerToString(twist) * tp;
  q := #DefRing(G);
  if ttp eq "3D4" then
    N := 12;
    x := function(i,a)
      return case< i | 
      1 : elt<G|<2,a>>,
      2 : elt<G|<1,-a>,<4,-a^q>,<3,-a^q^2>>,
      3 : elt<G|<5,a>,<7,a^q>,<6,a^q^2>>,
      4 : elt<G|<10,-a>,<8,-a^q>,<9,-a^q^3>>,
      5 : elt<G|<11,a>>,
      6 : elt<G|<12,a>>,
      -1 : elt<G|<N+2,a>>,
      -2 : elt<G|<N+1,-a>,<N+4,-a^q>,<N+3,-a^q^2>>,
      -3 : elt<G|<N+5,a>,<N+7,a^q>,<N+6,a^q^2>>,
      -4 : elt<G|<N+10,-a>,<N+8,-a^q>,<N+9,-a^q^3>>,
      -5 : elt<G|<N+11,a>>,
      -6 : elt<G|<N+12,a>>,
       default : false>;
    end function;
  elif ttp eq "2E6" then
    N := 36;
    x := function(i,a)
      return case< i | 
      1 : elt<G|<2,a>>,
      2 : elt<G|<4,a>>,
      3 : elt<G|<3,-a>,<5,-a^q>>,
      4 : elt<G|<1,a>,<6,a^q>>,
      5 : elt<G|<8,a>>,
      6 : elt<G|<9,a>,<10,a^q>>,
      7 : elt<G|<7,a>,<11,a^q>>,
      8 : elt<G|<15,-a>>,
      -1 : elt<G|<N+2,a>>,
      -2 : elt<G|<N+4,a>>,
      -3 : elt<G|<N+3,-a>,<N+5,-a^q>>,
      -4 : elt<G|<N+1,a>,<N+6,a^q>>,
      -5 : elt<G|<N+8,a>>,
      -6 : elt<G|<N+9,a>,<N+10,a^q>>,
      -7 : elt<G|<N+7,a>,<N+11,a^q>>,
      -8 : elt<G|<N+15,-a>>,
       default : false >;
   end function;
  else
    error "Not available for type",ttp;
  end if;
  return x;
end function;

obverseSymbol := function(G) 
  R := RootDatum(G);
  twist := TwistingDegree(R);
  ttp := IntegerToString(twist) * CartanName(R);
  q := #DefRing(G);
  if ttp eq "3D4" then
    N := 12;
    x := function(i,a)
      return case< i | 
       1 : elt<G|<N+2,a>>,
       2 : elt<G|<N+3,-a^q^2>,<N+4,-a^q>,<N+1,-a>>,
       3 : elt<G|<N+6,a^q^2>,<N+7,a^q>,<N+5,a>>,
       4 : elt<G|<N+9,-a^q^3>,<N+8,-a^q>,<N+10,-a>>,
       5 : elt<G|<N+11,a>>,
       6 : elt<G|<N+12,a>>,
      -1 : elt<G|<2,a>>,
      -2 : elt<G|<3,-a^q^2>,<4,-a^q>,<1,-a>>,
      -3 : elt<G|<6,a^q^2>,<7,a^q>,<5,a>>,
      -4 : elt<G|<9,-a^q^3>,<8,-a^q>,<10,-a>>,
      -5 : elt<G|<11,a>>,
      -6 : elt<G|<12,a>>,
     default : false>;
    end function;
  elif ttp eq "2E6" then
    N := 36;
    x := function(i,a)
    return case< i | 
       1 : elt<G|<N+2,a>>,
       2 : elt<G|<N+4,a>>,
       3 : elt<G|<N+5,-a^q>,<N+3,-a>>,
       4 : elt<G|<N+6,a^q>,<N+1,a>>,
       5 : elt<G|<N+8,a>>,
       6 : elt<G|<N+10,a^q>,<N+9,a>>,
       7 : elt<G|<N+11,a^q>,<N+7,a>>,
       8 : elt<G|<N+15,-a>>,
      -1 : elt<G|<2,a>>,
      -2 : elt<G|<4,a>>,
      -3 : elt<G|<5,-a^q>,<3,-a>>,
      -4 : elt<G|<6,a^q>,<1,a>>,
      -5 : elt<G|<8,a>>,
      -6 : elt<G|<10,a^q>,<9,a>>,
      -7 : elt<G|<11,a^q>,<7,a>>,
      -8 : elt<G|<15,-a>>,
     default : false >;
   end function;
  else
    error "Not available for type",ttp;
  end if;
  return x;
end function;

rootNorms := function(tp)
  if tp eq "3D4" then
    return [2,1,1,1,2,2];
  elif tp eq "2E6" then
    return [2,2,1,1,2,1,1,2];
  else
    error "Not available for",tp;
  end if;
end function;

tContravariantFormSpace := function(rho)
  G := Domain(rho);
  F := BaseRing(G);
  F0 := DefRing(G);
  basis := [Basis(F),Basis(F0)];
  RD := RootDatum(G);
  nm := CartanName(RD);
  twist := TwistingDegree(RD);
  ttp := IntegerToString(twist) * nm;
  x := steinbergSymbol(G);
  z := obverseSymbol(G);
  norms := rootNorms(ttp);
  r := RelativeRank(RD);
  Y := [ rho(x(i,a)) : a in basis[norms[i]], i in [1..r] ];
  Ym := [ rho(x(-i,a)) : a in basis[norms[i]], i in [1..r] ];
  Z := [ rho(z(i,a)) : a in basis[norms[i]], i in [1..r] ];
  Zm := [ rho(z(-i,a)) : a in basis[norms[i]], i in [1..r] ];
  I := Codomain(rho);
  M := GModule(sub< I | [g : g in Y cat Ym ] >);
  D := GModule(sub< I | [Transpose(g) : g in Z cat Zm ] >);
  return AHom(M,D), M, D;
end function;

uContravariantFormSpace := function(rho)
  G := Domain(rho);
  F := BaseRing(G);
  B := Basis(F);
  RD := RootDatum(G);
  ell := Rank(RD); // "SemisimpleRank(G)"
  N := NumPosRoots(RD);
  Y := [ rho(elt<G|<i,a>>) : a in B, i in [1..ell] ];
  Ym := [ rho(elt<G|<N+i,a>>) : a in B, i in [1..ell] ];
  I := Codomain(rho);
  M := GModule(sub< I | [g : g in Y cat Ym ] >);
  D := GModule(sub< I | [Transpose(g) : g in Ym cat Y ] >);
  return AHom(M,D), M, D;
end function;


//==============================================================================
intrinsic ContravariantFormSpace(rho::Map[GrpLie,GrpMat])
 -> ModMatGrp, ModGrp, ModGrp
{The space of contravariant forms on the image of rho}
  F := BaseRing(Domain(rho));
  require Type(F) eq FldFin : "the base ring must be a finite field";
  formSpace := IsTwisted(Domain(rho)) select
    tContravariantFormSpace else uContravariantFormSpace;
  return formSpace(rho);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ContravariantForm(rho::Map[GrpLie,GrpMat]) -> AlgMatElt
{The contravariant form for the image of the matrix
 representation rho of a group of Lie type}
  if assigned rho`ContravariantForm then return rho`ContravariantForm; end if;
  E := ContravariantFormSpace(rho);
  K := BaseRing(E);
  n := Dimension(Codomain(rho));
  A := MatrixAlgebra(K,n);
  B := Basis(E);
  b := #B;
  vprint Weights,1 : "Contravariant form space dimension =",b;

  if b eq 1 then
    rho`ContravariantForm := A!B[1];
    return rho`ContravariantForm;
  end if;

  if Characteristic(K) eq 2 then
    Q := Matrix(K,b,b,[Coordinates(E,Transpose(J)) : J in B]);
    Z := Eigenspace(Q,1);
    Bsym := [ &+[ Eltseq(Z.j)[i]*Matrix(B[i]) : i in [1..b]] : j in [1..Dimension(Z)]];
  else
    B := [Matrix(J) : J in B];
    Bsym := {@ @};
    for J in B do
      JT := Transpose(J);
      if J eq JT then
        Include(~Bsym,J);
      else
        Jsym := J + JT;
        if Jsym ne 0 then Include(~Bsym,Jsym); end if;
      end if;
    end for;
    Bsym := Basis(sub<E|Bsym>);
  end if;
  if #Bsym eq 1 then
    rho`ContravariantForm := A!Bsym[1];
    return rho`ContravariantForm;
  end if;

  Bsym := [ J : J in Bsym | Rank(J) ne 1 ];
  ranks := { Rank(J) : J in Bsym } diff {n};
  if not IsEmpty(ranks) then
    ndx := Index([Rank(J) : J in Bsym], Min(ranks));
    rho`ContravariantForm := A!Bsym[ndx];
    return rho`ContravariantForm;
  end if;
  C := Matrix(Bsym[1]*Bsym[2]^-1);
  evs := Eigenvalues(C);
  if not IsEmpty(evs) then
    c := Rep(evs)[1];
    J := Bsym[1] - c*Bsym[2];
    rho`ContravariantForm := A!J;
    return rho`ContravariantForm;
  else
    error "Contravariant form not found";
  end if;
end intrinsic;
//------------------------------------------------------------------------------

orbits := AssociativeArray();
orbits["D4"] := [[2],[4,3,1]];
orbits["E6"] := [[2],[4],[3,5],[1,6]];

tFrameBase := function(R, lambda) 
 C := ChangeRing(CartanMatrix(R),Rationals());
 tp := CartanName(R);
 pi := orbits[tp];
 n := #pi;

 wts := [ lambda ];
 ndx := 1;
 action := [[]];
 K := [1..n];
 J := [k : k in K | forall{s : s in pi[k] | lambda[s] eq 0} ];
 Q := [K,J];
 T := { k : k in K | k notin J };
 while not IsEmpty(J) do
   if exists(r,mu){ <r,mu> : r in T | 
     exists{ j : j in J | exists{ s : s in pi[j] | mu[s] ne 0} }
     where mu is wts[ndx] - &+[wts[ndx][s]*C[s] : s in pi[r]]} then

     Append(~wts,mu);
     Append(~action, Append(action[ndx],r));
     K := J;
     J := [j : j in J | forall{s : s in pi[j] | mu[s] eq 0} ];
     Append(~Q,J);
     Exclude(~T,r);
   else
     ndx +:= 1;
     T := { k : k in K | k notin J };
   end if;
 end while;
 return wts, action, Q;
end function;

uFrameBase := function(R, lambda)
 n := Rank(R); // Semisimple rank
 C := ChangeRing(CartanMatrix(R),Rationals());

 wts := [ lambda ];
 j := 1;
 S := CoxeterGroup(GrpFPCox,R);
 action := [One(S)];
 K := [1..n];
 J := [s : s in K | lambda[s] eq 0];
 Q := [K,J];
 T := { s : s in K | s notin J };
 while not IsEmpty(J) do
   if exists(r,mu){ <r,mu> : r in T | exists{ s : s in J | mu[s] ne 0 }
     where mu is wts[j] - wts[j][r]*C[r]} then

     Append(~wts,mu);
     Append(~action,action[j]*S.r);
     K := J;
     J := [s : s in J | C[r,s] eq 0];
     Append(~Q,J);
     Exclude(~T,r);
   else
     j +:= 1;
     T := { s : s in K | s notin J };
   end if;
 end while;
 return wts, action, Q;
end function;


//==============================================================================
intrinsic FrameBase(R::RootDtm, lambda::ModTupFldElt) -> SeqEnum,SeqEnum,SeqEnum
{Construct a frame base for the root datum R and weight
 vector lambda in the root lattice}
  require not IsZero(lambda) : "the weight should be nonzero";
  frameBase := IsTwisted(R) select tFrameBase else uFrameBase;
  return frameBase(R,lambda);
 end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic FrameBase(R::RootDtm, lambda::SeqEnum) -> SeqEnum,SeqEnum,SeqEnum
{"} // "
  return FrameBase(R,Vector(Rationals(),lambda));
end intrinsic;
//------------------------------------------------------------------------------

dominantWt := function( R, lambda : J := [1..Rank(R)] )
  C := ChangeRing(CartanMatrix(R),Rationals());
  S := CoxeterGroup(GrpFPCox,R);
  w := One(S);
  while exists(i){ i : i in J | lambda[i] lt 0 } do
    w *:= S.i;
    lambda -:= lambda[i]*C[i];
  end while;
  return lambda, w;
end function;

uWtOrbit := function(R,lambda : J := [1..Rank(R)])
 C := ChangeRing(CartanMatrix(R),Rationals());
 S := CoxeterGroup(GrpFPCox,R);
 if IsZero(lambda) then return {@ lambda @}, [Id(S)]; end if;

 lambda := dominantWt(R,lambda : J := J);
 current := {@ lambda @};
 thisAction := [ One(S) ];
 T := {@ @};  A := [ ];
 repeat
   previous := current;
   T join:= current;
   current := {@ @};
   lastAction := thisAction;
   A cat:= thisAction;
   thisAction := [ ];
   for k := 1 to #previous do
     mu := previous[k];
     K := { j : j in J | mu[j] lt 0 };
     for i in J do
       if mu[i] gt 0 and forall{ j : j in K | j lt i or mu[j] ge C[i,j]*mu[i] } then
         Include(~current, mu - mu[i]*C[i]);
         Append(~thisAction, lastAction[k]*S.i);
       end if;
     end for;
   end for;
 until IsEmpty(current);
 return T, A;
end function;

tWtOrbit := function(R,lambda : J := [1..RelativeRank(R)])
 C := ChangeRing(CartanMatrix(R),Rationals());
 tp := CartanName(R);
 pi := orbits[tp];
 T := {@ lambda @};  A := [ [] ];
 if IsZero(lambda) then return T, A; end if;
 ndx := 0;
 while ndx lt #T do
   ndx +:= 1;
   xi := T[ndx];
   s := A[ndx];
   for j in J do
     orb := pi[j];
     mu := xi;
     for i in orb do mu -:= mu[i]*C[i]; end for;
     if mu notin T then
       Include(~T,mu);
       Append(~A, Append(s,j));
     end if;
   end for;
 end while;
 return T, A;
end function;

uUnipotentFixedSpace := function(rho)
  L := Domain(rho);
  ell := SemisimpleRank(L);
  B := Basis(BaseRing(L));
  X := [ rho(elt<L|<i,b>>) : b in B, i in [1..ell] ];
  E := &meet[Eigenspace(u,1) : u in X];
  if Dimension(E) gt 1 then
    pos := PositiveRoots(L : Basis := "Root");
    ndx := [ i : i in [ell+1..#pos] | #Support(pos[i]) eq 2 ];
    for j in ndx do
      E meet:= &meet[ Eigenspace(rho(elt<L|<j,b>>),1) : b in B ];
      if Dimension(E) eq 1 then break; end if;
    end for;
  end if;
  return E;
end function;

tUnipotentFixedSpace := function(rho)
  G := Domain(rho);
  RD := RootDatum(G);
  r := RelativeRank(RD);
  F := BaseRing(G);
  F0 := DefRing(G);
  basis := [Basis(F),Basis(F0)];
  nm := CartanName(RD);
  twist := TwistingDegree(RD);
  ttp := IntegerToString(twist) * nm;
  x := steinbergSymbol(G);
  norms := rootNorms(ttp);
  X := [ rho(x(i,a)) : a in basis[norms[i]], i in [1..r]];
  E := &meet[Eigenspace(u,1) : u in X];
  if Dimension(E) gt 1 then
    for j := r+1 to #norms do
      E meet:= &meet[ Eigenspace(rho(x(j,a)),1) : a in basis[norms[j]] ];
      if Dimension(E) eq 1 then break; end if;
    end for;
  end if;
  return E;
end function;


//==============================================================================
intrinsic UnipotentFixedSpace(rho::Map[GrpLie,GrpMat]) -> ModTupRng
{The space of fixed points of the unipotent radical of
 the standard Borel subgroup acting on the image of rho}
  if IsTwisted(Domain(rho)) then
    return tUnipotentFixedSpace(rho);
  else
    return uUnipotentFixedSpace(rho);
  end if;
end intrinsic;
//------------------------------------------------------------------------------

highestWeight2 := function(rho)
  G := Domain(rho);
  ell := SemisimpleRank(G);
  fixU := uUnipotentFixedSpace(rho);
  N := NumPosRoots(G);
  if Dimension(fixU) ne 1 then
    J := ContravariantForm(rho);
    V := VectorSpace(BaseRing(J),Nrows(J),J);
    R0 := NullSpace(J);
    pos := PositiveRoots(G : Basis := "Root");
    ndx := [ i : i in [1..N] | #Support(pos[i]) le 2 ];
    E := &meet[ Eigenspace(rho(elt<G|<N+j,1>>),1) : j in ndx ];
    assert exists(w){ w : w in fixU | w notin R0 and w notin E
      and InnerProduct(V!w,V!w) ne 0};
    lambda := [ (w*rho(elt<G|<N+i,1>>) - w in R0) select 0 else 1 : i in [1..ell]];
  else
    w := fixU.1;
    lambda := [ (w*rho(elt<G|<N+i,1>>) eq w) select 0 else 1 : i in [1..ell]];
  end if;
  return VectorSpace(Rationals(),ell)!lambda, w;
end function;

uHighestWeight := function(rho)
  G := Domain(rho);
  K := BaseRing(G);

  xi := PrimitiveElement(K);
  ell := SemisimpleRank(G);

  torus := [ Matrix(rho(TorusTerm(G,i,xi))) : i in [1..ell] ];
  fixU := uUnipotentFixedSpace(rho);

  if Dimension(fixU) ne 1 then
    J := ContravariantForm(rho);
    R0 := NullSpace(J);

    evals, spaces := TheWeightSpaces(torus : U := fixU);
    assert exists(r){ r : r in [1..#spaces] | spaces[r] notsubset R0 };
    eigenvals := evals[r];
    assert exists(w){ w : w in spaces[r] | w notin R0 };
  else
    w := fixU.1;
    R0 := sub<Generic(fixU)|0>;
    j := Depth(w); // the index of the first non-zero entry
    eigenvals := [ (w*torus[i])[j]*w[j]^-1 : i in [1..ell] ];
  end if;

  lambda := [Log(xi,K!x) : x in eigenvals];

  N := NumPosRoots(G);
  q0 := #K - 1;
  for i := 1 to ell do
    if lambda[i] eq 0 then
      g := rho(elt<G|<N+i,xi>>);
      if w^g - w notin R0 then lambda[i] := q0; end if;
    end if;
  end for;
  return VectorSpace(Rationals(),ell)!lambda, w;
end function;

theTorus := function(G)
  RD := RootDatum(G);
  F := BaseRing(G);
  F0 := DefRing(G);
  q := #F0;
  xi := PrimitiveElement(F);
  tp := CartanName(RD);
  twist := TwistingDegree(RD);
  ttp := IntegerToString(twist) * tp;
  if ttp eq "3D4" then
    eta := xi^(q^2+q+1);
    gens := [elt<G| Vector([F0| 1,eta,1,1])>,
           elt<G| Vector([F| xi,1,xi^q^2,xi^q]) >];
  elif ttp eq "2E6" then
    eta := xi^(q+1);
    gens := [ elt<G| Vector([F0| 1,eta,1,1,1,1]) >,
            elt<G| Vector([F0| 1,1,1,eta,1,1]) >,
            elt<G| Vector([F| 1,1,xi,1,xi^q,1]) >,
            elt<G| Vector([F| xi,1,1,1,1,xi^q]) > ];
  else
    error "not implemented for", ttp;
  end if;
  return gens;
end function;

tHighestWeight := function(rho)
  G := Domain(rho);
  torus := [ Matrix(rho(t)) : t in theTorus(G) ];
  fixU := tUnipotentFixedSpace(rho);

  if Dimension(fixU) ne 1 then
    J := ContravariantForm(rho);
    R0 := NullSpace(J);

    evals, spaces := TheWeightSpaces(torus : U := fixU);
    assert exists(r){ r : r in [1..#spaces] | spaces[r] notsubset R0 };
    eigenvals := evals[r];
    assert exists(w){ w : w in spaces[r] | w notin R0 };
  else
    w := fixU.1;
    R0 := sub<Generic(fixU)|>;
    j := Depth(w); // the index of the first non-zero entry
    eigenvals := [ (w*h)[j]*w[j]^-1 : h in torus ];
  end if;

  x := steinbergSymbol(G);
  tp := CartanName(G);
  twist := TwistingDegree(RootDatum(G));
  ttp := IntegerToString(twist) * tp;
  K := BaseRing(G);
  K0 := DefRing(G);
  q := #K0;
  Q := #K;
  xi := PrimitiveElement(K);
  eta := K0!(xi^((Q - 1) div (q-1)));

  adjustLong := function(i)
    mu := K0!eigenvals[i];
    if mu eq K0!1 then
      return w^rho(x(-i,eta)) - w notin R0 select q - 1 else 0;
    end if;
    return Log(eta,mu);
  end function;

  adjustShort := function(i)
    mu := K!eigenvals[i];
    if mu eq K!1 then
      return w^rho(x(-i,xi)) - w notin R0 select Q - 1 else 0;
    end if;
    return Log(xi,mu);
  end function;

  if ttp eq "3D4" then
    a2 := adjustLong(1);
    aa := Intseq(adjustShort(2),q) cat [0,0,0];
    a1 := aa[1];
    a4 := aa[2];
    a3 := aa[3];
    lambda := [a1,a2,a3,a4];

  elif ttp eq "2E6" then
    a2 := adjustLong(1);
    a4 := adjustLong(2);
    aC := Intseq(adjustShort(3),q) cat [0,0];
    aD := Intseq(adjustShort(4),q) cat [0,0];
    a3 := aC[1];
    a5 := aC[2];
    a1 := aD[1];
    a6 := aD[2];
    lambda := [a1,a2,a3,a4,a5,a6];
  else
    error "not implemented for", ttp;
  end if;
  return VectorSpace(Rationals(),SemisimpleRank(G))!lambda, w;
end function;


//==============================================================================
intrinsic HighestWeight(rho::Map[GrpLie,GrpMat]) -> ModTupRngElt, ModTupRngElt
{Highest weight and maximal vector}
  K := BaseRing(Domain(rho));
  require IsFinite(K) : "The base ring must be finite";
  if #K eq 2 then
    require K eq BaseRing(Codomain(rho)):
    "The representation must be over the base ring of the group";
    return highestWeight2(rho);
  end if;
  highwt := IsTwisted(Domain(rho)) select tHighestWeight else uHighestWeight;
  return highwt(rho);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic HighestWeight(tp::MonStgElt,rk::RngIntElt,q::RngIntElt,
  X::SeqEnum,Xm::SeqEnum : GS := false, Verify := false) 
  -> ModTupRngElt, ModTupRngElt
{"} // "
  if Verify then
    require CST_VerifyPresentation(tp,rk,q,X,Xm : GS := GS) :
      "verification failed";
  end if;
  if tp in {"3D", "2E"} then
    G := TwistedGroupOfLieType(tp,rk,q);
  else
    tprk := tp cat IntegerToString(rk);
    signsFG := func< tp | (tp eq "G") select [-1,1,1,1]
      else [1,1,1,1,-1,1,1,1,-1,-1,1,-1,-1,1,-1,-1,-1,-1,-1,-1] >;
    RD := GS and (tp in "FG")
        select RootDatum(tprk : Signs := signsFG(tp), Isogeny := "SC")
        else RootDatum(tprk : Isogeny := "SC");
    G := GroupOfLieType(RD,q);
  end if;
  return HighestWeight(Morphism(G,X,Xm : GS := GS));
end intrinsic;
//------------------------------------------------------------------------------

FrameRecord := recformat<
  wtBase : SeqEnum,    // "B"
  vecBase : SeqEnum,   // "vectB"
  wtOrbits : SeqEnum,  // "Orbits"
  vecOrbits : SeqEnum, // "vectOrbit"
  Weylgps : SeqEnum,   // "Ws"
  actions : SeqEnum,   // "Actions"
  w0J : SeqEnum,
  form : AlgMatElt >;  // "M"

uWtFrameData := procedure(rho)
 G := Domain(rho);
 R := RootDatum(G);

 lambda, v0 := HighestWeight(rho);
 orbit, action := uWtOrbit(R,lambda);
 vecOrbit := [ v0^rho(elt<G|a>) : a in action ];

 wtBase, act, Jchain := FrameBase(R,lambda);
 vecBase := [ v0^rho(elt<G|a>) : a in act ];
 k := #wtBase;

 W := CoxeterGroup(R);
 Weylgps := [ ReflectionSubgroup(W, J) : J in Jchain ];

 longelts := [LongestElement(Q) : Q in Weylgps];
 w0J := [longelts[i-1]^-1 * longelts[i] : i in [2..#longelts]];

 wtOrbits := [ orbit ];
 vecOrbits := [ vecOrbit ];
 actions := [ [Eltseq(a) : a in action] ];
 for i := 2 to k do
   orbit, action := uWtOrbit(R, wtBase[i] : J := Jchain[i]);
   Append( ~wtOrbits, orbit );
   Append( ~vecOrbits, [ vecBase[i]^rho(elt<G|a>) : a in action ] );
   Append( ~actions, [Eltseq(a) : a in action] );
 end for;

 rho`WeightFrame := rec< FrameRecord |
   wtBase := wtBase,
   vecBase := vecBase,
   wtOrbits := wtOrbits,
   vecOrbits := vecOrbits,
   Weylgps := Weylgps,
   actions := actions,
   w0J := w0J,
   form := ContravariantForm(rho) >;
end procedure;

tWtFrameData := procedure(rho)
  G := Domain(rho);
  R := RootDatum(G);
  tp := CartanName(R);
  twist := TwistingDegree(R);
  ttp := IntegerToString(twist) * tp;
  S := CoxeterGroup(GrpFPCox,tp);
  pi := [ &*[S.i : i in orb] : orb in orbits[tp] ];

  lambda, v0 := HighestWeight(rho);
  orbit, action_ := tWtOrbit(R,lambda);

  action := [ &*[S| pi[s] : s in a ] : a in action_ ];
  vecOrbit := [ v0^rho(elt<G|a>) : a in action ];

  wtBase, act_, Jchain := FrameBase(R,lambda);
  act := [ &*[S| pi[s] : s in a ] : a in act_ ];
  vecBase := [ v0^rho(elt<G|a>) : a in act ];
  k := #wtBase;

  W0 := case< ttp | "3D4" : CoxeterGroup(Matrix(2,2,[2,-3,-1,2])), 
               "2E6" : CoxeterGroup(GrpPermCox,"F4"),
        default : "not implemented for " * ttp>;
  Weylgps := [ ReflectionSubgroup(W0, J) : J in Jchain ];

  longelts := [LongestElement(Q) : Q in Weylgps];
  w0J := [longelts[i-1]^-1 * longelts[i] : i in [2..#longelts]];

  wtOrbits := [ orbit ];
  vecOrbits := [ vecOrbit ];
  actions := [ action_ ];
  for i := 2 to k do
    orbit, action_ := tWtOrbit(R, wtBase[i] : J := Jchain[i]);
    action := [ &*[S| pi[s] : s in a ] : a in action_ ];
    Append( ~wtOrbits, orbit );
    Append( ~vecOrbits, [ vecBase[i]^rho(elt<G|a>) : a in action ] );
    Append( ~actions, action_ );
  end for;

  rho`WeightFrame := rec< FrameRecord |
    wtBase := wtBase,
    vecBase := vecBase,
    wtOrbits := wtOrbits,
    vecOrbits := vecOrbits,
    Weylgps := Weylgps,
    actions := actions,
    w0J := w0J,
    form := ContravariantForm(rho) >;
end procedure;


//==============================================================================
intrinsic WeightFrameData(rho::Map[GrpLie,GrpMat]) -> Rec
{ Data needed for row reduction calculations }
 if not assigned rho`WeightFrame then
   if IsTwisted(Domain(rho)) then  tWtFrameData(rho); else uWtFrameData(rho); end if;
 end if;
 return rho`WeightFrame;
end intrinsic;
//------------------------------------------------------------------------------

weightBase := function( rho )
  if (not assigned rho`WeightBase_B) then
    r := WeightFrameData(rho);
    rho`WeightBase_B          := r`wtBase;
    rho`WeightBase_vectB      := r`vecBase;
    rho`WeightBase_vectOrbit  := r`vecOrbits[1];
    rho`WeightBase_Orbits     := r`wtOrbits;
    rho`WeightBase_J          := [];
    rho`WeightBase_Ws         := r`Weylgps;
    rho`WeightBase_Actions    := r`actions;
    rho`WeightBase_M          := r`form;
    rho`WeightBase_WeylMxs    := [];
  end if;
  return rho`WeightBase_B,
    rho`WeightBase_vectB,
    rho`WeightBase_vectOrbit,
    rho`WeightBase_Orbits,
    rho`WeightBase_J,               // NOT USED
    rho`WeightBase_Ws,
    rho`WeightBase_Actions,
    rho`WeightBase_M,
    rho`WeightBase_WeylMxs;         // NOT USED
end function;


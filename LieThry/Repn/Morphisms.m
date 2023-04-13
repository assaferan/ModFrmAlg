freeze;

/*
  Extracted from Morphisms.tex by MagmaCode 2.1 on Fri Oct 25 23:25:37 2019
 
  Morphisms and the row reduction algorithm for finite groups of Lie type

  October 2019 Don Taylor

  $Id: Morphisms.m 65981 2022-06-11 01:03:52Z don $
*/

import "../GrpLie/CST.m" : extendList, quotientAction;
import "Weights.m" : theTorus;
declare verbose Rewrite, 5;


//==============================================================================
intrinsic Internal_UntwistedMorphism(G::GrpLie,X::SeqEnum,Xm::SeqEnum :
   OnlySimple := false, GS := false, Verify := false) -> Map
{The homomorphism from the simply connected group G of Lie type
 to the group with generators X, Xm. If OnlySimple is true, the
 sequences X and Xm are indexed by the simple roots and their
 negatives; otherwise they are assumed to be in
 Curtis-Steinberg-Tits format.  If GS is true, the long and
 short simple roots for groups of type G2 need to be swapped.}

  RD := RootDatum(G);
  require IsSemisimple(RD) : "Root datum is not semisimple";
  require SimpleCoroots(RD) eq IdentityMatrix(Rationals(),Rank(RD)) :
    "Root datum of the group must be standard simply connected";
//  require IsSimplyConnected(RD) : "Root datum is not simply connected";

  F := BaseRing(G);
  rank := Rank(G);
  tp := CartanName(RD);

  if Verify then
    assert CST_VerifyPresentation(tp[1],rank,#F,X,Xm : GS := GS);
  end if;

  if GS and tp eq "G2" then
    tmp := X[1]; X[1] := X[2]; X[2] := tmp;
    tmp := Xm[1]; Xm[1] := Xm[2]; Xm[2] := tmp;
  end if;

  M := Parent(X[1][1]);

  W := WeylGroup(G);
  P := PositiveRoots(RD : Basis := "Root");
  N := #P;
  PW := PositiveRoots(RD : Basis := "Standard");
  coPW := PositiveCoroots(RD : Basis := "Standard");

  if OnlySimple then X, Xm := extendList(RD,X,Xm); end if;
  U := X[1..rank];
  r := rank;

  for i := rank+1 to N do
    if #Support(P[i]) eq 2 then
      r +:= 1;
      U[i] := X[r];
    end if;
  end for;

  EW := [X[i][1]*Xm[i][1]^-1*X[i][1] : i in [1..rank]]; // Extended Weyl group
  ndx := {@ i : i in [1..N] | #Support(P[i]) le 2 @};

  for i := rank+1 to N do
    if i notin ndx then
      w := [];
      k := i;
      while k notin ndx do
        gamma := PW[k];
        j := rep{ j : j in [1..rank] | InnerProduct(coPW[j],gamma) gt 0 };
        Append(~w,j);
        k := k^W.j;
      end while;
      Q := U[k];
      for j in Reverse(w) do
        Q := [ A^EW[j] : A in Q ];
        if LieConstant_eta(RD,j,k) lt 0 then
          Q := [A^-1 : A in Q ];
        end if;
      end for;
      U[i] := Q;
    end if;
    Include(~ndx,i);
  end for;

  df := Degree(F);
  x := function(i,a) // a is never 0
    error if i lt -rank, "Unexpected index",i;
    v := Eltseq(a);
    ChangeUniverse(~v,Integers());
    if i lt 0 then
      return &*[ Xm[-i][j]^v[j] : j in [1..df] | v[j] ne 0 ];
    else
      return &*[ U[i][j]^v[j] : j in [1..df] | v[j] ne 0 ];
    end if;
  end function;

  h := func< i, t | EW[i]^-1 * x(i,t) * x(-i,-t^-1) * x(i,t) >;

  multByTorus := procedure(~ret, term)
    vprint Rewrite, 3: "multByTorus";
    for i := 1 to rank do
      ret *:= h(i, term[i]);
    end for;
  end procedure;

  multByUnipTerm := procedure(~ret, term)
    vprint Rewrite, 3: "multByUnipTerm";
    i, a := Explode(term);
    ret *:= x(i,a);
  end procedure;

  f := function( el )
    g := Unnormalise( el );
    list := g`List;
    ret := M!1;
    for item in list do
      if Type(item) eq SeqEnum then
        for term in item do
          multByUnipTerm( ~ret, term );
        end for;
      elif Type(item) eq ModTupFldElt then
        multByTorus( ~ret, item );
      elif Type(item) eq RngIntElt then
        ret *:= EW[item];
      else
        error "item has type", Type(item);
      end if;
    end for;
    return M!ret;
  end function;
  ret := hom< G -> M | x :-> f(x) >;
  ret`IsProjectiveRepresentation := false;
  return ret;
end intrinsic;
//------------------------------------------------------------------------------

unip3D4 := [
  <true, 2, 1, -1>, <false, 1, 2, 1>, <true, 2, 1, -1>, <true, 2, 1, -1>,
  <true, 3, 5, 1>, <true, 3, 5, 1>, <true, 3, 5, 1>, <true, 4, 10, -1>,
  <true, 4, 10, -1>, <true, 4, 10, -1>, <false, 5, 11, 1>, <false, 6, 12, 1>];

torus3D4 := [2,1];

weyl3D4 := [true, false];

unip2E6 := [
  <true, 4, 1, 1>, <false, 1, 2, 1>, <true, 3, 3, -1>, <false, 2, 4, 1>,
  <true, 3, 3, -1>, <true, 4, 1, 1>, <true, 7, 7, 1>, <false, 5, 8, 1>,
  <true, 6, 9, 1>, <true, 6, 9, 1>, <true, 7, 7, 1>, <true, 10, 12, 1>,
  <true, 8, 13, -1>, <true, 8, 13, -1>, <false, 9, 15, -1>, <true, 10, 12, 1>,
  <true, 12, 17, -1>, <true, 13, 18, -1>, <false, 11, 19, -1>, <true, 12, 17, -1>,
  <true, 13, 18, -1>, <true, 15, 22, -1>, <false, 16, 23, 1>, <false, 14, 24, 1>,
  <true, 15, 22, -1>, <true, 17, 26, -1>, <false, 18, 27, -1>, <true, 17, 26, -1>,
  <true, 19, 29, -1>, <false, 20, 30, -1>, <true, 19, 29, -1>, <true, 21, 32, -1>,
  <true, 21, 32, -1>, <false, 22, 34, 1>, <false, 23, 35, 1>, <false, 24, 36, 1>];

unip2E6GS := [
  <true, 4, 1, 1>, <false, 1, 2, 1>, <true, 3, 3, -1>, <false, 2, 4, 1>,
  <true, 3, 3, -1>, <true, 4, 1, 1>, <true, 7, 7, 1>, <false, 5, 8, 1>,
  <true, 6, 9, 1>, <true, 6, 9, 1>, <true, 7, 7, 1>, <true, 10, 12, 1>,
  <true, 8, 13, -1>, <true, 8, 13, -1>, <false, 9, 15, 1>, <true, 10, 12, 1>,
  <true, 12, 17, -1>, <true, 13, 18, -1>, <false, 11, 19, 1>, <true, 12, 17, -1>,
  <true, 13, 18, -1>, <true, 15, 22, -1>, <false, 16, 23, -1>, <false, 14, 24, -1>,
  <true, 15, 22, -1>, <true, 17, 26, -1>, <false, 18, 27, 1>, <true, 17, 26, -1>,
  <true, 19, 29, -1>, <false, 20, 30, 1>, <true, 19, 29, -1>, <true, 21, 32, -1>,
  <true, 21, 32, -1>, <false, 22, 34, -1>, <false, 23, 35, -1>, <false, 24, 36, -1>];

torus2E6 := [2,4,3,1];

weyl2E6 := [true, true, false, true];

restrictWeylWords := function(T)
  R := RootDatum(T);
  ttp := IntegerToString(TwistingDegree(R)) * CartanName(R);
  case ttp :
    when "2E6" :
      C := CoxeterGroup("E6");
      C0 := CoxeterGroup("F4");
      psi := hom< C0 -> C | C0.1 -> C.2, C0.2 -> C.4,
                        C0.3 -> C.3*C.5, C0.4 -> C.1*C.6 >;
    when "3D4" :
      C := CoxeterGroup("D4");
      C0 := CoxeterGroup("G2");
      psi := hom< C0 -> C | C0.1 -> C.2, C0.2 -> C.1*C.3*C.4 >;
    else error "Not implemented for type", ttp;
  end case;
  return func< wd | PermToWord(C0,WordToPerm(C,wd) @@ psi) >;
end function;

ChevalleyFnsFromRtDtm := function(RD,q,X,Xm : WeylAction := false)
  error if not IsTwisted(RD), "the root datum is not twisted";
  relRank := RelativeRank(RD);
  twist := TwistingDegree(RD);
  name := CartanName(RD);
  case name[1]:
    when "A":
      tp := "C" * IntegerToString(relRank);
      R0 := RootDatum(tp : Isogeny := "SC");
    when "D":
      if twist eq 3 then
        R0 := RootDatum(Matrix(2,2,[2,-3,-1,2]),Matrix(2,2,[1,0,0,1]));
      else
        tp := "B" * IntegerToString(relRank);
        R0 := RootDatum(tp : Isogeny := "SC");
      end if;
    when "E":
      R0 := RootDatum("F4" : Isogeny := "SC");
    else
      error "not implemented for type", name;
  end case;

  W := CoxeterGroup(R0);
  P := PositiveRoots(R0 : Basis := "Root");
  N := #P;
  PW := PositiveRoots(R0 : Basis := "Standard");
  coPW := PositiveCoroots(R0 : Basis := "Standard");

  K0 := GF(q);
  K := GF(q^twist);

  U := X[1..relRank];
  r := relRank;
  for i := relRank+1 to N do
    if #Support(P[i]) eq 2 then
      r +:= 1;
      U[i] := X[r];
    end if;
  end for;

  EW := [X[i][1]*Xm[i][1]^-1*X[i][1] : i in [1..relRank]];
  ndx := {@ i : i in [1..N] | #Support(P[i]) le 2 @};

  for i := relRank+1 to N do
    if i notin ndx then
      w := [];
      m := i;
      while m notin ndx do
        gamma := PW[m];
        j := rep{ j : j in [1..relRank] | InnerProduct(coPW[j],gamma) gt 0 };
        Append(~w,j);
        m := m^W.j;
      end while;
      Q := U[m];
      for j in Reverse(w) do
        Q := [ A^EW[j] : A in Q ];
        if LieConstant_eta(RD,j,m) lt 0 then
          Q := [A^-1 : A in Q ];
        end if;
      end for;
      U[i] := Q;
    end if;
    Include(~ndx,i);
  end for;

  degK := Degree(K);
  x := function(i,a) // a is never 0
    error if i lt -relRank, "Unexpected index",i;

    df := #U[Abs(i)];
    v := (df eq degK) select Eltseq(K!a) else Eltseq(K0!a);
    ChangeUniverse(~v,Integers());
    if i lt 0 then
      return &*[ Xm[-i][j]^v[j] : j in [1..df] | v[j] ne 0 ];
    else
      return &*[ U[i][j]^v[j] : j in [1..df] | v[j] ne 0 ];
    end if;
  end function;

  n := func< i,t | x(i,t)*x(-i,-t^-1)*x(i,t) >;
  h := func< i, t | EW[i]^-1 * n(i,t) >;

  if WeylAction then
    ndx := {@ i : i in [1..relRank] @};
    action := [< i, Id(Parent(EW[1])) > : i in [1..relRank] ];
    for i := relRank+1 to N do
      w := [];
      m := i;
      while m notin ndx do
        gamma := PW[m];
        j := rep{ j : j in [1..relRank] | InnerProduct(coPW[j],gamma) gt 0 };
        Append(~w,j);
        m := m^W.j;
      end while;
      r, s := Explode(action[m]);
      for j in Reverse(w) do s *:= EW[j]; end for;
      action[i] := <r,s>;
      Include(~ndx,i);
    end for;
  else
    action := [];
  end if;

  return x, h, n, EW, action;
end function;

ChevalleyFnsFromGrp := function(G : WeylAction := false, GS := false) 
  X,Xm := LieTypeGenerators(G : GS := GS);
  Y := [[G!g : g in root] : root in X ];
  Ym := [[G!g : g in root] : root in Xm ];
  return ChevalleyFnsFromRtDtm(RootDatum(G),#DefRing(G),Y,Ym : 
    WeylAction := WeylAction);
end function;


//==============================================================================
intrinsic Internal_TwistedMorphism(G::GrpLie,X::SeqEnum,Xm::SeqEnum
  : GS := false) -> Map
{The homomorphism from the twisted simply connected group G of Lie
 type to the group with generators X, Xm.}

  require IsTwisted(G) : "the group is not twisted";
  RD := RootDatum(G);
  twist := TwistingDegree(RD);
  ttp := IntegerToString(twist) * CartanName(RD);
  relRank := RelativeRank(RD);

  k := DefRing(G);
  K := BaseRing(G);
  M := Parent(X[1][1]);

  relUnipData :=  (GS and ttp eq "2E6") select unip2E6GS else  
    case< ttp | "3D4" : unip3D4, "2E6" : unip2E6, default : [] >;
  relTorusData := case< ttp | "3D4" : torus3D4, "2E6" : torus2E6, default : [] >;
  relWeylData := case< ttp | "3D4" : weyl3D4, "2E6" : weyl2E6, default : [] >;

  x, h, n, EW := ChevalleyFnsFromRtDtm(RD,#k,X,Xm);

  multByTorus := procedure(~ret, vec)
    vprint Rewrite, 3: "multByTorus";
    for i := 1 to relRank do
      ret *:= h(i, vec[relTorusData[i]]);
    end for;
  end procedure;

  multByUnipTerm := procedure(~ret, term)
    vprint Rewrite, 3: "multByUnipTerm";
    i, a := Explode(term);
    ret *:= x(i,a);
  end procedure;

  getnext := procedure(~ndx,~term,item)
    term := item[ndx]; ndx +:= 1;
    i, a := Explode(term);
    flag, j, r, sign := Explode(relUnipData[i]);
    if i eq r then term := <j,sign*a>; end if;
    if flag then
      for s := 2 to twist do
        prev := r;
        tt := item[ndx]; ndx +:= 1;
        i, a := Explode(tt);
        flag, j, r, sign := Explode(relUnipData[i]);
        assert flag;
        assert r eq prev;
        if i eq r then term := <j,sign*a>; end if;
      end for;
    end if;
  end procedure;

  rho := restrictWeylWords(G);

  f := function( el )
    ret := M!1;
    xu,xh,xw,xup := Bruhat(el);

    if xu ne 1 then
      ux := Unnormalise(xu);
      item := ux`List[1];
      ndx := 1;
      while ndx le #item do
        getnext(~ndx,~term,item);
        multByUnipTerm( ~ret, term );
      end while;
    end if;

    if xh ne 1 then
      hx := Unnormalise(xh);
      item := hx`List[1];
      multByTorus( ~ret, item );
    end if;

    if xw ne 1 then
      vprint Rewrite, 3: "multByWeylTerm";
      wx := Unnormalise(xw);
      item := rho([i : i in wx`List]);
      for j in item do
        ret *:= relWeylData[j] select EW[j] else EW[j]^-1;
      end for;
    end if;

    if xup ne 1 then
      upx := Unnormalise(xup);
      item := upx`List[1];
      ndx := 1;
      while ndx le #item do
        getnext(~ndx,~term,item);
        multByUnipTerm( ~ret, term );
      end while;
    end if;

    return M!ret;
  end function;
  return hom< G -> M | x :-> f(x) >;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Morphism(G::GrpLie,X::SeqEnum,Xm::SeqEnum :
   OnlySimple := false, GS := false, Verify := false) -> Map
{The homomorphism from the simply connected group G of Lie type
 to the group with generators X, Xm. If OnlySimple is true, the
 sequences X and Xm are indexed by the simple roots and their
 negatives; otherwise they are assumed to be in
 Curtis-Steinberg-Tits format.  If GS is true, the long and
 short simple roots for groups of type G2 need to be swapped.}
  if IsTwisted(G) then
    return Internal_TwistedMorphism(G,X,Xm : GS := GS);
  else
    return Internal_UntwistedMorphism(G,X,Xm : GS := GS, 
      OnlySimple := OnlySimple, Verify := Verify);
  end if;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic PapiOrder(W::GrpPermCox, wd::SeqEnum[RngIntElt]) -> SeqEnum
{An additive order for the set of positive roots sent
 negative by word wd^-1}
  if IsEmpty(wd) then return []; end if;
  r := #wd;
  refs := [W.i : i in [1..Ngens(W)]];
  P := [ wd[r] ];
  s := One(W);
  for i := r-1 to 1 by -1 do
    s := refs[wd[i+1]]*s;
    Append(~P,wd[i]^s);
  end for;
  return P;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic PapiOrder(W::GrpPermCox, w::GrpPermElt) -> SeqEnum
{An additive order for the set of positive roots sent
 negative by w^-1}
  return PapiOrder(W,PermToWord(W,w));
end intrinsic;
//------------------------------------------------------------------------------

torusGenerators := function(G)
  F := BaseRing(G);
  d := ReductiveRank(G);
  s := [F| 1 : i in [1..d]];
  s[1] := PrimitiveElement(F);
  gens := [Rotate(s,i) : i in [0..d-1]];
  return [elt<G| Vector(F,g) > : g in gens];
end function;


//==============================================================================
intrinsic TorusWord(rho::Map[GrpLie,GrpMat], A0::GrpMatElt)
    -> SeqEnum, ModTupFldElt
{ Return a torus element h of the domain of rho such that
  rho(h)^-1*A0 is a scalar matrix }

  G := Domain(rho);
  K := BaseRing(G);

  if #K eq 2 then
    if IsScalar(A0) then return [G!1], A0[1,1]; else return [],_; end if;
  end if;

  C := Codomain(rho);
  F := BaseRing(C);

  flag, A0 := IsCoercible(C,A0);
  require flag : "cannot coerce the matrix into the codomain";

  torus := [Matrix(rho(g)) : g in torusGenerators(G)];
  evals, spaces := TheWeightSpaces(torus);
  require forall{ e : e in &cat evals | IsCoercible(K,e) } :
    "cannot coerce the torus eigenvalues into the base ring";

  if Degree(F) lt Degree(K) then
    F := K;
    flag, A := IsCoercible(GL(Dimension(C),K),A0);
    require flag : "cannot write the matrix over the base field";
  else
    A := A0;
  end if;

  zeta := PrimitiveElement(F);
  q0 := #K - 1;
  c := (#F - 1) div q0;
  xi := K!(zeta^c);

  d := ReductiveRank(G);
  m := #evals;
  eigenvecs := [E.1 : E in spaces];

  wts := [Vector([Log(xi,K!evals[i][j]): j in [1..d]]) : i in [1..m]];

  B0 := Matrix(wts);

  V := Universe(eigenvecs);
  if not forall{ i : i in [1..m] | v*A in sub<V|v> where v is eigenvecs[i] } then
    return [],_;
  end if;

  eigA := [(v*A)[j]*v[j]^-1 : i in [1..m] | true 
      where j is Depth(v) where v is eigenvecs[i]];

  for i := 1 to m do
    if not forall{ v : v in Basis(spaces[i]) | v*A eq eigA[i]*v } then return [],_; end if;
  end for;

  eeA := [Log(zeta,e) : e in eigA ];

  getWord := function( : Scalars := false)
    if Scalars then
      if IsScalar(A) then return [G!1], A[1,1]; end if;
      B := Matrix([B0[i-1] - B0[i] : i in [2..m]]);
      ee := [ eeA[i-1]-eeA[i] : i in [2..m]];
    else
      B := B0;
      ee := eeA;
    end if;

    if (c ne 1) then
      if exists{ e : e in ee | e mod c ne 0 } then return [], _; end if;
      ee := [ e div c : e in ee ];
    end if;
    aa := Vector(ee);

    S, P, Q := SmithForm(Transpose(B));
    avec := aa*Q;
    soln := [[]];
    for i := 1 to d do
      r, s := Solution(S[i,i],avec[i],q0);
      if r eq -1 then return [], _; end if;
      flag, k := IsDivisibleBy(q0,s);
      assert flag;
      soln_ := soln;
      soln := [];
      for j := 0 to k-1 do
        for ans in soln_ do Append(~soln, Append(ans,r+s*j)); end for;
      end for;
    end for;
    for z in soln do
      x := Vector(z)*P;
      h := elt<G | Vector([ xi^x[i] : i in [1..d] ]) >;
      if Scalars then
        Z := A0*rho(h)^-1;
        if IsScalar(Z) then return [h],Z[1,1]; end if;
      elif rho(h) eq A0 then return [h],BaseRing(C)!1; end if;
    end for;
    return [],_;
  end function;

  wd, z := getWord();
  if IsNull(wd) then
     wd, z := getWord( : Scalars);
     if IsNull(wd) then return [], _; end if;
  end if;
  return wd, z;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Internal_PreChevalleyForm( rho::Map[GrpLie,GrpMat], A0::GrpMatElt )
  -> SeqEnum, GrpMatElt, MonStgElt
{The Chevalley normal form of the inverse image of A0}
  C := Codomain(rho);
  flag, A := IsCoercible(C,A0);
  require flag : "cannot coerce the matrix into the codomain";
  G := Domain(rho);
  R := RootDatum(G);
  K := BaseRing(G);
  N := NumPosRoots(R);

  wdot := [ rho(elt<G|gamma>) : gamma in [1..N] ];
// work around for old elt<G|i> bug
//  wdot := [ (Characteristic(K) eq 2 and gamma le N) select
//    &*[ rho(elt<G|i>) : i in ReflectionWord(R,gamma)] else rho(elt<G|gamma>) : gamma in [1..N]];

  r := WeightFrameData(rho);
  W := r`Weylgps[1];
  V := VectorSpace(BaseRing(C),Dimension(C),r`form);
  u := G!1; w := G!1; vs := []; ds := [];
  k := #r`wtBase;
  for j := 1 to k do
    vj := V!r`vecBase[j];
    Gamma := ChangeUniverse(r`vecOrbits[j],V);

    vjA := vj*A;
    if not exists(i){ i : i in [#Gamma .. 1 by -1] | InnerProduct(vjA,Gamma[i]) ne 0 } then
      return [], A, "cannot find a pivot";
    end if;
    vmu := Gamma[i];
    mu := r`wtOrbits[j][i];
    d := r`actions[j][i];

    v_ := G!1;
    for gamma in PapiOrder(W,d) do
      m := -Integers()!InnerProduct(mu,Coroot(R,gamma : Basis := "Root"));
      assert m ne 0;
      nu := wdot[gamma];
      b := K!(InnerProduct(vj*A,vmu*nu)/InnerProduct(vj*A,vmu));
      if b ne 0 then
        if not exists(a){ a : a in AllRoots(b,m) |
           InnerProduct(vj*A*rho(elt<G|<gamma,-a>>),vmu*nu) eq 0 }
        then
          return [], A, "cannot clear from the right";
        end if;
        v_ := elt<G|<gamma,a>>*v_;
        A *:= rho(elt<G|<gamma,-a>>);
      end if;
    end for;

    Append(~vs, v_);

    wj := r`w0J[j];
    lambda := r`wtBase[j];
    for gamma in PapiOrder(W,wj) do
      m := Integers()!InnerProduct(lambda,Coroot(R,gamma : Basis := "Root"));
      assert m ne 0;
      nu := wdot[gamma];
      b := K!(InnerProduct(vj*nu*A,vmu)/InnerProduct(vj*A,vmu));
      if b ne 0 then
        if IsOdd(m) then b := -b; end if;
        if not exists(a){ a : a in AllRoots(b,m) |
           InnerProduct(vj*nu*rho(elt<G|<gamma,-a>>)*A,vmu) eq 0 }
        then
          return [], A, "cannot clear from the left";
        end if;
        u *:= elt<G|<gamma,a>>;
        A := rho(elt<G|<gamma,-a>>)*A;
      end if;
    end for;

    D := IsEmpty(d) select G!1 else &*[elt<G|i> : i in d];
    Append(~ds, D);
    A *:= rho(D)^-1;
    w := D*w;
  end for;
  v := vs[k];
  for j := k-1 to 1 by -1 do v := v^ds[j] * vs[j]; end for;
  return [u,w,v],A,_;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Internal_UntwistedChevalleyForm( rho::Map[GrpLie,GrpMat], A::GrpMatElt )
  -> SeqEnum, FldFinElt
{The Chevalley normal form of the inverse image of A}
  wds, B, msg := Internal_PreChevalleyForm(rho,A);
  if IsNull(wds) then
    print msg;
    return [],_;
  end if;
  h, z := TorusWord(rho,B);
  if IsNull(h) then return [],_; end if;
  u,w,v := Explode(wds);
  return [u,h[1],w,v],z;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic RowReductionMap(rho::Map[GrpLie,GrpMat]) -> UserProgram
{ Returns a fuunction f such that for A in the codomain of rho, f(A) 
returns two values:a sequence w of length 0 or 1, and z.  If w is empty, 
then A is not in the image of rho extended by scalars and z is a message; 
otherwise z is a field element and w[1] is a Steinberg word in the domain 
of rho such that z * rho(w[1]) = A.}
  G := Domain(rho);
  C := Codomain(rho);
  R := RootDatum(G);
  K := BaseRing(G);
  N := NumPosRoots(R);

  wdot := [ (Characteristic(K) eq 2 and gamma le N) select
      &*[ rho(elt<G|i>) : i in ReflectionWord(R,gamma)] else rho(elt<G|gamma>) : gamma in [1..N]];

  r := WeightFrameData(rho);
  W := r`Weylgps[1];
  V := VectorSpace(BaseRing(C),Dimension(C),r`form);
  k := #r`wtBase;

  return function(A0)
    flag, A := IsCoercible(C,A0);
    error if not flag, "cannot coerce the matrix into the codomain";
    u := G!1; w := G!1; vs := []; ds := [];

    for j := 1 to k do
      vj := V!r`vecBase[j];
      Gamma := ChangeUniverse(r`vecOrbits[j],V);

      vjA := vj*A;
      if not exists(i){ i : i in [#Gamma .. 1 by -1] | InnerProduct(vjA,Gamma[i]) ne 0 } then
        return [], "cannot find a pivot";
      end if;
      vmu := Gamma[i];
      mu := r`wtOrbits[j][i];
      d := r`actions[j][i];

      v_ := G!1;
      for gamma in PapiOrder(W,d) do
        m := -Integers()!InnerProduct(mu,Coroot(R,gamma : Basis := "Root"));
        assert m ne 0;
        nu := wdot[gamma];
        b := K!(InnerProduct(vj*A,vmu*nu)/InnerProduct(vj*A,vmu));
        if b ne 0 then
          if not exists(a){ a : a in AllRoots(b,m) |
             InnerProduct(vj*A*rho(elt<G|<gamma,-a>>),vmu*nu) eq 0 }
          then
            return [], "cannot clear from the right";
          end if;
          g := elt<G|<gamma,a>>;
          v_ := g*v_;
          A *:= rho(g)^-1;
        end if;
      end for;
      Append(~vs,v_);

      wj := r`w0J[j];
      lambda := r`wtBase[j];
      for gamma in PapiOrder(W,wj) do
        m := Integers()!InnerProduct(lambda,Coroot(R,gamma : Basis := "Root"));
        assert m ne 0;
        nu := wdot[gamma];
        b := K!(InnerProduct(vj*nu*A,vmu)/InnerProduct(vj*A,vmu));
        if b ne 0 then
          if IsOdd(m) then b := -b; end if;
          if not exists(a){ a : a in AllRoots(b,m) |
             InnerProduct(vj*nu*rho(elt<G|<gamma,-a>>)*A,vmu) eq 0 }
          then
            return [], "cannot clear from the left";
          end if;
          g := elt<G|<gamma,a>>;
          u *:= g;
          A := rho(g)^-1*A;
        end if;
      end for;

      D := IsEmpty(d) select G!1 else elt<G| &*[W.i : i in d] >;
      Append(~ds,D);
      A *:= rho(D)^-1;
      w := D*w;
    end for;

    v := vs[k];
    for j := k-1 to 1 by -1 do
      v := v^ds[j]*vs[j];
    end for;

    h, z := TorusWord(rho,A);
    if IsNull(h) then
      return [], "no torus word";
    else
      return [u * h[1] * w * v], z;
    end if;
  end function;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic TwistedTorusWord(rho::Map[GrpLie,GrpMat], A0::GrpMatElt)
    -> SeqEnum, ModTupFldElt
{ Return a torus element h of the domain of rho such that
  rho(h)^-1*A_0 is a scalar matrix }

  G := Domain(rho);
  K := BaseRing(G);
  K0 := DefRing(G);
  q := #K0;
  C := Codomain(rho);
  F := BaseRing(C);

  flag, A0 := IsCoercible(C,A0);
  require flag : "cannot coerce the matrix into the codomain";

  T := theTorus(G);
  torus := [Matrix(rho(g)) : g in T];
  d := #T;
  evals, spaces := TheWeightSpaces(torus);
  require forall{ e : e in &cat evals | IsCoercible(K,e) } :
    "cannot coerce the torus eigenvalues into the base ring";

  if Degree(F) lt Degree(K) then
    F := K;
    flag, A := IsCoercible(GL(Dimension(C),K),A0);
    require flag : "cannot write the matrix over the base field";
  else
    A := A0;
  end if;

  zeta := PrimitiveElement(F);
  q1 := #K - 1;
  c := (#F - 1) div q1;
  xi := K!(zeta^c);

  m := #evals;
  eigenvecs := [E.1 : E in spaces];

  wts := [Vector([Log(xi,K!evals[i][j]): j in [1..d]]) : i in [1..m]];

  B0 := Matrix(wts);

  V := Universe(eigenvecs);
  if not forall{ i : i in [1..m] | v*A in sub<V|v> where v is eigenvecs[i] } then
    return [],_;
  end if;

  eigA := [(v*A)[j]*v[j]^-1 : i in [1..m] | true 
      where j is Depth(v) where v is eigenvecs[i]];

  for i := 1 to m do
    if not forall{ v : v in Basis(spaces[i]) | v*A eq eigA[i]*v } then return [],_; end if;
  end for;

  eeA := [ Log(zeta,e) : e in eigA ];

  getWord := function( : Scalars := false)
    if Scalars then
      if IsScalar(A) then return [G!1], A[1,1]; end if;
      B := Matrix([B0[i-1] - B0[i] : i in [2..m]]);
      ee := [ eeA[i-1]-eeA[i] : i in [2..m]];
    else
      B := B0;
      ee := eeA;
    end if;

    if (c ne 1) then
      if exists{ e : e in ee | e mod c ne 0 } then return [], _; end if;
      ee := [ e div c : e in ee ];
    end if;
    aa := Vector(ee);

    S, P, Q := SmithForm(Transpose(B));
    avec := aa*Q;
    if not forall{ i : i in [d+1..Ncols(avec)] | IsDivisibleBy(avec[i],q1) } then
      return [],_;
    end if;
    soln := [];
    for i := 1 to d do
      if i gt Nrows(S) or i gt Ncols(S) then
        r := 0;
      else
        r, s := Solution(S[i,i],avec[i],q1);
        if r eq -1 then return [], _; end if;
      end if;
      Append(~soln, r);
    end for;
    e := Vector(soln)*P;
    h := &*[ T[i]^e[i] : i in [1..d]];
    imh := &*[ torus[i]^e[i] : i in [1..d]];
    if Scalars then
      Z := A0*imh^-1;
      if IsScalar(Z) then 
        return [h],Z[1,1];
      end if;
    elif imh eq A0 then
      return [h],BaseRing(C)!1;
    end if;
    return [],_;
  end function;

  wd, z := getWord();
  if IsNull(wd) then
     wd, z := getWord( : Scalars);
     if IsNull(wd) then return [], _; end if;
  end if;
  return wd, z;

end intrinsic;
//------------------------------------------------------------------------------

ambientRoots :=  AssociativeArray();
ambientRoots["3D4"] := [[2],[1,4,3],[5,7,6],[10,8,9],[11],[12]];
ambientRoots["2E6"] := [
  [2],[4],[3,5],[1,6],[8],[9,10],[7,11],[13,14],[15],[12,16],[19],[17,20],
  [18,21],[24],[22,25],[23],[26,28],[27],[29,31],[30],[32,33],[34],[35],[36]];

relativePairing := function(R, mu, g, q)
  tp := IntegerToString(TwistingDegree(R)) * CartanName(R);
  eseq := ambientRoots[tp][g];
  m := 0; r := 1;

  for i := 1 to #eseq do 
    m +:= r*InnerProduct(mu,Coroot(R,eseq[i] : Basis := "Root"));
    r *:= q;
  end for;
  return Integers()!m;
end function;


//==============================================================================
intrinsic Internal_TwistedPreChevalleyForm(rho::Map[GrpLie,GrpMat],
   A0::GrpMatElt) -> SeqEnum, GrpMatElt, MonStgElt
{The Chevalley normal form of the inverse image of A0}
  C := Codomain(rho);
  flag, A := IsCoercible(C,A0);
  require flag : "cannot coerce the matrix into the codomain";
  G := Domain(rho);
  R := RootDatum(G);
  K<t> := BaseRing(G);
  xi := PrimitiveElement(K);
  K0 := DefRing(G);
  xi0 := PrimitiveElement(K0);
  field := [K,K0,K0];
  q := #K0;
  qe := #K;
  r := WeightFrameData(rho);

  W := r`Weylgps[1];
  rtNorm := ChangeUniverse(RootNorms(RootSystem(W)),Integers());
  x, h, n, EW, action := ChevalleyFnsFromGrp(G : WeylAction);

  wdot := func< gamma | &*[ rho(EW[i]) : i in ReflectionWord(W,gamma) ] >;
  V := VectorSpace(BaseRing(C),Dimension(C),r`form);
  u := G!1; w := G!1; vs := []; ds := [];
  k := #r`wtBase;
  for j := 1 to k do
    vj := V!r`vecBase[j];
    vjA := vj*A;
    Gamma := ChangeUniverse(r`vecOrbits[j],V);

    if not exists(i){ i : i in [#Gamma .. 1 by -1] | InnerProduct(vjA,Gamma[i]) ne 0 } then
        return [], A, "cannot find a pivot";
    end if;
    vmu := Gamma[i];
    mu := r`wtOrbits[j][i];
    d := r`actions[j][i];
    v_ := G!1;

vprint Rewrite, 2: "RIGHT",d;
    for g in PapiOrder(W,d) do
      nu := wdot(g);
      vmu_nu := vmu*nu;
      norm := rtNorm[g];
      F := field[norm];

      vjA := vj*A;
      b := InnerProduct(vjA,vmu_nu)/InnerProduct(vjA,vmu);
      if b ne 0 then
        flag, b := IsCoercible(F,b);
        if not flag then 
          return [],A,"cannot coerce b into the field of definition";
        end if;
        m := -relativePairing(R,mu,g,q);
        rts := AllRoots(b,m);
        if not exists(a){ a : a in rts |
             InnerProduct(vjA*rho(x(g,-a)),vmu_nu) eq 0 } then
          rts := AllRoots(-b,m);
          if not exists(a){ a : a in rts |
             InnerProduct(vjA*rho(x(g,-a)),vmu_nu) eq 0 } then
            return [], A, "cannot clear from the right";
          end if;
        end if;
vprint Rewrite, 2: "* Found *", b, a;
        v_ := x(g,a)*v_;
        A *:= rho(x(g,-a));
      end if;
    end for;

    Append(~vs, v_);

    wj := r`w0J[j];

vprint Rewrite, 2: "LEFT",PapiOrder(W,wj);

    lambda := r`wtBase[j];
    for g in PapiOrder(W,wj) do
vprint Rewrite, 2: "from the left. g =", g;
      gamma := Coroot(W,g : Basis := "Root");
      nu := wdot(g);
      vj_nu := vj*nu;
      norm := rtNorm[g];
      F := field[norm];
      vjA := vj*A;
      b := InnerProduct(vj_nu*A,vmu)/InnerProduct(vjA,vmu);
      if b ne 0 then
        flag, b := IsCoercible(F,b);
        if not flag then 
          return [],A,"cannot coerce b into the field of definition";
        end if;
        m := relativePairing(R,lambda,g,q);
        if IsOdd(m) then b := -b; end if;
        rts := AllRoots(b,m);
        if not exists(a){ a : a in rts |
             InnerProduct(vj_nu*rho(x(g,-a))*A,vmu) eq 0 } then
          rts := AllRoots(-b,m);
          if not exists(a){ a : a in rts |
             InnerProduct(vj_nu*rho(x(g,-a))*A,vmu) eq 0 } then
            return [], A, "cannot clear from the left";
          end if;
        end if;
vprint Rewrite, 2: "*Found*", b, a;
        u *:= x(g,a);
        A := rho(x(g,-a))*A;
      end if;
    end for;

    D := IsEmpty(d) select G!1 else &*[EW[i] : i in d];
    Append(~ds, D);
    A *:= rho(D)^-1;
    w := D*w;
  end for;
  v := vs[k];
  for j := k-1 to 1 by -1 do v := v^ds[j] * vs[j]; end for;
  return [u,w,v],A,_;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic Internal_TwistedChevalleyForm( rho::Map[GrpLie,GrpMat], A::GrpMatElt )
  -> SeqEnum, FldFinElt
{The Chevalley normal form of an inverse image of A}
  wds, B, msg := Internal_TwistedPreChevalleyForm(rho,A);
  if IsNull(wds) then
    print msg;
    return [],_;
  end if;
  h, z := TwistedTorusWord(rho,B);
  if IsNull(h) then return [],_; end if;
  u,w,v := Explode(wds);
  return [u,h[1],w,v],z;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic ChevalleyForm( rho::Map[GrpLie,GrpMat], A::GrpMatElt )
  -> SeqEnum, FldFinElt
{The Chevalley normal form of an inverse image of A}
  G := Domain(rho);
  if IsTwisted(G) then
    return Internal_TwistedChevalleyForm(rho,A);
  else
    return Internal_UntwistedChevalleyForm(rho,A);
  end if;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic TwistedRowReductionMap( rho::Map[GrpLie,GrpMat] ) -> UserProgram
{A projective inverse image of rho}
  C := Codomain(rho);
  G := Domain(rho);
  R := RootDatum(G);
  K<t> := BaseRing(G);
  xi := PrimitiveElement(K);
  K0 := DefRing(G);
  xi0 := PrimitiveElement(K0);
  field := [K,K0,K0];
  q := #K0;
  qe := #K;
  r := WeightFrameData(rho);

  W := r`Weylgps[1];
  rtNorm := ChangeUniverse(RootNorms(RootSystem(W)),Integers());
  x, h, n, EW, action := ChevalleyFnsFromGrp(G : WeylAction);

  wdot := func< gamma | &*[ rho(EW[i]) : i in ReflectionWord(W,gamma) ] >;
  V := VectorSpace(BaseRing(C),Dimension(C),r`form);
  k := #r`wtBase;

  return function(A0)
    flag, A := IsCoercible(C,A0);
    error if not flag, "cannot coerce the matrix into the codomain";
    u := G!1; w := G!1; vs := []; ds := [];

    for j := 1 to k do
      vj := V!r`vecBase[j];
      vjA := vj*A;
      Gamma := ChangeUniverse(r`vecOrbits[j],V);

      if not exists(i){ i : i in [#Gamma .. 1 by -1] | InnerProduct(vjA,Gamma[i]) ne 0 } then
          return [], "cannot find a pivot";
      end if;
      vmu := Gamma[i];
      mu := r`wtOrbits[j][i];
      d := r`actions[j][i];

      v_ := G!1;

vprint Rewrite, 2: "RIGHT",d;
      for g in PapiOrder(W,d) do
        gamma := Coroot(W,g : Basis := "Root");
        nu := wdot(g);
        vmu_nu := vmu*nu;
        norm := rtNorm[g];
        F := field[norm];
        vjA := vj*A;
        b := InnerProduct(vjA,vmu_nu)/InnerProduct(vjA,vmu);
        if b ne 0 then
          flag, b := IsCoercible(F,b);
          if not flag then 
            return [], "cannot coerce b into the field of definition";
          end if;
          m := -relativePairing(R,mu,g,q);
          rts := AllRoots(b,m);
          if not exists(a){ a : a in rts |
               InnerProduct(vjA*rho(x(g,-a)),vmu_nu) eq 0 } then
            rts := AllRoots(-b,m);
            if not exists(a){ a : a in rts |
               InnerProduct(vjA*rho(x(g,-a)),vmu_nu) eq 0 } then
              return [], A, "cannot clear from the right";
            end if;
          end if;

vprint Rewrite, 2: "* Found *", b, a;

          v_ := x(g,a)*v_;
          A *:= rho(x(g,-a));
        end if;
      end for;

      Append(~vs, v_);

      wj := r`w0J[j];

vprint Rewrite, 2: "LEFT",PapiOrder(W,wj);

      lambda := r`wtBase[j];
      for g in PapiOrder(W,wj) do
vprint Rewrite, 2: "from the left. g =", g;
        gamma := Coroot(W,g : Basis := "Root");
        nu := wdot(g);
        vj_nu := vj*nu;
        norm := rtNorm[g];
        F := field[norm];
        vjA := vj*A;
        b := InnerProduct(vj_nu*A,vmu)/InnerProduct(vjA,vmu);
        if b ne 0 then
          flag, b := IsCoercible(F,b);
          if not flag then 
            return [],"cannot coerce b into the field of definition";
          end if;
          m := relativePairing(R,lambda,g,q);
          if IsOdd(m) then b := -b; end if;
          rts := AllRoots(b,m);
          if not exists(a){ a : a in rts |
               InnerProduct(vj_nu*rho(x(g,-a))*A,vmu) eq 0 } then
            rts := AllRoots(-b,m);
            if not exists(a){ a : a in rts |
               InnerProduct(vj_nu*rho(x(g,-a))*A,vmu) eq 0 } then
              return [], A, "cannot clear from the left";
            end if;
          end if;

vprint Rewrite, 2: "*Found*", b, a;

          u *:= x(g,a);
          A := rho(x(g,-a))*A;
        end if;
      end for;

      D := IsEmpty(d) select G!1 else &*[EW[i] : i in d];
      Append(~ds, D);
      A *:= rho(D)^-1;
      w := D*w;
    end for;
    v := vs[k];
    for j := k-1 to 1 by -1 do v := v^ds[j] * vs[j]; end for;

    h, z := TwistedTorusWord(rho,A);
    if IsNull(h) then 
      return [],"no torus word"; 
    else 
      return [u * h[1] * w * v], z;
    end if;
  end function;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic PrepareRewrite(tp::MonStgElt,rk::RngIntElt,q::RngIntElt,
 X::SeqEnum, Xm::SeqEnum : OnlySimple := false, GS := false)
 -> UserProgram, Map
{Prepare to write elements in the group generated by CST
 generators X and Xm, of Lie type tp, rank rk as an SLP 
 in these generators}
  F := GF(q);
  K := BaseRing(X[1][1]);
  require Characteristic(K) eq Characteristic(F):
    "the domain and codomain must have the same characteristic";

  if OnlySimple then
    Q, Qm := SLPGeneratorList(tp,rk,q : GS := GS);
  else
    npos := &+[#Y : Y in X];
    S := SLPGroup(2*npos);
    b := #Basis(F);
    n := #X - 1;
    assert npos eq b*(n+1);
    Q := [[S.(b*i+j) : j in [1..b]] : i in [0..n]];
    Qm := [[S.(npos+b*i+j) : j in [1..b]] : i in [0..n]];
  end if;
  tprk := tp cat IntegerToString(rk);
  signsFG := func< tp | (tp eq "G") select [-1,1,1,1]
    else [1,1,1,1,-1,1,1,1,-1,-1,1,-1,-1,1,-1,-1,-1,-1,-1,-1] >;
  RD := GS and (tp in "FG")
      select RootDatum(tprk : Signs := signsFG(tp), Isogeny := "SC")
        else RootDatum(tprk : Isogeny := "SC");

  if GS and tp eq "G" then
    tmp := Q[1]; Q[1] := Q[2]; Q[2] := tmp;
    tmp := Qm[1]; Qm[1] := Qm[2]; Qm[2] := tmp;
  end if;

  G := GroupOfLieType(RD,F);
  phi := Internal_UntwistedMorphism(G,Q,Qm);
  rho := Internal_UntwistedMorphism(G,X,Xm : GS := GS);

  f := RowReductionMap(rho);
  return f, phi;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic LieTypeRewrite(tp::MonStgElt,rk::RngIntElt,q::RngIntElt,
 X::SeqEnum, Xm::SeqEnum, g::GrpMatElt : OnlySimple := false, GS := false)
 -> BoolElt, GrpSLPElt
{For g in the group generated by CST generators X and Xm, of
 Lie type tp, rank rk, write g as an SLP in these generators}
  f, phi := PrepareRewrite(tp,rk,q,X,Xm : OnlySimple := OnlySimple, GS := GS);
  wd,z := f(g);
  if IsNull(wd) then
    return false,false;
  else
    return IsOne(z), phi(wd[1]);
  end if;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic TwistedPrepareRewrite(tp::MonStgElt,rk::RngIntElt,q::RngIntElt,
 X::SeqEnum, Xm::SeqEnum : OnlySimple := false, GS := false)
 -> UserProgram, Map
{Prepare to write elements in the group generated by CST
 generators X and Xm, of Lie type tp, rank rk as an SLP 
 in these generators}
  flag, p, e := IsPrimePower(q);
  require flag : "q must be a prime power";

  require Characteristic(BaseRing(X[1][1])) eq p:
    "the domain and codomain must have the same characteristic";

  if OnlySimple then
    Q, Qm := SLPGeneratorList(tp,rk,q : GS := GS);
  else
    npos := &+[#Y : Y in X];
    S := SLPGroup(2*npos);
    n := 0;
    Q := []; Qm := [];
    for m := 1 to #X do
      k := #X[m];
      Append(~Q, [ S.(n+j) : j in [1..k]]);
      Append(~Qm, [ S.(npos+n+j) : j in [1..k]]);
      n +:= k;
    end for;
  end if;

  G := TwistedGroupOfLieType(tp,rk,q);
  phi := OnlySimple select Internal_TwistedMorphism(G,Q,Qm)
    else Internal_TwistedMorphism(G,Q,Qm : GS := GS);
  rho := Internal_TwistedMorphism(G,X,Xm : GS := GS);

  f := TwistedRowReductionMap(rho);
  return f, phi;

end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic TwistedLieTypeRewrite(tp::MonStgElt,rk::RngIntElt,q::RngIntElt,
 X::SeqEnum, Xm::SeqEnum, g::GrpMatElt : OnlySimple := false, GS := false)
 -> BoolElt, GrpSLPElt
{For g in the group generated by CST generators X and Xm, of
 Lie type tp, rank rk, write g as an SLP in these generators}
  f, phi := TwistedPrepareRewrite(tp,rk,q,X,Xm : OnlySimple := OnlySimple, GS := GS);
  wd,z := f(g);
  if IsNull(wd) then
    return false,false;
  else
    return IsOne(z), phi(wd[1]);
  end if;
end intrinsic;
//------------------------------------------------------------------------------


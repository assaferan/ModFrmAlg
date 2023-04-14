freeze;

/* 
  Extracted from CST.tex by MagmaCode 2.1 on Thu Oct 10 13:18:35 2019

  Curtis-Steinberg-Tits generators and relations for groups of Lie type

  October 2019 Don Taylor

  $Id: CST.m 65981 2022-06-11 01:03:52Z don $
*/

declare verbose CST, 3;

signs := AssociativeArray();
signs["D4"] := [1,-1,-1,1,1,1,1,1];
signs["D5"] := [-1,1,-1,-1,1, 1,1,1,1,1, 1,1,1,1,1];
signs["E6"] := [1,1,1,-1,-1,1, 1,1,1,-1,1,1, 1,1,1,1,1,1,
         1,1,1,1,1,1, 1,1,1,1,-1,-1];
signs["E7"] := [1,1,1,-1,-1,-1,1, 1,1,1,-1,-1,1,1, 1,1,1,-1,1,1,1,
        1,1,1,1,1,1,1, 1,1,1,1,1,1,1, 1,1,1,1,1,1,1,
       -1,1,1,-1,-1,1,-1, -1,-1,1,-1,1,-1,-1];
signs["F4"] := [1,1,1,1, -1,1,1,1, -1,-1,1,-1, -1,1,-1,-1, -1,-1,-1,-1];
signs["G2"] := [-1,1,1,1];

LieAdjointAction := function(RD, alpha : Basis := "Root")
  error if not IsSimplyConnected(RD), 
     "the root datum must be simply connected";
  error if Basis notin {"Standard","Root","Weight"},
     "Basis must be Standard, Root or Weight";

  C := ChangeRing(CartanMatrix(RD), Rationals());
  if Basis ne "Root" then alpha *:= C^-1; end if;

  R := Roots(RD : Basis := "Root");
  error if alpha notin R, "alpha is not a root of RD";
  LieConstant := func< beta,gamma | LieConstant_N(RD,Index(R,beta),Index(R,gamma)) >;

  posrts := PositiveRoots(RD : Basis := "Root");
  rank := Rank(RD);
  N := #posrts;
  nrank := N+rank;
  n := 2*N+rank;

  pos := {@ posrts[N+1-i] : i in [1..N] @};
  neg := {@ -posrts[i] : i in [1..N] @};
  ndx := Index(pos,alpha);
  if ndx eq 0 then ndx := nrank+Index(neg,alpha); end if;

  ad := Zero(MatrixRing(Integers(),n));
  C := ChangeRing(C,Integers());
  aC := ChangeRing(alpha,Integers())*C;
  lensq := RootNorms(RD);

  for j := 1 to N do
    if j+ndx eq n+1 then // $\alpha = -\beta$ (occurs at most once)
      aa := lensq[N+1-j];
      for i := 1 to rank do
        ad[j,N+i] := alpha[i]*lensq[i]/aa;
      end for;
    else
      beta := pos[j];
      b := LieConstant(beta,alpha);
      if b ne 0 then
        k := Index(pos,alpha+beta);
        if k eq 0 then
          ad[j,nrank+Index(neg,alpha+beta)] := b;
        else
          ad[j,k] := b;
        end if;
      end if;
    end if;
  end for;

  for j := 1 to rank do ad[N+j,ndx] := -aC[j]; end for;

  for j := 1 to N do
    jj := nrank+j;
    if jj+ndx eq n+1 then // $\alpha = -\beta$ (occurs at most once)
      aa := lensq[j];
      for i := 1 to rank do
        ad[jj,N+i] := alpha[i]*lensq[i]/aa;
      end for;
    else
      beta := neg[j];
      b := LieConstant(beta,alpha);
      if b ne 0 then
        k := Index(neg,alpha+beta);
        if k eq 0 then
          ad[jj,Index(pos,alpha+beta)] := b;
        else
          ad[jj,nrank+k] := b;
        end if;
      end if;
    end if;
  end for;
  return ad;
end function;

exponentialFn := function(A)
  is_nil, ndx := IsNilpotent(A);
  error if not is_nil, "matrix is not nilpotent";
  n := Ncols(A);

  return func< t |
    One(M) + &+[t^i*M!(A^i div Factorial(i)) : i in [1..ndx] ]
      where M is MatrixRing(Parent(t),n)>;
end function;


//==============================================================================
intrinsic StandardE8(q::RngIntElt : List := [1..15]) 
  -> SeqEnum[SeqEnum],SeqEnum[SeqEnum]
{ Generators for the adjoint representation of E8(q) }
  L := LieAlgebra("E8",Rationals());
  f := AdjointRepresentation(L);
  pos_, neg_, _ := StandardBasis(L);
  U := MatrixAlgebra(Integers(),248);
  I := IdentityMatrix(Integers(),120);
  K := DiagonalJoin(<I,-IdentityMatrix(Integers(),8),I>);
  pos := [U| -K*Matrix(f(b))*K : b in pos_];
  neg := [U| -K*Matrix(f(b))*K : b in neg_];
  B := Basis(GF(q));
  x := [exponentialFn(pos[i]) : i in List];
  y := [exponentialFn(neg[i]) : i in List];
  G := GL(248,q);
  Y := [[G| x[i](t) : t in B] : i in [1..#List]];
  Ym := [[G| y[i](t) : t in B] : i in [1..#List]];
  return Y, Ym;
end intrinsic;
//------------------------------------------------------------------------------

adjointChevalleyGenerators := function(tp,rk,q : OnlySimple := false)
  F := GF(q);

  tprk := tp * IntegerToString(rk);
  RD := RootDatum(tprk : Isogeny := "SC");
  posrts := PositiveRoots(RD : Basis := "Root");
  R := OnlySimple select posrts[1..Rank(RD)]
                 else {@ r : r in posrts | #Support(r) le 2 @};
  posmats := [LieAdjointAction(RD,alpha) : alpha in R];
  fpos := [exponentialFn(A) : A in posmats];
  negmats := [LieAdjointAction(RD,-alpha) : alpha in R];
  fneg := [exponentialFn(A) : A in negmats];
  B := Basis(F,PrimeField(F));
  d := Nrows(posmats[1]);
  G := GL(d,F);
  return [[G!f(t) : t in B] : f in fpos], [[G!f(t) : t in B] : f in fneg];
end function;


//==============================================================================
intrinsic AdjointChevalleyGroup(tp::MonStgElt,rk::RngIntElt,q::RngIntElt)
   -> GrpMat
{The adjoint Chevalley group of type tp and rank rk over the finite
 field of q elements}
  X, Xm := adjointChevalleyGenerators(tp,rk,q);
  n := Nrows(X[1][1]);
  return sub<GL(n,q) | &cat X, &cat Xm >;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic LieRootMatrix( RD::RootDtm, alpha::ModTupFldElt, X::SetIndx
  : Basis := "Root" ) -> AlgMatElt
{The matrix of ad(e_alpha) acting on X (on the right), where
 X is subset of the positive or the negative roots of the
 root datum RD}

  require IsSimplyConnected(RD) : "the root datum must be simply connected";

  if Basis ne "Root" then
    alpha *:= ChangeRing(CartanMatrix(RD),Rationals())^-1;
  end if;

  R := Roots(RD : Basis := "Root");
  require alpha in R : "alpha is not a root of RD";
  require X subset R : "X is not a set of roots of RD";
  n := #X;
  i := Index(R,alpha);
  ade:= Zero(MatrixRing(Integers(),n));
  for j := 1 to n do
    c := LieConstant_N( RD,Index(R,X[j]),i );
    if c ne 0 then
      ade[j][Index(X,alpha+X[j])] := c;
    end if;
  end for;
  return ade;
end intrinsic;
//------------------------------------------------------------------------------

reverse := func< X | {@ X[n+1-i] : i in [1..n] @} where n is #X >;


//==============================================================================
intrinsic StandardLieRepresentation( tp::MonStgElt, rk::RngIntElt )
    -> SeqEnum, SeqEnum
{Two sequences of integer matrices. The first sequence
 represents the simple roots, the second sequence represents
 the negatives of the simple roots for the simple Lie algebra
 of the given type and rank acting on the "standard module".}

  case tp:
  when "A","a","B","b","C","c","D","d":
    requirege rk, 1;
    RD := RootDatum( tp cat IntegerToString(rk+1) : Isogeny := "SC" );
    R := PositiveRoots(RD : Basis := "Root");
    X := reverse([x : x in R | x[1] eq 1]);
    if tp in "Aa" then
      E := [ LieRootMatrix(RD,R[i],X) : i in [rk+1..2 by -1] ];
      Eneg := [ LieRootMatrix(RD,-R[i],X) : i in [rk+1..2 by -1] ];
    elif tp in "Cc" then
      E := [ -LieRootMatrix(RD,R[i],X) : i in [2..rk] ];
      Eneg := [ -LieRootMatrix(RD,-R[i],X) : i in [2..rk] ];
      Append(~E, LieRootMatrix(RD,R[rk+1],X));
      Append(~Eneg, LieRootMatrix(RD,-R[rk+1],X));
    else
      E := [ -LieRootMatrix(RD,R[i],X) : i in [2..rk+1] ];
      Eneg := [ -LieRootMatrix(RD,-R[i],X) : i in [2..rk+1] ];
    end if;

  when "E","e":
    requirerange rk, 6, 8;
    if rk lt 8 then
      RD := RootDatum( tp cat IntegerToString(rk+1) : Isogeny := "SC" );
      R := PositiveRoots(RD : Basis := "Root");
      if rk eq 6 then
        X := {@ x : x in R | x[rk+1] eq 1 @};
        E := [ -LieRootMatrix(RD,-R[i],X) : i in [1..rk] ];
        Eneg := [ -LieRootMatrix(RD,R[i],X) : i in [1..rk] ];
      else
        X := reverse([x : x in R | x[rk+1] eq 1]);
        E := [ -LieRootMatrix(RD,R[i],X) : i in [1..rk] ];
        Eneg := [ -LieRootMatrix(RD,-R[i],X) : i in [1..rk] ];
      end if;
    else

      RD := RootDatum("E8" : Isogeny := "SC");
      R := PositiveRoots(RD : Basis := "Root");
      I := IdentityMatrix(Integers(),120);
      J := IdentityMatrix(Integers(),8);
      K := DiagonalJoin(<I,-J,I>);
      E := [ -K*Transpose(LieAdjointAction(RD,-R[i]))*K : i in [1..8] ];
      Eneg := [ -K*Transpose(LieAdjointAction(RD,R[i]))*K : i in [1..8] ];
    end if;

  when "F","f":
    require rk eq 4: "argument 2 should be 4";
    RD := RootDatum( "E7" : Isogeny := "SC" );
    R := PositiveRoots(RD : Basis := "Root");
    X := reverse([x : x in R | x[7] eq 1]);
    E := [ -LieRootMatrix(RD,R[i],X) : i in [1..6] ];
    EE := [E[2],E[4],E[3]+E[5],E[1]+E[6]];

    P := IdentityMatrix(Rationals(),27);
    P[13,14] := 1;
    P[14,13] := 1;  P[14,14] := -1;  P[14,15] := 1;
    P[15,14] := 1;
    Q := P^-1;

    M := MatrixRing(Integers(),26);
    I := [1..13] cat [15..27];
    res := func< A | M! &cat[[A[i,j] : j in I ] : i in I ] >;
    E := [ res(P*e*Q) : e in EE ];
    Eneg := [ res(P*Transpose(e)*Q) : e in EE ];

  when "G","g":
    require rk eq 2: "argument 2 should be 2";
    RD := RootDatum( "D5" : Signs := signs["D5"], Isogeny := "SC" );
    R := PositiveRoots(RD : Basis := "Root");
    X := reverse([ x : x in R | x[1] eq 1 ]);
    E := [ -LieRootMatrix(RD,R[i],X) : i in [2..5] ];
    EE := [E[1]+E[3]+E[4],E[2]];

    P := IdentityMatrix(Rationals(),8);
    P[4,5] := 1;
    P[5,4] := -1;
    Q := P^-1;

    M := MatrixRing(Integers(),7);
    I := [1..4] cat [6..8];
    res := func< A | M! &cat[[A[i,j] : j in I ] : i in I ] >;
    E := [ res(P*e*Q) : e in EE ];
    Eneg := [ res(P*Transpose(e)*Q) : e in EE ];

  else
    error "This type has not been implemented";
  end case;

  return E, Eneg;
end intrinsic;
//------------------------------------------------------------------------------

extendList := function(RD, X, Xm)
  W := CoxeterGroup(RD);
  P := PositiveRoots(RD : Basis := "Root");
  PW := PositiveRoots(RD : Basis := "Standard");
  coPW := PositiveCoroots(RD : Basis := "Standard");
  N := #P;
  rank := Rank(RD);

  EW := [X[i][1]*Xm[i][1]^-1*X[i][1] : i in [1..rank]];
  ndx := {@ i : i in [1..rank] @};

  U := X;
  Um := Xm;
  for i := rank+1 to N do
    if #Support(P[i]) le 2 then

      w := [];
      k := i;
      while k notin ndx do
        gamma := PW[k];
        j := rep{ j : j in [1..rank] | InnerProduct(coPW[j],gamma) gt 0 };
        Append(~w,j);
        k := k^W.j;
      end while;

      Q := U[k]; Qm := Um[k];
      for j in Reverse(w) do
        Q := [ EW[j]^-1*A*EW[j] : A in Q ];
        Qm := [ EW[j]^-1*A*EW[j] : A in Qm ];
        if LieConstant_eta(RD,j,k) lt 0 then
          Q := [A^-1 : A in Q ];
          Qm := [A^-1 : A in Qm ];
        end if;
      end for;
      Append(~U,Q);
      Append(~Um,Qm);
    end if;
    Include(~ndx,i);
  end for;
  return U,Um;
end function;

twistedBasis := function(q)
  flag, p, h := IsPrimePower(q);
  K := GF(q^2);
  theta := PrimitiveElement(K);
  eta := theta^(q+1);
  return [K| eta^nu : nu in [0..h-1]] cat [K| theta*eta^nu : nu in [0..h-1]];
end function;

twinnedBasis := function(B : LieConstant := 1)
  K := Universe(B);
  flag, q := IsSquare(#K);
  assert flag;
  theta := PrimitiveElement(K);
  eta := theta^(q+1);
  h := #B div 2;
  assert exists(u1){ x : x in K | x + x^q eq -LieConstant };
  assert exists(v1){ x : x in K | x + x^q eq -LieConstant*eta }; 
  uu := [eta^(2*nu)*u1 : nu in [0..h-1]] cat [ eta^(2*nu)*v1 : nu in [0..h-1]];
  return [<B[nu],uu[nu]> : nu in [1..2*h] ];
end function;

LieType2Agens := function(n,q)
  m := (n-1) div 2;
  B := twistedBasis(q);
  tp := "A" * IntegerToString(n);

  if IsEven(n) then
    RD := RootDatum(tp : Isogeny := "SC");
  else

    ss := [];
    for i := m to 1 by -1 do ss cat:= [1 : j in [1..m]] cat [-1 : j in [1..i]]; end for;
    ss cat:= [1 : j in [1..(m+1)*m div 2]];
    RD := RootDatum(tp : Isogeny := "SC", Signs := ss);
  end if;

  N := NumPosRoots(RD);
  G := GroupOfLieType(RD,q^2);
  x := func< i,a | elt<G|<i,a>> >;
  X := [[x(i,a)*x(n+1-i,a^q) : a in B] : i in [1..m]];
  Xm := [[x(N+i,a)*x(N+n+1-i,a^q) : a in B] : i in [1..m]];
  if IsEven(n) then
    pairs := twinnedBasis(B);
    X cat:= [[x(m+1,Q[1])*x(m+2,Q[1]^q)*x(3*m+3,Q[2]) : Q in pairs]];
    pairs := twinnedBasis(B : LieConstant := -1);
    Xm cat:= [[x(N+m+1,Q[1])*x(N+m+2,Q[1]^q)*x(N+3*m+3,Q[2]) : Q in pairs]];
  else
    h := #B div 2;
    X cat:= [[x(m+1,B[i]) : i in [1..h]]];
    Xm cat:= [[x(N+m+1,B[i]) : i in [1..h]]];
  end if;
  return X,Xm;
end function;

LieType2Dgens := function(n,q)
  F := GF(q^2);
  B := Basis(F);
  z := PrimitiveElement(F);
  F0, h := sub<F | z^(q+1) >;   // "GF(q)"
  B0 := [h(b) : b in Basis(F0)];

  tp := "D" * IntegerToString(n);
  RD := RootDatum(tp : Isogeny := "SC");
  N := NumPosRoots(RD);
  G := GroupOfLieType(RD,F);
  x := func< i,a | elt<G|<i,a>> >;
  X := [[x(i,b) : b in B0] : i in [1..n-2]] cat
       [[x(n-1,b)*x(n,b^q) : b in B]];
  Xm := [[x(N+i,b) : b in B0] : i in [1..n-2]] cat
       [[x(N+n-1,b)*x(N+n,b^q) : b in B]];
  return X,Xm;
end function;

LieType3D4gens := function(q)
  F := GF(q^3);
  B := Basis(F);
  z := PrimitiveElement(F);
  F0, h := sub<F | z^(q^2+q+1) >;   // "GF(q)"
  B0 := [h(b) : b in Basis(F0)];

  RD := RootDatum("D4" : Isogeny := "SC", Signs := signs["D4"]);
  N := NumPosRoots(RD);
  G := GroupOfLieType(RD,F);
  A := DiagonalMatrix(F,[-1,-1,1,1,-1,-1,1,1]);
  x := func< i,a | elt<G|<i,a>> >;
  X := [[x(2,b) : b in B0],
       [x(1,-b)*x(4,-b^q)*x(3,-b^q^2) : b in B],
       [x(5,b)*x(7,b^q)*x(6,b^q^2) : b in B],
       [x(10,-b)*x(8,-b^q)*x(9,-b^q^2) : b in B],
       [x(11,b) : b in B0],
       [x(12,b) : b in B0]];
  Xm := [[x(N+2,b) : b in B0],
        [x(N+1,-b)*x(N+4,-b^q)*x(N+3,-b^q^2) : b in B],
        [x(N+5,b)*x(N+7,b^q)*x(N+6,b^q^2) : b in B],
        [x(N+10,-b)*x(N+8,-b^q)*x(N+9,-b^q^2) : b in B],
        [x(N+11,b) : b in B0],
        [x(N+12,b) : b in B0]];
  return X,Xm;
end function;

LieType2E6gens := function(q : GS := false)
  F := GF(q^2);
  z := PrimitiveElement(F);
  F0,f := sub< F | z^(q+1) >; // GF(q)
  B := Basis(F);
  B0 := [ f(b) : b in Basis(F0) ];

  RD := RootDatum("E6" : Isogeny := "SC", Signs := signs["E6"]);
  N := NumPosRoots(RD);
  G := GroupOfLieType(RD,F);
  x := func< i,a | elt<G|<i,a>> >;

  eps := (GS) select 1 else -1;

  X := [
   [x(2,b) : b in B0],           // A
   [x(4,b) : b in B0],           // B
   [x(3,-b)*x(5,-b^q) : b in B], // C
   [x(1,b)*x(6,b^q) : b in B],   // D
   [x(8,b) : b in B0],           // A+B long
   [x(9,b)*x(10,b^q) : b in B],  // B+C short
   [x(7,b)*x(11,b^q) : b in B],  // C+D short
   [x(15,eps*b) : b in B0]];     // B+2C long
  Xm := [
   [x(N+2,b) : b in B0],
   [x(N+4,b) : b in B0],
   [x(N+3,-b)*x(N+5,-b^q) : b in B],
   [x(N+1,b)*x(N+6,b^q) : b in B],
   [x(N+8,b) : b in B0],
   [x(N+9,b)*x(N+10,b^q) : b in B],
   [x(N+7,b)*x(N+11,b^q) : b in B],
   [x(N+15,eps*b) : b in B0]];

  return X,Xm;
end function;

untwistedGenerators := function(tp, rk, K : GS := false)
  tprk := tp cat IntegerToString(rk);
  RD := GS and (tp in "FG") select
    RootDatum(tprk : Signs := signs[tprk], Isogeny := "SC") else
    RootDatum(tprk : Isogeny := "SC");
  G := GroupOfLieType(RD,K);
  roots := Roots(RD : Basis := "Root");
  N := NumPosRoots(RD);
  ndx := [1..N];
  if GS and tp eq "G" then ndx[1] := 2; ndx[2] := 1; end if;
  B := IsFinite(K) select Basis(K) else [One(K),K.1];
  x := func< i, t | elt<G|<i,t>> >;
  X := [[x(i,a) : a in B] : i in ndx | #Support(roots[i]) le 2];
  Xm := [[x(N+i,a) : a in B] : i in ndx | #Support(roots[i+N]) le 2];
  return X,Xm;
end function;


//==============================================================================
intrinsic LieTypeGenerators(tp::MonStgElt,rk::RngIntElt,q::RngIntElt
  : GS := false) -> SeqEnum[SeqEnum], SeqEnum[SeqEnum]
{Return the generators of a group of Lie type tp, rank rk over
 the field K or GF(q) in Curtis-Steinberg-Tits format}
  require IsPrimePower(q) : "q must be a prime power";
  case tp:
    when "2A" : return LieType2Agens(rk,q);
    when "2D" : return LieType2Dgens(rk,q);
    when "3D" :
      require rk eq 4 : "rank should be 4";
      return LieType3D4gens(q);
    when "2E" :
      require rk eq 6 : "rank should be 6";
      return LieType2E6gens(q : GS := GS);
  end case;
  return untwistedGenerators(tp,rk,GF(q) : GS := GS);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic LieTypeGenerators(tp::MonStgElt,rk::RngIntElt,K::Fld
  : GS := false) -> SeqEnum[SeqEnum], SeqEnum[SeqEnum]
{"} // "
   if IsFinite(K) and tp in ["2A","2D","3D","2E"] then
     return LieTypeGenerators(tp,rk,#K : GS := GS);
   else
     return untwistedGenerators(tp,rk,K : GS := GS);
   end if;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic LieTypeGenerators(G::GrpLie : GS := false) 
   -> SeqEnum[SeqEnum], SeqEnum[SeqEnum]
{Return the generators of a group G of Lie type in
 Curtis-Steinberg-Tits format}
  RD := RootDatum(G);
  require IsSimplyConnected(RD) : "the root datum must be simply connected";
  d := TwistingDegree(RD);
  tp := CartanName(RD)[1];
  nm := (d eq 1) select tp else IntegerToString(d) * tp;
  return LieTypeGenerators(nm,Rank(RD),DefRing(G) : GS := GS);
end intrinsic;
//------------------------------------------------------------------------------

quotientAction := function(V,U,X,Xm)
  if Dimension(U) eq 0 then return X, Xm; end if;
  E := ExtendBasis(U,V);
  C := Matrix(E);
  F := BaseRing(C);
  k := Dimension(U);
  d := Dimension(V) - k;
  G := GL(d,F);
  Y := [[G| Submatrix(C*A*C^-1,k+1,k+1,d,d) : A in Q] : Q in X];
  Ym := [[G| Submatrix(C*A*C^-1,k+1,k+1,d,d) : A in Q] : Q in Xm];
  return Y,Ym;
end function;

standardGens := function(G : GS := false)
  R := RootDatum(G);
  error if not (IsSimplyConnected(R) and IsIrreducible(R)),
   "available only for irreducible simply connected root data";
  F := BaseRing(G);
  error if Type(F) ne FldFin, "the base ring must be a finite field";
  tp := R`Type;
  t := tp[1,1];
  k := #tp[1,2];
  E, Em := StandardLieRepresentation(t,k);
  d := Nrows(E[1]);
  L := GL(d,F);
  B := Basis(F);
  p := Characteristic(F);

  name := CartanName(R);
  if name eq "F4" then
    Y := [[L| Transpose(exponentialFn(e)(a)) : a in B] : e in E];
    Ym := [[L| Transpose(exponentialFn(e)(a)) : a in B] : e in Em];

    if p eq 3 then
      L := GL(25,F);
      res := func< M, T | Solution(T,T*M) >;
      V := VectorSpace(F,26);
      S := Matrix([V.i : i in [1..12]] cat [V.13-V.14] cat [V.i : i in [15..26]]);
      Y := [[L| res(y,S) : y in Z] : Z in Y];
      Ym := [[L| res(y,S) : y in Z] : Z in Ym];
    end if;

  elif name eq "E6" then
    pi := L!PermutationMatrix(Integers(),Sym(d)!
       (7,8)(9,10)(11,12)(13,15)(16,17)(18,19)(20,21));
    Y := [[L| pi*exponentialFn(e)(a)*pi : a in B] : e in E];
    Ym := [[L| pi*exponentialFn(e)(a)*pi : a in B] : e in Em];

  elif name eq "G2" then
    Y := [[L| exponentialFn(e)(a) : a in B] : e in E];
    Ym := [[L| exponentialFn(e)(a) : a in B] : e in Em];

    if p eq 2 then
      V := VectorSpace(F,7);
      U := sub<V| V.4 >;
      Y, Ym := quotientAction(V,U,Y,Ym);
    end if;

  else
    Y := [[L| exponentialFn(e)(a) : a in B] : e in E];
    Ym := [[L| exponentialFn(e)(a) : a in B] : e in Em];
  end if;
  X,Xm := extendList(R,Y,Ym);
  if GS and name eq "G2" then
    X := [X[2],X[1]] cat X[3..6];
    Xm := [Xm[2],Xm[1]] cat Xm[3..6];
  end if;
  return X,Xm;
end function;

// standardRep := func< G : GS := false | Morphism(G,X,Xm)
//   where X, Xm is standardGens(G : GS := GS) >;


//==============================================================================
intrinsic IrreducibleHighestWeightGenerators(G::GrpLie, lambda::SeqEnum
   : OnlySimple := false) -> SeqEnum[SeqEnum], SeqEnum[SeqEnum]
{Return the reduced Curtis-Steinberg-Tits generators of the
 group G of Lie type in the irreducible representation with
 highest weight lambda. If OnlySimple is true, return
 generators for the simple roots only}

  F := BaseRing(G);
  require Type(F) eq FldFin : "the base ring must be a finite field";
  q := #F;
  require forall{ x : x in lambda | 0 le x and x lt q } : "weight not q-restricted";

  rho := HighestWeightRepresentation(G,lambda);

  B := Basis(F);
  N := NumberOfPositiveRoots(G);
  RD := RootDatum(G);
  roots := Roots(RD : Basis := "Root");
  if OnlySimple then
    n := Rank(G);
    X := [[rho(elt<G|<i,a>>) : a in B] : i in [1..n]];
    Xm := [[rho(elt<G|<i+N,a>>) : a in B] : i in [1..n]];
  else
    X := [[rho(elt<G|<i,a>>) : a in B] : i in [1..N] | #Support(roots[i]) le 2];
    Xm := [[rho(elt<G|<i+N,a>>) : a in B] : i in [1..N] | #Support(roots[i+N]) le 2];
  end if;
  I := sub<Codomain(rho) | &cat X, &cat Xm >;
  if IsIrreducible(I) then return X, Xm; end if;

  M := GModule(I);
  maxmod := MaximalSubmodules(M);
  assert #maxmod eq 1;

  V := VectorSpace(M);
  U := sub<V| [V| M!u : u in Basis(maxmod[1])] >;
  Y, Ym := quotientAction(V,U,X,Xm);
  return Y, Ym;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic IrreducibleHighestWeightFunction(G::GrpLie, lambda::SeqEnum)
    -> UserProgram
{Return x such that x(i,a) is the matrix representing x_i(a) in
 the irreducible highest weight representation L(lambda)}
  X,Xm := IrreducibleHighestWeightGenerators(G,lambda);
  rho := Morphism(G,X,Xm);
  return func<i,a | rho(elt<G|<i,a>>) >;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic VermaModule(G::GrpLie, lambda::SeqEnum) -> ModGrp,
  [], [], [], []
{ The universal highest weight module for G of weight lambda }
  R := RootDatum(G);
  n := Rank(R);
  require n eq #lambda : "bad weight length";
  F := BaseRing(G);
  require Type(F) eq FldFin : "the base ring must be a finite field";
  B := Basis(F);
  xi := PrimitiveElement(F);
  f := StandardRepresentation(G);
  I := Image(f);
  N := NumPosRoots(R);
  ugens := [[I| f(elt<G|<i,a>>) : a in Basis(F)] : i in [1..N]];
  vgens := [[I| f(elt<G|<i+N,a>>) : a in Basis(F)] : i in [1..N]];
  hgens := [I| f(TorusTerm(G,i,xi)) : i in [1..n] ];
  ngens := [I| f(elt<G|i>) : i in [1..n]];
  Ugens := &cat ugens;
  B := sub< I | Ugens, hgens >;
  A := MatrixAlgebra(F,1);
  gens := [A| [1] : i in [1..#Ugens]];
  if not IsTrivial(sub<I|hgens>) then gens cat:= [A| [xi^lambda[i]] : i in [1..n]]; end if;
  Y := GModule(B,gens);
  return Induction(Y,I), ugens, vgens, hgens, ngens;
end intrinsic;
//------------------------------------------------------------------------------

get2Agens := function(n,q,lambda : OnlySimple := false, Weyl := false)
  m := (n - 1) div 2;
  F := GF(q^2);
  B := twistedBasis(q);
  tp := "A" * IntegerToString(n);
  if IsEven(n) then
    RD := RootDatum(tp : Isogeny := "SC");
  else

    ss := [];
    for i := m to 1 by -1 do ss cat:= [1 : j in [1..m]] cat [-1 : j in [1..i]]; end for;
    ss cat:= [1 : j in [1..(m+1)*m div 2]];
    RD := RootDatum(tp : Isogeny := "SC", Signs := ss);
  end if;

  G := GroupOfLieType(RD,F);
  if IsEmpty(lambda) or Weyl then
    f := IsEmpty(lambda) select StandardRepresentation(G) else
           HighestWeightRepresentation(G,lambda);
    x := func< i,a | f(elt<G|<i,a>>) >;
  else
    x := IrreducibleHighestWeightFunction(G,lambda);
  end if;
  N := NumPosRoots(RD);
  d := Nrows(x(1,1));
  L := GL(d,F);
  X := [[L| x(i,b)*x(n+1-i,b^q) : b in B] : i in [1..m]];
  Xm := [[L| x(N+i,b)*x(N+n+1-i,b^q) : b in B] : i in [1..m]];

  if IsEven(n) then
    C := twinnedBasis(B);
    X cat:= [[L| x(m+1,Q[1])*x(m+2,Q[1]^q)*x(3*m+3,Q[2]) : Q in C]];
    if not OnlySimple then
      X cat:= [[L| x(n+i,b)*x(2*n-i,-b^q) : b in B] : i in [1..m-1]];
      X cat:= [[L| x(3*m+2,Q[1])*x(3*m+4,-Q[1]^q)*x(7*m+3,-Q[2]) : Q in C]];
    end if;
    C := twinnedBasis(B : LieConstant := -1);
    Xm cat:= [[L| x(N+m+1,Q[1])*x(N+m+2,Q[1]^q)*x(N+3*m+3,Q[2]) : 
      Q in C]];
    if not OnlySimple then
      Xm cat:= [[L| x(N+n+i,b)*x(N+2*n-i,-b^q) : b in B] : i in [1..m-1]];
      Xm cat:= [[L| x(N+3*m+2,Q[1])*x(N+3*m+4,-Q[1]^q)*x(N+7*m+3,-Q[2]) : 
       Q in C]];
    end if;
  else
    h := #B div 2;
    X cat:= [[L| x(m+1,B[i]) : i in [1..h]]];
    Xm cat:= [[L| x(N+m+1,B[i]) : i in [1..h]]];
    if not OnlySimple then
      X cat:= [[L| x(n+i,b)*x(2*n-i,b^q) : b in B] : i in [1..m]];
      Xm cat:= [[L| x(N+n+i,b)*x(N+2*n-i,b^q) : b in B] : i in [1..m]];
    end if;
  end if;
  return X, Xm;
end function;

get2Dgens := function(n,q,lambda : OnlySimple := false, Weyl := false)
  F := GF(q^2);
  B := Basis(F);
  z := PrimitiveElement(F);
  F0, h := sub<F | z^(q+1) >;   // "GF(q)"
  B0 := [h(b) : b in Basis(F0)];

  RD := RootDatum("D" * IntegerToString(n) : Isogeny := "SC");
  G := GroupOfLieType(RD,F);
  if IsEmpty(lambda) or Weyl then
    f := IsEmpty(lambda) select StandardRepresentation(G) else
           HighestWeightRepresentation(G,lambda);
    x := func< i,a | f(elt<G|<i,a>>) >;
  else
    x := IrreducibleHighestWeightFunction(G,lambda);
  end if;
  N := NumPosRoots(RD);
  d := Nrows(x(1,1));
  L := GL(d,F);
  X := [[L| x(i,b) : b in B0] : i in [1..n-2]] cat
       [[L| x(n-1,b)*x(n,b^q) : b in B]];
  Xm := [[L| x(N+i,b) : b in B0] : i in [1..n-2]] cat
       [[L| x(N+n-1,b)*x(N+n,b^q) : b in B]];

  if not OnlySimple then
    X cat:= [[L| x(n+i,b) : b in B0] : i in [1..n-3]] cat
         [[L| x(2*n-2,b)*x(2*n-1,b^q) : b in B]] cat
         [[L| x(3*n-2,b) : b in B0]];
    Xm cat:= [[L| x(N+n+i,b) : b in B0] : i in [1..n-3]] cat
         [[L| x(N+2*n-2,b)*x(N+2*n-1,b^q) : b in B]] cat
         [[L| x(N+3*n-2,b) : b in B0]];
  end if;
  return X, Xm;
end function;

get3D4gens := function(q,lambda : OnlySimple := false, Weyl := false)
  F := GF(q^3);
  B := Basis(F);
  z := PrimitiveElement(F);
  F0, h := sub<F | z^(q^2+q+1) >;   // "GF(q)"
  B0 := [h(b) : b in Basis(F0)];

  RD := RootDatum("D4" : Isogeny := "SC", Signs := signs["D4"]);
  G := GroupOfLieType(RD,F);
  if IsEmpty(lambda) or Weyl then
    f := IsEmpty(lambda) select StandardRepresentation(G) else
           HighestWeightRepresentation(G,lambda);
    if IsEmpty(lambda) then

      A := DiagonalMatrix(F,[-1,-1,1,1,-1,-1,1,1]);
      x := func< i,a | A*f(elt<G|<i,a>>)*A >;
    else
      x := func< i,a | f(elt<G|<i,a>>) >;
    end if;
  else
    x := IrreducibleHighestWeightFunction(G,lambda);
  end if;
  N := NumPosRoots(RD);
  X := []; Xm := [];
  d := Nrows(x(1,1));
  L := GL(d,F);
  X[1] := [L| x(2,b) : b in B0];
  X[2] := [L| x(1,-b)*x(4,-b^q)*x(3,-b^q^2) : b in B];
  Xm[1] := [L| x(N+2,b) : b in B0];
  Xm[2] := [L| x(N+1,-b)*x(N+4,-b^q)*x(N+3,-b^q^2) : b in B];

  if not OnlySimple then
    X[3] := [L| x(5,b)*x(7,b^q)*x(6,b^q^2) : b in B];
    X[4] := [L| x(10,-b)*x(8,-b^q)*x(9,-b^q^2) : b in B];
    X[5] := [L| x(11,b) : b in B0];
    X[6] := [L| x(12,b) : b in B0];

    Xm[3] := [L| x(N+5,b)*x(N+7,b^q)*x(N+6,b^q^2) : b in B];
    Xm[4] := [L| x(N+10,-b)*x(N+8,-b^q)*x(N+9,-b^q^2) : b in B];
    Xm[5] := [L| x(N+11,b) : b in B0];
    Xm[6] := [L| x(N+12,b) : b in B0];
  end if;
  return X, Xm;
end function;

get2E6gens := function(q,lambda : GS := false, OnlySimple := false, Weyl := false)
  F := GF(q^2);
  z := PrimitiveElement(F);
  F0,f := sub< F | z^(q+1) >; // GF(q)
  B := Basis(F);
  B0 := [ f(b) : b in Basis(F0) ];

  RD := RootDatum("E6" : Isogeny := "SC", Signs := signs["E6"]);
  G := GroupOfLieType(RD,F);
  if IsEmpty(lambda) or Weyl then
    f := IsEmpty(lambda) select StandardRepresentation(G) else
           HighestWeightRepresentation(G,lambda);
    if IsEmpty(lambda) then

      pi := PermutationMatrix(F,Sym(27)!
         (7,8)(9,10)(11,12)(13,15)(16,17)(18,19)(20,21));
      x := func< i,a | pi^-1*f(elt<G|<i,a>>)*pi >;
    else
      x := func< i,a | f(elt<G|<i,a>>) >;
    end if;
  else
    x := IrreducibleHighestWeightFunction(G,lambda);
  end if;
  N := NumPosRoots(RD);
  X := []; Xm := [];
  d := Nrows(x(1,1));
  L := GL(d,F);
  X[1] := [L| x(2,b) : b in B0];           // A
  X[2] := [L| x(4,b) : b in B0];           // B
  X[3] := [L| x(3,-b)*x(5,-b^q) : b in B]; // C
  X[4] := [L| x(1,b)*x(6,b^q) : b in B];   // D

  Xm[1] := [L| x(N+2,b) : b in B0];
  Xm[2] := [L| x(N+4,b) : b in B0];
  Xm[3] := [L| x(N+3,-b)*x(N+5,-b^q) : b in B];
  Xm[4] := [L| x(N+1,b)*x(N+6,b^q) : b in B];

  if not OnlySimple then
    eps := (GS) select 1 else -1;

    X[5] := [L| x(8,b) : b in B0];           // A+B long
    X[6] := [L| x(9,b)*x(10,b^q) : b in B];  // B+C short
    X[7] := [L| x(7,b)*x(11,b^q) : b in B];  // C+D short
    X[8] := [L| x(15,eps*b) : b in B0];      // B+2C long

    Xm[5] := [L| x(N+8,b) : b in B0];
    Xm[6] := [L| x(N+9,b)*x(N+10,b^q) : b in B];
    Xm[7] := [L| x(N+7,b)*x(N+11,b^q) : b in B];
    Xm[8] := [L| x(N+15,eps*b) : b in B0];

  end if;
  return X, Xm;
end function;


//==============================================================================
intrinsic CST_Generators(tp::MonStgElt,rk::RngIntElt,q::RngIntElt,lambda::SeqEnum
  : GS := false, OnlySimple := false, Weyl := false, Signs := 1)
  -> SeqEnum[SeqEnum], SeqEnum[SeqEnum]
{The reduced Curtis-Steinberg-Tits generators for the
 group of Lie type tp and rank rk over the field F in the
 representation with highest weight lambda. If OnlySimple is
 true, only generators for the simple roots are returned.}

  require IsPrimePower(q) : "q must be a prime power";
  require rk eq #lambda or #lambda eq 0 : "bad weight length";
  if tp eq "2A" then
    return get2Agens(rk,q,lambda : OnlySimple := OnlySimple, Weyl := Weyl);
  elif tp eq "2D" then
    require rk ge 4 : "rank should be at least 4";
    return get2Dgens(rk,q,lambda : OnlySimple := OnlySimple, Weyl := Weyl);
  elif tp eq "3D" then
    require rk eq 4 : "rank should be 4";
    return get3D4gens(q,lambda : OnlySimple := OnlySimple, Weyl := Weyl);
  elif tp eq "2E" then
    require rk eq 6 : "rank should be 6";
    return get2E6gens(q,lambda : GS := GS, OnlySimple := OnlySimple, Weyl := Weyl);
  elif tp eq "E" and rk eq 8 and IsEmpty(lambda) then
    return adjointChevalleyGenerators(tp,rk,q : OnlySimple := OnlySimple);
  end if;

  tprk := tp cat IntegerToString(rk);
  ss := GS and (tp in "FG") select signs[tprk] else Signs;
  RD := RootDatum(tprk : Isogeny := "SC", Signs := ss);
  G := GroupOfLieType(RD,q);

  if IsEmpty(lambda) or Weyl then
    if IsEmpty(lambda) then
      X, Xm := standardGens(G);
      if OnlySimple then
        X := X[1..rk];
        Xm := Xm[1..rk];
      end if;
    else
      f := HighestWeightRepresentation(G,lambda);
      roots := Roots(RD : Basis := "Root");
      N := NumPosRoots(RD);
      ndx := OnlySimple select [1..rk] else [1..N];
      B := Basis(GF(q));
      x := func< i,a | f(elt<G|<i,a>>) >;
      X := [[x(i,t) : t in B] : i in ndx | #Support(roots[i]) le 2 ];
      Xm := [[x(N+i,t) : t in B] : i in ndx | #Support(roots[N+i]) le 2 ];
    end if;
  else
    X,Xm := IrreducibleHighestWeightGenerators(G,lambda : OnlySimple := OnlySimple);
  end if;

  if GS and tp eq "G" then
    tmp := X[1]; X[1] := X[2]; X[2] := tmp;
    tmp := Xm[1]; Xm[1] := Xm[2]; Xm[2] := tmp;
  end if;

  return X,Xm;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic IrreducibleHighestWeightRepresentation(G::GrpLie, lambda::SeqEnum) -> Map
{The return value is the irreducible highest weight
 representation of the group G of Lie type with weight lambda}
  F := BaseRing(G);
  require Type(F) eq FldFin : "the base ring must be a finite field";
  R := RootDatum(G);
  tp := CartanName(R);
  rk := Rank(R);
  q := #F;
  X, Xm := CST_Generators(tp[1],rk,q,lambda);
  return Morphism(G, X, Xm);
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic UniversalHighWeightRepresentation(G::GrpLie, lambda::SeqEnum)
  -> Map, SeqEnum[SeqEnum], SeqEnum[SeqEnum]
{ The universal highest weight represenation for G of weight lambda }
  require not IsTwisted(G) : "not implemented for twisted groups";
  RD := RootDatum(G);
  roots := Roots(RD : Basis := "Root");
  n := Rank(RD);
  require n eq #lambda : "bad weight length";
  F := BaseRing(G);
  require Type(F) eq FldFin : "the base ring must be a finite field";
  N := NumPosRoots(RD);
  f := StandardRepresentation(G);
  I := Image(f);
  Y_,Ym_ := LieTypeGenerators(G);
  Y := [[I| f(g) : g in Y ] : Y in Y_];
  Ym := [[I| f(g) : g in Y ] : Y in Ym_];
  xi := PrimitiveElement(F);
  if xi eq F!1 then
    hgens := [];
  else
    hgens := [I| f(TorusTerm(G,i,xi)) : i in [1..n] ];
    ndx := [ i : i in [1..n] | hgens[i] ne One(I) ];
    hgens := [ h : h in hgens | h ne One(I) ];
  end if;
  ugens := &cat Y;

  B := sub< I | ugens cat hgens >;
  A := MatrixAlgebra(F,1);
  torus := (xi eq F!1) select [] else [A| [xi^lambda[i]] : i in ndx];
  gens := [A| [1] : i in [1..#ugens]] cat torus;
  Flambda := GModule(B,gens);
  J := Induction(Flambda,I);
  d := Dimension(J);
  C := GL(d,F);
  X := [[C| Matrix(F,d,d,[Vector(J.i*u) : i in [1..d]]) : u in useq] : useq in Y];
  Xm := [[C| Matrix(F,d,d,[Vector(J.i*u) : i in [1..d]]) : u in vseq] : vseq in Ym];
  return Morphism(G,X,Xm),X,Xm;
end intrinsic;
//------------------------------------------------------------------------------

extend3D4gen := function(X,Xm)

    e := -1;
    nA := x*Xm[1][1]^e*x where x is X[1][1];
    nB := x*Xm[2][1]^e*x where x is X[2][1];

    Z := [X[1],X[2]];
    Zm := [Xm[1],Xm[2]];

    Z[3] := [ (g^nA)^e : g in Z[2] ];
    Zm[3] := [ (g^nA)^e : g in Zm[2] ];
    Z[5] := [ g^nB : g in Z[3] ];
    Zm[5] := [ g^nB : g in Zm[3] ];
    Z[7] := [ g^nB : g in Z[1] ];
    Zm[7] := [ g^nB : g in Zm[1] ];
    Z[8] := [ (g^nA)^e : g in Z[7] ];
    Zm[8] := [ (g^nA)^e : g in Zm[7] ];

    ndx := [1,2,3,5,7,8];
    return [Z[i] : i in ndx],[Zm[i] : i in ndx];
end function;

extend2E6gen := function(X,Xm : GS := false)

  e := -1;
  nA := x*Xm[1][1]^e*x where x is X[1][1];
  nB := x*Xm[2][1]^e*x where x is X[2][1];
  nC := x*Xm[3][1]^e*x where x is X[3][1];
  nD := x*Xm[4][1]^e*x where x is X[4][1];

  Y := []; Ym := [];
  Y[3] := [ g^nB : g in X[1] ];
  Ym[3] := [ g^nB : g in Xm[1] ];
  Y[5] := [ (g^nB)^e : g in X[3] ];
  Ym[5] := [ (g^nB)^e : g in Xm[3] ];
  Y[7] := [ g^nD : g in X[3] ];
  Ym[7] := [ g^nD : g in Xm[3] ];
  if GS then
    Y[8] := [ g^nC : g in X[2] ];
    Ym[8] := [ g^nC : g in Xm[2] ];
  else
    Y[8] := [ (g^nC)^e : g in X[2] ];
    Ym[8] := [ (g^nC)^e : g in Xm[2] ];
  end if;

  ndx := [3,5,7,8];
  return X cat [Y[i] : i in ndx], Xm cat [Ym[i] : i in ndx];
end function;


//==============================================================================
intrinsic ExtendGeneratorList(tp::MonStgElt,rk::RngIntElt,
  X::SeqEnum[SeqEnum],Xm::SeqEnum[SeqEnum] : GS := false)
  -> SeqEnum[SeqEnum],SeqEnum[SeqEnum]
{Extend the list of generators for the group of Lie type
 (tp,rk) from simple roots and their negatives to all roots
 in rank 2 subsystems}

  if tp eq "3D" then
    return extend3D4gen(X,Xm);
  elif tp eq "2E" then
    return extend2E6gen(X,Xm : GS := GS);
  end if;

  require rk eq #X and rk eq #Xm : "wrong number of generators";
  tprk := tp cat IntegerToString(rk);
  RD := GS and (tp in "FG") 
      select RootDatum(tprk : Signs := signs[tprk], Isogeny := "SC")
        else RootDatum(tprk : Isogeny := "SC");

  if GS and tp eq "G" then
    U,Um :=  extendList(RD,[X[2],X[1]],[Xm[2],Xm[1]]);
    tmp := U[1]; U[1] := U[2]; U[2] := tmp;
    tmp := Um[1]; Um[1] := Um[2]; Um[2] := tmp;
  else
    U,Um :=  extendList(RD,X,Xm);
  end if;

  return U, Um;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic SLPGeneratorList(tp::MonStgElt,rk::RngIntElt,q::RngIntElt
  : GS := false) -> SeqEnum[SeqEnum],SeqEnum[SeqEnum]
{Reduced CST generators for the group of Lie type (tp,rk) over
 the field of order q as words in the generators indexed by
 the roots in rank 2 subsystems}
  flag, p, e := IsPrimePower(q);
  require flag : "q must be a prime power";
  tprk := tp cat IntegerToString(rk);
  if tprk eq "3D4" then
    S := SLPGroup(8*e);
    X := [[S.i : i in [1..e]]] cat [[S.(i+e) : i in [1..3*e]]];
    Xm := [[S.(4*e+i) : i in [1..e]]] cat [[S.(i+5*e) : i in [1..3*e]]];
    return extend3D4gen(X,Xm);
  end if;
  if tprk eq "2E6" then

    E := [e*i : i in [1,1,2,2]];
    npos := &+E;
    S := SLPGroup(2*npos);
    n := 0;
    X := []; Xm := [];
    for m := 1 to 4 do
      Append(~X, [ S.(n+j) : j in [1..E[m]]]);
      Append(~Xm, [ S.(npos+n+j) : j in [1..E[m]]]);
      n +:= E[m];
    end for;
    return extend2E6gen(X,Xm);
  end if;

  RD := GS and (tp in "FG")
      select RootDatum(tprk : Signs := signs[tprk], Isogeny := "SC")
      else RootDatum(tprk : Isogeny := "SC");
  npos := rk*e;
  S := SLPGroup(2*npos);
  X := [ [S.(m*e+i) : i in [1..e] ] : m in [0..rk-1] ];
  Xm := [ [S.(npos+m*e+i) : i in [1..e] ] : m in [0..rk-1] ];

  if GS and tp eq "G" then
    U,Um :=  extendList(RD,[X[2],X[1]],[Xm[2],Xm[1]]);
    tmp := U[1]; U[1] := U[2]; U[2] := tmp;
    tmp := Um[1]; Um[1] := Um[2]; Um[2] := tmp;
  else
    U,Um := extendList(RD,X,Xm);
  end if;

  return U, Um;
end intrinsic;
//------------------------------------------------------------------------------

expandGen := function (X, fld_elt)
  v := Eltseq(fld_elt);
  ChangeUniverse(~v,Integers());
  return &*[X[i]^v[i] : i in [1..#v] | v[i] ne 0 ];
end function;

sl2Presentation := function(q)
  K := GF(q);
  p := Characteristic(K);
  e := Degree(K);
  S := SLPGroup(2*e);
  X := [ S.i : i in [1..e] ];
  Xm := [ S.(e+i) : i in [1..e] ];

  rels := [ y^p = S!1 : y in X cat Xm ];

  if e eq 1 and p gt 3 then

    xa := func< a | X[1]^v where v is Integers()!a >;
    ya := func< a | Xm[1]^v where v is Integers()!a >;
    na := func< t | xa(t)*ya(-t^-1)*xa(t) >;
    ha := func< t | na(-1)*na(t) >;
    u := xa(1);
    h2 := ha(K!2);
    n := na(1);
    rels cat:= [ u^h2 = u^4, (n^2,u) = S!1,
      u*u^n*u = n, h2*n = xa(K!2^-1)*xa(K!2)^n*xa(K!2^-1)];

    xi := PrimitiveElement(K);
    if xi ne K!2 then
      h := ha(xi);
      rels cat:= [u^h = xa(xi^2), h^n = h^-1,
        h*n = xa(xi^-1)*xa(xi)^n*xa(xi^-1)];
    end if;
  else

    rels cat:= [(X[i],X[j]) = S!1 : j in [i+1..e], i in [1..e-1]];
    rels cat:= [(Xm[i],Xm[j]) = S!1 : j in [i+1..e], i in [1..e-1]];

    B := Basis(K);
    for i := 1 to e do
      b := B[i];
      n := X[i]*expandGen(Xm,-b^-1)*X[i];
      m := Xm[i]*expandGen(X,-b^-1)*Xm[i];
      for j := 1 to e do
        Append(~rels, n^-1*X[j]*n = expandGen(Xm,-b^-2*B[j]));
        Append(~rels, m^-1*Xm[j]*m = expandGen(X,-b^-2*B[j]));
      end for;
    end for;
  end if;

  return S, [ LHS(g)*RHS(g)^-1 : g in rels ];
end function;

twistedE6_Presentation := function(q : GS := false)

  flag, p, e := IsPrimePower(q);
  error if not flag, "q must be a prime power";
  F := GF(q^2);
  z := PrimitiveElement(F);
  F0,f := sub< F | z^(q+1) >; // GF(q)
  B := Basis(F);
  B0 := [ f(b) : b in Basis(F0) ];

  gs := GS select 1 else -1;
  RD := GS select RootDatum("F4" : Signs := signs["F4"], Isogeny := "SC")
        else RootDatum("F4" : Isogeny := "SC");
  Phi := Roots(RD : Basis := "Root");
  PhiPlus := PositiveRoots(RD : Basis := "Root");
  N := #PhiPlus;
  roots := [ i : i in [1..#Phi] | #Support(Phi[i]) le 2 ];

  Psi := {@ PhiPlus[i] : i in roots | i le N @};
  ndx := [ Index(PhiPlus,alpha) : alpha in Psi ];
  xdn := []; // inverted index
  for i := 1 to #ndx do xdn[ndx[i]] := i; end for;

  E := [e*i : i in [1,1,2,2,1,2,2,1]]; // long-short pattern
  npos := &+E;
  S := SLPGroup(2*npos);
  n := 0;
  X := []; Xm := [];
  for m := 1 to #Psi do
    Append(~X, [ S.(n+j) : j in [1..E[m]]]);
    Append(~Xm, [ S.(npos+n+j) : j in [1..E[m]]]);
    n +:= E[m];
  end for;

  rels := [ y^p = S!1 : y in Y, Y in X cat Xm ];
  vprint CST,1 : "(A1)",#rels;

  rels cat:=
    [(Y[i],Y[j]) = S!1 : j in [i+1..#Y], i in [1..#Y-1], Y in (X cat Xm)];
  vprint CST, 1 : "(A2)",#rels;

  for i := 1 to #roots - 1 do
    a := roots[i];
    Y := (a le N) select X[xdn[a]] else Xm[xdn[a-N]];
    for j := i+1 to #roots do
      b := roots[j];
      if (b ne a + N) and (Phi[a] + Phi[b] notin Phi) then
        Z := (b le N) select X[xdn[b]] else Xm[xdn[b-N]];
        rels cat:= [(y,z) = S!1 : y in Y, z in Z];
      end if;
    end for;
  end for;
  vprint CST, 1 : "(A3)",#rels;

  tuples := [ <1,2,5,1>, <25,26,29,-1>, <1,29,26,-1>,
              <2,29,25,1>, <25,5,2,1>, <26,5,1,-1> ]; // long
  for tt in tuples do
    a, b, c, eps := Explode(tt);
    Y := (a le N) select X[xdn[a]] else Xm[xdn[a-N]];
    Z := (b le N) select X[xdn[b]] else Xm[xdn[b-N]];
    W := (c le N) select X[xdn[c]] else Xm[xdn[c-N]];
    for nu := 1 to e do
      b_nu := B0[nu];
      for mu := 1 to e do
        b_mu := B0[mu];
        c := F0!(eps*b_nu*b_mu);
        Append(~rels, (Y[nu],Z[mu]) = expandGen(W,c));
      end for;
    end for;
  end for;
  vprint CST, 1 : "(B0) long",#rels;

  tuples := [ <3,4,7,1>, <27,28,31,-1>, <3,31,28,-1>,
              <4,31,27,1>, <27,7,4,1>, <28,7,3,-1> ]; // short
  for tt in tuples do
    a, b, c, eps := Explode(tt);
    Y := (a le N) select X[xdn[a]] else Xm[xdn[a-N]];
    Z := (b le N) select X[xdn[b]] else Xm[xdn[b-N]];
    W := (c le N) select X[xdn[c]] else Xm[xdn[c-N]];
    for nu := 1 to 2*e do
      for mu := 1 to 2*e do
        Append(~rels, (Y[nu],Z[mu]) = expandGen(W,eps*B[nu]*B[mu]));
      end for;
    end for;
  end for;
  vprint CST, 1 : "(B0) short",#rels;

  tuples := [
    <2,3,6,9,     func<t,u | t*u>,  func<t,u | gs*t*u*u^q> >,
    <2,30,27,33,  func<t,u | -t*u>, func<t,u | -gs*t*u*u^q> >,
    <26,6,3,9,    func<t,u | t*u>,  func<t,u | -gs*t*u*u^q> >,
    <26,27,30,33, func<t,u | -t*u>, func<t,u | gs*t*u*u^q> >,
    <9,27,6,2,    func<t,u | gs*t*u^q>,  func<t,u | gs*t*u*u^q> >,
    <9,30,3,26,   func<t,u | -gs*t*u^q>, func<t,u | -gs*t*u*u^q> >,
    <33,6,27,2,   func<t,u | gs*t*u^q>,  func<t,u | -gs*t*u*u^q> >,
    <33,3,30,26,  func<t,u | -gs*t*u^q>, func<t,u | gs*t*u*u^q> > ];
  for tt in tuples do
    a,b,c,d, f1,f2 := Explode(tt);
    Y := (a le N) select X[xdn[a]] else Xm[xdn[a-N]];
    Z := (b le N) select X[xdn[b]] else Xm[xdn[b-N]];
    V := (c le N) select X[xdn[c]] else Xm[xdn[c-N]];
    W := (d le N) select X[xdn[d]] else Xm[xdn[d-N]];
    for nu := 1 to e do
      b_nu := B0[nu];
      for mu := 1 to 2*e do
        b_mu := B[mu];
        c := f1(b_nu,b_mu);
        d := F0!(f2(b_nu,b_mu));
        Append(~rels, (Y[nu],Z[mu]) = expandGen(V,c)*expandGen(W,d));
      end for;
    end for;
  end for;
  vprint CST, 1 : "(B1)",#rels;

  tuples := [
    <6,3,9,    func<t,u | gs*(t*u^q + t^q*u) >>,
    <30,27,33, func<t,u | -gs*(t*u^q + t^q*u) >>,
    <6,27,2,   func<t,u | t*u + t^q*u^q >>,
    <30,3,26,  func<t,u | -(t*u + t^q*u^q) >>];
  for tt in tuples do
    a,b,c, f := Explode(tt);
    Y := (a le N) select X[xdn[a]] else Xm[xdn[a-N]];
    Z := (b le N) select X[xdn[b]] else Xm[xdn[b-N]];
    W := (c le N) select X[xdn[c]] else Xm[xdn[c-N]];
    for nu := 1 to 2*e do
      b_nu := B[nu];
      for mu := 1 to 2*e do
        b_mu := B[mu];
        c := F0!(f(b_nu,b_mu));
        rhs := (c eq 0) select S!1 else expandGen(W,c);
        Append(~rels, (Y[nu],Z[mu]) = rhs);
      end for;
    end for;
  end for;
  vprint CST, 1 : "(B2)",#rels;

  return S, [ LHS(g)*RHS(g)^-1 : g in rels ];
end function;

twistedD4_Presentation := function(q)
  flag, p, e := IsPrimePower(q);
  error if not flag, "q must be a prime power";
  F := GF(q^3);
  z := PrimitiveElement(F);
  F0,f := sub< F | z^(q^2+q+1) >; // GF(q)
  B := Basis(F);
  B0 := [ f(b) : b in Basis(F0) ];

  RD := RootDatum("G2" : Signs := signs["G2"], Isogeny := "SC");
  Phi := Roots(RD : Basis := "Root");
  N := NumPosRoots(RD);

  E := [e*i : i in [1,3,3,3,1,1]]; // 
  npos := &+E;
  S := SLPGroup(2*npos);
  n := 0;
  X := []; Xm := [];
  for m := 1 to N do
    Append(~X, [ S.(n+j) : j in [1..E[m]]]);
    Append(~Xm, [ S.(npos+n+j) : j in [1..E[m]]]);
    n +:= E[m];
  end for;

  rels := [ y^p = S!1 : y in Y, Y in X cat Xm ];
  vprint CST,1 : "(A1)",#rels;

  rels cat:=
    [(Y[i],Y[j]) = S!1 : j in [i+1..#Y], i in [1..#Y-1], Y in (X cat Xm)];
  vprint CST, 1 : "(A2)",#rels;

  xdn := [2,1,3,4,5,6,8,7,9,10,11,12]; // swap the simple roots (and their negatives)
  for a := 1 to 2*N - 1 do
    Y := (a le N) select X[a] else Xm[a-N];
    for b := a+1 to 2*N do
      if (b ne a + N) and (Phi[xdn[a]] + Phi[xdn[b]] notin Phi) then
        Z := (b le N) select X[b] else Xm[b-N];
        rels cat:= [(y,z) = S!1 : y in Y, z in Z];
      end if;
    end for;
  end for;
  vprint CST, 1 : "(A3)",#rels;

fcd := func< c, d | c*d >;
fmcd := func< c, d | -c*d >;
fcd2 := func< c, d | c*d^(q+q^2) >;
fmcd2 := func< c, d | -c*d^(q+q^2) >;
fcd3 := func< c, d | c*d^(1+q+q^2) >;
fmcd3 := func< c, d | -c*d^(1+q+q^2) >;
fc2d3 := func< c, d | c^2*d^(1+q+q^2) >;
fmc2d3 := func< c, d | -c^2*d^(1+q+q^2) >;

  tuples := [
    <1,2,3,4,5,6,    fcd,fmcd2,fcd3,fc2d3>,
    <1,9,8,10,12,11, fmcd,fcd2,fcd3,fmc2d3>,
    <5,8,4,3,1,6,    fmcd,fcd2,fcd3,fmc2d3>,
    <5,10,2,9,12,7,  fcd,fmcd2,fcd3,fc2d3>,
    <6,9,4,2,7,5,    fmcd,fmcd2,fmcd3,fc2d3>,
    <6,10,3,8,11,1,  fcd,fcd2,fmcd3,fmc2d3>,
    <7,8,9,10,11,12, fmcd,fmcd2,fmcd3,fc2d3>,
    <7,3,2,4,6,5,    fcd,fcd2,fmcd3,fmc2d3>,
    <11,2,10,9,7,12, fcd,fcd2,fmcd3,fmc2d3>,
    <11,4,8,3,6,1,   fmcd,fmcd2,fmcd3,fc2d3>,
    <12,3,10,8,1,11, fcd,fmcd2,fcd3,fc2d3>,
    <12,4,9,2,5,7,   fmcd,fcd2,fcd3,fmc2d3> ];

  for tt in tuples do
    i,j, a,b,c,d, f1,f2,f3,f4 := Explode(tt);
    I := (i le N) select X[i] else Xm[i-N];
    J := (j le N) select X[j] else Xm[j-N];
    Y := (a le N) select X[a] else Xm[a-N];
    Z := (b le N) select X[b] else Xm[b-N];
    V := (c le N) select X[c] else Xm[c-N];
    W := (d le N) select X[d] else Xm[d-N];
    for nu := 1 to e do
      b_nu := B0[nu];
      for mu := 1 to 3*e do
        b_mu := B[mu];
        a := (a_ eq 0) select S!1 else expandGen(Y,a_)
             where a_ is f1(b_nu,b_mu);
        b := (b_ eq 0) select S!1 else expandGen(Z,b_)
             where b_ is f2(b_nu,b_mu);
        c := (c_ eq 0) select S!1 else expandGen(V,c_)
             where c_ is F0!(f3(b_nu,b_mu));
        d := (d_ eq 0) select S!1 else expandGen(W,d_)
             where d_ is F0!(f4(b_nu,b_mu));
        Append(~rels, (I[nu],J[mu]) = a*b*c*d);
      end for;
    end for;
  end for;
  vprint CST, 1 : "(B1)",#rels;

  f2cd := func< c,d | c^q*d^(q^2) + c^(q^2)*d^q >;
  fm2cd := func< c,d | -c^q*d^(q^2) - c^(q^2)*d^q >;
  f3c2d := func< c,d | c^(1+q)*d^(q^2) + c^(q+q^2)*d + c^(1+q^2)*d^q >;
  fm3c2d := func< c,d | -c^(1+q)*d^(q^2) - c^(q+q^2)*d - c^(1+q^2)*d^q >;
  f3cd2 := func< c,d | c*d^(q+q^2) + c^q*d^(1+q^2) + c^(q^2)*d^(1+q) >;
  fm3cd2 := func< c,d | -c*d^(q+q^2) - c^q*d^(1+q^2) - c^(q^2)*d^(1+q) >;

  tuples := [
    <2,3,4,5,6,    f2cd,fm3c2d,fm3cd2>,
    <2,10,9,7,12,  fm2cd,f3c2d,f3cd2>,
    <3,10,8,1,11,  f2cd,fm3c2d,fm3cd2>,
    <4,8,3,6,1,    fm2cd,fm3c2d,fm3cd2>,
    <4,9,2,5,7,    f2cd,f3c2d,f3cd2>,
    <8,9,10,11,12, fm2cd,fm3c2d,fm3cd2> ];
  for tt in tuples do
    i,j, a,b,c, f1,f2,f3 := Explode(tt);
    I := (i le N) select X[i] else Xm[i-N];
    J := (j le N) select X[j] else Xm[j-N];
    Y := (a le N) select X[a] else Xm[a-N];
    Z := (b le N) select X[b] else Xm[b-N];
    V := (c le N) select X[c] else Xm[c-N];
    for nu := 1 to 3*e do
      b_nu := B[nu];
      for mu := 1 to 3*e do
        b_mu := B[mu];
        a := (a_ eq 0) select S!1 else expandGen(Y,a_)
             where a_ is f1(b_nu,b_mu);
        b := (b_ eq 0) select S!1 else expandGen(Z,b_)
             where b_ is F0!f2(b_nu,b_mu);
        c := (c_ eq 0) select S!1 else expandGen(V,c_)
             where c_ is F0!(f3(b_nu,b_mu));
        Append(~rels, (I[nu],J[mu]) = a*b*c);
      end for;
    end for;
  end for;
  vprint CST, 1 : "(B2)",#rels;

  tuples := [<1,5,6, fcd>,  <1,12,11, fmcd>, <5,12,7, fcd>,
    <6,7,5, fmcd>, <6,11,1, fcd>, <7,11,12, fmcd>];
  for tt in tuples do
    i,j, a, f1 := Explode(tt);
    I := (i le N) select X[i] else Xm[i-N];
    J := (j le N) select X[j] else Xm[j-N];
    Y := (a le N) select X[a] else Xm[a-N];
    for nu := 1 to e do
      for mu := 1 to e do
        a := (a_ eq 0) select S!1 else expandGen(Y,a_)
             where a_ is F0!(f1(B0[nu],B0[mu]));
        Append(~rels, (I[nu],J[mu]) = a);
      end for;
    end for;
  end for;
  vprint CST, 1 : "(B3)",#rels;

  f3cd := func<c,d | c*d + (c*d)^q + (c*d)^(q^2) >;
  fm3cd := func<c,d | -c*d - (c*d)^q - (c*d)^(q^2) >;
  tuples := [<2,4,5, f3cd>, <2,9,7, f3cd>, <3,4,6, f3cd>,
   <3,8,1, f3cd>, <8,10,11, fm3cd>, <9,10,12, fm3cd>];

  for tt in tuples do
    i,j, a, f1 := Explode(tt);
    I := (i le N) select X[i] else Xm[i-N];
    J := (j le N) select X[j] else Xm[j-N];
    Y := (a le N) select X[a] else Xm[a-N];
    for nu := 1 to 3*e do
      for mu := 1 to 3*e do
        a := (a_ eq 0) select S!1 else expandGen(Y,a_)
             where a_ is F0!(f1(B[nu],B[mu]));
        Append(~rels, (I[nu],J[mu]) = a);
      end for;
    end for;
  end for;
  vprint CST, 1 : "(B4)",#rels;

  return S, [ LHS(g)*RHS(g)^-1 : g in rels ];
end function;


//==============================================================================
intrinsic CST_Presentation(tp::MonStgElt, rk::RngIntElt, q::RngIntElt
          : GS := false) -> GrpSLP, SeqEnum[GrpSLPElt]
{The Curtis-Steinberg-Tits relations for the group of Lie
 type tp, rank rk over the field of q elements}

  flag, p, e := IsPrimePower(q);
  require flag : "q must be a prime power";
  if rk eq 1 then return sl2Presentation(q); end if;
  tprk := tp cat IntegerToString(rk);
  F := GF(q);

  if tprk eq "3D4" then
    S, rels := twistedD4_Presentation (q);
    return S, rels;
  elif tprk eq "2E6" then
    S, rels := twistedE6_Presentation (q: GS := GS);
    return S, rels;
  end if;

  if GS and (tp in "FG") then
    RD := RootDatum(tprk : Signs := signs[tprk], Isogeny := "SC");
  else
    RD := RootDatum(tprk : Isogeny := "SC");
  end if;
  Phi := Roots(RD : Basis := "Root");
  PhiPlus := PositiveRoots(RD : Basis := "Root");
  N := #PhiPlus;
  B := Basis(F);
  Psi := {@ alpha : alpha in PhiPlus | #Support(alpha) le 2 @};
  ndx := [ Index(PhiPlus,alpha) : alpha in Psi ];
  xdn := []; // inverted index
  for i := 1 to #ndx do xdn[ndx[i]] := i; end for;
  npos := #Psi * e;
  S := SLPGroup(2*npos);
  X := [ [S.(m*e+i) : i in [1..e] ] : m in [0..#Psi-1] ];
  Xm := [ [S.(npos+m*e+i) : i in [1..e] ] : m in [0..#Psi-1] ];
  if GS and tp eq "G" then
    X := [X[2],X[1]] cat [[g : g in Y] : Y in X[3..6]];
    Xm := [Xm[2],Xm[1]] cat [[g : g in Y] : Y in Xm[3..6]];
  end if;

  rels := [ y^p = S!1 : y in Y, Y in X cat Xm ];

  if e gt 1 then
    rels cat:=
     [(Y[i],Y[j]) = S!1 : j in [i+1..e], i in [1..e-1], Y in (X cat Xm)];
  end if;

  case tp:
    when "A","D","E":
      pairs := [<1,1>];
    when "B","C","F":
      pairs := [<1,1>,<1,2>,<2,1>];
    when "G":
      pairs := [<1,1>,<1,2>,<2,1>,<1,3>,<3,1>,<2,3>,<3,2>];
  else:
    error "Unknown type",tp;
  end case;

  for a := 1 to rk-1 do
    vprint CST, 2: "a =",a;
  for b := a+1 to rk do
    vprint CST, 2: "b =",b;
    _, Q := sub< RD | [a,b] >;
    m := #Q;
    for r_ := 1 to m-1 do
      r := Q[r_];
      alpha := Phi[r];
      Y := (r le N) select X[xdn[r]] else Xm[xdn[r-N]];
      for s_ := r_+1 to m do
        s := Q[s_];
        if s-r eq N then continue; end if;
        vprint CST, 2: "r =",r,"s =",s;
        beta := Phi[s];
        Z := (s le N) select X[xdn[s]] else Xm[xdn[s-N]];
        if alpha+beta notin Phi then
          rels cat:= [ (Y[i],Z[j]) = S!1 : i,j in [1..e] ];
        else
          for nu := 1 to e do
          vprint CST, 2: "nu =",nu;
            b_nu := B[nu];
            for mu := 1 to e do
              vprint CST, 2: "mu =",mu;
              b_mu := B[mu];
              lhs := (Y[nu],Z[mu]);
              rhs := [];
              for pair in [w : w in pairs | w[1]*alpha+w[2]*beta in Phi] do
                i, j := Explode(pair);
                c := LieConstant_C(RD,i,j,r,s);
                vprint CST, 2: "  ",i,j,c;
                if F!c ne 0 then
                  gamma := i*alpha+j*beta;
                  t := Index(Phi,gamma);
                  W := (t le N) select X[xdn[t]] else Xm[xdn[t-N]];
                  vprint CST, 2: "   t =",t;
                  Append(~rhs, expandGen(W,c*b_nu^i*b_mu^j));
                end if;
              end for;
              rhsval := IsEmpty(rhs) select S!1 else &*rhs;
              Append(~rels, lhs = rhsval);
            end for;
          end for;
        end if;
      end for;
    end for;
  end for;
  end for;

  return S, [ LHS(g)*RHS(g)^-1 : g in rels ];
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic CST_VerifyPresentation(tp::MonStgElt, rk::RngIntElt, q::RngIntElt,
    X::SeqEnum[SeqEnum], Xm::SeqEnum[SeqEnum] : GS := false)
    -> BoolElt, RngIntElt
{Verify the presentation of the group of type tp with
 Curtis-Steinberg-Tits generators X, Xm}
  S, rels := CST_Presentation(tp, rk, q : GS := GS);
  gens := &cat X cat &cat Xm;
  if #gens ne Ngens(S) then return false, 0; end if;
  T := Evaluate(rels, gens);
  G := Parent(X[1,1]);
  if exists(i){i : i in [1..#T] | T[i] ne One(G)} then
    return false, i;
  else
    return true, _;
  end if;
end intrinsic;
//------------------------------------------------------------------------------


//==============================================================================
intrinsic CSTtoChev(tp :: MonStgElt, rk :: RngIntElt, q :: RngIntElt,
     X :: SeqEnum, Xm :: SeqEnum : GS := false, UseMap := false) -> Map
 {A projective morphism from the group generated by the CST
  generators X and Xm to the standard copy}

  F := GF(q);
  n := Nrows(X[1][1]);
  K := BaseRing(X[1][1]);
  M := GL(n,K);
  H := sub< M | &cat X, &cat Xm >;

  if tp in { "2A","3D","2E" } then
    G := TwistedGroupOfLieType(tp,rk,q);
    rho := Internal_TwistedMorphism(G,X,Xm : GS := GS);
    Q,Qm := CST_Generators(tp,rk,q,[] : GS := GS);
    phi := Internal_TwistedMorphism(G,Q,Qm : GS := GS);
    psi := TwistedRowReductionMap(rho);
  else

    if K ne F and K subset F then
      X := [[GL(n,F)| x : x in lst] : lst in X];
      Xm := [[GL(n,F)| x : x in lst] : lst in Xm];
    end if;
    tprk := tp cat IntegerToString(rk);
    signsFG := func< tp | (tp eq "G") select [-1,1,1,1]
      else [1,1,1,1,-1,1,1,1,-1,-1,1,-1,-1,1,-1,-1,-1,-1,-1,-1] >;
    RD := GS and (tp in "FG")
        select RootDatum(tprk : Signs := signsFG(tp), Isogeny := "SC")
          else RootDatum(tprk : Isogeny := "SC");
    G := GroupOfLieType(RD,F);
    rho := Internal_UntwistedMorphism(G,X,Xm : GS := GS);
    Q,Qm := standardGens(G : GS := GS);
    phi := Internal_UntwistedMorphism(G,Q,Qm : GS := GS);
    psi := RowReductionMap(rho);
  end if;
  L := Generic(Parent(Q[1,1]));
  return UseMap select map< H -> L | g :-> phi(psi(g)[1]) >
         else func< g | phi(psi(g)[1]) >;
end intrinsic;
//------------------------------------------------------------------------------


freeze;

/*
  Lang's Theorem for classical groups

  March 2022 Don Taylor

  $Id: ClassicalLang.m 65594 2022-03-19 12:11:06Z don $
*/
matrixNorm := function(c,q,r)
  bool, p, e := IsPrimePower(q); assert bool;
  i := e;
  h := One(Parent(c));
  cs := Matrix(c);
  while r gt 0 do
    if IsOdd(r) then
      h := FrobeniusImage(h,i) * cs;
      r -:= 1;
    end if;
    cs := FrobeniusImage(cs,i) * cs;
    r div:= 2;
    i *:= 2;
  end while;
  return Parent(c)!h;
end function;

extendField := function( c, q )
  B := BaseRing(c);
  k := GF(q);
  K := CommonOverfield(k,sub< B | Eltseq(c) >);
  r := Degree(K,k);
  c0 := ChangeRing(c,K);
  s := Order(matrixNorm(c0,q,r));
  L := GF(q^(r*s));
  return L, ChangeRing(c0,L);
end function;

restrict := function(c,k)
  K := BaseRing(c);
  B := Basis(K,k);
  n := Nrows(c);
  blocks := [[ Matrix([Eltseq(b*c[i,j],k) : b in B]) : j in [1..n]] : i in [1..n]];
  return BlockMatrix(n,n,blocks);
end function;

consolidate := function(v,K,k)
  d := Degree(K,k);
  m := Degree(v);
  b, n := IsDivisibleBy(m,d); assert b;
  vs := Eltseq(v);
  return Vector([ K!vs[d*i+1 .. d*(i+1)] : i in [0..n-1] ]);
end function;

twistedEigenspace := function(c,q)
  K := BaseRing(c);
  k := GF(q);
  S := Matrix([Eltseq(b^q,k) : b in Basis(K,k)]);
  sigma := DiagonalJoin( [ S : i in [1..Nrows(c)] ]);
  V0 := Eigenspace(sigma*restrict(c,k),1);
  return [ consolidate(v,K,k) : v in Basis(V0) ];
end function;

langGL_D := function(c, q)
  L, c0 := extendField(c,q);
  E := twistedEigenspace(c0,q);
  return Matrix(E);
end function;

langGL_R := function(c,q)
  n := Nrows(c);
  bool, p, e := IsPrimePower(q); assert bool;
  L, c0 := extendField(c,q);
  r := Degree(L,GF(q));
  M := MatrixAlgebra(L,n);
  a := Zero(M);
  repeat
    prev := Random(M);
    xs := [ prev ];
    for i := 1 to r-1 do
      xx := FrobeniusImage(prev, e)*c0;
      Append(~xs,xx);
      prev := xx;
    end for;
    a := &+xs;
  until Determinant(a) ne 0;
  return a;
end function;


//==============================================================================
intrinsic ClassicalLang( tp::MonStgElt, c::GrpMatElt[FldFin], q::RngIntElt
   : Al := "Random" ) -> AlgMatElt
{ Return a such that c = a^-F *a , where F is the standard
  Frobenius endomorphism for q and c belongs to a classical 
  group of type tp, where tp is one of GL, SL, Sp, O, O+, O-}
  require tp in {"GL", "SL", "Sp", "O", "O+", "O-"} :
    "tp must be one of GL, SL, Sp, O, O+, O-";
  k := GF(q);
  K := BaseRing(c);
  b, p, e := IsPrimePower(q);
  require b: "q must be a power of a prime";
  require q mod Characteristic(K) eq 0: "base field of c incompatible with q";
  n := Nrows(c);
  a := (Al eq "Random") select langGL_R(c,q) else langGL_D(c,q);
  L := BaseRing(a);
  case tp:
    when "GL": 
      a0 := a;

    when "SL":
      require Determinant(c) eq 1: "The determinant of c should be 1";
      d := Determinant(a);
      if d ne 1 then
        s := IdentityMatrix(L,n); s[1,1] := d^-1;
        a0 := s*a;
      else
        a0 := a;
      end if;

    when "Sp":
      require IsEven(n): "the dimension of c should be even";
      require c in Sp(n,K): "c must be in the symplectic group";
      Xi := StandardAlternatingForm(n,L);
      J := a*Xi*Transpose(a);
      J0 := ChangeRing(J,k);
      T := TransformForm(J0,"symplectic");
      a0 := ChangeRing(T^-1,L)*a;
    when "O+":
      require Determinant(c) eq 1: "The determinant of c should be 1";
      if IsOdd(q) then
        require c in SOPlus(n,K): "c must be in the orthogonal group";
      else
        require c in OmegaPlus(n,K): "c must be in the Omega group";
      end if;
      if IsOdd(q) then
        Lambda := StandardSymmetricForm(n,L);
        J := a*Lambda*Transpose(a);
        J0 := ChangeRing(J,k);
        V0 := VectorSpace(k,n,J0);
        H := HyperbolicSplitting(V0);
        m := n div 2;
        B := [ H[1,i,1] : i in [1..m]] cat [ H[1,i,2] : i in [m..1 by -1]];
        a0 := ChangeRing(Matrix(B),L) * a;
      else
        Theta := StandardQuadraticForm(n,L);
        Q := TransformQuadForm(Theta,GL(n,L)!a);
        Q0 := ChangeRing(Q,k);
        T := TransformForm(Q0,"orth+");
        a0 := ChangeRing(T^-1,L)*a;
      end if;
      if DicksonInvariant(GL(n,L)!a0) ne 0 then
        s := IdentityMatrix(L,n);
        s[1,1] := 0; s[1,n] := 1; s[n,1] := 1; s[n,n] := 0;
        a0 := s*a0;
      end if;
    when "O-":
      require DicksonInvariant(c) eq 0: 
              "The Dickson invariant of c should be 0";
      if IsOdd(q) then
        Xi := StandardSymmetricForm(n,k : Minus);
        Lambda := ChangeRing(Xi,K);
        require c*Lambda*Transpose(c) eq Lambda:
           "c must be orthogonal and defined over GF(q)";
        Lambda0 := ChangeRing(Lambda,L);
        J := a*Lambda0*Transpose(a);
        J0 := ChangeRing(J,k);
        T := TransformForm(J0,"orth-");
        a0 := ChangeRing(T^-1,L)*a;
      else
        Theta0 := StandardQuadraticForm(n,k : Minus);
        Theta1 := ChangeRing(Theta0,K);
        require TransformQuadForm(Theta1,c) eq Theta1:
           "c must be orthogonal and defined over GF(q)";
        Theta := ChangeRing(Theta1,L);
        Q := TransformQuadForm(Theta,GL(n,L)!a);
        Q0 := ChangeRing(Q,k);
        T := TransformForm(Q0,"orth-");
        a0 := ChangeRing(T^-1,L)*a;
      end if;
      if DicksonInvariant(GL(n,L)!a0) ne 0 then
        s := IdentityMatrix(L,n);
        s[1,1] := 0; s[1,n] := 1; s[n,1] := 1; s[n,n] := 0;
        a0 := s*a0;
      end if;
    when "O":
      require IsOdd(n): "the dimension of c should be odd";
      require IsOdd(q): "available only in odd characteristic";
      Xi := StandardSymmetricForm(n,L);
      J := a*Xi*Transpose(a);
      J0 := ChangeRing(J,k);
      T := TransformForm(J0,"orth");
      a0 := ChangeRing(T^-1,L)*a;
      if Determinant(a0) ne 1 then
        m := (n - 1) div 2;
        s := IdentityMatrix(L,n);
        s[m+1,m+1] := -1;
        a0 := s*a0;
      end if;
    else
      error "tp must be one of GL, SL, Sp, O, O+, O-";
  end case;

  return a0;
end intrinsic;
//------------------------------------------------------------------------------


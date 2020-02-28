//freeze;

declare type RfxFrm;
declare attributes RfxFrm:
  V, // the vector space
  L, // the field
  type, // alternating, symmetric or Hermitian
  matrix, // the matrix representing the form
  aut; // the associated automorphism of L

/* constructors */

intrinsic ReflexiveForm(M::AlgMatElt, alpha::FldAut) -> RfxFrm
{.}
  phi := New(RfxFrm);
  phi`L := BaseField(alpha);
  n := NumberOfRows(M);
  is_coercible, M_L :=  IsCoercible(MatrixAlgebra(phi`L,n), M);
  require is_coercible :
    "matrix and automorphism should be defined over the same field.";
  phi`V := RowSpace(M_L);
  phi`matrix := M_L;
  phi`aut := alpha;

  if (Order(alpha) eq 2) then
     phi`type := "Hermitian";
  else if IsIdentity(alpha) then
     if Transpose(M_L) eq M_L then
        phi`type := "symmetric";
     else if Transpose(M_L) eq -M_L then
        phi`type := "alternating";
     else
       error "%o does not represent a reflexive form.\n", M;
     end if;
     end if;
  else
    error "%o is not an involution!", alpha;
  end if;
  end if;

  return phi;

end intrinsic;

/* print */

intrinsic Print(phi::RfxFrm)
{.}
printf "%o form on %o\n", phi`type, phi`V;
printf "Defined by the matrix: \n%o", phi`matrix;
end intrinsic;

/* access */

intrinsic FieldAutomorphism(phi::RfxFrm) -> FldAut
{.}
   return phi`aut;
end intrinsic;

intrinsic Involution(phi::RfxFrm) -> FldAut
{.}
  return phi`aut;
end intrinsic;

intrinsic BaseField(phi::RfxFrm) -> Fld
{.}
   return phi`L;
end intrinsic;

intrinsic VectorSpace(phi::RfxFrm) -> ModTupFld
{.}
   return phi`V;
end intrinsic;

intrinsic Matrix(phi::RfxFrm) -> AlgMatElt
{.}
   return phi`matrix;
end intrinsic;

intrinsic Type(phi::RfxFrm) -> MonStgElt
{.}
   return phi`type;
end intrinsic;

/* Evaluation */

intrinsic Evaluate(phi::RfxFrm, u::ModTupFldElt, v::ModTupFldElt) -> FldElt
{.}
   return (u * phi`matrix, phi`aut(v)); 
end intrinsic;

// That's the best I could do at the moment. How does one create
// an intrinsic for a call with several variables?

intrinsic '@'(v::Tup, phi::RfxFrm) -> FldElt
{.}
  return Evaluate(phi, v[1], v[2]);
end intrinsic;

intrinsic Radical(phi::RfxFrm) -> ModTupFld
{.}  
  return Kernel((phi`aut^(-1))(phi`matrix));
end intrinsic;

intrinsic IsNondegenerate(phi::RfxFrm) -> BoolElt
{.}
  V := VectorSpace(phi);
  return Radical(phi) eq sub<V|>;
end intrinsic;

intrinsic GramMatrix(Lamda::ModDed, phi::RfxFrm) -> AlgMatElt[Fld]
{.}
  L := BaseField(phi);
  Z_L := RingOfIntegers(L);
  V := VectorSpace(phi);
  require BaseRing(Lamda) eq Z_L :
    "lattice and form should be defined over the same field.";
  require Dimension(Lamda) eq Dimension(V) :
    "module should be a lattice in the underlying vector space of the form";

  psb := PseudoBasis(Lamda);
  B := Matrix([V!x[2] : x in psb]);
  alpha := phi`aut;
  return B * Matrix(phi) * Transpose(alpha(B));
end intrinsic;

/* this seems unnecessary
intrinsic LatticeMatrix(Lamda::ModDed, phi::RfxFrm) -> AlgMatElt[Fld]
{.}
  L := BaseField(phi);
  Z_L := RingOfIntegers(L);
  V := VectorSpace(phi);
  require BaseRing(Lamda) eq Z_L :
    "lattice and form should be defined over the same field.";
  require Dimension(Lamda) eq Dimension(V) :
    "module should be a lattice in the underlying vector space of the form";

  psb := PseudoBasis(Lamda);
  gens := [];
  for psb_elt in psb do
    I := psb_elt[1];
    v := V!psb_elt[2];
    for g in Generators(I) do
      Append(~gens, g*v);
    end for;
  end for;
  alpha := phi`aut;
  return alpha(Matrix(gens)) * Matrix(phi) * Transpose(Matrix(gens));
end intrinsic;
*/

intrinsic IsIntegral(Lamda::ModDed, phi::RfxFrm) -> BoolElt
{.}
  // Z_L := RingOfIntegers(BaseField(phi));
  alpha := Involution(phi);
  // old version
  //  G := LatticeMatrix(Lamda, phi);
  G := GramMatrix(Lamda, phi);
  I := [x[1] : x in PseudoBasis(Lamda)];
  n := NumberOfRows(G);
  for i in [1..n-1] do
    for j in [i+1..n] do
	    // old version
	    //if G[i,j] notin Z_L then
      if G[i,j] notin (I[i]*alpha(I[j]))^(-1) then
	return false;
      end if;
    end for;
  end for;
  return true;
end intrinsic;

intrinsic DualLattice(Lamda::ModDed, phi::RfxFrm) -> ModDed
{.}
  psb := PseudoBasis(Lamda);
  ideals := [x[1] : x in psb];
  vecs := [x[2] : x in psb];
  B := Matrix(vecs);
  alpha := Involution(phi);
  G := GramMatrix(Lamda, phi);
  // dual_vecs := Columns(Transpose(B) * alpha(G^(-1)));
  dual_vecs := Rows(Transpose(alpha(G^(-1))) * B);
  dual_vecs := [Universe(vecs)!v : v in dual_vecs];
  dual_ideals := [alpha(I)^(-1) : I in ideals];
  dual_psb := [<dual_ideals[i], dual_vecs[i]> : i in [1..#psb]];
  return Module(dual_psb);
end intrinsic;

intrinsic IsUnimodular(Lamda::ModDed, phi::RfxFrm) -> BoolElt
{.}
  return DualLattice(Lamda, phi) eq Lamda;
end intrinsic;

// This is taken from Cohen's paper. Couldn't find an implementation in
// Magma's documentation

intrinsic XGCD_Dedekind(a::RngOrdIdl, b::RngOrdIdl) -> RngOrdIdlElt,RngOrdIdlElt
{.}
  ZZ := Integers();
  R := Order(a);
  require a + b eq ideal<R | R!1> : "ideals must be coprime";
  K := FieldOfFractions(R);
  abs_Z_K := RingOfIntegers(AbsoluteField(K));
  a := ideal<abs_Z_K | a>;
  b := ideal<abs_Z_K | b>;
  abs_Z_K_base := Basis(abs_Z_K);
  z_a := EchelonForm(Transpose(BasisMatrix(a)));
  z_b := EchelonForm(Transpose(BasisMatrix(b)));
  z_a := Rows(Transpose(z_a))[1];
  z_b := Rows(Transpose(z_b))[1];
  z_a := &+[abs_Z_K_base[i] * z_a[i] : i in [1..#abs_Z_K_base]];
  z_b := &+[abs_Z_K_base[i] * z_b[i] : i in [1..#abs_Z_K_base]];
  d, u, v := XGCD(ZZ!z_a, ZZ!z_b);
  if d eq 1 then return R!(u*z_a), R!(v*z_b); end if;
// Could it not happen if a and b are coprime ???
end intrinsic;

intrinsic XGCD_Dedekind(aa::RngOrdFracIdl, bb::RngOrdFracIdl,
			a::FldOrdElt, b::FldOrdElt) -> NumFldElt, NumFldElt
{.}
  require (a ne 0) or (b ne 0) : "Field elements can't be both zero.";
  R := Order(aa);
  require R eq Order(bb) : "Fractional ideals should belong to the same order.";
  del := a * aa + b * bb;
  if a eq 0 then return 0, b^(-1); end if;
  if b eq 0 then return a^(-1), 0; end if;
  I := a * aa * del^(-1);
  J := b * bb * del^(-1);
  R := Order(I);
  assert R eq Order(J);
  I := ideal<R|I>;
  J := ideal<R|J>;
  // sanity check
  assert I + J eq ideal<R | R.1>;
  e, f := XGCD_Dedekind(I,J);
  assert e in I and f in J and e + f eq 1;
  return e/a, f/b;
end intrinsic;

// This is the naive version, which might still give large elements

intrinsic reduce(x::FldOrdElt, a::RngOrdFracIdl) -> FldOrdElt
{.}
  R := Order(a);
  K := FieldOfFractions(R);
  abs_K := AbsoluteField(K);
  abs_Z_K := RingOfIntegers(abs_K);
  a := ideal<abs_Z_K | a>;
  abs_Z_K_base := Basis(abs_Z_K);
  assert Basis(abs_K) eq abs_Z_K_base;
  H := EchelonForm(Transpose(BasisMatrix(a)));
  x := abs_K!x;
  X := Eltseq(x);
  N := NumberOfRows(H);
  //initialize
  i := N;
  y := Vector(X);
  //reduce
  while (i ne 0) do
    q := Floor(y[i] / H[i,i]);
    y -:= q * Transpose(H)[i];
    i -:= 1;
  end while;
  // finished
  return K!(&+[abs_Z_K_base[i] * y[i] : i in [1..#abs_Z_K_base]]);
end intrinsic;

// quite redundant, seems that PseudoBasis does it already.
// Maybe can now change it to get me the invariant factors I want

function HermiteNormalForm(Lamda)
  K := FieldOfFractions(BaseRing(Lamda));
  psb := PseudoBasis(Lamda);
  I := [x[1] : x in psb];
  A := Transpose(Matrix([x[2] : x in psb]));
  n := NumberOfRows(A);
  k := NumberOfColumns(A);
  // initialize
  i := n;
  j := k;
  U := IdentityMatrix(K, k);
  while (i ne 0) do
    // Check zero
    m := j;
    while (m ge 1) and (A[i,m] eq 0) do
      m -:= 1;
    end while;
    if m eq 0 then
      error "Module is not of full rank - error in pseudobasis.";
    else if m lt j then
      perm := SymmetricGroup(k)!(j,m);
      perm_mat := PermutationMatrix(K, perm);
      A := A * perm_mat;
      U := U * perm_mat;
      I := [I[num^perm] : num in [1..k]];
    end if;
    end if;
    // Put 1 on the main diagonal
    diag := [K!1 : num in [1..k]];
    diag[j] := A[i,j]^(-1);
    D := DiagonalMatrix(diag);
    A := A * D;
    U := U * D;
    I[j] := A[i,j] * I[j];
    m := j;
    // loop
    while (m ne 1) do
      m -:= 1;
      while (A[i,m] eq 0) and (m ne 1) do
        m -:= 1;
      end while;
      // Euclidean step
      if (A[i,m] ne 0) then
        del := A[i,m] * I[m] + I[j];
        u, v := XGCD_Dedekind(I[m], I[j], A[i,m], A[i,j]);
        mat := IdentityMatrix(K, k);
        mat[j,j] := v; mat[j,m] := -A[i,m]; mat[m,j] := u;
        A := A * mat; U := U*mat;
        I[m] := I[m] * I[j] * del^(-1);
        I[j] := del;
      end if;
    end while;
    // Final reductions of row i
    for m in [j+1..n] do
      q := reduce(A[i,m], I[m]*I[j]^(-1));
      mat := IdentityMatrix(K,k);
      mat[j,m] := -q;
      A := A * mat; U := U * mat;
    end for;
    i -:= 1;
    j -:= 1;
  end while;
  return U, A, I;
end function;

// It seems that this is also already implemented as ElementaryDivisors

function SmithNormalForm(A, b, a)
  // initialization
  n := NumberOfRows(A);
  assert n eq NumberOfColumns(A);
  assert n eq #a and n eq #b;
  assert not IsEmpty(a) and not IsEmpty(b); 
  R := Order(b[1]);
  assert &and [R eq Order(I) : I in b];
  assert &and [R eq Order(J) : J in a];
// assert &and [&and [A[i,j] in b[i]*a[j]^(-1) : j in [1..n]] : i in [1..n]];
  K := FieldOfFractions(R);
  i := n;
  U := IdentityMatrix(K, n);
  V := IdentityMatrix(K,n);
  if n eq 1 then
    return U, V, [b[1]], [a[1]];
  end if;
  // for debugging
  a_prod := &*[I : I in a];
  b_prod := &*[J : J in b];
  cc := &+ [&+ [A[i,j]*a[j]*b[i]^(-1) : j in [1..n]] : i in [1..n]];
    while (i ge 2) do
      reduce_again := true;
      while (reduce_again) do
	c := 1;
	reduce_again := false;
	while (c gt 0) do
	  // initialize j for row reduction
	  j := i;
	  c := 0;
	  // check zero
	  while (j ne 1) do
	    j -:= 1;
	    while (A[i,j] eq 0) and (j ne 1) do
	      j -:= 1;
	    end while;
	    // Euclidean step
	    if (A[i,j] ne 0) then
	      del := A[i,i] * a[i] + A[i,j] * a[j];
	      u,v := XGCD_Dedekind(a[i], a[j], A[i,i], A[i,j]);
	      // sanity checks
	      assert A[i,i] * u + A[i,j] * v eq 1;
	      assert u in a[i] * del^(-1);
	      assert v in a[j] * del^(-1);
	      mat := IdentityMatrix(K,n);
	      mat[j,j] := A[i,i]; mat[i,j] := -A[i,j]; mat[i,i] := u; mat[j,i] := v;
	      A := A * mat; U := U * mat;
	      a[j] := a[i]*a[j]*del^(-1);
	      a[i] := del;
              assert a_prod eq Determinant(U) * &* [I : I in a];
              assert cc eq &+ [&+ [A[i,j]*a[j]*b[i]^(-1) : j in [1..n]] : i in [1..n]];
	    end if;
	  end while;
	  // initialize j for column reduction
	  j := i;
	  if A[i,i] ne 1 then
	    mat := IdentityMatrix(K,n);
	    mat[i,i] := A[i,i]^(-1);
	    U := U * mat;
	    a[i] := A[i,i] * a[i];
	    A[i,i] := 1;
            assert a_prod eq Determinant(U) * &* [I : I in a];
            assert cc eq &+ [&+ [A[i,j]*a[j]*b[i]^(-1) : j in [1..n]] : i in [1..n]];
	  end if;
	  //check zero
	  while (j ne 1) do
	    j -:= 1;
	    while (A[j,i] eq 0) and (j ne 1) do
	      j -:= 1;
	    end while;
	    // Euclidean step
	    if (A[j,i] ne 0) then
	      del := b[i]^(-1) + A[j,i]*b[j]^(-1);
	      u,v := XGCD_Dedekind(b[i]^(-1), b[j]^(-1), K!1, A[j,i]);
	      // sanity checks
              assert u in b[i]^(-1) * del^(-1);
              assert v in b[j]^(-1) * del^(-1);
	      assert u + A[j,i]*v eq 1;
	      mat := IdentityMatrix(K,n);
              mat[j,j] := 1; mat[i,i] := u; mat[i,j] := v; mat[j,i] := -A[j,i];
	      A := mat * A; V := mat * V;
	      b[j] := b[i]*b[j]*del; b[i] := del^(-1);
	      c +:= 1;
              assert b_prod eq Determinant(V) * &* [I : I in b];
              assert cc eq &+ [&+ [A[i,j]*a[j]*b[i]^(-1) : j in [1..n]] : i in [1..n]];
	    end if;
	  end while;
          //printf "Norm(A[%o,%o] * a[%o] * b[%o]^(-1)) = %o\n", i, i, i, i,
          //	    Norm(Norm(A[i,i]*a[i]*b[i]^(-1)));
	end while;
	// check the rest of the matrix
	bb := a[i]*b[i]^(-1);
	for k in [1..i-1] do
	  for l in [1..i-1] do
	    if not (A[k,l] * a[l] * b[k]^(-1) subset bb) then
	      del := b[i] * b[k]^(-1);
	      _ := exists(d){x : x in Generators(del) |
			     A[k,l]*x notin a[i]*a[l]^(-1)};
	      mat := IdentityMatrix(K,n);
	      mat[i,k] := d;
	      A := mat * A; V := mat * V;
              assert b_prod eq Determinant(V) * &* [I : I in b];
              assert cc eq &+ [&+ [A[i,j]*a[j]*b[i]^(-1) : j in [1..n]] : i in [1..n]];
	      reduce_again := true;
	      break;
	    end if;
	  end for;
	  if reduce_again then break; end if;
	end for;
      end while;
      i -:= 1;
    end while;
    mat := IdentityMatrix(K,n);
    mat[1,1] := A[1,1]^(-1);
    U := U * mat;
    a[1] := A[1,1] * a[1];
    A[1,1] := 1;
    assert a_prod eq Determinant(U) * &* [I : I in a];
    assert cc eq &+ [&+ [A[i,j]*a[j]*b[i]^(-1) : j in [1..n]] : i in [1..n]];
    return U, V, b, a;
end function;


intrinsic InvariantFactors(Pi::ModDed, Lamda::ModDed) -> SeqEnum[RngOrdIdl]
{This function Computes the invariant factors of Pi relative to Lamda}
// require Pi subset Lamda : "First lattice should be contained in the second";
  psb_pi := PseudoBasis(Pi);
  psb_lam := PseudoBasis(Lamda);
  H := Transpose(Matrix([x[2] : x in psb_lam]));
  W := Transpose(Matrix([x[2] : x in psb_pi]));
  A := H^(-1)*W;
  a := [x[1] : x in psb_pi];
  b := [x[1] : x in psb_lam];
  U, V, b_prime, a_prime := SmithNormalForm(A, b, a);
  // sanity checks
  R := BaseRing(Pi);
  K := FieldOfFractions(R);
  n := #a;
  assert V*A*U eq IdentityMatrix(K,n);
  assert &*[I : I in a] eq Determinant(U) * &* [I : I in a_prime];
  assert &*[J : J in b] eq Determinant(V) * &* [J : J in b_prime]; 
  assert &and [&and [U[i,j] in a[i]*a_prime[j]^(-1) : j in [1..n]] :
		      i in [1..n]];
  assert &and [&and [V[i,j] in b_prime[i]*b[j]^(-1) : j in [1..n]] :
		      i in [1..n]];
  del := [a_prime[i]*b_prime[i]^(-1) : i in [1..n]];
  return [ideal<R|d> : d in del]; 
end intrinsic;

intrinsic Discriminant(Lamda::ModDed, Pi::ModDed) -> RngOrdIdl
{.}
  return &* InvariantFactors(Pi, Lamda);
end intrinsic;

intrinsic Discriminant(Lamda::ModDed, phi::RfxFrm) -> RngOrdIdl
{.}
  Lamda_dual := DualLattice(Lamda, phi);
  alpha := Involution(phi);
  F := FixedField(alpha);
  Z_F := RingOfIntegers(F);
  return Discriminant(Lamda_dual, Lamda) meet Z_F;
end intrinsic;

intrinsic Completion(Lamda::ModDed, P::RngOrdIdl) -> ModTupRng[RngPad]
{returns a matrix whose columns are a basis for the free module}
  Z_L := BaseRing(Lamda);
  Z_L_p, phi_p := Completion(Z_L, P);
  pi := UniformizingElement(Z_L_p);
  psb := PseudoBasis(Lamda);
  n := Dimension(Lamda);
  r := [pi^Minimum([Valuation(phi_p(g)) : g in Generators(x[1])]) : x in psb];
  B := [[r[i]*phi_p(psb[i][2][j]) : j in [1..n]] : i in [1..n]];
  return RSpaceWithBasis(Matrix(B));
end intrinsic;

function get_gens(Lamda)
  psb := PseudoBasis(Lamda);
  gens := [];
  for psb_elt in psb do
    I := psb_elt[1];
    v := psb_elt[2];
    for g in Generators(I) do
      Append(~gens, g*v);
    end for;
  end for;
  return gens;
end function;

// intrinsic InvariantFactors(Lamda::ModDed, Pi::ModDed) -> SeqEnum[

procedure sanity(Lamda, phi)
  Lamda_d := DualLattice(Lamda, phi);
  V := VectorSpace(phi);
  Z_L := RingOfIntegers(BaseField(phi));
  gens1 := [V!v : v in get_gens(Lamda)];
  gens2 := [V!v : v in get_gens(Lamda_d)];
  assert &and [&and [phi(<u,v>) in Z_L : u in gens1] : v in gens2];
end procedure;

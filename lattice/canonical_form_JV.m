function IsWellRounded(A)
  L := LatticeWithGram(A);
  minA := ShortestVectors(L);
  LminA := Lattice(ChangeRing(Matrix(minA),Rationals()), A);
  return Rank(LminA) eq Rank(L);
end function;

function V_wr_cvp(A)
  assert IsWellRounded(A);
  L := LatticeWithGram(A);
  minA := ShortestVectors(L);  // only includes one of v, -v, but that's enough
  LminA := Lattice(ChangeRing(Matrix(minA),Rationals()), A);
  Zn := LatticeWithGram(A);
  Q, quo := Zn / LminA;
  cs := [q@@quo : q in Q];
  B := ChangeRing(Matrix(Basis(LminA)),Rationals());
  L_B := LatticeWithGram(B * A * Transpose(B));
  ret := [ChangeRing(v, Rationals()) : v in minA];
  Binv := B^(-1);
  for c in cs do
    if IsZero(c) then 
      continue;
    else
      cQQ := ChangeRing(c,Rationals());
      ret cat:= [cQQ - ChangeRing(w,Rationals())*B : w in ClosestVectors(L_B, Vector(cQQ*Binv))];
    end if; 
  end for;
  return ret;
end function;

function satspan(v, A)
  v_mat := Matrix(v);
  d := Denominator(v_mat);
  dv_mat := ChangeRing(d*v_mat, Integers());
  // hnf_mat := VerticalJoin(dv_mat, d*IdentityMatrix(Integers(),Ncols(v_mat)));
  H := HermiteForm(dv_mat);
  H_basis := [Vector(r) : r in Rows(H)[1..Rank(H)]];
  sat_basis := 
  ChangeRing(Matrix([GCD(Eltseq(v))^(-1) * ChangeRing(v,Rationals()) 
     : v in H_basis]), Rationals());
  return Lattice(sat_basis, A);
end function;

function V_cvp(A)
  A := ChangeRing(A, Rationals());
  L := LatticeWithGram(A);
  minA := &cat[[v,-v] : v in ShortestVectors(L)];
  LminA := Lattice(ChangeRing(Matrix(minA),Rationals()), A);
  L1 := satspan(Basis(LminA), A);
  B1 := ChangeRing(Matrix(Basis(L1)),Rationals());
  A1 := B1 * A * Transpose(B1);
  // B2 := Matrix(Basis(Kernel(A*Transpose(B1))));
  B2 := Transpose(Matrix(Basis(Kernel(A*Transpose(B1)))));
  proj := B2 * (Transpose(B2)*A*B2)^(-1) * Transpose(A*B2);
  B2 := ChangeRing(Matrix(Basis(Lattice(Transpose(proj)))), Rationals());
  A2 := B2 * A * Transpose(B2);
  r := Rank(L1);
  if (r eq Rank(L)) then
    V_cvp_A2 := [];
  else
    V_cvp_A2 := V_cvp(A2);
  end if;
  A1_part := [Vector(Rationals(), v)*B1 : v in V_wr_cvp(A1)];
  A2_part := [Vector(v)*B2 : v in V_cvp_A2];
  union_A2_part := &cat[ClosestVectors(L,v) : v in A2_part];
  VA := A1_part cat union_A2_part;
  return [v : v in VA | v ne 0];
end function;

function T1(W)
  a := Maximum(Eltseq(W))+1;
  b := a + 1;
  p := Nrows(W);
  W_prime := MatrixRing(Integers(),p+2)!0;
  for i in [1..p] do
		for j in [i+1..p] do
			W_prime[i,j] := W[i,j];
		end for;
		W_prime[i,p+1] := W[i,i];
		W_prime[i,p+2] := a;
	end for;
	W_prime[p+1,p+2] := b;
	for i in [1..p+2] do
		for j in [1..i-1] do
			W_prime[i,j] := W_prime[j,i];
		end for;
  end for;
  return W_prime;
end function;

function bits(s,w)
  return [BitwiseAnd(ShiftRight(s,k),1) : k in [0..w-1]];
end function;

function T2(W)
  // Apparently the sort key doesn't really matter,
  // as the labels will be determined by the binary digits.
  // S := Sort([s : s in Set(Eltseq(W))], 
  // func< x,y | Abs(x) eq Abs(y) select x-y else Abs(x)-Abs(y) >);
  S := Sort([s : s in Set(Eltseq(W))]);
  w := Ceiling(Log(2,#S));
  all_bits := [bits(s,w) : s in [0..#S-1]];
  all_bits_bool := [[all_bits[s][k] eq 1 : k in [1..w]]
      : s in [1..#S]];
  p := Nrows(W);
  lut := AssociativeArray(S);
  for i->s in S do
  lut[s] := i;
  end for;
  vertices := [];
  edges := [];
  for i in [1..p] do
  v_nbrs := [[<i_prime,k-1> : i_prime in [i+1..p] | all_bits_bool[lut[W[i,i_prime]]][k] ] cat [<i,k_prime> : k_prime in [k..w-1]] : k in [1..w]];
  vertices cat:= [<i,k> : k in [0..w-1]];
  edges cat:= v_nbrs;
  end for;
  vertices := {@ v : v in vertices @};
  edges := [{@ e : e in es @} : es in edges];
  wts := [v[2] : v in vertices];
  G := Graph<vertices|edges>;
  AssignLabels(VertexSet(G),wts);
  return G;
end function;

function U_V(A)
  A := ChangeRing(A, Rationals());
  VA := V_cvp(A);
  // This is not really needed, we just keep track of the weights
  // G_A := CompleteGraph(#VA);
  B := ChangeRing(Matrix(VA),Rationals());
  W := B * A * Transpose(B);
  G := T1(W);
  T2G := T2(G);
  T2G_can, _, _, labels := CanonicalGraphMap(T2G);
  p := Nrows(G);
  S := [s : s in Set(Eltseq(G))];
  w := Ceiling(Log(2,#S));
  perm := [Minimum([Index(labels, <i,k>) : k in [0..w-1]]) : i in [1..p]];
  // this is the ordering of the vertices in G
  perm_inv := [Index(perm, i) : i in [1..#perm]];
  p -:= 2;
  v := [VA[i] : i in perm_inv | i le p];
  QA := ChangeRing(Transpose(Matrix(v)), Integers());
  H, U_inv := HermiteForm(QA);
  U := U_inv^(-1);
  assert U*H eq Transpose(Matrix(v));
  return U;
end function;

/*
function CanonicalForm(A)
  U := U_V(A);
  can_A := Transpose(U)*A*U;
  return can_A;
end function;
*/

intrinsic CanonicalForm(A::AlgMatElt) -> AlgMatElt
{Return a canonical form for the positive definite matrix A.}
  Ared := GramMatrix(LLL(LatticeWithGram(A)));
  U := U_V(Ared);
  can_A := Transpose(U)*Ared*U;
  return can_A;
end intrinsic;

intrinsic CanonicalForm(L::Lat) -> AlgMatElt
{Return a canonical form for L.}
  b := Basis(L);
  gram := InnerProductMatrix(L);
  b := [ChangeRing(Vector(Eltseq(x)), Rationals()) : x in b];
  A := Matrix(b)*gram*Transpose(Matrix(b));
  return CanonicalForm(A);
end intrinsic;

/*
intrinsic CanonicalForm(L::ModDedLat) -> AlgMatElt
{Return a canonical form for L.}
  lat := ZLattice(L);
  return CanonicalForm(lat);
end intrinsic;

intrinsic CanonicalForm(L::LatNF) -> AlgMatElt
{Return a canonical form for L.}
  return CanonicalForm(LatticeFromLatNF(L));
end intrinsic;
*/

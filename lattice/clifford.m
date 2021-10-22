freeze;
// In this file we implement various methods related to the even clifford functor

// This was constructed only for quaternary lattices, change later

function RationalEvenClifford(M)
  C_Q, V_Q, emb_Q := CliffordAlgebra(1/2*M);
  dim := Dimension(V_Q);
  e := [emb_Q(V_Q.i) : i in [1..dim]];
  C_Q_gr := [[&*([1] cat [e[i] : i in I]) : I in Subsets({1..dim}, k)] : k in [0..dim]];
  basis_C_Q := &cat C_Q_gr;
  // we construct the even and odd (rational) clifford algebras.
  basis_C_0 := &cat [C_Q_gr[1 + 2*k] : k in [0..dim div 2]];
  C_0_Q := sub<C_Q | basis_C_0>;
  return C_0_Q;
end function;

// Currently this only works for primitive lattices
intrinsic EvenClifford(M::AlgMatElt[RngInt]) ->
	  AlgGen[RngInt], Map[AlgGen[RngInt], AlgGen[RngInt]],
          Map[AlgGen[RngInt], AlgGen[RngInt]]
{Construct the even Clifford algebra of the lattice with Gram matrix M.}
  C_Q, V_Q, emb_Q := CliffordAlgebra(1/2*M);
  dim := Dimension(V_Q);
  e := [emb_Q(V_Q.i) : i in [1..dim]];
  // We want to make sure the two following lines use the same order, so we sort first
  subsets := [Sort([[y : y in x] : x in Subsets({1..dim},k)]) : k in [0..dim]];
  C_Q_gr := [[&*([1] cat [e[i] : i in I]) : I in subsets[1+k]] : k in [0..dim]];
  C_Q_gr_rev := [[&*([1] cat Reverse([e[i] : i in I]))
		  : I in subsets[1+k]] : k in [0..dim]];
  basis_C_Q := &cat C_Q_gr;
  basis_rev := &cat C_Q_gr_rev;
  // omega_Q is the reversal involution induced by M
  omega_Q := hom< C_Q -> C_Q | [basis_rev[Index(basis_C_Q, C_Q.i)] : i in [1..#basis_C_Q]]>;
  // we construct the even and odd (rational) clifford algebras.
  basis_C_0 := &cat [C_Q_gr[1 + 2*k] : k in [0..dim div 2]];
  basis_C_1 := &cat [C_Q_gr[1 + 2*k + 1] : k in [0..(dim-1) div 2]];
  V_C_Q, vec_Q := VectorSpace(C_Q);
  V_C := ChangeRing(V_C_Q, Integers());
  C_0_Q := sub<C_Q | basis_C_0>;
  C_1_Q, emb_C_1_Q := sub<V_C_Q | [vec_Q(b) : b in basis_C_1]>;
  C_1, emb_C_1 := sub<V_C | [ChangeRing(v, Integers()) : v in Basis(C_1_Q)]>;
  // We choose a generator for the odd clifford
  // What we really need to do is just to find a linear combination of the generators
  // such that we get a linearly independent set of vectors.
  R<[a]> := PolynomialRing(Rationals(), #basis_C_1);
  mat := &+[a[i]*ChangeRing(Matrix([Solution(Matrix(Basis(C_1_Q)),vec_Q(b * basis_C_1[i]))
				    : b in basis_C_0]),R) : i in [1..#basis_C_1]];
  det := Determinant(mat);
  //  det_fac := Factorization(Determinant(mat));
  // Now we want the determinant to be 1 (or -1)
  // There should be a better way of enumeration on this scheme
  a_vals := CartesianPower([-1,0,1],#a);
  
  for a_val in a_vals do
      if Abs(Evaluate(det, a_val)) eq 1 then
	  x := &+[a_val[i]*basis_C_1[i] : i in [1..#a_val]];
	  //  x := basis_C_1[1];
	  C_0_Q_x := sub<V_C_Q | [vec_Q(b * x) : b in basis_C_0] >;
	  x_C_0_Q := sub<V_C_Q | [vec_Q(x * b) : b in basis_C_0] >;
	  assert (C_0_Q_x eq C_1_Q) and (x_C_0_Q eq C_1_Q);
	  C_0_x := sub<V_C | [ChangeRing(vec_Q(b * x), Integers()) : b in basis_C_0] >;
	  basis_x_C_0 := [ChangeRing(vec_Q(x * b), Integers()) : b in basis_C_0];
	  x_C_0 := sub<V_C | basis_x_C_0 >;
	  assert (C_0_x eq C_1) and (x_C_0 eq C_1);
	  // We find the descent data iota
	  iota_vecs := [Solution(Matrix(basis_x_C_0),
			 ChangeRing(vec_Q(omega_Q(a)*x), Integers()))
			 : a in basis_C_0];
	  iota_vals := [&+[v[i] * (C_0_Q!(basis_C_0[i])) : i in [1..#basis_C_0]]
			: v in iota_vecs];
	  // This making iota into an isomorphism (rather than an involution)
	  // However, we actually need the invoutive iota (omgea iota, or iota bar)
	  //	  iota_vals := [C_0_Q!(omega_Q(C_0_Q!i_val)) : i_val in iota_vals];
	  iota_mat := Matrix(iota_vals);
	  assert &and[omega_Q(basis_C_0[i])*x eq x*iota_vals[i] : i in [1..#basis_C_0]];   
	  //assert &and[omega_Q(basis_C_0[i])*x eq x*omega_Q(iota_vals[i]) : i in [1..#basis_C_0]];
	  B := Matrix([C_0_Q!x : x in basis_C_0]);
	  iota_Q := hom<C_0_Q -> C_0_Q | Rows(B^(-1)*Matrix(iota_vals))>;
	  assert &and[omega_Q(a)*x eq x*iota_Q(a) : a in Basis(C_0_Q)];                    
	  // assert &and[omega_Q(a)*x eq x*omega_Q(iota_Q(a)) : a in Basis(C_0_Q)];
	  // we abbreviate for the next line                                                   
	  b := Basis(C_0_Q);
	  mult_table := &cat&cat[[ Eltseq(Solution(Matrix(b), b[i]*b[j]))
				   : j in [1..#b]] : i in [1..#b]];
	  C_0 := Algebra<Integers(), #b | mult_table>;
	  iota := hom<C_0 -> C_0 | Rows(B^(-1)*Matrix(iota_vals))>;
	  iota_mat := Matrix([iota(C_0.i) : i in [1..Dimension(C_0)]]);
	  if (Rank(iota_mat-1) eq (Dimension(C_0) div 2)) then
	      break;
	  end if;
      end if;
  end for;
  omega_mat := Matrix([[Integers() | x : x in Eltseq(C_0_Q!omega_Q(C_Q!(C_0_Q.i)))]
		       : i in [1..Dimension(C_0_Q)]]);
  omega := hom<C_0 -> C_0 | Rows(omega_mat)>;
  // We need omega for the norm form.
  delta := C_0!Eltseq(C_0_Q!(Center(C_0_Q).2));
  Z_C_0, emb_Z := sub<C_0 | 1, delta>;
  nm := hom<C_0 -> Z_C_0 | x :-> omega(x)*x>;
  return C_0, nm, iota;
end intrinsic;

function a_lattice(a_val, det, basis_C_1, basis_C_0, vec_Q, V_C_Q, C_0_Q, C_1_Q, C_1,
		   C_Q, V_C, omega_Q)
    assert Abs(Evaluate(det, a_val)) eq 1;
    x := &+[a_val[i]*basis_C_1[i] : i in [1..#a_val]];
    C_0_Q_x := sub<V_C_Q | [vec_Q(b * x) : b in basis_C_0] >;
    x_C_0_Q := sub<V_C_Q | [vec_Q(x * b) : b in basis_C_0] >;
    assert (C_0_Q_x eq C_1_Q) and (x_C_0_Q eq C_1_Q);
    C_0_x := sub<V_C | [ChangeRing(vec_Q(b * x), Integers()) : b in basis_C_0] >;
    basis_x_C_0 := [ChangeRing(vec_Q(x * b), Integers()) : b in basis_C_0];
    x_C_0 := sub<V_C | basis_x_C_0 >;
    assert (C_0_x eq C_1) and (x_C_0 eq C_1);
    iota_vecs := [Solution(Matrix(basis_x_C_0),
                           ChangeRing(vec_Q(omega_Q(a)*x), Integers()))
                  : a in basis_C_0];
    iota_vals := [&+[v[i] * (C_0_Q!(basis_C_0[i])) : i in [1..#basis_C_0]]
                  : v in iota_vecs];
    // making iota into an isomorphism (rather than an involution)                        
//     iota_vals := [C_0_Q!(omega_Q(C_0_Q!i_val)) : i_val in iota_vals];
    iota_mat := Matrix(iota_vals);
    assert &and[omega_Q(basis_C_0[i])*x eq x*iota_vals[i] : i in [1..#basis_C_0]];
    B := Matrix([C_0_Q!x : x in basis_C_0]);
    iota_Q := hom<C_0_Q -> C_0_Q | Rows(B^(-1)*Matrix(iota_vals))>;
    assert &and[omega_Q(a)*x eq x*iota_Q(a) : a in Basis(C_0_Q)];
    // we abbreviate for the next line                                                    
    b := Basis(C_0_Q);
    mult_table := &cat&cat[[ Eltseq(Solution(Matrix(b), b[i]*b[j]))
                             : j in [1..#b]] : i in [1..#b]];
    C_0 := Algebra<Integers(), #b | mult_table>;
    iota := hom<C_0 -> C_0 | Rows(B^(-1)*Matrix(iota_vals))>;
    iota_mat := Matrix([iota(C_0.i) : i in [1..Dimension(C_0)]]);
    if (Rank(iota_mat-1) ne (Dimension(C_0) div 2)) then
	return false, _;
    end if;
    omega_mat := Matrix([[Integers() | x : x in Eltseq(C_0_Q!omega_Q(C_Q!(C_0_Q.i)))]
                       : i in [1..Dimension(C_0_Q)]]);
    omega := hom<C_0 -> C_0 | Rows(omega_mat)>;
    // We need omega for the norm form.                                                        
    delta := C_0!Eltseq(C_0_Q!(Center(C_0_Q).2));
    Z_C_0, emb_Z := sub<C_0 | 1, delta>;
    nm := hom<C_0 -> Z_C_0 | x :-> omega(x)*x>;
    return true, InverseEvenClifford(C_0, nm, iota);
end function;

intrinsic InverseEvenClifford(C_0::AlgGen[RngInt],
			      nm::Map[AlgGen[RngInt], AlgGen[RngInt]],
			      iota::Map[AlgGen[RngInt], AlgGen[RngInt]]) -> AlgMatElt[RngInt]
{Given the even Clifford algebra, the norm map on it (induced by the reversal) and the descent data iota, returns the lattice.}
  basisker := Basis(Kernel(Matrix([iota(C_0.i) : i in [1..Dimension(C_0)]])-1));
  C_0_inv := [C_0!x : x in basisker];
  return Matrix([[Integers()!(nm(x+y) - nm(x) - nm(y))
		  : x in C_0_inv] : y in C_0_inv]);
end intrinsic;

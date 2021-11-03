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
  norm := Norm(Norm(LatticeFromLat(LatticeWithGram(M))));
  dim := Dimension(V_Q);
  e := [emb_Q(V_Q.i) : i in [1..dim]];
  // We want to make sure the two following lines use the same order, so we sort first
  subsets := [Sort([[y : y in x] : x in Subsets({1..dim},k)]) : k in [0..dim]];
  C_Q_gr := [[norm^(-(k div 2)) * &*([1] cat [e[i] : i in I]) : I in subsets[1+k]]
	     : k in [0..dim]];
  C_Q_gr_rev := [[norm^(-(k div 2)) * &*([1] cat Reverse([e[i] : i in I]))
		  : I in subsets[1+k]] : k in [0..dim]];
  basis_C_Q := &cat C_Q_gr;
  basis_rev := &cat C_Q_gr_rev;
  // we construct the even and odd (rational) clifford algebras.
  basis_C_0 := &cat [C_Q_gr[1 + 2*k] : k in [0..dim div 2]];
  basis_C_1 := &cat [C_Q_gr[1 + 2*k + 1] : k in [0..(dim-1) div 2]];
  V_C_Q, vec_Q := VectorSpace(C_Q);
  // omega_Q is the reversal involution induced by M
  omega_images := [&+[y[i]*basis_rev[i] : i in [1..2^dim]]
		   where y := Solution(Matrix(basis_C_Q),V_C_Q.j) : j in [1..2^dim]];
  omega_Q_V := hom<V_C_Q -> V_C_Q | omega_images>;
//  omega_Q_V := hom< V_C_Q -> V_C_Q |
//		  [basis_rev[Index(basis_C_Q, C_Q.i)] : i in [1..#basis_C_Q]]>;
  omega_Q := map<C_Q -> C_Q | x :-> (omega_Q_V(vec_Q(x)))@@vec_Q>;
  V_C := ChangeRing(V_C_Q, Integers());
  C_0_Q := sub<C_Q | basis_C_0>;
  C_1_Q, emb_C_1_Q := sub<V_C_Q | [vec_Q(b) : b in basis_C_1]>;
  C_1, emb_C_1 := sub<V_C | [Vector(ChangeRing(Solution(Matrix(basis_C_Q),v), Integers()))
			     : v in basis_C_1]>;
  // We choose a generator for the odd clifford
  // What we really need to do is just to find a linear combination of the generators
  // such that we get a linearly independent set of vectors.
  R<[a]> := PolynomialRing(Rationals(), #basis_C_1);
  mat := &+[a[i]*ChangeRing(Matrix([Solution(Matrix(basis_C_1),vec_Q(b * basis_C_1[i]))
				    : b in basis_C_0]),R) : i in [1..#basis_C_1]];
  det := Determinant(mat);
  //  det_fac := Factorization(Determinant(mat));
  // Now we want the determinant to be 1 (or -1)
  // There should be a better way of enumeration on this scheme
  B := Floor(Determinant(M)^(1/8));
  enum_set := [0] cat &cat[[i,-i] : i in [1..B]];
  a_vals := CartesianPower(enum_set,#a);
  
  for a_val in a_vals do
      if Abs(Evaluate(det, a_val)) eq 1 then
	  x := &+[a_val[i]*basis_C_1[i] : i in [1..#a_val]];
	  //  x := basis_C_1[1];
	  C_0_Q_x := sub<V_C_Q | [vec_Q(b * x) : b in basis_C_0] >;
	  x_C_0_Q := sub<V_C_Q | [vec_Q(x * b) : b in basis_C_0] >;
	  assert (C_0_Q_x eq C_1_Q) and (x_C_0_Q eq C_1_Q);
	  C_0_x := sub<V_C | [ChangeRing(Solution(Matrix(basis_C_Q),vec_Q(b * x)),
					 Integers()) : b in basis_C_0] >;
	  basis_x_C_0 := [ChangeRing(Solution(Matrix(basis_C_Q), vec_Q(x * b)),
				     Integers()) : b in basis_C_0];
	  x_C_0 := sub<V_C | basis_x_C_0 >;
	  assert (C_0_x eq C_1) and (x_C_0 eq C_1);
	  // We find the descent data iota
	  iota_vecs := [Solution(Matrix(basis_x_C_0),
			 ChangeRing(vec_Q(omega_Q(a)*x), Integers()))
			 : a in basis_C_0];
	  iota_vals := [&+[v[i] * (C_0_Q!(basis_C_0[i])) : i in [1..#basis_C_0]]
			: v in iota_vecs];
	  // This making iota into an isomorphism (rather than an involution)
	  iota_vals := [C_0_Q!(omega_Q(C_0_Q!i_val)) : i_val in iota_vals];
	  iota_mat := Matrix(iota_vals);
	  //assert &and[omega_Q(basis_C_0[i])*x eq x*iota_vals[i] : i in [1..#basis_C_0]];   
	  assert &and[omega_Q(basis_C_0[i])*x eq x*omega_Q(iota_vals[i]) : i in [1..#basis_C_0]];
	  B := Matrix([C_0_Q!x : x in basis_C_0]);
	  iota_Q := hom<C_0_Q -> C_0_Q | Rows(B^(-1)*Matrix(iota_vals))>;
//	  assert &and[omega_Q(a)*x eq x*iota_Q(a) : a in Basis(C_0_Q)];                    
	  assert &and[omega_Q(a)*x eq x*omega_Q(iota_Q(a)) : a in Basis(C_0_Q)];
	  // we abbreviate for the next line                                                   
	  b := Basis(C_0_Q);
	  mult_table := &cat&cat[[ Eltseq(Solution(Matrix(b), b[i]*b[j]))
				   : j in [1..#b]] : i in [1..#b]];
	  C_0 := Algebra<Integers(), #b | mult_table>;
	  iota := hom<C_0 -> C_0 | Rows(B^(-1)*Matrix(iota_vals))>;
	  iota_mat := Matrix([iota(C_0.i) : i in [1..Dimension(C_0)]]);
	  omega_mat := Matrix([[Integers() | x : x in Eltseq(C_0_Q!omega_Q(C_Q!(C_0_Q.i)))]
			       : i in [1..Dimension(C_0_Q)]]);
	  if (Rank(iota_mat-omega_mat) eq (Dimension(C_0) div 2)) then
	      break;
	  end if;
      end if;
  end for;
  V_C_0 := Module(C_0);
  omega_V := hom<V_C_0 -> V_C_0 | Rows(omega_mat)>;
  omega := map<C_0 -> C_0 | x :-> C_0!(omega_V(V_C_0!x))>;
  // We need omega for the norm form.
  delta_Q := C_0_Q!(Center(C_0_Q).2);
  delta := C_0!Eltseq(delta_Q*Denominator(delta_Q));
  Z_C_0, emb_Z := sub<C_0 | 1, delta>;
  nm := map<C_0 -> Z_C_0 | x :-> omega(x)*x>;
  return C_0, nm, iota*omega;
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
    nm := map<C_0 -> Z_C_0 | x :-> omega(x)*x>;
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

// TODO : migth be we could do that with only the integral data
function makeZ_K_Order(C_0_Q, iota_Q, omega_Q, delta)
    Z_C_0_Q := Center(C_0_Q);
    delta_Q := C_0_Q!Z_C_0_Q.2;
    K<delta_K> := ext< Rationals() | MinimalPolynomial(delta_Q)>;
    delta_mat := Matrix([delta_Q * C_0_Q.i : i in [1..8]]);
    basisker := Basis(Kernel(Matrix([iota_Q(C_0_Q.i) : i in [1..Dimension(C_0_Q)]])-1));
    C_0_Q_inv := [C_0_Q!x : x in basisker];
    X := Matrix(C_0_Q_inv);
    X_tmp := VerticalJoin(X, X * delta_mat);
    X_tmp_inv := X_tmp^(-1);
    nfl_basis := [Vector([X_tmp_inv[i,j] + delta_K * X_tmp_inv[i,j+4]
			  : j in [1..4]]) : i in [1..8]];
    basis_mat_K := Matrix(Basis(NumberFieldLattice(nfl_basis)));
    basis_mat := Matrix([Eltseq(Transpose(Matrix([Eltseq(basis_mat_K[i,j])
						  : j in [1..4]]))) : i in [1..4]]);
    K_basis := [C_0_Q!x : x in Rows(basis_mat * X_tmp)];
    b := K_basis;
    nm_Q := map<C_0_Q -> Z_C_0_Q | x :-> omega_Q(x)*x>;
    F_basis := K_basis cat [delta_Q * x : x in K_basis];
    mult_table := &cat&cat[[[x[1,j] + delta_K * x[1,j+4] : j in [1..4]]
			    where x := Solution(Matrix(F_basis),b[i]*b[k])
			    : k in [1..#b]] : i in [1..#b]];
    A := Algebra<K, #b | mult_table>;
    nm_A := map<A -> K | x :->  y[1] + y[2]*delta_K
				where y := nm_Q(&+[x[i]*b[i] : i in [1..4]])>;
    gram := Matrix([[nm_A(x+y)-nm_A(x)-nm_A(y)
		     : x in Basis(A)] : y in Basis(A)]);
    assert Determinant(gram) eq 1;
    //    return A, nm_A;
    // This is for retruning the integral one
    S := EquationOrder(MinimalPolynomial(delta));
    // When S is not maximal, the above is not guaranteed to work,
    // since NFL assumes we are over Z_K
    assert IsMaximal(S);
    delta_S := S.2;
    A_S := Algebra<S,#b | [S!Eltseq(x) : x in mult_table]>;
    nm_A_S := map<A_S -> S | x :->  y[1] + y[2]*delta_S
				where y := nm_Q(&+[x[i]*b[i] : i in [1..4]])>;
    gram := Matrix([[nm_A_S(x+y)-nm_A_S(x)-nm_A_S(y)
		     : x in Basis(A_S)] : y in Basis(A_S)]);
    assert Determinant(gram) eq 1;
    return A_S, nm_A_S;
end function;

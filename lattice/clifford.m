// freeze;
// In this file we implement various methods related to the even clifford functor

import "../neighbors/neighbor-CN1.m" : BuildNeighborProc;
import "../neighbors/neighbor-CN1.m" : BuildNeighbor;
import "../neighbors/neighbor-CN1.m" : GetNextNeighbor;

// This was constructed only for quaternary lattices, change later

function RationalEvenClifford(M : Isometries := [])
  C_Q, V_Q, emb_Q := CliffordAlgebra(1/2*M);
  dim := Dimension(V_Q);
  e := [emb_Q(V_Q.i) : i in [1..dim]];
  C_Q_gr := [[&*([1] cat [e[i] : i in I]) : I in Subsets({1..dim}, k)] : k in [0..dim]];
  basis_C_Q := &cat C_Q_gr;
  // we construct the even and odd (rational) clifford algebras.
  basis_C_0 := &cat [C_Q_gr[1 + 2*k] : k in [0..dim div 2]];
  C_0_Q := sub<C_Q | basis_C_0>;
  basismat := Matrix([C_0_Q!x : x in basis_C_0]);
  C_0_iso := [];
  for s in Isometries do
      s_e := [emb_Q(r) : r in Rows(s)];
      s_C_Q_gr := [[&*([1] cat [s_e[i] : i in I]) : I in Subsets({1..dim}, k)] : k in [0..dim]];
      s_C_0 := &cat [s_C_Q_gr[1 + 2*k] : k in [0..dim div 2]];
      Append(~C_0_iso, Matrix([C_0_Q!l : l in s_C_0])*basismat^(-1));
  end for;
  return C_0_Q, emb_Q, C_0_iso;
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
  omega_Q := map<C_Q -> C_Q | x :-> (omega_Q_V(vec_Q(x)))@@vec_Q>;
  V_C := ChangeRing(V_C_Q, Integers());
  C_0_Q := sub<C_Q | basis_C_0>;
  C_1_Q, emb_C_1_Q := sub<V_C_Q | [vec_Q(b) : b in basis_C_1]>;
  C_1, emb_C_1 := sub<V_C | [Vector(ChangeRing(Solution(Matrix(basis_C_Q),v), Integers()))
			     : v in basis_C_1]>;
  x := emb_Q(ShortestVector(LatticeWithGram(M)));
  assert x^2 eq 1;
  /*
  // We choose a generator for the odd clifford
  // What we really need to do is just to find a linear combination of the generators
  // such that we get a linearly independent set of vectors.
  // We want the generator to come from V so that iota will be an involution
  // R<[a]> := PolynomialRing(Rationals(), #basis_C_1);
  R<[a]> := PolynomialRing(Rationals(), #basis_C_1[1..4]);
  mat := &+[a[i]*ChangeRing(Matrix([Solution(Matrix(basis_C_1),vec_Q(b * basis_C_1[i]))
			//	    : b in basis_C_0]),R) : i in [1..#basis_C_1]];
				    : b in basis_C_0]),R) : i in [1..#a]];
  det := Determinant(mat);
  //  det_fac := Factorization(Determinant(mat));
  // Now we want the determinant to be 1 (or -1)
  // There should be a better way of enumeration on this scheme
  // B := Floor(Determinant(M)^(1/8));
  B := Floor(Determinant(M)^(1/4));
  enum_set := [0] cat &cat[[i,-i] : i in [1..B]];
  a_vals := CartesianPower(enum_set,#a);

  assert exists(a_val){a_val : a_val in a_vals | Abs(Evaluate(det, a_val)) eq 1};
  x := &+[a_val[i]*basis_C_1[i] : i in [1..#a_val]];
 */
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
  basis_mat := ChangeRing(Matrix(basis_C_Q), Integers());
  iota_vecs := [Solution(Matrix(basis_x_C_0)*basis_mat,
			 ChangeRing(vec_Q(omega_Q(a)*x), Integers()))
		: a in basis_C_0];
  iota_vals := [&+[v[i] * (C_0_Q!(basis_C_0[i])) : i in [1..#basis_C_0]]
		: v in iota_vecs];
  // This making iota into an isomorphism (rather than an involution)
  iota_vals := [C_0_Q!(omega_Q(C_0_Q!i_val)) : i_val in iota_vals];
  iota_mat := Matrix(iota_vals);
  assert &and[omega_Q(basis_C_0[i])*x eq x*omega_Q(iota_vals[i]) : i in [1..#basis_C_0]];
  B := Matrix([C_0_Q!x : x in basis_C_0]);
  iota_Q := hom<C_0_Q -> C_0_Q | Rows(B^(-1)*Matrix(iota_vals))>;
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
  assert Rank(iota_mat-omega_mat) eq (Dimension(C_0) div 2);

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

// a_lattice is a function for debugging purposes
// TODO : use it to make the code more modular

function a_lattice(a_val, det, basis_C_1, basis_C_0, vec_Q, V_C_Q, C_0_Q, C_1_Q, C_1,
		   C_Q, V_C, omega_Q, basis_C_Q)
    assert Abs(Evaluate(det, a_val)) eq 1;
    x := &+[a_val[i]*basis_C_1[i] : i in [1..#a_val]];
    C_0_Q_x := sub<V_C_Q | [vec_Q(b * x) : b in basis_C_0] >;
    x_C_0_Q := sub<V_C_Q | [vec_Q(x * b) : b in basis_C_0] >;
    assert (C_0_Q_x eq C_1_Q) and (x_C_0_Q eq C_1_Q);
    C_0_x := sub<V_C | [ChangeRing(Solution(Matrix(basis_C_Q),vec_Q(b * x)),
				   Integers()) : b in basis_C_0] >;
    basis_x_C_0 := [ChangeRing(Solution(Matrix(basis_C_Q), vec_Q(x * b)),
			       Integers()) : b in basis_C_0];
    x_C_0 := sub<V_C | basis_x_C_0 >;
    assert (C_0_x eq C_1) and (x_C_0 eq C_1);
    basis_mat := ChangeRing(Matrix(basis_C_Q), Integers());
    iota_vecs := [Solution(Matrix(basis_x_C_0)*basis_mat,
			   ChangeRing(vec_Q(omega_Q(a)*x), Integers()))
		  : a in basis_C_0];
    iota_vals := [&+[v[i] * (C_0_Q!(basis_C_0[i])) : i in [1..#basis_C_0]]
                  : v in iota_vecs];
    // making iota into an isomorphism (rather than an involution)                        
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

// TODO : might be we could do that with only the integral data
// Currently needs K to be a field.
function makeZ_K_Order(C_0_Q, iota_Q, omega_Q, delta)
    Z_C_0_Q := Center(C_0_Q);
    delta_Q := C_0_Q!Z_C_0_Q.2;
    K<delta_K> := ext< Rationals() | MinimalPolynomial(delta_Q)>;
    delta_mat := Matrix([delta_Q * C_0_Q.i : i in [1..8]]);
    basisker := Basis(Kernel(Matrix([iota_Q(omega_Q(C_0_Q.i)) : i in [1..Dimension(C_0_Q)]])-1));
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

// Isometry is an isometry from M to another lattice
// This gives the induced element of the quatenrion algebra.
function get_quaternion_orders(M : Isometry := 1)
    C_0_Q, emb_Q := RationalEvenClifford(M);
    _, T := Diagonalization(M);
    v_orth := [emb_Q(r) : r in Rows(T)];
    // assert v_orth[1]*v_orth[1] eq 1;
    i := v_orth[2]*v_orth[3];
    j := v_orth[3]*v_orth[4];
    B, quat_emb := sub<C_0_Q | i, j>;
    _, BB, isom := IsQuaternionAlgebra(B);
    BBB := QuaternionAlgebra(Discriminant(BB));
    _, isom2 := IsIsomorphic(BB,BBB : Isomorphism);
    isom := isom*isom2;
    BB := BBB;
    delta_Q := C_0_Q!(Center(C_0_Q).2);
    delta_Q := delta_Q * Denominator(delta_Q);
    delta_bar := Trace(delta_Q)/4 - delta_Q;
    my_basis := [1, i, j, i*j];
    my_basis := my_basis cat [delta_Q * x : x in my_basis];
    my_basis := [C_0_Q!x : x in my_basis];
    // This should just be the block matrix [[1,0],[tr(delta), -1]] !?
    // my_images := my_basis[1..4] cat [delta_bar * x : x in my_basis[1..4]];
    // sol_mat := Matrix([Solution(Matrix(my_basis), C_0_Q.i) : i in [1..8]]);
    // images := Rows(Matrix(my_images) * sol_mat);
//    images := [Solution(Matrix(my_basis), C_0_Q.i) * Matrix(my_images) : i in [1..8]];
    // iota_Q := hom<C_0_Q -> C_0_Q | [C_0_Q!Eltseq(x) : x in images]>;
    f<x> := MinimalPolynomial(delta_Q);
    K<delta_K> := quo<Parent(f) | f>;
    KK, roots := SplittingField(f);
    BB_KK, BB_KK_emb := ChangeRing(BB, KK);
//    roots := [x[1] : x in Roots(f)];
    //delta_homs := [hom<K -> Rationals() | r> : r in roots];
    delta_homs := [hom<K -> KK | r> : r in roots];
    delta_mat := Matrix([delta_Q * C_0_Q.i : i in [1..8]]);
    X := Matrix(my_basis[1..4]);
    X_tmp := VerticalJoin(X, X * delta_mat);
    // X_tmp is just my_basis again. Why do we do it twice?
    X_tmp_inv := X_tmp^(-1);
    // X_tmp_inv = sol_mat
    if (Isometry eq 1) then Isometry := IdentityMatrix(Rationals(), 4); end if;
    X_tmp_inv := DirectSum(Isometry,Isometry)*X_tmp_inv;
    nfl_basis := [Vector([X_tmp_inv[i,j] + delta_K * X_tmp_inv[i,j+4]
			  : j in [1..4]]) : i in [1..8]];
    mats := [Matrix([[h(x) : x in Eltseq(b)] : b in nfl_basis]) : h in delta_homs];
    if (Type(KK) eq FldRat) then
	denoms := [Denominator(mat) : mat in mats];
	int_mats := [ChangeRing(denoms[i]*mats[i], Integers()) : i in [1,2]];
	hnfs := [HermiteForm(mat) : mat in int_mats];
	rat_hnfs := [1/denoms[i] * ChangeRing(hnfs[i], Rationals()) : i in [1,2]];
	elts := [[isom(v[1] + v[2]*i + v[3]*j + v[4]*i*j) : v in Rows(hnf)] : hnf in rat_hnfs];
	orders := [QuaternionOrder(elt_seq) : elt_seq in elts];
    else
	idls := [ideal<Integers(KK) | 1> : i in [1..8]];
	pmat := PseudoMatrix(idls, mats[1]);
	hnf := HermiteForm(pmat);
	idls := CoefficientIdeals(hnf);
	bb := Basis(hnf);
	ideal_gens := [Generators(idl) : idl in idls];
	gen_vecs := &cat[[[g*b : b in bb[idx]] : g in ideal_gens[idx]]
			 : idx in [1..#ideal_gens]];
	gen_vecs_eltseq := [[Eltseq(x) : x in v] : v in gen_vecs];
	s := [1, i, j, i*j];
	gen_vecs_parts := [[isom(&+[v[idx][j]*s[idx] : idx in [1..4]]) :
			    j in [1..2]] : v in gen_vecs_eltseq];
	// delta_KK := KK.1;
	// HNF might change the basis
	omega_KK := KK!(Order(hnf).2);
//	elts := [BB_KK_emb(v[1]) + delta_KK * BB_KK_emb(v[2]) : v in gen_vecs_parts];
	elts := [BB_KK_emb(v[1]) + omega_KK * BB_KK_emb(v[2]) : v in gen_vecs_parts];
	orders := [Order(elts)];
    end if;
    return orders;
end function;

function get_genus_orders(genus)
//    genus := [GramMatrix(lat) : lat in Representatives(Genus(LatticeWithGram(M)))];
    all_orders := [get_quaternion_orders(L) : L in genus];
    // quat_alg := [QuaternionAlgebra(o[1]) : o in all_orders];
    quat_alg := [Algebra(o[1]) : o in all_orders];
    fields := [BaseRing(quat) : quat in quat_alg];
    B := quat_alg[1];
    F := fields[1];
    orders_B := [all_orders[1]];
    for idx in [2..#quat_alg] do
	B_prime := quat_alg[idx];
	F_prime := fields[idx];
	assert IsIsomorphic(F_prime, F);
	if (Type(F) ne FldRat) then 
	    B_prime, emb_F := ChangeRing(B_prime, F);
	    _, isom := IsIsomorphic(B_prime, B : Isomorphism);
	    order_B := [Order([isom(emb_F(x)) : x in Basis(O)]) : O in all_orders[idx]];
	else
	    _, isom := IsIsomorphic(B_prime, B : Isomorphism);
	    order_B := [QuaternionOrder([isom(x) : x in Basis(O)]) : O in all_orders[idx]];
	end if;
	Append(~orders_B, order_B);
    end for;
    return orders_B;
end function;

// Finds an isometry away from p, from M2 to M1,
// i.e. s * M1 * s^t = M2
function find_local_isom(M1, M2, p)
    L1 := LatticeFromLat(LatticeWithGram(M1));
    L2 := LatticeFromLat(LatticeWithGram(M2));
    pR := ideal<Integers() | p>;
    nProc := BuildNeighborProc(L1, pR, 1);
    is_isom := false;
    while (not is_isom) do
	L_prime := BuildNeighbor(nProc);
	is_isom, s := IsIsometric(ZLattice(L_prime), ZLattice(L2));
	GetNextNeighbor(~nProc);
    end while;
    isom_nbr := Matrix([x[2] : x in PseudoBasis(L_prime)]);
    assert s * isom_nbr * M1 * Transpose(s*isom_nbr) eq M2;
    return s * isom_nbr;
end function;

function PonomarevClassNumberFormula(Delta)
    K := QuadraticField(Delta);
    Delta_K := Discriminant(K);
    delta := Integers()!(SquareRoot(Delta div Delta_K));
    D, _ := SquareFreeFactorization(Delta);
    assert IsOdd(D) and Delta gt 5;
    primes := PrimeDivisors(delta);
    e := #primes;
    num := &*[p^2 + 1 : p in primes];
    denom := 3*2^(e+3) * (KroneckerSymbol(D,2)-4);
    M := num * &+([0] cat [KroneckerSymbol(D,m)*m : m in [1..(D-1) div 2]]) / denom;
    function h(m)
	return ClassNumber(QuadraticField(m));
    end function;
    c1 := IsEven(delta) select 3/16 else 1/8;
    c3 := (delta mod 3 eq 0) select ((D mod 8 eq 1) select 5/6 else 1/3) else 1/6;
    function sigma(m)
	if D mod 8 eq 1 then
	    if m mod 8 eq 3 then return -2; end if;
	    if m mod 8 eq 7 then return 0; end if;
	    return 2;
	else
	    if m mod 4 eq 3 then return 0; end if;
	    if m mod 4 eq 1 then return IsOdd(delta) select 2 else 3; end if;
	    return 2;
	end if;
    end function;
    function lambda(m)
	return #PrimeDivisors(m);
    end function;
    H := 2*M + c1 * h(-D) + c3 * h(-3*D);
    H +:= &+([0] cat [2^(-lambda(n) - sigma(n*d)) * h(-n*d) * h(-n*D/d)
	     : n in Divisors(delta), d in Divisors(D) | n*d notin [1,3] and d^2 lt D ]);
    return H;
end function;

function typeNumberPrimeSquare(p)
    h_p := (p+7) div 12;
    if p mod 12 eq 11 then h_p +:= 1; end if;
    f_p := (p mod 4 eq 1) select -1 else (p mod 8 eq 3) select 1 else 0;
    h_m_p := ClassNumber(QuadraticField(-p));
    return (h_p + 2^f_p *h_m_p) / 2;
end function;

function orthClassNumberPrimeSquare(p)
    h_p := (p+7) div 12;
    if p mod 12 eq 11 then h_p +:= 1; end if;
    f_p := (p mod 4 eq 1) select -1 else (p mod 8 eq 3) select 1 else 0;
    h_m_p := ClassNumber(QuadraticField(-p));
    return (h_p^2 + 4^f_p * h_m_p^2) / 2;
end function;

function firstPrimeNotDividing(n : LowerBound := 2)
    p := NextPrime(LowerBound-1);
    while n mod p eq 0 do
	p := NextPrime(p);
    end while;
    return p;
end function;

// return the dimensions of spaces of modular forms
// and cusp forms for the space of Hilbert modular forms
// over Q(sqrt(d)) of level n^2
function getHilbertDims(d,n : k := [2,2], UseFinite := false)
    // we take the genera corresponding to maximal lattices
    forms := [g[1] : g in QuaternaryQuadraticLattices(d*n^2) |
	      IsMaximalIntegral(LatticeFromLat(LatticeWithGram(g[1])))];
    Gs := [SO(Q) : Q in forms];
    // We go over all spinor norms to obtain all possible AL signs
    wt := [(k[1]+k[2]) div 2-2, (k[1]-k[2]) div 2];
    if UseFinite then
	p := firstPrimeNotDividing(d*n^2 : LowerBound := 2^4);
	Fp := GF(p);
	Gps := [SO(ChangeRing(Q, Fp)) : Q in forms];
	W0s := [HighestWeightRepresentation(G, wt) : G in Gps];
	f_desc := Sprintf("
      function foo(H)
        F := BaseRing(H);
        n := %m; 
        pR := Factorization(ideal<Integers(F)|%m>)[1][1];
        Fq, mod_q := ResidueClassField(pR);
        f := map< H -> GL(n,Fq) |
		  x :-> projLocalization(x, mod_q)>;
        return f;
      end function;
      return foo;
       ", 4, p);
	W0s := [Pullback(V,f_desc, GL(4, Rationals())) : V in W0s];
    else
	W0s := [HighestWeightRepresentation(G, wt) : G in Gs];
    end if;
    Ws := [[TensorProduct(W0s[i],SpinorNormRepresentation(Gs[i], d)) :
		d in Divisors(n)] : i in [1..#Gs]];
    L := IdentityMatrix(Rationals(),4);
    omfs := [[AlgebraicModularForms(Gs[i], W, L) : W in Ws[i]] : i in [1..#Gs]];
    total := &+([0] cat [&+[Dimension(omf) : omf in omfs_G] : omfs_G in omfs]);
    cusp := &+([0] cat [&+[Dimension(CuspidalSubspace(omf)) : omf in omfs_G]
	       : omfs_G in omfs]);
    return total, cusp;
end function;

// This function shows the passage from GU2(B) to GSpin(5)
function otherStuff()
    QQ := Rationals();
    B<i_B,j_B,k_B> := QuaternionAlgebra(QQ, -1, -1);
    B_conj := hom<B -> B | x :-> Conjugate(x)>;
    C<i_C,j_C,k_C> := QuaternionAlgebra(QQ, 1, 11);
    // First construction - direct, works with any B,C
    BC, iota_B, iota_C := DirectSum(B,C);
    basis := [iota_B(i_B), iota_B(j_B), iota_B(k_B), iota_C(i_C), iota_C(j_C)];
    function trd(x)
	return 1/2*(x + Conjugate(x));
    end function;
    function pairing(x,y)
	x1 := x @@ iota_B;
	x2 := x @@ iota_C;
	y1 := y @@ iota_B;
	y2 := y @@ iota_C;
	return -trd(B!(x1 * y1)) + trd(C!(x2*y2));
    end function;
    Matrix([[pairing(x,y) : y in basis] : x in basis]);
    M2B := MatrixRing(B,2);
    // These are the images of i_C, j_C under the isomorphism
    // C = (1,11 / QQ) = M2(QQ)
    im_i_C := M2B![1,0,0,-1];
    im_j_C := M2B![0,11,1,0];
    // This is the basis to the 5-dimensional space over which we will
    // have the quadratic form
    basis := [M2B | i_B, j_B, k_B, im_i_C, im_j_C];
    // This is the transofrmation to get to hermitian matrices
    w := Matrix([[0,1],[-1,0]]);
    w_basis := [b*w : b in basis];
    // This shows that the bilinear form comes from the determinant
    Matrix([[1/2*(Determinant(x)+Determinant(y)-Determinant(x+y)) :
	     y in basis] : x in basis]);
    // Here we want to get the general transformation from
    // the action of SL_2(B) on M_2^Her(B) to SO(5)
    
    R := PolynomialRing(B, 16);
    names := [c cat IntegerToString(num) : num in [1,2,3,4],
					   c in ["a", "b", "c","d"]];
    AssignNames(~R, names);
    a_vars := [R.i : i in [1..4]];
    b_vars := [R.i : i in [5..8]];
    c_vars := [R.i : i in [9..12]];
    d_vars := [R.i : i in [13..16]];
    R_star := hom<R -> R | B_conj, GeneratorsSequence(R) >;
    basis_B := [R | B!1, i_B, j_B, k_B];
    a := (Vector(a_vars), Vector(basis_B));
    b := (Vector(b_vars), Vector(basis_B));
    c := (Vector(c_vars), Vector(basis_B));
    d := (Vector(d_vars), Vector(basis_B));
    a_ := R_star(a);
    b_ := R_star(b);
    c_ := R_star(c);
    d_ := R_star(d);
    g := Matrix([[a,b],[c,d]]);
    g_star := Matrix([[a_, c_], [b_, d_]]);
    M2 := Parent(g);
    tmp := (g * M2![0,i_B,-i_B,0] * g_star)[1,2];
    coeffs, mons := CoefficientsAndMonomials(tmp);
    basis_B := [B!1, i_B, j_B, k_B];
    v := [&+[(coeffs[i]/b)*mons[i] : i in [1..#coeffs] |
	     IsCoercible(Rationals(), coeffs[i] / b)] : b in basis_B];
end function;

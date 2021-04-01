SetDebugOnError(true);
SetHelpUseExternalBrowser(false);
AttachSpec("ModFrmAlg.spec");

if assigned AlgebraicModularFormsExamples then
    delete AlgebraicModularFormsExamples;
end if;

if assigned testExample then
    delete testExample;
end if;

if assigned normalizeField then
    delete normalizeField;
end if;

import "tests/examples.m" : AlgebraicModularFormsExamples;
import "tests/tests.m" : testExample, testLSeries;
import "modfrmalg/modfrmalg.m" : normalizeField;
import "neighbors/hecke-CN1.m" : processNeighborWeight,
       HeckeOperatorCN1,
       HeckeOperatorCN1Sparse,
       printEstimate;
import "neighbors/inv-CN1.m" : Invariant;
import "neighbors/neighbor-CN1.m" : BuildNeighborProc,
       SkipToNeighbor,
       BuildNeighbor,
       LiftSubspace,
       GetNextNeighbor;

import "neighbors/genus-CN1.m" : OrthogonalMass, UnitaryMass;
import "lattice/lattice.m" : GuessMaxDet;

function inspect(M : prec := 20)
    Dimension(M);
    if IsZero(Dimension(M)) then return [* *]; end if;
    D := Decomposition(M,100);
    eigenforms := HeckeEigenforms(M);
    evs := [* HeckeEigensystem(f,1 : Precision := prec) :  f in eigenforms *];
    lpolys := [* LPolynomials(f : Precision := prec) : f in eigenforms *];
    lps :=  [* [Factorization(lp[p]) : p in PrimesUpTo(prec)] : lp in lpolys *];
    return evs, lps;
end function;

QQ := Rationals();
std_reps := AssociativeArray();
forms := AssociativeArray();
std_reps[3] := StandardRepresentation(GL(3,QQ));
std_reps[5] := StandardRepresentation(GL(5,QQ));
forms[3] := [IdentityMatrix(QQ,3),
	  SymmetricMatrix(QQ, [1,0,1,1/2,0,3]),
	  SymmetricMatrix(QQ, [2,-1/2,2,-1/2,0,6]) // Alok Shukla's example
	  ];
forms[5] := [
	  IdentityMatrix(QQ,5),
	  SymmetricMatrix(QQ, [1,0,1,0,0,1,0,0,0,1,1/2,0,0,0,3]),
	  SymmetricMatrix(QQ, [1,0,1,0,0,1,0,1/2,0,1,1/2,0,0,0,3])
];
// understand which of these examples is suitable to become a test
/*
for dim in [3,5] do
    for A in forms[dim] do
	A;
	G := SpecialOrthogonalGroup(A);
	// maybe should make k depend on the dimension
	for k in [0..6] do
	    k;
	    W := SymmetricRepresentation(std_reps[dim],k);
	    //	M := OrthogonalModularForms(A, W);
	    M := AlgebraicModularForms(G, W);
	    inspect(M);
	end for;
    end for;
end for;
*/

M, timing := AlgebraicModularFormsTests(:num_primes := 3,
					 decomposition := true);
print "testing L series cmoputation for O(5)...";
print "testing level 61, weights (3,0), (3,2) and (4,0)...";
testLSeries(61, [[3,0],[3,2],[4,0]], 5);
print "testing level 21, weight (3,2)....";
testLSeries(21, [[3,2]], 5);
// This does not seem to work at the moment for some reason!
// print "testing level 26, weight (3,2)....";
// testLSeries(26, [[3,2]], 5);
A := forms[5][2];
G := SpecialOrthogonalGroup(A);
W := SymmetricRepresentation(std_reps[5], 2);
M := AlgebraicModularForms(G,W);
evs, lpolys := inspect(M : prec := 10);

// testing an inert prime
example := AlgebraicModularFormsExamples[3];
M, timing := testExample(example : num_primes := 3);
T2 := HeckeOperator(M,2);
T3 := HeckeOperator(M,3);
assert T2*T3 eq T3*T2;

// Checking the 305 
a := Split("1   1   1   1  26   0   0   0   1   0   0   0   0   1   1", " ");
a := [eval(x) : x in a];
tmp := [a[1],a[6],a[2]] cat a[7..8] cat [a[3]] cat a[9..11] cat [a[4]] cat 
       a[12..15] cat [a[5]];
A := SymmetricMatrix(tmp);
A := 1/2*(A + DiagonalMatrix(Diagonal(A)));
Determinant(A);
d := 1;
G := OrthogonalGroup(A);
W := SpinorNormRepresentation(G, d);
M := AlgebraicModularForms(G, W);
D := Decomposition(M, 100);
eigenforms := HeckeEigenforms(M);

function load_Nipp(Nipp_str)
    a := Split(Nipp_str, " ");
    a := [eval(x) : x in a];
    tmp := [a[1],a[6],a[2]] cat a[7..8] cat [a[3]] cat a[9..11] cat [a[4]] cat 
	   a[12..15] cat [a[5]];
    A := SymmetricMatrix(tmp);
    A := 1/2*(A + DiagonalMatrix(Diagonal(A)));
    return A;
end function;

// This code is for checking the image of the Galois representation
// Later put it in a relevant place

// function getGaloisImage(L_p, l, psi, fp_hom)
function getGaloisImage(L_p, l)
    a := Coefficients(L_p);
    K := Universe(a);
    K_x<x> := Parent(L_p);
    _, phi := IsSquare(a[1]/a[5]);
    a := [a[2]/a[5], a[3]/a[5]];
    zero := MatrixRing(K,2)!0;
    A := CompanionMatrix(x^2);
    B := zero;
    B[2,2] := -phi^(-2);
    C := zero;
    C[1,1] := phi^3;
    C[1,2] := phi * a[1];
    D := zero;
    D[1,2] := -phi^(-1) * a[2];
    D[2,1] := phi;
    D[2,2] := -phi^(-1) * a[1];
    // This is a symplectic similtude matrix
    // (with the correct similitiude factor)
    // with characteristic polynomial L_p
    mat := BlockMatrix([[A,B],[C,D]]);
    mat_mod_l := GL(4,l)!mat;
    // g := (mat_mod_l @@ fp_hom) @ psi;
    //     return g;
    return mat_mod_l;
end function;

// At the moment this is for SO(5), so we use Sp(4)
// !!! TODO : make it work in general
function getGaloisImages(lpolys, l)
    a := PrimitiveElement(GF(l));
    zero := MatrixRing(GF(l),2)!0;
    one := MatrixRing(GF(l),2)!1;
    Q := BlockMatrix([[a*one, zero], [zero, one]]);
    CSp_4_l := sub<GL(4,l)|Sp(4,l),Q>;
 //   fp_grp, fp_hom := FPGroup(CSp_4_l);
 //   csp_4, psi := PermutationGroup(fp_grp);
    //    return [getGaloisImage(L_p, l, psi, fp_hom) : L_p in lpolys], psi, fp_hom;
    return [CSp_4_l | getGaloisImage(L_p, l) : L_p in lpolys];
end function;

function invariantSubspace(T)
    evs := [x[1] : x in Eigenvalues(T)];
    eigenspaces := [Eigenspace(T, ev) : ev in evs];
    return &+eigenspaces;
end function;

// Every central elation fixes all points in a plane and all the planes and
// lines through a point in that plane.
function centralElationPointOfFixedPlanes(T)
    // central elations have a plane of fixed points
    assert Dimension(invariantSubspace(T)) eq 3;
    _, X := JordanForm(T);
    v := X[Nrows(X)];
    V := Parent(v);
    return sub<V|X[Nrows(X)]>;
end function;


function getMaximalSubgroup(lpolys, l)
    // gs, psi, fp_hom := getGaloisImages(lpolys, l);
    gs := getGaloisImages(lpolys, l);
    gsp := Universe(gs);
    conj_classes := [Conjugates(gsp, g) : g in gs];
    max_subs := MaximalSubgroups(gsp);
    max_subs_set := [Set(H`subgroup) : H in max_subs];
    intersections := [];
    for i in [1..#conj_classes] do
	int_conj := [];
	for j in [1..#max_subs_set] do
	    Append(~int_conj, IsEmpty(conj_classes[i] meet max_subs_set[j]));
	end for;
	Append(~intersections, int_conj);
    end for;
    all_in_sub := [&and[not x[i] : x in intersections] :
		   i in [1..#max_subs_set]];
    not_all := exists(idx){idx : idx in [1..#all_in_sub] | all_in_sub[idx]};
    if not not_all then return "Full group GSp"; end if;
    H := max_subs[idx]`subgroup;
    // HH := (H @@ psi) @ fp_hom;
    // return HH;
    return H;
end function;

function groupCentralElations(HH_0, l)
    order_l := [x : x in HH_0 | IsDiagonal(x^l) and not IsDiagonal(x)]; 
    // order_l := [x : x in HH_0 | Order(x) eq l];
    // Those that have a plane of fixed points
    central := [T : T in order_l | Dimension(invariantSubspace(T)) eq 3];
    centers := [centralElationPointOfFixedPlanes(c) : c in central];
    axial_planes := [invariantSubspace(T) : T in central];
    common_centers := AssociativeArray();
    for i in [1..#central] do
	key := <axial_planes[i], centers[i]>;
	if not IsDefined(common_centers, key) then
	    common_centers[key] := [];
	end if;
	common_centers[key] cat:= [central[i]];
    end for;
    keys := [k : k in Keys(common_centers)];
    axial_planes := [k[1] : k in keys];
    centers := [k[2] : k in keys];
    return common_centers, keys, axial_planes, centers;
end function;

procedure updateConjugation(~grps, ~spaces, tt)
    for i in [1..#grps] do
	grps[i] := grps[i]^tt;
    end for;
    for i in [1..#spaces] do
	spaces[i] := spaces[i] * tt;
    end for;
end procedure;

function findConjugation(HH_0, ax1, ax2, c1, c2, l)
    
    V := VectorSpace(GF(l),4);
    
    intersection_line := ax1 meet ax2;

    // This function is good for debugging purposes
    function symp_form(x, y)
	return x[4]*y[1]-x[1]*y[4]+x[3]*y[2]-x[2]*y[3];
    end function;
    J := Matrix([[symp_form(x,y) : y in Basis(V)] : x in Basis(V)]);
    v1, v2 := Explode(Basis(intersection_line));
    u1 := Explode(Basis(c1));
    u2 := Explode(Basis(c2));
    s1 := symp_form(v1, v2);
    s2 := symp_form(u1, u2);
    my_basis := [v1, u1, -u2/s2, -v2/s1];
    // This is the symplectic form w.r.t this basis - should be J
    assert Matrix([[symp_form(x,y) : y in my_basis] : x in my_basis]) eq J;
    tt := GL(4,l)!Matrix(my_basis)^(-1);
    assert tt in Sp(4,l);
    return tt;
end function;

function getThirdElation(HH_0_conj, E1, E2, E3, c3, ax1, l)
    V := VectorSpace(GF(l),4);
    assert &or[x*y ne y*x : x in GeneratorsSequence(E2),
			    y in GeneratorsSequence(E3)];
    // This is just for debugging - if something goes wrong
    /*
    assert exists(refl_12){x : x in sub<HH_0_conj | E1, E2> |
			   Eigenspace(x, -1) eq joining_line};
    joining_line_23 := sub<V| c2, c3>;
    assert exists(refl_23){x : x in sub<HH_0_conj | E2, E3> |
			   Eigenspace(x, -1) eq joining_line_23};
    assert IsIsomorphic(sub<HH_0_conj | refl_23, refl_12>, DihedralGroup(l));
    conj_planes := [x : x in {sub<V|[ b*g :
				      b in Basis(ax1)]> :
			      g in sub<HH_0_conj | E1,E2>}];
    assert Set(conj_planes) eq {sub<V|[ b*g : b in Basis(ax2)]> :
				g in sub<HH_0_conj | E1,E2>};
   */
    assert exists(g){g : g in sub<HH_0_conj|E1,E2> |
		     c3 subset sub<V|[b*g^(-1) : b in Basis(ax1)]>};
    // We conjugate E3 so that its center will lie in ax1
    E3 := E3^g;
    c3 := c3*g;
    assert c3 subset ax1;
    v := Basis(c3)[1];
    x := v[1];
    y := v[4];
    z := v[2];
    assert z ne 0;
    assert (x ne 0) or (y ne 0);
    beta := -y/z;
    delta := x/z;
    if x ne 0 then
	alpha := z / x;
	gamma := 0;
    else // y ne 0
	alpha := 0;
	gamma := z/y;
    end if;
    mat := IdentityMatrix(GF(l),4);
    mat[1,1] := alpha;
    mat[1,4] := beta;
    mat[4,1] := gamma;
    mat[4,4] := delta;
    mat := Sp(4,l)!mat;
    return mat;
end function;

procedure swap(~x, ~y)
    tmp := x;
    x := y;
    y := tmp;
end procedure;

// Right now only identifies Klingen parabolic subgroup -
// !!! TODO : add identification for the other maximal subgroups

function identifyMaximalSubgroup(lpolys, l)
    print "Computing maximal subgroup...";
    HH := getMaximalSubgroup(lpolys, l);
    print "Done!";
    if (Type(HH) eq MonStgElt) then
	return HH;
    end if;
    HH_0 := HH meet Sp(4,l); // This makes things slightly easier to classify
    print "Finding a conjugate in which we have standard E1, E2...";
    common_centers, keys, axial_planes, centers :=
	groupCentralElations(HH_0, l);
    max, arg_max := Maximum([#common_centers[key] : key in keys]);
    E1 := sub<HH_0 | common_centers[keys[arg_max]] >;
    ax1 := axial_planes[arg_max];
    c1 := centers[arg_max];
    assert exists(idx){idx : idx in [1..#centers] |
		       not (centers[idx] subset ax1)};
    E2 := sub<HH_0 | common_centers[keys[idx]] >;
    ax2 := axial_planes[idx];
    c2 := centers[idx];
    tt := findConjugation(HH_0, ax1, ax2, c1, c2, l);
    // We swap them to make it the same as in the paper (could have
    // also chosen a different basis instead)
    E1 := E1^tt;
    E2 := E2^tt;
    c1 := c1*tt;
    c2 := c2*tt;
    ax1 := ax1*tt;
    ax2 := ax2*tt;
    T1 := GeneratorsSequence(E1)[1];
    if IsZero(T1[3,2]) then
	swap(~E1, ~E2);
	swap(~c1, ~c2);
	swap(~ax1, ~ax2);
    end if;
    tmp := [];
    updateConjugation(~tmp, ~centers, tt);
    updateConjugation(~tmp, ~axial_planes, tt);
    HH_0_conj := HH_0^tt;
    assert exists(idx){idx : idx in [1..#centers] | not (
			(centers[idx] subset ax1) or (centers[idx] subset ax2))
				and centers[idx] + c2 ne c1 + c2};
    E3 := sub<HH_0_conj | [x^tt : x in common_centers[keys[idx]]] >;
    ax3 := axial_planes[idx];
    c3 := centers[idx];
    print "Done!";
    printf "Finding a conjugate in which the third ";
    print "elation group E3 lies on the axial plane of E1...";
    mat := getThirdElation(HH_0_conj, E1, E2, E3, c3, ax1,l);
    E3 := E3^mat;
    c3 := c3*mat;
    HH_0_conj := HH_0_conj^mat;
    print "Done!";
    V := VectorSpace(GF(l),4);
    c4 := sub<V|[1,0,0,0]>;
    x4 := sub<V|[1,0,0,0],[0,1,0,0],[0,0,1,0]>;
    iso_line := c4*mat^(-1)*tt^(-1);
    
    // This is great for debugging, but we don't really need it
    /*
    tmp := [];
    updateConjugation(~tmp, ~centers, mat);
    updateConjugation(~tmp, ~axial_planes, mat);
    E_13 := sub<HH_0_conj | E1, E3>;
    grp1 := sub<E_13 | [1,0,0,0,0,1,0,0,1,-1,1,0,1,1,0,1]>;
    grp2 := sub<HH_0_conj | [1,0,0,0,0,1,0,0,-1,1,1,0,1,-1,0,1]>;
    grp_12 := sub<HH_0_conj | grp1, grp2>;
    central_12 := [t : t in grp_12 |
		   Order(t) eq l and Dimension(Eigenspace(t,1)) eq 3];
    c4 := sub<V|[1,0,0,0]>;
    exists(T){T : T in central_12 | centralElationPointOfFixedPlanes(T) eq c4};
    x4 := Eigenspace(T,1); // axial plane - x4 = 0
    // In this case alll centers lie on the axial plane
    assert &and[c subset x4 : c in centers]; 
    stab_x4 := sub<Sp(4,l)|[h : h in Sp(4,l) |
			    sub<V|[b*h : b in Basis(x4)]> eq x4]>;
    // This might be long, comment out.
    assert stab_x4 eq HH_0_conj;
    iso_line := c4*mat^(-1)*tt^(-1);
   */
    // Verifying HH_0 is indeed the stabilizer of iso_line
    stab_c4_conj := sub<Sp(4,l)|[h : h in Sp(4,l) |
				 sub<V|[b*h : b in Basis(iso_line)]>
				 eq iso_line]>;
    print "Verifying this is indeed the stabilizer...";
    assert stab_c4_conj eq HH_0;
   
    return "Klingen", iso_line, x4*mat^(-1)*tt^(-1);
end function;


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

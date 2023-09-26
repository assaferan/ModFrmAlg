function BuildUnimodularLatticeAMF(d)
    F := QuadraticField(d);
    B := QuaternionAlgebra(InfinitePlaces(F));
    O := MaximalOrder(B);
    gram_O := Matrix([[Norm(x+y)-Norm(x)-Norm(y) : y in Basis(O)] : x in Basis(O)]);
    V := AmbientReflexiveSpace(gram_O);
    idls := [pb[1] : pb in PseudoBasis(O)];
    lat := LatticeWithBasis(V, IdentityMatrix(F, 4), idls);
    G := OrthogonalGroup(gram_O);
    W := HighestWeightRepresentation(G, [0,0]);
    L := lat;
    M := AlgebraicModularForms(G, W, L);
    return M;
end function;

procedure testEisenstein(d, num_eis)
    M := BuildUnimodularLatticeAMF(d);
    assert #EisensteinSeries(M) eq num_eis;
end procedure;

// Fixing issue #77 Eisenstein
printf "Testing d = 40";
testEisenstein(40, 2);

// original code
/*
Qr<r> := QuadraticField(10);
mo := MaximalOrder(Qr);
m := SymmetricMatrix([2,r,6,0,-1,2,1,0,0,6]);
assert Determinant(m) eq 1;
G  := OrthogonalGroup(m);
W := HighestWeightRepresentation(G,[0,0,0]);
L := IdentityMatrix(Qr,4);
M := AlgebraicModularForms(G,W,L);
E := EisensteinSeries(M);
assert #E eq 2;
*/

// Additional tests

// Testing that this is really narow class group, as Q(sqrt3) has trivial class group but narrow class group of order 2
printf ",12";
testEisenstein(12, 2);

// Testing a class group with more than one generator (several connected components for each Hecke operator)
printf ",60";
testEisenstein(60, 4);

printf "\n";

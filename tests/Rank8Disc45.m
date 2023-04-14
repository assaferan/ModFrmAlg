procedure testRank8Disc45()
    printf "Testing Dan's example of a rank 8 lattice with discriminant 45...";
    mat := [ 2, 1, -1, -1, 1, -1, -1, -1, 1, 2, -1, -1, 1, -1, 0, 0, -1,
	     -1, 2, 1, -1, 1, 1, 1, -1, -1, 1, 2, -1, 1, 1, 1, 1, 1, -1, -1, 2, -1,
	     -1, -1, -1, -1, 1, 1, -1, 2, 1, 1, -1, 0, 1, 1, -1, 1, 4, 1, -1, 0, 1,
	     1, -1, 1, 1, 4 ];
    Q := Matrix(Rationals(), 8, 8, mat);
    G := OrthogonalGroup(Q);
    W := HighestWeightRepresentation(G, [0]);
    L := IdentityMatrix(Rationals(), 8);
    M := AlgebraicModularForms(G, W, L);
    assert Dimension(M) eq 4;
end procedure;

testRank8Disc45();

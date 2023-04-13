procedure testEigenspaceDecomposition()
    printf "Tests a bug that appeared in eigenspace decomposition...";
    Q := QuinaryQuadraticLattices(390)[2][1];
    G := OrthogonalGroup(Q);
    W := SpinorNormRepresentation(G, 6);
    M := AlgebraicModularForms(G, W);
    fs := HeckeEigenforms(M);
end procedure;

testEigenspaceDecomposition();

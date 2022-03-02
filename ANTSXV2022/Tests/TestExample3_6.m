Q := SymmetricMatrix([2,0,2,0,1,2,0,-1,-1,2,0,-1,-1,1,2,0,-1,-1,1,1,2,1,1,0,0,0,-1,4,0,0,-1,1,0,1,-1,4]);
assert Determinant(Q) eq 53;
M := OrthogonalModularForms(Q);
assert Dimension(M) eq 8;
time fs := HeckeEigenforms(M);

return true;

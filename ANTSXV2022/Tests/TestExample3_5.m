Q := SymmetricMatrix([2,1,2,1,1,2,-1,-1,-1,2,0,0,0,0,4,0,0,0,0,1,4]);
assert Determinant(Q) eq 75;
M := OrthogonalModularForms(Q);
assert Dimension(M) eq 3;
fs := HeckeEigenforms(M);

return true;

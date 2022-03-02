Q := SymmetricMatrix([2,-1,2,-1,1,2,-1,0,0,4,0,0,0,0,2,0,0,0,0,-1,2]);
assert Determinant(Q) eq 39;
M := OrthogonalModularForms(Q);
assert Dimension(M) eq 2;
fs := HeckeEigenforms(M);

return true;

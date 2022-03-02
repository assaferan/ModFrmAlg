Q := SymmetricMatrix([6,0,2,-4,-1,12,3,1,6,12]);
assert Determinant(Q) eq 193;
M := OrthogonalModularForms(Q);
assert Dimension(M) eq 9;
fs := HeckeEigenforms(M);

return true;

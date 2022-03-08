Q := SymmetricMatrix([2,0,2,0,1,34,1,0,0,34]);
assert Determinant(Q) eq 67^2;
M := OrthogonalModularForms(Q);
assert Dimension(M) eq 13;
fs := HeckeEigenforms(M);

return true;

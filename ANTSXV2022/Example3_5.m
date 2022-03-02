Q := SymmetricMatrix([2,1,2,1,1,2,-1,-1,-1,2,0,0,0,0,4,0,0,0,0,1,4]);
M := OrthogonalModularForms(Q);
time Dimension(M);
time fs := HeckeEigenforms(M);

exit;

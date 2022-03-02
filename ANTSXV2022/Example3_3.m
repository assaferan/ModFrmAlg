Q := SymmetricMatrix([6,0,2,-4,-1,12,3,1,6,12]);
M := OrthogonalModularForms(Q);
time Dimension(M);
time fs := HeckeEigenforms(M);

exit;

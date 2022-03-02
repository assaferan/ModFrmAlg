AttachSpec("../ModFrmAlg.spec");
Q := SymmetricMatrix([2,0,2,0,1,34,1,0,0,34]);
M := OrthogonalModularForms(Q);
time Dimension(M);
time fs := HeckeEigenforms(M);

exit;

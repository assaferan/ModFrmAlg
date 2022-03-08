AttachSpec("../ModFrmAlg.spec");
Q := SymmetricMatrix([2,0,2,0,1,2,0,-1,-1,2,0,-1,-1,1,2,0,-1,-1,1,1,2,1,1,0,0,0,-1,4,0,0,-1,1,0,1,-1,4]);
M := OrthogonalModularForms(Q);
time Dimension(M);
/*
8
Time: 305.020
*/
time fs := HeckeEigenforms(M);
/*
Time: 0.730
*/
exit;

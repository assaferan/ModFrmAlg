// This is Example 3.6 in the paper.
AttachSpec("../ModFrmAlg.spec");
Q := SymmetricMatrix([2,0,2,0,1,2,0,-1,-1,2,0,-1,-1,1,2,0,-1,-1,1,1,2,1,1,0,0,0,-1,4,0,0,-1,1,0,1,-1,4]);
M := OrthogonalModularForms(Q);
time Dimension(M);
/*
*/
time fs := HeckeEigenforms(M);
/*
*/
exit;

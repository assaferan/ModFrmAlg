AttachSpec("../ModFrmAlg.spec");
Q := SymmetricMatrix([2,1,2,1,1,2,-1,-1,-1,2,0,0,0,0,4,0,0,0,0,1,4]);
M := OrthogonalModularForms(Q);
time Dimension(M);
/*
3
Time: 0.450
*/
time fs := HeckeEigenforms(M);
/*
Time: 0.090
*/

exit;

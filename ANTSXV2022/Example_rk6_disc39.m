// This is Example 3.4 from the paper.
AttachSpec("../ModFrmAlg.spec");
Q := SymmetricMatrix([2,-1,2,-1,1,2,-1,0,0,4,0,0,0,0,2,0,0,0,0,-1,2]);
M := OrthogonalModularForms(Q);
time Dimension(M);
/*
2
Time: 0.360
*/
time fs := HeckeEigenforms(M);
/*
Time: 0.090
*/

exit;

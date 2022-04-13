// This is Example 3.3 in the paper.
AttachSpec("../ModFrmAlg.spec");
Q := SymmetricMatrix([6,0,2,-4,-1,12,3,1,6,12]);
M := OrthogonalModularForms(Q);
time Dimension(M);
/*
9
Time: 0.200
*/
time fs := HeckeEigenforms(M);
/*
Time: 0.120
*/

exit;

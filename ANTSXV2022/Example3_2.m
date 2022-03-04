// This is example 3.2 from the paper.
AttachSpec("../ModFrmAlg.spec");
Q := SymmetricMatrix([2,0,2,0,1,34,1,0,0,34]);
M := OrthogonalModularForms(Q);
time Dimension(M);
/*
13
Time: 0.300
*/
time fs := HeckeEigenforms(M);
/*
Time: 0.170
*/
exit;

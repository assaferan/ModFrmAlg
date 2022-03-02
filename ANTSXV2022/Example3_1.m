AttachSpec("../ModFrmAlg.spec");
Q := SymmetricMatrix([2,0,4,1,1,10,1,2,1,20]);
time M := OrthogonalModularForms(LatticeWithGram(Q));
time Dimension(M);
time fs := HeckeEigenforms(M);
time LPolynomial(fs[1],2);
time Theta1(fs[2]);
time Theta1(fs[3]);
time Theta1(fs[4]);

exit;

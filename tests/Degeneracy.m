import "neighbors/degeneracy.m" : DegeneracyMatrix, DegeneracyMatrixReverse;

Q11 := TernaryQuadraticLattice(11);
Q22 := TernaryQuadraticLattice(22);
omf11 := OrthogonalModularForms(Q11);
omf22_plus := OrthogonalModularForms(Q22);
omf22_minus := OrthogonalModularForms(Q22 : d := 2);
alpha_plus := DegeneracyMatrix(omf11, omf22_plus, 2, 1);
alpha_minus := DegeneracyMatrix(omf11, omf22_minus, 2, 1);
beta_plus := DegeneracyMatrixReverse(omf22_plus, omf11, 2, 1);
beta_minus := DegeneracyMatrixReverse(omf22_minus, omf11, 2, 1);
f11 := HeckeEigenforms(omf11)[2];

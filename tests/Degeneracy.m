Q11 := TernaryQuadraticLattice(11);
omf11 := OrthogonalModularForms(Q11 : Special);
f11 := HeckeEigenforms(omf11)[2]`vec;

Q22 := TernaryQuadraticLattice(22);
omf22_plus := OrthogonalModularForms(Q22 : Special);
omf22_minus := OrthogonalModularForms(Q22 : Special, d := 2);
alpha_2_plus := DegeneracyMatrix(omf11, omf22_plus, 2, 1);
alpha_2_minus := DegeneracyMatrix(omf11, omf22_minus, 2, 1);
beta_2_plus := DegeneracyMatrixReverse(omf22_plus, omf11, 2, 1);
beta_2_minus := DegeneracyMatrixReverse(omf22_minus, omf11, 2, 1);

f22_plus := HeckeEigenforms(omf22_plus)[2]`vec;
f22_minus := HeckeEigenforms(omf22_minus)[1]`vec;

assert f11*alpha_2_plus in sub<Parent(f22_plus) | f22_plus>;
assert f11*alpha_2_minus in sub<Parent(f22_minus) | f22_minus>;
assert f22_plus*beta_2_plus in sub<Parent(f11) | f11>;
// !!! This one still fails !!! Maybe an issue at 2?
assert f22_minus*beta_2_minus in sub<Parent(f11) | f11>;

Q55 := TernaryQuadraticLattice(55);
omf55_plus := OrthogonalModularForms(Q55 : Special);
omf55_minus := OrthogonalModularForms(Q55 : Special, d := 5);
alpha_5_plus := DegeneracyMatrix(omf11, omf55_plus, 5, 1);
alpha_5_minus := DegeneracyMatrix(omf11, omf55_minus, 5, 1);
beta_5_plus := DegeneracyMatrixReverse(omf55_plus, omf11, 5, 1);
beta_5_minus := DegeneracyMatrixReverse(omf55_minus, omf11, 5, 1);

f55_plus := HeckeEigenforms(omf55_plus)[2]`vec;
f55_minus := HeckeEigenforms(omf55_minus)[1]`vec;

assert f11*alpha_5_plus in sub<Parent(f55_plus) | f55_plus>;
assert f11*alpha_5_minus in sub<Parent(f55_minus) | f55_minus>;
assert f55_plus*beta_5_plus in sub<Parent(f11) | f11>;
assert f55_minus*beta_5_minus in sub<Parent(f11) | f11>;

function is_special_lattice(q)
    L := LatticeWithGram(q);
    L_dual := Dual(L : Rescale := false);
    return IsCyclic(L_dual / L);
end function;

// We choose an order with correct Witt Invariant to have degeneracy maps to Q45
// We also need them to be special
Q15 := TernaryQuadraticLattices(15)[2];
assert WittInvariant(Q15, 5) eq -1;
assert is_special_lattice(Q15);
omf15 := OrthogonalModularForms(Q15 : Special);
f15 := HeckeEigenforms(omf15)[2]`vec;

Q45 := TernaryQuadraticLattices(45)[2];
assert WittInvariant(Q45, 5) eq -1;
assert is_special_lattice(Q45);
omf45_plus := OrthogonalModularForms(Q45 : Special);
omf45_minus := OrthogonalModularForms(Q45 : Special, d := 3);
alpha_3_plus := DegeneracyMatrix(omf15, omf45_plus, 3, 1);
alpha_3_minus := DegeneracyMatrix(omf15, omf45_minus, 3, 1);
beta_3_plus := DegeneracyMatrixReverse(omf45_plus, omf15, 3, 1);
beta_3_minus := DegeneracyMatrixReverse(omf45_minus, omf15, 3, 1);

f45_plus := HeckeEigenforms(omf45_plus)[2]`vec;
f45_minus := HeckeEigenforms(omf45_minus)[1]`vec;

assert f15*alpha_3_plus in sub<Parent(f45_plus) | f45_plus>;
assert f15*alpha_3_minus in sub<Parent(f45_minus) | f45_minus>;
assert f45_plus*beta_3_plus in sub<Parent(f15) | f15>;
assert f45_minus*beta_3_minus in sub<Parent(f15) | f15>;

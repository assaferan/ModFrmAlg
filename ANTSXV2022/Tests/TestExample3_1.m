Q := SymmetricMatrix([2,0,4,1,1,10,1,2,1,20]);
assert Determinant(Q) eq 37^2;
M := OrthogonalModularForms(LatticeWithGram(Q));
assert Dimension(M) eq 4;
fs := HeckeEigenforms(M);
lpoly<x> := LPolynomial(fs[1],2);
assert lpoly eq 16*x^4 - 36*x^3 + 28*x^2 - 9*x + 1;

f2<q> := Theta1(fs[2]);
assert f2 eq q - 2*q^2 - 3*q^3 + 2*q^4 - 2*q^5 + 6*q^6 - q^7 + 6*q^9 + 4*q^10 - 5*q^11 -
6*q^12 - 2*q^13 + 2*q^14 + 6*q^15 - 4*q^16 - 12*q^18 - 4*q^20 + 3*q^21 +
	     10*q^22 + 2*q^23 + O(q^25);

f3<q> := Theta1(fs[3]);
assert f3 eq O(q^25);

f4<q> :=  Theta1(fs[4]);
assert f4 eq q + q^3 - 2*q^4 - q^7 - 2*q^9 + 3*q^11 - 2*q^12 - 4*q^13 + 4*q^16 + 6*q^17 +
	     2*q^19 - q^21 + 6*q^23 + O(q^25);
return true;

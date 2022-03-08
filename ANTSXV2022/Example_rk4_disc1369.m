AttachSpec("../ModFrmAlg.spec");
Q := SymmetricMatrix([2,0,4,1,1,10,1,2,1,20]);
time M := OrthogonalModularForms(LatticeWithGram(Q));
/*
Time: 0.070
*/
time Lambdas := [InnerProductMatrix(Lambda) : Lambda in GenusReps(M)];
/*
Time: 0.080
*/
time Dimension(M);
/*
4
Time: 0.130
*/
time fs := HeckeEigenforms(M);
/*
Time: 0.150
*/
time LPolynomial(fs[1],2);
/*
16*x^4 - 36*x^3 + 28*x^2 - 9*x + 1
Time: 0.020
*/

time Theta1(fs[2]);
/*
q - 2*q^2 - 3*q^3 + 2*q^4 - 2*q^5 + 6*q^6 - q^7 + 6*q^9 + 4*q^10 - 5*q^11 - 
    6*q^12 - 2*q^13 + 2*q^14 + 6*q^15 - 4*q^16 - 12*q^18 - 4*q^20 + 3*q^21 + 
    10*q^22 + 2*q^23 + O(q^25)
Time: 0.020
*/

time Theta1(fs[3]);
/*
O(q^25)
Time: 0.020
*/

time Theta1(fs[4]);
/*
q + q^3 - 2*q^4 - q^7 - 2*q^9 + 3*q^11 - 2*q^12 - 4*q^13 + 4*q^16 + 6*q^17 + 
    2*q^19 - q^21 + 6*q^23 + O(q^25)
Time: 0.020
*/

exit;

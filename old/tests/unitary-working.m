n := Dimension(Lambda);
kP,redP := ResidueClassField(P);
pbLambda := PseudoBasis(Lambda);
coeff_ideals := [x[1] : x in pbLambda];
A := [[x : x in Generators(I) | x notin P*I][1] : I in coeff_ideals];
B := BasisMatrix(Lambda);
G := LatticeAutomorphismGroup(Lambda);
gens_L := [PullUp(Matrix(g), Lambda, Lambda) : g in Generators(G)];
C := [Vector(A[i]*B[i]) : i in [1..n]];


f := function(v)
  w := Eltseq(v*B^-1);
  ans := [redP(w[i]/A[i]) : i in [1..n]];
  return ans;
end function;


gens_LmodP := [Matrix([f(c*g) : c in C]) : g in gens_L];
GmodP := sub<GL(n,kP)|gens_LmodP>;
modP_line_reps := [x[1].1 : x in LineOrbits(GmodP)];
line_reps := [&+[x[i]@@redP*C[i] : i in [1..n]] : x in modP_line_reps];
{x in Lambda : x in line_reps};
{x-y in P*Lambda : x,y in line_reps | x ne y};

// A[i] is in coeff_ideals[i] but not in P*coeff_ideals[i].
// An isomorphism of kP=ZZ_L/P with coeff_ideals[i]/P*coeff_ideals[i]
// is induced by x --> x*A[i] for x in ZZ_L.
// Conversely, given an element a of coeff_ideals[i], a/A[i] is
// P-integral, so can reduce it mod P, i.e., redP(a/A[i]) is defined.
//
// Lambda = coeff_ideals[1]*B[1] + ... + coeff_ideals[n]*B[n].
// Subordinate to this pseudobasis, we have an identification
// Lambda/P*Lambda = coeff_ideals[1]/P*coeff_ideals[2] x ... x 
//          coeff_ideals[n]/P*coeff_ideals[n]
//                 = ZZ_L/P x ... x \ZZ_L/P
//                 = kP x ... x kP.

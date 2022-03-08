AttachSpec("../ModFrmAlg.spec");
Q := SymmetricMatrix([2,-1,2,-1,1,2,-1,0,0,4,0,0,0,0,2,0,0,0,0,-1,2]);
M := OrthogonalModularForms(Q);
v := HeckeEigenforms(M);

//we first check the L_polynomial of the Eise 
_<x> := Parent(LPolynomial(v[1],2));

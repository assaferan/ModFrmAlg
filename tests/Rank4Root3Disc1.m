procedure testRank4Root3Disc1(: Orbits := true, LowMemory := false,
				ThetaPrec := 25)
    print "Testing Dan's example of a rank 4 lattice over Q(rt3)...";
    K<rt3>:=QuadraticField(3);
    mat:=[2,rt3,rt3,2];
    Q:=DiagonalJoin(Matrix(K,2,2,mat),Matrix(K,2,2,mat));
    L:=IdentityMatrix(K,#Rows(Q));
    G:=OrthogonalGroup(Q);
    W:=HighestWeightRepresentation(G,[0,0,0,0]);
    M:=AlgebraicModularForms(G,W,L:GramFactor:=2);
    E:=HeckeEigenforms(M : Orbits := Orbits, LowMemory := LowMemory,
			   ThetaPrec := ThetaPrec);
    pol:=LPolynomial(E[1],Factorization(2*Integers(K))[1][1],#Rows(Q) : Orbits := Orbits, LowMemory := LowMemory, ThetaPrec := ThetaPrec);
    _<x> := Parent(pol);
    assert pol eq 16*x^4 - 36*x^3 + 28*x^2 - 9*x + 1;
end procedure;

testRank4Root3Disc1();

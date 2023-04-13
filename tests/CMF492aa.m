procedure testCMF492aa(: Orbits := true, LowMemory := false, ThetaPrec := 25)
    printf "Testing OMF for lattice of rank 3 and half-discriminant 343 for the classical modular form 49.2.a.a....";
    Q := SymmetricMatrix([6,1,6,1,-1,20]);
    G := OrthogonalGroup(Q);
    L := IdentityMatrix(Rationals(),3);
    M := AlgebraicModularForms(G, HighestWeightRepresentation(G,[0]), L);
    fs := HeckeEigenforms(M : Orbits := Orbits, LowMemory := LowMemory, ThetaPrec := ThetaPrec);
    f := fs[2];
    evs := HeckeEigensystem(f, 1 : Precision := 100, Orbits := Orbits, LowMemory := LowMemory, ThetaPrec := ThetaPrec);
    cfs := [Coefficient(qExpansion(CuspForms(49).1,100),p) : p in PrimesUpTo(100)];
    assert evs eq cfs;
end procedure;

testCMF492aa();

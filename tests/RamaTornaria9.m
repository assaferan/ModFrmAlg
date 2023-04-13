procedure testRamaTornaria9()
    printf "Testing Example 9 from Rama-Tornaria of non-lift paramodular form...";
    A := SymmetricMatrix([2,1,2,0,0,2,0,0,0,4,-1,-1,0,-1,6]);
    G := OrthogonalGroup(A);
    W := TrivialRepresentation(GL(5,Rationals()), Rationals());
    level := IdentityMatrix(Rationals(),5);
    M := AlgebraicModularForms(G, W, level);
    D := Decomposition(M);
    eigenforms := HeckeEigenforms(M);
    reps := Representatives(Genus(M));
    weights := [#AutomorphismGroup(rep)^(-1) : rep in reps];
    invs := [Invariant(rep) : rep in reps];
    thetas := [* &+[weights[i]*f`vec[i] *
		    PowerSeriesRing(BaseRing(f`vec))!invs[i]
		  : i in [1..#reps]] : f in eigenforms *];
    assert exists(i){i : i in [1..#thetas] | IsEmpty(Coefficients(thetas[i]))};
    f := eigenforms[i];
    lpolys := LPolynomials(f : Precision := 5);
    lpolys := [lpolys[p] : p in [2,3,5]];
    x := Universe(lpolys).1;
    assert lpolys[1] eq 64*x^4 + 56*x^3 + 24*x^2 + 7*x + 1;
    assert lpolys[2] eq 729*x^4 + 81*x^3 + 3*x^2 + 3*x + 1;
    assert lpolys[3] eq 15625*x^4 - 375*x^3 + 85*x^2 - 3*x + 1;
end procedure;

testRamaTornaria9();

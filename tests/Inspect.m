function inspect(M : prec := 20)
    printf "dim=%o...", Dimension(M);
    if IsZero(Dimension(M)) then return [* *]; end if;
    D := Decomposition(M,100);
    eigenforms := HeckeEigenforms(M);
    evs := [* HeckeEigensystem(f,1 : Precision := prec) :  f in eigenforms *];
    lpolys := [* LPolynomials(f : Precision := prec) : f in eigenforms *];
    lps :=  [* [Factorization(lp[p]) : p in PrimesUpTo(prec)] : lp in lpolys *];
    return evs, lps;
end function;

QQ := Rationals();
std_reps := AssociativeArray();
forms := AssociativeArray();
std_reps[3] := StandardRepresentation(GL(3,QQ));
std_reps[5] := StandardRepresentation(GL(5,QQ));
forms[3] := [2*IdentityMatrix(QQ,3),
	  SymmetricMatrix(QQ, [2,0,2,1,0,6]),
	  SymmetricMatrix(QQ, [4,-1,4,-1,0,12]) // Alok Shukla's example
	  ];
forms[5] := [
	  2*IdentityMatrix(QQ,5),
	  SymmetricMatrix(QQ, [2,0,2,0,0,2,0,0,0,2,1,0,0,0,6]),
	  SymmetricMatrix(QQ, [2,0,2,0,0,2,0,1,0,2,1,0,0,0,6])
];
// understand which of these examples is suitable to become a test

//for dim in [3,5] do
for dim in [3] do
    for A in forms[dim] do
	printf "A=\n%o\n", A;
	G := SpecialOrthogonalGroup(A);
	// maybe should make k depend on the dimension
	for k in [0..6] do
	    printf "k=%o,", k;
	    W := SymmetricRepresentation(std_reps[dim],k);
	    //	M := OrthogonalModularForms(A, W);
	    M := AlgebraicModularForms(G, W);
            _ := inspect(M);
	end for;
    end for;
end for;

A := forms[5][2];
G := SpecialOrthogonalGroup(A);
W := SymmetricRepresentation(std_reps[5], 2);
M := AlgebraicModularForms(G,W);
evs, lpolys := inspect(M : prec := 10);

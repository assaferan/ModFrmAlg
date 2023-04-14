// Checking the 305
printf "Testing discriminant 305...";
a := Split("1   1   1   1  26   0   0   0   1   0   0   0   0   1   1", " ");
a := [eval(x) : x in a];
tmp := [a[1],a[6],a[2]] cat a[7..8] cat [a[3]] cat a[9..11] cat [a[4]] cat 
       a[12..15] cat [a[5]];
A := SymmetricMatrix(tmp);
A := A + DiagonalMatrix(Diagonal(A));
// Determinant(A);
d := 1;
G := OrthogonalGroup(A);
W := SpinorNormRepresentation(G, d);
M := AlgebraicModularForms(G, W);
D := Decomposition(M);
eigenforms := HeckeEigenforms(M);

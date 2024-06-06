procedure testDiscriminant2()
    printf "Testing John's question about discriminant 2...";
    printf "creating matrix...";
    T := Matrix([[2,0,0,0,1],[0,2,0,0,1],[0,0,2,1,1],[0,0,1,2,0],[1,1,1,0,2]]);
    printf "creating lattice...";
    L := LatticeWithGram(T);
    printf "creating ModDedLat object from lattice...";
    Lambda := LatticeFromLat(L);
    printf "Checking discriminant...";
    assert Discriminant(Lambda) eq FractionalIdeal(2);
    printf "Checking norm of discriminant...";
    assert Norm(Discriminant(Lambda)) eq 2;
end procedure;

testDiscriminant2();

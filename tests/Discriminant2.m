procedure testDiscriminant2()
  printf "Testing John's question about discriminant 2...";
  T := Matrix([[2,0,0,0,1],[0,2,0,0,1],[0,0,2,1,1],[0,0,1,2,0],[1,1,1,0,2]]);
  L := LatticeWithGram(T);
  Lambda := LatticeFromLat(L);
  assert Discriminant(Lambda) eq FractionalIdeal(2);
  assert Norm(Discriminant(Lambda)) eq 2;
end procedure;

testDiscriminant2();

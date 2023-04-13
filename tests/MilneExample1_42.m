procedure testMilneExample1_42( : p := 3)
  assert IsPrimePower(p) and IsOdd(p);
  k<t> := FunctionField(GF(p));
  k_al := AlgebraicClosure(k);
  G_a := AdditiveAlgebraicGroup(k);
  A2<x,y> := DirectProduct(G_a, G_a);
  G := sub<A2 | y^p-t*y-t*x^p>;
  assert IsConnected(G);
  G_k_al := BaseChange(G, k_al);
end procedure;

testMilneExample1_42();

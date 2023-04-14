procedure testMilneExample1_19( : p := 3)
  assert IsPrimePower(p) and IsOdd(p);
  k<t> := FunctionField(GF(p));
  G_a := AdditiveAlgebraicGroup(k);
  A2<x,y> := DirectProduct(G_a, G_a);
  poly := y^p - t*x^p;
  assert IsIrreducible(poly);
  G := sub<A2 | poly>;
  // This is because IsReduced in fact checks geometrical irreduciblity?
  assert not IsReduced(G);
end procedure;

testMilneExample1_19();

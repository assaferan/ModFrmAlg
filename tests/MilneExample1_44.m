procedure testMilneExample1_44( : p := 3)
  assert IsPrimePower(p) and IsOdd(p);
  k<t> := FunctionField(GF(p));
  G_a := AdditiveAlgebraicGroup(k);
  A4<x,y,u,v> := DirectProduct(G_a, 4);
  G := sub<A4 | [u^p-t*v^p, x^p-t*y^p]>;
  assert IsConnected(G) and Dimension(G) eq 2;
  try
    G_red := ReducedSubgroup(G);
  catch e
    assert e`Object eq "Runtime error in sub< ... >: subscheme is not closed under multiplication.\n";
  end try;
  G_red := ReducedSubscheme(Scheme(G));
  assert IsSingular(G_red, G_red![0,0,0,0]);
end procedure;

testMilneExample1_44();

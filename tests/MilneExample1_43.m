procedure testMilneExample1_43( : p := 3)
  assert IsPrimePower(p) and IsOdd(p);
  k<t> := FunctionField(GF(p));
  G_a<x> := AdditiveAlgebraicGroup(k);
  G := sub<G_a | x^(p^2) - t*x^p>;
  try
    G_red := ReducedSubgroup(G);
  catch e
    assert e`Object eq "Runtime error in sub< ... >: subscheme is not closed under multiplication.\n";
  end try;
end procedure;

testMilneExample1_43();

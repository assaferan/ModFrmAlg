// tests for group scheme module

forward testMilneExample1_7;
forward testMilneExample1_19;
forward testMilneExample1_37;
forward testMilneExample1_42;
forward testMilneExample1_43;

intrinsic GroupSchemeTests()
{.}
  testMilneExample1_7();
  testMilneExample1_19();
  testMilneExample1_37();
  testMilneExample1_42();
  testMilneExample1_43();
end intrinsic;

// These are basic examples from Milne's Algebraic Groups
procedure testMilneExample1_7()
  // (a) char(k) ne 3 and k contains 3rd root of unity
  k<zeta3> := CyclotomicField(3);
  mu_3 := MuAlgebraicGroup(3, k);
  assert #IrreducibleComponents(Scheme(mu_3)) eq 3 and IsReduced(mu_3);
  // (b) char(k) ne 3, no 3rd root of unity
  k := Rationals();
  mu_3 := MuAlgebraicGroup(3, k);
  assert #IrreducibleComponents(Scheme(mu_3)) eq 2 and IsReduced(mu_3);
  // (c) char(k) = 3
  k := GF(3);
  mu_3 := MuAlgebraicGroup(3, k);
  assert #IrreducibleComponents(Scheme(mu_3)) eq 1 and not IsReduced(mu_3);
end procedure;

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

procedure testMilneExample1_37(: p := 3)
  // (a)
  k := GF(p);
  G<[x]> := GeneralLinearAlgebraicGroup(p, k);
  det_inv := x[#x];
  SLp := sub<G | det_inv-1>;
  Gm<y, y_inv> := MultiplicativeAlgebraicGroup(k);
  phi := hom<Gm -> G |Eltseq(ScalarMatrix(p, y)) cat [y_inv^p] >;
  H := sub<G| Image(phi)>;
  mu_p := SLp meet H;
  assert (not IsReduced(mu_p)) and IsReduced(H) and IsReduced(SLp);
  // (b)
  k := GF(2);
  G_a := AdditiveAlgebraicGroup(k);
  G<x,y> := DirectProduct(G_a, G_a);
  H_1 := sub<G | y>;
  H_2 := sub<G | y-x^2-x^4>;
  assert IsSmooth(H_1) and IsSmooth(H_2) and not IsReduced(H_1 meet H_2);
end procedure;

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


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

testMilneExample1_7();

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

testMilneExample1_37();

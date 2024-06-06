// Warning - This test takes a very long time! We add some parameters to allow for faster runs
procedure testRamaTornariaTable1ANTS(: PrecT1 := 500, PrecT2 := 50, PrecLSer := 30)
  printf "Testing Table 1 from [RT]...";
  traces_1 := [-8,-10,-4,-14,-22,-4,-47,-12,41,50,-504,-102,174,30,42,156,-252,472,106,-481,-744,927,-632,-297,2,-992,-1222,1436,-954,19,516,-258, 1080, 1030, -974, -1119, 1152, 108, -2707, -182, 2568, -2804, -3035, 583, 2276, 6754, 360, 3569, -3346, 2220, -2780, -3878, -819, 6112, -5343, -808, 3592, 2954, -8334, -2942, 6360, -856, 3548, -6322, -9443, 108, 1596, -2129, 1856, 480, 1704, 4601, 6298, -4998, 7706, -18293, 5316, 4324, -4679, -3476, -910, 3552, -4878, 15213, -6909, -7130, 12908, -4005, -7334, -77, 12248, 6447, -14197, 1960, 3288];

  traces_2 := [10,11,-44,-9,-67,-158,260,41,-198,-187,2744,-730,800,442,-5052];

  disc := 167;
  A := QuinaryQuadraticLattices(disc)[1][1];
  G := OrthogonalGroup(A);
  d := 167;
  spin := SpinorNormRepresentation(G, d);
  M := AlgebraicModularForms(G, spin);
  fs := HeckeEigenforms(M);
  assert #fs eq 1;
  f := fs[1];
  evs1 := HeckeEigensystem(f, 1 : Precision := PrecT1);
  evs2 := HeckeEigensystem(f, 2 : Precision := PrecT2);
  num_primes_T1 := #PrimesUpTo(PrecT1);
  num_primes_T2 := #PrimesUpTo(PrecT2);
  assert traces_1[1..num_primes_T1] eq evs1;
  assert traces_2[1..num_primes_T2] eq evs2;
  lser := LSeries(f : Precision := PrecLSer);
  assert CFENew(lser) lt 10^(-PrecLSer);
end procedure;

SetVerbose("AlgebraicModularForms", 2);
testRamaTornariaTable1ANTS( : PrecT1 := 25, PrecT2 := 5, PrecLSer := 2);

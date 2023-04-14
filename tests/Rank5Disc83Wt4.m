// !! TODO - convert into one of the examples

procedure testRank5Disc83Wt4( : Precision := 20)  // :Precision := NumPrimes ?
  printf "Testing a rank 5 lattice of discriminant 83 and weight (4,0)...";
  Q := QuinaryQuadraticLattices(83)[1][1];
  G := SpecialOrthogonalGroup(Q);
// not yet
// W := StandardRepresentation(G);
  W := HighestWeightRepresentation(G, [1,0]);
  M := AlgebraicModularForms(G, W);
  assert Dimension(M) eq 1;
  fs := HeckeEigenforms(M);
  f := fs[1];
  vals := HeckeEigensystem(f, 1 : Precision := Precision);
  ps := PrimesUpTo(Precision);
  norm_vals := [vals[i]*ps[i] : i in [1..#ps]];
  known_vals := [-17,-23,-36,-124,-359,-288,464,1302, 252, -4134, -5910,
		    12556, 17530, -14770, 8528, -76, -38716, -13026, -28929,
		    -31938, -19497, 1506, 51583, -38017, 49633, -71238, 4730,
		    -19656, -29808, 18326, 146172, -70205, -208442, 226422,
		    -257018, 171382, 291876, 26516, -311996, -341730, 299927,
		    326866, 36346, -1103093, 42884, -509996, 87940, 736596,
		    -1251900, -1334028, 1922373, 830990, 204992, 201386,
		    -814035, -863468, -15718, 1545020, 1588032, 846955,
		    -824092, -2147486];		    
  assert norm_vals eq known_vals[1..#ps];
  // !! TODO - add eigenvalues of T_p,2, fix 83 to match ours
end procedure;

testRank5Disc83Wt4();

// Checks which fs are nonlifts using irreduciblity of the lpolynomials
// The number of lpolynomials checked is prec.
// The odds that even one of them is reducible by chance are slim
// But we're doing 2 to make sure.
function get_nonlifts(fs, disc : prec := 2, Estimate := false, Orbits := true,
		      LowMemory := false, ThetaPrec := 25)
  // This is just for checking irreducibility
  primes := [];
  p := 2;
  for i in [1..prec] do  
    while (disc mod p eq 0) do
      p := NextPrime(p);
    end while;
    Append(~primes, p);
    p := NextPrime(p);
  end for;
  lpolys := [LPolynomials(f : Estimate := Estimate,
			  Precision := primes,
			  Orbits := Orbits,
			  LowMemory := LowMemory,
			  ThetaPrec := ThetaPrec) : f in fs];
  nonlift_idxs := [];
  for idx in [1..#lpolys] do
    lpolys_f := lpolys[idx];
    // This is sometimes problematic, when the base field is large
    // magma might crash, e.g. disc = 229, genus = 1
    // nonlift := &or[IsIrreducible(lpolys_f[p]) : p in PrimesUpTo(prec)
    //		    | disc mod p ne 0];
    nonlift := false;
    for p in primes do
      if Type(BaseRing(lpolys_f[p])) eq FldRat then
         fac := Factorization(lpolys_f[p]);
      else
         fac := FactorPolynomialOverNumberField(lpolys_f[p]);
      end if;
      is_irred := (#fac eq 1) and (fac[1][2] eq 1);
      nonlift or:= is_irred;
    end for;
    if nonlift then
      Append(~nonlift_idxs, idx);
    end if;
  end for;
  return nonlift_idxs;
end function;

procedure testLSeries(disc, wts, prec : Orbits := true,
		      LowMemory := false, ThetaPrec := 25)
  printf "Testing level %o, weight ", disc;
  A := QuinaryQuadraticLattices(disc)[1][1];
  G := OrthogonalGroup(A);
  for wt in wts do
    printf "%o ", wt;
    k,j := Explode(wt);
// It seems that was wrong
//    W := HighestWeightRepresentation(G,[k+j-3, k-3]);
    W := HighestWeightRepresentation(G,[k-3+j div 2, j div 2]);
    for d in Divisors(disc) do
        spin := SpinorNormRepresentation(G, d);
        W_spin := TensorProduct(W, spin);
        M := AlgebraicModularForms(G, W_spin);
        fs := HeckeEigenforms(M : Orbits := Orbits,
			      LowMemory := LowMemory, ThetaPrec := ThetaPrec);
        nonlifts := get_nonlifts(fs, disc : Orbits := Orbits,
				 LowMemory := LowMemory,
			 ThetaPrec := ThetaPrec);
        printf "For wt = %o, d = %o there are %o nonlifts. The dimensions of their Galois orbits are %o.\n", wt, d, #nonlifts, [Degree(BaseRing(fs[idx]`vec)) : idx in nonlifts]; 
        for idx in nonlifts do
	  f := fs[idx];
          lser := LSeries(f : Precision := prec,
		Orbits := Orbits, LowMemory := LowMemory,
		ThetaPrec := ThetaPrec);
          assert CFENew(lser) eq 0;
	end for;
    end for;
  end for;
end procedure;

procedure runTest()
    printf "Testing L series computation for O(5).";
    // This is quite long, so we reduce the precision
    // testLSeries(61, [[3,0],[3,2],[4,0]], 5);
    testLSeries(61, [[3,0],[3,2],[4,0]], 2);
    print "testing level 21, weight (3,2)....";
    // This is quite long, so we reduce the precision
    // testLSeries(21, [[3,2]], 5);
    testLSeries(21, [[3,2]], 2);
    // This does not seem to work at the moment for some reason!
    // print "testing level 26, weight (3,2)....";
    // testLSeries(26, [[3,2]], 5);
end procedure;

runTest();

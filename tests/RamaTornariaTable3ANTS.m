//SetVerbose("AlgebraicModularForms", 1);

procedure testRamaTornariaTable3ANTS()
  printf "Testing Table 3 from [RT] (Rama, Tornaria, computing orthogonal modular forms)...";
  ps := [5,61];
  disc := &*ps;
  divs := Divisors(disc);
  dims := [[[8,9,13],[],[1],[1,1,8,13]],[[1,1,1,1,3,6,8,13],[1,1],[1],[8,13]]];
  kers := [{1},{2,3,4,5,7}];
  traces := [[[[1,-21,12,-28,-10],
	     [57,119,69,505,1338],
	     [73,129,455,647,1660]],
	    [],
	    [[-4,-12,-4,9,-13]],
	    [[-2,2,-2,-19,21],
	     [2,-6,10,-3,29],
	     [3,-27,-6,-58,-54],
	     [81,157,325,669,1652]]],
	   [[[2,14,25,62,164],
	     [-7,-3,28,-9,-4],
	     [-2,2,-2,-19,21],
	     [2,-6,10,-3,29],
	     [-10,12,-20,-3,239],
	     [29,59,314,309,612],
	     [3,-27,-6,-58,-54],
	     [81,157,325,669,1652]],
	    [[-7,-3,-22,-9,-4],
	     [-4,-12,-4,9,-13]],
	    [[-6,-4,-20,13,-23]],			   
	    [[1,-21,12,-28,-10],
	     [73,129,455,647,1660]]]
	   ];
			     
  genera := QuinaryQuadraticLattices(disc);
  for lat_idx in [1,2] do
    vprintf AlgebraicModularForms, 1 : "testing lattice no. %o...\n", lat_idx;
    A := genera[lat_idx][1];
    G := OrthogonalGroup(A);
    for div_idx in [1..#divs] do
      d := divs[div_idx];
      vprintf AlgebraicModularForms, 1 : "testing d = %o...\n", d;
      vprintf AlgebraicModularForms, 1 : "checking dimensions...\n";
      spin := SpinorNormRepresentation(G, d);
      M := AlgebraicModularForms(G, spin);
      fs := HeckeEigenforms(M);
      if (d eq 1) then 
        cusps := [f : f in fs | not f`IsEisenstein];
      else
        cusps := fs;
      end if;
      f_dims := [Degree(BaseRing(f`vec)) : f in cusps];
      assert f_dims eq dims[lat_idx][div_idx];
      if d eq 1 then
        vprintf AlgebraicModularForms, 1 : "checking ker(theta)...\n";
        reps := Representatives(Genus(M));
        weights := [#AutomorphismGroup(rep)^(-1) : rep in reps];
        invs := [Invariant(rep) : rep in reps];
        thetas := [* &+[weights[i]*f`vec[i] *
		    PowerSeriesRing(BaseRing(f`vec))!invs[i]
		  : i in [1..#reps]] : f in cusps *];
        ker := {i : i in [1..#thetas] | IsEmpty(Coefficients(thetas[i]))};
        assert ker eq kers[lat_idx];
      end if;
      vprintf AlgebraicModularForms, 1 : "checking traces...\n";
      for dim in Set(f_dims) do
	 dim_idxs := [idx : idx in [1..#cusps] | f_dims[idx] eq dim];
         dim_traces := Set([]);
         for f_idx in dim_idxs do
	  f := cusps[f_idx];
	  evs, primes := HeckeEigensystem(f,1 : Precision := 11);
          bad_primes := [i : i in [1..#primes] | Norm(primes[i]) in ps];
          for idx in bad_primes do
	    evs[idx] +:= 1;
            if (d mod Norm(primes[idx]) eq 0) then
	      // eps_p := WittInvariant(Module(M), primes[idx]);
              evs[idx] *:= CharacterQQModSquares(disc, Rationals()!Norm(primes[idx]));
            end if;
          end for;
          tr_evs := [Trace(ev) : ev in evs];
          Include(~dim_traces, tr_evs);
        end for;
        tr_idxs := [idx : idx in [1..#dims[lat_idx][div_idx]]
			| dims[lat_idx][div_idx][idx] eq dim];
        dim_tr_test := Set([traces[lat_idx][div_idx][idx] : idx in tr_idxs]);
        assert dim_traces eq dim_tr_test;
     end for;
    end for;
  end for;
end procedure;

testRamaTornariaTable3ANTS();

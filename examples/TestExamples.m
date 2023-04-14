import "examples.m" : AlgebraicModularFormsExamples;

forward testExample;

// Run all tests on the examples from the Greenverg-Voight paper
// Can limit the number of primes for which Hecke operators are computed by setting NumPrimes.

function testExampleTimingsSaveAndLoad(example : NumPrimes := 0,
						  UseExisting := false,
						  Orbits := true,
						  Estimate := true,
						  UseLLL := true,
						  Decomposition := true,
						  LowMemory := false,
						  ThetaPrec := 25)
    printf "Testing example %o. ", example`name;
    // testing that we obtain the correct results
    M, timings := testExample(example : NumPrimes := NumPrimes,
					UseExisting := UseExisting,
					Orbits := Orbits,
					UseLLL := UseLLL,
					Estimate := Estimate,
				        Decomposition := Decomposition,
					LowMemory := LowMemory,
					ThetaPrec := ThetaPrec);
    printf "Timings for Hecke eigenvalues are ";
    for k in [1..#timings] do
	printf "k=%o: ", k;
	for timing in timings[k] do 
	    printf "%.3o ", timing;
	end for;
    end for;
    printf ". Memory used: %o. ", GetMemoryUsage();
    printf "Saving and loading...";
    // saving to a file
    fname := Sprintf("Example_%o.dat", example`name);
    Save(M, fname : Overwrite := true);
    // loading from the file and verifying we get the same object
    M2 := AlgebraicModularForms(fname);
    assert M eq M2;
    return M;
end function;

// function for testing the functionality of Hecke operators on a given example
function testHeckeOperators(M, example, ps, N :
			    UseLLL := true, Orbits := true, LowMemory := false,
			    Estimate := true, ThetaPrec := 25)
    timings := [];
    for k in [1..#example`evs[1]] do
	Ts_k := [];
	timings_k := [];
	
	for i in [1..N] do
	    p := ps[i];
	    printf "Computing T(p,%o), (N(p) = %o) ...\n", k, Norm(p);
	    t := Cputime();
	    // maybe should restrict Orbits to k eq 1 - ? check why !?
	    Append(~Ts_k, HeckeOperator(M, p, k : BeCareful := false,
						  Estimate := Estimate,
						  UseLLL := UseLLL,
					          Orbits := Orbits,
					LowMemory := LowMemory,
					ThetaPrec := ThetaPrec
				                  ));
	    timing := Cputime() - t;
	    printf "took %o seconds.\n", timing;
	    Append(~timings_k, timing);
	    if (#example`timing ge i) and (timing ne 0) then
		ratio := example`timing[i] / timing;
		printf "this should take %o times the time.\n", ratio;
	    end if;
	end for;
	print "Done.";

	// Verify that these operators commute with each other.
	assert &and[ A*B eq B*A : A,B in Ts_k ];
	Append(~timings, timings_k);
    end for;
    return timings;
end function;

// function for testing the functionality of hecke eigenvalues on a given examples
procedure test_evs(example, evs, keys, N)
    for j in [1..#example`evs] do
	found := false;
	for i in [1..#evs] do
	    ev_calc := [evs[i][keys[idx]] : idx in [1..#keys]];
	    F1 := FieldOfFractions(Universe(ev_calc[1]));
	    if not IsFinite(F1) then
		F1 := AbsoluteField(F1);
		zeta := PrimitiveElement(F1);
	    end if;
	    lens := [Minimum(N, #example`evs[j][k]) : k in keys];
	    ev := [example`evs[j][keys[idx]][1..lens[idx]] :
		   idx in [1..#keys]];
	    ev_calc := [ev_calc[idx][1..lens[idx]] : idx in [1..#keys]];
	    F2 := FieldOfFractions(Universe(ev[1]));
	    
	    if IsFinite(F1) then
		assert IsFinite(F2);
		L := GF(LCM(#F1, #F2));
		if IsPrimeField(F1) then
		    embs := [hom<F1->L|>];
		else
		    roots := [x[1] : x in Roots(MinimalPolynomial(F1.1), L)];
		    embs := [hom<F1 -> L | r> : r in roots];
		end if;
	    else
		assert not IsFinite(F2);
		F2 := AbsoluteField(F2);
		L := CompositeFields(F1, F2)[1];
		if Type(F1) eq FldRat then
		    embs := [hom<F1 -> L | >];
		else
		    roots := [x[1] : x in Roots(MinimalPolynomial(zeta), L)];
		    embs := [hom<F1 -> L | r> : r in roots];
		end if;
	    end if;
	    ev_L := [[L!y : y in x] : x in ev];
	    is_compat := exists(emb){emb : emb in embs |
				     [[emb(y) : y in x] : x in ev_calc] eq
				     ev_L};
	    
	    // we found compatible j, so we can go to the next i
	    if is_compat then
		found := true;
		break;
	    end if;
	end for;
	// There should have been at least one compatible j
	assert found;
    end for;
end procedure;

// function for testing the decomposition of the space for a given example
function testDecomposition(M, example, ps, N :
			   UseLLL := true,  Orbits := true, Estimate := true,
			   LowMemory := false, ThetaPrec := 25)
    
    D := Decomposition(M : Estimate := true,
		           UseLLL := UseLLL,
		       Orbits := Orbits,
		       LowMemory := LowMemory,
		       ThetaPrec := ThetaPrec);
    eigenforms := HeckeEigenforms(M);
    evs := [* *];
    RR := RealField();
    timings := [[RR | 0 : j in [1..N]]
		   : i in [1..#example`evs[1]]];
    for f in eigenforms do
	if f`IsEigenform then
	    evs_f := [];
	    for dim in [1..#example`evs[1]] do
                for j in [1..N] do
		  t := Cputime();
		  evs_j := HeckeEigensystem(f, dim : Precision := ps[1..j],
							 Estimate := Estimate,
							 UseLLL := UseLLL,
					    Orbits := Orbits,
					    LowMemory := LowMemory,
					    ThetaPrec := ThetaPrec);
		  timings[dim][j] +:= Cputime() - t;
                end for;
		Append(~evs_f, evs_j);
	    end for;
	    Append(~evs, evs_f);
	end if;
    end for;
    return eigenforms, evs, timings;
end function;

// function for a comprhensive test of an example
function testExample(example : NumPrimes := 0, UseExisting := false,
		     Orbits := true, UseLLL := true, Estimate := true,
		     Decomposition := true, LowMemory := false,
		     ThetaPrec := 25)
    fname := Sprintf("Example_%o.dat", example`name);
    if UseExisting and FileExists(GetAMFPath() cat fname : ShowErrors := false) then
	M := AlgebraicModularForms(fname);
    else
	if example`group eq "Unitary" then
	    M := UnitaryModularForms(example`field, example`inner_form,
				     example`weight, example`coeff_char);
	elif example`group eq "Orthogonal" then
	    M := OrthogonalModularForms(example`field, example`inner_form,
					example`weight, example`coeff_char
					: d := example`spinor);
	elif example`group eq "SpecialOrthogonal" then
	    M := OrthogonalModularForms(example`field, example`inner_form,
					example`weight, example`coeff_char
					: Special, d := example`spinor);
	else
	    error "The group type %o is currently not supported!";
	end if;
    end if;
    
    printf "Computing genus representatives... ";
    _ := Representatives(Genus(M));
    printf "Done. ";
    printf "Found %o genus reps. ", #Representatives(Genus(M));

    assert #Representatives(Genus(M)) eq example`genus;

    if NumPrimes eq 0 then
	N := #example`norm_p;
    else
	N := NumPrimes;
    end if;
    
    ps := [Factorization(ideal<Integers(BaseRing(M))|n>)[1][1] :
	   n in example`norm_p];
    
    if Decomposition then
	printf "Decomposing the space, computing eigenforms...";
        eigenforms, evs, timings := testDecomposition(M, example, ps, N : 
						      UseLLL := UseLLL,
						      Orbits := Orbits,
						      Estimate := Estimate,
						      LowMemory := LowMemory,
						      ThetaPrec := ThetaPrec);
	printf "Done. ";
	keys := [1..#example`evs[1]];
    else
	printf "Computing T(p) Hecke operators...";
        timings := testHeckeOperators(M, example, ps, N : 
				      UseLLL := UseLLL,
				      Orbits := Orbits,
				      Estimate := Estimate,
				      LowMemory := LowMemory,
				      ThetaPrec := ThetaPrec);
	printf "Done. ";
	keys := Keys(M`Hecke`Ts);
	keys := Sort([ x : x in keys ]);
	// Compute eigenforms associated to this space of modular forms.
	eigenforms := HeckeEigenforms(M);
	
        evs := [* [HeckeEigensystem(f, dim
				    : Precision := ps[1..N]) : dim in keys]
		   : f in eigenforms | f`IsEigenform *];  
    end if;

    // Check that the eigenvalues agree with the papers
  
    test_evs(example, evs, keys, N);

    return M, timings;
end function;

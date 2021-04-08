freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         

   FILE: hecke-CN1.m (Implementation for computing Hecke matrices)

   05/29/20: Modified SkipToNeighbor to handle non-liftable isotropic subspaces

   05/27/20: Fixed a bug for SO(n) - automorphism groups were wrongly built.
             Changed default values to use orbit method and estimate, and not
             use LLL.

   05/26/20: Modified HeckeOperatorCN1 to support non-liftable isotropic vectors

   05/11/20: Added support for the Orbit method for k > 1, increasing
             efficiency.

   05/08/20: Fixed a bug in HeckeOperatorCN1SparseBasis with Orbits = false.

   05/04/20: Modified the orbit method to work with any weight.

   04/27/20: Changed default value of parameter BeCareful to false.

   04/24/20: Modified HeckeOperatorCN1 to include a parameter indicating 
             whether the isometries should be special.
             Moved all old code to the end.

   04/14/20: Added the parameter UseLLL.
 
   04/13/20: Added Time Estimates for the computations.

   03/26/20: Added some verbose print outs for debugging and profiling.
             Moved the calculation of the space from the Hecke operator
             computation to the initialization of the space.
             Made some modifications to enable weight spaces over rings
             other than QQ (e.g. finite fields)

   03/11/20: Modified HeckeOperatorTrivialWeightCN1 to have an optional
             parameter invoking the orbit method.
   	     Added the procedure processNeighbor, for better readability 
             and modularity of the code, towards introducing orbits

   03/10/20: started editing this file to add Unitary forms
 
 ***************************************************************************/

// imports

import "inv-CN1.m" : Invariant;
import "neighbor-CN1.m" : BuildNeighborProc, BuildNeighbor,
	GetNextNeighbor, SkipToNeighbor;
import "orbits.m" : build_polycyclic_data, orb_stab_pc, orb_stab_general;

procedure printEstimate(start, ~count, ~elapsed,
			fullCount, pR, k :
			increment := 1,
			printSkip := 1000,
			printOffset := 500,
			timeSkip := 5)

    // Increment counter.
    count +:= increment;

    last_elapsed := elapsed;

    // Elapsed real time.
    new_elapsed := Realtime() - start;
    
    if (count mod printSkip eq printOffset) or
       (new_elapsed gt last_elapsed + timeSkip) then

	// updating last time we printed an estimate
	elapsed := new_elapsed;

	// Seconds per neighbor computation.
	t := RealField()!(elapsed / count);

	// Number of neighbors left to compute.
	remaining := fullCount - count;

	// Estimate time remaining (in seconds).
	estimate := t * remaining;

	// Minutes remaining.
	mins := Floor(estimate / 60);

	// Seconds (modulo minutes) remaining.
	secs := Floor(estimate - mins*60);

	// Hours remaining.
	hours := Floor(mins / 60);
    
	// Minutes (modulo hours) remaining.
	mins -:= hours * 60;
    
	// Days remaining.
	days := Floor(hours / 24);
	
	// Hours (modulo days) remaining.
	hours -:= days * 24;

	// Display estimate.
	printf "Estimated time remaining for T_%o^%o:"
	       cat " %od %oh %om %os\n",
	       Norm(pR), k, days, hours, mins, secs;

        vprintf AlgebraicModularForms, 2 :
	  "Current memory usage:%o\n", GetMemoryUsage();
    end if;
end procedure;

// idx is i from the paper

procedure processNeighborWeight(~nProc, invs, ~hecke,
				idx, H :
				BeCareful := false,
				UseLLL := false,
				Weight := 1,
				Special := false)
    // Build the neighbor lattice corresponding to the
    //  current state of nProc.
    nLat := BuildNeighbor(nProc : BeCareful := BeCareful, UseLLL := UseLLL);

    if GetVerbose("AlgebraicModularForms") ge 2 then
	printf "Processing neighbor corresponding to isotropic subspace ";
	printf "indexed by %o.\n", nProc`isoSubspace;
	if GetVerbose("AlgebraicModularForms") ge 3 then
	    printf "Lattice is %o\n", nLat;
	end if;
    end if;

    // Compute the invariant of the neighbor lattice.
    inv := Invariant(nLat);

    // Retrieve the array of isometry classes matching this
    //  invariant.
    array := invs[inv];

    // Flag to determine whether an isometry class
    //  was actually found. This is a failsafe.
    found := false;

    iota := H[idx]`embedding;
    
    W := Codomain(iota);
    
    for j in [1..#array] do
	// Check for isometry.
	iso, g := IsIsometric(nLat, array[j][1] :
			      Special := Special, BeCareful := BeCareful);

	// If isometric, flag as found,
	//  increment Hecke matrix, and move on.
	if iso then
	    space_idx := array[j][2];
	    
	    if GetVerbose("AlgebraicModularForms") ge 2 then
		printf "Neighbor is isometric to genus %o.\n", space_idx;
	    end if;
	   
	    gg := W`G!ChangeRing(Transpose(g), BaseRing(W`G));

	    if GetVerbose("AlgebraicModularForms") ge 2 then
		print "Updating the Hecke operator...";
	    end if;
	    
	    found := true;
	    iota := H[space_idx]`embedding;
	    for vec_idx in [1..Dimension(H[space_idx])] do
	    	vec := gg * (iota(H[space_idx].vec_idx));
		hecke[space_idx][vec_idx][idx] +:= Weight * vec;
	    end for;
	    break;
	end if;
    end for;

    // Verify that the neighbor was indeed isometric
    //  to something in our list.
    assert found;
  
end procedure;

procedure HeckeOperatorCN1Update(reps, idx, pR, k, M, ~hecke, invs,
				 start, ~count, ~elapsed, fullCount :
				 BeCareful := false,
				 Orbits := true,
				 UseLLL := false,
				 Estimate := true)
    L := reps[idx];

    Q := ReflexiveSpace(Module(M));
    n := Dimension(Q);

    // Build neighboring procedure for this lattice.
    nProc := BuildNeighborProc(L, pR, k
			       : BeCareful := BeCareful);

    if GetVerbose("AlgebraicModularForms") ge 1 then
	printf "Computing %o%o-neighbors for isometry class "
	       cat "representative #%o...\n", pR,
	       k eq 1 select "" else "^" cat IntegerToString(k),
	       idx;
    end if;
	
    if Orbits then
	// The affine vector space.
	V := nProc`L`Vpp[pR]`V;
	
	// The base field.
	F := BaseRing(V);
	
	// The automorphism group restricted to the affine space.
	G := AutomorphismGroup(L : Special := IsSpecialOrthogonal(M));
	
	gens := [PullUp(Matrix(g), L, L :
			BeCareful := BeCareful) :
		 g in Generators(G)];
	
	pMaximalBasis :=
	    ChangeRing(L`pMaximal[nProc`pR][2], BaseRing(Q));
	
	conj_gens := [pMaximalBasis * g * pMaximalBasis^(-1) :
		      g in gens];
	
	gens_modp := [[L`Vpp[pR]`proj_pR(x) : x in Eltseq(g)]
		      : g in conj_gens];
	
	Aut := sub<GL(n, F) | gens_modp>;
	fp_aut, psi := FPGroup(Aut);

	// The isotropic orbit data.
	isoOrbits := IsotropicOrbits(V, Aut, k);
	    
	for orbit in isoOrbits do
	    skew0 := Zero(MatrixRing(F, k));
	    // Skip to the neighbor associated to this orbit.
	    SkipToNeighbor(~nProc, Basis(orbit[1]), skew0);
	    // In case it doesn't lift
	    if IsEmpty(nProc`X) then
		continue;
	    end if;
	    mat_gen_seq := [[gens[Index(gens_modp,
					Eltseq(Aut.Abs(i)))]^Sign(i) :
			     i in Eltseq(g@@psi)] :
			    g in orbit[2]];
	    mat_lifts := [IsEmpty(seq) select GL(n,BaseRing(Q))!1 else
			  &*seq : seq in mat_gen_seq];

	    w := &+[Matrix(getMatrixAction(M`W, Transpose(M`W`G!g))) :
		    g in mat_lifts];
	    // Changing the skew matrix, but not the isotropic
	    // subspace mod p
	    repeat
		processNeighborWeight(~nProc, invs, ~hecke, idx, M`H:
				      BeCareful := BeCareful,
				      UseLLL := UseLLL,
				      Weight := w,
				      Special := IsSpecialOrthogonal(M));
		// Update nProc in preparation for the next neighbor
		//  lattice.
		GetNextNeighbor(~nProc
				: BeCareful := BeCareful);
		if Estimate then
		    printEstimate(start, ~count, ~elapsed,
				  fullCount, pR, k :
				  increment := #orbit[2]);
		end if;
	    until (nProc`skewDim eq 0) or (nProc`skew eq skew0);
	end for;
    else
	while nProc`isoSubspace ne [] do
	    processNeighborWeight(~nProc, invs, ~hecke, idx, M`H :
				  BeCareful := BeCareful,
				  UseLLL := UseLLL,
				  Special := IsSpecialOrthogonal(M));
	    // Update nProc in preparation for the next neighbor
	    //  lattice.
	    GetNextNeighbor(~nProc
			    : BeCareful := BeCareful);
	    if Estimate then
		printEstimate(start, ~count, ~elapsed,
			      fullCount, pR, k);
	    end if;
	end while;
    end if;
end procedure;

function HeckeOperatorCN1(M, pR, k
			  : BeCareful := false,
			    UseLLL := false,
			    Estimate := true,
			    Orbits := true)
    
    // The genus representatives.
    reps := Representatives(Genus(M));

    hecke := [ [ [* M`W!0 : hh in M`H *] : vec_idx in [1..Dimension(h)]]
		 : h in M`H];

    // An associative array indexed by a specified invariant of an isometry
    //  class. This data structure allows us to bypass a number of isometry
    //  tests by filtering out those isometry classes whose invariant
    //  differs from the one specified.
    invs := M`genus`RepresentativesAssoc;

    Q := ReflexiveSpace(Module(M));
    n := Dimension(Q);

    fullCount := #M`H * NumberOfNeighbors(M, pR, k);
    count := 0;
    elapsed := 0;
    start := Realtime();
	
    for idx in [1..#M`H] do
	   //   for idx in [1..#rep_idxs] do
	// The current isometry class under consideration.
	L := reps[idx];

	// Build neighboring procedure for this lattice.
	nProc := BuildNeighborProc(L, pR, k
				   : BeCareful := BeCareful);

	if GetVerbose("AlgebraicModularForms") ge 1 then
	    printf "Computing %o%o-neighbors for isometry class "
		   cat "representative #%o...\n", pR,
		   k eq 1 select "" else "^" cat IntegerToString(k),
					   idx;
	end if;
	
	if Orbits then
	    // The affine vector space.
	    V := nProc`L`Vpp[pR]`V;

	    // The base field.
	    F := BaseRing(V);

	    // The automorphism group restricted to the affine space.
	    G := AutomorphismGroup(L : Special := IsSpecialOrthogonal(M));

	    gens := [PullUp(Matrix(g), L, L :
			    BeCareful := BeCareful) :
		     g in Generators(G)];

	    pMaximalBasis :=
		ChangeRing(L`pMaximal[nProc`pR][2], BaseRing(Q));

	    conj_gens := [pMaximalBasis * g * pMaximalBasis^(-1) :
		     g in gens];

	    gens_modp := [[L`Vpp[pR]`proj_pR(x) : x in Eltseq(g)]
			  : g in conj_gens];
		 
	    Aut := sub<GL(n, F) | gens_modp>;
	    fp_aut, psi := FPGroup(Aut);

	    // The isotropic orbit data.
	    isoOrbits := IsotropicOrbits(V, Aut, k);
	    
	    for orbit in isoOrbits do
		skew0 := Zero(MatrixRing(F, k));
		// Skip to the neighbor associated to this orbit.
		SkipToNeighbor(~nProc, Basis(orbit[1]), skew0);
		// In case it doesn't lift
		if IsEmpty(nProc`X) then
		    continue;
		end if;
		mat_gen_seq := [[gens[Index(gens_modp,
					    Eltseq(Aut.Abs(i)))]^Sign(i) :
				 i in Eltseq(g@@psi)] :
				g in orbit[2]];
		mat_lifts := [IsEmpty(seq) select GL(n,BaseRing(Q))!1 else
			      &*seq : seq in mat_gen_seq];

		w := &+[Matrix(getMatrixAction(M`W, Transpose(M`W`G!g))) :
			g in mat_lifts];
		// Changing the skew matrix, but not the isotropic
		// subspace mod p
		repeat
		    processNeighborWeight(~nProc, invs, ~hecke, idx, M`H:
					  BeCareful := BeCareful,
					  UseLLL := UseLLL,
					  Weight := w,
					  Special := IsSpecialOrthogonal(M));
		    // Update nProc in preparation for the next neighbor
		    //  lattice.
		    GetNextNeighbor(~nProc
				    : BeCareful := BeCareful);
		    if Estimate then
			printEstimate(start, ~count, ~elapsed,
				      fullCount, pR, k :
				      increment := #orbit[2]);
		    end if;
		until (nProc`skewDim eq 0) or (nProc`skew eq skew0);
	    end for;
	else
	    while nProc`isoSubspace ne [] do
		processNeighborWeight(~nProc, invs, ~hecke, idx, M`H :
				      BeCareful := BeCareful,
				      UseLLL := UseLLL,
				      Special := IsSpecialOrthogonal(M));
		// Update nProc in preparation for the next neighbor
		//  lattice.
		GetNextNeighbor(~nProc
				: BeCareful := BeCareful);
		if Estimate then
		    printEstimate(start, ~count, ~elapsed,
				  fullCount, pR, k);
		end if;
	    end while;
	end if;
    end for;

    iota := [h`embedding : h in M`H];

    mats := [[[Eltseq(hecke[space_idx][vec_idx][idx]@@iota[idx]) :
		      vec_idx in [1..Dimension(M`H[space_idx])]] :
           space_idx in [1..#M`H]] : idx in [1..#M`H]];

    vert_blocks := [&cat mat : mat in mats];

    empty_operator := MatrixAlgebra(BaseRing(M),0)![];
    
    if IsEmpty(vert_blocks) then return empty_operator; end if;
    if IsEmpty(vert_blocks[1]) then return empty_operator; end if;
    
    vert_mats := [* Matrix(blk) : blk in vert_blocks |
		  not IsEmpty(blk[1]) *];

    if IsEmpty(vert_mats) then return empty_operator; end if;

    // would have done a one liner, but there are universe issues
    ret := vert_mats[1];
    for idx in [2..#vert_mats] do
	ret := HorizontalJoin(ret, vert_mats[idx]);
    end for;
    
    return ret;
end function;

// For efficiency, we implement computation of the Hecke operator on a single
// (sparse) vector

// inv = <Invariant(reps[space_idx]), reps[space_idx]>
procedure processNeighborWeightSparse(~nProc, inv, ~hecke,
				      idx, H, space_idx, vec_idx :
				      BeCareful := false,
				      UseLLL := false,
				      Weight := [],
				      Special := false)
    // Build the neighbor lattice corresponding to the
    //  current state of nProc.
    nLat := BuildNeighbor(nProc : BeCareful := BeCareful, UseLLL := UseLLL);

    if GetVerbose("AlgebraicModularForms") ge 2 then
	printf "Processing neighbor corresponding to isotropic subspace ";
	printf "indexed by %o.\n", nProc`isoSubspace;
	if GetVerbose("AlgebraicModularForms") ge 3 then
	    printf "Lattice is %o\n", nLat;
	end if;
    end if;

    // Compute the invariant of the neighbor lattice.
    if inv[1] ne Invariant(nLat) then return; end if;

    // Check for isometry.
    iso, g := IsIsometric(nLat, inv[2] :
			  Special := Special, BeCareful := BeCareful);
    
    if not iso then return; end if;

    iota := H[space_idx]`embedding;
    W := Codomain(iota);

    w := &+[Matrix(getMatrixAction(W, Transpose(W`G!g))) : g in Weight];
   	    
    gg := W`G!ChangeRing(Transpose(g), BaseRing(W`G));

    if GetVerbose("AlgebraicModularForms") ge 2 then
	print "Updating the Hecke operator...";
    end if;
	   
    vec := gg * (iota(H[space_idx].vec_idx));
    hecke[idx] +:= w * vec;

end procedure;

forward HeckeOrbitLowMemorySingleIndex;

// compute T_p(e_{i,j}) where i = space_idx, j = vec_idx
function HeckeOperatorCN1SparseBasis(M, pR, k, idx
				     : BeCareful := false,
				       UseLLL := false,
				       Estimate := true,
				       Orbits := true,
				       LowMemory := false)

    assert 1 le idx and idx le #M`H;
    // The genus representatives.
    reps := Representatives(Genus(M));
    
    hecke := [ [ [* M`W!0 : hh in M`H*] : vec_idx in [1..Dimension(h)]] :
	       h in M`H];

    invs := M`genus`RepresentativesAssoc;

    Q := ReflexiveSpace(Module(M));
    n := Dimension(Q);

    fullCount := NumberOfNeighbors(M, pR, k);
    count := 0;
    elapsed := 0;
    start := Realtime();

    if Orbits and LowMemory then
      HeckeOrbitLowMemorySingleIndex(~nProc, invs, ~hecke, idx, M`H, M`W, k,
			      start, ~count, ~elapsed, fullCount :
			      BeCareful := false,
			      UseLLL := true,
			      Special := false,
				     Estimate := true);
    else
      HeckeOperatorCN1Update(reps, idx, pR, k, M, ~hecke, invs,
				 start, ~count, ~elapsed, fullCount :
				 BeCareful := BeCareful,
				 Orbits := Orbits,
				 UseLLL := UseLLL,
				 Estimate := Estimate);
    end if;
    
    iota := M`H[idx]`embedding;
   
    mats := [[[Eltseq(hecke[space_idx][vec_idx][idx]@@iota) :
	       vec_idx in [1..Dimension(M`H[space_idx])]] :
	      space_idx in [1..#M`H]]];

    vert_blocks := [&cat mat : mat in mats];

    empty_operator := MatrixAlgebra(BaseRing(M),0)![];
    
    if IsEmpty(vert_blocks) then return empty_operator; end if;
    if IsEmpty(vert_blocks[1]) then return empty_operator; end if;
    
    vert_mats := [* Matrix(blk) : blk in vert_blocks |
		  not IsEmpty(blk[1]) *];

    if IsEmpty(vert_mats) then return empty_operator; end if;

    // would have done a one liner, but there are universe issues
    ret := vert_mats[1];
    for i in [2..#vert_mats] do
	ret := HorizontalJoin(ret, vert_mats[i]);
    end for;
    
    return ret;
end function;

function HeckeOperatorCN1Sparse(M, pR, k, s
				: BeCareful := false,
				  UseLLL := false,
				  Estimate := true,
				  Orbits := true,
				  LowMemory := false)
    ret := [* KMatrixSpace(BaseRing(M`H[1]),Dimension(M),Dimension(h))!0 :
	    h in M`H *];
    for tup in s do
	scalar := tup[1];
	space_idx := tup[2];
       
	hecke := scalar *
		 HeckeOperatorCN1SparseBasis(M, pR, k, space_idx
					     : BeCareful := BeCareful,
					       UseLLL := UseLLL,
					       Estimate := Estimate,
					       Orbits := Orbits,
					       LowMemory := LowMemory);
	ret[space_idx] +:= hecke;
    end for;
    return ret;
end function;


procedure processNeighborWeightWithGenus(~nProc, ~reps, ~invs, ~hecke,
					 idx, ~H :
					 BeCareful := false,
					 UseLLL := false,
					 Weight := 1,
					 Special := false)
    // Build the neighbor lattice corresponding to the
    //  current state of nProc.
    nLat := BuildNeighbor(nProc : BeCareful := BeCareful, UseLLL := UseLLL);

    if GetVerbose("AlgebraicModularForms") ge 2 then
	printf "Processing neighbor corresponding to isotropic subspace ";
	printf "indexed by %o.\n", nProc`isoSubspace;
	if GetVerbose("AlgebraicModularForms") ge 3 then
	    printf "Lattice is %o\n", nLat;
	end if;
    end if;

    // Compute the invariant of the neighbor lattice.
    inv := Invariant(nLat);

    // Retrieve the array of isometry classes matching this
    //  invariant.
    if not IsDefined(invs, inv) then
       invs[inv] := [];
    end if;
    array := invs[inv];

    // Flag to determine whether an isometry class
    //  was actually found. This is a failsafe.
    found := false;

    iota := H[idx]`embedding;
    
    W := Codomain(iota);
    
    for j in [1..#array] do
	// Check for isometry.
	iso, g := IsIsometric(nLat, array[j][1] :
			      Special := Special, BeCareful := BeCareful);

	// If isometric, flag as found,
	//  increment Hecke matrix, and move on.
	if iso then
	    space_idx := array[j][2];
	    
	    if GetVerbose("AlgebraicModularForms") ge 2 then
		printf "Neighbor is isometric to genus %o.\n", space_idx;
	    end if;
	   
	    gg := W`G!ChangeRing(Transpose(g), BaseRing(W`G));

	    if GetVerbose("AlgebraicModularForms") ge 2 then
		print "Updating the Hecke operator...";
	    end if;
	    
	    found := true;
	    iota := H[space_idx]`embedding;
	    for vec_idx in [1..Dimension(H[space_idx])] do
	    	vec := gg * (iota(H[space_idx].vec_idx));
		hecke[space_idx][vec_idx][idx] +:= Weight * vec;
	    end for;
	    break;
	end if;
    end for;

    if not found then
      Append(~reps, nLat);
      Append(~invs[inv], <nLat, #reps>);
      gamma_rep := AutomorphismGroup(nLat : Special := Special);
      gamma := sub<W`G|
		[Transpose(PullUp(Matrix(g), nLat, nLat :
				  BeCareful := BeCareful)) :
			  g in Generators(gamma_rep)]>;
      h := FixedSubspace(gamma, W);
      for h_idx in [1..#H] do
	for v_idx in [1..Dimension(H[h_idx])] do
	  Append(~hecke[h_idx][v_idx], W!0);
        end for;
      end for;

      Append(~H, h);
      Append(~hecke, [ [* W!0 : hh in H *] : i in [1..Dimension(h)]]);

      if GetVerbose("AlgebraicModularForms") ge 2 then
	 print "Updating the Hecke operator...";
      end if;
	    
      iota := h`embedding;
      for vec_idx in [1..Dimension(h)] do
	vec := iota(h.vec_idx);
	hecke[#reps][vec_idx][idx] +:= Weight * vec;
      end for;
    end if;
  
end procedure;


procedure HeckeOperatorAndGenusCN1(~M, pR, k, ~result
				   : BeCareful := false,
				   UseLLL := false,
				   Estimate := true,
				   Orbits := true)
   
    L := Module(M);
    reps := [L];
    invs := AssociativeArray();
    invs[Invariant(L)] := [<L, 1>];
    gamma_rep := AutomorphismGroup(L : Special := IsSpecialOrthogonal(M));
    gamma := sub<M`W`G|
		[Transpose(PullUp(Matrix(g), L, L :
				  BeCareful := BeCareful)) :
			  g in Generators(gamma_rep)]>;
    M`H := [FixedSubspace(gamma, M`W)];

    hecke := [ [ [* M`W!0 : hh in M`H *] : vec_idx in [1..Dimension(h)]]
		 : h in M`H];

    Q := ReflexiveSpace(Module(M));
    n := Dimension(Q);

    fullCount := #M`H * NumberOfNeighbors(M, pR, k);
    count := 0;
    elapsed := 0;
    start := Realtime();

    idx := 1;
    while (idx le #M`H) do
	   //   for idx in [1..#rep_idxs] do
	// The current isometry class under consideration.
	L := reps[idx];

	// Build neighboring procedure for this lattice.
	nProc := BuildNeighborProc(L, pR, k
				   : BeCareful := BeCareful);

	if GetVerbose("AlgebraicModularForms") ge 1 then
	    printf "Computing %o%o-neighbors for isometry class "
		   cat "representative #%o...\n", pR,
		   k eq 1 select "" else "^" cat IntegerToString(k),
					   idx;
	end if;
	
	if Orbits then
	    // The affine vector space.
	    V := nProc`L`Vpp[pR]`V;

	    // The base field.
	    F := BaseRing(V);

	    // The automorphism group restricted to the affine space.
	    G := AutomorphismGroup(L : Special := IsSpecialOrthogonal(M));

	    gens := [PullUp(Matrix(g), L, L :
			    BeCareful := BeCareful) :
		     g in Generators(G)];

	    pMaximalBasis :=
		ChangeRing(L`pMaximal[nProc`pR][2], BaseRing(Q));

            // All this wiggling around is because we can't define a map
            // GL(n, R_p) -> GL(n, F) from the localization at p

	    conj_gens := [pMaximalBasis * g * pMaximalBasis^(-1) :
		     g in gens];

	    gens_modp := [[L`Vpp[pR]`proj_pR(x) : x in Eltseq(g)]
			  : g in conj_gens];
		 
	    Aut := sub<GL(n, F) | gens_modp>;
	    fp_aut, psi := FPGroup(Aut);

	    // The isotropic orbit data.
	    isoOrbits := IsotropicOrbits(V, Aut, k);
	    
	    for orbit in isoOrbits do
		skew0 := Zero(MatrixRing(F, k));
		// Skip to the neighbor associated to this orbit.
		SkipToNeighbor(~nProc, Basis(orbit[1]), skew0);
		// In case it doesn't lift
		if IsEmpty(nProc`X) then
		    continue;
		end if;
		mat_gen_seq := [[gens[Index(gens_modp,
					    Eltseq(Aut.Abs(i)))]^Sign(i) :
				 i in Eltseq(g@@psi)] :
				g in orbit[2]];
		mat_lifts := [IsEmpty(seq) select GL(n,BaseRing(Q))!1 else
			      &*seq : seq in mat_gen_seq];

		w := &+[Matrix(getMatrixAction(M`W, Transpose(M`W`G!g))) :
			g in mat_lifts];
		// Changing the skew matrix, but not the isotropic
		// subspace mod p
		repeat
	            processNeighborWeightWithGenus(~nProc, ~reps, ~invs,
						   ~hecke, idx, ~M`H:
						   BeCareful := BeCareful,
						   UseLLL := UseLLL,
						   Weight := w,
						   Special :=
						   IsSpecialOrthogonal(M));
		    // Update nProc in preparation for the next neighbor
		    //  lattice.
		    GetNextNeighbor(~nProc
				    : BeCareful := BeCareful);
		    if Estimate then
			printEstimate(start, ~count, ~elapsed,
				      fullCount, pR, k :
				      increment := #orbit[2]);
		    end if;
		until (nProc`skewDim eq 0) or (nProc`skew eq skew0);
	    end for;
	else
	    while nProc`isoSubspace ne [] do
		processNeighborWeightWithGenus(~nProc, ~reps, ~invs,
					       ~hecke, idx, ~M`H :
					       BeCareful := BeCareful,
					       UseLLL := UseLLL,
					       Special :=
					       IsSpecialOrthogonal(M));
		// Update nProc in preparation for the next neighbor
		//  lattice.
		GetNextNeighbor(~nProc
				: BeCareful := BeCareful);
		if Estimate then
		    printEstimate(start, ~count, ~elapsed,
				  fullCount, pR, k);
		end if;
	    end while;
	end if;
        idx +:= 1;
    end while;

    // update genus
    M`genus := New(GenusSym);
    M`genus`Representative := M`L;
    M`genus`Representatives := reps;
    M`genus`RepresentativesAssoc := invs;
	     
    iota := [h`embedding : h in M`H];

    mats := [[[Eltseq(hecke[space_idx][vec_idx][idx]@@iota[idx]) :
		      vec_idx in [1..Dimension(M`H[space_idx])]] :
           space_idx in [1..#M`H]] : idx in [1..#M`H]];

    vert_blocks := [&cat mat : mat in mats];

    empty_operator := MatrixAlgebra(BaseRing(M),0)![];
    
    if IsEmpty(vert_blocks) then result := empty_operator; return; end if;
    if IsEmpty(vert_blocks[1]) then result := empty_operator; return; end if;
    
    vert_mats := [* Matrix(blk) : blk in vert_blocks |
		  not IsEmpty(blk[1]) *];

    if IsEmpty(vert_mats) then result := empty_operator; return; end if;

    // would have done a one liner, but there are universe issues
    result := vert_mats[1];
    for idx in [2..#vert_mats] do
	result := HorizontalJoin(result, vert_mats[idx]);
    end for;
    
end procedure;



procedure HeckeOrbitLowMemorySingleIndex(~nProc, invs,  ~hecke, idx, H, W, k,
			      start, ~count, ~elapsed, fullCount :
			      BeCareful := false,
			      UseLLL := true,
			      Special := false,
			      Estimate := true)
  L := nProc`L;
  Q := ReflexiveSpace(L);
  n := Dimension(Q);
  pR := nProc`pR;
  V := L`Vpp[pR]`V;
  G := AutomorphismGroup(L : Special := Special);
  gens := [PullUp(Matrix(g), L, L : BeCareful := BeCareful)
	      : g in Generators(G)];
  pMaximalBasis := ChangeRing(L`pMaximal[pR][2], BaseRing(Q));
  conj_gens := [pMaximalBasis * g * pMaximalBasis^(-1) : g in gens];
  proj := L`Vpp[pR]`proj_pR;
  R := Domain(proj);
  F := Codomain(proj);
  G_conj := sub<GL(n,BaseRing(Q)) | conj_gens>;
  is_solvable, G_pc, f_pc, red := build_polycyclic_data(G_conj, V, proj);
  orb_stab := is_solvable select orb_stab_pc else orb_stab_general;
  orb_reps := [];
  y := nProc`isoSubspace;
  skew0 := Zero(MatrixRing(F, k));
  while y ne [] do
    gens_y := [ b * Transpose(V`Basis) : b in y ];
    W_y := sub<V | gens_y>;
    orb, stab := orb_stab(G_pc, f_pc, W_y);
    found := false;
    for x in orb_reps do
      gens_x := [ b * Transpose(V`Basis) : b in x ];
      W_x := sub<V | gens_x>;
      if W_x in orb then
        found := true;
        break;
      end if;
    end for;
    if not found then
      Append(~orb_reps, y);
      coset_reps_pc := Transversal(G_pc, stab);
      coset_reps_conj := [g@@red : g in coset_reps_pc];
      coset_reps := [pMaximalBasis^(-1)*ChangeRing(g, BaseRing(Q))*pMaximalBasis
			: g in coset_reps_conj];
      // Append(~g_reps, coset_reps);
      w := &+[Matrix(getMatrixAction(W, Transpose(W`G!g))) : g in coset_reps];
      // Skip to the neighbor associated to this orbit.
      SkipToNeighbor(~nProc, y, skew0);
      // Changing the skew matrix, but not the isotropic
      // subspace mod p
      repeat
         processNeighborWeight(~nProc, invs, ~hecke, idx, H:
					  BeCareful := BeCareful,
					  UseLLL := UseLLL,
					  Weight := w,
					  Special := Special);
         // Update nProc in preparation for the next neighbor
         //  lattice.
	 GetNextNeighbor(~nProc : BeCareful := BeCareful);
         if Estimate then
	    printEstimate(start, ~count, ~elapsed,
			  fullCount, pR, k : increment := #orb);
	 end if;
      until (nProc`skewDim eq 0) or (nProc`skew eq skew0);
    else
      GetNextNeighbor(~nProc : BeCareful := BeCareful);
    end if;
    y := nProc`isoSubspace;
  end while;
end procedure;

function HeckeOperatorCN1OrbitLowMemory(M, pR, k
			  : BeCareful := false,
			    UseLLL := false,
			    Estimate := true)
    
    // The genus representatives.
    reps := Representatives(Genus(M));

    hecke := [ [ [* M`W!0 : hh in M`H *] : vec_idx in [1..Dimension(h)]]
		 : h in M`H];

    // An associative array indexed by a specified invariant of an isometry
    //  class. This data structure allows us to bypass a number of isometry
    //  tests by filtering out those isometry classes whose invariant
    //  differs from the one specified.
    invs := M`genus`RepresentativesAssoc;

    Q := ReflexiveSpace(Module(M));
    n := Dimension(Q);

    fullCount := #M`H * NumberOfNeighbors(M, pR, k);
    count := 0;
    elapsed := 0;
    start := Realtime();
	
    for idx in [1..#M`H] do
	// The current isometry class under consideration.
	L := reps[idx];

	// Build neighboring procedure for this lattice.
	nProc := BuildNeighborProc(L, pR, k
				   : BeCareful := BeCareful);

	if GetVerbose("AlgebraicModularForms") ge 1 then
	    printf "Computing %o%o-neighbors for isometry class "
		   cat "representative #%o...\n", pR,
		   k eq 1 select "" else "^" cat IntegerToString(k),
					   idx;
	end if;
	
        HeckeOrbitLowMemorySingleIndex(~nProc, invs, ~hecke, idx, M`H, M`W, k,
				       start, ~count, ~elapsed, fullCount :
				       Special := IsSpecialOrthogonal(M),
				       Estimate := Estimate,
				       UseLLL := UseLLL,
				       BeCareful := BeCareful);
    end for;

    iota := [h`embedding : h in M`H];

    mats := [[[Eltseq(hecke[space_idx][vec_idx][idx]@@iota[idx]) :
		      vec_idx in [1..Dimension(M`H[space_idx])]] :
           space_idx in [1..#M`H]] : idx in [1..#M`H]];

    vert_blocks := [&cat mat : mat in mats];

    empty_operator := MatrixAlgebra(BaseRing(M),0)![];
    
    if IsEmpty(vert_blocks) then return empty_operator; end if;
    if IsEmpty(vert_blocks[1]) then return empty_operator; end if;
    
    vert_mats := [* Matrix(blk) : blk in vert_blocks |
		  not IsEmpty(blk[1]) *];

    if IsEmpty(vert_mats) then return empty_operator; end if;

    // would have done a one liner, but there are universe issues
    ret := vert_mats[1];
    for idx in [2..#vert_mats] do
	ret := HorizontalJoin(ret, vert_mats[idx]);
    end for;
    
    return ret;
end function;

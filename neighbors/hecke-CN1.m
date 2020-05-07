freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: hecke-CN1.m (Implementation for computing Hecke matrices)

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
    end if;
end procedure;

// idx is i from the paper

procedure processNeighborWeight(~nProc, invs, ~hecke,
				idx, H :
				BeCareful := false,
				UseLLL := false,
				weight := 1,
				special := false)
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
			      special := special, BeCareful := BeCareful);

	// If isometric, flag as found,
	//  increment Hecke matrix, and move on.
	if iso then
	    space_idx := array[j][2];
	    
	    if GetVerbose("AlgebraicModularForms") ge 2 then
		printf "Neighbor is isometric to genus %o.\n", space_idx;
	    end if;
	    
	    // calculating gamma_i_j, for i = idx, j the index of the
	    // p-neighbor (nLat), and j* = space_idx
	    /*
	    g_pulled := Transpose(PullUp(Matrix(g), nLat, array[j][1] :
			   BeCareful := BeCareful));
	    */
	    // gg := W`G!ChangeRing(g_pulled, BaseRing(W`G));
	    gg := W`G!ChangeRing(Transpose(g), BaseRing(W`G));

	    if GetVerbose("AlgebraicModularForms") ge 2 then
		print "Updating the Hecke operator...";
	    end if;
	    
	    found := true;
	    iota := H[space_idx]`embedding;
	    for vec_idx in [1..Dimension(H[space_idx])] do
	    	vec := gg * (iota(H[space_idx].vec_idx));
		hecke[space_idx][vec_idx][idx] +:= weight * vec;
	    end for;
	    break;
	end if;
    end for;

    // Verify that the neighbor was indeed isometric
    //  to something in our list.
    assert found;
  
    // Update nProc in preparation for the next neighbor
    //  lattice.
    nProc := GetNextNeighbor(nProc
			     : BeCareful := BeCareful);
end procedure;

function HeckeOperatorCN1(M, pR, k
			  : BeCareful := false,
			    UseLLL := false,
			    Estimate := false,
			    Orbits := false)
    
    // The genus representatives.
    reps := Representatives(Genus(M));

    hecke := [ [ [* M`W!0 : hh in M`H*] : vec_idx in [1..Dimension(h)]] :
	       h in M`H];

    // Keeping track of the gamma_i_j
    //  isom := [ [[] : h1 in H] : h2 in H ];

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
	
	if Orbits then
	    // The affine vector space.
	    V := nProc`L`Vpp[pR]`V;

	    // The base field.
	    F := BaseRing(V);

	    // The automorphism group restricted to the affine space.
	    G := AutomorphismGroup(L);

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

	    B := Transpose(V`Basis);
	    
	    for orbit in isoOrbits do
		// Skip to the neighbor associated to this orbit.
		nProc := SkipToNeighbor(nProc, Basis(orbit[1]));

		mat_gen_seq := [[
		    gens[Index(gens_modp, Eltseq(Aut.Abs(i)))]^Sign(i) :
				       i in Eltseq(g@@psi)] :
				g in orbit[2]];
		mat_lifts := [IsEmpty(seq) select GL(n,BaseRing(Q))!1 else
			      &*seq : seq in mat_gen_seq];

		w := &+[Matrix(getMatrixAction(M`W, Transpose(M`W`G!g))) :
			g in mat_lifts];
		
		processNeighborWeight(~nProc, invs, ~hecke, idx, M`H:
				      BeCareful := BeCareful,
				      UseLLL := UseLLL,
				      weight := w,
				      special := IsSpecialOrthogonal(M));
		if Estimate then
		    printEstimate(start, ~count, ~elapsed,
				  fullCount, pR, k :
				  increment := #orbit[2]);
		end if;
	    end for;
	else
	    while nProc`isoSubspace ne [] do
		processNeighborWeight(~nProc, invs, ~hecke, idx, M`H :
				      BeCareful := BeCareful,
				      UseLLL := UseLLL,
				      special := IsSpecialOrthogonal(M));
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
				      weight := [],
				      special := false)
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
			  special := special, BeCareful := BeCareful);
    
    if not iso then return; end if;

    iota := H[space_idx]`embedding;
    W := Codomain(iota);

    w := &+[Matrix(getMatrixAction(W, Transpose(W`G!g))) : g in weight];
   	    
    gg := W`G!ChangeRing(Transpose(g), BaseRing(W`G));

    if GetVerbose("AlgebraicModularForms") ge 2 then
	print "Updating the Hecke operator...";
    end if;
	   
    vec := gg * (iota(H[space_idx].vec_idx));
    hecke[idx] +:= w * vec;

end procedure;

// compute T_p(e_{i,j}) where i = space_idx, j = vec_idx
function HeckeOperatorCN1SparseBasis(M, pR, k, /* space_idx, vec_idx */ idx
				     : BeCareful := false,
				       UseLLL := false,
				       Estimate := false,
				       Orbits := false)
/*
    if space_idx gt #M`H then
	error "space_idx should be in the range [1..%o]", #M`H;
    end if;
    if vec_idx gt Dimension(M`H[space_idx]) then
	error "vec_idx should be in the range [1..%o]",
	      Dimension(M`H[space_idx]);
    end if;
*/
    assert 1 le idx and idx le Dimension(M);
    // The genus representatives.
    reps := Representatives(Genus(M));
    
    //    hecke := [* M`W!0 : hh in M`H *];
    hecke := [ [ [M`W!0] : vec_idx in [1..Dimension(h)]] : h in M`H];

    // Keeping track of the gamma_i_j
    //  isom := [ [[] : h1 in H] : h2 in H ];
    // TODO  : the invariant was already computed can use it
    // inv := <Invariant(reps[space_idx]), reps[space_idx]>;
    invs := M`genus`RepresentativesAssoc;

    Q := ReflexiveSpace(Module(M));
    n := Dimension(Q);

    fullCount := NumberOfNeighbors(M, pR, k);
    count := 0;
    elapsed := 0;
    start := Realtime();
	
    // for idx in [1..#M`H] do
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
	G := AutomorphismGroup(L);

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
	    // Skip to the neighbor associated to this orbit.
	    nProc := SkipToNeighbor(nProc, Basis(orbit[1]));
	    mat_gen_seq := [[
				   gens[Index(gens_modp,
					      Eltseq(Aut.Abs(i)))]^Sign(i) :
				   i in Eltseq(g@@psi)] :
			    g in orbit[2]];
	    mat_lifts := [IsEmpty(seq) select GL(n,BaseRing(Q))!1 else
			  &*seq : seq in mat_gen_seq];
	    
	    w := &+[Matrix(getMatrixAction(M`W, Transpose(M`W`G!g))) :
			g in mat_lifts];
	    /*
	      processNeighborWeightSparse(~nProc, inv, ~hecke, idx, M`H,
	      space_idx, vec_idx:
	      BeCareful := BeCareful,
	      UseLLL := UseLLL,
	      weight := mat_lifts,
	      special := IsSpecialOrthogonal(M));
	   */
	    processNeighborWeight(~nProc, invs, ~hecke, idx, M`H:
				  BeCareful := BeCareful,
				  UseLLL := UseLLL,
				  weight := w,
				  special := IsSpecialOrthogonal(M));
	    if Estimate then
		printEstimate(start, ~count, ~elapsed,
			      fullCount, pR, k :
			      increment := #orbit[2]);
	    end if;
	end for;
    else
	while nProc`isoSubspace ne [] do
	    processNeighborWeight(~nProc, invs, ~hecke, idx, M`H :
				  BeCareful := BeCareful,
				  UseLLL := UseLLL,
				  special := IsSpecialOrthogonal(M));
	    // Update nProc in preparation for the next neighbor
	    //  lattice.
	    nProc := GetNextNeighbor(nProc
				     : BeCareful := BeCareful);
	    if Estimate then
		printEstimate(start, ~count, ~elapsed,
			      fullCount, pR, k);
	    end if;
	end while;
    end if;
//    end for;
/*
    iota := [h`embedding : h in M`H];
   
    vec := &cat[Eltseq(hecke[i]@@iota[i]) : i in [1..#M`H]];

    empty_vec := VectorSpace(BaseRing(M`H[1]),0)![];
    
    if IsEmpty(vec) then return empty_vec; end if;
    
    return Vector(vec);
*/
    iota := M`H[idx]`embedding;
   
    mats := [[[Eltseq(hecke[space_idx][vec_idx][1]@@iota) :
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
				  UseLLL := true,
				  Estimate := true,
				  Orbits := true)
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
					       Orbits := Orbits);
	ret[space_idx] +:= hecke;
    end for;
    return ret;
end function;
/* 
old code:

procedure processNeighbor(~nProc, invs, ~hecke, idx :
			  BeCareful := true, UseLLL := false, weight := 1)
    // Build the neighbor lattice corresponding to the
    //  current state of nProc.
    nLat := BuildNeighbor(nProc : BeCareful := BeCareful, UseLLL := UseLLL);

    // Compute the invariant of the neighbor lattice.
    inv := Invariant(nLat);

    // Retrieve the array of isometry classes matching this
    //  invariant.
    array := invs[inv];

    // Isometry testing is only necessary if the array has
    //  length larger than 1.
    if #array ne 1 then
	// Flag to determine whether an isometry class
	//  was actually found. This is a failsafe.
	found := false;
	
	for j in [1..#array] do
	    // Check for isometry.
	    iso := IsIsometric(nLat, array[j][1]);
	    
	    // If isometric, flag as found,
	    //  increment Hecke matrix, and move on.
	    if iso then
		found := true;
		hecke[array[j][2]][idx] +:= weight;
		continue;
	    end if;
	end for;

	// Verify that the neighbor was indeed isometric
	//  to something in our list.
	assert found;
    else
	// Array length is one, and therefore conclude
	//  that nLat is isometric to the only entry in
	//  the array.
	hecke[array[1][2]][idx] +:= weight;
    end if;
    
    // Update nProc in preparation for the next neighbor
    //  lattice.
    nProc := GetNextNeighbor(nProc
			     : BeCareful := BeCareful);
end procedure;


function HeckeOperatorTrivialWeightCN1(M, pR, k
				       : BeCareful := true,
					 UseLLL := false,
				         Estimate := false,
				         Orbits := false)
	// The genus representatives.
	reps := Representatives(Genus(M));

	// The dimension of the Hecke matrix.
	dim := #reps;

	// Initialize the Hecke matrix.
	hecke := Zero(MatrixRing(Integers(), dim));

	// An associative array indexed by a specified invariant of an isometry
	//  class. This data structure allows us to bypass a number of isometry
	//  tests by filtering out those isometry classes whose invariant
	//  differs from the one specified.
	invs := M`genus`RepresentativesAssoc;

	Q := ReflexiveSpace(Module(M));
	n := Dimension(Q);

	fullCount := dim * NumberOfNeighbors(M, pR, k);
	count := 0;
	elapsed := 0;
	start := Realtime();
	
	for idx in [1..dim] do
		// The current isometry class under consideration.
		L := reps[idx];

		// Build neighboring procedure for this lattice.
		nProc := BuildNeighborProc(L, pR, k
					   : BeCareful := BeCareful);

		if GetVerbose("AlgebraicModularForms") ge 1 then
		    printf "Computing %o%o-neighbors for isometry class "
			cat "representiative #%o...\n", pR,
			   k eq 1 select "" else "^" cat IntegerToString(k),
			   idx;
		end if;

		if Orbits then
		    // The affine vector space.
		    V := nProc`L`Vpp[pR]`V;

		    // The base field.
		    F := BaseRing(V);

		    // The automorphism group restricted to the affine space.
		    G := AutomorphismGroup(L);

		    gens := [PullUp(Matrix(g), L, L :
				    BeCareful := BeCareful) :
			     g in Generators(G)];

		    pMaximalBasis :=
			ChangeRing(L`pMaximal[nProc`pR][2], BaseRing(Q));

		    gens := [pMaximalBasis * g * pMaximalBasis^(-1) :
			     g in gens];

		    gens_modp := [[L`Vpp[pR]`proj_pR(x) : x in Eltseq(g)]
				  : g in gens];
		 
		    Aut := sub<GL(n, F) | gens_modp>;

		    // The isotropic orbit data.
		    isoOrbits := IsotropicOrbits(V, Aut, k);

		    for orbit in isoOrbits do
			// Skip to the neighbor associated to this orbit.
			nProc := SkipToNeighbor(nProc, Basis(orbit[1]));
			processNeighbor(~nProc, invs, ~hecke, idx :
					BeCareful := BeCareful,
					UseLLL := UseLLL,
					weight := orbit[2]);
			// !!! TODO : Estimate by the total number of orbits
			if Estimate then
			    printEstimate(start, ~count, ~elapsed,
					  fullCount, pR, k
					 : increment := orbit[2]);
			end if;
		    end for;
		else
		    while nProc`isoSubspace ne [] do
			processNeighbor(~nProc, invs, ~hecke, idx :
					BeCareful := BeCareful,
					UseLLL := UseLLL);
			
			if Estimate then
			    printEstimate(start, ~count, ~elapsed,
					  fullCount, pR, k);
			end if;
		    end while;
		end if;
	end for;

	return hecke;
end function;

procedure processNeighborDebug(~nProc, invs, ~iso_classes :
			  BeCareful := true)
    // Build the neighbor lattice corresponding to the
    //  current state of nProc.
    nLat := BuildNeighbor(nProc : BeCareful := BeCareful);

    // Compute the invariant of the neighbor lattice.
    inv := Invariant(nLat);

    // Retrieve the array of isometry classes matching this
    //  invariant.
    array := invs[inv];

    // Isometry testing is only necessary if the array has
    //  length larger than 1.
    if #array ne 1 then
	// Flag to determine whether an isometry class
	//  was actually found. This is a failsafe.
	found := false;
	
	for j in [1..#array] do
	    // Check for isometry.
	    iso := IsIsometric(nLat, array[j][1]);
	    
	    // If isometric, flag as found,
 	    //  increment Hecke matrix, and move on.
	    if iso then
		found := true;
		iso_classes[nProc`isoSubspace] :=  array[j][2];
		continue;
	    end if;
	end for;

	// Verify that the neighbor was indeed isometric
	//  to something in our list.
	assert found;
    else
	// Array length is one, and therefore conclude
	//  that nLat is isometric to the only entry in
	//  the array.
	iso_classes[nProc`isoSubspace] := array[1][2];
    end if;
    
    // Update nProc in preparation for the next neighbor
    //  lattice.
    nProc := GetNextNeighbor(nProc
			     : BeCareful := BeCareful);
end procedure;


*/

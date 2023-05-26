freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J. Voight
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

import "../lattice/minkowski.m" : generate_orbit; 
import "../utils/helper.m" : printEstimate;

import "neighbor-CN1.m" : SkipToNeighbor;
import "orbits.m" : build_polycyclic_data, orb_stab_pc, orb_stab_general;

// This function is the atomic operation on a single neighbor
// It test the neighbor for isometry with the members of the genus
// and if so, adds the appropriate weight multiple to the
// matrix of the Hecke operator in the correct place.
procedure processNeighborWeight(~nProc, ~reps, ~invs, ~hecke, idx, ~H_source, H_target :
				 BeCareful := false,
				 UseLLL := false,
				 Weight := 1,
				 Special := false,
				 ComputeGenus := false,
				 ThetaPrec := 25,
				 Perestroika := false,
				 BuildNeighbor := BuildNeighbor,
				 Similarity := 1)
  // Build the neighbor lattice corresponding to the
  //  current state of nProc.
  nLat := BuildNeighbor(nProc : BeCareful := BeCareful,
			UseLLL := UseLLL,
			Perestroika := Perestroika, Similarity := Similarity);

  if Perestroika then
    isom_scale := BasisMatrix(Module(nLat));
    Vpp := nProc`L`Vpp[nProc`pR];
    pi := Vpp`pElt;
    nLat := ScaledLattice(nLat, 1/pi);
  end if;

  if (Type(Similarity) ne RngIntElt) then
      isom_scale := BasisMatrix(Module(nLat));
      Q := ReflexiveSpace(reps[1]);
      nLat := LatticeWithBasis(Q,ChangeRing(isom_scale,BaseRing(Q))*Similarity);
  end if;

  if GetVerbose("AlgebraicModularForms") ge 2 then
    printf "Processing neighbor corresponding to isotropic subspace ";
    printf "indexed by %o.\n", nProc`isoSubspace;
    if GetVerbose("AlgebraicModularForms") ge 3 then
      printf "Lattice is %o\n", nLat;
    end if;
  end if;

  // Compute the invariant of the neighbor lattice.
  if ThetaPrec eq -1 then
    inv := GreedyReduce(nLat);
  elif ThetaPrec eq -2 then
      inv := GreedyReduce2(nLat);
  elif ThetaPrec eq 0 then
      inv := Invariant(nLat : Precision := AbsolutePrecision(Random(Keys(invs)))-1);
  else
      inv := Invariant(nLat : Precision := ThetaPrec);
  end if;

  // Retrieve the array of isometry classes matching this invariant.
  if not IsDefined(invs, inv) then
    assert ComputeGenus;
    invs[inv] := [];
  end if;
  array := invs[inv];

  // Flag to determine whether an isometry class
  //  was actually found. This is a failsafe.
  found := false;

  iota_target := H_target[idx]`embedding;
    
  W_target := Codomain(iota_target);

  W_source := Codomain(H_source[1]`embedding);
  
  // If the weight is trivial, we don't need the isometry
  // If moreover, there is only one lattice with the invariant,
  // we can assume this is the neighbor it is isometric to.
  if (not ComputeGenus) and IsTrivial(W_target) and #array eq 1 then
    space_idx := array[1][2];
	    
    if GetVerbose("AlgebraicModularForms") ge 2 then
      printf "Neighbor is isometric to genus %o.\n", space_idx;
      print "Updating the Hecke operator...";
    end if;
	    
    found := true;
    iota_source := H_source[space_idx]`embedding;
    W_source := Codomain(iota_source);
    for vec_idx in [1..Dimension(H_source[space_idx])] do
	vec := iota_source(H_source[space_idx].vec_idx);
	vec := W_target!Eltseq(vec);
	hecke[space_idx][vec_idx][idx] +:= Weight * vec;
    end for;
  else
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

        if Perestroika then
          g := g * ChangeRing(isom_scale, BaseRing(g));
        end if;
	
	if (Type(Similarity) ne RngIntElt) then
	    g := Similarity * g * Similarity^(-1);
	end if;
	
        gg := W_target`G!ChangeRing(Transpose(g), BaseRing(W_target`G));

        if GetVerbose("AlgebraicModularForms") ge 2 then
	  print "Updating the Hecke operator...";
        end if;
	    
        found := true;
	iota_source := H_source[space_idx]`embedding;
	W_source := Codomain(iota_source);
	for vec_idx in [1..Dimension(H_source[space_idx])] do
	    vec := iota_source(H_source[space_idx].vec_idx);
	    vec := W_target!Eltseq(vec);
            if not IsTrivial(W_target) then
		vec := gg * vec;
            end if;
	    hecke[space_idx][vec_idx][idx] +:= Weight * vec;
	end for;
	break;
      end if;
    end for;
  end if;

  if not found then
    assert ComputeGenus; // should not happen if we computed the genus already
    Append(~reps, nLat);
    Append(~invs[inv], <nLat, #reps>);
    
    gamma := AutomorphismGroupOverField(nLat, W_source`G : Special := Special);
    h := FixedSubspace(gamma, W_source);
    for h_idx in [1..#H_target] do
      for v_idx in [1..Dimension(H_target[h_idx])] do
	Append(~hecke[h_idx][v_idx], W_target!0);
      end for;
    end for;

    Append(~H_source, h);
    if (H_source eq H_target) then
	Append(~hecke, [ [* W_target!0 : hh in H_source *] : i in [1..Dimension(h)]]);
    end if;

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

function createInvsWithPrecision(M, ThetaPrec)
  invs_orig := M`genus`RepresentativesAssoc;
  _<x> := Universe(Keys(invs_orig));
  invs := AssociativeArray();
  for inv in Keys(invs_orig) do
    inv_new := inv + O(x^(ThetaPrec+1));
    if not IsDefined(invs, inv_new) then
      invs[inv_new] := [];
    end if;
    invs[inv_new] cat:= invs_orig[inv];
  end for;
  return invs;
end function;

function createReducedInvs(reps)
  ZZq<q> := PuiseuxSeriesRing(Integers());
  invs := AssociativeArray(ZZq);
  for i in [1..#reps] do
    r := reps[i];
    red := GreedyReduce(r);
    if not IsDefined(invs, red) then
      invs[red] := [];
    end if;
    Append(~invs[red], <r, i>);
  end for;
  return invs;
end function;

function createReducedInvs2(reps)
  ZZq<q> := PuiseuxSeriesRing(Integers());
  invs := AssociativeArray(ZZq);
  for i in [1..#reps] do
    r := reps[i];
    reds := generate_orbit(GreedyReduce2(r));
    for red in reds do
      if not IsDefined(invs, red) then
        invs[red] := [];
      end if;
      Append(~invs[red], <r, i>);
    end for;
  end for;
  return invs;
end function;

// This procedure updates the matrix of the Hecke operator at
// column idx.
procedure HeckeOperatorCN1Update(~reps, idx, pR, k, M, ~hecke, ~invs,
				 start, ~count, ~elapsed, fullCount :
				 BeCareful := false,
				 Orbits := true,
				 UseLLL := false,
				 Estimate := true,
				 ComputeGenus := false,
				 LowMemory := false,
				 ThetaPrec := 25)
    L := reps[idx];

    Q := ReflexiveSpace(Module(M));
    n := Dimension(Q);

    kk := k ne 0 select k else n div 2;
    Perestroika := k eq 0;
    // Build neighboring procedure for this lattice.
    nProc := NeighborProcess(L, pR, kk : Perestroika := Perestroika);

    if GetVerbose("AlgebraicModularForms") ge 1 then
	printf "Computing %o%o-neighbors for isometry class "
	       cat "representative #%o...\n", pR,
	       k eq 1 select "" else "^" cat IntegerToString(k),
	       idx;
    end if;
    RR := RealField(10);
    nbr_tm := RR!0;
    if Orbits then
	// The affine vector space.
	V := nProc`L`Vpp[pR]`V;
	
	// The base field.
	F := BaseRing(V);
	
	// The automorphism group restricted to the affine space.
	G := AutomorphismGroupOverField(L, M`W`G : Special := IsSpecialOrthogonal(M));
	gens := [Transpose(Matrix(g)) : g in Generators(G)];
	
	pMaximalBasis :=
	    ChangeRing(L`pMaximal[nProc`pR][2], BaseRing(Q));
	
	conj_gens := [pMaximalBasis * g * pMaximalBasis^(-1) :
		      g in gens];
        G_conj := sub<GL(n,BaseRing(Q)) | conj_gens>;

	if LowMemory then
	  proj := L`Vpp[pR]`proj_pR;
          R := Domain(proj);
          is_solvable, G_pc, f_pc, red := build_polycyclic_data(G_conj, V, proj);
          orb_stab := is_solvable select orb_stab_pc else orb_stab_general;
          orb_reps := [];
          y := nProc`isoSubspace;
          skew0 := Zero(MatrixRing(F, kk));
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
              if IsTrivial(M`W) then
                w := #orb;
              else
	        coset_reps_pc := Transversal(G_pc, stab);
                coset_reps_conj := [g@@red : g in coset_reps_pc];
                coset_reps := [pMaximalBasis^(-1)*
			       ChangeRing(g, BaseRing(Q))*pMaximalBasis
				  : g in coset_reps_conj];
                w := &+[Matrix(getMatrixAction(M`W, Transpose(M`W`G!g)))
		   : g in coset_reps];
              end if;
              // Skip to the neighbor associated to this orbit.
              SkipToNeighbor(~nProc, y, skew0);
              // Changing the skew matrix, but not the isotropic
              // subspace mod p
              repeat
                processNeighborWeight(~nProc, ~reps, ~invs, ~hecke, idx, ~M`H, M`H:
					  BeCareful := BeCareful,
					  UseLLL := UseLLL,
					  Weight := w,
				          Special := IsSpecialOrthogonal(M),
				      ThetaPrec := ThetaPrec,
				      ComputeGenus := ComputeGenus,
				      Perestroika := Perestroika);
                // Update nProc in preparation for the next neighbor
                //  lattice.
	        NextNeighbor(~nProc);
                if Estimate then
	          printEstimate(start, ~count, ~elapsed,
			  fullCount, Sprintf("T_%o^%o", Norm(pR), kk)
			  : increment := #orb);
	        end if;
              until (nProc`skewDim eq 0) or (nProc`skew eq skew0);
            else
              NextNeighbor(~nProc);
            end if;
            y := nProc`isoSubspace;
          end while;
	else
	  // The isotropic orbit data.
          tm := Realtime();
          proj := map< G_conj -> GL(n,F) |
	    g :-> [L`Vpp[pR]`proj_pR(x) : x in Eltseq(g)]>;

          isoOrbits := IsotropicOrbits(V, G_conj, kk,
				       proj : Estimate := Estimate);
          // The constant per neighbor is really small, so we need more precision
          tm := ChangePrecision(Realtime() - tm, 10);
          nNbrs := NumberOfNeighbors(M, pR, kk);
	  if nNbrs ne 0 then
              vprintf AlgebraicModularForms, 1 :
		  "IsotropicOrbits took %o sec, found %o orbits. Time per neighbor is %o sec.\n", tm, #isoOrbits, tm / nNbrs;
	  end if;
          loopCount := fullCount - nNbrs + #isoOrbits * #F^nProc`skewDim;
          orb_start := Realtime();
	  for orbit in isoOrbits do
	    skew0 := Zero(MatrixRing(F, kk));
	    // Skip to the neighbor associated to this orbit.
            tm := Realtime();
	    SkipToNeighbor(~nProc, Basis(orbit[1]), skew0);
            nbr_tm +:= Realtime() - tm;
	    // In case it doesn't lift
	    if IsEmpty(nProc`X) then
		continue;
	    end if;
            if IsTrivial(M`W) then
	      w := #orbit[2];
            else
	      mat_lifts := [pMaximalBasis^(-1)*g*pMaximalBasis : g in orbit[2]];

	      w := &+[Matrix(getMatrixAction(M`W, Transpose(M`W`G!g))) :
		      g in mat_lifts];
            end if;
	    // Changing the skew matrix, but not the isotropic
	    // subspace mod p
	    repeat
	        tm := Realtime();
                processNeighborWeight(~nProc, ~reps, ~invs, ~hecke, idx, ~M`H, M`H:
				      BeCareful := BeCareful,
				      UseLLL := UseLLL,
				      Weight := w,
				      Special := IsSpecialOrthogonal(M),
				      ThetaPrec := ThetaPrec,
				      ComputeGenus := ComputeGenus,
				      Perestroika := Perestroika);
		// Update nProc in preparation for the next neighbor
		//  lattice.
		NextNeighbor(~nProc);
                nbr_tm +:= Realtime() - tm;
		if Estimate then
		  if IsTrivial(M`W) then
		    printEstimate(orb_start, ~count, ~elapsed, loopCount,
				  Sprintf("T_%o^%o", Norm(pR), kk));
		  else
		    printEstimate(orb_start, ~count, ~elapsed,
				  fullCount, Sprintf("T_%o^%o", Norm(pR), kk) :
				  increment := #orbit[2]);
                  end if;
		end if;
	    until (nProc`skewDim eq 0) or (nProc`skew eq skew0);
	end for;
      end if;
    else
	while nProc`isoSubspace ne [] do
	    processNeighborWeight(~nProc, ~reps, ~invs, ~hecke, idx, M`H, ~M`H :
				  BeCareful := BeCareful,
				  UseLLL := UseLLL,
				  Special := IsSpecialOrthogonal(M),
				  ComputeGenus := ComputeGenus,
				  ThetaPrec := ThetaPrec,
				  Perestroika := Perestroika);
	    // Update nProc in preparation for the next neighbor
	    //  lattice.
	    NextNeighbor(~nProc : BeCareful := BeCareful);
	    if Estimate then
		printEstimate(start, ~count, ~elapsed,
			      fullCount, Sprintf("T_%o^%o", Norm(pR), kk));
	    end if;
	end while;
    end if;
   
    vprintf AlgebraicModularForms, 1 :
      "time spent on neighbors is %o sec.\n", nbr_tm;
    if Orbits and not LowMemory and #isoOrbits gt 0 then
      vprintf AlgebraicModularForms, 1 :
       "time spent per orbit is %o sec.\n", nbr_tm / #isoOrbits;
    elif fullCount gt 0 then 
      vprintf AlgebraicModularForms, 1 :
       "time spent per neighbor is %o sec.\n", nbr_tm / fullCount;
    end if;
end procedure;

function finalizeHecke(M_source, M_target, hecke, idxs)
  iota := [h`embedding : h in M_target`H];

  mats := [[[Eltseq(hecke[space_idx][vec_idx][idx]@@iota[idx]) :
		    vec_idx in [1..Dimension(M_source`H[space_idx])]] :
           space_idx in [1..#M_source`H]] : idx in idxs];

  vert_blocks := [&cat mat : mat in mats];

  empty_operator := MatrixAlgebra(BaseRing(M_source),0)![];
    
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

forward fillHeckeFromRelations;

function HeckeOperatorCN1(M, pR, k
			  : BeCareful := false,
			    UseLLL := false,
			    Estimate := true,
			    Orbits := true,
			    ComputeGenus := false,
			    LowMemory := false,
			    ThetaPrec := 25,
			    AutoFill := false)
    if ComputeGenus then
      L := Module(M);
      reps := [L];
      ZZq<q> := PuiseuxSeriesRing(Integers());
      invs := AssociativeArray(ZZq);
      invs[Invariant(L : Precision := ThetaPrec)] := [<L, 1>];
      gamma := AutomorphismGroupOverField(L, M`W`G : Special := IsSpecialOrthogonal(M));
      M`H := [FixedSubspace(gamma, M`W)];
    else
      // The genus representatives.
      reps := Representatives(Genus(M));

      //  An associative array indexed by a specified invariant of an isometry
      //  class. This data structure allows us to bypass a number of isometry
      //  tests by filtering out those isometry classes whose invariant
      //  differs from the one specified.
      // invs := M`genus`RepresentativesAssoc;
      invs := HeckeInitializeInvs(M, ThetaPrec);
    end if;

    hecke := [ [ [* M`W!0 : hh in M`H *] : vec_idx in [1..Dimension(h)]]
		 : h in M`H];

    Q := ReflexiveSpace(Module(M));
    n := Dimension(Q);

    kk := k ne 0 select k else n div 2;
    fullCount := #M`H * NumberOfNeighbors(M, pR, kk);
    count := 0;
    elapsed := 0;
    start := Realtime();

    idx := 1;
    other_hecke_computed := (#HeckeOperators(M) gt 0);
    is_filled := false;
    // max_idx := (#HeckeOperators(M) gt 0) select 1 else #M`H;
    while (idx le #M`H) do
    //while (idx le max_idx) do
        HeckeOperatorCN1Update(~reps, idx, pR, k, M, ~hecke, ~invs,
			       start, ~count, ~elapsed, fullCount :
			       BeCareful := BeCareful,
			       Orbits := Orbits,
			       UseLLL := UseLLL,
			       Estimate := Estimate,
			       ComputeGenus := ComputeGenus,
			       LowMemory := LowMemory,
			       ThetaPrec := ThetaPrec);
        if AutoFill and (other_hecke_computed) and (idx lt #M`H) then
            tmp := finalizeHecke(M, M, hecke, [1..#M`H]);
            column := Transpose(tmp);
            indices := [1..idx];
            is_filled, ret := fillHeckeFromRelations(M, column, indices, idx);
            if (is_filled) then
                break;
            end if;
        end if;
        idx +:= 1;
    end while;

    if ComputeGenus then
      // update genus
      M`genus := New(GenusSym);
      M`genus`Representative := M`L;
      M`genus`Representatives := reps;
      M`genus`RepresentativesAssoc := invs;
    end if;

    if (not is_filled) then
        ret := finalizeHecke(M, M, hecke, [1..#M`H]);
    end if;

    return ret;
end function;

// compute T_p(e_{i,j}) where i = space_idx, j = vec_idx
function HeckeOperatorCN1SparseBasis(M, pR, k, idx, invs
				     : BeCareful := false,
				       UseLLL := false,
				       Estimate := true,
				       Orbits := true,
				       LowMemory := false,
				       ThetaPrec := 25)

    assert 1 le idx and idx le #M`H;
    // The genus representatives.
    reps := Representatives(Genus(M));
    
    hecke := [ [ [* M`W!0 : hh in M`H*] : vec_idx in [1..Dimension(h)]] :
	       h in M`H];

    

    Q := ReflexiveSpace(Module(M));
    n := Dimension(Q);

    kk := k ne 0 select k else n div 2;
    fullCount := NumberOfNeighbors(M, pR, kk);
    count := 0;
    elapsed := 0;
    start := Realtime();

    HeckeOperatorCN1Update(~reps, idx, pR, k, M, ~hecke, ~invs,
			     start, ~count, ~elapsed, fullCount :
			     BeCareful := BeCareful,
			     Orbits := Orbits,
			     UseLLL := UseLLL,
			     Estimate := Estimate,
			     LowMemory := LowMemory,
			     ThetaPrec := ThetaPrec);
   
    return finalizeHecke(M, M, hecke, [idx]);
end function;

function HeckeOperatorCN1Sparse(M, pR, k, s, invs
				: BeCareful := false,
				  UseLLL := false,
				  Estimate := true,
				  Orbits := true,
				  LowMemory := false,
				  ThetaPrec := 25)
    
    ret := [* KMatrixSpace(BaseRing(M`H[1]),Dimension(M),Dimension(h))!0 :
	    h in M`H *];
    for tup in s do
	scalar := tup[1];
	space_idx := tup[2];
       
	hecke := scalar *
	  HeckeOperatorCN1SparseBasis(M, pR, k, space_idx, invs
					     : BeCareful := BeCareful,
					       UseLLL := UseLLL,
					       Estimate := Estimate,
					       Orbits := Orbits,
					       LowMemory := LowMemory,
					       ThetaPrec := ThetaPrec);
	ret[space_idx] +:= hecke;
    end for;
    return ret;
end function;

forward get_best_prec;

intrinsic HeckeInitializeInvs(M::ModFrmAlg, ThetaPrec::RngIntElt) -> Assoc
{.}
  if ThetaPrec eq -1 then
    invs := createReducedInvs(Representatives(Genus(M)));
  elif ThetaPrec eq -2 then
      invs := createReducedInvs2(Representatives(Genus(M)));
  elif ThetaPrec eq 0 then
      prec := get_best_prec(Representatives(Genus(M)));
      invs := createInvsWithPrecision(M, prec);
  else
    invs := createInvsWithPrecision(M, ThetaPrec);
  end if;
  return invs;
end intrinsic;

function getIndices(M, dim)
    // Retrieve the Hecke eigenforms for this space.
    fs := HeckeEigenforms(M);

    // Prioritize the isometry class indices which allow us to reconstruct
    //  the Hecke matrix from a single list of neighbors.
    good := [ i : i in [1..dim]
        | &*[ Eltseq(f`vec)[i] eq 0 select 0 else 1 : f in fs ] eq 1 ];

    // Return a full list of indices in the order we will compute.
    return good cat [ i : i in [1..dim] | not i in good ];
end function;

// The involution alpha induces a permutation on the
// genus representatives, which is an ingredient in computing the
// invariant unitary form
// !! TODO !! - This could be just called once, remembering the information
function alpha_permutation(M)
    V := ReflexiveSpace(Module(M));
    alpha := Involution(V);
    F := BaseField(alpha);
    reps := Representatives(Genus(M));
    perm := [];
    for lat in reps do
	pb := PseudoBasis(lat);
	idls := [b[1] : b in pb];
	vecs := [b[2] : b in pb];
	alpha_idls := [alpha(x) : x in idls];
	alpha_vecs := [alpha(Vector(F,v)) : v in vecs];
	if Type(F) eq FldRat then
	    alpha_lat := LatticeWithBasis(V, Matrix(alpha_vecs));
	else
	    alpha_pmat := PseudoMatrix(alpha_idls, Matrix(alpha_vecs));
	    alpha_lat := LatticeWithPseudobasis(V, alpha_pmat);
	end if;
	// !! TODO !! use invariants to make thi faster.
	// can also use the fact that this is order 2 to do half the work
	for idx in [1..#reps] do
	    lat_prime := reps[idx];
	    if IsIsometric(lat_prime, alpha_lat) then
		Append(~perm, idx);
		break;
	    end if;
	end for;
    end for;
    return perm;
end function;

function fillHeckeFromRelations(M, column, indices, ind)
    // We will now recover the entire Hecke operator from the data
    //  we just computed by using some tricks involving the
    //  structure of the Hecke operators as well as some linear
    //  algebra.
    vprintf AlgebraicModularForms, 2 :
        "Attempting to build Hecke matrix (attempt #%o)...\n", ind;

    dim := Dimension(M);

    // The number of initial free variables.
    freevars := Binomial(dim - ind + 1, 2) - (dim - ind);

    // The sizes of the automorphism groups.
    /*
    aut := [ #AutomorphismGroup(L : Special := IsSpecialOrthogonal(M))
	     : L in M`genus`Representatives ];
   */
    aut := [ #AutomorphismGroupOverField(L, M`W`G : Special := IsSpecialOrthogonal(M))
	     : L in M`genus`Representatives ];

    // spreading them according to the spaces
    // !! TODO !! - Is this the correct thing to do?
    // Is it the natural unitary form?
    aut := &cat[[aut[i] : j in [1..Dimension(M`H[i])]] : i in [1..#M`H]];

    perm := alpha_permutation(M);

    h_dims := [Dimension(h) : h in M`H];
    space_idxs := [&+h_dims[1..i] : i in [0..#M`H-1]];
    perm := &cat[[space_idxs[perm[i]]+j : j in [1..Dimension(M`H[i])]] : i in [1..#M`H]];
    
    // add free variables in nonzero characteristic
    for j in [1..dim] do
        for i in [1..dim] do
            denom := BaseRing(Weight(M))!Denominator(aut[i]/aut[j]);
            if (denom eq 0) and (perm[i] notin indices[1..ind]) then
                freevars +:= 1;
            end if;
        end for;
    end for;

    // The polynomial ring under consideration.
    Z := PolynomialRing(BaseRing(Weight(M)), freevars);

    // We now construct the entire Hecke operator from the first
    //  column.
    hecke := Zero(MatrixRing(Z, dim));

    // Fill in the entries from the values we've already computed.
    kk := 0;
    for j in indices[1..ind] do
        for i in [1..dim] do
            hecke[j,i] := column[j][i];
            denom := BaseRing(Weight(M))!Denominator(aut[i]/aut[j]);
            if (denom ne 0) then
                hecke[perm[i],perm[j]] := aut[i] / aut[j] * column[j][i];
	    elif perm[i] notin indices[1..ind] then
                kk +:= 1;
                hecke[perm[i],perm[j]] := Z.kk;
            end if;
        end for;
    end for;
    
    // Count the number of neighbors computed.
    neighbors := &+Eltseq(column[indices[ind]]);

    // Let's fill out the hecke matrix first.
    for i in [1..dim] do
        // Skip the indices we've already computed.
        if i in indices[1..ind] then continue; end if;

        for j in [i..dim] do
            // Skip the indices we've already computed.
            if (perm[j] in indices[1..ind]) or
	       (j eq perm[i] or perm[j] lt i) then continue; end if;

            kk +:= 1;
            hecke[i,j] := Z.kk;
            denom := BaseRing(Weight(M))!Denominator(aut[j]/aut[i]);
            if (denom ne 0) then
                hecke[perm[j],perm[i]] := aut[j] / aut[i] * Z.kk;
            else
                kk +:= 1;
		hecke[perm[j],perm[i]] := Z.kk;
            end if;
        end for;
    end for;

    // Need to fill in the diagonal entries so that the row sums
    //  match.
    rows := Rows(hecke);
    for i in [1..dim] do
        // Skip the indices we've already computed.
        if i in indices[1..ind] then continue; end if;

        hecke[i,perm[i]] := neighbors - &+Eltseq(rows[i]);
    end for;

    // Now we transpose so that column sums are constant.
    hecke := Transpose(hecke);

    // If the dimension of the Hecke operator is 1 or 2, then we
    //  don't need to do any extra work.
    if dim le 2 then return true, ChangeRing(hecke, BaseRing(Weight(M))); end if;

    list := {};

    // Retrieve Hecke operators that has already been computed.
    // !! TODO : Do we want to limit the number of Hecke operators for efficiency reasons?
    for T_Q in HeckeOperators(M) do
        T := ChangeRing(T_Q, Z);

        // The commutator matrix must be zero, so we end up with
        // additional linear relations that need to be resolved.
        comm := hecke * T - T * hecke;

        // The distinct linear relations.
        list join:= Set([ Normalize(x) : x in Eltseq(comm) | x ne 0 ]);
        
    end for;

    // A list of lists that will be turned into a matrix encoding
    //  the linear relations we seek.
    mat := [];

    for x in list do
        // The list of coefficients of each term.
        c := Coefficients(x);

        // The monomials associated to each coefficient above.
        m := Monomials(x);

        // A sequence of coefficnets.
        coeff := [ BaseRing(Weight(M))!0^^(freevars+1) ];

        // A pointer to the current term we're considering.
        ptr := 1;
        for i in [1..freevars] do
            if ptr le #m and m[ptr] eq Z.i then
                // Update the coefficients and move on.
                coeff[i] := c[ptr];
                ptr +:= 1;
            end if;
        end for;

        // Include the constant coefficient.
        coeff[freevars+1] := -Evaluate(x, [ 0^^freevars ]);

        // Add coefficients to our list.
        Append(~mat, coeff);
    end for;

    if #mat ne 0 then
        // Construct a matrix from the coefficients we extracted
        //  from the relation.
        mat := Matrix(mat);

        // Compute the echelon form of this matrix.
        mat := EchelonForm(mat);

        // Extract the nonzero rows from this matrix.
        mat := Matrix([ row :
            row in Rows(mat) | not IsZero(row) ]);

        if #Rows(mat) eq freevars then
            // print "Success!";
            // The values of the free variables.
            evs := Rows(Transpose(mat))[freevars+1];
            return true, ChangeRing(Evaluate(hecke, Eltseq(evs)),
                BaseRing(Weight(M)));
        else
            return false,_;
        end if;
    end if;

    return false, _;
end function;

// TODO : Document better what's below and move some to isotropic.m

import "isotropic.m" : __initializePivot, __pivots;

intrinsic InitPivots(M::ModFrmAlg, pR::RngInt, k::RngIntElt, hecke_idx::RngIntElt) -> NeighborProc, RngIntElt
{.}
    reps := Representatives(Genus(M));
    L := reps[hecke_idx];
    nProc := NeighborProcess(L, pR, k);
    V := nProc`L`Vpp[nProc`pR]`V;
    if not IsDefined(V`ParamArray, k) then
	data := New(IsoParam);
	data`Pivots := __pivots(Dimension(V) - V`RadDim, V`AnisoDim, k);
	data`PivotPtr := 0;
	data`Params := [];
	V`ParamArray[k] := data;
    end if;
    data := V`ParamArray[k];
    return nProc, #data`Pivots;
end intrinsic;

intrinsic LogNumPivotNbrs(nProc::NeighborProc, pivot_idx::RngIntElt) -> RngIntElt
{.}
    V := nProc`L`Vpp[nProc`pR]`V;
    k := nProc`k;
    // Retrieve the parameters for the requested dimension.
    data := V`ParamArray[k];
    data`PivotPtr := pivot_idx;
    __initializePivot(V, k);
    return #data`FreeVars;
end intrinsic;

procedure update_params(~params, V, nFreeVars)
    // The current position in the parameterization.
    pos := 0;

    // Terminate loop once we found the next new subspace, or we
    //  hit the end of the list.
    repeat
	// Increment position.
	pos +:= 1;
	
	if V`Symbolic then
	    // Increment value.
	    params[pos] +:= 1;
	    
	    // Check to see if we've rolled over.
	    if (params[pos] mod #V`S) eq 0 then
		// Reset value if so.
		params[pos] := 0;
	    end if;
	else
	    // Manually move to the next element.
	    if IsPrime(#BaseRing(V)) then
		params[pos] +:= 1;
	    elif params[pos] eq 0 then
		params[pos] := V`PrimitiveElement;
	    elif params[pos] eq 1 then
		params[pos] := 0;
	    else
		params[pos] *:= V`PrimitiveElement;
	    end if;
	end if;
    until pos eq nFreeVars or params[pos] ne 0;
end procedure;

// not including upTo
intrinsic HeckePivot(M::ModFrmAlg, nProc::NeighborProc, pivot_idx::RngIntElt,
			hecke_idx::RngIntElt, start_idx::RngIntElt, upTo::RngIntElt :
		     BeCareful := false, Estimate := true, ThetaPrec := 25) -> ModMatFldElt
{.}
    invs := HeckeInitializeInvs(M, ThetaPrec);
    hecke := [ [ [* M`W!0 : hh in M`H *] : vec_idx in [1..Dimension(h)]]
	       : h in M`H];
    V := nProc`L`Vpp[nProc`pR]`V;
    k := nProc`k;
    // Retrieve the parameters for the requested dimension.
    data := V`ParamArray[k];
    data`PivotPtr := pivot_idx;
    p := #BaseRing(V);
    log_num_nbrs := LogNumPivotNbrs(nProc, pivot_idx);
    num := start_idx;
    // right now, we only support trivial skew
    for i in [1..log_num_nbrs] do
	data`Params[i] := num mod p;
	num div:= p;
    end for;
    evalList := [* 0 : i in [1..Dimension(V)*k] *];
    for i in [1..#data`Params] do
	evalList[data`FreeVars[i]] := V`S[data`Params[i]+1];
    end for;
    space := Rows(Evaluate(data`IsotropicParam, [ x : x in evalList]));
    skew := nProc`skew;
    // update params, so GetNextNeighbor would work. 
    if #data`FreeVars ne 0 then
	update_params(~data`Params, V, #data`FreeVars);
    end if;

    // If we've hit the end of the list, indicate we need to move on to the
    //  next pivot.
    if &and[ x eq 0 : x in data`Params ] then data`Params := []; end if;
    SkipToNeighbor(~nProc, space, skew);
    fullCount := #BaseRing(V)^(nProc`skewDim) * (upTo-start_idx);
    count := 0;
    elapsed := 0;
    start := Realtime();
 
    for i in [1..fullCount] do
	processNeighborWeight(~nProc, ~reps, ~invs, ~hecke, hecke_idx, ~M`H, M`H :
			      ThetaPrec := ThetaPrec);
	// Update nProc in preparation for the next neighbor
	//  lattice.
	NextNeighbor(~nProc);
	if Estimate then
	    printEstimate(start, ~count, ~elapsed,
			  fullCount, Sprintf("T_%o^%o", Norm(nProc`pR), k));
	end if;
    end for;
 
    return finalizeHecke(M, M, hecke, [hecke_idx]);
end intrinsic;

// Functions for automatic determination of theta precision

function time_theta(N, lat, prec)
    t := Cputime();
    for i in [1..N] do
	th := ThetaSeries(ZLattice(lat), prec);
    end for;
    return Cputime()-t;
end function;

function time_isom(N, lat)
    t := Cputime();
    for i in [1..N] do
	_ := IsIsometric(lat,lat);
    end for;
    return Cputime()-t;
end function;

function binary_search_prec(thetas, num_distinct, start_prec)
    L := 0;
    R := start_prec;
    _<q> := Universe(thetas);
    while L le R do
	prec := (L + R) div 2;
	theta_pr := {th + O(q^(prec+1)) : th in thetas};
	if #theta_pr ge num_distinct then
	    R := prec-1;
	else
	    L := prec+1;
	end if;
    end while;
    return prec;
end function;

// Currently we're applying a binary search heuristic.
// Should be able to do better.
function get_max_req_prec(lats : start_prec := 1)
    // We first determine a precision for which all are different.
    prec := start_prec;
    done := false;
    while not done do
	prec *:= 2;
	thetas := {ThetaSeries(ZLattice(lat), prec) : lat in lats};
	if (#thetas eq #lats) then
	    done := true;
	end if;
    end while;
    /*
    _<q> := Universe(thetas);
    L := 0;
    R := prec;
    while L le R do
	prec := (L + R) div 2;
	theta_pr := {th + O(q^(prec+1)) : th in thetas};
	if #theta_pr eq #lats then
	    R := prec-1;
	else
	    L := prec+1;
	end if;
    end while;
   */
    prec := binary_search_prec(thetas, #lats, prec);
    return prec, thetas;
end function;

function get_best_prec(lats)
    L, thetas := get_max_req_prec(lats);
    // see what are the correct N's to use for testing
    t_full_th := &+[time_theta(10^3, lat, L) : lat in lats];
    t_isom := &+[time_isom(10^3, lat) : lat in lats];
    all_times := [<t_full_th, L>];
    num_dist := #lats;
    while (num_dist gt 1) do
	num_dist -:= 1;
	prec := binary_search_prec(thetas, num_dist, L);
	t_th := &+[time_theta(10^3, lat, prec) : lat in lats];
	avg_time := t_th + ((#lats) / num_dist-1) * t_isom;
	Append(~all_times, <avg_time, prec>);
    end while;
    min_time, argmin := Minimum(all_times);
    return min_time[2];
end function;

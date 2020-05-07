//freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: genus-CN1.m (implementation file for genus computations)

   Implementation file for computing p-neighbors for genus computations

   04/15/20: Added the unitary mass formula. At the moment still not using it.

   03/06/20: added the procedure checkNextNeighbor, for easier debugging and flow

   02/28/20: started editing this file to add Unitary forms
 
 ***************************************************************************/

// imports

import "../modfrmalg/modfrmalg.m" : ModFrmAlgInit;
import "neighbor-CN1.m" : BuildNeighborProc, BuildNeighbor, GetNextNeighbor;
import "inv-CN1.m" : Invariant;

// functions

procedure checkNextNeighbor(nProc, buildNeighbor, ~invs, ~isoList
			   : BeCareful := true)

    // Compute the neighbor according to the current state
    //  of the neighbor procedure.
    nLat := buildNeighbor(nProc : BeCareful := BeCareful);

    // A specified invariant of the neighbor lattice.
    inv := Invariant(nLat);

    // If this invariant is defined for the array, we need
    //  to potentially check for isometry.
    if IsDefined(invs, inv) then
       // Retrieve the array for this invariant.
       array := invs[inv];

       // Flag whether we found the right class.
       found := false;
       for i in [1..#array] do
	 // Check for isometry.
	 iso := IsIsometric(array[i][1], nLat);

         // Skip ahead if an isometry is found.
	 if iso then
	    found := true;
	    break;
	 end if;
       end for;

       // If no isometry found, add it to the list.
       if not found then
         Append(~invs[inv], < nLat, #isoList+1 >);
	 Append(~isoList, nLat);
       end if;
    else
       invs[inv] := [ < nLat, #isoList+1 > ];
       Append(~isoList, nLat);
    end if;

end procedure;

function computeGenusRepsAt(p, isoList, invs
		: BeCareful := true, Force := false)
	// The index of the current isometry class being considered.
	isoIdx := 1;

	repeat
		// Build the neighbor procedure for the current lattice.
		nProc := BuildNeighborProc(isoList[isoIdx], p, 1
			: BeCareful := BeCareful);

		repeat
		        checkNextNeighbor(nProc, BuildNeighbor,
					   ~invs, ~isoList);
			// Move on to the next neighbor lattice.
			nProc := GetNextNeighbor(nProc
				: BeCareful := BeCareful);
		until nProc`isoSubspace eq [];

		// Move on to the next genus representative.
		isoIdx +:= 1;
	until isoIdx gt #isoList;

	return isoList, invs;
end function;

forward UnitaryMass;

procedure computeGenusRepsCN1(M : BeCareful := true, Force := false)
	// Do not compute the genus representatives if they've already been
	//  computed and we aren't forcing a recomputation.
	if not Force and assigned M`genus then return; end if;

	// An upper bound for the norm of the primes at which we seek to
	//  compute genus reps.
	upTo := 0;

	// The list of genus representatives. We initialize this list with
	//  the standard lattice with respect to our inner form.
	genList := [ Module(M) ];

	// Initialize the associative array hashed by an invariant. This will
	//  allow us to reduce the number of isometry tests required to
	//  determine equivalence.
	invs := AssociativeArray();
	invs[Invariant(Module(M))] := [ < Module(M), 1 > ];

	RR := RealField();
	total_mass := 0;
	eps := Infinity(); // ensure one pass

	// The formula as stated is simply incorrect
	// Have to fix it
	/*
	if SpaceType(ReflexiveSpace(Module(M))) eq "Hermitian" then
	    // replace with the calculaiton of mass relative to this lattice
	    total_mass := UnitaryMass(BaseRing(M), Dimension(Module(M)));
	    eps := RR!10^(-30);
	end if;
       */
	
	repeat
		repeat
			// Increment norm by 10.
			upTo +:= 10;

			// Compute a list of primes which do not divide the
			//  discriminant of the lattice.
			ps := [ p : p in PrimesUpTo(upTo, BaseRing(M)) |
				Gcd(Integers()!Norm(Discriminant(Module(M))),
					Norm(p)) eq 1 ];
		until #ps ne 0;

		idx := 1;
		repeat
			// Compute genus representatives at a specific prime.
			genList, invs := computeGenusRepsAt(
				ps[idx], genList, invs
				: BeCareful := BeCareful, Force := Force);

			// Move to the next prime.
			idx +:= 1;
			acc_mass := RR!(&+[#AutomorphismGroup(rep)^(-1) : rep in genList]);
		until (idx gt #ps) or (Abs(acc_mass - total_mass) lt eps);
	until Abs(acc_mass - total_mass) lt eps;

	// TODO: add mass formula for orthogonal group

	// Assign the genus symbol for the space of algebraic modular forms.
	M`genus := New(GenusSym);
	M`genus`Representative := M`L;
	M`genus`Representatives := genList;
	M`genus`RepresentativesAssoc := invs;
end procedure;

function sortGenusCN1(genus)
	// An empty associative array.
	invs := AssociativeArray();

	// An ordered list of genus representatives;
	lats := Representatives(genus);

	for i in [1..#lats] do
		// Compute the invariant associated to this genus rep.
		inv := Invariant(lats[i]);

		// Assign an empty list to the invariant hash if it hasn't been
		//  assigned yet.
		if not IsDefined(invs, inv) then invs[inv] := []; end if;

		// Add to list.
		Append(~invs[inv], < lats[i], i >);
	end for;

	// Assign the representatives associated array.
	genus`RepresentativesAssoc := invs;

	return genus;
end function;

// mass formulas for verifying the genus

function UnitaryMass(L, m : prec := 30)
    L := AbsoluteField(L);
    ZZ_L := MaximalOrder(L);
    _,cc := HasComplexConjugate(L);
    F := sub<L|[L.1+cc(L.1)]>;
    ZZ_F := MaximalOrder(F);
    d := Degree(L) div 2;
    tau := 2;

    // When F ne QQ, this might work better
    /*
    chars := ArtinRepresentations(L);
  I := [i : i in [1..#chars] | Type(F!!chars[i]) eq RngIntElt];
  J := [j : j in [1..#chars] | j notin I];
  Ls := [&*[LSeries(chi) : chi in chars[J]], &*[LSeries(chi) : chi in chars[I]]];
    // If chi is the character of L/F, then Lodd is the L(chi^odd) and Leven is L(chi^even).
  LofM := &*[Evaluate(Ls[(r mod 2)+1],1-r) : r in [1..m]];
   */
    
    ZL := LSeries(L : Precision := prec);
    ZF := LSeries(F : Precision := prec);
    LofM :=  &*[Evaluate(ZL/ZF,1-r) : r in [1..m] | r mod 2 eq 1]*
	     &*[Evaluate(ZF,1-r) : r in [1..m] | r mod 2 eq 0];

    RF := &cat[[x[1] : x in Factorization(p*ZZ_F)] : p in PrimeFactors(Discriminant(ZZ_L))];
    ramified_primes := [I : I in RF | Factorization(ideal<ZZ_L|Generators(I)>)[1,2] gt 1];
    RL := [Factorization(ideal<ZZ_L|Generators(I)>)[1,1] : I in ramified_primes];
    
    if (m mod 2 ne 0) then
	qs := [#ResidueClassField(p) : p in RL];
	N := #ramified_primes;
	prod_of_local_factors := (1/2)^N;
    else
	// we need -1 to not be a norm in the completion -
	// at odd primes can be checked modulo the prime, at 2 must be checked mod 4
	not_norm := [p : p in RL | (not IsSquare(ResidueClassField(p)!(-1))) or (Norm(p) eq 2)];
	N := #not_norm;
	qs := [#ResidueClassField(p) : p in not_norm];
	if (m mod 4 eq 2) then
	    if IsEmpty(qs) then
		prod_of_local_factors := -1;
	    else
		if qs[1] eq 2 then
		    qs[1] := 4;
		end if;
		prod_of_local_factors := -(1/2)^N * &*[(q^m - 1) / (q + 1) : q in qs];
	    end if;
	else
	    
	    if IsEmpty(qs) then
		prod_of_local_factors := 1;
	    else
		if qs[1] eq 2 then
		    qs[1] := 4;
		end if;
		prod_of_local_factors := (1/2)^N * &*[(q^m - 1) / (q^2 - 1) : q in qs];
	    end if;
	   
	end if;
    end if;

    mass := 1/2^(m*d)*LofM*tau*prod_of_local_factors;

    return mass;
    
end function;

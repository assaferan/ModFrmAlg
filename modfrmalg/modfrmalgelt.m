freeze;

/****-*-magma-**************************************************************
                                                                            
                     Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
             
                                                                            
   FILE: modfrmalgelt.m (main structure file)

   Implementation file for elements belong to the space of algebraic modular
   forms. the space of algebraic modular forms.

   05/29/20: Normalized the L-polynomials, and extended their use to O(n)

   05/26/20: Modified HeckeEigensystem to return the results sorted

   05/11/20: Added the intrinsic LPolynomials, which returns the L-polynomials
             of f, up to a specified precision. At the moment, only supports 
             SO(n) for 3<=n<=8.

   05/08/20: Modified 'eq' to handle eigenvalues having a fixed universe.
             (so now we actually check the embedding matches all eigenvalues)

   04/21/20: Modified 'eq' to handle also finite field case.

   04/17/20 : Fixed a bug in HeckeEigensystem.

   04/16/20: Added intrinsic 'eq' to compare two modular forms.

   04/02/20: In HeckeEigensystem - verified that the base ring of the 
             Hecke operators is a subfield of the base ring of the 
             eigensystem. That makes it work even when loading from disk.
             (otherwise, Magma does not record the map)

   03/10/20: started editing this file to add Unitary forms
 
 ***************************************************************************/

// imports

import "modfrmalg.m" : ModFrmAlgInit;

import "../representation/representation.m" : nu;

///////////////////////////////////////////////////////////////////
//                                                               //
//    ModFrmAlgElt: The algebraic modular form element object.   //
//                                                               //
///////////////////////////////////////////////////////////////////

declare type ModFrmAlgElt;
declare attributes ModFrmAlgElt:
	// Ambient modular space.
	M,

	// A vector representation of a modular form in M.
	vec,

	// Is this an eigenform?
	IsEigenform,

	// Is this a cusp form?
	IsCuspidal,

	// Is this an Eisenstein form?
	IsEisenstein,

	// Does the theta series vanish?
	IsInThetaKernel,

	// An associative array of eigenvalues (only used if this element is
	//  flagged as an eigenform).
	Eigenvalues;

// printing

intrinsic Print(f::ModFrmAlgElt) {}
	printf "%o%o%o%o%o given in coordinates by\n%o",
		f`IsEisenstein select "Eisenstein " else "",
		f`IsCuspidal select "Cuspidal " else "",
		f`IsEigenform select "eigenform" else "",
		(f`IsCuspidal or f`IsEigenform) and not f`IsEigenform
			select "form" else "",
		f`IsEisenstein or f`IsCuspidal or f`Eigenform
			select "" else "Modular form",
		f`vec;
end intrinsic;

// access

intrinsic HeckeEigenvalues(f::ModFrmAlgElt, p::RngIntElt) -> SeqEnum
{Returns a list of all Hecke eigenvalues at the specified prime.}
     return HeckeEigenvalues(f, BaseRing(Module(f`M))!!p);
end intrinsic;

intrinsic HeckeEigenvalues(f::ModFrmAlgElt, pR::RngInt) -> SeqEnum
{ Returns a list of all Hecke eigenvalues at the specified prime. }
	return HeckeEigenvalues(f, ideal< BaseRing(Module(f`M)) | Norm(pR) >);
end intrinsic;

intrinsic HeckeEigenvalues(f::ModFrmAlgElt, pR::RngOrdIdl) -> SeqEnum
{ Returns a list of all Hecke eigenvalues at the specified prime. }
	// Verify that this is an eigenform.
	if not f`IsEigenform then return []; end if;

	// The largest possible type of Hecke operator to look at.
	// max := Floor(Dimension(QuadraticSpace(f`M)) / 2);

        max := Floor(Dimension(ReflexiveSpace(Module(f`M))) / 2);

	// Compute the Hecke eigenvalues.
	for i in [1..max] do _, _ := HeckeEigensystem(f, i); end for;

	// A list of eigenvalues.
	eigs := [];

	// Retrieve the eigenvalues we've already computed.
	for k in [1..max] do
		// Skip if the associative array for this dimension hasn't
		//  already been assigned.
		if IsDefined(f`Eigenvalues, k) then
			// Assign the eigenvalues at this dimension.
			if IsDefined(f`Eigenvalues[k], pR) then
				Append(~eigs, < k, f`Eigenvalues[k][pR] >);
			end if;
		end if;
	end for;

	return eigs;
end intrinsic;

intrinsic HeckeEigensystems(M::ModFrmAlg, k::RngIntElt) -> List, SeqEnum
{ Computes all Hecke eigensystems for the space of modular forms. }
	// Retrieve eigenforms.
	fs := HeckeEigenforms(M);

	// List of eigenforms.
	list := [* *];

	for f in fs do
		Es, Ps := HeckeEigensystem(f, k);
		Append(~list, < f, Es >);
	end for;

	return list, Ps;
end intrinsic;

intrinsic DisplayHeckeEigensystem(f::ModFrmAlgElt : Verbose := true)
{ Displays a formatted list of Hecke eigenvalues associated to the eigenform. }
	// Check whether this element is an eigenform.
	if not f`IsEigenform then return; end if;

	// Retrieve all dimensions at which eigenvalues have been computed
	keys := Keys(f`Eigenvalues);
	keys := Sort([ x : x in keys ]);

	// Print the eigenform.
	f;

	for dim in keys do
	    // Retrieve the eigenvalues and associate prime.
	    Es, Ps := HeckeEigensystem(f, dim);

	    // Display the pairing of eigenvalues and ideals.
	    printf "Hecke eigenvalues for T(p%o) operators:\n",
		   dim eq 1 select "" else "^" cat IntegerToString(dim);
	    for i in [1..#Es] do
		printf "\tPrime of norm %o -->\t %o\n",
		       Norm(Ps[i]), Es[i];
	    end for;
	end for;

	// Display a helpful hint by default.
	if Verbose then
		print "Use HeckeEigensystems intrinsic to retrieve these eigenvalues.";
	end if;
end intrinsic;

intrinsic HeckeEigensystem(f::ModFrmAlgElt) -> List, SeqEnum
{ Computes the eigenvalues at various primes associated to this eigenform. }
	return HeckeEigensystem(f, 1);
end intrinsic;

procedure updatePrecision(f, k, ~Precision)
  if IsZero(Precision) then
    already_known := {};
    if IsDefined(f`M`Hecke`Ts, k) then
       already_known := already_known join Keys(f`M`Hecke`Ts[k]);
    end if;
    if IsDefined(f`Eigenvalues, k) then
       already_known := already_known join Keys(f`Eigenvalues[k]);
    end if;
    if IsEmpty(already_known) then
       error "No eigenvalues have been computed for this eigenform";
    end if;
    Precision := Sort([x : x in already_known]);
  else
    // This handles the case of integers  
    if Type(Precision) eq SeqEnum then
       Precision := [Integers(BaseRing(f`M))!!I : I in Precision];
    end if;
  end if;
end procedure;

intrinsic HeckeEigensystem(f::ModFrmAlgElt, k::RngIntElt :
			   Precision := 0, BeCareful := false,
			   Estimate := true, Orbits := true,
			   UseLLL := true) -> List, SeqEnum
{ Computes the eigenvalues at various primes associated to this eigenform, for primes up to norm Precision. If Precision = 0, computes the eigenvalues only for precomputed hecke operators }
	// Check whether this element is an eigenform.
	if not f`IsEigenform then return []; end if;

	// Assign an associative array for the eigenvalues if one hasn't
	//  already been defined.
	if not assigned f`Eigenvalues then
		f`Eigenvalues := AssociativeArray();
	end if;

	// If no eigenvalues computed at this dimension, assign an empty array.
	if not IsDefined(f`Eigenvalues, k) then
	    f`Eigenvalues[k] := AssociativeArray();
	end if;

	// Get the pivot of the eigenform
	pivot := 0;
	repeat pivot +:= 1;
	until f`vec[pivot] ne 0;

        updatePrecision(f, k, ~Precision);
	
	if GetVerbose("AlgebraicModularForms") ge 2 then
	    print "Computing Hecke eigenvalues at new primes";
	end if;
	use_lll := UseLLL and (not IsSpecialOrthogonal(f`M));
	hecke_images := HeckeImages(f`M, pivot, Precision, k :
				    BeCareful := BeCareful,
				    Estimate := Estimate,
				    Orbits := Orbits,
				    UseLLL := use_lll);
	if Type(Precision) eq SeqEnum then
	    Ps := Precision;
	else
	    Ps := Sort([x : x in Keys(hecke_images)]);
	end if;
	found_emb := false;
        K := BaseRing(f`M`W);
        L := BaseRing(f`vec);  
	for p in Ps do
	    if IsDefined(f`Eigenvalues[k], p) then
		if not found_emb then
		       // K := BaseRing(f`M`W);
		       // L := BaseRing(f`vec);
		    if not IsPrimeField(K) then
			roots := Roots(MinimalPolynomial(K.1), L);
			embs := [hom<K -> L | root[1] > : root in roots];
			vec := Eltseq(hecke_images[p]);
			assert exists(emb){emb : emb in embs |
				       f`Eigenvalues[k][p] eq
				       DotProduct(f`vec,
						  Vector([emb(x) : x in vec]))};
			K2 := sub<L|emb(K.1)>;
			assert IsIsomorphic(K,K2);
		    end if;
		end if;
	    else
		hecke_image := ChangeRing(hecke_images[p], BaseRing(f`vec));
		f`Eigenvalues[k][p] := DotProduct(f`vec, hecke_image);
	    end if;
	end for;
	
	return [ f`Eigenvalues[k][P] : P in Ps ], [ P : P in Ps ];
end intrinsic;

intrinsic HeckeEigenforms(M::ModFrmAlg : Estimate := true) -> List
{ Returns a list of cusp forms associated to this space. }
	// Initialize space of modular forms if needed.
	ModFrmAlgInit(M);	

	// Check if eigenforms have already been computed.
	if assigned M`Hecke`Eigenforms then
		// Check to see if all elements are listed as eigenforms. If an
		//  element is not flagged as an eigenform, then it must come
		//  from a decomposable eigenspace, and so we'll want to
		//  recompute the eigenbasis; otherwise, return what we have
		//  since it is completely decomposed.
		if &and[ f`IsEigenform : f in M`Hecke`Eigenforms ] then
			return M`Hecke`Eigenforms;
		end if;
	end if;

        // Not needed, if none were computed, we will compute them
/*
	// Display an error if no Hecke matrices have been computed yet.
	require IsDefined(M`Hecke`Ts, 1): "Compute some Hecke matrices first!";
*/
        // Decompose the spaceto eigenspaces
        D := Decomposition(M : Estimate := Estimate);

        // This actually repeats the previous to get the also the eigenvectors.
        // Since main computation is Hecke operators, we let it go for now

	// Decompose eigenspace.
        if IsDefined(M`Hecke`Ts, 1) then
	  spaces, reducible := 
		EigenspaceDecomposition(M`Hecke`Ts[1] : Warning := false);
        else // space is zero-dimensional
	  spaces := [];
          reducible := [];
        end if;

	// This is not enough yet, since the spaces aren't the eigenvectors.
	// !!! TODO - replace this 100 by a well chosen bound
//	spaces := Decomposition(M, 100);
	
	// A list of cusp forms.
	eigenforms := [* *];

	// to see if they are cusp forms
	reps := Representatives(Genus(M));
	// !!! TODO :
	// Replace this by an actual bilinear form compatible with the group
	// Add handling the case when the narrow class group of the field
	// is nontrivial.
	wts := &cat[[#AutomorphismGroup(reps[i]) : j in [1..Dimension(M`H[i])]]:
		    i in [1..#reps]];
	// instead of dividing by wts[i], we multiply for the case of positive
	// characteristic
        wt_prod := IsEmpty(wts) select 1 else &*wts;
	mult_wts := [wt_prod div wt : wt in wts];
	
	for i in [1..#spaces] do
	    // Extract the first basis vector of the eigenspace.
	    vec := Basis(spaces[i])[1];
	    
	    //		for vec in basis do
	    // Construct an element of the modular space.
	    mform := New(ModFrmAlgElt);

	    // Assign parent modular space.
	    mform`M := M;

            // for display purposes
            K_f := BaseRing(vec);
            if Type(K_f) ne FldRat then
               AssignNames(~K_f, [Sprintf("a_%o", i)]);
            end if;
	    // Assign vector.
	    mform`vec := vec;

	    // If the weight is non-trivial all forms are cuspidal
            // !!! TODO - do the general case, we might have some
            // multiplicity of the trivial representation
            if (Rank(Weight(M)) gt 1) or
	       ((assigned Weight(M)`weight) and (Weight(M)`weight[1] ne 1)) then
              mform`IsCuspidal := true;
	    else
	      mform`IsCuspidal := &+[ Eltseq(vec)[i] * mult_wts[i] :
				    i in [1..#wts]] eq 0;
            end if;

	    // Cusp forms are not Eistenstein.
	    mform`IsEisenstein := not mform`IsCuspidal;

	    // This shouldn't happen if we fully decomposed the space.
	    // This is an eigenform if and only if the size
	    //  of the subspace has dimension 1.
	    mform`IsEigenform := not i in reducible;
	    // mform`IsEigenform := true;

	    // Add to list.
	    Append(~eigenforms, mform);
		
	    // Store the Eisenstein series in memory.
	    if mform`IsEisenstein then
		M`Hecke`EisensteinSeries := mform;
	    end if;
	    // end for;
	end for;

	// Assign Hecke eigenforms.
	M`Hecke`Eigenforms := eigenforms;

	return M`Hecke`Eigenforms;
end intrinsic;

intrinsic EisensteinSeries(M::ModFrmAlg) -> ModFrmAlgElt
{ Returns the normalized Eistenstein series. }
	// Initialize the space of modular forms.
	ModFrmAlgInit(M);

	// If we've already computed the Eisenstein series, return it.
	if assigned M`Hecke`EisensteinSeries then
		return M`Hecke`EisensteinSeries;
	end if;

	/*
	// Compute the inverse of the size of the  automorphism groups for each
	//  of the genus representatives.
	auts := [ 1 / #AutomorphismGroup(L) : L in Representatives(Genus(M)) ];

	// Normalized so that the first element in auts is 1.
	vec := Vector([ auts[1]^-1 * e : e in auts ]);
       */
	// In order to support positive characteristic we leave the coordinates
	// not normalized by weights.

	require Dimension(M`W) eq 1 :
		"Cannot create Eisenstein series for nontrivial weight!";
	vec := Vector([1 : i in [1..Dimension(M)]]);
	
	// Create the modular form corresponding to the Eisenstein series.
	mform := New(ModFrmAlgElt);
	mform`M := M;
	mform`vec := vec;
	mform`IsCuspidal := false;
	mform`IsEisenstein := true;
	mform`IsEigenform := true;

	// Assign the Eisenstein series.
	M`Hecke`EisensteinSeries := mform;

	return mform;
end intrinsic;

intrinsic ModularForm(f::ModFrmAlgElt) -> ModFrmElt
{ Attempts to associate this eigenform to a classical newform. }
	// Verify that this is an eigenform.
	if not f`IsEigenform then return []; end if;

	// Return nothing if this is an Eisenstein series.
	if f`IsEisenstein then return []; end if;

	// The dimension.
	dim := Dimension(QuadraticSpace(Module(f`M)));

	// Only works for ternary forms.
	// TODO: Expand this.
	if dim ne 3 and dim ne 5 then return []; end if;

	// The bad primes for this form.
	badPrimes := PrimeFactors(Norm(Discriminant(Module(f`M))));

	// Retrieve the eigenvalues and primes to which this form is associated.
	Es, Ps := HeckeEigensystem(f);

	// Pair up the eigenvalues and primes.
	tuples := [ < Norm(Ps[i]), Es[i] > : i in [1..Min(#Es,10)] ];

	// Skip the bad primes.
	tuples := [ e : e in tuples | not e[1] in badPrimes ];

	// Adjust eigenvalues down by p+p^2 when we're in dimension 5.
	if dim eq 5 then
		tuples := [ < e[1], e[2]-e[1]-e[1]^2 > : e in tuples ];
	end if;

	// Retrieve all divisors of the discriminant of the inner form.
	divs := Divisors(Norm(Discriminant(Module(f`M))));

	// The base ring of the eigenform.
	F := BaseRing(f`vec);

	// The degree of the base field.
	deg := Degree(F);

	for d in divs do
		// The newforms at this particular level.
		Snew := Newforms(CuspForms(d, dim eq 3 select 2 else 4));

		for list in Snew do
			// The base ring of this newform.
			K := BaseRing(list[1]);

			// Skip this form if the degrees of the base rings
			//  don't match.
			if Degree(K) ne deg then continue; end if;

			if deg ne 1 then
				// Check if the base fields are isomorphic.
				iso, map := IsIsomorphic(
					//F, FieldOfFractions(K));
					NumberField(K), F);

				// If not, skip it.
				if not iso then continue; end if;
			else
				// An identity map for use with the rationals.
				map := func< x | x >;
			end if;

			// Compare coefficients.
			found := &and[ map(Coefficient(list[1], e[1])) eq e[2]
				: e in tuples ];

			// If the coefficients match, return this form.
			if found then return list[1]; end if;
		end for;
	end for;

	return [];
end intrinsic;

intrinsic 'eq'(f1::ModFrmAlgElt, f2::ModFrmAlgElt) -> BoolElt
{.}
  L1 := BaseRing(f1`vec);
  L2 := BaseRing(f2`vec);
  if IsFinite(L1) then
      isom := IsFinite(L2) and #L1 eq #L2;
      char := Characteristic(L2);
      if #L2 eq char then
	  aut := [hom<L2->L2|>];
      else
	  baseField := FiniteField(char);
	  _, aut, _ := AutomorphismGroup(L2, baseField);
      end if;
  else
      isom, _ := IsIsomorphic(L1, L2);
      aut := Automorphisms(L2);
  end if;
  if not isom then return false; end if;
  f1_changed := ChangeRing(f1`vec, L2);
  f1_vecs := [Vector([a(x) : x in Eltseq(f1_changed)]) :
	      a in aut];
  if f2`vec notin f1_vecs then return false; end if;
  K1 := BaseRing(f1`M);
  K2 := BaseRing(f2`M);
  isom, psi := IsIsomorphic(K1, K2);
  if not isom then return false; end if;

  // This is actually an overkill, the vectors suffice,
  // Meantime, it's good for debugging
  if assigned f1`Eigenvalues then
      if not assigned f2`Eigenvalues then
	  return false;
      end if;
      keys := Keys(f1`Eigenvalues);
      if keys ne Keys(f2`Eigenvalues) then return false; end if;

      evs := [* [HeckeEigensystem(f, dim) : dim in keys] : f in [f1,f2] *];  

      F := [* FieldOfFractions(Universe(ev[1])) : ev in evs *];
     
      if IsFinite(F[1]) then
	  assert IsFinite(F[2]);
	  L := GF(LCM(#F[1], #F[2]));
	  embs := [hom<F[1]->L|>];
      else
	  assert not IsFinite(F[2]);
	  F[1] := AbsoluteField(F[1]);
	  F[2] := AbsoluteField(F[2]);
	  L := CompositeFields(F[1], F[2])[1];
	  if Type(F[1]) eq FldRat then
	      embs := [hom<F[1] -> L | >];
	  else
	      zeta := PrimitiveElement(F[1]);
	      roots := [x[1] : x in Roots(MinimalPolynomial(zeta), L)];
	      embs := [hom<F[1] -> L | r> : r in roots];
	  end if;
      end if;
      
      ev_L := [[L!y : y in x] : x in evs[2]];
      is_compat := exists(emb){emb : emb in embs |
				     [[emb(y) : y in x] : x in evs[1]] eq
				     ev_L};
      if not is_compat then return false; end if;
  elif assigned f2`Eigenvalues then
      return false;
  end if;
  return true;
end intrinsic;

intrinsic LPolynomial(f::ModFrmAlgElt, p::RngIntElt, d::RngIntElt :
		      Estimate := true, Orbits := true) -> RngUPolElt
{Compute the L-polynomial of f at the prime p up to precision x^d.
    Currently only implemented for good primes. }
    return LPolynomial(f, BaseRing(Module(f`M))!!p, d
		       : Estimate := Estimate, Orbits := Orbits);
end intrinsic;

// Currently only implemented for good L-factors
intrinsic LPolynomial(f::ModFrmAlgElt, p::RngOrdIdl, d::RngIntElt :
		      Estimate := true, Orbits := true) -> RngUPolElt
{Compute the L-polynomial of f at the prime p up to precision x^d.
    Currently only implemented for good primes. }
  L := Module(f`M);
  n := Dimension(ReflexiveSpace(L));

  require (3 le n) and (n le 8) : "Currently only implemented for 3<=n<=8";

  n_evs := Minimum(d, n div 2);

  evs, _ := [HeckeEigensystem(f, k : Precision := [BaseRing(Module(f`M))!!p],
			      Estimate := Estimate,
			      Orbits := Orbits)[1] : k in [1..n_evs]];
  if n_evs lt n div 2 then
    evs cat:= [0 : i in [n_evs+1..n div 2]];
  end if;
  K := Universe(evs);
  K_x<x> := PowerSeriesRing(K);
  D := Integers()!(Norm(Discriminant(Module(f`M) :
				     GramFactor := 2, Half := IsOdd(n))));
  if assigned Weight(f`M)`weight then
     dw := Weight(f`M)`weight[1];
     w := Weight(f`M)`weight[2];
  else
    // In this case, we don't really know the weight.
    // We guess it is trivial. Could we infer it from W?
     w := 0;
  end if;
  is_split := (L`Vpp[p]`V`AnisoDim lt 2);
  p := Norm(p);
  // These explicit Satake polynomials are taken from Murphy's thesis 
  case n:
      when 3:
	  L_poly := p*x^2 - evs[1]*x+1;
      when 4:
          if is_split then
	    L_poly := p^4*x^4 - (evs[1]*p^2)*x^3 +
		    ((2+evs[2])*p)*x^2 - evs[1]*x + 1;
          else
       	    L_poly := (p*x-1)*(p*x+1)*(p^2*x^2-evs[1]*p*x+1);
	  end if;
      when 5:
          if D mod p ne 0 then
	     L_poly := p^(6+4*w)*x^4 - (evs[1]*p^(3+3*w))*x^3 +
	            ((evs[2] + p^2 + 1)*p^(1+2*w))*x^2 -
		    evs[1]*p^w*x + 1;
          else
	     eps_p := (-1)^w*WittInvariant(L,BaseRing(L)!!p);
             nu_p := (dw mod p eq 0) select nu(D,p) else 1;
             L_poly := p^(3+2*w)*x^2-(eps_p*p - nu(D,p)*(evs[1] + 1))*p^w*x+1;
             L_poly *:= eps_p*p^(1+w)*x+1;
	  end if;
      when 6:
          if is_split then
	    L_poly := p^12*x^6 - (evs[1]*p^8)*x^5 +
		      ((1+p+p^2+evs[2])*p^5)*x^4 -
		      ((2*evs[1]+evs[3])*p^3)*x^3 +
		      ((1+p+p^2+evs[2])*p)*x^2 - evs[1]*x + 1;
	  else
	    L_poly := (p^2*x-1)*(p^2*x+1)*(p^8*x^4 -
		       p^4*evs[1]*x^3 +
		       (1-p+p^2+p^3+evs[2])*p*x^2 -
		       evs[1]*x+1);
          end if;
      when 7:
	  L_poly := p^15*x^6 - (evs[1]*p^10)*x^5 +
		    ((evs[2]+1+p^2+p^4)*p^6)*x^4 -
		    (((p^2+1)*evs[1]+evs[3])*p^3)*x^3 +
		    ((evs[2]+1+p^2+p^4)*p)*x^2 -
		    evs[1]*x + 1;
      when 8:
          if is_split then
      // This is the L-poly for a split SO_8
	    L_poly := p^24*x^8 - (evs[1]*p^18)*x^7 +
		    ((evs[2]+p^4 + 2*p^2 +1)*p^13)*x^6 -
		    ((evs[3] + evs[1]*(p^2+p+1))*p^9)*x^5 +
		    ((evs[4]+2*evs[2]+2+2*p^2+2*p^4)*p^6)*x^4-
		    ((evs[3] + evs[1]*(p^2+p+1))*p^3)*x^3 +
		    ((evs[2]+p^4 + 2*p^2 +1)*p)*x^2 -
		    evs[1]*x + 1;
          else
      // This is the L-poly for a nonsplit SO_8
            L_poly := (p^3*x-1)*(p^3*x+1)*(p^18*x^6 -
		    (evs[1]*p^12)*x^5 +
	            (evs[2]+p^5+p^4+1)*p^7*x^4 -
	            (evs[3]+evs[1]*(p^3+p^2-p+1))*p^3*x^3 +
		    (evs[2]+p^5+p^4+1)*p*x^2 -
		    evs[1]*x + 1);
          end if;
   end case;
   if d ge 2*(n div 2) then
      K_x<x> := PolynomialRing(K);
      return K_x!Eltseq(L_poly);
   end if;
   return L_poly + O(x^(d+1));
end intrinsic;

intrinsic LPolynomials(f::ModFrmAlgElt : Precision := 0,
					 Estimate := true,
					 Orbits := true) -> SeqEnum[RngUPolElt]
{Compute the L-polynomials of f at primes up to norm precision.}
  require IsOrthogonal(f`M) : "Currently implemented only for orthogonal group";

  n := Dimension(ReflexiveSpace(Module(f`M)));

  require (3 le n) and (n le 8) : "Currently only implemented for 3<=n<=8";

  m := n div 2;

  if Type(Precision) eq SeqEnum then
    Ps := [Factorization(Integers(BaseRing(f`M)) !! p)[1][1] :
			p in Precision];
  elif (Precision eq 0) then
    Ps := [p : p in Keys(f`Eigenvalues[1])
	   | &and[p in Keys(f`Eigenvalues[j]) : j in [1..m]]];
  else
    Ps := [Factorization(Integers(BaseRing(f`M)) !! p)[1][1] :
			p in PrimesUpTo(Precision, Rationals())];
  end if;
  L_polys := AssociativeArray();
  for P in Ps do
      p := Norm(P);
      L_polys[p] := LPolynomial(f, p, n :
				Estimate := Estimate,
				Orbits := Orbits);
  end for;
  return L_polys;
end intrinsic;

intrinsic LSeries(f::ModFrmAlgElt : Precision := 0) -> LSer
{Build the L-series corresponding to f.}
  function local_factor(p,d)
    poly := LPolynomial(f, p, d);
    CC := ComplexField();
    CC_x := PowerSeriesRing(CC);
    K := BaseRing(Parent(poly));
    r := Roots(DefiningPolynomial(K),CC)[1][1];
    if Type(K) eq FldRat then
      h := hom<K -> CC|>;
    else 
      h := hom<K -> CC | r>;
    end if;
    return CC_x![h(c) : c in Eltseq(poly)];
  end function;
  n := Dimension(ReflexiveSpace(Module(f`M)));
  D := Integers()!(Norm(Discriminant(Module(f`M) : GramFactor := 2,
				     Half := IsOdd(n))));
  if assigned Weight(f`M)`weight then
     d := Weight(f`M)`weight[1];
     w := Weight(f`M)`weight[2];
     j := Weight(f`M)`weight[3];
  else
    // In this case, we don't really know the weight.
    // We guess it is trivial. Could we infer it from W?
     d := 1;
     w := 0;
     j := 0;
  end if;
  // Change this to correspond to the correct weight
  // should be (??)
  // LSeries(2*n+4, [-n-1,-n,0,1], D) ?? doesn't make sense. look more closely
  return LSeries(2*w+4, [-w-1+j,-w+j,j,j+1], D, local_factor :
		 Sign := (-1)^w*nu(D,d), Precision := Precision);
end intrinsic;

function DualRoot(alpha, G)
  return CoweightLattice(G)!(2/Norm(alpha) * alpha);
end function;

function get_monomial(R, coweight)
  exps := Eltseq(coweight);
  pos := [Maximum(e, 0) : e in exps];
  neg := [Maximum(-e, 0) : e in exps];
  return Monomial(R, pos cat neg);
end function;

function p_binom(r, k, p)
  res := 1;
  for l in [1..k] do
    res *:= (p^(r-l+1)-1) / (p^l - 1);
  end for;
  return res;
end function;

function SatakeTransform(mu, G, A, sqrt_p, r, K, k, a, R)
  alphas := PositiveRoots(G);
  rho := 1/2*&+alphas;
  W := WeylGroup(G);
  sum := 0;
  for w in W do
    w_mu := CorootAction(W)(mu, w);
    // This might need handling of a denominator in general
    w_mu := ChangeRing(w_mu, Integers());
    e_w_mu := get_monomial(A, w_mu);
    prod := K!e_w_mu;
    for alpha in alphas do
      alpha_d := DualRoot(alpha, G);
      w_alpha_d := CorootAction(W)(alpha_d, w);
      w_alpha_d := ChangeRing(w_alpha_d, Integers());
      e_w_alpha_d := get_monomial(A, w_alpha_d);
      prod *:= K!(1-sqrt_p^2*e_w_alpha_d) / K!(1-e_w_alpha_d);
    end for;
    sum +:= prod;
  end for;
  den := Denominator(sum);
  assert IsMonomial(R!den);
  exps := Exponents(den);
  den_inv := Monomial(A, exps[r+1..2*r] cat exps[1..r]);
  assert den_inv * den eq 1;
  A_sum := Numerator(sum)*den_inv;
  assert K!A_sum eq sum;
  K_mod_I := &+[sqrt_p^(2*CoxeterLength(W,w)) : w in W];
  num_neighbors := sqrt_p^(k*(k-1)) * p_binom(r,k,sqrt_p^2);
  min_i := Maximum(1, r+a-k);
  num_neighbors *:= &*[sqrt_p^(2*i) + 1 : i in [min_i..r+a-1]];
  p_exp := &+[mu[i]*rho[i] : i in [1..r]];
  sqrt_p_exp := Integers()!(2*p_exp);
  satake_mu := sqrt_p^(-sqrt_p_exp) * num_neighbors / K_mod_I * A_sum;
  return satake_mu;
end function;

function SatakePolynomialInner(G, a, r, F)
  S<sqrt_p> := FunctionField(F);
  RR<[c]> := PolynomialRing(S, r);
  RR_x<x> := PolynomialRing(RR);
  if r eq 0 then
    return RR_x!1;
  end if;
  // This is our patch for now to get the correct roots for the nonsplit case
  // Should do something more generic to get the structure of a reductive group
  cartan_type := CartanName(RootDatum(G`G0))[1];
  if IsOdd(a) then
	  //cartan_type := (cartan_type eq "D") select "B" else "D";
    cartan_type := "B";
  end if;
  G := GroupOfLieType(StandardRootDatum(cartan_type, r),
		      BaseRing(G`G0));
  
  // We are doing it symbolically so that in the future we will be able to
  // compute it once and then plug different ps
  SS<[s]> := PolynomialRing(S, 2*r);
  I := ideal<SS | [s[i]*s[i+r]-1 : i in [1..r]]>;
  A := quo<SS|I>;
  s := [Sprintf("s%o", i) : i in [1..r]];
  s_inv := [Sprintf("s%o_inv", i) : i in [1..r]];
  AssignNames(~A, s cat s_inv);
  K := FieldOfFractions(A);
  R<[t]> := PolynomialRing(S, r);
  
  coeffs := [];
  for k in [1..r] do
    mu := CoweightLattice(G)!([1 : i in [1..k]] cat [0 : i in [1..r-k]]);
    satake_mu := SatakeTransform(mu, G, A, sqrt_p, r, K, k, a, SS);
    if (k eq r) and IsEven(a) then
      mu := CoweightLattice(G)!([1 : i in [1..r-1]] cat [-1]);
      satake_mu +:= SatakeTransform(mu, G, A, sqrt_p, r, K, k, a, SS);
    end if;
    cfs, mons := CoefficientsAndMonomials(satake_mu);
    exps := [Exponents(mon) : mon in mons];
    betas := [Eltseq(Vector(e[1..r]) - Vector(e[r+1..2*r])) : e in exps];
    abs_betas := [[Abs(b) : b in beta] : beta in betas];
    // Here we verify that this is a polynomial in s_i + s_i^(-1)
    abs_betas_idxs := [Index(betas, a) : a in abs_betas];
    assert &and[cfs[i] eq cfs[abs_betas_idxs[i]] : i in [1..#cfs]];
    satake_t := &+[cfs[Index(betas, a)]*Monomial(R, a) : a in Set(abs_betas)];
    h := hom<R-> A | [A.i + A.(i+r) : i in [1..r]] >;
    assert h(satake_t) eq satake_mu;
    b := S!ConstantTerm(satake_t);
    lc := LeadingCoefficient(satake_t);
    assert lc*ElementarySymmetricPolynomial(R, k)+b eq satake_t;
    Append(~coeffs, (-1)^k*(c[k] - b)/lc);
  end for;
  _<t> := PolynomialRing(RR);
  t_poly :=  t^r;
  if (r gt 0) then
     t_poly +:= &+[coeffs[i]*t^(r-i) : i in [1..r]];
  end if;
  x_poly := &+[Coefficient(t_poly, i)*x^(r-i)*(x^2+1)^i : i in [0..r]];
  return x_poly;
end function;

function SatakePolynomial(f, p : d := Infinity())
  M := f`M;
  G := M`G;
  L := Module(M);
  V := ReflexiveSpace(L);
  n := Dimension(V);
  // verify whether this is the number of eigenvalues we need.
  n_evs := Minimum(d, n div 2);
  // This is not the most efficient way - we could first check if the
  // group is split at p or not (compute r) and then compute only up to r
  // plugging in the eigenvalues
  evs, _ := [HeckeEigensystem(f, k : Precision := [BaseRing(L)!!p])[1] :
			       k in [1..n_evs]];
  if n_evs lt n div 2 then
    evs cat:= [0 : i in [n_evs+1..n div 2]];
  end if;
  evs_fld := Universe(evs);
  evs_fld_x<x> := PowerSeriesRing(evs_fld); 
  V := L`Vpp[p]`V;
  // This is to determine splitting or non-splitting.
  a := V`AnisoDim;
  r := V`WittIndex;
  x_poly := SatakePolynomialInner(G, a, r, evs_fld);
  RR_x<x> := Parent(x_poly);
  RR<[c]> := BaseRing(RR_x);
  S<sqrt_p> := BaseRing(RR);
  if (a eq 2) then
    if (a + 2*r eq n) then
      x_poly *:= (1-x)*(1+x);
    else // ramified case, take extra care
      eps := WittInvariant(L, BaseRing(L)!!p);
      x_poly *:= 1 + (eps/sqrt_p^(n-2))*x;
    end if;
  end if;
  // normalizing to have integral coefficients
  nor_lp := Evaluate(x_poly, (sqrt_p)^(n-2) * x);
  // in case it is too short
  evs := evs cat [0 : i in [1..r - #evs]];
  // in case it is too long
  evs := evs[1..r];
  ev_hom := hom< RR -> S | evs >;
  S_x<x> := PolynomialRing(S);
  ev_hom_poly := hom<RR_x -> S_x | ev_hom, [x] >;
  // now we plug in sqrt(p) back again into the polynomial
  K<sqrtp> := QuadraticField(p);
  ev := hom<S -> K | sqrtp>;
  K_x<x> := PolynomialRing(K);
  ev_poly := hom<S_x -> K_x | ev, [x]>;
  ret := evs_fld_x!ev_poly(ev_hom_poly(nor_lp));
  _<x> := Parent(ret);
  if d ge 2*(n div 2) then
      evs_fld_x<x> := PolynomialRing(evs_fld);
      return evs_fld_x!Eltseq(ret);
  end if;
  return ret + O(x^(d+1));
end function;

function SatakeLSeries(f : Precision := 0)
  function local_factor(p,d)
    poly := SatakePolynomial(f, p : d := d);
    CC := ComplexField();
    CC_x := PowerSeriesRing(CC);
    K := BaseRing(Parent(poly));
    r := Roots(DefiningPolynomial(K),CC)[1][1];
    if Type(K) eq FldRat then
      h := hom<K -> CC|>;
    else 
      h := hom<K -> CC | r>;
    end if;
    return CC_x![h(c) : c in Eltseq(poly)];
  end function;
  M := f`M;
  L := Module(M);
  n := Dimension(ReflexiveSpace(L));
  D := Integers()!(Norm(Discriminant(L : GramFactor := 2)));

  if assigned Weight(M)`lambda then
    lambda := Weight(M)`lambda;
    lambda := lambda[1..n div 2];
    // Does this eork in general?
    w := (#lambda gt 1) select lambda[1]-lambda[2] else lambda[1];
    k := (n div 2)*(w+2);
    sign := 1;
    gammas := (#lambda gt 1) select [x + lambda[2]
				       : x in [-w-1,-w,0,1]] else [0,w+1];
  elif assigned Weight(M)`weight then
     d := Weight(M)`weight[1];
     w := Weight(M)`weight[2];
     j := Weight(M)`weight[3];
     sign := (-1)^w*nu(D,d);
     k := 2*w+4;
     gammas := [-w-1+j,-w+j,j,j+1];
  else
    error "LSeries parameters are unknown for this choice of weight.\n";
  end if;
  // We currently not include spinor norm
  return LSeries(k, gammas, D, local_factor :
		 Sign := sign, Precision := Precision);
end function;

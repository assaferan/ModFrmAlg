freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
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

intrinsic HeckeEigenvalues(f::ModFrmAlgElt, pR::RngInt) -> SeqEnum
{ Returns a list of all Hecke eigenvalues at the specified prime. }
	return HeckeEigenvalues(f, ideal< BaseRing(Module(f`M)) | Norm(pR) >);
end intrinsic;

intrinsic HeckeEigenvalues(f::ModFrmAlgElt, pR::RngOrdIdl) -> SeqEnum
{ Returns a list of all Hecke eigenvalues at the specified prime. }
	// Verify that this is an eigenform.
	if not f`IsEigenform then return []; end if;

	// The largest possible type of Hecke operator to look at.
	max := Floor(Dimension(QuadraticSpace(f`M)) / 2);

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

intrinsic HeckeEigensystem(f::ModFrmAlgElt, k::RngIntElt :
			   prec := 0, BeCareful := false,
			   Estimate := true, Orbits := true,
			   UseLLL := true) -> List, SeqEnum
{ Computes the eigenvalues at various primes associated to this eigenform, for primes up to norm prec. If prec = 0, computes the eigenvalues only for precomputed hecke operators }
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

	if IsZero(prec) then
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
	    prec := Sort([x : x in already_known]);
	end if;
	
	if GetVerbose("AlgebraicModularForms") ge 2 then
	    print "Computing Hecke eigenvalues at new primes";
	end if;
	use_lll := UseLLL and (not IsSpecialOrthogonal(f`M));
	hecke_images := HeckeImages(f`M, pivot, prec, k :
				    BeCareful := BeCareful,
				    Estimate := Estimate,
				    Orbits := Orbits,
				    UseLLL := use_lll);
	if Type(prec) eq SeqEnum then
	    Ps := prec;
	else
	    Ps := Sort([x : x in Keys(hecke_images)]);
	end if;
/*
	K := BaseRing(f`M`W);
	L := BaseRing(f`vec);
	roots := Roots(MinimalPolynomial(K.1), L);
	emb := hom<K -> L | roots[1][1]>;
	for p in Ps do
	    hecke_image := Vector([emb(x) : x in Eltseq(hecke_images[p])]);
	    f`Eigenvalues[k][p] := DotProduct(f`vec, hecke_image);
	end for;
*/
	found_emb := false;
	for p in Ps do
	    if IsDefined(f`Eigenvalues[k], p) then
		if not found_emb then
		    K := BaseRing(f`M`W);
		    L := BaseRing(f`vec);
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

intrinsic HeckeEigenforms(M::ModFrmAlg) -> List
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

	// Display an error if no Hecke matrices have been computed yet.
	require IsDefined(M`Hecke`Ts, 1): "Compute some Hecke matrices first!";

	// Decompose eigenspace.
	spaces, reducible :=
		EigenspaceDecomposition(M`Hecke`Ts[1] : Warning := false);

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
	wt_prod := &*wts;
	mult_wts := [wt_prod div wt : wt in wts];
	
	for i in [1..#spaces] do
		// Extract the first basis vector of the eigenspace.
		basis := Basis(spaces[i]);

		for vec in basis do
			// Construct an element of the modular space.
			mform := New(ModFrmAlgElt);

			// Assign parent modular space.
			mform`M := M;

			// Assign vector.
			mform`vec := vec;

			// Flag as cuspidal?
			mform`IsCuspidal := &+[ Eltseq(vec)[i] * mult_wts[i] :
						i in [1..#wts]] eq 0;

			// Cusp forms are not Eistenstein.
			mform`IsEisenstein := not mform`IsCuspidal;

			// This is an eigenform if and only if the size
			//  of the subspace has dimension 1.
			mform`IsEigenform := not i in reducible;

			// Add to list.
			Append(~eigenforms, mform);

			// Store the Eisenstein series in memory.
			if mform`IsEisenstein then
				M`Hecke`EisensteinSeries := mform;
			end if;
		end for;
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

intrinsic LPolynomials(f::ModFrmAlgElt : prec := 0,
					 Estimate := true,
					 Orbits := true) -> RngUPolElt
{Compute the L-polynomials of f at primes up to norm precision.}
  require IsOrthogonal(f`M) : "Currently implemented only for orthogonal group";

  n := Dimension(ReflexiveSpace(Module(f`M)));

  require (3 le n) and (n le 8) : "Currently only implemented for 3<=n<=8";

  m := n div 2;
  all_evs := AssociativeArray();
  for i in [1..m] do
      evs, ps := HeckeEigensystem(f, i : prec := prec,
					 Estimate := Estimate,
					 Orbits := Orbits);
      for j in [1..#ps] do
	  p := ps[j];
	  if not IsDefined(all_evs, p) then all_evs[p] := []; end if;
	  Append(~all_evs[p], evs[j]);
      end for;
  end for;
  L_polys := [* *];
  for P in ps do
      evs := all_evs[P];
      K := Universe(evs);
      K_x<x> := PolynomialRing(K);
      // Have to check what it should be when the base field is not QQ!!!
      p := Norm(P);
      // pre-normalization code
      /*
      if n mod 2 eq 1 then
	  is_p_square, sqrt_p := IsSquare(K!p);
	  if not is_p_square then
	      L<sqrt_p> := ext< K | x^2 - p>;
	      L_x<x> := PolynomialRing(L);
	  end if;
      end if;
      */
      case n:
      when 3:
	  // this was the version from Murphy's thesis
	  // L_poly := x^2 - (evs[1]/sqrt_p)*x+1;
	  // Here we normalize (multiply by sqrt_p)
	  L_poly := p*x^2 - evs[1]*x+1;
      when 4:
	  // L_poly := x^4 - (evs[1]/p)*x^3 +
	  //	    ((2+evs[2])/p)*x^2 - (evs[1]/p)*x + 1;
	  // normalization - multiplying by p
	  L_poly := p^4*x^4 - (evs[1]*p^2)*x^3 +
		    ((2+evs[2])*p)*x^2 - evs[1]*x + 1;
      when 5:
	  // L_poly := x^4 - (evs[1]/sqrt_p^3)*x^3 +
		//    ((evs[2] + p^2 + 1)/p^2)*x^2 -
	  //  (evs[1]/sqrt_p^3)*x + 1;
	  // normalization - multiplying by sqrt_p^3
	  L_poly := p^6*x^4 - (evs[1]*p^3)*x^3 +
		    ((evs[2] + p^2 + 1)*p)*x^2 -
		    evs[1]*x + 1;
      when 6:
	  // L_poly := x^6 - (evs[1]/p^2)*x^5 +
	//	    ((1+p+p^2+evs[2])/p^3)*x^4 -
	//	    ((2*evs[1]+evs[3])/p^3)*x^3 +
	//	    ((1+p+p^2+evs[2])/p^3)*x^2 - (evs[1]/p^2)*x + 1;
	  // normalization - multiplying by p^2
	  L_poly := p^12*x^6 - (evs[1]*p^8)*x^5 +
		    ((1+p+p^2+evs[2])*p^5)*x^4 -
		    ((2*evs[1]+evs[3])*p^3)*x^3 +
		    ((1+p+p^2+evs[2])*p)*x^2 - evs[1]*x + 1;
      when 7:
	 // L_poly := x^6 - (evs[1]/sqrt_p^5)*x^5 +
	//	    ((evs[2]+1+p^2+p^4)/p^4)*x^4 -
	//	    (((p^2+1)*evs[1]+evs[3])/sqrt_p^9)*x^3 +
	//	    ((evs[2]+1+p^2+p^4)/p^4)*x^2 -
	//	    (evs[1]/sqrt_p^5) * x + 1;
	  // normalization - multiplying by sqrt_p^5
	  L_poly := p^15*x^6 - (evs[1]*p^10)*x^5 +
		    ((evs[2]+1+p^2+p^4)*p^6)*x^4 -
		    (((p^2+1)*evs[1]+evs[3])*p^3)*x^3 +
		    ((evs[2]+1+p^2+p^4)*p)*x^2 -
		    evs[1]*x + 1;
      when 8:
	  //L_poly := x^8 - (evs[1]/p^3)*x^7 +
	//	    ((evs[2]+p^4 + 2*p^2 +1)/p^5)*x^6 -
	//	    ((evs[3] + evs[1]*(p^2+p+1))/p^6)*x^5 +
	//	    ((evs[4]+2*evs[2]+2+2*p^2+2*p^4)/p^6)*x^4-
	//	    ((evs[3] + evs[1]*(p^2+p+1))/p^6)*x^3 +
	//	    ((evs[2]+p^4 + 2*p^2 +1)/p^5)*x^2 -
	  //	    (evs[1]/p^3)*x + 1;
	  // normalization - multiplying by p^3
	  L_poly := p^24*x^8 - (evs[1]*p^18)*x^7 +
		    ((evs[2]+p^4 + 2*p^2 +1)*p^13)*x^6 -
		    ((evs[3] + evs[1]*(p^2+p+1))*p^9)*x^5 +
		    ((evs[4]+2*evs[2]+2+2*p^2+2*p^4)*p^6)*x^4-
		    ((evs[3] + evs[1]*(p^2+p+1))*p^3)*x^3 +
		    ((evs[2]+p^4 + 2*p^2 +1)*p)*x^2 -
		    evs[1]*x + 1;
      end case;
      Append(~L_polys, L_poly);
  end for;
  return L_polys;
end intrinsic;

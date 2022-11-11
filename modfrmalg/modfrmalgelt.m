freeze;

/****-*-magma-**************************************************************
                                                                            
                     Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J. Voight
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

// Here are the intrinsics this file defines
// Print(f::ModFrmAlgElt)
// HeckeEigenvalues(f::ModFrmAlgElt, p::RngIntElt) -> SeqEnum
// HeckeEigenvalues(f::ModFrmAlgElt, pR::RngInt) -> SeqEnum
// HeckeEigenvalues(f::ModFrmAlgElt, pR::RngOrdIdl) -> SeqEnum
// HeckeEigensystems(M::ModFrmAlg, k::RngIntElt) -> List, SeqEnum
// DisplayHeckeEigensystem(f::ModFrmAlgElt)
// HeckeEigensystem(f::ModFrmAlgElt) -> List, SeqEnum
// HeckeEigensystem(f::ModFrmAlgElt, k::RngIntElt) -> List, SeqEnum
// HeckeEigenforms(M::ModFrmAlg) -> List
// EisensteinSeries(M::ModFrmAlg) -> ModFrmAlgElt
// ModularForm(f::ModFrmAlgElt) -> ModFrmElt
// 'eq'(f1::ModFrmAlgElt, f2::ModFrmAlgElt) -> BoolElt
// LPolynomial(f::ModFrmAlgElt, p::RngIntElt, d::RngIntElt) -> RngUPolElt
// LPolynomial(f::ModFrmAlgElt, p::RngOrdIdl, d::RngIntElt) -> RngUPolElt
// LPolynomials(f::ModFrmAlgElt) -> SeqEnum[RngUPolElt]
// LSeries(f::ModFrmAlgElt) -> LSer

// imports

import "modfrmalg.m" : ModFrmAlgInit;

import "../neighbors/inv-CN1.m" : Invariant;
import "../neighbors/neighbor-CN1.m" : BuildNeighborProc;
import "../representation/representation.m" : nu;
import "../utils/linalg.m" : GetEigenvectors;

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

intrinsic BaseField(f::ModFrmAlgElt) -> Fld
{returns the field of definition of the vector representing the eigenform.}
  return BaseRing(f`vec);
end intrinsic;

intrinsic BaseRing(f::ModFrmAlgElt) -> Rng
{returns the field of definition of the vector representing the eigenform.}
  return BaseRing(f`vec);
end intrinsic;

intrinsic HeckeEigenvalue(f::ModFrmAlgElt, p::RngIntElt : k := 1) -> SeqEnum
{Returns the Hecke eigenvalue of T(p^k) at the specified prime.}
   R := BaseRing(Module(f`M));
   pR := Type(R) eq RngInt select ideal<R|p> else Factorization(R!!p)[1][1];
   return HeckeEigenvalue(f, pR : k := k);
end intrinsic;

intrinsic HeckeEigenvalue(f::ModFrmAlgElt, pR::RngInt : k := 1) -> SeqEnum
{Returns the Hecke eigenvalue of T(p^k) at the specified prime.}
  vals, _ := HeckeEigensystem(f, k : Precision := [pR]);
  return vals[1];
end intrinsic;

intrinsic HeckeEigenvalues(f::ModFrmAlgElt, p::RngIntElt) -> SeqEnum
{Returns a list of all Hecke eigenvalues at the specified prime.}
     R := BaseRing(Module(f`M));
     pR := Type(R) eq RngInt select ideal<R|p> else Factorization(R!!p)[1][1];
     return HeckeEigenvalues(f, pR);
end intrinsic;

intrinsic HeckeEigenvalues(f::ModFrmAlgElt, pR::RngInt) -> SeqEnum
{ Returns a list of all Hecke eigenvalues at the specified prime. }
	return HeckeEigenvalues(f, ideal< BaseRing(Module(f`M)) | Norm(pR) >);
end intrinsic;

intrinsic HeckeEigenvalues(f::ModFrmAlgElt, pR::RngOrdIdl) -> SeqEnum
{ Returns a list of all Hecke eigenvalues at the specified prime. }
        // not really needed
	// Verify that this is an eigenform.
	// if not f`IsEigenform then return []; end if;

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

intrinsic DisplayHeckeEigensystem(f::ModFrmAlgElt : Verbose := true, Precision := 0)
{ Displays a formatted list of Hecke eigenvalues associated to the eigenform. }
        // not really necessary
	// Check whether this element is an eigenform.
	// if not f`IsEigenform then return; end if;

	// Retrieve all dimensions at which eigenvalues have been computed
        if IsZero(Precision) then
          if assigned f`Eigenvalues then
	    keys := Keys(f`Eigenvalues);
          else
	    keys := [];
	  end if;
        else
          n := Dimension(Module(f`M));
          keys := [1..n div 2];
        end if;
	keys := Sort([ x : x in keys ]);

	// Print the eigenform.
	f;

	for dim in keys do
	    // Retrieve the eigenvalues and associate prime.
	    Es, Ps := HeckeEigensystem(f, dim : Precision := Precision);

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
       R := Integers(BaseRing(f`M));
       if Type(R) ne RngInt then
         Precision := [R!!I : I in Precision];
       end if;
    end if;
  end if;
end procedure;

intrinsic HeckeEigensystem(f::ModFrmAlgElt, k::RngIntElt :
			   Precision := 0, BeCareful := false,
			   Estimate := true, Orbits := true,
			   UseLLL := true, LowMemory := false,
			   ThetaPrec := 25) -> List, SeqEnum
{ Computes the eigenvalues at various primes associated to this eigenform, for primes up to norm Precision. If Precision = 0, computes the eigenvalues only for precomputed hecke operators }
         // !! No reason to do this - if this is an irreducible Hecke eigenspace,
         // we can still find the eigenvalues
	 // Check whether this element is an eigenform.
         // if not f`IsEigenform then return []; end if;

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
				    UseLLL := use_lll,
				    LowMemory := LowMemory,
				    ThetaPrec := ThetaPrec);
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
				       f`Eigenvalues[k][p] * f`vec[pivot] eq
				       DotProduct(f`vec,
						  Vector([emb(x) : x in vec]))};
			K2 := sub<L|emb(K.1)>;
			assert IsIsomorphic(K,K2);
		    end if;
		end if;
	    else
		hecke_image := ChangeRing(hecke_images[p], BaseRing(f`vec));
		f`Eigenvalues[k][p] := DotProduct(f`vec, hecke_image) / f`vec[pivot];
	    end if;
	end for;
	
	return [ f`Eigenvalues[k][P] : P in Ps ], [ P : P in Ps ];
end intrinsic;

intrinsic HeckeEigenforms(M::ModFrmAlg : Estimate := true,
			  Orbits := true, LowMemory := false, ThetaPrec := 25) -> List
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
        // if the discriminant is not square-free, we might have old forms
        // In this case, we have to set a bound.
        disc := Discriminant(Level(M));
        // Since we only work with integral lattices, there is no harm in that
        if Type(disc) eq FldRatElt then
          disc := Integers()!disc;
        end if;
        fac := Factorization(disc);
	if IsEven(Rank(Level(M))) then
	    is_sqrfree := &and[ fa[2] le 3 : fa in fac];
	else
            is_sqrfree := &and[fa[2] eq 1 : fa in fac];
	end if;
        if is_sqrfree and not IsSpecialOrthogonal(M) then
	  // Decompose the space to eigenspaces
          D := Decomposition(M : Estimate := Estimate,
			     Orbits := Orbits, LowMemory := LowMemory,
			     ThetaPrec := ThetaPrec);
	else
	    // !! TODO - figre out the correct Hecke bound
	    bound := 20;
	    D := Decomposition(M, bound : Estimate := Estimate,
					  Orbits := Orbits, LowMemory := LowMemory,
					  ThetaPrec := ThetaPrec);
	end if;

        // This actually repeats the previous to get also the eigenvectors.
        // Since main computation is Hecke operators, we let it go for now

	// Decompose eigenspace.
        if IsDefined(M`Hecke`Ts, 1) then
	  // spaces, reducible := 
	    //	EigenspaceDecomposition(M`Hecke`Ts[1] : Warning := false);
	    vecs, is_eigenform := GetEigenvectors(M, D);
	    // spaces := [sub<Parent(v) | v> : v in vecs];
	    // reducible := [];
        else // space is zero-dimensional
	    // spaces := [];
            // reducible := [];
	    vecs := [];
	    is_eigenform := [];
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
	wts := &cat[[#AutomorphismGroup(reps[i] : Special := IsSpecialOrthogonal(M))
		     : j in [1..Dimension(M`H[i])]]: i in [1..#reps]];
	// instead of dividing by wts[i], we multiply for the case of positive
	// characteristic
        wt_prod := IsEmpty(wts) select 1 else &*wts;
	mult_wts := [wt_prod div wt : wt in wts];
	
	// for i in [1..#spaces] do
	for i in [1..#vecs] do
	    // We build a form for every basis vector
	    // for vec in Basis(spaces[i]) do
	    vec := vecs[i];

		//	    vec := Basis(spaces[i])[1];
	    
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

		// This shouldn't happen if we fully decomposed the space.
		// This is an eigenform if and only if the size
		//  of the subspace has dimension 1.
		// mform`IsEigenform := true; // not i in reducible;

		mform`IsEigenform := is_eigenform[i];
		
		// If the weight is non-trivial all forms are cuspidal
		// !!! TODO - do the general case, we might have some
		// multiplicity of the trivial representation
		if not IsTrivial(Weight(M)) then
		    mform`IsCuspidal := true;
		else
		    mform`IsCuspidal := &+[ Eltseq(vec)[i] * mult_wts[i] :
					    i in [1..#wts]] eq 0;
		end if;
		
		// Cusp forms are not Eistenstein.
		mform`IsEisenstein := not mform`IsCuspidal;

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
	
	// require Dimension(M`W) eq 1 :
	require IsTrivial(M`W) : 
			 "Cannot create Eisenstein series for non-trivial weight";

	require Dimension(M) gt 0 :
				  "There are no Eisenstein Series in a 0-dimensional space";
	vec := Vector(BaseRing(M`W), [1 : i in [1..Dimension(M)]]);
	
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
  isom := IsIsomorphic(K1, K2);
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
		      Estimate := true, Orbits := true,
		      LowMemory := false,
		      ThetaPrec := 25, Satake := false) -> RngSerPowElt
{Compute the L-polynomial of f at the prime p up to precision x^d.
    Currently only implemented for good primes. }
    R := BaseRing(Module(f`M));
    pR := ideal<R | p>;
    return LPolynomial(f, pR, d
		       : Estimate := Estimate, Orbits := Orbits,
		       LowMemory := LowMemory, ThetaPrec := ThetaPrec, Satake := Satake);
end intrinsic;

intrinsic LPolynomial(f::ModFrmAlgElt, p::RngIntElt :
		      Estimate := true, Orbits := true,
		      LowMemory := false,
		      ThetaPrec := 25, Satake := false) -> RngUPolElt
{Compute the L-polynomial of f at the prime p.
    Currently only implemented for good primes. }
    R := BaseRing(Module(f`M));
    pR := ideal<R | p>;
    return LPolynomial(f, pR 
		       : Estimate := Estimate, Orbits := Orbits,
		       LowMemory := LowMemory, ThetaPrec := ThetaPrec, Satake := Satake);
end intrinsic;

// used in the following intrinsics
function lpoly(f, p, d, Estimate, Orbits, LowMemory, ThetaPrec : Satake := false)
  L := Module(f`M);
  n := Dimension(ReflexiveSpace(L));
  R := BaseRing(L);
  if Type(R) eq RngInt then
      pR := ideal<R | p>;
  else
    pR := Factorization(Integers(BaseRing(L))!!p)[1][1]; 
  end if;

  n_evs := Minimum(d, n div 2);

  evs, _ := [HeckeEigensystem(f, k : Precision := [pR],
			      Estimate := Estimate,
			      Orbits := Orbits,
			      LowMemory := LowMemory,
			      ThetaPrec := ThetaPrec)[1] : k in [1..n_evs]];
  if n_evs lt n div 2 then
    evs cat:= [0 : i in [n_evs+1..n div 2]];
  end if;
  K := Universe(evs);
  K_x<x> := PowerSeriesRing(K);
  D := Integers()!(Norm(Discriminant(Module(f`M))));
  if assigned Weight(f`M)`weight then
     dw := Weight(f`M)`weight[1];
     w := Weight(f`M)`weight[2];
  else
    // In this case, we don't really know the weight.
    // We guess it is trivial. Could we infer it from W?
     w := 0;
     dw := 1;
  end if;
  if not IsDefined(L`Vpp, pR) then
    nProc := BuildNeighborProc(L, pR, 1);
  end if;
  is_split := (L`Vpp[p]`V`AnisoDim lt 2);
  p := Norm(pR);
  // These explicit Satake polynomials are taken from Murphy's thesis 
  case n:
      when 3:
	  L_poly := p*x^2 - evs[1]*x+1;
      when 4:
          if is_split then
	    L_poly := p^4*x^4 - (evs[1]*p^2)*x^3 +
		    ((2+evs[2])*p)*x^2 - evs[1]*x + 1;
          else
       	    L_poly := (p*x-1)*(p*x+1)*(p^2*x^2-evs[1]*x+1);
	  end if;
      when 5:
          if D mod p ne 0 then
	     L_poly := p^(6+4*w)*x^4 - (evs[1]*p^(3+3*w))*x^3 +
	            ((evs[2] + p^2 + 1)*p^(1+2*w))*x^2 -
		    evs[1]*p^w*x + 1;
          else
	     eps_p := (-1)^w*WittInvariant(L,pR);
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
  if Satake then
      L_poly<x> := SatakePolynomial(f,p : d := d);
  end if;
  if d ge 2*(n div 2) then
      K_x<x> := PolynomialRing(K);
      return K_x!Eltseq(L_poly);
  end if;
  return L_poly + O(x^(d+1));
end function;

// Currently only implemented for good L-factors
intrinsic LPolynomial(f::ModFrmAlgElt, p::RngOrdIdl, d::RngIntElt :
		      Estimate := true, Orbits := true,
		      LowMemory := false, ThetaPrec := 25, Satake := false) -> RngSerPowElt
{Compute the L-polynomial of f at the prime p up to precision x^d.
    Currently only implemented for good primes. }
  L := Module(f`M);
  n := Dimension(ReflexiveSpace(L));
  require ((3 le n) and (n le 8)) or Satake : "Currently only implemented for 3<=n<=8";
  return lpoly(f, p, d, Estimate, Orbits, LowMemory, ThetaPrec : Satake := Satake);
end intrinsic;

// Currently only implemented for good L-factors
intrinsic LPolynomial(f::ModFrmAlgElt, p::RngOrdIdl :
		      Estimate := true, Orbits := true,
		      LowMemory := false, ThetaPrec := 25, Satake := false) -> RngUPolElt
{Compute the L-polynomial of f at the prime p up to precision x^d.
    Currently only implemented for good primes. }
  L := Module(f`M);
  n := Dimension(ReflexiveSpace(L));
  require ((3 le n) and (n le 8)) or Satake : "Currently only implemented for 3<=n<=8";
  return lpoly(f, p, n, Estimate, Orbits, LowMemory, ThetaPrec : Satake := Satake);
end intrinsic;

// Currently only implemented for good L-factors
intrinsic LPolynomial(f::ModFrmAlgElt, p::RngInt :
		      Estimate := true, Orbits := true,
		      LowMemory := false, ThetaPrec := 25, Satake := false) -> RngUPolElt
{Compute the L-polynomial of f at the prime p up to precision x^d.
    Currently only implemented for good primes. }
  L := Module(f`M);
  n := Dimension(ReflexiveSpace(L));
  require Degree(BaseRing(f`M)) eq 1 : "Base Field is not the Rational Field, need to speicfy a prime ideal";
  require ((3 le n) and (n le 8)) or Satake : "Currently only implemented for 3<=n<=8";
  return lpoly(f, p, n, Estimate, Orbits, LowMemory, ThetaPrec : Satake := Satake);
end intrinsic;

// Currently only implemented for good L-factors
intrinsic LPolynomial(f::ModFrmAlgElt, p::RngInt, d::RngIntElt:
		      Estimate := true, Orbits := true,
		      LowMemory := false, ThetaPrec := 25, Satake := false) -> RngSerPowElt
{Compute the L-polynomial of f at the prime p up to precision x^d.
    Currently only implemented for good primes. }
  L := Module(f`M);
  n := Dimension(ReflexiveSpace(L));
  require Degree(BaseRing(f`M)) eq 1 : "Base Field is not the Rational Field, need to speicfy a prime ideal";
  require ((3 le n) and (n le 8)) or Satake : "Currently only implemented for 3<=n<=8";
  return lpoly(f, p, d, Estimate, Orbits, LowMemory, ThetaPrec : Satake := Satake);
end intrinsic;

intrinsic LPolynomials(f::ModFrmAlgElt : Precision := 0,
					 Estimate := true,
		                         Orbits := true,
		       LowMemory := false,
		       ThetaPrec := 25)-> SeqEnum[RngUPolElt]
{Compute the L-polynomials of f at primes up to norm precision.}
  require IsOrthogonal(f`M) : "Currently implemented only for orthogonal group";

  n := Dimension(ReflexiveSpace(Module(f`M)));

  require (3 le n) and (n le 8) : "Currently only implemented for 3<=n<=8";

  m := n div 2;

  if Type(Precision) eq SeqEnum then
    R := Integers(BaseRing(f`M));
    if Type(R) eq RngInt then
      Ps := [ideal<R|p> : p in Precision];
    else
      Ps := [Factorization(R !! p)[1][1] :
			p in Precision];
    end if;
  elif (Precision eq 0) then
    Ps := [p : p in Keys(f`Eigenvalues[1])
	   | &and[p in Keys(f`Eigenvalues[j]) : j in [1..m]]];
  else
    R := Integers(BaseRing(f`M));
    if Type(R) eq RngInt then
      Ps := PrimesUpTo(Precision, Rationals());
    else
      Ps := [Factorization(R !! p)[1][1] :
			p in PrimesUpTo(Precision, Rationals())];
    end if;
  end if;
  L_polys := AssociativeArray();
  for P in Ps do
      p := Norm(P);
      L_polys[p] := LPolynomial(f, P, n :
				Estimate := Estimate,
				Orbits := Orbits,
				LowMemory := LowMemory,
				ThetaPrec := ThetaPrec);
  end for;
  return L_polys;
end intrinsic;

intrinsic LSeries(f::ModFrmAlgElt : Precision := 0,
		  Estimate := true, Orbits := true, LowMemory := false,
		  ThetaPrec := 25) -> LSer
{Build the L-series corresponding to f.}
  function local_factor(p,d)
    poly := LPolynomial(f, p, d : Estimate := Estimate,
			Orbits := Orbits, LowMemory := LowMemory,
			ThetaPrec := ThetaPrec);
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
  D := Integers()!(Norm(Discriminant(Module(f`M))));
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
  return LSeries(2*w+n-1, [-w-1+j,-w+j,j,j+1], D, local_factor :
		 Sign := (-1)^w*nu(D,d), Precision := Precision);
end intrinsic;

intrinsic ThetaSeries(f::ModFrmAlgElt : Precision := 25) -> RngSerPuisElt
{return the theta series associated to f.}
  v := f`vec;
  R<q> := PuiseuxSeriesRing(BaseRing(v));
  dim := Degree(v);
  reps := Representatives(Genus(f`M));
  aut := [#AutomorphismGroup(r : Special := IsSpecialOrthogonal(f`M)) : r in reps];
  invs := [R | Invariant(r : Precision := Precision) : r in reps];
  return &+[aut[i]^-1*v[i]*invs[i] : i in [1..#reps]];
end intrinsic;

// This one is to make sure we got it all correctly
intrinsic ShimuraLift(f::RngSerPowElt, k::RngIntElt,
					  N::RngIntElt : Precision := 25) -> RngSerPowElt
	  {return the Shimura Lift of f in the space M_k(N) with precision q^prec.}
    keys := PrimesUpTo(Precision-1);
    eigenvalues := AssociativeArray(keys);
    for p in keys do
	chi1 := p eq 2 select 0 else (-1)^(((p-1) div 2)*(k div 2));
	eigenvalues[p] := Coefficient(f, p^2)+ chi1 * p^(k div 2 - 1);
    end for;
    R<q> := Parent(f);
    a := [BaseRing(R) | 1 : n in [1..Precision-1]];
    for n in [2..Precision-1] do
	if IsPrime(n) then
	    a[n] := eigenvalues[n];
	else
	    is_prime_power, p, e := IsPrimePower(n);
	    if is_prime_power then
		// Is n div p or p^(e-1) faster?
		a[n] := a[p]*a[p^(e-1)];
		if (N mod p ne 0) then
		    a[n] -:= p^(k-1) * a[p^(e-2)];
		end if;
	    else
		// Enough to find one divisor, is there a function to that?
		fac := Factorization(n);
		p_e := fac[1][1]^fac[1][2];
		m := n div p_e;
		a[n] := a[m]*a[p_e];
	    end if;
	end if;
    end for;
    lift := &+[a[n]*q^n : n in [1..Precision-1]] + O(q^Precision);
    return lift;
end intrinsic;

// This is a temporary fix that only works for spherical polynomial representations,
// namely for weights of the form [k,0]
function embed_v_in_rep(v)
    // Should do something smarter in general, but this should work for Sym^n
    // return &cat[[v[i]] cat [0 : j in [1..Degree(v)-1]] : i in [1..Degree(v)]];
    return [v[i] : i in [1..Degree(v)]];
end function;

function MatrixSquareRoot(Q)
    f_Q<x> := CharacteristicPolynomial(Q);
    K<a> := SplittingField(Evaluate(f_Q, x^2));
    Q_K := ChangeRing(Q,K);
    evs := [x[1] : x in Eigenvalues(Q_K)];
    V := Matrix(&cat[Basis(Eigenspace(Q_K,ev)) : ev in evs]);
    D := V*Q*V^(-1);
    sqrt_D := DiagonalMatrix([Sqrt(x) : x in Diagonal(D)]);
    sqrt_Q := V^(-1)*sqrt_D*V;
    assert sqrt_Q^2 eq Q;
    return sqrt_Q;
end function;

// This does not include the constant coefficient, coming from the 0 vector
intrinsic Theta1(f::ModFrmAlgElt : Precision := 25) -> RngSerPowElt
	  {Return the theta lift of f of genus 1 - we return the normalized cuspform for GL2.}
    v := f`vec;
    h_dims := [Dimension(h) : h in f`M`H];
    h_dimsum := [&+h_dims[1..i] : i in [0..#h_dims]];
    v_h := [Eltseq(v)[h_dimsum[i]+1..h_dimsum[i+1]] : i in [1..#f`M`H]];
    H := [ChangeRing(h, FieldOfFractions(BaseRing(v))) : h in f`M`H];
    vecs := [* &+[v_h[j][i]*H[j]`embedding(H[j].i) : i in [1..Dimension(H[j])]]
	     : j in [1..#H] *];
    if IsTrivial(f`M`W) then
	n := Rank(InnerForm(f`M));
	all_polys := [* [PolynomialRing(BaseRing(v),n)!1] : vec in vecs *];
    else
	all_polys := [* Names(Parent(vec)`M) : vec in vecs *];
    end if;
    vecvec := [* vec`m`vec : vec in vecs *];
    polys := [*&+[vecvec[j][i]*all_polys[j][i] : i in [1..#all_polys[j]]]
	      : j in [1..#all_polys]*];
    _<q> := PowerSeriesRing(BaseRing(v));
    reps := Representatives(Genus(f`M));
    aut := [#AutomorphismGroup(r : Special := IsSpecialOrthogonal(f`M)) : r in reps];
    fs := [];
    assert #reps eq #H;
    for i in [1..#reps] do
	r := reps[i];
	shortvecs := ShortVectors(ZLattice(r), 2*(Precision-1));
	shortvecs cat:= [<-v[1],v[2]> : v in shortvecs];
	// Here we divide by 2 to obtain the actual modular form
	// (which could be of half integral weight, when the rank is odd)
	f_r := &+[Evaluate(polys[i], embed_v_in_rep(v[1]))*q^(Integers()!v[2] div 2)
		  : v in shortvecs];
	Append(~fs, f_r);
    end for;
    theta := &+[aut[i]^-1*fs[i] : i in [1..#reps]] + O(q^Precision);
    // We return a normalized eigenform
    nonzero := exists(pivot){i : i in [1..Precision-1] | Coefficient(theta,i) ne 0};
    if nonzero then
	theta := Coefficient(theta,pivot)^(-1)*theta;
    end if;
    return theta;
end intrinsic;

// Here there is a question by what do we bound the vectors,
// as we do not have control on all entries of the Gram matrix
// (maybe we can do this, but requires adaptation of LLL)
// For now we bound the norm of both vectors (and not bound their inner product)
intrinsic Theta2(f::ModFrmAlgElt : Precision := 25) -> Assoc
{return the theta lift of f to GSp(4). Result is returned as an associative array
	with exponents of the variables as keys, and coefficients as values.}
    v := f`vec;
    // we no longer use the power series ring, because we have negative powers,
    // and this forces some cumbersome operations.
    // Instead we use a hash table mapping the exponents to the coefficient
    coeffs := AssociativeArray();
    reps := Representatives(Genus(f`M));
    for i in [1..#reps] do
	r := reps[i];
	shortvecs := ShortVectors(ZLattice(r), Precision);
	shortvecs cat:= [<-v[1],v[2]> : v in shortvecs];
	num_auts := #AutomorphismGroup(r : Special := IsSpecialOrthogonal(f`M));
	wt := num_auts^-1*v[i];
	for v1,v2 in shortvecs do
	    if (v1[1] eq v2[1]) or (v1[1] eq -v2[1]) then
		continue;
	    end if;
	    key := <v1[2], (v1[1], v2[1]), v2[2]>;
	    if not IsDefined(coeffs, key) then
		coeffs[key] := 0;
	    end if;
	    coeffs[key] +:= wt;
	end for;
    end for;
    return coeffs;
end intrinsic;

// This is the general theta series.
// For g = 1,2 it is slower than the implementations above
intrinsic ThetaSiegel(f::ModFrmAlgElt, g::RngIntElt : Precision := 25) -> Assoc
{return the theta lift of f to GSp(4). Result is returned as an associative array
        with exponents of the variables as keys, and coefficients as values.}
    v := f`vec;
    // we no longer use the power series ring, because we have negative powers,                
    // and this forces some cumbersome operations in magma                                     
    // Instead we use a hash table mapping the exponents to the coefficient
    coeffs := AssociativeArray();
    reps := Representatives(Genus(f`M));
    for i in [1..#reps] do
        r := reps[i];
        shortvecs := ShortVectors(ZLattice(r), Precision);
        shortvecs cat:= [<-v[1],v[2]> : v in shortvecs];
	num_auts := #AutomorphismGroup(r : Special := IsSpecialOrthogonal(f`M));
        wt := num_auts^-1*v[i];
	subseqs := Subsequences(Set(shortvecs), g);
	for xs in subseqs do
	    vecs := [x[1] : x in xs];
	    mat := Matrix(vecs);
            if (Rank(mat) ne g) then
                continue;
            end if;
            key := &cat[[(vecs[i], vecs[j]) : j in [1..i]] : i in [1..g]];
            if not IsDefined(coeffs, key) then
                coeffs[key] := 0;
            end if;
            coeffs[key] +:= wt;
        end for;
    end for;
    return coeffs;
end intrinsic;

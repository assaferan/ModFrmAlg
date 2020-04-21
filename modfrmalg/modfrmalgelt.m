freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: modfrmalgelt.m (main structure file)

   Implementation file for elements belong to the space of algebraic modular
   forms. the space of algebraic modular forms.

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
	printf "%o%o%o%o%o given in coordinates by\n%o\n",
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

	// Retrieve all dimensions at which Hecke operators have been computed.
	keys := Keys(f`M`Hecke`Ts);
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

intrinsic HeckeEigensystem(f::ModFrmAlgElt, k::RngIntElt) -> List, SeqEnum
{ Computes the eigenvalues at various primes associated to this eigenform. }
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

	// Retrieve the Hecke matrices and primes at which the Hecke matrices
	//  have been computed.
	Ts, Ps := HeckeOperators(f`M, k);

	for i in [1..#Ts] do
		// Do not recompute eigenvalue if it has already been computed.
		if IsDefined(f`Eigenvalues[k], Ps[i]) then continue; end if;

		// Promote the Hecke matrix to the base ring of the eigenform.
		// Magma doesn't do IsSubfield(QQ,QQ)
		if (Type(BaseRing(Ts[i])) ne FldRat) and
		    (Type(BaseRing(f`vec)) ne FldRat) then
		    _ := IsSubfield(BaseRing(Ts[i]), BaseRing(f`vec));
		end if;
		T := ChangeRing(Ts[i], BaseRing(f`vec));

		// Get the pivot of the eigenform.
		pivot := 0;
		repeat pivot +:= 1;
		until f`vec[pivot] ne 0;

		// Assign eigenvalue at the specified prime.
		// f`Eigenvalues[k][Ps[i]] := MVM(T, f`vec)[pivot];
		f`Eigenvalues[k][Ps[i]] := (f`vec * T)[pivot];
	end for;

	return [* f`Eigenvalues[k][P] : P in Ps *], [ P : P in Ps ];
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
			mform`IsCuspidal := &+[ x : x in Eltseq(vec) ] eq 0;

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

	// Compute the inverse of the size of the  automorphism groups for each
	//  of the genus representatives.
	auts := [ 1 / #AutomorphismGroup(L) : L in Representatives(Genus(M)) ];

	// Normalized so that the first element in auts is 1.
	vec := Vector([ auts[1]^-1 * e : e in auts ]);

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
  
  if assigned f1`Eigenvalues then
      if not assigned f2`Eigenvalues then
	  return false;
      end if;
      keys := Keys(f1`Eigenvalues);
      if keys ne Keys(f2`Eigenvalues) then return false; end if;

      evs := [[HeckeEigensystem(f, dim) : dim in keys] : f in [f1,f2]];  

      for k in keys do
	  if IsEmpty(evs[1][k]) then
	      if not IsEmpty(evs[2][k]) then return false; end if;
	      continue;
	  end if;

	  for j in [1..#evs[1][k]] do
	      F := [* FieldOfFractions(Parent(ev[k][j]))  : ev in evs *];
	      for ev_idx in [1..#evs] do
		  if not IsFinite(F[ev_idx]) then
		      F[ev_idx] := AbsoluteField(F[ev_idx]);
		  end if;
	      end for;

	      if IsFinite(F[1]) then
		  if not IsFinite(F[2]) then return false; end if;
		  L := FiniteField(LCM(#F[1], #F[2]));
		  embs := [hom< F[1] -> L |>];
	      else
		  if IsFinite(F[2]) then return false; end if;
		  L := Compositum(F[1], F[2]);
		  zeta := PrimitiveElement(F[1]);
		  roots := [x[1] : x in Roots(MinimalPolynomial(zeta), L)];
		  embs := [hom< F[1] -> L | r> : r in roots];
	      end if;
	      
	      if not exists(emb){emb : emb in embs |
			     emb(evs[1][k][j]) eq evs[2][k][j]} then
		  return false;
	      end if;
	  end for;
      end for;
  elif assigned f2`Eigenvalues then
      return false;
  end if;
  return true;
end intrinsic;

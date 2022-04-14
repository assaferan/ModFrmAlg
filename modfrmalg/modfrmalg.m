freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
 
                                                                            
   FILE: modfrmalg.m (Class of space of algebraic modular forms)

   Implementation file for the space of algebraic modular forms.

   05/26/20: Modified the constructor to look for a maximal integral lattice
             with respect to the form.

   05/04/20: Fixed a bug in ModFrmAlgInit, had to tell magma that two fields
             are isomorphic.

   04/27/20: Modified ModFrmAlgInit to use the special automorphism group,
             when working with SO.

   04/24/20: Removed attribute isogenyType,
             Modified constructors to use GrpRed instead of GrpLie,
             and use new constructors for Orthogonal and Unitary Group.
             Modified booleans IsOrthogonal and IsSpecialOrthogonal
             Modified equality testing to be based on GrpRed.
             Changed default value of parameter BeCareful to false.

   04/21/20: Modified 'eq' to fix bugs when over a finite field.
   	     Modified the OrthogonalModularForms constructor to normalize the field.

   04/20/20: Added normalizeField, for brevity.

   04/16/20: Added the intrinsic 'eq' to test equality between spaces 
             of modular forms.

   04/01/20: Changed ModFrmAlgInit to compute the weight space, added
             verbose.

   03/31/20: Added constructors for UnitaryModularForms from weight
             given by a tuple and a characteristic

   03/29/20: Added (commented out) code that is supposed to consrtuct 
             the Lie group for U_n in UnitaryModularForms

   03/26/20: modified initialization to calculate the space once and for
             all. Also added the space as the attribute M`H.
             Fixed the function dimension to return the actual dimension,
             and not just the dimension in the trivial weight case.
             Added creation from pullback - to handle weights over finite
             fields.

   03/21/20: Changed ModFrmAlgInit to not assume the object has been 
   	     initialized if M`W is assigned.

   03/20/20: Added a constructor for algebraic modular forms of arbitrary
             weight. Right now, weight is given as an object of type GrpRep,
             which is my construction of a group representation.  

   03/16/20: Added a constructor for orthogonal modular forms.

   03/11/20: Added constructor for Unitary Modular Forms from an inner form

   03/10/20: Discarded irrelevant imports.
             Moved here the type declaration.
	     Modified to use always the reflexive space implementation.

   03/05/20: Removed most initialization functions, leaving a single one which 
   receives group of lie type as argument.

   02/28/20: started editing this file to add Unitary forms
 
 ***************************************************************************/

// Here are the intrinsics this file defines
// AlgebraicModularForms(G::GrpRed, weight::GrpRep, level::AlgMatElt) -> ModFrmAlg
// AlgebraicModularForms(G::GrpRed, weight::GrpRep) -> ModFrmAlg
// AlgebraicModularForms(G::GrpRed) -> ModFrmAlg
// OrthogonalModularForms(innerForm::AlgMatElt, weight::GrpRep) -> ModFrmAlg
// OrthogonalModularForms(innerForm::AlgMatElt) -> ModFrmAlg
// UnitaryModularForms(innerForm::AlgMatElt, weight::GrpRep) -> ModFrmAlg
// UnitaryModularForms(innerForm::AlgMatElt) -> ModFrmAlg
// UnitaryModularForms(F::Fld, n::RngIntElt, weight::GrpRep) -> ModFrmAlg
// UnitaryModularForms(F::Fld, n::RngIntElt) -> ModFrmAlg
// UnitaryModularForms(F::Fld, n::RngIntElt, weight::SeqEnum, char::RngIntElt) -> ModFrmAlg
// UnitaryModularForms(F::Fld, innerForm::AlgMatElt, weight::SeqEnum, char::RngIntElt) -> ModFrmAlg
// OrthogonalModularForms(F::Fld, innerForm::AlgMatElt, weight::SeqEnum, char::RngIntElt) -> ModFrmAlg
// Print(M::ModFrmAlg, level::MonStgElt)
// IsSpecialOrthogonal(M::ModFrmAlg) -> BoolElt
// IsOrthogonal(M::ModFrmAlg) -> BoolElt
// Module(M::ModFrmAlg) -> ModDedLat
// Level(M::ModFrmAlg) -> ModDedLat
// BaseRing(M::ModFrmAlg) -> FldOrd
// InnerForm(M::ModFrmAlg) -> AlgMatElt
// Genus(M::ModFrmAlg) -> GenusSym
// SetAutomorphismGroups(~M::ModFrmAlg, autgps::SeqEnum)
// Dimension(M::ModFrmAlg) -> RngIntElt
// CuspidalSubspace(M::ModFrmAlg) -> ModMatFldElt
// CuspidalHeckeOperator(M::ModFrmAlg, p::RngIntElt) -> AlgMatElt
// 'eq'(M1::ModFrmAlg, M2::ModFrmAlg) -> BoolElt
// Representation(M::ModFrmAlg) -> ModTupFld
// VectorSpace(M::ModFrmAlg) -> ModTupFld
// Weight(M::ModFrmAlg) -> GrpRep

// imports

import "../neighbors/genus-CN1.m" : computeGenusRepsCN1;
import "../representation/representation.m" : projLocalization;

///////////////////////////////////////////////////////////////////
//                                                               //
//    ModFrmAlg: The space of algebraic modular forms object.    //
//                                                               //
///////////////////////////////////////////////////////////////////

// Data type for implementation of algebraic modular forms.
declare type ModFrmAlg;
declare attributes ModFrmAlg:
	// The Lie group.
	G,

	// The weight, as a representation of G.
	W,

	// The level.
	K,

	// The vector space (as a sequence of vector spaces)
	H,

	// The inner form as a lattice.
	L,

	// Hecke data structure.
	Hecke,

	// The genus symbol for this lattice.
	genus,

	// The filename from which this space was loaded.
	filename,

	// Generic L-polynomials for the split and non-split primes
	// These are cached on the first occurence, and then substituted into on subsequent calls
	// Currently only tested for the orthogonal case.
	
        LPolynomialSplit,

	LPolynomialNonSplit;

/* constructors */

// At the moment we only allow the inner form to be given by an integral
// matrix. However, there seems to be no reason for that.

intrinsic AlgebraicModularForms(G::GrpRed,
			        weight::GrpRep,
				level::AlgMatElt[Rng] :
				GramFactor := 2) -> ModFrmAlg
{Builds the space of algebraic modular forms with respect to the reductive group G, representation weight and level given by the stabilizer of the lattice whose basis consists of the rows of the matrix.
    If GramFactor is 1, we assume that the bilinear pairing on the lattice is given by the inner form of G, namely M[i,i] = Q(e_i).
    If it is 2 (by default), we assume that the inner form is twice the bilinear pairing, explicitly M[i,i] = 2Q(e_i)}

  K := SplittingField(G);
  V := AmbientReflexiveSpace((2/GramFactor) * InnerForm(InnerForm(G,1)));
  return AlgebraicModularForms(G, weight,
			       LatticeWithBasis(V, ChangeRing(level, K))
			       : GramFactor := GramFactor);
end intrinsic;

intrinsic AlgebraicModularForms(G::GrpRed,
			        weight::GrpRep,
				level::ModDedLat :
				GramFactor := 2) -> ModFrmAlg
{Builds the space of algebraic modular forms with respect to the reductive group G, representation weight and level given by the stabilizer of the lattice whose basis consists of the rows of the matrix.
    If GramFactor is 1, we assume that the bilinear pairing on the lattice is given by the inner form of G, namely M[i,i] = Q(e_i).
    If it is 2 (by default), we assume that the inner form is twice the bilinear pairing, explicitly M[i,i] = 2Q(e_i)}

        require IsCompact(G) : "Group must be compact at infinity.";
        K := SplittingField(G);
        require IsField(K) : "Reductive group must be defined over a field.";
	// !!! TODO : eventually want them to be the same
	// G eq weight`G. For that needs to be able to build
	// representations of GrpRed
	require(Dimension(G) eq Degree(weight`G)) :
				"Weight must be a representation of the group.";
        if " " in CartanName(G) then
	  error "Groups of type %o are not supported.\n", CartanName(G);
        end if;

        cartanType := CartanName(G)[1];

        V := AmbientReflexiveSpace((2/GramFactor) * InnerForm(InnerForm(G,1)));

	// Build the lattice from the level
//	L := LatticeWithBasis(V, ChangeRing(level, K));
        L := level;

	// Initialize the space of algebraic modular forms.
	M := New(ModFrmAlg);

        dim := Dimension(L);
        M`K := K;
        M`G := G;
        M`L := L;
	M`W := weight;

	// Assign the Hecke module for this instance.
	M`Hecke := New(ModHecke);
	M`Hecke`Ts := AssociativeArray();

	return M;
end intrinsic;

intrinsic AlgebraicModularForms(G::GrpRed,
			        weight::GrpRep) -> ModFrmAlg
{ Builds the space of algebraic modular forms with respect to the reductive group G and representation weight.}

        require IsCompact(G) : "Group must be compact at infinity.";
        K := SplittingField(G);
        require IsField(K) : "Reductive group must be defined over a field.";

        if " " in CartanName(G) then
	  error "Groups of type %o are not supported.\n", CartanName(G);
        end if;

        cartanType := CartanName(G)[1];

	V := InnerForm(G,1);

	// Retrieve the standard lattice for this reflexive space.
	// L := StandardLattice(V);

	// Here we set the level to a maximal level
	L := MaximalIntegralLattice(V);

	// Initialize the space of algebraic modular forms.
	M := New(ModFrmAlg);

        dim := Dimension(L);
        M`K := K;
        M`G := G;
        M`L := L;
	M`W := weight;

	// Assign the Hecke module for this instance.
	M`Hecke := New(ModHecke);
	M`Hecke`Ts := AssociativeArray();

	return M;
end intrinsic;

intrinsic AlgebraicModularForms(G::GrpRed) -> ModFrmAlg
{.}
  K := SplittingField(G); // wants G to be a subgroup of GL(n,K)
  n := Dimension(G);
  weight := TrivialRepresentation(GL(n, K), K);
  return AlgebraicModularForms(G, weight);
end intrinsic;

function normalizeField(R)
    K := AbsoluteField(FieldOfFractions(R));

    return K;
end function;

intrinsic OrthogonalModularForms(lat::Lat : 
				 weight := [0],
				 Special := false) -> ModFrmAlg
{Create the space of orthogonal modular forms with respect to the lattice lat.}
  Q := InnerProductMatrix(lat);
  level := BasisMatrix(lat);
  if Special then
    G := SpecialOrthogonalGroup(Q);
  else
    G := OrthogonalGroup(Q);
  end if;
  W := HighestWeightRepresentation(G, weight);
  return AlgebraicModularForms(G, W, Matrix(level));
end intrinsic;

intrinsic OrthogonalModularForms(innerForm::AlgMatElt[Rng],
				 weight::SeqEnum
				 : Special := false) -> ModFrmAlg
{Create the space of modular forms with respect to the orthogonal group stabilizing the quadratic form given by innerForm.}
  K := normalizeField(BaseRing(innerForm));
  n := Nrows(innerForm);
  if Special then
    G := SpecialOrthogonalGroup(ChangeRing(innerForm, K));
  else
    G := OrthogonalGroup(ChangeRing(innerForm, K));
  end if;
  W := HighestWeightRepresentation(G, weight);
  return AlgebraicModularForms(G, W);
end intrinsic;

intrinsic OrthogonalModularForms(innerForm::AlgMatElt[Rng],
				 weight::GrpRep : Special := false) -> ModFrmAlg
{Create the space of modular forms with respect to the orthogonal group stabilizing the quadratic form given by innerForm.}

  K := normalizeField(BaseRing(innerForm));
  n := Nrows(innerForm);
  if Special then
    G := SpecialOrthogonalGroup(ChangeRing(innerForm, K));
  else
    G := OrthogonalGroup(ChangeRing(innerForm, K));
  end if;
  return AlgebraicModularForms(G, weight);
end intrinsic;

intrinsic OrthogonalModularForms(innerForm::AlgMatElt[Rng] :
				 Special := false) -> ModFrmAlg
{.}
  K := normalizeField(BaseRing(innerForm));
  n := Nrows(innerForm);
  W := TrivialRepresentation(GL(n,K),K);
  return OrthogonalModularForms(ChangeRing(innerForm,K), W :
				Special := Special);
end intrinsic;

intrinsic UnitaryModularForms(innerForm::AlgMatElt[Rng],
			      weight::GrpRep) -> ModFrmAlg
{Create the space of modular forms with respect to the unitary group stabilizing the Hermitian form given by innerForm.}
  K := normalizeField(BaseRing(innerForm));
  
  U_n := UnitaryGroup(ChangeRing(innerForm, K));
  n := Dimension(U_n);
  weight`G := GL(n,K);
  return AlgebraicModularForms(U_n, weight);
end intrinsic;

intrinsic UnitaryModularForms(innerForm::AlgMatElt[Rng]) -> ModFrmAlg
{.}
  K := normalizeField(BaseRing(innerForm));
  n := Nrows(innerForm);
  weight := TrivialRepresentation(GL(n, K), K);
  return UnitaryModularForms(innerForm, weight);
end intrinsic;

intrinsic UnitaryModularForms(F::Fld, n::RngIntElt,
					 weight::GrpRep) -> ModFrmAlg
{.}
  innerForm := IdentityMatrix(F,n);
  return UnitaryModularForms(innerForm, weight);
end intrinsic;

intrinsic UnitaryModularForms(F::Fld, n::RngIntElt) -> ModFrmAlg
{.}
  return UnitaryModularForms(IdentityMatrix(F, n));
end intrinsic;

function getWeightRep(G, weight, char, F, n)
//    F := AbsoluteField(F);
  //  if Type(F) eq FldRat then
	//F := RationalsAsNumberField();
   // end if;
    // !!! TODO - change the positive characteristic to support also orthogonal
    if char ne 0 then
      pR := Factorization(ideal<Integers(F)|char>)[1][1];
      Fq, mod_q := ResidueClassField(pR);
      if IsOrthogonal(G) then
	  lie_type := IsOdd(n) select "B" else "D";
	  lie_dim := n div 2;
      else
	  lie_type := "A";
	  lie_dim := n-1;
      end if;
      // GL_n_q := GroupOfLieType(StandardRootDatum("A",n-1), Fq);
      // G_q := GroupOfLieType(StandardRootDatum(lie_type,lie_dim), Fq);
      lie_data := Sprintf("%o%o", lie_type, lie_dim);
      // Problem : This does not construct the correct group,
      // only a subgroup. In the case of n = 4 this is even worse,
      // since the group is not simple
      G_q := GroupOfLieType(StandardRootDatum(lie_type,lie_dim), Fq);
      
      // G_q := GroupOfLieType(lie_data, Fq : Isogeny := "SC");
      V := GroupRepresentation(G_q, weight);
      /*
      innerForm := InnerForm(InnerForms(G)[1]);
      // !! TODO - support also inner forms of the unitary group
      D, T := Decompose(ChangeRing(innerForm,Fq));
      assert D eq PermutationMatrix(Fq, Reverse([1..n]));
      */
      f_desc := Sprintf("
      function foo(H)
        F := BaseRing(H);
        n := %m; 
        pR := Factorization(ideal<Integers(F)|%m>)[1][1];
        Fq, mod_q := ResidueClassField(pR);
        f := map< H -> GL(n,Fq) |
		  x :-> projLocalization(x, mod_q)>;
        return f;
      end function;
      return foo;
       ", n, char);
      W := Pullback(V,f_desc, GL(n, F));
    else
      // we would love to do that but Magma does not support that...
      /*
      GL_n := GroupOfLieType(StandardRootDatum("A",n-1), F);
      W := GroupRepresentation(GL_n, weight);
     */
      /*
      if &and[w eq 0 : w in weight] then
	  W := TrivialRepresentation(GL(n,F),F);
      elif n eq 3 then
	  W := getGL3HighestWeightRep(weight[1], weight[2], F); 
      else
	  error "at the moment we have not implemented highest weight representations of this type";
      end if;
      */
      W := HighestWeightRepresentation(G, weight);
    end if;
    return W;
end function;

intrinsic UnitaryModularForms(F::Fld,
			n::RngIntElt,
			weight::SeqEnum[RngIntElt],
			char::RngIntElt) -> ModFrmAlg
{.}
  F := normalizeField(F);
  G := UnitaryGroup(IdentityMatrix(F, n));
  W := getWeightRep(G,weight, char, F, n);
  return UnitaryModularForms(F, n, W);
end intrinsic;

intrinsic UnitaryModularForms(F::Fld,
			innerForm::AlgMatElt[Rng],
			weight::SeqEnum[RngIntElt],
			char::RngIntElt) -> ModFrmAlg
{.}
  F := normalizeField(F);
  n := Degree(Parent(innerForm));
  G := UnitaryGroup(ChangeRing(innerForm, F));
  W := getWeightRep(G, weight, char, F, n);
  return AlgebraicModularForms(G, W);
end intrinsic;

intrinsic OrthogonalModularForms(F::Fld,
				 innerForm::AlgMatElt[Rng],
				 weight::SeqEnum[RngIntElt],
				 char::RngIntElt
				 : Special := false, d := 1) -> ModFrmAlg
{.}
  F := normalizeField(F);
  n := Degree(Parent(innerForm));
  if Special then
    G := SpecialOrthogonalGroup(ChangeRing(innerForm,F));
  else
    G := OrthogonalGroup(ChangeRing(innerForm,F));
  end if;
  W := getWeightRep(G, weight, char, F, n);
  if (d ne 1) then
    W := TensorProduct(W, SpinorNormRepresentation(G, d));
  end if;
  return AlgebraicModularForms(G, W);
end intrinsic;
// Should also think how to get the isogeny in general,
// and how it should affect calculations

intrinsic Print(M::ModFrmAlg, level::MonStgElt) {}
	K := BaseRing(InnerForm(M));
	printf "Space of algebraic modular forms on %o", M`G;
        if level eq "Maximal" then
	  printf "Inner form:\n%o\n", InnerForm(M);
        end if;
        R := BaseRing(M`W);
        if IsTrivial(M`W) then
	  weight := Sprintf("trivial weight");
	else
          weight := "weight ";
          if Type(R) eq FldOrd then 
            R := NumberField(MaximalOrder(R));
          end if;
// Right now we want to distinguish QQ from QNF
//R := (Degree(R) eq 1) select Rationals() else R;
          weight cat:= (assigned M`W`lambda) select Sprintf("%o", M`W`lambda)
        	       else Sprintf("%o-dimensional vector space over %o",
			     Dimension(M`W), R);
        end if;
        printf " of %o and level %o", weight, M`L;
end intrinsic;

intrinsic IsSpecialOrthogonal(M::ModFrmAlg) -> BoolElt
{ Determines whether this space is of special orthogonal type. }
	return IsSpecialOrthogonal(M`G);
end intrinsic;

intrinsic IsOrthogonal(M::ModFrmAlg) -> BoolElt
{ Determines whether this space is of orthogonal type. }
	return IsOrthogonal(M`G);
end intrinsic;

intrinsic Module(M::ModFrmAlg) -> ModDedLat
{ Returns the underlying module used to generate this space. }
	return M`L;
end intrinsic;

intrinsic Level(M::ModFrmAlg) -> ModDedLat
{ Returns the lattice such that the level is the stabilizer of this lattice. }
	return M`L;
end intrinsic;

intrinsic BaseRing(M::ModFrmAlg) -> FldOrd
{ The base ring of the space of algebraic modular forms. }
      return M`K;
end intrinsic;

intrinsic InnerForm(M::ModFrmAlg) -> AlgMatElt
{ Returns the inner form associated with the space of algebraic modular forms.}
     return InnerForm(ReflexiveSpace(Module(M)));
end intrinsic;

intrinsic Genus(M::ModFrmAlg : BeCareful := false, Orbits := true) -> GenusSym
{ Returns the genus associated to the underlying module used to construct
  this space. }
	// If already computed, return it.
	if assigned M`genus then return M`genus; end if;

	// Otherwise, compute the genus and return it.
	   _ := GenusReps(M : BeCareful := BeCareful, Orbits := Orbits);
	     
	return M`genus;
end intrinsic;

/*
function special_subgroup(gamma)
    F := BaseRing(gamma);
    C2 := sub<GL(1, F) | [-1]>;
    h := hom<gamma -> C2 | [C2![Determinant(gamma.i)] : i in [1..Ngens(gamma)]]>;
    return Kernel(h); 
end function;
*/

intrinsic SetAutomorphismGroups(~M::ModFrmAlg, autgps::SeqEnum[GrpMat]
				: BeCareful := false)
{Set the automorphism groups of the lattices in the genus of M.}
  reps := Representatives(Genus(M));
  // Set the automorphism groups of the lattices as an attribute,
  // to remember for later
  for i in [1..#reps] do
     reps[i]`AutomorphismGroup := autgps[i];
  end for;
//  gamma_reps := autgps;
  assert IsIsomorphic(BaseRing(AmbientSpace(reps[1])),
			    BaseRing(M`W`G));

  //gamma_reps := [AutomorphismGroup(r : Special := IsSpecialOrthogonal(M))
  //		: r in reps];
  /*
  gammas := [sub<M`W`G|
		[Transpose(PullUp(Matrix(g), reps[i], reps[i] :
				  BeCareful := BeCareful)) :
		 //			  g in Generators(gamma_reps[i])]> :
		 g in Generators(autgps[i])]> :
	    i in [1..#reps]];

  if IsSpecialOrthogonal(M) then
      gammas := [special_subgroup(gamma) : gamma in gammas];
  end if;
 */
  gammas := [AutomorphismGroupOverField(r : Special := IsSpecialOrthogonal(M)) : r in reps];
  if GetVerbose("AlgebraicModularForms") ge 2 then
     printf "The sizes of the automorphism groups are %o.\n",
		   [#x : x in gammas];
     printf "Computing the fixed subspaces ";
     print "(space of algebraic modular forms)";
     t0 := Cputime();
  end if;
    
  M`H := [FixedSubspace(gamma, M`W) : gamma in gammas];
  dims := Sort([<Dimension(M`H[idx]), -#gammas[idx], idx> : idx in [1..#M`H]]);
  perm := [tup[3] : tup in dims];
  perm_inv := [Index(perm,i) : i in [1..#M`H]];
  // now these are in ascending order
  M`H := [M`H[i] : i in perm];
  // Have to reorder the genus representatives to match
  M`genus`Representatives := [M`genus`Representatives[i] :
				 i in perm];
  for inv in Keys(M`genus`RepresentativesAssoc) do
    M`genus`RepresentativesAssoc[inv] :=
	    [<tup[1], perm_inv[tup[2]]> :
		   tup in M`genus`RepresentativesAssoc[inv] ];
  end for;
end intrinsic;

// !!! TODO - make Orbits and LowMemory meaningful here

procedure ModFrmAlgInit(M : BeCareful := false, Orbits := true,
			LowMemory := false)
    
    // If the representation space has already been computed, then this
    //  object has already been initialized, and we can simply return
    //  without any further computations.

    if not assigned M`H then

	if GetVerbose("AlgebraicModularForms") ge 1 then
	    print "Computing genus representatives...";
	end if;

        reps := Representatives(Genus(M : BeCareful := BeCareful,
				      Orbits := Orbits));

	if GetVerbose("AlgebraicModularForms") ge 1 then
	    printf "Found %o genus representatives.\n", #reps;
	    print "Calculating the automorphism groups Gamma_i...";
	end if;

	// !!! TODO : treat the special unitary case
	
	gamma_reps := [AutomorphismGroup(r) : r in reps];
        SetAutomorphismGroups(~M, gamma_reps : BeCareful := BeCareful);
    end if;
end procedure;

intrinsic Dimension(M::ModFrmAlg) -> RngIntElt
{ Returns the dimension of this vector space. }
	// Initialize this space of modular forms.
	ModFrmAlgInit(M);

	return &+[Dimension(h) : h in M`H];
end intrinsic;

intrinsic CuspidalSubspace(M::ModFrmAlg) -> ModMatFldElt
{ Computes the cuspidal subspace of M. }
	// Initialize the space of algebraic modular forms.
	ModFrmAlgInit(M);

        // for a non-trivial representation, everything is cuspidal
        if not IsTrivial(M`W) or Dimension(M) eq 0 then
	    return VectorSpace(M);
	end if;

        // Retrieve the Eisenstein series.
	eis := EisensteinSeries(M);

	// The dimension of the space.
	// dim := #GenusReps(M);
	dim := Dimension(M);

	reps := Representatives(Genus(M));
	// !!! TODO :
	// Replace this by an actual bilinear form compatible with the group
	// Add handling the case when the narrow class group of the field
	// is nontrivial.
	wts := &cat[[#AutomorphismGroupOverField(reps[i] : Special := IsSpecialOrthogonal(M))
		     : j in [1..Dimension(M`H[i])]]: i in [1..#reps]];
	// instead of dividing by wts[i], we multiply for the case of positive
	// characteristic
        wt_prod := IsEmpty(wts) select 1 else &*wts;
	mult_wts := [wt_prod div wt : wt in wts];

	F := BaseRing(M`W);
	
	// Initialize the Hermitian inner product space in which the Hecke
	//  operators are self-adjoint.
	gram := ChangeRing(DiagonalMatrix(mult_wts), F);

	// vectors orthogonal to the Eisenstein series
	cuspBasis := Basis(Kernel(Transpose(Matrix(eis`vec*gram))));
	/*
	// The change-of-basis matrix.
	basis := Id(MatrixRing(F, dim));

	// Make the Eisenstein series the first basis vector.
	for i in [2..dim] do
		AddColumn(~gram, eis`vec[i], i, 1);
		AddRow(~gram, eis`vec[i], i, 1);
		AddRow(~basis, eis`vec[i], i, 1);
	end for;

	// Orthogonalize with respect to the Eisenstein series.
	for i in [2..dim] do
		scalar := -gram[1,i] / gram[1,1];
		AddColumn(~gram, scalar, 1, i);
		AddRow(~gram, scalar, 1, i);
		AddRow(~basis, scalar, 1, i);
	end for;

	// The normalized cuspidal basis.
	cuspBasis := [];

	// Normalize the basis vectors of the cuspidal subspace.
	for i in [2..dim] do
		// Retrieve the cuspical vector.
		vec := basis[i];

		// Find its pivot.
		pivot := 0; repeat pivot +:= 1; until vec[pivot] ne 0;

		// Normalize the vector add it to the list.
		Append(~cuspBasis, vec[pivot]^-1 * vec);
	end for;

	if IsEmpty(cuspBasis) then
	    return VectorSpace(F, 0);
	end if;
	
	// Reduce the cuspidal basis to be as sparse as possible.
	cuspBasis := EchelonForm(Matrix(cuspBasis));
	*/
	return VectorSpaceWithBasis(cuspBasis);
end intrinsic;

// TODO: Make this more general.
intrinsic CuspidalHeckeOperator(M::ModFrmAlg, p::RngIntElt) -> AlgMatElt
{ Computes the Hecke operator restricted to the cuspidal subspace. }
	// The Hecke operator at this prime.
	T := ChangeRing(HeckeOperator(M, p), Rationals());

	// The cuspidal subspace.
	C := CuspidalSubspace(M);

	// The restriction of the Hecke operator to the cuspidal subspace.
	T := Solution(C, Transpose(T * Transpose(C)));
	return T;
end intrinsic;

intrinsic 'eq'(M1::ModFrmAlg, M2::ModFrmAlg) -> BoolElt
{.}
  K1 := BaseRing(M1);
  K2 := BaseRing(M2);
  if Type(K1) eq FldRat or Type(K2) eq FldRat then
    isom_fields := IsIsomorphic(K1, K2);
    psi := hom<K1 -> K2 | >;
  else
    isom_fields, psi := IsIsomorphic(K1, K2);
  end if;
  if not isom_fields then return false; end if;
  // Checking the groups
  K_G1 := SplittingField(M1`G);
  K_G2 := SplittingField(M2`G);
  if Type(K_G1) eq FldRat or Type(K_G2) eq FldRat then
    isom_G := IsIsomorphic(K_G1,K_G2);
    psi_G := hom<K_G1 -> K_G2 | >;
  else
    isom_G, psi_G := IsIsomorphic(K_G1,K_G2);
  end if;
  if not isom_G then return false; end if;
  // !!! TODO : change this to check the entire G, and not just G0
  if not (ChangeRing(M1`G`G0, DefinitionField(M2`G)) eq M2`G`G0) then
      return false;
  end if;
  if not (ChangeRing(M1`W, BaseRing(M2`W)) eq M2`W) then return false; end if;
  keys := Keys(M1`Hecke`Ts);
  if keys ne Keys(M2`Hecke`Ts) then return false; end if;
  for k in keys do
      primes1 := [p : p in Keys(M1`Hecke`Ts[k])];
      // We have to convert to ideals in K2,
      // otherwise magma doesn't like it
      primes2 := [ideal<Integers(K2)|[psi(K1!x) : x in Generators(p)]> :
		  p in primes1];
      hecke_keys := {p : p in Keys(M2`Hecke`Ts[k])};
      if Type(K2) ne FldRat then
        primes2 := [K2!!p : p in primes2];
        hecke_keys := {K2!!p : p in hecke_keys};
      end if;
      if Set(primes2) ne hecke_keys then return false; end if;
      for idx in [1..#primes1] do
	  p1 := primes1[idx];
	  p2 := primes2[idx];
	  if ChangeRing(M1`Hecke`Ts[k][p1], BaseRing(M2`W)) ne
	     M2`Hecke`Ts[k][p2] then
	      return false;
	  end if;
      end for;
  end for;
  if assigned M1`Hecke`Eigenforms then
      if not assigned M2`Hecke`Eigenforms then
	  return false;
      end if;
      if M1`Hecke`Eigenforms ne M2`Hecke`Eigenforms then
	  return false;
      end if;
  end if;
  return true;
end intrinsic;

intrinsic Representation(M::ModFrmAlg) -> ModTupFld
{.}
  dim := Dimension(M);
  if dim eq 0 then return VectorSpace(BaseRing(M), 0); end if;
  return VectorSpace(BaseRing(M`H[1]), dim);
end intrinsic;

intrinsic VectorSpace(M::ModFrmAlg) -> ModTupFld
{.}
  return Representation(M);
end intrinsic;

intrinsic Weight(M::ModFrmAlg) -> GrpRep
{The representation which serves at the weight of M.}
  return M`W;
end intrinsic;

//freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: modfrmalg.m (Class of space of algebraic modular forms)

   Implementation file for the space of algebraic modular forms.

   03/11/20: Added constructor for Unitary Modular Forms from an inner form

   03/10/20: Discarded irrelevant imports.
             Moved here the type declaration.
	     Modified to use always the reflexive space implementation.

   03/05/20: Removed most initialization functions, leaving a single one which 
   receives group of lie type as argument.

   02/28/20: started editing this file to add Unitary forms
 
 ***************************************************************************/

// imports

import "../neighbors/genus-CN1.m" : computeGenusRepsCN1;

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

	// Isogeny type.
	isogenyType,

	// The inner form as a lattice.
	L,

	// Hecke data structure.
	Hecke,

	// The genus symbol for this lattice.
	genus,

	// The filename from which this space was loaded.
	filename;

/* constructors */

// At the moment we only allow the inner form to be given by an integral
// matrix. However, there seems to be no reason for that.

intrinsic AlgebraicModularForms(G::GrpLie,
				innerForm::AlgMatElt[Rng]) -> ModFrmAlg
{ Builds the space of algebraic modular forms with respect to the Lie group G, with inner form given by the isometry class of a specific matrix.}
	// The rationals as a number field.
       

        K := BaseRing(G);
        require IsField(K) : "Lie group must be defined over a field";
        K := AbsoluteField(K);
        if Type(K) eq FldRat then
           K := RationalsAsNumberField();
        end if;
	// The integers as a maximal order.
	R := Integers(K);

	// Coerce the inner form into coefficients of the maximal order.
	innerForm := ChangeRing(innerForm, R);

        if " " in CartanName(G) then
	  error "Groups of type %o are not supported.\n", CartanName(G);
        end if;

        cartanType := CartanName(G)[1];

        if cartanType in ["B", "D"] then
           isogenyType := "O";
           V := AmbientReflexiveSpace(innerForm);
	else if cartanType eq "A" then
	   require not IsSplit(G) : "Group is not compact.";
	   _, cc := HasComplexConjugate(K);
           cc := FieldAutomorphism(K, cc);
           isogenyType := "U";
           V := AmbientReflexiveSpace(innerForm, cc);
        else
	  error "Groups of type %o are not supported.\n", cartanType;
        end if;
        end if;

	// Retrieve the standard lattice for this reflexive space.
	L := StandardLattice(V);

        if IsSemisimple(G) then
           isogenyType := "S" cat isogenyType;
        end if;

        // !!! Remember to change the name of this parameter - these are not
        // isogeny types in general !
	// Make sure the isogeny type is valid.
        require isogenyType in [ "SO", "O" , "SU", "U"]:
		"Isogeny type must be (O)rthogonal or (S)pecial (O)rthogonal.";

	// Initialize the space of algebraic modular forms.
	M := New(ModFrmAlg);

        dim := Dimension(L);
        M`K := K;
        M`G := G;
        M`L := L;

	// Assign the isogeny type of the Lie group.
	M`isogenyType := isogenyType;

	// Assign the Hecke module for this instance.
	M`Hecke := New(ModHecke);
	M`Hecke`Ts := AssociativeArray();

	return M;
end intrinsic;

intrinsic AlgebraicModularForms(G::GrpLie,
				innerForm::AlgMatElt[Fld]) -> ModFrmAlg
{ Builds the space of algebraic modular forms with respect to the Lie group G, with inner form given by the isometry class of a specific matrix. }
        K := BaseRing(G);
        require IsField(K) : "Lie group must be defined over a field";

	// The integers as a maximal order.
	R := Integers(K);
	try
		// Attempt to coerce the inner form to the maximal order.
	  innerForm := ChangeRing(Denominator(innerForm)*innerForm, R);
	catch e
		require false: "Inner form must be given by a matrix over the 
                                same field as the Lie group";
	end try;

        return AlgebraicModularForms(G, innerForm);
end intrinsic;

intrinsic UnitaryModularForms(innerForm::AlgMatElt[Fld]) -> ModFrmAlg
{.}
  K := BaseRing(innerForm);
  _, cc := HasComplexConjugate(K);
  alpha := FieldAutomorphism(K, cc);
  F := FixedField(alpha);

  SL3 := GroupOfLieType("A2", K);
  A := AutomorphismGroup(SL3);
  AGRP := GammaGroup(F, A);
  grph_auts := [GraphAutomorphism(SL3, x) : x in [Sym(2) | 1, (1,2)]];
  ngens := NumberOfGenerators(AGRP`Gamma);
  c := OneCocycle( AGRP, [grph_auts[Order(AGRP`Gamma.i)] : i in [1..ngens]]);

  SU3 := TwistedGroupOfLieType(c);

  // This is hardly the right thing to do,
  // but I still don't know how to construct U_{n} as a group of Lie type (!?)
  // Instead, we just construct SU_3,
  // using the fact that the code at the moment does the same for both.

  return AlgebraicModularForms(SU3, innerForm);
end intrinsic;

// Should replace weight by Map[GrpLie, GrpMat]
// or something similar

// Should also think how to get the isogeny in general,
// and how it should affect calculations

intrinsic Print(M::ModFrmAlg) {}
	K := BaseRing(InnerForm(M));
	printf "Space of algebraic modular forms over %o.\n", M`G;
	printf "Inner form:\n%o", InnerForm(M);
end intrinsic;

intrinsic IsogenyType(M::ModFrmAlg) -> MonStgElt
{ Returns the isogeny type of this space. }
	return M`isogenyType;
end intrinsic;

intrinsic IsSpecialOrthogonal(M::ModFrmAlg) -> BoolElt
{ Determines whether this space is of special orthogonal type. }
	return IsogenyType(M) eq "SO";
end intrinsic;

intrinsic IsOrthogonal(M::ModFrmAlg) -> BoolElt
{ Determines whether this space is of orthogonal type. }
	return IsogenyType(M) eq "O";
end intrinsic;

intrinsic Module(M::ModFrmAlg) -> ModDedLat
{ Returns the underlying module used to generate this space. }
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

intrinsic Genus(M::ModFrmAlg : BeCareful := true, Orbits := false) -> GenusSym
{ Returns the genus associated to the underlying module used to construct
  this space. }
	// If already computed, return it.
	if assigned M`genus then return M`genus; end if;

	// Otherwise, compute the genus and return it.
	   _ := GenusReps(M : BeCareful := BeCareful, Orbits := Orbits);
	     
	return M`genus;
end intrinsic;

procedure ModFrmAlgInit(M : BeCareful := true, Force := false, Orbits := false)
	// If the representation space has already been computed, then this
	//  object has already been initialized, and we can simply return
	//  without any further computations.
	if assigned M`W then return; end if;

        computeGenusRepsCN1(M : BeCareful := BeCareful, Force := Force);

end procedure;

intrinsic Dimension(M::ModFrmAlg) -> RngIntElt
{ Returns the dimension of this vector space. }
	// Initialize this space of modular forms.
	ModFrmAlgInit(M);

	return #Representatives(Genus(M));
end intrinsic;

intrinsic HeckeEigenforms(M::ModFrmAlg) -> List
{ Returns a list of cusp forms associated to this space. }
	// Initialize space of modular forms if needed.
	ModFrmAlgInit(M);	

	// Display an error if no Hecke matrices have been computed yet.
	require IsDefined(M`Hecke`Ts, 1): "Compute some Hecke matrices first!";

	// Decompose eigenspace.
	spaces, reducible :=
		EigenspaceDecomposition(M`Hecke`Ts[1] : Warning := false);

	// A list of cusp forms.
	cuspForms := [* *];

	for space in spaces do
		// Extract the first basis vector of the eigenspace.
		basis := Basis(space);

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
			mform`IsEigenform := #basis eq 1;

			// Add to list.
			Append(~cuspForms, mform);
		end for;
	end for;

	return cuspForms;
end intrinsic;

intrinsic CuspidalSubspace(M::ModFrmAlg) -> ModMatFldElt
{ Computes the cuspidal subspace of M. }
	// Initialize the space of algebraic modular forms.
	ModFrmAlgInit(M);

	// Retrieve the Eisenstein series.
	eis := EisensteinSeries(M);

	// The dimension of the space.
	dim := #GenusReps(M);

	// Compute the sizes of the automorphism groups of each of the genus
	//  representatives.
	aut := [ #AutomorphismGroup(L) : L in Representatives(Genus(M)) ];

	// Initialize the Hermitian inner product space in which the Hecke
	//  operators are self-adjoint.
	gram := ChangeRing(DiagonalMatrix(aut), Rationals());

	// The change-of-basis matrix.
	basis := Id(MatrixRing(Rationals(), dim));

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

	// Reduce the cuspidal basis to be as sparse as possible.
	cuspBasis := EchelonForm(Matrix(cuspBasis));

	return cuspBasis;
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


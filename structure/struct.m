//freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: struct.m (main structure file)

   Declaration file for the space of algebraic modular forms.

   02/28/20: started from the orthogonal modular forms structure
 
 ***************************************************************************/


///////////////////////////////////////////////////////////////////
//                                                               //
//    ModFrmAlg: The algebraic modular forms object.             //
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

declare type ModHecke;
declare attributes ModHecke:
	// A list of Hecke matrices.
	Ts,

	// Hecke Eigenforms.
	Eigenforms,

	// A shortcut to the Eisenstein series.
	EisensteinSeries;

declare type GenusSym;
declare attributes GenusSym:
	// The lattice for which this genus symbol was initialized.
	Representative,

	// Representatives for the classes in this genus.
	Representatives,

	// A partition of the genus representatives.
	RepresentativesAssoc,

	// An ordered list of theta series for the genus representatives
	ThetaSeries;

declare type QuadSpace;
declare attributes QuadSpace:
	// The base field.
	F,

	// The base number ring.
	R,

	// The degree of the field extension.
	deg,

	// Class number of the field extension.
	classNo,

	// The inner form.
	innerForm,

	// The quadratic space as a vector space.
	V,

	// The quadratic form as a multinomial.
	Q,

	// The dimension.
	dim,

	// The quaternion algebras associated to this space (ternary only).
	QuaternionAlgebra,

	// Whether the form is definite or not.
	Definite,

	// The diagonalized Gram matrix over the field of fractions.
	Diagonal,

	// The basis for the diagonalized Gram matrix.
	DiagonalBasis,

	// The standard lattice for this quadratic space.
	stdLat;

declare type QuadSpaceAff;
declare attributes QuadSpaceAff:
	// The quadratic space.
	V,

	// The prime ideal.
	pR,

	// A uniformizing element of pR.
	pElt,

	// The finite field.
	F,

	// The characteristic.
	ch,

	// The quotient modulo pR^2.
	quot,

	// The projection map modulo pR.
	proj_pR,

	// The projection map modulo pR^2.
	proj_pR2,

	// Gram matrix modulo pR^2.
	quotGram,

	// The quadratic form modulo pR^2.
	Q_pR2;

declare type ModDedLat;
declare attributes ModDedLat:
	// The lattice.
	Module,

	// The base ring.
	R,

	// The base field.
	F,

	// The pseudobasis (only used when not over the rationals).
	psBasis,

	// The ambient quadratic space.
	quadSpace,

	// The discriminant ideal.
	Discriminant,

	// The p-maximal basis is not strictly-speaking a basis for the lattice,
	//  but instead a basis for the completed lattice at p. This is used to
	//  compute the affine quadratic space and thereby compute isotropic
	//  lines, etc.
	pMaximal,

	// The lattice pushed down to the integers. This is the same as L if
	//  and only if the base field is the rationals.
	ZLattice,

	// The automorphism group as a lattice over Z.
	AutomorphismGroup,

	// The scale of the lattice.
	Scale,

	// The norm of the lattice.
	Norm,

	// The level of the lattice.
	Level,

	// An associative array storing quadratic spaces modulo primes.
	Vpp,

	// Jordan decomposition of the lattice at a prime.
	Jordan,

	// The spinor norms as specified prime ideals.
	SpinorNorm;

declare attributes Lat:
	// The auxiliary forms associated to this lattice.
	auxForms,

	// The basis of the lattice with coefficients in R.
	basisR,

	// The basis of the lattice with coefficients in Z.
	basisZ,

	// An associative array storing quadratic spaces modulo primes
	Vpp;

declare type NeighborProc;
declare attributes NeighborProc:
	// The lattice.
	L,

	// The prime ideal.
	pR,

	// The norm of this prime.
	pRnorm,

	// The quadratic space over the residue class field.
	VFF,

	// The current isotropic subspace.
	isoSubspace,

	// The dimension of the isotropic subspaces.
	k,

	// Skew vector. This is used to "twist" the isotropic lifts when
	//  computing neighbor lattices when k gt 1.
	skew,

	// Skew dimension.
	skewDim,

	// The current (unaltered) p^2-isotropic lift we're looking at.
	X,

	// The current p^2-isotropic lift we're looking at.
	X_skew,

	// The current hyperbolic complement of X and X_skew.
	Z,

	// The space orthogonal to X+Z modulo p^2.
	U;

declare attributes ModTupFld:
	// The Witt index of the form. This is defined to be the number of
	//  hyperbolic planes in the Witt decomposition of the quadratic form.
	WittIndex,

	// The Gram matrix of the form. In characteristic 2, this is not a
	//  Gram matrix, since the diagonal entries may be nonzero.
	GramMatrix,

	// The standardized Gram matrix, isometric to the GramMatrix attribute.
	//  This is the Witt decomposition of the form:
	//    Hyperbolic + Ansiotropic + Radical.
	// In characteristic 2, this is not a gram matrix, as the diagonal
	//  entries may be nonzero.
	GramMatrixStd,

	// The basis which connects GramMatrix with GramMatrixStd such that
	//  GramMatrixStd eq Transpose(Basis) * GramMatrix * Basis
	// In characteristic 2, the diagonal entries of GramMatrixStd and
	//  GramMatrix must first be zeroed out for the above identity to be
	//  valid.
	Basis,

	// The original quadratic form associated to GramMatrix.
	Q,

	// The standardized quadratic form associated to GramMatrixStd.
	QStd,

	// The dimension of the anisotropic subspace.
	AnisoDim,

	// The dimension of the radical.
	RadDim,

	// Stores a list of entries that keep track of the current state of any
	//  isotropic subspaces being enumerated for this quadratic space.
	ParamArray,

	// Ordering of the elements in the finite field.
	S,

	// A flag used to determine whether we will use symbolic vectors.
	Symbolic,

	// The primitive element of the finite field.
	PrimitiveElement;

declare type IsoParam;
declare attributes IsoParam:
	// A list of valid pivots.
	Pivots,

	// A pointer to the current pivot.
	PivotPtr,

	// The free variables that parameterize the isotropic subspaces with
	//  respect to our current pivot.
	FreeVars,

	// The parameters for the free variables for the current pivot.
	Params,

	// A matrix whose rows correspond to the parameterized isotropic
	//  subspaces.
	IsotropicParam;


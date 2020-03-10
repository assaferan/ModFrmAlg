//freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: genus.m (class for all genus related data and computations)

   03/10/20: started from the orthogonal modular forms structure
 
 ***************************************************************************/

// imports

import "modfrmalg.m" : ModFrmAlgInit;

///////////////////////////////////////////////////////////////////
//                                                               //
//    GenusSym: The genus symbol object.                         //
//                                                               //
///////////////////////////////////////////////////////////////////


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

// printing

intrinsic Print(gen::GenusSym) {}
	printf "Genus symbol of size %o.", #gen`Representatives;
end intrinsic;

// access

intrinsic GenusReps(M::ModFrmAlg
	: BeCareful := true, Force := false, Orbits := false) -> SeqEnum
{ Computes the genus representatives of the inner form associated to the
space of algebraic modular forms provided. }
	// Initialize the space of algebraic modular forms so we can query the
	//  genus representatives.
	ModFrmAlgInit(M
		: BeCareful := BeCareful, Force := Force, Orbits := Orbits);

	return M`genus`Representatives;
end intrinsic;

intrinsic Representative(G::GenusSym) -> .
{ Return the lattice used to construct this genus symbol. }
	return G`Representative;
end intrinsic;

intrinsic Representatives(G::GenusSym) -> SeqEnum
{ Return all lattices in the genus. }
	return G`Representatives;
end intrinsic;

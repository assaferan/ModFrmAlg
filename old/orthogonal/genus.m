// All genus-related computations.

import "../structure/modfrmalg.m" : ModFrmAlgInit;
import "neighbor.m" : BuildNeighborProc, BuildNeighbor, GetNextNeighbor;

intrinsic Print(gen::GenusSym) {}
	printf "Genus symbol of size %o.", #gen`Representatives;
end intrinsic;

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


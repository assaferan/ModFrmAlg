// This script computes an invariant used to sort genus representatives.

function Invariant(L)
	return ThetaSeries(ZLattice(L), 25);
end function;


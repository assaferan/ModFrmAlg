freeze;
// This script computes an invariant used to sort genus representatives.

function Invariant(L : Precision := 25)
    return ThetaSeries(ZLattice(L), Precision);
end function;


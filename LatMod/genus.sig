174,0
A,LatMod,1,GenusComp
S,deletedata,deletes genus data stored in L,0,1,0,0,1,0,0,0,0,LatMod,,-38,-38,-38,-38,-38,-38
S,DetailedJordanDecomposition,A Jordan decomposition of the completion of L at p -- more detailed output than JordanDecomposition,0,2,0,0,0,0,0,0,0,217,,0,0,LatMod,,82,-38,-38,-38,-38,-38
S,IsSquarefreeLattice,Check whether L is a squarefree lattice at the prime p,0,2,0,0,0,0,0,0,0,217,,0,0,LatMod,,36,-38,-38,-38,-38,-38
S,IsSquarefreeLatticeEverywhere,Check whether L is a squarefree lattice,0,1,0,0,0,0,0,0,0,LatMod,,36,-38,-38,-38,-38,-38
S,IsPrimitiveLattice,"Check whether L is primitiveat p, i.e., any Jordan decomposition consists of a 0-valuated component A and a 1-valuated component B, and rank(A) ge rank(B)",0,2,0,0,0,0,0,0,0,217,,0,0,LatMod,,36,-38,-38,-38,-38,-38
S,IsUnverzweigt,check whether L is unimodular at p and Norm(L) equals 2*Scale(L) at p,0,2,0,0,0,0,0,0,0,217,,0,0,LatMod,,36,-38,-38,-38,-38,-38
S,IsUnverzweigtEverywhere,"check that IsUnverzweigt(L, p) holds for every p over 2",0,1,0,0,0,0,0,0,0,LatMod,,36,-38,-38,-38,-38,-38
S,RelativeQuadraticDefect,"Returns the valuation of the relative quadratic defect of a at the prime ideal p, as defined by C. Beli",0,2,0,0,0,0,0,0,0,217,,0,0,-45,,148,-38,-38,-38,-38,-38
S,IsGoodBONG,"Returns true iff BONG is a good BONG at p, as defined by C. Beli",0,2,0,0,0,0,0,0,0,217,,0,0,82,,36,-38,-38,-38,-38,-38
S,IsMaximalNormSplitting,returns true iff the given list G of Gram matrices corresponds to a maximal norm splitting at p,0,2,0,0,0,0,0,0,0,217,,0,0,82,,36,-38,-38,-38,-38,-38
S,MaximalNormSplitting,"A maximal norm splitting of L at a dyadic prime p, as defined by C. Beli. Returns a Jordan decomposition into 1x1 and 2x2 components, and the corresponding list of basis vectors",0,2,0,0,0,0,0,0,0,217,,0,0,LatMod,,82,82,-38,-38,-38,-38
S,MakeGoodBONG,"Return a good BONG of L at a dyadic prime p, as defined by C. Beli",0,2,0,0,0,0,0,0,0,217,,0,0,LatMod,,82,-38,-38,-38,-38,-38
S,SpinorNorm,"The spinor norm of L at p, as calculated by C. Beli for dyadic p and by M. Kneser for non-dyadic p. Returns a subspace of LocalMultiplicativeGroupModSquares(p), and a boolean which is true iff the spinor norm is exactly the units",0,2,0,0,0,0,0,0,0,217,,0,0,LatMod,,159,36,-38,-38,-38,-38
S,SpinorsNotExactlyTheUnits,those places of BaseRing(L) where the Spinor norm is not exactly the units,0,1,0,0,0,0,0,0,0,LatMod,,82,-38,-38,-38,-38,-38
S,MapIdeleIntoClassGroup,"map an idele into the class group associated to L. The parameter Idele must be a list of tuples <p, a_p>, where p is a prime of BaseRing(L), and a_p is an element of K^* (interpreted as an element of the completion K^*_p). The parameter AtInfinity can be a list of tuples <v, +1 or -1>, where v is an element of InfinitePlaces(BaseRing(L)). All places, finite or infinite, which are unspecified are interpreted as 1",0,2,0,0,0,0,0,0,0,82,,0,0,LatMod,,108,-38,-38,-38,-38,-38
S,MapPrincipalIdeleIntoClassGroup,Map the principal idele defined by the element 'a' into the ray class group identified with the proper spinor genera in Genus(L),0,2,0,0,0,0,0,0,0,28,,0,0,LatMod,,108,-38,-38,-38,-38,-38
S,PrepareClassGroup,internal use,0,1,0,0,1,0,0,0,0,LatMod,,-38,-38,-38,-38,-38,-38
S,GetPrimes,A complete set of primes of BaseRing(L) needed to enumerate the genus of L,0,1,0,0,0,0,0,0,0,LatMod,,82,-38,-38,-38,-38,-38
S,IteratedNeighbours,iterated neighbours at the prime p,0,2,0,0,0,0,0,0,0,217,,0,0,LatMod,,82,-38,-38,-38,-38,-38
S,GenusRepresentatives,"A list of representatives of the isometry classes in the genus of L. Optional parameters: Max, the maximum number of isometry classes to calculate; Extra, the number of extra primes for safety",0,1,0,0,0,0,0,0,0,LatMod,,82,-38,-38,-38,-38,-38
S,IsOneClassGenus,"returns true iff #GenusRepresentatives(L) eq 1, but is much faster than calling GenusRepresentatives",0,1,0,0,0,0,0,0,0,LatMod,,36,-38,-38,-38,-38,-38

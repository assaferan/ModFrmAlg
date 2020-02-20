L := QuaternionAlgebra(2*3*5);
Z_L := MaximalOrder(L);
d := Degree(L);
n := 2;
V := RSpace(L,n);
VBasis := [x*V.i : x in Basis(L), i in [1..n]];
VQ := RSpace(Rationals(),d*n);
VZ := RSpace(Integers(),d*n);

// matrices giving scalar multiplication from L
LMultMats := [];
for i in [1..d] do
  mat := Matrix([ VQ!&cat[Eltseq(L!x) : x in Eltseq(y)] : y in 
[(Z_L.i)*v : v in VBasis]]);
  Append(~LMultMats,mat);
end for;

// standard lattice Z_L-lattice
LambdaZModuleGens := [x*V.i : x in Basis(Z_L), i in [1..n]]; 
LambdaBasisMat := Matrix([ VQ!&cat[Eltseq(L!x) : x in Eltseq(y)] : y in LambdaZModuleGens ]);
Lambda := LatticeWithBasis(LambdaBasisMat);

// take a maximal left ideal of norm p
p := 7;
P := MaximalLeftIdeals(Z_L,p)[1];

//========================================================//
// RUN FROM HERE TILL OUTPUT LATTICE RHO PASSES THE TESTS //
//========================================================//

// vector giving rise to neighbor
X := &+[Random(Z_L)*V.i : i in [1..n]];
XConj := &+[Conjugate(X[i])*V.i : i in [1..n]];

// coordinates of X with respect to the Z-module with basis matrix BasisMat
XCoords := (VQ!&cat[Eltseq(x) : x in Eltseq(X)])*LambdaBasisMat^-1;
XConjCoords := (VQ!&cat[Eltseq(x) : x in Eltseq(XConj)])*LambdaBasisMat^-1;

// sublattice of Lambda that pairs with X into P
WFp := RSpace(GF(p),d);
Pmodp := sub<WFp|[WFp!Eltseq(Z_L!x) : x in Basis(P)]>;
quo,f := WFp/Pmodp;
fMat := Matrix([f(b) : b in Basis(WFp)]);

Pairings := [&+[u[i]*XConj[i] : i in [1..n]] : u in LambdaZModuleGens];
PairingsCoordMat := Mats!Matrix([Eltseq(Z_L!x) : x in Pairings]);
N := Nullspace(PairingsCoordMat*fMat);
NLiftedBasis := Matrix([VQ!VZ!x : x in Basis(N)]);
PiGens := Rows(NLiftedBasis*LambdaBasisMat) cat Rows(p*LambdaBasisMat);
Pi := sub<Lambda|PiGens>;

//PBarInvXGens := [1/p*Conjugate(b)*X : b in Basis(P)];
PBarInvXGens := [1/p*b*X : b in Basis(P)];
PBarInvXBasisMat := Matrix([ VQ!&cat[Eltseq(L!x) : x in Eltseq(y)] : y in PBarInvXGens ]);
PBarInvX := LatticeWithBasis(PBarInvXBasisMat);
Rho := PBarInvX + Pi;

// generators for Rho as a Z-submodule of V
RhoBasisMat := BasisMatrix(Rho);
RhoZModuleGens := [&+[(L!Eltseq(v)[(i-1)*d+1..i*d])*V.i : i in [1..n]] : v in Rows(RhoBasisMat)];

// these should be isomorphic to Z/p x Z/p
Rho/(Lambda meet Rho); 
Lambda/(Lambda meet Rho);

// these should be equal
Determinant(Lambda);
Determinant(Rho);

// these should all be true
[v*m in Rho : v in Basis(Rho), m in LMultMats];



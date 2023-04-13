Attach("quatlat.m");
Attach("hackobj.m");

L := QuaternionAlgebra(2*3*5);
R := MaximalOrder(L);
n := 2;
V := RSpace(L,n);
VQ := RSpace(Rationals(),4*n);
LambdaBasis := &cat[[x*V.i : x in Basis(R)] : i in [1..n]];
Lambda := Lattice(LambdaBasis);
LambdaBasisZ := [&cat[Eltseq(x) : x in Eltseq(y)] : y in LambdaBasis];  

p := 7;
P := MaximalLeftIdeals(R,p)[1];

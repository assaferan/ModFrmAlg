intrinsic Dual(L::Lattice, M::Lattice, p::RngIntElt) -> Lattice
  {Computes the p-dual of M in L, the sublattice N of L consisting of elements x for which q(x,M) is contained in pZ.}

  Lmodp, LmodpMap := quo<L|p*L>;
  Zmodp, f := AdditiveGroup(GF(p));  
  K := Lmodp;

  for m in Basis(M) do
    images := [InnerProduct((Lmodp.i)@@LmodpMap,m) : i in [1..Ngens(Lmodp)]];
    h := hom<Lmodp -> Zmodp | images>;
    K := K meet Kernel(h);
  end for;
  
  return sub<L|[x@@LmodpMap : x in Generators(K)] cat Basis(p*L)>;

end intrinsic;



intrinsic Dual(Lambda::ModDed, Y::ModDed, P::RngOrdIdl) -> ModDed
  {Computes the P-dual of Y in Lambda, the sublattice X of Lambda consisting of elements x for which q(x,Y) is contained in P.}
  
  ZZ_L := Integers(BaseRing(Lambda));
  B := ChangeRing(InnerProductMatrix(V), FieldOfFractions(ZZ_L));
  d := Degree(ZZ_L);
  m := Dimension(Lambda);

  if not assigned Lambda`Lattice then 
    LambdaZZ := Lattice(Lambda);
  end if;

  if not assigned Y`Lattice then 
    YZZ := Lattice(Y);
  end if;

  V := Lambda`HermitianSpace;
  B := InnerProductMatrix(V);
  LambdaZZ := Lambda`Lattice;
  LambdaZZBasis := Lambda`LatticeZZBasis; 
                 
  YZZ := Y`Lattice;
  YZZBasisConj := Y`LatticeZZBasis;
  ZZ_LmodP, ZZ_LmodPMap := ResidueClassField(P);
  ZZ_LmodPgp, ZZ_LmodPgpMap := AdditiveGroup(ZZ_LmodP);
  E := Exponent(ZZ_LmodPgp);
  LambdaZZmodE, LambdaZZmodEMap := quo<LambdaZZ|E*LambdaZZ>;
  K := LambdaZZmodE;

  for y in YZZBasisConj do  
    preimagesZZ := [Eltseq((LambdaZZmodE.i)@@LambdaZZmodEMap) : i in [1..Ngens (LambdaZZmodE)]];     
    preimages := [V![L!v[d*(k-1)+1..d*k] : k in [1..m]] : v in preimagesZZ];
    images := [(ZZ_LmodPMap((Matrix(x)*B*Transpose(Matrix(y)))[1,1]))@@ZZ_LmodPgpMap : x in preimages];
    h := hom<LambdaZZmodE -> ZZ_LmodPgp | images>;
    K := K meet Kernel(h);
  end for;

  PiZZ := sub<LambdaZZ | [k@@LambdaZZmodEMap : k in Generators(K)] cat Basis(E*LambdaZZ)>;
  Pi := Module([V![L!Eltseq(v)[d*(k-1)+1..d*k] : k in [1..m]] : v in Basis(PiZZ)]);
   
  return false;
end intrinsic;
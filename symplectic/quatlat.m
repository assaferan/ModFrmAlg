//====================
//
// ALGEBRAIC MODULAR FORMS: HERMITIAN LATTICES OVER DEDEKIND DOMAINS
//
// This file contains a few extra functions for ModDed used by the ModFrmAlg package.
//
// Matthew Greenberg and John Voight, 2012
//
//====================



// ******************************************************************************
// ******************************************************************************


intrinsic LConjugate(M::ModMatRngElt) -> AlgMatElt
  {Return the entry-by-entry conjugate of M.}
  return Parent(M)![Conjugate(x) : x in Eltseq(M)]; 
end intrinsic;


// ******************************************************************************
// ******************************************************************************

intrinsic Lattice(LambdaBasis::SeqEnum) -> Lat
  {The lattice associated to the quaternionic lattice Lambda.}  
  L := BaseRing(LambdaBasis[1]);
  n := Dimension(Parent(LambdaBasis[1]));
  d := Degree(L);
  Z_L := MaximalOrder(L);
  phis := [Matrix(d*n,d*n, [Trace((Matrix(z*x)*Transpose(LConjugate(Matrix(y))))[1,1]) : x,y in LambdaBasis]) : z in Basis(Z_L)];
  Lambda := LatticeWithGram(phis[1]);
  Lambda`ZBasisQuatLat := LambdaBasis;
  Lambda`AuxForms := phis;
  return Lambda;
end intrinsic;

// ******************************************************************************
// ******************************************************************************

intrinsic PairsFromWithInto(Lambda::Lat, X::ModTupRngElt, P::AlgQuatOrdIdl : Check := false) -> Lat
  {Elements from Lambda that pair with X into P.}
  B := Lambda`ZBasisQuatLat;
  L := BaseRing(B[1]);
  Z_L := L`MaximalOrder;
  d := Degree(L);
  n := Dimension(Parent(B[1]));
  p := Integers()!Norm(P);
  Vp := RSpace(GF(p),d);
  Pmodp := sub<Vp|[Vp![Integers()!t : t in Eltseq(Z_L!x)] : x in Basis(P)]>;
  Pmodp_perp := OrthogonalComplement(Vp,Pmodp);
  Pmodp_perp_mat := Matrix(Basis(Pmodp_perp));

  mats := RMatrixSpace(L,1,2);
  XX := mats!Eltseq(X);
  BB := [mats!Eltseq(b) : b in B];
  pairings := [(bb*Transpose(LConjugate(XX)))[1,1] : bb in BB];          
  
  pairings_mat := Matrix([[GF(p)!Integers()!t : t in Eltseq(Z_L!x)] : x in pairings]);
  null := Nullspace(pairings_mat*Transpose(Pmodp_perp_mat));
  gens := [Lambda!v : v in Basis(null)] cat [p*x : x in Basis(Lambda)];
  Pi := sub<Lambda|gens>;

  if Check then 
    BPi := [mats!Eltseq(&+[w[i]*B[i] : i in [1..n*d]]) : w in Basis(Pi)];
    print ""; print "Is <Pi,X> a subset P?"; print &and[(bb*Transpose(LConjugate(XX)))[1,1] in P : bb in BPi]; print "";
  end if;

  return Pi;
end intrinsic;


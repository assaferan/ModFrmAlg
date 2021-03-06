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


intrinsic IsIntegral(Lambda::ModDed) -> BoolElt
  {Decides whether Lambda is unimodular or not.}

  require assigned Lambda`AmbientSpace : "Lambda`AmbientSpace must be defined.";
  V := Lambda`AmbientSpace;

  if assigned Lambda`Dual then
    return Lambda subset Lambda`Dual;
  else 
    B := InnerProductMatrix(V);
    pbLambda := PseudoBasis(Lambda);
    ZZ_LModuleGens := &cat[ [V!(x*pb[2]) : x in Generators(pb[1])] : pb in pbLambda];
    pairings := [Matrix(x)*B*Transpose(ComplexConjugate(Matrix(y))) : x, y in ZZ_LModuleGens];
    return {x[1,1] in BaseRing(Lambda) : x in pairings} eq {true};
  end if;
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic Discriminant(Lambda::ModDed) -> RngOrdIdl
  {Returns the discriminant ideal of Lambda.}

  if assigned Lambda`Discriminant then
    return Lambda`Discriminant;
  end if;

  V := Lambda`AmbientSpace;
  pbLambda := PseudoBasis(Lambda);
  Lambda_basis := Basis(Lambda);

  disc := (&*[pb[1]*ComplexConjugate(pb[1]) : pb in pbLambda])*Determinant(Matrix(Lambda_basis)*InnerProductMatrix(V)*Transpose(ComplexConjugate(Matrix(Lambda_basis))));

  if IsTotallyReal(BaseField(V)) and Dimension(V) mod 2 eq 1 then
    disc /:= 2;
  end if;
  return disc;
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic IsUnimodular(Lambda::ModDed) -> BoolElt
  {Decides whether Lambda is unimodular or not.}
 
  if not assigned Lambda`Discriminant then
    disc := Discriminant(Lambda);
    Lambda`Discriminant := disc;
  end if;
    return IsIntegral(Lambda) and Lambda`Discriminant eq 1*BaseRing(Lambda);
end intrinsic;


intrinsic Pair(x::ModTupFldElt, y::ModTupFldElt, B::AlgMatElt) -> FldOrdElt
  {The B-pairing of x and y.} 
  return (Matrix(x)*B*Transpose(ComplexConjugate(Matrix(y))))[1,1];
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic PushDown(V::ModTupFld) -> BoolElt
  {Pushes V down to Q}
  
  L := BaseField(V);
  d := Degree(L);
  B := InnerProductMatrix(V);
  m := Dimension(V);

  VQBasis := &cat[[x*v : x in Basis(L)] : v in Basis(V)];
  phis := [Matrix(d*m, d*m, [ Trace((Matrix(z*x)*B*Transpose(ComplexConjugate(Matrix(y))))[1,1]) : x, y in VQBasis]) : z in Basis(L)]; 

  V`QSpaceBasis := VQBasis;
  V`AuxForms := phis;

  return VectorSpace(Rationals(),d*m,phis[1]);
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic Lattice(Lambda::ModTupRng) -> Lat
  {Returns the lattice of Lambda pushed down to ZZ.}

  R := BaseRing(Lambda);
  require Type(R) eq AlgQuatOrd : "Lambda must be a module over a Dedekind domain";
  A := Algebra(R);
  if assigned Lambda`Lattice then
    return Lambda`Lattice;
  end if;

  V := Parent(Lambda.1);
  Lambda`AmbientSpace := V;
  // Is the ambient space necessary?
  L := BaseField(V);
  if not assigned V`QSpaceBasis then
    V`QSpaceBasis := &cat[[a*v : a in Basis(L)] : v in Basis(V)]; 
  end if;

  ZZ_L := Integers(BaseRing(Lambda));
  B := ChangeRing(InnerProductMatrix(V), FieldOfFractions(ZZ_L));
  d := Degree(ZZ_L);
  m := Dimension(Lambda);

  pbLambda := PseudoBasis(Lambda);
  LambdaZZBasis := &cat[ [ V!(x*pb[2]) : x in Basis(pb[1]) ] : pb in pbLambda ];
  LambdaZZBasisConj := [V![ComplexConjugate(t) : t in Eltseq(v)] : v in LambdaZZBasis];

  phis := [Matrix(d*m, d*m, [ Trace((Matrix(z*x)*B*Transpose(Matrix(y)))[1,1]) : x in LambdaZZBasis, y in LambdaZZBasisConj ]) 
               : z in Basis(ZZ_L)];
  phis := [ChangeRing(phi, Integers()) : phi in phis];

  LambdaZZ := LatticeWithGram(phis[1]);

  Lambda`Lattice := LambdaZZ;
  Lambda`LatticeZZBasis := LambdaZZBasis;
  Lambda`LatticeZZBasisConj := LambdaZZBasisConj;
  Lambda`LatticeAuxForms := phis[1..#phis];

  return LambdaZZ;
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic LatticeAutomorphismGroup(Lambda::ModDed : BeCareful := true) -> GrpMat
  {Returns the automorphism group of the lattice pushed down to ZZ.}

  if assigned Lambda`LatticeAutomorphismGroup and not BeCareful then
    return Lambda`LatticeAutomorphismGroup;
  end if;

  LambdaZZ := Lattice(Lambda);
  AutLambdaZZ := AutomorphismGroup(LambdaZZ, Lambda`LatticeAuxForms);
  Lambda`LatticeAutomorphismGroup := AutLambdaZZ;

  if BeCareful then
    commutes := &and[CheckCommuting(g,Lambda) : g in Generators(AutLambdaZZ)];
    if commutes then
      print "Scalar multiplication commutation test passed.";
    else 
      print "Automorphisms don't commute with multiplication by scalars from L!";
    end if;
  end if;

  return AutLambdaZZ;
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic IsIsometric(Lambda::ModDed, Pi::ModDed : Special := false, BeCareful := true) -> BoolElt, AlgMatElt
  {Returns true if the Lambda and Pi are isomorphic as ZZ_F-lattices. Also returns the matrix g of an isometry from Pi to Lambda (sic) with respect to the bases of Pi and Lambda.}

  require  Lambda`AmbientSpace eq Pi`AmbientSpace : "Lattices must come from the same space.";

  LambdaZZ := Lattice(Lambda);
  LambdaZZAuxForms := Lambda`LatticeAuxForms;
  PiZZ := Lattice(Pi);
  PiZZAuxForms := Pi`LatticeAuxForms;

  bl, g := IsIsometric(LambdaZZ, LambdaZZAuxForms, PiZZ, PiZZAuxForms);

  if bl then
    if BeCareful then
      if CheckCommuting(g,Lambda,Pi) then
        print "Scalar multiplication commutation test passed.";
      else 
        print "Automorphisms don't commute with multiplication by scalars from L!";
      end if;
    end if;
    return bl, g;
  else
    return bl;
  end if;
  
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic PullUp(g::AlgMatElt, Lambda::ModDed, Pi::ModDed : BeCareful := true) -> AlgMatElt
  {Takes an isometry g : Pi -> Lambda and reexpresses it as an L-linear map gV : V -> V.}

  LambdaZZ := Lattice(Lambda);
  LambdaZZAuxForms := Lambda`LatticeAuxForms;
  PiZZ := Lattice(Pi);
  PiZZAuxForms := Pi`LatticeAuxForms;   
  BL := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Lambda`LatticeZZBasis]);
  BP := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Pi`LatticeZZBasis]);
  m := Dimension(Lambda);
  V := Lambda`AmbientSpace;
  L := BaseField(V);
  d := Degree(L);
  rows := [];
  for i in [1..m] do
    v := Vector(&cat[Eltseq(x) : x in Eltseq(V.i)]);
    rowQ := Eltseq(v*BP^-1*(Parent(BL)!g)*BL);
    rowL := Vector([L!rowQ[j*d+1..(j+1)*d] : j in [0..m-1]]); 
    Append(~rows,rowL);
  end for;
  ans := Matrix(rows);
  
  if BeCareful then
    print "gV maps Pi into Lambda?", &and[x*ans in Lambda : x in Pi`LatticeZZBasis];
    print "gV respects the inner product?", InnerProductMatrix(V) eq ans*InnerProductMatrix(V)*ComplexConjugate(Transpose(ans));
  end if;
  
  return ans;
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic CheckCommuting(g::GrpMatElt, Lambda::ModDed) -> BoolElt
  {Does g commute with multiplication by scalars in L?}

   V := Lambda`AmbientSpace;
   B := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Lambda`LatticeZZBasis]);

  if not assigned V`ScalarMultQMats then
    L := BaseField(V);
    V`ScalarMultQMats := [Matrix([&cat[Eltseq(z) : z in Eltseq(a*x)] : x in V`QSpaceBasis]) : a in Basis(L)]; 
  end if;

  return &and[x*B^-1*Matrix(g)*B eq B^-1*Matrix(g)*B*x : x in V`ScalarMultQMats]; 

end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic CheckCommuting(g::AlgMatElt, Lambda::ModDed, Pi::ModDed) -> BoolElt
  {Does g : Pi -> Lambda commute with multiplication by scalars in L?}

   V := Lambda`AmbientSpace;
   BL := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Lambda`LatticeZZBasis]);
   BP := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Pi`LatticeZZBasis]);

  if not assigned V`ScalarMultQMats then
    L := BaseField(V);
    V`ScalarMultQMats := [Matrix([&cat[Eltseq(z) : z in Eltseq(a*x)] : x in V`QSpaceBasis]) : a in Basis(L)]; 
  end if;

  return &and[x*BP^-1*Matrix(g)*BL eq BP^-1*Matrix(g)*BL*x : x in V`ScalarMultQMats]; 

end intrinsic;


// ******************************************************************************
// ******************************************************************************


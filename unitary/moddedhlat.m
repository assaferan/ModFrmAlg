//====================
//
// ALGEBRAIC MODULAR FORMS: HERMITIAN LATTICES OVER DEDEKIND DOMAINS
//
// This file contains a few extra functions for ModDed used by the ModFrmAlg package.
//
// Matthew Greenberg and John Voight, 2012
//
//====================

declare attributes ModTupRng:
  almost_basis;       // If M=I_1*a_1 + ... + I_n*a_n and
                      // b_i is in I_i-I_i^2, then almost_basis is
                      // [b_1*a_1, ..., b_n*a_n].
		      // This doesn't work for I_i not prime.

declare attributes ModTupFld:
  Quadraticity,       // "Orthogonal", "Hermitian", etc.
  QSpaceBasis,        // A basis of V as a Q-vector space 
  QSpaceBasisMatrix,  // The matrix of QSpaceBasis pushed down to Q
  AuxForms,           // The auxilliary forms that define V as an L-space
  ScalarMultQMats;    // Matrices of multiplication by elements of the basis of the base field of V 

declare attributes ModDed:   
                      // = Lambda
  AmbientSpace,       // Lambda's ambient L-space
  Discriminant,       // Discriminant
  Dual,               // Dual lattice  
  ModDedZZ_F,         // The Hermitian lattice Lambda, pushed down to ZZ_F 
  ModDedZZ_FBasis,    // Basis for LambdaZZ.
  ModDedZZ_FAuxForms, // The auxiliary forms which define LambdaZZ as a module over ZZ_F.

  QuadraticSpace,     // 
  Lattice,            // = Lattice(Lambda) = LambdaZZ, the lattice pushed down to ZZ, of type Lat.
  LatticeZZBasis,     // Basis for LambdaZZ.
  LatticeZZBasisConj, // Componentwise complex conjugate of LambdaZZ.
  LatticeAuxForms,    // The auxiliary forms which define LambdaZZ as a module over ZZ_F.
  LatticeAutomorphismGroup,
                      // = LatticeAutomorphismGroup(Lambda), the automorphism group of LambdaZZ.
  ParentModFrmAlg,    // = M

  Discriminant,       // = Discriminant(Lambda), the discriminant ideal of Lambda.

  ppStandardBases,    // Cached standard bases.  
  almost_basis,
  LatticeFormsScale;

intrinsic Random(Lambda::ModDed, B::RngIntElt) -> ModTupFldElt
  {Returns a "random" element of Lambda.}
  pbLambda := PseudoBasis(Lambda);
  return &+[ Random(pb[1],B)*pb[2] : pb in pbLambda];
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic HasComplexConjugate(Q::FldRat) -> BoolElt
  {No.}
  return false;
end intrinsic;

/*
// This is needed because magma has a bug in HasComplexConjugate
intrinsic HasComplexConjugate(K::FldCyc) -> BoolElt, UserProgram
{.}
  // This is the cyclotomic polynomial
  KasNum := ext<Rationals() | MinimalPolynomial(K.1)>;
  _, phi := IsIsomorphic(K, KasNum);
  _, cc := HasComplexConjugate(KasNum);

  function complex_conjugate(a)
    return (phi^(-1))(cc(phi(a)));
  end function;

  return true, complex_conjugate;
end intrinsic;
*/

// ******************************************************************************
// ******************************************************************************


intrinsic ComplexConjugate(I::RngOrdFracIdl) -> RngOrdIdl
  {Return the complex conjugate of I when it's defined.  When it's not, it returns I.}
  O := Order(I);
  L := AbsoluteField(FieldOfFractions(O));
  if HasComplexConjugate(L) then
    return ideal<O|[ComplexConjugate(L!x) : x in Generators(I)]>;
  else
    return I;
  end if;
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic ComplexConjugate(x::ModTupFldElt) -> ModTupFldElt
  {Return the complex conjugate of x when it's defined.  When it's not, it returns x.}
  L := AbsoluteField(BaseField(Parent(x)));
  _,cc := HasComplexConjugate(L);
  return Parent(x)![cc(y) : y in Eltseq(x)]; 
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic ComplexConjugate(M::AlgMatElt) -> AlgMatElt
  {Return the complex conjugate of M when it's defined. When it's, it just gives back M.}
  L := AbsoluteField(FieldOfFractions(BaseRing(M)));
  if HasComplexConjugate(L) then
    return Parent(M)![ComplexConjugate(L!x) : x in Eltseq(M)]; 
  else
    return M;
  end if;
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic ComplexConjugate(M::ModMatFldElt) -> AlgMatElt
  {Return the complex conjugate of M when it's defined. When it's, it just gives back M.}
  L := AbsoluteField(FieldOfFractions(BaseRing(M)));
  if HasComplexConjugate(L) then
    return Parent(M)![ComplexConjugate(L!x) : x in Eltseq(M)]; 
  else
    return M;
  end if;
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


intrinsic LineReps(Lambda::ModDedLat, P::RngOrdIdl :
		   UseAutomorphisms := true, BeCareful := true) ->.
  {Computes basis vectors for the lines in L/P*L}

  n := Dimension(Lambda);
  pbLambda := PseudoBasis(Lambda);
  coeff_ideals := [x[1] : x in pbLambda];
  B := Matrix(Basis(Module(Lambda)));
  if UseAutomorphisms then
    G := AutomorphismGroup(Lambda);
  else
    G := sub<GL(n, Integers()) | >;
  end if;
  gens_L := [PullUp(Matrix(g), Lambda, Lambda :
		  BeCareful := BeCareful) : g in Generators(G)];

  kP,redP := ResidueClassField(P);
  A := [[x : x in Generators(I) | x notin P*I][1] : I in coeff_ideals];
  V := VectorSpace(AmbientSpace(Lambda));
  C := [V!Vector(A[i]*B[i]) : i in [1..n]];
  B := ChangeRing(B, BaseField(V));

  f := function(v)
    w := Eltseq(v*B^-1);
    // why is w[i] / A[i] integral?
    ans := [redP(w[i]/A[i]) : i in [1..n]];
    return ans;
  end function;

  gens_LmodP := [Matrix([f(c*g) : c in C]) : g in gens_L];
  GmodP := sub<GL(n,kP)|gens_LmodP>;
  modP_line_reps := [x[1].1 : x in LineOrbits(GmodP)];
  line_reps := [&+[x[i]@@redP*C[i] : i in [1..n]] : x in modP_line_reps];

//{x in Lambda : x in line_reps};
//{x-y in P*Lambda : x,y in line_reps | x ne y};

//  A := [Random([a : a in Generators(I[1]) | Valuation(a,P) eq Valuation(I[1],P)]) : I in pbLambda];
    // A[i] generates the the completion of the coefficient ideal pbLambda[i,1] at P
//  kP,redP := ResidueClassField(P);
//  Pdminusone := [Eltseq(x) : x in RationalPoints(ProjectiveSpace(kP,n-1))];  
//  return [&+[x[i]@@redP*A[i]*pbLambda[i,2] : i in [1..n]] : x in Pdminusone]; 

  return line_reps; 
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


intrinsic Lattice(Lambda::ModDed) -> Lat
  {Returns the lattice of Lambda pushed down to ZZ.}

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
// B := ChangeRing(InnerProductMatrix(V), FieldOfFractions(ZZ_L));
  B := InnerProductMatrix(V);
  d := Degree(ZZ_L);
  m := Dimension(Lambda);
  L_abs := AbsoluteField(FieldOfFractions(ZZ_L));

  pbLambda := PseudoBasis(Lambda);
  LambdaZZBasis := &cat[ [ V!(x*pb[2]) : x in Basis(pb[1]) ] : pb in pbLambda ];
  LambdaZZBasisConj := [V![ComplexConjugate(L_abs!t) : t in Eltseq(v)] : v in LambdaZZBasis];

  phis := [Matrix(d*m, d*m, [ Trace((Matrix(z*x)*B*Transpose(Matrix(y)))[1,1]) : x in LambdaZZBasis, y in LambdaZZBasisConj ]) 
               : z in Basis(ZZ_L)];
  D := LCM([Denominator(x) : x in phis]);
  phis := [ChangeRing(D*phi, Integers()) : phi in phis];
  
//  phis := [ChangeRing(phi, Integers()) : phi in phis];
//  phis := [ChangeRing(phi, Rationals()) : phi in phis];

  LambdaZZ := LatticeWithGram(phis[1]);

  Lambda`Lattice := LambdaZZ;
  Lambda`LatticeZZBasis := LambdaZZBasis;
  Lambda`LatticeZZBasisConj := LambdaZZBasisConj;
  Lambda`LatticeAuxForms := phis[1..#phis];
  Lambda`LatticeFormsScale := D;

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
  PiZZ := Lattice(Pi);
// For some reason, IsIsometric can only eat integral matrices for the forms
// so we scale everything	       
  LambdaZZAuxForms := [Pi`LatticeFormsScale * x : x in Lambda`LatticeAuxForms];
  PiZZAuxForms := [Lambda`LatticeFormsScale * x : x in Pi`LatticeAuxForms];

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


intrinsic PullUp(g::AlgMatElt, Lambda::ModDedLat, Pi::ModDedLat :
		 BeCareful := true) -> AlgMatElt
  {Takes an isometry g : Pi -> Lambda and reexpresses it as an L-linear map gV : V -> V.}

  LambdaZZ := ZLattice(Lambda);
  LambdaZZAuxForms := AuxForms(Lambda);
  PiZZ := ZLattice(Pi);
  PiZZAuxForms := AuxForms(Pi);   
  BL := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Rows(LambdaZZ`basisZ)]);
  BP := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Rows(PiZZ`basisZ)]);
  m := Dimension(Lambda);
  V := VectorSpace(AmbientSpace(Lambda));
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


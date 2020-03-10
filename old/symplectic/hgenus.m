//====================
//
// GENERA AND NEIGHBORS
//
// This file contains functions for computing the genera and neighbors for the ModFrmAlg package.
//
// Matthew Greenberg and John Voight, 2012
//
//====================


intrinsic NeighborVectors(Lambda::ModDed, 
			       P::RngOrdIdl,
 			   Pbar ::RngOrdIdl) -> SeqEnum
  {vectors needed for neighbor construction}

  ZZ_L := BaseRing(Lambda);
  d := Dimension(Lambda);
  kP, redP := ResidueClassField(P);
  pibar := Generators(Pbar)[#Generators(Pbar)];

  if assigned Lambda`almost_basis then
    almost_basis := Lambda`almost_basis;
  else
    pbLambda := PseudoBasis(Lambda);
    almost_basis := [Generators(pb[1])[#Generators(pb[1])]*pb[2] : pb in pbLambda];
    Lambda`almost_basis := almost_basis;
   end if;

  Pdminusone := RationalPoints(ProjectiveSpace(kP,d-1));  
  lifts := [[t@@redP : t in Eltseq(x)] : x in Pdminusone];
  vectors := [&+[x[i]*almost_basis[i] : i in [1..d]] : x in lifts];
  ans := [pibar*v : v in vectors];
  
  return ans;
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic Neighbor(Lambda::ModDed,
                        P::RngOrdIdl,
                     Pbar::RngOrdIdl,
                        X::ModTupFldElt ) -> ModDed
  {Constructs the P-neighbour of Lambda associated to X}

  ZZ_L := BaseRing(Lambda);
  V := Lambda`AmbientSpace;
  B := InnerProductMatrix(V);
  pbLambda := PseudoBasis(Lambda);
  n := Dimension(Lambda);
  LocalBasis := [];
  
  for i in [1..n] do
    I := pbLambda[i,1];
    Igens := Generators(I);
    if Igens[1] notin Pbar*I then 
      Append(~LocalBasis,Igens[1]*pbLambda[i,2]);
    else 
      Append(~LocalBasis,Igens[2]*pbLambda[i,2]); 
    end if;
  end for;
  // LocalBasis does not depend on X.

  X_conj := V![ComplexConjugate(x) : x in Eltseq(X)];
  pairings := [(Matrix(y)*B*Transpose(Matrix(X_conj)))[1,1] : y in LocalBasis];
    // LocalBasis*B does not depend on X.
  kPbar,kPbarMap := ResidueClassField(Pbar);
    // KPbar and kPbarMap do not depend on X.
  A := Matrix(kPbar,n,1,[kPbarMap(x) : x in pairings]);
  LiftedNullspaceBasis := [&+[w[i]@@kPbarMap*LocalBasis[i] : i in [1..n]] : w in Basis(Nullspace(A))];

  pbPbarLambda := PseudoBasis(Pbar*Lambda);
    // pbPbarLambda does not depend on X.
  prePi := Module(LiftedNullspaceBasis cat &cat[[x*pb[2] : x in Generators(pb[1])] : pb in pbPbarLambda]);
  Pi := P^-1*X +prePi;
  Pi`AmbientSpace := V;
  
//  ed := ElementaryDivisors(Lambda,Pi);
//  correct := #[I : I in ed | I eq P^-1] eq 1 and #[I : I in ed | I eq Pbar] eq 1 and #[I : I in ed | I eq 1*ZZ_L] eq n-2;
//  print "P-neighbor associated to", X; 
//  print "(Check) Correct elementary divisors?", correct; 

  return Pi;
end intrinsic;


// ******************************************************************************
// ******************************************************************************

//=======
//
// Genus representatives
//
//=======

intrinsic Neighborhood(Lambda::ModDed, P::RngOrdIdl : BeCareful := true, verbose := false) -> SeqEnum[ModDed]
  {Returns a set of representatives for the genus of the defining lattice of M.}

dd := Discriminant(Lambda);
require &and[Valuation(dd,P) eq 0, Valuation(dd,ComplexConjugate(P)) eq 0] : "P must be coprime to the discriminant of Lambda.";

expanded := [**];
unexpanded := [*Lambda*];
if not assigned Lambda`LatticeAuxForms then
       	LambdaZZ := Lattice(Lambda);
end if;

tm:=Cputime();
count := 0;
while #unexpanded gt 0 do
        count := count + 1;
        print "expanded:", #expanded, "unexpanded:", #unexpanded, "count:", count;  
	Pi := unexpanded[1];
	ngbr_vectors := NeighborVectors(Pi,P,ComplexConjugate(P));
        a := 0;		
	for X in ngbr_vectors do
                a := a+1; if a mod 100 eq 0 then print a, "out of", #ngbr_vectors; end if;
		Rho := Neighbor(Pi,P,ComplexConjugate(P),X);
		RhoZZ := Lattice(Rho);	
   		if not exists(t){Sigma : Sigma in expanded cat unexpanded | IsIsometric(Rho,Sigma : BeCareful := false)} then
			Append(~unexpanded,Rho);
			print Cputime(tm), "seconds:", #expanded+#unexpanded,"classes found so far.";
		end if;
	end for;
	Remove(~unexpanded,1);
	Append(~expanded,Pi);
end while;	

return expanded;

end intrinsic;

// ******************************************************************************
// ******************************************************************************


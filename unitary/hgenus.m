//====================
//
// GENERA AND NEIGHBORS
//
// This file contains functions for computing the genera and neighbors for the ModFrmAlg package.
//
// Matthew Greenberg and John Voight, 2012
//
//====================

// More important - this is non-deterministic, and usually
// does not return the correct result

// Important - This does not produce all P-neighbours!!!
// It produces the P-neighbours in one direction
// To get the others should run it also with Pbar !!!!

// For some reason, this does not produce the correct results,
// have to understand why
// This intrinsic seems to be working
// If one works over rationals need to use RationalsAsNumberField

intrinsic NeighborVectors(Lambda::ModDed, 
			       P::RngOrdIdl,
			  Pbar ::RngOrdIdl :
			  UseAutomorphisms := true,
			  BeCareful := true) -> SeqEnum
  {vectors needed for neighbor construction}
  
  n := Dimension(Lambda);
  ZZ_L := BaseRing(Lambda);
  L := NumberField(ZZ_L);
  _,cc := HasComplexConjugate(L);
  F := sub<L|L.1+cc(L.1)>;
  ZZ_F := MaximalOrder(F);
  NP := ideal<ZZ_F|[x*cc(x) : x in Generators(P)]>;
  p := Factorization(NP)[1,1];
  if RamificationIndex(P) ne RamificationIndex(p) then 
    decomp := "ramified";
    // !!! For now we only use split primes
    return [];
  else
    if InertiaDegree(P) eq InertiaDegree(p) then
      decomp := "split";
    else
      decomp := "inert";
      // !!! for now we only use split primes
      return [];
    end if;
  end if;

  R1 := LineReps(Lambda,P :
	       UseAutomorphisms := UseAutomorphisms, BeCareful := BeCareful);
    // Compute basis vectors for the lines in L/P*L
  kP,redP := ResidueClassField(P);
// eran 28 Feb 2020:  This line was here, but it does not reallly work
// Reason is that a generator might be in P * Pbar
// Also, for debugging reasons we would like to reduce randomness wherever
// possible
//   pi := Random([x : x in Generators(P) | x notin P^2]);
  _ := exists(pi){g : g in Generators(P) | ZZ_F!Norm(g) notin p^2};
  pibar := ComplexConjugate(L!pi);

  if decomp eq "split" then 
    ans := [pibar*x : x in R1];
  else
    R2 := [x : x in R1 | InnerProduct(x,ComplexConjugate(x)) in P];
      // Find the isotropic lines.
    schiemann_lambdas := [x@@redP : x in kP];
      // Has nothing to do with the lattice Lambda.  Just want to stay consistent with Schiemann.
    Y := [Random([y : y in Basis(Lambda) | InnerProduct(y,ComplexConjugate(x)) notin P]) : x in R2];

    if decomp eq "ramified" then
      ans := [R2[i] + pi*lambda*Y[i] : i in [1..#R2], lambda in schiemann_lambdas];
    else
      ans := [R2[i]+pi*lambda*Y[i] : i in [1..#R2], lambda in schiemann_lambdas | InnerProduct(R2[i]+pi*Y[i]*lambda,ComplexConjugate(R2[i]+pi*Y[i]*lambda)) in P*Pbar];
    end if;

  end if;
  
  return ans;
end intrinsic;


// ******************************************************************************
// ******************************************************************************


intrinsic Neighbor(Lambda::ModDed,
                        P::RngOrdIdl,
                     Pbar::RngOrdIdl,
                        X::ModTupFldElt) -> ModDed
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

procedure computeHGenusReps(M : BeCareful := true, Force := false,
			    Orbits := false)
  if not Force and assigned M`genus then return; end if;

  upTo := 0;

  // Initialize the list with the module defining M
  genList := [Module(M)];

  // Later - add critical primes, etc. !!!
  ps := [];
  ps_idx := 1;

  RR := RealField();
  mass := UnitaryMass(BaseRing(M), Dimension(Module(M)));
tmp_mass := RR!#LatticeAutomorphismGroup(Module(M) :
					 BeCareful := BeCareful)^(-1);

  eps := RR!10^(-30);

  while (Abs(tmp_mass - mass) gt eps) do
    repeat
      upTo +:= 10;
      ps := [p : p in PrimesUpTo(upTo, BaseRing(M)) |
	     GCD(Integers()!Norm(Discriminant(Module(M)))*2, Norm(p)) eq 1];
    until #ps ne 0;

    while (ps_idx le #ps) and (Abs(tmp_mass - mass) gt eps) do
      nbd := Neighborhood(Module(M), ps[ps_idx]);
      for lat in nbd do
		if not (&or[IsIsometric(lat, r :
			    BeCareful := BeCareful) : r in genList]) then
          Append(~genList, lat);
          tmp_mass +:= 1/(#LatticeAutomorphismGroup(lat :
						    BeCareful := BeCareful));
        end if; 
      end for;
      ps_idx +:= 1;
    end while;
  end while;

  // TODO: Replace the last two until statements with the appropriate
  //  conditions to check the mass formula to see if we need to compute
  //  genus representatives at multiple primes.

  // Assign the genus symbol for the space of algebraic modular forms.
  M`genus := New(GenusSym);
  M`genus`Representative := M`L;
  M`genus`Representatives := genList;
//  M`genus`RepresentativesAssoc := invs;

end procedure;

// This works when Lamda is defined over an extension of a number field.
// 

intrinsic Neighborhood(Lambda::ModDed, P::RngOrdIdl :
		       BeCareful := false) -> SeqEnum[ModDed]
  {Returns a set of representatives for the genus of the defining lattice of M.}

dd := Discriminant(Lambda);
require &and[Valuation(dd,P) eq 0, Valuation(dd,ComplexConjugate(P)) eq 0] : "P must be coprime to the discriminant of Lambda.";

expanded := [];
unexpanded := [Lambda];
if not assigned Lambda`LatticeAuxForms then
       	LambdaZZ := Lattice(Lambda);
end if;

tm:=Cputime();
count := 0;
while #unexpanded gt 0 do
        count := count + 1;
        if BeCareful then
          print "expanded:", #expanded, "unexpanded:", #unexpanded, "count:", count;
        end if;
	Pi := unexpanded[1];
        ngbr_vectors := NeighborVectors(Pi,P,ComplexConjugate(P) :
				BeCareful := BeCareful);
        a := 0;		
	for X in ngbr_vectors do
                a := a+1; if a mod 100 eq 0 then print a, "out of", #ngbr_vectors; end if;
		Rho := Neighbor(Pi,P,ComplexConjugate(P),X);
		RhoZZ := Lattice(Rho);	
   		if not exists(t){Sigma : Sigma in expanded cat unexpanded | IsIsometric(Rho,Sigma : BeCareful := BeCareful)} then
			Append(~unexpanded,Rho);
                        if (BeCareful) then
			  print Cputime(tm), "seconds:", #expanded+#unexpanded,"classes found so far.";
                        end if;
		end if;
	end for;
	Remove(~unexpanded,1);
	Append(~expanded,Pi);
end while;	

return expanded;

end intrinsic;

// very naive implementation - just going over all neighbours,
// and checking isometries - (Np^2+Np+1)*(g^2) isometry tests

function HeckeOperatorTrivialWeightUnitary(M, P : BeCareful := true)
  genus := Representatives(Genus(M));
  d := #genus;
  T := MatrixAlgebra(Integers(), d)!0;
  Pbar := ComplexConjugate(P);
  for gen_idx1 in [1..d] do
	       ngbr_vectors := NeighborVectors(genus[gen_idx1],P,Pbar :
			  BeCareful := BeCareful, UseAutomorphisms := false);
    for X in ngbr_vectors do
      Rho := Neighbor(genus[gen_idx1],P,Pbar,X);
      RhoZZ := Lattice(Rho);
      for gen_idx2 in [1..d] do
	if IsIsometric(Rho, genus[gen_idx2] : BeCareful := BeCareful) then
          T[gen_idx2, gen_idx1] +:= 1;
	end if;
      end for;
    end for;
  end for;
  return T;
end function;

// ******************************************************************************
// ******************************************************************************

// Here one assumes L is given as a number field over Q
// (AbsoluteField)

intrinsic UnitaryMass(L,m : prec := 30) -> Lat
  {Returns an approximation to the mass of principal genus of Hermitian ZZ_L lattices.}

  L := AbsoluteField(L);
  ZZ_L := MaximalOrder(L);
  _,cc := HasComplexConjugate(L);
  F := sub<L|[L.1+cc(L.1)]>;
  ZZ_F := MaximalOrder(F);
  d := Degree(L) div 2;
  tau := 2;

  ZL := LSeries(L : Precision := prec);
  ZF := LSeries(F : Precision := prec);
  LofM :=  &*[Evaluate(ZL/ZF,1-r) : r in [1..m] | r mod 2 eq 1]*&*[Evaluate(ZF,1-r) : r in [1..m] | r mod 2 eq 0];   

  if m mod 2 eq 0 then
    prod_of_local_factors := 1;
  else 
    RF := &cat[[x[1] : x in Factorization(p*ZZ_F)] : p in PrimeFactors(Discriminant(ZZ_L))];                                                 
    RL := [Factorization(ideal<ZZ_L|Generators(I)>)[1,1] : I in RF]; 
    N := #[I : I in RF | Factorization(ideal<ZZ_L|Generators(I)>)[1,2] gt 1];
    prod_of_local_factors := (1/2)^N;
  end if;

  mass := 1/2^(m*d)*LofM*tau*prod_of_local_factors;
  return mass;
end intrinsic;


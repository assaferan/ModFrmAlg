freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch
                                                                            
   FILE: genus-CN1.m (implementation file for genus computations)

   Implementation file for computing p-neighbors for genus computations

   05/29/20: Modified computeGenusRepsAt - added a BeCareful when calling
             checkNextNeighbor.

   05/26/20: Modified computeGenusRepsAt to support non-liftable isotropic
             vectors mod pR.
             Modified computeGenusRepsCN1 to use the mass formula.
             At the moment we are still not using it as a stopping criterion,
             to accelerate the genus computation.
             Fixed some bugs in UnitaryMass.
             Added code from Kirschmer's package for calculating the 
	     orthogonal mass of a lattice.

   05/11/20: Updated computeGenusRepsAt, following interface change of 
             GetNextNeighbor.

   04/15/20: Added the unitary mass formula. At the moment still not using it.

   03/06/20: added the procedure checkNextNeighbor, for easier debugging and flow

   02/28/20: started editing this file to add Unitary forms
 
 ***************************************************************************/

// imports

import "../lattice/lattice.m" : GramMatrixOfBasis;
import "../modfrmalg/modfrmalg.m" : ModFrmAlgInit;
import "neighbor-CN1.m" : BuildNeighborProc, BuildNeighbor, GetNextNeighbor;
import "inv-CN1.m" : Invariant;

// functions

procedure checkNextNeighbor(nProc, buildNeighbor, ~invs, ~isoList, ~acc_mass, G
			    : BeCareful := false, Special := false, 
			      ThetaPrec := 25)

    // Compute the neighbor according to the current state
    //  of the neighbor procedure.
    nLat := buildNeighbor(nProc : BeCareful := BeCareful, UseLLL := not Special);

    // A specified invariant of the neighbor lattice.
    inv := Invariant(nLat : Precision := ThetaPrec);

    // If this invariant is defined for the array, we need
    //  to potentially check for isometry.
    if IsDefined(invs, inv) then
       // Retrieve the array for this invariant.
       array := invs[inv];

       // Flag whether we found the right class.
       found := false;
       for i in [1..#array] do
	 // Check for isometry.
	 iso := IsIsometric(array[i][1], nLat : Special := Special);

         // Skip ahead if an isometry is found.
	 if iso then
	    found := true;
	    break;
	 end if;
       end for;

       // If no isometry found, add it to the list.
       if not found then
         Append(~invs[inv], < nLat, #isoList+1 >);
	 Append(~isoList, nLat);
	 acc_mass +:= #AutomorphismGroupOverField(nLat, G : Special := Special)^(-1);
//	 assert acc_mass eq &+[#AutomorphismGroupOverField(r, G : Special := Special)^(-1) : r in isoList];
       end if;
    else
       invs[inv] := [ < nLat, #isoList+1 > ];
       Append(~isoList, nLat);
       acc_mass +:= #AutomorphismGroupOverField(nLat, G : Special := Special)^(-1);
//       assert acc_mass eq &+[#AutomorphismGroupOverField(r, G : Special := Special)^(-1) : r in isoList];
    end if;

end procedure;

function computeGenusRepsAt(p, isoList, invs, total_mass, acc_mass, G
			    : BeCareful := true, Force := false,
			    Special := false, UseMass := false,
			    ThetaPrec := 25)
    // The index of the current isometry class being considered.
    isoIdx := 1;

    repeat
	// Build the neighbor procedure for the current lattice.
	nProc := BuildNeighborProc(isoList[isoIdx], p, 1
				   : BeCareful := BeCareful);

	while nProc`isoSubspace ne [] do
	    checkNextNeighbor(nProc, BuildNeighbor,
			      ~invs, ~isoList, ~acc_mass, G:
			      BeCareful := BeCareful,
			      Special := Special,
			      ThetaPrec := ThetaPrec);
	    // Move on to the next neighbor lattice.
	    GetNextNeighbor(~nProc
			    : BeCareful := BeCareful);
	    if UseMass then
		if (acc_mass eq total_mass) then
		    return isoList, invs, acc_mass;
		end if;
	    end if;
	    
	end while;

	vprintf AlgebraicModularForms, 1: "isoIdx / #isoList = %o / %o\n", isoIdx, #isoList; 
	if GetVerbose("AlgebraicModularForms") ge 1 then
	    if UseMass then
		print "accumulated mass / total_mass = ", acc_mass * 1., "/", total_mass * 1.;
	    end if;
	end if;
	
	// Move on to the next genus representative.
	isoIdx +:= 1;
    until isoIdx gt #isoList;
    
    return isoList, invs, acc_mass;
end function;

forward UnitaryMass, OrthogonalMass;

procedure computeGenusRepsCN1(M : BeCareful := true, Force := false,
			      UseMass := false, ThetaPrec := 25)
    // Do not compute the genus representatives if they've already been
    //  computed and we aren't forcing a recomputation.
    if not Force and assigned M`genus then return; end if;

    // An upper bound for the norm of the primes at which we seek to
    //  compute genus reps.
    upTo := 0;

    // The list of genus representatives. We initialize this list with
    //  the standard lattice with respect to our inner form.
    genList := [ Module(M) ];

    // Initialize the associative array hashed by an invariant. This will
    //  allow us to reduce the number of isometry tests required to
    //  determine equivalence.
    ZZq<q> := PuiseuxSeriesRing(Integers());
    invs := AssociativeArray(ZZq);
    invs[Invariant(Module(M) : Precision := ThetaPrec)] := [ < Module(M), 1 > ];

    // Do we need this? Check the ramified primes
    bad_modulus := Numerator(Norm(Discriminant(Module(M))));
    V := ReflexiveSpace(Module(M));
    // something crashes in orthogonal mass
    // until we figure it out we leave it be
    if UseMass then
	// If we're doing more than one prime, it could be a bad one
	// Changing it to avoid issues with fake spinor norm representations
	if (not assigned M`W`weight) or (M`W`weight[1] eq 1) then
	    bad_modulus := Parent(bad_modulus)!1;
	end if;
	acc_mass := #AutomorphismGroupOverField(Module(M), M`W`G : Special := IsSpecialOrthogonal(M))^(-1);
	if SpaceType(V) eq "Hermitian" then
	    K := BaseRing(V);
	    // !!! TODO :
	    // replace with the calculation of mass relative to this lattice
	    total_mass := UnitaryMass(K, Dimension(Module(M)));
	else
	    total_mass := OrthogonalMass(Module(M) : Special := IsSpecialOrthogonal(M));
	end if;
    else
	total_mass := 0;
	acc_mass := 0;
    end if;
    repeat
	repeat
	    // Increment norm by 10.
	    upTo +:= 10;

	    // Compute a list of primes which do not divide the
	    //  discriminant of the lattice.            
	    ps := PrimesUpTo(upTo, BaseRing(M) : coprime_to := bad_modulus);
	until #ps ne 0;

	idx := 1;
	repeat
	    // Compute genus representatives at a specific prime.
	    genList, invs, acc_mass := computeGenusRepsAt(
					       ps[idx], genList, invs, 
					       total_mass, acc_mass, M`W`G
					       : BeCareful := BeCareful,
						 Force := Force,
						 Special := IsSpecialOrthogonal(M), 
						 UseMass := UseMass, 
						 ThetaPrec := ThetaPrec);

	    // Move to the next prime.
	    idx +:= 1;
            inner_stop_cond := UseMass select
	      ((idx gt #ps)  or (acc_mass eq total_mass)) else true;
       until inner_stop_cond;
       stop_cond := UseMass select acc_mass eq total_mass else true;
     until stop_cond;


    // Assign the genus symbol for the space of algebraic modular forms.
    M`genus := New(GenusSym);
    M`genus`Representative := M`L;
    M`genus`Representatives := genList;
    M`genus`RepresentativesAssoc := invs;
end procedure;

function sortGenusCN1(genus : ThetaPrec := 25)
    // An empty associative array.
    ZZq<q> := PuiseuxSeriesRing(Integers());
    invs := AssociativeArray(ZZq);

    // An ordered list of genus representatives;
    lats := Representatives(genus);

    for i in [1..#lats] do
	// Compute the invariant associated to this genus rep.
	inv := Invariant(lats[i] : Precision := ThetaPrec);

	// Assign an empty list to the invariant hash if it hasn't been
	//  assigned yet.
	if not IsDefined(invs, inv) then invs[inv] := []; end if;
	
	// Add to list.
	Append(~invs[inv], < lats[i], i >);
    end for;
    
    // Assign the representatives associated array.
    genus`RepresentativesAssoc := invs;
    
    return genus;
end function;

// All the code down below is for computing mass formulas

/* Evaluating Dedekind zeta functions at negative integers exactly */

// Working with ideal class groups

function CGPrimes(I, S, Generators, CoprimeTo, Minimal, Quotient)
  R:= Order(I);
  if not IsMaximal(R) or not IsAbsoluteOrder(R) then return false, "The order must be absolute and maximal"; end if;
  r1, r2:= Signature(NumberField(R));
  if not IsEmpty(S) then
    T:= Type(Universe(S));
    if T eq PlcNum then
      X:= S; S:= [];
      for s in X do
        ok, i:= IsInfinite(s); 
        if not ok or not IsReal(s) then return false, "The places must be real"; end if;
        Append(~S, i);
      end for;
    elif (T eq RngInt) and Minimum(S) ge 1 and Maximum(S) le r1 then
      ;
    elif (Universe(S) cmpeq PowerStructure(Infty)) and AbsoluteDegree(R) eq 1 then 
      S:= [1];
    else
      return false, "Wrong infinite places";
    end if;
    S:= Sort(S);
  end if;
  if not IsIntegral(I) then
    return false, "The ray is not integral";
  end if;

  if Type(Quotient) eq SetEnum then Quotient:= Setseq(Quotient); end if;
  if #Quotient ne 0 then
    T:= Type(Quotient[1]);
    if T in {RngIntElt, FldRatElt} then
      Quotient:= [ ideal< R | x> : x in Quotient ];
    elif T eq RngInt then
      Quotient:= [ ideal< R | Generator(x) > : x in Quotient ];
    elif not ISA(T, RngOrdFracIdl) or Order(Quotient[1]) cmpne R then
      return false, "Incompatible user defined generators";
    end if;
    if exists{ u: u in Quotient | not IsOne(I+u) } then 
      return false, "The user defined generators must be comprime to the ray";
    end if;
  end if;

  if CoprimeTo cmpne 1 then
    if ISA(Type(CoprimeTo), RngElt) then
      ok, CoprimeTo:= IsCoercible(FieldOfFractions(R), CoprimeTo);
      if not ok then return ok, "IscoprimeTo must be an ideal or field element"; end if;
    end if;
  end if;

  L:= [ PowerIdeal(R) | ];
  C, h:= RayClassGroup(I, S);
  C0:= sub< C | {u @@ h : u in Quotient} >;
  if #C0 ne 1 then
    C, hh:= quo< C | C0 >;
    h:= hh^-1 * h;
  end if;

  if Generators then
    n:= #AbelianInvariants(C);	// We will end up with this number of gens.
    U:= sub< C | >;
    p:= 1; i:= 1; D:= [];
    while n ne 0 do
      if i ge #D then p:= NextPrime(p); D:= Decomposition(R, p); i:= 1; end if;
      if (CoprimeTo cmpeq 1 or Valuation( CoprimeTo, D[i,1] ) eq 0) and IsOne(I+D[i,1]) then
        g:= D[i,1] @@ h;
        if g notin U then
          nn:= #AbelianInvariants( quo< C | U, g > );
          if nn ne n then
            assert nn eq n-1;
            n:= nn;
            Append(~L, D[i,1]);
            U:= sub< C | U, g >; 
          end if;
        end if;
      end if;
      i +:= 1;
    end while;
  else
    U:= {@ @};
    p:= 1; i:= 1; D:= [];
    while #U ne #C do
      if i ge #D then p:= NextPrime(p); D:= Decomposition(R, p); i:= 1; end if;
      if (CoprimeTo cmpeq 1 or Valuation( CoprimeTo, D[i,1] ) eq 0) and IsOne(I+D[i,1]) then
        g:= D[i,1] @@ h;
        if g notin U then
          Append(~L, D[i,1]);
          Include(~U, g);
        end if;
      end if;
      i +:= 1;
    end while;

    if Minimal then
      B:= Max([Norm(p): p in L]);
      P:= PrimesUpTo(B-1, NumberField(R): coprime_to:= CoprimeTo * I);
    
      for p in P do
        g:= p @@ h;
        i:= Index(U, g);
        if Norm(p) le Norm(L[i]) then 
          L[i]:= p;
        end if;
      end for;
    end if;
  end if;

  Norms:= [ Norm(p): p in L ];
  ParallelSort(~Norms, ~L);

  return true, L;
end function;

function ClassGroupPrimeIdealGenerators(I, S : CoprimeTo:= 1, Quotient:= [])
 // Returns prime ideals that generate the ray class group of I and the infinite places in S
  ok, L:= CGPrimes(I, S, true, CoprimeTo, true, Quotient);
  if not ok then
      error L;
  end if;
  return L;
end function;

function ExtensionToHeckeCharacter(E)
  assert Degree(E) eq 2;
  K:= BaseField(E);
//  if not IsAbsoluteField(K) then K:= AbsoluteField(K); end if;
  RE:= Integers(E);

  S:= [];
  for i in RealPlaces(K) do
    if #Decomposition(E, i) ne 2 then
      if Type(i) eq Infty then
        idx:= 1;
      else
        ok, idx:= IsInfinite(i); assert ok;
      end if;
      Append(~S, idx);
    end if;
  end for;
  S:= Sort(S);

//  S:= [1..Degree(K)];
  bad:= Type(K) eq FldRat;
  if bad then 
    DE:= Integers( QNF() ) * Discriminant(RE);
  else
    DE:= Discriminant(RE);
  end if;
  P:= ClassGroupPrimeIdealGenerators(DE, S);
  T:= < < p, IsSplit(bad select Minimum(p) else p, RE) select 1 else -1> : p in P >; 
  h:= HeckeCharacter(DE, S, T);
  assert IsPrimitive(h);
  return h;
end function;

function myEval(K, z, Relative)
  if IsOdd(z) then
    k:= 1-z;
    if Type(K) eq FldRat then
      return BernoulliNumber(k)/-k;
    elif Type(K) eq FldQuad then
      d:= Discriminant(Integers(K));
      if d gt 1 then
        return BernoulliNumber(k) * BernoulliNumber(k, KroneckerCharacter(d, Rationals())) / k^2;
      end if;
    end if;
  end if;

  if Relative then
    H:= ExtensionToHeckeCharacter(K);
    L:= LSeries(H);
//    F:= BaseField(K);
//    K:= OptimizedRepresentation(AbsoluteField(K));
//    L:= LSeries(K : Method:= Degree(F) ge 5 select "Direct" else "Default") / LSeries(F);
  else
    L:= LSeries(K);
  end if;

  i:= 0;
  repeat
    if i ge 1 then 
      LSetPrecision(L, 40 + i*20); 
      "increasing precision", i; 
    end if;
    x:= Evaluate(L, z);
    if Type(x) eq FldComElt and Im(x) le 10^-20 then x:= Re(x); end if;
    X:= Type(x) eq FldReElt select { BestApproximation(x, 10^i) : i in [12, 14, 16, 18] } else [];
    i +:= 1;
  until #X eq 1;
  X:= Rep(X);

//  if Relative then
//    assert Abs(Real(Evaluate(LSeries(H), z)) - X) le 10^-10;
//  end if;
  return X;
end function;

function DedekindZetaExact(K, z : Relative := false)
 // Evaluates the Dedekind zeta function of K at the negative integer z
    if not( (Relative and z eq 0) or z lt 0) then
	error "The argument must be a negative integer";
    end if;
    return myEval(K, z, Relative);
end function;

// mass formulas for verifying the genus

function UnitaryMass(L, m)
    L := NumberField(AbsoluteField(L));
    ZZ_L := MaximalOrder(L);
    _,cc := HasComplexConjugate(L);
    // This might fail, for example if cc(L.1) = -L.1...
    // F := sub<L|[L.1+cc(L.1)]>;
    F := FixedField(L, [cc]);
    ZZ_F := MaximalOrder(F);
    d := Degree(L) div 2;
    tau := 2;
    L_rel := ext< F | MinimalPolynomial(L.1, F)>;

    LofM :=  &*[DedekindZetaExact(L_rel,1-r : Relative:=true) :
		r in [1..m] | r mod 2 eq 1]*
	     &*[DedekindZetaExact(F,1-r) : r in [1..m] | r mod 2 eq 0];
    RF := &cat[[x[1] : x in Factorization(p*ZZ_F)] :
	       p in PrimeFactors(Discriminant(ZZ_L))];
    ramified_primes := [I : I in RF |
			Factorization(ideal<ZZ_L|Generators(I)>)[1,2] gt 1];
    RL := [Factorization(ideal<ZZ_L|Generators(I)>)[1,1] :
	   I in ramified_primes];
    
    if (m mod 2 ne 0) then
	qs := [#ResidueClassField(p) : p in RL];
	N := #ramified_primes;
	prod_of_local_factors := (1/2)^N;
    else
	
	// we need -1 to not be a norm in the completion -
	// at odd primes can be checked modulo the prime,
	// at 2 must be checked mod 4
	// These are the invariants that we should check for the module in
	// general
	not_norm := [p : p in RL |
		     (not IsSquare(ResidueClassField(p)!(-1))) or
		     (Norm(p) eq 2)];
	N := #not_norm;
	qs := [#ResidueClassField(p) : p in not_norm];
	prod_of_local_factors := (-1)^(m div 2);
	if not IsEmpty(qs) then
	    prod_of_local_factors *:=
		(1/2)^N * &*[(q^m - 1) / (q + 1) : q in qs];
	end if;
     
    end if;

    mass := 1/2^(m*d)*LofM*tau*prod_of_local_factors;

    return mass;
    
end function;

function WittToHasse(Dim, Det, Finite)
  K:= Parent(Det);
  c:= K ! case < Dim mod 8 | 3: -Det, 4: -Det, 5: -1, 6: -1, 7: Det, 0: Det, default : 1 >;
  return { x[1] : x in Finite | x[2] ne MyHilbertSymbol(K ! -1, c, x[1]) };
end function;

function LocalFactor(g, p)
  q:= Norm(p);
  m:= Ncols(g);
  if IsOdd(m) then
    return &* [ Rationals() | 1-q^(-i): i in [2..m by 2] ];
  end if;
  r:= m div 2;
  f:= &* [ Rationals() | 1-q^(-i): i in [2..m-2 by 2] ];
  d:= Determinant(g) * (-1)^r;
  if IsEven(Valuation(d, p)) then
    P := Type(p) eq RngInt select Norm(p) else p;
    if IsLocalSquare(d, P) then
      f *:= 1-q^(-r);
    else 
      f *:= 1+q^(-r); 
    end if;
  end if;
  return f;
end function;

function Combine(L, p)
  assert Minimum(p) ne 2;
  m:= Rank(L);
  q:= Norm(p);
  _, G, S:= JordanDecomposition(L, p);
//  "called with", #G, "components";
  f:= 1;
  e:= 0;
  Ms:= [Ncols(g) : g in G ];
  for i in [1..#G] do
    T:= i eq 1 select 0 else S[i-1];
    M:= &+Ms[i..#Ms];
    e +:= (S[i]-T) * (M+1)*M/2 - S[i] * Ms[i] *(m+1)/2;
    f *:= LocalFactor(G[i], p);
  end for;
// We already take care of Nr(disc(E/K))^((m-1)/2) globally.
  if IsEven(m) and IsOdd(Valuation(Determinant(InnerProductMatrix(L)), p)) then
    e +:= (m-1)/2;
  end if;
  assert IsIntegral(e);
  e:= Integers() ! e;
  return LocalFactor( DiagonalJoin(< g: g in G >), p) / (2^(#G-1) * f * q^e);
end function;

function WittToHasse2(L, Hasse)
    Witt := {};
    for p in Hasse do
	pR := p[1];
	nProc := BuildNeighborProc(L, pR, 1);
	Vp := L`Vpp[pR]`V;
	if Vp`AnisoDim ne 0 then
	    // the space is not split hyperbolic
	    Include(~Witt, pR);
	end if;
    end for;
    return Witt;
end function;

// !!! Something here is broken, see e.g.
// Q := QuaternaryQuadraticLattices(20)[3][1];
// It gives the same result as Gan-Hanke-Yu,
// but these do not match the actual mass.

function OrthogonalMass(L : Special := false)
// Returns the mass of L
    
  R:= BaseRing(L);
  K:= NumberField(R);

  // TODO: Handle not maximal at 2 and special genus
  D:= Decomposition(R, 2);

  for d in D do
      if not IsMaximalIntegral(L, d[1]) then
        if Type(R) eq RngInt then
	  // over the rationals we can cheat
	  genus_cmd := Special select SpinorGenus else Genus;
	  reps := [LatticeFromLat(r) : r in Representatives(Genus(ZLattice(L)))];
	  return &+[1/#AutomorphismGroupOverField(r, GL(Dimension(L),K) : Special := Special) : r in reps];

        else
	  error "The lattice must be maximal at primes over 2";
        end if;
      end if;
  end for;

  m:= Rank(L);
  Form:= GramMatrixOfBasis(L);
  r:= m div 2;
  Det, Hasse:= QuadraticFormInvariants(Form : Minimize:= false);
  // something is wrong with this WittToHasse using the invariants.
  // We check manually the WittIndex at each of these instead
  // Witt:= WittToHasse(m, Det, Hasse);
  // primes where the Witt-Invariant is not 1
  // Witt := {p[1] : p in Hasse | p[2] ne 1};


  // Mass from infinity and even places.
  mass:= 2^(-AbsoluteDegree(K) * r);
  if IsOdd(m) then
      // Here the old ways worked, so we leave it as they were
      Witt:= WittToHasse(m, Det, Hasse);
      B:= { p: p in BadPrimes(L) } join Witt;
      // B:= { p: p in Witt | Minimum(p) ne 2 };
      B := {p : p in B | Minimum(p) ne 2};
      Witt diff:= B;
      mass *:= &* [ DedekindZetaExact(K, -i) : i in [1..m-2 by 2] ];
      NonUnits:=  { f[1]: f in Factorization(Det*R) | IsOdd(f[2]) and Minimum(f[1]) eq 2 };
      mass *:= &* [ Rationals() | (Norm(p)^r + (p in Witt select -1 else 1)) / 2 : p in NonUnits ];
      Witt diff:= NonUnits;
      mass *:= &* [ Rationals() | (q^(m-1)-1)/(2*(q+1)) where q:= Norm(p) : p in Witt ];
  else
      // Witt:= WittToHasse2(L, Hasse);
      Witt:= WittToHasse(m, Det, Hasse);
      Witt:= { p: p in BadPrimes(L) } join Witt;
      B:= { p: p in Witt | Minimum(p) ne 2 };
      // B := {p : p in B | Minimum(p) ne 2};
      Witt diff:= B;
      Disc:= (-1)^((m*(m-1)) div 2) * Det;
      assert Disc eq (-1)^r * Det;
      mass *:= &* [ Rationals() | DedekindZetaExact(K, -i) : i in [1..m-3 by 2] ];
      if IsSquare(Disc) then
	  mass *:= DedekindZetaExact(K, 1-r);
      else
	  E:= ext< K | Polynomial([-Disc,0,1]) >;
	  mass *:= DedekindZetaExact(E, 1-r : Relative);
	  FD:= [ f: f in Factorization(Discriminant(Integers(E))) | Minimum(f[1]) eq 2 ];
	  // for the odd primes, their contribution will be done using Combine
	  mass /:= 2^#FD;
	  for_removal := {f[1]: f in FD};
	  if ExtendedType(for_removal) eq SetEnum[RngIntElt] then
              for_removal := {ideal<Integers()|x> : x in for_removal};
	  end if;
	  Witt diff:= for_removal;
      end if;
      for p in Witt do
	  P := Type(p) eq RngInt select Norm(p) else p;
	  w:= IsLocalSquare(Disc, P) select -1 else 1;
	  mass *:= (q^(r-1)+w)*(q^r+w)/(2*(q+1)) where q:= Norm(p);
      end for;
      if Special then mass *:= 2; end if;
  end if;

  // Fix odd places which are not unimodular or have Witt invariant -1.
  for p in B do
    mass *:= Combine(L, p);
  end for;

  return Abs(mass);
end function;

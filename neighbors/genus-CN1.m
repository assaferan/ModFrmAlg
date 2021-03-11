freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
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

import "../modfrmalg/modfrmalg.m" : ModFrmAlgInit;
import "neighbor-CN1.m" : BuildNeighborProc, BuildNeighbor, GetNextNeighbor;
import "inv-CN1.m" : Invariant;

// functions

procedure checkNextNeighbor(nProc, buildNeighbor, ~invs, ~isoList
			   : BeCareful := false)

    // Compute the neighbor according to the current state
    //  of the neighbor procedure.
    nLat := buildNeighbor(nProc : BeCareful := BeCareful);

    // A specified invariant of the neighbor lattice.
    inv := Invariant(nLat);

    // If this invariant is defined for the array, we need
    //  to potentially check for isometry.
    if IsDefined(invs, inv) then
       // Retrieve the array for this invariant.
       array := invs[inv];

       // Flag whether we found the right class.
       found := false;
       for i in [1..#array] do
	 // Check for isometry.
	 iso := IsIsometric(array[i][1], nLat);

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
       end if;
    else
       invs[inv] := [ < nLat, #isoList+1 > ];
       Append(~isoList, nLat);
    end if;

end procedure;

function computeGenusRepsAt(p, isoList, invs
		: BeCareful := true, Force := false)
    // The index of the current isometry class being considered.
    isoIdx := 1;

    repeat
	// Build the neighbor procedure for the current lattice.
	nProc := BuildNeighborProc(isoList[isoIdx], p, 1
				   : BeCareful := BeCareful);

	while nProc`isoSubspace ne [] do
	    checkNextNeighbor(nProc, BuildNeighbor,
			      ~invs, ~isoList : BeCareful := BeCareful);
	    // Move on to the next neighbor lattice.
	    GetNextNeighbor(~nProc
			    : BeCareful := BeCareful);
	end while;
	
	// Move on to the next genus representative.
	isoIdx +:= 1;
    until isoIdx gt #isoList;
    
    return isoList, invs;
end function;

forward UnitaryMass, OrthogonalMass;

procedure computeGenusRepsCN1(M : BeCareful := true, Force := false)
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
    invs := AssociativeArray();
    invs[Invariant(Module(M))] := [ < Module(M), 1 > ];

    // Do we need this? Check the ramified primes
    bad_modulus := Numerator(Norm(Discriminant(Module(M))));
    V := ReflexiveSpace(Module(M));
    // something crashes in orthogonal mass
    // until we figure it out we leave it be
/*
    if SpaceType(V) eq "Hermitian" then
	K := BaseRing(V);
	// !!! TODO :
	// replace with the calculation of mass relative to this lattice
	total_mass := UnitaryMass(K, Dimension(Module(M)));
    else
	total_mass := OrthogonalMass(Module(M));
    end if;
*/
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
	    genList, invs := computeGenusRepsAt(
				     ps[idx], genList, invs
				     : BeCareful := BeCareful, Force := Force);

	    // Move to the next prime.
	    idx +:= 1;
	    acc_mass := &+[#AutomorphismGroup(rep)^(-1) : rep in genList];
	until /* (idx gt #ps)  or (acc_mass eq total_mass) */ true;
    until /* acc_mass eq total_mass*/ true;


    // Assign the genus symbol for the space of algebraic modular forms.
    M`genus := New(GenusSym);
    M`genus`Representative := M`L;
    M`genus`Representatives := genList;
    M`genus`RepresentativesAssoc := invs;
end procedure;

function sortGenusCN1(genus)
	// An empty associative array.
	invs := AssociativeArray();

	// An ordered list of genus representatives;
	lats := Representatives(genus);

	for i in [1..#lats] do
		// Compute the invariant associated to this genus rep.
		inv := Invariant(lats[i]);

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

function DedekindZetaExact(K, z : Relative:= false)
    if not ( (Relative and z eq 0) or z lt 0) then
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

function GramMatrixOfBasis(L)
  P:= PseudoBasis(Module(L));
  U:= Universe(P);
  C:= [ U[1] | p[1]: p in P ];
  B:= [ U[2] | p[2]: p in P ] ;
  return GramMatrix( L, B ), C, B;
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
    if IsLocalSquare(d, p) then
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

function OrthogonalMass(L)
// Returns the mass of L
    
    R:= BaseRing(L);
    K:= NumberField(R);

  // TODO:
  D:= Decomposition(R, 2);
  for d in D do
      if not IsMaximalIntegral(L, d[1]) then
	  // commented out for it not to interfere at the moment.
	  // error "The lattice must be maximal at primes over 2";
	  return 0;
      end if;
  end for;

  m:= Rank(L);
  Form:= GramMatrixOfBasis(L);
  r:= m div 2;
  Det, Hasse:= QuadraticFormInvariants(Form : Minimize:= false);
  Witt:= WittToHasse(m, Det, Hasse);

  B:= { p: p in BadPrimes(L) } join Witt;
  B:= { p: p in B | Minimum(p) ne 2 };
  Witt diff:= B;

  // Mass from infinity and even places.
  mass:= 2^(-AbsoluteDegree(K) * r);
  if IsOdd(m) then
    mass *:= &* [ DedekindZetaExact(K, -i) : i in [1..m-2 by 2] ];
    NonUnits:=  { f[1]: f in Factorization(Det*R) | IsOdd(f[2]) and Minimum(f[1]) eq 2 };
    mass *:= &* [ Rationals() | (Norm(p)^r + (p in Witt select -1 else 1)) / 2 : p in NonUnits ];
    Witt diff:= NonUnits;
    mass *:= &* [ Rationals() | (q^(m-1)-1)/(2*(q+1)) where q:= Norm(p) : p in Witt ];
  else
    Disc:= (-1)^((m*(m-1)) div 2) * Det;
    assert Disc eq (-1)^r * Det;
    mass *:= &* [ Rationals() | DedekindZetaExact(K, -i) : i in [1..m-3 by 2] ];
    if IsSquare(Disc) then
      mass *:= DedekindZetaExact(K, 1-r);
    else
      E:= ext< K | Polynomial([-Disc,0,1]) >;
      mass *:= DedekindZetaExact(E, 1-r : Relative);
      FD:= [ f: f in Factorization(Discriminant(Integers(E))) | Minimum(f[1]) eq 2 ];		// TODO:: Remove odd places.
      mass /:= 2^#FD;
      Witt diff:= {f[1]: f in FD};
    end if;
    for p in Witt do
      w:= IsLocalSquare(Disc, p) select -1 else 1;
      mass *:= (q^(r-1)+w)*(q^r+w)/(2*(q+1)) where q:= Norm(p);
    end for;
  end if;

  // Fix odd places which are not unimodular or have Witt invariant -1.
  for p in B do
    mass *:= Combine(L, p);
  end for;

  return Abs(mass);
end function;

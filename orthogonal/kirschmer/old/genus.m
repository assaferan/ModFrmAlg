//freeze;
SetDebugOnError(true);


/***********************************************
*                                              *
* Spinor genera of lattices over number fields *
* BONGs of lattices over number fields         *
* Genera of lattices over number fields        *
*                                              *
* 2015 D. Lorch                                *
*                                              *
***********************************************/

// we fix some primes for the genus computations and add them as a global property of the field / lattice:
AddAttribute(FldNum, "ClassGroup");
AddAttribute(FldNum, "ClassGroupHom");
AddAttribute(FldNum, "LookupTable");

declare attributes LatMod:
  RCG,homRCG,M,MM,CriticalPrimes,ClassSubgroup,FactorGroup,FactorGroupHom,ListOfFinitePlaces;

import "lat.m": GetExtra;
  
// 0. Basic things which might later be turned into intrinsics:


function MyIsIsometric(L1, L2: Decomposition)
  return IsIsometric(L1, L2); // do not pass Decomposition parameter -- the function will decide on its own whether to turn it on or off
end function;

function CriticalPrimesOfField(K)
  // calculate a set S of representatives of CL^+(F), where F is the underlying field of L.
  // These are then stored in attributes of L, permanently even though L is only passed
  // as a function parameter.
  // 
  // The critical primes are important for the Watson-style transformations
  // (i.e., these are not possible on critical primes.).
  assert Type(K) eq FldNum;
  // printf "Calculating lookup table.\n";  
  // error if assigned (L`LookupTable), "please do not call this function again.";
  if (assigned (K`LookupTable)) then
     assert (#Keys(K`LookupTable) gt 0) or (#NarrowClassGroup(K) eq 1);
     return [ K`LookupTable[i]: i in Keys(K`LookupTable) ];
  end if;
  
  
  G, h := NarrowClassGroup(K);
  R := Integers(K);
  
  // we could do this:
  // S := [<g, g@h>: g in G | Order(g) ne 1];
  // but then the generators are not necessarily prime ideals. 
  // We want them to be prime ideals, so that we have to do only one correction at one other place!
  // So instead we map prime ideals into the class group until every element has been found:
  CGprimes := ClassGroupPrimeIdealRepresentatives(1*R, InfinitePlaces(K));
    
  K`LookupTable := AssociativeArray();
  // L`LookupTable[G!0] := BaseRing(L)!1;
  for c in CGprimes do 
    if Order(c@@h) gt 1 then
      // do not add a prime ideal as representative for the trivial class, this just leads to confusion.
      K`LookupTable[c@@h] := c; 
    end if;
    
    
  end for;
  
  K`ClassGroup := G;
  K`ClassGroupHom := h;

  // We really need to fix more than this:
  // - the narrow class group G = CL^+(F)
  // - a homomorphism h into that group
  // - a list <g, product of prime ideals that maps to g> for every g in G
  /* s := (((p@@h)@h));
  // Rescale with a totally positive generator of p*w^(-1), where w is a product of elements in S s.th. p*w^(-1) is trivial in the narrow class group.
  q := s * p;
  assert IsPrincipal(q);
  ok, x := HasTotallyPositiveGenerator(q);
  */
  
    
  return [K`LookupTable[i]: i in Keys(K`LookupTable)];
end function;

function ClassGroupLookup(K, p)
  // error if not assigned(L`LookupTable), "please call CriticalPrimesOfLattice first.";

  // return a prime element s that inverts p in the class group.
  
  // let's make sure that the lookup table has been initialized:
  // c := p@@L`ClassGroupHom;
  if not(assigned K`LookupTable) or not(p@@K`ClassGroupHom in Keys(K`LookupTable)) then
    crit := CriticalPrimesOfField(K);
    assert(Order(c) eq 1) or (c in Keys(K`LookupTable)) where c is p@@K`ClassGroupHom; // yes, this is how Magma works -.- attributes are object-permanent.
  end if;

    // p is mapped to a class group element c:
  c := p@@K`ClassGroupHom;
  if (Order(c) eq 1) then return 1; end if;
  
  return K`LookupTable[c];
end function;

intrinsic IsCriticalPrimeOfField(K::FldNum, p::RngOrdIdl) -> BoolElt
{returns true iff p is a member of an internal set of representatives for the ray class group of K.}
  require Order(p) cmpeq Integers(K) : "Incompatible arguments.";
  // let's make sure that the lookup table has been initialized:
  return (p cmpeq ClassGroupLookup(K, p));
end intrinsic;



function MatrixFromBlocks(List)
  M := List[1];
  for i in [2..#List] do M := DiagonalJoin(M, List[i]); end for;
  return M;
end function;

function DetailedJordanSplitting(M, F, p)
  O:= Order(p);
  even:= Minimum(p) eq 2;
  if even then pi:= PrimitiveElement(p); end if;
//  B:= LocalBasis(M, p: Type:= "Submodule");
  B:= LocalBasis(M, p);
  n:= Ncols(F);
  k:= 1;

  oldval:= Infinity();
  Blocks:= []; Exponents:= [];
  Steps_temp := [];
  S:= Matrix(B);
  Steps := []; // list of numbers of base vectors forming the 1x1 or 2x2 matrices that comprise the Jordan decomposition
  while k le n do
    G:= S*F*Transpose(S);

    // find an element <i, j> with minimal p-valuation.
    // Take it from the diagonal, if possible, and from the lowest-possible row number.
    X:= [ Valuation(G[i,i], p): i in [k..n] ];
    m, ii:= Minimum( X ); ii +:= k-1;
    pair:= <ii, ii>;

    for i in [k..n], j in [i+1..n] do
      tmp:= Valuation(G[i,j], p);
      if tmp lt m then m:= tmp; pair:= <i,j>; end if;
    end for;
    if m ne oldval then Append(~Blocks, k); oldval:= m; Append(~Exponents, m); end if;

    if even and pair[1] ne pair[2] then
//      printf "2 has no inverse, <%o,%o>\n", pair[1], pair[2];
//      printf "S=%o\n", print_matrix(ChangeRing(S, Integers()));

      SwapRows(~S, pair[1],   k); // swap f_1 and e_i
      SwapRows(~S, pair[2], k+1); // swap f_2 and e_j

//      Append(~Steps, [k, k+1]);
      T12:= (S[k] * F * Matrix(1, Eltseq(S[k+1])))[1];
      S[k] *:= pi^Valuation(T12, p)/T12;
      T := func<i,j|(S[i] * F * Matrix(1, Eltseq(S[j])))[1]>;
      T11 := T(k,k); T22 := T(k+1, k+1); T12:= T(k, k+1);

//      printf "d=%o*%o - %o\n", T(1,1),T(2,2), T(1,2)^2;
      d := T11*T22 - T12^2;
      for l in [k+2..n] do
        tl := T12*T(k+1,l)-T22*T(k  ,l); // t_k from step 4
        ul := T12*T(k  ,l)-T11*T(k+1,l); // u_k from step 4
        S[l] +:= (tl/d)*S[k] + (ul/d)*S[k+1];
      end for;
      k +:= 2;
      Append(~Steps_temp, 2);
    else
//      printf "pair is %o\n", pair;
      if pair[1] eq pair[2] then
//        printf "swapping %o and %o\n", pair[1], k;
        SwapRows(~S, pair[1], k);
//        Append(~Steps, [k]);
      else
//        printf "adding %o to $o\n", pair[2], pair[1];
        S[pair[1]] +:= S[pair[2]];
        SwapRows(~S, pair[1], k);
//        Append(~Steps, [k]);
      end if;
      nrm:= (S[k] * F * Matrix(1, Eltseq(S[k])))[1];
//      printf "nrm = %o\n", nrm;
      X:= S[k] * F * Transpose(S); // T(e_k, f_i), 1<=i<=n
//      printf "renorming %o..%o\n", k+1, n;
      for l in [k+1..n] do S[l] -:= X[l]/nrm * S[k]; end for;
      k+:= 1;
      Append(~Steps_temp, 1);
    end if;
  end while;

  Append(~Blocks, n+1);
  Matrices:= [* RowSubmatrix(S, Blocks[i], Blocks[i+1] - Blocks[i]) : i in [1..#Blocks-1] *];
  
  Steps := [];
  j := 1;
  for i in [1..#Blocks-1] do 
    // return a finer decomposition of the blocks into 1x1 and 2x2 matrices:
    start := Blocks[i];
    len := Blocks[i+1]-Blocks[i];
    while len gt 0 do
      if Steps_temp[j] eq 2 then Append(~Steps, [start, start+1]); len -:= 2; start +:= 2; else Append(~Steps, [start]); len -:= 1; start +:= 1; end if;
      j +:= 1;
    end while;
    ///if Blocks[i+1] eq Blocks[i]+1 then Append(~Steps, [Blocks[i]]); else Append(~Steps, [Blocks[i], Blocks[i]+1]); end if; 
  end for;
  //printf "Steps_temp = %o\n", Steps_temp;
  return Matrices, [* m*F*Transpose(m): m in Matrices *], Exponents, Blocks, Steps;
end function;

function DetailedJordanDecomposition(L, p)
  return DetailedJordanSplitting(L`Module, L`Form, p); 
end function;



function ScalesAndNorms(G, p, Uniformizer)
  e := RamificationIndex(p);
  sL := [Minimum({Valuation(g[i,j], p): i in [1..j], j in [1..Ncols(g)]}): g in G];

  aL:= []; uL:= []; wL:= [];
  sL := [Minimum({Valuation(x, p): x in Eltseq(g)}): g in G];
  for i in [1..#G] do
    // similar, but not equal to, the code for obtaining a genus symbol
    // (for the genus symbol, we consider a scaling L^(s(L_i)) in O'Meara's notation)
    GG := G[i];

    D:= Diagonal(GG);
    // 2*s(L_i) eq n_i?
    if e+sL[i] le Minimum({ Valuation(d, p) : d in D }) then
      Append(~aL, FieldOfFractions(Order(p))!Uniformizer^(e+sL[i]));
    else
      Append(~aL, D[b] where _, b is Minimum([Valuation(x,p): x in D]));
    end if;
    Append(~uL, Valuation(aL[i], p));
    assert uL[i] eq Valuation(Norm(LatticeModule(G[i])), p);
    Append(~wL, Minimum({e+sL[i]} join {uL[i] + QuadraticDefect(d/aL[i], p): d in D}));
  end for;

  return sL, aL, uL, wL; // scales, norm generators, norm valuations, weight valuations
end function;


function NormUpscaled(G, p: Debug:=false)
  // calculate Norm(L^{scale(L_i)}), for all i.
  // for def. of L^{a}, cf. § 82 I, p.237, in O'Meara
  
    
  // G is a splitting of a LatticeModule L into Gram matrices,
  // which can e.g. be calculated by JordanDecomposition(), but need not
  // be a Jordan decomposition.
  
    t:= #G;
    sL := [Minimum({Valuation(g[i,j], p): i in [1..j], j in [1..Ncols(g)]}): g in G];
    e := RamificationIndex(p);
    Uniformizer := UniformizingElement(p);
    
    aL:= []; uL:= []; wL:= [];
    for i in [1..t] do
      // Die Norm ist 2*Scale + <die Ideale die von den Diagonalelementen erzeugt werden>, cf. § 94 O'Meara.
      GG:= DiagonalJoin(< j lt i select Uniformizer^(2*(sL[i]-sL[j])) * G[j] else G[j] : j in [1..t] >);
      D:= Diagonal(GG);
      // Is 2*s(L_i) eq n_i? (We always have scale \supseteq norm \supseteq 2*scale)
      if Debug then printf "val(2*scale) = %o, val(diagonal)=%o\n", e+sL[i], Minimum({ Valuation(d, p) : d in D }); end if;
      // um einen Normerzeuger zu finden, muss man einfach Erzeuger des größeren der Ideale 2*Scale bzw. <Diagonalelemente> nehmen:
      if e+sL[i] le Minimum({ Valuation(d, p) : d in D }) then
        // 20150505: note that "le", not "eq", is correct here (we are not comparing 2*s(L) with norm(L), but 2*s(L) with only the diagonal elements).
        // 2*scale ist das größere Ideal
        if Debug then printf "NU: case 1\n"; end if;
        Append(~aL, FieldOfFractions(Order(p))!Uniformizer^(e+sL[i]));
      else
        // die Diagonalelemente bilden das größere Ideal:
        if Debug then printf "NU: case 2\n"; end if;
        Append(~aL, D[b] where _, b is Minimum([Valuation(x,p): x in D]));
      end if;
      Append(~uL, Valuation(aL[i], p));
      // Append(~wL, Minimum({e+sL[i]} join {uL[i] + QuadraticDefect(d/aL[i], p): d in D}));
    end for;

 // uL: the valuations of the upscaled norms
 // aL: the generators of the upscaled norms
 return uL, aL;
end function;

function MyDirectSum(LL)
  error if not Type(LL) eq SeqEnum, "must supply a list";
  error if #LL lt 1, "list is empty";
  K := LL[1];
  
  for j in [2..#LL] do if Rank(LL[j]) gt 0 then K := DirectSum(K, LL[j]); end if; end for;
  return K;
end function;

function IsSquarefreeLattice(L, p)
  // L any LatticeModule
   _,_,E := JordanDecomposition(L, p);
  return Set(E) subset {0, 1};
  // return (IsElementaryAbelian(Q)) and (Order(Q) mod Minimum(p) eq 0) where Q is QuoLat(Dual(L), L);
end function;

function IsSquarefreeLatticeEverywhere(L)
  //return &and[IsSquarefreeLattice(L, p): p in BadPrimes(L)];
  badP := [];
  for p in BadPrimes(L) do if not IsSquarefreeLattice(L, p) then Append(~badP, p); end if; end for;
  return #badP eq 0, badP;
end function;

function IsPrimitiveLattice(L, p)
assert Minimum(p) eq 2;
  dims, scale := GenusSymbol(L, p);
  return (Set(scale) subset {0,1}) and (dims[1] le (Rank(L)/2));
end function;

intrinsic IsUnverzweigt(L::LatMod, p::RngOrdIdl) -> BoolElt
{ check whether L is unimodular at p and Norm(L) equals 2*Scale(L) at p. }
  // see Pfeuffer, p.11
  return IsUnimodular(L, p) and (Valuation(Norm(L), p) eq Valuation(2*Scale(L), p));
end intrinsic;

intrinsic IsUnverzweigtEverywhere(L::LatMod) -> BoolElt
{ check that L is unimodular and that IsUnverzweigt(L, p) for every p over 2 }
  if #[b: b in BadPrimes(L) | Minimum(b) ne 2] gt 0 then return false; end if;
  return &and[IsUnverzweigt(L, p):  p in [x[1]: x in Factorization(2*Integers(BaseRing(L)))]];
end intrinsic;

  
// 1. BONGs and good BONGs, as defined by C. Beli:

intrinsic RelativeQuadraticDefect(a::RngElt, p::RngOrdIdl) -> RngIntElt
{Returns the valuation of the relative quadratic defect of a at the prime ideal p, as defined by C. Beli}
  q := QuadraticDefect(a, p);
  return q eq Infinity() select Infinity() else q - Valuation(a, p);
end intrinsic;

function IsInA(a, p) // needed for G_function
  e := Valuation(Order(p)!2, p);
 // cf. Lemma 3.5 in Beli: A is the set of all a \in F^* for which either (-a\not\in (F^*)^2 and D(-a) \subseteq O_p) or (-a\in (F^*)^2 and ord(a)\geq -2e).
  if (Type(QuadraticDefect(-a, p)) ne Infty) and (QuadraticDefect(-a, p) ge 0) then return true; end if;
  if (Type(QuadraticDefect(-a, p)) eq Infty) and (Valuation(a, p) ge -2*e) then return true; end if;
  return false;
end function;


function HasPropertyA(L, p) // needed for SpinorNorm
  error if not Minimum(p) eq 2, "property A only applies to lattices over dyadic fields";
  sL, wL, nL, fL, G := GenusSymbol(L, p); 
  //nL := [Valuation(aL[i], p): i in [1..#aL]];

  _, G, _ := JordanDecomposition(L, p);
  for i in [1..#G] do if Rank(G[i]) gt 2 then
    vprintf User1 : "[at a prime over 2]: property A is violated because there is a %o-dimensional Jordan component\n", Rank(G[i]);
    return false;
  end if; end for;
  
  // GenusSymbol: sL, wL, aL, fL, G, note that aL only contains valuations
  for i in [1..#sL] do for j in [i+1..#sL] do
    if not ((0 lt nL[j] - nL[i]) and (nL[j] - nL[i] lt 2*(sL[j] - sL[i]))) then
    vprintf User1 : "[at a prime over 2]: property A is violated at %o, %o (norm/scale valuations do not fit)\n", i, j;
    return false; 
    end if;
  end for; end for;
  return true;
end function;

function N_function(a, b, g, p)
  // b is a@@g, g is the mapping obtained by LocalMultiplicativeGroupModSquares(p).
  // Both are expensive to calculate, so we pass them as arguments.


  // project a into F^*/(O^*)^2:
  V := Parent(b);  // Full F_2-vector space of some dimension over GF(2)

  // treat the squares separately:
  if QuadraticDefect(a, p) eq Infinity() then return V; end if;

  B := Basis(V);
  
  // cf. paragraph before 1.2 in Beli 2003:
  // N(a) := N(F(\sqrt(a))/F), i.e. the values of the norm mapping of the quadratic extension
  // and N(a) is the orthogonal complement of (<a>(F^*)^2). 
  preimages := V!0;
  for i in [1..#B] do
    b := B[i];
    preim := b@g;
    // convert the Hasse symbol (as an element of the multiplicative group C_2)
    // to an element of the additive group F_2:
    // printf "Hilbert symbol with %o-th basis vector: %o\n", Index(B, b), HilbertSymbol(a, preim, p);
    preimages[i] := HilbertSymbol(a, preim, p) eq 1 select 0 else 1;
  end for;
  KernelGenerators := {B[i]: i in [1..#B] | preimages[i] eq 0};
  // (this fails if a is a square)
  j := Min({i: i in [1..#B] | preimages[i] eq 1});
  KernelGenerators join:= {B[i] + B[j]: i in [1..#B] | (preimages[i] eq 1) and (i ne j)};

  return sub<V | KernelGenerators>;
end function;

function G_function(a, V, g, p)
  // use LocalMultiplicativeGroupModSquares to calculate in F*/(O^*)^2
  // (or F^*/(F^*)^2 -- the last component of the result is the p-valuation
  // mod 2, and  F^*/(F^*)^2 =  F*/(O^*)^2 \times C_2.)
  // Also we expect V, g = LocalMultiplicativeGroupModSquares(p);

 // cf. Beli 2003, Def. 4.
  

  U := UnitSquareClassReps(p);
  assert U[1] eq 1;

  //b := a@@g;
  e := Valuation(Order(p)!2, p);
  R := Valuation(a, p);
  d := RelativeQuadraticDefect(-a, p);
  pi := UniformizingElement(p);
 
  if not IsInA(a, p) then     vprintf User1 : "G_function, case F\n"; return N_function(-a, (-a)@@g, g, p);
  elif ((-1/4)@@g eq a@@g) then     vprintf User1 : "G_function, case G\n"; return sub<V|[V.i: i in [1..Dimension(V)-1]]>;
  elif (R gt 4*e) then     vprintf User1 : "G_function, case H\n"; return sub<V| a@@g>;
  elif (2*e lt R) and (R le 4*e) then
    if (d le 2*e - R/2) then
    vprintf User1 : "G_function, case A\n";
      return (sub<V| (a@@g)> + sub<V|(1 + pi^(R + d - 2*e))@@g>) meet N_function(-a, (-a)@@g, g, p);
    else
    vprintf User1 : "G_function, case B\n";
    assert GF(2)!R eq 0;
      return (sub<V| (a@@g)> + sub<V|(1 + pi^(R/2))@@g>);
    end if;
  elif (R le 2*e) then 
    // printf "e = %o, R = %o, d = %o\n", e, R, d;
    if (d le e - R/2) then
    vprintf User1 : "G_function, case C\n";

    return N_function(-a, (-a)@@g, g, p);
    elif (e - R/2 lt d) and (d le 3*e/2 - R/4) then
      assert R mod 2 eq 0;
    vprintf User1 : "G_function, case D\n";

      return N_function(-a, (-a)@@g, g, p) meet sub<V| (1 + pi^(IntegerRing()!(R/2) + d - e))@@g>;
    else
    vprintf User1 : "G_function, case E\n";

    //assert R mod 4 eq 0;
      //assert e mod 2 eq 0;
      // attention! Use the Floor function wherever Beli writes stuff in square brackets. This is due to his citing Hsia's papers, which have this convention.
      return sub<V| (1 + pi^(e - (Floor(e/2 - R/4))))@@g>;
    end if;
  else error "this never happens.";
  end if;
end function;


intrinsic IsGoodBONG(BONG::[], p::RngOrdIdl) -> BoolElt
{Returns true iff BONG is a good BONG at p, as defined by C. Beli.}
  // Given: a BONG of a LatticeModule L at prime p.
  v := &and[Valuation(BONG[i], p) le Valuation(BONG[i+2], p): i in [1..#BONG-2]]; 
  return v;
end intrinsic;

procedure beli_correction(L, ~G, ~JJ, Steps, i, j, p);
  // this is helper procedure for MakeGoodBONG().
  // Correct the Jordan components with number i and j of L from the Jordan decomposition given in G and JJ,
  // in such a way that the new component with number i has maximal norm. 
  assert #Steps[i] eq 2;

  // for debugging:
  NU := NormUpscaled(G, p);
  // assert orthogonality of the vectors in JJ[Steps[i]] and those in JJ[Steps[j]], i.e. those that make up G[i] and G[j]:
  if Nrows(G[j]) eq 2 then assert IsZero( C*L`Form*Transpose(B) where B is RowSubmatrix(JJ, [Steps[i][1], Steps[i][2]]) where C is  RowSubmatrix(JJ, [Steps[j][2]])); end if;

  assert NU[i] lt Valuation(Norm(LatticeModule(G[i])), p); // hier ist die Normbedingung verletzt
  assert NU[j] le Valuation(Norm(LatticeModule(G[j])), p); // und das "<=" gilt sowieso immer, sonst ist etwas kaputt

  // we will need the original Gram matrix for re-orthogonalization:
  GI := G[i]^(-1); // over the quotient field
  assert #Steps[j] in [1,2];
  
  
  // if G[j] is two-dimensional, make sure that a norm generator is on the [1,1] position:
  if (Ncols(G[j]) eq 2) and (Valuation(G[j][1,1], p) gt Valuation(G[j][2,2], p)) then
    temp := JJ[Steps[j][1]];
    JJ[Steps[j][1]] := JJ[Steps[j][2]];
    JJ[Steps[j][2]] := temp;
    G[j] := B*L`Form*Transpose(B) where B is RowSubmatrix(JJ, [Steps[j][1]..Steps[j][#Steps[j]]]);
  end if;

  JJ[Steps[i][1]] +:= JJ[Steps[j][1]];
  
  // update Gram matrix for component #i:
  G[i] := B*L`Form*Transpose(B) where B is RowSubmatrix(JJ, [Steps[i][1], Steps[i][2]]);
  x := JJ[Steps[i][1]];
  y := JJ[Steps[i][2]];
  // Ansatz: v = JJ[Steps[j][1]] + lambda*x + mu*y
  
  // re-orthogonalize the first basis vector of G[j]:
  v := Vector([-G[j][1,1], 0]) * GI; // G[j][1,1] is always non-zero (the lattice is definite)

  // assert integrality at p:
  assert &and[Valuation(v[k], p) ge 0: k in [1..Ncols(v)]];
  JJ[Steps[j][1]] +:= v[1]*JJ[Steps[i][1]] + v[2]*JJ[Steps[i][2]];
  
  // if applicable, re-orthogonalize the second basis vector of G[j]:
  if Ncols(G[j]) eq 2 then
    w := Vector([-G[j][1,2], 0]) * GI; // G[j][1,2] is always non-zero (or else the lattice would have been further decomposed into two 1x1-lattices here)
    assert &and[Valuation(v[k], p) ge 0: k in [1..Ncols(w)]];
    JJ[Steps[j][2]] +:= w[1]*JJ[Steps[i][1]] + w[2]*JJ[Steps[i][2]];
  end if;

  // update Gram matrix for component #j:
  G[j] := B*L`Form*Transpose(B) where B is RowSubmatrix(JJ, [Steps[j][1]..Steps[j][#Steps[j]]]);

  assert Valuation(Norm(LatticeModule(G[i])), p) eq NU[i];
end procedure;

function IsMaximalNormSplittingInternal(GramMatrices, Scales, Norms, Dimensions, p)
  // Scales: list of valuations of scales
  // Norms: list of generators of norms
  // Dimensions: list of dimensions of Jordan components
  // occurring in a Genus symbol of L at p, as calculated
  // by GenusSymbol(L, p). 

  Norms := [Valuation(Norms[i], p): i in [1..#Norms]];

  // test if each component is either unary or binary:
  fail := exists(i){i: i in [1..#Dimensions] | not(Dimensions[i] in {1,2})};
  if fail then 
    //printf "fail: components are not all unary or binary\n";
    return false, -i, {}; 
  end if;

  // test if binary components are modular:
  fail := exists(i){i: i in [1..#GramMatrices] | #E ne 1 where _,_,E is JordanDecomposition(LatticeModule(GramMatrices[i]), p)};
  if fail then
    //printf "fail: at least one of the binary components is not modular\n";
    return false, -i, {}; 
  end if;
  

  // test if sL[1] \supseteq sL[2] \supseteq ... \supseteq sL[#sL]:
  for i in [1..#Scales-1] do if (Scales[i] gt Scales[i+1]) then 
    printf "FAIL: scale condition at components %o/%o not met, perhaps something is wrong with your lattice?\nFor your reference, the scale valuations are %o", i, i+1, Scales;
    return false, 0, {}; end if; 
  end for;

  // test if nL[i] = n(L^{sL[i]}):
  NU, _ := NormUpscaled(GramMatrices, p);
// printf "given: Scales = %o\nNorms=%o\nDimensions=%o\nNormUpscaled=%o\n", Scales, Norms, Dimensions, NU;
  failset := {}; // for testing purposes, we count the components that do not have maximal norm
  for i in [1..#Scales] do
    assert NU[i] le Norms[i];
    if NU[i] lt Norms[i] then 
      //printf "fail: norm condition at component %o\n", i;
      Include(~failset, i);
    end if;
  end for;
  if #failset gt 0 then return false, SetToSequence(failset)[1], failset; end if;
  return true, 0, {};  
end function;

intrinsic IsMaximalNormSplitting(G::[], p::RngOrdIdl) -> BoolElt
{returns true iff the given list G of Gram matrices corresponds to a maximal norm splitting at p.}
  sL, aL, _, _ := ScalesAndNorms(G, p, UniformizingElement(p));   
  Dimensions := [Nrows(a): a in G];
  return IsMaximalNormSplittingInternal(G, sL, aL, Dimensions, p);
end intrinsic;

intrinsic MaximalNormSplitting(L::LatMod, p::RngOrdIdl) -> [], []
{A maximal norm splitting of L at a dyadic prime p, as defined by C. Beli. Returns a Jordan decomposition into 1x1 and 2x2 components, and the corresponding list of basis vectors.}
  // we follow Beli, "Representation of Integral Quadratic Forms over Dyadic Local Fields", section 7

  require Order(p) cmpeq BaseRing(L) : "Incompatible arguments";
  require Minimum(p) eq 2 : "p must be a dyadic prime.";

  R := Order(p);
  e := RamificationIndex(p);
  Uniformizer := PrimitiveElement(p);

  // we can use the additional values returned by DetailedJordanDecomposition to 
  // further decompose a Jordan decomposition into unary and binary components:

  //  dims, sL, wL, aL, fL, _ := GenusSymbol(L, p);
  JJJ, JG, JE, Blocks, Steps := DetailedJordanDecomposition(L, p);
  // join JJJ into one matrix of base vectors:
  JJ := Matrix(&cat[[J[i]: i in [1..Nrows(J)]]: J in JJJ]);


  // join the individual Gram matrices:
  A := MatrixFromBlocks(JG);

  // read the finer decomposition:
  G := [* *];
  for i in [1..#Steps] do
    // are we in a 1x1 or in a 2x2 block?
    if #Steps[i] eq 1 then
      AA := SubmatrixRange(A, j,j,j,j) where j is Steps[i][1];
      Append(~G, AA);
    elif #Steps[i] eq 2 then
      AA := SubmatrixRange(A, j,j,j+1,j+1) where j is Steps[i][1];
      assert Steps[i][2] eq Steps[i][1] + 1;
      Append(~G, AA);
    else
      assert false;
    end if;
  end for;
  Dimensions := [Nrows(a): a in G];
  assert SequenceToSet(Dimensions) subset {1,2};
  assert &+Dimensions eq Rank(L);
  
  delete A;
  
  // now turn this decomposition into unary/binary components into a maximal norm splitting:
  failset := {};
  while true do
    // Scale valuations sL, Norm generators aL, Norm valuations uL,
    // weight valuations wL of the decomposition:
    sL, aL, uL, wL := ScalesAndNorms(G, p, Uniformizer); 

    failset_old := failset;
    b, i, failset := IsMaximalNormSplittingInternal(G, sL, aL, Dimensions, p);
    assert (failset_old eq {}) or (#failset_old gt #failset);
    if b then break; end if; // maximal norm splitting reached!
    assert i gt 0; // if b is false and i=0, something is wrong with our lattice

    // here comes the interesting stuff:
    assert #Steps[i] eq 2; // unary components already have maximal norm.
  
    // the maximal norm splitting condition is violated at index i.
    find_j := [Valuation(aL[k], p): k in [i+1..#aL]] cat [2*(sL[i] - sL[k]) + Valuation(aL[k], p): k in [1..i-1]];
    assert #find_j gt 0;
    min, j := Minimum(find_j);
    delete find_j;

    if j le #aL - i then
      j := j + i;  // we want j to correspond to a Jordan component, not an index in find_j
      assert j gt i;

      // This is case 1 in Beli.
      beli_correction(L, ~G, ~JJ, Steps, i, j, p); 
    else 
      j := j - (#aL - i); // we want j to correspond to a Jordan component, not an index in find_j
      assert j lt i;
      
      // This is case 2 in Beli.
      // switch to a basis of the dual lattice L^#: 
      for k in [1..#Steps] do 
        for l in [1..#Steps[k]] do 
          JJ[Steps[k][l]] *:= Uniformizer^(-sL[k]); 
        end for; 
        assert Valuation(Scale(LatticeModule(B*L`Form*Transpose(B))), p) eq -sL[k] where B is RowSubmatrix(JJ, [Steps[k][1]..Steps[k][#Steps[k]]]);
      end for;

      // apply case 1 to the reversed orthogonal sum of the dual lattices:
      
      Steps := Reverse(Steps);
      // update Gram matrices for the reversed, dualized lattice:
      for k in [1..#G] do 
        G[k] :=  B*L`Form*Transpose(B) where B is RowSubmatrix(JJ, [Steps[k][1]..Steps[k][#Steps[k]]]);
        assert Nrows(G[k]) in {1,2};
      end for;
      
      assert #Steps[#aL - i + 1] eq 2; // component i is now at position #aL-i+1
      
      beli_correction(L, ~G, ~JJ, Steps, #aL - i + 1, #aL - j + 1, p);

      Steps := Reverse(Steps);
      G := Reverse(G); 

      /// I think nothing will fail if these are not equal:
      /// assert #Steps eq #G; // 20150311 if this fails, nothing is wrong. We just need to fix the code to read off the dimensions of the G[i] instead of relying on Steps.
      
      // update norms/scales from the updated Gram matrices:
      sL, aL, uL, wL := ScalesAndNorms(G, p, Uniformizer); 
      // dualize again:
      for k in [1..#Steps] do for l in [1..#Steps[k]] do 
        JJ[Steps[k][l]] *:= Uniformizer^(-sL[k]); 
      end for; end for;

      // update Gram matrices:
      for k in [1..#G] do 
        G[k] :=  B*L`Form*Transpose(B) where B is RowSubmatrix(JJ, [Steps[k][1]..Steps[k][#Steps[k]]]);
        assert Nrows(G[k]) in {1,2};
      end for;
      
    end if;
  end while;

  assert &and[Nrows(G[k]) in {1,2}: k in [1..#G]];
  return G, JJ;
end intrinsic;


function MakeBONGdim2(L, p);
  // cf. Beli, Lemma 3.3
  // return a BONG of a 2-dimensional lattice.

  assert Rank(L) eq 2;
  
  _,G,E := JordanDecomposition(L, p); 
  assert (#E eq 1) and (#G eq 1); // must be a modular lattice
  r := E[1]; // L is p^r-modular
  
  pi := UniformizingElement(p);
  R := Order(p);
  
  A := G[1];
  
  // is the (1,1) entry a norm generator?
  if Valuation(A[1,1], p) ne Valuation(Norm(L), p) then
    // swap stuff around so that the (1,1) entry will be a norm generator
    b := exists{i: i in [1..Rank(A)] | Valuation(A[i,i], p) eq Valuation(Norm(L), p)};
    if b then
      B := LocalBasis(L`Module, p);
      S := Matrix(B);
      SwapRows(~S, 1, 2);
    else
      B:= LocalBasis(L`Module, p);
      S:= Matrix(B);
      S[1] +:= S[2];
    end if;
    A := S*L`Form*Transpose(S);
    L_old := L;
    L := LatticeModule(A);
    assert Valuation(A[1,1], p) eq Valuation(Norm(L), p);
  end if;
  
  n := A[1,1];
  
  // die p-Bewertung der Determinante muss gerade sein:
  disc := A[1,1]*A[2,2]- A[2,1]*A[1,2];
  val := Valuation(disc, p);
  assert GF(2)!val eq 0;
  assert Valuation(disc, p) eq 2*r;
  assert Valuation(n, p) ge 0;
  BONG := [n, disc / n];
  
  return BONG;
end function;


intrinsic MakeGoodBONG(L::LatMod, p::RngOrdIdl) -> []
{Return a good BONG of L at a dyadic prime p, as defined by C. Beli.}
  // Any BONG obtained from a maximal norm splitting is good, cf. Corollary 4.2 in Beli.
  // If a maximal norm splitting is calculated, a good BONG can be read off by joining
  // together the BONGs of the 1- and 2-dimensional components.
  require Order(p) cmpeq BaseRing(L) : "Incompatible arguments";
  require Minimum(p) eq 2 : "p must be a dyadic prime.";

  G, JJ := MaximalNormSplitting(L, p);
  BONG := [];
  pi := UniformizingElement(p);
  
  for i in [1..#G] do
    GG := G[i];
    if Nrows(GG) eq 2 then
      BONG cat:=MakeBONGdim2(LatticeModule(GG), p);
    elif Nrows(GG) eq 1 then
      Append(~BONG, GG[1,1]);
    else assert false;
    end if;
  end for;  
  return BONG;  
end intrinsic;



// 2. Spinor norms of lattices over number fields:

intrinsic SpinorNorm(L::LatMod, p::RngOrdIdl) -> ModTupFld, BoolElt
{The spinor norm of L at p, as calculated by C. Beli for dyadic p and by M. Kneser for non-dyadic p. Returns a subspace of LocalMultiplicativeGroupModSquares(p), and a boolean which is true iff the spinor norm is exactly the units.}
  require Order(p) cmpeq BaseRing(L) : "Incompatible arguments";
  // 2014-07-21.
  V, g := LocalMultiplicativeGroupModSquares(p);  
  e:= Valuation(BaseRing(L)! 2, p);

  if Minimum(p) ne 2 then
    // cf. Satz 3 in Kneser, "Klassenzahlen indefiniter quadratischer Formen in drei oder mehr Veränderlichen":
    J, G, E := JordanDecomposition(L, p);
    for i in [1..#G] do if Rank(G[i]) ge 2 then
      vprintf User1 : "This lattice has a 2-dimensional Jordan constituent, and p is odd. Spinor norm is either F^* or O_F^*(F^*)^2, i.e. we will find a vector space of dimension %o or %o.\n", Rank(G[i]), Rank(V)-1, Rank(V);
      // well, which of the two is the case?
      if #{e mod 2: e in E} lt 2 then
        // the units only: 
        return sub<V | [V.i: i in [1..Dimension(V)-1]]>, true;
      else
        // the whole group:
        return V, false;
      end if;
    end if; 
    end for;
    // this is the obscure case where p is odd and each
    // of its Jordan components has dimension 1. In this case, the units
    // need not be contained in the Spinor norm.
   
    // generators of the (principal) norm ideals of the Jordan
    // components: since p is odd, the norms (and the scales) are just the 
    // dimensions of the Jordan components
    NormGens := [g[1,1]: g in G];

    TwoNormGens := [];
    for i in [1..#NormGens] do for j in [i..#NormGens] do 
      Append(~TwoNormGens, NormGens[i]*NormGens[j]);
    end for; end for;
    TwoNormVectors := [x@@g: x in TwoNormGens];
    
    vprintf User1 : "odd p, norm generators of the %o Jordan components are: \n\n%o\n\n Products of two elements are \n\n%o\n\nTwoNormVectors:\n%o\n\n", #G, NormGens, TwoNormGens, TwoNormVectors; 
    
    // cf. Kneser 1956, Satz 3:
    SN := sub<V| TwoNormVectors>;
  else
    SN := sub<V| 0>;
    BONG := MakeGoodBONG(L, p);
    assert IsGoodBONG(BONG, p);
    if not HasPropertyA(L, p) then
      vprintf User1 : "This lattice does not have property A. Spinor norm is either F^* or O_F^*(F^*)^2, i.e. we will find a vector space of dimension %o or %o.\n", Rank(V)-1, Rank(V);
      // Using section 7, Thm. 3 in Beli 2002, one can decide which of the two cases applies. 
      // This is why we needed to compute a *good* BONG:
      for i in [1..#BONG-1] do
        BG := Basis(G_function(BONG[i+1]/BONG[i], V, g, p));
        for bg in BG do if bg[#Basis(V)] ne 0 then 
          // the whole group:
          //assert false;
          return V, false, <Sprintf("G(BONG[%o]/BONG[%o] contains non-units at entry #%o=%o", i+1, i, Index(BG, bg), bg)>;
        end if; end for;
      end for;
      for i in [1..#BONG-2] do
        if Valuation(BONG[i], p) eq Valuation(BONG[i+2], p) then 
          assert GF(2)!(Valuation(BONG[i+1], p) - Valuation(BONG[i], p)) eq 0;
          if GF(2)!((Valuation(BONG[i+1], p) - Valuation(BONG[i], p))/2) ne GF(2)!e then
            // the whole group:
            return V, false, i;
          end if;
        end if;
      end for;
       
      // if all checks have passed, the Spinor norm is exactly the units:
      return sub<V | [V.i: i in [1..Dimension(V)-1]]>, true;
    end if;
    // cf. Beli 2003, Thm. 1
    // printf "Got myself a BONG: %o\n", BONG;
    for i in [2..Rank(L)] do SN +:= G_function(BONG[i]/BONG[i-1], V, g, p); end for;
  
    // for this, see the remark on p. 161 in Beli 2003:
    if exists{i: i in [1..Rank(L)-2]| GF(2)!(Valuation(BONG[i+2], p) - Valuation(BONG[i], p)) eq 0} 
    then 
      alpha := IntegerRing()!Minimum({(Valuation(BONG[i+2], p) - Valuation(BONG[i], p))/2 : i in [1..Rank(L)-2]|  GF(2)!(Valuation(BONG[i+2], p) - Valuation(BONG[i], p)) eq 0});
      Uniformizer := UniformizingElement(p);
      SN +:= sub<V | (1+Uniformizer^alpha)@@g>;
    end if;
  end if;

  return SN, SN eq sub<V | [V.i: i in [1..Dimension(V)-1]]>;
end intrinsic;

intrinsic SpinorsNotExactlyTheUnits(L::LatMod) -> SeqEnum
{those places of BaseRing(L) where the Spinor norm is not exactly the units.}
  assert Rank(L) ge 3;
  // Rank >= 2 necessary for SpinorNorm().
  // Rank >= 3 necessary for \Phi from O'Meara 102:7 to be surjective.
  PP := Factorization(Discriminant(L));
  S := []; // set of bad primes
  for i in [1..#PP] do
    P := PP[i][1];
    SN, b := SpinorNorm(L, P);
    // we double-check:
    ExactlyTheUnits := sub<V| [V.i: i in [1..Rank(V) - 1]]> where V is LocalMultiplicativeGroupModSquares(P);  
;
    assert b eq (SN eq ExactlyTheUnits);
    if not b then Include(~S, [*P, SN*]); end if;
  end for;
  return S;
end intrinsic;





// 3. Enumerating genera of lattices over number fields:
  
function MapIntoClassGroupInternal(L, a, p)
  // this is only used in PrepareClassGroup. Outside of that function, you should only call MapIntoClassGroup, because you will map nice idèles of the form (1,...,1,pi,1,...,1) where pi is a uniformizer of the prime p, in the place p of the idèle.
  error if not (Order(p) cmpeq BaseRing(L)),  "Incompatible arguments";
  error if not (Parent(a) cmpeq NumberField(BaseRing(L))),  "Incompatible arguments.";
  assert assigned(L`RCG);
  assert assigned(L`homRCG);
  assert assigned(L`M);
  assert assigned(L`MM);
  assert assigned(L`ListOfFinitePlaces);
  
  // a, p: field element a \in F and prime ideal p.
  // a is interpreted as an element of the localization F_p.
  // That is, the associated idèle has entry "a" locally at p, and "1" everywhere else.
  
  ///  quo<Integers(F) | M>, dann mit Numerator, Denominator
  // SquareRepNice --> Einträge werden lokal um ein Quadrat verändert, das ist aber egal
  
  
  if not (p in L`ListOfFinitePlaces) then return (p^Valuation(a, p))@@L`homRCG; end if;
  
  
  
  result := Identity(L`RCG);
  
  F := Parent(a);
  R := Integers(F);

  IP := InfinitePlaces(F);
  error if not &and[IsReal(a): a in IP], "The base field is not totally real.";
  
  ListOfFinitePlaces := L`ListOfFinitePlaces;  
  
  a_idele := [q eq p select Integers(F)!a else Integers(F)!1: q in ListOfFinitePlaces];
  t := a_idele;
  a_idele_inf := [1: i in IP];
  i := Index(ListOfFinitePlaces, p);
  
  
  
  // can we invert this thing modulo M, or is a correction by a scalar needed?
  if (p in ListOfFinitePlaces) and (Valuation(a, p) gt 0) then
      assert( Valuation(a_idele[i], ListOfFinitePlaces[i]) eq 1); // a has been calculated by the homomorphism from LocalMultiplicativeGroupModSquares, and thus will be valuated at either 1 or 0 at every place
      s := WeakApproximation(ListOfFinitePlaces, [-Valuation(a_idele[i], ListOfFinitePlaces[i]): i in [1..#ListOfFinitePlaces]]); // [0,...,0,-1,0,...,0]
      
      // multiply with s at every place, and find nice representatives modulo squares in each component:
      for j in [1..#a_idele] do
         //a_idele[j] := Integers(F)!(((a_idele[j]*s)@@g)@g) where g is ListOfHomomorphisms[j];
         a_idele[j] := R!quo<R| L`MM[j]>!(a_idele[j]*s);
      end for;        

      assert &and[Valuation(a_idele[i], ListOfFinitePlaces[i]) eq 0: i in [1..#ListOfFinitePlaces]];
  else s := F!1;
  end if;

  // sanity check for MM/ListOfFinitePlaces:
  for i in [1..#L`MM] do assert Valuation(L`MM[i], ListOfFinitePlaces[i]) gt 0; end for;
  
    // make congruent to 1 mod M and make totally positive:
    
    
    el := CRT(a_idele, L`MM); 
  // printf "** CRT with %o --> %o\n", a_idele, el;  
    // usage: InverseMod(Integers(F)!element, IDEAL);
    
    a_idele_inf := [];

    el := InverseMod(el, L`M);  // M = &*MM
  // printf "** after InverseMod: %o\n", el;

    for j in [1..#IP] do
        if (Evaluate(el*s,IP[j]) lt 0) then
          a_idele_inf[j] := -1;
        else
          a_idele_inf[j] := 1;
        end if;
      end for;

    el2 := CRT(L`M, [1..#IP], R!1, a_idele_inf);
  // printf "** el2= %o\n", el2;
    
    //printf "assertion: %o\n", [(el*el2 * t[k]-1 in MM[k]): k in [1..#t]];
    assert &and[IsOne(quo< R | L`MM[k] > ! (s*el*el2 * t[k])): k in [1..#t]];
    assert IsTotallyPositive(s*el*el2);
  // printf "*** a=%o --> el*el2 = %o\n", a, el*el2;
  
    g := (p^Valuation(a,p)*s*el*el2)@@L`homRCG;       
  return g;

end function;
  

intrinsic PrepareClassGroup(L::LatMod)
{internal use.}
  F := NumberField(BaseRing(L));
  assert IsIdentical(BaseRing(L), Integers(F)); // debug 20150617: this should never fail!
  BP := SetToSequence(BadPrimes(L)); // the primes dividing 2*volume(L)  
  
  // we only need to carry around those finite places where the Spinor norm is not exactly the units:
  ListOfFinitePlaces := []; 
  ListOfHomomorphisms := [* *]; 
  ListOfSpinorNorms := [* *];

  Gens := [];
  for p in BP do
    V, g := LocalMultiplicativeGroupModSquares(p);  
    Spinors, ExactlyTheUnits := SpinorNorm(L, p);
    
    // if Minimum(p) eq 2 then Spinors := V; ExactlyTheUnits := false; printf "*** DEBUG: take the full vector space for p over 2 ***\n"; end if;

    if not ExactlyTheUnits then 
// printf "Found a prime over %o where the Spinor norm is not exactly the units of the order. dim(Spinors)=%o, dim(LocalMultGrpModSq)=%o\n", Minimum(p), Dimension(Spinors), Dimension(V);
    Append(~ListOfFinitePlaces, p); // UniformizingElement(p)^(1 + 2*e_p));// p);
      Append(~ListOfHomomorphisms, g);
      Append(~ListOfSpinorNorms, Spinors);
      // a basis of the Spinor norm of L at p, when viewed (modulo squares) as an F_2-vector space  (cf. LocalMultiplicativeGroupModSquares)
      b := Basis(Spinors); 
      Gens cat:= [<a@g, p>: a in b];
      assert &and[Valuation(gg, p) in {0,1}: gg in [a@g: a in b]];
    else
 // printf "At prime over %o, the Spinor norm is exactly the units of the order.\n", Minimum(p);    
    end if;
  end for;

  // calculate a ray M, and for convenience store its factors in MM:
  L`M := 1*Integers(F);
  // the individual powers of prime ideals composing the ray:
  L`MM := [];  
  // the places used for the ray:
  L`ListOfFinitePlaces := ListOfFinitePlaces; 

  /// vals := [];
  for i in [1..#ListOfFinitePlaces] do
    p := ListOfFinitePlaces[i];
    e_p := Valuation(Order(p)!2, p);
    L`M *:= p^(1 + 2*e_p);
    Append(~L`MM, (p)^(1 + 2*e_p));
  end for;
  // the ray we define includes all infinite places:
  L`RCG, L`homRCG := RayClassGroup(L`M, [1..Signature(F)]);
  
  // Step 1: map the generators into the class group to create the factor group.
  ClassSubgroupGens := [];
  ClassSubgroup := sub<L`RCG | 2*L`RCG>;
  
  for g in Gens do
    h := MapIntoClassGroupInternal(L, g[1], g[2]); 
// printf "*** mapping %o, prime ideal over %o \n", g[1], Minimum(g[2]);
    //// if (Type(h) eq Infty) then return false,false,false,false,false,false,false,false; end if;
    Append(~ClassSubgroupGens, h); 
    ClassSubgroup := sub<L`RCG | ClassSubgroupGens, 2*L`RCG>;
  end for;
  L`ClassSubgroup := ClassSubgroup;
  
// printf "*** PrepareClassGroup: number of generators used: %o\n", #Gens;
// printf "*** PrepareClassGroup: ray class group: size = %o\n", #L`RCG;
// printf "*** PrepareClassGroup: subgroup of ray class group: size = %o\n", #ClassSubgroup;


  // Step 2: find good generators (that is: generators which are not dyadic, and not in BadPrimes(L) -- so that neighbour generation is always possible), 
  // of this factor group.
  // Only pick Idèles of the form (1,...,1,p,1,...,1) so that:
  // a)  nothing has to be corrected before they can be mapped down into the factor group
  // b)  we can simply store the prime ideal and know that it corresponds to the (1,...,1,p,1,...,1) 
  // These prime ideals will be stored in L`CriticalPrimes.
  
  MySubgroup := ClassSubgroup; // we map more generators into MySubgroup until the quotient is trivial
  L`CriticalPrimes := []; // this is where the good primes are stored!

  
  // first grab all good primes which have norms up to the maximum norm of a bad prime:
  maxnorm := Maximum({Norm(q): q in BadPrimes(L)});
  GoodPrimes := [p: p in PrimesUpTo(maxnorm, F: coprime_to:=&*BadPrimes(L))];
  p_ind := 1;
  while #MySubgroup lt #L`RCG do
    
    while p_ind gt #GoodPrimes do
      // calculate more good primes!
      maxnorm := NextPrime(maxnorm);
      GoodPrimes := [p: p in PrimesUpTo(maxnorm, F: coprime_to:=&*BadPrimes(L))];
    end while;
    p := GoodPrimes[p_ind];
    
    // map the (1,...,1,pi,1,...,1) idèle into the class group, where pi is a uniformizing element of p:
    h := MapIntoClassGroup(L, p);
// printf "*** good primes: mapping prime ideal over %o ", Minimum(p);
    oldsize := #MySubgroup;
    Append(~ClassSubgroupGens, h);    
    MySubgroup := sub<L`RCG | ClassSubgroupGens, 2*L`RCG>;
    if #MySubgroup gt oldsize then 
      // printf " -- subgroup size increased.\n";
      // this prime ideal is relevant for neighbour generation, store it:
      Append(~L`CriticalPrimes, p);
    else
      // printf " -- subgroup size unchanged.\n";
    end if;  
    p_ind +:= 1;
  end while;
  
  L`FactorGroup, L`FactorGroupHom := quo<L`RCG | ClassSubgroup>;
// printf "*** good primes over %o (together with the squares) generate the subgroup.\n", [Minimum(q): q in L`CriticalPrimes];
// printf "*** PrepareClassGroup: factor group of ray class group: size = %o (this is the number of Spinor `+` genera in Genus(L))\n", #L`FactorGroup;

end intrinsic;


function SmallestNormGoodPrime(L)
  // return a smallest-norm prime which is not contained in BadPrimes(L),
  // i.e. not dyadic and does not divide Discriminant(L) -- making neighbor generation possible (and hopefully fast!).
  // Note that this prime can be contained in L`CriticalPrimes, and that this is not a problem!
  
  if not assigned(L`CriticalPrimes) then PrepareClassGroup(L); end if; 
  
  if #L`CriticalPrimes gt 0 then maxnorm := Maximum({Norm(a): a in L`CriticalPrimes}); else maxnorm := 10; end if;
  repeat
    PP := [q: q in PrimesUpTo(maxnorm, NumberField(BaseRing(L)))| not(q in BadPrimes(L))];
    maxnorm := NextPrime(maxnorm);
  until #PP gt 0;
  
  return PP[1];
end function;

// for use in for Genus enumeration:
intrinsic GetPrimes(L::LatMod, Ignore::BoolElt) -> []
{A complete set of primes of BaseRing(L) needed to enumerate the genus of L.}
  require Rank(L) ge 3 : "The rank of L must be at least 3."; // otherwise we are unsure about the Spinor norms at unimodular primes.
  if not assigned(L`CriticalPrimes) then PrepareClassGroup(L); end if;

  return L`CriticalPrimes;
end intrinsic;

intrinsic GenusRepresentatives(L::LatMod : Max:= Infinity(), UseAuto:= true, Extra:= 0, TestGenus2:= false, Decomposition:=true, NoBreakOnError:=false, ForceThesePrimes:=[]) -> []
{A list of representatives of the isometry classes in the genus of L. Optional parameters: Max, the maximum number of isometry classes to calculate; Extra, the number of extra primes for safety; TestGenus2, set to true to turn on sanity checks for the neighbor algorithm.}
	print "Hi.";

  require Rank(L) ge 3 : "Only implemented for lattices of rank at least 3.";
  require IsDefinite(L): "Only implemented for definite lattices.";
  requirege Extra, 0;
  require (Max ge 1): "Max should be an integer or Infinity().";
  
  Primes := #ForceThesePrimes eq 0 select {x: x in GetPrimes(L, false)} else ForceThesePrimes;
  
  
  // There are infinitely many primes generating our ray class group for L,
  // so there is no need to choose dyadic primes. Neighbour generation
  // for dyadic primes is a pain and should be avoided.
  error if not &and[Minimum(q) gt 2: q in Primes], "PrepareClassGroup should not pick dyadic primes.";
  error if not &and[#E eq 1 where _,_,E is JordanDecomposition(L, p): p in Primes], "PrepareClassGroup should not pick any primes where the lattice is not modular.";
  
  good := SmallestNormGoodPrime(L);
  //// Primes join:= {good};
  
  // this will be our special friend, remove it from the pack:
  if good in Primes then Primes := {x: x in Primes | x ne good}; end if;
  

  Reps:= [ L ]; // the todo-list 
  Markers := [ false ]; // marker for "have we calculated all neighbours with the good prime at Reps[i]"
  extra:= false;
  ExtraFail := false;

  while true do
    i:= 1;
    while i le #Reps and #Reps lt Max do
      if not Markers[i] then
        // all neighbours with our favorite prime:
        call:= func< LL | not iso, true where iso:= MyIsIsometric(Reps[i], LL: Decomposition:=Decomposition) >; // 20150803: note that the "already known" lattice needs to be the first parameter in IsIsometric when we use the decomposition method
        N:= Neighbours(Reps[i], good: CallBack:=call, Max:=Max, AutoOrbits:=UseAuto, TestGenus2:= TestGenus2);        

        for n in N do
          if forall{ r: r in Reps | not MyIsIsometric(r, n: Decomposition:=Decomposition) } then 
  	        Append(~Reps, n);
            Append(~Markers, true);
            if #Reps ge Max then break; end if;
    	  end if;
        end for;
        Markers[i] := true;
      end if;
    
      for p in Primes do
        // one neighbour each at all of the critical primes:
        // set AutoOrbits to false unless we wish wo calculate all of the neighbors!
        call_one:= func< LL | not iso, false where iso:= MyIsIsometric(Reps[i], LL: Decomposition:=Decomposition) >;
        N:= Neighbours(Reps[i], p: CallBack:=call_one, AutoOrbits:= false, TestGenus2:= TestGenus2);

        for n in N do
          if forall{ r: r in Reps | not MyIsIsometric(r, n: Decomposition:=Decomposition) } then 
  	        Append(~Reps, n);
            Append(~Markers, false);
            // are we in the extra rounds? Then we should NOT find anything new!
	        if extra then
              error if not NoBreakOnError, "Oops, found new rep in the extra rounds! --- Please report";
              ExtraFail := true;
            end if;
            if #Reps ge Max then break p; end if;
    	  end if;
        end for;
      end for;
      i +:= 1;
    end while;

    // are we done yet?
    if (#Reps ge Max) or extra or (Extra cmpeq 0) then 
      assert &and[b: b in Markers];
      return Reps, ExtraFail;
    end if;

    // Add some more extra rounds for safety and repeat
    Primes:= GetExtra(L, Primes, Extra);
    //if Extra gt 0 then printf "Double-checking with %o extra primes over %o...\n", Extra, [Minimum(a): a in GetExtra(L, Primes, Extra)]; 
    // end if;
    extra:= true;
  end while;
end intrinsic;
 

intrinsic IsOneClassGenus(L::LatMod: Debug:=false, UseAuto:=false, Decomposition:=true) -> BoolElt
{returns true iff #GenusRepresentatives(L) eq 1, but is much faster than calling GenusRepresentatives.}
  require Rank(L) ge 3 : "Only implemented for lattices of rank at least 3.";
  require IsDefinite(L): "Only implemented for definite lattices.";
  
  IsMaximal(BaseRing(L));
  
  F := NumberField(BaseRing(L));
 
  assert IsIdentical(BaseRing(L), Integers(F)); // debug 20150617: this should never fail!
  
  if not assigned(L`CriticalPrimes) then PrepareClassGroup(L); end if;
  
  // There are infinitely many primes generating our ray class group for L,
  // so there is no need to choose dyadic primes. Neighbour generation
  // for dyadic primes is a pain and should be avoided.
  error if not &and[Minimum(q) gt 2: q in L`CriticalPrimes], "PrepareClassGroup should not pick dyadic primes.";
  
  good:= SmallestNormGoodPrime(L);

  
// if Debug then printf "IsOneClassGenus: working with %o critical primes over %o and an auxiliary prime over %o.\n", #L`CriticalPrimes, [Minimum(a): a in L`CriticalPrimes] , Minimum(good); end if;

  // A callback function for the neighbors algorithm which keeps only those lattices not isometric to L, and stops once one non-isometric lattice has been found:
  call:= func< LL | not iso, iso where iso:= MyIsIsometric(L, LL:Decomposition:=Decomposition) >;
  call_one:= func< LL | not iso, false where iso:= MyIsIsometric(L, LL:Decomposition:=Decomposition) >;
  
  // One neighbour each at all the critical primes
  // (calculating a neighbour here *will* change the spinor-"+"-genus, but the resulting lattice might lie in the same spinor genus.)
  found := false;
// if Debug then printf "one neighbour each with critical primes ... "; end if;
  for p in L`CriticalPrimes do 
    found := found or (#Neighbours(L, p: CallBack:= call_one, AutoOrbits:=false, TestGenus2:=false) gt 0);
    if Debug and (not found) then 
      // this can only occur if all automorphisms of L have determinant 1 (hence the dimension must be even):
      // printf "exotic case.\n";
      assert &and[IsOne(Determinant(x)): x in Generators(AutomorphismGroup(L))];
      // if Debug then printf "***** WARNING, a neighbour should have been found *****\n"; else assert false; end if;
    end if;
    if found then break; end if;
  end for;
// if Debug then if not found then printf " nothing found yet.\n"; else printf "neighbour(s) found!\n"; end if; end if;

  // All the neighbours at our favorite auxiliary low-norm prime:
  // (calculating a neighbour here might or might not change the spinor genus. Depending on the structure of the RCG, 
  // there will be one or two spinor genera covered if we calculate all the neighbours here.)
  if not found then 
// if Debug then printf "complete orbit with auxiliary prime over %o of norm %o... ", Minimum(good), Norm(good); end if;
    found := found or (#Neighbours(L, good: CallBack:=call, AutoOrbits:=UseAuto, TestGenus2:=false) gt 0); 
  end if;
// if Debug then if not found then printf " nothing found.\n"; else printf "neighbour(s) found!\n"; end if; end if;
  if (not found) then
    if GF(2)!Rank(L) eq 0 then assert #L`FactorGroup in {1,2};
    else assert #L`FactorGroup in {1}; end if;
  end if;
  return not found;  
end intrinsic;

intrinsic MapIntoClassGroup(L::LatMod, p::RngOrdIdl) -> GrpAbElt
{Map a prime ideal into the ray class group used to determine the genus of L.}
  require Order(p) cmpeq BaseRing(L) : "Incompatible arguments";
  return MapIntoClassGroupInternal(L, NumberField(BaseRing(L))!UniformizingElement(p), p);
end intrinsic;

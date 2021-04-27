freeze;
/****-*-magma-******a********************************************************
                                                                            
                        Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
                   
   FILE: minkowski.m

   Implementation file for minkowski reduction routines

   04/22/2021 : File created
 
 ****************************************************************************/

import "/Applications/Magma/package/Lattice/Lat/minkowski.m" :
  NeighborReduction, SignNormalization, PermutationReduction,
  replacement_successive_minima;

// In what follows we have some code to construct positive definite
// ternary quadratic forms of arbitrary discriminant
// This follows the article "Levels of Positive Definite Ternary Quadratic Forms"
// by J. Larry Lehman https://doi.org/10.2307/2153043

// Checking conditions in Lehman Proposition 3
function IsFormReduced(a,b,c,r,s,t)
  // Condition (1)
  if a gt b then return false; end if;
  if b gt c then return false; end if;
  // Condition (2)
  if not (((r gt 0) and (s gt 0) and (t gt 0)) or
	  ((r le 0) and (s le 0) and (t le 0))) then
    return false;
  end if;
  // Condition (3)
  if a lt Abs(t) then return false; end if;
  if a lt Abs(s) then return false; end if;
  if b lt Abs(r) then return false; end if;
  // Condition (4)
  if a+b+r+s+t lt 0 then return false; end if;
  // Condition (5)
  if a eq t and s gt 2*r then return false; end if;
  if a eq s and t gt 2*r then return false; end if;
  if b eq r and t gt 2*s then return false; end if;
  // Condition (6) 
  if a eq -t and s ne 0 then return false; end if;
  if a eq -s and t ne 0 then return false; end if;
  if b eq -r and t ne 0 then return false; end if;
  // Condition (7) 
  if a+b+r+s+t eq 0 and 2*a+2*s+t gt 0 then return false; end if;
  // Condition (8)
  if a eq b and Abs(r) gt Abs(s) then return false; end if;
  if b eq c and Abs(s) gt Abs(t) then return false; end if;
  return true;
end function;

function TernaryFormMatrix(a,b,c,r,s,t)
  return SymmetricMatrix([2*a,t,2*b,s,r,2*c]);
end function;

intrinsic TernaryQuadraticLattices(d::RngIntElt) -> SeqEnum[AlgMatElt]
{Return representatives for all positive definite ternary quadratic forms of discriminant d, up to isometry.}
  forms := [];
  max_a := Floor(Root(d/2, 3));
  cnt := 0;
  for a in [1..max_a] do
    max_b := Floor(Sqrt(d/(2*a)));
    for b in [a..max_b] do
      min_c := Ceiling(Maximum(b, d/(4*a*b)));
      max_c := Floor(d/(2*a*b));
      for c in [min_c..max_c] do
        for r in [-b..0] do
	  for s in [-a..0] do
	    for t in [-a..0] do
	      A := TernaryFormMatrix(a,b,c,r,s,t);
	      disc := Determinant(A)/2;
	      if disc eq d and IsFormReduced(a,b,c,r,s,t) then
		Append(~forms, A);
              end if;
              cnt +:= 1;
	    end for;
          end for;
	end for;
        for r in [1..b] do
	  for s in [1..a] do
	    for t in [1..a] do
	      A := TernaryFormMatrix(a,b,c,r,s,t);
	      disc := Determinant(A)/2;
	      if disc eq d and IsFormReduced(a,b,c,r,s,t) then
		Append(~forms, A);
              end if;
              cnt +:= 1;
	    end for;
          end for;
	end for;
      end for;
    end for;
   end for;
   printf "Checked %o forms.\n", cnt;
   return forms;
end intrinsic;

function foo(r, N)
  assert N ge 2;
  ret := [];
  fac := Factorization(N);
  R<x> := PolynomialRing(Rationals(),r);
  factor_sets := [];
  for fa in fac do
    exp_set := [Exponents(x) : x in MonomialsOfDegree(R, fa[2])];
    Append(~factor_sets, [[fa[1]^e : e in exps] : exps in exp_set]); 
  end for;
  possible_factors := CartesianProduct(factor_sets);
  diags := {};
  for poss in possible_factors do
    diag := Multiset([&*[x[i] : x in poss] : i in [1..r]]);
    Include(~diags, diag);
  end for;
  diags := [MultisetToSequence(diag) : diag in diags];
  for diag in diags do
    D := 2*DiagonalMatrix(diag);
    lat := LatticeWithGram(D);
    L := LatticeFromLat(lat);
    // That's nice, but only when we are square-free
    // maybe we can make it stop at the appropriate level
    L_max := MaximalIntegralLattice(L);
    Append(~ret, GramMatrix(L_max, Basis(Module(L_max))));
  end for;
  return ret;
end function;

intrinsic TernaryQuadraticLattice(N::RngIntElt) -> Mtrx
{get a positive definite quadratic lattice.}
  assert N ge 2;
  fac := Factorization(N);
  require &and[x[2] le 2 : x in fac] : "Only supports cube-free levels.";
  // B<i,j,k> := QuaternionAlgebra(d);
  // This does not make it easy for us to find the square root of -d in the
  // quaternion algebra after constructing it. Therefore we use Ibukiyama's
  // recipe.
  all_primes := [x[1] : x in Factorization(N) | IsOdd(x[2])];
  primes := [x : x in all_primes | x ne 2]; 
  d := &*([1] cat all_primes);
  // In this case there is a definite quaternion algebra of discriminant d
  if IsOdd(#all_primes) then  
    // a quadratic non-residue suffices here, but this is usually not
    // time consuming.
    residues := [3] cat [-Integers()!PrimitiveElement(Integers(p)) : p in primes];
    q := CRT(residues, [8] cat primes);
    while not IsPrime(q) do
      q +:= &*([8] cat primes);
    end while;	    
    B<i,j,k> := QuaternionAlgebra(Rationals(), -q, -d);
    assert Discriminant(B) eq d;
    // We could also form the maximal order directly from Ibukiyama's recipe
    // if necessary
    // O_B := MaximalOrder(B);
  else
    // I'm not sure which quaternion algebra we want here
    // This one covers [1,1,d]
    // Step by step - when d is prime, the above has disc p
    // and it is the unique
    // when d = pq, we can have [1,1,pq] or [1,p,q]
    // In the first case we need (-pq,-pq), in the second we need
    // (-p,-q).
    // The first has discriminant 
    B<i,j,k> := QuaternionAlgebra(Rationals(), -d, -d);
// O_B := QuaternionOrder(B, N div Discriminant(B));
  end if;

  O_B := QuaternionOrder(B, N div Discriminant(B));
  alpha := Basis(O_B);
  // maybe we are lucky
  Q := Matrix([[Trace((alpha[m])*Conjugate(alpha[n]))
		   : n in [2..4]] : m in [2..4]]);
  if Determinant(Q) eq 2*N then
    return Q;
  end if;
  x := Basis(B);
  gram := Matrix([[Trace(x[m]*Conjugate(x[n]))
		      : n in [1..4]] : m in [1..4]]);
  basis := Matrix([Eltseq(x) : x in alpha]);
  lat_O := Lattice(basis, gram);
  mat_beta := [Eltseq(x) : x in Basis(Dual(lat_O : Rescale := false))];
  beta0 := [B!b : b in mat_beta];
  mat := [[Trace(alpha[m]*Conjugate(beta0[n])) : n in [1..4]] : m in [1..4]];
  beta := [B!b : b in Rows(Transpose(Matrix(mat))^(-1)*Matrix(mat_beta))];
  assert IsOne(Matrix([[Trace(alpha[m]*Conjugate(beta[n]))
			   : n in [1..4]] : m in [1..4]]));
  Q := Matrix([[Trace((beta[m]*j)*Conjugate(beta[n]*j))
		   : n in [2..4]] : m in [2..4]]);

  assert Determinant(Q) eq 2*N;
  return Q;
end intrinsic;

// Still not working - has to make it positive definite
intrinsic QuinaryQuadraticOfPrimeLevel(p::RngIntElt) -> Mtrx
{.}
  // For now we assume p is an odd prime
  require IsPrime(p) and IsOdd(p) : "Currently only implemented for odd primes.";
  residues := [3] cat [-Integers()!PrimitiveElement(Integers(p))];
  q := CRT(residues, [8,p]);
  while not IsPrime(q) do
    q +:= 8*p;
  end while;	    
  B<i,j,k> := QuaternionAlgebra(Rationals(), -p, -q);
  assert Discriminant(B) eq p;

  // we look for an element of norm -1, and we will only
  // be interested at its value mod p
  Bp := ChangeRing(B, Integers(p));
  assert exists(a){x : x in Bp | Norm(x) eq -1};
  a := [Integers()!x : x in Eltseq(a)];
  V := VectorSpace(Rationals(), 5);
  v1 := V!([1] cat a);
  v2 := V![0,p,0,0,0];
  v3 := V!([0] cat Eltseq(p*(1+j)/2));
  v4 := V!([0] cat Eltseq(i*(1+j)/2));
  s := CRT([0,1],[p,q]);
  _, r := IsSquare(GF(q)!(-p));
  r := Integers()!r;
  v5 := V!([0] cat Eltseq((r*s+i)*j/q));
  basis := [v1, v2, v3, v4, v5];
  function bilinear(v1, v2)
    t1 := v1[1];
    t2 := v2[1];
    r1 := B!(Eltseq(v1)[2..5]);
    r2 := B!(Eltseq(v2)[2..5]);
    return (2*t1*t2 + Trace(r1*Conjugate(r2)))/p;
  end function;
  Q := Matrix([[bilinear(basis[i], basis[j]) : j in [1..5]] : i in [1..5]]);
  return ChangeRing(Q, Rationals());
end intrinsic;

function possible_diagonals(M, k, n)
  if k eq 1 then
    return [[x] : x in [1..Floor(Root(M,n))]];
  end if;
  prefixes := possible_diagonals(M, k-1, n);
  ret := [];
  for prefix in prefixes do
    min_last := prefix[#prefix];
    max_last := Floor(Root(M / &*prefix, n+1-k)); 
    for last in [min_last..max_last] do
      Append(~ret, prefix cat [last]);
    end for;
  end for;
  return ret;
end function;

function prepareMinkowskiInequalities(n)
  aux_reflect := [];
  aux_permute := [];
  aux_sign := [];
  l_table := [CartesianProduct([{1}] cat [{-1,1} : k in [1..j]] cat
			       [{0} : i in [1..n-j-1]]) : j in [1..n-1]];
  if n ge 5 then
    l_table cat:= [CartesianProduct([{1}] cat [{-1,1} : k in [1..j]] cat
				    [{-2,2} : i in [1..n-j-1]]) : j in [3..n-2]];
  end if;
  if n eq 6 then
    Append(~l_table, CartesianProduct([{1}] cat [{-1,1} : k in [1..3]] cat
				      [{-2,2}, {-3,3}]));
    Append(~l_table, CartesianProduct([{1}] cat [{-1,1} : k in [1..3]] cat
				      [{-2,2}, {0}]));
  end if;
  l := &cat [[x : x in ll] : ll in l_table];
  S_n := Sym(n);
  X := GSet(S_n);
  act := Action(X);
  idxs := [<i,j> : i,j in [1..n] | i le j];
  constraints := [];
  for sigma in S_n do
    for ll in l do
      l_sigma := [ll[act(i,sigma^(-1))] : i in [1..n]];
      vec := [0 : i in [1..n*(n+1) div 2]];
      for idx in idxs do
        i := idx[1];
        j := idx[2];
        vec[Position(idxs, <i,j>)] := l_sigma[i]*l_sigma[j];
      end for;
      k := act(1, sigma);
      vec[Position(idxs, <k,k>)] -:= 1;
      Append(~constraints, vec);
      Append(~aux_reflect, <Vector(l_sigma), k>);
    end for;
  end for;
  for i in [1..n-1] do
    vec := [0 : i in [1..n*(n+1) div 2]];
    vec[Position(idxs, <i+1,i+1>)] := 1;
    vec[Position(idxs, <i,i>)] := -1;
    Append(~constraints, vec);
    Append(~aux_permute, [i, i+1]);
    vec := [0 : i in [1..n*(n+1) div 2]];
    vec[Position(idxs, <i,i+1>)] := 1;
    Append(~constraints, vec);
    Append(~aux_sign, i+1);
  end for;
return constraints, aux_reflect, aux_permute, aux_sign;
end function;

// Right now only supports n le 6 !!!
// intrinsic QuadraticLattice(n::RngIntElt, D::RngIntElt) -> AlgMatElt
// {Return a positive-definite quadratic form of dimension n and determinant D using Minkowski's description of the space of reduced forms.}
function QuadraticLattice(n, D)
  // These are Hermite's constants gamma^n for n in [1..8]
  hermite_pow := [1, 4/3, 2, 4, 8, 64/3, 64, 256];
  // here gamma is a lower bound for Hermite's constant
  // i.e. the constant such that gamma*a_{n,n}^n le D
  if n le 8 then
    gamma := Root(hermite_pow[n], n);
  else
    // !!! TODO - there are known lower bounds for
    // Hermite's constant for general n, implement them !!!
    gamma := 1;
  end if;
  // lambda is a lower bound for a constant such that
  // lambda * prod a_{i,i} le D
  lambda := gamma * (4/5)^(1/2*(n-3)*(n-4));
  // !!! - TODO - restrict also by gamma separately
  diags :=  possible_diagonals(D / lambda, n, n);
  
  constraints := prepareMinkowskiInequalities(n);
  idxs := [<i,j> : i,j in [1..n] | i le j];
  ineq_idxs := [idx : idx in idxs | idx[1] ne idx[2]];
  printf "There are %o diagonals.\n", #diags;
  for diag in diags do
    ineqs := [];
    bds := [];
    for v in constraints do
      bd := -&+[v[Position(idxs, <i,i>)]*diag[i] : i in [1..n]];
      ineq := [v[idx] : idx in [1..n*(n+1) div 2] | idxs[idx][1] ne idxs[idx][2]];
      Append(~ineqs, ineq);
      Append(~bds, bd);
    end for;
    bds_uniq := AssociativeArray();
    for i in [1..#bds] do
      ineq := ineqs[i];
      if IsZero(ineq) then continue; end if;
      if not IsDefined(bds_uniq, ineq) then
        bds_uniq[ineq] := bds[i];
      else
        bds_uniq[ineq] := Maximum(bds[i], bds_uniq[ineq]);
      end if;
    end for;
    ineqs := SetToSequence(Keys(bds_uniq));
    bds := [bds_uniq[ineq] : ineq in ineqs];
    ineqs := [LatticeVector(v) : v in ineqs];
    // This is not very efficient - should rethink how to do that
    P := PolyhedronWithInequalities(ineqs, bds);
    printf "Checking %o points.\n", #Points(P);
    for p in Points(P) do
      ordered := [[Eltseq(p)[Position(ineq_idxs, <i,j>)]
		      : i in [1..j-1]] cat [2*diag[j]] : j in [1..n]];
      Q := SymmetricMatrix(&cat ordered);
      // half discriminant for odd ranks
      factor := IsEven(n) select 1 else 2;
      if IsPositiveDefinite(Q) and Determinant(Q) eq factor*D then
        return [Q];
      end if;
    end for;
  end for;
  // something went wrong
  return [];
end function;
// end intrinsic;

function isReduced(vec, constraints)
  for i in [1..#constraints] do
    if (vec, constraints[i]) lt 0 then
      return false, i;
    end if;
  end for;
  return true, _;
end function;
/*
function MinkowskiReduction(A)
  assert IsPositiveDefinite(A);
  B := A;
  n := NumberOfRows(A);
  one := IdentityMatrix(Integers(), n);
  // This could be made in precomputation
  constraints, aux_reflect,
  aux_permute, aux_sign := prepareMinkowskiInequalities(n);
  constraints := [Vector(v) : v in constraints];
  n_reflect := #aux_reflect;
  n_permute := #aux_permute;
  reduced := false;
  while not reduced do
    B_flat := Vector([(i eq j select 1 else 2)*B[i,j] : i,j in [1..n] | i le j]);
    reduced, i := isReduced(B_flat, constraints);
    if not reduced then
      if i le n_reflect then
        l := aux_reflect[i][1];
        k := aux_reflect[i][2];
	e_k := one[k];
        // currently performing small steps - can do the actual reflection
	g := one + Transpose(Matrix(l-e_k))*Matrix(e_k);
      elif i le n_reflect + n_permute then
	i -:= n_reflect;
        g := PermutationMatrix(Integers(), Sym(n)!aux_permute[i]);
      else
        i -:= (n_reflect + n_permute);
        g := one;
        k := aux_sign[i];
        g[k,k] := -1;
      end if;
      B := Transpose(g)*B*g;
    end if;
  end while;
  return B;
end function;
*/
function VoronoiCoordinateBounds(d)
  // !! TODO - check what the real bounds are !!
  return [1 : i in [1..d]];
end function;

function closestLatticeVectorMinkowskiReduced(b, t, gram)
  d := #b + 1;
  one := IdentityMatrix(Rationals(), d);
  e_d := Matrix(Rows(one)[d]);
  diag := DiagonalMatrix(Rationals(), Diagonal(gram)[1..d-1]);
  H_v := diag^(-1)*Submatrix(gram, [1..d-1], [1..d]);
  H := Submatrix(H_v, [1..d-1], [1..d-1]);
  v := Submatrix(H_v, [1..d-1], [d]);
  // This is the precision to which we will want to compute H^(-1)
  // (we don't need it to be exact)
  r := Ceiling(Log(Maximum([1] cat Eltseq(v))));
  // There's an annoying sign error in the paper here
  y := H^(-1)*v;
  voronoi := VoronoiCoordinateBounds(d-1);
  x_min := [Ceiling(y[i,1] - voronoi[i]) : i in [1..d-1]];
  x_max := [Floor(y[i,1] + voronoi[i]) : i in [1..d-1]];
  xs := CartesianProduct([[x_min[i]..x_max[i]] : i in [1..d-1]]);
  min_dist := Infinity();
  min_g := one;
  min_x := Vector([0 : i in [1..d-1]]);
  for x in xs do
    xvec := Transpose(Matrix(Rationals(), Vector([x[i] : i in [1..d-1]])));
    g := one - VerticalJoin(xvec*e_d, 0*e_d);
    x_gram := Transpose(g)*gram*g;
    if x_gram[d,d] lt min_dist then
      min_dist := x_gram[d,d];
      min_g := g;
      min_x := xvec;
    end if;
  end for;
  return Transpose(min_x)*Matrix(b), min_g;
end function;

function magmaKohelReduction(M)
    deg := Degree(Parent(M));
    ZMat := MatrixAlgebra(Integers(),deg);
    I := Identity(ZMat);
    if Type(BaseRing(Parent(M))) eq RngInt then
	coeffs := Eltseq(M);
	c := GCD(coeffs);
	M0 := ZMat ! [ 1/c * x : x in coeffs ];
    else
	coeffs := Eltseq(M);
	den := LCM([ Denominator(x) : x in coeffs ]);
	num := GCD([ Numerator(den*x) : x in coeffs ]);
	c := num/den;
	M0 := ZMat![ 1/c * x : x in coeffs ];
    end if;
    // Treat some special cases here?
    if Eltseq(M0) eq [2,1,1,0,1,2,1,1,1,1,2,1,0,1,1,2] then
	return M, I;
    end if;
    //     D, B := SuccessiveMinima(LatticeWithGram(M0));
    D,B:=replacement_successive_minima(M0); // MW Dec 2017
    // Treat some special cases here.
    if deg eq 4 and &and[ D[i] eq D[1] : i in [2..4] ] then
	if D[1] le 2 then
	    MS := [
	            Matrix(4,4,[1,0,0,0,0,1,0,0,0,0,1,0,0,0,0,1]),
   		    Matrix(4,4,[2,1,1,0,1,2,1,1,1,1,2,1,0,1,1,2]),
		    Matrix(4,4,[2,1,0,0,1,2,0,0,0,0,2,1,0,0,1,2])
		  ];
	    for M1 in MS do
		L1 := LatticeWithGram(M1);
		bool, T1 := IsIsometric(LatticeWithGram(M0),L1);
		if bool then
		    return Parent(M) ! (c * M1), T1;
		end if;
	    end for;
	end if;
    elif deg eq 4 and D[1] eq D[2] then
	if D[1] le 2 then
	    MS := [
	            Matrix(4,4,[2,0,1,1,0,2,1,1,1,1,4,1,1,1,1,4]),
		    Matrix(4,4,[2,1,0,0,1,2,0,0,0,0,4,2,0,0,2,4]),
	            Matrix(4,4,[2,1,1,0,1,2,1,1,1,1,10,5,0,1,5,10])
		  ];
	    for M1 in MS do
		L1 := LatticeWithGram(M1);
		bool, T1 := IsIsometric(LatticeWithGram(M0),L1);
		if bool then
		    return Parent(M) ! (c * M1), T1;
		end if;
	    end for;
	end if;
    end if;
    if &or[ D[i] lt M0[i,i] : i in [1..deg] ] then
	T := ZMat! &cat [ Eltseq(v) : v in B ];
	M0 := T*M0*Transpose(T); 
    else // don't change if already there
	T := I;
    end if;
    repeat
	M0, T1 := PermutationReduction(M0);
        M0, T2 := SignNormalization(M0);
        M0, T3 := NeighborReduction(M0);
	T1 := T3*T2*T1; 
	T := T1*T;
    until T1 eq I;
    return Parent(M) ! (c * M0), T;
end function;

function GreedyReduction(b, gram)
  d := #b;
  one := IdentityMatrix(Rationals(), d);
  mult := one;
  if d eq 1 then return b, one; end if;
  repeat
    // we add the vector itself for a unique ordering
  //    perm := [x[3] : x in Sort([<gram[i,i],b[i], i> : i in [1..d]])];
    perm := [x[2] : x in Sort([<gram[i,i], i> : i in [1..d]])];
    b := [b[i] : i in perm];
    // Is it faster to do SwapRows and SwapCol?
    g := PermutationMatrix(Rationals(), perm)^(-1);
    gram := Transpose(g)*gram*g;
    mult := mult*g;
    b0, mult0 := GreedyReduction(b[1..d-1], Submatrix(gram, [1..d-1], [1..d-1]));
    g := DirectSum(mult0, Matrix(Rationals(), [[1]]));
    b := b0 cat [b[d]];
    gram := Transpose(g)*gram*g;
    mult := mult*g;
    c, g := closestLatticeVectorMinkowskiReduced(b0, b[d], gram);
    b[d] := Vector(Eltseq(b[d])) - Vector(Eltseq(c));
    gram := Transpose(g)*gram*g;
    mult := mult*g;
  until gram[d,d] ge gram[d-1,d-1];
  // we force the secondary diagonal to be positive
  for i in [1..d-1] do
    if gram[i, i+1] lt 0 then
      b[i+1] := -b[i+1];
      g := one;
      g[i+1,i+1] := -1;
      mult := mult*g;
      gram := Transpose(g)*gram*g;
    end if;
  end for;
  // we add the vector itself for a unique ordering
  // min_gram := [Minimum(Eltseq(gram[i])) : i in [1..d]];
  min_gram := [Sort(Eltseq(gram[i])) : i in [1..d]];
  perm := [x[4] : x in Sort([<gram[i,i],min_gram[i], b[i], i> : i in [1..d]])];
  b := [b[i] : i in perm];
  // Is it faster to do SwapRows and SwapCol?
  g := PermutationMatrix(Rationals(), perm)^(-1);
  gram := Transpose(g)*gram*g;
  mult := mult*g;
  return b, mult;
end function;

intrinsic GreedyReduce(L::ModDedLat) -> AlgMatElt
{Reduce L using the Greedy algorithm of Nguyen and Stehle.}
  lat := ZLattice(L);
  b := Basis(lat);
  gram := InnerProductMatrix(lat);
  b := [ChangeRing(Vector(Eltseq(x)), Rationals()) : x in b];
  gram_b := Matrix(b)*gram*Transpose(Matrix(b));
// b, mult := GreedyReduction(b, gram_b);
// return Transpose(mult)*gram_b*mult, Matrix(b);
  return magmaKohelReduction(gram_b);
end intrinsic;

primeSymbol := recformat <
        p  : RngIntElt, // prime
        power : RngIntElt,   // exponent
        ramified : BoolElt // whether ramified
      >;

function sign_vector(x, det, primes)
  vec := x eq -1 select 1 else 0;
  for symb in primes do
    value := HilbertSymbol(x, -det, symb`p);
    vec := 2*vec + (value eq -1 select 1 else 0);
  end for;
  return vec;
end function;

function GF2_solve_naive(vecs, start, target)
  upper := 2^#vecs;
  num_vecs := #vecs;
  for i in [start+1..upper-1] do
    x := 0;
    mask := upper div 2;
    for j in [0..num_vecs-1] do
      if (BitwiseAnd(i, mask) ne 0) then x := BitwiseXor(x, vecs[j+1]); end if;
      mask div:= 2;
    end for;
    if x eq target then return i; end if;
  end for;
  return 0;
end function;

function discriminant(q)
  a := q[1,1];
  b := q[2,2];
  c := q[3,3];
  f := q[2,3]+q[3,2];
  g := q[1,3]+q[3,1];
  h := q[1,2]+q[2,1];
  disc := 4*a*b*c-a*f^2-b*g+h*(f*g-c*h);
  return disc;
end function;

function Z_isotropic_mod_pp(q, p)
  pp := p*p;
  vec := [0,0,1];
  if Evaluate(q, vec) mod pp eq 0 then
    return vec;
  end if;
  vec[2] := 1;
  for z in [0..pp-1] do
    vec[3] := z;
    if Evaluate(q, vec) mod pp eq 0 then
      return vec;
    end if;
  end for;
  vec[1] := 1;
  for y in [0..pp-1] do
    for z in [0..pp-1] do
      if Evaluate(q, vec) mod pp eq 0 then
        return vec;
      end if;
    end for;
  end for;
  vec := [0,0,0];
  return vec;
end function;

function level_to_input(level : ramified_primes := [])
  facs := Factorization(level);
  ps := [x[1] : x in facs];
  es := [x[2] : x in facs];
  if IsEmpty(ramified_primes) then
    if IsEven(#ps) then
      ramified_primes := ps[1..#ps-1];
    else
      ramified_primes := ps;
    end if;
  else
    ramified_primes := [p : p in ramified_primes | p in ps];    
  end if;

  primes := [];
  for n in [1..#ps] do
    p := ps[n];
    prime := rec<primeSymbol | p := p, power := es[n],
                 ramified := p in ramified_primes>;

    Append(~primes, prime);
  end for;
  return primes;
end function;


// This is what Jeff does for ternary forms
// For quinary we actually need the ramification
// for each of the quaternion algebras - something to think about for later
function get_quad_form(input)
  det := 1;
  disc := 1;
  two_specified := false;
  num_ramified := 0;
  for symb in input do
    assert IsOdd(symb`power);
    if symb`p eq 2 then
      two_specified := true;
    end if;
    if symb`ramified then
      num_ramified +:= 1;
    end if;
    det *:= symb`p;
    for k in [0..symb`power-1] do
      disc *:= symb`p;
    end for;
  end for;
  assert IsOdd(num_ramified);  //"Must specify an odd number of ramified primes.";
  primes := [];
  target := 1;
  if not two_specified then
    s := rec < primeSymbol | p := 2, power := 0, ramified := false>;
    Append(~primes, s);
    target *:= 2;
  end if;
  for symb in input do
    Append(~primes, symb);
    target *:= 2;
    if symb`ramified then
      target +:= 1;
    end if;
  end for;
  fullbase := [];
  signs := [];

  Append(~fullbase, -1);
  Append(~signs, sign_vector(-1, det, primes));

  for symb in primes do
    Append(~signs, sign_vector(symb`p, det, primes));
    Append(~fullbase, symb`p);
  end for;

  p := 2;
  done := false;
  added_to_end := false;
  while not done do
    solution := 0;
    repeat
      solution := GF2_solve_naive(signs, solution, target);
      if solution ne 0 then
	mask := 2^#fullbase;
        b := -1;
        det2 := det;
	for q in fullbase do
	  mask := mask div 2;
	  if BitwiseAnd(solution, mask) ne 0 then
            b *:= q;
	    if q gt 0 then
	      if det2 mod q eq 0 then
	        det2 := det2 div q;
	      else
	        det2 *:= q;
	      end if;
	    end if;
	  end if;
	end for;
        mask := 2^#primes;
	for symb in primes do
	  mask := mask div 2;
          sign := (BitwiseAnd(target, mask) ne 0) select -1 else 1;
          assert HilbertSymbol(-b, -disc, symb`p) eq sign;  
	end for;
        good := true;
        for n in [#primes+1..#fullbase-1] do
	  sign := HilbertSymbol(-b, -disc, fullbase[n+1]);
	  if sign eq -1 then good := false; end if;
	end for;
	if good then
          done := true;
	  break;
	end if;
      end if;
    until solution eq 0;
    if done then break; end if;
    p := NextPrime(p);
    while disc mod p eq 0 do
      p := NextPrime(p);
    end while;
    if added_to_end then
      signs := signs[1..#signs-1];
      fullbase := fullbase[1..#fullbase-1];
    end if;
    Append(~signs, sign_vector(p, det, primes));
    Append(~fullbase, p);
    added_to_end := true;
  end while;
  b := -1;
  mask := 2^#fullbase;
  base := [2];
  for p in fullbase do
    mask div:= 2;
    if BitwiseAnd(solution, mask) ne 0 then
      b *:= p;
      if p gt 0 then
	if det mod p eq 0 then
	  det div:= p;
	else
	  det *:= p;
	   Append(~base, p);
	end if;
      end if;
    end if;
  end for;
  mask := 2^#primes;
  for symb in primes do
    mask div:= 2;
    sign := (BitwiseAnd(target, mask) ne 0) select -1 else 1;
    assert HilbertSymbol(-b, -disc, symb`p) eq sign;
  end for;
  a := 1;
  c := det;
  f := 0;
  g := 0;
  h := 0;
  b_q := SymmetricMatrix([a,h/2,b,g/2,f/2,c]);
  q := ChangeRing(QuadraticForm(b_q), Integers());
  N := Integers()!discriminant(b_q);
  assert N eq 4*Determinant(b_q);
  for p in base do
    pp := p*p;
    while N mod p^2 eq 0 do
      vec := Z_isotropic_mod_pp(q,p);
      assert Evaluate(q, vec) mod p^2 eq 0;
      if IsZero(vec) then
	break;
      elif vec[1] eq 0 and vec[2] eq 0 then
	assert vec[3] eq 1;
	assert g mod p eq 0;
	assert f mod p eq 0;
	assert c mod pp eq 0;
        c div:= pp;
	f div:= p;
	g div:= p;
      elif vec[1] eq 0 then
	b +:= c*vec[3]^2 + f*vec[3];
	f +:= 2*c*vec[3];
	h +:= g*vec[3];
	assert vec[2] eq 1;
	assert b mod pp eq 0;
	assert f mod p eq 0;
	b div:= pp;
	f div:= p;
	h div:= p;
      else
  	a +:= b*vec[2]^2+c*vec[3]^2+f*vec[2]*vec[3]+g*vec[3]+h*vec[2];
	g +:= 2*c*vec[3] + f*vec[2];
	h +:= 2*b*vec[2] + f*vec[3];
	assert vec[1] eq 1;
	assert a mod pp eq 0;
	assert g mod p eq 0;
	assert h mod p eq 0;
	a div:= pp;
	g div:= p;
	h div:= p;
      end if;
      b_q := SymmetricMatrix([a,h/2,b,g/2,f/2,c]);
      q := ChangeRing(QuadraticForm(b_q), Integers());
      N := Integers()!discriminant(b_q); 
    end while;
  end for;
//lat := LatticeWithGram(b_q);
//  b_q := InnerProductMatrix(MinkowskiReduction(lat : Canonical));
  b_q := magmaKohelReduction(b_q);
  a := b_q[1,1];
  b := b_q[2,2];
  c := b_q[3,3];
  f := b_q[2,3]+b_q[3,2];
  g := b_q[1,3]+b_q[3,1];
  h := b_q[2,1] + b_q[1,2];
  q := ChangeRing(QuadraticForm(b_q), Integers());
  for symb in primes do
    for j := 3 to symb`power by 2 do
      f *:= symb`p;
      g *:= symb`p;
      c *:= symb`p*symb`p;
    end for;
  end for;
  b_q := SymmetricMatrix([a,h/2,b,g/2,f/2,c]);
//  lat := LatticeWithGram(b_q);
//  b_q := InnerProductMatrix(MinkowskiReduction(lat : Canonical));
  b_q := magmaKohelReduction(b_q);
  a := b_q[1,1];
  b := b_q[2,2];
  c := b_q[3,3];
  f := b_q[2,3]+b_q[3,2];
  g := b_q[1,3]+b_q[3,1];
  h := b_q[2,1] + b_q[1,2];
  q := ChangeRing(QuadraticForm(b_q), Integers());
  x := Integers()!(4*a*b-h*h);
  mask := 2^#primes;
  for symb in primes do
    mask div:= 2;
    sign := (BitwiseAnd(target, mask) ne 0) select -1 else 1;
    assert HilbertSymbol(-x, -disc, symb`p) eq sign;
  end for;
  return 2*b_q;
end function;

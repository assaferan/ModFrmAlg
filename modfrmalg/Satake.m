freeze;

/****-*-magma-**************************************************************
                                                                            
                     Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
             
                                                                            
   FILE: Satake.m (algorithms for Satake polynomials)

   03/03/22: Creation

***************************************************************************/

// Exported intrinsics are:
// SatakePolynomialUnramified(M::ModFrmAlg : Split := false) -> RngUPolElt
// SatakePolynomial(f::ModFrmAlgElt, p::RngIntElt : d := Infinity()) -> .
// SatakePolynomialBallot(r::RngIntElt, a::RngIntElt) -> RngUPolElt

function DualRoot(alpha, G)
  return CoweightLattice(G)!(2/Norm(alpha) * alpha);
end function;

function get_monomial(R, coweight)
  exps := Eltseq(coweight);
  pos := [Maximum(e, 0) : e in exps];
  neg := [Maximum(-e, 0) : e in exps];
  return Monomial(R, pos cat neg);
end function;

function p_binom(r, k, p)
  res := 1;
  for l in [1..k] do
    res *:= (p^(r-l+1)-1) / (p^l - 1);
  end for;
  return res;
end function;

function SatakeTransform(mu, G, A, sqrt_p, r, K, k, a, R)
  alphas := PositiveRoots(G);
  mults := [1 : alpha in alphas];
  if (a eq 2) then
      mults := [ (&+Eltseq(alpha) eq 1) select 2 else 1 : alpha in alphas];
  end if;
  rho := 1/2*&+[mults[j]*alphas[j] : j in [1..#alphas]];
  W := WeylGroup(G);
  sum := 0;
  W_elts := [w : w in W];
  vprintf AlgebraicModularForms, 2 : "Computing Satake transform for k = %o, #W = %o\n i = ", k, #W;
  for i->w in W_elts do
    vprintf AlgebraicModularForms, 2 : "%o ", i;
    w_mu := CorootAction(W)(mu, w);
    // This might need handling of a denominator in general
    w_mu := ChangeRing(w_mu, Integers());
    //    if (r eq 1) then w_mu := [w_mu[1]]; end if;
    e_w_mu := get_monomial(A, w_mu);
    prod := K!e_w_mu;
    for j->alpha in alphas do
      alpha_d := DualRoot(alpha, G);
      w_alpha_d := CorootAction(W)(alpha_d, w);
      w_alpha_d := ChangeRing(w_alpha_d, Integers());
//      if (r eq 1) then w_alpha_d := [w_alpha_d[1]]; end if;
      e_w_alpha_d := get_monomial(A, w_alpha_d);
      // TODO : !! need some better way to determine the multiplicity of a root !
      mult := mults[j];
      prod *:= K!(1-sqrt_p^(2*mult)*e_w_alpha_d) / K!(1-e_w_alpha_d);
    end for;
    sum +:= prod;
  end for;
  den := Denominator(sum);
  assert IsMonomial(R!den);
  exps := Exponents(den);
  den_inv := Monomial(A, exps[r+1..2*r] cat exps[1..r]);
  assert den_inv * den eq 1;
  A_sum := Numerator(sum)*den_inv;
  assert K!A_sum eq sum;
  // sqrt_q := (a eq 2) select sqrt_p^2 else sqrt_p;
  // This should have worked in general, but W is not the same in the inert case.
  // K_mod_I_other := &+[sqrt_p^(2*CoxeterLength(W,w)) : w in W];
  K_mod_I := &*[(sqrt_p^(2*i) - 1) / (sqrt_p^2-1) : i in [1..r]];
  K_mod_I *:= &*[sqrt_p^(2*i) + 1 : i in [Maximum(1,a)..r+a-1]];
  // assert K_mod_I eq K_mod_I_other;
  num_neighbors := sqrt_p^(k*(k-1)) * p_binom(r,k,sqrt_p^2);
  min_i := Maximum(1, r+a-k);
  num_neighbors *:= &*[sqrt_p^(2*i) + 1 : i in [min_i..r+a-1]];
  p_exp := &+[mu[i]*rho[i] : i in [1..r]];
  sqrt_p_exp := Integers()!(2*p_exp);
  satake_mu := sqrt_p^(-sqrt_p_exp) * num_neighbors / K_mod_I * A_sum;
  return satake_mu;
end function;

function SatakePolynomialInner(G, a, r, F)
  S<sqrt_p> := FunctionField(F);
  RR<[c]> := PolynomialRing(S, r);
  RR_x<x> := PolynomialRing(RR);
  if r eq 0 then
    return RR_x!1;
  end if;
  // This is our patch for now to get the correct roots for the nonsplit case
  // Should do something more generic to get the structure of a reductive group
  cartan_type := CartanName(RootDatum(G`G0))[1];
  if (2*r ne n) then
	  //cartan_type := (cartan_type eq "D") select "B" else "D";
    cartan_type := "B";
  end if;
  /*
  if (r eq 1) and IsEven(Dimension(G)) then
      // D1 is not supported but D1 = A1
      G := GroupOfLieType("A1", BaseRing(G`G0));
  else
*/
      G := GroupOfLieType(StandardRootDatum(cartan_type, r),
			  BaseRing(G`G0));
 // end if;

  vprintf AlgebraicModularForms,2 : "Weyl group is of size %o\n", #WeylGroup(G);
      
  // We are doing it symbolically so that in the future we will be able to
  // compute it once and then plug different ps
  SS<[s]> := PolynomialRing(S, 2*r);
  I := ideal<SS | [s[i]*s[i+r]-1 : i in [1..r]]>;
  A := quo<SS|I>;
  s := [Sprintf("s%o", i) : i in [1..r]];
  s_inv := [Sprintf("s%o_inv", i) : i in [1..r]];
  AssignNames(~A, s cat s_inv);
  K := FieldOfFractions(A);
  R<[t]> := PolynomialRing(S, r);
  
  coeffs := [];
  for k in [1..r] do
    mu_seq := [1 : i in [1..k]] cat [0 : i in [1..r-k]];
    // if (r eq 1) then mu_seq := [1,-1]; end if;  
    mu := CoweightLattice(G)!(mu_seq);
    satake_mu := SatakeTransform(mu, G, A, sqrt_p, r, K, k, a, SS); 
    if (k eq r) and (a eq 0) then
	mu_seq := [1 : i in [1..r-1]] cat [-1];
	// if (r eq 1) then mu_seq := [-1,1]; end if;
	mu := CoweightLattice(G)!(mu_seq);
	satake_mu +:= SatakeTransform(mu, G, A, sqrt_p, r, K, k, a, SS);
    end if;
    cfs, mons := CoefficientsAndMonomials(satake_mu);
    exps := [Exponents(mon) : mon in mons];
    betas := [Eltseq(Vector(e[1..r]) - Vector(e[r+1..2*r])) : e in exps];
    abs_betas := [[Abs(b) : b in beta] : beta in betas];
    // Here we verify that this is a polynomial in s_i + s_i^(-1)
    abs_betas_idxs := [Index(betas, a) : a in abs_betas];
    assert &and[cfs[i] eq cfs[abs_betas_idxs[i]] : i in [1..#cfs]];
    satake_t := &+[cfs[Index(betas, a)]*Monomial(R, a) : a in Set(abs_betas)];
    h := hom<R-> A | [A.i + A.(i+r) : i in [1..r]] >;
    assert h(satake_t) eq satake_mu;
    is_sym, lin_comb := IsSymmetric(satake_t);
    b := S!ConstantTerm(lin_comb);
    sym_coeffs := [S!Coefficient(lin_comb, Parent(lin_comb).i, 1) : i in [1..k]];
//    b := S!ConstantTerm(satake_t);
//    lc := LeadingCoefficient(satake_t);
    //    assert lc*ElementarySymmetricPolynomial(R, k)+b eq satake_t;
    assert &+[sym_coeffs[i]*ElementarySymmetricPolynomial(R,i) : i in [1..k]] + b eq satake_t;
    assert sym_coeffs[k] ne 0;
    s := &+([0] cat [sym_coeffs[i] * (-1)^i * coeffs[i] : i in [1..k-1]]);
    Append(~coeffs, (-1)^k*(c[k] - b - s)/sym_coeffs[k]);
  end for;
  _<t> := PolynomialRing(RR);
  t_poly :=  t^r;
  if (r gt 0) then
     t_poly +:= &+[coeffs[i]*t^(r-i) : i in [1..r]];
  end if;
  x_poly := &+[Coefficient(t_poly, i)*x^(r-i)*(x^2+1)^i : i in [0..r]];
  return x_poly;
end function;

intrinsic SatakePolynomialUnramified(M::ModFrmAlg : Split := false) -> RngUPolElt
{Computes the generic Satake polynomial at an unramified prime for M, split if Split is set.}
    n := Rank(Module(M));
    if Split then
	r := n div 2;
    else
	r := n div 2 - 1;
    end if;
    a := n - 2*r;
    //    x_poly := SatakePolynomialInner(M`G, a, r, Rationals());
    x_poly := SatakePolynomialBallot(r, a);
    RR_x<x> := Parent(x_poly);
    RR<[c]> := BaseRing(RR_x);
    S<sqrt_p> := BaseRing(RR);
    /*
    if not Split then
	x_poly *:= (x+1)*(x-1);
    end if;
   */
    return x_poly;
end intrinsic;

intrinsic SatakePolynomial(f::ModFrmAlgElt, p::RngIntElt : d := Infinity()) -> .
{Computes the Satake polynomial of f at the prime p up to precision d.}
  M := f`M;
  G := M`G;
  L := Module(M);
  V := ReflexiveSpace(L);
  n := Dimension(V);
  // verify whether this is the number of eigenvalues we need.
  n_evs := Minimum(d, n div 2);
  // This is not the most efficient way - we could first check if the
  // group is split at p or not (compute r) and then compute only up to r
  // plugging in the eigenvalues
  R := BaseRing(L);
  pR := ideal<R | p>;
  evs, _ := [HeckeEigensystem(f, k : Precision := [pR])[1] :
			       k in [1..n_evs]];
  if n_evs lt n div 2 then
    evs cat:= [0 : i in [n_evs+1..n div 2]];
  end if;
  evs_fld := Universe(evs);
  evs_fld_x<x> := PowerSeriesRing(evs_fld); 
  V := L`Vpp[pR]`V;
  // This is to determine splitting or non-splitting.
  a := V`AnisoDim;
  r := V`WittIndex;
  f := V`RadDim;
  if (f eq 0) then
      split := (a lt 2);
      if split then
	  if not assigned M`LPolynomialSplit then
	      M`LPolynomialSplit := SatakePolynomialUnramified(M : Split);
	  end if;
	  x_poly := M`LPolynomialSplit;
      else
	  if not assigned M`LPolynomialNonSplit then
	      M`LPolynomialNonSplit := SatakePolynomialUnramified(M);
	  end if;
	  x_poly := M`LPolynomialNonSplit;
      end if;
  else
      // ramified case, take extra care
      eps := WittInvariant(L, pR);
      // !! TODO - check what is the correct thing to do in general
      if not assigned M`LPolynomialSplit then
	  M`LPolynomialSplit := SatakePolynomialUnramified(M : Split);
      end if;
      x_poly := M`LPolynomialSplit;
      x_poly *:= 1 + (eps/sqrt_p^(n-2))*x;
  end if;
  
  RR_x<x> := Parent(x_poly);
  RR<[c]> := BaseRing(RR_x);
  S<sqrt_p> := BaseRing(RR);
  // normalizing to have integral coefficients
  nor_lp := Evaluate(x_poly, (sqrt_p)^(n-2) * x);
  // in case it is too short
  evs := evs cat [0 : i in [1..r - #evs]];
  // in case it is too long
  evs := evs[1..r];
  ev_hom := hom< RR -> S | evs >;
  S_x<x> := PolynomialRing(S);
  ev_hom_poly := hom<RR_x -> S_x | ev_hom, [x] >;
  // now we plug in sqrt(p) back again into the polynomial
  // K<sqrtp> := QuadraticField(p);
  C := BaseRing(f`vec);
  C_x<x> := PolynomialRing(C);
  // K<sqrtp> := ext<C | x^2-p>;
  K, rts := SplittingField(x^2-p);
  sqrtp := rts[1];
  ev := hom<S -> K | sqrtp>;
  K_x<x> := PolynomialRing(K);
  ev_poly := hom<S_x -> K_x | ev, [x]>;
  ret := evs_fld_x!ev_poly(ev_hom_poly(nor_lp));
  _<x> := Parent(ret);
  if d ge 2*(n div 2) then
      evs_fld_x<x> := PolynomialRing(evs_fld);
      return evs_fld_x!Eltseq(ret);
  end if;
  return ret + O(x^(d+1));
end intrinsic;

procedure testSatake(Q, upTo)
    M := OrthogonalModularForms(LatticeWithGram(Q));
    fs := HeckeEigenforms(M);
    assert &and[&and[SatakePolynomial(f,p) eq LPolynomial(f,p) : p in PrimesUpTo(upTo) | 
		     Determinant(Q) mod p ne 0] : f in fs];
end procedure;

function SatakeLSeries(f : Precision := 0)
  function local_factor(p,d)
    poly := SatakePolynomial(f, p : d := d);
    CC := ComplexField();
    CC_x := PowerSeriesRing(CC);
    K := BaseRing(Parent(poly));
    r := Roots(DefiningPolynomial(K),CC)[1][1];
    if Type(K) eq FldRat then
      h := hom<K -> CC|>;
    else 
      h := hom<K -> CC | r>;
    end if;
    return CC_x![h(c) : c in Eltseq(poly)];
  end function;
  M := f`M;
  L := Module(M);
  n := Dimension(ReflexiveSpace(L));
  D := Integers()!(Norm(Discriminant(L)));

  if assigned Weight(M)`lambda then
    lambda := Weight(M)`lambda;
    lambda := lambda[1..n div 2];
    // Does this work in general?
    w := (#lambda gt 1) select lambda[1]-lambda[2] else lambda[1];
    sign := 1;
    gammas := (#lambda gt 1) select [x + lambda[2]
				       : x in [-w-1,-w,0,1]] else [0,w+1];
  elif assigned Weight(M)`weight then
     d := Weight(M)`weight[1];
     w := Weight(M)`weight[2];
     j := Weight(M)`weight[3];
     sign := (-1)^w*nu(D,d);
     gammas := [-w-1+j,-w+j,j,j+1];
  else
    // In this case, we don't really know the weight.
    // We guess it is trivial. Could we infer it from W?
     d := 1;
     w := 0;
     j := 0;
     sign := (-1)^w*nu(D,d);
     gammas := [-w-1+j,-w+j,j,j+1];
  end if;
  k := (n div 2)*(w+2) - ((n+1) mod 2);
  // We currently not include spinor norm
  return LSeries(k, gammas, D, local_factor :
		 Sign := sign, Precision := Precision);
end function;

// Here we use other methods to compute the Satake tranform, introduced in murphy.
// First, Ballot method

function all_ballots(n)
    all_as := CartesianPower([-1,1],n);
    as := [a : a in all_as | &and[&+[a[j] : j in [1..i]] ge 0 : i in [1..n]]];
    return [[a[i] : i in [1..n]] : a in as];
end function;

function BNs(s, p, t, n)
    // A := (p-1)^t;
    B_exp := #[i : i in [1..s] | n[i] eq -1] * 2 * t;
    B_exp +:= &+([0] cat [s-i : i in [1..s] | n[i] eq -1]);
    B := p^B_exp;
    // return A*B;
    return B;
end function;

function BPs(s, p, t, a, n)
    exp := &+([0] cat [s-i+2*t+a : i in [1..s] | n[i] eq -1]);
    return p^exp;
end function;

function BNd(p, t, r, s, a, b)
    // This was the explanation of this quantity in Murphy's thesis, but we modify it to match the code...
    assert #b eq 2*t;
    c := b[1..#b] cat [-b[2*t+1-i] : i in [1..2*t]];
    /*
    j := [idx : idx in [1..#c] | c[idx] eq -1];
    e := [#[k : k in [1..Min(j[i], 4*t+1-j[i])-1] | c[k] eq -1]-i+1 :
	  i in [1..2*t]];
    A := &*([1] cat [(p^e[i] - 1)/(p-1) * p^(e[i]-1) : i in [1..t]]);
   */
    A := 1;
    p_inds := [i-1 : i in [1..#c] | c[i] eq 1];
    p_inds := p_inds[t+1..#p_inds];
    for i in p_inds do
	special_e := #[x : x in c[Maximum(i, #c-i)+1..#c] | x eq -1] - #[x : x in c[i+2..#c] | x eq 1];
	vprintf AlgebraicModularForms, 2 : "at index %o special_e is %o\n", i, special_e;
	A *:= (p^special_e-1)*p^(special_e-1);
    end for;
    /*
    B_exp := (r-s+a)*#[i : i in [1..2*t] | b[i] eq -1];
    B_exp +:= &+([0] cat [2*t-i : i in [1..2*t] | b[i] eq -1]);
   */

//    B_exp := &+([0] cat [2*t-1-i : i in [0..2*t-1] | b[i+1] eq -1]);
    B_exp := &+([0] cat [2*t-i : i in [1..2*t] | b[i] eq -1]);
    
    B := p^B_exp;
    return A*B;
  
end function;

function BPd(p, r, s, t, a, b, num_ones)
    // c := b[1..#b] cat [-b[2*t+1-i] : i in [1..2*t]];
    // p_cols := [i : i in [0..4*t-1] | c[i+1] eq 1];
    // diag_first_half := [(i in p_cols) select 1 else -1 : i in [0..2*t-1]];
    //orbit_bins := [#[x : x in diag_first_half | x eq -1] + #[x : x in diag_first_half[1..i] | x eq -1]
    //		   + #[x : x in diag_first_half[i+1..t] | x eq 1] : i in [0..2*t]];
    // These just differ by the total number of -1
    // truncated_orbit_bins := [#[x : x in diag_first_half[1..i] | x eq -1]
    // + #[x : x in diag_first_half[i+1..t] | x eq 1] : i in [0..2*t]];
    // full_diag := initial_diag cat c cat [-i : i in Reverse(initial_diag)];
    
    c := [#[j : j in [1..i] | b[j] eq -1] + #[j : j in [i+1..2*t] | b[j] eq 1]
	  : i in [0..2*t]];
    // assert c eq truncated_orbit_bins;
    _<T> := PowerSeriesRing(Parent(p));
    
    //    A := Coefficient(&*[(1-p^c[i+1]*T)^(-1) : i in [0..2*t]], r-s);
    // A := Coefficient(&*[(1-p^c[i+1]*T)^(-1) : i in [0..2*t]], (num_ones - a) div 2);
    // B_exp := &+([0] cat [2*t-i+a+r-s : i in [1..2*t] | b[i] eq -1]);
    // B_exp := a*#[x : x in full_diag[1..#full_diag div 2] | x eq -1];
    // B_exp +:= #(&cat[[<i,j> : j in [i+1..#full_diag-1-i] | full_diag[j] eq 1] :
    //		     i in [1..#initial_diag + 2*t] | full_diag[i] eq -1]);
    B_exp := &+([0] cat [2*t-1-i : i in [0..2*t-1] | b[i+1] eq -1]);
    B_exp +:= ((num_ones + a) div 2)*#[x : x in b | x eq -1];
    B := p^B_exp;
    // f := &*[(1-p^truncated_orbit_bins[i+1]*T)^(-1) : i in [0..2*t]];
    f := &*[(1-p^c[i+1]*T)^(-1) : i in [0..2*t]];
    A := Coefficient(f, (num_ones - a) div 2);
    return A*B;
end function;

function possible_nus(G, a, mu : reps := true)
    r := Degree(mu);
    m := Eltseq(mu);
    if reps then
	all_ns := [*[n : n in CartesianPower([-1,1], i)] : i in [0..r]*];
	all_ns := &cat[[[n[j] : j in [1..i]] cat [0 : j in [i+1..r]] : n in all_ns[i+1]] : i in [0..r]];
    else
	all_ns := [n : n in CartesianPower([-1,0,1], r)];
    end if;
    num_0 := #[i : i in [1..r] | m[i] eq 0];
    diffs := [#[i : i in [1..r] | n[i] eq 0] - num_0 : n in all_ns];
    ns := [all_ns[j] : j in [1..#all_ns] | IsEven(diffs[j]) and diffs[j] ge 0];
    num_m1 := #[i : i in [1..r] | m[i] eq -1];
    if (a eq 0) and (num_0 eq 0) then
	ns := [n : n in ns | &and[n[i] ne 0 : i in [1..r]] or
			     IsEven(#[i : i in [1..r] | n[i] eq -1] - num_m1)];
    end if;
    return [CoweightLattice(G)![n[j] : j in [1..r]] : n in ns];
end function;

function coeff(a, m, n, sqrt_p)
    r := #m;
    dim := 2*r+a;
    num_0 := #[i : i in [1..r] | m[i] eq 0];
    t := (#[i : i in [1..r] | n[i] eq 0] - num_0) div 2;
    nz := [i : i in [1..r] | n[i] ne 0];
    s := IsEmpty(nz) select 0 else nz[#nz];
    // alphas := PositiveRoots(G);
    // rho := 1/2*&+alphas;
    rho2 := [dim-2*i : i in [1..r] ];
    sqrtp_exp := &+[rho2[i]*n[i] : i in [1..r]];
    sqrtp_exp := Integers()!(sqrtp_exp);
    
    p := sqrt_p^2;
    bs := all_ballots(2*t);
    if (a eq 0) and (num_0 eq 0) then
	bs := [b : b in bs | IsEven(#[bb : bb in b | bb eq -1])];
    end if;
    num_ones := dim - 2*(r - num_0);
    c := &+[BNd(p, t, r, s, a, b) * BPd(p, r, s, t, a, b, num_ones) : b in bs];
    c *:= BPs(s, p, t, a, n) * BNs(s, p, t, n);
    return sqrt_p^sqrtp_exp * c;
end function;

/*
function SatakeTransformBallot(G, a, mu)
  S<sqrt_p> := FunctionField(Rationals());
  r := Degree(mu);
  SS<[s]> := PolynomialRing(S, 2*r);
  I := ideal<SS | [s[i]*s[i+r]-1 : i in [1..r]]>;
  A := quo<SS|I>;
  s := [Sprintf("s%o", i) : i in [1..r]];
  s_inv := [Sprintf("s%o_inv", i) : i in [1..r]];
  AssignNames(~A, s cat s_inv);
//  K := FieldOfFractions(A);
//  R<[t]> := PolynomialRing(S, r);
  return &+[coeff(G, a, mu, nu, sqrt_p)*get_monomial(A, ChangeRing(nu, Integers())) : nu in possible_nus(G, a, mu)];
end function;
*/

intrinsic SatakePolynomialBallot(r::RngIntElt, a::RngIntElt) -> RngUPolElt
{Computes the Satake polynomial of an orthogonal group with split rank r, and
 anisotropic rank a, using ballot sequences,based on Murphy's thesis.}

  S<sqrt_p> := FunctionField(Rationals());
  
  R<[c]> := PolynomialRing(S, r);
  R_t<t> := PolynomialRing(R);
  
  elem := [R!1];
  for i in [1..r] do
      current_elem := c[i];
      mu := [1 : l in [1..i]] cat [0: l in [1..r-i]];
      
      for j := i-2 to 0 by -2 do
	  nu := [1 : l in [1..j]] cat [0: l in [1..r-j]];
	  scale := (i eq r) and (a eq 0) select 2 else 1;
	  current_elem -:= scale*coeff(a, mu, nu, sqrt_p)*elem[j+1];
      end for;

      current_elem /:= coeff(a, mu, mu, sqrt_p);
      Append(~elem, current_elem);
  end for;
  aux_poly := R_t!0;
  poly := R_t!0;
  for i in [0..r] do
      aux_poly +:= t^(r-i)*elem[i+1]*(-1)^i;
      poly +:= t^i*(t^2 + 1)^(r-i) * elem[i+1]*(-1)^i;
  end for;

  if a eq 2 then
      poly *:= (t+1)*(t-1);
  end if;
  return poly;
end intrinsic;

// !! TODO - add weight
procedure testSatakePolynomialBallot()
    // We test again the L polynomial expressions in Murphy's thesis
    S<sqrt_p> := FunctionField(Rationals());
    max_r := 4;
    R<[evs]> := PolynomialRing(S, max_r);
    R_x<x> := PolynomialRing(R);
    lpoly_hardcoded := AssociativeArray();
    for n in [3..8] do
	lpoly_hardcoded[n] := AssociativeArray();
    end for;
    lpoly_hardcoded[3][1] := x^2 - 1/sqrt_p*evs[1]*x + 1;
    lpoly_hardcoded[4][0] := x^4 - 1/sqrt_p^2*evs[1]*x^3 + (2+evs[2])/sqrt_p^2*x^2 - 1/sqrt_p^2*evs[1]*x+1;
    lpoly_hardcoded[4][2] := (x-1)*(x+1)*(x^2-1/sqrt_p^2*evs[1]*x+1);
    lpoly_hardcoded[5][1] := x^4 - 1/sqrt_p^3*evs[1]*x^3 +
			     ((evs[2] + sqrt_p^4 + 1)/sqrt_p^4)*x^2 -
			     1/sqrt_p^3*evs[1]*x + 1;
    lpoly_hardcoded[6][0] := x^6 - (evs[1]/sqrt_p^4)*x^5 +
			     ((1+sqrt_p^2+sqrt_p^4+evs[2])/sqrt_p^6)*x^4 -
			     ((2*evs[1]+evs[3])/sqrt_p^6)*x^3 +
			     ((1+sqrt_p^2+sqrt_p^4+evs[2])/sqrt_p^6)*x^2 - 1/sqrt_p^4*evs[1]*x + 1;
    lpoly_hardcoded[6][2] := (x-1)*(x+1)*(x^4 -
					  1/sqrt_p^4*evs[1]*x^3 +
					  (1-sqrt_p^2+sqrt_p^4+sqrt_p^6+evs[2])/sqrt_p^6*x^2 -
					  1/sqrt_p^4*evs[1]*x+1);
    lpoly_hardcoded[7][1] := x^6 - (evs[1]/sqrt_p^5)*x^5 +
			     ((evs[2]+1+sqrt_p^4+sqrt_p^8)/sqrt_p^8)*x^4 -
			     (((sqrt_p^4+1)*evs[1]+evs[3])/sqrt_p^9)*x^3 +
			     ((evs[2]+1+sqrt_p^4+sqrt_p^8)/sqrt_p^8)*x^2 -
			     1/sqrt_p^5*evs[1]*x + 1;
    lpoly_hardcoded[8][0] := x^8 - (evs[1]/sqrt_p^6)*x^7 +
			     ((evs[2]+sqrt_p^8 + 2*sqrt_p^4 +1)/sqrt_p^10)*x^6 -
			     ((evs[3] + evs[1]*(sqrt_p^4+sqrt_p^2+1))/sqrt_p^12)*x^5 +
			     ((evs[4]+2*evs[2]+2+2*sqrt_p^4+2*sqrt_p^8)/sqrt_p^12)*x^4-
			     ((evs[3] + evs[1]*(sqrt_p^4+sqrt_p^2+1))/sqrt_p^12)*x^3 +
			     ((evs[2]+sqrt_p^8 + 2*sqrt_p^4 +1)/sqrt_p^10)*x^2 -
			     1/sqrt_p^6*evs[1]*x + 1;
    lpoly_hardcoded[8][2] := (x-1)*(x+1)*(x^6 -
					  (evs[1]/sqrt_p^6)*x^5 +
					  (evs[2]+sqrt_p^10+sqrt_p^8+1)/sqrt_p^10*x^4 -
					  (evs[3]+evs[1]*(sqrt_p^6+sqrt_p^4-sqrt_p^2+1))/sqrt_p^12*x^3 +
					  (evs[2]+sqrt_p^10+sqrt_p^8+1)/sqrt_p^10*x^2 -
					  1/sqrt_p^6*evs[1]*x + 1);
    for n in [3..8] do
	vprintf AlgebraicModularForms, 1 : "Testing n = %o\n", n;
	min_aniso := n mod 2;
	max_aniso := 2;
	for a := min_aniso to max_aniso by 2 do
	    r := (n - a) div 2;
	    lpoly := SatakePolynomialBallot(r, a);
	    R0_x := Parent(lpoly);
	    R0 := BaseRing(lpoly);
	    S0<sqrt_p0> := BaseRing(R);
	    S0_hom := hom<S0 -> S | sqrt_p>;
	    R0_hom := hom<R0 -> R | S0_hom, [evs[i] : i in [1..Rank(R0)]]>;
	    im_poly := R_x![R0_hom(Coefficient(lpoly,i)) :  i in [0..Degree(lpoly)]];
	    assert im_poly eq lpoly_hardcoded[n][a];
	end for;
    end for;
end procedure;

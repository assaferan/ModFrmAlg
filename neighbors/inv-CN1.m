freeze;

// exports
// intrinsic Invariant(L::ModDedLat : Precision := 25) -> RngSerPowElt

// This script computes an invariant used to sort genus representatives.
intrinsic Invariant(L::ModDedLat : Precision := 25) -> RngSerPowElt
{Computes an invariant of the lattice L. At the moment, a theta series up to a certain precision.}
    return ThetaSeries(ZLattice(L), Precision);
end intrinsic;

// This is a temporary fix that only works for spherical polynomial representations,
// namely for weights of the form [k,0]
function embed_v_in_rep(v)
    return &cat[[v[i]] cat [0 : j in [1..Degree(v)-1]] : i in [1..Degree(v)]];
end function;

// This one is to make sure we got it all correctly
intrinsic ShimuraLift(f::RngSerPowElt, k::RngIntElt,
					  N::RngIntElt, prec::RngIntElt) -> RngSerPowElt
	  {return the Shimura Lift of f in the space M_k(N) with precision q^prec.}
    keys := PrimesUpTo(prec-1);
    eigenvalues := AssociativeArray(keys);
    for p in keys do
	chi1 := p eq 2 select 0 else (-1)^(((p-1) div 2)*(k div 2));
	eigenvalues[p] := Coefficient(f, p^2)+ chi1 * p^(k div 2 - 1);
    end for;
    R<q> := Parent(f);
    a := [BaseRing(R) | 1 : n in [1..prec-1]];
    for n in [2..prec-1] do
	if IsPrime(n) then
	    a[n] := eigenvalues[n];
	else
	    is_prime_power, p, e := IsPrimePower(n);
	    if is_prime_power then
		// Is n div p or p^(e-1) faster?
		a[n] := a[p]*a[p^(e-1)];
		if (N mod p ne 0) then
		    a[n] -:= p^(k-1) * a[p^(e-2)];
		end if;
	    else
		// Enough to find one divisor, is there a function to that?
		fac := Factorization(n);
		p_e := fac[1][1]^fac[1][2];
		m := n div p_e;
		a[n] := a[m]*a[p_e];
	    end if;
	end if;
    end for;
    lift := &+[a[n]*q^n : n in [1..prec-1]] + O(q^prec);
    return lift;
end intrinsic;

function MatrixSquareRoot(Q)
    f_Q<x> := CharacteristicPolynomial(Q);
    K<a> := SplittingField(Evaluate(f_Q, x^2));
    Q_K := ChangeRing(Q,K);
    evs := [x[1] : x in Eigenvalues(Q_K)];
    V := Matrix(&cat[Basis(Eigenspace(Q_K,ev)) : ev in evs]);
    D := V*Q*V^(-1);
    sqrt_D := DiagonalMatrix([Sqrt(x) : x in Diagonal(D)]);
    sqrt_Q := V^(-1)*sqrt_D*V;
    assert sqrt_Q^2 eq Q;
    return sqrt_Q;
end function;

// This does not include the constant coefficient, coming from the 0 vector
function Theta1(f, prec)
    v := f`vec;
    h_dims := [Dimension(h) : h in f`M`H];
    h_dimsum := [&+h_dims[1..i] : i in [0..#h_dims]];
    v_h := [Eltseq(v)[h_dimsum[i]+1..h_dimsum[i+1]] : i in [1..#f`M`H]];
    H := [ChangeRing(h, BaseRing(v)) : h in f`M`H];
    vecs := [* &+[v_h[j][i]*H[j]`embedding(H[j].i) : i in [1..Dimension(H[j])]]
	     : j in [1..#H] *];
    if IsTrivial(f`M`W) then
	n := Rank(InnerForm(f`M));
	all_polys := [* [PolynomialRing(BaseRing(v),n^2)!1] : vec in vecs *];
    else
	all_polys := [* Names(Parent(vec)`M) : vec in vecs *];
    end if;
    vecvec := [* vec`m`vec : vec in vecs *];
    polys := [*&+[vecvec[j][i]*all_polys[j][i] : i in [1..#all_polys[j]]]
	      : j in [1..#all_polys]*];
    _<q> := PowerSeriesRing(BaseRing(v));
    reps := Representatives(Genus(f`M));
    aut := [#AutomorphismGroup(r) : r in reps];
    fs := [];
    assert #reps eq #H;
    for i in [1..#reps] do
	r := reps[i];
	shortvecs := ShortVectors(ZLattice(r), 2*(prec-1));
	shortvecs cat:= [<-v[1],v[2]> : v in shortvecs];
	// Here we divide by 2 to obtain the actual modular form
	// (which could be of half integral weight, when the rank is odd)
	f_r := &+[Evaluate(polys[i], embed_v_in_rep(v[1]))*q^(Integers()!v[2] div 2)
		  : v in shortvecs];
	Append(~fs, f_r);
    end for;
    theta := &+[aut[i]^-1*fs[i] : i in [1..#reps]] + O(q^prec);
    // We return a normalized eigenform
    nonzero := exists(pivot){i : i in [1..prec-1] | Coefficient(theta,i) ne 0};
    if nonzero then
	theta := Coefficient(theta,pivot)^(-1)*theta;
    end if;
    return theta;
end function;

procedure TestTheta1(prec)
    // Here we test the lift from Yoshida's paper    
    for N in [2,11] do
	for k in [0..6] do
	    Q := TernaryQuadraticLattices(N^2)[1];
	    M := OrthogonalModularForms(Q,[k,0]);
	    num_eis := (k eq 0) select 1 else 0;
	    if (Dimension(M) gt num_eis) then
		fs := HeckeEigenforms(M);
		for j in [num_eis+1..#fs] do
		    f := HeckeEigenforms(M)[j];
		    theta := Theta1(f, prec^2);
		    if IsZero(theta) then continue; end if;
		    lift := ShimuraLift(theta, 2*(k+1), N, prec);
		    // !!! TODO - can we make them match also when p divides N ?
		    coeffs := [Coefficient(lift, i) : i in [1..prec-1] | GCD(i,N) eq 1];
		    // Check that it is in the right space
		    nfs := Newforms(ModularForms(N, 2*(k+1)));
		    found := false;
		    idxs := [0,0];
		    for idx1 in [1..#nfs] do
			for idx2 in [1..#nfs[idx1]] do
			    nfs_coeffs := [Coefficient(nfs[idx1][idx2],i) :
                                           i in [1..prec-1] | GCD(i,N) eq 1];
			    F1 := Universe(coeffs);
			    F2 := Universe(nfs_coeffs);
			    if (Type(F1) ne FldRat) and (Type(F2) ne FldRat) then
				is_isom, phi := IsIsomorphic(F1, F2);
			    else
				is_isom := IsIsomorphic(F1,F2);
				phi := Automorphisms(Rationals())[1];
			    end if;
			    if (is_isom) then
				auts := Automorphisms(Universe(coeffs));
				for aut in auts do
				    nfs_coeffs_emb := [phi(aut(x)) : x in nfs_coeffs];
				    if coeffs eq nfs_coeffs_emb then
					found := true;
					idxs := [idx1, idx2];
					break;
				    end if;
				end for;
			    end if;
			    if found then break; end if;
			end for;
			if found then break; end if;
		    end for;
		    assert found;
		    // Verify L-functions
		    nf := nfs[idxs[1]][idxs[2]];
		    assert &and[Coefficient(nf,p) eq HeckeEigenvalue(f,p)*p^k
				: p in PrimesUpTo(prec-1) | N mod p ne 0];
		end for;
	    end if;
	end for;
    end for;
    return;
end procedure;

// Here there is a question by what do we bound the vectors,
// as we do not have control on all entries of the Gram matrix
// (maybe we can do this, but requires adaptation of LLL)
// For now we bound the norm of both vectors (and not bound their inner product)
function Theta2(f, prec)
    v := f`vec;
    // we no longer use the power series ring, because we have negative powers,
    // and this forces some cumbersome operations.
    // Instead we use a hash table mapping the exponents to the coefficient
    coeffs := AssociativeArray();
    reps := Representatives(Genus(f`M));
    for i in [1..#reps] do
	r := reps[i];
	shortvecs := ShortVectors(ZLattice(r), prec);
	shortvecs cat:= [<-v[1],v[2]> : v in shortvecs];
	num_auts := #AutomorphismGroup(r);
	wt := num_auts^-1*v[i];
	for v1,v2 in shortvecs do
	    if (v1[1] eq v2[1]) or (v1[1] eq -v2[1]) then
		continue;
	    end if;
	    key := <v1[2], (v1[1], v2[1]), v2[2]>;
	    if not IsDefined(coeffs, key) then
		coeffs[key] := 0;
	    end if;
	    coeffs[key] +:= wt;
	end for;
    end for;
    return coeffs;
end function;

// This is the general theta series.
// For g = 1,2 it is slower than the implementations above
function ThetaSiegel(f, g, prec)
    v := f`vec;
    // we no longer use the power series ring, because we have negative powers,                
    // and this forces some cumbersome operations in magma                                     
    // Instead we use a hash table mapping the exponents to the coefficient
    coeffs := AssociativeArray();
    reps := Representatives(Genus(f`M));
    for i in [1..#reps] do
        r := reps[i];
        shortvecs := ShortVectors(ZLattice(r), prec);
        shortvecs cat:= [<-v[1],v[2]> : v in shortvecs];
	num_auts := #AutomorphismGroup(r);
        wt := num_auts^-1*v[i];
	subseqs := Subsequences(Set(shortvecs), g);
	for xs in subseqs do
	    vecs := [x[1] : x in xs];
	    mat := Matrix(vecs);
            if (Rank(mat) ne g) then
                continue;
            end if;
            key := &cat[[(vecs[i], vecs[j]) : j in [1..i]] : i in [1..g]];
            if not IsDefined(coeffs, key) then
                coeffs[key] := 0;
            end if;
            coeffs[key] +:= wt;
        end for;
    end for;
    return coeffs;
end function;

// Below is Adam's code, working with the genus
/*
function theta2(gr:bd1 := 100, bd2 := 10, sumbound := 20, silent := false, stable := 5)
  Z := Integers();
  Zn := RSpace(Z,#gr);
  ths := [ThetaSeries(i,bd1): i in gr];
  thvecs := [[Coefficient(t,i): i in [0..bd1 by 2]]: t in ths];
  // vshort := [*[s*v[1]: s in [1,-1], v in ShortVectors(g,2,bd2)]: g in gr*];
  // vns := [[*[v: v in vs|Norm(v) eq i]: vs in vshort*]: i in [2..bd2 by 2]];
  vns := [[*[s*v[1]: s in [1,-1], v in ShortVectors(g,n,n)]: g in gr*]: n in [2..bd2 by 2]];
  dims := [];
  ijpairs := [[i,j]: j in [1..i], i in [1..bd2 div 2]|i+j le sumbound/2];
  Sort(~ijpairs,func<x,y|&+[#vns[x[1],i]*#vns[x[2],i]-#vns[y[1],i]*#vns[y[2],i]: i in [1..#gr]]>);
  ker_th := Kernel(Matrix(thvecs));
  needed_inds := [x: x in [1..#gr]|exists{v: v in Basis(ker_th)|v[x] ne 0}];
  for ij in ijpairs do
    i,j := Explode(ij);
    pairs_ij := [n in needed_inds select {*Z|(x,y): x in vns[i,n], y in vns[j,n]*} else {*Z|*}: n in [1..#gr]];
    max := Max(&join pairs_ij join {*0*});
    thvecs := [thvecs[i] cat [Multiplicity(pairs_ij[i],n): n in [0..max]]: i in [1..#gr]];
    ker_th := Kernel(Matrix(thvecs));
    needed_inds := [x: x in [1..#gr]|exists{v: v in Basis(ker_th)|v[x] ne 0}];
    dim := #thvecs-Rank(Matrix(thvecs));
    Append(~dims,dim);
    if not silent then printf "%o ", <i,j,dim,#needed_inds>; end if;
    //thvecs := [Eltseq(i): i in Rows(Transpose(Matrix(Basis(RowSpace(Transpose(Matrix(thvecs)))))))];
    if Dimension(ker_th) eq 0 then /* "independent"; break i; */ /* return true, sub<Zn|>; end if;
    if #dims ge stable+1 and dim eq dims[#dims-stable] then return false, Kernel(Matrix(thvecs)); end if;
end for;
return false, Kernel(Matrix(thvecs));
end function;

function theta1(gr:bd := 100)
    ths := [ThetaSeries(i,bd): i in gr];
    thvecs := [[Coefficient(t,i): i in [0..bd by 2]]: t in ths];
    return Dimension(Kernel(Matrix(thvecs))) eq 0;
end function;

function theta1_ker(gr:bd := 100)
    ths := [ThetaSeries(i,bd): i in gr];
    thvecs := [[Coefficient(t,i): i in [0..bd by 2]]: t in ths];
    return Kernel(Matrix(thvecs));
end function;
*/

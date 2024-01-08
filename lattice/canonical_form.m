freeze;

function IsWellRounded(A)
    L := LatticeWithGram(A);
    minA := ShortestVectors(L);
    LminA := Lattice(ChangeRing(Matrix(minA),Rationals()), A);
    return Rank(LminA) eq Rank(L);
end function;

function V_wr_cvp(A)
    assert IsWellRounded(A);
    L := LatticeWithGram(A);
    minA := &cat[[v,-v] : v in ShortestVectors(L)];
    LminA := Lattice(ChangeRing(Matrix(minA),Rationals()), A);
    assert Rank(LminA) eq Rank(L);
    Zn := LatticeWithGram(A);
    Q, quo := Zn / LminA;
    cs := [ChangeRing(Vector(q@@quo), Rationals()) : q in Q];
    B := ChangeRing(Matrix(Basis(LminA)),Rationals());
    L_B := LatticeWithGram(B * A * Transpose(B));
    ret := [Vector(ChangeRing(v, Rationals())) : v in minA];
    ret cat:= &cat[[c - Vector(ChangeRing(v, Rationals())*B) : v in ClosestVectors(L_B, c*B^(-1))] : c in cs | not IsZero(c)];
    return ret;
end function;

function satspan(v, A)
    v_mat := Matrix(v);
    d := Denominator(v_mat);
    dv_mat := ChangeRing(d*v_mat, Integers());
    // hnf_mat := VerticalJoin(dv_mat, d*IdentityMatrix(Integers(),Ncols(v_mat)));
    H := HermiteForm(dv_mat);
    H_basis := [Vector(r) : r in Rows(H)[1..Rank(H)]];
    sat_basis := 
	ChangeRing(Matrix([GCD(Eltseq(v))^(-1) * ChangeRing(v,Rationals()) 
			   : v in H_basis]), Rationals());
    return Lattice(sat_basis, A);
end function;

function V_ms(A : max_num := Infinity())
    A := ChangeRing(A, Rationals());
    L := LatticeWithGram(A);
    max_norm := Maximum(Diagonal(A));
    all_vs := ShortVectors(L, max_norm);
    norms := {v[2] : v in all_vs};
    norms := Sort([n : n in norms]); 
    VA := [];
    for n in norms do
	VA cat:= &cat[[v[1],-v[1]] : v in all_vs | v[2] eq n];
	if (#VA ge max_num) then
	    return VA;
	end if;
	Lsub := sub<L | VA>;
	if (Lsub eq L) then
	    return VA;
	end if;
    end for;
    Lsub := sub<L | VA>;
    assert Lsub eq L;
    return VA;
end function;

function V_cvp(A : max_num := Infinity())
    A := ChangeRing(A, Rationals());
    L := LatticeWithGram(A);
    max_norm := Maximum(Diagonal(A));
    all_vs := ShortVectors(L, max_norm);
    norms := {v[2] : v in all_vs};
    norms := Sort([n : n in norms]);
//    minA := &cat[[v,-v] : v in ShortestVectors(L)];
    minA := [];
    rsub := 0;
    norm_idx := 0;
    while (rsub lt Rank(L)) do
	norm_idx +:= 1;
	n := norms[norm_idx];
	minA cat:= &cat[[v[1],-v[1]] : v in all_vs | v[2] eq n];
	if (#minA ge max_num) then
	    return minA;
	end if;
	LminA := sub<L | minA>;
	if (LminA eq L) then
	    return minA;
	end if;
	// LminA := Lattice(ChangeRing(Matrix(minA),Rationals()), A);
	L1 := satspan(Basis(LminA), A);
	B1 := ChangeRing(Matrix(Basis(L1)),Rationals());
	A1 := B1 * A * Transpose(B1);
	B2 := Transpose(Matrix(Basis(Kernel(A*Transpose(B1)))));
	proj := B2 * (Transpose(B2)*A*B2)^(-1) * Transpose(A*B2);
	B2 := ChangeRing(Matrix(Basis(Lattice(Transpose(proj)))), Rationals());
	A2 := B2 * A * Transpose(B2);
	r := Rank(L1);
	if (r eq Rank(L)) then
	    V_cvp_A2 := [];
	else
	    V_cvp_A2 := V_cvp(A2 : max_num := max_num);
	end if;
	A1_part := [Vector(Rationals(), v)*B1 : v in V_wr_cvp(A1)];
	A2_part := [Vector(v)*B2 : v in V_cvp_A2];
	union_A2_part := &cat[ClosestVectors(L,v) : v in A2_part];
	VA := A1_part cat union_A2_part;
	VA := [v : v in VA | v ne 0];
	Lsub :=  sub<L | VA>;
	rsub := Rank(Lsub);
    end while;
    /*
    if Rank(Lsub) lt Rank(L) then
	Q, quo := L / Lsub;
	cs := [q@@quo : q in Generators(Q)];
	max_nc := Maximum([Norm(c) : c in cs]);
	svs := ShortVectors(L, max_nc);
	ns := Sort([n : n in {v[2] : v in svs}]);
	for c in cs do
	    for n in ns do
		vs := [v[1] : v in svs | (v[2] eq n) and (v[1]-c) in Lsub];
		if (#vs gt 0) then
		    cs cat:= vs;
		    break;
		end if;
	    end for;
	end for;
	
	cs cat:= &cat[[v[1] : v in ShortVectors(L,Norm(c)) | v[1]-c in Lsub] 
		      : c in cs];
	
	cs := [ChangeRing(c, Rationals()) : c in cs];
	cs cat:= [-c : c in cs];
	VA cat:= &cat[[Vector(c - ChangeRing(v,Rationals())) 
		       : v in ClosestVectors(Lsub, Vector(c)) ] 
		      : c in cs];
	Lsub :=  sub<L | VA>;
    end if;
    */
    assert Rank(Lsub) eq Rank(L);
    Q, quo := L / Lsub;
    B := ChangeRing(Matrix(Basis(Lsub)),Rationals());
    L_B := LatticeWithGram(B * A * Transpose(B));
    cs := [ChangeRing(q@@quo, Rationals()) : q in Q];
    VA cat:= &cat[[Vector(c - ChangeRing(v, Rationals())*B) : v in ClosestVectors(L_B, Vector(c*B^(-1)))] : c in cs | not IsZero(c)];
    Lsub :=  sub<L | VA>;
    assert Lsub eq L;
    return VA;
end function;

function V_best(A)
    // Ad := GramMatrix(LLL(Dual(LatticeWithGram(A))));
    // Ad := GramMatrix(Dual(LatticeWithGram(A) : Rescale := false));
    VAs := [];
    // At the moment something is wrong with using duals, so we don't use them
    // for B in [A, Ad] do
    for B in [A] do
	Append(~VAs, <[Vector(v) : v in V_ms(B)],B>);
	try
	    Append(~VAs, <[Vector(v) : v in V_cvp(B )],B>);
	catch e
	    continue;
	end try;
    end for;
    sorted := Sort(VAs, func<x,y | #x[1]-#y[1]>);
    // return sorted[1];
    return sorted[1][1];
end function;

function V_best_with_dual(A)
    Ad := GramMatrix(LLL(Dual(LatticeWithGram(A))));
    VAs := [];
    max := Infinity();
    for B in [A, Ad] do
	for Vchar in [V_ms, V_cvp] do
	    VA := [Vector(v) : v in Vchar(B : max_num := max)];
	    Append(~VAs, <VA,B>);
	    if (#VA lt max) then
		max := #VA;
	    end if;
	end for;
    end for;
    sorted := Sort(VAs, func<x,y | #x[1]-#y[1]>);
    return sorted[1];
end function;

function T1(W)
    a := Maximum(Eltseq(W))+1;
    b := a + 1;
    p := Nrows(W);
//    W_prime := MatrixRing(Integers(),p+2)!0;
    W_prime := MatrixRing(Rationals(),p+2)!0;
    for i in [1..p] do
	for j in [i+1..p] do
	    W_prime[i,j] := W[i,j];
	end for;
	W_prime[i,p+1] := W[i,i];
	W_prime[i,p+2] := a;
    end for;
    W_prime[p+1,p+2] := b;
    for i in [1..p+2] do
	for j in [1..i-1] do
	    W_prime[i,j] := W_prime[j,i];
	end for;
    end for;
    return W_prime;
end function;

function bits(s,w)
    return [BitwiseAnd(ShiftRight(s,k),1) : k in [0..w-1]];
end function;

function T2(W)
    // Apparently the sort key doesn't really matter,
    // as the labels will be determined by the binary digits.
    // S := Sort([s : s in Set(Eltseq(W))], 
    // func< x,y | Abs(x) eq Abs(y) select x-y else Abs(x)-Abs(y) >);
    S := Sort([s : s in Set(Eltseq(W))]);
    w := Ceiling(Log(2,#S));
    all_bits := [bits(s,w) : s in [0..#S-1]];
    all_bits_bool := [[all_bits[s][k] eq 1 : k in [1..w]]
		      : s in [1..#S]];
    p := Nrows(W);
    lut := AssociativeArray(S);
    for i->s in S do
	lut[s] := i;
    end for;
    vertices := [];
    edges := [];
    for i in [1..p] do
	v_nbrs := [[<i_prime,k-1> : i_prime in [i+1..p] | all_bits_bool[lut[W[i,i_prime]]][k] ] cat [<i,k_prime> : k_prime in [k..w-1]] : k in [1..w]];
	vertices cat:= [<i,k> : k in [0..w-1]];
	edges cat:= v_nbrs;
    end for;
    vertices := {@ v : v in vertices @};
    edges := [{@ e : e in es @} : es in edges];
    wts := [v[2] : v in vertices];
    G := Graph<vertices|edges>;
    AssignLabels(VertexSet(G),wts);
    return G;
end function;

function U_V(A)
    A := ChangeRing(A, Rationals());
    VA, A := Explode(V_best_with_dual(A));
    // This is not really needed, we just keep track of the weights
    // G_A := CompleteGraph(#VA);
    B := ChangeRing(Matrix(VA),Rationals());
    W := B * A * Transpose(B);
    G := T1(W);
    T2G := T2(G);
    T2G_can, _, _, labels := CanonicalGraphMap(T2G);
    p := Nrows(G);
    S := [s : s in Set(Eltseq(G))];
    w := Ceiling(Log(2,#S));
    perm := [Minimum([Index(labels, <i,k>) : k in [0..w-1]]) : i in [1..p]];
    // this is the ordering of the vertices in G
    perm_inv := [Index(perm, i) : i in [1..#perm]];
    p -:= 2;
    v := [VA[i] : i in perm_inv | i le p];
    QA := ChangeRing(Transpose(Matrix(v)), Integers());
    H, U_inv := HermiteForm(QA);
    U := U_inv^(-1);
    assert U*H eq Transpose(Matrix(v));
    return U, A;
end function;

/*
function CanonicalForm(A)
    U := U_V(A);
    can_A := Transpose(U)*A*U;
    return can_A;
end function;
*/

intrinsic CanonicalForm(A::AlgMatElt) -> AlgMatElt
{Return a canonical form for the positive definite matrix A.}
    Ared := GramMatrix(LLL(LatticeWithGram(A)));
    U, Ared := U_V(Ared);
    can_A := Transpose(U)*Ared*U;
    return can_A;
end intrinsic;

intrinsic CanonicalForm(L::Lat) -> AlgMatElt
{Return a canonical form for L.}
  b := Basis(L);
  gram := InnerProductMatrix(L);
  b := [ChangeRing(Vector(Eltseq(x)), Rationals()) : x in b];
  A := Matrix(b)*gram*Transpose(Matrix(b));
  return CanonicalForm(A);
end intrinsic;

/*
intrinsic CanonicalForm(L::ModDedLat) -> AlgMatElt
{Return a canonical form for L.}
  lat := ZLattice(L);
  return CanonicalForm(lat);
end intrinsic;

intrinsic CanonicalForm(L::LatNF) -> AlgMatElt
{Return a canonical form for L.}
  return CanonicalForm(LatticeFromLatNF(L));
end intrinsic;
*/

// checks that V transforms well under linear transformations
procedure test_V(A : Vchar := V_cvp)
    A := ChangeRing(A, Integers());
    T := RandomGLnZ(Nrows(A),33,17);
    TA := T*A*Transpose(T);
    A := GramMatrix(LLL(LatticeWithGram(A)));
    TA := GramMatrix(LLL(LatticeWithGram(TA)));
    _, T := IsIsometric(LatticeWithGram(A), LatticeWithGram(TA));
    assert TA eq T*A*Transpose(T);
    A := ChangeRing(A, Rationals());
    T := ChangeRing(T, Rationals());
    TA := ChangeRing(TA, Rationals());
    VA := Vchar(A);
    VTA := Vchar(TA);
    VA := [ChangeRing(v,Rationals()) : v in VA];
    VTA := [ChangeRing(v,Rationals()) : v in VTA];
    assert {w*T : w in VTA} eq Set(VA);
    return;
end procedure;

procedure test_V_with_dual(A : Vchar := V_best_with_dual)
    A := ChangeRing(A, Integers());
    T := RandomGLnZ(Nrows(A),33,17);
    TA := T*A*Transpose(T);
    A := GramMatrix(LLL(LatticeWithGram(A)));
    TA := GramMatrix(LLL(LatticeWithGram(TA)));
    _, T := IsIsometric(LatticeWithGram(A), LatticeWithGram(TA));
    assert TA eq T*A*Transpose(T);
    A := ChangeRing(A, Rationals());
    T := ChangeRing(T, Rationals());
    TA := ChangeRing(TA, Rationals());
    VB, B := Explode(Vchar(A));
    VTB, TB := Explode(Vchar(TA));
    _, T := IsIsometric(LatticeWithGram(B), LatticeWithGram(TB));
    T := ChangeRing(T, Rationals());
    VB := [ChangeRing(v,Rationals()) : v in VB];
    VTB := [ChangeRing(v,Rationals()) : v in VTB];
    assert {w*T : w in VTB} eq Set(VB);
    return;
end procedure;


// check that Stab(A) maps into Stab(G_A)
// Cannnot establish surjectivity yet.
procedure test_W(A)
    A := ChangeRing(A, Integers());
    A := GramMatrix(LLL(LatticeWithGram(A)));
    A := ChangeRing(A, Rationals());
    VA := V_cvp(A);
    B := ChangeRing(Matrix(VA),Rationals());
    W := B * A * Transpose(B);
    stabA := AutomorphismGroup(LatticeWithGram(A));
    gens := Generators(stabA);
    // checking property (ii) of VA
    assert &and[{v*ChangeRing(S,Rationals()) : v in VA} eq Set(VA) : S in gens];
    imgs := [];
    for S in gens do
	sig := [Index(VA, v*ChangeRing(S, Rationals())) : v in VA];
	Append(~imgs, sig);
    end for;
    p := #VA;
    assert &and[&and[W[sig[i],sig[j]] eq W[i,j] : i,j in [1..p]] : sig in imgs];
end procedure;

function autT1_to_aut_T2(perm, w, vertexGset)
    p := #GSet(Parent(perm));
    big_perm := &cat[[Index(vertexGset, vertexGset[(i^perm-1)*w+j])
		      : j in [1..w]] : i in [1..p]];
    return Sym(w*p)!big_perm;
end function;

function autT2_to_autT1(sig, w, p)
    perm := [((w*i+1)^sig) div w + 1 : i in [0..p+1]];
    return Sym(p+2)!perm;
end function;

function autG_to_autT1(sig)
    p := #GSet(Parent(sig));
    perm := [i^sig : i in [1..p]] cat [p+1,p+2];
    return Sym(p+2)!perm;
end function;

function autT1_to_autG(sig)
    p := #GSet(Parent(sig))-2;
    perm := [i^sig : i in [1..p]];
    return Sym(p)!perm;
end function;
			 

procedure test_T2(A)
    A := ChangeRing(A, Integers());
    A := GramMatrix(LLL(LatticeWithGram(A)));
    A := ChangeRing(A, Rationals());
    VA := V_cvp(A);
    B := ChangeRing(Matrix(VA),Rationals());
    W := B * A * Transpose(B);
    G := T1(W);
    T2G := T2(G);
    autT2G, vertexGset, _, _, _, _ := AutomorphismGroup(T2G);
    act_vertices := Action(autT2G, vertexGset);
    p := #VA;
    S := [s : s in Set(Eltseq(G))];
    w := Ceiling(Log(2,#S));
    perms := [[Index(vertexGset, vertexGset[i]^act_vertices(sig))
	       : i in [1..(p+2)*w]] : sig in Generators(autT2G)];
    stabT2G := sub<Sym((p+2)*w) | perms>;
    stabA := AutomorphismGroup(LatticeWithGram(A));
    gens := Generators(stabA);
    imgs := [];
    for g in gens do
	assert {v*ChangeRing(g, Rationals()) : v in VA} eq Set(VA);
	sig := [Index(VA, v*ChangeRing(g, Rationals())) : v in VA];
	Append(~imgs, sig);
    end for;
    // imgs are now automorphisms of W, turning to automorphisms of G
    imgs := [sig cat [p+1,p+2] : sig in imgs];
    assert &and[&and[G[sig[i],sig[j]] eq G[i,j] : i,j in [1..p+2]]
		: sig in imgs];
    // converting to automorphisms of T2G
    big_perms := [&cat[[Index(vertexGset, vertexGset[(sig[i]-1)*w+j])
			: j in [1..w]] : i in [1..p+2]] : sig in imgs];
    stabA_im := sub<Sym((p+2)*w) | big_perms>;
end procedure;

function num_V(A)
    VA, A := Explode(V_best_with_dual(A));
    return #VA;
end function;

procedure test_canonical(A)
    T := Matrix(RandomGLnZ(Nrows(A),33,17));
    TA := T*A*Transpose(T);
    canA := CanonicalForm(A);
    canTA := CanonicalForm(TA);
    assert canA eq canTA;
end procedure;

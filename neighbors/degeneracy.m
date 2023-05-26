import "hecke-CN1.m" : finalizeHecke, processNeighborWeight;

function BuildHalfNeighbor(nProc : BeCareful := false, UseLLL := false, Perestroika := false, Similarity := 1)

    assert nProc`isoSubspace ne [];
    
    // The affine data.
    Vpp := nProc`L`Vpp[nProc`pR];

    // Shortcut for the projection map modulo pR^2.
    proj := Vpp`proj_pR2;

    // The dimension of the isotropic subspaces.
    k := nProc`k;

    // The lattice.
    L := nProc`L;

    // The prime
    pR := nProc`pR;

    // The base ring.
    R := BaseRing(L);

    // The reflexive space.
    Q := ReflexiveSpace(L);

    // The dimension.
    dim := Dimension(Q);

    // Degree of the field extension over the rationals.
    deg := Degree(BaseRing(Q));

    // for profiling reasons we need here a function
    function __pullUp(nProc, R, dim, proj)
      if Type(R) eq RngInt then
        Univ := RSpace(R, dim);
        XX := [Univ | x : x in nProc`X_skew];
        ZZ := [Univ | z : z in nProc`Z];
        UU := [Univ | u : u in nProc`U];
      else
        XX := [ Vector([ e @@ proj : e in Eltseq(x) ]) : x in nProc`X_skew ];
        ZZ := [ Vector([ e @@ proj : e in Eltseq(z) ]) : z in nProc`Z ];
        UU := [ Vector([ e @@ proj : e in Eltseq(u) ]) : u in nProc`U ];
      end if;
      return XX, ZZ, UU;
    end function;
    // Pull the pR*alpha(pR)-isotropic basis back to the number ring.
    XX, ZZ, UU := __pullUp(nProc, R, dim, proj);
    BB := Rows(Id(MatrixRing(R, dim)));

    // Convert the pulled-back basis to an appropriate p-maximal basis.
    pMaximalBasis :=
	ChangeRing(L`pMaximal[pR][2], BaseRing(Q));

    // for profiling reasons we need here a function
    function __changeBasis(XX,ZZ,UU, Q, pMaximalBasis)
      XX := [ ChangeRing(x, BaseRing(Q)) * pMaximalBasis : x in XX ];
      ZZ := [ ChangeRing(z, BaseRing(Q)) * pMaximalBasis : z in ZZ ];
      UU := [ ChangeRing(u, BaseRing(Q)) * pMaximalBasis : u in UU ];
      return XX, ZZ, UU;
    end function;
    XX, ZZ, UU := __changeBasis(XX,ZZ,UU, Q, pMaximalBasis);

    // Construct a basis on which to perform HNF.
    bb := Matrix(Rows(Matrix(XX cat ZZ cat UU)) cat Basis(Module(L)));
    
    p := Norm(pR);
    denom := L`pMaximal[pR][3]*BasisDenominator(Module(L));
    diag := nProc`scale;
    diag[2,2] := p;
    
    function __scale(XX, ZZ, UU, BB, denom)
        ret := denom*diag*Matrix(XX cat ZZ cat UU cat BB);
        return ChangeRing(ret, Integers());
    end function;
    
    BB := Basis(ZLattice(L));

    xzub := __scale(XX, ZZ, UU, BB, denom);

    H := HermiteForm(xzub);

    H := RowSubmatrix(H, 1, dim);

    function __rescale(H, denom, dim)
	return (1/denom) * ChangeRing(H, Rationals());
    end function;

    nLatBasis := __rescale(H, denom*p, dim);
    if (UseLLL and not BeCareful) then
	zlat := Lattice(nLatBasis, 2*InnerForm(Q));
	lll_ZZ := LLL(zlat : Proof := false);
	nLat := LatticeWithBasis(Q,
				 ChangeRing(BasisMatrix(lll_ZZ), Rationals()));
    end if;
    
    nLat := LatticeWithBasis(Q, ChangeRing(nLatBasis, BaseRing(Q)));
   
    return nLat;
end function;


function BuildHalfNeighborReverse(nProc : BeCareful := false, UseLLL := false, Perestroika := false, Similarity := 1)

    assert nProc`isoSubspace ne [];
    
    // The affine data.
    Vpp := nProc`L`Vpp[nProc`pR];

    // Shortcut for the projection map modulo pR^2.
    proj := Vpp`proj_pR2;

    // The dimension of the isotropic subspaces.
    k := nProc`k;

    // The lattice.
    L := nProc`L;

    // The prime
    pR := nProc`pR;

    // The base ring.
    R := BaseRing(L);

    // The reflexive space.
    Q := ReflexiveSpace(L);

    // The dimension.
    dim := Dimension(Q);

    // Degree of the field extension over the rationals.
    deg := Degree(BaseRing(Q));

    // for profiling reasons we need here a function
    function __pullUp(nProc, R, dim, proj)
      if Type(R) eq RngInt then
        Univ := RSpace(R, dim);
        XX := [Univ | x : x in nProc`X_skew];
        ZZ := [Univ | z : z in nProc`Z];
        UU := [Univ | u : u in nProc`U];
      else
        XX := [ Vector([ e @@ proj : e in Eltseq(x) ]) : x in nProc`X_skew ];
        ZZ := [ Vector([ e @@ proj : e in Eltseq(z) ]) : z in nProc`Z ];
        UU := [ Vector([ e @@ proj : e in Eltseq(u) ]) : u in nProc`U ];
      end if;
      return XX, ZZ, UU;
    end function;
    // Pull the pR*alpha(pR)-isotropic basis back to the number ring.
    XX, ZZ, UU := __pullUp(nProc, R, dim, proj);
    BB := Rows(Id(MatrixRing(R, dim)));

    // Convert the pulled-back basis to an appropriate p-maximal basis.
    pMaximalBasis :=
	ChangeRing(L`pMaximal[pR][2], BaseRing(Q));

    // for profiling reasons we need here a function
    function __changeBasis(XX,ZZ,UU, Q, pMaximalBasis)
      XX := [ ChangeRing(x, BaseRing(Q)) * pMaximalBasis : x in XX ];
      ZZ := [ ChangeRing(z, BaseRing(Q)) * pMaximalBasis : z in ZZ ];
      UU := [ ChangeRing(u, BaseRing(Q)) * pMaximalBasis : u in UU ];
      return XX, ZZ, UU;
    end function;
    XX, ZZ, UU := __changeBasis(XX,ZZ,UU, Q, pMaximalBasis);

    // Construct a basis on which to perform HNF.
    bb := Matrix(Rows(Matrix(XX cat ZZ cat UU)) cat Basis(Module(L)));
    
    p := Norm(pR);
    denom := L`pMaximal[pR][3]*BasisDenominator(Module(L));
    diag := nProc`scale;
    diag[1,1] := p^2;
    diag[2,2] := p;
    
    function __scale(XX, ZZ, UU, BB, denom)
        ret := denom*diag*Matrix(XX cat ZZ cat UU cat BB);
        return ChangeRing(ret, Integers());
    end function;
    
    BB := Basis(ZLattice(L));

    xzub := __scale(XX, ZZ, UU, BB, denom);

    H := HermiteForm(xzub);

    H := RowSubmatrix(H, 1, dim);

    function __rescale(H, denom, dim)
	return (1/denom) * ChangeRing(H, Rationals());
    end function;

    nLatBasis := __rescale(H, denom*p, dim);
    if (UseLLL and not BeCareful) then
	zlat := Lattice(nLatBasis, 2*InnerForm(Q));
	lll_ZZ := LLL(zlat : Proof := false);
	nLat := LatticeWithBasis(Q,
				 ChangeRing(BasisMatrix(lll_ZZ), Rationals()));
    end if;
    
    nLat := LatticeWithBasis(Q, ChangeRing(nLatBasis, BaseRing(Q)));
    
    return nLat;
end function;

function IsSimilar(M_old, M_new, p)
    Q_old := InnerForm(M_old);
    Q_new := InnerForm(M_new);
    // This does not work very well. Here is another option
    /*
    D_old, T_old, _ := Diagonalization(Q_old);
    D_new, T_new, _ := Diagonalization(1/p * Q_new);
    assert D_old eq D_new;
    h := T_old^(-1) * T_new;
   */
    reps_old := Representatives(Genus(M_old));
    L := Module(M_new);
    nProc := NeighborProcess(L, p, 1);
    if IsEmpty(nProc`isoSubspace) then return false, _; end if;
    nLat := BuildHalfNeighborReverse(nProc);
    isom_scale := BasisMatrix(Module(nLat));
    nLat := ScaledLattice(nLat, 1/p);
    is_iso := false;
    for L_old in reps_old do
	is_iso, g := IsIsometric(nLat, L_old);
	if (is_iso) then break; end if;
    end for;
    if not is_iso then return false, _; end if;
    b := ChangeRing(isom_scale, Rationals());
    h := g*b;
    assert h * (1/p * Q_new) * Transpose(h) eq Q_old;
    h := h^(-1);
    return true, h;
end function;

// We start with primes and with naive implementation, testing all for isometries
// We also start with trivial weight and only with the AL+ map
function DegeneracyMatrix(M_old, M_new, p, k : ThetaPrec := 25)
    ModFrmAlgInit(M_old);
    ModFrmAlgInit(M_new);
    mat := [ [ [* M_new`W!0 : hh in M_new`H *] : vec_idx in [1..Dimension(h)]]
		 : h in M_old`H];
    reps_old := Representatives(Genus(M_old));
    reps_new := Representatives(Genus(M_new));
    invs := HeckeInitializeInvs(M_old, ThetaPrec);
    // Fixing a similarity
    is_sim, h := IsSimilar(M_old, M_new, p);
    if is_sim then
	for col->L in reps_new do
	    nProc := NeighborProcess(L, p, k);
	    while not (IsEmpty(nProc`isoSubspace)) do
		processNeighborWeight(~nProc, ~reps_old, ~invs, ~mat, col, ~M_old`H, M_new`H, BuildHalfNeighborReverse :
				      Similarity := h);
		NextNeighbor(~nProc);
	    end while;
	end for;
    end if;
    ret := finalizeHecke(M_old, M_new, mat, [1..#M_new`H]);
    return ret;
end function;

function DegeneracyMatrixReverse(M_new, M_old, p, k : ThetaPrec := 25)
    ModFrmAlgInit(M_old);
    ModFrmAlgInit(M_new);
    mat := [ [ [* M_old`W!0 : hh in M_old`H *] : vec_idx in [1..Dimension(h)]]
		 : h in M_new`H];
    reps_old := Representatives(Genus(M_old));
    reps_new := Representatives(Genus(M_new));
    invs := HeckeInitializeInvs(M_new, ThetaPrec);
    // Fixing a similarity
    is_sim, h := IsSimilar(M_old, M_new, p);
    for col->L in reps_old do
	nProc := NeighborProcess(L, p, k);
	while not (IsEmpty(nProc`isoSubspace)) do
	    processNeighborWeight(~nProc, ~reps_new, ~invs, ~mat, col, ~M_new`H, M_old`H, BuildHalfNeighbor :
				  Similarity := h^(-1));
	    NextNeighbor(~nProc);
	end while;
    end for;
    ret := finalizeHecke(M_new, M_old, mat, [1..#M_old`H]);
    return ret;
end function;

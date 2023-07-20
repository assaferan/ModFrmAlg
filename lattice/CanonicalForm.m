function Min(A)
    minA := Set(ShortestVectors(LatticeWithGram(A)));
    return minA join {-v : v in minA};
end function;

function satspan(V)
    return Saturation(Matrix([v : v in V]));
end function;

function Lmin(A)
    vs := Min(A);
    L := Universe(vs);
    // V := AmbientSpace(L);
    // return sub<V|vs>;
    return sub<L | vs>;
end function;

function IsWellRounded(A)
    assert Nrows(A) eq Ncols(A);
    return Dimension(Lmin(A)) eq Nrows(A);
end function;

function CVP(A,v)
    return Set(ClosestVectors(LatticeWithGram(A),Vector(v)));
end function;

function Vwrcvp(A)
    n := Nrows(A);
    QQ := Rationals();
    VwrcvpA := Min(A);
    Latmin := Lmin(A);
    v := Basis(Latmin);
    Bt := Matrix(v);
    Bt := ChangeRing(Bt, QQ);
    B := Transpose(Bt);
    R, pi := LatticeWithBasis(IdentityMatrix(BaseRing(A),n),A)/Latmin;
    VwrcvpA join:= &join[{Vector(c@@pi) - ChangeRing(Vector(v),QQ)*Bt 
			  : v in CVP(Bt*A*B, ChangeRing(c@@pi,QQ)*Bt^(-1))} 
			 : c in R | c ne R!0];
    return VwrcvpA;
end function;

function Vcvp(A)
    assert Nrows(A) eq Ncols(A);
    n := Nrows(A);
    QQ := Rationals();
    AQ := ChangeRing(A, QQ);
    B1t := ChangeRing(satspan(Min(A)),QQ);
    L1 := LatticeWithBasis(B1t, AQ); 
    r := Rank(L1);
    v := Basis(L1);
    B1 := Transpose(B1t);
    A1 := B1t*AQ*B1;
    assert IsWellRounded(A1);
    B1Q := ChangeRing(B1, QQ);
    // projection onto L1
    P := B1Q*(Transpose(B1Q)*AQ*B1Q)^(-1)*Transpose(B1Q)*AQ;
    // projection onto orthogonal complement
    proj := ScalarMatrix(n,1)-P;
    L2 := LatticeWithBasis(BasisMatrix(RowSpace(Transpose(proj))),AQ);
    w := Basis(L2);
    B2t := Matrix(w);
    B2t := ChangeRing(B2t, QQ);
    B2 := Transpose(B2t);
    A2 := B2t * AQ * B2;
    if (r eq n) then
	VcvpA2 := {};
    else
	VcvpA2 := Vcvp(A2);
    end if;
    B2VcvpA2 := {Vector(v)*B2t : v in VcvpA2};
    VcvpA1 := Vwrcvp(A1);
    VcvpA := {ChangeRing(Vector(v),QQ)*B1t : v in VcvpA1};
    VcvpA join:= &join[CVP(A,v) : v in B2VcvpA2];
    return VcvpA;
end function;


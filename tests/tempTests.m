SetDebugOnError(true);
SetHelpUseExternalBrowser(false);
AttachSpec("ModFrmAlg.spec");
SetVerbose("AlgebraicModularForms", 1);

if assigned AlgebraicModularFormsExamples then
    delete AlgebraicModularFormsExamples;
end if;

if assigned testExample then
    delete testExample;
end if;

if assigned testLSeries then
    delete testLSeries;
end if;

import "tests/examples.m" : AlgebraicModularFormsExamples;
import "tests/tests.m" : testExample, testLSeries;

function inspect(M : prec := 20)
    Dimension(M);
    if IsZero(Dimension(M)) then return [* *]; end if;
    D := Decomposition(M,100);
    eigenforms := HeckeEigenforms(M);
    evs := [* HeckeEigensystem(f,1 : Precision := prec) :  f in eigenforms *];
    lpolys := [* LPolynomials(f : Precision := prec) : f in eigenforms *];
    lps :=  [* [Factorization(lp[p]) : p in PrimesUpTo(prec)] : lp in lpolys *];
    return evs, lps;
end function;

QQ := Rationals();
std_reps := AssociativeArray();
forms := AssociativeArray();
std_reps[3] := StandardRepresentation(GL(3,QQ));
std_reps[5] := StandardRepresentation(GL(5,QQ));
forms[3] := [2*IdentityMatrix(QQ,3),
	  SymmetricMatrix(QQ, [2,0,2,1,0,6]),
	  SymmetricMatrix(QQ, [4,-1,4,-1,0,12]) // Alok Shukla's example
	  ];
forms[5] := [
	  2*IdentityMatrix(QQ,5),
	  SymmetricMatrix(QQ, [2,0,2,0,0,2,0,0,0,2,1,0,0,0,6]),
	  SymmetricMatrix(QQ, [2,0,2,0,0,2,0,1,0,2,1,0,0,0,6])
];
// understand which of these examples is suitable to become a test

//for dim in [3,5] do
for dim in [3] do
    for A in forms[dim] do
	A;
	G := SpecialOrthogonalGroup(A);
	// maybe should make k depend on the dimension
	for k in [0..6] do
	    k;
	    W := SymmetricRepresentation(std_reps[dim],k);
	    //	M := OrthogonalModularForms(A, W);
	    M := AlgebraicModularForms(G, W);
            _ := inspect(M);
	end for;
    end for;
end for;


print "Testing examples from John and Matt's paper...";
print "Testing low memory version...";
M, timing := AlgebraicModularFormsTests(: NumPrimes := 3, LowMemory);
print "memory used: ", GetMemoryUsage();
print "Testing standard version...";
M2, timing2 := AlgebraicModularFormsTests(: NumPrimes := 3);
print "memory used: ", GetMemoryUsage();
ratios := [[[timing[i][j][k]/timing2[i][j][k] : k in [1..#timing[i][j]]
		     | timing2[i][j][k] ne 0] : j in [1..#timing[i]]]
	      : i in [1..#timing]];
// print "ratios are: ", ratios;
// print "Testing canonical form version...";
// M3, timing3 := AlgebraicModularFormsTests(: NumPrimes := 3, ThetaPrec := -1);

print "testing L series computation for O(5)...";
print "testing level 61, weights (3,0), (3,2) and (4,0)...";
// This is quite long, so we reduce the precision
// testLSeries(61, [[3,0],[3,2],[4,0]], 5);
 testLSeries(61, [[3,0],[3,2],[4,0]], 2);
print "testing level 21, weight (3,2)....";
// This is quite long, so we reduce the precision
// testLSeries(21, [[3,2]], 5);
testLSeries(21, [[3,2]], 2);
// This does not seem to work at the moment for some reason!
// print "testing level 26, weight (3,2)....";
// testLSeries(26, [[3,2]], 5);
A := forms[5][2];
G := SpecialOrthogonalGroup(A);
W := SymmetricRepresentation(std_reps[5], 2);
M := AlgebraicModularForms(G,W);
evs, lpolys := inspect(M : prec := 10);

// testing an inert prime
example := AlgebraicModularFormsExamples[3];
M, timing := testExample(example : NumPrimes := 3);
T2 := HeckeOperator(M,2);
T3 := HeckeOperator(M,3);
assert T2*T3 eq T3*T2;

// Checking the 305 
a := Split("1   1   1   1  26   0   0   0   1   0   0   0   0   1   1", " ");
a := [eval(x) : x in a];
tmp := [a[1],a[6],a[2]] cat a[7..8] cat [a[3]] cat a[9..11] cat [a[4]] cat 
       a[12..15] cat [a[5]];
A := SymmetricMatrix(tmp);
A := A + DiagonalMatrix(Diagonal(A));
Determinant(A);
d := 1;
G := OrthogonalGroup(A);
W := SpinorNormRepresentation(G, d);
M := AlgebraicModularForms(G, W);
D := Decomposition(M);
eigenforms := HeckeEigenforms(M);

// This function shows the passage from GU2(B) to GSpin(5)
function otherStuff()
    QQ := Rationals();
    B<i_B,j_B,k_B> := QuaternionAlgebra(QQ, -1, -1);
    B_conj := hom<B -> B | x :-> Conjugate(x)>;
    C<i_C,j_C,k_C> := QuaternionAlgebra(QQ, 1, 11);
    // First construction - direct, works with any B,C
    BC, iota_B, iota_C := DirectSum(B,C);
    basis := [iota_B(i_B), iota_B(j_B), iota_B(k_B), iota_C(i_C), iota_C(j_C)];
    function trd(x)
	return 1/2*(x + Conjugate(x));
    end function;
    function pairing(x,y)
	x1 := x @@ iota_B;
	x2 := x @@ iota_C;
	y1 := y @@ iota_B;
	y2 := y @@ iota_C;
	return -trd(B!(x1 * y1)) + trd(C!(x2*y2));
    end function;
    Matrix([[pairing(x,y) : y in basis] : x in basis]);
    M2B := MatrixRing(B,2);
    // These are the images of i_C, j_C under the isomorphism
    // C = (1,11 / QQ) = M2(QQ)
    im_i_C := M2B![1,0,0,-1];
    im_j_C := M2B![0,11,1,0];
    // This is the basis to the 5-dimensional space over which we will
    // have the quadratic form
    basis := [M2B | i_B, j_B, k_B, im_i_C, im_j_C];
    // This is the transofrmation to get to hermitian matrices
    w := Matrix([[0,1],[-1,0]]);
    w_basis := [b*w : b in basis];
    // This shows that the bilinear form comes from the determinant
    Matrix([[1/2*(Determinant(x)+Determinant(y)-Determinant(x+y)) :
	     y in basis] : x in basis]);
    // Here we want to get the general transformation from
    // the action of SL_2(B) on M_2^Her(B) to SO(5)
    
    R := PolynomialRing(B, 16);
    names := [c cat IntegerToString(num) : num in [1,2,3,4],
					   c in ["a", "b", "c","d"]];
    AssignNames(~R, names);
    a_vars := [R.i : i in [1..4]];
    b_vars := [R.i : i in [5..8]];
    c_vars := [R.i : i in [9..12]];
    d_vars := [R.i : i in [13..16]];
    R_star := hom<R -> R | B_conj, GeneratorsSequence(R) >;
    basis_B := [R | B!1, i_B, j_B, k_B];
    a := (Vector(a_vars), Vector(basis_B));
    b := (Vector(b_vars), Vector(basis_B));
    c := (Vector(c_vars), Vector(basis_B));
    d := (Vector(d_vars), Vector(basis_B));
    a_ := R_star(a);
    b_ := R_star(b);
    c_ := R_star(c);
    d_ := R_star(d);
    g := Matrix([[a,b],[c,d]]);
    g_star := Matrix([[a_, c_], [b_, d_]]);
    M2 := Parent(g);
    tmp := (g * M2![0,i_B,-i_B,0] * g_star)[1,2];
    coeffs, mons := CoefficientsAndMonomials(tmp);
    basis_B := [B!1, i_B, j_B, k_B];
    v := [&+[(coeffs[i]/b)*mons[i] : i in [1..#coeffs] |
	     IsCoercible(Rationals(), coeffs[i] / b)] : b in basis_B];
end function;

import "../neighbors/isotropic.m" : __initializePivot, __pivots;
import "../neighbors/neighbor-CN1.m" : BuildNeighborProc, SkipToNeighbor, GetNextNeighbor, LiftSubspace;
import "../neighbors/hecke-CN1.m" : processNeighborWeight, finalizeHecke;
import "../utils/helper.m" : printEstimate;

procedure GetNextNeighborNoSkew(~nProc : BeCareful := false)
	// The affine data.
	Vpp := nProc`L`Vpp[nProc`pR];

	// The isotropic dimension we're interested in.
	k := nProc`k;

	if GetVerbose("AlgebraicModularForms") ge 2 then
	    printf "Currently space = %o, running NextIsotropicSubspace...\n",
		   nProc`isoSubspace;
	end if;

	// get the next isotropic subspace modulo pR.
	nProc`isoSubspace := NextIsotropicSubspace(Vpp`V, k);

	if GetVerbose("AlgebraicModularForms") ge 2 then
	    printf "After NextIsotropicSubspace = %o, running lifting...\n",
		   nProc`isoSubspace;
	end if;
	
	// Lift the subspace if we haven't reached the end of the list.
	    
	nProc`X, nProc`Z, nProc`U :=
	    LiftSubspace(nProc : BeCareful := BeCareful);

	// Checking if we could lift modulo pR * alpha(pR)
	while IsEmpty(nProc`X) and (not IsEmpty(nProc`isoSubspace)) do
	    nProc`isoSubspace := NextIsotropicSubspace(Vpp`V, k);
	    nProc`X, nProc`Z, nProc`U :=
		LiftSubspace(nProc : BeCareful := BeCareful);
	end while;
	
	nProc`X_skew := [ x : x in nProc`X ];
	
end procedure;

function init_pivots(M, pR, k, hecke_idx)
    reps := Representatives(Genus(M));
    L := reps[hecke_idx];
    nProc := BuildNeighborProc(L, pR, k);
    V := nProc`L`Vpp[nProc`pR]`V;
    if not IsDefined(V`ParamArray, k) then
	data := New(IsoParam);
	data`Pivots := __pivots(Dimension(V) - V`RadDim, V`AnisoDim, k);
	data`PivotPtr := 0;
	data`Params := [];
	V`ParamArray[k] := data;
    end if;
    data := V`ParamArray[k];
    return nProc, #data`Pivots;
end function;

function log_num_pivot_nbrs(nProc, pivot_idx)
    V := nProc`L`Vpp[nProc`pR]`V;
    k := nProc`k;
    // Retrieve the parameters for the requested dimension.
    data := V`ParamArray[k];
    data`PivotPtr := pivot_idx;
    __initializePivot(V, k);
    return #data`FreeVars;
end function;

procedure update_params(~params, V, nFreeVars)
    // The current position in the parameterization.
    pos := 0;

    // Terminate loop once we found the next new subspace, or we
    //  hit the end of the list.
    repeat
	// Increment position.
	pos +:= 1;
	
	if V`Symbolic then
	    // Increment value.
	    params[pos] +:= 1;
	    
	    // Check to see if we've rolled over.
	    if (params[pos] mod #V`S) eq 0 then
		// Reset value if so.
		params[pos] := 0;
	    end if;
	else
	    // Manually move to the next element.
	    if IsPrime(#BaseRing(V)) then
		params[pos] +:= 1;
	    elif params[pos] eq 0 then
		params[pos] := V`PrimitiveElement;
	    elif params[pos] eq 1 then
		params[pos] := 0;
	    else
		params[pos] *:= V`PrimitiveElement;
	    end if;
	end if;
    until pos eq nFreeVars or params[pos] ne 0;
end procedure;

// not including upTo
function hecke_pivot(M, nProc, pivot_idx, ThetaPrec, hecke_idx, start_idx, upTo :
		     BeCareful := false, Estimate := true)

    invs := HeckeInitializeInvs(M, ThetaPrec);
    hecke := [ [ [* M`W!0 : hh in M`H *] : vec_idx in [1..Dimension(h)]]
	       : h in M`H];
    V := nProc`L`Vpp[nProc`pR]`V;
    k := nProc`k;
    // Retrieve the parameters for the requested dimension.
    data := V`ParamArray[k];
    data`PivotPtr := pivot_idx;
    p := #BaseRing(V);
    log_num_nbrs := log_num_pivot_nbrs(nProc, pivot_idx);
    num := start_idx;
    // right now, we only support trivial skew
    for i in [1..log_num_nbrs] do
	data`Params[i] := num mod p;
	num div:= p;
    end for;
    evalList := [* 0 : i in [1..Dimension(V)*k] *];
    for i in [1..#data`Params] do
	evalList[data`FreeVars[i]] := V`S[data`Params[i]+1];
    end for;
    space := Rows(Evaluate(data`IsotropicParam, [ x : x in evalList]));
    skew := nProc`skew;
    // update params, so GetNextNeighbor would work. 
    if #data`FreeVars ne 0 then
	update_params(~data`Params, V, #data`FreeVars);
    end if;

    // If we've hit the end of the list, indicate we need to move on to the
    //  next pivot.
    if &and[ x eq 0 : x in data`Params ] then data`Params := []; end if;
    SkipToNeighbor(~nProc, space, skew);
    fullCount := #BaseRing(V)^(nProc`skewDim) * (upTo-start_idx);
    count := 0;
    elapsed := 0;
    start := Realtime();
 
    for i in [1..fullCount] do
	processNeighborWeight(~nProc, ~reps, ~invs, ~hecke, hecke_idx, ~M`H :
			      ThetaPrec := ThetaPrec);
	// Update nProc in preparation for the next neighbor
	//  lattice.
	GetNextNeighbor(~nProc
			: BeCareful := BeCareful);
	if Estimate then
	    printEstimate(start, ~count, ~elapsed,
			  fullCount, Sprintf("T_%o^%o", Norm(nProc`pR), k));
	end if;
    end for;
 
    return finalizeHecke(M, hecke, [hecke_idx]);
end function;

function make_intervals(batch_size, num)
    num_batches := (num-1) div batch_size + 1;
    batches := [[batch_size*(j-1), batch_size*j] : j in [1..num_batches-1]];
    Append(~batches, [batch_size*(num_batches-1), num]);
    return batches;
end function;

// e.g.
// nProc, nPivots := init_pivots(M, pR, k, hecke_idx);
// nums := [p^log_num_pivot_nbrs(nProc, pivot_idx) : pivot_idx in [1..nPivots]];
// intervals := [make_intervals(B, num) : num in nums];
// heckes := [[hecke_pivot(M, nProc, pivot_idx, ThetaPrec, hecke_idx, I[1], I[2]) :
//             I in intervals[pivot_idx]] : pivot_idx in [1..npivots]];

procedure write_single_batch(M, pR, k, pivot_idx, start, upTo, hecke_idx, ThetaPrec)
    omf_name := "rank_8_d_53";
    batch_fname := omf_name cat Sprintf("_%o_%o_%o_%o_%o.m", Norm(pR), k, pivot_idx, start, upTo);
    output_fname := omf_name cat Sprintf("_%o_%o_%o_%o_%o.out", Norm(pR), k, pivot_idx, start, upTo);
    output := ["AttachSpec(\"ModFrmAlg.spec\")"];
    Append(~output, Sprintf("M := AlgebraicModularForms(\"%o\");", omf_name cat ".omf"));
    Append(~output, Sprintf("pR := %m;",pR));
    Append(~output, Sprintf("nProc := init_pivots(M, pR, %o, %o);", k, hecke_idx));
    Append(~output, Sprintf("hecke := hecke_pivot(M, nProc, %o, %o, %o, %o, %o);",
			    pivot_idx, ThetaPrec, hecke_idx, start, upTo));
    Append(~output, Sprintf("Write(\"%o\", Eltseq(hecke));", output_fname));
    Append(~output, "exit;");
end procedure;

procedure write_batch_files(M, p, k, pivot : ThetaPrec := 5, B := 10^5)
    pR := ideal<Integers() | p>;
    nProc, nPivots := init_pivots(M, pR, k, pivot);
    nums := [p^log_num_pivot_nbrs(nProc, pivot_idx) : pivot_idx in [1..nPivots]];
    intervals := [make_intervals(B, num) : num in nums];
    for pivot_idx in [1..nPivots] do
	for I in intervals[pivot_idx] do
	    write_single_batch(M, pR, k, pivot_idx, I[1], I[2], pivot, ThetaPrec);
	end for;
    end for;
end procedure;


// currently not working
/*
function hecke_pivot_skew(M, nProc, skew_idx, pivot_idx, ThetaPrec, hecke_idx :
			  BeCareful := false, Estimate := true)

    invs := HeckeInitializeInvs(M, ThetaPrec);
    hecke := [ [ [* M`W!0 : hh in M`H *] : vec_idx in [1..Dimension(h)]]
	       : h in M`H];
    V := nProc`L`Vpp[nProc`pR]`V;
    k := nProc`k;
    // Retrieve the parameters for the requested dimension.
    data := V`ParamArray[k];
    data`PivotPtr := pivot_idx;
    __initializePivot(V, k);
    evalList := [* 0 : i in [1..Dimension(V)*k] *];
    for i in [1..#data`Params] do
	evalList[data`FreeVars[i]] := V`S[data`Params[i]+1];
    end for;
    space := Rows(Evaluate(data`IsotropicParam, [ x : x in evalList]));
    skew := Matrix(BaseRing(V), [[skew_idx,0], [0,-skew_idx]]);
    // update params, so GetNextNeighbor would work. 
    if #data`FreeVars ne 0 then
	// The current position in the parameterization.
	pos := 0;

	// Terminate loop once we found the next new subspace, or we
	//  hit the end of the list.
	repeat
	    // Increment position.
	    pos +:= 1;
	    
	    if V`Symbolic then
		// Increment value.
		data`Params[pos] +:= 1;
		
		// Check to see if we've rolled over.
		if (data`Params[pos] mod #V`S) eq 0 then
		    // Reset value if so.
		    data`Params[pos] := 0;
		end if;
	    else
		// Manually move to the next element.
		if IsPrime(#BaseRing(V)) then
		    data`Params[pos] +:= 1;
		elif data`Params[pos] eq 0 then
		    data`Params[pos] := V`PrimitiveElement;
		elif data`Params[pos] eq 1 then
		    data`Params[pos] := 0;
		else
		    data`Params[pos] *:= V`PrimitiveElement;
		end if;
	    end if;
	until pos eq #data`FreeVars or data`Params[pos] ne 0;
    end if;

    // If we've hit the end of the list, indicate we need to move on to the
    //  next pivot.
    if &and[ x eq 0 : x in data`Params ] then data`Params := []; end if;
    SkipToNeighbor(~nProc, space, skew);
    fullCount := #BaseRing(V)^(#data`FreeVars);
    count := 0;
    elapsed := 0;
    start := Realtime();
    //while nProc`isoSubspace ne [] do
    for i in [1..fullCount] do
	processNeighborWeight(~nProc, ~reps, ~invs, ~hecke, hecke_idx, ~M`H :
			      ThetaPrec := ThetaPrec);
	// Update nProc in preparation for the next neighbor
	//  lattice.
	GetNextNeighborNoSkew(~nProc
			      : BeCareful := BeCareful);
	if Estimate then
	    printEstimate(start, ~count, ~elapsed,
			  fullCount, Sprintf("T_%o^%o", Norm(nProc`pR), k));
	end if;
    end for;
    //end while;
    // return fullCount;
    //return count;
    return finalizeHecke(M, hecke, [hecke_idx]);
end function;
*/

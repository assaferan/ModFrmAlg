freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
                      
                                                                            
   FILE: neighbor-CN1.m (Implementation of  computing p-neighbor lattices)

   05/29/20: Fixed bugs when handling inert primes, and when updating the skew 
             matrix along the anti-diagonal for the unitary case.

   05/29/20: Fixed a bug in lifting vectors from the radical.

   05/27/20: Updated LiftSubspace to handle the case of isotropic vectors
             mod pR that do not lift modulo pR * alpha(pR). 

   05/26/20: Modified BuildNeighborProc to determine splitting type of the
             prime, and accordingly modify the gram matrix in characteristic 2, 
             and set the skew variables.
             Also modified it to return with the first liftable isotropic 
	     subspace.
             Modified UpdateSkewMatrix to handle the unitary case as well, for 
             inert and ramified primes.
             Modified UpdateSkewSpace to verify that the skew space is
             isotropic.
             Updated GetNextNeighbor to use the new UpdateSkewMatrix, and 
             return only the next liftable isotropic vector.

   05/11/20: Updated SkipToNeighbor to be able to specify the skew-matrix for 
             p mod p^2.
             Took out code chunks from GetNextNeighbor to form UpdateSkewMatrix
             and UpdateSkewSpace, for greater modularity of the code.

   04/27/20: Changed the default value of the BeCareful parameter to false.

   04/23/20: Fixed bug in the unitary split case for k > 1, where skew vector 
             changed when constructing the isotropy subspace.
   
   04/22/20: Fixed bug in BuildNeighbor, of computing pairings only for k = 1 
             in the unitary case.

   04/13/20: Added the UseLLL parameter - performing LLL; on the lattice 
             after constructing it.

   03/11/20: Added the function SkipToNeighbor, from neighbor-QQ in the orthogonal
             case, in order to use it in the orbit method.

   03/10/20: Discarded irrelevant imports.
             Moved here the type declaration.
	     Modified to use always the reflexive space implementation.
             Added the involution on the ring of integers.
             Modified BuildNeighbor to work in the unitary case for 
             split primes, by using the code from unitary/hgenus.m
             Modified LiftSubspace to work also in the unitary case.
             Fixed bug in BuildNeighborProc. 

   03/05/20: Modified BuildNeighborProc to support the unitary case.

   02/28/20: started editing this file to add Unitary forms
 
 ***************************************************************************/

// imports

import "../lattice/lattice.m" : pMaximalGram;

///////////////////////////////////////////////////////////////////
//                                                               //
//    NeighborProc: The p-neighbor walking procedure object.     //
//                                                               //
///////////////////////////////////////////////////////////////////

declare type NeighborProc;
declare attributes NeighborProc:
	// The lattice.
	L,

 	// The prime ideal.
	pR,

	// The norm of this prime.
	pRnorm,

        // The involution of the underlying reflexive space
        inv_R,
  
	// The quadratic space over the residue class field.
	VFF,

	// The current isotropic subspace.
	isoSubspace,

	// The dimension of the isotropic subspaces.
	k,

        // for the case of the rationals as base field, we save a scaling matrix
        scale,
  
	// Skew vector. This is used to "twist" the isotropic lifts when
	//  computing neighbor lattices when k gt 1.
	skew,

	// Skew dimension.
	skewDim,

	// The current (unaltered) p^2-isotropic lift we're looking at.
	X,

	// The current p^2-isotropic lift we're looking at.
	X_skew,

	// The current hyperbolic complement of X and X_skew.
	Z,

	// The space orthogonal to X+Z modulo p^2.
	U;

// auxiliary function to lift a subspace from mod p

function LiftSubspace(nProc : BeCareful := false, Override := false)
    // If we're trying to lift an empty subspace, return trivial entries.
    if nProc`isoSubspace eq [] then return [], [], []; end if;

    alpha := Involution(ReflexiveSpace(nProc`L));
	
    // The local data.
    Vpp := nProc`L`Vpp[nProc`pR];
	
    pi := Vpp`pElt;
    pibar := nProc`inv_R(Vpp`pElt);
	
    // The standardized basis.
    basis := Vpp`V`Basis;
	
    // The requested isotropic dimension.
    k := nProc`k;

    // The pR-isotropic subspace.
    sp := nProc`isoSubspace;

    // The dimension.
    dim := Dimension(ReflexiveSpace(nProc`L));

    // The hyperbolic dimension.
    hDim := 2 * Vpp`V`WittIndex;
	
    // The affine vector space.
    V := Vpp`V;

    // Shortcuts to the projection maps.
    map := Vpp`proj_pR;
    proj := Vpp`proj_pR2;

    if not Override then
	// Parameterization data regarding the affine space.
	param := V`ParamArray[k];

	// Get the pivots for the bases of the isotropic subspaces.
	pivots := param`Pivots[param`PivotPtr];
    else
	pivots := [0^^k];
	for i in [1..k] do
	    pos := 0;
	    repeat pos +:= 1;
	    until sp[i][pos] ne 0;
	    pivots[i] := pos;
	end for;
    end if;

    // Set up the correct basis vectors.
    for i in [1..k], j in [pivots[i]+1..dim] do
	AddColumn(~basis, sp[i][j], j, pivots[i]);
    end for;

    alpha_pR := Vpp`inv_pR;

    // Extract our target isotropic subspace modulo pR.   
    X := [ MVM(basis, V.i, alpha_pR) : i in pivots ];

    if Vpp`splitting_type eq "split" then
	X := [ Vector([ proj(e @@ map) : e in Eltseq(x) ]) : x in X ];
	X := [pibar * x : x in X];
	return X,X,X;
    end if;
	
    // Extract the hyperbolic complement modulo pR.
    // paired := [ hDim+1-pivots[k+1-i] : i in [1..k] ];
    // if they have no pair (from the radical) will choose
    // arbitrary other vector to pair with
    num_non_paired := 0;
    paired := [];
    // recall that pivots is sorted
    ns_pivots := [pivots[i] : i in [1..k] | pivots[i] le hDim];
    sing_pivots := [pivots[i] : i in [1..k] | pivots[i] gt hDim];
    for pivot in ns_pivots do
	Append(~paired, hDim+1-pivot);
    end for;
    exclude := pivots cat paired;
    remain := [i : i in [1..dim] | not i in exclude];
    for pivot in sing_pivots do
	num_non_paired +:= 1;
	Append(~paired, remain[num_non_paired]);
    end for;
 
    Z := [ MVM(basis, V.i, alpha_pR) : i in Reverse(paired) ];

    // Extract the remaining basis vectors.
    exclude := pivots cat paired;
    U := [ MVM(basis, V.i, alpha_pR) : i in [1..dim] | not i in exclude ];
    B := Matrix(X cat Z cat U);

    // Convert to coordinates modulo pR^2.
    X := [ Vector([ proj(e @@ map) : e in Eltseq(x) ]) : x in X ];
    Z := [ Vector([ proj(e @@ map) : e in Eltseq(z) ]) : z in Z ];
    U := [ Vector([ proj(e @@ map) : e in Eltseq(u) ]) : u in U ];

    // In these cases, we are not going to bother with
    // making X and Z isotropic here
    if Vpp`splitting_type eq "ramified" then
	return X,Z,U;
    end if;
	
    // Build the coordinate matrix.
    B := Matrix(X cat Z cat U);

    alpha_pR2 := Vpp`inv_pR2;

    function __gram(B : quot := true)
	// In odd characteristic, things are exactly as we expect
	alpha_pR2 := Vpp`inv_pR2;
        if IsIdentity(alpha) then
          alpha_B := B;
        else
          alpha_B := Parent(B)![[alpha_pR2(B[i,j]) :
			       j in [1..Ncols(B)]]
			      : i in [1..Nrows(B)]];
        end if;

	if Vpp`ch ne 2 then
	    return B * Vpp`quotGram * Transpose(alpha_B);
	end if;

	// Promote the basis to the number ring.
	B := ChangeRing(B, nProc`L`R);

        alpha_R := nProc`inv_R;

        alpha_B := Parent(B)![[alpha_R(B[i,j]) :
			       j in [1..Ncols(B)]]
			      : i in [1..Nrows(B)]];

	// Compute the Gram matrix.
        gram := B * nProc`L`pMaximal[nProc`pR][1] *
		Transpose(alpha_B);

	// The dimension.
	dim := Nrows(B);
	    
	// Return the appropriate Gram matrix.
	if quot then
	    return Matrix(Vpp`quot, dim, dim, Eltseq(gram));
	else
	    return gram;
	end if;
    end function;
    
    for i in [1..k] do
	if pivots[i] gt hDim then
	    gram := __gram(Matrix(X[i]) : quot := false)[1,1];
	    if Vpp`ch eq 2 then
		if gram notin 2 * nProc`pR * alpha(nProc`pR) then
		// This can't lift to an isotropic subspace modulo pR*alpha(pR)
		    return [],[],[];
		end if;
	    else
		if not IsZero(gram) then
		    return [],[],[];
		end if;
	    end if;
	end if;
    end for;
    
    
    // Compute the Gram matrix of the subspace with respect to the spaces
    //  we will perform the following computations upon.
    gram := __gram(Matrix(X cat Z));

    // Lift Z so that it is in a hyperbolic pair with X modulo pR * alpha(pR).
    Z := [ Z[i] +
	   &+[ ((i eq j select 1 else 0) -
		alpha_pR2(gram[k+1-j,i+k])) * Z[j]
	       : j in [1..k] ] : i in [1..k] ];

    // Verify that X and Z form a hyperbolic pair.
    // Note - this will not work when lifting from the radical
    if BeCareful then
	// Compute the Gram matrix thusfar.
	B := Matrix(X cat Z cat U);
	temp := __gram(B);

	// Verify that we have ones and zeros in all the right places.
	assert &and[ temp[i,k+j] eq (i-k+j eq 1 select 1 else 0)
		     : i,j in [1..k] ];
    end if;
	
    // We will need to divide by 2, so we will need to consider the Gram
    //  matrix over the base ring instead of over the ring modulo pR^2.
    if Vpp`ch eq 2 then
	gram := __gram(Matrix(X cat Z) : quot := false);
	// !!! TODO : Check that it doesn't break anything !!!
	a := Involution(ReflexiveSpace(nProc`L));
	if Order(a) eq 2 then
	    factors := [];
	    FF := FixedField(a);
	    ZZ_F := Integers(FF);
	    if Vpp`splitting_type eq "inert" then
		pR_FF := ideal<ZZ_F|Generators(nProc`pR)>;
	    elif Vpp`splitting_type eq "ramified" then
		pR_FF := ideal<ZZ_F|
			      Generators(nProc`pR*a(nProc`pR))>;
	    end if;
	    FF_bar, proj_FF := ResidueClassField(pR_FF);
	    FF_x<x> := PolynomialRing(FF_bar);
	    
	    K := BaseField(a);
	    ZZ_K := Integers(K);
	    ZZ_K_basis := Basis(ZZ_K);
	    possible_ds := [ZZ_F!(FF!((x-a(x))^2)) : x in ZZ_K_basis];
	    assert exists(idx){idx : idx in [1..#possible_ds] |
			       possible_ds[idx] ne 0};
	    D := possible_ds[idx];
	    delta := ZZ_K_basis[idx] - a(ZZ_K_basis[idx]);
	    for i in [1..k] do
		f := proj_FF(gram[k+i,k+i]/pi)*x^2 - x +
		     proj_FF(gram[i,i]/pi);
		roots := Roots(f);
		t2 := FF_bar!0;
		while IsEmpty(roots) do
		    if (t2 eq 0) then
			t2 := FF_bar!1;
		    else
			t2 *:= FF_bar.1;
		    end if;
		    f2 := f - proj_FF(gram[k+i,k+i]/pi) *
			      proj_FF(D) * t2^2;  
		    roots := Roots(f2);
		end while;
		t1 := roots[1][1]@@proj_FF;
		Append(~factors, t1 + delta * (t2@@proj_FF));
	    end for;
	else
	    factors := [gram[i,i]/2 : i in [1..k]];
	end if;
    else
	factors := [gram[i,i]/2 : i in [1..k]];
    end if;

    // Lift X so that it is isotropic modulo pR^2.
    X := [ X[i] -
	   &+[(i+j-1 eq k select factors[i] else gram[i,k+1-j]) * Z[j]
	      : j in [k+1-i..k] ] : i in [1..k] ];
    
    // Verify that X is isotropic modulo pR*alpha(pR).
    if BeCareful then
	// The basis.
	B := Matrix(X);
	
	// The Gram matrix on this basis.
	temp := __gram(B);
	
	// Verify all is well.
	assert &and[ temp[i,j] eq 0 : i,j in [1..k] ];
	
    end if;

    // Lift Z so that it is isotropic modulo pR*alpha(pR).
    if Type(nProc`pR) ne RngInt or IsInvertible(Codomain(alpha_pR2)!2) then
      Z := [ Z[i] -
	   &+[ alpha_pR2(gram[k+i,2*k+1-j])/
	       (i+j-1 eq k select 2 else 1) * X[j]
	       : j in [k+1-i..k] ] : i in [1..k] ];
    else
      Z := [ Z[i] -
	      &+[ (alpha_pR2(gram[k+i,2*k+1-j]) div
		   (i+j-1 eq k select 2 else 1)) * X[j]
		    : j in [k+1-i..k] ] : i in [1..k] ];
    end if;

    // Verify that Z is isotropic modulo pR^2.
    if BeCareful then
	// The basis.
	B := Matrix(Z);
	
	// The Gram matrix on this basis.
	temp := __gram(B);
	
	// Verify all is well.
	assert &and[ temp[i,j] eq 0 : i,j in [1..k] ];

	// In characteristic 2, the above doesn't really check this
	if Vpp`ch eq 2 then
	    temp := __gram(B : quot := false);
	    assert &and[ temp[i,j] in nProc`pR *
				      alpha(nProc`pR) : i,j in [1..k] ]; 
	end if;
    end if;
    
    // The Gram matrix thusfar.
    gram := __gram(Matrix(X cat Z cat U));

    // renormalize the vectors in X so that the off-diagonal entries are 1
    // X := [ X[i] * gram[i, 2*k+1-i]^(-1) : i in [1..k] ];
    for i in [1..k] do
	if not IsZero(gram[i, 2*k+1-i]) then
	    X[i] := X[i] * gram[i, 2*k+1-i]^(-1);
	end if;
    end for;

    // The Gram matrix thusfar.
    gram := __gram(Matrix(X cat Z cat U));

    // Make U orthogonal to X+Z.
    for i in [1..k], j in [1..dim-2*k] do
	// Clear components corresponding to X.
	scalar := alpha_pR2(gram[2*k+1-i,2*k+j]);
	U[j] -:= scalar * X[i];

	// Clear components corresponding to Z.
        scalar := alpha_pR2(gram[k+1-i,2*k+j]);
	U[j] -:= scalar * Z[i];
    end for;

    // Verify that U is now orthogonal to X+Z.
    // Note - this also would not work when lifting from the radical
    if BeCareful then
	// The basis.
	B := Matrix(X cat Z cat U);

	// The Gram matrix.
	temp := __gram(B);

	// Verify correctness.
	assert &and[ temp[i,j] eq 0
		     : i in [1..2*k], j in [2*k+1..dim] ];
    end if;

    return X, Z, U;
end function;

// The initialization function

function BuildNeighborProc(L, pR, k : BeCareful := false)
	// Initialize the neighbor procedure.
	nProc := New(NeighborProc);

	// Assign the lattice, prime ideal, and isotropic dimension.
	nProc`L := L;
	nProc`pR := pR;
	nProc`pRnorm := Norm(pR);
	nProc`k := k;

	// The reflexive space.
	V := ReflexiveSpace(L);

        alpha := Involution(V);
        K := BaseField(V);
        R := Integers(K);

        nProc`inv_R := map< R -> R | x :-> R!(alpha(K!x))>;

	// The dimension.
	dim := Dimension(V);

	if not IsDefined(L`Vpp, pR) then
	    // Initialize the affine reflexive space.
	    qAff := New(RfxSpaceAff);

	    // The prime ideal.
	    qAff`pR := pR;

	    // A uniformizing element of pR.
            if Type(pR) eq RngInt then
              qAff`pElt := Norm(pR);
            else
	      qAff`pElt := SafeUniformizer(pR);
            end if;

	    // The residue class field.
	    qAff`F, qAff`proj_pR := ResidueClassField(pR);

	    // The characteristic.
	    qAff`ch := Characteristic(qAff`F);

	    // The quotient modulo pR * alpha(pR).
            qAff`quot, qAff`proj_pR2 := quo< BaseRing(L) | pR *
							   alpha(pR) >;

	    // Compute the Gram matrix of a p-maximal basis for L.
	    gram, basis := pMaximalGram(L, pR : BeCareful := BeCareful);

	    // This Gram matrix modulo pR.
	    mat := qAff`proj_pR(gram);

            mat := MatrixAlgebra(BaseRing(mat), Nrows(mat))!mat;
	    
	    // The Gram matrix modulo pR * alpha(pR).
	    qAff`quotGram := Matrix(qAff`quot, dim, dim,
				    [ qAff`proj_pR2(e) : e in Eltseq(gram) ]);
	    
	    // Determining the nature of the affine reflexive space.
            if (pR eq alpha(pR)) then
		alpha_res := map< qAff`F -> qAff`F |
				x :-> qAff`proj_pR(
					  nProc`inv_R(x@@qAff`proj_pR))>;
		
                alpha_aff := FieldAutomorphism(qAff`F, alpha_res);
		if IsIdentity(alpha) then
		    qAff`splitting_type := "none"; // orthogonal case
		else
		    qAff`splitting_type :=
		    IsIdentity(alpha_aff) select "ramified" else "inert";
		end if;
            else // split case
		qAff`splitting_type := "split";
	    end if;   

	    // Make some adjustments when we're in characteristic 2.
            if qAff`ch eq 2 then
		// Adjust the gram matrix entries accordingly.
		for i in [1..dim] do
		    for j in [1..dim] do
			case qAff`splitting_type:
			when "none", "ramified":
			    value := i eq j select gram[i,i]/2 else
				     (gram[i,j] + gram[j,i])/2;
			// !!! TODO: figure out whether this works
			when "inert", "split":
			    value := gram[i,j] / 2;
			end case;
			mat[i,j] := qAff`proj_pR(value);
			qAff`quotGram[i,j] := qAff`proj_pR2(value);
		    end for;
		end for;
	    end if;

	    // Building the affine space
	    
	    if qAff`splitting_type eq "split" then
		qAff`V := BuildTrivialReflexiveSpace(qAff`F, dim);
		id_map := map< qAff`F -> qAff`F | x :-> x >;
		qAff`inv_pR := FieldAutomorphism(qAff`F, id_map);
	    else
		qAff`V := BuildReflexiveSpace(mat, alpha_aff);
		qAff`inv_pR := alpha_aff;
	    end if;

            if IsIdentity(alpha) then
              qAff`inv_pR2 := map< qAff`quot -> qAff`quot | x :-> x >;
            else
              qAff`inv_pR2 := map< qAff`quot -> qAff`quot |
			      x :-> qAff`proj_pR2(nProc`inv_R(x@@qAff`proj_pR2))>;
            end if;
	    // Add this space to our associative array.
	    L`Vpp[pR] := qAff;
	end if;

	// Retrieve the affine reflexive space we're interested in.
	Vpp := L`Vpp[pR];

	// Build the skew vector.
	alpha := Involution(ReflexiveSpace(nProc`L));

	// !!! TODO : verify this is the correct dimension
	
	if Vpp`splitting_type in ["ramified", "inert"] then
	    nProc`skewDim := Integers()!(k*(k+1)/2);
	else
	    nProc`skewDim := Integers()!(k*(k-1)/2);
	end if;
	if nProc`skewDim ne 0 then
	    nProc`skew := Zero(MatrixRing(Vpp`F, k));
	end if;

	// Retrieve the first isotropic subspace of the given dimension.
	nProc`isoSubspace := FirstIsotropicSubspace(Vpp`V, k);

	// Lift subspace so that X and Z are a hyperbolic pair modulo pR * alpha(pR) and
	//  U is the hyperbolic complement to X+Z modulo pR * alpha(pR).
	nProc`X, nProc`Z, nProc`U :=
	    LiftSubspace(nProc : BeCareful := BeCareful);

	// Checking if we could lift modulo pR * alpha(pR)
	while IsEmpty(nProc`X) and (not IsEmpty(nProc`isoSubspace)) do
	    nProc`isoSubspace := NextIsotropicSubspace(Vpp`V, k);
	    nProc`X, nProc`Z, nProc`U :=
		LiftSubspace(nProc : BeCareful := BeCareful);
	end while;

	nProc`X_skew := [ x : x in nProc`X ];

        if Type(BaseRing(L)) eq RngInt then
          p := Norm(pR);
          // a scaling matrix for Hermite Normal Form over the rationals
          nProc`scale := DiagonalMatrix(Rationals(), [1 : i in [1..k]]
					cat [p^2 : i in [1..k]]
				 cat [p : i in [1..dim-2*k]]
					cat [p^3 : i in [1..dim]]);
        end if;

	return nProc;
end function;

// Constructing the next p-neighbor

function BuildNeighbor(nProc : BeCareful := true, UseLLL := false,
		       Perestroika := false)
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

    alpha := Involution(Q);

    // !!! TODO :
    // If one lifts ZZ and UU correctly, then the orthogonal
    // way should work, at least for inert and ramified ones
    
    if Vpp`splitting_type in ["split","ramified"] then
	pb := PseudoBasis(L);
	local_basis := [];
	for i in [1..dim] do
	    I := pb[i,1];
	    Igens := Generators(I);
	    if Igens[1] notin alpha(pR)*I then
		Append(~local_basis, Igens[1]*pb[i,2]);
	    else
		Append(~local_basis, Igens[2]*pb[i,2]);
	    end if;		
	end for;
	X_conj := [alpha(x) : x in XX];
	B := InnerForm(Q);
	//	    Fixing for it to work for larger k
	pairings := &cat[Eltseq(Matrix(y)*B*Transpose(Matrix(X_conj))) :
			 y in local_basis];
	kPbar, kPbarMap := ResidueClassField(alpha(pR));
	A := Matrix(kPbar, dim, #XX, [kPbarMap(x) : x in pairings]);
	lifted_null_space_basis := [&+[w[i]@@kPbarMap*local_basis[i] :
				       i in [1..dim]] :
				    w in Basis(Nullspace(A))];
	pbPbarLambda := PseudoBasis(alpha(pR)*Module(L));
	prePi := Module(lifted_null_space_basis cat
			&cat[[x*pb[2] : x in Generators(pb[1])] :
			     pb in pbPbarLambda]);
	Pi := &+[pR^-1 * x : x in XX] + prePi;
	psb := PseudoBasis(Pi);
	idls := [ x[1] : x in psb];
	basis := [ x[2] : x in psb];
	nLat := LatticeWithBasis(Q, Matrix(basis), idls);
    else
      // The special treatment below seems to sometime fail, so
      // we try to do the same
      // Special treatment of the rationals to speed things up
      if (Type(BaseRing(L)) eq RngInt) then	 
	  // The spacess we'll perform HNF on; they need to be scaled by D*p so
	  //  that HNF will be happy. We'll undo this once we perform HNF.
	  // Here D is the common denominator, which is a power of 2
	  p := Norm(pR);
          denom := L`pMaximal[pR][3]*BasisDenominator(Module(L));
          diag := Perestroika select
		  DiagonalMatrix(Rationals(), [1 : i in [1..k]]
					      cat [p : i in [1..k]]
					      cat [p^2 : i in [1..dim]])
		  else nProc`scale;
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

	  // Get new basis for the neighbor lattice.
	  
	  if Perestroika then
	      nLatBasis := __rescale(H, denom, dim);
	  else
              nLatBasis := __rescale(H, denom*p, dim);
	  end if;
	  
          // skip conversions back and forth
          if UseLLL and not BeCareful then
            zlat := Lattice(nLatBasis, 2*InnerForm(Q));
	    lll_ZZ := LLL(zlat : Proof := false);
            nLat := LatticeWithBasis(Q,
				   ChangeRing(BasisMatrix(lll_ZZ), Rationals()));
      
          // trying to save time in the next conversion
/*
          nLat`ZLattice := Lattice(ChangeRing(BasisMatrix(lll_ZZ), Rationals()),
				   2*InnerForm(Q));
          nLat`ZLattice`basisR := Basis(lll_ZZ);
          nLat`ZLattice`basisZ := ChangeRing(BasisMatrix(lll_ZZ), Rationals());
*/
//    if Perestroika then
//		nLat := ScaledLattice(nLat, 1/p);
//	    end if;
            return nLat;
	  end if;

	  // Build the neighbor lattice.

          nLat := LatticeWithBasis(Q, ChangeRing(nLatBasis, BaseRing(Q)));

      else
	if Perestroika then
	  idls := [ 1*R : i in [1..#XX] ] cat
	        [ alpha(pR) : i in [1..#ZZ] ] cat
	// There should not be any Us
	//	[ alpha(pR) : i in [1..#UU] ] cat
	        [ pR * alpha(pR) * pb[1] : pb in
						       PseudoBasis(Module(L)) ];
	else
	//  order to construct the neighbor lattice.
	idls := [ pR^-1 : i in [1..#XX] ] cat
	        [ alpha(pR) : i in [1..#ZZ] ] cat
		[ 1*R : i in [1..#UU] ] cat
	        [ pR * alpha(pR) * pb[1] : pb in
					   PseudoBasis(Module(L)) ];
        end if; 
	// Build the neighbor lattice.
	nLat := LatticeWithPseudobasis(Q, HermiteForm(PseudoMatrix(idls, bb)));

      end if;
    end if;
    if BeCareful then
       if not Perestroika then
	// Compute the intersection lattice.
	intLat := IntersectionLattice(nLat, L);
    
	// Verify that this neighbor has the proper index properties.
	assert Norm(Index(L, intLat)) eq nProc`pRnorm^nProc`k;
	assert Norm(Index(nLat, intLat)) eq nProc`pRnorm^nProc`k;
      end if;
      assert IsIntegral(ZLattice(nLat));
      assert IsIntegral(nLat);
    end if;
    
    if UseLLL then
	lll_ZZ := LLL(ZLattice(nLat) : Proof := false);
	K := BaseRing(Q);
	d := Degree(K);
        if d eq 1 then
	  nLat := LatticeWithBasis(Q,
				   ChangeRing(BasisMatrix(lll_ZZ), Rationals()));
        else
	  n := Dimension(Q);
          function __getBasis(Q, K, d, n, lll_ZZ)
	    basis := [VectorSpace(Q)![ K![b[j] : j in [d*(i-1)+1..d*i]] : i in [1..n]] : b in Basis(lll_ZZ)];
            return basis;
          end function;
          basis := __getBasis(Q, K, d, n, lll_ZZ);
	  nLat := LatticeWithBasis(Q, Matrix(basis));
        end if;
    end if;
/*
    if Perestroika then
	pi := Vpp`pElt;
	nLat := ScaledLattice(nLat, 1/pi);
    end if;
*/
    return nLat;
end function;

// Advancement - getting the next neighbor

procedure UpdateSkewMatrix(~nProc, ~row, ~col, overflow)
    // The affine data.
    Vpp := nProc`L`Vpp[nProc`pR];

    // The isotropic dimension we're interested in.
    k := nProc`k;

    // The primitive element of our finite field.
    x := Vpp`V`PrimitiveElement;

    F := Parent(x);
    
    repeat

	// Flag for determining whether we are done updating
	//  the skew matrix.
	done := true;
	
	// Increment value of the (row,col) position.
	if IsPrime(#F) then
	    nProc`skew[row,col] +:= 1;
	elif nProc`skew[row,col] eq 0 then
	    nProc`skew[row,col] := x;
	elif nProc`skew[row,col] eq 1 then
	    nProc`skew[row,col] := 0;
	else
	    nProc`skew[row,col] *:= x;
	end if;
	
	// Update the coefficient of the skew matrix reflected
	//  across the anti-diagonal.
	if (row + col ne k+1) then
	    nProc`skew[k-col+1,k-row+1] := -nProc`skew[row,col];
	end if;
	
	// If we've rolled over, move on to the next position.
	if nProc`skew[row,col] eq 0 then
	    // The next column of our skew matrix.
	    col +:= 1;
	    
	    // Are we at the end of the column?
	    if row+col eq overflow+1 then
		// Yes. Move to the next row.
		row +:= 1;
		
		// And reset the column.
		col := 1;
	    end if;
	    
	    // Indicate we should repeat another iteration.
	    done := false;
	end if;
    until done or row+col eq overflow+1;
end procedure;

procedure UpdateSkewSpace(~nProc : BeCareful := false)
    // The affine data.
    Vpp := nProc`L`Vpp[nProc`pR];
    // The isotropic dimension we're interested in.
    k := nProc`k;
    // Shortcuts for the projection maps modulo pR and
    //  pR * alpha(pR).
    map := Vpp`proj_pR;
    proj := Vpp`proj_pR2;
    // A nonzero element modulo pR^2 which is 0 modulo pR.
    pElt := Vpp`proj_pR2(Vpp`pElt);
    F := Parent(Vpp`V`PrimitiveElement);
    q := #F;
    // In the inert case we have to multiply by an element of trace zero.
    if Vpp`splitting_type eq "inert" and IsOdd(q) then
	factor := proj(((BaseRing(Vpp`V).1)^((q+1) div 2)) @@ map);
    else
	factor := 1;
    end if;
    // Update the skew space.
    nProc`X_skew := [ nProc`X[i] + pElt * factor *
				   &+[ proj(nProc`skew[i,j] @@ map) * nProc`Z[j]
				       : j in [1..k] ] : i in [1..k] ];
    if BeCareful then
	M_X := Matrix(nProc`X_skew);
	alpha := nProc`inv_R;
	alpha_M_X := Parent(M_X)![[alpha(M_X[i,j]) :
				   j in [1..Ncols(M_X)]]
				  : i in [1..Nrows(M_X)]];
	assert IsZero(M_X * ChangeRing(Vpp`quotGram, BaseRing(M_X)) *
		      Transpose(alpha_M_X));
    end if;
end procedure;

procedure GetNextNeighbor(~nProc : BeCareful := false)
	// The affine data.
	Vpp := nProc`L`Vpp[nProc`pR];

	// The isotropic dimension we're interested in.
	k := nProc`k;

	// The starting position of the skew vector to update.
	row := 1; col := 1;

	if Vpp`splitting_type in ["ramified", "inert"] then
	// In this case we also fill the anti-diagonal
	    overflow := k+1;
	else
	    overflow := k;
	end if;
	
	// Update the skew matrix
	if nProc`skewDim ne 0 then
	    UpdateSkewMatrix(~nProc, ~row, ~col, overflow);
	end if;

	// If we haven't rolled over, update the skew space and return...
	if (row+col lt overflow+1) then
	    UpdateSkewSpace(~nProc : BeCareful := BeCareful);
	    return;
	end if;

	if GetVerbose("AlgebraicModularForms") ge 2 then
	    printf "Currently space = %o, running NextIsotropicSubspace...\n",
		   nProc`isoSubspace;
	end if;
	
	// ...otherwise, get the next isotropic subspace modulo pR.
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
	
//	end if;
	
end procedure;

procedure SkipToNeighbor(~nProc, space, skew : BeCareful := false)
    nProc`isoSubspace := space;
    nProc`X, nProc`Z, nProc`U := LiftSubspace(nProc
					      : BeCareful := BeCareful,
						Override := true);
    nProc`X_skew := [ x : x in nProc`X ];
    // Update the skew matrix (only for k ge 2).
    if (nProc`skewDim ne 0) and (not IsEmpty(nProc`X)) then
	nProc`skew := skew;
	UpdateSkewSpace(~nProc);
    end if;
    
end procedure;

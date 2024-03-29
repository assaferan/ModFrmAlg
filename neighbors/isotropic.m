freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J. Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
                                                                            
   FILE: isotropic.m (class for tracking computation of isotropic subspaces)

   05/29/20: Modified NumberOfNeighbors to return the right answer also in the
             unitary case.

   05/29/20: Reverted last update. We don't want vectors from the radical,
             they contribtute to isotropic subsapces, but not to neighbors.

   05/26/20: Added __pivots_singular, allowing to choose vectors from the 
             radical as part of the isotropic subspace.
             Modified the construction of the hermitian form in char 2.

   05/08/20: relaxed the condition k = 1, to catch the problems in
             Orbits for k > 1 for future use.

   04/24/20: Fixed bug in BuildTrivialReflexiveSpace of not assigning 
   	     PrimitiveElement attribute.

   04/14/20: Added formulae for the number of isotropic subspaces for unitary
             spaces.

   04/10/20: Fixed bugs in computations for inert primes and mod 2.

   03/10/20: added the intrinic BuildTrivialReflexiveSpace, 
   for the split primes in the unitary case, where all lines mod p are isotropic 
   (lifted by multiplying by a uniformizer). 

   03/07/20: added the intrinsics BuildReflexiveSpace, generalizing BuildQuadraticSpace

   03/05/20: started from the orthogonal modular forms structure
 
***************************************************************************/

// Here are the intrinsics this file defines
// BuildTrivialReflexiveSpace(F::FldFin, dim::RngIntElt) -> ModTupFld
// BuildReflexiveSpace(M::ModMatFldElt) -> ModTupFld
// BuildReflexiveSpace(M::AlgMatElt, alpha::FldAut) ->  ModTupFld
// FirstIsotropicSubspace(V::ModTupFld, k::RngIntElt) -> SeqEnum
// NextIsotropicSubspace(V::ModTupFld, k::RngIntElt) -> SeqEnum
// NumberOfIsotropicSubspaces(V::ModTupFld, k::RngIntElt) -> RngIntElt
// AllIsotropicSubspaces(V::ModTupFld, k::RngIntElt) -> SeqEnum
// NumberOfIsotropicSubspaces(M::ModFrmAlg, p::RngIntElt, k::RngIntElt) -> RngIntElt
// NumberOfIsotropicSubspaces(M::ModFrmAlg, pR::RngInt, k::RngIntElt) -> RngIntElt
// NumberOfIsotropicSubspaces(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt) -> RngIntElt
// NumberOfNeighbors(M::ModFrmAlg, p::RngIntElt, k::RngIntElt) -> RngIntElt
// NumberOfNeighbors(M::ModFrmAlg, pR::RngInt, k::RngIntElt) -> RngIntElt
// NumberOfNeighbors(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt) -> RngIntElt

declare type IsoParam;
declare attributes IsoParam:
	// A list of valid pivots.
	Pivots,

	// A pointer to the current pivot.
	PivotPtr,

	// The free variables that parameterize the isotropic subspaces with
	//  respect to our current pivot.
	FreeVars,

	// The parameters for the free variables for the current pivot.
	Params,

	// A matrix whose rows correspond to the parameterized isotropic
	//  subspaces.
	IsotropicParam;

// imports

import "../utils/helper.m" : printEstimate;

import "neighbor-CN1.m" : BuildNeighborProc;

// A helper function for computing valid pivots.
function __pivots(n, aniso, k)
        // Base case.
        if k eq 1 then return [ [i] : i in [1..n-aniso] ]; end if;

        // Retrieve lower-dimensional maximal pivots.
        pivots1 := __pivots(n-2, aniso, k-1);
        pivots1 := [ [ x+1 : x in data ] : data in pivots1 ];

        // Determine the first set of pivots.
        pivots1 := [ [1] cat data : data in pivots1 ] cat
                [ data cat [n-aniso] : data in pivots1 ];

        // Add additional pivots when we're not in the maximal case.
        if 2*k lt n-aniso then
                pivots2 := __pivots(n-2, aniso, k);
                pivots2 := [ [ x+1 : x in data ] : data in pivots2 ];
                return pivots1 cat pivots2;
        end if;

        return pivots1;
end function;

// allow radicals to be pivots
// That's relevant in characteristic 2 of even dimension
// !!! TODO : the above function is a special case when nrad = 0
// unite them

function __pivots_singular(n, aniso, k, nrad)
    // Base case.
    if k eq 1 then
	return [ [i] : i in [1..n-aniso] cat [n+1..n+nrad] ];
    end if;

    // Retrieve lower-dimensional maximal pivots.
    pivots1 := __pivots_singular(n-2, aniso, k-1, nrad);
    pivots1 := [ [ x le n-2-aniso select x+1 else x+2 : x in data ] :
		 data in pivots1 ];

    // Determine the first set of pivots.
    pivots1 := [ [1] cat data : data in pivots1 ] cat
               [ Sort(data cat [n-aniso]) : data in pivots1 ];

    // Add additional pivots when we're not in the maximal case.
    if 2*k-nrad lt n-aniso then
        pivots2 := __pivots_singular(n-2, aniso, k, nrad);
        pivots2 := [ [ x le n-2-aniso select x+1 else x+2 : x in data ] :
		     data in pivots2 ];
        return pivots1 cat pivots2;
    end if;
    
    return pivots1;
    
end function;

// This is to get all lines, for the split primes in the unitary case
intrinsic BuildTrivialReflexiveSpace(F::FldFin,
			dim::RngIntElt) -> ModTupFld[FldFin]
{.}
  V := VectorSpace(F, dim);
  V`AnisoDim := 0;
  V`RadDim := 0;
  // Create an empty parameterization array.
  V`ParamArray := AssociativeArray();
  V`WittIndex := 0;
  V`S := [ 0 ] cat [ x : x in F | x ne 0 ];
  V`Symbolic := true;
  V`QStd := QuadraticForm(MatrixAlgebra(F,dim)!0);
  V`Basis := BasisMatrix(V);
  V`GramMatrix := MatrixAlgebra(F,dim)!0;
  V`GramMatrixStd := MatrixAlgebra(F,dim)!0;

  // Assign the cyclic generator of the group of units of the field.
  V`PrimitiveElement := PrimitiveElement(F);
  
  return V;
end intrinsic;

intrinsic BuildReflexiveSpace(M::ModMatFldElt : Symbolic := true)
	-> ModTupFld[FldFin]
{ Builds the reflexive space associated to the supplied Gram matrix. }
	M := Matrix(BaseRing(M), Nrows(M), Ncols(M), Eltseq(M));
	return BuildReflexiveSpace(M : Symbolic := Symbolic);
end intrinsic;

// Construct the reflexive space that we'll use to compute all isotropic lines.
intrinsic BuildReflexiveSpace(M::AlgMatElt[FldFin], alpha::FldAut :
			      Symbolic := true) ->  ModTupFld[FldFin]
{ Builds the reflexive space associated to the supplied Gram matrix. }
     // The reflexive space.
     if (Order(alpha) eq 2) then
       V := UnitarySpace(M, Automorphism(alpha));
       spaceType := "Hermitian";
     else if IsIdentity(alpha) then
       if Transpose(M) eq M then
         V := QuadraticSpace(M);
         spaceType := "Symmetric";
       else if Transpose(M) eq -M then
         V := SymplecticSpace(M);
         spaceType := "Alternating";
       else
	 error "Space does not represent a reflexive form.\n", M;
       end if;
       end if;
     else
       error "%o is not an involution!", alpha;
     end if;
     end if;

     // Make sure we're in dimension 3 or higher.
     // Why ???? and also it says 2 (!) ? 
     require Dimension(V) ge 2: "Dimension must be 3 or greater.";

     // Assign the Gram matrix.
     V`GramMatrix := M;
     
     // Decompose the form into a standard form (H + A + R).
     if spaceType eq "Symmetric" then
 	 V`GramMatrixStd, V`Basis := Decompose(M);
     elif spaceType eq "Hermitian" then
	 V`GramMatrixStd, V`Basis := Decompose(M, alpha);
     end if;

     // Count the rows at the end of the matrix which are exactly zero.
     idx := Dimension(V);
     while idx ge 1 and V`GramMatrixStd[idx] eq Zero(V) do
	 idx -:= 1;
     end while;

     // The dimension of the radical.
     V`RadDim := Dimension(V) - idx;

     // Determine the dimension of the totally hyperbolic subspace.
     idx := 1;
     while idx le Dimension(V)-V`RadDim and V`GramMatrixStd[idx,idx] eq 0 do
	 idx +:= 1;
     end while;

     // Dimension of the anistotropic subspace.
     V`AnisoDim := Dimension(V) - V`RadDim - idx + 1;

     // The number of hyperbolic planes in the Witt decomposition.
     // V`WittIndex := Integers()!((idx-1)/2);
     V`WittIndex := (idx - 1) div 2;

     // Assign the multinomial of the reflexive form.
     // Might want to change this one to the
     // bilinear form in general

     if spaceType eq "Symmetric" then
	 if Characteristic(BaseRing(M)) ne 2 then
	     V`Q := QuadraticForm(M / 2);
	     V`QStd := QuadraticForm(V`GramMatrixStd / 2);
	 else
	     V`Q := QF2(M);
	     V`QStd := QF2(V`GramMatrixStd);
	 end if;
     elif spaceType eq "Hermitian" then
	 F := BaseRing(V);
	 R := PolynomialRing(F, 2 * Dimension(V));
	 gens := GeneratorsSequence(R);
	 alpha_R := hom<R -> R | V`Involution, gens>;
	 // Initialize matrix that will determine parameterization.
	 vec := Vector([ R.i + F.1 * (R.(i+Dimension(V))) :
			 i in [1..Dimension(V)] ]);
	 vec_bar := Vector([alpha_R(x) : x in Eltseq(vec)]);
	 if Characteristic(BaseRing(M)) ne 2 then
	     V`Q := (vec * ChangeRing(M/2, BaseRing(vec)), vec_bar);
	     V`QStd := (vec * ChangeRing(V`GramMatrixStd/2, BaseRing(vec)),
			vec_bar);
	 else
	     V`Q := (vec * ChangeRing(M, BaseRing(vec)), vec_bar);
	     V`QStd := (vec * ChangeRing(V`GramMatrixStd, BaseRing(vec)),
			vec_bar);
	 end if;
     end if;

     // Assign an ordering to the elements of the finite field.
     V`S := [ 0 ] cat [ x : x in FixedField(alpha) | x ne 0 ];

     // Create an empty parameterization array.
     V`ParamArray := AssociativeArray();

     // Set symbolic flag.
     V`Symbolic := Symbolic;

     // Assign the cyclic generator of the group of units of the field.
     V`PrimitiveElement := PrimitiveElement(FixedField(alpha));

     return V;
end intrinsic;

procedure __initializePivot(V, k)
    // Retrieve parameters for this dimension.
    data := V`ParamArray[k];

    // The current pivot.
    pivot := data`Pivots[data`PivotPtr];

    // The base field.
    F := BaseRing(V);

    rank := k * Dimension(V);
	
    if IsUnitarySpace(V) then
	// Multivariant polynomial ring used to determine parameterization.
	R := PolynomialRing(F, 2 * rank);
	gens := GeneratorsSequence(R);
	alpha := hom<R -> R | V`Involution, gens>;
	// Initialize matrix that will determine parameterization.
	M := Matrix(R, k, Dimension(V), [R.i + F.1 * (R.(i+rank)) : i in [1..rank] ]);
    else
	// Multivariant polynomial ring used to determine parameterization.
	R := PolynomialRing(F, rank);
	alpha := hom<R -> R | IdentityFieldMorphism(F), GeneratorsSequence(R)>;
	// Initialize matrix that will determine parameterization.
	M := Matrix(R, k, Dimension(V), [ R.i : i in [1..rank] ]);
    end if;

    // Keep a list of non-free variables from which we will determine the
    //  free variables when we are done.
    remove := [];

    // Setup the columns corresponding to the pivots.
    for i in [1..k], j in [1..k] do
	M[i,pivot[j]] := i eq j select 1 else 0;
	Append(~remove, (i-1)*Dimension(V) + pivot[j]);
    end for;

    // Clear the rows prior to the pivot positions (but not the radical).
    for i in [1..k], j in [1..pivot[i]-1] do
	M[i,j] := 0;
	Append(~remove, (i-1)*Dimension(V) + j);
    end for;
    
    // Check if one or more of the anisotropic coordinates need to be zero.
    for i in [1..k] do
	if pivot[i] gt V`WittIndex then
	    for j in [1..V`AnisoDim] do
		M[i,Dimension(V)+1-V`RadDim-j] := 0;
		Append(~remove, i*Dimension(V)+1-V`RadDim-j);
	    end for;
	end if;
    end for;

    // Determine the number of rows of the matrix that we'll echelonize.
    rows := Integers()!(k*(k+1)/2);
    cols := Rank(R) + 1;

    // The field of fractions of the polynomial ring.
    RF := FieldOfFractions(R);

    // The matrix that we're going to echelonize.
    mat := Matrix(RF, rows, cols, [ 0 : i in [1..rows*cols] ]);

    // The current row to fill in in the matrix.
    row := 1;

    for i in [1..k], j in [i..k] do
	// The appropriate vector that we want to be isotropic.
	vec := i eq j select M[i] else M[i]+M[j];

	if IsUnitarySpace(V) then
	    FF := FixedField(FieldAutomorphism(F, V`Involution));
	    param_vars := [[],[]];
	    for idx in [1..Dimension(V)] do
		coeffs, monoms := CoefficientsAndMonomials(vec[idx]);
		param_coeffs := [Eltseq(x, FF) : x in coeffs];
		if vec[idx] eq 0 then
		    params := [R!0,R!0];
		else
		    params := [&+[param_coeffs[i][j] * monoms[i] :
				  i in [1..#monoms]] : j in [1..2]];
		end if;
		Append(~param_vars[1], R!params[1]);
		Append(~param_vars[2], R!params[2]);
	    end for;
	    f := Evaluate(V`QStd, param_vars[1] cat param_vars[2]);
	else
	    f := Evaluate(V`QStd, Eltseq(vec));
	end if;
	
	// Check each term of the resulting multinomial.
	if f ne 0 then
	    for term in Terms(f) do
		if Degree(term) eq 2 then
		    // Degree 2 terms are inhomogenous.
		    mat[row][cols] -:= term;
		else
		    // Otherwise we have a linear term.
		    // val, mono := Contpp(term);
		    vals, monos := CoefficientsAndMonomials(term);
		    val := vals[1]; mono := monos[1];
		    coord := &+[ mono eq R.n select n else 0
				 : n in [1..Rank(R)] ];
		    
		    // And so fill in the matrix accordingly.
		    mat[row,coord] := val;
		end if;
	    end for;
	end if;
	
	// Move on to the next row.
	row +:= 1;
    end for;

    // Compute the Echelon form of the matrix.
    E := EchelonForm(mat);

    // The evaluation list for replacing variables with their dependence
    //  relations.
    list := [* R.i : i in [1..Rank(R)] *];

    for i in [1..Nrows(E)] do
	// Find the pivot in the i-th row.
	c := 0; repeat c +:= 1;
		until c gt Rank(R)+1 or E[i][c] eq 1;
	
	// Add this pivot to the list of non-free variables.
	Append(~remove, c);
	
	// If the pivot is equal to rank+1, we have a problem.
	assert c ne Rank(R)+1;

	// If the row is entirely zero, skip it.
	if c gt Rank(R)+1 then continue; end if;
	
	// Build the multinomial for which R.c is dependent.
	f := E[i][Rank(R)+1];
	for j in [ l : l in [1..Rank(R)] | l ne c ] do
	    f -:= E[i][j] * R.j;
	end for;
	list[c] := f;
    end for;

    // The matrix whose rows parameterize all isotropic subspaces.
	
    M := Evaluate(M, [ l : l in list ]);

    // Verify that we didn't screw up somewhere along the line.
    for i in [1..k], j in [i..k] do
	vec := i eq j select M[i] else M[i]+M[j];
	if IsUnitarySpace(V) then
	    FF := FixedField(FieldAutomorphism(F, V`Involution));
	    param_vars := [[],[]];
	    for idx in [1..Dimension(V)] do
		coeffs, monoms := CoefficientsAndMonomials(Numerator(vec[idx]));
		param_coeffs := [Eltseq(x, FF) : x in coeffs];
		if vec[idx] eq 0 then
		    params := [R!0, R!0];
		else
		    params := [&+[param_coeffs[i][j] * monoms[i] : i in [1..#monoms]] : j in [1..2]];
		end if;
		Append(~param_vars[1], R!params[1]);
		Append(~param_vars[2], R!params[2]);
	    end for;
	    f := Evaluate(V`QStd, param_vars[1] cat param_vars[2]);
	else
	    f := Evaluate(V`QStd, Eltseq(vec));
	end if;
	assert f eq 0;
    end for;

    // Determine the free variables.
    // Note that in the unitary case, they are taken from the fixed field
    // of the involution

    remove cat:= [n : n in [1..Rank(R)] |
		  &and [ Degree(R!M[i,j],n) le 0 : i in [1..k],
						   j in [1..Dimension(V)] ]];
    
    data`FreeVars := [ n : n in [1..Rank(R)] | not n in remove ];

    // The parameterization vector for this pivot.
    data`Params := [* 0 : i in [1..#data`FreeVars] *];

    // Assign the parameterization of the isotropic subspaces.
    data`IsotropicParam := M;
end procedure;

intrinsic FirstIsotropicSubspace(V::ModTupFld[FldFin], k::RngIntElt) -> SeqEnum
{ Returns the first non-singular isotropic subspace. }
	// Make sure the requested dimension is valid.
	require k ge 1: "Requested isotropic dimension must be at least 1.";

	// Parameters for this dimension not yet initialized, so create a new
	//  entry in the catalog.
	if not IsDefined(V`ParamArray, k) then
		data := New(IsoParam);
		data`Pivots := __pivots(Dimension(V) - V`RadDim, V`AnisoDim, k);
		// data`Pivots := __pivots_singular(Dimension(V) - V`RadDim,
			//			 V`AnisoDim, k, V`RadDim);
		V`ParamArray[k] := data;
	end if;

	// Reset the pivot pointer and subspace parameters.
	V`ParamArray[k]`PivotPtr := 0;
	V`ParamArray[k]`Params := [];

	// Return the first isotropic subspace.
	return NextIsotropicSubspace(V, k);
end intrinsic;

intrinsic NextIsotropicSubspace(V::ModTupFld[FldFin], k::RngIntElt) -> SeqEnum
{ Returns the next non-singular isotropic subspace. }
	// Make sure the requested dimension is valid.
	require k ge 1: "Requested isotropic dimension must be at least 1.";

	// If isotropic subspaces of this dimension haven't been initialized,
	//  then treat it as if we were requesting the first isotropic subspace.
	if not IsDefined(V`ParamArray, k) then
	    data := New(IsoParam);
	    data`Pivots := __pivots(Dimension(V) - V`RadDim, V`AnisoDim, k);
	    // data`Pivots := __pivots_singular(Dimension(V) - V`RadDim,
		//			     V`AnisoDim, k, V`RadDim);
	    data`PivotPtr := 0;
	    data`Params := [];
	    V`ParamArray[k] := data;
	end if;

	// Retrieve the parameters for the requested dimension.
	data := V`ParamArray[k];

	// Check to see if we need to initialize a new pivot.
	if #data`Params eq 0 then
	    // Move to the next pivot.
	    data`PivotPtr +:= 1;

	    // If we've exceeded the list of pivots, we're done.
	    if data`PivotPtr gt #data`Pivots then
		// Reset the pivot pointer so that we can loop through
		//  the isotropic subspaces again if needed.
		data`PivotPtr := 0;
		return [];
	    end if;

	    // Initialize the new pivot.
	    __initializePivot(V, k);
	end if;

	// The dimension of the isotropic subspace we're constructing.
	k := #data`Pivots[data`PivotPtr];

	// The list of evaluation values.
	evalList := [* 0 : i in [1..Dimension(V)*k] *];

	if IsUnitarySpace(V) then
	    evalList := [* 0 : i in [1..Dimension(V) * k * 2] *];
	end if;

	// Produce the isotropic subspace corresponding to the current
	//  parameters.
	for i in [1..#data`Params] do
	    if V`Symbolic then
		evalList[data`FreeVars[i]] := V`S[data`Params[i]+1];
	    else
		evalList[data`FreeVars[i]] := data`Params[i];
	    end if;
	end for;

	// The basis for the current isotropic subspace.
	space := Rows(Evaluate(data`IsotropicParam, [ x : x in evalList]));

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

	return space;
end intrinsic;

intrinsic AllIsotropicSubspaces(V::ModTupFld[FldFin], k::RngIntElt
				: Estimate := true) -> SeqEnum
{ Returns an array consisting of all isotropic subspaces of dimension k. }
	// TODO: Relax this condition to allow for higher dimensional spaces.
	// require k eq 1: "Must be one dimensional subspaces currently.";

	// The first isotropic subspace.
	space := FirstIsotropicSubspace(V, k);

	// The list of isotropic subspaces.
	list := [];

        vprintf AlgebraicModularForms, 1 :
	  "Computing orbits on isotropic subspaces. Building list of spaces.\n";

        total := NumberOfIsotropicSubspaces(V,k);
        count := 0;
        elapsed := 0;
        start := Realtime();

	while space ne [] do
	    // Retrieve the isotropic subspace in the original coordinates.
	    vecs := [Vector(Matrix(x) * Transpose(V`Basis)) : x in space];
	    
	    // Add to list.
	    Append(~list, sub< V | vecs >);

	    // Next subspace.
	    space := NextIsotropicSubspace(V, k);
            if Estimate then
              printEstimate(start, ~count, ~elapsed, total,
			    "AllIsotropicSubspaces" :
			    printSkip := 10^6, printOffset := 5*10^5);
            end if;
	end while;

        // Maybe we don't want this assertion - it is just for testing the formula
        assert #list eq total;

	return list;
end intrinsic;

function NumIsotropicSubspacesUnitary(q, n, f, k)
    // formula from J.B.Derr
    // "Stabilizers of isotropic subspaces in classical groups",
    // Corollary 2 with d = 0, a,b,c = 0,k,0
    n := n-f;
    count := &*[q^(2*(n-i)-1) - q^(2*i) + (-1)^n*(q^n - q^(n-1))
		: i in [0..k-1] ] div
	     &*[q^(2*k) - q^(2*i) : i in [0..k-1] ];
    count *:= q^(k*f);
    return count;
end function;

function NumIsotropicSubspacesQuadratic(q, r, a, f, k)
    // Compute the number of isotropic subspaces.
    // This is from Murphy's thesis (also accounting for the radical)
    count := q^(k*f) * &*[q^(r-i+1)-1 : i in [1..k]] *
	     &*[q^(r+a-i)+1 : i in [1..k]] /
	     &*[ q^i-1 : i in [1..k] ];
    return count;
end function;

intrinsic NumberOfIsotropicSubspaces(V::ModTupFld[FldFin],
				     k::RngIntElt) -> RngIntElt
{ Counts all isotropic subspaces of dimension k. }

        F := BaseRing(V);
        q := #F;
        n := Dimension(V);
        r := V`WittIndex;
        a := V`AnisoDim;
        f := V`RadDim;
        if IsUnitarySpace(V) then
	  // V is a Hermitian space
	  _, q := IsSquare(q);
	  count := NumIsotropicSubspacesUnitary(q, n, f, k);
        elif IsQuadraticSpace(V) then
	  // in this case V is orthogonal
	     
	  // Compute the number of isotropic subspaces.
	  // This is from Murphy's thesis (also accounting for the radical)
	  
	  count := NumIsotropicSubspacesQuadratic(q, r, a, f, k);
        else
	  // This is a trivial reflexive space
	  // return number of all k-dimensional subspaces
	  count :=  &*[ q^(n-i+1)-1 : i in [1..k] ] / 
	            &*[ q^i-1 : i in [1..k] ];
	end if;

	// Verify that this count is an integer.
	assert Denominator(count) eq 1;

	return Integers()!count;
end intrinsic;

intrinsic NumberOfIsotropicSubspaces(M::ModFrmAlg, p::RngIntElt, k::RngIntElt)
	-> RngIntElt
{ Determine the number of isotropic subspaces. }
	return NumberOfIsotropicSubspaces(M, ideal< Integers() | p >, k);
end intrinsic;

// This is an internal function, since the intrinsic interface requires
// two different functions
function internalNumIsoSubs(M, pR, k)
  L := Module(M);
  nProc := BuildNeighborProc(L, pR, k);
  qAff := nProc`L`Vpp[pR];
  V := qAff`V;

  if qAff`splitting_type eq "split" then
    q := #qAff`F;
    n := Dimension(V);
    return (q^n - 1) div (q-1);
  else
    return NumberOfIsotropicSubspaces(V, k);
  end if;
end function;

intrinsic NumberOfIsotropicSubspaces(M::ModFrmAlg, pR::RngInt, k::RngIntElt)
	-> RngIntElt
{ Determine the number of isotropic subspaces. }
  // Make sure that the dimension is valid.
  require k ge 1:
    "Isotropic subspaces must have positive dimension.";

  // Verify that the ideal is prime.
  require IsPrime(pR): "Specified ideal must be prime.";

  return internalNumIsoSubs(M, pR, k);
end intrinsic;

intrinsic NumberOfIsotropicSubspaces(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt)
	-> RngIntElt
{ Determine the number of isotropic subspaces. }
  // Make sure that the dimension is valid.
  require k ge 1:
    "Isotropic subspaces must have positive dimension.";

  // Verify that the ideal is prime.
  require IsPrime(pR): "Specified ideal must be prime.";

  return internalNumIsoSubs(M, pR, k);
end intrinsic;

intrinsic NumberOfNeighbors(M::ModFrmAlg, p::RngIntElt, k::RngIntElt)
	-> RngIntElt
{ Determine the number of p^k-neighbor lattices. }
  pR := ideal<Integers(BaseRing(M)) | p>;
  return NumberOfNeighbors(M, pR, k);
end intrinsic;

// This is an internal function, since the intrinsic interface requires
// two different functions
function internalNumNeighbors(M, pR, k)
  // Determine the number of isotropic subspaces.
  n := NumberOfIsotropicSubspaces(M, pR, k);

  // The size of the residue class field.
  q := #ResidueClassField(pR);

  alpha := Involution(ReflexiveSpace(Module(M)));
  // Compute the number of p^k-neighbors.
  if IsOrthogonal(M) or (alpha(pR) ne pR) then
    // Either orthogonal or split unitary case
    return n * q^(Integers()!(k*(k-1)/2));
  else
    return n * q^(k*(k+1) div 2);
  end if;
end function;

intrinsic NumberOfNeighbors(M::ModFrmAlg, pR::RngInt, k::RngIntElt)
	-> RngIntElt
{ Determine the number of p^k-neighbor lattices. }
  return internalNumNeighbors(M, pR, k);
end intrinsic;

intrinsic NumberOfNeighbors(M::ModFrmAlg, pR::RngOrdIdl, k::RngIntElt)
	-> RngIntElt
{ Determine the number of p^k-neighbor lattices. }
  return internalNumNeighbors(M, pR, k);
end intrinsic;

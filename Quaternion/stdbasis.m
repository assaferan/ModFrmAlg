// freeze;
/****-*-magma-******a********************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                             Eran Assaf                                 
                                                                            
   FILE: stdbasis.m (Implementation file for converting hermitian forms defined over algebras over finite
   fields into a standard form)

   This means that the hermitian form will be expressed as hyperbolic + 
   anisotropic + radical, where the hyperbolic component is antidiagonal.

   04/04/2023 : Started this file by copying from unitary case
 
 ***************************************************************************/

// Question - does it still work in this generality?

// This one might not work sometimes - should fix that.

intrinsic OrthogonalizeForm(M::AlgMatElt, alpha::AlgAut) -> AlgMatElt
{.}
  MS := Parent(M);
  n := Degree(MS);
  one := MS!1;
  T := one;

  for i in [1..n] do
    if M[i,i] eq 0 then
      for j in [i+1..n] do
        if M[i,j] ne 0 then
          tmp := one;
          if M[i,j] + M [j,j] eq 0 then
	    tmp[j,i] := -1;
          else
	    tmp[j,i] := 1;
          end if;
          T := T * tmp;
          M := tmp * M * alpha(Transpose(tmp));
          break;
	end if;
      end for;
    end if;

    if M[i,i] ne 0 then
      tmp := one;
      for j in [i+1..n] do
        if M[i,j] ne 0 then
          tmp[i,j] := -M[i,j] / M[i,i];
        end if;
      end for;
      M := tmp * M * alpha(Transpose(tmp));
      T := T * tmp; 
    end if;
  end for;

  return M,T;
end intrinsic;

intrinsic HermitianForm(M::AlgMatElt, alpha::AlgAut) -> AlgMatElt
{.}
  MS := Parent(M);
  n := Degree(MS);
  R := PolynomialRing(BaseRing(M), 2*n);
  x_names := ["x" cat IntegerToString(i) : i in [1..n]];
  y_names := ["y" cat IntegerToString(i) : i in [1..n]];
  if Order(alpha) ne 1 then
    y_names := [var cat "bar" : var in y_names];
  end if;
  names := x_names cat y_names;
  AssignNames(~R, names);
  x := Vector([R.i : i in [1..n]]);
  y := Vector([R.(n+i) : i in [1..n]]);
  
  return (x*ChangeRing(M,R), y);
end intrinsic;

function VerifyMatrix(M, alpha)
	// Get the base ring and its characteristic.
	F := BaseRing(M);
	char := Characteristic(F);

	// Ensure that the matrix is square.
	assert Nrows(M) eq Ncols(M);

	// The dimension.
	dim := Nrows(M);

	// Make sure the matrix is hermitian.
        assert M eq Transpose(alpha(M));

	// Create a vector space we'll be working over.
	V := VectorSpace(F, dim);

	return F, V, char, dim;
end function;

function getNormRoot(elt, alpha)
  K := BaseField(alpha);
  F := FixedField(alpha);
  zeta := PrimitiveElement(K);
  is_square, root := IsSquare(F!elt);
  if is_square then return root; end if;
  is_square, root := IsSquare(F!(elt / Norm(zeta)));
  assert is_square;
  return root*zeta;
end function;


function FindIsotropicVector(M, alpha)
	// Get some useful information about the form / do a sanity check.
        F, V, char, dim := VerifyMatrix(M, alpha);

	if Determinant(M) eq 0 then
		// Return the first vector in the null space.
		return true, Rows(NullspaceMatrix(M))[1];
	elif dim eq 1 then
		// Return the first basis vector.
	        if M[1,1] eq 0 then
		   return true, V.1;
		else
		  return false, _;
                end if;
	elif dim eq 2 then
		// Take care of the easy case first.
		if M[1,1] eq 0 then return true, V.1; end if;

		// Simplify things by giving the coefficients names.
 		a := M[1,1]; b := M[1,2]; c := M[2,2];
 
                d := getNormRoot(b * alpha(b) - a*c, alpha);

                return true, V.2 + ((d - alpha(b))/a) * V.1;
	else
		// Check the diagonal for an isotropic basis vector.
		for i in [1..dim] do
			if M[i,i] eq 0 then return true, V.i; end if;
		end for;

                // !!! TODO - this is an overkill for the unitary case -
                // can just look at two.
		//  start by considering only three variables.
		subM := Submatrix(M, 1, 1, 3, 3);

		// Save a copy of the submatrix so we can verify correctness.
		backupM := subM;

		// Change of basis matrix which realizes the isometry on this
		//  submatrix.
		basis := Id(GL(VectorSpace(F, 3)));

		// Clear the off-diagonal entries.
		for i in [1..2], j in [i+1..3] do
			scalar := -subM[i,j] / subM[i,i];
			AddColumn(~subM, scalar, i, j);
                        AddRow(~subM, alpha(scalar), i, j);
                        AddRow(~basis, alpha(scalar), i, j);

			// We may have inadvertantly created an isotropic basis
			//  vector, so let's make sure before we proceed.
			if subM[j,j] eq 0 then
				return true, Vector(Eltseq(basis[j]) cat
					 [ 0 : i in [4..dim] ]);
			end if;
		end for;

		// Make sure we didn't make a mistake.
                assert basis * backupM * Transpose(alpha(basis)) eq subM;

		d := getNormRoot(-subM[1,1] * subM[2,2], alpha);

		vec := basis[1] + (M[1,1]/d) * basis[2];
		vec := Vector(Eltseq(vec) cat [ 0 : i in [4..dim] ]);
		return true, vec;
        end if;
end function;

function SplitHyperbolicPlane(M, alpha, vec)
	// Get the relevant data structures.
        F, V, char, dim := VerifyMatrix(M, alpha);

	// The change of basis which preserving the isometry.
	basis := Id(GL(V));

	// Make a copy of the Gram matrix.
	gram := M;

	// Save a copy of the original Gram matrix.
	originalGram := gram;

	// Find the pivot of the specified vector.
	pivot := 0;
	repeat pivot +:= 1;
	until vec[pivot] ne 0;

	// Perform the necessary basis changes so that vec becomes the first
	//  basis vector.
        MultiplyRow(~basis, vec[pivot], pivot);
        MultiplyColumn(~gram, alpha(vec[pivot]), pivot);
        MultiplyRow(~gram, vec[pivot], pivot);
	for i in [pivot+1..dim] do
		AddRow(~basis, vec[i], i, pivot);
                AddColumn(~gram, alpha(vec[i]), i, pivot);
                AddRow(~gram, vec[i], i, pivot);
	end for;
	SwapRows(~basis, 1, pivot);
	SwapColumns(~gram, 1, pivot);
	SwapRows(~gram, 1, pivot);

	// If the first row is entirely zero, then this vector belongs to the
	//  radical of the form.
	if gram[1] eq Zero(V) then
		return gram, basis;
	end if;

	// Find a basis vector which is not orthogonal to our isotropic vector.
	idx := 1;
	repeat idx +:= 1;
	until gram[1,idx] ne 0;

	// Swap this basis vector with the second basis.
	SwapRows(~basis, 2, idx);
	SwapColumns(~gram, 2, idx);
	SwapRows(~gram, 2, idx);

	// Normalize the second basis vector so the (1,2)-entry is 1.
	scalar := 1/gram[1,2];
        MultiplyRow(~basis, alpha(scalar), 2);
        MultiplyColumn(~gram, scalar, 2);
        MultiplyRow(~gram, alpha(scalar), 2);

	// Determine the appropriate scalar for clearing out the (2,2)-entry.
	if char eq 2 then
	    // scalar := - F.1 * gram[2,2] / Trace(F.1);
	    scalar := - F.1 * gram[2,2] / (F.1 + alpha(F.1)); 
	else
	    scalar := -gram[2,2] / 2;
	end if;

	// Clear the (2,2)-entry in the Gram matrix.
	AddRow(~basis, scalar, 1, 2);
        AddColumn(~gram, alpha(scalar), 1, 2);
	AddRow(~gram, scalar, 1, 2);

	// Clear the remaining entries in the Gram matrix.
	for i in [3..dim] do
		// Clear first row/column.
		scalar := -gram[1,i];
                AddRow(~basis, alpha(scalar), 2, i);
		AddColumn(~gram, scalar, 2, i);
                AddRow(~gram, alpha(scalar), 2, i);

		// Clear second row/column.
		scalar := -gram[2,i];
                AddRow(~basis, alpha(scalar), 1, i);
		AddColumn(~gram, scalar, 1, i);
                AddRow(~gram, alpha(scalar), 1, i);
	end for;

	// Make sure we haven't made any mistakes.
        assert basis * originalGram * Transpose(alpha(basis)) eq gram;

	return gram, basis;
end function;

function HyperbolizeForm(M, alpha)
	// Verify that the supplied matrix has the proper credentials and save
	//  some of its properties for later use.
        F, V, char, dim := VerifyMatrix(M, alpha);

	// Find an isotropic vector if one exists.
        found, vec := FindIsotropicVector(M, alpha);

        if not found then
	  assert dim eq 1;
          // Change of basis matrix realizing the isometry.
	  basis := Id(GL(V));

	  // Make a copy of the Gram matrix.
	  gram := M;
          d := getNormRoot(M[1,1], alpha);
          MultiplyRow(~basis, alpha(1/d), 1);
	  MultiplyColumn(~gram, 1/d, 1);
          MultiplyRow(~gram, alpha(1/d), 1);

          return gram, basis;
	end if;

	// The reflexive form.
        Q := HermitianForm(M, alpha);

	// Make sure the vector we found is isotropic.
        assert Evaluate(Q, Eltseq(vec) cat Eltseq(alpha(vec))) eq 0;

	// Attempt to split a hyperbolic plane from the form.
        gram, basis := SplitHyperbolicPlane(M, alpha, vec);

	// Determine how many dimensions we need to split off.
	lowerDim := gram[1] eq Zero(V) select 1 else 2;

	if dim ge lowerDim + 1 then
		// Split the hyperbolic plane from the form.
	        subM := Submatrix(gram, [lowerDim+1..dim], [lowerDim+1..dim]);

		// Iterate on the space orthogonal to the hyperbolic plane we
		//  just split off.
		subGram, subBasis :=
		  HyperbolizeForm(subM, alpha);

		// Superimpose the lower-dimensional Gram matrix onto the
		//  original Gram matrix.
		gram := InsertBlock(gram, subGram, lowerDim+1, lowerDim+1);

		// Lift the subBasis to a higher-dimensional basis so that it
		//  preserves the previously computed bases.
		newBasis := Id(GL(V));
		newBasis :=
			InsertBlock(newBasis, subBasis, lowerDim+1, lowerDim+1);
                basis := newBasis * basis;
	end if;

	return gram, basis;
end function;

intrinsic Decompose(M::ModMatFldElt[FldFin], alpha::FldAut
		: BeCareful := true)
	-> AlgMatElt[FldFin], AlgMatElt[FldFin]
{ Decomposes the supplied hermitian form into a standard form and returns the
change-of-basis matrix which performs this transformation. }
	// Convert the matrix into a different form.
	M := Matrix(BaseRing(M), Nrows(M), Ncols(M), Eltseq(M));

	// Return the decomposition.
        return Decompose(M, alpha
		: BeCareful := BeCareful);
end intrinsic;

intrinsic Decompose(M::AlgMatElt[FldFin], alpha::FldAut
		: BeCareful := true)
	-> AlgMatElt[FldFin], AlgMatElt[FldFin]
{ Decomposes the supplied hermitian form into a standard form and returns the
change-of-basis matrix which performs this transformation. }
	// Verify that the matrix has proper credentials and save some of its
	//  properties for later.
        F, V, char, dim := VerifyMatrix(M, alpha);

	// Decompose the matrix into hyperbolic planes as much as possible.
        gram, basis := HyperbolizeForm(M, alpha);

        // verifying we are correct
	temp1 := gram;
	temp2 := M;

	// Verify that the bilinear forms are similar.
        assert basis * temp2 * Transpose(alpha(basis)) eq temp1;

	// Let's bubble the basis vectors which belong to the radical to the
	//  end of the basis list.
	rad := 0;
	pos := dim;
	while pos ge 1 do
		if gram[pos] eq Zero(V) then
			rad +:= 1;
			for i in [pos+1..dim] do
				SwapRows(~basis, i-1, i);
				SwapColumns(~gram, i-1, i);
				SwapRows(~gram, i-1, i);
			end for;
		end if;
		pos -:= 1;
	end while;

	// Let's put the hyperbolic planes in our standard antidiagonal form.

	// The upper index of the hyperbolic space.
	upper := dim+1-rad;
	repeat upper -:= 1;
	until upper lt 1 or gram[upper,upper] eq 0;

	// Indices of the basis vectors we'll be swapping.
	i := 1;
	j := upper - 1;

	// Keep swapping basis vectors until j is less than or equal to i. Note
	//  that if there are no hyperbolic planes, this does nothing.
	while i lt j do
		SwapRows(~basis, i, j);
		SwapColumns(~gram, i, j);
		SwapRows(~gram, i, j);

		i +:= 2; j -:= 2;
	end while;

        // !!! TODO : Verify whether we need to also apply alpha to the result

	// Since we did everything with row vectors, we need to transpose the
	//  basis, so that the subsequent code that utilizes it doesn't break.
	return gram, Transpose(basis);
end intrinsic;


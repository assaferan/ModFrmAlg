//freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: linalg.m (Linear Algbera)

   Implementation file for useful linear algebra functions.

   !!! TODO : move to the utils folder

   04/01/20 : Started preparation to adjust for arbitrary characteristic.
              Not much of a change yet.

   03/26/20 : Added documentation to this file.

   03/26/20 : Fixed bug in Decompose - Optimized Representation only eats 
              absolute fields. (over the rationals)
 
 ***************************************************************************/

// import "../utils/helper.m" : MVM;

function Decompose(T, t)
    // The characteristic polynomial of this matrix.
    chi := CharacteristicPolynomial(T);
    
    // Factorization of the characteristic polynomial.
    fs := Factorization(chi);

    // The eigenspaces arising from this matrix.
    spaces := [* *];

    for data in fs do
	// Number field associated to one of the irreducible factors.
	// TODO: Fix this. Sometimes crashes.
	//K := NumberField(ChangeRing(data[1], Rationals()));
	//K := NumberField(data[1]);
	K := ext< BaseRing(data[1]) | data[1] >;
	// TODO: Keep an eye out for this, make sure it works.
	
	// The eigenvalue associated to this factor.
	if Degree(data[1]) eq 1 then
	    eig := -Evaluate(data[1], 0);
	else
	    eig := K.1;
	end if;

	// If the field K is not the rationals, try to optimize it as
	//  long as the degree of the field isn't too large.
	if Category(K) notin [FldRat,FldFin] and Degree(K) le 8 then
	    // Optimize the number field.
	    K, map := OptimizedRepresentation(AbsoluteField(K));
	    
	    // The eigenvalue in the new field.
	    eig := map(eig);
	end if;
	
	// The identity matrix of the appropriate dimension.
	id := Id(MatrixRing(K, Nrows(t)));
	
	// Promote the ambient matrix to the current number field.
	tt := ChangeRing(t, K);
	
	// Add eigenspace to the list of spaces and flag it depending
	//  on whether this eigenspace is irreducible.
	// !!! Problem - over finite field we might have generalized eigenspaces.
	// probably have to replace by another decomposition function...
	
	if Characteristic(BaseRing(T)) eq 0 then
	    // fa := data[1];
	    fT := tt-eig*id;
	else
	    //	    fa := data[1]^data[2];
	    fT := (tt-eig*id)^data[2];
	end if;
//	fT := Evaluate(fa, tt);

	Append(~spaces,
//	       	       < Nullspace(Transpose(tt)-eig*id), data[2] eq 1 >);
	       < Nullspace(fT), data[2] eq 1 >);
    end for;
    
    return spaces;
end function;

intrinsic EigenspaceDecomposition(array::Assoc : Warning := true)
	-> List, SeqEnum
{ Decompose an array of mutually commuting matrices into their eigenspaces. }
  // Make sure that the associative array is non-empty.
  require #array ne 0: "Associative array must not be empty.";

  // Extract the keys associated to the associative array.
  keys := Keys(array);

  // Put keys into an enumerative array.
  keys := [ x : x in keys ];

  // Extract the full list of matrices.
  Ts := [ array[x] : x in keys ];

  // Verify that all matrices mutually commute.
  require &and[ A*B eq B*A : A,B in Ts ]:
	"Matrices in array do not mutually commute.";

  // List of eigenspaces for the first matrix.
  sp := Decompose(Ts[1], Ts[1]);

  for idx in [2..#Ts] do
      // If all eigenspaces are irreducible, we're done.
      if &and[ data[2] : data in sp ] then break; end if;
      
      // The number of eigenspaces we are starting with.
      num := #sp;
      
      // Keep track of the eigenspaces we'll need to delete.
      delList := [];
      
      for i in [1..num] do
	  // Skip this eigenspace if it is irreducible.
	  if sp[i][2] then continue; end if;
	  
	  // Add the current eigenspace to the delete list.
	  Append(~delList, i);
	  
	  // The current subspace.
	  space := sp[i][1];

	  // something here doesn't look right - maybe it only works in characteristic 0 ?
	  // In any case the resulting matrix T is not the submatrix associated to this subspace
	  
	  
	  // Dimension of this space.
	  dim := Dimension(space);
/*	  
	  // The basis of this space.
	  basis := Basis(space);
	  
	  // The pivots for this space.
	  pivots := [ 0 : v in basis ];
	  for j in [1..#basis] do
	      repeat pivots[j] +:= 1;
	      until basis[j][pivots[j]] ne 0;
	  end for;

	  // Modify the base ring in preparation for matrix-
	  //  vector multiplication.
	  tempT := ChangeRing(Ts[idx], BaseRing(space));
	  
	  // Form a "tall" matrix which corresponds to the column
	  //  vectors AFTER we act tempT upon the eigenbasis.
	  T := Transpose(Matrix([ Eltseq(MVM(tempT, v))
				  : v in basis ]));
	  
	  // Extract the submatrix associated to this subspace.
	  T := Submatrix(T, pivots, [1..dim]);
*/
	  

	  B := BasisMatrix(space);
	  tempT := ChangeRing(Ts[idx], BaseRing(space));
	  T := Matrix(B*tempT*Transpose(B)*(B * Transpose(B))^(-1));
	  
	  
	  // Compute the eigenspaces associated to T.
	  newSpaces := Decompose(T, Ts[idx]);
	  
	  for newSp in newSpaces do
	      // The field over which both spaces live.
	      if Type(BaseRing(space)) eq FldFin then
		  deg := LCM(Degree(BaseRing(space)),
			     Degree(BaseRing(newSp[1])));
		  F := FiniteField(
			       Characteristic(BaseRing(space)), deg);
	      else
		  F := Compositum(
			       BaseRing(newSp[1]), BaseRing(space));
	      end if;
	      
	      // Compute the intersection of these two spaces
	      //  and add it to the list.
	      Append(~sp, < ChangeRing(newSp[1], F)
				      meet ChangeRing(space, F), newSp[2] >);
	  end for;
      end for;

      // Remove the outdated subspaces from last to first.
      sp := [* sp[i] : i in [1..#sp] | not i in delList *];
      
      assert &+[ Dimension(s[1]) * Degree(BaseRing(s[1])) : s in sp ]
	     eq Nrows(Ts[1]) * Degree(BaseRing(Ts[1]));
  end for;

  // Determine whether this decomposition is stll decomposable.
  decomposable := [ i : i in [1..#sp] | not sp[i][2] ];
  
  // Return the eigenspaces.
  sp := [* data[1] : data in sp *];

  // Display a warning if the decomposition is reducible.
  if Warning and #decomposable ne 0 then
      print "WARNING: Eigenspaces not completely decomposed!";
  end if;

  return sp, decomposable;
end intrinsic;


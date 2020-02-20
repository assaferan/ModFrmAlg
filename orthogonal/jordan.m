// Jordan decomposition.

forward initJordan;

function StepOne(gram, p)
	// The dimension of the space under consideration.
	dim := Nrows(gram);

	// If this is a 1-dimensional lattice, return.
	if dim eq 1 then return 1,1; end if;

	// Set the minimal valuation as the first element to get us started.
	min := Valuation(gram[1,1], p);
	i := 1; j := 1;

	// Look down the diagonal first.
	for n in [2..dim] do
		// The valuation of the current element.
		val := Valuation(gram[n,n], p);

		// Update minimum and location if we find a new minimum.
		if val lt min then
			min := val;
			i := n; j := n;
		end if;
	end for;

	// Check the off-diagonal, keeping the row as small as possible.
	for n in [1..dim-1], m in [n+1..dim] do
		// The valuation.
		val := Valuation(gram[n,m], p);

		// Update if smaller order element found.
		if val lt min then
			min := val;
			i := n; j := m;
		end if;
	end for;

	return i, j;
end function;

function SplitLattice(gram, p, i, j)
	// The dimension of the space under consideration.
	dim := Nrows(gram);

	// A convenience for constructing vectors.
	V := VectorSpace(BaseRing(gram), dim);

	// If this is a 1-dimensional space, return the only value.
	if dim eq 1 then return Matrix(V.1), [1]; end if;

	// Is this a dyadic completion?
	even := IsEven(Characteristic(ResidueClassField(p)));

	if i eq j or not even then
		m := 2;

		// Choose the appropriate vector to split off in the odd
		//  characteristic case.
		if i eq j then
			newBasis := [ V.i ];
		else
			newBasis := [ V.i + V.j ];
		end if;

		// Split off the i-th basis vector.
		for k in [ x : x in [1..dim] | x ne i ] do
			Append(~newBasis, V.k - (gram[i,k]/gram[i,i]) * V.i);
		end for;
	else // We may assume that i ne j and that p has even characteristic.
		m := 3;

		// A uniformizer.
		pi := SafeUniformizer(p);

		// Valuation of the minimal such element in the Gram matrix.
		v := Valuation(gram[i,j], p);

		// A p-adic unit measuring how close gram[i,j] is to pi^v.
		c := pi^v / gram[i,j];

		// The basis we wish to split off.
		newBasis := [ c * V.i, V.j ];

		// Compute the inner product with respect to these vectors.
		mat := Matrix(newBasis);
		T := mat * gram * Transpose(mat);

		// The determinant of this block.
		d := Determinant(T);

		// Split off the 2-dimensional block.
		for k in [ x : x in [1..dim] | x ne i and x ne j ] do
			// Convenience coefficients.
			t := T[1,2] * gram[j,k] - T[2,2] * c * gram[i,k];
			u := T[1,2] * c * gram[i,k] - T[1,1] * gram[j,k];

			// Add the new vector to the basis.
			Append(~newBasis, V.k + (t*c/d)*V.i + (u/d)*V.j);
		end for;
	end if;

	// Turn the new basis into a matrix.
	newBasis := Matrix(newBasis);

	// Compute the new Gram matrix.
	newGram := newBasis * gram * Transpose(newBasis);

	// Verify that we've established a valid splitting.
	assert &and[ newGram[i,j] eq 0 : i in [1..m-1], j in [m..dim] ];

	// Split off the piece we already computed.
	newGram := Submatrix(newGram, [m..dim], [m..dim]);

	// If the current basis is its own indecomposable lattice, return.
	if Nrows(newGram) eq 0 then return newBasis, [ m-1 ]; end if;

	// The basis coming from the split off submatrix.
	inductBasis, dimSeq := initJordan(newGram, p);

	// Keep track of the dimension sequences.
	dimSeq := [ m-1 ] cat dimSeq;

	// An identity matrix upon which we will paste the induction basis.
	basis := DiagonalMatrix([ BaseRing(newGram)!1^^dim ]);

	// Paste the induction basis.
	InsertBlock(~basis, inductBasis, m, m);

	// Change the basis accordingly.
	newBasis := basis * newBasis;

	return newBasis, dimSeq;
end function;

function initJordan(gram, p)
	// Find the coordinate of a nonzero element with least p-adic order.
	row, col := StepOne(gram, p);

	// Split off an appropriate block.
	return SplitLattice(gram, p, row, col);
end function;

function interpret(array, pR, inner : MaxSplit := false)
	// Return value sequences. These will be populated before returned.
	ords := []; bases := [];

	// Build an associative array where we'll append each block to a master
	//  list whose index depends upon the p-adic order of the block.
	if not MaxSplit then blockArray := AssociativeArray(); end if;

	for elt in array do
		// Turn the block basis into a matrix.
		basis := Matrix(elt);

		// Compute its Gram matrix.
		gram := basis * inner * Transpose(basis);

		// The dimension of this block.
		dim := Nrows(gram);

		// Compute the discriminant of the block. Note: we do not
		//  compute its half-discriminant, since this will not affect
		//  the order over non-dyadic fields, yet WILL affect the order
		//  over dyadic fields.
		// TODO: Hmmm. Be a bit more careful here... perhaps?
		d := Determinant(gram) /(dim eq 1 select 2 else 1);

		// Determine the p-adic order of the modular component.
		ord := Valuation(d, pR) / (dim eq 1 select 1 else 2);
		ord := Integers()!ord;

		if not MaxSplit then
			// Retrieve the current basis array if assigned.
			if IsDefined(blockArray, ord) then
				temp := blockArray[ord];
			else
				temp := [];
			end if;

			// Reassign the value of this constituent by appending
			//  the new basis elements to the list.
			blockArray[ord] := temp cat elt;
		else
			// Add this atomic block to the basis list.
			Append(~ords, ord);

			// Add the order of this block to the list.
			Append(~bases, elt);
		end if;
	end for;

	if not MaxSplit then
		// The sorted constituent orders.
		ords := Keys(blockArray);
		ords := Sort([ x : x in ords ]);

		// Build the constituent basis entries.
		for ord in ords do Append(~bases, blockArray[ord]); end for;
	end if;

	return bases, ords;
end function;

intrinsic JordanDecomp(L::ModDedLat, pR::RngOrdIdl : MaxSplit := false)
	-> SeqEnum
{ Computes the local Jordan decomposition at a prime. }
	// Verify that the ideal is prime.
	require IsPrime(pR): "Specified ideal must be prime.";

	// The inner form.
	innerForm := InnerForm(QuadraticSpace(L));

	if IsDefined(L`Jordan, pR) then
		return interpret(L`Jordan[pR], pR, innerForm
			: MaxSplit := MaxSplit);
	end if;

	// A local uniformizer.
	pi := SafeUniformizer(pR);

	// A local basis for the completed lattice.
	locBasis := Matrix([ pi^Valuation(pb[1],pR) * pb[2]
		: pb in PseudoBasis(L) ]);

	// The local Gram matrix.
	locGram := locBasis * innerForm * Transpose(locBasis);

	// Get the Jordan basis.
	jordanBasis, dimSeq := initJordan(locGram, pR);

	// Partition the Jordan basis into respective blocks.
	blockBases := Partition(Rows(jordanBasis), dimSeq);

	// Assign the Jordan decomposition.
	L`Jordan[pR] := blockBases;

	return interpret(blockBases, pR, innerForm : MaxSplit := MaxSplit);
end intrinsic;

intrinsic JordanDecomp(L::ModDedLat, pR::RngInt : MaxSplit := false)
	-> SeqEnum
{ Computes the local Jordan decomposition at a prime. }
	return JordanDecomp(L, Norm(pR) : MaxSplit := MaxSplit);
end intrinsic;

intrinsic JordanDecomp(L::ModDedLat, p::RngIntElt : MaxSplit := false)
	-> SeqEnum
{ Computes the local Jordan decomposition at a prime. }
	return JordanDecomp(L, ideal< BaseRing(L) | p >
		: MaxSplit := MaxSplit);
end intrinsic;

intrinsic JordanDecomp(L::Lat, p::RngIntElt : MaxSplit := false) -> SeqEnum
{ Computes the local Jordan decomposition at a prime. }
	// Convert the native Lat object to a ModDedLat object.
	L := LatticeFromLat(L);

	// Convert the integer prime to an ideal over the base ring.
	pR := ideal< BaseRing(L) | p >;

	// Pass to the master routine.
	return JordanDecomp(L, pR : MaxSplit := MaxSplit);
end intrinsic;


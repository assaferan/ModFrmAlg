// Implementation for computing Hecke matrices over the rationals.

import "inv-QQ.m" : Invariant;
import "neighbor-QQ.m" : BuildNeighborProc, BuildNeighbor,
	GetNextNeighbor;
import "hecke-QQ.m" : HeckeOperatorTrivialWeightQQ;

function getIndices(M, dim)
	// Retrieve the Hecke eigenforms for this space.
	fs := HeckeEigenforms(M);

	// Prioritize the isometry class indices which allow us to reconstruct
	//  the Hecke matrix from a single list of neighbors.
	good := [ i : i in [1..dim]
		| &*[ Eltseq(f`vec)[i] eq 0 select 0 else 1 : f in fs ] eq 1 ];

	// Return a full list of indices in the order we will compute.
	return good cat [ i : i in [1..dim] | not i in good ];
end function;

function HeckeOperatorTrivialWeightFastQQ(M, p, k
		: BeCareful := true, Estimate := false, UseLLL := true)
	// The dimension of the Hecke matrix.
	dim := #M`genus`Representatives;

	// Initilize the Hecke matrix.
	column := [ Vector([ 0^^dim ]) : i in [1..dim] ];

	// An associative array indexed by a specified invariant of an isometry
	//  class. This data structure allows us to bypass a number of isometry
	//  tests by filtering out those isometry classes whose invariant
	//  differs from the one specified.
	invs := M`genus`RepresentativesAssoc;

	// The isometry class representatives of the genus.
	Ls := GenusReps(M);

	// An ordered list of to compute.
	indices := getIndices(M, dim);

	for ind in [1..#indices] do
		// The current index.
		n := indices[ind];

		// Routine for estimating the amount of time it will take to
		//  compute this Hecke operator.
		if M`L`quadSpace`dim eq 5 then
			// TODO: Replace this with a more general formula.
			if k eq 1 then
				fullCount := p^3 + p^2 + p + 1;
			else
				fullCount := p * (p^3 + p^2 + p + 1);
			end if;

			// Counter for keeping track of the number of neighbors
			//  we've computed so far.
			count := 0;

			// The time for starting our realtime estimate.
			start := Realtime();
		elif M`L`quadSpace`dim eq 3 then
			fullCount := p + 1;
			count := 0;
			start := Realtime();
		end if;

		printf "Computing %o%o-neighbors for isometry class "
			cat "representiative #%o...\n", p,
			k eq 1 select "" else "^" cat IntegerToString(k), n;

		// Build neighboring procedure for this lattice.
		nProc := BuildNeighborProc(Ls[n], p, k
			: BeCareful := BeCareful);

		while nProc`isoSubspace ne [] do
			// Build the neighbor lattice corresponding to the
			//  current state of nProc.
			nLat := BuildNeighbor(nProc
				: BeCareful := BeCareful, UseLLL := UseLLL);

			// Increment counter.
			if Estimate then count +:= 1; end if;

			// Compute the invariant for this neighbor lattice.
			inv := Invariant(nLat);

			// Retrieve the array of isometry classes matching this
			//  invariant.
			array := invs[inv];

			// Isometry testing is only necessary if the array has
			//  length larger than 1.
			if #array ne 1 then
				// Flag to determine whether an isometry class
				//  was actually found. This is a failsafe.
				found := false;

				for j in [1..#array] do
					// Check for isometry.
					iso := IsIsometric(nLat, array[j][1]);

					// If isometric, flag as found,
					//  increment Hecke matrix, and move on.
					if iso then
						found := true;
						column[n][array[j][2]] +:= 1;
						continue;
					end if;
				end for;

				// Verify that the neighbor was indeed isometric
				//  to something in our list.
				assert found;
			else
				// Array length is one, and therefore conclude
				//  that nLat is isometric to the only entry in
				//  the array.
				column[n][array[1][2]] +:= 1;
			end if;

			if Estimate and count mod 1000 eq 500 then
				elapsed := Realtime() - start;
				t := RealField()!(elapsed / count);
			end if;

			if Estimate and count mod 1000000 eq 3000 then
				// Elapsed real time.
				elapsed := Realtime() - start;

				// Seconds per neighbor computation.
				t := RealField()!(elapsed / count);

				// Number of neighbors left to compute.
				remaining := fullCount - count;

				// Estimate time remaining (in seconds).
				estimate := t * remaining;

				// Minutes remaining.
				mins := Floor(estimate / 60);

				// Seconds (modulo minutes) remaining.
				secs := Floor(estimate - mins*60);

				// Hours remaining.
				hours := Floor(mins / 60);

				// Minutes (modulo hours) remaining.
				mins -:= hours * 60;

				// Days remaining.
				days := Floor(hours / 24);

				// Hours (modulo days) remaining.
				hours -:= days * 24;

				// Display estimate.
				printf "Estimated time remaining for T_%o^%o:"
					cat " %od %oh %om %os\n",
					Norm(p), k, days, hours, mins, secs;
			end if;

			// Update nProc in preparation for the next neighbor
			//  lattice.
			nProc := GetNextNeighbor(nProc
				: BeCareful := BeCareful);
		end while;

/*	if n eq 1 then
		column[1] := Vector([ 1200, 4704, 4320, 3744, 5184, 13536, 13248, 9408, 23040, 7104, 4032, 2544, 13248, 29952, 9408, 8256, 15264, 6048, 13536, 12096, 9600, 7104, 13536, 23616, 6336, 11520, 8064, 2496, 6192, 2496, 1728 ]);
	elif n eq 2 then
		column[2] := Vector([ 1176, 4164, 4500, 4032, 4272, 14004, 11916, 9144, 25392, 8184, 4308, 2328, 12816, 26100, 9504, 8796, 13320, 5844, 12192, 11676, 8904, 8424, 12156, 25908, 8604, 12096, 8832, 2160, 6948, 2256, 2604 ]);
	end if;*/

		// We will now recover the entire Hecke operator from the data
		//  we just computed by using some tricks involving the
		//  structure of the Hecke operators as well as some linear
		//  algebra.
		printf "Attempting to build Hecke matrix (attempt #%o)... ",
			ind;

		// The number of initial free variables.
		freevars := Binomial(dim - ind + 1, 2) - (dim - ind);

		// The polynomial ring under consideration.
		Z := PolynomialRing(Rationals(), freevars);

		// We now construct the entire Hecke operator from the first
		//  column.
		hecke := Zero(MatrixRing(Z, dim));

		// The sizes of the automorphism groups.
		aut := [ #AutomorphismGroup(L) : L in M`genus`Representatives ];

		// Fill in the entries from the values we've already computed.
		for j in indices[1..ind] do
			for i in [1..dim] do
				hecke[j,i] := column[j][i];
				hecke[i,j] := aut[i] / aut[j] * column[j][i];
			end for;
		end for;

		// Count the number of neighbors computed.
		neighbors := &+Eltseq(column[n]);

		// Let's fill out the hecke matrix first.
		kk := 0;
		for i in [1..dim] do
			// Skip the indices we've already computed.
			if i in indices[1..ind] then continue; end if;

			for j in [i+1..dim] do
				// Skip the indices we've already computed.
				if j in indices[1..ind] then continue; end if;

				kk +:= 1;
				hecke[i,j] := Z.kk;
				hecke[j,i] := aut[j] / aut[i] * Z.kk;
			end for;
		end for;

		// Need to fill in the diagonal entries so that the row sums
		//  match.
		rows := Rows(hecke);
		for i in [1..dim] do
			// Skip the indices we've already computed.
			if i in indices[1..ind] then continue; end if;

			hecke[i,i] := neighbors - &+Eltseq(rows[i]);
		end for;

		// Now we transpose so that column sums are constant.
		hecke := Transpose(hecke);

		// If the dimension of the Hecke operator is 1 or 2, then we
		//  don't need to do any extra work.
		if dim le 2 then return ChangeRing(hecke, Integers()); end if;

		// Retrieve a Hecke operator that has already been computed.
		T := ChangeRing(HeckeOperators(M)[1], Z);

		// The commutator matrix must be zero, so we end up with
		//  additional linear relations that need to be resolved.
		comm := hecke * T - T * hecke;

		// The distinct linear relations.
		list := Set([ Normalize(x) : x in Eltseq(comm) | x ne 0 ]);

		// A list of lists that will be turned into a matrix encoding
		//  the linear relations we seek.
		mat := [];

		for x in list do
			// The list of coefficients of each term.
			c := Coefficients(x);

			// The monomials associated to each coefficient above.
			m := Monomials(x);

			// A sequence of coefficnets.
			coeff := [ Rationals()!0^^(freevars+1) ];

			// A pointer to the current term we're considering.
			ptr := 1;
			for i in [1..freevars] do
				if ptr le #m and m[ptr] eq Z.i then
					// Update the coefficients and move on.
					coeff[i] := c[ptr];
					ptr +:= 1;
				end if;
			end for;

			// Include the constant coefficient.
			coeff[freevars+1] := -Evaluate(x, [ 0^^freevars ]);

			// Add coefficients to our list.
			Append(~mat, coeff);
		end for;

		if #mat ne 0 then
			// Construct a matrix from the coefficients we extracted
			//  from the relation.
			mat := Matrix(mat);

			// Compute the echelon form of this matrix.
			mat := EchelonForm(mat);

			// Extract the nonzero rows from this matrix.
			mat := Matrix([ row :
				row in Rows(mat) | not IsZero(row) ]);

			if #Rows(mat) eq freevars then
				print "Success!";
				// The values of the free variables.
				evs := Rows(Transpose(mat))[freevars+1];
				return ChangeRing(Evaluate(hecke, Eltseq(evs)),
					Integers());
			else
				print "Failed!";
			end if;
		end if;
	end for;

	print "Testing...";
	return HeckeOperatorTrivialWeightQQ(M, p, k : BeCareful := BeCareful,
		Estimate := Estimate, UseLLL := UseLLL);
end function;


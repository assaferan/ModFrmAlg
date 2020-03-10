// Scripts for computing isotropic line orbits under the automorphism group.

declare attributes ModTupFld: parent, rank;

intrinsic Orbits(V::ModTupFld[FldFin], G::GrpMat[FldFin]) -> SeqEnum
{ Computes orbits of isotropic lines. }
	// Verify that the base rings agree.
	require BaseRing(V) eq BaseRing(G): "Base fields must agree.";

	// Retrieve all isotropic lines and store them in memory.
	list := AllIsotropicSubspaces(V, 1);

	// Set up the appropriate data structure so we can apply union-find.
	for i in [1..#list] do
		list[i]`rank := 0;
		list[i]`parent := list[i];
	end for;

	// Retrieve the generators of the automorphism group.
	gs := Generators(G);

	// This function establishes the parent node of all elements in the
	//  partition to an element of least rank.
	function find(x)
		if x`parent ne x then
			x`parent := find(x`parent);
		end if;
		return x`parent;
	end function;

	// Merge sets which are in the same equivalance class. We do this by
	//  establishing the parent (found with `find' above) for all elements
	//  in the partition.
	procedure union(x,y)
		xRoot := find(x);
		yRoot := find(y);
		if xRoot eq yRoot then return; end if;

		if xRoot`rank lt yRoot`rank then
			xRoot`parent := yRoot;
		elif xRoot`rank gt yRoot`rank then
			yRoot`parent := xRoot;
		else
			yRoot`parent := xRoot;
			xRoot`rank := xRoot`rank + 1;
		end if;
	end procedure;

	// Apply the generators of the automorphism group to each subspace.
	for x in list do
		for g in gs do
			S := sub< V | x.1 * g >;
			idx := Index(list, S);
			union(x, list[idx]);
		end for;
	end for;

	// Generate an empty associative array.
	O := AssociativeArray();

	// Populate the associative array, keeping track of how many orbits are
	//  in each partition.
	for x in list do
		if not IsDefined(O, x`parent) then
			O[x`parent] := 1;
		else
			O[x`parent] +:= 1;
		end if;
	end for;

	// Prepare the data to be returned to the user.
	array := [];
	keys := Keys(O);
	for x in keys do
		x.1, O[x];
		Append(~array,
			< sub< V | x.1 * Transpose(V`Basis^-1) >, O[x] >);
	end for;

	array;

	return array;
end intrinsic;


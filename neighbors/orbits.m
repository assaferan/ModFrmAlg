freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: orbits.m (Scripts for computing isotropic line 
   	 	  	   orbits under the automorphism group.)

   05/04/20: started documentation. Added tracking of isometries, in order to
             support using orbits with non-trivial weights.
             Modified IsotropicOrbits to return the coset representatives.
 
****************************************************************************/


declare attributes ModTupFld: parent, rank, isom;

intrinsic IsotropicOrbits(V::ModTupFld[FldFin], G::GrpMat[FldFin],
						   k::RngIntElt) -> SeqEnum
{ Computes orbits of isotropic lines. }
	// Verify that the base rings agree.
	require BaseRing(V) eq BaseRing(G): "Base fields must agree.";

	// Retrieve all isotropic lines and store them in memory.
	list := AllIsotropicSubspaces(V, k);

	// Set up the appropriate data structure so we can apply union-find.
	for i in [1..#list] do
		list[i]`rank := 0;
		list[i]`parent := list[i];
		list[i]`isom := G!1;
	end for;

	// Retrieve the generators of the automorphism group.
	gs := Generators(G);

	gs := gs join {g^(-1) : g in gs};

	// This function establishes the parent node of all elements in the
	//  partition to an element of least rank.
	function find(x)
	    if x`parent ne x then
		x`parent, isom := find(x`parent);
		x`isom := isom * x`isom;
	    end if;
	    return x`parent, x`isom;
	end function;

	// Merge sets which are in the same equivalance class. We do this by
	//  establishing the parent (found with `find' above) for all elements
	//  in the partition.
	// TODO : This union-find is not very efficient...
	// Implement an efficient version
	procedure union(x,y,g)
	    xRoot, xIsom := find(x);
	    yRoot, yIsom := find(y);
	    if xRoot eq yRoot then return; end if;

	    if xRoot`rank lt yRoot`rank then
		xRoot`parent := yRoot;
		xRoot`isom := yIsom * g^(-1) * xIsom^(-1);
	    elif xRoot`rank gt yRoot`rank then
		yRoot`parent := xRoot;
		yRoot`isom := xIsom * g * yIsom^(-1);
	    else
		yRoot`parent := xRoot;
		yRoot`isom := xIsom * g * yIsom^(-1);
		xRoot`rank := xRoot`rank + 1;
	    end if;
	end procedure;

        rev_lookup := AssociativeArray();
        for i in [1..#list] do
	  rev_lookup[list[i]] := i;
        end for;
	// Apply the generators of the automorphism group to each subspace.
	for x in list do
	    for g in gs do
		gens := [ b * g : b in Basis(x)];
		// S := sub< V | x.1 * g >;
		S := sub< V | gens >;
// idx := Index(list, S);
                idx := rev_lookup[S];
		union(x, list[idx], g);
	    end for;
	end for;

	// Generate an empty associative array.
	O := AssociativeArray();

	// Populate the associative array, keeping track of how many orbits are
	//  in each partition.
	for x in list do
	    if not IsDefined(O, x`parent) then
		//O[x`parent] := 1;
		O[x`parent] := [x`isom];
	    else
		//O[x`parent] +:= 1;
		O[x`parent] := O[x`parent] cat [x`isom];
	    end if;
	end for;

	// Prepare the data to be returned to the user.
	array := [];
	keys := Keys(O);
	for x in keys do
	    // x.1, O[x];
	    gens := [ b * Transpose(V`Basis^-1) : b in Basis(x) ];
	    Append(~array,
//			< sub< V | x.1 * Transpose(V`Basis^-1) >, O[x] >);
		   < sub< V | gens >, O[x] >);
	end for;

	// array;

	return array;
end intrinsic;


freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
               E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch          
                                                                            
   FILE: orbits.m (Scripts for computing isotropic line 
   	 	  	   orbits under the automorphism group.)

   05/04/20: started documentation. Added tracking of isometries, in order to
             support using orbits with non-trivial weights.
             Modified IsotropicOrbits to return the coset representatives.
 
****************************************************************************/

// Here are the intrinsics this file defines
// IsotropicOrbits(V::ModTupFld, G::GrpMat, k::RngIntElt) -> SeqEnum

//imports
import "../utils/helper.m" : printEstimate;

declare attributes ModTupFld: parent, rank, isom;

// We want to pass the original group (not its reduction) to be able to
// write the isometries more easily in the hecke operator
// intrinsic IsotropicOrbits(V::ModTupFld[FldFin], G::GrpMat[FldFin],
intrinsic IsotropicOrbits(V::ModTupFld[FldFin], G::GrpMat,
			  k::RngIntElt, proj::Map : Estimate := true) -> SeqEnum
{ Computes orbits of isotropic lines. }
	// Verify that the base rings agree.
//	require BaseRing(V) eq BaseRing(G): "Base fields must agree.";

	// Retrieve all isotropic subspaces and store them in memory.
        list := AllIsotropicSubspaces(V, k : Estimate := Estimate);

        total := #list;
        count := 0;
        elapsed := 0;
        start := Realtime();
	// Set up the appropriate data structure so we can apply union-find.
	for i in [1..#list] do
	   list[i]`rank := 0;
	   list[i]`parent := list[i];
	   list[i]`isom := G!1;
           if Estimate then
              printEstimate(start, ~count, ~elapsed, total,
			    "union-find initialization" :
			    printSkip := 10^6, printOffset := 5*10^5);
            end if;
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

        count := 0;
        elapsed := 0;
        start := Realtime();
        rev_lookup := AssociativeArray();
        for i in [1..#list] do
	  rev_lookup[list[i]] := i;
          if Estimate then
              printEstimate(start, ~count, ~elapsed, total,
			    "building reverse lookup" :
			    printSkip := 10^6, printOffset := 5*10^5);
          end if;
        end for;

        count := 0;
        elapsed := 0;
        start := Realtime();
	// Apply the generators of the automorphism group to each subspace.
	for x in list do
	  for g in gs do
		gens := [ b * proj(g) : b in Basis(x)];
		// S := sub< V | x.1 * g >;
		S := sub< V | gens >;
// idx := Index(list, S);
                idx := rev_lookup[S];
		union(x, list[idx], g);
	  end for;
          if Estimate then
              printEstimate(start, ~count, ~elapsed, total,
			    "performing unions" :
			    printSkip := 10^6, printOffset := 5*10^5);
          end if;
	end for;

	// Generate an empty associative array.
	O := AssociativeArray();

        count := 0;
        elapsed := 0;
        start := Realtime();
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
            if Estimate then
              printEstimate(start, ~count, ~elapsed, total,
			    "constructing orbits" :
			    printSkip := 10^6, printOffset := 5*10^5);
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

        vprintf AlgebraicModularForms, 2 :
	  "The orbit lengths are: %o.\n", Sort([#a[2] : a in array]);

        delete keys;
        delete O;
        delete rev_lookup;
        delete list;
	// array;

	return array;
end intrinsic;

// Here we attempt to implemnt better orbit-stabilizer approaches
build_polycyclic_data := function(G, V, proj)
  // This should work, but I am not sure - double check !!!
  // We use the original group to avoid FPGroup
  F := Codomain(proj);
  R := Domain(proj);
  n := Dimension(V);
  gen_imgs := [[proj(x) : x in Eltseq(g)] : g in GeneratorsSequence(G)];
  red := hom<G -> GL(n,F) | gen_imgs>;
  red_G := red(G);
  is_solvable := IsSolvable(red_G);
  if is_solvable then
    G_pc, pi := PCGroup(red_G);
  else
    G_pc := red_G;
    pi := IdentityHomomorphism(red_G);
  end if;
  function g_action(tup)
    x := tup[1];
    g := tup[2];
    // This is because the code below assumes right action
    gens := [ b * (g@@pi) : b in Basis(x)];
    return sub< V | gens>;
  end function;
  return is_solvable, G_pc, g_action, red*pi;
end function;

orb_stab_pc := function(G, f, x)
    relative_orders := PCPrimes(G);
    orbit := {@ Parent(x) | x @};
    stab_gens := [ G | ];
    orbit_nos := [];
    for i := NPCgens(G) to 1 by -1 do
        g := G.i;
        pos := Position(orbit, f(<x, g>));
        orbit_len := #orbit;
        if pos eq 0 then
            for k := 1 to relative_orders[i]-1 do
                for j := 1 to orbit_len do
                    Include(~orbit, f(<orbit[j], g>));
                end for;
                g *:= G.i;
            end for;
            assert #orbit eq orbit_len * relative_orders[i];
            Append(~orbit_nos, i);
        else
            /* move to 0-index arrays for modulo arithmetic */
            pos -:= 1;
            for j := #orbit_nos to 1 by -1 do
                if pos eq 0 then break; end if;
                t := orbit_nos[j];
                orbit_len div:= relative_orders[t];
                pow := pos div orbit_len;
                g *:= G.t^-pow;
                pos -:= pow * orbit_len;
            end for;
            assert f(<x ,g>) eq x;
            Append(~stab_gens, g);
        end if;
    end for;
    stab := sub< G | stab_gens >;
    return orbit, stab, orbit_nos;
end function;

// !! TODO - improve this, we can do better.
// e.g. if an element g has order r, then only divisors of r
// should be considered for the stabilizer
// i.e. if p is the minimal prime dividing r and xg ne x, we can
// add xg^i for all i up to p-1.
// (or rather we can check if each of p^d stabilizes x

// can also save instead of an element of g, only a pointer to
// the previous index and the index of the last generator,
// and in the end unravel these.
orb_stab_general := function(G, f, x)
    gens := Generators(G);
    orbit := {@ Parent(x) | x @};
    stab_gens := [ G | ];
    orbit_nos := [ G | 1 ];
    next_idx := 1;
    while next_idx le #orbit do
      orbit_len := #orbit;
      for gen in gens do
	g := gen;
	next := f(<orbit[next_idx], g>);
	pos := Position(orbit, next);
        // This is the element leading from x to next
        g := orbit_nos[next_idx]*g;
        if pos eq 0 then
	  Include(~orbit, next);
          Append(~orbit_nos, g);
	else
	  // we have found an element of the stabilizer  
	  g *:= orbit_nos[pos]^(-1);
          assert f(<x ,g>) eq x;
          Append(~stab_gens, g);
	end if;
      end for;
      next_idx +:= 1;
    end while;
    stab := sub< G | stab_gens >;
    return orbit, stab, orbit_nos;
end function;

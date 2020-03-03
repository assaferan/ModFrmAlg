//====================
//
// GENERA AND NEIGHBORS
//
// This file contains functions for computing the genera and neighbors for the ModFrmAlg package.
//
// Matthew Greenberg and John Voight, 2012
//
//====================


import "stdbasis.m" : _ppOrthogonalStandardBasis;


//=======
//
// Preliminary functions
//
//=======

function MakeNeighborFromPseudoMatrix(Lambda, pmat);
  Pi := Module(pmat);
  Pi`QuadraticSpace := Lambda`QuadraticSpace;
  Pi`ParentModFrmAlg := Lambda`ParentModFrmAlg;
  return Pi;
end function;


function next_pivots(pivots, twon);
  k := #pivots;
  iterk := k;
  repeat
    if iterk eq 0 then
      return [];
    elif pivots[iterk] lt twon then
      pivots[iterk] +:= 1;
      for i := 1 to k-iterk do
        pivots[iterk+i] := pivots[iterk]+i;
      end for;
      if pivots[k] gt twon then
        iterk -:= 1;
      else
        iterk := k+1;
      end if;
    else
      iterk -:= 1;
    end if;
  until iterk eq k+1;
  return pivots;
end function;

//=======
//
// Neighbors process definition and hackobjs
//
//=======

// Uses GrpFrml in place of something better, for now.

declare attributes GrpFrml:
                   // = Nu, data for the pp-neighbors process.

  Lambda,          
  innerprod, 
  pp,              
  ppinv,
  P,
  Npp,
  pp_list,
  pp_list_mod,
  ZZ_F_pp,
  mpp,

  k,
  ppbasis,
  n,

  pivots,
  data,            // Seq of GrpFrmlElts
  
  ppneighborbasis_std,
  skewspace_index;            

  
declare attributes GrpFrmlElt:
                   // data for the pp-neighbors process.  
                   
  current,         // kth vector of the flag,
                   // a vector which is isotropic and orthogonal to the previous k-1 vectors in the flag,
  type,            // type is either "g" (general), "h" (hyperbolic), or "i" (isotropic):
                   // if type is general, then the pairing between pivot and polar is nonzero;
                   // if type is hyperbolic, then polar is a hyperbolic pair;
                   // if type is isotropic, then the span of pivot and the subspace is totally isotropic.
  pivot,
  polar_index,
  polar_basis,
  subspace_index,
  subspace_basis,
  subspace_dim;

intrinsic HackobjPrintGrpFrml(Nu::GrpFrml, level::MonStgElt)
{}
  printf "pp-neighbors process for k = %o and prime %o\n", Nu`k, Nu`pp;
  printf "pivots = %o\n", Nu`pivots;
  for i := 1 to Nu`k do
    printf "%o: type %o, polar_index %o, subspace_index %o\n", i, Nu`data[i]`type, Nu`data[i]`polar_index, Nu`data[i]`subspace_index;
  end for;
end intrinsic;

//=======
//
// pp-neighbor processing
//
//=======

intrinsic ppNeighbors(Lambda::ModDed, pp::RngOrdIdl : k := 1, BeSuperCareful := true, verbose := false) -> List
  {Returns the pp-neighbors of Lambda for isotropic subspaces of dimension k.}
  
  Nu := ppNeighborProcess(Lambda, pp : k := k, BeSuperCareful := BeSuperCareful);

  neigh := [];
  Pi, bl := NextppNeighbor(Nu : BeSuperCareful := BeSuperCareful, verbose := verbose);
  while bl do
    Append(~neigh, Pi);
    Pi, bl := NextppNeighbor(Nu : BeSuperCareful := BeSuperCareful, verbose := verbose);
  end while;

  return neigh;    
end intrinsic;
  
intrinsic ppNeighborProcess(Lambda::ModDed, pp::RngOrdIdl : k := 1, BeSuperCareful := true) -> GrpFrml
  {Returns the first pp-neighbor of Lambda for isotropic subspaces of dimension k and its 
   encoded representation, for purposes of iteration.}

  Nu := HackobjCreateRaw(GrpFrml);
  Nu`Lambda := Lambda;
  Nu`innerprod := InnerProductMatrix(Lambda`QuadraticSpace);

  Nu`pp := pp;
  Nu`Npp := Norm(pp);
  kappapp, mkappapp := ResidueClassField(pp);
  Nu`pp_list_mod := [x : x in kappapp];
  Nu`pp_list := [x@@mkappapp : x in Nu`pp_list_mod];
  assert Nu`pp_list[1] eq 0;  

  Nu`ppinv := pp^-1;
  Nu`P := SafeUniformiser(pp);
    
  ZZ_F := Order(pp);
  require ZZ_F eq BaseRing(Lambda) : "pp must be an ideal of the base ring of Lambda";

  Nu`k := k;

  ppbasis, n := ppStandardBasis(Lambda, pp : BeSuperCareful := BeSuperCareful);
  Nu`ppbasis := ppbasis;
  Nu`n := n;

  prec := Min([0] cat &cat[[Valuation(vi,pp) : vi in Eltseq(v)] : v in ppbasis]);
  prec := -2*prec+2;

  ZZ_F_pp, mpp := Completion(ZZ_F, pp : Precision := prec);
  Nu`ZZ_F_pp := ZZ_F_pp;
  Nu`mpp := mpp;
  
  Nu`pivots := [1..k];

  Nu`data := [];
  for i := 1 to k do
    nu := HackobjCreateRaw(GrpFrmlElt);
    nu`type := "";
    nu`polar_index := [];
    nu`subspace_index := [];
    Append(~Nu`data, nu);
  end for;
  
  Nu`skewspace_index := [];

  return Nu;
end intrinsic;

intrinsic _iterateSkewspace(Nu : BeSuperCareful := true, verbose := false) -> . 
  {}
  
	if Nu`k eq 1 then
	  return false;
	end if;

	skewiterated := false;
	skewiterind := (Nu`k*(Nu`k-1)) div 2;
	
	repeat
		if verbose then
			print "skewiterind:", skewiterind;
		end if;
		
    if Nu`skewspace_index[skewiterind] lt Nu`Npp then
      Nu`skewspace_index[skewiterind] +:= 1;
      skewiterated := true;

      if verbose then
				print "Iterated skewsubspace:", skewiterind, Nu`skewspace_index;
			end if;
    else // must carry
      Nu`skewspace_index[skewiterind] := 1;
      if skewiterind gt 1 then
        skewiterind -:= 1;
        
        if verbose then
					print "Moving back in skewspace index:", skewiterind, Nu`skewspace_index;
				end if;
			else
				if verbose then
					print "No more skew space to iterate!";
				end if;

			  return false;
      end if;
    end if;
  until skewiterated;
  
  return true;
end intrinsic;

intrinsic _iterateNeighbor(Nu : BeSuperCareful := true, verbose := false) -> . 
  {}
  
	// Iterate the kth vector.
	if BeSuperCareful then assert #Nu`data eq Nu`k; end if;
	
	iterated := false;
	iterk := Nu`k;
	itertype := Nu`data[iterk]`type;
	iterind := Nu`data[iterk]`subspace_dim;
	
	repeat
		if verbose then
			print "iterk, iterind, itertype:", iterk, iterind, itertype;
		end if;
		
		if itertype ne "h" then
			if Nu`data[iterk]`subspace_dim gt 0 and Nu`data[iterk]`subspace_index[iterind] lt Nu`Npp then 
				Nu`data[iterk]`subspace_index[iterind] +:= 1;
				iterated := true;

				if verbose then
					print "Iterated subspace:", iterk, iterind, Nu`data[iterk]`subspace_index;
				end if;
			else // must carry
				if Nu`data[iterk]`subspace_dim gt 0 then
					Nu`data[iterk]`subspace_index[iterind] := 1;
				end if;
				if iterind gt 1 then
					iterind -:= 1;

					if verbose then
						print "Moving back in subspace index:", iterk, iterind, Nu`data[iterk]`subspace_index;
					end if;
				else // must rewind the dimension
					Nu`data[iterk]`type := "";

					if iterk eq 1 then // no dimension to rewind, must get new pivots
						Nu`pivots := next_pivots(Nu`pivots, 2*Nu`n);
						iterated := true;
						
						if verbose then
							print "New pivots:", iterk, iterind, Nu`pivots;
						end if;
					else
						iterk -:= 1;
						iterind := Nu`data[iterk]`subspace_dim;
            itertype := Nu`data[iterk]`type;
						if verbose then
							print "Rewinding the dimension:", iterk, iterind;
						end if;
					end if;
				end if;
			end if;
		else // type eq "h"
			if #Nu`data[iterk]`polar_index eq 2 then // must pair to be zero, so enumerate [a,1] and [1,b] 
  			if Nu`data[iterk]`polar_index[2] eq 1 and Nu`data[iterk]`polar_index[1] lt Nu`Npp then
					Nu`data[iterk]`polar_index[1] +:= 1;
					iterated := true;

					if verbose then
						print "Iterated zero polar with second index '0':", iterk, iterind, Nu`data[iterk]`polar_index;
					end if;
				elif Nu`data[iterk]`polar_index eq [Nu`Npp,1] then
					Nu`data[iterk]`polar_index := [1,2];
					iterated := true;

					if verbose then
						print "Iterated zero polar; switching to first index '0':", iterk, iterind, Nu`data[iterk]`polar_index;
					end if;
				elif Nu`data[iterk]`polar_index[1] eq 1 and Nu`data[iterk]`polar_index[2] lt Nu`Npp then
					Nu`data[iterk]`polar_index[2] +:= 1;
					iterated := true;

					if verbose then
						print "Iterated zero polar with first index '0':", iterk, iterind, Nu`data[iterk]`polar_index;
					end if;
				else
					itertype := "g";
					Nu`data[iterk]`polar_index := [];

          if verbose then
            print "Done with zero polar, moving to subspace:", iterk, iterind, Nu`data[iterk]`polar_index;
          end if;
        end if;
      else 
        if Nu`data[iterk]`polar_index[1] lt Nu`Npp then
          Nu`data[iterk]`polar_index[1] +:= 1;
          iterated := true;

          if verbose then
            print "Iterated nonzero polar:", iterk, iterind, Nu`data[iterk]`polar_index;
          end if;
        else // no room left to iterate (and no zeros!)
          itertype := "g";
          Nu`data[iterk]`polar_index := [];

          if verbose then
            print "Done with nonzero polar, moving to subspace:", iterk, iterind, Nu`data[iterk]`polar_index;
          end if;
        end if;
      end if;
    end if;
  until iterated;
  
  return iterk;
end intrinsic;

intrinsic NextppNeighbor(Nu::GrpFrml : BeSuperCareful := true, verbose := false) -> ModDed, BoolElt
  {Returns the next pp-neighbor of Lambda for isotropic subspaces of dimension k and its iteration process.}

  if Nu`data[Nu`k]`type ne "" then
    skewiterated := _iterateSkewspace(Nu : BeSuperCareful := BeSuperCareful, verbose := verbose);
    if skewiterated then
      iterk := Nu`k;
    else
      iterk := _iterateNeighbor(Nu : BeSuperCareful := BeSuperCareful, verbose := verbose);
    end if;
  else
    skewiterated := false;
    iterk := 1;
  end if;
  
  if Nu`pivots eq [] then
    // Nothing left!
    return Nu, false;
  end if;
  
  if not skewiterated then
		while iterk le Nu`k do // set up spaces
			ktype := Nu`data[iterk]`type;
			if ktype eq "" then
				// Need to set up space
	
				if verbose then
					print "Setting up space:", iterk;
				end if;
	
				// First, find the span of nonpivots orthogonal to the previous iterk-1 vectors
				ppbasis_k := [Nu`ppbasis[i] : i in [Nu`pivots[iterk]..#Nu`ppbasis] | i notin Nu`pivots or i eq Nu`pivots[iterk]];
				if iterk gt 1 then
					V := Nu`Lambda`QuadraticSpace;
					current_k := [Nu`data[i]`current : i in [1..iterk-1]];
					B := Matrix(ppbasis_k)*Nu`innerprod*Transpose(Matrix(current_k));
					B := Matrix(Nrows(B),Ncols(B), [Nu`mpp(b) : b in Eltseq(B)]);
					kerB := Kernel(B);
					if Dimension(kerB) eq 0 then
						if verbose then
							print "Nonpivot orthogonal space empty!  Iterating...";
						end if;
						iterk := _iterateNeighbor(Nu : BeSuperCareful := BeSuperCareful, verbose := verbose);
						continue;
					end if;
					
					if not IsWeaklyZero(Eltseq(kerB.1)[1] - 1) then
						if verbose then
							print "Nonpivot orthogonal space projects trivially onto pivot space!  Iterating...";
						end if;
						iterk := _iterateNeighbor(Nu : BeSuperCareful := BeSuperCareful, verbose := verbose);
						continue;
					end if;
					 
					ppbasis_k := [&+[(v[i]@@Nu`mpp)*ppbasis_k[i] : i in [1..#ppbasis_k]] : v in Basis(kerB)];
					
					if BeSuperCareful then
						B := Matrix(ppbasis_k)*Nu`innerprod*Transpose(Matrix(current_k));
						assert &and[Valuation(b, Nu`pp) ge 2 : b in Eltseq(B)];
					end if;
	
					if verbose then
						print "Pivot + Nonpivot orthogonal space computed";
						print ppbasis_k;
					end if;
				else
					if verbose then
						print "Pivot + Nonpivot space computed";
						print ppbasis_k;
					end if;
				end if;
				
				// Now we have a basis whose first element has nonzero entry in the pivot column
				// and is supported on the other nonpivots.
				// We compute the beginning of a standard basis to decide the type.
				B := Matrix(ppbasis_k)*Nu`innerprod*Transpose(Matrix(ppbasis_k));
	
				minval := Min([Valuation(B[1,j],Nu`pp) : j in [1..Ncols(B)]]);
				assert minval eq 0 or minval ge 2;
				if minval eq 0 then
					if verbose then
						print "First line (g)...";
					end if;

					// either pivot is anisotropic or pairs nonzero, so general
					Nu`data[iterk]`type := "g";
	
					subspacebasis, _, T := _ppOrthogonalStandardBasis(ppbasis_k, Nu`pp, B : BeSuperCareful := BeSuperCareful, verbose := verbose);
          B := T*B*Transpose(T);

					if verbose then
						print "Basis computed (g)...";
					end if;

					blmonic := Valuation(T[1,1],Nu`pp) eq 0 and &and[Valuation(T[i,1],Nu`pp) ge 2 : i in [2..Nrows(T)]]; // Keep "monic" coefficient
          if not blmonic then
           	if verbose then
		  				print "Did not preserve monic: trying to fix!", T;
  					end if;

            minval, indminval := Min([Valuation(T[i,1],Nu`pp) : i in [1..Nrows(T)]]);
            assert minval eq 0;            
            subspacebasis := [subspacebasis[indminval]] cat ppbasis_k[2..#ppbasis_k];

            if BeSuperCareful then
							F := NumberField(Order(Nu`pp));
							changeofbasis := Solution(ChangeRing(Matrix(ppbasis_k), F), ChangeRing(Matrix(subspacebasis), F));
							assert Valuation(changeofbasis[1,1],Nu`pp) eq 0 and &and[Valuation(changeofbasis[i,1],Nu`pp) ge 2 : i in [2..Nrows(changeofbasis)]];
            end if;
            
            croppedbasis := subspacebasis[2..#subspacebasis];
            B := Matrix(croppedbasis)*Nu`innerprod*Transpose(Matrix(croppedbasis));
            croppedbasis, _, _, m := _ppOrthogonalStandardBasis(croppedbasis, Nu`pp, B : BeSuperCareful := BeSuperCareful, verbose := verbose);

            ppbasis_k_std := [subspacebasis[1]] cat croppedbasis;
            
            if BeSuperCareful then
							F := NumberField(Order(Nu`pp));
							changeofbasis := Solution(ChangeRing(Matrix(ppbasis_k), F), ChangeRing(Matrix(ppbasis_k_std), F));
							assert Valuation(changeofbasis[1,1],Nu`pp) eq 0 and &and[Valuation(changeofbasis[i,1],Nu`pp) ge 2 : i in [2..Nrows(changeofbasis)]];
            end if;
            
     				B := Matrix(ppbasis_k_std)*Nu`innerprod*Transpose(Matrix(ppbasis_k_std));
	  				subspacebasis, _, T, m := _ppOrthogonalStandardBasis(ppbasis_k_std, Nu`pp, B : BeSuperCareful := BeSuperCareful, verbose := false);
            B := T*B*Transpose(T);
            if Valuation(B[1,1],Nu`pp) eq 0 then
              assert m le 2; // anisotropic form
              if verbose then
  							print "Pivot + nonpivot space is anisotropic!";
	  					end if;
		   				iterk := _iterateNeighbor(Nu : BeSuperCareful := BeSuperCareful, verbose := verbose);
				  		continue;
            end if;
              
            assert Valuation(T[1,1],Nu`pp) eq 0 and &and[Valuation(T[i,1],Nu`pp) ge 2 : i in [2..m]];
            if m lt #subspacebasis then 
              assert &or[Valuation(T[i,1],Nu`pp) eq 0 : i in [m+1..Nrows(T)]] or
                     &and[Valuation(T[i,1],Nu`pp) ge 2 : i in [m+1..Nrows(T)]];
            end if;

            if BeSuperCareful then
							F := NumberField(Order(Nu`pp));
							changeofbasis := Solution(ChangeRing(Matrix(ppbasis_k), F), ChangeRing(Matrix(subspacebasis), F));
							assert Valuation(changeofbasis[1,1],Nu`pp) eq 0 and &and[Valuation(changeofbasis[i,1],Nu`pp) ge 2 : i in [2..m]];
            end if;
            
            if m lt #subspacebasis then
              minval, indminval := Min([Valuation(T[i,1],Nu`pp) : i in [m+1..Nrows(T)]]);
              indminval +:= m;
              if minval eq 0 then
                SwapElements(~subspacebasis,1,indminval);
                SwapRows(~T,1,indminval);
              end if;
              for i := m+1 to Nrows(T) do
                c := -(Nu`mpp(T[i,1])*Nu`mpp(T[1,1])^-1)@@Nu`mpp;
                subspacebasis[i] +:= c*subspacebasis[1];
                AddRow(~T, c, 1, i);
              end for;

              if BeSuperCareful then
                assert &and[Valuation(T[i,1],Nu`pp) ge 2 : i in [2..Nrows(T)]];
              end if;
              
              B := Matrix(subspacebasis)*Nu`innerprod*Transpose(Matrix(subspacebasis));
            end if;            
      		end if;
      		
      		ppbasis_k := subspacebasis;
        end if;
        
        minval, indminval := Min([Valuation(B[1,j],Nu`pp) : j in [1..Ncols(B)]]);
        if minval eq 0 then
          if indminval eq 1 then
            if verbose then
							print "Pivot + nonpivot space is anisotropic!";
						end if;
						iterk := _iterateNeighbor(Nu : BeSuperCareful := BeSuperCareful, verbose := verbose);
						continue;
          end if;
          
					if verbose then
						print "Type 'g': Pivot is anisotropic or pairs nonzero, so general; indminval =", indminval;
					end if;
		
					if BeSuperCareful then
						assert &and[Valuation(B[1,j], Nu`pp) ge 2 : j in [1..#subspacebasis] | j ne indminval] and
									 Valuation(B[1,indminval]-1, Nu`pp) ge 2 and
									 &and[Valuation(B[indminval,j], Nu`pp) ge 2 : j in [2..#subspacebasis]]; 
					end if;
	
					// The quadratic form looks like (1*)x_indminval + ... = 0
					// So for arbitrary values in the rest of the space, we can solve for x_indminval uniquely.
					Nu`data[iterk]`pivot := subspacebasis[1];
	
					Nu`data[iterk]`polar_index := [];
					b := (Nu`mpp(B[1,indminval])^-1)@@Nu`mpp;
					Nu`data[iterk]`polar_basis := [b*subspacebasis[indminval]];
	
					subspacebasis := [subspacebasis[i] : i in [2..#subspacebasis] | i ne indminval];
					Nu`data[iterk]`subspace_dim := #subspacebasis;
					Nu`data[iterk]`subspace_index := [1 : i in [1..#subspacebasis]];
					Nu`data[iterk]`subspace_basis := subspacebasis;
        else
					// Pivot is isotropic and pairs zero with all other vectors.
					// Check to see if the space contains a hyperbolic plane.
					if verbose then
						print "First line (hi)...";
					end if;
					
					Nu`data[iterk]`pivot := ppbasis_k[1];
	
					ppbasis_k := ppbasis_k[2..#ppbasis_k];
					RemoveRow(~B, 1);
					RemoveColumn(~B, 1);
	
					subspacebasis, n, T, m := _ppOrthogonalStandardBasis(ppbasis_k, Nu`pp, B : BeSuperCareful := BeSuperCareful, verbose := verbose);
  		    
					if n gt 0 then
    		    B := T*B*Transpose(T);
    		    
						// There is a hyperbolic plane
						// The quadratic form looks like (0 +) x_1*x_{n+1} + ... = 0
						// so for arbitrary values of the ... variables, we can solve for x_1, x_{n+1}.
						Nu`data[iterk]`type := "h";
						if verbose then
							print "Type 'h': Subspace contains a hyperbolic plane";
						end if;
	
						minval, indminval := Min([Valuation(B[1,j],Nu`pp) : j in [1..Ncols(B)]]);
						assert minval eq 0 and indminval gt 1 and Valuation(B[1,indminval]-1,Nu`pp) ge 2;

						Nu`data[iterk]`polar_index := [];
						Nu`data[iterk]`polar_basis := [subspacebasis[1],subspacebasis[indminval]];

						subspacebasis := [subspacebasis[i] : i in [2..#subspacebasis] | i ne indminval];
						Nu`data[iterk]`subspace_dim := #subspacebasis;
						Nu`data[iterk]`subspace_index := [1 : i in [1..#subspacebasis]];
						Nu`data[iterk]`subspace_basis := subspacebasis;
					else
						// The maximal isotropic subspace is actually contained in the radical; there are
						// no hyperbolic planes, and the quadratic form is zero + anisotropic.
						// So we must disregard the anisotropic subspace.
	
						Nu`data[iterk]`type := "i";
						if verbose then
							print "Type 'i': Subspace is totally isotropic + anisotropic (no hyperbolic plane)";
						end if;
	
						Nu`data[iterk]`polar_index := [];
						dim := #subspacebasis - m;
						Nu`data[iterk]`subspace_dim := dim;
						Nu`data[iterk]`subspace_index := [1 : i in [1..dim]];
						Nu`data[iterk]`subspace_basis := subspacebasis[m+1..#subspacebasis];
					end if;
				end if;
			end if;
			
			if Nu`data[iterk]`subspace_dim gt 0 then
				Nu`data[iterk]`current := 
						Nu`data[iterk]`pivot + 
							&+[Nu`pp_list[Nu`data[iterk]`subspace_index[i]]*Nu`data[iterk]`subspace_basis[i] : i in [1..Nu`data[iterk]`subspace_dim]];
			else
				Nu`data[iterk]`current := Nu`data[iterk]`pivot;
			end if;
	
			c := Matrix(Nu`data[iterk]`current)*Nu`innerprod*Transpose(Matrix(Nu`data[iterk]`current));
			c := (Nu`mpp(c[1,1])/2)@@Nu`mpp;
			
			if Nu`data[iterk]`type eq "g" then
				// type is general, and the pairing between pivot and polar is nonzero.
				Nu`data[iterk]`current -:= c*Nu`data[iterk]`polar_basis[1];
	
				if BeSuperCareful then
					// Check isotropy
					curnorm := Matrix(Nu`data[iterk]`current)*Nu`innerprod*Matrix(Transpose(Matrix(Nu`data[iterk]`current)));
					assert Valuation(curnorm[1,1], Nu`pp) ge 2;
				end if;
			elif Nu`data[iterk]`type eq "h" then
				// type is hyperbolic, and polar is a hyperbolic pair.
				if Nu`data[iterk]`polar_index eq [] then
					// new subspace vector, need to compute new polar constants
					if Valuation(c, Nu`pp) ge 2 then
						Nu`data[iterk]`polar_index := [1,1];
					else
						Nu`data[iterk]`polar_index := [2];
					end if;
				end if;
	
				x := Nu`pp_list[Nu`data[iterk]`polar_index[1]];
				if #Nu`data[iterk]`polar_index eq 2 then
					y := Nu`pp_list[Nu`data[iterk]`polar_index[2]];
				else
					y := -c*((Nu`mpp(x)^-1)@@Nu`mpp);
				end if;
	
				Nu`data[iterk]`current +:= x*Nu`data[iterk]`polar_basis[1] + y*Nu`data[iterk]`polar_basis[2];        
	
				if BeSuperCareful then
					// check that polar_basis was computed correctly.
				end if;
			else 
				assert Nu`data[iterk]`type eq "i";
				// type is isotropic, and the span of pivot and the subspace is totally isotropic.
			end if;
	
			if verbose then
				print "New current vector:", Nu`data[iterk]`current;
			end if;
	
			iterk +:= 1;
		end while;
	
		// Convert flag to neighbor
		ppneighborbasis := [Nu`data[i]`current : i in [1..Nu`k]] cat [Nu`ppbasis[i] : i in [1..#Nu`ppbasis] | i notin Nu`pivots];
		if BeSuperCareful then
			assert #ppneighborbasis eq #Nu`ppbasis;
			F := NumberField(Order(Nu`pp));
			changeofbasis := ChangeRing(Matrix(ppneighborbasis), F)*ChangeRing(Matrix(Nu`ppbasis), F)^-1;
			assert &and[Valuation(b,Nu`pp) ge 0 : b in Eltseq(changeofbasis)];
			assert Valuation(Determinant(changeofbasis),Nu`pp) eq 0;
			
			if verbose then
				print changeofbasis;
			end if;
		end if;
		
		B := Matrix(ppneighborbasis)*Nu`innerprod*Transpose(Matrix(ppneighborbasis));
		ppneighborbasis_std, n, T := _ppOrthogonalStandardBasis(ppneighborbasis, Nu`pp, B : BeSuperCareful := BeSuperCareful, verbose := verbose);
		if BeSuperCareful then
			assert n eq Nu`n;
			assert &and[T[i,j] eq 0 : i in [1..Nu`k], j in [Nu`k+1..Ncols(T)]];
			assert Valuation(Determinant(Submatrix(T,1,1,Nu`k,Nu`k)),Nu`pp) eq 0;
		end if;
		
		Nu`ppneighborbasis_std := ppneighborbasis_std;  // cache
    
    Nu`skewspace_index := [1 : i in [1..(Nu`k*(Nu`k-1)) div 2]];  // initialize skewspace
	end if;

  // Set up skewspace
  ppneighborbasis_std := Nu`ppneighborbasis_std;
  i := 1; j := 2;
  for ij := 1 to (Nu`k*(Nu`k-1)) div 2 do
    c := Nu`P*Nu`pp_list[Nu`skewspace_index[ij]];
    ppneighborbasis_std[i] +:= c*ppneighborbasis_std[j+Nu`n];
    ppneighborbasis_std[j] -:= c*ppneighborbasis_std[i+Nu`n];
    if j eq Nu`k then
      i +:= 1;
      j := i+1;
    else
      j +:= 1;
    end if;
  end for;
  
  if BeSuperCareful then 
    F := NumberField(Order(Nu`pp));
		changeofbasis := ChangeRing(Matrix(ppneighborbasis_std), F)*ChangeRing(Matrix(Nu`ppneighborbasis_std), F)^-1;
		assert &and[Valuation(b,Nu`pp) ge 0 : b in Eltseq(changeofbasis)];
		assert Valuation(Determinant(changeofbasis),Nu`pp) eq 0;
			
		if verbose then
      print "Added skewspace:", changeofbasis;
		end if;

		B := Matrix(ppneighborbasis_std)*Nu`innerprod*Transpose(Matrix(ppneighborbasis_std));
		_, n, T := _ppOrthogonalStandardBasis(ppneighborbasis_std, Nu`pp, B : BeSuperCareful := BeSuperCareful, verbose := verbose);
		assert Submatrix(T,1,1,2*n,2*n) eq 1;
  end if;

  ZZ_F := Order(Nu`pp);
  ppneighborbasis_idls := [* 1*ZZ_F : pnb in ppneighborbasis_std *];
  for i := 1 to Nu`k do
    ppneighborbasis_idls[i] := Nu`ppinv;
    ppneighborbasis_idls[i+Nu`n] := Nu`pp;
  end for;
  ppneighborbasis_idls := [P : P in ppneighborbasis_idls];

  // Now write down the lattice and HNF it
  pseudobasis := PseudoBasis(Nu`Lambda);
  pmat_idls := [Nu`pp*pb[1] : pb in pseudobasis] cat ppneighborbasis_idls;
  pmat_mat := Matrix([pb[2] : pb in pseudobasis] cat [pnb : pnb in ppneighborbasis_std]);
  pmat := HermiteForm(PseudoMatrix(pmat_idls, pmat_mat));
  Pi := MakeNeighborFromPseudoMatrix(Nu`Lambda, pmat);

  if BeSuperCareful then
    assert Genus(Lattice(Pi)) eq Genus(Lattice(Nu`Lambda));

    pbPi := PseudoBasis(Pi);
    PiZZbasis := &cat[ [ x*pb[2] : x in Basis(pb[1]) ] : pb in pbPi ];

    BPi := Matrix(PiZZbasis)*ChangeRing(Nu`innerprod,FieldOfFractions(ZZ_F))*Transpose(Matrix(PiZZbasis));
    assert &and[IsIntegral(b) : b in Eltseq(BPi)];
  
    LambdacapPi := Nu`Lambda meet Pi;
    LambdacapPi`ParentModFrmAlg := Nu`Lambda`ParentModFrmAlg;
    LambdacapPi`QuadraticSpace := Nu`Lambda`QuadraticSpace;
    assert Discriminant(LambdacapPi)/Discriminant(Nu`Lambda) eq Nu`pp^(2*Nu`k);

    assert ElementaryDivisors(Nu`Lambda,Pi) eq [Nu`ppinv : i in [1..Nu`k]] cat [1*ZZ_F : i in [1..Dimension(Nu`Lambda)-2*Nu`k]] cat [Nu`pp : i in [1..Nu`k]];
  end if;

  return Pi, true;
end intrinsic;



//=======
//
// Genus representatives
//
//=======

intrinsic GenusRepresentatives(M::ModFrmAlg : UsePrimes := [], BeSuperCareful := true, verbose := false) -> SeqEnum[ModDed]
  {Returns a set of representatives for the genus of the defining lattice of M.}

  if assigned M`GenusReps and UsePrimes eq [] then
    return M`GenusReps;
  end if;

  if verbose then
    print "WARNING: Strong approximation is assumed!!";
  end if;

  require IsOrthogonal(M) : "Haven't thought about unitary case yet!";

  Lambda := DefiningLattice(M);
  dd := Discriminant(Lambda);
  require &and[Valuation(dd,PP) eq 0 : PP in UsePrimes] : "UsePrimes must be coprime to the discriminant of Lambda.";

  // TODO: Put in conditions for strong approximation. 
  // I think it's OK that the spinor genus is equal to the genus for sums of squares,
  // but I'm not sure.

  F := BaseField(M);
  ZZ_F := Integers(F);

  Lambda := DefiningLattice(M);
  dd := Discriminant(Lambda);
  d := Integers()!Norm(dd);
  dfact := Factorization(d);
  if #dfact eq 0 then
    dmax := 1;
  else
    dmax := dfact[#dfact][1];
  end if;
  
  if #UsePrimes gt 0 then
    pps := UsePrimes;
    assert &and[Gcd(Norm(pp),2*d) eq 1 : pp in pps];
  else
    pps := [pp : pp in PrimesUpTo(Max(100,dmax),F) | Gcd(Norm(pp),2*d) eq 1][1..1];
  end if;

  genusreps := [Lambda];
  
  for pp in pps do
    if true then
      print "Starting with", #genusreps, "reps, computing neighbors for prime of norm", Norm(pp);
    end if;
    frontier := [Lambda];
    while frontier ne [] do
      newfrontier := [];
      for Lambda in frontier do
        Nu := ppNeighborProcess(Lambda, pp : BeSuperCareful := BeSuperCareful);
        Pi, bl := NextppNeighbor(Nu : BeSuperCareful := BeSuperCareful, verbose := verbose);
        while bl do // bl is false when NextppNeighbor says there are no more neighbors of Nu
          isnewrep := true;
          for Rho in genusreps do
            bl := IsIsometric(Pi, Rho : BeSuperCareful := BeSuperCareful);
            if bl then
              isnewrep := false;
              break;
            end if;
          end for;
          if isnewrep then
            Append(~newfrontier, Pi);
            Append(~genusreps, Pi);
          end if;
          Pi, bl := NextppNeighbor(Nu : BeSuperCareful := BeSuperCareful, verbose := verbose);
        end while;
      end for;
      frontier := newfrontier;
    end while;
    if true then
      print "Found", #genusreps, "reps with neighbors for prime of norm", Norm(pp);
    end if;
  end for;

  M`GenusReps := genusreps;

  return genusreps;
end intrinsic;

intrinsic Dimension(M::ModFrmAlg) -> RngIntElt
  {Returns the dimension of M.}

  if M`IsFull then
    return #GenusRepresentatives(M);
  else
    return #M`basis;
  end if;
end intrinsic;

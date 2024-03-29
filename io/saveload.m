freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: saveload.m (Routines used for saving and loading data to/from disk.)

   05/26/20: Modified save to support innerForms with coefficients in the 
             field of fractions. (and not just in the integer ring).

   05/08/20: Changed reading and writing of eigenvalues to have all 
             eigenvalues in the same universe.

   04/24/20: Modified reading and writing of group according to GrpRed

   04/21/20: Changed reading and writing of eigenforms to read and write also 
             the reducible spaces.

   04/20/20: Fixed bug when loading a representation over a finite field.

   04/17/20: Added reading and writing of the root datum and the group.

   04/15/20: Renamed Load to a constructor, to prevent collisions.

   04/02/20: Added documentation

   04/01/20: Added reading and writing of the group and the weight

   03/31/20: Changed references to quadSpace to the more general rfxSpace
 
 ***************************************************************************/

// Here are the intrinsics this file defines
// FileExists(filename::MonStgElt) -> BoolElt
// Save(M::ModFrmAlg)
// Save(M::ModFrmAlg, filename::MonStgElt)
// AlgebraicModularForms(filename::MonStgElt) -> ModFrmAlg

// imports


// TODO: Update this script to accommodate for the updated accessor functions
//  by removing direct access via the ` substructure symbol.

import "/Applications/Magma/package/LieThry/Root/RootDtm.m" : rootDatum;
import "../neighbors/genus-CN1.m" : sortGenusCN1;
import "../modfrmalg/modfrmalg.m" : ModFrmAlgInit;

intrinsic FileExists(filename::MonStgElt : ShowErrors := true) -> BoolElt
{ Checks whether a specified file exists on disk. }
	try
		// Attempt to open the file for reading.
		ptr := Open(filename, "r");

		// Delete the pointer, thereby closing the file stream (see
		//  Magma documentation for Open intrinsic).
		ptr := [];
	catch e
		if ShowErrors then
			print "ERROR: File does not exist!";
		end if;
		return false;
	end try;

	return true;
end intrinsic;

intrinsic Save(M::ModFrmAlg)
{ Save data if it was loaded from a file. }
	if assigned M`filename then
		Save(M, M`filename : Overwrite := true);
	else
		print "WARNING: File not saved, since no implicit filename.";
	end if;
end intrinsic;

intrinsic Save(M::ModFrmAlg, filename::MonStgElt : Overwrite := false)
{ Save data to disk. }
	// The file where the data will be stored.
	file := GetAMFPath() cat filename;

	// If overwrite flag not set and file exists, display warning and
	//  immediately return.
	if not Overwrite and FileExists(file : ShowErrors := false) then
		print "WARNING: File not saved. Set the Overwrite parameter.";
		return;
	end if;

	// The inner form associated to the ambient reflexive space.
	innerForm := ChangeRing(M`L`rfxSpace`innerForm,
				FieldOfFractions(M`L`R));

	// The genus representatives.
	genus := [* *];
	if assigned M`genus then
		for idx in [1..#M`genus`Representatives] do
			// Shortcut to the current genus representative.
			L := M`genus`Representatives[idx];

			if Type(BaseRing(M`L)) eq FldRat then
				// If we're over the rationals, we simply
				//  choose the basis of L.
				basis := Basis(L);
			else
				// Otherwise, we store the pseudobasis of L.
				basis := [*
					< [ Eltseq(b) : b in Generators(pb[1]) ],
					[ Eltseq(x) : x in Eltseq(pb[2]) ] >
					     : pb in PseudoBasis(L) *];
			end if;

			// Add the appropriate basis to the genus list.
			Append(~genus, basis);
		end for;
	end if;

	// Valid dimensions for the Hecke matrices.
	dims := Keys(M`Hecke`Ts);

	// The Hecke matrices we've computed.
	hecke := [* *];

	for dim in dims do
		// The list of Hecke matrices for this dimension.
		list := [* *];

		// Retrieve complete list of Hecke matrices and ideals.
		Ts, Ps := HeckeOperators(M, dim);

		// A coupled list of Hecke matrices and their ideals.
		list := [* < Generators(Ps[i]), Ts[i] > : i in [1..#Ts] *];

		// Add this list to the ongoing list of Hecke matrices.
		Append(~hecke, < dim, list >);
	end for;

	// The Hecke standard images we've computed.
	hecke_images := [* *];
        if assigned M`Hecke`standard_images then
	 for image_idx in [1..Dimension(M)] do
	    // dimensions for which the Hecke operators where computed
	    image_dims := Keys(M`Hecke`standard_images[image_idx]);
	    hecke_img_dim := [* *];
	    for dim in image_dims do
		// The list of Hecke images for this dimension.
		list := [* *];

		Ps := Keys(M`Hecke`standard_images[image_idx][dim]);
		Ps := Sort([P : P in Ps]);
		images := [M`Hecke`standard_images[image_idx][dim][P] :
			   P in Ps];

		// A coupled list of Hecke images and their ideals.
		list := [* < Generators(Ps[i]), images[i] > : i in [1..#Ps] *];

		// Add this list to the ongoing list of Hecke matrices.
		Append(~hecke_img_dim, < dim, list >);
	    end for;
	    Append(~hecke_images, hecke_img_dim);
	 end for;
        end if;
	// Initialize the eigenforms.
	eigenforms := [* *];

	// Build data structure for saving the eigenforms to disk.
	if assigned M`Hecke and assigned M`Hecke`Eigenforms then
	    for f in M`Hecke`Eigenforms do
		if f`IsEigenform then
		     
		    // Valid dimensions for the eigenvalues
		    
		    if not assigned f`Eigenvalues then
			   // f`Eigenvalues := AssociativeArray();
		      dims := [];
		    else
		      dims := Keys(f`Eigenvalues);
	            end if;
		
		    dims := Sort([x : x in dims]);

		    // The eigenvalues we've computed.
		    // eigenvalues := [];
		    all_ps := [];
		    all_evs := [];

		    for dim in dims do

			Ps := [p : p in Keys(f`Eigenvalues[dim])];
			evs := [Eltseq(f`Eigenvalues[dim][p]) : p in Ps ];
			
			// A coupled list of eigenvalues and the corresponding ideals.
			list := [* Generators(p) : p in Ps *];

			// Add this list to the ongoing list of Hecke matrices.
			Append(~all_evs, evs);
			Append(~all_ps, list);
		    end for;
		    eigenvalues := < dims, all_ps, all_evs >;
                    Append(~eigenforms, < Eltseq(f`vec) , true, eigenvalues,
                           f`IsEisenstein>);
		else
		    Append(~eigenforms, < Eltseq(f`vec) , false>);
		end if;
	    end for;
	end if;


	// Build the data structure that will be saved to file.
	data := [*
		< "GROUP", M`G >,
		< "WEIGHT", M`W >,
		< "LEVEL", M`L >,
		< "FIXED_SUBSPACES", M`H >,
		< "INNER", innerForm >,
		< "GENUS", genus >,
		< "HECKE", hecke >,
		< "HECKE_IMAGES", hecke_images >,
		< "EIGENFORMS", eigenforms >
	*];

	// Write data to file.
        // !!! Magma adds blank spaces and later can't read them !!!
	// Write(file, data, "Magma" : Overwrite := Overwrite);
        F := Open(file, "w");
        fprintf F, "%m", data;
        delete F;
end intrinsic;

intrinsic AlgebraicModularForms(filename::MonStgElt : ShowErrors := true) -> ModFrmAlg
{ Load an algebraic modular form from disk. }
	// The file where the data will be loaded.
	file := GetAMFPath() cat filename;

	// Build the polynomial ring over the integers so we are ready to read
	//  data from input file.
	Z<x> := PolynomialRing(Integers());

	// If file does not exist, display errors (if requested) and return.
	if not FileExists(file : ShowErrors := ShowErrors) then
		return false;
	end if;

	// The raw data from the file.
	str := Read(file);

	// Evaluate the data from file into Magma format.
	data := eval str;

	// An associative array which stores the appropriate meta data.
	array := AssociativeArray();

	// Store meta data.
	for entry in data do array[entry[1]] := entry[2]; end for;

	if not IsDefined(array, "INNER")  then
	    print "ERROR: Corrupt data.";
	    return false;
	end if;

	// Build the space of algebraic modular forms.

	G := array["GROUP"];
	
	// Build the number field we're working over.
	K := SplittingField(G);
	W := array["WEIGHT"];
        if IsDefined(array, "LEVEL") then 
           L := array["LEVEL"];
        end if;

        if IsDefined(array, "FIXED_SUBSPACES") then
          H := array["FIXED_SUBSPACES"];
        end if;

        if IsDefined(array, "FIXED_SUBSPACES") then 
	  for i in [1..#H] do
	    H[i] := ChangeRing(H[i], BaseRing(W));
            iota := H[i]`embedding;
            // We have to make sure these embed into W
            basis_images := [W!iota(H[i].j) : j in [1..Ngens(H[i])]];
            H[i]`embedding := Homomorphism(H[i], W, basis_images);
          end for;
        end if;

	// Assign the inner form.
	innerForm := ChangeRing(array["INNER"], K);

        if IsDefined(array, "LEVEL") then
	   L := ChangeRing(L, K);
           M := AlgebraicModularForms(G, W, L : GramFactor := IsQuadratic(L) select 2 else 1);
        else
           M := AlgebraicModularForms(G, W);
        end if;
        if IsDefined(array, "FIXED_SUBSPACES") then
          M`H := H;
        end if;
	// Assign genus representatives.
	if IsDefined(array, "GENUS") and #array["GENUS"] ne 0 then
	    // Retrive the list of genus representatives.
	    reps := array["GENUS"];

	    // Create a new genus symbol.
	    genus := New(GenusSym);
	    genus`Representatives := [];

	    if Type(BaseRing(M`L)) eq FldRat then
		// Handle the rationals separately.
		for i in [1..#reps] do
		    // Retrieve the basis for this genus rep and
		    //  convert it to the rationals just in case.
		    basis := Matrix(reps[i]);
		    basis := ChangeRing(basis, Rationals());
		    
		    // Build genus rep as a native lattice object.
		    L := LatticeWithBasis(basis, innerForm);

		    // Add it to the list.
		    Append(~genus`Representatives, L);
		end for;
	    else
		for i in [1..#reps] do
		    // List of coefficient ideals.
		    idls := [* *];
		    
		    // A basis of the ambient reflexive space.
		    basis := [];
		    
		    // Retrive the coefficient ideals and bases.
		    for data in reps[i] do
			// Convert the generators to the
			//  appropriate field.
			gens := [ M`L`F ! x : x in data[1] ];
			
			// Add coefficient ideal.
			Append(~idls, ideal< M`L`R | gens >);
			
			// Add basis vector.
			Append(~basis, Vector(
					       [ M`L`F!x : x in data[2] ]));
		    end for;
		    
		    // Convert ideals to fractional ideals.
		    idls := [ I : I in idls ];
		    
		    // A pseudomatrix we'll now use to construct the
		    //  appropriate genus representative.
		    //pmat := PseudoMatrix(idls, Matrix(basis));
		    
		    // Build genus representative.
		    L := LatticeWithBasis(
				 M`L`rfxSpace, Matrix(basis), idls);
		    
		    // Add lattice to the list of genus reps.
		    Append(~genus`Representatives, L);
		end for;
	    end if;

	    // Assign genus representative.
	    genus`Representative := genus`Representatives[1];

	    // Construct an associative array indexed by an invariant of
	    //  the isometry classes.

	    genus := sortGenusCN1(genus);
		
	    // Assign genus symbol to the space of modular forms.
	    M`genus := genus;
	end if;

	// Assign Hecke matrices.
	if IsDefined(array, "HECKE") and #array["HECKE"] ne 0 then
	    // Retrieve the list of Hecke matrices.
	    list := array["HECKE"];

	    // Assign Hecke matrix associative array.
	    M`Hecke`Ts := AssociativeArray();

	    for data in list do
		// The dimension of the Hecke matrices.
		k := data[1];
		
		// Assign an empty associative array for this dimension.
		M`Hecke`Ts[k] := AssociativeArray();
		
		for entry in data[2] do
		    // Generators of the prime ideal.
		    gens := [ M`L`R ! Eltseq(x) : x in entry[1] ];
		    
		    // The prime ideal associated to this entry.
		    P := ideal< M`L`R | gens >;
		    
		    // Assign Hecke matrix.
		    M`Hecke`Ts[k][P] := ChangeRing(entry[2],
						   BaseRing(M`W));
		end for;
	    end for;
	end if;

	// Assign Hecke images.
	if IsDefined(array, "HECKE_IMAGES") and #array["HECKE_IMAGES"] ne 0 then
	    // Retrieve the list of Hecke images.
	    list := array["HECKE_IMAGES"];

	    // Assign Hecke images associative array.
	    M`Hecke`standard_images := [AssociativeArray() : j in [1..#list]];

	    for j in [1..#list] do
		for data in list[j] do
		    // The dimension of the Hecke images.
		    k := data[1];
		
		    // Assign an empty associative array for this dimension.
		    M`Hecke`standard_images[j][k] := AssociativeArray();
		
		    for entry in data[2] do
			// Generators of the prime ideal.
			gens := [ M`L`R ! Eltseq(x) : x in entry[1] ];
			
			// The prime ideal associated to this entry.
			P := ideal< M`L`R | gens >;
		    
			// Assign Hecke image.
			M`Hecke`standard_images[j][k][P] :=
			    ChangeRing(entry[2],BaseRing(M`W));
		    end for;
		end for;
	    end for;
	end if;

	if IsDefined(array, "EIGENFORMS") then
		// Retrieve the list for convenient access.
		list := array["EIGENFORMS"];

		if #list ne 0 then
			M`Hecke`Eigenforms := [* *];
		end if;
                // This is for backwar compatibility,
                // erase when we don't need it anymore
                // to see if they are cusp forms
	        reps := Representatives(Genus(M));
	        // !!! TODO :
	        // Replace this by an actual bilinear
                // form compatible with the group
	        // Add handling the case when the narrow class group of the field
	        // is nontrivial.
                if not assigned M`H then ModFrmAlgInit(M); end if;
	        wts := &cat[[#AutomorphismGroup(reps[i])
				: j in [1..Dimension(M`H[i])]]:
		    i in [1..#reps]];
     
	        // instead of dividing by wts[i],
                // we multiply for the case of positive
         	// characteristic
                wt_prod := IsEmpty(wts) select 1 else &*wts;
	        mult_wts := [wt_prod div wt : wt in wts];

		for data in list do
                        // Construct an element of the modular space.
                        mform := New(ModFrmAlgElt);

                        // Assign parent modular space.
                        mform`M := M;

                        // Assign vector.
                        mform`vec := Vector(data[1]);

                        // for backward compatiblity
                        if #data lt 4 then 
                          // Flag as cuspidal?
			  if not IsTrivial(Weight(M)) then
			    mform`IsCuspidal := true;
			  else
			    mform`IsCuspidal := &+[ Eltseq(mform`vec)[i]
							  * mult_wts[i]
						      : i in [1..#wts]] eq 0;
                          end if;
                        else
			  assert #data eq 4;
                          mform`IsCuspidal := not data[4];
                        end if;

                        // Cusp forms are not Eistenstein.
                        mform`IsEisenstein := not mform`IsCuspidal;

			// Establish this as a Hecke eigenform.
                        mform`IsEigenform := data[2];

			if mform`IsEigenform then
			    // Retrieve the list of Hecke eigenvalues.
			    ev_list := data[3];
			    dims := ev_list[1];
			    ps := ev_list[2];
			    evs := ev_list[3];
			    F := BaseRing(mform`vec);

			    // Assign eigenvalues associative array.
			    mform`Eigenvalues := AssociativeArray();

			    for idx in [1..#dims] do
			    //for ev_data in ev_list do
				// The dimension of the eigenvalues.
				// k := ev_data[1];
				k := dims[idx];
				
				// Assign an empty associative array for this dimension.
				mform`Eigenvalues[k] := AssociativeArray();

				for p_idx in [1..#ps[idx]] do
				// for entry in ev_data[2] do
				    // Generators of the prime ideal.
				    gens := [ M`L`R ! Eltseq(x) :
					      x in ps[idx][p_idx]];
				
				    // The prime ideal associated to this entry.
				    P := ideal< M`L`R | gens >;
				    
				    // Assign eigenvalue.
				    mform`Eigenvalues[k][P] :=
					F!evs[idx][p_idx];
				    /*
					IsFinite(F) select
					F!evs[idx][p_idx] else evs[idx][p_idx];
				   */
				end for;
			    end for;
			   			   			   
			end if;
			Append(~M`Hecke`Eigenforms, mform);
			if mform`IsEisenstein then
			    M`Hecke`EisensteinSeries := mform;
			end if;
		end for;
	end if;

	// Save the name of the file from which this space was loaded.
	M`filename := filename;

	return M;
end intrinsic;


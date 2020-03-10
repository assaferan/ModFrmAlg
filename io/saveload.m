// Routines used for saving and loading data to/from disk.

// TODO: Update this script to accommodate for the updated accessor functions
//  by removing direct access via the ` substructure symbol.

import "path.m" : path;
// import "QQ/genus-QQ.m" : sortGenusQQ;
import "../neighbors/genus-CN1.m" : sortGenusCN1;

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
	file := path() cat filename;

	// If overwrite flag not set and file exists, display warning and
	//  immediately return.
	if not Overwrite and FileExists(file : ShowErrors := false) then
		print "WARNING: File not saved. Set the Overwrite parameter.";
		return;
	end if;

	// The inner form associated to the ambient quadratic space.
	innerForm := ChangeRing(M`L`quadSpace`innerForm, M`L`R);

	// The defining polynomial of the number field.
	f := DefiningPolynomial(BaseRing(innerForm));

	// The genus representatives.
	genus := [* *];
	if assigned M`genus then
		for idx in [1..#M`genus`Representatives] do
			// Shortcut to the current genus representative.
			L := M`genus`Representatives[idx];

			if M`L`quadSpace`deg eq 1 then
				// If we're over the rationals, we simply
				//  choose the basis of L.
				basis := Basis(L);
			else
				// Otherwise, we store the pseudobasis of L.
				basis := [*
					< [ Eltseq(b) : b in Basis(pb[1]) ],
					[ Eltseq(x) : x in Eltseq(pb[2]) ] >
						: pb in L`psBasis *];
			end if;

			// Add the appropriate basis to the genus list.
			Append(~genus, basis);
		end for;
	end if;

	// Valid dimensions for the Hecke matrices.
	dims := Keys(M`Hecke`Ts);

	// The Hecke matrice we've computed.
	hecke := [* *];

	for dim in dims do
		// The list of Hecke matrices for this dimension.
		list := [* *];

		// Retrieve complete list of Hecke matrices and ideals.
		Ts, Ps := HeckeOperators(M, dim);

		// A coupled list of Hecke matrices and their ideals.
		list := [* < Basis(Ps[i]), Ts[i] > : i in [1..#Ts] *];

		// Add this list to the ongoing list of Hecke matrices.
		Append(~hecke, < dim, list >);
	end for;

	// Initialize the eigenforms.
	eigenforms := [* *];

	// Build data structure for saving the eigenforms to disk.
	if assigned M`Hecke and assigned M`Hecke`Eigenforms then
		for f in M`Hecke`Eigenforms do
			if f`IsEigenform then
				Append(~eigenforms, < Eltseq(f`vec) >);
			end if;
		end for;
	end if;

	// Build the data structure that will be saved to file.
	data := [*
		< "POLY", f >,
		< "INNER", innerForm >,
		< "GENUS", genus >,
		< "HECKE", hecke >,
		< "ISOGENY", M`isogenyType >,
		< "EIGENFORMS", eigenforms >
	*];

	// Write data to file.
	Write(file, data, "Magma" : Overwrite := Overwrite);
end intrinsic;

intrinsic Load(filename::MonStgElt : ShowErrors := true) -> ModFrmAlg
{ Load an algebraic modular form from disk. }
	// The file where the data will be loaded.
	file := path() cat filename;

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

	if not IsDefined(array, "POLY") or
			not IsDefined(array, "INNER") or
			not IsDefined(array, "ISOGENY") then
		print "ERROR: Corrupt data.";
		return false;
	end if;

	// TODO: Something weird going on here, try to get this under control a
	//  bit more elegantly.

	// Build the number field we're working over.
	//K := NumberField(array["POLY"]);

//	if Degree(K) ne 1 then
	// The base ring of the inner form.
	K := BaseRing(array["INNER"]);

	// Assign the inner form.
	innerForm := array["INNER"];

	if Degree(K) eq 1 then
		K := NumberField(array["POLY"]);
		innerForm := ChangeRing(innerForm, K);
	end if;
		// If we're over the rationals, coerce base ring to K.
//		innerForm := ChangeRing(array["INNER"], K);
//	end if;

	// Assign the isogeny type.
	isogenyType := array["ISOGENY"];

	// Build the space of algebraic modular forms.
	// TODO: Refine the parameters to construct this appropriate space with
	//  specified weight and isogeny type.
	M := AlgebraicModularForms(innerForm);

	// Assign genus representatives.
	if IsDefined(array, "GENUS") and #array["GENUS"] ne 0 then
		// Retrive the list of genus representatives.
		reps := array["GENUS"];

		// Create a new genus symbol.
		genus := New(GenusSym);
		genus`Representatives := [];

		if M`L`quadSpace`deg eq 1 then
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

				// A basis of the ambient quadratic space.
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
					M`L`quadSpace, Matrix(basis), idls);

				// Add lattice to the list of genus reps.
				Append(~genus`Representatives, L);
			end for;
		end if;

		// Assign genus representative.
		genus`Representative := genus`Representatives[1];

		// Construct an associative array indexed by an invariant of
		//  the isometry classes.
/*
		if M`L`quadSpace`deg eq 1 then
			genus := sortGenusQQ(genus);
		else
*/
//		elif M`L`quadSpace`classNo eq 1 then
			genus := sortGenusCN1(genus);
//		else
//			print "ERROR: Class number 2+ not implemented.";
//			return false;
//		end if;

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
				M`Hecke`Ts[k][P] := entry[2];
			end for;
		end for;
	end if;

	if IsDefined(array, "EIGENFORMS") then
		// Retrieve the list for convenient access.
		list := array["EIGENFORMS"];

		if #list ne 0 then
			M`Hecke`Eigenforms := [* *];
		end if;

		for data in list do
                        // Construct an element of the modular space.
                        mform := New(ModFrmAlgElt);

                        // Assign parent modular space.
                        mform`M := M;

                        // Assign vector.
                        mform`vec := Vector(data[1]);

                        // Flag as cuspidal?
                        mform`IsCuspidal :=
				&+[ x : x in Eltseq(mform`vec) ] eq 0;

                        // Cusp forms are not Eistenstein.
                        mform`IsEisenstein := not mform`IsCuspidal;

			// Establish this as a Hecke eigenform.
                        mform`IsEigenform := true;

			Append(~M`Hecke`Eigenforms, mform);
		end for;
	end if;

	// Save the name of the file from which this space was loaded.
	M`filename := filename;

	return M;
end intrinsic;


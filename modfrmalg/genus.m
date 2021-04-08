freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         

                                                                            
   FILE: genus.m (class for all genus related data and computations)

   04/24/20: Modified default value of parameter BeCareful to false. 

   04/01/20: Removed call to ModFrmAlgInit from genus - 
             no need to construct the space to compute the genus.
             Added direct call to computeGenusRepsCN1

   03/10/20: started from the orthogonal modular forms structure
 
 ***************************************************************************/

// Here we list the intrinsics that this file defines
// Print(gen::GenusSym)
// GenusReps(M::ModFrmAlg) -> SeqEnum
// Representative(G::GenusSym) -> .
// Representatives(G::GenusSym) -> SeqEnum
// SetGenus(~M::ModFrmAlg, reps::SeqEnum[Lat])


// imports

import "../neighbors/genus-CN1.m" : computeGenusRepsCN1;
import "../neighbors/inv-CN1.m" : Invariant;

///////////////////////////////////////////////////////////////////
//                                                               //
//    GenusSym: The genus symbol object.                         //
//                                                               //
///////////////////////////////////////////////////////////////////


declare type GenusSym;
declare attributes GenusSym:
	// The lattice for which this genus symbol was initialized.
	Representative,

	// Representatives for the classes in this genus.
	Representatives,

	// A partition of the genus representatives.
	RepresentativesAssoc,

	// An ordered list of theta series for the genus representatives
	ThetaSeries;

// printing

intrinsic Print(gen::GenusSym) {}
	printf "Genus symbol of size %o.", #gen`Representatives;
end intrinsic;

// access

intrinsic GenusReps(M::ModFrmAlg
	: BeCareful := false, Force := false, Orbits := true) -> SeqEnum
{ Computes the genus representatives of the inner form associated to the
	   space of algebraic modular forms provided. }

        gram := IsOrthogonal(M) select 2 else 1;
        disc := Discriminant(Level(M) : Half, GramFactor := gram); 
        fac := Factorization(disc);
        is_sqrfree := &and[fa[2] eq 1 : fa in fac];
        computeGenusRepsCN1(M : BeCareful := BeCareful, Force := Force,
		    UseMass := not is_sqrfree);

	return M`genus`Representatives;
end intrinsic;

intrinsic Representative(G::GenusSym) -> .
{ Return the lattice used to construct this genus symbol. }
	return G`Representative;
end intrinsic;

intrinsic Representatives(G::GenusSym) -> SeqEnum
{ Return all lattices in the genus. }
	return G`Representatives;
end intrinsic;

// constructor from external data
intrinsic SetGenus(~M::ModFrmAlg, reps::SeqEnum[Lat] : GramFactor := 2)
{Set the Genus of M to a list of lattices.}
  M`genus := New(GenusSym);
  M`genus`Representative := Module(M);

  V_orig := ReflexiveSpace(Module(M));
  F := BaseRing(V_orig);
  
  lats := [];

  for rep in reps do
    lat := LatticeFromLat(rep : GramFactor := GramFactor);
    V := ReflexiveSpace(lat);
    V_F := AmbientReflexiveSpace(ChangeRing(InnerForm(V),F));
    pb := PseudoBasis(lat);
    idls := [Integers(F)!!p[1] : p in pb];
    basis := ChangeRing(Matrix([p[2] : p in pb]), F);
    lat := LatticeWithBasis(V_F, basis, idls);
    Append(~lats, lat);
  end for;

  M`genus`Representatives := lats;

  invs := AssociativeArray();
  for i in [1..#lats] do
    // Compute the invariant associated to this genus rep.
    inv := Invariant(lats[i]);

    // Assign an empty list to the invariant hash if it hasn't been
    //  assigned yet.
    if not IsDefined(invs, inv) then invs[inv] := []; end if;

    // Add to list.
    Append(~invs[inv], < lats[i], i >);
  end for;
  M`genus`RepresentativesAssoc := invs;
end intrinsic;

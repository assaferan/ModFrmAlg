//freeze;
/****-*-magma-******a********************************************************
                                                                            
                        Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
                   
   FILE: lattice.m

   Implementation file for hermitian lattice (over quaternion algebras) routines

   03/05/2020 : Created this file as a copy of the one from main package.
 
 ***************************************************************************/

// Here we list the intrinsics that this file defines

// !! TODO - add here the intrinsic list

// !! TODO : Should we make it a AlgAssVOrdLat ?

///////////////////////////////////////////////////////////////////
//                                                               //
//    AlgQuatOrdLat: Lattice over a quatenrion order object.     //
//                                                               //
///////////////////////////////////////////////////////////////////

declare type AlgQuatOrdLat;
declare attributes AlgQuatOrdLat:
	// The base ring.
	O,

	// The algebra.
	B,

	// The pseudobasis (only used when not over the rationals).
	psBasis,

        // The ambient hermitian space
        hSpace,
  
	// The discriminant ideal.
	Discriminant,

	// The p-maximal basis is not strictly-speaking a basis for the lattice,
	//  but instead a basis for the completed lattice at p. This is used to
	//  compute the affine reflexive space and thereby compute isotropic
	//  lines, etc.
	pMaximal,

	// The lattice pushed down to the integers. This is the same as L if
	//  and only if the base field is the rationals.
	ZLattice,

	// The automorphism group as a lattice over Z.
	AutomorphismGroup,

	// The special automorphism group as a lattice over Z.
	SpecialAutomorphismGroup,

	// The scale of the lattice.
	Scale,

	// The norm of the lattice.
	Norm,

	// The level of the lattice.
	Level,

	// An associative array storing reflexive spaces modulo primes.
	Vpp,

	// Jordan decomposition of the lattice at a prime.
	Jordan,

	// The spinor norms at specified prime ideals.
	SpinorNorm;

// adding some attributes to the existing lattice type Lat.

declare attributes Lat:
	// The auxiliary forms associated to this lattice.
	auxForms,

	// The basis of the lattice with coefficients in R.
	basisR,

	// The basis of the lattice with coefficients in Z.
	basisZ,

	// An associative array storing quadratic spaces modulo primes
	Vpp;

// Implementation of lattice routines.

intrinsic Parent(lat::AlgQuatOrdLat) {}
  PowerStructure(AlgQuatOrdLat);
end intrinsic;

// print

intrinsic Print(lat::AlgQuatOrdLat, level::MonStgElt) {}
   if level eq "Magma" then
     pb := PseudoBasis(lat);
     idls := [x[1] : x in pb];
     basis := Matrix([x[2] : x in pb]);
     V := HermitianSpace(lat);
     printf "LatticeWithBasis(%m, %m, %m)", V, basis, idls;
     return;
   end if;

// I don't yet have a good notion of a discriminant for a quaternion ideal
/*
   disc := "discriminant";
   
   printf "lattice whose %o has norm %o", disc,
     Norm(Discriminant(lat));
*/
   printf "lattice whose corresponding Z-lattice has discriminant %o", Discriminant(ZLattice(lat));
   if level eq "Maximal" then
     printf "%o", PseudoBasis(lat);
   end if;
end intrinsic;

// boolean operators

intrinsic 'eq'(lat1::AlgQuatOrdLat, lat2::AlgQuatOrdLat) -> BoolElt
{ Determine whether two lattices are equal. }
	return HermitianSpace(lat1) eq HermitianSpace(lat2) and
		ZLattice(lat1) eq ZLattice(lat2);
end intrinsic;

// access

intrinsic HermitianSpace(L::AlgQuatOrdLat) -> HermSpace
{ Returns the reflexive space of the lattice. }
	return L`hSpace;
end intrinsic;

intrinsic AmbientSpace(L::AlgQuatOrdLat) -> HermSpace
{ Returns the ambient hermitian space of the lattice. }
        return L`hSpace;
end intrinsic;

intrinsic PseudoBasis(L::AlgQuatOrdLat) -> SeqEnum[Tup]
{ Returns the pseudobasis for the underlying module structure. }
  if not assigned L`psBasis then
    error "No pseudbasis found";
  end if;
  return L`psBasis;
end intrinsic;

intrinsic BaseRing(L::AlgQuatOrdLat) -> AlgQuatOrd
{ Returns the base ring of the lattice. }
	return L`O;
end intrinsic;

intrinsic Basis(L::AlgQuatOrdLat) -> SeqEnum
{.}
  return [pb[2] : pb in PseudoBasis(L)];
end intrinsic;

intrinsic StandardLattice(hSpace::HermSpace) -> AlgQuatOrdLat
{ Builds the standard lattice for the given hermitian space. }
// Return the standard lattice for this space if it has already been
//  computed.
  if assigned hSpace`stdLat then return hSpace`stdLat; end if;

  // The standard basis.
  basis := Id(MatrixRing(BaseOrder(hSpace), Dimension(hSpace)));
  
  // Build the standard lattice.
  L := LatticeWithBasis(hSpace, basis);

  require IsIntegral(L) :
    "Standard Lattice is not integral for hermitian space!" ;

  // Assign the ZLattice.
  L`ZLattice := ZLattice(L : Standard := true);
  
  return L;
end intrinsic;

intrinsic LatticeWithBasis(hSpace::HermSpace, basis::Mtrx) -> AlgQuatOrdLat
{ Construct the lattice with the specified basis given by the rows of the
matrix provided. }
  // Make sure that the base algebra of the hermitian space and the base
  //  ring of the supplied basis agree.
  B := BaseAlgebra(hSpace);
  iso := IsIsomorphic(B, Algebra(BaseRing(basis)));

  require iso : "The base rings do not match.";
  basis := ChangeRing(basis, BaseAlgebra(hSpace));

  // Initialize the internal lattice structure.
  lat := New(AlgQuatOrdLat);

  // Assign the base algebra.
  lat`B := BaseAlgebra(hSpace);

  // Assign the base order.
  // The maximal order is no longer unique. We want to allow for any possible order
  //  lat`O := MaximalOrder(lat`B);
  lat`O := BaseOrder(hSpace);

  // Assign the pseudobasis.
  lat`psBasis := [< 1*lat`O, b > : b in Rows(basis)];

  // Assign the ambient reflexive space.
  lat`hSpace := hSpace;

  // Assign an empty associative array.
  lat`Vpp := AssociativeArray();

  // Assign an empty associative array.
  lat`Jordan := AssociativeArray();
  
  return lat;
end intrinsic;

intrinsic LatticeFromLat(L::Lat : GramFactor := 2) -> AlgQuatOrdLat
{ Builds an AlgQuatOrdLat structure from a native Lat structure. }
  // The inner form.
  innerForm := (2/GramFactor) * InnerProductMatrix(L);

  // The ambient reflexive space.
  Q := AmbientHermitianSpace(innerForm);

  // The basis for the lattice.
  basis := ChangeRing(Matrix(Basis(L)), BaseRing(Q));

  // Build the lattice and return it.
  return LatticeWithBasis(Q, basis);
end intrinsic;

intrinsic Dimension(L::AlgQuatOrdLat) -> RngIntElt
{ The dimension of the lattice. }
  return Dimension(HermitianSpace(L));
end intrinsic;

intrinsic LatticeWithBasis(hSpace::hSpace,
			   basis::AlgMatElt, idls::SeqEnum[AlgQuatOrdIdl]) -> AlgQuatOrdLat
{ Builds a lattice in an ambient hermitian space with the specified basis and
coefficient ideals. }
  // The dimension.
  dim := Dimension(hSpace);

  // Initialize the lattice data.
  lat := New(AlgQuatOrdLat);

  // Assign the basic properties.
  lat`hSpace := hSpace;
  lat`B := BaseRing(hSpace);
  lat`O := Integers(lat`B);

  basis := ChangeRing(basis, lat`B);
  
  idls := [lat`B!!I : I in idls];

  // assign the pseudobasis
  lat`psBasis := [<idls[i], Rows(basis)[i]> : i in [1..#idls]];
  
  // The associative array of affine reflexive spaces.
  lat`Vpp := AssociativeArray();

  // The associative array of Jordan decompositions.
  lat`Jordan := AssociativeArray();

  return lat;
end intrinsic;

intrinsic ChangeRing(lat::AlgQuatOrdLat, R::Rng) -> AlgQuatOrdLat
{.}
   pb := PseudoBasis(lat);

   B := Algebra(Order(R));
   idls := [B!!x[1] : x in pb];
   basis := ChangeRing(Matrix([x[2] : x in pb]), R);
   V := ChangeRing(HermitianSpace(lat), R);
   return LatticeWithBasis(V, basis, idls);
end intrinsic;

intrinsic ZLattice(lat::AlgQuatOrdLat : Standard := false) -> Lat
{ Push the lattice down to the integers. }
  
  // If we've already computed the ZLattice, return it.
  if assigned lat`ZLattice then return lat`ZLattice; end if;

  V := VectorSpace(HermitianSpace(lat));

  // Construct an R-basis for the lattice as a Z-module.
  basisR := &cat[ [ V!(x*pb[2]) : x in Basis(pb[1]) ]
		  : pb in PseudoBasis(lat) ];
  // Construct a Z-basis for the lattice as a Z-module.
  basisZ := Matrix([ &cat[ Eltseq(e) : e in Eltseq(b) ] : b in basisR ]);

  if Standard then
      // Build lattice as a Z-module in a rational quadratic space.
      lat`ZLattice := LatticeWithBasis(basisZ);

      // Assign the bases for this lattice.
      lat`ZLattice`basisR := basisR;
      lat`ZLattice`basisZ := basisZ;

      // Compute the auxiliary forms.
      auxForms := AuxForms(lat : Standard := Standard);
      
      // Assign the ambient inner form associated to this lattice.
      gram := auxForms[1];
  else
      // Assign the ambient inner form associated to this lattice.
      gram := lat`hSpace`stdLat`ZLattice`auxForms[1];
  end if;

  // Construct the ZLattice with basis in the correct quadratic space.
  lat`ZLattice := LatticeWithBasis(basisZ, ChangeRing(gram, Rationals())
				   : CheckPositive := false);

  // Assign the bases for the ZLattice.
  lat`ZLattice`basisR := basisR;
  lat`ZLattice`basisZ := basisZ;

  if Standard then
      lat`ZLattice`auxForms := AuxForms(lat : Standard := Standard);
  end if;

  return lat`ZLattice;
end intrinsic;

forward GramMatrixOfBasis;

intrinsic AuxForms(lat::AlgQuatOrdLat : Standard := false) -> SeqEnum
{ Compute the auxiliary forms associated to this lattice. }
  // Assign the ZLattice attribute if not yet assigned.
  if not assigned lat`ZLattice then
      lat`ZLattice := ZLattice(lat : Standard := Standard);
  end if;

  // As long as this isn't intended to become a standard lattice, return
  //  the auxiliary forms if they've already been computed.
  if not Standard and assigned lat`ZLattice`auxForms then
      return lat`ZLattice`auxForms;
  end if;

  // The base ring.
  R := BaseRing(lat);

  if (Type(R) eq RngInt) then
    return [ChangeRing(GramMatrixOfBasis(lat : Half := false),R)];
  end if;

  // The hermitian space associated to this lattice.
  V := HermitianSpace(lat);

  // The dimension.
  dim := Dimension(HermitianSpace(lat));

  // The degree of the field extension.
  deg := Degree(BaseRing(V));

  // The inner form of the ambient reflexive space.
  M := InnerForm(V);
  alpha := Involution(V);

  // The basis for the lattice over the rationals.
  basis := ZLattice(lat)`basisR;
  conj_basis := [alpha(b) : b in basis];

  // Compute a sequence of auxiliary pairings used to compute isometry
  //  of lattices over number field.
  phis := [ Matrix(deg*dim, deg*dim,
		   [ Trace((Matrix(z*x) * M * Transpose(Matrix(y)))[1,1])
		     : x in basis, y in conj_basis ]) : z in Basis(R) ];

  // Make sure that the lattice was pushed down to an integral one, and
  //  that the first bilinear pairing is symmetric and positive definite.
  // We no longer make sure of the conditions in the second line.
  try
      phis := [ ChangeRing(phi, Integers()) : phi in phis ];
      // !! TODO : in char. 2 check that we are alternating.
      assert Transpose(phis[1]) in [phis[1], -phis[1]];
  catch e
      require false: "Auxiliary forms are not of the correct form!";
  end try;
  
  return phis;
end intrinsic;

intrinsic Discriminant(lat::Lat) -> RngInt
{ Compute the discriminant ideal of the lattice. }
  // The dimension.
  dim := Dimension(lat);

  // Correction factor.
  factor := dim mod 2 eq 1 select 2 else 1;
  
  // The determinant of the lattice.
  det := Determinant(lat);

  return ideal< Integers() | det / factor >;
end intrinsic;

function pMaximalGram(L, pR : BeCareful := false, given_coeffs := [])
    if assigned L`pMaximal then
	// If the p-maximal data has been assigned, return it.
	if IsDefined(L`pMaximal, pR) then
	    return L`pMaximal[pR][1], L`pMaximal[pR][2];
	end if;
    else
	// If it consists of an empty array, create it.
	L`pMaximal := AssociativeArray();
    end if;

    // If we're over Q, we don't really need a p-maximal basis
    // for now, we just return the trivial basis, see that it works 
    if Type(BaseRing(L)) eq RngInt then
       vecs := Basis(L);
       gram := GramMatrix(L, vecs);
       L`pMaximal[pR] := < ChangeRing(gram, BaseRing(L)), Matrix(vecs),
	                    Denominator(Matrix(vecs))>;
       return L`pMaximal[pR][1], L`pMaximal[pR][2];
    end if;

    // The coefficient ideals for this lattice.
    idls := [ pb[1] : pb in PseudoBasis(L) ];

    // The pseudobasis vectors.
    basis := Basis(L);
    
    // Find a p-maximal basis.
    vecs := [];
    
    for i in [1..#idls] do
	// The generators of the coefficient ideal.
	gens := Generators(idls[i]);
	
	// Randomly choose a p-maximal vector.
	repeat
	    if IsEmpty(given_coeffs) then
		coeffs := [Random(11) - 5 : g in gens];
	    else
		coeffs := given_coeffs[i];
	    end if;
	    
            vec := &+[ gens[j] * coeffs[j] :
		       j in [1..#gens]] * basis[i];
	until not vec in pR * L;
	// for debugging
	if GetVerbose("AlgebraicModularForms") ge 3 then
	    printf "coeffs = %o\n", coeffs;
	end if;
	// Verify that the vectors were chosen properly.
	if BeCareful then
	    assert vec in L and not vec in pR * L;
	end if;
	
	// Add this vector to the list.
	Append(~vecs, vec);
    end for;
    
    gram := GramMatrix(L, vecs : Half := IsQuadratic(L));
    
    // Store the p-maximal basis for future use.
    L`pMaximal[pR] := < ChangeRing(2*gram, BaseRing(L)), Matrix(vecs),
                        Denominator(Matrix(vecs))>;
    
    // Return the Gram matrix, the basis, and its denominator
    return Explode(L`pMaximal[pR]);
end function;

intrinsic Level(lat::AlgQuatOrdLat) -> RngOrdFracIdl
{ Compute the level of the lattice. }
  // If the level has been computed, return it.
  if assigned lat`Level then return lat`Level; end if;

  // The coefficient ideals of the dual.
  idls := [ pb[1]^-1 : pb in PseudoBasis(lat) ];

  gram := GramMatrix(lat, Basis(lat) : Half := IsQuadratic(lat))^(-1);

  // The dimension.
  dim := Nrows(gram);

  a := Involution(HermitianSpace(lat));
  // In the orthogonal case, we want to divide by 2
  factor := IsQuadratic(lat) select 2 else 1; 
  
  // Compute the level of the lattice.
  lat`Level := (&+[ idls[i] * a(idls[i]) * gram[i,i]/factor : i in [1..dim ] ] +
		&+[ idls[i] * a(idls[j]) * gram[i,j]
		    : i,j in [1..dim] | i lt j ])^-1;
  
  // Return it.
  return lat`Level;
end intrinsic;

intrinsic Divisor(lat::AlgQuatOrdLat) -> RngOrdFracIdl
{ Compute the divisor ideal of the lattice. }
  // The coefficient ideals.
  idls := [ pb[1] : pb in PseudoBasis(lat) ];

  // The rank of the lattice.
  dim := #idls;

  // This is only implemented for ternary lattices.
  require dim eq 3: "Only implemented for ternary lattices.";

  gram := GramMatrix(lat, Basis(lat) : Half := IsQuadratic(lat));

  // Values of the Gram matrix for easy reference.
  a := gram[1,1] / 2; b := gram[2,2] / 2; c := gram[3,3] / 2;
  r := gram[2,3]; s := gram[1,3]; t := gram[1,2];
  
  // The (i,j)-cofactor ideals.
  A11 := (idls[2] * idls[3])^2 * (4*b*c - r^2);
  A12 := idls[1] * idls[2] * idls[3]^2 * (2*c*t - r*s);
  A13 := idls[1] * idls[2]^2 * idls[3] * (r*t - 2*b*s);
  A22 := (idls[1] * idls[3])^2 * (4*a*c - s^2);
  A23 := idls[1]^2 * idls[2] * idls[3] * (2*a*r - s*t);
  A33 := (idls[1] * idls[2])^2 * (4*a*b - t^2);

  // Return the divisor ideal.
  return A11 + A22 + A33 + 2*A12 + 2*A13 + 2*A23;
end intrinsic;

intrinsic Trace(p::RngOrdFracIdl, a::FldAut) -> RngOrdFracIdl
{Return the ideal generated by [g + a(g) : g in Generators(p)].}
  F := FixedField(a);
  return ideal<Integers(F) | [g + a(g) : g in Generators(p)]>;
end intrinsic;

intrinsic Trace(p::RngIntFracIdl, a::FldAut) -> RngIntFracIdl
{Return the ideal generated by [g + a(g) : g in Generators(p)].}
  F := FixedField(a);
  return FractionalIdeal([g + a(g) : g in Generators(p)]);
end intrinsic;

intrinsic Norm(p::RngOrdFracIdl, a::FldAut) -> RngOrdFracIdl
{Return the ideal generated by [g * a(g) : g in Generators(p)].}
  F := FixedField(a);
  return ideal<Integers(F) | [g * a(g) : g in Generators(p)]>;
end intrinsic;

intrinsic Norm(p::RngIntFracIdl, a::FldAut) -> RngIntFracIdl
{Return the ideal generated by [g * a(g) : g in Generators(p)].}
  F := FixedField(a);
  return FractionalIdeal([g * a(g) : g in Generators(p)]);
end intrinsic;

intrinsic Norm(lat::AlgQuatOrdLat) -> RngOrdFracIdl
{ Compute the norm of the lattice. }
  // If the norm has already been computed, return it.
  if assigned lat`Norm then return lat`Norm; end if;

  // The coefficient ideals.
  idls := [ pb[1] : pb in PseudoBasis(lat) ];

  gram := GramMatrix(lat, Basis(lat) : Half := IsQuadratic(lat));

  // The dimension.
  dim := Nrows(gram);

  a := Involution(HermitianSpace(lat));
  F := FixedField(a);
/*
  if Type(BaseRing(lat)) eq RngInt then
    return  &+[ ideal<Integers()| gram[i,i]> : i in [1..dim] ] +
	      &+[ ideal<Integers() | 2*gram[i,j] > : i,j in [1..dim] | i lt j ];
  end if;
*/
  // Compute the norm ideal for the lattice.
  lat`Norm := &+[ (F!gram[i,i]) * Norm(idls[i], a) : i in [1..dim] ] +
    &+[ Trace(gram[i,j] * idls[i] * a(idls[j]), a) : i,j in [1..dim]
		  | i lt j ];
  
  // Return the norm.
  return lat`Norm;
end intrinsic;

intrinsic GramMatrix(lat::AlgQuatOrdLat, vecs::SeqEnum[ModTupRngElt] :
		     Half := false) -> AlgMatElt
{.}
  // The underlying basis for lattice.
  basis := Matrix(vecs);

  // The involution of the reflexive space
  alpha := Involution(HermitianSpace(lat));

  F := BaseAlgebra(alpha);

  basis := ChangeRing(basis, F);

  // The Gram matrix for the underlying basis.
  gram := basis * InnerForm(HermitianSpace(lat)) *
    Transpose(alpha(basis));

  if Half then
    return 1/2*gram;
  end if;

  return gram;
end intrinsic;

intrinsic Scale(lat::AlgQuatOrdLat) -> RngOrdFracIdl
{ Compute the scale of the lattice. }
  // Return the scale if it has already been computed.
  if assigned lat`Scale then return lat`Scale; end if;

  // Extract the coefficient ideals.
  idls := [ pb[1] : pb in PseudoBasis(lat) ];

  gram := GramMatrix(lat, Basis(lat));
  
  // The dimension of the vector space.
  dim := Nrows(gram);

  a := Involution(HermitianSpace(lat));

  // Compute the scale of the lattice.
  lat`Scale := &+[gram[i,j] * idls[i] * a(idls[j]) : i,j in [1..dim]];

  // Return the scale.
  return lat`Scale;
end intrinsic;

// TODO - check that we have the right thing for number fields
// We actually return an isometric lattice 
intrinsic ScaledLattice(lat::AlgQuatOrdLat, alpha::FldElt) -> AlgQuatOrdLat
{The lattice similar to L with Gram matrix scaled by alpha.}
  gram := GramMatrixOfBasis(lat : Half := false);
  form := alpha * gram;
  V_new := AmbientHermitianSpace(form); 
  return StandardLattice(V_new);
end intrinsic;

intrinsic ElementaryDivisors(lambda::AlgQuatOrdLat, pi::AlgQuatOrdLat) -> SeqEnum
{.}
  error "Not implemented!";
  return [];
end intrinsic;

intrinsic Discriminant(lambda::AlgQuatOrdLat, pi::AlgQuatOrdLat) -> RngOrdFracIdl
{.}
  return &*ElementaryDivisors(lambda, pi);
end intrinsic;

intrinsic Discriminant(lat::AlgQuatOrdLat) -> RngOrdFracIdl
{ Compute the discriminant of the lattice. }
  // Return the discriminant if it's already been computed.
  if not assigned lat`Discriminant then 
     lat`Discriminant := Discriminant(DualLattice(lat), lat);
  end if;

  ret := lat`Discriminant;

  if IsQuadratic(lat) and IsOdd(Rank(lat)) then
    ret := 1/2*ret;
  end if;

  return ret;
end intrinsic;


intrinsic IntersectionLattice(lat1::AlgQuatOrdLat, lat2::AlgQuatOrdLat) -> AlgQuatOrdLat
{ Computes the intersection lattice of the two specified lattices. }
  // Make sure both lattices belong to the same ambient hermitian space.
  require HermitianSpace(lat1) eq HermitianSpace(lat2):
		"Both lattices must belong to the same reflexive space.";
  error "Not Implemented!";
  return lat1;
end intrinsic;

intrinsic Index(lat1::AlgQuatOrdLat, lat2::AlgQuatOrdLat) -> RngOrdFracIdl
{ Compute the index of Pi in Lambda. }
  // Ensure both lattices reside in the same ambient hermitian space.
  require HermitianSpace(lat1) eq HermitianSpace(lat2):
		"Both lattices must belong to the same reflexive space.";

  index :=  &*ElementaryDivisors(lat1, lat2);

  // Make sure this is an integral ideal
  assert Denominator(index) eq 1;

  return index;

  // old code - good for orthogonal case only
  
  // Compute discriminants.
  disc1 := Discriminant(lat1);
  disc2 := Discriminant(lat2);

  // The quotient of the two discriminants.
  quo := disc2 / disc1;

  // Make sure this is an integral ideal.
  assert Denominator(quo) eq 1;

  // Problem - quo is a square only in the quadratic case.
  // In the unitary case, it is of the form I * alpha(I)
  // and one cannot use only quo to determine I

  // Compute the square root.
  sq, root := IsSquare(quo);

  // Make sure the square root is valid.
  assert sq;

  return root;
end intrinsic;

intrinsic IsIsometric(lat1::AlgQuatOrdLat, lat2::AlgQuatOrdLat :
		      Special := false, BeCareful := false) -> BoolElt, Mtrx
{ Determines whether the two specified lattices are isometric. }
  // Retrieve the ZLattices for each lattice.
  L1 := ZLattice(lat1);
  L2 := ZLattice(lat2);

  // Check for isometry.
  iso, f := IsIsometric(L1, AuxForms(lat1), L2, AuxForms(lat2));

  if not iso then return false, _; end if;

  f := PullUp(Matrix(f), lat1, lat2 : BeCareful := BeCareful);
  MnF := Parent(f);
  F := BaseRing(MnF);
  n := Dimension(lat1);
  G := GL(n,F);
  
  // Currently, this only works for O and SO, where det in -1,1
  if Special and Determinant(f) eq -1 then
      // Look at the generators of the automorphism group of the
      //  first lattice.
      gens := [Transpose(g) : g in Generators(AutomorphismGroupOverField(lat1, G))];
      
      // If any of the generators have determinant -1, then we can
      //  compose f and g in such a way to produce a proper isometry.
      for g in gens do
	  if Determinant(g) eq -1 then
	      return true,
		     f*Matrix(g);
//		     PullUp(Matrix(f*g), lat1, lat2 :
//			    BeCareful := BeCareful);
	  end if;
      end for;

      // Same as above.
      gens := [Transpose(g) : g in Generators(AutomorphismGroupOverField(lat2, G))];
      for g in gens do
	  if Determinant(g) eq -1 then
	      return true,
		     Matrix(g)*f;
//		     PullUp(Matrix(g*f), lat1, lat2 :
//			    BeCareful := BeCareful);
	  end if;
      end for;
      
      // No generators of determinant -1 found, therefore these two
      //  lattices are not properly isometric.
      return false, _;
  end if;

  return iso,f;
	 //PullUp(Matrix(f), lat1, lat2 : BeCareful := BeCareful);
end intrinsic;

intrinsic AutomorphismGroup(lat::AlgQuatOrdLat : Special := false) -> SeqEnum
{ Computes the automorphism group of the specified lattice. }
  if Special then
      vprintf AlgebraicModularForms, 2:
         "In AutomorphismGroup, with Special flag.\n";
      if assigned lat`SpecialAutomorphismGroup then
	  return lat`SpecialAutomorphismGroup;
      end if;
      vprintf AlgebraicModularForms, 2:
	"Computing the regular automorphism group.\n";
      aut := AutomorphismGroup(lat);
      // Problem - this takes too long
      // return sub<aut |[x : x in aut | Determinant(x) eq 1]>;
      // This is to get the group {+-1}
      C2, phi := UnitGroup(Integers());
      vprintf AlgebraicModularForms, 2:
	"Defining determinant.\n"; 
      det_gens := [Determinant(aut.i) : i in [1..NumberOfGenerators(aut)]];
      det := hom<aut -> C2 | [x @@ phi : x in det_gens]>;
      vprintf AlgebraicModularForms, 2:
	"Finding kernel.\n"; 
      special_aut := Kernel(det);
      vprintf AlgebraicModularForms, 2:
	"Done. Saving and returning.\n";
      // Save it for further use.
      lat`SpecialAutomorphismGroup := special_aut;
      return special_aut;
  end if;

  // Return the automorphism group if it has already been computed.
  if assigned lat`AutomorphismGroup then
      return lat`AutomorphismGroup;
  end if;
  
  // Compute the automorphism group of this lattice.
  aut := AutomorphismGroup(ZLattice(lat), AuxForms(lat));
  
  // Save it for further use.
  lat`AutomorphismGroup := aut;
  
  return lat`AutomorphismGroup;
end intrinsic;

function special_subgroup(gamma)
    F := BaseRing(gamma);
    C2 := sub<GL(1, F) | [-1]>;
    h := hom<gamma -> C2 | [C2![Determinant(gamma.i)] : i in [1..Ngens(gamma)]]>;
    return Kernel(h); 
end function;

intrinsic AutomorphismGroupOverField(lat::AlgQuatOrdLat, G::GrpMat : Special := false) -> SeqEnum
{ Computes the automorphism group of the specified lattice. }
  Z_aut_grp := AutomorphismGroup(lat);
  gens := [Transpose(PullUp(Matrix(g), lat, lat)) : g in Generators(Z_aut_grp)];
  G := sub<G | gens>;
  if Special then
      return special_subgroup(G);
  end if;
  return G;
end intrinsic;

intrinsic IsFree(L::AlgQuatOrdLat) -> BoolElt
{ Determines whether the lattice is a free lattice or not. }
  // The pseudobasis for the lattice.
  psBasis := PseudoBasis(L);

  // The lattice is free if and only if the product of its coefficient
  //  ideals is principal.
  value := IsPrincipal(&*[ pb[1] : pb in psBasis ]);
  
  // Return value.
  return value;
end intrinsic;

intrinsic FreeBasis(L::AlgQuatOrdLat) -> SeqEnum
{ Computes and returns a basis for a free lattice. }
  // Require the lattice to be free.
  require IsFree(L): "Lattice must be free.";

  // The reflexive space.
  V := HermitianSpace(L);

  // The pseudobasis for the lattice.
  psBasis := PseudoBasis(L);

  // Extract the bases and coefficient ideals.
  idls := [ pb[1] : pb in psBasis ];
  basis := [ pb[2] : pb in psBasis ];

  // Dimension of the lattice.
  dim := Dimension(L);

  for i in [1..dim-1] do
      // Determine whether the current coefficient ideal is principal.
      check, elt := IsPrincipal(idls[i]);	

      // If principal, then scale the basis with the generator.
      if check then
	  idls[i] /:= idls[i];
	  basis[i] *:= elt;
	  continue;
      end if;
      
      // Convert the coefficient ideals into integral ideals.
      aa := Denominator(idls[i]); A := aa * idls[i];
      bb := Denominator(idls[i+1]); B := bb * idls[i+1];
      assert IsIntegral(A) and IsIntegral(B);
      
      // Generators of idls[i].
      gs := Generators(A);
      
      // Find elements according to Cohen's Proposition 1.3.12.
      repeat
	  repeat x := Random(5); y := Random(5);
	  until x ne 0 and y ne 0;
	  a := x * gs[1] + y * gs[2];
      until IsIntegral(a * idls[i]^-1) and
	    Factorization(a*A^-1 + B) eq [];
      
      // Construct a matrix so that we can apply HNF.
      C := Matrix([ Eltseq(x) : x in Basis(a*A^-1) cat Basis(B) ]);
      C := ChangeRing(C, Integers());
      
      // Perform an HNF.
      H, U := HermiteForm(C);
      
      // Verify that the top half of H is the identity matrix.
      assert Submatrix(H,[1..#gs],[1..#gs]) eq 1;
      
      // Find elements e and f following Cohen Algorithm 1.3.2.
      X := Submatrix(U, [1..1], [1..#gs]);
      AA := Matrix([ Eltseq(x) : x in Basis(a*A^-1) ]);
      AA := ChangeRing(AA, Integers());
      e := Order(A) ! Eltseq(X * AA);
      f := 1 - e;

      // Verify that the elements we chose are in the correct ideals.
      assert e in a * A^-1 and f in B;

      // Coefficients according to Cohen's Proposition 1.3.12.
      b := f / bb;
      c := (Order(B)!(-1)) * bb;
      d := e / a;
      
      // Verify that these elements belong the correct ideals.
      assert a*d - b*c eq 1;
      assert a in idls[i];
      assert b in idls[i+1];
      assert c in idls[i+1]^-1;
      assert d in idls[i]^-1;

      // The new bases and coefficient ideals.
      vec1 := a * basis[i] + b * basis[i+1];
      vec2 := c * basis[i] + d * basis[i+1];
      basis[i] := vec1;
      basis[i+1] := vec2;
      idls[i+1] *:= idls[i];
      idls[i] /:= idls[i];
  end for;
  
  // Confirm that the last ideal is principal.
  check, elt := IsPrincipal(idls[#idls]);
  assert check;

  // Update the last basis element.
  basis[#idls] *:= elt;
  
  assert LatticeWithBasis(V, Matrix(basis)) eq L;

  return basis;
end intrinsic;

intrinsic PullUp(g::AlgMatElt, Lambda::AlgQuatOrdLat, Pi::AlgQuatOrdLat :
		 BeCareful := false) -> AlgMatElt
  {Takes an isometry g : Pi -> Lambda and reexpresses it as an L-linear map gV : V -> V.}

  if Type(BaseRing(Lambda)) eq RngInt then
    return ChangeRing(BasisMatrix(Pi), Rationals())^(-1)*
           ChangeRing(g,Rationals())*
           ChangeRing(BasisMatrix(Lambda), Rationals());
  end if;

  LambdaZZ := ZLattice(Lambda);
  LambdaZZAuxForms := AuxForms(Lambda);
  R := BaseRing(Lambda);					  
  PiZZ := ZLattice(Pi);
  PiZZAuxForms := AuxForms(Pi);   
  BL := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Rows(LambdaZZ`basisZ)]);
  BP := Matrix([&cat[Eltseq(z) : z in Eltseq(y)] : y in Rows(PiZZ`basisZ)]);
  m := Dimension(Lambda);
  V := VectorSpace(AmbientSpace(Lambda));
  L := BaseField(V);
  d := Degree(L);
  rows := [];
  for i in [1..m] do
    v := Vector(&cat[Eltseq(x) : x in Eltseq(V.i)]);
    rowQ := Eltseq(v*BP^-1*(Parent(BL)!g)*BL);
    rowL := Vector([L!rowQ[j*d+1..(j+1)*d] : j in [0..m-1]]); 
    Append(~rows,rowL);
  end for;
  
  ans := Matrix(rows);
  
  if BeCareful then
    alpha := Involution(HermitianSpace(Lambda));
    print "gV maps Pi into Lambda?", &and[ChangeRing(x,L)*ans in Lambda :
					x in PiZZ`basisR];
    print "gV respects the inner product?", InnerProductMatrix(V) eq ans*InnerProductMatrix(V)*alpha(Transpose(ans));
  end if;
  
  return ans;
end intrinsic;

// functions for a-maximal lattices

// This returns the Gram Matrix in Kirschmer's convention
// so we halve the matrix unless explicitly stated otherwise in the quadratic case
function GramMatrixOfBasis(L : Half := true)
  P:= PseudoBasis(L);
  U:= Universe(P);
  C:= [ U[1] | p[1]: p in P ];
  B:= [ U[2] | p[2]: p in P ] ;
  return GramMatrix( L, B : Half := Half and IsQuadratic(L)), C, B;
end function;

intrinsic DualLattice(L::AlgQuatOrdLat) -> AlgQuatOrdLat
{return the dual of the lattice L - lattice L^# such that <L,L^#> = ZZ_F}
  V := HermitianSpace(L);
  G, C, B := GramMatrixOfBasis(L : Half := false);
  if #B eq 0 then return L; end if;	// L==0
  GI:= G^-1;
  BB:= GI * Matrix(B);
  a:= Involution(V);

  error "Dual lattice not implemented!";
  return LatticeWithBasis(V, BB, [a(c)^(-1) : c in C]);
end intrinsic;

intrinsic '*'(a::FldRatElt, L::AlgQuatOrdLat) -> AlgQuatOrdLat
{.}
  P:= PseudoBasis(L);
  U:= Universe(P);
  C:= [ U[1] | p[1]: p in P ];
  B:= [ U[2] | p[2]: p in P ];
  V := HermitianSpace(L);
  return LatticeWithBasis(V, a*Matrix(B), C);
end intrinsic;

intrinsic '*'(a::RngInt, L::Lat) -> Lat
{.}
  return Norm(a)*L;
end intrinsic;

intrinsic '*'(a::RngIntFracIdl, L::Lat) -> Lat
{.}
  return Norm(a)*L;
end intrinsic;

intrinsic '*'(a::RngOrdFracIdl, L::AlgQuatOrdLat) -> AlgQuatOrdLat
{.}
  P:= PseudoBasis(L);
  U:= Universe(P);
  C:= [ U[1] | p[1]: p in P ];
  B:= [ U[2] | p[2]: p in P ];
  V := HermitianSpace(L);
  return LatticeWithBasis(V, Matrix(B), [a*c : c in C]);
end intrinsic;

intrinsic 'subset'(lambda::ModDedLat, pi::ModDedLat) -> BoolElt
{.}
  error "Not Implemented";
  return false;
end intrinsic;

intrinsic DualLattice(L::AlgQuatOrdLat, a::RngOrdFracIdl) -> AlgQuatOrdLat
{.}
  return a * DualLattice(L);
end intrinsic;

intrinsic Rank(L::AlgQuatOrdLat) -> RngIntElt
{The rank or dimension of the lattice L}
  return #L`psBasis;
end intrinsic;

intrinsic IsZero(L::AlgQuatOrdLat) -> BoolElt
{Tests if the lattice L is zero}
  return Rank(L) eq 0;
end intrinsic;

intrinsic Degree(L::AlgQuatOrdLat) -> RngIntElt
{The degree of the lattice L}
  return #L`psBasis;
end intrinsic;

intrinsic IsFull(L::AlgQuatOrdLat) -> BoolElt
{Returns true if the lattice is of full rank}
  return Dimension(L) eq Degree(L);
end intrinsic;

intrinsic InnerProductMatrix(L::AlgQuatOrdLat) -> Mtrx
{Returns the inner product matrix of the lattice L}
  return InnerForm(HermitianSpace(L));
end intrinsic;

// check if this still works for hermitian forms
function MyDiagonal(L, Ambient)
  if Ambient and not IsFull(L) then
    return Diagonal(OrthogonalizeGram(InnerProductMatrix(L)));
  else
      F:= IsFull(L) select InnerProductMatrix(L) else
          GramMatrix(L, Basis(L) : Half := IsQuadratic(L));
      diagonal:= Diagonal(OrthogonalizeGram(F));
  end if;
  return diagonal;
end function;

// The even HilbertSymbol code

// We first start with our implementation of Alg. 6.2 -- 6.5 of
// John Voight, Characterizing quaternion rings over an arbitrary base, J. Reine Angew. Math. 657 (2011), 113-134.
function SolveCongruence(a,b,p)
  //assert Valuation(a,p) eq 0;
  //assert Valuation(b,p) eq 1;
  pi:= PrimitiveElement(p);
  k, h:= ResidueClassField(p);
  y:= 1/(SquareRoot(a @ h) @@ h); z:= 0;
  ee:= 2*RamificationIndex(p);
  told:= -1;
  while true do
    N:= 1 - a*y^2 - b*z^2;
    t:= Valuation(N, p); assert t gt told; told:= t;
    if t ge ee then return y,z; end if;
    w:= pi^(t div 2);
    if IsEven(t) then
      y +:= SquareRoot((N/(a*w^2)) @ h) @@ h * w;
    else
      z +:= SquareRoot((N/(b*w^2)) @ h) @@ h * w;
    end if;
  end while;
end function;

// Decide if a*x^2=1 mod p^e
// This is a variant of O'Meara ???. The code assumes that 0 <= e <= 2*RamIdx(p)
function CanLiftSquare(a,p,e)
  assert Valuation(a,p) eq 0;
  if Valuation(a-1, p) ge e then return true, Order(p) ! 1, e; end if;
  aold:= a;
  pi:= PrimitiveElement(p);
  k, h:= ResidueClassField(p);
  x:= SquareRoot( (a @ h)^-1 ) @@ h;
  a *:= x^2;
  t:= Valuation(a-1, p);
  while t lt e and IsEven(t) do
    s:= SquareRoot(h((a-1)/pi^t));
    s:= 1+(s@@h)*pi^(t div 2);
    a /:= s^2;
    x := x/s;
    tt:= Valuation(a-1, p);
    assert tt gt t;
    t:= tt;
  end while;
  t:= Min(t,e);
  assert Valuation(aold*x^2-1, p) ge t;
  return t eq e, x, t;
end function;

function SolveCongruence2(a,b,p)
  if Valuation(b, p) eq 1 then 
    y,z:= SolveCongruence(a,b,p);
    return y,z,0;
  end if;
  
  e:= RamificationIndex(p);
  pi:= PrimitiveElement(p);
  oka, a0, t:= CanLiftSquare(a, p, e);
  if oka then
    okb, b0, t:= CanLiftSquare(b, p, e);
    if okb then return a0, b0, a0*b0; end if;
    bt:= (b-(1/b0)^2) /pi^t;
    y, z:= SolveCongruence(b, -pi*bt/a, p);
    w:= pi^(t div 2);
    return w*b0/z, b0, y*w*b0/z;
  else
    at:= (a-(1/a0)^2) /pi^t;
    y, z:= SolveCongruence(a, -pi*at/b, p);
    w:= pi^(t div 2);
    return a0, w*a0/z, y*w*a0/z;
  end if;
end function;

normalize:= function(a, p)
  vala:= Valuation(a, p);
  n:= vala div 2;
  if n ne 0 then a /:= PrimitiveElement(p)^(2*n); vala -:= 2*n; end if;
  assert Valuation(a, p) eq vala and vala in {0,1};
  return a, vala;
end function;

intrinsic MyEvenHilbertSymbol(a::FldElt,b::FldElt,p::RngInt) -> RngIntElt
{}
  a, vala:= normalize(a, p);
  b, valb:= normalize(b, p);
  if vala eq 1 then
    if valb eq 1 then
      a:= (-a*b) / PrimitiveElement(p)^2;
    else
      x:= a; a:= b; b:= x;
    end if;
  end if;

  // lift solution to precision 2e
  y,z,w:= SolveCongruence2(a,b,p);
  nrm:= 1-a*y^2-b*z^2+a*b*w^2;
  assert Valuation(nrm, p) ge 2*RamificationIndex(p);
  tmp:= (b*z)^2*a + (a*y)^2*b;

  if tmp eq 0 or IsEven(Valuation(tmp, p)) then 
    res:= 1;
  else
    k,h:= ResidueClassField(p);
    res:= not IsIrreducible(Polynomial([k| (nrm/4)@h,-1,1])) select 1 else -1; 
  end if;
  //assert res eq HilbertSymbol(a,b,p);
  return res;
end intrinsic;

intrinsic MyEvenHilbertSymbol(a::FldElt,b::FldElt,p::RngOrdIdl) -> RngIntElt
{}
  a, vala:= normalize(a, p);
  b, valb:= normalize(b, p);
  if vala eq 1 then
    if valb eq 1 then
      a:= (-a*b) / PrimitiveElement(p)^2;
    else
      x:= a; a:= b; b:= x;
    end if;
  end if;

  // lift solution to precision 2e
  y,z,w:= SolveCongruence2(a,b,p);
  nrm:= 1-a*y^2-b*z^2+a*b*w^2;
  assert Valuation(nrm, p) ge 2*RamificationIndex(p);
  tmp:= (b*z)^2*a + (a*y)^2*b;

  if tmp eq 0 or IsEven(Valuation(tmp, p)) then 
    res:= 1;
  else
    k,h:= ResidueClassField(p);
    res:= not IsIrreducible(Polynomial([k| (nrm/4)@h,-1,1])) select 1 else -1; 
  end if;
  //assert res eq HilbertSymbol(a,b,p);
  return res;
end intrinsic;

intrinsic MyHilbertSymbol(a::FldRatElt, b::FldRatElt, pR::RngInt) -> RngIntElt
{The Hilbert symbol of a and b at p}
  if IsOne(a) or IsOne(b) then return 1; end if;
  require not IsZero(a) and not IsZero(b): "The elements must be non-zero";
  require IsPrime(pR): "The ideal must be prime";
  p := Norm(pR);
  return Minimum(p) ne 2 select HilbertSymbol(a,b,p) else MyEvenHilbertSymbol(a,b,pR);
end intrinsic;

intrinsic MyHilbertSymbol(a::FldAlgElt, b::FldAlgElt, p::RngOrdIdl) -> RngIntElt
{The Hilbert symbol of a and b at p}
  if IsOne(a) or IsOne(b) then return 1; end if;
  require not IsZero(a) and not IsZero(b): "The elements must be non-zero";
  require IsPrime(p): "The ideal must be prime";
  return Minimum(p) ne 2 select HilbertSymbol(a,b,p) else MyEvenHilbertSymbol(a,b,p);
end intrinsic;

// Isometry testing over the field of fractions
HS:= func<a,b,p | Type(p) eq RngIntElt select HilbertSymbol(a/1,b/1,p) else MyHilbertSymbol(a/1,b/1,p) >;
Hasse:= func< D, p | &*[ Integers() | HS(D[i], &*D[ [i+1..n] ], p) : i in [1..n-1] ] where n:= #D >;

intrinsic WittInvariant(L::AlgQuatOrdLat, p::RngInt :
			AmbientSpace:= false) -> RngIntElt
{The Witt invariant of L at p}
  R:= Order(p);
  require R cmpeq BaseRing(L) and IsPrime(p):
    "The second argument must be a prime ideal of the base ring of the lattice";
  h:= Hasse(MyDiagonal(L, AmbientSpace), p);
  Det:= Determinant(GramMatrixOfBasis(L));
  K:= NumberField(R);
  c:= K ! case < Degree(L) mod 8 |
	       3: -Det, 4: -Det, 5: -1, 6: -1, 7: Det, 0: Det, default : 1 >;
  return h * HS(K ! -1, c, p);
end intrinsic;

intrinsic WittInvariant(L::AlgQuatOrdLat, p::RngOrdIdl :
			AmbientSpace:= false) -> RngIntElt
{The Witt invariant of L at p}
  R:= Order(p);
  require R cmpeq BaseRing(L) and IsPrime(p):
    "The second argument must be a prime ideal of the base ring of the lattice";
  h:= Hasse(MyDiagonal(L, AmbientSpace), p);
  Det:= Determinant(GramMatrixOfBasis(L));
  K:= NumberField(R);
  c:= K ! case < Degree(L) mod 8 |
	       3: -Det, 4: -Det, 5: -1, 6: -1, 7: Det, 0: Det, default : 1 >;
  return h * HS(K ! -1, c, p);
end intrinsic;

function GuessMaxDet(L, p)
  m:= Rank(L); n:= m div 2;
  G := GramMatrixOfBasis(L);
  d:= Determinant(G);
  e:= 2*Valuation(Order(p) ! 2, p);
  if IsOdd(m) then
    v:= Valuation(d, p) mod 2;
    v:= WittInvariant(L, p) eq 1 select v-e*n else 2-v-e*n;
  else
    if IsOdd( (m*(m-1)) div 2 ) then d := -d; end if;
    qd:= (Type(p) eq RngInt) select QuadraticDefect(d, Norm(p)) else
         QuadraticDefect(d, p);
    if Type(qd) eq Infty then
      v:= WittInvariant(L, p) eq 1 select -e*n else 2-e*n;
    else		// Wrong? Fix scaling \alpha
      vd:= Valuation(d, p);
      v:= vd - 2*(qd div 2) + e*(1-n);
      //if IsEven(vd) and qd eq vd+e and WittInvariant(L,p) eq -1 then v:= v+2; end if;
/*K:= NumberField(BaseRing(L));
F:= ext< K | Polynomial([-d,0,1]) >;
ram:= IsRamified(p, Integers(F));
assert  (IsEven(vd) and qd eq vd+e) eq not ram;*/
      if IsEven(vd) and qd eq vd+e and WittInvariant(L,p) eq -1 then v:= -e*n+2; end if;
    end if;
  end if;
  // In the quadratic case  We add e*n to obtain the determinant of the matrix
  // of the bilinear form (which corresponds to the discriminant)
  if IsQuadratic(L) then v +:= e*n; end if;
  return v;
end function;

intrinsic Lattice(V::HermSpace, L::ModDed) -> AlgQuatOrdLat
{.}
  pb := PseudoBasis(L);
  I := [ p[1] : p in pb];
  B := [ p[2] : p in pb];
  return LatticeWithBasis(V, Matrix(B), I);
end intrinsic;

intrinsic Lattice(V::HermSpace, L::Lat) -> AlgQuatOrdLat
{.}
  return LatticeWithBasis(V, BasisMatrix(L));
end intrinsic;

intrinsic LocalBasis(M::ModDed, p::RngOrdIdl : ModuleType:= "") -> []
{A basis of a free module that coincides with M at the prime ideal p}
  require Order(p) cmpeq BaseRing(M) : "Incompatible arguments";
  require ModuleType in {"", "Submodule", "Supermodule"} : "Type must be \"Submodule\" or \"Supermodule\" when specified";
  if ModuleType eq "" then
    pi:= UniformizingElement(p);
  end if;
  B:= [ EmbeddingSpace(M) | ];
//  B:= [ VectorSpace(FieldOfFractions(BaseRing(M)), Degree(M)) | ];
  for pp in PseudoBasis(M) do
    g:= Generators(pp[1]);
    if #g eq 1 then x:= g[1];
    elif ModuleType eq "" then x:= pi^Valuation(pp[1], p);
    else
      Fact:= Factorization(pp[1]);
      Fact:= ModuleType eq "Submodule" select [ f: f in Fact | f[1] eq p or f[2] gt 0 ]
                                   else [ f: f in Fact | f[1] eq p or f[2] lt 0 ];
      if forall{ f: f in Fact | f[1] ne p } then Append(~Fact, <p, 0>); end if;
      x:= WeakApproximation([ f[1] : f in Fact ], [ f[2] : f in Fact ]);
    end if;
    assert Valuation(x, p) eq Valuation(pp[1], p);
    Append(~B, pp[2]*x);
  end for;
  return B;
end intrinsic;

intrinsic LocalBasis(M::Lat, p::RngInt : ModuleType:= "") -> []
{A basis of a free module that coincides with M at the prime ideal p}
  require Order(p) cmpeq Integers(BaseRing(M)) : "Incompatible arguments";
  require ModuleType in {"", "Submodule", "Supermodule"} : "Type must be \"Submodule\" or \"Supermodule\" when specified";
  if ModuleType eq "" then
    pi:= Norm(p);
  end if;
  B := [AmbientSpace(M)| ];

  for pp in PseudoBasis(M) do
    g:= Generators(pp[1]);
    if #g eq 1 then x:= g[1];
    elif ModuleType eq "" then x:= pi^Valuation(pp[1], p);
    else
      Fact:= Factorization(pp[1]);
      Fact:= ModuleType eq "Submodule" select [ f: f in Fact | f[1] eq p or f[2] gt 0 ]
                                   else [ f: f in Fact | f[1] eq p or f[2] lt 0 ];
      if forall{ f: f in Fact | f[1] ne p } then Append(~Fact, <p, 0>); end if;
      x:= WeakApproximation([ f[1] : f in Fact ], [ f[2] : f in Fact ]);
    end if;
    assert Valuation(x, p) eq Valuation(pp[1], p);
    Append(~B, pp[2]*x);
  end for;
  return B;
end intrinsic;

intrinsic IsHermitian(L::AlgQuatOrdLat) -> BoolElt
{.}
  return not IsIdentity(Involution(HermitianSpace(L)));
end intrinsic;

intrinsic IsIntegral(L::AlgQuatOrdLat, p::RngIntElt) -> BoolElt
{.}
  return IsIntegral(L, ideal<Integers() | p>);
end intrinsic;

// Duplicating for rational field
intrinsic IsIntegral(L::AlgQuatOrdLat, p::RngInt) -> BoolElt
{.}
  val2:= Valuation(2, p);
  G, C := GramMatrixOfBasis(L);
  D := Diagonal(G);
  alpha := Involution(HermitianSpace(L));
  min_diag := Minimum([Valuation(C[i],p) + Valuation(alpha(C[i]),p) +
		       Valuation(D[i],p) : i in [1..#C]]);
  min_val := Minimum([Valuation(C[i],p) + Valuation(alpha(C[j]),p)
		      + Valuation(G[i,j],p) : i, j in [1..#C]]);
  return (min_val ge -val2) and (min_diag ge 0);
end intrinsic;

intrinsic IsIntegral(L::AlgQuatOrdLat, p::RngOrdIdl) -> BoolElt
{.}
  val2:= Valuation(BaseRing(L)!2, p);
  G, C := GramMatrixOfBasis(L);
  D := Diagonal(G);
  alpha := Involution(HermitianSpace(L));
  min_diag := Minimum([Valuation(C[i],p) + Valuation(alpha(C[i]),p) +
		       Valuation(D[i],p) : i in [1..#C]]);
  min_val := Minimum([Valuation(C[i],p) + Valuation(alpha(C[j]),p)
		      + Valuation(G[i,j],p) : i, j in [1..#C]]);
  return (min_val ge -val2) and (min_diag ge 0);
end intrinsic;

intrinsic IsIntegral(L::AlgQuatOrdLat) -> BoolElt
{.}
  R := BaseRing(BaseRing(L));
  above_2 := {p[1] : p in Factorization(ideal<R|2>)};
  bad_primes := BadPrimes(L) join above_2;
  //  return &and[IsIntegral(L,p) : p in BadPrimes(L)];
  return &and[IsIntegral(L,p) : p in bad_primes];
end intrinsic;

intrinsic IsMaximalIntegral(L::AlgQuatOrdLat, p::RngIntElt) -> BoolElt, AlgQuatOrdLat
{Checks whether L is p-maximal integral. If not, a minimal integral over-lattice at p is returned}
  return IsMaximalIntegral(L, ideal<Integers() | p>);
end intrinsic;

// This function will be used in the next two intrinsics
function is_maximal_integral(L,p)
  a := Involution(HermitianSpace(L));
  // In this case it is not integral
  if IsIdentity(a) then
      if Type(p) eq RngInt then
         norm := ideal< Integers() | Norm(Norm(L))>;
      else
         norm := ideal<Order(p)| Norm(L) >;
      end if;
      if Valuation(norm, p) lt 0 then return false, _; end if;
      if GuessMaxDet(L, p) eq Valuation(Discriminant(L), p)
	  then return true, _;
      end if;
  end if;
 
  k, h:= ResidueClassField(p);
  BM:= Matrix(LocalBasis(L, p: ModuleType:= "Submodule"));
  
  G := GramMatrix(L, Rows(BM) : Half := IsQuadratic(L));

  if IsIdentity(a) then
      basis := [BaseRing(L)!1];
  else
      basis := Basis(BaseRing(L));
  end if;
  // we want Trace(<v.w>) = 0 and Trace(<alpha*v,w>) = 0
  // for all w, giving the following equations:
  // actually a basis over F should suffice.
  // How do we pull that off?
  Gs := [alpha*G + a(alpha*G) : alpha in basis];
  row_seqs := [[h(basis[i]*x) : x in Eltseq(Gs[i])] : i in [1..#basis]];
  mat := Matrix(#basis * Nrows(BM), &cat row_seqs);
  V:= KernelMatrix(mat);
  if Nrows(V) eq 0 then return true, _; end if;
  
  FF:= BaseRing(BM);
  val2:= Valuation(BaseRing(L)!2, p);
  PP:= ProjectiveLineProcess(k, Nrows(V));
  x:= Next(PP);
  while not IsZero(x) do
    e:= Eltseq(x * V) @@ h;
    v:= Vector(FF, e);
    valv:= Valuation( ((v*G) * a(Matrix(FF,1,e)))[1], p );
    // assert valv ge 1;
    assert valv ge 0;
    // TODO: Better code depending on whether -1 is a square or not and then take (1,p) or (p,p)
    // if valv ge val2+2 then
    if valv ge 2 then
        if Type(p) eq RngInt then
	  pMod := LatticeWithBasis(Matrix([WeakApproximation([p], [-1]) *v*BM ] ));
          // we go through all this trouble because L1 + L2 for integral lattice
          // encapsulates LLL, which might not keep the sign
          K := FieldOfFractions(Integers(QNF()));
          mat := ChangeRing(Matrix(Basis(L)
				   cat Basis(pMod)), K);
          h := HermiteForm(PseudoMatrix(mat));
          idls := CoefficientIdeals(h);
          sum := Matrix([Norm(idls[i]) * (Matrix(h)[i]) : i in [1..#idls]]);
          sum := ChangeRing(sum, Rationals());
          lat := LatticeWithBasis(HermitianSpace(L), sum);
        else
	  pMod := Module( [WeakApproximation([p], [-1]) *v*BM ] );
          lat := Lattice(HermitianSpace(L), L + pMod);        
        end if;
	assert IsIntegral(lat);
	return false, lat; 
    end if;
    x:= Next(PP);
  end while;
  // This should work but apparently does not work in the even case
  if IsIdentity(a) and IsOdd(Rank(L)) then
      assert GuessMaxDet(L, p) eq Valuation(Discriminant(L), p);
  end if;
  return true, _;
end function;

intrinsic IsMaximalIntegral(L::AlgQuatOrdLat, p::RngInt) -> BoolElt, AlgQuatOrdLat
{Checks whether L is p-maximal integral. If not, a minimal integral over-lattice at p is returned}
  require Order(p) cmpeq BaseRing(L) and IsPrime(p): 
    "The second argument must be a prime ideal of the base ring of the lattice";
  require not IsZero(L): "The lattice must be non-zero";
  return is_maximal_integral(L,p);
end intrinsic;

intrinsic IsMaximalIntegral(L::AlgQuatOrdLat, p::RngOrdIdl) -> BoolElt, AlgQuatOrdLat
{Checks whether L is p-maximal integral. If not, a minimal integral over-lattice at p is returned}
  require Order(p) cmpeq BaseRing(L) and IsPrime(p): 
    "The second argument must be a prime ideal of the base ring of the lattice";
  require not IsZero(L): "The lattice must be non-zero";
  return is_maximal_integral(L,p);
end intrinsic;

intrinsic BadPrimes(L::AlgQuatOrdLat) -> []
// {The list of prime ideals at which L is not unimodular or which are even}
{The list of prime ideals at which L is not unimodular}
  disc := Discriminant(ZLattice(L : Standard));
  scale := Scale(L);
  ret := { f[1] : f in Factorization(scale) } join { f[1] : f in Factorization(disc) };
  return ret;
end intrinsic;  

intrinsic NumberFieldLattice(L::AlgQuatOrdLat) -> LatNF
{Convert to the (now existing) magma built in type for number field lattices.}
  // We might need a GramFactor here in general, check it out.
  gram := 1/2*InnerForm(HermitianSpace(L));
  pb := PseudoBasis(L);
  ideals := [x[1] : x in pb];
  F := BaseRing(gram);
  if Type(F) eq FldRat then
      // currently this functionality only exists over a number field
      F := QNF();
      ideals := [ideal<Integers(F) | Norm(I)> : I in ideals];
  end if;
  basis := [Vector(NumberField(Integers(F)), x[2]) : x in pb];
  nfl := NumberFieldLattice(basis : Gram := gram, Ideals := ideals);
  return nfl;
end intrinsic;

// The standard GramFactor here is set to 1 beacuse this is the
// default in the magma built in package.
intrinsic LatticeFromLatNF(L::LatNF : GramFactor := 1) -> AlgQuatOrdLat
{Convert from the (now existing) magma built in type for number field lattices.}
  // The inner form.
  innerForm := (2/GramFactor) * PseudoGramMatrix(L);

  // The ambient reflexive space.
  Q := AmbientHermitianSpace(innerForm);

  // The basis for the lattice.
  basis := ChangeRing(Matrix(PseudoBasis(L)), BaseRing(Q));
  ideals := CoefficientIdeals(L);

  // Build the lattice and return it.
  return LatticeWithBasis(Q, basis, ideals);
end intrinsic;

// This is buggy!! Especially over 2
// We replace it by the stable version from the NumberFieldLattice package, at least for quadratic lattices
// (Eventually, all this file should be replaced by it)
intrinsic IsMaximalIntegral(L::AlgQuatOrdLat) -> BoolElt, AlgQuatOrdLat
{Checks whether L is maximal integral. If not, a minimal integral over-lattice is returned}

  if IsQuadratic(L) then
    // converting to number field lattice
    nfl := NumberFieldLattice(L);

    ok, LL := IsMaximalIntegral(nfl);
  
    if not ok then return false, LatticeFromLatNF(LL); end if;

    return true, _;
  end if;

  R := BaseRing(L);
  above_2 := {p[1] : p in Factorization(ideal<R|2>)};
  bad_primes := BadPrimes(L) join above_2;
  // for p in BadPrimes(L) do
  for p in bad_primes do
    ok, LL:= IsMaximalIntegral(L, p);
    if not ok then return false, LL; end if;
  end for;
  return true, _;

end intrinsic;

intrinsic MaximalIntegralLattice(L::AlgQuatOrdLat, p::RngOrdIdl) -> AlgQuatOrdLat
{A p-maximal integral lattice over L}
  require Order(p) eq BaseRing(L) and IsPrime(p): "The second argument must be a prime ideal of the base ring of L";
  norm := ideal<Order(p)| Norm(L) >;						
  require not IsZero(L) and Valuation(norm, p) ge 0 : "The norm of the lattice must be locally integral";

  ok, LL:= IsMaximalIntegral(L, p);
  while not ok do 
    L:= LL;    
    ok, LL:= IsMaximalIntegral(L, p);
  end while;
  return L;
end intrinsic;

intrinsic MaximalIntegralLattice(L::AlgQuatOrdLat) -> AlgQuatOrdLat
{A maximal integral lattice containing L}
  require not IsZero(L) and IsIntegral(Norm(L)) :
    "The lattice must be integral and non-zero";

  R := BaseRing(L);
  above_2 := {p[1] : p in Factorization(ideal<R|2>)};
  bad_primes := BadPrimes(L) join above_2;
  // for p in BadPrimes(L) do
  for p in bad_primes do
    ok, LL:= IsMaximalIntegral(L, p);
    while not ok do 
      L:= LL;    
      ok, LL:= IsMaximalIntegral(L, p);
    end while;
  end for;
  return L;
end intrinsic;

intrinsic MaximalIntegralLattice(V::RfxSpace) -> AlgQuatOrdLat
{A lattice which is maximal integral in the hermitian space V}

  R:= BaseRing(V); T:= Type(R); Q := InnerForm(V); a:= Involution(V);

  F := FixedField(a);
  R := Integers(F);
  n:= Nrows(Q);
  require Rank(Q) eq n : "The form must be non-degenerate";

  // We start with some integral lattice.
  L:= StandardLattice(V);
  N:= Norm(L);
/*
  if Type(N) eq FldRatElt then
    N := Integers()!N;
  end if;
*/
//  if (Type(N) eq RngIntElt and N ne 1) or (Type(N) ne RngIntElt and N ne 1*R) then
  if N ne 1*R then
    FN:= Factorization(N);
    if Type(R) eq RngInt then
      d:= &*[ FractionalIdeal(f[1])^(f[2] div 2) : f in FN ];
    end if;
    d:= &*[ f[1]^(f[2] div 2) : f in FN ];
    // For ideals in the ring of integers, inverse is not defined
    if Type(d) eq RngInt then d := Norm(d); end if;
    L:= d^-1*L;
    N:= Norm(L);
    assert IsIntegral(N);
  end if;

  return MaximalIntegralLattice(L);
end intrinsic;

intrinsic QuadraticFormInvariants(M::AlgMatElt[Fld]: Minimize:= true) -> FldAlgElt, SetEnum[RngOrdIdl], SeqEnum[RngIntElt]
{The invariants describing the quadratic form M}
  require IsSymmetric(M) and Rank(M) eq Ncols(M): "The form must be symmetric and regular";
  D:= Diagonal(OrthogonalizeGram(M));
  K:= BaseRing(M);
  R:= Integers(K);
  P:= { d[1] : d in Decomposition(R, 2) };
  U:= Universe(P);
  for d in D do
    P join:= { f[1] : f in Factorization(d*R) | IsOdd(f[2]) };
  end for;
  F:= Minimize select {U | p : p in P | Hasse(D, p) eq -1 } else { <p, Hasse(D, p) > : p in P };
  I:= [ #[ d: d in D | Evaluate(d, f) le 0 ] : f in RealPlaces(K) ];
  return &* D, F, I;
end intrinsic;

intrinsic JordanDecomposition(L::AlgQuadOrdLat, p::RngInt) -> []
{A Jordan decomposition of the completion of L at p}
  require BaseRing(L) cmpeq Order(p): "The arguments are incompatible";
  require IsPrime(p) : "The second argument must be prime";

  even:= Minimum(p) eq 2;
  if even then pi:= PrimitiveElement(p); end if;
//  B:= LocalBasis(M, p: Type:= "Submodule");
  F:= InnerProductMatrix(L);
  B:= LocalBasis(L, p);
  n:= #B;
  k:= 1;

  oldval:= Infinity();
  Blocks:= []; Exponents:= [];

  S:= Matrix(B);
  while k le n do
    G:= S*F*Transpose(S);

    // find an element <i, j> with minimal p-valuation.
    // Take it from the diagonal, if possible, and from the lowest-possible row number.
    X:= [ Valuation(G[i,i], p): i in [k..n] ];
    m, ii:= Minimum( X ); ii +:= k-1;
    pair:= <ii, ii>;

    for i in [k..n], j in [i+1..n] do
      tmp:= Valuation(G[i,j], p);
      if tmp lt m then m:= tmp; pair:= <i,j>; end if;
    end for;
    if m ne oldval then Append(~Blocks, k); oldval:= m; Append(~Exponents, m); end if;

    if even and pair[1] ne pair[2] then
//      printf "2 has no inverse, <%o,%o>\n", pair[1], pair[2];
//      printf "S=%o\n", print_matrix(ChangeRing(S, Integers()));

      SwapRows(~S, pair[1],   k); // swap f_1 and e_i
      SwapRows(~S, pair[2], k+1); // swap f_2 and e_j
      T12:= (S[k] * F * Matrix(1, Eltseq(S[k+1])))[1];
      S[k] *:= pi^Valuation(T12, p)/T12;
      T := func<i,j|(S[i] * F * Matrix(1, Eltseq(S[j])))[1]>;
      T11 := T(k,k); T22 := T(k+1, k+1); T12:= T(k, k+1);

//      printf "d=%o*%o - %o\n", T(1,1),T(2,2), T(1,2)^2;
      d := T11*T22 - T12^2;
      for l in [k+2..n] do
        tl := T12*T(k+1,l)-T22*T(k  ,l); // t_k from step 4
        ul := T12*T(k  ,l)-T11*T(k+1,l); // u_k from step 4
        S[l] +:= (tl/d)*S[k] + (ul/d)*S[k+1];
      end for;
      k +:= 2;
    else
//      printf "pair is %o\n", pair;
      if pair[1] eq pair[2] then
//        printf "swapping %o and %o\n", pair[1], k;
        SwapRows(~S, pair[1], k);
      else
//        printf "adding %o to $o\n", pair[2], pair[1];
        S[pair[1]] +:= S[pair[2]];
        SwapRows(~S, pair[1], k);
      end if;
      nrm:= (S[k] * F * Matrix(1, Eltseq(S[k])))[1];
//      printf "nrm = %o\n", nrm;
      X:= S[k] * F * Transpose(S); // T(e_k, f_i), 1<=i<=n
//      printf "renorming %o..%o\n", k+1, n;
      for l in [k+1..n] do S[l] -:= X[l]/nrm * S[k]; end for;
      k+:= 1;
    end if;
  end while;

  Append(~Blocks, n+1);
  Matrices:= [* RowSubmatrix(S, Blocks[i], Blocks[i+1] - Blocks[i]) : i in [1..#Blocks-1] *];

  return Matrices, [* m*F*Transpose(m): m in Matrices *], Exponents;
end intrinsic;

intrinsic JordanDecomposition(L::AlgQuadOrdLat, p::RngOrdIdl) -> []
{A Jordan decomposition of the completion of L at p}
  require BaseRing(L) cmpeq Order(p): "The arguments are incompatible";
  require IsPrime(p) : "The second argument must be prime";

  even:= Minimum(p) eq 2;
  if even then pi:= PrimitiveElement(p); end if;
//  B:= LocalBasis(M, p: Type:= "Submodule");
  F:= InnerProductMatrix(L);
  B:= LocalBasis(L, p);
  n:= #B;
  k:= 1;

  oldval:= Infinity();
  Blocks:= []; Exponents:= [];

  S:= Matrix(B);
  while k le n do
    G:= S*F*Transpose(S);

    // find an element <i, j> with minimal p-valuation.
    // Take it from the diagonal, if possible, and from the lowest-possible row number.
    X:= [ Valuation(G[i,i], p): i in [k..n] ];
    m, ii:= Minimum( X ); ii +:= k-1;
    pair:= <ii, ii>;

    for i in [k..n], j in [i+1..n] do
      tmp:= Valuation(G[i,j], p);
      if tmp lt m then m:= tmp; pair:= <i,j>; end if;
    end for;
    if m ne oldval then Append(~Blocks, k); oldval:= m; Append(~Exponents, m); end if;

    if even and pair[1] ne pair[2] then
//      printf "2 has no inverse, <%o,%o>\n", pair[1], pair[2];
//      printf "S=%o\n", print_matrix(ChangeRing(S, Integers()));

      SwapRows(~S, pair[1],   k); // swap f_1 and e_i
      SwapRows(~S, pair[2], k+1); // swap f_2 and e_j
      T12:= (S[k] * F * Matrix(1, Eltseq(S[k+1])))[1];
      S[k] *:= pi^Valuation(T12, p)/T12;
      T := func<i,j|(S[i] * F * Matrix(1, Eltseq(S[j])))[1]>;
      T11 := T(k,k); T22 := T(k+1, k+1); T12:= T(k, k+1);

//      printf "d=%o*%o - %o\n", T(1,1),T(2,2), T(1,2)^2;
      d := T11*T22 - T12^2;
      for l in [k+2..n] do
        tl := T12*T(k+1,l)-T22*T(k  ,l); // t_k from step 4
        ul := T12*T(k  ,l)-T11*T(k+1,l); // u_k from step 4
        S[l] +:= (tl/d)*S[k] + (ul/d)*S[k+1];
      end for;
      k +:= 2;
    else
//      printf "pair is %o\n", pair;
      if pair[1] eq pair[2] then
//        printf "swapping %o and %o\n", pair[1], k;
        SwapRows(~S, pair[1], k);
      else
//        printf "adding %o to $o\n", pair[2], pair[1];
        S[pair[1]] +:= S[pair[2]];
        SwapRows(~S, pair[1], k);
      end if;
      nrm:= (S[k] * F * Matrix(1, Eltseq(S[k])))[1];
//      printf "nrm = %o\n", nrm;
      X:= S[k] * F * Transpose(S); // T(e_k, f_i), 1<=i<=n
//      printf "renorming %o..%o\n", k+1, n;
      for l in [k+1..n] do S[l] -:= X[l]/nrm * S[k]; end for;
      k+:= 1;
    end if;
  end while;

  Append(~Blocks, n+1);
  Matrices:= [* RowSubmatrix(S, Blocks[i], Blocks[i+1] - Blocks[i]) : i in [1..#Blocks-1] *];

  return Matrices, [* m*F*Transpose(m): m in Matrices *], Exponents;
end intrinsic; 

// functions for p-adic completion and p-adic lattices

declare type RngPadIdl;
declare attributes RngPadIdl :
		   // the ring
		   R,
		   generator;

intrinsic Ideal(R::RngPad, t::.) -> RngPadIdl
{.}
  if Type(t) ne SeqEnum then t := [t]; end if;
  pi := UniformizingElement(R);
  val := Minimum([Valuation(R!x) : x in t]);
  I := New(RngPadIdl);
  I`R := R;
  I`generator := pi^val;
  return I;
end intrinsic;

intrinsic Generators(I::RngPadIdl) -> SeqEnum[RngPadElt]
{.}
  return [I`generator];
end intrinsic;

intrinsic Print(I::RngPadIdl)
{.}
  printf "Ideal of %o generated by %o", I`R, I`generator;
end intrinsic;

intrinsic '#'(I::RngPadIdl) -> RngIntElt
{.}
  k := ResidueClassField(I`R);
  v := Valuation(I`generator);
  return (#(I`R) / (#k)^v);
end intrinsic;  

declare type ModPad[ModTupFldElt];
declare attributes ModPad :
		   // the base ring
		   R,
	// the field of fractions
	F,
	// basis
	basis;

intrinsic Module(R::RngPad, n::RngIntElt) -> ModPad
{Create the free module R^n where R is a p-adic ring.}
  M := New(ModPad);
  M`R := R;
  M`F := FieldOfFractions(R);
  M`basis := Rows(IdentityMatrix(M`F, n));
  
  return M;
end intrinsic;

intrinsic pAdicModule(S::SeqEnum[ModTupFldElt]) -> ModPad
{Create a module from the sequence of ModElts with entries in the p-adic ring or its field of fractions. The elements of the resulting module will be the linear combinations of the ModElts.}
  M := New(ModPad);
  M`F := FieldOfFractions(BaseRing(Universe(S)));
  M`R := Integers(M`F);
  M`basis := S;

  return M;
end intrinsic;

intrinsic Print(L::ModPad)
{.}
  printf "Module over %o generated by: ", L`R;
  for b in L`basis do
    printf "\n%o", b;
  end for;
end intrinsic;

intrinsic '.'(L::ModPad, n::RngIntElt) -> ModTupFldElt
{.}	     
  return L`basis[n];
end intrinsic;

intrinsic 'in'(v::ModTupFldElt, L::ModPad) -> BoolElt
{.}
  B := Matrix(L`basis);
  coeffs := v * B^(-1);
  return &and [c in L`R : c in Eltseq(coeffs)];
end intrinsic;

intrinsic ChangeRing(L::ModPad, R::RngPad) -> ModPad
{.}
  F := FieldOfFractions(R);
  return pAdicModule([ChangeRing(b, F) : b in L`basis]);
end intrinsic;

intrinsic DirectSum(Ls::SeqEnum[ModPad]) -> ModPad
{.}
  return pAdicModule(Rows(DirectSum([Matrix(L`basis) : L in Ls])));
end intrinsic;

intrinsic 'subset'(L1::ModPad, L2::ModPad) -> BoolElt
{.}
  return &and [b in L2 : b in L1`basis];
end intrinsic;

intrinsic 'eq'(L1::ModPad, L2::ModPad) -> BoolElt
{.}
  return (L1 subset L2) and (L2 subset L1);
end intrinsic;

intrinsic Complete(L::ModDed, p::RngOrdIdl) -> ModPad
{Compute the completion of the lattice L at the prime p}
//    if Type(L) eq ModDedLat then L := Module(L); end if;
    psb := PseudoBasis(L);
    idls := [x[1] : x in psb];
    basis := [x[2] : x in psb];
    R := FieldOfFractions(BaseRing(L));
    R_p, comp_p := Completion(R,p);
    pi := UniformizingElement(R_p);
    val_idls_p := [ Minimum([Valuation(comp_p(g)) :
			     g in Generators(I)]) : I in idls];
    basis_p := [Vector([comp_p(x) : x in Eltseq(vec)]) :
		vec in basis];
    basis_p := [pi^(val_idls_p[i]) * basis_p[i] :
		i in [1..#basis_p]];
    return pAdicModule(basis_p);
end intrinsic;

intrinsic Complete(L::AlgQuadOrdLat, p::RngOrdIdl) -> ModPad
{.}
  return Complete(Module(L),p);	  
end intrinsic;

function pAdicLatticeAtSplitPrime(L,p)
    R := Integers(BaseRing(L));
    Ps := [fac[1] : fac in Factorization(ideal<R|p>)];
    L_p := [Complete(L, P) : P in Ps];
    ZZ_p := pAdicRing(p);
    L_p_pAdic := [ChangeRing(Lambda, ZZ_p) : Lambda in L_p];
    return DirectSum(L_p_pAdic);
end function;

function get_hecke_representatives(p)
    reps := [ DiagonalMatrix([p,1,1]) ];
    reps cat:= [ Matrix([[1,r,0],[0,p,0],[0,0,1]]) : r in [0..p-1]];
    reps cat:= [ Matrix([[1,0,r],[0,1,s],[0,0,p]]) : r,s in [0..p-1]];
    // The transposition is to get left cosets: KpK = U p_j K
    ret := [Transpose(r) : r in reps];
    // Checking they are indeed distinct representatives
    QQ := Rationals();
    ZZ := Integers();
    reps := [MatrixAlgebra(QQ,3)!x : x in ret];
    num := &+[r^(-1)*s in MatrixAlgebra(ZZ,3) select 1 else 0 :
	      r,s in reps];
    assert num eq #reps;
    return ret;
end function;

intrinsic PseudoBasis(L::Lat) -> SeqEnum
{A sequence of tuples containing ideals and vectors which generate
 the lattice L, for compatiblity with AlgQuadOrdLat. The ideals are trivial.}
  ret := [];
  one := FractionalIdeal(1);
  for b in Basis(L) do
    Append(~ret, < one, b >);
  end for;	
  return ret;
end intrinsic;

intrinsic WeakApproximation(I::SeqEnum[RngInt],
			    V::SeqEnum[RngIntElt]) -> FldRatElt
{Computes an element of valuation V[i] at the prime I[i].}
  // Here we use the fact that the integers is a PID
  // so all ideals have a single generator
  gens := [Norm(II) : II in I];
  return &*([1] cat [gens[i]^V[i] : i in [1..#V]]);
end intrinsic;

function MySquarefree(d)
  T:= Type(d);
  assert T notin {RngIntElt, FldRatElt};

  return d; // FIXME

  if ISA(T, FldElt) then
    _, x:= IsIntegral(d);
    d:= Integers(Parent(d)) ! (d*x^2);
  end if;
  R:= Parent(d); r:= R ! 1;
  if IsSquare(d) then return r; end if;
  F:= Reverse([ < f[1], f[2] div 2 >: f in Factorization(R*d) | f[2] ge 2 ]);
  for i in [1..#F] do
    for j in [1..F[i,2]] do
      ok, x:= IsPrincipal(F[i,1]);
      if ok then
	r *:= x^(F[i,2] div j);
        F[i,2] mod:= j;
	break;
      end if;
    end for;
  end for;

  F:= [f : f in F | f[2] ne 0 ];
  found := true;
  while #F ge 2 and found do
    found:= false;
    Prods:= [ 1*R ]; Vecs:= [ RSpace(Integers(), #F) ! 0 ];
    for i in [1..#F] do
      v:= Universe(Vecs).i;
      for j in [1..F[i,2]] do
	for k in [1..#Prods] do 
	  I:= Prods[k] * F[i,1];
          w:= Vecs[k] + v;
          ok, x:= IsPrincipal(I);
	  if ok then
	    found:= true;
	    for i in [1..#F] do F[i,2] -:= w[i]; end for;
	    r *:= x;
	    break i;
	  else
	    Append(~Prods, I);
	    Append(~Vecs, w);
	  end if;
	end for;
      end for;
    end for;
    F:= [f : f in F | f[2] ne 0 ];
  end while;
  return R ! (d / r^2);
end function;

// Returns all elements in R supported at the prime ideals in PP (up to squares).
function ElementsWithSupport(R, PP)
//  if ISA(Type(PP), SetEnum) then PP:= Setseq(PP); end if;
  if Type(R) eq RngInt then return [-1] cat PP, func<x|x>; end if;
  U, h:= UnitGroup(R);
  Result:= [ h(U.i): i in [1..Ngens(U)] ];
  Cl, h:= ClassGroup(R);
  if #Cl ne 1 then
    F:= FreeAbelianGroup(#PP);
    m:= hom< F -> Cl | [ p @@ h: p in PP ] >;
    K:= Kernel(m);
    for i in [1..Ngens(K)] do
      ok, x:= IsPrincipal(PowerProduct(PP, Eltseq(F ! K.i))); assert ok;
      Append(~Result, x);
    end for;
    _, hh:= quo< Cl | Image(m) >;
    f:= function(I)
      c:= (I @@ h);
      o:= Order(c @ hh);
      J:= PowerProduct(PP, Eltseq((-o * c) @@ m));
      ok, x:= IsPrincipal(I^o*J); assert ok;
      return x;
    end function;
  else
    for p in PP do
      ok, x := IsPrincipal(p); assert ok;
      Append(~Result, x);
    end for;
    f:= func< I | x where _, x:= IsPrincipal(I) >;
  end if;
  return Result, f;
end function;

intrinsic QuadraticFormWithInvariants(Dim::RngIntElt, Det::FldAlgElt, Finite::Setq[RngOrdIdl], Negative::[RngIntElt]) -> AlgMatElt
{Computes a quadratic form with of dimension Dim and determinant Det that has Hasse invariants -1 at the primes in Finite.
 The number of negative entries of the i-th real signature is given in Negative[i]}

  requirege Dim, 1;
  require Det ne 0: "The determinant must be nonzero";
  K:= Parent(Det);

  // Infinite places checking
  Inf:= RealPlaces(K);
  require #Negative eq #Inf: "The number of negative entries must be the number of real places";
  require forall(i){i : i in [1..#Inf] | Negative[i] in [0..Dim]}:
    Sprintf("Impossible negative entry at position %o", i);
  require forall(i){i : i in [1..#Inf] | Sign(Evaluate(Det, Inf[i])) eq (-1)^(Negative[i] mod 2)}:
    Sprintf("Information at the real place number %o does not match the sign of the determinant", i);

  // Dimension 1
  if Dim eq 1 then
    require IsEmpty(Finite): "Impossible Hasse invariants";
    return Matrix(1, [ Det ]);
  end if;

  // Finite places checking
  R:= Integers(K);
  PI:= PowerIdeal(R);
  require IsEmpty(Finite) or (Universe(Finite) cmpeq PI and forall{p : p in Finite | IsPrime(p)}):
    "The Invariants must be a set of prime ideals of the base field";
  Finite:= Set(Finite);

  // Dimension 2 needs some more love
  if Dim eq 2 then
    ok:= forall(p){p: p in Finite | IsLocalSquare(-Det, p)};
    require ok: Sprintf("A binary form with determinant %o must have Hasse invariant +1 at the prime ideal:\n%o", Det, p);
  end if;

  // Product formula checking
  require IsEven(#[ n: n in Negative | n mod 4 ge 2 ] + #Finite):
    "The number of places (finite or infinite) with Hasse invariant -1 must be even";

  // OK, a space with these invariants must exist.
  // For final testing, we store the invariants.
  Dim0:= Dim; Det0:= Det; Finite0:= Finite; Negative0:= Negative;

  // Reduce Det
  Det:= K ! MySquarefree(Det);

  // Pad with ones
  k:= Max(0, Dim - Max(3, Max(Negative)));
  D:= [ (K ! 1)^^k ];
  Dim -:= k;

  if Dim ge 4 then
    // Pad with minus ones
    k:= Min(Dim-3, Min(Negative));
    D2 := [ (K ! -1)^^k ];
    Dim -:= k;
    Negative:= [ n-k: n in Negative ];

    // Pad with other entries
    while Dim ge 4 do
      V:= []; Signs:= [];
      for i in [1..#Negative] do
        if Negative[i] eq 0 then 
	  Append(~V, Inf[i]); Append(~Signs, +1);
	elif Negative[i] eq Dim then
	  Append(~V, Inf[i]); Append(~Signs, -1);
	end if;
      end for;
      x:= RealWeakApproximation(V, Signs : Al:= "Small");
      s:= RealSigns(x);
      k:= Min([Dim-3] cat [ s[i] eq 1 select (Dim - Negative[i]) else (Negative[i]) : i in [1..#Negative] ]);
      D2 cat:= [ (K ! x)^^k ];
      Dim -:= k;
      for i in [1..#Negative] do
        if s[i] eq -1 then Negative[i] -:= k; end if;
      end for;
    end while;

    // Adjust invariants: Dim and Negative are already ok.
    d, f:= QuadraticFormInvariants(DiagonalMatrix(D2));
    PP:= &join [ Support(R*x) : x in D2 cat [2, Det] ];
    Finite:= { p: p in PP | HS(d, -Det, p) * (p in f select -1 else 1) * (p in Finite select -1 else 1) eq -1 };
    D cat:= D2;
    Det:= K ! MySquarefree(Det * d);
    delete d, f;
  end if;

  // The ternary case
  if Dim eq 3 then
//  "Dim 3", Det;
    // The primes at which the form is anisotropic
    PP:= Finite join Support(2*R) join Support(Det*R);
    PP:= [ PI | p : p in PP | HS(K ! -1, -Det, p) ne (p in Finite select -1 else 1) ];

    // Find some a such that for all p in PP: -a*Det is not a local square
    // TODO: Find some smaller a?! The approach below is very lame.
    // We simply make sure that a*Det has valuation 1 at each prime in PP....
    a:= K ! (#PP eq 0 select 1 else WeakApproximation(PP, [ (1+Valuation(Det, p)) mod 2 : p in PP ]));
    // Fix the signs of a if necessary.
    Idx:= [ i : i in [1..#Negative] | Negative[i] in {0,3} ];
    S:= [ Negative[i] eq 0 select s[i] else -s[i] : i in Idx ] where s:= RealSigns(a);
    a*:= K ! RealWeakApproximation(Inf[Idx], S: Al:= "Small", CoprimeTo:= &*PP);

    // Adjust invariants for the last time:
    s:= RealSigns(a);
    for i in [ i: i in [1..#Negative] | s[i] lt 0 ] do 
      Negative[i] -:= 1;
    end for;
    PP:= &join [ Support( R*x) : x in [K ! 2, Det, a] ];
    Finite:= { p: p in PP | HS(a, -Det, p) * (p in Finite select -1 else 1) eq -1 };
    Det:= K ! MySquarefree(Det * a);
    Append(~D, a);
  end if;

  // The binary case
  PP:= Setseq((Support(R*2) join Support(R*Det)) diff Finite); // the places at which we need +1
//  PP:= [ p[1]: p in Factorization((2*Det)*R) | p[1] notin Finite ];	
  I2:= [ i: i in [1..#Inf] | Negative[i] ne 1 ];

  target:= Vector(GF(2), [ Negative[i] div 2 : i in I2 ] cat [ 1^^#Finite ] cat [ 0^^#PP ] );	// the sign vector we are searching for
  if IsZero(target) then
    a:= K ! 1;
  else
    found:= false;
    //[ Norm(p): p in PP ], [ Norm(p): p in Finite ];
    PP:= Setseq(Finite) cat PP;

    U, h:= UnitGroup(R);
    V:= VectorSpace(GF(2), #I2 + #PP); S:= sub< V | >; Base:= [ K | ]; M:= [];
    SignVector:= func< g | Vector(GF(2), [ (1-Sign(Evaluate(g, Inf[i]))) div 2 : i in I2 ] cat [ (1-HS(g, -Det, p)) div 2 : p in PP ]) >;

    // Get initial factor base
    L, f:= ElementsWithSupport(R, PP);
    for l in L do
      x:= K ! l;
      v:= SignVector(x);
      if v in S then continue; end if;
      Append(~Base, x); Append(~M, v); S:= sub< V | S, v >;
      if target in S then
        found:= true; break;
      end if;
    end for;

    // Extend the factor base by one more prime ideal
    p:= 2;
    while not found do
      p:= NextPrime(p);
      for d in Decomposition(R, p) do
        if d[1] in PP then continue; end if;	// already there
        x:= K ! f(d[1]);
        v:= SignVector(x);
        // target notin S thus we can only hope for target+v in S
        if (target+v) in S then
          Append(~M, v); Append(~Base, x);
          found:= true; break;
        end if;
      end for;
    end while;

    // solve for the exponents and assemble the solution.
    exp:= Solution(Matrix(M), target);
    a:= PowerProduct(Base, ChangeUniverse(Eltseq(exp), Integers()));
  end if;
  D cat:= [a, Det*a];
  M:= DiagonalMatrix(D);

  // The final test...
  d, f, n:= QuadraticFormInvariants(M);
  assert Dim0 eq #D and IsSquare(d*Det0) and f eq Finite0 and n eq Negative0;

  return M;
end intrinsic;

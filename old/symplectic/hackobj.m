//====================
//
// ALGEBRAIC MODULAR FORMS


//
// This file contains the basic structures and hackobj nonsense for the ModFrmAlg package.
//
// Matthew Greenberg and John Voight, 2012
//
//====================


declare attributes Lat:   
  AmbientHermSpace,  // Ambient Hermitian space
  ZBasisQuatLat,     // Z-Basis of the associated quaternionic lattice
  Discriminant,       // Discriminant
  AuxForms,           // Auxiliary forms which defining Lambda as a module over Z_F.
  LatticeAutomorphismGroup;
                      // = LatticeAutomorphismGroup(Lambda), the automorphism group of LambdaZZ.



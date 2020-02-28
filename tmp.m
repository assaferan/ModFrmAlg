SetDebugOnError(true);
SetHelpUseExternalBrowser(false);
AttachSpec("spec");
ZZ := Integers();
QQ := Rationals();
ZZ_X<x> := PolynomialRing(ZZ);
E := NumberField(x^2 + 11);
M := AlgebraicModularForms(QQ, E, "A1");

 // for now assume E/Q quadratic, change later

function evaluate(a, v)
     V := Parent(v);
     return V![a(v[i]) : i in [1..Dimension(V)]]; 
end function;

function conv_rat_to_L(v, L)
  O_E := BaseRing(L);
  B_E := Basis(O_E);
  dim := #Basis(L);
  deg := #B_E;
  V := Universe(Basis(L));
  return V![&+[B_E[j] * v[(i-1)*deg + j] : j in [1..deg]] : i in [1..dim]];
end function;
     
function get_rational_lattice(L : H := 1)
  O_E := BaseRing(L);
  E := FieldOfFractions(O_E);
  aut := Automorphisms(E);
  B_L := Basis(L);
  B_E := Basis(O_E);
  dim := #B_L;
  if (H eq 1) then H := IdentityMatrix(E, dim); end if;
  deg := #B_E;
  nvars := dim*deg;
  E_X := PolynomialRing(E, nvars);
  BLX := [ChangeRing(v, E_X) : v in B_L];
  vecs := [ &+ [(&+[ a(B_E[j]) * E_X.((i-1)*deg + j) :
	    j in [1..deg] ])*BLX[i]  : i in [1..dim]] : a in aut];
  norm_form := InnerProduct(vecs[1]*ChangeRing(H, E_X), vecs[2]);
  coefs := &cat [[MonomialCoefficient(norm_form, E_X.i * E_X.j) :
			       j in [i..nvars]] : i in [1..nvars]];
  A := UpperTriangularMatrix(coefs);
  Q := ChangeRing((A + Transpose(A))/2, Rationals());
  Q_lat := LatticeWithGram(Q);
  return Q_lat;
end function;

function get_vectors_of_norm_up_to(Q_lat, B)
  shortvecs := ShortVectors(Q_lat, B);
  idxs := {v[2] : v in shortvecs};
  ret := AssociativeArray(idxs);
  for k in idxs do
     tmp := [v[1] : v in shortvecs | v[2] eq k];
     ret[k] := tmp cat [-v : v in tmp];
  end for;
  return ret;
end function;

function prod(x,y, H, a)
  return InnerProduct(x*H, evaluate(a,y));
end function;

function get_gamma(L, r, H, Q_lat)
   dim := Dimension(L);
   O_E := BaseRing(L);
   E := FieldOfFractions(O_E);
   a := Automorphisms(E)[2];
   inner_prods := [[prod(x,y,H,a) : x in Basis(L)]
		  : y in Basis(L)];
   svecs := get_vectors_of_norm_up_to(Q_lat, r * Max(&cat inner_prods));
   phi_pos := [{conv_rat_to_L(v,L) : v in svecs[r * inner_prods[i][i]]} :
						     i in [1..dim]];
   all_phis := CartesianProduct(phi_pos);

   gamma := [t : t in all_phis |
	    &and [&and [prod(t[i], t[j], H, a) eq r * inner_prods[i][j]
				: i in [1..dim]] : j in [1..dim]]];

   return [Matrix([x : x in g]) : g in gamma];
end function;

//intrinsic Conjugate(B::ModMatFldElt) -> ModMatFldElt
//{}
function myConjugate(B)
  LL := NumberField(BaseRing(Parent(B)));
  BB := [[Conjugate(LL!B[i,j]) : j in [1..NumberOfColumns(B)]] :
				      i in [1..NumberOfRows(B)]];
  return Parent(B)!Matrix(BB);
end function;
//end intrinsic;
/*
L := QuadraticField(-7);
n := 3;
F := Rationals();
// Hermitian form
H := IdentityMatrix(L,n);
Z_L := RingOfIntegers(L);
// a lattice
Lamda := Module(Z_L,n);
B := MatrixAlgebra(L,n)!BasisMatrix(Lamda);
E := B_bar * H * B;
assert IsCoercible(MatrixAlgebra(L,n), E);
// Matrix Basis of the dual lattice
E_dual := myConjugate(E^(-1));
*/

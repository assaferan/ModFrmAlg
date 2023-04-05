// freeze;
/****-*-magma-******a********************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                             Eran Assaf                                 
                                                                            
   FILE: algaut.m (Implementation file for algebra autmorphisms)

   This is basically just a construct to hold both the map and the element of
   the automorphism group together.

   Maybe should also write a structure for the group itself, 
   so far it is not eneded.

   04/04/2023 : started from a copy of fieldaut.m
 
 ***************************************************************************/

///////////////////////////////////////////////////////////////////
//                                                               //
//    AlgAut: The algebra automorphism object.                     //
//                                                               //
///////////////////////////////////////////////////////////////////

declare type AlgAut;
declare attributes AlgAut :
  B,   // the algebra
  fixed, // the fixed algebra of the automorphism
  map, // the mapping
  elt, // the element in the automorphism group
  isom; // the isomorphism between the group and the set of maps

/* constructors */

function fullAutomorphismGroup(B)
   // When B is a quaternion algebra we are only interested in the identity and the swap
   // !! TODO - think of how to unify all these cases 
   if Type(B) eq AlgQuat then
       id_map := hom<B->B | [B!1, B.1, B.2, B.3]>;
       alpha := hom<B->B | [B!1, -B.1, -B.2, -B.3]>;
       aut := [id_map, alpha];
       gal := Sym(2);
       return gal, aut, map<gal -> aut | <gal!1, aut[1]>, <gal!(1,2), aut[2]> >;
   end if;
   if Type(B) eq AlgAss then
       id_map := hom<B->B|[B.1,B.2]>;
       alpha := hom<B->B|[B.2,B.1]>;
       aut := [id_map, alpha];
       gal := Sym(2);
       return gal, aut, map<gal -> aut | <gal!1, aut[1]>, <gal!(1,2), aut[2]> >;
   end if;
   char := Characteristic(B);
   if (char eq 0) then
      gal, aut, phi := AutomorphismGroup(B);
   else
      baseField := FiniteField(char);

      // This special case is needed because AutomorphismGroup(L,L)
      // fails for finite fields !!!!
      if IsFinite(B) and #B eq char then
        gal := GaloisGroup(B,B);
        aut := [ hom<B->B|> ];
        phi := map<gal->aut| <gal!1, aut[1]> >;
      else
        gal, aut, phi := AutomorphismGroup(B, baseField);
      end if;
   end if;
   return gal, aut, phi;
end function;

intrinsic AlgebraAutomorphism(B::AlgAss[Fld], g::GrpPermElt) -> AlgAut
{Return the involution swapping the indices.}
  alpha := New(AlgAut);
  alpha`B := B;
  S2 := Parent(g);
  alpha`elt := g;
  if Dimension(B) eq 2 then
      id_map := hom<B -> B | [B.1, B.2]>;
      alpha`map := hom<B -> B | [B.2, B.1]>;
  elif Type(B) eq AlgQuat then
      id_map := hom<B->B | [B!1, B.1, B.2, B.3]>;
      alpha`map := hom<B->B | [B!1, -B.1, -B.2, -B.3]>;
  else
      error "Not Implemented for this type of algebra";
  end if; 
  alpha`isom := map<S2 -> Parent(alpha`map) | [<S2!1, id_map>,
					       <g, alpha`map> ] >;
  return alpha;
end intrinsic;

intrinsic AlgebraAutomorphism(B::AlgAss[Fld]) -> AlgAut
{Return the standard involution on B.}
  return AlgebraAutomorphism(B, Sym(2)!(1,2));
end intrinsic;

intrinsic AlgebraAutomorphism(L::Fld, g::GrpPermElt) -> AlgAut
{.}
  alpha := New(AlgAut);
  alpha`B := L;
  gal, _, psi := fullAutomorphismGroup(L);
  isom, phi := IsIsomorphic(Parent(g), gal);
  require isom :
  "Group element must be in the automorphism group of the field!";
  alpha`elt := phi(g);
  alpha`map := psi(alpha`elt);
  alpha`isom := psi;

  return alpha; 
end intrinsic;

intrinsic IdentityAutomorphism(B::Alg) -> AlgAut
{.}
  gal, _, _ := fullAutomorphismGroup(B);
  return AlgebraAutomorphism(B, gal!1);
end intrinsic;

// This is needed because HasComplexConjugate can return a UserProgram
intrinsic AlgebraAutomorphism(L::Fld, f::UserProgram) -> AlgAut
{.}
   gal, _, psi := fullAutomorphismGroup(L);
   if IsFinite(L) then
     gens := [L.1];
   else
     gens := Generators(L);
   end if;
   require exists(g){g : g in gal | &and[psi(g)(x) eq f(x) : x in gens]} :
     "Map must be an automorphism of the field!";
   return AlgebraAutomorphism(L, g);
end intrinsic;

intrinsic AlgebraAutomorphism(L::Fld, f::Intrinsic) -> AlgAut
{.}
   gal, _, psi := fullAutomorphismGroup(L);
   if IsFinite(L) then
     gens := [L.1];
   else
     gens := Generators(L);
   end if;
   require exists(g){g : g in gal | &and[psi(g)(x) eq f(x) : x in gens]} :
     "Map must be an automorphism of the field!";
   return AlgebraAutomorphism(L, g);
end intrinsic;

intrinsic AlgebraAutomorphism(L::Fld, f::Map[Fld,Fld]) -> AlgAut
{.}
    if IsFinite(L) then
	require (#L eq #Domain(f)) and (#L eq #Codomain(f)) :
	     "map must be an automorphism of the field.";
    elif FldRat notin [Type(L), Type(Domain(f))] then
	is_isom_in, phi_in := IsIsomorphic(L, Domain(f));
	is_isom_out, phi_out := IsIsomorphic(Codomain(f), L);
	require is_isom_in and is_isom_out :
		"map must be an automorphism of the field.";
	f := phi_in * f * phi_out;
    end if;
   gal, _, psi := fullAutomorphismGroup(L);
   if IsFinite(L) then
     gens := [L.1];
   else
     gens := Generators(L);
   end if;
   require exists(g){g : g in gal | &and[psi(g)(x) eq f(x) : x in gens]} :
     "Map must be an automorphism of the field!";
   return AlgebraAutomorphism(L, g);
end intrinsic;

// Currently, this one is only implemented for quadratic etale algebras
intrinsic AlgebraAutomorphism(L::AlgAss[Fld],
				 f::Map[AlgAss[Fld],AlgAss[Fld]]) -> AlgAut
{.}
    if IsFinite(BaseRing(L)) then
	require (#L eq #Domain(f)) and (#L eq #Codomain(f)) :
	     "map must be an automorphism of the algebra.";
    elif FldRat notin [Type(BaseRing(L)), Type(BaseRing(Domain(f)))] then
	is_isom_in, phi_in := IsIsomorphic(BaseRing(L), BaseRing(Domain(f)));
	is_isom_out, phi_out := IsIsomorphic(BaseRing(Codomain(f)),
					     BaseRing(L));
	require is_isom_in and is_isom_out :
		"map must be an automorphism of the field.";
	// f := phi_in * f * phi_out;
    end if;
    // !! TODO : check that it works in general
    if Dimension(L) eq 2 then
	f_in := hom<L -> Domain(f) | [Domain(f).1, Domain(f).2]>;
	f_out := hom<Codomain(f) -> L | [L.1, L.2]>;
	gens := [L.1, L.2];
    else
	f_in := hom<L -> Domain(f) | [Domain(f)!1, Domain(f).1, Domain(f).2, Domain(f).3]>;
	f_out := hom<Codomain(f) -> L | [L!1, L.1, L.2, L.3]>;
	gens := [L!1, L.1, L.2, L.3];
    end if;
    f := f_in * f * f_out;
    gal, _, psi := fullAutomorphismGroup(L);
    require exists(g){g : g in gal | &and[psi(g)(x) eq f(x) : x in gens]} :
		  "Map must be an automorphism of the field!";
    return AlgebraAutomorphism(L, g);
end intrinsic;

/* Printing */
intrinsic Print(alpha::AlgAut, level::MonStgElt)
{.}
  if level eq "Magma" then
      printf "AlgebraAutomorphism(%m, %m!%m)",
	     alpha`B, Parent(alpha`elt), alpha`elt;
  else      
      printf "Algebra Automorphism of %o", alpha`B;
  end if;
end intrinsic;

/* access */

intrinsic BaseAlgebra(alpha::AlgAut) -> Alg
{.}
  return alpha`B;
end intrinsic;

intrinsic Order(alpha::AlgAut) -> RngIntElt
{.}
  return Order(alpha`elt);
end intrinsic;

intrinsic FixedField(alpha::AlgAut) -> Fld
{.}	  
  if assigned alpha`fixed then return alpha`fixed; end if;
  if ISA(Type(alpha`B), AlgQuat) then
      return BaseField(alpha`B);
  end if;
  if IsFinite(alpha`B) or
     ((not ISA(Type(alpha`B),Fld)) and IsFinite(BaseRing(alpha`B))) then
    return sub<alpha`B|[x : x in alpha`B | alpha(x) eq x]>;
  end if;
  if Type(alpha`B) ne FldRat then
    F := FixedField(alpha`B, [alpha`map]);
    if Type(F) eq FldRat and Degree(alpha`B) eq 1 then
        F := QNF();
    end if;
    assert IsSubfield(F,alpha`B);
  else
    F := alpha`B;
  end if;

  alpha`fixed := F;
  return alpha`fixed;
end intrinsic;

intrinsic Automorphism(alpha::AlgAut) -> Map[Alg, Alg]
{.}
  return alpha`map;
end intrinsic;

/* arithmetic */

intrinsic '^'(alpha::AlgAut, n::RngIntElt) -> AlgAut
{.}
  beta := New(AlgAut);
  beta`B := alpha`B;
  beta`elt := alpha`elt^n;
  beta`isom := alpha`isom;
  beta`map := beta`isom(beta`elt);

  return beta;
end intrinsic;

intrinsic Inverse(alpha::AlgAut) -> AlgAut
{.}
  return alpha^(-1);
end intrinsic;

intrinsic '*'(alpha::AlgAut, beta::AlgAut) -> AlgAut
{.}
  require BaseAlgebra(alpha) eq BaseAlgebra(beta) :
     "Automorphisms should be of the same field";
  
  gamma := New(AlgAut);
  gamma`B := alpha`B;
  gamma`elt := alpha`elt * beta`elt;
  gamma`isom := alpha`isom;
  gamma`map := beta`map * alpha`map;

  return gamma;
end intrinsic;

intrinsic 'eq'(alpha::AlgAut, beta::AlgAut) -> BoolElt
{.}
  return BaseAlgebra(alpha) eq BaseAlgebra(beta) and alpha`elt eq beta`elt;
end intrinsic;

intrinsic IsIdentity(alpha::AlgAut) -> BoolElt
{.}
   return alpha`elt eq Parent(alpha`elt)!1;
end intrinsic;

/* Evaluation */

intrinsic '@'(x::AlgElt, alpha::AlgAut) -> AlgElt
{.}
  return alpha`map(x);
end intrinsic;

/*
intrinsic '@'(x::AlgAssElt[Fld], alpha::FldAut) -> FldElt
{.}
  return alpha`map(x);
end intrinsic;
*/

intrinsic '@'(v::ModTupRngElt, alpha::AlgAut) -> ModTupRngElt
{.}
  V := Parent(v);
  require BaseAlgebra(V) eq BaseAlgebra(alpha) : "map must be defined on elements!";
  return V![alpha(v[i]) : i in [1..Dimension(V)]];
end intrinsic;

intrinsic '@'(a::AlgMatElt, alpha::AlgAut) -> AlgMatElt
{.}
  A := Parent(a);
  require BaseRing(A) eq BaseAlgebra(alpha) : "map must be defined on elements!";
  return A![[alpha(a[i,j]) : j in [1..Degree(A)]]
				  : i in [1..Degree(A)]];
end intrinsic;

/*
intrinsic '@'(a::AlgMatElt[AlgAss[Fld]], alpha::FldAut) -> AlgMatElt[Fld]
{.}
  A := Parent(a);
  require BaseRing(A) eq BaseField(alpha) : "map must be defined on elements!";
  return A![[alpha(a[i,j]) : j in [1..Degree(A)]]
				  : i in [1..Degree(A)]];
end intrinsic;
*/

/*
intrinsic '@'(a::ModMatFldElt[Alg], alpha::AlgAut) -> ModMatFldElt[Alg]
{.}
  A := Parent(a);
  require BaseRing(A) eq BaseField(alpha) : "map must be defined on elements!";
  return A![[alpha(a[i,j]) : j in [1..Ncols(a)]]
				  : i in [1..Nrows(a)]];
end intrinsic;
*/

intrinsic '@'(I::AlgAssVOrdIdl[RngOrd], alpha::AlgAut) -> AlgAssVOrdIdl[RngOrd]
{.}
  B := BaseAlgebra(alpha);
  O := MaximalOrder(B);
  require O eq Order(I) :
    "Fractional ideal must be in the maximal order of the algebra the automorphism is acting on.";
  return ideal<O | [alpha`map(g) : g in Generators(I)]>;
end intrinsic;

// We duplicate for the case of rational field
intrinsic '@'(I::RngInt, alpha::AlgAut) -> RngInt
{.}
  L := BaseAlgebra(alpha);
  Z_L := RingOfIntegers(L);
  require Z_L eq Order(I) :
    "Fractional ideal must be in the ring of integers of the field the automorphism is acting on.";
  return ideal<Z_L | [alpha`map(g) : g in Generators(I)]>;
end intrinsic;

// We duplicate for the case of rational field
/*
intrinsic '@'(I::RngIntFracIdl, alpha::AlgAut) -> RngIntFracIdl
{.}
  L := BaseAlgebra(alpha);
  Z_L := RingOfIntegers(L);
  require Z_L eq Order(I) :
    "Fractional ideal must be in the ring of integers of the field the automorphism is acting on.";
//  return ideal<Z_L | [alpha`map(g) : g in Generators(I)]>;
  return FractionalIdeal([alpha`map(g) : g in Generators(I)]);
end intrinsic;
*/

intrinsic '@'(x::RngOrdElt, alpha::AlgAut) -> RngOrdElt
{.}
  L := BaseAlgebra(alpha);
  require IsCoercible(L,x) :
    "element must be in the field the automorphism is acting on.";
  return Parent(x)!(alpha(L!x));
end intrinsic;

intrinsic '@'(x::RngIntElt, alpha::AlgAut) -> RngIntElt
{.}
  L := BaseAlgebra(alpha);
  require IsCoercible(L,x) :
    "element must be in the field the automorphism is acting on.";
  return Parent(x)!(alpha(L!x));
end intrinsic;

intrinsic ChangeRing(alpha::AlgAut, R::Rng) -> AlgAut
{.}
  return AlgebraAutomorphism(R, alpha`elt);
end intrinsic;

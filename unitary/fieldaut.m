freeze;
/****-*-magma-******a********************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                             Eran Assaf                                 
                                                                            
   FILE: fieldaut.m (Implementation file for field autmorphisms)

   This is basically just a construct to hold both the map and the element of
   the automorphism group together.

   Maybe should also write a structure for the group itself, 
   so far it is not eneded.

   05/04/2020 : Added support in 2 dimensional etale algebras

   04/27/2020 : Fixed bug in constructor to handle construction from io.

   04/24/2020 : Added construction of automorphism for a quadratic etale case.
                Modified Print to have Magma level printing.
		Changed constructor to support construction from Magma level io.

   03/05/2020 : Added basic documentation.
 
 ***************************************************************************/

///////////////////////////////////////////////////////////////////
//                                                               //
//    FldAut: The field automorphism object.                     //
//                                                               //
///////////////////////////////////////////////////////////////////

declare type FldAut;
declare attributes FldAut :
  L,   // the field (or etale quadratic extension of a field)
  map, // the mapping
  elt, // the element in the automorphism group
  isom; // the isomorphism between the group and the set of maps

/* constructors */

function fullAutomorphismGroup(L)
   // assert IsField(L);
   if Type(L) eq AlgAss then
       id_map := hom<L->L|[L.1,L.2]>;
       alpha := hom<L->L|[L.2,L.1]>;
       aut := [id_map, alpha];
       gal := Sym(2);
       return gal, aut, map<gal -> aut | <gal!1, aut[1]>, <gal!(1,2), aut[2]> >;
   end if;
   char := Characteristic(L);
   if (char eq 0) then
      gal, aut, phi := AutomorphismGroup(L);
   else
      baseField := FiniteField(char);

      // This special case is needed because AutomorphismGroup(L,L)
      // fails for finite fields !!!!
      if IsFinite(L) and #L eq char then
        gal := GaloisGroup(L,L);
        aut := [ hom<L->L|> ];
        phi := map<gal->aut| <gal!1, aut[1]> >;
      else
        gal, aut, phi := AutomorphismGroup(L, baseField);
      end if;
   end if;
   return gal, aut, phi;
end function;

intrinsic FieldAutomorphism(L::AlgAss[Fld], g::GrpPermElt) -> FldAut
{Return the involution swapping the indices.}
  require Dimension(L) eq 2 :
			    "Algebra must be a quadratic etale algebra.";
  alpha := New(FldAut);
  alpha`L := L;
  S2 := Parent(g);
  alpha`elt := g;
  id_map := hom<L -> L | [L.1, L.2]>;
  alpha`map := hom<L -> L | [L.2, L.1]>;
  alpha`isom := map<S2 -> Parent(alpha`map) | [<S2!1, id_map>,
					       <g, alpha`map> ] >;
  return alpha;
end intrinsic;

intrinsic FieldAutomorphism(L::AlgAss[Fld]) -> FldAut
{Return the involution swapping the indices.}
  return FieldAutomorphism(L, Sym(2)!(1,2));
end intrinsic;

intrinsic FieldAutomorphism(L::Fld, g::GrpPermElt) -> FldAut
{.}
  alpha := New(FldAut);
  alpha`L := L;
  gal, _, psi := fullAutomorphismGroup(L);
  isom, phi := IsIsomorphic(Parent(g), gal);
  require isom :
  "Group element must be in the automorphism group of the field!";
  alpha`elt := phi(g);
  alpha`map := psi(alpha`elt);
  alpha`isom := psi;

  return alpha; 
end intrinsic;

// This is needed because HasComplexConjugate can return a UserProgram
intrinsic FieldAutomorphism(L::Fld, f::UserProgram) -> FldAut
{.}
//   gal, _, psi := AutomorphismGroup(L);
   gal, _, psi := fullAutomorphismGroup(L);
   if IsFinite(L) then
     gens := [L.1];
   else
     gens := Generators(L);
   end if;
   require exists(g){g : g in gal | &and[psi(g)(x) eq f(x) : x in gens]} :
     "Map must be an automorphism of the field!";
   return FieldAutomorphism(L, g);
end intrinsic;

intrinsic FieldAutomorphism(L::Fld, f::Intrinsic) -> FldAut
{.}
   gal, _, psi := fullAutomorphismGroup(L);
   if IsFinite(L) then
     gens := [L.1];
   else
     gens := Generators(L);
   end if;
   require exists(g){g : g in gal | &and[psi(g)(x) eq f(x) : x in gens]} :
     "Map must be an automorphism of the field!";
   return FieldAutomorphism(L, g);
end intrinsic;

intrinsic FieldAutomorphism(L::Fld, f::Map[Fld,Fld]) -> FldAut
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
   return FieldAutomorphism(L, g);
end intrinsic;

intrinsic FieldAutomorphism(L::AlgAss[Fld],
			       f::Map[AlgAss[Fld],AlgAss[Fld]]) -> FldAut
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
    f_in := hom<L -> Domain(f) | [Domain(f).1, Domain(f).2]>;
    f_out := hom<Codomain(f) -> L | [L.1, L.2]>;
    f := f_in * f * f_out;
    gal, _, psi := fullAutomorphismGroup(L);
    gens := [L.1, L.2];
    require exists(g){g : g in gal | &and[psi(g)(x) eq f(x) : x in gens]} :
		  "Map must be an automorphism of the field!";
    return FieldAutomorphism(L, g);
end intrinsic;

/* Printing */
intrinsic Print(alpha::FldAut, level::MonStgElt)
{.}
  if level eq "Magma" then
      printf "FieldAutomorphism(%m, %m!%m)",
	     alpha`L, Parent(alpha`elt), alpha`elt;
  else      
      printf "Field Automorphism of %o", alpha`L;
  end if;
end intrinsic;

/* access */

intrinsic BaseField(alpha::FldAut) -> Fld
{.}
  return alpha`L;
end intrinsic;

intrinsic Order(alpha::FldAut) -> RngIntElt
{.}
  return Order(alpha`elt);
end intrinsic;

intrinsic FixedField(alpha::FldAut) -> Fld
{.}
  // maybe better for all cases:
  // sub<alpha`L | [alpha`L.i + alpha(alpha`L.i) : i in [1..Ngens(alpha`L)]]>
  if IsFinite(alpha`L) or
     ((Type(alpha`L) eq AlgAss) and IsFinite(BaseRing(alpha`L))) then
    return sub<alpha`L|[x : x in alpha`L | alpha(x) eq x]>;
  end if;
  return FixedField(alpha`L, [alpha`map]);
end intrinsic;

intrinsic Automorphism(alpha::FldAut) -> Map[Fld, Fld]
{.}
  return alpha`map;
end intrinsic;

/* arithmetic */

intrinsic '^'(alpha::FldAut, n::RngIntElt) -> FldAut
{.}
  beta := New(FldAut);
  beta`L := alpha`L;
  beta`elt := alpha`elt^n;
  beta`isom := alpha`isom;
  beta`map := beta`isom(beta`elt);

  return beta;
end intrinsic;

intrinsic Inverse(alpha::FldAut) -> FldAut
{.}
  return alpha^(-1);
end intrinsic;

intrinsic '*'(alpha::FldAut, beta::FldAut) -> FldAut
{.}
  require BaseField(alpha) eq BaseField(beta) :
     "Automorphisms should be of the same field";
  
  gamma := New(FldAut);
  gamma`L := alpha`L;
  gamma`elt := alpha`elt * beta`elt;
  gamma`isom := alpha`isom;
  gamma`map := beta`map * alpha`map;

  return gamma;
end intrinsic;

intrinsic 'eq'(alpha::FldAut, beta::FldAut) -> BoolElt
{.}
  return BaseField(alpha) eq BaseField(beta) and alpha`elt eq beta`elt;
end intrinsic;

intrinsic IsIdentity(alpha::FldAut) -> BoolElt
{.}
   return alpha`elt eq Parent(alpha`elt)!1;
end intrinsic;

/* Evaluation */

intrinsic '@'(x::FldElt, alpha::FldAut) -> FldElt
{.}
  return alpha`map(x);
end intrinsic;

intrinsic '@'(x::AlgAssElt[Fld], alpha::FldAut) -> FldElt
{.}
  return alpha`map(x);
end intrinsic;

intrinsic '@'(v::ModTupFldElt[Fld], alpha::FldAut) -> ModTupFldElt
{.}
  V := Parent(v);
  require BaseField(V) eq BaseField(alpha) : "map must be defined on elements!";
  return V![alpha(v[i]) : i in [1..Dimension(V)]];
end intrinsic;

intrinsic '@'(a::AlgMatElt[Fld], alpha::FldAut) -> AlgMatElt[Fld]
{.}
  A := Parent(a);
  require BaseRing(A) eq BaseField(alpha) : "map must be defined on elements!";
  return A![[alpha(a[i,j]) : j in [1..Degree(A)]]
				  : i in [1..Degree(A)]];
end intrinsic;

intrinsic '@'(a::AlgMatElt[AlgAss[Fld]], alpha::FldAut) -> AlgMatElt[Fld]
{.}
  A := Parent(a);
  require BaseRing(A) eq BaseField(alpha) : "map must be defined on elements!";
  return A![[alpha(a[i,j]) : j in [1..Degree(A)]]
				  : i in [1..Degree(A)]];
end intrinsic;

intrinsic '@'(a::ModMatFldElt[Fld], alpha::FldAut) -> ModMatFldElt[Fld]
{.}
  A := Parent(a);
  require BaseRing(A) eq BaseField(alpha) : "map must be defined on elements!";
  return A![[alpha(a[i,j]) : j in [1..Ncols(a)]]
				  : i in [1..Nrows(a)]];
end intrinsic;

intrinsic '@'(I::RngOrdFracIdl[FldOrd], alpha::FldAut) -> RngOrdFracIdl[FldOrd]
{.}
  L := BaseField(alpha);
  Z_L := RingOfIntegers(L);
  require Z_L eq Order(I) :
    "Fractional ideal must be in the ring of integers of the field the automorphism is acting on.";
  return ideal<Z_L | [alpha`map(g) : g in Generators(I)]>;
end intrinsic;

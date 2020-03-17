//freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: combfreemod.m (class for combinatorial free modules)

   03/16/20: Added basic documentation
             Fixed bug in constructor of Homomorphism, when no images are
             given - to construct the zero morphism.

   03/13/20: Added handling of homomorphisms
   	     Created this file from representation.m

   ***************************************************************************/

// This should have been done using GModule
// But for some reason, it's really terrible, so we are doing our own

// CombFreeMod - the combinatorial free module
declare type CombFreeMod[CombFreeModElt];
declare attributes CombFreeMod :
		   // the actual module
		   M,
	// the names of the basis elements
	names;

declare attributes CombFreeModElt :
		   // the actual vector
		   vec,
	// its parent
	parent,
	// its name
	name;

/* constructors */

intrinsic CombinatorialFreeModule(R::Rng,
				  names::SeqEnum[MonStgElt]) -> CombFreeMod
{Construct a combinatorial free module over the ring R with basis given by names.}
  CFM := New(CombFreeMod);
  CFM`names := names;
  CFM`M := RModule(R, #names);
  return CFM;
end intrinsic;

intrinsic CombinatorialFreeModule(R::Rng, S::SetIndx) -> CombFreeMod
{Construct a combinatorial free module over the ring R with basis given by names.}
  CFM := New(CombFreeMod);
  CFM`names := S;
  CFM`M := RModule(R, #S);
  return CFM;
end intrinsic;

// a helper function for representing elements using strings

function createElementString(coeffs, names)
  dim := #names;
  function getCoeffString(coeff : is_first := false)
      if coeff eq 1 then return is_first select "" else " + "; end if;
      if coeff eq -1 then return is_first select "-" else " - "; end if;
      ret := Sprintf("%o*", coeff);
      if ("+" in ret[2..#ret]) or ("-" in ret[2..#ret]) then
	  ret := "(" cat ret cat ")";
      else
	  if ret[1] eq "-" then
	      prefix := is_first select "-" else " - "; 
	      return prefix cat ret[2..#ret];
	  end if;
      end if;
      if (not is_first) then
	  ret := " + " cat ret;
      end if;
      
      return ret;
  end function;
  idxs := [i : i in [1..dim] | coeffs[i] ne 0];
  if IsEmpty(idxs) then return "0"; end if;
  coeffs_strs := [getCoeffString(coeffs[idxs[1]] : is_first := true)];
  coeffs_strs cat:= [getCoeffString(coeffs[idxs[i]]) : i in [2..#idxs]];
  summands := [Sprintf("%o%o", coeffs_strs[i],
		       names[idxs[i]]) : i in [1..#idxs]];
  ret := &cat summands;

  return ret;
end function;

// access

intrinsic Rank(CFM::CombFreeMod) -> RngIntElt
{Return the rank of CFM.}
  return #Basis(CFM);	  
end intrinsic;

intrinsic Dimension(CFM::CombFreeMod) -> RngIntElt
{Return the rank of CFM.}
  return Rank(CFM);	  
end intrinsic;

intrinsic Basis(CFM::CombFreeMod) -> SeqEnum[CombFreeModElt]
{Return a basis for CFM.}
  return [CFM!b : b in Basis(CFM`M)];
end intrinsic;

intrinsic BaseRing(CFM::CombFreeMod) -> Rng
{return the ring over which CFM is defined.}
  return BaseRing(CFM`M);
end intrinsic;

/*
CombFreeModElt - the element class
*/

/* constructor */

intrinsic CombinatorialFreeModuleElement(CFM::CombFreeMod,
					      v::ModRngElt) -> CombFreeModElt
{Construct an element of CFM whose underlying vector is v.}
  elt := New(CombFreeModElt);
  elt`vec := v;
  elt`parent := CFM;
  dim := Dimension(CFM`M);
  elt`name := createElementString(Eltseq(v), CFM`names);

  return elt;
end intrinsic;

/* access */

intrinsic Parent(elt::CombFreeModElt) -> CombFreeMod
{.}
  return elt`parent;
end intrinsic;

/* generators and coercion */

intrinsic '.'(CFM::CombFreeMod, i::RngIntElt) -> CombFreeModElt
{.}
  return CombinatorialFreeModuleElement(CFM, CFM`M.i);	     
end intrinsic;

intrinsic IsCoercible(CFM::CombFreeMod, x::Any) -> BoolElt, .
{.}
  if Type(x) eq CombFreeModElt and Parent(x) eq CFM then return true, x; end if;
  is_coercible, v := IsCoercible(CFM`M, x);
  if is_coercible then
      return true, CombinatorialFreeModuleElement(CFM, v);
  else
      return false, "Illegal Coercion";
  end if;
end intrinsic;

/* booleans, equality and hashing */

intrinsic 'eq'(M1::CombFreeMod, M2::CombFreeMod) -> BoolElt
{.}
  return BaseRing(M1) eq BaseRing(M2) and Dimension(M1) eq Dimension(M2) and
       M1`M eq M2`M and M1`names eq M2`names;
end intrinsic;

intrinsic Hash(CFM::CombFreeMod) -> RngIntElt
{.}
  name_tuple := < name : name in CFM`names >;
  return Hash(<CFM`M, name_tuple>);
end intrinsic;

/* printing */

intrinsic Print(CFM::CombFreeMod, level::MonStgElt)
{.}
  desc := Sprintf("Free module of rank %o over %o",
		  Dimension(CFM`M), BaseRing(CFM`M));
  if (level eq "Minimal") then printf "%o", desc; return; end if; 
  names := CFM`names;
  MAX_LEN := 5;
  if (level eq "Default") and (#names gt MAX_LEN) then
      names := names[1..MAX_LEN];
      suffix := "...";
  else
      suffix := "";
  end if;
  desc := desc cat Sprintf(", with basis %o", names) cat suffix;
  if (level ne "Magma") then printf "%o", desc; return; end if;
end intrinsic;


// SubConstructor always returns the second value as a map,
// which we wish to avoid.

intrinsic SubCFModule(CFM::CombFreeMod, t::.) -> CombFreeMod, CombFreeModHom
{Construct the submodule generated by t.}
  t := [CFM!x : x in Flat(t)];
  N, iota := sub<CFM`M | [m`vec : m in t]>;

  // rethink that - maybe I would prefer to rename them
  // names := [(CFM!N.i)`name : i in [1..Ngens(N)]];
  names := [Sprintf("v%o", i) : i in [1..Ngens(N)]];

  CFN := CombinatorialFreeModule(BaseRing(CFM), names);

  emb := Homomorphism(CFN, CFM, [CFM!Eltseq(iota(N.i)) :
				 i in [1..Dimension(N)]]);
  return CFN, emb;
end intrinsic;

/* elements */

intrinsic Hash(elt::CombFreeModElt) -> RngIntElt
{.}
  return Hash(<elt`vec, elt`parent>);
end intrinsic;

intrinsic Print(elt::CombFreeModElt)
{.}
  printf elt`name;		   
end intrinsic;

/* arithmetic operations */ 

intrinsic '+'(elt_l::CombFreeModElt, elt_r::CombFreeModElt) -> CombFreeModElt
{.}
  require Parent(elt_l) eq Parent(elt_r) : "elements must belong to the same module";
  M := Parent(elt_l);
  return CombinatorialFreeModuleElement(M, elt_l`vec + elt_r`vec);
end intrinsic;

intrinsic '-'(elt_l::CombFreeModElt, elt_r::CombFreeModElt) -> CombFreeModElt
{.}
  require Parent(elt_l) eq Parent(elt_r) : "elements must belong to the same module";
  M := Parent(elt_l);
  return CombinatorialFreeModuleElement(M, elt_l`vec - elt_r`vec);
end intrinsic;

intrinsic '*'(scalar::RngElt, elt::CombFreeModElt) -> CombFreeModElt
{.}
  M := Parent(elt);
  return CombinatorialFreeModuleElement(M, scalar * elt`vec);
end intrinsic;

intrinsic Eltseq(elt::CombFreeModElt) -> SeqEnum
{.}
  return Eltseq(elt`vec);
end intrinsic;

/* morphisms */
// for some reason, just havin map<V->W|f> doesn't work. no idea why

declare type CombFreeModHom;
declare attributes CombFreeModHom :
		   domain,
	codomain,
	morphism;

/* constructors */
	   
intrinsic Homomorphism(V::CombFreeMod, W::CombFreeMod,
					  f::UserProgram) -> CombFreeModHom
{Construct the morphism described by f.}
  phi := New(CombFreeModHom);
  phi`domain := V;
  phi`codomain := W;
  phi`morphism := hom<V`M -> W`M | [f(V.i)`vec : i in [1..Dimension(V)]]>;

  return phi;
end intrinsic;

intrinsic Homomorphism(V::CombFreeMod, W::CombFreeMod, f::Map) -> CombFreeModHom
{Construct the morphism described by f.}
  phi := New(CombFreeModHom);
  phi`domain := V;
  phi`codomain := W;

  require (Domain(f) eq V`M) and (Codomain(f) eq W`M) :
	"Map should be defined on the underlying modules"; 
  phi`morphism := hom<V`M -> W`M | [f(V.i) : i in [1..Dimension(V)]]>;

  return phi;
end intrinsic;

intrinsic Homomorphism(V::CombFreeMod, W::CombFreeMod,
					  basis_images::SeqEnum) -> CombFreeModHom
{Construct the morphism sending the basis of V to basis_images.}
  phi := New(CombFreeModHom);
  phi`domain := V;
  phi`codomain := W;

  require IsEmpty(basis_images) or (Universe(basis_images) eq W) :
	"images should be in the codomain module"; 
  phi`morphism := hom<V`M -> W`M | [v`vec : v in basis_images]>;

  return phi;
end intrinsic;

/* access */

intrinsic Domain(phi::CombFreeModHom) -> CombFreeMod
{.}
  return phi`domain;
end intrinsic;

intrinsic Codomain(phi::CombFreeModHom) -> CombFreeMod
{.}
  return phi`codomain;
end intrinsic;

/* printing */

intrinsic Print(phi::CombFreeModHom)
{.}
  printf "Homorphism from %o to %o", Domain(phi), Codomain(phi);
end intrinsic;

/* evaluation, pre-image */

intrinsic Evaluate(phi::CombFreeModHom, v::CombFreeModElt) -> CombFreeModElt
{.}
  V := Domain(phi);
  W := Codomain(phi);
  require v in V : "Element should be in domain of the morphism";

  return W!(phi`morphism(V`M!Eltseq(v)));
end intrinsic;

intrinsic '@'(v::CombFreeModElt, phi::CombFreeModHom) -> CombFreeModElt
{.}
  return Evaluate(phi, v);	     
end intrinsic;

intrinsic '@@'(w::CombFreeModElt, phi::CombFreeModHom) -> CombFreeModElt
{.}
  V := Domain(phi);
  W := Codomain(phi);
  require w in W : "Element should be in the codomain of the morphism";

  return V!((W`M!Eltseq(w))@@(phi`morphism));
end intrinsic;


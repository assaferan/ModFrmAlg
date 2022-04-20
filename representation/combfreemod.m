freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: combfreemod.m (class for combinatorial free modules)

   04/21/20 : Fixed bugs in ChangeRing.

   04/20/20 : Modified Print to overcome the difficulty of introducing line 
   	      breaks in printed strings

   04/03/20: Added ChangeRing Intrinsic, added some coercions, changed construction of homomorphisms
             to support loading from files

   04/02/20: Fixed bugs in intrinsic 'eq' to handle several different cases of names

   04/01/20: Added the intrinsics 'in' and Ngens, added params to the constructor,
             so we would be able to record the names in the universe of the underlying set.

   03/31/20: Added Magma level printing for serialization (pickling), changed Homomorphism to handle
             reading and writing from disk.

   03/16/20: Added basic documentation
             Fixed bug in constructor of Homomorphism, when no images are
             given - to construct the zero morphism.

   03/13/20: Added handling of homomorphisms
   	     Created this file from representation.m

******************************************************************************/

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
				  names::SeqEnum[MonStgElt] : params := [* *]) -> CombFreeMod
{Construct a combinatorial free module over the ring R with basis given by names.}
  CFM := New(CombFreeMod);
  CFM`names := names;
  CFM`M := RModule(R, #names);
  return CFM;
end intrinsic;

intrinsic CombinatorialFreeModule(R::Rng, S::SetIndx : params := [* *]) -> CombFreeMod
{Construct a combinatorial free module over the ring R with basis given by names.}
  CFM := New(CombFreeMod);

  // An associative array which stores the appropriate meta data.
  param_array := AssociativeArray();

  // Store meta data.
  for entry in params do param_array[entry[1]] := entry[2]; end for;
  //CFM`names := S;
  U := Universe(S);
  // If these are polynomials, this is algebraic and we want the fields
  // to match
  if Type(U) eq RngMPol then
    U := ChangeRing(U, R);
  end if;
  CFM`names := {@ U | s : s in S @};
  if IsDefined(param_array, "NAMES") then
      AssignNames(~U, param_array["NAMES"]);
  end if;
  
  CFM`M := RModule(R, #S);
  return CFM;
end intrinsic;

// a helper function for representing elements using strings

function createElementString(coeffs, names)
  dim := #names;
  function getCoeffString(coeff : is_first := false)
      if coeff eq 1 then return is_first select "" else " + "; end if;
      if coeff eq -1 then return is_first select "-" else " - "; end if;
      ret := Sprintf("%o", coeff);
      if ("+" in ret[2..#ret]) or ("-" in ret[2..#ret]) then
	  ret := "(" cat ret cat ")";
      else
	  if ret[1] eq "-" then
	      prefix := is_first select "-" else " - "; 
	      ret := prefix cat ret[2..#ret];
	      is_first := true;
	  end if;
      end if;
      if (not is_first) then
	  ret := " + " cat ret;
      end if;
      
      return ret cat "*";
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
// return #Basis(CFM);
   return Rank(CFM`M);
end intrinsic;

intrinsic Dimension(CFM::CombFreeMod) -> RngIntElt
{Return the rank of CFM.}
// return Rank(CFM);
  return Dimension(CFM`M);
end intrinsic;

intrinsic Ngens(CFM::CombFreeMod) -> RngIntElt
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

intrinsic Names(CFM::CombFreeMod) -> .
{return the names of the basis elements.}
  return CFM`names;
end intrinsic;

intrinsic ChangeRing(CFM::CombFreeMod, R::Rng) -> CombFreeMod
{return the CFM with base ring changed to R.}
  params := [* *];
  if (not IsEmpty(CFM`names)) and (Type(Universe(CFM`names)) eq RngMPol) then
      Append(~params, <"NAMES", Names(Universe(CFM`names))>);
  end if;
  return CombinatorialFreeModule(R, CFM`names : params := params);
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

intrinsic CombinatorialFreeModuleElement(CFM::CombFreeMod,
					      v::ModEDElt) -> CombFreeModElt
{Construct an element of CFM whose underlying vector is v.}
  elt := New(CombFreeModElt);
  elt`vec := v;
  elt`parent := CFM;
  dim := Dimension(CFM`M);
  elt`name := createElementString(Eltseq(v), CFM`names);

  return elt;
end intrinsic;  

intrinsic CombinatorialFreeModuleElement(CFM::CombFreeMod,
			  v::ModTupFldElt[Fld]) -> CombFreeModElt
{Construct an element of CFM whose underlying vector is v.}
  elt := New(CombFreeModElt);
  elt`vec := v;
  elt`parent := CFM;
  dim := Dimension(CFM`M);
  elt`name := createElementString(Eltseq(v), CFM`names);

  return elt;
  end intrinsic;
  
/*
intrinsic CombinatorialFreeModuleElement(CFM::CombFreeMod,
			  v::ModTupFldElt[FldNum[FldRat]]) -> CombFreeModElt
{Construct an element of CFM whose underlying vector is v.}
  elt := New(CombFreeModElt);
  elt`vec := v;
  elt`parent := CFM;
  dim := Dimension(CFM`M);
  elt`name := createElementString(Eltseq(v), CFM`names);

  return elt;
end intrinsic;

intrinsic CombinatorialFreeModuleElement(CFM::CombFreeMod,
			  v::ModTupFldElt[FldRat]) -> CombFreeModElt
{Construct an element of CFM whose underlying vector is v.}
  elt := New(CombFreeModElt);
  elt`vec := v;
  elt`parent := CFM;
  dim := Dimension(CFM`M);
  elt`name := createElementString(Eltseq(v), CFM`names);

  return elt;
end intrinsic;
*/

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
  if Type(x) eq CombFreeModElt then
      is_coercible, v := IsCoercible(CFM`M, x`vec);
  else
      is_coercible, v := IsCoercible(CFM`M, x);
  end if;
  if is_coercible then
      return true, CombinatorialFreeModuleElement(CFM, v);
  else
      return false, "Illegal Coercion";
  end if;
end intrinsic;

intrinsic 'in'(elt::CombFreeModElt, V::CombFreeMod) -> BoolElt
{.}
  return Parent(elt) eq V;
end intrinsic;

/* booleans, equality and hashing */

intrinsic 'eq'(M1::CombFreeMod, M2::CombFreeMod) -> BoolElt
{.}
  if not (BaseRing(M1) eq BaseRing(M2) and Dimension(M1) eq Dimension(M2)) then
      return false;
  end if;
  if IsEmpty(M1`names) then
      return IsEmpty(M2`names);
  end if;
  if Type(Universe(M1`names)) ne Type(Universe(M2`names)) then
    return false;
  end if;
  if Type(Universe(M1`names)) eq RngMPol then  
      U1 := Universe(M1`names);
      U2 := Universe(M2`names);
      if Type(BaseRing(U1)) eq FldRat then
        is_isom := IsIsomorphic(BaseRing(U1), BaseRing(U2));
        if is_isom then psi := hom<BaseRing(U1) -> BaseRing(U2)|>; end if;
      elif Type(BaseRing(U2)) eq FldRat then
	is_isom := IsIsomorphic(BaseRing(U1), BaseRing(U2));
        if is_isom then psi := hom<BaseRing(U1) -> BaseRing(U2)| 1 >; end if;
      elif Type(BaseRing(U1)) eq FldFin then
	  if Type(BaseRing(U2)) ne FldFin then return false; end if;
	  return BaseRing(U1) eq BaseRing(U2);
      else
	is_isom, psi := IsIsomorphic(BaseRing(U1), BaseRing(U2));
      end if;
      
      if not is_isom or Ngens(U1) ne Ngens(U2) then
	  return false;
      end if;
      phi := hom<U1 -> U2 | psi, GeneratorsSequence(U2)>;
      return &and[phi(M1`names[i]) eq M2`names[i] : i in [1..#M1`names]];
  end if;
  if #M1`names ne #M2`names then return false; end if;
  return &and[&cat Split(M1`names[i], " \n") eq &cat Split(M2`names[i], " \n")
	    : i in [1..#M1`names]];
end intrinsic;

intrinsic Hash(CFM::CombFreeMod) -> RngIntElt
{.}
  name_tuple := < name : name in CFM`names >;
  return Hash(<CFM`M, name_tuple>);
end intrinsic;

/* printing */

function polynomialPrint(s)
  R := Parent(s);
  prefix_str := Sprintf("[ %m |\n", R);
  mon_strs := [Sprintf("Monomial(%m, %m)", R,
		       [Degree(m,i) : i in [1..Ngens(R)]]) : m in Monomials(s)];
  all_mon_str := ["\t" cat m_str cat ",\n"
		     : m_str in mon_strs[1..#mon_strs-1]];
  Append(~all_mon_str, "\t" cat mon_strs[#mon_strs] cat "\n]\n");
  all_mon_str := prefix_str cat (&cat all_mon_str);
  coefs_strs := Sprintf("%m", Coefficients(s));
  return Sprintf("Polynomial(%o, %o)", coefs_strs, all_mon_str);
end function;

intrinsic Print(CFM::CombFreeMod, level::MonStgElt)
{.}
    if (level eq "Magma") then
	params := [* *];
    if (not IsEmpty(CFM`names)) and (Type(Universe(CFM`names)) eq RngMPol) then
	  S := CFM`names;
	  R_X := Universe(S);
	  prefix_str := Sprintf("{@ %m |\n", R_X);
// mon_strs := [Sprintf("Monomial(%m, %m)", R_X, [Degree(s,i) : i in [1..Ngens(R// _X)]]) : s in S];
          poly_strs := [polynomialPrint(s) : s in S];
//all_mon_str := ["\t" cat m_str cat ",\n" : m_str in mon_strs[1..#mon_strs-1]];
          all_poly_str := ["\t" cat m_str cat ",\n"
			      : m_str in poly_strs[1..#poly_strs-1]];
// Append(~all_mon_str, "\t" cat mon_strs[#mon_strs] cat "\n@}\n");
          Append(~all_poly_str, "\t" cat poly_strs[#poly_strs] cat "\n@}\n");
	  names_str := prefix_str cat (&cat all_poly_str);
	  Append(~params, <"NAMES", Names(R_X)>);
	else
	    // we wanted to do this:
	    // names_str := Sprintf("%m", CFM`names);
	    // but when writing a list of strings, when there is a line break,
	    // magma might break the string
	    names_str := "[ Strings () | ";
	    if not IsEmpty(CFM`names) then
		names_str cat:= Sprintf("%m", CFM`names[1]);
	    end if;
	    for name in CFM`names[2..#CFM`names] do
		names_str cat:= Sprintf(",\n%m", name);
	    end for;
	    names_str cat:= "]";
	end if;
	printf "CombinatorialFreeModule(%m, %o : params := %m)", BaseRing(CFM`M), names_str, params;  
	return;
  end if;
  R := BaseRing(CFM`M);
  if Type(R) eq FldOrd then 
    R := NumberField(MaximalOrder(BaseRing(CFM`M)));
  end if;
  if (not IsFinite(R)) and IsField(R) and (Degree(R) eq 1) then
      R := Rationals();
  end if;
  desc := Sprintf("free module of rank %o over %o",
		  Dimension(CFM`M), R);
  if (level ne "Maximal") then printf "%o", desc; return; end if; 
  names := CFM`names;
  MAX_LEN := 5;
  if (#names gt MAX_LEN) then
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

// Constructing exterior (alternating) powers
function make_wedge_str(names, seq)
  if IsEmpty(seq) then
      return "1";
  end if;
  ret := Sprintf("%o", names[seq[1]]);
  for i in [2..#seq] do
    ret cat:= Sprintf("^%o", names[seq[i]]);
  end for;
  return ret;
end function;

intrinsic ExteriorPower(M::CombFreeMod, n::RngIntElt) -> CombFreeMod
{Construct the exterior power wedge^n M.}
  R := BaseRing(M);
  indices := Sort([SetToSequence(s) : s in Subsets(Set([1..Dimension(M)]),n)]);
  keys := {@ make_wedge_str(M`names, s) : s in indices @};
  return CombinatorialFreeModule(R, keys);
end intrinsic;

intrinsic AlternatingPower(M::CombFreeMod, n::RngIntElt) -> CombFreeMod
{Construct the alternating power wedge^n M.}
  return ExteriorPower(M,n);
end intrinsic;

intrinsic DirectSum(MM::SeqEnum[CombFreeMod]) -> CombFreeMod
{Construct the direct sum of the modules}
  if IsEmpty(MM) then
    return CombinatorialFreeModule(Integers(), {@ Strings() | @});
  end if;
  R := BaseRing(MM[1]);
  keys := &join[M`names : M in MM];
  return CombinatorialFreeModule(R, keys);
end intrinsic;

/* elements */

intrinsic Hash(elt::CombFreeModElt) -> RngIntElt
{.}
  return Hash(<elt`vec, elt`parent>);
end intrinsic;

intrinsic Print(elt::CombFreeModElt, level::MonStgElt)
{.}
  if level eq "Magma" then
      printf "%m ! %m", Parent(elt), Eltseq(elt);
      return;
  end if;
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

intrinsic ChangeRing(elt::CombFreeModElt, R::Rng) -> CombFreeModElt
{.}
  return ChangeRing(Parent(elt),R)!(Vector(ChangeRing(elt`vec, R)));
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
  require BaseRing(V) eq BaseRing(W) : "To define a homomorphism, 
  	  	      	 modules should be defined over the same ring";

  phi := New(CombFreeModHom);
  phi`domain := V;
  phi`codomain := W;
  phi`morphism := hom<V`M -> W`M | [f(V.i)`vec : i in [1..Dimension(V)]]>;

  return phi;
end intrinsic;

intrinsic Homomorphism(V::CombFreeMod, W::CombFreeMod, f::Map) -> CombFreeModHom
{Construct the morphism described by f.}
  require BaseRing(V) eq BaseRing(W) : "To define a homomorphism, 
  	  	      	 modules should be defined over the same ring";

  phi := New(CombFreeModHom);
  phi`domain := V;
  phi`codomain := W;

  require (Domain(f) eq V`M) and (Codomain(f) eq W`M) :
	"Map should be defined on the underlying modules"; 
  phi`morphism := hom<V`M -> W`M | [f(V.i) : i in [1..Dimension(V)]]>;

  return phi;
end intrinsic;

intrinsic Homomorphism(V::CombFreeMod, W::CombFreeMod,
					  basis_images::SeqEnum
		      : FromFile := false) -> CombFreeModHom
{Construct the morphism sending the basis of V to basis_images.}
/*  require BaseRing(V) eq BaseRing(W) : "To define a homomorphism, 
  	  	      	 modules should be defined over the same ring";
*/
  phi := New(CombFreeModHom);
  phi`domain := V;
  if FromFile then
      W := ChangeRing(W, BaseRing(V));
  else
      require BaseRing(V) eq BaseRing(W) : "To define a homomorphism, 
  	  	      	 modules should be defined over the same ring";
  end if;
  phi`codomain := W;

  require IsEmpty(basis_images) or IsCoercible(W,basis_images[1]) :
	"images should be in the codomain module"; 
  phi`morphism := hom<V`M -> W`M | [Eltseq(W!v) : v in basis_images]>;
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

intrinsic Print(phi::CombFreeModHom, level::MonStgElt)
{.}
  if level eq "Magma" then
      images := [Eltseq(phi(Domain(phi).i)) : i in [1..Dimension(Domain(phi))]];
      printf "Homomorphism(%m, %m, %m : FromFile := true)", Domain(phi), Codomain(phi), images;
      return;
  end if;
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

intrinsic ExteriorAlgebra(M::CombFreeMod) -> CombFreeMod, CombFreeModHom
{Returns the exterior algebra of M, together with an embedding of M as the degree 1 component.}
  n := Dimension(M);
  EM := DirectSum([ExteriorPower(M,i) : i in [0..n]]);
  phi := Homomorphism(M, EM, [EM.i : i in [2..Dimension(M)+1]]);
  return EM, phi;
end intrinsic;

// TODO : The right thing to d here is to have graded combinatorial free modules as a different category.
intrinsic Degree(v::CombFreeModElt) -> RngIntElt
{Return the degree of v. Assumes Parent(v) is an exterior algebra.}
  return 0;	  
end intrinsic;

function wedge(I,J)
    I := {@ x : x in I @};
    J := {@ x : x in J @};
    if not IsEmpty(I meet J) then
	return [], 0;
    end if;
    IJ := I join J;
    sorted := Sort(IJ);
    if IsEmpty(IJ) then
	sign := 1;
    else
	sign := Sign(Sym(#IJ)![Index(IJ,x) : x in sorted]);
    end if;
    return sorted, sign;
end function;

function get_index_set(EM, i)
    if i eq 1 then
	return {@ @};
    end if;
    return {@ Index(EM`names, x)-1 : x in Split((EM.i)`name, "^") @};
end function;

function elt_by_name(V, name)
    return V.(Index(V`names, name));
end function;

function elt_by_subset(V, I)
    if IsEmpty(I) then
	return V.1;
    end if;
    return elt_by_name(V, Join([V`names[i+1] : i in I], "^"));
end function;

function clifford_reduce(I,Q,C)
    for i in [1..#I-1] do
	if (I[i] ge I[i+1]) then
	    reduced := Q[I[i],I[i+1]]*clifford_reduce(I[1..i-1] cat I[i+2..#I], Q, C);
	    if I[i] eq I[i+1] then
		return 1/2*reduced;
	    else
		return reduced-clifford_reduce(I[1..i-1] cat [I[i+1], I[i]] cat I[i+2..#I], Q, C);
	    end if;
	end if;
    end for;
    return elt_by_subset(C, I);
end function;

function clifford_wedge(I, J, Q, C)
    I := [ x : x in I ];
    J := [ x : x in J ];
    return clifford_reduce(I cat J, Q, C);
end function;

function clifford_wedge_basis(V,i,j,Q)
    I := get_index_set(V, i);
    J := get_index_set(V, j);
    return clifford_wedge(I,J,Q,V);
end function;

function clifford_wedge_vecs(v1, v2, Q)
   V := Parent(v1);
   s := V!0;
   n := Dimension(V);
   for i in [1..n] do
       for j in [1..n] do
	   s +:= v1`vec[i]*v2`vec[j]*clifford_wedge_basis(V, i, j, Q);
       end for;
   end for;
   return s;
end function;

function wedge_basis(EM, i, j)
    I := get_index_set(EM, i);
    J := get_index_set(EM, j);
    IJ, s := wedge(I,J);
//    name := Join([EM`names[i+1] : i in IJ], "^");
//    if IsEmpty(IJ) then
//	name := "1";
//    end if;
    //    return s*elt_by_name(EM, name);
    return s * elt_by_subset(EM, IJ);
end function;

intrinsic '^'(v1::CombFreeModElt, v2::CombFreeModElt) -> CombFreeModElt
{Returns the wedge product v1^v2. Assumes these are vectors in an exterior algebra.}
   require Parent(v1) eq Parent(v2) : "vectors should be in the same module!";
   V := Parent(v1);
   s := V!0;
   n := Dimension(V);
   for i in [1..n] do
       for j in [1..n] do
	   s +:= v1`vec[i]*v2`vec[j]*wedge_basis(V, i, j);
       end for;
   end for;
   return s;
end intrinsic;

function D_theta(theta, v)
    W := Domain(theta);
    B := Basis(W);
    V := Parent(v);
    s := V!0;
    n := Dimension(V);
    for j in [1..n] do
	I := get_index_set(V, j);
	elt := &+([V!0] cat [(-1)^(i-1)*theta(B[I[i]])* elt_by_subset(V, I diff {@ I[i] @}) : i in [1..#I]]);
	s +:= v`vec[j]*elt;
    end for;
    return s;
end function;

function get_v_mat(v)
    Vpp := Parent(v);
    F := BaseRing(Vpp);
    witt := Vpp`WittIndex;
    assert 2*witt + 1 eq Dimension(Vpp);
    std_basis := Transpose(Vpp`Basis);
    coords := Solution(std_basis, v);
    w := Rows(std_basis)[1..witt];
    w_prime := Rows(std_basis)[witt+1..2*witt];
    u := std_basis[2*witt+1];
    norm_u := (u*Vpp`GramMatrix, u);
    is_sqr, sqrt2 := IsSquare(F!2 / norm_u);
    assert is_sqr;
    u *:= sqrt2;
    assert (u*Vpp`GramMatrix, u) eq 2;
    W := VectorSpaceWithBasis(w);
    W_prime := VectorSpaceWithBasis(w_prime);
    M := CombinatorialFreeModule(F, [Sprintf("x%o", i) : i in [1..witt]]);
    EM, phi := ExteriorAlgebra(M);
    v_W := Eltseq(coords)[1..witt];
    v_W_prime := &+[Eltseq(coords)[witt+j]*w_prime[j] : j in [1..witt]];
    v_u := coords[2*witt+1] / sqrt2;
    assert v eq &+[v_W[i]*w[i] : i in [1..witt]] + v_W_prime + v_u * u;
    im_v_W := Matrix([(phi(M!v_W)^b)`vec : b in Basis(EM)]);
    theta := hom<W -> F | w :-> (v_W_prime * Vpp`GramMatrix, w)>;
    im_v_W_prime := Matrix([D_theta(theta, b)`vec : b in Basis(EM)]);
    im_v_u := v_u*Matrix([(-1)^(#get_index_set(EM,i))*(EM.i)`vec : i in [1..Dimension(EM)]]);
    return im_v_W + im_v_W_prime + im_v_u;
end function;

function get_clifford_mat(v_C, V, emb)
    n := Dimension(V);
    e := [emb(V.i) : i in [1..n]];
    indices := [Sort([SetToSequence(x) : x in Subsets({1..n},k)]) : k in [0..n]];
    my_basis := &cat[[&*([1] cat [e[i] : i in I]) : I in indices[k]] : k in [1..n+1]];
    comps := Solution(Matrix(my_basis), v_C)[1];
    F := BaseRing(V);
    d := Dimension(V) div 2;
    one := IdentityMatrix(F, 2^d);
    return &+[comps[j]*(&*([one] cat [get_v_mat(V.i) : i in (&cat indices)[j]])) : j in [1..2^n]];
end function;

import "representation.m" : find_reflection_pts, projLocalization;

// we start with some g in SO(Q), e.g.
// g := Random(AutomorphismGroup(L));
// g := PullUp(Matrix(g), L, L);

function get_spin_matrix_action(g, pR, L)
   n := Dimension(L); 
   p_basis := L`pMaximal[pR][2];
   gg := p_basis * Matrix(Transpose(g)) * p_basis^(-1);
   Vpp := L`Vpp[pR]`V;
   gg := projLocalization(gg, L`Vpp[pR]`proj_pR);
   assert gg * Vpp`GramMatrix * Transpose(gg) eq Vpp`GramMatrix;
   F := BaseRing(Vpp);
   g_p := Matrix(GL(n,F)!Eltseq(gg));
   C_p, V_p, emb_p := CliffordAlgebra(1/2*Vpp`GramMatrix);
   vecs := find_reflection_pts(g_p, Vpp`GramMatrix);
   x_g := &*[emb_p(v) : v in Reverse(vecs)];
   is_sqr, sqrt := IsSquare(Norm(x_g));
   assert is_sqr; // SO should come from elements with norm 1
   x_g /:= sqrt;
   assert &and[x_g*emb_p(v)*x_g^(-1) eq emb_p(v*g_p) : v in Basis(Vpp)];
   return get_clifford_mat(x_g, Vpp, emb_p);
end function;

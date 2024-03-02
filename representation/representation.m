freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J. Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
                           
                                                                            
   FILE: representation.m (class for group representations)

   05/04/20: Fixed a bug in reading and writing a representation defined by
             a highest weight over a finite field. The relevant attributes 
	     weren`t read or written so far.
             Added multiplication by a non-invertible matrix 
	     (so far, only a matrix on the underlying vector space)

   04/20/20: Changed pullback to save the description instead of the function.

   04/13/20: Modified DimensionOfHighestWeightModule, as it is not supported 
             in newer versions of Magma.

   04/03/20: Added references to original representation in cases of
             dual and symmetric representations. Also added a flag for
             the standard representation, so that upon construction we can
             match the base rings of group and module, even when loading
             from a file.
             Changed the action description to include the representation
             as an argument, and so be self-contained.
             Modified the names in tensor product to be strings, and so 
             simplify saving and loading from files.
             Added the function build_rep_params that constructs all the 
             parameters of the representation.
             Added the ChangeRing Intrinsic.
             Modified construction of homomorphisms to support loading from
             files.

   04/01/20: Added the attribute action_desc to a representation, so we will
             be able to read and write to disk (serialization).
             This was needed because UserProgram does not support any, so 
             to record the action, we actually record the code that
             produces it.
             Added params to constructor, also to be able to load from disk
             when there are special flags to the representation.
             Changed all constructors to comply.
             Added Magma level printing.
             Changed 'eq' accordingly.

   03/29/20: Added verbose to FixedSubspace. 
             Added the function getActionMatrix to get the matrix 
             representing an element in a GrpLie in a certain weight 
	     representation.
             Added a FixedSubspace intrinsic for such a case.
             Added a constructor for a GroupRepresentation from
             a Lie group and a weight - good for finite characteristic.

   03/26/20: Modified FixedSubspace to handle representation over any
             coefficient ring.

   03/25/20: Fixed the (horrible!) bug in getActionHom by transposing the 
             matrices(!!!)

   03/23/20: Changed getGL3HighestWeightRep to work also when either
             a or b are zero.

   03/16/20: Added basic documentation
   	     Added operator @@ (preimage) 

   03/13/20: Added handling of homomorphisms
   	     Separated CombinatorialFreeModule to a separate file.

   03/12/20: started writing this file
 
 ***************************************************************************/

// Here are the intrinsics this file defines
// GroupRepresentation(G::Grp, M::CombFreeMod, action_desc::MonStgElt) -> GrpRep
// Subrepresentation(V::GrpRep, t::.) -> GrpRep, GrpRepHom
// TrivialRepresentation(G::Grp, R::Rng) -> GrpRep
// StandardRepresentation(G::GrpMat) -> GrpRep
// DeterminantRepresentation(G::GrpMat) -> GrpRep
// SymmetricRepresentation(V::GrpRep, n::RngIntElt) -> GrpRep
// AlternatingRepresentation(V::GrpRep, n::RngIntElt) -> GrpRep
// DualRepresentation(V::GrpRep) -> GrpRep
// TensorProduct(V::GrpRep, W::GrpRep) -> GrpRep
// TensorPower(V::GrpRep, d::RngIntElt) -> GrpRep
// Pullback(V::GrpRep, f_desc::MonStgElt, H::Grp) -> GrpRep
// Rank(V::GrpRep) -> RngIntElt
// Dimension(V::GrpRep) -> RngIntElt
// Ngens(V::GrpRep) -> RngIntElt
// Basis(V::GrpRep) -> SeqEnum
// BaseRing(V::GrpRep) -> Rng
// Group(V::GrpRep) -> Grp
// CFM(V::GrpRep) -> CombFreeMod
// ChangeRing(V::GrpRep, R::Rng) -> GrpRep
// Print(V::GrpRep, level::MonStgElt)
// '.'(V::GrpRep, i::RngIntElt) -> GrpRepElt
// IsCoercible(V::GrpRep, x::Any) -> BoolElt, .
// 'in'(elt::GrpRepElt, V::GrpRep) -> BoolElt
// GroupRepresentationElement(V::GrpRep, m::CombFreeModElt) -> GrpRepElt
// Parent(elt::GrpRepElt) -> GrpRep
// Eltseq(elt::GrpRepElt) -> SeqEnum
// Print(elt::GrpRepElt, level::MonStgElt)
// getMatrixAction(V::GrpRep, g::GrpElt) -> GrpMatElt
// '*'(g::GrpElt, v::GrpRepElt) -> GrpRepElt
// '*'(m::AlgMatElt, v::GrpRepElt) -> GrpRepElt
// '+'(elt_l::GrpRepElt, elt_r::GrpRepElt) -> GrpRepElt
// '-'(elt_l::GrpRepElt, elt_r::GrpRepElt) -> GrpRepElt
// '*'(scalar::RngElt, elt::GrpRepElt) -> GrpRepElt
// 'eq'(V1::GrpRep, V2::GrpRep) -> BoolElt
// Hash(V::GrpRep) -> RngIntElt
// 'eq'(v1::GrpRepElt, v2::GrpRepElt) -> BoolElt
// Hash(v::GrpRepElt) -> RngIntElt
// 'in'(v::., V::GrpRep) -> BoolElt
// Intersection(V::GrpRep, W::GrpRep) -> GrpRep
// 'meet'(V::GrpRep, W::GrpRep) -> GrpRep
// Homomorphism(V::GrpRep, W::GrpRep, f::UserProgram) -> GrpRepHom
// Homomorphism(V::GrpRep, W::GrpRep, f::Map) -> GrpRepHom
// Homomorphism(V::GrpRep, W::GrpRep, basis_images::SeqEnum) -> GrpRepHom
// Homomorphism(V::GrpRep, W::GrpRep, f::CombFreeModHom) -> GrpRepHom
// Domain(phi::GrpRepHom) -> GrpRep
// Codomain(phi::GrpRepHom) -> GrpRep
// Print(phi::GrpRepHom, level::MonStgElt)
// Evaluate(phi::GrpRepHom, v::GrpRepElt) -> GrpRepElt
// '@@'(v::GrpRepElt, phi::GrpRepHom) -> GrpRepElt
// '@'(v::GrpRepElt, phi::GrpRepHom) -> GrpRepElt
// Kernel(phi::GrpRepHom) -> GrpRep
// FixedSubspace(gamma::GrpMat, V::GrpRep) -> GrpRep
// FixedSubspace(gamma::GrpMat, G::GrpLie, pbMap::Map, weight::SeqEnum) -> ModTupFld
// GroupRepresentation(G::GrpLie, hw::SeqEnum) -> GrpRep
// SpinorNormRho(d::RngIntElt, sigma::GrpMatElt, A::AlgMatElt)
// SpinorNormRepresentation(G::GrpRed, d::RngIntElt) -> GrpRep
// Rho(G::GrpMat, k::RngIntElt, j::RngIntElt) -> GrpRep
// SymSpinor(G::GrpRed, d::RngIntElt, k::RngIntElt) -> GrpRep
// AltSpinor(G::GrpRed, d::RngIntElt, j::RngIntElt) -> GrpRep
// HighestWeightRepresentation(G::GrpRed, lambda::SeqEnum) -> GrpRep
// CharacterQQModSquares(d::RngIntElt,r::FldRatElt) -> RngIntElt

import "../neighbors/neighbor-CN1.m" : BuildNeighborProc;
import "../utils/linalg.m" : Restrict;

import "combfreemod.m" : make_wedge_str,
                         get_spin_matrix_action;

forward projLocalization;
forward spinor_norm_rho;

// This should have been done using GModule
// But for some reason, it's really terrible, so we are doing our own
// This is currently built on top of combinatorial free modules
// to allow for nice (= meaningful) representations of the elements

declare type GrpRep[GrpRepElt];
declare attributes GrpRep :
	// the (actual) group - currently we usde a matrix group containing grp
	G,
        // the reductive group
        grp,
	// the module
	M,
	// the action on basis elements
	action,
	action_desc,
	// an associative array recording the action matrix of some elements
	// everytime we apply an element, it is updated.
	// In the future, might want to add an option to compute the operation on
	// a single element without computing the matrix.
	act_mats,
	// List of finite subgroups that can be generated by elements of finite
	// order for which we have computed the action.
	// In theory, would like just to save the group generated by all elements
	// for which we have computed the action matrix, but we (=magma) don't know
	// how to solve the word problem for matrix groups of infinite order.
	known_grps,
        // trivial representation
        trivial,
	// dual representation
	dual,
	// standard representation
	standard,
	// symmetric representation
	symmetric,
        // alternating representation
        alternating,
	// spin representation
	spin,
	// tensor product of the matrices.
	tensor_product,
	// This is assigned only if our representation is a pullback
	// in this case we can compute the action matrix by computing it
	// for the space we are pulling back from
	pullback,
	mat_to_elt,
	weight,
        lambda,
        is_irreducible,
	// In case this is a subrepresentation, its ambient representation
	ambient,
	// In case this is a subrepresentation, the embedding into its ambient.
        embedding,
        // In case this is a highest weight in a van-der-Warden representation,
        // some data to ease computations
        hw_vdw, hw_vdw_rev;

declare attributes GrpRepElt :
		   // the actual element in the module
		   m,
	// its parent
	parent;

/* constructors */

// this function will be used in both constructors
function _grp_rep(G, M, action_desc, params)
    V := New(GrpRep);
  V`G := G;
  V`M := M;

  param_array := AssociativeArray();

  // Store meta data.
  for entry in params do param_array[entry[1]] := entry[2]; end for;

  if IsDefined(param_array, "TENSOR_PRODUCT") then
      V`tensor_product := param_array["TENSOR_PRODUCT"];
  end if;

  if IsDefined(param_array, "PULLBACK") then
      V`pullback := param_array["PULLBACK"];
  end if;

  if IsDefined(param_array, "AMBIENT") then
      W := param_array["AMBIENT"];
      iota := param_array["EMBEDDING"];
      fromFile := IsDefined(param_array, "FROM_FILE"); 
      V`embedding := Homomorphism(V, W, iota : FromFile := fromFile);
      V`ambient := Codomain(V`embedding);
  end if;

  if IsDefined(param_array, "TRIVIAL") then
      V`trivial := param_array["TRIVIAL"];
  end if;

  if IsDefined(param_array, "DUAL") then
      V`dual := param_array["DUAL"];
  end if;

  if IsDefined(param_array, "STANDARD") then
      V`standard := param_array["STANDARD"];
      // In this case it is crucial that the module and the group
      // will have the same base ring
      V`M := CombinatorialFreeModule(BaseRing(G), M`names);
  end if;

  if IsDefined(param_array, "SYMMETRIC") then
      V`symmetric := param_array["SYMMETRIC"];
  end if;

  if IsDefined(param_array, "ALTERNATING") then
      V`alternating := param_array["ALTERNATING"];
  end if;

  if IsDefined(param_array, "SPIN") then
      V`spin := param_array["SPIN"];
  end if;

  if IsDefined(param_array, "HW_VDW") then
      V`hw_vdw := param_array["HW_VDW"][1];
      V`M := CombinatorialFreeModule(BaseRing(Universe(M`names)), M`names);
      V`hw_vdw_rev := AssociativeArray();
      for i in [1..#V`hw_vdw[1]] do
	V`hw_vdw_rev[V`hw_vdw[1][i]] := i;
      end for;
      V`lambda := param_array["HW_VDW"][2];
      V`is_irreducible := true;
  end if;

  if IsDefined(param_array, "WEIGHT") then
      grp := param_array["WEIGHT"][1];
      hw := param_array["WEIGHT"][2];
      lie_G := grp`G0;
      std_rep := StandardRepresentation(lie_G);
      GL_std := Codomain(std_rep);
      mats := [std_rep(x) : x in AlgebraicGenerators(lie_G)];
      word_map := InverseWordMap(V`G);
      G_map := hom<Codomain(word_map) -> lie_G | AlgebraicGenerators(lie_G)>;
      if not IsSemisimple(lie_G) then
	  RootDat := RootDatum(lie_G);
	  AdRootDat := RootDatum(CartanName(RootDat));
	  // This is the central weight
	  ones := Vector([Rationals() | 1 : i in [1..Dimension(RootDat)]]);
	  zero := Vector([Rationals()| 0 : i in [1..Dimension(AdRootDat)]]);
	  A := VerticalJoin(SimpleRoots(RootDat), ones)^(-1) *
	       VerticalJoin(SimpleRoots(AdRootDat), zero);
	  B := VerticalJoin(SimpleCoroots(RootDat), ones)^(-1) *
	       VerticalJoin(SimpleCoroots(AdRootDat), zero);
	  phi := hom<RootDat -> AdRootDat | A, B>;
	  red := GroupOfLieTypeHomomorphism(phi, BaseRing(lie_G));
	  G_map := G_map * red;
      end if;
      V`mat_to_elt := word_map * G_map;
      V`weight := HighestWeightRepresentation(Codomain(V`mat_to_elt),hw);
      V`lambda := hw;
      V`is_irreducible := true;
  end if;

  if IsDefined(param_array, "IS_IRREDUCIBLE") then
    V`is_irreducible := param_array["IS_IRREDUCIBLE"];
  end if;

  if IsDefined(param_array, "GRP") then
    V`grp := param_array["GRP"];
  end if;

  V`action_desc := action_desc;
  action := eval action_desc;
  V`action := map< CartesianProduct(V`G, [1..Dimension(V`M)]) -> V`M |
		 x :-> action(x[1], x[2], V)>;  
  V`act_mats := AssociativeArray();
  V`known_grps := [sub<V`G|1>];
  V`act_mats[G!1] := IdentityMatrix(BaseRing(V`M), Dimension(V`M));
  return V;
end function;

// action_desc is a string description of the action,
// needed for serializaition, since Map does not really support it
intrinsic GroupRepresentation(G::Grp, M::CombFreeMod,
			action_desc::MonStgElt : params := [* *] ) -> GrpRep
{Constructs a group representation for the group G on the combinatorial free module
M, such that the action on basis elements G x Basis(M) -> M is described by the map action .}
  return _grp_rep(G, M, action_desc, params);
end intrinsic;

intrinsic GroupRepresentation(G::GrpRed, M::CombFreeMod,
			action_desc::MonStgElt : params := [* *] ) -> GrpRep
{Constructs a group representation for the group G on the combinatorial free module
M, such that the action on basis elements G x Basis(M) -> M is described by the map action .}
  return _grp_rep(G, M, action_desc, params);
end intrinsic;

// At the moment, we assume that the generators are
// for the subrepresentation as a module
// (i.e. without computing the G-action)
// Also, (bug / feature?) we do not check that this is indeed a subrepresentation

// Remark - this should have been implemented using SubConstructor
// However, SubConstructor would always return a Map,
// and something goes completely wrong with maps between these objects.

intrinsic Subrepresentation(V::GrpRep, t::.) -> GrpRep, GrpRepHom
{Computes the subrepresentation of V whose underlying free module
 is generated by t.}
  if Type(t) eq SeqEnum then t := Flat(t); else t := [t]; end if;
  t := [V!x : x in t];
  N, i := SubCFModule(V`M, [v`m : v in t]);
  action_desc := Sprintf("           
  	      function action(g, m, V)
	      	       i := V`embedding;
      	      	       return (g * (V`ambient)!(i((V`M).m))`m)@@i;
  	      end function;
  	      return action;
	      ");
  U_params := [* <"AMBIENT", V>, <"EMBEDDING", i> *];
  U := GroupRepresentation(V`G, N, action_desc :
			   params := U_params);
  if IsTrivial(V) then
     U`trivial := true;
  else
     U`trivial := false;
  end if;
  return U, U`embedding;
end intrinsic;

/* constructors of some special cases of representations */

intrinsic TrivialRepresentation(G::Grp, R::Rng : name := "v") -> GrpRep
{Constructs the trivial representation for G over the ring R.}
  M := CombinatorialFreeModule(R, [name]);
  a := Sprintf("
  function action(g,m,V)
  	   return (V`M).m;
  end function; 
  return action;
  ");
  V := GroupRepresentation(G, M, a);
  V`trivial := true;
  V`weight := <1,0,0>;
  return V;
end intrinsic;

// We duplicate because something goes wrong when trying to inherit from Grp
intrinsic TrivialRepresentation(G::GrpRed, R::Rng : name := "v") -> GrpRep
{Constructs the trivial representation for G over the ring R.}
  M := CombinatorialFreeModule(R, [name]);
  a := Sprintf("
  function action(g,m,V)
  	   return (V`M).m;
  end function; 
  return action;
  ");
  V := GroupRepresentation(G, M, a);
  V`trivial := true;
  return V;
end intrinsic;

// this function will be used for both the following intrinsics
function standard_rep(G, name)
  n := Degree(G);
  names := [name cat IntegerToString(i) : i in [1..n]];
  M := CombinatorialFreeModule(BaseRing(G), names);
/*  a := map< CartesianProduct(G, [1..Dimension(M)]) -> M |
	  x :-> M!((M.(x[2]))`vec * Transpose(x[1]))>;*/
  a := Sprintf("
  function action(g,m,V)
	return (V`M)!(((V`M).m)`vec * Transpose(g));
  end function;
  return action;
  ");
  return GroupRepresentation(G, M, a : params := [* <"STANDARD", true> *]);
end function;

// Should change that to also support arbitrary reductive group
intrinsic StandardRepresentation(G::GrpMat : name := "x") -> GrpRep
{Constructs the standard representation of the matrix group G its ring of definition R, i.e. the representation obtained by considering its given embedding in GL_n acting on R^n by invertible linear transformations.}
  return standard_rep(G, name);
end intrinsic;

intrinsic StandardRepresentation(G::GrpRed : name := "x") -> GrpRep
{Constructs the standard representation of the matrix group G its ring of definition R, i.e. the representation obtained by considering its given embedding in GL_n acting on R^n by invertible linear transformations.}
  return standard_rep(G, name);
end intrinsic;

intrinsic DeterminantRepresentation(G::GrpMat : k := 1, name := "v") -> GrpRep
{Constructs the 1-dimensional representation, where G acts via det.}
  M := CombinatorialFreeModule(BaseRing(G), [name]);
  a := Sprintf("
    function action(g,m,V)
       return (V`M)!((Determinant(g)^(%o))*((V`M).m)`vec);
    end function;
    return action;
  ", k);
  V := GroupRepresentation(G, M, a);
  if k eq 0 then
    V`trivial := true;
  else
    V`trivial := false;
  end if;
  return V;
end intrinsic;

intrinsic SymmetricRepresentation(V::GrpRep, n::RngIntElt) -> GrpRep
{Constructs the representation Sym^n(V).}
    R := BaseRing(V);	  
    R_X := PolynomialRing(R, Rank(V));
    AssignNames(~R_X, [x : x in V`M`names]);
    S := MonomialsOfDegree(R_X, n);
    M := CombinatorialFreeModule(R, S);
    a := Sprintf("
  function action(g,m,V)
      R := Universe(V`M`names);
      gens := RModule(R, Ngens(R))![R.i : i in [1..Ngens(R)]];
      coeffs := [RModule(R, Rank(V`symmetric)) | Eltseq((V`symmetric`G!g) * (V`symmetric).i) : i in [1..Dimension(V`symmetric)]];
      ys := Vector(gens) * Transpose(Matrix(coeffs));
      ans := Evaluate(V`M`names[m], Eltseq(ys));
      ans_coeffs, mons := CoefficientsAndMonomials(ans);
      idxs := [Index(mons, name) : name in V`M`names];
      return &+[ans_coeffs[idxs[i]] * (V`M).i : i in [1..#idxs] | idxs[i] ne 0];
  end function;
  return action;
  ");
  Sym := GroupRepresentation(V`G, M, a : params := [* <"SYMMETRIC", V> *]);
  if IsTrivial(V) or n eq 0 then
    Sym`trivial := true;
  else
    Sym`trivial := false;
  end if;
  return Sym;
end intrinsic;

// Should display those better...
intrinsic AlternatingRepresentation(V::GrpRep, n::RngIntElt) -> GrpRep
{Constructs the representation Alt^n(V).}
  R := BaseRing(V);
  indices := Sort([SetToSequence(s) : s in Subsets(Set([1..Dimension(V)]),n)]);
  keys := {@ make_wedge_str(V`M`names, s) : s in indices @};
  M := CombinatorialFreeModule(R, keys);
  a := Sprintf("
  function action(g,m,V)
       base_names := Split(V`M`names[m], \"^\");
       idxs := [Index(V`alternating`M`names, name) : name in base_names];
       vs := [V`alternating.i : i in idxs];
       mat := Matrix([Eltseq((V`alternating`G!g)*v) : v in vs]);
       return M!Reverse(Minors(mat,%o)); 
       end function;
  return action;
  ", n);
  Alt := GroupRepresentation(V`G, M, a : params := [* <"ALTERNATING", V> *]);
  if IsTrivial(V) or (n eq 0) then
    Alt`trivial := true;
  else
    Alt`trivial := false;
  end if;
  return Alt;
end intrinsic;

intrinsic DualRepresentation(V::GrpRep) -> GrpRep
{Constructs the dual representation of V.}
  R := BaseRing(V);
  names := [Sprintf("%o^*",b) : b in Basis(V)]; 
  M := CombinatorialFreeModule(R, names);
  a := Sprintf("
  function action(g,m,V)
      v := (V`dual)!Eltseq((V`M).m);
      return (V`M)!(Eltseq(Transpose((V`dual`G)!g)^(-1) * v));
  end function;
  return action;
  ");
  V_d := GroupRepresentation(V`G, M, a : params := [* <"DUAL", V> *]);
  if IsTrivial(V) then
    V_d`trivial := true;
  else
    V_d`trivial := false;
  end if;
  return V_d;
end intrinsic;

intrinsic TensorProduct(V::GrpRep, W::GrpRep) -> GrpRep
{Constructs the tensor product of the representations V and W, with diagonal action.}
  R := BaseRing(V);
  names := [Sprintf("<%o, %o>", v, w) : v in V`M`names, w in W`M`names];
  M := CombinatorialFreeModule(R, names);
  a := Sprintf("
  function action(g,m,V)
      ops := [(V`tensor_product[i]).(V`M`names[m][i]) : i in [1..2]];
      gs := [(V`tensor_product[i]`G)!g : i in [1..2]];
      vecs := [Vector(Eltseq(gs[i]*ops[i])) : i in [1..2]];
      return (V`M)!(TensorProduct(vecs[1], vecs[2]));
  end function;
  return action;  
  ");
  ret := GroupRepresentation(V`G, M, a :
			     params := [* <"TENSOR_PRODUCT", [V,W]> *]);
//  ret`tensor_product := [V,W];
  if assigned V`weight and assigned W`weight then
    ret`weight := <V`weight[1] * W`weight[1], V`weight[2] + W`weight[2],
                  V`weight[3] + W`weight[3]>;
  end if;
  // There are more cases where the tensor product might be trivial,
  // but we can't know for sure.
  if IsTrivial(V) and IsTrivial(W) then
    ret`trivial := true;
  else
    ret`trivial := false;
  end if;
  return ret;
end intrinsic;

intrinsic TensorPower(V::GrpRep, d::RngIntElt) -> GrpRep
{Construcs the tensor power representation V tensor itself d times.}
  if (d lt 0) then
    return TensorPower(DualRepresentation(V), -d);
  end if;
  if (d eq 0) then
    return TrivialRepresentation(Group(V), BaseRing(V));
  end if;
  V_d := V;
  for i in [1..d-1] do
     V_d := TensorProduct(V_d, V);
  end for;
  return V_d;
end intrinsic;

intrinsic Pullback(V::GrpRep, /* f::Map[Grp, Grp] */
		      f_desc::MonStgElt, H::Grp) -> GrpRep
{Constructs the pullback of the representation V along the
group homomorphism f. Does not verify that f is a group homomorphism}
  M := V`M;
  f := (eval f_desc)(H);
  G := Domain(f);
  action := Sprintf("
  f := eval %m;
  V_action := eval %m;
  function action(g,m,V)
    return V_action(f(g), m);
  end function;
  return action;
  ", f_desc, V`action_desc);
  ret := GroupRepresentation(G, M, action :
			     params := [* <"PULLBACK", <V, f_desc, H> > *]);
  if IsTrivial(V) then
    ret`trivial := true;
  else
    ret`trivial := false;
  end if;
  return ret;
end intrinsic;

// since magma doesn't support localization in arbitrary number fields
// we make a small patch for that
function projLocalization(g, proj)
    // denom := Parent(g)!ScalarMatrix(Degree(g),Denominator(g));
    n := Nrows(g);
    denom := LCM([Denominator(x) : x in Eltseq(g)]);
    denom := GL(n, BaseRing(g))!ScalarMatrix(n,denom);
    // numerator := GL(n, Domain(proj)) !(denom*g);
    numerator := MatrixAlgebra(Domain(proj),n)!(denom*g);
    f := hom< MatrixAlgebra(Domain(proj),n) ->
			  MatrixAlgebra(Codomain(proj),n) | proj >;
    // f_gl := hom< GL(n, Domain(proj)) ->
//		   GL(n, Codomain(proj)) | x :-> f(Matrix(x)) >;
    //    return f_gl(numerator) * f_gl(denom)^(-1);
    return GL(n,Codomain(proj))!(f(numerator)*f(denom)^(-1));
end function;
// Then one can pullback via something like
// f := map< GL(3,K) -> GL(3,F7) | x :-> projLocalization(x, mod_root_7)>;
// even though f is not defined on all GL(3,K), but only on a localization

/* access and properties */

intrinsic Rank(V::GrpRep) -> RngIntElt
{The rank of the free module underlying the representation V.}
// return #Basis(V);
   return Rank(V`M);
end intrinsic;

intrinsic Dimension(V::GrpRep) -> RngIntElt
{The rank of the free module underlying the representation V.}
//   return Rank(V);
  return Dimension(V`M);
end intrinsic;

intrinsic Ngens(V::GrpRep) -> RngIntElt
{The rank of the free module underlying the representation V.}
  return Rank(V);
end intrinsic;

intrinsic Basis(V::GrpRep) -> SeqEnum[GrpRepElt]
{Returns a basis for the free module underlying the representation V.}
  return [V!v : v in Basis(V`M)];
end intrinsic;

intrinsic BaseRing(V::GrpRep) -> Rng
{Returns the ring over which V is defined.}
  return BaseRing(V`M);
end intrinsic;

intrinsic Group(V::GrpRep) -> Grp
{Return the group that acts on V.}
  return V`G;
end intrinsic;

intrinsic CFM(V::GrpRep) -> CombFreeMod
{Return the combinatorial free module underlying V.}
  return V`M;
end intrinsic;

function build_rep_params(V, R)
    params := [* *];
    if assigned V`tensor_product then
	Append(~params, < "TENSOR_PRODUCT",
	       [ChangeRing(U, R) : U in V`tensor_product] >);
    end if;
    if assigned V`trivial then
	Append(~params, < "TRIVIAL", V`trivial >);
    end if;
    if assigned V`dual then
        Append(~params, < "DUAL", ChangeRing(V`dual, R) >);
    end if;
    if assigned V`standard then
        Append(~params, < "STANDARD", ChangeRing(V`standard, R) >);
    end if;
    if assigned V`symmetric then
        Append(~params, < "SYMMETRIC", ChangeRing(V`symmetric, R) >);
    end if;
    if assigned V`alternating then
        Append(~params, < "ALTERNATING", ChangeRing(V`alternating, R) >);
    end if;
    if assigned V`pullback then
        pb := <ChangeRing(V`pullback[1], R), V`pullback[2], V`pullback[3]>;
        Append(~params, < "PULLBACK", pb >);
    end if;
    if assigned V`hw_vdw then
        Append(~params, < "HW_VDW", <V`hw_vdw, V`lambda> >);
    end if;
    if assigned V`mat_to_elt then
	lie_grp := Codomain(Components(V`mat_to_elt)[2]);
	Append(~params, < "WEIGHT",
			  <ReductiveGroup(lie_grp,
					  CyclicGroup(1)),
			   HighestWeights(V`weight)[1] > >);
    end if;
    if assigned V`ambient then
        amb := ChangeRing(V`ambient, R);
        images := [amb`M |
		   ChangeRing(V`embedding(V.i)`m, R) : i in [1..Dimension(V)]];
        iota := Homomorphism(ChangeRing(V`M, R),
			     amb`M, images);
        Append(~params, < "AMBIENT", amb >);
        Append(~params, < "EMBEDDING", iota >);
    end if;
    if assigned V`is_irreducible then
        Append(~params, < "IS_IRREDUCIBLE", V`is_irreducible >);
    end if;
    if assigned V`grp then
        Append(~params, < "GRP", V`grp >);
    end if;
    return params;
end function;

intrinsic ChangeRing(V::GrpRep, R::Rng) -> GrpRep
{return the Group Representation with base ring changed to R.}
  // If this is an algebraic representation of a reductive group
  // then we want to change rings also for the group
  // !! TODO - have a better way to mark that a representation is algebraic
  // and have base change use that
  if Type(V`G) eq GrpRed then
    G := ChangeRing(V`G, R);
  // If we use GL(n,R) then magma doesn't know to base change
  elif (Type(V`G) eq GrpMat) and (Type(BaseRing(V`G)) eq Type(BaseRing(V)))
       and BaseRing(V`G) eq BaseRing(V)then
    G := GL(Degree(V`G), R);
  else
    G := V`G;
  end if;
  return GroupRepresentation(G, ChangeRing(V`M,R), V`action_desc
			     : params := build_rep_params(V, R));
end intrinsic;

/* booleans */
intrinsic IsTrivial(V::GrpRep) -> BoolElt
{Returns whether V is the trivial representation.}
  if not assigned V`trivial then
    V`trivial := false;
  end if;
  return V`trivial;
end intrinsic;

/* printing */

intrinsic Print(V::GrpRep, level::MonStgElt)
{.}
  if level eq "Magma" then
      params := build_rep_params(V, BaseRing(V));
      Append(~params, < "FROM_FILE", true>);
      printf "GroupRepresentation(%m, %m, %m : params := %m)",
	     V`G, V`M, V`action_desc, params;
      return;
  end if;
  G := (assigned V`grp) select V`grp else V`G;
  printf "%o with an action of %o", V`M, G; 
end intrinsic;		   

/* generators and coercion */ 

intrinsic '.'(V::GrpRep, i::RngIntElt) -> GrpRepElt
{.}
  return GroupRepresentationElement(V, V`M.i);	     
end intrinsic;

intrinsic IsCoercible(V::GrpRep, x::Any) -> BoolElt, .
{.}
  if Type(x) eq GrpRepElt then
    if Parent(x) eq V then
      return true, x;
    else
      is_coercible, v := IsCoercible(V`M, x`m);
    end if;
  else
    is_coercible, v := IsCoercible(V`M, x);
  end if;  
  if is_coercible then
      return true, GroupRepresentationElement(V, v);
  else
      return false, "Illegal Coercion";
  end if;
end intrinsic;

intrinsic 'in'(elt::GrpRepElt, V::GrpRep) -> BoolElt
{.}
  return Parent(elt) eq V;
end intrinsic;

/***************************************************

GrpRepElt - an element of a group representation

****************************************************/

/* constructor */
intrinsic GroupRepresentationElement(V::GrpRep, m::CombFreeModElt) -> GrpRepElt
{Construct an element of the group representation whose underlying vector is m.}
  elt := New(GrpRepElt);
  elt`m := m;
  elt`parent := V;
  
  return elt;
end intrinsic;

/* access */

intrinsic Parent(elt::GrpRepElt) -> GrpRep
{.}
  return elt`parent;	  
end intrinsic;

intrinsic Eltseq(elt::GrpRepElt) -> SeqEnum
{.}
  return Eltseq(elt`m);
end intrinsic;

/* printing */

intrinsic Print(elt::GrpRepElt, level::MonStgElt)
{.}
  if level eq "Magma" then
      printf "%m ! %m", Parent(elt), Eltseq(elt);
      return;
  end if;
  printf "%o", elt`m;
end intrinsic;

/*
 Computing the group action 
*/

// verifyKnownGroups is a procedure for cases of incoherent execution,
// e.g. execution was interrupted. It makes sure that the known groups
// are updated correctly.

procedure verifyKnownGroups(V)
    idxs := [[i : i in [1..Ngens(grp)] | /* grp.i in Keys(V`act_mats) */
	       IsDefined(V`act_mats, grp.i) ] :
	      grp in V`known_grps];
    V`known_grps := [sub<V`G | [V`known_grps[j].i : i in idxs[j]]> : j in [1..#idxs]];
end procedure;

// getActionHom returns the homomorphism from the finite group grp to the
// automorphisms of the representation. 
function getActionHom(V, grp)
    GL_V := GL(Dimension(V), BaseRing(V));
    // verifyKnownGroups(V); // this is in case there was some interrupt
    return hom< grp -> GL_V |
		  [Transpose(V`act_mats[grp.i]) : i in [1..Ngens(grp)]]>;
end function;

// At the moment, every time we compute the complete image of g in GL_V
// and store it for future use.
// When dimensions will be high, we would probably no longer wish to do that.

intrinsic getMatrixAction(V::GrpRep, g::GrpElt) -> GrpMatElt
{Computes the martix describing the action of g on V.}
  // In the cases of pullbacks and weight representations
  // we don't record anything, just compute from the underlying structure
  if (Type(g) ne GrpPermElt) and (Type(BaseRing(g)) ne FldFin) then
      assert IsIsomorphic(BaseRing(V`G),BaseRing(g));
  end if;
  if assigned V`pullback then
      W := V`pullback[1];
      f := (eval V`pullback[2])(V`pullback[3]);
      if Type(BaseRing(g)) ne FldFin then
	  assert IsIsomorphic(BaseRing(Domain(f)), BaseRing(g));
      end if;
      return getMatrixAction(W, f(g));
  end if;
  if assigned V`mat_to_elt then
      if GetVerbose("AlgebraicModularForms") ge 3 then
	  printf "Getting matrix action for element\n%o\n ", g;
	  printf " in representation over %o.\n", BaseRing(V`G);
	  printf "calculating element in algebraic group...";
      end if;
      elt := V`mat_to_elt(g);
      if GetVerbose("AlgebraicModularForms") ge 3 then
	  printf "calculating matrix in weight for %o.\n", elt;
      end if;
      mat := Transpose(V`weight(elt));
      if GetVerbose("AlgebraicModularForms") ge 3 then
	  printf "Done!\n";
      end if;
      // This is in the case we projected into PGL
      return ChangeRing(mat, BaseRing(V`G));
  end if;
  // verifyKnownGroups(V); // this is in case there was some interrupt

  if (Type(g) eq GrpPermElt) or HasFiniteOrder(g) then
      is_known := exists(grp){grp : grp in V`known_grps | g in grp};
  else
    // is_known := g in Keys(V`act_mats);
      is_known := IsDefined(V`act_mats, g);
  end if;

  if not is_known then
      if (Type(g) eq GrpPermElt) or HasFiniteOrder(g) then
	  grp_idx := 0;
	  for j in [1..#V`known_grps] do 
	      new_grp := sub<V`G | V`known_grps[j], g>;
	      if IsFinite(new_grp) then
		  V`known_grps[j] := new_grp;
		  grp_idx := j;
		  break;
	      end if;
	  end for;
	  if grp_idx eq 0 then
	      Append(~V`known_grps, sub<V`G | g>);
	      grp_idx := #V`known_grps;
	  end if;
	  grp := V`known_grps[grp_idx];
      end if;
      if assigned V`tensor_product then
	  V1, V2 := Explode(V`tensor_product);
	  V`act_mats[g] := TensorProduct(
		ChangeRing(getMatrixAction(V1, (V1`G)!g), BaseRing(V)),
		ChangeRing(getMatrixAction(V2, (V2`G)!g), BaseRing(V)));
      else if assigned V`ambient then
	       phi := Matrix(V`embedding`morphism);
	       phi_T := Transpose(phi);
	       mat_g := getMatrixAction(V`ambient, (V`ambient`G)!g);
	       V`act_mats[g] := phi * mat_g * phi_T * (phi * phi_T)^(-1); 
	   else
	       V`act_mats[g] := Matrix([V`action(g, i)`vec : i in [1..Dimension(V)]]);
	   end if;
      end if;
  end if;

  if (Type(g) eq GrpPermElt) or HasFiniteOrder(g) then
      act_hom := getActionHom(V, grp);
      return Transpose(act_hom(g));
  else
      return V`act_mats[g];
  end if;
  
end intrinsic;
/*
// in case we have a non-invertible element and the action is defined for it.

intrinsic getMatrixAction(V::GrpRep, m::AlgMatElt) -> AlgMatElt
{.}
   return Matrix([V`action(m, i)`vec : i in [1..Dimension(V)]]);
end intrinsic;
*/
/* arithmetic operations */

intrinsic '*'(g::GrpElt, v::GrpRepElt) -> GrpRepElt
{.}

  V := Parent(v);
  require g in V`G : "element must be in the group acting on the space";
  
  g_act := getMatrixAction(V,g);
  
  return V!(v`m`vec * g_act);
end intrinsic;

// Direct matrix multiplication
intrinsic '*'(m::AlgMatElt, v::GrpRepElt) -> GrpRepElt
{.}

  V := Parent(v);
  
  return V!(v`m`vec * m);
end intrinsic;

intrinsic '+'(elt_l::GrpRepElt, elt_r::GrpRepElt) -> GrpRepElt
{.}
  require Parent(elt_l) eq Parent(elt_r) : "elements must belong to the same 
  	  		   		   	     representation";
  V := Parent(elt_l);
  return GroupRepresentationElement(V, elt_l`m + elt_r`m);
end intrinsic;

intrinsic '-'(elt_l::GrpRepElt, elt_r::GrpRepElt) -> GrpRepElt
{.}
  require Parent(elt_l) eq Parent(elt_r) : "elements must belong to the same 
  	  		   		   	     representation";
  V := Parent(elt_l);
  return GroupRepresentationElement(V, elt_l`m - elt_r`m);
end intrinsic;

intrinsic '*'(scalar::RngElt, elt::GrpRepElt) -> GrpRepElt
{.}	     
  V := Parent(elt);
  require scalar in BaseRing(V) : "scalar is not in the base ring";
  return GroupRepresentationElement(V, scalar * elt`m);
end intrinsic;

/* booleans, equality and hashing */

intrinsic 'eq'(V1::GrpRep, V2::GrpRep) -> BoolElt
{.}
  // In theory, we could have equivalent action descriptions
  // but we cannot really check this
  R1 := BaseRing(V1`M);
  R2 := BaseRing(V2`M);
  if IsFinite(R1) then
      isom := (R1 eq R2);
  else
      isom := IsIsomorphic(R1, R2);
  end if;
  if (not isom) or (ChangeRing(V1`M, R2) ne V2`M) then
      return false;
  end if;
  // should find something better here.
  // for some reason can't change ring for these groups
  if Sprintf("%o",V1`G) ne Sprintf("%o", V2`G) then return false; end if;
  return Split(V1`action_desc, " \t\n") eq Split(V2`action_desc, " \t\n");
end intrinsic;

intrinsic Hash(V::GrpRep) -> RngIntElt
{.}
  // far from optimal, since magma doesn't know how to hash functions or groups
  // Should fix it in time (create a class wrapping functions having hash
  return Hash(<V`M, V`action>);
end intrinsic;

intrinsic 'eq'(v1::GrpRepElt, v2::GrpRepElt) -> BoolElt
{.}
  V := Parent(v1);
  if V ne Parent(v2) then return false; end if;
  return Eltseq(v1) eq Eltseq(v2);
end intrinsic;

intrinsic Hash(v::GrpRepElt) -> RngIntElt
{.}
  return Hash(<v`m, v`parent>);
end intrinsic;

intrinsic 'in'(v::., V::GrpRep) -> BoolElt
{Returns whether v is in V}
  return Parent(v) eq V;
end intrinsic;

intrinsic Intersection(V::GrpRep, W::GrpRep) -> GrpRep
{Compute the intersection of the representation V, W.}
  require (assigned V`embedding) and (assigned W`embedding) and
           (Codomain(V`embedding) eq Codomain(W`embedding)) :
  "Both representation should be subrepresentations of the same one.";
  U := Codomain(V`embedding);
  basis_imV := [Eltseq(V`embedding(V.i)) : i in [1..Dimension(V)]];
  basis_imW := [Eltseq(W`embedding(W.i)) : i in [1..Dimension(W)]];
  imV := sub< U`M`M | basis_imV >;
  imW := sub< U`M`M | basis_imW >;
  return Subrepresentation(U, Basis(imV meet imW));
end intrinsic;

intrinsic 'meet'(V::GrpRep, W::GrpRep) -> GrpRep
{Compute the intersection of the representation V, W.}
  return Intersection(V, W);
end intrinsic;

/***************************************************

GrpRepHom - Homomorphism of group representations

****************************************************/
// for some reason, just havin map<V->W|f> doesn't work. no idea why

declare type GrpRepHom;
declare attributes GrpRepHom :
		   domain,
	codomain,
	morphism;

/* constructors */

intrinsic Homomorphism(V::GrpRep, W::GrpRep, f::UserProgram) -> GrpRepHom
{Construct a homomorphism of group representation described by f. Note: the constructor does not verify that the map indeed describes a homomorphism of group representations.}
  require BaseRing(V) eq BaseRing(W) : "Represenations should have the same coefficient ring";
  phi := New(GrpRepHom);
  phi`domain := V;
  phi`codomain := W;
  phi`morphism := hom<V`M`M -> W`M`M | [f(V.i)`m`vec : i in [1..Dimension(V)]]>;

  return phi;
end intrinsic;

intrinsic Homomorphism(V::GrpRep, W::GrpRep, f::Map) -> GrpRepHom
{Construct a homomorphism of group representations described by f. Note: the constructor does not verify that the map indeed describes a homomorphism of group representations.}
  require BaseRing(V) eq BaseRing(W) : "Represenations should have the same coefficient ring";
  phi := New(GrpRepHom);
  phi`domain := V;
  phi`codomain := W;

  require (Domain(f) eq V`M) and (Codomain(f) eq W`M) :
	"Map should be defined on the combinatorial modules of the representations"; 
  phi`morphism := hom<V`M`M -> W`M`M | [f((V.i)`m)`vec : i in [1..Dimension(V)]]>;

  return phi;
end intrinsic;

intrinsic Homomorphism(V::GrpRep, W::GrpRep,
				     basis_images::SeqEnum :
		       FromFile := false) -> GrpRepHom
{Construct a homomorphism of group representations such that the images of the basis elements of V map to basis_images. Note: the constructor does not verify that the map indeed describes a homomorphism of group representations.}
  phi := New(GrpRepHom);
  phi`domain := V;
  if FromFile then
      W := ChangeRing(W, BaseRing(V));
  else
      require BaseRing(V) eq BaseRing(W) : "Represenations should have the same coefficient ring";
  end if;
  phi`codomain := W;

  require IsEmpty(basis_images) or IsCoercible(W,basis_images[1]) :
	"images should be in the codomain representation"; 
  phi`morphism := hom<V`M`M -> W`M`M | [Eltseq(W!v) : v in basis_images]>;

  return phi;
end intrinsic;

intrinsic Homomorphism(V::GrpRep, W::GrpRep,
				     f::CombFreeModHom
		      : FromFile := false) -> GrpRepHom
{Construct a homomorphism of group representations described by f. Note: the constructor does not verify that the map indeed describes a homomorphism of group representations.}
  phi := New(GrpRepHom);
  phi`domain := V;
  if FromFile then
      W := ChangeRing(W, BaseRing(V));
      images := [f(Domain(f).i)`vec : i in [1..Dimension(V)]];
      f := Homomorphism(V`M, W`M,
		[Vector(ChangeRing(x,BaseRing(W`M))) : x in images]);
  else
      require BaseRing(V) eq BaseRing(W) : "Represenations should have the same coefficient ring";
      require (Domain(f) eq V`M) and (Codomain(f) eq W`M) :
	"Map should be defined on the combinatorial modules of the representations"; 
  end if;
  phi`codomain := W;
  
  phi`morphism := hom<V`M`M -> W`M`M | [Eltseq(f((V.i)`m)) : i in [1..Dimension(V)]]>;
 
  return phi;
end intrinsic;

/* access */

intrinsic Domain(phi::GrpRepHom) -> GrpRep
{.}
  return phi`domain;
end intrinsic;

intrinsic Codomain(phi::GrpRepHom) -> GrpRep
{.}
  return phi`codomain;
end intrinsic;

/* printing */

intrinsic Print(phi::GrpRepHom, level::MonStgElt)
{.}
  if level eq "Magma" then
      images := [Eltseq(phi(Domain(phi).i)) :
		 i in [1..Dimension(Domain(phi))]];
      printf "Homomorphism(%m, %m, %m : FromFile := true)",
	     Domain(phi), Codomain(phi), images;
      return;
  end if;
  printf "Homomorphism from %o to %o", Domain(phi), Codomain(phi);
end intrinsic;

/* Evaluation, image and pre-image */

intrinsic Evaluate(phi::GrpRepHom, v::GrpRepElt) -> GrpRepElt
{Return phi(v).}
  V := Domain(phi);
  W := Codomain(phi);
  require v in V : "Element should be in domain of the morphism";

  return W!(phi`morphism(V`M`M!Eltseq(v)));
end intrinsic;

intrinsic '@@'(v::GrpRepElt, phi::GrpRepHom) -> GrpRepElt
{Return a preimage of v under phi.}
  V := Domain(phi);
  W := Codomain(phi);
  require v in W : "Element should be in codomain of the morphism";

  return V!((W`M`M!Eltseq(v))@@(phi`morphism));
end intrinsic;

intrinsic '@'(v::GrpRepElt, phi::GrpRepHom) -> GrpRepElt
{Return phi(v).}
  return Evaluate(phi, v);	     
end intrinsic;

intrinsic Kernel(phi::GrpRepHom) -> GrpRep
{Returns the kernel of a homomorphism of group representations.}
  V := Domain(phi);
  B := Basis(Kernel(phi`morphism));
  return Subrepresentation(V,B);
end intrinsic;

intrinsic FixedSubspace(gamma::GrpMat, V::GrpRep) -> GrpRep
{Return the fixed subspace of V under the group gamma.}
  gamma_gens := Generators(gamma);
  if GetVerbose("AlgebraicModularForms") ge 2 then
      printf "Calculating the fixed subspace for the group gamma";
      printf " with %o generators.\n", #gamma_gens;
  end if;
  if IsEmpty(gamma_gens) then gamma_gens := [gamma!1]; end if;
  gamma_actions := [getMatrixAction(V, g) : g in gamma_gens];
  if GetVerbose("AlgebraicModularForms") ge 2 then
      printf "Calculating kernel...\n";
  end if;
  X := HorizontalJoin([Matrix(g) - 1 : g in gamma_actions]);
  return Subrepresentation(V, Basis(Nullspace(X)));
end intrinsic;

// Here trying some things with magma built-in types
// See if it improves efficiency
// We assume g is an element in the standard representation of G
// G is the Lie group

function getActionMatrix(G, g, weight)
    std_rep := StandardRepresentation(G);
    GL_std := Codomain(std_rep);
    mats := [std_rep(x) : x in AlgebraicGenerators(G)];
    mat_grp := sub< GL_std | mats>;
    w := InverseWordMap(mat_grp)(g);
    f := hom<Parent(w) -> G | AlgebraicGenerators(G)>;
    // This does not work with GL_n, i.e.
    // GroupOfLieType(StandardRootDatum("A",2), F);
    // getting error - the integral UEA only exists for
    // semisimple Lie algebras
    // Right now this part is tailored specifically for GL_n
    if not IsSemisimple(G) then
	RootDat := RootDatum(G);
	AdRootDat := RootDatum(CartanName(RootDat));
	// This is the central weight
	ones := Vector([Rationals() | 1 : i in [1..Dimension(RootDat)]]);
	zero := Vector([Rationals()| 0 : i in [1..Dimension(AdRootDat)]]);
	A := VerticalJoin(SimpleRoots(RootDat), ones)^(-1) *
	     VerticalJoin(SimpleRoots(AdRootDat), zero);
	B := VerticalJoin(SimpleCoroots(RootDat), ones)^(-1) *
	     VerticalJoin(SimpleCoroots(AdRootDat), zero);
	phi := hom<RootDat -> AdRootDat | A, B>;
	red := GroupOfLieTypeHomomorphism(phi, BaseRing(G));
	f := f * red;
	G := GroupOfLieType(AdRootDat, BaseRing(G));
    end if;
    return HighestWeightRepresentation(G,weight)(f(w));
end function;

intrinsic FixedSubspace(gamma::GrpMat, G::GrpLie, pbMap::Map,
			weight::SeqEnum[RngIntElt]) -> ModTupFld
{Return the fixed subspace of the highest weight representation given by weight under the group gamma.}
  gamma_gens := Generators(gamma);
  gamma_actions := [getActionMatrix(G, pbMap(g), weight) : g in gamma_gens];
  X := HorizontalJoin([Matrix(g) - 1 : g in gamma_actions]);
  return Nullspace(X);
end intrinsic;

intrinsic GroupRepresentation(G::GrpLie, hw::SeqEnum[RngIntElt]) -> GrpRep
{Construct the representation of the group G with highest weight hw}
  V := New(GrpRep);
  std_rep := StandardRepresentation(G);
  GL_std := Codomain(std_rep);
  mats := [std_rep(x) : x in AlgebraicGenerators(G)];
  mat_grp := sub< GL_std | mats>;
  V`G := mat_grp;
  // This wouldn't work in characteristic 0
  word_map := InverseWordMap(mat_grp);
  G_map := hom<Codomain(word_map) -> G | AlgebraicGenerators(G)>;
  if not IsSemisimple(G) then
      RootDat := RootDatum(G);
      AdRootDat := RootDatum(CartanName(RootDat));
      // This is the central weight
      ones := Vector([Rationals() | 1 : i in [1..Dimension(RootDat)]]);
      zero := Vector([Rationals()| 0 : i in [1..Dimension(AdRootDat)]]);
      A := VerticalJoin(SimpleRoots(RootDat), ones)^(-1) *
	   VerticalJoin(SimpleRoots(AdRootDat), zero);
      B := VerticalJoin(SimpleCoroots(RootDat), ones)^(-1) *
	   VerticalJoin(SimpleCoroots(AdRootDat), zero);
      phi := hom<RootDat -> AdRootDat | A, B>;
      red := GroupOfLieTypeHomomorphism(phi, BaseRing(G));
      G_map := G_map * red;
  end if;
  V`mat_to_elt := word_map * G_map;
  V`weight := HighestWeightRepresentation(Codomain(V`mat_to_elt),hw);
  
  // d := DimensionOfHighestWeightModule(RootDatum(G), hw);
  d := Degree(Codomain(V`weight));
  names := ["v" cat IntegerToString(n) : n in [1..d]];
  V`M := CombinatorialFreeModule(BaseRing(G), names);
  V`act_mats := AssociativeArray();
  V`known_grps := [sub<mat_grp|1>];
  V`act_mats[mat_grp!1] := IdentityMatrix(BaseRing(V`M), Dimension(V`M));
  V`action_desc := Sprintf("
  function action(g, m, V)
    mat := getMatrixAction(V, g);
    return (V`M)!(Rows(Transpose(mat))[m]);
  end function;
  return action;
  ");
  action := eval V`action_desc;
  V`action := map< CartesianProduct(V`G, [1..Dimension(V`M)]) -> V`M |
		 x :-> action(x[1], x[2], V)>;
  if &and[x eq 0 : x in hw] then
    V`trivial := true;
  else
    V`trivial := false;
  end if;
  return V;
end intrinsic;	  

function build_reflection(y, A)
    dim := Nrows(A);
    R := BaseRing(A);
    A_y := Matrix(y*A);
    return IdentityMatrix(R,dim)-(2/(y*A,y))*Transpose(A_y)*Matrix(y);
end function;

function get_aniso_vec(subspace, A)
    B := Basis(subspace);
    BM := BasisMatrix(subspace);
    A_res := BM*A*Transpose(BM);
    if A_res eq 0 then
	return false, _;
    end if;
    diag := Diagonal(A_res);
    dim := Dimension(subspace);
    aniso := exists(i){i : i in [1..dim] | diag[i] ne 0};
    if aniso then
	x := B[i];
    else
	// This should be true because A_res is nonzero
	// Why is it up to 2 here? Shouldn't that be up to dimension?
	assert exists(ij){[i,j] : i,j in [1..2] |
			  A_res[i,j] ne 0 and i lt j};
	i := ij[1]; j := ij[2];
	// Now this is anisotropic
	x := B[i] + B[j];
    end if;
    return true, x;
end function;

// reflections with respect to A - Cartan-Dieudonne
function find_reflection_pts(sigma, A)
    // assert Transpose(sigma)*A*sigma eq A;
    assert sigma*A*Transpose(sigma) eq A;
    if sigma eq IdentityMatrix(BaseRing(A), Nrows(A)) then
	return [];
    end if;
    if (Nrows(A) eq 1) and (sigma[1,1] eq -1) then
	return [Vector([1])];
    end if;
    fixed := Eigenspace(sigma,1);
    aniso_fixed, x := get_aniso_vec(fixed, A);
    if aniso_fixed then
	// case 1
	H := Kernel(Transpose(Matrix(x*A)));
	sigma_H := Restrict(sigma, H);
	A_H := BasisMatrix(H)*A*Transpose(BasisMatrix(H));
	refls_pts_H := find_reflection_pts(sigma_H, A_H);
	refls_pts := [y*BasisMatrix(H) : y in refls_pts_H];
    else
	// For now this works, since A is positive definite.
	// In general, should find a way to find y such that x is aniso
	aniso, y := get_aniso_vec(Image(sigma-1), A);
//	x := Solution(sigma-1,y);
//	assert (x*A, x) ne 0;
	if aniso then
	    // case 2
	    tau := build_reflection(y,A);
	    refls_pts := [y] cat find_reflection_pts(tau*sigma, A);
	else
	    // case 3
	    n := Nrows(A);
	    // from step 1
	    assert (n ge 4) and IsEven(n) and (Determinant(sigma) eq 1);
	    aniso, y := get_aniso_vec(RowSpace(A), A);
	    assert aniso; // else A = 0, which doesn't make sense
	    tau := build_reflection(y,A);
	    refls_pts := [y] cat find_reflection_pts(tau*sigma, A);
	end if;
    end if;
    assert &*[build_reflection(y, A) : y in refls_pts] eq sigma;
    return refls_pts;
end function;

function spinor_norm(sigma, A)
    refl_pts := find_reflection_pts(sigma, A);
    if #refl_pts eq 0 then return 1; end if;
    return &*[(x*A, x) : x in refl_pts];
end function;

intrinsic CharacterQQModSquares(d::RngIntElt,r::FldRatElt) -> RngIntElt
{Compute the value of the character of QQ / QQ^2 defined by d on the element r.
 d defines the character which sends the primes dividing d to -1.}
    fac_num := Factorization(ideal<Integers(Parent(r)) | Numerator(r)>);
    fac_den := Factorization(ideal<Integers(Parent(r)) | Denominator(r)>);
    fac := fac_num cat fac_den;
    ret := 1;
    for p_e in fac do
	p, e := Explode(p_e);
	if IsOdd(e) and (Order(p)!d in p) then
	    ret := -ret;
	end if;
    end for;
    return ret;
end intrinsic;

function rho(d, sigma, A)
    // assert Transpose(sigma)*A*sigma eq A;
    assert sigma * A * Transpose(sigma) eq A;
    if (Determinant(sigma) eq -1) then
	assert IsOdd(NumberOfRows(sigma));
	return rho(d, -sigma, A);
    end if;
    QQ := Rationals();
    return CharacterQQModSquares(d, QQ!spinor_norm(sigma, A));
end function;

// Is this the spinor norm of sigma or of its transpose???
intrinsic SpinorNormRho(d::RngIntElt, sigma::GrpMatElt, A::AlgMatElt)
  -> RngIntElt
{The spinor norm of sigma w.r.t. O(A), d divisor of disc(A).}
    return rho(d, ChangeRing(Transpose(Matrix(sigma)), BaseRing(A)), A);
end intrinsic;

forward my_prod;

intrinsic SpinorNormRepresentation(G::GrpRed, d::RngIntElt :
				   name := "x") -> GrpRep
{Constructs the spinor norm representation of the matrix group G.}
  A := InnerForm(InnerForm(G,1)); 
  K := BaseRing(A);
  Z_K := Integers(K);
  num := Z_K!Numerator(Determinant(A));
  denom := Z_K!Denominator(Determinant(A));
  fac := Factorization(ideal< Z_K | num*denom>);
  // We only care about the discriminant modulo squares in this case
  D := &*([ideal<Z_K | 1>] cat [f[1] : f in fac | IsOdd(f[2])]);
//  require D subset Z_K!!d :
//		"d should divide the discriminant";
  n := Nrows(A);
  M := CombinatorialFreeModule(K, [name]);
  a := Sprintf("
  function action(g,m,V)
  	return SpinorNormRho(%m, g, %m)*(V`M).m;   
  end function;
  return action;
  ", d, A);
  V :=  GroupRepresentation(GL(n,K), M, a);
  if d eq 1 then
    V`trivial := true;
  else
    V`trivial := false;
  end if;
  V`weight := <d, 0, 0>;
  return V;
end intrinsic;

intrinsic Rho(G::GrpMat, k::RngIntElt, j::RngIntElt) -> GrpRep
{Constructs the representation det^k \otimes Sym_j}
  det := DeterminantRepresentation(G : k := k);
  std := StandardRepresentation(G);
  sym := SymmetricRepresentation(std, j);
  return TensorProduct(det, sym);
end intrinsic;

intrinsic SymSpinor(G::GrpRed, d::RngIntElt, k::RngIntElt) -> GrpRep
{Constructs the representation spin_d \otimes Sym_k}
  spin := SpinorNormRepresentation(G, d);
  A := InnerForm(InnerForm(G,1));
  n := Nrows(A);
  K := BaseRing(A);
  if (Degree(K) eq 1) then
    K := Rationals();
  end if;
  std := StandardRepresentation(GL(n,K));
  sym := SymmetricRepresentation(std, k);
  W := TensorProduct(spin, sym);
  W`weight := <d,k,0>;
  return W;
end intrinsic;

intrinsic AltSpinor(G::GrpRed, d::RngIntElt, j::RngIntElt) -> GrpRep
{Constructs the representation spin_d \otimes Alt_j}
  spin := SpinorNormRepresentation(G, d);
  A := InnerForm(InnerForm(G,1));
  n := Nrows(A);
  K := BaseRing(A);
  if (Degree(K) eq 1) then
    K := Rationals();
  end if;
  std := StandardRepresentation(GL(n,K));
  sym := AlternatingRepresentation(std, j);
  W := TensorProduct(spin, sym);
  W`weight := <d,0,j div 2>;
  return W;
end intrinsic;

// This is code for experimenting with new features
// Here we construct representations of the symmetric group
// using Young symmetrizers
// At the moment we assume t is a canonical tableau

function getTableauRepresentation(t : R := Rationals())
  
  d := Weight(t);
  S := SymmetricGroup(d);
  act := Action(GSet(S));
  // This is an inefficient construction, as it goes over all elements
  // in S. Should rewrite.
  P_t := [g : g in S | &and[ {act(x,g) : x in Eltseq(r)} eq
			     {x : x in Eltseq(r)} : r in Rows(t)]];
  Q_t := [g : g in S | &and[ {act(x,g) : x in Eltseq(r)} eq
			     {x : x in Eltseq(r)} : r in Columns(t)]];
  Q_S := GroupAlgebra(R, S);
  a_t := &+[Q_S!g : g in P_t];
  b_t := &+[Sign(g)*Q_S!g : g in Q_t];
  c_t := a_t*b_t;
  V_t := lideal<Q_S | c_t>;

  M := CombinatorialFreeModule(Rationals(), IndexedSet(Basis(V_t)));


  a := Sprintf("
  function action(g, m, V)
    g_V := Vector(Eltseq(g*((V`M)`names[m])));
    orig := Matrix([Eltseq(b) : b in (V`M)`names]);
    vec := Solution(orig, g_V);
    return (V`M)!vec;
    end function;
    return action;
  ");

  V := GroupRepresentation(S, M, a);
  if &and[x eq 0 : x in d] then
    V`trivial := true;
  else
    V`trivial := false;
  end if;
  return V;
end function;

function getDigitsLittleEndian(i, b, d)
  assert Type(i) eq RngIntElt and i ge 0;
  tmp := i;
  digits := [];
  for j in [1..d] do
    Append(~digits, tmp mod b);
    tmp div:= b;
  end for;
  return digits;
end function;

function getNumberFromDigitsLittleEndian(digits, b)
  summands := [digits[i]* b^(i-1) : i in [1..#digits]];
  if IsEmpty(summands) then
    return 0;
  end if;
  return &+summands;
end function;

function getPermOnTensorPower(g, i, n)
  S := Parent(g);
  d := #GSet(S);
  act := Action(GSet(S));
  digits := getDigitsLittleEndian(i-1,n,d);
  perm_digits := [digits[act(j,g)] : j in [1..d]];
//  return &+[perm_digits[i]* n^(i-1) : i in [1..d]] + 1;
  return getNumberFromDigitsLittleEndian(perm_digits, n) + 1;
end function;

// This is the first construction in Fulton and Harris
// Can be made more efficient if needed.
// Also possible to use their construction in Chapter 15.
// Can also realize all representations at once.

function WeylModule(lambda, V)
  n := Dimension(V);
  R := BaseRing(V);
  k := #lambda;
  sums := [&+lambda[1..i] : i in [0..k]];
  tab := [[sums[i]+1..sums[i+1]] : i in [1..k]];
  t := Tableau(tab);
  d := Weight(t);
  if d eq 0 then
    return TensorPower(V, 0);
  end if;
  S := SymmetricGroup(d);
  act := Action(GSet(S));
  // This is an inefficient construction, as it goes over all elements
  // in S. Should rewrite.
  P_t := [g : g in S | &and[ {act(x,g) : x in Eltseq(r)} eq
			     {x : x in Eltseq(r)} : r in Rows(t)]];
  Q_t := [g : g in S | &and[ {act(x,g) : x in Eltseq(r)} eq
			     {x : x in Eltseq(r)} : r in Columns(t)]];
  // G := GL(n, R);
  // V := StandardRepresentation(G);
  V_d := TensorPower(V,d);
  big_sym := SymmetricGroup(n^d);
  P_t_act := [ big_sym![getPermOnTensorPower(g, i, n) : i in [1..n^d]]
		     : g in P_t	];
  Q_t_act := [ big_sym![getPermOnTensorPower(g, i, n) : i in [1..n^d]]
		     : g in Q_t	];
  P_t_act_V_d := [PermutationMatrix(R, g) : g in P_t_act];
  Q_t_act_V_d := [PermutationMatrix(R, g) : g in Q_t_act];
  a_t := &+[g : g in P_t_act_V_d];
  b_t := &+[Sign(Q_t[i])*Q_t_act_V_d[i] : i in [1..#Q_t]];
  c_t := a_t*b_t;
  return Subrepresentation(V_d, Rows(c_t));
end function;

function getGLnHighestWeightRepresentation(n, lambda : R := Rationals())
  V := StandardRepresentation(GL(n, R));
  return WeylModule(lambda, V);
end function;

// !!! TODO : Add the construction via polynomials appearing in exercise 15.57

function get_basis(lambda, n : F := Rationals())
  R := PolynomialRing(F, n^2);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..n]] : i in [1..n]];
  AssignNames(~R, &cat var_names);
  mu := ConjugatePartition(lambda);
  x := Matrix([[R.(Index(&cat var_names, var_names[i][j])) : j in [1..n]]
		  : i in [1..n]]);
  tabs := TableauxOfShape(lambda, n);
  basis := [&*[Determinant(Submatrix(x, [1..mu[j]],
				     [Integers()!Columns(t)[j][i]
					 : i in [1..mu[j]]])) : j in [1..#mu]]
	       : t in tabs];
  return basis, x;
end function;

function get_action_polys(lambda, n, g : F := Rationals())
  B, x := get_basis(lambda, n  : F := F);
  R := Universe(B);
  g_R := ChangeRing(g, R);
  B_g := [Evaluate(f, Eltseq(x*g_R)) : f in B];
  mons := &join([Set(Monomials(b)) : b in B]);
  mons := SetToSequence(mons);
  V := VectorSpace(F, #mons);
  vecs := [&+[Coefficients(b)[i]*V.(Index(mons, Monomials(b)[i]))
		 : i in [1..#Monomials(b)]] : b in B];
  vecs_g := [&+[Coefficients(b)[i]*V.(Index(mons, Monomials(b)[i]))
		   : i in [1..#Monomials(b)]] : b in B_g];
  return Solution(Matrix(vecs), Matrix(vecs_g));
end function;

// !! TODO : complete - have to pass along all the relevant data
// about the polynomials

// This is not very efficient, but will do for now

function getGLnHighestWeightRepresentationPolys(n, lambda : F := Rationals())
  B := get_basis(lambda, n  : F := F);
  M := CombinatorialFreeModule(F, {@ b : b in B@});
 
  action_desc := Sprintf("           
  	      function action(g, m, V)
	      	      B := Names(V`M);
                      R := Universe(B);
                      n := %o;
                      x := Matrix([[R.(n*i+j+1) : j in [0..n-1]] 
                           : i in [0..n-1]]);
                      F := BaseRing(R);
                      mons := &join([Set(Monomials(b)) : b in B]);
                      mons := SetToSequence(mons);
                      mon_vs := VectorSpace(F, #mons);
                      vecs := [&+[Coefficients(b)[i]*
                              mon_vs.(Index(mons, Monomials(b)[i]))
		               : i in [1..#Monomials(b)]] : b in B];
                      g_R := ChangeRing(g, R);
                      f := B[m];
                      f_g := Evaluate(f, Eltseq(x*g_R));
                      vec_g := &+[Coefficients(f_g)[i]*
                                mon_vs.(Index(mons, Monomials(f_g)[i]))
		                : i in [1..#Monomials(f_g)]];
                      return (V`M)!Solution(Matrix(vecs), vec_g);
  	      end function;
  	      return action;
	      ", n);
  V := GroupRepresentation(GL(n, F), M, action_desc);
  if &and[x eq 0 : x in lambda] then
    V`trivial := true;
  else
    V`trivial := false;
  end if;
  return V;
end function;

function Contraction(Q, p, q, d)
  assert (1 le p) and (p lt q) and (q le d);
  function get_contraction_image(i, Q, p, q, d)
    n := Degree(Parent(Q));
    digits := getDigitsLittleEndian(i-1,n,d);
    rest_digits := [digits[i] : i in [1..d] | i notin [p,q]];
// image_ind := &+[rest_digits[i]* n^(i-1) : i in [1..d-2]] + 1;
    image_ind := getNumberFromDigitsLittleEndian(rest_digits, n) + 1;
    return <Q[digits[p]+1, digits[q]+1],image_ind>;
  end function;
  R := BaseRing(Q);
  n := Degree(Parent(Q));
  V := StandardRepresentation(GL(n,R));
  V_d := TensorPower(V, d);
  V_d_2 := TensorPower(V, d-2);
  images := [get_contraction_image(i, Q, p, q, d) : i in [1..n^d]];
  basis_images := [t[1]*V_d_2.(t[2]) : t in images];
  // This could be a problem - creating a morphism between
  // two large spaces is difficult for magma for some reason.
  return Homomorphism(V_d, V_d_2, basis_images);
end function;

// Here Q can either be a symmetric or a symplectic form.
function getHighestWeightRepresentation(Q, lambda)
  n := Degree(Parent(Q));
  V := StandardRepresentation(GL(n,BaseRing(Q)));
  k := #lambda;
  sums := [&+lambda[1..i] : i in [0..k]];
  tab := [[sums[i]+1..sums[i+1]] : i in [1..k]];
  t := Tableau(tab);
  d := Weight(t);
  kernels := [Kernel(Contraction(Q, p, q, d))
		       : p,q in [1..d] | p lt q];
  if IsEmpty(kernels) then
    return WeylModule(lambda, V);
  end if;
  V_bracket_d := &meet kernels;  
  ret := V_bracket_d meet WeylModule(lambda, V);
  // Here we add a 1 in the beginning to indicate a divisor of the
  // Discriminant, see e.g. spinor norm.
  // Should understand what are the irreps over Q to do this properly.
  ret`weight := [1] cat lambda;
  // This is also a temporary patch
  ret`weight := ret`weight cat [0 : i in [1..3-#ret`weight]];
  return ret;
end function;

function getSpHighestWeightRepresentation(n, lambda : R := Rationals())
  G := SymplecticGroup(n, R);
  Q := InnerForm(InnerForms(G)[1]);
  return getHighestWeightRepresentation(Q, lambda);
end function;

function my_sum(seq, univ)
  if IsEmpty(seq) then
     return univ!0;
  end if;
  return &+seq;
end function;

function my_prod(seq, univ)
  if IsEmpty(seq) then
     return univ!1;
  end if;
  return &*seq;
end function;

function get_lap_kernel(lap : basis := false)
  F := BaseRing(Universe(lap));
  im_B := lap;
  im_mons := SetToSequence(&join([Set(Monomials(b)) : b in im_B]));
  W := VectorSpace(F, #im_mons);
  im_vecs := [my_sum([Coefficients(b)[i]*W.(Index(im_mons, Monomials(b)[i]))
		      : i in [1..#Monomials(b)]], W) : b in im_B];
  if basis then
      vec_basis :=  Basis(sub<Universe(im_vecs) | im_vecs>);
      poly_basis := [&+[b[i] * im_mons[i] : i in [1..#im_mons]] : b in vec_basis];
      return poly_basis;
  end if;
  K := Kernel(Matrix(im_vecs));
  return K;
end function;

function get_hw_basis_gl(lambda, F, n)
  mu := ConjugatePartition(lambda);
  k := Maximum(mu cat [0]);
  R := PolynomialRing(F, n*k);
  var_names := [[Sprintf("x_%o_%o", i,j) : j in [1..k]] : i in [1..n]];
  AssignNames(~R, &cat var_names);

  if k eq 0 then
      x := RMatrixSpace(R, n, 0)!0;
  else
      x := Matrix([[R.(Index(&cat var_names, var_names[i][j]))
		    : j in [1..k]]: i in [1..n]]);
  end if;
  // TableauxOfShape needs the exact partition, so we trim
  lam := [l : l in lambda | l gt 0];
  if IsEmpty(lam) then
    lam := [0];
  end if;
  tabs := TableauxOfShape(lam, n);
  B := [my_prod([Determinant(Submatrix(x, [Integers()!Columns(t)[j][i]
					: i in [1..mu[j]]], [1..mu[j]]))
	      : j in [1..#mu]], R) : t in tabs];
  return B, x;
end function;

function tau_polys(x,Q,sign)
    assert IsEven(Rank(Q));
    F := BaseRing(Q);
    _<y> := PolynomialRing(F);
    is_sqr, scale := IsSquare(Determinant(Q));
    if is_sqr then
	K := F;
    else
	K<scale> := ext<F | y^2 - Determinant(Q)>;
    end if;
    
    n := Rank(Q) div 2;
    assert Nrows(x) eq 2*n;
    
    idxs := [SetToSequence(s) : s in Subsets({1..2*n}, n)];
    basis := [Minor(x,I,[1..n]) : I in idxs];
    K_polys := ChangeRing(Universe(basis), K);
    tau_basis := [K_polys!b : b in basis[1..#basis]];
    
    // complements to idxs
    comp := [[x : x in [1..2*n] | x notin idx] :  idx in idxs];
    assert &and[c in idxs : c in comp];
    for i in [1..#idxs] do
	I := idxs[i];
	for j in [1..#idxs] do
	    J_prime := idxs[j];
	    J := comp[j];
	    s := Sign(Sym(2*n)!(J_prime cat J));
	    tau_basis[i] +:= K_polys!(sign * s * Minor(Q,I,J) * basis[j]) / scale;
	end for;
    end for;
 
    return tau_basis;
end function;

function get_hw_basis_so(lambda, Q : Dual := true, Special := false)
  F := BaseRing(Q);
  n := Degree(Parent(Q));
  lambda_gl := lambda;
  // in the even rank case, this could be negative
  lambda_gl[#lambda] := Abs(lambda[#lambda]);
  B, x := get_hw_basis_gl(lambda_gl, F, n);
  Q_lap := Dual select Q^(-1) else Q;
  k := Maximum(ConjugatePartition(lambda_gl) cat [0]);
  laplacians := [[&+[Q_lap[i,j]*Derivative(Derivative(f, x[i][p]), x[j][q])
		     : i,j in [1..n]] : f in B] : p,q in [1..k]];
  kers := [get_lap_kernel(lap) : lap in laplacians];
  
  ker := &meet (kers cat [VectorSpace(F, #B)]);
  basis := [&+[b[i]*B[i] : i in [1..#B]] : b in Basis(ker)];
  // In even rank, when lambda_n ne 0, the above gives a sum of two irreducibles.
  // We separate them out using the map tau, as described in [FultonHarris, p. 298]
  if (n eq 2 * #lambda) and (lambda[#lambda] ne 0) and Special then
      sign := Sign(lambda[#lambda]);
      tau_basis := tau_polys(x, Q_lap, sign);
      deg_gap := Degree(B[1]) - (n div 2);
      // R_poly := BaseRing(x);
      R_poly := Universe(tau_basis);
      I := [mon*p : mon in MonomialsOfDegree(R_poly,deg_gap), p in tau_basis];
      // I_basis := get_lap_kernel(I : basis);
      // I_red := [&+[b[i]*I[i] : i in [1..#I]] : b in I_basis];
      I_red := get_lap_kernel(I : basis);
      basis := [R_poly!b : b in basis];
      ker := get_lap_kernel(basis cat I_red);
      basis := [&+[b[i]*basis[i] : i in [1..#basis]] : b in Basis(ker)];
  end if;
  return basis;
end function;

function get_hw_rep_poly(lambda, B, n, F : Dual := false)
  R := Universe(B);
  K := BaseRing(R);
  M := CombinatorialFreeModule(K, {@ b : b in B@});
  mons := &join([Set(Monomials(b)) : b in B]);
  mons := SetToSequence(mons);
  degs := [[Integers() | Degree(m, R.i) : i in [1..Rank(R)]] : m in mons];
  mon_vs := VectorSpace(K, #mons);
  // This is somewhat long, optimize if needed
  vecs := [&+([mon_vs!0] cat [Coefficients(b)[i]*
              mon_vs.(Index(mons, Monomials(b)[i]))
	      : i in [1..#Monomials(b)]]) : b in B];
  hw_vdw_data := [* degs, [Eltseq(v) : v in vecs] *];
  // !!! TODO - this is still inefficient
  // can change construction of vec_g to not need multiplication
  g_R_str := Dual select Sprintf("g^(-1)") else Sprintf("Transpose(g)");
  k := Maximum(ConjugatePartition(lambda[1..#lambda-1] cat [Abs(lambda[#lambda])]) cat [0]);
  action_desc := Sprintf("           
  	      function action(g, m, V)
	      	      B := Names(V`M);
                      R := Universe(B);
                      n := %o;
		      k := %o;
                      gens := GeneratorsSequence(R);
		      if k eq 0 then
		      	 x := RMatrixSpace(R, n, 0)!0;
		      else			 
                         x := Matrix([[gens[k*i+j+1] 
                                       : j in [0..k-1]] : i in [0..n-1]]);
		      end if;
                      g_R := ChangeRing(%o, R);
                      f := B[m];
                      f_g := Evaluate(f, Eltseq(g_R*x));
                      deg_rev := V`hw_vdw_rev;
                      F := BaseRing(R);
                      mon_vs := VectorSpace(F, #deg_rev);
                      basis_mat := ChangeRing(Matrix(V`hw_vdw[2]), F);
                      degs_f_g := [];
                      mons_f_g := Monomials(f_g);
                      for m in mons_f_g do
                         degs_m := Exponents(m);
                         Append(~degs_f_g, degs_m);
                      end for;
                      coeffs := Coefficients(f_g);
                      vec_g := mon_vs!0;
                      for i in [1..#degs_f_g] do
                         vec_g +:= coeffs[i]*mon_vs.(deg_rev[degs_f_g[i]]);
                      end for;
                      // return (V`M)!Solution(basis_mat, vec_g);
                      return CombinatorialFreeModuleElement(V`M, 
                                 Solution(basis_mat, vec_g));
  	      end function;
  	      return action;
	      ", n, k, g_R_str);
  
  V := GroupRepresentation(GL(n, F), M, action_desc :
			   params := [* <"HW_VDW", <hw_vdw_data, lambda> > *]);
  if &and[x eq 0 : x in lambda] then
    V`trivial := true;
  else
    V`trivial := false;
  end if;
  return V;
end function;

function getGLHighestWeightRepresentationPolys(lambda, F, n)
  is_dominant := &and[lambda[i] ge lambda[i+1] : i in [1..#lambda-1]];
  error if not is_dominant, "highest weight must be dominant";
  adjust := false;
  m := lambda[#lambda];
  if m lt 0 then
    det_rep := DeterminantRepresentation(GL(n,F) : k := m);
    adjust := true;
    w := [l - m : l in lambda];
  else
    w := lambda;
  end if;
  B := get_hw_basis_gl(w, F, n);
  V := get_hw_rep_poly(w, B, n, F);
  if adjust then
    V := TensorProduct(V, det_rep);
    V`lambda := lambda;
  end if;
  return V;
end function;

function getSOHighestWeightRepresentationPolys(lambda, Q : Special := false)
  n := Degree(Parent(Q));
  B := get_hw_basis_so(lambda, Q : Special := Special);
  F := BaseRing(Q);
  return get_hw_rep_poly(lambda, B, n, F : Dual);
end function;

// This is for debugging purposes
function dimensionOfHighestWeightRepresentationOddOrthogonal(lambda, m)
  assert IsOdd(m);
  n := m div 2;
  assert #lambda le n;
  lambda cat:= [0 : i in [1..(n-#lambda)]];
  l := [lambda[i] + n - i : i in [1..n]];
  prod := my_prod([(l[i]-l[j])*(l[i]+l[j]+1) : i,j in [1..n] | i lt j],
		Integers());
  num := prod * &*[2*l[i]+1 : i in [1..n]];
  denom := &*[Factorial(2*n-2*j+1) : j in [1..n]];
  return num div denom;
end function;

intrinsic HighestWeightRepresentation(G::GrpRed,
				      lambda::SeqEnum[RngIntElt]) -> GrpRep
{returns the irreducible representation with highest weight lambda.}
  require #InnerForms(G) eq 1 : "Highest weight representation for G is currently not supported";
  Q := InnerForm(InnerForms(G)[1]);
  F := BaseRing(Q);
  if Type(F) ne FldFin then
      F := NumberField(MaximalOrder(F));
  end if;
  Q := ChangeRing(Q, F);
  if IsOrthogonal(G) then
    V := getSOHighestWeightRepresentationPolys(lambda, Q : Special := IsSpecialOrthogonal(G));
    if NumberOfRows(Q) eq 5 then
       V`weight := <1, lambda[1] - lambda[2], lambda[2]>;
    end if;
  elif IsUnitary(G) then
    V := getGLHighestWeightRepresentationPolys(lambda, F, Degree(Parent(Q)));
  // Should check this out, but I believe this would work.
  elif IsSymplectic(G) then
    V := getSOHighestWeightRepresentationPolys(lambda, Q);
  else
    error "Highest weight representation for G is currently not supported";
  end if;
  V`grp := G;
  return V;
end intrinsic;

// !! TODO - this is false when p = 2 (-1 = 1 in F2)
intrinsic SinglePrimeSpinorNormRepresentation(G::GrpRed, p::RngIntElt) -> GrpRep 
{new method of constructing the spinor norm representations. }
  Q := InnerForm(G,1);
  L := StandardLattice(Q);
  disc := Norm(Discriminant(L));
  v := Valuation(disc,p);
  if (p eq 2) then v +:= 1; end if;
  n := Dimension(L);
  pR := Factorization(ideal<BaseRing(L) | p>)[1][1];
  nProc := BuildNeighborProc(L, pR, 1);
  // we use the fact that in our standard decomposition,
  // the radical is in the end
  Vpp := L`Vpp[pR]`V;
  rad := Matrix(Transpose(Vpp`Basis)[n-Vpp`RadDim+1..n]);
  basis := L`pMaximal[pR][2];
  ZF := Order(pR);
  ZF_p := Completion(ZF, pR);
  // Needed to introduce this line due to a bug in Magma 2.26-12
  ZF_p := Integers(ZF_p);
  Fp := ResidueClassField(ZF_p);
  rad := rad * ChangeRing(basis, Fp);
  pRdata := [Eltseq(x) : x in Generators(pR)];
  Q := ChangeRing(InnerForm(Q), Integers());
//  if (p eq 2) then
  for j in [2..v] do
      lift := Matrix([[Integers()!x : x in Eltseq(rad_row)] : rad_row in Rows(rad)]);
      liftQ := lift * Q;
      liftp := ChangeRing(liftQ div p^(j-1), GF(p));
      sol := Solution(ChangeRing(Q, GF(p)), -liftp);
      sol_lift := Matrix([[Integers()!x : x in Eltseq(sol_row)] : sol_row in Rows(sol)]);
      rad := ChangeRing(lift + p^(j-1)*sol_lift, Integers(p^j));
  end for;
//  end if;
  a := Sprintf("
    function action(g,m,V)
          rad := %m;
          n := %m;
          Fp := BaseRing(rad);
          ZF := Integers(BaseRing(g));
          pRdata := %m;
          pR := ideal<ZF | [ZF!x : x in pRdata]>;
	  p := PrimeDivisors(#Fp)[1];
	  if (not IsPrime(#Fp)) then  
	     v := Valuation(Denominator(g),p);
	     g_p := ChangeRing(p^v*Matrix(Transpose(g)),Fp);
	     is_coer := true;
	     if (v ne 0) and (#Fp eq 4) then
	     	is_coer := false;
	     end if;	
	  else
	     ZF_p := Completion(ZF, pR);
	     // Needed to introduce this line due to a bug in Magma 2.26-12
  	     ZF_p := Integers(ZF_p);
             dummy, redp := ResidueClassField(ZF_p);
             assert Fp eq dummy;
             redp_mat := hom<MatrixAlgebra(ZF_p, n) -> MatrixAlgebra(Fp,n) | redp>;
	     is_coer, g_0 := IsCoercible(MatrixAlgebra(ZF_p, n),g);
	     if is_coer then
	     	     g_p := Transpose(redp_mat(g_0));
	     end if;
	  end if;
	  if (not is_coer) then
	       return SpinorNormRho(p, g, %m)*(V`M).m;
	  end if;
	  sol := Solution(rad,rad*g_p);
	  if (not IsPrime(#Fp)) then
	     Mn := MatrixRing(Integers(#Fp div p^v), Nrows(sol));
	     sol := Mn![x div p^v : x in  Eltseq(sol)];
	  end if;
          scalar := Determinant(sol);
	  assert (scalar eq 1) or (scalar eq -1);
          scalar := (scalar eq 1) select Integers()!1 else -Integers()!1;
          return scalar*(V`M).m; 
    end function;
    return action;
  ", rad, n, pRdata, ChangeRing(Q, Rationals()));
  M := CombinatorialFreeModule(BaseRing(G), ["v"]);
  return GroupRepresentation(GL(n,BaseRing(G)), M, a);
end intrinsic;

// Something here is off
intrinsic SpinorNormRepresentationFast(G::GrpRed, d::RngIntElt) -> GrpRep
{Constructs the spinor norm representation of the matrix group G.}
  A := InnerForm(InnerForm(G,1)); 
  K := BaseRing(A);
  fac := Factorization(d);
  // We only care about the discriminant modulo squares in this case
//  D := &*([ideal<Z_K | 1>] cat [f[1] : f in fac | IsOdd(f[2])]);
//  require D subset Z_K!!d :
//		"d should divide the discriminant";
  primes := [f[1] : f in fac | IsOdd(f[2])];
  n := NumberOfRows(A);
  V := TrivialRepresentation(GL(n,K), K);
  for p in primes do
    V := TensorProduct(V, SinglePrimeSpinorNormRepresentation(G, p));
  end for;
  if d eq 1 then
    V`trivial := true;
  else
    V`trivial := false;
  end if;
  V`weight := <d, 0, 0>;
  return V;
end intrinsic;

function tau_alternating(V, Q)
    assert IsEven(Rank(Q));
    n := Rank(Q) div 2;
    tau := ZeroMatrix(BaseRing(V), Dimension(V));
    bases_names := [Split(name , "^") : name in V`M`names];
    idxs := [[Index(V`alternating`M`names, name) : name in base_names] : base_names in bases_names];
    // complements to idxs
    comp := [[x : x in [1..2*n] | x notin idx] :  idx in idxs];
    assert &and[c in idxs : c in comp];
    for i in [1..#idxs] do
	I := idxs[i];
	for j in [1..#idxs] do
	    J_prime := idxs[j];
	    J := comp[j];
	    s := Sign(Sym(2*n)!(J_prime cat J));
	    tau[i][j] := s * Minor(Q,I,J);
	end for;
    end for;
    assert IsScalar(tau^2);
    return tau;
end function;

function get_plus_representation(V,Q)
    tau := tau_alternating(V, Q);
    tau2 := (tau^2)[1,1]; // This should be det(Q), but to be on the safe side
    is_sqr, sqrt_tau := IsSquare(tau2);
    // !! TODO - handle the non-square case
    return Subrepresentation(V,Basis(Eigenspace(tau, sqrt_tau)));
end function;

intrinsic GetSplitPrimeWithSquare(G::GrpRed : LowerBound := 2) -> RngIntElt
{Returns a prime where G_p is split, and 2 is a square.}
  V := InnerForm(G,1);
  L := StandardLattice(V);
  n := Dimension(L);
  is_split_prime := false;
  p := LowerBound-1;
  while (not is_split_prime) do
      p := NextPrime(p);
      pR := Factorization(ideal<BaseRing(L) | p>)[1][1];
      nProc := BuildNeighborProc(L, pR, 1);
      Vpp := L`Vpp[pR]`V;
      witt := Vpp`WittIndex;
      is_split_prime := Vpp`WittIndex eq n div 2;
      std_basis := Transpose(Vpp`Basis);
      u := std_basis[n];
      norm_u := (u*Vpp`GramMatrix, u);
      is_split_prime and:= IsSquare(GF(p)!2 / norm_u);
  end while;
  return p;
end intrinsic;			   
		       
intrinsic SpinRepresentation(G::GrpRed, p::RngIntElt) -> GrpRep
{Constructs the Spin representation of G=SO(Q) mod p. }
  V := InnerForm(G,1);
  Q := InnerForm(V);
  L := StandardLattice(V);
  n := Dimension(L);
  pR := Factorization(ideal<BaseRing(L) | p>)[1][1];
  nProc := BuildNeighborProc(L, pR, 1);
  Vpp := L`Vpp[pR]`V;
  F := BaseRing(Vpp);
  M := CombinatorialFreeModule(F, [Sprintf("x%o", i) : i in [1..n div 2]]);
  M := ExteriorAlgebra(M);
  a := Sprintf("
  function action(g,m,V)
      pR := V`spin[1];
      L := V`spin[2];
      mat := get_spin_matrix_action(g, pR, L);
      return V`M!(mat[m]);
  end function;
  return action;
  ");
  Spin := GroupRepresentation(GL(n,BaseRing(V)), M, a  : params := [* <"SPIN", [* pR, L *]> *]);
  Spin`trivial := false;
  
  return Spin;
  end intrinsic;

intrinsic HighestWeightRepresentation(G::GrpRed, lambda::SeqEnum[RngIntElt], char::RngIntElt) -> GrpRep
{.}
   V := HighestWeightRepresentation(G, lambda);
   F := BaseRing(G);
   pR := Factorization(ideal<Integers(F)|char>)[1][1];
   Fq, mod_q := ResidueClassField(pR);
   V := ChangeRing(V, Fq);   
   n := Dimension(InnerForm(G,1));

   f_desc := Sprintf("
      function foo(H)
        F := BaseRing(H);
        n := %m; 
        pR := Factorization(ideal<Integers(F)|%m>)[1][1];
        Fq, mod_q := ResidueClassField(pR);
        f := map< H -> GL(n,Fq) |
		  x :-> projLocalization(x, mod_q)>;
        return f;
      end function;
      return foo;
       ", n, char);
   W := Pullback(V,f_desc, GL(n, F));
   return W;
end intrinsic;

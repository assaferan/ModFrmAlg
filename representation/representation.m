//freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: representation.m (class for group representations)

   03/16/20: Added basic documentation
   	     Added operator @@ (preimage) 

   03/13/20: Added handling of homomorphisms
   	     Separated CombinatorialFreeModule to a separate file.

   03/12/20: started writing this file
 
 ***************************************************************************/

// This should have been done using GModule
// But for some reason, it's really terrible, so we are doing our own
// This is currently built on top of combinatorial free modules
// to allow for nice (= meaningful) representations of the elements

declare type GrpRep[GrpRepElt];
declare attributes GrpRep :
		   // the group
		   G,
	// the module
	M,
	// the action on basis elements
	action,
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
	// This is assigned only if our representation is a tensor product, since
	// in this case we can compute the action matrix easily by computing the
	// tensor product of the matrices.
	tensor_product,
	// In case this is a subrepresentation, its ambient representation
	ambient,
	// In case this is a subrepresentation, the embedding into its ambient.
	embedding;

declare attributes GrpRepElt :
		   // the actual element in the module
		   m,
	// its parent
	parent;

/* constructors */

intrinsic GroupRepresentation(G::Grp, M::CombFreeMod, action::Map) -> GrpRep
{Constructs a group representation for the group G on the combinatorial free module
M, such that the action on basis elements G x Basis(M) -> M is described by the map action .}

  V := New(GrpRep);
  V`G := G;
  V`M := M;
  V`action := action;

  require (Domain(action) eq CartesianProduct(G, [1..Dimension(M)])) and
	  (Codomain(action) eq M) :
	"action should have domain G x [1..Dimension(M)], and codomain M.";
  V`act_mats := AssociativeArray();
  V`known_grps := [sub<G|1>];
  V`act_mats[G!1] := IdentityMatrix(BaseRing(M), Dimension(M));

  return V;
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
  t := [V!x : x in Flat(t)];
  N, i := SubCFModule(V`M, [v`m : v in t]);
  N_idx := [1..Dimension(N)];
  action := map< CartesianProduct(V`G, N_idx) -> N |
	       x :-> ((x[1] * V!(i(N.(x[2]))))`m)@@i>;
  U := GroupRepresentation(V`G, N, action);
  iota := Homomorphism(U, V, i);
  U`ambient := V;
  U`embedding := iota;
  return U, iota;
end intrinsic;

/* constructors of some special cases of representations */

intrinsic TrivialRepresentation(G::Grp, R::Rng : name := "v") -> GrpRep
{Constructs the trivial representation for G over the ring R.}
  M := CombinatorialFreeModule(R, [name]);
  a := map < CartesianProduct(G,[1..Dimension(M)]) -> M | x :-> M.(x[2])>;
  return GroupRepresentation(G, M, a);
end intrinsic;

intrinsic StandardRepresentation(G::GrpMat, R::Rng : name := "x") -> GrpRep
{Constructs the standard representation of the matrix group G on the ring R, i.e. the representation obtained by considering its given embedding in GL_n acting on R^n by invertible linear transformations.}
  n := Degree(G);
  names := [name cat IntegerToString(i) : i in [1..n]];
  M := CombinatorialFreeModule(R, names);
  a := map< CartesianProduct(G, [1..Dimension(M)]) -> M |
	  x :-> M!((M.(x[2]))`vec * Transpose(x[1]))>;
  return GroupRepresentation(G, M, a);
end intrinsic;

intrinsic SymmetricRepresentation(V::GrpRep, n::RngIntElt) -> GrpRep
{Constructs the representation Sym(V).}
  R := BaseRing(V);	  
  R_X := PolynomialRing(R, Rank(V));
  AssignNames(~R_X, V`M`names);
  S := MonomialsOfDegree(R_X, n);
  M := CombinatorialFreeModule(R, S);
  gens := RModule(R_X, Rank(V))!SetToSequence(MonomialsOfDegree(R_X,1));  
  function action(g,m)
      coeffs := [RModule(R_X, Rank(V)) | Eltseq(g * V.i) : i in [1..Dimension(V)]];
      ys := Vector(gens) * Transpose(Matrix(coeffs));
      ans := Evaluate(S[m], Eltseq(ys));
      ans_coeffs, mons := CoefficientsAndMonomials(ans);
      idxs := [Index(mons, name) : name in M`names];
      return &+[ans_coeffs[idxs[i]] * M.i : i in [1..#idxs] | idxs[i] ne 0];
  end function;
  a := map< CartesianProduct(V`G, [1..Dimension(M)]) -> M |
	  x :-> action(x[1], x[2]) >;
  return GroupRepresentation(V`G, M, a);
end intrinsic;

intrinsic DualRepresentation(V::GrpRep) -> GrpRep
{Constructs the dual representation of V.}
  R := BaseRing(V);
  names := [Sprintf("%o^*",b) : b in Basis(V)]; 
  M := CombinatorialFreeModule(R, names);
  function action(g,m)
      v := V!Eltseq(M.m);
      return M!(Eltseq(Transpose(g)^(-1) * v));
  end function;
  a := map< CartesianProduct(V`G, [1..Dimension(M)]) -> M | x :-> action(x[1], x[2]) >;
  return GroupRepresentation(V`G, M, a);
end intrinsic;

intrinsic TensorProduct(V::GrpRep, W::GrpRep) -> GrpRep
{Constructs the tensor product of the representations V and W, with diagonal action.}
  R := BaseRing(V);
  names := {@<v, w> : v in Basis(V), w in Basis(W)@};
  M := CombinatorialFreeModule(R, names);
  function action(g,m)
      vecs := [Vector(Eltseq(g*n)) : n in M`names[m]];
      return M!(TensorProduct(vecs[1], vecs[2]));
  end function;
  a := map< CartesianProduct(V`G, [1..Dimension(M)]) -> M | x :-> action(x[1], x[2]) >;
  ret := GroupRepresentation(V`G, M, a);
  ret`tensor_product := [V,W];
  return ret;
end intrinsic;

/* access and properties */

intrinsic Rank(V::GrpRep) -> RngIntElt
{The rank of the free module underlying the representation V.}
  return #Basis(V);	  
end intrinsic;

intrinsic Dimension(V::GrpRep) -> RngIntElt
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

/* printing */

intrinsic Print(V::GrpRep)
{.}
  printf "%o with an action of %o", V`M, V`G; 
end intrinsic;		   

/* generators and coercion */ 

intrinsic '.'(V::GrpRep, i::RngIntElt) -> GrpRepElt
{.}
  return GroupRepresentationElement(V, V`M.i);	     
end intrinsic;

intrinsic IsCoercible(V::GrpRep, x::Any) -> BoolElt, .
{.}
  is_coercible, v := IsCoercible(V`M, x);
  if is_coercible then
      return true, GroupRepresentationElement(V, v);
  else
      return false, "Illegal Coercion";
  end if;
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

intrinsic Print(elt::GrpRepElt)
{.}
  printf "%o", elt`m;
end intrinsic;

/*
 Computing the group action 
*/

// verifyKnownGroups is a procedure for cases of incoherent execution,
// e.g. execution was interrupted. It makes sure that the known groups
// are updated correctly.

procedure verifyKnownGroups(V)
    idxs := [[i : i in [1..Ngens(grp)] | grp.i in Keys(V`act_mats)] :
	     grp in V`known_grps];
    V`known_grps := [sub<V`G | [V`known_grps[j].i : i in idxs[j]]> : j in [1..#idxs]];
end procedure;

// getActionHom returns the homomorphism from the finite group grp to the
// automorphisms of the representation. 
function getActionHom(V, grp)
    GL_V := GL(Dimension(V), BaseRing(V));
    verifyKnownGroups(V); // this is in case there was some interrupt
    return hom< grp -> GL_V |
		  [V`act_mats[grp.i] : i in [1..Ngens(grp)]]>;
end function;

// At the moment, every time we compute the complete image of g in GL_V
// and store it for future use.
// When dimensions will be high, we would probably no longer wish to do that.

intrinsic getMatrixAction(V::GrpRep, g::GrpElt) -> GrpMatElt
{Computes the martix describing the action of g on V.}
  verifyKnownGroups(V); // this is in case there was some interrupt

  if HasFiniteOrder(g) then
      is_known := exists(grp){grp : grp in V`known_grps | g in grp};
  else
      is_known := g in Keys(V`act_mats);
  end if;

  if not is_known then
      if HasFiniteOrder(g) then
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
	  V`act_mats[g] := TensorProduct(getMatrixAction(V1, g),
					 getMatrixAction(V2, g));
      else if assigned V`ambient then
	       phi := Matrix(V`embedding`morphism);
	       phi_T := Transpose(phi);
	       mat_g := getMatrixAction(V`ambient, g);
	       V`act_mats[g] := phi * mat_g * phi_T * (phi * phi_T)^(-1); 
	   else
	       V`act_mats[g] := Matrix([V`action(g, i)`vec : i in [1..Dimension(V)]]);
	   end if;
      end if;
  end if;

  if HasFiniteOrder(g) then
      act_hom := getActionHom(V, grp);
      return act_hom(g);
  else
      return V`act_mats[g];
  end if;
  
end intrinsic;

/* arithmetic operations */

intrinsic '*'(g::GrpElt, v::GrpRepElt) -> GrpRepElt
{.}

  V := Parent(v);
  require g in V`G : "element must be in the group acting on the space";
  
  g_act := getMatrixAction(V,g);
  
  return V!(v`m`vec * g_act);
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
  return V1`M eq V2`M and V1`G eq V2`G and V1`action eq V2`action;
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

// This function is here simply due to our interest in GL3, U3, O3
// TODO : 1. Move it to the tests and examples.
//        2. Create a more general function for such constructions for
//           arbitrary dimensions.

function getGL3Rep(a, b, K)
    G := GL(3, K);
    V := StandardRepresentation(G, K);
    V_dual := DualRepresentation(V);
    sym_a := SymmetricRepresentation(V,a);
    sym_b_dual := SymmetricRepresentation(V_dual,b);
    return TensorProduct(sym_a, sym_b_dual);
end function;

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
  phi := New(GrpRepHom);
  phi`domain := V;
  phi`codomain := W;
  phi`morphism := hom<V`M`M -> W`M`M | [f(V.i)`m`vec : i in [1..Dimension(V)]]>;

  return phi;
end intrinsic;

intrinsic Homomorphism(V::GrpRep, W::GrpRep, f::Map) -> GrpRepHom
{Construct a homomorphism of group representations described by f. Note: the constructor does not verify that the map indeed describes a homomorphism of group representations.}
  phi := New(GrpRepHom);
  phi`domain := V;
  phi`codomain := W;

  require (Domain(f) eq V`M) and (Codomain(f) eq W`M) :
	"Map should be defined on the combinatorial modules of the representations"; 
  phi`morphism := hom<V`M`M -> W`M`M | [f((V.i)`m)`vec : i in [1..Dimension(V)]]>;

  return phi;
end intrinsic;

intrinsic Homomorphism(V::GrpRep, W::GrpRep, basis_images::SeqEnum) -> GrpRepHom
{Construct a homomorphism of group representations such that the images of the basis elements of V map to basis_images. Note: the constructor does not verify that the map indeed describes a homomorphism of group representations.}
  phi := New(GrpRepHom);
  phi`domain := V;
  phi`codomain := W;

  require (Universe(basis_images) eq W) :
	"images should be in the codomain representation"; 
  phi`morphism := hom<V`M`M -> W`M`M | [v`m`vec : v in basis_images]>;

  return phi;
end intrinsic;

intrinsic Homomorphism(V::GrpRep, W::GrpRep, f::CombFreeModHom) -> GrpRepHom
{Construct a homomorphism of group representations described by f. Note: the constructor does not verify that the map indeed describes a homomorphism of group representations.}
  phi := New(GrpRepHom);
  phi`domain := V;
  phi`codomain := W;

  require (Domain(f) eq V`M) and (Codomain(f) eq W`M) :
	"Map should be defined on the combinatorial modules of the representations"; 
  phi`morphism := hom<V`M`M -> W`M`M | [f((V.i)`m)`vec : i in [1..Dimension(V)]]>;
 
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

intrinsic Print(phi::GrpRepHom)
{.}
  printf "Homorphism from %o to %o", Domain(phi), Codomain(phi);
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

// getGL3Contraction map returns the contraction homomorphism between Sym^a(V) \otimes
// Sym^b(V^v) and Sym^{a-1}(V) \otimes Sym^{b-1}(V^v)
// where V is the standard representation of GL3. K is the coefficient ring.

// should change it to just specify what it does on basis vectors, that's enough

function getGL3ContractionMap(a,b,K)
    W_ab := getGL3Rep(a,b,K);
    W_minus := getGL3Rep(a-1, b-1,K);
    pure_tensor := W_ab`M`names[1];
    mon := pure_tensor[1];
    mon_dual := pure_tensor[2];
    mon_basis := Parent(mon)`M`names;
    alphas := [[Degree(b, i) : i in [1..3]] : b in mon_basis];
    mon_dual_basis := Parent(mon_dual)`M`names;
    betas := [[Degree(b, i) : i in [1..3]] : b in mon_dual_basis];
    coeffs := [[[alpha[i] * beta[i] : i in [1..3]] : beta in betas] : alpha in alphas];
    idxs := [[[i : i in [1..3] | coeff[i] ne 0] : coeff in coeffs_row] :
	     coeffs_row in coeffs];
    image_vecs := [[[<mon_basis[j1] div (Parent(mon_basis[j1]).i),
		     mon_dual_basis[j2] div Parent(mon_dual_basis[j2]).i> :
		     i in idxs[j1][j2]] : j2 in [1..#idxs[j1]]] : j1 in [1..#idxs]];
    pure_tensor_minus := W_minus`M`names[1];
    mon_minus := pure_tensor_minus[1];
    mon_dual_minus := pure_tensor_minus[2];
    sym_minus := Parent(mon_minus);
    sym_dual_minus := Parent(mon_dual_minus);
    mon_basis_minus := sym_minus`M`names;
    mon_dual_basis_minus := sym_dual_minus`M`names;
    image_idxs := [[[<sym_minus.Index(mon_basis_minus, im_vec[1]),
		      sym_dual_minus.Index(mon_dual_basis_minus,im_vec[2])> :
		     im_vec in image_vecs[j1][j2]] :
		    j2 in [1..#image_vecs[j1]]] : j1 in [1..#image_vecs]];
    W_minus_image := [[[W_minus.Index(W_minus`M`names, im_idx) :
		      im_idx in image_idxs[j1][j2]] :
		       j2 in [1..#image_idxs[j1]]] : j1 in [1..#image_idxs]];
    function get_basis_image(coeffs, idxs, W_minus_image)
	if IsEmpty(idxs) then return W_minus!0; end if;
	return &+[coeffs[idxs[i]] * W_minus_image[i] : i in [1..#idxs]];
    end function;
    basis_images := &cat [[get_basis_image(coeffs[j1][j2], idxs[j1][j2],
				      W_minus_image[j1][j2]) :
		      j2 in [1..#image_idxs[j1]]] :
			  j1 in [1..#image_idxs]];
    return Homomorphism(W_ab, W_minus, basis_images);
end function;

// getGL3HighestWeightRep - returns the highest weight representation of GL3 over K
// of highest weight (a,b,0)
// (at this point we do not consider the twist by the determinant)

function getGL3HighestWeightRep(a,b,K)
    return Kernel(getGL3ContractionMap(a,b,K));
end function;

intrinsic FixedSubspace(gamma::GrpMat, V::GrpRep) -> GrpRep
{Return the fixed subspace of V under the group gamma.}
  require IsFinite(gamma) :
		"At the moment this is only supported for finite groups";
  char := Characteristic(BaseRing(V));
  require (char eq 0) or (GCD(#gamma, char) eq 1) :
    "At the moment this only works when characteristic is prime to the group size";
  gamma_gens := Generators(gamma);
  gamma_actions := [getMatrixAction(V, g) : g in gamma_gens];
  GL_V := GL(Dimension(V), BaseRing(V));
  gamma_image := sub<GL_V | gamma_actions>;
  trace := &+[Matrix(g) : g in gamma_image];
  return Subrepresentation(V, Basis(Image(trace)));
end intrinsic;

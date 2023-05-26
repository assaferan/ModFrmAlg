// Cayley-Dickson algebras
declare type AlgCD[AlgCDElt];
declare attributes AlgCD :
		   // the algebra with involution we start with
		   A,
	// the involution
	sigma,
	// the constant delta we are using 
        delta,
	// a basis for the subspace of this subalgebra
        basis,
	ambient,
	embedding;

declare attributes AlgCDElt :
		   // the CD algebra it belongs to
		   parent,
		   // the vector (of length 2) representing the element in A + A
	vec;

intrinsic CDAlgebra(A::AlgGen, sigma::Map, delta::FldElt) -> AlgCD
{Create the Cayley-Dickson algebra associated to the algebra with involution A and delta.}
  require BaseField(A) eq Parent(delta) : "Element should be in the base field of the algebra";
  B := New(AlgCD);
  B`A := A;
  B`sigma := sigma;
  B`delta := delta;
  B`ambient := B;
  B`embedding := map<B -> B | x :-> x>;
  B`basis := [B![x,0] : x in Basis(B`A)] cat [B![0,x] : x in Basis(B`A)];
  return B;
end intrinsic;

intrinsic BaseField(B::AlgCD) -> Fld
{.}
  return BaseField(B`A);
end intrinsic;

intrinsic Ambient(S::AlgCD) -> AlgCD
{.}
  return S`ambient;
end intrinsic;

intrinsic Basis(B::AlgCD) -> SeqEnum[AlgCDElt]
{Returns a basis of B.}
  return B`basis;
end intrinsic;

intrinsic '.'(B::AlgCD, i::RngIntElt) -> AlgCDElt
{.}
  require ((i gt 0) and (i le #B`basis)) : "index out of range.";
  return B`basis[i];
end intrinsic;

intrinsic Print(B::AlgCD, level::MonStgElt)
{.}
  if (level eq "Magma") then
    printf "CDAlgebra(%m, %m)", B`A, B`delta;
  end if;
  printf "Cayley-Dickson algebra over %o with delta=%o", B`A, B`delta;
  return;
end intrinsic;

intrinsic IsCoercible(B::AlgCD, v::.) -> BoolElt, .
{Coerce v into B if possible.}
   if Type(v) eq AlgCDElt then	
       if Parent(v) eq B then
	   return true, v;
       end if;
       S := Parent(v);
       if (S`A eq B`A) and (S`sigma eq B`sigma) and (S`delta eq B`delta) then
	   return true, B!(v`vec);
       end if;
       return false, "Arguments are not compatible";
   end if;
   if ISA(Type(v), SeqEnum) then
       if #v eq 2 then
	   is_A1, v1 := IsCoercible(B`A, v[1]);
	   is_A2, v2 := IsCoercible(B`A, v[2]);
	   if (not is_A1) or (not is_A2) then return false, "Arguments are not compatible"; end if;
	   b := New(AlgCDElt);
	   b`parent := B;
	   b`vec := [v1, v2];
	   return true, b;
       elif #v eq 8 then
	   is_coercible := true;
	   v_elts := [];
	   for i in [1..8] do
	       is_F, x := IsCoercible(BaseField(B), v[i]);
	       if not is_F then return false, "Arguments are not compatible"; end if;
	       Append(~v_elts, x);
	   end for;
	   b := New(AlgCDElt);
	   b`parent := B;
	   b`vec := [(B`A)!v_elts[1..4], (B`A)!v_elts[5..8]];
	   return true, b;
       else
	   return false, "Degree is incompatible";
       end if;
  end if;
  is_A, v_A := IsCoercible(B`A, v);
  if is_A then
      return true, B![v_A, 0];
  end if;
  return false, "Illegal coercion";
end intrinsic;

intrinsic Print(b::AlgCDElt, level::MonStgElt)
{.}
  if (level eq "Magma") then
    printf "%m!%m", Parent(b), b`vec;
  end if;
  printf "%o", b`vec;
  return;
end intrinsic;

intrinsic '+'(x::AlgCDElt, y::AlgCDElt) -> AlgCDElt
{.}
  require Parent(x) eq Parent(y) : "Arguments are not compatible";
  B := Parent(x);
  x1, x2 := Explode(x`vec);
  y1, y2 := Explode(y`vec);
  z := [x1+y1, x2+y2];
  return B!z;
end intrinsic;

intrinsic '-'(x::AlgCDElt) -> AlgCDElt
{.}
  B := Parent(x);
  x1, x2 := Explode(x`vec);
  return B![-x1,-x2];
end intrinsic;

intrinsic '-'(x::AlgCDElt, y::AlgCDElt) -> AlgCDElt
{.}
  return x+(-y);
end intrinsic;

intrinsic '+'(x::FldElt, y::AlgCDElt) -> AlgCDElt
{.}
  return (Parent(y)!x) + y;
end intrinsic;

intrinsic '*'(x::FldElt, y::AlgCDElt) -> AlgCDElt
{.}
  return (Parent(y)!x) * y;
end intrinsic;
	     
intrinsic '*'(x::AlgCDElt, y::AlgCDElt) -> AlgCDElt
{.}
  require Parent(x) eq Parent(y) : "Arguments are not compatible";
  B := Parent(x);
  x1, x2 := Explode(x`vec);
  y1, y2 := Explode(y`vec);
  delta := B`delta;
  sigma := B`sigma;
  z := [x1*y1 + delta*sigma(y2)*x2, y2*x1+x2*sigma(y1)];
  return B!z;
end intrinsic;

intrinsic Conjugate(x::AlgCDElt) -> AlgCDElt
{.}
  B := Parent(x);
  x1, x2 := Explode(x`vec);
  sigma := B`sigma;
  return B![sigma(x1), -x2];
end intrinsic;	  

intrinsic '!'(F::Fld, x::AlgCDElt) -> FldElt
{.}
  B := Parent(x);
  require F eq BaseField(B`A) : "Illegal coercion";
  x1, x2 := Explode(x`vec);
  require x2 eq 0 : "Illegal coercion";
  return F!x1;
end intrinsic;

intrinsic Norm(x::AlgCDElt) -> FldElt
{.}
  B := Parent(x);
  return BaseField(B`A)!(x * Conjugate(x));
end intrinsic;

intrinsic Parent(x::AlgCDElt) -> AlgCD
{.}
  return x`parent;
end intrinsic;

intrinsic 'eq'(B1::AlgCD, B2::AlgCD) -> BoolElt
{.}
  return (B1`A eq B2`A) and (B1`delta eq B2`delta);
end intrinsic;

intrinsic trd(x::AlgCDElt, y::AlgCDElt) -> FldElt
{.}
  require Parent(x) eq Parent(y) : "Arguments are not compatible";	  
  return BaseField(Parent(x)`A)!(x*Conjugate(y) + y * Conjugate(x));	  
end intrinsic;

intrinsic IsCommutative(B::AlgCD) -> BoolElt
{.}
  return IsField(B`A);
end intrinsic;

intrinsic IsAssociative(B::AlgCD) -> BoolElt
{.}
  return IsCommutative(B`A);
end intrinsic;

intrinsic IsAlternative(B::AlgCD) -> BoolElt
{.}
  return IsAssociative(B`A);
end intrinsic;

intrinsic Vector(b::AlgCDElt) -> ModTupFldElt
{.}
  return Vector(Eltseq(b));
end intrinsic;

intrinsic Eltseq(b::AlgCDElt) -> SeqEnum
{.}
  return &cat[Eltseq(x) : x in b`vec];
end intrinsic;

intrinsic 'in'(b::AlgCDElt, B::AlgCD) -> BoolElt
{.}
  return Parent(b) eq B;
end intrinsic;

intrinsic Algebra(B::AlgCD) -> AlgGen
{Return an algebra structure in Magma.}
  b := Basis(B);
  mat_b := Matrix([Vector(x) : x in b]);
  mult_table := &cat&cat[[ Eltseq(Solution(mat_b, Vector(b[i]*b[j])))
			   : j in [1..#b]] : i in [1..#b]];
  A := B`A;
  B_alg := Algebra<BaseField(A), #b | mult_table>;
  d := Dimension(A);
  // TODO : The inverse map doesn't work for some reason...
  B_map := map<B_alg -> B | b :-> [Eltseq(b)[1..d], Eltseq(b)[d+1..2*d]], x :-> Eltseq(Vector(x)) >;
  return B_alg, B_map;
end intrinsic;  

intrinsic Dimension(B::AlgCD) -> RngIntElt
{.}
  return #Basis(B);
end intrinsic;

intrinsic SubConstructor(B::AlgCD, t::.) -> AlgCD, Map
{Return the subalgebra of B generated by elements of the tuple t}
  // This corresponds to the constructor call sub<X | r1, r2, ..., rn>
  // t is ALWAYS a tuple of the form <r1, r2, ..., rn>
  // Code: do tests on the elements in t to see whether valid and then
  //       set S to the substructure of T generated by r1, r2, ..., rn
  // Use standard require statements for error checking
  // Possibly use "t := Flat(t);" to make it easy to loop over t if
  //     any of the ri are sequences
  B_alg, iota_B := Algebra(B);
  S_alg, iota_S := sub<B_alg | [Eltseq(Vector(x)) : x in t] >;
  S := New(AlgCD);
  S`A := B`A;
  S`delta := B`delta;
  S`sigma := B`sigma;
  S`basis := [S!(iota_B(iota_S(b))) : b in Basis(S_alg)];
  S_map := map<S -> B | s :-> B!s>;
  S`embedding := S_map;
  S`ambient := B;
  return S, S_map;
end intrinsic;

intrinsic Perp(S::AlgCD) -> SeqEnum[AlgCDElt]
{Returns a basis for the submodule perpendicular to S.}
  B := Ambient(S);
  iota := S`embedding;
  b := Matrix([Vector(x) : x in Basis(B)]);
  Q := Matrix([ [Norm(x+y) - Norm(x) - Norm(y) : y in Basis(B)] : x in Basis(B)]);
  s := Matrix([Vector(iota(x)) : x in Basis(S)]);
  s := Solution(b, s);
  ker := Kernel(Q * Transpose(s));
  d := Dimension(B`A);
  return [B | [Eltseq(v)[1..d], Eltseq(v)[d+1..2*d]] : v in Basis(ker)];
end intrinsic;

// the alternating form
intrinsic Sx(x::AlgCDElt, y::AlgCDElt, z::AlgCDElt) -> FldElt
{.}
  return trd(x*y, z);
end intrinsic;

// The Hermitian form on Perp(A_x)
intrinsic Hx(x::AlgCDElt, y::AlgCDElt, z::AlgCDElt) -> FldElt
{.}
  return 1/2*trd(y,z)+1/2*trd(x*y,z)/Norm(x)*Conjugate(x);
end intrinsic;

// alternating semilinear map
intrinsic Pix(x::AlgCDElt, y::AlgCDElt, z::AlgCDElt) -> FldElt
{.}
  return 1/2*(y*z - z*y - Hx(x, y*z - z*y, Parent(x)!1));	  
end intrinsic;

// The trilinear map
intrinsic Tx(x::AlgCDElt, a::AlgCDElt, b::AlgCDElt, c::AlgCDElt) -> FldElt
{.}
  return Hx(x, c, Pix(x,a,b));
end intrinsic;

function is_order(gens)
    coeffs := Matrix([Vector(g) : g in gens]);
    lat := Lattice(coeffs);

    for i in [1..#gens] do
	for j in [1..#gens] do
	    g := gens[1]*gens[2];
	    v := Vector(g);
	    if v notin lat then return false; end if;
	end for;
    end for;

    return true;
end function;

/* Last commands - using GroupOfLieType to regain the quadratic form

G := GroupOfLieType(RootDatum("G2"), Rationals());
std_rep := StandardRepresentation(G);
G2 := sub<GL(7, Rationals()) | [std_rep(x) : x in AlgebraicGenerators(G)]>;
W := WeylGroup(RootDatum(G));
R := RootDatum(G);
g2, G_adj := LieAlgebra(G);
d := Dimension(R);
n := Rank(R);
N := #Roots(R) div 2;

// Following the construction in [FH] p. 354 to describe the standard representation of g_2 

v4 := HighestWeightVectors(std_rep)[1];

// choosing a "random" prime to generate a torus element

p := 97;
t := elt<G | Vector([p,1])>;
alpha := Roots(R);
beta := alpha[N+1..2*N];
alpha := alpha[1..N];
h := CartanSubalgebra(g2);
s := elt<G | Vector([1,p])>;

// Generating the standard basis of the Lie algebra by looking at the torus action on the adjoint representation
// Following [FH] p. 340

X1 := g2!Basis(Kernel(Matrix(G_adj(s))-1) meet Kernel(Matrix(G_adj(t)) - p))[1];
Y1 := g2!Basis(Kernel(Matrix(G_adj(s))-1) meet Kernel(Matrix(G_adj(t)) - p^(-1)))[1];
X2 := g2!Basis(Kernel(Matrix(G_adj(t))-1) meet Kernel(Matrix(G_adj(s)) - p))[1];
Y2 := g2!Basis(Kernel(Matrix(G_adj(t))-1) meet Kernel(Matrix(G_adj(s)) - p^(-1)))[1];
H1 := LieBracket(X1, Y1);
H2 := LieBracket(X2, Y2);

// Renormalize Y1, Y2 such that [H1, X1] = 2X1 (alpha1(H1) = 2) and [H2, X2] = 2X2

ratio1 := Solution(X1, LieBracket(H1, X1))[1,1];
ratio2 := Solution(X2, LieBracket(H2, X2))[1,1];
Y1 *:= 2/ratio1;
Y2 *:= 2/ratio2;
H1 := LieBracket(X1, Y1);
H2 := LieBracket(X2, Y2);

// making sure that worked...

assert Solution(X1, LieBracket(H1, X1))[1,1] eq 2;
assert Solution(X2, LieBracket(H2, X2))[1,1] eq 2;

// and that math is consistent

assert Solution(Y2, LieBracket(H2, Y2))[1,1] eq -2;
assert Solution(Y1, LieBracket(H1, Y1))[1,1] eq -2;

// making sure the alphas are indexed as in [FH]. 

assert alpha[3] eq alpha[1] + alpha[2];
assert alpha[4] eq alpha[1] + alpha[3];
assert alpha[5] eq alpha[1] + alpha[4];
assert alpha[6] eq alpha[2] + alpha[5];

// Creating the rest of the generators

X3 := LieBracket(X1, X2);
X4 := LieBracket(X1, X3);
X5 := LieBracket(X1, X4);
X6 := LieBracket(X2, X5);
Y3 := LieBracket(Y1, Y2);
Y4 := LieBracket(Y1, Y3);
Y5 := LieBracket(Y1, Y4);
Y6 := LieBracket(Y2, Y5);

X := [X1, X2, X3, X4, X5, X6];
Y := [Y1, Y2, Y3, Y4, Y5, Y6];

// basis := [H1, H2, X1, X2, X3, X4, X5, X6, Y1, Y2, Y3, Y4, Y5, Y6];

not_root_pairs := [<i,j> : i,j in [1..6] | (i lt j) and alpha[i] + alpha[j] notin Roots(R)];
assert &and[LieBracket(X[p[1]], X[p[2]]) eq 0 : p in not_root_pairs];
assert &and[LieBracket(Y[p[1]], Y[p[2]]) eq 0 : p in not_root_pairs];
not_root_pairs2 := [<i,j> : i,j in [1..6] | alpha[i] + beta[j] notin Roots(R) and alpha[i] + beta[j] ne 0];
assert &and[LieBracket(X[p[1]], Y[p[2]]) eq 0 : p in not_root_pairs2];

basis := [H1, H2] cat &cat[[X[i], Y[i]] : i in [1..6]];

// verifying table at bottom of p. 343
assert [Solution(b, LieBracket(H1, b))[1,1] : b in basis] eq [ 0, 0, 2, -2, -3, 3, -1, 1, 1, -1, 3, -3, 0, 0 ];
assert [Solution(b, LieBracket(H2, b))[1,1] : b in basis] eq [ 0, 0, -1, 1, 2, -2, 1, -1, 0, 0, -1, 1, 1, -1 ];

// verifying table at bottom of p. 344
assert [LieBracket(X1, b) : b in basis[4..#basis]] eq [g2 | H1, X3, 0, X4, 3*Y2, X5, 4*Y3, 0, 3*Y4, 0, 0];
assert [LieBracket(Y1, b) : b in basis[5..#basis]] eq [g2 | 0, Y3, 3*X2, Y4, 4*X3, Y5, 3*X4, 0, 0, 0];
assert [LieBracket(X2, b) : b in basis[6..#basis]] eq [g2 | H2, 0, -Y1, 0, 0, X6, 0, 0, Y5];
assert [LieBracket(Y2, b) : b in basis[7..#basis]] eq [g2 | -X1, 0, 0, 0, 0, Y6, X5, 0];

// verifying the rest of the multiplication table (p. 345)
assert [LieBracket(X3, b) : b in basis[8..#basis]] eq [g2 | -H1-3*H2, -X6, 4*Y1, 0, 0, 0, 3*Y4];
assert [LieBracket(Y3, b) : b in basis[9..#basis]] eq [g2 | 4*X1, -Y6, 0, 0, 3*X4, 0];
assert [LieBracket(X4, b) : b in basis[10..#basis]] eq [g2 | 8*H1 + 12*H2, 0, -12*Y1, 0, 12*Y3];
assert [LieBracket(Y4, b) : b in basis[11..#basis]] eq [g2 | -12*X1, 0, 12*X3, 0];
assert [LieBracket(X5, b) : b in basis[12..#basis]] eq [g2 | -36*H1-36*H2, 0, 36*Y2];
assert [LieBracket(Y5, b) : b in basis[13..#basis]] eq [g2 | 36*X2, 0];
assert [LieBracket(X6, b) : b in basis[14..#basis]] eq [g2 | 36*H1 + 72*H2];

// We now perform the modifications suggested at the bottom of p. 345 to make it more symmetric

Y3 := -Y3;
X4 := 1/2*X4;
Y4 := 1/2 * Y4;
X5 := -1/6 * X5;
Y5 := 1/6 * Y5;
X6 := 1/6 * X6;
Y6 := 1/6 * Y6;

X := [X1, X2, X3, X4, X5, X6];
Y := [Y1, Y2, Y3, Y4, Y5, Y6];

basis := [H1, H2] cat &cat[[X[i], Y[i]] : i in [1..6]];

// verifying the multiplication table after changes (p. 346)
assert [Solution(b, LieBracket(H1, b))[1,1] : b in basis] eq [ 0, 0, 2, -2, -3, 3, -1, 1, 1, -1, 3, -3, 0, 0 ];
assert [Solution(b, LieBracket(H2, b))[1,1] : b in basis] eq [ 0, 0, -1, 1, 2, -2, 1, -1, 0, 0, -1, 1, 1, -1 ];
assert [LieBracket(X1, b) : b in basis[4..#basis]] eq [g2 | H1, X3, 0, 2*X4, -3*Y2, -3*X5, -2*Y3, 0, Y4, 0, 0];
assert [LieBracket(Y1, b) : b in basis[5..#basis]] eq [g2 | 0, -Y3, 3*X2, -2*Y4, 2*X3, 3*Y5, -X4, 0, 0, 0];
assert [LieBracket(X2, b) : b in basis[6..#basis]] eq [g2 | H2, 0, Y1, 0, 0, -X6, 0, 0, Y5];
assert [LieBracket(Y2, b) : b in basis[7..#basis]] eq [g2 | -X1, 0, 0, 0, 0, Y6, -X5, 0];
assert [LieBracket(X3, b) : b in basis[8..#basis]] eq [g2 | H1+3*H2, -3*X6, 2*Y1, 0, 0, 0, Y4];
assert [LieBracket(Y3, b) : b in basis[9..#basis]] eq [g2 | -2*X1, 3*Y6, 0, 0, -X4, 0];
assert [LieBracket(X4, b) : b in basis[10..#basis]] eq [g2 | 2*H1 + 3*H2, 0, -Y1, 0, -Y3];
assert [LieBracket(Y4, b) : b in basis[11..#basis]] eq [g2 | X1, 0, X3, 0];
assert [LieBracket(X5, b) : b in basis[12..#basis]] eq [g2 | H1+H2, 0, -Y2];
assert [LieBracket(Y5, b) : b in basis[13..#basis]] eq [g2 | X2, 0];
assert [LieBracket(X6, b) : b in basis[14..#basis]] eq [g2 | H1 + 2*H2];

// Creating the elements H_i = [X_i, Y_i]

H3 := H1 + 3*H2;
H4 := 2*H1 + 3*H2;
H5 := H1 + H2;
H6 := H1 + 2*H2;

H := [H1, H2, H3, H4, H5, H6];

assert &and[H[i] eq LieBracket(X[i], Y[i]) : i in [1..6]];
assert &and[2*X[i] eq LieBracket(H[i], X[i]) : i in [1..6]];
assert &and[-2*Y[i] eq LieBracket(H[i], Y[i]) : i in [1..6]];

// constructing the subrepresentations isomorphic to sl_3, the standard representation and its dual.
g0_basis := [H5, H2, X5, Y5, X2, Y2, X6, Y6];
W_basis := [X4, Y1, Y3];
W_star_basis := [Y4, X1, X3];

// Now that we have the Lie algebra, we can act on elements of the standard representation.
// We get back to p. 354
std_rep_lie_alg := StandardRepresentation(g2);
v3 := v4 * std_rep_lie_alg(Y1);
v1 := -v3 * std_rep_lie_alg(Y2);
u := v1 * std_rep_lie_alg(Y1);
w1 := 1/2*u*std_rep_lie_alg(Y1);
w3 := w1*std_rep_lie_alg(Y2);
w4 := -Y1*std_rep_lie_alg(w3);
w4 := -w3*std_rep_lie_alg(Y1);

// Could not find a way to consider the symmetric square of the standard representation, so
// fell back to using HighestWeightModule

V := HighestWeightModule(g2, [1,0]);
dimV := Dimension(V);
sym2V, phi := SymmetricPower(V, 2);
irreds, embeddings := DirectSumDecomposition(sym2V);
triv := DirectSumDecomposition(sym2V)[1];
fixed_vec := sym2V!(triv.1);
mat := Matrix(&cat[[phi(Basis(V)[i], Basis(V)[j]) : j in [i..dimV]] : i in [1..dimV]]);
idxs := &cat[[[i,j] : j in [i..dimV]] : i in [1..dimV]];
sol := Solution(mat, fixed_vec);
assert Eltseq(sol) eq Eltseq(&+[sol[i] * phi(Basis(V)[idxs[i][1]], Basis(V)[idxs[i][2]]) : i in [1..#idxs]]);

// constructing the corresponding quadratic form

Q := ZeroMatrix(Rationals(),7);
for i in [1..#idxs] do
  Q[idxs[i][1], idxs[i][2]] +:= sol[i];
  Q[idxs[i][2], idxs[i][1]] +:= sol[i];
end for;

Transpose(std_rep(x2_1))*Q*std_rep(x2_1);
x2_1;
std_rep;
Transpose(x2_1) * Q * x2_1;
V;
V.1;
H1*V.1;
V.1 * H1;;
V * std_rep_lie_alg(H1);
V.1 * std_rep_lie_alg(H1);
(V.1 * std_rep_lie_alg(H1))*Q;
((V.1 * std_rep_lie_alg(H1))*Q, V.1 * std_rep_lie_alg(H1));
(V.1 * std_rep_lie_alg(H1))*Q;
vec := V.1 * std_rep_lie_alg;
vec := V.1 * std_rep_lie_alg(H1);
vec;
(vec * Q, vec);
Vector(vec);
vec := Vector(V.1 * std_rep_lie_alg(H1));
(vec * Q, vec);
vecs := [Vector(b * std_rep_lie_alg(H1)) : b in Basis(V)];
Matrix([[(vecs[i] * Q, vecs[j]): j in [1..7]] : i in [1..7]]);
orig_vecs := [Vector(b) : b in Basis(V)];
Matrix([[(orig_vecs[i] * Q, orig_vecs[j]): j in [1..7]] : i in [1..7]]);
V.1;
H1;
V psi := HighestWeightModule(g2, [1,0]);
V, psi := HighestWeightModule(g2, [1,0]);
g2.1 * V.1;
C := CanonicalBasis(V);
ModuleWithBasis(V);
V;
ActionMatrix(V, g2.1);
V.1 * Transpose(ActionMatrix(V, H1));
V.1 * std_rep_lie_alg(H1);
std_rep_lie_alg(H1) eq Transpose(ActionMatrix(V, H1));

w0 := elt< G | 6 > * elt <G | Vector([p^(Integers()!i) : i in Eltseq(alpha0_dual)])>;
*/

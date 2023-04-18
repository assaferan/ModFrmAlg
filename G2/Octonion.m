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
      if #v ne 2 then return false, "Degree is incompatible"; end if;
      is_A1, v1 := IsCoercible(B`A, v[1]);
      is_A2, v2 := IsCoercible(B`A, v[2]);
      if (not is_A1) or (not is_A2) then return false, "Arguments are not compatible"; end if;
      b := New(AlgCDElt);
      b`parent := B;
      b`vec := [v1, v2];
      return true, b;
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
  return Vector(&cat[Eltseq(x) : x in b`vec]);
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

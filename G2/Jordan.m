// Constructing the exceptinal Jordan algebra

declare type ExcJord[ExcJordElt];
declare attributes ExcJord :
		   // the Cayley-Dickson algebra
		   O;

declare attributes ExcJordElt :
		   // the Exceptional Jordan algebra it belongs to
		   parent,
		   // the 3x3 "matrix" representing the element
	mat;

declare type ExcJordDual[ExcJordDualElt];

declare attributes ExcJordDual:
	     // the original algebra
	     J;

// Todo - can represent these better by saving the action on an F-basis
declare attributes ExcJordDualElt :
		   // the dual of the Exceptional Jordan algebra it belongs to
		   parent,
	// a vector representing the functional in the dual vector space
	vec;

intrinsic ExceptionalJordan(O::AlgCD) -> ExcJord
{Create the Exceptional Jordan algebra associated to the Cayley-Dickson algebra O.}
  J := New(ExcJord);
  J`O := O;
  return J;
end intrinsic;

intrinsic Dual(J::ExcJord) -> ExcJordDual
{Creates the dual of the Exceptional Jordan algebra J.}
  Jdual := New(ExcJordDual);
  Jdual`J := J;
  return Jdual;
end intrinsic;

intrinsic Algebra(J::ExcJord) -> AlgCD
{.}
  return J`O;
end intrinsic;

intrinsic Algebra(Jdual::ExcJordDual) -> ExcJord
{.}
  return Jdual`J;
end intrinsic;

intrinsic 'eq'(J1::ExcJord, J2::ExcJord) -> BoolElt
{.}
  return (J1`O eq J2`O);
end intrinsic;

intrinsic 'eq'(J1::ExcJordDual, J2::ExcJordDual) -> BoolElt
{.}
  return (J1`J eq J2`J);
end intrinsic;

intrinsic Print(J::ExcJord, level::MonStgElt)
{.}
  if (level eq "Magma") then
      printf "ExceptionalJordan(%m)", J`O;
      return;
  end if;
  printf "Exceptional Jordan Algebra (the Albert algebra) over %o", J`O;
  return;
end intrinsic;

intrinsic Print(Jdual::ExcJordDual, level::MonStgElt)
{.}
  if (level eq "Magma") then
      printf "Dual(%m)", Jdual`J;
      return;
  end if;
  printf "Dual of %o", Jdual`J;
  return;
end intrinsic;

intrinsic IsCoercible(J::ExcJord, X::.) -> BoolElt, .
{Coerce X into J if possible.}
   if Type(X) eq ExcJordElt then	
       if Parent(X) eq J then
	   return true, X;
       end if;
       JJ := Parent(X);
       if (JJ`O eq J`O) then
	   return true, J!(X`mat);
       end if;
       return false, "Arguments are not compatible";
   end if;
   if ISA(Type(X), SeqEnum) or ISA(Type(X), List) then
       if #X eq 2 then // of the form X = [ c, x ]
	   c, x := Explode(X);
	   if Type(c) ne SeqEnum then
	       c := Eltseq(c);
	   end if;
	   if Type(x) ne SeqEnum then
	       x := Eltseq(x);
	   end if;
	   if (#c ne 3) or (#x ne 3) then
	       return false, "Arguments are not compatible";
	   end if;
	   F := BaseField(J`O);
	   c_scalars := [];
	   x_elts := [];
	   for i in [1..3] do
	       is_scalar, coeff := IsCoercible(F, c[i]);
	       if not is_scalar then
		   return false, "Arguments are not compatible";
	       end if;
	       Append(~c_scalars, coeff);
	       is_O, elt := IsCoercible(J`O, x[i]);
	       if not is_O then
		   return false, "Arguments are not compatible";
	       end if;
	       Append(~x_elts, elt);
	   end for;
	   c := [(J`O)!cc : cc in c_scalars];
	   x := x_elts;
	   xbar := [Conjugate(xx) : xx in x];
	   X_J := New(ExcJordElt);
	   X_J`parent := J;
	   X_J`mat := [[c[1], x[3], xbar[2]], [xbar[3], c[2], x[1]], [x[2], xbar[1], c[3]]];
	   return true, X_J;
       elif #X eq 3 then // of the form of a 3x3 matrix
	   c := [];
	   x := [];
	   for i in [1..3] do
	       if (#X[i] ne 3) then
		   return false, "Arguments are not compatible";
	       end if;
	       for j in [1..3] do
		   base := (j eq i) select BaseField(J`O) else J`O;
		   is_good, elt := IsCoercible(base, X[i][j]);
		   if not is_good then
		       return false, "Arguments are not compatible";
		   end if;
		   if (i eq j) then
		       Append(~c, elt);
		   else
		       Append(~x, elt);
		   end if;
	       end for;
	   end for;
	   c := [(J`O)!cc : cc in c_scalars];
	   x := x_elts;
	   xbar := [Conjugate(xx) : xx in x];
	   X_J := New(ExcJordElt);
	   X_J`parent := J;
	   X_J`mat := [[c[1], x[3], xbar[2]], [xbar[3], c[2], x[1]], [x[2], xbar[1], c[3]]];
	   return true, X_J;
       else
	   return false, "Degree is incompatible";
       end if;
  end if;
  is_F, X_F := IsCoercible(BaseField(J`O), X); // if it is central
  if is_F then
      return true, J![[X_F, X_F, X_F],[0,0,0]];
  end if;
  return false, "Illegal coercion";
end intrinsic;

intrinsic IsCoercible(Jdual::ExcJordDual, f::.) -> BoolElt, .
{Coerce f into Jdual if possible.}
    V, mV := VectorSpace(Jdual`J);
    if ISA(Type(f), UserProgram) then
	phi := New(ExcJordDualElt);
	phi`parent := Jdual;
	phi`vec := Vector([f((V.i)@@mV) : i in [1..27]]);
	return true, phi;
    end if;
    is_vec, v := IsCoercible(V, f);
    if is_vec then
	phi := New(ExcJordDualElt);
	phi`parent := Jdual;
	phi`vec := v;
	return true, phi;
    end if;
    return false, "Illegal coercion";
end intrinsic;

intrinsic Print(X::ExcJordElt, level::MonStgElt)
{.}
  if (level eq "Magma") then
      printf "%m!%m", Parent(X), X`mat;
      return;
  end if;
  for i in [1..3] do
      printf "[";  
      for j in [1..3] do
	  if (i eq j) then
	      printf "%o", BaseField(Algebra(Parent(X)))!(X`mat[i][j]);
	  else
	      printf "%o", X`mat[i][j];
	  end if;
	  if (j ne 3) then
	      printf " ";
	  end if;
      end for;
      printf "]";
      if (i ne 3) then
	  printf "\n";
      end if;
  end for;
  return;
end intrinsic;

intrinsic Parent(X::ExcJordElt) -> ExcJord
{.}
  return X`parent;	  
end intrinsic;	  

intrinsic Diagonal(X::ExcJordElt) -> SeqEnum[FldElt]
{.}
    J := Parent(X);
    F := BaseField(Algebra(J));
    return [F!(X`mat[i][i]) : i in [1..3]];
end intrinsic;	  

intrinsic Vector(X::ExcJordElt) -> SeqEnum[AlgCDElt]
{.}
  return [X`mat[2][3], X`mat[3][1], X`mat[1][2]];
end intrinsic;

intrinsic Norm(X::ExcJordElt) -> FldElt
{.}
  c := Diagonal(X);
  x := Vector(X);
  return &*c - &+[c[i]*Norm(x[i]) : i in [1..3]] + Trilinear(x[1],x[2],x[3]);
end intrinsic;

intrinsic Trace(X::ExcJordElt) -> FldElt
{.}
  c := Diagonal(X);
  return &+c;
end intrinsic;  

intrinsic '+'(X::ExcJordElt, Y::ExcJordElt) -> ExcJordElt
{.}
  require Parent(X) eq Parent(Y) : "both elements must be in the same algebra";
  Z := New(ExcJordElt);
  Z`parent := Parent(X);
  Z`mat := [[X`mat[i][j] + Y`mat[i][j] : j in [1..3]] : i in [1..3]];
  return Z;
end intrinsic;

intrinsic '+'(X::ExcJordElt, a::FldElt) -> ExcJordElt
{.}
  return X + Parent(X)!a;
end intrinsic;
  

intrinsic '-'(X::ExcJordElt, Y::ExcJordElt) -> ExcJordElt
{.}
  require Parent(X) eq Parent(Y) : "both elements must be in the same algebra";
  Z := New(ExcJordElt);
  Z`parent := Parent(X);
  Z`mat := [[X`mat[i][j] - Y`mat[i][j] : j in [1..3]] : i in [1..3]];
  return Z;
end intrinsic;

intrinsic '*'(a::FldElt, X::ExcJordElt) -> ExcJordElt
{.}
  F := BaseField(Algebra(Parent(X)));
  is_F, a_F := IsCoercible(F,a);
  require is_F : "scalar must be in the same field";
  Y := New(ExcJordElt);
  Y`parent := Parent(X);
  Y`mat := [[a_F*X`mat[i][j] : j in [1..3]] : i in [1..3]];
  return Y;
end intrinsic;  

intrinsic 'eq'(X::ExcJordElt, Y::ExcJordElt) -> ExcJordElt
{.}
  if Parent(X) ne Parent(Y) then
    return false;
  end if;
  return &and[&and[X`mat[i][j] eq Y`mat[i][j] : j in [1..3]] : i in [1..3]];
end intrinsic;

intrinsic Dot(X::ExcJordElt, Y::ExcJordElt) -> ExcJordElt
{.}
  require Parent(X) eq Parent(Y) : "both elements must be in the same algebra";
  Z := New(ExcJordElt);
  Z`parent := Parent(X);
  XY_mat := [[&+[X`mat[i][k] * Y`mat[k][j] : k in [1..3]] : j in [1..3]] : i in [1..3]];
  YX_mat := [[&+[Y`mat[i][k] * X`mat[k][j] : k in [1..3]] : j in [1..3]] : i in [1..3]];
  Z`mat := [[1/2*(XY_mat[i][j]+YX_mat[i][j]) : j in [1..3]] : i in [1..3]];
  return Z;
end intrinsic;

intrinsic Trilinear(X::ExcJordElt, Y::ExcJordElt, Z::ExcJordElt) -> FldElt
{.}
  return Norm(X+Y+Z)-Norm(X+Y)-Norm(Y+Z)-Norm(Z+X)+Norm(X)+Norm(Y)+Norm(Z);
end intrinsic;

intrinsic Sharp(X::ExcJordElt) -> ExcJordDualElt
{.}
    function eval_X_sharp(Z)
      return 1/2*Trilinear(Z, X, X);
    end function;
    return Dual(Parent(X))!eval_X_sharp;
end intrinsic;

intrinsic Parent(f::ExcJordDualElt) -> ExcJordDual
{.}
  return f`parent;
end intrinsic;

intrinsic Print(f::ExcJordDualElt, level::MonStgElt)
{.}
  if (level eq "Magma") then
      printf "%m!%m", Parent(f), f`vec;
      return;
  end if;
  printf "functional in %o", Parent(f);
  return;
end intrinsic;

intrinsic Evaluate(f::ExcJordDualElt, X::ExcJordElt) -> FldElt
{.}
  V, mV := VectorSpace(Parent(X));
  X_vec := mV(X);
  return (f`vec, X_vec);
end intrinsic;	  

intrinsic '+'(f::ExcJordDualElt, g::ExcJordDualElt) -> ExcJordDualElt
{.}
  require Parent(f) eq Parent(g) : "both elements must be in the same algebra";
  h := New(ExcJordDualElt);
  h`parent := Parent(f);
  h`vec := f`vec + g`vec;
  return h;
end intrinsic;

intrinsic '-'(f::ExcJordDualElt, g::ExcJordDualElt) -> ExcJordDualElt
{.}
  require Parent(f) eq Parent(g) : "both elements must be in the same algebra";
  h := New(ExcJordDualElt);
  h`parent := Parent(f);
  h`vec := f`vec - g`vec;
  return h;
end intrinsic;

intrinsic CrossProduct(X::ExcJordElt, Y::ExcJordElt) -> ExcJordDualElt
{.}
  return Sharp(X+Y)-Sharp(X)-Sharp(Y);
end intrinsic;

intrinsic BilinearU(X::ExcJordElt,Y::ExcJordElt,U::ExcJordElt) -> FldElt
{.}
  U_sharp := Sharp(U);
  return Evaluate(U_sharp, X)*Evaluate(U_sharp,Y) - Trilinear(U,X,Y);
end intrinsic;

intrinsic Iota(f::ExcJordDualElt) -> ExcJordElt
{.}
  J := Parent(f)`J;
  O := Algebra(J);
  F := BaseField(O);
  I := J![* [F | 1,1,1], [Eltseq(O!0) : i in [1..3]] *];
  // mat := Matrix([[BilinearU((V.i)@@mV, (V.j)@@mV, I) : j in [1..27]] : i in [1..27]]);
  // The above is a bit slow, so we write explicitly this matrix here
  // Leave the commented out in case we want to modify I
  mat := DiagonalMatrix(F, [1,1,1] cat [2 : i in [1..24]]);
  V, mV := VectorSpace(J);
  vec := Vector([Evaluate(f, (V.i)@@mV) : i in [1..27]]);
  sol := Solution(mat, vec);
  return sol@@mV;
end intrinsic;

intrinsic VectorSpace(J::ExcJord) -> ExcJord
{.}
  W, mW := VectorSpace(J`O);
  U := VectorSpace(BaseField(J`O), 3);
  V, s, p := DirectSum([U, W, W, W]);
  mV := map< J -> V | X :-> s[1](U!Diagonal(X)) + &+[s[i+1](mW(Vector(X)[i])) : i in [1..3]],
	              v :-> [* p[1](v), [p[i+1](v)@@mW : i in [1..3]] *] >;
  return V, mV;
end intrinsic;

intrinsic GenericMinimalPolynomial(X::ExcJordElt) -> RngUPolElt
{.}
  F := BaseField(Algebra(Parent(X)));
  _<x> := PolynomialRing(F);
  return x^3 - Trace(X)*x^2 + 1/2*(Trace(X)^2 - Trace(Dot(X,X)))*x-Norm(X);
end intrinsic;	  

intrinsic InnerCrossProduct(X::ExcJordElt, Y::ExcJordElt) -> ExcJordElt
{.}
  return Dot(X,Y) - 1/2*(Trace(Y)*X + Trace(X)*Y) + 1/2*(Trace(X)*Trace(Y)-Trace(Dot(X,Y)));
end intrinsic;

intrinsic TripleBracket(X::ExcJordElt, Y::ExcJordElt, Z::ExcJordElt) -> ExcJordElt
{.}
  return Dot(Dot(X,Y),Z) - Dot(X, Dot(Y,Z));
end intrinsic;

intrinsic L(X::ExcJordElt) -> AlgMatElt
{.}
  V, mV := VectorSpace(Parent(X));
  L_X := Matrix([mV(Dot(X, (V.i)@@mV)) : i in [1..27]]);
  return L_X;
end intrinsic;	  

intrinsic L(X::ExcJordElt, Y::ExcJordElt) -> AlgMatElt
{.}
  return L(X)*L(Y) - L(Y)*L(X);
end intrinsic;	  


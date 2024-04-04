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
		   // the functional
	func;

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
    if ISA(Type(f), UserProgram) then
	phi := New(ExcJordDualElt);
	phi`parent := Jdual;
	phi`func := f;
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
  return c[1]*c[2]*c[3]-c[1]*Norm(x[1])-c[2]*Norm(x[2])-c[3]*Norm(x[3])+Trilinear(x[1],x[2],x[3]);
end intrinsic;

intrinsic '+'(X::ExcJordElt, Y::ExcJordElt) -> ExcJordElt
{.}
  require Parent(X) eq Parent(Y) : "both elements must be in the same algebra";
  Z := New(ExcJordElt);
  Z`parent := Parent(X);
  Z`mat := [[X`mat[i][j] + Y`mat[i][j] : j in [1..3]] : i in [1..3]];
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
      printf "%m!%m", Parent(f), f`func;
      return;
  end if;
  printf "functional in %o", Parent(f);
  return;
end intrinsic;

intrinsic Evaluate(f::ExcJordDualElt, X::ExcJordElt) -> FldElt
{.}
  return f`func(X);	  
end intrinsic;	  

intrinsic '+'(f::ExcJordDualElt, g::ExcJordDualElt) -> ExcJordDualElt
{.}
  require Parent(f) eq Parent(g) : "both elements must be in the same algebra";
  h := New(ExcJordDualElt);
  h`parent := Parent(f);
  function hfunc(X)
      return f`func(X) + g`func(X);
  end function;
  h`func := hfunc;
  return h;
end intrinsic;

intrinsic '-'(f::ExcJordDualElt, g::ExcJordDualElt) -> ExcJordDualElt
{.}
  require Parent(f) eq Parent(g) : "both elements must be in the same algebra";
  h := New(ExcJordDualElt);
  h`parent := Parent(f);
  function hfunc(X)
      return f`func(X) - g`func(X);
  end function;
  h`func := hfunc;
  return h;
end intrinsic;

intrinsic CrossProduct(X::ExcJordElt, Y::ExcJordElt) -> ExcJordDualElt
{.}
  return Sharp(X+Y)-Sharp(X)-Sharp(Y);
end intrinsic;

intrinsic BilinearU(X::ExcJordElt,Y::ExcJordElt,U::ExcJordElt) -> FldElt
{.}
  U_sharp := Sharp(U);
  return U_sharp(X)*U_sharp(Y) - Trilinear(U,X,Y);
end function;

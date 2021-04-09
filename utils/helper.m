freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
                
                                                                            
   FILE: helper.m (helper and utility functions)

   04/06/21 : Added this documentation, listed intrinsics
 
 ***************************************************************************/

/***********************************************

 03/10/20 : Turned MVM into several intrinsics

***********************************************/

// Here we list the intrinsics that this file defines
// RandomSymmetric(FF::Fld, dim::RngElt) -> Mtrx
// RandomSymmetric(R::RngOrd, dim::RngIntElt, maxNorm::RngIntElt) -> AlgMatElt
// RandomSymmetricInt(Dim::RngElt, Max::RngElt) -> Mtrx
// RandomLattice(Dim::RngElt, Max::RngElt) -> Lat
// QF2(M::AlgMatElt) -> RngMPolElt
// QF2(M::AlgMatElt) -> RngMPolElt
// MVM(M::AlgMatElt, v::ModMatFldElt, alpha::FldAut) -> ModTupFldElt
// MVM(M::AlgMatElt, v::ModTupFldElt, alpha::FldAut) -> ModTupFldElt
// MVM(M::ModMatFldElt, v::ModTupFldElt, alpha::FldAut) -> ModTupFldElt
// MVM(M::AlgMatElt, v::ModMatFldElt) -> ModTupFldElt
// MVM(M::AlgMatElt, v::ModTupFldElt) -> ModTupFldElt

// helper functions

// this is a function useful for time estimate
function get_human_time(t)
  // Minutes.
  mins := Floor(t / 60);

  // Seconds (modulo minutes) remaining.
  secs := Floor(t - mins*60);

  // Hours remaining.
  hours := Floor(mins / 60);
    
  // Minutes (modulo hours).
  mins -:= hours * 60;
    
  // Days.
  days := Floor(hours / 24);
	
  // Hours (modulo days).
  hours -:= days * 24;

  return Sprintf("%od %oh %om %os", days, hours, mins, secs);
end function;

procedure printEstimate(start, ~count, ~elapsed,
			fullCount, comp_str :
			increment := 1,
			printSkip := 1000,
			printOffset := 500,
			timeSkip := 5)

    // Increment counter.
    count +:= increment;

    last_elapsed := elapsed;

    // Elapsed real time.
    new_elapsed := Realtime() - start;
    
    if (count mod printSkip eq printOffset) or
       (new_elapsed gt last_elapsed + timeSkip) then

	// updating last time we printed an estimate
	elapsed := new_elapsed;

	// Seconds per computation.
	t := RealField()!(elapsed / count);

	// Number of computations left to compute.
	remaining := fullCount - count;

	// Estimate time remaining (in seconds).
	estimate := t * remaining;

        est_str := get_human_time(estimate);

        // Display estimate.
	printf "Estimated time remaining for %o: %o\n",
	       comp_str, est_str;

        vprintf AlgebraicModularForms, 1 :
	  "Current memory usage:%o\n", GetMemoryUsage();
    end if;
end procedure;

// This one is because magma doesn't sum an empty set
function my_sum(seq)
  if IsEmpty(seq) then return 0; end if;
  return &+seq;
end function;

// These functions are because sometimes factoring a polynmoial over a number
// field in magma takes unreasonably long time. This worls faster.
// This is based on "Factoring Polynomials over Algebraic Number Fields" by
// S. Landau, SIAM journal on computing 14.1 (1985) : 184-195. 

// my_eval evaluates an element in F[x][y] at the point (x,y)
// (for technical reason this does not work direcly)
function my_eval(f, x, y)
  coeffs := [Evaluate(c, x) : c in Eltseq(f)];
  return &+[coeffs[i]*y^(i-1) : i in [1..#coeffs]];
end function;

// This function performs squarefree factorization 
function my_facAlgExtSqrf(F)
   K<alpha> := BaseRing(F);
   QQ := BaseRing(K); // That should be the rationals, maybe as a number field
   Q_y<y> := PolynomialRing(QQ);
   Q_yx<x> := PolynomialRing(Q_y);
   F_y := Q_yx![Eltseq(c) : c in Eltseq(F)];
   Q_x<x> := PolynomialRing(QQ);
   Q_xy<y> := PolynomialRing(Q_x);
   F_y := my_eval(F_y, y, x);
   mipo := Evaluate(MinimalPolynomial(alpha), y);
   mipo *:= Denominator(mipo);
   shift := 0;
   k := 0;
   count := 0;
   shiftBuf := false;
   f := F_y * Denominator(F_y);
   factors := [];
   tmp := [f];
   repeat
     tmp2 := [];
     for iter in tmp do
       oldF := iter * Denominator(iter);
       if (shift eq 0) then
	 f := oldF;
       else
         f := my_eval(oldF, x-shift*y, y);
         f *:= Denominator(f);
       end if;
       norm := Resultant(mipo, f);
       normFactors := Factorization(norm);
       if (#normFactors ge 1) and (normFactors[1][1] in QQ) then
         normFactors := normFactors[2..#normFactors];
       end if;
       if (#normFactors eq 1) and (normFactors[1][2] eq 1) then
	  Append(~factors, oldF);
          continue;
       end if;
       if #normFactors ge 1 then
         i := normFactors[1];
       end if;
       shiftBuf := false;
       if not ((#normFactors eq 2) and (Degree(i[1]) le Degree(f))) then
         if shift ne 0 then
	   buf := f;
         else
	   buf := oldF;
         end if;
         shiftBuf := true;
       else
         buf := oldF;	   
       end if;
       count := 0;
       for i in normFactors do
	 if shiftBuf then
	   factor := Gcd(buf, i[1]);
         else
	   if shift eq 0 then
      	     factor := Gcd(buf, i[1]);
           else
	     factor := Gcd(buf, (i[1])(x+shift*y));
           end if;
	 end if;
         buf div:= factor;
         if shiftBuf then
	   if shift ne 0 then
	     factor := factor(x+shift*y);
	   end if;
	 end if;
         if (i[2] eq 1) or (Degree(factor) eq 1) then
	   Append(~factors, factor);
         else
           Append(~tmp2, factor);
	 end if;
         if buf in QQ then
	   break;
         end if;
         count +:= 1;
         if ((#normFactors - 1) eq count) then
	   if shiftBuf then
	     if normFactors[#normFactors][2] eq 1 then
	       Append(~factors, my_eval(buf, x+shift*y, y));
             else
	       Append(~tmp2, my_eval(buf, x+shift*y, y));
	     end if;
	   else
	     if normFactors[#normFactors][2] eq 1 then
               Append(~factors, buf);
             else
	       Append(~tmp2, buf);
	     end if;  
	   end if;
           buf := 1;
           break;
	 end if;
       end for;
     end for;
     k +:= 1;
     if (shift eq 0) then
       shift +:= 1;
       k := 1;
     end if;
     if (k eq 2) then
       shift := -shift;
     end if;
     if (k eq 3) then
       shift := -shift;
       shift +:= 1;
       k := 1;
     end if;
     tmp := tmp2;
   until IsEmpty(tmp);
   K_x<x> := Parent(F);
   return [my_eval(f, x, alpha) : f in factors];
end function;

// This is the final factorization function

function my_facAlgExt(f)
  res := [];
  sqfree_fac := SquareFreeFactorization(f);
  for fa in sqfree_fac do
    f, a := Explode(fa);
    f_fac := my_facAlgExtSqrf(f);
    res cat:= [<g, a> : g in f_fac];
  end for;
  return res;
end function;

// Constructs a random symmetric matrix over a specified finite field of a specified dimension.
intrinsic RandomSymmetric(FF::Fld, dim::RngElt) -> Mtrx
{ Generate a random symmetric matrix of dimension Dim over a finite field FF. }
	M := RandomMatrix(FF, dim, dim);
	for j in [2..dim] do
		for k in [1..j-1] do
			M[j,k] := M[k,j];
		end for;
	end for;

	return M;
end intrinsic;

intrinsic RandomSymmetric(R::RngOrd, dim::RngIntElt, maxNorm::RngIntElt) -> AlgMatElt
{ Generates a random symmetric matrix over a ring. }
	M := Zero(MatrixRing(R, dim));

	for i in [1..dim] do
		for j in [i..dim] do
			repeat
				elt := R ! [ Random(-maxNorm,maxNorm) : x in [1..Degree(R)] ];
			until Norm(elt) le maxNorm;
			M[i,j] := elt;
			M[j,i] := elt;
		end for;
	end for;

	return M;
end intrinsic;

intrinsic RandomSymmetricInt(Dim::RngElt, Max::RngElt) -> Mtrx
{ Generates a random matrix over the integers with specified dimension, with maximal absolute entry. }
	R := MatrixRing(Integers(), Dim);

	repeat
		M := Zero(R);

		for i in [1..Dim] do
			num := Random(-Max, Max);
			M[i,i] := 2*num;
			for j in [i+1..Dim] do
				num := Random(-Max, Max);
				M[i,j] := num;
				M[j,i] := num;
			end for;
		end for;
	until IsPositiveDefinite(M);

	return M;
end intrinsic;

intrinsic RandomLattice(Dim::RngElt, Max::RngElt) -> Lat
{ Generates a random lattice with a gram matrix via the RandomSymmetricInt intrinsic. }
	return LatticeWithGram(RandomSymmetricInt(Dim, Max));
end intrinsic;

intrinsic QF2(M::AlgMatElt[RngOrdRes]) -> RngMPolElt
{}
	dim := Nrows(M);
	R := PolynomialRing(BaseRing(M), dim);
	Q := 0;
	for i in [1..dim] do
		for j in [i..dim] do
			Q +:= M[i,j] * R.j * R.i;
		end for;
	end for;
	return Q;
end intrinsic;

intrinsic QF2(M::AlgMatElt[FldFin]) -> RngMPolElt
{ Takes in a symmetric matrix over a field of characteristic 2 and constructs a multinomial corresponding to the quadratic form this matrix represents. }
	// Make sure the matrix is square.
	require Nrows(M) eq Ncols(M): "Supplied matrix must be square.";

	// Make sure the matrix is symmetric.
	require IsSymmetric(M): "Supplied matrix must be symmetric.";

	// Make sure the characteristic of the base ring is 2.
	require Characteristic(BaseRing(M)) eq 2:
		"Supplied matrix must be characteristic 2.";

	Dim := Nrows(M);
	R := PolynomialRing(BaseRing(M), Dim);
	Q := 0;
	for i in [1..Dim] do
		for j in [i..Dim] do
			Q +:= M[i,j] * R.j * R.i;
		end for;
	end for;

	return Q;
end intrinsic;

intrinsic MVM(M::AlgMatElt, v::ModMatFldElt, alpha::FldAut) -> ModTupFldElt
{.}
  return Vector(Transpose(M * Transpose(alpha(v))));
end intrinsic;

intrinsic MVM(M::AlgMatElt, v::ModTupFldElt, alpha::FldAut) -> ModTupFldElt
{.}
  return Vector(Transpose(M * Transpose(alpha(Matrix(v)))));
end intrinsic;

intrinsic MVM(M::ModMatFldElt, v::ModTupFldElt, alpha::FldAut) -> ModTupFldElt
{.}
  return Vector(Transpose(M * Transpose(alpha(Matrix(v)))));
end intrinsic;

intrinsic MVM(M::AlgMatElt, v::ModMatFldElt) -> ModTupFldElt
{.}
  return Vector(Transpose(M * Transpose(v)));
end intrinsic;

intrinsic MVM(M::AlgMatElt, v::ModTupFldElt) -> ModTupFldElt
{.}
  return Vector(Transpose(M * Transpose(Matrix(v))));
end intrinsic;

freeze;

/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J. Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
          
                                                                            
   FILE: linalg.m (Linear Algbera)

   Implementation file for useful linear algebra functions.

   05/29/20 : Modified Decomposition to use also Hecke operators at primes
              dividing the level.

   05/26/20 : Updated since Discriminant can be from now on 2-integral.

   05/08/20 : Added functions for decomposition of the space (future use).

   04/08/20 : Modified to handle finite fields as well.

   04/01/20 : Started preparation to adjust for arbitrary characteristic.
              Not much of a change yet.

   03/26/20 : Added documentation to this file.

   03/26/20 : Fixed bug in Decompose - Optimized Representation only eats 
              absolute fields. (over the rationals)
 
 ***************************************************************************/

// Here are the intrinsics this file defines
// EigenspaceDecomposition(array::Assoc) -> List, SeqEnum
// Decomposition(M::ModFrmAlg, bound::RngIntElt) -> SeqEnum, BoolElt
// Decomposition(M::ModFrmAlg) -> SeqEnum, BoolElt

function Decompose(T, t)
    // The characteristic polynomial of this matrix.
    chi := CharacteristicPolynomial(T);
    
    // Factorization of the characteristic polynomial.
    fs := Factorization(chi);

    // The eigenspaces arising from this matrix.
    spaces := [* *];

    for data in fs do
	// Number field associated to one of the irreducible factors.
	vprintf AlgebraicModularForms, 2:
	    "Working on polynomial of degree %o\n", Degree(data[1]);
	// This started throwing errors when base ring is a FldOrd
	// K := ext< BaseRing(data[1]) | data[1] >;
	K0 := BaseRing(data[1]);
	if Type(K0) eq FldOrd then
	  K := ext< NumberField(K0) | data[1] >;
	else
	  K := ext< K0 | data[1] >;
        end if;

	// The eigenvalue associated to this factor.
	if Degree(data[1]) eq 1 then
	    eig := -Evaluate(data[1], 0);
	else
	    // That fails when K is the fraction field of an order
	    // eig := K.1;
	    eig := GeneratorsSequence(K)[1];
	end if;
	assert Evaluate(data[1], eig) eq 0;

	// If the field K is not the rationals, try to optimize it as
	//  long as the degree of the field isn't too large.
	if Category(K) notin [FldRat,FldFin] and Degree(K) le 8 then
	    // Optimize the number field.
	    K, map := OptimizedRepresentation(AbsoluteField(K));
	    
	    // The eigenvalue in the new field.
	    eig := map(eig);
	end if;
	
	// The identity matrix of the appropriate dimension.
	id := Id(MatrixRing(K, Nrows(t)));
	
	// Promote the ambient matrix to the current number field.
	tt := ChangeRing(t, K);
	

	
	if Characteristic(BaseRing(T)) eq 0 then
	    fT := tt-eig*id;
	else
	    fT := (tt-eig*id)^data[2];
	end if;

	Append(~spaces,
	       < Nullspace(fT), data[2] eq 1 >);
    end for;
    
    return spaces;
end function;

intrinsic EigenspaceDecomposition(array::Assoc : Warning := true)
	-> List, SeqEnum
{ Decompose an array of mutually commuting matrices into their eigenspaces. }
  // Make sure that the associative array is non-empty.
  require #array ne 0: "Associative array must not be empty.";

  // Extract the keys associated to the associative array.
  keys := Keys(array);

  // Put keys into an enumerative array.
  keys := [ x : x in keys ];

  // Extract the full list of matrices.
  Ts := [ array[x] : x in keys ];

  // Verify that all matrices mutually commute.
  require &and[ A*B eq B*A : A,B in Ts ]:
	"Matrices in array do not mutually commute.";

  // List of eigenspaces for the first matrix.
  sp := Decompose(Ts[1], Ts[1]);

  for idx in [2..#Ts] do
      // If all eigenspaces are irreducible, we're done.
      if &and[ data[2] : data in sp ] then break; end if;
      
      // The number of eigenspaces we are starting with.
      num := #sp;
      
      // Keep track of the eigenspaces we'll need to delete.
      delList := [];
      
      for i in [1..num] do
	  // Skip this eigenspace if it is irreducible.
	  if sp[i][2] then continue; end if;
	  
	  // Add the current eigenspace to the delete list.
	  Append(~delList, i);
	  
	  // The current subspace.
	  space := sp[i][1];

	  // something here doesn't look right - maybe it only works in characteristic 0 ?
	  // In any case the resulting matrix T is not the submatrix associated to this subspace
	  
	  
	  // Dimension of this space.
	  dim := Dimension(space);

	  B := BasisMatrix(space);
	  tempT := ChangeRing(Ts[idx], BaseRing(space));
	  T := Matrix(B*tempT*Transpose(B)*(B * Transpose(B))^(-1));
	  
	  
	  // Compute the eigenspaces associated to T.
	  newSpaces := Decompose(T, Ts[idx]);
	  
	  for newSp in newSpaces do
	      // The field over which both spaces live.
	      if Type(BaseRing(space)) eq FldFin then
		  deg := LCM(Degree(BaseRing(space)),
			     Degree(BaseRing(newSp[1])));
		  F := FiniteField(
			       Characteristic(BaseRing(space)), deg);
                  homF := hom<BaseRing(space) -> F | >;
	      else
		  F := CompositeFields(
			       BaseRing(newSp[1]), BaseRing(space))[1];
                  F_space := BaseRing(space);
                  if Type(F_space) eq FldRat then
                    homF := hom<F_space -> F| >;
                  else
                    homs := [hom<F_space -> F | r[1]> :
				r in Roots(DefiningPolynomial(F_space), F)];
		    assert exists(homF){h : h in homs |
		      Dimension(ChangeRing(space, F, h) meet
				ChangeRing(newSp[1], F)) ne 0};
                  end if;
		  
	      end if;
	      
	      // Compute the intersection of these two spaces
	      //  and add it to the list.
	      Append(~sp, < ChangeRing(newSp[1], F)
		     meet ChangeRing(space, F, homF), newSp[2] >);
	  end for;
      end for;

      // Remove the outdated subspaces from last to first.
      sp := [* sp[i] : i in [1..#sp] | not i in delList *];
      
      assert &+[ Dimension(s[1]) * Degree(BaseRing(s[1])) : s in sp ]
	     eq Nrows(Ts[1]) * Degree(BaseRing(Ts[1]));
  end for;

  // Determine whether this decomposition is stll decomposable.
  decomposable := [ i : i in [1..#sp] | not sp[i][2] ];
  
  // Return the eigenspaces.
  sp := [* data[1] : data in sp *];

  // Display a warning if the decomposition is reducible.
  if Warning and #decomposable ne 0 then
      print "WARNING: Eigenspaces not completely decomposed!";
  end if;

  return sp, decomposable;
end intrinsic;

// functions copied (and modified) from ModSym to do decomposition

function MyCharpoly(A, proof)
   assert Nrows(A) gt 0;
   if Type(BaseRing(Parent(A))) eq FldRat then
      return CharacteristicPolynomial(A : Al := "Modular", Proof:=proof);
   end if;
   return CharacteristicPolynomial(A);
end function;

function Restrict(A, x)
   F := BaseRing(Parent(A));
   if Type(x) eq SeqEnum then
      B := Matrix(F, x);
   else
      assert Type(x) in {ModTupRng, ModTupFld};
      if Dimension(x) eq 0 then
         return MatrixAlgebra(F,0)!0;
      end if;
      B := Matrix(F, BasisMatrix(x));
   end if; 
   R := MatrixAlgebra(F, Nrows(B)) ! Solution(B, B*A);
   return R;
end function;

function KernelOn(A, B)
// Suppose B is a basis for an n-dimensional subspace
// of some ambient space and A is an nxn matrix.
// Then A defines a linear transformation of the space
// spanned by B.  This function returns the
// kernel of that transformation.
   if Type(B) eq ModTupFld then
      BM := BasisMatrix(B);
   else
      BM := Matrix(B);
   end if;
   return RowSpace(KernelMatrix(A) * BM);
end function;

function SimpleIrreducibleTest(W,a)

   // a is the exponent of the factor of the charpoly.
   
    if a eq 1 then
	return true;
    end if;
    
    return false;
    
end function;

function W_is_irreducible(M,W,a,random_operator_bound :
			  Estimate := true, Orbits := true,
			  UseLLL := true, LowMemory := false, ThetaPrec := 25)
   /*
   W = subspace of the dual
   a = exponent of factor of the characteristic polynomial.
   */

   irred := SimpleIrreducibleTest(W,a);

   if irred then
      return true;
   end if;

   if random_operator_bound gt 1 then
      if IsVerbose("AlgebraicModularForms") then 
         printf "Trying to prove irreducible using random sum of Hecke operators.\n";
      end if;
      T := &+[Random([-3,-2,-1,1,2,3])*Restrict(HeckeOperator(M,ell :
						Estimate := Estimate,
						Orbits := Orbits,
						UseLLL := UseLLL,
						LowMemory := LowMemory,
						ThetaPrec := ThetaPrec), W) : 
                ell in PrimesUpTo(random_operator_bound, BaseRing(M))];
      f := CharacteristicPolynomial(T);
      if IsVerbose("AlgebraicModularForms") then 
         printf "Charpoly = %o.\n", f;
      end if;
      if IsIrreducible(f) then
         return true;
      end if;
   end if;

   return false;  

end function;

function Decomposition_recurse(M, V, primes, prime_idx, 
                               proof, random_op :
			       UseLLL := true, Estimate := true,
			       Orbits := true, LowMemory := false,
			       ThetaPrec := 25)

   assert Type(M) eq ModFrmAlg;
   assert Type(primes) eq SeqEnum;
   assert Type(proof) eq BoolElt;
   assert Type(random_op) eq BoolElt;

   // Compute the Decomposition of the subspace V of M
   // starting with Tp.
   if Dimension(V) eq 0 then
      return [], true;
   end if;


   if Abs(prime_idx) gt #primes then
     return [V], false;
   end if;

   
   fac := Factorization(ideal<Integers(BaseRing(M))|
			Generators(primes[Abs(prime_idx)])>);
   // if the prime is ramified or inert above 2, at the moment the Hecke Operator
   // is not computed correctly
   if ((#fac eq 1) and (fac[1][2] eq 2)) or ((#fac eq 1) and (fac[1][2] eq 1) and IsEven(Norm(primes[Abs(prime_idx)]))) then
       return Decomposition_recurse(M, V,primes,prime_idx+1,proof,
				    random_op : UseLLL := UseLLL,
						Estimate := Estimate,
						Orbits := Orbits,
						LowMemory := LowMemory,
						ThetaPrec := ThetaPrec);
   end if;

   pR := fac[1][1];

   vprintf AlgebraicModularForms, 1 : "Decomposing space of dimension %o using T_%o.\n", Dimension(V), Norm(pR);
   vprintf AlgebraicModularForms, 2 : "\t\t(will stop at %o)\n",
				      Norm(primes[#primes]);

   hecke_op := prime_idx lt 0 select PlusOperator else HeckeOperator;
   T := Restrict(hecke_op(M, pR : Estimate := Estimate,
			       Orbits := Orbits, UseLLL := UseLLL,
			       LowMemory := LowMemory,
			       ThetaPrec := ThetaPrec), V);
   D := [* *];

   
   if GetVerbose("AlgebraicModularForms") ge 2 then
       t := Cputime();
       printf "Computing characteristic polynomial of T_%o.\n", Norm(pR);
   end if;
   f<x> := MyCharpoly(T,proof);
   if GetVerbose("AlgebraicModularForms") ge 2 then
       f;
       printf "\t\ttime = %o\n", Cputime(t);
       t := Cputime();
       printf "Factoring characteristic polynomial.\n";
   end if;
   FAC := Factorization(f);
   if GetVerbose("AlgebraicModularForms") ge 2 then
       FAC;
       printf "\t\ttime = %o\n", Cputime(t);
   end if;

   is_complete := true;
   for fac in FAC do
       f,a := Explode(fac);
       fa := f^a;
     
       vprintf AlgebraicModularForms, 2: "Cutting out subspace using f(T_%o), where f=%o.\n",Norm(pR), f;
       fT  := Evaluate(fa,T);
       W   := KernelOn(fT,V);

      if Dimension(W) eq 0 then
          error "WARNING: dim W = 0 factor; shouldn't happen.";
      end if;

      if (Characteristic(BaseRing(Weight(M))) eq 0 and
	 W_is_irreducible(M,W,a,random_op select Norm(pR) else 0 :
			  Estimate := Estimate, Orbits := Orbits,
			  UseLLL := UseLLL, LowMemory := LowMemory,
			  ThetaPrec := ThetaPrec)) or (Dimension(W) eq 1) then
         Append(~D,W);
         is_complete_W := true;
      else
	if Abs(prime_idx) lt #primes then
	      q_idx   := Dimension(W) eq Dimension(V) select
			 ((IsEven(Rank(Module(M))) and (prime_idx gt 0) and IsSpecialOrthogonal(M)) select -prime_idx 
			  else Abs(prime_idx) + 1) else 1;
              Sub, is_complete_W  := Decomposition_recurse(M, W, primes, q_idx, 
                                            proof, random_op :
					    UseLLL := UseLLL,
					    Orbits := Orbits,
					    Estimate := Estimate,
					    LowMemory := LowMemory,
					    ThetaPrec := ThetaPrec); 
              for WW in Sub do 
                  Append(~D, WW);
              end for;
          else
              Append(~D,W);
              is_complete_W := false;
          end if;
      end if;
      is_complete and:= is_complete_W;
   end for;
   return D, is_complete;
end function;

procedure SortDecomp(~D)
    dims := [< Dimension(D[i]) * Degree(BaseField(D[i])), i > : i in [1..#D]]; 
    Sort(~dims);
    D := [D[tup[2]] : tup in dims];
end procedure;

intrinsic Decomposition(M::ModFrmAlg, bound::RngIntElt :
			UseLLL := true,
			Orbits := true,
			Estimate := true,
			LowMemory := false,
			ThetaPrec := 25,
			Proof := true,
		        Force := false) -> SeqEnum, BoolElt
{Decomposition of M with respect to the Hecke operators T_p with
p coprime to the level of M and p<= bound. }

   if Dimension(M) eq 0 then
      return [], true;
   end if;

   if Force or (not assigned M`Hecke`decomposition) then   

      RF := recformat <
        bound  : RngIntElt, // bound so far
        decomp : List,   // subspaces of M
        is_complete : BoolElt
      >;

      D := [* VectorSpace(M) *];

      M`Hecke`decomposition := rec < RF | bound := 0,
	decomp := D,
	is_complete := false>;
   end if;

   decomp := (M`Hecke`decomposition)`decomp;
   known  := (M`Hecke`decomposition)`bound;
   is_complete := (M`Hecke`decomposition)`is_complete;
   if bound le known then
      SortDecomp(~decomp);
      return decomp, is_complete;
   end if;

   // refine decomp
   alpha := Involution(AmbientSpace(Module(M)));
   F := FixedField(alpha);

   if (not assigned M`W`weight) or (M`W`weight[1] ne 1) then
       primes := PrimesUpTo(bound, F : coprime_to := Numerator(Norm(Discriminant(Module(M)))));
   else
       primes := PrimesUpTo(bound, F);
   end if;
   prime_idx := [i : i in [1..#primes] | Norm(primes[i]) gt known][1];
   use_LLL := UseLLL and (not IsSpecialOrthogonal(M));
   refined_decomp := [* *];
   is_complete := true;
   for MM in decomp do
       DD, is_complete_MM := Decomposition_recurse(M,MM, primes, prime_idx,
						   Proof, false :
						   UseLLL := use_LLL,
						   Orbits := Orbits,
						   Estimate := Estimate,
						   LowMemory := LowMemory,
						   ThetaPrec := ThetaPrec);
       refined_decomp cat:= DD;
       is_complete and:= is_complete_MM;
   end for;

   (M`Hecke`decomposition)`bound := bound;
   (M`Hecke`decomposition)`decomp := refined_decomp;
   (M`Hecke`decomposition)`is_complete := is_complete;

   SortDecomp(~refined_decomp);
   return refined_decomp, is_complete;
end intrinsic;

intrinsic Decomposition(M::ModFrmAlg :
			UseLLL := true,
			Orbits := true,
			Estimate := true,
			LowMemory := false,
			ThetaPrec := 25,
			Proof := true,
		        Force := false) -> SeqEnum, BoolElt
{Decomposition of M with respect to the Hecke operators T_p with
p coprime to the level of M and p<= bound. }
   bound := 10;
   is_complete := false; 
   while not is_complete do
     D, is_complete := Decomposition(M, bound : UseLLL := UseLLL,
				     Orbits := Orbits,
				     Estimate := Estimate,
				     LowMemory := LowMemory,
				     ThetaPrec := ThetaPrec,
				     Proof := Proof,
				     Force := Force);
     bound *:= 2;
     // in non-zero characteristic we don't have semisimplicity, and the Hecke bound is too large.
     // Right now, we stop at 10
     if (Characteristic(BaseRing(Weight(M))) ne 0) then
	 break;
     end if;
   end while;
   return D;
end intrinsic;

function EigenvectorOfMatrixWithCharpoly(T, f : e := 1)
/* Let T be an nxn matrix over K with irreducible characteristic
 polynomial f.  This function returns an eigenvector for T
 over the extension field K[x]/(f(x)). 
 assaferan : added e to denot exponent, so that T could have as
 a characteristic polynomial a power of an irreducible - f^e
*/

    // This is implemented using a quotient of a polynomial ring
    // because this works generically for any field.
    n  := Degree(f) * e;
    K  := Parent(T[1,1]);
    if n eq 1 then
	return VectorSpace(K,n)![1];
    end if;
   
    vprintf AlgebraicModularForms,1: "Calling EigenvectorOfMatrixWithCharpoly ... ";
    time0_eig := Cputime();

    if Type(K) eq FldRat or ISA(Type(K),FldAlg) then
	L<a> := ext< K | f : DoLinearExtension, Check:=false>;
    else
	// still occurs in the finite characteristic case
	R := PolynomialRing(K);
	L<a> := quo<R | f>;
    end if;
    b    := 1/a;
    c    := [-b*Coefficient(f,0)];
    for i in [1..Degree(f)-1] do
	Append(~c, (c[i] - Coefficient(f,i))*b);
    end for;

    Ln := RSpace(L,n);     // magma is weird in that it can take *way* too long to do this!
                          // (possible thing to optimize)  see remarks in same function 
                          // level1.m in ModFrm package
                          //
                          // This will have changed because we're using number fields now,
                          // not quo's. I think this problem has been fixed for quo's, anyway.  
                          //   --- Steve
    time0 := Cputime();
    
    if Type(K) eq FldRat then
	S := IntegerRing();
	denom := LCM([Denominator(x): x in Eltseq(T)]);
	// "denom:", denom;
	denom_scale := 1/denom;
	T := Matrix(S, denom*T);
    else
	S := L;
	T  := RMatrixSpace(L,n,n)!T;
	denom := 1;
	denom_scale := 1;
    end if;
    if Cputime(time0) gt 1 then "RMatrixSpace coercion", Cputime(time0); end if;

    Ln := RSpace(L, n);
    Sn := RSpace(S, n);
    v  := Sn!0;
    
    repeat
	v[Random(1,n)] +:= 1;
	w  := c[1]*Ln!v;
	vv := v;
	scale := denom_scale;
	// "eigen loop", #c; time
	for i in [2..#c] do 
	    time0 := Cputime();
            vv := vv*T;
	    time1 := Cputime(time0);
            //w +:= c[i]*vv;
            u := Ln!vv;
	    time2 := Cputime(time1);
	    if denom_scale ne 1 then
		e := Eltseq(vv);
		g := GCD(e);
		if g ne 1 then
		    // printf " {GCD %o}", g;
		    vv := Parent(vv)![x div g: x in e];
		    scale *:= g;
		end if;
		u := Ln!vv;
		u := scale*u;
		scale *:= denom_scale;
	    else
		u := Ln!vv;
	    end if;
            w +:= c[i]*u;
	    time3 := Cputime(time0);
	    //printf "  %o", [time1, time3-time1];
	end for;
    until w ne Parent(w)! 0;
   
    vprintf AlgebraicModularForms,1: "%os\n", Cputime(time0_eig);

    return w;
end function;

// get eigenvectors from results of decomposition
// !! TODO - figure out what to do when there are still reducible subspaces (failure of multiplicity one)
function GetEigenvectors(M, D)
    T := M`Hecke`Ts[1];
    keys := [k : k in Keys(T)];
    vecs := [* *];
    is_eigenform := [];
    for d in D do
	p_idx := 0;
	repeat
	    p_idx +:= 1;
	    Tp := T[keys[p_idx]];
	    Td := Restrict(Tp,d);
	    f := CharacteristicPolynomial(Td);
	until (IsIrreducible(f)) or (p_idx ge #keys);
	if IsIrreducible(f) then
	    wd := EigenvectorOfMatrixWithCharpoly(Td, f);
	    w := wd*ChangeRing(BasisMatrix(d), BaseRing(wd));
	    Append(~vecs, w);
	    Append(~is_eigenform, true);
	else
	    for w in Basis(d) do
		Append(~vecs, w);
		Append(~is_eigenform, false);
	    end for;
	end if;
    end for;
    return vecs, is_eigenform;
end function;

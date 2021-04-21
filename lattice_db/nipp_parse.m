/****-*-magma-**************************************************************

                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         

                                                                            
   FILE: nipp_parse.m (file for parsing Nipp database files of quinary lattices)

   04/06/21: Added this documentation and listed the intrinsics.

 
 ***************************************************************************/

// Here are the intrinsics this file defines
// ParseNippFile(fname::MonStgElt) -> SeqEnum
// ParseNippDisc(fname::MonStgElt, d::RngIntElt) -> SeqEnum
// NippToForm(nipp_entry::Rec) -> AlgMatElt
// NippToForms(nipp_entry::Rec) -> AlgMatElt
// TernaryQuadraticForms(d::RngIntElt) -> SeqEnum
// QuinaryQuadraticLattices(d::RngIntElt) -> SeqEnum
// QuinaryQuadraticLattices(table_idx::RngIntElt, idx::RngIntElt) -> SeqEnum, RngIntElt, RngIntElt

freeze;

lattice_RF := recformat< form : SeqEnum,
                         numAut : Integers()>;

latticeGenus_RF := recformat< D : Integers(),
		              genus : Integers(),
		              mass : Rationals(),
		              HasseSym : SeqEnum,
		              lattices : SeqEnum>;

recField_RF := recformat< name : MonStgElt,
                          sep : MonStgElt,
                          offset : Integers(),
                          multiple : BoolElt>;

function parseNextEntry(entry, desc_to_field : multiple := false)
  sep := " ";
  s := Split(entry, sep);
  is_rec := (not IsEmpty(s)) and (s[1] in Keys(desc_to_field));
  if is_rec then
    fld := desc_to_field[s[1]];
    sep := fld`sep;
    offset := fld`offset;
    multiple := fld`multiple;
  else
    offset := 0;
  end if;
  s := Split(entry, sep);
  if multiple then 
    ans := [eval s[j] : j in [offset+1..#s]];
  else
    ans := IsEmpty(s) select "" else eval s[offset+1];
  end if;
  if is_rec then
    return true, ans, fld;
  else
    return false, ans, _;
  end if;
end function;

function parseNextGenus(r_entries, idx, desc_to_field)
  if idx gt #r_entries then
    return 0, _, _;
  end if;
  latticeGen := rec<latticeGenus_RF | >;
  for j in [1..4] do 
    is_rec, ans, fld := parseNextEntry(r_entries[idx+j], desc_to_field);
// assert is_rec;
    if not is_rec then
      return 0, _, _;
    end if;
    latticeGen``(fld`name) := ans;
  end for;
  lattices := [];
  j := 5;
  is_rec, ans, fld := parseNextEntry(r_entries[idx+j], desc_to_field
				   : multiple := true);
  while (not is_rec) and (idx + j lt #r_entries) do
    lattice := rec<lattice_RF | >;
    lattice`form := ans;
    j +:= 1;
    is_rec, ans, fld := parseNextEntry(r_entries[idx+j], desc_to_field);
    assert not is_rec;
    lattice`numAut := ans;
    j +:= 1;
    Append(~lattices, lattice);
    if (idx + j le #r_entries) then
      is_rec, ans, fld := parseNextEntry(r_entries[idx+j], desc_to_field
				       : multiple := true);
    end if;
  end while;
  latticeGen`lattices := lattices;
  return latticeGen, idx + j - 1;
end function;

function initDescDict()
  desc_to_field := AssociativeArray();
  desc_to_field["D="] := rec< recField_RF | name := "D",
    sep := "= ", offset := 1, multiple := false>;
  desc_to_field["GENUS#"] := rec< recField_RF | name := "genus",
    sep := " ", offset := 1, multiple := false>;
  desc_to_field["MASS="] := rec< recField_RF | name := "mass",
    sep := "=", offset := 1, multiple := false>;
  desc_to_field["HASSE"] := rec< recField_RF | name := "HasseSym",
    sep := " ", offset := 3, multiple := true>;
  return desc_to_field;
end function;

intrinsic ParseNippFile(fname::MonStgElt) -> SeqEnum[Rec]
{Parse an entire file from the Nipp database of quinary lattices.}
  r := Read(fname);
  start := Index(r, "D=");
  r := r[start..#r];
  r_entries := Split(r,";\n");
  idx := 0;
  desc_to_field := initDescDict();
  genera := [];
  while (idx lt #r_entries) do
    latGen, idx := parseNextGenus(r_entries, idx, desc_to_field);
    Append(~genera, latGen);
  end while;
  return genera;
end intrinsic;

intrinsic ParseNippDisc(fname::MonStgElt, d::RngIntElt) -> SeqEnum[Rec]
{Extract the records of a certain discrminant from a file in the Nipp database of quinary lattices.}
  r := Read(fname);
  num_str := Sprintf("%o", d);
  blank := &cat[" " : i in [1..5-#num_str]];
  find_str := "D=" cat blank cat num_str;
  start := Index(r, find_str);
  require start ne 0 : Sprintf("No entry with discriminant %o found", d);
    
  r := r[start..#r];
  r_entries := Split(r,";\n");
  idx := 0;
  desc_to_field := initDescDict();
  genera := [];
  latGen, idx := parseNextGenus(r_entries, idx, desc_to_field);
  while (latGen`D eq d) do
    Append(~genera, latGen);
    latGen, idx := parseNextGenus(r_entries, idx, desc_to_field);
  end while;
  return genera;
end intrinsic;

intrinsic NippToForm(nipp_entry::Rec) -> AlgMatElt
{.}
  // We take the first lattice, but it doesn't matter to us
  a := nipp_entry`lattices[1]`form;
  off_diag := [x / 2 : x in a[6..#a]];
  triangular := [j*(j-1) div 2 : j in [1..5]];
  columns := [[]];
  columns cat:= [off_diag[triangular[j]+1..triangular[j+1]] : j in [1..4]];
  a_magma := &cat[columns[i] cat [a[i]] : i in [1..5]];
  return SymmetricMatrix(a_magma);
end intrinsic;

intrinsic NippToForms(nipp_entry::Rec) -> AlgMatElt
{Convert a record in the Nipp database of quinary lattices to a sequence of matrices represting the forms in the genus.}
  forms := [];
  as := [lat`form : lat in nipp_entry`lattices];
  triangular := [j*(j-1) div 2 : j in [1..5]];
  for a in as do
    off_diag := a[6..#a];
    columns := [[]];
    columns cat:= [off_diag[triangular[j]+1..triangular[j+1]] : j in [1..4]];
    a_magma := &cat[columns[i] cat [2*a[i]] : i in [1..5]];
    Append(~forms, SymmetricMatrix(a_magma));
  end for;
  return forms; 
end intrinsic;

// In what follows we have some code to construct positive definite
// ternary quadratic forms of arbitrary discriminant
// This follows the article "Levels of Positive Definite Ternary Quadratic Forms"
// by J. Larry Lehman https://doi.org/10.2307/2153043

// Checking conditions in Lehman Proposition 3
function IsFormReduced(a,b,c,r,s,t)
  // Condition (1)
  if a gt b then return false; end if;
  if b gt c then return false; end if;
  // Condition (2)
  if not (((r gt 0) and (s gt 0) and (t gt 0)) or
	  ((r le 0) and (s le 0) and (t le 0))) then
    return false;
  end if;
  // Condition (3)
  if a lt Abs(t) then return false; end if;
  if a lt Abs(s) then return false; end if;
  if b lt Abs(r) then return false; end if;
  // Condition (4)
  if a+b+r+s+t lt 0 then return false; end if;
  // Condition (5)
  if a eq t and s gt 2*r then return false; end if;
  if a eq s and t gt 2*r then return false; end if;
  if b eq r and t gt 2*s then return false; end if;
  // Condition (6) 
  if a eq -t and s ne 0 then return false; end if;
  if a eq -s and t ne 0 then return false; end if;
  if b eq -r and t ne 0 then return false; end if;
  // Condition (7) 
  if a+b+r+s+t eq 0 and 2*a+2*s+t gt 0 then return false; end if;
  // Condition (8)
  if a eq b and Abs(r) gt Abs(s) then return false; end if;
  if b eq c and Abs(s) gt Abs(t) then return false; end if;
  return true;
end function;

function TernaryFormMatrix(a,b,c,r,s,t)
  return SymmetricMatrix([2*a,t,2*b,s,r,2*c]);
end function;

intrinsic TernaryQuadraticLattices(d::RngIntElt) -> SeqEnum[AlgMatElt]
{Return representatives for all positive definite ternary quadratic forms of discriminant d, up to isometry.}
  forms := [];
  max_a := Floor(Root(d/2, 3));
  cnt := 0;
  for a in [1..max_a] do
    max_b := Floor(Sqrt(d/(2*a)));
    for b in [a..max_b] do
      min_c := Ceiling(Maximum(b, d/(4*a*b)));
      max_c := Floor(d/(2*a*b));
      for c in [min_c..max_c] do
        for r in [-b..0] do
	  for s in [-a..0] do
	    for t in [-a..0] do
	      A := TernaryFormMatrix(a,b,c,r,s,t);
	      disc := Determinant(A)/2;
	      if disc eq d and IsFormReduced(a,b,c,r,s,t) then
		Append(~forms, A);
              end if;
              cnt +:= 1;
	    end for;
          end for;
	end for;
        for r in [1..b] do
	  for s in [1..a] do
	    for t in [1..a] do
	      A := TernaryFormMatrix(a,b,c,r,s,t);
	      disc := Determinant(A)/2;
	      if disc eq d and IsFormReduced(a,b,c,r,s,t) then
		Append(~forms, A);
              end if;
              cnt +:= 1;
	    end for;
          end for;
	end for;
      end for;
    end for;
   end for;
   printf "Checked %o forms.\n", cnt;
   return forms;
end intrinsic;

intrinsic TernaryQuadraticLattice(d::RngIntElt) -> Mtrx
{get a positive definite quadratic lattice.}
  // B<i,j,k> := QuaternionAlgebra(d);
  // This does not make it easy for us to find the square root of -d in the
  // quaternion algebra after constructing it. Therefore we use Ibukiyama's
  // recipe.
  all_primes := [x[1] : x in Factorization(d)];
  primes := [x : x in all_primes | x ne 2]; 
  // a quadratic non-residue suffices here, but this is usually not
  // time consuming.
  if IsOdd(#all_primes) then
    // In this case there is a definite quaternion algebra of discriminant d
    residues := [3] cat [-Integers()!PrimitiveElement(Integers(p)) : p in primes];
    q := CRT(residues, [8] cat primes);
    while not IsPrime(q) do
      q +:= &*([8] cat primes);
    end while;	    
    B<i,j,k> := QuaternionAlgebra(Rationals(), -q, -d);
    assert Discriminant(B) eq d;
  else
    // I'm not sure which quaternion algebra we want here
    // Is it this one?
    B<i,j,k> := QuaternionAlgebra(Rationals(), -1, -d);
  end if;
  // We could also form the maximal order directly from Ibukiyama's recipe
  // if necessary
  O_B := MaximalOrder(B);
  alpha := Basis(O_B);
  x := Basis(B);
  gram := Matrix([[Trace(x[m]*Conjugate(x[n]))
		      : n in [1..4]] : m in [1..4]]);
  basis := Matrix([Eltseq(x) : x in alpha]);
  lat_O := Lattice(basis, gram);
  mat_beta := [Eltseq(x) : x in Basis(Dual(lat_O : Rescale := false))];
  beta0 := [B!b : b in mat_beta];
  mat := [[Trace(alpha[m]*Conjugate(beta0[n])) : n in [1..4]] : m in [1..4]];
  beta := [B!b : b in Rows(Transpose(Matrix(mat))^(-1)*Matrix(mat_beta))];
  assert IsOne(Matrix([[Trace(alpha[m]*Conjugate(beta[n]))
			   : n in [1..4]] : m in [1..4]]));
  Q := Matrix([[Trace((beta[m]*j)*Conjugate(beta[n]*j))
		   : n in [2..4]] : m in [2..4]]);
  assert Determinant(Q) eq 2*d;
  return Q;
end intrinsic;

// Should change this, right now only works for small discs (up to 256)
// and slowly
function get_nipp_idx(disc, nipp)
  return [idx : idx in [1..#nipp] | nipp[idx]`D eq disc][1];
end function;

function get_last_nipp_idx(disc, nipp)
  idxs := [idx : idx in [1..#nipp] | nipp[idx]`D eq disc];
  if IsEmpty(idxs) then return 0; end if;
  return idxs[#idxs];
end function;

function get_nipp_table_idx(disc, nipp_maxs)
  table_idx := 1;
  while nipp_maxs[table_idx+1] lt disc do
      table_idx +:= 1;
      if table_idx ge #nipp_maxs then
	 error "This size of lattices is not yet supported!";
      end if;
  end while;
  return table_idx;
end function;

intrinsic QuinaryQuadraticLattices(d::RngIntElt) -> SeqEnum[SeqEnum[AlgMatElt]]
{Return representatives for all genera of positive definite quinary quadratic forms of discriminant d. Currently uses Nipp database and only works for d up to 513.}
  nipp_maxs := [0,256,270,300,322,345,400,440,480,500,513];
  assert exists(table_idx){i : i in [1..#nipp_maxs-1] | nipp_maxs[i+1] ge d};
  nipp_fname := Sprintf("lattice_db/nipp%o-%o.txt",
			  nipp_maxs[table_idx]+1, nipp_maxs[table_idx+1]);
  nipps := ParseNippDisc(nipp_fname, d);
  return [NippToForms(nipp) : nipp in nipps];
end intrinsic;

intrinsic QuinaryQuadraticLattices(table_idx::RngIntElt,
				   idx::RngIntElt) -> SeqEnum[AlgMatElt],
                                                      RngIntElt, RngIntElt
{Return representatives for all genera of positive definite quinary quadratic forms of discriminant d. Currently uses Nipp database and only works for d up to 513.}
  nipp_maxs := [0,256,270,300,322,345,400,440,480,500,513];
  nipp_fname := Sprintf("lattice_db/nipp%o-%o.txt",
			  nipp_maxs[table_idx]+1, nipp_maxs[table_idx+1]);
  nipps := ParseNippFile(nipp_fname);
  return NippToForms(nipps[idx]), nipps[idx]`D, nipps[idx]`genus;
end intrinsic;

function possible_diagonals(M, k, n)
  if k eq 1 then
    return [[x] : x in [1..Floor(Root(M,n))]];
  end if;
  prefixes := possible_diagonals(M, k-1, n);
  ret := [];
  for prefix in prefixes do
    min_last := prefix[#prefix];
    max_last := Floor(Root(M / &*prefix, n+1-k)); 
    for last in [min_last..max_last] do
      Append(~ret, prefix cat [last]);
    end for;
  end for;
  return ret;
end function;

function prepareMinkowskiInequalities(n)
  aux_reflect := [];
  aux_permute := [];
  aux_sign := [];
  l_table := [CartesianProduct([{1}] cat [{-1,1} : k in [1..j]] cat
			       [{0} : i in [1..n-j-1]]) : j in [1..n-1]];
  if n ge 5 then
    l_table cat:= [CartesianProduct([{1}] cat [{-1,1} : k in [1..j]] cat
				    [{-2,2} : i in [1..n-j-1]]) : j in [3..n-2]];
  end if;
  if n eq 6 then
    Append(~l_table, CartesianProduct([{1}] cat [{-1,1} : k in [1..3]] cat
				      [{-2,2}, {-3,3}]));
    Append(~l_table, CartesianProduct([{1}] cat [{-1,1} : k in [1..3]] cat
				      [{-2,2}, {0}]));
  end if;
  l := &cat [[x : x in ll] : ll in l_table];
  S_n := Sym(n);
  X := GSet(S_n);
  act := Action(X);
  idxs := [<i,j> : i,j in [1..n] | i le j];
  constraints := [];
  for sigma in S_n do
    for ll in l do
      l_sigma := [ll[act(i,sigma^(-1))] : i in [1..n]];
      vec := [0 : i in [1..n*(n+1) div 2]];
      for idx in idxs do
        i := idx[1];
        j := idx[2];
        vec[Position(idxs, <i,j>)] := l_sigma[i]*l_sigma[j];
      end for;
      k := act(1, sigma);
      vec[Position(idxs, <k,k>)] -:= 1;
      Append(~constraints, vec);
      Append(~aux_reflect, <Vector(l_sigma), k>);
    end for;
  end for;
  for i in [1..n-1] do
    vec := [0 : i in [1..n*(n+1) div 2]];
    vec[Position(idxs, <i+1,i+1>)] := 1;
    vec[Position(idxs, <i,i>)] := -1;
    Append(~constraints, vec);
    Append(~aux_permute, [i, i+1]);
    vec := [0 : i in [1..n*(n+1) div 2]];
    vec[Position(idxs, <i,i+1>)] := 1;
    Append(~constraints, vec);
    Append(~aux_sign, i+1);
  end for;
return constraints, aux_reflect, aux_permute, aux_sign;
end function;

// Right now only supports n le 6 !!!
// intrinsic QuadraticLattice(n::RngIntElt, D::RngIntElt) -> AlgMatElt
// {Return a positive-definite quadratic form of dimension n and determinant D using Minkowski's description of the space of reduced forms.}
function QuadraticLattice(n, D)
  // These are Hermite's constants gamma^n for n in [1..8]
  hermite_pow := [1, 4/3, 2, 4, 8, 64/3, 64, 256];
  // here gamma is a lower bound for Hermite's constant
  // i.e. the constant such that gamma*a_{n,n}^n le D
  if n le 8 then
    gamma := Root(hermite_pow[n], n);
  else
    // !!! TODO - there are known lower bounds for
    // Hermite's constant for general n, implement them !!!
    gamma := 1;
  end if;
  // lambda is a lower bound for a constant such that
  // lambda * prod a_{i,i} le D
  lambda := gamma * (4/5)^(1/2*(n-3)*(n-4));
  // !!! - TODO - restrict also by gamma separately
  diags :=  possible_diagonals(D / lambda, n, n);
  
  constraints := prepareMinkowskiInequalities(n);
  idxs := [<i,j> : i,j in [1..n] | i le j];
  ineq_idxs := [idx : idx in idxs | idx[1] ne idx[2]];
  printf "There are %o diagonals.\n", #diags;
  for diag in diags do
    ineqs := [];
    bds := [];
    for v in constraints do
      bd := -&+[v[Position(idxs, <i,i>)]*diag[i] : i in [1..n]];
      ineq := [v[idx] : idx in [1..n*(n+1) div 2] | idxs[idx][1] ne idxs[idx][2]];
      Append(~ineqs, ineq);
      Append(~bds, bd);
    end for;
    bds_uniq := AssociativeArray();
    for i in [1..#bds] do
      ineq := ineqs[i];
      if IsZero(ineq) then continue; end if;
      if not IsDefined(bds_uniq, ineq) then
        bds_uniq[ineq] := bds[i];
      else
        bds_uniq[ineq] := Maximum(bds[i], bds_uniq[ineq]);
      end if;
    end for;
    ineqs := SetToSequence(Keys(bds_uniq));
    bds := [bds_uniq[ineq] : ineq in ineqs];
    ineqs := [LatticeVector(v) : v in ineqs];
    // This is not very efficient - should rethink how to do that
    P := PolyhedronWithInequalities(ineqs, bds);
    printf "Checking %o points.\n", #Points(P);
    for p in Points(P) do
      ordered := [[Eltseq(p)[Position(ineq_idxs, <i,j>)]
		      : i in [1..j-1]] cat [2*diag[j]] : j in [1..n]];
      Q := SymmetricMatrix(&cat ordered);
      // half discriminant for odd ranks
      factor := IsEven(n) select 1 else 2;
      if IsPositiveDefinite(Q) and Determinant(Q) eq factor*D then
        return [Q];
      end if;
    end for;
  end for;
  // something went wrong
  return [];
end function;
// end intrinsic;

function isReduced(vec, constraints)
  for i in [1..#constraints] do
    if (vec, constraints[i]) lt 0 then
      return false, i;
    end if;
  end for;
  return true, _;
end function;

function MinkowskiReduction(A)
  assert IsPositiveDefinite(A);
  B := A;
  n := NumberOfRows(A);
  one := IdentityMatrix(Integers(), n);
  // This could be made in precomputation
  constraints, aux_reflect,
  aux_permute, aux_sign := prepareMinkowskiInequalities(n);
  constraints := [Vector(v) : v in constraints];
  n_reflect := #aux_reflect;
  n_permute := #aux_permute;
  reduced := false;
  while not reduced do
    B_flat := Vector([(i eq j select 1 else 2)*B[i,j] : i,j in [1..n] | i le j]);
    reduced, i := isReduced(B_flat, constraints);
    if not reduced then
      if i le n_reflect then
        l := aux_reflect[i][1];
        k := aux_reflect[i][2];
	e_k := one[k];
        // currently performing small steps - can do the actual reflection
	g := one + Transpose(Matrix(l-e_k))*Matrix(e_k);
      elif i le n_reflect + n_permute then
	i -:= n_reflect;
        g := PermutationMatrix(Integers(), Sym(n)!aux_permute[i]);
      else
        i -:= (n_reflect + n_permute);
        g := one;
        k := aux_sign[i];
        g[k,k] := -1;
      end if;
      B := Transpose(g)*B*g;
    end if;
  end while;
  return B;
end function;

function VoronoiCoordinateBounds(d)
  // !! TODO - check what the real bounds are !!
  return [1 : i in [1..d]];
end function;

function closestLatticeVectorMinkowskiReduced(b, t, gram)
  d := #b + 1;
  one := IdentityMatrix(Rationals(), d);
  e_d := Matrix(Rows(one)[d]);
  diag := DiagonalMatrix(Rationals(), Diagonal(gram)[1..d-1]);
  H_v := diag^(-1)*Submatrix(gram, [1..d-1], [1..d]);
  H := Submatrix(H_v, [1..d-1], [1..d-1]);
  v := Submatrix(H_v, [1..d-1], [d]);
  // This is the precision to which we will want to compute H^(-1)
  // (we don't need it to be exact)
  r := Ceiling(Log(Maximum([1] cat Eltseq(v))));
  y := -H^(-1)*v;
  voronoi := VoronoiCoordinateBounds(d-1);
  x_min := [Ceiling(y[i,1] - voronoi[i]) : i in [1..d-1]];
  x_max := [Floor(y[i,1] + voronoi[i]) : i in [1..d-1]];
  xs := CartesianProduct([[x_min[i]..x_max[i]] : i in [1..d-1]]);
  min_dist := Infinity();
  min_g := one;
  min_x := Vector([0 : i in [1..d-1]]);
  for x in xs do
    xvec := Transpose(Matrix(Rationals(), Vector([x[i] : i in [1..d-1]])));
    g := one - VerticalJoin(xvec*e_d, 0*e_d);
    x_gram := Transpose(g)*gram*g;
    if x_gram[d,d] lt min_dist then
      min_dist := x_gram[d,d];
      min_g := g;
      min_x := xvec;
    end if;
  end for;
  return Transpose(min_x)*Matrix(b), min_g;
end function;

function GreedyReduction(b, gram)
  d := #b;
  one := IdentityMatrix(Rationals(), d);
  mult := one;
  if d eq 1 then return b, one; end if;
  repeat
    perm := [x[2] : x in Sort([<gram[i,i],i> : i in [1..d]])];
    b := [b[i] : i in perm];
    // Is it faster to do SwapRows and SwapCol?
    g := PermutationMatrix(Rationals(), perm);
    gram := Transpose(g)*gram*g;
    mult := mult*g;
    b0, mult0 := GreedyReduction(b[1..d-1], Submatrix(gram, [1..d-1], [1..d-1]));
    g := DirectSum(mult0, Matrix(Rationals(), [[1]]));
    b := b0 cat [b[d]];
    gram := Transpose(g)*gram*g;
    mult := mult*g;
    c, g := closestLatticeVectorMinkowskiReduced(b0, b[d], gram);
    b[d] := Vector(Eltseq(b[d])) - Vector(Eltseq(c));
    gram := Transpose(g)*gram*g;
    mult := mult*g;
  until gram[d,d] ge gram[d-1,d-1];
  return b, mult;
end function;

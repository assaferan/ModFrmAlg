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
  is_rec := s[1] in Keys(desc_to_field);
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
    ans := eval s[offset+1];
  end if;
  if is_rec then
    return true, ans, fld;
  else
    return false, ans, _;
  end if;
end function;

function parseNextGenus(r_entries, idx, desc_to_field)
  latticeGen := rec<latticeGenus_RF | >;
  for j in [1..4] do 
    is_rec, ans, fld := parseNextEntry(r_entries[idx+j], desc_to_field);
    assert is_rec;
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
/*
  start := Index(r, Sprintf("D=  %o;",d));
  if start eq 0 then
    start := Index(r, Sprintf("D=   %o;",d));
  end if;
*/
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
    off_diag := [x / 2 : x in a[6..#a]];
    columns := [[]];
    columns cat:= [off_diag[triangular[j]+1..triangular[j+1]] : j in [1..4]];
    a_magma := &cat[columns[i] cat [a[i]] : i in [1..5]];
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
	    end for;
          end for;
	end for;
      end for;
    end for;
   end for;
   return forms;
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

// Right now only supports n le 6 !!!
intrinsic QuadraticLattice(n::RngIntElt, D::RngIntElt) -> AlgMatElt
{Return a positive-definite quadratic form of dimension n and determinant D using Minkowski's description of the space of reduced forms.}
  // These are Hermite's constants gamma^n for n in [1..8]
  hermite_pow := [1, 4/3, 2, 4, 8, 64/3, 64, 256];
  // here gamma is a lower bound for Hermite's constant
  // i.e. the constant such that gamma*a_{n,n}^n le D
  if n le 8 then
    gamma := Root(hermite_pow, n);
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
  for sigma in S_n do
    for ll in l do
      l_sigma := [ll[act(i,sigma^(-1))] : i in [1..n]];
      vec := [0 : i in [1..n*(n+1) div 2]];
      for idx in idxs do
        i := idx[1];
        j := idx[2];
        c := (i ne j) select 2 else 1;
        vec[Position(idxs, <i,j>)] := c*l_sigma[i]*l_sigma[j];
      end for;
      k := act(1, sigma);
      vec[Position(idxs, <k,k>)] -:= 1;
      Append(~constraints, vec);
    end for;
    for i in [1..n-1] do
      vec := [0 : i in [1..n*(n+1) div 2]];
      vec[Position(idxs, <i+1,i+1>)] := 1;
      vec[Position(idxs, <i,i>)] := -1;
      Append(~constraints, vec);
    end for;
  end for;
  // !! TODO - go over possible values of the diagonal and for each
  // create the proper ineqs and bds
  ineqs := [LatticeVector(v) : v in constraints];
  bds := [0 : i in [1..#ineqs]];
  P := PolyhedronWithInequalities(ineqs, bds);
  for p in Points(P) do
    Q := SymmetricMatrix(p);
    if IsPositiveDefinite(Q) and Determinant(Q) eq D then
      return Q;
    end if;
  end for;	
end intrinsic;

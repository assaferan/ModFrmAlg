/****-*-magma-**************************************************************

                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J. Voight
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
  latticeGen := rec<latticeGenus_RF | >;
  latticeGen`D := 0;

  if idx ge #r_entries then
    return latticeGen, idx;
  end if;
  
  for j in [1..4] do 
    is_rec, ans, fld := parseNextEntry(r_entries[idx+j], desc_to_field);
    if not is_rec then
      return latticeGen, idx + j;
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

intrinsic ParseNippDiscQuaternary(fname::MonStgElt, d::RngIntElt) -> SeqEnum[Rec]
{Extract the records of a certain discrminant from a file in the Nipp database of quaternary lattices.}
  r := Read(fname);
  r_lines := Split(r, "\n");
  split_lines := [Split(line, "\t ") : line in r_lines];
  split_lines_disc := [line : line in split_lines |
		       (#line ne 0) and (eval line[1]) eq d];
  genera := [];
  latGen := rec<latticeGenus_RF | >;
  latGen`D := d;
  latGen`genus := 1;
  latGen`lattices := [];
  num_hasse := #PrimeDivisors(2*d);
  for line in split_lines_disc do
      genus := eval line[2];
      if (genus gt latGen`genus) then
	  Append(~genera, latGen);
	  latGen`genus := genus;
	  latGen`lattices := [];
      end if;
      lattice := rec<lattice_RF | >;
      lattice`form := [eval line[j] : j in [3..12]];
      hasse_chars := [[line[i][j] : j in [1..#line[i]]] : i in [13..#line-4]];
      hasse_strs := [&cat[(x eq "-") select " -" else x : x in hasse_char]
		     : hasse_char in hasse_chars];
      hasse_sym := &cat [[eval(y) : y in Split(hasse_str, " ")] : hasse_str in hasse_strs];
      assert num_hasse eq #hasse_sym;
      latGen`HasseSym := hasse_sym;
      lattice`numAut := eval line[#line-2];
      latGen`mass := (eval line[#line-1])/(eval line[#line]);
      Append(~latGen`lattices, lattice);
  end for;
  Append(~genera, latGen);
  return genera;
end intrinsic;

intrinsic NippToForm(nipp_entry::Rec : Rank := 5) -> AlgMatElt
{Convert an entry from the Nipp database to a symmetric matrix.}
  // We take the first lattice, but it doesn't matter to us
  a := nipp_entry`lattices[1]`form;
  off_diag := a[Rank+1..#a];
  triangular := [j*(j-1) div 2 : j in [1..Rank]];
  columns := [[]];
  columns cat:= [off_diag[triangular[j]+1..triangular[j+1]] : j in [1..Rank-1]];
  a_magma := &cat[columns[i] cat [2*a[i]] : i in [1..Rank]];
  return SymmetricMatrix(a_magma);
end intrinsic;

intrinsic NippToForms(nipp_entry::Rec : Rank := 5) -> AlgMatElt
{Convert a record in the Nipp database of quinary lattices to a sequence of matrices represting the forms in the genus.}
  forms := [];
  as := [lat`form : lat in nipp_entry`lattices];
  triangular := [j*(j-1) div 2 : j in [1..Rank]];
  for a in as do
    off_diag := a[Rank+1..#a];
    columns := [[]];
    columns cat:= [off_diag[triangular[j]+1..triangular[j+1]] : j in [1..Rank-1]];
    a_magma := &cat[columns[i] cat [2*a[i]] : i in [1..Rank]];
    Append(~forms, SymmetricMatrix(a_magma));
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

intrinsic QuaternaryQuadraticLattices(d::RngIntElt) -> SeqEnum[SeqEnum[AlgMatElt]]
{Return representatives for all genera of positive definite quinary quadratic forms of discrimi
nant d. Currently uses Nipp database and only works for d up to 457.}
  //nipp_fname := "lattice_db/nipp_4_4-457.txt";
  //nipps := ParseNippDiscQuaternary(nipp_fname, d);
  nipp_web := "http://www.math.rwth-aachen.de/~Gabriele.Nebe/LATTICES/";
  nipp_maxs := [0, 457, 641, 777, 893, 992, 1080, 1161, 1236, 1308, 1373, 1433, 1492, 1549, 1604, 1656, 1705, 1732];
  table_idx := get_nipp_table_idx(d, nipp_maxs);
  //  nipp_mins := [4, 458, 642, 778, 894, 993, 1081, 1162, 1237, 1309, 1374, 1434, 1493, 1550, 1605, 1657, 1706];
  fname := Sprintf("d%o.html", nipp_maxs[table_idx+1]);
  if table_idx eq 1 then
      fname := "d4to457.html";
  end if;
  I := POpen("lynx -dump " cat nipp_web cat fname, "r");
  nipps := ParseNippDiscQuaternary2(Read(I), d);
  return [NippToForms(nipp : Rank := 4) : nipp in nipps];
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

intrinsic ParseNippDiscQuaternary2(r::MonStgElt, d::RngIntElt) -> SeqEnum[Rec]
{Extract the records of a certain discrminant from a file in the Nipp database of quaternary lattices.}
  r_lines := Split(r, "\n");
  split_lines := [Split(line, "\t ") : line in r_lines];
  if Split("404 Not Found", " ") eq split_lines[1] then
      error "Webpage not found!";
  end if;
  digits := [Sprintf("%o", i) : i in [0..9]];
  is_lattice := false;
  idx := 0;
  while not is_lattice do
      idx +:= 1;
      line := split_lines[idx];
      is_lattice := line[1][1] in digits;
  end while;
  // TODO : can binary search the file to make this part faster
  is_disc_lt_d := (#line ne 0) and (eval line[1]) lt d;
  while is_lattice and is_disc_lt_d do
      idx +:= 1;
      line := split_lines[idx];
      is_lattice := line[1][1] in digits;
      if is_lattice then
	  is_disc_lt_d := (#line ne 0) and (eval line[1]) lt d;
      end if;
  end while;
  // split_lines_disc := [line : line in split_lines |
  //		       (#line ne 0) and (eval line[1]) eq d];
  split_lines_disc := [];
  is_disc_d := is_lattice and (#line ne 0) and (eval line[1]) eq d;
  while is_disc_d do
      Append(~split_lines_disc, line);
      idx +:= 1;
      line := split_lines[idx];
      is_lattice := line[1][1] in digits;
      if is_lattice then
	  is_disc_d := (#line ne 0) and (eval line[1]) eq d;
      end if;
  end while;
  genera := [];
  latGen := rec<latticeGenus_RF | >;
  latGen`D := d;
  latGen`genus := 1;
  latGen`lattices := [];
  num_hasse := #PrimeDivisors(2*d);
  for line in split_lines_disc do
      genus := eval line[2];
      if (genus gt latGen`genus) then
	  Append(~genera, latGen);
	  latGen`genus := genus;
	  latGen`lattices := [];
      end if;
      lattice := rec<lattice_RF | >;
      lattice`form := [eval line[j] : j in [3..12]];
      hasse_chars := [[line[i][j] : j in [1..#line[i]]] : i in [13..#line-4]];
      hasse_strs := [&cat[(x eq "-") select " -" else x : x in hasse_char]
		     : hasse_char in hasse_chars];
      hasse_sym := &cat [[eval(y) : y in Split(hasse_str, " ")] : hasse_str in hasse_strs];
      assert num_hasse eq #hasse_sym;
      latGen`HasseSym := hasse_sym;
      lattice`numAut := eval line[#line-2];
      latGen`mass := (eval line[#line-1])/(eval line[#line]);
      Append(~latGen`lattices, lattice);
  end for;
  if not IsEmpty(split_lines_disc) then
      Append(~genera, latGen);
  end if;
  return genera;
end intrinsic;

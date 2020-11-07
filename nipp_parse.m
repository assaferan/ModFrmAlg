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

function parseNippFile(fname)
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
end function;

function NippToForm(nipp_entry)
  // We take the first lattice, but it doesn't matter to us
  a := nipp_entry`lattices[1]`form;
  off_diag := [x / 2 : x in a[6..#a]];
  triangular := [j*(j-1) div 2 : j in [1..5]];
  columns := [[]];
  columns cat:= [off_diag[triangular[j]+1..triangular[j+1]] : j in [1..4]];
  a_magma := &cat[columns[i] cat [a[i]] : i in [1..5]];
  return SymmetricMatrix(a_magma);
end function;

// old code

/*
procedure parseEntry(~rec, entry, fieldName, sep : desc := desc)
  s := Split(entry, sep);
  if #desc gt 0 then 
    assert s[1] eq desc;
  end if;
  rec``fieldName := eval s[2];
end procedure;
*/

/*
procedure parseSeqEntry(~rec, entry, fieldName, sep :
			desc := "", offset := 1, multiple := false)
  s := Split(entry, sep);
  if #desc gt 0 then 
    assert s[1] eq desc;
  end if;
  if multiple then 
    rec``fieldName  := [eval s[j] : j in [offset+1..#s]];
  else
    rec``fieldName := eval s[offset+1];
  end if;
end procedure;
*/

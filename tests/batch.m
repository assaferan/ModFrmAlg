freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
                
                                                                            
   FILE: batch.m (functions for batch runs)

   04/06/21 : File created
 
 ***************************************************************************/

// Here we list the intrinsics that this file defines

// imports
import "../io/path.m" : path;
import "../lattice_db/nipp_parse.m" : get_nipp_table_idx, get_last_nipp_idx;

import "tests.m" : get_nonlifts;

function analyticConductor(k, j)
//  return (j+7)*(j+9)*(2*k+j+3)*(2*k+j+5)/16;
  // These differ from the theory, but seem to work in practice
  gamma_shifts := [k-5/2,k-3/2,k+j-3/2, k+j-1/2];
  return &*[Abs(kappa) + 3 : kappa in gamma_shifts];
end function;

function getWeightsByAnalyticConductor(N_an)
  // This is another possiblity
  // max_j := 2*Floor(N_an^(1/4)) - 7;
  // for j in [0..max_j] do
  //end for;
  j := 0;
  // The JL transfer only works for weight ge 3 
  k := 3;
  cur_cond := analyticConductor(k, j);
  res := [];
  while cur_cond le N_an do
    while cur_cond le N_an do
      Append(~res, [k,j]);
      k +:= 1;
      cur_cond := analyticConductor(k, j);
    end while;
    k := 3;
    // We only consider even j
    j +:= 2;
    cur_cond := analyticConductor(k, j);
  end while;
  return res;
end function;

function getBoxByAnalyticConductor(N_an)
  weights := getWeightsByAnalyticConductor(N_an);
  nipp_maxs := [0,256,270,300,322,345,400,440,480,500,513];
  max_max := Floor(N_an / analyticConductor(3, 0));
  num_tables := get_nipp_table_idx(max_max, nipp_maxs);
  nipp_fnames := [Sprintf("lattice_db/nipp%o-%o.txt",
			  nipp_maxs[i]+1, nipp_maxs[i+1])
		     : i in [1..num_tables]];
  nipps := [ParseNippFile(fname) : fname in nipp_fnames];
  nipp_lens := [#nipp : nipp in nipps];
  res := [];
  for w in weights do
     max_N := Floor(N_an / analyticConductor(w[1], w[2]));
     // last index with this disc
     table_idx := get_nipp_table_idx(max_N, nipp_maxs);
     nipp := nipps[table_idx];
     max_idx := get_last_nipp_idx(max_N, nipp);
     if max_idx ge 1 then
       Append(~res, <w, table_idx, max_idx>);
     end if;
  end for;
  return res, nipp_lens;
end function;

// This is needed due to unexplained magma crashes
function createBatchFile(tid, idx, k, j)
  fname := Sprintf("batch_files/lpolys_single_%o_%o_%o_%o.m", tid, idx, k, j);
  f := Open(fname, "w");
  output_str := "AttachSpec(\"spec\");\n";
  output_str cat:= "import \"tests/tests.m\" : get_lpolys;\n";
  output_str cat:= "time0 := Cputime();\n";
  output_str cat:= Sprintf("get_lpolys(%o, %o, [%o, %o]);\n", tid, idx, k, j);
  output_str cat:= "printf \"elapsed: %%o\\n\", Cputime()-time0;\n";
  output_str cat:= "exit;\n";
  fprintf f, output_str;
  delete f;
  return fname;
end function;

function get_lpolys_batch(N_an)
  vprintf AlgebraicModularForms, 2:
    "Calculating boxes...";
  boxes, nipp_lens := getBoxByAnalyticConductor(N_an);
  cmds := [];
  vprintf AlgebraicModularForms, 2:
    "Done!\nPreparing batch files....\n";
  for box in boxes do
     k := box[1][1];
     j := box[1][2];
     table_idx := box[2];
     max_idx := box[3];
     vprintf AlgebraicModularForms, 2:
	 "k = %o, j = %o, table_idx = %o, max_idx = %o...\n",
	 k, j, table_idx, max_idx;
     for tid in [1..table_idx] do
       if tid eq table_idx then
	 mid := max_idx;
       else
         mid := nipp_lens[tid];
       end if;
       for idx in [1..mid] do
	 fname := createBatchFile(tid, idx, k, j);
         // magma_cmd := Sprintf("magma -b " cat fname);
         // Append(~cmds, magma_cmd);
         Append(~cmds, fname);
       end for;
	    // we abandon this method due to unexplained magma crashes
	    // cmd := Sprintf("./lpolys_batch.sh 1 %o %o %o", box[2],
	    //	   box[1][1], box[1][2]);
	    //System(cmd);
     end for;
  end for;
  vprintf AlgebraicModularForms, 2: "Done!\n";
  return cmds;
end function;

procedure prepareBatchFile(N_an)
  cmds := get_lpolys_batch(N_an);
  fname := Sprintf("batch_files/lpolys_box_%o.sh", N_an);
  f := Open(fname, "w");
  output_str := "#!/bin/bash\n";
  all_cmds := &cat[ "\"" cat cmd cat "\" \\ \n" : cmd in cmds];  
  output_str cat:= "PROCESSES_TO_RUN=(" cat all_cmds cat ")\n";
  output_str cat:= "for i in ${PROCESSES_TO_RUN[@]}; do\n";
  output_str cat:= "\t magma -b ${i%%/*}/./${i##*/} > ${i}.log 2>&1 &\n";
  output_str cat:= "done\n";
// output_str cat:= "wait\n";
  fprintf f, output_str;
  delete f;
  chmod_cmd := Sprintf("chmod +x %o", fname);
  System(chmod_cmd);
  // we will run it from outside
  // System("./" cat fname);
end procedure;

procedure LaunchCommands(cmds)
  vprintf AlgebraicModularForms, 2:
    "Done! Launching %o commands.", #cmds;
  for cmd in cmds do
    System(cmd);
  end for;
end procedure;

procedure write_lser_invariants(lser, num_coeffs, fname)
  lser_invs := AssociativeArray();
  lser_invs["dirichlet"] := LGetCoefficients(lser, num_coeffs);
  lser_data := LSeriesData(lser);
  lser_invs["weight"] := lser_data[1];
  lser_invs["gamma_shifts"] := lser_data[2];
  lser_invs["conductor"] := lser_data[3];
  lser_invs["sign"] := lser_data[5];
  lser_invs["poles"] := lser_data[6];
  lser_invs["residues"] := lser_data[7];
// save for later - else it tries to compute all necessary coefficients
//  lser_invs["critical_values"] := [<pt, Evaluate(lser, pt)>
//				      : pt in CriticalPoints(lser)];
  lser_invs["motivic_weight"] := MotivicWeight(lser);
  lser_invs["degree"] := Degree(lser);
  num_euler := Floor(Sqrt(num_coeffs));
  lser_invs["euler_factors"] := [<p, EulerFactor(lser, p)>
				    : p in PrimesUpTo(num_euler)];

  file := Open(path() cat fname, "w");
  for key in Keys(lser_invs) do
    fprintf file, "%o := %m;\n", key, lser_invs[key];
  end for;
  delete file;
end procedure;

// In order to find out interesting things
// Right now focus on disc le 256
// wt is a pair [k,j] for Paramodular P_{k,j}
function compute_lsers(disc, g, nipp, nipp_idx, wt, prec : Estimate := false)
  wt_str := Join([Sprintf("%o", x) : x in wt], "_");
  fname_pre := Sprintf("lser_disc_%o_genus_%o_wt_%o_idx_%o",
		       disc, g, wt_str, nipp_idx);
  fname := fname_pre cat ".amf"; 
  if FileExists(path() cat fname : ShowErrors := false) then
    M := AlgebraicModularForms(fname);
  else
    A := NippToForm(nipp[nipp_idx]);
    k,j := Explode(wt);
    G := OrthogonalGroup(A);
    W := HighestWeightRepresentation(G,[k+j-3, k-3]); 
    M := AlgebraicModularForms(G, W);
  end if;
  fs := HeckeEigenforms(M : Estimate := Estimate);
  nonlift_idxs := get_nonlifts(fs, disc : Estimate := Estimate);
  lsers := [];
  for idx in nonlift_idxs do
    lser := LSeries(fs[idx] : Estimate := Estimate);
    coeffs := LGetCoefficients(lser, prec);
    Append(~lsers, lser);
  end for;
  if Estimate then
    printf "Saving to file %o.\n", fname;
  end if;
  Save(M, fname : Overwrite);
  for lser_idx in [1..#lsers] do
    lser_fname := Sprintf("%o_f_%o.m", fname_pre, lser_idx);
    lser := lsers[lser_idx];
    write_lser_invariants(lser, prec, lser_fname);
  end for;
  return lsers;
end function;

// get the first prec*sqrt(disc) coefficients of the L-series
// !!! TODO - the hard coded 138.84 is the number for (k,j) = (3,0), (4,0)
// Should replace by reading from the Edgar file !!!
procedure get_lsers(table_idx, nipp_idx, wt :
		   prec := 138.84, Estimate := false, chunk := 10)
  nipp_maxs := [0,256,270,300,322,345,400,440,480,500,513];
  nipp_fname := Sprintf("lattice_db/nipp%o-%o.txt",
			  nipp_maxs[table_idx]+1, nipp_maxs[table_idx+1]);
  nipp := ParseNippFile(nipp_fname);
  disc := nipp[nipp_idx]`D;
  g := nipp[nipp_idx]`genus;
  num_coeffs := Ceiling(Sqrt(disc)*prec);
  time0 := Cputime();
  for i in [1..num_coeffs div chunk] do
      lsers := compute_lsers(disc, g, nipp, nipp_idx, wt, i*chunk
		      : Estimate := Estimate);
      printf "computed %o coefficients. elapsed: %o\n",
	i*chunk, Cputime()-time0;
      if IsEmpty(lsers) then return; end if;
  end for;
  lsers := compute_lsers(disc, g, nipp, nipp_idx, wt, num_coeffs
		: Estimate := Estimate);
end procedure;

// This is needed due to unexplained magma crashes
function createLSerBatchFile(tid, idx, k, j)
  fname := Sprintf("batch_files/lser_single_%o_%o_%o_%o.m", tid, idx, k, j);
  f := Open(fname, "w");
  output_str := "AttachSpec(\"ModFrmAlg.spec\");\n";
  output_str cat:= "import \"tests/batch.m\" : get_lsers;\n";
  output_str cat:= "time0 := Cputime();\n";
  output_str cat:= Sprintf("get_lsers(%o, %o, [%o, %o]);\n", tid, idx, k, j);
  output_str cat:= "printf \"elapsed: %%o\\n\", Cputime()-time0;\n";
  output_str cat:= "exit;\n";
  fprintf f, output_str;
  delete f;
  return fname;
end function;

procedure prepareLSerBatchFile(t_idx, start, upto, wt)
  k,j := Explode(wt);
  cmds := [createLSerBatchFile(t_idx, idx, k, j) : idx in [start..upto]];
  fname := Sprintf("batch_files/lser_%o_%o_%o_%o_%o.sh",
		   t_idx, start, upto, k, j);
  f := Open(fname, "w");
  output_str := "#!/bin/bash\n";
  all_cmds := &cat[ "\"" cat cmd cat "\" \\ \n" : cmd in cmds];  
  output_str cat:= "PROCESSES_TO_RUN=(" cat all_cmds cat ")\n";
  output_str cat:= "for i in ${PROCESSES_TO_RUN[@]}; do\n";
  output_str cat:= "\t magma -b ${i%%/*}/./${i##*/} > ${i}.log 2>&1 &\n";
  output_str cat:= "done\n";
// output_str cat:= "wait\n";
  fprintf f, output_str;
  delete f;
  chmod_cmd := Sprintf("chmod +x %o", fname);
  System(chmod_cmd);
  // we will run it from outside
  // System("./" cat fname);
end procedure;

function aut_group_data(disc : Estimate := false)
  Qs := QuinaryQuadraticLattices(disc);
  all_aut_size := [];
  all_aut_fs := [];
  for Qgen in Qs do
    Q := Qgen[1];
    G := OrthogonalGroup(Q);
    aut_fs := [];
    for d in Divisors(disc) do
      W := SpinorNormRepresentation(G, d);
      M := AlgebraicModularForms(G, W);
      fs := HeckeEigenforms(M : Estimate := Estimate);
      if d eq 1 then
        reps := Representatives(Genus(M));
        auts := [AutomorphismGroup(r) : r in reps];
        aut_size := [#aut : aut in auts];
        Append(~all_aut_size, aut_size);
      end if;
      nonlift_idxs := get_nonlifts(fs, disc : Estimate := Estimate);
      for idx in nonlift_idxs do
        f := fs[idx];
        pivot := 1;
        while f`vec[pivot] eq 0 do pivot +:= 1; end while;
        Append(~aut_fs, aut_size[pivot]);
      end for;
   end for;
   Append(~all_aut_fs, aut_fs);
  end for;
  return all_aut_size, all_aut_fs;
end function;

procedure write_aut_group_data(disc : Estimate := false)
  fname := Sprintf("autgrp/autgrp_disc_%o_wt_3_0.m", disc);
  file := Open(path() cat fname, "w");
  autgrp_invs := AssociativeArray();
  aut_size, aut_fs := aut_group_data(disc : Estimate := Estimate); 
  autgrp_invs["aut_size"] := aut_size;
  autgrp_invs["aut_fs"] := aut_fs;
  for key in Keys(autgrp_invs) do
    fprintf file, "%o := %m;\n", key, autgrp_invs[key];
  end for;
  delete file;
end procedure;

function createAutGrpBatchFile(disc)
  fname := Sprintf("batch_files/autgrp_disc_%o.m", disc);
  f := Open(fname, "w");
  output_str := "GetSeed();\n";
  output_str cat:= "AttachSpec(\"ModFrmAlg.spec\");\n";
  output_str cat:= "import \"tests/batch.m\" : write_aut_group_data;\n";
  output_str cat:= "time0 := Cputime();\n";
  output_str cat:= Sprintf("write_aut_group_data(%o);\n", disc);
  output_str cat:= "printf \"elapsed: %%o\\n\", Cputime()-time0;\n";
  output_str cat:= "exit;\n";
  fprintf f, output_str;
  delete f;
  return fname;
end function;

procedure prepareAutGrpBatchFile(start, upto)
  cmds := [createAutGrpBatchFile(disc) : disc in [start..upto]];
  fname := Sprintf("batch_files/autgrp_discs_%o_%o.sh",
		   start, upto);
  f := Open(fname, "w");
  output_str := "#!/bin/bash\n";
  all_cmds := &cat[ "\"" cat cmd cat "\" \\ \n" : cmd in cmds];  
  output_str cat:= "PROCESSES_TO_RUN=(" cat all_cmds cat ")\n";
  output_str cat:= "for i in ${PROCESSES_TO_RUN[@]}; do\n";
  output_str cat:= "\t magma -b ${i%%/*}/./${i##*/} > ${i}.log 2>&1 &\n";
  output_str cat:= "done\n";
  fprintf f, output_str;
  delete f;
  chmod_cmd := Sprintf("chmod +x %o", fname);
  System(chmod_cmd);
  // we will run it from outside
  // System("./" cat fname);
end procedure;

// Adding batch files for parallel Hecke operators

function make_intervals(batch_size, num)
    num_batches := (num-1) div batch_size + 1;
    batches := [[batch_size*(j-1), batch_size*j] : j in [1..num_batches-1]];
    Append(~batches, [batch_size*(num_batches-1), num]);
    return batches;
end function;

// e.g.
// nProc, nPivots := InitPivots(M, pR, k, hecke_idx);
// nums := [p^LogNumPivotNbrs(nProc, pivot_idx) : pivot_idx in [1..nPivots]];
// intervals := [make_intervals(B, num) : num in nums];
// heckes := [[HeckePivot(M, nProc, pivot_idx, ThetaPrec, hecke_idx, I[1], I[2]) :
//             I in intervals[pivot_idx]] : pivot_idx in [1..npivots]];
//  omf_name := "rank_8_d_53";


function createHeckeBatchFile(omf_name, pR, k, pivot_idx, start, upTo, hecke_idx, ThetaPrec)
  batch_fname := omf_name cat Sprintf("_%o_%o_%o_%o_%o.m", Norm(pR), k, pivot_idx, start, upTo);
  output_fname := omf_name cat Sprintf("_%o_%o_%o_%o_%o.out", Norm(pR), k, pivot_idx, start, upTo);
  f := Open(batch_fname, "w");
  output_str := "GetSeed();\n";
  output_str cat:= "AttachSpec(\"ModFrmAlg.spec\");\n";
  output_str cat:= Sprintf("M := AlgebraicModularForms(\"%o\");\n", omf_name cat ".omf");
  output_str cat:= Sprintf("pR := %m;\n",pR);
  output_str cat:= Sprintf("nProc := InitPivots(M, pR, %o, %o);\n", k, hecke_idx);
  output_str cat:= Sprintf("hecke := HeckePivot(M, nProc, %o, %o, %o, %o, %o);\n",
			    pivot_idx, ThetaPrec, hecke_idx, start, upTo);
  output_str cat:= Sprintf("Write(\"%o\", Eltseq(hecke));\n", output_fname);
  output_str cat:= "exit;\n";
  fprintf f, output_str;
  delete f;
  return batch_fname;
end function;

function createHeckeBatchFiles(omf_name, p, k, pivot : ThetaPrec := 5, B := 10^5)
    M := AlgebraicModularForms(omf_name + ".omf");
    pR := ideal<Integers() | p>;
    nProc, nPivots := InitPivots(M, pR, k, pivot);
    nums := [p^LogNumPivotNbrs(nProc, pivot_idx) : pivot_idx in [1..nPivots]];
    intervals := [make_intervals(B, num) : num in nums];
    fnames := [];
    for pivot_idx in [1..nPivots] do
	for I in intervals[pivot_idx] do
	    f := createHeckeBatchFile(omf_name, pR, k, pivot_idx, I[1], I[2], pivot, ThetaPrec);
	    Append(~fnames, f);
	end for;
    end for;
    return fnames;
end function;

procedure prepareHeckeBatchFile(omf_name, p, k, pivot : ThetaPrec := 5, B := 10^5)
  cmds := createHeckeBatchFiles(omf_name, p, k, pivot : ThetaPrec := ThetaPrec, B := B);
  fname := omf_name cat Sprintf("_%o_%o_%o_%o_%o.sh", p, k, pivot_idx, start, upTo);
  f := Open(fname, "w");
  output_str := "#!/bin/bash\n";
  all_cmds := &cat[ "\"" cat cmd cat "\" \\ \n" : cmd in cmds];  
  output_str cat:= "PROCESSES_TO_RUN=(" cat all_cmds cat ")\n";
  output_str cat:= "for i in ${PROCESSES_TO_RUN[@]}; do\n";
  output_str cat:= "\t magma -b ${i%%/*}/./${i##*/} > ${i}.log 2>&1 &\n";
  output_str cat:= "done\n";
  fprintf f, output_str;
  delete f;
  chmod_cmd := Sprintf("chmod +x %o", fname);
  System(chmod_cmd);
  // we will run it from outside
  // System("./" cat fname);
end procedure;

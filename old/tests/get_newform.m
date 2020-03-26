
// To make the character of type GrpDrchElt, type "MakeCharacter_7_b();"
function MakeCharacter(level, char_order)
    N := level;
    order := char_order;
    char_gens := SequenceToList(UnitGenerators(DirichletGroup(N)));
    v := [*1 : g in char_gens*];
    // chi(gens[i]) = zeta^v[i]
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

function MakeNewformModFrm(level, weight, char_order, hecke_orbit :prec:=4)
    prec := Min(prec, NextPrime(997) - 1);
    chi := MakeCharacter(level, char_order);
    S := CuspidalSubspace(ModularSymbols(chi, weight));
    Snew := NewSubspace(S);
    D := NewformDecomposition(Snew);
    f := Eigenform(D[hecke_orbit], prec + 1);
    
    return f;
end function;

function path()
	return "/Users/eranassaf/Documents/Code/ModFrmAlg/data/";
end function;

function real_eq(M, other)
    if assigned M`eps then
	if not assigned other`eps then return false; end if;
	if M`eps ne other`eps then return false; end if;
    end if;
  
    if assigned M`multi then
	if not assigned other`multi then
	    return false;
	end if;
	if M`multi ne other`multi then
	    return false;
	end if;
    end if;
    if assigned M`is_multi then
	if not assigned other`is_multi then
	    return false;
	end if;
	if M`is_multi ne other`is_multi then
	    return false;
	end if;
    end if;
    if assigned M`multi_modsymgens then
	if not assigned other`multi_modsymgens then
	    return false;
	end if;
	if M`multi_modsymgens ne other`multi_modsymgens then
	    return false;
	end if;
    end if;
    if assigned M`multi_quo_maps then
	if not assigned other`multi_quo_maps then
	    return false;
	end if;
	if M`multi_quo_maps ne other`multi_quo_maps then
	    return false;
	end if;
    end if;
    if assigned M`MC_ModSymBasis_raw then
	if not assigned other`MC_ModSymBasis_raw then
	    return false;
	end if;
	if M`MC_ModSymBasis_raw ne other`MC_ModSymBasis_raw then
	    return false;
	end if;
    end if;
    if assigned M`associated_newform_space then
	if not assigned other`associated_newform_space then
	    return false;
	end if;
	if M`associated_newform_space ne other`associated_newform_space then
	    return false;
	end if;
    end if;
    if assigned M`isgamma1 then
	if not assigned other`isgamma1 then
	    return false;
	end if;
	if M`isgamma1 ne other`isgamma1 then
	    return false;
	end if;
    end if;
    if assigned M`isgamma then
	if not assigned other`isgamma then
	    return false;
	end if;
	if M`isgamma ne other`isgamma then
	    return false;
	end if;
    end if;

    if M`k ne other`k then return false; end if;
    if M`sign ne other`sign then return false; end if;
  
    if assigned M`hecke_bound then
      if not assigned other`hecke_bound then
	  return false;
      end if;
      if M`hecke_bound ne other`hecke_bound then
	  return false;
      end if;
    end if;
    if assigned M`root then
      if not assigned other`root then
	  return false;
      end if;
      if M`root ne other`root then
	  return false;
      end if;
    end if;

    if M`is_ambient_space ne other`is_ambient_space then
	return false;
    end if;
 
    if assigned M`creator then
	if not assigned other`creator then
	    return false;
	end if;
	if M`creator ne other`creator then
	    return false;
	end if;
    end if;
    
    if assigned M`other_levels then
	if not assigned other`other_levels then
	    return false;
	end if;
	for i in [1..#M`other_levels] do
	    if M`other_levels[i] ne other`other_levels[i] then
		return false;
	    end if;
	end for;
    end if;
    if assigned M`mlist then
	if not assigned other`mlist then
	    return false;
	end if;
	if M`mlist`k ne other`mlist`k then
	    return false;
	end if;
	if M`mlist`F ne other`mlist`F then
	    return false;
	end if;
	if M`mlist`R ne other`mlist`R then
	    return false;
	end if;
	if M`mlist`p1list ne other`mlist`p1list then
	    return false;
	end if;
	if M`mlist`n ne other`mlist`n then
	    return false;
	end if;
    end if;
    if assigned M`quot then
	if not assigned other`quot then
	    return false;
	end if;
	if M`quot`Sgens ne other`quot`Sgens then
	    return false;
	end if;
	if M`quot`Squot ne other`quot`Squot then
	    return false;
	end if;
	if M`quot`Scoef ne other`quot`Scoef then
	    return false;
	end if;
	if M`quot`Tgens ne other`quot`Tgens then
	    return false;
	end if;
	if M`quot`Tquot ne other`quot`Tquot then
	    return false;
	end if;
	if assigned M`quot`Tquot_scaled then
	    if not assigned other`quot`Tquot_scaled then
		return false;
	    end if;
	    if M`quot`Tquot_scaled ne other`quot`Tquot_scaled then
		return false;
	    end if;
	end if;
	if assigned M`quot`scalar then
	    if not assigned other`quot`scalar then
		return false;
	    end if;
	    if M`quot`scalar ne other`quot`scalar then
		return false;
	    end if;
	end if;
    end if;
    if assigned M`N then
	if not assigned other`N then
	    return false;
	end if;
	if M`N ne other`N then
	    return false;
	end if;
    end if;
    if assigned M`dual_representation then
	if not assigned other`dual_representation then
	    return false;
	end if;
	if M`dual_representation ne other`dual_representation then
	    return false;
	end if;
    end if;

    if M`dimension ne other`dimension then return false; end if;
    if M`F ne other`F then return false; end if;
    if M`sub_representation ne other`sub_representation then
	return false;
    end if;
 
    if assigned M`sub_cuspidal_representation then
	if not assigned other`sub_cuspidal_representation then
	    return false;
	end if;
	if M`sub_cuspidal_representation ne
	   other`sub_cuspidal_representation then
	    return false;
	end if;
    end if;
    if assigned M`dual_cuspidal_representation then
	if not assigned other`dual_cuspidal_representation then
	    return false;
	end if;
	if M`dual_cuspidal_representation ne
	   other`dual_cuspidal_representation then
	    return false;
	end if;
    end if;
    if assigned M`sub_integral_representation then
	if not assigned other`sub_integral_representation then
	    return false;
	end if;
	if M`sub_integral_representation ne
	   other`sub_integral_representation then
	    return false;
	end if;
    end if;
    if assigned M`dual_integral_representation then
	if not assigned other`dual_integral_representation then
	    return false;
	end if;
	if M`dual_integral_representation ne
	   other`dual_integral_representation then
	    return false;
	end if;
    end if;
    if assigned M`sub_integral_cuspidal_representation then
	if not assigned other`sub_integral_cuspidal_representation then
	    return false;
	end if;
	if M`sub_integral_cuspidal_representation ne
	   other`sub_integral_cuspidal_representation then
	    return false;
	end if;
    end if;
    if assigned M`dual_integral_cuspidal_representation then
	if not assigned other`dual_integral_cuspidal_representation then
	    return false;
	end if;
	if M`dual_integral_cuspidal_representation ne
	   other`dual_integral_cuspidal_representation then
	    return false;
	end if;
    end if;
    if assigned M`newform_decomposition then
	if not assigned other`newform_decomposition then
	    return false;
	end if;
	if M`newform_decomposition ne
	   other`newform_decomposition then
	    return false;
	end if;
    end if;
    if assigned M`decomposition then
	if not assigned other`decomposition then
	    return false;
	end if;
	if M`decomposition ne
	   other`decomposition then
	    return false;
	end if;
    end if;
    if assigned M`complement then
	if not assigned other`complement then
	    return false;
	end if;
	if M`complement ne
	   other`complement then
	    return false;
	end if;
    end if;
    if assigned M`cuspidal_part then
	if not assigned other`cuspidal_part then
	    return false;
	end if;
	if M`cuspidal_part ne
	   other`cuspidal_part then
	    return false;
	end if;
    end if;
    if assigned M`eisenstein_part then
	if not assigned other`eisenstein_part then
	    return false;
	end if;
	if M`eisenstein_part ne
	   other`eisenstein_part then
	    return false;
	end if;
    end if;
    if assigned M`plus_part_sub then
	if not assigned other`plus_part_sub then
	    return false;
	end if;
	if M`plus_part_sub ne
	   other`plus_part_sub then
	    return false;
	end if;
    end if;
    if assigned M`plus_part_dual then
	if not assigned other`plus_part_dual then
	    return false;
	end if;
	if M`plus_part_dual ne
	   other`plus_part_dual then
	    return false;
	end if;
    end if;
    if assigned M`minus_part_sub then
	if not assigned other`minus_part_sub then
	    return false;
	end if;
	if M`minus_part_sub ne
	   other`minus_part_sub then
	    return false;
	end if;
    end if;
    if assigned M`minus_part_dual then
	if not assigned other`minus_part_dual then
	    return false;
	end if;
	if M`minus_part_dual ne
	   other`minus_part_dual then
	    return false;
	end if;
    end if;
    if assigned M`plus_subspace then
	if not assigned other`plus_subspace then
	    return false;
	end if;
	if M`plus_subspace ne
	   other`plus_subspace then
	    return false;
	end if;
    end if;
    if assigned M`minus_subspace then
	if not assigned other`minus_subspace then
	    return false;
	end if;
	if M`minus_subspace ne
	   other`minus_subspace then
	    return false;
	end if;
    end if;
    if assigned M`new_part then
	if not assigned other`new_part then
	    return false;
	end if;
	if M`new_part ne
	   other`new_part then
	    return false;
	end if;
    end if;
    if assigned M`old_part then
	if not assigned other`old_part then
	    return false;
	end if;
	if M`old_part ne
	   other`old_part then
	    return false;
	end if;
    end if;
    if assigned M`p_new_part then
	if not assigned other`p_new_part then
	    return false;
	end if;
	if M`p_new_part ne
	   other`p_new_part then
	    return false;
	end if;
    end if;
    if assigned M`modsym_basis then
	if not assigned other`modsym_basis then
	    return false;
	end if;
	if M`modsym_basis ne
	   other`modsym_basis then
	    return false;
	end if;
    end if;
    if assigned M`associated_new_space then
	if not assigned other`associated_new_space then
	    return false;
	end if;
	if M`associated_new_space ne
	   other`associated_new_space then
	    return false;
	end if;
    end if;
    if assigned M`star_involution then
	if not assigned other`star_involution then
	    return false;
	end if;
	if M`star_involution ne
	   other`star_involution then
	    return false;
	end if;
    end if;
    if assigned M`dual_star_involution then
	if not assigned other`dual_star_involution then
	    return false;
	end if;
	if M`dual_star_involution ne
	   other`dual_star_involution then
	    return false;
	end if;
    end if;
    if assigned M`discriminant then
	if not assigned other`discriminant then
	    return false;
	end if;
	if M`discriminant ne
	   other`discriminant then
	    return false;
	end if;
    end if;
    if assigned M`discriminant_Q then
	if not assigned other`discriminant_Q then
	    return false;
	end if;
	if M`discriminant_Q ne
	   other`discriminant_Q then
	    return false;
	end if;
    end if;
    if assigned M`winding then
	if not assigned other`winding then
	    return false;
	end if;
	if M`winding ne
	   other`winding then
	    return false;
	end if;
    end if;
    if assigned M`twisted_winding then
	if not assigned other`twisted_winding then
	    return false;
	end if;
	if M`twisted_winding ne
	   other`twisted_winding then
	    return false;
	end if;
    end if;
    if assigned M`twisted_winding_index then
	if not assigned other`twisted_winding_index then
	    return false;
	end if;
	if M`twisted_winding_index ne
	   other`twisted_winding_index then
	    return false;
	end if;
    end if;
    if assigned M`boundary_map then
	if not assigned other`boundary_map then
	    return false;
	end if;
	if M`boundary_map ne
	   other`boundary_map then
	    return false;
	end if;
    end if;
    if assigned M`cusplist then
	if not assigned other`cusplist then
	    return false;
	end if;
	if M`cusplist ne
	   other`cusplist then
	    return false;
	end if;
    end if;
    if assigned M`heilbronn_cremona then
	if not assigned other`heilbronn_cremona then
	    return false;
	end if;
	if M`heilbronn_cremona ne
	   other`heilbronn_cremona then
	    return false;
	end if;
    end if;
    if assigned M`heilbronn_merel then
	if not assigned other`heilbronn_merel then
	    return false;
	end if;
	if M`heilbronn_merel ne
	   other`heilbronn_merel then
	    return false;
	end if;
    end if;
    if assigned M`atkin_lehner then
	if not assigned other`atkin_lehner then
	    return false;
	end if;
	if M`atkin_lehner ne
	   other`atkin_lehner then
	    return false;
	end if;
    end if;
    if assigned M`dual_atkin_lehner then
	if not assigned other`dual_atkin_lehner then
	    return false;
	end if;
	if M`dual_atkin_lehner ne
	   other`dual_atkin_lehner then
	    return false;
	end if;
    end if;
    if assigned M`hecke_operator then
	if not assigned other`hecke_operator then
	    return false;
	end if;
	if M`hecke_operator ne
	   other`hecke_operator then
	    return false;
	end if;
    end if;
    if assigned M`hecke_operator_proj_data then
	if not assigned other`hecke_operator_proj_data then
	    return false;
	end if;
	if M`hecke_operator_proj_data ne
	   other`hecke_operator_proj_data then
	    return false;
	end if;
    end if;
    if assigned M`dual_hecke_operator then
	if not assigned other`dual_hecke_operator then
	    return false;
	end if;
	if M`dual_hecke_operator ne
	   other`dual_hecke_operator then
	    return false;
	end if;
    end if;
    if assigned M`projection_matrix then
	if not assigned other`projection_matrix then
	    return false;
	end if;
	if M`projection_matrix ne
	   other`projection_matrix then
	    return false;
	end if;
    end if;
    if assigned M`standard_images then
	if not assigned other`standard_images then
	    return false;
	end if;
	if M`standard_images ne
	   other`standard_images then
	    return false;
	end if;
    end if;
    if assigned M`standard_images_all then
	if not assigned other`standard_images_all then
	    return false;
	end if;
	if M`standard_images_all ne
	   other`standard_images_all then
	    return false;
	end if;
    end if;
    if assigned M`degeneracy_matrices_out then
	if not assigned other`degeneracy_matrices_out then
	    return false;
	end if;
	if M`degeneracy_matrices_out ne
	   other`degeneracy_matrices_out then
	    return false;
	end if;
    end if;
    if assigned M`degeneracy_matrices_in then
	if not assigned other`degeneracy_matrices_in then
	    return false;
	end if;
	if M`degeneracy_matrices_in ne
	   other`degeneracy_matrices_in then
	    return false;
	end if;
    end if;
    if assigned M`hecke_algebra then
	if not assigned other`hecke_algebra then
	    return false;
	end if;
	if M`hecke_algebra ne
	   other`hecke_algebra then
	    return false;
	end if;
    end if;
    if assigned M`hecke_algebra_over_q then
	if not assigned other`hecke_algebra_over_q then
	    return false;
	end if;
	if M`hecke_algebra_over_q ne
	   other`hecke_algebra_over_q then
	    return false;
	end if;
    end if;
    if assigned M`hecke_algebra_disc then
	if not assigned other`hecke_algebra_disc then
	    return false;
	end if;
	if M`hecke_algebra_disc ne
	   other`hecke_algebra_disc then
	    return false;
	end if;
    end if;
    if assigned M`hecke_eigenvalue_field then
	if not assigned other`hecke_eigenvalue_field then
	    return false;
	end if;
	if M`hecke_eigenvalue_field ne
	   other`hecke_eigenvalue_field then
	    return false;
	end if;
    end if;
    if assigned M`hecke_eigenvalue_ring then
	if not assigned other`hecke_eigenvalue_ring then
	    return false;
	end if;
	if M`hecke_eigenvalue_ring ne
	   other`hecke_eigenvalue_ring then
	    return false;
	end if;
    end if;
    if assigned M`hecke_algebra_z_basis then
	if not assigned other`hecke_algebra_z_basis then
	    return false;
	end if;
	if M`hecke_algebra_z_basis ne
	   other`hecke_algebra_z_basis then
	    return false;
	end if;
    end if;
    if assigned M`inner_twists then
	if not assigned other`inner_twists then
	    return false;
	end if;
	if M`inner_twists ne
	   other`inner_twists then
	    return false;
	end if;
    end if;
    if assigned M`action_on_modsyms then
	if not assigned other`action_on_modsyms then
	    return false;
	end if;
	if M`action_on_modsyms ne
	   other`action_on_modsyms then
	    return false;
	end if;
    end if;
    if assigned M`X then
	if not assigned other`X then
	    return false;
	end if;
	if M`X ne
	   other`X then
	    return false;
	end if;
    end if;
    if assigned M`mestre then
	if not assigned other`mestre then
	    return false;
	end if;
	if M`mestre ne
	   other`mestre then
	    return false;
	end if;
    end if;
    if assigned M`qeigenform then
	if not assigned other`qeigenform then
	    return false;
	end if;
	if M`qeigenform ne
	   other`qeigenform then
	    return false;
	end if;
    end if;
    if assigned M`qexpbasis then
	if not assigned other`qexpbasis then
	    return false;
	end if;
	if M`qexpbasis ne
	   other`qexpbasis then
	    return false;
	end if;
    end if;
    if assigned M`qintbasis then
	if not assigned other`qintbasis then
	    return false;
	end if;
	if M`qintbasis ne
	   other`qintbasis then
	    return false;
	end if;
    end if;
    if assigned M`field_embedding then
	if not assigned other`field_embedding then
	    return false;
	end if;
	if M`field_embedding ne
	   other`field_embedding then
	    return false;
	end if;
    end if;
    if assigned M`eigenvector_in_terms_of_integral_basis then
	if not assigned other`eigenvector_in_terms_of_integral_basis then
	    return false;
	end if;
	if M`eigenvector_in_terms_of_integral_basis ne
	   other`eigenvector_in_terms_of_integral_basis then
	    return false;
	end if;
    end if;
    if assigned M`eigenvector_in_terms_of_expansion_basis then
	if not assigned other`eigenvector_in_terms_of_expansion_basis then
	    return false;
	end if;
	if M`eigenvector_in_terms_of_expansion_basis ne
	   other`eigenvector_in_terms_of_expansion_basis then
	    return false;
	end if;
    end if;
    if assigned M`eigen then
	if not assigned other`eigen then
	    return false;
	end if;
	if M`eigen ne
	   other`eigen then
	    return false;
	end if;
    end if;
    if assigned M`eigenplus then
	if not assigned other`eigenplus then
	    return false;
	end if;
	if M`eigenplus ne
	   other`eigenplus then
	    return false;
	end if;
    end if;
    if assigned M`eigenminus then
	if not assigned other`eigenminus then
	    return false;
	end if;
	if M`eigenminus ne
	   other`eigenminus then
	    return false;
	end if;
    end if;
    if assigned M`eigenint then
	if not assigned other`eigenint then
	    return false;
	end if;
	if M`eigenint ne
	   other`eigenint then
	    return false;
	end if;
    end if;
    if assigned M`one_over_ei then
	if not assigned other`one_over_ei then
	    return false;
	end if;
	if M`one_over_ei ne
	   other`one_over_ei then
	    return false;
	end if;
    end if;
    if assigned M`modular_kernel then
	if not assigned other`modular_kernel then
	    return false;
	end if;
	if M`modular_kernel ne
	   other`modular_kernel then
	    return false;
	end if;
    end if;
    if assigned M`modular_degree then
	if not assigned other`modular_degree then
	    return false;
	end if;
	if M`modular_degree ne
	   other`modular_degree then
	    return false;
	end if;
    end if;
    if assigned M`congruence_group then
	if not assigned other`congruence_group then
	    return false;
	end if;
	if M`congruence_group ne
	   other`congruence_group then
	    return false;
	end if;
    end if;
    if assigned M`is_new then
	if not assigned other`is_new then
	    return false;
	end if;
	if M`is_new ne
	   other`is_new then
	    return false;
	end if;
    end if;
    if assigned M`is_p_new then
	if not assigned other`is_p_new then
	    return false;
	end if;
	if M`is_p_new ne
	   other`is_p_new then
	    return false;
	end if;
    end if;
    if assigned M`is_cuspidal then
	if not assigned other`is_cuspidal then
	    return false;
	end if;
	if M`is_cuspidal ne
	   other`is_cuspidal then
	    return false;
	end if;
    end if;
    if assigned M`is_eisenstein then
	if not assigned other`is_eisenstein then
	    return false;
	end if;
	if M`is_eisenstein ne
	   other`is_eisenstein then
	    return false;
	end if;
    end if;
    if assigned M`is_irreducible then
	if not assigned other`is_irreducible then
	    return false;
	end if;
	if M`is_irreducible ne
	   other`is_irreducible then
	    return false;
	end if;
    end if;
    if assigned M`scaled_rational_period_map then
	if not assigned other`scaled_rational_period_map then
	    return false;
	end if;
	if M`scaled_rational_period_map ne
	   other`scaled_rational_period_map then
	    return false;
	end if;
    end if;
    if assigned M`period_lattice then
	if not assigned other`period_lattice then
	    return false;
	end if;
	if M`period_lattice ne
	   other`period_lattice then
	    return false;
	end if;
    end if;
    if assigned M`real_volume then
	if not assigned other`real_volume then
	    return false;
	end if;
	if M`real_volume ne
	   other`real_volume then
	    return false;
	end if;
    end if;
    if assigned M`minus_volume then
	if not assigned other`minus_volume then
	    return false;
	end if;
	if M`minus_volume ne
	   other`minus_volume then
	    return false;
	end if;
    end if;
    if assigned M`c_inf then
	if not assigned other`c_inf then
	    return false;
	end if;
	if M`c_inf ne
	   other`c_inf then
	    return false;
	end if;
    end if;
    if assigned M`c_inf_minus then
	if not assigned other`c_inf_minus then
	    return false;
	end if;
	if M`c_inf_minus ne
	   other`c_inf_minus then
	    return false;
	end if;
    end if;
    if assigned M`PeriodGens then
	if not assigned other`PeriodGens then
	    return false;
	end if;
	if M`PeriodGens ne
	   other`PeriodGens then
	    return false;
	end if;
    end if;
    if assigned M`RatPeriodMap then
	if not assigned other`RatPeriodMap then
	    return false;
	end if;
	if M`RatPeriodMap ne
	   other`RatPeriodMap then
	    return false;
	end if;
    end if;
    if assigned M`RatPeriodLat then
	if not assigned other`RatPeriodLat then
	    return false;
	end if;
	if M`RatPeriodLat ne
	   other`RatPeriodLat then
	    return false;
	end if;
    end if;
    if assigned M`RatPeriodConj then
	if not assigned other`RatPeriodConj then
	    return false;
	end if;
	if M`RatPeriodConj ne
	   other`RatPeriodConj then
	    return false;
	end if;
    end if;
    if assigned M`RatPeriodMapSign then
	if not assigned other`RatPeriodMapSign then
	    return false;
	end if;
	if M`RatPeriodMapSign ne
	   other`RatPeriodMapSign then
	    return false;
	end if;
    end if;
    if assigned M`PeriodMap then
	if not assigned other`PeriodMap then
	    return false;
	end if;
	if M`PeriodMap ne
	   other`PeriodMap then
	    return false;
	end if;
    end if;
    if assigned M`PeriodMapPrecision then
	if not assigned other`PeriodMapPrecision then
	    return false;
	end if;
	if M`PeriodMapPrecision ne
	   other`PeriodMapPrecision then
	    return false;
	end if;
    end if;
    if assigned M`L_ratios then
	if not assigned other`L_ratios then
	    return false;
	end if;
	if M`L_ratios ne
	   other`L_ratios then
	    return false;
	end if;
    end if;
    if assigned M`L_ratios_odd then
	if not assigned other`L_ratios_odd then
	    return false;
	end if;
	if M`L_ratios_odd ne
	   other`L_ratios_odd then
	    return false;
	end if;
    end if;
    if assigned M`ZxZalp then
	if not assigned other`ZxZalp then
	    return false;
	end if;
	if M`ZxZalp ne
	   other`ZxZalp then
	    return false;
	end if;
    end if;
    if assigned M`VolLEven then
	if not assigned other`VolLEven then
	    return false;
	end if;
	if M`VolLEven ne
	   other`VolLEven then
	    return false;
	end if;
    end if;
    if assigned M`VolLOdd then
	if not assigned other`VolLOdd then
	    return false;
	end if;
	if M`VolLOdd ne
	   other`VolLOdd then
	    return false;
	end if;
    end if;
    if assigned M`compgrp_orders then
	if not assigned other`compgrp_orders then
	    return false;
	end if;
	if M`compgrp_orders ne
	   other`compgrp_orders then
	    return false;
	end if;
    end if;
    if assigned M`tamagawa_numbers then
	if not assigned other`tamagawa_numbers then
	    return false;
	end if;
	if M`tamagawa_numbers ne
	   other`tamagawa_numbers then
	    return false;
	end if;
    end if;
    if assigned M`xdata then
	if not assigned other`xdata then
	    return false;
	end if;
	if M`xdata ne
	   other`xdata then
	    return false;
	end if;
    end if;
    if assigned M`component_group_image then
	if not assigned other`component_group_image then
	    return false;
	end if;
	if M`component_group_image ne
	   other`component_group_image then
	    return false;
	end if;
    end if;
    if assigned M`int_pairing then
	if not assigned other`int_pairing then
	    return false;
	end if;
	if M`int_pairing ne
	   other`int_pairing then
	    return false;
	end if;
    end if;
    if assigned M`al_decomp then
	if not assigned other`al_decomp then
	    return false;
	end if;
	if M`al_decomp ne
	   other`al_decomp then
	    return false;
	end if;
  end if;

  return true;
end function;

function real_index(modsymList, M)
    for idx in [1..#modsymList] do
	if real_eq(modsymList[idx], M) then
	    return idx;
	end if;
    end for;
    return 0;
end function;

procedure modsymListSerialize(~modsymList, ~serList)
  M := modsymList[#serList + 1];
  data := [* *];
  if assigned M`eps then
      data_char_grp_elt_array := [* *];
      
      for key in Keys(M`eps`Parent`EltArray) do
	  elt := M`eps`Parent`EltArray[key];
	  data_elt := [*
		   < "BASERING", elt`BaseRing>,
		   < "ELEMENT", Eltseq(elt`Element)>,
		   < "MODULUS", elt`Modulus>
		   *];
	  if assigned elt`Conductor then
	      Append(~data_elt, < "CONDUCTOR", elt`Conductor >);
	  end if;
	  if assigned elt`GaussSum then
	      Append(~data_elt, < "GAUSSSUM", elt`GaussSum>);
	  end if;
	  if assigned elt`ValueList then
	      Append(~data_elt, < "VALUELIST", elt`ValueList>);
	  end if;
	  Append(~data_char_grp_elt_array, < Eltseq(key), data_elt>);
      end for;
      
      data_char_group := [*
			  < "ABGRP", M`eps`Parent`AbGrp >,
			  < "BASERING", M`eps`Parent`BaseRing >,
			  < "ELTARRAY", data_char_grp_elt_array >,
			  < "EXPONENT", M`eps`Parent`Exponent >,
			  < "LABELS" , M`eps`Parent`Labels >,
			  < "MODULUS", M`eps`Parent`Modulus >,
			  < "ORDEROFROOT", M`eps`Parent`OrderOfRoot >,
			  < "ORDERSGENS", M`eps`Parent`OrdersGens >,
			  < "ORDERSUGROUP",
			    M`eps`Parent`OrdersUGroup >,
			  < "POWERSOFROOT",
			    M`eps`Parent`PowersOfRoot >,
			  < "ROOTOF1", M`eps`Parent`RootOf1 >,
			  < "VALSATMINUS1",
			    M`eps`Parent`ValsAtMinus1 >
			  *];
      if assigned M`eps`Parent`AbGrpMap then
	  Append(~data_char_group,
		 < "ABGRPMAP", M`eps`Parent`AbGrpMap >);
      end if;
      if assigned M`eps`Parent`DecompositionParents then
	  Append(~data_char_group,
		 < "DECOMPOSITIONPARENTS",
		   M`eps`Parent`DecompositionParents >);
      end if;
      if assigned M`eps`Parent`Elements then
	  Append(~data_char_group, < "ELEMENTS",
				     M`eps`Parent`Elements >);
      end if;
      if assigned M`eps`Parent`Images then
	  Append(~data_char_group, < "IMAGES", M`eps`Parent`Images >);
      end if;
      if assigned M`eps`Parent`NF then
	  Append(~data_char_group, < "NF", M`eps`Parent`NF >);
      end if;
      if assigned M`eps`Parent`Pairing then
	  Append(~data_char_group, < "PAIRING",
				     M`eps`Parent`Pairing >);
      end if;
      if assigned M`eps`Parent`Residue_map then
	  Append(~data_char_group, < "RESIDUE_MAP",
				     M`eps`Parent`Residue_map >);
      end if;
      if assigned M`eps`Parent`Zeta then
	  Append(~data_char_group, < "ZETA", M`eps`Parent`Zeta >);
      end if;
      data_eps := [*
		   < "BASERING", M`eps`BaseRing>,
		   < "ELEMENT", Eltseq(M`eps`Element)>,
		   < "MODULUS", M`eps`Modulus>,
		   < "PARENT", data_char_group >
		   *];
      if assigned M`eps`Conductor then
	  Append(~data_eps, < "CONDUCTOR", M`eps`Conductor>);
      end if;
      if assigned M`eps`GaussSum then
	  Append(~data_eps, < "GAUSSSUM", M`eps`GaussSum>);
      end if;
      if assigned M`eps`ValueList then
	  Append(~data_eps, < "VALUELIST", M`eps`ValueList>);
      end if;
      Append(~data, < "EPSILON", data_eps >);
  end if;
  
  if assigned M`multi then
      Append(~data, < "MULTI", M`multi >);
  end if;
  if assigned M`is_multi then
      Append(~data, < "IS_MULTI", M`is_multi >);
  end if;
  if assigned M`multi_modsymgens then
      Append(~data, < "MULTI_MODSYMGENS", M`multi_modsymgens >);
  end if;
  if assigned M`multi_quo_maps then
      Append(~data, < "MULTI_QUO_MAPS", M`multi_quo_maps >);
  end if;
  if assigned M`MC_ModSymBasis_raw then
      Append(~data, < "MC_MODSYMBASIS_RAW", M`MC_ModSymBasis_raw >);
  end if;
  if assigned M`associated_newform_space then
      Append(~data,
	     < "ASSOCIATED_NEWFORM_SPACE",
	       M`associated_newform_space >);
  end if;
  if assigned M`isgamma1 then
      Append(~data, < "ISGAMMA1", M`isgamma1 >);
  end if;
  if assigned M`isgamma then
      Append(~data, < "ISGAMMA", M`isgamma >);
  end if;
  data cat:= [*
	      < "K", M`k >,
	      < "SIGN", M`sign >
	      *];
  if assigned M`hecke_bound then
      Append(~data, < "HECKE_BOUND", M`hecke_bound >);
  end if;
  if assigned M`root then
      idx := real_index(modsymList, M`root);
      if idx eq 0 then
	  Append(~modsymList, M`root);
	  idx := #modsymList;
      end if;
      Append(~data, < "ROOT", idx >);
  end if;
  data cat:= [*
	      < "IS_AMBIENT_SPACE", M`is_ambient_space >
	      *];
  if assigned M`creator then
      idx := real_index(modsymList, M`creator);
      if idx eq 0 then
	  Append(~modsymList, M`creator);
	  idx := #modsymList;
      end if;
      Append(~data, < "CREATOR", idx >);
  end if;
  if assigned M`other_levels then
      data_other_levels := [* *];
      for other_level in M`other_levels do
	  idx := real_index(modsymList, other_level[2]);
	  if idx eq 0 then
	      Append(~modsymList, other_level[2]);
	      idx := #modsymList;
	  end if;
	  Append(~data_other_levels, < other_level[1], idx >);
      end for;
      Append(~data, < "OTHER_LEVELS", data_other_levels >);
  end if;
  if assigned M`mlist then
      Append(~data, < "MLIST", M`mlist >);
  end if;
  if assigned M`quot then
      Append(~data, < "QUOT", M`quot >);
  end if;
  if assigned M`N then
      Append(~data, <"N", M`N >);
  end if;
  if assigned M`dual_representation then
      Append(~data, < "DUAL_REPRESENTATION", M`dual_representation >);
  end if;
  data cat:= [*
	      < "DIMENSION", M`dimension >,
	      < "F", M`F >,
	      < "SUB_REPRESENTATION", M`sub_representation >
	      *];
  if assigned M`sub_cuspidal_representation then
      Append(~data,
	     < "SUB_CUSPIDAL_REPRESENTATION",
	       M`sub_cuspidal_representation >);
  end if;
  if assigned M`dual_cuspidal_representation then
      Append(~data,
	     < "DUAL_CUSPIDAL_REPRESENTATION",
	       M`dual_cuspidal_representation >);
  end if;
  if assigned M`sub_integral_representation then
      Append(~data,
	     < "SUB_INTEGRAL_REPRESENTATION",
	       M`sub_integral_representation >);
  end if;
  if assigned M`dual_integral_representation then
      Append(~data,
	     < "DUAL_INTEGRAL_REPRESENTATION",
	       M`dual_integral_representation >);
  end if;
  if assigned M`sub_integral_cuspidal_representation then
      Append(~data,
	     < "SUB_INTEGRAL_CUSPIDAL_REPRESENTATION",
	       M`sub_integral_cuspidal_representation >);
  end if;
  if assigned M`dual_integral_cuspidal_representation then
      Append(~data,
	     < "DUAL_INTEGRAL_CUSPIDAL_REPRESENTATION",
	       M`dual_integral_cuspidal_representation >);
  end if;
  if assigned M`newform_decomposition then
      data_newform_decomposition := [];
      for d in M`newform_decomposition do
	  idx := real_index(modsymList, d);
	  if idx eq 0 then
	      Append(~modsymList, d);
	      idx := #modsymList;
	  end if;
	  Append(~data_newform_decomposition, idx);
      end for;
      Append(~data,
	     < "NEWFORM_DECOMPOSITION",
	       data_newform_decomposition > );
  end if;
  if assigned M`decomposition then
      Append(~data, < "DECOMPOSITION", M`decomposition >);
  end if;
  if assigned M`complement then
      Append(~data, < "COMPLEMENT", M`complement >);
  end if;
  if assigned M`cuspidal_part then
      idx := real_index(modsymList, M`cuspidal_part);
      if idx eq 0 then
	  Append(~modsymList, M`cuspidal_part);
	  idx := #modsymList;
      end if;
      Append(~data, < "CUSPIDAL_PART", idx >);
  end if;
  if assigned M`eisenstein_part then
      idx := real_index(modsymList, M`eisenstein_part);
      if idx eq 0 then
	  Append(~modsymList, M`eisenstein_part);
	  idx := #modsymList;
      end if;
      Append(~data, < "EISENSTEIN_PART", idx >); 
  end if;
  if assigned M`plus_part_sub then
      idx := real_index(modsymList, M`plus_part_sub);
      if idx eq 0 then
	  Append(~modsymList, M`plus_part_sub);
	  idx := #modsymList;
      end if;
      Append(~data, < "PLUS_PART_SUB", idx >);
  end if;
  if assigned M`plus_part_dual then
      idx := real_index(modsymList, M`plus_part_dual);
      if idx eq 0 then
	  Append(~modsymList, M`plus_part_dual);
	  idx := #modsymList;
      end if;
      Append(~data, < "PLUS_PART_DUAL", idx >);
  end if;
  if assigned M`minus_part_sub then
      idx := real_index(modsymList, M`minus_part_sub);
      if idx eq 0 then
	  Append(~modsymList, M`minus_part_sub);
	  idx := #modsymList;
      end if;
      Append(~data, < "MINUS_PART_SUB", idx >);
  end if;
  if assigned M`minus_part_dual then
      idx := real_index(modsymList, M`minus_part_dual);
      if idx eq 0 then
	  Append(~modsymList, M`minus_part_dual);
	  idx := #modsymList;
      end if;
      Append(~data, < "MINUS_PART_DUAL", idx >);
  end if;
  if assigned M`plus_subspace then
      idx := real_index(modsymList, M`plus_subspace);
      if idx eq 0 then
	  Append(~modsymList, M`plus_subspace);
	  idx := #modsymList;
      end if;
      Append(~data, < "PLUS_SUBSPACE", idx >);
  end if;
  if assigned M`minus_subspace then
      idx := real_index(modsymList, M`minus_subspace);
      if idx eq 0 then
	  Append(~modsymList, M`minus_subspace);
	  idx := #modsymList;
      end if;
      Append(~data, < "MINUS_SUBSPACE", idx >);
  end if;
  if assigned M`new_part then
      idx := real_index(modsymList, M`new_part);
      if idx eq 0 then
	  Append(~modsymList, M`new_part);
	  idx := #modsymList;
      end if;
      Append(~data, < "NEW_PART", idx >);
  end if;
  if assigned M`old_part then
      idx := real_index(modsymList, M`old_part);
      if idx eq 0 then
	  Append(~modsymList, M`old_part);
	  idx := #modsymList;
      end if;
      Append(~data, < "OLD_PART", idx >);
  end if;
  if assigned M`p_new_part then
      Append(~data, < "P_NEW_PART", M`p_new_part >);
  end if;
  if assigned M`modsym_basis then
      printf "This is in modsym %o\n", M;
      printf "Its index is %o\n", #serList + 1;
      data_modsym_basis := [];
      for v in M`modsym_basis do
	  data_v := [];
	  for symb in v do
	      X := Parent(symb[1]).1;
	      _, f := IsUnivariate(Evaluate(symb[1], <X,1>));
	      Append(~data_v, < Coefficients(f), symb[2] >);
	  end for;
	  Append(~data_modsym_basis, data_v);
      end for;
      Append(~data, < "MODSYM_BASIS", data_modsym_basis >);
  end if;
  if assigned M`associated_new_space then
      Append(~data, < "ASSOCIATED_NEW_SPACE",
		      M`associated_new_space >);
  end if;
  if assigned M`star_involution then
      Append(~data, < "STAR_INVOLUTION", M`star_involution >);
  end if;
  if assigned M`dual_star_involution then
      Append(~data, < "DUAL_STAR_INVOLUTION",
		      M`dual_star_involution >);
  end if;
  if assigned M`discriminant then
      Append(~data, < "DISCRIMINANT", M`discriminant >);
  end if;
  if assigned M`discriminant_Q then
      Append(~data, < "DISCRIMINANT_Q", M`discriminant_Q >);
  end if;
  if assigned M`winding then
      Append(~data, < "WINDING", M`winding >);
  end if;
  if assigned M`twisted_winding then
      Append(~data, < "TWISTED_WINDING", M`twisted_winding >);
  end if;
  if assigned M`twisted_winding_index then
      Append(~data, < "TWISTED_WINDING_INDEX",
		      M`twisted_winding_index >);
  end if;
  if assigned M`boundary_map then
      Append(~data, < "BOUNDARY_MAP", M`boundary_map >);
  end if;
  if assigned M`cusplist then
      Append(~data, < "CUSPLIST", M`cusplist >);
  end if;
  if assigned M`heilbronn_cremona then
      Append(~data, < "HEILBRONN_CREMONA", M`heilbronn_cremona >);
  end if;
  if assigned M`heilbronn_merel then
      Append(~data, < "HEILBRONN_MEREL", M`heilbronn_merel >);
  end if;
  if assigned M`atkin_lehner then
      Append(~data, < "ATKIN_LEHNER", M`atkin_lehner >);
  end if;
  if assigned M`dual_atkin_lehner then
      Append(~data, < "DUAL_ATKIN_LEHNER", M`dual_atkin_lehner >);
  end if;
  if assigned M`hecke_operator then
      Append(~data, < "HECKE_OPERATOR", M`hecke_operator >);
  end if;
  if assigned M`hecke_operator_proj_data then
      Append(~data, < "HECKE_OPERATOR_PROJ_DATA",
		      M`hecke_operator_proj_data >);
  end if;
  if assigned M`dual_hecke_operator then
      Append(~data, < "DUAL_HECKE_OPERATOR", M`dual_hecke_operator >);
  end if;
  if assigned M`projection_matrix then
      Append(~data, < "PROJECTION_MATRIX", M`projection_matrix >);
  end if;
  if assigned M`standard_images then
      Append(~data, < "STANDARD_IMAGES", M`standard_images >);
  end if;
  if assigned M`standard_images_all then
      Append(~data, < "STANDARD_IMAGES_ALL", M`standard_images_all >);
  end if;
  if assigned M`degeneracy_matrices_out then
      Append(~data, < "DEGENERACY_MATRICES_OUT",
		      M`degeneracy_matrices_out >);
  end if;
  if assigned M`degeneracy_matrices_in then
      Append(~data, < "DEGENERACY_MATRICES_IN",
		      M`degeneracy_matrices_in >);
  end if;
  if assigned M`hecke_algebra then
      Append(~data, < "HECKE_ALGEBRA", M`hecke_algebra >);
  end if;
  if assigned M`hecke_algebra_over_q then
      Append(~data, < "HECKE_ALGEBRA_OVER_Q",
		      M`hecke_algebra_over_q >);
  end if;
  if assigned M`hecke_algebra_disc then
      Append(~data, < "HECKE_ALGEBRA_DISC", M`hecke_algebra_disc >);
  end if;
  if assigned M`hecke_eigenvalue_field then
      Append(~data, < "HECKE_EIGENVALUE_FIELD",
		      M`hecke_eigenvalue_field >);
  end if;
  if assigned M`hecke_eigenvalue_ring then
      Append(~data, < "HECKE_EIGENVALUE_RING",
		      M`hecke_eigenvalue_ring >);
  end if;
  if assigned M`hecke_algebra_z_basis then
      Append(~data, < "HECKE_ALGEBRA_Z_BASIS",
		      M`hecke_algebra_z_basis >);
  end if;
  if assigned M`inner_twists then
      Append(~data, < "INNER_TWISTS", M`inner_twists >);
  end if;
  if assigned M`action_on_modsyms then
      Append(~data, < "ACTION_ON_MODSYMS", M`action_on_modsyms >);
  end if;
  if assigned M`X then
      Append(~data, < "X", M`X >);
  end if;
  if assigned M`mestre then
      Append(~data, < "MESTRE", M`mestre >);
  end if;
  if assigned M`qeigenform then
      Append(~data, < "QEIGENFORM", M`qeigenform >);
  end if;
  if assigned M`qexpbasis then
      Append(~data, < "QEXPBASIS", M`qexpbasis >);
  end if;
  if assigned M`qintbasis then
      Append(~data, < "QINTBASIS", M`qintbasis >);
  end if;
  if assigned M`field_embedding then
      Append(~data, < "FIELD_EMBEDDING", M`field_embedding >);
  end if;
  if assigned M`eigenvector_in_terms_of_integral_basis then
      Append(~data,
	     < "EIGENVECTOR_IN_TERMS_OF_INTEGRAL_BASIS",
	       M`eigenvector_in_terms_of_integral_basis >);
  end if;
  if assigned M`eigenvector_in_terms_of_expansion_basis then
      Append(~data,
	     < "EIGENVECTOR_IN_TERMS_OF_EXPANSION_BASIS",
	       M`eigenvector_in_terms_of_expansion_basis >);
  end if;
  if assigned M`eigen then
      Append(~data, < "EIGEN", M`eigen >);
  end if;
  if assigned M`eigenplus then
      Append(~data, < "EIGENPLUS", M`eigenplus >);
  end if;
  if assigned M`eigenminus then
      Append(~data, < "EIGENMINUS", M`eigenminus >);
  end if;
  if assigned M`eigenint then
      Append(~data, < "EIGENINT", M`eigenint >);
  end if;
  if assigned M`one_over_ei then
      Append(~data, < "ONE_OVER_EI", M`one_over_ei >);
  end if;
  if assigned M`modular_kernel then
      Append(~data, < "MODULAR_KERNEL", M`modular_kernel >);
  end if;
  if assigned M`modular_degree then
      Append(~data, < "MODULAR_DEGREE", M`modular_degree >);
  end if;
  if assigned M`congruence_group then
      Append(~data, < "CONGRUENCE_GROUP", M`congruence_group >);
  end if;
  if assigned M`is_new then
      Append(~data, < "IS_NEW", M`is_new >);
  end if;
  if assigned M`is_p_new then
      Append(~data, < "IS_P_NEW", M`is_p_new >);
  end if;
  if assigned M`is_cuspidal then
      Append(~data, < "IS_CUSPIDAL", M`is_cuspidal >);
  end if;
  if assigned M`is_eisenstein then
      Append(~data, < "IS_EISENSTEIN", M`is_eisenstein >);
  end if;
  if assigned M`is_irreducible then
      Append(~data, < "IS_IRREDUCIBLE", M`is_irreducible >);
  end if;
  if assigned M`scaled_rational_period_map then
      Append(~data, < "SCALED_RATIONAL_PERIOD_MAP",
		      M`scaled_rational_period_map >);
  end if;
  if assigned M`period_lattice then
      Append(~data, < "PERIOD_LATTICE", M`period_lattice >);
  end if;
  if assigned M`real_volume then
      Append(~data, < "REAL_VOLUME", M`real_volume >);
  end if;
  if assigned M`minus_volume then
      Append(~data, < "MINUS_VOLUME", M`minus_volume >);
  end if;
  if assigned M`c_inf then
      Append(~data, < "C_INF", M`c_inf >);
  end if;
  if assigned M`c_inf_minus then
      Append(~data, < "C_INF_MINUS", M`c_inf_minus >);
  end if;
  if assigned M`PeriodGens then
      Append(~data, < "PERIODGENS", M`PeriodGens >);
  end if;
  if assigned M`RatPeriodMap then
      Append(~data, < "RATPERIODMAP", M`RatPeriodMap >);
  end if;
  if assigned M`RatPeriodLat then
      Append(~data, < "RATPERIODLAT", M`RatPeriodLat >);
  end if;
  if assigned M`RatPeriodConj then
      Append(~data, < "RATPERIODCONJ", M`RatPeriodConj >);
  end if;
  if assigned M`RatPeriodMapSign then
      Append(~data, < "RATPERIODMAPSIGN", M`RatPeriodMapSign >);
  end if;
  if assigned M`PeriodMap then
      Append(~data, < "PERIODMAP", M`PeriodMap >);
  end if;
  if assigned M`PeriodMapPrecision then
      Append(~data, < "PERIODMAPPRECISION", M`PeriodMapPrecision >);
  end if;
  if assigned M`L_ratios then
      Append(~data, < "L_RATIOS", M`L_ratios >);
  end if;
  if assigned M`L_ratios_odd then
      Append(~data, < "L_RATIOS_ODD", M`L_ratios_odd >);
  end if;
  if assigned M`ZxZalp then
      Append(~data, < "ZXZALP", M`ZxZalp >);
  end if;
  if assigned M`VolLEven then
      Append(~data, < "VOLLEVEN", M`VolLEven >);
  end if;
  if assigned M`VolLOdd then
      Append(~data, < "VOLLODD", M`VolLOdd >);
  end if;
  if assigned M`compgrp_orders then
      Append(~data, < "COMPGRP_ORDERS", M`compgrp_orders >);
  end if;
  if assigned M`tamagawa_numbers then
      Append(~data, < "TAMAGAWA_NUMBERS", M`tamagawa_numbers >);
  end if;
  if assigned M`xdata then
      Append(~data, < "XDATA", M`xdata >);
  end if;
  if assigned M`component_group_image then
      Append(~data, < "COMPONENT_GROUP_IMAGE",
		      M`component_group_image >);
  end if;
  if assigned M`int_pairing then
      Append(~data, < "INT_PAIRING", M`int_pairing >);
  end if;
  if assigned M`al_decomp then
      Append(~data, < "AL_DECOMP", M`al_decomp >);
  end if;
  
  Append(~serList, data);
  
end procedure;

intrinsic Serialize(M::ModSym) -> SeqEnum[List]
{.}
  modsymList := [M];
  serList := [];
  while #serList ne #modsymList do
      modsymListSerialize(~modsymList, ~serList);
  end while;
  
  return serList;
end intrinsic;

procedure UnpackModSym(~modsymArr ,dataSeq, idx)

  printf "unpacking modular symbols space at index %o..\n", idx;

  data := dataSeq[idx];
  // An associative array which stores the appropriate meta data.
  array := AssociativeArray();

  // Store meta data.
  for entry in data do array[entry[1]] := entry[2]; end for;

  M := New(ModSym);
  modsymArr[idx] := M;

  if IsDefined(array, "EPSILON") then
      data_eps := array["EPSILON"];
      array_eps := AssociativeArray();
      for entry in data_eps do array_eps[entry[1]] := entry[2]; end for;

      data_eps_parent := array_eps["PARENT"];
      array_eps_parent := AssociativeArray();
      for entry in data_eps_parent do
	  array_eps_parent[entry[1]] := entry[2];
      end for;

      M`eps := New(GrpDrchElt);
      M`eps`BaseRing := array_eps["BASERING"];
      M`eps`Modulus := array_eps["MODULUS"];

      M`eps`Parent := New(GrpDrch);
      M`eps`Parent`AbGrp := array_eps_parent["ABGRP"];
      M`eps`Parent`BaseRing := array_eps_parent["BASERING"];
      
      M`eps`Parent`Exponent := array_eps_parent["EXPONENT"];
      M`eps`Parent`Labels := array_eps_parent["LABELS"];
      M`eps`Parent`Modulus := array_eps_parent["MODULUS"];
      M`eps`Parent`OrderOfRoot := array_eps_parent["ORDEROFROOT"];
      M`eps`Parent`OrdersGens := array_eps_parent["ORDERSGENS"];
      M`eps`Parent`OrdersUGroup := array_eps_parent["ORDERSUGROUP"];
      M`eps`Parent`PowersOfRoot := array_eps_parent["POWERSOFROOT"];
      M`eps`Parent`RootOf1 :=
	  M`eps`Parent`BaseRing!(array_eps_parent["ROOTOF1"]);
      M`eps`Parent`UGroup, M`eps`Parent`UnitsMap :=
	  UnitGroup(Integers(M`eps`Modulus));
      M`eps`Element := M`eps`Parent`UGroup!(array_eps["ELEMENT"]);

      M`eps`Parent`EltArray := AssociativeArray();
      for entry in array_eps_parent["ELTARRAY"] do
	  data_elt := entry[2];
	  array_elt := AssociativeArray();
	  for elt_entry in data_elt do
	      array_elt[elt_entry[1]] := elt_entry[2];
	  end for;
	  elt := New(GrpDrchElt);
	  elt`BaseRing := array_elt["BASERING"];
	  elt`Modulus := array_elt["MODULUS"];
	  elt`Parent := M`eps`Parent;
	  elt`Element := M`eps`Parent`UGroup!(array_elt["ELEMENT"]);
	  
	  if IsDefined(array_elt, "CONDUCTOR") then
	      elt`Conductor := array_elt["CONDUCTOR"];
	  end if;
	  if IsDefined(array_elt, "GAUSSSUM") then
	      elt`GaussSum := array_elt["GAUSSSUM"];
	  end if;
	  if IsDefined(array_elt, "VALUELIST") then
	      elt`ValueList := array_elt["VALUELIST"];
	  end if;
      
	  M`eps`Parent`EltArray[M`eps`Parent`AbGrp!(entry[1])] := elt;
      end for;
      
      M`eps`Parent`ValsAtMinus1 := array_eps_parent["VALSATMINUS1"];
      if IsDefined(array_eps_parent, "ZETA") then
	  M`eps`Parent`Zeta := array_eps_parent["ZETA"];
      end if;
      if IsDefined(array_eps_parent, "RESIDUE_MAP") then
	  M`eps`Parent`Residue_map := array_eps_parent["RESIDUE_MAP"];
      end if;
      if IsDefined(array_eps_parent, "PAIRING") then
	  M`eps`Parent`Pairing := array_eps_parent["PAIRING"];
      end if;
      if IsDefined(array_eps_parent, "ABGRPMAP") then
	  M`eps`Parent`AbGrpMap := array_eps_parent["ABGRPMAP"];
      end if;
      if IsDefined(array_eps_parent, "DECOMPOSITIONPARENTS") then
	  M`eps`Parent`DecompositionParents :=
	      array_eps_parent["DECOMPOSITIONPARENTS"];
      end if;
      if IsDefined(array_eps_parent, "ELEMENTS") then
	  M`eps`Parent`Elements := array_eps_parent["ELEMENTS"];
      end if;
      if IsDefined(array_eps_parent, "IMAGES") then
	  M`eps`Parent`Images := array_eps_parent["Images"];
      end if;
      if IsDefined(array_eps_parent, "NF") then
	  M`eps`Parent`NF := array_eps_parent["NF"];
      end if;

      if IsDefined(array_eps, "CONDUCTOR") then
	  M`eps`Conductor := array_eps["CONDUCTOR"];
      end if;
      if IsDefined(array_eps, "GAUSSSUM") then
	  M`eps`GaussSum := array_eps["GAUSSSUM"];
      end if;
      if IsDefined(array_eps, "VALUELIST") then
	  M`eps`ValueList := array_eps["VALUELIST"];
      end if;
  end if; // IsDefined(array, "EPSILON")
  
  if IsDefined(array, "MULTI") then
      M`multi := array["MULTI"];
  end if;
  if IsDefined(array, "IS_MULTI") then
      M`is_multi := array["IS_MULTI"];
  end if;
  if IsDefined(array, "MULTI_MODSYMGENS") then
      M`multi_modsymgens := array["MULTI_MODSYMGENS"];
  end if;
  if IsDefined(array, "MULTI_QUO_MAPS") then
      M`multi_quo_maps := array["MULTI_QUO_MAPS"];
  end if;
  if IsDefined(array, "MC_MODSYMBASIS_RAW") then
      M`MC_ModSymBasis_raw := array["MC_MODSYMBASIS_RAW"];
  end if;
  if IsDefined(array, "ASSOCIATED_NEWFORM_SPACE") then
      M`associated_newform_space := array["ASSOCIATED_NEWFORM_SPACE"];
  end if;
  if IsDefined(array, "ISGAMMA1") then
      M`isgamma1 := array["ISGAMMA1"];
  end if;
  if IsDefined(array, "ISGAMMA") then
      M`isgamma := array["ISGAMMA"];
  end if;

  M`k := array["K"];
  M`sign := array["SIGN"];

  if IsDefined(array, "HECKE_BOUND") then
      M`hecke_bound := array["HECKE_BOUND"];
  end if;
  if IsDefined(array, "ROOT") then
      if array["ROOT"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["ROOT"]);
      end if;
      M`root := modsymArr[array["ROOT"]];
  end if;

  M`is_ambient_space := array["IS_AMBIENT_SPACE"];

  if IsDefined(array, "CREATOR") then
      if array["CREATOR"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["CREATOR"]);
      end if;
      M`creator := modsymArr[array["CREATOR"]];
  end if;

  if IsDefined(array, "OTHER_LEVELS") then
      M`other_levels := [* *];
      for other_level in array["OTHER_LEVELS"] do
	  if other_level[2] notin Keys(modsymArr) then
	      UnpackModSym(~modsymArr, dataSeq, other_level[2]);
	  end if;
	  Append(~M`other_levels, < other_level[1],
				    modsymArr[other_level[2]] >);
      end for;
  end if;

  if IsDefined(array, "MLIST") then
      M`mlist := array["MLIST"];
  end if;
  if IsDefined(array, "QUOT") then
      M`quot := array["QUOT"];
  end if;
  M`dimension := array["DIMENSION"];
  if IsDefined(array, "N") then
      M`N := array["N"];
  end if;
  M`F := array["F"];
  M`sub_representation := array["SUB_REPRESENTATION"];
  if IsDefined(array, "DUAL_REPRESENTATION") then
      M`dual_representation := array["DUAL_REPRESENTATION"];
  end if;
  
  if IsDefined(array, "SUB_CUSPIDAL_REPRESENTATION") then
      M`sub_cuspidal_representation :=
	  array["SUB_CUSPIDAL_REPRESENTATION"];
  end if;
  if IsDefined(array, "DUAL_CUSPIDAL_REPRESENTATION") then
      M`dual_cuspidal_representation :=
	  array["DUAL_CUSPIDAL_REPRESENTATION"];
  end if;
  if IsDefined(array, "SUB_INTEGRAL_REPRESENTATION") then
      M`sub_integral_representation :=
	  array["SUB_INTEGRAL_REPRESENTATION"];
  end if;
  if IsDefined(array, "DUAL_INTEGRAL_REPRESENTATION") then
      M`dual_integral_representation :=
	  array["DUAL_INTEGRAL_REPRESENTATION"];
  end if;
  if IsDefined(array, "SUB_INTEGRAL_CUSPIDAL_REPRESENTATION") then
      M`sub_integral_cuspidal_representation :=
	  array["SUB_INTEGRAL_CUSPIDAL_REPRESENTATION"];
  end if;
  if IsDefined(array, "DUAL_INTEGRAL_CUSPIDAL_REPRESENTATION") then
      M`dual_integral_cuspidal_representation :=
	  array["DUAL_INTEGRAL_CUSPIDAL_REPRESENTATION"];
  end if;

  if IsDefined(array, "NEWFORM_DECOMPOSITION") then
      M`newform_decomposition := [];
      for idx in array["NEWFORM_DECOMPOSITION"] do
	  if idx notin Keys(modsymArr) then
	      UnpackModSym(~modsymArr, dataSeq, idx);
	  end if;
	  Append(~M`newform_decomposition, modsymArr[idx]);
      end for;
  end if;
  if IsDefined(array, "DECOMPOSITION") then
      M`decomposition := array["DECOMPOSITION"];
  end if;
  if IsDefined(array, "COMPLEMENT") then
      M`complement := array["COMPLEMENT"];
  end if;
  if IsDefined(array, "CUSPIDAL_PART") then
      if array["CUSPIDAL_PART"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["CUSPIDAL_PART"]);
      end if;
      M`cuspidal_part := modsymArr[array["CUSPIDAL_PART"]];
  end if;
  if IsDefined(array, "EISENSTEIN_PART") then
      if array["EISENSTEIN_PART"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["EISENSTEIN_PART"]);
      end if;
      M`eisenstein_part := modsymArr[array["EISENSTEIN_PART"]];
  end if;
  if IsDefined(array, "PLUS_PART_SUB") then
      if array["PLUS_PART_SUB"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["PLUS_PART_SUB"]);
      end if;
      M`plus_part_sub := modsymArr[array["PLUS_PART_SUB"]];
  end if;
  if IsDefined(array, "PLUS_PART_DUAL") then
      if array["PLUS_PART_DUAL"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["PLUS_PART_DUAL"]);
      end if;
      M`plus_part_dual := modsymArr[array["PLUS_PART_DUAL"]];
  end if;
  if IsDefined(array, "MINUS_PART_SUB") then
      if array["MINUS_PART_SUB"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["MINUS_PART_SUB"]);
      end if;
      M`minus_part_sub := modsymArr[array["MINUS_PART_SUB"]];
  end if;
  if IsDefined(array, "MINUS_PART_DUAL") then
      if array["MINUS_PART_DUAL"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["MINUS_PART_DUAL"]);
      end if;
      M`minus_part_dual := modsymArr[array["MINUS_PART_DUAL"]];
  end if;
  if IsDefined(array, "PLUS_SUBSPACE") then
      if array["PLUS_SUBSPACE"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["PLUS_SUBSPACE"]);
      end if;
      M`plus_subspace := modsymArr[array["PLUS_SUBSPACE"]];
  end if;
  if IsDefined(array, "MINUS_SUBSPACE") then
      if array["MINUS_SUBSPACE"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["MINUS_SUBSPACE"]);
      end if;
      M`minus_subspace := modsymArr[array["MINUS_SUBSPACE"]];
  end if;
  if IsDefined(array, "NEW_PART") then
      if array["NEW_PART"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["NEW_PART"]);
      end if;
      M`new_part := modsymArr[array["NEW_PART"]];
  end if;
  if IsDefined(array, "OLD_PART") then
      if array["OLD_PART"] notin Keys(modsymArr) then
	  UnpackModSym(~modsymArr, dataSeq, array["OLD_PART"]);
      end if;
      M`old_part := modsymArr[array["OLD_PART"]];
  end if;
  if IsDefined(array, "P_NEW_PART") then
      M`p_new_part := array["P_NEW_PART"];
  end if;
  if IsDefined(array, "MODSYM_BASIS") then
      M`modsym_basis := [];
      for v in array["MODSYM_BASIS"] do
	  v_poly := [];
	  for symb in v do
	      R := Universe(symb[1]);
	      R_XY<X,Y> := PolynomialRing(R,2);
	      f := &+[ symb[1][i] * X^(i-1) * Y^(#symb[1] - i) :
		       i in [1..#symb[1]]];
	      Append(~v_poly, <f, symb[2]>);
	  end for;
	  Append(~M`modsym_basis, v_poly);
      end for;
  end if;
  if IsDefined(array, "ASSOCIATED_NEW_SPACE") then
      M`associated_new_space := array["ASSOCIATED_NEW_SPACE"];
  end if;
  if IsDefined(array, "STAR_INVOLUTION") then
      M`star_involution := array["STAR_INVOLUTION"];
  end if;
  if IsDefined(array, "DUAL_STAR_INVOLUTION") then
      M`dual_star_involution := array["DUAL_STAR_INVOLUTION"];
  end if;
  if IsDefined(array, "DISCRIMINANT") then
      M`discriminant := array["DISCRIMINANT"];
  end if;
  if IsDefined(array, "DISCRIMINANT_Q") then
      M`discriminant_Q := array["DISCRIMINANT_Q"];
  end if;
  if IsDefined(array, "WINDING") then
      M`winding := array["WINDING"];
  end if;
  if IsDefined(array, "TWISTED_WINDING") then
      M`twisted_winding := array["TWISTED_WINDING"];
  end if;
  if IsDefined(array, "TWISTED_WINDING_INDEX") then
      M`twisted_winding_index := array["TWISTED_WINDING_INDEX"];
  end if;
  if IsDefined(array, "BOUNDARY_MAP") then
      M`boundary_map := array["BOUNDARY_MAP"];
  end if;
  if IsDefined(array, "CUSPLIST") then
      M`cusplist := array["CUSPLIST"];
  end if;
  if IsDefined(array, "HEILBRONN_CREMONA") then
      M`heilbronn_cremona := array["HEILBRONN_CREMONA"];
  end if;
  if IsDefined(array, "HEILBRONN_MEREL") then
      M`heilbronn_merel := array["HEILBRONN_MEREL"];
  end if;
  if IsDefined(array, "ATKIN_LEHNER") then
      M`atkin_lehner := array["ATKIN_LEHNER"];
  end if;
  if IsDefined(array, "DUAL_ATKIN_LEHNER") then
      M`dual_atkin_lehner := array["DUAL_ATKIN_LEHNER"];
  end if;
  if IsDefined(array, "HECKE_OPERATOR") then
      M`hecke_operator := array["HECKE_OPERATOR"];
  end if;
  if IsDefined(array, "HECKE_OPERATOR_PROJ_DATA") then
      M`hecke_operator_proj_data := array["HECKE_OPERATOR_PROJ_DATA"];
  end if;
  if IsDefined(array, "DUAL_HECKE_OPERATOR") then
      M`dual_hecke_operator := array["DUAL_HECKE_OPERATOR"];
  end if;
  if IsDefined(array, "PROJECTION_MATRIX") then
      M`projection_matrix := array["PROJECTION_MATRIX"];
  end if;
  if IsDefined(array, "STANDARD_IMAGES") then
      M`standard_images := array["STANDARD_IMAGES"];
  end if;
  if IsDefined(array, "STANDARD_IMAGES_ALL") then
      M`standard_images_all := array["STANDARD_IMAGES_ALL"];
  end if;
  if IsDefined(array, "DEGENERACY_MATRICES_OUT") then
      M`degeneracy_matrices_out := array["DEGENERACY_MATRICES_OUT"];
  end if;
  if IsDefined(array, "DEGENERACY_MATRICES_IN") then
      M`degeneracy_matrices_in := array["DEGENERACY_MATRICES_IN"];
  end if;
  if IsDefined(array, "HECKE_ALGEBRA") then
      M`hecke_algebra := array["HECKE_ALGEBRA"];
  end if;
  if IsDefined(array, "HECKE_ALGEBRA_OVER_Q") then
      M`hecke_algebra_over_q := array["HECKE_ALGEBRA_OVER_Q"];
  end if;
  if IsDefined(array, "HECKE_ALGEBRA_DISC") then
      M`hecke_algebra_disc := array["HECKE_ALGEBRA_DISC"];
  end if;
  if IsDefined(array, "HECKE_EIGENVALUE_FIELD") then
      M`hecke_eigenvalue_field := array["HECKE_EIGENVALUE_FIELD"];
  end if;
  if IsDefined(array, "HECKE_EIGENVALUE_RING") then
      M`hecke_eigenvalue_ring := array["HECKE_EIGENVALUE_RING"];
  end if;
  if IsDefined(array, "HECKE_ALGEBRA_Z_BASIS") then
      M`hecke_algebra_z_basis := array["HECKE_ALGEBRA_Z_BASIS"];
  end if;
  if IsDefined(array, "INNER_TWISTS") then
      M`inner_twists := array["INNER_TWISTS"];
  end if;
  if IsDefined(array, "ACTION_ON_MODSYMS") then
      M`action_on_modsyms := array["ACTION_ON_MODSYMS"];
  end if;
  if IsDefined(array, "X") then
      M`X := array["X"];
  end if;
  if IsDefined(array, "MESTRE") then
      M`mestre := array["MESTRE"];
  end if;
  if IsDefined(array, "QEIGENFORM") then
      M`qeigenform := array["QEIGENFORM"];
  end if;
  if IsDefined(array, "QEXPBASIS") then
      M`qexpbasis := array["QEXPBASIS"];
  end if;
  if IsDefined(array, "QINTBASIS") then
      M`qintbasis := array["QINTBASIS"];
  end if;
  if IsDefined(array, "FIELD_EMBEDDING") then
      M`field_embedding := array["FIELD_EMBEDDING"];
  end if;
  if IsDefined(array, "EIGENVECTOR_IN_TERMS_OF_INTEGRAL_BASIS") then
      M`eigenvector_in_terms_of_integral_basis :=
	  "EIGENVECTOR_IN_TERMS_OF_INTEGRAL_BASIS";
  end if;
  if IsDefined(array, "EIGENVECTOR_IN_TERMS_OF_EXPANSION_BASIS") then
      M`eigenvector_in_terms_of_exapnsion_basis :=
	  "EIGENVECTOR_IN_TERMS_OF_EXPANSION_BASIS";
  end if;
  if IsDefined(array, "EIGEN") then
      M`eigen := array["EIGEN"];
  end if;
  if IsDefined(array, "EIGENPLUS") then
      M`eigenplus := array["EIGENPLUS"];
  end if;
  if IsDefined(array, "EIGENMINUS") then
      M`eigenminus := array["EIGENMINUS"];
  end if;
  if IsDefined(array, "EIGENINT") then
      M`eigenint := array["EIGENINT"];
  end if;
  if IsDefined(array, "ONE_OVER_EI") then
      M`one_over_ei := array["ONE_OVER_EI"];
  end if;
  if IsDefined(array, "MODULAR_KERNEL") then
      M`modular_kernel := array["MODULAR_KERNEL"];
  end if;
  if IsDefined(array, "MODULAR_DEGREE") then
      M`modular_degree := array["MODULAR_DEGREE"];
  end if;
  if IsDefined(array, "CONGRUENCE_GROUP") then
      M`congruence_group := array["CONGRUENCE_GROUP"];
  end if;
  if IsDefined(array, "IS_NEW") then
      M`is_new := array["IS_NEW"];
  end if;
  if IsDefined(array, "IS_P_NEW") then
      M`is_p_new := array["IS_P_NEW"];
  end if;
  if IsDefined(array, "IS_CUSPIDAL") then
      M`is_cuspidal := array["IS_CUSPIDAL"];
  end if;
  if IsDefined(array, "IS_EISENSTEIN") then
      M`is_eisenstein := array["IS_EISENSTEIN"];
  end if;
  if IsDefined(array, "IS_IRREDUCIBLE") then
      M`is_irreducible := array["IS_IRREDUCIBLE"];
  end if;
  if IsDefined(array, "SCALED_RATIONAL_PERIOD_MAP") then
      M`scaled_rational_period_map := array["SCALED_RATIONAL_PERIOD_MAP"];
  end if;
  if IsDefined(array, "PERIOD_LATTICE") then
      M`period_lattice := array["PERIOD_LATTICE"];
  end if;
  if IsDefined(array, "REAL_VOLUME") then
      M`real_volume := array["REAL_VOLUME"];
  end if;
  if IsDefined(array, "MINUS_VOLUME") then
      M`minus_volume := array["MINUS_VOLUME"];
  end if;
  if IsDefined(array, "C_INF") then
      M`c_inf := array["C_INF"];
  end if;
  if IsDefined(array, "C_INF_MINUS") then
      M`c_inf_minus := array["C_INF_MINUS"];
  end if;
  if IsDefined(array, "PERIODGENS") then
      M`PeriodGens := array["PERIODGENS"];
  end if;
  if IsDefined(array, "RATPERIODMAP") then
      M`RatPeriodMap := array["RATPERIODMAP"];
  end if;
  if IsDefined(array, "RATPERIODLAT") then
      M`RatPeriodLat := array["RATPERIODLAT"];
  end if;
  if IsDefined(array, "RATPERIODCONJ") then
      M`RatPeriodConj := array["RATPERIODCONJ"];
  end if;
  if IsDefined(array, "RATPERIODMAPSIGN") then
      M`RatPeriodMapSign := array["RATPERIODMAPSIGN"];
  end if;
  if IsDefined(array, "PERIODMAP") then
      M`PeriodMap := array["PERIODMAP"];
  end if;
  if IsDefined(array, "PERIODMAPPRECISION") then
      M`PeriodMapPrecision := array["PERIODMAPPRECISION"];
  end if;
  if IsDefined(array, "L_RATIOS") then
      M`L_ratios := array["L_RATIOS"];
  end if;
  if IsDefined(array, "L_RATIOS_ODD") then
      M`L_ratios_odd := array["L_RATIOS_ODD"];
  end if;
  if IsDefined(array, "ZXZALP") then
      M`ZxZalp := array["ZXZALP"];
  end if;
  if IsDefined(array, "VOLLEVEN") then
      M`VolLEven := array["VOLLEVEN"];
  end if;
  if IsDefined(array, "VOLLODD") then
      M`VolLOdd := array["VOLLODD"];
  end if;
  if IsDefined(array, "COMPGRP_ORDERS") then
      M`compgrp_orders := array["COMPGRP_ORDERS"];
  end if;
  if IsDefined(array, "TAMAGAWA_NUMBERS") then
      M`tamagawa_numbers := array["TAMAGAWA_NUMBERS"];
  end if;
  if IsDefined(array, "XDATA") then
      M`xdata := array["XDATA"];
  end if;
  if IsDefined(array, "COMPONENT_GROUP_IMAGE") then
      M`component_group_image := array["COMPONENT_GROUP_IMAGE"];
  end if;
  if IsDefined(array, "INT_PAIRING") then
      M`int_pairing := array["INT_PAIRING"];
  end if;
  if IsDefined(array, "AL_DECOMP") then
      M`al_decomp := array["AL_DECOMP"];
  end if;
	  
end procedure;

intrinsic Save(M::ModSym, filename::MonStgElt : Overwrite := false)
{ Save data to disk. }
	// The file where the data will be stored.
	file := path() cat filename;

	// If overwrite flag not set and file exists, display warning and
	//  immediately return.
	if not Overwrite and FileExists(file : ShowErrors := false) then
		print "WARNING: File not saved. Set the Overwrite parameter.";
		return;
	end if;

	// Build the data structure that will be saved to file.
	data := Serialize(M);

	// Write data to file.
	Write(file, data, "Magma" : Overwrite := Overwrite);
		  
end intrinsic;

// This could be made more efficient by using the same list
// for all spaces, at the moment we do not care

intrinsic Save(D::SeqEnum[ModSym], filename::MonStgElt : Overwrite := false)
{ Save data to disk. }
	// The file where the data will be stored.
	file := path() cat filename;

	// If overwrite flag not set and file exists, display warning and
	//  immediately return.
	if not Overwrite and FileExists(file : ShowErrors := false) then
		print "WARNING: File not saved. Set the Overwrite parameter.";
		return;
	end if;

	// Build the data structure that will be saved to file.
	data := [ Serialize(M) : M in D];

	// Write data to file.
	Write(file, data, "Magma" : Overwrite := Overwrite);
		  
end intrinsic;

intrinsic LoadModSym(filename::MonStgElt : ShowErrors := true) -> ModSym
{.}
  file := path() cat filename;
  // If file does not exist, display errors (if requested) and return.
  if not FileExists(file : ShowErrors := ShowErrors) then
      return false;
  end if;

  // The raw data from the file.
  str := Read(file);

  data := eval str;

  modsymArr := AssociativeArray([1..#data]);

  printf "Read data containing %o modular symbols spaces..\n", #data;
  
  UnpackModSym(~modsymArr, data, 1);

  return modsymArr[1];
end intrinsic;

intrinsic LoadModSymSeq(filename::MonStgElt : ShowErrors := true) -> SeqEnum[ModSym]
{.}
  file := path() cat filename;
  // If file does not exist, display errors (if requested) and return.
  if not FileExists(file : ShowErrors := ShowErrors) then
      return false;
  end if;

  // The raw data from the file.
  str := Read(file);

  dataSeq := eval str;

  printf "Read data containing %o modular symbols spaces..\n", #dataSeq;

  ret := [];
  for data in dataSeq do
      printf "Read data containing %o modular symbols spaces..\n", #data;
      modsymArr := AssociativeArray([1..#data]);
      UnpackModSym(~modsymArr, data, 1);
      Append(~ret, modsymArr[1]);
  end for;
  
  return ret;
end intrinsic;

intrinsic FileExists(filename::MonStgElt : ShowErrors := true) -> BoolElt
{ Checks whether a specified file exists on disk. }
	try
		// Attempt to open the file for reading.
		ptr := Open(filename, "r");

		// Delete the pointer, thereby closing the file stream (see
		//  Magma documentation for Open intrinsic).
		ptr := [];
	catch e
		if ShowErrors then
			print "ERROR: File does not exist!";
		end if;
		return false;
	end try;

	return true;
end intrinsic;

function getNewSpaceStages(level, weight, char_order : prec := 100)
    prec := Min(prec, NextPrime(997) - 1);
    chi := MakeCharacter(level, char_order);
    SetVerbose("ModularSymbols", 2);
    M := ModularSymbols(chi, weight);
    M_name := Sprintf("full_modsym_%o_%o_%o.dat",
		      level, weight, char_order);
    Save(M, M_name : Overwrite := true);
    M := LoadModSym(M_name);
    S := CuspidalSubspace(M);
    S_name := Sprintf("cuspidal_modsym_%o_%o_%o.dat",
		      level, weight, char_order);
    Save(S, S_name : Overwrite := true);
    S := LoadModSym(S_name);
    Snew := NewSubspace(S);
    Snew_name := Sprintf("new_modsym_%o_%o_%o.dat",
			 level, weight, char_order);
    Save(Snew, Snew_name : Overwrite := true);
    Snew := LoadModSym(Snew_name);
    D := NewformDecomposition(Snew);
    Save(Snew, Snew_name : Overwrite := true);
    Snew := LoadModSym(Snew_name);
    ret := [* qEigenform(d, prec) : d in D *];
    Save(Snew, Snew_name : Overwrite := true);
    return ret;
end function;

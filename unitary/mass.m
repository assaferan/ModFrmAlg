intrinsic UnitaryMass(L,m) -> Lat
  {Returns an approximation to the mass of principal genus of Hermitian ZZ_L lattices.}

 ZZ_L := MaximalOrder(L);
  _,cc := HasComplexConjugate(L);
  F := sub<L|[L.1+cc(L.1)]>;
  ZZ_F := MaximalOrder(F);
  d := Degree(L) div 2;
  tau := 2;
  chars := ArtinRepresentations(L);
  I := [i : i in [1..#chars] | Type(F!!chars[i]) eq RngIntElt];
  J := [j : j in [1..#chars] | j notin I];
  Ls := [&*[LSeries(chi) : chi in chars[J]], &*[LSeries(chi) : chi in chars[I]]];
    // If chi is the character of L/F, then Lodd is the L(chi^odd) and Leven is L(chi^even).
  LofM := &*[Evaluate(Ls[(r mod 2)+1],1-r) : r in [1..m]];
  if m mod 2 eq 0 then
    prod_of_local_factors := 1;
  else 
    RF := &cat[[x[1] : x in Factorization(p*ZZ_F)] : p in PrimeFactors(Discriminant(ZZ_L))];                                                 
    RL := [Factorization(ideal<ZZ_L|Generators(I)>)[1,1] : I in RF]; 
    N := #[I : I in RF | Factorization(ideal<ZZ_L|Generators(I)>)[1,2] gt 1];
    prod_of_local_factors := (1/2)^N;
  end if;

  mass := 1/2^(m*d)*LofM*tau*prod_of_local_factors;
  return mass;
end intrinsic;


intrinsic NeighborVectors(Lambda::ModDed, 
			       P::RngOrdIdl,
 			   Pbar ::RngOrdIdl) -> SeqEnum
  {vectors needed for neighbor construction}

  ZZ_L := BaseRing(Lambda);
  d := Dimension(Lambda);
  kP, redP := ResidueClassField(P);
  pibar := Generators(Pbar)[#Generators(Pbar)];
  n := Dimension(Lambda);

  if assigned Lambda`almost_basis then
    almost_basis := Lambda`almost_basis;
  else
    pbLambda := PseudoBasis(Lambda);
    almost_basis := [Generators(pb[1])[#Generators(pb[1])]*pb[2] : pb in pbLambda];
    Lambda`almost_basis := almost_basis;
  end if;

  A := [Random([a : a in Generators(I[1]) | Valuation(a,P) eq Valuation(I[1],P)]) : I in pbLambda];
  B := [A[i]*pbLambda[i,2] : i in [1..#pbLambda]];

  V := RSpace(kP,n);
    
  if assigned Lambda`LatticeAutomorphismGroup then
    G := Lambda`LatticeAutomorphismGroup;
    GLgens := [PullUp(Matrix(g),Lambda,Lambda) : g in Generators(G)];
  else
    G := LatticeAutomorphismGroup(Lambda);
    Lambda`LatticeAutomorphismGroup := G;
    GLgens := [PullUp(Matrix(g),Lambda,Lambda) : g in Generators(G)]; 
  end if;

  M := Parent(GLgens[1]);
  B := M!Basis(Lambda);

  Pdminusone := RationalPoints(ProjectiveSpace(kP,d-1));  
  lifts := [[t@@redP : t in Eltseq(x)] : x in Pdminusone];
  vectors := [&+[x[i]*almost_basis[i] : i in [1..d]] : x in lifts];
  ans := [pibar*v : v in vectors];
  
  return ans;
end intrinsic;








intrinsic NeighborVectors(Lambda::ModDed, 
			       P::RngOrdIdl,
 			   Pbar ::RngOrdIdl) -> SeqEnum
  {vectors needed for neighbor construction}

  
  ZZ_L := BaseRing(Lambda);
  d := Degree(ZZ_L);
  n := Dimension(Lambda);
  kP, redP := ResidueClassField(P);
  pibar := Generators(Pbar)[#Generators(Pbar)];

  A := [Random([a : a in Generators(I[1]) | Valuation(a,P) eq Valuation(I[1],P)]) : I in pbLambda];
    // i-th component of A is generates I_i/P*I_i, where I_i is the i-th coefficient ideal of Lambda
  B := [A[i]*pbLambda[i,2] : i in [1..#pbLambda]];
  Pdminusone := [Eltseq(x) : x in RationalPoints(ProjectiveSpace(kP,d-1))];  
  R1 := [&+[x[i]@@redP*B[i] : i in [1..n]] : x in Pdminusone];
  R2 := [x : x in R1 | &+[y*ComplexConjugate(y) : y in Eltseq(x)] in P];
  T := [Random([b : b in Basis(Lambda) | &+[x[i]*ComplexConjugate(b[i]) : i in [1..n]] notin P]) : x in R2];
  pi := Random([x : x in Generators(P) | x notin P^2]);
  Y := [x@@redP : x in kP];
  X := [R2[i] + pi*y*T[i] : i in [1..#R2], y in Y];
  lifts := [[t@@redP : t in Eltseq(x)] : x in Pdminusone];
  vectors := [&+[x[i]*almost_basis[i] : i in [1..d]] : x in lifts];
  ans := [pibar*v : v in vectors];
  
  return ans;
end intrinsic;



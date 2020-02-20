Attach("hackobj.m");
Attach("hgenus.m");
Attach("moddedhlat.m");

L := CyclotomicField(5);
ZZ_L := MaximalOrder(L);
Lambda := Module(ZZ_L,4);
Lambda`AmbientSpace := EmbeddingSpace(Lambda);
LambdaZZ := Lattice(Lambda);

P := Factorization(11*ZZ_L)[1,1];
Pbar := ComplexConjugate(P);



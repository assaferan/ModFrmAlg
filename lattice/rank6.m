import "canonical_form.m" : satspan;

function createRank6Lattice(D)
    lat_db := LatticeDatabase();
    E8 := Lattice(lat_db, "E8");
    K := QuadraticField(-D);
    ZK := Integers(K);
    ZK_gram := Matrix([[Norm(x+y)-Norm(x)-Norm(y) : x in Basis(ZK)] 
		       : y in Basis(ZK)]);
    assert ZK_gram[1,1] eq 2;
    E8_len_2 := ShortVectors(E8,2,2); 
    E8_len_w := ShortVectors(E8,ZK_gram[2,2],ZK_gram[2,2]);
    found := false;
    for v in E8_len_2 do
	found := exists(w){w : w in E8_len_w | (v[1],w[1]) eq 1};
	if found then 
	    vecs := [v[1],w[1]];
	    break; 
	end if;
    end for;
    assert found;
    ZK_lat_emb := sub<E8|vecs>;
    V := QuadraticSpace(1/2*GramMatrix(E8));
    V_ZK_lat := sub<V|Basis(ZK_lat_emb)>;
    V_orth := OrthogonalComplement(V, V_ZK_lat);
    lam := satspan(Basis(V_orth),ChangeRing(GramMatrix(E8),Rationals()));
    L := GramMatrix(lam);
    assert Determinant(L) eq D;
    return L;
end function;

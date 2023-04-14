procedure TestTheta1Single(N, k, prec)
    Q := TernaryQuadraticLattices(N^2)[1];
    M := OrthogonalModularForms(Q,[k,0]);
    num_eis := (k eq 0) select 1 else 0;
    if (Dimension(M) gt num_eis) then
	fs := HeckeEigenforms(M);
	for j in [num_eis+1..#fs] do
	    f := HeckeEigenforms(M)[j];
	    theta := Theta1(f : Precision := prec^2);
	    if IsZero(theta) then continue; end if;
	    lift := ShimuraLift(theta, 2*(k+1), N : Precision := prec);
	    // !!! TODO - can we make them match also when p divides N ?
	    coeffs := [Coefficient(lift, i) : i in [1..prec-1] | GCD(i,N) eq 1];
	    // Check that it is in the right space
	    nfs := Newforms(ModularForms(N, 2*(k+1)));
	    found := false;
	    idxs := [0,0];
	    for idx1 in [1..#nfs] do
		for idx2 in [1..#nfs[idx1]] do
		    nfs_coeffs := [Coefficient(nfs[idx1][idx2],i) :
                                   i in [1..prec-1] | GCD(i,N) eq 1];
		    F1 := Universe(coeffs);
		    F2 := Universe(nfs_coeffs);
		    if (Type(F1) ne FldRat) and (Type(F2) ne FldRat) then
			is_isom, phi := IsIsomorphic(F1, F2);
		    else
			is_isom := IsIsomorphic(F1,F2);
			phi := Automorphisms(Rationals())[1];
		    end if;
		    if (is_isom) then
			auts := Automorphisms(Universe(coeffs));
			for aut in auts do
			    nfs_coeffs_emb := [phi(aut(x)) : x in nfs_coeffs];
			    if coeffs eq nfs_coeffs_emb then
				found := true;
				idxs := [idx1, idx2];
				break;
			    end if;
			end for;
		    end if;
		    if found then break; end if;
		end for;
		if found then break; end if;
	    end for;
	    assert found;
	    // Verify L-functions
	    nf := nfs[idxs[1]][idxs[2]];
	    assert &and[Coefficient(nf,p) eq HeckeEigenvalue(f,p)*p^k
			: p in PrimesUpTo(prec-1) | N mod p ne 0];
	end for;
    end if;    
end procedure;

procedure TestTheta1(prec)
    // Here we test the lift from Yoshida's paper
    printf "Testing theta lifts from [Y]...";
    for N in [2,11] do
	printf "N=%o,k=", N;
	for k in [0..6] do
	    printf "%o ", k;
	    TestTheta1Single(N,k,prec);
	end for;
    end for;
    return;
end procedure;

TestTheta1(25);

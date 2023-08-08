G_type := [<61,1,1,2>, <69,1,1,2>, <73,1,1,3>, <76,3,38,1>, <79,1,1,2>,
	   <82,1,82,1>, <85,1,1,3>, <87,1,1,2>, <89,1,1,4>, <91,1,91,1>,
	   <93,1,1,3>, <94,1,1,2>, <94,1,94,1>, <96,4,1,6>, <97,1,1,2>];

procedure testLSer(form_data, prec)
    N, gen, d, idx := Explode(form_data);
    Q := QuinaryQuadraticLattices(N)[gen][1];
    M := OrthogonalModularForms(Q : Special, d := d);
    fs := HeckeEigenforms(M);
    f := fs[idx];
    lser := LSeries(f : Precision := prec);
    eps := 10^(-prec);
    assert CFENew(lser) lt eps;
    return;
end procedure;

prec := 5;
printf "N=...";
for form in G_type do
    printf "%o,", form[1];
    testLSer(form, prec);
end for;
printf("\n");

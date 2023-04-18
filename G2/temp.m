import "./neighbors/neighbor-CN1.m" : BuildNeighbor, BuildNeighborProc, GetNextNeighbor;

// Functions for working with Cayley octonions
function bar(x)
    return Vector([Conjugate(x[1]), -x[2]]);
end function;

function prod(x,y)
    return Vector([x[1]*y[1] - Conjugate(y[2])*x[2], y[2]*x[1] + x[2]*Conjugate(y[1])]);
end function;

function cross_product(x,y)
    return 1/2*(prod(x,y) - prod(y,x));
end function;

function norm(x)
    n := prod(x, bar(x));
    assert n[2] eq 0;
    assert n[1] in Rationals();
    return Rationals()!n[1];
end function;

// an example - discriminant 1
B := QuaternionAlgebra(Rationals(), -1, -1);

// What happens when we change the discriminant of B ??

// Basis for the Octonions
e := [Vector([x,0]) : x in Basis(B)] cat [Vector([0,x]) : x in Basis(B)];

// Basis for the space perpendicular to (1,0)
e := e[2..#e];

// Multiplication lines for the octonions
lines := [[1,2,3],[6,1,7],[7,2,5],[5,3,6],[5,4,1],[6,4,2],[7,4,3]];
signs := CartesianPower([-1,1],4);

// Doubly Hurwitz octonions
dHurwitz := &cat[[1/2*(sign[1]*Vector([1,0]) + &+[sign[i+1]*e[line[i]] : i in [1..3]]) : sign in signs] : line in lines];

// The lattice of double Hurwitz octonions
dHurwitz_lat := Lattice(Matrix([Eltseq(g[1]) cat Eltseq(g[2]) : g in dHurwitz]));

// Kirmse's "integral" octonions
Kirmse := [Vector([B!Eltseq(b)[1..4],B!Eltseq(b)[5..8]]) : b in Basis(dHurwitz_lat)];

// Here we decided to swap 1,2 - but any swap of 1 with something would do
Cayley := [Vector([B![Eltseq(k[1])[j] : j in [2,1,3,4]], k[2]]) : k in Kirmse];

// verifications
// verifying that this is indeed an order

function is_order(gens)
    coeffs := Matrix([Eltseq(g[1]) cat Eltseq(g[2]) : g in gens]);
    lat := Lattice(coeffs);

    for i in [1..#gens] do
	for j in [1..#gens] do
	    g := prod(gens[i], gens[j]);
	    v := Vector(Eltseq(g[1]) cat Eltseq(g[2]));
	    if v notin lat then return false; end if;
	end for;
    end for;

    return true;
end function;

assert is_order(Cayley);

cayley_coeffs := Matrix([Eltseq(g[1]) cat Eltseq(g[2]) : g in Cayley]);
cayley_lat := Lattice(cayley_coeffs);

for i in [1..8] do
    for j in [1..8] do
	g := prod(Cayley[i], Cayley[j]);
	v := Vector(Eltseq(g[1]) cat Eltseq(g[2]));
	assert v in cayley_lat;
    end for;
end for;
// assert IsIsometric(cayley_lat, E8);

// The quadratic form
Q := Matrix([[norm(x+y)-norm(x) - norm(y) : x in Cayley] : y in Cayley]);
Q := ChangeRing(Q, Rationals());

assert Determinant(Q) eq 1;

// The auxiliary forms that we want to preserve
forms := [Matrix([[Solution(cayley_coeffs, Vector(Eltseq(prod(x,y)[1]) cat Eltseq(prod(x,y)[2])))[i] : x in Cayley] : y in Cayley]) : i in [1..8]];

M := OrthogonalModularForms(Q);
reps := Representatives(Genus(M));
basis_mats := [Matrix(Basis(Module(r))) : r in reps];

// We start by looking at 2-neighbors
p := 2;
nProc := BuildNeighborProc(Module(M), ideal<Integers() | p>, 1);

scaled_forms := [p*f : f in forms];
all_forms := [[basis_mats[i] * f * Transpose(basis_mats[i]) : f in scaled_forms] : i in [1..#reps]];
D := LCM([LCM([Denominator(f) : f in fforms]) : fforms in all_forms]);
all_forms := [[ChangeRing(D*f, Integers()) : f in fforms] : fforms in all_forms];
scaled_forms := all_forms[1];

while (nProc`isoSubspace ne []) do
      nLat := BuildNeighbor(nProc);
      basis_mat := Matrix(Basis(Module(nLat)));
      nforms := [ChangeRing(basis_mat * f * Transpose(basis_mat),Integers()) : f in scaled_forms];
      is_isom := exists(idx){i : i in [1..#reps] | IsIsometric(ZLattice(nLat), nforms, ZLattice(reps[i]), all_forms[i])};
      if not (is_isom) then
	  Append(~reps, nLat);
	  Append(~basis_mats, basis_mat);
	  Append(~all_forms, nforms);
      end if;
      GetNextNeighbor(~nProc);
end while;

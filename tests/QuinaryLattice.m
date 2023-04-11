// TODO : add Watson's construction of lattices corresponding to Dummigan-Pacetti-Tornaria-Rama

procedure testQuinaryLattice( : NumTimes := 5)
    printf "Testing the reading of quinary lattices from teh database doesn't crash...d=";
    ds := [Random([2..513]) : i in [1..NumTimes]];
    // These ones are at the end of their file and appeared to be problematic
    ds cat:= [256, 300];
    for d in ds do
	printf "%o ", d;
	Q := QuinaryQuadraticLattices(d);
    end for;
    return;
end procedure;

testQuinaryLattice();

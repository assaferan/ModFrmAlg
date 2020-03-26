
// Make newform 7.7.b.b in Magma, downloaded from the LMFDB on 23 March 2020.
function ConvertToHeckeField(input: pass_field := false, Kf := [])
    if not pass_field then
        poly := [*510, 0, 1*];
        Kf := NumberField(Polynomial([elt : elt in poly]));
        AssignNames(~Kf, ["nu"]);
    end if;
    Rf_num := [*\
[*1, 0*],
[*0, 2*]*];
    Rf_basisdens := [*\
1,
1*];
    Rf_basisnums := ChangeUniverse([[z : z in elt] : elt in Rf_num], Kf);
    Rfbasis := [Rf_basisnums[i]/Rf_basisdens[i] : i in [1..Degree(Kf)]];
    inp_vec := Vector(Rfbasis)*ChangeRing(Transpose(Matrix([[elt : elt in row] : row in input])),Kf);
    return Eltseq(inp_vec);
end function;


// To make the character of type GrpDrchElt, type "MakeCharacter_7_b();"
function MakeCharacter_7_b()
    N := 7;
    order := 2;
    char_gens := [*3*];
    v := [*\
1*];
    // chi(gens[i]) = zeta^v[i]
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    F := CyclotomicField(order);
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),[F|F.1^e:e in v]);
    return MinimalBaseRingCharacter(chi);
end function;

// To make the character of type GrpDrchElt with Codamain the HeckeField, type "MakeCharacter_7_b_Hecke();"
function MakeCharacter_7_b_Hecke(Kf)
    N := 7;
    order := 2;
    char_gens := [*3*];
    char_values := [*[*-1, 0*]*];
    assert SequenceToList(UnitGenerators(DirichletGroup(N))) eq char_gens;
    values := ConvertToHeckeField(char_values : pass_field := true, Kf := Kf); // the value of chi on the gens as elements in the Hecke field
    F := Universe(values);// the Hecke field
    chi := DirichletCharacterFromValuesOnUnitGenerators(DirichletGroup(N,F),values);
    return chi;
end function;


// To make the Hecke irreducible modular symbols subspace (type ModSym)
// containing the newform, type "MakeNewformModSym_7_7_b_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose line below.
function MakeNewformModSym_7_7_b_b()
    R<x> := PolynomialRing(Rationals());
    chi := MakeCharacter_7_b();
    // SetVerbose("ModularSymbols", true);
    Snew := NewSubspace(CuspidalSubspace(ModularSymbols(chi,7,-1)));
    Vf := Kernel([<2,R![8, 1]>],Snew);
    return Vf;
end function;


function ExtendMultiplicatively(weight, aps, character)
    prec := NextPrime(NthPrime(#aps)) - 1; // we will able to figure out a_0 ... a_prec
    primes := PrimesUpTo(prec);
    prime_powers := primes;
    assert #primes eq #aps;
    log_prec := Floor(Log(prec)/Log(2)); // prec < 2^(log_prec+1)
    F := Universe(aps);
    FXY<X, Y> := PolynomialRing(F, 2);
    // 1/(1 - a_p T + p^(weight - 1) * char(p) T^2) = 1 + a_p T + a_{p^2} T^2 + ...
    R<T> := PowerSeriesRing(FXY : Precision := log_prec + 1);
    recursion := Coefficients(1/(1 - X*T + Y*T^2));
    coeffs := [F!0: i in [1..(prec+1)]];
    coeffs[1] := 1; //a_1
    for i := 1 to #primes do
        p := primes[i];
        coeffs[p] := aps[i];
        b := p^(weight - 1) * F!character(p);
        r := 2;
        p_power := p * p;
        //deals with powers of p
        while p_power le prec do
            Append(~prime_powers, p_power);
            coeffs[p_power] := Evaluate(recursion[r + 1], [aps[i], b]);
            p_power *:= p;
            r +:= 1;
        end while;    
    end for;
    Sort(~prime_powers);
    for pp in prime_powers do
        for k := 1 to Floor(prec/pp) do
            if GCD(k, pp) eq 1 then
                coeffs[pp*k] := coeffs[pp]*coeffs[k];
            end if;
        end for;
    end for;
    return coeffs;
end function;


function qexpCoeffs()
    // To make the coeffs of the qexp of the newform in the Hecke field type "qexpCoeffs();"
    weight := 7;
    raw_aps := [*\
[*-8, 0*],
        [*0, 1*],
        [*0, -1*],
        [*133, 7*],
        [*874, 0*],
        [*0, 49*],
        [*0, -132*],
        [*0, 69*],
        [*4738, 0*],
        [*11146, 0*],
        [*0, -608*],
        [*3002, 0*],
        [*0, 1274*],
        [*31418, 0*],
        [*0, -1604*],
        [*-76406, 0*],
        [*0, 2507*],
        [*0, -6091*],
        [*495242, 0*],
        [*-184406, 0*],
        [*0, -1350*],
        [*-534934, 0*],
        [*0, -15827*],
        [*0, -13938*],
        [*0, 18032*],
        [*0, -43217*],
        [*0, 37582*],
        [*1616026, 0*],
        [*199226, 0*],
        [*-1807622, 0*],
        [*3324722, 0*],
        [*0, 69425*],
        [*2129266, 0*],
        [*0, -37289*],
        [*-2595734, 0*],
        [*-1685566, 0*],
        [*0, 81397*],
        [*1881914, 0*],
        [*0, -69874*],
        [*0, -50807*],
        [*3518458, 0*],
        [*0, -165669*],
        [*-7200278, 0*],
        [*-13088902, 0*],
        [*-9174758, 0*],
        [*0, -150282*],
        [*8400842, 0*],
        [*0, 108584*],
        [*0, 292657*],
        [*0, -7505*],
        [*4841458, 0*],
        [*-13729742, 0*],
        [*0, 81236*],
        [*0, 348243*],
        [*0, -167056*],
        [*-13205942, 0*],
        [*0, 353361*],
        [*0, -550068*],
        [*16001306, 0*],
        [*-603566, 0*],
        [*0, 491947*],
        [*0, -947905*],
        [*0, -890379*],
        [*0, 326306*],
        [*0, 928766*],
        [*43092202, 0*],
        [*-53220406, 0*],
        [*2345786, 0*],
        [*-48059558, 0*],
        [*0, 222509*],
        [*0, -1694216*],
        [*8397346, 0*],
        [*0, -84748*],
        [*-49383622, 0*],
        [*37456106, 0*],
        [*0, 1109240*],
        [*224986, 0*],
        [*0, 19305*],
        [*14490874, 0*],
        [*0, -2309306*],
        [*0, 1820105*],
        [*-13378006, 0*],
        [*-134244398, 0*],
        [*0, 2285556*],
        [*0, -588526*],
        [*131971594, 0*],
        [*147766306, 0*],
        [*-82286758, 0*],
        [*0, -2919959*],
        [*1399274, 0*],
        [*0, -401451*],
        [*0, -640688*],
        [*-94751518, 0*],
        [*-25883366, 0*],
        [*156023258, 0*],
        [*0, 2468130*],
        [*0, 1650389*],
        [*0, -4344654*],
        [*0, 1023063*],
        [*-75290566, 0*],
        [*72675962, 0*],
        [*-310740998, 0*],
        [*0, 1253981*],
        [*51730426, 0*],
        [*86876474, 0*],
        [*0, 1305984*],
        [*0, 6882295*],
        [*0, 7676388*],
        [*94777066, 0*],
        [*0, 4537694*],
        [*0, -7276088*],
        [*267966698, 0*],
        [*-388908518, 0*],
        [*0, 1396823*],
        [*-130826806, 0*],
        [*-71753606, 0*],
        [*0, -5669447*],
        [*0, 10917894*],
        [*155036314, 0*],
        [*-301682582, 0*],
        [*0, -3990293*],
        [*406264994, 0*],
        [*0, -393737*],
        [*-266054342, 0*],
        [*0, 5412245*],
        [*231727162, 0*],
        [*-309704662, 0*],
        [*0, -8533260*],
        [*0, 6950258*],
        [*0, -1589939*],
        [*27781466, 0*],
        [*-703366046, 0*],
        [*-300617038, 0*],
        [*117056522, 0*],
        [*0, -5834914*],
        [*0, -2782808*],
        [*0, -3505473*],
        [*0, 11418373*],
        [*0, 20577893*],
        [*-689730854, 0*],
        [*0, -633129*],
        [*-251151398, 0*],
        [*240085418, 0*],
        [*914380042, 0*],
        [*0, -11577579*],
        [*0, -20959946*],
        [*0, 5099675*],
        [*0, 961990*],
        [*0, 3567451*],
        [*256356778, 0*],
        [*247674986, 0*],
        [*0, -23382996*],
        [*-538571542, 0*],
        [*0, -2510614*],
        [*-458650774, 0*],
        [*600691954, 0*],
        [*719637386, 0*],
        [*0, 10271344*],
        [*0, -28098462*],
        [*0, 2348921*],
        [*360650506, 0*],
        [*1358094418, 0*],
        [*483871586, 0*],
        [*0, 6819063*],
        [*-233409758, 0*],
        [*0, 13342162*],
        [*1127722154, 0*],
        [*0, -25953913*]*];
    aps := ConvertToHeckeField(raw_aps);
    chi := MakeCharacter_7_b_Hecke(Universe(aps));
    return ExtendMultiplicatively(weight, aps, chi);
end function;


// To make the newform (type ModFrm), type "MakeNewformModFrm_7_7_b_b();".
// This may take a long time!  To see verbose output, uncomment the SetVerbose lines below.
function MakeNewformModFrm_7_7_b_b(:prec:=4)
    prec := Min(prec, NextPrime(997) - 1);
    chi := MakeCharacter_7_b();
    f_vec := qexpCoeffs();
    Kf := Universe(f_vec);
    f_vec := Vector(Kf, [0] cat [f_vec[i]: i in [1..prec]]);
    // SetVerbose("ModularForms", true);
    // SetVerbose("ModularSymbols", true);
    S := CuspidalSubspace(ModularForms(chi, 7));
    S := BaseChange(S, Kf);
    B := Basis(S, prec + 1);
    S_basismat := Matrix([AbsEltseq(g): g in B]);
    S_basismat := ChangeRing(S_basismat,Kf);
    f_lincom := Solution(S_basismat,f_vec);
    f := &+[f_lincom[i]*B[i] : i in [1..#B]];
    return f;
end function;

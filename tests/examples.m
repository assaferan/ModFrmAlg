freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma                          
                            Eran Assaf                                 
                                                                            
   FILE: examples.m (data for examples to test on)

   04/14/20: Created an array of examples to be exported.

   04/13/20: Added the orthogonal examples

   04/03/20: renamed from unitary-examples

 
 ***************************************************************************/

// to use the examples, simply import AlgebraicModularFormsExamples

ExampleRF := recformat< name : MonStgElt,
			group : MonStgElt,
		        field : Fld,
			inner_form : AlgMatElt,
			coeff_char : RngIntElt,
			genus : RngIntElt,
			weight : SeqEnum,
			norm_p : SeqEnum,
			timing : SeqEnum,
		        evs : SeqEnum>;

inner_form_7_2 := Matrix([[2,0,1],[0,2,0],[1,0,6]]);
ps_7_2 := PrimesUpTo(100);
eis_7_2 := [[* p eq 11 select 0 else p+1 : p in ps_7_2 *]];
cusp_7_2 := 
    [[* p eq 11 select 0 else
     Coefficient(Newforms(ModularForms(11))[1][1], p) : p in ps_7_2 *]];
Example_7_2 := rec< ExampleRF | name := "[GV2]_7_2",
				group := "Orthogonal",
				field := Rationals(),
				inner_form := inner_form_7_2,
				coeff_char := 0,
				genus := 2,
				weight := [0,0],
				norm_p := ps_7_2,
				timing := [],
				evs := [eis_7_2, cusp_7_2] >;

inner_form_7_3 := Matrix([[2,0,0,1],[0,2,1,0],[0,1,6,0],[1,0,0,6]]);
eis_7_3 := [[* x^2 : x in eis_7_2[1] *], [* 2*x*(x-1) : x in eis_7_2[1] *]];
a_7_3 := [[* x^2 : x in cusp_7_2[1] *],
	  [* ps_7_2[i] eq 11 select 0 else
	   2*(cusp_7_2[1][i]^2 - ps_7_2[i] - 1) : i in [1..#ps_7_2] *]];
b_7_3 := [[* cusp_7_2[1][i] * eis_7_2[1][i] : i in [1..#ps_7_2] *],
	  [*  ps_7_2[i] eq 11 select 0 else
	   cusp_7_2[1][i]^2 + ps_7_2[i]^2 - 1 : i in [1..#ps_7_2]  *] ];
Example_7_3 := rec< ExampleRF | name := "[GV2]_7_3",
				group := "Orthogonal",
				field := Rationals(),
				inner_form := inner_form_7_3,
				coeff_char := 0,
				genus := 3,
				weight := [0,0],
				norm_p := ps_7_2,
				timing := [],
				evs := [eis_7_3, a_7_3, b_7_3] >;

Example_7_4 := rec< ExampleRF | name := "[GV2]_7_4",
				group := "Unitary",
				field := QuadraticField(-7),
				inner_form := IdentityMatrix(
					QuadraticField(-7), 3),
				coeff_char := 0,
				genus := 2,
				weight := [0,0],
				norm_p := [2, 11, 23, 29, 37, 43,
					   53, 67, 71,
					   79, 107, 109, 113, 127, 137, 149,
					   151, 163, 179, 191, 193, 197],
				timing := [0.02, 0.07, 0.18, 0.28, 0.42,
					   0.57, 0.82, 1.35, 1.46, 1.86,
					   3.73, 4.18, 4.59, 5.85, 7.08,
					   8.56, 9.04, 10.88, 13.78, 16.92,
					   17.22, 17.29],
				evs := [[[* 7, 133, 553, 871, 1407, 1893,
					  2863,
					  4557, 5113, 6321, 11557, 11991,
					  12883,
					  16257, 18907, 22351, 22953, 26733,
					  32221, 36673, 37443, 39007 *]],
					[[* -1, 5, 41, -25, -1, 101, 47,
					  -51, 185,
					  -15, 293, 215, -109, 129, -37,
					  335,
					  425, 237, -163, -127, 131,
					  479 *]] ]>;

// This example is from David Loeffler's
// Explicit Calculations of Automorphic Forms for
// Definite Unitary Groups, section 4.2

function chi(r,s,p,alpha_R)
    R := Order(p);
    _, pi := IsPrincipal(p);                               
    pi_bar := alpha_R(pi);
    // This assumes we are in a quadratic extension
    if (r+s mod 2 eq 1) then
	lambda := Factorization(ideal<R | Discriminant(R)>)[1][1];
	F, mod_lambda := ResidueClassField(lambda);
	mul := KroneckerSymbol(Integers()!mod_lambda(pi),#F);
    else
	mul := 1;
    end if;
    return mul * pi_bar^r * pi^s;
end function;

function createExamples_7_4()
    K := QuadraticField(-7);
    inner_form := IdentityMatrix(K, 3);
    R := Integers(K);
    _, cc := HasComplexConjugate(K);
    alpha := FieldAutomorphism(K, cc);
    alpha_R := hom< R -> R | x :-> alpha(K!x) >;
    evs_2_0 := [[[* *]]];
    evs_3_1 := [[[* *]]];
    evs_2_2 := [[[* *]],[[* *]]];
    evs_3_3 := [[[* *]],[[* *]]];
    evs_4_0 := [[[* *]],[[* *]],[[* *]]];

    norm_p := [2, 11, 23, 29, 37, 43, 53, 67, 71,
	   79, 107, 109, 113, 127, 137, 149,
	   151, 163, 179, 191, 193, 197];

    mod_frm_7_7 := [ -8, 874, 4738, 11146, 3002, 31418, -76406, 495242,
		     -184406, -534934, 1616026, 199226, -1807622, 3324722,
		     2129266, -2595734, -1685566, 1881914, 3518458,
		     -7200278, -13088902, -9174758];
    mod_frm_49_6 := [ -2, -284, 1496, -4366, -12630, -1356, 14150, -3644,
		       35632, -54616, 218188, -96030, -137422, 170368,
		       -75562, 361030, 32280, -61364, 610564, 341192,
		       -616158, 231478];

    // for the third example, the coefficients are too ugly to write
    // down like that, and computing them is quite quick.

    M := ModularSymbols(KroneckerCharacter(-7, CyclotomicField(7)),9);
    D := NewformDecomposition(NewSubspace(CuspidalSubspace(M)));

    mod_frm_7_9 := [ Coefficient(qEigenform(D[2],200),n) : n in norm_p];

    L := Universe(mod_frm_7_9);
    
    ps := [Factorization(ideal<R|n>)[1][1] : n in norm_p];
    for i in [1..#ps] do
	p := ps[i];
	val_2_0 := K!(chi(4,-2,p,alpha_R) + chi(1,1,p,alpha_R) +
		      chi(0,2,p,alpha_R));
	val_3_1 := K!(chi(1,1,p,alpha_R)) +
		   K!(chi(-1,-3,p,alpha_R)) * mod_frm_7_7[i];
	val_3_3 := L!(chi(1,1,p,alpha_R)) +
		   L!(chi(-3,-3,p,alpha_R)) * L!mod_frm_7_9[i];
	val_4_0_a := K!(chi(6,-4,p,alpha_R) + chi(1,1,p,alpha_R) +
			chi(0,2,p,alpha_R));
	val_4_0_b := K!(chi(0,2,p,alpha_R)) +
		     K!(chi(1,-4,p,alpha_R)) * K!mod_frm_49_6[i];
	val_4_0_c := K!(chi(1,1,p,alpha_R)) +
		     K!(chi(0,-4,p,alpha_R)) * mod_frm_7_7[i];
	val_2_2_a := mod_frm_7_7[i] * K!(chi(-2,-2,p,alpha_R))
			+ K!(chi(1,1,p,alpha_R));
	val_2_2_b := K!(chi(4,-2,p,alpha_R) + chi(1,1,p,alpha_R) +
			chi(-2,4,p,alpha_R));
	Append(~evs_2_0[1][1], val_2_0);
	Append(~evs_3_1[1][1], val_3_1);
	Append(~evs_3_3[1][1], val_3_3);
	Append(~evs_2_2[1][1], val_2_2_a);
	Append(~evs_2_2[2][1], val_2_2_b);
	Append(~evs_4_0[1][1], val_4_0_a);
	Append(~evs_4_0[2][1], val_4_0_b);
	Append(~evs_4_0[3][1], val_4_0_c);
    end for;

    F<alpha> := QuadraticField(-259);
    evs_3_3[2][1] := [* (alpha - 7) / 8, (244*alpha - 7441) / 1331,
		   (-21940 * alpha - 162337) / 12167 *];
    
    Example_7_4_W_2_0 := rec<ExampleRF | name := "[GV2]_7_4_W_2_0",
					 group := "Unitary",
					 field := QuadraticField(-7),
					 inner_form := inner_form,
					 coeff_char := 0,
					 genus := 2,
					 weight := [2,0],
					 norm_p := norm_p,
					 timing := [],
					 evs := evs_2_0>;

    Example_7_4_W_3_1 := rec<ExampleRF | name := "[GV2]_7_4_W_3_1",
					 group := "Unitary",
					 field := QuadraticField(-7),
					 inner_form := inner_form,
					 coeff_char := 0,
					 genus := 2,
					 weight := [3,1],
					 norm_p := norm_p,
					 timing := [],
					 evs := evs_3_1>;

    Example_7_4_W_3_3 := rec<ExampleRF | name := "[GV2]_7_4_W_3_3",
					 group := "Unitary",
					 field := QuadraticField(-7),
					 inner_form := inner_form,
					 coeff_char := 0,
					 genus := 2,
					 weight := [3,3],
					 norm_p := norm_p,
					 timing := [],
					 evs := evs_3_3>;

    Example_7_4_W_4_0 := rec<ExampleRF | name := "[GV2]_7_4_W_4_0",
					 group := "Unitary",
					 field := QuadraticField(-7),
					 inner_form := inner_form,
					 coeff_char := 0,
					 genus := 2,
					 weight := [4,0],
					 norm_p := norm_p,
					 timing := [],
					 evs := evs_4_0>;

    Example_7_4_W_2_2 := rec<ExampleRF | name := "[GV2]_7_4_W_2_2",
					 group := "Unitary",
					 field := QuadraticField(-7),
					 inner_form := inner_form,
					 coeff_char := 0,
					 genus := 2,
					 weight := [2,2],
					 norm_p := norm_p,
					 timing := [],
					 evs := evs_2_2>;
    
    ret := [Example_7_4_W_2_0,
	    Example_7_4_W_2_2,
	    Example_7_4_W_3_1,
	    Example_7_4_W_3_3,
	    Example_7_4_W_4_0];
    return ret;
end function;

Example_7_4_W_2_0,
Example_7_4_W_2_2,
Example_7_4_W_3_1,
Example_7_4_W_3_3,
Example_7_4_W_4_0 := Explode(createExamples_7_4());

// TODO : This one is slightly different than the other two -
// Should make appropriate modifications in the test function

F<root13> := QuadraticField(13);
R<x> := PolynomialRing(F);
K := ext< F | x^2 + 13 + 2*root13 >;

Example_7_5 := rec<ExampleRF | name := "[GV2]_7_5",
			       group := "Unitary",
			       field := K,
			       inner_form := IdentityMatrix(K,3),
			       coeff_char := 13,
			       genus := 9,
			       weight := [0,0],
			       norm_p := [29, 53, 61, 79, 107, 113, 131,
					  139,
					  157, 191, 211],
			       timing := [15.15, 51.73, 70.35, 123.21,
					  216.82,
					  242.20, 339.50, 378.81, 486.22,
					  727.81,
					  943.89],
			       evs := [[[* GF(13)!x :
					 x in [4, 11, 12, 5, 5, 3, 6,
					 10, 1, 11, 2] *]]]>;
K := CyclotomicField(7);
Example_7_6 := rec<ExampleRF | name := "[GV2]_7_6",
			       group := "Unitary",
			       field := K,
			       inner_form := IdentityMatrix(K,3),
			       coeff_char := 0,
			       genus := 2,
			       weight := [0,0],
			       norm_p := [29, 43, 71, 113, 127, 197, 211,
					  239, 281],
			       timing := [2.16, 2.85, 6.77, 16.43, 21.35,
					  51.14, 53.58, 73.05, 101.84],
			       evs := [[[* 871, 1893, 5113, 12883, 16257,
					39007, 44733, 57361, 79243 *]],
				       [[* -25, 101, 185, -109, 129, 479,
					-67, 17, 395 *]]]>;

AlgebraicModularFormsExamples := [ Example_7_2,
				  Example_7_3,
				  Example_7_4,
				  Example_7_4_W_2_0,
				  Example_7_4_W_2_2,
				  Example_7_4_W_3_1,
				  Example_7_4_W_3_3,
				  Example_7_4_W_4_0,
				  Example_7_5,
				  Example_7_6];

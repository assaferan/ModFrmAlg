// data for examples to test on

UnitaryExampleRF := recformat< field : Fld,
			       genus : RngIntElt,
			       norm_p : SeqEnum,
			       timing : SeqEnum,
		               a : List,
		               b : List>;

UnitaryExample_7_2 := rec<UnitaryExampleRF |
			 field := QuadraticField(-7),
			 genus := 2,
			 norm_p := [2, 11, 23, 29, 37, 43, 53, 67, 71,
				    79, 107, 109, 113, 127, 137, 149,
				    151, 163, 179, 191, 193, 197],
			 timing := [0.02, 0.07, 0.18, 0.28, 0.42,
				    0.57, 0.82, 1.35, 1.46, 1.86,
				    3.73, 4.18, 4.59, 5.85, 7.08,
				    8.56, 9.04, 10.88, 13.78, 16.92,
				    17.22, 17.29],
			 a := [* 7, 133, 553, 871, 1407, 1893, 2863,
			       4557, 5113, 6321, 11557, 11991, 12883,
			       16257, 18907, 22351, 22953, 26733,
			       32221, 36673, 37443, 39007 *],
			 b := [* -1, 5, 41, -25, -1, 101, 47, -51, 185,
			       -15, 293, 215, -109, 129, -37, 335,
			       425, 237, -163, -127, 131, 479 *]>;

// TODO : This one is slightly different than the other two -
// Should make appropriate modifications in the test function

UnitaryExample_7_3 := rec<UnitaryExampleRF |
			 field := ext<QuadraticField(13) | >,
			 genus := 9,
			 norm_p := [29, 53, 61, 79, 107, 113, 131, 139,
				    157, 191, 211],
			 timing := [15.15, 51.73, 70.35, 123.21, 216.82,
				    242.20, 339.50, 378.81, 486.22, 727.81,
				    943.89],
			 a := [* 4, 11, 12, 5, 5, 3, 6, 10, 1, 11, 2 *],
			 b := [* *]>;
    
UnitaryExample_7_4 := rec<UnitaryExampleRF |
			     field := CyclotomicField(7),
			     genus := 2,
			     norm_p := [29, 43, 71, 113, 127, 197, 211,
					239, 281],
			     timing := [2.16, 2.85, 6.77, 16.43, 21.35,
					51.14, 53.58, 73.05, 101.84],
			     a := [* 871, 1893, 5113, 12883, 16257, 39007,
				   44733, 57361, 79243 *],
			     b := [* -25, 101, 185, -109, 129, 479, -67,
				   17, 395 *]>;

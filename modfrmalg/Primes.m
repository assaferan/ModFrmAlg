freeze;
 
/****-*-magma-************************************************
                                                                          
                  ModFrmAlg : Algebraic Modular Forms in Magma

 FILE: Primes.m (Version Support)                                        
                                                                       
 Last updated : 03/02/2024, Eran Assaf

***************************************************************************/

// This file is intended for supporting older versions of magma
// In particular these functions only appear in Magma v. 2.23-1 and afterwards.

is_defined, PrimeIdealsOverPrime := IsIntrinsic("PrimeIdealsOverPrime");

if not is_defined then
    CheckVersion();
    function PrimeIdealsOverPrime(K, p)
	R := Integers(K);
	pR := p*R;
	return [pa[1] : pa in Factorization(pR)];
    end function;
end if;

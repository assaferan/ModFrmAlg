freeze;
/****-*-magma-**************************************************************
                                                                            
                    Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J.Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
                
                                                                            
   FILE: bad_primes.m (functions for recovering euler factors at bad primes)

   04/06/21 : File created.
 
 ***************************************************************************/

// Here we list the intrinsics that this file defines
//

// These functions are for debugging bad Euler factors

function check_signs(f, signs, evs, ps, w, j, D, d, eps_ps, dim, x, Precision)
  lpolys := AssociativeArray();
  for i in [1..#ps] do
    s := signs[i];
    p := ps[i];
    L_poly := p^(3+2*w)*x^2+(s[1]*p + s[2]*evs[i][1] + s[3]*dim)*p^w*x+1;
    L_poly *:= eps_ps[i]*p^(1+w)*x+1;
    lpolys[p] := L_poly;
  end for;
  function local_factor(p,d)
    if p in ps then
      poly := lpolys[p];
    else
      poly := LPolynomial(f,p,d);
    end if;
    CC := ComplexField();
    CC_x := PowerSeriesRing(CC);
    K := BaseRing(Parent(poly));
    r := Roots(DefiningPolynomial(K),CC)[1][1];
    if Type(K) eq FldRat then
      h := hom<K -> CC|>;
    else 
      h := hom<K -> CC | r>;
    end if;
    return CC_x![h(c) : c in Eltseq(poly)];
  end function;
  lser := LSeries(2*w+4, [-w-1+j,-w+j,j,j+1], D, local_factor :
                 Sign := (-1)^w*nu(D,d), Precision := Precision);
  return CFENew(lser);
end function;

function find_signs(f, evs, ps, w, j, D, d, eps_ps, dim, x)
  signs := CartesianPower(CartesianPower([-1,0,1],3),#ps);
  prec := 1;
  while (#signs gt 1) do 
     tmp := [<s, check_signs(f, s, evs, ps, w, j, D, d, eps_ps, dim, x, prec)>
		 : s in signs];
     signs := [x[1] : x in tmp | IsZero(x[2])];
     prec +:= 1;
  end while;
  if IsEmpty(signs) then return false, _; end if;
  return true, signs[1];
end function;

// We implement Ibukiyama's formulas for S_{k,j}(K(p))
// These are paramodular cusp forms of level K(p)
// and weight det^k \otimes Sym^j
// The following assume j is even and k >= 3

function IK_Kronecker(a,N)
  if (N eq 2) then
    if (a eq -1) then
      return 0;
    elif a eq -3 then
      return -1;
    elif a eq 3 then // ?
      return 0;
    end if;
  end if;
  if IsPrime(N) then
    return KroneckerSymbol(a,N);
  end if;
  primes := [f[1] : f in Factorization(N)];
  return (IsEmpty(primes) select 1 else &*[IK_Kronecker(-1,p) : p in primes]);
end function;

function H1(p,k,j)
  a := (p^2 + 1) / 2880;
  b := (j+1)*(k-2)*(j+k-1)*(j+2*k-3) / 6;
  return a*b;
end function;

function H1prime(k, j, N)
  primes := [f[1] : f in Factorization(N)];
  prod := &*[p^2 - 1 : p in primes];
  denom := 2^7*3^3*5;
  num := (j+1)*(k-2)*(j+k-1)*(j+2*k-3);
  return num*prod/denom;
end function;

function H2(p,k,j)
  if p ne 2 then
    a := 7/576;
  else
    a := 11/1152;
  end if;
  return (-1)^k *(j+k-1)*(k-2)*a;
end function;

function H2prime(k,j,N)
  if N ne 2 then
    return 0;
  end if;
  denom := 2^7*3^2;
  num := -3*(-1)^k*(j+k-1)*(k-2);
  return num/denom;
end function;

function H3(p,k,j)
  if p ne 2 then
    c := 1/(3*2^4);
  else
    c := 5/(2^5*3);
  end if;
  a := [(-1)^(j div 2)*(k-2), -(j+k-1)];
  a[3] := -a[1];
  a[4] := -a[2];
// b := a[(k - 1) mod 4 + 1];
  b := a[k mod 4 + 1];
  return b*c;
end function;

function C1(k,j)
  a := [[1,0,0,-1,-1,-1,-1,0,0,1,1,1],
	[-1,1,0,1,1,0,1,-1,0,-1,-1,0],
	[1,-1,0,1,1,0,1,-1,0,-1,-1,0],
	[-1,0,0,-1,1,-1,1,0,0,1,-1,1],
	[1,1,0,1,-1,0,-1,-1,0,-1,1,0],
	[-1,-1,0,0,1,1,1,1,0,0,-1,-1]];
//return a[(j div 2) mod 6 + 1][(k-1) mod 12 + 1];
  return a[(j div 2) mod 6 + 1][k mod 12 + 1];
end function;

function C2(k,j)
  a := [[1,0,0,-1,0,0],
	[-1,1,0,1,-1,0],
	[0,-1,0,0,1,0]];
//return a[(j div 2) mod 3 + 1][(k-1) mod 6 + 1];
  return a[(j div 2) mod 3 + 1][k mod 6 + 1];
end function;

function C3(k,j)
  a := [[-1,0,0,-1,0],
	[-1,1,0,0,0],
	[0,0,0,0,0],
	[0,0,0,1,-1],
	[0,-1,0,0,1]];
// return a[(j div 2) mod 5 + 1][(k-1) mod 5 + 1];
  return a[(j div 2) mod 5 + 1][k mod 5 + 1];
end function;

function C4(k,j)
  a := [[1,0,0,-1],
	[-1,1,0,0],
	[-1,0,0,1],
	[1,-1,0,0]];
// return a[(j div 2) mod 4 + 1][(k-1) mod 4 + 1];
  return a[(j div 2) mod 4 + 1][k mod 4 + 1];
end function;

// This is C3 from Ibukiyama-Kityama,
// as opposed to C3 from Ibukiyama

function C_3(k,j)
   a := [(k-2)*(-1)^(j div 2), -(j+k-1), -(k-2)*(-1)^(j div 2), j+k-1];
// return a[(k-1) mod 4 + 1];
   return a[k mod 4 + 1];
end function;

// This is C4 from Ibukiyama-Kityama,
// as opposed to C4 from Ibukiyama

function C_4(k,j)
  a := [1,-1,0];
  b := [1,0,-1];
// return (j+k-1)*a[(k-1) mod 3 + 1] + (k-2)*b[(j+k-1) mod 3 +1];
  return (j+k-1)*a[(k) mod 3 + 1] + (k-2)*b[(j+k) mod 3 +1];
end function;

function C_5(k,j)
  a := [-1,-1,0,1,1,0];
  b := [1,0,-1,-1,0,1];
// return (j+k-1)*a[(k-1) mod 6 + 1] + (k-2)*b[(j+k-1) mod 6 + 1];
  return (j+k-1)*a[(k) mod 6 + 1] + (k-2)*b[(j+k) mod 6 + 1];
end function;

function C_8(k,j)
  return C1(k,j);
end function;

function C_9(k,j)
  return C2(k,j);
end function;

function C_10(k,j)
  a := [[1,0,0,-1,0],
	[-1,1,0,0,0],
	[0,0,0,0,0],
	[0,0,0,1,-1],
	[0,-1,0,0,1]];
// return a[(j div 2) mod 5 + 1][(k-1) mod 5 + 1];
  return a[(j div 2) mod 5 + 1][k mod 5 + 1];
end function;

function C_11(k,j)
  return C4(k,j);
end function;

function H3prime(k,j,N)
  if N ne 2 then
    return 0;
  end if;
  return C_3(k,j)/32;
end function;

function H4(p,k,j)
  if p ne 3 then
    c := 1/(2^2*3^3);
  else
    c := 5/(2^2*3^3);
  end if;
  a1 := [j+k-1, -(j+k-1),0];
// b1 := a1[(k-1) mod 3 + 1];
  b1 := a1[k mod 3 + 1];
  a2 := [k-2,0,-(k-2)];
//  b2 := a2[(j+k-1) mod 3 + 1];
  b2 := a2[(j+k) mod 3 +1];
  return (b1+b2)*c;
end function;

function H4prime(k,j,N)
  if N ne 3 then
    return 0;
  end if;
  return C_4(k,j) / 27;
end function;

function H5(p,k,j)
//a := [-(j+k-1), -(j+k-1), 0, (j+k-1), (j+k-1), 0];
// b := a[(k-1) mod 6 + 1];
//b := a[k mod 6  +1];
  b := C_5(k,j);
  return b / (2^2*3^2);
end function;

function H5prime(k,j,N)
  return 0;
end function;

function H6(p,k,j)
  case p mod 4:
   when 1:
     a := 5*(p+1)*(-1)^(j div 2)*(2*k+j-3)/(2^7*3);
     b := (p+1)*(-1)^(k+j div 2)*(j+1)/(2^7);
     return a+b;
   when 3:
     a := (p-1)*(-1)^(j div 2)*(2*k+j-3) / (2^7);
     b := 5*(p-1)*(-1)^(k+j div 2)*(j+1) / (2^7*3);
     return a+b;
   when 2:
     a := 3*(-1)^(j div 2)*(2*k+j-3) / (2^7);
     b := 7*(-1)^(k+j div 2)*(j+1)/(2^7*3);
     return a+b;
  end case;
end function;

function H6prime1(N)
  denom1 := 2^5*3;
  denom2 := 2^7*3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := &*[p - IK_Kronecker(-1,p) : p in primes];
  prod2 := &*[p*IK_Kronecker(-1,p)-1 : p in primes];
  return prod1/denom1 + prod2/denom2;
end function;

function H6prime2(N)
  denom1 := 2^5*3;
  denom2 := 2^7*3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := &*[p - IK_Kronecker(-1,p) : p in primes];
  prod2 := &*[p*IK_Kronecker(-1,p)-1 : p in primes];
  return (-1)^(#primes)*prod1/denom1 - prod2/denom2;
end function;

function H6prime(k,j,N)
  a := (-1)^(j div 2)*(2*k+j-3)*H6prime1(N);
  b := (-1)^(j div 2 + k)*(j+1)*H6prime2(N);
  return a + b;
end function;

function H7(p,k,j)
  case p mod 3:
    when 1:
     a := [-1,0,1];
// b1 := a[(j+2-1) mod 3 + 1];
     b1 := a[(j+2) mod 3 + 1];
     c1 := (p+1)*(2*k+j-3)*b1/(2*3^3);
// b2 := a[(2*k+j-2-1) mod 3 + 1];
     b2 := a[(2*k+j-2) mod 3 + 1];
     c2 := (p+1)*(j+1)*b2 / (2^2*3^3);
     return c1 + c2;
   when 2:
     a := [-1,0,1];
// b1 := a[(j+2-1) mod 3 + 1];
     b1 := a[(j+2) mod 3 + 1];
     c1 := (p-1)*(2*k+j-3)*b1/(2^2*3^3);
// b2 := a[(2*k+j-2-1) mod 3 + 1];
     b2 := a[(2*k+j-2) mod 3 + 1];
     c2 := (p-1)*(j+1)*b2 / (2*3^3);
     return c1 + c2;
   when 0:
     a := [-1,0,1];
// b1 := a[(j+2-1) mod 3 + 1];
     b1 := a[(j+2) mod 3 + 1];
     c1 := 5*(2*k+j-3)*b1/(2^3*3^3);
// b2 := a[(2*k+j-2-1) mod 3 + 1];
     b2 := a[(2*k+j-2) mod 3 + 1];
     c2 := (j+1)*b2 / (3^3);
     return c1 + c2;
  end case;
end function;

function H7prime1(N)
  denom1 := 2^3*3^2;
  denom2 := 2^3*3^3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := &*[p - IK_Kronecker(-3,p) : p in primes];
  prod2 := &*[p*IK_Kronecker(-3,p)-1 : p in primes];
  return prod1/denom1 + prod2/denom2;
end function;

function H7prime2(N)
  denom1 := 2^3*3^2;
  denom2 := 2^3*3^3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := &*[p - IK_Kronecker(-3,p) : p in primes];
  prod2 := &*[p*IK_Kronecker(-3,p)-1 : p in primes];
  return (-1)^(#primes)*prod1/denom1 - prod2/denom2;
end function;

function H7prime(k,j,N)
  a := [1,-1,0];
  b := [0,1,-1];
  c := a[(j-1) mod 3 + 1]*(2*k+j-3)*H7prime1(N);
  d := b[(j+2*k-1) mod 3 + 1]*(j+1)*H7prime2(N);
  return c + d;
end function;

function H8(p,k,j)
  return C1(k,j)/6;
end function;

function H8prime(k,j,N)
  return 0;
end function;

function H9(p,k,j)
  if p ne 2 then
    return C2(k,j)*2/3^2;
  else
    return C2(k,j)/(2*3^2);
  end if;
end function;

function H9prime(k,j,N)
  if N ne 2 then
    return 0;
  end if;
  return -C_9(k,j)/6;
end function;

function H10(p,k,j)
  case p mod 5:
    when 1,4:
      a := 2/5;
    when 0:
      a := 1/5;
    when 2,3:
      a := 0;
  end case;
  return a*C3(k,j);
end function;

function H10prime(k,j,N)
  primes := [f[1] : f in Factorization(N)];
  N1_5 := {p : p in primes | p mod 5 eq 1};
  N4_5 := {p : p in primes | p mod 5 eq 4};
  if not IsEmpty(N1_5 join N4_5) then
    return 0;
  end if;
  if N mod 5 eq 0 then
    scalar := 1;
  else
    scalar := 2;
  end if;
  return (-2)^(#primes)*scalar*C_10(k,j)/10;
end function;

function H11(p,k,j)
  case p mod 8:
  when 1,7:
    a := 1/4;
  when 3,5:
    a := 0;
  when 2:
    a := 1/8;
  end case;
  return a*C4(k,j);
end function;

function H11prime(k,j,N)
  primes := [f[1] : f in Factorization(N)];
  N1_8 := {p : p in primes | p mod 8 eq 1};
  N7_8 := {p : p in primes | p mod 8 eq 7};
  if not IsEmpty(N1_8 join N7_8) then
    return 0;
  end if;
  if N mod 2 eq 0 then
    scalar := 1;
  else
    scalar := 2;
  end if;
  return (-2)^(#primes)*scalar*C_11(k,j)/16;
end function;

function H12(p,k,j)
  a := [1,0,-1];
  case p mod 12:
    when 1:
// b := a[(2*k+j-2-1) mod 3 + 1];
      b := a[(2*k+j-2) mod 3 + 1];
      return -(-1)^(j div 2 + 1)*b/6;
    when 11:
    // b := a[(j+2-1) mod 3 + 1];
      b := a[(j+2) mod 3 + 1];
      return (-1)^(j div 2 + k -1)*b/6;
    when 5,7:
      return 0;
    when 2,3:
      // b := a[(j+2-1) mod 3 + 1];
      b := a[(j+2) mod 3 + 1];
      return (-1)^(j div 2 + k - 1) * b / 12;
  end case;
end function;

function H12prime1(N)
  denom1 := 2^3*3;
  denom2 := 2^3*3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := &*[1 - IK_Kronecker(3,p) : p in primes];
  prod2 := &*[IK_Kronecker(-1,p)-IK_Kronecker(-3,p) : p in primes];
  return (-1)^(#primes)*prod1/denom1 - prod2/denom2;
end function;

function H12prime2(N)
  denom1 := 2^3*3;
  denom2 := 2^3*3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := &*[1 - IK_Kronecker(3,p) : p in primes];
  prod2 := &*[IK_Kronecker(-1,p)-IK_Kronecker(-3,p) : p in primes];
  return (-1)^(#primes)*prod1/denom1 + (-1)^(#primes)*prod2/denom2;
end function;

function H12prime(k,j,N)
  a := [1,-1,0];
  b := [0,-1,1];
  c := (-1)^(j div 2 + k)*a[(j-1) mod 3 + 1]*H12prime1(N);
  d := (-1)^(j div 2)*b[(j+2*k-1) mod 3 + 1]*H12prime2(N);
  return c + d;
end function;

function I1(p,k,j)
  a := -p*(j+1)*(2*k+j-3)/(2^4*3^2);
  b := (p+1)*(j+1)/(2^3*3);
  return a+b - (j+1)/24;
end function;

function I1prime(k,j,N)
  primes := [f[1] : f in Factorization(N)];
  prod := &*[p-1 : p in primes];
  return (j+1)*prod/24;
end function;

function I2(p,k,j)
  return (-1)^k * (4 - IK_Kronecker(-1,p))/2^4 - (-1)^k*(j+2*k-3)/24;
end function;

function I2prime(k,j,N)
  return 0;
end function;

function I3(p,k,j)
  a := [(-1)^(j div 2), -1, (-1)^(j div 2 + 1), 1];
// return -a[(k-1) mod 4 + 1]/4;
  return -a[(k) mod 4 + 1]/4;
end function;

function I3prime(k,j,N)
  return 0;
end function;

function A(p,k,j)
  a := [1,-1,0];
  b := [1,0,-1];
// return -a[(k-1) mod 3 + 1] - b[(j+k-1) mod 3 + 1];
  return -a[(k) mod 3 + 1] - b[(j+k) mod 3 + 1];
end function;

function C(p,k,j)
  a := [1,0,1];
  b := [0,-1,-1];
//return -2*a[(k-1) mod 3 + 1] - 2*b[(j+k-1) mod 3 + 1];
  return -2*a[(k) mod 3 + 1] - 2*b[(j+k) mod 3 + 1];
end function;

function B(p,k,j)
  return 2*A(p,k,j)-C(p,k,j);
end function;

function I4(p,k,j)
  ret := A(p,k,j)/18;
  case p mod 3:
    when 0:
      return ret + A(p,k,j)/9;
    when 1:
      return ret + C(p,k,j)/9;
    when 2:
      return ret + B(p,k,j)/9;
  end case;
end function;

function I4prime(k,j,N)
  return 0;
end function;

function I5(p,k,j)
  a := [-1,-1,0,1,1,0];
  b := [1,0,-1,-1,0,1];
// return -(a[(k-1) mod 6 + 1] + b[(j+k-1) mod 6 + 1])/6;
  return -(a[(k) mod 6 + 1] + b[(j+k) mod 6 + 1])/6;
end function;

function I5prime(k,j,N)
  return 0;
end function;

function I6(p,k,j)
  return (-1)^(j div 2 + 1)*(1 + IK_Kronecker(-1,p))/8;
end function;

function I6prime(k,j,N)
  return 0;
end function;

function I7(p,k,j)
  a := [-1,0,1];
  c := -(1 + IK_Kronecker(-3,p))/6;
// return c*a[(j+2-1) mod 3 + 1];
  return c*a[(j+2) mod 3 + 1];
end function;

function I7prime(k,j,N)
  return 0;
end function;

function I8prime(k,j,N)
  return 0;
end function;

function I9prime(k,j,N)
  primes := [f[1] : f in Factorization(N)];
  prod := &*[IK_Kronecker(-1,p)-1 : p in primes];
  return -(-1)^(j div 2)*prod / 8;
end function;

function I10prime(k,j,N)
  a := [1,-1,0];
  primes := [f[1] : f in Factorization(N)];
  prod := &*[IK_Kronecker(-3,p)-1 : p in primes];
// return a[(j-1) mod 3 + 1]*prod / 6;
  return a[(j) mod 3 + 1]*prod / 6;
end function;

// This one is from Ibukiyama short announcement of result,
// and doesn't really work. Should check why.

function DimensionOfParamodularCuspFormSpace(p,k,j)
  Hs := [H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, H12];
  Is := [I1, I2, I3, I4, I5, I6, I7];
  ret :=  &+[H(p,k,j) : H in Hs] + &+[I(p,k,j) : I in Is];
  if k eq 3 and j eq 0 then
    return ret + 1;
  else
    return ret;
  end if;
end function;

// This is from Ibukiyama-Kitiyama

function DimensionOfParamodularFormSpace(k,j,N)
  Hs := [H1prime, H2prime, H3prime, H4prime, H5prime, H6prime,
		H7prime, H8prime, H9prime, H10prime, H11prime, H12prime];
  Is := [I1prime, I2prime, I3prime, I4prime, I5prime, I6prime,
		I7prime, I8prime, I9prime, I10prime];
  primes := [f[1] : f in Factorization(N)];
  if IsOdd(#primes) then
    ret :=  &+[H(k,j,N) : H in Hs];
  else
    ret :=  &+[H(k,j,N) : H in Hs] + &+[I(k,j,N) : I in Is];
  end if;
  if k eq 3 and j eq 0 then
    return ret + 1;
  else
    return ret;
  end if;
end function;

// Another try - Ibukiyama Kitiyama final formulae

function H_1(k,j,N)
  primes := [f[1] : f in Factorization(N)];
  prod := IsEmpty(primes) select 1 else &*[p^2 + 1 : p in primes];
  denom := 2^7*3^3*5;
  num := (j+1)*(k-2)*(j+k-1)*(j+2*k-3);
  return num * prod/denom;
end function;

function H_2(k,j,N)
  omega := #Factorization(N);
  denom := 2^(8-omega)*3^2;
  scalar := (N mod 2 eq 0) select 11 else 14;
  return (-1)^k*(k-2)*(j+k-1)*scalar / denom;
end function;

function H_3(k,j,N)
  omega := #Factorization(N);
  denom := 2^(6-omega)*3;
  scalar := (N mod 2 eq 0) select 5 else 2;
  return C_3(k,j)*scalar/denom;
end function;

function H_4(k,j,N)
  omega := #Factorization(N);
  denom := 2^(3-omega)*3^3;
  scalar := (N mod 3 eq 0) select 5 else 1;
  return C_4(k,j)*scalar/denom;
end function;

function H_5(k,j,N)
  omega := #Factorization(N);
  denom := 2^(3-omega)*3^2;
  return C_5(k,j) / denom;
end function;

function H_6_1(N)
  denom1 := 2^5*3;
  denom2 := 2^7*3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := IsEmpty(primes) select 1 else &*[p + IK_Kronecker(-1,p) : p in primes];
  prod2 := IsEmpty(primes) select 1 else &*[p*IK_Kronecker(-1,p)+1 : p in primes];
  return prod1/denom1 + prod2/denom2;
end function;

function H_6_2(N)
  denom1 := 2^5*3;
  denom2 := 2^7*3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := IsEmpty(primes) select 1 else &*[p + IK_Kronecker(-1,p) : p in primes];
  prod2 := IsEmpty(primes) select 1 else &*[p*IK_Kronecker(-1,p)+1 : p in primes];
  return prod1/denom1 - prod2/denom2;
end function;

function H_6(k,j,N)
  a :=  (-1)^(j div 2)*(2*k+j-3)*H_6_1(N);
  b := (-1)^(j div 2 + k)*(j+1)*H_6_2(N);
  return a+b;
end function;

function H_7_1(N)
  denom1 := 2^3*3^2;
  denom2 := 2^3*3^3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := IsEmpty(primes) select 1 else &*[p + IK_Kronecker(-3,p) : p in primes];
  prod2 := IsEmpty(primes) select 1 else &*[p*IK_Kronecker(-3,p)+1 : p in primes];
  return prod1/denom1 + prod2/denom2;
end function;

function H_7_2(N)
  denom1 := 2^3*3^2;
  denom2 := 2^3*3^3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := IsEmpty(primes) select 1 else &*[p + IK_Kronecker(-3,p) : p in primes];
  prod2 := IsEmpty(primes) select 1 else &*[p*IK_Kronecker(-3,p)+1 : p in primes];
  return prod1/denom1 - prod2/denom2;
end function;

function H_7(k,j,N)
  a := [1,-1,0];
  b := [0,1,-1];
  c := a[j mod 3 + 1] * (2*k+j-3)*H_7_1(N);
  d := b[(j+2*k) mod 3 + 1]*(j+1)*H_7_2(N);
  return c + d;
end function;

function H_8(k,j,N)
  omega := #Factorization(N);
  return C_8(k,j) / (2^(2-omega)*3);
end function;

function H_9(k,j,N)
  omega := #Factorization(N);
  scalar := (N mod 2 eq 0) select 1 else 4;
  return scalar*C_9(k,j) / (2^(2-omega)*3^2);
end function;

function H_10(k,j,N)
  primes := [f[1] : f in Factorization(N)];
  N5 := [#[p : p in primes | p mod 5 eq i] : i in [1..4]];
  scalar := (N5[2]+N5[3] eq 0) select 2^(N5[1]+N5[4]) else 0;
  return C_10(k,j)*scalar/5;
end function;

function H_11(k,j,N)
  primes := [f[1] : f in Factorization(N)];
  N8 := [#[p : p in primes | p mod 8 eq i] : i in [1..7]];
  scalar := (N8[3]+N8[5] eq 0) select 2^(N8[1]+N8[7]) else 0;
  return C_11(k,j)*scalar/8;
end function;

function H_12_1(N)
  denom1 := 2^3*3;
  denom2 := 2^3*3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := IsEmpty(primes) select 1 else &*[1 + IK_Kronecker(3,p) : p in primes];
  prod2 := IsEmpty(primes) select 1 else &*[IK_Kronecker(-1,p)+IK_Kronecker(-3,p) : p in primes];
  return prod1/denom1 - prod2/denom2;
end function;

function H_12_2(N)
  denom1 := 2^3*3;
  denom2 := 2^3*3;
  primes := [f[1] : f in Factorization(N)];
  prod1 := IsEmpty(primes) select 1 else &*[1 + IK_Kronecker(3,p) : p in primes];
  prod2 := IsEmpty(primes) select 1 else &*[IK_Kronecker(-1,p)+ IK_Kronecker(-3,p) : p in primes];
  return prod1/denom1 + prod2/denom2;
end function;

function H_12(k,j,N)
  a := [1,-1,0];
  b := [0,-1,1];
  c := a[j mod 3 + 1]*(-1)^(j div 2 + k)*H_12_1(N);
  d := b[(j+2*k) mod 3 + 1] *(-1)^(j div 2)*H_12_2(N);
  return c + d;
end function;

function I_1(k,j,N)
  primes := [f[1] : f in Factorization(N)];
  prod := IsEmpty(primes) select 1 else &*[p+1 : p in primes];
  return (j+1)*prod / 24;
end function;

function I_2(k,j,N)
  omega := #Factorization(N);
  return -2^(omega-4)*3^(-1)*(j+1);
end function;

function I_3(k,j,N)
  omega := #Factorization(N);
  denom := 2^(5-omega)*3^2;
  return -N*(j+1)*(2*k+j-3)/denom;
end function;

function I_4(k,j,N)
  omega := #Factorization(N);
  return 2^(omega-5)*(-1)^k*(4-IK_Kronecker(-1,N));
end function;

function I_5(k,j,N)
  omega := #Factorization(N);
  return -2^(omega-4)*3^(-1)*(-1)^k*(2*k+j-3);
end function;

function I_6(k,j,N)
  omega := #Factorization(N);
  a := [(-1)^(j div 2), -1, -(-1)^(j div 2), 1];
  return -2^(omega-3)*a[k mod 4 + 1];
end function;

function I_7(k,j,N)
  omega := #Factorization(N);
  a := [[3,-3,0],
	[5,-1,4],
	[1,-5,-4]];
  b := [[3,0,-3],[1,-4,-5],[5,4,-1]];
  return -2^(omega-2)*3^(-2)*(a[N mod 3 + 1][k mod 3 + 1] +
			      b[N mod 3 + 1][(j+k) mod 3 + 1]);
end function;

function I_8(k,j,N)
  omega := #Factorization(N);
  a := [-1,-1,0,1,1,0];
  b := [1,0,-1,-1,0,1];
  return -2^(omega-2)*3^(-1)*(a[k mod 6 + 1] + b[(j+k) mod 6 + 1]);
end function;

function I_9(k,j,N)
  primes := [f[1] : f in Factorization(N)];
  prod := IsEmpty(primes) select 1 else &*[1+IK_Kronecker(-1,p) : p in primes];
  return -2^(-3)*(-1)^(j div 2)*prod;
end function;

function I_10(k,j,N)
  primes := [f[1] : f in Factorization(N)];
  prod := IsEmpty(primes) select 1 else &*[1+IK_Kronecker(-3,p) : p in primes];
  a := [1,-1,0];
  return -2^(-1)*3^(-1)*a[j mod 3 + 1]*prod;
end function;

// Finally!!! This works
function IbukiyamaKitiyama(k,j,N)
  if IsOdd(j) then
     return 0;
  end if;
  Hs := [H_1, H_2, H_3, H_4, H_5, H_6, H_7, H_8, H_9, H_10, H_11, H_12];
  Is := [I_1, I_2, I_3, I_4, I_5, I_6, I_7, I_8, I_9, I_10];
  ret := &+[H(k,j,N) : H in Hs] + &+[I(k,j,N) : I in Is];
  if (k eq 3) and (j eq 0) then
    ret +:= 1;
  end if;
  return ret;
end function;

function dimensionOfLifts(k, j, N)
  ret := 0;
  for d in Divisors(N) do
    omega := #PrimeDivisors(d);
    M := ModularSymbols(N div d, 2*k+j-2);
    S := CuspidalSubspace(M);
    Snew := NewSubspace(S);
    t := Dimension(NewSubspace(CuspidalSubspace(ModularSymbols(d,j+2))));
    if (j eq 0) then
      w := AtkinLehnerOperator(Snew, N div d);
      ret +:= Dimension(Eigenspace(w,(-1)^(omega+k))) div 2;
    end if;
    ret +:= t*Dimension(Snew) div 4;
  end for;
  return ret;
end function;

function DimensionOfNewSubspace(k,j,N)
  ret := 0;
  for d in Divisors(N) do
    omega := #PrimeDivisors(d);
    ret +:= (-2)^omega * IbukiyamaKitiyama(k,j,N div d);
    if (j eq 0) and (d ne 1) then
      M := ModularSymbols(N div d, 2*k-2);
      S := CuspidalSubspace(M);
      Snew := NewSubspace(S);
      w := AtkinLehnerOperator(Snew, N div d);
      ret -:= (-1)^omega*Dimension(Eigenspace(w,(-1)^(k))) div 2;;
    end if;
  end for;
  return ret;
end function;

function DimensionOfNonliftSubspace(k,j,N)
  ret := 0;
  for d in Divisors(N) do
    omega := #PrimeDivisors(d);
    ret +:= (-2)^omega * IbukiyamaKitiyama(k,j,N div d);
    M := ModularSymbols(N div d, 2*k+j-2);
    S := CuspidalSubspace(M);
    Snew := NewSubspace(S);
    t := Dimension(NewSubspace(CuspidalSubspace(ModularSymbols(d,j+2))));
    if (j eq 0) then
      w := AtkinLehnerOperator(Snew, N div d);
      ret -:= (-1)^omega*Dimension(Eigenspace(w,(-1)^k)) div 2;
    end if;
    ret -:= t*Dimension(Snew) div 4;
  end for;
  return ret;
end function;

freeze;
 
/****-*-magma-************************************************
                                                                          
                  VERSION: Algebraic Modular Forms in Magma

 FILE: quadratic_defect.m (Version Support)                                        
                                                                       
 Last updated : 03/02/2024, Eran Assaf

***************************************************************************/

// This file is intended for supporting older versions of magma
// In particular these functions only appear in Magma v. 2.23-1 and afterwards.

is_defined, QuadraticDefect := IsIntrinsic("QuadrarticDefect");
    
if not is_defined then

    QuadraticDefectInt := function(a, p)
	
	assert p ge 2 and IsPrime(p: Proof:= false);
	if IsZero(a) then return Infinity(); end if;
	v:= Valuation(a, p);
	if IsOdd(v) then return v; end if;
	a/:= p^v;
	a:= Numerator(a)*Denominator(a);
	if p ne 2 then
	    return KroneckerSymbol(a, p) eq 1 select Infinity() else v;
	end if;
	return case< a mod 8 | 1: Infinity(), 5: v+2, default: v+1 >;
        
    end function;
    
    QuadraticDefect := function(a, p)
	if Type(a) eq RngIntElt then
	    a := a/1;
	end if;
	if Type(p) eq RngIntElt then
	    return QuadraticDefectInt(a,p);
	end if;
	
	R:= Order(p);
	assert IsPrime(p) and IsMaximal(R);
	ok, a:= IsCoercible(NumberField(R), a);
	assert ok;

	if IsZero(a) then return Infinity(); end if;
	v:= Valuation(a, p);
	if IsOdd(v) then return v; end if;    // trivial

	pi:= PrimitiveElement(p);
	a /:= pi^v;
	k, h:= ResidueClassField(p);
	ok, s:= IsSquare(h(a));

	if Minimum(p) ne 2 then
	    return ok select Infinity() else v;
	end if;

	// The case 2 \in p:
	// make a of the form 1 + eps*pi^w, then try to increase w if necessary.
	assert ok;
	a /:= (s @@ h)^2;
	w:= Valuation(a-1, p);
	assert w ge 1;
	ee:= 2*Valuation(Order(p) ! 2, p);

	// If 1 < w < 2e is even, we can lift once more, see O'Meara 63:2.
	while w lt ee and IsEven(w) do
	    s:= SquareRoot(h((a - 1) / pi^w));
	    a /:= (1+(s@@h)*pi^(w div 2))^2;
	    w:= Valuation(a-1, p);
	end while;

	// The following line is O'Meara 63:3 (w==ee) and 63:5 (ww<ee).
	return (w gt ee) or (w eq ee and not IsIrreducible(Polynomial([k | ((a-1)/4) @ h, 1, 1]))) select Infinity() else v+w;
    end function;
    
end if;

v1, v2, v3 := GetVersion();
version := Vector([v1, v2, v3]);

if version lt Vector([2,23,1]) then   
    error "This package is not supported on Magma version %o", version;
end if;

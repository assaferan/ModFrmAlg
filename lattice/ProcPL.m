freeze;
/****-*-magma-******a********************************************************
                                                                            
                        Algebraic Modular Forms in Magma
                        
                  E. Assaf, M. Greenberg, J. Hein, J. Voight
         using lattices over number fields by M. Kirschmer and D. Lorch         
                   
   FILE: ProcPL.m
   
   ProjectiveLineProcess
 ***************************************************************************/

// is_defined, ProjectiveLineProcess := IsIntrinsic("ProjectiveLineProcess");

// The Magma command no longer works in Magma V2.28-2

is_defined := false;

if is_defined then
    
    _, Next := IsIntrinsic("Next");

    // empty procedure in this case
    procedure Advance(~PP)
	return;
    end procedure;

else
    
    ProcPL := recformat< a, v, dim, depth>;

    function ProjectiveLineProcessVS(V)
	PL:= rec<ProcPL|>;
	PL`a:= PrimitiveElement(BaseField(V));
	PL`v:= V ! 0;
	PL`dim:= Dimension(V);
	PL`depth:= PL`dim+1;
	return PL;
    end function;

    function ProjectiveLineProcess(k, n)
	assert n ge 1;
	return ProjectiveLineProcessVS(VectorSpace(k, n));
    end function;

    function SizePL(PL)
	q:= #Parent(PL`a);
	return (q^PL`dim-1) div (q-1);
    end function;

    procedure Advance(~PL)
	if PL`depth ne 0 then
	    i:= PL`dim;
	    while true do
		if i eq PL`depth then
		    PL`v[i]:= 0; i -:= 1;
		elif i lt PL`depth then
		    PL`depth:= i;
		    if i ge 1 then PL`v[i]:= 1; end if;
		    break;
		elif PL`v[i] eq 0 then PL`v[i]:= 1; break;
		else
		    PL`v[i] *:= PL`a;
		    if PL`v[i] eq 1 then PL`v[i]:= 0; i -:= 1; else break; end if;
		end if;
	    end while;
	end if;
    end procedure;

    function Next(PL)
	return PL`v;
    end function;
    
end if;

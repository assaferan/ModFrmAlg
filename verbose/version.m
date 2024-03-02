freeze;
 
/****-*-magma-************************************************
                                                                          
                  VERSION: Algebraic Modular Forms in Magma

 FILE: version.m (Version Support)                                        
                                                                       
 Last updated : 03/02/2024, Eran Assaf

***************************************************************************/

intrinsic CheckVersion()
{.}
  v1, v2, v3 := GetVersion();
  version := Vector([v1, v2, v3]);

  if version lt Vector([2,22,6]) then   
      error "This package is not supported on Magma version %o", version;
  end if;
  return;
end intrinsic;

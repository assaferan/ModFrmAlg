// Edit this file to alter the path for saving files.

// exports
// intrinsic GetAMFPath() -> MonStgElt

intrinsic GetAMFPath() -> MonStgElt
{Returns the path for saving and loading files for algebraic modular forms.
It is currently hard-coded, as I haven't figured out how to do it differently in magma.}
  // return "/Users/eranassaf/Documents/GitHub/ModFrmAlg/data/";
  return "./data/";
end intrinsic;

freeze;

/*
  $Id: GrpCox.m 65966 2022-06-07 05:27:45Z don $

  Scott H Murray

  16 November 2000


  Package for creating Coxeter groups.
  Together with Cartan.m and RootDtm.m, parts of this file are based
  on the old Coxeter.m by D E Taylor

  The CoxeterGroup intrinsics revised and consolidated by DET (2022-03-26)
*/

import "../Root/Cartan.m": typeToBasicDegrees, isFiniteType, isFinAffType, 
  isCrystType, nameToType, cartanToType, tnToType, coxeterToType, typeToOrder,
  typeToName, typeToCoxeter, typeToCartan;
import "../Root/RootDtm.m": toType, rootDatumByIsogeny, rootDatum,
  typeToRootSystem, typeToRootDatum;
import "../Repn/Repn.m" : standardRootSystemInj;


// Attributes and declarations are in declarations.m


// ====================================================
//
// Conversion utilities
//
// ====================================================

// This function computes the matrix transforming one basis to another
transformation := function( B1, B2 )
  B1 := Matrix( B1 );
  B2 := Matrix( B2 );
  R := BaseRing( B1 );
  if ISA( Category( R ), Fld ) then
    return B1^-1 * B2;
  else
    k := FieldOfFractions( R );
    B1 := ChangeRing( B1, k );
    B2 := ChangeRing( B2, k );
    A := B1^-1 * B2;
    b, A_ := IsCoercible(Parent(B1),A);
    if b then A := A_; end if;
    return A;
  end if;
end function;


permToMatrix := function( R, g : BasisType:="Standard" )
  ch_ring := false;
  n := Rank( R );
  case BasisType :
  when "Standard" :
    B1 := SimpleRoots( R );
    B2 := [ Root( R, r^g ) : r in [1..n] ];
    if not IsSemisimple( R ) then
      V := RootSpace( R );
      M := GramMatrix(V);
      B1 := [ V | B1[i] : i in [1..n] ];  
      B2 := [ V | B2[i] : i in [1..n] ];
      B := Basis(Nullspace(M*Transpose(SimpleCoroots(R))));
      B1 cat:= B;  
      B2 cat:= B;
    end if;
    ch_ring := true;
  when "Root" :
    B2 := [ Root( R, r^g : Basis:="Root" ) : r in [1..n] ];
    B1 := Basis(Universe(B2));
  when "Weight" :
    B1 := Matrix(Rationals(), CartanMatrix( R ));
    B2 := [ Root( R, r^g : Basis:="Root" )*B1 : r in [1..n] ];
  else 
    error "Invalid Basis parameter";
  end case;  
  T := transformation( B1, B2 );
  if ch_ring then  
    M := MatrixAlgebra(Integers(),n);
    b, T_ := IsCoercible(M,T);
    if b then T := T_; end if;
  end if;
  return T;
end function;

matrixToPerm := function( R, g : BasisType:="Standard" )
  Phi := Roots( R : Basis:=BasisType );
  N := NumPosRoots( R );
  neg := func< r | (r le N) select r+N else r-N >;
  // ims := [ RootPosition( R, Phi[r]*g : Basis:=Basis ) : r in [1..N] ];
  ims := [ Position( Phi, Phi[r]*g ) : r in [1..N] ];
  return Sym(2*N)!( ims cat [ neg(r) : r in ims ] );
end function;

permToWord := function( R, g )
  ref := SimpleReflectionPermutations( R );  //NB: forward reference
  N := NumPosRoots( R );  n := Rank( R );
  w := [];
  while g ne Parent(g)!1 do
    r := rep{ r : r in [1..n] | r^g gt N };
    Append( ~w, r );
    g := ref[r] * g;
  end while;
  return w;
end function;

wordToPerm := function( R, g )
  ref := SimpleReflectionPermutations( R );  //NB: forward reference
  return &*[ Universe(ref) | ref[r] : r in Eltseq(g) ];
end function; 

// so far we can only do this for finite groups
matrixToWord := function( R, g : BasisType :="Standard" )
  ref := SimpleReflectionMatrices( R );  //NB: forward reference
  N := NumPosRoots( R );  n := Rank( R );
  rts := SimpleRoots( R );  rts := [ rts[i] : i in [1..n] ];
  w := [];
  while g ne Parent(g)!1 do
    r := rep{ r : r in [1..n] | RootPosition(R,rts[r]*g) gt N };
    Append( ~w, r );
    g := ref[r] * g;
  end while;
  return w;
end function;

wordToMatrix := function( R, g )
  ref := SimpleReflectionMatrices( R );  //NB: forward reference
  return &*[ Universe(ref) | ref[r] : r in Eltseq(g) ];
end function; 


// ====================================================
//
// Reflections for root systems/data
//
// Note that permutations are constructed from matrices,
// and words are constructed from permutations.
// ====================================================

reflMat := function( R, r, BasisType, co )
  if BasisType eq "Standard" then
    fld := (co) select "CoreflectionMatrices" else "ReflectionMatrices";
    if not assigned R``fld then  R``fld := [];  end if;
    if not IsDefined( R``fld, r ) then
      u := Root(R,r);  v := Coroot(R,r);
      R``fld[r] := (co) select Reflection(v,u) else Reflection(u,v);
    end if;
    return R``fld[r];
  elif BasisType eq "Root" then
    C := Matrix(Rationals(),CartanMatrix( R ));
    u := Root(R,r:Basis:=BasisType);  v := Coroot(R,r:Basis:=BasisType);
    return (co) select Reflection(v,u*C) else Reflection(u,v*Transpose(C));
  else // elif BasisType eq "Weight" then
    C := Matrix(Rationals(),CartanMatrix( R ));
    u := Root(R,r:Basis:="Root");  v := Coroot(R,r:Basis:="Root");
    return (co) select Reflection(v*Transpose(C),u) else Reflection(u*C,v);
  end if;
end function;

intrinsic ReflectionMatrix( R::RootSys, r::RngIntElt : Basis := "Standard" ) 
  -> AlgMatElt
{The reflection in the rth root of R}
  requirerange r, 1, 2*NumPosRoots(R);
  require Basis in ["Standard","Root"] : "Invalid Basis parameter";
  return reflMat( R, r, Basis, false );
end intrinsic;

intrinsic ReflectionMatrix( R::RootDtm, r::RngIntElt : Basis := "Standard" ) 
  -> AlgMatElt
{"} // " use the description of the previous intrinsic 
  requirerange r, 1, 2*NumPosRoots(R);
  require Basis in ["Standard","Root","Weight"] : "Invalid Basis parameter";
  return reflMat( R, r, Basis, false );
end intrinsic;


intrinsic ReflectionMatrices( R::RootSys : Basis := "Standard" ) -> []
{The reflections in the roots of R}
  require Basis in ["Standard","Root"] : "Invalid Basis parameter";
  return [ reflMat( R, r, Basis, false ) : r in [1..2*NumPosRoots(R)] ];
end intrinsic;

intrinsic ReflectionMatrices( R::RootDtm : Basis := "Standard" ) -> []
{"} // " use the description of the previous intrinsic 
  require Basis in ["Standard","Root","Weight"] : "Invalid Basis parameter";
  return [ reflMat( R, r, Basis, false ) : r in [1..2*NumPosRoots(R)] ];
end intrinsic;


intrinsic SimpleReflectionMatrices( R::RootSys : Basis := "Standard" ) -> []
{The reflections in the simple roots of R}
  require Basis in ["Standard","Root"] : "Invalid Basis parameter";
  return [ reflMat( R, r, Basis, false ) : r in [1..Rank(R)] ];
end intrinsic;

intrinsic SimpleReflectionMatrices( R::RootDtm : Basis := "Standard" ) -> []
{"} // " use the description of the previous intrinsic 
  require Basis in ["Standard","Root","Weight"] : "Invalid Basis parameter";
  return [ reflMat( R, r, Basis, false ) : r in [1..Rank(R)] ];
end intrinsic;



intrinsic CoreflectionMatrix( R::RootSys, r::RngIntElt : Basis := "Standard" ) 
  -> AlgMatElt
{The reflection in the rth coroot of R}
  requirerange r, 1, 2*NumPosRoots(R);
  require Basis in ["Standard","Root"] : "Invalid Basis parameter";
  return reflMat( R, r, Basis, true );
end intrinsic;

intrinsic CoreflectionMatrix( R::RootDtm, r::RngIntElt : Basis := "Standard" ) 
  -> AlgMatElt
{"} // " use the description of the previous intrinsic 
  requirerange r, 1, 2*NumPosRoots(R);
  require Basis in ["Standard","Root","Weight"] : "Invalid Basis parameter";
  return reflMat( R, r, Basis, true );
end intrinsic;


intrinsic CoreflectionMatrices( R::RootSys : Basis := "Standard" ) -> []
{The reflections in the coroots of R}
  require Basis in ["Standard","Root"] : "Invalid Basis parameter";
  return [ reflMat( R, r, Basis, true ) : r in [1..2*NumPosRoots(R)] ];
end intrinsic;

intrinsic CoreflectionMatrices( R::RootDtm : Basis := "Standard" ) -> []
{"} // " use the description of the previous intrinsic 
  require Basis in ["Standard","Root","Weight"] : "Invalid Basis parameter";
  return [ reflMat( R, r, Basis, true ) : r in [1..2*NumPosRoots(R)] ];
end intrinsic;


intrinsic SimpleCoreflectionMatrices( R::RootSys : Basis := "Standard" ) -> []
{The reflections of the simple coroots of R}
  require Basis in ["Standard","Root"] : "Invalid Basis parameter";
  return [ reflMat( R, r, Basis, true ) : r in [1..Rank(R)] ];
end intrinsic;

intrinsic SimpleCoreflectionMatrices( R::RootDtm : Basis := "Standard" ) -> []
{"} // " use the description of the previous intrinsic 
  require Basis in ["Standard","Root","Weight"] : "Invalid Basis parameter";
  return [ reflMat( R, r, Basis, true ) : r in [1..Rank(R)] ];
end intrinsic;



reflPerm := function( R, r )
  if not assigned R`ReflectionPerms then
    R`ReflectionPerms := [];
  end if;
  if not IsDefined( R`ReflectionPerms, r ) then
    R`ReflectionPerms[r] := matrixToPerm( R, reflMat( R, r, "Standard", false ) );
  end if;
  return R`ReflectionPerms[r];
end function;

intrinsic ReflectionPermutation( R::RootSys, r::RngIntElt ) -> GrpPermElt
{The reflection permutation of the rth (co)root of R}
  requirerange r, 1, 2*NumPosRoots(R);
  return reflPerm( R, r );
end intrinsic;

intrinsic ReflectionPermutation( R::RootDtm, r::RngIntElt ) -> GrpPermElt
{"} // " use the description of the previous intrinsic 
  requirerange r, 1, 2*NumPosRoots(R);
  return reflPerm( R, r );
end intrinsic;


intrinsic ReflectionPermutations( R::RootSys ) -> []
{The reflection permutations of the roots of R}
  return [ reflPerm( R, r ) : r in [1..2*NumPosRoots(R)] ];
end intrinsic;

intrinsic ReflectionPermutations( R::RootDtm ) -> []
{"} // " use the description of the previous intrinsic 
  return [ reflPerm( R, r ) : r in [1..2*NumPosRoots(R)] ];
end intrinsic;


intrinsic SimpleReflectionPermutations( R::RootSys ) -> []
{The reflection permutations of the simple roots of R}
  return [ reflPerm( R, r ) : r in [1..Rank(R)] ];
end intrinsic;

intrinsic SimpleReflectionPermutations( R::RootDtm ) -> []
{"} // " use the description of the previous intrinsic 
  return [ reflPerm( R, r ) : r in [1..Rank(R)] ];
end intrinsic;


reflWord := function( R, r )
  if not assigned R`ReflectionWords then
    R`ReflectionWords := [ [r] : r in [1..Rank(R)] ];
  end if;
  if not IsDefined( R`ReflectionWords, r ) then
    R`ReflectionWords[r] := permToWord( R, reflPerm( R, r ) );
  end if;
  return R`ReflectionWords[r];
end function;

intrinsic ReflectionWord( R::RootSys, r::RngIntElt ) -> []
{The reflection word of the rth root of R}
  requirerange r, 1, 2*NumPosRoots(R);
  return reflWord( R, r );
end intrinsic;

intrinsic ReflectionWord( R::RootDtm, r::RngIntElt ) -> []
{"} // " use the description of the previous intrinsic 
  requirerange r, 1, 2*NumPosRoots(R);
  return reflWord( R, r );
end intrinsic;


intrinsic ReflectionWords( R::RootSys ) -> []
{The reflection words of the roots of R}
  return [ reflWord( R, r ) : r in [1..2*NumPosRoots(R)] ];
end intrinsic;

intrinsic ReflectionWords( R::RootDtm ) -> []
{"} // " use the description of the previous intrinsic 
  return [ reflWord( R, r ) : r in [1..2*NumPosRoots(R)] ];
end intrinsic;

// ====================================================
//
// Coxeter group constructions
//
// ====================================================
//
// FP group utilities
//
// ----------------------------------------------------
braidWord := function( x, y, n )
  q, r := Quotrem( n, 2 );
  return (x*y)^q * x^r;
end function;

braidRel := func< x, y, n | braidWord(x,y,n) = braidWord(y,x,n) >;

coxeterToBraidGroup := function( M )
  n := Nrows( M );
  if n eq 0 then
    F<s> := FreeGroup( 1 );
    return quo< F | s >;
  else
    F<[s]> := FreeGroup( n );
    return quo< F | [ braidRel( s[i], s[j], M[i,j] ) : j in [i+1..n], i in [1..n] ] >;
  end if;
end function;

coxeterToGrpFP := function( M )
  B<[s]> := coxeterToBraidGroup( M );
  W := quo< B | [ s[i]^2 : i in [1..Nrows(M)] ] >;
  order := CoxeterGroupOrder( M );
  W`Order := ( Category(order) eq RngIntElt ) select order else 0;
  return W;
end function;

coxeterToGrpFPCox := function( M )  
  W := GrpFPToCox( coxeterToGrpFP( M ) );
  W`CoxeterMatrix := M;
  order := CoxeterGroupOrder( M );
  W`Order := ( Category(order) eq RngIntElt ) select order else 0;
  return W;
end function;

toGrpFP := function( R )
  return coxeterToGrpFPCox( CoxeterMatrix( R ) );
end function;

toGrpFPCox := function( R )
  if not assigned R`CoxeterGroupFP then
    R`CoxeterGroupFP := coxeterToGrpFPCox( CoxeterMatrix( R ) );
  end if;
  return R`CoxeterGroupFP;
end function;
 
// ----------------------------------------------------
//
// Permutation group utilities
//
// ----------------------------------------------------
toGrpPerm := function( R )
  N := NumPosRoots( R );
  n := ( N ne 0 ) select 2*N else 1;
  //W := GrpPermToCox(sub< Sym(n) | SimpleReflectionPermutations(R) >);
  W := (sub< Sym(n) | SimpleReflectionPermutations(R) >);
  order := typeToOrder( toType( R ) );
  W`Order := ( Category( order ) eq RngIntElt ) select order else 0;
  return W;
end function;

toGrpPermCox := function( R )
  if not assigned R`CoxeterGroupPerm then
    W := GrpPermToCox( toGrpPerm(R) );
    if Category( R ) eq RootSys then
      W`RootSystem := R;
    else
      W`RootDatum := R;
    end if;
    R`CoxeterGroupPerm := W;
  end if;
  return R`CoxeterGroupPerm;
end function;  

// ----------------------------------------------------
//
// Matrix group utilities
//
// ----------------------------------------------------
toGrpMat := function( R : BasisType:= "Standard" )
  if BasisType eq "Standard" and assigned R`CoxeterGroupMat then
    return R`CoxeterGroupMat;
  end if;

  Cobasis := case< BasisType | 
    "Root" : "Weight", "Weight" : "Root", default : "Standard" >;
  n := Rank(R);
  k := BaseRing(R);
  if n eq 0 then
    if BasisType in {"Root","Weight"} then
      d := 1;
    else
      d := Max(1,Dimension(R)); // d must be at least 1 for a matrix group!
    end if;
    A := Matrix( k,n,d,[] );
    B := A;
  else
    A := Matrix( [ BasisChange( R,   Root( R, r ) : OutBasis:=BasisType        ) : r in [1..n] ] );
    B := Matrix( [ BasisChange( R, Coroot( R, r ) : OutBasis:=Cobasis, Coroots ) : r in [1..n] ] );
  end if;
  W := ReflectionGroup( A, B );

  if BasisType eq "Standard" then
    if Category( R ) eq RootSys then
      W`RootSystem := R;
    else
      W`RootDatum := R;
    end if;
    R`CoxeterGroupMat := W;
    if not assigned R`ReflectionMatrices then
      R`ReflectionMatrices := [ W.r : r in [1..n] ];
    end if;
  end if;

  return W;
end function;


// ====================================================
//
// Coxeter groups from root systems and root data
//
// ----------------------------------------------------
intrinsic CoxeterGroup(grpcat :: Cat,R :: RootStr : Basis := "Standard") -> Grp
{The Coxeter group in category 'grpcat' of the root system or root datum R}
  case grpcat:
    when GrpMat:
      return toGrpMat(R : BasisType:=Basis);
    when GrpPermCox:
      return toGrpPermCox(R);
    when GrpPerm:
      return toGrpPerm(R);
    when GrpFPCox:
      if not assigned R`CoxeterGroupFP then 
        R`CoxeterGroupFP := coxeterToGrpFPCox(CoxeterMatrix(R));
      end if;
      return R`CoxeterGroupFP;
    when GrpFP:
      return coxeterToGrpFP( CoxeterMatrix( R ) );
  end case;
end intrinsic;

intrinsic WeylGroup(grpcat :: Cat,R :: RootStr : Basis := "Standard") -> Grp
{The Weyl group in category 'grpcat' of the root system or root datum R,
where 'grpcat' is one of GrpMat, GrpPermCox, GrpPerm, GrpFPCox or GrpFP.}
  case grpcat:
    when GrpMat:
      return toGrpMat(R : BasisType:=Basis);
    when GrpPermCox:
      return toGrpPermCox(R);
    when GrpPerm:
      return toGrpPerm(R);
    when GrpFPCox:
      if not assigned R`CoxeterGroupFP then 
        R`CoxeterGroupFP := coxeterToGrpFPCox(CoxeterMatrix(R));
      end if;
      return R`CoxeterGroupFP;
    when GrpFP:
      return coxeterToGrpFP( CoxeterMatrix( R ) );
  end case;
end intrinsic;
intrinsic CoxeterGroup( R::RootStr ) -> GrpPermCox
{The Coxeter group of the root system or root datum R}
  return toGrpPermCox(R);
end intrinsic;

intrinsic ReflectionGroup( R::RootStr : Basis:= "Standard" ) -> GrpMat
{The reflection group of R}
  return toGrpMat( R : BasisType:=Basis );
end intrinsic;

intrinsic WeylGroup( R::RootStr ) -> GrpPermCox
{The Weyl group of the root system or root datum R}
  return toGrpPermCox(R);
end intrinsic;

intrinsic CoxeterFPGroup(R::RootStr ) -> GrpFP
{The Coxeter group of the root system or root datum R as an fp-group}
  return coxeterToGrpFP( CoxeterMatrix( R ) );
end intrinsic;

intrinsic WeylFPGroup(R::RootStr ) -> GrpFP
{The Weyl group of the root system or root datum R as an fp-group}
  return coxeterToGrpFP( CoxeterMatrix( R ) );
end intrinsic;


// ====================================================
//
// Coxeter groups from a Coxeter or Cartan matrix
//
// ----------------------------------------------------
matToCartan := function( M )
  if IsCoxeterMatrix( M ) then
    return CartanMatrix( M ), _;
  else
    ok, realinj := IsCartanMatrix( M );
    if ok then
      return M, realinj;
    else
      error "Not a Coxeter matrix or Cartan matrix";
    end if;
  end if;
end function;

matToCoxeter := function( M )
  if IsCartanMatrix( M ) then
    return CoxeterMatrix( M );
  elif IsCoxeterMatrix( M ) then
    return M;
  else
    error "Not a Coxeter matrix or Cartan matrix";
  end if;
end function;


onlyfinite := "Only finite groups have a permutation representation"; 

intrinsic CoxeterGroup(grpcat :: Cat, M :: AlgMatElt) -> Grp
{The Coxeter group in category 'grpcat' of the Coxeter or Cartan matrix M,
where 'grpcat' is one of GrpMat, GrpPermCox, GrpPerm, GrpFPCox or GrpFP.}
  case grpcat:
    when GrpMat:
      C := matToCartan( M );
      W := ReflectionGroup( Parent(C)!1, Transpose(C) );
      W`CartanMatrix := C;
      if C ne M then  W`CoxeterMatrix := M;  end if;
      return W;
    when GrpPermCox, GrpPerm:
      require IsCoxeterFinite( M ) : onlyfinite;
      return toGrpPermCox(RootSystem( M ));
    when GrpFPCox, GrpFP:
      return coxeterToGrpFPCox(matToCoxeter( M ));
  end case;
end intrinsic;

intrinsic CoxeterFPGroup(M::AlgMatElt ) -> GrpFP
{The Coxeter group of the Coxeter or Cartan matrix M as an fp-group
(without normalisation)}
  return CoxeterGroup( GrpFPCox, M );
end intrinsic;

intrinsic ReflectionGroup( M::AlgMatElt ) -> GrpMat
{The reflection group of the Coxeter or Cartan matrix M}
  return (IsCoxeterMatrix( M ) or IsCartanMatrix( M ))
    select CoxeterGroup( GrpMat, M )
    else ComplexReflectionGroup( M );
end intrinsic;

intrinsic CoxeterGroup( M::AlgMatElt ) -> Grp
{The permutation representation or (if the group is inifinite) the FP
representation of the Coxeter group whose Coxeter or Cartan matrix is M}
  return (IsCoxeterFinite(M)) 
    select CoxeterGroup(GrpPermCox, M) 
    else CoxeterGroup(GrpFPCox, M);
end intrinsic;


// ====================================================
//
// Coxeter groups from Coxeter graphs
//
// ----------------------------------------------------
intrinsic CoxeterGroup(grpcat :: Cat, G :: GrphUnd) -> Grp
{The Coxeter group in category 'grpcat' of the Coxeter graph G}
  case grpcat:
    when GrpMat:
      W := CoxeterGroup(GrpMat, CoxeterMatrix(G));
      W`CoxeterGraph := G;
      return W;
    when GrpPermCox:
      require IsCoxeterFinite(G) : onlyfinite;
      W := CoxeterGroup(GrpPermCox, RootSystem(G));
      W`CoxeterGraph := G;
      return W;
    when GrpPerm:
      require IsCoxeterFinite(G) : onlyfinite;
      return toGrpPerm(RootSystem(G));
    when GrpFPCox:
      W := coxeterToGrpFPCox(CoxeterMatrix(G));
      W`CoxeterGraph := G;
      return W;
    when GrpFP:
      return coxeterToGrpFP(CoxeterMatrix(G));
  end case;
end intrinsic;

intrinsic CoxeterFPGroup(G::GrphUnd ) -> GrpFP
{The Coxeter group of the Coxeter graph G as an fp-group
(without normalisation)}
  return coxeterToGrpFP( CoxeterMatrix( G ) );
end intrinsic;

intrinsic ReflectionGroup( G::GrphUnd ) -> GrpMat
{The reflection group of the Coxeter graph G}
  return CoxeterGroup( GrpMat, G );
end intrinsic; 

intrinsic CoxeterGroup( G::GrphUnd ) -> Grp
{The permutation representation or (if the group is inifinite) the FP
representation of the Coxeter group with Coxeter graph G}
  return (IsCoxeterFinite( G )) 
    select CoxeterGroup( GrpPermCox, G ) 
    else CoxeterGroup( GrpFPCox, G );
end intrinsic;


// ====================================================
//
// Coxeter groups from Dynkin digraphs
//
// ----------------------------------------------------
intrinsic CoxeterGroup(grpcat :: Cat, D :: GrphDir) -> Grp
{The Coxeter group in category 'grpcat' of the Dynkin digraph D}
  case grpcat:
    when GrpMat:
      W := CoxeterGroup(GrpMat, CoxeterMatrix(D));
      W`DynkinDigraph := D;
      return W;
    when GrpPermCox:
      require IsCoxeterFinite(D) : onlyfinite;
      return toGrpPermCox(RootDatum(D));
    when GrpPerm:
      require IsCoxeterFinite(D) : onlyfinite;
      return toGrpPerm(RootDatum(D));
    when GrpFPCox:
      return coxeterToGrpFPCox(CoxeterMatrix(D));
    when GrpFP:
      return coxeterToGrpFP(CoxeterMatrix(D));
  end case;
end intrinsic;

intrinsic CoxeterFPGroup(D::GrphDir ) -> GrpFP
{The Coxeter group of the Coxeter graph G as an fp-group
(without normalisation)}
  return coxeterToGrpFP( CoxeterMatrix( D ) );
end intrinsic;

intrinsic ReflectionGroup( D::GrphDir ) -> GrpMat
{The reflection group of the Dynkin digraph D}
  return CoxeterGroup( GrpMat, D );
end intrinsic; 

intrinsic CoxeterGroup( D::GrphDir ) -> Grp
{The permutation representation or (if the group is inifinite) the FP
representation of the Coxeter group with Dynkin diagram D}
  return (IsCoxeterFinite( D )) 
    select CoxeterGroup( GrpPermCox, D ) 
    else CoxeterGroup( GrpFPCox, D );
end intrinsic;


// ====================================================
//
// Coxeter groups from roots and coroots
//
// ----------------------------------------------------
intrinsic CoxeterGroup(grpcat :: Cat, A :: Mtrx, B :: Mtrx) -> Grp
{The Coxeter group in category 'grpcat' with simple roots A and simple coroots B}
  case grpcat:
    when GrpMat:
      return ReflectionGroup(A, B);
    when GrpPermCox:
      return toGrpPermCox(RootSystem(A, B));
    when GrpPerm:
      return toGrpPerm(RootSystem(A, B));
  end case;
end intrinsic;


intrinsic CoxeterGroup( A::Mtrx, B::Mtrx ) -> Grp
{The permutation representation or (if the group is inifinite) the FP
representation of the Coxeter group with simple roots A and simple coroots B}
  return (IsCoxeterFinite( Matrix( A*Transpose(B) ) )) 
    select CoxeterGroup( GrpPermCox, A, B ) 
    else CoxeterGroup( GrpFPCox, A*Transpose(B) );
end intrinsic;


// ====================================================
//
// Coxeter groups from Cartan names
//
// ----------------------------------------------------
intrinsic CoxeterGroup(grpcat :: Cat, N :: MonStgElt : Basis := "Standard") -> Grp
{The Coxeter group in category 'grpcat' with Cartan name N}
  case grpcat:
    when GrpMat:
      type := nameToType( N );
      return isFiniteType( type )
        select CoxeterGroup( GrpMat, typeToRootSystem( type ) : Basis:=Basis )
        else CoxeterGroup( GrpMat, typeToCartan( type ) );
    when GrpPermCox:
      type := nameToType( N );
      require isFiniteType( type ) : onlyfinite;
      return toGrpPermCox( typeToRootSystem( type ) );
    when GrpPerm:
      type := nameToType( N );
      require isFiniteType( type ) : onlyfinite;
      return toGrpPerm( typeToRootSystem( type ) );
    when GrpFPCox:
      return coxeterToGrpFPCox(CoxeterMatrix(N));
//      return CoxeterGroup(GrpFPCox, typeToCoxeter(nameToType(N)));
    when GrpFP:
      return coxeterToGrpFP(CoxeterMatrix(N));
  end case;
end intrinsic;

intrinsic CoxeterFPGroup(N::MonStgElt ) -> GrpFP
{The Coxeter group with Cartan name N as an fp-group (without normalisation)}
  return coxeterToGrpFP( CoxeterMatrix( N ) );
end intrinsic;

intrinsic ReflectionGroup( N::MonStgElt : Basis:="Standard" ) -> GrpMat
{The reflection group with Cartan name N}
  return CoxeterGroup( GrpMat, N : Basis:=Basis );
end intrinsic;

intrinsic CoxeterGroup( N::MonStgElt ) -> GrpPermCox
{The permutation representation or (if the group is inifinite) the FP
representation of the Coxeter group with Cartan name N}
  type := nameToType( N );
  if isFiniteType( type ) then
    return CoxeterGroup( GrpPermCox, typeToRootSystem( type ) );
  else
    return CoxeterGroup( GrpFPCox, typeToCartan( type ) );
  end if;
end intrinsic;

// ====================================================
//
// Irreducible Coxeter groups from a Cartan name and rank
//
// ----------------------------------------------------
intrinsic IrreducibleCoxeterGroup(grpcat :: Cat, X :: MonStgElt, n :: RngIntElt) -> Grp
{The irreducible Coxeter group in category 'grpcat' with Cartan name X and rank n}
  case grpcat:
    when GrpMat:
      type := tnToType( X, n );
      return isFiniteType( type )
        select CoxeterGroup(GrpMat, typeToRootSystem(type))
        else CoxeterGroup(GrpMat, typeToCartan(type));
    when GrpPermCox:
      type := tnToType( X, n );
      require isFiniteType( type ) : onlyfinite;
      return toGrpPermCox( typeToRootSystem( type ) );
    when GrpPerm:
      type := tnToType( X, n );
      require isFiniteType( type ) : onlyfinite;
      return toGrpPerm( typeToRootSystem( type ) );
    when GrpFPCox:
      type := tnToType( X, n );
      return CoxeterGroup(GrpFPCox, typeToCoxeter(type));
    when GrpFP:
      return coxeterToGrpFP(IrreducibleCoxeterMatrix(X,n));
  end case;
end intrinsic;

intrinsic IrreducibleCoxeterFPGroup(X::MonStgElt, n::RngIntElt ) 
  -> GrpFP
{The irreducible Coxeter group with Cartan name N as an fp-group
(without normalisation)}
  return coxeterToGrpFP( IrreducibleCoxeterMatrix( X, n ) );
end intrinsic;

intrinsic IrreducibleReflectionGroup( X::MonStgElt, n::RngIntElt ) -> GrpMat
{The irreducible reflection group with Cartan name X_n}
  return IrreducibleCoxeterGroup( GrpMat, X, n );
end intrinsic;

intrinsic IrreducibleCoxeterGroup( X::MonStgElt, n::RngIntElt ) -> Grp
{The irreducible Coxeter group with Cartan name X_n}
  type := tnToType( X, n );
  return isFiniteType(type)
    select CoxeterGroup( GrpPermCox, typeToRootSystem( type ) )
    else CoxeterGroup( GrpFPCox, typeToCartan( type ) );
end intrinsic;


// ====================================================
//
// Conversion bwetween representations of Coxeter groups
//
// ====================================================
// Root systems and root data
determineABC := procedure( M, ~A, ~B, ~C )
  cA := Category(A);  cB := Category(B);  cC := Category(C);
  if cC eq BoolElt then
    if cA ne BoolElt and cB ne BoolElt then
      C := A * Transpose( B );
    else
      C := CartanMatrix( M );
    end if;
  end if;
  if cA eq BoolElt and cB eq BoolElt then
    A := IdentityMatrix( BaseRing( C ), Ncols( C ) );
    B := Transpose( C );
  elif cA eq BoolElt then
    A := C * Transpose( B )^-1;
  elif cB eq BoolElt then
    B := Transpose( A^-1 * C );
  end if;
end procedure;

// return either a root system or a root datum
groupToRoot := function( W )
  if not IsFinite(W) then
    error "The Coxeter group must be finite";
  end if;
  if Category(W) eq GrpFPCox then
    return RootSystem( CartanMatrix( CoxeterMatrix( W ) ) );
  elif assigned W`RootDatum then
    return W`RootDatum;
  elif assigned W`RootSystem then
    return W`RootSystem;
  else  // W must be a reflection group
    R := RootSystem( W`SimpleRoots, W`SimpleCoroots );
    W`RootSystem := R;
    return R;
  end if;
end function;

isRealReflGrp := function( G )
  k := BaseRing( G );  
  kcat := Category( k );
  if not (kcat eq RngInt or kcat eq FldRat or ISA(kcat, FldAlg)) then
    return false, 
      "Real reflection groups must be defined over integers, rationals, a cyclotomic field, or a number field",_,_;
  elif kcat eq FldCyc then
    d := Degree( G ); 
    if not forall{ l : l in [1..NumberOfGenerators(G)] |
    forall{ <i,j> : i in [1..d], j in [1..d] | IsReal((G.l)[i,j]) } } then
      return false, "The group must be defined over the reals",_,_;
    end if;
  elif ISA(kcat,FldAlg) then
    if not IsReal( Conjugate(k.1,1) ) then
      return false, "The base field does not have an injection into the real numbers",_,_;
    end if;
  end if;
  if IsReflectionGroup(G) then
    orders, roots, coroots := RootsAndCoroots( G );
  else
    return false, "", _, _;
  end if;
  if { m : m in orders } eq {2} then
    return true, "", roots, coroots;
  else
    return false, "", _, _;
  end if;
end function;

intrinsic CoxeterGroup(grpcat :: Cat, W :: Grp : 
    Basis := "Standard", A:=false, B:=false, C:=false) -> Grp, Map
{The Coxeter group W converted to its representation G in category 'grpcat',
where 'grpcat' is one of GrpMat, GrpPermCox, GrpPerm, GrpFPCox or GrpFP.  
The second return value is the isomorphism from W to G}
  fromType := Type(W);
  require fromType in {GrpMat, GrpPermCox, GrpFPCox} : 
    "W must be a group of type GrpMat, GrpPermCox or GrpFPCox";
  case fromType:
    when GrpMat:
      require isRealReflGrp(W) : "The group must be a reflection group";
      case grpcat:
        when GrpMat:
          return W, IdentityHomomorphism(W);
        when GrpPermCox:
          require IsFinite(W) : onlyfinite;
          R := groupToRoot(W);  
          W2 := toGrpPermCox(R);
          return W2, hom< W -> W2 | x :-> matrixToPerm(R,x), y :-> permToMatrix(R,y) >;
        when GrpPerm:
          require IsFinite(W) : onlyfinite;
          R := groupToRoot(W);  
          W2 := toGrpPerm(R);
          return W2, hom< W -> W2 | x :-> matrixToPerm(R,x), y :-> permToMatrix(R,y) >;
        when GrpFPCox:
          if IsFinite(W) then
            R := groupToRoot( W );  
            W2 := toGrpFPCox(R);
            return W2, hom< W -> W2 | x :-> matrixToWord(R,x), y :-> wordToMatrix(R,y) >;
          else
            W2 := ReflectionGroup(SimpleRoots(W), SimpleCoroots(W)); //forward calls
            return W2, _; // map not currently available
          end if;
        when GrpFP:
          if IsFinite(W) then
            R := groupToRoot( W );  
            W2 := toGrpFP(R);
            return W2, hom< W -> W2 | x :-> matrixToWord(R,x), y :-> wordToMatrix(R,y) >;
          else
            W2 := CoxeterGroup(GrpFP, SimpleRoots(W), SimpleCoroots(W)); //forward calls
            return W2; // map not currently available
          end if;
      end case;
    when GrpPermCox:
      case grpcat:
        when GrpMat:
          if Basis eq "Standard" and assigned W`ReflectionGroupHom then
            h := W`ReflectionGroupHom;
          else 
            R := groupToRoot(W);  
            W2 := toGrpMat( R : BasisType:=Basis );
            h := hom< W -> W2 | x :-> permToMatrix( R,x : BasisType:=Basis ), 
                                y :-> matrixToPerm( R,y : BasisType:=Basis ) >;
            if Basis eq "Standard" then W`ReflectionGroupHom := h; end if;
          end if;
          return Codomain(h), h;
        when GrpPermCox:
          return W, IdentityHomomorphism(W);
        when GrpPerm:
          W2 := sub< Sym(Degree(W)) | [ W.i : i in [1..Rank(W)] ] >;
          return W2, hom< W -> W2 | x :-> x, y :-> y >;
        when GrpFPCox:
          if not assigned W`FPGroupHom then
            R := groupToRoot(W);  
            W2 := toGrpFPCox(R);
            W`FPGroupHom := hom< W -> W2 | x :-> permToWord(R,x), 
                                           y :-> wordToPerm(R,y) >;
          end if;
          h := W`FPGroupHom;
          return Codomain(h), h;    
        when GrpFP:
          R := groupToRoot(W);  
          W2 := toGrpFP(R);
          return W2, hom< W -> W2 | x :-> permToWord(R,x), y :-> wordToPerm(R,y) >;
      end case;
    when GrpFPCox:
      case grpcat:
        when GrpMat:
          M := CoxeterMatrix(W);
          determineABC(M, ~A, ~B, ~C);
          if IsCoxeterFinite(M) then
            R := RootSystem(A, B);
            W2 := toGrpMat(R);
            return W2, hom< W -> W2 | x :-> wordToMatrix(R,x), y :-> matrixToWord(R,y) >;
          else
            W2 := ReflectionGroup(A, B); //forward call
            return W2, hom< W -> W2 | x :-> &*[W2| W2.r : r in Eltseq(x) ] >;
            // inverse not currently available
          end if;
        when GrpPermCox:
          require IsFinite(W) : onlyfinite;
          M := CoxeterMatrix(W);
          determineABC(M, ~A, ~B, ~C);
          R := RootSystem(A, B);  
          W2 := toGrpPermCox(R);   // USE ROOT DATUM???
          return W2, hom< W -> W2 | x :-> wordToPerm(R,x), y :-> permToWord(R,y) >;
        when GrpPerm:
          require IsFinite(W) : onlyfinite;
          M := CoxeterMatrix(W);
          determineABC(M, ~A, ~B, ~C);
          R := RootSystem(A, B);  
          W2 := toGrpPerm(R);
          return W2, hom< W -> W2 | x :-> wordToPerm(R,x), y :-> permToWord(R,y) >;
        when GrpFPCox:
          return W, IdentityHomomorphism(W);
        when GrpFP:
          W2 := coxeterToGrpFP(CoxeterMatrix( W ));
          return W2, hom< W -> W2 | x :-> x, y :-> y >;
      end case;
    end case;
end intrinsic;

intrinsic ReflectionGroup( W::GrpPermCox : Basis:="Standard" ) -> GrpMat, Map
{The reflection group of the given coxeter group}
  return CoxeterGroup( GrpMat, W : Basis:=Basis );
end intrinsic;

intrinsic CoreflectionGroup( W::GrpPermCox : Basis:="Standard" ) -> GrpMat, Map
{The coreflection group of the given coxeter group}
  V := Dual(W);
  R,h := ReflectionGroup( V : Basis:=Basis );
  h := iso<W->V|[V.i:i in [1..Ngens(W)]]> * h;
  return R,h;
end intrinsic;

intrinsic CoxeterFPGroup(W::GrpPermCox ) -> GrpFP, Map
{The FP representation of the Coxeter group W}
  R := groupToRoot(W);  
  W2 := toGrpFP(R);
  return W2, hom< W -> W2 | x :-> permToWord(R,x), y :-> wordToPerm(R,y) >;
end intrinsic;

intrinsic Presentation( W::GrpPermCox ) -> GrpFPCox
{The presentation of W}
  return CoxeterGroup( GrpFP, W );
end intrinsic;


// WAS THIS EVER NEEDED?
// intrinsic CoxeterGroup( W::GrpPermCox ) -> GrpPermCox, Map
// {The identity} 
//   return W, IdentityHomomorphism( W );
// end intrinsic;


intrinsic ReflectionGroup( W::GrpFPCox : A:=false,B:=false,C:=false ) -> GrpMat, Map
{The reflection group of the given Coxeter group}
  return CoxeterGroup( GrpMat, W : A:=A,B:=B,C:=C );
end intrinsic;

intrinsic CoxeterFPGroup(W::GrpFPCox ) -> GrpFP, Map
{The FP group uderlying the Coxeter FP group W}
  W2 := coxeterToGrpFP( CoxeterMatrix( W ) );
  return W2, hom< W -> W2 | x :-> x, y :-> y >;
end intrinsic;

intrinsic CoxeterGroup( W::GrpFPCox : A:=false,B:=false,C:=false ) -> GrpPermCox, Map
{If W is finite, the permutation representation of the FP Coxeter group W}
  if IsFinite(W) then
    return CoxeterGroup(GrpPermCox, W : A:=false,B:=false,C:=false);
  else
    return W, IdentityHomomorphism(W);
  end if;
end intrinsic;

intrinsic IsRealReflectionGroup( G::GrpMat ) -> BoolElt, [], []
{True iff G is a real reflection group}
  ok, msg, roots, coroots := isRealReflGrp( G );
  require msg eq "" : msg;
  if ok then
    return ok, roots, coroots;
  else
    return ok, _, _;
  end if;
end intrinsic;


intrinsic CoxeterFPGroup(W::GrpMat ) -> GrpFP
{The FP representation of the Coxeter group W}
  require isRealReflGrp(W) : "The group must be a reflection group";
  if IsFinite(W) then // W finite
    R := groupToRoot( W );  
    W2 := toGrpFP(R);
    return W2, hom< W -> W2 | x :-> matrixToWord(R,x), y :-> wordToMatrix(R,y) >;
  else
    W2 := CoxeterGroup( GrpFP, SimpleRoots(W), SimpleCoroots(W) ); //forward calls
    return W2; // map not currently available
  end if;
end intrinsic;


intrinsic CoxeterGroup( W::GrpMat ) -> Grp
{The permutation or (if W is infinite) the FP representation of the Coxeter group W}
  require isRealReflGrp(W) : "The group must be a reflection group";
  if IsFinite( W ) then
    return CoxeterGroup( GrpPermCox, W );
  else
    return CoxeterGroup( GrpFPCox, W );
  end if;
end intrinsic;


// =================================================
//
// Dual groups
//
// =================================================

intrinsic Dual( W::GrpMat ) -> GrpMat
{The dual of the reflection group W}
  require IsReflectionGroup( W ) : "Not a reflection group";
  roots := W`SimpleRoots;  coroots := W`SimpleCoroots;
  G := MatrixGroup< Degree(W), BaseRing(W) | 
       [ Reflection( coroots[i], roots[i] ) : i in [1..#roots] ] >;
  G`IsReflectionGroup := true;
  G`SimpleRoots := coroots;
  G`SimpleCoroots := roots;
  return G;
end intrinsic;

intrinsic Dual( W::GrpPermCox ) -> GrpPermCox
{The dual of W}
  return CoxeterGroup( Dual( RootDatum( W ) ) );
end intrinsic;


// =================================================
//
// Direct products
// 
// =================================================
groupToRootSystem := function( W )
  if not IsFinite( W ) then
    error "The Coxeter group must be finite";
  end if;
  if Category( W ) eq GrpFPCox then
    return RootSystem( CartanMatrix( CoxeterMatrix( W ) ) );
  elif assigned W`RootSystem then
    return W`RootSystem;
  elif assigned W`RootDatum then
    R := RootSystem( W`RootDatum );
  else  // W must be a reflection group
    R := RootSystem( W`SimpleRoots, W`SimpleCoroots );
  end if;
  W`RootSystem := R;
  return R;
end function;

intrinsic DirectProduct( W1::GrpPermCox, W2::GrpPermCox ) -> GrpPermCox
{The direct product of W1 and W2}
  R := DirectSum( groupToRootSystem( W1 ), groupToRootSystem( W2 ) );
  return CoxeterGroup( R );
end intrinsic;

intrinsic DirectProduct( W1::GrpFPCox, W2::GrpFPCox ) -> GrpFPCox
{The direct product of W1 and W2}
  return CoxeterGroup( GrpFPCox, 
    CoxeterGraph( W1 ) join CoxeterGraph( W2 ) );
end intrinsic;



// =================================================
//
// Operations
//
// =================================================


// -------------------------------------------------
//
// Coxeter matrix
//
intrinsic CoxeterMatrix( W::GrpFPCox ) -> AlgMatElt
{The Coxeter matrix of W}
  return W`CoxeterMatrix;
end intrinsic;

intrinsic CoxeterMatrix( W::GrpPermCox ) -> AlgMatElt
{"} // " use the description of the previous intrinsic 
  return CoxeterMatrix( groupToRootSystem( W ) );
end intrinsic;

intrinsic CoxeterMatrix( W::GrpMat ) -> AlgMatElt
{The Coxeter matrix of the real reflection group W}
  require IsReflectionGroup( W ) : "Not a reflection group";
  if not assigned W`CoxeterMatrix then
    W`CoxeterMatrix := CoxeterMatrix( CartanMatrix( W ) );
  end if;
  return W`CoxeterMatrix;
end intrinsic;

// -------------------------------------------------
//
// Coxeter graph
//
intrinsic CoxeterGraph( W::GrpFPCox ) -> AlgMatElt
{The Coxeter graph of W}
  if not assigned W`CoxeterGraph then
    W`CoxeterGraph := CoxeterGraph( CoxeterMatrix( W ) );
  end if;
  return W`CoxeterGraph;
end intrinsic;

intrinsic CoxeterGraph( W::GrpPermCox ) -> AlgMatElt
{The Coxeter graph of W}
  if not assigned W`CoxeterGraph then
    W`CoxeterGraph := CoxeterGraph( CoxeterMatrix( W ) );
  end if;
  return W`CoxeterGraph;
end intrinsic;

intrinsic CoxeterGraph( W::GrpMat ) -> AlgMatElt
{The Coxeter graph of the real reflection group W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  if not assigned W`CoxeterGraph then
    W`CoxeterGraph := CoxeterGraph( CartanMatrix( W ) );
  end if;
  return W`CoxeterGraph;
end intrinsic;

// -------------------------------------------------
//
// Cartan matrix
//
intrinsic CartanMatrix( W::GrpPermCox ) -> AlgMatElt
{The Cartan matrix of W}
  return CartanMatrix( groupToRoot( W ) );
end intrinsic;

intrinsic CartanMatrix( W::GrpMat ) -> AlgMatElt
{The Cartan matrix of the real reflection group W}
  require IsReflectionGroup( W ) : "Not a reflection group";
  if not assigned W`CartanMatrix then
    W`CartanMatrix := W`SimpleRoots * Transpose( W`SimpleCoroots );
  end if;
  return W`CartanMatrix;
end intrinsic;

// -------------------------------------------------
//
// Dynkin digraph
//
intrinsic DynkinDigraph( W::GrpPermCox ) -> AlgMatElt
{The Dynkin digraph of W}
  C := CartanMatrix( W );
  require IsCrystallographic( C ) : "Not a crystallographic group";
  return DynkinDigraph( C );
end intrinsic;

intrinsic DynkinDigraph( W::GrpMat ) -> AlgMatElt
{The Dynkin digraph of the real reflection group W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  C := CartanMatrix( W );
  require IsCrystallographic( C ) : "Not a crystallographic group";  
  if not assigned W`DynkinDigraph then
    W`DynkinDigraph := DynkinDigraph( C );
  end if;
  return W`DynkinDigraph;
end intrinsic;


// -------------------------------------------------
//
// Root system
//
intrinsic RootSystem( W::GrpPermCox ) -> RootSys
{The root system of W}
  return groupToRootSystem( W );
end intrinsic;

intrinsic RootSystem( W::GrpMat ) -> RootSys
{The root system of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  R := groupToRootSystem( W );
  require Category( R ) ne BoolElt : "The Coxeter group is not finite";
  return R;
end intrinsic;


// -------------------------------------------------
//
// Root datum
//

isIntegerMatrix := function( M )
  flag, _ := CanChangeUniverse(Eltseq(M),Integers());
  return flag;
end function;

groupToRootDatum := function( W )
  if not IsFinite( W ) then
    error "The Coxeter group must be finite";
  end if;
  if Category( W ) eq GrpFPCox then
    RD := RootDatum( CartanMatrix( CoxeterMatrix(W) ) );
  elif assigned W`RootDatum then
    RD := W`RootDatum;
  elif assigned W`RootSystem then
    R := W`RootSystem;
    if IsCrystallographic( R ) then
      RD := RootDatum( R );  
      W`RootDatum := RD;
    else
      error "This group does not have a root datum";
    end if;
  else  // W must be a reflection group
    A := W`SimpleRoots;  B := W`SimpleCoroots;
    if isIntegerMatrix( A ) and isIntegerMatrix( B ) then
      RD := RootDatum( A, B );  W`RootDatum := RD;
    else
      error "This group does not have a root datum";
    end if;
  end if;
  RD`CoxeterGroupPerm := CoxeterGroup(GrpPermCox, W);
  RD`CoxeterGroupFP   := CoxeterGroup(GrpFPCox,   W);
  RD`CoxeterGroupMat  := CoxeterGroup(GrpMat,     W);
  return RD;
end function;

intrinsic RootDatum( W::GrpPermCox ) -> RootDtm
{The root datum of W}
  return groupToRootDatum( W );
end intrinsic;

intrinsic RootDatum( W::GrpFPCox ) -> RootDtm
{The root datum of W}
  return groupToRootDatum( W );
end intrinsic;

intrinsic RootDatum( W::GrpMat ) -> RootDtm
{The root datum of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  R := groupToRootDatum( W );
  require Category( R ) ne BoolElt : "The Coxeter group is not finite";
  return R;
end intrinsic;

// utility function
groupToType := function( W )
  if Category( W ) ne GrpFPCox and assigned W`RootDatum then
    return toType( W`RootDatum );
  elif Category( W ) ne GrpFPCox and assigned W`RootSystem then
    return toType( W`RootSystem );
  else
    type := (Category(W) eq GrpFPCox) select coxeterToType( CoxeterMatrix(W) )
            else cartanToType( CartanMatrix( W ) );
    if isFinAffType( type ) then
      return type;
    else
      return false;
    end if;
  end if;
end function;

// -------------------------------------------------
//
// Root space
//
intrinsic RootSpace( W::GrpPermCox ) -> ModTupRng
{The root space of W}
  C := CartanMatrix( W );
  return RSpace( BaseRing(C), Nrows(C) );
end intrinsic;

intrinsic RootSpace( W::GrpMat ) -> ModTupRng
{"} // "
  require IsReflectionGroup( W ) : "Not a reflection group";
  return RSpace( W );
end intrinsic;

// -------------------------------------------------
//
// Coroot space
//
intrinsic CorootSpace( W::GrpPermCox ) -> ModTupRng
{The coroot space of W}

  C := CartanMatrix( W );
  return RSpace( BaseRing(C), Nrows(C) );
end intrinsic;

intrinsic CorootSpace( W::GrpMat ) -> ModTupRng
{"} // "
  require IsReflectionGroup( W ) : "Not a reflection group";
  return RSpace( W );
end intrinsic;

// -------------------------------------------------
//
// Simple roots
//
intrinsic SimpleRoots( W::GrpPermCox ) -> Mtrx
{The simple roots of W as the rows of a matrix}
  return SimpleRoots( groupToRoot( W ) );
end intrinsic;

intrinsic SimpleRoots( W::GrpMat ) -> Mtrx
{"} // "
  require IsReflectionGroup( W ) : "Not a reflection group";
  return W`SimpleRoots;
end intrinsic;

// -------------------------------------------------
//
// Simple coroots
//
intrinsic SimpleCoroots( W::GrpPermCox ) -> Mtrx
{The simple coroots of W as the rows of a matrix}
  return SimpleCoroots( groupToRoot( W ) );
end intrinsic;

intrinsic SimpleCoroots( W::GrpMat ) -> Mtrx
{"} // "
  require IsReflectionGroup( W ) : "Not a reflection group";
  return W`SimpleCoroots;
end intrinsic;

// -------------------------------------------------
//
// Simple orders
//
intrinsic SimpleOrders( W::GrpMat ) -> Mtrx
{The simple orders of W as the rows of a matrix}
  require IsReflectionGroup( W ) : "Not a reflection group";
  return W`PseudoreflectionOrders;
end intrinsic;


// -------------------------------------------------
//
// Number of positive roots
//
intrinsic NumberOfPositiveRoots( W::GrpFPCox ) -> RngIntElt
{The number of positive roots of W}
  if not IsFinite( W ) then
    return Infinity();
  else
    return NumberOfPositiveRoots( groupToRoot(W) );
  end if;
end intrinsic;

intrinsic NumberOfPositiveRoots( W::GrpPermCox ) -> RngIntElt
{"} // " get comment from the previous intrinsic
  return NumberOfPositiveRoots( groupToRoot( W ) );
end intrinsic;

intrinsic NumberOfPositiveRoots( W::GrpMat ) -> RngIntElt
{"} // " get comment from the previous intrinsic
  require isRealReflGrp( W ) : "Not a real reflection group";
  if not IsFinite( W ) then
    return Infinity();
  else
    R := groupToRootDatum( W );
    return NumberOfPositiveRoots( R );
  end if;
end intrinsic;

// -------------------------------------------------
//
// Rank
//
intrinsic Rank( W::GrpFPCox ) -> RngIntElt
{The rank of W}
  return NumberOfGenerators( W );
end intrinsic;

intrinsic Rank( W::GrpPermCox ) -> RngIntElt
{The rank of W}
  return Rank( groupToRoot(W) );
end intrinsic;

intrinsic Rank( W::GrpMat ) -> RngIntElt
{The rank of W}
  require IsReflectionGroup( W ) : "Not a reflection group";
  try 
    flag, _, _ := IsRealReflectionGroup( W );
    return NumberOfGenerators( W );
  catch e;
    return Dimension( W ) - Dimension(Fix(GModule(W)));
  end try;
end intrinsic;

// -------------------------------------------------
//
// Dimension
//
intrinsic Dimension( W::GrpPermCox ) -> RngIntElt
{The dimension of W}
  return Dimension( groupToRoot( W ) );
end intrinsic;


// -------------------------------------------------
//
// Cartan name
//
intrinsic CartanName( W::GrpFPCox ) -> MonStgElt
{The Cartan name of W}
  type := groupToType( W );
  require Type(type) ne BoolElt : 
    "CartanName is available only for finite or affine Coxeter groups";
//  require isFinAffType( type ) : "The group must be finite or affine";
  return typeToName( type );
end intrinsic;

intrinsic CartanName( W::GrpPermCox ) -> MonStgElt
{The Cartan name of W}
  return CartanName( groupToRoot( W ) );
end intrinsic;

intrinsic CartanName( W::GrpMat ) -> MonStgElt
{The Cartan name of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  type := groupToType( W );
  require Type(type) ne BoolElt : 
    "CartanName is available only for finite or affine Coxeter groups";
//  require isFinAffType( type ) : "The group must be finite or affine";
  return typeToName( type );
end intrinsic;

// -------------------------------------------------
//
// Fundamental group
//
intrinsic FundamentalGroup( W::GrpPermCox ) -> GrpAb
{The fundamental group of W}
  return FundamentalGroup( groupToRootDatum( W ) );
end intrinsic;

intrinsic FundamentalGroup( W::GrpMat ) -> GrpAb
{The fundamental group of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRootDatum( W );
  return FundamentalGroup( R );
end intrinsic;

// -------------------------------------------------
//
// Isogeny group
//
intrinsic IsogenyGroup( W::GrpPermCox ) -> GrpAb
{The isogeny group of W}
  return IsogenyGroup( groupToRootDatum( W ) );
end intrinsic;

intrinsic IsogenyGroup( W::GrpMat ) -> GrpAb
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRootDatum( W );
  return IsogenyGroup( R );
end intrinsic;

// -------------------------------------------------
//
// Coisogeny group
//
intrinsic CoisogenyGroup( W::GrpPermCox ) -> GrpAb
{The coisogeny group of W}
  return CoisogenyGroup( groupToRootDatum( W ) );
end intrinsic;

intrinsic CoisogenyGroup( W::GrpMat ) -> GrpAb
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRootDatum( W );
  return CoisogenyGroup( R );
end intrinsic;

// =================================================
//
// Roots, coroots and weights
//
// =================================================

// -------------------------------------------------
//
// Roots
//
intrinsic Roots( W::GrpPermCox : Basis := "Standard" ) -> {@ @}
{The roots of W}
  return Roots( groupToRoot( W ) : Basis := Basis );
end intrinsic;

intrinsic Roots( W::GrpMat : Basis := "Standard" ) -> {@ @}
{ " } // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return Roots( R : Basis := Basis );
end intrinsic;

// -------------------------------------------------
//
// Positive roots
//
intrinsic PositiveRoots( W::GrpPermCox : Basis := "Standard" ) -> {@@}
{The positive roots of W}
  return PositiveRoots( groupToRoot( W ) : Basis := Basis );
end intrinsic;

intrinsic PositiveRoots( W::GrpMat : Basis := "Standard" ) -> {@@}
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return PositiveRoots( R : Basis := Basis );
end intrinsic;

// -------------------------------------------------
//
// Root
//
intrinsic Root( W::GrpPermCox, r::RngIntElt : Basis := "Standard" ) -> ModTupFld
{The rth root of W}
  return Root( groupToRoot( W ), r : Basis := Basis );
end intrinsic;

intrinsic Root( W::GrpMat, r::RngIntElt : Basis := "Standard" ) -> ModTupFld
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return Root( R, r : Basis := Basis );
end intrinsic;

// -------------------------------------------------
//
// Root position
//
intrinsic RootPosition( W::GrpPermCox, v : Basis := "Standard" ) -> RngIntElt
{The position of the vector v as a root of W}
  return RootPosition( groupToRoot( W ), v : Basis := Basis );
end intrinsic;

intrinsic RootPosition( W::GrpMat, v : Basis := "Standard" ) -> RngIntElt
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return RootPosition( R, v : Basis := Basis );
end intrinsic;

// -------------------------------------------------
//
// Coroots
//
intrinsic Coroots( W::GrpPermCox : Basis := "Standard" ) -> {@@}
{The coroots of W}
  return Coroots( groupToRoot( W ) : Basis := Basis );
end intrinsic;

intrinsic Coroots( W::GrpMat : Basis := "Standard" ) -> {@@}
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return Coroots( R : Basis := Basis );
end intrinsic;

// -------------------------------------------------
//
// Positive coroots
//
intrinsic PositiveCoroots( W::GrpPermCox : Basis := "Standard" ) -> {@@}
{The positive coroots of W}
  return PositiveCoroots( groupToRoot( W ) : Basis := Basis );
end intrinsic;

intrinsic PositiveCoroots( W::GrpMat : Basis := "Standard" ) -> {@@}
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return PositiveCoroots( R : Basis := Basis );
end intrinsic;

// -------------------------------------------------
//
// Coroot
//
intrinsic Coroot(W::GrpPermCox,r::RngIntElt : Basis := "Standard") -> ModTupFld
{The rth coroot of W}
  return Coroot( groupToRoot( W ), r : Basis := Basis );
end intrinsic;

intrinsic Coroot(W::GrpMat, r::RngIntElt : Basis := "Standard") -> ModTupFld
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return Coroot( R, r : Basis := Basis );
end intrinsic;

// -------------------------------------------------
//
// Coroot position
//
intrinsic CorootPosition( W::GrpPermCox, v : Basis := "Standard" ) -> RngIntElt
{The position of the vector v as a coroot of W}
  return CorootPosition( groupToRoot( W ), v : Basis := Basis );
end intrinsic;

intrinsic CorootPosition( W::GrpMat, v : Basis := "Standard" ) -> RngIntElt
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return CorootPosition( R, v : Basis := Basis );
end intrinsic;


// -------------------------------------------------
//
// Dynkin/Coxeter diagrams
//
intrinsic CoxeterDiagram( W::GrpFPCox )
{Print the Coxeter diagram of W}
  M := CoxeterMatrix( W );
  require IsCoxeterFinite( M ) or IsCoxeterAffine( M ) : "Finite and affine groups only";
  CoxeterDiagram( M );
end intrinsic;

intrinsic CoxeterDiagram( W::GrpPermCox )
{"} // "
  M := CoxeterMatrix( W );
  CoxeterDiagram( M );
end intrinsic;

intrinsic CoxeterDiagram( W::GrpMat )
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  M := CoxeterMatrix( W );
  require IsCoxeterFinite( M ) or IsCoxeterAffine( M ) : "Finite and affine groups only";
  CoxeterDiagram( M );
end intrinsic;


intrinsic DynkinDiagram( W::GrpPermCox )
{Print the Dynkin diagram of W}
  C := CartanMatrix( W );
  require (IsCoxeterFinite( C ) or IsCoxeterAffine( C )) and 
  IsCrystallographic( C ) : "Finite and affine Crystallographic groups only";
  DynkinDiagram( C );
end intrinsic;

intrinsic DynkinDiagram( W::GrpMat )
{"} // "
  require isRealReflGrp( W ) : "Not a real reflection group";
  C := CartanMatrix( W );
  require (IsCoxeterFinite( C ) or IsCoxeterAffine( C )) and IsCrystallographic( C ) :
  "crystallographic groups only";
  DynkinDiagram( C );
end intrinsic;



// -------------------------------------------------
//
// Basic degrees and codegrees
// 
// We use Carter's table for degrees of real refl grps.
// We use Don Taylors code for complex refl grps and
// for codegrees
// 
//
degrees := function(G)
  K := CoefficientRing(G);
  P := PolynomialRing(K); x := P.1;
  f := &+[ cl[2]*x^Dimension(Eigenspace(cl[3],1)) : cl in Classes(G) ];
  deg := [Integers()|];
  for p in Roots(f) do
    for j := 1 to p[2] do Append(~deg,-p[1]+1); end for;
  end for;
  return Sort(deg);
end function;

codegrees := function(G)
  K := CoefficientRing(G);
  P := PolynomialRing(K); x := P.1;
  f := &+[ cl[2]*Determinant(cl[3])*x^Dimension(Eigenspace(cl[3],1)) :
     cl in Classes(G) ];
  codeg := [Integers()|];
  for p in Roots(f) do
    for j := 1 to p[2] do Append(~codeg,p[1]-1); end for;
  end for;
  return codeg;
end function;

intrinsic BasicDegrees( W::GrpFPCox ) -> []
{The degrees of the basic polynomial invariants of W}
  require IsFinite( W ) : "The group must be finite";
  deg := BasicDegrees( groupToRoot( W ) );  // lose the second returned value
  return deg;
end intrinsic;

intrinsic BasicDegrees( W::GrpPermCox ) -> []
{The degrees of the basic polynomial invariants of W}
  deg := BasicDegrees( groupToRoot( W ) );  // lose the second returned value
  return deg;
end intrinsic;

intrinsic BasicDegrees( W::GrpMat ) -> []
{The degrees of the basic polynomial invariants of W}
  require IsReflectionGroup( W ) : "Not a reflection group";
  require IsFinite( W ) : "The group must be finite";
  if isRealReflGrp( W ) then
    deg := BasicDegrees( groupToRoot( W ) );  // lose the second returned value
    d := Dimension(W);
    k := d - #deg;
    if k gt 0 then
      deg := [ 1 : i in [1..k] ] cat deg;
    end if;
    return deg;
  else
    return degrees(W);
  end if;
end intrinsic;

intrinsic BasicCodegrees( W::GrpMat ) -> []
{The basic codegrees of W}
  require IsReflectionGroup( W ) : "Not a reflection group";
  require IsFinite( W ) : "The group must be finite";
  return codegrees(W);
end intrinsic;

intrinsic BasicCodegrees( W::GrpFPCox ) -> []
{The basic codegrees of W}
  require IsFinite( W ) : "The group must be finite";
  return BasicCodegrees( ReflectionGroup( W ) );
end intrinsic;

intrinsic BasicCodegrees( W::GrpPermCox ) -> []
{The basic codegrees of W}
  return BasicCodegrees( ReflectionGroup( W ) );
end intrinsic;




// -------------------------------------------------
//
// Fundamental weights
//
intrinsic FundamentalWeights( W::GrpPermCox : Basis := "Standard" ) -> Mtrx
{The fundamental weights of W as the rows of a matrix}
  return FundamentalWeights( RootDatum( W ) : Basis:=Basis );
end intrinsic;  

intrinsic FundamentalWeights( W::GrpMat : Basis := "Standard" ) -> Mtrx
{The fundamental weights of W as the rows of a matrix}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRootDatum( W );
  return FundamentalWeights( R : Basis:=Basis );
end intrinsic;  

// -------------------------------------------------
//
// Fundamental coweights
//
intrinsic FundamentalCoweights( W::GrpPermCox : Basis := "Standard" ) -> Mtrx
{The fundamental coweights of W as the rows of a matrix}
  return FundamentalCoweights( RootDatum( W ) : Basis:=Basis );
end intrinsic;  

intrinsic FundamentalCoweights( W::GrpMat : Basis := "Standard" ) -> Mtrx
{The fundamental coweights of W as the rows of a matrix}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRootDatum( W );
  return FundamentalCoweights( R : Basis:=Basis );
end intrinsic;  

// -------------------------------------------------
//
// Weight lattice
//

intrinsic WeightLattice( W::GrpPermCox ) -> Lat
{The weight lattice of W}
  return WeightLattice( RootDatum( W ) );
end intrinsic;

intrinsic WeightLattice( W::GrpMat ) -> Lat
{The weight lattice of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRootDatum( W );
  return WeightLattice( R );
end intrinsic;

// -------------------------------------------------
//
// Coweight lattice
//
intrinsic CoweightLattice( W::GrpPermCox ) -> Lat
{The weight lattice of W}
  return CoweightLattice( RootDatum( W ) );
end intrinsic;  

intrinsic CoweightLattice( W::GrpMat ) -> Lat
{The weight lattice of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRootDatum( W );
  return CoweightLattice( R );
end intrinsic;  

// -------------------------------------------------
//
// Dominant weight
//
intrinsic DominantWeight( W::GrpPermCox, v : Basis := "Standard" ) -> 
  ModTupFldElt, GrpFPCoxElt
{The dominant weight of W in the orbit of the weight v}
  return DominantWeight( RootDatum(W), v : Basis:=Basis );
end intrinsic;

intrinsic DominantWeight( W::GrpMat, v : Basis := "Standard" ) -> 
  ModTupFldElt, GrpFPCoxElt
{The dominant weight of W in the orbit of the weight v}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRootDatum( W );
  return DominantWeight( R, v : Basis:=Basis );
end intrinsic;

// -------------------------------------------------
//
// Weight orbit
//
intrinsic WeightOrbit( W::GrpPermCox, v : Basis := "Standard" ) -> SetIndx, SeqEnum
{The orbit the weight v under the Coxeter group W}
  return WeightOrbit( RootDatum(W), v : Basis:=Basis );
end intrinsic;

intrinsic WeightOrbit( W::GrpMat, v : Basis := "Standard" ) -> SetIndx, SeqEnum
{The orbit the weight v under the Coxeter group W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRootDatum( W );
  return WeightOrbit( R, v : Basis:=Basis );
end intrinsic;

// -------------------------------------------------
//
// Overgroup
//
intrinsic Overgroup( W::GrpFPCox ) -> GrpFPCox
{The overgroup of W}
  return assigned W`Overgroup select W`Overgroup else W;
end intrinsic;

intrinsic Overgroup( W::GrpPermCox ) -> GrpPermCox
  {"} // " get comment from the previous intrinsic
  return assigned W`Overgroup select W`Overgroup else W;
end intrinsic;

intrinsic Overgroup( W::GrpMat ) -> GrpMat
  {"} // " get comment from the previous intrinsic
  return assigned W`Overgroup select W`Overgroup else W;
end intrinsic;

// -------------------------------------------------
//
// Overdatum
//
intrinsic Overdatum( W::GrpPermCox ) -> RootDtm
{The root datum of the overgroup of W}
  return RootDatum( Overgroup( W ) );
end intrinsic;

intrinsic Overdatum( W::GrpMat ) -> RootDtm
{The root datum of the overgroup of W}
  return RootDatum( Overgroup( W ) );
end intrinsic;



// =================================================
//
// Reflections
//
// =================================================
intrinsic SimpleReflectionMatrices( W::GrpPermCox : Basis := "Standard" ) -> []
{The reflection matrices of the simple roots of W}
  return SimpleReflectionMatrices( groupToRoot( W ) : Basis:=Basis );
end intrinsic;

intrinsic SimpleReflectionMatrices( W::GrpMat : Basis := "Standard" ) -> []
{The reflection matrices of the simple roots of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  if IsFinite( W ) and 
  ISA(Category(groupToRoot( W )), RootDtm) then
    return SimpleReflectionMatrices( groupToRoot(W) : Basis:=Basis );
  else
    case Basis:
    when "Root":
      C := CartanMatrix( W );
      roots := Parent( C )!1;  coroots := Transpose( C );
      return [ Reflection( roots[1], coroots[i] ) : i in [1..Nrows(roots)] ];
    when "Standard":
      return [ W.i : i in [1..NumberOfGenerators(W) ] ];
    when "Weight":
      error "Weights only defined for finite, crystallographic groups";
    else
      error "Invalid Basis parameter";
    end case;
  end if;
end intrinsic;

intrinsic ReflectionMatrices( W::GrpPermCox : Basis := "Standard" ) -> []
{The reflection matrices of the roots of W}
  return ReflectionMatrices( groupToRoot( W ) : Basis := Basis );
end intrinsic;

intrinsic ReflectionMatrices( W::GrpMat : Basis := "Standard" ) -> []
{The reflection matrices of the roots of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return ReflectionMatrices( R : Basis := Basis );
end intrinsic;

intrinsic ReflectionMatrix( W::GrpPermCox, r::RngIntElt : Basis := "Standard" ) 
  -> AlgMatElt
{The reflection matrix of the rth root of W}
  return ReflectionMatrix( groupToRoot( W ), r : Basis := Basis );
end intrinsic;

intrinsic ReflectionMatrix( W::GrpMat, r::RngIntElt : Basis := "Standard" ) 
  -> AlgMatElt
{The reflection matrix of the rth root of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  return ReflectionMatrix( groupToRoot( W ), r : Basis := Basis );
end intrinsic;

intrinsic SimpleCoreflectionMatrices( W::GrpPermCox : Basis := "Standard" ) -> []
{The reflection matrices of the simple coroots of W}
  return SimpleCoreflectionMatrices( groupToRoot( W ) : Basis:=Basis );
end intrinsic;

intrinsic SimpleCoreflectionMatrices( W::GrpMat : Basis := "Standard" ) -> []
{The reflection matrices of the simple coroots of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  if IsFinite(W) and ISA(Category(groupToRoot( W )), RootDtm) then
    return SimpleCoreflectionMatrices( groupToRoot( W ) : Basis:=Basis );
  else
    case Basis:
    when "Root":
      C := CartanMatrix( W );
      roots := C;  coroots := Parent( C )!1;
    when "Standard":
      R := groupToRoot( W );
      roots := SimpleCoroots( R );  coroots := SimpleRoots( R );
    when "Weight":
      error "Weights only defined for finite, crystallographic groups";
    else
      error "Invalid Basis parameter";
    end case;
    return [ Reflection( roots[1], coroots[i] ) : i in [1..Nrows(roots)] ];
  end if;
end intrinsic;

intrinsic CoreflectionMatrices( W::GrpPermCox : Basis := "Standard" ) -> []
{The reflection matrices of the coroots of W}
  return CoreflectionMatrices( groupToRoot( W ) : Basis := Basis );
end intrinsic;

intrinsic CoreflectionMatrices( W::GrpMat : Basis := "Standard" ) -> []
{The reflection matrices of the coroots of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  return CoreflectionMatrices( groupToRoot( W ) : Basis := Basis );
end intrinsic;

intrinsic CoreflectionMatrix( W::GrpPermCox, r::RngIntElt : Basis := "Standard" ) -> AlgMatElt
{The reflection matrix of the rth root of W}
  return CoreflectionMatrix( groupToRoot( W ), r : Basis := Basis );
end intrinsic;

intrinsic CoreflectionMatrix( W::GrpMat, r::RngIntElt : Basis := "Standard" ) -> AlgMatElt
{The reflection matrix of the rth root of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  return CoreflectionMatrix( groupToRoot(W), r : Basis := Basis );
end intrinsic;

// -------------------------------------------------
//
// Simple reflection permutations
//
forward inc;

intrinsic SimpleReflections( W::GrpFPCox ) -> []
{The simple roots of W}
  return [ W.i : i in [1..Ngens(W)] ];
end intrinsic;


intrinsic SimpleReflections( W::GrpPermCox : Local := false ) -> []
{The action of the simple roots on the roots of W}
  if Local or not assigned W`RootDatum then
    return ChangeUniverse( SimpleReflectionPermutations( groupToRoot( W ) ), W );
  else
    return [ ReflectionPermutation( Overdatum(W), inc(W,r) ) : r in [1..Rank(W)] ];
  end if;
end intrinsic;

intrinsic SimpleReflectionPermutations( W::GrpPermCox : Local := false ) -> []
{The action of the simple roots on the roots of W}
  return SimpleReflections( W : Local:=Local );
end intrinsic;


intrinsic SimpleReflectionPermutations( W::GrpMat ) -> [] 
{The action of the simple roots on the roots of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  R := groupToRoot( W );
  return SimpleReflectionPermutations( R );
end intrinsic;


// -------------------------------------------------
//
// Reflection permutations
//
intrinsic Reflections( W::GrpPermCox : Local := false ) -> []
{The action of the roots on the roots of W}
  if Local or not assigned W`RootDatum then
    return ChangeUniverse( ReflectionPermutations( groupToRoot( W ) ), W );
  else
    return [ W | ReflectionPermutation( Overdatum(W), inc(W,r) ) : 
      r in [1..2*NumPosRoots(W)] ];
  end if;
end intrinsic;

intrinsic ReflectionPermutations( W::GrpPermCox : Local := false ) -> []
{The action of the roots on the roots of W}
  return Reflections( W : Local:=Local );
end intrinsic


intrinsic ReflectionPermutations( W::GrpMat ) -> []
{The action of the roots on the roots of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  return ReflectionPermutations( groupToRoot( W ) );
end intrinsic;

// -------------------------------------------------
//
// Reflection permutation
//
intrinsic Reflection( W::GrpPermCox, r::RngIntElt : Local := false )
  -> GrpPermElt
{The action of the rth root on the roots of W}
  if Local or not assigned W`RootDatum then
    return ReflectionPermutation( groupToRoot( W ), r );
  else
    return ReflectionPermutation( Overdatum(W), inc(W,r) );
  end if;
end intrinsic;

intrinsic ReflectionPermutation( W::GrpPermCox, r::RngIntElt : Local := false )
  -> GrpPermElt
{The action of the rth root on the roots of W}
  return Reflection( W, r : Local:=Local );
end intrinsic;


intrinsic ReflectionPermutation( W::GrpMat, r::RngIntElt : Local := false )
  -> GrpPermElt
{The action of the rth root on the roots of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  if Local then
    return ReflectionPermutation( R, r );
  else
    return ReflectionPermutation( Overdatum(W), inc(W,r) );
  end if;
end intrinsic;



// -------------------------------------------------
//
// Reflection words
//
intrinsic Reflections( W::GrpFPCox ) -> []
{The words of the reflections in the roots of W}
  require IsFinite( W ) : "The Coxeter group must be finite";
  wds := ReflectionWords( groupToRoot(W) );
  ChangeUniverse( ~wds, W );
  return wds;
end intrinsic;

intrinsic ReflectionWords( W::GrpFPCox ) -> []
{The words of the reflections in the roots of W}
  return Reflections( W );
end intrinsic;


intrinsic ReflectionWords( W::GrpPermCox ) -> []
{The words of the reflections in the roots of W}
  require IsFinite( W ) : "The Coxeter group must be finite";
  return ReflectionWords( groupToRoot(W) );
end intrinsic;


intrinsic ReflectionWords( W::GrpMat ) -> []
{The words of the reflections in the roots of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return ReflectionWords( R );
end intrinsic;


// -------------------------------------------------
//
// Reflection word
//
intrinsic ReflectionWord( W::GrpPermCox, r::RngIntElt ) -> GrpFPCoxElt
{The word of the reflection in the rth root of W}
  require IsFinite( W ) : "The Coxeter group must be finite";
  return ReflectionWord( groupToRoot(W), r );
end intrinsic;

intrinsic ReflectionWord( W::GrpMat, r::RngIntElt ) -> GrpFPCoxElt
{The word of the reflection in the rth root of W}
  require isRealReflGrp( W ) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRoot( W );
  return ReflectionWord( R, r );
end intrinsic;


// ====================================================
//
// Properties
//
// ====================================================

// -------------------------------------------------
//
// Finite
//
intrinsic IsFinite( W::GrpFPCox ) -> BoolElt, RngIntElt
{True iff W is finite}
  o := Order( W );
  flag := Category( o ) eq RngIntElt and o ne 0;
  if flag then 
    return true, o;
  else
    return false, _;
  end if;
end intrinsic;

intrinsic IsFinite( W::GrpPerm ) -> BoolElt, RngIntElt
{True iff W is finite}
  return true, #W;
end intrinsic;

intrinsic IsFinite( W::GrpPermCox ) -> BoolElt, RngIntElt
{True iff W is finite}
  return true, #W;
end intrinsic;

// -------------------------------------------------
//
// Affine
//
intrinsic IsAffine( W::GrpFPCox ) -> BoolElt
{True iff W is affine}
  return IsCoxeterAffine( CoxeterMatrix( W ) );
end intrinsic;

intrinsic IsAffine( W::GrpPermCox ) -> BoolElt
{True iff W is affine}
  return false;
end intrinsic;

// -------------------------------------------------
//
// Hyperbolic
//
intrinsic IsHyperbolic( W::GrpFPCox ) -> BoolElt
{True iff W is hyperbolic}
  return IsCoxeterHyperbolic( CoxeterMatrix( W ) );
end intrinsic;

intrinsic IsHyperbolic( W::GrpPermCox ) -> BoolElt
{True iff W is hyperbolic}
  return false;
end intrinsic;

// -------------------------------------------------
//
// Compact hyperbolic
//
intrinsic IsCompactHyperbolic( W::GrpFPCox ) -> BoolElt
{True iff W is compact hyperbolic}
  return IsCoxeterCompactHyperbolic( CoxeterMatrix( W ) );
end intrinsic;

intrinsic IsCompactHyperbolic( W::GrpPermCox ) -> BoolElt
{True iff W is compact hyperbolic}
  return false;
end intrinsic;

// -------------------------------------------------
//
// Irreducible
//
intrinsic IsIrreducible( W::GrpFPCox ) -> BoolElt
{True iff W is an irreducible Coxeter group}
  return IsCoxeterIrreducible( CoxeterMatrix( W ) );
end intrinsic;

intrinsic IsIrreducible( W::GrpPermCox ) -> BoolElt
{True iff W is an irreducible Coxeter group}
  return IsIrreducible( groupToRoot( W ) );
end intrinsic;

// function already exists for matrix groups


// -------------------------------------------------
//
// Semisimple
//
intrinsic IsSemisimple( W::GrpPermCox ) -> BoolElt
{True iff W is semisimple}
  R := groupToRootDatum( W );
  return IsSemisimple( R );
end intrinsic;

// -------------------------------------------------
//
// Crystallographic
//
intrinsic IsCrystallographic( W::GrpPermCox ) -> BoolElt
{True iff W is crystallographic}
  return IsCrystallographic( CartanMatrix( W ) );
end intrinsic;

intrinsic IsCrystallographic( W::GrpMat ) -> BoolElt
{True iff W is a crystallographic reflection group}
  return IsCrystallographic( CartanMatrix( W ) );
end intrinsic;

// -------------------------------------------------
//
// Simply laced
//
intrinsic IsSimplyLaced( W::GrpFPCox ) -> BoolElt
{True iff W is simply laced}
  return IsSimplyLaced( CoxeterMatrix( W ) );
end intrinsic;

intrinsic IsSimplyLaced( W::GrpPermCox ) -> BoolElt
{True iff W is simply laced}
  return IsSimplyLaced( groupToRoot( W ) );
end intrinsic;

intrinsic IsSimplyLaced( W::GrpMat ) -> BoolElt
{True iff W is a simply laced reflection group}
  require isRealReflGrp( W ) : "Not a real reflection group";
  return IsSimplyLaced( CoxeterMatrix( W ) );
end intrinsic;




// ====================================================
//
// Isomorphism etc
//
// ====================================================

intrinsic IsCoxeterIsomorphic( W1::GrpMat, W2::GrpMat ) -> BoolElt, []
{True iff W1 and W2 are isomorphic as Coxeter groups}
  require isRealReflGrp( W1 ) : 
  "The first group is not a real reflection group";
  require isRealReflGrp( W2 ) : 
  "The second group is not a real reflection group";
  return IsCoxeterIsomorphic( CoxeterMatrix(W1), CoxeterMatrix(W2) );
end intrinsic;

intrinsic IsCoxeterIsomorphic( W1::GrpFPCox, W2::GrpFPCox ) -> BoolElt, []
{True iff W1 and W2 are isomorphic as Coxeter groups}
  return IsCoxeterIsomorphic( CoxeterMatrix(W1), CoxeterMatrix(W2) );
end intrinsic;

intrinsic IsCoxeterIsomorphic( W1::GrpPermCox, W2::GrpPermCox : 
  Crystallographic:=false ) -> BoolElt, []
{True iff W1 and W2 are isomorphic as Coxeter groups}
  return IsCoxeterIsomorphic( CoxeterMatrix(W1), CoxeterMatrix(W2) );
end intrinsic;


intrinsic IsCartanEquivalent( W1::GrpMat, W2::GrpMat ) -> BoolElt
{True iff W1 and W2 are Cartan equivalent}
  require IsCrystallographic(W1) : "The first group is not crystallographic";
  require IsCrystallographic(W2) : "The second group is not crystallographic";
  return IsCartanEquivalent( CartanMatrix(W1), CartanMatrix(W2)  );
end intrinsic;

/*intrinsic IsCartanEquivalent( W1::GrpFPCox, W2::GrpFPCox ) -> BoolElt
{True iff W1 and W2 are Cartan equivalent}
  return IsCartanEquivalent( CartanMatrix(W1), CartanMatrix(W2)  );
end intrinsic;*/

intrinsic IsCartanEquivalent( W1::GrpPermCox, W2::GrpPermCox ) -> BoolElt
{True iff W1 and W2 are Cartan equivalent}
  require IsCrystallographic(W1) : "The first group is not crystallographic";
  require IsCrystallographic(W2) : "The second group is not crystallographic";
  
  return IsCartanEquivalent( CartanMatrix(W1), CartanMatrix(W2)  );
end intrinsic;

  
// ====================================================
//
// Braid groups
//
// ====================================================

intrinsic BraidGroup( W::GrpFPCox ) -> GrpFP, Map
{The braid group of W}
  if not assigned W`BraidGroup then
    M := W`CoxeterMatrix;
    for i in [1..Ncols(M)] do  M[i,i] := -1;  end for;
    B := coxeterToBraidGroup( M );
    H := hom< B -> W | [ W.i : i in [1..NumberOfGenerators(W)] ]>;
    W`BraidGroup := B;
    W`BraidGroupHom := H;
    return B, H;
  end if;
  return W`BraidGroup, W`BraidGroupHom;
  //B := W`BraidGroup;
  //return B, hom< B -> W | [ W.i : i in [1..NumberOfGenerators(W)] ] >;;
end intrinsic;

intrinsic PureBraidGroup( W::GrpFPCox ) -> GrpFP
{The pure braid group of W}
  B := BraidGroup(W);
  M := W`CoxeterMatrix;
  if Nrows(M) eq 0 then  return B, IdentityHomomorphism(B);  end if;
  return sub< B | [ (B.i)^2 : i in [1..NumberOfGenerators(B)] ] >;
end intrinsic;


// ====================================================
//
// Arithmetic
//
// ====================================================

import "reftable2.m":refTable;

intrinsic ReflectionTable ( W :: GrpFPCox ) -> SeqEnum
{Internal.  The table giving the action of the generators of W on the elementary
roots}
  if assigned W`ReflectionTable then
    T := W`ReflectionTable;
  else
    T := refTable( CoxeterMatrix(W) );
    W`ReflectionTable := T;
  end if;
  return T;
end intrinsic;

intrinsic 'eq'( x::GrpFPCoxElt, y::RngIntElt ) -> BoolElt
{True iff x is equal to y}
  require y eq 1 : "Incompatable categories";
  return #x eq 0;
end intrinsic;

intrinsic Name( W::GrpFPCox, i::RngIntElt ) -> GrpFPCoxElt
{The ith generator}
  return SequenceToElement(W, [Abs(i)]);
end intrinsic;

procedure normalise(M,~w)
  w := Eltseq(InternalMultiply(ReflectionTable(M), SequenceToElement(M,w)));
end procedure;

/*
intrinsic '!'( M::GrpFPCox, x::SeqEnum ) -> GrpFPCoxElt
{Coerce x into M}
  return InternalMultiply(SequenceToElement(M,x));
end intrinsic;
*/

bangNoCheck := func< M, x | SequenceToElement(M, x) >;

intrinsic '*:='( ~x::GrpFPCoxElt, y::GrpFPCoxElt )
{Replace x with x * y in normal form}
  x := InternalMultiply(x, y);
end intrinsic;

intrinsic '&*'( S::[GrpFPCoxElt] ) -> GrpFPCoxElt
{The product of all elements of S}
  W := Universe( S );
  if #S eq 0 then
    w := SequenceToElement(W, []);
  else
    w := S[1];
    T := ReflectionTable(W);
    for i in [2..#S] do
      w := InternalMultiply(T, w, S[i]);
    end for;
  end if;
  return w;
end intrinsic;

intrinsic Inverse( w::GrpFPCoxElt ) -> GrpFPElt
{The inverse of w}
  return InternalInverse(w);
end intrinsic;

/* This is now written in C (I think)
intrinsic '^'( x::GrpFPCoxElt, n::RngIntElt ) -> GrpFPCoxElt
{The nth power of x}
  W := Parent(x);
  if n eq 0 then
    return SequenceToElement(W, []);
  end if;

  T := ReflectionTable(W);
  if n gt 0 then
    power := x;
  else
    power := InternalInverse(T, x);  n := -n;
  end if;

  if n eq 1 then return power; end if;

  ret := SequenceToElement(W, []);
  repeat
    if n mod 2 eq 1 then
      n := n-1;
      ret := InternalMultiply(T, ret, power);
    end if;
    if n ne 0 then
      n div:= 2;
      power := InternalMultiply(T, power, power);
    end if;
  until n eq 0;
  return ret;
end intrinsic;*/

intrinsic '^'( x::GrpFPCoxElt, y::GrpFPCoxElt ) -> GrpFPCoxElt
{Conjugate of x by y}
  return Inverse( y ) * x * y;
end intrinsic;

intrinsic Order( x::GrpFPCoxElt ) -> RngIntElt
{The order of x}  // This could be more efficient
  i := 1;  y := x;
  T := ReflectionTable(Parent(x));
  repeat
    if y eq 1 then
      return i;  
    else
      y := InternalMultiply(T, y, x);
      i +:= 1;
    end if;
  until false;
end intrinsic;

// ====================================================
//
// G-sets
//
// ====================================================

intrinsic RootGSet( W::GrpPermCox : Basis:="Standard" ) -> GSetIndx
{The G-set of W on its roots}
  return GSetFromIndexed( W, Roots( W : Basis:=Basis ) );
end intrinsic;

intrinsic CorootGSet( W::GrpPermCox : Basis:="Standard" ) -> GSetIndx
{The G-set of W on its coroots}
  return GSetFromIndexed( W, Coroots( W : Basis:=Basis ) );
end intrinsic;

// ====================================================
//
// Actions
//
// ====================================================

// ----------------------------------------------------
//
// On indices
//
/*intrinsic Action( W::GrpFPCox ) -> Map
{The action of the Coxeter presentation W on the (co)root indices}
  require IsFinite( W ) : "Not implemented for infinite groups";
  R := groupToRoot( G );
  C := CoxeterGroup( R );
  X := {1..2*NumPosRoots(C)};
  return map< car<X,W> -> X | x :-> WordOnRoot(C,x[1],x[2]) >;
end intrinsic;*/

intrinsic Action( W::GrpMat ) -> Map
{The action of the finite real reflection group W on the (co)root indices}
  require isRealReflGrp(W) : "The group must be a reflection group";
  require IsFinite( W ) : "Only finite groups have a permutation representation"; 
  R := groupToRoot( W );
  X := {1..2*NumPosRoots(R)};
  return map< car<X,W> -> X | 
  x :-> RootPosition( R, Root(R,x[1]:Basis:="Root")*x[2] : Basis:="Root") >;
end intrinsic;

// ----------------------------------------------------
//
// On (co)root space
//
/*intrinsic RootAction( W::GrpFPCox : Basis := "Standard") -> Map
{The action of W on the root space}
  R := groupToRoot( W );
  C := CoxeterGroup( RootDatum(W) );
  X := RootSpace(C);
  return map< car<X,W> -> X | x :-> WordOnRootSpace(C,x[1],x[2]:Basis:=Basis) >;
end intrinsic;

intrinsic CorootAction( W::GrpFPCox : Basis := "Standard") -> Map
{The action of W on the coroot space}
  require assigned W`RootDatum : "W must have a root datum";
  C := CoxeterGroup( RootDatum(W) );
  X := CorootSpace(C);
  return map< car<X,W> -> X | x :-> WordOnCorootSpace(C,x[1],x[2]:Basis:=Basis) >;
end intrinsic;*/

ratIntMult := function(x,A)
  if Category(BaseRing(x)) eq FldRat then
    A := ChangeRing( A, Rationals() );
  elif Category(BaseRing(A)) eq FldRat then
    x := ChangeRing( x, Rationals() );
  end if;
  return x*A;
end function;

intrinsic RootAction( W::GrpPermCox : Basis := "Standard") -> Map
{The action of W on the root space}
  R := RootDatum(W);
  case Basis:
  when "Standard":
    X := R`Vstd;
  when "Root":
    X := R`Vrts;
  when "Weight":
    X := R`Vwgt;
  end case; 
  return map< car<X,W> -> X | x :->
  ratIntMult(x[1],PermToMatrix(W,x[2]:Basis:=Basis)) >;
end intrinsic;

intrinsic CorootAction( W::GrpPermCox : Basis := "Standard") -> Map
{The action of W on the coroot space}
  R := RootDatum(W);
  case Basis:
  when "Standard":
    X := R`Ustd;
  when "Root":
    X := R`Urts;
  when "Weight":
    X := R`Uwgt;
  end case; 
  return map< car<X,W> -> X | x :-> 
  ratIntMult(x[1],PermToDualMatrix(W,x[2]:Basis:=Basis)) >;
end intrinsic;


// ====================================================
//
// Reflection subgroups for GrpPermCox
//
// ====================================================

reflectionSubgroup := function( W, rts )
  O := Overgroup(W);
  if IsCrystallographic(O) then
    R := RootDatum(O);
  else 
    R := RootSystem(O);
  end if;
  try
    s, inc := sub< R | rts >;
  catch e
    error e`Object;
  end try;
  simples := inc[[1..Rank(s)]];
  H := sub< W | [ ReflectionPermutation(R, i) : i in simples ] >;
  H := GrpPermToCox(H);
  if Category(s) eq RootSys then
    H`RootSystem := s;
  else
    H`RootDatum := s;
  end if;
  H`Overgroup := O;
  H`RootInclusion := inc;
  H`RootRestriction := [ Position( inc, r ) : r in [1..2*NumPosRoots(R)] ];
  H`IsParabolic := ( Seqset(simples) subset {1..Rank(R)} );
  return H;
end function;

intrinsic ReflectionSubgroup( W::GrpPermCox, simples::SeqEnum ) -> GrpPermCox
{The Coxeter subgroup of W with the given simple roots}
  return reflectionSubgroup( W, simples );
end intrinsic;

intrinsic ReflectionSubgroup( W::GrpPermCox, gens::SetEnum ) -> GrpPermCox
{The Coxeter subgroup of W generated by the given reflections}
  return reflectionSubgroup( W, gens );
end intrinsic;

intrinsic IsReflectionSubgroup( W::GrpPermCox, H::GrpPermCox ) -> BoolElt
{True iff H is a Coxeter subgroup of W}
  OW := Overgroup(W); OH := Overgroup(H);
  if IsCrystallographic(OW) and IsCrystallographic(OH) then
    return RootDatum( OW ) eq RootDatum( OH ) and H subset W;
  else
    return RootSystem( OW ) eq RootSystem( OH )  and H subset W;
  end if;
end intrinsic;

intrinsic StandardParabolicSubgroup( W::GrpPermCox, simples::SetEnum ) -> GrpPermCox
{The standard parabolic subgroup of W generated by the given simples}
  require simples subset {1..Rank(W)} : "simples must be in range 1..", Rank(W);
  return ReflectionSubgroup( W, simples );
end intrinsic;

intrinsic IsStandardParabolicSubgroup( W::GrpPermCox, H::GrpPermCox ) -> BoolElt
{True iff H is a standard parabolic subgroup of W}
  return H subset W and (H eq W or H`IsParabolic);
end intrinsic;

intrinsic LocalCoxeterGroup( H::GrpPermCox ) -> GrpPermCox
{The Coxeter group isomorphic to Coxeter subgroup H,
but acting on its own roots}
  if not assigned H`Overgroup then
    return H, IdentityHomomorphism(H);
  end if;

  W := H`Overgroup;  R := RootDatum( W );
  sub := H`RootDatum;
  n := NumPosRoots( sub );  N := NumPosRoots( R );
  inc := H`RootInclusion;   res := H`RootRestriction;
  L := CoxeterGroup( sub );

  LtoH := function( p )
    // more efficient using du Cloux chains??
    w := PermToWord( L, p );
    w := [ inc[r] : r in w ];
    return  &*[ H | ReflectionPermutation( W, r ) : r in w ];
  end function;
  HtoL := function( q )
    p := [];
    for r in [1..n] do
      im := res[ inc[r]^q ];
      p[r] := im;  p[r+n] := (im le n) select im+n else im-n;
    end for;
    return L!p;
  end function;

  return L, hom< L -> H | x :-> LtoH(x), y :-> HtoL(y) >;
end intrinsic;

res := function( H, r )
  if assigned H`RootRestriction then
    return H`RootRestriction[r];
  else
    return r;
  end if;
end function;

inc := function( H, r )
  if assigned H`RootInclusion then
    return H`RootInclusion[r];
  else
    return r;
  end if;
end function;


// Note: this may not be efficient
intrinsic IsParabolic( W::GrpPermCox, H::GrpPermCox ) -> BoolElt
{True iff H is a parabolic subgroup of W}
  if not assigned H`RootInclusion then return false, _; end if;
  R := RootDatum( W );
  inc := H`RootInclusion;
  simples := Seqset( inc[[1..Rank(H)]] );
  if simples subset {1..Rank(R)} then  return true;  end if;
  for gens2 in Subsets({1..Rank(R)},Rank(H)) do
    if IsCoxeterIsomorphic( CoxeterMatrix(H),
    CoxeterMatrix(sub< R | gens2 >) ) and
    IsConjugate( W, H, ReflectionSubgroup(W,gens2) )
    then
      return true;
    end if;
  end for;
  return false;
end intrinsic;

intrinsic InternalExistsCoveringStructureGrpFPCox( W1::GrpFPCox, W2::GrpFPCox ) ->
  BoolElt
{Intrinsic for internal use only}

  return W1 eq W2;
end intrinsic;

intrinsic InternalCoveringStructureGrpFPCox( W1::GrpFPCox, W2::GrpFPCox ) ->
  BoolElt
{Intrinsic for internal use only}
  require W1 eq W2 :  "No covering structure";
  return W1 eq W2;
end intrinsic;

intrinsic InternalExistsCoveringStructureGrpPermCox( W1::GrpPermCox, W2::GrpPermCox ) ->
  BoolElt
{Intrinsic for internal use only}
  return Overgroup( W1 ) eq Overgroup( W2 );
end intrinsic;

intrinsic InternalCoveringStructureGrpPermCox( W1::GrpPermCox, W2::GrpPermCox ) ->
  BoolElt
{Intrinsic for internal use only}
  require Overgroup( W1 ) eq Overgroup( W2 ) :  "No covering structure";
  return Overgroup( W1 );
end intrinsic;


// ====================================================
//
// Reflection subgroups for GrpFPCox
//
// ====================================================

submat := func< M, Q | 
  Matrix( BaseRing(M), #Q, #Q, [ M[i,j] : j in Q, i in Q ] ) >;

intrinsic StandardParabolicSubgroup( W::GrpFPCox, simples::SetEnum[RngIntElt] ) 
  -> GrpFPCox
{The standard parabolic subgroup of W generated by the given simples}
  require simples subset {1..Rank(W)} : "Invalid simples";
  Q := Sort( Setseq( simples ) );
  H := CoxeterGroup( GrpFPCox, submat( CoxeterMatrix(W), Q ) );
  
  inj := hom< H -> W | h :-> bangNoCheck( W, [ Q[r] : r in Eltseq(h) ] ) >;
  return H, inj;
end intrinsic;


// ====================================================
//
// Operations on Coxeter group elements
//
// ====================================================

// -------------------------------------------------
//
// Coxeter length
//
intrinsic Length( w::GrpFPCoxElt ) -> RngIntElt
{The Coxeter length of w}
  return #w;
end intrinsic;

intrinsic CoxeterLength( w::GrpFPCoxElt ) -> RngIntElt
{The Coxeter length of w}
  return #w;
end intrinsic;

intrinsic Length( W::GrpPermCox, w::GrpPermElt ) -> RngIntElt
{The Coxeter length of w in W}
  require w in W : "element is not in the given Coxeter group";
  len := 0;
  N := NumPosRoots(W);
  posroots := (assigned W`RootInclusion) 
    select Seqset(W`RootInclusion[1..N]) else { 1..N };
  for r in posroots do
    if r^w notin posroots then len +:= 1; end if;
  end for;
  return len;
end intrinsic;

intrinsic CoxeterLength( W::GrpPermCox, w::GrpPermElt ) -> RngIntElt
{The Coxeter length of w in W}
  return Length( W, w );
end intrinsic;

intrinsic Length( w::GrpMatElt ) -> RngIntElt
{The Coxeter length of w}
  W := Parent( w );
  require IsRealReflectionGroup( W ) : 
    "Not an element of a real reflection group";
  G, h := CoxeterGroup( GrpFP, W );
  return #h(w);
end intrinsic;

intrinsic CoxeterLength( w::GrpMatElt ) -> RngIntElt
{The Coxeter length of w}
  W := Parent( w );
  require IsRealReflectionGroup( W ) : 
    "Not an element of a real reflection group";
  G, h := CoxeterGroup( GrpFP, W );
  return #h(w);
end intrinsic;


// -------------------------------------------------
//
// Longest element
//
// We store LongestElements for GrpFPCox because the creation of
// a GrpPermCox causes a memory leak.
intrinsic LongestElement( W::GrpFPCox ) -> GrpFPElt
{The longest element of W}
  require IsFinite( W ) : "The group must be finite";
  if not assigned W`LongestElement then
    pW := CoxeterGroup( GrpPermCox, W );
    w := W!1;  N := NumPosRoots( W );
    while exists(r){ r : r in [1..Rank(W)] | WordOnRoot( pW, r, Eltseq(w) ) le N } do
      w := W.r * w;
    end while;
    W`LongestElement := w;
  end if;
  return W`LongestElement;
end intrinsic;

intrinsic LongestElement( W::GrpPermCox ) -> GrpPermElt
{The longest element of W}
  w := W!1;  N := NumPosRoots( W );
  _, h := LocalCoxeterGroup( W );  h := Inverse( h );
  while exists(r){ r : r in [1..Rank(W)] | r^h(w) le N } do
    w := W.r * w;
  end while;
  return w;
end intrinsic;

intrinsic LongestElement( W::GrpMat ) -> GrpPermElt
{The longest element of W}
  require isRealReflGrp(W) : "Not a real reflection group";
  require IsFinite( W ): "The group must be finite";
  R := groupToRoot( W );
  wd := Eltseq( LongestElement( CoxeterGroup( GrpFPCox, R ) ) );
  return &*[W| W.i : i in wd ];
end intrinsic;



// -------------------------------------------------
//
// Coxeter element
//
intrinsic CoxeterElement( W::GrpFPCox ) -> GrpElt
{The Coxeter element of W}
  return &*[ W | W.i : i in [1..NumberOfGenerators(W)] ];
end intrinsic;

intrinsic CoxeterElement( W::GrpPermCox ) -> GrpElt
{The Coxeter element of W}
  return &*[ W | W.i : i in [1..NumberOfGenerators(W)] ];
end intrinsic;

intrinsic CoxeterElement( W::GrpMat ) -> GrpElt
{The Coxeter element of W}
  require isRealReflGrp(W) : "Not a real reflection group";
  return &*[ W | W.i : i in [1..NumberOfGenerators(W)] ];
end intrinsic;


// -------------------------------------------------
//
// Coxeter number
//
intrinsic CoxeterNumber( W::GrpFPCox ) -> RngIntElt
{The Coxeter number of W}
  R := groupToRootDatum( W );
  require Category( R ) ne BoolElt : "The group must be finite";
  require IsIrreducible( R ) : "Not an irreducible group";
  return ( 2*NumPosRoots(R) ) div Rank(R);
end intrinsic;

intrinsic CoxeterNumber( W::GrpPermCox ) -> RngIntElt
{The Coxeter number of W}
  require IsIrreducible( W ) : "Not an irreducible group";
  return ( 2*NumPosRoots(W) ) div Rank(W);
end intrinsic;

intrinsic CoxeterNumber( W::GrpMat ) -> RngIntElt
{The Coxeter number of W}
  require isRealReflGrp(W) : "Not a real reflection group";
  require IsFinite( W ) : "The group must be finite";
  R := groupToRootDatum( W );
  require IsIrreducible( R ) : "Not an irreducible group";
  return ( 2*NumPosRoots(R) ) div Rank(R);
end intrinsic;


// -------------------------------------------------
//
// Descent sets
//
intrinsic LeftDescentSet( W::GrpPermCox, w::GrpPermElt ) -> {}
{The set of indices r such that the length of s_r*w is
less than that of w}
  return { r : r in [1..Rank(W)] | r^w gt NumPosRoots(W) };
end intrinsic;

intrinsic RightDescentSet( W::GrpPermCox, w::GrpPermElt ) -> {}
{The set of indices r such that the length of w*s_r is
less than that of w}
  return LeftDescentSet( W, w^-1 );
end intrinsic;

isPos := function( v )
  if exists(i){ i : i in [1..OverDimension(v)] | v[i] ne 0 } then
    return v[i] gt 0;
  else
    return false;
  end if;
end function;

intrinsic LeftDescentSet( W::GrpMat, w::GrpMatElt ) -> {}
{The set of indices r such that the length of s_r*w is
less than that of w}
  require isRealReflGrp(W) : "Not a real reflection group";
  V := RSpace( W );
  return { i : i in [1..Dimension(V)] | not isPos( V.i*w ) };
end intrinsic;

intrinsic RightDescentSet( W::GrpMat, w::GrpMatElt ) -> {}
{The set of indices r such that the length of w*s_r is
less than that of w}
  return LeftDescentSet( W, w^-1 );
end intrinsic;


// -------------------------------------------------
//
// Additive order
//
additiveOrder := function( W, w )
  n := #w;
  if n eq 0 then  return [];  end if; 
  refs := SimpleReflectionPermutations( RootSystem(W) ); 
  P := [ w[n] ];
  for i in [n-1..1 by -1] do
    r := w[i];
    for s in w[ [i+1..n] ] do
      r ^:= refs[s];
    end for;
    Append( ~P, r );
  end for;
  return P;
end function;

intrinsic AdditiveOrder( W::GrpPermCox ) -> SeqEnum
{An additive order of the roots of W}
  w := PermToWord( W, LongestElement( W ) ); 
  return additiveOrder( W, w );
end intrinsic;



// ====================================================
//
// Standard action
//
// ====================================================

intrinsic StandardActionGroup( W::GrpPermCox ) -> GrpPerm, Map
{The group of the standard action of W}
  if not assigned W`StandardGroupHom then
    R := RootDatum( W );
    if NumPosRoots( R ) ne 0 then
      if not (IsCrystallographic( R ) and IsAdjoint( R )) then
        R := rootDatumByIsogeny( CartanMatrix(W), groupToType(W), "Ad", ExtraspecialSigns(R) );
      end if;
      over, incl, X := standardRootSystemInj( R );
      gens := [ &*[ReflectionPermutation( over, r ):r in incl[i]] : 
        i in [1..Rank(W)] ];
      S := Sym( #X );
      gens := [ S | [ Position(X,i^g) : i in X ] : g in gens ];
      G := sub< S | gens >;
      W`StandardGroupHom := hom< W -> G | w :-> &*[ G | G.i : i in PermToWord( W, w ) ] >;
    else
      W`StandardGroupHom := IdentityHomomorphism( W );
    end if;
  end if;
  h := W`StandardGroupHom;
  return Codomain( h ), h;
end intrinsic;

intrinsic StandardActionGroup( W::GrpFPCox ) -> GrpPerm, Map
{The group of the standard action of W}
  S := StandardActionGroup( CoxeterGroup( GrpPermCox, W ) );
  h := func< x | &*[S|  S.i : i in Eltseq( x ) ] >;
  return S, hom< W -> S | x :-> h(x) >;
end intrinsic;

intrinsic StandardActionGroup( W::GrpMat ) -> GrpPerm, Map
{The group of the standard action of W}
  require isRealReflGrp(W) : "The group must be a reflection group";
  G, h1 := CoxeterGroup( GrpPermCox, W );
  S, h2 := StandardActionGroup( G );
  h := func< x | &*[S| S.i : i in Eltseq( x ) ] >;
  return S, h1*h2;
end intrinsic;

intrinsic StandardAction( W::GrpPermCox ) -> Map, GrpPerm, {@ @}
{The standard action of W}
  G, h := StandardActionGroup( W );
  X := [1..Degree(G)];
  return map< car<X,G> -> X | x :-> x[1]^h(x[2]) >;
end intrinsic;

intrinsic StandardAction( W::GrpFPCox ) -> Map, GrpPerm, {@ @}
{The standard action of W}
  G, h := StandardActionGroup( W );
  X := [1..Degree(G)];
  return map< car<X,G> -> X | x :-> x[1]^h(x[2]) >;
end intrinsic;

intrinsic StandardAction( W::GrpMat ) -> Map, GrpPerm, {@ @}
{The standard action of W}
  G, h := StandardActionGroup( W );
  X := [1..Degree(G)];
  return map< car<X,G> -> X | x :-> x[1]^h(x[2]) >;
end intrinsic;



// ====================================================
//
// Transversals
//
// ====================================================

intrinsic TransversalElt( W::GrpPermCox, H::GrpPermCox, x::GrpPermElt ) -> GrpPermElt
{The transversal element in the coset H x}
  rank := Rank(H);  N := NumPosRoots( Overdatum(W) );
  while exists(i){ i : i in [1..rank] | inc(H,i)^x gt N } do
    x := H.i * x;
  end while;
  return x;
end intrinsic;

intrinsic InternalReflSubgrpToPositive(W::Any, J::{RngIntElt}) -> SetEnum
{Get simple system of positive roots for subgroup of W generated by roots in J. 
(W should be some Coxeter group)}
/* Please note: this intrinsic is called from C -- so be careful changing it! */
	_, incl := sub< RootDatum(W) | J >;
	return Seqset( incl[[1..#J]] );
end intrinsic;	

intrinsic Transversal( W::GrpPermCox, H::GrpPermCox ) -> {@ @}
{The indexed set of coset representatives of shortest length of H in W}
  current := {@ W!1 @};  N := NumPosRoots(W);  n := Rank(W);
  T := current;
  simpleH := {inc(H,r) : r in [1..Rank(H)]};
  assert simpleH subset {1..N};

  repeat
    previous := current;
    T join:= current;
    current := {@ W | @};
    for u in previous do
      v := u^-1;
      for i := 1 to n do
        j := i^v;
        if j le N and j notin simpleH then
          Include( ~current, u*(W.i) );
        end if;
      end for;
    end for;
  until IsEmpty(current);
  return T;
end intrinsic;

intrinsic Transversal( W::GrpFPCox, J::{RngIntElt}, L::RngIntElt ) -> {@ @}
{Minimal length right coset representatives for the reflection subgroup of W 
 generated by reflections indexed by J. Length of representatives is limited by L}
  return (J subset {1..Rank(W)}) select TransversalParabolic(W, J, L) 
                                 else TransversalNonParabolic(W, J, L);
end intrinsic;

intrinsic Transversal( W::GrpFPCox, J::{RngIntElt} ) -> {@ @}
{Minimal length right coset representatives for the reflection subgroup of W 
 generated by reflections indexed by J}
  return (J subset {1..Rank(W)}) select TransversalParabolic(W, J) 
                                 else TransversalNonParabolic(W, J);
end intrinsic;

intrinsic TransversalWords( W::GrpPermCox, H::GrpPermCox ) -> {@ @}
{The indexed set of coset representatives (as elements of the finitely
 presented Coxeter group) of shortest length of H in W}
	assert IsReflectionSubgroup(W, H);

	Wfp, phi := CoxeterGroup(GrpFPCox, W);

	if assigned H`RootInclusion then
		simpleH := Seqset( (H`RootInclusion)[1..Rank(H)] );
		return Transversal(Wfp, simpleH);
	else
		//Slow: Have to use the permutation code and convert to words afterwards.
		tr := Transversal(W, H);
		return {@ phi(t) : t in tr @};
	end if;

end intrinsic;

// ====================================================
//
// Element conversion functions
//
// ====================================================

function w2p( W, w : Local := false ) 
  O := (Local) select W else Overgroup( W );
  N := NumPosRoots( O );
  ref := SimpleReflectionPermutations( O : Local );
  perm := [];
  for r in [1..N] do
    im := r;
    for s in w do
      im ^:= ref[s];
    end for;
    perm[r] := im;  perm[r+N] := (im le N) select im+N else im-N;
  end for;
  return (#perm eq 0) select W!1 else W!perm;
end function;

intrinsic WordToPerm( W::GrpPermCox, w::SeqEnum : Local := false ) -> GrpPermElt
{Converts a word w to a permutation of the roots of W}
// cpu := Cputime();
//   old := w2p(W,w:Local:=Local);
// old_time := Cputime()-cpu;
//   
// cpu := Cputime();

  O := (Local) select W else Overgroup( W );
  
  // these are local for O, so must be  O.i  (???)
  // but it doesn't seem to slow down the process mucn, so leave as it is.
  ref := SimpleReflectionPermutations( O : Local );

  perm := W!(&*[O| ref[s] : s in w ]);

// new_time := Cputime()-cpu;
// 
//   assert perm eq old;
// 
// if new_time ne old_time then "Time diff:", old_time, new_time-old_time, new_time; end if;
// 

  return perm;
end intrinsic;

intrinsic WordToPerm( W::GrpPermCox, w::GrpFPElt : Local := false ) -> GrpPermElt
{Converts a word w to a permutation of the roots of W}
  return WordToPerm( W, Eltseq(w) : Local := Local );
end intrinsic;

convertBasis := function( M, O, Basis : co := false )
  case Basis:
  when "Root":
    return M;
  when "Standard":
    B := (co) select SimpleCoroots(O) else SimpleRoots(O);
    B := ChangeRing( B, FieldOfFractions(BaseRing(B)) );
    return MatrixAlgebra( BaseRing(M), Ncols(B) )! (B^(-1) * M * B);
  when "Weight":
    B := CartanMatrix(O);
    if co then B := Transpose(B); end if;
    B := ChangeRing( B, FieldOfFractions(BaseRing(B)) );
    return B^(-1) * M * B;
  else
    error "Invalid Basis parameter";
  end case;
end function;

intrinsic WordToMatrix( W::GrpPermCox, w::SeqEnum : Local := false, Basis := "Standard" ) -> Mtrx
{Converts a word w to a matrix acting on the root space of W}
  O := (Local) select W else Overgroup( W );
  ref := SimpleReflectionMatrices( O : Basis:=Basis );
  M := Universe(ref)!1;
  for r in w do
    M *:= ref[r];
  end for;
  return M;
end intrinsic;

intrinsic WordToMatrix( W::GrpPermCox, w::GrpFPElt : Local := false, Basis := "Standard" ) -> Mtrx
{Converts a word w to a matrix acting on the root space of W}
  return WordToMatrix( W, Eltseq(w) : Local := Local, Basis := Basis );
end intrinsic;

intrinsic WordToDualMatrix( W::GrpPermCox, w::SeqEnum : Local := false, Basis := "Standard" ) -> Mtrx
{Converts a word w to a matrix acting on the coroot space of W}
  O := (Local) select W else Overgroup( W );
  ref := SimpleCoreflectionMatrices( O : Basis:=Basis );
  M := Universe(ref)!1;
  for r in w do
    M *:= ref[r];
  end for;
  return M;
end intrinsic;

intrinsic WordToDualMatrix( W::GrpPermCox, w::GrpFPElt : Local := false, Basis := "Standard" ) -> Mtrx
{Converts a word w to a matrix acting on the coroot space of W}
  return WordToDualMatrix( W, Eltseq(w) : Local := Local, Basis := Basis );
end intrinsic;

intrinsic PermToWord( W::GrpPermCox, p::GrpPermElt : Local := false, Group := false ) -> SeqEnum
{Converts a permutation p in W to a word}
  O := (Local) select W else Overgroup( W );
  ref := SimpleReflectionPermutations( O : Local );
  N := NumPosRoots(O);  rank := Rank(O);
  id := Id(W);
  w := [];
  while p ne id do
    r := rep{ r : r in [1..rank] | r^p gt N };
    Append( ~w, r );
    p := ref[r] * p;
  end while;
  return (Group) select Presentation(O)!w else w;
end intrinsic;

intrinsic MatrixToWord( W::GrpPermCox, M::Mtrx : Local := false, Basis := "Standard", Group := false ) -> SeqEnum
{Converts a matrix M acting on the root space of W to a word}
  O := (Local) select W else Overgroup(W);
  roots := Roots( O : Basis := Basis );
  ref := SimpleReflectionMatrices( O : Basis := Basis );
  N := NumPosRoots(O);  rank := Rank(O);
  id := Identity(Parent(M));
  w := [];
  while M ne id do
    r := rep{ r : r in [1..rank] | RootPosition( O, roots[r]*M : Basis:=Basis ) gt N };
    Append( ~w, r );
    M := ref[r] * M;
  end while;
  return (Group) select Presentation(O)!w else w;
end intrinsic;

intrinsic DualMatrixToWord( W::GrpPermCox, M::Mtrx : Local := false, Basis := "Standard", Group := false ) -> SeqEnum
{Converts a matrix M acting on the coroot space of W to a word}
  O := (Local) select W else Overgroup(W);
  roots := Coroots( O : Basis := Basis );
  ref := SimpleCoreflectionMatrices( O : Basis := Basis );
  N := NumPosRoots(O);  rank := Rank(O);
  id := Identity(Parent(M));
  w := [];
  while M ne id do
    r := rep{ r : r in [1..rank] | CorootPosition( O, roots[r]*M : Basis:=Basis ) gt N };
    Append( ~w, r );
    M := ref[r] * M;
  end while;
  return (Group) select Presentation(O)!w else w;
end intrinsic;

intrinsic MatrixToPerm( W::GrpPermCox, M::Mtrx : Local := false, Basis := "Standard" ) -> GrpPermElt
{Converts a matrix M acting on the root space of W to a permutation on the roots}
  O := (Local) select W else Overgroup(W);
  roots := Roots( O : Basis := Basis );
  N := NumPosRoots( O );
  perm := [];
  for r in [1..N] do
    s := RootPosition( W, roots[r]*M : Basis:=Basis );
    perm[r] := s;
    perm[r+N] := (s le N) select s+N else s-N;
  end for;
  return (#perm eq 0) select O!1 else O!perm;
end intrinsic;

intrinsic DualMatrixToPerm( W::GrpPermCox, M::Mtrx : Local := false, Basis := "Standard" ) -> GrpPermElt
{Converts a matrix M acting on the coroot space of W to a permutation on the roots}
  O := (Local) select W else Overgroup(W);
  roots := Coroots( O : Basis := Basis );
  N := NumPosRoots( O );
  perm := [];
  for r in [1..N] do
    s := CorootPosition( W, roots[r]*M : Basis:=Basis );
    perm[r] := s;
    perm[r+N] := (s le N) select s+N else s-N;
  end for;
  return (#perm eq 0) select O!1 else O!perm;
end intrinsic;

intrinsic PermToMatrix( W::GrpPermCox, p::GrpPermElt : Local := false, Basis := "Standard" ) -> Mtrx
{Converts a permutation of the roots of W to a matrix acting on the root space}
  O := (Local) select W else Overgroup(W);
  if not IsSemisimple( RootDatum( O ) ) then
    return WordToMatrix( O, PermToWord( O, p :Local ) : Local, Basis:=Basis );
  end if;
  roots := Roots( O : Basis := "Root" );
  M := Matrix( [ roots[r^p] : r in [1..Rank(O)] ] );
  return convertBasis( M, O, Basis );
end intrinsic;

intrinsic PermToDualMatrix( W::GrpPermCox, p::GrpPermElt : Local := false, Basis := "Standard" ) -> Mtrx
{Converts a permutation of the roots of W to a matrix acting on the root space}
  O := (Local) select W else Overgroup(W);
  if not IsSemisimple( RootDatum( O ) ) then
    return WordToDualMatrix( O, PermToWord( O, p :Local ) : Local, Basis:=Basis );
  end if;
  roots := Coroots( O : Basis := "Root" );
  M := Matrix( [ roots[r^p] : r in [1..Rank(O)] ] );
  return convertBasis( M, O, Basis : co );
end intrinsic;

intrinsic WordOnRoot( W::GrpPermCox, r::RngIntElt, w : Local := false ) -> RngIntElt
{The action of the word w on the rth root of W}
  O := (Local) select W else Overgroup(W);
  w := Eltseq( w );
  refs := SimpleReflectionPermutations( O : Local );
  for s in w do
    r ^:= refs[s];
  end for;
  return r;
end intrinsic;


intrinsic WordOnRootSpace( W::GrpPermCox, v, w : Local := false, Basis := "Standard" ) -> .
{The action of the word w on v in the root space of W}
  O := (Local) select W else Overgroup(W);
  w := Eltseq( w );
  v := RootSpace( O ) ! v;
  refs := SimpleReflectionMatrices( O );
  for r in w do
    v *:= refs[r];
  end for;
  return v;
end intrinsic;

intrinsic WordOnCorootSpace( W::GrpPermCox, v, w : Local := false, Basis := "Standard" ) -> .
{The action of the word w on v in the root space of W}
  O := (Local) select W else Overgroup(W);
  w := Eltseq( w );
  v := CorootSpace( O ) ! v;
  refs := SimpleCoreflectionMatrices( O );
  for r in w do
    v *:= refs[r];
  end for;
  return v;
end intrinsic;

// --------------------- eof --------------------------


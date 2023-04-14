freeze;

/*
  $Id: declarations.m 65590 2022-03-18 05:16:36Z don $

  Don Taylor

  17 March 2022

  Verbosity and attribute declarations for the three types of Coxeter groups
    GrpFPCox
    GrpPermCox
    GrpMat

  These declarations were extracted from the files:

  LieThry/GrpCox/Conj.m
  LieThry/GrpCox/GrpCox.m
  LieThry/GrpLie/GrpLie.m

*/

declare verbose VerboseGrpCox,  6; // verbosity levels up to 5; debug from 6 on

declare attributes GrpFPCox :
  CoxeterMatrix, // assigned at creation
  CoxeterGraph,
//  ReflectionTable, // declared in the C kernel
//  minimal roots and actions for computing multiplication
  BraidGroup,
  BraidGroupHom,
  LongestElement,
  Overgroup,

  Classes,
  ClassParameters;

declare attributes GrpPermCox:
  // required
  RootSystem,
  RootDatum,

  CoxeterMatrix,
  CartanMatrix,
  CoxeterGraph,
  // reflection subgroups
  Overgroup,
  RootInclusion,
  RootRestriction,
  IsParabolic,
  
  // Associated groups
  FPGroupHom,
  ReflectionGroupHom,
  StandardGroupHom,

  // Conjugacy classes
  ClassParameters,

  // Used in GrpLie/GrpLie.m
  ReflectionTorusElements;

declare attributes GrpMat:
  // required
  IsReflectionGroup,
  SimpleRoots,
  SimpleCoroots,
  
  // optional
  CartanMatrix,
  RootSystem,
  RootDatum,
  CoxeterMatrix,
  CoxeterGraph,
  DynkinDigraph,

  // reflection subgroups
  Overgroup,
  RootInclusion,
  RootRestriction,
  IsParabolic,

  // Pseudoreflection groups
  IsPseudoreflectionGroup,
  PseudoreflectionOrders;
 



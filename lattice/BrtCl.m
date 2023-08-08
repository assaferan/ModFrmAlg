// freeze

import "clifford.m" : get_genus_orders;

declare type BrtCl[BrtClElt];

declare attributes BrtCl:
		   Elements,
	IsomClasses,
	Names;

declare attributes BrtClElt:
		   Orders,
	Parent;

intrinsic BrandtGroupoid(orders::SeqEnum[SeqEnum[AlgQuatOrd]]) -> BrtCl
{}
  B := New(BrtCl);
  B`Elements := [];
  B`IsomClasses := [];
  B`Names := [];
  for O in orders do
      B_elt := New(BrtClElt);
      B_elt`Orders := O;
      B_elt`Parent := B;
      Append(~B`Elements, B_elt);
      names := [];
      for i in [1..#O] do
	  is_new := true;
	  for j in [1..#B`IsomClasses] do
	      if IsIsomorphic(O[i], B`IsomClasses[j]) then
		  Append(~names, Sprintf("O%o", j));
		  is_new := false;
		  break;
	      end if;
	  end for;
	  if is_new then
	      Append(~B`IsomClasses, O[i]);
	      Append(~names, Sprintf("O%o", #B`IsomClasses));
	  end if;
      end for;
      Append(~B`Names, Join(names, " x "));
  end for;
  return B;
end intrinsic;

intrinsic BrandtGroupoid(M::ModFrmAlg) -> BrtCl
{}
// genus := [GramMatrix(ZLattice(lat)) : lat in Representatives(Genus(M))];
  genus := Representatives(Genus(M));
  orders := get_genus_orders(genus);
  return BrandtGroupoid(orders);
end intrinsic;

intrinsic 'eq'(B1::BrtCl, B2::BrtCl) -> BoolElt
{}
  return B1`Elements eq B2`Elements;
end intrinsic;

intrinsic Print(B::BrtCl, level::MonStgElt)
{}
  if level eq "magma" then
      error "Not Implemented!";
  end if;
  printf "[ %o ]", Join(B`Names, ", ");
  return;
end intrinsic;

intrinsic 'eq'(B1::BrtClElt, B2::BrtClElt) -> BoolElt
{}
  return B1`Orders eq B2`Orders;
end intrinsic;

intrinsic IsCoercible(S::BrtCl, x::.) -> BoolElt, .
{}
  if Type(x) ne BrtClElt then return false; end if;
  if Parent(x) ne S then return false; end if;
  return true, x;
end intrinsic;
    
intrinsic Parent(B::BrtClElt) -> BrtCl
{}
  return B`Parent;
end intrinsic;

intrinsic Print(B::BrtClElt, level::MonStgElt)
{}
  if level eq "magma" then
      error "Not Implemented!";
  end if;
  printf "%o", B`Orders;
end intrinsic;

  

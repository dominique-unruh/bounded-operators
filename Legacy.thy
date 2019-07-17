(* 

This theory contains the things that are still needed for qrhl-tool but should be removed eventually from here.

*)

theory Legacy
imports Bounded_Operators Complex_L2
begin

type_synonym ('a,'b) l2bounded = "('a ell2, 'b ell2) bounded"
abbreviation "applyOp == Rep_bounded"

end

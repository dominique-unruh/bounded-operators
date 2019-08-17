(* 

This theory contains the things that are still needed for qrhl-tool but should be removed eventually from here.

*)

theory Legacy
imports Bounded_Operators Complex_L2 "HOL-Library.Adhoc_Overloading" Tensor_Product ToDo
begin

type_synonym ('a,'b) l2bounded = "('a ell2, 'b ell2) bounded"
abbreviation "applyOp == times_bounded_vec"

unbundle bounded_notation

consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhoc_overloading
  cdot timesOp applyOp applyOpSpace

end

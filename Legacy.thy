(* 

This theory contains the things that are still needed for qrhl-tool but should be removed eventually from here.

*)

theory Legacy
imports Bounded_Operators
begin

(* TODO: move to Legacy *)
type_synonym ('a,'b) l2bounded = "('a ell2, 'b ell2) bounded"
abbreviation "applyOp == Rep_bounded"
  (* typedef ('a,'b) l2bounded = "{A::'a ell2\<Rightarrow>'b ell2. bounded_clinear A}"
  morphisms applyOp Abs_l2bounded
  using bounded_clinear_zero by blast
setup_lifting type_definition_l2bounded *)


end

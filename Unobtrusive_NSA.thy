theory Unobtrusive_NSA
  imports "HOL-Nonstandard_Analysis.Nonstandard_Analysis"
begin

text \<open>
Load this theory instead of \<^theory>\<open>HOL-Nonstandard_Analysis.Nonstandard_Analysis\<close>. 
This will not include the syntax from \<^theory>\<open>HOL-Nonstandard_Analysis.Nonstandard_Analysis\<close>
(which is somewhat intrusive because it overwrites, e.g., the letters \<epsilon> and \<omega>).

Reactivate the notation locally via "includes nsa_notation" in a lemma statement.
(Or sandwich a declaration using that notation between "unbundle nsa_notation ... unbundle no_nsa_notation".)
\<close>

(* TODO: restore Transfer.transfer method via short name *)

(* TODO: add any syntax introduced by HOL-Nonstandard_Analysis both here and in the bundle below *)
bundle no_nsa_notation begin
no_notation epsilon ("\<epsilon>")
end

bundle nsa_notation begin
notation epsilon ("\<epsilon>")
end

unbundle no_nsa_notation

end

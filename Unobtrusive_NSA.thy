section \<open>\<open>Unobtrusive_NSA\<close> -- Cleaning up syntax from \<open>Nonstandard_Analysis\<close>\<close>

theory Unobtrusive_NSA
  imports "HOL-Nonstandard_Analysis.Nonstandard_Analysis" Extended_Sorry
begin

text \<open>
Load this theory instead of \<^theory>\<open>HOL-Nonstandard_Analysis.Nonstandard_Analysis\<close>. 
This will not include the syntax from \<^theory>\<open>HOL-Nonstandard_Analysis.Nonstandard_Analysis\<close>
(which is somewhat intrusive because it overwrites, e.g., the letters \<open>\<epsilon>\<close> and \<open>\<omega>\<close>).

Reactivate the notation locally via "@{theory_text \<open>includes nsa_notation\<close>}" in a lemma statement.
(Or sandwich a declaration using that notation between "@{theory_text \<open>unbundle nsa_notation ... unbundle no_nsa_notation\<close>}.)
\<close>

(* TODO: add any syntax introduced by HOL-Nonstandard_Analysis both here and in the bundle below *)
bundle no_nsa_notation begin
no_notation HyperDef.epsilon ("\<epsilon>")
no_notation HyperDef.omega ("\<omega>")
no_notation NSA.approx (infixl "\<approx>" 50)
end

bundle nsa_notation begin
notation HyperDef.epsilon ("\<epsilon>")
notation HyperDef.omega ("\<omega>")
notation NSA.approx (infixl "\<approx>" 50)
end

unbundle no_nsa_notation

text \<open>The following restores the method transfer under the name transfer.
      Use @{method StarDef.transfer} for the transfer method for nonstandard analysis.\<close>
method_setup transfer = \<open>
  let val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
        error ("Bad free variable: " ^ Syntax.string_of_term ctxt t))
      val fixing = Scan.optional (Scan.lift (Args.$$$ "fixing" -- Args.colon)
        |-- Scan.repeat free) []
      fun transfer_method equiv : (Proof.context -> Proof.method) context_parser =
        fixing >> (fn vs => fn ctxt =>
          SIMPLE_METHOD' (Transfer.gen_frees_tac vs ctxt THEN' Transfer.transfer_tac equiv ctxt))
  in
    transfer_method true
  end\<close>

end

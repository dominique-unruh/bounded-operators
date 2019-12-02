section \<open>\<open>Unobtrusive_NSA\<close> -- Cleaning up syntax from \<open>Nonstandard_Analysis\<close>\<close>

theory Unobtrusive_NSA
  imports "HOL-Nonstandard_Analysis.Nonstandard_Analysis"
begin

text \<open>
Load this theory instead of \<^theory>\<open>HOL-Nonstandard_Analysis.Nonstandard_Analysis\<close>. 
This will not include the syntax from \<^theory>\<open>HOL-Nonstandard_Analysis.Nonstandard_Analysis\<close>
(which is somewhat intrusive because it overwrites, e.g., the letters \<open>\<epsilon>\<close> and \<open>\<omega>\<close>).

Reactivate the notation locally via "@{theory_text \<open>includes nsa_notation\<close>}" in a lemma statement.
(Or sandwich a declaration using that notation between "@{theory_text \<open>unbundle nsa_notation ... unbundle no_nsa_notation\<close>}.)
\<close>

bundle no_nsa_notation begin
no_notation HyperDef.epsilon ("\<epsilon>")
no_notation HyperDef.omega ("\<omega>")
no_notation NSA.approx (infixl "\<approx>" 50)
no_notation HyperDef.pow (infixr "pow" 80)
no_notation HLim.NSLIM ("((_)/ \<midarrow>(_)/\<rightarrow>\<^sub>N\<^sub>S (_))" [60, 0, 60] 60)
no_notation HLog.powhr (infixr "powhr" 80)
no_notation HSEQ.NSLIMSEQ ("((_)/ \<longlonglongrightarrow>\<^sub>N\<^sub>S (_))" [60, 60] 60)
no_notation HSeries.NSsums (infixr "NSsums" 80)
no_notation Star.starfun_n ("*fn* _" [80] 80)
no_notation StarDef.FreeUltrafilterNat (\<open>\<U>\<close>)
no_notation StarDef.Ifun (\<open>(_ \<star>/ _)\<close> [300, 301] 300)
no_notation StarDef.starfun (\<open>*f* _\<close> [80] 80)
no_notation StarDef.starfun2 (\<open>*f2* _\<close> [80] 80)
no_notation StarDef.starP (\<open>*p* _\<close> [80] 80)
no_notation StarDef.starP2 (\<open>*p2* _\<close> [80] 80)
no_notation StarDef.starset (\<open>*s* _\<close> [80] 80)
end

bundle nsa_notation begin
notation HyperDef.epsilon ("\<epsilon>")
notation HyperDef.omega ("\<omega>")
notation NSA.approx (infixl "\<approx>" 50)
notation HyperDef.pow (infixr "pow" 80)
notation HLim.NSLIM ("((_)/ \<midarrow>(_)/\<rightarrow>\<^sub>N\<^sub>S (_))" [60, 0, 60] 60)
notation HLog.powhr (infixr "powhr" 80)
notation HSEQ.NSLIMSEQ ("((_)/ \<longlonglongrightarrow>\<^sub>N\<^sub>S (_))" [60, 60] 60)
notation HSeries.NSsums (infixr "NSsums" 80)
notation Star.starfun_n ("*fn* _" [80] 80)
notation StarDef.FreeUltrafilterNat (\<open>\<U>\<close>)
notation StarDef.Ifun (\<open>(_ \<star>/ _)\<close> [300, 301] 300)
notation StarDef.starfun (\<open>*f* _\<close> [80] 80)
notation StarDef.starfun2 (\<open>*f2* _\<close> [80] 80)
notation StarDef.starP (\<open>*p* _\<close> [80] 80)
notation StarDef.starP2 (\<open>*p2* _\<close> [80] 80)
notation StarDef.starset (\<open>*s* _\<close> [80] 80)
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

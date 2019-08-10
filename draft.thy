    proof-
      have \<open>(case inv_option \<pi> j of None \<Rightarrow> 0
     | Some i \<Rightarrow> (\<lambda>y. if x = y then 1 else 0) i) = 0\<close>
        for j
      proof(induction \<open>inv_option \<pi> j\<close>)
        case None
        thus ?case
          by simp 
      next
        case (Some y)
        hence \<open>\<pi> y = Some j\<close>
          unfolding inv_option_def inv_def
          apply auto
          by (metis Some.hyps f_inv_into_f inv_option_def option.discI option.sel)
        hence \<open>x \<noteq> y\<close>
          using \<open>inj_option \<pi>\<close> None.hyps by auto
        thus ?case
          by (metis (mono_tags, lifting) Some.hyps option.simps(5)) 
      qed
      hence \<open>(case inv_option \<pi> j of None \<Rightarrow> 0
     | Some i \<Rightarrow> Rep_ell2 ((Abs_ell2  (\<lambda>y. if x = y then 1 else 0) )) i) = 0\<close>
        for j
      proof-
        have \<open>has_ell2_norm (\<lambda>y. if x = y then 1 else 0)\<close>
        proof-
          have \<open>Rep_ell2 (ket x) = (\<lambda>y. if x = y then 1 else 0)\<close>
            apply transfer by blast
          moreover have \<open>has_ell2_norm (Rep_ell2 (ket x))\<close>
            using Rep_ell2
            by auto
          ultimately show ?thesis by simp
        qed
        thus ?thesis 
          using Abs_ell2_inverse
          by (metis \<open>\<And>j. (case inv_option \<pi> j of None \<Rightarrow> 0 | Some i \<Rightarrow> if x = i then 1 else 0) = 0\<close> mem_Collect_eq)          
      qed
      hence \<open> (case inv_option \<pi> j of None \<Rightarrow> 0
     | Some i \<Rightarrow> Rep_ell2 ((Abs_ell2 \<circ> (\<lambda>x y. if x = y then 1 else 0) \<circ> (\<lambda>x. x)) x) i) = 0\<close>
        for j
        by (metis comp_apply)        
      hence \<open>(\<lambda> b. case inv_option \<pi> b 
              of None \<Rightarrow> 0 | Some i \<Rightarrow> (Rep_ell2 (ket x)) i) j = 0\<close>
        for j
        unfolding ket_def map_fun_def id_def
        by blast        
      hence \<open>Rep_ell2 ( Abs_ell2 (\<lambda> b. case inv_option \<pi> b 
              of None \<Rightarrow> 0 | Some i \<Rightarrow> (Rep_ell2 (ket x)) i) ) j = 0\<close>
        for j
        by (metis Rep_ell2 Rep_ell2_inverse classical_operator'.abs_eq classical_operator'.rep_eq eq_onp_def mem_Collect_eq)
      moreover have \<open>(*\<^sub>v)  (Abs_bounded (\<lambda>\<phi>. Abs_ell2 (\<lambda> b. case inv_option \<pi> b 
              of None \<Rightarrow> 0 | Some i \<Rightarrow> (Rep_ell2 \<phi>) i))) = 
              (\<lambda>\<phi>. Abs_ell2 (\<lambda> b. case inv_option \<pi> b 
              of None \<Rightarrow> 0 | Some i \<Rightarrow> (Rep_ell2 \<phi>) i))\<close>
      proof-
        have \<open>bounded_clinear (\<lambda>\<phi>. Abs_ell2 (\<lambda> b. case inv_option \<pi> b 
              of None \<Rightarrow> 0 | Some i \<Rightarrow> (Rep_ell2 \<phi>) i))\<close>
          using bounded_clinear_Abs_ell2_option by blast
        thus ?thesis
          using Abs_bounded_inverse
          by blast
      qed        
      ultimately have \<open>Rep_ell2 (Abs_bounded (\<lambda>\<phi>. Abs_ell2 (\<lambda> b. case inv_option \<pi> b 
              of None \<Rightarrow> 0 | Some i \<Rightarrow> (Rep_ell2 \<phi>) i)) *\<^sub>v ket x) j = 0\<close>
        for j
        by auto
      moreover have \<open>Abs_ell2 \<circ> (\<lambda>\<psi> b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some i \<Rightarrow> \<psi> i) \<circ>
      Rep_ell2 = (\<lambda>\<phi>. Abs_ell2 (\<lambda> b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some i \<Rightarrow> (Rep_ell2 \<phi>) i))\<close>
      proof-
        have \<open>(\<lambda>\<psi> b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some i \<Rightarrow> \<psi> i) \<circ>
      Rep_ell2 = (\<lambda>\<phi> b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some i \<Rightarrow> (Rep_ell2 \<phi>) i)\<close>
          by auto
        thus ?thesis
          by auto
      qed
      ultimately have \<open>Rep_ell2 (Abs_bounded (Abs_ell2 \<circ>
      (\<lambda>\<psi> b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some i \<Rightarrow> \<psi> i) \<circ>
      Rep_ell2) *\<^sub>v ket x) j = 0\<close>
        for j
        by simp
      hence \<open>Rep_ell2 (Abs_bounded (Abs_ell2 \<circ>
      (\<lambda>\<psi> b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some i \<Rightarrow> \<psi> i) \<circ>
      Rep_ell2) *\<^sub>v ket x) = (\<lambda> _. 0)\<close>
        by blast
      moreover have \<open>Rep_ell2 (0::'b ell2) = (\<lambda> _. 0)\<close>
        by (metis cr_ell2_def ell2.pcr_cr_eq zero_ell2.transfer)
      ultimately have \<open>Rep_ell2 (Abs_bounded (Abs_ell2 \<circ>
      (\<lambda>\<psi> b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some i \<Rightarrow> \<psi> i) \<circ>
      Rep_ell2) *\<^sub>v ket x) = Rep_ell2 0\<close>
        by auto
      hence \<open>Abs_bounded (Abs_ell2 \<circ>
      (\<lambda>\<psi> b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some i \<Rightarrow> \<psi> i) \<circ> Rep_ell2) *\<^sub>v ket x = 0\<close>
        using Rep_ell2_inject
        by blast        
      thus ?thesis 
        unfolding map_fun_def classical_operator_def classical_operator'_def
        by auto
    qed

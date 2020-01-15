section \<open>Miscellaneous results about the operator norm needed for the proof 
of Banach-Steinhaus theorem\<close>

(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

theory Operator_Norm_Missing_Banach_Steinhaus
  imports 
    "HOL-Analysis.Infinite_Set_Sum"
    General_Results_Missing_Banach_Steinhaus
begin

lemma ex_norm_1:
  \<open>(UNIV::'a set) \<noteq> {0} \<Longrightarrow> \<exists> x::'a::real_normed_vector. norm x = 1\<close>
  by (metis (full_types) UNIV_eq_I insertI1 norm_sgn)

lemma ex_norm_1':
  \<open>\<exists> x::('a::{real_normed_vector,not_singleton}). norm x = 1\<close>
  by (simp add: ex_norm_1)

lemma norm_set_nonempty_eq1:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>(UNIV::'a set) \<noteq> {0}\<close>
  shows \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
  using assms ex_norm_1 by auto  

lemma norm_set_nonempty_eq1':
  fixes f :: \<open>'a::{real_normed_vector, not_singleton} \<Rightarrow> 'b::real_normed_vector\<close> 
  shows \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
  using norm_set_nonempty_eq1 General_Results_Missing_Banach_Steinhaus.UNIV_not_singleton 
    norm_set_nonempty_eq1 by blast

lemma norm_set_bdd_above_less1: 
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close> 
  shows \<open>bdd_above {norm (f x) |x. norm x < 1}\<close>
proof-
  have \<open>\<exists> M. \<forall> x. norm x < 1 \<longrightarrow> norm (f x) \<le> M\<close>
  proof -
    { fix aa :: "real \<Rightarrow> 'a"
      obtain rr :: "('a \<Rightarrow> 'b) \<Rightarrow> real" where
        "\<And>f a. 0 \<le> rr f \<and> (\<not> bounded_linear f \<or> norm (f a) \<le> norm a * rr f)"
        using bounded_linear.nonneg_bounded by moura
      hence "\<exists>r. \<not> norm (aa r) < 1 \<or> norm (f (aa r)) \<le> r"
        by (metis assms dual_order.trans less_eq_real_def mult.commute mult_left_le) }
    thus ?thesis
      by metis
  qed  
  thus ?thesis
    by auto 
qed

lemma norm_set_bdd_above_eq1: 
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> 
  assumes \<open>bounded_linear f\<close> 
  shows \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
  by (smt assms bdd_aboveI bounded_linear.bounded mem_Collect_eq)

proposition onorm_open_ball:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close> and \<open>(UNIV::'a set) \<noteq> {0}\<close>
  shows \<open>onorm f = Sup {norm (f x) | x. norm x < 1 }\<close>
proof(cases \<open>f = (\<lambda> _. 0)\<close>)
  case True
  have \<open>onorm f = 0\<close>
    by (simp add: True onorm_eq_0)
  moreover have \<open>Sup {norm (f x) | x. norm x < 1 } = 0\<close>
  proof-
    have \<open>norm (f x) = 0\<close>
      for x
      by (simp add: True)   
    hence \<open>{norm (f x) | x. norm x < 1 } = {0}\<close>
    proof-
      have \<open>{norm (f x) | x. norm x < 1 } \<subseteq> {0}\<close>
        using \<open>\<And>x. norm (f x) = 0\<close> by blast        
      moreover have \<open>{norm (f x) | x. norm x < 1 } \<supseteq> {0}\<close>
        using assms linear_simps(3) by fastforce                
      ultimately show ?thesis 
        by blast
    qed
    thus ?thesis by simp
  qed
  ultimately show ?thesis by simp
next
  case False
  have \<open>Sup {norm (f x) | x. norm x = 1} = Sup {norm (f x) | x. norm x < 1}\<close>
  proof-
    have \<open>Sup {norm (f x) | x. norm x = 1} \<le> Sup {norm (f x) | x. norm x < 1}\<close>
    proof-
      have \<open>{norm (f x) | x. norm x = 1} \<noteq> {}\<close>
      proof -
        have "\<exists>a. norm (a::'a) = 1"
          by (metis (full_types) False assms(1) linear_simps(3) norm_sgn)
        thus ?thesis
          by blast
      qed
      moreover have \<open>bdd_above {norm (f x) | x. norm x = 1}\<close>
        by (simp add: assms norm_set_bdd_above_eq1) 
      moreover have \<open>y \<in> {norm (f x) | x. norm x = 1} \<Longrightarrow> y \<le> Sup {norm (f x) | x. norm x < 1}\<close>
        for y
      proof-
        assume \<open>y \<in> {norm (f x) | x. norm x = 1}\<close>
        hence \<open>\<exists> x. y = norm (f x) \<and> norm x = 1\<close>
          by blast
        then obtain x where \<open>y = norm (f x)\<close> and \<open>norm x = 1\<close>
          by auto
        have \<open>\<exists> yy. (\<forall> n::nat. yy n \<in> {norm (f x) | x. norm x < 1}) \<and> (yy \<longlonglongrightarrow> y)\<close>
        proof-
          define yy where \<open>yy n = (1 - (inverse (real (Suc n)))) *\<^sub>R y\<close>
            for n
          have \<open>yy n \<in> {norm (f x) | x. norm x < 1}\<close>
            for n
          proof-
            have \<open>yy n = norm (f ( (1 - (inverse (real (Suc n)))) *\<^sub>R x) )\<close>
            proof-
              have \<open>yy n = (1 - (inverse (real (Suc n)))) *\<^sub>R norm (f x)\<close>
                using yy_def \<open>y = norm (f x)\<close> by blast
              also have \<open>... = \<bar>(1 - (inverse (real (Suc n))))\<bar> *\<^sub>R norm (f x)\<close>
                by (metis (mono_tags, hide_lams) \<open>y = norm (f x)\<close> abs_1 abs_le_self_iff abs_of_nat abs_of_nonneg add_diff_cancel_left' add_eq_if cancel_comm_monoid_add_class.diff_cancel diff_ge_0_iff_ge eq_iff_diff_eq_0 inverse_1 inverse_le_iff_le nat.distinct(1) of_nat_0  of_nat_Suc of_nat_le_0_iff zero_less_abs_iff zero_neq_one)
              also have \<open>... = norm ( (1 - (inverse (real (Suc n)))) *\<^sub>R (f x))\<close>
                by simp
              also have \<open>... = norm (f ((1 - (inverse (real (Suc n)))) *\<^sub>R  x))\<close>
                using \<open>bounded_linear f\<close>
                by (simp add: linear_simps(5)) 
              finally show ?thesis by blast
            qed
            moreover have \<open>norm ((1 - (inverse (real (Suc n)))) *\<^sub>R x) < 1\<close>
            proof-
              have \<open>norm ((1 - (inverse (real (Suc n)))) *\<^sub>R x) 
                  = \<bar>(1 - (inverse (real (Suc n))))\<bar> * norm x\<close>
                by simp
              hence \<open>norm ((1 - (inverse (real (Suc n)))) *\<^sub>R x) 
                  = (1 - (inverse (real (Suc n)))) * norm x\<close>
                by (simp add: linordered_field_class.inverse_le_1_iff)                
              thus ?thesis using \<open>norm x = 1\<close>
                by simp 
            qed
            ultimately show ?thesis
              by blast 
          qed
          moreover have \<open>yy \<longlonglongrightarrow> y\<close>
          proof-
            have \<open>(\<lambda> n. (1 - (inverse (real (Suc n)))) ) \<longlonglongrightarrow> 1\<close>
              using Limits.LIMSEQ_inverse_real_of_nat_add_minus by simp
            hence \<open>(\<lambda> n. (1 - (inverse (real (Suc n)))) *\<^sub>R y) \<longlonglongrightarrow> 1 *\<^sub>R y\<close>
              using Limits.tendsto_scaleR by blast
            hence \<open>(\<lambda> n. (1 - (inverse (real (Suc n)))) *\<^sub>R y) \<longlonglongrightarrow> y\<close>
              by simp
            hence \<open>(\<lambda> n. yy n) \<longlonglongrightarrow> y\<close>
              using yy_def by simp
            thus ?thesis by simp
          qed
          ultimately show ?thesis by blast
        qed
        then obtain yy
          where \<open>\<And> n::nat. yy n \<in> {norm (f x) | x. norm x < 1}\<close> and \<open>yy \<longlonglongrightarrow> y\<close>
          by auto
        have \<open>{norm (f x) | x. norm x < 1} \<noteq> {}\<close>
          using \<open>\<And>n. yy n \<in> {norm (f x) |x. norm x < 1}\<close> by auto          
        moreover have \<open>bdd_above {norm (f x) | x. norm x < 1}\<close>
          by (simp add: assms norm_set_bdd_above_less1)          
        ultimately have \<open>yy n \<le> Sup {norm (f x) | x. norm x < 1}\<close>
          for n
          using \<open>\<And> n::nat. yy n \<in> {norm (f x) | x. norm x < 1}\<close>
          by (simp add: cSup_upper)
        hence \<open>y \<le> Sup {norm (f x) | x. norm x < 1}\<close>
          using \<open>yy \<longlonglongrightarrow> y\<close> Topological_Spaces.Sup_lim
          by (meson LIMSEQ_le_const2) 
        thus ?thesis by blast
      qed
      ultimately show ?thesis
        by (meson cSup_least)
    qed
    moreover have \<open>Sup {norm (f x) | x. norm x < 1} \<le> Sup {norm (f x) | x. norm x = 1}\<close>
    proof-
      have \<open>{norm (f x) | x. norm x < 1} \<noteq> {}\<close>
        by (metis (mono_tags, lifting) Collect_empty_eq_bot bot_empty_eq empty_iff norm_zero zero_less_one)  
      moreover have \<open>bdd_above {norm (f x) | x. norm x < 1}\<close>
        using \<open>bounded_linear f\<close>
        by (simp add: norm_set_bdd_above_less1)        
      moreover have \<open>y \<in> {norm (f x) | x. norm x < 1} \<Longrightarrow> y \<le> Sup {norm (f x) | x. norm x = 1}\<close>
        for y
      proof(cases \<open>y = 0\<close>)
        case True
        thus ?thesis
        proof-
          have \<open>norm (f x) \<ge> 0\<close>
            for x
            by simp            
          moreover have \<open>{norm (f x) |x::'a. norm x = 1} \<noteq> {}\<close>          
            using  \<open>(UNIV::'a set) \<noteq> {0}\<close> norm_set_nonempty_eq1[where f = "f"] by blast
          moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
            by (simp add: assms norm_set_bdd_above_eq1)            
          ultimately have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
            using Collect_empty_eq cSup_upper mem_Collect_eq
          proof -
            have "\<exists>r. (\<exists>a. r = norm (f a) \<and> norm a = 1) \<and> 0 \<le> r"
              using \<open>\<And>x. 0 \<le> norm (f x)\<close> \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close> by blast
            hence "\<exists>r. r \<in> {norm (f a) |a. norm a = 1} \<and> 0 \<le> r"
              by blast
            thus ?thesis
              by (metis (lifting) \<open>bdd_above {norm (f x) |x. norm x = 1}\<close> cSup_upper2)
          qed            
          thus ?thesis
            by (simp add: True) 
        qed
      next
        case False
        hence \<open>y \<noteq> 0\<close> by blast
        assume \<open>y \<in> {norm (f x) | x. norm x < 1}\<close>
        hence \<open>\<exists> x. y = norm (f x) \<and> norm x < 1\<close>
          by blast
        then obtain x where \<open>y = norm (f x)\<close> and \<open>norm x < 1\<close>
          by blast
        have \<open>{norm (f x) | x. norm x = 1} \<noteq> {}\<close>
          using False \<open>y = norm (f x)\<close> assms norm_set_nonempty_eq1[where f = "f"]
          by blast          
        moreover have \<open>bdd_above {norm (f x) | x. norm x = 1}\<close>
          using assms norm_set_bdd_above_eq1 by force
        moreover have \<open>(1/norm x) * y \<in> {norm (f x) | x. norm x = 1}\<close>
        proof-
          have \<open>(1/norm x) * y  = norm (f ((1/norm x) *\<^sub>R x))\<close>
          proof-
            have \<open>(1/norm x) * y = (1/norm x) * norm (f x)\<close>
              by (simp add: \<open>y = norm (f x)\<close>)
            also have \<open>... = \<bar>1/norm x\<bar> * norm (f x)\<close>
              by simp
            also have \<open>... = norm ((1/norm x) *\<^sub>R (f x))\<close>
              by simp
            also have \<open>... = norm (f ((1/norm x) *\<^sub>R x))\<close>
              by (simp add: assms linear_simps(5))
            finally show ?thesis by blast
          qed
          moreover have \<open>norm ((1/norm x) *\<^sub>R x) = 1\<close>
          proof-              
            have \<open>x \<noteq> 0\<close>
              using  \<open>y \<noteq> 0\<close> \<open>y = norm (f x)\<close> assms linear_simps(3) by auto
            have \<open>norm ((1/norm x) *\<^sub>R x) = \<bar> (1/norm x) \<bar> * norm x\<close>
              by simp
            also have \<open>... = (1/norm x) * norm x\<close>
              by simp
            finally show ?thesis using \<open>x \<noteq> 0\<close>
              by simp 
          qed
          ultimately show ?thesis
            by blast 
        qed
        ultimately have \<open>(1/norm x) * y \<le> Sup {norm (f x) | x. norm x = 1}\<close>
          by (simp add: cSup_upper)
        moreover have \<open>y \<le> (1/norm x) * y\<close> 
          using \<open>norm x < 1\<close> \<open>y = norm (f x)\<close> assms divide_less_eq_1_pos linear_simps(3) mult_less_cancel_right2 norm_ge_zero norm_le_zero_iff
          by (metis less_imp_not_less not_le_imp_less)
        thus ?thesis
          using calculation by linarith 
      qed
      ultimately show ?thesis
        by (meson cSup_least) 
    qed
    ultimately show ?thesis by simp
  qed
  moreover have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) | x. norm x = 1}\<close>
  proof-
    have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) / norm x | x. True}\<close>
      by (simp add: full_SetCompr_eq)
    also have \<open>... = Sup {norm (f x) | x. norm x = 1}\<close>
    proof-
      have \<open>{norm (f x) / norm x |x. True} = {norm (f x) |x. norm x = 1} \<union> {0}\<close>
      proof-
        have \<open>y \<in> {norm (f x) / norm x |x. True} \<Longrightarrow> y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
          for y
        proof-
          assume \<open>y \<in> {norm (f x) / norm x |x. True}\<close>
          show ?thesis
          proof(cases \<open>y = 0\<close>)
            case True
            thus ?thesis
              by simp 
          next
            case False
            have \<open>\<exists> x. y = norm (f x) / norm x\<close>
              using \<open>y \<in> {norm (f x) / norm x |x. True}\<close> by auto
            then obtain x where \<open>y = norm (f x) / norm x\<close>
              by blast
            hence \<open>y = \<bar>(1/norm x)\<bar> * norm ( f x )\<close>
              by simp
            hence \<open>y = norm ( (1/norm x) *\<^sub>R f x )\<close>
              by simp
            hence \<open>y = norm ( f ((1/norm x) *\<^sub>R x) )\<close>
              by (simp add: assms linear_simps(5))
            moreover have \<open>norm ((1/norm x) *\<^sub>R x) = 1\<close>
              using False \<open>y = norm (f x) / norm x\<close> by auto              
            ultimately have \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
              by blast
            thus ?thesis by blast
          qed
        qed
        moreover have \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0} \<Longrightarrow> y \<in> {norm (f x) / norm x |x. True}\<close>
          for y
        proof(cases \<open>y = 0\<close>)
          case True
          thus ?thesis
            by auto 
        next
          case False
          hence \<open>y \<notin> {0}\<close>
            by simp
          moreover assume \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
          ultimately have \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
            by simp
          hence \<open>\<exists> x. norm x = 1 \<and> y = norm (f x)\<close>
            by auto
          then obtain x where \<open>norm x = 1\<close> and \<open>y = norm (f x)\<close>
            by auto
          have \<open>y = norm (f x) / norm x\<close> using  \<open>norm x = 1\<close>  \<open>y = norm (f x)\<close>
            by simp 
          thus ?thesis
            by auto 
        qed
        ultimately show ?thesis by blast
      qed
      hence \<open>Sup {norm (f x) / norm x |x. True} = Sup ({norm (f x) |x. norm x = 1} \<union> {0})\<close>
        by simp
      moreover have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
      proof-
        have \<open>\<exists> x::'a. norm x = 1 \<and> norm (f x) \<ge> 0\<close>
        proof-
          have \<open>\<exists> x::'a. norm x = 1\<close>
            by (metis (full_types) False assms(1) linear_simps(3) norm_sgn)
          then obtain x::'a where \<open>norm x = 1\<close>
            by blast
          have \<open>norm (f x) \<ge> 0\<close>
            by simp
          thus ?thesis using \<open>norm x = 1\<close> by blast
        qed
        hence \<open>\<exists> y \<in> {norm (f x) |x. norm x = 1}. y \<ge> 0\<close>
          by blast
        then obtain y::real where \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> 
          and \<open>y \<ge> 0\<close>
          by auto
        have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
          using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> by blast         
        moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
          by (simp add: assms norm_set_bdd_above_eq1)          
        ultimately have \<open>y \<le> Sup {norm (f x) |x. norm x = 1}\<close>
          using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
          by (simp add: cSup_upper) 
        thus ?thesis using \<open>y \<ge> 0\<close> by simp
      qed
      moreover have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {0}) = Sup {norm (f x) |x. norm x = 1}\<close>
      proof-
        have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
          using False assms norm_set_nonempty_eq1 by fastforce
        moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
          by (simp add: assms norm_set_bdd_above_eq1)    
        have \<open>{0::real} \<noteq> {}\<close>
          by simp
        moreover have \<open>bdd_above {0::real}\<close>
          by simp
        ultimately have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {(0::real)})
             = max (Sup {norm (f x) |x. norm x = 1}) (Sup {0::real})\<close>
        proof -
          have "\<And>r s. \<not> (r::real) \<le> s \<or> sup r s = s"
            by (metis (lifting) sup.absorb_iff1 sup_commute)
          thus ?thesis
            by (metis (lifting) \<open>0 \<le> Sup {norm (f x) |x. norm x = 1}\<close> \<open>bdd_above {0}\<close> \<open>bdd_above {norm (f x) |x. norm x = 1}\<close> \<open>{0} \<noteq> {}\<close> \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close> cSup_singleton cSup_union_distrib max.absorb_iff1 sup_commute)
        qed
        moreover have \<open>Sup {(0::real)} = (0::real)\<close>
          by simp          
        moreover have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
          by (simp add: \<open>0 \<le> Sup {norm (f x) |x. norm x = 1}\<close>)
        ultimately show ?thesis
          by simp
      qed
      moreover have \<open>Sup ( {norm (f x) |x. norm x = 1} \<union> {0})
           = max (Sup {norm (f x) |x. norm x = 1}) (Sup {0}) \<close>
        using calculation(2) calculation(3) by auto
      ultimately show ?thesis by simp 
    qed
    ultimately show ?thesis
      by linarith 
  qed
  ultimately have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) | x. norm x < 1 }\<close>
    by simp
  thus ?thesis using onorm_def
    by metis 
qed

proposition onorm_open_ball':
  fixes f :: \<open>'a::{real_normed_vector, not_singleton} \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close>
  shows \<open>onorm f = Sup {norm (f x) | x. norm x < 1 }\<close>
  using onorm_open_ball assms by fastforce

lemma onorm_open_ball_scaled:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
    and  r :: real
  assumes \<open>r > 0\<close> and \<open>bounded_linear f\<close>
  shows  \<open>onorm f  = (1/r) * Sup {norm (f x) | x. norm x < r}\<close>
proof(cases \<open>(UNIV::'a set) = {0}\<close>)
  case True
  have \<open>f 0 = 0\<close>
    using \<open>bounded_linear f\<close>
    by (simp add: linear_simps(3))
  moreover have \<open>x = 0\<close>
    for x::'a
    using \<open>UNIV = {0}\<close>
    by auto
  ultimately have \<open>f x = 0\<close>
    for x
    by (metis (full_types))
  hence \<open>norm (f x) = 0\<close>
    for x
    by auto
  hence \<open>onorm f = 0\<close>
    by (simp add: \<open>\<And>x. f x = 0\<close> assms(2) onorm_eq_0)    
  moreover have \<open>(1/r) * Sup {norm (f x) | x. norm x < r} = 0\<close>
  proof-
    have \<open>\<exists> x. norm x < r\<close>
      by (metis assms(1) norm_zero)
    hence \<open>{norm (f x) | x. norm x < r} = {0}\<close>
      using \<open>\<And> x. norm (f x) = 0\<close> norm_zero singleton_conv
      by (simp add: \<open>\<exists>x. norm x < r\<close>)
    thus ?thesis
      by simp 
  qed
  ultimately show ?thesis
    by simp
next
  case False
  have \<open>(1/r) * Sup {norm (f x) | x. norm x < r} = Sup {norm (f x) | x. norm x < 1}\<close>
  proof-
    have \<open>(1/r) * Sup {norm (f x) | x. norm x < r}
        = Sup {(1/r) * norm (f x) | x. norm x < r}\<close>
    proof-
      define S where \<open>S = {norm (f x) | x. norm x < r}\<close>
      have \<open>S \<noteq> {}\<close>
        using S_def
        by (metis (mono_tags, lifting) Collect_empty_eq assms(1) norm_eq_zero)
      moreover have  \<open>bdd_above S\<close>
      proof-
        have \<open>\<exists> K. \<forall> x. norm x < r \<longrightarrow> norm (f x) < K\<close>
        proof-
          have \<open>norm (f x) \<le> onorm f * norm x\<close>
            for x
            by (simp add: assms(2) onorm)            
          thus ?thesis
            by (meson assms(2) bounded_linear.pos_bounded dual_order.strict_trans2 real_mult_less_iff1) 
        qed
        thus ?thesis
          using S_def order.strict_implies_order by force 
      qed
      moreover have \<open>mono ( (*) (1/r) )\<close>
      proof-
        from \<open>r > 0\<close>
        have \<open>(1/r) > 0\<close>
          by simp
        thus ?thesis
          using mono_def real_mult_le_cancel_iff2 by blast 
      qed
      moreover have \<open>continuous (at_left (Sup S)) ( (*) (1/r) )\<close>
      proof-
        have \<open>isCont ( (*) (1/r) ) x\<close>
          for x
          by simp          
        thus ?thesis using \<open>S \<noteq> {}\<close> \<open>bdd_above S\<close>
          by (simp add: continuous_at_imp_continuous_at_within)
      qed
      ultimately have \<open>( (*) (1/r) ) (Sup S) = Sup {( (*) (1/r) ) s | s. s \<in> S}\<close>
      proof -
        have "Sup ((*) (1 / r) ` S) = 1 / r * Sup S"
          by (metis (full_types) \<open>S \<noteq> {}\<close> \<open>bdd_above S\<close> \<open>continuous (at_left (Sup S)) ((*) (1 / r))\<close> \<open>mono ((*) (1 / r))\<close> continuous_at_Sup_mono)
        thus ?thesis
          by (simp add: setcompr_eq_image)
      qed        
      hence  \<open>Sup {( (*) (1/r) ) ( norm (f x) ) | x. norm x < r}
              = ( (*) (1/r) ) ( Sup {norm (f x) | x. norm x < r} )\<close>
      proof -
        have "\<forall>p q. (\<exists>r. ((r::real) \<in> Collect p) \<noteq> (r \<in> Collect q)) \<or> Collect p = Collect q"
          by blast
        then obtain rr :: "(real \<Rightarrow> bool) \<Rightarrow> (real \<Rightarrow> bool) \<Rightarrow> real" where
          f1: "\<forall>p q. (rr q p \<in> Collect p) \<noteq> (rr q p \<in> Collect q) \<or> Collect p = Collect q"
          by (metis (no_types))
        have f2: "\<forall>x0. (norm (x0::'a) < r) = (\<not> r + - 1 * norm x0 \<le> 0)"
          by linarith
        obtain rra :: "real \<Rightarrow> real" where
          f3: "(rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<notin> {1 / r * ra |ra. ra \<in> S} \<or> rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) = 1 / r * rra (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r)) \<and> rra (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r)) \<in> S) \<and> (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * ra |ra. ra \<in> S} \<or> (\<forall>ra. rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<noteq> 1 / r * ra \<or> ra \<notin> S))"
          by moura
        have "\<forall>x0. (norm (x0::'a) < r) = (\<not> r + - 1 * norm x0 \<le> 0)"
          by fastforce
        then obtain aa :: "real \<Rightarrow> 'a" where
          f4: "rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * ra |ra. ra \<in> S} \<longrightarrow> rra (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r)) = norm (f (aa (rra (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r))))) \<and> \<not> r + - 1 * norm (aa (rra (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r)))) \<le> 0"
          using f3 S_def by moura
        hence "rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * ra |ra. ra \<in> S} \<longrightarrow> rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) = 1 / r * norm (f (aa (rra (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r)))))"
          using f3 by presburger
        hence f5: "rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<notin> {1 / r * ra |ra. ra \<in> S} \<or> rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * norm (f a) |a. norm a < r}"
          using f4 f2 by blast
        obtain aaa :: "real \<Rightarrow> 'a" where
          f6: "(rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<notin> {1 / r * norm (f a) |a. norm a < r} \<or> rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) = 1 / r * norm (f (aaa (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r)))) \<and> \<not> r + - 1 * norm (aaa (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r))) \<le> 0) \<and> (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * norm (f a) |a. norm a < r} \<or> (\<forall>a. rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<noteq> 1 / r * norm (f a) \<or> r + - 1 * norm a \<le> 0))"
          by moura
        have "(rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<notin> {1 / r * norm (f a) |a. norm a < r}) = (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * ra |ra. ra \<in> S}) \<longrightarrow> (\<forall>a. norm (f (aaa (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r)))) \<noteq> norm (f a) \<or> r + - 1 * norm a \<le> 0)"
          using S_def by blast
        hence "(rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<notin> {1 / r * norm (f a) |a. norm a < r}) \<noteq> (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * ra |ra. ra \<in> S})"
          using f6 f5 by blast
        hence "{1 / r * norm (f a) |a. norm a < r} = {1 / r * ra |ra. ra \<in> S}"
          using f1 by meson
        thus ?thesis
          using S_def \<open>1 / r * Sup S = Sup {1 / r * s |s. s \<in> S}\<close> by presburger
      qed          
      thus ?thesis by simp
    qed
    also have \<open>...
        = Sup { norm ((1/r) *\<^sub>R (f x)) | x. norm x < r}\<close>
    proof-
      have \<open>(1/r) * norm (f x) = norm ((1/r) *\<^sub>R (f x))\<close>
        for x
      proof-
        have \<open>1/r > 0\<close>
          by (simp add: assms(1))
        moreover have \<open>\<bar>(1/r)\<bar> * norm (f x) = norm ((1/r) *\<^sub>R (f x))\<close>
          by simp          
        ultimately show ?thesis by simp
      qed
      thus ?thesis
        by presburger 
    qed
    also have \<open>...
        = Sup {norm (f ((1/r) *\<^sub>R x)) | x. norm x < r}\<close>
    proof-
      have \<open>(1/r) *\<^sub>R (f x) = f ((1/r) *\<^sub>R x)\<close>
        for x
        using \<open>bounded_linear f\<close>
        by (simp add: linear_simps(5))
      thus ?thesis
        by simp 
    qed
    also have \<open>...
        = Sup { norm (f ((1/r) *\<^sub>R (r *\<^sub>R x))) | x. norm (r *\<^sub>R x) < r}\<close>
    proof-
      have \<open>{norm (f ((1/r) *\<^sub>R x)) | x. norm x < r} 
           = (\<lambda> x. norm (f ((1/r) *\<^sub>R x))) ` {x | x. norm x < r}\<close>
        by auto
      also have \<open>... 
           = (\<lambda> x. norm (f ((1/r) *\<^sub>R x))) ` {r *\<^sub>R x | x. norm ( r *\<^sub>R x) < r}\<close>
      proof-    
        have \<open>bij (((*\<^sub>R) r)::'a \<Rightarrow> 'a)\<close>
        proof-
          have \<open>r \<noteq> 0\<close>
            using assms(1) by auto            
          hence \<open>inj (((*\<^sub>R) r)::'a \<Rightarrow> 'a)\<close>
            by (simp add: \<open>r \<noteq> 0\<close> inj_on_def)
          moreover have \<open>surj (((*\<^sub>R) r)::'a \<Rightarrow> 'a)\<close>
            using assms(1) cone_iff by auto 
          ultimately show ?thesis
            by (simp add: bijI) 
        qed
        hence \<open>{x | x::'a. norm x < r} = { (inv ( (*\<^sub>R) r)) x | x. norm ( (inv ( (*\<^sub>R) r)) x ) < r}\<close>
          by (metis UNIV_I bij_betw_inv_into_left)
        hence \<open>{x | x::'a. norm x < r} = {r *\<^sub>R x | x::'a. norm (r *\<^sub>R x) < r}\<close>
          by (metis (mono_tags, lifting) UNIV_I \<open>bij ((*\<^sub>R) r)\<close> bij_betw_inv_into bij_betw_inv_into_left inv_inv_eq)          
        thus ?thesis
          by fastforce
      qed
      finally have \<open>{norm (f ((1/r) *\<^sub>R x)) | x::'a. norm x < r} = {norm (f ((1/r) *\<^sub>R (r *\<^sub>R x))) | x::'a. norm (r *\<^sub>R x) < r}\<close>
        by blast
      thus ?thesis
        by simp 
    qed
    also have \<open>...
        = Sup { norm (f x) | x. norm x < 1}\<close>
    proof-
      have \<open>{norm (f ((1 / r) *\<^sub>R r *\<^sub>R x)) |x. norm (r *\<^sub>R x) < r}
            = {norm (f x) |x. norm (r *\<^sub>R x) < r}\<close>
        by simp
      hence \<open>...
            = {norm (f x) |x. \<bar>r\<bar> * norm x < r}\<close>
        by simp
      hence \<open>...
            = {norm (f x) |x. \<bar>r\<bar> * norm x < r}\<close>
        by simp
      hence \<open>...
            = {norm (f x) |x. r * norm x < r}\<close>
        using \<open>r > 0\<close> by simp
      have \<open>...
            = {norm (f x) |x. norm x < 1}\<close>
        using \<open>r > 0\<close> by simp
      hence \<open>{norm (f ((1 / r) *\<^sub>R r *\<^sub>R x)) |x. norm (r *\<^sub>R x) < r}
            = {norm (f x) |x. norm x < 1}\<close>
        using \<open>{norm (f x) |x. \<bar>r\<bar> * norm x < r} = {norm (f x) |x. r * norm x < r}\<close> by auto
      thus ?thesis by simp
    qed
    finally show ?thesis by blast
  qed
  thus ?thesis
    using \<open>bounded_linear f\<close> False onorm_open_ball[where f = "f"]
    by auto
qed

end

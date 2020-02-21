(*
  File:   Banach_Steinhaus_Missing.thy
  Author: Dominique Unruh, University of Tartu
  Author: Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Missing results for Banach-Steinhaus\<close>
(*
subjective perfection = 60% (Jose)
this file is really ugly
*)

theory Banach_Steinhaus_Missing
  imports 
    "HOL-Analysis.Infinite_Set_Sum"
    "HOL-Types_To_Sets.Types_To_Sets"
begin

text\<open>
  In this file we put all the preliminary results in order to develop the proof of 
  Banach-Steinhaus theorem.
\<close>

subsection\<open>General results missing\<close>

lemma sum_interval_split: 
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add" and a b :: nat
  assumes "b>a" 
  shows "sum f {Suc a..b} = sum f {..b} - sum f {..a}" 
proof -
  obtain c where c: "b = a+c"
    using \<open>a < b\<close> less_imp_add_positive by blast
  show ?thesis
    unfolding c sum_up_index_split
    by auto 
qed

class not_singleton =
  assumes not_singleton_card: "\<exists>x. \<exists>y. x \<noteq> y"

lemma not_singleton_existence[simp]:
  \<open>\<exists> x::('a::not_singleton). x \<noteq> t\<close>
proof (rule classical)
  assume \<open>\<nexists>x. (x::'a) \<noteq> t\<close> 
  have \<open>\<exists> x::'a. \<exists> y::'a. x \<noteq> y\<close>
    using not_singleton_card
    by blast
  then obtain x y::'a where \<open>x \<noteq> y\<close>
    by blast
  have \<open>\<forall> x::'a. x = t\<close>
    using \<open>\<nexists>x. (x::'a) \<noteq> t\<close> by simp
  hence \<open>x = t\<close>
    by blast
  moreover have \<open>y = t\<close>
    using \<open>\<forall> x::'a. x = t\<close>
    by blast
  ultimately have \<open>x = y\<close>
    by simp
  thus ?thesis using \<open>x \<noteq> y\<close> by blast
qed

lemma UNIV_not_singleton[simp]: "(UNIV::_::not_singleton set) \<noteq> {x}"
  using not_singleton_existence[of x] by blast

lemma UNIV_not_singleton_converse: "(\<And> x. (UNIV::'a set) \<noteq> {x}) \<Longrightarrow> \<exists>x::'a. \<exists>y::'a. x \<noteq> y"
  by fastforce

lemma UNIV_not_singleton_converse_zero: "((UNIV::('a::real_normed_vector) set) \<noteq> {0}) \<Longrightarrow> \<exists>x::'a. \<exists>y::'a. x \<noteq> y"
  using UNIV_not_singleton_converse
  by fastforce 

lemma linear_plus_minus_one_half: 
  "linear f \<Longrightarrow> f \<xi> = (inverse (of_nat 2)) *\<^sub>R (f (x + \<xi>) - f (x - \<xi>))"
proof-
  assume \<open>linear f\<close>
  have \<open>\<xi> = (inverse (of_nat 2)) *\<^sub>R ( (x + \<xi>) - (x - \<xi>) )\<close>
    by simp
  have \<open>f \<xi> = f ((inverse (of_nat 2)) *\<^sub>R ( (x + \<xi>) - (x - \<xi>) ))\<close>
    by simp 
  also have \<open>\<dots> = (inverse (of_nat 2)) *\<^sub>R f ( (x + \<xi>) - (x - \<xi>) )\<close>
    using \<open>linear f\<close> linear_scale by blast
  finally show ?thesis
    using \<open>linear f\<close> linear_diff
    by metis
qed

lemma bdd_above_plus:
  \<open>S \<noteq> {} \<Longrightarrow> bdd_above (f ` S) \<Longrightarrow> bdd_above (g ` S) \<Longrightarrow> bdd_above ((\<lambda> x. f x + g x) ` S)\<close>
  for f::\<open>'a \<Rightarrow> real\<close>
proof-
  assume \<open>S \<noteq> {}\<close> and \<open>bdd_above (f ` S)\<close> and \<open>bdd_above (g ` S)\<close>
  obtain M where \<open>\<And> x. x\<in>S \<Longrightarrow> f x \<le> M\<close>
    using \<open>bdd_above (f ` S)\<close>
    unfolding bdd_above_def
    by auto
  obtain N where \<open>\<And> x. x\<in>S \<Longrightarrow> g x \<le> N\<close>
    using \<open>bdd_above (g ` S)\<close>
    unfolding bdd_above_def
    by auto
  have \<open>\<And> x. x\<in>S \<Longrightarrow> f x + g x \<le> M + N\<close>
    using \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<le> M\<close> \<open>\<And>x. x \<in> S \<Longrightarrow> g x \<le> N\<close> by fastforce
  thus ?thesis
    unfolding bdd_above_def by auto
qed


subsection\<open>Operator norm missing\<close>

text\<open>The results developed here are a complement to the file Operator_Norm.thy.\<close>

lemma ex_norm_1:
  \<open>\<exists> x::('a::{real_normed_vector,not_singleton}). norm x = 1\<close>
proof-
  have \<open>(UNIV::'a set) \<noteq> {0} \<Longrightarrow> \<exists> x::'a. norm x = 1\<close>
    by (metis (full_types) UNIV_eq_I insertI1 norm_sgn)
  thus ?thesis
    by simp
qed

lemma norm_set_nonempty_eq1:
  fixes f :: \<open>'a::{real_normed_vector, not_singleton} \<Rightarrow> 'b::real_normed_vector\<close> 
  shows \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
  using ex_norm_1
  by simp 

lemma norm_set_nonempty_eq1':
  fixes f :: \<open>'c::{real_normed_vector} \<Rightarrow> 'b::real_normed_vector\<close> 
  assumes "(UNIV::'c set)\<noteq>0" 
  shows \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
proof -
  have ex2: "\<exists>x y :: 'c. x \<noteq> y"
    apply (rule exI[of _ 0])
    using assms by auto
  have rnv: "class.real_normed_vector (-) dist norm (+) (0::'c) uminus (*\<^sub>R) sgn uniformity open"
    apply (rule class.real_normed_vector.intro)
         apply (rule class.dist_norm.intro)
         apply (rule dist_norm)
        apply (rule class.real_vector.intro)
         apply (rule class.ab_group_add.intro)
          apply (rule class.comm_monoid_add.intro)
           apply (rule class.ab_semigroup_add.intro)
            apply intro_classes
    by (auto intro: sgn_div_norm uniformity_dist simp: open_uniformity scaleR_add_right 
        scaleR_add_left norm_triangle_ineq)
  show ?thesis
    apply (rule norm_set_nonempty_eq1[internalize_sort "'a::{real_normed_vector, not_singleton}"])
    using ex2 apply (rule class.not_singleton.intro)
    by (rule rnv)
qed

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
  assumes \<open>bounded_linear f\<close>
  shows \<open>onorm f = Sup {norm (f x) | x. norm x < 1 }\<close>
proof(cases \<open>(UNIV::'a set) = 0\<close>)
  case True
  hence \<open>x = 0\<close> for x::'a
    by auto
  hence \<open>f x = 0\<close> for x
    using \<open>bounded_linear f\<close> by (metis (full_types) linear_simps(3))
  hence \<open>onorm f = 0\<close>
    by (simp add: assms onorm_eq_0)    
  moreover have \<open>Sup {norm (f x) | x. norm x < 1} = 0\<close>
  proof-
    have \<open>{norm (f x) | x. norm x < 1} = {0}\<close>
      by (smt Collect_cong \<open>\<And>x. f x = 0\<close> norm_zero singleton_conv)      
    thus ?thesis by simp
  qed
  ultimately show ?thesis
    by simp
next
  case False
  hence \<open>(UNIV::'a set) \<noteq> 0\<close>
    by simp
  have \<open>onorm f = Sup {norm (f x) | x. norm x < 1 }\<close>
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
              apply (rule norm_set_nonempty_eq1')
              using \<open>UNIV \<noteq> 0\<close> by auto                            
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
          proof-              
            have \<open>\<exists> x::'a. norm x = 1\<close>
            proof-
              have \<open>\<exists> x::'a. x \<noteq> 0\<close>
                using \<open>UNIV \<noteq> 0\<close> by auto
              then obtain x::'a where \<open>x \<noteq> 0\<close>
                by blast
              hence \<open>norm x \<noteq> 0\<close>
                by auto
              define y where \<open>y = x /\<^sub>R norm x\<close>
              have \<open>norm y = norm (x /\<^sub>R norm x)\<close>
                unfolding y_def by auto
              also have \<open>\<dots> = (norm x) /\<^sub>R (norm x)\<close>
                by auto
              also have \<open>\<dots> = 1\<close>
                using \<open>norm x \<noteq> 0\<close> by auto
              finally have \<open>norm y = 1\<close>
                by blast
              thus ?thesis by blast
            qed
            thus ?thesis by blast
          qed
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
            using \<open>UNIV \<noteq> 0\<close> norm_set_nonempty_eq1' by auto            
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
  thus ?thesis
    by simp    
qed


lemma onorm_open_ball_scaled:
  fixes f :: \<open>'a::{real_normed_vector,not_singleton} \<Rightarrow> 'b::real_normed_vector\<close>
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
    using \<open>bounded_linear f\<close> False
    by (simp add: onorm_open_ball)
qed

lemma linear_plus_norm:
  "linear f \<Longrightarrow> norm (f \<xi>) \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))"
proof-
  assume \<open>linear f\<close>
  have \<open>norm (f \<xi>) = norm ( (inverse (of_nat 2)) *\<^sub>R (f (x + \<xi>) - f (x - \<xi>)) )\<close>
    by (metis \<open>linear f\<close> linear_plus_minus_one_half)    
  also have \<open>\<dots> = inverse (of_nat 2) * norm (f (x + \<xi>) - f (x - \<xi>))\<close>
    using Real_Vector_Spaces.real_normed_vector_class.norm_scaleR
    by simp
  also have \<open>\<dots> \<le> inverse (of_nat 2) * (norm (f (x + \<xi>)) + norm (f (x - \<xi>)))\<close>
    by (simp add: norm_triangle_ineq4)
  also have \<open>\<dots> \<le>  max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>
    by auto
  finally show ?thesis
    by blast
qed

lemma onorm_1:
  \<open>bounded_linear f \<Longrightarrow> onorm f = Sup ((norm \<circ> f) ` (ball 0 1))\<close>
  unfolding ball_def 
  by (simp add: onorm_open_ball setcompr_eq_image)


lemma ball_scale:
  \<open>r > 0 \<Longrightarrow> ball (0::'a::real_normed_vector) r = ((*\<^sub>R) r) ` (ball 0 1)\<close>
proof-
  assume \<open>r > 0\<close>
  have \<open>norm x < 1 \<Longrightarrow> \<bar>r\<bar> * norm x < r\<close>
    for x::'a
    using  \<open>r > 0\<close> by auto
  moreover have \<open>norm x < r \<Longrightarrow> x \<in> (*\<^sub>R) r ` {y. norm y < 1}\<close>
    for x::'a
  proof-
    assume \<open>norm x < r\<close>
    define y where \<open>y = (inverse r) *\<^sub>R x\<close>
    have \<open>x = r *\<^sub>R y\<close>
      unfolding y_def
      using \<open>r > 0\<close>
      by auto
    moreover have \<open>norm y < 1\<close>
      unfolding y_def
      using \<open>r > 0\<close>  \<open>norm x < r\<close>
      by (smt left_inverse mult_left_le_imp_le norm_scaleR positive_imp_inverse_positive)      
    ultimately show ?thesis 
      by blast
  qed
  ultimately show ?thesis
    unfolding ball_def
    by auto
qed

lemma onorm_r:
  "bounded_linear f \<Longrightarrow> r > 0 \<Longrightarrow> onorm f = (inverse r) * Sup ((norm \<circ> f) ` (ball 0 r))"
proof-
  assume \<open>bounded_linear f\<close> and \<open>r > 0\<close>
  have \<open>ball (0::'a) r = ((*\<^sub>R) r) ` (ball 0 1)\<close>
    using \<open>0 < r\<close> ball_scale by blast
  hence \<open>Sup ((norm \<circ> f) ` (ball 0 r)) = Sup ((norm \<circ> f) ` (((*\<^sub>R) r) ` (ball 0 1)))\<close>
    by simp
  also have \<open>\<dots> = Sup ((norm \<circ> f \<circ> ((*\<^sub>R) r)) ` (ball 0 1))\<close>
    using Sup.SUP_image by auto
  also have \<open>\<dots> = Sup ((norm \<circ> ((*\<^sub>R) r) \<circ> f) ` (ball 0 1))\<close>
  proof-
    have \<open>(f \<circ> ((*\<^sub>R) r)) x = (((*\<^sub>R) r) \<circ> f) x\<close> for x
      using \<open>bounded_linear f\<close> by (simp add: linear_simps(5))
    hence \<open>f \<circ> ((*\<^sub>R) r) = ((*\<^sub>R) r) \<circ> f\<close>
      by auto      
    thus ?thesis
      by (simp add: comp_assoc) 
  qed
  also have \<open>\<dots> = Sup ((((*\<^sub>R) \<bar>r\<bar>) \<circ> norm \<circ> f) ` (ball 0 1))\<close>
  proof-
    have \<open>norm \<circ> ((*\<^sub>R) r) = ((*\<^sub>R) \<bar>r\<bar>) \<circ> (norm::'a \<Rightarrow> real)\<close>
      by auto
    thus ?thesis 
      by auto
  qed
  also have \<open>\<dots> = Sup ((((*\<^sub>R) r) \<circ> norm \<circ> f) ` (ball 0 1))\<close>
    using \<open>r > 0\<close> by auto
  also have \<open>\<dots> = r * Sup ((norm \<circ> f) ` (ball 0 1))\<close>
  proof(rule cSup_eq_non_empty)
    show \<open>((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1 \<noteq> {}\<close>
      by auto
    show \<open>x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1 \<Longrightarrow>
          x \<le> r * Sup ((norm \<circ> f) ` ball 0 1)\<close> for x
    proof-
      assume \<open>x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1\<close>
      hence \<open>\<exists> t. x = r *\<^sub>R norm (f t) \<and> norm t < 1\<close>
        by auto
      then obtain t where \<open>x = r *\<^sub>R norm (f t)\<close> and \<open>norm t < 1\<close>
        by blast
      have \<open>(norm \<circ> f) ` ball 0 1 \<noteq> {}\<close>
        by simp        
      moreover have \<open>bdd_above ((norm \<circ> f) ` ball 0 1)\<close>
        using \<open>bounded_linear f\<close> Elementary_Normed_Spaces.bounded_linear_image
          [where S = "ball (0::'a) 1" and f = f] bdd_above_norm image_comp
          Elementary_Metric_Spaces.bounded_ball[where x = "0::'a" and e = 1] by metis
      moreover have \<open>\<exists> y. y \<in> (norm \<circ> f) ` ball 0 1 \<and> x \<le> r * y\<close>
      proof-
        define y where \<open>y = x /\<^sub>R r\<close>
        have \<open>y \<in> (norm \<circ> f) ` ball 0 1\<close>
          unfolding y_def using \<open>x = r *\<^sub>R norm (f t)\<close>  \<open>norm t < 1\<close>
          by (smt \<open>0 < r\<close> \<open>x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1\<close> comp_apply image_iff 
              inverse_inverse_eq pos_le_divideR_eq positive_imp_inverse_positive)
        moreover have \<open>x \<le> r * y\<close>          
        proof -
          have "x = r * (inverse r * x)"
            using \<open>x = r *\<^sub>R norm (f t)\<close> by auto
          hence "x + - 1 * (r * (inverse r * x)) \<le> 0"
            by linarith
          hence "x \<le> r * (x /\<^sub>R r)"
            by auto
          thus ?thesis
            unfolding y_def by blast
        qed
        ultimately show ?thesis 
          by blast
      qed
      ultimately show ?thesis
        by (smt \<open>0 < r\<close> cSup_upper ordered_comm_semiring_class.comm_mult_left_mono) 
    qed
    show \<open>(\<And>x. x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1 \<Longrightarrow> x \<le> y) \<Longrightarrow>
         r * Sup ((norm \<circ> f) ` ball 0 1) \<le> y\<close> for y
    proof-
      assume \<open>\<And>x. x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1 \<Longrightarrow> x \<le> y\<close>
      have \<open>(norm \<circ> f) ` ball 0 1 \<noteq> {}\<close>
        by simp        
      moreover have \<open>bdd_above ((norm \<circ> f) ` ball 0 1)\<close>
        using \<open>bounded_linear f\<close> Elementary_Normed_Spaces.bounded_linear_image
          [where S = "ball (0::'a) 1" and f = f] bdd_above_norm image_comp
          Elementary_Metric_Spaces.bounded_ball[where x = "0::'a" and e = 1] by metis
      moreover have \<open>x \<in> ((norm \<circ> f) ` ball 0 1) \<Longrightarrow> x \<le> (inverse r) * y\<close> for x
      proof-
        assume \<open>x \<in> (norm \<circ> f) ` ball 0 1\<close>
        then obtain t where \<open>t \<in> ball (0::'a) 1\<close> and \<open>x = norm (f t)\<close>
          by auto
        define x' where \<open>x' = r *\<^sub>R x\<close>
        have \<open>x' = r *  norm (f t)\<close>
          by (simp add: \<open>x = norm (f t)\<close> x'_def)
        hence \<open>x' \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1\<close>
          using \<open>t \<in> ball (0::'a) 1\<close> by auto
        hence \<open>x' \<le> y\<close>
          using  \<open>\<And>x. x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1 \<Longrightarrow> x \<le> y\<close> by blast
        thus ?thesis
          unfolding x'_def using \<open>r > 0\<close> by (metis pos_le_divideR_eq real_scaleR_def)
      qed
      ultimately have \<open>Sup ((norm \<circ> f) ` ball 0 1) \<le> (inverse r) * y\<close>
        by (simp add: cSup_least)        
      thus ?thesis 
        using \<open>r > 0\<close>
        by (metis pos_le_divideR_eq real_scaleR_def) 
    qed
  qed
  also have \<open>\<dots> = r * onorm f\<close>
  proof-
    have \<open>onorm f = Sup ((norm \<circ> f) ` (ball 0 1))\<close>
      by (simp add: \<open>bounded_linear f\<close> onorm_1)      
    thus ?thesis
      by simp
  qed
  finally have \<open>Sup ((norm \<circ> f) ` ball 0 r) = r * onorm f\<close>
    by simp    
  thus ?thesis
    using \<open>r > 0\<close>
    by simp
qed


lemma sphere_antipodal:
  \<open>\<xi> \<in> ball (0::'a::real_normed_vector) r \<Longrightarrow> -\<xi> \<in> ball 0 r\<close>
proof-
  assume \<open>\<xi> \<in> ball (0::'a) r\<close>
  hence \<open>norm \<xi> < r\<close> by simp
  moreover have \<open>norm (-\<xi>) = norm \<xi>\<close> by simp
  ultimately show ?thesis by simp
qed

lemma max_Sup_absord_left:
  \<open>X \<noteq> {} \<Longrightarrow> bdd_above (f ` X) \<Longrightarrow>  bdd_above (g ` X) \<Longrightarrow> Sup (f ` X) \<ge> Sup (g ` X) \<Longrightarrow>
   Sup ((\<lambda> x. max (f x) (g x)) ` X) = Sup (f ` X)\<close>
  for f g :: \<open>'a \<Rightarrow> real\<close> and X::\<open>'a set\<close>
proof-
  assume \<open>X \<noteq> {}\<close> and \<open>bdd_above (f ` X)\<close> and \<open>bdd_above (g ` X)\<close> and \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close>
  have \<open>Sup ((\<lambda> x. max (f x) (g x)) ` X) \<le> Sup (f ` X)\<close>
  proof-
    have \<open>y \<in> ((\<lambda> x. max (f x) (g x)) ` X) \<Longrightarrow> y \<le> Sup (f ` X)\<close> for y
    proof-
      assume \<open>y \<in> ((\<lambda> x. max (f x) (g x)) ` X)\<close>
      then obtain x where \<open>y = max (f x) (g x)\<close> and \<open>x \<in> X\<close>
        by blast
      have \<open>f x \<le> Sup (f ` X)\<close>
        by (simp add:  \<open>x \<in> X\<close> \<open>bdd_above (f ` X)\<close> cSUP_upper) 
      moreover have  \<open>g x \<le> Sup (g ` X)\<close>
        by (simp add:  \<open>x \<in> X\<close> \<open>bdd_above (g ` X)\<close> cSUP_upper) 
      ultimately have \<open>max (f x) (g x) \<le> Sup (f ` X)\<close>
        using  \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close>
        by auto
      thus ?thesis
        by (simp add: \<open>y = max (f x) (g x)\<close>) 
    qed
    thus ?thesis
      by (simp add: \<open>X \<noteq> {}\<close> cSup_least) 
  qed
  moreover have \<open>Sup ((\<lambda> x. max (f x) (g x)) ` X) \<ge> Sup (f ` X)\<close>
  proof-
    have \<open>y \<in> f ` X \<Longrightarrow> y \<le> Sup ((\<lambda> x. max (f x) (g x)) ` X)\<close> for y
    proof-
      assume \<open>y \<in> f ` X\<close>
      then obtain x where \<open>x \<in> X\<close> and \<open>y = f x\<close>
        by blast
      have  \<open>bdd_above ((\<lambda> \<xi>. max (f \<xi>) (g \<xi>)) ` X)\<close>
        by (metis (no_types) \<open>bdd_above (f ` X)\<close> \<open>bdd_above (g ` X)\<close> bdd_above_image_sup sup_max)
      moreover have \<open>e > 0 \<Longrightarrow> \<exists> k \<in> (\<lambda> \<xi>. max (f \<xi>) (g \<xi>)) ` X. y \<le> k + e\<close>
        for e::real
        using \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close>
        by (smt \<open>x \<in> X\<close> \<open>y = f x\<close> image_eqI)        
      ultimately show ?thesis
        using \<open>x \<in> X\<close> \<open>y = f x\<close> cSUP_upper by fastforce                 
    qed
    thus ?thesis
      by (metis (mono_tags) cSup_least calculation empty_is_image)
  qed
  ultimately show ?thesis by simp
qed

lemma max_Sup_absord_right:
  \<open>X \<noteq> {} \<Longrightarrow> bdd_above (f ` X) \<Longrightarrow>  bdd_above (g ` X) \<Longrightarrow> Sup (f ` X) \<le> Sup (g ` X) \<Longrightarrow>
   Sup ((\<lambda> x. max (f x) (g x)) ` X) = Sup (g ` X)\<close>
  for f g :: \<open>'a \<Rightarrow> real\<close> and X::\<open>'a set\<close>
proof-
  assume \<open>X \<noteq> {}\<close> and \<open>bdd_above (f ` X)\<close> and \<open>bdd_above (g ` X)\<close> and \<open>Sup (f ` X) \<le> Sup (g ` X)\<close>
  hence \<open>Sup ((\<lambda> x. max (g x) (f x)) ` X) = Sup (g ` X)\<close>
    using max_Sup_absord_left by (simp add: \<open>bdd_above (g ` X)\<close> max_Sup_absord_left) 
  moreover have \<open>max (g x) (f x) = max (f x) (g x)\<close> for x
    by auto
  ultimately show ?thesis by simp
qed

lemma max_Sup:
  \<open>X \<noteq> {} \<Longrightarrow> bdd_above (f ` X) \<Longrightarrow>  bdd_above (g ` X) \<Longrightarrow> 
   Sup ((\<lambda> x. max (f x) (g x)) ` X) = max (Sup (f ` X))  (Sup (g ` X))\<close>
  for f g :: \<open>'a \<Rightarrow> real\<close> and X::\<open>'a set\<close>
proof(cases \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close>)
  case True 
  assume \<open>X \<noteq> {}\<close> and \<open>bdd_above (f ` X)\<close> and \<open>bdd_above (g ` X)\<close>
  thus ?thesis
    by (smt Inf.INF_cong \<open>X \<noteq> {}\<close> max_Sup_absord_right)
next
  case False
  assume \<open>X \<noteq> {}\<close> and \<open>bdd_above (f ` X)\<close> and \<open>bdd_above (g ` X)\<close>
  thus ?thesis
    by (smt Inf.INF_cong \<open>X \<noteq> {}\<close> max_Sup_absord_left)
qed

lemma bounded_linear_ball_bdd_above:
  \<open>r > 0 \<Longrightarrow> bounded_linear f \<Longrightarrow> bdd_above ((norm \<circ> f) ` (ball x r))\<close>
proof-
  assume \<open>r > 0\<close> and \<open>bounded_linear f\<close>
  define M where \<open>M = onorm f * (r + norm x)\<close>
  have \<open>norm (x - y) < r \<Longrightarrow> norm (f y) \<le> M\<close> for y
  proof-
    assume \<open>norm (x - y) < r\<close>
    moreover have \<open>norm (f \<xi>) \<le> onorm f * norm \<xi>\<close> for \<xi>
      by (simp add: \<open>bounded_linear f\<close> onorm)    
    moreover have \<open>norm y \<le> norm (x - y) + norm x\<close> for y
      by (smt norm_triangle_ineq3)
    ultimately show ?thesis
      by (smt M_def \<open>bounded_linear f\<close> combine_common_factor 
          linordered_comm_semiring_strict_class.comm_mult_strict_left_mono onorm_pos_le) 
  qed
  thus ?thesis
    unfolding bdd_above_def ball_def
    by (smt comp_eq_dest_lhs imageE mem_Collect_eq dist_norm)
qed

subsection \<open>Real Analysis Missing\<close>

text\<open>The results developed here are a complement to the real analysis of Isabelle/HOL\<close>

subsubsection \<open>Limits of sequences\<close>

lemma lim_shift:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and l::'a and n::nat
  assumes \<open>(\<lambda> k. x (n + k)) \<longlonglongrightarrow> l\<close>
  shows \<open>x \<longlonglongrightarrow> l\<close>
proof-
  have \<open>\<forall> x::nat \<Rightarrow> 'a::real_normed_vector. \<forall> l::'a. ((\<lambda> k. x (n + k)) \<longlonglongrightarrow> l) \<longrightarrow> (x \<longlonglongrightarrow> l)\<close>
  proof(induction n)
    case 0
    thus ?case by simp
  next
    case (Suc n)
    have \<open>(\<lambda>k. x (Suc n + k)) \<longlonglongrightarrow> l \<Longrightarrow> x \<longlonglongrightarrow> l\<close>
      for x::"nat \<Rightarrow> 'a" and l::'a
    proof-
      assume \<open>(\<lambda>k. x (Suc n + k)) \<longlonglongrightarrow> l\<close>
      hence \<open>(\<lambda>k. x (n + Suc k)) \<longlonglongrightarrow> l\<close>
        by simp
      hence \<open>(\<lambda> t. (\<lambda>k. x (n + k)) (Suc t)) \<longlonglongrightarrow> l\<close>
        by simp
      hence \<open>(\<lambda> t. (\<lambda>k. x (n + k)) t) \<longlonglongrightarrow> l\<close>
        by (rule LIMSEQ_imp_Suc)
      hence \<open>(\<lambda>k. x (n + k)) \<longlonglongrightarrow> l\<close>
        by simp
      thus ?thesis 
        by (simp add: \<open>(\<lambda>k. x (n + k)) \<longlonglongrightarrow> l\<close> Suc.IH)
    qed
    thus ?case by blast
  qed
  thus ?thesis
    using assms by blast 
qed

lemma identity_telescopic:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and l::'a and n::nat
  assumes \<open>x \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<longlonglongrightarrow> l - x n\<close>
proof-
  have \<open>sum (\<lambda> k. x (Suc k) - x k) {n..n+p} = x (Suc (n+p)) - x n\<close>
    for p
  proof(induction p)
    case 0
    thus ?case by simp
  next
    case (Suc p)
    thus ?case by simp
  qed
  moreover have \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) (n + t)  = (\<lambda> p. sum (\<lambda> k. x (Suc k) - x k) {n..n+p}) t\<close>
    for t
    by blast
  moreover have \<open>(\<lambda> p. x (Suc (n + p)) - x n)\<longlonglongrightarrow> l - x n\<close>
  proof-
    from \<open>x \<longlonglongrightarrow> l\<close>
    have \<open>(\<lambda> p. x (p + Suc n)) \<longlonglongrightarrow> l\<close>
      by (rule LIMSEQ_ignore_initial_segment)
    hence \<open>(\<lambda> p. x (Suc n + p)) \<longlonglongrightarrow> l\<close>   
      by (simp add: add.commute)
    have \<open>(\<lambda> p. x (Suc (n + p))) \<longlonglongrightarrow> l\<close>
    proof-
      have \<open>Suc n + p = Suc (n + p)\<close>
        for p
        by simp
      thus ?thesis using \<open>(\<lambda> p. x (Suc n + p)) \<longlonglongrightarrow> l\<close> by simp 
    qed
    hence \<open>(\<lambda> t. (- (x n)) + (\<lambda> p.  x (Suc (n + p))) t ) \<longlonglongrightarrow> (- (x n))  + l\<close>
      using tendsto_add_const_iff 
      by metis 
    thus ?thesis by simp
  qed
  ultimately have  \<open>(\<lambda> p. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) (n + p)) \<longlonglongrightarrow> l - x n\<close>
    by simp
  hence  \<open>(\<lambda> p. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) p) \<longlonglongrightarrow> l - x n\<close>
    by (rule lim_shift)
  hence  \<open>(\<lambda> M. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) M) \<longlonglongrightarrow> l - x n\<close>
    by simp
  thus ?thesis by blast
qed

lemma bound_telescopic:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and l::'a and n::nat and K::real
  assumes \<open>x \<longlonglongrightarrow> l\<close> and \<open>\<And> k. (sum (\<lambda> t. norm (x (Suc t) - x t)) {n..k}) \<le> K\<close>
  shows \<open>norm (l - x n) \<le> K\<close>
proof-
  have \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<longlonglongrightarrow> l - x n\<close>
    by (simp add: assms identity_telescopic)
  hence \<open>(\<lambda> N. norm (sum (\<lambda> k. x (Suc k) - x k) {n..N})) \<longlonglongrightarrow> norm (l - x n)\<close>
    using tendsto_norm by blast
  moreover have \<open>norm (sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<le> K\<close>
    for N
  proof-
    have \<open>norm (sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<le> sum (\<lambda> n. norm (x (Suc n) - x n)) {n..N}\<close>
      by (simp add: sum_norm_le)      
    also have \<open>... \<le> K \<close>
    proof-
      have \<open>sum (\<lambda> n. norm (x (Suc n) - x n)) {n..N}
               \<in> { (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..K})|K::nat. True}\<close>
        by blast
      moreover have \<open>bdd_above { (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..K})|K::nat. True}\<close>
        using  \<open>\<And> k. (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..k}) \<le> K\<close>
        by fastforce        
      ultimately have  \<open>sum (\<lambda> n. norm (x (Suc n) - x n)) {n..N} \<le> K\<close>
        using  \<open>\<And> k. (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..k}) \<le> K\<close>
        by blast
      thus ?thesis
        by (simp add: full_SetCompr_eq) 
    qed
    finally show ?thesis by blast
  qed
  ultimately show ?thesis
    using Lim_bounded by blast 
qed


lemma LIMSEQ_realpow_inf:
  fixes x :: real
  assumes \<open>x > 1\<close>
  shows  \<open>( \<lambda> n::nat. x^n) \<longlonglongrightarrow> \<infinity>\<close>
  using Limits.LIMSEQ_inverse_realpow_zero
  by (metis (mono_tags, lifting) Elementary_Topology.real_arch_pow Lim_PInfty assms le_ereal_le less_eq_ereal_def less_ereal.simps(1) power_increasing_iff) 

lemma LIMSEQ_scalarR: 
  fixes x :: \<open>nat \<Rightarrow> real\<close> and c :: real
  assumes \<open>x \<longlonglongrightarrow> \<infinity>\<close> and \<open>c > 0\<close>
  shows  \<open>(\<lambda> n::nat. c * (x n)) \<longlonglongrightarrow> \<infinity>\<close>
proof-
  have \<open>M \<ge> 0 \<Longrightarrow> \<exists> N. \<forall> n\<ge>N. c * x n \<ge> ereal M\<close>
    for M
  proof-
    assume \<open>M \<ge> 0\<close>
    hence \<open>(1/c) * M \<ge> 0\<close>
      using \<open>c > 0\<close>
      by auto
    from \<open>x \<longlonglongrightarrow> \<infinity>\<close>
    have \<open>\<exists> N. \<forall> n\<ge>N. x n \<ge> ereal ((1/c) * M)\<close>
      by (simp add: Lim_PInfty)
    hence \<open>\<exists> N. \<forall> n\<ge>N. c*(x n) \<ge> ereal M\<close>
      using \<open>c > 0\<close>
      by (simp add: mult.commute pos_divide_le_eq)
    thus ?thesis
      by blast 
  qed
  hence \<open>\<exists> N. \<forall> n\<ge>N. c * x n \<ge> ereal M\<close>
    for M
  proof(cases \<open>M \<ge> 0\<close>)
    case True
    thus ?thesis
      using \<open>\<And>M. 0 \<le> M \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. ereal M \<le> ereal (c * x n)\<close> by auto 
  next
    case False
    thus ?thesis
    proof -
      have "(0::real) \<le> 0"
        by auto
      then obtain nn :: "real \<Rightarrow> nat" where
        f1: "\<forall>n. \<not> nn 0 \<le> n \<or> ereal 0 \<le> ereal (c * x n)"
        by (meson \<open>\<And>M. 0 \<le> M \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. ereal M \<le> ereal (c * x n)\<close>)
      obtain nna :: "nat \<Rightarrow> nat" where
        "\<forall>x0. (\<exists>v1\<ge>x0. \<not> ereal M \<le> ereal (c * x v1)) = (x0 \<le> nna x0 \<and> \<not> ereal M \<le> ereal (c * x (nna x0)))"
        by moura
      moreover
      { assume "0 \<le> c * x (nna (nn 0))"
        hence "M + - 1 * (c * x (nna (nn 0))) \<le> 0"
          using False by linarith
        hence "\<exists>n. \<not> n \<le> nna n \<or> ereal M \<le> ereal (c * x (nna n))"
          by auto }
      ultimately show ?thesis
        using f1 ereal_less_eq(3) by blast
    qed 
  qed
  thus ?thesis 
    by (simp add: Lim_PInfty)
qed

subsubsection \<open>Cauchy sequences\<close>

lemma non_Cauchy_unbounded:
  fixes a ::\<open>nat \<Rightarrow> real\<close> and e::real
  assumes  \<open>\<And> n. a n \<ge> 0\<close> and \<open>e > 0\<close> and
    \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
  shows \<open>(\<lambda> n. (sum a  {0..n})) \<longlonglongrightarrow> \<infinity>\<close>
proof-
  have \<open>incseq (\<lambda> n. (sum a  {..<n}))\<close>
    using \<open>\<And> n. a n \<ge> 0\<close> using Extended_Real.incseq_sumI 
    by auto
  hence \<open>incseq (\<lambda> n. (sum a  {..< Suc n}))\<close>
    by (meson incseq_Suc_iff)
  hence \<open>incseq (\<lambda> n. (sum a  {0..n}))\<close>  
    by (simp add: sum_mono2 assms(1) incseq_def) 
  hence \<open>incseq (\<lambda> n. (sum a  {0..n})::ereal)\<close>
    using incseq_ereal by blast
  hence \<open>(\<lambda> n. (sum a  {0..n})::ereal) \<longlonglongrightarrow> Sup (range (\<lambda> n. (sum a  {0..n})::ereal))\<close>
    using LIMSEQ_SUP by auto
  moreover have \<open>Sup ((range (\<lambda> n. (sum a  {0..n})))::ereal set) = \<infinity>\<close>
  proof-
    define S where \<open>S = ((range (\<lambda> n. (sum a  {0..n})))::ereal set)\<close>
    have \<open>\<exists> s \<in> S.  k*e \<le> s\<close>
      for k::nat
    proof(induction k)
      case 0
      from \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
      obtain m n where \<open>m \<ge> 0\<close> and \<open>n \<ge> 0\<close> and \<open>m > n\<close>
        and \<open>sum a {Suc n..m} \<ge> e\<close>
        by blast
      from \<open>sum a {Suc n..m} \<ge> e\<close>
      have \<open>sum a {Suc n..m} > 0\<close>
        using \<open>e > 0\<close>
        by linarith
      moreover have \<open>sum a {0..n} \<ge> 0\<close>
        by (simp add: assms(1) sum_nonneg)
      moreover have \<open>sum a {0..n} + sum a {Suc n..m} = sum a {0..m}\<close>
      proof-
        have \<open>finite {0..n}\<close>
          by simp
        moreover have \<open>finite {Suc n..m}\<close>
          by simp
        moreover have \<open>{0..n} \<union> {Suc n..m} = {0..m}\<close>
        proof-
          have \<open>n < Suc n\<close>
            by simp
          thus ?thesis using Set_Interval.ivl_disj_un(7)
            using \<open>n < m\<close> by auto
        qed
        moreover have \<open>{0..n} \<inter> {Suc n..m} = {}\<close>
          by simp
        ultimately show ?thesis
          by (metis sum.union_disjoint) 
      qed
      ultimately have \<open>sum a {0..m} > 0\<close>
        by linarith
      moreover have \<open>ereal (sum a {0..m}) \<in> S\<close>
        unfolding S_def
        by blast
      ultimately have \<open>\<exists> s \<in> S. 0 \<le> s\<close>
        using ereal_less_eq(5) by fastforce    
      thus ?case
        by (simp add: zero_ereal_def)  
    next
      case (Suc k)
      assume \<open>\<exists>s\<in>S. ereal (real k * e) \<le> s\<close>
      then obtain s where \<open>s \<in> S\<close> 
        and \<open> ereal (real k * e) \<le> s\<close>
        by blast
      have \<open>\<exists> N. s = ereal (sum a {0..N})\<close>
        using \<open>s \<in> S\<close>
        unfolding S_def by blast
      then obtain N where \<open>s = ereal (sum a {0..N})\<close>
        by blast
      from \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
      obtain m n where \<open>m \<ge> Suc N\<close> and \<open>n \<ge> Suc N\<close> and \<open>m > n\<close>
        and \<open>sum a {Suc n..m} \<ge> e\<close>
        by blast
      have \<open>sum a {Suc N..m} \<ge> e\<close>
      proof-
        have \<open>sum a {Suc N..m} = sum a {Suc N..n} + sum a {Suc n..m}\<close>
        proof-
          have \<open>finite {Suc N..n}\<close>
            by simp
          moreover have \<open>finite {Suc n..m}\<close>
            by simp
          moreover have \<open>{Suc N..n} \<union> {Suc n..m} = {Suc N..m}\<close>
            using Set_Interval.ivl_disj_un
            by (smt \<open>Suc N \<le> n\<close> \<open>n < m\<close> atLeastSucAtMost_greaterThanAtMost less_imp_le_nat)
          moreover have \<open>{} = {Suc N..n} \<inter> {Suc n..m}\<close>
            by simp
          ultimately show ?thesis 
            by (metis sum.union_disjoint)
        qed
        moreover have \<open>sum a {Suc N..n} \<ge> 0\<close>
          using  \<open>\<And> n. a n \<ge> 0\<close>
          by (simp add: sum_nonneg) 
        ultimately show ?thesis
          using \<open>e \<le> sum a {Suc n..m}\<close> by linarith 
      qed
      moreover have \<open>sum a {0..N} + sum a {Suc N..m} =  sum a {0..m}\<close>
      proof-
        have \<open>finite {0..N}\<close>
          by simp
        have \<open>finite {Suc N..m}\<close>
          by simp
        moreover have \<open>{0..N} \<union> {Suc N..m} = {0..m}\<close>
        proof-
          have \<open>N < Suc N\<close>
            by simp
          thus ?thesis using Set_Interval.ivl_disj_un(7)
              \<open>Suc N \<le> m\<close> by auto            
        qed          
        moreover have \<open>{0..N} \<inter> {Suc N..m} = {}\<close>
          by simp
        ultimately show ?thesis 
          by (metis \<open>finite {0..N}\<close> sum.union_disjoint)
      qed
      ultimately have \<open>e + k * e \<le> sum a {0..m}\<close>
        using \<open>ereal (real k * e) \<le> s\<close> \<open>s = ereal (sum a {0..N})\<close> by auto
      moreover have \<open>e + k * e = (Suc k) * e\<close>
      proof-
        have \<open>e + k * e = (1 + k) * e\<close>
          by (simp add: semiring_normalization_rules(3))
        thus ?thesis by simp
      qed
      ultimately have \<open>(Suc k) * e \<le> sum a {0..m}\<close>
        by linarith
      hence \<open>ereal ((Suc k) * e) \<le> ereal (sum a {0..m})\<close>
        by auto
      moreover have \<open>ereal (sum a {0..m}) \<in> S\<close>
        unfolding S_def
        by blast
      ultimately show ?case
        by blast
    qed
    hence  \<open>\<exists> s \<in> S.  (real n) \<le> s\<close>
      for n::nat
      by (meson assms(2) ereal_le_le ex_less_of_nat_mult less_le_not_le)
    hence  \<open>Sup S = \<infinity>\<close>
      using Sup_le_iff Sup_subset_mono dual_order.strict_trans1 leD less_PInf_Ex_of_nat subsetI 
      by metis
    thus ?thesis using S_def 
      by blast
  qed
  ultimately show ?thesis 
    using PInfty_neq_ereal by auto 
qed

lemma sum_Cauchy_positive:
  fixes a ::\<open>nat \<Rightarrow> real\<close>
  assumes \<open>\<And> n. a n \<ge> 0\<close> 
    and \<open>\<exists> K. \<forall> n::nat. (sum a  {0..n}) \<le> K\<close>
  shows \<open>Cauchy (\<lambda> n. (sum a  {0..n}))\<close>
proof-
  have \<open>e>0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
    for e
  proof-
    assume \<open>e>0\<close>       
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
    proof(rule classical)
      assume \<open>\<not>(\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e)\<close>
      hence \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> \<not>(sum a {Suc n..m} < e)\<close>
        by blast
      hence \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
        by fastforce
      hence \<open>(\<lambda> n. (sum a  {0..n}) ) \<longlonglongrightarrow> \<infinity>\<close>
        using non_Cauchy_unbounded \<open>0 < e\<close> assms(1) by blast
      from  \<open>\<exists> K. \<forall> n::nat. (sum a  {0..n}) \<le> K\<close>
      obtain K where  \<open>\<forall> n::nat. (sum a  {0..n}) \<le> K\<close>
        by blast
      from  \<open>(\<lambda> n. (sum a  {0..n}) ) \<longlonglongrightarrow> \<infinity>\<close>
      have \<open>\<forall>B. \<exists>N. \<forall>n\<ge>N. (\<lambda> n. (sum a  {0..n}) ) n \<ge> ereal B\<close>
        using Lim_PInfty by simp
      hence  \<open>\<exists> n::nat. (sum a  {0..n}) \<ge> K+1\<close>
        using ereal_less_eq(3) by blast        
      thus ?thesis using  \<open>\<forall> n::nat. (sum a  {0..n}) \<le> K\<close> by smt       
    qed
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
    proof-
      have \<open>sum a {Suc n..m} = sum a {0..m} - sum a {0..n}\<close>
        if "m > n" for m n
        apply (simp add: that atLeast0AtMost)
        using that by (rule sum_interval_split)
      thus ?thesis using \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close> 
        by smt 
    qed
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
    proof-
      from \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
      obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
        by blast
      moreover have \<open>m > n \<Longrightarrow> sum a {0..m} \<ge> sum a {0..n}\<close>
        for m n
        using \<open>\<And> n. a n \<ge> 0\<close> 
        by (simp add: sum_mono2)
      ultimately show ?thesis 
        by auto
    qed
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m \<ge> n \<longrightarrow> \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
      by (metis \<open>0 < e\<close> abs_zero cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' less_irrefl_nat linorder_neqE_nat zero_less_diff)      
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
      by (metis abs_minus_commute nat_le_linear)
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
      by (simp add: dist_real_def)      
    thus ?thesis by blast
  qed
  thus ?thesis
    using Cauchy_altdef2 le_refl by fastforce 
qed

lemma convergent_series_Cauchy:
  fixes a::\<open>nat \<Rightarrow> real\<close> and \<phi>::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>\<exists> M. \<forall> n. (sum a {0..n}) \<le> M\<close>
    and \<open>\<And> n. dist (\<phi> (Suc n)) (\<phi> n) \<le> a n\<close>
  shows \<open>Cauchy \<phi>\<close>
proof-
  have \<open>e > 0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> dist (\<phi> m) (\<phi> n) < e\<close>
    for e
  proof-
    assume \<open>e > 0\<close>
    have \<open>dist (\<phi> (n+p+1)) (\<phi> n) \<le> sum a {n..n+p}\<close>
      for p n :: nat
    proof(induction p)
      case 0
      thus ?case
        by (simp add: assms(2))
    next
      case (Suc p)
      thus ?case
        by (smt Suc_eq_plus1 add_Suc_right assms(2) dist_self dist_triangle2 le_add1 sum.nat_ivl_Suc') 
    qed
    hence \<open>m > n \<Longrightarrow> dist (\<phi> m) (\<phi> n) \<le> sum a {n..m-1}\<close>
      for m n :: nat
      by (metis Suc_eq_plus1 Suc_le_D diff_Suc_1  gr0_implies_Suc less_eq_Suc_le less_imp_Suc_add zero_less_Suc)
    moreover have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {n..m-1} < e\<close>
    proof-
      have  \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
      proof-
        have \<open>\<And> k. a k \<ge> 0\<close>
          using \<open>\<And> n. dist (\<phi> (Suc n)) (\<phi> n) \<le> a n\<close>
            dual_order.trans zero_le_dist by blast
        hence \<open>Cauchy (\<lambda> k. sum a {0..k})\<close>
          using  \<open>\<exists> M. \<forall> n. (sum a {0..n}) \<le> M\<close>
            sum_Cauchy_positive by blast
        hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
          unfolding Cauchy_def
          using \<open>e > 0\<close>
          by blast
        hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> dist (sum a {0..m}) (sum a {0..n}) < e\<close>
          by blast
        have \<open>m > n \<Longrightarrow> dist (sum a {0..m}) (sum a {0..n}) = sum a {Suc n..m}\<close>
          for m n
        proof-
          assume \<open>m > n\<close>
          have \<open>dist (sum a {0..m}) (sum a {0..n}) 
            = \<bar>(sum a {0..m}) - (sum a {0..n})\<bar>\<close>
            using dist_real_def by blast
          moreover have \<open>(sum a {0..m}) - (sum a {0..n}) = sum a {Suc n..m}\<close>
          proof-
            have  \<open>(sum a {0..n}) + sum a {Suc n..m} = (sum a {0..m})\<close>
            proof-
              have \<open>finite {0..n}\<close>
                by simp
              moreover have \<open>finite {Suc n..m}\<close>
                by simp
              moreover have \<open>{0..n} \<union> {Suc n..m} = {0..m}\<close>
              proof-
                have \<open>n < Suc n\<close>
                  by simp
                thus ?thesis using  \<open>n < m\<close> by auto
              qed
              moreover have  \<open>{0..n} \<inter> {Suc n..m} = {}\<close>
                by simp
              ultimately show ?thesis
                by (metis sum.union_disjoint)
            qed
            thus ?thesis
              by linarith 
          qed
          ultimately show ?thesis
            by (simp add: \<open>\<And>k. 0 \<le> a k\<close> sum_nonneg) 
        qed
        thus ?thesis
          by (metis \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>) 
      qed  
      show ?thesis 
      proof-
        obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
          using \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. n < m \<longrightarrow> sum a {Suc n..m} < e\<close> by blast
        hence  \<open>\<forall>m. \<forall>n. Suc m \<ge> Suc M \<and> Suc n \<ge> Suc M \<and> Suc m > Suc n \<longrightarrow> sum a {Suc n..Suc m - 1} < e\<close>
          by simp
        hence  \<open>\<forall>m\<ge>1. \<forall>n\<ge>1. m \<ge> Suc M \<and> n \<ge> Suc M \<and> m > n \<longrightarrow> sum a {n..m - 1} < e\<close>
          by (metis Suc_le_D)
        thus ?thesis 
          by (meson add_leE)
      qed
    qed
    ultimately show ?thesis using \<open>e > 0\<close> by smt
  qed
  thus ?thesis
    using Cauchy_altdef2 by fastforce 
qed

subsubsection \<open>Convergence\<close>

text\<open>Pointwise convergence\<close>
definition pointwise_convergent_to :: 
  \<open>( nat \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) ) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> 
  (\<open>((_)/ \<midarrow>pointwise\<rightarrow> (_))\<close> [60, 60] 60) where
  \<open>pointwise_convergent_to x l = (\<forall> t::'a. (\<lambda> n. (x n) t) \<longlonglongrightarrow> l t)\<close>

lemma linear_limit_linear:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_vector \<Rightarrow> 'b::real_normed_vector)\<close>
    and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. linear (f n)\<close> and  \<open>f \<midarrow>pointwise\<rightarrow> F\<close>
  shows \<open>linear F\<close> 
proof
  have \<open>\<And> x. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
    using  \<open>f \<midarrow>pointwise\<rightarrow> F\<close>
    by (auto simp: pointwise_convergent_to_def)
  show "F (x + y) = F x + F y"
    for x :: 'a
      and y :: 'a
  proof-
    have \<open>(\<lambda> n. (f n) (x + y)) \<longlonglongrightarrow> F (x + y)\<close>
      by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>(\<lambda> n. (f n) y) \<longlonglongrightarrow> F y\<close>
      by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>lim (\<lambda> n. (f n) (x + y)) = lim (\<lambda> n. (f n) x) + lim (\<lambda> n. (f n) y)\<close> 
    proof-
      have \<open>(f n) (x + y) = (f n) x + (f n) y\<close>
        for n
        using \<open>\<And> n.  linear (f n)\<close>
        unfolding linear_def
        using Real_Vector_Spaces.linear_iff assms(1) by auto
      hence \<open>lim (\<lambda> n. (f n) (x + y)) = lim (\<lambda> n. (f n) x + (f n) y)\<close>
        by simp
      moreover have \<open>lim (\<lambda> n. (f n) x + (f n) y) = lim (\<lambda> n. (f n) x) + lim (\<lambda> n. (f n) y)\<close>
      proof-
        have \<open>convergent (\<lambda> n. (f n) x)\<close> 
          using \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> convergentI by auto
        moreover have \<open>convergent (\<lambda> n. (f n) y)\<close> 
          using \<open>(\<lambda> n. (f n) y) \<longlonglongrightarrow> F y\<close> convergentI by auto            
        ultimately show ?thesis
        proof -
          have f1: "\<forall>a. F a = lim (\<lambda>n. f n a)"
            by (metis (full_types)  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close> limI)
          have "\<forall>f b ba fa. (lim (\<lambda>n. fa n + f n) = (b::'b) + ba \<or> \<not> f \<longlonglongrightarrow> ba) \<or> \<not> fa \<longlonglongrightarrow> b"
            by (metis (no_types) limI tendsto_add)
          thus ?thesis
            using f1  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close> by fastforce
        qed 
      qed
      ultimately show ?thesis
        by simp  
    qed
    ultimately show ?thesis
      by (metis limI) 
  qed
  show "F (r *\<^sub>R x) = r *\<^sub>R F x"
    for r :: real
      and x :: 'a
  proof-
    have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      by (simp add:  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>(\<lambda> n.  (f n) (r *\<^sub>R x)) \<longlonglongrightarrow> F (r *\<^sub>R x)\<close>
      by (simp add:  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>lim (\<lambda> n.  (f n) (r *\<^sub>R x)) = r *\<^sub>R lim (\<lambda> n. (f n) x)\<close>
    proof-
      have \<open>(f n) (r *\<^sub>R x) = r *\<^sub>R (f n) x\<close>
        for n
        using  \<open>\<And> n.  linear (f n)\<close>
        unfolding linear_def
        unfolding Modules.additive_def
        by (simp add: Real_Vector_Spaces.linear_def real_vector.linear_scale)
      hence \<open>lim (\<lambda> n. (f n) (r *\<^sub>R x)) = lim (\<lambda> n. r *\<^sub>R (f n) x)\<close>
        by simp
      show ?thesis 
      proof-
        have \<open>convergent (\<lambda> n. (f n) x)\<close>
          using \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> convergentI by auto
        moreover have \<open>isCont (\<lambda> t::'b. r *\<^sub>R t) tt\<close>
          for tt
          by (simp add: bounded_linear_scaleR_right)
        ultimately have \<open>lim (\<lambda> n. r *\<^sub>R ((f n) x)) =  r *\<^sub>R lim (\<lambda> n. (f n) x)\<close>
          by (metis (mono_tags)  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close> isCont_tendsto_compose limI)
        thus ?thesis using  \<open>lim (\<lambda> n. (f n) (r *\<^sub>R x)) = lim (\<lambda> n. r *\<^sub>R (f n) x)\<close>
          by simp
      qed
    qed
    ultimately show ?thesis
      by (metis limI) 
  qed
qed

lemma bound_Cauchy_to_lim:
"\<lbrakk>y \<longlonglongrightarrow> x;  (\<And> n. norm (y (Suc n) - y n) \<le> c^n); y 0 = 0; c < 1\<rbrakk>
 \<Longrightarrow> norm (x - y (Suc n)) \<le> (c * inverse (1 - c)) * (c ^ n)"
proof-
  assume \<open>y \<longlonglongrightarrow> x\<close> and \<open>\<And> n. norm (y (Suc n) - y n) \<le> c^n\<close> and \<open>y 0 = 0\<close> and \<open>c < 1\<close>
  have \<open>c \<ge> 0\<close>
    using  \<open>\<And> n. norm (y (Suc n) - y n) \<le> c^n\<close> by (smt norm_imp_pos_and_ge power_Suc0_right)
  have \<open>(\<lambda> N. (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N})) \<longlonglongrightarrow> x - y (Suc n)\<close>
    by (metis (no_types) \<open>y \<longlonglongrightarrow> x\<close> identity_telescopic)
  hence \<open>(\<lambda> N. norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N})) \<longlonglongrightarrow> norm (x - y (Suc n))\<close>
    using tendsto_norm by blast
  moreover have \<open>norm (\<Sum>k = Suc n..N. y (Suc k) - y k) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close> for N
  proof(cases \<open>N < Suc n\<close>)
    case True
    hence \<open>norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}) = 0\<close>
      by auto
    thus ?thesis
      using  \<open>c \<ge> 0\<close> \<open>c < 1\<close> by auto       
  next
    case False
    hence \<open>N \<ge> Suc n\<close>
      by auto
    have \<open>norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N})
            \<le> (sum (\<lambda>k. norm (y (Suc k) - y k)) {Suc n .. N})\<close>
      by (simp add: sum_norm_le)
    also have \<open>\<dots> \<le> (sum (power c) {Suc n .. N})\<close>
      using \<open>\<And> n. norm (y (Suc n) - y n) \<le> c^n\<close>
      by (simp add: sum_mono) 
    finally have \<open>norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}) \<le> (sum (power c) {Suc n .. N})\<close>
      by blast
    moreover have \<open>1 - c > 0\<close>
      by (simp add: \<open>c < 1\<close>)      
    ultimately have \<open>(1 - c) * norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}) 
                   \<le> (1 - c) * (sum (power c) {Suc n .. N})\<close>
      by simp
    also have \<open>\<dots> = c^(Suc n) - c^(Suc N)\<close>
      using Set_Interval.sum_gp_multiplied \<open>Suc n \<le> N\<close> by blast
    also have \<open>\<dots> \<le> c^(Suc n)\<close>
    proof-
      have \<open>c^(Suc N) \<ge> 0\<close>
        using \<open>c \<ge> 0\<close> by auto
      thus ?thesis by auto
    qed
    finally have \<open>(1 - c) * norm (\<Sum>k = Suc n..N. y (Suc k) - y k) \<le> c ^ Suc n\<close>
      by blast
    moreover have \<open>inverse (1 - c) > 0\<close>
      using \<open>0 < 1 - c\<close> by auto      
    ultimately have \<open>(inverse (1 - c)) * ((1 - c) * norm (\<Sum>k = Suc n..N. y (Suc k) - y k) )
                   \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
      by auto
    moreover have \<open>(inverse (1 - c)) * ((1 - c) * norm (\<Sum>k = Suc n..N. y (Suc k) - y k) ) 
          = norm (\<Sum>k = Suc n..N. y (Suc k) - y k)\<close>
    proof-
      have \<open>inverse (1 - c) * (1 - c) = 1\<close>
        using \<open>0 < 1 - c\<close> by auto
      thus ?thesis by auto
    qed
    ultimately show \<open>norm (\<Sum>k = Suc n..N. y (Suc k) - y k) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
      by auto
  qed
  ultimately have \<open>norm (x - y (Suc n)) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
    using Lim_bounded by blast
  hence  \<open>norm (x - y (Suc n)) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
    by auto
  moreover have \<open> (inverse (1 - c)) * (c ^ Suc n) = (c * inverse (1 - c)) * (c ^ n)\<close>
    by auto
  ultimately show \<open>norm (x - y (Suc n)) \<le> (c * inverse (1 - c)) * (c ^ n)\<close>
    by linarith 
qed


end
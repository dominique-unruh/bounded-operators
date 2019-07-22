(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Complement of "HOL-Analysis.Operator_Norm".

*)

theory Operator_Norm_Missing
  imports 
    "HOL-Analysis.Infinite_Set_Sum"
    "HOL-Analysis.Operator_Norm"
    "HOL-ex.Sketch_and_Explore"
begin

section \<open>Sets defined using the norms\<close>

lemma ex_norm_1:
  \<open>(UNIV::('a::real_normed_vector) set) \<noteq> 0 \<Longrightarrow> \<exists> x::'a. norm x = 1\<close>
proof-
  assume \<open>(UNIV::('a::real_normed_vector) set) \<noteq> 0\<close>
  hence \<open>\<exists> x::'a.  x \<noteq> 0\<close>
    by auto
  then obtain t::'a where \<open>t \<noteq> 0\<close>
    by blast
  define x::'a where \<open>x = (inverse (norm t)) *\<^sub>R t\<close>
  have \<open>norm x = 1\<close>
    using x_def
    by (simp add: \<open>t \<noteq> 0\<close>)
  thus ?thesis
    by auto
qed


lemma norm_set_nonempty_eq1:
  fixes f :: \<open>'a::{real_normed_vector} \<Rightarrow> 'b::real_normed_vector\<close> 
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>bounded_linear f\<close>
  shows \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
proof-
  have \<open>\<exists> x::'a. x \<noteq> 0\<close>
    using  \<open>(UNIV::'a set) \<noteq> 0\<close> by auto
  hence \<open>\<exists> x::'a. norm x \<noteq> 0\<close>
    by simp
  hence \<open>\<exists> x::'a. norm x = 1\<close>
    by (metis (full_types) norm_sgn)
  thus ?thesis
    by simp 
qed

lemma norm_set_bdd_above_eq1: 
  fixes f :: \<open>('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> 
  assumes \<open>bounded_linear f\<close> 
  shows \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
proof-
  have \<open>\<exists> M. \<forall> x. norm x = 1 \<longrightarrow> norm (f x) \<le> M\<close>
    by (metis assms bounded_linear.bounded)
  thus ?thesis
    by auto 
qed

lemma norm_set_bdd_above_less1: 
  fixes f :: \<open>('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> 
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

section \<open>Characterization of the operator norm\<close>

lemma onorm_sphere:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and  \<open>bounded_linear f\<close>
  shows \<open>onorm f = Sup {norm (f x) | x. norm x = 1}\<close>
proof(cases \<open>f = (\<lambda> _. 0)\<close>)
  case True
  have \<open>onorm f = 0\<close>
    by (simp add: True onorm_eq_0)  
  moreover have \<open>Sup {norm (f x) | x. norm x = 1} = 0\<close>
  proof-
    have \<open>norm (f x) = 0\<close>
      for x
      by (simp add: True)      
    hence \<open>{norm (f x) | x. norm x = 1} = {0}\<close>
      using assms norm_set_nonempty_eq1 by fastforce
    thus ?thesis
      by simp 
  qed
  ultimately show ?thesis by simp
next
  case False
  thus ?thesis 
  proof-
    have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) | x. norm x = 1}\<close>
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
              by (metis (full_types) False assms(2) linear_simps(3) norm_sgn)              
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
            by (metis (lifting) \<open>0 \<le> Sup {norm (f x) |x. norm x = 1}\<close> \<open>bdd_above {0}\<close> \<open>bdd_above {norm (f x) |x. norm x = 1}\<close> \<open>{0} \<noteq> {}\<close> \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close> cSup_singleton cSup_union_distrib max.absorb_iff1 sup.absorb_iff1)
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
    thus ?thesis unfolding onorm_def by blast
  qed
qed

proposition operator_norm_characterization_1:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>bounded_linear f\<close>
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
        using assms(2) linear_simps(3) by fastforce        
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
          by (metis (full_types) False assms(2) linear_simps(3) norm_sgn)
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
            using  norm_set_nonempty_eq1 \<open>(UNIV::'a set) \<noteq> 0\<close> 
              \<open>bounded_linear f\<close> by blast 
          moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
            by (simp add: assms norm_set_bdd_above_eq1)            
          ultimately have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
            using Collect_empty_eq cSup_upper mem_Collect_eq
          proof -
            have "\<exists>r. (\<exists>a. r = norm (f a) \<and> norm a = 1) \<and> 0 \<le> r"
              using \<open>\<And>x. 0 \<le> norm (f x)\<close> \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close> by blast
            hence "\<exists>r. r \<in> {norm (f a) |a. norm a = 1} \<and> 0 \<le> r"
              by blast
            then show ?thesis
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
          using False \<open>y = norm (f x)\<close> assms norm_set_nonempty_eq1 by fastforce
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
            by (metis (full_types) False assms(2) linear_simps(3) norm_sgn)
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
          then show ?thesis
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


proposition operator_norm_characterization_2:
  fixes f :: \<open>'a::{real_normed_vector} \<Rightarrow> 'b::real_normed_vector\<close>
  assumes  \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>bounded_linear f\<close>
  shows  \<open>onorm f = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
proof-
  have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Inf {K. (\<forall>x\<noteq>0. norm (f x)/ norm x \<le>  K)}\<close>
  proof-
    define A where \<open>A = {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
    have \<open>A \<noteq> {}\<close>
    proof-
      have \<open>\<exists> x::'a. x \<noteq> 0\<close>
        using \<open>(UNIV::'a set) \<noteq> 0\<close> by auto
      thus ?thesis using A_def
        by simp 
    qed
    moreover have \<open>bdd_above A\<close>
    proof-
      have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
        using \<open>bounded_linear f\<close> le_onorm by auto
      thus ?thesis using A_def
        by auto 
    qed
    ultimately have \<open>Sup A = Inf {b. \<forall>a\<in>A. a \<le> b}\<close>
      using Complete_Lattices.complete_lattice_class.Sup_Inf
      by (simp add: cSup_cInf)  
    moreover have \<open>{b. \<forall>a\<in>A. a \<le> b} = {K. (\<forall>x\<noteq>0. norm (f x)/ norm x \<le>  K)}\<close>
    proof-
      have \<open>{b. \<forall>a\<in>A. a \<le> b} = {b. \<forall>a\<in>{norm (f x) / (norm x) | x. x \<noteq> 0}. a \<le> b}\<close>
        using A_def by blast
      also have \<open>... = {b. \<forall>x\<in>{x | x. x \<noteq> 0}. norm (f x) / (norm x) \<le> b}\<close>
        by auto
      also have \<open>... = {b. \<forall>x\<noteq>0. norm (f x) / (norm x) \<le> b}\<close>
        by auto
      finally show ?thesis by blast
    qed
    ultimately show ?thesis 
      using A_def
      by simp 
  qed
  moreover have \<open>(\<forall>x\<noteq>0. norm (f x) \<le> norm x * K) \<longleftrightarrow> (\<forall>x\<noteq>0. norm (f x)/ norm x \<le> K)\<close>
    for K
  proof
    show "\<forall>x\<noteq>0. norm (f x) / norm x \<le> K"
      if "\<forall>x\<noteq>0. norm (f x) \<le> norm x * K"
      using divide_le_eq nonzero_mult_div_cancel_left norm_le_zero_iff that
      by (simp add: divide_le_eq mult.commute)

    show "\<forall>x\<noteq>0. norm (f x) \<le> norm x * K"
      if "\<forall>x\<noteq>0. norm (f x) / norm x \<le> K"
      using divide_le_eq nonzero_mult_div_cancel_left norm_le_zero_iff that
      by (simp add: divide_le_eq mult.commute)
  qed
  ultimately have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
    by simp
  moreover have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Sup {norm (f x) / (norm x) | x. True}\<close>
  proof-
    have \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0}  = {norm (f x) / (norm x) | x. True}\<close>
      using Collect_cong by blast
    hence \<open>Sup ({norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0}) = Sup {norm (f x) / (norm x) | x. True}\<close>
      by simp
    moreover have \<open>Sup ({norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0})
        = max (Sup {norm (f x) / (norm x) | x. x \<noteq> 0}) (Sup {norm (f x) / (norm x) | x. x = 0})\<close>
    proof-
      have \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<noteq> {}\<close>
      proof-
        have \<open>\<exists> x::'a. x \<noteq> 0\<close>
          using \<open>(UNIV::'a set)\<noteq>0\<close> by auto
        thus ?thesis
          by simp 
      qed
      moreover have \<open>bdd_above {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
      proof-
        have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
          using \<open>bounded_linear f\<close>
          by (metis \<open>\<And>K. (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) \<le> norm x * K) = (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) / norm x \<le> K)\<close> bounded_linear.nonneg_bounded mult_divide_mult_cancel_left_if norm_zero real_divide_square_eq)
        thus ?thesis
          by auto 
      qed
      moreover have \<open>{norm (f x) / (norm x) | x. x = 0} \<noteq> {}\<close>
        by simp
      moreover have \<open>bdd_above {norm (f x) / (norm x) | x. x = 0}\<close>
        by simp
      ultimately show ?thesis
        by (metis (no_types, lifting) cSup_union_distrib sup_max)  
    qed      
    moreover have \<open>Sup {norm (f x) / (norm x) | x. x = 0} = 0\<close>
    proof-
      have \<open>{norm (f x) / (norm x) | x. x = 0} = {norm (f 0) / (norm 0)}\<close>
        by simp
      thus ?thesis
        by simp 
    qed
    moreover have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} \<ge> 0\<close>
    proof-
      have \<open>norm (f x) / (norm x) \<ge> 0\<close>
        for x
        by simp
      hence \<open>\<forall> y\<in>{norm (f x) / (norm x) | x. x \<noteq> 0}. y \<ge> 0\<close>
        by blast
      moreover have \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<noteq> {}\<close>
      proof-
        have \<open>\<exists> x::'a. x \<noteq> 0\<close>
          using \<open>(UNIV::'a set)\<noteq>0\<close> by auto
        thus ?thesis 
         by auto
      qed
      moreover have \<open>bdd_above {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
      proof-
        have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
          using \<open>bounded_linear f\<close>
          by (metis \<open>\<And>K. (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) \<le> norm x * K) = (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) / norm x \<le> K)\<close> bounded_linear.nonneg_bounded mult_divide_mult_cancel_left_if norm_zero real_divide_square_eq)
        thus ?thesis
          by auto 
      qed
      ultimately show ?thesis
        by (metis (lifting) \<open>\<forall>y\<in>{norm (f x) / norm x |x. x \<noteq> 0}. 0 \<le> y\<close> \<open>bdd_above {norm (f x) / norm x |x. x \<noteq> 0}\<close> \<open>{norm (f x) / norm x |x. x \<noteq> 0} \<noteq> {}\<close> bot.extremum_uniqueI cSup_upper2 subset_emptyI)        
    qed
    ultimately show ?thesis
      by linarith 
  qed
  ultimately have \<open>(SUP x. norm (f x) / (norm x)) = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
    by (simp add: full_SetCompr_eq)
  thus ?thesis
    by (simp add: onorm_def)
qed

lemma operation_norm_closed:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close>
  shows \<open>closed { K | K::real. \<forall>x. norm (f x) \<le> norm x * K}\<close>
proof-
  have \<open>\<forall> n. (k n) \<in> { K | K::real. \<forall>x. norm (f x) \<le> norm x * K}
    \<Longrightarrow> k \<longlonglongrightarrow> l 
    \<Longrightarrow> l \<in> { K | K::real. \<forall>x. norm (f x) \<le> norm x * K}\<close>
    for k and l
  proof-
    assume \<open>\<forall> n. (k n) \<in> { K | K::real. \<forall>x. norm (f x) \<le> norm x * K}\<close>
    hence \<open>\<forall> n. norm (f x) \<le> norm x * (k n)\<close>
      for x
      by blast
    assume \<open>k \<longlonglongrightarrow> l\<close>
    have \<open>norm (f x) \<le> norm x * l\<close>
      for x
    proof-
      have  \<open>\<forall> n. norm (f x) \<le> norm x * (k n)\<close>
        by (simp add: \<open>\<And>x. \<forall>n. norm (f x) \<le> norm x * k n\<close>)
      moreover have \<open>(\<lambda> n.  norm x * (k n) ) \<longlonglongrightarrow> norm x * l\<close>
        using  \<open>k \<longlonglongrightarrow> l\<close>
        by (simp add: tendsto_mult_left)
      ultimately show ?thesis
        using Topological_Spaces.Lim_bounded2
        by fastforce
    qed
    thus ?thesis
      by simp  
  qed
  thus ?thesis
    by (meson closed_sequential_limits) 
qed

section \<open>Banach-Steinhaus theorem\<close>

lemma norm_ball:
  fixes f :: \<open>'a::{real_normed_vector} \<Rightarrow> 'b::real_normed_vector\<close>
    and  r :: real
  assumes \<open>r > 0\<close> and \<open>bounded_linear f\<close>
  shows  \<open>onorm f  = (1/r) * Sup {norm (f x) | x. norm x < r}\<close>
proof (cases \<open>(UNIV::'a set) = 0\<close>)
  case True
  have \<open>f 0 = 0\<close>
    using \<open>bounded_linear f\<close>
    by (simp add: linear_simps(3))
  moreover have \<open>x = 0\<close>
    for x::'a
    using \<open>(UNIV::'a set) = 0\<close>
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
  moreover have \<open>(1/r) * Sup {norm (f x) | x. norm x < r} = Sup {norm (f x) | x. norm x < 1}\<close>
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
        then have "rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * ra |ra. ra \<in> S} \<longrightarrow> rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) = 1 / r * norm (f (aa (rra (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r)))))"
          using f3 by presburger
        then have f5: "rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<notin> {1 / r * ra |ra. ra \<in> S} \<or> rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * norm (f a) |a. norm a < r}"
          using f4 f2 by blast
        obtain aaa :: "real \<Rightarrow> 'a" where
          f6: "(rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<notin> {1 / r * norm (f a) |a. norm a < r} \<or> rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) = 1 / r * norm (f (aaa (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r)))) \<and> \<not> r + - 1 * norm (aaa (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r))) \<le> 0) \<and> (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * norm (f a) |a. norm a < r} \<or> (\<forall>a. rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<noteq> 1 / r * norm (f a) \<or> r + - 1 * norm a \<le> 0))"
          by moura
        have "(rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<notin> {1 / r * norm (f a) |a. norm a < r}) = (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * ra |ra. ra \<in> S}) \<longrightarrow> (\<forall>a. norm (f (aaa (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r)))) \<noteq> norm (f a) \<or> r + - 1 * norm a \<le> 0)"
          using S_def by blast
        then have "(rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<notin> {1 / r * norm (f a) |a. norm a < r}) \<noteq> (rr (\<lambda>ra. \<exists>rb. ra = 1 / r * rb \<and> rb \<in> S) (\<lambda>ra. \<exists>a. ra = 1 / r * norm (f a) \<and> norm a < r) \<in> {1 / r * ra |ra. ra \<in> S})"
          using f6 f5 by blast
        then have "{1 / r * norm (f a) |a. norm a < r} = {1 / r * ra |ra. ra \<in> S}"
          using f1 by meson
        then show ?thesis
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
  ultimately show ?thesis
    using False operator_norm_characterization_1 
      \<open>bounded_linear f\<close>
    by auto
qed

(* TODO: replace in a better place *)
lemma Sup_Ineq:
  fixes f g :: \<open>'a \<Rightarrow> real\<close>
  assumes \<open>\<forall> x \<in> S. f x \<le> g x\<close>
    and \<open>bdd_above (g ` S)\<close>
  shows \<open>Sup (f ` S) \<le> Sup (g ` S)\<close>
proof-
  have  \<open>y \<in> (f ` S) \<Longrightarrow> y \<le> Sup (g ` S)\<close>
    for y
  proof-
    assume \<open>y \<in> (f ` S)\<close>
    hence \<open>\<exists> x\<in>S. y = f x\<close>
      by blast
    then obtain x where \<open>y = f x\<close> and \<open>x \<in> S\<close>
      by blast
    hence \<open>y \<le> g x\<close>
      using  \<open>\<forall> x \<in> S. f x \<le> g x\<close> \<open>x \<in> S\<close>
      by blast
    have \<open>g x \<in> (g ` S)\<close>
      by (simp add: \<open>x \<in> S\<close>)
    hence \<open>g x \<le> Sup (g ` S)\<close>
      using \<open>bdd_above (g ` S)\<close>
      by (simp add: cSup_upper)
    thus ?thesis using \<open>y \<le> g x\<close> by simp
  qed
  hence \<open>Sup (f ` S) \<le> Sup (g ` S)\<close>
    by (metis assms(1) assms(2) cSUP_subset_mono image_empty order_refl)
  thus ?thesis
    by simp 
qed

text \<open>The proof of the following result was taken from [sokal2011really]\<close>
lemma sokal_banach_steinhaus:
  fixes f :: \<open>'a::{real_normed_vector} \<Rightarrow> 'b::real_normed_vector\<close>
    and r :: real and x :: 'a 
  assumes \<open>r > 0\<close> and \<open>bounded_linear f\<close>
  shows \<open>(onorm f) * r \<le> Sup {norm (f y) | y. dist y x < r}\<close>
proof-
  have \<open>norm (f \<xi>) \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>
    for \<xi>
  proof-
    from  \<open>bounded_linear f\<close>
    have \<open>linear f\<close>
      unfolding bounded_linear_def
      by blast
    hence \<open>Modules.additive f\<close>
      by (simp add: Modules.additive_def linear_add)
    have homogeneous: "f (r *\<^sub>R x) = r  *\<^sub>R (f x)"
      for r and x
      by (simp add: \<open>linear f\<close> linear.scaleR)
    have \<open>2 *\<^sub>R \<xi> = (x + \<xi>) - (x - \<xi>)\<close>
      by (simp add: scaleR_2)
    hence \<open>f (2 *\<^sub>R \<xi>) = f ((x + \<xi>) - (x - \<xi>))\<close>
      by simp
    moreover have \<open>f (2 *\<^sub>R \<xi>) = 2 *\<^sub>R (f \<xi>)\<close>
      using homogeneous
      by (simp add: \<open>Modules.additive f\<close> additive.add scaleR_2)    
    moreover have \<open>f ((x + \<xi>) - (x - \<xi>)) = f (x + \<xi>) - f (x - \<xi>)\<close>
      using \<open>Modules.additive f\<close> additive.diff by blast
    ultimately have \<open>2 *\<^sub>R (f \<xi>) = f (x + \<xi>) - f (x - \<xi>)\<close>
      by simp
    hence \<open>(f \<xi>) = (1/2) *\<^sub>R (f (x + \<xi>) - f (x - \<xi>))\<close>
      by (metis scaleR_2 scaleR_half_double)
    hence \<open>norm (f \<xi>) = norm ( (1/2) *\<^sub>R (f (x + \<xi>) - f (x - \<xi>)) )\<close>
      by simp
    moreover have \<open>norm ( (1/2) *\<^sub>R (f (x + \<xi>) - f (x - \<xi>)) )
               = ((1/2)::real) * ( norm (f (x + \<xi>) - f (x - \<xi>)) )\<close>
      by simp          
    ultimately have \<open>norm (f \<xi>) = ((1/2)::real) * norm (f (x + \<xi>) - f (x - \<xi>))\<close>
      by simp
    moreover have \<open>norm (f (x + \<xi>) - f (x - \<xi>)) \<le> norm (f (x + \<xi>)) + norm (f (x - \<xi>))\<close>
      by (simp add: norm_triangle_ineq4)
    ultimately have \<open>norm (f \<xi>) \<le> ((1/2)::real) * (norm (f (x + \<xi>)) + norm (f (x - \<xi>)))\<close>
      by simp
    moreover have \<open>(norm (f (x + \<xi>)) + norm (f (x - \<xi>))) 
        \<le> 2 * max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>  
    proof(cases \<open>norm (f (x + \<xi>)) \<le> norm (f (x - \<xi>))\<close>)
      case True
      have \<open>(norm (f (x + \<xi>)) + norm (f (x - \<xi>))) \<le> 2*norm (f (x - \<xi>))\<close>
        using True by auto    
      moreover have \<open>norm (f (x - \<xi>)) \<le> Max { norm (f (x + \<xi>)),  norm (f (x - \<xi>))}\<close>
        using True by simp
      ultimately show ?thesis
        by linarith 
    next
      case False
      have \<open>(norm (f (x + \<xi>)) + norm (f (x - \<xi>))) \<le> 2*norm (f (x + \<xi>))\<close>
        using False by auto    
      moreover have \<open>norm (f (x + \<xi>)) \<le> max (norm (f (x + \<xi>)))  (norm (f (x - \<xi>)))\<close>
        using False by simp
      ultimately show ?thesis
        by simp 
    qed
    ultimately show ?thesis
      by simp 
  qed
  define u where \<open>u \<xi> = norm (f \<xi>)\<close>
    for \<xi>
  define v where \<open>v \<xi> = max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>
    for \<xi>
  define S where \<open>S = Collect (\<lambda> \<xi>::'a. norm \<xi> < r)\<close>
  have \<open>bdd_above (v ` S)\<close>
  proof-
    have \<open>\<xi> \<in> S \<Longrightarrow> u \<xi> \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>
      for \<xi>
      by (simp add: \<open>\<And>\<xi>. norm (f \<xi>) \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close> \<open>u \<equiv> \<lambda>\<xi>. norm (f \<xi>)\<close>)
    moreover have \<open>norm (f (x + \<xi>)) \<le> (onorm f) * (norm x + norm \<xi>)\<close>
      for \<xi>
    proof-
      have \<open>norm (f (x + \<xi>)) \<le> (onorm f) * (norm (x + \<xi>))\<close>
        by (simp add: assms(2) onorm)        
      moreover have \<open>norm (x + \<xi>) \<le> norm x + norm \<xi>\<close>
        by (simp add: norm_triangle_ineq)        
      moreover have \<open>onorm f \<ge> 0\<close>
        by (simp add: assms(2) onorm_pos_le)        
      ultimately show ?thesis
        using mult_left_mono by fastforce
    qed
    moreover have \<open>norm (f (x - \<xi>)) \<le> (onorm f) * (norm x + norm \<xi>)\<close>
      for \<xi>
      by (metis (no_types, hide_lams) add_diff_cancel add_diff_eq calculation(2) norm_minus_commute)
    ultimately have \<open>\<xi> \<in> S \<Longrightarrow> v \<xi> \<le> (onorm f) * (norm x + norm \<xi>)\<close>
      for \<xi>
      by (simp add: \<open>v \<equiv> \<lambda>\<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>)
    moreover have \<open>\<xi> \<in> S \<Longrightarrow> norm \<xi> \<le> r\<close>
      for \<xi>
      by (simp add: S_def)      
    moreover have \<open>onorm f \<ge> 0\<close>
      by (simp add: assms(2) onorm_pos_le)      
    ultimately have \<open>\<xi> \<in> S \<Longrightarrow> v \<xi> \<le> (onorm f) * (norm x + r)\<close>
      for \<xi>
    proof-
      assume \<open>\<xi> \<in> S\<close>
      have \<open>v \<xi> \<le> (onorm f) * (norm x + norm \<xi>)\<close>
        by (simp add: \<open>\<And>\<xi>. \<xi> \<in> S \<Longrightarrow> v \<xi> \<le> onorm f * (norm x + norm \<xi>)\<close> \<open>\<xi> \<in> S\<close>)
      moreover have \<open>(onorm f) * (norm x + norm \<xi>) \<le> (onorm f) * (norm x + r)\<close>
      proof-
        have \<open>norm \<xi> \<le> r\<close>
          by (simp add: \<open>\<And>\<xi>. \<xi> \<in> S \<Longrightarrow> norm \<xi> \<le> r\<close> \<open>\<xi> \<in> S\<close>)
        hence \<open>norm x + norm \<xi> \<le> norm x + r\<close>
          by simp
        thus ?thesis using \<open>onorm f \<ge> 0\<close>
          by (simp add: mult_left_mono) 
      qed
      ultimately show ?thesis 
        using mult_left_mono
        by simp
    qed
    thus ?thesis
      by (meson bdd_aboveI2) 
  qed
  hence \<open>Sup (u ` S) \<le> Sup (v ` S)\<close>
    using Sup_Ineq \<open>\<And> \<xi>. norm (f \<xi>) \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>
    by (simp add: Sup_Ineq \<open>u \<equiv> \<lambda>\<xi>. norm (f \<xi>)\<close> \<open>v \<equiv> \<lambda>\<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>)    
  moreover have \<open>Sup (u ` S) = (onorm f) * r\<close>
  proof-
    have \<open>onorm f = (1/r) * Sup {norm (f x) | x. norm x < r}\<close>
      using assms(1) assms(2) norm_ball by auto
    hence  \<open> Sup {norm (f x) | x. norm x < r} = onorm f * r\<close>
      using assms(1) by auto
    moreover have \<open>Sup {norm (f x) |x. norm x < r} = (SUP \<xi>\<in>{\<xi>. norm \<xi> < r}. norm (f \<xi>))\<close>
      by (simp add: setcompr_eq_image)
    ultimately show ?thesis unfolding S_def u_def by simp
  qed
  moreover have \<open>Sup (v ` S) = Sup {norm (f y) | y. dist y x < r }\<close>
  proof-
    have \<open>Sup (v ` S) \<le> Sup {norm (f y) | y. dist y x < r }\<close>
    proof-
      have \<open>y \<in> v ` S \<Longrightarrow> y \<in> {norm (f y) | y. dist y x < r }\<close>
        for y
      proof-
        assume \<open>y \<in> v ` S\<close>
        hence \<open>\<exists> t \<in> S. y = v t\<close>
          by blast
        then obtain t where \<open>y = v t\<close>
          by blast
        hence \<open>y = max (norm (f (x + t))) (norm (f (x - t)))\<close>
          unfolding v_def by blast
        show ?thesis
        proof(cases \<open>y = (norm (f (x + t)))\<close>)
          case True
          thus ?thesis
          proof -
            have "\<exists>a. a \<in> S \<and> y = v a"
              by (metis \<open>\<exists>t\<in>S. y = v t\<close>)
            then obtain aa :: 'a where
              f1: "aa \<in> S \<and> y = (if norm (f (x + aa)) + - 1 * norm (f (x - aa)) \<le> 0 then norm (f (x - aa)) else norm (f (x + aa)))"
              using \<open>v \<equiv> \<lambda>\<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close> by moura
            then have f2: "aa \<in> {a. norm a < r}"
              by (metis S_def)
            have "norm aa = dist (x + aa) x"
              by (metis (full_types) add_diff_cancel_right' dist_diff(1))
            then show ?thesis
              using f2 f1 by auto
          qed            
        next
          case False
          hence  \<open>y = (norm (f (x - t)))\<close>
            using \<open>y = max (norm (f (x + t))) (norm (f (x - t)))\<close> by linarith
          thus ?thesis
          proof -
            obtain aa :: 'a where
              f1: "aa \<in> S \<and> y = (if norm (f (x + aa)) + - 1 * norm (f (x - aa)) \<le> 0 then norm (f (x - aa)) else norm (f (x + aa)))"
              using \<open>\<exists>t\<in>S. y = v t\<close> \<open>v \<equiv> \<lambda>\<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close> by moura
            then have f2: "aa \<in> {a. norm a < r}"
              using S_def by blast
            have "norm aa = dist (x + aa) x"
              by (metis add_diff_cancel_right' dist_diff(1))
            then have "\<exists>a. norm (f (x - t)) = norm (f a) \<and> \<not> r + - 1 * dist a x \<le> 0"
              using f2 f1 \<open>y = norm (f (x - t))\<close> by force
            then show ?thesis
              using \<open>y = norm (f (x - t))\<close> by force
          qed
        qed
      qed
      hence \<open>(v ` S) \<subseteq> {norm (f y) | y. dist y x < r }\<close>
        by blast
      moreover have \<open>bdd_above {norm (f y) | y. dist y x < r }\<close>
      proof-
        have \<open>dist t x < r \<Longrightarrow> norm (f t) \<le> onorm f * (r + norm x)\<close>
          for t
        proof-
          assume \<open>dist t x < r\<close>
          show ?thesis
          proof-
            have \<open>norm (f t) \<le> onorm f * norm t\<close>
              using \<open>bounded_linear f\<close>
              by (simp add: onorm)
            have \<open>norm t \<le> norm x + norm (t - x)\<close>
              by (simp add: norm_triangle_sub)
            from \<open>dist t x < r\<close>
            have \<open>norm (t - x) < r\<close>
              by (simp add: dist_norm) 
            have \<open>onorm f \<ge> 0\<close>
              using assms(2) onorm_pos_le by auto
            hence \<open>norm (f t) \<le> onorm f * (norm x + norm (t - x))\<close>
              using \<open>norm (f t) \<le> onorm f * norm t\<close> \<open>norm t \<le> norm x + norm (t - x)\<close> mult_left_mono by fastforce
            have \<open>norm x + norm (t - x) < norm x + r\<close>
              by (simp add: \<open>norm (t - x) < r\<close>)
            hence \<open>norm x + norm (t - x) \<le> norm x + r\<close>
              by simp
            hence \<open>onorm f * (norm x + norm (t - x)) \<le> onorm f * (norm x + r)\<close>
              using \<open>0 \<le> onorm f\<close> mult_left_mono by blast
            hence \<open>norm (f t) \<le> onorm f * (norm x + r)\<close>
              using \<open>norm (f t) \<le> onorm f * (norm x + norm (t - x))\<close> by auto              
            thus \<open>norm (f t) \<le> onorm f * (r + norm x)\<close>
              by (simp add: add.commute)                             
          qed
        qed
        thus ?thesis
          by fastforce 
      qed
      moreover have \<open>{norm (f y) | y. dist y x < r } \<noteq> {}\<close>
        by (metis S_def assms(1) bot.extremum_uniqueI calculation(1) empty_iff image_is_empty mem_Collect_eq norm_zero)
      ultimately show ?thesis
        by (metis (no_types, lifting) Collect_empty_eq S_def assms(1) cSup_subset_mono empty_is_image norm_zero)  
    qed
    have \<open>y \<in> {norm (f y) | y. dist y x < r } \<Longrightarrow> y \<le> Sup (v ` S)\<close>
      for y
    proof-
      assume \<open>y \<in> {norm (f y) | y. dist y x < r }\<close>
      hence \<open>\<exists> t. y = norm (f t) \<and> dist t x < r\<close>
        by blast
      then obtain t where \<open>y = norm (f t)\<close> and \<open>dist t x < r\<close>
        by blast
      define \<xi> where \<open>\<xi> = t - x\<close>
      have \<open>norm \<xi> < r\<close>
        using  \<open>dist t x < r\<close> \<xi>_def
        by (simp add: dist_norm)
      have \<open>v ` S = {max (norm (f (x + \<xi>))) (norm (f (x - \<xi>))) | \<xi>. norm \<xi> < r}\<close>
        using v_def S_def
        by auto
      have \<open>norm (f (x + \<xi>)) \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>
        for \<xi>
        by auto
      moreover have \<open>max (norm (f (x + \<xi>))) (norm (f (x - \<xi>))) \<le> Sup {max (norm (f (x + \<xi>))) (norm (f (x - \<xi>))) | \<xi>. norm \<xi> < r}\<close>
      proof-
        have \<open>(v ` S) \<noteq> {}\<close>
          unfolding  S_def 
          using \<open>norm \<xi> < r\<close> by auto
        thus ?thesis using  \<open>bdd_above (v ` S)\<close>   \<open>v ` S = {max (norm (f (x + \<xi>))) (norm (f (x - \<xi>))) | \<xi>. norm \<xi> < r}\<close>
          by (metis S_def \<open>norm \<xi> < r\<close> cSUP_upper mem_Collect_eq v_def)
      qed
      ultimately show ?thesis
        using S_def \<open>bdd_above (v ` S)\<close> \<open>norm \<xi> < r\<close> \<open>v \<equiv> \<lambda>\<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close> \<open>y = norm (f t)\<close> \<xi>_def cSUP_upper2 by fastforce 
    qed
    moreover have  \<open>{norm (f y) | y. dist y x < r } \<noteq> {}\<close>
    proof -
      have "\<exists>ra a. ra = norm (f a) \<and> dist a x < r"
        by (metis (full_types) assms(1) dist_eq_0_iff)
      thus ?thesis
        by blast
    qed
    moreover have \<open>bdd_above {norm (f y) | y. dist y x < r }\<close>
    proof-
      have \<open>dist t x < r \<Longrightarrow> norm (f t) \<le> onorm f * (r + norm x)\<close>
        for t
      proof-
        assume \<open>dist t x < r\<close>
        have \<open>norm (f t) \<le> onorm f * norm t\<close>
          using \<open>bounded_linear f\<close>
          by (simp add: onorm)
        moreover have \<open>norm t \<le> norm x + norm (t - x)\<close>
          by (simp add: norm_triangle_sub)
        ultimately show ?thesis 
        proof-
          have \<open>norm (f t) \<le> onorm f * norm t\<close>
            using \<open>bounded_linear f\<close>
            by (simp add: onorm)
          have \<open>norm t \<le> norm x + norm (t - x)\<close>
            by (simp add: norm_triangle_sub)
          from \<open>dist t x < r\<close>
          have \<open>norm (t - x) < r\<close>
            by (simp add: dist_norm) 
          have \<open>onorm f \<ge> 0\<close>
            using assms(2) onorm_pos_le by auto
          hence \<open>norm (f t) \<le> onorm f * (norm x + norm (t - x))\<close>
            using \<open>norm (f t) \<le> onorm f * norm t\<close> \<open>norm t \<le> norm x + norm (t - x)\<close> mult_left_mono by fastforce
          have \<open>norm x + norm (t - x) < norm x + r\<close>
            by (simp add: \<open>norm (t - x) < r\<close>)
          hence \<open>norm x + norm (t - x) \<le> norm x + r\<close>
            by simp
          hence \<open>onorm f * (norm x + norm (t - x)) \<le> onorm f * (norm x + r)\<close>
            using \<open>0 \<le> onorm f\<close> mult_left_mono by blast
          hence \<open>norm (f t) \<le> onorm f * (norm x + r)\<close>
            using \<open>norm (f t) \<le> onorm f * (norm x + norm (t - x))\<close> by auto              
          thus \<open>norm (f t) \<le> onorm f * (r + norm x)\<close>
            by (simp add: add.commute)                             
        qed
      qed
      thus ?thesis
        by fastforce 
    qed
    ultimately have \<open>Sup {norm (f y) |y. dist y x < r} \<le> Sup (v ` S)\<close>
    proof -
      assume "\<And>y. y \<in> {norm (f y) |y. dist y x < r} \<Longrightarrow> y \<le> Sup (v ` S)"
      then show ?thesis
        by (metis (lifting) \<open>{norm (f y) |y. dist y x < r} \<noteq> {}\<close> cSup_least)
    qed 
    thus ?thesis
      using \<open>Sup (v ` S) \<le> Sup {norm (f y) |y. dist y x < r}\<close>
      by linarith      
  qed
  thus ?thesis
    using calculation(1) calculation(2) by auto 
qed

lemma bounded_linear_ball:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
    and K :: real
  assumes \<open>linear f\<close> and \<open>\<And> x. norm x = 1 \<Longrightarrow> norm (f x) \<le> K\<close>
  shows \<open>bounded_linear f\<close>
proof-
  have \<open>norm (f x) \<le> norm x * K\<close>
    for x
  proof(cases \<open>x = 0\<close>)
    case True
    thus ?thesis
      by (simp add: assms(1) linear_0) 
  next
    case False
    hence \<open>norm x > 0\<close>
      by simp
    hence \<open>norm (inverse (norm x) *\<^sub>R x) = 1\<close>
      by auto
    hence \<open>norm (f (inverse (norm x) *\<^sub>R x)) \<le> K\<close>
      using \<open>\<And> x. norm x = 1 \<Longrightarrow> norm (f x) \<le> K\<close>
      by blast
    hence \<open>norm (inverse (norm x) *\<^sub>R  (f x)) \<le> K\<close>
      by (simp add: assms(1) linear_scale)
    hence \<open>\<bar>inverse (norm x)\<bar> * norm (f x) \<le> K\<close>
      by simp
    hence \<open>inverse (norm x) * norm (f x) \<le> K\<close>
      using \<open>norm x > 0\<close>
      by simp
    show ?thesis 
    proof-
      have \<open>inverse (norm x) \<ge> 0\<close>
        using \<open>norm x > 0\<close>
        by simp
      moreover have \<open>norm (f x) \<ge> 0\<close>
        by simp
      moreover have \<open>K \<ge> 0\<close>
        using \<open>inverse (norm x) * norm (f x) \<le> K\<close> \<open>inverse (norm x) \<ge> 0\<close> \<open>norm x > 0\<close>
          calculation(2) 
        by (metis \<open>norm (f (x /\<^sub>R norm x)) \<le> K\<close> dual_order.trans norm_ge_zero)
      ultimately show ?thesis  using \<open>inverse (norm x) * norm (f x) \<le> K\<close>
      proof -
        have "\<forall>r. norm x * (inverse (norm x) * r) = r"
          by (metis \<open>norm (x /\<^sub>R norm x) = 1\<close> ab_semigroup_mult_class.mult_ac(1) abs_inverse abs_norm_cancel mult.commute mult.left_neutral norm_scaleR)
        hence "norm (f x) \<le> K * norm x"
          by (metis (no_types) \<open>inverse (norm x) * norm (f x) \<le> K\<close> mult.commute norm_ge_zero real_scaleR_def scaleR_left_mono)
        thus ?thesis
          by (metis mult.commute)
      qed  
    qed
  qed
  thus ?thesis using \<open>linear f\<close> unfolding bounded_linear_def bounded_linear_axioms_def by blast
qed

lemma norm_unit_sphere:
  fixes f::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>bounded_linear f\<close> 
  shows \<open>\<forall>e>0. \<exists> x\<in>(sphere 0 1). norm (norm(f x) - (onorm f)) < e\<close>
proof-
  define S::\<open>real set\<close> where \<open>S = { norm (f x)| x. x \<in> sphere 0 1 }\<close>
  have \<open>S\<noteq>{}\<close>
    unfolding S_def
    using assms(1) assms(2) norm_set_nonempty_eq1 by auto
  hence \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. Sup S - e < y\<close>
    for e
    by (simp add: less_cSupD)
  moreover have \<open>Sup S = onorm f\<close>
  proof-
    have \<open>onorm f = Sup { norm (f x)| x. norm x = 1 }\<close>
      using  \<open>(UNIV::'a set) \<noteq> 0\<close> \<open>bounded_linear f\<close> onorm_sphere
      by blast
    hence \<open>onorm f = Sup { norm (f x)| x. x \<in> sphere 0 1 }\<close>
      unfolding sphere_def
      by simp
    thus ?thesis unfolding S_def by auto
  qed
  ultimately have \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. (onorm f) - e < y\<close>
    for e
    by simp
  hence \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. (onorm f) - y  < e\<close>
    for e
    by force
  hence \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. norm ((onorm f) - y)  < e\<close>
    for e
  proof-
    assume \<open>e > 0\<close>
    have \<open>\<exists> y \<in> S. (onorm f) - y  < e\<close>
      using \<open>0 < e\<close> \<open>\<And>e. 0 < e \<Longrightarrow> \<exists>y\<in>S. onorm f - y < e\<close> by auto
    then obtain y where \<open>y \<in> S\<close> and \<open>(onorm f) - y  < e\<close>
      by blast
    have  \<open>bdd_above S\<close>
    proof-
      have \<open>y \<in> {norm (f x) |x. x \<in> sphere 0 1} \<Longrightarrow> y \<le> onorm f\<close>
      proof-
        assume \<open>y \<in> {norm (f x) |x. x \<in> sphere 0 1}\<close>
        hence \<open>\<exists> x \<in> sphere 0 1. y = norm (f x)\<close>
          by blast
        then obtain x where \<open>x \<in> sphere 0 1\<close> and \<open>y = norm (f x)\<close>
          by blast
        from \<open>y = norm (f x)\<close>
        have \<open>y \<le> onorm f * norm x\<close>
          using assms(2) onorm by auto
        moreover have \<open>norm x = 1\<close>
          using  \<open>x \<in> sphere 0 1\<close> unfolding sphere_def by auto
        ultimately show ?thesis by simp
      qed
      hence \<open>bdd_above {norm (f x) |x. x \<in> sphere 0 1}\<close>
        using assms(2) norm_set_bdd_above_eq1 by force
      thus ?thesis unfolding S_def by blast 
    qed
    hence \<open>y \<le> Sup S\<close>
      using \<open>y \<in> S\<close> \<open>S \<noteq> {}\<close> cSup_upper
      by blast
    hence \<open>0 \<le> Sup S - y\<close>
      by simp
    hence \<open>0 \<le> onorm f - y\<close>
      using \<open>Sup S = onorm f\<close>
      by simp
    hence \<open>\<bar> (onorm f - y) \<bar> = onorm f - y\<close>
      by simp
    hence \<open>norm (onorm f - y)  = onorm f - y\<close>
      by auto
    thus ?thesis
      using \<open>onorm f - y < e\<close> \<open>y \<in> S\<close> by force 
  qed
  hence \<open> 0 < e \<Longrightarrow> \<exists>y\<in>{norm (f x) |x. x \<in> sphere 0 1}. norm (onorm f - y) < e\<close>
    for e
    unfolding S_def by blast
  thus ?thesis 
  proof -
    assume a1: "\<And>e. 0 < e \<Longrightarrow> \<exists>y\<in>{norm (f x) |x. x \<in> sphere 0 1}. norm (onorm f - y) < e"
    have "\<forall>r. r \<notin> S \<or> (\<exists>a. r = norm (f a) \<and> a \<in> sphere 0 1)"
      using S_def by blast
    then show ?thesis
      using a1 by (metis (lifting) S_def norm_minus_commute)
  qed 
qed


end
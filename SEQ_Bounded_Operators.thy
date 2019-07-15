(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Properties of sequences of bounded operators.

*)

theory SEQ_Bounded_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL-Analysis.Infinite_Set_Sum"
    Operator_Norm_Plus
    Convergence_Operators
    Banach_Steinhaus
begin
section \<open>Properties of sequences of bounded operators\<close>



lemma linear_limit_linear:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_vector \<Rightarrow> 'b::real_normed_vector)\<close>
    and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. linear (f n)\<close> 
    and  \<open>f \<midarrow>strong\<rightarrow> F\<close>
  shows \<open>linear F\<close> 
proof
  have \<open>\<And> x. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
    using  \<open>f \<midarrow>strong\<rightarrow> F\<close> by (rule strong_convergence_pointwise)
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
        by (simp add: Real_Vector_Spaces.linear_def linear_scale)

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

lemma bounded_linear_limit_bounded_linear:
  fixes f :: \<open>nat \<Rightarrow> ('a::{banach, perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close>
    and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. bounded_linear (f n)\<close> and  \<open>f \<midarrow>strong\<rightarrow> F\<close> 
  shows \<open>bounded_linear F\<close> 
proof-
  have \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
    using \<open>f \<midarrow>strong\<rightarrow> F\<close> by (rule strong_convergence_pointwise)
  have \<open>linear F\<close>
    using assms(1) assms(2) bounded_linear.linear linear_limit_linear by blast
  moreover have \<open>bounded_linear_axioms F\<close>
  proof
    have "\<exists>K. \<forall> n. \<forall>x. norm ((f n) x) \<le> norm x * K"
    proof-
      have \<open>\<exists> M. \<forall> n. norm ((f n) x) \<le> M\<close>
        for x
      proof-
        have \<open>isCont (\<lambda> t::'b. norm t) y\<close>
          for y::'b
          using Limits.isCont_norm
          by simp
        hence \<open>(\<lambda> n. norm ((f n) x)) \<longlonglongrightarrow> (norm (F x))\<close>
          using \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
          by (simp add: tendsto_norm)
        thus ?thesis using Elementary_Metric_Spaces.convergent_imp_bounded
          by (metis UNIV_I \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> bounded_iff image_eqI)
      qed
      hence \<open>\<exists> M. \<forall> n. onorm (f n) \<le> M\<close>
      proof-
        have \<open>\<And> n. bounded_linear (f n)\<close>
          by (simp add: assms(1) bounded_linear.bounded_linear)           
        moreover have  \<open>\<And>x. \<exists>M. \<forall>n. norm (f n x) \<le> M\<close>
          by (simp add: \<open>\<And>x. \<exists>M. \<forall>n. norm (f n x) \<le> M\<close>)          
        ultimately show ?thesis 
          by (rule banach_steinhaus)
      qed
      then obtain M where \<open>\<forall> n. \<forall> x. onorm (f n) \<le> M\<close>
        by blast
      have \<open>\<forall> n. \<forall>x. norm ((f n) x) \<le> norm x * onorm (f n)\<close>
        using \<open>\<And> n. bounded_linear (f n)\<close>
        unfolding bounded_linear_def
        by (metis assms(1) mult.commute onorm)
      thus ?thesis using  \<open>\<forall> n. \<forall> x. onorm (f n) \<le> M\<close>
        by (metis (no_types, hide_lams) dual_order.trans norm_eq_zero order_refl real_mult_le_cancel_iff2 vector_space_over_itself.scale_zero_left zero_less_norm_iff)    
    qed
    thus "\<exists>K. \<forall>x. norm (F x) \<le> norm x * K"
      using  \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      by (metis Lim_bounded tendsto_norm) 
  qed
  ultimately show ?thesis unfolding bounded_linear_def by blast
qed




end

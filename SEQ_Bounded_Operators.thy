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


lemma strong_convergence_pointwise: 
  \<open>f \<midarrow>strong\<rightarrow> F \<Longrightarrow> (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
  for x
proof-
  assume  \<open>f \<midarrow>strong\<rightarrow> F\<close>
  hence  \<open>( \<lambda> n. norm ((f n) x - F x))  \<longlonglongrightarrow> 0\<close>
    unfolding strong_convergence_def
    by blast
  have \<open>( \<lambda> n. (F x) )  \<longlonglongrightarrow> F x\<close>
    by simp
  moreover have  \<open>( \<lambda> n. ( (f n) x - F x))  \<longlonglongrightarrow> 0\<close>
    using  \<open>( \<lambda> n. norm ((f n) x - F x) )  \<longlonglongrightarrow> 0\<close>
    by (simp add:  tendsto_norm_zero_iff)
  ultimately have  \<open>( \<lambda> n. (f n) x)  \<longlonglongrightarrow> F x\<close>
    by (rule Limits.Lim_transform)
  thus ?thesis by blast
qed

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

lemma onorm_tendsto:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> and l :: \<open>'a \<Rightarrow> 'b\<close> 
    and e :: real
  assumes \<open>\<forall>n. bounded_linear (f n)\<close> and \<open>e > 0\<close>
    and \<open>bounded_linear l\<close> and \<open>f \<midarrow>onorm\<rightarrow> l\<close>
  shows \<open>\<forall>\<^sub>F n in sequentially. onorm (\<lambda>x. f n x - l x) < e\<close>
proof-
  from  \<open>f \<midarrow>onorm\<rightarrow> l\<close>
  have \<open>(\<lambda> n. onorm (\<lambda> x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
    unfolding onorm_convergence_def
    by blast
  hence \<open>\<exists> N. \<forall> n \<ge> N. dist ((\<lambda> n. onorm (\<lambda>x. f n x - l x)) n) 0 < e\<close>
    using \<open>e > 0\<close>
    by (simp add: lim_sequentially) 
  hence \<open>\<exists> N. \<forall> n \<ge> N. \<bar> onorm (\<lambda>x. f n x - l x) \<bar> < e\<close>
    by simp
  have \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) < e\<close>
  proof-
    have \<open>bounded_linear t \<Longrightarrow> onorm t \<ge> 0\<close>
      for t::\<open>'a \<Rightarrow> 'b\<close>
      using onorm_pos_le by blast 
    thus ?thesis using  \<open>\<exists> N. \<forall> n \<ge> N. \<bar> onorm (\<lambda>x. f n x - l x) \<bar> < e\<close> by fastforce
  qed
  thus ?thesis
    by (simp add: eventually_at_top_linorder)
qed


lemma onorm_strong:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> and l::\<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>\<forall>n. bounded_linear (f n)\<close> and \<open>bounded_linear l\<close> and \<open>f \<midarrow>onorm\<rightarrow> l\<close>
  shows \<open>f \<midarrow>strong\<rightarrow> l\<close>
proof-
  have \<open>(\<lambda>n. norm (f n x - l x)) \<longlonglongrightarrow> 0\<close>
    for x
  proof-
    have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N. dist (norm (f n x - l x)) 0 < e\<close>
      for e::real
    proof-
      assume \<open>e > 0\<close>
      have \<open>\<exists> N. \<forall> n \<ge> N. norm (f n x - l x) < e\<close>
      proof-
        have \<open>norm (f n x - l x) \<le> onorm (\<lambda> t. f n t - l t) * norm x\<close>
          for n::nat
          using assms(1) assms(2) bounded_linear_sub onorm by blast                          
        moreover have \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda> t. f n t - l t) * norm x < e\<close>
        proof(cases \<open>norm x = 0\<close>)
          case True
          thus ?thesis
            by (simp add: \<open>0 < e\<close>) 
        next
          case False
          hence \<open>norm x > 0\<close>
            by simp
          have \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda> t. f n t - l t) < e/norm x\<close>
          proof-
            from \<open>f \<midarrow>onorm\<rightarrow> l\<close>
            have \<open>(\<lambda> n. onorm (\<lambda> t. f n t - l t)) \<longlonglongrightarrow> 0\<close>
              unfolding onorm_convergence_def
              by blast
            moreover have \<open>e / norm x > 0\<close>
              using \<open>e > 0\<close> \<open>norm x > 0\<close> by simp
            ultimately have \<open>\<exists> N. \<forall> n\<ge>N. norm ((\<lambda> n. onorm (\<lambda> t. f n t - l t)) n ) < e / norm x\<close>
              by (simp add: LIMSEQ_iff) 
            then obtain N where \<open>\<forall> n\<ge>N. norm ((\<lambda> n. onorm (\<lambda> t. f n t - l t)) n ) < e / norm x\<close>
              by blast
            hence \<open>\<forall> n\<ge>N. norm ( onorm (\<lambda> t. f n t - l t ) ) < e / norm x\<close>
              by blast
            have \<open>\<forall> n\<ge>N.  onorm (\<lambda> t. f n t - l t ) < e / norm x\<close>
            proof-
              have \<open>onorm (\<lambda> t. f n t - l t ) \<ge> 0\<close>
                for n
                by (simp add: assms(1) assms(2) bounded_linear_sub onorm_pos_le)                
              thus ?thesis using  \<open>\<forall> n\<ge>N. norm ( onorm (\<lambda> t. f n t - l t ) ) < e / norm x\<close>
                by simp
            qed
            thus ?thesis by blast
          qed
          thus ?thesis using \<open>norm x > 0\<close>
          proof -
            { fix nn :: "nat \<Rightarrow> nat"
              have ff1: "\<forall>r ra. (ra::real) * r = r * ra \<or> ra = 0"
                by auto
              have "\<forall>r ra rb. (((rb::real) = 0 \<or> rb * ra < r) \<or> \<not> ra < r / rb) \<or> \<not> 0 < rb"
                by (metis (no_types) linordered_comm_semiring_strict_class.comm_mult_strict_left_mono nonzero_mult_div_cancel_left times_divide_eq_right)
              hence "\<exists>n. \<not> n \<le> nn n \<or> onorm (\<lambda>a. f (nn n) a - l a) * norm x < e"
                using ff1 by (metis (no_types) False \<open>0 < norm x\<close> \<open>\<exists>N. \<forall>n\<ge>N. onorm (\<lambda>t. f n t - l t) < e / norm x\<close>) }
            thus ?thesis
              by (metis (no_types))
          qed  
        qed
        ultimately show ?thesis by smt
      qed
      thus ?thesis
        by auto 
    qed
    thus ?thesis
      by (simp add: LIMSEQ_I) 
  qed
  thus ?thesis unfolding strong_convergence_def by blast
qed


end

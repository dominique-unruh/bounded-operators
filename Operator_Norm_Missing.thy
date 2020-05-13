section \<open>\<open>Operator_Norm_Missing\<close> -- Miscellaneous results about the operator norm\<close>

(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

theory Operator_Norm_Missing
  imports 
    Complex_Main
    Banach_Steinhaus
    "HOL-Analysis.Infinite_Set_Sum"
    "HOL-Analysis.Operator_Norm"
begin

text \<open>This theorem complements \<^theory>\<open>HOL-Analysis.Operator_Norm\<close>
      additional useful facts about operator norms.\<close>

subsection \<open>Characterization of the operator norm\<close>

lemma ex_norm1: 
  assumes \<open>(UNIV::'a::real_normed_vector set) \<noteq> {0}\<close>
  shows \<open>\<exists>x::'a. norm x = 1\<close>
proof-
  have \<open>\<exists>x::'a. x \<noteq> 0\<close>
    using assms by fastforce
  then obtain x::'a where \<open>x \<noteq> 0\<close>
    by blast
  hence \<open>norm x \<noteq> 0\<close>
    by simp
  hence \<open>(norm x) / (norm x) = 1\<close>
    by simp
  moreover have \<open>(norm x) / (norm x) = norm (x /\<^sub>R (norm x))\<close>
    by simp
  ultimately have \<open>norm (x /\<^sub>R (norm x)) = 1\<close>
    by simp
  thus ?thesis
    by blast 
qed

lemma bdd_above_norm_f:
  assumes "bounded_linear f"
  shows \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
proof-
  have \<open>\<exists>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f x) \<le> M\<close>
    using assms
    by (metis bounded_linear.axioms(2) bounded_linear_axioms_def)
  thus ?thesis by auto
qed

(* ask to dominique where not_singleton was defined *)
(* TODO: remove assumption "UNIV\<noteq>{0}" and add type class not_singleton instead *)
lemma onorm_sphere:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>(UNIV::'a set) \<noteq> {0}\<close> and  \<open>bounded_linear f\<close>
  shows \<open>onorm f = Sup {norm (f x) | x. norm x = 1}\<close>
proof(cases \<open>f = (\<lambda> _. 0)\<close>)
  case True
  have \<open>onorm f = 0\<close>
    by (simp add: True onorm_eq_0)  
  moreover have \<open>Sup {norm (f x) | x. norm x = 1} = 0\<close>
  proof-
    have \<open>\<exists>x::'a. norm x = 1\<close>
      using \<open>(UNIV::'a set) \<noteq> {0}\<close> ex_norm1
      by blast
    have \<open>norm (f x) = 0\<close>
      for x
      by (simp add: True)      
    hence \<open>{norm (f x) | x. norm x = 1} = {0}\<close>
      apply auto using \<open>\<exists>x. norm x = 1\<close> by blast 
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
          moreover have \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}
                     \<Longrightarrow> y \<in> {norm (f x) / norm x |x. True}\<close>
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
            using bdd_above_norm_f
            by (metis (mono_tags, lifting) assms(2)) 
          ultimately have \<open>y \<le> Sup {norm (f x) |x. norm x = 1}\<close>
            using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
            by (simp add: cSup_upper) 
          thus ?thesis using \<open>y \<ge> 0\<close> by simp
        qed
        moreover have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {0}) = Sup {norm (f x) |x. norm x = 1}\<close>
        proof-
          have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
            by (simp add: assms(1) ex_norm1)
          moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
            using assms(2) bdd_above_norm_f by force
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


(* TODO: remove assumption "UNIV\<noteq>{0}" and add type class not_singleton instead *)
proposition onorm_Inf_bound:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes  \<open>(UNIV::'a set) \<noteq> {0}\<close> and \<open>bounded_linear f\<close>
  shows  \<open>onorm f = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
proof-
  have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Inf {K. (\<forall>x\<noteq>0. norm (f x)/ norm x \<le>  K)}\<close>
  proof-
    define A where \<open>A = {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
    have \<open>A \<noteq> {}\<close>
    proof-
      have \<open>\<exists> x::'a. x \<noteq> 0\<close>
        using \<open>UNIV \<noteq> {0}\<close> by auto
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
          using \<open>UNIV\<noteq>{0}\<close> by auto
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
          using \<open>UNIV\<noteq>{0}\<close> by auto
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


subsection \<open>Banach-Steinhaus theorem\<close>

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

(* TODO: remove assumption "UNIV\<noteq>{0}" and add type class not_singleton instead *)
lemma norm_unit_sphere:
  fixes f::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>(UNIV::'a set) \<noteq> {0}\<close> and \<open>bounded_linear f\<close> and \<open>e > 0\<close>
  shows \<open>\<exists> x\<in>(sphere 0 1). norm (norm(f x) - (onorm f)) < e\<close>
proof-
  define S::\<open>real set\<close> where \<open>S = { norm (f x)| x. x \<in> sphere 0 1 }\<close>
  have \<open>S\<noteq>{}\<close>
  proof-
    have \<open>\<exists>x::'a. x \<in> sphere 0 1\<close>
      unfolding sphere_def apply auto using \<open>(UNIV::'a set) \<noteq> {0}\<close> ex_norm1
      by auto      
    thus ?thesis unfolding S_def by auto
  qed
  hence \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. Sup S - e < y\<close>
    for e
    by (simp add: less_cSupD)
  moreover have \<open>Sup S = onorm f\<close>
  proof-
    have \<open>onorm f = Sup { norm (f x)| x. norm x = 1 }\<close>
      using  \<open>(UNIV::'a set) \<noteq> {0}\<close> \<open>bounded_linear f\<close> onorm_sphere
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
        using assms(2) bdd_above_norm_f by force
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
    thus ?thesis
      using a1 \<open>\<And>e. 0 < e \<Longrightarrow> \<exists>y\<in>S. norm (onorm f - y) < e\<close> assms(3) by force 
  qed 
qed

lemma sphere_nonzero:
  assumes \<open>S \<subseteq> sphere 0 r\<close> and \<open>r > 0\<close> and \<open>x \<in> S\<close>
  shows \<open>x \<noteq> 0\<close>
proof-
  from \<open>S \<subseteq> sphere 0 r\<close> and  \<open>x \<in> S\<close>
  have  \<open>x \<in> sphere 0 r\<close>
    by blast
  hence \<open>dist x 0 = r\<close>
    by (simp add: dist_commute)     
  thus ?thesis using \<open>r > 0\<close>
    by auto
qed


end

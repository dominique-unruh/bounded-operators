theory Extra_Operator_Norm
  imports "HOL-Analysis.Operator_Norm"
    Extra_General
begin


subsection \<open>\<open>Operator_Norm_Missing\<close> -- Miscellaneous results about the operator norm\<close>

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

lemma onorm_sphere:
  fixes f :: "'a::{real_normed_vector, not_singleton} \<Rightarrow> 'b::real_normed_vector"
  assumes a1: "bounded_linear f"
  shows \<open>onorm f = Sup {norm (f x) | x. norm x = 1}\<close>
proof(cases \<open>f = (\<lambda> _. 0)\<close>)
  case True
  have \<open>(UNIV::'a set) \<noteq> {0}\<close>
    by simp
  hence \<open>\<exists>x::'a. norm x = 1\<close>
    using  ex_norm1
    by blast
  have \<open>norm (f x) = 0\<close>
    for x
    by (simp add: True)      
  hence \<open>{norm (f x) | x. norm x = 1} = {0}\<close>
    using \<open>\<exists>x. norm x = 1\<close> by auto
  hence v1: \<open>Sup {norm (f x) | x. norm x = 1} = 0\<close>
    by simp 
  have \<open>onorm f = 0\<close>
    by (simp add: True onorm_eq_0)  
  thus ?thesis using v1 by simp
next
  case False
  have \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
    if "y \<in> {norm (f x) / norm x |x. True}"
    for y
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
      apply (subst linear_cmul[of f])
      by (simp_all add: assms bounded_linear.linear)
    moreover have \<open>norm ((1/norm x) *\<^sub>R x) = 1\<close>
      using False \<open>y = norm (f x) / norm x\<close> by auto              
    ultimately have \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
      by blast
    thus ?thesis by blast
  qed
  moreover have "y \<in> {norm (f x) / norm x |x. True}"
    if \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
    for y
  proof(cases \<open>y = 0\<close>)
    case True
    thus ?thesis
      by auto 
  next
    case False
    hence \<open>y \<notin> {0}\<close>
      by simp
    hence \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
      using that by auto      
    hence \<open>\<exists> x. norm x = 1 \<and> y = norm (f x)\<close>
      by auto
    then obtain x where \<open>norm x = 1\<close> and \<open>y = norm (f x)\<close>
      by auto
    have \<open>y = norm (f x) / norm x\<close> using  \<open>norm x = 1\<close>  \<open>y = norm (f x)\<close>
      by simp 
    thus ?thesis
      by auto 
  qed
  ultimately have \<open>{norm (f x) / norm x |x. True} = {norm (f x) |x. norm x = 1} \<union> {0}\<close> 
    by blast
  hence \<open>Sup {norm (f x) / norm x |x. True} = Sup ({norm (f x) |x. norm x = 1} \<union> {0})\<close>
    by simp
  moreover have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
  proof-
    have \<open>\<exists> x::'a. norm x = 1\<close>
      by (metis (mono_tags, hide_lams) False assms bounded_linear.nonneg_bounded mult_zero_left norm_le_zero_iff norm_sgn)
    then obtain x::'a where \<open>norm x = 1\<close>
      by blast
    have \<open>norm (f x) \<ge> 0\<close>
      by simp
    hence \<open>\<exists> x::'a. norm x = 1 \<and> norm (f x) \<ge> 0\<close>
      using \<open>norm x = 1\<close> by blast
    hence \<open>\<exists> y \<in> {norm (f x) |x. norm x = 1}. y \<ge> 0\<close>
      by blast
    then obtain y::real where \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> 
      and \<open>y \<ge> 0\<close>
      by auto
    have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
      using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> by blast         
    moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
      using bdd_above_norm_f
      by (metis (mono_tags, lifting) a1) 
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
      using a1 bdd_above_norm_f by force
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
  ultimately have w1: "Sup {norm (f x) / norm x | x. True} = Sup {norm (f x) | x. norm x = 1}"
    by simp 

  have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) / norm x | x. True}\<close>
    by (simp add: full_SetCompr_eq)
  also have \<open>... = Sup {norm (f x) | x. norm x = 1}\<close>
    using w1 by auto
  ultimately  have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) | x. norm x = 1}\<close>
    by linarith
  thus ?thesis unfolding onorm_def by blast
qed


lemma onorm_Inf_bound:
  fixes f :: \<open>'a::{real_normed_vector,not_singleton} \<Rightarrow> 'b::real_normed_vector\<close>
  assumes a1: "bounded_linear f"
  shows "onorm f = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}"
proof-
  have a2: \<open>(UNIV::'a set) \<noteq> {0}\<close>
    by simp

  define A where \<open>A = {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
  have \<open>A \<noteq> {}\<close>
  proof-
    have \<open>\<exists> x::'a. x \<noteq> 0\<close>
      using a2 by auto
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
  ultimately have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} 
                    = Inf {K. (\<forall>x\<noteq>0. norm (f x)/ norm x \<le>  K)}\<close>
    using A_def
    by simp 
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
  ultimately have f1: \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
    by simp
  moreover 
  have t1: \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0}  = {norm (f x) / (norm x) | x. True}\<close>
    using Collect_cong by blast

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
      using \<open>bounded_linear f\<close> bounded_linear.nonneg_bounded 
        mult_divide_mult_cancel_left_if norm_zero real_divide_square_eq
      using le_onorm by blast
    thus ?thesis
      by auto 
  qed
  moreover have \<open>{norm (f x) / (norm x) | x. x = 0} \<noteq> {}\<close>
    by simp
  moreover have \<open>bdd_above {norm (f x) / (norm x) | x. x = 0}\<close>
    by simp
  ultimately 
  have d1: \<open>Sup ({norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0})
        = max (Sup {norm (f x) / (norm x) | x. x \<noteq> 0}) (Sup {norm (f x) / (norm x) | x. x = 0})\<close>
    by (metis (no_types, lifting) cSup_union_distrib sup_max)
  have g1: \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} \<ge> 0\<close>
  proof-
    have t2: \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<noteq> {}\<close>
    proof-
      have \<open>\<exists> x::'a. x \<noteq> 0\<close>
        using \<open>UNIV\<noteq>{0}\<close> by auto
      thus ?thesis 
        by auto
    qed
    have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
      using \<open>bounded_linear f\<close>
      by (metis \<open>\<And>K. (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) \<le> norm x * K) = (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) / norm x \<le> K)\<close> bounded_linear.nonneg_bounded mult_divide_mult_cancel_left_if norm_zero real_divide_square_eq)
    hence t3: \<open>bdd_above {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
      by auto
    have \<open>norm (f x) / (norm x) \<ge> 0\<close>
      for x
      by simp
    hence \<open>\<forall> y\<in>{norm (f x) / (norm x) | x. x \<noteq> 0}. y \<ge> 0\<close>
      by blast
    show ?thesis
      by (metis (lifting) \<open>\<forall>y\<in>{norm (f x) / norm x |x. x \<noteq> 0}. 0 \<le> y\<close> \<open>bdd_above {norm (f x) / norm x |x. x \<noteq> 0}\<close> \<open>{norm (f x) / norm x |x. x \<noteq> 0} \<noteq> {}\<close> bot.extremum_uniqueI cSup_upper2 subset_emptyI)
  qed
  hence r: \<open>Sup ({norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0}) 
         = Sup {norm (f x) / (norm x) | x. True}\<close>
    using t1 by auto
  have \<open>{norm (f x) / (norm x) | x. x = 0} = {norm (f 0) / (norm 0)}\<close>
    by simp
  hence \<open>Sup {norm (f x) / (norm x) | x. x = 0} = 0\<close>
    by simp
  have h1: \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Sup {norm (f x) / (norm x) | x. True}\<close>
    using d1 r g1 by auto 
  have \<open>(SUP x. norm (f x) / (norm x)) = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
    using full_SetCompr_eq
    by (metis f1 h1)
  thus ?thesis
    by (simp add: onorm_def)
qed


end

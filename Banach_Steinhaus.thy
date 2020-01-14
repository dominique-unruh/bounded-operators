section \<open>Banach-Steinhaus theorem\<close>
(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Main results
- banach_steinhaus: Banach-Steinhaus theorem. The reference of the proof is [sokal2011really].
- bounded_linear_limit_bounded_linear: A corollary of  Banach-Steinhaus theorem. A sufficient 
condition for a sequence of linear bounded operators to converge pointwise to a linear bounded 
operator.
*)

theory Banach_Steinhaus
  imports Real_Analysis_Missing Operator_Norm_Missing_Banach_Steinhaus
begin

subsection \<open>Preliminaries for the proof of Banach-Steinhaus\<close>

text \<open>The proof of the following result was taken from @{cite sokal2011really}\<close>
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
    using \<open>\<And> \<xi>. norm (f \<xi>) \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>
  proof -
    assume "\<And>\<xi>. norm (f \<xi>) \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))"
    then have f1: "\<And>a. norm (f a) \<le> v a"
      by (metis \<open>v \<equiv> \<lambda>\<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>)
    have "(Sup {}::real) \<le> Sup {}"
      by (metis order_refl)
    then show ?thesis
      using f1 by (metis (no_types) \<open>bdd_above (v ` S)\<close> \<open>u \<equiv> \<lambda>\<xi>. norm (f \<xi>)\<close> cSUP_mono image_empty)
  qed
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
            hence f2: "aa \<in> {a. norm a < r}"
              by (metis S_def)
            have "norm aa = dist (x + aa) x"
              by (metis (full_types) add_diff_cancel_right' dist_diff(1))
            thus ?thesis
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
            hence f2: "aa \<in> {a. norm a < r}"
              using S_def by blast
            have "norm aa = dist (x + aa) x"
              by (metis add_diff_cancel_right' dist_diff(1))
            hence "\<exists>a. norm (f (x - t)) = norm (f a) \<and> \<not> r + - 1 * dist a x \<le> 0"
              using f2 f1 \<open>y = norm (f (x - t))\<close> by force
            thus ?thesis
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
      thus ?thesis
        by (metis (lifting) \<open>{norm (f y) |y. dist y x < r} \<noteq> {}\<close> cSup_least)
    qed 
    thus ?thesis
      using \<open>Sup (v ` S) \<le> Sup {norm (f y) |y. dist y x < r}\<close>
      by linarith      
  qed
  thus ?thesis
    using calculation(1) calculation(2) by auto 
qed


subsection \<open>Banach-Steinhaus theorem\<close>

theorem banach_steinhaus:
  fixes f :: \<open>'c \<Rightarrow> ('a::{banach,perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close>
  assumes \<open>\<And> n. bounded_linear (f n)\<close>
    and  \<open>\<And> x. \<exists> M. \<forall> n.  norm ((f n) x) \<le> M\<close>
  shows  \<open>\<exists> M. \<forall> n. onorm (f n) \<le> M\<close>
proof(rule classical)
  assume \<open>\<not>(\<exists> M. \<forall> k. onorm (f k) \<le> M)\<close>
  hence \<open>\<forall> M. \<exists> k. onorm (f k) > M\<close>
    using leI by blast
  hence \<open>\<forall> n. \<exists> k. onorm (f k) > 4^n\<close>
    by simp
  hence \<open>\<exists> k\<^sub>f. \<forall> n. onorm (f (k\<^sub>f n)) > 4^n\<close>
    by metis
  then obtain k\<^sub>f where \<open>\<forall> n. onorm (f (k\<^sub>f n)) > 4^n\<close> 
    by blast
  define g::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close> where \<open>g n = f (k\<^sub>f n)\<close>
    for n
  hence \<open>\<forall> n. onorm (g n) > 4^n\<close>
    using  \<open>\<forall> n. onorm (f (k\<^sub>f n)) > 4^n\<close>  by simp
  from \<open>\<And> n. bounded_linear (f n)\<close>
  have \<open>\<And> n. bounded_linear (g n)\<close>
    using g_def by simp
  have \<open>bounded_linear h \<Longrightarrow> 0 < onorm h \<Longrightarrow> r > 0
     \<Longrightarrow> \<exists> y. dist y x < r \<and> norm (h y) > (2/3) * r * onorm h\<close>
    for r and x and h::\<open>'a \<Rightarrow> 'b\<close>
  proof-
    assume \<open>bounded_linear h\<close>
    moreover assume \<open>r > 0\<close>
    ultimately have \<open>(onorm h) * r \<le> Sup {norm (h y) | y. dist y x < r}\<close>
      by (simp add: sokal_banach_steinhaus)
    assume \<open>0 < onorm h\<close>
    have \<open>(onorm h) * r * (2/3) < Sup {norm (h y) | y. dist y x < r}\<close>
    proof -
      have f1: "\<forall>r ra. (ra::real) * r = r * ra"
        by auto
      hence f2: "r * onorm h \<le> Sup {norm (h a) |a. dist a x < r}"
        by (metis \<open>onorm h * r \<le> Sup {norm (h y) |y. dist y x < r}\<close>)
      have "0 < r * onorm h"
        by (metis \<open>0 < onorm h\<close> \<open>0 < r\<close> linordered_semiring_strict_class.mult_pos_pos)
      hence "r * onorm h * (2 / 3) < Sup {norm (h a) |a. dist a x < r}"
        using f2 by linarith
      thus ?thesis
        using f1 by presburger
    qed 
    moreover have \<open>{norm (h y) | y. dist y x < r} \<noteq> {}\<close>
    proof-
      have \<open>\<exists> y::'a. dist y x < r\<close>
        using \<open>r > 0\<close>
        by (metis dist_self)
      hence \<open>{y | y. dist y x < r} \<noteq> {}\<close>
        by simp
      hence \<open>(\<lambda> y. norm ((g n) y)) ` {y | y. dist y x < r} \<noteq> {}\<close>
        for n
        by blast
      thus ?thesis by blast
    qed
    moreover have \<open>bdd_above {norm (h y) | y. dist y x < r}\<close>
    proof-
      have \<open>norm (h y) \<le> onorm h * norm y\<close>
        for y
        using \<open>bounded_linear h\<close>
        by (simp add: onorm)    
      moreover have \<open>norm y \<le> norm x + norm (y - x)\<close>
        for y
        by (simp add: norm_triangle_sub)        
      moreover have \<open>onorm h \<ge> 0\<close>
        by (simp add: \<open>bounded_linear h\<close> onorm_pos_le)
      ultimately have \<open>norm (h y) \<le> onorm h * (norm x + norm (y - x))\<close>
        for y
        by (smt ordered_comm_semiring_class.comm_mult_left_mono)
      hence \<open>norm (h y) \<le> onorm h * (norm x + dist y x)\<close>
        for y
        by (simp add: dist_norm)
      hence \<open>dist y x < r \<Longrightarrow> norm (h y) < onorm h * (norm x + r)\<close>
        for y
        by (smt \<open>0 < onorm h\<close> mult_left_le_imp_le)
      hence \<open>t \<in> {norm (h y) | y. dist y x < r} \<Longrightarrow> t \<le> onorm h * (norm x + r)\<close>
        for t
        by fastforce
      thus ?thesis by fastforce
    qed
    ultimately have \<open>\<exists> t \<in> {norm (h y) | y. dist y x < r}. 
                    (onorm h) * r * (2/3) < t\<close>
      using less_cSup_iff
      by smt
    hence \<open>\<exists> s \<in> {y | y. dist y x < r}. 
                    (onorm h) * r * (2/3) < norm (h s)\<close>
      by blast
    hence \<open>\<exists> y. dist y x < r \<and> 
                    (onorm h) * r * (2/3) < norm (h y)\<close>
      by blast
    hence \<open>\<exists> y. dist y x < r \<and> 
                   r * (2/3) * (onorm h) < norm (h y)\<close>
      by (metis mult.commute vector_space_over_itself.scale_scale)
    thus ?thesis by auto
  qed
  hence \<open>\<exists> y. dist y x < (1/3)^n \<and> norm ((g n) y) > (2/3) * (1/3)^n * onorm (g n)\<close>
    for n and x
  proof-
    have \<open>((1/3)::real)^n > 0\<close>
      by simp
    moreover have \<open>\<And> n. onorm (g n) > 0\<close>
      using  \<open>\<forall> n. onorm (g n) > (4::real)^n\<close>
      by (smt zero_less_power)                             
    ultimately show ?thesis using  \<open>\<And> n. bounded_linear (g n)\<close>
      using \<open>\<And>x r h. \<lbrakk>bounded_linear h; 0 < onorm h; 0 < r\<rbrakk> \<Longrightarrow> \<exists>y. dist y x < r \<and> 2 / 3 * r * onorm h < norm (h y)\<close> by auto
  qed
  hence \<open>\<forall> n. \<forall> x. \<exists> y. dist y x < (1/3)^n \<and> norm ((g n) y) > (2/3) * (1/3)^n * onorm (g n)\<close>
    by blast
  hence \<open>\<exists> \<Phi>. \<forall> n. \<forall> x. dist (\<Phi> n x) x < (1/3)^n \<and> norm ((g n) (\<Phi> n x)) > (2/3) * (1/3)^n * onorm (g n)\<close>
    by metis
  then obtain \<Phi>
    where \<open>\<forall> n. \<forall> x. dist (\<Phi> n x) x <
       (1/3)^n \<and> norm ((g n) (\<Phi> n x)) > (2/3) * (1/3)^n * onorm (g n)\<close>
    by blast
  define \<phi>::\<open>nat \<Rightarrow> 'a\<close> where \<open>\<phi> n = rec_nat 0 \<Phi> n\<close>
    for n
  have \<open>\<phi> 0 = 0\<close>
    using \<phi>_def by simp
  have \<open>\<phi> (Suc n) = \<Phi> n (\<phi> n)\<close>
    for n
    using \<phi>_def by simp
  from \<open>\<forall> n. \<forall> x. dist (\<Phi> n x) x <
       (1/3)^n \<and> norm ((g n) (\<Phi> n x)) > (2/3) * (1/3)^n * onorm (g n)\<close>
  have \<open>dist (\<phi> (Suc n))  (\<phi> n) < (1/3)^n\<close>
    for n
    using \<open>\<And>n. \<phi> (Suc n) = \<Phi> n (\<phi> n)\<close> by auto
  have \<open>Cauchy \<phi>\<close>
  proof-
    have \<open>norm ((1/3)::real) < 1\<close>
      by simp      
    hence \<open>summable (\<lambda> k. ((1/3)::real)^k)\<close>
      using Series.summable_geometric_iff 
      by fastforce
    hence \<open>\<exists>s. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..<n}) \<longlonglongrightarrow> s\<close>
      unfolding summable_def sums_def by blast
    hence \<open>\<exists>s. (\<lambda>m. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..<n}) (Suc m)) \<longlonglongrightarrow> s\<close>
    proof-
      obtain s where \<open>(\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..<n}) \<longlonglongrightarrow> s\<close>
        using  \<open>\<exists>s. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..<n}) \<longlonglongrightarrow> s\<close> by blast
      hence  \<open>(\<lambda>m. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..<n}) (Suc m)) \<longlonglongrightarrow> s\<close>
        by (rule LIMSEQ_Suc) 
      thus ?thesis by blast 
    qed
    hence \<open>\<exists>s. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {..n}) \<longlonglongrightarrow> s\<close>
      using \<open>summable (\<lambda> k::nat. ((1/3)::real)^k)\<close> summable_LIMSEQ' by blast 
    hence \<open>\<exists>s::real. (\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<longlonglongrightarrow> s\<close>
      unfolding atLeastAtMost_def 
      by auto
    then obtain s::real where \<open>(\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<longlonglongrightarrow> s\<close>
      by blast
    from  \<open>(\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<longlonglongrightarrow> s\<close>
    have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> m \<ge> N. dist ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m)  s < e\<close>
      for e::real
      by (meson LIMSEQ_iff_nz)
    moreover have \<open>(1::real) > 0\<close>
      by auto
    ultimately have \<open>\<exists> N. \<forall> m \<ge> N. dist ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m)  s < (1::real)\<close>
      by auto
    then obtain N where \<open>\<forall> m \<ge> N. dist ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m)  s < (1::real)\<close>
      by blast
    hence \<open>\<forall> m \<ge> N. \<bar> ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m) - s \<bar> < (1::real)\<close>
      by (simp add: dist_real_def)
    hence \<open>\<forall> m \<ge> N. \<bar> ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m) \<bar> < \<bar>s\<bar> + (1::real)\<close>
      by auto
    hence \<open>\<forall> m \<ge> N. ((\<lambda>n. sum (\<lambda> k. ((1/3)::real)^k) {0..n}) m) < \<bar>s\<bar> + (1::real)\<close>
      by auto
    hence \<open>\<forall> n \<ge> N. (sum (\<lambda> k. ((1/3)::real)^k) {0..n}) < \<bar>s\<bar> + (1::real)\<close>
      by auto
    hence \<open>\<forall> n \<ge> N. (sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<le> \<bar>s\<bar> + (1::real)\<close>
      by auto
    moreover have \<open>\<forall> n < N. (sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<le> (sum (\<lambda> k. ((1/3)::real)^k) {0..N})\<close>
    proof-
      have  \<open>\<forall> n. f n \<ge> 0 \<Longrightarrow> \<forall> n < N. sum f {0..n} \<le> sum f {0..N}\<close>
        for f :: \<open>nat \<Rightarrow> real\<close> and N::nat
      proof(induction N)
        case 0
        thus ?case
          by simp 
      next
        case (Suc N)
        assume \<open>\<forall> n. f n \<ge> 0\<close>
        moreover assume \<open>\<forall>n. 0 \<le> f n \<Longrightarrow> \<forall>n<N. sum f {0..n} \<le> sum f {0..N}\<close>
        ultimately have \<open>\<forall>n<N. sum f {0..n} \<le> sum f {0..N}\<close>
          by blast
        moreover have  \<open>sum f {0..N} \<le> sum f {0..Suc N}\<close>
        proof-
          have \<open>sum f {0..Suc N} = sum f {0..N} + f (Suc N)\<close>
            using sum.atLeast0_atMost_Suc by blast          
          thus ?thesis
            by (simp add: Suc.prems) 
        qed
        ultimately show ?case
          by (smt less_antisym)  
      qed
      thus ?thesis
        by auto
    qed
    ultimately have \<open>\<forall> n. (sum (\<lambda> k. ((1/3)::real)^k) {0..n})
         \<le> max (\<bar>s\<bar> + (1::real)) (sum (\<lambda> k. ((1/3)::real)^k) {0..N})\<close>
      by (smt diff_is_0_eq gr_zeroI zero_less_diff)
    hence \<open>\<exists> M. \<forall> n. (sum (\<lambda> k. ((1/3)::real)^k) {0..n}) \<le> M\<close>
      by blast
    thus ?thesis
      using convergent_series_Cauchy  \<open>\<And> n. dist (\<phi> (Suc n))  (\<phi> n) < (1/3)^n\<close>
      by smt
  qed
  hence \<open>\<exists> l. \<phi> \<longlonglongrightarrow> l\<close>
    by (simp add: convergent_eq_Cauchy)
  then obtain l where \<open>\<phi> \<longlonglongrightarrow> l\<close>
    by blast
  obtain M where \<open>\<forall> n.  norm ((f n) l) \<le> M\<close>
    using \<open>\<And> x. \<exists> M. \<forall> n.  norm ((f n) x) \<le> M\<close>
    by blast
  have \<open>(\<lambda> n. norm ((g n) l)) \<longlonglongrightarrow> \<infinity>\<close>    
  proof-
    have \<open>norm ((\<phi> (Suc n)) - l) \<le> (1/2)*(1/3::real)^n\<close>
      for n
    proof-             
      define x where \<open>x = (\<lambda> n.  \<phi> (Suc n))\<close>
      have \<open>x \<longlonglongrightarrow> l\<close> 
        using x_def
        by (meson \<open>\<phi> \<longlonglongrightarrow> l\<close> le_imp_less_Suc pinf(8) tendsto_explicit)
      moreover have \<open>(sum (\<lambda> t. norm (x (Suc t) - x t)) {n..k}) \<le> (1/2)*(1/3::real)^n\<close>
        for k
      proof-
        have \<open>(sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..k}) \<le> (1/2)*(1/3::real)^n\<close>
        proof-
          from \<open>\<And> n. dist (\<phi> (Suc n))  (\<phi> n) < (1/3)^n\<close>
          have \<open>norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t)) < (1/3::real)^(Suc t)\<close>
            for t
            by (metis dist_norm)            
          hence \<open>(sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..n+p}) 
              \<le> (sum (\<lambda> t. (1/3::real)^(Suc t) ) {n..n+p})\<close> 
            for p::nat
          proof(induction p)
            case 0
            have \<open>norm (\<phi> (Suc (Suc n)) - \<phi> (Suc n)) < (1/3::real)^(Suc n)\<close>
              using \<open>\<And> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t)) < (1/3::real)^(Suc t)\<close>
              by blast
            hence \<open>(\<Sum>t = n..n. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) \<le> (\<Sum>t = n..n. (1 / 3) ^ Suc t)\<close>
              by simp
            thus ?case 
              by simp
          next
            case (Suc p)
            thus ?case
              by (smt add_Suc_right le_add1 sum.nat_ivl_Suc') 
          qed
          moreover have  \<open>(sum (\<lambda> t. (1/3::real)^(Suc t) ) {n..n+p}) \<le> (1/2)*(1/3::real)^n\<close> 
            for p::nat
          proof-
            have \<open>n \<le> n + p\<close>
              by auto
            hence \<open>(sum (\<lambda> t. (1/3::real)^(Suc t)) {n..n+p})  
                = (sum ((\<lambda> t. (1/3::real)^(Suc t))\<circ>((+) n)) {0..(n + p) - n})\<close> 
              by (rule Set_Interval.comm_monoid_add_class.sum.atLeastAtMost_shift_0)
            hence \<open>(sum (\<lambda> t. (1/3::real)^(Suc t)) {n..n+p})  
                = (sum (\<lambda> t. (1/3::real)^(Suc n+t)) {0..p})\<close> 
              by simp
            hence \<open>(sum (\<lambda> t. (1/3::real)^(Suc t)) {n..n+p})  
                = (sum (\<lambda> t. (1/3::real)^(Suc n)*(1/3::real)^t) {0..p})\<close>
              by (simp add: power_add) 
            hence \<open>(sum (\<lambda> t. (1/3::real)^(Suc t)) {n..n+p})  
                = (1/3::real)^(Suc n)*(sum (\<lambda> t. (1/3::real)^t) {0..p})\<close>
              by (simp add: sum_distrib_left)
            moreover have  \<open>(sum (\<lambda> t. (1/3::real)^t) {0..p}) \<le> (3/2::real)\<close>
            proof-
              have \<open>norm (1/3::real) < 1\<close>
                by simp
              hence \<open>(sum (\<lambda> t. (1/3::real)^t) {0..p}) = (1 - (1/3::real)^(Suc p))/(1 -  (1/3::real))\<close>
                using sum_gp0
                by (smt atMost_atLeast0 right_inverse_eq)
              also have \<open>... \<le> 1/(1 -  (1/3::real))\<close>
                by simp
              finally show ?thesis by simp
            qed
            ultimately have \<open>(sum (\<lambda> t. (1/3::real)^(Suc t) ) {n..n+p}) 
                  \<le> (1/3::real)^(Suc n)*(3/2)\<close>
              by (smt ordered_comm_semiring_class.comm_mult_left_mono zero_le_divide_1_iff zero_le_power)               
            thus ?thesis
              by simp 
          qed
          ultimately have \<open>(sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..n+p})
                           \<le> (1/2)*(1/3::real)^n\<close>
            for p::nat
            by smt
          hence \<open>m \<ge> n \<Longrightarrow> (sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..m})
                           \<le> (1/2)*(1/3::real)^n\<close>
            for m::nat
            using nat_le_iff_add by auto
          moreover have \<open>m < n \<Longrightarrow> (sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..m})
                           \<le> (1/2)*(1/3::real)^n\<close>
            for m::nat
            by simp
          ultimately have \<open>(sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..m})
                           \<le> (1/2)*(1/3::real)^n\<close>
            for m::nat
            by (metis (full_types) le_eq_less_or_eq less_or_eq_imp_le linorder_neqE_nat) 
          thus ?thesis by blast           
        qed
        thus ?thesis unfolding x_def by blast
      qed
      ultimately have \<open>norm (l - x n) \<le> (1/2)*(1/3::real)^n\<close>
        by (rule bound_telescopic )
      show ?thesis using x_def
        by (metis \<open>norm (l - x n) \<le> 1 / 2 * (1 / 3) ^ n\<close> norm_minus_commute) 
    qed
    have \<open>norm ((g n) l) \<ge> (1/6) * (1/3::real)^n * onorm (g n)\<close>
      for n
    proof-
      have \<open>norm ((g n) (\<phi> (Suc n))) = norm ( ((g n) l) + (g n) ((\<phi> (Suc n)) - l) )\<close>
      proof-
        have \<open>(g n) (\<phi> (Suc n)) = ((g n) l) + (g n) ((\<phi> (Suc n)) - l)\<close>
          using \<open>bounded_linear (g n)\<close>
          by (simp add: linear_simps(2)) 
        thus ?thesis by simp
      qed
      also have \<open>... \<le>  norm ((g n) l) + norm ((g n) ((\<phi> (Suc n)) - l))\<close>
        by (simp add: norm_triangle_ineq) 
      finally have \<open>norm ((g n) (\<phi> (Suc n))) \<le> norm ((g n) l) + norm ((g n) ((\<phi> (Suc n)) - l))\<close>
        by blast
      moreover have \<open>norm ((g n) ((\<phi> (Suc n)) - l)) \<le> onorm (g n) * norm ((\<phi> (Suc n)) - l)\<close>
      proof-
        have \<open>bounded_linear (g n)\<close>
          by (simp add: \<open>\<And>n. bounded_linear (g n)\<close>)          
        thus ?thesis using onorm by blast
      qed
      ultimately have \<open>norm ((g n) (\<phi> (Suc n))) \<le> norm ((g n) l) + onorm (g n) * norm ((\<phi> (Suc n)) - l)\<close>
        by simp
      also have \<open>... \<le>  norm ((g n) l) + onorm (g n) * ((1/2) * (1/3::real)^n) \<close>
      proof-
        have \<open>onorm (g n)  \<ge> 0\<close>
          by (simp add: \<open>\<And>n. bounded_linear (g n)\<close> onorm_pos_le)          
        hence \<open>onorm (g n) * norm ((\<phi> (Suc n)) - l) \<le> onorm (g n) * ((1/2) * (1/3::real)^n)\<close>
          using \<open>norm ((\<phi> (Suc n)) - l) \<le> (1/2)*(1/3::real)^n\<close>
          using mult_left_mono by blast
        thus ?thesis by simp
      qed
      finally have \<open>norm ((g n) (\<phi> (Suc n))) \<le> norm ((g n) l) + onorm (g n) * ((1/2) * (1/3::real)^n)\<close>
        by blast
      moreover have \<open>norm ((g n) (\<phi> (Suc n))) > (2/3) * (1/3)^n * onorm (g n)\<close>
      proof-
        from \<open>\<forall> n. \<forall> x. dist (\<Phi> n x) x <
         (1/3)^n \<and> norm ((g n) (\<Phi> n x)) > (2/3) * (1/3)^n * onorm (g n)\<close>
        have \<open>norm ((g n) (\<Phi> n x)) > (2/3) * (1/3)^n * onorm (g n)\<close>
          for x     
          by blast
        hence \<open>norm ((g n) (\<Phi> n (\<phi> n))) > (2/3) * (1/3)^n * onorm (g n)\<close>
          by blast
        thus ?thesis by (simp add: \<open>\<And>n. \<phi> (Suc n) = \<Phi> n (\<phi> n)\<close>)
      qed
      ultimately have \<open>(2/3) * (1/3)^n * onorm (g n) < norm ((g n) l) + onorm (g n) * ((1/2) * (1/3::real)^n)\<close>
        by simp
      hence \<open>(2/3) * (1/3)^n * onorm (g n) - onorm (g n) * ((1/2) * (1/3::real)^n)  < norm ((g n) l)\<close>
        by smt
      hence \<open>(2/3) * ((1/3)^n * onorm (g n)) - (1/2) * ((1/3::real)^n * onorm (g n))  < norm ((g n) l)\<close>
        by simp
      moreover have \<open>(2/3) * ((1/3)^n * onorm (g n)) - (1/2) * ((1/3::real)^n * onorm (g n))
          = (1/6) * (1/3)^n * onorm (g n)\<close>
        by simp
      ultimately have \<open>(1/6) * (1/3)^n * onorm (g n) < norm ((g n) l)\<close>
        by linarith
      thus ?thesis by simp
    qed
    moreover have \<open>(1/6) * (1/3::real)^n * onorm (g n) > (1/6) * (1/3::real)^n * 4^n\<close>
      for n
      using \<open>\<forall> n. onorm (g n) > 4^n\<close>
      by auto
    ultimately have \<open>norm ((g n) l) > (1/6) * (1/3::real)^n * 4^n\<close>
      for n
      by smt
    hence \<open>norm ((g n) l) > ereal((1/6) * (4/3::real)^n)\<close>
      for n
      by (simp add: power_divide) 
    moreover have \<open>(\<lambda> n::nat. ereal((1/6) * (4/3::real)^n) ) \<longlonglongrightarrow> \<infinity>\<close>
    proof-
      have \<open>norm (4/3::real) > 1\<close>
        by simp
      hence  \<open>(\<lambda> n::nat. ((4/3::real)^n)) \<longlonglongrightarrow> \<infinity>\<close>
        using LIMSEQ_realpow_inf by auto
      moreover have \<open>(1/6::real) > 0\<close>
        by simp
      ultimately have \<open>(\<lambda> n::nat. (1/6::real) * (4/3::real)^n ) \<longlonglongrightarrow> \<infinity>\<close>
        using LIMSEQ_scalarR
        by blast       
      thus ?thesis by blast
    qed
    ultimately show ?thesis using Lim_PInfty
    proof -
      obtain rr :: real where
        "\<forall>n. norm (g n l) \<le> rr"
        by (metis (no_types) \<open>\<And>thesis. (\<And>M. \<forall>n. norm (f n l) \<le> M \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>g \<equiv> \<lambda>n. f (k\<^sub>f n)\<close>)
      hence "\<forall>e. e \<le> ereal rr \<or> \<not> (\<lambda>n. ereal (1 / 6 * (4 / 3) ^ n)) \<longlonglongrightarrow> e"
        by (meson Lim_bounded \<open>\<And>n. ereal (1 / 6 * (4 / 3) ^ n) < ereal (norm (g n l))\<close> less_eq_ereal_def less_ereal_le)
      hence "\<infinity> \<le> ereal rr"
        using \<open>(\<lambda>n. ereal (1 / 6 * (4 / 3) ^ n)) \<longlonglongrightarrow> \<infinity>\<close> by blast
      thus ?thesis
        by simp
    qed 
  qed
  hence \<open>(\<lambda> n. norm ((f (k\<^sub>f n)) l)) \<longlonglongrightarrow> \<infinity>\<close>    
    using g_def by simp
  hence \<open>\<exists> N. norm ((f (k\<^sub>f N)) l) > M\<close>
    using Lim_bounded_PInfty2 \<open>\<forall>n. norm (f n l) \<le> M\<close> ereal_less_eq(3) by blast 
  then obtain N where \<open>norm ((f (k\<^sub>f N)) l) > M\<close>
    by blast
  have \<open>norm ((f (k\<^sub>f N)) l) \<le> M\<close>
    by (simp add: \<open>\<forall>n. norm (f n l) \<le> M\<close>)
  show ?thesis using  \<open>norm ((f (k\<^sub>f N)) l) > M\<close>  \<open>norm ((f (k\<^sub>f N)) l) \<le> M\<close>
    by linarith
qed

subsection \<open>Consequences of Banach-Steinhaus\<close>

corollary bounded_linear_limit_bounded_linear:
  fixes f :: \<open>nat \<Rightarrow> ('a::{banach, perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close>
    and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. bounded_linear (f n)\<close> and \<open>f \<midarrow>pointwise\<rightarrow> F\<close> 
  shows \<open>bounded_linear F\<close> 
proof-
  have \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
    using \<open>f \<midarrow>pointwise\<rightarrow> F\<close>
    by (simp add: pointwise_convergent_to_def)
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
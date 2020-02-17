(*
  File:   Banach_Steinhaus.thy
  Author: Dominique Unruh, University of Tartu
  Author: Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Banach-Steinhaus theorem\<close>

theory Banach_Steinhaus
  imports 
    Banach_Steinhaus_Missing
begin

text \<open>
  We formalize Banach-Steinhaus theorem as theorem @{text banach_steinhaus}.
\<close>

subsection \<open>Preliminaries for Sokal's proof of Banach-Steinhaus theorem\<close>

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

(* TODO: move? *)
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

text \<open>                 
  The following lemma is due to Alain Sokal ~\cite{sokal2011reall}.
\<close>
lemma sokal_banach_steinhaus:
  fixes f::"'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector" and r::real and x::'a 
  assumes \<open>r > 0\<close> and \<open>bounded_linear f\<close> 
  shows "onorm f \<le> (inverse r) * Sup ((norm \<circ> f) ` (ball x r) )"
proof-
  have \<open>onorm f = (inverse r) * Sup ((norm \<circ> f) ` (ball 0 r))\<close>
    using assms(1) assms(2) onorm_r by blast
  moreover have \<open>Sup ((norm \<circ> f) ` (ball 0 r)) \<le> Sup ( (\<lambda> \<xi>. norm (f \<xi>)) ` (ball x r) )\<close>
  proof-
    have \<open>(norm \<circ> f) \<xi> \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close> for \<xi>
      using linear_plus_norm \<open>bounded_linear f\<close>
      by (simp add: linear_plus_norm bounded_linear.linear)
    moreover have \<open>bdd_above ((\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) ` (ball 0 r))\<close> 
    proof-
      have \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close>
      proof-
        have \<open>ball (0::'a) r \<noteq> {}\<close>
          using assms(1) by auto          
        moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f x)) ` (ball 0 r))\<close>
          by auto          
        moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f \<xi>)) ` (ball 0 r))\<close>
        proof-
          obtain M where \<open>\<And> \<xi>. norm (f \<xi>) \<le> M * norm \<xi>\<close> and \<open>M \<ge> 0\<close>
            using \<open>bounded_linear f\<close> 
            by (metis bounded_linear.nonneg_bounded semiring_normalization_rules(7))            
          hence \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f \<xi>) \<le> M * r\<close>
            using \<open>r > 0\<close> by (smt mem_ball_0 mult_left_mono) 
          thus ?thesis
            by (meson bdd_aboveI2) 
        qed
        ultimately have \<open>bdd_above ((\<lambda> \<xi>. norm (f x) + norm (f \<xi>)) ` (ball 0 r))\<close>
          using bdd_above_plus[where S = "ball (0::'a) r" and f = "\<lambda> \<xi>. norm (f x)" 
              and g = "\<lambda> \<xi>. norm (f \<xi>)"] by simp
        then obtain M where \<open>\<And> \<xi>. \<xi> \<in> ball (0::'a) r \<Longrightarrow> norm (f x) + norm (f \<xi>) \<le> M\<close>
          unfolding bdd_above_def by (meson image_eqI)
        moreover have \<open>norm (f (x + \<xi>)) \<le> norm (f x) + norm (f \<xi>)\<close> for \<xi>
          by (simp add: assms(2) linear_simps(1) norm_triangle_ineq)          
        ultimately have \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> M\<close>
          by (simp add: assms(2) linear_simps(1) norm_triangle_le)          
        thus ?thesis
          by (meson bdd_aboveI2)                    
      qed
      moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f (x - \<xi>))) ` (ball 0 r))\<close>
      proof-
        obtain M where \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> M\<close>
          using  \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close>
          unfolding bdd_above_def
          by (meson image_eqI)
        moreover have \<open>\<xi> \<in> ball (0::'a) r \<Longrightarrow> -\<xi> \<in> ball 0 r\<close> for \<xi>
          using sphere_antipodal by auto
        ultimately show ?thesis
        proof -
          assume a1: "\<And>\<xi>. (\<xi>::'a) \<in> ball 0 r \<Longrightarrow> - \<xi> \<in> ball 0 r"
          assume "\<And>\<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> M"
          hence f2: "\<And>a. a \<notin> ball 0 r \<or> norm (f (a + x)) \<le> M"
            by (metis add.commute)
          have "\<forall>A f r. \<exists>a. (bdd_above (f ` A) \<or> (a::'a) \<in> A) \<and> (\<not> f a \<le> (r::real) \<or> bdd_above (f ` A))"
            by (metis bdd_aboveI2)
          thus ?thesis
            using f2 a1 by (metis uminus_add_conv_diff)
        qed       
      qed
      ultimately show ?thesis 
        unfolding  max_def
        apply auto
         apply (meson bdd_above_Int1 bdd_above_mono image_Int_subset)
        by (meson bdd_above_Int1 bdd_above_mono image_Int_subset)
    qed
    moreover have \<open>ball (0::'a) r \<noteq> {}\<close>
      using assms(1) by auto      
    ultimately have \<open>Sup ((norm \<circ> f) ` (ball 0 r)) \<le> 
          Sup ((\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) ` (ball 0 r))\<close>
      using cSUP_mono[where A = "ball (0::'a) r" and B = "ball (0::'a) r"
          and f = "norm \<circ> f" and g = "\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))"]
      by blast
    also have \<open>\<dots> = max (Sup ((\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r)))  
                        (Sup ((\<lambda> \<xi>. (norm (f (x - \<xi>)))) ` (ball 0 r)))\<close> 
    proof-
      have \<open>ball (0::'a) r \<noteq> {}\<close>
        using \<open>r > 0\<close> by auto
      moreover have \<open>bdd_above ((\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r)\<close>
      proof-
        have \<open>(\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r = (norm \<circ> f) ` ball x r\<close>
        proof -
          have "(\<lambda>a. norm (f (x + a))) ` ball 0 r = (\<lambda>a. (norm \<circ> f) (x + a)) ` ball 0 r"
            by (metis comp_apply)
          thus ?thesis
            by (metis (no_types) add.left_neutral image_add_ball image_image)
        qed
        moreover have \<open>bdd_above ((norm \<circ> f) ` ball x r)\<close>
        proof-
          have \<open>bounded (ball x r)\<close>
            by simp            
          hence \<open>bounded ((norm \<circ> f) ` ball x r)\<close>
            using \<open>bounded_linear f\<close> bounded_linear_image bounded_norm_comp by auto 
          thus ?thesis
            by (simp add: bounded_imp_bdd_above)          
        qed
        ultimately show ?thesis 
          by simp
      qed
      moreover have \<open>bdd_above ((\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r)\<close>
      proof-
        have \<open>(\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r = (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close>
        proof auto
          show \<open>norm \<xi> < r \<Longrightarrow>
         norm (f (x - \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close> for \<xi>
          proof-
            assume \<open>norm \<xi> < r\<close>
            hence \<open>\<xi> \<in> ball (0::'a) r\<close>
              by auto
            hence \<open>-\<xi> \<in> ball (0::'a) r\<close>
              by auto
            thus ?thesis
              by (metis (no_types, lifting) ab_group_add_class.ab_diff_conv_add_uminus image_iff) 
          qed
          show \<open>norm \<xi> < r \<Longrightarrow>
         norm (f (x + \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r\<close> for \<xi>
          proof-
            assume \<open>norm \<xi> < r\<close>
            hence \<open>\<xi> \<in> ball (0::'a) r\<close>
              by auto
            hence \<open>-\<xi> \<in> ball (0::'a) r\<close>
              by auto
            thus ?thesis
              by (metis (no_types, lifting) diff_minus_eq_add image_iff)
          qed
        qed
        thus ?thesis
          by (simp add: calculation(2)) 
      qed
      ultimately show ?thesis
        using max_Sup[where X = "ball (0::'a) r" and f = "\<lambda> \<xi>. (norm (f (x + \<xi>)))" 
            and g = "\<lambda> \<xi>. (norm (f (x - \<xi>)))"] by blast
    qed
    also have \<open>\<dots> = Sup ((\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r))\<close>
    proof-
      have \<open>(\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r) = (\<lambda> \<xi>. (norm (f (x - \<xi>)))) ` (ball 0 r)\<close>
      proof auto
        show \<open>norm \<xi> < r \<Longrightarrow>
         norm (f (x + \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r\<close> for \<xi>
        proof-
          assume \<open>norm \<xi> < r\<close>
          have \<open>norm (f (x + \<xi>)) = norm (f (x - (- \<xi>)))\<close>
            by simp
          moreover have \<open>-\<xi> \<in> ball 0 r\<close>
            by (simp add: \<open>norm \<xi> < r\<close>)            
          ultimately show ?thesis
            by blast             
        qed
        show  \<open>norm \<xi> < r \<Longrightarrow>
         norm (f (x - \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close> for \<xi>
        proof-
          assume \<open>norm \<xi> < r\<close>
          have \<open>norm (f (x - \<xi>)) = norm (f (x + (- \<xi>)))\<close>
            by simp
          moreover have \<open>-\<xi> \<in> ball 0 r\<close>
            by (simp add: \<open>norm \<xi> < r\<close>)            
          ultimately show ?thesis
            by blast             
        qed
      qed
      hence \<open>Sup ((\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r)) 
          = Sup ((\<lambda> \<xi>. (norm (f (x - \<xi>)))) ` (ball 0 r))\<close>
        by simp
      thus ?thesis 
        by auto
    qed
    also have \<open>\<dots> = Sup ((\<lambda> \<xi>. (norm (f \<xi>))) ` (ball x r))\<close>
      by (metis  add.right_neutral ball_translation image_image)      
    finally show ?thesis
      by blast
  qed
  ultimately show ?thesis
    by (simp add: assms(1))    
qed

subsection \<open>Banach-Steinhaus theorem\<close>

text \<open>Reference: @{cite sokal2011really}\<close>
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
    assume \<open>bounded_linear h\<close>  \<open>r > 0\<close>
    hence \<open>onorm h \<le> (inverse r) * Sup ( (norm \<circ> h) ` (ball x r) )\<close>
      using sokal_banach_steinhaus[where r = r and f = h] 
      by auto      
    hence \<open>r * onorm h \<le> Sup ( (norm \<circ> h) ` (ball x r) )\<close>
      sorry
    assume \<open>0 < onorm h\<close>
    have \<open>(2/3) * r * onorm h < Sup ( (norm \<circ> h) ` (ball x r) )\<close>
      sorry
    moreover have \<open>(norm \<circ> h) ` (ball x r) \<noteq> {}\<close>
      sorry
    moreover have \<open>bdd_above ((norm \<circ> h) ` (ball x r))\<close>
      sorry
    ultimately have \<open>\<exists> t \<in> (norm \<circ> h) ` (ball x r). (2/3) * r * onorm h <  t\<close>
      using less_cSup_iff
      sorry
    hence \<open>\<exists> s \<in> ball x r. (2/3) * r * onorm h < norm (h s)\<close>
      sorry
    hence \<open>\<exists> y. dist y x < r \<and> (2/3) * r * onorm h < norm (h y)\<close>
      sorry
    hence \<open>\<exists> y. dist y x < r \<and> (2/3) * r * onorm h < norm (h y)\<close>
      sorry
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

(*
  File:   Banach_Steinhaus.thy
  Author: Dominique Unruh, University of Tartu
  Author: Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Banach-Steinhaus theorem\<close>
  (*
subjective perfection = between 90% and 100% (Jose)
*)

theory Banach_Steinhaus
  imports 
    Banach_Steinhaus_Missing
    Real_Bounded_Operators
    "HOL-ex.Sketch_and_Explore"
begin

text \<open>
  We formalize Banach-Steinhaus theorem as theorem @{text banach_steinhaus}.
\<close>

subsection \<open>Preliminaries for Sokal's proof of Banach-Steinhaus theorem\<close>

text \<open>                 
  The following lemma is due to Alain Sokal ~\cite{sokal2011reall}.
\<close>
lemma sokal_banach_steinhaus:
  "r > 0 \<Longrightarrow> norm f \<le> (inverse r) * Sup ( (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) )"
proof transfer
  fix r::real and f::\<open>'a \<Rightarrow> 'b\<close> and x::'a
  assume \<open>r > 0\<close> and \<open>bounded_linear f\<close>
  {
    obtain M where \<open>\<And> \<xi>. norm (f \<xi>) \<le> M * norm \<xi>\<close> and \<open>M \<ge> 0\<close>
      using \<open>bounded_linear f\<close> 
      by (metis bounded_linear.nonneg_bounded semiring_normalization_rules(7))
    hence \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f \<xi>) \<le> M * r\<close>
      using \<open>r > 0\<close> by (smt mem_ball_0 mult_left_mono) 
    hence \<open>bdd_above ((\<lambda> \<xi>. norm (f \<xi>)) ` (ball 0 r))\<close>
      by (meson bdd_aboveI2)     
  } note bdd_above_3 = this
  {
    have \<open>ball (0::'a) r \<noteq> {}\<close>
      using \<open>0 < r\<close> by auto          
    moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f x)) ` (ball 0 r))\<close>
      by auto          
    moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f \<xi>)) ` (ball 0 r))\<close>
      using bdd_above_3 by blast
    ultimately have \<open>bdd_above ((\<lambda> \<xi>. norm (f x) + norm (f \<xi>)) ` (ball 0 r))\<close>
      using bdd_above_plus[where S = "ball (0::'a) r" and f = "\<lambda> \<xi>. norm (f x)" 
          and g = "\<lambda> \<xi>. norm (f \<xi>)"] by simp
    then obtain M where \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f x) + norm (f \<xi>) \<le> M\<close>
      unfolding bdd_above_def by (meson image_eqI)
    moreover have \<open>norm (f (x + \<xi>)) \<le> norm (f x) + norm (f \<xi>)\<close> for \<xi>
      by (simp add: \<open>bounded_linear f\<close> linear_simps(1) norm_triangle_ineq)          
    ultimately have \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> M\<close>
      by (simp add:  \<open>bounded_linear f\<close> linear_simps(1) norm_triangle_le)          
    hence \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close>
      by (meson bdd_aboveI2)                          
  } note bdd_above_2 = this
  {
    obtain K where \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> K\<close>
      using  \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close> unfolding bdd_above_def 
      by (meson image_eqI)
    have \<open>\<xi> \<in> ball (0::'a) r \<Longrightarrow> -\<xi> \<in> ball 0 r\<close> for \<xi>
      using sphere_antipodal by auto
    hence \<open>bdd_above ((\<lambda> \<xi>. norm (f (x - \<xi>))) ` (ball 0 r))\<close>
      by (metis \<open>\<And>\<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> K\<close> 
          ab_group_add_class.ab_diff_conv_add_uminus bdd_aboveI2)        
  } note bdd_above_4 = this
  {
    have \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close>
      using bdd_above_2 by blast
    moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f (x - \<xi>))) ` (ball 0 r))\<close>
      using bdd_above_4 by blast
    ultimately have \<open>bdd_above ((\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) ` (ball 0 r))\<close>
      unfolding max_def apply auto apply (meson bdd_above_Int1 bdd_above_mono image_Int_subset)
      by (meson bdd_above_Int1 bdd_above_mono image_Int_subset)   
  } note bdd_above_1 = this
  {
    have \<open>bounded (ball x r)\<close>
      by simp            
    hence \<open>bounded ((norm \<circ> f) ` ball x r)\<close>
      using \<open>bounded_linear f\<close> bounded_linear_image bounded_norm_comp by auto
    hence \<open>bdd_above ((norm \<circ> f) ` ball x r)\<close>
      by (simp add: bounded_imp_bdd_above)
  } note bdd_above_6 = this
  {
    have "(\<lambda>a. norm (f (x + a))) ` ball 0 r = (\<lambda>a. (norm \<circ> f) (x + a)) ` ball 0 r"
      by (metis comp_apply)
    hence \<open>(\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r = (norm \<circ> f) ` ball x r\<close>
      by (metis (no_types) add.left_neutral image_add_ball image_image)
  } note norm_1 = this
  {
    have \<open>(\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r = (norm \<circ> f) ` ball x r\<close>
      using norm_1 by blast
    moreover have \<open>bdd_above ((norm \<circ> f) ` ball x r)\<close>
      using bdd_above_6 by blast
    ultimately have \<open>bdd_above ((\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r)\<close> 
      by simp
  } note bdd_above_5 = this
  {
    fix \<xi>::'a
    assume \<open>norm \<xi> < r\<close>
    hence \<open>\<xi> \<in> ball (0::'a) r\<close>
      by auto
    hence \<open>-\<xi> \<in> ball (0::'a) r\<close>
      by auto
    hence \<open>norm \<xi> < r \<Longrightarrow> norm (f (x - \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close> 
      by (metis (no_types, lifting) ab_group_add_class.ab_diff_conv_add_uminus image_iff) 
  } note norm_2 = this
  {
    fix \<xi>::'a
    assume \<open>norm \<xi> < r\<close>
    hence \<open>\<xi> \<in> ball (0::'a) r\<close>
      by auto
    hence \<open>-\<xi> \<in> ball (0::'a) r\<close>
      by auto
    hence \<open>norm \<xi> < r \<Longrightarrow> norm (f (x + \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r\<close> 
      by (metis (no_types, lifting) diff_minus_eq_add image_iff)          
  } note norm_2' = this
  {
    have \<open>(\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r = (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close>
      apply auto using norm_2 apply auto using norm_2' by auto 
    hence \<open>bdd_above ((\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r)\<close>
      using bdd_above_4 by blast       
  } note bdd_above_6 = this
  {
    have \<open>ball (0::'a) r \<noteq> {}\<close>
      using \<open>r > 0\<close> by auto
    moreover have \<open>bdd_above ((\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r)\<close>
      using bdd_above_5 by blast
    moreover have \<open>bdd_above ((\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r)\<close>
      using bdd_above_6 by blast
    ultimately have \<open>(SUP \<xi>\<in>ball 0 r. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) =
                 max (SUP \<xi>\<in>ball 0 r. norm (f (x + \<xi>))) (SUP \<xi>\<in>ball 0 r. norm (f (x - \<xi>)))\<close>
      using max_Sup[where X = "ball (0::'a) r" and f = "\<lambda> \<xi>. (norm (f (x + \<xi>)))" 
          and g = "\<lambda> \<xi>. (norm (f (x - \<xi>)))"] by blast    
  } note Sup_2 = this
  {
    fix \<xi>::'a
    assume \<open>norm \<xi> < r\<close>
    have \<open>norm (f (x + \<xi>)) = norm (f (x - (- \<xi>)))\<close>
      by simp
    moreover have \<open>-\<xi> \<in> ball 0 r\<close>
      by (simp add: \<open>norm \<xi> < r\<close>)            
    ultimately have \<open>norm \<xi> < r \<Longrightarrow> norm (f (x + \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r\<close>
      by blast
  } note Sup_3' = this
  {
    fix \<xi>::'a
    assume \<open>norm \<xi> < r\<close>
    have \<open>norm (f (x - \<xi>)) = norm (f (x + (- \<xi>)))\<close>
      by simp
    moreover have \<open>-\<xi> \<in> ball 0 r\<close>
      by (simp add: \<open>norm \<xi> < r\<close>)            
    ultimately have \<open>norm \<xi> < r \<Longrightarrow> norm (f (x - \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close>
      by blast             
  } note Sup_3'' = this
  {
    have \<open>(\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r) = (\<lambda> \<xi>. (norm (f (x - \<xi>)))) ` (ball 0 r)\<close>
      apply auto using Sup_3' apply auto using Sup_3'' by blast
    hence \<open>Sup ((\<lambda> \<xi>.(norm (f (x + \<xi>)))) ` (ball 0 r))=Sup ((\<lambda> \<xi>.(norm (f (x - \<xi>)))) ` (ball 0 r))\<close>
      by simp
    hence \<open>max (SUP \<xi>\<in>ball 0 r. norm (f (x + \<xi>))) (SUP \<xi>\<in>ball 0 r. norm (f (x - \<xi>))) =
        (SUP \<xi>\<in>ball 0 r. norm (f (x + \<xi>)))\<close> 
      by auto
  } note Sup_3 = this
  {
    have \<open>(norm \<circ> f) \<xi> \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close> for \<xi>
      using linear_plus_norm \<open>bounded_linear f\<close> 
      by (simp add: linear_plus_norm bounded_linear.linear)
    moreover have \<open>bdd_above ((\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) ` (ball 0 r))\<close> 
      using bdd_above_1 by blast
    moreover have \<open>ball (0::'a) r \<noteq> {}\<close>
      using \<open>r > 0\<close> by auto      
    ultimately have \<open>Sup ((norm \<circ> f) ` (ball 0 r)) \<le>
                     Sup ((\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) ` (ball 0 r))\<close>
      using cSUP_mono[where A = "ball (0::'a) r" and B = "ball (0::'a) r" and f = "norm \<circ> f" and 
          g = "\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))"] by blast
    also have \<open>\<dots> = max (Sup ((\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r)))
                        (Sup ((\<lambda> \<xi>. (norm (f (x - \<xi>)))) ` (ball 0 r)))\<close> 
      using Sup_2 by blast
    also have \<open>\<dots> = Sup ((\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r))\<close>
      using Sup_3 by blast
    also have \<open>\<dots> = Sup ((\<lambda> \<xi>. (norm (f \<xi>))) ` (ball x r))\<close>
      by (metis  add.right_neutral ball_translation image_image)      
    finally have \<open>Sup ((norm \<circ> f) ` (ball 0 r)) \<le> Sup ( (\<lambda> \<xi>. norm (f \<xi>)) ` (ball x r) )\<close> by blast
  } note Sup_1 = this
  have \<open>onorm f = (inverse r) * Sup ((norm \<circ> f) ` (ball 0 r))\<close>
    using \<open>0 < r\<close> \<open>bounded_linear f\<close> onorm_r by blast
  moreover have \<open>Sup ((norm \<circ> f) ` (ball 0 r)) \<le> Sup ( (\<lambda> \<xi>. norm (f \<xi>)) ` (ball x r) )\<close>
    using Sup_1 by blast
  ultimately show \<open>onorm f \<le> inverse r * Sup ((norm \<circ> f) ` ball x r)\<close>
    by (simp add: \<open>r > 0\<close>)    
qed

text \<open>                 
  In the proof of Banach-Steinhaus theorem, we will use the following variation of
  the lemma @{thm sokal_banach_steinhaus}.
\<close>

lemma sokal_banach_steinhaus':
  "\<lbrakk>r > 0; \<tau> < 1; f \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>\<xi>\<in>ball x r.  \<tau> * r * norm f \<le> norm (f *\<^sub>v \<xi>)"
proof-
  assume \<open>r > 0\<close> and \<open>\<tau> < 1\<close> and \<open>f \<noteq> 0\<close>
  have  \<open>norm f > 0\<close>
    using \<open>f \<noteq> 0\<close> by auto
  have \<open>norm f \<le> (inverse r) * Sup ( (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) )\<close>
    using \<open>r > 0\<close> sokal_banach_steinhaus by blast
  hence \<open>r * norm f \<le> r * (inverse r) * Sup ( (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) )\<close>
    using \<open>r > 0\<close> by (smt linordered_field_class.sign_simps(4) mult_left_less_imp_less) 
  hence \<open>r * norm f \<le> Sup ( (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) )\<close>
    using \<open>0 < r\<close> by auto
  moreover have \<open>\<tau> * r * norm f < r * norm f\<close>
    using  \<open>\<tau> < 1\<close> using \<open>0 < norm f\<close> \<open>0 < r\<close> by auto
  ultimately have \<open>\<tau> * r * norm f < Sup ( (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) )\<close>
    by simp
  moreover have \<open>(norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) \<noteq> {}\<close>
    using \<open>0 < r\<close> by auto    
  moreover have \<open>bdd_above ((norm \<circ> ( (*\<^sub>v) f)) ` (ball x r))\<close>
    using \<open>0 < r\<close> apply transfer by (meson bounded_linear_ball_bdd_above)    
  ultimately have \<open>\<exists>t \<in> (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r). \<tau> * r * norm f < t\<close> 
    by (simp add: less_cSup_iff)    
  thus ?thesis by (smt comp_def image_iff) 
qed

subsection \<open>Banach-Steinhaus theorem\<close>

theorem banach_steinhaus:
  \<open>\<lbrakk>\<And>x. bounded (range (\<lambda>n. (f n) *\<^sub>v x))\<rbrakk> \<Longrightarrow> bounded (range f)\<close>
  for f::\<open>'c \<Rightarrow> ('a::banach, 'b::real_normed_vector) real_bounded\<close>
proof-
  {
    assume \<open>\<not>(bounded (range f))\<close> and \<open>\<And>x. bounded (range (\<lambda>n. f n *\<^sub>v x))\<close>
    {
      have \<open>summable (\<lambda>n. (inverse (real_of_nat 3))^n)\<close>
        using Series.summable_geometric_iff [where c = "inverse (real_of_nat 3)"] by auto
      moreover have \<open>(inverse (real_of_nat 3))^n = inverse (real_of_nat 3^n)\<close> for n::nat
        using power_inverse by blast        
      ultimately have \<open>summable (\<lambda>n. inverse (real_of_nat 3^n))\<close>
        by auto
      hence \<open>bounded (range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n}))\<close>
        using summable_imp_sums_bounded[where f = "(\<lambda>n. inverse (real_of_nat 3^n))"]
          lessThan_atLeast0 by auto
      hence \<open>\<exists>M. \<forall>h\<in>(range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n})). norm h \<le> M\<close>
        using bounded_iff by blast
      then obtain M where \<open>h\<in>range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n}) \<Longrightarrow> norm h \<le> M\<close> 
        for h
        by blast      
      {
        fix n
        have  \<open>norm (sum (\<lambda> k. inverse (real 3 ^ k)) {0..< Suc n}) \<le> M\<close>
          using \<open>\<And>h. h\<in>(range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n})) \<Longrightarrow> norm h \<le> M\<close> 
          by blast
        hence  \<open>norm (sum (\<lambda> k. inverse (real 3 ^ k)) {0..n}) \<le> M\<close>
          by (simp add: atLeastLessThanSuc_atLeastAtMost)        
        hence  \<open>(sum (\<lambda> k. inverse (real 3 ^ k)) {0..n}) \<le> M\<close>
          by auto
        hence \<open>sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> M\<close> by blast
      } note sum_2 = this
      have \<open>sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> M\<close> for n 
        using sum_2 by blast
      hence \<open>\<exists>K. \<forall>n. sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> K\<close> 
        by blast
    } note sum_1 = this
    have \<open>of_rat 2/3 < (1::real)\<close>
      by auto
    hence \<open>\<forall>g::('a, 'b) real_bounded. \<forall>x. \<forall>r. \<exists>\<xi>. g \<noteq> 0 \<and> r > 0
               \<longrightarrow> (\<xi>\<in>ball x r \<and> (of_rat 2/3) * r * norm g \<le> norm (g *\<^sub>v \<xi>))\<close> 
      using sokal_banach_steinhaus' by blast
    hence \<open>\<exists>\<xi>. \<forall>g::('a, 'b) real_bounded. \<forall>x. \<forall>r. g \<noteq> 0 \<and> r > 0
               \<longrightarrow> ((\<xi> g x r)\<in>ball x r \<and> (of_rat 2/3) * r * norm g \<le> norm (g *\<^sub>v (\<xi> g x r)))\<close> 
      by metis
    then obtain \<xi> where f1: \<open>\<lbrakk>g \<noteq> 0; r > 0\<rbrakk> \<Longrightarrow> 
        \<xi> g x r \<in> ball x r \<and>  (of_rat 2/3) * r * norm g \<le> norm (g *\<^sub>v (\<xi> g x r))\<close>
      for g::\<open>('a, 'b) real_bounded\<close> and x and r
      by blast
    have \<open>\<forall>n. \<exists>k. norm (f k) \<ge> 4^n\<close>
      using \<open>\<not>(bounded (range f))\<close> by (metis (mono_tags, hide_lams) boundedI image_iff linear)
    hence  \<open>\<exists>k. \<forall>n. norm (f (k n)) \<ge> 4^n\<close>
      by metis
    hence  \<open>\<exists>k. \<forall>n. norm ((f \<circ> k) n) \<ge> 4^n\<close>
      by simp
    then obtain k where \<open>norm ((f \<circ> k) n) \<ge> 4^n\<close> for n
      by blast
    define T where \<open>T = f \<circ> k\<close>
    have \<open>T n \<in> range f\<close> for n
      unfolding T_def by simp        
    have \<open>norm (T n) \<ge> of_nat (4^n)\<close> for n
      unfolding T_def using \<open>\<And> n. norm ((f \<circ> k) n) \<ge> 4^n\<close> by auto
    hence \<open>T n \<noteq> 0\<close> for n
      by (smt T_def \<open>\<And>n. 4 ^ n \<le> norm ((f \<circ> k) n)\<close> norm_zero power_not_zero zero_le_power)
    have \<open>inverse (of_nat 3^n) > (0::real)\<close> for n
      by auto
    define y::\<open>nat \<Rightarrow> 'a\<close> where \<open>y = rec_nat 0 (\<lambda>n x. \<xi> (T n) x (inverse (of_nat 3^n)))\<close>
    have \<open>y (Suc n) \<in> ball (y n) (inverse (of_nat 3^n))\<close> for n
      using f1 \<open>\<And> n. T n \<noteq> 0\<close> \<open>\<And> n. inverse (of_nat 3^n) > 0\<close> unfolding y_def by auto
    hence \<open>norm (y (Suc n) - y n) \<le> inverse (of_nat 3^n)\<close> for n
      unfolding ball_def apply auto using dist_norm by (smt norm_minus_commute) 
    moreover have \<open>\<exists>K. \<forall>n. sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> K\<close>
      using sum_1 by blast
    moreover have \<open>Cauchy y\<close>
      using convergent_series_Cauchy[where a = "\<lambda>n. inverse (of_nat 3^n)" and \<phi> = y] dist_norm
      by (metis calculation(1) calculation(2))
    hence \<open>\<exists> x. y \<longlonglongrightarrow> x\<close>
      by (simp add: convergent_eq_Cauchy)
    then obtain x where \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    { 
      fix n
      have \<open>inverse (real_of_nat 3) < 1\<close>
        by simp        
      moreover have \<open>y 0 = 0\<close>
        using y_def by auto
      ultimately have \<open>norm (x - y (Suc n)) 
    \<le> (inverse (of_nat 3)) * inverse (1 - (inverse (of_nat 3))) * ((inverse (of_nat 3)) ^ n)\<close>
        using bound_Cauchy_to_lim[where c = "inverse (of_nat 3)" and y = y and x = x]
          power_inverse semiring_norm(77)  \<open>y \<longlonglongrightarrow> x\<close>
          \<open>\<And> n. norm (y (Suc n) - y n) \<le> inverse (of_nat 3^n)\<close> by metis
      moreover have \<open>inverse (real_of_nat 3) * inverse (1 - (inverse (of_nat 3)))
                   = inverse (of_nat 2)\<close>
        by auto
      ultimately have \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close>
        by (metis power_inverse) 
    } note norm_2 = this
    have \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close> for n
      using norm_2 by blast
    have \<open>\<exists> M. \<forall> n. norm (T n *\<^sub>v x) \<le> M\<close>
      unfolding T_def apply auto
      by (metis \<open>\<And>x. bounded (range (\<lambda>n. f n *\<^sub>v x))\<close> bounded_iff rangeI)
    then obtain M where \<open>norm (T n *\<^sub>v x) \<le> M\<close> for n
      by blast
    {
      fix n   
      have \<open>norm (y (Suc n) - x) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close>
        using \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close> 
        by (simp add: norm_minus_commute)
      moreover have \<open>norm (T n) \<ge> 0\<close>
        by auto
      ultimately have \<open>norm (T n) * norm (y (Suc n) - x) 
                     \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))*norm (T n)\<close>
        by (simp add: \<open>\<And>n. T n \<noteq> 0\<close>)
      hence \<open>norm (T n) * norm (y (Suc n) - x) + norm (T n *\<^sub>v x)
    \<le> inverse (real 2) * inverse (real 3 ^ n) * norm (T n) + norm (T n *\<^sub>v x)\<close> by simp      
    } note norm_1 = this
    { 
      fix n
      have \<open>(of_rat 2/3)*(inverse (of_nat 3^n)) * norm (T n) \<le> norm ((T n) *\<^sub>v (y (Suc n)))\<close> 
        using f1 \<open>\<And> n. T n \<noteq> 0\<close> \<open>\<And> n. inverse (of_nat 3^n) > 0\<close> unfolding y_def by auto
      also have \<open>\<dots> = norm ((T n) *\<^sub>v ((y (Suc n) - x) + x))\<close>
        by auto
      also have \<open>\<dots> = norm ((T n) *\<^sub>v (y (Suc n) - x) + (T n) *\<^sub>v x)\<close>
        apply transfer apply auto by (metis diff_add_cancel linear_simps(1))
      also have \<open>\<dots> \<le> norm ((T n) *\<^sub>v (y (Suc n) - x)) + norm ((T n) *\<^sub>v x)\<close>
        by (simp add: norm_triangle_ineq)
      also have \<open>\<dots> \<le> norm (T n) * norm (y (Suc n) - x) + norm ((T n) *\<^sub>v x)\<close>
        apply transfer apply auto using onorm by auto 
      also have \<open>\<dots> \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))*norm (T n) + norm ((T n) *\<^sub>v x)\<close>
        using norm_1 by blast
      finally have \<open>(of_rat 2/3) * inverse (real 3 ^ n) * norm (T n)
                \<le> inverse (real 2) * inverse (real 3 ^ n) * norm (T n) + norm (T n *\<^sub>v x)\<close>
        by blast
      hence \<open>(of_rat 2/3) * inverse (real 3 ^ n) * norm (T n) 
             - inverse (real 2) * inverse (real 3 ^ n) * norm (T n) \<le> norm (T n *\<^sub>v x)\<close>
        by linarith
      hence \<open>(inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n) \<le> norm (T n *\<^sub>v x)\<close>
        by (simp add: linordered_field_class.sign_simps(5))                
    } note inverse_2 = this
    {
      fix n
      have \<open>of_rat (4/3)^n = inverse (real 3 ^ n) * (of_nat 4^n)\<close>
        apply auto by (metis divide_inverse_commute of_rat_divide power_divide of_rat_numeral_eq) 
      also have \<open>\<dots> \<le>  inverse (real 3 ^ n) * norm (T n)\<close>
        using \<open>\<And>n. norm (T n) \<ge> of_nat (4^n)\<close> by simp
      finally have \<open>of_rat (4/3)^n \<le> inverse (real 3 ^ n) * norm (T n)\<close>
        by blast
      moreover have \<open>inverse (of_nat 6) > (0::real)\<close>
        by auto
      ultimately have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) 
                    \<le> (inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n)\<close> by auto
    } note inverse_3 = this
    {
      fix n
      have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) 
          \<le> (inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n)\<close> 
        using inverse_3 by blast
      also have \<open>\<dots> \<le> norm (T n *\<^sub>v x)\<close> 
        using inverse_2 by blast
      finally have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> norm (T n *\<^sub>v x)\<close>
        by auto
      hence \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> M\<close> 
        using \<open>\<And> n. norm (T n *\<^sub>v x) \<le> M\<close> by smt
    } note inverse_1 = this
    have \<open>\<exists>n. M < (inverse (of_nat 6)) * (of_rat (4/3)^n)\<close>
      by (simp add: Elementary_Topology.real_arch_pow)
    moreover have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> M\<close> for n
      using inverse_1 by blast                      
    ultimately have False
      by smt
  } note main = this
  assume \<open>\<And>x. bounded (range (\<lambda>n. (f n) *\<^sub>v x))\<close> thus ?thesis using main by blast
qed

subsection \<open>A consequence of Banach-Steinhaus theorem\<close>

text\<open>
  We define the pointwise convergence of a sequence of real bounded operators.
\<close>
lift_definition real_bounded_pointwise::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded) \<Rightarrow> ('a, 'b) real_bounded
  \<Rightarrow> bool\<close> (\<open>((_)/ \<midarrow>Pointwise\<rightarrow> (_))\<close> [60, 60] 60)
  is pointwise_convergent_to.

text\<open>
  An important consequence of Banach-Steinhaus theorem is that if a sequence of bounded operators 
  converges pointwise, then the limit is a bounded operator too.
\<close>
corollary bounded_linear_limit_bounded_linear:
  \<open>\<lbrakk>\<And>x. convergent (\<lambda>n. (f n) *\<^sub>v x)\<rbrakk> \<Longrightarrow> \<exists>g. f \<midarrow>Pointwise\<rightarrow> g\<close>
  for f::\<open>nat \<Rightarrow> ('a::{banach, perfect_space}, 'b::real_normed_vector) real_bounded\<close>
proof-
  assume \<open>\<And>x. convergent (\<lambda>n. (f n) *\<^sub>v x)\<close>
  hence \<open>\<exists>l. (\<lambda>n. (f n) *\<^sub>v x) \<longlonglongrightarrow> l\<close> for x
    by (simp add: convergentD)
  hence \<open>\<exists>F. (\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close>
    unfolding pointwise_convergent_to_def by metis
  obtain F where \<open>(\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close>
    using \<open>\<exists>F. (\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close> by auto
  have \<open>\<And>x. (\<lambda> n. (f n) *\<^sub>v x) \<longlonglongrightarrow> F x\<close>
    using \<open>(\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close> apply transfer
    by (simp add: pointwise_convergent_to_def)
  {
    assume \<open>\<And>x. \<exists>M. \<forall>n. norm ((f n) *\<^sub>v x) \<le> M\<close>
    have \<open>bounded (range (\<lambda>n. (f n)*\<^sub>v x))\<close> for x
      using  \<open>\<And>x. \<exists>M. \<forall>n. norm ((f n) *\<^sub>v x) \<le> M\<close>
      by (metis (no_types, lifting) boundedI rangeE)
    hence \<open>bounded (range f)\<close>
      using banach_steinhaus by blast
    hence \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close> unfolding bounded_def
      by (meson UNIV_I \<open>bounded (range f)\<close> bounded_iff image_eqI) 
  } note norm_f_n = this
  {
    have \<open>isCont (\<lambda> t::'b. norm t) y\<close> for y::'b
      using Limits.isCont_norm by simp
    hence \<open>(\<lambda> n. norm ((f n) *\<^sub>v x)) \<longlonglongrightarrow> (norm (F x))\<close>
      using \<open>\<And> x::'a. (\<lambda> n. (f n) *\<^sub>v x) \<longlonglongrightarrow> F x\<close> by (simp add: tendsto_norm)
    hence \<open>\<exists> M. \<forall> n. norm ((f n) *\<^sub>v x) \<le> M\<close> for x 
      using Elementary_Metric_Spaces.convergent_imp_bounded
      by (metis UNIV_I \<open>\<And> x::'a. (\<lambda> n. (f n) *\<^sub>v x) \<longlonglongrightarrow> F x\<close> bounded_iff image_eqI)
  } note norm_f_n_x = this
  {
    have \<open>\<exists> M. \<forall> n. norm ((f n) *\<^sub>v x) \<le> M\<close> for x
      using norm_f_n_x  \<open>\<And>x. (\<lambda>n. f n *\<^sub>v x) \<longlonglongrightarrow> F x\<close> by blast
    hence \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
      using norm_f_n by simp 
    then obtain M::real where \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
      by blast
    have \<open>\<forall> n. \<forall>x. norm ((f n) *\<^sub>v x) \<le> norm x * norm (f n)\<close>
      apply transfer apply auto by (metis mult.commute onorm) 
    hence "\<exists>K. \<forall>n. \<forall>x. norm ((f n) *\<^sub>v x) \<le> norm x * K" using \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
      by (metis (no_types, hide_lams) dual_order.trans norm_eq_zero order_refl real_mult_le_cancel_iff2 vector_space_over_itself.scale_zero_left zero_less_norm_iff)
  } note norm_f = this
  { 
    have "\<exists>K. \<forall>n. \<forall>x. norm ((f n) *\<^sub>v x) \<le> norm x * K"
      using norm_f \<open>\<And>x. (\<lambda>n. f n *\<^sub>v x) \<longlonglongrightarrow> F x\<close> by auto
    hence "\<exists>K. \<forall>x. norm (F x) \<le> norm x * K"
      using  \<open>\<And> x::'a. (\<lambda> n. (f n) *\<^sub>v  x) \<longlonglongrightarrow> F x\<close> apply transfer 
      by (metis Lim_bounded tendsto_norm)   
  } note norm_F_x = this
  have \<open>linear F\<close>
    using  \<open>(\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close>
    apply transfer apply auto using bounded_linear.linear linear_limit_linear by blast
  moreover have \<open>bounded_linear_axioms F\<close>
    using norm_F_x by (simp add: \<open>\<And>x. (\<lambda>n. f n *\<^sub>v x) \<longlonglongrightarrow> F x\<close> bounded_linear_axioms_def) 
  ultimately have \<open>bounded_linear F\<close> 
    unfolding bounded_linear_def by blast
  hence \<open>\<exists>g. (*\<^sub>v) g = F\<close>
    using Abs_real_bounded_inverse by auto
  thus ?thesis
    using \<open>(\<lambda>n. (*\<^sub>v) (f n)) \<midarrow>pointwise\<rightarrow> F\<close> apply transfer by auto
qed

end

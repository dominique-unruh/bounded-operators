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
  assumes \<open>\<And> n. bounded_linear (f n)\<close> and  \<open>\<And> x. \<exists> M. \<forall> n.  norm ((f n) x) \<le> M\<close>
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
     \<Longrightarrow> \<exists> y. dist y x < r \<and> norm (h y) > r * (of_rat (Fract 2 3)) * onorm h\<close>
    for r and x and h::\<open>'a \<Rightarrow> 'b\<close>
  proof-
    assume \<open>bounded_linear h\<close>  \<open>r > 0\<close>
    hence \<open>onorm h \<le> (inverse r) * Sup ( (norm \<circ> h) ` (ball x r) )\<close>
      using sokal_banach_steinhaus[where r = r and f = h] 
      by auto
    hence \<open>onorm h \<le> (inverse r) * Sup ( (norm \<circ> h) ` (ball x r) )\<close>
      by simp      
    moreover assume \<open>0 < onorm h\<close>
    moreover have \<open>((of_rat (Fract 2 3)) * onorm h) < onorm h\<close>
    proof-
      have \<open>of_rat (Fract 2 3) < (1::real)\<close>
        by (simp add: Fract_less_one_iff)
      thus ?thesis
        using \<open>0 < onorm h\<close> by auto
    qed
    ultimately have \<open>(of_rat (Fract 2 3)) * onorm h < (inverse r) * Sup ( (norm \<circ> h) ` (ball x r) )\<close>
      by linarith
    hence  \<open>r * (of_rat (Fract 2 3)) * onorm h < r * (inverse r) * Sup ( (norm \<circ> h) ` (ball x r) )\<close>
      by (simp add: \<open>0 < r\<close>) 
    moreover have \<open>r * (inverse r) = 1\<close>
      using \<open>r > 0\<close> by auto
    ultimately have \<open>r * (of_rat (Fract 2 3)) * onorm h  < Sup ( (norm \<circ> h) ` (ball x r) )\<close>
      by auto
    moreover have \<open>(norm \<circ> h) ` (ball x r) \<noteq> {}\<close>
      using \<open>0 < r\<close> by auto      
    moreover have \<open>bdd_above ((norm \<circ> h) ` (ball x r))\<close>
    proof-
      have \<open>bounded (ball x r)\<close>
        by simp
      hence \<open>bounded (h ` (ball x r))\<close>
        by (simp add: \<open>bounded_linear h\<close> bounded_linear_image)
      hence \<open>\<exists> M. \<forall> \<xi> \<in> (h ` (ball x r)). norm \<xi> \<le> M\<close>
        using bounded_iff by blast
      then obtain M where \<open>\<And> \<xi>.  \<xi> \<in> (h ` (ball x r)) \<Longrightarrow> norm \<xi> \<le> M\<close>
        by blast
      hence \<open>\<And> \<sigma>. \<sigma> \<in> (ball x r) \<Longrightarrow> norm (h \<sigma>) \<le> M\<close>
        by simp
      hence \<open>bdd_above ((norm \<circ> h) ` (ball x r))\<close>
        by (metis (full_types) \<open>bounded (h ` ball x r)\<close> bdd_above_norm image_comp)        
      thus ?thesis
        by auto        
    qed
    ultimately have \<open>\<exists> t \<in> (norm \<circ> h) ` (ball x r). r * (of_rat (Fract 2 3)) * onorm h < t\<close>
      by (meson less_cSupD)
    hence \<open>\<exists> s \<in> ball x r. r * (of_rat (Fract 2 3)) * onorm h < (norm \<circ> h) s\<close>
      by auto
    hence \<open>\<exists> s \<in> ball x r. r * (of_rat (Fract 2 3)) * onorm h < norm (h s)\<close>
      by simp
    hence \<open>\<exists> y. dist y x < r \<and> r * (of_rat (Fract 2 3)) * onorm h < norm (h y)\<close>
      unfolding ball_def by (simp add: dist_commute) 
    hence \<open>\<exists> y. dist y x < r \<and> r * (of_rat (Fract 2 3)) * onorm h < norm (h y)\<close>
      by simp      
    thus ?thesis by auto
  qed
  hence \<open>\<exists> y. dist y x < (of_rat (Fract 1 3))^n \<and> 
        norm ((g n) y) > (of_rat (Fract 2 3)) * (of_rat (Fract 1 3))^n * onorm (g n)\<close>
    for n and x
  proof-
    have \<open>(of_rat (Fract 1 3))^n > (0::real)\<close>
      by (simp add: zero_less_Fract_iff)      
    moreover have \<open>\<And> n. onorm (g n) > 0\<close>
      using  \<open>\<forall> n. onorm (g n) > (4::real)^n\<close>
      by (smt zero_less_power)                             
    ultimately show ?thesis using  \<open>\<And> n. bounded_linear (g n)\<close>
      by (metis \<open>0 < real_of_rat (Fract 1 3) ^ n\<close> \<open>\<And>n. 0 < onorm (g n)\<close> \<open>\<And>n. bounded_linear (g n)\<close> \<open>\<And>x r h. \<lbrakk>bounded_linear h; 0 < onorm h; 0 < r\<rbrakk> \<Longrightarrow> \<exists>y. dist y x < r \<and> r * real_of_rat (Fract 2 3) * onorm h < norm (h y)\<close> linordered_field_class.sign_simps(5))          
  qed
  hence \<open>\<forall> n. \<forall> x. \<exists> y. dist y x < (of_rat (Fract 1 3))^n \<and> norm ((g n) y) > (of_rat (Fract 2 3)) * (of_rat (Fract 1 3))^n * onorm (g n)\<close>
    by blast
  hence \<open>\<exists> \<Phi>. \<forall> n. \<forall> x. dist (\<Phi> n x) x < (of_rat (Fract 1 3))^n \<and> norm ((g n) (\<Phi> n x)) > (of_rat (Fract 2 3)) * (of_rat (Fract 1 3))^n * onorm (g n)\<close>
    by metis
  then obtain \<Phi>
    where \<open>\<forall> n. \<forall> x. dist (\<Phi> n x) x <
       (of_rat (Fract 1 3))^n \<and> norm ((g n) (\<Phi> n x)) > (of_rat (Fract 2 3)) * (of_rat (Fract 1 3))^n * onorm (g n)\<close>
    by blast
  define \<phi>::\<open>nat \<Rightarrow> 'a\<close> where \<open>\<phi> n = rec_nat 0 \<Phi> n\<close>
    for n
  have \<open>\<phi> 0 = 0\<close>
    using \<phi>_def by simp
  have \<open>\<phi> (Suc n) = \<Phi> n (\<phi> n)\<close>
    for n
    using \<phi>_def by simp
  from \<open>\<forall> n. \<forall> x. dist (\<Phi> n x) x <
       (of_rat (Fract 1 3))^n \<and> norm ((g n) (\<Phi> n x)) > (of_rat (Fract 2 3)) * (of_rat (Fract 1 3))^n * onorm (g n)\<close>
  have  \<open>dist (\<phi> (Suc n))  (\<phi> n) < (of_rat (Fract 1 3))^n\<close>
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
      using convergent_series_Cauchy  \<open>\<And> n. dist (\<phi> (Suc n))  (\<phi> n) < (of_rat (Fract 1 3))^n\<close>
      sorry
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
          from \<open>\<And> n. dist (\<phi> (Suc n))  (\<phi> n) < (of_rat (Fract 1 3))^n\<close>
          have \<open>norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t)) < (of_rat (Fract 1 3))^(Suc t)\<close>
            for t
            using dist_norm
            by metis 
          hence \<open>(sum (\<lambda> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) {n..n+p}) 
              \<le> (sum (\<lambda> t. (1/3::real)^(Suc t) ) {n..n+p})\<close> 
            for p::nat
          proof(induction p)
            case 0
            have \<open>norm (\<phi> (Suc (Suc n)) - \<phi> (Suc n)) < (of_rat (Fract 1 3))^(Suc n)\<close>
              using \<open>\<And> t. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t)) < (of_rat (Fract 1 3))^(Suc t)\<close>
              by blast
            hence \<open>(\<Sum>t = n..n. norm (\<phi> (Suc (Suc t)) - \<phi> (Suc t))) \<le> (\<Sum>t = n..n. (of_rat (Fract 1 3)) ^ Suc t)\<close>
              by simp
            thus ?case 
              sorry        
          next
            case (Suc p)
            thus ?case
              (*
              by (smt add_Suc_right le_add1 sum.nat_ivl_Suc')
*) sorry
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
         (of_rat (Fract 1 3))^n \<and> norm ((g n) (\<Phi> n x)) > (of_rat (Fract 2 3)) * (of_rat (Fract 1 3))^n * onorm (g n)\<close>
        have \<open>norm ((g n) (\<Phi> n x)) > (of_rat (Fract 2 3)) * (of_rat (Fract 1 3))^n * onorm (g n)\<close>
          for x     
          by auto          
        hence \<open>norm ((g n) (\<Phi> n (\<phi> n))) > (of_rat (Fract 2 3)) * (of_rat (Fract 1 3))^n * onorm (g n)\<close>
          by blast
        thus ?thesis using \<open>\<And>n. \<phi> (Suc n) = \<Phi> n (\<phi> n)\<close>
          by (metis (mono_tags, hide_lams) divide_rat mult_numeral_1 mult_numeral_1_right numeral_One of_rat_divide of_rat_numeral_eq rat_number_expand(3))
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

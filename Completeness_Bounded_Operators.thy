(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Completeness of the metric space of (real) bounded operators.

*)

theory Completeness_Bounded_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL-Analysis.Infinite_Set_Sum"
    Operator_Norm_Plus
    Convergence_Operators
begin

lemma uniform_strong_onorm:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close> and l::\<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>\<forall>n. bounded_linear (f n)\<close> and \<open>bounded_linear l\<close>
    and \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
  shows \<open>f \<midarrow>onorm\<rightarrow> l\<close> 
proof-
  have \<open>(\<lambda>n. onorm (\<lambda>x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
  proof-
    have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N.  onorm (\<lambda>x. f n x - l x) \<le> e\<close>
      for e
    proof-
      assume \<open>e > 0\<close>
      hence \<open>\<exists> N. \<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
        using \<open>f \<midarrow>ustrong\<rightarrow> l\<close> unfolding ustrong_convergence_def
        by blast
      then obtain N where \<open>\<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
        by blast
      have \<open>bounded_linear g \<Longrightarrow> \<exists> x. norm x = 1 \<and> onorm g \<le> norm (g x) + inverse (real (Suc m))\<close>
        for x::'a and g::\<open>'a \<Rightarrow> 'b\<close> and m :: nat
      proof-
        assume \<open>bounded_linear g\<close>
        hence \<open>onorm g = Sup {norm (g x) | x. norm x = 1}\<close>
          using onorm_sphere by blast
        have \<open>\<exists> t \<in> {norm (g x) | x. norm x = 1}. onorm g \<le>  t + inverse (real (Suc m))\<close>
        proof-
          have \<open>ereal (inverse (real (Suc m))) > 0\<close>
            by simp
          moreover have \<open>\<bar>Sup {ereal (norm (g x)) | x. norm x = 1}\<bar> \<noteq> \<infinity>\<close>
          proof-
            have \<open>\<exists> M::real. \<forall> x. norm x = 1 \<longrightarrow>  (norm (g x))  \<le> M\<close>
              by (metis \<open>bounded_linear g\<close>  bounded_linear.bounded)
            then obtain M::real where \<open>\<forall> x. norm x = 1 \<longrightarrow>  (norm (g x))  \<le> M\<close>
              by blast
            hence \<open>\<forall> x. norm x = 1 \<longrightarrow> ereal (norm (g x)) \<le> M\<close>
              by simp
            hence \<open>t \<in> {ereal (norm (g x)) | x. norm x = 1} \<Longrightarrow> t \<le> M\<close>
              for t
              by blast
            hence \<open>Sup {ereal (norm (g x)) | x. norm x = 1} \<le> M\<close>
              using Sup_least by blast
            moreover have \<open>Sup { ereal (norm (g x))  | x. norm x = 1} \<ge> 0\<close>
            proof-
              have \<open>t \<in> { ereal (norm (g x))  | x. norm x = 1} \<Longrightarrow> t \<ge> 0\<close>
                for t
                by auto                
              moreover have \<open>{ ereal (norm (g x))  | x. norm x = 1} \<noteq> {}\<close>
              proof-
                have \<open>\<exists> x::'a.  norm x = 1\<close>
                  using le_numeral_extra(1) vector_choose_size by blast
                thus ?thesis by blast
              qed
              ultimately show ?thesis
                by (meson less_eq_Sup) 
            qed
            ultimately have \<open>\<bar> Sup { ereal (norm (g x))  | x. norm x = 1} \<bar> \<le> M\<close>
              by simp
            thus ?thesis by auto
          qed
          moreover have \<open>{ereal(norm (g x)) | x. norm x = 1} \<noteq> {}\<close>
            by (metis Sup_empty bot.extremum_strict calculation(2) less_ereal.simps(1) lt_ex not_infty_ereal)
          ultimately have \<open>\<exists> t \<in> {ereal(norm (g x)) | x. norm x = 1}. Sup {ereal(norm (g x)) | x. norm x = 1}
               - ereal (inverse (real (Suc m))) < t\<close>
            by (rule Sup_ereal_close)
          hence \<open>\<exists> t \<in> {(norm (g x)) | x. norm x = 1}. Sup {ereal(norm (g x)) | x. norm x = 1}
               - (inverse (real (Suc m))) < t\<close>
            by auto
          then obtain t::real where \<open>t \<in> {(norm (g x)) | x. norm x = 1}\<close> 
            and \<open>Sup {ereal(norm (g x)) | x. norm x = 1}
               - (inverse (real (Suc m))) < t\<close>
            by blast
          have \<open>onorm g = Sup {ereal(norm (g x)) | x. norm x = 1}\<close>
            using \<open>onorm g = Sup {norm (g x) | x. norm x = 1}\<close>
            by simp
          also have \<open>...
                < t + (inverse (real (Suc m)))\<close>
            apply auto
            using \<open>Sup {ereal(norm (g x)) | x. norm x = 1}
               - (inverse (real (Suc m))) < t\<close>
          proof auto
            assume \<open>Sup {ereal (norm (g x)) |x. norm x = 1} - ereal (inverse (1 + real m))
                  < ereal t\<close>
            moreover have \<open>\<bar> ereal (inverse (1 + real m)) \<bar> \<noteq> \<infinity>\<close>
              by auto
            ultimately have \<open>Sup {ereal (norm (g x)) |x. norm x = 1}
                  < ereal t + ereal (inverse (1 + real m))\<close>
              using ereal_minus_less by simp               
            hence \<open>Sup {ereal (norm (g x)) |x. norm x = 1}
                  < t + (inverse (1 + real m))\<close>
              by simp
            moreover have \<open>Sup {ereal (norm (g x)) |x. norm x = 1} = 
                    Sup {(norm (g x)) |x. norm x = 1}\<close>
            proof-
              have \<open>{ereal (norm (g x)) |x. norm x = 1} = 
                    {(norm (g x)) |x. norm x = 1}\<close>
                by simp
              hence \<open>y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<in> {(norm (g x)) |x. norm x = 1}\<close>
                for y
                by simp
              moreover have \<open>{ (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (metis \<open>t \<in> {norm (g x) |x. norm x = 1}\<close> empty_iff)                
              moreover have \<open>bdd_above { (norm (g x)) |x. norm x = 1}\<close>
                by (metis (mono_tags, lifting)  \<open>bounded_linear g\<close> norm_set_bdd_above_eq1) 
              ultimately have \<open>y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {(norm (g x)) |x. norm x = 1}\<close>
                for y
                by (smt cSup_upper ereal_less_eq(3) mem_Collect_eq)
              from \<open>{ereal (norm (g x)) |x. norm x = 1} = 
                    {(norm (g x)) |x. norm x = 1}\<close>
              have \<open>y \<in> {(norm (g x)) |x. norm x = 1} \<Longrightarrow>
                   y \<in> {ereal (norm (g x)) |x. norm x = 1}\<close>
                for y
                by simp
              moreover have \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (metis \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>)                
              moreover have \<open>bdd_above {ereal (norm (g x)) |x. norm x = 1}\<close>
                by (metis (no_types, lifting) bdd_above_top) 
              ultimately have \<open>y \<in> {(norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                for y
                by (simp add: Sup_upper)
              from  \<open>\<And> y. y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {(norm (g x)) |x. norm x = 1}\<close>
              have \<open>Sup {ereal (norm (g x)) |x. norm x = 1} \<le>  Sup {(norm (g x)) |x. norm x = 1}\<close>
                using \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (meson cSup_least)
              have \<open>(Sup { (norm (g x)) |x. norm x = 1}) \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close> 
              proof-
                define X::\<open>ereal set\<close> where \<open>X = {norm (g x) |x. norm x = 1}\<close>
                define z::ereal where \<open>z = Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                have \<open>X \<noteq> {}\<close>
                  unfolding X_def
                  using \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close> by blast 
                moreover have \<open>\<And>x. x \<in> X \<Longrightarrow> x \<le> z\<close>
                  unfolding X_def z_def
                  by (simp add: Sup_upper)
                ultimately have \<open>Sup X \<le> z\<close>
                  by (rule cSup_least)
                hence \<open>Sup X \<le>  Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  unfolding z_def 
                  by auto
                hence \<open>real_of_ereal (Sup {norm (g x) |x. norm x = 1}) \<le>  Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  unfolding X_def 
                  by auto
                thus ?thesis
                  by (smt \<open>\<And>y. y \<in> {norm (g x) |x. norm x = 1} \<Longrightarrow> ereal y \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close> \<open>\<bar>Sup {ereal (norm (g x)) |x. norm x = 1}\<bar> \<noteq> \<infinity>\<close> \<open>{norm (g x) |x. norm x = 1} \<noteq> {}\<close> cSup_least ereal_le_real_iff) 
              qed
              show ?thesis 
                using \<open>(Sup {(norm (g x)) |x. norm x = 1}) \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  \<open>Sup {ereal (norm (g x)) |x. norm x = 1} \<le>  Sup {(norm (g x)) |x. norm x = 1}\<close>
                by auto
            qed
            ultimately show \<open>Sup {norm (g x) |x. norm x = 1} < t + inverse (1 + real m)\<close>
              by simp
          qed
          finally have \<open>(onorm g) < t + (inverse (real (Suc m)))\<close>
            by blast
          thus ?thesis
            using \<open>t \<in> {norm (g x) |x. norm x = 1}\<close> by auto             
        qed
        thus ?thesis by auto
      qed
      hence \<open>\<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
        for n and m::nat
        using \<open>\<forall>n. bounded_linear (f n)\<close>
        by (simp add: assms(2) bounded_linear_sub)
      hence \<open>n \<ge> N \<Longrightarrow>  onorm (\<lambda> x. f n x - l x) \<le> e\<close>
        for n
      proof-
        assume \<open>n \<ge> N\<close>
        hence  \<open>\<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          using \<open>\<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          by blast
        have  \<open>\<forall> m. \<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
          using \<open>\<And> m. \<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
          by blast
        hence  \<open>\<exists> x. \<forall> m. norm (x m) = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m))\<close>
          using choice by simp  
        then obtain x where \<open>norm (x m) = 1\<close> 
          and \<open>onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m))\<close>
        for m::nat
          by blast          
        have \<open>\<forall> m. onorm (\<lambda> x. f n x - l x) < e + inverse (real (Suc m))\<close>
          using \<open>\<And> m. norm (x m) = 1\<close>  \<open>\<And> m. onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m)) \<close>
            \<open>\<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          by smt
        have \<open>onorm (\<lambda> x. f n x - l x) \<le> e\<close>
        proof(rule classical)
          assume \<open>\<not>(onorm (\<lambda> x. f n x - l x) \<le> e)\<close>
          hence \<open>e < onorm (\<lambda> x. f n x - l x)\<close>
            by simp
          hence \<open>0 < onorm (\<lambda> x. f n x - l x) - e\<close>
            by simp
          hence \<open>\<exists> n0. inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close>
            by (rule Archimedean_Field.reals_Archimedean)
          then obtain n0 where \<open>inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close>
            by blast
          have \<open>\<forall> m. onorm (\<lambda> x. f n x - l x) - e < inverse (real (Suc m))\<close>
            by (smt \<open>\<forall>m. onorm (\<lambda>x. f n x - l x) < e + inverse (real (Suc m))\<close>)
          hence \<open>\<forall> m. inverse (real (Suc n0)) < inverse (real (Suc m))\<close>
            using  \<open>inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close> by smt
          hence \<open>inverse (real (Suc n0)) < inverse (real (Suc n0))\<close>
            by blast
          thus ?thesis by blast
        qed
        thus ?thesis by blast 
      qed
      thus ?thesis by blast
    qed
    hence \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N. norm ( onorm (\<lambda>x. f n x - l x) ) \<le> e\<close>
      for e
    proof-
      assume \<open>e > 0\<close>
      hence \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        using  \<open>\<And> e. e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N.  onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        by blast
      then obtain N where \<open>\<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        by blast
      have  \<open>\<forall> n \<ge> N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close>
      proof-
        have \<open>n \<ge> N \<Longrightarrow> norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close>
          for n
        proof-
          assume \<open>n \<ge> N\<close>
          hence \<open>onorm (\<lambda>x. f n x - l x) \<le> e\<close>
            using \<open>\<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close> by blast
          moreover have \<open>onorm (\<lambda>x. f n x - l x) \<ge> 0\<close>
            by (simp add: assms(1) assms(2) bounded_linear_sub onorm_pos_le)            
          ultimately show ?thesis by simp
        qed
        thus ?thesis by blast
      qed
      thus ?thesis by blast 
    qed
    have \<open>0 < e \<Longrightarrow>
      \<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) < e\<close>
      for e::real
    proof-
      assume \<open>0 < e\<close>
      hence \<open>e/2 < e\<close>
        by simp
      have \<open>0 < e/2\<close>
        using \<open>0 < e\<close> by simp
      hence \<open>\<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e/2\<close>
        using \<open>\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close> by blast
      thus ?thesis using \<open>e/2 < e\<close> by fastforce
    qed
    thus ?thesis by (simp add: LIMSEQ_I) 
  qed
  thus ?thesis unfolding onorm_convergence_def by blast
qed



lemma PREuCauchy_ustrong:
  fixes f :: \<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>uCauchy f\<close>
  shows \<open>\<exists> l::'a\<Rightarrow>'b. f \<midarrow>ustrong\<rightarrow> l\<close>
proof-
  have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
    using \<open>uCauchy f\<close> unfolding uCauchy_def by blast
  hence \<open>norm x = 1 \<Longrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (f m x - f n x) < e)\<close>
    for x
    by blast
  hence \<open>norm x = 1 \<Longrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m x) (f n x) < e)\<close>
    for x
    by (simp add: dist_norm)    
  hence \<open>norm x = 1 \<Longrightarrow> Cauchy (\<lambda> n. f n x)\<close>
    for x
    using Cauchy_def by blast
  hence \<open>norm x = 1 \<Longrightarrow> convergent (\<lambda> n. f n x)\<close>
    for x
    by (simp add: Cauchy_convergent_iff)
  hence \<open>norm x = 1 \<Longrightarrow> \<exists> l. (\<lambda> n. f n x) \<longlonglongrightarrow> l\<close>
    for x
    by (simp add: convergentD)
  hence \<open>\<forall> x. \<exists> l. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l\<close>
    by blast
  hence \<open>\<exists> l. \<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
    by metis
  then obtain l where \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close> by blast
  have \<open>e > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<forall>x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
    for e::real
  proof-
    assume \<open>e > 0\<close>
    hence \<open>e/2 > 0\<close>
      by simp
    hence \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. dist (f n x) (l x) < e/2)\<close>
      using  \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
      by (meson LIMSEQ_iff_nz)

    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x)  (f n x) < e/2\<close>
      using  \<open>e/2 > 0\<close> \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
      by (metis dist_norm)
    then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (f n x) < e/2\<close>
      by blast
    have \<open>m \<ge> M \<Longrightarrow> \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (l x) < e\<close>
      for m
    proof-
      assume \<open>m \<ge> M\<close>
      have \<open>norm x = 1 \<Longrightarrow> dist (f m x) (l x) < e\<close>
        for x
      proof-
        assume \<open>norm x = 1\<close>
        have \<open>dist (f m x) (l x) \<le> dist (f m x) (f n x) + dist (l x) (f n x)\<close>
          for n
          by (simp add: dist_triangle2)
        moreover have \<open>n \<ge> M \<Longrightarrow> dist (f m x) (f n x) < e/2\<close>
          for n
          using \<open>M \<le> m\<close> \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (f n x) < e / 2\<close> \<open>norm x = 1\<close> by blast
        moreover have \<open>\<exists> N. \<forall> n \<ge> N. dist (l x) (f n x) < e/2\<close>
        proof-
          have \<open>\<exists> N. \<forall> n \<ge> N. dist (f n x) (l x) < e/2\<close>
            using \<open>e/2 > 0\<close> \<open>\<forall>x. norm x = 1 \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. dist (f n x) (l x) < e / 2)\<close> \<open>norm x = 1\<close> by auto 
          thus ?thesis
            by (simp add: dist_commute) 
        qed
        ultimately show ?thesis
          by (meson dist_triangle_half_l le_add1 le_add2) 
      qed
      thus ?thesis by blast
    qed
    thus ?thesis
      by (metis dist_norm) 
  qed
  thus ?thesis unfolding ustrong_convergence_def by blast
qed


lemma uCauchy_ustrong:
  fixes f :: \<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::banach)\<close>
  assumes  \<open>uCauchy f\<close> and \<open>\<And> n. bounded_linear (f n)\<close>
  shows \<open>\<exists> l::'a\<Rightarrow>'b. bounded_linear l \<and> f \<midarrow>ustrong\<rightarrow> l\<close>
proof-
  have \<open>\<exists> s::'a\<Rightarrow>'b. f \<midarrow>ustrong\<rightarrow> s\<close>
    by (simp add: PREuCauchy_ustrong assms(1))
  then obtain s where \<open>f \<midarrow>ustrong\<rightarrow> s\<close> by blast
  define l::\<open>'a \<Rightarrow> 'b\<close> where \<open>l x = (norm x) *\<^sub>R s ((inverse (norm x)) *\<^sub>R x)\<close>
    for x::'a
  have \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
    using l_def \<open>f \<midarrow>ustrong\<rightarrow> s\<close> 
    unfolding l_def
    unfolding ustrong_convergence_def
    by simp
  moreover have \<open>bounded_linear l\<close>
  proof-
    have \<open>(\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
      for x
    proof(cases \<open> x = 0\<close>)
      case True
      have \<open>(\<lambda> n. f n x) \<longlonglongrightarrow> 0\<close>
      proof-
        have \<open>f n x = (0::'b)\<close>
          for n
          using \<open>\<And> n. bounded_linear (f n)\<close>
          by (simp add: True linear_simps(3))
        moreover  have \<open>(\<lambda> n. (0::'b)) \<longlonglongrightarrow> 0\<close>
          by simp            
        ultimately show ?thesis by simp
      qed
      moreover have \<open>l x = 0\<close>
      proof-
        have \<open>norm x = 0\<close>
          using \<open>x = 0\<close> by simp
        thus ?thesis using l_def by simp
      qed
      ultimately show ?thesis by simp 
    next
      case False
      hence  \<open>norm x \<noteq> 0\<close> by simp
      thus ?thesis
      proof-
        have  \<open>(\<lambda> n. f n (x  /\<^sub>R norm x)) \<longlonglongrightarrow> s (x /\<^sub>R norm x)\<close>
        proof-
          have \<open>norm (x  /\<^sub>R norm x) = 1\<close>
            by (simp add: False)
          have \<open> \<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x. norm x = 1 \<longrightarrow> norm (f n x - s x) < e\<close>
            using \<open>f \<midarrow>ustrong\<rightarrow> s\<close>
            unfolding ustrong_convergence_def by blast
          hence \<open> \<forall>e>0. \<exists>N. \<forall>n\<ge>N. norm (f n (x  /\<^sub>R norm x) - s (x  /\<^sub>R norm x)) < e\<close>
            using  \<open>norm (x  /\<^sub>R norm x) = 1\<close> by fastforce
          thus ?thesis
            by (simp add: LIMSEQ_iff) 
        qed
        hence  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow>  (norm x) *\<^sub>R  s (x /\<^sub>R norm x)\<close>
          using bounded_linear.tendsto bounded_linear_scaleR_right by blast
        hence  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
          using l_def
          by simp
        have  \<open>(\<lambda> n.  f n x) \<longlonglongrightarrow> l x\<close>
        proof-
          have \<open>(norm x) *\<^sub>R f n (x /\<^sub>R norm x) = f n x\<close>
            for n
            using \<open>norm x \<noteq> 0\<close> \<open>\<And> n. bounded_linear (f n)\<close>
            unfolding bounded_linear_def linear_def
            by (simp add: assms(2) linear_simps(5)) 
          thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close> by simp
        qed
        thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
          by auto
      qed
    qed
    have \<open>linear l\<close>
    proof
      show "l (b1 + b2) = l b1 + l b2"
        for b1 :: 'a
          and b2 :: 'a
      proof-
        have \<open>(\<lambda> n. f n (b1 + b2)) \<longlonglongrightarrow> l (b1 + b2)\<close>
          using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
          by blast
        moreover have \<open>(\<lambda> n. f n (b1 + b2)) \<longlonglongrightarrow> l b1 + l b2\<close>
        proof-
          have \<open>(\<lambda> n. f n b1) \<longlonglongrightarrow> l b1\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          moreover have \<open>(\<lambda> n. f n b2) \<longlonglongrightarrow> l b2\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          ultimately have \<open>(\<lambda> n. f n b1 + f n b2) \<longlonglongrightarrow> l b1 + l b2\<close>
            by (simp add: tendsto_add) 
          moreover have \<open>(\<lambda> n. f n (b1 + b2)) = (\<lambda> n. f n b1 + f n b2)\<close>
          proof-
            have \<open>f n (b1 + b2) = f n b1 + f n b2\<close>
              for n
              using \<open>\<And> n. bounded_linear (f n)\<close>
              unfolding bounded_linear_def
              by (simp add: linear_add)
            thus ?thesis by blast
          qed
          ultimately show ?thesis by simp 
        qed
        ultimately show ?thesis
          using LIMSEQ_unique by blast            
      qed
      show "l (r *\<^sub>R b) = r *\<^sub>R l b"
        for r :: real
          and b :: 'a
      proof-
        have \<open>(\<lambda> n. f n (r *\<^sub>R b)) \<longlonglongrightarrow> l (r *\<^sub>R b)\<close>
          using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
          by blast
        moreover have \<open>(\<lambda> n. f n (r *\<^sub>R b)) \<longlonglongrightarrow>  r *\<^sub>R (l b)\<close>
        proof-
          have \<open>(\<lambda> n. f n b) \<longlonglongrightarrow> l b\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          hence \<open>(\<lambda> n. r *\<^sub>R (f n b)) \<longlonglongrightarrow> r *\<^sub>R (l b)\<close>
            using bounded_linear.tendsto bounded_linear_scaleR_right by blast
          moreover have \<open>(\<lambda> n. (f n (r *\<^sub>R b))) = (\<lambda> n. r *\<^sub>R (f n b))\<close>
          proof-
            have \<open>f n (r *\<^sub>R b) = r *\<^sub>R (f n b)\<close>
              for n
              using \<open>\<And> n. bounded_linear (f n)\<close>
              unfolding bounded_linear_def
              by (simp add: linear_scale)
            thus ?thesis by blast
          qed
          ultimately show ?thesis by simp 
        qed
        ultimately show ?thesis
          using LIMSEQ_unique by blast            
      qed
    qed
    moreover have \<open>bounded_linear_axioms l\<close>
    proof-
      have \<open>\<exists>K. \<forall>x. norm (l x) \<le> norm x * K\<close>
      proof(rule classical)
        assume \<open>\<not> (\<exists>K. \<forall>x. norm (l x) \<le> norm x * K)\<close>
        hence \<open>\<forall> K. \<exists> x. norm (l x) > norm x * K\<close>
          by smt
        hence \<open>\<forall> K. \<exists> x \<noteq> 0. norm (l x) > norm x * K\<close>
          using calculation linear_0 by force
        have \<open>\<forall> K. \<exists> x. norm x = 1 \<and> K < norm (l x)\<close>
        proof-
          have \<open>\<exists> x. norm x = 1 \<and> K < norm (l x)\<close>
            for K
          proof-
            have \<open>\<exists> x \<noteq> 0. norm (l x) > norm x * K\<close>
              using  \<open>\<forall> K. \<exists> x \<noteq> 0. norm (l x) > norm x * K\<close> by blast
            then obtain x where \<open>x \<noteq> 0\<close> and \<open>norm (l x) > norm x * K\<close>
              by blast
            have \<open>norm x > 0\<close> using \<open>x \<noteq> 0\<close> by simp
            hence  \<open>inverse (norm x) * norm (l x) > inverse (norm x) * (norm x) * K\<close>
              using  \<open>norm (l x) > norm x * K\<close>
              by (smt linordered_field_class.sign_simps(23) mult_left_le_imp_le positive_imp_inverse_positive) 
            moreover have \<open>(inverse (norm x)) * (norm x) = 1\<close>
              using \<open>norm x > 0\<close> by simp
            ultimately have \<open>(inverse (norm x)) * norm (l x) >  K\<close>
              by simp
            moreover have \<open>(inverse (norm x)) * norm (l x) = norm ((inverse (norm x)) *\<^sub>R (l x))\<close>
            proof-
              have \<open>(inverse (norm x)) > 0\<close>
                using \<open>norm x > 0\<close> 
                by simp
              thus ?thesis using norm_scaleR
                by simp 
            qed
            hence \<open> norm ((inverse (norm x)) *\<^sub>R (l x)) >  K\<close>
              using calculation by linarith
            hence \<open> norm (l ((inverse (norm x)) *\<^sub>R  x)) >  K\<close>
            proof-
              have \<open>(inverse (norm x)) *\<^sub>R (l x) = l ((inverse (norm x)) *\<^sub>R  x)\<close>
                by (simp add: \<open>linear l\<close> linear_scale)
              thus ?thesis
                using \<open>K < norm (l x /\<^sub>R norm x)\<close> by simp                 
            qed
            have \<open>norm ( (inverse (norm x)) *\<^sub>R  x ) = 1\<close>
              using \<open>norm x > 0\<close> by simp
            show ?thesis
              using \<open>K < norm (l (x /\<^sub>R norm x))\<close> \<open>norm (x /\<^sub>R norm x) = 1\<close> by blast 
          qed
          thus ?thesis by blast
        qed
        have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < e\<close>
          using \<open>uCauchy f\<close>
          unfolding uCauchy_def
          by blast
        hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < 1\<close>
          by auto
        then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < 1\<close>
          by blast
        hence \<open>\<forall>m\<ge>M. \<forall>x. 
            norm x = 1 \<longrightarrow> norm (f m x - f M x) < 1\<close>
          by blast
        have \<open>norm (f m x) \<le> norm (f M x) + norm (f m x - f M x)\<close>
          for m and x
          by (simp add: norm_triangle_sub) 
        hence \<open>norm (f m x) \<le> onorm (f M) * norm x + norm (f m x - f M x)\<close>
          for m and x
          using onorm
          by (smt assms(2)) 
        hence \<open>norm x = 1 \<Longrightarrow> norm (f m x) \<le> onorm (f M) + norm (f m x - f M x)\<close>
          for m and x
          by (metis mult_cancel_left2)
        hence \<open>m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm (f m x) < onorm (f M) + 1\<close>
          for m and x
          using  \<open>\<forall>m\<ge>M. \<forall>x. 
            norm x = 1 \<longrightarrow> norm (f m x - f M x) < 1\<close> 
          by smt
        have \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. f m x) \<longlonglongrightarrow> l x\<close>
          for x
          by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> l x\<close>)
        hence \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
          for x
          by (simp add: tendsto_norm)
        hence \<open>norm x = 1 \<Longrightarrow> norm (l x) \<le> onorm (f M) + 1\<close>
          for x
        proof-
          assume \<open>norm x = 1\<close>
          hence \<open>(\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
            using  \<open>\<And> x. norm x = 1 \<Longrightarrow> (\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
            by blast
          moreover have \<open>\<forall>  m \<ge> M. norm (f m x) \<le> onorm (f M) + 1\<close>
            using  \<open>\<And> m. \<And> x.  m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm (f m x) < onorm (f M) + 1\<close>
              \<open>norm x = 1\<close> by smt
          ultimately show ?thesis 
            by (rule Topological_Spaces.Lim_bounded)
        qed
        moreover have  \<open>\<exists> x. norm x = 1 \<and> onorm (f M) + 1 < norm (l x)\<close>
          by (simp add: \<open>\<forall>K. \<exists>x. norm x = 1 \<and> K < norm (l x)\<close>)
        ultimately show ?thesis
          by fastforce 
      qed
      thus ?thesis unfolding bounded_linear_axioms_def by blast
    qed
    ultimately show ?thesis unfolding bounded_linear_def by blast
  qed
  ultimately show ?thesis by blast
qed

theorem completeness_real_bounded:
  fixes f :: \<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>\<forall>n. bounded_linear (f n)\<close>
    and \<open>oCauchy f\<close>
  shows \<open>\<exists> l. bounded_linear l \<and> f \<midarrow>onorm\<rightarrow> l\<close>
proof-
  from \<open>oCauchy f\<close>
  have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
    unfolding oCauchy_def by blast
  have \<open>uCauchy f\<close>
  proof-
    have  \<open>e > 0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
      for e::real
    proof-
      assume \<open>e > 0\<close>
      hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
        using \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
        by blast
      then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
        by blast
      have \<open>m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
        for m n::nat
      proof-
        assume \<open>m \<ge> M\<close>
        moreover assume \<open>n \<ge> M\<close>
        ultimately have \<open>onorm (\<lambda>x. f m x - f n x) < e\<close>
          by (simp add: \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>)
        moreover have \<open>norm x = 1 \<Longrightarrow>  norm (f m x - f n x) \<le> onorm (\<lambda>x. f m x - f n x)\<close>
          for x
        proof-
          assume \<open>norm x = 1\<close>
          moreover have \<open>norm (f m x - f n x) \<le> onorm (\<lambda>x. f m x - f n x) * norm x\<close>
            using assms(1) bounded_linear_sub onorm by blast          
          ultimately show ?thesis by simp
        qed
        ultimately show ?thesis by smt
      qed
      thus ?thesis by blast
    qed
    thus ?thesis
      by (simp add: uCauchy_def) 
  qed
  hence \<open>\<exists> l. bounded_linear l \<and> f \<midarrow>ustrong\<rightarrow> l\<close>
    using \<open>\<forall>n. bounded_linear (f n)\<close>
      uCauchy_ustrong
    by auto
  then obtain l where  \<open>bounded_linear l\<close> and \<open>f \<midarrow>ustrong\<rightarrow> l\<close> 
    by blast
  have \<open>(\<lambda>n. onorm (\<lambda>x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
    using  \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
      \<open>bounded_linear l\<close> assms(1) onorm_convergence_def uniform_strong_onorm by blast
  thus ?thesis
    unfolding onorm_convergence_def using \<open>bounded_linear l\<close> by blast
qed



end
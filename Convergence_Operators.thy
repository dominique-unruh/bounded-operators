(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Several definitions of convergence of families of operators.

*)

theory Convergence_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL.Real_Vector_Spaces"
    "HOL-Analysis.Operator_Norm"
    Operator_Norm_Plus
begin

section \<open>Pointwise convergence\<close>

definition strong_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>strong_convergence f l = ( \<forall> x. ( \<lambda> n. norm (f n x - l x) ) \<longlonglongrightarrow> 0 )\<close>

abbreviation strong_convergence_abbr:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  (\<open>((_)/ \<midarrow>strong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>strong\<rightarrow> l \<equiv> ( strong_convergence f l )\<close>

definition onorm_convergence::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>onorm_convergence f l = ( ( \<lambda> n. onorm (\<lambda> x. f n x - l x) ) \<longlonglongrightarrow> 0 )\<close>

section \<open>Convergence with respect to the operator norm\<close>

abbreviation onorm_convergence_abbr::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>  (\<open>((_)/ \<midarrow>onorm\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>onorm\<rightarrow> l \<equiv> ( onorm_convergence f l )\<close>

definition oCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>oCauchy f = ( \<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e )\<close>

section \<open>Uniform convergence on the unit sphere\<close>

definition ustrong_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close> where 
  \<open>ustrong_convergence f l = ( \<forall> e > 0. \<exists> N. \<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e )\<close>

abbreviation ustrong_convergence_abbr::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>  (\<open>((_)/ \<midarrow>ustrong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>ustrong\<rightarrow> l \<equiv> ( ustrong_convergence f l )\<close>

definition uCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>uCauchy f = ( \<forall> e > 0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e )\<close>

section \<open>Relationships among the different kind of convergence\<close>

lemma ustrong_onorm:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close>
    and l::\<open>'a \<Rightarrow> 'b\<close>
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
          also have \<open>... < t + (inverse (real (Suc m)))\<close>
            apply auto
            using \<open>Sup {ereal(norm (g x)) | x. norm x = 1} - (inverse (real (Suc m))) < t\<close>
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


lemma oCauchy_uCauchy:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close>
  assumes \<open>\<forall>n. bounded_linear (f n)\<close>
    and \<open>oCauchy f\<close>
  shows \<open>uCauchy f\<close>
proof-
  have  \<open>e > 0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
    for e::real
  proof-
    assume \<open>e > 0\<close>
    moreover have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
      using \<open>oCauchy f\<close> unfolding oCauchy_def by blast
    ultimately have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
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


end
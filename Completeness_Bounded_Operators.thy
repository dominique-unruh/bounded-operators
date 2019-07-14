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
    Convergence_Operators
begin
                  

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
      \<open>bounded_linear l\<close> assms(1) onorm_convergence_def ustrong_onorm by blast
  thus ?thesis
    unfolding onorm_convergence_def using \<open>bounded_linear l\<close> by blast
qed



end
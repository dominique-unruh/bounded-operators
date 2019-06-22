(*  Title:      bounded-Operators/Operator_Norm_Plus.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

This is a complement to the file HOL/Analysis/Operator_Norm.thy (Amine Chaieb, Brian Huffman).

References:             

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}

*)

theory Operator_Norm_Plus
  imports Complex_L2
    "HOL-Analysis.Operator_Norm"
    "HOL-Library.Adhoc_Overloading"
    "HOL-Analysis.Abstract_Topology" 
    Extended_Sorry
begin
  (*
definition operator_norm::\<open>('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> real\<close> where
  \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})= \<close>
*)

lemma bounded_clinear_refined: \<open>bounded_clinear T \<Longrightarrow> \<exists> K\<ge>0. (\<forall>x. norm (T x) \<le> norm x * K)\<close>
  by (metis (mono_tags, hide_lams) bounded_clinear.bounded eq_iff mult_zero_left norm_ge_zero order.trans zero_le_mult_iff)


(* TODO: exists? *)
lemma operator_norm_non_neg:
  \<open>bounded_clinear f \<Longrightarrow>  (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f \<ge> 0\<close>
proof-
  assume \<open>bounded_clinear f\<close>
    (*  have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f = Inf { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by (simp add: operator_norm_def) *)
  moreover have \<open>{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} \<noteq> {}\<close>
    using  \<open>bounded_clinear f\<close> bounded_clinear_refined
    by auto
  moreover have \<open>bdd_below { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by auto  
  ultimately show ?thesis
    by (metis (no_types, lifting) cInf_greatest mem_Collect_eq) 
qed

(* TODO: exists? TODO: needed? *)
lemma operation_norm_closed:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close>
  shows \<open>closed { K | K::real. \<forall>x. norm (f x) \<le> norm x * K}\<close>
proof-
  have \<open>\<forall> n. (k n) \<in> { K | K::real. \<forall>x. norm (f x) \<le> norm x * K}
    \<Longrightarrow> k \<longlonglongrightarrow> l 
    \<Longrightarrow> l \<in> { K | K::real. \<forall>x. norm (f x) \<le> norm x * K}\<close>
    for k and l
  proof-
    assume \<open>\<forall> n. (k n) \<in> { K | K::real. \<forall>x. norm (f x) \<le> norm x * K}\<close>
    hence \<open>\<forall> n. norm (f x) \<le> norm x * (k n)\<close>
      for x
      by blast
    assume \<open>k \<longlonglongrightarrow> l\<close>
    have \<open>norm (f x) \<le> norm x * l\<close>
      for x
    proof-
      have  \<open>\<forall> n. norm (f x) \<le> norm x * (k n)\<close>
        by (simp add: \<open>\<And>x. \<forall>n. norm (f x) \<le> norm x * k n\<close>)
      moreover have \<open>(\<lambda> n.  norm x * (k n) ) \<longlonglongrightarrow> norm x * l\<close>
        using  \<open>k \<longlonglongrightarrow> l\<close>
        by (simp add: tendsto_mult_left)
      ultimately show ?thesis
        using Topological_Spaces.Lim_bounded2
        by fastforce
    qed
    thus ?thesis
      by simp  
  qed
  thus ?thesis
    by (meson closed_sequential_limits) 
qed

lemma operation_norm_intro:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
    and x :: 'a
  assumes \<open>bounded_linear f\<close>
  shows \<open>norm (f x) \<le> norm x * ((\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f)\<close>
proof-
  have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f = Inf { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by simp
  moreover have \<open>closed { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
  proof-
    have \<open>closed { K | K::real. K \<ge> 0}\<close>
      by (metis atLeast_def closed_atLeast) 
    moreover have \<open>closed { K | K::real. (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
      using operation_norm_closed assms by auto 
    moreover have \<open>{ K | K::real. K \<ge> 0} \<inter> { K | K::real. (\<forall>x. norm (f x) \<le> norm x * K)}
          = { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
      by blast
    ultimately show ?thesis
      using closed_Int by fastforce  
  qed
  moreover have \<open>bdd_below { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by auto
  moreover have \<open>{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} \<noteq> {}\<close>
    using \<open>bounded_linear f\<close>  bounded_linear.nonneg_bounded by auto 
  ultimately show ?thesis
    by (metis (mono_tags, lifting) closed_contains_Inf mem_Collect_eq) 
qed

(* TODO: exists? *)
lemma operator_norm_zero:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close> and \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f = 0\<close>
  shows \<open>f = (\<lambda>_. 0)\<close>
proof-
  have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f = Inf { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by (smt Collect_cong)
  hence \<open>Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} = (0::real)\<close>
    using \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f = 0\<close>
    by linarith
  moreover have \<open>{K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} \<noteq> {}\<close>
    using \<open>bounded_linear f\<close> bounded_linear.nonneg_bounded by auto 
  ultimately have \<open>\<forall> (\<epsilon>::real)>0. \<exists> K::real. K < \<epsilon>  \<and>  K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)\<close>
    by (metis (no_types, lifting) cInf_lessD mem_Collect_eq)
  hence \<open>norm (f x) \<le> 0\<close>
    for x
  proof(cases \<open>norm x = 0\<close>)
    case True
    then show ?thesis
      using assms(1) linear_simps(3) by auto 
  next
    case False
    then show ?thesis 
    proof-
      have \<open>norm x > 0\<close>
        using False by auto
      have \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> K::real. K < \<epsilon>  \<and>  K \<ge> 0 \<and> (norm (f x) \<le> norm x * K)\<close>
        for \<epsilon>::real
        using  \<open>\<forall> (\<epsilon>::real)>0. \<exists> K::real. K < \<epsilon>  \<and>  K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)\<close>
        by blast
      hence \<open>\<epsilon> > 0 \<Longrightarrow> norm (f x) \<le> norm x * \<epsilon>\<close>
        for \<epsilon>::real
      proof-
        assume \<open>\<epsilon> > 0\<close>
        then obtain K where  \<open>K < \<epsilon>\<close> and \<open>K \<ge> 0\<close> and \<open>norm (f x) \<le> norm x * K\<close>
          using \<open>\<And> \<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists> K::real. K < \<epsilon>  \<and>  K \<ge> 0 \<and> (norm (f x) \<le> norm x * K)\<close>
          by blast
        from \<open>norm (f x) \<le> norm x * K\<close> \<open>K \<ge> 0\<close> \<open>K < \<epsilon>\<close>
        show ?thesis
          by (smt mult_left_less_imp_less norm_ge_zero)  
      qed
      hence \<open>\<epsilon> > 0 \<Longrightarrow> norm (f x) \<le> \<epsilon>\<close>
        for \<epsilon>::real
      proof-
        assume \<open>\<epsilon> > 0\<close>
        hence \<open>\<epsilon> / norm x > 0\<close>
          using \<open>0 < norm x\<close> linordered_field_class.divide_pos_pos by blast
        hence \<open>norm (f x) \<le> norm x * (\<epsilon>/norm x)\<close>
          using \<open>\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> norm (f x) \<le> norm x * \<epsilon>\<close> by blast
        thus ?thesis 
          using False by auto 
      qed
      thus ?thesis
        by (meson eucl_less_le_not_le leI nice_ordered_field_class.dense_le_bounded)
    qed
  qed
  hence \<open>norm (f x) = 0\<close>
    for x
    by simp
  thus ?thesis
    by auto 
qed

(* TODO: exists? *)
lemma operator_norm_of_zero: \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})(\<lambda> _::('a::real_normed_vector). (0::('b::real_normed_vector))) = 0\<close>
proof-
  have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})(\<lambda> _::'a. 0::'b) = Inf { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm ((\<lambda> _::'a. 0::'b) x) \<le> norm x * K)}\<close>
    by (smt Collect_cong )
  moreover have \<open>(\<forall>x. norm ((\<lambda> _::'a. 0::'b) x) \<le> norm x * (0::real))\<close>
    by simp
  ultimately show ?thesis
  proof -
    have "\<exists>r. 0 = r \<and> 0 \<le> r \<and> (\<forall>a. norm (0::'b) \<le> norm (a::'a) * r)"
      by (metis (lifting) \<open>\<forall>x. norm 0 \<le> norm x * 0\<close> order_refl)
    then have "0 \<in> {r |r. 0 \<le> r \<and> (\<forall>a. norm (0::'b) \<le> norm (a::'a) * r)}"
      by blast
    then show ?thesis
      by (metis (lifting) cInf_eq_minimum mem_Collect_eq)
  qed
qed

(* TODO: exists? *)
lemma operator_norm_triangular:
  fixes f g :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close> and \<open>bounded_linear g\<close>
  shows \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})(\<lambda>t. f t + g t)
           \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f + (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})g\<close>
proof-
  have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f = Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by simp
  moreover have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})g = Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)}\<close>
    by simp
  moreover have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})(\<lambda>t. f t + g t) = Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x + g x) \<le> norm x * K)}\<close>
    by simp
  moreover have \<open>Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x + g x) \<le> norm x * K)}
              \<le> Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
               + Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)}\<close>
  proof-
    have \<open>Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
        + Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)}
        \<in> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x + g x) \<le> norm x * K)}\<close>
    proof-
      have \<open>Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
        + Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)} \<ge> 0\<close>
      proof-
        have \<open>Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} \<ge> 0\<close>
        proof-
          have \<open>K \<in> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} \<Longrightarrow> K \<ge> 0\<close>
            for K::real
            by blast
          moreover have \<open>{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} \<noteq> {}\<close>
            using \<open>bounded_linear f\<close> bounded_linear.bounded bounded_linear.nonneg_bounded by auto 
          ultimately show ?thesis
            by (meson cInf_greatest)  
        qed
        moreover have \<open>Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)} \<ge> 0\<close>
        proof-
          have \<open>K \<in> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)} \<Longrightarrow> K \<ge> 0\<close>
            for K::real
            by blast
          moreover have \<open>{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)} \<noteq> {}\<close>
            using \<open>bounded_linear g\<close> bounded_linear.bounded bounded_linear.nonneg_bounded by auto 
          ultimately show ?thesis
            by (meson cInf_greatest)  
        qed
        ultimately show ?thesis by simp
      qed
      moreover have \<open>norm (f x + g x) \<le>
 norm x * (Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
         + Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)})\<close>
        for x
      proof- 
        have \<open>norm (f x + g x) \<le> norm (f x) + norm (g x)\<close>
          by (simp add: norm_triangle_ineq)
        moreover have \<open>norm (f x) \<le> norm x * (Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})\<close>
          using operation_norm_intro  \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f = Inf {K |K. 0 \<le> K \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close> assms(1) by fastforce 
        moreover have \<open>norm (g x) \<le> norm x * (Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)})\<close>
          using operation_norm_intro  \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})g = Inf {K |K. 0 \<le> K \<and> (\<forall>x. norm (g x) \<le> norm x * K)}\<close> assms(2) by fastforce 
        ultimately show ?thesis
          by (smt ring_class.ring_distribs(1)) 
      qed 
      ultimately show ?thesis
        by blast 
    qed
    moreover have \<open>bdd_below { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x + g x) \<le> norm x * K)}\<close>
      by auto
    ultimately show ?thesis 
      using Conditionally_Complete_Lattices.conditionally_complete_lattice_class.cInf_lower
      by (simp add: cInf_lower)
  qed
  ultimately show ?thesis
    by linarith 
qed


(* TODO: exists? *)
lemma operator_norm_prod_real: 
  fixes a::real and f::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close> 
  shows \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})(\<lambda>t. a *\<^sub>R f t) = \<bar>a\<bar> * (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f\<close>
proof-
  have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f = Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by simp
  moreover have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})(\<lambda>t. a *\<^sub>R f t) = Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K)}\<close>
    by simp
  moreover have \<open>Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K)}
               =  \<bar>a\<bar> * Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
  proof-
    have \<open>a \<noteq> 0 \<Longrightarrow> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K)}
               =  {\<bar>a\<bar> * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    proof-
      assume \<open>a \<noteq> 0\<close>
      have \<open>K \<in> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K)}
               \<Longrightarrow> K \<in>  {\<bar>a\<bar> * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
        for K
      proof-
        have \<open>\<bar>a\<bar> > 0\<close> using \<open>a \<noteq> 0\<close> by simp
        assume \<open>K \<in> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K)}\<close>
        then obtain \<open>K \<ge> 0\<close> and \<open>\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K\<close>
          by blast
        define k :: real where \<open>k = K / \<bar>a\<bar>\<close>
        hence \<open>K = \<bar>a\<bar> * k\<close>
          using \<open>0 < \<bar>a\<bar>\<close> by simp
        moreover have \<open>k \<ge> 0\<close> using \<open>\<bar>a\<bar> > 0\<close> and \<open>K \<ge> 0\<close>
          by (simp add: k_def)
        moreover have \<open>norm (f x) \<le> norm x * k\<close>
          for x
        proof-
          have \<open>norm (a *\<^sub>R f x) \<le> norm x * K\<close>
            using \<open>\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K\<close> by blast
          hence \<open>norm (a *\<^sub>R f x) \<le> norm x * ( \<bar>a\<bar>*k )\<close>
            using calculation(1) by blast
          hence \<open> \<bar>a\<bar>* norm (f x) \<le> norm x * ( \<bar>a\<bar>*k )\<close>
            by simp
          thus ?thesis using \<open>\<bar>a\<bar> > 0\<close>
            by simp 
        qed
        ultimately show ?thesis
          by blast 
      qed
      moreover have \<open>K \<in>  {\<bar>a\<bar> * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
                \<Longrightarrow> K \<in> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K)}\<close>
        for K
      proof-
        assume \<open>K \<in> {\<bar>a\<bar> * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
        then obtain k :: real 
          where \<open>K = \<bar>a\<bar> * k\<close> and \<open>k \<ge> 0\<close> and \<open>\<forall>x. norm (f x) \<le> norm x * k\<close>
          by blast 
        have \<open>\<bar>a\<bar> \<ge> 0\<close>
          by simp
        hence \<open>K \<ge> 0\<close>
          using  \<open>k \<ge> 0\<close>  \<open>K = \<bar>a\<bar> * k\<close> by simp
        moreover have \<open>norm (a *\<^sub>R f x) \<le> norm x * K\<close>
          for x
        proof-
          have \<open>norm (f x) \<le> norm x * k\<close>
            using  \<open>\<forall>x. norm (f x) \<le> norm x * k\<close>
            by blast
          hence \<open>\<bar>a\<bar> * norm (f x) \<le> \<bar>a\<bar> * (norm x * k)\<close>
            using \<open>\<bar>a\<bar> \<ge> 0\<close> ordered_comm_semiring_class.comm_mult_left_mono by blast
          hence \<open>\<bar>a\<bar> * norm (f x) \<le> norm x * K\<close>
            using \<open>K = \<bar>a\<bar> * k\<close>
            by (simp add: mult.left_commute) 
          thus ?thesis
            by simp 
        qed
        ultimately show ?thesis by blast
      qed
      ultimately show ?thesis
        by blast
    qed
    have  \<open>Inf { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K)}
               = Inf  {\<bar>a\<bar> * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    proof(cases \<open>a = 0\<close>)
      case True
      have \<open>{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K)} = {0..}\<close>
      proof-
        have \<open>K \<ge> 0 \<Longrightarrow> \<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K\<close>
          for K::real
          using \<open>a = 0\<close>
          by simp
        thus ?thesis
          by blast 
      qed
      moreover have \<open>{\<bar>a\<bar> * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} = {0}\<close>
        by (simp add: True assms bounded_linear.nonneg_bounded)    
      ultimately show ?thesis
        by simp  
    next
      case False
      then show ?thesis using  \<open>a \<noteq> 0 \<Longrightarrow> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>R f x) \<le> norm x * K)}
               =  {\<bar>a\<bar> * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
        by simp
    qed
    moreover have \<open>Inf  {\<bar>a\<bar> * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
        = \<bar>a\<bar> * Inf  {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    proof-
      have \<open>\<bar>a\<bar> \<ge> 0\<close>
        by simp      
      have \<open>mono (\<lambda> K. \<bar>a\<bar> * K)\<close>
        by (simp add: mono_def mult_left_mono)    
      moreover have  \<open>continuous (at_right (Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})) (\<lambda> K. \<bar>a\<bar> * K)\<close>
        using bounded_linear_mult_right linear_continuous_within by auto       
      moreover have \<open>{K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} \<noteq> {}\<close>
        using assms bounded_linear.bounded bounded_linear.nonneg_bounded by fastforce
      moreover have \<open>bdd_below  {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
        by auto
      ultimately have \<open>(\<lambda> t. \<bar>a\<bar> * t) ( Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})
               = Inf ( (\<lambda> t. \<bar>a\<bar> * t) ` { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})\<close>
        using Topological_Spaces.continuous_at_Inf_mono 
        by blast
      have  \<open>(\<lambda> t. \<bar>a\<bar> * t) ( Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})
               = Inf ( { (\<lambda> t. \<bar>a\<bar> * t) K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})\<close>
      proof-
        have \<open>(\<lambda> t. \<bar>a\<bar> * t) ` { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
          = {(\<lambda> t. \<bar>a\<bar> * t) K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
          by blast
        thus ?thesis using  \<open>(\<lambda> t. \<bar>a\<bar> * t) ( Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})
               = Inf ( (\<lambda> t. \<bar>a\<bar> * t) ` { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})\<close>
          by simp
      qed
      thus ?thesis
        by simp
    qed
    ultimately show ?thesis
      by linarith 
  qed
  ultimately show ?thesis
    by simp  
qed

(* TODO: exists? *)
lemma operator_norm_prod_complex:
  fixes a::complex and f::\<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes \<open>bounded_clinear f\<close> 
  shows \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})(\<lambda>t. a *\<^sub>C f t) = (cmod a) * (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f\<close>
proof-
  have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})f = Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by simp
  moreover have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})(\<lambda>t. a *\<^sub>C f t) = Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K)}\<close>
    by simp
  moreover have \<open>Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K)}
               =  (cmod a) * Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
  proof-
    have \<open>a \<noteq> 0 \<Longrightarrow> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K)}
               =  {(cmod a) * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    proof-
      assume \<open>a \<noteq> 0\<close>
      have \<open>K \<in> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K)}
               \<Longrightarrow> K \<in>  {(cmod a) * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
        for K
      proof-
        have \<open>cmod a > 0\<close> using \<open>a \<noteq> 0\<close> by simp
        assume \<open>K \<in> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K)}\<close>
        then obtain \<open>K \<ge> 0\<close> and \<open>\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K\<close>
          by blast
        define k :: real where \<open>k = K / cmod a\<close>
        hence \<open>K = (cmod a) * k\<close>
          using \<open>0 < cmod a\<close> by simp
        moreover have \<open>k \<ge> 0\<close> using \<open>cmod a > 0\<close> and \<open>K \<ge> 0\<close>
          by (simp add: k_def)
        moreover have \<open>norm (f x) \<le> norm x * k\<close>
          for x
        proof-
          have \<open>norm (a *\<^sub>C f x) \<le> norm x * K\<close>
            using \<open>\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K\<close> by blast
          hence \<open>norm (a *\<^sub>C f x) \<le> norm x * ( (cmod a)*k )\<close>
            using calculation(1) by blast
          hence \<open> (cmod a)* norm (f x) \<le> norm x * ( (cmod a)*k )\<close>
            by simp
          thus ?thesis using \<open>cmod a > 0\<close>
            by simp 
        qed
        ultimately show ?thesis
          by auto
      qed
      moreover have \<open>K \<in>  {(cmod a) * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
                \<Longrightarrow> K \<in> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K)}\<close>
        for K
      proof-
        assume \<open>K \<in> {(cmod a) * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
        then obtain k :: real 
          where \<open>K = (cmod a) * k\<close> and \<open>k \<ge> 0\<close> and \<open>\<forall>x. norm (f x) \<le> norm x * k\<close>
          by blast 
        have \<open>cmod a \<ge> 0\<close>
          by simp
        hence \<open>K \<ge> 0\<close>
          using  \<open>k \<ge> 0\<close>  \<open>K = (cmod a) * k\<close> by simp
        moreover have \<open>norm (a *\<^sub>C f x) \<le> norm x * K\<close>
          for x
        proof-
          have \<open>norm (f x) \<le> norm x * k\<close>
            using  \<open>\<forall>x. norm (f x) \<le> norm x * k\<close>
            by blast
          hence \<open>(cmod a) * norm (f x) \<le> (cmod a) * (norm x * k)\<close>
            using \<open>(cmod a) \<ge> 0\<close> ordered_comm_semiring_class.comm_mult_left_mono by blast
          hence \<open>(cmod a) * norm (f x) \<le> norm x * K\<close>
            using \<open>K = (cmod a) * k\<close>
            by (simp add: mult.left_commute) 
          thus ?thesis
            by simp 
        qed
        ultimately show ?thesis by blast
      qed
      ultimately show ?thesis
        by blast
    qed
    have  \<open>Inf { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K)}
               = Inf  {(cmod a) * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    proof(cases \<open>a = 0\<close>)
      case True
      have \<open>{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K)} = {0..}\<close>
      proof-
        have \<open>K \<ge> 0 \<Longrightarrow> \<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K\<close>
          for K::real
          using \<open>a = 0\<close>
          by simp
        thus ?thesis
          by blast 
      qed
      moreover have \<open>{(cmod a) * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} = {0}\<close>
      proof-
        have \<open>{(cmod a) * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} 
            = {0 * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
          using \<open>a = 0\<close> by simp
        also have \<open>{0 * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
                = {0 | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
          by simp
        also have \<open> {0 | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} = {0}\<close>
        proof-
          have \<open>\<exists> K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)\<close>
            using \<open>bounded_clinear f\<close>
            unfolding bounded_clinear_def
            by (metis (no_types, hide_lams) bounded_clinear_axioms_def dual_order.antisym dual_order.trans mult.commute mult_zero_left norm_ge_zero order_refl zero_le_mult_iff)      
          thus ?thesis
            by simp 
        qed
        finally show ?thesis by blast
      qed
      ultimately show ?thesis
        by simp  
    next
      case False
      then show ?thesis using  \<open>a \<noteq> 0 \<Longrightarrow> { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (a *\<^sub>C f x) \<le> norm x * K)}
               =  {(cmod a) * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
        by simp
    qed
    moreover have \<open>Inf  {(cmod a) * K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
        = (cmod a) * Inf  {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    proof-
      have \<open>cmod a \<ge> 0\<close>
        by simp      
      have \<open>mono (\<lambda> K. (cmod a) * K)\<close>
        by (simp add: mono_def mult_left_mono)    
      moreover have  \<open>continuous (at_right (Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})) (\<lambda> K. (cmod a) * K)\<close>
        using bounded_linear_mult_right linear_continuous_within by auto       
      moreover have \<open>{K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} \<noteq> {}\<close>
        using bounded_linear.nonneg_bounded
        by (smt Collect_empty_eq_bot assms bot_empty_eq bounded_clinear.bounded_linear empty_iff mult.commute) 
      moreover have \<open>bdd_below  {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
        by auto
      ultimately have \<open>(\<lambda> t. (cmod a) * t) ( Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})
               = Inf ( (\<lambda> t. (cmod a) * t) ` { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})\<close>
        using Topological_Spaces.continuous_at_Inf_mono 
        by blast
      have  \<open>(\<lambda> t. (cmod a) * t) ( Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})
               = Inf ( { (\<lambda> t. (cmod a) * t) K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})\<close>
      proof-
        have \<open>(\<lambda> t. (cmod a) * t) ` { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}
          = {(\<lambda> t. (cmod a) * t) K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
          by blast
        thus ?thesis using  \<open>(\<lambda> t. (cmod a) * t) ( Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})
               = Inf ( (\<lambda> t. (cmod a) * t) ` { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})\<close>
          by simp
      qed
      thus ?thesis
        by simp
    qed
    ultimately show ?thesis
      by linarith 
  qed
  ultimately show ?thesis
    by simp
qed



(* TODO: trivial for onorm? TODO: reuse to show onorm = <your definition of operator_norm> *)
lemma norm_ball_1:
  assumes \<open>bounded_clinear T\<close>
  shows  \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T = Sup {norm (T x) | x. norm x < 1 }\<close>
proof(cases \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T = 0\<close>)
  case True
  from \<open>bounded_clinear T\<close>
  have \<open>norm (T x) \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T * norm x\<close>
    for x :: 'a
  proof -
    have "norm (T x) \<le> norm x * Inf {r |r. 0 \<le> r \<and> (\<forall>a. norm (T a) \<le> norm a * r)}"
      using assms(1) bounded_clinear.bounded_linear operation_norm_intro by blast
    then show ?thesis
      by (simp add: mult.commute)
  qed

  hence \<open>norm (T x) = 0\<close>
    for x::'a
    using True
    by auto
  hence \<open>{norm (T x) | x. norm x < 1 } = {0}\<close>
    by (smt Collect_cong norm_zero singleton_conv)
  hence \<open>Sup {norm (T x) | x. norm x < 1 } = 0\<close>
    by simp
  thus  ?thesis using True by simp 
next
  case False
  hence \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T \<noteq> 0\<close>
    by blast
  then show ?thesis 
  proof-
    have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T = 
      Inf {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}\<close>
      by simp

    have \<open>\<forall> x. norm x \<ge> 0\<close>
      by simp
    have \<open>Sup {norm (T x) | x. norm x < 1 }
         \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T\<close>
    proof-
      have \<open>K \<in> {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}
                  \<Longrightarrow> Sup {norm (T x) | x. norm x < 1 } \<le> K\<close>
        for K
      proof-
        assume \<open>K \<in> {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}\<close>
        hence \<open>K \<ge> 0\<close>
          by blast
        from  \<open>K \<in> {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}\<close>
        have \<open>norm (T x) \<le> norm x * K\<close>
          for x
          by blast

        have \<open>K \<noteq> 0\<close>
          using \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T \<noteq> 0\<close> 
          by (smt Collect_cong \<open>\<And>x. norm (T x) \<le> norm x * K\<close> \<open>\<forall>x. 0 \<le> norm x\<close> mult_nonneg_nonneg mult_not_zero norm_zero  operator_norm_of_zero)

        have \<open>x \<noteq> 0 \<Longrightarrow> (inverse (norm x)) * norm (T x) \<le>  K\<close>
          for x
        proof-
          assume \<open>x \<noteq> 0\<close>
          hence \<open>inverse (norm x) > 0\<close>
            by simp
          have \<open>inverse (norm x) * norm (T x) \<le> inverse (norm x) * norm x * K\<close>
            using \<open>norm (T x) \<le> norm x * K\<close>  \<open>inverse (norm x) > 0\<close>
            by (smt linordered_field_class.sign_simps(23) mult_left_less_imp_less)
          thus ?thesis using  \<open>inverse (norm x) > 0\<close> by simp
        qed
        hence \<open>x \<noteq> 0 \<Longrightarrow> norm ((inverse (norm x)) *\<^sub>R T x ) \<le>  K\<close>
          for x
          by simp
        hence \<open>x \<noteq> 0 \<Longrightarrow> norm ( T ((inverse (norm x)) *\<^sub>R x) ) \<le>  K\<close>
          for x
        proof-
          assume \<open>x \<noteq> 0\<close>
          from  \<open>bounded_clinear T\<close>
          have  \<open>bounded_linear T\<close>
            by (simp add: bounded_clinear.bounded_linear)
          hence \<open>\<forall>r x. T (r *\<^sub>R x) = r *\<^sub>R T x\<close>
            by (simp add: linear_simps(5))
          hence \<open>T ((inverse (norm x)) *\<^sub>R x) = (inverse (norm x)) *\<^sub>R T x\<close>
            by auto
          thus ?thesis
            using \<open>\<And>x. x \<noteq> 0 \<Longrightarrow> norm (T x /\<^sub>R norm x) \<le> K\<close> \<open>x \<noteq> 0\<close> by auto 
        qed         
        hence \<open>norm x = 1 \<Longrightarrow> norm (T x) \<le>  K\<close>
          for x
          by (metis \<open>\<And>x. norm (T x) \<le> norm x * K\<close> mult_cancel_right2)
        hence \<open>norm x < 1 \<Longrightarrow> norm (T x) <  K\<close>
          for x
        proof(cases \<open>x = 0\<close>)
          case True
          thus ?thesis
            by (smt \<open>0 \<le> K\<close> \<open>K \<noteq> 0\<close> \<open>\<And>x. norm (T x) \<le> norm x * K\<close> mult_cancel_left1 norm_zero) 
        next          
          assume \<open>norm x < 1\<close>
          case False
          hence \<open>x \<noteq> 0\<close> by blast
          hence \<open>norm ( (inverse (norm x)) *\<^sub>R x ) = 1\<close>
          proof-
            have \<open>norm ( (inverse (norm x)) *\<^sub>R x )
            = (inverse (norm x)) * norm x\<close>
              by auto
            also have \<open>... = 1\<close>
              by (simp add: False)
            finally show ?thesis by blast
          qed
          hence \<open>norm (T ( (inverse (norm x)) *\<^sub>R x )) \<le>  K\<close>
            by (simp add: \<open>\<And>x. norm x = 1 \<Longrightarrow> norm (T x) \<le> K\<close>)
          hence \<open>norm (  (inverse (norm x)) *\<^sub>R T x ) \<le>  K\<close>
            using False \<open>\<And>x. x \<noteq> 0 \<Longrightarrow> norm (T x /\<^sub>R norm x) \<le> K\<close> by auto
          hence \<open>\<bar>(inverse (norm x))\<bar> * norm ( T x ) \<le>  K\<close>
            by simp
          hence \<open>(inverse (norm x)) * norm ( T x ) \<le>  K\<close>
            by simp
          hence \<open>norm ( T x ) \<le> (norm x) *  K\<close>
            by (simp add: \<open>\<And>x. norm (T x) \<le> norm x * K\<close>)
          also have \<open>(norm x) *  K < K\<close>
          proof-
            have  \<open>norm x > 0\<close>
              by (simp add: False)
            thus ?thesis using \<open>norm x < 1\<close>  \<open>K \<noteq> 0\<close> \<open>K \<ge> 0\<close>
              by auto 
          qed
          finally show ?thesis by blast
        qed
        hence \<open>\<forall> J \<in> {norm (T x) | x. norm x < 1 }. J < K\<close>
          by blast
        hence \<open>\<forall> J \<in> {norm (T x) | x. norm x < 1 }. J \<le> K\<close>
          by auto
        moreover have \<open>{norm (T x) | x. norm x < 1 } \<noteq> {}\<close>
          by (smt Collect_empty_eq norm_zero) 
        moreover have \<open>bdd_above {norm (T x) | x. norm x < 1 }\<close>
          using calculation(1) by fastforce        
        ultimately have \<open>Sup {norm (T x) | x. norm x < 1 } \<le> K\<close>
          by (simp add: cSup_le_iff)
        thus ?thesis 
          by auto
      qed 
      hence \<open>\<forall> K. K \<in> {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}
                  \<longrightarrow> Sup {norm (T x) | x. norm x < 1 } \<le> K\<close>
        by blast
      moreover have \<open>{K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)} \<noteq> {}\<close>
        using \<open>bounded_clinear T\<close> bounded_clinear_refined
        by auto
      moreover have \<open>bdd_below {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}\<close>
        by auto
      ultimately have \<open>Sup {norm (T x) | x. norm x < 1 }
         \<le> Inf {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}\<close>
        by (meson cInf_greatest)
      thus ?thesis
        by (simp add: \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T = Inf {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}\<close>)
    qed
    moreover have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T 
        \<le> Sup {norm (T x) | x. norm x < 1 }\<close>
    proof-
      have \<open>\<forall> y. norm (T y) \<le>  norm y * (Sup {norm (T x) | x. norm x < 1 })\<close>
      proof(rule classical)
        assume \<open>\<not> (\<forall> y. norm (T y) \<le> norm y * (Sup {norm (T x) | x. norm x < 1 }))\<close>
        hence \<open>\<exists> y. norm (T y) > norm y * (Sup {norm (T x) | x. norm x < 1 })\<close>
          by smt
        then obtain y where \<open>norm (T y) > norm y * (Sup {norm (T x) | x. norm x < 1 })\<close>
          by blast
        hence \<open>y \<noteq> 0\<close>
          by (smt assms(1) bounded_clinear_refined mult_cancel_left1 norm_zero) 
        hence \<open>norm y \<noteq> 0\<close>
          by simp
        hence \<open>norm y > 0\<close>
          by simp
        hence \<open>(inverse (norm y)) > 0\<close>
          by simp
        hence  \<open>(inverse (norm y)) * norm (T y) > (inverse (norm y)) * norm y * (Sup {norm (T x) | x. norm x < 1 })\<close>
          using  \<open>norm (T y) > norm y * (Sup {norm (T x) | x. norm x < 1 })\<close>
          by (metis (no_types, lifting) ordered_field_class.sign_simps(23) ordered_semiring_strict_class.mult_strict_left_mono)
        hence  \<open>(inverse (norm y)) * norm (T y) >  (Sup {norm (T x) | x. norm x < 1 })\<close>
          using \<open>norm y \<noteq> 0\<close> by auto
        hence  \<open>\<bar>(inverse (norm y))\<bar> * norm (T y) >  (Sup {norm (T x) | x. norm x < 1 })\<close>
          by simp
        hence  \<open>norm ((inverse (norm y)) *\<^sub>R  T y) >  (Sup {norm (T x) | x. norm x < 1 })\<close>
          by simp
        hence  \<open>norm (T ((inverse (norm y)) *\<^sub>R y)) >  (Sup {norm (T x) | x. norm x < 1 })\<close>
        proof-
          from \<open>bounded_clinear T\<close>
          have \<open>bounded_linear T\<close>
            by (simp add: bounded_clinear.bounded_linear)
          hence \<open>(inverse (norm y)) *\<^sub>R  (T y) = T ((inverse (norm y)) *\<^sub>R y)\<close>
            unfolding bounded_linear_def linear_def
            by (simp add: \<open>bounded_linear T\<close> linear_simps(5))           
          thus ?thesis
            using \<open>Sup {norm (T x) |x. norm x < 1} < norm (T y /\<^sub>R norm y)\<close> by auto 
        qed
        define z where \<open>z \<equiv> (inverse (norm y)) *\<^sub>R y\<close>
        hence  \<open>norm (T z) >  (Sup {norm (T x) | x. norm x < 1 })\<close>
          by (simp add: \<open>Sup {norm (T x) |x. norm x < 1} < norm (T (y /\<^sub>R norm y))\<close>)

        have \<open>norm z = 1\<close>
          by (simp add: \<open>y \<noteq> 0\<close> z_def)
        have \<open>isCont T z\<close>
          using assms(1) bounded_linear_continuous by auto
        hence \<open>x \<longlonglongrightarrow> z \<Longrightarrow> (\<lambda> n. T (x n)) \<longlonglongrightarrow> T z\<close>
          for x :: \<open>nat \<Rightarrow> 'a\<close>
          by (simp add: isCont_tendsto_compose)
        hence \<open>(\<lambda> n::nat. ( 1 - inverse (real (Suc n)) ) *\<^sub>R z ) \<longlonglongrightarrow> z
                   \<Longrightarrow> (\<lambda> n::nat. T ((1 - inverse (real (Suc n)) ) *\<^sub>R z) ) \<longlonglongrightarrow> T z\<close>
          by blast
        moreover have \<open>(\<lambda> n::nat. ( 1 - inverse (real (Suc n)) ) *\<^sub>R z ) \<longlonglongrightarrow> z\<close>
        proof-
          have \<open>(\<lambda> n::nat. ( 1 + ( - inverse (real (Suc n)) )) ) \<longlonglongrightarrow> 1\<close>
            using Limits.LIMSEQ_inverse_real_of_nat_add_minus
            by blast
          have \<open>isCont (\<lambda> r. r *\<^sub>R z) 1\<close>
            using isCont_scaleR by auto
          have  \<open>( \<lambda> m. (\<lambda> r. r *\<^sub>R z) ( (\<lambda> n::nat. ( 1 + ( - inverse (real (Suc n)) ))) m) ) \<longlonglongrightarrow> (\<lambda> r. r *\<^sub>R z) 1\<close>
            using  \<open>isCont (\<lambda> r. r *\<^sub>R z) 1\<close> \<open>(\<lambda> n::nat. ( 1 + ( - inverse (real (Suc n)) )) ) \<longlonglongrightarrow> 1\<close>
            by (rule isCont_tendsto_compose) 
          hence  \<open>(\<lambda> n::nat. (\<lambda> r. r *\<^sub>R z) ( 1 + ( - inverse (real (Suc n)) )) ) \<longlonglongrightarrow> (\<lambda> r. r *\<^sub>R z) 1\<close>
            by auto
          hence  \<open>(\<lambda> n::nat. (\<lambda> r. r *\<^sub>R z) ( 1 + ( - inverse (real (Suc n)) )) ) \<longlonglongrightarrow> z\<close>
            by simp
          hence  \<open>(\<lambda> n::nat. ( 1 + ( - inverse (real (Suc n)) )) *\<^sub>R z ) \<longlonglongrightarrow> z\<close>
            by simp
          thus ?thesis by simp
        qed
        ultimately have \<open>(\<lambda> n::nat. T ((1 - inverse (real (Suc n)) ) *\<^sub>R z) ) \<longlonglongrightarrow> T z\<close>
          by blast
        have \<open>norm ( ( 1 - inverse (real (Suc n)) ) *\<^sub>R z ) < 1\<close>
          for n
        proof-
          have \<open>norm ( ( 1 - inverse (real (Suc n)) ) *\<^sub>R z )  = \<bar> ( 1 - inverse (real (Suc n)) )\<bar> * norm  z\<close>
            by simp
          moreover have \<open>1 - inverse (real (Suc n)) \<ge> 0\<close>
            by (smt One_nat_def less_eq_Suc_le nice_ordered_field_class.one_less_inverse_iff real_of_nat_ge_one_iff zero_less_Suc)

          ultimately have \<open>norm ( ( 1 - inverse (real (Suc n)) ) *\<^sub>R z )  =  ( 1 - inverse (real (Suc n)) ) * norm  z\<close>
            by linarith
          moreover have \<open>( 1 - inverse (real (Suc n)) ) < 1\<close>
            by simp
          ultimately show ?thesis
            by (simp add: \<open>norm z = 1\<close>) 
        qed
        hence \<open>norm ( T ( ( 1 - inverse (real (Suc n)) ) *\<^sub>R z ) ) \<in> {norm (T x) |x. norm x < 1}\<close>
          for n
          by blast
        moreover have \<open>{norm (T x) |x. norm x < 1} \<noteq> {}\<close>
          by (metis (mono_tags, lifting) Collect_empty_eq norm_eq_zero zero_less_one)

        moreover have \<open>bdd_above {norm (T x) |x. norm x < 1}\<close>
        proof-
          have \<open>\<forall> x. norm (T x) \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T * norm x\<close>
          proof -
            { fix aa :: 'a
              have "norm (T aa) \<le> norm aa * Inf {r |r. 0 \<le> r \<and> (\<forall>a. norm (T a) \<le> norm a * r)}"
                using assms(1) bounded_clinear.bounded_linear operation_norm_intro by blast
              then have "norm (T aa) \<le> Inf {r |r. 0 \<le> r \<and> (\<forall>a. norm (T a) \<le> norm a * r)} * norm aa"
                by (simp add: mult.commute) }
            then show ?thesis
              by meson
          qed
          hence \<open>\<forall> x. norm x < 1 \<longrightarrow> norm (T x) \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T\<close>
            using  mult_less_cancel_left2 
            by (smt \<open>\<forall>x. 0 \<le> norm x\<close> \<open>norm z = 1\<close> mult_cancel_left1)
          thus ?thesis by auto
        qed
        ultimately have \<open>\<forall> n\<ge>0. norm ( T ( ( 1 - inverse (real (Suc n)) ) *\<^sub>R z ) ) \<le> Sup {norm (T x) |x. norm x < 1}\<close>
          by (simp add: cSup_upper)
        moreover have  \<open>(\<lambda> n::nat. norm (T ((1 - inverse (real (Suc n)) ) *\<^sub>R z) )) \<longlonglongrightarrow> norm (T z)\<close>
          using  \<open>(\<lambda> n::nat. T ((1 - inverse (real (Suc n)) ) *\<^sub>R z) ) \<longlonglongrightarrow> T z\<close>
          by (simp add: tendsto_norm)

        ultimately have  \<open>norm ( T  z  ) \<le> Sup {norm (T x) |x. norm x < 1}\<close>
          by (simp add: Lim_bounded) 
        hence \<open>norm ( T  z ) < norm ( T  z )\<close> using  \<open>norm (T z) >  (Sup {norm (T x) | x. norm x < 1 })\<close>
          by simp
        thus ?thesis by blast
      qed
      moreover have \<open>Sup {norm (T x) | x. norm x < 1 } \<ge> 0\<close>
      proof-
        have \<open>norm (T x) \<ge> 0\<close> 
          for x
          by auto
        moreover have \<open>{norm (T x) | x. norm x < 1 } \<noteq> {}\<close>
          by (smt Collect_empty_eq norm_zero) 
        moreover have \<open>bdd_above {norm (T x) | x. norm x < 1 }\<close>
        proof-
          have \<open>\<forall> x. norm (T x) \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T * norm x\<close>
          proof -
            { fix aa :: 'a
              have "norm (T aa) \<le> norm aa * Inf {r |r. 0 \<le> r \<and> (\<forall>a. norm (T a) \<le> norm a * r)}"
                using assms(1) bounded_clinear.bounded_linear operation_norm_intro by blast
              then have "norm (T aa) \<le> Inf {r |r. 0 \<le> r \<and> (\<forall>a. norm (T a) \<le> norm a * r)} * norm aa"
                by (simp add: mult.commute) }
            then show ?thesis
              by meson
          qed

          hence \<open>\<forall> x. norm x < 1 \<longrightarrow> norm (T x) \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T\<close>
            using False Collect_cong assms(1) mult_less_cancel_left2 operator_norm_non_neg
            by smt
          thus ?thesis by auto
        qed
        ultimately show ?thesis 
          by (smt cSup_upper empty_Collect_eq mem_Collect_eq)
      qed
      ultimately have \<open>Sup {norm (T x) | x. norm x < 1 }
         \<in> {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}\<close>
        by simp   
      moreover have \<open>{K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)} \<noteq> {}\<close>
        using \<open>bounded_clinear T\<close> bounded_clinear_refined
        by auto
      moreover have \<open>bdd_below {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}\<close>
        by auto
      ultimately have \<open>Inf {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)} \<le> Sup {norm (T x) | x. norm x < 1 }\<close>
        by (simp add: cInf_lower)
      thus ?thesis using \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T =
      Inf {K |K. 0 \<le> K \<and> (\<forall>x. norm (T x) \<le> norm x * K)}\<close>
        by simp        
    qed
    ultimately show ?thesis
      by auto 
  qed
qed

(* TODO: as for norm_ball_1 *)
lemma norm_ball:
  fixes r :: real 
  assumes \<open>r > 0\<close> and \<open>bounded_clinear T\<close>
  shows  \<open>((\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T) * r = Sup {norm (T x) | x. norm x < r}\<close>
proof-                     
  have  \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T = Sup {norm (T x) | x. norm x < 1 }\<close>
    using assms(2) less_numeral_extra(1) norm_ball_1 by blast
  moreover have \<open>r * Sup {norm (T x) | x. norm x < 1 } = Sup {norm (T x) | x. norm x < r}\<close>
  proof-
    have \<open>r * (Sup  {norm (T x) | x. norm x < 1}) 
          = Sup  {r * (norm (T x)) | x. norm x < 1}\<close>
    proof-
      define S where \<open>S \<equiv> {norm (T x) | x. norm x < 1}\<close>
      have \<open>((*) r) (Sup S) = Sup ( ((*) r) ` S )\<close>
      proof-
        have \<open>mono ((*) r)\<close>
          using \<open>r > 0\<close>
          by (simp add: mono_def) 
        moreover have \<open>S \<noteq> {}\<close>
        proof-
          have \<open>norm (0::'a) = 0\<close>
            by auto
          thus ?thesis unfolding S_def
          proof -
            have "\<exists>a. norm (a::'a) < 1"
              by (metis \<open>norm 0 = 0\<close> zero_less_one)
            then show "{norm (T a) |a. norm a < 1} \<noteq> {}"
              by blast
          qed 
        qed
        moreover have \<open>bdd_above S\<close>
        proof-
          have \<open>norm (T x) \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T * norm x\<close>
            for x
          proof -
            have "norm (T x) \<le> norm x * Inf {r |r. 0 \<le> r \<and> (\<forall>a. norm (T a) \<le> norm a * r)}"
              using assms(2) bounded_clinear.bounded_linear operation_norm_intro by blast
            then show ?thesis
              by (simp add: ordered_field_class.sign_simps(24))
          qed

          hence \<open>norm x < 1 \<Longrightarrow>  norm (T x) \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T\<close>
            for x
          proof-
            assume \<open>norm x < 1\<close>
            moreover have \<open>norm x \<ge> 0\<close>
              by auto
            moreover have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T  \<ge> 0\<close>
              using assms(2) operator_norm_non_neg by auto
            ultimately have \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T * norm x \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T\<close>
              using less_eq_real_def mult_left_le by blast
            have \<open>norm (T x) \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T * norm x\<close>
              using \<open>\<And>x. norm (T x) \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T * norm x\<close>
              by blast

            show ?thesis 
              using \<open>norm (T x) \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T * norm x\<close>
                \<open>(\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T * norm x \<le> (\<lambda> f. Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)})T\<close>
              by simp
          qed
          thus ?thesis using S_def
            using less_eq_real_def by fastforce 
        qed
        moreover have \<open>continuous (at_left (Sup S)) ((*) r)\<close>
        proof-
          have \<open>isCont ((*) r) x\<close>
            for x
            by auto
          thus ?thesis
            by (simp add: continuous_at_split)  
        qed
        ultimately show ?thesis
          using Topological_Spaces.continuous_at_Sup_mono
          by blast
      qed
      hence \<open>((*) r) (Sup  {norm (T x) | x. norm x < 1}) 
          = Sup ( ((*) r) `  {norm (T x) | x. norm x < 1} )\<close>
        using S_def by blast
      hence \<open>r * (Sup  {norm (T x) | x. norm x < 1}) 
          = Sup ( ((*) r) `  {norm (T x) | x. norm x < 1} )\<close>
        by blast
      hence \<open>r * (Sup  {norm (T x) | x. norm x < 1}) 
          = Sup  {((*) r) (norm (T x)) | x. norm x < 1}\<close>
        by (simp add: image_image setcompr_eq_image)
      hence \<open>r * (Sup  {norm (T x) | x. norm x < 1}) 
          = Sup  {r * (norm (T x)) | x. norm x < 1}\<close>
        by blast
      thus ?thesis by blast
    qed
    moreover have \<open>{r * (norm (T x)) | x. norm x < 1} 
      = {(norm (T x)) | x. norm x < r}\<close>
    proof-
      have \<open>{r * (norm (T x)) | x. norm x < 1}      
          = { norm ( r *\<^sub>R T x ) | x. norm x < 1}\<close>
      proof-
        have \<open>\<bar>r\<bar> * (norm (T x)) =  norm ( r *\<^sub>R T x )\<close>
          for x
          by simp    
        hence \<open>r * (norm (T x)) =  norm ( r *\<^sub>R T x )\<close>
          for x
          using \<open>r > 0\<close>
          by simp    
        thus ?thesis
          by presburger 
      qed
      also have \<open>...      
          = { norm ( T (r *\<^sub>R x) ) | x. norm x < 1}\<close>
      proof-
        have \<open>r *\<^sub>R (T x) = T (r *\<^sub>R x)\<close>
          for x
          using \<open>bounded_clinear T\<close>
          unfolding bounded_clinear_def clinear_def clinear_axioms_def
          by (simp add: scaleR_scaleC)          
        thus ?thesis
          by auto 
      qed
      also have \<open>...      
          = { norm ( T (r *\<^sub>R ((inverse r) *\<^sub>R  x)) ) | x. norm ((inverse r) *\<^sub>R  x) < 1}\<close>
      proof - (* sledgehammer *)
        { fix aa :: 'a and aaa :: "real \<Rightarrow> 'a" and aab :: 'a and rr :: real
          have "(0::real) = 1 \<longrightarrow> (\<exists>ra a. \<not> norm aa < 1 \<or> \<not> norm (aaa ra) < 1 \<or> \<not> norm (aab /\<^sub>R r) < 1 \<and> norm (T (r *\<^sub>R aa)) \<noteq> rr \<or> norm (T (r *\<^sub>R (aab /\<^sub>R r))) \<noteq> rr \<and> norm (T (r *\<^sub>R aa)) \<noteq> rr \<or> norm (T (r *\<^sub>R (a /\<^sub>R r))) = rr \<and> norm (a /\<^sub>R r) < 1)"
            by linarith
          then have "\<exists>ra a. \<not> norm aa < 1 \<or> \<not> norm (aaa ra) < 1 \<or> \<not> norm (aab /\<^sub>R r) < 1 \<and> norm (T (r *\<^sub>R aa)) \<noteq> rr \<or> norm (T (r *\<^sub>R (aab /\<^sub>R r))) \<noteq> rr \<and> norm (T (r *\<^sub>R aa)) \<noteq> rr \<or> norm (T (r *\<^sub>R (a /\<^sub>R r))) = rr \<and> norm (a /\<^sub>R r) < 1"
            by (metis (no_types) norm_one norm_zero right_inverse scaleR_one scaleR_scaleR scale_eq_0_iff zero_less_norm_iff) }
        then have "\<forall>a aa ra. Ex ((\<lambda>rb. \<forall>ab. \<exists>ac. \<not> norm a < 1 \<or> \<not> norm (ab::'a) < 1 \<or> \<not> norm (aa /\<^sub>R r) < 1 \<and> norm (T (r *\<^sub>R a)) \<noteq> ra \<or> norm (T (r *\<^sub>R (aa /\<^sub>R r))) \<noteq> ra \<and> norm (T (r *\<^sub>R a)) \<noteq> ra \<or> norm (T (r *\<^sub>R (ac /\<^sub>R r))) = ra \<and> norm (ac /\<^sub>R r) < 1)::real \<Rightarrow> bool)"
          by meson
        then show ?thesis
          by (metis (lifting))
      qed
      also have \<open>...      
          = { norm ( T x ) | x. norm ((inverse r) *\<^sub>R  x) < 1}\<close>
        using assms(1) by auto
      also have \<open>...      
          = { norm ( T x ) | x. \<bar>(inverse r)\<bar> * norm x < 1}\<close>
        by simp
      also have \<open>...      
          = { norm ( T x ) | x. (inverse r) * norm x < 1}\<close>
        using \<open>r > 0\<close>
        by auto
      also have \<open>...      
          = { norm ( T x ) | x. norm x < r}\<close>
      proof-
        have \<open>\<forall> x. (inverse r) * norm x < 1 \<longleftrightarrow> norm x < r\<close>
          by (smt assms(1) left_inverse linordered_field_class.positive_imp_inverse_positive mult_less_cancel_left)
        thus ?thesis
          by auto 
      qed
      finally show ?thesis by blast
    qed
    ultimately show ?thesis by simp   
  qed
  ultimately show ?thesis
    by (simp add: mult.commute) 
qed

(* NEW *)
lemma norm_set_nonempty1: 
  fixes f :: \<open>('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> 
  assumes \<open>bounded_linear f\<close> and \<open>f \<noteq> (\<lambda> _. 0)\<close>
  shows \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
proof-
  have \<open>\<exists> x::'a. x \<noteq> 0\<close>
    by (metis (full_types) assms(1) assms(2) linear_simps(3))
  hence \<open>\<exists> x::'a. norm x \<noteq> 0\<close>
    by simp
  hence \<open>\<exists> x::'a. norm x = 1\<close>
    by (metis (full_types) norm_sgn)
  thus ?thesis
    by simp 
qed

(* NEW *)
lemma norm_set_bdd_above1: 
  fixes f :: \<open>('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> 
  assumes \<open>bounded_linear f\<close> 
  shows \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
proof-
  have \<open>\<exists> M. \<forall> x. norm x = 1 \<longrightarrow> norm (f x) \<le> M\<close>
    by (metis assms bounded_linear.bounded)
  thus ?thesis
    by auto 
qed

(* NEW *)
lemma norm_set_bdd_above2: 
  fixes f :: \<open>('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> 
  assumes \<open>bounded_linear f\<close> 
  shows \<open>bdd_above {norm (f x) |x. norm x < 1}\<close>
proof-
  have \<open>\<exists> M. \<forall> x. norm x < 1 \<longrightarrow> norm (f x) \<le> M\<close>
  proof -
    { fix aa :: "real \<Rightarrow> 'a"
      obtain rr :: "('a \<Rightarrow> 'b) \<Rightarrow> real" where
        "\<And>f a. 0 \<le> rr f \<and> (\<not> bounded_linear f \<or> norm (f a) \<le> norm a * rr f)"
        using bounded_linear.nonneg_bounded by moura
      then have "\<exists>r. \<not> norm (aa r) < 1 \<or> norm (f (aa r)) \<le> r"
        by (metis assms dual_order.trans less_eq_real_def mult.commute mult_left_le) }
    then show ?thesis
      by metis
  qed  
  thus ?thesis
    by auto 
qed


(* NEW *)
proposition Operator_Norm_characterization_1:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close>
  shows  \<open>onorm f = Sup {norm (f x) | x. norm x < 1 }\<close>
proof(cases \<open>f = (\<lambda> _. 0)\<close>)
  case True
  have \<open>onorm f = 0\<close>
    by (simp add: True onorm_eq_0)
  moreover have \<open>Sup {norm (f x) | x. norm x < 1 } = 0\<close>
  proof-
    have \<open>norm (f x) = 0\<close>
      for x
      by (simp add: True)   
    hence \<open>{norm (f x) | x. norm x < 1 } = {0}\<close>
      by (smt Collect_cong norm_zero singleton_conv)    
    thus ?thesis by simp
  qed
  ultimately show ?thesis by simp
next
  case False
  have \<open>Sup {norm (f x) | x. norm x = 1} = Sup {norm (f x) | x. norm x < 1}\<close>
  proof-
    have \<open>Sup {norm (f x) | x. norm x = 1} \<le> Sup {norm (f x) | x. norm x < 1}\<close>
    proof-
      have \<open>{norm (f x) | x. norm x = 1} \<noteq> {}\<close>
        using False assms norm_set_nonempty1 by fastforce
      moreover have \<open>bdd_above {norm (f x) | x. norm x = 1}\<close>
        by (simp add: assms norm_set_bdd_above1)      
      moreover have \<open>y \<in> {norm (f x) | x. norm x = 1} \<Longrightarrow> y \<le> Sup {norm (f x) | x. norm x < 1}\<close>
        for y
      proof-
        assume \<open>y \<in> {norm (f x) | x. norm x = 1}\<close>
        hence \<open>\<exists> x. y = norm (f x) \<and> norm x = 1\<close>
          by blast
        then obtain x where \<open>y = norm (f x)\<close> and \<open>norm x = 1\<close>
          by auto
        have \<open>\<exists> yy. (\<forall> n::nat. yy n \<in> {norm (f x) | x. norm x < 1}) \<and> (yy \<longlonglongrightarrow> y)\<close>
        proof-
          define yy where \<open>yy n = (1 - (inverse (real (Suc n)))) *\<^sub>R y\<close>
            for n
          have \<open>yy n \<in> {norm (f x) | x. norm x < 1}\<close>
            for n
          proof-
            have \<open>yy n = norm (f ( (1 - (inverse (real (Suc n)))) *\<^sub>R x) )\<close>
            proof-
              have \<open>yy n = (1 - (inverse (real (Suc n)))) *\<^sub>R norm (f x)\<close>
                using yy_def \<open>y = norm (f x)\<close> by blast
              also have \<open>... = \<bar>(1 - (inverse (real (Suc n))))\<bar> *\<^sub>R norm (f x)\<close>
                by (simp add: nice_ordered_field_class.inverse_le_imp_le )
              also have \<open>... = norm ( (1 - (inverse (real (Suc n)))) *\<^sub>R (f x))\<close>
                by simp
              also have \<open>... = norm (f ((1 - (inverse (real (Suc n)))) *\<^sub>R  x))\<close>
                using \<open>bounded_linear f\<close>
                by (simp add: linear_simps(5)) 
              finally show ?thesis by blast
            qed
            moreover have \<open>norm ((1 - (inverse (real (Suc n)))) *\<^sub>R x) < 1\<close>
            proof-
              have \<open>norm ((1 - (inverse (real (Suc n)))) *\<^sub>R x) 
                  = \<bar>(1 - (inverse (real (Suc n))))\<bar> * norm x\<close>
                by simp
              hence \<open>norm ((1 - (inverse (real (Suc n)))) *\<^sub>R x) 
                  = (1 - (inverse (real (Suc n)))) * norm x\<close>
                by (simp add: linordered_field_class.inverse_le_1_iff)                
              thus ?thesis using \<open>norm x = 1\<close>
                by simp 
            qed
            ultimately show ?thesis
              by blast 
          qed
          moreover have \<open>yy \<longlonglongrightarrow> y\<close>
          proof-
            have \<open>(\<lambda> n. (1 - (inverse (real (Suc n)))) ) \<longlonglongrightarrow> 1\<close>
              using Limits.LIMSEQ_inverse_real_of_nat_add_minus by simp
            hence \<open>(\<lambda> n. (1 - (inverse (real (Suc n)))) *\<^sub>R y) \<longlonglongrightarrow> 1 *\<^sub>R y\<close>
              using Limits.tendsto_scaleR by blast
            hence \<open>(\<lambda> n. (1 - (inverse (real (Suc n)))) *\<^sub>R y) \<longlonglongrightarrow> y\<close>
              by simp
            hence \<open>(\<lambda> n. yy n) \<longlonglongrightarrow> y\<close>
              using yy_def by simp
            thus ?thesis by simp
          qed
          ultimately show ?thesis by blast
        qed
        then obtain yy
          where \<open>\<And> n::nat. yy n \<in> {norm (f x) | x. norm x < 1}\<close> and \<open>yy \<longlonglongrightarrow> y\<close>
          by auto
        have \<open>{norm (f x) | x. norm x < 1} \<noteq> {}\<close>
          using \<open>\<And>n. yy n \<in> {norm (f x) |x. norm x < 1}\<close> by auto          
        moreover have \<open>bdd_above {norm (f x) | x. norm x < 1}\<close>
          by (simp add: assms norm_set_bdd_above2)          
        ultimately have \<open>yy n \<le> Sup {norm (f x) | x. norm x < 1}\<close>
          for n
          using \<open>\<And> n::nat. yy n \<in> {norm (f x) | x. norm x < 1}\<close>
          by (simp add: cSup_upper)
        hence \<open>y \<le> Sup {norm (f x) | x. norm x < 1}\<close>
          using \<open>yy \<longlonglongrightarrow> y\<close> Topological_Spaces.Sup_lim
          by (meson LIMSEQ_le_const2) 
        thus ?thesis by blast
      qed
      ultimately show ?thesis
        by (meson cSup_least)
    qed
    moreover have \<open>Sup {norm (f x) | x. norm x < 1} \<le> Sup {norm (f x) | x. norm x = 1}\<close>
    proof-
      have \<open>{norm (f x) | x. norm x < 1} \<noteq> {}\<close>
        by (metis (mono_tags, lifting) Collect_empty_eq_bot bot_empty_eq empty_iff norm_zero zero_less_one)  
      moreover have \<open>bdd_above {norm (f x) | x. norm x < 1}\<close>
        using \<open>bounded_linear f\<close>
        by (simp add: norm_set_bdd_above2)        
      moreover have \<open>y \<in> {norm (f x) | x. norm x < 1} \<Longrightarrow> y \<le> Sup {norm (f x) | x. norm x = 1}\<close>
        for y
      proof(cases \<open>y = 0\<close>)
        case True
        then show ?thesis
          by (smt Collect_cong False assms cSup_upper empty_Collect_eq mem_Collect_eq norm_not_less_zero norm_set_bdd_above1 norm_set_nonempty1) 
      next
        case False
        hence \<open>y \<noteq> 0\<close> by blast
        assume \<open>y \<in> {norm (f x) | x. norm x < 1}\<close>
        hence \<open>\<exists> x. y = norm (f x) \<and> norm x < 1\<close>
          by blast
        then obtain x where \<open>y = norm (f x)\<close> and \<open>norm x < 1\<close>
          by blast
        have \<open>{norm (f x) | x. norm x = 1} \<noteq> {}\<close>
          using False \<open>y = norm (f x)\<close> assms norm_set_nonempty1 by fastforce
        moreover have \<open>bdd_above {norm (f x) | x. norm x = 1}\<close>
          using assms norm_set_bdd_above1 by force
        moreover have \<open>(1/norm x) * y \<in> {norm (f x) | x. norm x = 1}\<close>
        proof-
          have \<open>(1/norm x) * y  = norm (f ((1/norm x) *\<^sub>R x))\<close>
          proof-
            have \<open>(1/norm x) * y = (1/norm x) * norm (f x)\<close>
              by (simp add: \<open>y = norm (f x)\<close>)
            also have \<open>... = \<bar>1/norm x\<bar> * norm (f x)\<close>
              by simp
            also have \<open>... = norm ((1/norm x) *\<^sub>R (f x))\<close>
              by simp
            also have \<open>... = norm (f ((1/norm x) *\<^sub>R x))\<close>
              by (simp add: assms linear_simps(5))
            finally show ?thesis by blast
          qed
          moreover have \<open>norm ((1/norm x) *\<^sub>R x) = 1\<close>
          proof-              
            have \<open>x \<noteq> 0\<close>
              using  \<open>y \<noteq> 0\<close> \<open>y = norm (f x)\<close> assms linear_simps(3) by auto
            have \<open>norm ((1/norm x) *\<^sub>R x) = \<bar> (1/norm x) \<bar> * norm x\<close>
              by simp
            also have \<open>... = (1/norm x) * norm x\<close>
              by simp
            finally show ?thesis using \<open>x \<noteq> 0\<close>
              by simp 
          qed
          ultimately show ?thesis
            by blast 
        qed
        ultimately have \<open>(1/norm x) * y \<le> Sup {norm (f x) | x. norm x = 1}\<close>
          by (simp add: cSup_upper)
        moreover have \<open>y \<le> (1/norm x) * y\<close> 
          using \<open>norm x < 1\<close>
          by (metis \<open>y = norm (f x)\<close> assms less_eq_real_def linear_simps(3) mult_less_cancel_right2 nice_ordered_field_class.divide_less_eq_1_pos norm_eq_zero norm_ge_zero not_le) 
        thus ?thesis
          using calculation by linarith 
      qed
      ultimately show ?thesis
        by (meson cSup_least) 
    qed
    ultimately show ?thesis by simp
  qed
  moreover have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) | x. norm x = 1}\<close>
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
            then show ?thesis
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
        moreover have \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0} \<Longrightarrow> y \<in> {norm (f x) / norm x |x. True}\<close>
          for y
        proof(cases \<open>y = 0\<close>)
          case True
          then show ?thesis
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
            by (metis (full_types) False assms linear_simps(3) norm_sgn)
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
          by (simp add: assms norm_set_bdd_above1)          
        ultimately have \<open>y \<le> Sup {norm (f x) |x. norm x = 1}\<close>
          using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
          by (simp add: cSup_upper) 
        thus ?thesis using \<open>y \<ge> 0\<close> by simp
      qed
      moreover have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {0}) = Sup {norm (f x) |x. norm x = 1}\<close>
      proof-
        have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
          using False assms norm_set_nonempty1 by fastforce
        moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
          by (simp add: assms norm_set_bdd_above1)    
        have \<open>{0::real} \<noteq> {}\<close>
          by simp
        moreover have \<open>bdd_above {0::real}\<close>
          by simp
        ultimately have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {(0::real)})
             = max (Sup {norm (f x) |x. norm x = 1}) (Sup {0::real})\<close>
          by (smt \<open>bdd_above {norm (f x) |x. norm x = 1}\<close> cSup_insert_If cSup_singleton cSup_union_distrib insert_absorb2 sup.strict_order_iff sup_commute)
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
  ultimately have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) | x. norm x < 1 }\<close>
    by simp
  thus ?thesis using onorm_def
    by metis 
qed


(* NEW *)
proposition Operator_Norm_characterization_2:
  fixes f :: \<open>('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close>
  assumes \<open>bounded_linear f\<close>
  shows  \<open>onorm f = Inf {K. (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
  sorry

end
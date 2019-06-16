(*  Title:      bounded-Operators/bounded_Operators.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

References:             

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}

*)


(*
We will derive the properties of bounded operators from 
the properties of Cstar_algebras
*)

theory Bounded_Operators
  imports Complex_L2 "HOL-Library.Adhoc_Overloading" 
    "HOL-Analysis.Abstract_Topology"  Extended_Sorry
begin

subsection \<open>Preliminaries\<close>

(* The complex numbers are a Hilbert space *)
instantiation complex :: "chilbert_space" begin
instance ..
end

subsection \<open>Operator norm\<close>

(* The norm of a bouded operator *)
definition operator_norm::\<open>('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> real\<close> where
  \<open>operator_norm \<equiv> \<lambda> f. Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>

(* NEW *)
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

(* NEW *)
lemma operation_norm_intro:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
    and x :: 'a
  assumes \<open>bounded_linear f\<close>
  shows \<open>norm (f x) \<le> norm x * (operator_norm f)\<close>
proof-
  have \<open>operator_norm f = Inf { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by (simp add: operator_norm_def)
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

(* NEW *)
lemma operator_norm_zero:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close> and \<open>operator_norm f = 0\<close>
  shows \<open>f = (\<lambda> _::('a::real_normed_vector). (0::('b::real_normed_vector)))\<close>
proof-
  have \<open>operator_norm f = Inf { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by (smt Collect_cong operator_norm_def)
  hence \<open>Inf {K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)} = (0::real)\<close>
    using \<open>operator_norm f = 0\<close>
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

(* NEW *)
lemma operator_norm_of_zero: \<open>operator_norm (\<lambda> _::('a::real_normed_vector). (0::('b::real_normed_vector))) = 0\<close>
proof-
  have \<open>operator_norm (\<lambda> _::'a. 0::'b) = Inf { K | K::real. K \<ge> 0 \<and> (\<forall>x. norm ((\<lambda> _::'a. 0::'b) x) \<le> norm x * K)}\<close>
    by (smt Collect_cong operator_norm_def)
  moreover have \<open>(\<forall>x. norm ((\<lambda> _::'a. 0::'b) x) \<le> norm x * (0::real))\<close>
    by simp
  ultimately show ?thesis
  proof -
    have "\<exists>r. 0 = r \<and> 0 \<le> r \<and> (\<forall>a. norm (0::'b) \<le> norm (a::'a) * r)"
      by (metis (lifting) \<open>\<forall>x. norm 0 \<le> norm x * 0\<close> order_refl)
    then have "0 \<in> {r |r. 0 \<le> r \<and> (\<forall>a. norm (0::'b) \<le> norm (a::'a) * r)}"
      by blast
    then show ?thesis
      by (metis (lifting) \<open>operator_norm (\<lambda>_. 0) = Inf {K |K. 0 \<le> K \<and> (\<forall>x. norm 0 \<le> norm x * K)}\<close> cInf_eq_minimum mem_Collect_eq)
  qed
qed

(* NEW *)
lemma operator_norm_triangular:
  fixes f g :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>bounded_linear f\<close> and \<open>bounded_linear g\<close>
  shows \<open>operator_norm (\<lambda>t. f t + g t)
           \<le> operator_norm f + operator_norm g\<close>
proof-
  have \<open>operator_norm f = Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close>
    by (simp add: operator_norm_def)
  moreover have \<open>operator_norm g = Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)}\<close>
    by (simp add: operator_norm_def)
  moreover have \<open>operator_norm (\<lambda>t. f t + g t) = Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (f x + g x) \<le> norm x * K)}\<close>
    by (simp add: operator_norm_def)
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
          using operation_norm_intro  \<open>operator_norm f = Inf {K |K. 0 \<le> K \<and> (\<forall>x. norm (f x) \<le> norm x * K)}\<close> assms(1) by fastforce 
        moreover have \<open>norm (g x) \<le> norm x * (Inf{ K | K::real. K \<ge> 0 \<and> (\<forall>x. norm (g x) \<le> norm x * K)})\<close>
          using operation_norm_intro  \<open>operator_norm g = Inf {K |K. 0 \<le> K \<and> (\<forall>x. norm (g x) \<le> norm x * K)}\<close> assms(2) by fastforce 
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


(* NEW *)
lemma operator_norm_prod_real: \<open>operator_norm (\<lambda>t. a *\<^sub>R x t) = \<bar>a\<bar> * operator_norm x\<close>
  sorry

(* NEW *)
lemma operator_norm_prod_complex: \<open>operator_norm (\<lambda>t. a *\<^sub>C x t) = (cmod a) * operator_norm x\<close>
  sorry


subsection \<open>Riesz Representation\<close>

lemma bounded_clinearDiff: \<open>clinear A \<Longrightarrow> clinear B \<Longrightarrow> clinear (A - B)\<close>
  by (smt add_diff_add additive.add clinear.axioms(1) clinear.axioms(2) clinearI clinear_axioms_def complex_vector.scale_right_diff_distrib minus_apply)

(* TODO: remove and define locally in lemma *)
definition proportion :: \<open>('a::complex_vector) set \<Rightarrow> bool\<close> where
  \<open>proportion S =  (
  \<forall> x y. x \<in> S \<and> x \<noteq> 0 \<and> y \<in> S \<and> y \<noteq> 0 \<longrightarrow> (\<exists> k. x = k *\<^sub>C y) 
)\<close>

(* TODO: locally *)
lemma proportion_existence:
  \<open>proportion S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists> t \<in> S. (\<forall> x \<in> S. \<exists> k. x = k *\<^sub>C t)\<close>
  using complex_vector.scale_zero_left ex_in_conv proportion_def
  by metis

(* functional *)
type_synonym 'a functional = \<open>'a \<Rightarrow> complex\<close>

lemma ker_ortho_nonzero:
  fixes f :: \<open>('a::chilbert_space) functional\<close> and x :: 'a
  assumes \<open>bounded_clinear f\<close> and \<open>x \<noteq> 0\<close> and \<open>x \<in> (orthogonal_complement (ker_op f))\<close> 
  shows \<open>f x \<noteq> 0\<close>
proof(rule classical)
  have \<open>is_subspace (ker_op f)\<close> using \<open>bounded_clinear f\<close>
    by (simp add: ker_op_lin) 
  assume \<open>\<not>(f x \<noteq> 0)\<close>
  hence \<open>x \<in> ker_op f\<close>
    by (simp add: ker_op_def) 
  moreover have \<open>(ker_op f)\<inter>(orthogonal_complement (ker_op f)) = {0}\<close>
    using \<open>is_subspace (ker_op f)\<close> is_linear_manifold.zero is_subspace.subspace ortho_inter_zero by auto
  ultimately have  \<open>x \<notin> orthogonal_complement (ker_op f)\<close> using \<open>x \<noteq> 0\<close>
    by (smt Int_iff empty_iff insert_iff) 
  thus ?thesis using \<open>x \<in> orthogonal_complement (ker_op f)\<close> by blast
qed

(* TODO: local in Riesz_Frechet_representation_existence *)
lemma ker_unidim:
  fixes f :: \<open>('a::chilbert_space) functional\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>proportion (orthogonal_complement (ker_op f))\<close>
proof-
  have \<open>x \<in> (orthogonal_complement (ker_op f)) \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<in> orthogonal_complement (ker_op f) \<Longrightarrow> y \<noteq> 0 
    \<Longrightarrow> \<exists> k. x = k *\<^sub>C y\<close>
    for x y
  proof-
    assume \<open>x \<in> (orthogonal_complement (ker_op f))\<close> and \<open>x \<noteq> 0\<close> and \<open>y \<in>(orthogonal_complement (ker_op f))\<close> and \<open>y \<noteq> 0\<close>
    from \<open>bounded_clinear f\<close> 
    have \<open>is_subspace (ker_op f)\<close>
      by (simp add: ker_op_lin)
    hence \<open>is_subspace (orthogonal_complement (ker_op f))\<close>
      by simp
    hence \<open>f x \<noteq> 0\<close>
      using ker_ortho_nonzero \<open>x \<in> (orthogonal_complement (ker_op f))\<close> \<open>x \<noteq> 0\<close> assms by auto 
    from \<open>is_subspace (orthogonal_complement (ker_op f))\<close>
    have \<open>f y \<noteq> 0\<close>
      using ker_ortho_nonzero \<open>y \<in> (orthogonal_complement (ker_op f))\<close> \<open>y \<noteq> 0\<close> assms by auto 
    from  \<open>f x \<noteq> 0\<close>  \<open>f y \<noteq> 0\<close>
    have \<open>\<exists> k. (f x) = k*(f y)\<close>
      by (metis add.inverse_inverse minus_divide_eq_eq)
    then obtain k where \<open>(f x) = k*(f y)\<close>
      by blast
    hence  \<open>(f x) = (f (k *\<^sub>C y))\<close>
      using  \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def
      by (simp add: clinear.scaleC)
    hence  \<open>(f x) - (f (k *\<^sub>C y)) = 0\<close>
      by simp
    hence  \<open>f (x - (k *\<^sub>C y)) = 0\<close>
      using  \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def
      by (simp add: additive.diff clinear.axioms(1))
    hence  \<open>(x - (k *\<^sub>C y)) \<in> ker_op f\<close>
      using ker_op_def
      by (simp add: ker_op_def)
    moreover have \<open>(ker_op f) \<inter> (orthogonal_complement (ker_op f)) = {0}\<close>
      by (simp add: \<open>is_subspace (ker_op f)\<close> is_linear_manifold.zero is_subspace.subspace ortho_inter_zero)
    moreover have \<open>(x - (k *\<^sub>C y)) \<in> orthogonal_complement (ker_op f)\<close>
    proof-
      from  \<open>y \<in> (orthogonal_complement (ker_op f))\<close>
      have  \<open>k *\<^sub>C y \<in> (orthogonal_complement (ker_op f))\<close>
        using \<open>is_subspace (orthogonal_complement (ker_op f))\<close>
        unfolding is_subspace_def
        by (simp add: is_linear_manifold.smult_closed)
      thus ?thesis using  \<open>x \<in> (orthogonal_complement (ker_op f))\<close>  \<open>is_subspace (orthogonal_complement (ker_op f))\<close>
        unfolding is_subspace_def
        by (metis \<open>is_subspace (ker_op f)\<close> add_diff_cancel_left' calculation(1) diff_add_cancel diff_zero is_linear_manifold.zero is_subspace.subspace proj_uniq)
    qed
    ultimately have \<open>x - (k *\<^sub>C y) = 0\<close>
      using \<open>f (x - k *\<^sub>C y) = 0\<close> \<open>x - k *\<^sub>C y \<in> orthogonal_complement (ker_op f)\<close> 
        assms ker_ortho_nonzero by blast
    thus ?thesis by simp
  qed 
  thus ?thesis
    by (simp add: proportion_def) 
qed

(* https://en.wikipedia.org/wiki/Riesz_representation_theorem *)
lemma Riesz_Frechet_representation_existence:
  fixes f::\<open>'a::chilbert_space functional\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>\<exists>t.  \<forall>x.  f x = \<langle>t, x\<rangle>\<close>
proof(cases \<open>\<forall> x. f x = 0\<close>)
  case True
  then show ?thesis
    by (metis cinner_zero_left) 
next
  case False
  then show ?thesis 
  proof-
    from \<open>bounded_clinear f\<close>
    have \<open>proportion (orthogonal_complement (ker_op f))\<close>
      by (simp add: ker_unidim)
    moreover have \<open>\<exists> h \<in> (orthogonal_complement (ker_op f)). h \<noteq> 0\<close>
      by (metis ExistenceUniquenessProj False assms diff_0_right ker_op_lin orthogonal_complement_twice projPropertiesA projPropertiesD proj_fixed_points proj_ker_simp)
    ultimately have \<open>\<exists> t. t \<noteq> 0 \<and> (\<forall> x \<in>(orthogonal_complement (ker_op f)). \<exists> k. x = k *\<^sub>C t)\<close>
      by (metis complex_vector.scale_zero_right equals0D proportion_existence) 
    then obtain t where \<open>t \<noteq> 0\<close> and \<open>\<forall> x \<in>(orthogonal_complement (ker_op f)). \<exists> k. x = k *\<^sub>C t\<close>
      by blast
    have  \<open>is_subspace ( orthogonal_complement (ker_op f))\<close>
      by (simp add: assms ker_op_lin)
    hence  \<open>t \<in> (orthogonal_complement (ker_op f))\<close>
    proof-
      have \<open>\<exists> s \<in> (orthogonal_complement (ker_op f)). s \<noteq> 0\<close>
        by (simp add: \<open>\<exists>h\<in>orthogonal_complement (ker_op f). h \<noteq> 0\<close>)
      then obtain s where \<open>s \<in> (orthogonal_complement (ker_op f))\<close> and \<open>s \<noteq> 0\<close>
        by blast
      have \<open>\<exists> k. s = k *\<^sub>C t\<close>
        by (simp add: \<open>\<forall>x\<in>orthogonal_complement (ker_op f). \<exists>k. x = k *\<^sub>C t\<close> \<open>s \<in> orthogonal_complement (ker_op f)\<close>)
      then obtain k where \<open>s = k *\<^sub>C t\<close>
        by blast
      have  \<open>k \<noteq> 0\<close>
        using \<open>s \<noteq> 0\<close>
        by (simp add: \<open>s = k *\<^sub>C t\<close>) 
      hence  \<open>(1/k) *\<^sub>C s = t\<close>
        using  \<open>s = k *\<^sub>C t\<close> by simp
      moreover have \<open>(1/k) *\<^sub>C s \<in>  (orthogonal_complement (ker_op f))\<close>
        using \<open>is_subspace  (orthogonal_complement (ker_op f))\<close>
        unfolding is_subspace_def
        by (simp add: \<open>s \<in> orthogonal_complement (ker_op f)\<close> is_linear_manifold.smult_closed)
      ultimately show ?thesis
        by simp 
    qed
    have \<open>proj (orthogonal_complement (ker_op f)) x = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
      for x
      using inner_product_proj \<open>is_subspace  (orthogonal_complement (ker_op f))\<close>
        \<open>\<forall> m \<in>  (orthogonal_complement (ker_op f)). \<exists> k. m = k *\<^sub>C t\<close>  \<open>t \<in> (orthogonal_complement (ker_op f))\<close>
      by (simp add: inner_product_proj \<open>t \<noteq> 0\<close>)
    hence \<open>f (proj (orthogonal_complement (ker_op f)) x) = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) * (f t)\<close>
      for x
      using \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def
      by (simp add: clinear.scaleC)
    hence \<open>f (proj (orthogonal_complement (ker_op f)) x) = \<langle>(((cnj (f t))/(\<langle>t , t\<rangle>)) *\<^sub>C t) , x\<rangle>\<close>
      for x
    proof-
      from \<open>f (proj (orthogonal_complement (ker_op f)) x) = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) * (f t)\<close>
      have \<open>f (proj (orthogonal_complement (ker_op f)) x) = ((f t)/(\<langle>t , t\<rangle>)) * (\<langle>t , x\<rangle>)\<close>
        by simp
      thus ?thesis
        by auto 
    qed
    moreover have \<open>f (proj ((ker_op f)) x) = 0\<close>
      for x
      using proj_ker_simp
      by (simp add: proj_ker_simp assms) 
    ultimately have \<open>f x = \<langle>(((cnj (f t))/(\<langle>t , t\<rangle>)) *\<^sub>C t) , x\<rangle>\<close>
      for x
      by (smt \<open>t \<in> orthogonal_complement (ker_op f)\<close> additive.add assms bounded_clinear_def cinner_simps(1) cinner_simps(5) cinner_simps(6) cinner_zero_left clinear.axioms(1) ker_op_lin ortho_decomp projPropertiesA projPropertiesD proj_fixed_points proj_ker_simp proj_ker_simp)
    thus ?thesis
      by blast  
  qed
qed

subsection \<open>Adjoin\<close>

definition \<open>Adj G = (SOME F. \<forall>x. \<forall>y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>)\<close>
  for G :: "'b::complex_inner \<Rightarrow> 'a::complex_inner"

lemma Adj_is_adjoint:
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::chilbert_space"
  assumes \<open>bounded_clinear G\<close>
  shows \<open>\<forall>x. \<forall>y. \<langle>Adj G x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
proof (unfold Adj_def, rule someI_ex[where P="\<lambda>F. \<forall>x. \<forall>y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>"])
  include notation_norm
  from assms have \<open>clinear G\<close>
    unfolding bounded_clinear_def by blast
  have  \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
    using  \<open>bounded_clinear G\<close>
    unfolding bounded_clinear_def
    by (simp add: bounded_clinear_axioms_def) 
  define g :: \<open>'a \<Rightarrow> ('b \<Rightarrow> complex)\<close> where
    \<open>g \<equiv> \<lambda> x. ( \<lambda> y. (\<langle>x , (G y)\<rangle>) )\<close>
  have \<open>bounded_clinear (g x)\<close>
    for x
  proof-
    have \<open>clinear (g x)\<close>
    proof-
      have \<open>(g x) (a + b) = (g x) a + (g x) b\<close>
        for a b
        unfolding  \<open>g \<equiv> \<lambda> x. ( \<lambda> y. (\<langle>x , (G y)\<rangle>) )\<close>
        using  \<open>clinear G\<close>
        by (simp add: additive.add cinner_right_distrib clinear_def)
      moreover have  \<open>(g x) (k *\<^sub>C a) = k *\<^sub>C ((g x) a)\<close>
        for a k
        unfolding g_def
        using  \<open>clinear G\<close>
        by (simp add: clinear.scaleC)
      ultimately show ?thesis
        by (simp add: clinearI) 
    qed
    moreover have \<open>\<exists> M. \<forall> y. \<parallel> (g x) y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
      using \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close> g_def
      by (simp add: \<open>bounded_clinear G\<close> bounded_clinear.bounded bounded_clinear_cinner_right_comp)
    ultimately show ?thesis unfolding bounded_linear_def
      using bounded_clinear.intro bounded_clinear_axioms_def by auto 
  qed
  hence  \<open>\<forall> x. \<exists> t::'b. ( \<forall> y :: 'b.  (g x) y = (\<langle>t , y\<rangle>) )\<close>
    using  Riesz_Frechet_representation_existence by blast
  hence  \<open>\<exists> F. \<forall> x. ( \<forall> y :: 'b.  (g x) y = (\<langle>(F x) , y\<rangle>) )\<close>
    by metis
  then obtain F where \<open>\<forall> x. ( \<forall> y :: 'b.  (g x) y = (\<langle>(F x) , y\<rangle>) )\<close>
    by blast
  thus "\<exists>x. \<forall>xa y. \<langle>x xa, y\<rangle> = \<langle>xa, G y\<rangle>" using  g_def
    by auto
qed

notation Adj ("_\<^sup>\<dagger>" [99] 100)

lemma AdjI: \<open>bounded_clinear G \<Longrightarrow> 
 \<langle>((G\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (G y)\<rangle> \<close>
  for G:: \<open>'b::chilbert_space \<Rightarrow> 'a::chilbert_space\<close>
proof-
  assume \<open>bounded_clinear G\<close> 
  moreover have \<open>\<forall> G:: 'b::chilbert_space \<Rightarrow> 'a::chilbert_space. 
 bounded_clinear G \<longrightarrow> ( 
   \<forall> x::'a. \<forall> y::'b. \<langle>((G\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (G y)\<rangle> )\<close>
    using Adj_is_adjoint 
    by (smt tfl_some)
  ultimately show ?thesis by blast  
qed


lemma AdjUniq:
  fixes G:: \<open>'b::chilbert_space \<Rightarrow> 'a::chilbert_space\<close>
    and F:: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close>
  assumes "bounded_clinear G"
  assumes F_is_adjoint: \<open>\<And>x y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
  shows \<open>F = G\<^sup>\<dagger>\<close>
proof-
  note F_is_adjoint
  moreover have \<open>\<forall> x::'a. \<forall> y::'b. \<langle>((G\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (G y)\<rangle>\<close>
    using  \<open>bounded_clinear G\<close> AdjI by blast
  ultimately have  \<open>\<forall> x::'a. \<forall> y::'b. 
    (\<langle>(F x) , y\<rangle> )-(\<langle>((G\<^sup>\<dagger>) x) , y\<rangle>) = 0\<close>
    by (simp add: \<open>\<forall>x y. \<langle> (G\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , G y \<rangle>\<close> F_is_adjoint)
  hence  \<open>\<forall> x::'a. \<forall> y::'b. 
    (\<langle>((F x) - ((G\<^sup>\<dagger>) x)) , y\<rangle> ) = 0\<close>
    by (simp add: cinner_diff_left)
  hence \<open>\<forall> x::'a. (F x) - ((G\<^sup>\<dagger>) x) = 0\<close>
    by (metis cinner_gt_zero_iff cinner_zero_left)
  hence \<open>\<forall> x::'a. (F - (G\<^sup>\<dagger>)) x = 0\<close>
    by simp
  hence \<open>\<forall> x::'a. F x = (G\<^sup>\<dagger>) x\<close>
    by (simp add: \<open>\<forall>x. F x - (G\<^sup>\<dagger>) x = 0\<close> eq_iff_diff_eq_0)
  thus ?thesis by auto
qed

lemma Adj_bounded_clinear:
  fixes A :: "'a::chilbert_space \<Rightarrow> 'b::chilbert_space"
  shows \<open>bounded_clinear A \<Longrightarrow> bounded_clinear (A\<^sup>\<dagger>)\<close>
proof-
  include notation_norm 
  assume \<open>bounded_clinear A\<close>
  have \<open>\<langle>((A\<^sup>\<dagger>) x), y\<rangle> = \<langle>x , (A y)\<rangle>\<close>
    for x y
    by (auto intro: AdjI \<open>bounded_clinear A\<close>)
  have \<open>Modules.additive (A\<^sup>\<dagger>)\<close>
  proof-
    have \<open>\<langle>((A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2)) , y\<rangle> = 0\<close>
      for x1 x2 y
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close> cinner_diff_left cinner_left_distrib)        
    hence \<open>(A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2) = 0\<close>
      for x1 x2
      using cinner_eq_zero_iff by blast
    thus ?thesis
      by (simp add: \<open>\<And>x2 x1. (A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2) = 0\<close> additive.intro eq_iff_diff_eq_0) 
  qed 
  moreover have \<open>(A\<^sup>\<dagger>) (r *\<^sub>C x) = r *\<^sub>C  (A\<^sup>\<dagger>) x\<close>
    for r x
  proof-
    have \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> = \<langle>(r *\<^sub>C x) , (A y)\<rangle>\<close>
      for y
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close>)
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> = (cnj r) * ( \<langle>x , (A y)\<rangle>)\<close>
      for y
      by simp
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> =  (\<langle>x , ((cnj r) *\<^sub>C A y)\<rangle>)\<close>
      for y
      by simp
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> =  (cnj r) * (\<langle>x , A y\<rangle>)\<close>
      for y
      by auto
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> =  (cnj r) * (\<langle>(A\<^sup>\<dagger>) x , y\<rangle>)\<close>
      for y
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close>)
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> =  (\<langle>r *\<^sub>C (A\<^sup>\<dagger>) x , y\<rangle>)\<close>
      for y
      by simp
    hence \<open>\<langle>(((A\<^sup>\<dagger>) (r *\<^sub>C x)) - (r *\<^sub>C (A\<^sup>\<dagger>) x )) , y\<rangle> = 0\<close>
      for y
      by (simp add: \<open>\<And>y. \<langle> (A\<^sup>\<dagger>) (r *\<^sub>C x) , y \<rangle> = \<langle> r *\<^sub>C (A\<^sup>\<dagger>) x , y \<rangle>\<close> cinner_diff_left)
    hence \<open>((A\<^sup>\<dagger>) (r *\<^sub>C x)) - (r *\<^sub>C (A\<^sup>\<dagger>) x ) = 0\<close>
      using cinner_eq_zero_iff by blast
    thus ?thesis
      by (simp add: \<open>(A\<^sup>\<dagger>) (r *\<^sub>C x) - r *\<^sub>C (A\<^sup>\<dagger>) x = 0\<close> eq_iff_diff_eq_0) 
  qed
  moreover have \<open>(\<exists>K. \<forall>x. \<parallel> (A\<^sup>\<dagger>) x\<parallel> \<le> \<parallel>x\<parallel> * K)\<close>
  proof-
    have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<langle>((A\<^sup>\<dagger>) x) , ((A\<^sup>\<dagger>) x)\<rangle>\<close>
      for x
      using power2_norm_eq_cinner' by auto
    moreover have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<ge> 0\<close>
      for x
      by simp
    ultimately have  \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<bar> \<langle>((A\<^sup>\<dagger>) x) , ((A\<^sup>\<dagger>) x)\<rangle> \<bar>\<close>
      for x
      by (simp add: abs_pos)
    hence \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<bar> \<langle>x , (A ((A\<^sup>\<dagger>) x))\<rangle> \<bar>\<close>
      for x
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close>)
    moreover have  \<open>\<bar>\<langle>x , (A ((A\<^sup>\<dagger>) x))\<rangle>\<bar> \<le> \<parallel>x\<parallel> *  \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close>
      for x
      by (simp add: complex_inner_class.norm_cauchy_schwarz)
    ultimately have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2  \<le> \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close>
      for x
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close> complex_inner_class.Cauchy_Schwarz_ineq2 power2_norm_eq_cinner)
    moreover have \<open>\<exists> M. M \<ge> 0 \<and> (\<forall> x.  \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le>  \<parallel>x\<parallel> * M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>)\<close>
    proof-
      have \<open>\<exists> M. M \<ge> 0 \<and> (\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>)\<close>
        using \<open>bounded_clinear A\<close>
        by (metis (mono_tags, hide_lams) bounded_clinear.bounded linear mult_nonneg_nonpos mult_zero_right norm_ge_zero order.trans semiring_normalization_rules(7)) 
      then obtain M where \<open>M \<ge> 0\<close> and \<open>\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
        by blast
      have \<open>\<forall> x. \<parallel>x\<parallel> \<ge> 0\<close>
        by simp
      hence \<open>\<forall> x.  \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le>  \<parallel>x\<parallel> * M * \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
        using  \<open>\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
        by (smt ordered_comm_semiring_class.comm_mult_left_mono vector_space_over_itself.scale_scale) 
      thus ?thesis using \<open>M \<ge> 0\<close> by blast
    qed
    ultimately have  \<open>\<exists> M. M \<ge> 0 \<and> (\<forall> x. \<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>)\<close>
      by (meson order.trans)
    then obtain M where \<open>M \<ge> 0\<close> and \<open>\<forall> x. \<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
      by blast
    have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel> \<le> \<parallel>x\<parallel> *  M\<close>
      for x
    proof(cases \<open> \<parallel>(A\<^sup>\<dagger>) x\<parallel> = 0\<close>)
      case True
      thus ?thesis
        by (simp add: \<open>0 \<le> M\<close>) 
    next
      case False
      have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
        using \<open>\<forall> x. \<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
        by simp
      thus ?thesis
        by (smt False mult_right_cancel mult_right_mono norm_ge_zero semiring_normalization_rules(29)) 
    qed
    thus ?thesis by blast
  qed
  ultimately show ?thesis
    unfolding bounded_clinear_def
    unfolding clinear_def
    by (simp add: bounded_clinear_axioms_def clinear_axioms.intro)
qed


subsection \<open>bounded operators\<close>

typedef (overloaded) ('a::complex_normed_vector, 'b::complex_normed_vector) bounded
  = \<open>{A::'a \<Rightarrow> 'b. bounded_clinear A}\<close>
  using bounded_clinear_zero by blast

setup_lifting type_definition_bounded

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "zero"
begin
lift_definition zero_bounded :: "('a,'b) bounded" is "Abs_bounded (\<lambda>x::'a. (0::'b))".
instance ..
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "uminus"
begin
lift_definition uminus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded"
  is "\<lambda> f. Abs_bounded (\<lambda> t::'a. - (Rep_bounded f) t)".
instance ..
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "semigroup_add"
begin
lift_definition plus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  \<open>\<lambda> f g. Abs_bounded (\<lambda> t. (Rep_bounded f) t + (Rep_bounded g) t)\<close>.
instance
proof      
  fix a b c :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer
  proof transfer 
    fix a b c::\<open>'a \<Rightarrow> 'b\<close>
    assume \<open>bounded_clinear a\<close>
      and \<open>bounded_clinear b\<close>
      and \<open>bounded_clinear c\<close>
    have  \<open>(\<lambda>t.  ( (\<lambda>t. a t + b t)) t + c t) 
          = (\<lambda>t. a t +  ( (\<lambda>t. b t + c t)) t)\<close>
      by (simp add: ordered_field_class.sign_simps(1))
    hence  \<open>(\<lambda>t.  ( (\<lambda>t. a t + b t)) t + c t) 
          = (\<lambda>t. a t + Rep_bounded (Abs_bounded (\<lambda>t. b t + c t)) t)\<close>
      by (simp add: Abs_bounded_inverse \<open>bounded_clinear b\<close> \<open>bounded_clinear c\<close> bounded_clinear_add)
    hence  \<open>(\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>t. a t + b t)) t + c t) 
          = (\<lambda>t. a t + Rep_bounded (Abs_bounded (\<lambda>t. b t + c t)) t)\<close>
      using Abs_bounded_inverse
      by (simp add: Abs_bounded_inverse \<open>bounded_clinear a\<close> \<open>bounded_clinear b\<close> bounded_clinear_add)
    thus \<open>Abs_bounded
        (\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>t. a t + b t)) t + c t) =
       Abs_bounded
        (\<lambda>t. a t + Rep_bounded (Abs_bounded (\<lambda>t. b t + c t)) t)\<close>
      by simp
  qed
qed
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "comm_monoid_add" begin
instance
proof
  fix a b :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded\<close>
  show \<open>a + b = b + a\<close>
    apply transfer
  proof transfer
    fix a b :: \<open>'a \<Rightarrow> 'b\<close>
    assume \<open>bounded_clinear a\<close> and \<open>bounded_clinear b\<close>
    have \<open> (\<lambda>t. a t + b t) =
            (\<lambda>t. b t + a t)\<close>
      by (simp add: ordered_field_class.sign_simps(2))
    thus \<open>Abs_bounded (\<lambda>t. a t + b t) =
           Abs_bounded (\<lambda>t. b t + a t)\<close> by simp
  qed

  fix a :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded\<close>
  show \<open>0 + a = a\<close>
  proof transfer
    have  \<open>\<And> a::('a::complex_normed_vector)\<Rightarrow>('b::complex_normed_vector). bounded_clinear a \<Longrightarrow> (Abs_bounded (\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>x. 0)) t + a t)) = Abs_bounded a\<close>
    proof-
      fix a :: \<open>('a::complex_normed_vector) \<Rightarrow> ('b::complex_normed_vector)\<close>
      assume \<open>bounded_clinear a\<close>
      have \<open>Rep_bounded (Abs_bounded (\<lambda>x. 0))  =  (\<lambda>x. 0)\<close>
        by (simp add: Abs_bounded_inverse)
      have \<open>(\<lambda> t. Rep_bounded (Abs_bounded (\<lambda>x. 0)) t + a t)  = (\<lambda> t. (\<lambda>x. 0) t + a t)\<close>
        by (simp add: \<open>Rep_bounded (Abs_bounded (\<lambda>x. 0)) = (\<lambda>x. 0)\<close>)
      moreover have  \<open>(\<lambda>x. 0) t + a t = a t\<close>
        for t
        by simp 
      ultimately have \<open>(\<lambda> t. Rep_bounded (Abs_bounded (\<lambda>x. 0)) t + a t)  = (\<lambda> t. a t)\<close>
        by auto
      hence \<open>(\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>x. 0)) t + a t) = a\<close>
        by simp
      thus \<open>(Abs_bounded
            (\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>x. 0)) t + a t)) = Abs_bounded a\<close> 
        by simp
    qed
    thus \<open>\<And>a:: ('a, 'b) bounded. Abs_bounded (\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>x. 0)) t + Rep_bounded a t) = a\<close> 
      by (metis Abs_bounded_cases Rep_bounded_cases Rep_bounded_inverse mem_Collect_eq)
  qed
qed
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "ab_group_add" begin
lift_definition minus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded"
  is \<open>\<lambda> f g. Abs_bounded (\<lambda>t. (Rep_bounded f) t - (Rep_bounded g) t)\<close>.

instance
proof
  fix a::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded\<close>
  show \<open>- a + a = 0\<close>
    apply transfer
  proof transfer
    fix a :: \<open>'a \<Rightarrow> 'b\<close>
    assume \<open>bounded_clinear a\<close>
    have \<open>(\<lambda>t.  ( (\<lambda>t. - a t)) t +  a t) = (\<lambda>x. 0)\<close>
      by simp 
    hence \<open>(\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>t. - a t)) t + a t) = (\<lambda>x. 0)\<close> 
      by (simp add: Abs_bounded_inverse \<open>bounded_clinear a\<close> bounded_clinear_minus)
    thus \<open>Abs_bounded
          (\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>t. - a t)) t + a t) = Abs_bounded (\<lambda>x. 0)\<close> 
      by simp
  qed

  fix a b::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded\<close>
  show \<open>a - b = a + - b\<close>
    apply transfer
  proof transfer
    fix a b :: \<open>'a \<Rightarrow> 'b\<close> 
    assume \<open>bounded_clinear a\<close> and \<open>bounded_clinear b\<close>
    have \<open>(\<lambda>t. a t - b t) = (\<lambda>t. a t +  (\<lambda>t. - b t) t)\<close>
      by simp
    hence \<open>(\<lambda>t. a t - b t) = (\<lambda>t. a t + Rep_bounded (Abs_bounded (\<lambda>t. - b t)) t)\<close>
      by (metis Abs_bounded_inverse \<open>bounded_clinear b\<close> bounded_clinear_minus mem_Collect_eq)      
    thus \<open>Abs_bounded (\<lambda>t. a t - b t) = Abs_bounded (\<lambda>t. a t + Rep_bounded (Abs_bounded (\<lambda>t. - b t)) t)\<close>
      by simp
  qed
qed
end

lemma PREscaleR_bounded:
  fixes c :: real
  assumes \<open>bounded_clinear f\<close>
  shows \<open>bounded_clinear (\<lambda> x. c *\<^sub>R f x )\<close>
proof-
  have  \<open>bounded_clinear (\<lambda> x. (complex_of_real c) *\<^sub>C f x )\<close>
    by (simp add: assms bounded_clinear_const_scaleC)
  thus ?thesis
    by (simp add: scaleR_scaleC) 
qed

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "complex_vector" begin
lift_definition scaleC_bounded :: "complex \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" 
  is \<open>\<lambda> r. \<lambda> f. Abs_bounded ( \<lambda> t::'a. r *\<^sub>C (Rep_bounded f) t )\<close>.

lift_definition scaleR_bounded :: "real \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" 
  is \<open>\<lambda> r. \<lambda> f. Abs_bounded ( \<lambda> t::'a. r *\<^sub>R (Rep_bounded f) t )\<close>.

instance
  apply intro_classes
proof
  fix r::real and x::\<open>('a, 'b) bounded\<close>
  show \<open>r *\<^sub>R x = complex_of_real r *\<^sub>C x\<close>
    apply transfer
    by (simp add: scaleR_scaleC) 

  fix a::complex and x y::\<open>('a, 'b) bounded\<close>
  show \<open>a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    apply transfer
  proof transfer
    fix a :: complex
    fix x y :: \<open>'a \<Rightarrow> 'b\<close>
    assume \<open>bounded_clinear x\<close> and \<open>bounded_clinear y\<close>
    have \<open>(\<lambda>t. a *\<^sub>C
              ( (\<lambda>t. x t + y t)) t) =
        (\<lambda>t.  ( (\<lambda>t. a *\<^sub>C x t)) t +
              ( (\<lambda>t. a *\<^sub>C y t)) t)\<close>
      by (simp add: scaleC_add_right)
    hence \<open>(\<lambda>t. a *\<^sub>C
             Rep_bounded (Abs_bounded (\<lambda>t. x t + y t)) t) =
        (\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>t. a *\<^sub>C x t)) t +
             Rep_bounded (Abs_bounded (\<lambda>t. a *\<^sub>C y t)) t)\<close>
      by (simp add: Abs_bounded_inverse \<open>bounded_clinear x\<close> \<open>bounded_clinear y\<close> bounded_clinear_add bounded_clinear_const_scaleC)
    thus \<open>Abs_bounded
        (\<lambda>t. a *\<^sub>C
             Rep_bounded (Abs_bounded (\<lambda>t. x t + y t)) t) =
       Abs_bounded
        (\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>t. a *\<^sub>C x t)) t +
             Rep_bounded (Abs_bounded (\<lambda>t. a *\<^sub>C y t)) t)\<close>
      by simp
  qed

  fix a b and x::\<open>('a, 'b) bounded\<close>
  show \<open>(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x\<close>
    apply transfer
  proof transfer
    fix a b :: complex
    fix x :: \<open>'a \<Rightarrow> 'b\<close>
    assume \<open>bounded_clinear x\<close>
    have \<open> (\<lambda>t. (a + b) *\<^sub>C x t) =
        (\<lambda>t.   (\<lambda>t. a *\<^sub>C x t) t +
               (\<lambda>t. b *\<^sub>C x t) t)\<close>
      by (simp add: scaleC_left.add)  
    hence \<open> (\<lambda>t. (a + b) *\<^sub>C x t) =
        (\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>t. a *\<^sub>C x t)) t +
             Rep_bounded (Abs_bounded (\<lambda>t. b *\<^sub>C x t)) t)\<close>
      using Abs_bounded_inverse
      by (simp add: Abs_bounded_inverse \<open>bounded_clinear x\<close> bounded_clinear_compose bounded_clinear_scaleC_right)
    thus \<open>Abs_bounded (\<lambda>t. (a + b) *\<^sub>C x t) =
       Abs_bounded
        (\<lambda>t. Rep_bounded (Abs_bounded (\<lambda>t. a *\<^sub>C x t)) t +
             Rep_bounded (Abs_bounded (\<lambda>t. b *\<^sub>C x t)) t)\<close>
      by simp
  qed

  fix a b::complex and x :: \<open>('a, 'b) bounded\<close>
  show \<open>a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x\<close>
    apply transfer 
  proof transfer
    fix a b :: complex
    fix x :: \<open>'a \<Rightarrow> 'b\<close>
    assume \<open>bounded_clinear x\<close>
    have \<open> (\<lambda>t. a *\<^sub>C ( (\<lambda>t. b *\<^sub>C x t)) t) =
        (\<lambda>t. (a * b) *\<^sub>C x t)\<close>
      by simp  
    hence \<open> (\<lambda>t. a *\<^sub>C Rep_bounded (Abs_bounded (\<lambda>t. b *\<^sub>C x t)) t) =
        (\<lambda>t. (a * b) *\<^sub>C x t)\<close>
      by (simp add: Abs_bounded_inverse \<open>bounded_clinear x\<close> bounded_clinear_compose bounded_clinear_scaleC_right)
    thus \<open>Abs_bounded  (\<lambda>t. a *\<^sub>C Rep_bounded (Abs_bounded (\<lambda>t. b *\<^sub>C x t)) t) =
       Abs_bounded (\<lambda>t. (a * b) *\<^sub>C x t)\<close>
      by simp
  qed

  fix x::\<open>('a, 'b) bounded\<close>
  show \<open>1 *\<^sub>C x = x\<close>
    apply transfer
    apply auto
    using Rep_bounded_inverse by auto    
qed
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "dist_norm" begin
lift_definition norm_bounded :: \<open>('a, 'b) bounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f. operator_norm (Rep_bounded f)\<close>.
lift_definition dist_bounded :: \<open>('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. operator_norm (Rep_bounded f - Rep_bounded g) \<close>.

instance
  apply intro_classes
  apply transfer
proof transfer
  fix x y :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>bounded_clinear x\<close> and \<open>bounded_clinear y\<close>
  have \<open>operator_norm (x - y) =
           operator_norm ( ( (\<lambda>t. x t - y t)))\<close>
    by (meson minus_apply) 
  thus \<open>operator_norm (x - y) =
           operator_norm (Rep_bounded (Abs_bounded (\<lambda>t. x t - y t)))\<close>
    using Abs_bounded_inverse
    by (simp add: Abs_bounded_inverse \<open>bounded_clinear x\<close> \<open>bounded_clinear y\<close> bounded_clinear_sub)
qed
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "sgn_div_norm" begin
lift_definition sgn_bounded :: \<open>('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded\<close>
  is \<open>\<lambda> f::('a, 'b) bounded. f /\<^sub>R norm f\<close>.

instance
  apply intro_classes
  by (metis (mono_tags, lifting) Bounded_Operators.sgn_bounded.transfer)
end


instantiation bounded :: (complex_normed_vector, complex_normed_vector) "uniformity_dist" begin
lift_definition uniformity_bounded :: \<open>(('a, 'b) bounded \<times> ('a, 'b) bounded) filter\<close>
  is \<open>(INF e:{0<..}. principal {((f::('a, 'b) bounded), g). dist f g < e})\<close> .

instance
  apply intro_classes
  by (simp add: uniformity_bounded.transfer)
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "open_uniformity" begin
lift_definition open_bounded :: \<open>(('a, 'b) bounded) set \<Rightarrow> bool\<close>
  is \<open>\<lambda> U::(('a, 'b) bounded) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)\<close>.
instance
  apply intro_classes
  apply auto
  apply (metis (mono_tags, lifting) open_bounded.transfer)
  by (smt case_prod_beta eventually_mono open_bounded.transfer)
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "complex_normed_vector" begin
instance
  apply intro_classes
  apply auto
proof transfer
  show \<open>\<And>x::('a, 'b) bounded. operator_norm (Rep_bounded x) = 0 \<Longrightarrow>
         x = Abs_bounded (\<lambda>x. 0)\<close>
  proof-
    fix x::\<open>('a, 'b) bounded\<close>
    assume \<open>operator_norm (Rep_bounded x) = 0\<close>
    hence \<open>Rep_bounded x = (\<lambda>x. 0)\<close>
      using operator_norm_zero
      by (simp add: operator_norm_zero)
    hence \<open>Abs_bounded (Rep_bounded x) = Abs_bounded (\<lambda>x. 0)\<close>
      by simp
    thus \<open>x = Abs_bounded (\<lambda>x. 0)\<close>
      by (simp add: Rep_bounded_inverse)      
  qed
next 
  show \<open>norm (0::('a,'b) bounded) = 0\<close>
    apply transfer
  proof-
    have \<open>Rep_bounded (Abs_bounded (\<lambda>x. 0)) = (\<lambda>x. 0)\<close>
      by (simp add: Abs_bounded_inverse)
    moreover have \<open>U = V \<Longrightarrow> operator_norm U = operator_norm V\<close>
      for U V:: \<open>'a \<Rightarrow> 'b\<close>
      by simp
    ultimately have \<open>operator_norm ( Rep_bounded (Abs_bounded (\<lambda>x::'a. 0::'b)) ) = operator_norm (\<lambda>x::'a. 0::'b)\<close>
      by blast
    thus \<open>operator_norm (Rep_bounded (Abs_bounded (\<lambda>x::'a. 0::'b))) = 0\<close>
      using operator_norm_of_zero
      by simp
  qed
next
  fix x y :: \<open>('a, 'b) bounded\<close>
  show \<open>norm (x + y) \<le> norm x + norm y\<close>
    apply transfer
  proof transfer
    fix x y :: \<open>'a \<Rightarrow> 'b\<close>
    assume \<open>bounded_clinear x\<close> and  \<open>bounded_clinear y\<close>
    have \<open>operator_norm (\<lambda>t. x t + y t)
           \<le> operator_norm x + operator_norm y\<close>
      using operator_norm_triangular by blast
    show \<open>operator_norm (Rep_bounded (Abs_bounded (\<lambda>t. x t + y t)))
           \<le> operator_norm x + operator_norm y\<close>
      using Abs_bounded_inverse
      by (simp add: Abs_bounded_inverse \<open>bounded_clinear x\<close> \<open>bounded_clinear y\<close> \<open>operator_norm (\<lambda>t. x t + y t) \<le> operator_norm x + operator_norm y\<close> bounded_clinear_add)
  qed
next
  fix a :: real  and x :: \<open>('a, 'b) bounded\<close>
  show \<open>norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x\<close>
    apply transfer
  proof transfer
    fix a :: real and x :: \<open>'a \<Rightarrow> 'b\<close>
    assume \<open>bounded_clinear x\<close>
    have \<open>operator_norm (\<lambda>t. a *\<^sub>R x t) = \<bar>a\<bar> * operator_norm x\<close>
      using operator_norm_prod_real by blast
    thus \<open>operator_norm
            (Rep_bounded (Abs_bounded (\<lambda>t. a *\<^sub>R x t))) =
           \<bar>a\<bar> * operator_norm x\<close>
      using Abs_bounded_inverse
    proof -
      show ?thesis
        by (simp add: Abs_bounded_inverse PREscaleR_bounded \<open>bounded_clinear x\<close> \<open>operator_norm (\<lambda>t. a *\<^sub>R x t) = \<bar>a\<bar> * operator_norm x\<close>)
    qed
  qed
next
  fix a :: complex  and x :: \<open>('a, 'b) bounded\<close>
  show \<open>norm (a *\<^sub>C x) = cmod a * norm x\<close>
    apply transfer
  proof transfer
    fix a :: complex and x :: \<open>'a \<Rightarrow> 'b\<close>
    assume \<open>bounded_clinear x\<close>
    have \<open>operator_norm (\<lambda>t. a *\<^sub>C x t) =  (cmod a) * operator_norm x\<close>
      using operator_norm_prod_complex 
      by (simp add: operator_norm_prod_complex)
    thus \<open>operator_norm
            (Rep_bounded (Abs_bounded (\<lambda>t. a *\<^sub>C x t))) =
           (cmod a) * operator_norm x\<close>
      using Abs_bounded_inverse
      by (simp add: Abs_bounded_inverse \<open>bounded_clinear x\<close> bounded_clinear_compose bounded_clinear_scaleC_right)
  qed
qed

end


(*
instantiation bounded :: (complex_normed_vector, chilbert_space) "cbanach" begin

lift_definition sign_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded"
  is \<open>\<lambda> f::('a,'b) bounded. 
    Abs_bounded (\<lambda> t::'a. ( (Rep_bounded f) t ) /\<^sub>R operator_norm (Rep_bounded f))\<close> .
lift_definition norm_bounded :: "('a,'b) bounded \<Rightarrow> real"
  is \<open>\<lambda> f::('a, 'b) bounded. operator_norm (Rep_bounded f)\<close> .
lift_definition dist_bounded :: "('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded \<Rightarrow> real"
  is \<open>\<lambda> f. \<lambda> g. operator_norm (Rep_bounded f - Rep_bounded g )\<close> .
lift_definition uniformity_bounded :: \<open>(('a, 'b) bounded \<times> ('a, 'b) bounded) filter\<close>
  is \<open>(INF e:{0<..}. principal {(f, g). operator_norm (Rep_bounded f - Rep_bounded g ) < e})\<close> .
lift_definition open_bounded :: "('a, 'b) bounded set \<Rightarrow> bool"
  is "\<lambda> U. (\<forall>f\<in>U. \<forall>\<^sub>F (f', g) in INF e:{0<..}. principal {(f, g). operator_norm (Rep_bounded f - Rep_bounded g ) < e}. f' = f \<longrightarrow> g \<in> U)" .

instance  
proof
  fix x y :: \<open>('a, 'b) bounded\<close>   
  show \<open>dist x y = norm (x - y)\<close>
    apply transfer
    

  qed

(* by (cheat bounded_cbanach) *)
end

*)

(* TODO: move to Legacy *)
type_synonym ('a,'b) l2bounded = "('a ell2, 'b ell2) bounded"
abbreviation "applyOp == Rep_bounded"
  (* typedef ('a,'b) l2bounded = "{A::'a ell2\<Rightarrow>'b ell2. bounded_clinear A}"
  morphisms applyOp Abs_l2bounded
  using bounded_clinear_zero by blast
setup_lifting type_definition_l2bounded *)

lift_definition idOp :: "('a::complex_normed_vector,'a) bounded" is id
  by (metis bounded_clinear_ident comp_id fun.map_ident)

(* instantiation l2bounded :: (type,type) zero begin
lift_definition zero_l2bounded :: "('a,'b) l2bounded" is "\<lambda>_. 0" by simp
instance ..
end *)

(* TODO define for bounded *)
lift_definition timesOp :: 
  "('b::complex_normed_vector,'c::complex_normed_vector) bounded
     \<Rightarrow> ('a::complex_normed_vector,'b) bounded \<Rightarrow> ('a,'c) bounded" 
  is "(o)"
  unfolding o_def 
  by (rule bounded_clinear_compose, simp_all)

(* TODO: rename bounded_clinearE' *)
lemma bound_op_characterization: 
  \<open>bounded_clinear f \<Longrightarrow> \<exists>K. \<forall>x. K \<ge> 0 \<and> norm (f x) \<le> norm x * K\<close>
  by (metis (mono_tags) bounded_clinear.bounded mult_zero_left  norm_eq_zero  norm_le_zero_iff order.trans ordered_field_class.sign_simps(24) zero_le_mult_iff)

lemma bounded_clinear_comp:
  \<open>bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_clinear (f \<circ> g)\<close>
proof-
  include notation_norm 
  assume \<open>bounded_clinear f\<close>
  assume \<open>bounded_clinear g\<close>
  have \<open>clinear (f \<circ> g)\<close>
  proof-
    have \<open>clinear f\<close>
      by (simp add: \<open>bounded_clinear f\<close> bounded_clinear.clinear)
    moreover have \<open>clinear g\<close>
      by (simp add: \<open>bounded_clinear g\<close> bounded_clinear.clinear)
    ultimately show ?thesis
    proof - (* automatically generated *)
      obtain cc :: "('c \<Rightarrow> 'b) \<Rightarrow> complex" and cca :: "('c \<Rightarrow> 'b) \<Rightarrow> 'c" where
        f1: "\<forall>x0. (\<exists>v1 v2. x0 (v1 *\<^sub>C v2) \<noteq> v1 *\<^sub>C x0 v2) = (x0 (cc x0 *\<^sub>C cca x0) \<noteq> cc x0 *\<^sub>C x0 (cca x0))"
        by moura
      obtain ccb :: "('c \<Rightarrow> 'b) \<Rightarrow> 'c" and ccc :: "('c \<Rightarrow> 'b) \<Rightarrow> 'c" where
        f2: "\<forall>x0. (\<exists>v1 v2. x0 (v1 + v2) \<noteq> x0 v1 + x0 v2) = (x0 (ccb x0 + ccc x0) \<noteq> x0 (ccb x0) + x0 (ccc x0))"
        by moura
      have "\<forall>c ca. g (c + ca) = g c + g ca"
        by (meson Modules.additive_def \<open>clinear g\<close> clinear.axioms(1))
      then have f3: "(f \<circ> g) (ccb (f \<circ> g) + ccc (f \<circ> g)) = (f \<circ> g) (ccb (f \<circ> g)) + (f \<circ> g) (ccc (f \<circ> g))"
        by (simp add: \<open>clinear f\<close> additive.add clinear.axioms(1))
      have "(f \<circ> g) (cc (f \<circ> g) *\<^sub>C cca (f \<circ> g)) = cc (f \<circ> g) *\<^sub>C (f \<circ> g) (cca (f \<circ> g))"
        by (simp add: \<open>clinear f\<close> \<open>clinear g\<close> clinear.scaleC)
      then show ?thesis
        using f3 f2 f1 by (meson clinearI)
    qed
  qed
  moreover have \<open>\<exists>K. \<forall>x. \<parallel>(f \<circ> g) x\<parallel> \<le> \<parallel>x\<parallel> * K\<close>
  proof-
    have \<open>\<exists> K\<^sub>f. \<forall>x. K\<^sub>f \<ge> 0 \<and> \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>f\<close>
      using \<open>bounded_clinear f\<close> bound_op_characterization 
      by blast
    then obtain K\<^sub>f where \<open> K\<^sub>f \<ge> 0\<close> and \<open>\<forall>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>f\<close>
      by metis
    have \<open>\<exists> K\<^sub>g. \<forall>x. \<parallel>g x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>g\<close>
      using \<open>bounded_clinear g\<close> bounded_clinear.bounded by blast 
    then obtain K\<^sub>g where \<open>\<forall>x. \<parallel>g x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>g\<close>
      by metis
    have \<open>\<parallel>(f \<circ> g) x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>g * K\<^sub>f\<close>
      for x
    proof-                             
      have \<open>\<parallel>(f \<circ> g) x\<parallel> \<le> \<parallel>f (g x)\<parallel>\<close>
        by simp
      also have \<open>... \<le> \<parallel>g x\<parallel> * K\<^sub>f\<close>
        by (simp add: \<open>\<forall>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>f\<close>)
      also have \<open>... \<le> (\<parallel>x\<parallel> * K\<^sub>g) * K\<^sub>f\<close>
        using \<open>K\<^sub>f \<ge> 0\<close>
        by (metis \<open>\<forall>x. \<parallel>g x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>g\<close> mult.commute ordered_comm_semiring_class.comm_mult_left_mono)
      finally show ?thesis
        by simp
    qed
    thus ?thesis 
      by (metis  comp_eq_dest_lhs linordered_field_class.sign_simps(23) )
  qed
  ultimately show ?thesis 
    using bounded_clinear_def bounded_clinear_axioms_def by blast
qed

lemma is_linear_manifold_image:
  assumes "clinear f" and "is_linear_manifold S"
  shows "is_linear_manifold (f ` S)"
  apply (rule is_linear_manifold.intro)
  subgoal proof - (* sledgehammer proof *)
    fix x :: 'b and y :: 'b
    assume a1: "x \<in> f ` S"
    assume a2: "y \<in> f ` S"
    obtain aa :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 = x1 v3) = (aa x0 x1 x2 \<in> x0 \<and> x2 = x1 (aa x0 x1 x2))"
      by moura
    then have f3: "\<forall>b f A. (b \<notin> f ` A \<or> aa A f b \<in> A \<and> b = f (aa A f b)) \<and> (b \<in> f ` A \<or> (\<forall>a. a \<notin> A \<or> b \<noteq> f a))"
      by blast
    then have "aa S f x + aa S f y \<in> S"
      using a2 a1 by (metis (no_types) assms(2) is_linear_manifold_def)
    then show "x + y \<in> f ` S"
      using f3 a2 a1 by (metis (no_types) additive.add assms(1) clinear.axioms(1))
  qed
  subgoal proof -
    fix x :: 'b and c :: complex
    assume a1: "x \<in> f ` S"
    obtain aa :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 = x1 v3) = (aa x0 x1 x2 \<in> x0 \<and> x2 = x1 (aa x0 x1 x2))"
      by moura
    then have f2: "aa S f x \<in> S \<and> x = f (aa S f x)"
      using a1 by (simp add: Bex_def_raw image_iff)
    then have "c *\<^sub>C x = f (c *\<^sub>C aa S f x)"
      by (metis (no_types) assms(1) clinear_axioms_def clinear_def)
    then show "c *\<^sub>C x \<in> f ` S"
      using f2 by (metis (no_types) assms(2) image_iff is_linear_manifold_def)
  qed
  by (metis Complex_Vector_Spaces.eq_vector_fraction_iff \<open>\<And>x c. x \<in> f ` S \<Longrightarrow> c *\<^sub>C x \<in> f ` S\<close> assms(2) imageI is_linear_manifold_def)

lemma PREapplyOpSpace:
  fixes f::\<open>('a::chilbert_space) \<Rightarrow> ('b::chilbert_space)\<close>
    and S::\<open>'a set\<close>
    (* assumes \<open>bounded_clinear f\<close> and \<open>is_subspace S\<close> *)
  assumes "clinear f" and "is_linear_manifold S"
  shows  \<open>is_subspace (closure {f x |x. x \<in> S})\<close> (* TODO: use f ` S *)
proof -
  have "is_linear_manifold {f x |x. x \<in> S}"
    using assms is_linear_manifold_image
    by (simp add: is_linear_manifold_image Setcompr_eq_image)
  then show \<open>is_subspace (closure {f x |x. x \<in> S})\<close>
    apply (rule_tac is_subspace.intro)
    using is_subspace_cl apply blast
    by blast
qed

(* 
proof-
  have \<open>bounded_clinear (proj S)\<close>
    using \<open>is_subspace S\<close> projPropertiesA by blast
  hence \<open>bounded_clinear (f \<circ> (proj S))\<close>
    using  \<open>bounded_clinear f\<close> bounded_clinear_comp by blast
  hence \<open>clinear (f \<circ> (proj S))\<close>
    unfolding bounded_clinear_def
    by blast
  hence \<open>is_linear_manifold (ran_op (f \<circ> (proj S)))\<close>
    using ran_op_lin
    by blast
  hence \<open>is_linear_manifold {x. \<exists> y. (f \<circ> (proj S)) y = x}\<close>
    unfolding ran_op_def by blast
  moreover have \<open>{f x |x. x \<in> S} = {x. \<exists> y. (f \<circ> (proj S)) y = x}\<close>
    by (metis assms(2) comp_apply proj_fixed_points proj_intro2)
  ultimately have  \<open>is_linear_manifold {f x |x. x \<in> S}\<close>
    by simp
  hence  \<open>is_linear_manifold (closure {f x |x. x \<in> S})\<close>
    by (simp add: is_subspace_cl)
  moreover have \<open>closed (closure {f x |x. x \<in> S})\<close>
    by auto
  ultimately show ?thesis
    using is_subspace_def by blast
qed
 *)

(* Note that without "closure", applyOpSpace would not in general return a subspace.
   See: https://math.stackexchange.com/questions/801806/is-the-image-of-a-closed-subspace-under-a-bounded-linear-operator-closed *)
(* TODO define for bounded *)
lift_definition applyOpSpace :: \<open>('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> 'a linear_space \<Rightarrow> 'b linear_space\<close> is
  "\<lambda>A S. closure {A x|x. x\<in>S}"
  using PREapplyOpSpace bounded_clinear_def is_subspace.subspace by blast

(* instantiation bounded :: (chilbert_space,chilbert_space) scaleC begin
lift_definition scaleC_l2bounded :: "complex \<Rightarrow> ('a,'b) l2bounded \<Rightarrow> ('a,'b) l2bounded" is
  "\<lambda>c A x. c *\<^sub>C A x"
  by (rule bounded_clinear_const_scaleC)
lift_definition scaleR_l2bounded :: "real \<Rightarrow> ('a,'b) l2bounded \<Rightarrow> ('a,'b) l2bounded" is
  "\<lambda>c A x. c *\<^sub>R A x"
  by (cheat scaleR_bounded)
instance
  apply standard unfolding scaleC_l2bounded_def scaleR_l2bounded_def
  by (simp add: scaleR_scaleC)
end *)

(* TODO: same for linear_space *)
instantiation linear_space :: (chilbert_space) scaleC begin
lift_definition scaleC_linear_space :: "complex \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is
  "\<lambda>c S. scaleC c ` S"
  apply (rule is_subspace.intro)
  using bounded_clinear_def bounded_clinear_scaleC_right is_linear_manifold_image is_subspace.subspace apply blast
  by (simp add: closed_scaleC is_subspace.closed)
lift_definition scaleR_linear_space :: "real \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is
  "\<lambda>c S. scaleR c ` S"
  apply (rule is_subspace.intro)
  apply (metis bounded_clinear_def bounded_clinear_scaleC_right is_linear_manifold_image is_subspace.subspace scaleR_scaleC)
  by (simp add: closed_scaling is_subspace.closed)
instance 
  apply standard
  by (simp add: scaleR_scaleC scaleC_linear_space_def scaleR_linear_space_def)
end

lift_definition
  adjoint :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> ('b,'a) bounded" ("_*" [99] 100) is Adj
  by (fact Adj_bounded_clinear)

lemma applyOp_0[simp]: "applyOpSpace U 0 = 0" 
  apply transfer
  by (simp add: additive.zero bounded_clinear_def clinear.axioms(1))

lemma times_applyOp: "applyOp (timesOp A B) \<psi> = applyOp A (applyOp B \<psi>)" 
  apply transfer by simp

lemma timesScalarSpace_0[simp]: "0 *\<^sub>C S = 0" for S :: "_ linear_space"
  apply transfer apply (auto intro!: exI[of _ 0])
  using  is_linear_manifold.zero is_subspace.subspace  by auto
    (* apply (metis (mono_tags, lifting) Collect_cong bounded_clinear_ident closure_eq is_subspace.closed ker_op_def ker_op_lin mem_Collect_eq) *)
    (*   using  is_linear_manifold.zero is_subspace.subspace
  by (metis (mono_tags, lifting) Collect_cong bounded_clinear_ident is_subspace_cl ker_op_def ker_op_lin) *)



(* TODO rename, e.g., subspace_scale_invariant *)
lemma PREtimesScalarSpace_not0: 
  fixes a S
  assumes \<open>a \<noteq> 0\<close> and \<open>is_subspace S\<close>
    (* TODO: is_linear_manifold instead? *)
  shows \<open>(*\<^sub>C) a ` S = S\<close>
proof-
  have  \<open>x \<in> (*\<^sub>C) a ` S \<Longrightarrow> x \<in> S\<close>
    for x
    using assms(2) is_linear_manifold.smult_closed is_subspace.subspace by fastforce
  moreover have  \<open>x \<in> S \<Longrightarrow> x \<in> (*\<^sub>C) a ` S\<close>
    for x
  proof - (* automatically generated *)
    assume "x \<in> S"
    then have "\<exists>c aa. (c / a) *\<^sub>C aa \<in> S \<and> c *\<^sub>C aa = x"
      using assms(2) is_linear_manifold_def is_subspace.subspace scaleC_one by blast
    then have "\<exists>aa. aa \<in> S \<and> a *\<^sub>C aa = x"
      using assms(1) by auto
    then show ?thesis
      by (meson image_iff)
  qed 
  ultimately show ?thesis by blast
qed

lemma timesScalarSpace_not0[simp]: "a \<noteq> 0 \<Longrightarrow> a *\<^sub>C S = S" for S :: "_ linear_space"
  apply transfer using PREtimesScalarSpace_not0 by blast

lemma one_times_op[simp]: "scaleC (1::complex) B = B" for B :: "(_,_) bounded"
  apply transfer by simp

lemma scalar_times_adj[simp]: "(scaleC a A)* = scaleC (cnj a) (A*)" for A::"(_,_)bounded"
  apply transfer by (cheat scalar_times_adj)

lemma timesOp_assoc: "timesOp (timesOp A B) C = timesOp A (timesOp B C)" 
  apply transfer by auto

lemma times_adjoint[simp]: "adjoint (timesOp A B) = timesOp (adjoint B) (adjoint A)" 
  by (cheat times_adjoint)

lemma PREtimesOp_assoc_linear_space:
  fixes A B S
  assumes \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close>
    and \<open>is_subspace S\<close>
  shows \<open>closure {(A \<circ> B) x |x. x \<in> S} =
       closure {A x |x. x \<in> closure {B x |x. x \<in> S}}\<close>
proof-
  have  \<open>closure {(A \<circ> B) x |x. x \<in> S} \<subseteq>
       closure {A x |x. x \<in> closure {B x |x. x \<in> S}}\<close>
    by (smt closure_mono closure_subset comp_apply mem_Collect_eq subset_iff)
  moreover have  \<open>closure {(A \<circ> B) x |x. x \<in> S} \<supseteq>
       closure {A x |x. x \<in> closure {B x |x. x \<in> S}}\<close>
  proof-
    have \<open>t \<in> {A x |x. x \<in> closure {B x |x. x \<in> S}}
        \<Longrightarrow> t \<in> closure {(A \<circ> B) x |x. x \<in> S}\<close>
      for t
    proof-
      assume \<open>t \<in> {A x |x. x \<in> closure {B x |x. x \<in> S}}\<close>
      then obtain u where 
        \<open>t = A u\<close> and \<open>u \<in> closure {B x |x. x \<in> S}\<close>
        by auto
      from  \<open>u \<in> closure {B x |x. x \<in> S}\<close> 
      obtain v where \<open>v \<longlonglongrightarrow> u\<close>
        and \<open>\<forall> n. v n \<in>  {B x |x. x \<in> S}\<close>
        using closure_sequential by blast
      from  \<open>\<forall> n. v n \<in>  {B x |x. x \<in> S}\<close>
      have \<open>\<forall> n. \<exists> x \<in> S.  v n = B x\<close>
        by auto
      then obtain w where \<open>w n \<in> S\<close> and \<open>v n = B (w n)\<close>
        for n
        by metis
      have \<open>(\<lambda> n. B (w n) ) \<longlonglongrightarrow> u\<close>
        using  \<open>\<And> n. v n = B (w n)\<close> \<open>v \<longlonglongrightarrow> u\<close>
        by presburger
      moreover have \<open>isCont A x\<close>
        for x
        using \<open>bounded_clinear A\<close>
        by (simp add: bounded_linear_continuous)
      ultimately have \<open>(\<lambda> n. A (B (w n)) ) \<longlonglongrightarrow> t\<close>
        using  \<open>t = A u\<close>
          isCont_tendsto_compose by blast
      hence  \<open>(\<lambda> n. (A \<circ> B) (w n) ) \<longlonglongrightarrow> t\<close>
        by simp                               
      thus ?thesis using \<open>\<And> n. w n \<in> S\<close>
        using closure_sequential by fastforce
    qed
    hence \<open> {A x |x. x \<in> closure {B x |x. x \<in> S}}
        \<subseteq> closure {(A \<circ> B) x |x. x \<in> S}\<close>
      by blast
    thus ?thesis
      by (metis (no_types, lifting) closure_closure closure_mono) 
  qed
  ultimately show ?thesis by blast
qed

lemma timesOp_assoc_linear_space: "applyOpSpace (timesOp A B) S = applyOpSpace A (applyOpSpace B S)" 
  apply transfer
  using PREtimesOp_assoc_linear_space by blast

(* instantiation bounded :: (chilbert_space,chilbert_space) ab_group_add begin
lift_definition plus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>a b x. a x + b x"
  by (rule bounded_clinear_add)
lift_definition minus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>a b x. a x - b x"
  by (rule bounded_clinear_sub)
lift_definition uminus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>a x. - a x"
  by (rule bounded_clinear_minus)
instance 
  apply intro_classes
  by (transfer; auto)+
end *)

(* TODO: where are these definitions needed? Should they be in qrhl-tool instead? *)
lemmas assoc_left = timesOp_assoc[symmetric] timesOp_assoc_linear_space[symmetric] add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded", symmetric]
lemmas assoc_right = timesOp_assoc timesOp_assoc_linear_space add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded"]

lemma scalar_times_op_add[simp]: "scaleC a (A+B) = scaleC a A + scaleC a B" for A B :: "(_,_) bounded"
  apply transfer
  by (simp add: scaleC_add_right) 
lemma scalar_times_op_minus[simp]: "scaleC a (A-B) = scaleC a A - scaleC a B" for A B :: "(_,_) bounded"
  apply transfer
  by (simp add: complex_vector.scale_right_diff_distrib)

lemma applyOp_bot[simp]: "applyOpSpace U bot = bot"
  by (simp add: linear_space_zero_bot[symmetric])

lemma equal_basis: "(\<And>x. applyOp A (ket x) = applyOp B (ket x)) \<Longrightarrow> A = B"
  by (cheat equal_basis)

lemma adjoint_twice[simp]: "(U*)* = U" for U :: "(_,_) bounded"
  by (cheat adjoint_twice)

(* TODO: move specialized syntax into QRHL-specific file *)
consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)
adhoc_overloading
  cdot timesOp applyOp applyOpSpace "scaleC :: _\<Rightarrow>(_,_)bounded\<Rightarrow>_" 

lemma cdot_plus_distrib[simp]: "U \<cdot> (A + B) = U \<cdot> A + U \<cdot> B"
  for A B :: "_ linear_space" and U :: "(_,_) bounded"
  apply transfer 
  by (cheat cdot_plus_distrib)


lemma scalar_op_linear_space_assoc [simp]: 
  "(\<alpha>\<cdot>A)\<cdot>S = \<alpha>\<cdot>(A\<cdot>S)" for \<alpha>::complex and A::"(_,_)bounded" and S::"_ linear_space"
proof transfer
  fix \<alpha> and A::"'a::chilbert_space \<Rightarrow> 'b::chilbert_space" and S
  have "(*\<^sub>C) \<alpha> ` closure {A x |x. x \<in> S} = closure {\<alpha> *\<^sub>C x |x. x \<in> {A x |x. x \<in> S}}" (is "?nested = _")
    by (simp add: closure_scaleC setcompr_eq_image)
  also have "\<dots> = closure {\<alpha> *\<^sub>C A x |x. x \<in> S}" (is "_ = ?nonnested")
    by (simp add: Setcompr_eq_image image_image)
  finally show "?nonnested = ?nested" by simp
qed

lemma apply_idOp[simp]: "applyOp idOp \<psi> = \<psi>"
  by (simp add: idOp.rep_eq)

lemma scalar_mult_0_op[simp]: "(0::complex) \<cdot> A = 0" for A::"(_,_) bounded"
  apply transfer by auto

lemma scalar_op_op[simp]: "(a \<cdot> A) \<cdot> B = a \<cdot> (A \<cdot> B)"
  for a :: complex and A :: "(_,_) bounded" and B :: "(_,_) bounded"
  apply transfer by auto

lemma op_scalar_op[simp]: "timesOp A (a \<cdot> B) = a \<cdot> (timesOp A B)" 
  for a :: complex and A :: "(_,_) bounded" and B :: "(_,_) bounded"
  apply transfer
  by (simp add: bounded_clinear.clinear clinear.scaleC o_def)

lemma scalar_scalar_op[simp]: "a \<cdot> (b \<cdot> A) = (a*b) \<cdot> A"
  for a b :: complex and A  :: "(_,_) bounded"
  apply transfer by auto

lemma scalar_op_vec[simp]: "(a \<cdot> A) \<cdot> \<psi> = a *\<^sub>C (A \<cdot> \<psi>)" 
  for a :: complex and A :: "(_,_) bounded" and \<psi> :: "'a ell2"
  apply transfer by auto


lemma add_scalar_mult: "a\<noteq>0 \<Longrightarrow> a \<cdot> A = a \<cdot> B \<Longrightarrow> A=B" for A B :: "('a,'b)l2bounded" and a::complex 
  by (rule scaleC_left_imp_eq)

lemma apply_idOp_space[simp]: "applyOpSpace idOp S = S"
  apply transfer by (simp add: is_subspace.closed)

lemma apply_0[simp]: "applyOp U 0 = 0"
  apply transfer 
  using additive.zero bounded_clinear.clinear clinear.axioms(1) by blast

lemma times_idOp1[simp]: "U \<cdot> idOp = U"
  apply transfer by auto

lemma times_idOp2[simp]: "timesOp idOp V = V" for V :: "(_,_) bounded"
  apply transfer by auto

lemma idOp_adjoint[simp]: "idOp* = idOp"
  by (cheat idOp_adjoint)

lemma mult_INF[simp]: "U \<cdot> (INF x. V x) = (INF x. U \<cdot> V x)" 
  for V :: "'a \<Rightarrow> 'b::chilbert_space linear_space" and U :: "('b,'c::chilbert_space) bounded"
  apply transfer apply auto
  by (cheat mult_INF)

lemma mult_inf_distrib[simp]: "U \<cdot> (B \<sqinter> C) = (U \<cdot> B) \<sqinter> (U \<cdot> C)" 
  for U :: "(_,_) bounded" and B C :: "_ linear_space"
  using mult_INF[where V="\<lambda>x. if x then B else C" and U=U]
  unfolding INF_UNIV_bool_expand
  by simp

definition "inj_option \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"
definition "inv_option \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (Hilbert_Choice.inv \<pi> (Some y)) else None)"
lemma inj_option_Some_pi[simp]: "inj_option (Some o \<pi>) = inj \<pi>"
  unfolding inj_option_def inj_def by simp

lemma inj_option_Some[simp]: "inj_option Some"
  using[[show_consts,show_types,show_sorts]]
  apply (rewrite asm_rl[of "(Some::'a\<Rightarrow>_) = Some o id"]) apply simp
  unfolding inj_option_Some_pi by simp

lemma inv_option_Some: "surj \<pi> \<Longrightarrow> inv_option (Some o \<pi>) = Some o (Hilbert_Choice.inv \<pi>)"
  unfolding inv_option_def o_def inv_def apply (rule ext) by auto
lemma inj_option_map_comp[simp]: "inj_option f \<Longrightarrow> inj_option g \<Longrightarrow> inj_option (f \<circ>\<^sub>m g)"
  unfolding inj_option_def apply auto
  by (smt map_comp_Some_iff)

lemma inj_option_inv_option[simp]: "inj_option (inv_option \<pi>)"
proof (unfold inj_option_def, rule allI, rule allI, rule impI, erule conjE)
  fix x y
  assume same: "inv_option \<pi> x = inv_option \<pi> y"
    and pix_not_None: "inv_option \<pi> x \<noteq> None"
  have x_pi: "Some x \<in> range \<pi>" 
    using pix_not_None unfolding inv_option_def apply auto
    by (meson option.distinct(1))
  have y_pi: "Some y \<in> range \<pi>" 
    using pix_not_None unfolding same unfolding inv_option_def apply auto
    by (meson option.distinct(1))
  have "inv_option \<pi> x = Some (Hilbert_Choice.inv \<pi> (Some x))"
    unfolding inv_option_def using x_pi by simp
  moreover have "inv_option \<pi> y = Some (Hilbert_Choice.inv \<pi> (Some y))"
    unfolding inv_option_def using y_pi by simp
  ultimately have "Hilbert_Choice.inv \<pi> (Some x) = Hilbert_Choice.inv \<pi> (Some y)"
    using same by simp
  then show "x = y"
    by (meson inv_into_injective option.inject x_pi y_pi)
qed

consts classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> ('a ell2,'b ell2) bounded"
lemma classical_operator_basis: "inj_option \<pi> \<Longrightarrow>
    applyOp (classical_operator \<pi>) (ket x) = (case \<pi> x of Some y \<Rightarrow> ket y | None \<Rightarrow> 0)"
  by (cheat TODO5)
lemma classical_operator_adjoint[simp]: 
  "inj_option \<pi> \<Longrightarrow> adjoint (classical_operator \<pi>) = classical_operator (inv_option \<pi>)"
  for \<pi> :: "'a \<Rightarrow> 'b option"
  by (cheat TODO1)

lemma classical_operator_mult[simp]:
  "inj_option \<pi> \<Longrightarrow> inj_option \<rho> \<Longrightarrow> classical_operator \<pi> \<cdot> classical_operator \<rho> = classical_operator (map_comp \<pi> \<rho>)"
  apply (rule equal_basis)
  unfolding times_applyOp
  apply (subst classical_operator_basis, simp)+
  apply (case_tac "\<rho> x")
  apply auto
  apply (subst classical_operator_basis, simp)
  by auto

lemma classical_operator_Some[simp]: "classical_operator Some = idOp"
  apply (rule equal_basis) apply (subst classical_operator_basis) apply simp by auto

definition "unitary U = (U \<cdot> (U*) = idOp \<and> U* \<cdot> U = idOp)"  
definition "isometry U = (U* \<cdot> U = idOp)"  

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* \<cdot> U = idOp" unfolding isometry_def by simp
lemma UadjU[simp]: "unitary U \<Longrightarrow> U \<cdot> U* = idOp" unfolding unitary_def by simp

lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"(_,_)bounded"
  unfolding unitary_def by auto

lemma unitary_times[simp]: "unitary A \<Longrightarrow> unitary B \<Longrightarrow> unitary (A\<cdot>B)"
  unfolding unitary_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma isometry_times[simp]: "isometry A \<Longrightarrow> isometry B \<Longrightarrow> isometry (A\<cdot>B)"
  unfolding isometry_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma isometry_classical_operator[simp]:
  assumes "inj \<pi>"
  shows "isometry (classical_operator (Some o \<pi>))"
proof -
  have comp: "inv_option (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>) = Some" 
    apply (rule ext) unfolding inv_option_def o_def 
    using assms unfolding inj_def inv_def by auto

  show ?thesis
    unfolding isometry_def
    apply (subst classical_operator_adjoint) using assms apply simp
    apply (subst classical_operator_mult) using assms apply auto[2]
    apply (subst comp)
    by simp
qed

lemma unitary_classical_operator[simp]:
  assumes "bij \<pi>"
  shows "unitary (classical_operator (Some o \<pi>))"
proof (unfold unitary_def, rule conjI)
  have "isometry (classical_operator (Some o \<pi>))"
    by (simp add: assms bij_is_inj)
  then show "classical_operator (Some \<circ> \<pi>)* \<cdot> classical_operator (Some \<circ> \<pi>) = idOp"
    unfolding isometry_def by simp
next
  have "inj \<pi>"
    by (simp add: assms bij_is_inj)
  have comp: "Some \<circ> \<pi> \<circ>\<^sub>m inv_option (Some \<circ> \<pi>) = Some"
    apply (rule ext)
    unfolding inv_option_def o_def map_comp_def
    unfolding inv_def apply auto
    apply (metis \<open>inj \<pi>\<close> inv_def inv_f_f)
    by (metis assms bij_def image_iff range_eqI)

  show "classical_operator (Some \<circ> \<pi>) \<cdot> classical_operator (Some \<circ> \<pi>)* = idOp"
    by (simp add: comp \<open>inj \<pi>\<close>)
qed

lemma unitary_image[simp]: "unitary U \<Longrightarrow> applyOpSpace U top = top"
  by (cheat TODO1)

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def by simp

(* TODO: Replace by existing class CARD_1 *)
class singleton = fixes the_single :: "'a" assumes everything_the_single: "x=the_single" begin
lemma singleton_UNIV: "UNIV = {the_single}"
  using everything_the_single by auto
lemma everything_the_same: "(x::'a)=y"
  apply (subst everything_the_single, subst (2) everything_the_single) by simp
lemma singleton_ext: "x (a::'a) = y b \<Longrightarrow> x = y"
  apply (rule ext) 
  apply (subst (asm) everything_the_same[where x=a])
  apply (subst (asm) everything_the_same[where x=b])
  by simp
lemma CARD_singleton[simp]: "CARD('a) = 1"
  by (simp add: singleton_UNIV)
subclass finite apply standard unfolding singleton_UNIV by simp  
end

instantiation unit :: singleton begin
definition "singleton = ()"
instance apply standard by auto
end

(* TODO move to L2_Complex *)
lift_definition C1_to_complex :: "'a::singleton ell2 \<Rightarrow> complex" is
  "\<lambda>\<psi>. \<psi> the_single" .
lift_definition complex_to_C1 :: "complex \<Rightarrow> 'a::singleton ell2" is
  "\<lambda>c _. c" 
  by simp

lemma C1_to_complex_inverse[simp]: "complex_to_C1 (C1_to_complex \<psi>) = \<psi>"
  apply transfer apply (rule singleton_ext) by auto

lemma complex_to_C1_inverse[simp]: "C1_to_complex (complex_to_C1 \<psi>) = \<psi>"
  apply transfer by simp

lemma bounded_clinear_complex_to_C1: "bounded_clinear complex_to_C1"
  apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def)+

lemma bounded_clinear_C1_to_complex: "bounded_clinear C1_to_complex"
  apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def singleton_UNIV)+

lift_definition ell2_to_bounded :: "'a::chilbert_space \<Rightarrow> (unit ell2,'a) bounded" is
  "\<lambda>(\<psi>::'a) (x::unit ell2). C1_to_complex x *\<^sub>C \<psi>"
  by (simp add: bounded_clinear_C1_to_complex bounded_clinear_scaleC_const)

lemma ell2_to_bounded_applyOp: "ell2_to_bounded (A\<cdot>\<psi>) = A \<cdot> ell2_to_bounded \<psi>" for A :: "(_,_)bounded"
  apply transfer
  by (simp add: bounded_clinear_def clinear.scaleC o_def)

lemma ell2_to_bounded_scalar_times: "ell2_to_bounded (a *\<^sub>C \<psi>) = a \<cdot> ell2_to_bounded \<psi>" for a::complex
  apply (rewrite at "a *\<^sub>C \<psi>" DEADID.rel_mono_strong[of _ "(a\<cdot>idOp) \<cdot> \<psi>"])
  apply transfer apply simp
  apply (subst ell2_to_bounded_applyOp)
  by simp

lift_definition kernel :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> 'a linear_space" is ker_op
  by (metis ker_op_lin)

definition eigenspace :: "complex \<Rightarrow> ('a::chilbert_space,'a) bounded \<Rightarrow> 'a linear_space" where
  "eigenspace a A = kernel (A-a\<cdot>idOp)" 

lemma kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a\<cdot>A) = kernel A"
  for a :: complex and A :: "(_,_) bounded"
  apply transfer
  by (smt Collect_cong complex_vector.scale_eq_0_iff ker_op_def)

lemma kernel_0[simp]: "kernel 0 = top"
  apply transfer unfolding ker_op_def by simp

lemma kernel_id[simp]: "kernel idOp = 0"
  apply transfer unfolding ker_op_def by simp

lemma [simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a\<cdot>A) = eigenspace (b/a) A"
  unfolding eigenspace_def
  apply (rewrite at "kernel \<hole>" DEADID.rel_mono_strong[where y="a \<cdot> (A - b / a \<cdot> idOp)"])
  apply auto[1]
  by (subst kernel_scalar_times, auto)

section \<open>Projectors\<close>

(* TODO: link with definition from Complex_Inner (needs definition of adjoint, first) *)
definition "isProjector P = (P=P* \<and> P=P\<cdot>P)"

consts Proj :: "'a linear_space \<Rightarrow> ('a,'a) bounded"
lemma isProjector_Proj[simp]: "isProjector (Proj S)"
  by (cheat TODO5)

lemma imageOp_Proj[simp]: "applyOpSpace (Proj S) top = S"
  by (cheat TODO5)

lemma Proj_leq: "Proj S \<cdot> A \<le> S"
  by (metis imageOp_Proj inf.orderE inf.orderI mult_inf_distrib top_greatest)


lemma Proj_times: "A \<cdot> Proj S \<cdot> A* = Proj (A\<cdot>S)" for A::"(_,_)bounded"
  by (cheat TODO2)

abbreviation proj :: "'a::chilbert_space \<Rightarrow> ('a,'a) bounded" where "proj \<psi> \<equiv> Proj (span {\<psi>})"

lemma proj_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" for a::complex and \<psi>::"'a ell2"
  by (cheat TODO2)


lemma move_plus:
  "Proj (ortho C) \<cdot> A \<le> B \<Longrightarrow> A \<le> B + C"
  for A B C::"_ linear_space"
  by (cheat TODO2)


section \<open>Tensor products\<close>

consts "tensorOp" :: "('a,'b) l2bounded \<Rightarrow> ('c,'d) l2bounded \<Rightarrow> ('a*'c,'b*'d) l2bounded"
consts "tensorSpace" :: "'a ell2 linear_space \<Rightarrow> 'c ell2 linear_space \<Rightarrow> ('a*'c) ell2 linear_space"
consts "tensorVec" :: "'a ell2 \<Rightarrow> 'c ell2 \<Rightarrow> ('a*'c) ell2"
consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<otimes>" 71)
adhoc_overloading tensor tensorOp tensorSpace tensorVec

lemma idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"
  by (cheat TODO2)

consts "comm_op" :: "('a*'b, 'b*'a) l2bounded"

lemma adj_comm_op[simp]: "adjoint comm_op = comm_op"
  by (cheat TODO2)

lemma
  comm_op_swap[simp]: "comm_op \<cdot> (A\<otimes>B) \<cdot> comm_op = B\<otimes>A"
  for A::"('a,'b) l2bounded" and B::"('c,'d) l2bounded"
  by (cheat TODO3)

lemma comm_op_times_comm_op[simp]: "comm_op \<cdot> comm_op = idOp"
proof -
  find_theorems "idOp \<otimes> idOp"
  have "comm_op \<cdot> (idOp \<otimes> idOp) \<cdot> comm_op = idOp \<otimes> idOp" by (simp del: idOp_tensor_idOp)
  then show ?thesis by simp
qed

lemma unitary_comm_op[simp]: "unitary comm_op"
  unfolding unitary_def by simp

consts "assoc_op" :: "('a*'b*'c, ('a*'b)*'c) l2bounded"
lemma unitary_assoc_op[simp]: "unitary assoc_op"
  by (cheat TODO5)

lemma tensor_scalar_mult1[simp]: "(a \<cdot> A) \<otimes> B = a \<cdot> (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)
lemma tensor_scalar_mult2[simp]: "A \<otimes> (a \<cdot> B) = a \<cdot> (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)

lemma tensor_times[simp]: "(U1 \<otimes> U2) \<cdot> (V1 \<otimes> V2) = (U1 \<cdot> V1) \<otimes> (U2 \<cdot> V2)"
  for V1 :: "('a1,'b1) l2bounded" and U1 :: "('b1,'c1) l2bounded"
    and V2 :: "('a2,'b2) l2bounded" and U2 :: "('b2,'c2) l2bounded"
  by (cheat TODO3)

consts remove_qvar_unit_op :: "('a*unit,'a) l2bounded"


definition addState :: "'a ell2 \<Rightarrow> ('b,'b*'a) l2bounded" where
  "addState \<psi> = idOp \<otimes> (ell2_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*"

lemma addState_times_scalar[simp]: "addState (a *\<^sub>C \<psi>) = a \<cdot> addState \<psi>" for a::complex and psi::"'a ell2"
  unfolding addState_def by (simp add: ell2_to_bounded_scalar_times)

lemma tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)"
  for U :: "('a,'b) l2bounded" and V :: "('c,'d) l2bounded"
  by (cheat TODO3)

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

subsection \<open>Dual\<close>

(* The interpretation of Riesz representation theorem as an anti-isomorphism
between a Hilbert space and its dual of a Hilbert space is the justification of 
the brac-ket notation *)

(* TODO: the things related to topological_real_vector should be in earlier theory *)

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>continuous_on\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>)\<close>

class topological_real_vector = real_vector + topological_ab_group_add +
  assumes scaleR_continuous: "continuous_on UNIV (case_prod scaleR)"

class topological_complex_vector = complex_vector + topological_ab_group_add +
  assumes scaleC_continuous: "continuous_on UNIV (case_prod scaleC)"

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>continuous_on\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> ('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> bool\<close>)\<close>

thm tendsto_scaleR
  (* This overwrites Limits.tendsto_scaleR by a stronger fact *)
lemma tendsto_scaleR[tendsto_intros]:
  fixes b :: "'a::topological_real_vector"
  assumes "(f \<longlongrightarrow> a) F" and "(g \<longlongrightarrow> b) F"
  shows "((\<lambda>x. f x *\<^sub>R g x) \<longlongrightarrow> a *\<^sub>R b) F"
proof -
  have "(((\<lambda>x. case_prod scaleR (f x, g x))) \<longlongrightarrow> case_prod scaleR (a, b)) F"
    apply (rule tendsto_compose[where g="case_prod scaleR"])
    using continuous_on_def scaleR_continuous apply blast
    by (simp add: assms(1) assms(2) tendsto_Pair)
  then show ?thesis
    by (simp add: case_prod_beta o_def)
qed

(* This overwrites Limits.tendsto_scaleR by a stronger fact *)
lemma tendsto_scaleC[tendsto_intros]:
  fixes b :: "'a::topological_complex_vector"
  assumes "(f \<longlongrightarrow> a) F" and "(g \<longlongrightarrow> b) F"
  shows "((\<lambda>x. f x *\<^sub>C g x) \<longlongrightarrow> a *\<^sub>C b) F"
proof -
  have "(((\<lambda>x. case_prod scaleC (f x, g x))) \<longlongrightarrow> case_prod scaleC (a, b)) F"
    apply (rule tendsto_compose[where g="case_prod scaleC"])
    using continuous_on_def scaleC_continuous apply blast
    by (simp add: assms(1) assms(2) tendsto_Pair)
  then show ?thesis
    by (simp add: case_prod_beta o_def)
qed

(* lemma continuous_on_scaleC[continuous_intros]:
  fixes g :: "_\<Rightarrow>'a::topological_complex_vector"
  assumes "continuous_on s f" and "continuous_on s g"
  shows "continuous_on s (\<lambda>x. f x *\<^sub>C g x)" 
  using assms unfolding continuous_on_def by (auto intro!: tendsto_intros) *)

instance topological_complex_vector \<subseteq> topological_real_vector
  apply standard
  apply (rewrite at "case_prod scaleR" DEADID.rel_mono_strong[of _ "\<lambda>x. (complex_of_real (fst x)) *\<^sub>C (snd x)"])
  apply (auto simp: scaleR_scaleC case_prod_beta)[1]
  unfolding continuous_on_def
  apply (auto intro!: tendsto_intros)
  using tendsto_fst tendsto_snd by fastforce+

instance real_normed_vector \<subseteq> topological_real_vector
proof standard 
  have "(\<lambda>(x, y). x *\<^sub>R y) \<midarrow>(a, b)\<rightarrow> a *\<^sub>R b" for a and b :: 'a
    unfolding case_prod_beta apply (rule Limits.tendsto_scaleR)
    using tendsto_fst tendsto_snd by fastforce+
  then show "continuous_on UNIV (\<lambda>(x, y::'a). x *\<^sub>R y)"
    unfolding continuous_on_def by simp
qed

instance complex_normed_vector \<subseteq> topological_complex_vector
proof standard 
  note tendsto_scaleC = bounded_bilinear.tendsto[OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]
  have "(\<lambda>(x, y). x *\<^sub>C y) \<midarrow>(a, b)\<rightarrow> a *\<^sub>C b" for a and b :: 'a
    unfolding case_prod_beta apply (rule tendsto_scaleC)
    using tendsto_fst tendsto_snd by fastforce+
  then show "continuous_on UNIV (\<lambda>(x, y::'a). x *\<^sub>C y)"
    unfolding continuous_on_def by simp
qed

lemma clinear_0[simp]: "clinear (\<lambda>f. 0)"
  unfolding clinear_def Modules.additive_def clinear_axioms_def by simp

typedef (overloaded) 'a dual = \<open>{f::'a::topological_complex_vector\<Rightarrow>complex. continuous_on UNIV f \<and> clinear f}\<close>
  apply (rule exI[where x="\<lambda>f. 0"]) by auto

instantiation dual :: (complex_normed_vector) chilbert_space begin
instance 
  by (cheat "dual :: (complex_normed_vector) chilbert_space")
end

subsection \<open>Dimension\<close>


lift_definition finite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> is
  \<open>\<lambda>S. \<exists>G. finite G \<and> complex_vector.span G = S\<close> .

(* lift_definition infinite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> is
\<open>\<lambda>S. (
\<exists> f::nat \<Rightarrow> 'a set.
(\<forall>n. is_subspace (f n)) \<and>
(\<forall> n. f n \<subset> f (Suc n)) \<and>
(\<forall> n. f n \<subseteq> S)
)\<close> *)


(* (* TODO: define on sets first and lift? *)
(* TODO: I would define only finite_dim and just negate it for infinite_dim (avoid too many definitions) *)
definition infinite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> where
\<open>infinite_dim S = (
\<exists> f::nat \<Rightarrow> 'a linear_space.
(\<forall> n::nat. Rep_linear_space (f n) \<subset> Rep_linear_space (f (Suc n))) \<and>
(\<forall> n::nat. Rep_linear_space (f n) \<subseteq> Rep_linear_space S)
)\<close> *)

(* definition finite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> where
\<open>finite_dim S = ( \<not> (infinite_dim S) )\<close> *)


subsection \<open>Tensor product\<close>

(* TODO: define Tensor later as "('a dual, 'b) hilbert_schmidt" *)

(* (* Tensor product *)
typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) tensor
(* TODO: is that compatible (isomorphic) with tensorVec? *)
= \<open>{ A :: ('a dual, 'b) bounded. finite_dim (Abs_linear_space ((Rep_bounded A) ` UNIV)) }\<close>
   *)

(* TODO: universal property of tensor products *)

(* Embedding of (x,y) into the tensor product as x\<otimes>y *)
(* TODO: Shouldn't this be called "tensor" or similar then? *)
(* definition HS_embedding :: \<open>('a::chilbert_space)*('b::chilbert_space) \<Rightarrow> ('a, 'b) tensor\<close> where
\<open>HS_embedding x = Abs_tensor ( Abs_bounded (\<lambda> w::'a dual. ( (Rep_bounded w) (fst x) ) *\<^sub>C (snd x) ) )\<close> *)

(* The tensor product of two Hilbert spaces is a Hilbert space *)
(* instantiation tensor :: (chilbert_space,chilbert_space) "chilbert_space" begin
instance 
end *)



end

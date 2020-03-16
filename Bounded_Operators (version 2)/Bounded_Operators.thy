(*  Title:      Bounded_Operators.thy
    Author:     Dominique Unruh (University of Tartu)
    Author:     Jose Manuel Rodriguez Caballero (University of Tartu)
*)

section \<open>Bounded Complex-Linear Function\<close>

theory Bounded_Operators

imports
  Complex_Vector_Spaces
  "HOL-Analysis.Bounded_Linear_Function"

begin

lemma c_onorm_componentwise:
  assumes "bounded_clinear f"
  shows "onorm f \<le> (\<Sum>i\<in>Basis. norm (f i))"
  by (simp add: assms bounded_clinear_is_bounded_linear onorm_componentwise)

(* Ask to Dominique 
lemmas onorm_componentwise_le = order_trans[OF onorm_componentwise]
*)
subsection\<^marker>\<open>tag unimportant\<close> \<open>Intro rules for \<^term>\<open>bounded_clinear\<close>\<close>

named_theorems bounded_clinear_intros

lemma c_onorm_inner_left:
  assumes "bounded_clinear r"
  shows "onorm (\<lambda>x. r x \<bullet> f) \<le> onorm r * norm f"
  by (simp add: assms bounded_clinear_is_bounded_linear onorm_inner_left)


lemma c_onorm_inner_right:
  assumes "bounded_clinear r"
  shows "onorm (\<lambda>x. f \<bullet> r x) \<le> norm f * onorm r"
  by (simp add: assms bounded_clinear_is_bounded_linear onorm_inner_right)

(* Ask to Dominique
lemmas [bounded_clinear_intros] =
  bounded_clinear_zero
  bounded_clinear_add
  bounded_clinear_const_mult
  bounded_clinear_mult_const
  bounded_clinear_scaleR_const
  bounded_clinear_const_scaleR
  bounded_clinear_ident
  bounded_clinear_sum
  bounded_clinear_Pair
  bounded_clinear_sub
  bounded_clinear_fst_comp
  bounded_clinear_snd_comp
  bounded_clinear_inner_left_comp
  bounded_clinear_inner_right_comp
*)

subsection\<^marker>\<open>tag unimportant\<close> \<open>declaration of derivative/continuous/tendsto introduction rules 
  for bounded complex-linear functions\<close>

(* Ask to Dominique
attribute_setup bounded_clinear =
  \<open>Scan.succeed (Thm.declaration_attribute (fn thm =>
    fold (fn (r, s) => Named_Theorems.add_thm s (thm RS r))
      [
        (@{thm bounded_clinear.has_derivative}, \<^named_theorems>\<open>derivative_intros\<close>),
        (@{thm bounded_clinear.tendsto}, \<^named_theorems>\<open>tendsto_intros\<close>),
        (@{thm bounded_clinear.continuous}, \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_clinear.continuous_on}, \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_clinear.uniformly_continuous_on}, \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_clinear_compose}, \<^named_theorems>\<open>bounded_clinear_intros\<close>)
      ]))\<close>
*) 

(* Ask to Dominique
attribute_setup bounded_sesquilinear =
  \<open>Scan.succeed (Thm.declaration_attribute (fn thm =>
    fold (fn (r, s) => Named_Theorems.add_thm s (thm RS r))
      [
        (@{thm bounded_bilinear.FDERIV}, \<^named_theorems>\<open>derivative_intros\<close>),
        (@{thm bounded_bilinear.tendsto}, \<^named_theorems>\<open>tendsto_intros\<close>),
        (@{thm bounded_bilinear.continuous}, \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_bilinear.continuous_on}, \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_clinear_compose[OF bounded_sesquilinear.bounded_clinear_left]},
          \<^named_theorems>\<open>bounded_clinear_intros\<close>),
        (@{thm bounded_clinear_compose[OF bounded_bilinear.bounded_clinear_right]},
          \<^named_theorems>\<open>bounded_clinear_intros\<close>),
        (@{thm bounded_clinear.uniformly_continuous_on[OF bounded_bilinear.bounded_clinear_left]},
          \<^named_theorems>\<open>continuous_intros\<close>),
        (@{thm bounded_clinear.uniformly_continuous_on[OF bounded_bilinear.bounded_clinear_right]},
          \<^named_theorems>\<open>continuous_intros\<close>)
      ]))\<close>
*)

subsection \<open>Type of bounded linear functions\<close>

typedef\<^marker>\<open>tag important\<close> (overloaded) ('a, 'b) bounded ("(_ \<Rightarrow>\<^sub>B /_)" [22, 21] 21) =
  "{f::'a::complex_normed_vector\<Rightarrow>'b::complex_normed_vector. bounded_clinear f}"
  morphisms bounded_apply Bounded
  using bounded_clinear_zero by blast
  
(*
declare [[coercion
    "bounded_apply :: ('a::complex_normed_vector \<Rightarrow>\<^sub>B'b::complex_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'b"]]
*)

lemma bounded_clinear_bounded_apply[bounded_clinear_intros]:
  "bounded_clinear g \<Longrightarrow> bounded_clinear (\<lambda>x. bounded_apply f (g x))"
  using bounded_apply bounded_clinear_compose by auto

setup_lifting type_definition_bounded

lemma bounded_eqI: "(\<And>i. bounded_apply x i = bounded_apply y i) \<Longrightarrow> x = y"
  by transfer auto

lemma bounded_clinear_Bounded_apply: "bounded_clinear f \<Longrightarrow> bounded_apply (Bounded f) = f"
  by (auto simp: Bounded_inverse)


subsection \<open>Type class instantiations\<close>

instantiation bounded :: (complex_normed_vector, complex_normed_vector) complex_normed_vector
begin

lift_definition\<^marker>\<open>tag important\<close> norm_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> real" is onorm .

lift_definition minus_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  is "\<lambda>f g x. f x - g x"
  by (rule bounded_clinear_sub)

definition dist_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> real"
  where "dist_bounded a b = norm (a - b)"

definition [code del]:
  "(uniformity :: (('a \<Rightarrow>\<^sub>B 'b) \<times> ('a \<Rightarrow>\<^sub>B 'b)) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_bounded :: "('a \<Rightarrow>\<^sub>B 'b) set \<Rightarrow> bool"
  where [code del]: "open_bounded S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"

lift_definition uminus_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b" is "\<lambda>f x. - f x"
  by (rule bounded_clinear_minus)

lift_definition\<^marker>\<open>tag important\<close> zero_bounded :: "'a \<Rightarrow>\<^sub>B 'b" is "\<lambda>x. 0"
  by (rule bounded_clinear_zero)

lift_definition\<^marker>\<open>tag important\<close> plus_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  is "\<lambda>f g x. f x + g x"
  by (simp add: bounded_clinear_add)

lift_definition\<^marker>\<open>tag important\<close> scaleR_bounded::"real \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b" is "\<lambda>r f x. r *\<^sub>R f x"
  by (simp add: scalarR_bounded_clinear)

lift_definition\<^marker>\<open>tag important\<close> scaleC_bounded::"complex \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b" is "\<lambda>r f x. r *\<^sub>C f x"
  by (simp add: bounded_clinear_compose bounded_clinear_scaleR_right)

definition sgn_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  where "sgn_bounded x = scaleC (inverse (norm x)) x"

instance
  proof
  show "a + b + c = a + (b + c)"
    for a :: "'a \<Rightarrow>\<^sub>B 'b"
      and b :: "'a \<Rightarrow>\<^sub>B 'b"
      and c :: "'a \<Rightarrow>\<^sub>B 'b"
        apply transfer by auto

  show "a + b = b + a"
    for a :: "'a \<Rightarrow>\<^sub>B 'b"
      and b :: "'a \<Rightarrow>\<^sub>B 'b"
        apply transfer by auto

  show "(0::'a \<Rightarrow>\<^sub>B 'b) + a = a"
    for a :: "'a \<Rightarrow>\<^sub>B 'b"
        apply transfer by auto

  show "- a + a = 0"
    for a :: "'a \<Rightarrow>\<^sub>B 'b"
        apply transfer by auto

  show "a - b = a + - b"
    for a :: "'a \<Rightarrow>\<^sub>B 'b"
      and b :: "'a \<Rightarrow>\<^sub>B 'b"
        apply transfer by auto

  show "a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
      and y :: "'a \<Rightarrow>\<^sub>B 'b"
        apply transfer
    by (simp add: pth_6) 

  show "(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
        apply transfer
    by (simp add: scaleR_left.add) 

  show "a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by simp

  show "1 *\<^sub>R x = x"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer by simp
  show "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
      and y :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: scaleC_add_right) 
  show "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: scaleC_left.add) 
  show "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by simp 
  show "1 *\<^sub>C x = x"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer by auto
  show scaleR_scaleC1: "((*\<^sub>R) r::'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
  proof-
    have \<open>r *\<^sub>R f = (complex_of_real r) *\<^sub>C f\<close> for f::\<open>'a \<Rightarrow>\<^sub>B 'b\<close>
      apply transfer
      by (simp add: scaleR_scaleC)
    thus ?thesis by blast
  qed
  show "dist x y = norm (x - y)"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
      and y :: "'a \<Rightarrow>\<^sub>B 'b"
    by (simp add: dist_bounded_def)   
  show "sgn x = inverse (norm x) *\<^sub>R x"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
    using scaleR_scaleC1
    by (simp add: sgn_bounded_def)    
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a \<Rightarrow>\<^sub>B 'b) y < e})"
    by (simp add: uniformity_bounded_def)
    
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a \<Rightarrow>\<^sub>B 'b) = x \<longrightarrow> y \<in> U)"
    for U :: "('a \<Rightarrow>\<^sub>B 'b) set"
    by (simp add: Bounded_Operators.open_bounded_def)
    
  show "(norm x = 0) = (x = 0)"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
  proof
    show "x = 0"
      if "norm x = 0"
      using that apply transfer
      by (metis (no_types) bounded_clinear_is_bounded_linear less_numeral_extra(3) onorm_pos_lt)
    show "norm x = 0"
      if "x = 0"
      using that apply transfer
      by (simp add: onorm_eq_0) 
  qed
  show "norm (x + y) \<le> norm x + norm y"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
      and y :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: bounded_clinear_is_bounded_linear onorm_triangle)
  show "norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x"
    for a :: real
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: bounded_clinear_is_bounded_linear onorm_scaleR) 
  show "norm (a *\<^sub>C x) = norm a * norm x"
    for a :: complex
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: onorm_scalarC)
qed
end

declare uniformity_Abort[where 'a="('a :: complex_normed_vector) \<Rightarrow>\<^sub>B ('b :: complex_normed_vector)", code]

lemma c_norm_bounded_eqI:
  assumes "n \<le> norm (bounded_apply f x) / norm x"
  assumes "\<And>x. norm (bounded_apply f x) \<le> n * norm x"
  assumes "0 \<le> n"
  shows "norm f = n"
  using assms apply transfer
  using antisym onorm_bound assms order_trans[OF _ le_onorm]
  by (simp add: \<open>\<And>xa x f. \<lbrakk>xa \<le> norm (f x) / norm x; bounded_linear f\<rbrakk> \<Longrightarrow> xa \<le> onorm f\<close> antisym onorm_bound bounded_clinear_is_bounded_linear)
    

lemma c_norm_bounded: "norm (bounded_apply f x) \<le> norm f * norm x"
  apply transfer
  by (simp add: bounded_clinear_is_bounded_linear onorm) 

lemma c_norm_bounded_bound: "0 \<le> b \<Longrightarrow> (\<And>x. norm (bounded_apply f x) \<le> b * norm x) \<Longrightarrow> norm f \<le> b"
  by transfer (rule onorm_bound)

(* Ask to Dominique
declare bounded.zero_left [simp] bounded.zero_right [simp]
*)

context bounded_sesquilinear
begin

named_theorems sesquilinear_simps

lemmas [bilinear_simps] =
  add_left
  add_right
  diff_left
  diff_right
  minus_left
  minus_right
  scaleR_left
  scaleR_right
  zero_left
  zero_right
  sum_left
  sum_right

end


instance bounded :: (complex_normed_vector, cbanach) cbanach
  proof
  show "convergent X"
    if "Cauchy X"
    for X :: "nat \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
    using that apply transfer sorry
qed
subsection\<^marker>\<open>tag unimportant\<close> \<open>On Euclidean Space\<close>

lemma Zfun_sum:
  assumes "finite s"
  assumes f: "\<And>i. i \<in> s \<Longrightarrow> Zfun (f i) F"
  shows "Zfun (\<lambda>x. sum (\<lambda>i. f i x) s) F"
  using assms by induct (auto intro!: Zfun_zero Zfun_add)

lemma norm_bounded_euclidean_le:
  fixes a::"'a::euclidean_space \<Rightarrow>\<^sub>B 'b::complex_normed_vector"
  shows "norm a \<le> sum (\<lambda>x. norm (a x)) Basis"
  apply (rule norm_bounded_bound)
   apply (simp add: sum_nonneg)
  apply (subst euclidean_representation[symmetric, where 'a='a])
  apply (simp only: bounded.bilinear_simps sum_distrib_right)
  apply (rule order.trans[OF norm_sum sum_mono])
  apply (simp add: abs_mult mult_right_mono ac_simps Basis_le_norm)
  done

lemma tendsto_componentwise1:
  fixes a::"'a::euclidean_space \<Rightarrow>\<^sub>B 'b::complex_normed_vector"
    and b::"'c \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  assumes "(\<And>j. j \<in> Basis \<Longrightarrow> ((\<lambda>n. b n j) \<longlongrightarrow> a j) F)"
  shows "(b \<longlongrightarrow> a) F"
proof -
  have "\<And>j. j \<in> Basis \<Longrightarrow> Zfun (\<lambda>x. norm (b x j - a j)) F"
    using assms unfolding tendsto_Zfun_iff Zfun_norm_iff .
  hence "Zfun (\<lambda>x. \<Sum>j\<in>Basis. norm (b x j - a j)) F"
    by (auto intro!: Zfun_sum)
  thus ?thesis
    unfolding tendsto_Zfun_iff
    by (rule Zfun_le)
      (auto intro!: order_trans[OF norm_bounded_euclidean_le] simp: bounded.bilinear_simps)
qed

lift_definition
  bounded_of_matrix::"('b::euclidean_space \<Rightarrow> 'a::euclidean_space \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  is "\<lambda>a x. \<Sum>i\<in>Basis. \<Sum>j\<in>Basis. ((x \<bullet> j) * a i j) *\<^sub>R i"
  by (intro bounded_clinear_intros)

lemma bounded_of_matrix_works:
  fixes f::"'a::euclidean_space \<Rightarrow>\<^sub>B 'b::euclidean_space"
  shows "bounded_of_matrix (\<lambda>i j. (f j) \<bullet> i) = f"
proof (transfer, rule,  rule euclidean_eqI)
  fix f::"'a \<Rightarrow> 'b" and x::'a and b::'b assume "bounded_clinear f" and b: "b \<in> Basis"
  then interpret bounded_clinear f by simp
  have "(\<Sum>j\<in>Basis. \<Sum>i\<in>Basis. (x \<bullet> i * (f i \<bullet> j)) *\<^sub>R j) \<bullet> b
    = (\<Sum>j\<in>Basis. if j = b then (\<Sum>i\<in>Basis. (x \<bullet> i * (f i \<bullet> j))) else 0)"
    using b
    by (simp add: inner_sum_left inner_Basis if_distrib cong: if_cong) (simp add: sum.swap)
  also have "\<dots> = (\<Sum>i\<in>Basis. (x \<bullet> i * (f i \<bullet> b)))"
    using b by (simp add: sum.delta)
  also have "\<dots> = f x \<bullet> b"
    by (metis (mono_tags, lifting) Linear_Algebra.linear_componentwise linear_axioms)
  finally show "(\<Sum>j\<in>Basis. \<Sum>i\<in>Basis. (x \<bullet> i * (f i \<bullet> j)) *\<^sub>R j) \<bullet> b = f x \<bullet> b" .
qed

lemma bounded_of_matrix_apply:
  "bounded_of_matrix a x = (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. ((x \<bullet> j) * a i j) *\<^sub>R i)"
  by transfer simp

lemma bounded_of_matrix_minus: "bounded_of_matrix x - bounded_of_matrix y = bounded_of_matrix (x - y)"
  by transfer (auto simp: algebra_simps sum_subtractf)

lemma norm_bounded_of_matrix:
  "norm (bounded_of_matrix a) \<le> (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. \<bar>a i j\<bar>)"
  apply (rule norm_bounded_bound)
   apply (simp add: sum_nonneg)
  apply (simp only: bounded_of_matrix_apply sum_distrib_right)
  apply (rule order_trans[OF norm_sum sum_mono])
  apply (rule order_trans[OF norm_sum sum_mono])
  apply (simp add: abs_mult mult_right_mono ac_simps Basis_le_norm)
  done

lemma tendsto_bounded_of_matrix:
  assumes "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> ((\<lambda>n. b n i j) \<longlongrightarrow> a i j) F"
  shows "((\<lambda>n. bounded_of_matrix (b n)) \<longlongrightarrow> bounded_of_matrix a) F"
proof -
  have "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> Zfun (\<lambda>x. norm (b x i j - a i j)) F"
    using assms unfolding tendsto_Zfun_iff Zfun_norm_iff .
  hence "Zfun (\<lambda>x. (\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. \<bar>b x i j - a i j\<bar>)) F"
    by (auto intro!: Zfun_sum)
  thus ?thesis
    unfolding tendsto_Zfun_iff bounded_of_matrix_minus
    by (rule Zfun_le) (auto intro!: order_trans[OF norm_bounded_of_matrix])
qed

lemma tendsto_componentwise:
  fixes a::"'a::euclidean_space \<Rightarrow>\<^sub>B 'b::euclidean_space"
    and b::"'c \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  shows "(\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> ((\<lambda>n. b n j \<bullet> i) \<longlongrightarrow> a j \<bullet> i) F) \<Longrightarrow> (b \<longlongrightarrow> a) F"
  apply (subst bounded_of_matrix_works[of a, symmetric])
  apply (subst bounded_of_matrix_works[of "b x" for x, symmetric, abs_def])
  by (rule tendsto_bounded_of_matrix)

lemma
  continuous_bounded_componentwiseI:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::euclidean_space \<Rightarrow>\<^sub>B 'c::euclidean_space"
  assumes "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> continuous F (\<lambda>x. (f x) j \<bullet> i)"
  shows "continuous F f"
  using assms by (auto simp: continuous_def intro!: tendsto_componentwise)

lemma
  continuous_bounded_componentwiseI1:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::euclidean_space \<Rightarrow>\<^sub>B 'c::complex_normed_vector"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> continuous F (\<lambda>x. f x i)"
  shows "continuous F f"
  using assms by (auto simp: continuous_def intro!: tendsto_componentwise1)

lemma
  continuous_on_bounded_componentwise:
  fixes f:: "'d::t2_space \<Rightarrow> 'e::euclidean_space \<Rightarrow>\<^sub>B 'f::complex_normed_vector"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> continuous_on s (\<lambda>x. f x i)"
  shows "continuous_on s f"
  using assms
  by (auto intro!: continuous_at_imp_continuous_on intro!: tendsto_componentwise1
    simp: continuous_on_eq_continuous_within continuous_def)

lemma bounded_clinear_bounded_matrix: "bounded_clinear (\<lambda>x. (x::_\<Rightarrow>\<^sub>B _) j \<bullet> i)"
  by (auto intro!: bounded_clinearI' bounded_clinear_intros)

lemma continuous_bounded_matrix:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>B 'c::real_inner"
  assumes "continuous F f"
  shows "continuous F (\<lambda>x. (f x) j \<bullet> i)"
  by (rule bounded_clinear.continuous[OF bounded_clinear_bounded_matrix assms])

lemma continuous_on_bounded_matrix:
  fixes f::"'a::t2_space \<Rightarrow> 'b::complex_normed_vector \<Rightarrow>\<^sub>B 'c::real_inner"
  assumes "continuous_on S f"
  shows "continuous_on S (\<lambda>x. (f x) j \<bullet> i)"
  using assms
  by (auto simp: continuous_on_eq_continuous_within continuous_bounded_matrix)

lemma continuous_on_bounded_of_matrix[continuous_intros]:
  assumes "\<And>i j. i \<in> Basis \<Longrightarrow> j \<in> Basis \<Longrightarrow> continuous_on S (\<lambda>s. g s i j)"
  shows "continuous_on S (\<lambda>s. bounded_of_matrix (g s))"
  using assms
  by (auto simp: continuous_on intro!: tendsto_bounded_of_matrix)

lemma mult_if_delta:
  "(if P then (1::'a::comm_semiring_1) else 0) * q = (if P then q else 0)"
  by auto

lemma compact_bounded_lemma:
  fixes f :: "nat \<Rightarrow> 'a::euclidean_space \<Rightarrow>\<^sub>B 'b::euclidean_space"
  assumes "bounded (range f)"
  shows "\<forall>d\<subseteq>Basis. \<exists>l::'a \<Rightarrow>\<^sub>B 'b. \<exists> r::nat\<Rightarrow>nat.
    strict_mono r \<and> (\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>d. dist (f (r n) i) (l i) < e) sequentially)"
  by (rule compact_lemma_general[where unproj = "\<lambda>e. bounded_of_matrix (\<lambda>i j. e j \<bullet> i)"])
   (auto intro!: euclidean_eqI[where 'a='b] bounded_clinear_image assms
    simp: bounded_of_matrix_works bounded_of_matrix_apply inner_Basis mult_if_delta sum.delta'
      scaleR_sum_left[symmetric])

lemma bounded_euclidean_eqI: "(\<And>i. i \<in> Basis \<Longrightarrow> bounded_apply x i = bounded_apply y i) \<Longrightarrow> x = y"
  apply (auto intro!: bounded_eqI)
  apply (subst (2) euclidean_representation[symmetric, where 'a='a])
  apply (subst (1) euclidean_representation[symmetric, where 'a='a])
  apply (simp add: bounded.bilinear_simps)
  done

lemma Bounded_eq_matrix: "bounded_clinear f \<Longrightarrow> Bounded f = bounded_of_matrix (\<lambda>i j. f j \<bullet> i)"
  by (intro bounded_euclidean_eqI)
     (auto simp: bounded_of_matrix_apply bounded_clinear_Bounded_apply inner_Basis if_distrib
      if_distribR sum.delta' euclidean_representation
      cong: if_cong)

text \<open>TODO: generalize (via \<open>compact_cball\<close>)?\<close>
instance bounded :: (euclidean_space, euclidean_space) heine_borel
proof
  fix f :: "nat \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  assume f: "bounded (range f)"
  then obtain l::"'a \<Rightarrow>\<^sub>B 'b" and r where r: "strict_mono r"
    and l: "\<forall>e>0. eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) i) (l i) < e) sequentially"
    using compact_bounded_lemma [OF f] by blast
  {
    fix e::real
    let ?d = "real_of_nat DIM('a) * real_of_nat DIM('b)"
    assume "e > 0"
    hence "e / ?d > 0" by (simp)
    with l have "eventually (\<lambda>n. \<forall>i\<in>Basis. dist (f (r n) i) (l i) < e / ?d) sequentially"
      by simp
    moreover
    {
      fix n
      assume n: "\<forall>i\<in>Basis. dist (f (r n) i) (l i) < e / ?d"
      have "norm (f (r n) - l) = norm (bounded_of_matrix (\<lambda>i j. (f (r n) - l) j \<bullet> i))"
        unfolding bounded_of_matrix_works ..
      also note norm_bounded_of_matrix
      also have "(\<Sum>i\<in>Basis. \<Sum>j\<in>Basis. \<bar>(f (r n) - l) j \<bullet> i\<bar>) <
        (\<Sum>i\<in>(Basis::'b set). e / real_of_nat DIM('b))"
      proof (rule sum_strict_mono)
        fix i::'b assume i: "i \<in> Basis"
        have "(\<Sum>j::'a\<in>Basis. \<bar>(f (r n) - l) j \<bullet> i\<bar>) < (\<Sum>j::'a\<in>Basis. e / ?d)"
        proof (rule sum_strict_mono)
          fix j::'a assume j: "j \<in> Basis"
          have "\<bar>(f (r n) - l) j \<bullet> i\<bar> \<le> norm ((f (r n) - l) j)"
            by (simp add: Basis_le_norm i)
          also have "\<dots> < e / ?d"
            using n i j by (auto simp: dist_norm bounded.bilinear_simps)
          finally show "\<bar>(f (r n) - l) j \<bullet> i\<bar> < e / ?d" by simp
        qed simp_all
        also have "\<dots> \<le> e / real_of_nat DIM('b)"
          by simp
        finally show "(\<Sum>j\<in>Basis. \<bar>(f (r n) - l) j \<bullet> i\<bar>) < e / real_of_nat DIM('b)"
          by simp
      qed simp_all
      also have "\<dots> \<le> e" by simp
      finally have "dist (f (r n)) l < e"
        by (auto simp: dist_norm)
    }
    ultimately have "eventually (\<lambda>n. dist (f (r n)) l < e) sequentially"
      using eventually_elim2 by force
  }
  then have *: "((f \<circ> r) \<longlongrightarrow> l) sequentially"
    unfolding o_def tendsto_iff by simp
  with r show "\<exists>l r. strict_mono r \<and> ((f \<circ> r) \<longlongrightarrow> l) sequentially"
    by auto
qed


subsection\<^marker>\<open>tag unimportant\<close> \<open>concrete bounded linear functions\<close>

lemma transfer_bounded_bilinear_bounded_clinearI:
  assumes "g = (\<lambda>i x. (bounded_apply (f i) x))"
  shows "bounded_bilinear g = bounded_clinear f"
proof
  assume "bounded_bilinear g"
  then interpret bounded_bilinear f by (simp add: assms)
  show "bounded_clinear f"
  proof (unfold_locales, safe intro!: bounded_eqI)
    fix i
    show "f (x + y) i = (f x + f y) i" "f (r *\<^sub>R x) i = (r *\<^sub>R f x) i" for r x y
      by (auto intro!: bounded_eqI simp: bounded.bilinear_simps)
    from _ nonneg_bounded show "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
      by (rule ex_reg) (auto intro!: onorm_bound simp: norm_bounded.rep_eq ac_simps)
  qed
qed (auto simp: assms intro!: bounded.comp)

lemma transfer_bounded_bilinear_bounded_clinear[transfer_rule]:
  "(rel_fun (rel_fun (=) (pcr_bounded (=) (=))) (=)) bounded_bilinear bounded_clinear"
  by (auto simp: pcr_bounded_def cr_bounded_def rel_fun_def OO_def
    intro!: transfer_bounded_bilinear_bounded_clinearI)

context bounded_bilinear
begin

lift_definition prod_left::"'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'c" is "(\<lambda>b a. prod a b)"
  by (rule bounded_clinear_left)
declare prod_left.rep_eq[simp]

lemma bounded_clinear_prod_left[bounded_clinear]: "bounded_clinear prod_left"
  by transfer (rule flip)

lift_definition prod_right::"'a \<Rightarrow> 'b \<Rightarrow>\<^sub>B 'c" is "(\<lambda>a b. prod a b)"
  by (rule bounded_clinear_right)
declare prod_right.rep_eq[simp]

lemma bounded_clinear_prod_right[bounded_clinear]: "bounded_clinear prod_right"
  by transfer (rule bounded_bilinear_axioms)

end

lift_definition id_bounded::"'a::complex_normed_vector \<Rightarrow>\<^sub>B 'a" is "\<lambda>x. x"
  by (rule bounded_clinear_ident)

lemmas bounded_apply_id_bounded[simp] = id_bounded.rep_eq

lemma norm_bounded_id[simp]:
  "norm (id_bounded::'a::{complex_normed_vector, perfect_space} \<Rightarrow>\<^sub>B 'a) = 1"
  by transfer (auto simp: onorm_id)

lemma norm_bounded_id_le:
  "norm (id_bounded::'a::complex_normed_vector \<Rightarrow>\<^sub>B 'a) \<le> 1"
  by transfer (auto simp: onorm_id_le)


lift_definition fst_bounded::"('a::complex_normed_vector \<times> 'b::complex_normed_vector) \<Rightarrow>\<^sub>B 'a" is fst
  by (rule bounded_clinear_fst)

lemma bounded_apply_fst_bounded[simp]: "bounded_apply fst_bounded = fst"
  by transfer (rule refl)


lift_definition snd_bounded::"('a::complex_normed_vector \<times> 'b::complex_normed_vector) \<Rightarrow>\<^sub>B 'b" is snd
  by (rule bounded_clinear_snd)

lemma bounded_apply_snd_bounded[simp]: "bounded_apply snd_bounded = snd"
  by transfer (rule refl)


lift_definition bounded_compose::
  "'a::complex_normed_vector \<Rightarrow>\<^sub>B 'b::complex_normed_vector \<Rightarrow>
    'c::complex_normed_vector \<Rightarrow>\<^sub>B 'a \<Rightarrow>
    'c \<Rightarrow>\<^sub>B 'b" (infixl "o\<^sub>L" 55) is "(o)"
  parametric comp_transfer
  unfolding o_def
  by (rule bounded_clinear_compose)

lemma bounded_apply_bounded_compose[simp]: "(a o\<^sub>L b) c = a (b c)"
  by (simp add: bounded_compose.rep_eq)

lemma norm_bounded_compose:
  "norm (f o\<^sub>L g) \<le> norm f * norm g"
  by transfer (rule onorm_compose)

lemma bounded_bilinear_bounded_compose[bounded_bilinear]: "bounded_bilinear (o\<^sub>L)"
  by unfold_locales
    (auto intro!: bounded_eqI exI[where x=1] simp: bounded.bilinear_simps norm_bounded_compose)

lemma bounded_compose_zero[simp]:
  "bounded_compose 0 = (\<lambda>_. 0)"
  "bounded_compose x 0 = 0"
  by (auto simp: bounded.bilinear_simps intro!: bounded_eqI)

lemma bounded_bij2:
  fixes f::"'a \<Rightarrow>\<^sub>B 'a::euclidean_space"
  assumes "f o\<^sub>L g = id_bounded"
  shows "bij (bounded_apply g)"
proof (rule bijI)
  show "inj g"
    using assms
    by (metis bounded_apply_id_bounded bounded_compose.rep_eq injI inj_on_imageI2)
  then show "surj g"
    using bounded.bounded_clinear_right bounded_clinear_def linear_inj_imp_surj by blast
qed

lemma bounded_bij1:
  fixes f::"'a \<Rightarrow>\<^sub>B 'a::euclidean_space"
  assumes "f o\<^sub>L g = id_bounded"
  shows "bij (bounded_apply f)"
proof (rule bijI)
  show "surj (bounded_apply f)"
    by (metis assms bounded_apply_bounded_compose bounded_apply_id_bounded surjI)
  then show "inj (bounded_apply f)"
    using bounded.bounded_clinear_right bounded_clinear_def linear_surj_imp_inj by blast
qed

lift_definition bounded_inner_right::"'a::real_inner \<Rightarrow> 'a \<Rightarrow>\<^sub>B real" is "(\<bullet>)"
  by (rule bounded_clinear_inner_right)
declare bounded_inner_right.rep_eq[simp]

lemma bounded_clinear_bounded_inner_right[bounded_clinear]: "bounded_clinear bounded_inner_right"
  by transfer (rule bounded_bilinear_inner)


lift_definition bounded_inner_left::"'a::real_inner \<Rightarrow> 'a \<Rightarrow>\<^sub>B real" is "\<lambda>x y. y \<bullet> x"
  by (rule bounded_clinear_inner_left)
declare bounded_inner_left.rep_eq[simp]

lemma bounded_clinear_bounded_inner_left[bounded_clinear]: "bounded_clinear bounded_inner_left"
  by transfer (rule bounded_bilinear.flip[OF bounded_bilinear_inner])


lift_definition bounded_scaleR_right::"real \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'a::complex_normed_vector" is "(*\<^sub>R)"
  by (rule bounded_clinear_scaleR_right)
declare bounded_scaleR_right.rep_eq[simp]

lemma bounded_clinear_bounded_scaleR_right[bounded_clinear]: "bounded_clinear bounded_scaleR_right"
  by transfer (rule bounded_bilinear_scaleR)


lift_definition bounded_scaleR_left::"'a::complex_normed_vector \<Rightarrow> real \<Rightarrow>\<^sub>B 'a" is "\<lambda>x y. y *\<^sub>R x"
  by (rule bounded_clinear_scaleR_left)
lemmas [simp] = bounded_scaleR_left.rep_eq

lemma bounded_clinear_bounded_scaleR_left[bounded_clinear]: "bounded_clinear bounded_scaleR_left"
  by transfer (rule bounded_bilinear.flip[OF bounded_bilinear_scaleR])


lift_definition bounded_mult_right::"'a \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'a::real_normed_algebra" is "(*)"
  by (rule bounded_clinear_mult_right)
declare bounded_mult_right.rep_eq[simp]

lemma bounded_clinear_bounded_mult_right[bounded_clinear]: "bounded_clinear bounded_mult_right"
  by transfer (rule bounded_bilinear_mult)


lift_definition bounded_mult_left::"'a::real_normed_algebra \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'a" is "\<lambda>x y. y * x"
  by (rule bounded_clinear_mult_left)
lemmas [simp] = bounded_mult_left.rep_eq

lemma bounded_clinear_bounded_mult_left[bounded_clinear]: "bounded_clinear bounded_mult_left"
  by transfer (rule bounded_bilinear.flip[OF bounded_bilinear_mult])

lemmas bounded_clinear_function_uniform_limit_intros[uniform_limit_intros] =
  bounded_clinear.uniform_limit[OF bounded_clinear_apply_bounded]
  bounded_clinear.uniform_limit[OF bounded_clinear_bounded_apply]
  bounded_clinear.uniform_limit[OF bounded_clinear_bounded_matrix]


subsection \<open>The strong operator topology on continuous linear operators\<close>

text \<open>Let \<open>'a\<close> and \<open>'b\<close> be two normed real vector spaces. Then the space of linear continuous
operators from \<open>'a\<close> to \<open>'b\<close> has a canonical norm, and therefore a canonical corresponding topology
(the type classes instantiation are given in \<^file>\<open>Bounded_Linear_Function.thy\<close>).

However, there is another topology on this space, the strong operator topology, where \<open>T\<^sub>n\<close> tends to
\<open>T\<close> iff, for all \<open>x\<close> in \<open>'a\<close>, then \<open>T\<^sub>n x\<close> tends to \<open>T x\<close>. This is precisely the product topology
where the target space is endowed with the norm topology. It is especially useful when \<open>'b\<close> is the set
of real numbers, since then this topology is compact.

We can not implement it using type classes as there is already a topology, but at least we
can define it as a topology.

Note that there is yet another (common and useful) topology on operator spaces, the weak operator
topology, defined analogously using the product topology, but where the target space is given the
weak-* topology, i.e., the pullback of the weak topology on the bidual of the space under the
canonical embedding of a space into its bidual. We do not define it there, although it could also be
defined analogously.
\<close>

definition\<^marker>\<open>tag important\<close> strong_operator_topology::"('a::complex_normed_vector \<Rightarrow>\<^sub>B'b::complex_normed_vector) topology"
where "strong_operator_topology = pullback_topology UNIV bounded_apply euclidean"

lemma strong_operator_topology_topspace:
  "topspace strong_operator_topology = UNIV"
unfolding strong_operator_topology_def topspace_pullback_topology topspace_euclidean by auto

lemma strong_operator_topology_basis:
  fixes f::"('a::complex_normed_vector \<Rightarrow>\<^sub>B'b::complex_normed_vector)" and U::"'i \<Rightarrow> 'b set" and x::"'i \<Rightarrow> 'a"
  assumes "finite I" "\<And>i. i \<in> I \<Longrightarrow> open (U i)"
  shows "openin strong_operator_topology {f. \<forall>i\<in>I. bounded_apply f (x i) \<in> U i}"
proof -
  have "open {g::('a\<Rightarrow>'b). \<forall>i\<in>I. g (x i) \<in> U i}"
    by (rule product_topology_basis'[OF assms])
  moreover have "{f. \<forall>i\<in>I. bounded_apply f (x i) \<in> U i}
                = bounded_apply-`{g::('a\<Rightarrow>'b). \<forall>i\<in>I. g (x i) \<in> U i} \<inter> UNIV"
    by auto
  ultimately show ?thesis
    unfolding strong_operator_topology_def by (subst openin_pullback_topology) auto
qed

lemma strong_operator_topology_continuous_evaluation:
  "continuous_map strong_operator_topology euclidean (\<lambda>f. bounded_apply f x)"
proof -
  have "continuous_map strong_operator_topology euclidean ((\<lambda>f. f x) o bounded_apply)"
    unfolding strong_operator_topology_def apply (rule continuous_map_pullback)
    using continuous_on_product_coordinates by fastforce
  then show ?thesis unfolding comp_def by simp
qed

lemma continuous_on_strong_operator_topo_iff_coordinatewise:
  "continuous_map T strong_operator_topology f
    \<longleftrightarrow> (\<forall>x. continuous_map T euclidean (\<lambda>y. bounded_apply (f y) x))"
proof (auto)
  fix x::"'b"
  assume "continuous_map T strong_operator_topology f"
  with continuous_map_compose[OF this strong_operator_topology_continuous_evaluation]
  have "continuous_map T euclidean ((\<lambda>z. bounded_apply z x) o f)"
    by simp
  then show "continuous_map T euclidean (\<lambda>y. bounded_apply (f y) x)"
    unfolding comp_def by auto
next
  assume *: "\<forall>x. continuous_map T euclidean (\<lambda>y. bounded_apply (f y) x)"
  have "\<And>i. continuous_map T euclidean (\<lambda>x. bounded_apply (f x) i)"
    using * unfolding comp_def by auto
  then have "continuous_map T euclidean (bounded_apply o f)"
    unfolding o_def
    by (metis (no_types) continuous_map_componentwise_UNIV euclidean_product_topology)
  show "continuous_map T strong_operator_topology f"
    unfolding strong_operator_topology_def
    apply (rule continuous_map_pullback')
    by (auto simp add: \<open>continuous_map T euclidean (bounded_apply o f)\<close>)
qed

lemma strong_operator_topology_weaker_than_euclidean:
  "continuous_map euclidean strong_operator_topology (\<lambda>f. f)"
  by (subst continuous_on_strong_operator_topo_iff_coordinatewise,
    auto simp add: linear_continuous_on)

end

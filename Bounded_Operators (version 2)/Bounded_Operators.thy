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
unbundle notation_norm

lemma c_onorm_componentwise:
  assumes "bounded_clinear f"
  shows "onorm f \<le> (\<Sum>i\<in>Basis. \<parallel>f i\<parallel>)"
  using assms bounded_clinear_is_bounded_linear onorm_componentwise by fastforce

subsection\<^marker>\<open>tag unimportant\<close> \<open>Intro rules for \<^term>\<open>bounded_clinear\<close>\<close>

named_theorems bounded_clinear_intros

lemma c_onorm_inner_left:
  assumes "bounded_clinear r"
  shows "onorm (\<lambda>x. r x \<bullet> f) \<le> onorm r * \<parallel>f\<parallel>"
  by (simp add: assms bounded_clinear_is_bounded_linear onorm_inner_left)


lemma c_onorm_inner_right:
  assumes "bounded_clinear r"
  shows "onorm (\<lambda>x. f \<bullet> r x) \<le> \<parallel>f\<parallel> * onorm r"
  by (simp add: assms bounded_clinear_is_bounded_linear onorm_inner_right)


lemmas [bounded_clinear_intros] =
  bounded_clinear_zero
  bounded_clinear_add
  bounded_clinear_const_mult
  bounded_clinear_mult_const
  bounded_clinear_ident
  bounded_clinear_sum
  bounded_clinear_sub

subsection \<open>Type of bounded complex-linear functions\<close>

typedef\<^marker>\<open>tag important\<close> (overloaded) ('a, 'b) bounded ("(_ \<Rightarrow>\<^sub>B /_)" [22, 21] 21) =
  "{f::'a::complex_normed_vector \<Rightarrow>'b::complex_normed_vector. bounded_clinear f}"
  morphisms bounded_apply BOUNDED
  using bounded_clinear_zero by blast

declare [[coercion
      "bounded_apply :: ('a::complex_normed_vector \<Rightarrow>\<^sub>B'b::complex_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'b"]]

lemma bounded_apply_blinfun_apply:
  "\<exists>f. bounded_apply F = blinfun_apply f"
proof-
  have \<open>bounded_clinear (bounded_apply F)\<close>
    using bounded_apply by blast
  hence \<open>bounded_linear (bounded_apply F)\<close>
    by (simp add: bounded_clinear_is_bounded_linear)
  thus ?thesis by (metis bounded_linear_Blinfun_apply) 
qed

lemma bounded_clinear_bounded_apply[bounded_clinear_intros]:
  "bounded_clinear g \<Longrightarrow> bounded_clinear (\<lambda>x. bounded_apply f (g x))"
  apply transfer
  using bounded_apply bounded_clinear_compose by blast 

setup_lifting type_definition_bounded

lemma bounded_eqI: "(\<And>i. bounded_apply x i = bounded_apply y i) \<Longrightarrow> x = y"
  by transfer auto

lemma bounded_linear_BOUNDED_apply: "bounded_clinear f \<Longrightarrow> bounded_apply (BOUNDED f) = f"
  by (simp add: BOUNDED_inverse)

subsection \<open>Type class instantiations\<close>

instantiation bounded :: (complex_normed_vector, complex_normed_vector) complex_normed_vector
begin

lift_definition\<^marker>\<open>tag important\<close> norm_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> real" is onorm .

lift_definition minus_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  is "\<lambda>f g x. f x - g x"
  by (simp add: bounded_clinear_sub)


definition dist_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> real"
  where "dist_bounded a b = \<parallel>a - b\<parallel>"

definition [code del]:
  "(uniformity :: (('a \<Rightarrow>\<^sub>B 'b) \<times> ('a \<Rightarrow>\<^sub>B 'b)) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_bounded :: "('a \<Rightarrow>\<^sub>B 'b) set \<Rightarrow> bool"
  where [code del]: "open_bounded S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"

lift_definition uminus_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b" is "\<lambda>f x. - f x"
  by (simp add: bounded_clinear_minus)  

lift_definition\<^marker>\<open>tag important\<close> zero_bounded :: "'a \<Rightarrow>\<^sub>B 'b" is "\<lambda>x. 0"
  by simp

lift_definition\<^marker>\<open>tag important\<close> plus_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  is "\<lambda>f g x. f x + g x"
  by (simp add: bounded_clinear_add)

lift_definition\<^marker>\<open>tag important\<close> scaleR_bounded::"real \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b" is "\<lambda>r f x. r *\<^sub>R f x"
  by (simp add: scalarR_bounded_clinear)

lift_definition\<^marker>\<open>tag important\<close> scaleC_bounded::"complex \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b" 
  is "\<lambda>r f x. r *\<^sub>C f x"
  by (simp add: bounded_clinear_compose bounded_clinear_scaleR_right)

definition sgn_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  where "sgn_bounded x = (inverse \<parallel>x\<parallel>) *\<^sub>R x"

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
    using scaleR_left.add by auto 
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
    apply transfer by simp
  show "((*\<^sub>R) r::'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
  proof
    show "r *\<^sub>R (x::'a \<Rightarrow>\<^sub>B 'b) = complex_of_real r *\<^sub>C x"
      for x :: "'a \<Rightarrow>\<^sub>B 'b"
      by (simp add: Bounded_Operators.scaleC_bounded.rep_eq Bounded_Operators.scaleR_bounded.rep_eq 
          bounded_eqI scaleR_scaleC)      
  qed
  show "dist x y = \<parallel>x - y\<parallel>"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
      and y :: "'a \<Rightarrow>\<^sub>B 'b"
    by (simp add: dist_bounded_def)

  show "sgn x = inverse \<parallel>x\<parallel> *\<^sub>R x"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
    by (simp add: sgn_bounded_def)

  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a \<Rightarrow>\<^sub>B 'b) y < e})"
    by (simp add: uniformity_bounded_def)

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
    for U :: "('a \<Rightarrow>\<^sub>B 'b) set"
    by (simp add: Bounded_Operators.open_bounded_def)

  show "(\<parallel>x\<parallel> = 0) = (x = 0)"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
  proof
    show "x = 0"
      if "\<parallel>x\<parallel> = 0"
      using that apply transfer
      by (metis (no_types) bounded_clinear_is_bounded_linear less_numeral_extra(3) onorm_pos_lt)
    show "\<parallel>x\<parallel> = 0"
      if "x = 0"
      using that apply transfer
      by (simp add: onorm_eq_0) 
  qed
  show "\<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
      and y :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: bounded_clinear_is_bounded_linear onorm_triangle)
  show "\<parallel>a *\<^sub>R x\<parallel> = \<bar>a\<bar> * \<parallel>x\<parallel>"
    for a :: real
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: bounded_clinear_is_bounded_linear onorm_scaleR) 
  show "\<parallel>a *\<^sub>C x\<parallel> = \<parallel>a\<parallel> * \<parallel>x\<parallel>"
    for a :: complex
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: onorm_scalarC) 
qed
end



unbundle no_notation_norm

end

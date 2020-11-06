theory One_Dimensional_Spaces
  imports Complex_Inner_Product
begin

text \<open>The class \<open>one_dim\<close> applies to one-dimensional vector spaces.
Those are additionally interpreted as \<^class>\<open>complex_algebra_1\<close>s 
via the canonical isomorphism between a one-dimensional vector space and 
\<^typ>\<open>complex\<close>.\<close>
class one_dim = onb_enum + one + times + complex_inner +
  assumes one_dim_canonical_basis: "canonical_basis = [1]"
  assumes one_dim_prod_scale1: "(a *\<^sub>C 1) * (b *\<^sub>C 1) = (a*b) *\<^sub>C 1"
  (* TODO: Add whatever is necessary to make one_dim also a complex_normed_field *)
  (* TODO: Dominique does it *)

instance complex :: one_dim
  apply intro_classes
  unfolding canonical_basis_complex_def is_ortho_set_def
  by auto

lemma one_dim_1_times_1: \<open>\<langle>(1::('a::one_dim)), 1\<rangle> = 1\<close>
proof-
  include notation_norm
  have \<open>(canonical_basis::'a list) = [1::('a::one_dim)]\<close>
    by (simp add: one_dim_canonical_basis)    
  hence \<open>\<parallel>1::'a::one_dim\<parallel> = 1\<close>
    by (metis is_normal list.set_intros(1))
  hence \<open>\<parallel>1::'a::one_dim\<parallel>^2 = 1\<close>
    by simp
  moreover have  \<open>\<parallel>(1::('a::one_dim))\<parallel>^2 = \<langle>(1::('a::one_dim)), 1\<rangle>\<close>
    using power2_norm_eq_cinner' by auto
  ultimately show ?thesis by simp
qed

lemma one_dim_1_times_a_eq_a: \<open>\<langle>1::('a::one_dim), a\<rangle> *\<^sub>C 1 = a\<close>
proof-
  have \<open>(canonical_basis::'a list) = [1]\<close>
    by (simp add: one_dim_canonical_basis)
  hence \<open>a \<in> complex_vector.span ({1::'a})\<close>        
    using  iso_tuple_UNIV_I empty_set is_generator_set list.simps(15)
    by metis
  hence \<open>\<exists> s. a = s *\<^sub>C 1\<close>
  proof -
    have "(1::'a) \<notin> {}"
      by (metis equals0D)
    thus ?thesis
      by (metis Diff_insert_absorb \<open>a \<in> complex_vector.span {1}\<close> complex_vector.span_breakdown complex_vector.span_empty eq_iff_diff_eq_0 singleton_iff)
  qed
  then obtain s where \<open>a = s *\<^sub>C 1\<close>
    by blast
  have  \<open>\<langle>(1::'a), a\<rangle> = \<langle>(1::'a), s *\<^sub>C 1\<rangle>\<close>
    using \<open>a = s *\<^sub>C 1\<close>
    by simp 
  also have \<open>\<dots> = s * \<langle>(1::'a), 1\<rangle>\<close>
    by simp
  also have \<open>\<dots> = s\<close>
    using one_dim_1_times_1 by auto
  finally show ?thesis
    by (simp add: \<open>a = s *\<^sub>C 1\<close>) 
qed

lemma one_dim_prod: "(\<psi>::_::one_dim) * \<phi> = (\<langle>1, \<psi>\<rangle> * \<langle>1, \<phi>\<rangle>) *\<^sub>C 1"
  apply (subst one_dim_1_times_a_eq_a[symmetric, of \<psi>])
  apply (subst one_dim_1_times_a_eq_a[symmetric, of \<phi>])
  by (simp add: one_dim_prod_scale1)


instance one_dim \<subseteq> complex_algebra_1
proof
  show "(a * b) * c = a * (b * c)"
    for a :: 'a
      and b :: 'a
      and c :: 'a
    by (simp add: one_dim_prod[where ?'a='a])
  show "(a + b) * c = a * c + b * c"
    for a :: 'a
      and b :: 'a
      and c :: 'a
    apply (simp add: one_dim_prod[where ?'a='a])
    by (metis (no_types, lifting) cinner_right_distrib scaleC_add_left scaleC_scaleC)
  show "a * (b + c) = a * b + a * c"
    for a :: 'a
      and b :: 'a
      and c :: 'a
    apply (simp add: one_dim_prod[where ?'a='a])
    by (simp add: cinner_right_distrib scaleC_add_left vector_space_over_itself.scale_right_distrib)
  show "(a *\<^sub>C x) * y = a *\<^sub>C (x * y)"
    for a :: complex
      and x :: 'a
      and y :: 'a
    apply (simp add: one_dim_prod[where ?'a='a]).
  show "x * (a *\<^sub>C y) = a *\<^sub>C (x * y)"
    for x :: 'a
      and a :: complex
      and y :: 'a
    apply (simp add: one_dim_prod[where ?'a='a]).
  show "(1::'a) * a = a"
    for a :: 'a
  proof-
    have \<open>\<langle>(1::'a), 1\<rangle> = 1\<close>
      by (simp add: one_dim_1_times_1)      
    moreover have \<open>\<langle>1, a\<rangle> *\<^sub>C 1 = a\<close>
      using one_dim_1_times_a_eq_a by blast
    ultimately have \<open>(\<langle>(1::'a), 1\<rangle> * \<langle>1, a\<rangle>) *\<^sub>C 1 = a\<close>
      by simp
    thus ?thesis
      by (simp add: one_dim_prod[where ?'a='a])
  qed
  show "(a::'a) * 1 = a"
    for a :: 'a
    apply (simp add: one_dim_prod[where ?'a='a])
    by (simp add: one_dim_1_times_1 one_dim_1_times_a_eq_a)
  show "(0::'a) \<noteq> 1"
  proof-
    have \<open>(canonical_basis::('a list)) = [1]\<close>
      by (simp add: one_dim_canonical_basis)
    hence \<open>1 \<in> set (canonical_basis::('a list))\<close>
      by (metis list.set_intros(1))
    thus ?thesis
      using canonical_basis_non_zero by fastforce       
  qed
qed

instance one_dim \<subseteq> complex_normed_algebra
proof
  show "norm (x * y) \<le> norm x * norm y"
    for x y::"'a::one_dim"
  proof-
    have "\<langle>(1::'a), 1\<rangle> = 1"
      by (simp add: one_dim_1_times_1)
    hence "(norm (1::'a))^2 = 1"
      by (simp add: power2_norm_eq_cinner)
    hence "norm (1::'a) = 1"
      by (smt abs_norm_cancel power2_eq_1_iff)
    hence "cmod (\<langle>1::'a, x\<rangle> * \<langle>1::'a, y\<rangle>) * norm (1::'a) = cmod (\<langle>1::'a, x\<rangle> * \<langle>1::'a, y\<rangle>)"
      by simp
    also have "\<dots> = cmod (\<langle>1::'a, x\<rangle>) * cmod (\<langle>1::'a, y\<rangle>)"
      by (simp add: norm_mult)
    also have "\<dots> \<le> norm (1::'a) * norm x * norm (1::'a) * norm y"
    proof-
      have "cmod (\<langle>1::'a, x\<rangle>) \<le> norm (1::'a) * norm x"
        by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)
      moreover have "cmod (\<langle>1::'a, y\<rangle>) \<le> norm (1::'a) * norm y"
        by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)
      ultimately show ?thesis
        by (smt \<open>norm 1 = 1\<close> mult_cancel_left1 mult_cancel_right1 norm_scaleC one_dim_1_times_a_eq_a)
    qed
    also have "\<dots> = norm x * norm y"
      by (simp add: \<open>norm 1 = 1\<close>)
    finally show ?thesis
      by (simp add: one_dim_prod[where ?'a='a])
  qed
qed

instance one_dim \<subseteq> complex_normed_algebra_1
  apply intro_classes
  by (metis complex_inner_1_left norm_eq_sqrt_cinner norm_one one_dim_1_times_1)

(* TODO-DOMINIQUE rename to one_dim_isom *)
definition one_dim_isom' :: "'a::one_dim \<Rightarrow> 'b::one_dim"
  where "one_dim_isom' a = of_complex (\<langle>1, a\<rangle>)"

lemma one_dim_isom'_inverse[simp]: "one_dim_isom' (one_dim_isom' x) = x"
  apply (simp add: one_dim_isom'_def)
  by (simp add: of_complex_def one_dim_1_times_a_eq_a)

lemma one_dim_isom'_adjoint: "\<langle>one_dim_isom' x, y\<rangle> = \<langle>x, one_dim_isom' y\<rangle>"
  by (simp add: one_dim_isom'_def of_complex_def)

lemma one_dim_isom'_eq_of_complex[simp]: "one_dim_isom' = of_complex"
  unfolding one_dim_isom'_def by auto

lemma of_complex_one_dim_isom'[simp]: "of_complex (one_dim_isom' \<psi>) = \<psi>"
  by (subst one_dim_isom'_eq_of_complex[symmetric], rule one_dim_isom'_inverse)

lemma one_dim_isom'_of_complex[simp]: "one_dim_isom' (of_complex c) = c"
  by (subst one_dim_isom'_eq_of_complex[symmetric], rule one_dim_isom'_inverse)

lemma one_dim_isom'_add[simp]:
  \<open>one_dim_isom' (a + b) = one_dim_isom' a + one_dim_isom' b\<close>
  by (simp add: cinner_simps(2) one_dim_isom'_def)

lemma one_dim_isom'_scaleC[simp]: "one_dim_isom' (c *\<^sub>C \<psi>) = c *\<^sub>C one_dim_isom' \<psi>"
  by (metis cinner_scaleC_right of_complex_mult one_dim_isom'_def scaleC_conv_of_complex)

lemma clinear_one_dim_isom'[simp]: "clinear one_dim_isom'"
  apply (rule clinearI) by auto

lemma cbounded_linear_one_dim_isom'[simp]: "cbounded_linear one_dim_isom'"
  apply (rule cbounded_linear_intro[where K=1], auto)
  by (metis (full_types) norm_of_complex of_complex_def one_dim_1_times_a_eq_a one_dim_isom'_def order_refl)

lemma one_dim_isom'_one[simp]: "one_dim_isom' (1::'a::one_dim) = 1"
  by (simp add: one_dim_1_times_1 one_dim_isom'_def)

lemma onorm_one_dim_isom'[simp]: "onorm one_dim_isom' = 1"
  apply (rule onormI[where b=1 and x=1])
  apply auto
  by (metis eq_iff norm_of_complex of_complex_def one_dim_1_times_a_eq_a one_dim_isom'_def)

lemma one_dim_isom'_times[simp]: "one_dim_isom' (\<psi> * \<phi>) = one_dim_isom' \<psi> * one_dim_isom' \<phi>"
  by (smt of_complex_inner_1 one_dim_isom'_def one_dim_isom'_one one_dim_isom'_scaleC one_dim_prod)

lemma one_dim_isom'_0[simp]: "one_dim_isom' 0 = 0"
  by (simp add: complex_vector.linear_0)

lemma one_dim_isom'_0': "one_dim_isom' x = 0 \<Longrightarrow> x = 0"
  by (metis one_dim_isom'_0 one_dim_isom'_inverse)

lemma one_dim_scaleC_1[simp]: "one_dim_isom' x *\<^sub>C 1 = x"
  sorry

lemma one_dim_linear_eq: 
  assumes "(x::'a::one_dim) \<noteq> 0"
  assumes "clinear f" and "clinear g"
  assumes "f x = g x"
  shows "f = g"
proof (rule ext)
  fix y :: 'a
  from \<open>f x = g x\<close>
  have \<open>one_dim_isom' x *\<^sub>C f 1 = one_dim_isom' x *\<^sub>C g 1\<close>
   by (metis assms(2) assms(3) complex_vector.linear_scale one_dim_scaleC_1)
  then have "f 1 = g 1"
    using assms(1) one_dim_isom'_0' by auto
  then show "f y = g y"
    by (metis assms(2) assms(3) complex_vector.linear_scale one_dim_scaleC_1)
qed

lemma one_dim_norm: "norm x = cmod (one_dim_isom' x)"
  apply (subst one_dim_scaleC_1[symmetric])
  apply (simp only: norm_scaleC) by simp

lemma one_dim_onorm:
  fixes f :: "'a::one_dim \<Rightarrow> 'b::complex_normed_vector"
  assumes "clinear f"
  shows "onorm f = norm (f 1)"
proof (rule onormI[where x=1])
  fix x :: 'a
  show "norm (f x) \<le> norm (f 1) * norm x"
    apply (subst one_dim_scaleC_1[symmetric])
    apply (simp only: linear_scale assms norm_scaleC one_dim_norm[symmetric])
    by auto
qed auto

lemma one_dim_onorm':
  fixes f :: "'a::one_dim \<Rightarrow> 'b::one_dim"
  assumes "clinear f"
  shows "onorm f = cmod (one_dim_isom' (f 1))"
  using assms one_dim_norm one_dim_onorm by fastforce

instance one_dim \<subseteq> zero_neq_one ..

lemma one_dim_isom'_inj: "one_dim_isom' x = one_dim_isom' y \<Longrightarrow> x = y"
  by (metis one_dim_isom'_inverse)
  

end

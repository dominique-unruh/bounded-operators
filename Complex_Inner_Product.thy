(* Title:      Bounded-Operators/Complex_Inner_Product.thy
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

section \<open>Inner Product Spaces and the Gradient Derivative\<close>

theory Complex_Inner_Product
  imports "HOL-Analysis.Infinite_Set_Sum" Complex_Main Complex_Vector_Spaces "HOL-Analysis.Inner_Product"
begin

subsection \<open>Complex inner product spaces\<close>

text \<open>
Temporarily relax type constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
\<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::open set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::dist \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniformity \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::norm \<Rightarrow> real\<close>)\<close>

class complex_inner = complex_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  fixes cinner :: "'a \<Rightarrow> 'a \<Rightarrow> complex"
  assumes cinner_commute: "cinner x y = cnj (cinner y x)"
    and cinner_add_left: "cinner (x + y) z = cinner x z + cinner y z"
    and cinner_scaleC_left [simp]: "cinner (scaleC r x) y = cnj r * (cinner x y)"
    and cinner_ge_zero [simp]: "0 \<le> cinner x x"
    and cinner_eq_zero_iff [simp]: "cinner x x = 0 \<longleftrightarrow> x = 0"
    and norm_eq_sqrt_cinner: "norm x = sqrt (cmod (cinner x x))"
begin


lemma cinner_real: "cinner x x \<in> \<real>"
  by (simp add: reals_zero_comparable_iff)

lemmas cinner_commute' [simp] = cinner_commute[symmetric]

lemma cinner_zero_left [simp]: "cinner 0 x = 0"
  using cinner_add_left [of 0 0 x] by simp

lemma cinner_minus_left [simp]: "cinner (- x) y = - cinner x y"
  using cinner_add_left [of x "- x" y]
  by (metis (mono_tags, lifting) cancel_ab_semigroup_add_class.add_diff_cancel_left' cinner_zero_left group_add_class.diff_0 local.right_minus)

lemma cinner_diff_left: "cinner (x - y) z = cinner x z - cinner y z"
  using cinner_add_left [of x "- y" z] by simp

lemma cinner_sum_left: "cinner (\<Sum>x\<in>A. f x) y = (\<Sum>x\<in>A. cinner (f x) y)"
  by (cases "finite A", induct set: finite, simp_all add: cinner_add_left)

text \<open>Transfer distributivity rules to right argument.\<close>

lemma cinner_add_right: "cinner x (y + z) = cinner x y + cinner x z"
  using cinner_add_left [of y z x]
  by (metis complex_cnj_add local.cinner_commute)

lemma cinner_scaleC_right [simp]: "cinner x (scaleC r y) = r * (cinner x y)"
  using cinner_scaleC_left [of r y x]
  by (metis complex_cnj_cnj complex_cnj_mult local.cinner_commute)

lemma cinner_zero_right [simp]: "cinner x 0 = 0"
  using cinner_zero_left [of x] 
  by (metis (mono_tags, lifting) complex_cnj_zero local.cinner_commute) 

lemma cinner_minus_right [simp]: "cinner x (- y) = - cinner x y"
  using cinner_minus_left [of y x]
  by (metis complex_cnj_minus local.cinner_commute)

lemma cinner_diff_right: "cinner x (y - z) = cinner x y - cinner x z"
  using cinner_diff_left [of y z x]
  by (metis complex_cnj_diff local.cinner_commute)

lemma cinner_sum_right: "cinner x (\<Sum>y\<in>A. f y) = (\<Sum>y\<in>A. cinner x (f y))"
  apply (subst cinner_commute)
  apply (subst (2) cinner_commute)
  unfolding cnj_sum[symmetric]
  apply (subst cinner_sum_left) by simp

lemmas cinner_add [algebra_simps] = cinner_add_left cinner_add_right
lemmas cinner_diff [algebra_simps]  = cinner_diff_left cinner_diff_right
lemmas cinner_scaleC = cinner_scaleC_left cinner_scaleC_right

text \<open>Legacy theorem names\<close>
lemmas cinner_left_distrib = cinner_add_left
lemmas cinner_right_distrib = cinner_add_right
lemmas cinner_distrib = cinner_left_distrib cinner_right_distrib

lemma cinner_gt_zero_iff [simp]: "0 < cinner x x \<longleftrightarrow> x \<noteq> 0"
  by (simp add: order_less_le)

lemma power2_norm_eq_cinner: "(norm x)\<^sup>2 = cmod (cinner x x)"
  by (simp add: norm_eq_sqrt_cinner)


lemma power2_norm_eq_cinner': "complex_of_real ((norm x)\<^sup>2) = cinner x x"
  apply (subst power2_norm_eq_cinner)
  using cinner_ge_zero by (rule complex_of_real_cmod)

lemma power2_norm_eq_cinner'': "(complex_of_real (norm x))\<^sup>2 = cinner x x"
  using power2_norm_eq_cinner' by simp


text \<open>Identities involving complex multiplication and division.\<close>

lemma cinner_mult_left: "cinner (of_complex m * a) b = cnj m * (cinner a b)"
  unfolding of_complex_def by simp

lemma cinner_mult_right: "cinner a (of_complex m * b) = m * (cinner a b)"
  by (metis complex_inner_class.cinner_scaleC_right scaleC_conv_of_complex)

lemma cinner_mult_left': "cinner (a * of_complex m) b = cnj m * (cinner a b)"
  using cinner_mult_left by (simp add: of_complex_def)

lemma cinner_mult_right': "cinner a (b * of_complex m) = (cinner a b) * m"
  by (simp add: of_complex_def complex_inner_class.cinner_scaleC_right)

lemma Cauchy_Schwarz_ineq:
  "cinner x y * cnj (cinner x y) \<le> cinner x x * cinner y y"
proof (cases)
  assume "y = 0"
  thus ?thesis by simp
next
  assume y: "y \<noteq> 0"
  have [simp]: "cnj (cinner y y) = cinner y y" for y
    by (metis local.cinner_commute)
  define r where "r = cnj (cinner x y) / cinner y y"
  have "0 \<le> cinner (x - scaleC r y) (x - scaleC r y)"
    by (rule cinner_ge_zero)
  also have "\<dots> = cinner x x - r * cinner x y - cnj r * cinner y x + r * cnj r * cinner y y"
    unfolding cinner_diff_left cinner_diff_right cinner_scaleC_left cinner_scaleC_right by algebra
  also have "\<dots> = cinner x x - cinner y x * cnj r"
    unfolding r_def by auto
  also have "\<dots> = cinner x x - cinner x y * cnj (cinner x y) / cinner y y"
    unfolding r_def by (simp add: power2_eq_square)
  finally have "0 \<le> cinner x x - cinner x y * cnj (cinner x y) / cinner y y" .
  hence "cinner x y * cnj (cinner x y) / cinner y y \<le> cinner x x"
    by (simp add: le_diff_eq)
  thus "cinner x y * cnj (cinner x y) \<le> cinner x x * cinner y y"
    by (simp add: pos_divide_le_eq y)
qed

lemma Im_cinner_x_x[simp]: "Im (cinner x x) = 0"
  using comp_Im_same[OF cinner_ge_zero] by simp

lemma cinner_norm_sq: "cinner x x = complex_of_real ((norm x)^2)"
proof -
  define r where "r = Re (cinner x x)"
  have r: "cinner x x = complex_of_real r"
    unfolding r_def
    using Im_cinner_x_x[of x] apply (cases "cinner x x") by (auto simp: complex_of_real_def)
  have rpos: "r \<ge> 0"
    unfolding r_def
    using complex_of_real_nn_iff r r_def by fastforce
  show ?thesis
    unfolding power2_norm_eq_cinner
    unfolding r using rpos by auto
qed

lemma Cauchy_Schwarz_ineq2:
  "cmod (cinner x y) \<le> norm x * norm y"
proof (rule power2_le_imp_le)
  have ineq: "cinner x y * cnj (cinner x y) \<le> cinner x x * cinner y y"
    using Cauchy_Schwarz_ineq .
  have "(cmod (cinner x y))^2 = Re (cinner x y * cnj (cinner x y))"
    by (metis (mono_tags) Re_complex_of_real complex_norm_square)
  also have "\<dots> \<le> Re (cinner x x * cinner y y)"
    using ineq by (rule Re_mono)
  also have "\<dots> = Re (complex_of_real ((norm x)^2) * complex_of_real ((norm y)^2))"
    unfolding cinner_norm_sq by simp
  also have "\<dots> = (norm x * norm y)\<^sup>2"
    by (simp add: power_mult_distrib)
  finally show "(cmod (cinner x y))^2 \<le> (norm x * norm y)\<^sup>2" .
  show "0 \<le> norm x * norm y"
    by (simp add: local.norm_eq_sqrt_cinner)
qed

lemma norm_cauchy_schwarz: "abs (cinner x y) \<le> complex_of_real (norm x) * complex_of_real (norm y)"
  using Cauchy_Schwarz_ineq2 [of x y, THEN complex_of_real_mono]
  unfolding abs_complex_def
  by auto

subclass complex_normed_vector
proof
  fix a :: complex and r :: real and x y :: 'a
  show "norm x = 0 \<longleftrightarrow> x = 0"
    unfolding norm_eq_sqrt_cinner by simp
  show "norm (x + y) \<le> norm x + norm y"
  proof (rule power2_le_imp_le)
    have "cinner x y + cinner y x = complex_of_real (2 * Re (cinner x y))"
      apply (subst (2) cinner_commute)
      by (cases "cinner x y", simp add: complex_add complex_cnj complex_of_real_def)
    also have "\<dots> \<le> complex_of_real (2 * cmod (cinner x y))"
      apply (subst complex_of_real_mono_iff)
      using complex_Re_le_cmod by auto
    also have "\<dots> = 2 * abs (cinner x y)"
      unfolding abs_complex_def by simp
    also have "\<dots> \<le> 2 * complex_of_real (norm x) * complex_of_real (norm y)"
      using norm_cauchy_schwarz
      by (metis add_mono_thms_linordered_semiring(1) mult.assoc mult_2) 
    finally have xyyx: "cinner x y + cinner y x \<le> complex_of_real (2 * norm x * norm y)" by auto

    have "complex_of_real ((norm (x + y))\<^sup>2) = cinner (x+y) (x+y)"
      by (fact power2_norm_eq_cinner')
    also have "\<dots> = cinner x x + cinner x y + cinner y x + cinner y y"
      by (simp add: cinner_add)
    also have "\<dots> = complex_of_real ((norm x)\<^sup>2) + complex_of_real ((norm y)\<^sup>2) + cinner x y + cinner y x"
      unfolding power2_norm_eq_cinner' by simp
    also have "\<dots> \<le> complex_of_real ((norm x)\<^sup>2) + complex_of_real ((norm y)\<^sup>2) + complex_of_real (2 * norm x * norm y)"
      using xyyx by auto
    also have "\<dots> = complex_of_real ((norm x + norm y)\<^sup>2)"
      unfolding power2_sum by auto
    finally show "(norm (x + y))\<^sup>2 \<le> (norm x + norm y)\<^sup>2"
      apply (subst (asm) complex_of_real_mono_iff) by assumption
    show "0 \<le> norm x + norm y"
      unfolding norm_eq_sqrt_cinner by simp
  qed
  show norm_scaleC: "norm (a *\<^sub>C x) = cmod a * norm x" for a
    apply (rule power2_eq_imp_eq)
    by (simp_all add: norm_eq_sqrt_cinner norm_mult power2_eq_square power2_norm_eq_cinner power_mult_distrib)
  show "norm (r *\<^sub>R x) = \<bar>r\<bar> * norm x"
    unfolding scaleR_scaleC norm_scaleC by auto
qed

end

abbreviation cinner_Dirac::"'a::complex_inner \<Rightarrow> 'a \<Rightarrow> complex" ( "\<langle>_ | _\<rangle> " )
  where \<open>\<langle> x | y \<rangle> \<equiv> cinner x y\<close>

abbreviation cinner_abbr::"'a::complex_inner \<Rightarrow> 'a::complex_inner \<Rightarrow> complex" (infixl "\<cdot>" 67)
  where \<open>x \<cdot> y \<equiv> cinner x y\<close>

abbreviation norm_abbr::"'a::complex_inner \<Rightarrow> real" ("\<parallel>_\<parallel>")
  where \<open>\<parallel>x\<parallel> \<equiv> norm x\<close>

lemma cinner_divide_right:
  fixes a :: "'a :: {complex_inner,complex_div_algebra}"
  shows "cinner a (b / of_complex m) = (cinner a b) / m"
  by (metis (no_types, lifting) cinner_mult_right' divide_inverse divide_self_if inverse_eq_divide of_complex_divide of_complex_eq_0_iff one_neq_zero)

lemma cinner_divide_left:
  fixes a :: "'a :: {complex_inner,complex_div_algebra}"
  shows "cinner (a / of_complex m) b = (cinner a b) / cnj m"
  apply (subst cinner_commute) apply (subst cinner_divide_right) by simp

text \<open>
Re-enable constraints for \<^term>\<open>open\<close>, \<^term>\<open>uniformity\<close>,
\<^term>\<open>dist\<close>, and \<^term>\<open>norm\<close>.
\<close>

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::topological_space set \<Rightarrow> bool\<close>)\<close>

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniform_space \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::real_normed_vector \<Rightarrow> real\<close>)\<close>

lemma bounded_sesquilinear_cinner:
  "bounded_sesquilinear (cinner::'a::complex_inner \<Rightarrow> 'a \<Rightarrow> complex)"
proof
  fix x y z :: 'a and r :: complex
  show "cinner (x + y) z = cinner x z + cinner y z"
    by (rule cinner_add_left)
  show "cinner x (y + z) = cinner x y + cinner x z"
    by (rule cinner_add_right)
  show "cinner (scaleC r x) y = scaleC (cnj r) (cinner x y)"
    unfolding complex_scaleC_def by (rule cinner_scaleC_left)
  show "cinner x (scaleC r y) = scaleC r (cinner x y)"
    unfolding complex_scaleC_def by (rule cinner_scaleC_right)
  show "\<exists>K. \<forall>x y::'a. norm (cinner x y) \<le> norm x * norm y * K"
  proof
    show "\<forall>x y::'a. norm (cinner x y) \<le> norm x * norm y * 1"
      by (simp add: Cauchy_Schwarz_ineq2)
  qed
qed

(* term bounded_bilinear
thm bounded_bilinear.tendsto
 *)

lemmas tendsto_cinner [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas isCont_cinner [simp] =
  bounded_bilinear.isCont [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas has_derivative_cinner [derivative_intros] =
  bounded_bilinear.FDERIV [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas bounded_csemilinear_cinner_left =
  bounded_sesquilinear.bounded_csemilinear_left [OF bounded_sesquilinear_cinner]

lemmas bounded_clinear_cinner_right =
  bounded_sesquilinear.bounded_clinear_right [OF bounded_sesquilinear_cinner]

lemmas bounded_clinear_cinner_left_comp = bounded_csemilinear_cinner_left[THEN bounded_csemilinear_compose2]
lemmas bounded_csemilinear_cinner_left_comp = bounded_csemilinear_cinner_left[THEN bounded_csemilinear_compose1]

lemmas bounded_clinear_cinner_right_comp = bounded_clinear_cinner_right[THEN bounded_clinear_compose]
lemmas bounded_csemilinear_cinner_right_comp = bounded_clinear_cinner_right[THEN bounded_csemilinear_compose3]

lemmas has_derivative_cinner_right [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_clinear_cinner_right[THEN bounded_clinear.bounded_linear]]

lemmas has_derivative_cinner_left [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_csemilinear_cinner_left[THEN bounded_csemilinear.bounded_linear]]

lemma differentiable_cinner [simp]:
  "f differentiable (at x within s) \<Longrightarrow> g differentiable at x within s \<Longrightarrow> 
      (\<lambda>x. cinner (f x) (g x)) differentiable at x within s"
  unfolding differentiable_def by (blast intro: has_derivative_cinner)


subsection \<open>Class instances\<close>

instantiation complex :: complex_inner
begin

definition cinner_complex_def [simp]: "cinner x y = cnj x * y"

instance
proof
  fix x y z r :: complex
  show "cinner x y = cnj (cinner y x)"
    unfolding cinner_complex_def by auto
  show "cinner (x + y) z = cinner x z + cinner y z"
    unfolding cinner_complex_def
    by (simp add: ring_class.ring_distribs(2))
  show "cinner (scaleC r x) y = cnj r * cinner x y"
    unfolding cinner_complex_def complex_scaleC_def by simp
  show "0 \<le> cinner x x"
    apply (rule less_eq_complexI)
    unfolding cinner_complex_def by auto
  show "cinner x x = 0 \<longleftrightarrow> x = 0"
    unfolding cinner_complex_def by simp
  show "norm x = sqrt (cmod (cinner x x))"
    apply (cases x, hypsubst_thin)
    unfolding cinner_complex_def complex_cnj complex_mult complex_norm
    by (simp add: power2_eq_square) 
qed

end

lemma
  shows complex_inner_1_left[simp]: "cinner 1 x = x"
    and complex_inner_1_right[simp]: "cinner x 1 = cnj x"
  by simp_all

lemma norm_eq_square: "norm x = a \<longleftrightarrow> 0 \<le> a \<and> cinner x x = complex_of_real (a\<^sup>2)"
  by (metis cinner_norm_sq norm_ge_zero of_real_eq_iff power2_eq_imp_eq)

lemma norm_le_square: "norm x \<le> a \<longleftrightarrow> 0 \<le> a \<and> cinner x x \<le> complex_of_real (a\<^sup>2)"
  by (metis add.left_neutral add.right_neutral add_mono_thms_linordered_field(4) cinner_norm_sq complex_of_real_mono_iff norm_ge_zero not_le power2_le_imp_le power_mono)

lemma norm_ge_square: "norm x \<ge> a \<longleftrightarrow> a \<le> 0 \<or> cinner x x \<ge> complex_of_real (a\<^sup>2)"
  by (smt complex_of_real_mono_iff norm_ge_zero power2_le_imp_le power2_norm_eq_cinner')

lemma norm_lt_square: "norm x < a \<longleftrightarrow> 0 < a \<and> cinner x x < complex_of_real (a\<^sup>2)"
  by (smt Complex_Inner_Product.norm_eq_square Complex_Inner_Product.norm_le_square less_le)

lemma norm_gt_square: "norm x > a \<longleftrightarrow> a < 0 \<or> cinner x x > complex_of_real (a\<^sup>2)"
  by (smt Complex_Inner_Product.norm_le_square less_le norm_of_real of_real_power power2_norm_eq_cinner'')

text\<open>Dot product in terms of the norm rather than conversely.\<close>

lemmas cinner_simps = cinner_add_left cinner_add_right cinner_diff_right cinner_diff_left
  cinner_scaleC_left cinner_scaleC_right

lemma of_complex_inner_1 [simp]: 
  "cinner (1 :: 'a :: {complex_inner, complex_normed_algebra_1}) (of_complex x) = x"  
  by (simp add: cinner_norm_sq of_complex_def)

lemma of_complex_inner_1' [simp]:
  "cinner (of_complex x) (1 :: 'a :: {complex_inner, complex_normed_algebra_1}) = cnj x"  
  by (simp add: cinner_norm_sq of_complex_def)

lemma summable_of_complex_iff: 
  "summable (\<lambda>x. of_complex (f x) :: 'a :: {complex_normed_algebra_1,complex_inner}) \<longleftrightarrow> summable f"
proof
  assume *: "summable (\<lambda>x. of_complex (f x) :: 'a)"
  interpret bounded_linear "\<lambda>x::'a. cinner 1 x"
    apply (rule bounded_clinear.bounded_linear)
    by (rule bounded_clinear_cinner_right)
  from summable [OF *] show "summable f" by simp
next
  assume sum: "summable f"
  then show "summable (\<lambda>x. of_complex (f x) :: 'a)"
    by (rule summable_of_complex)
qed


subsection \<open>Gradient derivative\<close>

definition
  cgderiv ::
  "['a::complex_inner \<Rightarrow> complex, 'a, 'a] \<Rightarrow> bool"
  ("(cGDERIV (_)/ (_)/ :> (_))" [1000, 1000, 60] 60)
  where
    "cGDERIV f x :> D \<longleftrightarrow> FDERIV f x :> (cinner D)"

lemma cgderiv_deriv [simp]: "cGDERIV f x :> D \<longleftrightarrow> DERIV f x :> (cnj D)"
  by (simp only: cgderiv_def has_field_derivative_def cinner_complex_def[THEN ext])

lemma cGDERIV_DERIV_compose:
  assumes "cGDERIV f x :> df" and "DERIV g (f x) :> cnj dg"
  shows "cGDERIV (\<lambda>x. g (f x)) x :> scaleC dg df"
  apply (insert assms)
  unfolding cgderiv_def has_field_derivative_def
  apply (drule (1) has_derivative_compose)
  unfolding cinner_scaleC_left complex_cnj_cnj
  by assumption

lemma cGDERIV_subst: "\<lbrakk>cGDERIV f x :> df; df = d\<rbrakk> \<Longrightarrow> cGDERIV f x :> d"
  by simp

lemma cGDERIV_const: "cGDERIV (\<lambda>x. k) x :> 0"
  unfolding cgderiv_def cinner_zero_left[THEN ext] by (rule has_derivative_const)

lemma cGDERIV_add:
  "\<lbrakk>cGDERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
   \<Longrightarrow> cGDERIV (\<lambda>x. f x + g x) x :> df + dg"
  unfolding cgderiv_def cinner_add_left[THEN ext] by (rule has_derivative_add)

lemma cGDERIV_minus:
  "cGDERIV f x :> df \<Longrightarrow> cGDERIV (\<lambda>x. - f x) x :> - df"
  unfolding cgderiv_def cinner_minus_left[THEN ext] by (rule has_derivative_minus)

lemma cGDERIV_diff:
  "\<lbrakk>cGDERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
   \<Longrightarrow> cGDERIV (\<lambda>x. f x - g x) x :> df - dg"
  unfolding cgderiv_def cinner_diff_left by (rule has_derivative_diff)

lemmas has_derivative_scaleC[simp, derivative_intros] = 
  bounded_bilinear.FDERIV[OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]

lemma cGDERIV_scaleC:
  "\<lbrakk>DERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
   \<Longrightarrow> cGDERIV (\<lambda>x. scaleC (f x) (g x)) x
    :> (scaleC (cnj (f x)) dg + scaleC (cnj df) (cnj (g x)))"
  unfolding cgderiv_def has_field_derivative_def cinner_add_left cinner_scaleC_left
  apply (rule has_derivative_subst)
   apply (erule (1) has_derivative_scaleC)
  by (simp add: ac_simps)


lemma cGDERIV_mult:
  "\<lbrakk>cGDERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
   \<Longrightarrow> cGDERIV (\<lambda>x. f x * g x) x :> scaleC (cnj (f x)) dg + scaleC (cnj (g x)) df"
  unfolding cgderiv_def
  apply (rule has_derivative_subst)
   apply (erule (1) has_derivative_mult)
  unfolding cinner_add
  unfolding cinner_scaleC_left[THEN ext]
  by (simp add: cinner_add ac_simps)

lemma cGDERIV_inverse:
  "\<lbrakk>cGDERIV f x :> df; f x \<noteq> 0\<rbrakk>
   \<Longrightarrow> cGDERIV (\<lambda>x. inverse (f x)) x :> cnj (- (inverse (f x))\<^sup>2) *\<^sub>C df"
  apply (erule cGDERIV_DERIV_compose, simp)
  by (erule DERIV_inverse [folded numeral_2_eq_2])

(* TODO: 

lemma cGDERIV_norm:
assumes "x \<noteq> 0" shows "cGDERIV (\<lambda>x. complex_of_real (norm x)) x :> sgn x"

lemmas has_derivative_norm = cGDERIV_norm [unfolded cgderiv_def]
*)

class hilbert_space = complex_inner + complete_space begin
subclass banach by standard
end

class chilbert_space = complex_inner + complete_space begin
subclass hilbert_space by standard
end

subsection \<open>Some identities and inequalities\<close>

lemma polarization_identity_plus:
  \<open>(\<parallel>x + y\<parallel>)^2 = (\<parallel>x\<parallel>)^2 + (\<parallel>y\<parallel>)^2 + 2*Re (x \<cdot> y)\<close>
  (* Reference: In the proof of Corollary 1.5 in conway2013course *)
proof-
  have \<open>(x \<cdot> y) + (y \<cdot> x) = (x \<cdot> y) + cnj (x \<cdot> y)\<close>
    by simp
  hence \<open>(x \<cdot> y) + (y \<cdot> x) = 2* Re (x \<cdot> y) \<close>
    using complex_add_cnj by presburger
  have \<open>(\<parallel>x + y\<parallel>)^2 = ( (x+y) \<cdot> (x+y) )\<close> 
    using power2_norm_eq_cinner' by auto
  hence \<open>(\<parallel>x + y\<parallel>)^2 = (x \<cdot> x) + (x \<cdot> y) + (y \<cdot> x) + (y \<cdot> y)\<close>
    by (simp add: cinner_left_distrib cinner_right_distrib)
  thus ?thesis using  \<open>(x \<cdot> y) + (y \<cdot> x) = 2* Re (x \<cdot> y)\<close>
    by (smt Re_complex_of_real cinner_norm_sq plus_complex.simps(1))
qed

lemma polarization_identity_minus:
  \<open>(\<parallel>x - y\<parallel>)^2 = (\<parallel>x\<parallel>)^2 + (\<parallel>y\<parallel>)^2 - 2*Re (x \<cdot> y)\<close>
proof-
  have \<open>(\<parallel>x + (-y)\<parallel>)^2 = (\<parallel>x\<parallel>)^2 + (\<parallel>(-y)\<parallel>)^2 + 2*Re (x \<cdot> (-y))\<close>
    using polarization_identity_plus by blast
  hence \<open>(\<parallel>x - y\<parallel>)^2 = (\<parallel>x\<parallel>)^2 + (\<parallel>y\<parallel>)^2 - 2*Re (x \<cdot> y)\<close>
    by simp
  thus ?thesis 
    by blast
qed

proposition ParallelogramLaw:
  fixes x y :: "'a::complex_inner"
  shows \<open>(\<parallel>x+y\<parallel>)^2 + (\<parallel>x-y\<parallel>)^2 = 2*( (\<parallel>x\<parallel>)^2 + (\<parallel>y\<parallel>)^2 )\<close>
    (* Reference: Theorem 2.3 in conway2013course *)
  by (simp add: polarization_identity_minus polarization_identity_plus)

corollary ParallelogramLawVersion1:
  \<open>(\<parallel> (1/2) *\<^sub>C x - (1/2) *\<^sub>C y \<parallel>)^2
    = (1/2)*( (\<parallel>x\<parallel>)^2 + (\<parallel>y\<parallel>)^2 ) - (\<parallel> (1/2) *\<^sub>C x + (1/2) *\<^sub>C y \<parallel>)^2\<close>
  (* Reference: In the proof of  Theorem 2.5 in conway2013course *)
proof -
  have \<open>(\<parallel> (1/2) *\<^sub>C x + (1/2) *\<^sub>C y \<parallel>)^2 + (\<parallel> (1/2) *\<^sub>C x - (1/2) *\<^sub>C y \<parallel>)^2 
  = 2*((\<parallel>(1/2) *\<^sub>C x\<parallel>)^2 + ( \<parallel>(1/2) *\<^sub>C y\<parallel>)^2)\<close>
    using ParallelogramLaw by blast
  also have \<open>... = 2*( ((1/2) * (\<parallel>x\<parallel>))^2 + ((1/2) * (\<parallel>y\<parallel>))^2)\<close>
    by auto
  also have \<open>... = 2*( (1/2)^2 * (\<parallel>x\<parallel>)^2 +  (1/2)^2 * (\<parallel>y\<parallel>)^2 )\<close>
    by (metis power_mult_distrib)
  also have \<open>... = 2*( (1/4) * (\<parallel>x\<parallel>)^2 +  (1/4) * (\<parallel>y\<parallel>)^2 )\<close>
    by (metis (no_types, lifting) mult.right_neutral numeral_Bit0 one_add_one one_power2 power2_sum power_divide)
  also have \<open>... = 2*(1/4) * (\<parallel>x\<parallel>)^2 + 2*(1/4) * (\<parallel>y\<parallel>)^2\<close>
    by auto
  also have \<open>... = (1/2) * (\<parallel>x\<parallel>)^2 + (1/2) * (\<parallel>y\<parallel>)^2\<close>
    by auto
  also have \<open>... = (1/2) * ( (\<parallel>x\<parallel>)^2 + (\<parallel>y\<parallel>)^2 )\<close>
    by auto
  finally have \<open>(\<parallel>(1 / 2) *\<^sub>C x + (1 / 2) *\<^sub>C y\<parallel>)\<^sup>2 + (\<parallel>(1 / 2) *\<^sub>C x - (1 / 2) *\<^sub>C y\<parallel>)\<^sup>2
                   = 1 / 2 * ((\<parallel>x\<parallel>)\<^sup>2 + (\<parallel>y\<parallel>)\<^sup>2)\<close>
    by blast
  thus ?thesis 
    by (metis add_diff_cancel_left')
qed


theorem PythagoreanId:
  \<open>x \<cdot> y = 0 \<Longrightarrow> (\<parallel> x + y \<parallel>)^2 = (\<parallel> x \<parallel>)^2 + (\<parallel> y \<parallel>)^2\<close> 
  (* Reference: In the proof of  Theorem 2.2 in conway2013course *)
  by (simp add: polarization_identity_plus)


subsection \<open>Orthogonality\<close>

definition "is_orthogonal x y = (\<langle> x | y \<rangle> = 0)"

abbreviation is_orthogonal_abbr::"'a::complex_inner \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<bottom>" 50)
  where \<open>x \<bottom> y \<equiv> is_orthogonal x y\<close>

definition "orthogonal_complement S = {x. \<forall>y\<in>S. x \<bottom> y}" 

abbreviation orthogonal_complement_abbr::"('a::complex_inner) set \<Rightarrow> ('a::complex_inner) set" ("_\<^sub>\<bottom>")
  where \<open>M\<^sub>\<bottom> \<equiv> (orthogonal_complement M)\<close>

lemma orthogonal_comm: "(\<psi> \<bottom> \<phi>) = (\<phi> \<bottom> \<psi>)"
  unfolding is_orthogonal_def apply (subst cinner_commute) by blast

locale is_general_subspace =
  fixes A::"('a::complex_vector) set"
  assumes additive_closed: "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x+y\<in>A"
  assumes smult_closed: "x\<in>A \<Longrightarrow> c *\<^sub>C x \<in> A"
  assumes zero: "0 \<in> A"

abbreviation is_general_subspace_abbr::"('a::complex_vector) set \<Rightarrow>  bool" ("_ is-a-subspace")
  where \<open>M is-a-subspace \<equiv> is_general_subspace M\<close>

abbreviation is_closed_abbr::"('a::topological_space) set \<Rightarrow> bool" ("_ is-closed")
  where \<open>M is-closed \<equiv> closed M\<close>

locale is_subspace =
  fixes A::"('a::{complex_vector,topological_space}) set"
  assumes subspace: "A is-a-subspace"
  assumes closed: "A is-closed"

abbreviation is_subspace_abbr::"('a::{complex_vector,topological_space}) set \<Rightarrow>  bool" ("_ is-a-closed-subspace")
  where \<open>M is-a-closed-subspace \<equiv> is_subspace M\<close>

lemma is_subspace_closure:
  fixes A::"('a::complex_inner) set"
  assumes \<open>A is-a-subspace\<close>
  shows \<open>(closure A) is-a-subspace\<close>
proof-
  have "x\<in>(closure A) \<Longrightarrow> y\<in>(closure A) \<Longrightarrow> x+y\<in>(closure A)" for x y
  proof-
    assume \<open>x\<in>(closure A)\<close>
    then obtain xx where \<open>\<forall> n::nat. xx n \<in> A\<close> and \<open>xx \<longlonglongrightarrow> x\<close>
      using closure_sequential by blast
    assume \<open>y\<in>(closure A)\<close>
    then obtain yy where \<open>\<forall> n::nat. yy n \<in> A\<close> and \<open>yy \<longlonglongrightarrow> y\<close>
      using closure_sequential by blast
    have \<open>\<forall> n::nat. (xx n) + (yy n) \<in> A\<close> 
      by (simp add: \<open>\<forall>n. xx n \<in> A\<close> \<open>\<forall>n. yy n \<in> A\<close> assms is_general_subspace.additive_closed)
    hence  \<open>(\<lambda> n. (xx n) + (yy n)) \<longlonglongrightarrow> x + y\<close> using  \<open>xx \<longlonglongrightarrow> x\<close> \<open>yy \<longlonglongrightarrow> y\<close> 
      by (simp add: tendsto_add)
    thus ?thesis using  \<open>\<forall> n::nat. (xx n) + (yy n) \<in> A\<close>
      by (meson closure_sequential)
  qed
  moreover have "x\<in>(closure A) \<Longrightarrow> c *\<^sub>C x \<in> (closure A)" for x c
  proof-
    assume \<open>x\<in>(closure A)\<close>
    then obtain xx where \<open>\<forall> n::nat. xx n \<in> A\<close> and \<open>xx \<longlonglongrightarrow> x\<close>
      using closure_sequential by blast
    have \<open>\<forall> n::nat. c *\<^sub>C (xx n) \<in> A\<close> 
      by (simp add: \<open>\<forall>n. xx n \<in> A\<close> assms is_general_subspace.smult_closed)
    have \<open>isCont (\<lambda> t. c *\<^sub>C t) x\<close> 
      using bounded_clinear.bounded_linear bounded_clinear_scaleC_right linear_continuous_at by auto
    hence  \<open>(\<lambda> n. c *\<^sub>C (xx n)) \<longlonglongrightarrow> c *\<^sub>C x\<close> using  \<open>xx \<longlonglongrightarrow> x\<close>
      by (simp add: isCont_tendsto_compose)
    thus ?thesis using  \<open>\<forall> n::nat. c *\<^sub>C (xx n) \<in> A\<close> 
      by (meson closure_sequential)
  qed
  moreover have "0 \<in> (closure A)"
    using assms closure_subset is_general_subspace.zero by fastforce
  ultimately show ?thesis 
    by (simp add: is_general_subspace_def)
qed

lemma is_subspace_plus:
  assumes \<open>A is-a-subspace\<close> and \<open>B is-a-subspace\<close>
  shows \<open>{\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B} is-a-subspace\<close>
proof-
  obtain C where \<open>C = {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}\<close>
    by blast
  have  "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> x+y\<in>C" for x y
  proof-
    assume \<open>x \<in> C\<close>
    then obtain xA xB where \<open>x = xA + xB\<close> and \<open>xA \<in> A\<close> and \<open>xB \<in> B\<close>
      using \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> by blast
    assume \<open>y \<in> C\<close>
    then obtain yA yB where \<open>y = yA + yB\<close> and \<open>yA \<in> A\<close> and \<open>yB \<in> B\<close>
      using \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> by blast
    have \<open>x + y = (xA + yA) +  (xB + yB)\<close>
      by (simp add: \<open>x = xA + xB\<close> \<open>y = yA + yB\<close>)
    moreover have \<open>xA + yA \<in> A\<close> 
      by (simp add: \<open>xA \<in> A\<close> \<open>yA \<in> A\<close> assms(1) is_general_subspace.additive_closed)
    moreover have \<open>xB + yB \<in> B\<close>
      by (simp add: \<open>xB \<in> B\<close> \<open>yB \<in> B\<close> assms(2) is_general_subspace.additive_closed)
    ultimately show ?thesis
      using \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> by blast
  qed
  moreover have "x\<in>C \<Longrightarrow> c *\<^sub>C x \<in> C" for x c
  proof-
    assume \<open>x \<in> C\<close>
    then obtain xA xB where \<open>x = xA + xB\<close> and \<open>xA \<in> A\<close> and \<open>xB \<in> B\<close>
      using \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> by blast
    have \<open>c *\<^sub>C x = (c *\<^sub>C xA) + (c *\<^sub>C xB)\<close>
      by (simp add: \<open>x = xA + xB\<close> scaleC_add_right)
    moreover have \<open>c *\<^sub>C xA \<in> A\<close>
      by (simp add: \<open>xA \<in> A\<close> assms(1) is_general_subspace.smult_closed)
    moreover have \<open>c *\<^sub>C xB \<in> B\<close>
      by (simp add: \<open>xB \<in> B\<close> assms(2) is_general_subspace.smult_closed)
    ultimately show ?thesis
      using \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> by blast
  qed
  moreover have  "0 \<in> C"
    by (metis (mono_tags, lifting) \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> add.inverse_neutral add_uminus_conv_diff assms(1) assms(2) diff_0 is_general_subspace.zero mem_Collect_eq)
  ultimately show ?thesis
    by (simp add: \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> is_general_subspace_def)
qed


lemma is_subspace_0[simp]: 
"({0} :: ('a::{complex_vector,t1_space}) set)  is-a-closed-subspace"
proof-
  have \<open>{0} is-a-subspace\<close>
    using add.right_neutral is_general_subspace_def scaleC_right.zero by blast
  moreover have "({0} :: ('a::{complex_vector,t1_space}) set)  is-closed"
    by simp 
  ultimately show ?thesis 
    by (simp add: is_subspace_def)
qed

lemma is_subspace_UNIV[simp]: "(UNIV::('a::{complex_vector,topological_space}) set) is-a-closed-subspace"
proof-
  have \<open>UNIV is-a-subspace\<close>
    by (simp add: is_general_subspace_def)
  moreover have \<open>UNIV is-closed\<close>
    by simp
  ultimately show ?thesis by (simp add: is_subspace_def)
qed

lemma is_subspace_inter[simp]:
  assumes "A is-a-closed-subspace" and "B is-a-closed-subspace"
  shows "(A\<inter>B) is-a-closed-subspace"
proof-
  obtain C where \<open>C = A \<inter> B\<close> by blast
  have \<open>C is-a-subspace\<close>
  proof-
    have "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> x+y\<in>C" for x y
      by (metis IntD1 IntD2 IntI \<open>C = A \<inter> B\<close> assms(1) assms(2) is_general_subspace_def is_subspace_def)
    moreover have "x\<in>C \<Longrightarrow> c *\<^sub>C x \<in> C" for x c
      by (metis IntD1 IntD2 IntI \<open>C = A \<inter> B\<close> assms(1) assms(2) is_general_subspace_def is_subspace_def)
    moreover have "0 \<in> C" 
    using  \<open>C = A \<inter> B\<close> assms(1) assms(2) is_general_subspace_def is_subspace_def by fastforce
    ultimately show ?thesis 
      by (simp add: is_general_subspace_def)
  qed
  moreover have \<open>C is-closed\<close>
    using  \<open>C = A \<inter> B\<close>
    by (simp add: assms(1) assms(2) closed_Int is_subspace.closed)
  ultimately show ?thesis
    using  \<open>C = A \<inter> B\<close>
    by (simp add: is_subspace_def)
qed


lemma is_subspace_INF[simp]:
"\<forall> A \<in> \<A>. (A is-a-closed-subspace) \<Longrightarrow> (\<Inter>\<A>) is-a-closed-subspace"
proof-
  assume \<open>\<forall> A \<in> \<A>. (A is-a-closed-subspace)\<close>
  have \<open>(\<Inter>\<A>) is-a-subspace\<close>
    by (smt Inter_iff \<open>Ball \<A> is_subspace_abbr\<close> is_general_subspace.additive_closed is_general_subspace.intro is_general_subspace.smult_closed is_general_subspace.zero is_subspace_def)
  moreover have \<open>(\<Inter>\<A>) is-closed\<close>
    by (simp add: \<open>Ball \<A> is_subspace_abbr\<close> closed_Inter is_subspace.closed)
  ultimately show ?thesis 
    by (simp add: is_subspace.intro)
qed

lemma is_subspace_orthog[simp]: "A is-a-closed-subspace \<Longrightarrow> (A\<^sub>\<bottom>) is-a-closed-subspace"
  for A :: \<open>('a::complex_inner) set\<close>
proof-
  assume \<open>A is-a-closed-subspace\<close>
  have  "x\<in>(A\<^sub>\<bottom>) \<Longrightarrow> y\<in>(A\<^sub>\<bottom>) \<Longrightarrow> x+y\<in>(A\<^sub>\<bottom>)" for x y
  proof-
    assume \<open>x\<in>(A\<^sub>\<bottom>)\<close>
    assume \<open>y\<in>(A\<^sub>\<bottom>)\<close>
    hence  \<open>\<forall> z \<in> A. \<langle> z | y \<rangle> = 0\<close> 
      using is_orthogonal_def orthogonal_comm orthogonal_complement_def by fastforce
    moreover have   \<open>\<forall> z \<in> A. \<langle> z | x \<rangle> = 0\<close> using  \<open>x\<in>(A\<^sub>\<bottom>)\<close>
      using is_orthogonal_def orthogonal_comm orthogonal_complement_def by fastforce
    ultimately have \<open>\<forall> z \<in> A. \<langle> z | x \<rangle> +  \<langle> z | y \<rangle> = 0\<close>
      by simp
    hence  \<open>\<forall> z \<in> A. \<langle> z | x + y \<rangle> = 0\<close> 
      by (simp add: cinner_right_distrib)
    thus ?thesis 
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
  qed
  moreover have "x\<in>(A\<^sub>\<bottom>) \<Longrightarrow> c *\<^sub>C x \<in> (A\<^sub>\<bottom>)" for x c
  proof-
    assume \<open>x \<in> (A\<^sub>\<bottom>)\<close>
    hence \<open>\<forall> y \<in> A. \<langle> y | x \<rangle> = 0\<close>
      using is_orthogonal_def orthogonal_comm orthogonal_complement_def by fastforce
    hence \<open>\<forall> y \<in> A. c*\<langle> y | x \<rangle> = 0\<close>
      by simp
    hence \<open>\<forall> y \<in> A. \<langle> y | c *\<^sub>C x \<rangle> = 0\<close>
      by simp
    thus ?thesis 
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
  qed
  moreover have  "(A\<^sub>\<bottom>) is-closed"
  proof-
    have \<open>\<lbrakk>(\<forall> n::nat. x n \<in> (A\<^sub>\<bottom>)); x \<longlonglongrightarrow> l \<rbrakk> \<Longrightarrow> l \<in> (A\<^sub>\<bottom>)\<close> for x::\<open>nat \<Rightarrow> ('a::complex_inner)\<close> and l::\<open>('a::complex_inner)\<close>
    proof-
      assume \<open>\<forall> n::nat. x n \<in> (A\<^sub>\<bottom>)\<close>
      hence \<open>\<forall> y \<in> A. \<forall> n. \<langle> y | x n \<rangle> = 0\<close>
        by (metis (no_types, lifting) cinner_commute complex_cnj_zero_iff is_orthogonal_def mem_Collect_eq orthogonal_complement_def)
      assume \<open>x \<longlonglongrightarrow> l\<close>
      moreover have \<open>isCont (\<lambda> x. \<langle> y | x \<rangle>) l\<close> for y
      proof-
        have \<open>bounded_clinear (\<lambda> x. \<langle> y | x \<rangle>)\<close> 
          by (simp add: bounded_clinear_cinner_right)
        thus ?thesis
          by simp
      qed
      ultimately have \<open>(\<lambda> n. (\<lambda> v. \<langle> y | v \<rangle>) (x n)) \<longlonglongrightarrow> (\<lambda> v. \<langle> y | v \<rangle>) l\<close> for y
        using isCont_tendsto_compose by fastforce
      hence  \<open>\<forall> y\<in>A. (\<lambda> n. \<langle> y | x n \<rangle>  ) \<longlonglongrightarrow>  \<langle> y | l \<rangle>\<close>
        by simp
      hence  \<open>\<forall> y\<in>A. (\<lambda> n. 0  ) \<longlonglongrightarrow>  \<langle> y | l \<rangle>\<close> 
        using \<open>\<forall> y \<in> A. \<forall> n. \<langle> y | x n \<rangle> = 0\<close> 
        by fastforce
      hence  \<open>\<forall> y \<in> A. \<langle> y | l \<rangle> = 0\<close> 
        using limI by fastforce
      thus ?thesis 
        by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    qed
    thus ?thesis 
      using closed_sequential_limits by blast
  qed
  moreover have  "0 \<in> (A\<^sub>\<bottom>)"
    by (simp add: is_orthogonal_def orthogonal_complement_def)
  ultimately show ?thesis 
    by (simp add: is_general_subspace.intro is_subspace_def)
qed

subsection {* Minimum distance *}

definition is_arg_min_on :: \<open>('a \<Rightarrow> 'b :: ord) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>is_arg_min_on f M x = (is_arg_min f (\<lambda> t. t \<in> M) x)\<close>


lemma ExistenceUniquenessMinNorm:
  fixes M :: \<open>('a::{complex_inner, complete_space}) set\<close>  
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>! k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) M k\<close>
(*
It is not possible to generalize to Banach spaces, at least in the obvious way, the results from 
Conway's book, in which the parallelogram law is involved, because a Banach space in which this 
identity holds is automatically a Hilbert space.
*)

proof-
  have \<open>\<exists> k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) M k\<close>
  proof-
    have \<open>\<exists> k. is_arg_min_on (\<lambda> x. (\<parallel>x\<parallel>)^2) M k\<close>
    proof-
      obtain d where \<open>d = Inf { (\<parallel>x\<parallel>)^2 | x. x \<in> M }\<close>
        by blast
      have \<open>{ (\<parallel>x\<parallel>)^2 | x. x \<in> M } \<noteq> {}\<close>
        by (simp add: assms(3))
      have \<open>\<forall> x. (\<parallel>x\<parallel>)^2 \<ge> 0\<close>
        by simp
      hence \<open>bdd_below  { (\<parallel>x\<parallel>)^2 | x. x \<in> M }\<close>
        by fastforce
      have \<open>x \<in> M \<Longrightarrow> d \<le> (\<parallel>x\<parallel>)^2\<close> for x
      proof -
        assume a1: "x \<in> M"
        have "\<forall>v. (\<exists>va. Re (\<langle>v | v\<rangle> ) = (\<parallel>va\<parallel>)\<^sup>2 \<and> va \<in> M) \<or> v \<notin> M"
          by (metis (no_types) Re_complex_of_real power2_norm_eq_cinner')
        then have "Re (\<langle>x | x\<rangle> ) \<in> {(\<parallel>v\<parallel>)\<^sup>2 |v. v \<in> M}"
          using a1 by blast
        then show ?thesis
          by (metis (lifting) Re_complex_of_real \<open>bdd_below {(\<parallel>x\<parallel>)\<^sup>2 |x. x \<in> M}\<close> \<open>d = Inf {(\<parallel>x\<parallel>)\<^sup>2 |x. x \<in> M}\<close> cInf_lower power2_norm_eq_cinner')
      qed
      have  \<open>\<forall> n::nat. \<exists> x \<in> M.  (\<parallel>x\<parallel>)^2 < d + 1/(n+1)\<close>
      proof-
        have \<open>\<forall> \<epsilon> > 0. \<exists> t \<in> { (\<parallel>x\<parallel>)^2 | x. x \<in> M }.  t < d + \<epsilon>\<close>
          using \<open>d = Inf { (\<parallel>x\<parallel>)^2 | x. x \<in> M }\<close>  \<open>{ (\<parallel>x\<parallel>)^2 | x. x \<in> M } \<noteq> {}\<close>  \<open>bdd_below  { (\<parallel>x\<parallel>)^2 | x. x \<in> M }\<close>
          by (meson cInf_lessD less_add_same_cancel1)
        hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  (\<parallel>x\<parallel>)^2 < d + \<epsilon>\<close>
          by auto    
        hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  (\<parallel>x\<parallel>)^2 < d + \<epsilon>\<close>
          by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> (\<parallel>x\<parallel>)\<^sup>2\<close>)
        thus ?thesis by auto
      qed
      then obtain r::\<open>nat \<Rightarrow> 'a::{complex_inner, complete_space}\<close> where \<open>\<forall> n. r n \<in> M \<and>  (\<parallel> r n \<parallel>)^2 < d + 1/(n+1)\<close>
        by metis
      have \<open>\<forall> n. r n \<in> M\<close> 
        by (simp add: \<open>\<forall>n. r n \<in> M \<and>  (\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / (real n + 1)\<close>)
      have \<open>\<forall> n. (\<parallel> r n \<parallel>)^2 < d + 1/(n+1)\<close>
        by (simp add: \<open>\<forall>n. r n \<in> M \<and> (\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / (real n + 1)\<close>)    
      have \<open>(\<parallel> (r n) - (r m) \<parallel>)^2 < 2*(1/(n+1) + 1/(m+1))\<close> for m n 
      proof-
        have \<open> (\<parallel> r n \<parallel>)^2 < d + 1/(n+1)\<close>
          by (metis \<open>\<forall>n. r n \<in> M \<and> (\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / (real n + 1)\<close>  of_nat_1 of_nat_add)
        have \<open> (\<parallel> r m \<parallel>)^2 < d + 1/(m+1)\<close>
          by (metis \<open>\<forall>n. r n \<in> M \<and> (\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / (real n + 1)\<close>  of_nat_1 of_nat_add)
        have \<open>(r n) \<in> M\<close> 
          by (simp add: \<open>\<forall>n. r n \<in> M\<close>)
        moreover have \<open>(r m) \<in> M\<close> 
          by (simp add: \<open>\<forall>n. r n \<in> M\<close>)
        ultimately have \<open>(1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<in> M\<close>
          using \<open>convex M\<close> 
          by (simp add: convexD)
        hence \<open> (\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>)^2 \<ge> d\<close>
          by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> (\<parallel>x\<parallel>)\<^sup>2\<close>)
        have \<open>(\<parallel> (1/2) *\<^sub>R (r n) - (1/2) *\<^sub>R (r m) \<parallel>)^2
              = (1/2)*( (\<parallel> r n \<parallel>)^2 + (\<parallel> r m \<parallel>)^2 ) - (\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>)^2\<close> 
          using  ParallelogramLawVersion1 
          by (simp add: ParallelogramLawVersion1 scaleR_scaleC)
        also have  \<open>...  
              < (1/2)*( d + 1/(n+1) + (\<parallel> r m \<parallel>)^2 ) - (\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>)^2\<close>
          using \<open>(\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / real (n + 1)\<close> by auto
        also have  \<open>...  
              < (1/2)*( d + 1/(n+1) + d + 1/(m+1) ) - (\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>)^2\<close>
          using \<open>(\<parallel>r m\<parallel>)\<^sup>2 < d + 1 / real (m + 1)\<close> by auto
        also have  \<open>...  
              \<le> (1/2)*( d + 1/(n+1) + d + 1/(m+1) ) - d\<close>
          by (simp add: \<open>d \<le> (\<parallel>(1 / 2) *\<^sub>R r n + (1 / 2) *\<^sub>R r m\<parallel>)\<^sup>2\<close>)
        also have  \<open>...  
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) + 2*d ) - d\<close>
          by simp
        also have  \<open>...  
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) ) + (1/2)*(2*d) - d\<close>
          by (simp add: distrib_left)
        also have  \<open>...  
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) ) + d - d\<close>
          by simp
        also have  \<open>...  
              \<le> (1/2)*( 1/(n+1) + 1/(m+1) )\<close>
          by simp
        finally have \<open> (\<parallel>(1 / 2) *\<^sub>R r n - (1 / 2) *\<^sub>R r m\<parallel>)\<^sup>2 < 1 / 2 * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by blast
        hence \<open> (\<parallel>(1 / 2) *\<^sub>R (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by (simp add: scale_right_diff_distrib)
        hence \<open> ((1 / 2)*(\<parallel> (r n - r m) \<parallel>))\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by simp
        hence \<open> (1 / 2)^2*((\<parallel> (r n - r m) \<parallel>))\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by (metis power_mult_distrib)
        hence \<open> (1 / 4) *((\<parallel> (r n - r m) \<parallel>))\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by (simp add: power_divide)
        hence \<open> (\<parallel> (r n - r m) \<parallel>)\<^sup>2 < 2 * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by simp
        thus ?thesis 
          by (metis of_nat_1 of_nat_add)
      qed
      hence  \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> (\<parallel> (r n) - (r m) \<parallel>)^2 < \<epsilon>^2\<close> for \<epsilon>
      proof-
        assume \<open>\<epsilon> > 0\<close>
        obtain N::nat where \<open>1/(N + 1) < \<epsilon>^2/4\<close>
          using LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1]
          by (metis Suc_eq_plus1 \<open>0 < \<epsilon>\<close> nat_approx_posE zero_less_divide_iff zero_less_numeral zero_less_power )
        hence \<open>4/(N + 1) < \<epsilon>^2\<close>
          by simp
        have \<open>n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> 2*(1/(n+1) + 1/(m+1)) < \<epsilon>^2\<close> for m n::nat
        proof-
          assume \<open>n \<ge> N\<close>
          hence \<open>1/(n+1) \<le> 1/(N+1)\<close> 
            by (simp add: linordered_field_class.frac_le)
          assume \<open>m \<ge> N\<close>
          hence \<open>1/(m+1) \<le> 1/(N+1)\<close> 
            by (simp add: linordered_field_class.frac_le)
          have  \<open>2*(1/(n+1) + 1/(m+1)) \<le> 4/(N+1)\<close>
            using  \<open>1/(n+1) \<le> 1/(N+1)\<close>  \<open>1/(m+1) \<le> 1/(N+1)\<close>
            by simp
          thus ?thesis using \<open>4/(N + 1) < \<epsilon>^2\<close> 
            by linarith
        qed
        hence \<open> n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> (\<parallel> (r n) - (r m) \<parallel>)^2 < \<epsilon>^2\<close> for m n::nat
          by (smt \<open>\<And>n m. (\<parallel>r n - r m\<parallel>)\<^sup>2 < 2 * (1 / (real n + 1) + 1 / (real m + 1))\<close> of_nat_1 of_nat_add)
        thus ?thesis 
          by blast
      qed
      hence  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> (\<parallel> (r n) - (r m) \<parallel>)^2 < \<epsilon>^2\<close>
        by blast
      hence  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> (\<parallel> (r n) - (r m) \<parallel>) < \<epsilon>\<close>
        by (meson less_eq_real_def power_less_imp_less_base)
      hence \<open>Cauchy r\<close>
        using CauchyI by fastforce
      then obtain k where \<open>r \<longlonglongrightarrow> k\<close>
        using  convergent_eq_Cauchy by auto
      have \<open>k \<in> M\<close> using \<open>closed M\<close>
        using \<open>\<forall>n. r n \<in> M\<close> \<open>r \<longlonglongrightarrow> k\<close> closed_sequentially by auto
      have  \<open>(\<lambda> n.  (\<parallel> r n \<parallel>)^2) \<longlonglongrightarrow>  (\<parallel> k \<parallel>)^2\<close>
        by (simp add: \<open>r \<longlonglongrightarrow> k\<close> tendsto_norm tendsto_power)
      moreover  have  \<open>(\<lambda> n.  (\<parallel> r n \<parallel>)^2) \<longlonglongrightarrow>  d\<close>
      proof-
        have \<open>\<bar>(\<parallel> r n \<parallel>)^2 - d\<bar> < 1/(n+1)\<close> for n :: nat
          by (smt \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> (\<parallel>x\<parallel>)\<^sup>2\<close> \<open>\<forall>n. r n \<in> M \<and> (\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / (real n + 1)\<close> of_nat_1 of_nat_add)
        moreover have \<open>(\<lambda>n. 1 / real (n + 1)) \<longlonglongrightarrow> 0\<close> 
          using  LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1] by blast        
        ultimately have \<open>(\<lambda> n. \<bar>(\<parallel> r n \<parallel>)^2 - d\<bar> ) \<longlonglongrightarrow> 0\<close> 
          by (simp add: LIMSEQ_norm_0)
        hence \<open>(\<lambda> n. (\<parallel> r n \<parallel>)^2 - d ) \<longlonglongrightarrow> 0\<close> 
          by (simp add: tendsto_rabs_zero_iff)
        moreover have \<open>(\<lambda> n. d ) \<longlonglongrightarrow> d\<close>
          by simp
        ultimately have \<open>(\<lambda> n. ((\<parallel> r n \<parallel>)^2 - d)+d ) \<longlonglongrightarrow> 0+d\<close> 
          using tendsto_add by fastforce
        thus ?thesis by simp
      qed
      ultimately have \<open>d = (\<parallel> k \<parallel>)^2\<close>
        using LIMSEQ_unique by auto
      hence \<open>t \<in> M \<Longrightarrow> (\<parallel> k \<parallel>)^2 \<le> (\<parallel> t \<parallel>)^2\<close> for t
        using \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> (\<parallel>x\<parallel>)\<^sup>2\<close> by auto
      thus ?thesis using \<open>k \<in> M\<close>
        unfolding is_arg_min_on_def
        using is_arg_min_def \<open>d = (\<parallel>k\<parallel>)\<^sup>2\<close>
        by smt
    qed

    thus ?thesis 
      unfolding is_arg_min_on_def
      by (smt is_arg_min_def norm_ge_zero power2_eq_square power2_le_imp_le)
  qed
  moreover have \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r \<Longrightarrow> is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s \<Longrightarrow> r = s\<close> for r s
  proof-
    assume \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close>
    assume \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>
    have \<open>(\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>)^2
      = (1/2)*( (\<parallel>r\<parallel>)^2 + (\<parallel>s\<parallel>)^2 ) - (\<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>)^2\<close> 
      using  ParallelogramLawVersion1 
      by (simp add: ParallelogramLawVersion1 scaleR_scaleC)
    moreover have \<open>(\<parallel>r\<parallel>)^2 \<le> (\<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>)^2\<close>
    proof-
      have \<open>r \<in> M\<close> 
        using \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close>
        by (simp add: is_arg_min_def is_arg_min_on_def)
      moreover have \<open>s \<in> M\<close> 
        using \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>
        by (simp add: is_arg_min_def is_arg_min_on_def)
      ultimately have \<open>((1/2) *\<^sub>R r + (1/2) *\<^sub>R s) \<in> M\<close> using \<open>convex M\<close>
        by (simp add: convexD)
      hence \<open> (\<parallel>r\<parallel>) \<le> (\<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>)\<close>
        using  \<open>is_arg_min_on norm_abbr M r\<close>
        unfolding is_arg_min_on_def
        by (smt is_arg_min_def)
      thus ?thesis
        using norm_ge_zero power_mono by blast
    qed
    moreover have \<open>(\<parallel>r\<parallel>) = (\<parallel>s\<parallel>)\<close>
    proof-
      have \<open>(\<parallel>r\<parallel>) \<le> (\<parallel>s\<parallel>)\<close> 
        using  \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close> \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>  is_arg_min_def 
        unfolding is_arg_min_on_def
        by smt

      moreover have \<open>(\<parallel>s\<parallel>) \<le> (\<parallel>r\<parallel>)\<close>
        using  \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close> \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>  is_arg_min_def 
        unfolding is_arg_min_on_def
        by smt

      ultimately show ?thesis by simp
    qed
    ultimately have \<open>(\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>)^2 \<le> 0\<close>
      by simp
    hence \<open>(\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>)^2 = 0\<close>
      by simp
    hence \<open>(\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>) = 0\<close>
      by auto
    hence \<open>(1/2) *\<^sub>R r - (1/2) *\<^sub>R s = 0\<close>
      using norm_eq_zero by blast
    thus ?thesis by simp
  qed
  ultimately show ?thesis 
    by auto
qed

(* Connected.closed_translation shows the same thing, but only for 'a::real_normed_vector *)
lemma TransClosed:
  \<open>closed (S::('a::{topological_ab_group_add,t2_space,first_countable_topology}) set) \<Longrightarrow> closed {s + h| s. s \<in> S}\<close>
proof-
  assume \<open>closed S\<close>
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. r n \<in> S) \<longrightarrow> lim r \<in> S\<close>
    using closed_sequentially convergent_LIMSEQ_iff by blast
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. r n \<in>  {s | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n)) \<in>  {s | s. s \<in> S}\<close>
    by simp
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n) \<in>  {s | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+h \<in>  {s+h | s. s \<in> S}\<close>
    by blast
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+h \<in>  {s+h | s. s \<in> S}\<close>
    by simp
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+lim (\<lambda> n. h) \<in>  {s+h | s. s \<in> S}\<close>
    by auto
  have \<open>convergent r \<Longrightarrow>  (lim r) + h = lim (\<lambda> n. (r n)+h)\<close> for r::\<open>nat \<Rightarrow> 'a\<close>
  proof-
    assume \<open>convergent r\<close>
    then obtain R where \<open>r \<longlonglongrightarrow> R\<close>
      using convergent_def by auto
    have \<open>(\<lambda> n. h) \<longlonglongrightarrow> h\<close>
      by simp
    have \<open>(\<lambda> n. (r n)+h) \<longlonglongrightarrow> R + h\<close>  
      using  \<open>r \<longlonglongrightarrow> R\<close>  \<open>(\<lambda> n. h) \<longlonglongrightarrow> h\<close> tendsto_add
      by fastforce
    thus ?thesis 
      by (metis \<open>r \<longlonglongrightarrow> R\<close> limI)
  qed
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n)+h) \<in>  {s+h | s. s \<in> S}\<close>
    using  \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+lim (\<lambda> n. h) \<in> {s+h | s. s \<in> S}\<close>
      add_diff_cancel_left' by auto
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent (\<lambda> n. (r n)+h) \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n)+h) \<in> {s+h | s. s \<in> S}\<close>
    using convergent_add_const_right_iff by blast
  have \<open> \<forall>r. convergent (\<lambda>n. r n + (h::'a)) \<and> (\<forall>n. r n \<in> S)
 \<longrightarrow> (\<exists>s. lim (\<lambda>n. r n + h) = s + h \<and> s \<in> S)
 \<Longrightarrow>   convergent t \<Longrightarrow> \<forall>n. \<exists>s. t n = s + h \<and> s \<in> S \<Longrightarrow> \<exists>s. lim t = s + h \<and> s \<in> S \<close> for t
  proof-
    assume \<open> \<forall>r. convergent (\<lambda>n. r n + h) \<and> (\<forall>n. r n \<in> S) \<longrightarrow> (\<exists>s. lim (\<lambda>n. r n + h) = s + h \<and> s \<in> S) \<close>
    assume \<open>convergent t\<close>
    assume \<open>\<forall>n. \<exists>s. t n = s + h \<and> s \<in> S\<close>
    obtain r::\<open>nat \<Rightarrow> 'a\<close> where \<open>\<forall>n. t n = (r n) + h \<and> r n \<in> S\<close> using  \<open>\<forall>n. \<exists>s. t n = s + h \<and> s \<in> S\<close>
      by metis
    from  \<open>\<forall>n. t n = (r n) + h \<and> r n \<in> S\<close>
    have  \<open>\<forall>n. t n = (r n) + h\<close> by simp
    from  \<open>\<forall>n. t n = (r n) + h \<and> r n \<in> S\<close>
    have  \<open>\<forall>n. r n \<in> S\<close> by simp
    have \<open> convergent (\<lambda>n. t n) \<close> using  \<open>convergent t\<close> by blast
    hence \<open> convergent (\<lambda>n. (r n) + h) \<close> using   \<open>\<forall>n. t n = (r n) + h\<close> 
      by simp
    have \<open>\<exists>s. lim (\<lambda>n. r n + h) = s + h \<and> s \<in> S\<close> 
      using \<open>\<forall>n. t n = r n + h \<and> r n \<in> S\<close> \<open>\<forall>r. convergent (\<lambda>n. r n + h) \<and> (\<forall>n. r n \<in> S) \<longrightarrow> (\<exists>s. lim (\<lambda>n. r n + h) = s + h \<and> s \<in> S)\<close> \<open>convergent (\<lambda>n. r n + h)\<close> by auto
    hence \<open>\<exists>s. lim (\<lambda>n. t n) = s + h \<and> s \<in> S\<close> using  \<open>\<forall>n. t n = (r n) + h\<close> by simp
    hence \<open>\<exists>s. lim t = s + h \<and> s \<in> S\<close> by simp
    thus ?thesis by blast
  qed
  hence \<open>\<forall> t::nat \<Rightarrow> 'a. convergent (\<lambda> n. t n) \<and> (\<forall> n::nat. t n \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. t n) \<in> {s+h | s. s \<in> S}\<close>
    using \<open>\<forall>r. convergent (\<lambda>n. r n + h) \<and> (\<forall>n. r n + h \<in> {s + h |s. s \<in> S}) \<longrightarrow> lim (\<lambda>n. r n + h) \<in> {s + h |s. s \<in> S}\<close> by auto   
  hence \<open>\<forall> t::nat \<Rightarrow> 'a. convergent t \<and> (\<forall> n::nat. t n \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim t \<in> {s+h | s. s \<in> S}\<close>
    by simp
  thus ?thesis unfolding convergent_LIMSEQ_iff 
    by (metis (no_types, lifting) closed_sequential_limits limI)
qed


theorem ExistenceUniquenessMinDist:
  fixes M :: \<open>('a::{complex_inner, complete_space}) set\<close> and h :: 'a 
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>! k. is_arg_min_on (\<lambda> x. dist x h) M k\<close>
    (* Reference: Theorem 2.5 in conway2013course *)
proof-
  have \<open>{m - h| m. m \<in> M} \<noteq> {}\<close>
    by (simp add: assms(3))
  moreover have \<open>closed {m - h| m. m \<in> M}\<close>
  proof-
    have \<open>closed {m + (- h)| m. m \<in> M}\<close>
      using  \<open>closed M\<close> TransClosed by blast
    thus ?thesis by simp
  qed
  moreover have \<open>convex {m - h| m. m \<in> M}\<close>
  proof-
    have \<open>convex ((\<lambda>x. -h + x) ` M)\<close>
      using convex_translation \<open>convex M\<close> by blast
    hence \<open>convex ((\<lambda>x.  x - h) ` M)\<close> by simp
    moreover have \<open>{(\<lambda>x.  x - h) m | m. m \<in> M} = ((\<lambda>x.  x - h) ` M)\<close>
      by auto
    ultimately show ?thesis by simp
  qed
  ultimately have \<open>\<exists>! k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h| m. m \<in> M} k\<close>
    by (simp add: ExistenceUniquenessMinNorm)
  have \<open>\<exists>! k. is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M k\<close>
  proof-
    have \<open>\<exists> k. is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M k\<close>
    proof-
      obtain k where \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h| m. m \<in> M} k\<close>
        using  \<open>\<exists>! k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h| m. m \<in> M} k\<close> by blast
      have \<open>(\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k\<parallel>) \<le> (\<parallel>t\<parallel>)) \<and> k \<in> {m - h |m. m \<in> M}\<close>
        using is_arg_min_def  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h| m. m \<in> M} k\<close>
        unfolding is_arg_min_on_def
        by smt

      hence \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k\<parallel>) \<le> (\<parallel>t\<parallel>)\<close>
        by blast
      hence \<open>\<forall>t. t + h \<in> M \<longrightarrow> (\<parallel>k\<parallel>) \<le> (\<parallel>t\<parallel>)\<close>
        by auto
      hence \<open>\<forall>t. t \<in> M \<longrightarrow> (\<parallel>k\<parallel>) \<le> (\<parallel>t - h\<parallel>)\<close>
        by auto
      hence \<open>\<forall>t. t \<in> M \<longrightarrow> (\<parallel>(k+h)-h\<parallel>) \<le> (\<parallel>t - h\<parallel>)\<close>
        by auto
      from \<open>(\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k\<parallel>) \<le> (\<parallel>t\<parallel>)) \<and> k \<in> {m - h |m. m \<in> M}\<close>
      have  \<open>k \<in> {m - h |m. m \<in> M}\<close>
        by blast
      hence  \<open>k + h \<in> M\<close>
        by auto

      have \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) {m| m. m \<in> M} (k + h)\<close>
      proof-
        have \<open>\<nexists>y. y \<in> {m |m. m \<in> M} \<and> \<parallel>y - h\<parallel> < \<parallel>(k + h) - h\<parallel>\<close>
          using \<open>\<forall>t. t \<in> M \<longrightarrow> (\<parallel>(k+h)-h\<parallel>) \<le> (\<parallel>t - h\<parallel>)\<close>  
          by auto
        thus ?thesis
          using \<open>k + h \<in> M\<close>
          unfolding is_arg_min_on_def
          by (simp add: is_arg_min_def)
      qed
      thus ?thesis 
        by auto
    qed 
    moreover have \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  k \<Longrightarrow> is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  t
                    \<Longrightarrow> k = t\<close> for k t
    proof-
      have \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  k \<Longrightarrow> is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h |m. m \<in> M} (k - h)\<close> for k
      proof-
        assume \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  k \<close>
        hence \<open>\<forall>t. t \<in> M \<longrightarrow> (\<parallel>k - h\<parallel>) \<le> (\<parallel>t - h\<parallel>)\<close>
          unfolding is_arg_min_on_def
          by (meson is_arg_min_linorder)

        hence \<open>\<forall>t. t - h \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k - h\<parallel>) \<le> (\<parallel>t - h\<parallel>)\<close>
          by auto
        hence \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k - h\<parallel>) \<le> (\<parallel>t\<parallel>)\<close>
          by blast
        have \<open>k \<in> M\<close>
          using  \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  k \<close>
          unfolding is_arg_min_on_def
          using is_arg_min_def
          by (simp add: is_arg_min_linorder)

        hence \<open>k - h \<in> {m - h |m. m \<in> M}\<close>
          by auto
        have  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h |m. m \<in> M} (k - h)\<close>
          using  \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k - h\<parallel>) \<le> (\<parallel>t\<parallel>)\<close>
            \<open>k - h \<in> {m - h |m. m \<in> M}\<close>
            is_arg_min_def
          unfolding is_arg_min_on_def
          by smt
        thus ?thesis by blast
      qed

      assume \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M k\<close>
      hence  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>)  {m - h |m. m \<in> M} (k - h)\<close>
        by (simp add: \<open>\<And>k. is_arg_min_on (\<lambda>x. \<parallel>x - h\<parallel>) M k \<Longrightarrow> is_arg_min_on norm_abbr {m - h |m. m \<in> M} (k - h)\<close>)

      assume  \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M t\<close> 
      hence  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>)  {m - h |m. m \<in> M} (t - h)\<close>
        using \<open>\<And>k. is_arg_min_on (\<lambda>x. \<parallel>x - h\<parallel>) M k \<Longrightarrow> is_arg_min_on norm_abbr {m - h |m. m \<in> M} (k - h)\<close> by auto

      show ?thesis 
        by (metis (no_types, lifting) \<open>\<exists>!k. is_arg_min_on norm_abbr {m - h |m. m \<in> M} k\<close> \<open>is_arg_min_on norm_abbr {m - h |m. m \<in> M} (k - h)\<close> \<open>is_arg_min_on norm_abbr {m - h |m. m \<in> M} (t - h)\<close> diff_add_cancel)

    qed
    ultimately show ?thesis by blast
  qed
  moreover have \<open>(\<lambda> x. dist x h) = (\<lambda> x. \<parallel>x - h\<parallel>)\<close>
    by (simp add: dist_norm)
  ultimately show ?thesis by simp
qed

theorem DistMinOrtho:
  fixes M :: \<open>('a::{complex_inner, complete_space}) set\<close> and h k::\<open>'a\<close> 
  assumes "M is-a-closed-subspace"
  shows  \<open>(is_arg_min_on (\<lambda> x. dist x h) M k) \<longleftrightarrow> h - k \<in> (M\<^sub>\<bottom>) \<and> k \<in> M\<close>
    (* Reference: Theorem 2.6 in conway2013course *)
proof-
  have \<open>is_arg_min_on (\<lambda> x. dist x h) M k
     \<Longrightarrow>  h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
  proof-
    assume \<open>is_arg_min_on (\<lambda> x. dist x h) M k\<close>
    hence  \<open>k \<in> M\<close>
      unfolding is_arg_min_on_def
      by (simp add: is_arg_min_def)
    moreover have \<open>h - k \<in> orthogonal_complement M\<close>
    proof-
      have \<open>f \<in> M \<Longrightarrow> \<langle> h - k | f \<rangle> = 0\<close> for f
      proof-
        assume \<open>f \<in> M\<close>
        hence  \<open>\<forall> c. c *\<^sub>R f \<in> M\<close>
          by (simp add: assms is_general_subspace.smult_closed is_subspace.subspace scaleR_scaleC)
        have \<open>f \<in> M \<Longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<le> (\<parallel> f \<parallel>)^2\<close> for f
        proof-
          assume \<open>f \<in>  M\<close>             
          hence \<open>k + f \<in>  M\<close> 
            by (simp add: assms calculation is_general_subspace.additive_closed is_subspace.subspace)
          hence \<open>dist h k \<le> dist  h (k + f)\<close>
          proof -
            have "\<forall>f A a aa. \<not> is_arg_min_on f A (a::'a) \<or> (f a::real) \<le> f aa \<or> aa \<notin> A"
              by (metis (no_types) is_arg_min_linorder is_arg_min_on_def)
            then have "dist k h \<le> dist (f + k) h"
              by (metis \<open>is_arg_min_on (\<lambda>x. dist x h) M k\<close> \<open>k + f \<in> M\<close> add.commute)
            then show ?thesis
              by (simp add: add.commute dist_commute)
          qed
          hence \<open>(\<parallel> h - k \<parallel>) \<le> (\<parallel> h - (k + f) \<parallel>)\<close>
            by (simp add: dist_norm)
          hence \<open>(\<parallel> h - k \<parallel>)^2 \<le> (\<parallel> h - (k + f) \<parallel>)^2\<close>
            by (simp add: power_mono)
          also have \<open>... \<le> (\<parallel> (h - k) - f \<parallel>)^2\<close>
            by (simp add: diff_diff_add)
          also have \<open>... \<le> (\<parallel> (h - k) \<parallel>)^2 + (\<parallel> f \<parallel>)^2 -  2 * Re (\<langle> h - k | f \<rangle>)\<close>
            by (simp add: polarization_identity_minus)
          finally have \<open>(\<parallel> (h - k) \<parallel>)^2 \<le> (\<parallel> (h - k) \<parallel>)^2 + (\<parallel> f \<parallel>)^2 -  2 * Re (\<langle> h - k | f \<rangle>)\<close>
            by simp
          thus ?thesis by simp
        qed
        hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<le> (\<parallel> f \<parallel>)^2\<close>
          by blast
        hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (\<langle> h - k | f \<rangle>) = 0\<close>
        proof-
          have \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real.  2 * Re (\<langle> h - k | c *\<^sub>R f \<rangle>) \<le> (\<parallel> c *\<^sub>R f \<parallel>)^2)\<close>
            by (metis \<open>\<And>f. f \<in> M \<Longrightarrow> 2 * Re ((h - k) \<cdot> f) \<le> \<parallel>f\<parallel>\<^sup>2\<close> assms is_general_subspace.smult_closed is_subspace.subspace scaleR_scaleC)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (\<langle> h - k | f \<rangle>)) \<le> (\<parallel> c *\<^sub>R f \<parallel>)^2)\<close>
            by (metis Re_complex_of_real cinner_scaleC_right complex_add_cnj complex_cnj_complex_of_real complex_cnj_mult of_real_mult scaleR_scaleC semiring_normalization_rules(34))
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (\<langle> h - k | f \<rangle>)) \<le> \<bar>c\<bar>^2*(\<parallel> f \<parallel>)^2)\<close>
            by (simp add: power_mult_distrib)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c * (2 * Re (\<langle> h - k | f \<rangle>)) \<le> c^2*(\<parallel> f \<parallel>)^2)\<close>
            by auto
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> c * (2 * Re (\<langle> h - k | f \<rangle>)) \<le> c^2*(\<parallel> f \<parallel>)^2)\<close>
            by simp
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> c*(2 * Re (\<langle> h - k | f \<rangle>)) \<le> c*(c*(\<parallel> f \<parallel>)^2))\<close>
            by (simp add: power2_eq_square)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<le> c*(\<parallel> f \<parallel>)^2)\<close>
            by simp 
          have \<open>f \<in>  M \<Longrightarrow> \<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<le> 0\<close> for f
          proof-
            assume \<open>f \<in>  M\<close> 
            hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k | f \<rangle>) \<le> c*(\<parallel> f \<parallel>)^2\<close>
              by (simp add: \<open>\<forall>f. f \<in> M \<longrightarrow> (\<forall>c>0. 2 * Re \<langle>h - k | f\<rangle> \<le> c * \<parallel>f\<parallel>\<^sup>2)\<close>)
            hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k | f \<rangle>) \<le> c\<close>
            proof (cases \<open>(\<parallel> f \<parallel>)^2 > 0\<close>)
              case True
              hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k | f \<rangle>) \<le> (c/(\<parallel> f \<parallel>)^2)*(\<parallel> f \<parallel>)^2\<close>
                using \<open>\<forall>c>0. 2 * Re (\<langle>h - k | f\<rangle> ) \<le> c * (\<parallel>f\<parallel>)\<^sup>2\<close> linordered_field_class.divide_pos_pos by blast
              then show ?thesis 
                using True by auto
            next
              case False
              hence \<open>(\<parallel> f \<parallel>)^2 = 0\<close> 
                by simp
              then show ?thesis 
                by auto
            qed
            thus ?thesis 
              by smt
          qed
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<le> 0)\<close>
            by simp
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> (2 * Re (\<langle> h - k | (-1) *\<^sub>R f \<rangle>)) \<le> 0)\<close>
            by (metis assms is_general_subspace.smult_closed is_subspace.subspace scaleR_scaleC)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> -(2 * Re (\<langle> h - k | f \<rangle>)) \<le> 0)\<close>
            by simp
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<ge> 0)\<close>
            by simp
          hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) = 0)\<close>
            using  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> (2 * Re (\<langle> h - k | f \<rangle>)) \<le> 0)\<close>
            by fastforce
          hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) = 0\<close>
          proof-
            have \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                 ((1::real) > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) = 0)\<close>
              using \<open>\<forall>f. f \<in>  M \<longrightarrow> (\<forall>c>0. 2 * Re (\<langle>h - k | f\<rangle> ) = 0)\<close> by blast
            thus ?thesis by auto
          qed
          thus ?thesis by simp
        qed
        also have \<open>\<forall> f. f \<in>  M \<longrightarrow> Im (\<langle> h - k | f \<rangle>) = 0\<close>
        proof-
          have  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (\<langle> h - k | (Complex 0 (-1)) *\<^sub>C f \<rangle>) = 0\<close>
            using assms calculation  is_general_subspace.smult_closed is_subspace.subspace by blast
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re ( (Complex 0 (-1))*(\<langle> h - k | f \<rangle>) ) = 0\<close>
            by simp
          thus ?thesis 
            using Complex_eq_neg_1 Re_i_times cinner_scaleC_right complex_of_real_def by auto
        qed
        ultimately have \<open>\<forall> f. f \<in>  M \<longrightarrow> (\<langle> h - k | f \<rangle>) = 0\<close>
          by (simp add: complex_eq_iff)
        thus ?thesis 
          by (simp add: \<open>f \<in>  M\<close>)
      qed
      thus ?thesis 
        by (simp add: is_orthogonal_def orthogonal_complement_def)
    qed
    ultimately show ?thesis 
      by simp
  qed
  also have  \<open>h - k \<in> orthogonal_complement M \<and> k \<in>  M 
     \<Longrightarrow> ( is_arg_min_on (\<lambda> x. dist x h) M k )\<close>
  proof-
    assume \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
    hence \<open>h - k \<in> orthogonal_complement M\<close>
      by blast
    have \<open>k \<in> M\<close> using \<open>h - k \<in> orthogonal_complement M \<and> k \<in>  M\<close>
      by blast
    have \<open>f \<in> M \<Longrightarrow> dist h k \<le> dist h f \<close> for f
    proof-
      assume \<open>f \<in>  M\<close>
      hence \<open>h - k \<bottom> k - f\<close>
        by (smt \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close> cinner_diff_right eq_iff_diff_eq_0 is_orthogonal_def mem_Collect_eq orthogonal_complement_def)
      have \<open>(\<parallel> h - f \<parallel>)^2 = (\<parallel> (h - k) + (k - f) \<parallel>)^2\<close>
        by simp
      also have \<open>... = (\<parallel> h - k \<parallel>)^2 + (\<parallel> k - f \<parallel>)^2\<close>
        using  \<open>h - k \<bottom> k - f\<close> PythagoreanId 
        using is_orthogonal_def by blast
      also have \<open>... \<ge> (\<parallel> h - k \<parallel>)^2\<close>
        by simp
      finally have \<open>(\<parallel>h - k\<parallel>)\<^sup>2 \<le> (\<parallel>h - f\<parallel>)\<^sup>2 \<close>
        by blast
      hence \<open>(\<parallel>h - k\<parallel>) \<le> (\<parallel>h - f\<parallel>)\<close>
        using norm_ge_zero power2_le_imp_le by blast
      thus ?thesis 
        by (simp add: dist_norm)
    qed
    thus ?thesis 
      by (simp add: \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close> dist_commute is_arg_min_linorder is_arg_min_on_def)
  qed
  ultimately show ?thesis by blast
qed

lemma SubspaceConvex:
  \<open>M is-a-closed-subspace \<Longrightarrow> convex M\<close> 
proof-
  assume \<open>is_subspace M\<close>
  hence \<open>\<forall>x\<in>M. \<forall>y\<in> M. \<forall>u. \<forall>v. u *\<^sub>C x + v *\<^sub>C y \<in>  M\<close>
    by (simp add: is_general_subspace.additive_closed is_general_subspace.smult_closed is_subspace.subspace)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u::real. \<forall>v::real. u *\<^sub>R x + v *\<^sub>R y \<in> M\<close>
    by (simp add: scaleR_scaleC)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in>M\<close>
    by blast
  thus ?thesis using convex_def by blast
qed

corollary ExistenceUniquenessProj:
  fixes M :: \<open>('a::{complex_inner, complete_space}) set\<close> 
  assumes \<open>M is-a-closed-subspace\<close>
  shows  \<open>\<forall> h. \<exists>! k. (h - k) \<in> orthogonal_complement M \<and> k \<in> M\<close>
proof-  
  have \<open>0 \<in> M\<close> 
    using  \<open>is_subspace M\<close>
    by (simp add: is_general_subspace.zero is_subspace.subspace)
  hence \<open>M \<noteq> {}\<close> by blast
  have \<open>closed  M\<close>
    using  \<open>is_subspace M\<close>
    by (simp add: is_subspace.closed)
  have \<open>convex  M\<close>
    using  \<open>is_subspace M\<close>
    by (simp add: SubspaceConvex)
  have \<open>\<forall> h. \<exists>! k.  is_arg_min_on (\<lambda> x. dist x h) M k\<close>
    by (simp add: ExistenceUniquenessMinDist \<open>closed M\<close> \<open>convex M\<close> \<open>M \<noteq> {}\<close>)
  thus ?thesis
    using DistMinOrtho 
    by (smt Collect_cong Collect_empty_eq_bot ExistenceUniquenessMinDist \<open>M \<noteq> {}\<close> \<open>closed M\<close> \<open>convex M\<close> assms bot_set_def empty_Collect_eq empty_Diff insert_Diff1 insert_compr  is_subspace_orthog orthogonal_complement_def set_diff_eq singleton_conv2 someI_ex)
qed

(* Definition of projection onto the subspace M *)
definition proj :: \<open>('a::complex_inner) set \<Rightarrow> (('a::complex_inner) \<Rightarrow> ('a::complex_inner))\<close> where (* using 'a::something set, 'a\<Rightarrow>'a *)
  \<open>proj \<equiv> \<lambda> M. \<lambda> h. THE k. ((h - k) \<in> (M\<^sub>\<bottom>) \<and> k \<in>  M)\<close>

lemma proj_intro1:
  \<open>M is-a-closed-subspace  \<Longrightarrow> h - (proj M) h \<in> orthogonal_complement M\<close>
  for M :: \<open>('a::{complex_inner, complete_space}) set\<close>
  by (metis (no_types, lifting) Complex_Inner_Product.proj_def ExistenceUniquenessProj theI)

lemma proj_intro2:
  \<open>M is-a-closed-subspace  \<Longrightarrow> (proj M) h \<in> M\<close>
  for M :: \<open>('a::{complex_inner, complete_space}) set\<close>
  by (metis (no_types, lifting) Complex_Inner_Product.proj_def ExistenceUniquenessProj theI)

lemma proj_uniq:
  fixes  M :: \<open>('a::{complex_inner, complete_space}) set\<close>
  assumes  \<open>M is-a-closed-subspace\<close> and \<open>h - x \<in> orthogonal_complement M\<close> and \<open>x \<in> M\<close>
  shows \<open>(proj M) h = x\<close>
  by (smt ExistenceUniquenessProj add.commute assms(1) assms(2) assms(3) orthogonal_complement_def proj_intro1 proj_intro2 uminus_add_conv_diff)

lemma proj_fixed_points:                         
  \<open>M is-a-closed-subspace  \<Longrightarrow> x \<in> M \<Longrightarrow> (proj M) x = x\<close>
  for M :: \<open>('a::{complex_inner, complete_space}) set\<close>
  by (simp add: is_general_subspace.zero is_subspace.subspace proj_uniq)

lemma bounded_linear_continuous:
  assumes \<open>bounded_clinear f\<close> 
  shows "isCont f x"
  by (simp add: assms bounded_clinear.bounded_linear linear_continuous_at)

theorem projPropertiesB:
  \<open>is_subspace M  \<Longrightarrow> \<parallel> (proj M) h \<parallel> \<le> \<parallel> h \<parallel>\<close>
  for M :: \<open>('a::{complex_inner, complete_space}) set\<close>
  (* Reference: Theorem 2.7 in conway2013course *)
proof-
  assume \<open>is_subspace M\<close>
  hence \<open>h - (proj M) h \<in> orthogonal_complement M\<close> 
    by (simp add: proj_intro1)
  hence \<open>\<forall> k \<in>  M.  (h - (proj M) h) \<bottom> k\<close>
    by (simp add: orthogonal_complement_def)
  hence \<open>\<forall> k \<in> M. \<langle>  h - (proj M) h | k \<rangle> = 0\<close>
    using is_orthogonal_def by blast
  also have \<open>(proj M) h \<in>  M\<close>
    using  \<open>is_subspace M\<close>
    by (simp add: proj_intro2)
  ultimately have \<open>\<langle>  h - (proj M) h | (proj M) h \<rangle> = 0\<close>
    by auto
  hence \<open>(\<parallel> (proj M) h \<parallel>)^2 + (\<parallel> h - (proj M) h \<parallel>)^2 = (\<parallel> h \<parallel>)^2\<close>
    using PythagoreanId by fastforce
  hence \<open>(\<parallel> (proj M) h \<parallel>)^2 \<le> (\<parallel> h \<parallel>)^2\<close>
    by (smt zero_le_power2)    
  thus ?thesis 
    using norm_ge_zero power2_le_imp_le by blast
qed

theorem projPropertiesA:
  \<open>is_subspace M \<Longrightarrow> bounded_clinear (proj M)\<close> 
  for M :: \<open>('a::{complex_inner, complete_space}) set\<close>
  (* Reference: Theorem 2.7 (version) in conway2013course *)
proof-
  assume \<open>is_subspace M\<close>
  hence \<open>is_subspace (orthogonal_complement M)\<close>
    by simp
  have \<open>(proj M) (c *\<^sub>C x) = c *\<^sub>C ((proj M) x)\<close> for x c
  proof-                   
    have  \<open>\<forall> x.  ((proj M) x) \<in> M\<close>
      using  \<open>is_subspace M\<close>
      by (simp add: proj_intro2)
    hence  \<open>\<forall> x. \<forall> t.  t *\<^sub>C ((proj M) x) \<in> M\<close>
      using \<open>M is-a-closed-subspace\<close> is_general_subspace.smult_closed is_subspace.subspace by blast
    have  \<open>\<forall> x. \<forall> t. ((proj M) (t *\<^sub>C x)) \<in>  M\<close>
      using  \<open>is_subspace M\<close>
      by (simp add: proj_intro2)
    have \<open>\<forall> x. \<forall> t. (t *\<^sub>C x) - (proj M) (t *\<^sub>C x) \<in> orthogonal_complement M\<close>
      using  \<open>is_subspace M\<close>
      by (simp add: proj_intro1)
    have \<open>\<forall> x. x - (proj M) x \<in> orthogonal_complement M\<close>
      using  \<open>is_subspace M\<close>
      by (simp add: proj_intro1)
    hence \<open>\<forall> x. \<forall> t. t *\<^sub>C (x - (proj M) x) \<in> orthogonal_complement M\<close>
      by (simp add: \<open>M\<^sub>\<bottom> is-a-closed-subspace\<close> is_general_subspace.smult_closed is_subspace.subspace)
    hence \<open>\<forall> x. \<forall> t.  t *\<^sub>C x - t *\<^sub>C ((proj M) x) \<in> orthogonal_complement M\<close>
      by (simp add: complex_vector.scale_right_diff_distrib)
    from  \<open>\<forall> x. \<forall> t. t *\<^sub>C x - (proj M) (t *\<^sub>C x) \<in> orthogonal_complement M\<close>
      \<open>\<forall> x. \<forall> t.  t *\<^sub>C x - t *\<^sub>C ((proj M) x) \<in> orthogonal_complement M\<close>
    have \<open>\<forall> x. \<forall> t. (t *\<^sub>C x - t *\<^sub>C ((proj M) x)) - (t *\<^sub>C x - (proj M) (t *\<^sub>C x)) \<in> orthogonal_complement M\<close>
      by (metis \<open>M is-a-closed-subspace\<close> \<open>\<forall>x t. t *\<^sub>C proj M x \<in> M\<close> add_diff_cancel_left' diff_add_cancel diff_right_commute proj_fixed_points proj_uniq)

    hence \<open>\<forall> x. \<forall> t. (proj M) (t *\<^sub>C x) - t *\<^sub>C ((proj M) x) \<in> orthogonal_complement M\<close>
      by simp
    moreover have \<open>\<forall> x. \<forall> t. (proj M) (t *\<^sub>C x) - t *\<^sub>C ((proj M) x) \<in>  M\<close>         
      using  \<open>\<forall> x. \<forall> t.  t *\<^sub>C ((proj M) x) \<in>  M\<close>  \<open>\<forall> x. \<forall> t. ((proj M) (t *\<^sub>C x)) \<in>  M\<close>
      by (metis \<open>M is-a-closed-subspace\<close> \<open>\<forall>x t. t *\<^sub>C x - t *\<^sub>C proj M x \<in> (M\<^sub>\<bottom>)\<close> cancel_comm_monoid_add_class.diff_cancel is_general_subspace.zero is_subspace.subspace proj_uniq)
    ultimately have  \<open>\<forall> x. \<forall> t. (proj M) (t *\<^sub>C x) = t *\<^sub>C ((proj M) x)\<close>
      by (simp add: \<open>\<forall>x t. t *\<^sub>C proj M x \<in> M\<close> \<open>\<forall>x t. t *\<^sub>C x - t *\<^sub>C proj M x \<in> orthogonal_complement M\<close> \<open>is_subspace M\<close> proj_uniq)
    thus ?thesis
      by simp
  qed
  moreover have \<open>Modules.additive (proj M)\<close>
  proof-                   
    have  \<open>\<forall> x.  ((proj M) x) \<in>  M\<close>
      using \<open>is_subspace M\<close>
      by (simp add: proj_intro2) 
    hence  \<open>\<forall> x. \<forall> y. ((proj M) x) + ((proj M) y) \<in>  M\<close>
      by (simp add: \<open>is_subspace M\<close>  is_general_subspace.additive_closed is_subspace.subspace)
    have  \<open>\<forall> x. \<forall> y. ((proj M) (x + y)) \<in> M\<close>
      using \<open>is_subspace M\<close>
      by (simp add: proj_intro2)
    have  \<open>\<forall> x. \<forall> y. (x + y) - (proj M) (x + y) \<in> orthogonal_complement M\<close>
      using \<open>is_subspace M\<close>
      by (simp add: proj_intro1)
    have \<open>\<forall> x. x - (proj M) x \<in> orthogonal_complement M\<close>
      using \<open>is_subspace M\<close>
      by (simp add: proj_intro1)
    hence \<open>\<forall> x. \<forall> y. (x + y) - ((proj M) x + (proj M) y) \<in> orthogonal_complement M\<close>
      by (simp add: \<open>is_subspace (orthogonal_complement M)\<close> add_diff_add is_general_subspace.additive_closed is_subspace.subspace)
    from  \<open>\<forall> x. \<forall> y. (x + y) - ((proj M) x + (proj M) y) \<in>  orthogonal_complement M\<close>
      \<open>\<forall> x. \<forall> y. (x + y) - ((proj M) (x + y)) \<in>  orthogonal_complement M\<close>
    have  \<open>\<forall> x. \<forall> y. ( (x + y) - ((proj M) x + (proj M) y) ) - ( (x + y) - ((proj M) (x + y)) ) \<in>  orthogonal_complement M\<close>
      by (metis \<open>\<forall>x y. proj M x + proj M y \<in> M\<close> \<open>is_subspace M\<close> cancel_comm_monoid_add_class.diff_cancel proj_fixed_points proj_uniq)
    hence \<open>\<forall> x. \<forall> y. (proj M) (x + y) -  ((proj M) x + (proj M) y) \<in> orthogonal_complement M\<close>
      by (metis (no_types, lifting) add_diff_cancel_left diff_minus_eq_add uminus_add_conv_diff)
    moreover have \<open>\<forall> x. \<forall> y. (proj M) (x + y) -  ((proj M) x + (proj M) y) \<in> M\<close>       
      by (metis \<open>M is-a-closed-subspace\<close> \<open>\<forall>x y. proj M x + proj M y \<in> M\<close> \<open>\<forall>x y. x + y - (proj M x + proj M y) \<in> (M\<^sub>\<bottom>)\<close> cancel_comm_monoid_add_class.diff_cancel is_general_subspace.zero is_subspace.subspace proj_uniq)
    ultimately have \<open>\<forall> x. \<forall> y. (proj M) (x + y) - ( ((proj M) x) + ((proj M) y) ) = 0\<close>
      using \<open>\<forall>x y. proj M x + proj M y \<in> M\<close> \<open>\<forall>x y. x + y - (proj M x + proj M y) \<in> orthogonal_complement M\<close> \<open>is_subspace M\<close> proj_uniq by fastforce
    hence  \<open>\<forall> x. \<forall> y. (proj M) (x + y) =  ((proj M) x) + ((proj M) y)\<close>
      by auto
    thus ?thesis
      by (simp add: Modules.additive_def)
  qed

  ultimately have \<open>clinear (proj M)\<close> 
    by (simp add: Modules.additive_def clinearI)
  moreover have \<open>bounded_clinear_axioms (proj M)\<close>
    using projPropertiesB  \<open>is_subspace M\<close> 
    unfolding bounded_clinear_axioms_def
    by (metis mult.commute mult.left_neutral)
  ultimately show ?thesis
    using  bounded_clinear_def
    by auto 
qed


theorem projPropertiesC:
  \<open>is_subspace M \<Longrightarrow> (proj M) \<circ> (proj M) = proj M\<close>
  for M :: \<open>('a::{complex_inner, complete_space}) set\<close>

  (* Reference: Theorem 2.7 in conway2013course *)
  using proj_fixed_points proj_intro2 by fastforce

definition ker_op :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 'a set\<close> where
  \<open>ker_op \<equiv> \<lambda> f. {x. f x = 0}\<close>

lemma ker_op_lin:
  \<open>bounded_clinear f \<Longrightarrow> (ker_op f) is-a-closed-subspace\<close>
proof-
  assume \<open>bounded_clinear f\<close>
  have \<open>x \<in>  {x. f x = 0} \<Longrightarrow> t *\<^sub>C x \<in> {x. f x = 0}\<close> for x t
  proof-
    assume \<open>x \<in>  {x. f x = 0}\<close>
    hence \<open>f x = 0\<close>
      by blast
    hence  \<open>f  (t *\<^sub>C x) = 0\<close>
      by (simp add: \<open>bounded_clinear f\<close> bounded_clinear.clinear clinear.scaleC)
    hence \<open> t *\<^sub>C x \<in> {x. f x = 0}\<close>
      by simp
    show ?thesis 
      using \<open>t *\<^sub>C x \<in> {x. f x = 0}\<close> by auto
  qed

  have \<open>x \<in> {x. f x = 0} \<Longrightarrow> y \<in> {x. f x = 0} \<Longrightarrow> x + y \<in> {x. f x = 0}\<close> for x y
  proof-
    assume \<open>x \<in>  {x. f x = 0}\<close> and \<open>y \<in> {x. f x = 0}\<close>
    have \<open>f x = 0\<close> 
      using \<open>x \<in> {x. f x = 0}\<close> by auto
    have  \<open>f y = 0\<close>
      using \<open>y \<in> {x. f x = 0}\<close> by auto
    have  \<open>f (x + y) = f x + f y\<close>
      using \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def clinear_def
      using Modules.additive_def
      by blast
    hence  \<open>f (x + y) = 0\<close>
      by (simp add: \<open>f x = 0\<close> \<open>f y = 0\<close>)
    hence \<open>x + y \<in>  {x. f x = 0}\<close>
      by simp
    show ?thesis 
      using \<open>x + y \<in> {x. f x = 0}\<close> by auto
  qed

  have \<open>t \<in> {x. f x = 0} \<Longrightarrow> c *\<^sub>C t \<in> {x. f x = 0}\<close> for t c
    using \<open>\<And>x t. x \<in> {x. f x = 0} \<Longrightarrow> t *\<^sub>C x \<in> {x. f x = 0}\<close> by auto
  moreover have \<open>u \<in> {x. f x = 0} \<Longrightarrow> v \<in> {x. f x = 0} \<Longrightarrow> u + v \<in> {x. f x = 0}\<close> for u v
    using \<open>\<And>y x. \<lbrakk>x \<in> {x. f x = 0}; y \<in> {x. f x = 0}\<rbrakk> \<Longrightarrow> x + y \<in> {x. f x = 0}\<close> by auto

  moreover have \<open>closed {x. f x = 0}\<close>
  proof-
    have \<open>r \<longlonglongrightarrow> L \<Longrightarrow> \<forall> n. r n \<in> {x. f x = 0} \<Longrightarrow> L \<in> {x. f x = 0}\<close> for r and  L 
    proof-
      assume \<open>r \<longlonglongrightarrow> L\<close>
      assume \<open>\<forall> n. r n \<in> {x. f x = 0}\<close>
      hence \<open>\<forall> n. f (r n) = 0\<close>
        by simp
      from \<open>bounded_clinear f\<close> 
      have \<open>(\<lambda> n. f (r n)) \<longlonglongrightarrow> f L\<close>
        using \<open>r \<longlonglongrightarrow> L\<close> bounded_linear_continuous continuous_at_sequentiallyI
        unfolding isCont_def
        using tendsto_compose by fastforce

      hence \<open>(\<lambda> n. 0) \<longlonglongrightarrow> f L\<close>
        using \<open>\<forall> n. f (r n) = 0\<close> by simp        
      hence \<open>f L = 0\<close>
        using limI by fastforce
      thus ?thesis by blast
    qed
    thus ?thesis 
      using closed_sequential_limits by blast
  qed
  ultimately show ?thesis
    using  \<open>bounded_clinear f\<close> bounded_clinear_def clinear.scaleC complex_vector.scale_eq_0_iff is_subspace.intro ker_op_def
      bounded_clinear.clinear 
    by (smt Collect_cong is_general_subspace.intro mem_Collect_eq)
qed


theorem projPropertiesD:
  \<open>M is-a-closed-subspace \<Longrightarrow> ker_op  (proj M) = (M\<^sub>\<bottom>)\<close>
  for M :: \<open>('a::{complex_inner, complete_space}) set\<close>
  (* Reference: Theorem 2.7 in conway2013course *)
proof-
  assume \<open>is_subspace M\<close> 

  have \<open>x \<in> orthogonal_complement M \<Longrightarrow> x \<in>  (ker_op  (proj M))\<close> for x
  proof-
    assume \<open>x \<in> orthogonal_complement M\<close>
    hence \<open>(proj M) x = 0\<close>
      using  \<open>is_subspace M\<close>
      by (simp add: is_general_subspace.zero is_subspace.subspace proj_uniq)
    hence \<open>x \<in> (ker_op  (proj M))\<close>
      using ker_op_lin projPropertiesA
      by (simp add: ker_op_def)
    thus ?thesis
      by simp
  qed

  moreover have \<open>x \<in> ker_op  (proj M) \<Longrightarrow> x \<in> orthogonal_complement M\<close> for x
  proof-
    assume \<open>x \<in> ker_op  (proj M)\<close>
    hence  \<open>x \<in> {y.  (proj M) x = 0}\<close>
      using ker_op_lin  projPropertiesA \<open>is_subspace M\<close>
      by (simp add: ker_op_def)
    hence \<open>(proj M) x = 0\<close>
      by (metis (mono_tags, lifting) mem_Collect_eq)
    hence  \<open>x \<in> orthogonal_complement M\<close>
      using \<open>is_subspace M\<close>
      by (metis  diff_zero proj_intro1)   
    thus ?thesis
      by simp
  qed

  ultimately have \<open>orthogonal_complement M = ker_op  (proj M)\<close>         
    by blast
  thus ?thesis 
    by blast
qed


definition ran_op :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 'b set\<close> where
  \<open>ran_op \<equiv> \<lambda> f. {x. \<exists> y. f y = x}\<close>

lemma ran_op_lin:
  \<open>clinear f \<Longrightarrow>  (ran_op f) is-a-subspace\<close>
proof-
  assume \<open>clinear f\<close>
  obtain A where \<open>A = (ran_op f)\<close>
    by simp
  have "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x+y\<in>A" for x y
  proof-
    assume \<open>x \<in> A\<close>
    then obtain xx where \<open>x = f xx\<close> using  \<open>A = (ran_op f)\<close> 
      by (smt mem_Collect_eq ran_op_def)
    assume \<open>y \<in> A\<close>
    then obtain yy where \<open>y = f yy\<close> using  \<open>A = (ran_op f)\<close> 
      by (smt mem_Collect_eq ran_op_def)
    have \<open>x + y = f (xx + yy)\<close> 
      by (metis Modules.additive_def \<open>clinear f\<close> \<open>x = f xx\<close> \<open>y = f yy\<close>  clinear_def)
    thus ?thesis 
      by (metis (mono_tags, lifting) \<open>A = ran_op f\<close> mem_Collect_eq ran_op_def)
  qed
  have  "x\<in>A \<Longrightarrow> c *\<^sub>C x \<in> A" for x c
  proof-
    assume \<open>x \<in> A\<close>
    then obtain y where \<open>x = f y\<close>
      using  \<open>A = (ran_op f)\<close> 
      by (smt mem_Collect_eq ran_op_def)
    have \<open>c *\<^sub>C x = f (c *\<^sub>C y)\<close>
      using  \<open>x = f y\<close>
      by (simp add: \<open>clinear f\<close>  clinear.scaleC)
    thus ?thesis
      using  \<open>x = f y\<close>
      by (metis (mono_tags, lifting) \<open>A = ran_op f\<close> mem_Collect_eq ran_op_def)
  qed
  have  "0 \<in> A"
  proof-
    have \<open>0 = f 0\<close> 
      using \<open>clinear f\<close> additive.zero clinear_def by auto    
      hence \<open>0 \<in> ran_op f\<close>
      by (metis (mono_tags, lifting) mem_Collect_eq ran_op_def)
    thus ?thesis 
      by (simp add: \<open>A = ran_op f\<close>)
  qed
  thus ?thesis 
    using \<open>A = ran_op f\<close> \<open>\<And>x c. x \<in> A \<Longrightarrow> c *\<^sub>C x \<in> A\<close> \<open>\<And>y x. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> x + y \<in> A\<close> is_general_subspace.intro by blast
qed

theorem projPropertiesE:
  \<open>M is-a-closed-subspace \<Longrightarrow> ran_op  (proj M) = M\<close>
  for M :: \<open>('a::{complex_inner, complete_space}) set\<close>
  (* Reference: Theorem 2.7 in conway2013course *)
proof-
  assume \<open>M is-a-closed-subspace\<close>
  have \<open>x \<in> ran_op  (proj M) \<Longrightarrow> x \<in> M\<close> for x
    by (smt \<open>M is-a-closed-subspace\<close> mem_Collect_eq proj_intro2 ran_op_def)
  moreover have \<open>x \<in> M \<Longrightarrow> x \<in> ran_op  (proj M)\<close> for x
    by (metis (mono_tags, lifting) \<open>M is-a-closed-subspace\<close> mem_Collect_eq proj_fixed_points ran_op_def)
  ultimately show ?thesis by blast
qed

lemma pre_ortho_twice: "M is-a-subspace \<Longrightarrow> M \<subseteq> ((M\<^sub>\<bottom>)\<^sub>\<bottom>) " 
proof-
  assume \<open>M is-a-subspace\<close>
  have \<open>x \<in> M \<Longrightarrow> x \<in> ((M\<^sub>\<bottom>)\<^sub>\<bottom>)\<close> for x 
  proof-
    assume \<open>x \<in> M\<close>
    hence \<open>\<forall> y \<in> (M\<^sub>\<bottom>). x \<bottom> y\<close>
      by (simp add: orthogonal_comm orthogonal_complement_def)
    hence \<open>x \<in>  ((M\<^sub>\<bottom>)\<^sub>\<bottom>)\<close>
      by (simp add: orthogonal_complement_def)
    thus ?thesis by blast
  qed            
  thus ?thesis 
    by (simp add: subsetI)
qed


lemma ProjOntoOrtho:
  \<open>is_subspace M \<Longrightarrow> id - proj M = proj (M\<^sub>\<bottom>) \<close>
  for M :: \<open>('a::{complex_inner, complete_space}) set\<close>
  (* Reference: Exercice 2 (section 2, chapter I) in conway2013course *)
proof-
  assume \<open>is_subspace M\<close>
  have   \<open> (id -  proj M) x = (proj ((M\<^sub>\<bottom>))) x \<close> for x
  proof-
    have \<open>x - (proj M) x \<in> orthogonal_complement M\<close>
      using \<open>is_subspace M\<close> proj_intro1 by auto
    hence \<open>(id -  proj M) x \<in> orthogonal_complement M\<close>
      by simp
    have \<open>(proj M) x \<in>  M\<close> 
      by (simp add: \<open>is_subspace M\<close> proj_intro2)
    hence  \<open>x - (id -  proj M) x \<in>  M\<close>
      by simp
    hence \<open>(proj M) x \<in>  ((M\<^sub>\<bottom>)\<^sub>\<bottom>)\<close>
      using pre_ortho_twice  \<open>is_subspace M\<close>  \<open>(proj M) x \<in>  M\<close>  is_subspace.subspace by blast
    hence  \<open>x - (id -  proj M) x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      by simp
    thus ?thesis
      by (metis \<open>(id - proj M) x \<in> orthogonal_complement M\<close> \<open>is_subspace M\<close>   is_subspace_orthog  proj_uniq)
  qed
  thus ?thesis by blast
qed

corollary ortho_twice[simp]: "M is-a-closed-subspace \<Longrightarrow> M = ((M\<^sub>\<bottom>)\<^sub>\<bottom>)"
  for M :: \<open>('a::{complex_inner, complete_space}) set\<close>
    (* Reference: Corollary 2.8 in conway2013course *)
proof-
  assume \<open>M is-a-closed-subspace\<close>
  have \<open>((M\<^sub>\<bottom>)\<^sub>\<bottom>) = ker_op (proj (M\<^sub>\<bottom>))\<close>
    by (simp add: \<open>M is-a-closed-subspace\<close> projPropertiesD)
  also have \<open>... = ker_op ( id - (proj M) )\<close>
    by (simp add: ProjOntoOrtho \<open>M is-a-closed-subspace\<close>)
  also have \<open>... = M\<close>
  proof-
    have \<open>x \<in>  M \<Longrightarrow> x \<in>  ( ker_op ( id - (proj M) ) )\<close> for x
    proof-
      assume \<open>x \<in> M\<close>
      hence \<open>(proj M) x = x\<close>
        using \<open>M is-a-closed-subspace\<close> proj_fixed_points by auto
        hence \<open>(id - (proj M)) x = 0\<close> 
        by simp
      hence \<open>x \<in> {v. (id - (proj M)) v = 0}\<close>
        by simp
      hence \<open>x \<in>  (span {v. (id - (proj M)) v = 0})\<close>
        using span_superset 
        by fastforce
      hence \<open>x \<in> ( ker_op ( id - (proj M) ) )\<close> 
        by (metis ProjOntoOrtho \<open>(id - proj M) x = 0\<close> \<open>M is-a-closed-subspace\<close> calculation diff_zero is_subspace_orthog proj_intro1)
      thus ?thesis 
        by simp                  
    qed
    moreover have \<open>x \<in>  ( ker_op ( id - (proj M) ) ) \<Longrightarrow> x \<in>  M\<close> for x
    proof-
      assume \<open>x \<in>  ( ker_op ( id - (proj M) ) )\<close>
      hence \<open>(id - (proj M)) x = 0\<close>
        by (simp add: ker_op_def)
      hence \<open>(proj M) x = x\<close>
        by auto
      hence \<open>(proj M) x \<in>  M\<close>
        by (metis \<open>M is-a-closed-subspace\<close> proj_intro2)
      hence \<open>x \<in>  M\<close>
        using  \<open>(proj M) x = x\<close> 
        by simp
      thus ?thesis by blast
    qed
    ultimately have \<open>x \<in>  M \<longleftrightarrow> x \<in>  ( ker_op ( id - (proj M) ) )\<close> for x
      by blast
    hence \<open> ( ker_op ( id - (proj M) ) ) =  M\<close>
      by blast
    thus ?thesis 
      by simp
  qed     
  finally show ?thesis by blast
qed

lemma ortho_leq[simp]:
  fixes  A B :: \<open>('a::{complex_inner, complete_space}) set\<close>
  assumes \<open>A is-a-closed-subspace\<close> and  \<open>B is-a-closed-subspace\<close>
  shows \<open>(A\<^sub>\<bottom>) \<subseteq> (B\<^sub>\<bottom>) \<longleftrightarrow> A \<supseteq> B\<close>
proof-
  have \<open>A \<supseteq> B \<Longrightarrow> (A\<^sub>\<bottom>) \<subseteq> (B\<^sub>\<bottom>)\<close>
    by (simp add: orthogonal_complement_def subset_eq)
  moreover have  \<open> (A\<^sub>\<bottom>) \<subseteq> (B\<^sub>\<bottom>) \<Longrightarrow> ((A\<^sub>\<bottom>)\<^sub>\<bottom>) \<supseteq> ((B\<^sub>\<bottom>)\<^sub>\<bottom>)\<close>
    by (simp add: orthogonal_complement_def subset_eq)
  moreover have \<open>A =  ((A\<^sub>\<bottom>)\<^sub>\<bottom>)\<close> 
    by (simp add: assms(1))
  moreover have \<open>B =  ((B\<^sub>\<bottom>)\<^sub>\<bottom>)\<close> 
    by (simp add: assms(2))
  ultimately show ?thesis 
    by blast
qed

lemma ortho_top[simp]: 
" ((top::('a::{complex_inner, complete_space}) set)\<^sub>\<bottom>) 
= ({0}::('a::{complex_inner, complete_space}) set)"
proof-
  have \<open>({0}::('a::{complex_inner, complete_space}) set) \<subseteq>  ((top::('a::{complex_inner, complete_space}) set)\<^sub>\<bottom>)\<close>
    by (simp add: is_general_subspace.zero is_subspace.subspace)
  moreover have  \<open>({0}::('a::{complex_inner, complete_space}) set) \<supseteq>  ((top::('a::{complex_inner, complete_space}) set)\<^sub>\<bottom>)\<close>
    by (metis is_subspace_0 is_subspace_UNIV is_subspace_orthog ortho_leq ortho_twice top_greatest)
  ultimately show ?thesis by blast
qed

lemma ortho_bot[simp]:
" (({0}::('a::{complex_inner, complete_space}) set)\<^sub>\<bottom>) 
= (top::('a::{complex_inner, complete_space}) set)"
  using is_subspace_UNIV ortho_twice by fastforce


subsection {* Disjunction *}

definition general_sum:: \<open>('a::{complex_vector}) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
\<open>general_sum A B = {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}\<close>

abbreviation general_sum_abbr::  \<open>('a::{complex_vector}) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> ("_ \<plusminus> _") where
\<open>A \<plusminus> B  \<equiv> general_sum A B\<close>

abbreviation closure_abbr::  \<open>('a::{topological_space}) set \<Rightarrow> 'a set\<close> ("cl _") where
\<open>cl A \<equiv> closure A\<close>

definition closed_sum:: \<open>('a::{complex_vector,topological_space}) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
\<open>closed_sum A B = cl (A \<plusminus> B)\<close>

abbreviation closed_sum_abbr::  \<open>('a::{complex_vector,topological_space}) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> ("_ \<minusplus> _") where
\<open>A \<minusplus> B  \<equiv> closed_sum A B\<close>

lemma sum_existential:
\<open>x \<in> (A \<plusminus> B) \<Longrightarrow> \<exists> a\<in>A. \<exists> b\<in>B. x = a + b\<close>
proof -
  assume "x \<in> (A \<plusminus> B)"
  then have "\<exists>a aa. x = a + aa \<and> a \<in> A \<and> aa \<in> B"
    using general_sum_def by blast
  then show ?thesis
    by (metis (lifting))
qed

lemma is_closed_subspace_comm:
  assumes \<open>A is-a-closed-subspace\<close> and \<open>B is-a-closed-subspace\<close>
  shows \<open>(A \<minusplus> B) = (B \<minusplus> A)\<close>
  by (smt Collect_cong add.commute closed_sum_def general_sum_def)

lemma is_closed_subspace_asso:
  fixes A B C::"('a::complex_inner) set"
  assumes \<open>A is-a-closed-subspace\<close> and \<open>B is-a-closed-subspace\<close> and \<open>C is-a-closed-subspace\<close>
  shows \<open>(A \<minusplus> (B \<minusplus> C)) = ((A \<minusplus> B) \<minusplus> C)\<close>
  sorry

lemma is_closed_subspace_ord:
  assumes \<open>A is-a-closed-subspace\<close> and \<open>B is-a-closed-subspace\<close> and \<open>C is-a-closed-subspace\<close>
    and \<open>A \<subseteq> B\<close>
  shows \<open>(C\<minusplus>A) \<subseteq>(C\<minusplus>B)\<close>
  sorry


lemma is_closed_subspace_zero:
  assumes \<open>A is-a-closed-subspace\<close>
  shows \<open>(({0})\<minusplus>A) = A\<close>
  sorry

subsection {* Direct sum *}

definition InternalDirectSum :: \<open>('a::ab_group_add) set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
\<open>InternalDirectSum C A B = (C = {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B} \<and> A \<inter> B = {0})\<close>                                    

abbreviation InternalDirectSum_abbr :: \<open>('a::ab_group_add) set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool\<close> ("_ =  _ \<oplus> _") where
\<open>C = A \<oplus> B \<equiv> InternalDirectSum C A B\<close>

lemma is_subspace_oplus:
  assumes \<open>A is-a-closed-subspace\<close> and \<open>B is-a-closed-subspace\<close>
    and \<open>C = A \<oplus> B\<close>
  shows \<open>C is-a-closed-subspace\<close>
proof-
  have \<open>C is-a-subspace\<close>
  proof-
   have \<open>A is-a-subspace\<close>
      by (simp add: assms(1) is_subspace.subspace)  
   moreover have \<open>B is-a-subspace\<close>
    by (simp add: assms(2) is_subspace.subspace)
   moreover have \<open>C = {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}\<close> using \<open>C = A \<oplus> B\<close> InternalDirectSum_def 
    by blast
  ultimately show ?thesis 
    by (simp add: is_subspace_plus)
  qed
  moreover have \<open>C is-closed\<close>
    sorry
  ultimately show ?thesis 
    by (simp add: is_subspace_def)

qed


end
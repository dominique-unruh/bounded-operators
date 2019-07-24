(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Main results
- complex_inner: Class of complex vector spaces with inner product.
- cgderiv: Gradient derivative.
- chilbert_space: Class of complex Hilbert spaces
- existence_uniqueness_min_dist: Existence and uniqueness of a point in a convex body whose
distance to a given point reach its minimum in the convex body.
- dist_min_ortho: Equivalence between point at minimum distance and orthogonal projection.
- proj: Definition of orthogonal projection.
- projPropertiesA: The orthogonal projection is a bounded operator.
- orthogonal_complement_twice: The orthogonal complement is an involution.
- ortho_decomp: Decomposition of a Hilbert space into a sum of a subspace and its orthogonal 
complement.
- riesz_frechet_representation_existence: Riesz-Frechet representation theorem
- Adj: Definition of adjoint.
- dagger_dagger_id: The adjoint is an involution.
*)

section \<open>Inner Product Spaces and the Gradient Derivative\<close>

theory Complex_Inner_Product
  imports "HOL-Analysis.Infinite_Set_Sum" Complex_Main Complex_Vector_Spaces
    "HOL-Analysis.Inner_Product"  
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

class complex_inner = complex_vector + sgn_div_norm + dist_norm + uniformity_dist + 
  open_uniformity +
  fixes cinner :: "'a \<Rightarrow> 'a \<Rightarrow> complex"  ("\<langle>_, _\<rangle>") 
  assumes cinner_commute: "\<langle>x, y\<rangle> = cnj \<langle>y, x\<rangle>"
    and cinner_add_left: "\<langle>x + y, z\<rangle> = \<langle>x, z\<rangle> +  \<langle>y, z\<rangle>"
    and cinner_scaleC_left [simp]: "\<langle>r *\<^sub>C x, y\<rangle> = (cnj r) * \<langle>x, y\<rangle>"
    and cinner_ge_zero [simp]: "0 \<le> \<langle>x, x\<rangle>"
    and cinner_eq_zero_iff [simp]: "\<langle>x, x\<rangle> = 0 \<longleftrightarrow> x = 0"
    and norm_eq_sqrt_cinner: "norm x = sqrt (cmod (\<langle>x, x\<rangle>))"
begin

lemma cinner_real: "\<langle>x, x\<rangle> \<in> \<real>"
  by (simp add: reals_zero_comparable_iff)

lemmas cinner_commute' [simp] = cinner_commute[symmetric]

lemma cinner_zero_left [simp]: "\<langle>0, x\<rangle> = 0"
  using cinner_add_left [of 0 0 x] by simp

lemma cinner_minus_left [simp]: "\<langle>-x, y\<rangle> = - \<langle>x, y\<rangle>"
  using cinner_add_left [of x "- x" y]
  by (metis (mono_tags, lifting) cancel_ab_semigroup_add_class.add_diff_cancel_left' cinner_zero_left group_add_class.diff_0 local.right_minus)

lemma cinner_diff_left: "\<langle>x - y, z\<rangle> = \<langle>x, z\<rangle> - \<langle>y, z\<rangle>"
  using cinner_add_left [of x "- y" z] by simp

lemma cinner_sum_left: "\<langle>\<Sum>x\<in>A. f x, y\<rangle> = (\<Sum>x\<in>A. \<langle>f x, y\<rangle>)"
  by (cases "finite A", induct set: finite, simp_all add: cinner_add_left)

text \<open>Transfer distributivity rules to right argument.\<close>

lemma cinner_add_right: "\<langle>x, y + z\<rangle> = \<langle>x, y\<rangle> + \<langle>x, z\<rangle>"
  using cinner_add_left [of y z x]
  by (metis complex_cnj_add local.cinner_commute)

lemma cinner_scaleC_right [simp]: "\<langle>x , (r *\<^sub>C y)\<rangle> = r * (\<langle>x , y\<rangle>)"
  using cinner_scaleC_left [of r y x]
  by (metis complex_cnj_cnj complex_cnj_mult local.cinner_commute)

lemma cinner_zero_right [simp]: "\<langle>x , 0\<rangle> = 0"
  using cinner_zero_left [of x] 
  by (metis (mono_tags, lifting) complex_cnj_zero local.cinner_commute) 

lemma cinner_minus_right [simp]: "\<langle>x , (- y)\<rangle> = - (\<langle>x , y\<rangle>)"
  using cinner_minus_left [of y x]
  by (metis complex_cnj_minus local.cinner_commute)

lemma cinner_diff_right: "\<langle>x , (y - z)\<rangle> = (\<langle>x , y\<rangle>) - (\<langle>x , z\<rangle>)"
  using cinner_diff_left [of y z x]
  by (metis complex_cnj_diff local.cinner_commute)

lemma cinner_sum_right: "\<langle>x , (\<Sum>y\<in>A. f y)\<rangle> = (\<Sum>y\<in>A. \<langle>x , (f y)\<rangle>)"
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

lemma cinner_gt_zero_iff [simp]: "0 < \<langle>x, x\<rangle> \<longleftrightarrow> x \<noteq> 0"
  by (simp add: order_less_le)

lemma power2_norm_eq_cinner:
  includes notation_norm
  shows "\<parallel>x\<parallel>\<^sup>2 = cmod \<langle>x, x\<rangle>"
  by (simp add: norm_eq_sqrt_cinner)


lemma power2_norm_eq_cinner':
  includes notation_norm
  shows "complex_of_real (\<parallel> x \<parallel>\<^sup>2) = \<langle>x, x\<rangle>"
  apply (subst power2_norm_eq_cinner)
  using cinner_ge_zero by (rule complex_of_real_cmod)

lemma power2_norm_eq_cinner'':
  includes notation_norm
  shows "(complex_of_real \<parallel>x\<parallel>)\<^sup>2 = \<langle>x, x\<rangle>"
  using power2_norm_eq_cinner' by simp


text \<open>Identities involving complex multiplication and division.\<close>

lemma cinner_mult_left: "\<langle>(of_complex m * a) , b\<rangle> =  (cnj m) * (\<langle>a , b\<rangle>)"
  unfolding of_complex_def by simp

lemma cinner_mult_right: "\<langle>a , (of_complex m * b)\<rangle> = m * (\<langle>a , b\<rangle>)"
  by (metis complex_inner_class.cinner_scaleC_right scaleC_conv_of_complex)

lemma cinner_mult_left': "\<langle>(a * of_complex m) , b\<rangle> =  (cnj m) * (\<langle>a , b\<rangle>)"
  using cinner_mult_left by (simp add: of_complex_def)

lemma cinner_mult_right': "\<langle>a , (b * of_complex m)\<rangle> = (\<langle>a , b\<rangle>) * m"
  by (simp add: of_complex_def complex_inner_class.cinner_scaleC_right)

lemma Cauchy_Schwarz_ineq:
  "(\<langle>x , y\<rangle>) * (cnj (\<langle>x , y\<rangle>) ) \<le> (\<langle>x , x\<rangle>) * (\<langle>y , y\<rangle>)"
proof (cases)
  assume "y = 0"
  thus ?thesis by simp
next
  assume y: "y \<noteq> 0"
  have [simp]: "cnj (\<langle>y , y\<rangle>) = \<langle>y , y\<rangle>" for y
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

lemma Im_cinner_x_x[simp]: "Im (\<langle>x , x\<rangle>) = 0"
  using comp_Im_same[OF cinner_ge_zero] by simp

lemma cinner_norm_sq:
  includes notation_norm
  shows "\<langle>x, x\<rangle> = complex_of_real (\<parallel>x\<parallel>^2)"
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

lemma norm_cauchy_schwarz:
  includes notation_norm 
  shows "cmod \<langle>x , y\<rangle> \<le> \<parallel>x\<parallel> * \<parallel>y\<parallel>"
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

lemma norm_cauchy_schwarz2:
  includes notation_norm 
  shows "\<bar>\<langle>x , y\<rangle>\<bar> \<le> complex_of_real \<parallel>x\<parallel> * complex_of_real \<parallel>y\<parallel>"
  using norm_cauchy_schwarz [of x y, THEN complex_of_real_mono]
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
      using norm_cauchy_schwarz2
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

lemma cinner_divide_right:
  fixes a :: "'a :: {complex_inner,complex_div_algebra}"
  shows "cinner a (b / of_complex m) = (\<langle>a , b\<rangle>) / m"
  by (metis (no_types, lifting) cinner_mult_right' divide_inverse divide_self_if inverse_eq_divide of_complex_divide of_complex_eq_0_iff one_neq_zero)

lemma cinner_divide_left:
  fixes a :: "'a :: {complex_inner,complex_div_algebra}"
  shows "\<langle>(a / of_complex m) , b\<rangle> = (\<langle>a , b\<rangle>) / (cnj m)"
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
      by (simp add: norm_cauchy_schwarz)
  qed
qed


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

definition cinner_complex_def [simp]: "\<langle>x, y\<rangle> = (cnj x) * y"

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
  shows complex_inner_1_left[simp]: "\<langle>1 , x\<rangle> = x"
    and complex_inner_1_right[simp]: "\<langle>x , 1\<rangle> = (cnj x)"
  by simp_all

lemma norm_eq_square: "norm x = a \<longleftrightarrow> 0 \<le> a \<and> \<langle>x , x\<rangle> = complex_of_real (a\<^sup>2)"
  by (metis cinner_norm_sq norm_ge_zero of_real_eq_iff power2_eq_imp_eq)

lemma norm_le_square: "norm x \<le> a \<longleftrightarrow> 0 \<le> a \<and>  \<langle>x , x\<rangle> \<le> complex_of_real (a\<^sup>2)"
  by (metis add.left_neutral add.right_neutral add_mono_thms_linordered_field(4) cinner_norm_sq complex_of_real_mono_iff norm_ge_zero not_le power2_le_imp_le power_mono)

lemma norm_ge_square: "norm x \<ge> a \<longleftrightarrow> a \<le> 0 \<or> \<langle>x , x\<rangle> \<ge> complex_of_real (a\<^sup>2)"
  by (smt complex_of_real_mono_iff norm_ge_zero power2_le_imp_le power2_norm_eq_cinner')

lemma norm_lt_square: "norm x < a \<longleftrightarrow> 0 < a \<and> \<langle>x , x\<rangle> < complex_of_real (a\<^sup>2)"
  by (smt Complex_Inner_Product.norm_eq_square Complex_Inner_Product.norm_le_square less_le)

lemma norm_gt_square: "norm x > a \<longleftrightarrow> a < 0 \<or> \<langle>x , x\<rangle> > complex_of_real (a\<^sup>2)"
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

class chilbert_space =  complex_inner + complete_space
begin
subclass cbanach by standard
end


class hilbert_space =  real_inner + complete_space
begin
subclass banach by standard
end


subsection \<open>Some identities and inequalities\<close>

lemma polarization_identity_plus:
  includes notation_norm
  shows \<open>\<parallel>x + y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 + 2*Re \<langle>x, y\<rangle>\<close>
    \<comment> \<open>Shown in the proof of Corollary 1.5 in @{cite conway2013course}\<close> 
proof-
  have \<open>(\<langle>x , y\<rangle>) + (\<langle>y , x\<rangle>) = (\<langle>x , y\<rangle>) + cnj (\<langle>x , y\<rangle>)\<close>
    by simp
  hence \<open>(\<langle>x , y\<rangle>) + (\<langle>y , x\<rangle>) = 2* Re (\<langle>x , y\<rangle>) \<close>
    using complex_add_cnj by presburger
  have \<open>\<parallel>x + y\<parallel>^2 = ( \<langle>(x+y) , (x+y)\<rangle> )\<close> 
    using power2_norm_eq_cinner' by auto
  hence \<open>\<parallel>x + y\<parallel>^2 = (\<langle>x , x\<rangle>) + (\<langle>x , y\<rangle>) + (\<langle>y , x\<rangle>) + (\<langle>y , y\<rangle>)\<close>
    by (simp add: cinner_left_distrib cinner_right_distrib)
  thus ?thesis using  \<open>(\<langle>x , y\<rangle>) + (\<langle>y , x\<rangle>) = 2* Re (\<langle>x , y\<rangle>)\<close>
    by (smt Re_complex_of_real cinner_norm_sq plus_complex.simps(1))
qed

lemma polarization_identity_minus:
  includes notation_norm 
  shows \<open>\<parallel>x - y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 - 2*Re \<langle>x, y\<rangle>\<close>
proof-
  have \<open>\<parallel>x + (-y)\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>-y\<parallel>^2 + 2*Re (\<langle>x , (-y)\<rangle>)\<close>
    using polarization_identity_plus by blast
  hence \<open>\<parallel>x - y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 - 2*Re (\<langle>x , y\<rangle>)\<close>
    by simp
  thus ?thesis 
    by blast
qed

proposition ParallelogramLaw:
  includes notation_norm
  fixes x y :: "'a::complex_inner"
  shows \<open>\<parallel>x+y\<parallel>^2 + \<parallel>x-y\<parallel>^2 = 2*( \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 )\<close>
    \<comment> \<open>Shown in the proof of Theorem 2.3 in @{cite conway2013course}\<close> 
  by (simp add: polarization_identity_minus polarization_identity_plus)

corollary ParallelogramLawVersion1:
  includes notation_norm
  fixes x :: "'a::complex_inner"
  shows \<open>\<parallel> (1/2) *\<^sub>C x - (1/2) *\<^sub>C y \<parallel>^2
    = (1/2)*( \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 ) - \<parallel> (1/2) *\<^sub>C x + (1/2) *\<^sub>C y \<parallel>^2\<close>
    \<comment> \<open>Shown in the proof of Theorem 2.5 in @{cite conway2013course}\<close> 
proof -
  have \<open>\<parallel> (1/2) *\<^sub>C x + (1/2) *\<^sub>C y \<parallel>^2 + \<parallel> (1/2) *\<^sub>C x - (1/2) *\<^sub>C y \<parallel>^2 
  = 2*( \<parallel>(1/2) *\<^sub>C x\<parallel>^2 +  \<parallel>(1/2) *\<^sub>C y\<parallel>^2)\<close>
    using ParallelogramLaw by blast
  also have \<open>... = 2*( ((1/2) * \<parallel>x\<parallel>)^2 + ((1/2) * \<parallel>y\<parallel>)^2)\<close>
    by auto
  also have \<open>... = 2*( (1/2)^2 * \<parallel>x\<parallel>^2 +  (1/2)^2 * \<parallel>y\<parallel>^2 )\<close>
    by (metis power_mult_distrib)
  also have \<open>... = 2*( (1/4) * \<parallel>x\<parallel>^2 +  (1/4) * \<parallel>y\<parallel>^2 )\<close>
    by (metis (no_types, lifting) mult.right_neutral numeral_Bit0 one_add_one one_power2 power2_sum power_divide)
  also have \<open>... = 2*(1/4) * \<parallel>x\<parallel>^2 + 2*(1/4) * \<parallel>y\<parallel>^2\<close>
    by auto
  also have \<open>... = (1/2) * \<parallel>x\<parallel>^2 + (1/2) * \<parallel>y\<parallel>^2\<close>
    by auto
  also have \<open>... = (1/2) * ( \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 )\<close>
    by auto
  finally have \<open>\<parallel>(1 / 2) *\<^sub>C x + (1 / 2) *\<^sub>C y\<parallel>\<^sup>2 + \<parallel>(1 / 2) *\<^sub>C x - (1 / 2) *\<^sub>C y\<parallel>\<^sup>2
                   = 1 / 2 * (\<parallel>x\<parallel>\<^sup>2 + \<parallel>y\<parallel>\<^sup>2)\<close>
    by blast
  thus ?thesis 
    by (metis add_diff_cancel_left')
qed


theorem PythagoreanId:
  includes notation_norm
  shows \<open>\<langle>x , y\<rangle> = 0 \<Longrightarrow> \<parallel> x + y \<parallel>^2 = \<parallel> x \<parallel>^2 + \<parallel> y \<parallel>^2\<close> 
    \<comment> \<open>Shown in the proof of Theorem 2.2 in @{cite conway2013course}\<close> 
  by (simp add: polarization_identity_plus)


subsection \<open>Orthogonality\<close>

definition "is_orthogonal x y = (\<langle> x, y \<rangle> = 0)"

abbreviation is_orthogonal_abbr::"'a::complex_inner \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<bottom>" 50)
  where \<open>x \<bottom> y \<equiv> is_orthogonal x y\<close>

definition "orthogonal_complement S = {x | x. \<forall>y\<in>S. x \<bottom> y}" 

lemma orthogonal_comm: "(\<psi> \<bottom> \<phi>) = (\<phi> \<bottom> \<psi>)"
  unfolding is_orthogonal_def apply (subst cinner_commute) by blast

\<comment> \<open>The name "linear manifold" came from page 10 in @{cite conway2013course}\<close> 
locale is_linear_manifold =
  fixes A::"('a::complex_vector) set"
  assumes additive_closed: "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x+y\<in>A"
  assumes smult_closed: "x\<in>A \<Longrightarrow> c *\<^sub>C x \<in> A"
  assumes zero: "0 \<in> A"

locale is_subspace =
  fixes A::"('a::{complex_vector,topological_space}) set"
  assumes subspace: "is_linear_manifold A"
  assumes closed: "closed A"

lemma is_subspace_cl:
  fixes A::"('a::complex_normed_vector) set"
  assumes \<open>is_linear_manifold A\<close>
  shows \<open>is_linear_manifold (closure A)\<close>
proof-
  have "x \<in> closure A \<Longrightarrow> y \<in> closure A \<Longrightarrow> x+y \<in> closure A" for x y
  proof-
    assume \<open>x\<in>(closure A)\<close>
    then obtain xx where \<open>\<forall> n::nat. xx n \<in> A\<close> and \<open>xx \<longlonglongrightarrow> x\<close>
      using closure_sequential by blast
    assume \<open>y\<in>(closure A)\<close>
    then obtain yy where \<open>\<forall> n::nat. yy n \<in> A\<close> and \<open>yy \<longlonglongrightarrow> y\<close>
      using closure_sequential by blast
    have \<open>\<forall> n::nat. (xx n) + (yy n) \<in> A\<close> 
      by (simp add: \<open>\<forall>n. xx n \<in> A\<close> \<open>\<forall>n. yy n \<in> A\<close> assms is_linear_manifold.additive_closed)
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
      by (simp add: \<open>\<forall>n. xx n \<in> A\<close> assms is_linear_manifold.smult_closed)
    have \<open>isCont (\<lambda> t. c *\<^sub>C t) x\<close> 
      using bounded_clinear.bounded_linear bounded_clinear_scaleC_right linear_continuous_at by auto
    hence  \<open>(\<lambda> n. c *\<^sub>C (xx n)) \<longlonglongrightarrow> c *\<^sub>C x\<close> using  \<open>xx \<longlonglongrightarrow> x\<close>
      by (simp add: isCont_tendsto_compose)
    thus ?thesis using  \<open>\<forall> n::nat. c *\<^sub>C (xx n) \<in> A\<close> 
      by (meson closure_sequential)
  qed
  moreover have "0 \<in> (closure A)"
    using assms closure_subset is_linear_manifold.zero by fastforce
  ultimately show ?thesis 
    by (simp add: is_linear_manifold_def)
qed

\<comment> \<open>The name "Minkoswki_sum" can be found in @{cite conway2013course}\<close> 

definition Minkoswki_sum:: \<open>('a::{complex_vector}) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>Minkoswki_sum A B = {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}\<close>

notation Minkoswki_sum (infixl "+\<^sub>m" 65)

lemma is_subspace_plus:
  assumes \<open>is_linear_manifold A\<close> and \<open>is_linear_manifold B\<close>
  shows \<open>is_linear_manifold (A +\<^sub>m B)\<close>
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
      by (simp add: \<open>xA \<in> A\<close> \<open>yA \<in> A\<close> assms(1) is_linear_manifold.additive_closed)
    moreover have \<open>xB + yB \<in> B\<close>
      by (simp add: \<open>xB \<in> B\<close> \<open>yB \<in> B\<close> assms(2) is_linear_manifold.additive_closed)
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
      by (simp add: \<open>xA \<in> A\<close> assms(1) is_linear_manifold.smult_closed)
    moreover have \<open>c *\<^sub>C xB \<in> B\<close>
      by (simp add: \<open>xB \<in> B\<close> assms(2) is_linear_manifold.smult_closed)
    ultimately show ?thesis
      using \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> by blast
  qed
  moreover have  "0 \<in> C"
    by (metis (mono_tags, lifting) \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> add.inverse_neutral add_uminus_conv_diff assms(1) assms(2) diff_0 is_linear_manifold.zero mem_Collect_eq)
  ultimately show ?thesis
    by (metis (no_types, lifting) assms(1) assms(2) complex_vector.subspace_def complex_vector.subspace_sums Minkoswki_sum_def is_linear_manifold_def)
qed


lemma is_subspace_0[simp]: 
  "is_subspace ({0} :: ('a::{complex_vector,t1_space}) set)"
proof-
  have \<open>is_linear_manifold {0}\<close>
    using add.right_neutral is_linear_manifold_def scaleC_right.zero by blast
  moreover have "closed ({0} :: ('a::{complex_vector,t1_space}) set)"
    by simp 
  ultimately show ?thesis 
    by (simp add: is_subspace_def)
qed

lemma is_subspace_UNIV[simp]: "is_subspace (UNIV::('a::{complex_vector,topological_space}) set)"
proof-
  have \<open>is_linear_manifold UNIV\<close>
    by (simp add: is_linear_manifold_def)
  moreover have \<open>closed UNIV\<close>
    by simp
  ultimately show ?thesis by (simp add: is_subspace_def)
qed

lemma is_subspace_inter[simp]:
  assumes "is_subspace A" and "is_subspace B"
  shows "is_subspace (A\<inter>B)"
proof-
  obtain C where \<open>C = A \<inter> B\<close> by blast
  have \<open>is_linear_manifold C\<close>
  proof-
    have "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> x+y\<in>C" for x y
      by (metis IntD1 IntD2 IntI \<open>C = A \<inter> B\<close> assms(1) assms(2) is_linear_manifold_def is_subspace_def)
    moreover have "x\<in>C \<Longrightarrow> c *\<^sub>C x \<in> C" for x c
      by (metis IntD1 IntD2 IntI \<open>C = A \<inter> B\<close> assms(1) assms(2) is_linear_manifold_def is_subspace_def)
    moreover have "0 \<in> C" 
      using  \<open>C = A \<inter> B\<close> assms(1) assms(2) is_linear_manifold_def is_subspace_def by fastforce
    ultimately show ?thesis 
      by (simp add: is_linear_manifold_def)
  qed
  moreover have \<open>closed C\<close>
    using  \<open>C = A \<inter> B\<close>
    by (simp add: assms(1) assms(2) closed_Int is_subspace.closed)
  ultimately show ?thesis
    using  \<open>C = A \<inter> B\<close>
    by (simp add: is_subspace_def)
qed


lemma is_subspace_INF[simp]:
  "\<forall> A \<in> \<A>. (is_subspace A) \<Longrightarrow> is_subspace (\<Inter>\<A>)"
proof-
  assume \<open>\<forall> A \<in> \<A>. (is_subspace A)\<close>
  have \<open>is_linear_manifold (\<Inter>\<A>)\<close>
  proof -
    obtain aa :: "'a set \<Rightarrow> 'a" and cc :: "'a set \<Rightarrow> complex" where
      f1: "\<forall>x0. (\<exists>v1 v2. v1 \<in> x0 \<and> v2 *\<^sub>C v1 \<notin> x0) = (aa x0 \<in> x0 \<and> cc x0 *\<^sub>C aa x0 \<notin> x0)"
      by moura
    obtain aaa :: "'a set \<Rightarrow> 'a" and aab :: "'a set \<Rightarrow> 'a" where
      "\<forall>x0. (\<exists>v1 v2. (v1 \<in> x0 \<and> v2 \<in> x0) \<and> v1 + v2 \<notin> x0) = ((aaa x0 \<in> x0 \<and> aab x0 \<in> x0) \<and> aaa x0 + aab x0 \<notin> x0)"
      by moura
    then have f2: "\<forall>A. (\<not> is_linear_manifold A \<or> (\<forall>a aa. a \<notin> A \<or> aa \<notin> A \<or> a + aa \<in> A) \<and> (\<forall>a c. a \<notin> A \<or> c *\<^sub>C a \<in> A) \<and> 0 \<in> A) \<and> (is_linear_manifold A \<or> aaa A \<in> A \<and> aab A \<in> A \<and> aaa A + aab A \<notin> A \<or> aa A \<in> A \<and> cc A *\<^sub>C aa A \<notin> A \<or> 0 \<notin> A)"
      using f1 by (metis (no_types) is_linear_manifold_def)
    obtain AA :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x0 \<and> x1 \<notin> v2) = (AA x0 x1 \<in> x0 \<and> x1 \<notin> AA x0 x1)"
      by moura
    then have f3: "\<forall>a A. (a \<notin> \<Inter> A \<or> (\<forall>Aa. Aa \<notin> A \<or> a \<in> Aa)) \<and> (a \<in> \<Inter> A \<or> AA A a \<in> A \<and> a \<notin> AA A a)"
      by auto
    have f4: "\<forall>A. \<not> is_subspace (A::'a set) \<or> is_linear_manifold A"
      by (metis is_subspace.subspace)
    have f5: "\<forall>A. A \<notin> \<A> \<or> is_subspace A"
      by (metis \<open>\<forall>A\<in>\<A>. is_subspace A\<close>)
    then have f6: "aa (\<Inter> \<A>) \<notin> \<Inter> \<A> \<or> cc (\<Inter> \<A>) *\<^sub>C aa (\<Inter> \<A>) \<in> \<Inter> \<A>"
      using f4 f3 f2 by meson
    have f7: "0 \<in> \<Inter> \<A>"
      using f5 f4 f3 f2 by meson
    have "aaa (\<Inter> \<A>) \<notin> \<Inter> \<A> \<or> aab (\<Inter> \<A>) \<notin> \<Inter> \<A> \<or> aaa (\<Inter> \<A>) + aab (\<Inter> \<A>) \<in> \<Inter> \<A>"
      using f5 f4 f3 f2 by meson
    then show ?thesis
      using f7 f6 f2 by (metis (no_types))
  qed
  moreover have \<open>closed (\<Inter>\<A>)\<close>
    by (simp add: \<open>\<forall>A\<in>\<A>. is_subspace A\<close> closed_Inter is_subspace.closed)
  ultimately show ?thesis 
    by (simp add: is_subspace.intro)
qed

lemma is_subspace_orthog[simp]: "is_subspace A \<Longrightarrow> is_subspace (orthogonal_complement A)"
  for A :: \<open>('a::complex_inner) set\<close>
proof-
  assume \<open>is_subspace A\<close>
  have  "x\<in>(orthogonal_complement A) \<Longrightarrow> y\<in>(orthogonal_complement A) \<Longrightarrow> x+y\<in>(orthogonal_complement A)" for x y
  proof-
    assume \<open>x\<in>(orthogonal_complement A)\<close>
    assume \<open>y\<in>(orthogonal_complement A)\<close>
    hence  \<open>\<forall> z \<in> A. \<langle>z, y\<rangle> = 0\<close> 
      using is_orthogonal_def orthogonal_comm orthogonal_complement_def by fastforce
    moreover have   \<open>\<forall> z \<in> A. \<langle>z, x\<rangle> = 0\<close> using  \<open>x\<in>(orthogonal_complement A)\<close>
      using is_orthogonal_def orthogonal_comm orthogonal_complement_def by fastforce
    ultimately have \<open>\<forall> z \<in> A. \<langle>z, x\<rangle> +  \<langle>z, y\<rangle> = 0\<close>
      by simp
    hence  \<open>\<forall> z \<in> A. \<langle> z , x + y \<rangle> = 0\<close> 
      by (simp add: cinner_right_distrib)
    thus ?thesis 
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
  qed
  moreover have "x\<in>(orthogonal_complement A) \<Longrightarrow> c *\<^sub>C x \<in> (orthogonal_complement A)" for x c
  proof-
    assume \<open>x \<in> (orthogonal_complement A)\<close>
    hence \<open>\<forall> y \<in> A. \<langle> y , x \<rangle> = 0\<close>
      using is_orthogonal_def orthogonal_comm orthogonal_complement_def by fastforce
    hence \<open>\<forall> y \<in> A. c*\<langle> y , x \<rangle> = 0\<close>
      by simp
    hence \<open>\<forall> y \<in> A. \<langle> y , c *\<^sub>C x \<rangle> = 0\<close>
      by simp
    thus ?thesis 
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
  qed
  moreover have  "closed (orthogonal_complement A)"
  proof-
    have \<open>\<lbrakk>(\<forall> n::nat. x n \<in> (orthogonal_complement A)); x \<longlonglongrightarrow> l \<rbrakk> \<Longrightarrow> l \<in> (orthogonal_complement A)\<close> for x::\<open>nat \<Rightarrow> ('a::complex_inner)\<close> and l::\<open>('a::complex_inner)\<close>
    proof-
      assume \<open>\<forall> n::nat. x n \<in> (orthogonal_complement A)\<close>
      hence \<open>\<forall> y \<in> A. \<forall> n. \<langle> y , x n \<rangle> = 0\<close>
        by (metis (no_types, lifting) cinner_commute complex_cnj_zero_iff is_orthogonal_def mem_Collect_eq orthogonal_complement_def)
      assume \<open>x \<longlonglongrightarrow> l\<close>
      moreover have \<open>isCont (\<lambda> x. \<langle> y , x \<rangle>) l\<close> for y
      proof-
        have \<open>bounded_clinear (\<lambda> x. \<langle> y , x \<rangle>)\<close> 
          by (simp add: bounded_clinear_cinner_right)
        thus ?thesis
          by simp
      qed
      ultimately have \<open>(\<lambda> n. (\<lambda> v. \<langle> y , v \<rangle>) (x n)) \<longlonglongrightarrow> (\<lambda> v. \<langle> y , v \<rangle>) l\<close> for y
        using isCont_tendsto_compose by fastforce
      hence  \<open>\<forall> y\<in>A. (\<lambda> n. \<langle> y , x n \<rangle>  ) \<longlonglongrightarrow>  \<langle> y , l \<rangle>\<close>
        by simp
      hence  \<open>\<forall> y\<in>A. (\<lambda> n. 0  ) \<longlonglongrightarrow>  \<langle> y , l \<rangle>\<close> 
        using \<open>\<forall> y \<in> A. \<forall> n. \<langle> y , x n \<rangle> = 0\<close> 
        by fastforce
      hence  \<open>\<forall> y \<in> A. \<langle> y , l \<rangle> = 0\<close> 
        using limI by fastforce
      thus ?thesis 
        by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    qed
    thus ?thesis 
      using closed_sequential_limits by blast
  qed
  moreover have  "0 \<in> (orthogonal_complement A)"
    by (simp add: is_orthogonal_def orthogonal_complement_def)
  ultimately show ?thesis 
    by (simp add: is_linear_manifold.intro is_subspace_def)
qed

subsection \<open>Minimum distance\<close>

(* TODO: move? *)
definition is_arg_min_on :: \<open>('a \<Rightarrow> 'b :: ord) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>is_arg_min_on f M x = (is_arg_min f (\<lambda> t. t \<in> M) x)\<close>

lemma ExistenceUniquenessMinNorm:
  includes notation_norm
  fixes M :: \<open>('a::chilbert_space) set\<close>  
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>! k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) M k\<close>
proof-
  have \<open>\<exists> k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) M k\<close>
  proof-
    have \<open>\<exists> k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>^2) M k\<close>
    proof-
      obtain d where \<open>d = Inf { \<parallel>x\<parallel>^2 | x. x \<in> M }\<close>
        by blast
      have \<open>{ \<parallel>x\<parallel>^2 | x. x \<in> M } \<noteq> {}\<close>
        by (simp add: assms(3))
      have \<open>\<forall> x. \<parallel>x\<parallel>^2 \<ge> 0\<close>
        by simp
      hence \<open>bdd_below  { \<parallel>x\<parallel>^2 | x. x \<in> M }\<close>
        by fastforce
      have \<open>x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>^2\<close> for x
      proof -
        assume a1: "x \<in> M"
        have "\<forall>v. (\<exists>va. Re (\<langle>v , v\<rangle> ) = \<parallel>va\<parallel>\<^sup>2 \<and> va \<in> M) \<or> v \<notin> M"
          by (metis (no_types) Re_complex_of_real power2_norm_eq_cinner')
        then have "Re (\<langle>x , x\<rangle> ) \<in> {\<parallel>v\<parallel>\<^sup>2 |v. v \<in> M}"
          using a1 by blast
        then show ?thesis
          by (metis (lifting) Re_complex_of_real \<open>bdd_below {\<parallel>x\<parallel>\<^sup>2 |x. x \<in> M}\<close> \<open>d = Inf {\<parallel>x\<parallel>\<^sup>2 |x. x \<in> M}\<close> cInf_lower power2_norm_eq_cinner')
      qed
      have  \<open>\<forall> n::nat. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + 1/(n+1)\<close>
      proof-
        have \<open>\<forall> \<epsilon> > 0. \<exists> t \<in> { \<parallel>x\<parallel>^2 | x. x \<in> M }.  t < d + \<epsilon>\<close>
          using \<open>d = Inf { \<parallel>x\<parallel>^2 | x. x \<in> M }\<close>  \<open>{ \<parallel>x\<parallel>^2 | x. x \<in> M } \<noteq> {}\<close>  \<open>bdd_below  { \<parallel>x\<parallel>^2 | x. x \<in> M }\<close>
          by (meson cInf_lessD less_add_same_cancel1)
        hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + \<epsilon>\<close>
          by auto    
        hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + \<epsilon>\<close>
          by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close>)
        thus ?thesis by auto
      qed
      then obtain r::\<open>nat \<Rightarrow> 'a::chilbert_space\<close> where \<open>\<forall> n. r n \<in> M \<and>  \<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
        by metis
      have \<open>\<forall> n. r n \<in> M\<close> 
        by (simp add: \<open>\<forall>n. r n \<in> M \<and>  \<parallel>r n\<parallel>\<^sup>2 < d + 1 / (real n + 1)\<close>)
      have \<open>\<forall> n. \<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
        by (simp add: \<open>\<forall>n. r n \<in> M \<and> \<parallel>r n\<parallel>\<^sup>2 < d + 1 / (real n + 1)\<close>)    
      have \<open>\<parallel> (r n) - (r m) \<parallel>^2 < 2*(1/(n+1) + 1/(m+1))\<close> for m n 
      proof-
        have \<open> \<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
          by (metis \<open>\<forall>n. r n \<in> M \<and> \<parallel>r n\<parallel>\<^sup>2 < d + 1 / (real n + 1)\<close>  of_nat_1 of_nat_add)
        have \<open> \<parallel> r m \<parallel>^2 < d + 1/(m+1)\<close>
          by (metis \<open>\<forall>n. r n \<in> M \<and> \<parallel>r n\<parallel>\<^sup>2 < d + 1 / (real n + 1)\<close>  of_nat_1 of_nat_add)
        have \<open>(r n) \<in> M\<close> 
          by (simp add: \<open>\<forall>n. r n \<in> M\<close>)
        moreover have \<open>(r m) \<in> M\<close> 
          by (simp add: \<open>\<forall>n. r n \<in> M\<close>)
        ultimately have \<open>(1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<in> M\<close>
          using \<open>convex M\<close> 
          by (simp add: convexD)
        hence \<open> \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2 \<ge> d\<close>
          by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close>)
        have \<open>\<parallel> (1/2) *\<^sub>R (r n) - (1/2) *\<^sub>R (r m) \<parallel>^2
              = (1/2)*( \<parallel> r n \<parallel>^2 + \<parallel> r m \<parallel>^2 ) - \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2\<close> 
          using  ParallelogramLawVersion1 
          by (simp add: ParallelogramLawVersion1 scaleR_scaleC)
        also have  \<open>...  
              < (1/2)*( d + 1/(n+1) + \<parallel> r m \<parallel>^2 ) - \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2\<close>
          using \<open>\<parallel>r n\<parallel>\<^sup>2 < d + 1 / real (n + 1)\<close> by auto
        also have  \<open>...  
              < (1/2)*( d + 1/(n+1) + d + 1/(m+1) ) - \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2\<close>
          using \<open>\<parallel>r m\<parallel>\<^sup>2 < d + 1 / real (m + 1)\<close> by auto
        also have  \<open>...  
              \<le> (1/2)*( d + 1/(n+1) + d + 1/(m+1) ) - d\<close>
          by (simp add: \<open>d \<le> \<parallel>(1 / 2) *\<^sub>R r n + (1 / 2) *\<^sub>R r m\<parallel>\<^sup>2\<close>)
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
        finally have \<open> \<parallel>(1 / 2) *\<^sub>R r n - (1 / 2) *\<^sub>R r m\<parallel>\<^sup>2 < 1 / 2 * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by blast
        hence \<open> \<parallel>(1 / 2) *\<^sub>R (r n - r m) \<parallel>\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by (simp add: scale_right_diff_distrib)
        hence \<open> ((1 / 2)*\<parallel> (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by simp
        hence \<open> (1 / 2)^2*(\<parallel> (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by (metis power_mult_distrib)
        hence \<open> (1 / 4) *(\<parallel> (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by (simp add: power_divide)
        hence \<open> \<parallel> (r n - r m) \<parallel>\<^sup>2 < 2 * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by simp
        thus ?thesis 
          by (metis of_nat_1 of_nat_add)
      qed
      hence  \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> \<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2\<close> for \<epsilon>
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
        hence \<open> n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> \<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2\<close> for m n::nat
          by (smt \<open>\<And>n m. \<parallel>r n - r m\<parallel>\<^sup>2 < 2 * (1 / (real n + 1) + 1 / (real m + 1))\<close> of_nat_1 of_nat_add)
        thus ?thesis 
          by blast
      qed
      hence  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> \<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2\<close>
        by blast
      hence  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> \<parallel> (r n) - (r m) \<parallel> < \<epsilon>\<close>
        by (meson less_eq_real_def power_less_imp_less_base)
      hence \<open>Cauchy r\<close>
        using CauchyI by fastforce
      then obtain k where \<open>r \<longlonglongrightarrow> k\<close>
        using  convergent_eq_Cauchy by auto
      have \<open>k \<in> M\<close> using \<open>closed M\<close>
        using \<open>\<forall>n. r n \<in> M\<close> \<open>r \<longlonglongrightarrow> k\<close> closed_sequentially by auto
      have  \<open>(\<lambda> n.  \<parallel> r n \<parallel>^2) \<longlonglongrightarrow>  \<parallel> k \<parallel>^2\<close>
        by (simp add: \<open>r \<longlonglongrightarrow> k\<close> tendsto_norm tendsto_power)
      moreover  have  \<open>(\<lambda> n.  \<parallel> r n \<parallel>^2) \<longlonglongrightarrow>  d\<close>
      proof-
        have \<open>\<bar>\<parallel> r n \<parallel>^2 - d\<bar> < 1/(n+1)\<close> for n :: nat
          by (smt \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close> \<open>\<forall>n. r n \<in> M \<and> \<parallel>r n\<parallel>\<^sup>2 < d + 1 / (real n + 1)\<close> of_nat_1 of_nat_add)
        moreover have \<open>(\<lambda>n. 1 / real (n + 1)) \<longlonglongrightarrow> 0\<close> 
          using  LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1] by blast        
        ultimately have \<open>(\<lambda> n. \<bar>\<parallel> r n \<parallel>^2 - d\<bar> ) \<longlonglongrightarrow> 0\<close> 
          by (simp add: LIMSEQ_norm_0)
        hence \<open>(\<lambda> n. \<parallel> r n \<parallel>^2 - d ) \<longlonglongrightarrow> 0\<close> 
          by (simp add: tendsto_rabs_zero_iff)
        moreover have \<open>(\<lambda> n. d ) \<longlonglongrightarrow> d\<close>
          by simp
        ultimately have \<open>(\<lambda> n. (\<parallel> r n \<parallel>^2 - d)+d ) \<longlonglongrightarrow> 0+d\<close> 
          using tendsto_add by fastforce
        thus ?thesis by simp
      qed
      ultimately have \<open>d = \<parallel> k \<parallel>^2\<close>
        using LIMSEQ_unique by auto
      hence \<open>t \<in> M \<Longrightarrow> \<parallel> k \<parallel>^2 \<le> \<parallel> t \<parallel>^2\<close> for t
        using \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close> by auto
      thus ?thesis using \<open>k \<in> M\<close>
        unfolding is_arg_min_on_def
        using is_arg_min_def \<open>d = \<parallel>k\<parallel>\<^sup>2\<close>
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
    have \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2
      = (1/2)*( \<parallel>r\<parallel>^2 + \<parallel>s\<parallel>^2 ) - \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>^2\<close> 
      using  ParallelogramLawVersion1 
      by (simp add: ParallelogramLawVersion1 scaleR_scaleC)
    moreover have \<open>\<parallel>r\<parallel>^2 \<le> \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>^2\<close>
    proof-
      have \<open>r \<in> M\<close> 
        using \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close>
        by (simp add: is_arg_min_def is_arg_min_on_def)
      moreover have \<open>s \<in> M\<close> 
        using \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>
        by (simp add: is_arg_min_def is_arg_min_on_def)
      ultimately have \<open>((1/2) *\<^sub>R r + (1/2) *\<^sub>R s) \<in> M\<close> using \<open>convex M\<close>
        by (simp add: convexD)
      hence \<open> \<parallel>r\<parallel> \<le> \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>\<close>
        using  \<open>is_arg_min_on norm M r\<close>
        unfolding is_arg_min_on_def
        by (smt is_arg_min_def)
      thus ?thesis
        using norm_ge_zero power_mono by blast
    qed
    moreover have \<open>\<parallel>r\<parallel> = \<parallel>s\<parallel>\<close>
    proof-
      have \<open>\<parallel>r\<parallel> \<le> \<parallel>s\<parallel>\<close> 
        using  \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close> \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>  is_arg_min_def 
        unfolding is_arg_min_on_def
        by smt
      moreover have \<open>\<parallel>s\<parallel> \<le> \<parallel>r\<parallel>\<close>
        using  \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close> \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>  is_arg_min_def 
        unfolding is_arg_min_on_def
        by smt
      ultimately show ?thesis by simp
    qed
    ultimately have \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2 \<le> 0\<close>
      by simp
    hence \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2 = 0\<close>
      by simp
    hence \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel> = 0\<close>
      by auto
    hence \<open>(1/2) *\<^sub>R r - (1/2) *\<^sub>R s = 0\<close>
      using norm_eq_zero by blast
    thus ?thesis by simp
  qed
  ultimately show ?thesis 
    by auto
qed

lemma TransClosed:
  \<open>closed (S::('a::{topological_ab_group_add,t2_space,first_countable_topology}) set) 
\<Longrightarrow> closed {s + h| s. s \<in> S}\<close>
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

\<comment> \<open>Theorem 2.5 in @{cite conway2013course}\<close> 
theorem existence_uniqueness_min_dist:
  fixes M::\<open>('a::chilbert_space) set\<close> and h::'a 
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>! k. is_arg_min_on (\<lambda> x. dist x h) M k\<close>
proof-
  include notation_norm 
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
      have \<open>(\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k\<parallel> \<le> \<parallel>t\<parallel>) \<and> k \<in> {m - h |m. m \<in> M}\<close>
        using is_arg_min_def  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h| m. m \<in> M} k\<close>
        unfolding is_arg_min_on_def
        by smt
      hence \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k\<parallel> \<le> \<parallel>t\<parallel>\<close>
        by blast
      hence \<open>\<forall>t. t + h \<in> M \<longrightarrow> \<parallel>k\<parallel> \<le> \<parallel>t\<parallel>\<close>
        by auto
      hence \<open>\<forall>t. t \<in> M \<longrightarrow> \<parallel>k\<parallel> \<le> \<parallel>t - h\<parallel>\<close>
        by auto
      hence \<open>\<forall>t. t \<in> M \<longrightarrow> \<parallel>(k+h)-h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>
        by auto
      from \<open>(\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k\<parallel> \<le> \<parallel>t\<parallel>) \<and> k \<in> {m - h |m. m \<in> M}\<close>
      have  \<open>k \<in> {m - h |m. m \<in> M}\<close>
        by blast
      hence  \<open>k + h \<in> M\<close>
        by auto
      have \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) {m| m. m \<in> M} (k + h)\<close>
      proof-
        have \<open>\<nexists>y. y \<in> {m |m. m \<in> M} \<and> \<parallel>y - h\<parallel> < \<parallel>(k + h) - h\<parallel>\<close>
          using \<open>\<forall>t. t \<in> M \<longrightarrow> \<parallel>(k+h)-h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>  
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
        assume \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  k\<close>
        hence \<open>\<forall>t. t \<in> M \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>
          unfolding is_arg_min_on_def
          by (meson is_arg_min_linorder)
        hence \<open>\<forall>t. t - h \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>
          by auto
        hence \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t\<parallel>\<close>
          by blast
        have \<open>k \<in> M\<close>
          using  \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  k \<close>
          unfolding is_arg_min_on_def
          using is_arg_min_def
          by (simp add: is_arg_min_linorder)
        hence \<open>k - h \<in> {m - h |m. m \<in> M}\<close>
          by auto
        have  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h |m. m \<in> M} (k - h)\<close>
          using  \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t\<parallel>\<close>
            \<open>k - h \<in> {m - h |m. m \<in> M}\<close>
            is_arg_min_def
          unfolding is_arg_min_on_def
          by smt
        thus ?thesis by blast
      qed
      assume \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M k\<close>
      hence  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>)  {m - h |m. m \<in> M} (k - h)\<close>
        by (simp add: \<open>\<And>k. is_arg_min_on (\<lambda>x. \<parallel>x - h\<parallel>) M k \<Longrightarrow> is_arg_min_on norm {m - h |m. m \<in> M} (k - h)\<close>)
      assume  \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M t\<close> 
      hence  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>)  {m - h |m. m \<in> M} (t - h)\<close>
        using \<open>\<And>k. is_arg_min_on (\<lambda>x. \<parallel>x - h\<parallel>) M k \<Longrightarrow> is_arg_min_on norm {m - h |m. m \<in> M} (k - h)\<close> by auto
      show ?thesis 
        by (metis (no_types, lifting) \<open>\<exists>!k. is_arg_min_on norm {m - h |m. m \<in> M} k\<close> \<open>is_arg_min_on norm {m - h |m. m \<in> M} (k - h)\<close> \<open>is_arg_min_on norm {m - h |m. m \<in> M} (t - h)\<close> diff_add_cancel)
    qed
    ultimately show ?thesis by blast
  qed
  moreover have \<open>(\<lambda> x. dist x h) = (\<lambda> x. \<parallel>x - h\<parallel>)\<close>
    by (simp add: dist_norm)
  ultimately show ?thesis by simp
qed


\<comment> \<open>Theorem 2.6 in @{cite conway2013course}\<close> 
theorem dist_min_ortho:
  fixes M::\<open>('a::chilbert_space) set\<close> and h k::'a 
  assumes \<open>is_subspace M\<close>
  shows  \<open>(is_arg_min_on (\<lambda> x. dist x h) M k) \<longleftrightarrow> h - k \<in> (orthogonal_complement M) \<and> k \<in> M\<close>
proof-
  include notation_norm
  have \<open>is_arg_min_on (\<lambda> x. dist x h) M k
     \<Longrightarrow>  h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
  proof-
    assume \<open>is_arg_min_on (\<lambda> x. dist x h) M k\<close>
    hence  \<open>k \<in> M\<close>
      unfolding is_arg_min_on_def
      by (simp add: is_arg_min_def)
    moreover have \<open>h - k \<in> orthogonal_complement M\<close>
    proof-
      have \<open>f \<in> M \<Longrightarrow> \<langle> h - k , f \<rangle> = 0\<close> for f
      proof-
        assume \<open>f \<in> M\<close>
        hence  \<open>\<forall> c. c *\<^sub>R f \<in> M\<close>
          by (simp add: assms is_linear_manifold.smult_closed is_subspace.subspace scaleR_scaleC)
        have \<open>f \<in> M \<Longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> \<parallel> f \<parallel>^2\<close> for f
        proof-
          assume \<open>f \<in>  M\<close>             
          hence \<open>k + f \<in>  M\<close> 
            by (simp add: assms calculation is_linear_manifold.additive_closed is_subspace.subspace)
          hence \<open>dist h k \<le> dist  h (k + f)\<close>
          proof -
            have "\<forall>f A a aa. \<not> is_arg_min_on f A (a::'a) \<or> (f a::real) \<le> f aa \<or> aa \<notin> A"
              by (metis (no_types) is_arg_min_linorder is_arg_min_on_def)
            then have "dist k h \<le> dist (f + k) h"
              by (metis \<open>is_arg_min_on (\<lambda>x. dist x h) M k\<close> \<open>k + f \<in> M\<close> add.commute)
            then show ?thesis
              by (simp add: add.commute dist_commute)
          qed
          hence \<open>\<parallel> h - k \<parallel> \<le> \<parallel> h - (k + f) \<parallel>\<close>
            by (simp add: dist_norm)
          hence \<open>\<parallel> h - k \<parallel>^2 \<le> \<parallel> h - (k + f) \<parallel>^2\<close>
            by (simp add: power_mono)
          also have \<open>... \<le> \<parallel> (h - k) - f \<parallel>^2\<close>
            by (simp add: diff_diff_add)
          also have \<open>... \<le> \<parallel> (h - k) \<parallel>^2 + \<parallel> f \<parallel>^2 -  2 * Re (\<langle> h - k , f \<rangle>)\<close>
            by (simp add: polarization_identity_minus)
          finally have \<open>\<parallel> (h - k) \<parallel>^2 \<le> \<parallel> (h - k) \<parallel>^2 + \<parallel> f \<parallel>^2 -  2 * Re (\<langle> h - k , f \<rangle>)\<close>
            by simp
          thus ?thesis by simp
        qed
        hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> \<parallel> f \<parallel>^2\<close>
          by blast
        hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (\<langle> h - k , f \<rangle>) = 0\<close>
        proof-
          have \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real.  2 * Re (\<langle> h - k , c *\<^sub>R f \<rangle>) \<le> \<parallel> c *\<^sub>R f \<parallel>^2)\<close>
            by (metis \<open>\<And>f. f \<in> M \<Longrightarrow> 2 * Re (\<langle>(h - k) , f\<rangle>) \<le> \<parallel>f\<parallel>\<^sup>2\<close> assms is_linear_manifold.smult_closed is_subspace.subspace scaleR_scaleC)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (\<langle> h - k , f \<rangle>)) \<le> \<parallel> c *\<^sub>R f \<parallel>^2)\<close>
            by (metis Re_complex_of_real cinner_scaleC_right complex_add_cnj complex_cnj_complex_of_real complex_cnj_mult of_real_mult scaleR_scaleC semiring_normalization_rules(34))
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (\<langle> h - k , f \<rangle>)) \<le> \<bar>c\<bar>^2*\<parallel> f \<parallel>^2)\<close>
            by (simp add: power_mult_distrib)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c * (2 * Re (\<langle> h - k , f \<rangle>)) \<le> c^2*\<parallel> f \<parallel>^2)\<close>
            by auto
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> c * (2 * Re (\<langle> h - k , f \<rangle>)) \<le> c^2*\<parallel> f \<parallel>^2)\<close>
            by simp
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> c*(2 * Re (\<langle> h - k , f \<rangle>)) \<le> c*(c*\<parallel> f \<parallel>^2))\<close>
            by (simp add: power2_eq_square)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> c*\<parallel> f \<parallel>^2)\<close>
            by simp 
          have \<open>f \<in>  M \<Longrightarrow> \<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> 0\<close> for f
          proof-
            assume \<open>f \<in>  M\<close> 
            hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k , f \<rangle>) \<le> c*\<parallel> f \<parallel>^2\<close>
              by (simp add: \<open>\<forall>f. f \<in> M \<longrightarrow> (\<forall>c>0. 2 * Re \<langle>h - k , f\<rangle> \<le> c * \<parallel>f\<parallel>\<^sup>2)\<close>)
            hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k , f \<rangle>) \<le> c\<close>
            proof (cases \<open>\<parallel> f \<parallel>^2 > 0\<close>)
              case True
              hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k , f \<rangle>) \<le> (c/\<parallel> f \<parallel>^2)*\<parallel> f \<parallel>^2\<close>
                using \<open>\<forall>c>0. 2 * Re (\<langle>h - k , f\<rangle> ) \<le> c * \<parallel>f\<parallel>\<^sup>2\<close> linordered_field_class.divide_pos_pos by blast
              then show ?thesis 
                using True by auto
            next
              case False
              hence \<open>\<parallel> f \<parallel>^2 = 0\<close> 
                by simp
              then show ?thesis 
                by auto
            qed
            thus ?thesis 
              by smt
          qed
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> 0)\<close>
            by simp
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> (2 * Re (\<langle> h - k , (-1) *\<^sub>R f \<rangle>)) \<le> 0)\<close>
            by (metis assms is_linear_manifold.smult_closed is_subspace.subspace scaleR_scaleC)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> -(2 * Re (\<langle> h - k , f \<rangle>)) \<le> 0)\<close>
            by simp
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<ge> 0)\<close>
            by simp
          hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) = 0)\<close>
            using  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> (2 * Re (\<langle> h - k , f \<rangle>)) \<le> 0)\<close>
            by fastforce
          hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) = 0\<close>
          proof-
            have \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                 ((1::real) > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) = 0)\<close>
              using \<open>\<forall>f. f \<in>  M \<longrightarrow> (\<forall>c>0. 2 * Re (\<langle>h - k , f\<rangle> ) = 0)\<close> by blast
            thus ?thesis by auto
          qed
          thus ?thesis by simp
        qed
        also have \<open>\<forall> f. f \<in>  M \<longrightarrow> Im (\<langle> h - k , f \<rangle>) = 0\<close>
        proof-
          have  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (\<langle> h - k , (Complex 0 (-1)) *\<^sub>C f \<rangle>) = 0\<close>
            using assms calculation  is_linear_manifold.smult_closed is_subspace.subspace by blast
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re ( (Complex 0 (-1))*(\<langle> h - k , f \<rangle>) ) = 0\<close>
            by simp
          thus ?thesis 
            using Complex_eq_neg_1 Re_i_times cinner_scaleC_right complex_of_real_def by auto
        qed
        ultimately have \<open>\<forall> f. f \<in>  M \<longrightarrow> (\<langle> h - k , f \<rangle>) = 0\<close>
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
      have \<open>\<parallel> h - f \<parallel>^2 = \<parallel> (h - k) + (k - f) \<parallel>^2\<close>
        by simp
      also have \<open>... = \<parallel> h - k \<parallel>^2 + \<parallel> k - f \<parallel>^2\<close>
        using  \<open>h - k \<bottom> k - f\<close> PythagoreanId 
        using is_orthogonal_def by blast
      also have \<open>... \<ge> \<parallel> h - k \<parallel>^2\<close>
        by simp
      finally have \<open>\<parallel>h - k\<parallel>\<^sup>2 \<le> \<parallel>h - f\<parallel>\<^sup>2 \<close>
        by blast
      hence \<open>\<parallel>h - k\<parallel> \<le> \<parallel>h - f\<parallel>\<close>
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
  \<open>is_subspace M \<Longrightarrow> convex M\<close> 
proof-
  assume \<open>is_subspace M\<close>
  hence \<open>\<forall>x\<in>M. \<forall>y\<in> M. \<forall>u. \<forall>v. u *\<^sub>C x + v *\<^sub>C y \<in>  M\<close>
    by (simp add: is_linear_manifold.additive_closed is_linear_manifold.smult_closed is_subspace.subspace)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u::real. \<forall>v::real. u *\<^sub>R x + v *\<^sub>R y \<in> M\<close>
    by (simp add: scaleR_scaleC)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in>M\<close>
    by blast
  thus ?thesis using convex_def by blast
qed

corollary ExistenceUniquenessProj:
  fixes M :: \<open>('a::chilbert_space) set\<close> 
  assumes \<open>is_subspace M\<close>
  shows  \<open>\<forall> h. \<exists>! k. (h - k) \<in> orthogonal_complement M \<and> k \<in> M\<close>
proof-  
  have \<open>0 \<in> M\<close> 
    using  \<open>is_subspace M\<close>
    by (simp add: is_linear_manifold.zero is_subspace.subspace)
  hence \<open>M \<noteq> {}\<close> by blast
  have \<open>closed  M\<close>
    using  \<open>is_subspace M\<close>
    by (simp add: is_subspace.closed)
  have \<open>convex  M\<close>
    using  \<open>is_subspace M\<close>
    by (simp add: SubspaceConvex)
  have \<open>\<forall> h. \<exists>! k.  is_arg_min_on (\<lambda> x. dist x h) M k\<close>
    by (simp add: existence_uniqueness_min_dist \<open>closed M\<close> \<open>convex M\<close> \<open>M \<noteq> {}\<close>)
  thus ?thesis
    using dist_min_ortho 
    by (smt Collect_cong Collect_empty_eq_bot existence_uniqueness_min_dist \<open>M \<noteq> {}\<close> \<open>closed M\<close> \<open>convex M\<close> assms bot_set_def empty_Collect_eq empty_Diff insert_Diff1 insert_compr  is_subspace_orthog orthogonal_complement_def set_diff_eq singleton_conv2 someI_ex)
qed

definition proj :: \<open>('a::complex_inner) set \<Rightarrow> (('a::complex_inner) \<Rightarrow> ('a::complex_inner))\<close> where
  \<open>proj \<equiv> \<lambda> M. \<lambda> h. THE k. ((h - k) \<in> (orthogonal_complement M) \<and> k \<in>  M)\<close>

lemma proj_intro1:
  \<open>is_subspace M  \<Longrightarrow> h - (proj M) h \<in> orthogonal_complement M\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
  by (metis (no_types, lifting) Complex_Inner_Product.proj_def ExistenceUniquenessProj theI)

lemma proj_intro2:
  \<open>is_subspace M  \<Longrightarrow> (proj M) h \<in> M\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
  by (metis (no_types, lifting) Complex_Inner_Product.proj_def ExistenceUniquenessProj theI)

lemma proj_uniq:
  fixes  M :: \<open>('a::chilbert_space) set\<close>
  assumes  \<open>is_subspace M\<close> and \<open>h - x \<in> orthogonal_complement M\<close> and \<open>x \<in> M\<close>
  shows \<open>(proj M) h = x\<close>
  by (smt ExistenceUniquenessProj add.commute assms(1) assms(2) assms(3) orthogonal_complement_def proj_intro1 proj_intro2 uminus_add_conv_diff)

lemma proj_fixed_points:                         
  \<open>is_subspace M  \<Longrightarrow> x \<in> M \<Longrightarrow> (proj M) x = x\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
  by (simp add: is_linear_manifold.zero is_subspace.subspace proj_uniq)

lemma bounded_linear_continuous:
  assumes \<open>bounded_clinear f\<close> 
  shows \<open>isCont f x\<close>
  by (simp add: assms bounded_clinear.bounded_linear linear_continuous_at)

\<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close> 
proposition projPropertiesB:
  includes notation_norm
  fixes M :: \<open>('a::chilbert_space) set\<close>
  shows \<open>is_subspace M  \<Longrightarrow> \<parallel> (proj M) h \<parallel> \<le> \<parallel> h \<parallel>\<close>
proof-
  assume \<open>is_subspace M\<close>
  hence \<open>h - (proj M) h \<in> orthogonal_complement M\<close> 
    by (simp add: proj_intro1)
  hence \<open>\<forall> k \<in>  M.  (h - (proj M) h) \<bottom> k\<close>
    by (simp add: orthogonal_complement_def)
  hence \<open>\<forall> k \<in> M. \<langle>  h - (proj M) h , k \<rangle> = 0\<close>
    using is_orthogonal_def by blast
  also have \<open>(proj M) h \<in>  M\<close>
    using  \<open>is_subspace M\<close>
    by (simp add: proj_intro2)
  ultimately have \<open>\<langle>  h - (proj M) h , (proj M) h \<rangle> = 0\<close>
    by auto
  hence \<open>\<parallel> (proj M) h \<parallel>^2 + \<parallel> h - (proj M) h \<parallel>^2 = \<parallel> h \<parallel>^2\<close>
    using PythagoreanId by fastforce
  hence \<open>\<parallel> (proj M) h \<parallel>^2 \<le> \<parallel> h \<parallel>^2\<close>
    by (smt zero_le_power2)    
  thus ?thesis 
    using norm_ge_zero power2_le_imp_le by blast
qed

\<comment> \<open>Theorem 2.7 (version) in @{cite conway2013course}\<close> 
theorem projPropertiesA:
  \<open>is_subspace M \<Longrightarrow> bounded_clinear (proj M)\<close> 
  for M :: \<open>('a::chilbert_space) set\<close>
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
      using \<open>is_subspace  M \<close> is_linear_manifold.smult_closed is_subspace.subspace by blast
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
      by (simp add: \<open>is_subspace (orthogonal_complement M)\<close> is_linear_manifold.smult_closed is_subspace.subspace)
    hence \<open>\<forall> x. \<forall> t.  t *\<^sub>C x - t *\<^sub>C ((proj M) x) \<in> orthogonal_complement M\<close>
      by (simp add: complex_vector.scale_right_diff_distrib)
    from  \<open>\<forall> x. \<forall> t. t *\<^sub>C x - (proj M) (t *\<^sub>C x) \<in> orthogonal_complement M\<close>
      \<open>\<forall> x. \<forall> t.  t *\<^sub>C x - t *\<^sub>C ((proj M) x) \<in> orthogonal_complement M\<close>
    have \<open>\<forall> x. \<forall> t. (t *\<^sub>C x - t *\<^sub>C ((proj M) x)) - (t *\<^sub>C x - (proj M) (t *\<^sub>C x)) \<in> orthogonal_complement M\<close>
      by (metis \<open>\<forall>x t. t *\<^sub>C proj M x \<in> M\<close> \<open>is_subspace (orthogonal_complement M)\<close> \<open>is_subspace M\<close> diff_self is_linear_manifold.zero is_subspace.subspace proj_uniq)
    hence \<open>\<forall> x. \<forall> t. (proj M) (t *\<^sub>C x) - t *\<^sub>C ((proj M) x) \<in> orthogonal_complement M\<close>
      by simp
    moreover have \<open>\<forall> x. \<forall> t. (proj M) (t *\<^sub>C x) - t *\<^sub>C ((proj M) x) \<in>  M\<close>         
      using  \<open>\<forall> x. \<forall> t.  t *\<^sub>C ((proj M) x) \<in>  M\<close>  \<open>\<forall> x. \<forall> t. ((proj M) (t *\<^sub>C x)) \<in>  M\<close>
      by (metis \<open>is_subspace M\<close> \<open>\<forall>x t. t *\<^sub>C x - t *\<^sub>C proj M x \<in> (orthogonal_complement M)\<close> cancel_comm_monoid_add_class.diff_cancel is_linear_manifold.zero is_subspace.subspace proj_uniq)
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
      by (simp add: \<open>is_subspace M\<close>  is_linear_manifold.additive_closed is_subspace.subspace)
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
      by (simp add: \<open>is_subspace (orthogonal_complement M)\<close> add_diff_add is_linear_manifold.additive_closed is_subspace.subspace)
    from  \<open>\<forall> x. \<forall> y. (x + y) - ((proj M) x + (proj M) y) \<in>  orthogonal_complement M\<close>
      \<open>\<forall> x. \<forall> y. (x + y) - ((proj M) (x + y)) \<in>  orthogonal_complement M\<close>
    have  \<open>\<forall> x. \<forall> y. ( (x + y) - ((proj M) x + (proj M) y) ) - ( (x + y) - ((proj M) (x + y)) ) \<in>  orthogonal_complement M\<close>
      by (metis \<open>\<forall>x y. proj M x + proj M y \<in> M\<close> \<open>is_subspace M\<close> cancel_comm_monoid_add_class.diff_cancel proj_fixed_points proj_uniq)
    hence \<open>\<forall> x. \<forall> y. (proj M) (x + y) -  ((proj M) x + (proj M) y) \<in> orthogonal_complement M\<close>
      by (metis (no_types, lifting) add_diff_cancel_left diff_minus_eq_add uminus_add_conv_diff)
    moreover have \<open>\<forall> x. \<forall> y. (proj M) (x + y) -  ((proj M) x + (proj M) y) \<in> M\<close>       
      by (metis \<open>is_subspace M\<close> \<open>\<forall>x y. proj M x + proj M y \<in> M\<close> \<open>\<forall>x y. x + y - (proj M x + proj M y) \<in> (orthogonal_complement M)\<close> cancel_comm_monoid_add_class.diff_cancel is_linear_manifold.zero is_subspace.subspace proj_uniq)
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

\<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close> 
proposition projPropertiesC:
  \<open>is_subspace M \<Longrightarrow> (proj M) \<circ> (proj M) = proj M\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
  using proj_fixed_points proj_intro2 by fastforce

definition ker_op :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 'a set\<close> where
  \<open>ker_op \<equiv> \<lambda> f. {x. f x = 0}\<close>

lemma ker_op_lin:
  \<open>bounded_clinear f \<Longrightarrow> is_subspace  (ker_op f)\<close>
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
    by (smt Collect_cong is_linear_manifold.intro mem_Collect_eq)
qed

\<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close> 
proposition projPropertiesD:
  \<open>is_subspace M  \<Longrightarrow> ker_op  (proj M) = (orthogonal_complement M)\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
proof-
  assume \<open>is_subspace M\<close> 
  have \<open>x \<in> orthogonal_complement M \<Longrightarrow> x \<in>  (ker_op  (proj M))\<close> for x
  proof-
    assume \<open>x \<in> orthogonal_complement M\<close>
    hence \<open>(proj M) x = 0\<close>
      using  \<open>is_subspace M\<close>
      by (simp add: is_linear_manifold.zero is_subspace.subspace proj_uniq)
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

(* TODO: already exists: "range" *)
definition ran_op :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 'b set\<close> where
  \<open>ran_op \<equiv> \<lambda> f. {x. \<exists> y. f y = x}\<close>

lemma ran_op_lin:
  \<open>clinear f \<Longrightarrow>  is_linear_manifold (ran_op f)\<close>
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
    using \<open>A = ran_op f\<close> \<open>\<And>x c. x \<in> A \<Longrightarrow> c *\<^sub>C x \<in> A\<close> \<open>\<And>y x. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> x + y \<in> A\<close> is_linear_manifold.intro by blast
qed

\<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close> 
theorem projPropertiesE:
  \<open>is_subspace M \<Longrightarrow> ran_op  (proj M) = M\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
proof-
  assume \<open>is_subspace M\<close>
  have \<open>x \<in> ran_op  (proj M) \<Longrightarrow> x \<in> M\<close> for x
    by (smt \<open>is_subspace M\<close> mem_Collect_eq proj_intro2 ran_op_def)
  moreover have \<open>x \<in> M \<Longrightarrow> x \<in> ran_op  (proj M)\<close> for x
    by (metis (mono_tags, lifting) \<open>is_subspace M\<close> mem_Collect_eq proj_fixed_points ran_op_def)
  ultimately show ?thesis by blast
qed

lemma pre_ortho_twice: "is_linear_manifold M \<Longrightarrow> M \<subseteq> (orthogonal_complement (orthogonal_complement M)) " 
proof-
  have \<open>x \<in> M \<Longrightarrow> x \<in> (orthogonal_complement (orthogonal_complement M))\<close> for x 
  proof-
    assume \<open>x \<in> M\<close>
    hence \<open>\<forall> y \<in> (orthogonal_complement M). x \<bottom> y\<close>
      by (simp add: orthogonal_comm orthogonal_complement_def)
    hence \<open>x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      by (simp add: orthogonal_complement_def)
    thus ?thesis by blast
  qed            
  thus ?thesis 
    by (simp add: subsetI)
qed

\<comment> \<open>Exercice 2 (section 2, chapter I) in  @{cite conway2013course}\<close> 
lemma ProjOntoOrtho:
  \<open>is_subspace M  \<Longrightarrow> id - proj M = proj (orthogonal_complement M) \<close>
  for M :: \<open>('a::chilbert_space) set\<close>
proof-
  assume \<open>is_subspace M\<close>
  have   \<open> (id -  proj M) x = (proj ((orthogonal_complement M))) x \<close> for x
  proof-
    have \<open>x - (proj M) x \<in> orthogonal_complement M\<close>
      using \<open>is_subspace M\<close> proj_intro1 by auto
    hence \<open>(id -  proj M) x \<in> orthogonal_complement M\<close>
      by simp
    have \<open>(proj M) x \<in>  M\<close> 
      by (simp add: \<open>is_subspace M\<close> proj_intro2)
    hence  \<open>x - (id - proj M) x \<in>  M\<close>
      by simp
    hence \<open>(proj M) x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      using pre_ortho_twice  \<open>is_subspace M\<close>  \<open>(proj M) x \<in>  M\<close>  is_subspace.subspace by blast
    hence  \<open>x - (id -  proj M) x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      by simp
    thus ?thesis
      by (metis \<open>(id - proj M) x \<in> orthogonal_complement M\<close> \<open>is_subspace M\<close>   is_subspace_orthog  proj_uniq)
  qed
  thus ?thesis by blast
qed

\<comment> \<open>Corollary 2.8 in  @{cite conway2013course}\<close> 
theorem orthogonal_complement_twice:
 "is_subspace M \<Longrightarrow> (orthogonal_complement (orthogonal_complement M)) = M"
  for M :: \<open>('a::chilbert_space) set\<close>
proof-
  assume \<open>is_subspace M\<close>
  have \<open>(orthogonal_complement (orthogonal_complement M)) = ker_op (proj (orthogonal_complement M))\<close>
    by (simp add: \<open>is_subspace M\<close> projPropertiesD)
  also have \<open>... = ker_op ( id - (proj M) )\<close>
    by (simp add: ProjOntoOrtho \<open>is_subspace M\<close>)
  also have \<open>... = M\<close>
  proof-
    have \<open>x \<in>  M \<Longrightarrow> x \<in>  ( ker_op ( id - (proj M) ) )\<close> for x
    proof-
      assume \<open>x \<in> M\<close>
      hence \<open>(proj M) x = x\<close>
        using \<open>is_subspace M\<close> proj_fixed_points by auto
      hence \<open>(id - (proj M)) x = 0\<close> 
        by simp
      hence \<open>x \<in> {v. (id - (proj M)) v = 0}\<close>
        by simp
      hence \<open>x \<in>  (span {v. (id - (proj M)) v = 0})\<close>
        using span_superset 
        by fastforce
      hence \<open>x \<in> ( ker_op ( id - (proj M) ) )\<close> 
        by (metis ProjOntoOrtho \<open>(id - proj M) x = 0\<close> \<open>is_subspace M\<close> calculation diff_zero is_subspace_orthog proj_intro1)
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
        by (metis \<open>is_subspace M\<close> proj_intro2)
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
  fixes  A B :: \<open>('a::chilbert_space) set\<close>
  assumes \<open>is_subspace A\<close> and  \<open>is_subspace B\<close>
  shows \<open>(orthogonal_complement A) \<subseteq> (orthogonal_complement B) \<longleftrightarrow> A \<supseteq> B\<close>
proof-
  have \<open>A \<supseteq> B \<Longrightarrow> (orthogonal_complement A) \<subseteq> (orthogonal_complement B)\<close>
    by (simp add: orthogonal_complement_def subset_eq)
  moreover have  \<open> (orthogonal_complement A) \<subseteq> (orthogonal_complement B) \<Longrightarrow> (orthogonal_complement (orthogonal_complement A)) \<supseteq> (orthogonal_complement (orthogonal_complement B))\<close>
    by (simp add: orthogonal_complement_def subset_eq)
  moreover have \<open>A =  (orthogonal_complement (orthogonal_complement A))\<close> 
    by (simp add: orthogonal_complement_twice assms(1))
  moreover have \<open>B =  (orthogonal_complement (orthogonal_complement B))\<close> 
    by (simp add: orthogonal_complement_twice assms(2))
  ultimately show ?thesis 
    by blast
qed

lemma ortho_top[simp]: 
  " (orthogonal_complement (top::('a::chilbert_space) set)) 
= ({0}::('a::chilbert_space) set)"
proof-
  have \<open>({0}::('a::chilbert_space) set) \<subseteq>  (orthogonal_complement (top::('a::chilbert_space) set))\<close>
    by (simp add: is_linear_manifold.zero is_subspace.subspace)
  moreover have  \<open>({0}::('a::chilbert_space) set) \<supseteq>  (orthogonal_complement (top::('a::chilbert_space) set))\<close>
    by (metis is_subspace_0 is_subspace_UNIV is_subspace_orthog ortho_leq orthogonal_complement_twice top_greatest)
  ultimately show ?thesis by blast
qed

lemma ortho_bot[simp]:
  " (orthogonal_complement ({0}::('a::chilbert_space) set)) 
= (top::('a::chilbert_space) set)"
  using is_subspace_UNIV orthogonal_complement_twice by fastforce


subsection \<open>Closed sum\<close>

definition closed_sum:: \<open>('a::{complex_vector,topological_space}) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>closed_sum A B = closure (A +\<^sub>m B)\<close>

notation closed_sum (infixl "+\<^sub>M" 65)

lemma sum_existential:
  \<open>x \<in> (A +\<^sub>m B) \<Longrightarrow> \<exists> a\<in>A. \<exists> b\<in>B. x = a + b\<close>
proof -
  assume "x \<in> (A +\<^sub>m B)"
  then have "\<exists>a aa. x = a + aa \<and> a \<in> A \<and> aa \<in> B"
    using Minkoswki_sum_def by blast
  then show ?thesis
    by (metis (lifting))
qed

lemma is_closed_subspace_comm:                                                                 
  assumes \<open>is_subspace A\<close> and \<open>is_subspace B\<close>
  shows \<open>A +\<^sub>M B = B +\<^sub>M A\<close>
  by (smt Collect_cong add.commute closed_sum_def Minkoswki_sum_def)

lemma OrthoClosed:
  fixes A ::"('a::chilbert_space) set"
  shows \<open>closed (orthogonal_complement A)\<close>                                                
proof-
  have \<open>\<forall> n. x n \<in> (orthogonal_complement A) \<Longrightarrow> x \<longlonglongrightarrow> l \<Longrightarrow> l \<in> (orthogonal_complement A)\<close> for x l
  proof-
    assume \<open>\<forall> n. x n \<in> (orthogonal_complement A)\<close>
    hence \<open>\<forall> n. \<forall> y \<in> A. \<langle> y , x n \<rangle> = 0\<close>
      by (metis (no_types, lifting) cinner_commute complex_cnj_zero_iff is_orthogonal_def mem_Collect_eq orthogonal_complement_def)
    assume \<open>x \<longlonglongrightarrow> l\<close>
    moreover have \<open>isCont (\<lambda> t. \<langle> y , t \<rangle>) l\<close> for y
      by simp
    ultimately have \<open>(\<lambda> n. (\<langle> y , x n \<rangle>) ) \<longlonglongrightarrow> \<langle> y , l \<rangle>\<close> for y 
      by (simp add: isCont_tendsto_compose)
    hence \<open>\<forall> y \<in> A. (\<lambda> n. (\<langle> y , x n \<rangle>) ) \<longlonglongrightarrow> \<langle> y , l \<rangle>\<close>
      by simp
    hence \<open>\<forall> y \<in> A. (\<lambda> n. 0 ) \<longlonglongrightarrow> \<langle> y , l \<rangle>\<close>
      using  \<open>\<forall> n. \<forall> y \<in> A. \<langle> y , x n \<rangle> = 0\<close> by fastforce
    hence \<open>\<forall> y \<in> A. \<langle> y , l \<rangle> = 0\<close> 
      using limI by fastforce
    thus ?thesis 
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
  qed
  thus ?thesis 
    using closed_sequential_limits by blast
qed


lemma OrthoClosedEq:
  fixes A ::"('a::chilbert_space) set"
  shows \<open>(orthogonal_complement A) = (orthogonal_complement (closure A)) \<close>                                                
proof-
  have \<open>x \<in> (orthogonal_complement A) \<Longrightarrow> x \<in> (orthogonal_complement (closure A))\<close> for x
  proof-
    assume \<open>x \<in> (orthogonal_complement A)\<close>
    hence \<open>\<forall> y \<in> A. \<langle> y , x \<rangle> = 0\<close>
      by (metis (no_types, lifting) cinner_commute complex_cnj_zero_iff is_orthogonal_def mem_Collect_eq orthogonal_complement_def)
    hence \<open>y \<in> closure A \<Longrightarrow> \<langle> y , x \<rangle> = 0\<close> for y
    proof-
      assume \<open>y \<in> closure A\<close>  
      then obtain yy where \<open>\<forall> n. yy n \<in> A\<close> and \<open>yy \<longlonglongrightarrow> y\<close> 
        by (meson closure_sequential)
      have \<open>isCont (\<lambda> t. \<langle> t , x \<rangle>) y\<close>
        by simp
      hence \<open>(\<lambda> n. \<langle> yy n , x \<rangle>) \<longlonglongrightarrow>  \<langle> y , x \<rangle>\<close>
        using \<open>yy \<longlonglongrightarrow> y\<close> isCont_tendsto_compose
        by fastforce
      hence \<open>(\<lambda> n. 0) \<longlonglongrightarrow>  \<langle> y , x \<rangle>\<close>
        using \<open>\<forall> y \<in> A. \<langle> y , x \<rangle> = 0\<close>  \<open>\<forall> n. yy n \<in> A\<close> by simp
      thus ?thesis 
        using limI by force
    qed
    thus ?thesis 
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
  qed
  moreover have \<open>x \<in> (orthogonal_complement (closure A)) \<Longrightarrow> x \<in> (orthogonal_complement A)\<close> for x
    by (smt closure_subset mem_Collect_eq orthogonal_complement_def subset_eq)
  ultimately show ?thesis by blast
qed

lemma is_subspace_closed_plus:
  fixes A B::"('a::chilbert_space) set"
  assumes \<open>is_subspace A\<close> and \<open>is_subspace B\<close>
  shows \<open>is_subspace (A +\<^sub>M B)\<close>
  by (simp add: assms(1) assms(2) closed_sum_def is_subspace.intro is_subspace.subspace is_subspace_cl is_subspace_plus)


lemma DeMorganOrtho:        
  fixes A B::"('a::chilbert_space) set"
  assumes \<open>is_subspace A\<close> and \<open>is_subspace B\<close>
  shows \<open>orthogonal_complement (A +\<^sub>M B) = (orthogonal_complement A) \<inter> (orthogonal_complement B)\<close>
proof-
  have \<open>x \<in> (orthogonal_complement (A +\<^sub>M B)) \<Longrightarrow> x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)\<close> for x
  proof-
    assume \<open>x \<in> (orthogonal_complement (A +\<^sub>M B))\<close>
    moreover have \<open>orthogonal_complement (A +\<^sub>M B) = (orthogonal_complement (A +\<^sub>m B))\<close>
      unfolding closed_sum_def by (subst OrthoClosedEq[symmetric], simp)
    ultimately have \<open>x \<in> (orthogonal_complement (A +\<^sub>m B))\<close>
      by smt
    hence \<open>\<forall> z \<in> (A +\<^sub>m B). \<langle> z , x \<rangle> = 0\<close> 
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    hence \<open>\<forall> z \<in> A. \<langle> z , x \<rangle> = 0\<close> 
      using assms(2) Minkoswki_sum_def is_linear_manifold.zero is_subspace.subspace by force
    hence \<open>x \<in> (orthogonal_complement A)\<close>
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    from  \<open>\<forall> z \<in> (A +\<^sub>m B). \<langle> z , x \<rangle> = 0\<close> 
    have \<open>\<forall> z \<in> B. \<langle> z , x \<rangle> = 0\<close> 
      by (smt Groups.add_ac(2) add.right_neutral assms(1) Minkoswki_sum_def is_linear_manifold.zero is_subspace.subspace mem_Collect_eq)
    hence \<open>x \<in> (orthogonal_complement B)\<close>
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    show ?thesis 
      using \<open>x \<in> (orthogonal_complement A)\<close> \<open>x \<in> (orthogonal_complement B)\<close> by auto
  qed
  moreover have \<open>x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B) \<Longrightarrow> x \<in> (orthogonal_complement (A +\<^sub>M B))\<close> for x
  proof-
    assume \<open>x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)\<close>
    hence \<open>x \<in> (orthogonal_complement A)\<close> by blast
    hence \<open> \<forall> y\<in> A. \<langle> y , x \<rangle> = 0\<close>
      by (metis (no_types, lifting) cinner_commute complex_cnj_zero_iff is_orthogonal_def mem_Collect_eq orthogonal_complement_def)
    have \<open>x \<in> (orthogonal_complement B)\<close> using \<open>x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)\<close> by blast
    hence \<open>\<forall> y\<in> B. \<langle> y , x \<rangle> = 0\<close>
      by (metis (no_types, lifting) cinner_commute complex_cnj_zero_iff is_orthogonal_def mem_Collect_eq orthogonal_complement_def)
    have \<open>\<forall> a\<in>A. \<forall> b\<in>B. \<langle> a+b , x \<rangle> = 0\<close>
      by (simp add: \<open>\<forall>y\<in>A. \<langle>y , x\<rangle> = 0\<close> \<open>\<forall>y\<in>B. \<langle>y , x\<rangle> = 0\<close> cinner_left_distrib)
    hence \<open>\<forall> y \<in> (A +\<^sub>m B). \<langle> y , x \<rangle> = 0\<close>
      using sum_existential by blast
    hence \<open>x \<in> (orthogonal_complement (A +\<^sub>m B))\<close>
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    moreover have \<open>(orthogonal_complement (A +\<^sub>m B)) = (orthogonal_complement (A +\<^sub>M B))\<close>
      unfolding closed_sum_def by (subst OrthoClosedEq[symmetric], simp)
    ultimately have \<open>x \<in> (orthogonal_complement (A +\<^sub>M B))\<close>
      by blast
    thus ?thesis
      by blast
  qed
  ultimately show ?thesis by blast
qed


lemma DeMorganOrthoDual:
  fixes A B::"('a::chilbert_space) set"
  assumes \<open>is_subspace A\<close> and \<open>is_subspace B\<close>
  shows  \<open>orthogonal_complement (A \<inter> B) = ((orthogonal_complement A) +\<^sub>M (orthogonal_complement B))\<close>  
proof-
  have \<open>orthogonal_complement (A \<inter> B) = (orthogonal_complement ((orthogonal_complement (orthogonal_complement A)) \<inter> (orthogonal_complement (orthogonal_complement B) )))\<close>
    by (metis assms(1) assms(2) orthogonal_complement_twice)
  also have \<open>... = (orthogonal_complement ( orthogonal_complement ((orthogonal_complement A) +\<^sub>M (orthogonal_complement B)) ))\<close>
    using DeMorganOrtho assms(1) assms(2) is_subspace_orthog by force
  also have \<open>... = ((orthogonal_complement A) +\<^sub>M (orthogonal_complement B))\<close>
    by (simp add: assms(1) assms(2) is_subspace_closed_plus orthogonal_complement_twice)
  finally show ?thesis by blast
qed


lemma is_closed_subspace_asso:
  fixes A B C::"('a::chilbert_space) set"
  assumes \<open>is_subspace A\<close> and \<open>is_subspace B\<close> and \<open>is_subspace C\<close>
  shows \<open>A +\<^sub>M (B +\<^sub>M C) = (A +\<^sub>M B) +\<^sub>M C\<close>
proof-
  have \<open>is_linear_manifold (B +\<^sub>M C)\<close>
    by (simp add: assms(2) assms(3) is_subspace.subspace is_subspace_closed_plus)
  moreover have \<open>closed (B +\<^sub>M C)\<close>
    by (simp add: closed_sum_def)
  ultimately have \<open>is_subspace (B +\<^sub>M C)\<close>
    by (simp add: is_subspace_def)
  hence \<open>is_subspace (A +\<^sub>M (B +\<^sub>M C))\<close>
    by (metis DeMorganOrthoDual assms(1) is_subspace_inter is_subspace_orthog orthogonal_complement_twice)
  have \<open>(A +\<^sub>M (B +\<^sub>M C)) = (orthogonal_complement (orthogonal_complement (A +\<^sub>M (B +\<^sub>M C))))\<close>
    by (smt \<open>is_subspace (A +\<^sub>M (B +\<^sub>M C))\<close> orthogonal_complement_twice)
  also have  \<open>... = (orthogonal_complement (  (orthogonal_complement A) \<inter> (orthogonal_complement (B +\<^sub>M C))  ))\<close>
    by (simp add: DeMorganOrtho \<open>is_subspace (B +\<^sub>M C)\<close> assms(1))
  also have  \<open>... = (orthogonal_complement (  (orthogonal_complement A) \<inter> ((orthogonal_complement B) \<inter> (orthogonal_complement C))  ))\<close>
    by (simp add: DeMorganOrtho assms(2) assms(3))
  also have  \<open>... = (orthogonal_complement (  ((orthogonal_complement A) \<inter> (orthogonal_complement B)) \<inter> (orthogonal_complement C)  ))\<close>
    by (simp add: inf_assoc)
  also have  \<open>... = (orthogonal_complement (orthogonal_complement  ((orthogonal_complement((orthogonal_complement A) \<inter> (orthogonal_complement B))))  \<inter> (orthogonal_complement C)  ))\<close>
    by (metis assms(1) assms(2) is_subspace_inter is_subspace_orthog orthogonal_complement_twice)
  also have  \<open>... = (orthogonal_complement ( orthogonal_complement ( (A +\<^sub>M B) +\<^sub>M C )  ))\<close>
    by (simp add: DeMorganOrtho \<open>orthogonal_complement (orthogonal_complement A \<inter> orthogonal_complement B \<inter> orthogonal_complement C) = orthogonal_complement (orthogonal_complement (orthogonal_complement (orthogonal_complement A \<inter> orthogonal_complement B)) \<inter> orthogonal_complement C)\<close> assms(1) assms(2) assms(3) is_subspace_closed_plus)
  finally show ?thesis
    by (metis DeMorganOrthoDual assms(1) assms(2) assms(3) is_subspace_inter is_subspace_orthog orthogonal_complement_twice)
qed


lemma is_closed_subspace_zero:
  fixes A :: \<open>('a::chilbert_space) set\<close>
  assumes \<open>is_subspace A\<close>
  shows \<open>(({0}::('a::chilbert_space) set)+\<^sub>MA) = A\<close>
  by (smt Collect_cong DeMorganOrthoDual IntE IntI UNIV_I assms is_subspace_UNIV is_subspace_orthog ortho_top orthogonal_complement_twice orthogonal_complement_def)


lemma is_closed_subspace_ord:
  fixes A B C:: \<open>('a::chilbert_space) set\<close>
  assumes \<open>is_subspace A\<close> and \<open>is_subspace B\<close> and \<open>is_subspace C\<close>
    and \<open>A \<subseteq> B\<close>
  shows \<open>(C+\<^sub>MA) \<subseteq> (C+\<^sub>MB)\<close>
  by (smt DeMorganOrthoDual Int_Collect_mono assms(1) assms(2) assms(3) assms(4) is_closed_subspace_comm is_subspace_inter is_subspace_orthog ortho_leq orthogonal_complement_twice orthogonal_complement_def)


lemma is_closed_subspace_universal_inclusion_left:
  fixes A B:: \<open>('a::chilbert_space) set\<close>
  assumes \<open>is_subspace A\<close> and \<open>is_subspace B\<close>
  shows \<open>A \<subseteq> (A +\<^sub>M B)\<close>
  by (metis DeMorganOrtho Int_lower1 assms(1) assms(2) is_subspace_closed_plus ortho_leq)

lemma is_closed_subspace_universal_inclusion_right:
  fixes A B:: \<open>('a::chilbert_space) set\<close>
  assumes \<open>is_subspace A\<close> and \<open>is_subspace B\<close>
  shows \<open>B \<subseteq> (A +\<^sub>M B)\<close>
  by (metis assms(1) assms(2)  is_closed_subspace_comm is_closed_subspace_universal_inclusion_left)


lemma is_closed_subspace_universal_inclusion_inverse:
  fixes A B C:: \<open>('a::chilbert_space) set\<close>
  assumes \<open>is_subspace A\<close> and \<open>is_subspace B\<close> and \<open>is_subspace C\<close>
    and \<open>A \<subseteq> C\<close> and \<open>B \<subseteq> C\<close>
  shows \<open>(A +\<^sub>M B) \<subseteq> C\<close>
  by (metis DeMorganOrtho assms(1) assms(2) assms(3) assms(4) assms(5) inf_greatest is_subspace_closed_plus ortho_leq)

lemma ortho_inter_zero:
  assumes "0\<in>M"
  shows \<open>M \<inter> (orthogonal_complement M) = {0}\<close>
proof -
  have "x=0" if "x\<in>M" and "x\<in>orthogonal_complement M" for x
  proof -
    from that have "x \<bottom> x"
      unfolding orthogonal_complement_def by auto
    then have "\<langle>x, x\<rangle> = 0"
      using is_orthogonal_def by blast
    then show "x=0"
      by auto
  qed
  with assms show ?thesis
    unfolding orthogonal_complement_def is_orthogonal_def by auto
qed

theorem ortho_decomp:
  fixes x :: \<open>'a::chilbert_space\<close>
  assumes  \<open>is_subspace M\<close>
  shows \<open>x = (proj M) x + (proj (orthogonal_complement M)) x\<close>
  by (metis ProjOntoOrtho assms diff_add_cancel id_apply is_subspace_orthog minus_apply orthogonal_complement_twice)

lemma proj_ker_simp:
  fixes x :: \<open>'a::chilbert_space\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>f (proj (ker_op f) x) = 0\<close>
proof-
  from \<open>bounded_clinear f\<close>
  have \<open>is_subspace (ker_op f)\<close>
    by (simp add: ker_op_lin)
  hence \<open>proj (ker_op f) x \<in> ker_op f\<close>
    by (simp add: proj_intro2)
  thus ?thesis using ker_op_def
    by (simp add: ker_op_def)
qed

lemma inner_product_proj:
  fixes x t :: \<open>'a::chilbert_space\<close>
  assumes \<open>is_subspace M\<close> and \<open>t \<noteq> 0\<close> and \<open>t \<in> M\<close>
    and \<open>\<forall> m \<in> M. \<exists> k. m = k *\<^sub>C t\<close>
  shows \<open>proj M x = (\<langle>t , x\<rangle> / \<langle>t , t\<rangle>) *\<^sub>C t\<close>
proof-
  have \<open>(\<langle>t , t\<rangle>) \<noteq> 0\<close>
    using \<open>t \<noteq> 0\<close>
    by simp
  obtain k where \<open>(proj M) x = k *\<^sub>C t\<close>
    using assms(1) assms(4) proj_intro2 by blast    
  have \<open>((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t =
 ((\<langle>t , ((proj M) x + (proj (orthogonal_complement M)) x)\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
    using assms(1) ortho_decomp by fastforce
  also have \<open>... = ((\<langle>t , ((proj M) x)\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
  proof-
    have \<open> (proj (orthogonal_complement M)) x \<in> orthogonal_complement M\<close>
      by (simp add: assms(1) proj_intro2)
    hence \<open>\<langle>t , (proj (orthogonal_complement M)) x\<rangle> = 0\<close>
      using \<open>t \<in> M\<close>
      unfolding orthogonal_complement_def
      unfolding is_orthogonal_def
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm)
    thus ?thesis
      by (simp add: cinner_right_distrib) 
  qed
  also have \<open>... = ((\<langle>t , (k *\<^sub>C t)\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
    using \<open>(proj M) x = k *\<^sub>C t\<close> 
    by simp
  also have \<open>... = ((k*(\<langle>t , t\<rangle>))/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
    by simp   
  also have \<open>... = k *\<^sub>C t\<close>
    using  \<open>(\<langle>t , t\<rangle>) \<noteq> 0\<close> by simp
  finally show ?thesis using \<open>(proj M) x = k *\<^sub>C t\<close> 
    by auto
qed

section "Unsorted"

typedef (overloaded) ('a::"{complex_vector,topological_space}") 
linear_space = \<open>{S::'a set. is_subspace S}\<close>
  using is_subspace_UNIV by blast

setup_lifting type_definition_linear_space

definition is_onb :: "'a::chilbert_space set \<Rightarrow> bool" where "is_onb = undefined"

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>is_onb\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>

class basis_enum = chilbert_space +
  fixes canonical_basis :: "'a list"
  fixes canonical_basis_length :: "'a itself \<Rightarrow> nat"
  assumes "distinct canonical_basis"
  assumes "is_onb (set canonical_basis)"
  assumes "canonical_basis_length TYPE('a) = length canonical_basis"

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>is_onb\<close>, SOME \<^typ>\<open>'a::chilbert_space set \<Rightarrow> bool\<close>)\<close>


section \<open>Riesz Representation\<close>

definition proportion :: \<open>('a::complex_vector) set \<Rightarrow> bool\<close> where
  \<open>proportion S =  (
  \<forall> x y. x \<in> S \<and> x \<noteq> 0 \<and> y \<in> S \<and> y \<noteq> 0 \<longrightarrow> (\<exists> k. x = k *\<^sub>C y) 
)\<close>

lemma proportion_existence:
  \<open>proportion S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists> t \<in> S. (\<forall> x \<in> S. \<exists> k. x = k *\<^sub>C t)\<close>
  using complex_vector.scale_zero_left ex_in_conv proportion_def
  by metis

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

lemma ker_unidim:
  fixes f :: \<open>('a::chilbert_space) functional\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>proportion (orthogonal_complement (ker_op f))\<close>
proof-
  have \<open>x \<in> (orthogonal_complement (ker_op f)) \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<in> orthogonal_complement (ker_op f)
 \<Longrightarrow> y \<noteq> 0  \<Longrightarrow> \<exists> k. x = k *\<^sub>C y\<close>
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

lemma riesz_frechet_representation_existence:
  fixes f::\<open>'a::chilbert_space functional\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>\<exists>t. \<forall>x.  f x = \<langle>t, x\<rangle>\<close>
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

section \<open>Adjointness\<close>

definition \<open>Adj G = (SOME F. \<forall>x. \<forall>y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>)\<close>
  for G :: "'b::complex_inner \<Rightarrow> 'a::complex_inner"

lemma Adj_I:
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
    using  riesz_frechet_representation_existence by blast
  hence  \<open>\<exists> F. \<forall> x. ( \<forall> y :: 'b.  (g x) y = (\<langle>(F x) , y\<rangle>) )\<close>
    by metis
  then obtain F where \<open>\<forall> x. ( \<forall> y :: 'b.  (g x) y = (\<langle>(F x) , y\<rangle>) )\<close>
    by blast
  thus "\<exists>x. \<forall>xa y. \<langle>x xa, y\<rangle> = \<langle>xa, G y\<rangle>" using  g_def
    by auto
qed

notation Adj ("_\<^sup>\<dagger>" [99] 100)

lemma Adj_D:
  fixes G:: \<open>'b::chilbert_space \<Rightarrow> 'a::chilbert_space\<close>
    and F:: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close>
  assumes "bounded_clinear G" and
    F_is_adjoint: \<open>\<And>x y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
  shows \<open>F = G\<^sup>\<dagger>\<close>
proof-
  note F_is_adjoint
  moreover have \<open>\<forall> x::'a. \<forall> y::'b. \<langle>((G\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (G y)\<rangle>\<close>
    using  \<open>bounded_clinear G\<close> Adj_I by blast
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
    using Adj_I \<open>bounded_clinear A\<close>
    by auto
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
      by (simp add: complex_inner_class.norm_cauchy_schwarz2)
    ultimately have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2  \<le> \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close>
      for x
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close> complex_inner_class.norm_cauchy_schwarz power2_norm_eq_cinner)
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

instantiation complex :: "chilbert_space" begin
instance ..
end

proposition dagger_dagger_id:
  \<open>bounded_clinear U \<Longrightarrow> U\<^sup>\<dagger>\<^sup>\<dagger> = U\<close>
  for U :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close>
  proof
  show "(U\<^sup>\<dagger>\<^sup>\<dagger>) x = U x"
    if "bounded_clinear U"
    for x :: 'a
    using that 
  proof-
    have \<open>\<langle> (U\<^sup>\<dagger>) r, s \<rangle> = \<langle> r, U s \<rangle>\<close>
      for r s
      using that
      by (simp add: Adj_I)
    have \<open>\<langle> U s, r \<rangle> = \<langle> s, (U\<^sup>\<dagger>) r \<rangle>\<close>
      for r s
    proof-
      have \<open>\<langle> (U\<^sup>\<dagger>) r, s \<rangle> = cnj \<langle> s, (U\<^sup>\<dagger>) r \<rangle>\<close>
        by simp
      moreover have \<open>\<langle> r, U s \<rangle> = cnj \<langle>  U s, r\<rangle>\<close>
        by simp
      ultimately have \<open>cnj \<langle> s, (U\<^sup>\<dagger>) r \<rangle> = cnj \<langle> U s, r \<rangle>\<close>
        using \<open>\<langle> (U\<^sup>\<dagger>) r, s \<rangle> = \<langle> r, U s \<rangle>\<close> by smt
      hence \<open>cnj (cnj \<langle> s, (U\<^sup>\<dagger>) r \<rangle>) = cnj (cnj \<langle> U s, r \<rangle>)\<close>
        by simp
      hence \<open>\<langle> s, (U\<^sup>\<dagger>) r \<rangle> = \<langle> U s, r \<rangle>\<close>
        by simp
      thus ?thesis by simp
    qed
    moreover have \<open>bounded_clinear (U\<^sup>\<dagger>)\<close>
      by (simp add: Adj_bounded_clinear that)
    ultimately show ?thesis
      using Adj_D by fastforce 
  qed
qed

lemma id_bounded_clinear: \<open>bounded_clinear id\<close>
  proof
  show "id ((x::'a) + y) = id x + id y"
    for x :: 'a
      and y :: 'a
    unfolding id_def by blast
  show "id (r *\<^sub>C (x::'a)) = r *\<^sub>C id x"
    for r :: complex
      and x :: 'a
    unfolding id_def by blast
  show "\<exists>K. \<forall>x. norm (id (x::'a)) \<le> norm x * K"
     unfolding id_def
     using less_eq_real_def by auto 
qed

lemma id_dagger: \<open>(id::'a::chilbert_space\<Rightarrow>'a)\<^sup>\<dagger> = id\<close>
proof-
  have \<open>bounded_clinear id\<close>
    by (simp add: id_bounded_clinear)
  moreover have \<open>\<langle> id x, y \<rangle> = \<langle> x, id y \<rangle>\<close>
    for x y::'a
    unfolding id_def by blast
  ultimately show ?thesis
    by (smt Adj_D)  
qed

lemma scalar_times_adjc_flatten:
fixes A::\<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close>
assumes \<open>bounded_linear A\<close> and \<open>\<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x\<close> 
shows \<open>(\<lambda> t. a *\<^sub>C (A t))\<^sup>\<dagger> = (\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s))\<close>
proof-
  from \<open>bounded_linear A\<close>
  have \<open>bounded_linear (\<lambda> t. a *\<^sub>C (A t))\<close>
    by (simp add: bounded_clinear.bounded_linear bounded_clinear_scaleC_right bounded_linear_compose)
  moreover have \<open>bounded_clinear (\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s))\<close>
  proof-
    from \<open>bounded_linear A\<close>
    have \<open>bounded_linear (A\<^sup>\<dagger>)\<close>
      using Adj_bounded_clinear assms(2) bounded_clinear.bounded_linear bounded_linear_bounded_clinear by blast
    thus ?thesis
      by (simp add: Adj_bounded_clinear assms(1) assms(2) bounded_clinear_const_scaleC bounded_linear_bounded_clinear) 
  qed
  moreover have \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = \<langle>x, (\<lambda> t. a *\<^sub>C (A t)) y \<rangle>\<close>
    for x y
  proof-
    have \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = \<langle>(cnj a) *\<^sub>C ((A\<^sup>\<dagger>) x), y \<rangle>\<close>
      by blast
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a *  \<langle>(A\<^sup>\<dagger>) x, y \<rangle>\<close>
      by simp
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a * cnj \<langle>y, (A\<^sup>\<dagger>) x\<rangle>\<close>
      by simp
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a * cnj \<langle>((A\<^sup>\<dagger>)\<^sup>\<dagger>) y, x\<rangle>\<close>
      by (simp add: Adj_I Adj_bounded_clinear assms(1) assms(2) bounded_linear_bounded_clinear)
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a * cnj (cnj \<langle>x, ((A\<^sup>\<dagger>)\<^sup>\<dagger>) y\<rangle>)\<close>
      by simp
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a * \<langle>x, ((A\<^sup>\<dagger>)\<^sup>\<dagger>) y\<rangle>\<close>
      by simp
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a * \<langle>x, A y\<rangle>\<close>
      using Adj_I  assms(1) assms(2) bounded_linear_bounded_clinear by fastforce
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = \<langle>x, a *\<^sub>C A y\<rangle>\<close>
      by simp
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = \<langle>x, (\<lambda> t. a *\<^sub>C (A t)) y \<rangle>\<close>
      by simp
    thus ?thesis by blast
  qed
  ultimately show ?thesis
  proof - (* automatic proof *)
    assume a1: "\<And>x y. \<langle>cnj a *\<^sub>C (A\<^sup>\<dagger>) x, y\<rangle> = \<langle>x, a *\<^sub>C A y\<rangle>"
    { fix bb :: 'b
      have "\<And>b aa. \<langle>cnj a *\<^sub>C (A\<^sup>\<dagger>) b, aa\<rangle> = \<langle>b, A (a *\<^sub>C aa)\<rangle>"
        using a1 by (metis (lifting) assms(2))
      then have "\<And>aa b. \<langle>aa, cnj a *\<^sub>C (A\<^sup>\<dagger>) b\<rangle> = cnj \<langle>b, A (a *\<^sub>C aa)\<rangle>"
        by (metis (lifting) cinner_commute')
      then have "\<And>b aa. a *\<^sub>C \<langle>(A\<^sup>\<dagger>) b, aa\<rangle> = \<langle>b, A (a *\<^sub>C aa)\<rangle>"
        by (metis (no_types) cinner_commute' cinner_scaleC_left cinner_scaleC_right complex_scaleC_def)
      then have "(\<lambda>b. cnj a *\<^sub>C (A\<^sup>\<dagger>) b) = (\<lambda>aa. a *\<^sub>C A aa)\<^sup>\<dagger>"
        by (simp add: Adj_D \<open>bounded_linear (\<lambda>t. a *\<^sub>C A t)\<close> assms(2) bounded_linear_bounded_clinear)
      then have "cnj a *\<^sub>C (A\<^sup>\<dagger>) bb = ((\<lambda>aa. a *\<^sub>C A aa)\<^sup>\<dagger>) bb"
        by metis }
    then show ?thesis
      by presburger
  qed  
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

lemma clinear_is_linear_manifoldis_subspace_closure:
  fixes f::\<open>('a::chilbert_space) \<Rightarrow> ('b::chilbert_space)\<close>
    and S::\<open>'a set\<close>
  assumes "clinear f" and "is_linear_manifold S"
  shows  \<open>is_subspace (closure {f x |x. x \<in> S})\<close>
proof -
  have "is_linear_manifold {f x |x. x \<in> S}"
    using assms is_linear_manifold_image
    by (simp add: is_linear_manifold_image Setcompr_eq_image)
  then show \<open>is_subspace (closure {f x |x. x \<in> S})\<close>
    apply (rule_tac is_subspace.intro)
    using is_subspace_cl apply blast
    by blast
qed



end

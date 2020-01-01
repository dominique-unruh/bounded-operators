(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Main results
- complex_inner: Class of complex vector spaces with inner product.
- cgderiv: Gradient derivative.
- complex_inner: Class of complex Hilbert spaces
- existence_uniqueness_min_dist: Existence and uniqueness of a point in a convex body whose
distance to a given point reach its minimum in the convex body.
- dist_min_ortho: Equivalence between point at minimum distance and orthogonal projectionection.
- projection: Definition of orthogonal projectionection.
- projectionPropertiesA: The orthogonal projectionection is a bounded operator.
- orthogonal_complement_twice: The orthogonal complement is an involution.
- ortho_decomp: Decomposition of a Hilbert space into a sum of a complex_vector.subspace and its orthogonal 
complement.
- riesz_frechet_representation_existence: Riesz-Frechet representation theorem
- Adj: Definition of adjoint.
- dagger_dagger_id: The adjoint is an involution.
*)

subsection \<open>\<open>Complex_Inner_Product\<close> -- Inner Product Spaces and the Gradient Derivative\<close>

theory Complex_Inner_Product
  imports "HOL-Analysis.Infinite_Set_Sum" Complex_Main Complex_Vector_Spaces
    "HOL-Analysis.Inner_Product"  Lattice_Missing Operator_Norm_Missing
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

text \<open>Near-Hilbert space according to Definition 3, page 67, @{cite Helemskii}\<close>
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

lemma cinner_scaleC_right [simp]: "\<langle>x , r *\<^sub>C y\<rangle> = r * \<langle>x , y\<rangle>"
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
  "\<langle>x , y\<rangle> * (cnj \<langle>x , y\<rangle> ) \<le> \<langle>x , x\<rangle> * \<langle>y , y\<rangle>"
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
  shows "norm \<langle>x , y\<rangle> \<le> \<parallel>x\<parallel> * \<parallel>y\<parallel>"
proof (rule power2_le_imp_le)
  have ineq: "cinner x y * cnj (cinner x y) \<le> cinner x x * cinner y y"
    using Cauchy_Schwarz_ineq .
  have "(norm (cinner x y))^2 = Re (cinner x y * cnj (cinner x y))"
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

subsection \<open>Recovered theorems\<close>

(* Recovered theorem *)
lemma Cauchy_Schwarz_ineq2:
  "norm (cinner x y) \<le> norm x * norm y"
  by (simp add: local.norm_cauchy_schwarz)

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

(* FIXME
lemmas tendsto_cinner [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]
*)

lemma tendsto_cinner0: "lim (\<lambda>n. \<langle>x n::'a, x n\<rangle>) = 0"
  if "Cauchy (x::nat \<Rightarrow> 'a)"
    and "Cauchy (\<lambda>n. 0::'a)"
    and "x \<longlonglongrightarrow> (0::'a)"
  for x :: "nat \<Rightarrow> 'a::complex_inner"
proof-
  have \<open>(\<lambda> n. norm (x n) ) \<longlonglongrightarrow> 0\<close>
    by (simp add: tendsto_norm_zero that(3))        
  hence \<open>(\<lambda> n. (norm (x n))^2 ) \<longlonglongrightarrow> 0\<close>
    by (metis power_zero_numeral tendsto_power)        
  moreover have \<open>(norm (x n))^2 = norm \<langle>x n, x n\<rangle>\<close>
    for n
    by (simp add: power2_norm_eq_cinner)        
  ultimately have \<open>(\<lambda> n. norm \<langle>x n, x n\<rangle>) \<longlonglongrightarrow> 0\<close>
    by auto
  hence \<open>(\<lambda> n. \<langle>x n, x n\<rangle>) \<longlonglongrightarrow> 0\<close>
    using tendsto_norm_zero_iff by auto
  thus ?thesis
    by (simp add: limI) 
qed


(* FIXME
lemmas isCont_cinner [simp] =
  bounded_bilinear.isCont [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]
*)

(* FIXME
lemmas has_derivative_cinner [derivative_intros] =
  bounded_bilinear.FDERIV [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]
*)

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

(* FIXME 
lemmas has_derivative_cinner_left [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_csemilinear_cinner_left[THEN bounded_csemilinear.bounded_linear]]
*)

(*
lemma differentiable_cinner [simp]:
  "f differentiable (at x within s) \<Longrightarrow> g differentiable at x within s \<Longrightarrow> 
      (\<lambda>x. cinner (f x) (g x)) differentiable at x within s"
  unfolding differentiable_def by (blast intro: has_derivative_cinner)
*)

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
  thus "summable (\<lambda>x. of_complex (f x) :: 'a)"
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


definition "orthogonal_complement S = {x | x. \<forall>y\<in>S. \<langle> x, y \<rangle> = 0}" 

lemma orthogonal_complement_D1:
  \<open>x \<in> orthogonal_complement M \<Longrightarrow> y \<in> M \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
  unfolding orthogonal_complement_def by auto

lemma orthogonal_complement_D2:
  \<open>x \<in> M \<Longrightarrow> y \<in> orthogonal_complement M \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
proof-
  assume \<open>x \<in> M\<close> and \<open>y \<in> orthogonal_complement M\<close>
  hence \<open>\<langle> y, x \<rangle> = 0\<close>
    using orthogonal_complement_D1
    by blast
  moreover have \<open>\<langle> x, y \<rangle> = cnj \<langle> y, x \<rangle>\<close>
    by simp    
  moreover have \<open>0 = cnj (0::complex)\<close>
    by simp
  ultimately show ?thesis by simp
qed

lemma orthogonal_complement_I2:
  \<open>(\<And>x. x \<in> M \<Longrightarrow> \<langle> y, x \<rangle> = 0) \<Longrightarrow> y \<in> orthogonal_complement M\<close>
  unfolding orthogonal_complement_def
  by simp

lemma orthogonal_complement_I1:
  \<open>(\<And>x. x \<in> M \<Longrightarrow> \<langle> x, y \<rangle> = 0) \<Longrightarrow> y \<in> orthogonal_complement M\<close>
proof-
  assume \<open>\<And>x. x \<in> M \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
  have  \<open>x \<in> M \<Longrightarrow> \<langle> y, x \<rangle> = 0\<close>
    for x
  proof-
    assume \<open>x \<in> M\<close>
    hence \<open>\<langle> x, y \<rangle> = 0\<close>
      by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> \<langle>x, y\<rangle> = 0\<close>)
    moreover have \<open>\<langle> y, x \<rangle> = cnj \<langle> x, y \<rangle>\<close>
      by auto
    moreover have \<open>0 = cnj 0\<close>
      by simp
    ultimately show ?thesis by simp 
  qed
  thus \<open>y \<in> orthogonal_complement M\<close> 
    unfolding orthogonal_complement_def 
    by auto
qed

definition is_orthogonal::\<open>'a::complex_inner \<Rightarrow> 'a \<Rightarrow> bool\<close>  where
  \<open>is_orthogonal x y \<equiv> ( \<langle> x, y \<rangle> = 0 )\<close>

bundle orthogonal_notation begin
notation is_orthogonal (infixl "\<bottom>" 69)
end

bundle no_orthogonal_notation begin
no_notation is_orthogonal (infixl "\<bottom>" 69)
end


lemma orthogonal_comm: "(is_orthogonal \<psi>  \<phi>) = (is_orthogonal \<phi> \<psi>)"
  unfolding is_orthogonal_def apply (subst cinner_commute) by blast


lemma subspace_orthog[simp]: "closed_subspace A \<Longrightarrow> closed_subspace (orthogonal_complement A)"
  for A :: \<open>('a::complex_inner) set\<close>
proof-
  assume \<open>closed_subspace A\<close>
  have  "x\<in>(orthogonal_complement A) \<Longrightarrow> y\<in>(orthogonal_complement A) \<Longrightarrow> x+y\<in>(orthogonal_complement A)" for x y
  proof-
    assume \<open>x\<in>(orthogonal_complement A)\<close>
    assume \<open>y\<in>(orthogonal_complement A)\<close>
    hence  \<open>\<forall> z \<in> A. \<langle>z, y\<rangle> = 0\<close> 
      by (simp add: orthogonal_complement_D2) 
    moreover have   \<open>\<forall> z \<in> A. \<langle>z, x\<rangle> = 0\<close>
      using  \<open>x\<in>(orthogonal_complement A)\<close>
      by (simp add: orthogonal_complement_D2)     
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
      by (simp add: orthogonal_complement_D2)
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
        by (simp add: orthogonal_complement_D2)
      assume \<open>x \<longlonglongrightarrow> l\<close>
      moreover have \<open>isCont (\<lambda> x. \<langle> y , x \<rangle>) l\<close> for y
      proof-
        have \<open>bounded_clinear (\<lambda> x. \<langle> y , x \<rangle>)\<close> 
          by (simp add: bounded_clinear_cinner_right)
        thus ?thesis
          by (simp add: bounded_linear_continuous)          
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
    using closed_subspace_def
    by (simp add: closed_subspace_def complex_vector.subspaceI)
qed

lemma ortho_inter_zero:
  assumes "0\<in>M"
  shows \<open>M \<inter> (orthogonal_complement M) = {0}\<close>
proof -
  have "x=0" if "x\<in>M" and "x\<in>orthogonal_complement M" for x
  proof -
    from that have "\<langle> x, x \<rangle> = 0"
      unfolding orthogonal_complement_def by auto
    thus "x=0"
      by auto
  qed
  with assms show ?thesis
    unfolding orthogonal_complement_def is_orthogonal_def 
    by auto
qed


subsection \<open>Minimum distance\<close>

lemma ExistenceUniquenessMinNorm:
  includes notation_norm
  fixes M :: \<open>('a::chilbert_space) set\<close>  
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>! k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) k\<close>
proof-
  have \<open>\<exists> k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) k\<close>
  proof-
    have \<open>\<exists> k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>^2) (\<lambda> t. t \<in> M) k\<close>
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
        hence "Re (\<langle>x , x\<rangle> ) \<in> {\<parallel>v\<parallel>\<^sup>2 |v. v \<in> M}"
          using a1 by blast
        thus ?thesis
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
      then obtain r::\<open>nat \<Rightarrow> 'a\<close> where \<open>\<forall> n. r n \<in> M \<and>  \<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
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
          by (simp add: real_vector.scale_right_diff_distrib)          
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
          using \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close> \<open>\<forall>n. r n \<in> M \<and> \<parallel>r n\<parallel>\<^sup>2 < d + 1 / (real n + 1)\<close> of_nat_1 of_nat_add
          by smt
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
          is_arg_min_def \<open>d = \<parallel>k\<parallel>\<^sup>2\<close>
        by smt
    qed
    thus ?thesis 
      by (smt is_arg_min_def norm_ge_zero power2_eq_square power2_le_imp_le)
  qed
  moreover have \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r \<Longrightarrow> is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s \<Longrightarrow> r = s\<close> for r s
  proof-
    assume \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r\<close>
    assume \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s\<close>
    have \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2
      = (1/2)*( \<parallel>r\<parallel>^2 + \<parallel>s\<parallel>^2 ) - \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>^2\<close> 
      using  ParallelogramLawVersion1 
      by (simp add: ParallelogramLawVersion1 scaleR_scaleC)
    moreover have \<open>\<parallel>r\<parallel>^2 \<le> \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>^2\<close>
    proof-
      have \<open>r \<in> M\<close> 
        using \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r\<close>
        by (simp add: is_arg_min_def)
      moreover have \<open>s \<in> M\<close> 
        using \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s\<close>
        by (simp add: is_arg_min_def)
      ultimately have \<open>((1/2) *\<^sub>R r + (1/2) *\<^sub>R s) \<in> M\<close> using \<open>convex M\<close>
        by (simp add: convexD)
      hence \<open> \<parallel>r\<parallel> \<le> \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>\<close>
        using  \<open>is_arg_min norm (\<lambda> t. t \<in> M) r\<close>
        by (smt is_arg_min_def)
      thus ?thesis
        using norm_ge_zero power_mono by blast
    qed
    moreover have \<open>\<parallel>r\<parallel> = \<parallel>s\<parallel>\<close>
    proof-
      have \<open>\<parallel>r\<parallel> \<le> \<parallel>s\<parallel>\<close> 
        using  \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r\<close> \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s\<close>  is_arg_min_def 
        by smt
      moreover have \<open>\<parallel>s\<parallel> \<le> \<parallel>r\<parallel>\<close>
        using  \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r\<close> \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s\<close>  is_arg_min_def 
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
  shows  \<open>\<exists>! k. is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k\<close>
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
  ultimately have \<open>\<exists>! k. is_arg_min norm (\<lambda> x. x \<in> {m - h| m. m \<in> M}) k\<close>
    using ExistenceUniquenessMinNorm \<open>closed {m - h |m. m \<in> M}\<close> \<open>convex {m - h |m. m \<in> M}\<close> \<open>{m - h |m. m \<in> M} \<noteq> {}\<close> 
    by blast
  have \<open>\<exists>! k. is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k\<close>
  proof-
    have \<open>\<exists> k. is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k\<close>
    proof-
      obtain k where \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h| m. m \<in> M}) k\<close>
        using  \<open>\<exists>! k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x  \<in> {m - h| m. m \<in> M}) k\<close> by blast
      have \<open>(\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k\<parallel> \<le> \<parallel>t\<parallel>) \<and> k \<in> {m - h |m. m \<in> M}\<close>
        using is_arg_min_def  \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h| m. m \<in> M}) k\<close>
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
      have \<open>is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> {m| m. m \<in> M}) (k + h)\<close>
      proof-
        have \<open>\<nexists>y. y \<in> {m |m. m \<in> M} \<and> \<parallel>y - h\<parallel> < \<parallel>(k + h) - h\<parallel>\<close>
          using \<open>\<forall>t. t \<in> M \<longrightarrow> \<parallel>(k+h)-h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>  
          by auto
        thus ?thesis
          using \<open>k + h \<in> M\<close>
          by (simp add: is_arg_min_def)
      qed
      thus ?thesis 
        by auto
    qed 
    moreover have \<open>is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k \<Longrightarrow> is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) t
                    \<Longrightarrow> k = t\<close> for k t
    proof-
      have \<open>is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k \<Longrightarrow> is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)\<close> for k
      proof-
        assume \<open>is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k\<close>
        hence \<open>\<forall>t. t \<in> M \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>
          by (meson is_arg_min_linorder)
        hence \<open>\<forall>t. t - h \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>
          by auto
        hence \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t\<parallel>\<close>
          by blast
        have \<open>k \<in> M\<close>
          using  \<open>is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k \<close>
          using is_arg_min_def
          by (simp add: is_arg_min_linorder)
        hence \<open>k - h \<in> {m - h |m. m \<in> M}\<close>
          by auto
        have  \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)\<close>
          using  \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t\<parallel>\<close>
            \<open>k - h \<in> {m - h |m. m \<in> M}\<close>
            is_arg_min_def
          by smt
        thus ?thesis by blast
      qed
      assume \<open>is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k\<close>
      hence  \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)\<close>
        using  \<open>\<And>k. is_arg_min (\<lambda>x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k \<Longrightarrow> is_arg_min norm (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)\<close>
        by blast
      assume  \<open>is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) t\<close> 
      hence  \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (t - h)\<close>
        using \<open>\<And>k. is_arg_min (\<lambda>x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k \<Longrightarrow> is_arg_min norm (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)\<close> by auto
      show ?thesis 
        using \<open>\<exists>!k. is_arg_min norm (\<lambda> x. x \<in> {m - h |m. m \<in> M}) k\<close> \<open>is_arg_min norm (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)\<close> \<open>is_arg_min norm (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (t - h)\<close> diff_add_cancel
        by (metis (no_types, lifting))
    qed
    ultimately show ?thesis by blast
  qed
  moreover have \<open>(\<lambda> x. dist x h) = (\<lambda> x. \<parallel>x - h\<parallel>)\<close>
    by (simp add: dist_norm)
  ultimately show ?thesis by auto
qed


\<comment> \<open>Theorem 2.6 in @{cite conway2013course}\<close> 
theorem dist_min_ortho:
  fixes M::\<open>('a::complex_inner) set\<close> and h k::'a 
  assumes \<open>closed_subspace M\<close>
  shows  \<open>(is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k) \<longleftrightarrow> h - k \<in> (orthogonal_complement M) \<and> k \<in> M\<close>
proof-
  include notation_norm
  have  \<open>complex_vector.subspace M\<close>
    using \<open>closed_subspace M\<close> unfolding closed_subspace_def by blast
  have \<open>is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k
     \<Longrightarrow>  h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
  proof-
    assume \<open>is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k\<close>
    hence  \<open>k \<in> M\<close>
      by (simp add: is_arg_min_def)
    moreover have \<open>h - k \<in> orthogonal_complement M\<close>
    proof-
      have \<open>f \<in> M \<Longrightarrow> \<langle> h - k , f \<rangle> = 0\<close> for f
      proof-
        assume \<open>f \<in> M\<close>
        hence  \<open>\<forall> c. c *\<^sub>R f \<in> M\<close>
          using assms scaleR_scaleC  \<open>complex_vector.subspace M\<close> complex_vector.subspace_def
          by (simp add: complex_vector.subspace_def scaleR_scaleC)
        have \<open>f \<in> M \<Longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> \<parallel> f \<parallel>^2\<close> for f
        proof-
          assume \<open>f \<in>  M\<close>             
          hence \<open>k + f \<in>  M\<close> 
            using  calculation \<open>complex_vector.subspace M\<close>
            by (simp add: complex_vector.subspace_def)
          hence \<open>dist h k \<le> dist  h (k + f)\<close>
          proof -
            have "\<forall>f A a aa. \<not> is_arg_min f (\<lambda> x. x \<in> A) (a::'a) \<or> (f a::real) \<le> f aa \<or> aa \<notin> A"
              by (metis (no_types) is_arg_min_linorder)
            hence "dist k h \<le> dist (f + k) h"
              by (metis \<open>is_arg_min (\<lambda>x. dist x h) (\<lambda> x. x \<in> M) k\<close> \<open>k + f \<in> M\<close> add.commute)
            thus ?thesis
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
            using \<open>\<And>f. f \<in> M \<Longrightarrow> 2 * Re (\<langle>(h - k) , f\<rangle>) \<le> \<parallel>f\<parallel>\<^sup>2\<close> assms scaleR_scaleC
              complex_vector.subspace_def
            by (metis \<open>complex_vector.subspace M\<close>)
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
              thus ?thesis 
                using True by auto
            next
              case False
              hence \<open>\<parallel> f \<parallel>^2 = 0\<close> 
                by simp
              thus ?thesis 
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
            using assms scaleR_scaleC complex_vector.subspace_def
            by (metis \<open>complex_vector.subspace M\<close>)
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
            using assms calculation complex_vector.subspace_def
            by (metis \<open>complex_vector.subspace M\<close>) 
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
     \<Longrightarrow> ( is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k )\<close>
  proof-
    assume \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
    hence \<open>h - k \<in> orthogonal_complement M\<close>
      by blast
    have \<open>k \<in> M\<close> using \<open>h - k \<in> orthogonal_complement M \<and> k \<in>  M\<close>
      by blast
    have \<open>f \<in> M \<Longrightarrow> dist h k \<le> dist h f \<close> for f
    proof-
      assume \<open>f \<in>  M\<close>
      hence \<open>\<langle> h - k,  k - f \<rangle> = 0\<close>
        by (metis (no_types, lifting) \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close> cinner_diff_right diff_0_right orthogonal_complement_D1)
      have \<open>\<parallel> h - f \<parallel>^2 = \<parallel> (h - k) + (k - f) \<parallel>^2\<close>
        by simp
      also have \<open>... = \<parallel> h - k \<parallel>^2 + \<parallel> k - f \<parallel>^2\<close>
        using  \<open>\<langle> h - k, k - f \<rangle> = 0\<close> PythagoreanId 
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
      by (simp add: \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close> dist_commute is_arg_min_linorder)
  qed
  ultimately show ?thesis by blast
qed

lemma linear_manifold_Convex:
  \<open>complex_vector.subspace M \<Longrightarrow> convex M\<close> 
proof-
  assume \<open>complex_vector.subspace M\<close>
  hence \<open>\<forall>x\<in>M. \<forall>y\<in> M. \<forall>u. \<forall>v. u *\<^sub>C x + v *\<^sub>C y \<in>  M\<close>
    using complex_vector.subspace_def
    by (simp add: complex_vector.subspace_def)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u::real. \<forall>v::real. u *\<^sub>R x + v *\<^sub>R y \<in> M\<close>
    by (simp add: scaleR_scaleC)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in>M\<close>
    by blast
  thus ?thesis using convex_def by blast
qed

lemma SubspaceConvex:
  \<open>closed_subspace M \<Longrightarrow> convex M\<close> 
  unfolding closed_subspace_def
  using linear_manifold_Convex
  by blast

corollary ExistenceUniquenessProj:
  fixes M :: \<open>('a::chilbert_space) set\<close> 
  assumes \<open>closed_subspace M\<close>
  shows  \<open>\<forall> h. \<exists>! k. (h - k) \<in> orthogonal_complement M \<and> k \<in> M\<close>
proof-  
  have \<open>complex_vector.subspace M\<close>
    using  \<open>closed_subspace M\<close>
    unfolding closed_subspace_def
    by blast
  hence \<open>0 \<in> M\<close> 
    using complex_vector.subspace_def
    by auto    
  hence \<open>M \<noteq> {}\<close> by blast
  have \<open>closed  M\<close>
    using  \<open>closed_subspace M\<close>
    by (simp add: closed_subspace.closed)
  have \<open>convex  M\<close>
    using  \<open>closed_subspace M\<close>
    by (simp add: SubspaceConvex)
  have \<open>\<forall> h. \<exists>! k.  is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k\<close>
    by (simp add: existence_uniqueness_min_dist \<open>closed M\<close> \<open>convex M\<close> \<open>M \<noteq> {}\<close>)
  thus ?thesis
  proof - (* sledgehammer *)
    { fix aa :: 'a and aaa :: "'a \<Rightarrow> 'a"
      obtain aab :: "'a \<Rightarrow> 'a" where
        ff1: "\<And>a aa. is_arg_min (\<lambda>aa. dist aa a) (\<lambda>a. a \<in> M) (aab a) \<and> (\<not> is_arg_min (\<lambda>aa. dist aa a) (\<lambda>a. a \<in> M) aa \<or> aa = aab a)"
        using \<open>\<forall>h. \<exists>!k. is_arg_min (\<lambda>x. dist x h) (\<lambda>x. x \<in> M) k\<close> by moura
      hence ff2: "\<And>a aa. a \<notin> M \<or> aa - a \<notin> {a. \<forall>aa. aa \<in> M \<longrightarrow> \<langle>a, aa\<rangle> = 0} \<or> a = aab aa"
        by (metis (no_types) assms dist_min_ortho orthogonal_complement_def)
      { assume "aab aa \<in> M \<and> aaa (aab aa) \<in> M \<and> aaa (aab aa) \<noteq> aab aa"
        hence "\<exists>a. a \<in> M \<and> aa - a \<in> {a. \<forall>aa. aa \<in> M \<longrightarrow> \<langle>a, aa\<rangle> = 0} \<and> aa - aaa a \<notin> {a. \<forall>aa. aa \<in> M \<longrightarrow> \<langle>a, aa\<rangle> = 0}"
          using ff2 ff1 by (metis (no_types) assms dist_min_ortho orthogonal_complement_def)
        hence "\<exists>a. aa - a \<in> orthogonal_complement M \<and> a \<in> M \<and> aaa a \<notin> M \<or> aaa a = a \<and> aa - a \<in> orthogonal_complement M \<and> a \<in> M \<or> aa - a \<in> orthogonal_complement M \<and> a \<in> M \<and> aa - aaa a \<notin> orthogonal_complement M"
          using orthogonal_complement_def by auto }
      hence "\<exists>a. aa - a \<in> orthogonal_complement M \<and> a \<in> M \<and> aaa a \<notin> M \<or> aaa a = a \<and> aa - a \<in> orthogonal_complement M \<and> a \<in> M \<or> aa - a \<in> orthogonal_complement M \<and> a \<in> M \<and> aa - aaa a \<notin> orthogonal_complement M"
        using ff1 assms dist_min_ortho by blast }
    thus ?thesis
      by (metis (no_types))
  qed
qed


definition is_projection_on::\<open>('a \<Rightarrow> 'a) \<Rightarrow> ('a::complex_inner) set \<Rightarrow> bool\<close> where
  \<open>is_projection_on \<pi> M \<longleftrightarrow> (\<forall>h. ((h - \<pi> h) \<in> (orthogonal_complement M) \<and> \<pi> h \<in> M))\<close>


lemma is_projection_on_existence:
  \<open>closed_subspace (M::('a::chilbert_space) set) \<Longrightarrow> \<exists> \<pi>. is_projection_on \<pi> M\<close>
  unfolding is_projection_on_def
  using ExistenceUniquenessProj
  by metis

definition projection :: \<open>('a::complex_inner) set \<Rightarrow> ('a::complex_inner \<Rightarrow> 'a)\<close> where
  \<open>projection M \<equiv> (SOME \<pi>. is_projection_on \<pi> M)\<close>

lemma projection_intro1':
  \<open>is_projection_on \<pi> M  \<Longrightarrow> h - (\<pi> h) \<in> orthogonal_complement M\<close>
  for M :: \<open>('a::complex_inner) set\<close>
  by (metis is_projection_on_def)

lemma projection_intro1:
  \<open>closed_subspace M  \<Longrightarrow> h - (projection M) h \<in> orthogonal_complement M\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
  using is_projection_on_existence  projection_intro1'
  by (metis projection_def someI_ex) 

lemma projection_intro2':
  \<open>is_projection_on \<pi> M \<Longrightarrow> \<pi> h \<in> M\<close>
  by (simp add: is_projection_on_def)

lemma projection_intro2:
  \<open>closed_subspace M  \<Longrightarrow> (projection M) h \<in> M\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
  using is_projection_on_existence  projection_intro2'
  by (metis projection_def someI_ex) 

lemma projection_uniq':
  fixes  M :: \<open>('a::complex_inner) set\<close>
  assumes  \<open>closed_subspace M\<close> and \<open>h - x \<in> orthogonal_complement M\<close> and \<open>x \<in> M\<close>
    and \<open>is_projection_on \<pi> M\<close>
  shows \<open>\<pi> h = x\<close>
proof-
  from \<open>is_projection_on \<pi> M\<close>
  have \<open>h - \<pi> h \<in> orthogonal_complement M \<and> \<pi> h \<in> M\<close>
    unfolding is_projection_on_def
    by blast
  hence \<open>\<pi> h \<in> M\<close> by blast
  have \<open>h - \<pi> h \<in> orthogonal_complement M\<close>
    using \<open>h - \<pi> h \<in> orthogonal_complement M \<and> \<pi> h \<in> M\<close> by blast
  have \<open>x - \<pi> h \<in> M\<close>
    using \<open>closed_subspace M\<close> \<open>\<pi> h \<in> M\<close>  \<open>x \<in> M\<close>
    unfolding closed_subspace_def
    by (simp add: complex_vector.subspace_diff)
  moreover have \<open>x - \<pi> h \<in> orthogonal_complement M\<close>
  proof-
    have \<open>closed_subspace (orthogonal_complement M)\<close>
      by (simp add: assms(1))
    from \<open>h - x \<in> orthogonal_complement M\<close>  \<open>h - \<pi> h \<in> orthogonal_complement M\<close>
    have  \<open>(h - \<pi> h) - (h - x) \<in> orthogonal_complement M\<close>
      using \<open>closed_subspace (orthogonal_complement M)\<close>
        complex_vector.subspace_diff closed_subspace_def by blast
    thus ?thesis by simp
  qed
  ultimately have \<open>x - \<pi> h \<in> M \<inter> (orthogonal_complement M)\<close>
    by auto
  moreover have \<open>M \<inter> (orthogonal_complement M) = {0}\<close>
    using \<open>closed_subspace M\<close> assms(3)  ortho_inter_zero
      complex_vector.subspace_def closed_subspace.subspace by metis
  ultimately have \<open>x - \<pi> h = 0\<close>
    by auto
  thus ?thesis
    by simp
qed

lemma projection_uniq:
  fixes  M :: \<open>('a::chilbert_space) set\<close>
  assumes  \<open>closed_subspace M\<close> and \<open>h - x \<in> orthogonal_complement M\<close> and \<open>x \<in> M\<close>
  shows \<open>(projection M) h = x\<close>
  by (smt ExistenceUniquenessProj add.commute assms(1) assms(2) assms(3) orthogonal_complement_def projection_intro1 projection_intro2 uminus_add_conv_diff)

lemma projection_fixed_points':
  \<open>is_projection_on \<pi> M \<Longrightarrow> closed_subspace M  \<Longrightarrow> x \<in> M \<Longrightarrow> \<pi> x = x\<close>
  for M :: \<open>('a::complex_inner) set\<close>
  using closed_subspace.subspace complex_vector.subspace_0
  unfolding is_projection_on_def
  by (metis (mono_tags, lifting) diff_self is_projection_on_def projection_uniq' subspace_orthog)


lemma projection_fixed_points:                         
  \<open>closed_subspace M  \<Longrightarrow> x \<in> M \<Longrightarrow> (projection M) x = x\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
  using projection_fixed_points'
  by (metis is_projection_on_existence projection_intro1 projection_intro2 projection_uniq')

\<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close>

proposition projectionPropertiesB':
  includes notation_norm
  fixes M :: \<open>('a::complex_inner) set\<close>
  assumes \<open>is_projection_on \<pi> M\<close>
  shows \<open>\<parallel> \<pi>  h \<parallel> \<le> \<parallel> h \<parallel>\<close>
proof-
  have \<open>h - \<pi> h \<in> orthogonal_complement M\<close> 
    using \<open>is_projection_on \<pi> M\<close>
    by (simp add: projection_intro1')    
  hence \<open>\<forall> k \<in> M. \<langle>  h - \<pi> h , k \<rangle> = 0\<close>
    using is_orthogonal_def
    using orthogonal_complement_D1 by blast 
  also have \<open>\<pi> h \<in>  M\<close>
    using \<open>is_projection_on \<pi> M\<close>
    by (simp add: projection_intro2')
  ultimately have \<open>\<langle>  h - \<pi> h , \<pi> h \<rangle> = 0\<close>
    by auto
  hence \<open>\<parallel> \<pi> h \<parallel>^2 + \<parallel> h - \<pi> h \<parallel>^2 = \<parallel> h \<parallel>^2\<close>
    using PythagoreanId by fastforce
  hence \<open>\<parallel>\<pi> h \<parallel>^2 \<le> \<parallel> h \<parallel>^2\<close>
    by (smt zero_le_power2)    
  thus ?thesis 
    using norm_ge_zero power2_le_imp_le by blast
qed

proposition projectionPropertiesB:
  includes notation_norm
  fixes M :: \<open>('a::chilbert_space) set\<close>
  shows \<open>closed_subspace M  \<Longrightarrow> \<parallel> (projection M) h \<parallel> \<le> \<parallel> h \<parallel>\<close>
  using projectionPropertiesB' 
  by (metis is_projection_on_existence projection_intro1 projection_intro2 projection_uniq')


\<comment> \<open>Theorem 2.7 (version) in @{cite conway2013course}\<close>
theorem projectionPropertiesA':
  \<open>is_projection_on \<pi> M \<Longrightarrow> closed_subspace M \<Longrightarrow> bounded_clinear \<pi>\<close>
  for M :: \<open>('a::complex_inner) set\<close>
proof-
  assume \<open>is_projection_on \<pi> M\<close>
  assume \<open>closed_subspace M\<close>
  hence \<open>complex_vector.subspace (orthogonal_complement M)\<close>
    by (simp add: closed_subspace.subspace)    
  have \<open>\<pi> (c *\<^sub>C x) = c *\<^sub>C (\<pi> x)\<close> for x c
  proof - (* sledgehammer *)
    have f1: "\<forall>a. a - \<pi> a \<in> orthogonal_complement M \<and> \<pi> a \<in> M"
      by (metis \<open>is_projection_on \<pi> M\<close> is_projection_on_def)
    hence "c *\<^sub>C x - c *\<^sub>C \<pi> x \<in> orthogonal_complement M"
      by (metis (no_types) \<open>complex_vector.subspace (orthogonal_complement M)\<close> add_diff_cancel_right' complex_vector.subspace_def diff_add_cancel scaleC_add_right)
    thus ?thesis
      using f1 by (meson \<open>closed_subspace M\<close> \<open>is_projection_on \<pi> M\<close> closed_subspace.subspace complex_vector.subspace_def projection_uniq')
  qed    
  moreover have \<open>\<pi> (x + y) =  (\<pi> x) + (\<pi> y)\<close>
    for x y
  proof-
    have \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> M\<close>
    proof -
      have "\<forall>A. \<not> closed_subspace (A::'a set) \<or> complex_vector.subspace A"
        by (metis closed_subspace.subspace)
      hence "complex_vector.subspace M"
        by (metis \<open>closed_subspace M\<close>)
      thus ?thesis
        by (meson \<open>is_projection_on \<pi> M\<close> complex_vector.subspace_add complex_vector.subspace_diff is_projection_on_def)
    qed      
    moreover have \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> orthogonal_complement M\<close>
    proof-
      from \<open>closed_subspace M\<close>
      have \<open>closed_subspace (orthogonal_complement M)\<close>
        by simp
      thus ?thesis
      proof - (* sledgehammer *)
        have f1: "\<forall>a aa. (aa::'a) + (a - aa) = a"
          by (metis add.commute diff_add_cancel)
        have f2: "\<forall>a aa. (aa::'a) - aa = a - a"
          by auto
        hence f3: "\<forall>a. a - a \<in> orthogonal_complement M"
          by (metis (full_types) \<open>complex_vector.subspace (orthogonal_complement M)\<close> \<open>is_projection_on \<pi> M\<close> complex_vector.subspace_diff is_projection_on_def)
        have "\<forall>a aa. (a \<in> orthogonal_complement M \<or> a + aa \<notin> orthogonal_complement M) \<or> aa \<notin> orthogonal_complement M"
          using f2 f1 by (metis \<open>complex_vector.subspace (orthogonal_complement M)\<close> add_diff_eq complex_vector.subspace_diff)
        hence "\<forall>a aa ab. (a \<in> orthogonal_complement M \<or> ab - (aa + a) \<notin> orthogonal_complement M) \<or> ab - aa \<notin> orthogonal_complement M"
          using f1 by (metis diff_diff_add)
        hence f4: "\<forall>a aa f. (f a - aa \<in> orthogonal_complement M \<or> a - aa \<notin> orthogonal_complement M) \<or> \<not> is_projection_on f M"
          using f1 by (metis (no_types) is_projection_on_def)
        have f5: "\<forall>a aa ab ac. (ac::'a) - (ab + (aa - a)) = ac + (a - (aa + ab))"
          by auto
        have "x - \<pi> x \<in> orthogonal_complement M"
          by (metis \<open>is_projection_on \<pi> M\<close> is_projection_on_def)
        thus ?thesis
          using f5 f4 f3 by (metis \<open>complex_vector.subspace (orthogonal_complement M)\<close> \<open>is_projection_on \<pi> M\<close> add_diff_eq complex_vector.subspace_diff diff_diff_add diff_diff_eq2)
      qed 
    qed
    ultimately have \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> M \<inter> (orthogonal_complement M)\<close>
      by simp
    moreover have \<open>M \<inter> (orthogonal_complement M) = {0}\<close>
      by (simp add: \<open>closed_subspace M\<close> closed_subspace.subspace complex_vector.subspace_0 ortho_inter_zero)      
    ultimately have \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) = 0\<close>
      by auto      
    thus ?thesis by simp
  qed
  ultimately have \<open>clinear \<pi>\<close>
    by (simp add: clinearI)
  moreover have \<open>\<exists> K. \<forall> x. norm (\<pi> x) \<le> norm x * K\<close>
  proof-
    have \<open>\<forall> x. norm (\<pi> x) \<le> norm x\<close>
      using \<open>is_projection_on \<pi> M\<close> projectionPropertiesB' by auto
    hence \<open>\<forall> x. norm (\<pi> x) \<le> norm x * 1\<close>
      by simp
    thus ?thesis
      by blast
  qed
  ultimately show ?thesis 
    unfolding bounded_clinear_def
    by blast
qed

theorem projectionPropertiesA:
  \<open>closed_subspace M \<Longrightarrow> bounded_clinear (projection M)\<close> 
  for M :: \<open>('a::chilbert_space) set\<close>
  using projectionPropertiesA' is_projection_on_def projection_intro1 projection_intro2
  by fastforce

\<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close>

proposition projectionPropertiesC':
  \<open>is_projection_on \<pi> M \<Longrightarrow> closed_subspace M \<Longrightarrow> \<pi> \<circ> \<pi> = \<pi>\<close>
  for M :: \<open>('a::complex_inner) set\<close>
proof-
  assume \<open>is_projection_on \<pi> M\<close> and \<open>closed_subspace M\<close>
  have \<open>(\<pi> \<circ> \<pi>) x = \<pi> x\<close>
    for x
  proof-
    have \<open>\<pi> x \<in> M\<close>
      by (simp add: \<open>is_projection_on \<pi> M\<close> projection_intro2')      
    hence \<open>\<pi> (\<pi> x) = \<pi> x\<close>
      using \<open>is_projection_on \<pi> M\<close> \<open>closed_subspace M\<close> projection_fixed_points' by auto
    thus ?thesis by simp
  qed
  thus ?thesis by blast
qed

proposition projectionPropertiesC:
  \<open>closed_subspace M \<Longrightarrow> (projection M) \<circ> (projection M) = projection M\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
  using projectionPropertiesC'
  by (metis is_projection_on_def projection_intro1 projection_intro2) 

lemma ker_op_lin:
  \<open>bounded_clinear f \<Longrightarrow> closed_subspace  (f -` {0})\<close>
proof-
  assume \<open>bounded_clinear f\<close>
  have \<open>x \<in>  {x. f x = 0} \<Longrightarrow> t *\<^sub>C x \<in> {x. f x = 0}\<close> for x t
  proof-
    assume \<open>x \<in>  {x. f x = 0}\<close>
    hence \<open>f x = 0\<close>
      by blast
    hence  \<open>f  (t *\<^sub>C x) = 0\<close>
      using \<open>bounded_clinear f\<close> bounded_clinear.clinear
      by (simp add: bounded_clinear.is_clinear complex_vector.linear_scale) 
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
      unfolding bounded_clinear_def clinear_def Vector_Spaces.linear_def module_hom_def module_hom_axioms_def
      by auto
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
  moreover have \<open>0 \<in> {x. f x = 0}\<close>
  proof-
    have \<open>clinear f\<close>
      using \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def by blast
    hence \<open>f 0 = 0\<close>
      by (simp add: complex_vector.linear_0)      
    thus ?thesis by blast
  qed
  ultimately show ?thesis
  proof - (* sledgehammer *)
    obtain aa :: "'a set \<Rightarrow> 'a" where
      "\<forall>x0. (\<exists>v1. v1 \<in> x0 \<and> (\<exists>v2. v2 \<in> x0 \<and> v1 + v2 \<notin> x0)) = (aa x0 \<in> x0 \<and> (\<exists>v2. v2 \<in> x0 \<and> aa x0 + v2 \<notin> x0))"
      by moura
    then obtain aaa :: "'a set \<Rightarrow> 'a" where
      f1: "\<forall>A. (\<exists>a. a \<in> A \<and> (\<exists>aa. aa \<in> A \<and> a + aa \<notin> A)) = (aa A \<in> A \<and> aaa A \<in> A \<and> aa A + aaa A \<notin> A)"
      by (metis (full_types))
    obtain aab :: "'a set \<Rightarrow> 'a" and cc :: "'a set \<Rightarrow> complex" where
      "\<forall>x0. (\<exists>v1 v2. v2 \<in> x0 \<and> v1 *\<^sub>C v2 \<notin> x0) = (aab x0 \<in> x0 \<and> cc x0 *\<^sub>C aab x0 \<notin> x0)"
      by moura
    hence f2: "\<forall>A. (\<not> complex_vector.subspace A \<or> 0 \<in> A \<and> (\<forall>a. a \<notin> A \<or> (\<forall>aa. aa \<notin> A \<or> a + aa \<in> A)) \<and> (\<forall>c a. a \<notin> A \<or> c *\<^sub>C a \<in> A)) \<and> (complex_vector.subspace A \<or> 0 \<notin> A \<or> aa A \<in> A \<and> aaa A \<in> A \<and> aa A + aaa A \<notin> A \<or> aab A \<in> A \<and> cc A *\<^sub>C aab A \<notin> A)"
      using f1 by (metis (no_types) complex_vector.subspace_def)
    have f3: "f -` {b. b = 0 \<or> b \<in> {}} = {a. f a = 0}"
      by blast
    have "closed_subspace {a. f a = 0}"
      using f2 by (metis \<open>0 \<in> {x. f x = 0}\<close> \<open>\<And>t c. t \<in> {x. f x = 0} \<Longrightarrow> c *\<^sub>C t \<in> {x. f x = 0}\<close> \<open>\<And>v u. \<lbrakk>u \<in> {x. f x = 0}; v \<in> {x. f x = 0}\<rbrakk> \<Longrightarrow> u + v \<in> {x. f x = 0}\<close> \<open>closed {x. f x = 0}\<close> closed_subspace.intro)
    thus ?thesis
      using f3 by auto
  qed
qed

proposition projectionPropertiesD':
  \<open>is_projection_on \<pi> M \<Longrightarrow> closed_subspace M  \<Longrightarrow> \<pi> -` {0} = (orthogonal_complement M)\<close>
  for M :: \<open>('a::complex_inner) set\<close>
proof-
  assume \<open>is_projection_on \<pi> M\<close> and \<open>closed_subspace M\<close> 
  have \<open>x \<in> orthogonal_complement M \<Longrightarrow> x \<in> (\<pi> -` {0})\<close> for x
  proof-
    assume \<open>x \<in> orthogonal_complement M\<close>
    moreover have \<open>\<pi> x \<in> M\<close>
      using  \<open>is_projection_on \<pi> M\<close>
      by (simp add: projection_intro2')
    hence \<open>\<pi> x = 0\<close>
    proof - (* sledgehammer *)
      have f1: "\<And>a aa. a \<notin> M \<or> \<langle>x - aa, a\<rangle> = - \<langle>aa, a\<rangle>"
        by (metis (no_types) calculation cinner_diff_left diff_0 orthogonal_complement_D1)
      have "\<And>a aa. a \<notin> M \<or> \<langle>aa - \<pi> aa, a\<rangle> = 0"
        by (meson \<open>is_projection_on \<pi> M\<close> is_projection_on_def orthogonal_complement_D1)
      thus ?thesis
        using f1 by (metis (no_types) \<open>is_projection_on \<pi> M\<close> add.inverse_inverse cinner_eq_zero_iff diff_0 diff_self is_projection_on_def)
    qed      
    hence \<open>x \<in> (\<pi> -` {0})\<close>
      by simp
    thus ?thesis
      by simp
  qed
  moreover have \<open>x \<in> \<pi> -` {0} \<Longrightarrow> x \<in> orthogonal_complement M\<close> for x
  proof-
    assume \<open>x \<in> \<pi> -` {0}\<close>
    hence  \<open>x \<in> {y.  \<pi> x = 0}\<close>
      by simp      
    hence \<open>\<pi> x = 0\<close>
      by (metis (mono_tags, lifting) mem_Collect_eq)
    hence  \<open>x \<in> orthogonal_complement M\<close>
      by (metis \<open>is_projection_on \<pi> M\<close> diff_zero is_projection_on_def)   
    thus ?thesis
      by simp
  qed
  ultimately have \<open>orthogonal_complement M = \<pi> -` {0}\<close>         
    by blast
  thus ?thesis 
    by blast
qed

\<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close> 
proposition projectionPropertiesD:
  \<open>closed_subspace M  \<Longrightarrow> (projection M) -` {0} = (orthogonal_complement M)\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
  by (simp add: projectionPropertiesD' is_projection_on_def projection_intro1 projection_intro2)

lemma range_lin:
  \<open>clinear f \<Longrightarrow>  complex_vector.subspace (range f)\<close>
proof-
  assume \<open>clinear f\<close>
  obtain A where \<open>A = (range f)\<close>
    by simp
  have "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x+y\<in>A" for x y
  proof-
    assume \<open>x \<in> A\<close>
    then obtain xx where \<open>x = f xx\<close> using  \<open>A = (range f)\<close> 
      using mem_Collect_eq
      by blast
    assume \<open>y \<in> A\<close>
    then obtain yy where \<open>y = f yy\<close> using  \<open>A = (range f)\<close> 
      using mem_Collect_eq
      by blast
    have \<open>x + y = f (xx + yy)\<close> 
      using Modules.additive_def \<open>clinear f\<close> \<open>x = f xx\<close> \<open>y = f yy\<close>  clinear_def
      by (simp add: complex_vector.linear_add)
    thus ?thesis 
      using \<open>A = range f\<close> mem_Collect_eq
      by blast 
  qed
  have  "x\<in>A \<Longrightarrow> c *\<^sub>C x \<in> A" for x c
  proof-
    assume \<open>x \<in> A\<close>
    then obtain y where \<open>x = f y\<close>
      using  \<open>A = (range f)\<close> mem_Collect_eq
      by blast
    have \<open>c *\<^sub>C x = f (c *\<^sub>C y)\<close>
      using  \<open>x = f y\<close> \<open>clinear f\<close>
      by (simp add: complex_vector.linear_scale)
    thus ?thesis
      using  \<open>x = f y\<close> \<open>A = range f\<close> mem_Collect_eq
      by blast
  qed
  have  "0 \<in> A"
  proof-
    have \<open>0 = f 0\<close> 
      using \<open>clinear f\<close> additive.zero clinear_def
      by (simp add: complex_vector.linear_0)     
    hence \<open>0 \<in> range f\<close>
      using  mem_Collect_eq
      by auto 
    thus ?thesis 
      by (simp add: \<open>A = range f\<close>)
  qed
  thus ?thesis 
    using \<open>A = range f\<close> \<open>\<And>x c. x \<in> A \<Longrightarrow> c *\<^sub>C x \<in> A\<close> \<open>\<And>y x. \<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> x + y \<in> A\<close>
      complex_vector.subspace_def
    by (simp add: complex_vector.subspace_def) 
qed

theorem projectionPropertiesE':
  \<open>is_projection_on \<pi> M \<Longrightarrow> closed_subspace M \<Longrightarrow> range \<pi> = M\<close>
  for M :: \<open>('a::complex_inner) set\<close>
proof-
  assume \<open>is_projection_on \<pi> M\<close> and \<open>closed_subspace M\<close>
  hence \<open>x \<in> range \<pi> \<Longrightarrow> x \<in> M\<close> for x
    using projection_intro2' by fastforce     
  moreover have \<open>x \<in> M \<Longrightarrow> x \<in> range \<pi>\<close> for x
    using \<open>closed_subspace M\<close>
    by (metis UNIV_I \<open>is_projection_on \<pi> M\<close> image_eqI projection_fixed_points') 
  ultimately show ?thesis by blast
qed

\<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close> 
theorem projectionPropertiesE:
  \<open>closed_subspace M \<Longrightarrow> range  (projection M) = M\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
proof - (* sledgehammer *)
  assume a1: "closed_subspace M"
  obtain aa :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
    f2: "\<forall>f A. (\<not> is_projection_on f A \<or> (\<forall>a. a - f a \<in> orthogonal_complement A \<and> f a \<in> A)) \<and> (is_projection_on f A \<or> aa A f - f (aa A f) \<notin> orthogonal_complement A \<or> f (aa A f) \<notin> A)"
    by (metis (no_types) is_projection_on_def)
  obtain aaa :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a" where
    "is_projection_on (aaa M) M"
    using a1 by (meson is_projection_on_existence)
  hence "\<forall>a. a - aaa M a \<in> orthogonal_complement M \<and> aaa M a \<in> M"
    using f2 by blast
  thus ?thesis
    using f2 a1 by (metis (no_types) projectionPropertiesE' projection_uniq)
qed 

lemma pre_ortho_twice: "complex_vector.subspace M 
\<Longrightarrow> M \<subseteq> (orthogonal_complement (orthogonal_complement M))" 
proof-
  have \<open>x \<in> M \<Longrightarrow> x \<in> (orthogonal_complement (orthogonal_complement M))\<close> for x 
  proof-
    assume \<open>x \<in> M\<close>
    hence \<open>\<forall> y \<in> (orthogonal_complement M). \<langle> x, y \<rangle> = 0\<close>
      using orthogonal_complement_D2 by auto
    hence \<open>x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      by (simp add: orthogonal_complement_def)
    thus ?thesis by blast
  qed            
  thus ?thesis 
    by (simp add: subsetI)
qed

lemma ProjOntoOrtho':
  \<open>is_projection_on \<pi> M \<Longrightarrow> is_projection_on \<sigma> (orthogonal_complement M)
 \<Longrightarrow> closed_subspace M  \<Longrightarrow> id - \<pi> = \<sigma>\<close>
  for M :: \<open>('a::complex_inner) set\<close>
proof-
  assume \<open>is_projection_on \<pi> M\<close> and \<open>is_projection_on \<sigma> (orthogonal_complement M)\<close> and \<open>closed_subspace M\<close>
  have   \<open> (id - \<pi>) x = \<sigma> x \<close> for x
  proof-
    have \<open>x - \<pi> x \<in> orthogonal_complement M\<close>
      using \<open>closed_subspace M\<close>
      by (simp add: \<open>is_projection_on \<pi> M\<close> projection_intro1') 
    hence \<open>(id -  \<pi>) x \<in> orthogonal_complement M\<close>
      by simp
    have \<open>\<pi> x \<in>  M\<close>
      by (simp add: \<open>is_projection_on \<pi> M\<close> projection_intro2') 
    hence  \<open>x - (id - \<pi>) x \<in>  M\<close>
      by simp
    hence \<open>\<pi> x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      using pre_ortho_twice  \<open>closed_subspace M\<close> complex_vector.subspace_def
      unfolding closed_subspace_def
      using \<open>\<pi> x \<in> M\<close> by blast            
    hence  \<open>x - (id -  \<pi>) x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      by simp
    thus ?thesis
      using \<open>closed_subspace M\<close>  subspace_orthog
      by (metis \<open>(id - \<pi>) x \<in> orthogonal_complement M\<close> \<open>is_projection_on \<sigma> (orthogonal_complement M)\<close> projection_uniq')
  qed
  thus ?thesis by blast
qed

\<comment> \<open>Exercice 2 (section 2, chapter I) in  @{cite conway2013course}\<close> 
lemma ProjOntoOrtho:
  \<open>closed_subspace M  \<Longrightarrow> id - projection M = projection (orthogonal_complement M)\<close>
  for M :: \<open>('a::chilbert_space) set\<close>
  using ProjOntoOrtho'
  by (metis is_projection_on_def projection_intro1 projection_intro2 subspace_orthog)

\<comment> \<open>Corollary 2.8 in  @{cite conway2013course}\<close>
theorem orthogonal_complement_twice:
  "closed_subspace M \<Longrightarrow> (orthogonal_complement (orthogonal_complement M)) = M"
  for M :: \<open>('a::chilbert_space) set\<close>
proof-
  assume \<open>closed_subspace M\<close>
  have \<open>(orthogonal_complement (orthogonal_complement M)) =  (projection (orthogonal_complement M)) -` {0}\<close>
    by (simp add: \<open>closed_subspace M\<close> projectionPropertiesD)
  also have \<open>... = ( id - (projection M) ) -` {0}\<close>
    by (simp add: ProjOntoOrtho \<open>closed_subspace M\<close>)
  also have \<open>... = M\<close>
  proof-
    have \<open>x \<in>  M \<Longrightarrow> x \<in>  ( ( id - (projection M) ) -` {0} )\<close> for x
    proof-
      assume \<open>x \<in> M\<close>
      hence \<open>(projection M) x = x\<close>
        using \<open>closed_subspace M\<close> projection_fixed_points by auto
      hence \<open>(id - (projection M)) x = 0\<close> 
        by simp
      hence \<open>x \<in> {v. (id - (projection M)) v = 0}\<close>
        by simp
      hence \<open>x \<in>  (real_vector.span {v. (id - (projection M)) v = 0})\<close>
        using span_superset
        by (simp add: real_vector.span_base)         
      hence \<open>x \<in> ( ( id - (projection M) ) -` {0} )\<close> 
        using ProjOntoOrtho \<open>(id - projection M) x = 0\<close> \<open>closed_subspace M\<close> calculation diff_zero  projection_intro1
          complex_vector.subspace_def \<open>(id - projection M) x = 0\<close> by blast
      thus ?thesis 
        by simp                  
    qed
    moreover have \<open>x \<in>  ( ( id - (projection M) ) -` {0} ) \<Longrightarrow> x \<in>  M\<close> for x
    proof-
      assume \<open>x \<in>  ( ( id - (projection M) ) -` {0} )\<close>
      hence \<open>(id - (projection M)) x = 0\<close>
        by simp
      hence \<open>(projection M) x = x\<close>
        by auto
      hence \<open>(projection M) x \<in>  M\<close>
        by (metis \<open>closed_subspace M\<close> projection_intro2)
      hence \<open>x \<in>  M\<close>
        using  \<open>(projection M) x = x\<close> 
        by simp
      thus ?thesis by blast
    qed
    ultimately have \<open>x \<in>  M \<longleftrightarrow> x \<in>  ( ( id - (projection M) ) -` {0} )\<close> for x
      by blast
    hence \<open> (  ( id - (projection M) ) -` {0} ) =  M\<close>
      by blast
    thus ?thesis
      by simp
  qed     
  finally show ?thesis by blast
qed


lemma ortho_leq[simp]:
  fixes  A B :: \<open>('a::chilbert_space) set\<close>
  assumes \<open>closed_subspace A\<close> and  \<open>closed_subspace B\<close>
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
  "(orthogonal_complement (top::('a::chilbert_space) set)) = ({0}::'a set)"
proof-
  have \<open>({0}::'a set) \<subseteq>  (orthogonal_complement (top::'a set))\<close>
    using complex_vector.subspace_def
    by (metis Int_iff complex_vector.subspace_0 complex_vector.subspace_UNIV empty_subsetI insert_subset ortho_inter_zero singletonI)
  moreover have  \<open>({0}::('a) set) \<supseteq>  (orthogonal_complement (top::('a) set))\<close>
    using  ortho_leq orthogonal_complement_twice top_greatest
    by (metis Complex_Vector_Spaces.subspace_0 Complex_Vector_Spaces.subspace_UNIV subspace_orthog)
  ultimately show ?thesis by blast
qed

lemma ortho_bot[simp]:
  "(orthogonal_complement ({0}::'a::chilbert_space set))  = (top::'a set)"
  using  orthogonal_complement_twice 
  by (metis Complex_Vector_Spaces.subspace_UNIV ortho_top)


subsection \<open>Closed sum\<close>

definition closed_sum:: \<open>('a::{complex_vector,topological_space}) set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>closed_sum A B = closure (A + B)\<close>

notation closed_sum (infixl "+\<^sub>M" 65)

lemma sum_existential:
  \<open>x \<in> (A + B) \<Longrightarrow> \<exists> a\<in>A. \<exists> b\<in>B. x = a + b\<close>
proof -
  assume "x \<in> (A + B)"
  hence "\<exists>a aa. x = a + aa \<and> a \<in> A \<and> aa \<in> B"
    by (meson set_plus_elim)    
  thus ?thesis
    by (metis (lifting))
qed

lemma is_closed_subspace_comm:                                                                 
  assumes \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close>
  shows \<open>A +\<^sub>M B = B +\<^sub>M A\<close>
  by (smt Collect_cong add.commute closed_sum_def)

lemma cinner_isCont_left:
  \<open>isCont (\<lambda> t. \<langle> t , x \<rangle>) y\<close>
proof-
  have \<open>s \<longlonglongrightarrow> y \<Longrightarrow> ((\<lambda> t. \<langle> t , x \<rangle>) \<circ> s) \<longlonglongrightarrow> (\<lambda> t. \<langle> t , x \<rangle>) y\<close>
    for s::\<open>nat \<Rightarrow> _\<close>
  proof-
    assume \<open>s \<longlonglongrightarrow> y\<close>
    have \<open>\<exists> K. \<forall> u v. norm \<langle>u , v \<rangle> \<le> norm u * norm v * K\<close>
      using bounded_sesquilinear.bounded bounded_sesquilinear_cinner by auto
    then obtain K where  \<open>\<forall> u v::'a. norm \<langle>u , v\<rangle> \<le> norm u * norm v * K\<close>
      by blast
    hence CS: \<open>norm \<langle>u , v\<rangle> \<le> norm u * norm v * K\<close>
      for u::'a and v::'a
      by auto
    have \<open>norm \<langle>s n - y , x\<rangle> \<le> norm (s n - y) * norm x * K\<close>
      for n
      using CS[where u1 = "s n - y" and v1 = "x"]
      by blast
    hence \<open>\<forall> n. cmod \<langle>s n - y, x\<rangle> \<le> norm (norm (s n - y) * norm x) * norm K\<close>
      by (smt norm_mult real_norm_def)      
    moreover have \<open>(\<lambda> n.  norm (s n - y) * norm x) \<longlonglongrightarrow> 0\<close>
    proof-
      have \<open>(\<lambda> n.  norm (s n - y)) \<longlonglongrightarrow> 0\<close>
        using \<open>s \<longlonglongrightarrow> y\<close>
        by (simp add: LIM_zero_iff tendsto_norm_zero)
      thus ?thesis
        by (simp add: tendsto_mult_left_zero) 
    qed
    ultimately have \<open>(\<lambda> n. \<langle> s n - y , x \<rangle>) \<longlonglongrightarrow> 0\<close>
      using Limits.tendsto_0_le[where g = "(\<lambda> n. \<langle> s n - y , x \<rangle>)" and f = "(\<lambda> n. norm (s n - y) * norm x)" and K = "norm K"]
      by auto      
    moreover have \<open>\<langle> s n - y , x \<rangle> =  \<langle> s n , x \<rangle> - \<langle> y , x \<rangle>\<close>
      for n
      by (simp add: cinner_diff_left)      
    ultimately have \<open>(\<lambda> n. \<langle> s n , x \<rangle> - \<langle> y , x \<rangle>) \<longlonglongrightarrow> 0\<close>
      by simp
    hence \<open>(\<lambda> n. \<langle> s n , x \<rangle>) \<longlonglongrightarrow> \<langle> y , x \<rangle>\<close>
      by (simp add: LIM_zero_iff)      
    hence \<open>(\<lambda> n. ((\<lambda> t. \<langle> t , x \<rangle>) \<circ> s) n) \<longlonglongrightarrow> \<langle> y , x \<rangle>\<close>
      by auto
    hence \<open>((\<lambda> t. \<langle> t , x \<rangle>) \<circ> s) \<longlonglongrightarrow> \<langle> y , x \<rangle>\<close>
      by blast
    thus ?thesis by auto
  qed
  hence \<open>\<forall> s. (s \<longlonglongrightarrow> y) \<longrightarrow> (((\<lambda> t. \<langle> t , x \<rangle>) \<circ> s) \<longlonglongrightarrow> (\<lambda> t. \<langle> t , x \<rangle>) y)\<close>
    by blast
  thus ?thesis 
    using Elementary_Topology.continuous_at_sequentially
      [where a = "y" and f = "(\<lambda> t. \<langle> t , x \<rangle>) "]
    by blast
qed

lemma cinner_isCont_right:
  \<open>isCont (\<lambda> t. \<langle> x, t \<rangle>) y\<close>
proof-
  have \<open>(\<lambda> t. \<langle> x, t \<rangle>) = cnj \<circ> (\<lambda> t. \<langle> t, x \<rangle>)\<close>
    by auto
  moreover have \<open>isCont (\<lambda> t. \<langle> t , x \<rangle>) y\<close>
    by (simp add: cinner_isCont_left)
  moreover have \<open>isCont cnj ((\<lambda> t. \<langle> t , x \<rangle>) y)\<close>
    using Complex.isCont_cnj[where g = "id" and a = "\<langle>y, x\<rangle>"]
    by auto
  ultimately show ?thesis
    by (metis continuous_at_compose) 
qed

lemma OrthoClosed:
  fixes A ::"('a::complex_inner) set"
  shows \<open>closed (orthogonal_complement A)\<close>                                                
proof-
  have \<open>\<forall> n. x n \<in> (orthogonal_complement A) \<Longrightarrow> x \<longlonglongrightarrow> l \<Longrightarrow> l \<in> (orthogonal_complement A)\<close> for x l
  proof-
    assume \<open>\<forall> n. x n \<in> (orthogonal_complement A)\<close>
    hence \<open>\<forall> n. \<forall> y \<in> A. \<langle> y , x n \<rangle> = 0\<close>
      by (simp add: orthogonal_complement_D2)
    assume \<open>x \<longlonglongrightarrow> l\<close>
    moreover have \<open>isCont (\<lambda> t. \<langle> y , t \<rangle>) l\<close> for y
      using cinner_isCont_right by blast
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
  fixes A ::"('a::complex_inner) set"
  shows \<open>(orthogonal_complement A) = (orthogonal_complement (closure A))\<close>
proof-
  have \<open>x \<in> (orthogonal_complement A) \<Longrightarrow> x \<in> (orthogonal_complement (closure A))\<close> for x
  proof-
    assume \<open>x \<in> (orthogonal_complement A)\<close>
    hence \<open>\<forall> y \<in> A. \<langle> y , x \<rangle> = 0\<close>
      by (simp add: orthogonal_complement_D2)
    hence \<open>y \<in> closure A \<Longrightarrow> \<langle> y , x \<rangle> = 0\<close> for y
    proof-
      assume \<open>y \<in> closure A\<close>  
      then obtain yy where \<open>\<forall> n. yy n \<in> A\<close> and \<open>yy \<longlonglongrightarrow> y\<close> 
        by (meson closure_sequential)
      have \<open>isCont (\<lambda> t. \<langle> t , x \<rangle>) y\<close>
        using cinner_isCont_left by blast
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

lemma subspace_closed_plus:
  fixes A B::"('a::complex_normed_vector) set"
  assumes \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close>
  shows \<open>closed_subspace (A +\<^sub>M B)\<close>
  using assms(1) assms(2) closed_sum_def 
  by (metis closed_subspace.subspace subspace_I subspace_plus)

lemma DeMorganOrtho:        
  fixes A B::"('a::complex_inner) set"
  assumes \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close>
  shows \<open>orthogonal_complement (A +\<^sub>M B) = (orthogonal_complement A) \<inter> (orthogonal_complement B)\<close>
proof-
  have \<open>x \<in> (orthogonal_complement (A +\<^sub>M B)) \<Longrightarrow> x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)\<close> for x
  proof-
    assume \<open>x \<in> (orthogonal_complement (A +\<^sub>M B))\<close>
    moreover have \<open>orthogonal_complement (A +\<^sub>M B) = (orthogonal_complement (A + B))\<close>
      unfolding closed_sum_def by (subst OrthoClosedEq[symmetric], simp)
    ultimately have \<open>x \<in> (orthogonal_complement (A + B))\<close>
      by smt
    hence \<open>\<forall> z \<in> (A + B). \<langle> z , x \<rangle> = 0\<close> 
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    hence \<open>\<forall> z \<in> A. \<langle> z , x \<rangle> = 0\<close> 
    proof-
      have \<open>0 \<in> B\<close>
        using assms(2) complex_vector.subspace_def
        unfolding closed_subspace_def
        by auto
      hence \<open>A \<subseteq> A + B\<close>
        using subset_iff add.commute set_zero_plus2 
        by fastforce
      thus ?thesis
        using  \<open>\<forall> z \<in> (A + B). \<langle> z , x \<rangle> = 0\<close> by auto
    qed
    hence \<open>x \<in> (orthogonal_complement A)\<close>
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    have \<open>\<forall> z \<in> B. \<langle> z , x \<rangle> = 0\<close> 
    proof-
      have \<open>0 \<in> A\<close>
        using assms(1) complex_vector.subspace_def
        unfolding closed_subspace_def
        by auto
      hence \<open>B \<subseteq> A + B\<close>
        using subset_iff set_zero_plus2 by blast        
      thus ?thesis
        using  \<open>\<forall> z \<in> (A + B). \<langle> z , x \<rangle> = 0\<close> by auto
    qed
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
      by (simp add: orthogonal_complement_D2)
    have \<open>x \<in> (orthogonal_complement B)\<close> using \<open>x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)\<close> by blast
    hence \<open>\<forall> y\<in> B. \<langle> y , x \<rangle> = 0\<close>
      by (simp add: orthogonal_complement_D2)
    have \<open>\<forall> a\<in>A. \<forall> b\<in>B. \<langle> a+b , x \<rangle> = 0\<close>
      by (simp add: \<open>\<forall>y\<in>A. \<langle>y , x\<rangle> = 0\<close> \<open>\<forall>y\<in>B. \<langle>y , x\<rangle> = 0\<close> cinner_left_distrib)
    hence \<open>\<forall> y \<in> (A + B). \<langle> y , x \<rangle> = 0\<close>
      using sum_existential by blast
    hence \<open>x \<in> (orthogonal_complement (A + B))\<close>
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    moreover have \<open>(orthogonal_complement (A + B)) = (orthogonal_complement (A +\<^sub>M B))\<close>
      unfolding closed_sum_def by (subst OrthoClosedEq[symmetric], simp)
    ultimately have \<open>x \<in> (orthogonal_complement (A +\<^sub>M B))\<close>
      by blast
    thus ?thesis
      by blast
  qed
  ultimately show ?thesis by blast
qed

theorem ortho_decomp:
  fixes x :: \<open>'a::chilbert_space\<close>
  assumes  \<open>closed_subspace M\<close>
  shows \<open>x = (projection M) x + (projection (orthogonal_complement M)) x\<close>
  using ProjOntoOrtho assms diff_add_cancel id_apply  minus_apply orthogonal_complement_twice
    complex_vector.subspace_def
  by (smt subspace_orthog)

lemma DeMorganOrthoDual:
  fixes A B::"('a::chilbert_space) set"
  assumes \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close>
  shows  \<open>orthogonal_complement (A \<inter> B) = ((orthogonal_complement A) +\<^sub>M (orthogonal_complement B))\<close>  
proof-
  have \<open>orthogonal_complement (A \<inter> B) = (orthogonal_complement ((orthogonal_complement (orthogonal_complement A)) \<inter> (orthogonal_complement (orthogonal_complement B) )))\<close>
    by (metis assms(1) assms(2) orthogonal_complement_twice)
  also have \<open>... = (orthogonal_complement ( orthogonal_complement ((orthogonal_complement A) +\<^sub>M (orthogonal_complement B)) ))\<close>
    using DeMorganOrtho assms(1) assms(2) complex_vector.subspace_def
    by (simp add: DeMorganOrtho)
  also have \<open>... = ((orthogonal_complement A) +\<^sub>M (orthogonal_complement B))\<close>
    using assms(1) assms(2) orthogonal_complement_twice
      complex_vector.subspace_def
    by (simp add: orthogonal_complement_twice subspace_closed_plus)
  finally show ?thesis by blast
qed


lemma is_closed_subspace_asso:
  fixes A B C::"('a::chilbert_space) set"
  assumes \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close> and \<open>closed_subspace C\<close>
  shows \<open>A +\<^sub>M (B +\<^sub>M C) = (A +\<^sub>M B) +\<^sub>M C\<close>
proof-
  have \<open>complex_vector.subspace (B +\<^sub>M C)\<close>
    using assms(2) assms(3)  complex_vector.subspace_def
    by (meson closed_subspace.subspace subspace_closed_plus)
  moreover have \<open>closed (B +\<^sub>M C)\<close>
    by (simp add: closed_sum_def)
  ultimately have \<open>closed_subspace (B +\<^sub>M C)\<close>
    by (simp add: closed_subspace_def)
  hence \<open>closed_subspace (A +\<^sub>M (B +\<^sub>M C))\<close>
    using DeMorganOrthoDual assms(1)  orthogonal_complement_twice
      complex_vector.subspace_def
    by (simp add: subspace_closed_plus)
  have \<open>(A +\<^sub>M (B +\<^sub>M C)) = (orthogonal_complement (orthogonal_complement (A +\<^sub>M (B +\<^sub>M C))))\<close>
    by (smt \<open>closed_subspace (A +\<^sub>M (B +\<^sub>M C))\<close> orthogonal_complement_twice)
  also have  \<open>... = (orthogonal_complement (  (orthogonal_complement A) \<inter> (orthogonal_complement (B +\<^sub>M C))  ))\<close>
    by (simp add: DeMorganOrtho \<open>closed_subspace (B +\<^sub>M C)\<close> assms(1))
  also have  \<open>... = (orthogonal_complement (  (orthogonal_complement A) \<inter> ((orthogonal_complement B) \<inter> (orthogonal_complement C))  ))\<close>
    by (simp add: DeMorganOrtho assms(2) assms(3))
  also have  \<open>... = (orthogonal_complement (  ((orthogonal_complement A) \<inter> (orthogonal_complement B)) \<inter> (orthogonal_complement C)  ))\<close>
    by (simp add: inf_assoc)
  also have  \<open>... = (orthogonal_complement (orthogonal_complement  ((orthogonal_complement((orthogonal_complement A) \<inter> (orthogonal_complement B))))  \<inter> (orthogonal_complement C)  ))\<close>
    using assms(1) assms(2)  
    by (simp add: orthogonal_complement_twice)
  also have  \<open>... = (orthogonal_complement ( orthogonal_complement ( (A +\<^sub>M B) +\<^sub>M C )  ))\<close>
    using DeMorganOrtho \<open>orthogonal_complement (orthogonal_complement A \<inter> orthogonal_complement B \<inter> orthogonal_complement C) = orthogonal_complement (orthogonal_complement (orthogonal_complement (orthogonal_complement A \<inter> orthogonal_complement B)) \<inter> orthogonal_complement C)\<close> assms(1) assms(2) assms(3) 
      complex_vector.subspace_def
    by (simp add: DeMorganOrtho subspace_closed_plus)
  finally show ?thesis
    using DeMorganOrthoDual assms(1) assms(2) assms(3) 
    by (simp add: orthogonal_complement_twice subspace_closed_plus)
qed


lemma is_closed_subspace_zero:
  fixes A :: \<open>('a::chilbert_space) set\<close>
  assumes \<open>closed_subspace A\<close>
  shows \<open>(({0}::'a set) +\<^sub>M A) = A\<close>
  using  DeMorganOrthoDual  assms  
    ortho_top orthogonal_complement_twice orthogonal_complement_def
  by (metis (no_types, lifting) Complex_Vector_Spaces.subspace_UNIV Int_UNIV_left subspace_orthog)

lemma is_closed_subspace_ord:
  fixes A B C:: \<open>('a::chilbert_space) set\<close>
  assumes \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close> and \<open>closed_subspace C\<close>
    and \<open>A \<subseteq> B\<close>
  shows \<open>C +\<^sub>M A \<subseteq> C +\<^sub>M B\<close>
  by (metis DeMorganOrtho Int_mono assms(1) assms(2) assms(3) assms(4) order_refl ortho_leq subspace_closed_plus)


lemma is_closed_subspace_universal_inclusion_left:
  fixes A B:: \<open>('a::chilbert_space) set\<close>
  assumes \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close>
  shows \<open>A \<subseteq> A +\<^sub>M B\<close>
  using DeMorganOrtho Int_lower1 assms(1) assms(2)  ortho_leq
  by (metis subspace_closed_plus)


lemma is_closed_subspace_universal_inclusion_right:
  fixes A B:: \<open>('a::chilbert_space) set\<close>
  assumes \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close>
  shows \<open>B \<subseteq> (A +\<^sub>M B)\<close>
  by (metis assms(1) assms(2)  is_closed_subspace_comm is_closed_subspace_universal_inclusion_left)

lemma is_closed_subspace_universal_inclusion_inverse:
  fixes A B C:: \<open>('a::chilbert_space) set\<close>
  assumes \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close> and \<open>closed_subspace C\<close>
    and \<open>A \<subseteq> C\<close> and \<open>B \<subseteq> C\<close>
  shows \<open>(A +\<^sub>M B) \<subseteq> C\<close>
  using DeMorganOrtho assms(1) assms(2) assms(3) assms(4) assms(5) inf_greatest  ortho_leq
  by (metis subspace_closed_plus)


lemma projection_ker_simp:
  fixes x :: \<open>'a::chilbert_space\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>f (projection (f -` {0}) x) = 0\<close>
proof-
  from \<open>bounded_clinear f\<close>
  have \<open>closed_subspace (f -` {0})\<close>
    by (simp add: ker_op_lin)
  hence \<open>projection (f -` {0}) x \<in> f -` {0}\<close>
    using projection_intro2
    by blast
  thus ?thesis
    by simp
qed

lemma inner_product_projection:
  fixes x t :: \<open>'a::chilbert_space\<close>
  assumes \<open>closed_subspace M\<close> and \<open>t \<noteq> 0\<close> and \<open>t \<in> M\<close>
    and \<open>\<forall> m \<in> M. \<exists> k. m = k *\<^sub>C t\<close>
  shows \<open>projection M x = (\<langle>t , x\<rangle> / \<langle>t , t\<rangle>) *\<^sub>C t\<close>
proof-
  have \<open>(\<langle>t , t\<rangle>) \<noteq> 0\<close>
    using \<open>t \<noteq> 0\<close>
    by simp
  obtain k where \<open>(projection M) x = k *\<^sub>C t\<close>
    using assms(1) assms(4) projection_intro2 by blast    
  have \<open>((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t =
 ((\<langle>t , ((projection M) x + (projection (orthogonal_complement M)) x)\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
    using assms(1) ortho_decomp by fastforce
  also have \<open>... = ((\<langle>t , ((projection M) x)\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
  proof-
    have \<open> (projection (orthogonal_complement M)) x \<in> orthogonal_complement M\<close>
      by (simp add: assms(1) projection_intro2)
    hence \<open>\<langle>t , (projection (orthogonal_complement M)) x\<rangle> = 0\<close>
      using \<open>t \<in> M\<close>
      unfolding orthogonal_complement_def
      unfolding is_orthogonal_def
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm)
    thus ?thesis
      by (simp add: cinner_right_distrib) 
  qed
  also have \<open>... = ((\<langle>t , (k *\<^sub>C t)\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
    using \<open>(projection M) x = k *\<^sub>C t\<close> 
    by simp
  also have \<open>... = ((k*(\<langle>t , t\<rangle>))/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
    by simp   
  also have \<open>... = k *\<^sub>C t\<close>
    using  \<open>(\<langle>t , t\<rangle>) \<noteq> 0\<close> by simp
  finally show ?thesis using \<open>(projection M) x = k *\<^sub>C t\<close> 
    by auto
qed


subsection \<open>Riesz Representation\<close>

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
  assumes \<open>bounded_clinear f\<close> and \<open>x \<noteq> 0\<close> and \<open>x \<in> (orthogonal_complement (f -` {0}))\<close> 
  shows \<open>f x \<noteq> 0\<close>
proof(rule classical)
  have \<open>closed_subspace (f -` {0})\<close> using \<open>bounded_clinear f\<close>
    by (simp add: ker_op_lin) 
  assume \<open>\<not>(f x \<noteq> 0)\<close>
  hence \<open>x \<in> f -` {0}\<close>
    by simp  
  moreover have \<open>(f -` {0})\<inter>(orthogonal_complement (f -` {0})) = {0}\<close>
    using \<open>closed_subspace (f -` {0})\<close>  ortho_inter_zero
    by (metis assms(3) projectionPropertiesD projection_intro2 vimage_singleton_eq)    
  ultimately have  \<open>x \<notin> orthogonal_complement (f -` {0})\<close> using \<open>x \<noteq> 0\<close>
    by (smt Int_iff empty_iff insert_iff) 
  thus ?thesis using \<open>x \<in> orthogonal_complement (f -` {0})\<close> by blast
qed

lemma ker_unidim:
  fixes f :: \<open>('a::chilbert_space) functional\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>proportion (orthogonal_complement (f -` {0}))\<close>
proof-
  have \<open>x \<in> (orthogonal_complement (f -` {0})) \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<in> orthogonal_complement (f -` {0})
 \<Longrightarrow> y \<noteq> 0  \<Longrightarrow> \<exists> k. x = k *\<^sub>C y\<close>
    for x y
  proof-
    assume \<open>x \<in> (orthogonal_complement (f -` {0}))\<close> and \<open>x \<noteq> 0\<close> and \<open>y \<in>(orthogonal_complement (f -` {0}))\<close> and \<open>y \<noteq> 0\<close>
    from \<open>bounded_clinear f\<close> 
    have \<open>closed_subspace (f -` {0})\<close>
      by (simp add: ker_op_lin)
    hence \<open>closed_subspace (orthogonal_complement (f -` {0}))\<close>
      by simp
    hence \<open>f x \<noteq> 0\<close>
      using \<open>closed_subspace (f -` {0})\<close> \<open>x \<in> orthogonal_complement (f -` {0})\<close> \<open>x \<noteq> 0\<close> projectionPropertiesD projection_fixed_points by force
    have \<open>f y \<noteq> 0\<close>
      by (metis \<open>y \<in> orthogonal_complement (f -` {0})\<close> \<open>y \<noteq> 0\<close> cinner_eq_zero_iff orthogonal_complement_D2 vimage_singleton_eq)
    from  \<open>f x \<noteq> 0\<close>  \<open>f y \<noteq> 0\<close>
    have \<open>\<exists> k. (f x) = k*(f y)\<close>
      by (metis add.inverse_inverse minus_divide_eq_eq)
    then obtain k where \<open>(f x) = k*(f y)\<close>
      by blast
    hence  \<open>(f x) = (f (k *\<^sub>C y))\<close>
      using  \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def
      by (simp add: complex_vector.linear_scale)
    hence  \<open>(f x) - (f (k *\<^sub>C y)) = 0\<close>
      by simp
    hence  \<open>f (x - (k *\<^sub>C y)) = 0\<close>
      using additive.diff  \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def
      by (simp add: complex_vector.linear_diff)        
    hence  \<open>(x - (k *\<^sub>C y)) \<in> f -` {0}\<close>
      by simp
    moreover have \<open>(f -` {0}) \<inter> (orthogonal_complement (f -` {0})) = {0}\<close>
      by (metis \<open>closed_subspace (f -` {0})\<close> \<open>x \<in> orthogonal_complement (f -` {0})\<close> ortho_inter_zero projectionPropertiesD projection_intro2 vimage_singleton_eq)
    moreover have \<open>(x - (k *\<^sub>C y)) \<in> orthogonal_complement (f -` {0})\<close>
    proof-
      from  \<open>y \<in> (orthogonal_complement (f -` {0}))\<close>
      have  \<open>k *\<^sub>C y \<in> (orthogonal_complement (f -` {0}))\<close>
        using \<open>closed_subspace (orthogonal_complement (f -` {0}))\<close>
        unfolding closed_subspace_def
        by (simp add: complex_vector.subspace_scale)        
      thus ?thesis using  \<open>x \<in> (orthogonal_complement (f -` {0}))\<close>  \<open>closed_subspace (orthogonal_complement (f -` {0}))\<close>
        unfolding closed_subspace_def
        using \<open>closed_subspace (f -` {0})\<close> add_diff_cancel_left' calculation(1) 
          diff_add_cancel diff_zero  projection_uniq
        by (simp add: complex_vector.subspace_diff)
    qed
    ultimately have \<open>x - (k *\<^sub>C y) = 0\<close>
      using \<open>f (x - k *\<^sub>C y) = 0\<close> \<open>x - k *\<^sub>C y \<in> orthogonal_complement (f -` {0})\<close> 
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
  thus ?thesis
    by (metis cinner_zero_left) 
next
  case False
  thus ?thesis 
  proof-
    from \<open>bounded_clinear f\<close>
    have \<open>proportion (orthogonal_complement (f -` {0}))\<close>
      by (simp add: ker_unidim)
    moreover have \<open>\<exists> h \<in> (orthogonal_complement (f -` {0})). h \<noteq> 0\<close>
    proof -
      have "(\<exists>a\<in>orthogonal_complement (f -` {0}). a \<noteq> 0) \<or> orthogonal_complement (f -` {0}) \<noteq> {} \<and> f -` {0} \<noteq> UNIV"
        by (metis (no_types) False UNIV_I assms insert_absorb ker_op_lin ortho_bot orthogonal_complement_twice projection_intro1 vimage_singleton_eq)
      thus ?thesis
        by (metis (no_types) assms insertI1 is_singletonE is_singletonI' ker_op_lin ortho_bot orthogonal_complement_twice)
    qed
    ultimately have \<open>\<exists> t. t \<noteq> 0 \<and> (\<forall> x \<in>(orthogonal_complement (f -` {0})). \<exists> k. x = k *\<^sub>C t)\<close>
      by (metis complex_vector.scale_zero_right equals0D proportion_existence) 
    then obtain t where \<open>t \<noteq> 0\<close> and \<open>\<forall> x \<in>(orthogonal_complement (f -` {0})). \<exists> k. x = k *\<^sub>C t\<close>
      by blast
    have  \<open>closed_subspace ( orthogonal_complement (f -` {0}))\<close>
      by (simp add: assms ker_op_lin)
    hence  \<open>t \<in> (orthogonal_complement (f -` {0}))\<close>
    proof-
      have \<open>\<exists> s \<in> (orthogonal_complement (f -` {0})). s \<noteq> 0\<close>
        by (simp add: \<open>\<exists>h\<in>orthogonal_complement (f -` {0}). h \<noteq> 0\<close>)
      then obtain s where \<open>s \<in> (orthogonal_complement (f -` {0}))\<close> and \<open>s \<noteq> 0\<close>
        by blast
      have \<open>\<exists> k. s = k *\<^sub>C t\<close>
        by (simp add: \<open>\<forall>x\<in>orthogonal_complement (f -` {0}). \<exists>k. x = k *\<^sub>C t\<close> \<open>s \<in> orthogonal_complement (f -` {0})\<close>)
      then obtain k where \<open>s = k *\<^sub>C t\<close>
        by blast
      have  \<open>k \<noteq> 0\<close>
        using \<open>s \<noteq> 0\<close>
        by (simp add: \<open>s = k *\<^sub>C t\<close>) 
      hence  \<open>(1/k) *\<^sub>C s = t\<close>
        using  \<open>s = k *\<^sub>C t\<close> by simp
      moreover have \<open>(1/k) *\<^sub>C s \<in>  (orthogonal_complement (f -` {0}))\<close>
        unfolding closed_subspace_def
        by (simp add: \<open>s \<in> orthogonal_complement (f -` {0})\<close> orthogonal_complement_D2 orthogonal_complement_I1)
      ultimately show ?thesis
        by simp 
    qed
    have \<open>projection (orthogonal_complement (f -` {0})) x = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
      for x
      using inner_product_projection \<open>closed_subspace  (orthogonal_complement (f -` {0}))\<close>
        \<open>\<forall> m \<in>  (orthogonal_complement (f -` {0})). \<exists> k. m = k *\<^sub>C t\<close>  \<open>t \<in> (orthogonal_complement (f -` {0}))\<close>
      by (simp add: inner_product_projection \<open>t \<noteq> 0\<close>)
    hence \<open>f (projection (orthogonal_complement (f -` {0})) x) = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) * (f t)\<close>
      for x
      using \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def
      by (simp add: complex_vector.linear_scale)
    hence \<open>f (projection (orthogonal_complement (f -` {0})) x) = \<langle>(((cnj (f t))/(\<langle>t , t\<rangle>)) *\<^sub>C t) , x\<rangle>\<close>
      for x
    proof-
      from \<open>f (projection (orthogonal_complement (f -` {0})) x) = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) * (f t)\<close>
      have \<open>f (projection (orthogonal_complement (f -` {0})) x) = ((f t)/(\<langle>t , t\<rangle>)) * (\<langle>t , x\<rangle>)\<close>
        by simp
      thus ?thesis
        by auto 
    qed
    moreover have \<open>f (projection (f -` {0}) x) = 0\<close>
      for x
      using  assms ker_op_lin projection_intro2 by blast
    ultimately have \<open>f x = \<langle>(((cnj (f t))/(\<langle>t , t\<rangle>)) *\<^sub>C t) , x\<rangle>\<close>
      for x
    proof -
      assume "\<And>x. f (projection (f -` {0}) x) = 0"
      hence "\<And>a b. f (projection (f -` {0}) a + b) = 0 + f b"
        by (metis (no_types) additive.add assms bounded_clinear_def clinear_additive_D)
      hence "\<And>a. 0 + f (projection (orthogonal_complement (f -` {0})) a) = f a"
        by (metis (no_types) assms ker_op_lin ortho_decomp)
      thus ?thesis
        by (simp add: \<open>\<And>x. f (projection (orthogonal_complement (f -` {0})) x) = \<langle>(cnj (f t) / \<langle>t, t\<rangle>) *\<^sub>C t, x\<rangle>\<close>)
    qed
    thus ?thesis
      by blast  
  qed
qed

subsection \<open>Adjointness\<close>

definition \<open>Adj G = (SOME F. \<forall>x. \<forall>y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>)\<close>
  for G :: "'b::complex_inner \<Rightarrow> 'a::complex_inner"

lemma Adj_I:
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes \<open>bounded_clinear G\<close>
  shows \<open>\<forall>x. \<forall>y. \<langle>Adj G x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
proof (unfold Adj_def, rule someI_ex[where P="\<lambda>F. \<forall>x. \<forall>y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>"])
  include notation_norm
  from assms have \<open>clinear G\<close>
    unfolding bounded_clinear_def by blast
  have  \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
    using  \<open>bounded_clinear G\<close>
    unfolding bounded_clinear_def
    by simp
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
        using  \<open>clinear G\<close> additive.add cinner_right_distrib clinear_def
        by (simp add: cinner_right_distrib complex_vector.linear_add)
      moreover have  \<open>(g x) (k *\<^sub>C a) = k *\<^sub>C ((g x) a)\<close>
        for a k
        unfolding g_def
        using  \<open>clinear G\<close>
        by (simp add: complex_vector.linear_scale)
      ultimately show ?thesis
        by (simp add: clinearI) 
    qed
    moreover have \<open>\<exists> M. \<forall> y. \<parallel> (g x) y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
      using \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close> g_def
      by (simp add: \<open>bounded_clinear G\<close> bounded_clinear.bounded bounded_clinear_cinner_right_comp)
    ultimately show ?thesis unfolding bounded_linear_def
      using bounded_clinear.intro
      by blast 
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

lemma Adj_I':
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes \<open>bounded_clinear G\<close>
  shows \<open>\<forall>x. \<forall>y. \<langle>x, Adj G y\<rangle> = \<langle>G x, y\<rangle>\<close>
  by (metis Adj_I assms cinner_commute')

notation Adj ("_\<^sup>\<dagger>" [99] 100)

lemma Adj_D:
  fixes G:: \<open>'b::chilbert_space \<Rightarrow> 'a::complex_inner\<close>
    and F:: \<open>'a \<Rightarrow> 'b\<close>
  assumes "bounded_clinear G" and
    F_is_adjoint: \<open>\<And>x y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
  shows \<open>F = G\<^sup>\<dagger>\<close>
proof-
  note F_is_adjoint
  moreover have \<open>\<forall> x::'a. \<forall> y::'b. \<langle>(G\<^sup>\<dagger>) x , y\<rangle> = \<langle>x , G y\<rangle>\<close>
    using  \<open>bounded_clinear G\<close> Adj_I by blast
  ultimately have  \<open>\<forall> x::'a. \<forall> y::'b. 
    \<langle>F x , y\<rangle> - \<langle>(G\<^sup>\<dagger>) x , y\<rangle> = 0\<close>
    by (simp add: \<open>\<forall>x y. \<langle> (G\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , G y \<rangle>\<close> F_is_adjoint)
  hence  \<open>\<forall> x::'a. \<forall> y::'b. 
    (\<langle>((F x) - ((G\<^sup>\<dagger>) x)) , y\<rangle> ) = 0\<close>
    by (simp add: cinner_diff_left)
  hence \<open>\<forall> x::'a. F x - (G\<^sup>\<dagger>) x = 0\<close>
    by (metis cinner_gt_zero_iff cinner_zero_left)
  hence \<open>\<forall> x::'a. (F - (G\<^sup>\<dagger>)) x = 0\<close>
    by simp
  hence \<open>\<forall> x::'a. F x = (G\<^sup>\<dagger>) x\<close>
    by (simp add: \<open>\<forall>x. F x - (G\<^sup>\<dagger>) x = 0\<close> eq_iff_diff_eq_0)
  thus ?thesis by auto
qed


lemma Adj_bounded_clinear:
  fixes A :: "'a::chilbert_space \<Rightarrow> 'b::complex_inner"
  shows \<open>bounded_clinear A \<Longrightarrow> bounded_clinear (A\<^sup>\<dagger>)\<close>
proof-
  include notation_norm 
  assume \<open>bounded_clinear A\<close>
  have \<open>\<langle>(A\<^sup>\<dagger>) x, y\<rangle> = \<langle>x , (A y)\<rangle>\<close>
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
    unfolding bounded_clinear_def  Modules.additive_def
    using clinearI by blast    
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
      moreover have \<open>\<langle> r, U s \<rangle> = cnj \<langle> U s, r\<rangle>\<close>
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

lemma id_dagger: \<open>(id::'a::chilbert_space\<Rightarrow>'a)\<^sup>\<dagger> = id\<close>
proof-
  have \<open>\<langle> id x, y \<rangle> = \<langle> x, id y \<rangle>\<close>
    for x y::'a
    unfolding id_def by blast
  thus ?thesis
    using id_bounded_clinear
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
  proof - (* sledgehammer *)
    assume a1: "\<And>x y. \<langle>cnj a *\<^sub>C (A\<^sup>\<dagger>) x, y\<rangle> = \<langle>x, a *\<^sub>C A y\<rangle>"
    { fix bb :: 'b
      have "\<And>b aa. \<langle>cnj a *\<^sub>C (A\<^sup>\<dagger>) b, aa\<rangle> = \<langle>b, A (a *\<^sub>C aa)\<rangle>"
        using a1 by (metis (lifting) assms(2))
      hence "\<And>aa b. \<langle>aa, cnj a *\<^sub>C (A\<^sup>\<dagger>) b\<rangle> = cnj \<langle>b, A (a *\<^sub>C aa)\<rangle>"
        by (metis (lifting) cinner_commute')
      hence "\<And>b aa. a *\<^sub>C \<langle>(A\<^sup>\<dagger>) b, aa\<rangle> = \<langle>b, A (a *\<^sub>C aa)\<rangle>"
        by (metis (no_types) cinner_commute' cinner_scaleC_left cinner_scaleC_right complex_scaleC_def)
      hence "(\<lambda>b. cnj a *\<^sub>C (A\<^sup>\<dagger>) b) = (\<lambda>aa. a *\<^sub>C A aa)\<^sup>\<dagger>"
        by (simp add: Adj_D \<open>bounded_linear (\<lambda>t. a *\<^sub>C A t)\<close> assms(2) bounded_linear_bounded_clinear)
      hence "cnj a *\<^sub>C (A\<^sup>\<dagger>) bb = ((\<lambda>aa. a *\<^sub>C A aa)\<^sup>\<dagger>) bb"
        by metis }
    thus ?thesis
      by presburger
  qed  
qed

lemma projection_D1':
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_projection_on \<pi> M\<close> and \<open>closed_subspace M\<close>
  shows \<open>\<pi> = \<pi>\<^sup>\<dagger>\<close>
proof-
  have \<open>\<pi> x = (\<pi>\<^sup>\<dagger>) x\<close>
    for x
  proof-
    have "\<pi> x - (\<pi>\<^sup>\<dagger>) x \<in> orthogonal_complement M"
    proof-
      have "\<langle>x - (\<pi>\<^sup>\<dagger>) x, y\<rangle> = 0"
        if "y \<in> M"
        for y :: 'a
      proof-
        have \<open>y = \<pi> y\<close>
          using that(1) assms(1) assms(2) projection_fixed_points' 
          by fastforce 
        hence \<open>y - \<pi> y = 0\<close>
          by simp
        have \<open>\<langle>x - ((\<pi>)\<^sup>\<dagger>) x, y\<rangle> = \<langle>x, y\<rangle> - \<langle>((\<pi>)\<^sup>\<dagger>) x, y\<rangle>\<close>
          by (simp add: cinner_diff_left)
        also have \<open>... = \<langle>x, y\<rangle> - \<langle>x, \<pi> y\<rangle>\<close>
          using Adj_I assms(1) assms(2) projectionPropertiesA' 
          by auto          
        also have \<open>... = \<langle>x, y - \<pi> y\<rangle>\<close>
          by (simp add: cinner_diff_right)
        also have \<open>... = \<langle>x, 0\<rangle>\<close>
          using  \<open>y - \<pi> y = 0\<close>
          by simp
        also have \<open>... = 0\<close>
          by simp          
        finally show ?thesis
          by simp 
      qed
      thus ?thesis
      proof - (* sledgehammer *)
        obtain aa :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a" where
          "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> \<langle>x0, v2\<rangle> \<noteq> 0) = (aa x0 x1 \<in> x1 \<and> \<langle>x0, aa x0 x1\<rangle> \<noteq> 0)"
          by moura
        hence f1: "\<forall>A a. aa a A \<in> A \<and> \<langle>a, aa a A\<rangle> \<noteq> 0 \<or> a \<in> orthogonal_complement A"
          by (meson orthogonal_complement_I2)
        have f2: "\<forall>a. a - \<pi> a \<in> orthogonal_complement M \<and> \<pi> a \<in> M"
          by (metis \<open>is_projection_on \<pi> M\<close> is_projection_on_def)
        hence f3: "\<pi> (\<pi> x) = \<pi> x"
          by (metis \<open>closed_subspace M\<close> \<open>is_projection_on \<pi> M\<close> projection_fixed_points')
        { assume "\<langle>\<pi> x - (\<pi>\<^sup>\<dagger>) x, aa (\<pi> x - (\<pi>\<^sup>\<dagger>) x) M\<rangle> \<noteq> 0"
          { assume "\<langle>\<pi> x - (\<pi>\<^sup>\<dagger>) x, aa (\<pi> x - (\<pi>\<^sup>\<dagger>) x) M\<rangle> \<noteq> \<langle>x - (\<pi>\<^sup>\<dagger>) x, aa (\<pi> x - (\<pi>\<^sup>\<dagger>) x) M\<rangle>"
            hence "(+) \<langle>\<pi> x - \<pi> (\<pi> x), aa (\<pi> x - (\<pi>\<^sup>\<dagger>) x) M\<rangle> \<noteq> (+) \<langle>x - \<pi> x, aa (\<pi> x - (\<pi>\<^sup>\<dagger>) x) M\<rangle>"
              using f3 by (metis (no_types) cinner_diff_left diff_add_cancel)
            hence "aa (\<pi> x - (\<pi>\<^sup>\<dagger>) x) M \<notin> M \<or> \<langle>\<pi> x - (\<pi>\<^sup>\<dagger>) x, aa (\<pi> x - (\<pi>\<^sup>\<dagger>) x) M\<rangle> = 0"
              using f2 by (metis \<open>closed_subspace M\<close> orthogonal_complement_D2 orthogonal_complement_twice) }
          hence ?thesis
            using f1 by (metis (no_types) \<open>\<And>y. y \<in> M \<Longrightarrow> \<langle>x - (\<pi>\<^sup>\<dagger>) x, y\<rangle> = 0\<close>) }
        thus ?thesis
          using f1 by metis
      qed        
    qed
    moreover have "(\<pi>\<^sup>\<dagger>) x \<in> M"
    proof-
      have "y \<in> orthogonal_complement M \<Longrightarrow> \<langle> (\<pi>\<^sup>\<dagger>) x, y \<rangle> = 0"
        for y
      proof-
        assume \<open>y \<in> orthogonal_complement M\<close>
        hence \<open>\<pi> y = 0\<close>
          by (metis assms(1) assms(2) cinner_zero_left diff_zero orthogonal_complement_I2 orthogonal_complement_twice projection_uniq')           
        hence \<open>\<langle> x, \<pi> y \<rangle> = 0\<close>
          by simp
        thus ?thesis
          using Adj_I assms projectionPropertiesA'
          by fastforce 
      qed
      hence "(\<pi>\<^sup>\<dagger>) x \<in> orthogonal_complement (orthogonal_complement M)"
        unfolding orthogonal_complement_def is_orthogonal_def
        by simp        
      thus ?thesis
        by (simp add: assms orthogonal_complement_twice) 
    qed
    ultimately show ?thesis
      by (metis assms(1) assms(2) is_projection_on_def projection_fixed_points projection_uniq) 
  qed
  thus ?thesis by blast
qed


lemma projection_D1:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>closed_subspace M\<close>
  shows \<open>projection M = (projection M)\<^sup>\<dagger>\<close>
  using projection_D1' assms is_projection_on_def projection_intro1 projection_intro2 
  by fastforce


lemma closed_subspace_closure:
  fixes f::\<open>('a::complex_inner) \<Rightarrow> ('b::complex_inner)\<close>
    and S::\<open>'a set\<close>
  assumes "clinear f" and "complex_vector.subspace S"
  shows  \<open>closed_subspace (closure {f x |x. x \<in> S})\<close>
proof -
  have "complex_vector.subspace {f x |x. x \<in> S}"
    using assms Setcompr_eq_image
    by (simp add: Setcompr_eq_image complex_vector.linear_subspace_image)
  thus \<open>closed_subspace (closure {f x |x. x \<in> S})\<close>
    apply (rule_tac closed_subspace.intro)
     apply (simp add: subspace_cl)
    by simp
qed


instantiation linear_space :: (complex_inner) "uminus"
begin
lift_definition uminus_linear_space::\<open>'a linear_space  \<Rightarrow> 'a linear_space\<close>
  is \<open>orthogonal_complement\<close>
  by simp

instance ..
end



instantiation linear_space :: (complex_inner) "Sup"
begin
lift_definition Sup_linear_space::\<open>'a linear_space set \<Rightarrow> 'a linear_space\<close>
  is \<open>\<lambda> S. closure (complex_vector.span (Union S))\<close>
proof
  show "complex_vector.subspace (closure (complex_vector.span (\<Union> S::'a set)))"
    if "\<And>x. (x::'a set) \<in> S \<Longrightarrow> closed_subspace x"
    for S :: "'a set set"
    using that
    by (simp add: closed_subspace.subspace subspace_I) 
  show "closed (closure (complex_vector.span (\<Union> S::'a set)))"
    if "\<And>x. (x::'a set) \<in> S \<Longrightarrow> closed_subspace x"
    for S :: "'a set set"
    using that
    by simp 
qed

instance..
end


instantiation linear_space :: ("{complex_vector,topological_space}") inf begin 
lift_definition inf_linear_space :: "'a linear_space \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is "(\<inter>)" by simp
instance .. end

instantiation linear_space :: (complex_normed_vector) sup begin
lift_definition sup_linear_space :: "'a linear_space \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" 
  is "\<lambda>A B::'a set. A +\<^sub>M B"
  by (simp add: subspace_closed_plus) 
instance .. 
end

instantiation linear_space :: (complex_inner) minus begin
lift_definition minus_linear_space :: "'a linear_space \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space"
  is "\<lambda> A B. ( A \<inter> (orthogonal_complement B) )"
  by simp
instance..
end


instantiation linear_space :: ("{complex_vector,topological_space}") order_top begin
instance apply intro_classes
  apply transfer by simp
end

instantiation linear_space :: (chilbert_space) order_bot begin
instance apply intro_classes
  apply transfer 
  using ortho_bot ortho_leq Complex_Vector_Spaces.subspace_0 
  by blast 
end

instantiation linear_space :: ("{complex_vector,topological_space}") semilattice_inf begin
instance apply intro_classes
    apply transfer apply simp
   apply transfer apply simp
  apply transfer by simp
end


(* 
Dominique: Try if "linear_space :: (complex_inner) lattice"
and "linear_space :: (complex_inner) complete_lattice" (below)
work with something weaker than complex_inner
(it does not work for "linear_space :: (complex_inner) orthocomplemented_lattice"). 

Jose: I substituted al the "chilbert_spaces" by "complex_inner", I corrected
lemma by lemma and even in that case, it does not work the elimination of the hypothesis
of completeness.

*)

instantiation linear_space :: (chilbert_space) lattice begin
instance 
proof
  show \<open>(x::'a linear_space) \<le> (sup x y)\<close>
    for x :: "'a linear_space"
      and y :: "'a linear_space"
  proof-
    have \<open>t \<in> space_as_set x \<Longrightarrow>
          t \<in> space_as_set
                 (Abs_linear_space
                   (closure
                     {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set x \<and> \<phi> \<in> space_as_set y}))\<close>
      for t
    proof-
      assume \<open>t \<in> space_as_set x\<close>
      moreover have \<open>0 \<in> space_as_set y\<close>
      proof-
        have \<open>closed_subspace (space_as_set y)\<close>
          using space_as_set by blast
        thus ?thesis
          using insert_subset is_closed_subspace_universal_inclusion_left is_closed_subspace_zero
          by (metis Complex_Vector_Spaces.subspace_0) 
      qed
      moreover have \<open>t = t + 0\<close>
        by simp
      ultimately have \<open>t \<in>  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set x \<and> \<phi> \<in> space_as_set y}\<close>
        by force
      hence \<open>t \<in> closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set x \<and> \<phi> \<in> space_as_set y}\<close>
        by (meson closure_subset subset_eq)        
      thus ?thesis using Abs_linear_space_inverse
      proof -
        have "t \<in> closure (space_as_set x + space_as_set y)"
          using \<open>t \<in> closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set x \<and> \<phi> \<in> space_as_set y}\<close>
          by (metis (no_types, lifting) \<open>0 \<in> space_as_set y\<close> \<open>t = t + 0\<close> \<open>t \<in> space_as_set x\<close> closure_subset in_mono set_plus_intro)
        hence "t \<in> space_as_set (Abs_linear_space (closure (space_as_set x + space_as_set y)))"
          by (metis (no_types) Abs_linear_space_inverse closed_sum_def mem_Collect_eq space_as_set subspace_closed_plus)
        thus ?thesis
          unfolding set_plus_def
          by (smt Collect_cong)
      qed
    qed
    thus ?thesis
      unfolding  less_eq_linear_space_def 
        closed_sum_def 
      apply auto
      using is_closed_subspace_universal_inclusion_left space_as_set sup_linear_space.rep_eq
      by fastforce
  qed

  show "(y::'a linear_space) \<le> (sup x y)"
    for y :: "'a linear_space"
      and x :: "'a linear_space"
  proof-
    have \<open>y \<le> (sup y x)\<close>
      by (simp add: \<open>\<And>y x. x \<le> sup x y\<close>)
    moreover have \<open>sup y x = sup x y\<close>
      apply transfer
      by (simp add: is_closed_subspace_comm)
    ultimately show ?thesis
      by simp     
  qed
  show "(sup (y::'a linear_space) z) \<le> x"
    if "(y::'a linear_space) \<le> x"
      and "(z::'a linear_space) \<le> x"
    for y :: "'a linear_space"
      and x :: "'a linear_space"
      and z :: "'a linear_space"
    using that
  proof-
    have \<open>space_as_set y \<subseteq> space_as_set x \<Longrightarrow>
          space_as_set z \<subseteq> space_as_set x \<Longrightarrow>
          (closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set y \<and> \<phi> \<in> space_as_set z})
          \<subseteq> space_as_set x\<close>
    proof-
      assume \<open>space_as_set y \<subseteq> space_as_set x\<close>
        and \<open>space_as_set z \<subseteq> space_as_set x\<close>
      have \<open>closed (space_as_set x)\<close>
      proof-
        have \<open>closed_subspace (space_as_set x)\<close>
          using space_as_set by simp
        thus ?thesis
          by (simp add: closed_subspace.closed) 
      qed
      moreover have \<open>({\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set y \<and> \<phi> \<in> space_as_set z})
          \<subseteq> space_as_set x\<close>
      proof
        show "t \<in> space_as_set x"
          if "t \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set y \<and> \<phi> \<in> space_as_set z}"
          for t :: 'a
        proof-
          have \<open>\<exists> \<psi> \<phi>. \<psi> \<in> space_as_set y \<and> \<phi> \<in> space_as_set z \<and> t = \<psi> + \<phi>\<close>
            using that by blast
          then obtain  \<psi> \<phi> where \<open>\<psi> \<in> space_as_set y\<close> and \<open>\<phi> \<in> space_as_set z\<close> 
            and \<open>t = \<psi> + \<phi>\<close>
            by blast
          have \<open>\<psi> \<in> space_as_set x\<close>
            using \<open>space_as_set y \<subseteq> space_as_set x\<close> \<open>\<psi> \<in> space_as_set y\<close> by auto
          moreover have \<open>\<phi> \<in> space_as_set x\<close>
            using \<open>space_as_set z \<subseteq> space_as_set x\<close> \<open>\<phi> \<in> space_as_set z\<close> by auto
          moreover have \<open>closed_subspace (space_as_set x)\<close>
            using space_as_set by simp
          ultimately show ?thesis
            using \<open>t = \<psi> + \<phi>\<close>  complex_vector.subspace_def
            using closed_subspace.subspace by blast
        qed
      qed
      ultimately show ?thesis
        by (simp add: closure_minimal)  
    qed
    hence \<open>space_as_set y \<subseteq> space_as_set x \<Longrightarrow>
          space_as_set z \<subseteq> space_as_set x \<Longrightarrow>
           space_as_set
                 (Abs_linear_space
                   (closure
                     {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set y \<and> \<phi> \<in> space_as_set z})) 
          \<subseteq> space_as_set x\<close>
    proof -
      assume a1: "space_as_set y \<subseteq> space_as_set x"
      assume a2: "space_as_set z \<subseteq> space_as_set x"
      have f3: "\<And>l la. closure {a. \<exists>aa ab. (a::'a) = aa + ab \<and> aa \<in> space_as_set l \<and> ab \<in> space_as_set la} = space_as_set (sup l la)"
        using closed_sum_def sup_linear_space.rep_eq Collect_cong
        unfolding set_plus_def
        by smt
          (* > 1 s *)
      hence "space_as_set (sup y z) \<subseteq> space_as_set x"
        using a2 a1 \<open>\<lbrakk>space_as_set y \<subseteq> space_as_set x; space_as_set z \<subseteq> space_as_set x\<rbrakk> \<Longrightarrow> closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set y \<and> \<phi> \<in> space_as_set z} \<subseteq> space_as_set x\<close> by blast
      thus ?thesis
        using f3 by (simp add: space_as_set_inverse)
    qed
    thus ?thesis
    proof -
      have "space_as_set y \<subseteq> space_as_set x \<and> space_as_set z \<subseteq> space_as_set x"
        by (metis less_eq_linear_space.rep_eq that(1) that(2))
      thus ?thesis
        unfolding less_eq_linear_space_def 
          closed_sum_def set_plus_def
        using set_plus_def \<open>\<lbrakk>space_as_set y \<subseteq> space_as_set x; space_as_set z \<subseteq> space_as_set x\<rbrakk> \<Longrightarrow> space_as_set (Abs_linear_space (closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set y \<and> \<phi> \<in> space_as_set z})) \<subseteq> space_as_set x\<close> closed_sum_def sup_linear_space_def
        by (smt Collect_cong id_apply map_fun_apply)
          (* > 1 s *)
    qed  
  qed
qed
end



lemma span_superset:
  \<open>A \<subseteq> space_as_set (Span A)\<close> for A :: \<open>('a::chilbert_space) set\<close>
proof-
  have \<open>\<forall> S. S \<in> {S. A \<subseteq> space_as_set S} \<longrightarrow> A \<subseteq> space_as_set S\<close>
    by simp
  hence \<open>A \<subseteq> \<Inter> {space_as_set S| S. A \<subseteq> space_as_set S}\<close>
    by blast
  hence \<open>A \<subseteq> space_as_set( Inf {S| S. A \<subseteq> space_as_set S})\<close>
    by (metis (no_types, lifting)  INF_greatest Inf_linear_space.rep_eq \<open>\<forall>S. S \<in> {S. A \<subseteq> space_as_set S} \<longrightarrow> A \<subseteq> space_as_set S\<close>)
  thus ?thesis using span_def' by metis
qed

lemma bot_plus[simp]: "sup bot x = x" for x :: "'a::chilbert_space linear_space"
  apply transfer
  unfolding sup_linear_space_def[symmetric] 
  using is_closed_subspace_zero
  unfolding closed_sum_def
  unfolding set_plus_def
  by smt

instantiation linear_space :: (chilbert_space) complete_lattice begin
instance 
proof
  show "Inf A \<le> (x::'a linear_space)"
    if "(x::'a linear_space) \<in> A"
    for x :: "'a linear_space"
      and A :: "'a linear_space set"
    using that 
    apply transfer
    by auto

  show "(z::'a linear_space) \<le> Inf A"
    if "\<And>x. (x::'a linear_space) \<in> A \<Longrightarrow> z \<le> x"
    for A :: "'a linear_space set"
      and z :: "'a linear_space"
    using that 
    apply transfer
    by auto

  show "(x::'a linear_space) \<le> Sup A"
    if "(x::'a linear_space) \<in> A"
    for x :: "'a linear_space"
      and A :: "'a linear_space set"
    using that 
    apply transfer
    by (meson Union_upper closure_subset complex_vector.span_superset dual_order.trans)

  show "Sup A \<le> (z::'a linear_space)"
    if "\<And>x. (x::'a linear_space) \<in> A \<Longrightarrow> x \<le> z"
    for A :: "'a linear_space set"
      and z :: "'a linear_space"
    using that 
    apply transfer
    apply auto
    by (metis (no_types, hide_lams) Sup_least closed_subspace.closed closure_minimal subsetD subspace_span_A)

  show "Inf {} = (top::'a linear_space)"
    using \<open>\<And>z A. (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A\<close> top.extremum_uniqueI by auto

  show "Sup {} = (bot::'a linear_space)"
    using \<open>\<And>z A. (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z\<close> bot.extremum_uniqueI by auto    
qed
end

instance linear_space :: (chilbert_space) complete_orthomodular_lattice 
proof
  show "inf x (- x) = bot"
    for x :: "'a linear_space"
    apply transfer
    by (metis Complex_Vector_Spaces.subspace_0 insert_subset is_closed_subspace_universal_inclusion_left is_closed_subspace_zero ortho_inter_zero)
  show "sup x (- x) = top"
    for x :: "'a linear_space"
  proof-
    have \<open>closed_subspace x \<Longrightarrow> x +\<^sub>M orthogonal_complement x = UNIV\<close>
      for x::\<open>'a set\<close>
    proof-
      assume \<open>closed_subspace x\<close>
      have \<open>t \<in> x +\<^sub>M orthogonal_complement x\<close>
        for t
      proof-
        have \<open>t = (projection x) t + (projection (orthogonal_complement x)) t\<close>
          using \<open>closed_subspace x\<close> ortho_decomp by blast
        moreover have \<open>(projection x) t \<in> x\<close>
          by (simp add: \<open>closed_subspace x\<close> projection_intro2)        
        moreover have \<open>(projection (orthogonal_complement x)) t \<in> orthogonal_complement x\<close>
          by (simp add: \<open>closed_subspace x\<close> projection_intro2)        
        ultimately show ?thesis
        proof -
          have "orthogonal_complement x \<subseteq> x +\<^sub>M orthogonal_complement x"
            using \<open>closed_subspace x\<close> is_closed_subspace_universal_inclusion_right
              subspace_orthog by blast 
          thus ?thesis
            using \<open>closed_subspace x\<close> 
              \<open>projection (orthogonal_complement x) t \<in> orthogonal_complement x\<close> \<open>projection x t \<in> x\<close>
              \<open>t = projection x t + projection (orthogonal_complement x) t\<close> in_mono 
              is_closed_subspace_universal_inclusion_left complex_vector.subspace_def
            by (metis closed_subspace.subspace subspace_closed_plus subspace_orthog)               
        qed 
      qed
      thus ?thesis
        by auto 
    qed
    thus ?thesis
      apply transfer
      using ortho_decomp
      by blast
  qed
  show "- (- x) = x"
    for x :: "'a linear_space"
    apply transfer
    by (simp add: orthogonal_complement_twice)

  show "- y \<le> - x"
    if "x \<le> y"
    for x :: "'a linear_space"
      and y :: "'a linear_space"
    using that apply transfer
    by simp 

  show "sup x (inf (- x) y) = y"
    if "x \<le> y"
    for x :: "'a linear_space"
      and y :: "'a linear_space"
    using that apply transfer
  proof
    show "(x::'a set) +\<^sub>M orthogonal_complement x \<inter> y \<subseteq> y"
      if "closed_subspace (x::'a set)"
        and "closed_subspace (y::'a set)"
        and "(x::'a set) \<subseteq> y"
      for x :: "'a set"
        and y :: "'a set"
      using that
      by (simp add: is_closed_subspace_universal_inclusion_inverse) 

    show "y \<subseteq> x +\<^sub>M ((orthogonal_complement x) \<inter> y)"
      if "closed_subspace x"
        and "closed_subspace y"
        and "x \<subseteq> y"
      for x :: "'a set"
        and y :: "'a set"   
    proof-
      have \<open>u \<in> y \<Longrightarrow> u \<in> x +\<^sub>M ((orthogonal_complement x) \<inter> y)\<close>
        for u
      proof-
        assume \<open>u \<in> y\<close>
        have \<open>(projection x) u \<in> x\<close>
          by (simp add: projection_intro2 that(1))
        hence \<open>(projection x) u \<in> y\<close>
          using that(3) by auto        
        have \<open>subspace y\<close>
          by (simp add: closed_subspace.subspace that(2))          
        have \<open>u - (projection x) u \<in> orthogonal_complement x\<close>
          by (simp add: projection_intro1 that(1))
        moreover have  \<open>u - (projection x) u \<in> y\<close>
          using \<open>u \<in> y\<close> \<open>(projection x) u \<in> y\<close> \<open>subspace y\<close>
          by (simp add: Complex_Vector_Spaces.subspace_raw_def complex_vector.subspace_diff)
        ultimately have \<open>u - (projection x) u \<in> ((orthogonal_complement x) \<inter> y)\<close>
          by simp
        hence \<open>\<exists> v \<in> ((orthogonal_complement x) \<inter> y). u = (projection x) u + v\<close>
          by (metis \<open>u - projection x u \<in> orthogonal_complement x \<inter> y\<close> diff_add_cancel ordered_field_class.sign_simps(2))
        then obtain v where \<open>v \<in> ((orthogonal_complement x) \<inter> y)\<close> and \<open>u = (projection x) u + v\<close>
          by blast
        hence \<open>u \<in> x + ((orthogonal_complement x) \<inter> y)\<close>
          using \<open>projection x u \<in> x\<close> \<open>v \<in> ((orthogonal_complement x) \<inter> y)\<close> \<open>u = (projection x) u + v\<close>
          unfolding set_plus_def
          by blast
        thus ?thesis
          unfolding closed_sum_def
          using closure_subset by blast 
      qed
      thus ?thesis by blast
    qed
  qed

  show "x - y = inf x (- y)"
    for x :: "'a linear_space"
      and y :: "'a linear_space"
    apply transfer
    by simp
qed


lemma bounded_sesquilinear_bounded_clinnear_cinner_right:
  \<open>bounded_clinear A \<Longrightarrow> bounded_sesquilinear (\<lambda> x y. \<langle> x, A y \<rangle>)\<close>
  by (simp add: bounded_sesquilinear.comp2 bounded_sesquilinear_cinner)

lemma bounded_sesquilinear_bounded_clinnear_cinner_left:
  \<open>bounded_clinear A \<Longrightarrow> bounded_sesquilinear (\<lambda> x y. \<langle> A x, y \<rangle>)\<close>
  by (simp add: bounded_sesquilinear.comp1 bounded_sesquilinear_cinner)


subsection \<open>Unsorted\<close>

text \<open>Orthogonal set\<close>
definition is_ortho_set :: "'a::complex_inner set \<Rightarrow> bool" where
  \<open>is_ortho_set S = (\<forall> x \<in> S. \<forall> y \<in> S. x \<noteq> y \<longrightarrow> \<langle>x, y\<rangle> = 0)\<close>


text \<open>Orthonormal basis\<close>
definition is_onb :: "'a::complex_inner set \<Rightarrow> bool" 
  where "is_onb S  = (
  is_ortho_set S \<and> 
  is_basis S \<and>
  S \<subseteq> sphere 0 1
)"


lemma is_onb_nonzero:
  assumes \<open>is_onb S\<close> and \<open>x \<in> S\<close>
  shows \<open>x \<noteq> 0\<close>
proof -
  have f1: "(1::real) > 0"
    by auto
  have "\<forall>x. ((0::real) < x) = (\<not> x \<le> 0)"
    by auto
  then show ?thesis
    using f1 by (metis (no_types) assms(1) assms(2) is_onb_def sphere_nonzero)
qed 

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>is_onb\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>

class basis_enum = complex_inner +
  fixes canonical_basis :: "'a list"
    and canonical_basis_length :: "'a itself \<Rightarrow> nat"
  assumes distinct_canonical_basis:
    "distinct canonical_basis"
    and is_onb_set:
    "is_onb (set canonical_basis)"
    and canonical_basis_length_eq:
    "canonical_basis_length TYPE('a) = length canonical_basis"

lemma canonical_basis_non_zero:
  assumes \<open>x \<in> set (canonical_basis::('a::basis_enum list))\<close>
  shows \<open>x \<noteq> 0\<close>
  using assms is_onb_nonzero is_onb_set by blast

text \<open>The class \<open>one_dim\<close> applies to one-dimensional vector spaces.
Those are additionally interpreted as \<^class>\<open>complex_algebra_1\<close>s 
via the canonical isomorphism between a one-dimensional vector space and 
\<^typ>\<open>complex\<close>.\<close>
class one_dim = basis_enum + one + times + complex_inner +
  assumes one_dim_canonical_basis: "canonical_basis = [1]"
  (* TODO: replace by simpler "(a *\<^sub>C 1) * (b *\<^sub>C 1) = (a*b) *\<^sub>C 1" *)
  (* Jose: It produce errors *)
  (* TODO: but they were all easily fixable by proving one_dim_prod below (you can remove this TODO) *)
  assumes one_dim_prod_scale1: "(a *\<^sub>C 1) * (b *\<^sub>C 1) = (a*b) *\<^sub>C 1"
begin

definition one_dim_to_complex :: \<open>'a \<Rightarrow> complex\<close> where
  \<open>one_dim_to_complex \<psi> = \<langle>1, \<psi>\<rangle>\<close>

end

lemma span_explicit_finite:
\<open>finite A \<Longrightarrow> {\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> A} = {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}\<close>
for A::\<open>'a::complex_vector set\<close>
  proof
  show "{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> A} \<subseteq> {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}"
    if "finite A"
  proof
    show "x \<in> {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}"
      if "x \<in> {\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> A}"
      for x :: 'a
    proof-
      obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> A\<close> and \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        using \<open>x \<in> {\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> A}\<close> by blast
      define s where \<open>s a = (if a \<in> t then r a else 0)\<close> for a
      have \<open>x = (\<Sum>a\<in>A. s a *\<^sub>C a)\<close>
      proof-
        have \<open>(\<Sum>a\<in>A. s a *\<^sub>C a) = (\<Sum>a\<in>t. s a *\<^sub>C a) + (\<Sum>a\<in>A-t. s a *\<^sub>C a)\<close>
          by (metis (no_types, lifting) \<open>finite A\<close> \<open>t \<subseteq> A\<close> add.commute sum.subset_diff)
        moreover have \<open>(\<Sum>a\<in>t. s a *\<^sub>C a) = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
          using \<open>s \<equiv> \<lambda>a. if a \<in> t then r a else 0\<close> by auto          
        moreover have \<open>(\<Sum>a\<in>A-t. s a *\<^sub>C a) = 0\<close>
        proof-
          have \<open>a\<in>A-t \<Longrightarrow> s a *\<^sub>C a = 0\<close>
            for a
          proof-
            assume \<open>a\<in>A-t\<close>
            hence \<open>s a = 0\<close>
              by (simp add: s_def)
            hence \<open>s a *\<^sub>C a = 0 *\<^sub>C a\<close>
              by simp
            also have \<open>0 *\<^sub>C a = 0\<close>
              by simp              
            finally show ?thesis
              by simp 
          qed
          thus ?thesis
            by (simp add: \<open>\<And>a. a \<in> A - t \<Longrightarrow> s a *\<^sub>C a = 0\<close>)            
        qed
        ultimately show ?thesis
          by (simp add: \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>) 
      qed
      moreover have \<open>(\<Sum>a\<in>A. s a *\<^sub>C a) \<in> {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}\<close>
        by blast
      ultimately show ?thesis 
        by blast
    qed
  qed
  show "{\<Sum>a\<in>A. r a *\<^sub>C a |r. True} \<subseteq> {\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> A}"
    if "finite A"
    using that
    by auto 
qed


lemma one_dim_1_times_1: \<open>\<langle>(1::('a::one_dim)), 1\<rangle> = 1\<close>
proof-
  include notation_norm
  have \<open>(canonical_basis::'a list) = [1::('a::one_dim)]\<close>
    by (simp add: one_dim_canonical_basis)    
  hence \<open>is_onb {1::'a::one_dim}\<close>
    by (metis \<open>canonical_basis = [1]\<close> empty_set is_onb_set list.simps(15))    
  hence \<open>\<parallel>1::'a::one_dim\<parallel> = 1\<close>
    unfolding is_onb_def sphere_def
    using dist_norm
    by simp
  hence \<open>\<parallel>1::'a::one_dim\<parallel>^2 = 1\<close>
    by simp
  moreover have  \<open>\<parallel>(1::('a::one_dim))\<parallel>^2 = \<langle>(1::('a::one_dim)), 1\<rangle>\<close>
    using power2_norm_eq_cinner' by auto
  ultimately show ?thesis by simp
qed

lemma isCont_scalar_right:
  fixes k :: \<open>'a::complex_normed_vector\<close>
  shows \<open>isCont (\<lambda> t. t *\<^sub>C k) a\<close>
proof(cases \<open>k = 0\<close>)
  case True
  thus ?thesis
    by simp 
next
  case False
  define f where \<open>f t = t *\<^sub>C k\<close> for t
  have \<open>c \<longlonglongrightarrow> a \<Longrightarrow> (f \<circ> c) \<longlonglongrightarrow> f a\<close>
    for c
  proof-
    assume \<open>c \<longlonglongrightarrow> a\<close>
    hence  \<open>(\<lambda> n. norm ((c n) - a) ) \<longlonglongrightarrow> 0\<close>
      by (simp add: LIM_zero_iff tendsto_norm_zero)      
    hence  \<open>(\<lambda> n. norm ((c n) - a) * norm k ) \<longlonglongrightarrow> 0\<close>
      using tendsto_mult_left_zero by auto      
    moreover have \<open>norm (((c n) - a) *\<^sub>C k) = norm ((c n) - a) * norm k\<close>
      for n
      by simp      
    ultimately have  \<open>(\<lambda> n. norm (((c n) - a) *\<^sub>C k)) \<longlonglongrightarrow> 0\<close>
      by simp
    moreover have \<open>((c n) - a) *\<^sub>C k = (c n) *\<^sub>C k - a *\<^sub>C k\<close>
      for n
      by (simp add: scaleC_left.diff)
    ultimately have  \<open>(\<lambda> n. norm ((c n) *\<^sub>C k - a *\<^sub>C k)) \<longlonglongrightarrow> 0\<close>
      by simp
    hence  \<open>(\<lambda> n. dist ((c n) *\<^sub>C k) (a *\<^sub>C k)) \<longlonglongrightarrow> 0\<close>
      by (metis (no_types) LIM_zero_cancel \<open>(\<lambda>n. norm (c n *\<^sub>C k - a *\<^sub>C k)) \<longlonglongrightarrow> 0\<close> tendsto_dist_iff tendsto_norm_zero_iff)
    hence  \<open>(\<lambda> n. dist (((\<lambda>t. t *\<^sub>C k) \<circ> c) n) (a *\<^sub>C k)) \<longlonglongrightarrow> 0\<close>
      by simp
    hence  \<open>((\<lambda>t. t *\<^sub>C k) \<circ> c) \<longlonglongrightarrow> a *\<^sub>C k\<close>
      using tendsto_dist_iff by blast      
    thus \<open>(f \<circ> c) \<longlonglongrightarrow> f a\<close> 
      unfolding f_def by blast
  qed
  hence \<open>isCont f a\<close>
    by (simp add: continuous_at_sequentially)    
  thus ?thesis 
    unfolding f_def by blast
qed

lemma cinner_continuous_right:
  assumes \<open>t \<longlonglongrightarrow> y\<close>
  shows \<open>(\<lambda> n. \<langle> x, t n \<rangle>) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
proof-
  have \<open>(\<lambda> n. \<langle> x, t n - y \<rangle>) \<longlonglongrightarrow> 0\<close>
  proof-
    have \<open>\<exists> K. \<forall> a b::'a. norm \<langle>a, b\<rangle> \<le> norm a * norm b * K\<close>
      using bounded_sesquilinear.bounded bounded_sesquilinear_cinner by auto
    then obtain K where \<open>\<And> a b::'a. norm \<langle>a, b\<rangle> \<le> norm a * norm b * K\<close>
      by blast
    have \<open>(\<lambda> n. norm x * norm (t n - y)) \<longlonglongrightarrow> 0\<close>
    proof-
      have \<open>(\<lambda> n. t n - y) \<longlonglongrightarrow> 0\<close>
        using \<open>t \<longlonglongrightarrow> y\<close> LIM_zero by auto
      thus ?thesis
        by (simp add: tendsto_mult_right_zero tendsto_norm_zero) 
    qed
    moreover have \<open>norm \<langle> x, t n - y \<rangle> \<le> norm (norm x * norm (t n - y)) * K\<close>
      for n
      using \<open>\<And> a b::'a. norm \<langle>a, b\<rangle> \<le> norm a * norm b * K\<close>
      by auto
    ultimately show ?thesis using Limits.tendsto_0_le
      by (metis (no_types, lifting) eventually_sequentiallyI)
  qed
  moreover have \<open>\<langle> x, t n - y \<rangle> =  \<langle> x, t n \<rangle> - \<langle> x, y \<rangle>\<close>
    for n
    by (simp add: cinner_diff_right)    
  ultimately have \<open>(\<lambda> n. \<langle> x, t n \<rangle> - \<langle> x, y \<rangle>) \<longlonglongrightarrow> 0\<close>
    by simp
  thus ?thesis
    by (simp add: LIM_zero_iff) 
qed

lemma cinner_continuous_left:
  assumes \<open>t \<longlonglongrightarrow> x\<close>
  shows \<open>(\<lambda> n. \<langle> t n, y \<rangle>) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
proof-
  have \<open>(\<lambda> n. \<langle> y, t n \<rangle>) \<longlonglongrightarrow> \<langle> y, x \<rangle>\<close>
    by (simp add: assms cinner_continuous_right)
  hence \<open>(\<lambda> n. cnj \<langle> y, t n \<rangle>) \<longlonglongrightarrow> cnj \<langle> y, x \<rangle>\<close>
    using lim_cnj by fastforce
  moreover have \<open>cnj \<langle> y, t n \<rangle> = \<langle> t n, y \<rangle>\<close>
    for n
    by simp    
  moreover have \<open>cnj \<langle> y, x \<rangle> = \<langle> x, y \<rangle>\<close>
    by simp    
  ultimately show ?thesis 
    by simp
qed


lemma closed_line:
  \<open>closed {c *\<^sub>C (k::'a::complex_inner)| c. True}\<close>
proof(cases \<open>k = 0\<close>)
  case True
  hence \<open>{c *\<^sub>C k| c. True} = {0}\<close>
    by auto
  thus ?thesis
    by simp
next
  case False
  hence \<open>norm k > 0\<close>
    by simp
  have \<open>(\<And> n. x n \<in> {c *\<^sub>C k| c. True}) \<Longrightarrow>
        x \<longlonglongrightarrow> l \<Longrightarrow> l \<in> {c *\<^sub>C k| c. True}\<close>
    for x l
  proof-
    assume \<open>\<And> n. x n \<in> {c *\<^sub>C k| c. True}\<close> and
      \<open>x \<longlonglongrightarrow> l\<close>
    from \<open>\<And> n. x n \<in> {c *\<^sub>C k| c. True}\<close>
    have \<open>\<And> n. \<exists> c. x n = c *\<^sub>C k\<close>
      by simp
    hence \<open>\<exists> c. \<forall> n. x n = (c n) *\<^sub>C k\<close>
      by metis
    then obtain c where \<open>\<And> n. x n = (c n) *\<^sub>C k\<close>
      by blast
    from \<open>x \<longlonglongrightarrow> l\<close>
    have \<open>convergent x\<close>
      using convergentI by auto
    hence \<open>Cauchy x\<close>
      using LIMSEQ_imp_Cauchy convergent_def by blast
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (x m) (x n) < e\<close>
      unfolding Cauchy_def
      by blast
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (x m - x n) < e\<close>
      using dist_norm
      by (simp add: dist_norm)
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m *\<^sub>C k - c n *\<^sub>C k) < e\<close>
      by (simp add: \<open>\<And>n. x n = c n *\<^sub>C k\<close>)
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) * norm k < e\<close>
      by (metis complex_vector.scale_left_diff_distrib norm_scaleC)
    hence f1: \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) < e/norm k\<close>
      by (simp add: False linordered_field_class.pos_less_divide_eq)
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) < (e*(norm k))/(norm k)\<close>
    proof-
      have \<open>e>0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) < (e*(norm k))/(norm k)\<close>
        for e
      proof-
        assume \<open>e > 0\<close>
        hence  \<open>e * norm k > 0\<close>
          using \<open>norm k > 0\<close>
          by simp
        thus ?thesis
          using f1 by fastforce
      qed
      thus ?thesis by blast
    qed
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) < e\<close>
      using \<open>norm k > 0\<close>
      by simp
    hence \<open>Cauchy c\<close>
      by (simp add: CauchyI)
    hence \<open>convergent c\<close>
      by (simp add: Cauchy_convergent_iff)
    hence \<open>\<exists> a. c \<longlonglongrightarrow> a\<close>
      by (simp add: convergentD)
    then obtain a where \<open>c \<longlonglongrightarrow> a\<close>
      by blast
    define f where \<open>f t = t *\<^sub>C k\<close> for t
    have \<open>isCont f a\<close>
      using isCont_scalar_right 
      unfolding f_def by blast
    hence \<open>(\<lambda> n. f (c n)) \<longlonglongrightarrow>  f a\<close>
      using  \<open>c \<longlonglongrightarrow> a\<close> 
        Topological_Spaces.isContD[where f = "f" and x = "a"]
        isCont_tendsto_compose by blast 
    hence \<open>(\<lambda> n. (c n) *\<^sub>C k) \<longlonglongrightarrow> a *\<^sub>C k\<close>
      unfolding f_def
      by simp
    hence \<open>(\<lambda> n. x n) \<longlonglongrightarrow> a *\<^sub>C k\<close>
      using \<open>\<And> n. x n = (c n) *\<^sub>C k\<close>
      by simp
    hence \<open>x \<longlonglongrightarrow> a *\<^sub>C k\<close>
      by simp
    hence \<open>l = a *\<^sub>C k\<close>
      using LIMSEQ_unique \<open>x \<longlonglongrightarrow> l\<close> by blast
    moreover have \<open>a *\<^sub>C k \<in> {c *\<^sub>C k |c. True}\<close>
      by auto
    ultimately show ?thesis by blast
  qed
  thus ?thesis
    using closed_sequential_limits by blast 
qed



(* TODO: remove lemma (subsumed by closed_finite_dim' below, hide_fact does not fully remove it) *)
(* TODO: Use \<And> and \<Longrightarrow> instead of \<forall>, \<longrightarrow> *)
lemma closed_finite_dim'_induction:
  \<open>\<And> A::'a::complex_inner set. card A = n \<Longrightarrow> finite A \<Longrightarrow> 0 \<notin> A \<Longrightarrow>
 (\<And> a a'.  a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a \<noteq> a' \<Longrightarrow> \<langle>a, a'\<rangle> = 0)
\<Longrightarrow> closed (complex_vector.span A)\<close>
proof(induction n)
  case 0
  thus ?case
    by fastforce 
next
  case (Suc n)
  have \<open>card A = Suc n \<Longrightarrow> finite A \<Longrightarrow> 0 \<notin> A \<Longrightarrow> \<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0 
  \<Longrightarrow> closed (complex_vector.span A)\<close>
    for A::\<open>'a set\<close>
  proof-
    assume \<open>card A = Suc n\<close> and \<open>finite A\<close> and \<open>0 \<notin> A\<close> and
      \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
    from \<open>card A = Suc n\<close>
    have \<open>\<exists> b B. b \<notin> B \<and> A = insert b B\<close>
      by (meson card_Suc_eq)
    then obtain b B where \<open>b \<notin> B\<close> and \<open>A = insert b B\<close>
      by blast
    have \<open>card B = n\<close>
      using \<open>A = insert b B\<close> \<open>b \<notin> B\<close> \<open>card A = Suc n\<close> \<open>finite A\<close> 
      by auto      
    moreover have \<open>finite B\<close>
      using \<open>A = insert b B\<close> \<open>finite A\<close> 
      by auto
    moreover have \<open>0 \<notin> B\<close>
      using \<open>0 \<notin> A\<close> \<open>A = insert b B\<close> 
      by auto
    moreover have \<open>\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
      by (simp add: \<open>A = insert b B\<close> \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>)      
    ultimately have \<open>closed (complex_vector.span B)\<close>
      using Suc.IH by blast
    have \<open>(\<And> k. x k \<in> complex_vector.span A) \<Longrightarrow> x \<longlonglongrightarrow> l \<Longrightarrow> l \<in> complex_vector.span A\<close>
      for x l
    proof-
      assume \<open>\<And> k. x k \<in> complex_vector.span A\<close> and \<open>x \<longlonglongrightarrow> l\<close>
      have \<open>convergent x\<close>
        using  \<open>x \<longlonglongrightarrow> l\<close>
        unfolding convergent_def by blast
      have \<open>\<exists> c. x k - c *\<^sub>C b \<in> complex_vector.span B\<close>
        for k
        using \<open>A = insert b B\<close> \<open>\<And>k. x k \<in> complex_vector.span A\<close> complex_vector.span_breakdown_eq 
        by blast
      hence \<open>\<exists> c. \<forall> k. x k - (c k) *\<^sub>C b \<in> complex_vector.span B\<close>
        by metis
      then obtain c where \<open>\<And> k. x k - (c k) *\<^sub>C b \<in> complex_vector.span B\<close>
        by blast
      have \<open>convergent c\<close>
      proof-
        have \<open>b \<in> A\<close>
          by (simp add: \<open>A = insert b B\<close>)
        hence \<open>b \<noteq> 0\<close>
          using \<open>0 \<notin> A\<close> by auto          
        hence \<open>\<langle> b, b \<rangle> \<noteq> 0\<close>
          by simp          
        have \<open>\<langle> b, x k \<rangle> = c k * \<langle> b, b \<rangle>\<close>
          for k
        proof-
          have \<open>\<langle> b, x k \<rangle> = \<langle> b, (x k - c k *\<^sub>C b) + c k *\<^sub>C b\<rangle>\<close>
            by simp
          also have \<open>\<dots> = \<langle>b, x k - c k *\<^sub>C b\<rangle> + \<langle>b, c k *\<^sub>C b\<rangle>\<close>
            using cinner_right_distrib by blast
          also have \<open>\<dots> = \<langle>b, c k *\<^sub>C b\<rangle>\<close>
          proof-
            have \<open>b \<in> orthogonal_complement (complex_vector.span B)\<close>
            proof-
              have \<open>b' \<in> B \<Longrightarrow> \<langle>b, b'\<rangle> = 0\<close>
                for b'
                using \<open>A = insert b B\<close> \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> \<open>b \<notin> B\<close> 
                by auto
              hence \<open>b' \<in> complex_vector.span B \<Longrightarrow> \<langle>b, b'\<rangle> = 0\<close>
                for b'
              proof-
                assume \<open>b' \<in> complex_vector.span B\<close>
                hence \<open>\<exists> T r. finite T \<and> T \<subseteq> B \<and> b' = (\<Sum>a \<in>T. r a *\<^sub>C a)\<close>
                  by (smt complex_vector.span_explicit mem_Collect_eq)
                then obtain T r where \<open>finite T\<close> and \<open>T \<subseteq> B\<close> and \<open>b' = (\<Sum>a\<in>T. r a *\<^sub>C a)\<close>
                  by blast
                have \<open>\<langle>b, b'\<rangle> = (\<Sum>a\<in>T. \<langle>b, r a *\<^sub>C a\<rangle>)\<close>
                  using  \<open>finite T\<close> \<open>b' = (\<Sum>a\<in>T. r a *\<^sub>C a)\<close> cinner_sum_right by blast
                show \<open>\<langle>b, b'\<rangle> = 0\<close>
                proof-
                  have \<open>a \<in> T \<Longrightarrow> \<langle>b, r a *\<^sub>C a\<rangle> = 0\<close>
                    for a
                  proof-
                    assume \<open>a \<in> T\<close>
                    hence \<open>\<langle>b, a\<rangle> = 0\<close>
                      using \<open>T \<subseteq> B\<close> \<open>\<And>b'. b' \<in> B \<Longrightarrow> \<langle>b, b'\<rangle> = 0\<close>
                      by auto
                    thus ?thesis
                      by simp 
                  qed
                  thus ?thesis 
                    using \<open>\<langle>b, b'\<rangle> = (\<Sum>a\<in>T. \<langle>b, r a *\<^sub>C a\<rangle>)\<close> sum.not_neutral_contains_not_neutral 
                    by force                    
                qed
              qed
              thus ?thesis
                by (simp add: orthogonal_complement_I2) 
            qed
            hence \<open>\<langle>b, x k - c k *\<^sub>C b\<rangle> = 0\<close>
              using \<open>x k - c k *\<^sub>C b \<in> complex_vector.span B\<close>
              using orthogonal_complement_D1 by blast
            thus ?thesis by simp
          qed
          also have \<open>\<dots> = c k * \<langle>b, b\<rangle>\<close>
            by simp
          finally show ?thesis by blast
        qed
        moreover have \<open>(\<lambda> k. \<langle> b, x k \<rangle>) \<longlonglongrightarrow>  \<langle> b, l \<rangle>\<close>
          using \<open>x \<longlonglongrightarrow> l\<close>
          by (simp add: cinner_continuous_right)
        ultimately have \<open>(\<lambda> k. c k * \<langle> b, b \<rangle>) \<longlonglongrightarrow>  \<langle> b, l \<rangle>\<close>
          by simp
        hence \<open>convergent (\<lambda> k. c k * \<langle> b, b \<rangle>)\<close>
          using convergentI by auto
        hence \<open>convergent (\<lambda> k. (c k * \<langle> b, b \<rangle>)*(1/\<langle> b, b \<rangle>))\<close>
          using \<open>\<langle> b, b \<rangle> \<noteq> 0\<close>
          by (metis convergent_mult_const_right_iff divide_eq_0_iff zero_neq_one)          
        thus \<open>convergent c\<close>
          using \<open>\<langle> b, b \<rangle> \<noteq> 0\<close>
          by simp
      qed
      hence \<open>\<exists> a. c \<longlonglongrightarrow> a\<close>
        by (simp add: convergentD)
      then obtain a where \<open>c \<longlonglongrightarrow> a\<close>
        by blast
      moreover have \<open>isCont (\<lambda> t. t *\<^sub>C b) a\<close>
        using isCont_scalar_right by auto
      ultimately have \<open>(\<lambda> k. (c k) *\<^sub>C b) \<longlonglongrightarrow> a *\<^sub>C b\<close>
        using isCont_tendsto_compose[where g = "(\<lambda> t. t *\<^sub>C b)" and l = "a" and f = "c" 
            and F = "sequentially"]
        by blast
      hence \<open>(\<lambda> k. x k - (c k) *\<^sub>C b) \<longlonglongrightarrow> l - a *\<^sub>C b\<close>
        using \<open>x \<longlonglongrightarrow> l\<close> tendsto_diff by blast
      hence \<open>l - a *\<^sub>C b \<in> complex_vector.span B\<close>
        by (meson \<open>\<And>k. x k - c k *\<^sub>C b \<in> complex_vector.span B\<close> \<open>closed (complex_vector.span B)\<close> closed_sequentially)
      hence \<open>l - a *\<^sub>C b \<in> complex_vector.span A\<close>
        by (metis \<open>A = insert b B\<close> complex_vector.span_base complex_vector.span_breakdown_eq complex_vector.span_diff complex_vector.span_scale insertI1)
      moreover have \<open>a *\<^sub>C b \<in> complex_vector.span A\<close>
        by (simp add: \<open>A = insert b B\<close> complex_vector.span_base complex_vector.span_scale)
      ultimately show \<open>l \<in> complex_vector.span A\<close>
        using \<open>A = insert b B\<close> \<open>l - a *\<^sub>C b \<in> complex_vector.span B\<close> complex_vector.span_breakdown_eq 
        by blast 
    qed
    thus \<open>closed (complex_vector.span A)\<close>
      using closed_sequential_limits by blast      
  qed
  thus ?case 
    by (smt Suc.prems(1) Suc.prems(2) Suc.prems(3) Suc.prems(4))
      (* > 1s *)
qed

(* TODO: Remove lemma (subsumed by closed_finite_dim below) *)
lemma closed_finite_dim':
  fixes A::\<open>'a::complex_inner set\<close>
  assumes \<open>\<And> a a'. a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a \<noteq> a' \<Longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
    and \<open>0 \<notin> A\<close> and \<open>finite A\<close>
  shows \<open>closed (complex_vector.span A)\<close>
  using assms closed_finite_dim'_induction by blast

hide_fact closed_finite_dim'_induction

(* TODO: remove lemma (subsumed by Gram_Schmidt0' below, hide_fact does not fully remove it) *)
lemma Gram_Schmidt0':
  \<open>\<forall>S::'a::complex_inner set. 0\<notin>S \<and> finite S \<and> card S = n \<longrightarrow> (\<exists> A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> complex_vector.span A = complex_vector.span S
           \<and> 0 \<notin> A \<and> finite A)\<close>
proof (induction n)
  show "\<forall>S. (0::'a) \<notin> S \<and> finite S \<and> card S = 0 \<longrightarrow> (\<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<and> complex_vector.span A = complex_vector.span S \<and> 0 \<notin> A \<and> finite A)"
    using card_0_eq by blast

  show "\<forall>S. (0::'a) \<notin> S \<and> finite S \<and> card S = Suc n \<longrightarrow> (\<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<and> complex_vector.span A = complex_vector.span S \<and> 0 \<notin> A \<and> finite A)"
    if "\<forall>S. (0::'a) \<notin> S \<and> finite S \<and> card S = n \<longrightarrow> (\<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<and> complex_vector.span A = complex_vector.span S \<and> 0 \<notin> A \<and> finite A)"
    for n :: nat
  proof-
    have \<open>0 \<notin> S \<Longrightarrow> finite S \<Longrightarrow> card S = Suc n \<Longrightarrow> \<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. (a::'a) \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<and> complex_vector.span A = complex_vector.span S \<and> 0 \<notin> A \<and> finite A\<close>
      for S
    proof-
      assume \<open>0 \<notin> S\<close> and \<open>finite S\<close> and \<open>card S = Suc n\<close>
      hence \<open>\<exists> S' s. finite S' \<and> s\<notin>S' \<and> S = insert s S'\<close>
        by (metis card_Suc_eq finite_insert)
      then obtain S' s where \<open>finite S'\<close> and \<open>s\<notin>S'\<close> and \<open>S = insert s S'\<close>
        by blast
      have \<open>card S' = n\<close>
        using \<open>S = insert s S'\<close> \<open>card S = Suc n\<close> \<open>finite S'\<close> \<open>s \<notin> S'\<close> 
        by auto
      have \<open>\<exists>A'. (\<forall>a\<in>A'. \<forall>a'\<in>A'. (a::'a) \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<and> 
          complex_vector.span A' = complex_vector.span S' \<and> 0 \<notin> A' \<and> finite A'\<close>
        using \<open>0 \<notin> S\<close> \<open>S = insert s S'\<close> \<open>card S' = n\<close> \<open>finite S'\<close> that 
        by blast
      then obtain A'::\<open>'a set\<close> where \<open>\<forall>a\<in>A'. \<forall>a'\<in>A'. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> and
        \<open>complex_vector.span A' = complex_vector.span S'\<close> and \<open>0 \<notin> A'\<close> and \<open>finite A'\<close>
        by auto
      define \<sigma> where \<open>\<sigma> = s - (\<Sum>a'\<in>A'. ((cnj \<langle>s, a'\<rangle>)/\<langle>a', a'\<rangle>) *\<^sub>C a')\<close>
      show ?thesis
      proof (cases \<open>\<sigma> = 0\<close>)
        show "\<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<and> 
            complex_vector.span A = complex_vector.span S \<and> 0 \<notin> A \<and> finite A"
          if "\<sigma> = 0"
        proof-
          have \<open>complex_vector.span A' = complex_vector.span S\<close>
          proof-
            have \<open>s \<in> complex_vector.span A'\<close>
              unfolding \<sigma>_def
              by (metis (no_types, lifting) \<sigma>_def complex_vector.span_base complex_vector.span_scale complex_vector.span_sum eq_iff_diff_eq_0 that)
            thus ?thesis
              by (simp add: \<open>S = insert s S'\<close> \<open>complex_vector.span A' = complex_vector.span S'\<close> complex_vector.span_redundant) 
          qed
          thus ?thesis
            using \<open>0 \<notin> A'\<close> \<open>\<forall>a\<in>A'. \<forall>a'\<in>A'. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> \<open>finite A'\<close> 
            by blast 
        qed
        show "\<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<and> complex_vector.span A = complex_vector.span S \<and> 0 \<notin> A \<and> finite A"
          if "\<sigma> \<noteq> 0"
        proof-
          define A where \<open>A = insert \<sigma> A'\<close>
          have \<open>a\<in>A \<Longrightarrow> a'\<in>A \<Longrightarrow> a \<noteq> a' \<Longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
            for a a'
          proof (cases \<open>a \<in> A' \<and> a' \<in> A'\<close>)
            show "\<langle>a, a'\<rangle> = 0"
              if "a \<in> A"
                and "a' \<in> A"
                and "a \<noteq> a'"
                and "a \<in> A' \<and> a' \<in> A'"
              using that
              by (simp add: \<open>\<forall>a\<in>A'. \<forall>a'\<in>A'. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>) 
            show  "\<langle>a, a'\<rangle> = 0"
              if "a \<in> A"
                and "a' \<in> A"
                and "a \<noteq> a'"
                and "\<not> (a \<in> A' \<and> a' \<in> A')"
            proof-
              have \<open>a \<notin> A' \<or> a' \<notin> A'\<close>
                using that(4) by blast
              show ?thesis 
              proof (cases \<open>a \<notin> A'\<close>)
                have caseI : \<open>a \<in> A \<Longrightarrow> a' \<in> A \<Longrightarrow> a' \<in> A' \<Longrightarrow> a \<notin> A' \<Longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
                  for a a'::'a
                proof-
                  assume \<open>a \<in> A\<close> and \<open>a' \<in> A\<close> and \<open>a' \<in> A'\<close> and \<open>a \<notin> A'\<close>
                  have \<open>a = \<sigma>\<close>
                    using A_def \<open>a \<in> A\<close>
                    by (simp add: \<open>a \<notin> A'\<close>) 
                  hence \<open>\<langle>a, a'\<rangle> = \<langle>s - (\<Sum>a'\<in>A'.  ((cnj \<langle>s, a'\<rangle>)/\<langle>a', a'\<rangle>) *\<^sub>C a') , a'\<rangle>\<close>
                    using \<sigma>_def by auto
                  also have \<open>\<dots> = \<langle>s, a'\<rangle> - \<langle>(\<Sum>a'\<in>A'.  ((cnj \<langle>s, a'\<rangle>)/\<langle>a', a'\<rangle>) *\<^sub>C a'), a'\<rangle>\<close>
                    by (simp add: cinner_diff_left)
                  also have \<open>\<dots> = 0\<close>
                  proof-
                    have \<open>\<langle>(\<Sum>a''\<in>A'.  ((cnj \<langle>s, a''\<rangle>)/\<langle>a'', a''\<rangle>) *\<^sub>C a''), a'\<rangle>
                         = (\<Sum>a''\<in>A'. \<langle> ((cnj \<langle>s, a''\<rangle>)/\<langle>a'', a''\<rangle>) *\<^sub>C a'', a'\<rangle>)\<close>
                      using cinner_sum_left by blast
                    also have \<open>\<dots> = (\<Sum>a''\<in>A'.  (\<langle>s, a'\<rangle>/\<langle>a', a'\<rangle>) * \<langle> a'', a'\<rangle>)\<close>
                    proof-
                      have \<open>\<langle> ((cnj \<langle>s, a'\<rangle>)/\<langle>a', a'\<rangle>) *\<^sub>C a'', a'\<rangle> =  (\<langle>s, a'\<rangle>/\<langle>a', a'\<rangle>) * \<langle> a'', a'\<rangle>\<close>
                        for a'' a'
                        by simp
                      thus ?thesis
                        by (smt \<open>\<forall>a\<in>A'. \<forall>a'\<in>A'. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> \<open>a' \<in> A'\<close> cinner_scaleC_left mult_not_zero sum.cong) 
                    qed
                    also have \<open>\<dots> =  (\<langle>s, a'\<rangle>/\<langle>a', a'\<rangle>) * \<langle> a', a'\<rangle>
                                  + (\<Sum>a''\<in>A'-{a'}. (\<langle>s, a'\<rangle>/\<langle>a', a'\<rangle>) * \<langle> a'', a'\<rangle>)\<close>
                    proof-
                      have \<open>a' \<in> A\<close>
                        by (simp add: \<open>a' \<in> A\<close>)
                      thus ?thesis
                        by (meson \<open>a' \<in> A'\<close> \<open>finite A'\<close> sum.remove)                        
                    qed
                    also have \<open>\<dots> =  \<langle>s, a'\<rangle>\<close>
                    proof-
                      have \<open>a''\<in>A'-{a'} \<Longrightarrow> \<langle> a'', a' \<rangle> = 0\<close>
                        for a''
                        using \<open>\<forall>a\<in>A'. \<forall>a'\<in>A'. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> \<open>a' \<in> A'\<close> by auto                        
                      hence \<open>(\<Sum>a''\<in>A'-{a'}. (\<langle>s, a'\<rangle>/\<langle>a', a'\<rangle>) * \<langle> a'', a'\<rangle>) = 0\<close>
                        by simp                        
                      thus ?thesis by simp
                    qed
                    finally have \<open>\<langle>\<Sum>a''\<in>A'. ((cnj \<langle>s, a''\<rangle>)/\<langle>a'', a''\<rangle>) *\<^sub>C a'', a'\<rangle> = \<langle>s, a'\<rangle>\<close>
                      by blast
                    thus ?thesis by simp
                  qed
                  finally show ?thesis by blast
                qed
                show   "\<langle>a, a'\<rangle> = 0"
                  if "a \<notin> A'"
                proof-
                  have \<open>a' \<in> A'\<close>
                    using A_def \<open>a \<in> A\<close> \<open>a \<noteq> a'\<close> \<open>a' \<in> A\<close> that 
                    by auto
                  moreover have \<open>a \<notin> A'\<close>
                    using \<open>\<not> (a \<in> A' \<and> a' \<in> A')\<close> \<open>a' \<in> A'\<close>
                    by blast
                  ultimately show \<open>\<langle>a, a'\<rangle> = 0\<close>
                    using caseI[where a = "a" and a' = "a'"] \<open>a \<in> A\<close> \<open>a' \<in> A\<close> by blast
                qed
                show "\<langle>a, a'\<rangle> = 0"
                  if "\<not> a \<notin> A'"
                proof-
                  have \<open>a \<in> A'\<close>
                    using that by auto
                  moreover have \<open>a' \<notin> A'\<close>
                    using \<open>\<not> (a \<in> A' \<and> a' \<in> A')\<close> \<open>a \<in> A'\<close>
                    by blast
                  ultimately have \<open>\<langle>a', a\<rangle> = 0\<close>
                    using caseI[where a = "a'" and a' = "a"] \<open>a \<in> A\<close> \<open>a' \<in> A\<close> 
                    by blast
                  moreover have \<open>\<langle>a, a'\<rangle> =  cnj \<langle>a', a\<rangle>\<close>
                    by simp
                  ultimately show ?thesis by simp
                qed
              qed
            qed
          qed
          moreover have \<open>complex_vector.span A = complex_vector.span S\<close>
          proof-
            have \<open>complex_vector.span A \<subseteq> complex_vector.span S\<close>
            proof-
              have \<open>\<sigma> \<in> complex_vector.span S\<close>
              proof-
                have \<open>s \<in> S\<close>
                  by (simp add: \<open>S = insert s S'\<close>)                  
                moreover have \<open>(\<Sum>a'\<in>A'. (cnj \<langle>s, a'\<rangle> / \<langle>a', a'\<rangle>) *\<^sub>C a') \<in> complex_vector.span S\<close>
                proof-
                  have \<open>a'\<in>A' \<Longrightarrow> a' \<in> complex_vector.span S\<close>
                    for a'
                  proof-
                    assume \<open>a'\<in>A'\<close>
                    hence \<open>a' \<in> complex_vector.span S'\<close>
                      using \<open>complex_vector.span A' = complex_vector.span S'\<close> complex_vector.span_base
                      by blast
                    moreover have \<open>complex_vector.span S' \<subseteq> complex_vector.span S\<close>
                    proof-
                      have \<open>S' \<subseteq> S\<close>
                        by (simp add: \<open>S = insert s S'\<close> subset_insertI)
                      thus ?thesis
                        by (simp add: complex_vector.span_mono) 
                    qed
                    ultimately show ?thesis by blast
                  qed
                  thus ?thesis
                    by (simp add: complex_vector.span_scale complex_vector.span_sum) 
                qed
                ultimately show ?thesis
                  using \<sigma>_def complex_vector.span_base complex_vector.span_diff by blast 
              qed
              moreover have \<open>A' \<subseteq> complex_vector.span S\<close>
              proof-
                have \<open>A' \<subseteq> complex_vector.span A\<close>
                  by (simp add: A_def complex_vector.span_base subsetI)                  
                moreover have \<open>complex_vector.span A \<subseteq> complex_vector.span S\<close>
                  by (smt A_def \<open>S = insert s S'\<close> \<open>\<sigma> \<in> complex_vector.span S\<close> \<open>complex_vector.span A' = complex_vector.span S'\<close> complex_vector.span_mono complex_vector.span_span complex_vector.span_superset insert_subset order_subst1)
                    (* > 1 s *)
                ultimately show ?thesis by blast
              qed
              ultimately show ?thesis unfolding A_def
                by (metis complex_vector.span_mono complex_vector.span_span insert_subset) 
            qed
            moreover have \<open>complex_vector.span S \<subseteq> complex_vector.span A\<close>
            proof-
              have \<open>S \<subseteq> complex_vector.span A\<close>
              proof-
                have \<open>s \<in> complex_vector.span A\<close>
                proof-
                  have \<open>\<sigma> \<in> complex_vector.span A\<close>
                    by (simp add: A_def complex_vector.span_base)
                  moreover have \<open>\<sigma> - s  \<in> complex_vector.span A\<close>
                  proof-
                    have \<open>a'\<in>A' \<Longrightarrow> a' \<in> complex_vector.span A\<close>
                      for a'
                    proof-
                      assume \<open>a'\<in>A'\<close>
                      hence \<open> a' \<in> complex_vector.span A'\<close>
                        by (simp add: complex_vector.span_base)
                      moreover have \<open>complex_vector.span A' \<subseteq> complex_vector.span A\<close>
                      proof-
                        have \<open>A' \<subseteq> A\<close>
                          by (simp add: A_def subset_insertI)
                        thus ?thesis
                          by (simp add: complex_vector.span_mono) 
                      qed
                      ultimately show ?thesis by blast
                    qed
                    hence \<open>(\<Sum>a'\<in>A'. (cnj \<langle>s, a'\<rangle> / \<langle>a', a'\<rangle>) *\<^sub>C a') \<in> complex_vector.span A\<close>
                      by (simp add: complex_vector.span_scale complex_vector.span_sum)
                    thus ?thesis
                      unfolding \<sigma>_def
                      using complex_vector.span_diff complex_vector.span_zero by fastforce 
                  qed
                  ultimately show ?thesis
                    by (metis complex_vector.eq_span_insert_eq complex_vector.span_base complex_vector.span_redundant insertI1) 
                qed
                moreover have \<open>S' \<subseteq> complex_vector.span A\<close>
                proof-
                  have \<open>S' \<subseteq>  complex_vector.span S'\<close>
                    using complex_vector.span_eq by auto
                  hence \<open>S' \<subseteq>  complex_vector.span A'\<close>
                    by (simp add: \<open>complex_vector.span A' = complex_vector.span S'\<close>)
                  moreover have \<open>complex_vector.span A' \<subseteq> complex_vector.span A\<close>
                  proof-
                    have  \<open>A' \<subseteq> A\<close>
                      by (simp add: A_def subset_insertI)
                    thus ?thesis
                      by (simp add: complex_vector.span_mono) 
                  qed
                  ultimately show ?thesis by blast
                qed
                ultimately show ?thesis
                  by (simp add: \<open>S = insert s S'\<close>) 
              qed
              thus ?thesis
                using complex_vector.span_mono complex_vector.span_span
                by blast 
            qed
            ultimately show ?thesis by auto
          qed
          moreover have \<open>0 \<notin> A\<close>
            by (simp add: A_def \<open>0 \<notin> A'\<close> that)            
          moreover have \<open>finite A\<close>
            by (simp add: A_def \<open>finite A'\<close>)            
          ultimately show ?thesis by blast
        qed
      qed
    qed
    thus ?thesis by blast
  qed
qed


lemma Gram_Schmidt0:
  fixes S::\<open>'a::complex_inner set\<close>
  assumes \<open>0 \<notin> S\<close> and \<open>finite S\<close>
  shows \<open>\<exists> A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> complex_vector.span A = complex_vector.span S
           \<and> 0 \<notin> A \<and> finite A\<close>
  using assms Gram_Schmidt0' by blast

hide_fact Gram_Schmidt0'

lemma Gram_Schmidt:
  fixes S::\<open>'a::complex_inner set\<close>
  assumes \<open>finite S\<close>
  shows \<open>\<exists> A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> complex_vector.span A = complex_vector.span S
           \<and> 0 \<notin> A \<and> finite A\<close>
proof-
  have \<open>0 \<notin> S - {0}\<close>
    by simp
  moreover have \<open>finite (S - {0})\<close>
    using \<open>finite S\<close>
    by simp
  ultimately have \<open>\<exists> A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> complex_vector.span A = complex_vector.span (S-{0})
           \<and> 0 \<notin> A \<and> finite A\<close>
    using Gram_Schmidt0[where S = "S - {0}"]
    by blast
  moreover have \<open>complex_vector.span (S - {0}) =  complex_vector.span S\<close>
    by simp
  ultimately show ?thesis by simp
qed

thm Gram_Schmidt

hide_fact Gram_Schmidt0

(* TODO: Use the one from ToDo_Finite_Span_Closed instead. *)
lemma closed_finite_dim:
  fixes T::\<open>'a::complex_inner set\<close>
  assumes \<open>finite T\<close>
  shows \<open>closed (complex_vector.span T)\<close>
proof-
  have \<open>\<exists> A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> complex_vector.span A = complex_vector.span T
           \<and> 0 \<notin> A \<and> finite A\<close>
    using \<open>finite T\<close> Gram_Schmidt by blast
  then obtain A where \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
    and \<open>complex_vector.span A = complex_vector.span T\<close>
    and \<open>0 \<notin> A\<close> and \<open>finite A\<close>
    by auto
  hence \<open>closed (complex_vector.span A)\<close>
    using closed_finite_dim' by blast
  thus ?thesis 
    using \<open>complex_vector.span A = complex_vector.span T\<close>
    by auto
qed

lemma one_dim_1_times_a_eq_a: \<open>\<langle>1::('a::one_dim), a\<rangle> *\<^sub>C 1 = a\<close>
proof-
  have \<open>(canonical_basis::'a list) = [1]\<close>
    by (simp add: one_dim_canonical_basis)
  hence \<open>is_onb {1::'a}\<close>
    by (metis \<open>canonical_basis = [1]\<close> empty_set is_onb_set list.simps(15))    
  hence \<open>a \<in> complex_vector.span ({1::'a})\<close>
    unfolding is_onb_def is_basis_def
    apply auto
    using closed_finite_dim 
    by (metis closure_eq finite.emptyI finite.insertI iso_tuple_UNIV_I)
  hence \<open>\<exists> s. a = s *\<^sub>C 1\<close>
  proof -
    have "(1::'a) \<notin> {}"
      by (metis equals0D)
    then show ?thesis
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
    by (simp add: one_dim_prod)
  show "(a + b) * c = a * c + b * c"
    for a :: 'a
      and b :: 'a
      and c :: 'a
    apply (simp add: one_dim_prod)
    by (metis (no_types, lifting) cinner_right_distrib scaleC_add_left scaleC_scaleC)
  show "a * (b + c) = a * b + a * c"
    for a :: 'a
      and b :: 'a
      and c :: 'a
    apply (simp add: one_dim_prod)
    by (simp add: cinner_right_distrib scaleC_add_left vector_space_over_itself.scale_right_distrib)
  show "(a *\<^sub>C x) * y = a *\<^sub>C (x * y)"
    for a :: complex
      and x :: 'a
      and y :: 'a
    apply (simp add: one_dim_prod).
  show "x * (a *\<^sub>C y) = a *\<^sub>C (x * y)"
    for x :: 'a
      and a :: complex
      and y :: 'a
    apply (simp add: one_dim_prod).
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
      by (simp add: one_dim_prod)
  qed
  show "(a::'a) * 1 = a"
    for a :: 'a
        apply (simp add: one_dim_prod)
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


lemma one_dim_to_complex_one[simp]: "one_dim_to_complex (1::'a::one_dim) = 1"
  by (simp add: one_dim_1_times_1 one_dim_to_complex_def)

(* TODO: prove those lemmas. Some of them can be moved into the class one_dim context above
(before \<open>instance one_dim \<subseteq> complex_algebra_1\<close>) if they are useful for the proof
of that instance. *)
context one_dim begin

lemma one_dim_to_complex_inverse[simp]: "of_complex (one_dim_to_complex \<psi>) = \<psi>"
  by (simp add: of_complex_def one_dim_1_times_a_eq_a one_dim_class.one_dim_to_complex_def)
  
lemma complex_to_one_dim_inverse[simp]: "one_dim_to_complex (of_complex c) = c"
  using of_complex_eq_iff one_dim_to_complex_inverse by blast
  
lemma bounded_clinear_one_dim_to_complex: "bounded_clinear one_dim_to_complex"
  by (smt Adj_D Adj_I Adj_I' Adj_bounded_clinear bounded_clinear_of_complex complex_inner_1_left of_complex_1 one_dim_class.one_dim_to_complex_def)
  
end

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>is_onb\<close>, SOME \<^typ>\<open>'a::complex_inner set \<Rightarrow> bool\<close>)\<close>


lemma bounded_sesquilinear_0_left: 
  assumes \<open>bounded_sesquilinear B\<close>
  shows \<open>B 0 y = 0\<close>
proof-
  have \<open>B 0 y = B (0 + 0) y\<close>
    by simp
  also have \<open>\<dots> = B 0 y + B 0 y\<close>
    using assms bounded_sesquilinear.add_left by blast
  finally have \<open>B 0 y = B 0 y + B 0 y\<close>
    by blast
  thus ?thesis by simp
qed

lemma sesquilinear_finite_sum_induction:
  assumes \<open>bounded_sesquilinear B\<close>
  shows \<open>\<forall> t. finite t \<and> card t = n \<longrightarrow> B (\<Sum>a\<in>t. (r a) *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)\<close>
proof (induction n)
  show "\<forall>t. finite t \<and> card t = 0 \<longrightarrow> B (\<Sum>a\<in>t. r a *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)"
  proof
    show "finite t \<and> card t = 0 \<longrightarrow> B (\<Sum>a\<in>t. r a *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)"
      for t :: "'a set"
    proof
      show "B (\<Sum>a\<in>t. r a *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)"
        if "finite t \<and> card t = 0"
        using that proof
        show "B (\<Sum>a\<in>t. r a *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)"
          if "finite t"
            and "card t = 0"
        proof-
          have \<open>(\<Sum>a\<in>t. r a *\<^sub>C a) = 0\<close>
            using card_0_eq sum_clauses(1) that(1) that(2) by blast
          hence \<open>B (\<Sum>a\<in>t. r a *\<^sub>C a) y = B 0 y\<close>
            by simp
          also have \<open>B 0 y = 0\<close>
            using bounded_sesquilinear_0_left \<open>bounded_sesquilinear B\<close> by blast
          finally have \<open>B (\<Sum>a\<in>t. r a *\<^sub>C a) y = 0\<close>
            by blast
          moreover have \<open>(\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y) = 0\<close>
            using card_0_eq sum_clauses(1) that(1) that(2) by blast
          ultimately show ?thesis by simp
        qed
      qed
    qed
  qed
  show "\<forall>t. finite t \<and> card t = Suc n \<longrightarrow> B (\<Sum>a\<in>t. r a *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)"
    if "\<forall>t. finite t \<and> card t = n \<longrightarrow> B (\<Sum>a\<in>t. r a *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)"
    for n :: nat
  proof-
    have \<open>finite t \<Longrightarrow> card t = Suc n \<Longrightarrow> B (\<Sum>a\<in>t. r a *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)\<close>
      for t
    proof-
      assume \<open>finite t\<close> and \<open>card t = Suc n\<close>
      hence \<open>\<exists> k s. finite s \<and> card s = n \<and> insert k s = t\<close>
        by (metis card_Suc_eq finite_insert)
      then obtain k s where \<open>finite s\<close> and \<open>card s = n\<close> and \<open>insert k s = t\<close>
        by blast
      have \<open>B (\<Sum>a\<in>t. r a *\<^sub>C a) y = B (\<Sum>a\<in>s. r a *\<^sub>C a) y +  cnj (r k) *\<^sub>C B k y\<close>
      proof-
        have \<open>(\<Sum>a\<in>t. r a *\<^sub>C a) = (\<Sum>a\<in>s. r a *\<^sub>C a) +  r k *\<^sub>C k\<close>
        proof -
          have "card (insert k s) = Suc n"
            by (metis \<open>card t = Suc n\<close> \<open>insert k s = t\<close>)
          hence "k \<notin> s"
            by (metis \<open>card s = n\<close> \<open>finite s\<close> card_insert_if n_not_Suc_n)
          thus ?thesis
            using \<open>finite s\<close> \<open>insert k s = t\<close> by auto
        qed
        hence \<open>B (\<Sum>a\<in>t. r a *\<^sub>C a) y = B (\<Sum>a\<in>s. r a *\<^sub>C a) y + B (r k *\<^sub>C k) y\<close>
          by (simp add: assms bounded_sesquilinear.add_left)
        thus ?thesis
          by (simp add: assms bounded_sesquilinear.scaleC_left) 
      qed
      moreover have \<open>(\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y) = (\<Sum>a\<in>s. cnj (r a) *\<^sub>C B a y) +  cnj (r k) *\<^sub>C B k y\<close>
        by (metis (no_types, lifting) \<open>card s = n\<close> \<open>card t = Suc n\<close> \<open>finite s\<close> \<open>insert k s = t\<close> add.commute card_insert_if n_not_Suc_n sum.insert)
      moreover have \<open>B (\<Sum>a\<in>s. r a *\<^sub>C a) y = (\<Sum>a\<in>s. cnj (r a) *\<^sub>C B a y)\<close>
        using \<open>card s = n\<close> \<open>finite s\<close> that by auto        
      ultimately show ?thesis by simp
    qed
    thus ?thesis by blast
  qed
qed

lemma sesquilinear_finite_sum:                     
  assumes \<open>bounded_sesquilinear B\<close> and \<open>finite t\<close>
  shows \<open>B (\<Sum>a\<in>t. (r a) *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)\<close>
  by (simp add: sesquilinear_finite_sum_induction assms(1) assms(2))

lemma sesquilinear_superposition:
  assumes \<open>bounded_sesquilinear B\<close> and \<open>\<And> p q. p \<in> S_left \<Longrightarrow> q \<in> S_right \<Longrightarrow> B p q = 0\<close>
    and \<open>x \<in> complex_vector.span S_left\<close> and \<open>y \<in> complex_vector.span S_right\<close>
  shows \<open>B x y = 0\<close>
proof-
  have \<open>y \<in> complex_vector.span S_right \<Longrightarrow> \<forall> p \<in> S_left. B p y = 0\<close>
    for y
  proof (rule complex_vector.span_induct)
    show "(0::'c) \<in> complex_vector.span {0}"
      if "y \<in> complex_vector.span S_right"
      by auto
    show "complex_vector.subspace {a. \<forall>p\<in>S_left. B p y = a}"
      if "y \<in> complex_vector.span S_right"
      unfolding complex_vector.subspace_def
    proof
      show "0 \<in> {a. \<forall>p\<in>S_left. B p y = a}"
      proof-
        have \<open>p\<in>S_left \<Longrightarrow> B p y = 0\<close>
          for p
        proof-
          assume \<open>p\<in>S_left\<close>
          moreover have \<open>t \<in> complex_vector.span S_right \<Longrightarrow> B p t = 0\<close>
            for t
          proof (rule complex_vector.span_induct)
            show "(0::'c) \<in> complex_vector.span {0}"
              if "t \<in> complex_vector.span S_right"
              by auto
            show "complex_vector.subspace {a. B p t = a}"
              if "t \<in> complex_vector.span S_right"
              unfolding complex_vector.subspace_def
            proof
              show "0 \<in> Collect ((=) (B p t))"
              proof -
                have "clinear (B p)"
                  by (meson assms(1) bounded_sesquilinear.add_right bounded_sesquilinear.scaleC_right clinearI)
                hence "B p t = 0"
                  using assms(2) calculation complex_vector.linear_eq_0_on_span that by fastforce
                thus ?thesis
                  by (metis (full_types) mem_Collect_eq)
              qed
              show "(\<forall>x\<in>Collect ((=) (B p t)). \<forall>y\<in>Collect ((=) (B p t)). x + y \<in> Collect ((=) (B p t)))
           \<and> (\<forall>c. \<forall>x\<in>Collect ((=) (B p t)). c *\<^sub>C x \<in> Collect ((=) (B p t)))"
              proof
                show "\<forall>x\<in>Collect ((=) (B p t)). \<forall>y\<in>Collect ((=) (B p t)). x + y \<in> Collect ((=) (B p t))"
                  using \<open>0 \<in> Collect ((=) (B p t))\<close> by auto              
                show "\<forall>c. \<forall>x\<in>Collect ((=) (B p t)). c *\<^sub>C x \<in> Collect ((=) (B p t))"
                  using \<open>0 \<in> Collect ((=) (B p t))\<close> by auto              
              qed
            qed
            show "B p t = x"
              if "t \<in> complex_vector.span S_right"
                and "(x::'c) \<in> {0}"
              for x :: 'c
              using that
              using \<open>t \<in> complex_vector.span S_right \<Longrightarrow> complex_vector.subspace {a. B p t = a}\<close> complex_vector.subspace_0 by blast 
          qed
          ultimately show ?thesis
            by (simp add: that) 
        qed
        thus ?thesis
          by simp
      qed
      show "(\<forall>a\<in>{a. \<forall>p\<in>S_left. B p y = a}. \<forall>b\<in>{a. \<forall>p\<in>S_left. B p y = a}. a + b \<in> {a. \<forall>p\<in>S_left. B p y = a})
   \<and> (\<forall>c. \<forall>a\<in>{a. \<forall>p\<in>S_left. B p y = a}. c *\<^sub>C a \<in> {a. \<forall>p\<in>S_left. B p y = a})"
      proof
        show "\<forall>a\<in>{a. \<forall>p\<in>S_left. B p y = a}. \<forall>b\<in>{a. \<forall>p\<in>S_left. B p y = a}. a + b \<in> {a. \<forall>p\<in>S_left. B p y = a}"
          using \<open>0 \<in> {a. \<forall>p\<in>S_left. B p y = a}\<close> by auto      
        show "\<forall>c. \<forall>a\<in>{a. \<forall>p\<in>S_left. B p y = a}. c *\<^sub>C a \<in> {a. \<forall>p\<in>S_left. B p y = a}"
          using \<open>0 \<in> {a. \<forall>p\<in>S_left. B p y = a}\<close> by auto      
      qed
    qed
    show "\<forall>p\<in>S_left. B p y = x"
      if "y \<in> complex_vector.span S_right"
        and "(x::'c) \<in> {0}"
      for x :: 'c
      using that \<open>y \<in> complex_vector.span S_right \<Longrightarrow> complex_vector.subspace {a. \<forall>p\<in>S_left. B p y = a}\<close> complex_vector.subspace_0 by blast 
  qed
  hence \<open>\<forall> y \<in> complex_vector.span S_right. \<forall> p \<in> S_left. B p y = 0\<close>
    by blast
  hence \<open>\<forall> p \<in> S_left. \<forall> y \<in> complex_vector.span S_right. B p y = 0\<close>
    by blast
  have "B p y = 0"
    if "p \<in> complex_vector.span S_left"
      and "y \<in> complex_vector.span S_right"
    for y and p
  proof-
    have \<open>\<exists> t r. finite t \<and> t \<subseteq> S_left \<and> p = (\<Sum>a\<in>t. (r a) *\<^sub>C a)\<close>
      using complex_vector.span_explicit
      by (smt mem_Collect_eq that(1)) 
    then obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> S_left\<close> and \<open>p = (\<Sum>a\<in>t. (r a) *\<^sub>C a)\<close>
      by blast
    have \<open>B p y = B (\<Sum>a\<in>t. (r a) *\<^sub>C a) y\<close>
      using \<open>p = (\<Sum>a\<in>t. (r a) *\<^sub>C a)\<close> by blast
    also have \<open>\<dots> = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)\<close>
      using sesquilinear_finite_sum \<open>bounded_sesquilinear B\<close> \<open>finite t\<close>
      by blast
    also have \<open>\<dots> = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C 0)\<close>
      using  \<open>t \<subseteq> S_left\<close> \<open>\<And>y. y \<in> complex_vector.span S_right \<Longrightarrow> \<forall>p\<in>S_left. B p y = 0\<close>
        in_mono that(2) by fastforce
    also have \<open>\<dots> = (\<Sum>a\<in>t. 0)\<close>
      by simp
    also have \<open>\<dots> = 0\<close>
      by simp
    finally show ?thesis
      by blast
  qed
  thus ?thesis
    by (simp add: assms(3) assms(4))        
qed

lemma bounded_sesquilinear_continuous:
  includes nsa_notation
  assumes \<open>bounded_sesquilinear B\<close>
    and \<open>star_of x \<approx> u\<close> and \<open>star_of y \<approx> v\<close>
  shows \<open>(*f2* B) (star_of x) (star_of y) \<approx> (*f2* B) u v\<close>
proof-
  have \<open>B x y = B (x - p) (y - q) + (B x q - B p q) + (B p y - B p q) + B p q\<close>
    for p q
  proof-
    have \<open>B (x - p) (y - q) = B x y - B x q - B p y + B p q\<close>
      using \<open>bounded_sesquilinear B\<close>
      by (smt add.assoc add.commute add_left_imp_eq bounded_sesquilinear.add_left bounded_sesquilinear.add_right diff_add_cancel)
    thus ?thesis by auto
  qed
  hence \<open>\<forall> p q. B x y = B (x - p) (y - q) + (B x q - B p q) + (B p y - B p q) + B p q\<close>
    by blast
  hence \<open>\<forall> p q. (*f2* B) (star_of x) (star_of y) = (*f2* B) (star_of x - p) (star_of y - q)
     + ((*f2* B) (star_of x) q - (*f2* B) p q)
     + ((*f2* B) p (star_of y) - (*f2* B) p q) + (*f2* B) p q\<close>
    by StarDef.transfer
  hence \<open>(*f2* B) (star_of x) (star_of y) \<approx>
     (*f2* B) (star_of x - p) (star_of y - q)
   + ((*f2* B) (star_of x) q - (*f2* B) p q)
   + ((*f2* B) p (star_of y) - (*f2* B) p q) + (*f2* B) p q\<close>
    for p q
    by auto
  moreover have \<open>(*f2* B) (star_of x - u) (star_of y - v) \<approx> 0\<close>
  proof-
    have \<open>\<exists> K. \<forall> p q. norm (B (x - p) (y - q)) \<le> norm (x - p) * norm (y - q) * K\<close>
      using assms(1) bounded_sesquilinear.bounded by blast
    then obtain K where \<open>\<forall> p q. norm (B (x - p) (y - q)) \<le> norm (x - p) * norm (y - q) * K\<close>
      by blast
    hence  \<open>\<forall> p q. hnorm ((*f2* B) (star_of x - p) (star_of y - q))
         \<le> hnorm (star_of x - p) * hnorm (star_of y - q) * (star_of K)\<close>
      by StarDef.transfer
    hence \<open>hnorm ((*f2* B) (star_of x - u) (star_of y - v)) 
      \<le> hnorm (star_of x - u) * hnorm (star_of y - v) * (star_of K)\<close>
      by blast
    moreover have \<open>hnorm (star_of x - u) * hnorm (star_of y - v) * (star_of K) \<in> Infinitesimal\<close>
      by (simp add: Infinitesimal_approx_minus Infinitesimal_hnorm_iff Infinitesimal_mult Infinitesimal_star_of_mult assms(2) assms(3))
    ultimately show ?thesis
      using hnorm_le_Infinitesimal mem_infmal_iff by blast 
  qed
  moreover have \<open>(*f2* B) (star_of x) v - (*f2* B) u v \<approx> 0\<close>
  proof-
    have \<open>(*f2* B) (star_of x) v - (*f2* B) u v
        = (*f2* B) (star_of x - u) v\<close>
    proof-
      have \<open>\<forall> p q. B x q - B p q = B (x - p) q\<close>
        by (metis (mono_tags, lifting) assms(1) bounded_sesquilinear.add_left eq_diff_eq)
      hence \<open>\<forall> p q. (*f2* B) (star_of x) q - (*f2* B) p q = (*f2* B) (star_of x - p) q\<close>
        by StarDef.transfer
      thus ?thesis by blast
    qed
    moreover have \<open>(*f2* B) (star_of x - u) v \<approx> 0\<close>
    proof-
      have \<open>\<exists> K. \<forall> p q. norm (B (x - p) q) \<le> norm (x - p) * norm q * K\<close>
        using assms(1) bounded_sesquilinear.bounded by blast
      then obtain K where \<open>\<forall> p q. norm (B (x - p) q) \<le> norm (x - p) * norm q * K\<close>
        by blast
      from  \<open>\<forall> p q. norm (B (x - p) q) \<le> norm (x - p) * norm q * K\<close>
      have  \<open>\<forall> p q. hnorm ((*f2* B) (star_of x - p) q)
           \<le> hnorm (star_of x - p) * hnorm q * (star_of K)\<close>
        by StarDef.transfer
      hence \<open>hnorm ((*f2* B) (star_of x - u) v)
           \<le> hnorm (star_of x - u) * hnorm v * (star_of K)\<close>
        by blast
      moreover have \<open>hnorm (star_of x - u) * hnorm v * (star_of K) \<in> Infinitesimal\<close>
      proof-
        have \<open>hnorm (star_of x - u) \<in> Infinitesimal\<close>
          by (simp add: Infinitesimal_approx_minus Infinitesimal_hnorm_iff assms(2))
        moreover have \<open>hnorm v \<in> HFinite\<close>
          using \<open>star_of y \<approx> v\<close>
          by (metis HFinite_star_of approx_HFinite approx_hnorm star_of_norm)
        moreover have \<open>star_of K \<in> HFinite\<close>
          by auto
        ultimately show ?thesis
          using Infinitesimal_HFinite_mult by blast 
      qed
      ultimately show ?thesis
        using hnorm_le_Infinitesimal mem_infmal_iff by blast 
    qed
    ultimately show ?thesis by simp
  qed
  moreover have \<open>((*f2* B) u (star_of y) - (*f2* B) u v) \<approx> 0\<close>
  proof-
    have \<open>\<exists> K. \<forall> p q. norm (B p (y - q)) \<le> norm p * norm (y - q) * K\<close>
      using assms(1) bounded_sesquilinear.bounded by blast
    then obtain K where \<open>\<forall> p q. norm (B p (y - q)) \<le> norm p * norm (y - q) * K\<close>
      by blast
    from  \<open>\<forall> p q. norm (B p (y - q)) \<le> norm p * norm (y - q) * K\<close>
    have  \<open>\<forall> p q. hnorm ((*f2* B) p (star_of y - q))
           \<le> hnorm p * hnorm (star_of y - q) * (star_of K)\<close>
      by StarDef.transfer
    hence \<open>hnorm ((*f2* B) u (star_of y - v))
           \<le> hnorm u * hnorm (star_of y - v) * (star_of K)\<close>
      by blast
    moreover have \<open>hnorm u * hnorm (star_of y - v) * (star_of K) \<in> Infinitesimal\<close>
    proof-
      have \<open>hnorm (star_of y - v) \<in> Infinitesimal\<close>
        by (simp add: Infinitesimal_approx_minus Infinitesimal_hnorm_iff assms(3))
      moreover have \<open>hnorm u \<in> HFinite\<close>
        using \<open>star_of x \<approx> u\<close>
        by (metis HFinite_star_of approx_HFinite approx_hnorm star_of_norm)
      moreover have \<open>star_of K \<in> HFinite\<close>
        by auto
      ultimately show ?thesis
        by (meson Infinitesimal_HFinite_mult Infinitesimal_HFinite_mult2 \<open>hnorm (star_of y - v) \<in> Infinitesimal\<close> \<open>hnorm u \<in> HFinite\<close> \<open>hypreal_of_real K \<in> HFinite\<close>)
    qed
    ultimately have \<open>(*f2* B) u (star_of y - v) \<in> Infinitesimal\<close>
      using hnorm_le_Infinitesimal   
      by blast
    moreover have \<open>(*f2* B) u (star_of y) - (*f2* B) u v
        = (*f2* B) u (star_of y - v)\<close>
    proof-
      have \<open>\<forall> p q. B p y - B p q = B p (y - q)\<close>
        by (metis (mono_tags, lifting) assms(1) bounded_sesquilinear.add_right eq_diff_eq)
      hence \<open>\<forall> p q. (*f2* B) p (star_of y) - (*f2* B) p q = (*f2* B) p (star_of y - q)\<close>
        by StarDef.transfer
      thus ?thesis by blast
    qed
    ultimately show ?thesis
      by (simp add: mem_infmal_iff) 
  qed
  ultimately show \<open>(*f2* B) (star_of x) (star_of y) \<approx> (*f2* B) u v\<close>
  proof -
    have f1: "monad ((*f2* B) (star_of x) (star_of y)) = monad ((*f2* B) (star_of x - u) (star_of y - v) + ((*f2* B) (star_of x) v - (*f2* B) u v) + ((*f2* B) u (star_of y) - (*f2* B) u v) + (*f2* B) u v)"
      by (meson \<open>\<And>q p. (*f2* B) (star_of x) (star_of y) \<approx> (*f2* B) (star_of x - p) (star_of y - q) + ((*f2* B) (star_of x) q - (*f2* B) p q) + ((*f2* B) p (star_of y) - (*f2* B) p q) + (*f2* B) p q\<close> approx_monad_iff)
    have "(0::'c star) \<in> monad 0"
      by (meson Infinitesimal_monad_zero_iff Infinitesimal_zero)
    hence "monad ((*f2* B) u v + ((*f2* B) u (star_of y) - (*f2* B) u v + ((*f2* B) (star_of x - u) (star_of y - v) + ((*f2* B) (star_of x) v - (*f2* B) u v)))) = monad ((*f2* B) u v)"
      by (meson Infinitesimal_add Infinitesimal_monad_eq Infinitesimal_monad_zero_iff \<open>(*f2* B) (star_of x - u) (star_of y - v) \<approx> 0\<close> \<open>(*f2* B) (star_of x) v - (*f2* B) u v \<approx> 0\<close> \<open>(*f2* B) u (star_of y) - (*f2* B) u v \<approx> 0\<close> approx_mem_monad_zero approx_sym)
    thus ?thesis
      using f1 by (simp add: approx_monad_iff ordered_field_class.sign_simps(2))
  qed
qed


lemma is_ortho_set_independent:
  \<open>0 \<notin> S \<Longrightarrow> is_ortho_set S \<Longrightarrow> complex_independent S\<close>
proof
  show False
    if "is_ortho_set S" 
      and "complex_vector.dependent S"
      and "0 \<notin> S"
  proof-
    have \<open>\<exists>t u. finite t \<and> t \<subseteq> S \<and> (\<Sum>i\<in>t. u i *\<^sub>C i) = 0 \<and> (\<exists>i\<in>t. u i \<noteq> 0)\<close>
      using complex_vector.dependent_explicit that(2)
      by blast
    then obtain t u where \<open>finite t\<close> and \<open>t \<subseteq> S\<close> and \<open>(\<Sum>i\<in>t. u i *\<^sub>C i) = 0\<close> 
      and \<open>\<exists>k\<in>t. u k \<noteq> 0\<close>
      by blast
    from \<open>\<exists>k\<in>t. u k \<noteq> 0\<close>
    obtain k where \<open>u k \<noteq> 0\<close> and \<open>k\<in>t\<close>
      by blast
    have \<open>\<langle>(\<Sum>i\<in>t. u i *\<^sub>C i), k\<rangle> = (\<Sum>i\<in>t. cnj (u i) *\<^sub>C \<langle>i,k\<rangle>)\<close>
    proof-
      have \<open>bounded_sesquilinear cinner\<close>
        by (simp add: bounded_sesquilinear_cinner)
      thus ?thesis
        using \<open>finite t\<close> sesquilinear_finite_sum
        by blast
    qed
    hence \<open>(\<Sum>i\<in>t. cnj (u i) *\<^sub>C \<langle>i,k\<rangle>) = 0\<close>
      by (simp add: \<open>(\<Sum>i\<in>t. u i *\<^sub>C i) = 0\<close>)
    moreover have \<open>(\<Sum>i\<in>t. cnj (u i) *\<^sub>C \<langle>i,k\<rangle>) = cnj (u k) *\<^sub>C \<langle>k,k\<rangle> + (\<Sum>i\<in>(t-{k}). cnj (u i) *\<^sub>C \<langle>i,k\<rangle>)\<close>
    proof-
      have \<open>t = {k} \<union> (t-{k})\<close>
        using  \<open>k \<in> t\<close>
        by auto
      moreover have \<open>{k} \<inter> (t-{k}) = {}\<close>
        by simp
      ultimately have \<open>(\<Sum>i\<in>t. cnj (u i) *\<^sub>C \<langle>i,k\<rangle>)
         = (\<Sum>i\<in>{k}. cnj (u i) *\<^sub>C \<langle>i,k\<rangle>) + (\<Sum>i\<in>(t-{k}). cnj (u i) *\<^sub>C \<langle>i,k\<rangle>)\<close>
        by (metis (no_types, lifting) Un_upper1 \<open>finite t\<close> add.commute sum.subset_diff)
      moreover have \<open> (\<Sum>i\<in>{k}. cnj (u i) *\<^sub>C \<langle>i,k\<rangle>) = cnj (u k) *\<^sub>C \<langle>k,k\<rangle>\<close>
        by simp
      ultimately show ?thesis by simp
    qed
    moreover have \<open>(\<Sum>i\<in>(t-{k}). cnj (u i) *\<^sub>C \<langle>i,k\<rangle>) = 0\<close>
    proof-
      have \<open>i \<in> t-{k} \<Longrightarrow> cnj (u i) *\<^sub>C \<langle>i,k\<rangle> = 0\<close>
        for i
      proof-
        assume \<open>i \<in> t-{k}\<close>
        hence \<open>\<langle>i,k\<rangle> = 0\<close>
          by (metis DiffD1 DiffD2 \<open>k \<in> t\<close> \<open>t \<subseteq> S\<close> in_mono is_ortho_set_def singletonI that(1))
        thus ?thesis
          by simp 
      qed
      thus ?thesis
        by (meson sum.not_neutral_contains_not_neutral) 
    qed
    ultimately have \<open>cnj (u k) *\<^sub>C \<langle>k,k\<rangle> = 0\<close>
      by simp
    moreover have \<open>\<langle>k,k\<rangle> \<noteq> 0\<close>
    proof-
      have \<open>0 \<notin> t\<close>
        using \<open>0 \<notin> S\<close> \<open>t \<subseteq> S\<close> by auto
      hence \<open>k \<noteq> 0\<close>
        using \<open>k \<in> t\<close>
        by blast
      thus ?thesis
        by simp 
    qed
    ultimately have \<open>cnj (u k) = 0\<close>
      by auto
    hence \<open>u k = 0\<close>
      by auto
    thus ?thesis using \<open>u k \<noteq> 0\<close> by blast
  qed
qed



subsection \<open>Commutative monoid of subspaces\<close>

instantiation linear_space :: (chilbert_space) comm_monoid_add begin
definition zero_linear_space :: "'a linear_space" where [simp]: "zero_linear_space = bot"
definition plus_linear_space :: "'a linear_space \<Rightarrow> _ \<Rightarrow> _" where [simp]: "plus_linear_space = sup"
instance 
  apply standard 
    apply (simp add: sup_assoc)
   apply (simp add: sup_commute)
  by simp
end


lemma Pythagorean_generalized':
  \<open>\<forall> t z r. card t = n \<and> finite t \<and> (\<forall> a a'. a \<in> t \<and> a' \<in> t \<and> a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
 \<and> z = (\<Sum>a\<in>t. r a *\<^sub>C a) \<longrightarrow> (norm z)^2 = (\<Sum>a\<in>t. norm (r a)^2 * (norm a)^2)\<close>
proof (induction n)
  case 0
  have \<open>card t = 0 \<Longrightarrow> finite t \<Longrightarrow>
       (\<forall>a a'. a \<in> t \<and> a' \<in> t \<and> a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<Longrightarrow>
       z = (\<Sum>a\<in>t. r a *\<^sub>C a) \<Longrightarrow>
       (norm z)\<^sup>2 = (\<Sum>a\<in>t. (cmod (r a))\<^sup>2 * (norm a)\<^sup>2)\<close>
    for t::\<open>'a set\<close> and z::'a and r
  proof-
    assume \<open>card t = 0\<close> and \<open>finite t\<close> and
      \<open>\<forall>a a'. a \<in> t \<and> a' \<in> t \<and> a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> and
      \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
    have \<open>t = {}\<close>
      using \<open>card t = 0\<close> \<open>finite t\<close>
      by auto
    have \<open>(norm z)\<^sup>2 = 0\<close>
      using \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by (simp add: \<open>t = {}\<close>)
    moreover have \<open>(\<Sum>a\<in>t. (cmod (r a))\<^sup>2 * (norm a)\<^sup>2) = 0\<close>
      by (simp add: \<open>t = {}\<close>)
    ultimately show ?thesis by simp
  qed
  thus ?case by blast
next
  case (Suc n)
  have \<open>card T = Suc n \<Longrightarrow> finite T \<Longrightarrow>
            \<forall>a a'. a \<in> T \<and> a' \<in> T \<and> a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0 \<Longrightarrow>
            z = (\<Sum>a\<in>T. r a *\<^sub>C a) \<Longrightarrow>
            (norm z)\<^sup>2 = (\<Sum>a\<in>T. (cmod (r a))\<^sup>2 * (norm a)\<^sup>2)\<close>
    for T::\<open>'a set\<close> and z r
  proof-
    assume \<open>card T = Suc n\<close> and \<open>finite T\<close> and
      \<open>\<forall>a a'. a \<in> T \<and> a' \<in> T \<and> a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> and
      \<open>z = (\<Sum>a\<in>T. r a *\<^sub>C a)\<close>
    have \<open>\<exists> s S. T = insert s S \<and> s \<notin> S\<close>
      using \<open>card T = Suc n\<close> card_eq_SucD by blast
    then obtain s S where \<open>T = insert s S\<close> and \<open>s \<notin> S\<close>
      by blast
    have \<open>card S = n\<close>
      using \<open>T = insert s S\<close> \<open>card T = Suc n\<close> \<open>finite T\<close> \<open>s \<notin> S\<close> 
      by auto
    have \<open>z = r s *\<^sub>C s + (\<Sum>a\<in>S. r a *\<^sub>C a)\<close>
      using \<open>T = insert s S\<close> \<open>finite T\<close> \<open>s \<notin> S\<close> \<open>z = (\<Sum>a\<in>T. r a *\<^sub>C a)\<close> 
      by auto
    hence \<open>(norm z)^2 = norm (r s *\<^sub>C s + (\<Sum>a\<in>S. r a *\<^sub>C a))^2\<close>
      by simp
    also have \<open>\<dots> = (norm (r s *\<^sub>C s))^2 + (norm (\<Sum>a\<in>S. r a *\<^sub>C a))^2\<close>
    proof-
      have \<open>\<langle>r s *\<^sub>C s, (\<Sum>a\<in>S. r a *\<^sub>C a)\<rangle> = 0\<close>
      proof-
        have \<open>\<langle>r s *\<^sub>C s, (\<Sum>a\<in>S. r a *\<^sub>C a)\<rangle> = (cnj (r s)) * \<langle>s, (\<Sum>a\<in>S. r a *\<^sub>C a)\<rangle>\<close>
          by simp
        moreover have \<open>\<langle>s, (\<Sum>a\<in>S. r a *\<^sub>C a)\<rangle> = 0\<close>
        proof-
          have \<open>\<langle>s, (\<Sum>a\<in>S. r a *\<^sub>C a)\<rangle> = (\<Sum>a\<in>S. \<langle>s,  r a *\<^sub>C a\<rangle>)\<close>
            using cinner_sum_right by blast
          also have \<open>\<dots> = (\<Sum>a\<in>S. r a * \<langle>s, a\<rangle>)\<close>
            by auto
          also have \<open>\<dots> = 0\<close>
          proof-
            have \<open>a \<in> S \<Longrightarrow> \<langle>s, a\<rangle> = 0\<close>
              for a
            proof-
              assume \<open>a \<in> S\<close>
              hence \<open>s \<noteq> a\<close>
                using \<open>s \<notin> S\<close> by blast
              thus ?thesis
                by (simp add: \<open>T = insert s S\<close> \<open>\<forall>a a'. a \<in> T \<and> a' \<in> T \<and> a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> \<open>a \<in> S\<close>) 
            qed
            thus ?thesis
              by simp 
          qed
          finally show ?thesis by blast
        qed
        ultimately show ?thesis by simp
      qed
      thus ?thesis
        using PythagoreanId by blast 
    qed
    also have \<open>\<dots> = (norm (r s *\<^sub>C s))^2 + (\<Sum>a\<in>S. (cmod (r a))\<^sup>2 * (norm a)\<^sup>2)\<close>
    proof-
      have \<open>finite S\<close>
        using \<open>T = insert s S\<close> \<open>finite T\<close> by auto        
      moreover have \<open>\<forall>a a'. a \<in> S \<and> a' \<in> S \<and> a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
        by (simp add: \<open>T = insert s S\<close> \<open>\<forall>a a'. a \<in> T \<and> a' \<in> T \<and> a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>)
      ultimately have \<open>(norm (\<Sum>a\<in>S. r a *\<^sub>C a))^2 = (\<Sum>a\<in>S. (cmod (r a))\<^sup>2 * (norm a)\<^sup>2)\<close>
        using \<open>card S = n\<close> Suc.IH by blast        
      thus ?thesis by simp
    qed
    also have \<open>\<dots> = (cmod (r s))\<^sup>2 * (norm s)\<^sup>2 + (\<Sum>a\<in>S. (cmod (r a))\<^sup>2 * (norm a)\<^sup>2)\<close>
      using power_mult_distrib by auto
    also have \<open>\<dots> = (\<Sum>a\<in>T. (cmod (r a))\<^sup>2 * (norm a)\<^sup>2)\<close>
      using \<open>T = insert s S\<close> \<open>finite T\<close> \<open>s \<notin> S\<close> by auto
    finally show ?thesis by blast
  qed
  thus ?case by simp
qed

lemma Pythagorean_generalized:
  assumes \<open>finite t\<close> and \<open>\<forall> a a'. a \<in> t \<and> a' \<in> t \<and> a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> 
    and \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
  shows  \<open>(norm z)^2 = (\<Sum>a\<in>t. norm (r a)^2 * (norm a)^2)\<close>
  using assms Pythagorean_generalized'  
  by force

hide_fact Pythagorean_generalized'

lemma projection_zero_subspace:
\<open>projection {0::'a::chilbert_space} = (\<lambda> _. 0)\<close>
proof-
  have \<open>closed_subspace {0::'a::chilbert_space}\<close>
    by simp
  hence \<open>(projection {0::'a::chilbert_space}) -` {0} = (orthogonal_complement {0::'a::chilbert_space})\<close>
    by (simp add: projectionPropertiesD)
  moreover have \<open>(orthogonal_complement {0::'a::chilbert_space}) = UNIV\<close>
    by simp
  ultimately have \<open>(projection {0::'a::chilbert_space}) -` {0} = UNIV\<close>
    by blast
  thus ?thesis by auto
qed


subsection \<open>Recovered theorems\<close>


setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniform_space \<times> 'a) filter\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::real_normed_vector \<Rightarrow> real\<close>)\<close>


lemmas tendsto_cinner [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas isCont_cinner [simp] =
  bounded_bilinear.isCont [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]

lemmas has_derivative_cinner [derivative_intros] =
  bounded_bilinear.FDERIV [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]


lemmas has_derivative_cinner_left [derivative_intros] =
  bounded_linear.has_derivative [OF bounded_csemilinear_cinner_left[THEN bounded_csemilinear.bounded_linear]]

lemma differentiable_cinner [simp]:
  "f differentiable (at x within s) \<Longrightarrow> g differentiable at x within s \<Longrightarrow> 
        (\<lambda>x. cinner (f x) (g x)) differentiable at x within s"
  unfolding differentiable_def by (blast intro: has_derivative_cinner)


(* TODO: 

lemma cGDERIV_norm:
  assumes "x \<noteq> 0" shows "cGDERIV (\<lambda>x. complex_of_real (norm x)) x :> sgn x"

lemmas has_derivative_norm = cGDERIV_norm [unfolded cgderiv_def]
*)

(* TODO (Jose): Change name, because it is more general than ell2 *)
lemma cinner_ext_0: 
  assumes "\<And>\<gamma>. \<langle>\<gamma>, \<psi>\<rangle> = 0"
  shows "\<psi> = 0"
  using assms cinner_eq_zero_iff by blast

text \<open>This is a useful rule for establishing the equality of vectors\<close>
(* TODO (Jose): Change name, because it is more general than ell2 *)
lemma cinner_ext:
  assumes \<open>\<And>\<gamma>. \<langle>\<gamma>, \<psi>\<rangle> = \<langle>\<gamma>, \<phi>\<rangle>\<close>
  shows \<open>\<psi> = \<phi>\<close>
proof-
  have \<open>\<langle>\<gamma>, \<psi> - \<phi>\<rangle> = 0\<close>
    for \<gamma>
    using \<open>\<And>\<gamma>. \<langle>\<gamma>, \<psi>\<rangle> = \<langle>\<gamma>, \<phi>\<rangle>\<close>
    by (simp add: cinner_diff_right)    
  hence \<open>\<psi> - \<phi> = 0\<close>
    using cinner_ext_0[where \<psi> = "\<psi> - \<phi>"] by blast
  thus ?thesis by simp
qed


lemma linear_space_member_inf[simp]:
  "x \<in> space_as_set (A \<sqinter> B) \<longleftrightarrow> x \<in> space_as_set A \<and> x \<in> space_as_set B"
  apply transfer by simp


lemma one_dim_to_complex_scaleC[simp]: "one_dim_to_complex (c *\<^sub>C \<psi>) = c *\<^sub>C one_dim_to_complex \<psi>"
  apply transfer
  by (metis complex_scaleC_def complex_to_one_dim_inverse of_complex_mult one_dim_to_complex_inverse scaleC_conv_of_complex)
    (* > 1s *)
  
lemma one_dim_to_complex_times[simp]: "one_dim_to_complex (\<psi> * \<phi>) = one_dim_to_complex \<psi> * one_dim_to_complex \<phi>"
  apply transfer
  by (metis of_complex_eq_iff of_complex_mult one_dim_to_complex_inverse)

end

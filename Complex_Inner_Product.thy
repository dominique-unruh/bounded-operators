(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

section \<open>\<open>Complex_Inner_Product\<close> -- Inner Product Spaces and the Gradient Derivative\<close>

theory Complex_Inner_Product
  imports 
    Complex_Vector_Spaces
    "HOL-Analysis.Infinite_Set_Sum" 
    "HOL-Analysis.Inner_Product"  
    "HOL-Types_To_Sets.Types_To_Sets"
begin

subsection \<open>Complex inner product spaces\<close>


instantiation clinear_space :: ("{complex_vector,t1_space}") zero begin
definition zero_clinear_space :: "'a clinear_space" where [simp]: "zero_clinear_space = bot"
instance ..
end


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
proof (subst cinner_commute)
  have "(\<Sum>y\<in>A. \<langle>f y, x\<rangle>) = (\<Sum>y\<in>A. \<langle>f y, x\<rangle>)" 
    by blast   
  hence "cnj (\<Sum>y\<in>A. \<langle>f y, x\<rangle>) = cnj (\<Sum>y\<in>A. \<langle>f y, x\<rangle>)"
    by simp
  hence "cnj \<langle>sum f A, x\<rangle> = (\<Sum>y\<in>A. cnj \<langle>f y, x\<rangle>)"
    by (simp add: cinner_sum_left)
  thus "cnj \<langle>sum f A, x\<rangle> = (\<Sum>y\<in>A. \<langle>x, f y\<rangle>)"
    by (subst (2) cinner_commute)    
qed

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
  by (simp add: complex_of_real_cmod power2_norm_eq_cinner)

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
  have "\<langle>x, x\<rangle> = complex_of_real (Re \<langle>x, x\<rangle>)"
    if "Im \<langle>x, x\<rangle> = 0" and "\<langle>x, x\<rangle> = Complex x1 x2"
    for x1 x2
    using that
    by (auto simp: complex_of_real_def)
  have r: "cinner x x = complex_of_real r"
    unfolding r_def
    using Im_cinner_x_x[of x]
    by (simp add: cinner_real)      
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
    have "Re \<langle>x, y\<rangle> \<le> cmod \<langle>x, y\<rangle>"
      if "\<And>x. Re x \<le> cmod x" and
        "\<And>x y. x \<le> y \<Longrightarrow> complex_of_real x \<le> complex_of_real y"
      using that by simp
    hence a1: "2 * Re \<langle>x, y\<rangle> \<le> 2 * cmod \<langle>x, y\<rangle>"
      if "\<And>x. Re x \<le> cmod x" and
        "\<And>x y. x \<le> y \<Longrightarrow> complex_of_real x \<le> complex_of_real y"
      using that by simp
    have "cinner x y + cinner y x = complex_of_real (2 * Re (cinner x y))"
      by (metis cinner_commute' complex_add_cnj)
    also have "\<dots> \<le> complex_of_real (2 * cmod (cinner x y))"
      using complex_Re_le_cmod complex_of_real_mono a1
      by blast      
    also have "\<dots> = 2 * abs (cinner x y)"
      unfolding abs_complex_def by simp
    also have "\<dots> \<le> 2 * complex_of_real (norm x) * complex_of_real (norm y)"
      using norm_cauchy_schwarz2
      by (metis add_mono_thms_linordered_semiring(1) mult.assoc mult_2) 
    finally have xyyx: "cinner x y + cinner y x \<le> complex_of_real (2 * norm x * norm y)" 
      by auto
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
      using complex_of_real_mono_iff by blast
    show "0 \<le> norm x + norm y"
      unfolding norm_eq_sqrt_cinner by simp
  qed
  show norm_scaleC: "norm (a *\<^sub>C x) = cmod a * norm x" for a
  proof (rule power2_eq_imp_eq)
    show "(norm (a *\<^sub>C x))\<^sup>2 = (cmod a * norm x)\<^sup>2"
      by (simp_all add: norm_eq_sqrt_cinner norm_mult power2_eq_square)      
    show "0 \<le> norm (a *\<^sub>C x)"
      by (simp_all add: norm_eq_sqrt_cinner)     
    show "0 \<le> cmod a * norm x"
      by (simp_all add: norm_eq_sqrt_cinner)     
  qed
  show "norm (r *\<^sub>R x) = \<bar>r\<bar> * norm x"
    unfolding scaleR_scaleC norm_scaleC by auto
qed

subsection \<open>Recovered theorems\<close>

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
  by (metis cinner_commute' cinner_divide_right complex_cnj_divide)

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
  have "\<forall>x y::'a. norm (cinner x y) \<le> norm x * norm y * 1"
    by (simp add: norm_cauchy_schwarz)
  thus "\<exists>K. \<forall>x y::'a. norm (cinner x y) \<le> norm x * norm y * K"
    by metis
qed

(* FIXME
lemmas tendsto_cinner [tendsto_intros] =
  bounded_bilinear.tendsto [OF bounded_sesquilinear_cinner[THEN bounded_sesquilinear.bounded_bilinear]]
*)

lemma tendsto_cinner0: "lim (\<lambda>n. \<langle>x n::'a, x n\<rangle>) = 0"
  if "Cauchy (x::nat \<Rightarrow> 'a)" and "Cauchy (\<lambda>n. 0::'a)" and "x \<longlonglongrightarrow> (0::'a)"
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

lemmas cbounded_linear_cinner_right =
  bounded_sesquilinear.cbounded_linear_right [OF bounded_sesquilinear_cinner]

lemmas cbounded_linear_cinner_left_comp = bounded_csemilinear_cinner_left[THEN bounded_csemilinear_compose2]
lemmas bounded_csemilinear_cinner_left_comp = bounded_csemilinear_cinner_left[THEN bounded_csemilinear_compose1]

lemmas cbounded_linear_cinner_right_comp = cbounded_linear_cinner_right[THEN cbounded_linear_compose]
lemmas bounded_csemilinear_cinner_right_comp = cbounded_linear_cinner_right[THEN bounded_csemilinear_compose3]

lemmas has_derivative_cinner_right [derivative_intros] =
  bounded_linear.has_derivative [OF cbounded_linear_cinner_right[THEN cbounded_linear.bounded_linear]]

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
  show "0 \<le> \<langle>x, x\<rangle>"
    by simp
  show "cinner x x = 0 \<longleftrightarrow> x = 0"
    unfolding cinner_complex_def by simp
  have "cmod (Complex x1 x2) = sqrt (cmod \<langle>Complex x1 x2, Complex x1 x2\<rangle>)"
    for x1 x2
    unfolding cinner_complex_def complex_cnj complex_mult complex_norm
    by (simp add: power2_eq_square)
  thus "norm x = sqrt (cmod (cinner x x))"
    by (cases x, hypsubst_thin) 
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
  have "cbounded_linear (cinner (1::'a))"
    by (rule cbounded_linear_cinner_right)
  then interpret bounded_linear "\<lambda>x::'a. cinner 1 x"
    by (rule cbounded_linear.bounded_linear)
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
proof (insert assms)
  show "cGDERIV (\<lambda>x. g (f x)) x :> dg *\<^sub>C df"
    if "cGDERIV f x :> df"
      and "(g has_field_derivative cnj dg) (at (f x))"
    unfolding cgderiv_def has_field_derivative_def cinner_scaleC_left complex_cnj_cnj
    using that
    by (simp add: cgderiv_def has_derivative_compose has_field_derivative_imp_has_derivative) 

qed

lemma cGDERIV_subst: 
  assumes a1: "cGDERIV f x :> df" and a2: "df = d"
  shows  "cGDERIV f x :> d"
  using a1 a2
  by simp

lemma cGDERIV_const: "cGDERIV (\<lambda>x. k) x :> 0"
  unfolding cgderiv_def cinner_zero_left[THEN ext] by (rule has_derivative_const)

lemma cGDERIV_add:
  assumes a1: "cGDERIV f x :> df" and a2: "cGDERIV g x :> dg"
  shows "cGDERIV (\<lambda>x. f x + g x) x :> df + dg"
  using a1 a2
  unfolding cgderiv_def cinner_add_left[THEN ext] by (rule has_derivative_add)

lemma cGDERIV_minus:
  assumes a1: "cGDERIV f x :> df"
  shows "cGDERIV (\<lambda>x. - f x) x :> - df"
  using a1
  unfolding cgderiv_def cinner_minus_left[THEN ext] by (rule has_derivative_minus)

lemma cGDERIV_diff:
  assumes a1: "cGDERIV f x :> df" and a2: "cGDERIV g x :> dg"
  shows "cGDERIV (\<lambda>x. f x - g x) x :> df - dg"
  using a1 a2
  unfolding cgderiv_def cinner_diff_left by (rule has_derivative_diff)

lemmas has_derivative_scaleC[simp, derivative_intros] =
  bounded_bilinear.FDERIV[OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]


(* Ask to Dominique
lemma cGDERIV_scaleC:
  "\<lbrakk>DERIV f x :> df; cGDERIV g x :> dg\<rbrakk>
   \<Longrightarrow> cGDERIV (\<lambda>x. scaleC (f x) (g x)) x
    :> (scaleC (cnj (f x)) dg + scaleC (cnj df) (cnj (g x)))"
  unfolding cgderiv_def has_field_derivative_def cinner_add_left cinner_scaleC_left
  apply (rule has_derivative_subst)
   apply (erule (1) has_derivative_scaleC)
  by (simp add: ac_simps)
*)

(* TODO: finish converting this proof to Isar style *)
lemma cGDERIV_mult:
  assumes "cGDERIV f x :> df"
  assumes "cGDERIV g x :> dg"
  shows "cGDERIV (\<lambda>x. f x * g x) x :> cnj (f x) *\<^sub>C dg + cnj (g x) *\<^sub>C df"
proof -

  have 1: "f x * \<langle>dg, h\<rangle> + \<langle>df, h\<rangle> * g x = cinner (cnj (f x) *\<^sub>C dg + cnj (g x) *\<^sub>C df) h" for h
    unfolding cinner_add
    unfolding cinner_scaleC_left[THEN ext]
    by (simp add: cinner_add ac_simps)

  show ?thesis
    using assms apply -
    unfolding cgderiv_def
    apply (rule has_derivative_subst[where df="(\<lambda>h. f x * \<langle>dg, h\<rangle> + \<langle>df, h\<rangle> * g x)"])
     apply (erule (1) has_derivative_mult)
    by (simp add: 1)
qed

lemma cGDERIV_inverse:
  assumes a1: "cGDERIV f x :> df" and a2: "f x \<noteq> 0"
  shows "cGDERIV (\<lambda>x. inverse (f x)) x :> cnj (- (inverse (f x))\<^sup>2) *\<^sub>C df"
proof-
  have "(inverse has_field_derivative - (inverse (f x))\<^sup>2) (at (f x))"
    if "f x \<noteq> 0"
    using that  DERIV_inverse [folded numeral_2_eq_2]
    by blast
  thus ?thesis
    using cGDERIV_DERIV_compose
    by (metis a1 a2 complex_cnj_cnj)
qed


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
  have \<open>\<langle>x , y\<rangle> + \<langle>y , x\<rangle> = \<langle>x , y\<rangle> + cnj \<langle>x , y\<rangle>\<close>
    by simp
  hence \<open>\<langle>x , y\<rangle> + \<langle>y , x\<rangle> = 2 * Re \<langle>x , y\<rangle> \<close>
    using complex_add_cnj by presburger
  have \<open>\<parallel>x + y\<parallel>^2 = \<langle>x+y, x+y\<rangle>\<close> 
    using power2_norm_eq_cinner' by auto
  hence \<open>\<parallel>x + y\<parallel>^2 = \<langle>x , x\<rangle> + \<langle>x , y\<rangle> + \<langle>y , x\<rangle> + \<langle>y , y\<rangle>\<close>
    by (simp add: cinner_left_distrib cinner_right_distrib)
  thus ?thesis using  \<open>\<langle>x , y\<rangle> + \<langle>y , x\<rangle> = 2 * Re \<langle>x , y\<rangle>\<close>
    by (smt Re_complex_of_real cinner_norm_sq plus_complex.simps(1))
qed

lemma polarization_identity_minus:
  includes notation_norm 
  shows \<open>\<parallel>x - y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 - 2 * Re \<langle>x, y\<rangle>\<close>
proof-
  have \<open>\<parallel>x + (-y)\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>-y\<parallel>^2 + 2 * Re \<langle>x , (-y)\<rangle>\<close>
    using polarization_identity_plus by blast
  hence \<open>\<parallel>x - y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 - 2*Re \<langle>x , y\<rangle>\<close>
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
  have  \<open>\<langle> y, x \<rangle> = 0\<close>
    if "x \<in> M"
    for x
  proof-
    have \<open>\<langle> x, y \<rangle> = 0\<close> 
      using that
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
  \<open>is_orthogonal x y \<equiv> \<langle> x, y \<rangle> = 0\<close>

bundle orthogonal_notation begin
notation is_orthogonal (infixl "\<bottom>" 69)
end

bundle no_orthogonal_notation begin
no_notation is_orthogonal (infixl "\<bottom>" 69)
end


lemma orthogonal_comm: "is_orthogonal \<psi>  \<phi> = is_orthogonal \<phi> \<psi>"
  by (metis is_orthogonal_def mem_Collect_eq orthogonal_complement_D2 orthogonal_complement_I2)

lemma subspace_orthog[simp]: 
  "closed_subspace (orthogonal_complement A)"
  if "closed_subspace A"
  for A :: \<open>('a::complex_inner) set\<close>
proof-
  have c1: "l \<in> orthogonal_complement A"
    if "\<forall>n::nat. x n \<in> orthogonal_complement A" and "x \<longlonglongrightarrow> l"
    for x::\<open>nat \<Rightarrow> 'a::complex_inner\<close> and l::"'a::complex_inner"
  proof-
    have b1: \<open>cbounded_linear (\<lambda> x. \<langle> y , x \<rangle>)\<close> 
      for y::'a
      by (simp add: cbounded_linear_cinner_right)
    have \<open>\<forall> y \<in> A. \<forall> n. \<langle> y , x n \<rangle> = 0\<close>
      using orthogonal_complement_D2
      by (simp add: orthogonal_complement_D2 that(1))
    moreover have \<open>isCont (\<lambda> x. \<langle> y , x \<rangle>) l\<close> for y
      using b1 bounded_linear_continuous
      by (simp add: bounded_linear_continuous cbounded_linear_cinner_right)
    ultimately have \<open>(\<lambda> n. (\<lambda> v. \<langle> y , v \<rangle>) (x n)) \<longlonglongrightarrow> (\<lambda> v. \<langle> y , v \<rangle>) l\<close> for y
      using isCont_tendsto_compose
      by (simp add: isCont_tendsto_compose that(2))
    hence  \<open>\<forall> y\<in>A. (\<lambda> n. \<langle> y , x n \<rangle>  ) \<longlonglongrightarrow>  \<langle> y , l \<rangle>\<close>
      by simp
    hence  \<open>\<forall> y\<in>A. (\<lambda> n. 0  ) \<longlonglongrightarrow>  \<langle> y , l \<rangle>\<close> 
      using \<open>\<forall> y \<in> A. \<forall> n. \<langle> y , x n \<rangle> = 0\<close> 
      by fastforce
    hence  \<open>\<forall> y \<in> A. \<langle> y , l \<rangle> = 0\<close> 
      using limI by fastforce
    thus ?thesis
      by (simp add: orthogonal_complement_I1)         
  qed

  have "x+y\<in>(orthogonal_complement A)"
    if a1: "x\<in>(orthogonal_complement A)" and a2: "y\<in>(orthogonal_complement A)"
    for x y
  proof-
    have  \<open>\<forall> z \<in> A. \<langle>z, y\<rangle> = 0\<close> 
      using a2
      by (simp add: orthogonal_complement_D2) 
    moreover have   \<open>\<forall> z \<in> A. \<langle>z, x\<rangle> = 0\<close>
      using  \<open>x\<in>(orthogonal_complement A)\<close>
      by (simp add: orthogonal_complement_D2)     
    ultimately have \<open>\<forall> z \<in> A. \<langle>z, x\<rangle> +  \<langle>z, y\<rangle> = 0\<close>
      by simp
    hence  \<open>\<forall> z \<in> A. \<langle> z , x + y \<rangle> = 0\<close> 
      by (simp add: cinner_right_distrib)
    thus ?thesis
      by (simp add: orthogonal_complement_I1)       
  qed
  moreover have "c *\<^sub>C x \<in> (orthogonal_complement A)" 
    if "x\<in>(orthogonal_complement A)"
    for x c
  proof-
    have \<open>\<forall> y \<in> A. \<langle> y , x \<rangle> = 0\<close>
      using that
      by (simp add: orthogonal_complement_D2)
    hence \<open>\<forall> y \<in> A. c * \<langle> y , x \<rangle> = 0\<close>
      by simp
    hence \<open>\<forall> y \<in> A. \<langle> y , c *\<^sub>C x \<rangle> = 0\<close>
      by simp
    thus ?thesis
      using orthogonal_complement_I1 by blast 
  qed
  moreover have  "closed (orthogonal_complement A)"
    using closed_sequential_limits c1 by blast
  moreover have  "0 \<in> orthogonal_complement A"
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
  fixes M :: \<open>'a::chilbert_space set\<close>  
  assumes q1: \<open>convex M\<close> and q2: \<open>closed M\<close> and q3: \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>! k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) k\<close>
proof-
  define d where \<open>d = Inf { \<parallel>x\<parallel>^2 | x. x \<in> M }\<close>    
  have w4: \<open>{ \<parallel>x\<parallel>^2 | x. x \<in> M } \<noteq> {}\<close>
    by (simp add: assms(3))
  have \<open>\<forall> x. \<parallel>x\<parallel>^2 \<ge> 0\<close>
    by simp
  hence bdd_below1: \<open>bdd_below { \<parallel>x\<parallel>^2 | x. x \<in> M }\<close>
    by fastforce    
  have \<open>d \<le> \<parallel>x\<parallel>^2\<close> 
    if a1: "x \<in> M"
    for x
  proof-
    have "\<forall>v. (\<exists>w. Re (\<langle>v , v\<rangle> ) = \<parallel>w\<parallel>\<^sup>2 \<and> w \<in> M) \<or> v \<notin> M"
      by (metis (no_types) Re_complex_of_real power2_norm_eq_cinner')
    hence "Re (\<langle>x , x\<rangle> ) \<in> {\<parallel>v\<parallel>\<^sup>2 |v. v \<in> M}"
      using a1 by blast
    thus ?thesis
      unfolding d_def
      by (metis (lifting) Re_complex_of_real bdd_below1 cInf_lower power2_norm_eq_cinner')
  qed

  have \<open>\<forall> \<epsilon> > 0. \<exists> t \<in> { \<parallel>x\<parallel>^2 | x. x \<in> M }.  t < d + \<epsilon>\<close>
    unfolding d_def
    using w4  bdd_below1
    by (meson cInf_lessD less_add_same_cancel1)
  hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + \<epsilon>\<close>
    by auto    
  hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + \<epsilon>\<close>
    by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close>)
  hence w1: \<open>\<forall> n::nat. \<exists> x \<in> M.  \<parallel>x\<parallel>^2 < d + 1/(n+1)\<close> by auto

  then obtain r::\<open>nat \<Rightarrow> 'a\<close> where w2: \<open>\<forall> n. r n \<in> M \<and>  \<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
    by metis
  have w3: \<open>\<forall> n. r n \<in> M\<close> 
    by (simp add: w2)
  have \<open>\<forall> n. \<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
    by (simp add: w2)    
  have w5: \<open>\<parallel> (r n) - (r m) \<parallel>^2 < 2*(1/(n+1) + 1/(m+1))\<close> 
    for m n 
  proof-
    have w6: \<open>\<parallel> r n \<parallel>^2 < d + 1/(n+1)\<close>
      by (metis w2  of_nat_1 of_nat_add)
    have \<open> \<parallel> r m \<parallel>^2 < d + 1/(m+1)\<close>
      by (metis w2 of_nat_1 of_nat_add)
    have \<open>(r n) \<in> M\<close>
      by (simp add: \<open>\<forall>n. r n \<in> M\<close>) 
    moreover have \<open>(r m) \<in> M\<close> 
      by (simp add: \<open>\<forall>n. r n \<in> M\<close>)
    ultimately have \<open>(1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<in> M\<close>
      using \<open>convex M\<close> 
      by (simp add: convexD)
    hence \<open>\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2 \<ge> d\<close>
      by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> \<parallel>x\<parallel>\<^sup>2\<close>)
    have \<open>\<parallel> (1/2) *\<^sub>R (r n) - (1/2) *\<^sub>R (r m) \<parallel>^2
              = (1/2)*( \<parallel> r n \<parallel>^2 + \<parallel> r m \<parallel>^2 ) - \<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>^2\<close> 
      using ParallelogramLawVersion1 
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
  hence "\<exists> N. \<forall> n m. n \<ge> N \<and> m \<ge> N \<longrightarrow> \<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2"
    if "\<epsilon> > 0" 
    for \<epsilon>
  proof-
    obtain N::nat where \<open>1/(N + 1) < \<epsilon>^2/4\<close>
      using LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1]
      by (metis Suc_eq_plus1 \<open>0 < \<epsilon>\<close> nat_approx_posE zero_less_divide_iff zero_less_numeral 
          zero_less_power )
    hence \<open>4/(N + 1) < \<epsilon>^2\<close>
      by simp
    have "2*(1/(n+1) + 1/(m+1)) < \<epsilon>^2"
      if f1: "n \<ge> N" and f2: "m \<ge> N" 
      for m n::nat
    proof-
      have \<open>1/(n+1) \<le> 1/(N+1)\<close> 
        by (simp add: f1 linordered_field_class.frac_le)
      moreover have \<open>1/(m+1) \<le> 1/(N+1)\<close> 
        by (simp add: f2 linordered_field_class.frac_le)
      ultimately have  \<open>2*(1/(n+1) + 1/(m+1)) \<le> 4/(N+1)\<close>
        by simp
      thus ?thesis using \<open>4/(N + 1) < \<epsilon>^2\<close> 
        by linarith
    qed
    hence "\<parallel> (r n) - (r m) \<parallel>^2 < \<epsilon>^2"
      if y1: "n \<ge> N" and y2: "m \<ge> N" 
      for m n::nat
      using that
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
  hence q1: \<open>\<exists> k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>^2) (\<lambda> t. t \<in> M) k\<close> 
    using \<open>k \<in> M\<close>
      is_arg_min_def \<open>d = \<parallel>k\<parallel>\<^sup>2\<close>
    by smt
  hence r1: \<open>\<exists> k. is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) k\<close> 
    by (smt is_arg_min_def norm_ge_zero power2_eq_square power2_le_imp_le)
  have rs: "r = s"
    if y1: "is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r" and y2: "is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s"
    for r s
  proof-
    have u1: \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2
      = (1/2)*( \<parallel>r\<parallel>^2 + \<parallel>s\<parallel>^2 ) - \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>^2\<close> 
      using  ParallelogramLawVersion1 
      by (simp add: ParallelogramLawVersion1 scaleR_scaleC)

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
    hence u2: \<open>\<parallel>r\<parallel>^2 \<le> \<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>^2\<close>
      using norm_ge_zero power_mono by blast

    have \<open>\<parallel>r\<parallel> \<le> \<parallel>s\<parallel>\<close> 
      using  \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r\<close> \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s\<close>  is_arg_min_def
    proof -
      have f1: "\<forall>x0. (0 \<le> - 1 * \<parallel>r\<parallel> + \<parallel>x0::'a\<parallel>) = (\<parallel>r\<parallel> + - 1 * \<parallel>x0\<parallel> \<le> 0)"
        by auto
      have f2: "\<forall>x0. \<parallel>x0::'a\<parallel> + - 1 * \<parallel>r\<parallel> = - 1 * \<parallel>r\<parallel> + \<parallel>x0\<parallel>"
        by auto
      have "\<forall>x0 x1 x3. (x3 (x0::'a) < x3 x1) = (\<not> (0::real) \<le> x3 x0 + - 1 * x3 x1)"
        by force
      hence "\<parallel>r\<parallel> + - 1 * \<parallel>s\<parallel> \<le> 0"
        using f2 f1 by (metis (no_types) \<open>is_arg_min norm (\<lambda>t. t \<in> M) r\<close> \<open>is_arg_min norm (\<lambda>t. t \<in> M) s\<close> is_arg_min_def)
      thus ?thesis
        by linarith
    qed         
    moreover have \<open>\<parallel>s\<parallel> \<le> \<parallel>r\<parallel>\<close>
      using  \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) r\<close> \<open>is_arg_min (\<lambda>x. \<parallel>x\<parallel>) (\<lambda> t. t \<in> M) s\<close>  is_arg_min_def 
      by smt
    ultimately have u3: \<open>\<parallel>r\<parallel> = \<parallel>s\<parallel>\<close> by simp      

    have \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2 \<le> 0\<close>
      using u1 u2 u3
      by simp
    hence \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>^2 = 0\<close>
      by simp
    hence \<open>\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel> = 0\<close>
      by auto
    hence \<open>(1/2) *\<^sub>R r - (1/2) *\<^sub>R s = 0\<close>
      using norm_eq_zero by blast
    thus ?thesis by simp
  qed
  show ?thesis
    using r1 rs by blast     
qed

lemma TransClosed:
  assumes t1:  \<open>closed (S::('a::{topological_ab_group_add,t2_space,first_countable_topology}) set)\<close>
  shows "closed {s + h| s. s \<in> S}"
proof-
  have \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. r n \<in> S) \<longrightarrow> lim r \<in> S\<close>
    using closed_sequentially convergent_LIMSEQ_iff t1 by blast
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. r n \<in>  {s | s. s \<in> S}) 
          \<longrightarrow> lim (\<lambda> n. (r n)) \<in>  {s | s. s \<in> S}\<close>
    by simp
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n) \<in>  {s | s. s \<in> S}) 
          \<longrightarrow> lim (\<lambda> n. (r n))+h \<in>  {s+h | s. s \<in> S}\<close>
    by blast
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) 
            \<longrightarrow> lim (\<lambda> n. (r n))+h \<in>  {s+h | s. s \<in> S}\<close>
    by simp
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) 
            \<longrightarrow> lim (\<lambda> n. (r n))+lim (\<lambda> n. h) \<in>  {s+h | s. s \<in> S}\<close>
    by auto
  have \<open>(lim r) + h = lim (\<lambda> n. (r n)+h)\<close> 
    if r1: \<open>convergent r\<close>    
    for r::\<open>nat \<Rightarrow> 'a\<close>
  proof-
    obtain R where \<open>r \<longlonglongrightarrow> R\<close>
      using convergent_def r1 by auto
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
  have \<open>\<exists>s. lim t = s + h \<and> s \<in> S \<close> 
    if t1: \<open>\<forall>r. convergent (\<lambda>n. r n + h) \<and> (\<forall>n. r n \<in> S) \<longrightarrow> (\<exists>s. lim (\<lambda>n. r n + h) = s + h \<and> s \<in> S) \<close>
      and t2: \<open>convergent t\<close> and t3: \<open>\<forall>n. \<exists>s. t n = s + h \<and> s \<in> S\<close>
    for t
  proof-
    obtain r::\<open>nat \<Rightarrow> 'a\<close> where \<open>\<forall>n. t n = (r n) + h \<and> r n \<in> S\<close> using  \<open>\<forall>n. \<exists>s. t n = s + h \<and> s \<in> S\<close>
      by metis
    from  \<open>\<forall>n. t n = (r n) + h \<and> r n \<in> S\<close>
    have  \<open>\<forall>n. t n = (r n) + h\<close> by simp
    from  \<open>\<forall>n. t n = (r n) + h \<and> r n \<in> S\<close>
    have  \<open>\<forall>n. r n \<in> S\<close> by simp
    have \<open>convergent (\<lambda>n. t n) \<close>
      by (simp add: t2) 
    hence \<open>convergent (\<lambda>n. (r n) + h)\<close> using   \<open>\<forall>n. t n = (r n) + h\<close> 
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
  fixes M::\<open>'a::chilbert_space set\<close> and h 
  assumes a1: \<open>convex M\<close> and a2: \<open>closed M\<close> and a3: \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>! k. is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k\<close>
proof-
  include notation_norm 
  have t6: \<open>closed {m + (- h)| m. m \<in> M}\<close>
    using  a2 TransClosed by blast
  hence t1: \<open>closed {m - h| m. m \<in> M}\<close> by simp
  have t5: \<open>{m - h| m. m \<in> M} \<noteq> {}\<close>
    by (simp add: a3)  
  have t4: \<open>convex ((\<lambda>x. -h + x) ` M)\<close>
    using convex_translation \<open>convex M\<close> by blast
  hence t3: \<open>convex ((\<lambda>x.  x - h) ` M)\<close> by simp
  moreover have t7: \<open>{(\<lambda>x.  x - h) m | m. m \<in> M} = ((\<lambda>x.  x - h) ` M)\<close>
    by auto
  ultimately have t2: \<open>convex {m - h| m. m \<in> M}\<close> by simp
  have v2: \<open>\<exists>! k. is_arg_min norm (\<lambda> x. x \<in> {m - h| m. m \<in> M}) k\<close>
    using ExistenceUniquenessMinNorm
    by (metis t7 t1 t3 t5)
  obtain k where v6: \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h| m. m \<in> M}) k\<close>
    using  v2 by blast
  have v7: \<open>(\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k\<parallel> \<le> \<parallel>t\<parallel>) \<and> k \<in> {m - h |m. m \<in> M}\<close>
    using is_arg_min_def  v6
    by smt
  hence \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k\<parallel> \<le> \<parallel>t\<parallel>\<close>
    by blast
  hence \<open>\<forall>t. t + h \<in> M \<longrightarrow> \<parallel>k\<parallel> \<le> \<parallel>t\<parallel>\<close>
    by auto
  hence \<open>\<forall>t. t \<in> M \<longrightarrow> \<parallel>k\<parallel> \<le> \<parallel>t - h\<parallel>\<close>
    by auto
  hence \<open>\<forall>t. t \<in> M \<longrightarrow> \<parallel>(k+h)-h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>
    by auto
  have  \<open>k \<in> {m - h |m. m \<in> M}\<close>
    using v7
    by blast
  hence  \<open>k + h \<in> M\<close>
    by auto
  have \<open>\<nexists>y. y \<in> {m |m. m \<in> M} \<and> \<parallel>y - h\<parallel> < \<parallel>(k + h) - h\<parallel>\<close>
    using \<open>\<forall>t. t \<in> M \<longrightarrow> \<parallel>(k+h)-h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>  
    by auto
  hence \<open>is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> {m| m. m \<in> M}) (k + h)\<close>
    using \<open>k + h \<in> M\<close>
    by (simp add: is_arg_min_def)
  hence q1: \<open>\<exists> k. is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k\<close>
    by auto 
  have g1: "is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)"
    if x1: \<open>is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k\<close> 
    for k
  proof-
    have \<open>\<forall>t. t \<in> M \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>
      using x1
      by (meson is_arg_min_linorder)
    hence \<open>\<forall>t. t - h \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t - h\<parallel>\<close>
      by auto
    hence s1: \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> \<parallel>k - h\<parallel> \<le> \<parallel>t\<parallel>\<close>
      by blast
    have \<open>k \<in> M\<close>
      using  \<open>is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k\<close> is_arg_min_def
      by (simp add: is_arg_min_linorder)
    hence \<open>k - h \<in> {m - h |m. m \<in> M}\<close>
      by auto
    hence  \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)\<close>
      using  s1 is_arg_min_def
      by smt
    thus ?thesis by blast
  qed
  have v1: \<open>k = t\<close> 
    if x1: "is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k"
      and x2: "is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) t"
    for k t
  proof-   
    have v3: \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)\<close>
      using x1  \<open>\<And>k. is_arg_min (\<lambda>x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k \<Longrightarrow> is_arg_min norm (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)\<close>
      by blast
    have v4: \<open>is_arg_min (\<lambda> x. \<parallel>x\<parallel>) (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (t - h)\<close>
      using x2 \<open>\<And>k. is_arg_min (\<lambda>x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k \<Longrightarrow> is_arg_min norm (\<lambda> x. x \<in> {m - h |m. m \<in> M}) (k - h)\<close> by auto
    show ?thesis 
      using v2 v3 v4 diff_add_cancel
      by (metis (no_types, lifting))
  qed
  have \<open>\<exists>! k. is_arg_min (\<lambda> x. \<parallel>x - h\<parallel>) (\<lambda> x. x \<in> M) k\<close>
    using v1 q1 by blast    
  moreover have \<open>(\<lambda> x. dist x h) = (\<lambda> x. \<parallel>x - h\<parallel>)\<close>
    by (simp add: dist_norm)
  ultimately show ?thesis by auto
qed


\<comment> \<open>Theorem 2.6 in @{cite conway2013course}\<close> 
theorem dist_min_ortho:
  fixes M::\<open>'a::complex_inner set\<close> and h k::'a 
  assumes b1: \<open>closed_subspace M\<close>
  shows  \<open>(is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k) \<longleftrightarrow> 
          h - k \<in> (orthogonal_complement M) \<and> k \<in> M\<close>
proof-
  include notation_norm
  have  \<open>complex_vector.subspace M\<close>
    using \<open>closed_subspace M\<close> unfolding closed_subspace_def by blast
  have r1: \<open>2 * Re (\<langle> h - k , f \<rangle>) \<le> \<parallel> f \<parallel>^2\<close>
    if "f \<in> M" and \<open>k \<in> M\<close> and \<open>is_arg_min (\<lambda>x. dist x h) (\<lambda> x. x \<in> M) k\<close>
    for f
  proof-
    have \<open>k + f \<in>  M\<close> 
      using \<open>complex_vector.subspace M\<close>
      by (simp add:complex_vector.subspace_add that)
    have "\<forall>f A a b. \<not> is_arg_min f (\<lambda> x. x \<in> A) (a::'a) \<or> (f a::real) \<le> f b \<or> b \<notin> A"
      by (metis (no_types) is_arg_min_linorder)
    hence "dist k h \<le> dist (f + k) h"
      by (metis \<open>is_arg_min (\<lambda>x. dist x h) (\<lambda> x. x \<in> M) k\<close> \<open>k + f \<in> M\<close> add.commute)
    hence \<open>dist h k \<le> dist  h (k + f)\<close>
      by (simp add: add.commute dist_commute)
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

  have q4: \<open>\<forall> c > 0.  2 * Re (\<langle> h - k , f \<rangle>) \<le> c\<close>
    if  \<open>\<forall>c>0. 2 * Re (\<langle>h - k , f\<rangle> ) \<le> c * \<parallel>f\<parallel>\<^sup>2\<close>
    for f
  proof (cases \<open>\<parallel> f \<parallel>^2 > 0\<close>)
    case True
    hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k , f \<rangle>) \<le> (c/\<parallel> f \<parallel>^2)*\<parallel> f \<parallel>^2\<close>
      using that linordered_field_class.divide_pos_pos by blast
    thus ?thesis 
      using True by auto
  next
    case False
    hence \<open>\<parallel> f \<parallel>^2 = 0\<close> 
      by simp
    thus ?thesis 
      by auto
  qed
  have q3: \<open>\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> 0\<close> 
    if a3: \<open>\<forall>f. f \<in> M \<longrightarrow> (\<forall>c>0. 2 * Re \<langle>h - k , f\<rangle> \<le> c * \<parallel>f\<parallel>\<^sup>2)\<close>
      and a2: "f \<in>  M"
      and a1: "is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k"
    for f
  proof-
    have \<open>\<forall> c > 0.  2 * Re (\<langle> h - k , f \<rangle>) \<le> c*\<parallel> f \<parallel>^2\<close>
      by (simp add: that )    
    thus ?thesis 
      using q4 by smt
  qed
  have w2: "h - k \<in> orthogonal_complement M \<and> k \<in> M"
    if a1: "is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k"
  proof-
    have  \<open>k \<in> M\<close>
      using is_arg_min_def that by fastforce    
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> \<parallel> f \<parallel>^2\<close>
      using r1
      by (simp add: that) 
    have \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real.  2 * Re (\<langle> h - k , c *\<^sub>R f \<rangle>) \<le> \<parallel> c *\<^sub>R f \<parallel>^2)\<close>
      using  assms scaleR_scaleC complex_vector.subspace_def \<open>complex_vector.subspace M\<close>
      by (metis \<open>\<forall>f. f \<in> M \<longrightarrow> 2 * Re \<langle>h - k, f\<rangle> \<le> \<parallel>f\<parallel>\<^sup>2\<close>)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (\<langle> h - k , f \<rangle>)) \<le> \<parallel> c *\<^sub>R f \<parallel>^2)\<close>
      by (metis Re_complex_of_real cinner_scaleC_right complex_add_cnj complex_cnj_complex_of_real
          complex_cnj_mult of_real_mult scaleR_scaleC semiring_normalization_rules(34))
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
    hence  q4: \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> c*\<parallel> f \<parallel>^2)\<close>
      by simp     
    have  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) \<le> 0)\<close>
      using q3
      by (simp add: q4 that)      
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

    have \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                 ((1::real) > 0 \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) = 0)\<close>
      using \<open>\<forall>f. f \<in>  M \<longrightarrow> (\<forall>c>0. 2 * Re (\<langle>h - k , f\<rangle> ) = 0)\<close> by blast
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (\<langle> h - k , f \<rangle>) = 0\<close>
      by simp
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (\<langle> h - k , f \<rangle>) = 0\<close> 
      by simp     
    have  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (\<langle> h - k , (Complex 0 (-1)) *\<^sub>C f \<rangle>) = 0\<close>
      using assms  complex_vector.subspace_def \<open>complex_vector.subspace M\<close>
      by (metis \<open>\<forall>f. f \<in> M \<longrightarrow> Re \<langle>h - k, f\<rangle> = 0\<close>)
    hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re ( (Complex 0 (-1))*(\<langle> h - k , f \<rangle>) ) = 0\<close>
      by simp
    hence \<open>\<forall> f. f \<in>  M \<longrightarrow> Im (\<langle> h - k , f \<rangle>) = 0\<close> 
      using Complex_eq_neg_1 Re_i_times cinner_scaleC_right complex_of_real_def by auto        

    have \<open>\<forall> f. f \<in>  M \<longrightarrow> (\<langle> h - k , f \<rangle>) = 0\<close>
      using complex_eq_iff
      by (simp add: \<open>\<forall>f. f \<in> M \<longrightarrow> Im \<langle>h - k, f\<rangle> = 0\<close> \<open>\<forall>f. f \<in> M \<longrightarrow> Re \<langle>h - k, f\<rangle> = 0\<close>)
    hence \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
      by (simp add: \<open>k \<in> M\<close> orthogonal_complement_I2) 
    have  \<open>\<forall> c. c *\<^sub>R f \<in> M\<close>
      if "f \<in> M"
      for f
      using that scaleR_scaleC  \<open>complex_vector.subspace M\<close> complex_vector.subspace_def
      by (simp add: complex_vector.subspace_def scaleR_scaleC)
    have \<open>\<langle> h - k , f \<rangle> = 0\<close> 
      if "f \<in> M"
      for f
      using \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close> orthogonal_complement_D1 that by auto
    hence \<open>h - k \<in> orthogonal_complement M\<close> 
      by (simp add: is_orthogonal_def orthogonal_complement_def)
    thus ?thesis
      using \<open>k \<in> M\<close> by auto       
  qed

  have q1: \<open>dist h k \<le> dist h f \<close> 
    if "f \<in> M" and  \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
    for f
  proof-
    have \<open>\<langle> h - k,  k - f \<rangle> = 0\<close>
      by (metis (no_types, lifting) that 
          cinner_diff_right diff_0_right orthogonal_complement_D1 that)
    have \<open>\<parallel> h - f \<parallel>^2 = \<parallel> (h - k) + (k - f) \<parallel>^2\<close>
      by simp
    also have \<open>... = \<parallel> h - k \<parallel>^2 + \<parallel> k - f \<parallel>^2\<close>
      using  \<open>\<langle> h - k, k - f \<rangle> = 0\<close> PythagoreanId  is_orthogonal_def by blast
    also have \<open>... \<ge> \<parallel> h - k \<parallel>^2\<close>
      by simp
    finally have \<open>\<parallel>h - k\<parallel>\<^sup>2 \<le> \<parallel>h - f\<parallel>\<^sup>2 \<close>
      by blast
    hence \<open>\<parallel>h - k\<parallel> \<le> \<parallel>h - f\<parallel>\<close>
      using norm_ge_zero power2_le_imp_le by blast
    thus ?thesis 
      by (simp add: dist_norm)
  qed

  have  w1: "is_arg_min (\<lambda> x. dist x h) (\<lambda> x. x \<in> M) k"
    if "h - k \<in> orthogonal_complement M \<and> k \<in>  M"
  proof-
    have \<open>h - k \<in> orthogonal_complement M\<close>
      using that by blast
    have \<open>k \<in> M\<close> using \<open>h - k \<in> orthogonal_complement M \<and> k \<in>  M\<close>
      by blast   
    thus ?thesis
      by (metis (no_types, lifting) dist_commute is_arg_min_linorder q1 that) 
  qed
  show ?thesis
    using w1 w2 by blast 
qed


lemma linear_manifold_Convex:
  assumes a1: "complex_vector.subspace M"
  shows "convex M"
proof-
  have \<open>\<forall>x\<in>M. \<forall>y\<in> M. \<forall>u. \<forall>v. u *\<^sub>C x + v *\<^sub>C y \<in>  M\<close>
    using a1
    by (simp add:  complex_vector.subspace_def)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u::real. \<forall>v::real. u *\<^sub>R x + v *\<^sub>R y \<in> M\<close>
    by (simp add: scaleR_scaleC)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in>M\<close>
    by blast
  thus ?thesis using convex_def by blast
qed

lemma SubspaceConvex:
  assumes a1: "closed_subspace M"
  shows "convex M"
  using linear_manifold_Convex a1
  unfolding closed_subspace_def
  by blast

corollary ExistenceUniquenessProj:
  fixes M :: \<open>'a::chilbert_space set\<close> 
  assumes \<open>closed_subspace M\<close>
  shows  \<open>\<forall>h. \<exists>!k. h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
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
    by (simp add: assms dist_min_ortho)  
qed


definition is_projection_on::\<open>('a \<Rightarrow> 'a) \<Rightarrow> ('a::complex_inner) set \<Rightarrow> bool\<close> where
  \<open>is_projection_on \<pi> M \<longleftrightarrow> (\<forall>h. h - \<pi> h \<in> orthogonal_complement M \<and> \<pi> h \<in> M)\<close>


lemma is_projection_on_existence:
  assumes a1: \<open>closed_subspace (M::'a::chilbert_space set)\<close>
  shows "\<exists>\<pi>. is_projection_on \<pi> M"
  unfolding is_projection_on_def
  using a1 ExistenceUniquenessProj
  by metis

definition projection :: \<open>'a::complex_inner set \<Rightarrow> ('a::complex_inner \<Rightarrow> 'a)\<close> where
  \<open>projection M \<equiv> SOME \<pi>. is_projection_on \<pi> M\<close>

lemma projection_intro1':
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: \<open>is_projection_on \<pi> M\<close>
  shows "h - \<pi> h \<in> orthogonal_complement M"
  using a1 is_projection_on_def by blast

lemma projection_intro1:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes a1: "closed_subspace M"
  shows "h - projection M h \<in> orthogonal_complement M"
  using a1 is_projection_on_existence  projection_intro1'
  by (metis projection_def someI_ex) 

lemma projection_intro2':
  assumes a1: "is_projection_on \<pi> M"
  shows "\<pi> h \<in> M"
  using a1
  by (simp add: is_projection_on_def)

lemma projection_intro2:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes a1: "closed_subspace M"
  shows "projection M h \<in> M"
  using a1 is_projection_on_existence  projection_intro2'
  by (metis projection_def someI_ex) 

lemma projection_uniq':
  fixes  M :: \<open>'a::complex_inner set\<close>
  assumes a1: \<open>closed_subspace M\<close> and a2: \<open>h - x \<in> orthogonal_complement M\<close> and a3: \<open>x \<in> M\<close> 
    and a4: \<open>is_projection_on \<pi> M\<close>
  shows \<open>\<pi> h = x\<close>
proof-
  have t6: \<open>h - \<pi> h \<in> orthogonal_complement M \<and> \<pi> h \<in> M\<close>
    using a4
    unfolding is_projection_on_def
    by blast
  hence t1: \<open>\<pi> h \<in> M\<close> 
    by blast
  have t3: \<open>h - \<pi> h \<in> orthogonal_complement M\<close>
    using t6 by blast
  have t5: \<open>x - \<pi> h \<in> M\<close>
    using a1 t1 a3
    unfolding closed_subspace_def
    by (simp add: complex_vector.subspace_diff)
  have t2: \<open>closed_subspace (orthogonal_complement M)\<close>
    by (simp add: a1)
  have  \<open>(h - \<pi> h) - (h - x) \<in> orthogonal_complement M\<close>
    using complex_vector.subspace_diff closed_subspace_def
    using t2 t3 a2 
    by blast 
  hence \<open>x - \<pi> h \<in> orthogonal_complement M\<close> 
    by simp 
  hence \<open>x - \<pi> h \<in> M \<inter> (orthogonal_complement M)\<close>
    using t5 by auto    
  moreover have \<open>M \<inter> (orthogonal_complement M) = {0}\<close>
    using a1 a3  ortho_inter_zero
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
  by (smt ExistenceUniquenessProj add.commute assms(1) assms(2) assms(3) orthogonal_complement_def 
      projection_intro1 projection_intro2 uminus_add_conv_diff)

lemma projection_fixed_points':
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: "is_projection_on \<pi> M" and a2: "closed_subspace M" and a3: "x \<in> M"
  shows "\<pi> x = x"
  by (metis (no_types, lifting) a1 a2 a3 closed_subspace.subspace complex_vector.subspace_0 
      diff_self projection_uniq' subspace_orthog)

lemma projection_fixed_points:
  fixes M :: \<open>('a::chilbert_space) set\<close>
  assumes a1: "closed_subspace M" and a2: "x \<in> M"
  shows "(projection M) x = x"
  using projection_fixed_points'
    \<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close>
  by (metis a1 a2 is_projection_on_existence projection_intro1 projection_intro2 projection_uniq')

proposition projectionPropertiesB':
  includes notation_norm
  fixes M :: \<open>('a::complex_inner) set\<close>
  assumes a1: \<open>is_projection_on \<pi> M\<close>
  shows \<open>\<parallel> \<pi>  h \<parallel> \<le> \<parallel> h \<parallel>\<close>
proof-
  have \<open>h - \<pi> h \<in> orthogonal_complement M\<close> 
    using a1
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
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes a1: "closed_subspace M"
  shows \<open>\<parallel> projection M h \<parallel> \<le> \<parallel> h \<parallel>\<close>
  using projectionPropertiesB' a1
  by (metis is_projection_on_existence projection_intro1 projection_intro2 projection_uniq')

\<comment> \<open>Theorem 2.7 (version) in @{cite conway2013course}\<close>
theorem projectionPropertiesA':
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: "is_projection_on \<pi> M" and a2: "closed_subspace M"
  shows "cbounded_linear \<pi>"
proof-
  have b1:  \<open>complex_vector.subspace (orthogonal_complement M)\<close>
    by (simp add: a2 closed_subspace.subspace)
  have f1: "\<forall>a. a - \<pi> a \<in> orthogonal_complement M \<and> \<pi> a \<in> M"
    by (metis a1 is_projection_on_def)
  hence "c *\<^sub>C x - c *\<^sub>C \<pi> x \<in> orthogonal_complement M"
    for c x
    by (metis (no_types) b1 
        add_diff_cancel_right' complex_vector.subspace_def diff_add_cancel scaleC_add_right)
  hence r1: \<open>\<pi> (c *\<^sub>C x) = c *\<^sub>C (\<pi> x)\<close> for x c
    using f1 by (meson a2 a1 closed_subspace.subspace 
        complex_vector.subspace_def projection_uniq')
  have r2: \<open>\<pi> (x + y) =  (\<pi> x) + (\<pi> y)\<close>
    for x y
  proof-
    have "\<forall>A. \<not> closed_subspace (A::'a set) \<or> complex_vector.subspace A"
      by (metis closed_subspace.subspace)
    hence "complex_vector.subspace M"
      using a2 by auto      
    hence \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> M\<close>
      by (simp add: complex_vector.subspace_add complex_vector.subspace_diff f1)      
    have \<open>closed_subspace (orthogonal_complement M)\<close>
      using a2
      by simp
    have f1: "\<forall>a b. (b::'a) + (a - b) = a"
      by (metis add.commute diff_add_cancel)
    have f2: "\<forall>a b. (b::'a) - b = a - a"
      by auto
    hence f3: "\<forall>a. a - a \<in> orthogonal_complement M"
      using b1 complex_vector.subspace_def by auto      
    have "\<forall>a b. (a \<in> orthogonal_complement M \<or> a + b \<notin> orthogonal_complement M)
             \<or> b \<notin> orthogonal_complement M"
      using add_diff_cancel_right' b1 complex_vector.subspace_diff by force
    hence "\<forall>a b c. (a \<in> orthogonal_complement M \<or> c - (b + a) \<notin> orthogonal_complement M) 
              \<or> c - b \<notin> orthogonal_complement M"
      using f1 by (metis diff_diff_add)
    hence f4: "\<forall>a b f. (f a - b \<in> orthogonal_complement M \<or> a - b \<notin> orthogonal_complement M) 
              \<or> \<not> is_projection_on f M"
      using f1 by (metis (no_types) is_projection_on_def)
    have f5: "\<forall>a b c d. (d::'a) - (c + (b - a)) = d + (a - (b + c))"
      by auto
    have "x - \<pi> x \<in> orthogonal_complement M"
      by (metis \<open>is_projection_on \<pi> M\<close> is_projection_on_def)
    hence q1: \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> orthogonal_complement M\<close>
      using f5 f4 f3 by (metis \<open>complex_vector.subspace (orthogonal_complement M)\<close> 
          \<open>is_projection_on \<pi> M\<close> add_diff_eq complex_vector.subspace_diff diff_diff_add 
          diff_diff_eq2)
    hence \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) \<in> M \<inter> (orthogonal_complement M)\<close>
      by (simp add: \<open>\<pi> (x + y) - (\<pi> x + \<pi> y) \<in> M\<close>)      
    moreover have \<open>M \<inter> (orthogonal_complement M) = {0}\<close>
      by (simp add: \<open>closed_subspace M\<close> closed_subspace.subspace complex_vector.subspace_0 ortho_inter_zero)      
    ultimately have \<open>\<pi> (x + y) - ( (\<pi> x) + (\<pi> y) ) = 0\<close>
      by auto      
    thus ?thesis by simp
  qed
  have t2: \<open>clinear \<pi>\<close>
    by (simp add: clinearI r1 r2) 
  have \<open>\<forall> x. norm (\<pi> x) \<le> norm x\<close>
    using a1 projectionPropertiesB' by auto
  hence \<open>\<forall> x. norm (\<pi> x) \<le> norm x * 1\<close>
    by simp
  hence t1: \<open>\<exists> K. \<forall> x. norm (\<pi> x) \<le> norm x * K\<close>
    by blast
  show ?thesis 
    unfolding cbounded_linear_def
    by (simp add: t1 t2)    
qed

theorem projectionPropertiesA:
  fixes M :: \<open>('a::chilbert_space) set\<close>
  assumes a1: "closed_subspace M"
  shows \<open>cbounded_linear (projection M)\<close> 
    \<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close>
  by (meson assms is_projection_on_def projectionPropertiesA' projection_intro1 projection_intro2)

proposition projectionPropertiesC':
  fixes M :: \<open>('a::complex_inner) set\<close>
  assumes a1: "is_projection_on \<pi> M" and a2: "closed_subspace M"
  shows " \<pi> \<circ> \<pi> = \<pi>"
proof-
  have \<open>(\<pi> \<circ> \<pi>) x = \<pi> x\<close>
    for x
  proof-
    have \<open>\<pi> x \<in> M\<close>
      by (simp add: \<open>is_projection_on \<pi> M\<close> projection_intro2')      
    hence \<open>\<pi> (\<pi> x) = \<pi> x\<close>
      using a1 a2 projection_fixed_points' by auto
    thus ?thesis by simp
  qed
  thus ?thesis by blast
qed

proposition projectionPropertiesC:
  fixes M :: "'a::chilbert_space set"
  assumes a1: "closed_subspace M"
  shows "(projection M) \<circ> (projection M) = projection M"
  using a1 projectionPropertiesC'
  by (metis is_projection_on_def projection_intro1 projection_intro2) 

lemma ker_op_lin:
  assumes a1: "cbounded_linear f"
  shows "closed_subspace  (f -` {0})"
proof-
  have w3: \<open>t *\<^sub>C x \<in> {x. f x = 0}\<close> 
    if b1: "x \<in>  {x. f x = 0}"
    for x t
  proof-
    have \<open>f x = 0\<close>
      using that by auto      
    hence  \<open>f  (t *\<^sub>C x) = 0\<close>
      using a1 cbounded_linear.clinear
      by (simp add: cbounded_linear.is_clinear complex_vector.linear_scale) 
    hence \<open> t *\<^sub>C x \<in> {x. f x = 0}\<close>
      by simp
    thus ?thesis 
      by auto
  qed
  have \<open>clinear f\<close>
    using \<open>cbounded_linear f\<close>
    unfolding cbounded_linear_def by blast
  hence \<open>f 0 = 0\<close>
    by (simp add: complex_vector.linear_0)      
  hence s2: \<open>0 \<in> {x. f x = 0}\<close>
    by blast
  have s1: "L \<in> {x. f x = 0}"
    if "r \<longlonglongrightarrow> L" and "\<forall> n. r n \<in> {x. f x = 0}"
    for r and  L 
  proof-
    have d1: \<open>\<forall> n. f (r n) = 0\<close>
      using that(2) by auto
    have \<open>(\<lambda> n. f (r n)) \<longlonglongrightarrow> f L\<close>
      using assms bounded_linear_continuous continuous_within_tendsto_compose' that(1) 
      by fastforce
    hence \<open>(\<lambda> n. 0) \<longlonglongrightarrow> f L\<close>
      using d1 by simp        
    hence \<open>f L = 0\<close>
      using limI by fastforce
    thus ?thesis by blast
  qed

  have w4: "x + y \<in> {x. f x = 0}"
    if c1: "x \<in> {x. f x = 0}" and c2: "y \<in> {x. f x = 0}"
    for x y
  proof-
    have w1: \<open>f x = 0\<close> 
      using c1 by auto
    have w2: \<open>f y = 0\<close>
      using c2 by auto
    have  \<open>f (x + y) = f x + f y\<close>
      using \<open>cbounded_linear f\<close>
      unfolding cbounded_linear_def clinear_def Vector_Spaces.linear_def module_hom_def 
        module_hom_axioms_def by auto
    hence  \<open>f (x + y) = 0\<close>
      by (simp add: w1 w2)
    hence \<open>x + y \<in>  {x. f x = 0}\<close>
      by simp
    show ?thesis
      using \<open>x + y \<in> {x. f x = 0}\<close> by blast 
  qed
  have s4: \<open>c *\<^sub>C t \<in> {x. f x = 0}\<close> 
    if "t \<in> {x. f x = 0}"
    for t c
    using that w3 by auto
  have s5: "u + v \<in> {x. f x = 0}"
    if "u \<in> {x. f x = 0}" and "v \<in> {x. f x = 0}"
    for u v
    using w4 that(1) that(2) by auto    
  have s3: \<open>closed {x. f x = 0}\<close>
    using closed_sequential_limits s1 by blast 
  have f3: "f -` {b. b = 0 \<or> b \<in> {}} = {a. f a = 0}"
    by blast
  have "closed_subspace {a. f a = 0}"
    by (metis closed_subspace.intro complex_vector.subspace_def s2 s3 s4 s5)
  thus ?thesis
    using f3 by auto
qed


proposition projectionPropertiesD':
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: "is_projection_on \<pi> M" and a2: "closed_subspace M"
  shows "\<pi> -` {0} = (orthogonal_complement M)"
proof-
  have "x \<in> (\<pi> -` {0})" 
    if "x \<in> orthogonal_complement M"
    for x
  proof-
    have \<open>\<pi> x \<in> M\<close>
      using  \<open>is_projection_on \<pi> M\<close>
      by (simp add: projection_intro2')
    have f1: "\<forall>a. (a::'a) = 0 \<or> - \<langle>a, a\<rangle> < 0"
      by (metis cinner_gt_zero_iff neg_less_0_iff_less)
    have f2: "- \<pi> 0 \<in> orthogonal_complement M"
      by (metis (no_types) a1 add.inverse_inverse add.left_neutral diff_minus_eq_add 
          is_projection_on_def)
    have f3: "- (0::'a) = 0"
      by simp
    have "0 \<in> M"
      using f2 f1 by (metis (no_types) a1 cinner_gt_zero_iff cinner_minus_left cinner_zero_left 
          is_projection_on_def orthogonal_complement_D1)
    hence \<open>\<pi> x = 0\<close>
      using f3 by (metis (no_types) a1 a2 add.right_neutral diff_minus_eq_add projection_uniq' that)
    hence \<open>x \<in> (\<pi> -` {0})\<close>
      by simp
    thus ?thesis
      by simp
  qed
  moreover have "x \<in> orthogonal_complement M"
    if s1: "x \<in> \<pi> -` {0}" for x
  proof-
    have \<open>x \<in> {y.  \<pi> x = 0}\<close>
      using s1
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
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes a1: "closed_subspace M"
  shows "(projection M) -` {0} = (orthogonal_complement M)"
  using a1
  by (simp add: projectionPropertiesD' is_projection_on_def projection_intro1 projection_intro2)

lemma range_lin:
  assumes a1: "clinear f"
  shows "complex_vector.subspace (range f)"
proof-
  define A where "A = (range f)"
  have add: "x+y\<in>A" 
    if s1: "x\<in>A" and s2: "y\<in>A" 
    for x y
  proof-
    obtain xx where \<open>x = f xx\<close> using  \<open>A = (range f)\<close> 
      using s1 mem_Collect_eq
      by blast
    obtain yy where \<open>y = f yy\<close> using  \<open>A = (range f)\<close> 
      using s2 mem_Collect_eq
      by blast
    have \<open>x + y = f (xx + yy)\<close> 
      using Modules.additive_def \<open>clinear f\<close> \<open>x = f xx\<close> \<open>y = f yy\<close>  clinear_def
      by (simp add: complex_vector.linear_add)
    thus ?thesis 
      unfolding A_def
      using  mem_Collect_eq
      by blast 
  qed
  have mult: "c *\<^sub>C x \<in> A" 
    if s: "x\<in>A"
    for x c
  proof-
    obtain y where y_def: \<open>x = f y\<close>
      using s \<open>A = (range f)\<close> mem_Collect_eq
      by blast
    have \<open>c *\<^sub>C x = f (c *\<^sub>C y)\<close>
      using  \<open>x = f y\<close> \<open>clinear f\<close>
      by (simp add: complex_vector.linear_scale)
    thus ?thesis
      unfolding A_def
      using y_def
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
      unfolding A_def
      by simp
  qed
  thus ?thesis 
    unfolding A_def
    using assms complex_vector.linear_subspace_image complex_vector.subspace_UNIV by blast 
qed

theorem projectionPropertiesE':
  fixes M :: "'a::complex_inner set"
  assumes a1: "is_projection_on \<pi> M" and a2: "closed_subspace M"
  shows "range \<pi> = M"
proof-
  have \<open>x \<in> M\<close> 
    if "x \<in> range \<pi>"
    for x
    using projection_intro2' a1 that by blast 
  moreover have \<open>x \<in> range \<pi>\<close> 
    if "x \<in> M" for x
    using that \<open>closed_subspace M\<close>
    by (metis UNIV_I a1 image_eqI projection_fixed_points')     
  ultimately show ?thesis by blast
qed

\<comment> \<open>Theorem 2.7 in @{cite conway2013course}\<close> 
theorem projectionPropertiesE:
  fixes M :: \<open>('a::chilbert_space) set\<close>
  assumes a1: "closed_subspace M"
  shows "range  (projection M) = M"
proof-
  obtain b :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a" where
    f2: "\<forall>f A. (\<not> is_projection_on f A \<or> (\<forall>a. a - f a \<in> orthogonal_complement A \<and> f a \<in> A)) 
    \<and> (is_projection_on f A \<or> b A f - f (b A f) \<notin> orthogonal_complement A \<or> f (b A f) \<notin> A)"
    by (metis (no_types) is_projection_on_def)
  obtain c :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a" where
    "is_projection_on (c M) M"
    using a1 by (meson is_projection_on_existence)
  hence "\<forall>a. a - c M a \<in> orthogonal_complement M \<and> c M a \<in> M"
    using f2 by blast
  thus ?thesis
    using f2 a1 by (metis (no_types) projectionPropertiesE' projection_uniq)
qed 

lemma pre_ortho_twice:
  assumes a1: "complex_vector.subspace M"
  shows "M \<subseteq> (orthogonal_complement (orthogonal_complement M))"
proof-
  have "x \<in> (orthogonal_complement (orthogonal_complement M))"
    if s1: "x \<in> M"
    for x
  proof-
    have \<open>\<forall> y \<in> (orthogonal_complement M). \<langle> x, y \<rangle> = 0\<close>
      using s1 orthogonal_complement_D2 by auto
    hence \<open>x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      by (simp add: orthogonal_complement_def)
    thus ?thesis by blast
  qed            
  thus ?thesis 
    by (simp add: subsetI)
qed


lemma ProjOntoOrtho':
  fixes M :: \<open>'a::complex_inner set\<close>
  assumes a1: "is_projection_on \<pi> M" and a2: "is_projection_on \<sigma> (orthogonal_complement M)"
    and a3: "closed_subspace M"
  shows "id - \<pi> = \<sigma>"   
proof-
  have \<open>(id - \<pi>) x = \<sigma> x\<close> for x
  proof-
    have b1:\<open>x - \<pi> x \<in> orthogonal_complement M\<close>
      by (simp add: a1 projection_intro1')            
    hence b2: \<open>(id -  \<pi>) x \<in> orthogonal_complement M\<close>
      by simp
    have b3: \<open>\<pi> x \<in>  M\<close>
      by (simp add: a1 projection_intro2')      
    hence b4: \<open>x - (id - \<pi>) x \<in>  M\<close>
      by simp
    hence b5: \<open>\<pi> x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      by (simp add: orthogonal_complement_D1 orthogonal_complement_I1)            
    hence b6:\<open>x - (id -  \<pi>) x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      by simp
    thus ?thesis
      using a2 a3 b2 projection_uniq' subspace_orthog by fastforce
  qed
  thus ?thesis by blast
qed

\<comment> \<open>Exercice 2 (section 2, chapter I) in  @{cite conway2013course}\<close> 
lemma ProjOntoOrtho:
  fixes M :: "'a::chilbert_space set"
  assumes a1: "closed_subspace M"
  shows "id - projection M = projection (orthogonal_complement M)"
  using ProjOntoOrtho'
  by (metis assms is_projection_on_def projection_intro1 projection_intro2 subspace_orthog)


\<comment> \<open>Corollary 2.8 in  @{cite conway2013course}\<close>
theorem orthogonal_complement_twice:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes a1: "closed_subspace M"
  shows "orthogonal_complement (orthogonal_complement M) = M"  
proof-
  have b2: "x \<in>  ( ( id - (projection M) ) -` {0} )"
    if c1: "x \<in>  M"
    for x
  proof-
    have \<open>(projection M) x = x\<close>
      by (simp add: assms projection_fixed_points that)
    hence \<open>(id - (projection M)) x = 0\<close> 
      by simp
    hence \<open>x \<in> {v. (id - (projection M)) v = 0}\<close>
      by simp
    hence \<open>x \<in>  (real_vector.span {v. (id - (projection M)) v = 0})\<close>
      using span_superset
      by (simp add: real_vector.span_base)         
    hence \<open>x \<in> ( ( id - (projection M) ) -` {0} )\<close>
      using \<open>(id - projection M) x = 0\<close> by auto 
    thus ?thesis 
      by simp                  
  qed

  have b3: \<open>x \<in>  M\<close> 
    if c1: \<open>x \<in> ( id - (projection M) ) -` {0}\<close>
    for x
  proof-
    have \<open>(id - (projection M)) x = 0\<close>
      using c1
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
  have \<open>x \<in>  M \<longleftrightarrow> x \<in>  ( ( id - (projection M) ) -` {0} )\<close> for x
    using b2 b3 by blast      
  hence b4: \<open>( id - (projection M) ) -` {0} =  M\<close>
    by blast
  have b1: "orthogonal_complement (orthogonal_complement M) 
          = (projection (orthogonal_complement M)) -` {0}"
    by (simp add: a1 projectionPropertiesD)
  also have \<open>... = ( id - (projection M) ) -` {0}\<close>
    by (simp add: ProjOntoOrtho a1)
  also have \<open>... = M\<close>
    by (simp add: b4)     
  finally show ?thesis by blast
qed


lemma ortho_leq[simp]:
  fixes  A B :: \<open>('a::chilbert_space) set\<close>
  assumes \<open>closed_subspace A\<close> and  \<open>closed_subspace B\<close>
  shows \<open>orthogonal_complement A \<subseteq> orthogonal_complement B \<longleftrightarrow> A \<supseteq> B\<close>
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
  "orthogonal_complement ({0}::'a::chilbert_space set) = (top::'a set)"
  using  orthogonal_complement_twice 
  by (metis Complex_Vector_Spaces.subspace_UNIV ortho_top)


subsection \<open>Closed sum\<close>

definition closed_sum:: \<open>'a::{complex_vector,topological_space} set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>closed_sum A B = closure (A + B)\<close>

notation closed_sum (infixl "+\<^sub>M" 65)

lemma sum_existential:
  assumes  "x \<in> (A + B)"
  shows "\<exists>a\<in>A. \<exists>b\<in>B. x = a + b"
  by (meson assms set_plus_elim)

lemma is_closed_subspace_comm:                                                                 
  assumes \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close>
  shows \<open>A +\<^sub>M B = B +\<^sub>M A\<close>
  by (smt Collect_cong add.commute closed_sum_def)

lemma cinner_isCont_left:
  \<open>isCont (\<lambda> t. \<langle> t, x \<rangle>) y\<close>
proof-
  have \<open>((\<lambda> t. \<langle> t , x \<rangle>) \<circ> s) \<longlonglongrightarrow> (\<lambda> t. \<langle> t , x \<rangle>) y\<close>
    if a1: "s \<longlonglongrightarrow> y"
    for s::\<open>nat \<Rightarrow> _\<close>
  proof-
    have \<open>\<exists> K. \<forall> u v. norm \<langle>u , v \<rangle> \<le> norm u * norm v * K\<close>
      using bounded_sesquilinear.bounded bounded_sesquilinear_cinner by auto
    then obtain K where K_def: \<open>\<forall> u v::'a. norm \<langle>u , v\<rangle> \<le> norm u * norm v * K\<close>
      by blast
    hence CS: \<open>norm \<langle>u, v\<rangle> \<le> norm u * norm v * K\<close>
      for u::'a and v::'a
      by auto
    have \<open>norm \<langle>s n - y, x\<rangle> \<le> norm (s n - y) * norm x * K\<close>
      for n
      using CS[where u1 = "s n - y" and v1 = "x"]
      by blast
    hence s1: \<open>\<forall> n. cmod \<langle>s n - y, x\<rangle> \<le> norm (norm (s n - y) * norm x) * norm K\<close>
      by (smt norm_mult real_norm_def)      
    have \<open>(\<lambda> n.  norm (s n - y)) \<longlonglongrightarrow> 0\<close>
      using \<open>s \<longlonglongrightarrow> y\<close>
      by (simp add: LIM_zero_iff tendsto_norm_zero)
    hence s2: \<open>(\<lambda> n.  norm (s n - y) * norm x) \<longlonglongrightarrow> 0\<close>
      by (simp add: tendsto_mult_left_zero)
    hence \<open>(\<lambda> n. \<langle> s n - y , x \<rangle>) \<longlonglongrightarrow> 0\<close>
      using Limits.tendsto_0_le[where g = "(\<lambda> n. \<langle> s n - y , x \<rangle>)" and f = "(\<lambda> n. norm (s n - y) * norm x)" and K = "norm K"]
        always_eventually s1 by blast            
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
  have "l \<in> (orthogonal_complement A)"
    if a1: "\<forall> n. x n \<in> (orthogonal_complement A)" and a2: "x \<longlonglongrightarrow> l"
    for x l
  proof-
    have \<open>\<forall> n. \<forall> y \<in> A. \<langle> y , x n \<rangle> = 0\<close>
      by (simp add: a1 orthogonal_complement_D2)      
    moreover have \<open>isCont (\<lambda> t. \<langle> y , t \<rangle>) l\<close> for y
      using cinner_isCont_right by blast
    ultimately have \<open>(\<lambda> n. (\<langle> y , x n \<rangle>) ) \<longlonglongrightarrow> \<langle> y , l \<rangle>\<close> for y 
      using isCont_tendsto_compose
      by (simp add: isCont_tendsto_compose a2)
    hence \<open>\<forall> y \<in> A. (\<lambda> n. (\<langle> y , x n \<rangle>) ) \<longlonglongrightarrow> \<langle> y , l \<rangle>\<close>
      by simp
    hence \<open>\<forall> y \<in> A. (\<lambda> n. 0 ) \<longlonglongrightarrow> \<langle> y , l \<rangle>\<close>
      using  \<open>\<forall> n. \<forall> y \<in> A. \<langle> y , x n \<rangle> = 0\<close> by fastforce
    hence \<open>\<forall> y \<in> A. \<langle> y , l \<rangle> = 0\<close> 
      using limI by fastforce
    thus ?thesis
      by (simp add: orthogonal_complement_I1) 
  qed
  thus ?thesis 
    using closed_sequential_limits by blast
qed


lemma OrthoClosedEq:
  fixes A ::"('a::complex_inner) set"
  shows "orthogonal_complement A = orthogonal_complement (closure A)"
proof-
  have s1: \<open>\<langle> y, x \<rangle> = 0\<close> 
    if a1: "x \<in> (orthogonal_complement A)"
      and a2: \<open>y \<in> closure A\<close>  
    for x y
  proof-
    have \<open>\<forall> y \<in> A. \<langle> y , x \<rangle> = 0\<close>
      by (simp add: a1 orthogonal_complement_D2)
    then obtain yy where \<open>\<forall> n. yy n \<in> A\<close> and \<open>yy \<longlonglongrightarrow> y\<close>
      using a2 closure_sequential by blast       
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
  hence "x \<in> orthogonal_complement (closure A)"
    if a1: "x \<in> (orthogonal_complement A)"
    for x
    using that
    by (simp add: orthogonal_complement_I1) 
  moreover have \<open>x \<in> (orthogonal_complement A)\<close> 
    if "x \<in> (orthogonal_complement (closure A))"
    for x
    using that
    by (meson closure_subset orthogonal_complement_D1 orthogonal_complement_I2 subset_eq)
  ultimately show ?thesis by blast
qed

lemma subspace_closed_plus:
  fixes A B::"('a::complex_normed_vector) set"
  assumes a1: \<open>closed_subspace A\<close> and a2: \<open>closed_subspace B\<close>
  shows \<open>closed_subspace (A +\<^sub>M B)\<close>
  using a1 a2 closed_sum_def 
  by (metis closed_subspace.subspace subspace_I subspace_plus)

lemma DeMorganOrtho:        
  fixes A B::"('a::complex_inner) set"
  assumes a1: \<open>closed_subspace A\<close> and a2: \<open>closed_subspace B\<close>
  shows \<open>orthogonal_complement (A +\<^sub>M B) = (orthogonal_complement A) \<inter> (orthogonal_complement B)\<close>
proof-
  have "x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)"
    if "x \<in> orthogonal_complement (A +\<^sub>M B)" 
    for x
  proof-
    have \<open>orthogonal_complement (A +\<^sub>M B) = orthogonal_complement (A + B)\<close>
      unfolding closed_sum_def by (subst OrthoClosedEq[symmetric], simp)
    hence \<open>x \<in> orthogonal_complement (A + B)\<close>
      using that by blast      
    hence t1: \<open>\<forall>z \<in> (A + B). \<langle> z , x \<rangle> = 0\<close>
      by (simp add: orthogonal_complement_D2) 
    have \<open>0 \<in> B\<close>
      using assms(2) complex_vector.subspace_def
      unfolding closed_subspace_def
      by auto
    hence \<open>A \<subseteq> A + B\<close>
      using subset_iff add.commute set_zero_plus2 
      by fastforce
    hence \<open>\<forall>z \<in> A. \<langle> z , x \<rangle> = 0\<close> 
      using t1 by auto
    hence w1: \<open>x \<in> (orthogonal_complement A)\<close>
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    have \<open>0 \<in> A\<close>
      using assms(1) complex_vector.subspace_def
      unfolding closed_subspace_def
      by auto
    hence \<open>B \<subseteq> A + B\<close>
      using subset_iff set_zero_plus2 by blast        
    hence \<open>\<forall> z \<in> B. \<langle> z , x \<rangle> = 0\<close>
      using t1 by auto   
    hence \<open>x \<in> (orthogonal_complement B)\<close>
      by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm orthogonal_complement_def)
    thus ?thesis 
      using w1 by auto
  qed
  moreover have "x \<in> (orthogonal_complement (A +\<^sub>M B))"
    if v1: "x \<in> (orthogonal_complement A) \<inter> (orthogonal_complement B)"
    for x
  proof-
    have \<open>x \<in> (orthogonal_complement A)\<close> 
      using v1
      by blast
    hence \<open>\<forall>y\<in> A. \<langle> y , x \<rangle> = 0\<close>
      by (simp add: orthogonal_complement_D2)
    have \<open>x \<in> (orthogonal_complement B)\<close> 
      using v1 
      by blast
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
  fixes A B::"'a::chilbert_space set"
  assumes a1: \<open>closed_subspace A\<close> and a2: \<open>closed_subspace B\<close>
  shows  \<open>orthogonal_complement (A \<inter> B) = orthogonal_complement A +\<^sub>M orthogonal_complement B\<close>
proof-
  have \<open>orthogonal_complement (A \<inter> B) 
    = orthogonal_complement ((orthogonal_complement (orthogonal_complement A)
   \<inter> orthogonal_complement (orthogonal_complement B) ))\<close>
    by (metis assms(1) assms(2) orthogonal_complement_twice)
  also have \<open>... = orthogonal_complement ( orthogonal_complement ((orthogonal_complement A)
                     +\<^sub>M (orthogonal_complement B)) )\<close>
    using DeMorganOrtho assms(1) assms(2) complex_vector.subspace_def
    by (simp add: DeMorganOrtho)
  also have \<open>... = (orthogonal_complement A +\<^sub>M orthogonal_complement B)\<close>
    using a1 a2 orthogonal_complement_twice
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
  assumes \<open>cbounded_linear f\<close>
  shows \<open>f (projection (f -` {0}) x) = 0\<close>
proof-
  from \<open>cbounded_linear f\<close>
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
  assumes a1: \<open>closed_subspace M\<close> and a2: \<open>t \<noteq> 0\<close> and a3: \<open>t \<in> M\<close>
    and a4: \<open>\<forall> m \<in> M. \<exists> k. m = k *\<^sub>C t\<close>
  shows \<open>projection M x = (\<langle>t , x\<rangle> / \<langle>t , t\<rangle>) *\<^sub>C t\<close>
proof-
  have tt: \<open>\<langle>t , t\<rangle> \<noteq> 0\<close>
    by (simp add: a2)
  obtain k where k_def: \<open>projection M x = k *\<^sub>C t\<close>
    using assms(1) assms(4) projection_intro2 by blast
  have \<open>projection (orthogonal_complement M) x \<in> orthogonal_complement M\<close>
    by (simp add: a1 projection_intro2)
  hence t1: \<open>\<langle>t , projection (orthogonal_complement M) x\<rangle> = 0\<close>
    using a3
    unfolding orthogonal_complement_def is_orthogonal_def
    by (smt is_orthogonal_def mem_Collect_eq orthogonal_comm)
  have \<open>(\<langle>t , x\<rangle>/\<langle>t , t\<rangle>) *\<^sub>C t =
 (\<langle>t , projection M x + projection (orthogonal_complement M) x\<rangle>/\<langle>t , t\<rangle>) *\<^sub>C t\<close>
    using a1 ortho_decomp by fastforce
  also have \<open>... = (\<langle>t , (projection M) x\<rangle>/\<langle>t , t\<rangle>) *\<^sub>C t\<close>
    using t1 by (simp add: cinner_right_distrib) 
  also have \<open>... = (\<langle>t , (k *\<^sub>C t)\<rangle>/\<langle>t , t\<rangle>) *\<^sub>C t\<close>
    using k_def 
    by simp
  also have \<open>... = (k*\<langle>t , t\<rangle>/\<langle>t , t\<rangle>) *\<^sub>C t\<close>
    by simp   
  also have \<open>... = k *\<^sub>C t\<close>
    using  tt by simp
  finally show ?thesis
    using k_def by auto      
qed


subsection \<open>Riesz Representation\<close>

definition proportion :: \<open>'a::complex_vector set \<Rightarrow> bool\<close> where
  \<open>proportion S =  (
  \<forall> x y. x \<in> S \<and> x \<noteq> 0 \<and> y \<in> S \<and> y \<noteq> 0 \<longrightarrow> (\<exists> k. x = k *\<^sub>C y) 
)\<close>

lemma proportion_existence:
  assumes a1: "proportion S" and a2: "S \<noteq> {}"
  shows "\<exists> t \<in> S. \<forall> x \<in> S. \<exists> k. x = k *\<^sub>C t" 
  using a1 a2 complex_vector.scale_zero_left ex_in_conv proportion_def
  by metis

type_synonym 'a functional = \<open>'a \<Rightarrow> complex\<close>

lemma ker_ortho_nonzero:
  fixes f :: \<open>'a::chilbert_space functional\<close> and x :: 'a
  assumes a1: \<open>cbounded_linear f\<close> and a2: \<open>x \<noteq> 0\<close> and a3: \<open>x \<in> orthogonal_complement (f -` {0})\<close> 
  shows \<open>f x \<noteq> 0\<close>
  using a1 a2 a3 ker_op_lin projectionPropertiesD projection_fixed_points by force

lemma ker_unidim:
  fixes f :: \<open>'a::chilbert_space functional\<close>
  assumes a1: \<open>cbounded_linear f\<close>
  shows \<open>proportion (orthogonal_complement (f -` {0}))\<close>
proof-
  have "\<exists> k. x = k *\<^sub>C y"
    if b1: \<open>x \<in> (orthogonal_complement (f -` {0}))\<close> and b2: \<open>x \<noteq> 0\<close> 
      and b3:  \<open>y \<in>(orthogonal_complement (f -` {0}))\<close> and b4: \<open>y \<noteq> 0\<close>
    for x y
  proof-
    have f1: \<open>closed_subspace (f -` {0})\<close>
      using a1
      by (simp add: ker_op_lin)
    hence r3: \<open>closed_subspace (orthogonal_complement (f -` {0}))\<close>
      by simp
    hence r1: \<open>f x \<noteq> 0\<close>
      by (simp add: assms b1 b2 ker_ortho_nonzero)
    have r2: \<open>f y \<noteq> 0\<close>
      by (simp add: assms b3 b4 ker_ortho_nonzero)
    have \<open>\<exists> k. (f x) = k*(f y)\<close>
      by (metis add.inverse_inverse minus_divide_eq_eq r2)
    then obtain k where k_def: \<open>f x = k * f y\<close>
      by blast
    hence  \<open>f x = f (k *\<^sub>C y)\<close>
      using a1
      unfolding cbounded_linear_def
      by (simp add: complex_vector.linear_scale)
    hence  \<open>f x - f (k *\<^sub>C y) = 0\<close>
      by simp
    hence s1: \<open>f (x - k *\<^sub>C y) = 0\<close>
      using additive.diff a1
      unfolding cbounded_linear_def
      by (simp add: complex_vector.linear_diff)        
    have  \<open>k *\<^sub>C y \<in> (orthogonal_complement (f -` {0}))\<close>
      using r3 complex_vector.subspace_scale
      unfolding closed_subspace_def
      by (simp add: complex_vector.subspace_scale b3)
    hence s2: \<open>x - (k *\<^sub>C y) \<in> orthogonal_complement (f -` {0})\<close>
      by (smt f1 b1 eq_iff_diff_eq_0 is_projection_on_existence 
          orthogonal_complement_twice projectionPropertiesD projection_fixed_points 
          projection_fixed_points' projection_uniq' r3 s1 vimage_singleton_eq)
    have s3: \<open>(x - (k *\<^sub>C y)) \<in> f -` {0}\<close>
      using s1
      by simp
    moreover have \<open>(f -` {0}) \<inter> (orthogonal_complement (f -` {0})) = {0}\<close>
      by (metis f1 b1 ortho_inter_zero projectionPropertiesD projection_intro2 vimage_singleton_eq)    
    ultimately have \<open>x - (k *\<^sub>C y) = 0\<close>
      using s2 by blast
    thus ?thesis by simp
  qed 
  thus ?thesis
    by (simp add: proportion_def) 
qed

lemma riesz_frechet_representation_existence:
  fixes f::\<open>'a::chilbert_space functional\<close>
  assumes a1: \<open>cbounded_linear f\<close>
  shows \<open>\<exists>t. \<forall>x.  f x = \<langle>t, x\<rangle>\<close>
proof(cases \<open>\<forall> x. f x = 0\<close>)
  case True
  thus ?thesis
    by (metis cinner_zero_left) 
next
  case False
  have r1: \<open>proportion (orthogonal_complement (f -` {0}))\<close>
    using a1
    by (simp add: ker_unidim)    
  have "(\<exists>a\<in>orthogonal_complement (f -` {0}). a \<noteq> 0)
     \<or> orthogonal_complement (f -` {0}) \<noteq> {} \<and> f -` {0} \<noteq> UNIV"
    by (metis (no_types) False UNIV_I assms insert_absorb ker_op_lin ortho_bot 
        orthogonal_complement_twice projection_intro1 vimage_singleton_eq)
  hence  r2: \<open>\<exists> h \<in> (orthogonal_complement (f -` {0})). h \<noteq> 0\<close>
    by (metis (no_types) assms insertI1 is_singletonE is_singletonI' ker_op_lin ortho_bot 
        orthogonal_complement_twice)        
  have \<open>\<exists> t. t \<noteq> 0 \<and> (\<forall> x \<in>(orthogonal_complement (f -` {0})). \<exists> k. x = k *\<^sub>C t)\<close>
    using r1 r2
    by (metis complex_vector.scale_zero_right equals0D proportion_existence) 
  then obtain t where w1: \<open>t \<noteq> 0\<close> and w2: \<open>\<forall>x\<in>orthogonal_complement (f -` {0}). \<exists>k. x = k *\<^sub>C t\<close>
    by blast
  have q1: \<open>closed_subspace (orthogonal_complement (f -` {0}))\<close>
    by (simp add: assms ker_op_lin)
  have \<open>\<exists>s \<in> (orthogonal_complement (f -` {0})). s \<noteq> 0\<close>
    by (simp add: r2)
  then obtain s where s1: \<open>s \<in> (orthogonal_complement (f -` {0}))\<close> and s2: \<open>s \<noteq> 0\<close>
    by blast
  have \<open>\<exists> k. s = k *\<^sub>C t\<close>
    by (simp add: s1 w2)    
  then obtain k where k_def: \<open>s = k *\<^sub>C t\<close>
    by blast
  have  \<open>k \<noteq> 0\<close>
    using k_def s2 by auto    
  hence  \<open>(1/k) *\<^sub>C s = t\<close>
    by (simp add: k_def)
  moreover have \<open>(1/k) *\<^sub>C s \<in>  (orthogonal_complement (f -` {0}))\<close>
    unfolding closed_subspace_def
    by (simp add: s1 orthogonal_complement_D2 orthogonal_complement_I1)
  ultimately have w3: \<open>t \<in> (orthogonal_complement (f -` {0}))\<close>
    by simp
  have \<open>projection (orthogonal_complement (f -` {0})) x = (\<langle>t , x\<rangle>/\<langle>t , t\<rangle>) *\<^sub>C t\<close>
    for x
    using inner_product_projection
    by (simp add: inner_product_projection q1 w1 w2 w3) 
  hence l1: \<open>f (projection (orthogonal_complement (f -` {0})) x) = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) * (f t)\<close>
    for x
    using a1
    unfolding cbounded_linear_def
    by (simp add: complex_vector.linear_scale)
  hence l2: \<open>f (projection (orthogonal_complement (f -` {0})) x) = \<langle>((cnj (f t)/\<langle>t , t\<rangle>) *\<^sub>C t) , x\<rangle>\<close>
    for x
  proof-
    have \<open>f (projection (orthogonal_complement (f -` {0})) x) = ((f t)/(\<langle>t , t\<rangle>)) * (\<langle>t , x\<rangle>)\<close>
      by (simp add: l1)
    thus ?thesis
      by auto 
  qed
  have l3: \<open>f (projection (f -` {0}) x) = 0\<close>
    for x
    using  assms ker_op_lin projection_intro2 by blast
  have "\<And>a b. f (projection (f -` {0}) a + b) = 0 + f b"
    using additive.add assms l3
    by (simp add: cbounded_linear_def complex_vector.linear_add)
  hence "\<And>a. 0 + f (projection (orthogonal_complement (f -` {0})) a) = f a"
    by (metis (no_types) assms ker_op_lin ortho_decomp)
  hence \<open>f x = \<langle>(cnj (f t)/\<langle>t , t\<rangle>) *\<^sub>C t, x\<rangle>\<close>
    for x
    by (simp add: l2) 
  thus ?thesis
    by blast
qed

subsection \<open>Adjointness\<close>
definition \<open>Adj G = (SOME F. \<forall>x. \<forall>y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>)\<close>
  for G :: "'b::complex_inner \<Rightarrow> 'a::complex_inner"

lemma Adj_I:
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes a1: \<open>cbounded_linear G\<close>
  shows \<open>\<forall>x. \<forall>y. \<langle>Adj G x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
proof (unfold Adj_def, rule someI_ex[where P="\<lambda>F. \<forall>x. \<forall>y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>"])
  include notation_norm
  have b1: \<open>clinear G\<close>
    using a1
    unfolding cbounded_linear_def by blast
  have b2: \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
    using  \<open>cbounded_linear G\<close>
    unfolding cbounded_linear_def
    by simp
  define g :: \<open>'a \<Rightarrow> 'b \<Rightarrow> complex\<close> 
    where \<open>g x y = \<langle>x , G y\<rangle>\<close> for x y
  have \<open>cbounded_linear (g x)\<close>
    for x
  proof-
    have \<open>g x (a + b) = g x a + g x b\<close>
      for a b
      unfolding g_def
      using b1 additive.add cinner_right_distrib clinear_def
      by (simp add: cinner_right_distrib complex_vector.linear_add)
    moreover have  \<open>g x (k *\<^sub>C a) = k *\<^sub>C (g x a)\<close>
      for a k
      unfolding g_def
      using b1
      by (simp add: complex_vector.linear_scale)
    ultimately have \<open>clinear (g x)\<close>
      by (simp add: clinearI)    
    moreover have \<open>\<exists>M. \<forall>y. \<parallel> g x y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
      using b2 g_def
      by (simp add: a1 cbounded_linear.bounded cbounded_linear_cinner_right_comp)
    ultimately show ?thesis unfolding bounded_linear_def
      using cbounded_linear.intro
      by blast 
  qed
  hence  \<open>\<forall>x. \<exists>t. \<forall>y.  g x y = \<langle>t, y\<rangle>\<close>
    using  riesz_frechet_representation_existence by blast
  hence  \<open>\<exists>F. \<forall>x. \<forall>y.  g x y = \<langle>F x, y\<rangle>\<close>
    by metis
  then obtain F where \<open>\<forall>x. \<forall>y. g x y = \<langle>F x, y\<rangle>\<close>
    by blast
  thus "\<exists>x. \<forall>i y. \<langle>x i, y\<rangle> = \<langle>i, G y\<rangle>" using  g_def
    by auto
qed

lemma Adj_I':
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::complex_inner"
  assumes a1: \<open>cbounded_linear G\<close>
  shows \<open>\<forall>x. \<forall>y. \<langle>x, Adj G y\<rangle> = \<langle>G x, y\<rangle>\<close>
  by (metis Adj_I assms cinner_commute')

notation Adj ("_\<^sup>\<dagger>" [99] 100)

lemma Adj_D:
  fixes G:: \<open>'b::chilbert_space \<Rightarrow> 'a::complex_inner\<close>
    and F:: \<open>'a \<Rightarrow> 'b\<close>
  assumes a1: "cbounded_linear G" and
    F_is_adjoint: \<open>\<And>x y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
  shows \<open>F = G\<^sup>\<dagger>\<close>
proof-
  have b1: \<open>\<forall>x. \<forall>y. \<langle>(G\<^sup>\<dagger>) x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
    using  a1 Adj_I by blast
  have  \<open>\<forall>x. \<forall>y. \<langle>F x , y\<rangle> - \<langle>(G\<^sup>\<dagger>) x , y\<rangle> = 0\<close>
    by (simp add: b1 F_is_adjoint)
  hence  \<open>\<forall>x. \<forall> y. \<langle>F x - (G\<^sup>\<dagger>) x, y\<rangle> = 0\<close>
    by (simp add: cinner_diff_left)
  hence b2: \<open>\<forall> x. F x - (G\<^sup>\<dagger>) x = 0\<close>
    by (metis cinner_gt_zero_iff cinner_zero_left)
  hence \<open>\<forall>x. (F - (G\<^sup>\<dagger>)) x = 0\<close>
    by simp
  hence \<open>\<forall>x. F x = (G\<^sup>\<dagger>) x\<close>
    by (simp add: b2 eq_iff_diff_eq_0)
  thus ?thesis by auto
qed


lemma Adj_cbounded_linear:
  fixes A :: "'a::chilbert_space \<Rightarrow> 'b::complex_inner"
  assumes a1: "cbounded_linear A"
  shows \<open>cbounded_linear (A\<^sup>\<dagger>)\<close>
proof-
  include notation_norm 
  have b1: \<open>\<langle>(A\<^sup>\<dagger>) x, y\<rangle> = \<langle>x , A y\<rangle>\<close>
    for x y
    using Adj_I a1
    by auto
  have \<open>\<langle>(A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2) , y\<rangle> = 0\<close>
    for x1 x2 y
    by (simp add: b1 cinner_diff_left cinner_left_distrib)        
  hence b2: \<open>(A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2) = 0\<close>
    for x1 x2
    using cinner_eq_zero_iff by blast
  hence z1: \<open>(A\<^sup>\<dagger>) (x1 + x2) = (A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2\<close>
    for x1 x2
    by (simp add: b2 eq_iff_diff_eq_0)

  have f1: \<open>\<langle>(A\<^sup>\<dagger>) (r *\<^sub>C x) - (r *\<^sub>C (A\<^sup>\<dagger>) x ), y\<rangle> = 0\<close>
    for r x y
  proof-
    have \<open>\<langle>(A\<^sup>\<dagger>) (r *\<^sub>C x), y\<rangle> = \<langle>r *\<^sub>C x, A y\<rangle>\<close>
      for y
      by (simp add: Adj_I assms)      
    hence \<open>\<langle>(A\<^sup>\<dagger>) (r *\<^sub>C x), y\<rangle> = (cnj r) * \<langle>x, A y\<rangle>\<close>
      for y
      by simp
    hence \<open>\<langle>(A\<^sup>\<dagger>) (r *\<^sub>C x), y\<rangle> =  \<langle>x, (cnj r) *\<^sub>C A y\<rangle>\<close>
      for y
      by simp
    hence \<open>\<langle>(A\<^sup>\<dagger>) (r *\<^sub>C x) , y\<rangle> =  (cnj r) * \<langle>x , A y\<rangle>\<close>
      for y
      by auto
    hence \<open>\<langle>(A\<^sup>\<dagger>) (r *\<^sub>C x), y\<rangle> = (cnj r) * \<langle>(A\<^sup>\<dagger>) x , y\<rangle>\<close>
      for y
      by (simp add: b1)
    hence b4: \<open>\<langle>(A\<^sup>\<dagger>) (r *\<^sub>C x) , y\<rangle> = \<langle>r *\<^sub>C (A\<^sup>\<dagger>) x , y\<rangle>\<close>
      for y
      by simp
    show ?thesis
      by (simp add: b4 cinner_diff_left)
  qed
  hence z2: \<open>(A\<^sup>\<dagger>) (r *\<^sub>C x) = r *\<^sub>C (A\<^sup>\<dagger>) x\<close>
    for r x
    using cinner_eq_zero_iff eq_iff_diff_eq_0 by blast
  have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<langle>(A\<^sup>\<dagger>) x, (A\<^sup>\<dagger>) x\<rangle>\<close>
    for x
    using power2_norm_eq_cinner' by auto
  moreover have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<ge> 0\<close>
    for x
    by simp
  ultimately have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<bar> \<langle>(A\<^sup>\<dagger>) x, (A\<^sup>\<dagger>) x\<rangle> \<bar>\<close>
    for x
    by (simp add: abs_pos)
  hence \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<bar> \<langle>x, A ((A\<^sup>\<dagger>) x)\<rangle> \<bar>\<close>
    for x
    by (simp add: b1)
  moreover have  \<open>\<bar>\<langle>x , A ((A\<^sup>\<dagger>) x)\<rangle>\<bar> \<le> \<parallel>x\<parallel> *  \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close>
    for x
    by (simp add: complex_inner_class.norm_cauchy_schwarz2)
  ultimately have b5: \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2  \<le> \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close>
    for x
    by (simp add: b1 complex_inner_class.norm_cauchy_schwarz power2_norm_eq_cinner)
  have \<open>\<exists>M. M \<ge> 0 \<and> (\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>)\<close>
    using a1
    by (metis (mono_tags, hide_lams) cbounded_linear.bounded linear mult_nonneg_nonpos
        mult_zero_right norm_ge_zero order.trans semiring_normalization_rules(7)) 
  then obtain M where q1: \<open>M \<ge> 0\<close> and q2: \<open>\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M * \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
    by blast
  have \<open>\<forall> x. \<parallel>x\<parallel> \<ge> 0\<close>
    by simp
  hence b6: \<open>\<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le>  \<parallel>x\<parallel> * M * \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
    for x
    using q2
    by (smt ordered_comm_semiring_class.comm_mult_left_mono vector_space_over_itself.scale_scale) 
  have z3: \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel> \<le> \<parallel>x\<parallel> * M\<close>
    for x
  proof(cases \<open>\<parallel>(A\<^sup>\<dagger>) x\<parallel> = 0\<close>)
    case True
    thus ?thesis
      by (simp add: \<open>0 \<le> M\<close>) 
  next
    case False
    have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
      by (smt b5 b6)
    thus ?thesis
      by (smt False mult_right_cancel mult_right_mono norm_ge_zero semiring_normalization_rules(29)) 
  qed
  show ?thesis 
    unfolding cbounded_linear_def Modules.additive_def
    using clinearI z1 z2 z3
    by auto 
qed

instantiation complex :: "chilbert_space" begin
instance ..
end

proposition dagger_dagger_id:
  fixes U :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close>
  assumes a1: "cbounded_linear U"
  shows "U\<^sup>\<dagger>\<^sup>\<dagger> = U"
proof-
  have b1: \<open>\<langle> (U\<^sup>\<dagger>) r, s \<rangle> = \<langle> r, U s \<rangle>\<close>
    for r s
    using a1
    by (simp add: Adj_I)
  have b2: \<open>\<langle> U s, r \<rangle> = \<langle> s, (U\<^sup>\<dagger>) r \<rangle>\<close>
    for r s
  proof-
    have \<open>\<langle> (U\<^sup>\<dagger>) r, s \<rangle> = cnj \<langle> s, (U\<^sup>\<dagger>) r \<rangle>\<close>
      by simp
    moreover have \<open>\<langle> r, U s \<rangle> = cnj \<langle> U s, r\<rangle>\<close>
      by simp
    ultimately have \<open>cnj \<langle> s, (U\<^sup>\<dagger>) r \<rangle> = cnj \<langle> U s, r \<rangle>\<close>
      using b1 by smt
    hence \<open>cnj (cnj \<langle> s, (U\<^sup>\<dagger>) r \<rangle>) = cnj (cnj \<langle> U s, r \<rangle>)\<close>
      by simp
    hence \<open>\<langle> s, (U\<^sup>\<dagger>) r \<rangle> = \<langle> U s, r \<rangle>\<close>
      by simp
    thus ?thesis by simp
  qed
  moreover have \<open>cbounded_linear (U\<^sup>\<dagger>)\<close>
    by (simp add: Adj_cbounded_linear a1)
  ultimately show ?thesis
    using Adj_D by fastforce
qed

lemma id_dagger: \<open>(id::'a::chilbert_space\<Rightarrow>'a)\<^sup>\<dagger> = id\<close>
proof-
  have \<open>\<langle> id x, y \<rangle> = \<langle> x, id y \<rangle>\<close>
    for x y::'a
    unfolding id_def by blast
  thus ?thesis
    using id_cbounded_linear
    by (smt Adj_D)  
qed


lemma scalar_times_adjc_flatten:
  fixes A::"'a::chilbert_space \<Rightarrow> 'b::chilbert_space"
  assumes a1: "bounded_linear A" and a2: "\<And>c x. A (c *\<^sub>C x) = c *\<^sub>C A x"
  shows \<open>(\<lambda>t. a *\<^sub>C (A t))\<^sup>\<dagger> = (\<lambda>s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s))\<close>
proof-
  have b1: \<open>bounded_linear (\<lambda> t. a *\<^sub>C (A t))\<close>
    using a1
    by (simp add: cbounded_linear.bounded_linear cbounded_linear_scaleC_right 
        bounded_linear_compose)

  have \<open>bounded_linear (A\<^sup>\<dagger>)\<close>
    using a1 a2 Adj_cbounded_linear cbounded_linear.bounded_linear bounded_linear_cbounded_linear 
    by blast
  hence b2: \<open>cbounded_linear (\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s))\<close>
    by (simp add: Adj_cbounded_linear a1 a2 cbounded_linear_const_scaleC 
        bounded_linear_cbounded_linear)

  have b3: \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = \<langle>x, (\<lambda> t. a *\<^sub>C (A t)) y \<rangle>\<close>
    for x y
  proof-
    have \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = \<langle>(cnj a) *\<^sub>C ((A\<^sup>\<dagger>) x), y \<rangle>\<close>
      by blast
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a *  \<langle>(A\<^sup>\<dagger>) x, y \<rangle>\<close>
      by simp
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a * cnj \<langle>y, (A\<^sup>\<dagger>) x\<rangle>\<close>
      by simp
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a * cnj \<langle>((A\<^sup>\<dagger>)\<^sup>\<dagger>) y, x\<rangle>\<close>
      by (simp add: Adj_I Adj_cbounded_linear assms(1) assms(2) bounded_linear_cbounded_linear)
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a * cnj (cnj \<langle>x, ((A\<^sup>\<dagger>)\<^sup>\<dagger>) y\<rangle>)\<close>
      by simp
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a * \<langle>x, ((A\<^sup>\<dagger>)\<^sup>\<dagger>) y\<rangle>\<close>
      by simp
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = a * \<langle>x, A y\<rangle>\<close>
      using Adj_I  assms(1) assms(2) bounded_linear_cbounded_linear by fastforce
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = \<langle>x, a *\<^sub>C A y\<rangle>\<close>
      by simp
    hence \<open>\<langle>(\<lambda> s. (cnj a) *\<^sub>C ((A\<^sup>\<dagger>) s)) x, y \<rangle> = \<langle>x, (\<lambda> t. a *\<^sub>C (A t)) y \<rangle>\<close>
      by simp
    thus ?thesis by blast
  qed

  have "((\<lambda>t. a *\<^sub>C A t)\<^sup>\<dagger>) b = cnj a *\<^sub>C (A\<^sup>\<dagger>) b"
    for b::'b
  proof-
    have "\<forall>t c. c *\<^sub>C a *\<^sub>C A t = a *\<^sub>C A (c *\<^sub>C t)"
      using a2 by force
    hence "cbounded_linear (\<lambda>t. a *\<^sub>C A t)"
      by (simp add: b1 bounded_linear_cbounded_linear)
    thus ?thesis
      by (metis (no_types) Adj_D b3) 
  qed
  thus ?thesis
    by blast
qed

lemma projection_D1':
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes a1: \<open>is_projection_on \<pi> M\<close> and a2: \<open>closed_subspace M\<close>
  shows \<open>\<pi> = \<pi>\<^sup>\<dagger>\<close>
proof-
  have b1: \<open>\<pi> x = (\<pi>\<^sup>\<dagger>) x\<close>
    for x
  proof-
    have d1: "\<langle>x - (\<pi>\<^sup>\<dagger>) x, y\<rangle> = 0"
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
    hence c2: "\<pi> x - (\<pi>\<^sup>\<dagger>) x \<in> orthogonal_complement M"
      by (smt Adj_I' a1 a2 cinner_diff_right is_projection_on_def minus_diff_eq
          orthogonal_complement_D2 orthogonal_complement_I1 projectionPropertiesA' 
          projection_fixed_points')
    have "\<langle> (\<pi>\<^sup>\<dagger>) x, y \<rangle> = 0"
      if "y \<in> orthogonal_complement M"
      for y
    proof-
      have \<open>\<pi> y = 0\<close>
        by (metis a1 a2 diff_0_right diff_self is_projection_on_existence 
            orthogonal_complement_twice projection_fixed_points' projection_intro1' projection_uniq' 
            subspace_orthog that)           
      hence \<open>\<langle> x, \<pi> y \<rangle> = 0\<close>
        by simp
      thus ?thesis
        using Adj_I assms projectionPropertiesA'
        by fastforce 
    qed

    hence "(\<pi>\<^sup>\<dagger>) x \<in> orthogonal_complement (orthogonal_complement M)"
      unfolding orthogonal_complement_def is_orthogonal_def
      by simp        
    hence c1: "(\<pi>\<^sup>\<dagger>) x \<in> M"
      by (simp add: assms orthogonal_complement_twice)    
    show ?thesis
      by (metis a1 a2 c1 c2 is_projection_on_def projection_fixed_points projection_uniq) 
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
  fixes f::\<open>'a::complex_inner \<Rightarrow> 'b::complex_inner\<close>
    and S::\<open>'a set\<close>
  assumes a1: "clinear f" and a2: "complex_vector.subspace S"
  shows  \<open>closed_subspace (closure {f x |x. x \<in> S})\<close>
proof -
  have b1: "complex_vector.subspace {f x |x. x \<in> S}"
    using assms Setcompr_eq_image
    by (simp add: Setcompr_eq_image complex_vector.linear_subspace_image)
  have b2: "csubspace (closure {f x |x. x \<in> S})"
    if "csubspace {f x |x. x \<in> S}"
    using that
    by (simp add: subspace_cl) 
  show \<open>closed_subspace (closure {f x |x. x \<in> S})\<close>
    using b2 b1 subspace_I by auto
qed

instantiation clinear_space :: (complex_inner) "uminus"
begin
lift_definition uminus_clinear_space::\<open>'a clinear_space  \<Rightarrow> 'a clinear_space\<close>
  is \<open>orthogonal_complement\<close>
  by simp

instance ..
end

instantiation clinear_space :: (complex_inner) "Sup"
begin
lift_definition Sup_clinear_space::\<open>'a clinear_space set \<Rightarrow> 'a clinear_space\<close>
  is \<open>\<lambda>S. closure (complex_vector.span (Union S))\<close>
proof
  show "complex_vector.subspace (closure (complex_vector.span (\<Union> S::'a set)))"
    if "\<And>x::'a set. x \<in> S \<Longrightarrow> closed_subspace x"
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


instantiation clinear_space :: ("{complex_vector,topological_space}") inf begin 
lift_definition inf_clinear_space :: "'a clinear_space \<Rightarrow> 'a clinear_space \<Rightarrow> 'a clinear_space" 
  is "(\<inter>)" by simp
instance .. end

instantiation clinear_space :: (complex_normed_vector) sup begin
lift_definition sup_clinear_space :: "'a clinear_space \<Rightarrow> 'a clinear_space \<Rightarrow> 'a clinear_space" 
  is "\<lambda>A B::'a set. A +\<^sub>M B"
  by (simp add: subspace_closed_plus) 
instance .. 
end

instantiation clinear_space :: (complex_inner) minus begin
lift_definition minus_clinear_space :: "'a clinear_space \<Rightarrow> 'a clinear_space \<Rightarrow> 'a clinear_space"
  is "\<lambda>A B. A \<inter> (orthogonal_complement B)"
  by simp
instance..
end


instantiation clinear_space :: ("{complex_vector,topological_space}") order_top begin
instance 
proof
  show "a \<le> \<top>"
    for a :: "'a clinear_space"
    apply transfer
    by simp
qed
end

instantiation clinear_space :: (chilbert_space) order_bot begin
instance 
proof
  show "(\<bottom>::'a clinear_space) \<le> a"
    for a :: "'a clinear_space"
    apply transfer
    using Complex_Vector_Spaces.subspace_0 is_closed_subspace_universal_inclusion_left 
      is_closed_subspace_zero by blast
qed
end

instantiation clinear_space :: ("{complex_vector,topological_space}") semilattice_inf begin
instance 
proof
  show "x \<sqinter> y \<le> x"
    for x :: "'a clinear_space"
      and y :: "'a clinear_space"
    apply transfer
    by simp

  show "x \<sqinter> y \<le> y"
    for x :: "'a clinear_space"
      and y :: "'a clinear_space"
    apply transfer
    by simp

  show "x \<le> y \<sqinter> z"
    if "x \<le> y"
      and "x \<le> z"
    for x :: "'a clinear_space"
      and y :: "'a clinear_space"
      and z :: "'a clinear_space"
    using that 
    apply transfer
    by simp
qed  
end


(* 
DOMINIQUE: Try if "clinear_space :: (complex_inner) lattice"
and "clinear_space :: (complex_inner) complete_lattice" (below)
work with something weaker than complex_inner
(it does not work for "clinear_space :: (complex_inner) orthocomplemented_lattice"). 

Jose: I substituted al the "chilbert_spaces" by "complex_inner", I corrected
lemma by lemma and even in that case, it does not work the elimination of the hypothesis
of completeness.

*)

instantiation clinear_space :: (chilbert_space) lattice begin
instance 
proof
  show \<open>x \<le> (sup x y)\<close>
    for x :: "'a clinear_space"
      and y :: "'a clinear_space"
    apply transfer
    by (simp add: is_closed_subspace_universal_inclusion_left)

  show "y \<le> sup x y"
    for y :: "'a clinear_space"
      and x :: "'a clinear_space"
    apply transfer
    by (simp add: is_closed_subspace_universal_inclusion_right) 

  show "sup y z \<le> x"
    if "y \<le> x" and "z \<le> x"
    for y :: "'a clinear_space"
      and x :: "'a clinear_space"
      and z :: "'a clinear_space"
    using that
    apply transfer
    using is_closed_subspace_universal_inclusion_inverse by blast 
qed
end



lemma span_superset:
  \<open>A \<subseteq> space_as_set (Span A)\<close> 
  for A :: \<open>'a::chilbert_space set\<close>
proof-
  have b1: \<open>A \<subseteq> space_as_set S\<close>
    if "S \<in> {S. A \<subseteq> space_as_set S}"
    for S
    using that
    by simp
  hence \<open>A \<subseteq> \<Inter> {space_as_set S| S. A \<subseteq> space_as_set S}\<close>
    by blast
  hence \<open>A \<subseteq> space_as_set( Inf {S| S. A \<subseteq> space_as_set S})\<close>
    using Inf_clinear_space.rep_eq by fastforce    
  thus ?thesis using span_def' by metis
qed

lemma bot_plus[simp]: "sup bot x = x" 
  for x :: "'a::chilbert_space clinear_space"
  apply transfer
  using is_closed_subspace_zero
  unfolding sup_clinear_space_def[symmetric] closed_sum_def set_plus_def
  by smt

instantiation clinear_space :: (chilbert_space) complete_lattice begin
instance 
proof
  show "Inf A \<le> x"
    if "x \<in> A"
    for x :: "'a clinear_space"
      and A :: "'a clinear_space set"
    using that 
    apply transfer
    by auto

  have b1: "z \<subseteq> \<Inter> A"
    if "Ball A closed_subspace" and
      "closed_subspace z" and
      "(\<And>x. closed_subspace x \<Longrightarrow> x \<in> A \<Longrightarrow> z \<subseteq> x)"
    for z::"'a set" and A
    using that
    by auto 
  show "z \<le> Inf A"
    if "\<And>x::'a clinear_space. x \<in> A \<Longrightarrow> z \<le> x"
    for A :: "'a clinear_space set"
      and z :: "'a clinear_space"
    using that 
    apply transfer
    using b1 by blast

  show "x \<le> Sup A"
    if "x \<in> A"
    for x :: "'a clinear_space"
      and A :: "'a clinear_space set"
    using that 
    apply transfer
    by (meson Union_upper closure_subset complex_vector.span_superset dual_order.trans)  
  have b2: "x \<in> z"
    if "\<forall>x\<in>A. closed_subspace x" and
      "closed_subspace z" and
      "\<And>x. x \<in> A \<Longrightarrow> x \<subseteq> z" and
      "x \<in> closure (cspan (\<Union> A))"
    for x::'a and z and A
    by (metis OrthoClosedEq Sup_subset_mono atMost_iff cSup_atMost closed_subspace.subspace 
        closure_mono orthogonal_complement_twice subset_iff subspace_I subspace_span_A that(2) 
        that(3) that(4))    
  show "Sup A \<le> z"
    if "\<And>x::'a clinear_space. x \<in> A \<Longrightarrow> x \<le> z"
    for A :: "'a clinear_space set"
      and z :: "'a clinear_space"
    using that 
    apply transfer
    using b2 by blast

  show "Inf {} = (top::'a clinear_space)"
    using \<open>\<And>z A. (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A\<close> top.extremum_uniqueI by auto

  show "Sup {} = (bot::'a clinear_space)"
    using \<open>\<And>z A. (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z\<close> bot.extremum_uniqueI by auto 
qed
end

instance clinear_space :: (chilbert_space) complete_orthomodular_lattice 
proof
  show "inf x (- x) = bot"
    for x :: "'a clinear_space"
    apply transfer
    by (metis Complex_Vector_Spaces.subspace_0 insert_subset 
        is_closed_subspace_universal_inclusion_left is_closed_subspace_zero ortho_inter_zero)

  have \<open>t \<in> x +\<^sub>M orthogonal_complement x\<close>
    if a1: \<open>closed_subspace x\<close>
    for t::'a and x
  proof-
    have e1: \<open>t = (projection x) t + (projection (orthogonal_complement x)) t\<close>
      using \<open>closed_subspace x\<close> ortho_decomp by blast
    have e2: \<open>(projection x) t \<in> x\<close>
      by (simp add: \<open>closed_subspace x\<close> projection_intro2)        
    have e3: \<open>(projection (orthogonal_complement x)) t \<in> orthogonal_complement x\<close>
      by (simp add: \<open>closed_subspace x\<close> projection_intro2)        
    have "orthogonal_complement x \<subseteq> x +\<^sub>M orthogonal_complement x"
      by (simp add: is_closed_subspace_universal_inclusion_right that)
    thus ?thesis
      using \<open>closed_subspace x\<close> 
        \<open>projection (orthogonal_complement x) t \<in> orthogonal_complement x\<close> \<open>projection x t \<in> x\<close>
        \<open>t = projection x t + projection (orthogonal_complement x) t\<close> in_mono 
        is_closed_subspace_universal_inclusion_left complex_vector.subspace_def
      by (metis closed_subspace.subspace subspace_closed_plus subspace_orthog) 
  qed  
  hence b1: \<open>x +\<^sub>M orthogonal_complement x = UNIV\<close>
    if a1: \<open>closed_subspace x\<close>
    for x::\<open>'a set\<close>
    using that by blast
  show "sup x (- x) = top"
    for x :: "'a clinear_space"
    apply transfer
    using b1 by auto
  show "- (- x) = x"
    for x :: "'a clinear_space"
    apply transfer
    by (simp add: orthogonal_complement_twice)

  show "- y \<le> - x"
    if "x \<le> y"
    for x :: "'a clinear_space"
      and y :: "'a clinear_space"
    using that apply transfer
    by simp 

  have c1: "x +\<^sub>M orthogonal_complement x \<inter> y \<subseteq> y"
    if "closed_subspace x"
      and "closed_subspace y"
      and "x \<subseteq> y"
    for x :: "'a set"
      and y :: "'a set"
    using that
    by (simp add: is_closed_subspace_universal_inclusion_inverse) 

  have c2: \<open>u \<in> x +\<^sub>M ((orthogonal_complement x) \<inter> y)\<close>
    if a1: "closed_subspace x" and a2: "closed_subspace y" and a3: "x \<subseteq> y" and x1: \<open>u \<in> y\<close>
    for x :: "'a set" and y :: "'a set"  and u
  proof-
    have d4: \<open>(projection x) u \<in> x\<close>
      by (simp add: a1 projection_intro2)                
    hence d2: \<open>(projection x) u \<in> y\<close>
      using a3 by auto
    have d1: \<open>csubspace y\<close>
      by (simp add: a2 closed_subspace.subspace)          
    have \<open>u - (projection x) u \<in> orthogonal_complement x\<close>
      by (simp add: a1 projection_intro1)        
    moreover have  \<open>u - (projection x) u \<in> y\<close>
      by (simp add: d1 d2 complex_vector.subspace_diff x1)      
    ultimately have d3: \<open>u - (projection x) u \<in> ((orthogonal_complement x) \<inter> y)\<close>
      by simp
    hence \<open>\<exists> v \<in> ((orthogonal_complement x) \<inter> y). u = (projection x) u + v\<close>
      by (metis d3 diff_add_cancel ordered_field_class.sign_simps(2))
    then obtain v where \<open>v \<in> ((orthogonal_complement x) \<inter> y)\<close> and \<open>u = (projection x) u + v\<close>
      by blast
    hence \<open>u \<in> x + ((orthogonal_complement x) \<inter> y)\<close>
      by (metis d4 set_plus_intro)
    thus ?thesis
      unfolding closed_sum_def
      using closure_subset by blast 
  qed

  have c3: "y \<subseteq> x +\<^sub>M ((orthogonal_complement x) \<inter> y)"
    if a1: "closed_subspace x" and a2: "closed_subspace y" and a3: "x \<subseteq> y"
    for x y :: "'a set"   
    using c2 a1 a2 a3 by auto 

  show "sup x (inf (- x) y) = y"
    if "x \<le> y"
    for x y :: "'a clinear_space"
    using that apply transfer
    using c1 c3
    by (simp add: subset_antisym)

  show "x - y = inf x (- y)"
    for x y :: "'a clinear_space"
    apply transfer
    by simp
qed


lemma bounded_sesquilinear_bounded_clinnear_cinner_right:
  assumes a1: "cbounded_linear A"
  shows   \<open>bounded_sesquilinear (\<lambda> x y. \<langle> x, A y \<rangle>)\<close>
  using a1
  by (simp add: bounded_sesquilinear.comp2 bounded_sesquilinear_cinner)

lemma bounded_sesquilinear_bounded_clinnear_cinner_left:
  assumes a1: "cbounded_linear A"
  shows \<open>bounded_sesquilinear (\<lambda> x y. \<langle> A x, y \<rangle>)\<close>
  using a1
  by (simp add: bounded_sesquilinear.comp1 bounded_sesquilinear_cinner)


subsection \<open>Unsorted\<close>

text \<open>Orthogonal set\<close>
definition is_ortho_set :: "'a::complex_inner set \<Rightarrow> bool" where
  \<open>is_ortho_set S = ((\<forall>x\<in>S. \<forall>y\<in>S. x \<noteq> y \<longrightarrow> \<langle>x, y\<rangle> = 0) \<and> (\<forall>x\<in>S. x \<noteq> 0))\<close>

lemma is_onb_delete:
  assumes "is_ortho_set (insert x B)"
  shows "is_ortho_set B"
  using assms
  unfolding  is_ortho_set_def
  by blast

lemma is_ob_nonzero:
  assumes "is_ortho_set S" and 
    "complex_vector.independent S" and
    "closure (complex_vector.span S) = UNIV" 
    and \<open>x \<in> S\<close>
  shows \<open>x \<noteq> 0\<close>
  using assms
  by (simp add: is_ortho_set_def) 


class basis_enum = complex_vector +
  fixes canonical_basis :: "'a list"
    and canonical_basis_length :: "'a itself \<Rightarrow> nat"
  assumes distinct_canonical_basis[simp]: 
    "distinct canonical_basis"
    and is_cindependent_set:
    "cindependent (set canonical_basis)"
    and is_generator_set:
    "cspan (set canonical_basis) = UNIV" 
    and canonical_basis_length_eq:
    "canonical_basis_length TYPE('a) = length canonical_basis"

setup \<open>Sign.add_const_constraint ("Complex_Vector_Spaces.cindependent", 
  SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint ("Complex_Vector_Spaces.cdependent", 
  SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint ("Complex_Vector_Spaces.cspan", 
  SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> 'a set\<close>)\<close>
setup \<open>Sign.add_const_constraint ("Complex_Vector_Spaces.complex_vector.span", 
  SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> 'a set\<close>)\<close>
  (* TODO end move *)


setup \<open>Sign.add_const_constraint (\<^const_name>\<open>is_ortho_set\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>

class onb_enum = basis_enum + complex_inner +
  assumes is_orthonormal:
    "is_ortho_set (set canonical_basis)"
    and is_normal:
    "\<And>x. x \<in> (set canonical_basis) \<Longrightarrow> norm x = 1"

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>is_ortho_set\<close>, SOME \<^typ>\<open>'a::complex_inner set \<Rightarrow> bool\<close>)\<close>


lemma canonical_basis_non_zero:
  assumes \<open>x \<in> set (canonical_basis::('a::onb_enum list))\<close>
  shows \<open>x \<noteq> 0\<close>
  using \<open>x \<in> set canonical_basis\<close> 
    complex_vector.dependent_zero[where A = "set (canonical_basis::('a::onb_enum list))"]
    is_cindependent_set
  by smt


(* TODO: move to Complex_Vector_Spaces 
  Reply: it does not work

*)
instantiation complex :: basis_enum begin
definition "canonical_basis = [1::complex]"
definition "canonical_basis_length (_::complex itself) = 1"
instance
proof
  show "distinct (canonical_basis::complex list)"
    by (simp add: canonical_basis_complex_def)    
  show "cindependent (set (canonical_basis::complex list))"
    unfolding canonical_basis_complex_def
    by auto
  show "cspan (set (canonical_basis::complex list)) = UNIV"
    unfolding canonical_basis_complex_def 
    by (auto simp add: Complex_Vector_Spaces.cspan_raw_def vector_space_over_itself.span_Basis)
  show "canonical_basis_length (TYPE(complex)::complex itself)
         = length (canonical_basis::complex list)"
    unfolding canonical_basis_complex_def canonical_basis_length_complex_def
    by auto
qed
end


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
  have \<open>(f \<circ> c) \<longlonglongrightarrow> f a\<close>
    if a1: "c \<longlonglongrightarrow> a"
    for c
  proof-
    have  \<open>(\<lambda>n. norm (c n - a)) \<longlonglongrightarrow> 0\<close>
      using a1
      by (simp add: LIM_zero_iff tendsto_norm_zero) 
    hence \<open>(\<lambda>n. norm (c n - a) * norm k ) \<longlonglongrightarrow> 0\<close>
      using tendsto_mult_left_zero by auto      
    moreover have \<open>norm ((c n - a) *\<^sub>C k) = norm (c n - a) * norm k\<close>
      for n
      by simp      
    ultimately have  \<open>(\<lambda> n. norm ((c n - a) *\<^sub>C k)) \<longlonglongrightarrow> 0\<close>
      by simp
    moreover have \<open>(c n - a) *\<^sub>C k = (c n) *\<^sub>C k - a *\<^sub>C k\<close>
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
  assumes a1: \<open>t \<longlonglongrightarrow> y\<close>
  shows \<open>(\<lambda> n. \<langle> x, t n \<rangle>) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
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
  ultimately have b1: \<open>(\<lambda> n. \<langle> x, t n - y \<rangle>) \<longlonglongrightarrow> 0\<close>
    using Limits.tendsto_0_le
    by (metis (no_types, lifting) eventually_sequentiallyI)

  have b2: \<open>\<langle> x, t n - y \<rangle> =  \<langle> x, t n \<rangle> - \<langle> x, y \<rangle>\<close>
    for n
    by (simp add: cinner_diff_right)    
  hence \<open>(\<lambda> n. \<langle> x, t n \<rangle> - \<langle> x, y \<rangle>) \<longlonglongrightarrow> 0\<close>
    using b1
    by simp
  thus ?thesis
    by (simp add: LIM_zero_iff) 
qed

lemma cinner_continuous_left:
  assumes a1: \<open>t \<longlonglongrightarrow> x\<close>
  shows \<open>(\<lambda> n. \<langle> t n, y \<rangle>) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
proof-
  have \<open>(\<lambda> n. \<langle> y, t n \<rangle>) \<longlonglongrightarrow> \<langle> y, x \<rangle>\<close>
    by (simp add: a1 cinner_continuous_right)
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
  have "l \<in> {c *\<^sub>C k| c. True}"
    if b1: "\<And>n. x n \<in> {c *\<^sub>C k| c. True}"
      and b2: "x \<longlonglongrightarrow> l"
    for x l
  proof-
    have "\<exists> c. x n = c *\<^sub>C k"
      for n
      using b1 by auto      
    hence \<open>\<exists> c. \<forall> n. x n = (c n) *\<^sub>C k\<close>
      by metis
    then obtain c where c_def: \<open>\<And> n. x n = (c n) *\<^sub>C k\<close>
      by blast
    have \<open>convergent x\<close>
      using convergentI b2 by auto 
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
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) < (e*(norm k))/(norm k)\<close>
      if z1: "e>0"
      for e
    proof-
      have  \<open>e * norm k > 0\<close>
        using z1 \<open>norm k > 0\<close>
        by simp
      thus ?thesis
        using f1 by fastforce
    qed
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) < (e*(norm k))/(norm k)\<close>
      by blast
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



lemma Gram_Schmidt:
  fixes S::"'a::complex_inner set"
  assumes a1: "finite S"
  shows "\<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> cspan A = cspan S
           \<and> 0 \<notin> A \<and> finite A"
proof-
  have  \<open>\<forall>S::'a::complex_inner set. 0\<notin>S \<and> finite S \<and> card S = n
       \<longrightarrow> (\<exists> A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> complex_vector.span A = complex_vector.span S
           \<and> 0 \<notin> A \<and> finite A)\<close> for n
  proof (induction n)
    case 0 thus ?case using card_0_eq by auto 
  next
    case (Suc n)
    have "\<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. (a::'a) \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
         \<and> complex_vector.span A = complex_vector.span S \<and> 0 \<notin> A \<and> finite A"
      if b1: \<open>0 \<notin> S\<close> and b2: \<open>finite S\<close> and b3: \<open>card S = Suc n\<close>
      for S
    proof-
      have \<open>\<exists>S' s. finite S' \<and> s\<notin>S' \<and> S = insert s S'\<close>
        by (metis b2 b3 card_Suc_eq finite_insert)
      then obtain S' s where S'1: \<open>finite S'\<close> and S'2: \<open>s\<notin>S'\<close> and S'3: \<open>S = insert s S'\<close>
        by blast
      have s1: \<open>card S' = n\<close>
        using S'1 S'2 S'3 b3 by auto
      have \<open>\<exists>A'. (\<forall>a\<in>A'. \<forall>a'\<in>A'. (a::'a) \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<and> 
          complex_vector.span A' = complex_vector.span S' \<and> 0 \<notin> A' \<and> finite A'\<close>
        using Suc.IH S'1 S'3 s1 b1 by blast                  
      then obtain A'::\<open>'a set\<close> where A'_def1: \<open>\<forall>a\<in>A'. \<forall>a'\<in>A'. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> and
        A'_def2: \<open>complex_vector.span A' = complex_vector.span S'\<close> and A'_def3: \<open>0 \<notin> A'\<close> 
        and A'_def4:\<open>finite A'\<close>
        by auto
      define \<sigma> where \<open>\<sigma> = s - (\<Sum>a'\<in>A'. ((cnj \<langle>s, a'\<rangle>)/\<langle>a', a'\<rangle>) *\<^sub>C a')\<close>
      have c2: "\<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<and> 
            complex_vector.span A = complex_vector.span S \<and> 0 \<notin> A \<and> finite A"
        if "\<sigma> = 0"
      proof-
        have \<open>s \<in> complex_vector.span A'\<close>
          unfolding \<sigma>_def
          by (metis (no_types, lifting) \<sigma>_def complex_vector.span_base complex_vector.span_scale 
              complex_vector.span_sum eq_iff_diff_eq_0 that)
        hence \<open>complex_vector.span A' = complex_vector.span S\<close>
          by (simp add: A'_def2 S'3 complex_vector.span_redundant)
        thus ?thesis
          using A'_def1 A'_def3 A'_def4 by blast                     
      qed
      define A where \<open>A = insert \<sigma> A'\<close>

      have caseI : \<open>\<langle>a, a'\<rangle> = 0\<close>
        if p1: \<open>a \<in> A\<close> and p2: \<open>a' \<in> A\<close> and p3: \<open>a' \<in> A'\<close> and p4: \<open>a \<notin> A'\<close>
        for a a'::'a
      proof-
        have \<open>a''\<in>A'-{a'} \<Longrightarrow> \<langle> a'', a' \<rangle> = 0\<close>
          for a''
          by (simp add: A'_def1 p3)  
        hence uu2: \<open>(\<Sum>a''\<in>A'-{a'}. (\<langle>s, a'\<rangle>/\<langle>a', a'\<rangle>) * \<langle> a'', a'\<rangle>) = 0\<close>
          by simp
        have r1: \<open>\<langle> ((cnj \<langle>s, a'\<rangle>)/\<langle>a', a'\<rangle>) *\<^sub>C a'', a'\<rangle> =  (\<langle>s, a'\<rangle>/\<langle>a', a'\<rangle>) * \<langle> a'', a'\<rangle>\<close>
          for a'' a'
          by simp
        have \<open>\<langle>(\<Sum>a''\<in>A'.  ((cnj \<langle>s, a''\<rangle>)/\<langle>a'', a''\<rangle>) *\<^sub>C a''), a'\<rangle>
                         = (\<Sum>a''\<in>A'. \<langle> ((cnj \<langle>s, a''\<rangle>)/\<langle>a'', a''\<rangle>) *\<^sub>C a'', a'\<rangle>)\<close>
          using cinner_sum_left by blast
        also have \<open>\<dots> = (\<Sum>a''\<in>A'.  (\<langle>s, a'\<rangle>/\<langle>a', a'\<rangle>) * \<langle> a'', a'\<rangle>)\<close>
          using r1
          by (smt A'_def1 cinner_scaleC_left mult_not_zero sum.cong p3)             
        also have \<open>\<dots> =  (\<langle>s, a'\<rangle>/\<langle>a', a'\<rangle>) * \<langle> a', a'\<rangle>
                                  + (\<Sum>a''\<in>A'-{a'}. (\<langle>s, a'\<rangle>/\<langle>a', a'\<rangle>) * \<langle> a'', a'\<rangle>)\<close>
          by (meson A'_def4 sum.remove p3)        
        also have \<open>\<dots> =  \<langle>s, a'\<rangle>\<close>
          using uu2 by auto          
        finally have uu1: \<open>\<langle>\<Sum>a''\<in>A'. ((cnj \<langle>s, a''\<rangle>)/\<langle>a'', a''\<rangle>) *\<^sub>C a'', a'\<rangle> = \<langle>s, a'\<rangle>\<close>
          by blast
        have \<open>a = \<sigma>\<close>
          using A_def p1 p4 by blast 
        hence \<open>\<langle>a, a'\<rangle> = \<langle>s - (\<Sum>a'\<in>A'.  ((cnj \<langle>s, a'\<rangle>)/\<langle>a', a'\<rangle>) *\<^sub>C a') , a'\<rangle>\<close>
          using \<sigma>_def by auto
        also have \<open>\<dots> = \<langle>s, a'\<rangle> - \<langle>(\<Sum>a'\<in>A'.  ((cnj \<langle>s, a'\<rangle>)/\<langle>a', a'\<rangle>) *\<^sub>C a'), a'\<rangle>\<close>
          by (simp add: cinner_diff_left)
        also have \<open>\<dots> = 0\<close>
          using uu1 by auto
        finally show ?thesis by blast
      qed
      have s1x: "\<langle>a, a'\<rangle> = 0"
        if w1: "a \<in> A"
          and w2: "a' \<in> A"
          and w3: "a \<noteq> a'"
          and w4: "a \<notin> A'"
        for a a'
        using A_def caseI w1 w2 w3 w4 by auto
      moreover have s1y: "\<langle>a, a'\<rangle> = 0"
        if w1: "a \<in> A"
          and w2: "a' \<in> A"
          and w3: "a \<noteq> a'"
          and w4: "a' \<notin> A'"
        for a a'
        using is_orthogonal_def orthogonal_comm s1x w1 w2 w3 w4 by blast      
      ultimately have s1: "\<langle>a, a'\<rangle> = 0"
        if w1: "a \<in> A"
          and w2: "a' \<in> A"
          and w3: "a \<noteq> a'"
          and w4: "\<not> (a \<in> A' \<and> a' \<in> A')"
        for a a'
        using that by blast      
      have z1: "\<langle>a, a'\<rangle> = 0"
        if w1: "a\<in>A" and w2: "a'\<in>A" and w3: "a \<noteq> a'"
        for a a'
        using A'_def1 s1x s1y w1 w2 w3 by blast     
      have s1: \<open>s \<in> S\<close>
        by (simp add: \<open>S = insert s S'\<close>)                  
      have S'S: \<open>S' \<subseteq> S\<close>
        by (simp add: S'3 subset_insertI)        
      hence S'Sspan: \<open>complex_vector.span S' \<subseteq> complex_vector.span S\<close>
        by (simp add: complex_vector.span_mono) 
      have xx2: \<open>a' \<in> complex_vector.span S\<close>
        if "a'\<in>A'"
        for a'
        using A'_def2 S'Sspan complex_vector.span_superset that by auto     
      hence w1: \<open>(\<Sum>a'\<in>A'. (cnj \<langle>s, a'\<rangle> / \<langle>a', a'\<rangle>) *\<^sub>C a') \<in> complex_vector.span S\<close>
        by (simp add: complex_vector.span_scale complex_vector.span_sum)
      have d1: \<open>\<sigma> \<in> complex_vector.span S\<close>
        using \<sigma>_def complex_vector.span_base complex_vector.span_diff s1 w1 by blast 
      have t1: \<open>A' \<subseteq> complex_vector.span A\<close>
        by (simp add: A_def complex_vector.span_base subsetI)                  
      moreover have \<open>complex_vector.span A \<subseteq> complex_vector.span S\<close>
        by (metis A_def xx2
            complex_vector.span_mono complex_vector.span_span d1 insert_subset subsetI)
      ultimately have d2: \<open>A' \<subseteq> complex_vector.span S\<close>
        by auto
      have d3: \<open>complex_vector.span A \<subseteq> complex_vector.span S\<close>
        by (metis A_def complex_vector.span_mono complex_vector.span_span d1 d2 insert_subset)
      have \<open>\<sigma> \<in> complex_vector.span A\<close>
        by (simp add: A_def complex_vector.span_base)
      have \<open>a' \<in> complex_vector.span A\<close>
        if "a'\<in>A'"
        for a'
        using t1 that by auto      
      hence \<open>(\<Sum>a'\<in>A'. (cnj \<langle>s, a'\<rangle> / \<langle>a', a'\<rangle>) *\<^sub>C a') \<in> complex_vector.span A\<close>
        by (simp add: complex_vector.span_scale complex_vector.span_sum)
      hence \<open>\<sigma> - s  \<in> complex_vector.span A\<close>
        unfolding \<sigma>_def
        using complex_vector.span_diff complex_vector.span_zero
        by (metis (no_types, lifting) diff_right_commute diff_self)            
      hence scs:\<open>s \<in> complex_vector.span A\<close>
        by (metis A_def complex_vector.eq_span_insert_eq complex_vector.span_base 
            complex_vector.span_redundant insertI1)        
      have A'A: \<open>A' \<subseteq> A\<close>
        by (simp add: A_def subset_insertI)
      have \<open>S' \<subseteq>  complex_vector.span S'\<close>
        using complex_vector.span_eq by auto
      hence \<open>S' \<subseteq>  complex_vector.span A'\<close>
        by (simp add: A'_def2)
      moreover have \<open>complex_vector.span A' \<subseteq> complex_vector.span A\<close>
        using A'A
        by (simp add: complex_vector.span_mono) 
      ultimately have \<open>S' \<subseteq> complex_vector.span A\<close>
        by blast
      hence d4: \<open>S \<subseteq> complex_vector.span A\<close>
        by (simp add: S'3 scs)       
      have \<open>complex_vector.span S \<subseteq> complex_vector.span A\<close>
        using d1 d2 d3 d4 complex_vector.span_mono complex_vector.span_span
        by blast 
      hence z2: \<open>complex_vector.span A = complex_vector.span S\<close>
        by (simp add: d3 set_eq_subset) 
      hence c1: "\<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) \<and> 
            complex_vector.span A = complex_vector.span S \<and> 0 \<notin> A \<and> finite A"
        if "\<sigma> \<noteq> 0"
        by (metis A'_def3 A'_def4 A_def finite.insertI insert_iff that z1)
      show ?thesis
        using c1 c2 by blast 
    qed
    thus ?case by blast        
  qed
  hence Gram_Schmidt0:
    \<open>\<exists>A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> complex_vector.span A = complex_vector.span S
           \<and> 0 \<notin> A \<and> finite A\<close>
    if b1: \<open>0 \<notin> S\<close> and b2: \<open>finite S\<close>
    for S::\<open>'a::complex_inner set\<close>
    using b1 b2 by blast    
  have \<open>0 \<notin> S - {0}\<close>
    by simp
  moreover have \<open>finite (S - {0})\<close>
    by (simp add: a1)
  ultimately have \<open>\<exists> A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> complex_vector.span A = complex_vector.span (S-{0})
           \<and> 0 \<notin> A \<and> finite A\<close>
    using Gram_Schmidt0[where S = "S - {0}"]
    by blast
  moreover have \<open>complex_vector.span (S - {0}) = complex_vector.span S\<close>
    by simp
  ultimately show ?thesis by simp
qed

lemma ortho_imples_independent:
  assumes a1: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<langle>x, y\<rangle> = 0"
    and a2: "0 \<notin> A" 
  shows "complex_vector.independent A"
proof-
  have "u v = 0"
    if b1: "finite t" and b2: "t \<subseteq> A" and b3: "(\<Sum>v\<in>t. u v *\<^sub>C v) = 0" and b4: "v \<in> t"
    for t u v
  proof-
    have "\<langle>v, v'\<rangle> = 0" 
      if c1: "v'\<in>t-{v}"
      for v'
      by (metis DiffD1 DiffD2 a1 b2 b4 singleton_iff subsetD that)    
    hence sum0: "(\<Sum>v'\<in>t-{v}. u v' * \<langle>v, v'\<rangle>) = 0"
      by simp
    have "\<langle>v, (\<Sum>v'\<in>t. u v' *\<^sub>C v')\<rangle> = (\<Sum>v'\<in>t. u v' * \<langle>v, v'\<rangle>)"
      using b1
      by (metis (mono_tags, lifting) cinner_scaleC_right cinner_sum_right sum.cong) 
    also have "\<dots> = u v * \<langle>v, v\<rangle> + (\<Sum>v'\<in>t-{v}. u v' * \<langle>v, v'\<rangle>)"
      by (meson b1 b4 sum.remove)
    also have "\<dots> = u v * \<langle>v, v\<rangle>"
      using sum0 by simp
    finally have "\<langle>v, (\<Sum>v'\<in>t. u v' *\<^sub>C v')\<rangle> =  u v * \<langle>v, v\<rangle>"
      by blast
    hence "u v * \<langle>v, v\<rangle> = 0" using b3 by simp
    moreover have "\<langle>v, v\<rangle> \<noteq> 0"
      using a2 b2 b4 by auto    
    ultimately show "u v = 0" by simp
  qed
  thus ?thesis using independent_explicit_module
    by (smt cdependent_raw_def)
qed



lemma complex_real_span:
  "complex_vector.span B = real_vector.span (B \<union> scaleC \<i> ` B)"
proof auto
  let ?cspan = complex_vector.span
  let ?rspan = real_vector.span
  fix \<psi>
  assume cspan: "\<psi> \<in> ?cspan B"
  have "\<exists>B' r. finite B' \<and> B' \<subseteq> B \<and> \<psi> = (\<Sum>b\<in>B'. r b *\<^sub>C b)"
    using complex_vector.span_explicit[of B] cspan
    by auto
  then obtain B' r where "finite B'" and "B' \<subseteq> B" and \<psi>_explicit: "\<psi> = (\<Sum>b\<in>B'. r b *\<^sub>C b)"
    by atomize_elim 
  define R where "R = B \<union> scaleC \<i> ` B"

  have x2: "(case x of (b, i) \<Rightarrow> if i 
            then Im (r b) *\<^sub>R \<i> *\<^sub>C b 
            else Re (r b) *\<^sub>R b) \<in> span (B \<union> (*\<^sub>C) \<i> ` B)"
    if "x \<in> B' \<times> (UNIV::bool set)"
    for x :: "'a \<times> bool"
    using that \<open>B' \<subseteq> B\<close> by (auto simp add: real_vector.span_base real_vector.span_scale subset_iff)
  have x1: "\<psi> = (\<Sum>x\<in>B'. \<Sum>i\<in>UNIV. if i then Im (r x) *\<^sub>R \<i> *\<^sub>C x else Re (r x) *\<^sub>R x)"
    if "\<And>b. r b *\<^sub>C b = Re (r b) *\<^sub>R b + Im (r b) *\<^sub>R \<i> *\<^sub>C b"
    using that by (simp add: UNIV_bool \<psi>_explicit)
  moreover have "r b *\<^sub>C b = Re (r b) *\<^sub>R b + Im (r b) *\<^sub>R \<i> *\<^sub>C b" for b
    using complex_eq scaleC_add_left scaleC_scaleC scaleR_scaleC
    by (metis (no_types, lifting) complex_of_real_i i_complex_of_real)
  ultimately have "\<psi> = (\<Sum>(b,i)\<in>(B'\<times>UNIV). if i then Im (r b) *\<^sub>R (\<i> *\<^sub>C b) else Re (r b) *\<^sub>R b)"
    by (simp add: sum.cartesian_product)     
  also have "\<dots> \<in> ?rspan R"
    unfolding R_def
    using x2
    by (rule real_vector.span_sum) 
  finally show "\<psi> \<in> ?rspan R" by -
next
  let ?cspan = complex_vector.span
  let ?rspan = real_vector.span
  define R where "R = B \<union> scaleC \<i> ` B"
  fix \<psi>
  assume rspan: "\<psi> \<in> ?rspan R"
  have "subspace {a. a \<in> cspan B}"
    by (rule real_vector.subspaceI, auto simp add: complex_vector.span_zero 
        complex_vector.span_add_eq2 complex_vector.span_scale scaleR_scaleC)
  moreover have "x \<in> cspan B"
    if "x \<in> R"
    for x :: 'a
    using that R_def complex_vector.span_base complex_vector.span_scale by fastforce
  ultimately show "\<psi> \<in> ?cspan B"
    using real_vector.span_induct rspan by blast  
qed

lemma finite_span_complete_aux:
  fixes b :: "'b::real_normed_vector" and B :: "'b set"
    and  rep :: "'basis::finite \<Rightarrow> 'b" and abs :: "'b \<Rightarrow> 'basis"
  assumes t: "type_definition rep abs B"
    and t1: "finite B" and t2: "b\<in>B" and t3: "independent B"
  shows "\<exists>D>0. \<forall>\<psi>. norm (real_vector.representation B \<psi> b) \<le> norm \<psi> * D"
    and "complete (real_vector.span B)"

  text \<open>This auxiliary lemma shows more or less the same as \<open>finite_span_representation_bounded\<close>
     \<open>finite_span_complete\<close> below (see there for an intuition about the mathematical 
     content of the lemmas. However, there is one difference: We additionally assume here
     that there is a bijection rep/abs between a finite type \<^typ>\<open>'basis\<close> and the set $B$.
     This is needed to be able to use results about euclidean spaces that are formulated w.r.t.
     the type class \<^class>\<open>finite\<close>

     Since we anyway assume that $B$ is finite, this added assumption does not make the lemma
     weaker. However, we cannot derive the existence of \<^typ>\<open>'basis\<close> inside the proof
     (HOL does not support such reasoning). Therefore we have the type \<^typ>\<open>'basis\<close> as
     an explicit assumption and remove it using @{attribute internalize_sort} after the proof.\<close>

proof -
  define repr  where "repr = real_vector.representation B"
  define repr' where "repr' \<psi> = Abs_euclidean_space (repr \<psi> o rep)" for \<psi>
  define comb  where "comb l = (\<Sum>b\<in>B. l b *\<^sub>R b)" for l
  define comb' where "comb' l = comb (Rep_euclidean_space l o abs)" for l

  have comb_cong: "comb x = comb y" if "\<And>z. z\<in>B \<Longrightarrow> x z = y z" for x y
    unfolding comb_def using that by auto
  have comb_repr[simp]: "comb (repr \<psi>) = \<psi>" if "\<psi> \<in> real_vector.span B" for \<psi>
    using \<open>comb \<equiv> \<lambda>l. \<Sum>b\<in>B. l b *\<^sub>R b\<close> local.repr_def real_vector.sum_representation_eq t1 t3 that 
    by fastforce    

  have w5:"(\<Sum>b | (b \<in> B \<longrightarrow> x b \<noteq> 0) \<and> b \<in> B. x b *\<^sub>R b) =
    (\<Sum>b\<in>B. x b *\<^sub>R b)"
    for x
    using \<open>finite B\<close>
    by (smt DiffD1 DiffD2 mem_Collect_eq real_vector.scale_eq_0_iff subset_eq sum.mono_neutral_left)
  have "representation B (\<Sum>b\<in>B. x b *\<^sub>R b) =  (\<lambda>b. if b \<in> B then x b else 0)"
    for x
  proof (rule real_vector.representation_eqI)
    show "independent B"
      by (simp add: t3)      
    show "(\<Sum>b\<in>B. x b *\<^sub>R b) \<in> span B"
      by (meson real_vector.span_scale real_vector.span_sum real_vector.span_superset subset_iff)      
    show "b \<in> B"
      if "(if b \<in> B then x b else 0) \<noteq> 0"
      for b :: 'b
      using that
      by meson 
    show "finite {b. (if b \<in> B then x b else 0) \<noteq> 0}"
      using t1 by auto      
    show "(\<Sum>b | (if b \<in> B then x b else 0) \<noteq> 0. (if b \<in> B then x b else 0) *\<^sub>R b) = (\<Sum>b\<in>B. x b *\<^sub>R b)"
      using w5
      by simp
  qed
  hence repr_comb[simp]: "repr (comb x) = (\<lambda>b. if b\<in>B then x b else 0)" for x
    unfolding repr_def comb_def.
  have repr_bad[simp]: "repr \<psi> = (\<lambda>_. 0)" if "\<psi> \<notin> real_vector.span B" for \<psi>
    unfolding repr_def using that
    by (simp add: real_vector.representation_def)
  have [simp]: "repr' \<psi> = 0" if "\<psi> \<notin> real_vector.span B" for \<psi>
    unfolding repr'_def repr_bad[OF that]
    apply transfer
    by auto
  have comb'_repr'[simp]: "comb' (repr' \<psi>) = \<psi>" 
    if "\<psi> \<in> real_vector.span B" for \<psi>
  proof -
    have x1: "(repr \<psi> \<circ> rep \<circ> abs) z = repr \<psi> z"
      if "z \<in> B"
      for z
      unfolding o_def
      using t that type_definition.Abs_inverse by fastforce
    have "comb' (repr' \<psi>) = comb ((repr \<psi> \<circ> rep) \<circ> abs)"
      unfolding comb'_def repr'_def
      by (subst Abs_euclidean_space_inverse; simp)
    also have "\<dots> = comb (repr \<psi>)"
      using x1 comb_cong by blast
    also have "\<dots> = \<psi>"
      using that by simp
    finally show ?thesis by -
  qed

  have t1: "Abs_euclidean_space (Rep_euclidean_space t) = t"
    if "\<And>x. rep x \<in> B"
    for t::"'a euclidean_space"
    apply (subst Rep_euclidean_space_inverse)
    by simp
  have "Abs_euclidean_space
     (\<lambda>y. if rep y \<in> B 
           then Rep_euclidean_space x y
           else 0) = x"
    for x
    using type_definition.Rep[OF t] apply simp
    using t1 by blast
  hence "Abs_euclidean_space
     (\<lambda>y. if rep y \<in> B
           then Rep_euclidean_space x (abs (rep y))
           else 0) = x"
    for x
    apply (subst type_definition.Rep_inverse[OF t])
    by simp
  hence repr'_comb'[simp]: "repr' (comb' x) = x" for x
    unfolding comb'_def repr'_def o_def
    by simp
  have sphere: "compact (sphere 0 d :: 'basis euclidean_space set)" 
    for d
    using compact_sphere by blast
  have "complete (UNIV :: 'basis euclidean_space set)"
    by (simp add: complete_UNIV)


  have "(\<Sum>b\<in>B. (Rep_euclidean_space (x + y) \<circ> abs) b *\<^sub>R b) = (\<Sum>b\<in>B. (Rep_euclidean_space x \<circ> abs) b *\<^sub>R b) + (\<Sum>b\<in>B. (Rep_euclidean_space y \<circ> abs) b *\<^sub>R b)"
    for x :: "'basis euclidean_space"
      and y :: "'basis euclidean_space"
    apply (transfer fixing: abs)
    by (simp add: scaleR_add_left sum.distrib)
  moreover have "(\<Sum>b\<in>B. (Rep_euclidean_space (c *\<^sub>R x) \<circ> abs) b *\<^sub>R b) = c *\<^sub>R (\<Sum>b\<in>B. (Rep_euclidean_space x \<circ> abs) b *\<^sub>R b)"
    for c :: real
      and x :: "'basis euclidean_space"
    apply (transfer fixing: abs)
    by (simp add: real_vector.scale_sum_right)
  ultimately have blin_comb': "bounded_linear comb'"
    unfolding comb_def comb'_def 
    by (rule bounded_linearI')
  hence "continuous_on X comb'" for X
    by (simp add: linear_continuous_on)
  hence "compact (comb' ` sphere 0 d)" for d
    using sphere
    by (rule compact_continuous_image)
  hence compact_norm_comb': "compact (norm ` comb' ` sphere 0 1)"
    using compact_continuous_image continuous_on_norm_id by blast
  have not0: "0 \<notin> norm ` comb' ` sphere 0 1"
  proof (rule ccontr, simp)
    assume "0 \<in> norm ` comb' ` sphere 0 1"
    then obtain x where nc0: "norm (comb' x) = 0" and x: "x \<in> sphere 0 1"
      by auto
    hence "comb' x = 0"
      by simp
    hence "repr' (comb' x) = 0"
      unfolding repr'_def o_def repr_def apply simp
      by (smt repr'_comb' blin_comb' dist_0_norm linear_simps(3) mem_sphere norm_zero x)
    hence "x = 0"
      by auto
    with x show False
      by simp
  qed

  have "closed (norm ` comb' ` sphere 0 1)"
    using compact_imp_closed compact_norm_comb' by blast    
  moreover have "0 \<notin> norm ` comb' ` sphere 0 1"
    by (simp add: not0)    
  ultimately have "\<exists>d>0. \<forall>x\<in>norm ` comb' ` sphere 0 1. d \<le> dist 0 x"
    by (meson separate_point_closed)

  then obtain d where d: "x\<in>norm ` comb' ` sphere 0 1 \<Longrightarrow> d \<le> dist 0 x"  
    and "d > 0" for x
    by metis
  define D where "D = 1/d"
  hence "D > 0"
    using \<open>d>0\<close> unfolding D_def by auto
  have "x \<ge> d"  
    if "x\<in>norm ` comb' ` sphere 0 1" 
    for x
    using d that
    apply auto
    by fastforce
  hence *: "norm (comb' x) \<ge> d" if "norm x = 1" for x
    using that by auto
  have norm_comb': "norm (comb' x) \<ge> d * norm x" for x
  proof (cases "x=0")
    show "d * norm x \<le> norm (comb' x)"
      if "x = 0"
      using that
      by simp 
    show "d * norm x \<le> norm (comb' x)"
      if "x \<noteq> 0"
      using that
      using *[of "(1/norm x) *\<^sub>R x"]
      unfolding linear_simps(5)[OF blin_comb']
      apply auto
      by (simp add: le_divide_eq)
  qed

  have *:  "norm (repr' \<psi>) \<le> norm \<psi> * D" for \<psi>
  proof (cases "\<psi> \<in> real_vector.span B")
    show "norm (repr' \<psi>) \<le> norm \<psi> * D"
      if "\<psi> \<in> span B"
      using that     unfolding D_def
      using norm_comb'[of "repr' \<psi>"] \<open>d>0\<close>
      by (simp_all add: linordered_field_class.mult_imp_le_div_pos mult.commute)

    show "norm (repr' \<psi>) \<le> norm \<psi> * D"
      if "\<psi> \<notin> span B"
      using that \<open>0 < D\<close> by auto 
  qed

  hence "norm (Rep_euclidean_space (repr' \<psi>) (abs b)) \<le> norm \<psi> * D" for \<psi>
  proof -
    have "(Rep_euclidean_space (repr' \<psi>) (abs b)) = repr' \<psi> \<bullet> euclidean_space_basis_vector (abs b)"
      apply (transfer fixing: abs b)
      by auto
    also have "\<bar>\<dots>\<bar> \<le> norm (repr' \<psi>)"
      apply (rule Basis_le_norm)
      unfolding Basis_euclidean_space_def by simp
    also have "\<dots> \<le> norm \<psi> * D"
      using * by auto
    finally show ?thesis by simp
  qed
  hence "norm (repr \<psi> b) \<le> norm \<psi> * D" for \<psi>
    unfolding repr'_def
    by (smt \<open>comb' \<equiv> \<lambda>l. comb (Rep_euclidean_space l \<circ> abs)\<close> 
        \<open>repr' \<equiv> \<lambda>\<psi>. Abs_euclidean_space (repr \<psi> \<circ> rep)\<close> comb'_repr' comp_apply norm_le_zero_iff 
        repr_bad repr_comb)     
  thus "\<exists>D>0. \<forall>\<psi>. norm (repr \<psi> b) \<le> norm \<psi> * D"
    using \<open>D>0\<close> by auto
  from \<open>d>0\<close>
  have complete_comb': "complete (comb' ` UNIV)"
  proof (rule complete_isometric_image)
    show "subspace (UNIV::'basis euclidean_space set)"
      by simp      
    show "bounded_linear comb'"
      by (simp add: blin_comb')      
    show "\<forall>x\<in>UNIV. d * norm x \<le> norm (comb' x)"
      by (simp add: norm_comb')      
    show "complete (UNIV::'basis euclidean_space set)"
      by (simp add: \<open>complete UNIV\<close>)      
  qed

  have range_comb': "comb' ` UNIV = real_vector.span B"
  proof (auto simp: image_def)
    show "comb' x \<in> real_vector.span B" for x
      by (metis comb'_def comb_cong comb_repr local.repr_def repr_bad repr_comb real_vector.representation_zero real_vector.span_zero)
  next
    fix \<psi> assume "\<psi> \<in> real_vector.span B"
    then obtain f where f: "comb f = \<psi>"
      apply atomize_elim
      unfolding real_vector.span_finite[OF \<open>finite B\<close>] comb_def
      by auto
    define f' where "f' b = (if b\<in>B then f b else 0)" for b :: 'b
    have f': "comb f' = \<psi>"
      unfolding f[symmetric]
      apply (rule comb_cong)
      unfolding f'_def by simp
    define x :: "'basis euclidean_space" where "x = Abs_euclidean_space (f' o rep)"
    have "\<psi> = comb' x"
      by (metis (no_types, lifting) \<open>\<psi> \<in> span B\<close> \<open>repr' \<equiv> \<lambda>\<psi>. Abs_euclidean_space (repr \<psi> \<circ> rep)\<close> 
          comb'_repr' f' fun.map_cong repr_comb t type_definition.Rep_range x_def)
    thus "\<exists>x. \<psi> = comb' x"
      by auto
  qed

  from range_comb' complete_comb'
  show "complete (real_vector.span B)"
    by simp
qed


lemma finite_span_complete:
  fixes A :: "'a::real_normed_vector set"
  assumes "finite A"
  shows "complete (real_vector.span A)"
  text \<open>The span of a finite set is complete.\<close>
proof (cases "A \<noteq> {} \<and> A \<noteq> {0}")
  case True
  obtain B where
    BT: "real_vector.span B = real_vector.span A"
    and "independent B"  
    and "finite B"
    by (meson True assms finite_subset real_vector.maximal_independent_subset real_vector.span_eq
        real_vector.span_superset subset_trans)

  have "B\<noteq>{}"
    apply (rule ccontr, simp)
    using BT True
    by (metis real_vector.span_superset real_vector.span_empty subset_singletonD)

(* The following generalizes finite_span_complete_aux to hold without the assumption
     that 'basis has type class finite *)
  {
    (* The type variable 'basisT must not be the same as the one used in finite_span_complete_aux,
       otherwise "internalize_sort" below fails *)
    assume "\<exists>(Rep :: 'basisT\<Rightarrow>'a) Abs. type_definition Rep Abs B"
    then obtain rep :: "'basisT \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'basisT" where t: "type_definition rep abs B"
      by auto
    have basisT_finite: "class.finite TYPE('basisT)"
      apply intro_classes
      using \<open>finite B\<close> t
      by (metis (mono_tags, hide_lams) ex_new_if_finite finite_imageI image_eqI type_definition_def)
    note finite_span_complete_aux(2)[internalize_sort "'basis::finite"]
    note this[OF basisT_finite t]
  }
  note this[cancel_type_definition, OF \<open>B\<noteq>{}\<close> \<open>finite B\<close> _ \<open>independent B\<close>]
  hence "complete (real_vector.span B)"
    using \<open>B\<noteq>{}\<close> by auto
  thus "complete (real_vector.span A)"
    unfolding BT by simp
next
  case False
  thus ?thesis
    using complete_singleton by auto
qed


lemma finite_cspan_complete: 
  fixes B :: "'a::complex_normed_vector set"
  assumes "finite B"
  shows "complete (complex_vector.span B)"
proof (subst complex_real_span)
  show "complete (span (B \<union> (*\<^sub>C) \<i> ` B))"
    by (simp add: assms finite_span_complete)
qed

lemma finite_span_closed: 
  fixes B :: "'a::real_normed_vector set"
  assumes "finite B"
  shows "closed (real_vector.span B)"
  by (simp add: assms complete_imp_closed finite_span_complete) 

lemma closed_finite_dim:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes a1: \<open>finite S\<close>
  shows \<open>closed (complex_vector.span S)\<close>  
  by (simp add: finite_cspan_complete assms complete_imp_closed)

lemma is_ortho_set_independent:
  assumes c1: "is_ortho_set S"
  shows "cindependent S"
proof(rule ccontr)
  assume constr: "\<not> cindependent S"
  have \<open>\<exists>t u. finite t \<and> t \<subseteq> S \<and> (\<Sum>i\<in>t. u i *\<^sub>C i) = 0 \<and> (\<exists>i\<in>t. u i \<noteq> 0)\<close>
    using complex_vector.dependent_explicit constr by blast 
  then obtain t u where u1: \<open>finite t\<close> and u2: \<open>t \<subseteq> S\<close> and u3: \<open>(\<Sum>i\<in>t. u i *\<^sub>C i) = 0\<close> 
    and u4: \<open>\<exists>k\<in>t. u k \<noteq> 0\<close>
    by blast
  from \<open>\<exists>k\<in>t. u k \<noteq> 0\<close>
  obtain k where \<open>u k \<noteq> 0\<close> and \<open>k\<in>t\<close>
    by blast
  have \<open>bounded_sesquilinear cinner\<close>
    by (simp add: bounded_sesquilinear_cinner)
  hence \<open>\<langle>(\<Sum>i\<in>t. u i *\<^sub>C i), k\<rangle> = (\<Sum>i\<in>t. cnj (u i) *\<^sub>C \<langle>i,k\<rangle>)\<close>
    using \<open>finite t\<close> sesquilinear_finite_sum
    by blast
  hence v1: \<open>(\<Sum>i\<in>t. cnj (u i) *\<^sub>C \<langle>i,k\<rangle>) = 0\<close>
    by (simp add: \<open>(\<Sum>i\<in>t. u i *\<^sub>C i) = 0\<close>)
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
  ultimately have v2: \<open>(\<Sum>i\<in>t. cnj (u i) *\<^sub>C \<langle>i,k\<rangle>) = cnj (u k) *\<^sub>C \<langle>k,k\<rangle> + (\<Sum>i\<in>(t-{k}). cnj (u i) *\<^sub>C \<langle>i,k\<rangle>)\<close>
    by simp
  have \<open>cnj (u i) *\<^sub>C \<langle>i,k\<rangle> = 0\<close>
    if "i \<in> t-{k}"
    for i
    by (metis DiffD1 DiffD2 \<open>k \<in> t\<close> c1 complex_vector.scale_eq_0_iff in_mono is_ortho_set_def 
        singletonI that u2)  
  hence v3: \<open>(\<Sum>i\<in>(t-{k}). cnj (u i) *\<^sub>C \<langle>i,k\<rangle>) = 0\<close>
    by (meson sum.not_neutral_contains_not_neutral)  
  have y1: \<open>cnj (u k) *\<^sub>C \<langle>k,k\<rangle> = 0\<close>
    using v1 v2 v3 by auto  
  have \<open>0 \<notin> t\<close>
    using \<open>t \<subseteq> S\<close>
    by (meson c1 in_mono is_ortho_set_def) 
  hence \<open>k \<noteq> 0\<close>
    using \<open>k \<in> t\<close>
    by blast
  hence y2: \<open>\<langle>k,k\<rangle> \<noteq> 0\<close>
    by simp 
  have \<open>cnj (u k) = 0\<close>
    using y1 y2 by auto    
  hence \<open>u k = 0\<close>
    by auto
  thus False using \<open>u k \<noteq> 0\<close> by blast
qed

subsection \<open>Commutative monoid of subspaces\<close>

instantiation clinear_space :: (chilbert_space) comm_monoid_add begin
definition plus_clinear_space :: "'a clinear_space \<Rightarrow> _ \<Rightarrow> _"
  where [simp]: "plus_clinear_space = sup"
instance 
proof
  show "a + b + c = a + (b + c)"
    for a :: "'a clinear_space"
      and b :: "'a clinear_space"
      and c :: "'a clinear_space"
    using sup.assoc by auto    
  show "a + b = b + a"
    for a :: "'a clinear_space"
      and b :: "'a clinear_space"
    by (simp add: sup.commute)    
  show "(0::'a clinear_space) + a = a"
    for a :: "'a clinear_space"
    by simp    
qed

end

lemma Pythagorean_generalized:
  assumes q1: "\<And>a a'. a \<in> t \<Longrightarrow> a' \<in> t \<Longrightarrow> a \<noteq> a' \<Longrightarrow> \<langle>f a, f a'\<rangle> = 0"
    and q2: "finite t"
  shows "(norm  (\<Sum>a\<in>t. f a))^2 = (\<Sum>a\<in>t.(norm (f a))^2)"
  using q2
proof (insert q1, induction)
  case empty
  show ?case
    by auto 
next
  case (insert x F)
  have r1: "\<langle>f x, f a\<rangle> = 0"
    if "a \<in> F"
    for a
    using that insert.hyps(2) insert.prems by auto 
  have "sum f F = (\<Sum>a\<in>F. f a)"
    by simp
  hence s4: "\<langle>f x, sum f F\<rangle> = \<langle>f x, (\<Sum>a\<in>F. f a)\<rangle>"
    by simp
  also have s3: "\<dots> = (\<Sum>a\<in>F. \<langle>f x, f a\<rangle>)"
    using cinner_sum_right by auto
  also have s2: "\<dots> = (\<Sum>a\<in>F. 0)"
    using r1
    by simp
  also have s1: "\<dots> = 0"
    by simp
  finally have xF_ortho: "\<langle>f x, sum f F\<rangle> = 0"
    using s2 s3 by auto       
  have "(norm (sum f (insert x F)))\<^sup>2 = (norm (f x + sum f F))\<^sup>2"
    by (simp add: insert.hyps(1) insert.hyps(2))
  also have "\<dots> = (norm (f x))\<^sup>2 + (norm (sum f F))\<^sup>2"
    using xF_ortho by (rule PythagoreanId)
  also have "\<dots> = (norm (f x))\<^sup>2 + (\<Sum>a\<in>F.(norm (f a))^2)"
    apply (subst insert.IH) using insert.prems by auto
  also have "\<dots> = (\<Sum>a\<in>insert x F.(norm (f a))^2)"
    by (simp add: insert.hyps(1) insert.hyps(2))
  finally show ?case
    by simp
qed


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


lemma has_derivative_norm[derivative_intros]:
  fixes x :: "'a::complex_inner"
  assumes "x \<noteq> 0" 
  shows "(norm has_derivative (\<lambda>y. Re \<langle>x, y\<rangle> / norm x)) (at x)"
proof -
  have Re_pos: "0 < Re \<langle>x, x\<rangle>"
    using assms 
    by (metis Re_strict_mono cinner_gt_zero_iff zero_complex.simps(1))
  have Re_plus_Re: "Re \<langle>x, y\<rangle> + Re \<langle>y, x\<rangle> = 2 * Re \<langle>x, y\<rangle>" 
    for x y :: 'a
    by (metis cinner_commute cnj.simps(1) mult_2_right semiring_normalization_rules(7))
  have norm: "norm x = sqrt (Re \<langle>x, x\<rangle>)" for x :: 'a
    apply (subst norm_eq_sqrt_cinner, subst cmod_Re)
    by auto
  have v2:"((\<lambda>x. sqrt (Re \<langle>x, x\<rangle>)) has_derivative
          (\<lambda>xa. (Re \<langle>x, xa\<rangle> + Re \<langle>xa, x\<rangle>) * (inverse (sqrt (Re \<langle>x, x\<rangle>)) / 2))) (at x)" 
    by (rule derivative_eq_intros | simp add: Re_pos)+
  have v1: "((\<lambda>x. sqrt (Re \<langle>x, x\<rangle>)) has_derivative (\<lambda>y. Re \<langle>x, y\<rangle> / sqrt (Re \<langle>x, x\<rangle>))) (at x)"
    if "((\<lambda>x. sqrt (Re \<langle>x, x\<rangle>)) has_derivative (\<lambda>xa. Re \<langle>x, xa\<rangle> * inverse (sqrt (Re \<langle>x, x\<rangle>)))) (at x)"
    using that apply (subst divide_real_def)
    by simp
  show ?thesis
    using v2
    apply (auto simp: Re_plus_Re norm [abs_def])
    using v1 by blast    
qed


lemma cinner_ext_0: 
  assumes "\<And>\<gamma>. \<langle>\<gamma>, \<psi>\<rangle> = 0"
  shows "\<psi> = 0"
  using assms cinner_eq_zero_iff by blast

text \<open>This is a useful rule for establishing the equality of vectors\<close>
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

lemma clinear_space_member_inf[simp]:
  "x \<in> space_as_set (A \<sqinter> B) \<longleftrightarrow> x \<in> space_as_set A \<and> x \<in> space_as_set B"
  apply transfer by simp

lemma clinear_space_top_not_bot[simp]: 
  "(top::'a::{complex_vector,t1_space,not_singleton} clinear_space) \<noteq> bot"
  (* The type class t1_space is needed because the definition of bot in clinear_space needs it *)
  by (metis UNIV_not_singleton bot_clinear_space.rep_eq top_clinear_space.rep_eq)

lemma clinear_space_bot_not_top[simp]:
  "(bot::'a::{complex_vector,t1_space,not_singleton} clinear_space) \<noteq> top"
  using clinear_space_top_not_bot by metis

subsection\<open>NSA miscellany\<close>

unbundle nsa_notation

subsection \<open>Boundeness\<close>

lemma nsbounded_existencial:
  \<open>(\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite) \<longleftrightarrow> (\<exists>x. ((*f2* dist) x) ` (*s* S) \<subseteq> HFinite)\<close>
  for S::\<open>'a::metric_space set\<close>
proof
  show "\<exists>x. (*f2* dist) x ` (*s* S) \<subseteq> HFinite"
    if "\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite"
    using that image_subset_iff  by fastforce
  show "\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite"
    if "\<exists>x. (*f2* dist) x ` (*s* S) \<subseteq> HFinite"
  proof-
    obtain z where \<open>(*f2* dist) z ` (*s* S) \<subseteq> HFinite\<close>
      using \<open>\<exists>x. (*f2* dist) x ` (*s* S) \<subseteq> HFinite\<close> by blast
    have \<open>(*f2* dist) x y \<in> HFinite\<close>
      if u1: \<open>x\<in>*s* S\<close> and u2: \<open>y\<in>*s* S\<close>
      for x y
    proof-
      have \<open>\<forall> xx yy zz. dist xx yy \<le> dist xx zz + dist zz yy\<close>
        by (simp add: dist_triangle)
      hence \<open>\<forall> xx yy zz. (*f2* dist) xx yy \<le> (*f2* dist) xx zz + (*f2* dist) zz yy\<close>
        by StarDef.transfer
      hence z1: \<open>(*f2* dist) x y \<le> (*f2* dist) x z + (*f2* dist) z y\<close>
        by blast
      have l1:  \<open>(*f2* dist) z x \<in> HFinite\<close>
        using \<open>(*f2* dist) z ` (*s* S) \<subseteq> HFinite\<close> \<open>x\<in>*s* S \<close> 
        by blast
      have \<open>\<forall> zz xx. dist zz xx = dist xx zz\<close>
        using dist_commute by blast
      hence \<open>\<forall> zz xx. (*f2* dist) zz xx = (*f2* dist) xx zz\<close>
        by StarDef.transfer
      hence l2: \<open>(*f2* dist) z x = (*f2* dist) x z\<close>
        by blast
      have  \<open>(*f2* dist) x z \<in> HFinite\<close>
        using l1 l2 by auto        
      moreover have  \<open>(*f2* dist) z y \<in> HFinite\<close>
        using \<open>(*f2* dist) z ` (*s* S) \<subseteq> HFinite\<close> \<open>y\<in>*s* S \<close> 
        by blast
      ultimately have z2: \<open>(*f2* dist) x z + (*f2* dist) z y \<in> HFinite\<close>
        by (simp add: HFinite_add)
      have \<open>\<forall> xx yy. 0 \<le> dist xx yy\<close>
        by simp
      hence \<open>\<forall> xx yy. 0 \<le> (*f2* dist) xx yy\<close>
        by StarDef.transfer
      hence z3: \<open>0 \<le> (*f2* dist) x y\<close>
        by (simp add: \<open>\<forall>xx yy. 0 \<le> (*f2* dist) xx yy\<close>) 
      show ?thesis
        using HFinite_bounded z1 z2 z3 by blast  
    qed
    thus ?thesis by blast
  qed
qed

lemma nsbounded_I:
  \<open>\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite \<Longrightarrow> \<exists>x. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
  by blast

lemma nsbounded_D:
  \<open>\<exists>x. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite \<Longrightarrow> \<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
  by (meson image_subsetI nsbounded_existencial)

lemma bounded_nsbounded:
  fixes S :: \<open>('a::metric_space) set\<close>
  assumes h1: \<open>bounded S\<close> and h2: "x\<in>*s* S" and h3: "y\<in>*s* S"
  shows \<open>(*f2* dist) x y \<in> HFinite\<close>
proof- 
  have \<open>\<exists>M. \<exists> u. \<forall> v \<in> S. dist u v < M\<close>
    using h1
    by (meson bounded_def gt_ex le_less_trans)
  then obtain M where \<open>\<exists> u. \<forall> v \<in> S. dist u v < M\<close>
    by blast
  hence \<open>\<exists> u. \<forall> v \<in> *s* S. (*f2* dist) u v < hypreal_of_real M\<close>
    by StarDef.transfer
  then obtain u where u_def: \<open>\<And>v. v \<in> *s* S \<Longrightarrow> (*f2* dist) u v < hypreal_of_real M\<close>
    by blast
  have \<open>(*f2* dist) u v \<in> HFinite\<close>
    if \<open>v \<in> *s* S\<close>
    for v
  proof-
    have q1: \<open>(*f2* dist) u v < hypreal_of_real M\<close>
      by (simp add: u_def that)
    have \<open>\<forall> uu vv. norm (dist uu vv) =  dist uu vv\<close>
      by simp         
    hence \<open>\<forall> uu vv. hnorm ((*f2* dist) uu vv) =  (*f2* dist) uu vv\<close>
      by StarDef.transfer
    hence q2: \<open>hnorm ((*f2* dist) u v) = (*f2* dist) u v\<close>
      by blast
    show \<open>(*f2* dist) u v \<in> HFinite\<close>
      using q1 q2
      by (metis HInfiniteD HInfinite_HFinite_disj SReal_hypreal_of_real order.asym) 
  qed  
  thus ?thesis
    using nsbounded_D h2 h3 by auto   
qed

lemma nsbounded_bounded:
  fixes S :: \<open>'a::metric_space set\<close>
  assumes a1: "\<And>x y. x\<in>*s* S \<Longrightarrow> y\<in>*s* S \<Longrightarrow> (*f2* dist) x y \<in> HFinite"
  shows \<open>bounded S\<close>
proof-
  from a1
  obtain x where \<open>\<forall> y \<in> *s* S. (*f2* dist) x y \<in> HFinite\<close>
    by blast
  have \<open>\<exists>M. \<forall> y \<in> *s* S. (*f2* dist) x y < M\<close>
  proof(rule classical)
    assume \<open>\<not>(\<exists> M. \<forall> y \<in> *s* S. (*f2* dist) x y < M)\<close>
    hence \<open>\<forall>M. \<exists> y \<in> *s* S. (*f2* dist) x y \<ge> M\<close>
      using leI by blast
    hence \<open>\<exists>y \<in> *s* S. (*f2* dist) x y \<ge> hypreal_of_hypnat whn\<close>
      by blast
    then obtain y where \<open>y \<in> *s* S\<close> and \<open>(*f2* dist) x y \<ge> hypreal_of_hypnat whn\<close>
      by blast
    have \<open>(*f2* dist) x y \<notin> HFinite\<close>
    proof(rule classical)
      assume \<open>\<not>((*f2* dist) x y \<notin> HFinite)\<close>
      hence \<open>(*f2* dist) x y \<in> HFinite\<close>
        by blast
      hence s1: \<open>\<exists> r \<in> \<real>. hnorm ((*f2* dist) x y) < r\<close>
        using HFinite_def by blast
      have \<open>\<forall> xx. \<forall> yy. norm ( dist xx yy) = dist xx yy\<close>
        by simp
      hence \<open>\<forall> xx. \<forall> yy. hnorm ((*f2* dist) xx yy) = (*f2* dist) xx yy\<close>
        by StarDef.transfer
      hence s2: \<open>hnorm ((*f2* dist) x y) = (*f2* dist) x y\<close>
        by blast
      have \<open>\<exists> r \<in> \<real>. (*f2* dist) x y < r\<close>
        using s1 s2
        by simp
      hence \<open>\<exists>r \<in> \<real>. hypreal_of_hypnat whn < r\<close>
        using \<open>(*f2* dist) x y \<ge> hypreal_of_hypnat whn\<close>
          order.not_eq_order_implies_strict by fastforce
      then obtain r where \<open>r \<in> \<real>\<close> and \<open>hypreal_of_hypnat whn < r\<close>
        by blast
      from \<open>r \<in> \<real>\<close>
      have \<open>\<exists> s. r = hypreal_of_real s\<close>
        by (simp add: SReal_iff)
      then obtain s where \<open>r = hypreal_of_real s\<close>
        by blast
      have \<open>\<exists> n::nat. s < n\<close>
        by (simp add: reals_Archimedean2)
      then obtain n::nat where \<open>s < n\<close>
        by blast
      from \<open>s < n\<close>
      have \<open>hypreal_of_real s < hypreal_of_nat n\<close>
        by StarDef.transfer
      hence \<open>\<exists>n. r < hypreal_of_nat n\<close> 
        using \<open>r = hypreal_of_real s\<close> by blast
      then obtain n where \<open>r < hypreal_of_nat n\<close>
        by blast
      from \<open>hypreal_of_hypnat whn < r\<close>  \<open>r < hypreal_of_nat n\<close>
      have t1: \<open>hypreal_of_hypnat whn < hypreal_of_nat n\<close>
        by simp

      have  \<open>hypnat_of_nat n < whn\<close>
        by simp
      hence  \<open>hypreal_of_hypnat (hypnat_of_nat n) < hypreal_of_hypnat whn\<close>
        by simp
      moreover have \<open>hypreal_of_hypnat (hypnat_of_nat n) = hypreal_of_nat n\<close>
        using hypreal_of_hypnat_hypnat_of_nat_hypreal_of_nat by blast
      ultimately have t2: \<open>hypreal_of_nat n < hypreal_of_hypnat whn\<close>
        by simp      
      hence \<open>hypreal_of_hypnat whn < hypreal_of_hypnat whn\<close>
        using t1 by auto        
      thus ?thesis by blast
    qed
    thus ?thesis
      using \<open>\<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close> \<open>y \<in> *s* S\<close> by auto 
  qed
  hence \<open>\<exists> x. \<exists>M. \<forall>y\<in>*s* S. (*f2* dist) x y < M\<close>
    by blast
  hence \<open>\<exists> x. \<exists>M. \<forall>y\<in>*s* S. (*f2* dist) x y \<le> M\<close>
    using le_less by blast
  hence \<open>\<exists>x e. \<forall>y\<in>S. dist x y \<le> e\<close>  by StarDef.transfer
  thus ?thesis using bounded_def by blast
qed

proposition bounded_nsbounded_iff:
  \<open>bounded S \<longleftrightarrow> (\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite)\<close>
  using bounded_nsbounded nsbounded_bounded by blast

lemma ex_approx:
  fixes f::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
    and S::\<open>'a set\<close> and l::'b
  assumes a1: \<open>\<And>e. e>0 \<Longrightarrow> \<exists> x\<in>S. norm (f x - l) < e\<close>
  shows \<open>\<exists>x\<in>*s* S. (*f* f) x \<approx> star_of l\<close>
proof-
  have \<open>\<forall>e>0. \<exists>x. x\<in>S \<and> norm (f x - l) < e\<close>
    using a1
    by blast
  hence \<open>\<exists>x. \<forall>e>0. x e \<in> S \<and> norm (f (x e) - l) < e\<close>
    by metis
  then obtain x where w1: \<open>\<forall>e>0. x e \<in> S\<close> and w2: \<open>\<forall>e>0. norm (f (x e) - l) < e\<close>
    by blast
  from w1 
  have \<open>\<forall>e>0. (*f* x) e \<in> *s* S\<close>
    by StarDef.transfer
  hence \<open>(*f* x) epsilon \<in> *s* S\<close>
    using epsilon_gt_zero by auto
  from  w2
  have  \<open>\<forall>e>0. hnorm ((*f* f) ((*f* x) e) - (star_of l)) < e\<close>
    by StarDef.transfer
  hence \<open>hnorm ((*f* f) ((*f* x) epsilon) - (star_of l)) < epsilon\<close>
    using epsilon_gt_zero by blast    
  hence  \<open>(*f* f) ((*f* x) epsilon) \<approx> (star_of l)\<close>
    by (metis Infinitesimal_epsilon add_diff_cancel_left' bex_Infinitesimal_iff2 diff_add_cancel 
        hnorm_less_Infinitesimal)
  thus ?thesis using \<open>(*f* x) epsilon \<in> *s* S\<close> by blast
qed


lemma inv_hSuc_Infinite_Infinitesimal:
  assumes a1: "N\<in>HNatInfinite"
  shows "inverse (hypreal_of_hypnat (hSuc N)) \<in> Infinitesimal"
proof-
  have \<open>\<And>n. n < Suc n\<close>
    by auto
  hence \<open>\<And>n. n < hSuc n\<close>
    by StarDef.transfer
  hence \<open>N < hSuc N\<close>
    by blast
  hence \<open>hSuc N \<in> HNatInfinite\<close>
    using \<open>N\<in>HNatInfinite\<close> HNatInfinite_upward_closed dual_order.strict_implies_order by blast
  thus ?thesis
    by simp
qed

definition starfun3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a star \<Rightarrow> 'b star \<Rightarrow> 'c star \<Rightarrow> 'd star"  (\<open>*f3* _\<close> [80] 80)
  where "starfun3 f \<equiv> \<lambda>x y z. star_of f \<star> x \<star> y \<star> z"
declare starfun3_def [StarDef.transfer_unfold]

subsection \<open>Closure\<close>

lemma nsclosure_I:
  assumes a1: \<open>r \<in> closure A\<close>
  shows \<open>\<exists>a \<in> *s* A. star_of r \<approx> a\<close>
proof-
  have \<open>\<exists>s. (\<forall> n. s n \<in> A) \<and> s \<longlonglongrightarrow> r\<close>
    using closure_sequential assms by auto
  then obtain s::\<open>nat\<Rightarrow>_\<close> where b1: \<open>\<And>n. s n \<in> A\<close> and b2: \<open>s \<longlonglongrightarrow> r\<close>     
    by blast
  from  b1
  have c1: \<open>\<And> n. (*f* s) n \<in> *s* A\<close>
    by StarDef.transfer
  obtain N where N_def: \<open>N \<in> HNatInfinite\<close>
    using HNatInfinite_whn by blast
  have \<open>(*f* s) N \<in> *s* A\<close>
    by (simp add: c1)    
  moreover have \<open>(*f* s) N \<approx> star_of r\<close>    
    using b2
    by (simp add: LIMSEQ_NSLIMSEQ NSLIMSEQ_D N_def)
  ultimately show ?thesis
    using approx_reorient by blast 
qed

lemma nsclosure_D:
  assumes a1: "\<exists>a \<in> *s* A. star_of r \<approx> a"
  shows \<open>r \<in> closure A\<close>
proof-
  have \<open>\<exists>a \<in> *s* A. hnorm (star_of r - a) \<in> Infinitesimal\<close>
    using a1 Infinitesimal_hnorm_iff bex_Infinitesimal_iff by auto
  hence \<open>\<exists>a \<in> *s* A. \<forall> e\<in>Reals. e > 0 \<longrightarrow> hnorm (star_of r - a) <  e\<close>
    using Infinitesimal_less_SReal2 by blast
  hence \<open>\<exists>a \<in> *s* A. hnorm (star_of r - a) <  e\<close>
    if "e\<in>Reals" and "e > 0"
    for e
    using that
    by blast
  hence \<open>\<exists>a \<in> *s* A. hnorm (star_of r - a)
           < hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
    if "hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n ) > 0"
    for n::nat    
    using that
    by auto
  hence \<open>\<exists>a \<in> *s* A. hnorm (star_of r - a)
           < hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
    for n::nat
    by (meson InfinitesimalD2 assms bex_Infinitesimal_iff 
        nice_ordered_field_class.inverse_positive_iff_positive of_nat_0_less_iff zero_less_Suc)    
  have \<open>\<exists>a\<in>A. norm (r - a)
           <  ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
    for n::nat
  proof-
    have \<open>\<exists>a \<in> *s* A. hnorm (star_of r - a)
           < hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
      using \<open>\<And>n. \<exists>a\<in>*s* A. hnorm (star_of r - a) < hypreal_of_real (inverse (real (Suc n)))\<close> 
      by auto
    thus ?thesis
      by StarDef.transfer
  qed
  hence \<open>\<And>n. \<exists> a \<in>  A. norm (r - a)  <  (\<lambda>n. inverse (real (Suc n))) n\<close>
    by blast
  hence \<open>\<exists> s. \<forall> n. s n \<in> A \<and> norm (r - s n)  <  (\<lambda>n. inverse (real (Suc n))) n\<close>
    by metis
  then obtain s where s_def1: \<open>\<And>n. s n \<in> A\<close> 
    and s_def2: \<open>\<And>n. norm (r - s n)  <  (\<lambda>n. inverse (real (Suc n))) n\<close> 
    by blast
  have s1: \<open>\<And>n. hnorm (star_of r - (*f* s) n)  <  (*f* (\<lambda>n. inverse (real (Suc n)))) n\<close>
    using s_def2
    by StarDef.transfer
  have \<open>(*f* s) N \<approx> star_of r\<close>
    if  \<open>N \<in> HNatInfinite\<close>
    for N
  proof-
    have \<open>hnorm (star_of r - (*f* s) N)  <  (*f* (\<lambda>n. inverse (real (Suc n)))) N\<close>
      using s1 by blast
    moreover have \<open>(*f* (\<lambda>n. inverse (real (Suc n)))) N \<in> Infinitesimal\<close>
      using  \<open>N \<in> HNatInfinite\<close>
      by (metis (full_types) hSuc_def inv_hSuc_Infinite_Infinitesimal of_hypnat_def starfun_inverse2 
          starfun_o2)
    ultimately have \<open>hnorm (star_of r - (*f* s) N) \<in> Infinitesimal\<close>
      using Infinitesimal_hnorm_iff hnorm_less_Infinitesimal by blast
    thus \<open>(*f* s) N \<approx> star_of r\<close>
      by (meson Infinitesimal_hnorm_iff approx_sym bex_Infinitesimal_iff)
  qed
  hence \<open>s \<longlonglongrightarrow> r\<close>
    using NSLIMSEQ_I NSLIMSEQ_LIMSEQ by metis     
  thus ?thesis
    using closure_sequential s_def1 by auto 
qed

text \<open>Theorem 10.1.1 (3) of [goldblatt2012lectures]\<close>
lemma nsclosure_iff:
  \<open>r \<in> closure A \<longleftrightarrow> (\<exists> a \<in> *s* A. star_of r \<approx> a)\<close>
  using nsclosure_D nsclosure_I by blast

text \<open>Hyperfinite set\<close>
definition hypfinite where \<open>hypfinite = (*p* finite)\<close> 


subsection \<open>Unsorted\<close>

lemma Cauchy_convergent_norm:
  assumes a1: "Cauchy (x::nat \<Rightarrow> 'a::real_normed_vector)"
  shows  \<open>Cauchy (\<lambda> n. norm (x n))\<close>
proof-
  have \<open>(*f* x) N \<approx> (*f* x) M\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M
    using that
    by (simp add: Cauchy_NSCauchy NSCauchyD a1)
  hence \<open>hnorm ((*f* x) N) \<approx> hnorm ((*f* x) M)\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M
    using that
    by (simp add: approx_hnorm)
  thus \<open>Cauchy (\<lambda> n. norm (x n))\<close>
    by (metis (full_types) NSCauchyI NSCauchy_Cauchy_iff starfun_hnorm)
qed

lemma Cauchy_add:
  fixes f g::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes a1: \<open>Cauchy f\<close> and a2: \<open>Cauchy g\<close>
  shows \<open>Cauchy (\<lambda> n. f n + g n)\<close>
proof-
  from a1
  have b1: \<open>(*f* f) N \<approx> (*f* f) M\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M::hypnat
    using NSCauchy_Cauchy_iff NSCauchy_def that by blast
  from a2
  have b2: \<open>(*f* g) N \<approx> (*f* g) M\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M::hypnat
    using NSCauchy_Cauchy_iff NSCauchy_def that by blast  
  have b3: \<open>(*f* (\<lambda> n. f n + g n)) N \<approx> (*f*  (\<lambda> n. f n + g n)) M\<close>
    if \<open>N \<in> HNatInfinite\<close> and \<open>M \<in> HNatInfinite\<close>
    for N M::hypnat
    by (metis (mono_tags) b1 b2 approx_add starfun_add that(1) that(2))  
  thus \<open>Cauchy (\<lambda> n. f n + g n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed

lemma lim_leq:
  fixes x y :: \<open>nat \<Rightarrow> real\<close>
  assumes \<open>\<And> n. x n \<le> y n\<close> and \<open>convergent x\<close> and \<open>convergent y\<close>
  shows \<open>lim x \<le> lim y\<close>
  by (metis NSLIMSEQ_le NSconvergent_def assms(1) assms(2) assms(3) convergent_NSconvergent_iff lim_nslim_iff nslimI)

lemma lim_ge:
  fixes x ::real and y :: \<open>nat \<Rightarrow> real\<close>
  assumes \<open>\<And> n. x \<le> y n\<close> and \<open>convergent y\<close>
  shows \<open>x \<le> lim y\<close>
  using lim_leq
  by (metis (full_types) NSLIMSEQ_le_const NSconvergent_NSLIMSEQ_iff assms(1) assms(2) convergent_NSconvergent_iff lim_nslim_iff) 

lemma lim_add:
  fixes x y :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>convergent x\<close> and \<open>convergent y\<close>
  shows \<open>lim (\<lambda> n. x n + y n) = lim x + lim y\<close>
proof-
  have b1: \<open>(*f* x) N \<approx> star_of (lim x)\<close>
    if "N \<in> HNatInfinite"
    for N
    using \<open>convergent x\<close> that
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  have b2: \<open>(*f* y) N \<approx> star_of (lim y)\<close>
    if "N \<in> HNatInfinite"
    for N
    using \<open>convergent y\<close> that
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  have b3: \<open>(*f* x) N + (*f* y) N \<approx> star_of (lim x) + star_of (lim y)\<close>
    if "N \<in> HNatInfinite"
    for N
    using that
    by (simp add: approx_add b1 b2)    
  moreover have \<open>(*f* (\<lambda> n. x n + y n)) N = (*f* x) N + (*f* y) N\<close>
    for N
    by auto
  moreover have \<open>star_of (lim x + lim y) = star_of (lim x) + star_of (lim y)\<close>
    by auto
  ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow>  (*f* (\<lambda> n. x n + y n)) N \<approx> star_of (lim x + lim y)\<close>
    for N
    by simp
  thus ?thesis
    by (simp add: NSLIMSEQ_I lim_nslim_iff nslimI) 
qed


lemma lim_add_const_left:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and c::'a
  assumes \<open>convergent x\<close>
  shows \<open>lim (\<lambda> n. c + x n) = c + lim x\<close>
proof-
  have \<open>convergent (\<lambda> i. c)\<close>
    by (simp add: convergent_const)    
  hence \<open>lim (\<lambda> n. (\<lambda> i. c) n + x n) = lim (\<lambda> n. c) + lim x\<close>
    using \<open>convergent x\<close> lim_add[where x = "(\<lambda> i. c)" and y = "x"]
    by blast
  moreover have \<open>lim (\<lambda> i. c) = c\<close>
    by simp
  ultimately show ?thesis by auto
qed

lemma lim_add_const_right:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes  \<open>convergent x\<close>
  shows \<open>lim (\<lambda> n. x n + c) = lim x + c\<close>
proof-
  have \<open>lim (\<lambda> n. c + x n) = c + lim x\<close>
    using assms lim_add_const_left by blast
  moreover have \<open>(\<lambda> n. c + x n) = (\<lambda> n. x n + c)\<close>
    by auto
  moreover have \<open>c + lim x = lim x + c\<close>
    by simp
  ultimately show ?thesis by simp
qed

lemma lim_scaleR:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and r::real
  assumes a1: \<open>convergent x\<close> 
  shows \<open>lim (\<lambda> n. r *\<^sub>R x n ) = r *\<^sub>R lim x\<close>
proof-
  have \<open>(*f* x) N \<approx> star_of (lim x)\<close>
    if "N \<in> HNatInfinite"
    for N
    using \<open>convergent x\<close> that
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  hence \<open>r *\<^sub>R (*f* x) N \<approx> r *\<^sub>R (star_of (lim x))\<close>
    if "N \<in> HNatInfinite"
    for N
    using that
    by (simp add: approx_scaleR2)
  moreover have \<open>(*f* (\<lambda> n. r *\<^sub>R x n)) N = r *\<^sub>R (*f* x) N\<close>
    for N
    by (simp add: star_scaleR_def)    
  moreover have \<open>star_of (r *\<^sub>R lim x) = r *\<^sub>R star_of (lim x)\<close>
    by auto
  ultimately have \<open>(*f* (\<lambda> n. r *\<^sub>R x n)) N \<approx> star_of (r *\<^sub>R lim x)\<close>
    if "N \<in> HNatInfinite"
    for N
    using that by auto
  thus ?thesis
    by (simp add: NSLIMSEQ_I lim_nslim_iff nslimI) 
qed


lemma Cauchy_minus:
  fixes f g::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes a1: \<open>Cauchy f\<close> and a2: \<open>Cauchy g\<close>
  shows  \<open>Cauchy (\<lambda> n. f n - g n)\<close>
proof-
  from a1
  have b1: \<open>(*f* f) N \<approx> (*f* f) M\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M::hypnat
    using that NSCauchy_Cauchy_iff NSCauchy_def by blast
  from a2
  have b2: \<open>(*f* g) N \<approx> (*f* g) M\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M::hypnat
    using that NSCauchy_Cauchy_iff NSCauchy_def by blast  
  have \<open>(*f* (\<lambda> n. f n -g n)) N \<approx> (*f*  (\<lambda> n. f n -g n)) M\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M::hypnat
  proof-
    have \<open>(*f* f) N - (*f* g) N \<approx> (*f* f) M - (*f* g) M\<close>
      by (simp add: approx_diff b1 b2 that(1) that(2))      
    moreover have \<open>(*f* (\<lambda> n. f n - g n)) N = (*f* f) N - (*f* g) N\<close>
      by auto
    moreover have \<open>(*f* (\<lambda> n. f n - g n)) M = (*f* f) M - (*f* g) M\<close>
      by auto
    ultimately show \<open>(*f* (\<lambda> n. f n - g n)) N \<approx> (*f*  (\<lambda> n. f n - g n)) M\<close>
      by simp
  qed
  thus \<open>Cauchy (\<lambda> n. f n - g n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed

lemma Cauchy_sgn:
  fixes x::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes a1: \<open>Cauchy x\<close>
  shows \<open>Cauchy (\<lambda> n. (x n) /\<^sub>R lim (\<lambda> n. norm (x n)))\<close>
proof-
  have b1: \<open>\<exists>L. lim (\<lambda>n. norm (x n)) = L\<close>
    by auto
  then obtain L where L_def: \<open>lim (\<lambda>n. norm (x n)) = L\<close>
    by blast
  show \<open>Cauchy (\<lambda>n. x n /\<^sub>R lim (\<lambda>n. norm (x n)))\<close>
  proof(cases "L = 0")
    case True
    have \<open>(x n) /\<^sub>R L = 0\<close>
      for n
      by (simp add: True)
    hence \<open>(\<lambda>n. (x n) /\<^sub>R L) = (\<lambda> _. 0)\<close>
      by blast
    moreover have \<open>lim (\<lambda> _. 0) = 0\<close>
      by auto
    ultimately have \<open>(\<lambda>n. (x n) /\<^sub>R L) \<longlonglongrightarrow> 0\<close>
      by simp
    hence \<open>convergent (\<lambda>n. (x n) /\<^sub>R L)\<close>
      unfolding convergent_def
      by blast
    thus ?thesis
      using  \<open>lim (\<lambda>n. norm (x n)) = L\<close> LIMSEQ_imp_Cauchy \<open>(\<lambda>n. x n /\<^sub>R L) \<longlonglongrightarrow> 0\<close> by blast
  next
    case False
    have c1: \<open>(\<lambda>n. x n /\<^sub>R lim (\<lambda>n. norm (x n))) = (\<lambda>n. x n /\<^sub>R L)\<close>
      by (simp add: L_def)
    from \<open>Cauchy x\<close>
    have p1: \<open>(*f* x) N \<approx> (*f* x) M\<close>
      if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
      for N M
      using that
      by (simp add: Cauchy_NSCauchy NSCauchyD)
    hence \<open>(*f2* scaleR) (inverse (star_of L)) ((*f* x) N) \<approx> (*f2* scaleR) (inverse (star_of L)) ((*f* x) M)\<close>
      if d1: "N \<in> HNatInfinite" and d2: "M \<in> HNatInfinite"
      for N M
    proof -
      have "(*f* x) N \<approx> (*f* x) M"
        by (simp add: p1 d1 d2)
      thus ?thesis
        by (metis approx_scaleR2 star_of_inverse star_scaleR_def starfun2_star_of)        
    qed
    moreover have \<open>(*f2* scaleR) (inverse (star_of L)) ((*f* x) N) =  (*f* (\<lambda>n. x n /\<^sub>R L)) N\<close>
      for N
      by (metis star_of_inverse starfun2_star_of starfun_o2)
    ultimately have \<open>(*f* (\<lambda>n. x n /\<^sub>R L)) N \<approx> (*f* (\<lambda>n. x n /\<^sub>R L)) M\<close>
      if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
      for N M
      using that
      by simp
    hence c2:\<open>Cauchy (\<lambda>n. x n /\<^sub>R L)\<close>
      using NSCauchyI NSCauchy_Cauchy by blast    
    thus ?thesis
      by (simp add: L_def)  
  qed
qed


lemma Cauchy_scaleR:
  fixes r::real and x::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes a1: "Cauchy x" 
  shows \<open>Cauchy (\<lambda>n. r *\<^sub>R x n)\<close>
proof-
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
    (*f* x) N \<approx> (*f* x) M\<close>
    for N M
    using a1
    by (simp add: NSCauchyD NSCauchy_Cauchy_iff)
  hence \<open>(*f2* scaleR) (star_of r) ((*f* x) N) \<approx> (*f2* scaleR) (star_of r) ((*f* x) M)\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M
    by (metis approx_scaleR2 star_scaleR_def starfun2_star_of that(1) that(2))    
  moreover have \<open>(*f2* scaleR) (star_of r) ((*f* x) N) = (*f* (\<lambda>n. r *\<^sub>R x n)) N\<close>
    for N
    by auto
  ultimately have  \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
      (*f* (\<lambda>n. r *\<^sub>R x n)) N \<approx> (*f* (\<lambda>n. r *\<^sub>R x n)) M\<close>
    for N M
    by simp
  thus \<open>Cauchy (\<lambda>n. r *\<^sub>R x n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed

lemma Infinitesimal_scaleC2: 
  fixes x :: \<open>('a::complex_normed_vector) star\<close>
  assumes "x \<in> Infinitesimal" 
  shows "a *\<^sub>C x \<in> Infinitesimal"
proof-
  have \<open>hnorm x \<in> Infinitesimal\<close>
    using \<open>x \<in> Infinitesimal\<close>
    by (simp add: Infinitesimal_hnorm_iff)
  hence \<open>(star_of (cmod a)) * hnorm x \<in> Infinitesimal\<close>
    using Infinitesimal_star_of_mult2 by blast
  moreover have \<open>(star_of (cmod a)) * hnorm x = hnorm (a *\<^sub>C x)\<close>
    by (simp add: hnorm_scaleC)
  ultimately have \<open>hnorm (a *\<^sub>C x) \<in> Infinitesimal\<close>
    by simp
  thus ?thesis by (simp add: Infinitesimal_hnorm_iff)
qed

lemma approx_scaleC2: 
  fixes a b :: \<open>('a::complex_normed_vector) star\<close>
  assumes a1: \<open>a \<approx> b\<close>
  shows "c *\<^sub>C a \<approx> c *\<^sub>C b"
proof-
  have \<open>a - b \<in> Infinitesimal\<close>
    using a1
    by (simp add: Infinitesimal_approx_minus)
  hence \<open>c *\<^sub>C (a - b) \<in> Infinitesimal\<close>
    by (simp add: Infinitesimal_scaleC2)
  moreover have \<open>c *\<^sub>C (a - b) = c *\<^sub>C a - c *\<^sub>C b\<close>
    by (simp add: complex_vector.scale_right_diff_distrib)
  ultimately have \<open>c *\<^sub>C a - c *\<^sub>C b \<in> Infinitesimal\<close> 
    by simp
  thus ?thesis by (simp add: Infinitesimal_approx_minus)
qed

lemma Cauchy_scaleC:
  fixes r::complex and x::\<open>nat \<Rightarrow> 'a::complex_normed_vector\<close>
  assumes a1: "Cauchy x"
  shows \<open>Cauchy (\<lambda>n. r *\<^sub>C x n)\<close>
proof-
  have \<open>(*f* x) N \<approx> (*f* x) M\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M
    using a1 that
    by (simp add: NSCauchyD NSCauchy_Cauchy_iff)
  hence d3: \<open>(*f2* scaleC) (star_of r) ((*f* x) N) \<approx> (*f2* scaleC) (star_of r) ((*f* x) M)\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M
    using that
    by (metis approx_scaleC2 star_scaleC_def starfun2_star_of)
  have \<open>\<forall> n. ( scaleC) ( r) (( x) n) = ( (\<lambda>n. r *\<^sub>C x n)) n\<close>
    by auto
  hence d2:\<open>\<forall> n. (*f2* scaleC) (star_of r) ((*f* x) n) = (*f* (\<lambda>n. r *\<^sub>C x n)) n\<close>
    by StarDef.transfer
  hence d1: \<open>(*f2* scaleC) (star_of r) ((*f* x) N) = (*f* (\<lambda>n. r *\<^sub>C x n)) N\<close>
    for N
    by blast
  have  \<open>(*f* (\<lambda>n. r *\<^sub>C x n)) N \<approx> (*f* (\<lambda>n. r *\<^sub>C x n)) M\<close>
    if "N \<in> HNatInfinite" and "M \<in> HNatInfinite"
    for N M
    using that d1 d3 by auto    
  thus \<open>Cauchy (\<lambda>n. r *\<^sub>C x n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed


lemma limit_point_Cauchy:
  assumes a1: \<open>Cauchy x\<close>
  shows \<open>\<exists>L\<in>HFinite. \<forall>N\<in>HNatInfinite. (*f* x) N \<approx> L\<close>
proof-
  have \<open>\<exists>L. \<forall> N. N \<in> HNatInfinite \<longrightarrow> (*f* x) N \<approx> L\<close>
    using Cauchy_NSCauchy NSCauchyD assms by blast
  then obtain L where L_def: \<open>\<And>N. N \<in> HNatInfinite \<Longrightarrow> (*f* x) N \<approx> L\<close>
    by blast
  moreover have \<open>\<And>N. N \<in> HNatInfinite \<Longrightarrow> (*f* x) N \<in> HFinite\<close>
    by (simp add: Cauchy_NSCauchy NSBseqD2 NSCauchy_NSBseq assms)
  ultimately show ?thesis
    using HFinite_star_of approx_HFinite by blast 
qed

lemma lim_initial_segment:
  assumes \<open>convergent x\<close>
  shows \<open>lim x = lim (\<lambda> n. x (n + k))\<close>
proof-
  have \<open>\<exists> L. x \<longlonglongrightarrow> L\<close>
    using \<open>convergent x\<close>
    unfolding convergent_def
    by blast
  then obtain L where L_def: \<open>x \<longlonglongrightarrow> L\<close>
    by blast
  hence \<open>(\<lambda> n. x (n + k)) \<longlonglongrightarrow> L\<close>
    using Topological_Spaces.LIMSEQ_ignore_initial_segment
    by auto
  thus ?thesis 
    unfolding lim_def
    by (metis LIMSEQ_unique L_def) 
qed

lemma lim_initial_segment':
  assumes \<open>convergent x\<close>
  shows \<open>lim x = lim (\<lambda> n. x (k + n))\<close>
proof-
  have \<open>lim x = lim (\<lambda> n. x (n + k))\<close>
    using \<open>convergent x\<close> lim_initial_segment by blast
  moreover have \<open>n + k = k + n\<close>
    for n
    by simp
  ultimately show ?thesis by auto
qed

lemma Lim_bounded_lim:
  fixes x :: \<open>nat \<Rightarrow> 'a::linorder_topology\<close>
  assumes a1: \<open>convergent x\<close> and a2: \<open>\<And>n. n\<ge>M \<Longrightarrow> x n \<le> C\<close>
  shows \<open>lim x \<le> C\<close>
proof-
  have \<open>\<exists>l. x \<longlonglongrightarrow> l\<close>
    using \<open>convergent x\<close>
    unfolding convergent_def
    by blast
  then obtain l where l_def: \<open>x \<longlonglongrightarrow> l\<close>
    by blast
  hence \<open>l \<le> C\<close> using a2
    using Topological_Spaces.Lim_bounded
    by blast
  thus ?thesis unfolding lim_def using l_def
    by (metis limI t2_space_class.Lim_def) 
qed

lemma Cauchy_cinner_Cauchy:
  fixes x y :: \<open>nat \<Rightarrow> 'a::complex_inner\<close>
  assumes a1: \<open>Cauchy x\<close> and a2: \<open>Cauchy y\<close>
  shows \<open>Cauchy (\<lambda> n. \<langle> x n, y n \<rangle>)\<close>
proof-
  have \<open>bounded (range x)\<close>
    using a1
    by (simp add: Elementary_Metric_Spaces.cauchy_imp_bounded)
  hence b1: \<open>\<exists>M. \<forall>n. norm (x n) < M\<close>
    by (meson bounded_pos_less rangeI)  
  have \<open>bounded (range y)\<close>
    using a2
    by (simp add: Elementary_Metric_Spaces.cauchy_imp_bounded)
  hence b2: \<open>\<exists> M. \<forall> n. norm (y n) < M\<close>
    by (meson bounded_pos_less rangeI)  
  have \<open>\<exists>M. \<forall>n. norm (x n) < M \<and> norm (y n) < M\<close>
    using b1 b2
    by (metis dual_order.strict_trans linorder_neqE_linordered_idom)  
  then obtain M where M1: \<open>\<And>n. norm (x n) < M\<close> and M2: \<open>\<And>n. norm (y n) < M\<close>
    by blast
  have M3: \<open>M > 0\<close>
    by (smt M2 norm_not_less_zero)     
  have \<open>\<exists>N. \<forall>n \<ge> N. \<forall>m \<ge> N. norm ( (\<lambda> i. \<langle> x i, y i \<rangle>) n -  (\<lambda> i. \<langle> x i, y i \<rangle>) m ) < e\<close>
    if "e > 0"
    for e
  proof-
    have \<open>e / (2*M) > 0\<close>
      using M3
      by (simp add: that)
    hence \<open>\<exists>N. \<forall>n\<ge>N. \<forall>m\<ge>N. norm (x n - x m) < e / (2*M)\<close>
      using a1
      by (simp add: Cauchy_iff) 
    then obtain N1 where N1_def: \<open>\<And>n m. n\<ge>N1 \<Longrightarrow> m\<ge>N1 \<Longrightarrow> norm (x n - x m) < e / (2*M)\<close>
      by blast
    have x1: \<open>\<exists>N. \<forall> n\<ge>N. \<forall> m\<ge>N. norm (y n - y m) < e / (2*M)\<close>
      using a2 \<open>e / (2*M) > 0\<close>
      by (simp add: Cauchy_iff) 
    obtain N2 where N2_def: \<open>\<And>n m.  n\<ge>N2 \<Longrightarrow> m\<ge>N2 \<Longrightarrow> norm (y n - y m) < e / (2*M)\<close>
      using x1
      by blast
    define N where N_def: \<open>N = N1 + N2\<close>
    hence \<open>N \<ge> N1\<close>
      by auto
    have \<open>N \<ge> N2\<close>
      using N_def
      by auto
    have \<open>norm ( \<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle> ) < e\<close>
      if \<open>n \<ge> N\<close> and \<open>m \<ge> N\<close>
      for n m
    proof-
      have \<open>\<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle> = (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) + (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>)\<close>
        by simp
      hence y1: \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle>) \<le> norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>)
           + norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>)\<close>
        by (metis norm_triangle_ineq)

      have \<open>\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle> = \<langle> x n - x m, y n \<rangle>\<close>
        by (simp add: cinner_diff_left)
      hence \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) = norm \<langle> x n - x m, y n \<rangle>\<close>
        by simp
      moreover have \<open>norm \<langle> x n - x m, y n \<rangle> \<le> norm (x n - x m) * norm (y n)\<close>
        using complex_inner_class.norm_cauchy_schwarz by auto
      moreover have \<open>norm (y n) < M\<close>
        by (simp add: M2)        
      moreover have \<open>norm (x n - x m) < e/(2*M)\<close>
        using \<open>N \<le> m\<close> \<open>N \<le> n\<close> \<open>N1 \<le> N\<close> N1_def by auto
      ultimately have \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) < (e/(2*M)) * M\<close>
        by (smt linordered_semiring_strict_class.mult_strict_mono norm_ge_zero)
      moreover have \<open> (e/(2*M)) * M = e/2\<close>
        using \<open>M > 0\<close> by simp
      ultimately have  \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) < e/2\<close>
        by simp      
      hence y2: \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) < e/2\<close>
        by blast        
      have \<open>\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle> = \<langle> x m, y n - y m \<rangle>\<close>
        by (simp add: cinner_diff_right)
      hence \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) = norm \<langle> x m, y n - y m \<rangle>\<close>
        by simp
      moreover have \<open>norm \<langle> x m, y n - y m \<rangle> \<le> norm (x m) * norm (y n - y m)\<close>
        using complex_inner_class.norm_cauchy_schwarz by auto
      moreover have \<open>norm (x m) < M\<close>
        by (simp add: M1)
      moreover have \<open>norm (y n - y m) < e/(2*M)\<close>
        using \<open>N \<le> m\<close> \<open>N \<le> n\<close> \<open>N2 \<le> N\<close> N2_def by auto 
      ultimately have \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) < M * (e/(2*M))\<close>
        by (smt linordered_semiring_strict_class.mult_strict_mono norm_ge_zero)
      moreover have \<open>M * (e/(2*M)) = e/2\<close>
        using \<open>M > 0\<close> by simp
      ultimately have  \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) < e/2\<close>
        by simp
      hence y3: \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) < e/2\<close>
        by blast
      show \<open>norm ( \<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle> ) < e\<close>
        using y1 y2 y3 by simp
    qed
    thus ?thesis by blast
  qed
  thus ?thesis
    by (simp add: CauchyI)
qed

lemma Cauchy_cinner_convergent:
  fixes x y :: \<open>nat \<Rightarrow> 'a::complex_inner\<close>
  assumes a1: \<open>Cauchy x\<close> and a2: \<open>Cauchy y\<close>
  shows \<open>convergent (\<lambda> n. \<langle> x n, y n \<rangle>)\<close>
proof-
  have b1: \<open>Cauchy (\<lambda> n. \<langle> x n, y n \<rangle>)\<close>
    using a1 a2 Cauchy_cinner_Cauchy
    by blast
  hence \<open>Cauchy (\<lambda> n. norm \<langle> x n, y n \<rangle>)\<close>
    by (simp add: Cauchy_convergent_norm)
  hence \<open>convergent (\<lambda> n. norm \<langle> x n, y n \<rangle>)\<close>
    using Cauchy_convergent_iff by auto
  thus ?thesis
    using Cauchy_convergent_iff b1 by auto
qed

lemma lim_minus:
  fixes x y :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes a1: \<open>convergent x\<close> and a2: \<open>convergent y\<close>
  shows \<open>lim (\<lambda> n. x n - y n) = lim x - lim y\<close>
proof-
  have \<open>convergent (\<lambda> i. x i - y i)\<close>
    using a1 a2
    by (simp add: convergent_diff)
  hence \<open>lim (\<lambda> n. (\<lambda> i. x i - y i) n + y n) = lim (\<lambda> i. x i - y i) + lim y\<close>
    using a2 lim_add by blast
  moreover have \<open>(\<lambda> n. (\<lambda> i. x i - y i) n + y n) = x\<close>
    by auto
  ultimately have \<open>lim x = lim (\<lambda> i. x i - y i) + lim y\<close>
    by simp
  thus ?thesis by simp
qed

lemma lim_scaleC:
  fixes x :: \<open>nat \<Rightarrow> 'a::complex_normed_vector\<close> and r::complex
  assumes a1: \<open>convergent x\<close> 
  shows \<open>lim (\<lambda> n. r *\<^sub>C x n ) = r *\<^sub>C lim x\<close>
proof-
  have \<open>(*f* x) N \<approx> star_of (lim x)\<close>
    if "N \<in> HNatInfinite"
    for N
    using a1 that
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  hence \<open>r *\<^sub>C (*f* x) N \<approx> r *\<^sub>C (star_of (lim x)) \<close>
    if "N \<in> HNatInfinite"
    for N
    using that
    by (simp add: approx_scaleC2)
  moreover have \<open>(*f* (\<lambda> n. r *\<^sub>C x n)) N = r *\<^sub>C (*f* x) N\<close>
    for N
    using star_scaleC_def
    by (metis starfun_o2) 
  moreover have \<open>star_of (r *\<^sub>C lim x) = r *\<^sub>C star_of (lim x)\<close>
    by auto
  ultimately have \<open>(*f* (\<lambda> n. r *\<^sub>C x n)) N \<approx> star_of (r *\<^sub>C lim x)\<close>
    if "N \<in> HNatInfinite"
    for N
    using that
    by auto
  thus ?thesis
    by (simp add: NSLIMSEQ_I lim_nslim_iff nslimI) 
qed

lemma lim_Lim_bounded2:
  fixes x::\<open>nat \<Rightarrow> real\<close>
  assumes a1: \<open>\<And>n.  n \<ge> N \<Longrightarrow> C \<le> x n\<close> and a2: \<open>convergent x\<close>
  shows \<open>C \<le> lim x\<close>
proof-
  have \<open>\<exists> l. x \<longlonglongrightarrow> l\<close>
    using a2
    unfolding convergent_def by blast
  then obtain l where l_def: \<open>x \<longlonglongrightarrow> l\<close>
    by blast
  hence \<open>C \<le> l\<close>
    using  Topological_Spaces.Lim_bounded2[where f = "x" and l="l" and N = "N"]
    by (simp add: a1)
  thus \<open>C \<le> lim x\<close>
    using \<open>x \<longlonglongrightarrow> l\<close> limI by auto    
qed

lemma lim_complex_of_real:
  fixes x::\<open>nat \<Rightarrow> real\<close>
  assumes a1: \<open>convergent x\<close>
  shows \<open>lim (\<lambda> n. complex_of_real (x n)) = complex_of_real (lim x)\<close>
proof-
  have \<open>\<exists>l. x \<longlonglongrightarrow> l\<close>
    using a1 unfolding convergent_def
    by blast
  then obtain l where l_def: \<open>x \<longlonglongrightarrow> l\<close>
    by blast
  moreover have \<open>(\<lambda>n. (0::real)) \<longlonglongrightarrow> 0\<close>
    by auto
  ultimately have \<open>(\<lambda>n. Complex (x n) ((\<lambda>n. (0::real)) n)) \<longlonglongrightarrow> Complex l 0\<close>
    using Complex.tendsto_Complex[where f = "x" and g = "(\<lambda>n. (0::real))"]
    by auto
  hence \<open>(\<lambda>n. Complex (x n) 0) \<longlonglongrightarrow> Complex l 0\<close>
    by simp
  moreover  have \<open>lim x = l\<close>
    using l_def limI by auto 
  ultimately have \<open>(\<lambda>n. Complex (x n) 0) \<longlonglongrightarrow> Complex (lim x) 0\<close>
    by simp
  hence \<open>lim (\<lambda>n. Complex (x n) 0) = Complex (lim x) 0\<close>
    using limI by auto
  thus ?thesis
    unfolding complex_of_real_def
    by blast
qed     

lemma lim_norm:
  fixes x::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes a1: \<open>convergent x\<close>
  shows \<open>lim (\<lambda> n. norm (x n)) = norm (lim x)\<close>
proof-
  have \<open>\<exists>l. x \<longlonglongrightarrow> l\<close>
    using a1 unfolding convergent_def by blast
  then obtain l where l_def: \<open>x \<longlonglongrightarrow> l\<close>
    by blast
  hence \<open>(\<lambda> n. norm (x n) ) \<longlonglongrightarrow> norm l\<close>
    by (simp add: tendsto_norm)
  moreover have \<open>lim x = l\<close>
    using  l_def
    by (simp add: limI) 
  ultimately show ?thesis
    by (simp add: limI) 
qed

lemma lim_sqrt:
  fixes x::\<open>nat \<Rightarrow> real\<close>
  assumes \<open>convergent x\<close>
  shows \<open>lim (\<lambda> n. sqrt (x n)) = sqrt (lim x)\<close>
proof-
  from \<open>convergent x\<close>
  have \<open>\<exists> l. x \<longlonglongrightarrow> l\<close>
    by (simp add: convergent_def)
  then obtain l where \<open>x \<longlonglongrightarrow> l\<close>
    by blast
  hence lim:\<open>lim x = l\<close>
    by (simp add: limI)
  from \<open>x \<longlonglongrightarrow> l\<close>
  have \<open>(\<lambda> n.  sqrt (x n)) \<longlonglongrightarrow> sqrt l\<close>
    by (simp add: tendsto_real_sqrt)
  thus ?thesis using lim
    by (simp add: limI) 
qed

lemma cbounded_linear_Cauchy:
  assumes a1: \<open>Cauchy x\<close> and a2: \<open>cbounded_linear f\<close>
  shows \<open>Cauchy (\<lambda> n. f (x n))\<close>
proof-
  have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (f (x m) - f (x n)) < e\<close>
    if h1: \<open>e > 0\<close>
    for e
  proof-
    have b1: \<open>\<exists>M. \<forall> t. norm (f t) \<le> norm t * M \<and> M > 0\<close>
      using a2 cbounded_linear.bounded_linear bounded_linear.pos_bounded
      by blast
    then obtain M where M_def: \<open>\<And> t. norm (f t) \<le> norm t * M\<close> and \<open>M > 0\<close>
      by blast
    have b2: \<open>norm (f (x m - x n)) \<le> norm (x m - x n) * M\<close>
      for m n
      using M_def by blast
    moreover have \<open>f (x m - x n) = f (x m) - f (x n)\<close>
      for m n
      using \<open>cbounded_linear f\<close> unfolding cbounded_linear_def
      by (simp add: complex_vector.linear_diff) 
    ultimately have f1: \<open>norm (f (x m) - f (x n)) \<le> norm (x m - x n) * M\<close>
      for m n
      by simp
    have \<open>e/M > 0\<close>
      by (simp add: \<open>0 < M\<close> \<open>0 < e\<close>)
    hence \<open>\<exists>K. \<forall>m\<ge>K. \<forall>n\<ge>K. norm (x m - x n) < e/M\<close>
      using Cauchy_iff assms(1) by blast
    then obtain K where \<open>\<And> m n. m\<ge>K \<Longrightarrow> n\<ge>K \<Longrightarrow> norm (x m - x n) < e/M\<close>
      by blast
    hence \<open>norm (f (x m) - f (x n)) < e\<close>
      if \<open>m \<ge> K\<close> and \<open>n \<ge> K\<close>
      for m n
    proof-
      have \<open>norm (f (x m) - f (x n)) \<le> norm (x m -x n) * M\<close>
        by (simp add: f1)
      also have \<open>\<dots> < e/M * M\<close>
        using \<open>0 < M\<close> \<open>K \<le> m\<close> \<open>K \<le> n\<close> \<open>\<And>n m. \<lbrakk>K \<le> m; K \<le> n\<rbrakk> \<Longrightarrow> norm (x m - x n) < e / M\<close> linordered_semiring_strict_class.mult_strict_right_mono by blast
      also have \<open>\<dots> = e\<close>
        using \<open>0 < M\<close> by auto        
      finally show ?thesis by blast
    qed
    thus ?thesis
      by blast 
  qed
  thus ?thesis 
    unfolding Cauchy_def
    using dist_norm
    by smt
qed




lemma tendsto_finite_sum:
  fixes X :: \<open>_ \<Rightarrow> _ \<Rightarrow> _::topological_monoid_add\<close>
  assumes  \<open>\<And> t. t\<in>T \<Longrightarrow> X t \<longlonglongrightarrow> L t\<close> \<open>finite T\<close>
  shows \<open>(\<lambda> n. (\<Sum>t\<in>T. X t n)) \<longlonglongrightarrow>  (\<Sum>t\<in>T. L t)\<close>
  using  Complex_Vector_Spaces.finite_sum_tendsto assms 
  by auto


lemma infinitesimal_square:
  fixes x::hypreal
  shows \<open>x^2 \<in> Infinitesimal \<Longrightarrow> x \<in> Infinitesimal\<close>
  by (metis (full_types) NSA.Infinitesimal_mult_disj semiring_normalization_rules(29))


proposition unbounded_nsbounded_D:
  fixes S::\<open>'a::real_normed_vector set\<close>
  assumes a1: \<open>\<not>(bounded S)\<close>
  shows \<open>\<exists> x\<in>*s* S. x \<in> HInfinite\<close>
proof-
  have \<open>\<And> M. \<exists> x\<in>S. norm x > M\<close>
    unfolding a1 bounded_def
    by (meson assms boundedI not_less) 
  hence \<open>\<And> M. \<exists> x\<in>*s* S. hnorm x > M\<close>
    by StarDef.transfer
  hence \<open>\<exists> x\<in>*s* S. hnorm x > \<omega>\<close>
    by blast
  thus ?thesis
    using HInfiniteI SReal_less_omega less_trans by blast
qed

proposition unbounded_nsbounded_I:
  fixes S::\<open>'a::real_normed_vector set\<close>
  assumes a1: "\<exists>x\<in>*s* S. x \<in> HInfinite"
  shows \<open>\<not>(bounded S)\<close>
proof(rule classical)
  assume c: \<open>\<not>( \<not>(bounded S))\<close>
  hence \<open>bounded S\<close>
    by blast
  hence \<open>bounded (insert 0 S)\<close>
    by simp
  from  a1 obtain x where x1: \<open>x\<in>*s* S\<close> and x2: \<open>x \<in> HInfinite\<close>
    by blast
  have \<open>x\<in>*s* (insert 0 S)\<close>
    using x1 by simp 
  moreover have \<open>0\<in>*s* (insert 0 S)\<close>
    by auto
  ultimately have \<open>(*f2* dist) 0 x \<in> HFinite\<close>
    using \<open>bounded (insert 0 S)\<close> bounded_nsbounded by blast
  have \<open>\<And>t::'a. dist 0 t = norm t\<close>
    using dist_norm  by auto
  hence \<open>\<And> t::'a star. (*f2* dist) 0 t = hnorm t\<close>
    by StarDef.transfer
  hence \<open>(*f2* dist) 0 x = hnorm x\<close>
    by simp
  hence \<open>hnorm x \<in> HFinite\<close>
    using \<open>(*f2* dist) 0 x \<in> HFinite\<close> by auto    
  hence \<open>x \<in> HFinite\<close>
    unfolding HFinite_def by auto   
  thus ?thesis using \<open>x \<in> HInfinite\<close>
    by (simp add: HInfinite_HFinite_iff) 
qed

proposition bounded_nsbounded_norm_D:
  \<open>bounded S \<Longrightarrow> (\<And>x. x\<in>*s* S \<Longrightarrow> x \<in> HFinite)\<close>
  for S::\<open>'a::real_normed_vector set\<close>
  using not_HFinite_HInfinite unbounded_nsbounded_I by blast

proposition bounded_nsbounded_norm_I:
  \<open>(\<And>x. x\<in>*s* S \<Longrightarrow> x \<in> HFinite) \<Longrightarrow> bounded S\<close>
  for S::\<open>'a::real_normed_vector set\<close>
  using HFinite_not_HInfinite unbounded_nsbounded_D
  by blast

proposition bounded_nsbounded_norm:
  \<open>(\<forall> x\<in>*s* S. x \<in> HFinite) \<longleftrightarrow> bounded S\<close>
  for S::\<open>'a::real_normed_vector set\<close>
  using bounded_nsbounded_norm_I[where S = S] bounded_nsbounded_norm_D[where S = S] 
  by blast

lemma span_finite_dim:
  fixes T::\<open>'a::complex_inner set\<close>
  assumes \<open>finite T\<close>
  shows \<open>closure (complex_vector.span T)  = complex_vector.span T\<close>
  using closed_finite_dim
  by (simp add: closed_finite_dim assms)

lemma Span_insert:
  assumes "finite (S::'a'::complex_inner set)"
  shows "space_as_set (Span (insert a S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> space_as_set (Span S)}"
proof -
  have "closure (cspan (insert a S)) = cspan (insert a S)"
    by (metis assms finite_insert span_finite_dim)
  thus ?thesis
    by (simp add: Span.rep_eq assms complex_vector.span_insert span_finite_dim)
qed

lemma closed_subspace_cspan_finite:
  assumes "finite (S::'a::chilbert_space set)"
  shows "closed_subspace (cspan S)"
  unfolding closed_subspace_def apply auto
  by (simp add: assms closed_finite_dim)

lemma projection_singleton:
  assumes "(a::'a::chilbert_space) \<noteq> 0"
  shows "projection (cspan {a}) u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
proof-
  define p where "p u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a" for u
  define M where "M = cspan {a}"
  have y1: "closed_subspace M"
    unfolding M_def 
    using closed_subspace_cspan_finite
    by (simp add: closed_subspace_cspan_finite)
  have "u - (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a \<in> {x |x. \<forall>y\<in>cspan {a}. \<langle>x, y\<rangle> = 0}"
  proof auto
    fix y
    assume "y \<in> cspan {a}" 
    hence "\<exists>c. y = c *\<^sub>C a"
      by (simp add: cspan_singleton)
    then obtain c where c_def: "y = c *\<^sub>C a"
      by blast
    have "\<langle>u - (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, c *\<^sub>C a\<rangle> = 
          \<langle>u, c *\<^sub>C a\<rangle> - \<langle>(\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, c *\<^sub>C a\<rangle>"
      using cinner_diff_left by blast    
    also have "\<dots> = 0"
      by simp
    finally have "\<langle>u - (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, c *\<^sub>C a\<rangle> = 0".
    thus "\<langle>u - (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, y\<rangle> = 0"
      using c_def by simp
  qed
  hence y2: "u - p u \<in> orthogonal_complement M"
    unfolding p_def M_def orthogonal_complement_def
    by blast
  have y3: "p u \<in> M"
    unfolding p_def M_def
    by (simp add: complex_vector.span_base complex_vector.span_scale)
  have "projection M u = p u"
    using y1 y2 y3 projection_uniq[where x = "p u" and h = u and M = M] by blast
  thus ?thesis unfolding M_def p_def.
qed

lemma ortho_cspan:
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> \<langle>a, s\<rangle> = 0" and a2: "finite (S::'a::chilbert_space set)"
    and a3: "x \<in> cspan S"
  shows "\<langle>a, x\<rangle> = 0"
proof-
  have "\<exists>t r. finite t \<and> t \<subseteq> S \<and> (\<Sum>a\<in>t. r a *\<^sub>C a) = x"
    using complex_vector.span_explicit
    by (smt a3 mem_Collect_eq)
  then obtain t r where b1: "finite t" and b2: "t \<subseteq> S" and b3: "(\<Sum>a\<in>t. r a *\<^sub>C a) = x"
    by blast
  have x1: "\<langle>a, i\<rangle> = 0"
    if "i\<in>t" for i
    using b2 a1 that by blast
  have  "\<langle>a, x\<rangle> = \<langle>a, (\<Sum>i\<in>t. r i *\<^sub>C i)\<rangle>"
    by (simp add: b3) 
  also have  "\<dots> = (\<Sum>i\<in>t. r i *\<^sub>C \<langle>a, i\<rangle>)"
    by (simp add: cinner_sum_right)
  also have  "\<dots> = 0"
    using x1 by simp
  finally show ?thesis.
qed

(* TODO: replace by lemma projection_union:
  assumes "\<And>x y. x:A \<Longrightarrow> y:B \<Longrightarrow> orthogonal x y"
  shows projection (A \<union> B) = projection A + projection B
  
  do not assume that A and B are finite-dimensional
 *)
lemma projection_insert:
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> \<langle>a, s\<rangle> = 0" and a2: "finite (S::'a::chilbert_space set)"
  shows "projection {x. \<exists>k. x - k *\<^sub>C a \<in> cspan S} u
        = projection (cspan {a}) u
        + projection (cspan S) u"
proof-
  define p where "p u = projection (cspan {a}) u
                      + projection (cspan S) u" for u
  define M where "M = {x. \<exists>k. x - k *\<^sub>C a \<in> cspan S}"
  have "projection (cspan {a}) u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
    by (metis complex_vector.scale_zero_right complex_vector.span_empty complex_vector.span_insert_0 
        projection_singleton projection_zero_subspace)
  have "closed_subspace M"
    unfolding M_def
    by (metis (no_types) a2 closed_subspace_cspan_finite complex_vector.span_insert 
        finite_insert) 
  have "projection (cspan {a}) u + projection (cspan S) u
    \<in> {x. \<exists>k. x - k *\<^sub>C a \<in> cspan S}"
  proof auto 
    define k where "k = \<langle>a, u\<rangle>/\<langle>a, a\<rangle>"
    have "projection (cspan {a}) u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
      by (simp add: \<open>projection (cspan {a}) u = (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a\<close>)      
    hence "projection (cspan {a}) u +
          projection (cspan S) u - k *\<^sub>C a
          \<in> cspan S"
      unfolding k_def
      by (simp add: a2 closed_subspace_cspan_finite projection_intro2)      
    thus "\<exists>k. projection (cspan {a}) u +
              projection (cspan S) u - k *\<^sub>C a
              \<in> cspan S"
      by blast
  qed
  hence f1: "p u \<in> M"
    unfolding p_def M_def 
    by blast

  have "u - p u \<in> {x |x. \<forall>y\<in>M. \<langle>x, y\<rangle> = 0}"
  proof auto
    fix y
    assume b1: "y \<in> M"
    hence "\<exists>k. y - k *\<^sub>C a \<in> cspan S"
      unfolding M_def by simp
    then obtain k where k_def: "y - k *\<^sub>C a \<in> cspan S"
      by blast
    have "u - projection (cspan S) u \<in> orthogonal_complement (cspan S)"
      by (simp add: a2 closed_subspace_cspan_finite projection_intro1)
    moreover have "projection (cspan {a}) u \<in> orthogonal_complement (cspan S)"
      unfolding orthogonal_complement_def
    proof auto
      fix y
      assume "y \<in> cspan S"
      have "\<langle>a, y\<rangle> = 0"
        using ortho_cspan
          \<open>y \<in> cspan S\<close> a1 a2 by auto
      thus "\<langle>projection (cspan {a}) u, y\<rangle> = 0"
        by (simp add: \<open>projection (cspan {a}) u = (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a\<close>)         
    qed
    ultimately have "(u - projection (cspan S) u)
                    - projection (cspan {a}) u \<in> orthogonal_complement (cspan S)"
      using Complex_Vector_Spaces.complex_vector.span_diff
      by (smt cinner_diff_left diff_zero orthogonal_complement_D1 orthogonal_complement_I2)
    hence "u - projection (cspan {a}) u 
            - projection (cspan S) u \<in> orthogonal_complement (cspan S)"
      by (simp add: cancel_ab_semigroup_add_class.diff_right_commute)
    have "\<langle>u - projection (cspan {a}) u 
         - projection (cspan S) u, y - k *\<^sub>C a\<rangle> = 0"
      using \<open>u - projection (cspan {a}) u - projection (cspan S) u \<in> 
        orthogonal_complement (cspan S)\<close> k_def orthogonal_complement_D1 by auto      
    moreover have "\<langle>u - projection (cspan {a}) u 
         - projection (cspan S) u, k *\<^sub>C a\<rangle> = 0"
    proof-
      have "u - projection (cspan {a}) u \<in> orthogonal_complement (cspan {a})"
        by (simp add: closed_subspace_cspan_finite projection_intro1)
      moreover have "projection (cspan S) u \<in> orthogonal_complement (cspan {a})"
        unfolding orthogonal_complement_def
      proof auto
        fix y
        assume "y \<in> cspan {a}"
        hence "\<exists>k. y = k *\<^sub>C a"
          by (simp add: cspan_singleton)
        then obtain k where ky:"y = k *\<^sub>C a"
          by blast
        have "projection (cspan S) u \<in> cspan S"
          by (simp add: a2 closed_subspace_cspan_finite projection_intro2)          
        hence "\<langle>projection (cspan S) u, a\<rangle> = 0"
          by (meson a1 a2 ortho_cspan orthogonal_complement_D2 orthogonal_complement_I2)          
        thus "\<langle>projection (cspan S) u, y\<rangle> = 0"
          using ky
          by simp
      qed
      moreover have "complex_vector.subspace ( orthogonal_complement (cspan {a}))"
        by (simp add: closed_subspace.subspace closed_subspace_cspan_finite)

      ultimately have "(u - projection (cspan {a}) u) - projection (cspan S) u
                   \<in> orthogonal_complement (cspan {a})"
        by (smt complex_vector.subspace_diff)
      thus ?thesis
        using complex_vector.span_base orthogonal_complement_D1 by fastforce 
    qed
    ultimately have "\<langle>u - projection (cspan {a}) u 
         - projection (cspan S) u, y\<rangle> = 0"
      by (simp add: cinner_diff_right)
    moreover have "\<langle>u - p u, y\<rangle> =
      \<langle>u - projection (cspan {a}) u 
         - projection (cspan S) u, y\<rangle>"
      unfolding p_def
      by (simp add: diff_diff_add) 
    ultimately show "\<langle>u - p u, y\<rangle> = 0" by simp
  qed
  hence f2: "u - p u \<in> orthogonal_complement M"
    unfolding orthogonal_complement_def
    by blast
  hence "projection M u = p u"
    using projection_uniq[where x = "p u" and h = u and M = M]
      \<open>closed_subspace M\<close> f1 by auto     
  thus ?thesis 
    unfolding p_def M_def by auto
qed

lemma Span_canonical_basis[simp]: "Span (set canonical_basis) = top"
  using Span.rep_eq space_as_set_inject top_clinear_space.rep_eq
    closure_UNIV is_generator_set
  by metis

unbundle no_nsa_notation


end

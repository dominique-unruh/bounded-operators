(*  Title:      Complex_Inner_Product.thy
    Author:     Dominique Unruh (University of Tartu)
    Author:     Jose Manuel Rodriguez Caballero (University of Tartu)
*)

section \<open>Complex Inner Product Spaces\<close>

theory Complex_Inner_Product

imports
  Complex_Vector_Spaces

begin

text\<open>
  We extend the file @text{HOL/Analysis/Inner_Product.thy (Brian Huffman)} to the complex numbers.
\<close>

subsection \<open>Complex inner product spaces\<close>

unbundle notation_norm

class complex_inner = complex_normed_vector + sgn_div_norm + dist_norm + uniformity_dist 
  + open_uniformity +
  fixes cinner :: "'a \<Rightarrow> 'a \<Rightarrow> complex"  ("\<langle>_, _\<rangle>") 
  assumes cinner_cnj_commute: "\<langle>x, y\<rangle> = cnj \<langle>y, x\<rangle>"
    and cinner_add_left: "\<langle>x + y, z\<rangle> = \<langle>x, z\<rangle> +  \<langle>y, z\<rangle>"
    and cinner_scaleC_left [simp]: "\<langle>r *\<^sub>C x, y\<rangle> = (cnj r) * \<langle>x, y\<rangle>"
    and cinner_ge_zero [simp]: "\<langle>x, x\<rangle> \<in> complex_of_real ` {r. r \<ge> 0}"
    and cinner_eq_zero_iff [simp]: "\<langle>x, x\<rangle> = 0 \<longleftrightarrow> x = 0"
    and norm_eq_sqrt_cinner: "\<parallel>x\<parallel> = sqrt \<parallel>\<langle>x, x\<rangle>\<parallel>"
begin

lemma cinner_zero_left [simp]: "\<langle>0, x\<rangle> = 0"
  by (metis (full_types) cancel_comm_monoid_add_class.add_cancel_left_left local.cinner_add_left local.minus_zero local.right_minus)

lemma cinner_minus_left [simp]: "\<langle>- x, y\<rangle> = - \<langle>x, y\<rangle>"
  by (metis (mono_tags, lifting) cancel_ab_semigroup_add_class.add_diff_cancel_right' group_add_class.add.inverse_unique group_add_class.add.left_inverse group_add_class.add_minus_cancel local.cinner_add_left local.minus_add_cancel)

lemma cinner_diff_left: "\<langle>x - y, z\<rangle> = \<langle>x, z\<rangle> - \<langle>y, z\<rangle>"
  by (metis cinner_minus_left group_add_class.diff_conv_add_uminus local.cinner_add_left local.diff_conv_add_uminus)

lemma cinner_sum_left: "\<langle>\<Sum>x\<in>A. f x, y\<rangle> = (\<Sum>x\<in>A. \<langle>f x, y\<rangle>)"
  by (cases "finite A", induct set: finite, simp_all add: cinner_add_left)

lemma call_zero_iff [simp]: "(\<forall>u. \<langle>x, u\<rangle> = 0) \<longleftrightarrow> (x = 0)"
  by auto (use cinner_eq_zero_iff in blast)

text \<open>Transfer distributivity rules to right argument.\<close>

lemma cinner_add_right: "\<langle>x, y + z\<rangle> = \<langle>x, y\<rangle> + \<langle>x, z\<rangle>"
  by (metis complex_cnj_add local.cinner_add_left local.cinner_cnj_commute)

lemma cinner_scaleR_right [simp]: "\<langle>x, r *\<^sub>R y\<rangle> = r * \<langle>x, y\<rangle>"
  by (metis complex_cnj_complex_of_real complex_cnj_mult local.cinner_cnj_commute local.cinner_scaleC_left local.scaleR_scaleC)

lemma cinner_zero_right [simp]: "\<langle>x, 0\<rangle> = 0"
  by (metis (mono_tags, lifting) cinner_zero_left local.cinner_cnj_commute)

lemma cinner_minus_right [simp]: "\<langle>x, - y\<rangle> = - \<langle>x, y\<rangle>"
  by (metis cinner_minus_left complex_cnj_minus local.cinner_cnj_commute)

lemma cinner_diff_right: "\<langle>x, y - z\<rangle> = \<langle>x, y\<rangle> - \<langle>x, z\<rangle>"
  by (metis cinner_add_right cinner_minus_right group_add_class.diff_conv_add_uminus local.diff_conv_add_uminus)

lemma cinner_sum_right: "\<langle>x, \<Sum>y\<in>A. f y\<rangle> = (\<Sum>y\<in>A. \<langle>x, f y\<rangle>)"
  using cinner_sum_left [of f A x] cinner_cnj_commute
  by (metis (mono_tags, lifting) cnj_sum comm_monoid_add_class.sum.cong)

lemmas cinner_add [algebra_simps] = cinner_add_left cinner_add_right
lemmas cinner_diff [algebra_simps]  = cinner_diff_left cinner_diff_right
lemmas cinner_scaleR = cinner_scaleC_left cinner_scaleR_right

text \<open>Legacy theorem names\<close>
lemmas cinner_left_distrib = cinner_add_left
lemmas cinner_right_distrib = cinner_add_right
lemmas cinner_distrib = cinner_left_distrib cinner_right_distrib

lemma cinner_gt_zero_iff [simp]: "0 \<noteq> \<langle>x, x\<rangle> \<longleftrightarrow> x \<noteq> 0"
  by (simp add: order_less_le)

lemma cinner_norm_of_square: "complex_of_real \<parallel>\<langle>x, x\<rangle>\<parallel> = \<langle>x, x\<rangle>"
proof-
  have \<open>\<exists>r. \<langle>x, x\<rangle> = complex_of_real r \<and> r \<ge> 0\<close>
    using cinner_ge_zero
    by (meson image_iff mem_Collect_eq)
  then obtain r where a1: "\<langle>x, x\<rangle> = complex_of_real r" and a2:"r \<ge> 0"
    by blast
  have "\<parallel>complex_of_real r\<parallel> = r"
    using a2 by simp
  thus ?thesis using a1 by simp
qed

lemma cpower2_norm_eq_inner: "\<parallel>x\<parallel>\<^sup>2 = \<langle>x, x\<rangle>"
proof-
  have "\<parallel>x\<parallel>\<^sup>2 = \<parallel>\<langle>x, x\<rangle>\<parallel>"
    using norm_eq_sqrt_cinner by simp 
  thus ?thesis using cinner_norm_of_square by simp
qed

text \<open>Identities involving real multiplication and division.\<close>

lemma cinner_mult_left: "\<langle>(of_real m * a), b\<rangle> = m * \<langle>a, b\<rangle>"
  by (metis (mono_tags, lifting) complex_cnj_scaleR complex_inner_class.cinner_cnj_commute complex_inner_class.cinner_scaleR_right scaleR_conv_of_real)

lemma cinner_mult_right: "\<langle>a, (of_real m * b)\<rangle> = m * \<langle>a, b\<rangle>"
  by (metis complex_inner_class.cinner_scaleR_right scaleR_conv_of_real)

lemma cinner_mult_left': "\<langle>a * of_real m, b\<rangle> = m * \<langle>a, b\<rangle>"
  by (metis cinner_mult_left mult.right_neutral mult_scaleR_right scaleR_conv_of_real)

lemma cinner_mult_right': "\<langle>a, b * of_real m\<rangle> = \<langle>a, b\<rangle> * m"
  by (metis (mono_tags, lifting) cinner_mult_left' complex_cnj_scaleR complex_inner_class.cinner_cnj_commute mult.commute scaleR_conv_of_real)

lemma Cauchy_Schwarz_ineq_square:
  "\<parallel>\<langle>x, y\<rangle>\<parallel>^2 \<le> \<parallel>x\<parallel>^2 * \<parallel>y\<parallel>^2"
proof (cases)
  assume "y = 0"
  thus ?thesis by simp
next
  assume y: "y \<noteq> 0"
  have [simp]: "cnj (\<langle>y , y\<rangle>) = \<langle>y , y\<rangle>" for y
    by (metis local.cinner_cnj_commute)    
  define r where "r = cnj \<langle>x, y\<rangle> / \<langle>y, y\<rangle>"
  have "\<exists>t. \<langle>x - scaleC r y, x - scaleC r y\<rangle> = complex_of_real t \<and> t \<ge> 0"
    by (metis cinner_norm_of_square real_normed_vector_class.norm_ge_zero)    
  then obtain t where a1: "\<langle>x - scaleC r y, x - scaleC r y\<rangle> = complex_of_real t" and a2: "t \<ge> 0"
    by blast
  have "\<exists>t'. \<langle>y, y\<rangle> = complex_of_real t' \<and> t' \<ge> 0"
    by (metis (mono_tags) cinner_norm_of_square real_normed_vector_class.norm_ge_zero)
  then obtain t' where b1: "\<langle>y, y\<rangle> = complex_of_real t'" and b2: "t' \<ge> 0"
    by blast
  define T where "T = t*t'"
  have T_pos: "T \<ge> 0"
    unfolding T_def
    by (simp add: a2 b2)
  have "t = \<langle>x - r *\<^sub>C y, x - r *\<^sub>C y\<rangle>"
    using a1 by simp
  also have "\<dots> = \<langle>x, x\<rangle> - r * \<langle>x, y\<rangle> - cnj r * \<langle>y, x\<rangle> + r * cnj r * \<langle>y, y\<rangle>"
    by (smt ab_group_add_class.diff_add_eq ab_semigroup_mult_class.mult_ac(1) cinner_diff_left cinner_diff_right complex_cnj_divide complex_cnj_mult group_add_class.diff_diff_eq2 local.cinner_cnj_commute local.cinner_scaleC_left r_def)
  also have "\<dots> = \<langle>x, x\<rangle> - \<langle>y, x\<rangle> * cnj r"
    unfolding r_def by auto
  also have "\<dots> = \<langle>x, x\<rangle> - \<langle>x, y\<rangle> * cnj \<langle>x, y\<rangle> / \<langle>y, y\<rangle>"
    unfolding r_def
    by (metis complex_cnj_divide local.cinner_cnj_commute mult.commute times_divide_eq_left) 
  finally have "t = \<langle>x, x\<rangle> - \<langle>x, y\<rangle> * cnj \<langle>x, y\<rangle> / \<langle>y, y\<rangle>"
    by simp    
  hence "\<langle>x, y\<rangle> * cnj \<langle>x, y\<rangle> / \<langle>y, y\<rangle> + t = \<langle>x, x\<rangle>"
    by (simp add: le_diff_eq)
  hence "\<langle>x, y\<rangle> * cnj \<langle>x, y\<rangle> + t * \<langle>y, y\<rangle> = \<langle>x, x\<rangle> * \<langle>y, y\<rangle>"
    by (simp add: add_divide_eq_if_simps(2) nonzero_divide_eq_eq y)
  hence "\<langle>x, y\<rangle> * cnj \<langle>x, y\<rangle> + t * \<langle>y, y\<rangle> = \<parallel>x\<parallel>^2 * \<parallel>y\<parallel>^2"
    using cpower2_norm_eq_inner by auto
  hence "\<parallel>\<langle>x, y\<rangle>\<parallel>^2 + t * \<langle>y, y\<rangle> = \<parallel>x\<parallel>^2 * \<parallel>y\<parallel>^2"
    using complex_norm_square by auto    
  hence "\<parallel>\<langle>x, y\<rangle>\<parallel>^2 + complex_of_real T = \<parallel>x\<parallel>^2 * \<parallel>y\<parallel>^2"
    unfolding T_def using b1 by auto
  thus ?thesis using T_pos by (smt of_real_add of_real_eq_iff)    
qed

lemma Cauchy_Schwarz_ineq:
  "\<parallel>\<langle>x, y\<rangle>\<parallel> \<le> \<parallel>x\<parallel> * \<parallel>y\<parallel>"
  using Cauchy_Schwarz_ineq_square
  by (simp add: Cauchy_Schwarz_ineq_square power2_le_imp_le power_mult_distrib zero_le_mult_iff)

subclass complex_normed_vector ..

end


lemma complex_norm_le: "\<parallel>x\<parallel> \<le> \<parallel>y\<parallel> \<longleftrightarrow> \<parallel>\<langle>x, x\<rangle>\<parallel> \<le> \<parallel>\<langle>y, y\<rangle>\<parallel>"
  by (simp add: norm_eq_sqrt_cinner)


lemma complex_norm_lt: "\<parallel>x\<parallel> < \<parallel>y\<parallel> \<longleftrightarrow> \<parallel>\<langle>x, x\<rangle>\<parallel> < \<parallel>\<langle>y, y\<rangle>\<parallel>"
  by (simp add: norm_eq_sqrt_cinner)


lemma complex_norm_eq: "\<parallel>x\<parallel> = \<parallel>y\<parallel> \<longleftrightarrow> \<parallel>\<langle>x, x\<rangle>\<parallel> = \<parallel>\<langle>y, y\<rangle>\<parallel>"
  by (smt complex_norm_le)


lemma complex_norm_eq_1: "\<parallel>x\<parallel> = 1 \<longleftrightarrow> \<parallel>\<langle>x, x\<rangle>\<parallel> = 1"
  by (simp add: norm_eq_sqrt_cinner)

lemma complex_inner_divide_left:
  fixes a :: "'a :: {complex_inner,real_div_algebra}"
  shows "\<langle>a / of_real m, b\<rangle> = \<langle>a, b\<rangle> / m"
proof-
  have "\<langle>a / of_real m, b\<rangle> = \<langle>(inverse (of_real m)) * a, b\<rangle>"
    by (metis cinner_mult_left cinner_mult_left' divide_inverse of_real_inverse)
  also have "\<dots> = (cnj (inverse (of_real m))) * \<langle>a, b\<rangle>"
    by (metis cinner_mult_left complex_cnj_complex_of_real of_real_inverse)
  also have "\<dots> = (inverse (of_real m)) * \<langle>a, b\<rangle>"
    by simp
  also have "\<dots> = \<langle>a, b\<rangle> / (of_real m)"
    by (simp add: divide_inverse)
  finally show ?thesis by blast
qed

lemma complex_inner_divide_right:
  fixes a :: "'a :: {complex_inner,real_div_algebra}"
  shows "\<langle>a, b / of_real m\<rangle> = \<langle>a, b\<rangle> / m"
proof-
  have "\<langle>a, b / of_real m\<rangle> = \<langle>a, (inverse (of_real m)) * b\<rangle>"
    by (metis (no_types, lifting) cinner_cnj_commute cinner_mult_left cinner_mult_left' 
        divide_inverse of_real_inverse)    
  also have "\<dots> = (inverse (of_real m)) * \<langle>a, b\<rangle>"
    by (metis cinner_mult_right of_real_inverse)
  also have "\<dots> = \<langle>a, b\<rangle> / (of_real m)"
    by (simp add: divide_inverse)
  finally show ?thesis by blast
qed

lemma bounded_sesquilinear_cinner:
  "bounded_bilinear (cinner::'a::complex_inner \<Rightarrow> 'a \<Rightarrow> complex)"
proof
  show "\<langle>a + a', b\<rangle> = \<langle>a, b\<rangle> + \<langle>a', b\<rangle>"
    for a :: 'a
      and a' :: 'a
      and b :: 'a
    by (simp add: cinner_left_distrib)

  show "\<langle>a, b + b'\<rangle> = \<langle>a, b\<rangle> + \<langle>a, b'\<rangle>"
    for a :: 'a
      and b :: 'a
      and b' :: 'a
    by (simp add: cinner_right_distrib)

  show "\<langle>r *\<^sub>R a, b\<rangle> = r *\<^sub>R \<langle>a, b\<rangle>"
    for r :: real
      and a :: 'a
      and b :: 'a
    by (metis cinner_cnj_commute cinner_scaleR_right complex_cnj_complex_of_real complex_cnj_mult 
        scaleR_conv_of_real)

  show "\<langle>a, r *\<^sub>R b\<rangle> = r *\<^sub>R \<langle>a, b\<rangle>"
    for a :: 'a
      and r :: real
      and b :: 'a
    by (simp add: scaleR_conv_of_real)

  show "\<exists>K. \<forall>a b. \<parallel>\<langle>a::'a, b\<rangle>\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
    by (metis complex_inner_class.Cauchy_Schwarz_ineq 
        mult.commute vector_space_over_itself.scale_one)    
qed

subsection \<open>Class instances\<close>

instantiation complex :: complex_inner
begin

definition cinner_real_def [simp]: "cinner = (\<lambda>x y. (cnj x) * y)"

instance
proof
  show "\<langle>x, y\<rangle> = cnj \<langle>y, x\<rangle>"
    for x :: complex
      and y :: complex
    by simp

  show "\<langle>x + y, z\<rangle> = \<langle>x, z\<rangle> + \<langle>y, z\<rangle>"
    for x :: complex
      and y :: complex
      and z :: complex
    apply auto
    using ring_class.ring_distribs(2) by auto
  show "\<langle>r *\<^sub>C x, y\<rangle> = cnj r * \<langle>x, y\<rangle>"
    for r :: complex
      and x :: complex
      and y :: complex
    by auto
  show "\<langle>x, x\<rangle> \<in> complex_of_real ` {r. 0 \<le> r}"
    for x :: complex
  proof auto
    have "cnj x * x = \<parallel>x\<parallel>^2"
      using complex_norm_square by auto
    moreover have "\<parallel>x\<parallel>^2 \<ge> 0"
      by (metis zero_le_power2)
    ultimately show "cnj x * x \<in> complex_of_real ` {r. 0 \<le> r}"
      by blast      
  qed
  show "(\<langle>x, x\<rangle> = 0) = (x = 0)"
    for x :: complex
  proof
    show "x = 0"
      if "\<langle>x, x\<rangle> = 0"
      using that by auto
    show "\<langle>x, x\<rangle> = 0"
      if "x = 0"
      using that by auto
  qed
  show "cmod x = sqrt (cmod \<langle>x, x\<rangle>)"
    for x :: complex
  proof auto
    have "cmod (cnj x * x) = (cmod (cnj x))*(cmod x)"
      by (simp add: norm_mult)      
    also have "\<dots> = (cmod x)*(cmod x)"
      by simp      
    finally have "cmod (cnj x * x) = (cmod x)^2"
      by (simp add: power2_eq_square)      
    thus "cmod x = sqrt (cmod (cnj x * x))"
      by simp
  qed
qed

end

lemma
  shows complex_inner_1_left[simp]: "\<langle>1, x\<rangle> = x"
    and complex_inner_1_right[simp]: "\<langle>x, 1\<rangle> = cnj x"
  by auto

lemma complex_dot_square_norm: "\<parallel>\<langle>x, x\<rangle>\<parallel> = \<parallel>x\<parallel>\<^sup>2"
  by (metis cinner_norm_of_square cpower2_norm_eq_inner of_real_eq_iff)

lemma complex_norm_eq_square: "\<parallel>x\<parallel> = a \<longleftrightarrow> 0 \<le> a \<and> \<langle>x, x\<rangle> = complex_of_real(a\<^sup>2)"
  by (metis cpower2_norm_eq_inner norm_ge_zero of_real_eq_iff real_sqrt_unique)

lemma complex_norm_le_square: "\<parallel>x\<parallel> \<le> a \<longleftrightarrow> 0 \<le> a \<and> \<parallel>\<langle>x, x\<rangle>\<parallel> \<le> a\<^sup>2"
  by (smt complex_dot_square_norm norm_ge_zero power2_le_imp_le)

lemma complex_norm_ge_square: "\<parallel>x\<parallel> \<ge> a \<longleftrightarrow> a \<le> 0 \<or> \<parallel>\<langle>x, x\<rangle>\<parallel> \<ge> a\<^sup>2"
  by (smt complex_dot_square_norm complex_norm_le_square power2_eq_imp_eq)

lemma complex_norm_lt_square: "\<parallel>x\<parallel> < a \<longleftrightarrow> 0 < a \<and> \<parallel>\<langle>x, x\<rangle>\<parallel> < a\<^sup>2"
  by (smt complex_norm_ge_square)

lemma complex_norm_gt_square: "\<parallel>x\<parallel> > a \<longleftrightarrow> a < 0 \<or> \<parallel>\<langle>x, x\<rangle>\<parallel> > a\<^sup>2"
  by (smt complex_norm_le_square)

lemma polarization_identity_plus:
  "\<parallel>x + y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 + 2*Re \<langle>x, y\<rangle>"
  \<comment> \<open>Shown in the proof of Corollary 1.5 in @{cite conway2013course}\<close> 
proof-
  have "\<langle>x, y\<rangle> + \<langle>y, x\<rangle> = \<langle>x , y\<rangle> + cnj \<langle>x , y\<rangle>"
    using cinner_cnj_commute by auto    
  also have "\<dots> = 2 * Re \<langle>x , y\<rangle>"
    using complex_add_cnj by presburger
  finally have b1: "\<langle>x, y\<rangle> + \<langle>y, x\<rangle> = 2 * Re \<langle>x , y\<rangle>"
    by blast
  have "\<parallel>x + y\<parallel>^2 = \<langle>x+y, x+y\<rangle>"
    using cpower2_norm_eq_inner by blast    
  also have "\<dots> = \<langle>x , x\<rangle> + \<langle>x , y\<rangle> + \<langle>y , x\<rangle> + \<langle>y , y\<rangle>"
    by (simp add: cinner_left_distrib cinner_right_distrib)    
  finally show ?thesis using b1
    by (smt Re_complex_of_real cpower2_norm_eq_inner plus_complex.simps(1)) 
qed


lemma complex_dot_norm: "Re \<langle>x, y\<rangle> = (\<parallel>x + y\<parallel>\<^sup>2 - \<parallel>x\<parallel>\<^sup>2 - \<parallel>y\<parallel>\<^sup>2) / 2"
  using polarization_identity_plus
  by (simp add: polarization_identity_plus)

lemma polarization_identity_minus:
  "\<parallel>x - y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 - 2 * Re \<langle>x, y\<rangle>"
proof-
  have \<open>\<parallel>x + (-y)\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>-y\<parallel>^2 + 2*Re (\<langle>x , (-y)\<rangle>)\<close>
    using polarization_identity_plus by blast
  hence \<open>\<parallel>x - y\<parallel>^2 = \<parallel>x\<parallel>^2 + \<parallel>y\<parallel>^2 - 2*Re (\<langle>x , y\<rangle>)\<close>
    by simp
  thus ?thesis by blast
qed

lemma complex_dot_norm_neg: "Re \<langle>x, y\<rangle> = (\<parallel>x\<parallel>\<^sup>2 + \<parallel>y\<parallel>\<^sup>2 - \<parallel>x - y\<parallel>\<^sup>2) / 2"
  by (simp add: polarization_identity_minus) 

lemma of_real_cinner_1 [simp]: 
  "\<langle>(of_real x), (1 :: 'a :: {complex_inner, real_normed_algebra_1})\<rangle> = cnj x"
  by (metis (no_types, lifting) cinner_cnj_commute cinner_norm_of_square cinner_scaleR_right 
      complex_norm_eq_1 of_real_1 of_real_def real_normed_algebra_1_class.norm_one
      scaleR_conv_of_real)

unbundle no_notation_norm

end
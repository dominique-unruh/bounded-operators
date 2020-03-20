(*  Title:      Complex_Inner_Product.thy
    Author:     Dominique Unruh (University of Tartu)
    Author:     Jose Manuel Rodriguez Caballero (University of Tartu)
*)

section \<open>Complex Inner Product Spaces\<close>

theory Complex_Inner_Product

imports
  Complex_Vector_Spaces

begin

text\<open>We extend the file HOL/Analysis/Inner_Product.thy (Brian Huffman) to the complex numbers.\<close>

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

unbundle no_notation_norm

end
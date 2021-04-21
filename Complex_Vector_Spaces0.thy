(*  Title:      HOL/Real_Vector_Spaces.thy
    Author:     Brian Huffman
    Author:     Johannes Hölzl
*)

section \<open>Vector Spaces and Algebras over the Reals\<close>

theory Complex_Vector_Spaces0
  imports HOL.Real_Vector_Spaces HOL.Topological_Spaces HOL.Vector_Spaces
    Complex_Main Jordan_Normal_Form.Conjugate
begin                                   

declare less_complex_def[simp del]
declare less_eq_complex_def[simp del]

subsection \<open>Complex vector spaces\<close>

class scaleC = scaleR +
  fixes scaleC :: "complex \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "*\<^sub>C" 75)
  assumes scaleR_scaleC: "scaleR r = scaleC (complex_of_real r)"
begin

abbreviation divideC :: "'a \<Rightarrow> complex \<Rightarrow> 'a"  (infixl "'/\<^sub>C" 70)
  where "x /\<^sub>C c \<equiv> inverse c *\<^sub>C x"

end

class complex_vector = scaleC + ab_group_add +
  assumes scaleC_add_right: "a *\<^sub>C (x + y) = (a *\<^sub>C x) + (a *\<^sub>C y)"
    and scaleC_add_left: "(a + b) *\<^sub>C x = (a *\<^sub>C x) + (b *\<^sub>C x)"
    and scaleC_scaleC[simp]: "a *\<^sub>C (b *\<^sub>C x) =  (a * b) *\<^sub>C x"
    and scaleC_one[simp]: "1 *\<^sub>C x = x"

class complex_algebra = complex_vector + ring +
  assumes mult_scaleC_left [simp]: "a *\<^sub>C x * y = a *\<^sub>C (x * y)"
    and mult_scaleC_right [simp]: "x * a *\<^sub>C y = a *\<^sub>C (x * y)"

class complex_algebra_1 = complex_algebra + ring_1

class complex_div_algebra = complex_algebra_1 + division_ring

class complex_field = complex_div_algebra + field

instantiation complex :: complex_field
begin

definition complex_scaleC_def [simp]: "scaleC a x = a * x"

instance
proof intro_classes
  fix r :: real and a b x y :: complex
  show "((*\<^sub>R) r::complex \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    by (auto simp add: scaleR_conv_of_real)
  show "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
    by (simp add: ring_class.ring_distribs(1))
  show "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x"
    by (simp add: algebra_simps)
  show "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x"
    by simp
  show "1 *\<^sub>C x = x"
    by simp
  show "a *\<^sub>C (x::complex) * y = a *\<^sub>C (x * y)"
    by simp
  show "(x::complex) * a *\<^sub>C y = a *\<^sub>C (x * y)"
    by simp
qed

end

locale clinear = Vector_Spaces.linear "scaleC::_\<Rightarrow>_\<Rightarrow>'a::complex_vector" "scaleC::_\<Rightarrow>_\<Rightarrow>'b::complex_vector"
begin

lemmas scaleC = scale

end

(* TODO: Does the global_interpretation command allow us to prefix all global names with a "c"? *)
global_interpretation complex_vector?: vector_space "scaleC :: complex \<Rightarrow> 'a \<Rightarrow> 'a :: complex_vector"
  rewrites "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    and "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
  defines cdependent_raw_def: cdependent = complex_vector.dependent
    and crepresentation_raw_def: crepresentation = complex_vector.representation
    and csubspace_raw_def: csubspace = complex_vector.subspace
    and cspan_raw_def: cspan = complex_vector.span
    and cextend_basis_raw_def: cextend_basis = complex_vector.extend_basis
    and cdim_raw_def: cdim = complex_vector.dim
proof unfold_locales
  show "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear" "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
    by (force simp: clinear_def complex_scaleC_def[abs_def])+
qed (use scaleC_add_right scaleC_add_left in auto)

hide_const (open)\<comment> \<open>locale constants\<close>
  complex_vector.dependent
  complex_vector.independent
  complex_vector.representation
  complex_vector.subspace
  complex_vector.span
  complex_vector.extend_basis
  complex_vector.dim

abbreviation "cindependent x \<equiv> \<not> cdependent x"

(* TODO: Does the global_interpretation command allow us to prefix all global names with a "c"? *)
global_interpretation complex_vector?: vector_space_pair "scaleC::_\<Rightarrow>_\<Rightarrow>'a::complex_vector" "scaleC::_\<Rightarrow>_\<Rightarrow>'b::complex_vector"
  rewrites  "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    and "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
  defines cconstruct_raw_def: cconstruct = complex_vector.construct
proof unfold_locales
  show "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
  unfolding clinear_def complex_scaleC_def by auto
qed (auto simp: clinear_def)

hide_const (open)\<comment> \<open>locale constants\<close>
  complex_vector.construct

lemma linear_compose: "linear f \<Longrightarrow> linear g \<Longrightarrow> linear (g \<circ> f)"
  unfolding linear_def by (rule Vector_Spaces.linear_compose)

text \<open>Recover original theorem names\<close>

lemmas scaleC_left_commute = complex_vector.scale_left_commute
lemmas scaleC_zero_left = complex_vector.scale_zero_left
lemmas scaleC_minus_left = complex_vector.scale_minus_left
lemmas scaleC_diff_left = complex_vector.scale_left_diff_distrib
lemmas scaleC_sum_left = complex_vector.scale_sum_left
lemmas scaleC_zero_right = complex_vector.scale_zero_right
lemmas scaleC_minus_right = complex_vector.scale_minus_right
lemmas scaleC_diff_right = complex_vector.scale_right_diff_distrib
lemmas scaleC_sum_right = complex_vector.scale_sum_right
lemmas scaleC_eq_0_iff = complex_vector.scale_eq_0_iff
lemmas scaleC_left_imp_eq = complex_vector.scale_left_imp_eq
lemmas scaleC_right_imp_eq = complex_vector.scale_right_imp_eq
lemmas scaleC_cancel_left = complex_vector.scale_cancel_left
lemmas scaleC_cancel_right = complex_vector.scale_cancel_right

lemma [field_simps]:
  "c \<noteq> 0 \<Longrightarrow> a = b /\<^sub>C c \<longleftrightarrow> c *\<^sub>C a = b"
  "c \<noteq> 0 \<Longrightarrow> b /\<^sub>C c = a \<longleftrightarrow> b = c *\<^sub>C a"
  "c \<noteq> 0 \<Longrightarrow> a + b /\<^sub>C c = (c *\<^sub>C a + b) /\<^sub>C c"
  "c \<noteq> 0 \<Longrightarrow> a /\<^sub>C c + b = (a + c *\<^sub>C b) /\<^sub>C c"
  "c \<noteq> 0 \<Longrightarrow> a - b /\<^sub>C c = (c *\<^sub>C a - b) /\<^sub>C c"
  "c \<noteq> 0 \<Longrightarrow> a /\<^sub>C c - b = (a - c *\<^sub>C b) /\<^sub>C c"
  "c \<noteq> 0 \<Longrightarrow> - (a /\<^sub>C c) + b = (- a + c *\<^sub>C b) /\<^sub>C c"
  "c \<noteq> 0 \<Longrightarrow> - (a /\<^sub>C c) - b = (- a - c *\<^sub>C b) /\<^sub>C c"
  for a b :: "'a :: complex_vector"
  by (auto simp add: scaleC_add_right scaleC_add_left scaleC_diff_right scaleC_diff_left)


text \<open>Legacy names -- omitted\<close>

(* lemmas scaleC_left_distrib = scaleC_add_left
lemmas scaleC_right_distrib = scaleC_add_right
lemmas scaleC_left_diff_distrib = scaleC_diff_left
lemmas scaleC_right_diff_distrib = scaleC_diff_right *)

(* TODO: These with a c *)
lemmas linear_injective_0 = linear_inj_iff_eq_0
  and linear_injective_on_subspace_0 = linear_inj_on_iff_eq_0
  and linear_cmul = linear_scale
  and linear_scaleC = linear_scale_self
  and subspace_mul = subspace_scale
  and span_linear_image = linear_span_image
  and span_0 = span_zero
  and span_mul = span_scale
  and injective_scaleC = injective_scale

lemma scaleC_minus1_left [simp]: "scaleC (-1) x = - x"
  for x :: "'a::complex_vector"
  using scaleC_minus_left [of 1 x] by simp

lemma scaleC_2:
  fixes x :: "'a::complex_vector"
  shows "scaleC 2 x = x + x"
  unfolding one_add_one [symmetric] scaleC_add_left by simp

lemma scaleC_half_double [simp]:
  fixes a :: "'a::complex_vector"
  shows "(1 / 2) *\<^sub>C (a + a) = a"
proof -
  have "\<And>r. r *\<^sub>C (a + a) = (r * 2) *\<^sub>C a"
    by (metis scaleC_2 scaleC_scaleC)
  thus ?thesis
    by simp
qed

lemma linear_scale_complex:
  fixes c::complex shows "clinear f \<Longrightarrow> f (c * b) = c * f b"
  using linear_scale by fastforce


interpretation scaleC_left: additive "(\<lambda>a. scaleC a x :: 'a::complex_vector)"
  by standard (rule scaleC_add_left)

interpretation scaleC_right: additive "(\<lambda>x. scaleC a x :: 'a::complex_vector)"
  by standard (rule scaleC_add_right)

lemma nonzero_inverse_scaleC_distrib:
  "a \<noteq> 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> inverse (scaleC a x) = scaleC (inverse a) (inverse x)"
  for x :: "'a::complex_div_algebra"
  by (rule inverse_unique) simp

lemma inverse_scaleC_distrib: "inverse (scaleC a x) = scaleC (inverse a) (inverse x)"
  for x :: "'a::{complex_div_algebra,division_ring}"
  by (metis inverse_zero nonzero_inverse_scaleC_distrib scale_eq_0_iff)

(* lemmas sum_constant_scaleC = real_vector.sum_constant_scale\<comment> \<open>legacy name\<close> *)

named_theorems vector_add_divide_simps "to simplify sums of scaled vectors"

lemma [vector_add_divide_simps]:
  "v + (b / z) *\<^sub>C w = (if z = 0 then v else (z *\<^sub>C v + b *\<^sub>C w) /\<^sub>C z)"
  "a *\<^sub>C v + (b / z) *\<^sub>C w = (if z = 0 then a *\<^sub>C v else ((a * z) *\<^sub>C v + b *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v + w = (if z = 0 then w else (a *\<^sub>C v + z *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v + b *\<^sub>C w = (if z = 0 then b *\<^sub>C w else (a *\<^sub>C v + (b * z) *\<^sub>C w) /\<^sub>C z)"
  "v - (b / z) *\<^sub>C w = (if z = 0 then v else (z *\<^sub>C v - b *\<^sub>C w) /\<^sub>C z)"
  "a *\<^sub>C v - (b / z) *\<^sub>C w = (if z = 0 then a *\<^sub>C v else ((a * z) *\<^sub>C v - b *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v - w = (if z = 0 then -w else (a *\<^sub>C v - z *\<^sub>C w) /\<^sub>C z)"
  "(a / z) *\<^sub>C v - b *\<^sub>C w = (if z = 0 then -b *\<^sub>C w else (a *\<^sub>C v - (b * z) *\<^sub>C w) /\<^sub>C z)"
  for v :: "'a :: complex_vector"
  by (simp_all add: divide_inverse_commute scaleC_add_right scaleC_diff_right)

lemma eq_vector_fraction_iff [vector_add_divide_simps]:
  fixes x :: "'a :: complex_vector"
  shows "(x = (u / v) *\<^sub>C a) \<longleftrightarrow> (if v=0 then x = 0 else v *\<^sub>C x = u *\<^sub>C a)"
  by auto (metis (no_types) divide_eq_1_iff divide_inverse_commute scaleC_one scaleC_scaleC)

lemma vector_fraction_eq_iff [vector_add_divide_simps]:
  fixes x :: "'a :: complex_vector"
  shows "((u / v) *\<^sub>C a = x) \<longleftrightarrow> (if v=0 then x = 0 else u *\<^sub>C a = v *\<^sub>C x)"
  by (metis eq_vector_fraction_iff)

lemma complex_vector_affinity_eq:
  fixes x :: "'a :: complex_vector"
  assumes m0: "m \<noteq> 0"
  shows "m *\<^sub>C x + c = y \<longleftrightarrow> x = inverse m *\<^sub>C y - (inverse m *\<^sub>C c)"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  hence "m *\<^sub>C x = y - c" by (simp add: field_simps)
  hence "inverse m *\<^sub>C (m *\<^sub>C x) = inverse m *\<^sub>C (y - c)" by simp
  thus "x = inverse m *\<^sub>C y - (inverse m *\<^sub>C c)"
    using m0
    by (simp add: complex_vector.scale_right_diff_distrib)
next
  assume ?rhs
  with m0 show "m *\<^sub>C x + c = y"
    by (simp add: complex_vector.scale_right_diff_distrib)
qed

lemma complex_vector_eq_affinity: "m \<noteq> 0 \<Longrightarrow> y = m *\<^sub>C x + c \<longleftrightarrow> inverse m *\<^sub>C y - (inverse m *\<^sub>C c) = x"
  for x :: "'a::complex_vector"
  using complex_vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma scaleC_eq_iff [simp]: "b + u *\<^sub>C a = a + u *\<^sub>C b \<longleftrightarrow> a = b \<or> u = 1"
  for a :: "'a::complex_vector"
proof (cases "u = 1")
  case True
  thus ?thesis by auto
next
  case False
  have "a = b" if "b + u *\<^sub>C a = a + u *\<^sub>C b"
  proof -
    from that have "(u - 1) *\<^sub>C a = (u - 1) *\<^sub>C b"
      by (simp add: algebra_simps)
    with False show ?thesis
      by auto
  qed
  thus ?thesis by auto
qed

lemma scaleC_collapse [simp]: "(1 - u) *\<^sub>C a + u *\<^sub>C a = a"
  for a :: "'a::complex_vector"
  by (simp add: algebra_simps)

subsection \<open>Embedding of the Complex Numbers into any \<open>complex_algebra_1\<close>: \<open>of_complex\<close>\<close>


definition of_complex :: "complex \<Rightarrow> 'a::complex_algebra_1"
  where "of_complex c = scaleC c 1"


lemma scaleC_conv_of_complex: "scaleC r x = of_complex r * x"
  by (simp add: of_complex_def)

lemma of_complex_0 [simp]: "of_complex 0 = 0"
  by (simp add: of_complex_def)

lemma of_complex_1 [simp]: "of_complex 1 = 1"
  by (simp add: of_complex_def)

lemma of_complex_add [simp]: "of_complex (x + y) = of_complex x + of_complex y"
  by (simp add: of_complex_def scaleC_add_left)

lemma of_complex_minus [simp]: "of_complex (- x) = - of_complex x"
  by (simp add: of_complex_def)

lemma of_complex_diff [simp]: "of_complex (x - y) = of_complex x - of_complex y"
  by (simp add: of_complex_def scaleC_diff_left)

lemma of_complex_mult [simp]: "of_complex (x * y) = of_complex x * of_complex y"
  by (simp add: of_complex_def mult.commute)

lemma of_complex_sum[simp]: "of_complex (sum f s) = (\<Sum>x\<in>s. of_complex (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma of_complex_prod[simp]: "of_complex (prod f s) = (\<Prod>x\<in>s. of_complex (f x))"
  by (induct s rule: infinite_finite_induct) auto

lemma nonzero_of_complex_inverse:
  "x \<noteq> 0 \<Longrightarrow> of_complex (inverse x) = inverse (of_complex x :: 'a::complex_div_algebra)"
  by (simp add: of_complex_def nonzero_inverse_scaleC_distrib)

lemma of_complex_inverse [simp]:
  "of_complex (inverse x) = inverse (of_complex x :: 'a::{complex_div_algebra,division_ring})"
  by (simp add: of_complex_def inverse_scaleC_distrib)

lemma nonzero_of_complex_divide:
  "y \<noteq> 0 \<Longrightarrow> of_complex (x / y) = (of_complex x / of_complex y :: 'a::complex_field)"
  by (simp add: divide_inverse nonzero_of_complex_inverse)

lemma of_complex_divide [simp]:
  "of_complex (x / y) = (of_complex x / of_complex y :: 'a::complex_div_algebra)"
  by (simp add: divide_inverse)

lemma of_complex_power [simp]:
  "of_complex (x ^ n) = (of_complex x :: 'a::{complex_algebra_1}) ^ n"
  by (induct n) simp_all

lemma of_complex_power_int [simp]:
  "of_complex (power_int x n) = power_int (of_complex x :: 'a :: {complex_div_algebra,division_ring}) n"
  by (auto simp: power_int_def)

lemma of_complex_eq_iff [simp]: "of_complex x = of_complex y \<longleftrightarrow> x = y"
  by (simp add: of_complex_def)

lemma inj_of_complex: "inj of_complex"
  by (auto intro: injI)

lemmas of_complex_eq_0_iff [simp] = of_complex_eq_iff [of _ 0, simplified]
lemmas of_complex_eq_1_iff [simp] = of_complex_eq_iff [of _ 1, simplified]

lemma minus_of_complex_eq_of_complex_iff [simp]: "-of_complex x = of_complex y \<longleftrightarrow> -x = y"
  using of_complex_eq_iff[of "-x" y] by (simp only: of_complex_minus)

lemma of_complex_eq_minus_of_complex_iff [simp]: "of_complex x = -of_complex y \<longleftrightarrow> x = -y"
  using of_complex_eq_iff[of x "-y"] by (simp only: of_complex_minus)

lemma of_complex_eq_id [simp]: "of_complex = (id :: complex \<Rightarrow> complex)"
  by (rule ext) (simp add: of_complex_def)

text \<open>Collapse nested embeddings.\<close>
lemma of_complex_of_nat_eq [simp]: "of_complex (of_nat n) = of_nat n"
  by (induct n) auto

lemma of_complex_of_int_eq [simp]: "of_complex (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) simp

lemma of_complex_numeral [simp]: "of_complex (numeral w) = numeral w"
  using of_complex_of_int_eq [of "numeral w"] by simp

lemma of_complex_neg_numeral [simp]: "of_complex (- numeral w) = - numeral w"
  using of_complex_of_int_eq [of "- numeral w"] by simp

lemma numeral_power_int_eq_of_complex_cancel_iff [simp]:
  "power_int (numeral x) n = (of_complex y :: 'a :: {complex_div_algebra, division_ring}) \<longleftrightarrow>
     power_int (numeral x) n = y"
proof -
  have "power_int (numeral x) n = (of_complex (power_int (numeral x) n) :: 'a)"
    by simp
  also have "\<dots> = of_complex y \<longleftrightarrow> power_int (numeral x) n = y"
    by (subst of_complex_eq_iff) auto
  finally show ?thesis .
qed

lemma of_complex_eq_numeral_power_int_cancel_iff [simp]:
  "(of_complex y :: 'a :: {complex_div_algebra, division_ring}) = power_int (numeral x) n \<longleftrightarrow>
     y = power_int (numeral x) n"
  by (subst (1 2) eq_commute) simp

lemma of_complex_eq_of_complex_power_int_cancel_iff [simp]:
  "power_int (of_complex b :: 'a :: {complex_div_algebra, division_ring}) w = of_complex x \<longleftrightarrow>
     power_int b w = x"
  by (metis of_complex_power_int of_complex_eq_iff)

term real_of_int
lemma of_complex_in_Ints_iff [simp]: "of_complex x \<in> \<int> \<longleftrightarrow> x \<in> \<int>"
proof safe
  fix x assume "(of_complex x :: 'a) \<in> \<int>"
  then obtain n where "(of_complex x :: 'a) = of_int n"
    by (auto simp: Ints_def)
  also have "of_int n = of_complex (of_int n)"
    by simp
  finally have "x = of_int n"
    by (subst (asm) of_complex_eq_iff)
  thus "x \<in> \<int>"
    by auto
qed (auto simp: Ints_def)

lemma Ints_of_complex [intro]: "x \<in> \<int> \<Longrightarrow> of_complex x \<in> \<int>"
  by simp


text \<open>Every complex algebra has characteristic zero.\<close>
instance complex_algebra_1 < ring_char_0
proof
  from inj_of_complex inj_of_nat have "inj (of_complex \<circ> of_nat)"
    by (rule inj_compose)
  then show "inj (of_nat :: nat \<Rightarrow> 'a)"
    by (simp add: comp_def)
qed

lemma fraction_scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(numeral u / numeral v) *\<^sub>C (numeral w * a) = (numeral u * numeral w / numeral v) *\<^sub>C a"
  by (metis (no_types, lifting) of_complex_numeral scaleC_conv_of_complex scaleC_scaleC times_divide_eq_left)

lemma inverse_scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(1 / numeral v) *\<^sub>C (numeral w * a) = (numeral w / numeral v) *\<^sub>C a"
  by (metis divide_inverse_commute inverse_eq_divide of_complex_numeral scaleC_conv_of_complex scaleC_scaleC)

lemma scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(numeral u) *\<^sub>C (numeral w * a) = (numeral u * numeral w) *\<^sub>C a"
  by (simp add: scaleC_conv_of_complex)

instance complex_field < field_char_0 ..


subsection \<open>The Set of Real Numbers\<close>

definition Complexs :: "'a::complex_algebra_1 set"  ("\<complex>")
  where "\<complex> = range of_complex"

lemma Complexs_of_complex [simp]: "of_complex r \<in> \<complex>"
  by (simp add: Complexs_def)

lemma Complexs_of_int [simp]: "of_int z \<in> \<complex>"
  by (subst of_complex_of_int_eq [symmetric], rule Complexs_of_complex)

lemma Complexs_of_nat [simp]: "of_nat n \<in> \<complex>"
  by (subst of_complex_of_nat_eq [symmetric], rule Complexs_of_complex)

lemma Complexs_numeral [simp]: "numeral w \<in> \<complex>"
  by (subst of_complex_numeral [symmetric], rule Complexs_of_complex)

lemma Complexs_0 [simp]: "0 \<in> \<complex>" and Complexs_1 [simp]: "1 \<in> \<complex>"
  by (simp_all add: Complexs_def)

lemma Complexs_add [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a + b \<in> \<complex>"
  apply (auto simp add: Complexs_def)
    by (metis of_complex_add range_eqI) 

lemma Complexs_minus [simp]: "a \<in> \<complex> \<Longrightarrow> - a \<in> \<complex>"
  by (auto simp: Complexs_def)

lemma Complexs_minus_iff [simp]: "- a \<in> \<complex> \<longleftrightarrow> a \<in> \<complex>"
  using Complexs_minus by fastforce

lemma Complexs_diff [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a - b \<in> \<complex>"
  by (metis Complexs_add Complexs_minus_iff add_uminus_conv_diff)

lemma Complexs_mult [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a * b \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  by (metis of_complex_mult rangeI)

lemma nonzero_Complexs_inverse: "a \<in> \<complex> \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> inverse a \<in> \<complex>"
  for a :: "'a::complex_div_algebra"
  apply (auto simp add: Complexs_def)
  by (metis of_complex_inverse range_eqI) 

lemma Complexs_inverse: "a \<in> \<complex> \<Longrightarrow> inverse a \<in> \<complex>"
  for a :: "'a::{complex_div_algebra,division_ring}"
  using nonzero_Complexs_inverse by fastforce

lemma Complexs_inverse_iff [simp]: "inverse x \<in> \<complex> \<longleftrightarrow> x \<in> \<complex>"
  for x :: "'a::{complex_div_algebra,division_ring}"
  by (metis Complexs_inverse inverse_inverse_eq)

lemma nonzero_Complexs_divide: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a / b \<in> \<complex>"
  for a b :: "'a::complex_field"
  by (simp add: divide_inverse)

lemma Complexs_divide [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a / b \<in> \<complex>"
  for a b :: "'a::{complex_field,field}"
  using nonzero_Complexs_divide by fastforce

lemma Complexs_power [simp]: "a \<in> \<complex> \<Longrightarrow> a ^ n \<in> \<complex>"
  for a :: "'a::complex_algebra_1"
  apply (auto simp add: Complexs_def)
  by (metis range_eqI of_complex_power[symmetric])

lemma Complexs_cases [cases set: Complexs]:
  assumes "q \<in> \<complex>"
  obtains (of_complex) c where "q = of_complex c"
  unfolding Complexs_def
proof -
  from \<open>q \<in> \<complex>\<close> have "q \<in> range of_complex" unfolding Complexs_def .
  then obtain c where "q = of_complex c" ..
  then show thesis ..
qed

lemma sum_in_Complexs [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<complex>) \<Longrightarrow> sum f s \<in> \<complex>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  then show ?case by (metis Complexs_0 sum.infinite)
qed simp_all

lemma prod_in_Complexs [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<complex>) \<Longrightarrow> prod f s \<in> \<complex>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  then show ?case by (metis Complexs_1 prod.infinite)
qed simp_all

lemma Complexs_induct [case_names of_complex, induct set: Complexs]:
  "q \<in> \<complex> \<Longrightarrow> (\<And>r. P (of_complex r)) \<Longrightarrow> P q"
  by (rule Complexs_cases) auto



subsection \<open>Ordered complex vector spaces\<close>

class ordered_complex_vector = complex_vector + ordered_ab_group_add +
  assumes scaleC_left_mono: "x \<le> y \<Longrightarrow> 0 \<le> a \<Longrightarrow> a *\<^sub>C x \<le> a *\<^sub>C y"
    and scaleC_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> b *\<^sub>C x"
begin

lemma scaleC_mono:
  "a \<le> b \<Longrightarrow> x \<le> y \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> b *\<^sub>C y"
  by (meson order_trans scaleC_left_mono scaleC_right_mono)
  
lemma scaleC_mono':
  "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> a *\<^sub>C c \<le> b *\<^sub>C d"
  by (rule scaleC_mono) (auto intro: order.trans)

lemma pos_le_divideR_eq [field_simps]:
  "a \<le> b /\<^sub>C c \<longleftrightarrow> c *\<^sub>C a \<le> b" (is "?P \<longleftrightarrow> ?Q") if "0 < c"
proof
  assume ?P
  with scaleC_left_mono that have "c *\<^sub>C a \<le> c *\<^sub>C (b /\<^sub>C c)"
    using preorder_class.less_imp_le by blast
  with that show ?Q
    by auto
next
  assume ?Q
  with scaleC_left_mono that have "c *\<^sub>C a /\<^sub>C c \<le> b /\<^sub>C c"
    using less_complex_def less_eq_complex_def by fastforce
  with that show ?P
    by auto
qed

lemma pos_less_divideR_eq [field_simps]:
  "a < b /\<^sub>C c \<longleftrightarrow> c *\<^sub>C a < b" if "c > 0"
  using that pos_le_divideR_eq [of c a b]
  by (auto simp add: le_less)

lemma pos_divideR_le_eq [field_simps]:
  "b /\<^sub>C c \<le> a \<longleftrightarrow> b \<le> c *\<^sub>C a" if "c > 0"
  using that pos_le_divideR_eq [of "inverse c" b a]
    less_complex_def by auto

lemma pos_divideR_less_eq [field_simps]:
  "b /\<^sub>C c < a \<longleftrightarrow> b < c *\<^sub>C a" if "c > 0"
  using that pos_less_divideR_eq [of "inverse c" b a]
  by (simp add: local.less_le_not_le local.pos_divideR_le_eq local.pos_le_divideR_eq)

lemma pos_le_minus_divideR_eq [field_simps]:
  "a \<le> - (b /\<^sub>C c) \<longleftrightarrow> c *\<^sub>C a \<le> - b" if "c > 0"
  using that
  by (metis left_inverse local.ab_left_minus local.add.inverse_unique local.add.right_inverse local.add_minus_cancel local.le_minus_iff local.pos_divideR_le_eq local.scaleC_add_right local.scaleC_one local.scaleC_scaleC order_class.antisym_conv2 preorder_class.less_imp_le)
  
lemma pos_less_minus_divideR_eq [field_simps]:
  "a < - (b /\<^sub>C c) \<longleftrightarrow> c *\<^sub>C a < - b" if "c > 0"
  using that by (metis le_less less_le_not_le pos_divideR_le_eq
    pos_divideR_less_eq pos_le_minus_divideR_eq)

lemma pos_minus_divideR_le_eq [field_simps]:
  "- (b /\<^sub>C c) \<le> a \<longleftrightarrow> - b \<le> c *\<^sub>C a" if "c > 0"
  using that
  by (metis local.add_minus_cancel local.left_minus local.pos_divideR_le_eq local.scaleC_add_right)

lemma pos_minus_divideR_less_eq [field_simps]:
  "- (b /\<^sub>C c) < a \<longleftrightarrow> - b < c *\<^sub>C a" if "c > 0"
  using that by (simp add: less_le_not_le pos_le_minus_divideR_eq pos_minus_divideR_le_eq) 

lemma scaleC_image_atLeastAtMost: "c > 0 \<Longrightarrow> scaleC c ` {x..y} = {c *\<^sub>C x..c *\<^sub>C y}"
  apply (auto intro!: scaleC_left_mono simp: image_iff Bex_def)
  by (meson local.eq_iff pos_divideR_le_eq pos_le_divideR_eq)

end (* class ordered_complex_vector *)

lemma neg_le_divideR_eq [field_simps]:
  "a \<le> b /\<^sub>C c \<longleftrightarrow> b \<le> c *\<^sub>C a" (is "?P \<longleftrightarrow> ?Q") if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that pos_le_divideR_eq [of "- c" a "- b"]
  by (simp add: less_complex_def scaleC_scaleC)

lemma neg_less_divideR_eq [field_simps]:
  "a < b /\<^sub>C c \<longleftrightarrow> b < c *\<^sub>C a" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that neg_le_divideR_eq [of c a b]
  by (smt (verit, ccfv_SIG) Complex_Vector_Spaces0.neg_le_divideR_eq antisym_conv2 complex_vector.scale_minus_right dual_order.strict_implies_order le_less_trans neg_le_iff_le scaleC_scaleC)

lemma neg_divideR_le_eq [field_simps]:
  "b /\<^sub>C c \<le> a \<longleftrightarrow> c *\<^sub>C a \<le> b" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that pos_divideR_le_eq [of "- c" "- b" a]
  by (simp add: less_complex_def scaleC_scaleC)

lemma neg_divideR_less_eq [field_simps]:
  "b /\<^sub>C c < a \<longleftrightarrow> c *\<^sub>C a < b" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that neg_divideR_le_eq [of c b a]
  by (meson Complex_Vector_Spaces0.neg_le_divideR_eq less_le_not_le)

lemma neg_le_minus_divideR_eq [field_simps]:
  "a \<le> - (b /\<^sub>C c) \<longleftrightarrow> - b \<le> c *\<^sub>C a" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that pos_le_minus_divideR_eq [of "- c" a "- b"]
  by (metis Complex_Vector_Spaces0.neg_le_divideR_eq complex_vector.scale_minus_right scaleC_scaleC)
  
lemma neg_less_minus_divideR_eq [field_simps]:
  "a < - (b /\<^sub>C c) \<longleftrightarrow> - b < c *\<^sub>C a" if "c < 0"
   for a b :: "'a :: ordered_complex_vector"
proof -
  have *: "- b = c *\<^sub>C a \<longleftrightarrow> b = - (c *\<^sub>C a)"
    by (metis add.inverse_inverse)
  from that neg_le_minus_divideR_eq [of c a b]
  show ?thesis by (auto simp add: le_less *)
qed

lemma neg_minus_divideR_le_eq [field_simps]:
  "- (b /\<^sub>C c) \<le> a \<longleftrightarrow> c *\<^sub>C a \<le> - b" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that pos_minus_divideR_le_eq [of "- c" "- b" a]
  by (metis Complex_Vector_Spaces0.neg_divideR_le_eq complex_vector.scale_minus_right)

lemma neg_minus_divideR_less_eq [field_simps]:
  "- (b /\<^sub>C c) < a \<longleftrightarrow> c *\<^sub>C a < - b" if "c < 0"
    for a b :: "'a :: ordered_complex_vector"
  using that by (simp add: less_le_not_le neg_le_minus_divideR_eq neg_minus_divideR_le_eq)

lemma [field_split_simps]:
  "a = b /\<^sub>C c \<longleftrightarrow> (if c = 0 then a = 0 else c *\<^sub>C a = b)"
  "b /\<^sub>C c = a \<longleftrightarrow> (if c = 0 then a = 0 else b = c *\<^sub>C a)"
  "a + b /\<^sub>C c = (if c = 0 then a else (c *\<^sub>C a + b) /\<^sub>C c)"
  "a /\<^sub>C c + b = (if c = 0 then b else (a + c *\<^sub>C b) /\<^sub>C c)"
  "a - b /\<^sub>C c = (if c = 0 then a else (c *\<^sub>C a - b) /\<^sub>C c)"
  "a /\<^sub>C c - b = (if c = 0 then - b else (a - c *\<^sub>C b) /\<^sub>C c)"
  "- (a /\<^sub>C c) + b = (if c = 0 then b else (- a + c *\<^sub>C b) /\<^sub>C c)"
  "- (a /\<^sub>C c) - b = (if c = 0 then - b else (- a - c *\<^sub>C b) /\<^sub>C c)"
    for a b :: "'a :: complex_vector"
  by (auto simp add: field_simps)

lemma [field_split_simps]:
  "0 < c \<Longrightarrow> a \<le> b /\<^sub>C c \<longleftrightarrow> (if c > 0 then c *\<^sub>C a \<le> b else if c < 0 then b \<le> c *\<^sub>C a else a \<le> 0)"
  "0 < c \<Longrightarrow> a < b /\<^sub>C c \<longleftrightarrow> (if c > 0 then c *\<^sub>C a < b else if c < 0 then b < c *\<^sub>C a else a < 0)"
  "0 < c \<Longrightarrow> b /\<^sub>C c \<le> a \<longleftrightarrow> (if c > 0 then b \<le> c *\<^sub>C a else if c < 0 then c *\<^sub>C a \<le> b else a \<ge> 0)"
  "0 < c \<Longrightarrow> b /\<^sub>C c < a \<longleftrightarrow> (if c > 0 then b < c *\<^sub>C a else if c < 0 then c *\<^sub>C a < b else a > 0)"
  "0 < c \<Longrightarrow> a \<le> - (b /\<^sub>C c) \<longleftrightarrow> (if c > 0 then c *\<^sub>C a \<le> - b else if c < 0 then - b \<le> c *\<^sub>C a else a \<le> 0)"
  "0 < c \<Longrightarrow> a < - (b /\<^sub>C c) \<longleftrightarrow> (if c > 0 then c *\<^sub>C a < - b else if c < 0 then - b < c *\<^sub>C a else a < 0)"
  "0 < c \<Longrightarrow> - (b /\<^sub>C c) \<le> a \<longleftrightarrow> (if c > 0 then - b \<le> c *\<^sub>C a else if c < 0 then c *\<^sub>C a \<le> - b else a \<ge> 0)"
  "0 < c \<Longrightarrow> - (b /\<^sub>C c) < a \<longleftrightarrow> (if c > 0 then - b < c *\<^sub>C a else if c < 0 then c *\<^sub>C a < - b else a > 0)"
  for a b :: "'a :: ordered_complex_vector"
  by (clarsimp intro!: field_simps)+

lemma scaleC_nonneg_nonneg: "0 \<le> a \<Longrightarrow> 0 \<le> x \<Longrightarrow> 0 \<le> a *\<^sub>C x"
  for x :: "'a::ordered_complex_vector"
  using scaleC_left_mono [of 0 x a] by simp

lemma scaleC_nonneg_nonpos: "0 \<le> a \<Longrightarrow> x \<le> 0 \<Longrightarrow> a *\<^sub>C x \<le> 0"
  for x :: "'a::ordered_complex_vector"
  using scaleC_left_mono [of x 0 a] by simp

lemma scaleC_nonpos_nonneg: "a \<le> 0 \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> 0"
  for x :: "'a::ordered_complex_vector"
  using scaleC_right_mono [of a 0 x] by simp

lemma split_scaleC_neg_le: "(0 \<le> a \<and> x \<le> 0) \<or> (a \<le> 0 \<and> 0 \<le> x) \<Longrightarrow> a *\<^sub>C x \<le> 0"
  for x :: "'a::ordered_complex_vector"
  by (auto simp: scaleC_nonneg_nonpos scaleC_nonpos_nonneg)

lemma le_add_iff1: "a *\<^sub>C e + c \<le> b *\<^sub>C e + d \<longleftrightarrow> (a - b) *\<^sub>C e + c \<le> d"
  for c d e :: "'a::ordered_complex_vector"
  by (simp add: algebra_simps)

lemma le_add_iff2: "a *\<^sub>C e + c \<le> b *\<^sub>C e + d \<longleftrightarrow> c \<le> (b - a) *\<^sub>C e + d"
  for c d e :: "'a::ordered_complex_vector"
  by (simp add: algebra_simps)

lemma scaleC_left_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b"
  for a b :: "'a::ordered_complex_vector"
  by (drule scaleC_left_mono [of _ _ "- c"], simp_all add: less_eq_complex_def)

lemma scaleC_right_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> a *\<^sub>C c \<le> b *\<^sub>C c"
  for c :: "'a::ordered_complex_vector"
  by (drule scaleC_right_mono [of _ _ "- c"], simp_all)

lemma scaleC_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> 0 \<le> a *\<^sub>C b"
  for b :: "'a::ordered_complex_vector"
  using scaleC_right_mono_neg [of a 0 b] by simp

lemma split_scaleC_pos_le: "(0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0) \<Longrightarrow> 0 \<le> a *\<^sub>C b"
  for b :: "'a::ordered_complex_vector"
  by (auto simp: scaleC_nonneg_nonneg scaleC_nonpos_nonpos)

lemma zero_le_scaleC_iff:
  fixes b :: "'a::ordered_complex_vector"
  assumes "a \<in> \<real>" (* Not present in Real_Vector_Spaces.thy *)
  shows "0 \<le> a *\<^sub>C b \<longleftrightarrow> 0 < a \<and> 0 \<le> b \<or> a < 0 \<and> b \<le> 0 \<or> a = 0"
    (is "?lhs = ?rhs")
proof (cases "a = 0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof
    assume ?lhs
    from \<open>a \<noteq> 0\<close> consider "a > 0" | "a < 0"
      by (metis assms complex_is_Real_iff less_complex_def less_eq_complex_def not_le order.not_eq_order_implies_strict that(1) zero_complex.sel(2))
    then show ?rhs
    proof cases
      case 1
      with \<open>?lhs\<close> have "inverse a *\<^sub>C 0 \<le> inverse a *\<^sub>C (a *\<^sub>C b)"
        by (metis complex_vector.scale_zero_right ordered_complex_vector_class.pos_le_divideR_eq)
      with 1 show ?thesis
        by simp
    next
      case 2
      with \<open>?lhs\<close> have "- inverse a *\<^sub>C 0 \<le> - inverse a *\<^sub>C (a *\<^sub>C b)"
        by (metis Complex_Vector_Spaces0.neg_le_minus_divideR_eq complex_vector.scale_zero_right neg_le_0_iff_le scaleC_left.minus)
      with 2 show ?thesis
        by simp
    qed
  next
    assume ?rhs
    then show ?lhs
      using less_imp_le split_scaleC_pos_le by auto
  qed
qed

lemma scaleC_le_0_iff:
  "a *\<^sub>C b \<le> 0 \<longleftrightarrow> 0 < a \<and> b \<le> 0 \<or> a < 0 \<and> 0 \<le> b \<or> a = 0"
  if "a \<in> \<real>" (* Not present in Real_Vector_Spaces *)
  for b::"'a::ordered_complex_vector"
  apply (insert zero_le_scaleC_iff [of "-a" b])
  using less_complex_def that by force
  

lemma scaleC_le_cancel_left: "c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  if "c \<in> \<real>" (* Not present in Real_Vector_Spaces *)
  for b :: "'a::ordered_complex_vector"
  by (smt (verit, ccfv_threshold) Complex_Vector_Spaces0.neg_divideR_le_eq complex_vector.scale_cancel_left complex_vector.scale_zero_right dual_order.eq_iff dual_order.trans ordered_complex_vector_class.pos_le_divideR_eq that zero_le_scaleC_iff)

lemma scaleC_le_cancel_left_pos: "0 < c \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> a \<le> b"
  for b :: "'a::ordered_complex_vector"
  by (simp add: complex_is_Real_iff less_complex_def scaleC_le_cancel_left)

lemma scaleC_le_cancel_left_neg: "c < 0 \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> b \<le> a"
  for b :: "'a::ordered_complex_vector"
  by (simp add: complex_is_Real_iff less_complex_def scaleC_le_cancel_left)

lemma scaleC_left_le_one_le: "0 \<le> x \<Longrightarrow> a \<le> 1 \<Longrightarrow> a *\<^sub>C x \<le> x"
  for x :: "'a::ordered_complex_vector" and a :: complex
  using scaleC_right_mono[of a 1 x] by simp

subsection \<open>Complex normed vector spaces\<close>

(* Classes dist, norm, sgn_div_norm, dist_norm, uniformity_dist
   defined in Real_Vector_Spaces are unchanged in the complex setting.
   No need to define them here. *)

class complex_normed_vector = complex_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  real_normed_vector + (* Not present in Real_Normed_Vector *)
  assumes norm_scaleC [simp]: "norm (scaleC a x) = cmod a * norm x"
begin
(* lemma norm_ge_zero [simp]: "0 \<le> norm x" *) (* Not needed, included from real_normed_vector *)
end

class complex_normed_algebra = complex_algebra + complex_normed_vector +
  real_normed_algebra (* Not present in Real_Normed_Vector *)
  (* assumes norm_mult_ineq: "norm (x * y) \<le> norm x * norm y" *) (* Not needed, included from real_normed_algebra *)

class complex_normed_algebra_1 = complex_algebra_1 + complex_normed_algebra +
  real_normed_algebra_1 (* Not present in Real_Normed_Vector *)
  (* assumes norm_one [simp]: "norm 1 = 1" *) (* Not needed, included from real_normed_algebra_1 *)

lemma (in complex_normed_algebra_1) scaleC_power [simp]: "(scaleC x y) ^ n = scaleC (x^n) (y^n)"
  by (induct n) (simp_all add: scaleC_one scaleC_scaleC mult_ac)

class complex_normed_div_algebra = complex_div_algebra + complex_normed_vector +
  real_normed_div_algebra (* Not present in Real_Normed_Vector *)
  (* assumes norm_mult: "norm (x * y) = norm x * norm y" *) (* Not needed, included from complex_normed_div_algebra *)

class complex_normed_field = complex_field + complex_normed_div_algebra +
  real_normed_field (* Not present in Real_Normed_Vector *)

instance complex_normed_div_algebra < complex_normed_algebra_1 ..

context complex_normed_vector begin
(* Inherited from _normed_vector:
lemma norm_zero [simp]: "norm (0::'a) = 0"
lemma zero_less_norm_iff [simp]: "norm x > 0 \<longleftrightarrow> x \<noteq> 0"
lemma norm_not_less_zero [simp]: "\<not> norm x < 0"
lemma norm_le_zero_iff [simp]: "norm x \<le> 0 \<longleftrightarrow> x = 0"
lemma norm_minus_cancel [simp]: "norm (- x) = norm x"
lemma norm_minus_commute: "norm (a - b) = norm (b - a)"
lemma dist_add_cancel [simp]: "dist (a + b) (a + c) = dist b c"
lemma dist_add_cancel2 [simp]: "dist (b + a) (c + a) = dist b c"
lemma norm_uminus_minus: "norm (- x - y) = norm (x + y)"
lemma norm_triangle_ineq2: "norm a - norm b \<le> norm (a - b)"
lemma norm_triangle_ineq3: "\<bar>norm a - norm b\<bar> \<le> norm (a - b)"
lemma norm_triangle_ineq4: "norm (a - b) \<le> norm a + norm b"
lemma norm_triangle_le_diff: "norm x + norm y \<le> e \<Longrightarrow> norm (x - y) \<le> e"
lemma norm_diff_ineq: "norm a - norm b \<le> norm (a + b)"
lemma norm_triangle_sub: "norm x \<le> norm y + norm (x - y)"
lemma norm_triangle_le: "norm x + norm y \<le> e \<Longrightarrow> norm (x + y) \<le> e"
lemma norm_triangle_lt: "norm x + norm y < e \<Longrightarrow> norm (x + y) < e"
lemma norm_add_leD: "norm (a + b) \<le> c \<Longrightarrow> norm b \<le> norm a + c"
lemma norm_diff_triangle_ineq: "norm ((a + b) - (c + d)) \<le> norm (a - c) + norm (b - d)"
lemma norm_diff_triangle_le: "norm (x - z) \<le> e1 + e2"
  if "norm (x - y) \<le> e1"  "norm (y - z) \<le> e2"
lemma norm_diff_triangle_less: "norm (x - z) < e1 + e2"
  if "norm (x - y) < e1"  "norm (y - z) < e2"
lemma norm_triangle_mono:
  "norm a \<le> r \<Longrightarrow> norm b \<le> s \<Longrightarrow> norm (a + b) \<le> r + s"
lemma norm_sum: "norm (sum f A) \<le> (\<Sum>i\<in>A. norm (f i))"
  for f::"'b \<Rightarrow> 'a"
lemma sum_norm_le: "norm (sum f S) \<le> sum g S"
  if "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> g x"
  for f::"'b \<Rightarrow> 'a"
lemma abs_norm_cancel [simp]: "\<bar>norm a\<bar> = norm a"
lemma sum_norm_bound:
  "norm (sum f S) \<le> of_nat (card S)*K"
  if "\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> K"
  for f :: "'b \<Rightarrow> 'a"
lemma norm_add_less: "norm x < r \<Longrightarrow> norm y < s \<Longrightarrow> norm (x + y) < r + s"
*)
end

lemma dist_scaleC [simp]: "dist (x *\<^sub>C a) (y *\<^sub>C a) = \<bar>x - y\<bar> * norm a"
  for a :: "'a::complex_normed_vector"
  by (metis dist_scaleR scaleR_scaleC)

(* Inherited from _normed_vector *)
(* lemma norm_mult_less: "norm x < r \<Longrightarrow> norm y < s \<Longrightarrow> norm (x * y) < r * s"
  for x y :: "'a::complex_normed_algebra" *)

lemma norm_of_complex [simp]: "norm (of_complex c :: 'a::complex_normed_algebra_1) = cmod c"
  by (simp add: of_complex_def)

(* Inherited from _normed_vector:
lemma norm_numeral [simp]: "norm (numeral w::'a::complex_normed_algebra_1) = numeral w"
lemma norm_neg_numeral [simp]: "norm (- numeral w::'a::complex_normed_algebra_1) = numeral w"
lemma norm_of_complex_add1 [simp]: "norm (of_real x + 1 :: 'a :: complex_normed_div_algebra) = \<bar>x + 1\<bar>"
lemma norm_of_complex_addn [simp]:
  "norm (of_real x + numeral b :: 'a :: complex_normed_div_algebra) = \<bar>x + numeral b\<bar>"
lemma norm_of_int [simp]: "norm (of_int z::'a::complex_normed_algebra_1) = \<bar>of_int z\<bar>"
lemma norm_of_nat [simp]: "norm (of_nat n::'a::complex_normed_algebra_1) = of_nat n"
lemma nonzero_norm_inverse: "a \<noteq> 0 \<Longrightarrow> norm (inverse a) = inverse (norm a)"
  for a :: "'a::complex_normed_div_algebra"
lemma norm_inverse: "norm (inverse a) = inverse (norm a)"
  for a :: "'a::{complex_normed_div_algebra,division_ring}"
lemma nonzero_norm_divide: "b \<noteq> 0 \<Longrightarrow> norm (a / b) = norm a / norm b"
  for a b :: "'a::complex_normed_field"
lemma norm_divide: "norm (a / b) = norm a / norm b"
  for a b :: "'a::{complex_normed_field,field}"
lemma norm_inverse_le_norm:
  fixes x :: "'a::complex_normed_div_algebra"
  shows "r \<le> norm x \<Longrightarrow> 0 < r \<Longrightarrow> norm (inverse x) \<le> inverse r"
lemma norm_power_ineq: "norm (x ^ n) \<le> norm x ^ n"
  for x :: "'a::complex_normed_algebra_1"
*)

lemma norm_power: "norm (x ^ n) = norm x ^ n"
  for x :: "'a::complex_normed_div_algebra"
  by (induct n) (simp_all add: norm_mult)

lemma norm_power_int: "norm (power_int x n) = power_int (norm x) n"
  for x :: "'a::complex_normed_div_algebra"
  by (cases n rule: int_cases4) (auto simp: norm_power power_int_minus norm_inverse)

lemma power_eq_imp_eq_norm:
  fixes w :: "'a::complex_normed_div_algebra"
  assumes eq: "w ^ n = z ^ n" and "n > 0"
    shows "norm w = norm z"
proof -
  have "norm w ^ n = norm z ^ n"
    by (metis (no_types) eq norm_power)
  then show ?thesis
    using assms by (force intro: power_eq_imp_eq_base)
qed

lemma power_eq_1_iff:
  fixes w :: "'a::complex_normed_div_algebra"
  shows "w ^ n = 1 \<Longrightarrow> norm w = 1 \<or> n = 0"
  by (metis norm_one power_0_left power_eq_0_iff power_eq_imp_eq_norm power_one)

lemma norm_mult_numeral1 [simp]: "norm (numeral w * a) = numeral w * norm a"
  for a b :: "'a::{complex_normed_field,field}"
  by (simp add: norm_mult)

lemma norm_mult_numeral2 [simp]: "norm (a * numeral w) = norm a * numeral w"
  for a b :: "'a::{complex_normed_field,field}"
  by (simp add: norm_mult)

lemma norm_divide_numeral [simp]: "norm (a / numeral w) = norm a / numeral w"
  for a b :: "'a::{complex_normed_field,field}"
  by (simp add: norm_divide)

lemma norm_of_complex_diff [simp]:
  "norm (of_real b - of_real a :: 'a::complex_normed_algebra_1) \<le> \<bar>b - a\<bar>"
  by (metis norm_of_real of_complex_diff order_refl)

text \<open>Despite a superficial resemblance, \<open>norm_eq_1\<close> is not relevant.\<close>
lemma square_norm_one:
  fixes x :: "'a::complex_normed_div_algebra"
  assumes "x\<^sup>2 = 1"
  shows "norm x = 1"
  by (metis assms norm_minus_cancel norm_one power2_eq_1_iff)

lemma norm_less_p1: "norm x < norm (of_real (norm x) + 1 :: 'a)"
  for x :: "'a::complex_normed_algebra_1"
proof -
  have "norm x < norm (of_real (norm x + 1) :: 'a)"
    by (simp add: of_complex_def)
  then show ?thesis
    by simp
qed

lemma prod_norm: "prod (\<lambda>x. norm (f x)) A = norm (prod f A)"
  for f :: "'a \<Rightarrow> 'b::{comm_semiring_1,complex_normed_div_algebra}"
  by (induct A rule: infinite_finite_induct) (auto simp: norm_mult)

lemma norm_prod_le:
  "norm (prod f A) \<le> (\<Prod>a\<in>A. norm (f a :: 'a :: {complex_normed_algebra_1,comm_monoid_mult}))"
proof (induct A rule: infinite_finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  then have "norm (prod f (insert a A)) \<le> norm (f a) * norm (prod f A)"
    by (simp add: norm_mult_ineq)
  also have "norm (prod f A) \<le> (\<Prod>a\<in>A. norm (f a))"
    by (rule insert)
  finally show ?case
    by (simp add: insert mult_left_mono)
next
  case infinite
  then show ?case by simp
qed

lemma norm_prod_diff:
  fixes z w :: "'i \<Rightarrow> 'a::{complex_normed_algebra_1, comm_monoid_mult}"
  shows "(\<And>i. i \<in> I \<Longrightarrow> norm (z i) \<le> 1) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> norm (w i) \<le> 1) \<Longrightarrow>
    norm ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) \<le> (\<Sum>i\<in>I. norm (z i - w i))"
proof (induction I rule: infinite_finite_induct)
  case empty
  then show ?case by simp
next
  case (insert i I)
  note insert.hyps[simp]

  have "norm ((\<Prod>i\<in>insert i I. z i) - (\<Prod>i\<in>insert i I. w i)) =
    norm ((\<Prod>i\<in>I. z i) * (z i - w i) + ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) * w i)"
    (is "_ = norm (?t1 + ?t2)")
    by (auto simp: field_simps)
  also have "\<dots> \<le> norm ?t1 + norm ?t2"
    by (rule norm_triangle_ineq)
  also have "norm ?t1 \<le> norm (\<Prod>i\<in>I. z i) * norm (z i - w i)"
    by (rule norm_mult_ineq)
  also have "\<dots> \<le> (\<Prod>i\<in>I. norm (z i)) * norm(z i - w i)"
    by (rule mult_right_mono) (auto intro: norm_prod_le)
  also have "(\<Prod>i\<in>I. norm (z i)) \<le> (\<Prod>i\<in>I. 1)"
    by (intro prod_mono) (auto intro!: insert)
  also have "norm ?t2 \<le> norm ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) * norm (w i)"
    by (rule norm_mult_ineq)
  also have "norm (w i) \<le> 1"
    by (auto intro: insert)
  also have "norm ((\<Prod>i\<in>I. z i) - (\<Prod>i\<in>I. w i)) \<le> (\<Sum>i\<in>I. norm (z i - w i))"
    using insert by auto
  finally show ?case
    by (auto simp: ac_simps mult_right_mono mult_left_mono)
next
  case infinite
  then show ?case by simp
qed

lemma norm_power_diff:
  fixes z w :: "'a::{complex_normed_algebra_1, comm_monoid_mult}"
  assumes "norm z \<le> 1" "norm w \<le> 1"
  shows "norm (z^m - w^m) \<le> m * norm (z - w)"
proof -
  have "norm (z^m - w^m) = norm ((\<Prod> i < m. z) - (\<Prod> i < m. w))"
    by simp
  also have "\<dots> \<le> (\<Sum>i<m. norm (z - w))"
    by (intro norm_prod_diff) (auto simp: assms)
  also have "\<dots> = m * norm (z - w)"
    by simp
  finally show ?thesis .
qed


subsection \<open>Metric spaces\<close>

class metric_space = uniformity_dist + open_uniformity +
  assumes dist_eq_0_iff [simp]: "dist x y = 0 \<longleftrightarrow> x = y"
    and dist_triangle2: "dist x y \<le> dist x z + dist y z"
begin

lemma dist_self [simp]: "dist x x = 0"
  by simp

lemma zero_le_dist [simp]: "0 \<le> dist x y"
  using dist_triangle2 [of x x y] by simp

lemma zero_less_dist_iff: "0 < dist x y \<longleftrightarrow> x \<noteq> y"
  by (simp add: less_le)

lemma dist_not_less_zero [simp]: "\<not> dist x y < 0"
  by (simp add: not_less)

lemma dist_le_zero_iff [simp]: "dist x y \<le> 0 \<longleftrightarrow> x = y"
  by (simp add: le_less)

lemma dist_commute: "dist x y = dist y x"
proof (rule order_antisym)
  show "dist x y \<le> dist y x"
    using dist_triangle2 [of x y x] by simp
  show "dist y x \<le> dist x y"
    using dist_triangle2 [of y x y] by simp
qed

lemma dist_commute_lessI: "dist y x < e \<Longrightarrow> dist x y < e"
  by (simp add: dist_commute)

lemma dist_triangle: "dist x z \<le> dist x y + dist y z"
  using dist_triangle2 [of x z y] by (simp add: dist_commute)

lemma dist_triangle3: "dist x y \<le> dist a x + dist a y"
  using dist_triangle2 [of x y a] by (simp add: dist_commute)

lemma abs_dist_diff_le: "\<bar>dist a b - dist b c\<bar> \<le> dist a c"
  using dist_triangle3[of b c a] dist_triangle2[of a b c] by simp

lemma dist_pos_lt: "x \<noteq> y \<Longrightarrow> 0 < dist x y"
  by (simp add: zero_less_dist_iff)

lemma dist_nz: "x \<noteq> y \<longleftrightarrow> 0 < dist x y"
  by (simp add: zero_less_dist_iff)

declare dist_nz [symmetric, simp]

lemma dist_triangle_le: "dist x z + dist y z \<le> e \<Longrightarrow> dist x y \<le> e"
  by (rule order_trans [OF dist_triangle2])

lemma dist_triangle_lt: "dist x z + dist y z < e \<Longrightarrow> dist x y < e"
  by (rule le_less_trans [OF dist_triangle2])

lemma dist_triangle_less_add: "dist x1 y < e1 \<Longrightarrow> dist x2 y < e2 \<Longrightarrow> dist x1 x2 < e1 + e2"
  by (rule dist_triangle_lt [where z=y]) simp

lemma dist_triangle_half_l: "dist x1 y < e / 2 \<Longrightarrow> dist x2 y < e / 2 \<Longrightarrow> dist x1 x2 < e"
  by (rule dist_triangle_lt [where z=y]) simp

lemma dist_triangle_half_r: "dist y x1 < e / 2 \<Longrightarrow> dist y x2 < e / 2 \<Longrightarrow> dist x1 x2 < e"
  by (rule dist_triangle_half_l) (simp_all add: dist_commute)

lemma dist_triangle_third:
  assumes "dist x1 x2 < e/3" "dist x2 x3 < e/3" "dist x3 x4 < e/3"
  shows "dist x1 x4 < e"
proof -
  have "dist x1 x3 < e/3 + e/3"
    by (metis assms(1) assms(2) dist_commute dist_triangle_less_add)
  then have "dist x1 x4 < (e/3 + e/3) + e/3"
    by (metis assms(3) dist_commute dist_triangle_less_add)
  then show ?thesis
    by simp
qed
  
subclass uniform_space
proof
  fix E x
  assume "eventually E uniformity"
  then obtain e where E: "0 < e" "\<And>x y. dist x y < e \<Longrightarrow> E (x, y)"
    by (auto simp: eventually_uniformity_metric)
  then show "E (x, x)" "\<forall>\<^sub>F (x, y) in uniformity. E (y, x)"
    by (auto simp: eventually_uniformity_metric dist_commute)
  show "\<exists>D. eventually D uniformity \<and> (\<forall>x y z. D (x, y) \<longrightarrow> D (y, z) \<longrightarrow> E (x, z))"
    using E dist_triangle_half_l[where e=e]
    unfolding eventually_uniformity_metric
    by (intro exI[of _ "\<lambda>(x, y). dist x y < e / 2"] exI[of _ "e/2"] conjI)
      (auto simp: dist_commute)
qed

lemma open_dist: "open S \<longleftrightarrow> (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
  by (simp add: dist_commute open_uniformity eventually_uniformity_metric)

lemma open_ball: "open {y. dist x y < d}"
  unfolding open_dist
proof (intro ballI)
  fix y
  assume *: "y \<in> {y. dist x y < d}"
  then show "\<exists>e>0. \<forall>z. dist z y < e \<longrightarrow> z \<in> {y. dist x y < d}"
    by (auto intro!: exI[of _ "d - dist x y"] simp: field_simps dist_triangle_lt)
qed

subclass first_countable_topology
proof
  fix x
  show "\<exists>A::nat \<Rightarrow> 'a set. (\<forall>i. x \<in> A i \<and> open (A i)) \<and> (\<forall>S. open S \<and> x \<in> S \<longrightarrow> (\<exists>i. A i \<subseteq> S))"
  proof (safe intro!: exI[of _ "\<lambda>n. {y. dist x y < inverse (Suc n)}"])
    fix S
    assume "open S" "x \<in> S"
    then obtain e where e: "0 < e" and "{y. dist x y < e} \<subseteq> S"
      by (auto simp: open_dist subset_eq dist_commute)
    moreover
    from e obtain i where "inverse (Suc i) < e"
      by (auto dest!: reals_Archimedean)
    then have "{y. dist x y < inverse (Suc i)} \<subseteq> {y. dist x y < e}"
      by auto
    ultimately show "\<exists>i. {y. dist x y < inverse (Suc i)} \<subseteq> S"
      by blast
  qed (auto intro: open_ball)
qed

end

instance metric_space \<subseteq> t2_space
proof
  fix x y :: "'a::metric_space"
  assume xy: "x \<noteq> y"
  let ?U = "{y'. dist x y' < dist x y / 2}"
  let ?V = "{x'. dist y x' < dist x y / 2}"
  have *: "d x z \<le> d x y + d y z \<Longrightarrow> d y z = d z y \<Longrightarrow> \<not> (d x y * 2 < d x z \<and> d z y * 2 < d x z)"
    for d :: "'a \<Rightarrow> 'a \<Rightarrow> real" and x y z :: 'a
    by arith
  have "open ?U \<and> open ?V \<and> x \<in> ?U \<and> y \<in> ?V \<and> ?U \<inter> ?V = {}"
    using dist_pos_lt[OF xy] *[of dist, OF dist_triangle dist_commute]
    using open_ball[of _ "dist x y / 2"] by auto
  then show "\<exists>U V. open U \<and> open V \<and> x \<in> U \<and> y \<in> V \<and> U \<inter> V = {}"
    by blast
qed

text \<open>Every normed vector space is a metric space.\<close>
instance complex_normed_vector < metric_space
proof
  fix x y z :: 'a
  show "dist x y = 0 \<longleftrightarrow> x = y"
    by (simp add: dist_norm)
  show "dist x y \<le> dist x z + dist y z"
    using norm_triangle_ineq4 [of "x - z" "y - z"] by (simp add: dist_norm)
qed


subsection \<open>Class instances for real numbers\<close>

instantiation real :: complex_normed_field
begin

definition dist_complex_def: "dist x y = \<bar>x - y\<bar>"

definition uniformity_complex_def [code del]:
  "(uniformity :: (real \<times> real) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_complex_def [code del]:
  "open (U :: real set) \<longleftrightarrow> (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"

definition complex_norm_def [simp]: "norm r = \<bar>r\<bar>"

instance
  by intro_classes (auto simp: abs_mult open_complex_def dist_complex_def sgn_complex_def uniformity_complex_def)x

end

declare uniformity_Abort[where 'a=real, code]

lemma dist_of_real [simp]: "dist (of_real x :: 'a) (of_real y) = dist x y"
  for a :: "'a::complex_normed_div_algebra"
  by (metis dist_norm norm_of_real of_complex_diff complex_norm_def)x

declare [[code abort: "open :: real set \<Rightarrow> bool"]]

instance real :: linorder_topology
proof
  show "(open :: real set \<Rightarrow> bool) = generate_topology (range lessThan \<union> range greaterThan)"
  proof (rule ext, safe)
    fix S :: "real set"
    assume "open S"
    then obtain f where "\<forall>x\<in>S. 0 < f x \<and> (\<forall>y. dist y x < f x \<longrightarrow> y \<in> S)"
      unfolding open_dist bchoice_iff ..
    then have *: "(\<Union>x\<in>S. {x - f x <..} \<inter> {..< x + f x}) = S" (is "?S = S")
      by (fastforce simp: dist_complex_def)
    moreover have "generate_topology (range lessThan \<union> range greaterThan) ?S"
      by (force intro: generate_topology.Basis generate_topology_Union generate_topology.Int)
    ultimately show "generate_topology (range lessThan \<union> range greaterThan) S"
      by simp
  next
    fix S :: "real set"
    assume "generate_topology (range lessThan \<union> range greaterThan) S"
    moreover have "\<And>a::real. open {..<a}"
      unfolding open_dist dist_complex_def
    proof clarify
      fix x a :: real
      assume "x < a"
      then have "0 < a - x \<and> (\<forall>y. \<bar>y - x\<bar> < a - x \<longrightarrow> y \<in> {..<a})" by auto
      then show "\<exists>e>0. \<forall>y. \<bar>y - x\<bar> < e \<longrightarrow> y \<in> {..<a}" ..
    qed
    moreover have "\<And>a::real. open {a <..}"
      unfolding open_dist dist_complex_def
    proof clarify
      fix x a :: real
      assume "a < x"
      then have "0 < x - a \<and> (\<forall>y. \<bar>y - x\<bar> < x - a \<longrightarrow> y \<in> {a<..})" by auto
      then show "\<exists>e>0. \<forall>y. \<bar>y - x\<bar> < e \<longrightarrow> y \<in> {a<..}" ..
    qed
    ultimately show "open S"
      by induct auto
  qed
qed

instance real :: linear_continuum_topology ..

lemmas open_complex_greaterThan = open_greaterThan[where 'a=real]
lemmas open_complex_lessThan = open_lessThan[where 'a=real]
lemmas open_complex_greaterThanLessThan = open_greaterThanLessThan[where 'a=real]
lemmas closed_complex_atMost = closed_atMost[where 'a=real]
lemmas closed_complex_atLeast = closed_atLeast[where 'a=real]
lemmas closed_complex_atLeastAtMost = closed_atLeastAtMost[where 'a=real]

instance real :: ordered_complex_vector
  by standard (auto intro: mult_left_mono mult_right_mono)


subsection \<open>Extra type constraints\<close>

text \<open>Only allow \<^term>\<open>open\<close> in class \<open>topological_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>open\<close>, SOME \<^typ>\<open>'a::topological_space set \<Rightarrow> bool\<close>)\<close>

text \<open>Only allow \<^term>\<open>uniformity\<close> in class \<open>uniform_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>uniformity\<close>, SOME \<^typ>\<open>('a::uniformity \<times> 'a) filter\<close>)\<close>

text \<open>Only allow \<^term>\<open>dist\<close> in class \<open>metric_space\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>dist\<close>, SOME \<^typ>\<open>'a::metric_space \<Rightarrow> 'a \<Rightarrow> real\<close>)\<close>

text \<open>Only allow \<^term>\<open>norm\<close> in class \<open>complex_normed_vector\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::complex_normed_vector \<Rightarrow> real\<close>)\<close>


subsection \<open>Sign function\<close>

lemma norm_sgn: "norm (sgn x) = (if x = 0 then 0 else 1)"
  for x :: "'a::complex_normed_vector"
  by (simp add: sgn_div_norm)

lemma sgn_zero [simp]: "sgn (0::'a::complex_normed_vector) = 0"
  by (simp add: sgn_div_norm)

lemma sgn_zero_iff: "sgn x = 0 \<longleftrightarrow> x = 0"
  for x :: "'a::complex_normed_vector"
  by (simp add: sgn_div_norm)

lemma sgn_minus: "sgn (- x) = - sgn x"
  for x :: "'a::complex_normed_vector"
  by (simp add: sgn_div_norm)

lemma sgn_scaleC: "sgn (scaleC r x) = scaleC (sgn r) (sgn x)"
  for x :: "'a::complex_normed_vector"
  by (simp add: sgn_div_norm ac_simps)

lemma sgn_one [simp]: "sgn (1::'a::complex_normed_algebra_1) = 1"
  by (simp add: sgn_div_norm)

lemma sgn_of_real: "sgn (of_real r :: 'a::complex_normed_algebra_1) = of_real (sgn r)"
  unfolding of_complex_def by (simp only: sgn_scaleC sgn_one)

lemma sgn_mult: "sgn (x * y) = sgn x * sgn y"
  for x y :: "'a::complex_normed_div_algebra"
  by (simp add: sgn_div_norm norm_mult)

hide_fact (open) sgn_mult

lemma complex_sgn_eq: "sgn x = x / \<bar>x\<bar>"
  for x :: real
  by (simp add: sgn_div_norm divide_inverse)

lemma zero_le_sgn_iff [simp]: "0 \<le> sgn x \<longleftrightarrow> 0 \<le> x"
  for x :: real
  by (cases "0::real" x rule: linorder_cases) simp_all

lemma sgn_le_0_iff [simp]: "sgn x \<le> 0 \<longleftrightarrow> x \<le> 0"
  for x :: real
  by (cases "0::real" x rule: linorder_cases) simp_all

lemma norm_conv_dist: "norm x = dist x 0"
  unfolding dist_norm by simp

declare norm_conv_dist [symmetric, simp]

lemma dist_0_norm [simp]: "dist 0 x = norm x"
  for x :: "'a::complex_normed_vector"
  by (simp add: dist_norm)

lemma dist_diff [simp]: "dist a (a - b) = norm b"  "dist (a - b) a = norm b"
  by (simp_all add: dist_norm)

lemma dist_of_int: "dist (of_int m) (of_int n :: 'a :: complex_normed_algebra_1) = of_int \<bar>m - n\<bar>"
proof -
  have "dist (of_int m) (of_int n :: 'a) = dist (of_int m :: 'a) (of_int m - (of_int (m - n)))"
    by simp
  also have "\<dots> = of_int \<bar>m - n\<bar>" by (subst dist_diff, subst norm_of_int) simp
  finally show ?thesis .
qed

lemma dist_of_nat:
  "dist (of_nat m) (of_nat n :: 'a :: complex_normed_algebra_1) = of_int \<bar>int m - int n\<bar>"
  by (subst (1 2) of_int_of_nat_eq [symmetric]) (rule dist_of_int)


subsection \<open>Bounded Linear and Bilinear Operators\<close>

lemma linearI: "linear f"
  if "\<And>b1 b2. f (b1 + b2) = f b1 + f b2"
    "\<And>r b. f (r *\<^sub>C b) = r *\<^sub>C f b"
  using that
  by unfold_locales (auto simp: algebra_simps)

lemma linear_iff:
  "linear f \<longleftrightarrow> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (c *\<^sub>C x) = c *\<^sub>C f x)"
  (is "linear f \<longleftrightarrow> ?rhs")
proof
  assume "linear f"
  then interpret f: linear f .
  show "?rhs" by (simp add: f.add f.scale)
next
  assume "?rhs"
  then show "linear f" by (intro linearI) auto
qed

lemmas linear_scaleC_left = linear_scale_left
lemmas linear_imp_scaleC = linear_imp_scale

corollary complex_linearD:
  fixes f :: "real \<Rightarrow> real"
  assumes "linear f" obtains c where "f = (*) c"
  by (rule linear_imp_scaleC [OF assms]) (force simp: scaleC_conv_of_real)

lemma linear_times_of_real: "linear (\<lambda>x. a * of_real x)"
  by (auto intro!: linearI simp: distrib_left)
    (metis mult_scaleC_right scaleC_conv_of_real)

locale bounded_linear = linear f for f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

lemma pos_bounded: "\<exists>K>0. \<forall>x. norm (f x) \<le> norm x * K"
proof -
  obtain K where K: "\<And>x. norm (f x) \<le> norm x * K"
    using bounded by blast
  show ?thesis
  proof (intro exI impI conjI allI)
    show "0 < max 1 K"
      by (rule order_less_le_trans [OF zero_less_one max.cobounded1])
  next
    fix x
    have "norm (f x) \<le> norm x * K" using K .
    also have "\<dots> \<le> norm x * max 1 K"
      by (rule mult_left_mono [OF max.cobounded2 norm_ge_zero])
    finally show "norm (f x) \<le> norm x * max 1 K" .
  qed
qed

lemma nonneg_bounded: "\<exists>K\<ge>0. \<forall>x. norm (f x) \<le> norm x * K"
  using pos_bounded by (auto intro: order_less_imp_le)

lemma linear: "linear f"
  by (fact local.linear_axioms)

end

lemma bounded_linear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (scaleC r x) = scaleC r (f x)"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_linear f"
  by standard (blast intro: assms)+

locale bounded_bilinear =
  fixes prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
    (infixl "**" 70)
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleC_left: "prod (scaleC r a) b = scaleC r (prod a b)"
    and scaleC_right: "prod a (scaleC r b) = scaleC r (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

lemma pos_bounded: "\<exists>K>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
proof -
  obtain K where "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    using bounded by blast
  then have "norm (a ** b) \<le> norm a * norm b * (max 1 K)" for a b
    by (rule order.trans) (simp add: mult_left_mono)
  then show ?thesis
    by force
qed

lemma nonneg_bounded: "\<exists>K\<ge>0. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
  using pos_bounded by (auto intro: order_less_imp_le)

lemma additive_right: "additive (\<lambda>b. prod a b)"
  by (rule additive.intro, rule add_right)

lemma additive_left: "additive (\<lambda>a. prod a b)"
  by (rule additive.intro, rule add_left)

lemma zero_left: "prod 0 b = 0"
  by (rule additive.zero [OF additive_left])

lemma zero_right: "prod a 0 = 0"
  by (rule additive.zero [OF additive_right])

lemma minus_left: "prod (- a) b = - prod a b"
  by (rule additive.minus [OF additive_left])

lemma minus_right: "prod a (- b) = - prod a b"
  by (rule additive.minus [OF additive_right])

lemma diff_left: "prod (a - a') b = prod a b - prod a' b"
  by (rule additive.diff [OF additive_left])

lemma diff_right: "prod a (b - b') = prod a b - prod a b'"
  by (rule additive.diff [OF additive_right])

lemma sum_left: "prod (sum g S) x = sum ((\<lambda>i. prod (g i) x)) S"
  by (rule additive.sum [OF additive_left])

lemma sum_right: "prod x (sum g S) = sum ((\<lambda>i. (prod x (g i)))) S"
  by (rule additive.sum [OF additive_right])


lemma bounded_linear_left: "bounded_linear (\<lambda>a. a ** b)"
proof -
  obtain K where "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    using pos_bounded by blast
  then show ?thesis
    by (rule_tac K="norm b * K" in bounded_linear_intro) (auto simp: algebra_simps scaleC_left add_left)
qed

lemma bounded_linear_right: "bounded_linear (\<lambda>b. a ** b)"
proof -
  obtain K where "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    using pos_bounded by blast
  then show ?thesis
    by (rule_tac K="norm a * K" in bounded_linear_intro) (auto simp: algebra_simps scaleC_right add_right)
qed

lemma prod_diff_prod: "(x ** y - a ** b) = (x - a) ** (y - b) + (x - a) ** b + a ** (y - b)"
  by (simp add: diff_left diff_right)

lemma flip: "bounded_bilinear (\<lambda>x y. y ** x)"
proof
  show "\<exists>K. \<forall>a b. norm (b ** a) \<le> norm a * norm b * K"
    by (metis bounded mult.commute)
qed (simp_all add: add_right add_left scaleC_right scaleC_left)

lemma comp1:
  assumes "bounded_linear g"
  shows "bounded_bilinear (\<lambda>x. (**) (g x))"
proof unfold_locales
  interpret g: bounded_linear g by fact
  show "\<And>a a' b. g (a + a') ** b = g a ** b + g a' ** b"
    "\<And>a b b'. g a ** (b + b') = g a ** b + g a ** b'"
    "\<And>r a b. g (r *\<^sub>C a) ** b = r *\<^sub>C (g a ** b)"
    "\<And>a r b. g a ** (r *\<^sub>C b) = r *\<^sub>C (g a ** b)"
    by (auto simp: g.add add_left add_right g.scaleC scaleC_left scaleC_right)
  from g.nonneg_bounded nonneg_bounded obtain K L
    where nn: "0 \<le> K" "0 \<le> L"
      and K: "\<And>x. norm (g x) \<le> norm x * K"
      and L: "\<And>a b. norm (a ** b) \<le> norm a * norm b * L"
    by auto
  have "norm (g a ** b) \<le> norm a * K * norm b * L" for a b
    by (auto intro!:  order_trans[OF K] order_trans[OF L] mult_mono simp: nn)
  then show "\<exists>K. \<forall>a b. norm (g a ** b) \<le> norm a * norm b * K"
    by (auto intro!: exI[where x="K * L"] simp: ac_simps)
qed

lemma comp: "bounded_linear f \<Longrightarrow> bounded_linear g \<Longrightarrow> bounded_bilinear (\<lambda>x y. f x ** g y)"
  by (rule bounded_bilinear.flip[OF bounded_bilinear.comp1[OF bounded_bilinear.flip[OF comp1]]])

end

lemma bounded_linear_ident[simp]: "bounded_linear (\<lambda>x. x)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_linear_zero[simp]: "bounded_linear (\<lambda>x. 0)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_linear_add:
  assumes "bounded_linear f"
    and "bounded_linear g"
  shows "bounded_linear (\<lambda>x. f x + g x)"
proof -
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  show ?thesis
  proof
    from f.bounded obtain Kf where Kf: "norm (f x) \<le> norm x * Kf" for x
      by blast
    from g.bounded obtain Kg where Kg: "norm (g x) \<le> norm x * Kg" for x
      by blast
    show "\<exists>K. \<forall>x. norm (f x + g x) \<le> norm x * K"
      using add_mono[OF Kf Kg]
      by (intro exI[of _ "Kf + Kg"]) (auto simp: field_simps intro: norm_triangle_ineq order_trans)
  qed (simp_all add: f.add g.add f.scaleC g.scaleC scaleC_right_distrib)
qed

lemma bounded_linear_minus:
  assumes "bounded_linear f"
  shows "bounded_linear (\<lambda>x. - f x)"
proof -
  interpret f: bounded_linear f by fact
  show ?thesis
    by unfold_locales (simp_all add: f.add f.scaleC f.bounded)
qed

lemma bounded_linear_sub: "bounded_linear f \<Longrightarrow> bounded_linear g \<Longrightarrow> bounded_linear (\<lambda>x. f x - g x)"
  using bounded_linear_add[of f "\<lambda>x. - g x"] bounded_linear_minus[of g]
  by (auto simp: algebra_simps)

lemma bounded_linear_sum:
  fixes f :: "'i \<Rightarrow> 'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector"
  shows "(\<And>i. i \<in> I \<Longrightarrow> bounded_linear (f i)) \<Longrightarrow> bounded_linear (\<lambda>x. \<Sum>i\<in>I. f i x)"
  by (induct I rule: infinite_finite_induct) (auto intro!: bounded_linear_add)

lemma bounded_linear_compose:
  assumes "bounded_linear f"
    and "bounded_linear g"
  shows "bounded_linear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_linear f by fact
  interpret g: bounded_linear g by fact
  show ?thesis
  proof unfold_locales
    show "f (g (x + y)) = f (g x) + f (g y)" for x y
      by (simp only: f.add g.add)
    show "f (g (scaleC r x)) = scaleC r (f (g x))" for r x
      by (simp only: f.scaleC g.scaleC)
    from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
      by blast
    from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
      by blast
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    proof (intro exI allI)
      fix x
      have "norm (f (g x)) \<le> norm (g x) * Kf"
        using f .
      also have "\<dots> \<le> (norm x * Kg) * Kf"
        using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
      also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
        by (rule mult.assoc)
      finally show "norm (f (g x)) \<le> norm x * (Kg * Kf)" .
    qed
  qed
qed

lemma bounded_bilinear_mult: "bounded_bilinear ((*) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a::complex_normed_algebra)"
proof (rule bounded_bilinear.intro)
  show "\<exists>K. \<forall>a b::'a. norm (a * b) \<le> norm a * norm b * K"
    by (rule_tac x=1 in exI) (simp add: norm_mult_ineq)
qed (auto simp: algebra_simps)

lemma bounded_linear_mult_left: "bounded_linear (\<lambda>x::'a::complex_normed_algebra. x * y)"
  using bounded_bilinear_mult
  by (rule bounded_bilinear.bounded_linear_left)

lemma bounded_linear_mult_right: "bounded_linear (\<lambda>y::'a::complex_normed_algebra. x * y)"
  using bounded_bilinear_mult
  by (rule bounded_bilinear.bounded_linear_right)

lemmas bounded_linear_mult_const =
  bounded_linear_mult_left [THEN bounded_linear_compose]

lemmas bounded_linear_const_mult =
  bounded_linear_mult_right [THEN bounded_linear_compose]

lemma bounded_linear_divide: "bounded_linear (\<lambda>x. x / y)"
  for y :: "'a::complex_normed_field"
  unfolding divide_inverse by (rule bounded_linear_mult_left)

lemma bounded_bilinear_scaleC: "bounded_bilinear scaleC"
proof (rule bounded_bilinear.intro)
  show "\<exists>K. \<forall>a b. norm (a *\<^sub>C b) \<le> norm a * norm b * K"
    using less_eq_complex_def by auto
qed (auto simp: algebra_simps)

lemma bounded_linear_scaleC_left: "bounded_linear (\<lambda>r. scaleC r x)"
  using bounded_bilinear_scaleC
  by (rule bounded_bilinear.bounded_linear_left)

lemma bounded_linear_scaleC_right: "bounded_linear (\<lambda>x. scaleC r x)"
  using bounded_bilinear_scaleC
  by (rule bounded_bilinear.bounded_linear_right)

lemmas bounded_linear_scaleC_const =
  bounded_linear_scaleC_left[THEN bounded_linear_compose]

lemmas bounded_linear_const_scaleC =
  bounded_linear_scaleC_right[THEN bounded_linear_compose]

lemma bounded_linear_of_real: "bounded_linear (\<lambda>r. of_real r)"
  unfolding of_complex_def by (rule bounded_linear_scaleC_left)

lemma complex_bounded_linear: "bounded_linear f \<longleftrightarrow> (\<exists>c::real. f = (\<lambda>x. x * c))"
  for f :: "real \<Rightarrow> real"
proof -
  {
    fix x
    assume "bounded_linear f"
    then interpret bounded_linear f .
    from scaleC[of x 1] have "f x = x * f 1"
      by simp
  }
  then show ?thesis
    by (auto intro: exI[of _ "f 1"] bounded_linear_mult_left)
qed

instance complex_normed_algebra_1 \<subseteq> perfect_space
proof
  fix x::'a
  have "\<And>e. 0 < e \<Longrightarrow> \<exists>y. norm (y - x) < e \<and> y \<noteq> x"
    by (rule_tac x = "x + of_real (e/2)" in exI) auto
  then show "\<not> open {x}" 
    by (clarsimp simp: open_dist dist_norm)
qed


subsection \<open>Filters and Limits on Metric Space\<close>

lemma (in metric_space) nhds_metric: "nhds x = (INF e\<in>{0 <..}. principal {y. dist y x < e})"
  unfolding nhds_def
proof (safe intro!: INF_eq)
  fix S
  assume "open S" "x \<in> S"
  then obtain e where "{y. dist y x < e} \<subseteq> S" "0 < e"
    by (auto simp: open_dist subset_eq)
  then show "\<exists>e\<in>{0<..}. principal {y. dist y x < e} \<le> principal S"
    by auto
qed (auto intro!: exI[of _ "{y. dist x y < e}" for e] open_ball simp: dist_commute)

lemma (in metric_space) tendsto_iff: "(f \<longlongrightarrow> l) F \<longleftrightarrow> (\<forall>e>0. eventually (\<lambda>x. dist (f x) l < e) F)"
  unfolding nhds_metric filterlim_INF filterlim_principal by auto

lemma tendsto_dist_iff:
  "((f \<longlongrightarrow> l) F) \<longleftrightarrow> (((\<lambda>x. dist (f x) l) \<longlongrightarrow> 0) F)"
  unfolding tendsto_iff by simp

lemma (in metric_space) tendstoI [intro?]:
  "(\<And>e. 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F) \<Longrightarrow> (f \<longlongrightarrow> l) F"
  by (auto simp: tendsto_iff)

lemma (in metric_space) tendstoD: "(f \<longlongrightarrow> l) F \<Longrightarrow> 0 < e \<Longrightarrow> eventually (\<lambda>x. dist (f x) l < e) F"
  by (auto simp: tendsto_iff)

lemma (in metric_space) eventually_nhds_metric:
  "eventually P (nhds a) \<longleftrightarrow> (\<exists>d>0. \<forall>x. dist x a < d \<longrightarrow> P x)"
  unfolding nhds_metric
  by (subst eventually_INF_base)
     (auto simp: eventually_principal Bex_def subset_eq intro: exI[of _ "min a b" for a b])

lemma eventually_at: "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<and> dist x a < d \<longrightarrow> P x)"
  for a :: "'a :: metric_space"
  by (auto simp: eventually_at_filter eventually_nhds_metric)

lemma frequently_at: "frequently P (at a within S) \<longleftrightarrow> (\<forall>d>0. \<exists>x\<in>S. x \<noteq> a \<and> dist x a < d \<and> P x)"
  for a :: "'a :: metric_space"
  unfolding frequently_def eventually_at by auto

lemma eventually_at_le: "eventually P (at a within S) \<longleftrightarrow> (\<exists>d>0. \<forall>x\<in>S. x \<noteq> a \<and> dist x a \<le> d \<longrightarrow> P x)"
  for a :: "'a::metric_space"
  unfolding eventually_at_filter eventually_nhds_metric
  apply safe
  apply (rule_tac x="d / 2" in exI, auto)
  done

lemma eventually_at_left_real: "a > (b :: real) \<Longrightarrow> eventually (\<lambda>x. x \<in> {b<..<a}) (at_left a)"
  by (subst eventually_at, rule exI[of _ "a - b"]) (force simp: dist_complex_def)

lemma eventually_at_right_real: "a < (b :: real) \<Longrightarrow> eventually (\<lambda>x. x \<in> {a<..<b}) (at_right a)"
  by (subst eventually_at, rule exI[of _ "b - a"]) (force simp: dist_complex_def)

lemma metric_tendsto_imp_tendsto:
  fixes a :: "'a :: metric_space"
    and b :: "'b :: metric_space"
  assumes f: "(f \<longlongrightarrow> a) F"
    and le: "eventually (\<lambda>x. dist (g x) b \<le> dist (f x) a) F"
  shows "(g \<longlongrightarrow> b) F"
proof (rule tendstoI)
  fix e :: real
  assume "0 < e"
  with f have "eventually (\<lambda>x. dist (f x) a < e) F" by (rule tendstoD)
  with le show "eventually (\<lambda>x. dist (g x) b < e) F"
    using le_less_trans by (rule eventually_elim2)
qed

lemma filterlim_complex_sequentially: "LIM x sequentially. real x :> at_top"
proof (clarsimp simp: filterlim_at_top)
  fix Z
  show "\<forall>\<^sub>F x in sequentially. Z \<le> real x"
    by (meson eventually_sequentiallyI nat_ceiling_le_eq)
qed

lemma filterlim_nat_sequentially: "filterlim nat sequentially at_top"
proof -
  have "\<forall>\<^sub>F x in at_top. Z \<le> nat x" for Z
    by (auto intro!: eventually_at_top_linorderI[where c="int Z"])
  then show ?thesis
    unfolding filterlim_at_top ..
qed

lemma filterlim_floor_sequentially: "filterlim floor at_top at_top"
proof -
  have "\<forall>\<^sub>F x in at_top. Z \<le> \<lfloor>x\<rfloor>" for Z
    by (auto simp: le_floor_iff intro!: eventually_at_top_linorderI[where c="of_int Z"])
  then show ?thesis
    unfolding filterlim_at_top ..
qed

lemma filterlim_sequentially_iff_filterlim_real:
  "filterlim f sequentially F \<longleftrightarrow> filterlim (\<lambda>x. real (f x)) at_top F" (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    using filterlim_compose filterlim_complex_sequentially by blast
next
  assume R: ?rhs
  show ?lhs
  proof -
    have "filterlim (\<lambda>x. nat (floor (real (f x)))) sequentially F"
      by (intro filterlim_compose[OF filterlim_nat_sequentially]
          filterlim_compose[OF filterlim_floor_sequentially] R)
    then show ?thesis by simp
  qed
qed


subsubsection \<open>Limits of Sequences\<close>

lemma lim_sequentially: "X \<longlonglongrightarrow> L \<longleftrightarrow> (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n) L < r)"
  for L :: "'a::metric_space"
  unfolding tendsto_iff eventually_sequentially ..

lemmas LIMSEQ_def = lim_sequentially  (*legacy binding*)

lemma LIMSEQ_iff_nz: "X \<longlonglongrightarrow> L \<longleftrightarrow> (\<forall>r>0. \<exists>no>0. \<forall>n\<ge>no. dist (X n) L < r)"
  for L :: "'a::metric_space"
  unfolding lim_sequentially by (metis Suc_leD zero_less_Suc)x

lemma metric_LIMSEQ_I: "(\<And>r. 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r) \<Longrightarrow> X \<longlonglongrightarrow> L"
  for L :: "'a::metric_space"
  by (simp add: lim_sequentially)

lemma metric_LIMSEQ_D: "X \<longlonglongrightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>no. \<forall>n\<ge>no. dist (X n) L < r"
  for L :: "'a::metric_space"
  by (simp add: lim_sequentially)

lemma LIMSEQ_norm_0:
  assumes  "\<And>n::nat. norm (f n) < 1 / real (Suc n)"
  shows "f \<longlonglongrightarrow> 0"
proof (rule metric_LIMSEQ_I)
  fix \<epsilon> :: "real"
  assume "\<epsilon> > 0"
  then obtain N::nat where "\<epsilon> > inverse N" "N > 0"
    by (metis neq0_conv complex_arch_inverse)
  then have "norm (f n) < \<epsilon>" if "n \<ge> N" for n
  proof -
    have "1 / (Suc n) \<le> 1 / N"
      using \<open>0 < N\<close> inverse_of_nat_le le_SucI that by blast
    also have "\<dots> < \<epsilon>"
      by (metis (no_types) \<open>inverse (real N) < \<epsilon>\<close> inverse_eq_divide)
    finally show ?thesis
      by (meson assms less_eq_complex_def not_le order_trans)
  qed
  then show "\<exists>no. \<forall>n\<ge>no. dist (f n) 0 < \<epsilon>"
    by auto
qed


subsubsection \<open>Limits of Functions\<close>

lemma LIM_def: "f \<midarrow>a\<rightarrow> L \<longleftrightarrow> (\<forall>r > 0. \<exists>s > 0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r)"
  for a :: "'a::metric_space" and L :: "'b::metric_space"
  unfolding tendsto_iff eventually_at by simp

lemma metric_LIM_I:
  "(\<And>r. 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r) \<Longrightarrow> f \<midarrow>a\<rightarrow> L"
  for a :: "'a::metric_space" and L :: "'b::metric_space"
  by (simp add: LIM_def)

lemma metric_LIM_D: "f \<midarrow>a\<rightarrow> L \<Longrightarrow> 0 < r \<Longrightarrow> \<exists>s>0. \<forall>x. x \<noteq> a \<and> dist x a < s \<longrightarrow> dist (f x) L < r"
  for a :: "'a::metric_space" and L :: "'b::metric_space"
  by (simp add: LIM_def)

lemma metric_LIM_imp_LIM:
  fixes l :: "'a::metric_space"
    and m :: "'b::metric_space"
  assumes f: "f \<midarrow>a\<rightarrow> l"
    and le: "\<And>x. x \<noteq> a \<Longrightarrow> dist (g x) m \<le> dist (f x) l"
  shows "g \<midarrow>a\<rightarrow> m"
  by (rule metric_tendsto_imp_tendsto [OF f]) (auto simp: eventually_at_topological le)

lemma metric_LIM_equal2:
  fixes a :: "'a::metric_space"
  assumes "g \<midarrow>a\<rightarrow> l" "0 < R"
    and "\<And>x. x \<noteq> a \<Longrightarrow> dist x a < R \<Longrightarrow> f x = g x"
  shows "f \<midarrow>a\<rightarrow> l"
proof -
  have "\<And>S. \<lbrakk>open S; l \<in> S; \<forall>\<^sub>F x in at a. g x \<in> S\<rbrakk> \<Longrightarrow> \<forall>\<^sub>F x in at a. f x \<in> S"
    apply (simp add: eventually_at)
    by (metis assms(2) assms(3) dual_order.strict_trans linorder_neqE_linordered_idom)
  then show ?thesis
    using assms by (simp add: tendsto_def)
qed

lemma metric_LIM_compose2:
  fixes a :: "'a::metric_space"
  assumes f: "f \<midarrow>a\<rightarrow> b"
    and g: "g \<midarrow>b\<rightarrow> c"
    and inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> b"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> c"
  using inj by (intro tendsto_compose_eventually[OF g f]) (auto simp: eventually_at)

lemma metric_isCont_LIM_compose2:
  fixes f :: "'a :: metric_space \<Rightarrow> _"
  assumes f [unfolded isCont_def]: "isCont f a"
    and g: "g \<midarrow>f a\<rightarrow> l"
    and inj: "\<exists>d>0. \<forall>x. x \<noteq> a \<and> dist x a < d \<longrightarrow> f x \<noteq> f a"
  shows "(\<lambda>x. g (f x)) \<midarrow>a\<rightarrow> l"
  by (rule metric_LIM_compose2 [OF f g inj])


subsection \<open>Complete metric spaces\<close>

subsection \<open>Cauchy sequences\<close>

lemma (in metric_space) Cauchy_def: "Cauchy X = (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e)"
proof -
  have *: "eventually P (INF M. principal {(X m, X n) | n m. m \<ge> M \<and> n \<ge> M}) \<longleftrightarrow>
    (\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. P (X m, X n))" for P
    apply (subst eventually_INF_base)
    subgoal by simp
    subgoal for a b
      by (intro bexI[of _ "max a b"]) (auto simp: eventually_principal subset_eq)
    subgoal by (auto simp: eventually_principal, blast)
    done
  have "Cauchy X \<longleftrightarrow> (INF M. principal {(X m, X n) | n m. m \<ge> M \<and> n \<ge> M}) \<le> uniformity"
    unfolding Cauchy_uniform_iff le_filter_def * ..
  also have "\<dots> = (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e)"
    unfolding uniformity_dist le_INF_iff by (auto simp: * le_principal)
  finally show ?thesis .
qed

lemma (in metric_space) Cauchy_altdef: "Cauchy f \<longleftrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (f m) (f n) < e)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  show ?lhs
    unfolding Cauchy_def
  proof (intro allI impI)
    fix e :: real assume e: "e > 0"
    with \<open>?rhs\<close> obtain M where M: "m \<ge> M \<Longrightarrow> n > m \<Longrightarrow> dist (f m) (f n) < e" for m n
      by blast
    have "dist (f m) (f n) < e" if "m \<ge> M" "n \<ge> M" for m n
      using M[of m n] M[of n m] e that by (cases m n rule: linorder_cases) (auto simp: dist_commute)
    then show "\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m) (f n) < e"
      by blast
  qed
next
  assume ?lhs
  show ?rhs
  proof (intro allI impI)
    fix e :: real
    assume e: "e > 0"
    with \<open>Cauchy f\<close> obtain M where "\<And>m n. m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> dist (f m) (f n) < e"
      unfolding Cauchy_def by blast
    then show "\<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (f m) (f n) < e"
      by (intro exI[of _ M]) force
  qed
qed

lemma (in metric_space) Cauchy_altdef2: "Cauchy s \<longleftrightarrow> (\<forall>e>0. \<exists>N::nat. \<forall>n\<ge>N. dist(s n)(s N) < e)" (is "?lhs = ?rhs")
proof 
  assume "Cauchy s"
  then show ?rhs by (force simp: Cauchy_def)
next
    assume ?rhs
    {
      fix e::real
      assume "e>0"
      with \<open>?rhs\<close> obtain N where N: "\<forall>n\<ge>N. dist (s n) (s N) < e/2"
        by (erule_tac x="e/2" in allE) auto
      {
        fix n m
        assume nm: "N \<le> m \<and> N \<le> n"
        then have "dist (s m) (s n) < e" using N
          using dist_triangle_half_l[of "s m" "s N" "e" "s n"]
          by blast
      }
      then have "\<exists>N. \<forall>m n. N \<le> m \<and> N \<le> n \<longrightarrow> dist (s m) (s n) < e"
        by blast
    }
    then have ?lhs
      unfolding Cauchy_def by blast
  then show ?lhs
    by blast
qed

lemma (in metric_space) metric_CauchyI:
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X"
  by (simp add: Cauchy_def)

lemma (in metric_space) CauchyI':
  "(\<And>e. 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n>m. dist (X m) (X n) < e) \<Longrightarrow> Cauchy X"
  unfolding Cauchy_altdef by blast

lemma (in metric_space) metric_CauchyD:
  "Cauchy X \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (X m) (X n) < e"
  by (simp add: Cauchy_def)

lemma (in metric_space) metric_Cauchy_iff2:
  "Cauchy X = (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. dist (X m) (X n) < inverse(real (Suc j))))"
  apply (auto simp add: Cauchy_def)
  by (metis less_trans of_nat_Suc reals_Archimedean)

lemma Cauchy_iff2: "Cauchy X \<longleftrightarrow> (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. \<bar>X m - X n\<bar> < inverse (real (Suc j))))"
  by (simp only: metric_Cauchy_iff2 dist_complex_def)

lemma lim_1_over_n [tendsto_intros]: "((\<lambda>n. 1 / of_nat n) \<longlongrightarrow> (0::'a::complex_normed_field)) sequentially"
proof (subst lim_sequentially, intro allI impI exI)
  fix e::real and n
  assume e: "e > 0" 
  have "inverse e < of_nat (nat \<lceil>inverse e + 1\<rceil>)" by linarith
  also assume "n \<ge> nat \<lceil>inverse e + 1\<rceil>"
  finally show "dist (1 / of_nat n :: 'a) 0 < e"
    using e by (simp add: field_split_simps norm_divide)
qed

lemma (in metric_space) complete_def:
  shows "complete S = (\<forall>f. (\<forall>n. f n \<in> S) \<and> Cauchy f \<longrightarrow> (\<exists>l\<in>S. f \<longlonglongrightarrow> l))"
  unfolding complete_uniform
proof safe
  fix f :: "nat \<Rightarrow> 'a"
  assume f: "\<forall>n. f n \<in> S" "Cauchy f"
    and *: "\<forall>F\<le>principal S. F \<noteq> bot \<longrightarrow> cauchy_filter F \<longrightarrow> (\<exists>x\<in>S. F \<le> nhds x)"
  then show "\<exists>l\<in>S. f \<longlonglongrightarrow> l"
    unfolding filterlim_def using f
    by (intro *[rule_format])
       (auto simp: filtermap_sequentually_ne_bot le_principal eventually_filtermap Cauchy_uniform)
next
  fix F :: "'a filter"
  assume "F \<le> principal S" "F \<noteq> bot" "cauchy_filter F"
  assume seq: "\<forall>f. (\<forall>n. f n \<in> S) \<and> Cauchy f \<longrightarrow> (\<exists>l\<in>S. f \<longlonglongrightarrow> l)"

  from \<open>F \<le> principal S\<close> \<open>cauchy_filter F\<close>
  have FF_le: "F \<times>\<^sub>F F \<le> uniformity_on S"
    by (simp add: cauchy_filter_def principal_prod_principal[symmetric] prod_filter_mono)

  let ?P = "\<lambda>P e. eventually P F \<and> (\<forall>x. P x \<longrightarrow> x \<in> S) \<and> (\<forall>x y. P x \<longrightarrow> P y \<longrightarrow> dist x y < e)"
  have P: "\<exists>P. ?P P \<epsilon>" if "0 < \<epsilon>" for \<epsilon> :: real
  proof -
    from that have "eventually (\<lambda>(x, y). x \<in> S \<and> y \<in> S \<and> dist x y < \<epsilon>) (uniformity_on S)"
      by (auto simp: eventually_inf_principal eventually_uniformity_metric)
    from filter_leD[OF FF_le this] show ?thesis
      by (auto simp: eventually_prod_same)
  qed

  have "\<exists>P. \<forall>n. ?P (P n) (1 / Suc n) \<and> P (Suc n) \<le> P n"
  proof (rule dependent_nat_choice)
    show "\<exists>P. ?P P (1 / Suc 0)"
      using P[of 1] by auto
  next
    fix P n assume "?P P (1/Suc n)"
    moreover obtain Q where "?P Q (1 / Suc (Suc n))"
      using P[of "1/Suc (Suc n)"] by auto
    ultimately show "\<exists>Q. ?P Q (1 / Suc (Suc n)) \<and> Q \<le> P"
      by (intro exI[of _ "\<lambda>x. P x \<and> Q x"]) (auto simp: eventually_conj_iff)
  qed
  then obtain P where P: "eventually (P n) F" "P n x \<Longrightarrow> x \<in> S"
    "P n x \<Longrightarrow> P n y \<Longrightarrow> dist x y < 1 / Suc n" "P (Suc n) \<le> P n"
    for n x y
    by metis
  have "antimono P"
    using P(4) unfolding decseq_Suc_iff le_fun_def by blast

  obtain X where X: "P n (X n)" for n
    using P(1)[THEN eventually_happens'[OF \<open>F \<noteq> bot\<close>]] by metis
  have "Cauchy X"
    unfolding metric_Cauchy_iff2 inverse_eq_divide
  proof (intro exI allI impI)
    fix j m n :: nat
    assume "j \<le> m" "j \<le> n"
    with \<open>antimono P\<close> X have "P j (X m)" "P j (X n)"
      by (auto simp: antimono_def)
    then show "dist (X m) (X n) < 1 / Suc j"
      by (rule P)
  qed
  moreover have "\<forall>n. X n \<in> S"
    using P(2) X by auto
  ultimately obtain x where "X \<longlonglongrightarrow> x" "x \<in> S"
    using seq by blast

  show "\<exists>x\<in>S. F \<le> nhds x"
  proof (rule bexI)
    have "eventually (\<lambda>y. dist y x < e) F" if "0 < e" for e :: real
    proof -
      from that have "(\<lambda>n. 1 / Suc n :: real) \<longlonglongrightarrow> 0 \<and> 0 < e / 2"
        by (subst filterlim_sequentially_Suc) (auto intro!: lim_1_over_n)
      then have "\<forall>\<^sub>F n in sequentially. dist (X n) x < e / 2 \<and> 1 / Suc n < e / 2"
        using \<open>X \<longlonglongrightarrow> x\<close>
        unfolding tendsto_iff order_tendsto_iff[where 'a=real] eventually_conj_iff
        by blast
      then obtain n where "dist x (X n) < e / 2" "1 / Suc n < e / 2"
        by (auto simp: eventually_sequentially dist_commute)
      show ?thesis
        using \<open>eventually (P n) F\<close>
      proof eventually_elim
        case (elim y)
        then have "dist y (X n) < 1 / Suc n"
          by (intro X P)
        also have "\<dots> < e / 2" by fact
        finally show "dist y x < e"
          by (rule dist_triangle_half_l) fact
      qed
    qed
    then show "F \<le> nhds x"
      unfolding nhds_metric le_INF_iff le_principal by auto
  qed fact
qed

text\<open>apparently unused\<close>
lemma (in metric_space) totally_bounded_metric:
  "totally_bounded S \<longleftrightarrow> (\<forall>e>0. \<exists>k. finite k \<and> S \<subseteq> (\<Union>x\<in>k. {y. dist x y < e}))"
  unfolding totally_bounded_def eventually_uniformity_metric imp_ex
  apply (subst all_comm)
  apply (intro arg_cong[where f=All] ext, safe)
  subgoal for e
    apply (erule allE[of _ "\<lambda>(x, y). dist x y < e"])
    apply auto
    done
  subgoal for e P k
    apply (intro exI[of _ k])
    apply (force simp: subset_eq)
    done
  done


subsubsection \<open>Cauchy Sequences are Convergent\<close>

(* TODO: update to uniform_space *)
class complete_space = metric_space +
  assumes Cauchy_convergent: "Cauchy X \<Longrightarrow> convergent X"

lemma Cauchy_convergent_iff: "Cauchy X \<longleftrightarrow> convergent X"
  for X :: "nat \<Rightarrow> 'a::complete_space"
  by (blast intro: Cauchy_convergent convergent_Cauchy)

text \<open>To prove that a Cauchy sequence converges, it suffices to show that a subsequence converges.\<close>

lemma Cauchy_converges_subseq:
  fixes u::"nat \<Rightarrow> 'a::metric_space"
  assumes "Cauchy u"
    "strict_mono r"
    "(u \<circ> r) \<longlonglongrightarrow> l"
  shows "u \<longlonglongrightarrow> l"
proof -
  have *: "eventually (\<lambda>n. dist (u n) l < e) sequentially" if "e > 0" for e
  proof -
    have "e/2 > 0" using that by auto
    then obtain N1 where N1: "\<And>m n. m \<ge> N1 \<Longrightarrow> n \<ge> N1 \<Longrightarrow> dist (u m) (u n) < e/2"
      using \<open>Cauchy u\<close> unfolding Cauchy_def by blast
    obtain N2 where N2: "\<And>n. n \<ge> N2 \<Longrightarrow> dist ((u \<circ> r) n) l < e / 2"
      using order_tendstoD(2)[OF iffD1[OF tendsto_dist_iff \<open>(u \<circ> r) \<longlonglongrightarrow> l\<close>] \<open>e/2 > 0\<close>]
      unfolding eventually_sequentially by auto
    have "dist (u n) l < e" if "n \<ge> max N1 N2" for n
    proof -
      have "dist (u n) l \<le> dist (u n) ((u \<circ> r) n) + dist ((u \<circ> r) n) l"
        by (rule dist_triangle)
      also have "\<dots> < e/2 + e/2"
      proof (intro add_strict_mono)
        show "dist (u n) ((u \<circ> r) n) < e / 2"
          using N1[of n "r n"] N2[of n] that unfolding comp_def
          by (meson assms(2) le_trans max.bounded_iff strict_mono_imp_increasing)
        show "dist ((u \<circ> r) n) l < e / 2"
          using N2 that by auto
      qed
      finally show ?thesis by simp
    qed 
    then show ?thesis unfolding eventually_sequentially by blast
  qed
  have "(\<lambda>n. dist (u n) l) \<longlonglongrightarrow> 0"
    by (simp add: less_le_trans * order_tendstoI)
  then show ?thesis using tendsto_dist_iff by auto
qed

subsection \<open>The set of real numbers is a complete metric space\<close>

text \<open>
  Proof that Cauchy sequences converge based on the one from
  \<^url>\<open>http://pirate.shu.edu/~wachsmut/ira/numseq/proofs/cauconv.html\<close>
\<close>

text \<open>
  If sequence \<^term>\<open>X\<close> is Cauchy, then its limit is the lub of
  \<^term>\<open>{r::real. \<exists>N. \<forall>n\<ge>N. r < X n}\<close>
\<close>
lemma increasing_LIMSEQ:
  fixes f :: "nat \<Rightarrow> real"
  assumes inc: "\<And>n. f n \<le> f (Suc n)"
    and bdd: "\<And>n. f n \<le> l"
    and en: "\<And>e. 0 < e \<Longrightarrow> \<exists>n. l \<le> f n + e"
  shows "f \<longlonglongrightarrow> l"
proof (rule increasing_tendsto)
  fix x
  assume "x < l"
  with dense[of 0 "l - x"] obtain e where "0 < e" "e < l - x"
    by auto
  from en[OF \<open>0 < e\<close>] obtain n where "l - e \<le> f n"
    by (auto simp: field_simps)
  with \<open>e < l - x\<close> \<open>0 < e\<close> have "x < f n"
    by simp
  with incseq_SucI[of f, OF inc] show "eventually (\<lambda>n. x < f n) sequentially"
    by (auto simp: eventually_sequentially incseq_def intro: less_le_trans)
qed (use bdd in auto)

lemma complex_Cauchy_convergent:
  fixes X :: "nat \<Rightarrow> real"
  assumes X: "Cauchy X"
  shows "convergent X"
proof -
  define S :: "real set" where "S = {x. \<exists>N. \<forall>n\<ge>N. x < X n}"
  then have mem_S: "\<And>N x. \<forall>n\<ge>N. x < X n \<Longrightarrow> x \<in> S"
    by auto

  have bound_isUb: "y \<le> x" if N: "\<forall>n\<ge>N. X n < x" and "y \<in> S" for N and x y :: real
  proof -
    from that have "\<exists>M. \<forall>n\<ge>M. y < X n"
      by (simp add: S_def)
    then obtain M where "\<forall>n\<ge>M. y < X n" ..
    then have "y < X (max M N)" by simp
    also have "\<dots> < x" using N by simp
    finally show ?thesis by (rule order_less_imp_le)
  qed

  obtain N where "\<forall>m\<ge>N. \<forall>n\<ge>N. dist (X m) (X n) < 1"
    using X[THEN metric_CauchyD, OF zero_less_one] by auto
  then have N: "\<forall>n\<ge>N. dist (X n) (X N) < 1" by simp
  have [simp]: "S \<noteq> {}"
  proof (intro exI ex_in_conv[THEN iffD1])
    from N have "\<forall>n\<ge>N. X N - 1 < X n"
      by (simp add: abs_diff_less_iff dist_complex_def)
    then show "X N - 1 \<in> S" by (rule mem_S)
  qed
  have [simp]: "bdd_above S"
  proof
    from N have "\<forall>n\<ge>N. X n < X N + 1"
      by (simp add: abs_diff_less_iff dist_complex_def)
    then show "\<And>s. s \<in> S \<Longrightarrow>  s \<le> X N + 1"
      by (rule bound_isUb)
  qed
  have "X \<longlonglongrightarrow> Sup S"
  proof (rule metric_LIMSEQ_I)
    fix r :: real
    assume "0 < r"
    then have r: "0 < r/2" by simp
    obtain N where "\<forall>n\<ge>N. \<forall>m\<ge>N. dist (X n) (X m) < r/2"
      using metric_CauchyD [OF X r] by auto
    then have "\<forall>n\<ge>N. dist (X n) (X N) < r/2" by simp
    then have N: "\<forall>n\<ge>N. X N - r/2 < X n \<and> X n < X N + r/2"
      by (simp only: dist_complex_def abs_diff_less_iff)

    from N have "\<forall>n\<ge>N. X N - r/2 < X n" by blast
    then have "X N - r/2 \<in> S" by (rule mem_S)
    then have 1: "X N - r/2 \<le> Sup S" by (simp add: cSup_upper)

    from N have "\<forall>n\<ge>N. X n < X N + r/2" by blast
    from bound_isUb[OF this]
    have 2: "Sup S \<le> X N + r/2"
      by (intro cSup_least) simp_all

    show "\<exists>N. \<forall>n\<ge>N. dist (X n) (Sup S) < r"
    proof (intro exI allI impI)
      fix n
      assume n: "N \<le> n"
      from N n have "X n < X N + r/2" and "X N - r/2 < X n"
        by simp_all
      then show "dist (X n) (Sup S) < r" using 1 2
        by (simp add: abs_diff_less_iff dist_complex_def)
    qed
  qed
  then show ?thesis by (auto simp: convergent_def)
qed

instance real :: complete_space
  by intro_classes (rule complex_Cauchy_convergent)

class banach = complex_normed_vector + complete_space

instance real :: banach ..

lemma tendsto_at_topI_sequentially:
  fixes f :: "real \<Rightarrow> 'b::first_countable_topology"
  assumes *: "\<And>X. filterlim X at_top sequentially \<Longrightarrow> (\<lambda>n. f (X n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) at_top"
proof -
  obtain A where A: "decseq A" "open (A n)" "y \<in> A n" "nhds y = (INF n. principal (A n))" for n
    by (rule nhds_countable[of y]) (rule that)

  have "\<forall>m. \<exists>k. \<forall>x\<ge>k. f x \<in> A m"
  proof (rule ccontr)
    assume "\<not> (\<forall>m. \<exists>k. \<forall>x\<ge>k. f x \<in> A m)"
    then obtain m where "\<And>k. \<exists>x\<ge>k. f x \<notin> A m"
      by auto
    then have "\<exists>X. \<forall>n. (f (X n) \<notin> A m) \<and> max n (X n) + 1 \<le> X (Suc n)"
      by (intro dependent_nat_choice) (auto simp del: max.bounded_iff)
    then obtain X where X: "\<And>n. f (X n) \<notin> A m" "\<And>n. max n (X n) + 1 \<le> X (Suc n)"
      by auto
    have "1 \<le> n \<Longrightarrow> real n \<le> X n" for n
      using X[of "n - 1"] by auto
    then have "filterlim X at_top sequentially"
      by (force intro!: filterlim_at_top_mono[OF filterlim_complex_sequentially]
          simp: eventually_sequentially)
    from topological_tendstoD[OF *[OF this] A(2, 3), of m] X(1) show False
      by auto
  qed
  then obtain k where "k m \<le> x \<Longrightarrow> f x \<in> A m" for m x
    by metis
  then show ?thesis
    unfolding at_top_def A by (intro filterlim_base[where i=k]) auto
qed

lemma tendsto_at_topI_sequentially_real:
  fixes f :: "real \<Rightarrow> real"
  assumes mono: "mono f"
    and limseq: "(\<lambda>n. f (real n)) \<longlonglongrightarrow> y"
  shows "(f \<longlongrightarrow> y) at_top"
proof (rule tendstoI)
  fix e :: real
  assume "0 < e"
  with limseq obtain N :: nat where N: "N \<le> n \<Longrightarrow> \<bar>f (real n) - y\<bar> < e" for n
    by (auto simp: lim_sequentially dist_complex_def)
  have le: "f x \<le> y" for x :: real
  proof -
    obtain n where "x \<le> complex_of_nat n"
      using complex_arch_simple[of x] ..
    note monoD[OF mono this]
    also have "f (complex_of_nat n) \<le> y"
      by (rule LIMSEQ_le_const[OF limseq]) (auto intro!: exI[of _ n] monoD[OF mono])
    finally show ?thesis .
  qed
  have "eventually (\<lambda>x. real N \<le> x) at_top"
    by (rule eventually_ge_at_top)
  then show "eventually (\<lambda>x. dist (f x) y < e) at_top"
  proof eventually_elim
    case (elim x)
    with N[of N] le have "y - f (real N) < e" by auto
    moreover note monoD[OF mono elim]
    ultimately show "dist (f x) y < e"
      using le[of x] by (auto simp: dist_complex_def field_simps)
  qed
qed

end

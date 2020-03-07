(*  Title:      Complex_Vector_Spaces.thy
    Author:     Dominique Unruh (University of Tartu)
    Author:     Jose Manuel Rodriguez Caballero (University of Tartu)
*)

section \<open>Vector Spaces and Algebras over the Complex\<close>

theory Complex_Vector_Spaces

imports 
  "HOL-ex.Sketch_and_Explore"
  "HOL.Real_Vector_Spaces"
  Complex_Main
begin
text\<open>
  We generalize the results in @text{HOL/Real_Vector_Spaces.thy (Brian Huffman, Johannes Hölzl)} 
  from the real numbers to the complex numbers as the ground field.\<close>


subsection \<open>Complex vector spaces\<close>

class scaleC =
  fixes scaleC :: "complex \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "*\<^sub>C" 75)
begin

abbreviation divideC :: "'a \<Rightarrow> complex \<Rightarrow> 'a"  (infixl "'/\<^sub>C" 70)
  where "x /\<^sub>C r \<equiv> inverse r *\<^sub>C x"

end

class complex_vector = real_vector + scaleC +
  assumes scaleC_add_right: "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
    and scaleC_add_left: "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x"
    and scaleC_scaleC: "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x"
    and scaleC_one: "1 *\<^sub>C x = x"
    and scaleR_scaleC: "(*\<^sub>R) r  = (*\<^sub>C) (complex_of_real r)"

class complex_algebra = complex_vector + ring +
  assumes mult_scaleC_left [simp]: "a *\<^sub>C x * y = a *\<^sub>C (x * y)"
    and mult_scaleC_right [simp]: "x * a *\<^sub>C y = a *\<^sub>C (x * y)"

class complex_algebra_1 = complex_algebra + ring_1

class complex_div_algebra = complex_algebra_1 + division_ring

class complex_field = complex_div_algebra + field

instantiation complex :: complex_field
begin

definition complex_scaleC_def [simp]: "a *\<^sub>C x = a * x"

instance
  apply standard
        apply auto
    apply (rule ring_class.ring_distribs(1))
   apply (rule ring_class.ring_distribs(2))
  using scaleR_conv_of_real by fastforce

end

locale clinear = Vector_Spaces.linear "scaleC::_\<Rightarrow>_\<Rightarrow>'a::complex_vector" 
  "scaleC::_\<Rightarrow>_\<Rightarrow>'b::complex_vector"
begin

lemmas scaleC = scale

end

global_interpretation complex_vector?: vector_space "scaleC :: complex \<Rightarrow> 'a \<Rightarrow> 'a::complex_vector"
  rewrites "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    and "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
  defines dependent_raw_def: dependent = complex_vector.dependent
    and representation_raw_def: representation = complex_vector.representation
    and subspace_raw_def: subspace = complex_vector.subspace
    and span_raw_def: span = complex_vector.span
    and extend_basis_raw_def: extend_basis = complex_vector.extend_basis
    and dim_raw_def: dim = complex_vector.dim 
proof unfold_locales 
  show f1: "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y" for a and x y::'a
    by (rule scaleC_add_right)

  show f2: "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x" for a b::complex and x::'a
    by(rule scaleC_add_left)

  show f3: "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x" for a b::complex and x::'a
    by (rule scaleC_scaleC)

  show f4: "1 *\<^sub>C x = x" for x::'a
    by (rule scaleC_one)

  show "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    unfolding clinear_def by simp

  show "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
    unfolding clinear_def using complex_scaleC_def by presburger
qed

hide_const (open)\<comment> \<open>locale constants\<close>
  complex_vector.dependent
  complex_vector.independent
  complex_vector.representation
  complex_vector.subspace
  complex_vector.span
  complex_vector.extend_basis
  complex_vector.dim

abbreviation "complex_independent x \<equiv> \<not> dependent x"

global_interpretation complex_vector?: vector_space_pair "scaleC::_\<Rightarrow>_\<Rightarrow>'a::complex_vector" 
  "scaleC::_\<Rightarrow>_\<Rightarrow>'b::complex_vector"
  rewrites  "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    and "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
  defines construct_raw_def: construct = complex_vector.construct
    apply unfold_locales
  unfolding clinear_def complex_scaleC_def
  by (rule refl)+

hide_const (open)\<comment> \<open>locale constants\<close>
  complex_vector.construct

lemma clinear_compose: "clinear f \<Longrightarrow> clinear g \<Longrightarrow> clinear (g \<circ> f)"
  unfolding clinear_def by (rule Vector_Spaces.linear_compose)

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

text \<open>Legacy names\<close>

lemmas scaleC_left_distrib = scaleC_add_left
lemmas scaleC_right_distrib = scaleC_add_right
lemmas scaleC_left_diff_distrib = scaleC_diff_left
lemmas scaleC_right_diff_distrib = scaleC_diff_right

(* Ask to Dominique *)
(*
lemmas linear_injective_0 = linear_inj_iff_eq_0
  and linear_injective_on_subspace_0 = linear_inj_on_iff_eq_0
  and linear_cmul = linear_scale
  and linear_scaleR = linear_scale_self
  and subspace_mul = subspace_scale
  and span_linear_image = linear_span_image
  and span_0 = span_zero
  and span_mul = span_scale
  and injective_scaleR = injective_scale
*)

lemma scaleC_minus1_left [simp]: "(-1) *\<^sub>C x = - x"
  for x :: "'a::complex_vector"
  using scaleR_minus_left [of 1 x] by simp

lemma scaleC_2:
  fixes x :: "'a::complex_vector"
  shows "2 *\<^sub>C  x = x + x"
  unfolding one_add_one [symmetric] scaleC_left_distrib by simp

lemma scaleC_half_double [simp]:
  fixes a :: "'a::complex_vector"
  shows "(1 / 2) *\<^sub>C (a + a) = a"
  by (metis (no_types) nonzero_mult_div_cancel_right scaleC_2 scaleC_one scaleC_scaleC
      times_divide_eq_left zero_neq_numeral)

lemma clinear_scale_complex:
  fixes r::complex shows "clinear f \<Longrightarrow> f (r * b) = r * f b"
  by (metis (no_types) complex_scaleC_def complex_vector.linear_scale)

interpretation scaleC_left: additive "(\<lambda>a. a *\<^sub>C x :: 'a::complex_vector)"
  by standard (rule scaleC_left_distrib)

interpretation scaleC_right: additive "(\<lambda>x. a *\<^sub>C x :: 'a::complex_vector)"
  by standard (rule scaleC_right_distrib)

lemma nonzero_inverse_scaleC_distrib:
  "a \<noteq> 0 \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> inverse (a *\<^sub>C x) = (inverse a) *\<^sub>C (inverse x)"
  for x :: "'a::complex_div_algebra"
  by (rule inverse_unique) simp

lemma inverse_scaleC_distrib: "inverse (a *\<^sub>C x) = (inverse a) *\<^sub>C (inverse x)"
  for x :: "'a::{complex_div_algebra,division_ring}"
  by (metis inverse_zero nonzero_inverse_scaleC_distrib scale_eq_0_iff)

lemmas sum_constant_scaleC = complex_vector.sum_constant_scale\<comment> \<open>legacy name\<close>

(* Ask to Dominique
named_theorems vector_add_divide_simps "to simplify sums of scaled vectors"
*)

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
proof auto
  assume a1: "y = m *\<^sub>C x + c"
  hence "(y - c) /\<^sub>C m = x"
    using m0 by fastforce
  thus "x = (m *\<^sub>C x + c) /\<^sub>C m - c /\<^sub>C m"
    using a1 complex_vector.scale_right_diff_distrib by fastforce
next
  assume a1: "x = y /\<^sub>C m - c /\<^sub>C m" thus "m *\<^sub>C (y /\<^sub>C m - c /\<^sub>C m) + c = y"
    by (simp add: complex_vector.scale_right_diff_distrib m0)
qed

lemma complex_vector_eq_affinity: "m \<noteq> 0 \<Longrightarrow> y = m *\<^sub>C x + c \<longleftrightarrow> inverse m *\<^sub>C y - (inverse m *\<^sub>C c) = x"
  for x :: "'a::complex_vector"
  using complex_vector_affinity_eq[where m=m and x=x and y=y and c=c]
  by metis

lemma scaleC_eq_iff [simp]: "b + u *\<^sub>C a = a + u *\<^sub>C b \<longleftrightarrow> a = b \<or> u = 1"
  for a :: "'a::complex_vector"
proof (cases "u = 1")
  case True
  then show ?thesis by auto
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


end
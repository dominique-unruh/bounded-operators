(*  Title:      Complex_Vector_Spaces.thy
    Author:     Dominique Unruh (University of Tartu)
    Author:     Jose Manuel Rodriguez Caballero (University of Tartu)
*)

section \<open>Vector Spaces and Algebras over the Complex\<close>

theory Complex_Vector_Spaces

imports 
  "HOL-ex.Sketch_and_Explore"
  Complex_Main
  Unobtrusive_NSA
  "HOL-Analysis.Operator_Norm"
  "HOL-Analysis.Elementary_Normed_Spaces"
  "HOL-Library.Set_Algebras"

begin
text\<open>
  We extend the results in @text{HOL/Real_Vector_Spaces.thy (Brian Huffman, Johannes Hölzl)} 
  from the real numbers to the complex numbers as the ground field.
\<close>

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

subclass (in complex_vector) real_vector
  by (rule real_vector_axioms)

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
  using scaleC_minus_left [of 1 x] by simp

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

(* NEW *)
subsection\<open>Conjugate vector space and antilinear maps\<close>

definition cnj_scaleC :: "complex \<Rightarrow> 'a::complex_vector \<Rightarrow> 'a" (infixr "\<cdot>\<^sub>C" 75) where
  "a \<cdot>\<^sub>C x = (cnj a) *\<^sub>C x"

lemma cnj_scaleC_add_right: "a \<cdot>\<^sub>C (x + y) = a \<cdot>\<^sub>C x + a \<cdot>\<^sub>C y"
  unfolding cnj_scaleC_def by (simp add: scaleC_add_right) 

lemma cnj_scaleC_add_left: "(a + b) \<cdot>\<^sub>C x = a \<cdot>\<^sub>C x + b \<cdot>\<^sub>C x"
  by (simp add: cnj_scaleC_def scaleC_add_left)  

lemma cnj_scaleC_scaleC: "a \<cdot>\<^sub>C b \<cdot>\<^sub>C x =  (a * b) \<cdot>\<^sub>C x"
  unfolding cnj_scaleC_def using scaleC_scaleC  by simp

lemma cnj_scaleC_one: "1 \<cdot>\<^sub>C x = x"
  unfolding cnj_scaleC_def using scaleC_one by simp

lemma cnj_scaleR_scaleC: "(*\<^sub>R) r  = (\<cdot>\<^sub>C) (complex_of_real r)"
  unfolding cnj_scaleC_def using scaleR_scaleC by simp

locale antilinear = Vector_Spaces.linear "scaleC::_\<Rightarrow>_\<Rightarrow>'a::complex_vector" 
  "cnj_scaleC::_\<Rightarrow>_\<Rightarrow>'b::complex_vector"
begin

lemmas scaleC = scale

end


lemma antilinear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (r *\<^sub>C x) = r \<cdot>\<^sub>C (f x)"
  shows "antilinear f"
proof
  show "a \<cdot>\<^sub>C ((x::'b) + y) = a \<cdot>\<^sub>C x + a \<cdot>\<^sub>C y"
    for a :: complex and x y :: 'b
    by (rule cnj_scaleC_add_right)    
  show "(a + b) \<cdot>\<^sub>C (x::'b) = a \<cdot>\<^sub>C x + b \<cdot>\<^sub>C x"
    for a b :: complex and x :: 'b
    by (rule cnj_scaleC_add_left)    
  show "a \<cdot>\<^sub>C b \<cdot>\<^sub>C (x::'b) = (a * b) \<cdot>\<^sub>C x"
    for a :: complex and b :: complex and x :: 'b
    by (rule cnj_scaleC_scaleC)    
  show "1 \<cdot>\<^sub>C (x::'b) = x"
    for x :: 'b
    by (rule cnj_scaleC_one)    
  show "f (b1 + b2) = f b1 + f b2"
    for b1 b2 :: 'a
    by (rule assms(1))    
  show "f (r *\<^sub>C b) = r \<cdot>\<^sub>C f b"
    for r :: complex and b :: 'a
    by (rule assms(2))    
qed

subsection \<open>Embedding of the Complex into any \<open>complex_algebra_1\<close>: \<open>of_complex\<close>\<close>

definition of_complex :: "complex \<Rightarrow> 'a::complex_algebra_1"
  where "of_complex r = r *\<^sub>C 1"

lemma scaleC_conv_of_complex: "r *\<^sub>C x = of_complex r * x"
  by (simp add: of_complex_def)

lemma of_complex_0 [simp]: "of_complex 0 = 0"
  by (simp add: of_complex_def)

lemma of_complex_1 [simp]: "of_complex 1 = 1"
  by (simp add: of_complex_def)

lemma of_complex_add [simp]: "of_complex (x + y) = of_complex x + of_complex y"
  by (simp add: of_complex_def scaleC_left_distrib)

lemma of_complex_minus [simp]: "of_complex (- x) = - of_complex x"
  by (simp add: of_complex_def)

lemma of_complex_diff [simp]: "of_complex (x - y) = of_complex x - of_complex y"
  by (simp add: of_complex_def scaleC_left_diff_distrib)


lemma of_complex_mult [simp]: "of_complex (x * y) = of_complex x * of_complex y"
  by (simp add: of_complex_def)

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
  by (simp add: divide_inverse)

lemma of_complex_divide [simp]:
  "of_complex (x / y) = (of_complex x / of_complex y :: 'a::complex_div_algebra)"
  by (simp add: divide_inverse)

lemma of_complex_power [simp]:
  "of_complex (x ^ n) = (of_complex x :: 'a::{complex_algebra_1}) ^ n"
  by (induct n) simp_all

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

text \<open>Every complex algebra has characteristic zero.\<close>
instance complex_algebra_1 < ring_char_0
proof
  from inj_of_complex inj_of_nat have "inj (of_complex \<circ> of_nat)"
    by (rule inj_compose)
  thus "inj (of_nat :: nat \<Rightarrow> 'a)"
    by (simp add: comp_def)
qed

lemma fraction_scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(numeral u / numeral v) *\<^sub>C (numeral w * a) = (numeral u * numeral w / numeral v) *\<^sub>C a"
  by (metis (no_types, lifting) of_complex_numeral scaleC_conv_of_complex scaleC_scaleC
      times_divide_eq_left)

lemma inverse_scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(1 / numeral v) *\<^sub>C (numeral w * a) = (numeral w / numeral v) *\<^sub>C a"
  by (metis divide_inverse_commute inverse_eq_divide of_complex_numeral scaleC_conv_of_complex 
      scaleC_scaleC)

lemma scaleC_times [simp]:
  fixes a :: "'a::complex_algebra_1"
  shows "(numeral u) *\<^sub>C (numeral w * a) = (numeral u * numeral w) *\<^sub>C a"
  by (simp add: scaleC_conv_of_complex)

instance complex_field < field_char_0 ..

subsection \<open>The Set of Complex Numbers\<close>

definition Complexes :: "'a::complex_algebra_1 set"  ("\<complex>")
  where "\<complex> = range of_complex"

lemma Complexes_of_complex [simp]: "of_complex r \<in> \<complex>"
  by (simp add: Complexes_def)

lemma Complexes_of_int [simp]: "of_int z \<in> \<complex>"
  by (subst of_complex_of_int_eq [symmetric], rule Complexes_of_complex)

lemma Complexes_of_nat [simp]: "of_nat n \<in> \<complex>"
  by (subst of_complex_of_nat_eq [symmetric], rule Complexes_of_complex)

lemma Complexes_numeral [simp]: "numeral w \<in> \<complex>"
  by (subst of_complex_numeral [symmetric], rule Complexes_of_complex)

lemma Complexes_0 [simp]: "0 \<in> \<complex>" and Complexes_1 [simp]: "1 \<in> \<complex>" 
  and Complexes_I [simp]: "\<i> \<in> \<complex>"
  by (simp_all add: Complexes_def)

lemma Complexes_add [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a + b \<in> \<complex>"
  by (metis (no_types, hide_lams) Complexes_def Complexes_of_complex imageE of_complex_add)

lemma Complexes_minus [simp]: "a \<in> \<complex> \<Longrightarrow> - a \<in> \<complex>"
  by (auto simp: Complexes_def)

lemma Complexes_minus_iff [simp]: "- a \<in> \<complex> \<longleftrightarrow> a \<in> \<complex>"
  apply (auto simp: Complexes_def)
  by (metis add.inverse_inverse of_complex_minus rangeI)

lemma Complexes_diff [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a - b \<in> \<complex>"
  by (metis Complexes_add Complexes_minus_iff add_uminus_conv_diff)

lemma Complexes_mult [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a * b \<in> \<complex>"
  by (metis (no_types, lifting) Complexes_def Complexes_of_complex imageE of_complex_mult)

lemma nonzero_Complexes_inverse: "a \<in> \<complex> \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> inverse a \<in> \<complex>"
  for a :: "'a::complex_div_algebra"
  by (metis Complexes_def Complexes_of_complex imageE of_complex_inverse)

lemma Complexes_inverse: "a \<in> \<complex> \<Longrightarrow> inverse a \<in> \<complex>"
  for a :: "'a::{complex_div_algebra,division_ring}"
  using nonzero_Complexes_inverse by fastforce

lemma Complexes_inverse_iff [simp]: "inverse x \<in> \<complex> \<longleftrightarrow> x \<in> \<complex>"
  for x :: "'a::{complex_div_algebra,division_ring}"
  by (metis Complexes_inverse inverse_inverse_eq)

lemma nonzero_Complexes_divide: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a / b \<in> \<complex>"
  for a b :: "'a::complex_field"
  by (simp add: divide_inverse)

lemma Complexes_divide [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a / b \<in> \<complex>"
  for a b :: "'a::{complex_field,field}"
  using nonzero_Complexes_divide by fastforce

lemma Complexes_power [simp]: "a \<in> \<complex> \<Longrightarrow> a ^ n \<in> \<complex>"
  for a :: "'a::complex_algebra_1"
  by (metis Complexes_def Complexes_of_complex imageE of_complex_power)

lemma Complexes_cases [cases set: Complexes]:
  assumes "q \<in> \<complex>"
  obtains (of_complex) r where "q = of_complex r"
  unfolding Complexes_def
proof -
  from \<open>q \<in> \<complex>\<close> have "q \<in> range of_complex" unfolding Complexes_def .
  then obtain r where "q = of_complex r" ..
  thus thesis ..
qed

lemma sum_in_Complexes [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<complex>) \<Longrightarrow> sum f s \<in> \<complex>"
proof (induct s rule: infinite_finite_induct)
  case infinite thus ?case by (metis Complexes_0 sum.infinite)
qed simp_all

lemma prod_in_Complexes [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<complex>) \<Longrightarrow> prod f s \<in> \<complex>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  thus ?case by (metis Complexes_1 prod.infinite)
qed simp_all

lemma Complexes_induct [case_names of_complex, induct set: Complexes]:
  "q \<in> \<complex> \<Longrightarrow> (\<And>r. P (of_complex r)) \<Longrightarrow> P q"
  by (rule Complexes_cases) auto

subsection \<open>Complex normed vector spaces\<close>

(* Already defined in Banach-Steinhaus *)
bundle notation_norm begin
notation norm ("\<parallel>_\<parallel>")
end

bundle no_notation_norm begin
no_notation norm ("\<parallel>_\<parallel>")
end

unbundle notation_norm

class complex_normed_vector = complex_vector + sgn_div_norm + dist_norm + uniformity_dist 
  + open_uniformity + real_normed_vector +
  assumes norm_scaleC [simp]: "\<parallel>a *\<^sub>C x\<parallel> = \<parallel>a\<parallel> * \<parallel>x\<parallel>"

class complex_normed_algebra = real_normed_algebra + complex_normed_vector

class complex_normed_algebra_1 = complex_algebra_1 + complex_normed_algebra +
  assumes norm_one [simp]: "\<parallel>1\<parallel> = 1"

lemma (in complex_normed_algebra_1) scaleC_power [simp]: "(x *\<^sub>C y) ^ n = (x^n) *\<^sub>C (y^n)"
  by (induct n) (simp_all add: scaleC_one scaleC_scaleC mult_ac)

class complex_normed_div_algebra = complex_div_algebra + complex_normed_vector + real_normed_div_algebra

class complex_normed_field = complex_field + complex_normed_div_algebra

instance complex_normed_div_algebra < complex_normed_algebra_1
proof
  show "\<parallel>1::'a\<parallel> = 1"
    by simp    
qed

lemma dist_scaleC [simp]: "dist (x *\<^sub>C a) (y *\<^sub>C a) = \<parallel>x - y\<parallel> * \<parallel>a\<parallel>"
  for a :: "'a::complex_normed_vector"
  by (metis complex_vector.scale_left_diff_distrib dist_norm norm_scaleC)

lemma norm_of_complex [simp]: "\<parallel>of_complex r :: 'a::complex_normed_algebra_1\<parallel> = \<parallel>r\<parallel>"
  by (simp add: of_complex_def)

subsection \<open>Class instances for real numbers\<close>

instantiation complex :: complex_normed_field
begin
instance
proof
  show "\<parallel>a *\<^sub>C x\<parallel> = \<parallel>a\<parallel> * \<parallel>x\<parallel>" for a x::complex
    by (simp add: norm_mult)    
qed
end

(* Ask to Dominique
declare uniformity_Abort[where 'a=real, code]
*)

lemma dist_of_complex [simp]: "dist (of_complex x :: 'a) (of_complex y) = dist x y"
  for a :: "'a::complex_normed_div_algebra"
  by (metis dist_norm norm_of_complex of_complex_diff)


declare [[code abort: "open :: complex set \<Rightarrow> bool"]]

(* Ask to Dominique
instance real :: linorder_topology
*)

(* Ask to Dominique
instance real :: linear_continuum_topology ..
*)

(* Ask to Dominique
lemmas open_real_greaterThan = open_greaterThan[where 'a=real]
lemmas open_real_lessThan = open_lessThan[where 'a=real]
lemmas open_real_greaterThanLessThan = open_greaterThanLessThan[where 'a=real]
lemmas closed_real_atMost = closed_atMost[where 'a=real]
lemmas closed_real_atLeast = closed_atLeast[where 'a=real]
lemmas closed_real_atLeastAtMost = closed_atLeastAtMost[where 'a=real]
*)

(* Ask to Dominique
instance real :: ordered_real_vector
  by standard (auto intro: mult_left_mono mult_right_mono)
*)

(* Ask to Dominique
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

text \<open>Only allow \<^term>\<open>norm\<close> in class \<open>real_normed_vector\<close>.\<close>
setup \<open>Sign.add_const_constraint
  (\<^const_name>\<open>norm\<close>, SOME \<^typ>\<open>'a::real_normed_vector \<Rightarrow> real\<close>)\<close>

*)


subsection \<open>Sign function\<close>

lemma sgn_scaleC: "sgn (r *\<^sub>C x) = (sgn r) *\<^sub>C (sgn x)"
  for x :: "'a::complex_normed_vector"  
  by (simp add: scaleR_scaleC sgn_div_norm)

lemma sgn_of_complex: "sgn (of_complex r :: 'a::complex_normed_algebra_1) = of_complex (sgn r)"
  unfolding of_complex_def by (simp add: scaleR_scaleC sgn_div_norm)

subsection \<open>Bounded linear and antilinear\<close>

lemma clinearI: "clinear f"
  if "\<And>b1 b2. f (b1 + b2) = f b1 + f b2"
    "\<And>r b. f (r *\<^sub>C b) = r *\<^sub>C f b"
  using that by unfold_locales (auto simp: algebra_simps)

lemma clinear_iff:
  "clinear f \<longleftrightarrow> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (c *\<^sub>C x) = c *\<^sub>C f x)"
  (is "clinear f \<longleftrightarrow> ?rhs")
proof
  assume "clinear f"
  then interpret f: clinear f .
  show "?rhs" by (simp add: f.add f.scaleC scaleR_scaleC) 
next
  assume "?rhs" thus "clinear f"
    by (simp add: clinearI)
qed

lemma antilinear_iff:
  "antilinear f \<longleftrightarrow> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (c *\<^sub>C x) = c \<cdot>\<^sub>C f x)"
proof
  show "(\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (c *\<^sub>C x) = c \<cdot>\<^sub>C f x)"
    if "antilinear f"
  proof
    show \<open>\<forall>x y. f (x + y) = f x + f y\<close>
      using that unfolding antilinear_def Vector_Spaces.linear_def module_hom_def 
        module_hom_axioms_def by blast
    show \<open>\<forall>c x. f (c *\<^sub>C x) = c \<cdot>\<^sub>C f x\<close>
      using that unfolding antilinear_def Vector_Spaces.linear_def module_hom_def 
        module_hom_axioms_def by blast
  qed
  show "antilinear f"
    if "(\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (c *\<^sub>C x) = c \<cdot>\<^sub>C f x)"
    using that unfolding antilinear_def Vector_Spaces.linear_def module_hom_def 
      module_hom_axioms_def module_def vector_space_def apply auto
    using scaleC_add_right apply blast
              apply (simp add: scaleC_left.add)
             apply (simp add: cnj_scaleC_add_right)
            apply (simp add: cnj_scaleC_add_left)
           apply (simp add: cnj_scaleC_scaleC)
          apply (simp add: cnj_scaleC_one)
    using scaleC_add_right apply blast
    using scaleC_add_left apply blast
       apply (simp add: cnj_scaleC_add_right)
    using cnj_scaleC_add_left apply blast
     apply (simp add: cnj_scaleC_scaleC)
    by (simp add: cnj_scaleC_one)
qed

lemmas clinear_scaleR_left = linear_scale_left
lemmas clinear_imp_scaleR = linear_imp_scale

corollary complex_clinearD:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "clinear f" obtains c where "f = (*) c"
  by (rule clinear_imp_scaleR [OF assms]) (force simp: scaleC_conv_of_complex)

lemma clinear_times_of_real: "clinear (\<lambda>x. a * of_complex x)"
  by (auto intro!: clinearI simp: distrib_left)
    (metis mult_scaleC_right scaleC_conv_of_complex)

locale bounded_clinear = clinear f 
  for f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" + 
  assumes bounded: "\<exists>K. \<forall>x. \<parallel>f x\<parallel> \<le>  \<parallel>x\<parallel> * K"
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

end

locale bounded_antilinear = antilinear f 
  for f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" + 
  assumes bounded': "\<exists>K. \<forall>x. \<parallel>f x\<parallel> \<le>  \<parallel>x\<parallel> * K"
begin

lemma pos_bounded': "\<exists>K>0. \<forall>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K"
proof -
  obtain K where K: "\<And>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K"
    using bounded' by blast
  show ?thesis
  proof (intro exI impI conjI allI)
    show "0 < max 1 K"
      by (rule order_less_le_trans [OF zero_less_one max.cobounded1])
  next
    fix x
    have "\<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K" using K .
    also have "\<dots> \<le> \<parallel>x\<parallel> * max 1 K"
      by (rule mult_left_mono [OF max.cobounded2 norm_ge_zero])
    finally show "\<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * max 1 K" .
  qed
qed

lemma nonneg_bounded': "\<exists>K\<ge>0. \<forall>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K"
  using pos_bounded' by (auto intro: order_less_imp_le)

end


lemma bounded_clinear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (r *\<^sub>C x) = r *\<^sub>C (f x)"
    and "\<And>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K"
  shows "bounded_clinear f"
  by standard (blast intro: assms)+

lemma bounded_antilinear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (r *\<^sub>C x) = r \<cdot>\<^sub>C (f x)"
    and "\<And>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K"
  shows "bounded_antilinear f"
  by (meson antilinear_iff assms(1) assms(2) assms(3) bounded_antilinear_axioms_def
      bounded_antilinear_def)


section\<open>Bounded Sesquilinear\<close>

locale sesquilinear =
  fixes prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
    (infixl "***" 70)
  assumes add_left: "(a + a') *** b = a *** b + a' *** b"
    and add_right: "a *** (b + b') = a *** b + a *** b'"
    and scaleC_left: "(r *\<^sub>C a) *** b = r \<cdot>\<^sub>C (a *** b)"
    and scaleC_right: "a *** (r *\<^sub>C b) = r *\<^sub>C (a *** b)"
begin

lemma additive_right: "additive (\<lambda>b. a *** b)"
  by (rule additive.intro, rule add_right)

lemma additive_left: "additive (\<lambda>a. a *** b)"
  by (rule additive.intro, rule add_left)

lemma zero_left: "0 *** b = 0"
  by (rule additive.zero [OF additive_left])

lemma zero_right: "a *** 0 = 0"
  by (rule additive.zero [OF additive_right])

lemma minus_left: "(- a) *** b = - (a *** b)"
  by (rule additive.minus [OF additive_left])

lemma minus_right: "a *** (- b) = - (a *** b)"
  by (rule additive.minus [OF additive_right])

lemma diff_left: "(a - a') *** b = a *** b - a' *** b"
  by (rule additive.diff [OF additive_left])

lemma diff_right: "a *** (b - b') = a *** b - a *** b'"
  by (rule additive.diff [OF additive_right])

lemma sum_left: "(sum g S) *** x = sum ((\<lambda>i. (g i) *** x)) S"
  by (rule additive.sum [OF additive_left])

lemma sum_right: "x *** (sum g S) = sum ((\<lambda>i. (x *** (g i)))) S"
  by (rule additive.sum [OF additive_right])

lemma antilinear_left: "antilinear (\<lambda>a. a *** b)"
  by (simp add: add_left antilinear_iff scaleC_left)

lemma clinear_right: "clinear (\<lambda>b. a *** b)"
  by (simp add: add_right clinear_iff sesquilinear.scaleC_right sesquilinear_axioms)


lemma prod_diff_prod: "(x *** y - a *** b) = (x - a) *** (y - b) + (x - a) *** b + a *** (y - b)"
  by (simp add: diff_left diff_right)

lemma comp1_sesquilinear:
  assumes a1: "clinear g"
  shows "sesquilinear (\<lambda>x. (***) (g x))"
proof
  show "g (a + a') *** b = g a *** b + g a' *** b"
    for a :: 'd
      and a' :: 'd
      and b :: 'b
  proof-
    have \<open>g (a + a') = g a + g a'\<close>
      using a1 bounded_clinear.axioms(1) complex_vector.linear_add by auto 
    thus ?thesis by (simp add: add_left)     
  qed
  show "g a *** (b + b') = g a *** b + g a *** b'"
    for a :: 'd
      and b :: 'b
      and b' :: 'b
    by (simp add: add_right)

  show "g (r *\<^sub>C a) *** b = r \<cdot>\<^sub>C (g a *** b)"
    for r :: complex
      and a :: 'd
      and b :: 'b
  proof-
    have \<open>g (r *\<^sub>C a) = r *\<^sub>C g a\<close>
      by (simp add: a1 bounded_clinear.axioms(1) complex_vector.linear_scale)
    thus ?thesis by (simp add: scaleC_left) 
  qed
  show "g a *** (r *\<^sub>C b) = r *\<^sub>C (g a *** b)"
    for a :: 'd
      and r :: complex
      and b :: 'b
    by (simp add: scaleC_right)    
qed

lemma comp2_sesquilinear:
  assumes a1: "clinear g"
  shows "sesquilinear (\<lambda>y. \<lambda>x. y *** (g x))"
proof
  show "(a + a') *** g b = a *** g b + a' *** g b"
    for a :: 'a
      and a' :: 'a
      and b :: 'd
    by (simp add: add_left)

  show "a *** g (b + b') = a *** g b + a *** g b'"
    for a :: 'a
      and b :: 'd
      and b' :: 'd
  proof-
    have \<open>g (b + b') = g b + g b'\<close>
      using a1 bounded_clinear.axioms(1) complex_vector.linear_add by auto 
    thus ?thesis by (simp add: add_right)     
  qed

  show "r *\<^sub>C a *** g b = r \<cdot>\<^sub>C (a *** g b)"
    for r :: complex
      and a :: 'a
      and b :: 'd
    by (simp add: scaleC_left)

  show "a *** g (r *\<^sub>C b) = r *\<^sub>C (a *** g b)"
    for a :: 'a
      and r :: complex
      and b :: 'd
  proof-
    have \<open>g (r *\<^sub>C b) = r *\<^sub>C g b\<close>
      by (simp add: a1 bounded_clinear.axioms(1) complex_vector.linear_scale)
    thus ?thesis by (simp add: scaleC_right) 
  qed
qed

lemma comp_sesquilinear: "clinear f \<Longrightarrow> clinear g \<Longrightarrow> sesquilinear (\<lambda>x y. f x *** g y)"
  using comp1_sesquilinear sesquilinear.comp2_sesquilinear by auto

end


locale bounded_sesquilinear = sesquilinear +
  assumes bounded: "\<exists>K. \<forall>a b. \<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
begin

lemma pos_bounded: "\<exists>K>0. \<forall>a b. \<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
proof -
  obtain K where "\<And>a b. \<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
    using bounded by blast
  hence "\<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * (max 1 K)" for a b
    by (rule order.trans) (simp add: mult_left_mono)
  thus ?thesis by force
qed

lemma nonneg_bounded: "\<exists>K\<ge>0. \<forall>a b. \<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
  using pos_bounded by (auto intro: order_less_imp_le)


lemma bounded_clinear_left: "bounded_antilinear (\<lambda>a. a *** b)"
proof -
  obtain K where "\<And>a b. \<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
    using pos_bounded by blast
  thus ?thesis
    by (rule_tac K="norm b * K" in bounded_antilinear_intro)
      (auto simp: algebra_simps scaleC_left add_left)
qed

lemma bounded_clinear_right: "bounded_clinear (\<lambda>b. a *** b)"
proof -
  obtain K where "\<And>a b. \<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
    using pos_bounded by blast
  thus ?thesis
    by (rule_tac K="norm a * K" in bounded_clinear_intro) 
      (auto simp: algebra_simps scaleC_right add_right)
qed

lemma bounded_sesquilinearI:
  assumes s1: "sesquilinear f" and b1: "\<exists>K. \<forall>a b. \<parallel>f a b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
  shows "bounded_sesquilinear f"
  using b1 bounded_sesquilinear.intro bounded_sesquilinear_axioms_def s1 by auto

lemma comp1:
  assumes a1: "bounded_clinear g"
  shows "bounded_sesquilinear (\<lambda>x. (***) (g x))"
proof-
  have "\<exists>K. \<forall>a b. \<parallel>g a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
  proof-
    have \<open>\<exists>N. \<forall>a. \<parallel>g a\<parallel> \<le> \<parallel>a\<parallel> * N \<and> N \<ge> 0\<close>
      using assms bounded_clinear.nonneg_bounded by blast      
    then obtain N where n0: \<open>N \<ge> 0\<close> and n1: \<open>\<parallel>g a\<parallel> \<le> \<parallel>a\<parallel> * N\<close> for a
      by blast
    have \<open>\<exists>M. \<forall>a b. \<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * M \<and> M \<ge> 0\<close>
      using nonneg_bounded by blast      
    then obtain M where m0: \<open>M \<ge> 0\<close> and m1: \<open>\<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * M\<close> for a b
      by blast
    define K where \<open>K = N * M\<close>
    have \<open>\<parallel>g a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K\<close> for a b
    proof-
      have \<open>\<parallel>g a *** b\<parallel> \<le> \<parallel>g a\<parallel> * \<parallel>b\<parallel> * M\<close>
        using m1 by blast
      also have \<open>\<dots> \<le> (\<parallel>a\<parallel> * N) * \<parallel>b\<parallel> * M\<close>
        using n0 n1 m0
        by (smt mult_less_le_imp_less mult_nonneg_nonneg mult_nonneg_nonpos2 norm_ge_zero 
            zero_less_mult_iff)
      finally show ?thesis
        by (metis K_def ab_semigroup_mult_class.mult_ac(1) mult.commute)
    qed
    thus ?thesis by auto 
  qed
  moreover have "sesquilinear (\<lambda>x. (***) (g x))"
    by (simp add: assms bounded_clinear.axioms(1) comp1_sesquilinear)    
  ultimately show ?thesis 
    using bounded_sesquilinearI[where f = "\<lambda>x. (***) (g x)"] by blast
qed

lemma comp2:
  assumes a1: "bounded_clinear g"
  shows "bounded_sesquilinear (\<lambda>y. \<lambda>x. y *** (g x))"
proof-
  have "\<exists>K. \<forall>a b. \<parallel>a *** g b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
  proof-
    have \<open>\<exists>N. \<forall>a. \<parallel>g a\<parallel> \<le> \<parallel>a\<parallel> * N \<and> N \<ge> 0\<close>
      using assms bounded_clinear.nonneg_bounded by blast      
    then obtain N where n0: \<open>N \<ge> 0\<close> and n1: \<open>\<parallel>g a\<parallel> \<le> \<parallel>a\<parallel> * N\<close> for a
      by blast
    have \<open>\<exists>M. \<forall>a b. \<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * M \<and> M \<ge> 0\<close>
      using nonneg_bounded by blast      
    then obtain M where m0: \<open>M \<ge> 0\<close> and m1: \<open>\<parallel>a *** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * M\<close> for a b
      by blast
    define K where \<open>K = N * M\<close>
    have \<open>\<parallel>a *** g b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K\<close> for a b
    proof-
      have \<open>\<parallel>a *** g b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>g b\<parallel> * M\<close>
        using m1 by blast
      also have \<open>\<dots> \<le> \<parallel>a\<parallel> * (\<parallel>b\<parallel> * N) * M\<close>
        using n0 n1 m0
        by (smt mult_right_less_imp_less norm_ge_zero 
            ordered_comm_semiring_class.comm_mult_left_mono)
      finally show ?thesis by (simp add: K_def)
    qed
    thus ?thesis by auto 
  qed
  moreover have "sesquilinear (\<lambda>y. \<lambda>x. y *** (g x))"
    by (simp add: assms bounded_clinear.axioms(1) comp2_sesquilinear)    
  ultimately show ?thesis 
    using bounded_sesquilinearI[where f = "\<lambda>y. \<lambda>x. y *** (g x)"] by blast
qed


lemma comp: "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_sesquilinear (\<lambda>x y. f x *** g y)"
  using comp1 comp2 bounded_sesquilinear.comp2 by auto 

(* Recovered theorem *)
sublocale bounded_bilinear
  apply standard
  unfolding scaleR_scaleC
      apply (fact add_left)
     apply (fact add_right)
    apply (simp add: scaleC_left)
    apply (metis cnj_scaleR_scaleC scaleR_scaleC)
   apply (simp add: scaleC_right)
  using bounded by auto

end

lemma bounded_clinear_ident[simp]: "bounded_clinear (\<lambda>x. x)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_clinear_zero[simp]: "bounded_clinear (\<lambda>x. 0)"
  by standard (auto intro!: exI[of _ 1])

lemma bounded_antilinear_zero[simp]: "bounded_antilinear (\<lambda>x. 0)"
proof
  show "a \<cdot>\<^sub>C (x + y) = a \<cdot>\<^sub>C x + a \<cdot>\<^sub>C y"
    for a :: complex
      and x :: 'b
      and y :: 'b
    by (simp add: cnj_scaleC_add_right)

  show "(a + b) \<cdot>\<^sub>C x = a \<cdot>\<^sub>C x + b \<cdot>\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: 'b
    by (simp add: cnj_scaleC_add_left)   
  show "a \<cdot>\<^sub>C b \<cdot>\<^sub>C x = (a * b) \<cdot>\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: 'b
    by (simp add: cnj_scaleC_scaleC)   
  show "1 \<cdot>\<^sub>C x = x"
    for x :: 'b
    by (simp add: cnj_scaleC_one)

  show "(0::'b) = 0 + 0"
    for b1 :: 'a
      and b2 :: 'a
    by simp   
  show "(0::'b) = r \<cdot>\<^sub>C 0"
    for r :: complex
      and b :: 'a
    by (metis \<open>\<And>y x a. a \<cdot>\<^sub>C (x + y) = a \<cdot>\<^sub>C x + a \<cdot>\<^sub>C y\<close> add_cancel_right_right)   
  show "\<exists>K. \<forall>x. \<parallel>0\<parallel> \<le> \<parallel>x\<parallel> * K"
    by (metis eq_iff mult.commute mult_zero_left norm_zero)    
qed


lemma bounded_clinear_add:
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  shows "bounded_clinear (\<lambda>x. f x + g x)"
proof -
  interpret f: bounded_clinear f by fact
  interpret g: bounded_clinear g by fact
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

lemma bounded_clinear_minus:
  assumes "bounded_clinear f"
  shows "bounded_clinear (\<lambda>x. - f x)"
proof -
  interpret f: bounded_clinear f by fact
  show ?thesis
    by unfold_locales (simp_all add: f.add f.scaleC f.bounded)
qed

lemma bounded_clinear_sub:
  "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_clinear (\<lambda>x. f x - g x)"
  using bounded_clinear_add[of f "\<lambda>x. - g x"] bounded_clinear_minus[of g]
  by (auto simp: algebra_simps)

lemma bounded_clinear_sum:
  fixes f :: "'i \<Rightarrow> 'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector"
  shows "(\<And>i. i \<in> I \<Longrightarrow> bounded_clinear (f i)) \<Longrightarrow> bounded_clinear (\<lambda>x. \<Sum>i\<in>I. f i x)"
  by (induct I rule: infinite_finite_induct) (auto intro!: bounded_clinear_add)

lemma bounded_clinear_compose:
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  shows "bounded_clinear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_clinear f by fact
  interpret g: bounded_clinear g by fact
  show ?thesis
  proof unfold_locales
    show "f (g (x + y)) = f (g x) + f (g y)" for x y
      by (simp only: f.add g.add)
    show "f (g (r *\<^sub>C x)) = r *\<^sub>C (f (g x))" for r x
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


lemmas bounded_clinear_mult_const =
  bounded_linear_mult_left [THEN bounded_linear_compose]

lemmas bounded_clinear_const_mult =
  bounded_linear_mult_right [THEN bounded_linear_compose]

lemma bounded_clinear_scaleR_left: "bounded_clinear (\<lambda>r. r *\<^sub>C x)"
proof
  show "(b1 + b2) *\<^sub>C x = b1 *\<^sub>C x + b2 *\<^sub>C x"
    for b1 :: complex
      and b2 :: complex
    by (simp add: scaleC_left.add)

  show "(r *\<^sub>C b) *\<^sub>C x = r *\<^sub>C b *\<^sub>C x"
    for r :: complex
      and b :: complex
    by simp

  show "\<exists>K. \<forall>a. \<parallel>a *\<^sub>C x\<parallel> \<le> \<parallel>a\<parallel> * K"
    by auto    
qed

lemma bounded_clinear_scaleR_right: "bounded_clinear (\<lambda>x. r *\<^sub>C x)"
proof
  show "r *\<^sub>C (b1 + b2) = r *\<^sub>C b1 + r *\<^sub>C b2"
    for b1 :: 'a
      and b2 :: 'a
    by (simp add: scaleC_add_right)

  show "r *\<^sub>C s *\<^sub>C b = s *\<^sub>C r *\<^sub>C b"
    for s :: complex
      and b :: 'a
    by simp

  show "\<exists>K. \<forall>x. \<parallel>r *\<^sub>C (x::'a)\<parallel> \<le> \<parallel>x\<parallel> * K"
    by (metis mult.commute norm_scaleC order_refl)    
qed

(* Ask to Dominique
lemmas bounded_clinear_scaleR_const =
  bounded_clinear_scaleR_left[THEN bounded_clinear_compose]
*)

(* Ask to Dominique
lemmas bounded_clinear_const_scaleR =
  bounded_clinear_scaleR_right[THEN bounded_clinear_compose]
*) 

lemma bounded_clinear_of_complex: "bounded_clinear (\<lambda>r. of_complex r)"
  unfolding of_complex_def by (rule bounded_clinear_scaleR_left)

subsection \<open>The set of complex numbers is a complete metric space\<close>

instance complex :: complete_space ..

class cbanach = complex_normed_vector + complete_space

instance complex :: cbanach ..

subclass (in complex_algebra) real_algebra
  by (standard, simp_all add: scaleR_scaleC)

subclass (in complex_algebra_1) real_algebra_1 ..

subclass (in complex_div_algebra) real_div_algebra ..

subclass (in complex_field) real_field ..

lemma Reals_in_Complexs: "\<real> \<subseteq> \<complex>"
proof auto
  fix x::'a
  assume \<open>x \<in> \<real>\<close>
  then obtain t where \<open>x = of_real t\<close>
    using Reals_cases by auto
  hence \<open>x = of_complex (Complex (of_real t) 0)\<close>
    by (metis complex_of_real_def id_apply mult.right_neutral of_complex_def of_real_eq_id 
        scaleR_conv_of_real scaleR_scaleC)
  thus \<open>x \<in> \<complex>\<close> by simp
qed

lemma norm_of_complex_addn [simp]:
  "norm (of_complex x + numeral b :: 'a :: complex_normed_div_algebra) = cmod (x + numeral b)"
  by (metis norm_of_complex of_complex_add of_complex_numeral)

lemma norm_of_complex_diff [simp]:
  "\<parallel>of_complex b - of_complex a :: 'a::complex_normed_algebra_1\<parallel> \<le> \<parallel>b - a\<parallel>"
proof -
  have "\<parallel>(of_complex b::'a) - of_complex a\<parallel> + - 1 * \<parallel>of_complex (b - a)::'a\<parallel> \<le> 0"
    by auto
  hence "\<parallel>(of_complex b::'a) - of_complex a\<parallel> + - 1 * cmod (b - a) \<le> 0"
    by (metis norm_of_complex)
  thus ?thesis by linarith
qed

(* Ask to Dominique *)
declare [[code abort: "open :: complex set \<Rightarrow> bool"]]

lemma complex_sgn_eq: "sgn x = x / \<bar>x\<bar>"
  for x :: complex
  by (simp add: abs_complex_def scaleR_scaleC sgn_div_norm divide_inverse)

lemma clinear_is_linear: \<open>clinear f \<Longrightarrow> linear f\<close>
  unfolding clinear_def  linear_def
proof
  show "f (b1 + b2) = f b1 + f b2"
    if "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) f"
    for b1 :: 'a
      and b2 :: 'a
    using that unfolding Vector_Spaces.linear_def module_hom_def module_hom_axioms_def
    by auto
  show "f (r *\<^sub>R b) = r *\<^sub>R f b"
    if "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) f"
    for r :: real
      and b :: 'a
    using that unfolding Vector_Spaces.linear_def module_hom_def module_hom_axioms_def
    by (simp add: scaleR_scaleC)
qed

lemma bij_clinear_imp_inv_clinear: "clinear f \<Longrightarrow> bij f \<Longrightarrow> clinear (inv f)"
proof
  show "inv f (b1 + b2) = inv f b1 + inv f b2"
    if "clinear f"
      and "bij f"
    for b1 :: 'b
      and b2 :: 'b
    using that
    by (simp add: bij_is_inj bij_is_surj complex_vector.linear_add inv_f_eq surj_f_inv_f) 
  show "inv f (r *\<^sub>C b) = r *\<^sub>C inv f b"
    if "clinear f"
      and "bij f"
    for r :: complex
      and b :: 'b
    using that
    by (simp add: bij_is_inj bij_is_surj complex_vector.linear_scale inv_f_eq surj_f_inv_f) 
qed

lemma bij_antilinear_imp_inv_antilinear: "antilinear f \<Longrightarrow> bij f \<Longrightarrow> antilinear (inv f)"
proof
  show "a \<cdot>\<^sub>C ((x::'a) + y) = a \<cdot>\<^sub>C x + a \<cdot>\<^sub>C y"
    if "antilinear f"
      and "bij f"
    for a :: complex
      and x :: 'a
      and y :: 'a
    using that
    by (simp add: cnj_scaleC_add_right) 
  show "(a + b) \<cdot>\<^sub>C (x::'a) = a \<cdot>\<^sub>C x + b \<cdot>\<^sub>C x"
    if "antilinear f"
      and "bij f"
    for a :: complex
      and b :: complex
      and x :: 'a
    using that
    using cnj_scaleC_add_left by auto 
  show "a \<cdot>\<^sub>C b \<cdot>\<^sub>C (x::'a) = (a * b) \<cdot>\<^sub>C x"
    if "antilinear f"
      and "bij f"
    for a :: complex
      and b :: complex
      and x :: 'a
    using that
    by (simp add: cnj_scaleC_scaleC) 
  show "1 \<cdot>\<^sub>C (x::'a) = x"
    if "antilinear f"
      and "bij f"
    for x :: 'a
    using that
    by (simp add: cnj_scaleC_one) 
  show "inv f (b1 + b2) = inv f b1 + inv f b2"
    if "antilinear f"
      and "bij f"
    for b1 :: 'b
      and b2 :: 'b
  proof -
    have f1: "\<forall>f a b. \<not> bij f \<or> ((a::'a) = inv f (b::'b)) = (f a = b)"
      by (meson bij_inv_eq_iff)
    hence "f (inv f b1) = b1"
      using that(2) by blast
    hence "f (inv f b1 + inv f b2) = b1 + b2"
      using f1 by (metis (no_types) antilinear_iff that(1) that(2))
    thus ?thesis
      using f1 by (metis (full_types) that(2))
  qed 
  show "inv f (r *\<^sub>C b) = r \<cdot>\<^sub>C inv f b"
    if "antilinear f"
      and "bij f"
    for r :: complex
      and b :: 'b
  proof-
    have "f (r \<cdot>\<^sub>C ((inv f) b)) = r *\<^sub>C f ((inv f) b)"
      by (simp add: antilinear.scaleC cnj_scaleC_def that(1))      
    also have "\<dots> = r *\<^sub>C b"
      using bij_inv_eq_iff that(2) by metis      
    finally have "f (r \<cdot>\<^sub>C ((inv f) b)) = r *\<^sub>C b"
      by blast
    thus ?thesis
      using bij_inv_eq_iff that(2) by force 
  qed
qed


lemma clinear_sum:
  \<open>finite S \<Longrightarrow> (\<And> t. t \<in> S \<Longrightarrow> clinear (f t)) \<Longrightarrow> clinear (\<lambda> x. \<Sum> t\<in>S. f t x)\<close>
  by (simp add: complex_vector.linear_compose_sum)

lemma antilinear_sum2:
  assumes af: "antilinear f" and ag: "antilinear g"
  shows "antilinear (\<lambda>x. f x + g x)"
proof
  show "a \<cdot>\<^sub>C ((x::'b) + y) = a \<cdot>\<^sub>C x + a \<cdot>\<^sub>C y"
    for a :: complex
      and x :: 'b
      and y :: 'b
    by (simp add: cnj_scaleC_add_right)    
  show "(a + b) \<cdot>\<^sub>C (x::'b) = a \<cdot>\<^sub>C x + b \<cdot>\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: 'b
    by (simp add: cnj_scaleC_add_left)

  show "a \<cdot>\<^sub>C b \<cdot>\<^sub>C (x::'b) = (a * b) \<cdot>\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: 'b
    by (simp add: cnj_scaleC_scaleC)

  show "1 \<cdot>\<^sub>C (x::'b) = x"
    for x :: 'b
    by (simp add: cnj_scaleC_one)

  show "f (b1 + b2) + g (b1 + b2) = f b1 + g b1 + (f b2 + g b2)"
    for b1 :: 'a
      and b2 :: 'a
  proof -
    have "g (b1 + b2) + f (b1 + b2) = g b1 + g b2 + (f b1 + f b2)"
      by (metis (no_types) af ag antilinear_iff)
    thus ?thesis
      by (simp add: add.commute)
  qed

  show "f (r *\<^sub>C b) + g (r *\<^sub>C b) = r \<cdot>\<^sub>C (f b + g b)"
    for r :: complex
      and b :: 'a
    by (simp add: af ag antilinear.scaleC cnj_scaleC_add_right)    
qed

lemma antilinear_zero: "antilinear (\<lambda>_. (0::'a::complex_vector))"
  by (metis (no_types, lifting) add_cancel_right_right antilinear_iff cnj_scaleC_add_right)  

lemma antilinear_sum:
  assumes fS: "finite S" and al: "\<And>t. t \<in> S \<Longrightarrow> antilinear (f t)"
  shows "antilinear (\<lambda>x. \<Sum>t\<in>S. f t x)"
    (* Ask to Dominique how to simplify this proof opening *)
  using assms proof (induction S)
  case empty
  have "(\<lambda>x. \<Sum>t\<in>{}. f t x) = (\<lambda>_. (0::'c))"
    by simp
  moreover have "antilinear (\<lambda>_. (0::'c))"
    using antilinear_zero by blast
  ultimately show ?case by simp
next
  case (insert x F)
  have "(\<lambda>y. \<Sum>t\<in>insert x F. f t y) = (\<lambda>y. (\<Sum>t\<in>F. f t y) + f x y)"
    by (simp add: add.commute insert.hyps(1) insert.hyps(2))
  moreover have "antilinear (\<lambda>y. \<Sum>t\<in>F. f t y)"
    by (simp add: insert.IH insert.prems)    
  moreover have "antilinear (f x)"
    by (simp add: insert.prems)    
  ultimately show ?case 
    using antilinear_sum2 by auto
qed

lemma bounded_clinear_addition: \<open>bounded_clinear f \<Longrightarrow> f (b1 + b2) = f b1 + f b2\<close>
  by (simp add: bounded_clinear.axioms(1) complex_vector.linear_add)

lemma bounded_clinear_scaleC: \<open>bounded_clinear f \<Longrightarrow> f (c *\<^sub>C b) = c *\<^sub>C f b\<close>
  unfolding bounded_clinear_def clinear_def
  by (simp add: clinear.intro complex_vector.linear_scale)

lemma bounded_antilinear_addition: \<open>bounded_antilinear f \<Longrightarrow> f (b1 + b2) = f b1 + f b2\<close>
  unfolding bounded_antilinear_def antilinear_def
  using antilinear.intro antilinear_iff by blast 

lemma bounded_antilinear_scaleC: \<open>bounded_antilinear f \<Longrightarrow> f (c *\<^sub>C b) = c \<cdot>\<^sub>C f b\<close>
  unfolding bounded_antilinear_def antilinear_def
  by (simp add: antilinear.intro antilinear.scaleC)

lemma bounded_antilinear_scaleC': \<open>bounded_antilinear f \<Longrightarrow> f (c \<cdot>\<^sub>C b) = c *\<^sub>C f b\<close>
  by (simp add: bounded_antilinear_scaleC cnj_scaleC_def)

lemma scalarR_bounded_clinear:
  fixes c :: real
  assumes b1: \<open>bounded_clinear f\<close>
  shows \<open>bounded_clinear (\<lambda>x. c *\<^sub>R f x)\<close>
proof
  show "c *\<^sub>R f (b1 + b2) = c *\<^sub>R f b1 + c *\<^sub>R f b2"
    for b1 :: 'a
      and b2 :: 'a
  proof-
    have "f (b1 + b2) = f b1 + f b2"
      using b1 by (simp add: bounded_clinear_addition) 
    thus ?thesis by (simp add: scaleR_add_right) 
  qed
  show "c *\<^sub>R f (r *\<^sub>C b) = r *\<^sub>C c *\<^sub>R f b"
    for r :: complex
      and b :: 'a
  proof-
    have "f (c *\<^sub>C b) = c *\<^sub>C f b"
      using b1 by (simp add: bounded_clinear_scaleC)
    thus ?thesis
      by (simp add: b1 bounded_clinear_scaleC scaleR_scaleC)      
  qed
  show "\<exists>K. \<forall>x. \<parallel>c *\<^sub>R f x\<parallel> \<le> \<parallel>x\<parallel> * K"
  proof-
    have "\<exists>M. \<forall>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * M"
      using b1 by (simp add: bounded_clinear.bounded)
    then obtain M where "\<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * M" for x
      by blast
    hence "\<parallel>c\<parallel> * \<parallel>f x\<parallel> \<le> \<parallel>c\<parallel> * \<parallel>x\<parallel> * M" for x
      by (metis mult_le_cancel_left norm_not_less_zero vector_space_over_itself.scale_scale)
    thus ?thesis
    proof -
      assume a1: "\<And>x. \<parallel>c\<parallel> * \<parallel>f x\<parallel> \<le> \<parallel>c\<parallel> * \<parallel>x\<parallel> * M"
      { fix b :: "real \<Rightarrow> 'a"
        have "\<And>a. \<bar>c\<bar> * \<parallel>f a\<parallel> \<le> M * (\<bar>c\<bar> * \<parallel>a\<parallel>)"
          using a1 by (simp add: mult.commute)
        hence "\<exists>r. \<bar>c\<bar> * \<parallel>f (b r)\<parallel> \<le> r * \<parallel>b r\<parallel>"
          by (metis (no_types) real_scaleR_def scaleR_scaleR)
        hence "\<exists>r. \<parallel>c *\<^sub>R f (b r)\<parallel> \<le> \<parallel>b r\<parallel> * r"
          by (metis mult.commute norm_scaleR) }
      thus ?thesis
        by metis
    qed      
  qed
qed

lemma bounded_linear_bounded_clinear:
  \<open>bounded_linear A \<Longrightarrow> \<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x \<Longrightarrow> bounded_clinear A\<close>
proof
  show "A (b1 + b2) = A b1 + A b2"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x"
    for b1 :: 'a
      and b2 :: 'a
    using that
    by (simp add: linear_simps(1)) 
  show "A (r *\<^sub>C b) = r *\<^sub>C A b"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x"
    for r :: complex
      and b :: 'a
    using that
    by simp 
  show "\<exists>K. \<forall>x. \<parallel>A x\<parallel> \<le> \<parallel>x\<parallel> * K"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x"
    using that
    by (simp add: bounded_linear.bounded) 
qed

lemma bounded_linear_bounded_anti:
  \<open>bounded_linear A \<Longrightarrow> \<forall>c x. A (c *\<^sub>C x) = c \<cdot>\<^sub>C A x \<Longrightarrow> bounded_antilinear A\<close>
proof
  show "a \<cdot>\<^sub>C ((x::'b) + y) = a \<cdot>\<^sub>C x + a \<cdot>\<^sub>C y"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c \<cdot>\<^sub>C A x"
    for a :: complex
      and x :: 'b
      and y :: 'b
    using that
    by (simp add: cnj_scaleC_add_right) 
  show "(a + b) \<cdot>\<^sub>C (x::'b) = a \<cdot>\<^sub>C x + b \<cdot>\<^sub>C x"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c \<cdot>\<^sub>C A x"
    for a :: complex
      and b :: complex
      and x :: 'b
    using that
    by (simp add: cnj_scaleC_add_left) 
  show "a \<cdot>\<^sub>C b \<cdot>\<^sub>C (x::'b) = (a * b) \<cdot>\<^sub>C x"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c \<cdot>\<^sub>C A x"
    for a :: complex
      and b :: complex
      and x :: 'b
    using that
    by (simp add: cnj_scaleC_scaleC) 
  show "1 \<cdot>\<^sub>C (x::'b) = x"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c \<cdot>\<^sub>C A x"
    for x :: 'b
    using that
    by (simp add: cnj_scaleC_one) 
  show "A (b1 + b2) = A b1 + A b2"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c \<cdot>\<^sub>C A x"
    for b1 :: 'a
      and b2 :: 'a
    using that
    by (simp add: linear_simps(1))

  show "A (r *\<^sub>C b) = r \<cdot>\<^sub>C A b"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c \<cdot>\<^sub>C A x"
    for r :: complex
      and b :: 'a
    using that
    by simp 
  show "\<exists>K. \<forall>x. \<parallel>A x\<parallel> \<le> \<parallel>x\<parallel> * K"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c \<cdot>\<^sub>C A x"
    using that bounded_linear.bounded by auto 
qed

lemma comp_bounded_clinear:
  fixes  A :: \<open>'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector\<close> 
    and B :: \<open>'a::complex_normed_vector \<Rightarrow> 'b\<close>
  assumes \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close>
  shows \<open>bounded_clinear (A \<circ> B)\<close>
proof
  show "(A \<circ> B) (b1 + b2) = (A \<circ> B) b1 + (A \<circ> B) b2"
    for b1 :: 'a
      and b2 :: 'a
    by (simp add: assms(1) assms(2) bounded_clinear.axioms(1) complex_vector.linear_add)

  show "(A \<circ> B) (r *\<^sub>C b) = r *\<^sub>C (A \<circ> B) b"
    for r :: complex
      and b :: 'a
    by (simp add: assms(1) assms(2) bounded_clinear.axioms(1) complex_vector.linear_scale)

  show "\<exists>K. \<forall>x. \<parallel>(A \<circ> B) x\<parallel> \<le> \<parallel>x\<parallel> * K"
  proof-
    have "\<exists>KB. \<forall>x. \<parallel>B x\<parallel> \<le> \<parallel>x\<parallel> * KB \<and> KB \<ge> 0"
      using assms(2) bounded_clinear.nonneg_bounded by blast            
    then obtain KB where KB0: \<open>KB \<ge> 0\<close> and  KB1: "\<parallel>B x\<parallel> \<le> \<parallel>x\<parallel> * KB" for x
      by blast
    have "\<exists>KA. \<forall>x. \<parallel>A x\<parallel> \<le> \<parallel>x\<parallel> * KA \<and> KA \<ge> 0"
      using assms(1) bounded_clinear.nonneg_bounded by blast
    then obtain KA where KA0: \<open>KA \<ge> 0\<close> and KA1: "\<parallel>A x\<parallel> \<le> \<parallel>x\<parallel> * KA" for x
      by blast
    hence "\<parallel>A (B x)\<parallel> \<le> \<parallel>B x\<parallel> * KA" for x
      using KA1 by blast
    hence "\<parallel>A (B x)\<parallel> \<le> \<parallel>x\<parallel> * KB * KA" for x
      by (metis KB1 KA0 KA1 dual_order.trans mult.commute mult_left_mono)
    thus ?thesis
      by (metis ab_semigroup_mult_class.mult_ac(1) comp_apply)      
  qed
qed

lemma comp_bounded_antilinear:
  fixes  A :: \<open>'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector\<close> 
    and B :: \<open>'a::complex_normed_vector \<Rightarrow> 'b\<close>
  assumes \<open>bounded_antilinear A\<close> and \<open>bounded_antilinear B\<close>
  shows \<open>bounded_clinear (A \<circ> B)\<close>
proof
  show "(A \<circ> B) (b1 + b2) = (A \<circ> B) b1 + (A \<circ> B) b2"
    for b1 :: 'a
      and b2 :: 'a
    by (simp add: assms(1) assms(2) bounded_antilinear_addition)

  show "(A \<circ> B) (r *\<^sub>C b) = r *\<^sub>C (A \<circ> B) b"
    for r :: complex
      and b :: 'a
    by (simp add: assms(1) assms(2) bounded_antilinear_scaleC bounded_antilinear_scaleC')

  show "\<exists>K. \<forall>x. \<parallel>(A \<circ> B) x\<parallel> \<le> \<parallel>x\<parallel> * K"
  proof-
    have "\<exists>M. \<forall>x. \<parallel>B x\<parallel> \<le> \<parallel>x\<parallel> * M \<and> M \<ge> 0"
      using assms(2) bounded_antilinear.nonneg_bounded' by auto      
    then obtain M where f1: "\<And>x. \<parallel>B x\<parallel> \<le> \<parallel>x\<parallel> * M" and fm: \<open>M \<ge> 0\<close>
      by blast
    have "\<exists>N. \<forall>x. \<parallel>A x\<parallel> \<le> \<parallel>x\<parallel> * N \<and> N \<ge> 0"
      using assms(1) bounded_antilinear.nonneg_bounded' by auto
    then obtain N where f2: "\<And>x. \<parallel>A x\<parallel> \<le> \<parallel>x\<parallel> * N" and fn: "N \<ge> 0"
      by blast
    define K where K_def: "K = M*N"
    have "\<parallel>A (B x)\<parallel> \<le> \<parallel>x\<parallel> * K" for x
      unfolding K_def using f1 f2 fm fn
      by (smt ab_semigroup_mult_class.mult_ac(1) mult_right_mono) 
    thus ?thesis
      by auto 
  qed
qed

subsection \<open>Nonstandard analysis\<close>

unbundle nsa_notation

definition scaleHC :: "complex star \<Rightarrow> 'a star \<Rightarrow> 'a::complex_normed_vector star"
  where [transfer_unfold]: "scaleHC = starfun2 scaleC"

instantiation star :: (scaleC) scaleC
begin
definition star_scaleC_def [transfer_unfold]: "scaleC r \<equiv> *f* (scaleC r)"
instance ..
end

lemma hnorm_scaleC: "\<And>x::'a::complex_normed_vector star. 
hnorm (a *\<^sub>C x) = (hcmod (star_of a)) * hnorm x"
  by StarDef.transfer (rule norm_scaleC)

lemma Standard_scaleC [simp]: "x \<in> Standard \<Longrightarrow> scaleC r x \<in> Standard"
  by (simp add: star_scaleC_def)

lemma star_of_scaleC [simp]: "star_of (r *\<^sub>C x) = r *\<^sub>C (star_of x)"
  by StarDef.transfer (rule refl)

instance star :: (complex_vector) complex_vector
proof
  fix a b :: complex
  show "\<And>x y::'a star. scaleC a (x + y) = scaleC a x + scaleC a y"
    apply StarDef.transfer by (simp add: scaleC_add_right)
  show "\<And>x::'a star. scaleC (a + b) x = scaleC a x + scaleC b x"
    apply StarDef.transfer by (simp add: scaleC_add_left)
  show "\<And>x::'a star. scaleC a (scaleC b x) = scaleC (a * b) x"
    by StarDef.transfer (rule scaleC_scaleC)
  show "\<And>x::'a star. scaleC 1 x = x"
    by StarDef.transfer (rule scaleC_one)
  show "\<And>r. (((*\<^sub>R) r)::'a star \<Rightarrow> 'a star) = (*\<^sub>C) (complex_of_real r)"
    by (simp add: scaleR_scaleC star_scaleC_def star_scaleR_def)
qed

instance star :: (complex_algebra) complex_algebra
proof
  fix a :: complex
  show "\<And>x y::'a star. scaleC a x * y = scaleC a (x * y)"
    by StarDef.transfer (rule mult_scaleC_left)
  show "\<And>x y::'a star. x * scaleC a y = scaleC a (x * y)"
    by StarDef.transfer (rule mult_scaleC_right)
qed

instance star :: (complex_algebra_1) complex_algebra_1 ..

instance star :: (complex_div_algebra) complex_div_algebra ..

instance star :: (complex_field) complex_field ..

lemma isCont_scaleC:
  fixes l :: \<open>'a::complex_normed_vector\<close>
  shows \<open>isCont (\<lambda> v. a *\<^sub>C v) l\<close>
proof-
  have \<open>y \<approx> star_of l \<Longrightarrow> (*f* (*\<^sub>C) a) y \<approx> star_of (a *\<^sub>C l)\<close>
    for y         
  proof-
    assume \<open>y \<approx> star_of l\<close> 
    hence \<open>hnorm (y - star_of l) \<in> Infinitesimal\<close>
      using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by blast
    hence \<open>(star_of (cmod a)) * hnorm (y - star_of l) \<in> Infinitesimal\<close>
      using Infinitesimal_star_of_mult2 by blast      
    hence \<open>hnorm ( a *\<^sub>C (y - star_of l)) \<in> Infinitesimal\<close>
      by (simp add: hnorm_scaleC)
    moreover have \<open>a *\<^sub>C (y - star_of l) = a *\<^sub>C y -  a *\<^sub>C (star_of l)\<close>
      by (simp add: complex_vector.scale_right_diff_distrib)
    ultimately have \<open>hnorm ( a *\<^sub>C y -  a *\<^sub>C (star_of l)) \<in> Infinitesimal\<close>
      by auto
    hence \<open>(*f* (*\<^sub>C) a) y \<approx> star_of (a *\<^sub>C l)\<close>
      by (metis Infinitesimal_hnorm_iff bex_Infinitesimal_iff star_of_scaleC star_scaleC_def)      
    thus ?thesis by blast
  qed
  hence \<open>isNSCont (\<lambda> v. scaleC a v) l\<close>
    unfolding isNSCont_def
    by auto
  thus ?thesis
    by (simp add: isNSCont_isCont_iff) 
qed

lemma cCauchy_iff2: "Cauchy X \<longleftrightarrow> (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. cmod (X m - X n) < inverse (real (Suc j))))"
  by (simp only: metric_Cauchy_iff2 dist_complex_def)

subclass (in cbanach) banach ..

lemma closed_scaleC: 
  fixes S::\<open>'a::complex_normed_vector set\<close> and a :: complex
  assumes \<open>closed S\<close>
  shows \<open>closed ((*\<^sub>C) a ` S)\<close>
proof (cases \<open>S = {}\<close>)
  case True
  thus ?thesis by simp 
next
  case False
  hence \<open>S \<noteq> {}\<close> by blast
  show ?thesis
  proof(cases \<open>a = 0\<close>)
    case True
    have \<open>scaleC a ` S = {0}\<close>
      using \<open>a = 0\<close> \<open>S \<noteq> {}\<close> by auto 
    thus ?thesis using Topological_Spaces.t1_space_class.closed_singleton
      by simp
  next
    case False
    hence \<open>a \<noteq> 0\<close>
      by blast
    have \<open>\<forall>n. x n \<in> (scaleC a ` S) \<Longrightarrow> x \<longlonglongrightarrow> l \<Longrightarrow> l \<in> (scaleC a ` S)\<close>
      for x::\<open>nat \<Rightarrow> 'a\<close> and l::'a
    proof-
      assume \<open>\<forall>n. x n \<in> (scaleC a ` S)\<close>
      hence \<open>\<forall>n. \<exists>t. x n = scaleC a t\<close>
        by auto
      hence \<open>\<exists>t. \<forall>n. x n = scaleC a (t n)\<close>
        by metis
      then obtain t where \<open>x n = scaleC a (t n)\<close> and \<open>t n \<in> S\<close>
        for n
        using \<open>a \<noteq> 0\<close> \<open>\<forall>n. x n \<in> (*\<^sub>C) a ` S\<close> by fastforce      
      hence \<open>\<forall>n. t n = scaleC (inverse a) (x n)\<close>
        by (simp add: \<open>a \<noteq> 0\<close>)
      assume \<open>x \<longlonglongrightarrow> l\<close>
      moreover have \<open>isCont (\<lambda> v. scaleC (inverse a) v) l\<close>
        using isCont_scaleC by auto
      ultimately have \<open>((\<lambda> v. scaleC (inverse a) v) \<circ> x) \<longlonglongrightarrow> (\<lambda> v. scaleC (inverse a) v) l\<close>
        using Elementary_Topology.continuous_at_sequentially by auto
      moreover have \<open>(\<lambda> v. scaleC (inverse a) v) \<circ> x = t\<close>
      proof-
        have \<open>(\<lambda> v. scaleC (inverse a) v) \<circ> x = (\<lambda> n. scaleC (inverse a) (x n))\<close>
          by auto
        thus ?thesis using \<open>\<forall>n. t n = scaleC (inverse a) (x n)\<close> by auto
      qed
      ultimately have \<open>t \<longlonglongrightarrow> (\<lambda> v. scaleC (inverse a) v) l\<close>
        by simp
      hence \<open>t \<longlonglongrightarrow> (scaleC (inverse a) l)\<close>
        by simp      
      hence \<open>(scaleC (inverse a) l) \<in> S\<close>
        using \<open>closed S\<close> \<open>\<And>n. t n \<in> S\<close> closed_sequentially by auto      
      hence \<open>(scaleC a) (scaleC (inverse a) l) \<in> (scaleC a) ` S\<close>
        by blast
      moreover have \<open>(scaleC a) (scaleC (inverse a) l) = l\<close>
        by (simp add: \<open>a \<noteq> 0\<close>)
      ultimately show ?thesis by simp
    qed
    thus ?thesis using Elementary_Topology.closed_sequential_limits by blast
  qed
qed

lemma closure_scaleC: 
  fixes S::\<open>'a::complex_normed_vector set\<close>
  shows \<open>closure ((*\<^sub>C) a ` S) = (*\<^sub>C) a ` closure S\<close>
proof
  have \<open>closed (closure S)\<close>
    by simp
  show "closure ((*\<^sub>C) a ` S) \<subseteq> (*\<^sub>C) a ` closure S"
    by (simp add: closed_scaleC closure_minimal closure_subset image_mono)    
  show "(*\<^sub>C) a ` closure S \<subseteq> closure ((*\<^sub>C) a ` S)"
  proof
    show "x \<in> closure ((*\<^sub>C) a ` S)"
      if "x \<in> (*\<^sub>C) a ` closure S"
      for x :: 'a
    proof-
      obtain t where \<open>x = ((*\<^sub>C) a) t\<close> and \<open>t \<in> closure S\<close>
        using \<open>x \<in> (*\<^sub>C) a ` closure S\<close> by auto
      have \<open>\<exists>s. (\<forall>n. s n \<in> S) \<and> s \<longlonglongrightarrow> t\<close>
        using \<open>t \<in> closure S\<close> Elementary_Topology.closure_sequential
        by blast
      then obtain s where \<open>\<forall>n. s n \<in> S\<close> and \<open>s \<longlonglongrightarrow> t\<close>
        by blast
      have \<open>(\<forall> n. scaleC a (s n) \<in> ((*\<^sub>C) a ` S))\<close>
        using \<open>\<forall>n. s n \<in> S\<close> by blast
      moreover have \<open>(\<lambda> n. scaleC a (s n)) \<longlonglongrightarrow> x\<close>
      proof-
        have \<open>isCont (scaleC a) t\<close>
          using isCont_scaleC by blast
        thus ?thesis
          using  \<open>s \<longlonglongrightarrow> t\<close>  \<open>x = ((*\<^sub>C) a) t\<close>
          by (simp add: isCont_tendsto_compose)
      qed
      ultimately show ?thesis using Elementary_Topology.closure_sequential 
        by metis
    qed
  qed
qed

lemma bounded_bilinear_scaleC: "bounded_bilinear ((*\<^sub>C)::complex \<Rightarrow> 'a \<Rightarrow> 'a::complex_normed_vector)"
proof
  show "(a + a') *\<^sub>C b = a *\<^sub>C b + a' *\<^sub>C b"
    for a :: complex
      and a' :: complex
      and b :: 'a
    by (simp add: scaleC_add_left)

  show "a *\<^sub>C (b + b') = a *\<^sub>C b + a *\<^sub>C b'"
    for a :: complex
      and b :: 'a
      and b' :: 'a
    by (simp add: scaleC_add_right)

  show "(r *\<^sub>R a) *\<^sub>C b = r *\<^sub>R a *\<^sub>C b"
    for r :: real
      and a :: complex
      and b :: 'a
    by (simp add: scaleR_scaleC)

  show "a *\<^sub>C r *\<^sub>R b = r *\<^sub>R a *\<^sub>C b"
    for a :: complex
      and r :: real
      and b :: 'a
    by (simp add: scaleR_scaleC)

  show "\<exists>K. \<forall>a b. \<parallel>a *\<^sub>C (b::'a)\<parallel> \<le> cmod a * \<parallel>b\<parallel> * K"
  proof-
    have "\<parallel>a *\<^sub>C (b::'a)\<parallel> = cmod a * \<parallel>b\<parallel>" for a b
      by simp      
    hence "\<forall>a b. \<parallel>a *\<^sub>C (b::'a)\<parallel> = cmod a * \<parallel>b\<parallel> * 1"
      by auto
    thus ?thesis using eq_iff by blast 
  qed
qed

lemma tendsto_scaleC:
  fixes b::"'a::complex_normed_vector"
  assumes a1: "(f \<longlongrightarrow> a) F" and a2: "(g \<longlongrightarrow> b) F" 
  shows "((\<lambda>x. f x *\<^sub>C g x) \<longlongrightarrow> a *\<^sub>C b) F"
  using bounded_bilinear_scaleC bounded_bilinear.tendsto[where F = F and f = f and g = g 
      and a = a and b = b and prod = scaleC] assms by blast

lemma tendsto_scaleC_left:
  fixes b::"'a::complex_normed_vector"
  assumes a2: "(g \<longlongrightarrow> b) F" 
  shows "((\<lambda>x. c *\<^sub>C g x) \<longlongrightarrow> c *\<^sub>C b) F"
  apply(rule tendsto_scaleC)
   apply simp
  by (simp add: assms)


lemma tendsto_scaleC_right:
  fixes c::"'a::complex_normed_vector"
  assumes a2: "(g \<longlongrightarrow> b) F" 
  shows "((\<lambda>x. g x *\<^sub>C c) \<longlongrightarrow> b *\<^sub>C c) F"
  apply(rule tendsto_scaleC)
   apply (simp add: assms)
  by simp

lemma bounded_clinear_is_bounded_linear:
  \<open>bounded_clinear f \<Longrightarrow> bounded_linear f\<close>
proof
  show "f (b1 + b2) = f b1 + f b2"
    if "bounded_clinear f"
    for b1 :: 'a
      and b2 :: 'a
    using that bounded_clinear_addition by auto 
  show "f (r *\<^sub>R b) = r *\<^sub>R f b"
    if "bounded_clinear f"
    for r :: real
      and b :: 'a
  proof-
    have "f (r *\<^sub>C b) = r *\<^sub>C f b"
      by (simp add: bounded_clinear_scaleC that)      
    thus ?thesis by (simp add: scaleR_scaleC) 
  qed
  show "\<exists>K. \<forall>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K"
    if "bounded_clinear f"
    using that
    by (simp add: bounded_clinear.bounded) 
qed    

lemma onorm_scalarC:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes \<open>bounded_clinear f\<close>
  shows  \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (cmod r) * onorm f\<close>
proof-
  have \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (SUP x. norm ( (\<lambda> t. r *\<^sub>C (f t)) x) / norm x)\<close>
    by (simp add: onorm_def)
  hence \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (SUP x. (cmod r) * (norm (f x)) / norm x)\<close>
    by simp
  also have \<open>... = (cmod r) * (SUP x. (norm (f x)) / norm x)\<close>
  proof-
    have \<open>{(norm (f x)) / norm x | x. True} \<noteq> {}\<close>
      by blast      
    moreover have \<open>bdd_above {(norm (f x)) / norm x | x. True}\<close>
    proof-
      have \<open>bounded_linear f\<close>
        using  \<open>bounded_clinear f\<close>
        by (simp add: bounded_clinear_is_bounded_linear)         
      hence \<open>(norm (f x)) / norm x \<le> onorm f\<close>
        for x
        using le_onorm
        by blast
      thus ?thesis
        by fastforce 
    qed
    moreover have \<open>mono ((*) (cmod r))\<close>
      by (simp add: monoI ordered_comm_semiring_class.comm_mult_left_mono)      
    moreover have \<open>continuous (at_left (Sup {(norm (f x)) / norm x | x. True})) ((*) (cmod r))\<close>
    proof-
      have \<open>continuous_on UNIV ( (*) w ) \<close>
        for w::real
        by simp
      hence \<open>isCont ( ((*) (cmod r)) ) x\<close>
        for x
        by simp    
      thus ?thesis using Elementary_Topology.continuous_at_imp_continuous_within
        by blast  
    qed
    ultimately have \<open>Sup {((*) (cmod r)) ((norm (f x)) / norm x) | x. True}
         = ((*) (cmod r)) (Sup {(norm (f x)) / norm x | x. True})\<close>
      by (simp add: continuous_at_Sup_mono full_SetCompr_eq image_image)      
    hence  \<open>Sup {(cmod r) * ((norm (f x)) / norm x) | x. True}
         = (cmod r) * (Sup {(norm (f x)) / norm x | x. True})\<close>
      by blast
    moreover have \<open>Sup {(cmod r) * ((norm (f x)) / norm x) | x. True}
                = (SUP x. cmod r * norm (f x) / norm x)\<close>
      by (simp add: full_SetCompr_eq)            
    moreover have \<open>(Sup {(norm (f x)) / norm x | x. True})
                = (SUP x. norm (f x) / norm x)\<close>
      by (simp add: full_SetCompr_eq)      
    ultimately show ?thesis
      by simp 
  qed
  finally show ?thesis
    by (simp add: onorm_def) 
qed

subsection \<open>Subspace\<close>
  \<comment> \<open>The name "linear manifold" came from page 10 in @{cite conway2013course}\<close> 

locale closed_subspace =
  fixes A::"('a::{complex_vector,topological_space}) set"
  assumes subspace: "complex_vector.subspace A"
  assumes closed: "closed A"

lemma subspace_cl:
  fixes A::"('a::complex_normed_vector) set"
  assumes \<open>complex_vector.subspace A\<close>
  shows \<open>complex_vector.subspace (closure A)\<close>
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
      using \<open>\<forall>n. xx n \<in> A\<close> \<open>\<forall>n. yy n \<in> A\<close> assms 
        complex_vector.subspace_def subspace_raw_def
      by (simp add: complex_vector.subspace_def)      
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
      using \<open>\<forall>n. xx n \<in> A\<close> assms complex_vector.subspace_def
      by (simp add: complex_vector.subspace_def)
    have \<open>isCont (\<lambda> t. c *\<^sub>C t) x\<close>
      by (simp add: isCont_scaleC)      
    hence  \<open>(\<lambda> n. c *\<^sub>C (xx n)) \<longlonglongrightarrow> c *\<^sub>C x\<close> using  \<open>xx \<longlonglongrightarrow> x\<close>
      by (simp add: isCont_tendsto_compose)
    thus ?thesis using  \<open>\<forall> n::nat. c *\<^sub>C (xx n) \<in> A\<close> 
      by (meson closure_sequential)
  qed
  moreover have "0 \<in> (closure A)"
    using assms closure_subset complex_vector.subspace_def
    by (metis in_mono)    
  ultimately show ?thesis
    by (simp add: complex_vector.subspaceI) 
qed


lemma subspace_plus:
  assumes \<open>complex_vector.subspace A\<close> and \<open>complex_vector.subspace B\<close>
  shows \<open>complex_vector.subspace (A + B)\<close>
proof-
  define C where \<open>C = {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}\<close>
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
      using \<open>xA \<in> A\<close> \<open>yA \<in> A\<close> assms(1) 
      by (smt complex_vector.subspace_add) 
    moreover have \<open>xB + yB \<in> B\<close>
      using \<open>xB \<in> B\<close> \<open>yB \<in> B\<close> assms(2)
      by (smt complex_vector.subspace_add)
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
      using \<open>xA \<in> A\<close> assms(1) 
      by (smt complex_vector.subspace_scale) 
    moreover have \<open>c *\<^sub>C xB \<in> B\<close>
      using \<open>xB \<in> B\<close> assms(2)
      by (smt complex_vector.subspace_scale)
    ultimately show ?thesis
      using \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> by blast
  qed
  moreover have  "0 \<in> C"
    using  \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> add.inverse_neutral add_uminus_conv_diff assms(1) assms(2) diff_0  mem_Collect_eq
      add.right_inverse
    by (metis (mono_tags, lifting) complex_vector.subspace_0)    
  ultimately show ?thesis
    unfolding C_def complex_vector.subspace_def
    by (smt mem_Collect_eq set_plus_elim set_plus_intro)    
qed


lemma subspace_0[simp]:
  "closed_subspace ({0} :: ('a::{complex_vector,t1_space}) set)"
proof-
  have \<open>complex_vector.subspace {0}\<close>
    using add.right_neutral complex_vector.subspace_def scaleC_right.zero
    by blast    
  moreover have "closed ({0} :: 'a set)"
    by simp 
  ultimately show ?thesis 
    by (simp add: closed_subspace_def)
qed

lemma subspace_UNIV[simp]: "closed_subspace (UNIV::('a::{complex_vector,topological_space}) set)"
proof-
  have \<open>complex_vector.subspace UNIV\<close>
    by simp  
  moreover have \<open>closed UNIV\<close>
    by simp
  ultimately show ?thesis 
    unfolding closed_subspace_def by auto
qed

lemma subspace_inter[simp]:
  assumes "closed_subspace A" and "closed_subspace B"
  shows "closed_subspace (A\<inter>B)"
proof-
  obtain C where \<open>C = A \<inter> B\<close> by blast
  have \<open>complex_vector.subspace C\<close>
  proof-
    have "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> x+y\<in>C" for x y
      by (metis IntD1 IntD2 IntI \<open>C = A \<inter> B\<close> assms(1) assms(2) complex_vector.subspace_def closed_subspace_def)
    moreover have "x\<in>C \<Longrightarrow> c *\<^sub>C x \<in> C" for x c
      by (metis IntD1 IntD2 IntI \<open>C = A \<inter> B\<close> assms(1) assms(2) complex_vector.subspace_def closed_subspace_def)
    moreover have "0 \<in> C" 
      using  \<open>C = A \<inter> B\<close> assms(1) assms(2) complex_vector.subspace_def closed_subspace_def by fastforce
    ultimately show ?thesis 
      by (simp add: complex_vector.subspace_def)
  qed
  moreover have \<open>closed C\<close>
    using  \<open>C = A \<inter> B\<close>
    by (simp add: assms(1) assms(2) closed_Int closed_subspace.closed)
  ultimately show ?thesis
    using  \<open>C = A \<inter> B\<close>
    by (simp add: closed_subspace_def)
qed


lemma subspace_INF[simp]:
  "(\<And>A. A\<in>\<A> \<Longrightarrow> closed_subspace A) \<Longrightarrow> closed_subspace (\<Inter>\<A>)"
proof-
  assume \<open>\<And>A. A\<in>\<A> \<Longrightarrow> closed_subspace A\<close>
  have \<open>complex_vector.subspace (\<Inter>\<A>)\<close>
  proof -
    obtain aa :: "'a set \<Rightarrow> 'a" and cc :: "'a set \<Rightarrow> complex" where
      f1: "(\<exists>v1 v2. v1 \<in> x0 \<and> v2 *\<^sub>C v1 \<notin> x0) = (aa x0 \<in> x0 \<and> cc x0 *\<^sub>C aa x0 \<notin> x0)" for x0
      by moura
    obtain aaa :: "'a set \<Rightarrow> 'a" and aab :: "'a set \<Rightarrow> 'a" where
      "(\<exists>v1 v2. (v1 \<in> x0 \<and> v2 \<in> x0) \<and> v1 + v2 \<notin> x0)
         = ((aaa x0 \<in> x0 \<and> aab x0 \<in> x0) \<and> aaa x0 + aab x0 \<notin> x0)" for x0
      by moura
    hence f2: "(\<not> complex_vector.subspace A \<or> (\<forall>a aa. a \<notin> A \<or> aa \<notin> A \<or> a + aa \<in> A) 
      \<and> (\<forall>a c. a \<notin> A \<or> c *\<^sub>C a \<in> A) \<and> 0 \<in> A) \<and> (complex_vector.subspace A \<or> aaa A \<in> A \<and> aab A \<in> A 
      \<and> aaa A + aab A \<notin> A \<or> aa A \<in> A \<and> cc A *\<^sub>C aa A \<notin> A \<or> 0 \<notin> A)" for A
      using f1 by (metis (no_types) complex_vector.subspace_def)
    obtain AA :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x0 \<and> x1 \<notin> v2) = (AA x0 x1 \<in> x0 \<and> x1 \<notin> AA x0 x1)"
      by moura
    hence f3: "(a \<notin> \<Inter> A \<or> (\<forall>Aa. Aa \<notin> A \<or> a \<in> Aa)) \<and> (a \<in> \<Inter> A \<or> AA A a \<in> A \<and> a \<notin> AA A a)" for a A
      by auto
    have f4: " \<not> closed_subspace (A::'a set) \<or> complex_vector.subspace A" for A
      by (simp add: closed_subspace.subspace)      
    have f5: "A \<notin> \<A> \<or> closed_subspace A" for A
      using \<open>\<And>A. A \<in> \<A> \<Longrightarrow> closed_subspace A\<close> by auto      
    hence f6: "aa (\<Inter> \<A>) \<notin> \<Inter> \<A> \<or> cc (\<Inter> \<A>) *\<^sub>C aa (\<Inter> \<A>) \<in> \<Inter> \<A>"
      using f4 f3 f2 by meson
    have f7: "0 \<in> \<Inter> \<A>"
      using f5 f4 f3 f2 by meson
    have "aaa (\<Inter> \<A>) \<notin> \<Inter> \<A> \<or> aab (\<Inter> \<A>) \<notin> \<Inter> \<A> \<or> aaa (\<Inter> \<A>) + aab (\<Inter> \<A>) \<in> \<Inter> \<A>"
      using f5 f4 f3 f2 by meson
    thus ?thesis
      using f7 f6 f2 by (metis (no_types))
  qed
  moreover have \<open>closed (\<Inter>\<A>)\<close>
    by (simp add: \<open>\<And>A. A \<in> \<A> \<Longrightarrow> closed_subspace A\<close> closed_Inter closed_subspace.closed)    
  ultimately show ?thesis 
    by (simp add: closed_subspace.intro)
qed


subsection \<open>Linear space\<close>

typedef (overloaded) ('a::"{complex_vector,topological_space}") 
  linear_space = \<open>{S::'a set. closed_subspace S}\<close>
  morphisms space_as_set Abs_linear_space
  using Complex_Vector_Spaces.subspace_UNIV by blast

setup_lifting type_definition_linear_space

instantiation linear_space :: (complex_normed_vector) scaleC begin
lift_definition scaleC_linear_space :: "complex \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is
  "\<lambda>c S. (*\<^sub>C) c ` S"
  apply (rule closed_subspace.intro)
  using bounded_clinear_def  closed_subspace.subspace complex_vector.linear_subspace_image
   apply (simp add: closed_subspace.subspace complex_vector.linear_subspace_image) 
  by (simp add: closed_scaleC closed_subspace.closed)

lift_definition scaleR_linear_space :: "real \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is
  "\<lambda>c S. ((*\<^sub>R) c) ` S"
  apply (rule closed_subspace.intro)
  using bounded_clinear_def  scaleR_scaleC
   apply (simp add: scaleR_scaleC closed_subspace.subspace complex_vector.linear_subspace_image)
  by (simp add: closed_scaling closed_subspace.closed)

instance  ..  
end

instantiation linear_space :: ("{complex_vector,t1_space}") bot begin
lift_definition bot_linear_space :: \<open>'a linear_space\<close> is \<open>{0}\<close>
  by simp
instance..
end

lemma timesScalarSpace_0[simp]: "0 *\<^sub>C S = bot" for S :: "_ linear_space"
  apply transfer apply (auto intro!: exI[of _ 0])
  unfolding closed_subspace_def
  by (simp add: complex_vector.linear_subspace_image complex_vector.module_hom_zero complex_vector.subspace_0)

lemma subspace_scale_invariant: 
  fixes a S
  assumes \<open>a \<noteq> 0\<close> and \<open>closed_subspace S\<close>
  shows \<open>(*\<^sub>C) a ` S = S\<close>
proof-
  have  \<open>x \<in> (*\<^sub>C) a ` S \<Longrightarrow> x \<in> S\<close> for x
    using assms(2) closed_subspace.subspace complex_vector.subspace_scale by blast 
  moreover have  \<open>x \<in> S \<Longrightarrow> x \<in> (*\<^sub>C) a ` S\<close> for x
  proof -
    assume "x \<in> S"
    hence "\<exists>c aa. (c / a) *\<^sub>C aa \<in> S \<and> c *\<^sub>C aa = x"
      using assms(2) complex_vector.subspace_def scaleC_one
      by (metis closed_subspace.subspace) 
    hence "\<exists>aa. aa \<in> S \<and> a *\<^sub>C aa = x"
      using assms(1) by auto
    thus ?thesis by (meson image_iff)
  qed 
  ultimately show ?thesis by blast
qed


lemma timesScalarSpace_not0[simp]: "a \<noteq> 0 \<Longrightarrow> a *\<^sub>C S = S" for S :: "_ linear_space"
  apply transfer
  by (simp add: subspace_scale_invariant) 

instantiation linear_space :: ("{complex_vector,topological_space}") "top"
begin
lift_definition top_linear_space :: \<open>'a linear_space\<close> is \<open>UNIV\<close>
  by (rule Complex_Vector_Spaces.subspace_UNIV)

instance ..
end

instantiation linear_space :: ("{complex_vector,topological_space}") "Inf"
begin
lift_definition Inf_linear_space::\<open>'a linear_space set \<Rightarrow> 'a linear_space\<close>
  is \<open>\<lambda> S. \<Inter> S\<close>
proof
  show "complex_vector.subspace (\<Inter> S::'a set)"
    if "\<And>x. (x::'a set) \<in> S \<Longrightarrow> closed_subspace x"
    for S :: "'a set set"
    using that by (simp add: closed_subspace.subspace) 
  show "closed (\<Inter> S::'a set)"
    if "\<And>x. (x::'a set) \<in> S \<Longrightarrow> closed_subspace x"
    for S :: "'a set set"
    using that by (simp add: closed_subspace.closed) 
qed

instance ..
end

subsection \<open>Span\<close>

lift_definition Span :: "'a::complex_normed_vector set \<Rightarrow> 'a linear_space"
  is "\<lambda>G. closure (complex_vector.span G)"
  apply (rule closed_subspace.intro) apply (simp add: subspace_cl)
  by simp

lemma subspace_span_A:
  assumes \<open>closed_subspace S\<close> and \<open>A \<subseteq> S\<close>
  shows \<open>complex_vector.span A \<subseteq> S\<close>
  using assms
  unfolding complex_vector.span_def complex_vector.subspace_def
    hull_def closed_subspace_def complex_vector.subspace_def
  by auto

lemma subspace_span_B:
  assumes \<open>closed_subspace S\<close> and \<open>complex_vector.span A \<subseteq> S\<close>
  shows \<open>A \<subseteq> S\<close>
  using assms(2) complex_vector.span_superset by blast

lemma span_def': \<open>Span A = Inf {S. A \<subseteq> space_as_set S}\<close>
  for A::\<open>('a::cbanach) set\<close>
proof-
  have \<open>x \<in> space_as_set (Span A) 
    \<Longrightarrow> x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
    for x::'a
  proof-
    assume \<open>x \<in> space_as_set (Span A)\<close>
    hence \<open>x \<in> closure (complex_vector.span A)\<close>
      unfolding Span_def
      apply auto
      using Abs_linear_space_inverse \<open>x \<in> space_as_set (Span A)\<close> Span.rep_eq 
      by blast
    hence \<open>\<exists> y::nat \<Rightarrow> 'a. (\<forall> n. y n \<in> (complex_vector.span A)) \<and> y \<longlonglongrightarrow> x\<close>
      by (simp add: closure_sequential)
    then obtain y where \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close> and \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>y n \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S}\<close> for n
      using  \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close>
      by auto
    have \<open>x \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S}\<close> 
    proof-
      have \<open>closed_subspace S \<Longrightarrow> closed S\<close> for S::\<open>'a set\<close>
        by (simp add: closed_subspace.closed)
      hence \<open>closed ( \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S})\<close>
        by blast        
      thus ?thesis using \<open>y \<longlonglongrightarrow> x\<close>
        using \<open>\<And>n. y n \<in> \<Inter> {S. complex_vector.span A \<subseteq> S \<and> closed_subspace S}\<close> closed_sequentially 
        by blast  
    qed
    moreover have \<open>{S. A \<subseteq> S \<and> closed_subspace S} \<subseteq> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S}\<close>
      using Collect_mono_iff
      by (simp add: Collect_mono_iff subspace_span_A)  
    ultimately have \<open>x \<in> \<Inter> {S. A \<subseteq> S \<and> closed_subspace S}\<close>
      by blast     
    thus \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close> 
      apply transfer by blast
  qed
  moreover have \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S}) \<Longrightarrow> x \<in> space_as_set (Span A)\<close> 
    for x::'a
  proof-
    assume \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
    hence \<open>x \<in> \<Inter> {S. A \<subseteq> S \<and> closed_subspace S}\<close>
      apply transfer by blast
    moreover have \<open>{S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S} \<subseteq> {S. A \<subseteq> S \<and> closed_subspace S}\<close>
      using Collect_mono_iff by (simp add: Collect_mono_iff subspace_span_B) 
    ultimately have \<open>x \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S}\<close>
      by blast 
    thus \<open>x \<in> space_as_set (Span A)\<close>
      by (metis (no_types, lifting) Inter_iff space_as_set closure_subset mem_Collect_eq Span.rep_eq)      
  qed
  ultimately have \<open>space_as_set (Span A) = space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
    by blast
  thus ?thesis
    using space_as_set_inject by auto 
qed

lemma span_mult[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> span { a *\<^sub>C \<psi> } = span {\<psi>}"
  for \<psi>::"'a::complex_vector"
  by (smt Complex_Vector_Spaces.span_raw_def Diff_insert_absorb complex_vector.dependent_single complex_vector.in_span_delete complex_vector.independent_insert complex_vector.scale_eq_0_iff complex_vector.span_base complex_vector.span_redundant complex_vector.span_scale insert_absorb insert_commute insert_not_empty singletonI)

lemma subspace_I:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes \<open>complex_vector.subspace S\<close>
  shows \<open>closed_subspace (closure S)\<close>
proof-
  have "x + y \<in> closure S"
    if "x \<in> closure S"
      and "y \<in> closure S"
    for x :: 'a
      and y :: 'a
  proof-
    have \<open>\<exists> r. (\<forall> n::nat. r n \<in> S) \<and> r \<longlonglongrightarrow> x\<close>
      using closure_sequential that(1) by auto
    then obtain r where \<open>\<forall> n::nat. r n \<in> S\<close> and \<open>r \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>\<exists> s. (\<forall> n::nat. s n \<in> S) \<and> s \<longlonglongrightarrow> y\<close>
      using closure_sequential that(2) by auto
    then obtain s where \<open>\<forall> n::nat. s n \<in> S\<close> and \<open>s \<longlonglongrightarrow> y\<close>
      by blast
    have \<open>\<forall> n::nat. r n + s n \<in> S\<close>
      using \<open>\<forall>n. r n \<in> S\<close> \<open>\<forall>n. s n \<in> S\<close> assms complex_vector.subspace_add by blast 
    moreover have \<open>(\<lambda> n. r n + s n) \<longlonglongrightarrow> x + y\<close>
      by (simp add: \<open>r \<longlonglongrightarrow> x\<close> \<open>s \<longlonglongrightarrow> y\<close> tendsto_add)
    ultimately show ?thesis
      using assms that(1) that(2) by (simp add: complex_vector.subspace_add subspace_cl) 
  qed
  moreover have "c *\<^sub>C x \<in> closure S"
    if "x \<in> closure S"
    for x :: 'a and c :: complex
  proof-
    have \<open>\<exists> y. (\<forall> n::nat. y n \<in> S) \<and> y \<longlonglongrightarrow> x\<close>
      using Elementary_Topology.closure_sequential that by auto
    then obtain y where \<open>\<forall> n::nat. y n \<in> S\<close> and \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>isCont (scaleC c) x\<close>
      using continuous_at continuous_on_def isCont_scaleC by blast
    hence \<open>(\<lambda> n. scaleC c (y n)) \<longlonglongrightarrow> scaleC c x\<close>
      using  \<open>y \<longlonglongrightarrow> x\<close>
      by (simp add: isCont_tendsto_compose) 
    from  \<open>\<forall> n::nat. y n \<in> S\<close>
    have  \<open>\<forall> n::nat. scaleC c (y n) \<in> S\<close>
      using assms complex_vector.subspace_scale by auto
    thus ?thesis
      using assms that by (simp add: complex_vector.subspace_scale subspace_cl) 
  qed
  moreover have "0 \<in> closure S"
    by (metis \<open>\<And>x c. x \<in> closure S \<Longrightarrow> c *\<^sub>C x \<in> closure S\<close> all_not_in_conv assms closure_eq_empty complex_vector.scale_zero_left complex_vector.subspace_def)    
  moreover have "closed (closure S)"
    by auto
  ultimately show ?thesis
    by (simp add: \<open>\<And>x c. x \<in> closure S \<Longrightarrow> c *\<^sub>C x \<in> closure S\<close> \<open>\<And>y x. \<lbrakk>x \<in> closure S; y \<in> closure S\<rbrakk> \<Longrightarrow> x + y \<in> closure S\<close> assms closed_subspace.intro subspace_cl) 
qed

lemma bounded_linear_continuous:
  assumes \<open>bounded_clinear f\<close> 
  shows \<open>isCont f x\<close>
  using assms linear_continuous_at bounded_clinear_is_bounded_linear by auto 

lemma equal_span_0:
  fixes f::\<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close> 
    and S::\<open>'a set\<close> and x::'a
  assumes \<open>clinear f\<close> and \<open>\<forall> t \<in> S. f t = 0\<close> and xS: \<open>x \<in> complex_vector.span S\<close> 
  shows \<open>f x = 0\<close>
  using assms(1) assms(2) complex_vector.linear_eq_0_on_span xS by blast

instantiation linear_space :: ("{complex_vector,topological_space}") "order"
begin
lift_definition less_eq_linear_space :: \<open>'a linear_space \<Rightarrow> 'a linear_space \<Rightarrow> bool\<close>
  is  \<open>(\<subseteq>)\<close>.
declare less_eq_linear_space_def[code del]
lift_definition less_linear_space :: \<open>'a linear_space \<Rightarrow> 'a linear_space \<Rightarrow> bool\<close>
  is \<open>(\<subset>)\<close>.
declare less_linear_space_def[code del]
instance
proof
  show "((x::'a linear_space) < y) = (x \<le> y \<and> \<not> y \<le> x)"
    for x :: "'a linear_space"
      and y :: "'a linear_space"
    by (simp add: less_eq_linear_space.rep_eq less_le_not_le less_linear_space.rep_eq)    
  show "(x::'a linear_space) \<le> x"
    for x :: "'a linear_space"
    by (simp add: less_eq_linear_space.rep_eq)    
  show "(x::'a linear_space) \<le> z"
    if "(x::'a linear_space) \<le> y"
      and "(y::'a linear_space) \<le> z"
    for x :: "'a linear_space"
      and y :: "'a linear_space"
      and z :: "'a linear_space"
    using that less_eq_linear_space.rep_eq by auto 
  show "(x::'a linear_space) = y"
    if "(x::'a linear_space) \<le> y"
      and "(y::'a linear_space) \<le> x"
    for x :: "'a linear_space"
      and y :: "'a linear_space"
    using that by (simp add: space_as_set_inject less_eq_linear_space.rep_eq) 
qed
end


lemma bounded_sesquilinear_diff:
  \<open>bounded_sesquilinear A \<Longrightarrow> bounded_sesquilinear B \<Longrightarrow> bounded_sesquilinear (\<lambda>x y. A x y - B x y)\<close>
proof
  show "A (a + a') b - B (a + a') b = A a b - B a b + (A a' b - B a' b)"
    if "bounded_sesquilinear A" and "bounded_sesquilinear B"
    for a::'a and a'::'a and b::'b
    using that
    by (simp add: bounded_sesquilinear.axioms(1) sesquilinear.add_left)  
  show "A a (b + b') - B a (b + b') = A a b - B a b + (A a b' - B a b')"
    if "bounded_sesquilinear A" and "bounded_sesquilinear B"
    for a::'a and b::'b and b'::'b
    using that
    by (simp add: bounded_sesquilinear.axioms(1) sesquilinear.add_right)  
  show "A (r *\<^sub>C a) b - B (r *\<^sub>C a) b = r \<cdot>\<^sub>C (A a b - B a b)"
    if "bounded_sesquilinear A" and "bounded_sesquilinear B"
    for r :: complex and a::'a and b::'b
    using that
    by (simp add: bounded_sesquilinear.axioms(1) cnj_scaleC_def 
        complex_vector.scale_right_diff_distrib sesquilinear.scaleC_left)

  show "A a (r *\<^sub>C b) - B a (r *\<^sub>C b) = r *\<^sub>C (A a b - B a b)"
    if "bounded_sesquilinear A" and "bounded_sesquilinear B"
    for a :: 'a and r :: complex and b :: 'b
  proof-
    have "A a (r *\<^sub>C b) = r *\<^sub>C (A a b)"
      by (simp add: bounded_sesquilinear.axioms(1) sesquilinear.scaleC_right that(1))
    moreover have "B a (r *\<^sub>C b) = r *\<^sub>C (B a b)"
      by (simp add: bounded_sesquilinear.axioms(1) sesquilinear.scaleC_right that(2))
    ultimately have "A a (r *\<^sub>C b) - B a (r *\<^sub>C b) =  r *\<^sub>C (A a b) -  r *\<^sub>C (B a b)"
      by simp
    also have "\<dots> =  r *\<^sub>C (A a b - B a b)"
      by (simp add: complex_vector.scale_right_diff_distrib)
    finally show ?thesis by simp 
  qed
  show "\<exists>K. \<forall>a b. norm (A a b - B a b) \<le> norm a * norm b * K"
    if "bounded_sesquilinear A" and "bounded_sesquilinear B"
  proof-
    have \<open>\<exists> KA. \<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
      by (simp add: bounded_sesquilinear.bounded that(1))
    then obtain KA where \<open>\<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
      by blast
    have \<open>\<exists> KB. \<forall> a b. norm (B a b) \<le> norm a * norm b * KB\<close>
      by (simp add: bounded_sesquilinear.bounded that(2))
    then obtain KB where \<open>\<forall> a b. norm (B a b) \<le> norm a * norm b * KB\<close>
      by blast
    have \<open>norm (A a b - B a b) \<le> norm a * norm b * (KA + KB)\<close>
      for a b
    proof-
      have \<open>norm (A a b - B a b) \<le> norm (A a b) +  norm (B a b)\<close>
        by (simp add: norm_triangle_ineq4)
      also have \<open>\<dots> \<le> norm a * norm b * KA + norm a * norm b * KB\<close>
        using  \<open>\<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
          \<open>\<forall> a b. norm (B a b) \<le> norm a * norm b * KB\<close>
        using add_mono by blast
      also have \<open>\<dots>=  norm a * norm b * (KA + KB)\<close>
        by (simp add: mult.commute ring_class.ring_distribs(2))
      finally show ?thesis 
        by blast
    qed
    thus ?thesis by blast
  qed
qed

subsection \<open>Unsorted\<close>

definition is_basis :: "'a::complex_normed_vector set \<Rightarrow> bool" 
  where \<open>is_basis S = (
    (complex_vector.independent S) \<and> closure (complex_vector.span S) = UNIV
)\<close>


lemma complex_dependent_isolation:
  assumes \<open>complex_vector.dependent V\<close> and \<open>finite V\<close>
  shows \<open>\<exists>f. \<exists>s\<in>V. s = (\<Sum>v\<in>V-{s}. f v *\<^sub>C v )\<close>
proof-
  from \<open>complex_vector.dependent V\<close>
  have \<open>\<exists>T f. finite T \<and>
           T \<subseteq> V \<and> (\<Sum>i\<in>T. f i *\<^sub>C i) = 0 \<and> (\<exists>i\<in>T. f i \<noteq> 0)\<close>
    using complex_vector.dependent_explicit by blast
  hence \<open>\<exists>f. (\<Sum>i\<in>V. f i *\<^sub>C i) = 0 \<and> (\<exists> i\<in>V. f i \<noteq> 0)\<close>
    using \<open>complex_vector.dependent V\<close> \<open>finite V\<close> complex_vector.independent_if_scalars_zero by fastforce
  show \<open>\<exists>f. \<exists> s\<in>V. s = (\<Sum>v\<in>V-{s}. f v *\<^sub>C v )\<close>
  proof-
    from \<open>\<exists>f. (\<Sum>i\<in>V. f i *\<^sub>C i) = 0 \<and> (\<exists> i\<in>V. f i \<noteq> 0)\<close>
    obtain f where  \<open>(\<Sum>i\<in>V. f i *\<^sub>C i) = 0\<close> and \<open>\<exists> i\<in>V. f i \<noteq> 0\<close>
      by blast
    from \<open>\<exists>i\<in>V. f i \<noteq> 0\<close>
    obtain s where \<open>s \<in> V\<close> and \<open>f s \<noteq> 0\<close>
      by blast
    from  \<open>f s \<noteq> 0\<close>
    have  \<open>- f s \<noteq> 0\<close>
      by simp
    have \<open>(\<Sum>i\<in>V-{s}. f i *\<^sub>C i) = (- f s) *\<^sub>C s\<close>
      using \<open>s \<in> V\<close> \<open>(\<Sum>i\<in>V. f i *\<^sub>C i) = 0\<close>
      by (simp add: \<open>finite V\<close> sum_diff1)
    hence \<open>s = (\<Sum>i\<in>V-{s}. f i *\<^sub>C i) /\<^sub>C (- f s)\<close>
      using  \<open>- f s \<noteq> 0\<close> by auto
    also have \<open>(\<Sum>i\<in>V-{s}. f i *\<^sub>C i) /\<^sub>C (- f s) = (\<Sum>i\<in>V-{s}. ((f i) /\<^sub>C (- f s)) *\<^sub>C i)\<close>
      using Complex_Vector_Spaces.complex_vector.scale_sum_right
        [where f = "(\<lambda> i. f i *\<^sub>C i)" and A = "V - {s}" and a = "inverse (- f s)"]
      by auto
    finally have \<open>s = (\<Sum>i\<in>V-{s}. ((f i) /\<^sub>C (- f s)) *\<^sub>C i)\<close>
      by blast
    thus ?thesis 
      using \<open>s \<in> V\<close> 
      by metis
  qed
qed

definition cbilinear :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector) \<Rightarrow> bool\<close>
  where \<open>cbilinear \<equiv> (\<lambda>f. (\<forall> y. clinear (\<lambda> x. f x y)) \<and> (\<forall> x. clinear (\<lambda> y. f x y)) )\<close>

lemma cbilinear_from_product_clinear:
  fixes g' :: \<open>'a::complex_vector \<Rightarrow> complex\<close> and g::\<open>'b::complex_vector \<Rightarrow> complex\<close>
  assumes \<open>\<And> x y. h x y = (g' x)*(g y)\<close> and \<open>clinear g\<close> and \<open>clinear g'\<close>
  shows \<open>cbilinear h\<close>
  unfolding cbilinear_def proof
  show "\<forall>y. clinear (\<lambda>x. h x y)"
  proof
    show "clinear (\<lambda>x. h x y)"
      for y :: 'b
      unfolding clinear_def proof
      show "h (b1 + b2) y = h b1 y + h b2 y"
        for b1 :: 'a
          and b2 :: 'a
      proof-
        have \<open>h (b1 + b2) y = g' (b1 + b2) * g y\<close>
          using \<open>\<And> x y. h x y = (g' x)*(g y)\<close>
          by auto
        also have \<open>\<dots> = (g' b1 + g' b2) * g y\<close>
          using \<open>clinear g'\<close>
          unfolding clinear_def
          by (simp add: assms(3) complex_vector.linear_add)
        also have \<open>\<dots> = g' b1 * g y + g' b2 * g y\<close>
          by (simp add: ring_class.ring_distribs(2))
        also have \<open>\<dots> = h b1 y + h b2 y\<close>
          using assms(1) by auto          
        finally show ?thesis by blast
      qed
      show "h (r *\<^sub>C b) y = r *\<^sub>C h b y"
        for r :: complex
          and b :: 'a
      proof-
        have \<open>h (r *\<^sub>C b) y = g' (r *\<^sub>C b) * g y\<close>
          by (simp add: assms(1))
        also have \<open>\<dots> = r *\<^sub>C (g' b * g y)\<close>
          by (simp add: assms(3) complex_vector.linear_scale)
        also have \<open>\<dots> = r *\<^sub>C (h b y)\<close>
          by (simp add: assms(1))          
        finally show ?thesis by blast
      qed
    qed
  qed
  show "\<forall>x. clinear (h x)"
    unfolding clinear_def proof
    show "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) (h x)"
      for x :: 'a
    proof
      show "h x (b1 + b2) = h x b1 + h x b2"
        for b1 :: 'b
          and b2 :: 'b
      proof-
        have \<open>h x (b1 + b2)  = g' x * g (b1 + b2)\<close>
          using \<open>\<And> x y. h x y = (g' x)*(g y)\<close>
          by auto
        also have \<open>\<dots> = g' x * (g b1 + g b2)\<close>
          using \<open>clinear g'\<close>
          unfolding clinear_def
          by (simp add: assms(2) complex_vector.linear_add)
        also have \<open>\<dots> = g' x * g b1 + g' x * g b2\<close>
          by (simp add: ring_class.ring_distribs(1))
        also have \<open>\<dots> = h x b1 + h x b2\<close>
          using assms(1) by auto          
        finally show ?thesis by blast
      qed

      show "h x (r *\<^sub>C b) = r *\<^sub>C h x b"
        for r :: complex
          and b :: 'b
      proof-
        have \<open>h x (r *\<^sub>C b) =  g' x * g (r *\<^sub>C b)\<close>
          by (simp add: assms(1))
        also have \<open>\<dots> = r *\<^sub>C (g' x * g b)\<close>
          by (simp add: assms(2) complex_vector.linear_scale)
        also have \<open>\<dots> = r *\<^sub>C (h x b)\<close>
          by (simp add: assms(1))          
        finally show ?thesis by blast
      qed
    qed
  qed
qed

lemma bilinear_Kronecker_delta:
  fixes u::\<open>'a::complex_vector\<close> and v::\<open>'b::complex_vector\<close>
  assumes \<open>complex_vector.independent A\<close> and \<open>complex_vector.independent B\<close> and \<open>u \<in> A\<close> and \<open>v \<in> B\<close>
  shows \<open>\<exists> h::_\<Rightarrow>_\<Rightarrow>complex. cbilinear h \<and> (h u v = 1) \<and> (\<forall>x\<in>A. \<forall>y\<in>B. (x,y) \<noteq> (u,v) \<longrightarrow> h x y = 0)\<close>
proof-
  define f where \<open>f x = (if x = v then (1::complex) else 0)\<close> for x
  have \<open>\<exists>g. clinear g \<and> (\<forall>x\<in>B. g x = f x)\<close>
    using \<open>complex_vector.independent B\<close> complex_vector.linear_independent_extend
    by (simp add: complex_vector.linear_independent_extend Complex_Vector_Spaces.dependent_raw_def) 
  then obtain g where \<open>clinear g\<close> and \<open>\<forall>x\<in>B. g x = f x\<close>
    by blast
  define f' where \<open>f' x = (if x = u then (1::complex) else 0)\<close> for x
  hence \<open>\<exists>g'. clinear g' \<and> (\<forall>x\<in>A. g' x = f' x)\<close>
    by (simp add: Complex_Vector_Spaces.dependent_raw_def assms(1) complex_vector.linear_independent_extend)    
  then obtain g' where \<open>clinear g'\<close> and \<open>\<forall>x\<in>A. g' x = f' x\<close>
    by blast
  define h where \<open>h x y = (g' x)*(g y)\<close> for x y
  have \<open>cbilinear h\<close>
    by (simp add: \<open>clinear g'\<close> \<open>clinear g\<close> cbilinear_from_product_clinear h_def)
  moreover have \<open>h u v = 1\<close>
  proof-
    have \<open>g' u = 1\<close>
    proof-
      have \<open>g' u = f' u\<close>
        using \<open>u \<in> A\<close> by (simp add: \<open>\<forall>x\<in>A. g' x = f' x\<close>)
      also have \<open>\<dots> = 1\<close>
        by (simp add: f'_def)
      finally show ?thesis by blast
    qed
    moreover have \<open>g v = 1\<close>
    proof-
      have \<open>g v = f v\<close>
        using \<open>v \<in> B\<close> by (simp add: \<open>\<forall>x\<in>B. g x = f x\<close>)
      also have \<open>\<dots> = 1\<close>
        by (simp add: f_def)
      finally show ?thesis by blast
    qed
    ultimately show ?thesis unfolding h_def by auto
  qed
  moreover have \<open>x\<in>A \<Longrightarrow> y\<in>B \<Longrightarrow> (x,y) \<noteq> (u,v) \<Longrightarrow> h x y = 0\<close> for x y
  proof-
    assume \<open>x\<in>A\<close> and \<open>y\<in>B\<close> and \<open>(x,y) \<noteq> (u,v)\<close>
    from \<open>(x,y) \<noteq> (u,v)\<close>
    have \<open>x \<noteq> u \<or> y \<noteq> v\<close>
      by simp
    moreover have \<open>x \<noteq> u \<Longrightarrow> h x y = 0\<close>
    proof-
      assume \<open>x \<noteq> u\<close>
      hence \<open>g' x = 0\<close>
        by (simp add: \<open>\<forall>x\<in>A. g' x = f' x\<close> \<open>x \<in> A\<close> f'_def)
      thus ?thesis
        by (simp add: \<open>h \<equiv> \<lambda>x y. g' x * g y\<close>) 
    qed
    moreover have \<open>y \<noteq> v \<Longrightarrow> h x y = 0\<close>
    proof-
      assume \<open>y \<noteq> v\<close>
      hence \<open>g y = 0\<close>
        using \<open>\<forall>x\<in>B. g x = f x\<close> \<open>y \<in> B\<close> f_def by auto
      thus ?thesis
        by (simp add: \<open>h \<equiv> \<lambda>x y. g' x * g y\<close>) 
    qed
    ultimately show ?thesis by blast
  qed
  ultimately show ?thesis 
    by blast
qed

lemma span_finite:
  assumes \<open>z\<in>complex_vector.span T\<close>
  shows \<open>\<exists>S. finite S \<and> S \<subseteq> T \<and> z\<in>complex_vector.span S\<close>
proof-
  have \<open>\<exists>S r. finite S \<and> S \<subseteq> T \<and> z = (\<Sum>a\<in>S. r a *\<^sub>C a)\<close>
    using complex_vector.span_explicit[where b = "T"]
      assms by auto
  then obtain S r where \<open>finite S\<close> and \<open>S \<subseteq> T\<close> and \<open>z = (\<Sum>a\<in>S. r a *\<^sub>C a)\<close>
    by blast
  thus ?thesis by (meson complex_vector.span_scale complex_vector.span_sum 
        complex_vector.span_superset subset_iff) 
qed

lemma span_explicit_finite:
  assumes \<open>complex_vector.span S = UNIV\<close> and \<open>complex_vector.independent S\<close> and \<open>finite S\<close>
  shows \<open>\<exists>t. x = (\<Sum>s\<in>S. t s *\<^sub>C s)\<close>
proof-
  have \<open>x \<in> complex_vector.span S\<close>
    using \<open>complex_vector.span S = UNIV\<close> by blast
  hence \<open>\<exists> T t'. finite T \<and> T \<subseteq> S \<and> x = (\<Sum>s\<in>T. t' s *\<^sub>C s)\<close>
    using complex_vector.span_explicit[where b = S] by auto
  then obtain T t' where \<open>finite T\<close> and \<open>T \<subseteq> S\<close> and
    \<open>x = (\<Sum>s\<in>T. t' s *\<^sub>C s)\<close>
    by blast
  define t where \<open>t s = (if s\<in>T then t' s else 0)\<close> for s
  have \<open>(\<Sum>s\<in>T. t s *\<^sub>C s) + (\<Sum>s\<in>S-T. t s *\<^sub>C s)
    = (\<Sum>s\<in>S. t s *\<^sub>C s)\<close>
    using \<open>T \<subseteq> S\<close>
    by (metis (no_types, lifting) add.commute assms(3) sum.subset_diff)    
  moreover have \<open>(\<Sum>s\<in>S-T. t s *\<^sub>C s) = 0\<close>
  proof-
    have \<open>s\<in>S-T \<Longrightarrow> t s *\<^sub>C s = 0\<close> for s
    proof-
      assume \<open>s\<in>S-T\<close>
      hence \<open>t s = 0\<close>
        unfolding t_def by auto
      thus ?thesis by auto
    qed
    thus ?thesis
      by (simp add: sum.neutral) 
  qed
  ultimately have \<open>x = (\<Sum>s\<in>S. t s *\<^sub>C s)\<close>
    using \<open>x = (\<Sum>s\<in>T. t' s *\<^sub>C s)\<close> t_def by auto
  thus ?thesis by blast
qed


lemma linear_space_leI:
  assumes "\<And>x. x \<in> space_as_set A \<Longrightarrow> x \<in> space_as_set B"
  shows "A \<le> B"
  using assms apply transfer by auto

lemma finite_sum_tendsto:
  fixes A::\<open>'a set\<close> and r :: "'a \<Rightarrow> nat \<Rightarrow> 'b::{comm_monoid_add,topological_monoid_add}"
  assumes  \<open>\<And>a. a \<in> A \<Longrightarrow> r a \<longlonglongrightarrow> \<phi> a\<close> and \<open>finite A\<close>
  shows \<open>(\<lambda>n. (\<Sum>a\<in>A. r a n)) \<longlonglongrightarrow>  (\<Sum>a\<in>A. \<phi> a)\<close>
  apply (insert assms(1)) using \<open>finite A\<close>
    (* Ask to Dominique: how to make this proof more elegant *)
proof induction
  case empty show \<open>(\<lambda>n. \<Sum>a\<in>{}. r a n) \<longlonglongrightarrow> sum \<phi> {}\<close> by auto
next
  case (insert x F)
  hence "r x \<longlonglongrightarrow> \<phi> x" and "(\<lambda>n. \<Sum>a\<in>F. r a n) \<longlonglongrightarrow> sum \<phi> F"
    by auto
  hence "(\<lambda>n. r x n + (\<Sum>a\<in>F. r a n)) \<longlonglongrightarrow> \<phi> x + sum \<phi> F"
    using tendsto_add by blast
  thus \<open>(\<lambda>n. \<Sum>a\<in>insert x F. r a n) \<longlonglongrightarrow> sum \<phi> (insert x F)\<close> using sum.insert insert by auto
qed

unbundle no_notation_norm

end
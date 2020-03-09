(*  Title:      Complexes_Vector_Spaces.thy
    Author:     Dominique Unruh (University of Tartu)
    Author:     Jose Manuel Rodriguez Caballero (University of Tartu)
*)

section \<open>Vector Spaces and Algebras over the Complex\<close>

theory Complex_Vector_Spaces

imports 
  "HOL-ex.Sketch_and_Explore"
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

subsection \<open>Bounded Linear and Bilinear Operators\<close>

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

lemma pos_bounded': "\<exists>K>0. \<forall>x. norm (f x) \<le> norm x * K"
proof -
  obtain K where K: "\<And>x. norm (f x) \<le> norm x * K"
    using bounded' by blast
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

lemma nonneg_bounded': "\<exists>K\<ge>0. \<forall>x. norm (f x) \<le> norm x * K"
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
  

locale bounded_sesquilinear =
  fixes prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
    (infixl "**" 70)
  assumes add_left: "(a + a') ** b = a ** b + a' ** b"
    and add_right: "a ** (b + b') = a ** b + a ** b'"
    and scaleC_left: "(r *\<^sub>C a) ** b = r \<cdot>\<^sub>C (a ** b)"
    and scaleC_right: "a ** (r *\<^sub>C b) = r *\<^sub>C (a ** b)"
    and bounded: "\<exists>K. \<forall>a b. norm (a ** b) \<le> norm a * norm b * K"
begin

lemma pos_bounded: "\<exists>K>0. \<forall>a b. \<parallel>a ** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
proof -
  obtain K where "\<And>a b. \<parallel>a ** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
    using bounded by blast
  hence "\<parallel>a ** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * (max 1 K)" for a b
    by (rule order.trans) (simp add: mult_left_mono)
  thus ?thesis by force
qed

lemma nonneg_bounded: "\<exists>K\<ge>0. \<forall>a b. \<parallel>a ** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
  using pos_bounded by (auto intro: order_less_imp_le)

lemma additive_right: "additive (\<lambda>b. a ** b)"
  by (rule additive.intro, rule add_right)

lemma additive_left: "additive (\<lambda>a. a ** b)"
  by (rule additive.intro, rule add_left)

lemma zero_left: "0 ** b = 0"
  by (rule additive.zero [OF additive_left])

lemma zero_right: "a ** 0 = 0"
  by (rule additive.zero [OF additive_right])

lemma minus_left: "(- a) ** b = - (a ** b)"
  by (rule additive.minus [OF additive_left])

lemma minus_right: "a ** (- b) = - (a ** b)"
  by (rule additive.minus [OF additive_right])

lemma diff_left: "(a - a') ** b = a ** b - a' ** b"
  by (rule additive.diff [OF additive_left])

lemma diff_right: "a ** (b - b') = a ** b - a ** b'"
  by (rule additive.diff [OF additive_right])

lemma sum_left: "(sum g S) ** x = sum ((\<lambda>i. (g i) ** x)) S"
  by (rule additive.sum [OF additive_left])

lemma sum_right: "x ** (sum g S) = sum ((\<lambda>i. (x ** (g i)))) S"
  by (rule additive.sum [OF additive_right])

lemma bounded_clinear_left: "bounded_antilinear (\<lambda>a. a ** b)"
proof -
  obtain K where "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    using pos_bounded by blast
  thus ?thesis
    by (rule_tac K="norm b * K" in bounded_antilinear_intro)
       (auto simp: algebra_simps scaleC_left add_left)
qed

lemma bounded_clinear_right: "bounded_clinear (\<lambda>b. a ** b)"
proof -
  obtain K where "\<And>a b. norm (a ** b) \<le> norm a * norm b * K"
    using pos_bounded by blast
  thus ?thesis
    by (rule_tac K="norm a * K" in bounded_clinear_intro) 
       (auto simp: algebra_simps scaleC_right add_right)
qed

lemma prod_diff_prod: "(x ** y - a ** b) = (x - a) ** (y - b) + (x - a) ** b + a ** (y - b)"
  by (simp add: diff_left diff_right)

lemma comp1:
  assumes a1: "bounded_clinear g"
  shows "bounded_sesquilinear (\<lambda>x. (**) (g x))"
proof
  show "g (a + a') ** b = g a ** b + g a' ** b"
    for a :: 'd
      and a' :: 'd
      and b :: 'b
  proof-
    have \<open>g (a + a') = g a + g a'\<close>
      using a1 bounded_clinear.axioms(1) complex_vector.linear_add by auto 
    thus ?thesis by (simp add: add_left)     
  qed
  show "g a ** (b + b') = g a ** b + g a ** b'"
    for a :: 'd
      and b :: 'b
      and b' :: 'b
    by (simp add: add_right)

  show "g (r *\<^sub>C a) ** b = r \<cdot>\<^sub>C (g a ** b)"
    for r :: complex
      and a :: 'd
      and b :: 'b
  proof-
    have \<open>g (r *\<^sub>C a) = r *\<^sub>C g a\<close>
      by (simp add: a1 bounded_clinear.axioms(1) complex_vector.linear_scale)
    thus ?thesis by (simp add: scaleC_left) 
  qed
  show "g a ** (r *\<^sub>C b) = r *\<^sub>C (g a ** b)"
    for a :: 'd
      and r :: complex
      and b :: 'b
    by (simp add: scaleC_right)    
  show "\<exists>K. \<forall>a b. \<parallel>g a ** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
  proof-
    have \<open>\<exists>N. \<forall>a. \<parallel>g a\<parallel> \<le> \<parallel>a\<parallel> * N \<and> N \<ge> 0\<close>
      using assms bounded_clinear.nonneg_bounded by blast      
    then obtain N where n0: \<open>N \<ge> 0\<close> and n1: \<open>\<parallel>g a\<parallel> \<le> \<parallel>a\<parallel> * N\<close> for a
      by blast
    have \<open>\<exists>M. \<forall>a b. \<parallel>a ** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * M \<and> M \<ge> 0\<close>
      using nonneg_bounded by blast      
    then obtain M where m0: \<open>M \<ge> 0\<close> and m1: \<open>\<parallel>a ** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * M\<close> for a b
      by blast
    define K where \<open>K = N * M\<close>
    have \<open>\<parallel>g a ** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K\<close> for a b
    proof-
      have \<open>\<parallel>g a ** b\<parallel> \<le> \<parallel>g a\<parallel> * \<parallel>b\<parallel> * M\<close>
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
qed

lemma comp2:
  assumes a1: "bounded_clinear g"
  shows "bounded_sesquilinear (\<lambda>y. \<lambda>x. y ** (g x))"
  proof
  show "(a + a') ** g b = a ** g b + a' ** g b"
    for a :: 'a
      and a' :: 'a
      and b :: 'd
    by (simp add: add_left)
    
  show "a ** g (b + b') = a ** g b + a ** g b'"
    for a :: 'a
      and b :: 'd
      and b' :: 'd
  proof-
    have \<open>g (b + b') = g b + g b'\<close>
      using a1 bounded_clinear.axioms(1) complex_vector.linear_add by auto 
    thus ?thesis by (simp add: add_right)     
  qed

  show "r *\<^sub>C a ** g b = r \<cdot>\<^sub>C (a ** g b)"
    for r :: complex
      and a :: 'a
      and b :: 'd
    by (simp add: scaleC_left)

  show "a ** g (r *\<^sub>C b) = r *\<^sub>C (a ** g b)"
    for a :: 'a
      and r :: complex
      and b :: 'd
      proof-
    have \<open>g (r *\<^sub>C b) = r *\<^sub>C g b\<close>
      by (simp add: a1 bounded_clinear.axioms(1) complex_vector.linear_scale)
    thus ?thesis by (simp add: scaleC_right) 
  qed

  show "\<exists>K. \<forall>a b. \<parallel>a ** g b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K"
  proof-
    have \<open>\<exists>N. \<forall>a. \<parallel>g a\<parallel> \<le> \<parallel>a\<parallel> * N \<and> N \<ge> 0\<close>
      using assms bounded_clinear.nonneg_bounded by blast      
    then obtain N where n0: \<open>N \<ge> 0\<close> and n1: \<open>\<parallel>g a\<parallel> \<le> \<parallel>a\<parallel> * N\<close> for a
      by blast
    have \<open>\<exists>M. \<forall>a b. \<parallel>a ** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * M \<and> M \<ge> 0\<close>
      using nonneg_bounded by blast      
    then obtain M where m0: \<open>M \<ge> 0\<close> and m1: \<open>\<parallel>a ** b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * M\<close> for a b
      by blast
    define K where \<open>K = N * M\<close>
    have \<open>\<parallel>a ** g b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>b\<parallel> * K\<close> for a b
    proof-
      have \<open>\<parallel>a ** g b\<parallel> \<le> \<parallel>a\<parallel> * \<parallel>g b\<parallel> * M\<close>
        using m1 by blast
      also have \<open>\<dots> \<le> \<parallel>a\<parallel> * (\<parallel>b\<parallel> * N) * M\<close>
        using n0 n1 m0
        by (smt mult_right_less_imp_less norm_ge_zero 
            ordered_comm_semiring_class.comm_mult_left_mono)
      finally show ?thesis by (simp add: K_def)
    qed
    thus ?thesis by auto 
  qed
qed


lemma comp: "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_sesquilinear (\<lambda>x y. f x ** g y)"
  using comp1 comp2 bounded_sesquilinear.comp2 by auto 
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

lemma bounded_clinear_sub: "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_clinear (\<lambda>x. f x - g x)"
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



unbundle no_notation_norm



end
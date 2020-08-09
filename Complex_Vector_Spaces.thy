section \<open>Complex Vector Spaces\<close>

(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)

theory Complex_Vector_Spaces
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL-Analysis.Elementary_Topology"
    "HOL-Analysis.Operator_Norm"
    "HOL-Analysis.Elementary_Normed_Spaces"
    "HOL-Library.Set_Algebras"
    Preliminaries
begin

bundle notation_norm begin
notation norm ("\<parallel>_\<parallel>")
end

subsection \<open>Complex vector spaces\<close>

class scaleC = scaleR +
  fixes scaleC :: "complex \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "*\<^sub>C" 75)
  assumes scaleR_scaleC: "scaleR r = scaleC (complex_of_real r)"
begin

abbreviation divideC :: "'a \<Rightarrow> complex \<Rightarrow> 'a"  (infixl "'/\<^sub>C" 70)
  where "x /\<^sub>C c \<equiv> scaleC (inverse c) x"

lemma scaleC_real: assumes "r\<in>\<real>" shows "r *\<^sub>C x = Re r *\<^sub>R x"
  unfolding scaleR_scaleC using assms by simp

end

class complex_vector = scaleC + ab_group_add +
  assumes scaleC_add_right: "a *\<^sub>C (x + y) = (a *\<^sub>C x) + (a *\<^sub>C y)"
    and scaleC_add_left: "(a + b) *\<^sub>C x = (a *\<^sub>C x) + (b *\<^sub>C x)"
    and scaleC_scaleC[simp]: "a *\<^sub>C (b *\<^sub>C x) =  (a * b) *\<^sub>C x"
    and scaleC_one[simp]: "1 *\<^sub>C x = x"

(*
(* TODO remove (nothing like that in Real_Vector_Spaces) *)
(* Jose: I find errors when I remove it *)
interpretation complex_vector: vector_space "scaleC :: complex \<Rightarrow> 'a \<Rightarrow> 'a::complex_vector"
  apply unfold_locales
     apply (rule scaleC_add_right)
    apply (rule scaleC_add_left)
   apply (rule scaleC_scaleC)
  by (rule scaleC_one)
*)

subclass (in complex_vector) real_vector
  by (standard, simp_all add: scaleR_scaleC scaleC_add_right scaleC_add_left)

class complex_algebra = complex_vector + ring +
  assumes mult_scaleC_left [simp]: "scaleC a x * y = scaleC a (x * y)"
    and mult_scaleC_right [simp]: "x * scaleC a y = scaleC a (x * y)"

subclass (in complex_algebra) real_algebra
  by (standard, simp_all add: scaleR_scaleC)

class complex_algebra_1 = complex_algebra + ring_1

subclass (in complex_algebra_1) real_algebra_1 ..

class complex_div_algebra = complex_algebra_1 + division_ring

subclass (in complex_div_algebra) real_div_algebra ..

class complex_field = complex_div_algebra + field

subclass (in complex_field) real_field ..

instantiation complex :: scaleC
begin
definition complex_scaleC_def [simp]: "scaleC = (*)"
instance 
  apply intro_classes
  apply (rule ext)
  by (simp add: scaleR_conv_of_real)
end

instantiation complex :: complex_field
begin
instance
  apply intro_classes
  by (simp_all add: algebra_simps scaleR_scaleC)
end

subsection \<open>Bounded Linear and Bilinear Operators\<close>

definition clinear::\<open>('a::complex_vector \<Rightarrow>'b'::complex_vector) \<Rightarrow> bool\<close> where
  "clinear f =  Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) f"

global_interpretation complex_vector?: vector_space "scaleC :: complex \<Rightarrow> 'a \<Rightarrow> 'a::complex_vector"
  rewrites "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    and "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
  defines dependent_raw_def: dependent = complex_vector.dependent
    and representation_raw_def: representation = complex_vector.representation
    and subspace_raw_def: subspace = complex_vector.subspace
    and span_raw_def: span = complex_vector.span
    and extend_basis_raw_def: extend_basis = complex_vector.extend_basis
    and dim_raw_def: dim = complex_vector.dim
  apply (simp add: scaleC_add_left scaleC_add_right vector_space_def)    
  unfolding clinear_def
  by auto

hide_const (open)\<comment> \<open>locale constants\<close>
  complex_vector.dependent
  complex_vector.independent
  complex_vector.representation
  complex_vector.subspace
  complex_vector.span
  complex_vector.extend_basis
  complex_vector.dim

abbreviation complex_independent where "complex_independent x \<equiv> \<not> complex_vector.dependent x"


global_interpretation complex_vector?: vector_space_pair "scaleC::_\<Rightarrow>_\<Rightarrow>'a::complex_vector" "scaleC::_\<Rightarrow>_\<Rightarrow>'b::complex_vector"
  rewrites  "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    and "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
  defines construct_raw_def: construct = complex_vector.construct
    apply unfold_locales
  unfolding clinear_def
  by auto

hide_const (open)\<comment> \<open>locale constants\<close>
  complex_vector.construct

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
  apply (cases "a = 0")
   apply simp
  apply (cases "x = 0")
   apply simp
  by (erule (1) nonzero_inverse_scaleC_distrib)


lemma sum_constant_scaleC: "(\<Sum>x\<in>A. y) = of_nat (card A) *\<^sub>C y"
  for y :: "'a::complex_vector"
  by (induct A rule: infinite_finite_induct) (simp_all add: algebra_simps)

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
  by (simp_all add: divide_inverse_commute scaleC_add_right complex_vector.scale_right_diff_distrib)

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

lemma of_complex_eq_iff [simp]: "of_complex x = of_complex y \<longleftrightarrow> x = y"
  by (simp add: of_complex_def)

lemma inj_of_complex: "inj of_complex"
  by (auto intro: injI)

lemmas of_complex_eq_0_iff [simp] = of_complex_eq_iff [of _ 0, simplified]
lemmas of_complex_eq_1_iff [simp] = of_complex_eq_iff [of _ 1, simplified]

lemma of_complex_eq_id [simp]: "of_complex = (id :: complex \<Rightarrow> complex)"
  by (rule ext) (simp add: of_complex_def)

text \<open>Collapse nested embeddings.\<close>
lemma of_complex_of_nat_eq [simp]: "of_complex (of_nat n) = of_nat n"
  by (induct n) auto

lemma of_complex_of_real_eq [simp]: "of_complex (of_real n) = of_real n"
  unfolding of_complex_def of_real_def unfolding scaleR_scaleC by simp

lemma of_complex_of_int_eq [simp]: "of_complex (of_int z) = of_int z"
  by (cases z rule: int_diff_cases) simp

lemma of_complex_numeral [simp]: "of_complex (numeral w) = numeral w"
  using of_complex_of_int_eq [of "numeral w"] by simp

lemma of_complex_neg_numeral [simp]: "of_complex (- numeral w) = - numeral w"
  using of_complex_of_int_eq [of "- numeral w"] by simp

text \<open>Every complex algebra has characteristic zero.\<close>
instance complex_algebra_1 < ring_char_0 ..

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


subsection \<open>The Set of Complex Numbers\<close>

definition Complexs :: "'a::complex_algebra_1 set"  ("\<complex>")
  where "\<complex> = range of_complex"

lemma Complexs_of_complex [simp]: "of_complex r \<in> \<complex>"
  by (simp add: Complexs_def)

lemma Complexs_of_real [simp]: "of_real r \<in> \<complex>"
  unfolding Complexs_def of_real_def of_complex_def 
  apply (subst scaleR_scaleC) by simp

lemma Reals_in_Complexs: "\<real> \<subseteq> \<complex>"
  unfolding Reals_def by auto

lemma Complexs_of_int [simp]: "of_int z \<in> \<complex>"
  by (subst of_complex_of_int_eq [symmetric], rule Complexs_of_complex)

lemma Complexs_of_nat [simp]: "of_nat n \<in> \<complex>"
  by (subst of_complex_of_nat_eq [symmetric], rule Complexs_of_complex)

lemma Complexs_numeral [simp]: "numeral w \<in> \<complex>"
  by (subst of_complex_numeral [symmetric], rule Complexs_of_complex)

lemma Complexs_0 [simp]: "0 \<in> \<complex>"
  apply (unfold Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_0 [symmetric])

lemma Complexs_1 [simp]: "1 \<in> \<complex>"
  apply (unfold Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_1 [symmetric])


lemma Complexs_add [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a + b \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_add [symmetric])


lemma Complexs_minus [simp]: "a \<in> \<complex> \<Longrightarrow> - a \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_minus [symmetric])


lemma Complexs_diff [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a - b \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_diff [symmetric])


lemma Complexs_mult [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a * b \<in> \<complex>"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_mult [symmetric])


lemma nonzero_Complexs_inverse: "a \<in> \<complex> \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> inverse a \<in> \<complex>"
  for a :: "'a::complex_div_algebra"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (erule nonzero_of_complex_inverse [symmetric])


lemma Complexs_inverse: "a \<in> \<complex> \<Longrightarrow> inverse a \<in> \<complex>"
  for a :: "'a::{complex_div_algebra,division_ring}"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_inverse [symmetric])


lemma Complexs_inverse_iff [simp]: "inverse x \<in> \<complex> \<longleftrightarrow> x \<in> \<complex>"
  for x :: "'a::{complex_div_algebra,division_ring}"
  by (metis Complexs_inverse inverse_inverse_eq)

lemma nonzero_Complexs_divide: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a / b \<in> \<complex>"
  for a b :: "'a::complex_field"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (erule nonzero_of_complex_divide [symmetric])


lemma Complexs_divide [simp]: "a \<in> \<complex> \<Longrightarrow> b \<in> \<complex> \<Longrightarrow> a / b \<in> \<complex>"
  for a b :: "'a::{complex_field,field}"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_divide [symmetric])


lemma Complexs_power [simp]: "a \<in> \<complex> \<Longrightarrow> a ^ n \<in> \<complex>"
  for a :: "'a::complex_algebra_1"
  apply (auto simp add: Complexs_def)
  apply (rule range_eqI)
  by (rule of_complex_power [symmetric])


lemma Complexs_cases [cases set: Complexs]:
  assumes "q \<in> \<complex>"
  obtains (of_complex) r where "q = of_complex r"
  unfolding Complexs_def
proof -
  from \<open>q \<in> \<complex>\<close> have "q \<in> range of_complex" unfolding Complexs_def .
  then obtain r where "q = of_complex r" ..
  thus thesis ..
qed

lemma sum_in_Complexs [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<complex>) \<Longrightarrow> sum f s \<in> \<complex>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  thus ?case by (metis Complexs_0 sum.infinite)
qed simp_all

lemma prod_in_Complexs [intro,simp]: "(\<And>i. i \<in> s \<Longrightarrow> f i \<in> \<complex>) \<Longrightarrow> prod f s \<in> \<complex>"
proof (induct s rule: infinite_finite_induct)
  case infinite
  thus ?case by (metis Complexs_1 prod.infinite)
qed simp_all

lemma Complexs_induct [case_names of_complex, induct set: Complexs]:
  "q \<in> \<complex> \<Longrightarrow> (\<And>r. P (of_complex r)) \<Longrightarrow> P q"
  by (rule Complexs_cases) auto

subsection \<open>Ordered complex vector spaces\<close>

class ordered_complex_vector = complex_vector + ordered_ab_group_add +
  assumes scaleC_left_mono: "x \<le> y \<Longrightarrow> 0 \<le> a \<Longrightarrow> a *\<^sub>C x \<le> a *\<^sub>C y"
    and scaleC_right_mono: "a \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> b *\<^sub>C x"
begin

subclass ordered_real_vector
  apply standard unfolding scaleR_scaleC 
   apply (rule scaleC_left_mono) apply auto[2] 
  apply (rule scaleC_right_mono) by auto

lemma scaleC_mono: "a \<le> b \<Longrightarrow> x \<le> y \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> x \<Longrightarrow> a *\<^sub>C x \<le> b *\<^sub>C y"
  apply (erule scaleC_right_mono [THEN order_trans])
   apply assumption
  apply (erule scaleC_left_mono)
  by assumption


lemma scaleC_mono': "a \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> 0 \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> a *\<^sub>C c \<le> b *\<^sub>C d"
  by (rule scaleC_mono) (auto intro: order.trans)

lemma pos_le_divideRI:
  assumes "0 < c"
    and "c *\<^sub>C a \<le> b"
  shows "a \<le> b /\<^sub>C c"
proof -
  have "a = inverse c *\<^sub>C c *\<^sub>C a" using assms(1) by auto
  also have "\<dots> \<le> inverse c *\<^sub>C b"
    apply (rule scaleC_left_mono) using assms by auto
  finally show ?thesis by simp
qed

lemma pos_le_divideR_eq:
  assumes "0 < c"
  shows "a \<le> b /\<^sub>C c \<longleftrightarrow> c *\<^sub>C a \<le> b"
    (is "?lhs \<longleftrightarrow> ?rhs")
proof -
  have "0 \<noteq> c"
    using assms by blast
  thus ?thesis
    using assms local.pos_le_divideRI local.scaleC_left_mono preorder_class.less_imp_le by fastforce
qed

lemma scaleC_image_atLeastAtMost: "c > 0 \<Longrightarrow> scaleC c ` {x..y} = {c *\<^sub>C x..c *\<^sub>C y}"
  apply (auto intro!: scaleC_left_mono)
  apply (rule_tac x = "inverse c *\<^sub>C xa" in image_eqI)
  by (simp_all add: pos_le_divideR_eq[symmetric])

end

lemma neg_le_divideR_eq:
  fixes a :: "'a :: ordered_complex_vector"
  assumes "c < 0"
  shows "a \<le> b /\<^sub>C c \<longleftrightarrow> b \<le> c *\<^sub>C a"
  using pos_le_divideR_eq [of "-c" a "-b"] assms by simp

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
  by (auto simp add: scaleC_nonneg_nonpos scaleC_nonpos_nonneg)

lemma le_add_iff1: "a *\<^sub>C e + c \<le> b *\<^sub>C e + d \<longleftrightarrow> (a - b) *\<^sub>C e + c \<le> d"
  for c d e :: "'a::ordered_complex_vector"
  by (simp add: algebra_simps)

lemma le_add_iff2: "a *\<^sub>C e + c \<le> b *\<^sub>C e + d \<longleftrightarrow> c \<le> (b - a) *\<^sub>C e + d"
  for c d e :: "'a::ordered_complex_vector"
  by (simp add: algebra_simps)

lemma scaleC_left_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b"
  for a b :: "'a::ordered_complex_vector"
  apply (drule scaleC_left_mono [of _ _ "- c"])
  by simp_all


lemma scaleC_right_mono_neg: "b \<le> a \<Longrightarrow> c \<le> 0 \<Longrightarrow> a *\<^sub>C c \<le> b *\<^sub>C c"
  for c :: "'a::ordered_complex_vector"
  apply (drule scaleC_right_mono [of _ _ "- c"])
  by simp_all


lemma scaleC_nonpos_nonpos: "a \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> 0 \<le> a *\<^sub>C b"
  for b :: "'a::ordered_complex_vector"
  using scaleC_right_mono_neg [of a 0 b] by simp

lemma split_scaleC_pos_le: "(0 \<le> a \<and> 0 \<le> b) \<or> (a \<le> 0 \<and> b \<le> 0) \<Longrightarrow> 0 \<le> a *\<^sub>C b"
  for b :: "'a::ordered_complex_vector"
  by (auto simp add: scaleC_nonneg_nonneg scaleC_nonpos_nonpos)

lemma reals_zero_comparable_iff:
  "(x::complex)\<in>\<real> \<longleftrightarrow> x \<le> 0 \<or> x \<ge> 0"
  unfolding complex_is_Real_iff less_eq_complex_def
  by auto

lemma reals_zero_comparable:
  fixes x::complex
  assumes "x\<in>\<real>"
  shows "x \<le> 0 \<or> x \<ge> 0"
  using assms unfolding reals_zero_comparable_iff by assumption

lemma zero_le_scaleC_iff:
  fixes b :: "'a::ordered_complex_vector"
  assumes "a \<in> \<real>"
  shows "0 \<le> a *\<^sub>C b \<longleftrightarrow> 0 < a \<and> 0 \<le> b \<or> a < 0 \<and> b \<le> 0 \<or> a = 0"
    (is "?lhs = ?rhs")
proof (cases "a = 0")
  case True
  thus ?thesis by simp
next
  case False
  show ?thesis
  proof
    assume ?lhs
    from \<open>a \<noteq> 0\<close> consider "a > 0" | "a < 0"
      using reals_zero_comparable[OF assms] by auto
    thus ?rhs
    proof cases
      case 1
      with \<open>?lhs\<close> have "inverse a *\<^sub>C 0 \<le> inverse a *\<^sub>C (a *\<^sub>C b)"
        by (intro scaleC_mono) auto
      with 1 show ?thesis
        by simp
    next
      case 2
      with \<open>?lhs\<close> have "- inverse a *\<^sub>C 0 \<le> - inverse a *\<^sub>C (a *\<^sub>C b)"
        by (intro scaleC_mono) auto
      with 2 show ?thesis
        by simp
    qed
  next
    assume ?rhs
    thus ?lhs
      using reals_zero_comparable[OF assms]
      by (auto simp: not_le \<open>a \<noteq> 0\<close> intro!: split_scaleC_pos_le )
  qed
qed

lemma scaleC_le_0_iff: 
  fixes b::"'a::ordered_complex_vector"
  assumes "a \<in> \<real>"
  shows "a *\<^sub>C b \<le> 0 \<longleftrightarrow> 0 < a \<and> b \<le> 0 \<or> a < 0 \<and> 0 \<le> b \<or> a = 0"
  apply (insert zero_le_scaleC_iff [of "-a" b]) 
  using reals_zero_comparable[OF assms]
  using assms by auto

lemma scaleC_le_cancel_left: 
  fixes b :: "'a::ordered_complex_vector"
  assumes "c \<in> \<real>"
  shows "c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> (0 < c \<longrightarrow> a \<le> b) \<and> (c < 0 \<longrightarrow> b \<le> a)"
  using assms apply cases apply (simp add: scaleR_scaleC[symmetric] less_complex_def)
  by (rule scaleR_le_cancel_left)

lemma scaleC_le_cancel_left_pos: "0 < c \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> a \<le> b"
  for b :: "'a::ordered_complex_vector"
  by (meson dual_order.strict_implies_order reals_zero_comparable_iff scaleC_le_cancel_left scaleC_left_mono)

lemma scaleC_le_cancel_left_neg: "c < 0 \<Longrightarrow> c *\<^sub>C a \<le> c *\<^sub>C b \<longleftrightarrow> b \<le> a"
  for b :: "'a::ordered_complex_vector"
  by (meson dual_order.strict_implies_order reals_zero_comparable_iff scaleC_le_cancel_left scaleC_left_mono_neg)

lemma scaleC_left_le_one_le: "0 \<le> x \<Longrightarrow> a \<le> 1 \<Longrightarrow> a *\<^sub>C x \<le> x"
  for x :: "'a::ordered_complex_vector" and a :: complex
  using scaleC_right_mono[of a 1 x] by simp

subsection \<open>Complex normed vector spaces\<close>

class complex_normed_vector = complex_vector + sgn_div_norm + dist_norm + uniformity_dist + open_uniformity +
  real_normed_vector + 
  assumes norm_scaleC [simp]: "norm (a *\<^sub>C x) = (cmod a) * norm x"

class complex_normed_algebra = complex_algebra + complex_normed_vector + real_normed_algebra

class complex_normed_algebra_1 = complex_algebra_1 + complex_normed_algebra + real_normed_algebra_1

lemma (in complex_normed_algebra_1) scaleC_power [simp]: "(scaleC x y) ^ n = scaleC (x^n) (y^n)"
  by (induct n) (simp_all add: mult_ac)

class complex_normed_div_algebra = complex_div_algebra + complex_normed_vector + real_normed_div_algebra

class complex_normed_field = complex_field + complex_normed_div_algebra + real_normed_field

instance complex_normed_div_algebra < complex_normed_algebra_1 ..

lemma dist_scaleC [simp]: "dist (x *\<^sub>C a) (y *\<^sub>C a) = cmod (x - y) * norm a"
  for a :: "'a::complex_normed_vector"
  by (metis dist_norm norm_scaleC scaleC_left.diff)

lemma norm_of_complex [simp]: "norm (of_complex r :: 'a::complex_normed_algebra_1) = cmod r"
  by (simp add: of_complex_def)

lemma norm_of_complex_add1 [simp]: "norm (of_complex x + 1 :: 'a :: complex_normed_div_algebra) = cmod (x + 1)"
  by (metis norm_of_complex of_complex_1 of_complex_add)

lemma norm_of_complex_addn [simp]:
  "norm (of_complex x + numeral b :: 'a :: complex_normed_div_algebra) = cmod (x + numeral b)"
  by (metis norm_of_complex of_complex_add of_complex_numeral)

lemma norm_of_complex_diff [simp]:
  "norm (of_complex b - of_complex a :: 'a::complex_normed_algebra_1) \<le> cmod (b - a)"
  by (metis norm_of_complex of_complex_diff order_refl)

subsection \<open>Class instances for complex numbers\<close>

instantiation complex :: complex_normed_field
begin

instance
  apply intro_classes 
  by (simp add: norm_mult)

end

lemma dist_of_complex [simp]: "dist (of_complex x :: 'a) (of_complex y) = dist x y"
  for a :: "'a::complex_normed_div_algebra"
  by (metis dist_norm norm_of_complex of_complex_diff)

declare [[code abort: "open :: complex set \<Rightarrow> bool"]]

subsection \<open>Sign function\<close>

lemma sgn_scaleC: "sgn (scaleC r x) = scaleC (sgn r) (sgn x)"
  for x :: "'a::complex_normed_vector"
  by (simp add: scaleR_scaleC sgn_div_norm ac_simps)

lemma sgn_of_complex: "sgn (of_complex r :: 'a::complex_normed_algebra_1) = of_complex (sgn r)"
  unfolding of_complex_def by (simp only: sgn_scaleC sgn_one)

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

lemma linear_compose: "clinear f \<Longrightarrow> clinear g \<Longrightarrow> clinear (g \<circ> f)"
  unfolding clinear_def
  using Vector_Spaces.linear_compose
  by blast

lemma clinear_additive_D:
  \<open>clinear f \<Longrightarrow> (\<And> x y. f (x + y) = f x + f y)\<close>
  by (simp add: additive.intro complex_vector.linear_add)

lemma clinear_imp_scaleC:
  assumes "clinear D"
  obtains d where "D = (\<lambda>x. x *\<^sub>C d)"
  by (metis assms complex_scaleC_def complex_vector.linear_scale mult.commute mult.left_neutral)

corollary complex_clinearD:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "clinear f" obtains c where "f = (*) c"
  by (rule clinear_imp_scaleC [OF assms]) (force simp: scaleC_conv_of_complex)

lemma clinearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>C x) = c *\<^sub>C f x"
  shows "clinear f"
  unfolding clinear_def
proof
  show "f (b1 + b2) = f b1 + f b2"
    for b1 :: 'a
      and b2 :: 'a
    by (simp add: assms(1))    
  show "f (r *\<^sub>C b) = r *\<^sub>C f b"
    for r :: complex
      and b :: 'a
    by (simp add: assms(2))    
qed

lemma clinear_times_of_complex: "clinear (\<lambda>x. a * of_complex x)"
proof (rule clinearI)
  show "a * of_complex (x + y) = a * of_complex x + a * of_complex y"
    for x :: complex
      and y :: complex
    by (simp add: ring_class.ring_distribs(1))    
  show "a * of_complex (c *\<^sub>C x) = c *\<^sub>C (a * of_complex x)"
    for c :: complex
      and x :: complex
    by (metis complex_scaleC_def mult_scaleC_right of_complex_mult scaleC_conv_of_complex)
qed

locale cbounded_linear = 
  fixes f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector"
  assumes 
    is_clinear: "clinear f" and
    bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

sublocale bounded_linear
proof
  have \<open>linear f\<close>
    by (simp add: clinear_is_linear is_clinear)

  show "f (b1 + b2) = f b1 + f b2"
    for b1 :: 'a
      and b2 :: 'a
    using  \<open>linear f\<close>
    by (simp add: real_vector.linear_add)
  show "f (r *\<^sub>R b) = r *\<^sub>R f b"
    for r :: real
      and b :: 'a
    using \<open>linear f\<close>
    by (simp add: real_vector.linear_scale)
  show "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
    by (simp add: bounded)    
qed


lemma bounded_linear: "bounded_linear f"
  by (fact bounded_linear)

lemma clinear: "clinear f"
  by (simp add: is_clinear)

end

lemma clinear_times: "clinear (\<lambda>x. c * x)"
  for c :: "'a::complex_algebra"
  by (auto simp: clinearI distrib_left)

lemma cbounded_linear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (r *\<^sub>C x) = r *\<^sub>C (f x)"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "cbounded_linear f"
  using assms(1) assms(2) assms(3) cbounded_linear_def clinearI by blast

locale csemilinear = additive f for f :: "'a::complex_vector \<Rightarrow> 'b::complex_vector" +
  assumes scaleC: "f (scaleC r x) = scaleC (cnj r) (f x)"

sublocale csemilinear \<subseteq> linear
  apply (rule linearI)
   apply (rule add)
  unfolding scaleR_scaleC by (subst scaleC, simp)

lemma csemilinear_imp_scaleC:
  assumes "csemilinear D"
  obtains d where "D = (\<lambda>x. cnj (x *\<^sub>C d))"
proof (atomize_elim, rule exI[of _ "cnj (D 1)"], rule ext)
  fix x
  have "cnj (x *\<^sub>C cnj (D 1)) = cnj x *\<^sub>C D 1" by simp
  also have "\<dots> = D (x *\<^sub>C 1)" by (rule csemilinear.scaleC[OF assms, symmetric])
  also have "\<dots> = D x" by simp
  finally show "D x = cnj (x *\<^sub>C cnj (D 1))" by simp
qed

corollary complex_csemilinearD:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "csemilinear f" obtains c where "f = (\<lambda>x. cnj (c * x))"
  by (rule csemilinear_imp_scaleC [OF assms]) (force simp: scaleC_conv_of_complex)

lemma csemilinear_times_of_complex: "csemilinear (\<lambda>x. cnj (a * of_complex x))"
  apply (simp add: csemilinear_def additive_def csemilinear_axioms_def)
  by (simp add: distrib_left additive.intro)

lemma csemilinearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>C x) = cnj c *\<^sub>C f x"
  shows "csemilinear f"
  by standard (rule assms)+

locale bounded_csemilinear = csemilinear f for f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

sublocale bounded_linear
  apply standard by (fact bounded) 

(* Recovered Theorem *)
lemma bounded_linear: "bounded_linear f"
  by (fact bounded_linear)

(* Recovered Theorem *)
lemma csemilinear: "csemilinear f"
  by (fact csemilinear_axioms)

end

lemma bounded_csemilinear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (scaleC r x) = scaleC (cnj r) (f x)"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_csemilinear f"
  by standard (blast intro: assms)+

lemma cnj_bounded_csemilinear[simp]: "bounded_csemilinear cnj"
  apply (rule bounded_csemilinear_intro[where K=1]) by auto

lemma bounded_csemilinear_compose1:
  assumes "bounded_csemilinear f"
    and "bounded_csemilinear g"
  shows "cbounded_linear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_csemilinear f by fact
  interpret g: bounded_csemilinear g by fact
  show ?thesis
  proof 
    show "clinear (\<lambda>x. f (g x))"
      unfolding clinear_def
    proof
      show "f (g (b1 + b2)) = f (g b1) + f (g b2)"
        for b1 :: 'c
          and b2 :: 'c
        by (simp add: f.add g.add)

      show "f (g (r *\<^sub>C b)) = r *\<^sub>C f (g b)"
        for r :: complex
          and b :: 'c
        by (simp add: f.scaleC g.scaleC)  
    qed
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    proof-
      have "\<exists> Kf. \<forall>x. norm (f (g x)) \<le> norm (g x) * Kf"
        using f.pos_bounded by auto
      then obtain Kf where \<open>\<forall>x. norm (f (g x)) \<le> norm (g x) * Kf\<close>
        by blast        
      have "\<exists> Kg. \<forall>x. norm (g x) * Kf \<le> (norm x * Kg) * Kf"
        by (metis g.pos_bounded mult.commute mult_eq_0_iff mult_le_cancel_left norm_ge_zero real_mult_le_cancel_iff2)        
      then obtain Kg where \<open>\<forall>x. norm (g x) * Kf \<le> (norm x * Kg) * Kf\<close>
        by blast
      have \<open>\<forall>x. (norm x * Kg) * Kf = norm x * (Kg * Kf)\<close>
        using mult.assoc
        by simp 
      define  K where \<open>K = Kg * Kf\<close>
      have  \<open>\<forall>x. norm (f (g x)) \<le> norm x * K\<close>
        unfolding K_def
        by (metis K_def \<open>\<forall>x. norm (f (g x)) \<le> norm (g x) * Kf\<close> \<open>\<forall>x. norm (g x) * Kf \<le> norm x * Kg * Kf\<close> \<open>\<forall>x. norm x * Kg * Kf = norm x * (Kg * Kf)\<close> dual_order.trans) 
      thus ?thesis 
        by blast
    qed
  qed
qed

lemma bounded_csemilinear_compose2:
  assumes "bounded_csemilinear f"
    and "cbounded_linear g"
  shows "bounded_csemilinear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_csemilinear f by fact
  interpret g: cbounded_linear g by fact
  show ?thesis
  proof unfold_locales
    show "f (g (x + y)) = f (g x) + f (g y)" for x y
      by (simp only: f.add g.add)
    show "f (g (scaleC r x)) = scaleC (cnj r) (f (g x))" for r x
      by (simp add: complex_vector.linear_scale f.scaleC g.is_clinear)

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

lemma bounded_csemilinear_compose3:
  assumes "cbounded_linear f"
    and "bounded_csemilinear g"
  shows "bounded_csemilinear (\<lambda>x. f (g x))"
proof -
  interpret f: cbounded_linear f by fact
  interpret g: bounded_csemilinear g by fact
  show ?thesis
  proof unfold_locales
    show "f (g (x + y)) = f (g x) + f (g y)" for x y
      by (simp only: f.add g.add)
    show "f (g (scaleC r x)) = scaleC (cnj r) (f (g x))" for r x
      using complex_vector.linear_scale f.is_clinear g.scaleC by auto
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

locale bounded_cbilinear =
  fixes prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
    (* (infixl "**" 70) *)
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleC_left: "prod (r *\<^sub>C a) b = r *\<^sub>C (prod a b)"
    and scaleC_right: "prod a (r *\<^sub>C b) = r *\<^sub>C (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

sublocale bounded_bilinear
  apply standard
  unfolding scaleR_scaleC
      apply (fact add_left)
     apply (fact add_right)
    apply (fact scaleC_left)
   apply (fact scaleC_right)
  by (fact bounded)

(* Should be bounded_cbilinear *)
lemma bounded_bilinear: "bounded_bilinear prod"
  by (fact bounded_bilinear_axioms)

lemma cbounded_linear_left: "cbounded_linear (\<lambda>a. prod a b)"
  apply (insert bounded)
  apply safe
  apply (rule_tac K="norm b * K" in cbounded_linear_intro)
    apply (rule add_left)
   apply (rule scaleC_left)
  by (simp add: ac_simps)


lemma cbounded_linear_right: "cbounded_linear (\<lambda>b. prod a b)"
  apply (insert bounded)
  apply safe
  apply (rule_tac K="norm a * K" in cbounded_linear_intro)
    apply (rule add_right)
   apply (rule scaleC_right)
  by (simp add: ac_simps)


lemma flip: "bounded_cbilinear (\<lambda>x y. prod y x)"
  apply standard
      apply (rule add_right)
     apply (rule add_left)
    apply (rule scaleC_right)
   apply (rule scaleC_left)
  apply (subst mult.commute)
  apply (insert bounded)
  by blast


lemma comp1:
  assumes "cbounded_linear g"
  shows "bounded_cbilinear (\<lambda>x. prod (g x))"
proof unfold_locales
  interpret g: cbounded_linear g by fact
  write prod (infixl "***" 70)
  show "\<And>a a' b. g (a + a') *** b = g a *** b + g a' *** b"
    "\<And>a b b'. g a *** (b + b') = g a *** b + g a *** b'"
    "\<And>r a b. g (r *\<^sub>C a) *** b = r *\<^sub>C (g a *** b)"
    "\<And>a r b. g a *** (r *\<^sub>C b) = r *\<^sub>C (g a *** b)"
       apply (simp add: add_left g.add)
      apply (simp add: add_right)
     apply (simp add: complex_vector.linear_scale g.is_clinear scaleC_left)
    by (simp add: scaleC_right)

  from g.nonneg_bounded nonneg_bounded obtain K L
    where nn: "0 \<le> K" "0 \<le> L"
      and K: "\<And>x. norm (g x) \<le> norm x * K"
      and L: "\<And>a b. norm (a *** b) \<le> norm a * norm b * L"
    by auto
  have "norm (g a *** b) \<le> norm a * K * norm b * L" for a b
    by (auto intro!:  order_trans[OF K] order_trans[OF L] mult_mono simp: nn)
  thus "\<exists>K. \<forall>a b. norm (g a *** b) \<le> norm a * norm b * K"
    by (auto intro!: exI[where x="K * L"] simp: ac_simps)
qed

lemma comp: "cbounded_linear f \<Longrightarrow> cbounded_linear g \<Longrightarrow> bounded_cbilinear (\<lambda>x y. prod (f x) (g y))"
  by (rule bounded_cbilinear.flip[OF bounded_cbilinear.comp1[OF bounded_cbilinear.flip[OF comp1]]])

end

lemma cbounded_linear_ident[simp]: "cbounded_linear id"
  unfolding cbounded_linear_def
  apply auto
   apply (simp add: clinearI)
  using less_eq_real_def by auto


lemma cbounded_linear_zero[simp]: "cbounded_linear (\<lambda>x. 0)"
  unfolding cbounded_linear_def
  by (metis complex_vector.module_hom_zero mult.commute mult_zero_left norm_zero order_refl)


lemma cbounded_linear_add:
  assumes "cbounded_linear f"
    and "cbounded_linear g"
  shows "cbounded_linear (\<lambda>x. f x + g x)"
proof -
  interpret f: cbounded_linear f by fact
  interpret g: cbounded_linear g by fact
  from f.bounded obtain Kf where Kf: "norm (f x) \<le> norm x * Kf" for x
    by blast
  from g.bounded obtain Kg where Kg: "norm (g x) \<le> norm x * Kg" for x
    by blast
  show ?thesis
  proof
    show "clinear (\<lambda>x. f x + g x)"
      by (simp add: clinearI complex_vector.linear_scale f.add f.is_clinear g.add g.is_clinear scaleC_add_right)

    show "\<exists>K. \<forall>x. norm (f x + g x) \<le> norm x * K"
      using add_mono[OF Kf Kg]
      by (intro exI[of _ "Kf + Kg"]) (auto simp: field_simps intro: norm_triangle_ineq order_trans)
  qed
qed

lemma cbounded_linear_minus:
  assumes "cbounded_linear f"
  shows "cbounded_linear (\<lambda>x. - f x)"
proof -
  interpret f: cbounded_linear f by fact
  show ?thesis
  proof
    show "clinear (\<lambda>x. - f x)"
      by (simp add: complex_vector.linear_compose_neg f.is_clinear)
    show "\<exists>K. \<forall>x. norm (- f x) \<le> norm x * K"
      using f.pos_bounded by auto    
  qed
qed

lemma cbounded_linear_sub: "cbounded_linear f \<Longrightarrow> cbounded_linear g \<Longrightarrow> cbounded_linear (\<lambda>x. f x - g x)"
  using cbounded_linear_add[of f "\<lambda>x. - g x"] cbounded_linear_minus[of g]
  by (auto simp add: algebra_simps)

lemma cbounded_linear_sum:
  fixes f :: "'i \<Rightarrow> 'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector"
  shows "(\<And>i. i \<in> I \<Longrightarrow> cbounded_linear (f i)) \<Longrightarrow> cbounded_linear (\<lambda>x. \<Sum>i\<in>I. f i x)"
  by (induct I rule: infinite_finite_induct) (auto intro!: cbounded_linear_add)

lemma cbounded_linear_compose:
  assumes "cbounded_linear f"
    and "cbounded_linear g"
  shows "cbounded_linear (\<lambda>x. f (g x))"
proof -
  interpret f: cbounded_linear f by fact
  interpret g: cbounded_linear g by fact
  show ?thesis
  proof
    show "clinear (\<lambda>x. f (g x))"
      unfolding clinear_def
    proof
      show "f (g (b1 + b2)) = f (g b1) + f (g b2)"
        for b1 :: 'c
          and b2 :: 'c
        by (simp add: f.add g.add)

      show "f (g (r *\<^sub>C b)) = r *\<^sub>C f (g b)"
        for r :: complex
          and b :: 'c
        by (simp add: complex_vector.linear_scale f.is_clinear g.is_clinear)

    qed
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


lemma bounded_cbilinear_mult: "bounded_cbilinear ((*) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a::complex_normed_algebra)"
  apply (rule bounded_cbilinear.intro)
      apply (rule distrib_right)
     apply (rule distrib_left)
    apply (rule mult_scaleC_left)
   apply (rule mult_scaleC_right)
  apply (rule_tac x="1" in exI)
  by (simp add: norm_mult_ineq)


lemma cbounded_linear_mult_left: "cbounded_linear (\<lambda>x::'a::complex_normed_algebra. x * y)"
  using bounded_cbilinear_mult
  by (rule bounded_cbilinear.cbounded_linear_left)

lemma cbounded_linear_mult_right: "cbounded_linear (\<lambda>y::'a::complex_normed_algebra. x * y)"
  using bounded_cbilinear_mult
  by (rule bounded_cbilinear.cbounded_linear_right)

lemmas cbounded_linear_mult_const =
  cbounded_linear_mult_left [THEN cbounded_linear_compose]

lemmas cbounded_linear_const_mult =
  cbounded_linear_mult_right [THEN cbounded_linear_compose]

lemma cbounded_linear_divide: "cbounded_linear (\<lambda>x. x / y)"
  for y :: "'a::complex_normed_field"
  unfolding divide_inverse by (rule cbounded_linear_mult_left)

lemma bounded_cbilinear_scaleC: "bounded_cbilinear scaleC"
  apply (rule bounded_cbilinear.intro)
      apply (rule scaleC_add_left)
     apply (rule scaleC_add_right)
    apply simp
   apply (rule scaleC_left_commute)
  apply (rule_tac x="1" in exI)
  by simp


lemma cbounded_linear_scaleC_left: "cbounded_linear (\<lambda>r. scaleC r x)"
  using bounded_cbilinear_scaleC
  by (rule bounded_cbilinear.cbounded_linear_left)

lemma cbounded_linear_scaleC_right: "cbounded_linear (\<lambda>x. scaleC r x)"
  using bounded_cbilinear_scaleC
  by (rule bounded_cbilinear.cbounded_linear_right)

lemmas cbounded_linear_scaleC_const =
  cbounded_linear_scaleC_left[THEN cbounded_linear_compose]

lemmas cbounded_linear_const_scaleC =
  cbounded_linear_scaleC_right[THEN cbounded_linear_compose]

lemma cbounded_linear_of_complex: "cbounded_linear (\<lambda>r. of_complex r)"
  unfolding of_complex_def by (rule cbounded_linear_scaleC_left)

lemma complex_cbounded_linear: "cbounded_linear f \<longleftrightarrow> (\<exists>c::complex. f = (\<lambda>x. x * c))"
  for f :: "complex \<Rightarrow> complex"
proof -
  {
    fix x
    assume "cbounded_linear f"
    then interpret cbounded_linear f .
    have "f x = x * f 1"
      by (metis complex_scaleC_def complex_vector.linear_scale is_clinear mult.comm_neutral)      
  }
  thus ?thesis
    by (auto intro: exI[of _ "f 1"] cbounded_linear_mult_left)
qed

lemma bij_clinear_imp_inv_clinear: "clinear f \<Longrightarrow> bij f \<Longrightarrow> clinear (inv f)"
  unfolding clinear_def
proof
  show "inv f (b1 + b2) = inv f b1 + inv f b2"
    if "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) f"
      and "bij f"
    for b1 :: 'b
      and b2 :: 'b
    using that  bij_inv_eq_iff complex_vector.vector_space_pair_axioms vector_space_pair.linear_add
  proof -
    have "\<And>a b. f a + f b = f (a + b)"
      by (metis (no_types) complex_vector.vector_space_pair_axioms that(1) vector_space_pair.linear_add)
    thus ?thesis
      by (metis (no_types) bij_inv_eq_iff that(2))
  qed

  show "inv f (r *\<^sub>C b) = r *\<^sub>C inv f b"
    if "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) f"
      and "bij f"
    for r :: complex
      and b :: 'b
    using that
    by (smt bij_inv_eq_iff clinear_def complex_vector.linear_scale) 
qed

locale bounded_sesquilinear =
  fixes prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleC_left: "prod (r *\<^sub>C a) b = (cnj r) *\<^sub>C (prod a b)"
    and scaleC_right: "prod a (r *\<^sub>C b) = r *\<^sub>C (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

(* Recovered theorem *)
sublocale bounded_bilinear
  apply standard
  unfolding scaleR_scaleC
      apply (fact add_left)
     apply (fact add_right)
    apply (simp add: scaleC_left)
   apply (fact scaleC_right)
  by (fact bounded)

(* Recovered theorem *)
lemma bounded_bilinear: "bounded_bilinear prod" by (fact bounded_bilinear_axioms)

lemma bounded_csemilinear_left: "bounded_csemilinear (\<lambda>a. prod a b)"
  apply (insert bounded)
  apply safe
  apply (rule_tac K="norm b * K" in bounded_csemilinear_intro)
    apply (rule add_left)
   apply (simp add: scaleC_left)
  by (simp add: ac_simps)

lemma cbounded_linear_right: "cbounded_linear (\<lambda>b. prod a b)"
  apply (insert bounded)
  apply safe
  apply (rule_tac K="norm a * K" in cbounded_linear_intro)
    apply (rule add_right)
   apply (rule scaleC_right)
  by (simp add: ac_simps)

lemma comp1:
  assumes \<open>cbounded_linear g\<close>
  shows \<open>bounded_sesquilinear (\<lambda>x. prod (g x))\<close>
proof
  show "prod (g (a + a')) b = prod (g a) b + prod (g a') b"
    for a :: 'd
      and a' :: 'd
      and b :: 'b
  proof-
    have \<open>g (a + a') = g a + g a'\<close>
      using \<open>cbounded_linear g\<close>
      unfolding cbounded_linear_def
      by (simp add: complex_vector.linear_add)
    thus ?thesis
      by (simp add: add_left) 
  qed
  show "prod (g a) (b + b') = prod (g a) b + prod (g a) b'"
    for a :: 'd
      and b :: 'b
      and b' :: 'b
    by (simp add: add_right)
  show "prod (g (r *\<^sub>C a)) b = cnj r *\<^sub>C prod (g a) b"
    for r :: complex
      and a :: 'd
      and b :: 'b
  proof-
    have \<open>g (r *\<^sub>C a) = r *\<^sub>C (g a)\<close>
      using \<open>cbounded_linear g\<close>
      unfolding cbounded_linear_def
      by (simp add: complex_vector.linear_scale)
    thus ?thesis
      by (simp add: scaleC_left)      
  qed  
  show "prod (g a) (r *\<^sub>C b) = r *\<^sub>C prod (g a) b"
    for a :: 'd
      and r :: complex
      and b :: 'b
    by (simp add: scaleC_right)    
  show "\<exists>K. \<forall>a b. norm (prod (g a) b) \<le> norm a * norm b * K"
  proof-
    have \<open>\<exists> M. \<forall> a. norm (g a) \<le> norm a * M\<close>
      using \<open>cbounded_linear g\<close>
      unfolding cbounded_linear_def
      by simp
    hence \<open>\<exists> M. \<forall> a. norm (g a) \<le> norm a * M \<and> M \<ge> 0\<close>
      by (metis linear mult.commute mult_nonneg_nonpos2 mult_zero_left norm_ge_zero order.trans)
    then obtain M where \<open>\<And> a. norm (g a) \<le> norm a * M\<close> and \<open>M \<ge> 0\<close>
      by blast
    have \<open>\<exists>N. \<forall>a b. norm (prod a b) \<le> norm a * norm b * N\<close>
      using bounded
      by blast
    hence \<open>\<exists>N. \<forall>a b. norm (prod a b) \<le> norm a * norm b * N \<and> N \<ge> 0\<close>
    proof - (* sledgehammer *)
      { fix aa :: "real \<Rightarrow> 'a" and bb :: "real \<Rightarrow> 'b"
        have ff1: "\<forall>a b r. r * (norm (b::'b) * norm (a::'a)) \<le> 0 \<or> 0 \<le> r"
          by (metis (no_types) linear mult_nonneg_nonpos2 norm_ge_zero semiring_normalization_rules(18))
        obtain rr :: real where
          "\<forall>a b r. norm (prod a b) \<le> r \<or> r < rr * (norm b * norm a)"
          by (metis bounded dual_order.strict_trans1 mult.commute not_le)
        hence "\<exists>r. norm (prod (aa r) (bb r)) \<le> norm (aa r) * norm (bb r) * r \<and> 0 \<le> r"
          using ff1 by (metis (no_types) linear mult.commute mult_zero_left not_le) }
      thus ?thesis
        by metis
    qed
    then obtain N where \<open>\<And> a b. norm (prod a b) \<le> norm a * norm b * N\<close> and \<open>N \<ge> 0\<close>
      by blast
    define K where \<open>K = M * N\<close>
    have \<open>K \<ge> 0\<close>
      unfolding K_def
      by (simp add: \<open>0 \<le> M\<close> \<open>0 \<le> N\<close>)
    have \<open>norm (prod (g a) b) \<le> norm (g a) * norm b * N\<close>
      for a b
      using \<open>\<And> a b. norm (prod a b) \<le> norm a * norm b * N\<close>
      by blast
    hence \<open>norm (prod (g a) b) \<le> (norm a * M) * norm b * N\<close>
      for a b
    proof -
      have "\<forall>d b. norm (b::'b) * norm (g d) \<le> norm b * (M * norm d)"
        by (metis \<open>\<And>a. norm (g a) \<le> norm a * M\<close> mult.commute norm_ge_zero ordered_comm_semiring_class.comm_mult_left_mono)
      thus ?thesis
        by (metis (no_types) \<open>0 \<le> N\<close> \<open>\<And>b a. norm (prod (g a) b) \<le> norm (g a) * norm b * N\<close> dual_order.trans mult.commute ordered_comm_semiring_class.comm_mult_left_mono)
    qed
    hence \<open>norm (prod (g a) b) \<le> norm a * norm b * K\<close>
      for a b
      unfolding K_def
      by (simp add: mult.commute mult.left_commute)
    thus ?thesis
      by blast      
  qed  
qed

lemma comp2:
  assumes \<open>cbounded_linear g\<close>
  shows \<open>bounded_sesquilinear (\<lambda>x y. prod x (g y))\<close>
proof
  show "prod (a + a') (g b) = prod a (g b) + prod a' (g b)"
    for a :: 'a
      and a' :: 'a
      and b :: 'd
    by (simp add: add_left)    
  show "prod a (g (b + b')) = prod a (g b) + prod a (g b')"
    for a :: 'a
      and b :: 'd
      and b' :: 'd
  proof-
    have \<open>g (b + b') = g b + g b'\<close>
      using \<open>cbounded_linear g\<close>
      unfolding cbounded_linear_def
      by (simp add: complex_vector.linear_add)
    thus ?thesis
      by (simp add: add_right) 
  qed
  show "prod (r *\<^sub>C a) (g b) = cnj r *\<^sub>C prod a (g b)"
    for r :: complex
      and a :: 'a
      and b :: 'd
    by (simp add: scaleC_left)    
  show "prod a (g (r *\<^sub>C b)) = r *\<^sub>C prod a (g b)"
    for a :: 'a
      and r :: complex
      and b :: 'd
  proof-
    have \<open>g (r *\<^sub>C b) = r *\<^sub>C g b\<close>
      using \<open>cbounded_linear g\<close>
      unfolding cbounded_linear_def
      by (simp add: complex_vector.linear_scale)
    thus ?thesis
      by (simp add: scaleC_right) 
  qed
  show "\<exists>K. \<forall>a b. norm (prod a (g b)) \<le> norm a * norm b * K"
  proof-
    have \<open>\<exists> M. \<forall> a. norm (g a) \<le> norm a * M\<close>
      using \<open>cbounded_linear g\<close>
      unfolding cbounded_linear_def
      by simp
    hence \<open>\<exists> M. \<forall> a. norm (g a) \<le> norm a * M \<and> M \<ge> 0\<close>
      by (metis linear mult.commute mult_nonneg_nonpos2 mult_zero_left norm_ge_zero order.trans)
    then obtain M where \<open>\<And> a. norm (g a) \<le> norm a * M\<close> and \<open>M \<ge> 0\<close>
      by blast
    have \<open>\<exists>N. \<forall>a b. norm (prod a b) \<le> norm a * norm b * N\<close>
      using bounded
      by blast
    hence \<open>\<exists>N. \<forall>a b. norm (prod a b) \<le> norm a * norm b * N \<and> N \<ge> 0\<close>
    proof - (* sledgehammer *)
      { fix aa :: "real \<Rightarrow> 'a" and bb :: "real \<Rightarrow> 'b"
        have ff1: "\<forall>a b r. r * (norm (b::'b) * norm (a::'a)) \<le> 0 \<or> 0 \<le> r"
          by (metis (no_types) linear mult_nonneg_nonpos2 norm_ge_zero semiring_normalization_rules(18))
        obtain rr :: real where
          "\<forall>a b r. norm (prod a b) \<le> r \<or> r < rr * (norm b * norm a)"
          by (metis bounded dual_order.strict_trans1 mult.commute not_le)
        hence "\<exists>r. norm (prod (aa r) (bb r)) \<le> norm (aa r) * norm (bb r) * r \<and> 0 \<le> r"
          using ff1 by (metis (no_types) linear mult.commute mult_zero_left not_le) }
      thus ?thesis
        by metis
    qed
    then obtain N where \<open>\<And> a b. norm (prod a b) \<le> norm a * norm b * N\<close> and \<open>N \<ge> 0\<close>
      by blast
    define K where \<open>K = M * N\<close>
    have \<open>K \<ge> 0\<close>
      unfolding K_def
      by (simp add: \<open>0 \<le> M\<close> \<open>0 \<le> N\<close>)

    have \<open>norm (prod a (g b)) \<le> norm a * norm b * K\<close>
      for a b
    proof-
      have \<open>norm (prod a (g b)) \<le> norm a * norm (g b) * N\<close>
        using \<open>\<And> a b. norm (prod a b) \<le> norm a * norm b * N\<close>
        by blast
      also have \<open>norm a * norm (g b) * N \<le> norm a * (norm b * M) * N\<close>
        using  \<open>\<And> a. norm (g a) \<le> norm a * M\<close> \<open>M \<ge> 0\<close>
        by (smt \<open>0 \<le> N\<close> mult_cancel_right norm_ge_zero ordered_comm_semiring_class.comm_mult_left_mono real_mult_less_iff1)
      also have \<open>norm a * (norm b * M) * N = norm a * norm b * K\<close>
        by (simp add: K_def)
      finally show ?thesis by blast
    qed
    thus ?thesis
      by blast      
  qed  
qed

lemma comp: "cbounded_linear f \<Longrightarrow> cbounded_linear g \<Longrightarrow> bounded_sesquilinear (\<lambda>x y. prod (f x) (g y))" 
  using comp1 bounded_sesquilinear.comp2 by auto

end


instance complex_normed_algebra_1 \<subseteq> perfect_space ..

lemma clinear_linear:
  fixes f :: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector\<close>
  assumes \<open>clinear f\<close>
  shows \<open>linear f\<close>
  using Complex_Vector_Spaces.clinear_is_linear
  by (simp add: clinear_is_linear assms)

lemma clinear_add:
  \<open>clinear f \<Longrightarrow> clinear g \<Longrightarrow> clinear (\<lambda> x. f x + g x)\<close>
  by (simp add: complex_vector.linear_compose_add)

lemma clinear_minus:
  \<open>clinear f \<Longrightarrow> clinear g \<Longrightarrow> clinear (\<lambda> x. f x - g x)\<close>
  by (simp add: complex_vector.linear_compose_sub)

lemma clinear_zero:
  fixes f :: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector\<close>
  shows \<open>clinear f \<Longrightarrow> f 0 = 0\<close>
  by (rule  Complex_Vector_Spaces.complex_vector.linear_0)

lemma clinear_sum_induction:
  \<open>\<forall> f S. card S = n \<and> (\<forall> t \<in> S. clinear (f t))  \<longrightarrow> clinear (\<lambda> x. \<Sum> t\<in>S. f t x)\<close>
proof (induction n)
  show "\<forall>f S. card S = 0 \<and> (\<forall>t\<in>S. clinear (\<lambda>a. f (t::'a) (a::'b)::'c)) \<longrightarrow> clinear (\<lambda>x. \<Sum>t\<in>S. f t x)"
    using complex_vector.linear_compose_sum by auto

  show "\<forall>f S. card S = Suc n \<and> (\<forall>t\<in>S. clinear (\<lambda>a. f (t::'a) (a::'b)::'c)) \<longrightarrow> clinear (\<lambda>x. \<Sum>t\<in>S. f t x)"
    if "\<forall>f S. card S = n \<and> (\<forall>t\<in>S. clinear (\<lambda>a. f (t::'a) (a::'b)::'c)) \<longrightarrow> clinear (\<lambda>x. \<Sum>t\<in>S. f t x)"
    for n :: nat
    using that complex_vector.linear_compose_sum by blast 
qed

lemma clinear_sum:
  \<open>finite S \<Longrightarrow> (\<And> t. t \<in> S \<Longrightarrow> clinear (f t)) \<Longrightarrow> clinear (\<lambda> x. \<Sum> t\<in>S. f t x)\<close>
  using clinear_sum_induction by blast

lemma cbounded_linearDiff: \<open>clinear A \<Longrightarrow> clinear B \<Longrightarrow> clinear (A - B)\<close>
  by (simp add: add_diff_add additive.add clinearI complex_vector.scale_right_diff_distrib clinear_additive_D complex_vector.linear_scale)

lemma scalarR_cbounded_linear:
  fixes c :: real
  assumes \<open>cbounded_linear f\<close>
  shows \<open>cbounded_linear (\<lambda> x. c *\<^sub>R f x )\<close>
proof-
  have  \<open>cbounded_linear (\<lambda> x. (complex_of_real c) *\<^sub>C f x )\<close>
    by (simp add: assms cbounded_linear_const_scaleC)
  thus ?thesis
    by (simp add: scaleR_scaleC) 
qed

lemma bounded_linear_cbounded_linear:
  \<open>bounded_linear A \<Longrightarrow> \<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x \<Longrightarrow> cbounded_linear A\<close>
proof
  show "clinear A"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x"
    using that
    by (simp add: bounded_linear.linear clinearI real_vector.linear_add) 
  show "\<exists>K. \<forall>x. norm (A x) \<le> norm x * K"
    if "bounded_linear A"
      and "\<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x"
    using that
    by (simp add: bounded_linear.bounded) 
qed

lemma comp_cbounded_linear:
  fixes  A :: \<open>'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector\<close> 
    and B :: \<open>'a::complex_normed_vector \<Rightarrow> 'b\<close>
  assumes \<open>cbounded_linear A\<close> and \<open>cbounded_linear B\<close>
  shows \<open>cbounded_linear (A \<circ> B)\<close>
proof
  show "clinear (A \<circ> B)"
    by (simp add: Complex_Vector_Spaces.linear_compose assms(1) assms(2) cbounded_linear.is_clinear)

  show "\<exists>K. \<forall>x. norm ((A \<circ> B) x) \<le> norm x * K"
  proof-
    obtain KB where \<open>\<forall>x. norm (B x) \<le> norm x * KB\<close> and \<open>KB \<ge> 0\<close>
      using assms(2) cbounded_linear.bounded
      by (metis (mono_tags, hide_lams) mult_le_0_iff norm_ge_zero order.trans zero_le_mult_iff) 
    obtain KA where \<open>\<forall>x. norm (A x) \<le> norm x * KA\<close> and \<open>KA \<ge> 0\<close>
      using assms(1) cbounded_linear.bounded
      by (metis (mono_tags, hide_lams) mult_le_0_iff norm_ge_zero order.trans zero_le_mult_iff) 
    have \<open>\<forall>x. norm (A (B x)) \<le> norm x * KB * KA\<close>
      using  \<open>\<forall>x. norm (A x) \<le> norm x * KA\<close>  \<open>KA \<ge> 0\<close> 
        \<open>\<forall>x. norm (B x) \<le> norm x * KB\<close>  \<open>KB \<ge> 0\<close>
      by (metis order.trans ordered_comm_semiring_class.comm_mult_left_mono semiring_normalization_rules(7))
    thus ?thesis
      by (metis ab_semigroup_mult_class.mult_ac(1) comp_apply)     
  qed
qed



subsection \<open>Nonstandard analysis\<close>

unbundle nsa_notation

definition scaleHC :: "complex star \<Rightarrow> 'a star \<Rightarrow> 'a::complex_normed_vector star"
  where [transfer_unfold]: "scaleHC = starfun2 scaleC"

instantiation star :: (scaleC) scaleC
begin
definition star_scaleC_def [transfer_unfold]: "scaleC r \<equiv> *f* (scaleC r)"
instance 
  apply intro_classes
  by (simp add: scaleR_scaleC star_scaleC_def star_scaleR_def)  
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
    apply StarDef.transfer
    by (simp add: scaleC_add_right)
  show "\<And>x::'a star. scaleC (a + b) x = scaleC a x + scaleC b x"
    apply StarDef.transfer
    by (simp add: scaleC_add_left)
  show "\<And>x::'a star. scaleC a (scaleC b x) = scaleC (a * b) x"
    by StarDef.transfer (rule scaleC_scaleC)
  show "\<And>x::'a star. scaleC 1 x = x"
    by StarDef.transfer (rule scaleC_one)
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
  includes nsa_notation
  fixes l :: \<open>'a::complex_normed_vector\<close>
  shows \<open>isCont (\<lambda> v. scaleC a v) l\<close>
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

unbundle no_nsa_notation

subsection \<open>Cauchy sequences\<close>

lemma cCauchy_iff2: "Cauchy X \<longleftrightarrow> (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. cmod (X m - X n) < inverse (real (Suc j))))"
  by (simp only: metric_Cauchy_iff2 dist_complex_def)

subsection \<open>Cauchy Sequences are Convergent\<close>

subsection \<open>The set of complex numbers is a complete metric space\<close>

class cbanach = complex_normed_vector + complete_space

subclass (in cbanach) banach ..

instance complex :: cbanach ..

lemmas sums_of_complex = bounded_linear.sums [OF cbounded_linear_of_complex[THEN cbounded_linear.bounded_linear]]
lemmas summable_of_complex = bounded_linear.summable [OF cbounded_linear_of_complex[THEN cbounded_linear.bounded_linear]]
lemmas suminf_of_complex = bounded_linear.suminf [OF cbounded_linear_of_complex[THEN cbounded_linear.bounded_linear]]

lemmas sums_scaleC_left = bounded_linear.sums[OF cbounded_linear_scaleC_left[THEN cbounded_linear.bounded_linear]]
lemmas summable_scaleC_left = bounded_linear.summable[OF cbounded_linear_scaleC_left[THEN cbounded_linear.bounded_linear]]
lemmas suminf_scaleC_left = bounded_linear.suminf[OF cbounded_linear_scaleC_left[THEN cbounded_linear.bounded_linear]]

lemmas sums_scaleC_right = bounded_linear.sums[OF cbounded_linear_scaleC_right[THEN cbounded_linear.bounded_linear]]
lemmas summable_scaleC_right = bounded_linear.summable[OF cbounded_linear_scaleC_right[THEN cbounded_linear.bounded_linear]]
lemmas suminf_scaleC_right = bounded_linear.suminf[OF cbounded_linear_scaleC_right[THEN cbounded_linear.bounded_linear]]

subsection \<open>Miscellany\<close>

lemma closed_scaleC: 
  fixes S::\<open>'a::complex_normed_vector set\<close> and a :: complex
  assumes \<open>closed S\<close>
  shows \<open>closed (scaleC a ` S)\<close>
proof (cases \<open>S = {}\<close>)
  case True
  thus ?thesis
    by simp 
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
        using Elementary_Topology.continuous_at_sequentially
        by auto
      moreover have \<open>(\<lambda> v. scaleC (inverse a) v) \<circ> x = t\<close>
      proof-
        have \<open>(\<lambda> v. scaleC (inverse a) v) \<circ> x = (\<lambda> n. scaleC (inverse a) (x n))\<close>
          by auto
        thus ?thesis using \<open>\<forall>n. t n = scaleC (inverse a) (x n)\<close>
          by auto
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
    thus ?thesis using Elementary_Topology.closed_sequential_limits
      by blast
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

lemma onorm_scalarC:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes \<open>cbounded_linear f\<close>
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
      have \<open>(norm (f x)) / norm x \<le> onorm f\<close>
        for x
        using \<open>cbounded_linear f\<close>
        by (simp add: cbounded_linear.bounded_linear le_onorm)        
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
      using cbounded_linear.bounded_linear cbounded_linear_scaleC_right linear_continuous_at by auto
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
  "\<forall> A \<in> \<A>. (closed_subspace A) \<Longrightarrow> closed_subspace (\<Inter>\<A>)"
proof-
  assume \<open>\<forall> A \<in> \<A>. (closed_subspace A)\<close>
  have \<open>complex_vector.subspace (\<Inter>\<A>)\<close>
  proof -
    obtain aa :: "'a set \<Rightarrow> 'a" and cc :: "'a set \<Rightarrow> complex" where
      f1: "\<forall>x0. (\<exists>v1 v2. v1 \<in> x0 \<and> v2 *\<^sub>C v1 \<notin> x0) = (aa x0 \<in> x0 \<and> cc x0 *\<^sub>C aa x0 \<notin> x0)"
      by moura
    obtain aaa :: "'a set \<Rightarrow> 'a" and aab :: "'a set \<Rightarrow> 'a" where
      "\<forall>x0. (\<exists>v1 v2. (v1 \<in> x0 \<and> v2 \<in> x0) \<and> v1 + v2 \<notin> x0) = ((aaa x0 \<in> x0 \<and> aab x0 \<in> x0) \<and> aaa x0 + aab x0 \<notin> x0)"
      by moura
    hence f2: "\<forall>A. (\<not> complex_vector.subspace A \<or> (\<forall>a aa. a \<notin> A \<or> aa \<notin> A \<or> a + aa \<in> A) \<and> (\<forall>a c. a \<notin> A \<or> c *\<^sub>C a \<in> A) \<and> 0 \<in> A) \<and> (complex_vector.subspace A \<or> aaa A \<in> A \<and> aab A \<in> A \<and> aaa A + aab A \<notin> A \<or> aa A \<in> A \<and> cc A *\<^sub>C aa A \<notin> A \<or> 0 \<notin> A)"
      using f1 by (metis (no_types) complex_vector.subspace_def)
    obtain AA :: "'a set set \<Rightarrow> 'a \<Rightarrow> 'a set" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x0 \<and> x1 \<notin> v2) = (AA x0 x1 \<in> x0 \<and> x1 \<notin> AA x0 x1)"
      by moura
    hence f3: "\<forall>a A. (a \<notin> \<Inter> A \<or> (\<forall>Aa. Aa \<notin> A \<or> a \<in> Aa)) \<and> (a \<in> \<Inter> A \<or> AA A a \<in> A \<and> a \<notin> AA A a)"
      by auto
    have f4: "\<forall>A. \<not> closed_subspace (A::'a set) \<or> complex_vector.subspace A"
      by (simp add: closed_subspace.subspace)      
    have f5: "\<forall>A. A \<notin> \<A> \<or> closed_subspace A"
      by (metis \<open>\<forall>A\<in>\<A>. closed_subspace A\<close>)
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
    by (simp add: \<open>\<forall>A\<in>\<A>. closed_subspace A\<close> closed_Inter closed_subspace.closed)
  ultimately show ?thesis 
    by (simp add: closed_subspace.intro)
qed


subsection \<open>Linear space\<close>

(* TODO rename 
  Ask to Dominique: Which name?
 *)
typedef (overloaded) ('a::"{complex_vector,topological_space}") 
  linear_space = \<open>{S::'a set. closed_subspace S}\<close>
  morphisms space_as_set Abs_linear_space
  using Complex_Vector_Spaces.subspace_UNIV by blast


setup_lifting type_definition_linear_space

lemma subspace_image:
  assumes "clinear f" and "complex_vector.subspace S"
  shows "complex_vector.subspace (f ` S)"
  by (simp add: assms(1) assms(2) complex_vector.linear_subspace_image)


instantiation linear_space :: (complex_normed_vector) scaleC begin
lift_definition scaleC_linear_space :: "complex \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is
  "\<lambda>c S. scaleC c ` S"
  apply (rule closed_subspace.intro)
  using cbounded_linear_def cbounded_linear_scaleC_right closed_subspace.subspace complex_vector.linear_subspace_image apply blast
  by (simp add: closed_scaleC closed_subspace.closed)

lift_definition scaleR_linear_space :: "real \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is
  "\<lambda>c S. (scaleR c) ` S"
  apply (rule closed_subspace.intro)
  using cbounded_linear_def cbounded_linear_scaleC_right scaleR_scaleC
   apply (metis closed_subspace.subspace complex_vector.linear_subspace_image)
  by (simp add: closed_scaling closed_subspace.closed)
instance 
  apply standard
  by (simp add: scaleR_scaleC scaleC_linear_space_def scaleR_linear_space_def)
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
  have  \<open>x \<in> (*\<^sub>C) a ` S \<Longrightarrow> x \<in> S\<close>
    for x
    using assms(2) closed_subspace.subspace complex_vector.subspace_scale by blast 
  moreover have  \<open>x \<in> S \<Longrightarrow> x \<in> (*\<^sub>C) a ` S\<close>
    for x
  proof -
    assume "x \<in> S"
    hence "\<exists>c aa. (c / a) *\<^sub>C aa \<in> S \<and> c *\<^sub>C aa = x"
      using assms(2) complex_vector.subspace_def scaleC_one
      by (metis closed_subspace.subspace) 
    hence "\<exists>aa. aa \<in> S \<and> a *\<^sub>C aa = x"
      using assms(1) by auto
    thus ?thesis
      by (meson image_iff)
  qed 
  ultimately show ?thesis by blast
qed


lemma timesScalarSpace_not0[simp]: "a \<noteq> 0 \<Longrightarrow> a *\<^sub>C S = S" for S :: "_ linear_space"
  apply transfer
  by (simp add: subspace_scale_invariant) 

instantiation linear_space :: ("{complex_vector,topological_space}") "top"
begin
lift_definition top_linear_space :: \<open>'a linear_space\<close> is \<open>UNIV\<close>
  by simp

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
    using that
    by (simp add: closed_subspace.subspace) 
  show "closed (\<Inter> S::'a set)"
    if "\<And>x. (x::'a set) \<in> S \<Longrightarrow> closed_subspace x"
    for S :: "'a set set"
    using that
    by (simp add: closed_subspace.closed) 
qed

instance ..
end


subsection \<open>Span\<close>

lift_definition Span :: "'a::complex_normed_vector set \<Rightarrow> 'a linear_space"
  is "\<lambda>G. closure (complex_vector.span G)"
  apply (rule closed_subspace.intro)
   apply (simp add: subspace_cl)
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
      using Abs_linear_space_inverse \<open>x \<in> space_as_set (Span A)\<close> 
        Span.rep_eq 
      by blast
    hence \<open>\<exists> y::nat \<Rightarrow> 'a. (\<forall> n. y n \<in> (complex_vector.span A)) \<and> y \<longlonglongrightarrow> x\<close>
      by (simp add: closure_sequential)
    then obtain y where \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close> and \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>y n \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S}\<close>
      for n
      using  \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close>
      by auto
    have \<open>x \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S}\<close> 
    proof-
      have \<open>closed_subspace S \<Longrightarrow> closed S\<close>
        for S::\<open>'a set\<close>
        by (simp add: closed_subspace.closed)
      hence \<open>closed ( \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S})\<close>
        by simp
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
      apply transfer
      by blast
  qed
  moreover have \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})
             \<Longrightarrow> x \<in> space_as_set (Span A)\<close>
    for x::'a
  proof-
    assume \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
    hence \<open>x \<in> \<Inter> {S. A \<subseteq> S \<and> closed_subspace S}\<close>
      apply transfer
      by blast
    moreover have \<open>{S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S} \<subseteq> {S. A \<subseteq> S \<and> closed_subspace S}\<close>
      using Collect_mono_iff
      by (simp add: Collect_mono_iff subspace_span_B) 
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
      using assms that(1) that(2)
      by (simp add: complex_vector.subspace_add subspace_cl) 
  qed
  moreover have "c *\<^sub>C x \<in> closure S"
    if "x \<in> closure S"
    for x :: 'a
      and c :: complex
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
      using assms that
      by (simp add: complex_vector.subspace_scale subspace_cl) 
  qed
  moreover have "0 \<in> closure S"
    by (metis \<open>\<And>x c. x \<in> closure S \<Longrightarrow> c *\<^sub>C x \<in> closure S\<close> all_not_in_conv assms closure_eq_empty complex_vector.scale_zero_left complex_vector.subspace_def)    
  moreover have "closed (closure S)"
    by auto
  ultimately show ?thesis
    by (simp add: \<open>\<And>x c. x \<in> closure S \<Longrightarrow> c *\<^sub>C x \<in> closure S\<close> \<open>\<And>y x. \<lbrakk>x \<in> closure S; y \<in> closure S\<rbrakk> \<Longrightarrow> x + y \<in> closure S\<close> assms closed_subspace.intro subspace_cl) 
qed

lemma bounded_linear_continuous:
  assumes \<open>cbounded_linear f\<close> 
  shows \<open>isCont f x\<close>
  by (simp add: assms cbounded_linear.bounded_linear linear_continuous_at)

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
    using that
    using less_eq_linear_space.rep_eq by auto 
  show "(x::'a linear_space) = y"
    if "(x::'a linear_space) \<le> y"
      and "(y::'a linear_space) \<le> x"
    for x :: "'a linear_space"
      and y :: "'a linear_space"
    using that
    by (simp add: space_as_set_inject less_eq_linear_space.rep_eq) 
qed
end

lemma id_cbounded_linear: \<open>cbounded_linear id\<close>
  by (rule Complex_Vector_Spaces.cbounded_linear_ident)

lemma bounded_sesquilinear_diff:
  \<open>bounded_sesquilinear A \<Longrightarrow> bounded_sesquilinear B \<Longrightarrow> bounded_sesquilinear (\<lambda> x y. A x y - B x y)\<close>
proof
  show "A (a + a') b - B (a + a') b = A a b - B a b + (A a' b - B a' b)"
    if "bounded_sesquilinear A"
      and "bounded_sesquilinear B"
    for a :: 'a
      and a' :: 'a
      and b :: 'b
    using that
    by (simp add: bounded_sesquilinear.add_left) 
  show "A a (b + b') - B a (b + b') = A a b - B a b + (A a b' - B a b')"
    if "bounded_sesquilinear A"
      and "bounded_sesquilinear B"
    for a :: 'a
      and b :: 'b
      and b' :: 'b
    using that
    by (simp add: bounded_sesquilinear.add_right) 
  show "A (r *\<^sub>C a) b - B (r *\<^sub>C a) b = cnj r *\<^sub>C (A a b - B a b)"
    if "bounded_sesquilinear A"
      and "bounded_sesquilinear B"
    for r :: complex
      and a :: 'a
      and b :: 'b
    using that
    by (simp add: bounded_sesquilinear.scaleC_left complex_vector.scale_right_diff_distrib) 
  show "A a (r *\<^sub>C b) - B a (r *\<^sub>C b) = r *\<^sub>C (A a b - B a b)"
    if "bounded_sesquilinear A"
      and "bounded_sesquilinear B"
    for a :: 'a
      and r :: complex
      and b :: 'b
    using that
    by (simp add: bounded_sesquilinear.scaleC_right complex_vector.scale_right_diff_distrib) 
  show "\<exists>K. \<forall>a b. norm (A a b - B a b) \<le> norm a * norm b * K"
    if "bounded_sesquilinear A"
      and "bounded_sesquilinear B"
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
  shows \<open>\<exists> f. \<exists> s\<in>V. s = (\<Sum>v\<in>V-{s}. f v *\<^sub>C v )\<close>
proof-
  from \<open>complex_vector.dependent V\<close>
  have \<open>\<exists>T f. finite T \<and>
           T \<subseteq> V \<and> (\<Sum>i\<in>T. f i *\<^sub>C i) = 0 \<and> (\<exists>i\<in>T. f i \<noteq> 0)\<close>
    using complex_vector.dependent_explicit
    by blast
  hence \<open>\<exists>f. (\<Sum>i\<in>V. f i *\<^sub>C i) = 0 \<and> (\<exists> i\<in>V. f i \<noteq> 0)\<close>
    using \<open>complex_vector.dependent V\<close> \<open>finite V\<close> complex_vector.independent_if_scalars_zero by fastforce
  show \<open>\<exists> f. \<exists> s\<in>V. s = (\<Sum>v\<in>V-{s}. f v *\<^sub>C v )\<close>
  proof-
    from \<open>\<exists>f. (\<Sum>i\<in>V. f i *\<^sub>C i) = 0 \<and> (\<exists> i\<in>V. f i \<noteq> 0)\<close>
    obtain f where  \<open>(\<Sum>i\<in>V. f i *\<^sub>C i) = 0\<close> and \<open>\<exists> i\<in>V. f i \<noteq> 0\<close>
      by blast
    from \<open>\<exists> i\<in>V. f i \<noteq> 0\<close>
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
  where \<open>cbilinear \<equiv> (\<lambda> f. (\<forall> y. clinear (\<lambda> x. f x y)) \<and> (\<forall> x. clinear (\<lambda> y. f x y)) )\<close>

lemma cbilinear_from_product_clinear:
  fixes g' :: \<open>'a::complex_vector \<Rightarrow> complex\<close> and g :: \<open>'b::complex_vector \<Rightarrow> complex\<close>
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
  assumes \<open>complex_vector.independent A\<close> and \<open>complex_vector.independent B\<close>
    and \<open>u \<in> A\<close> and \<open>v \<in> B\<close>
  shows \<open>\<exists> h::_\<Rightarrow>_\<Rightarrow>complex. cbilinear h \<and> (h u v = 1) \<and>
    (\<forall>x\<in>A. \<forall>y\<in>B. (x,y) \<noteq> (u,v) \<longrightarrow> h x y = 0)\<close>
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
        using \<open>u \<in> A\<close>
        by (simp add: \<open>\<forall>x\<in>A. g' x = f' x\<close>)
      also have \<open>\<dots> = 1\<close>
        by (simp add: f'_def)
      finally show ?thesis by blast
    qed
    moreover have \<open>g v = 1\<close>
    proof-
      have \<open>g v = f v\<close>
        using \<open>v \<in> B\<close>
        by (simp add: \<open>\<forall>x\<in>B. g x = f x\<close>)
      also have \<open>\<dots> = 1\<close>
        by (simp add: f_def)
      finally show ?thesis by blast
    qed
    ultimately show ?thesis unfolding h_def by auto
  qed
  moreover have \<open>x\<in>A \<Longrightarrow> y\<in>B \<Longrightarrow> (x,y) \<noteq> (u,v) \<Longrightarrow> h x y = 0\<close>
    for x y
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
  assumes \<open>z \<in> complex_vector.span T\<close>
  shows \<open>\<exists> S. finite S \<and> S \<subseteq> T \<and> z \<in> complex_vector.span S\<close>
proof-
  have \<open>\<exists> S r. finite S \<and> S \<subseteq> T \<and> z = (\<Sum>a\<in>S. r a *\<^sub>C a)\<close>
    using complex_vector.span_explicit[where b = "T"]
      assms by auto
  then obtain S r where \<open>finite S\<close> and \<open>S \<subseteq> T\<close> and \<open>z = (\<Sum>a\<in>S. r a *\<^sub>C a)\<close>
    by blast
  thus ?thesis
    by (meson complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset subset_iff) 
qed

lemma span_explicit_finite:
  assumes a1: \<open>x \<in> complex_vector.span S\<close> 
    and a2: \<open>complex_vector.independent S\<close>
    and a3: \<open>finite S\<close>
  shows \<open>\<exists> t. x = (\<Sum>s\<in>S. t s *\<^sub>C s)\<close>
proof-
  have \<open>\<exists> T t'. finite T \<and> T \<subseteq> S \<and> x = (\<Sum>s\<in>T. t' s *\<^sub>C s)\<close>
    using a1 complex_vector.span_explicit[where b = S]
    by auto
  then obtain T t' where \<open>finite T\<close> and \<open>T \<subseteq> S\<close> and
    \<open>x = (\<Sum>s\<in>T. t' s *\<^sub>C s)\<close>
    by blast
  define t where \<open>t s = (if s\<in>T then t' s else 0)\<close> for s
  have \<open>(\<Sum>s\<in>T. t s *\<^sub>C s) + (\<Sum>s\<in>S-T. t s *\<^sub>C s)
    = (\<Sum>s\<in>S. t s *\<^sub>C s)\<close>
    using \<open>T \<subseteq> S\<close>
    by (metis (no_types, lifting) assms(3) ordered_field_class.sign_simps(2) sum.subset_diff)
  moreover have \<open>(\<Sum>s\<in>S-T. t s *\<^sub>C s) = 0\<close>
  proof-
    have \<open>s\<in>S-T \<Longrightarrow> t s *\<^sub>C s = 0\<close>
      for s
    proof-
      assume \<open>s\<in>S-T\<close>
      hence \<open>t s = 0\<close>
        unfolding t_def
        by auto
      thus ?thesis by auto
    qed
    thus ?thesis
      by (simp add: sum.neutral) 
  qed
  ultimately have \<open>x = (\<Sum>s\<in>S. t s *\<^sub>C s)\<close>
    using \<open>x = (\<Sum>s\<in>T. t' s *\<^sub>C s)\<close> t_def by auto
  thus ?thesis by blast
qed


subsection \<open>Recovered theorems\<close>

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
  by (simp_all add: divide_inverse_commute scaleC_add_right complex_vector.scale_right_diff_distrib)


lemma linear_space_leI:
  assumes "\<And>x. x \<in> space_as_set A \<Longrightarrow> x \<in> space_as_set B"
  shows "A \<le> B"
  using assms apply transfer by auto

(* lemma finite_sum_tendsto:
  fixes A::\<open>('a::cbanach) set\<close>
  assumes  \<open>\<forall> a \<in> A. (\<lambda> n. r n a) \<longlonglongrightarrow> \<phi> a\<close> and \<open>finite A\<close>
  shows \<open>(\<lambda> n. (\<Sum>a\<in>A. r n a *\<^sub>C a)) \<longlonglongrightarrow>  (\<Sum>a\<in>A. \<phi> a *\<^sub>C a)\<close>
  using finite_sum_tendsto' assms by blast *)

(* TODO: José, please compare this with your proof of finite_sum_tendsto
   to see how inductions over finite sets are easier to do than by 
   induction over the cardinality. 

   TODO: Replace finite_sum_tendsto by this.

Jose: It is not possible to deduce finite_sum_tendsto from finite_sum_tendsto in 
an via sledgehammer. Hence, finite_sum_tendsto and finite_sum_tendsto are not
pre-equivalent.

I define two theorems A and B to be pre-equivalent if and only if
theorem A can be obtained from theorem B using sledgehammer and 
theorem B can be obtained from theorem A using sledgehammer.

Notice that this is not an equivalent relation, because transitivity may fail.

*)

lemma finite_sum_tendsto:
  fixes A::\<open>'a set\<close> and r :: "'a \<Rightarrow> nat \<Rightarrow> 'b::{comm_monoid_add,topological_monoid_add}"
  assumes  \<open>\<And>a. a \<in> A \<Longrightarrow> r a \<longlonglongrightarrow> \<phi> a\<close> 
  assumes \<open>finite A\<close>
  shows \<open>(\<lambda> n. (\<Sum>a\<in>A. r a n)) \<longlonglongrightarrow>  (\<Sum>a\<in>A. \<phi> a)\<close>
  apply (insert assms(1)) using \<open>finite A\<close>
proof induction
  case empty
  show ?case 
    by auto
next
  case (insert x F)
  then have "r x \<longlonglongrightarrow> \<phi> x" and "(\<lambda>n. \<Sum>a\<in>F. r a n) \<longlonglongrightarrow> sum \<phi> F"
    by auto
  then have "(\<lambda>n. r x n + (\<Sum>a\<in>F. r a n)) \<longlonglongrightarrow> \<phi> x + sum \<phi> F"
    using tendsto_add by blast
  then show ?case 
    using sum.insert insert by auto
qed

lemma (in bounded_cbilinear) tendsto:
  "(f \<longlongrightarrow> a) F \<Longrightarrow> (g \<longlongrightarrow> b) F \<Longrightarrow> ((\<lambda>x. prod (f x) (g x)) \<longlongrightarrow> prod a b) F"
  by (rule tendsto)
 
lemmas tendsto_scaleC [tendsto_intros] =
  bounded_cbilinear.tendsto [OF bounded_cbilinear_scaleC]


lemma independent_real_complex: 
  assumes "complex_vector.independent (S::'a::complex_vector set)" and "finite S"
  shows "real_vector.independent S"
  using assms
proof(induction "card S" arbitrary: S)
  case 0
  hence "card S = 0"
    by auto    
  hence "S = ({}::'a set)"
    using "0.prems"(2) card_0_eq by blast    
  moreover have "real_vector.independent ({}::'a set)"
    by (metis Real_Vector_Spaces.dependent_raw_def real_vector.independent_empty)    
  ultimately show ?case by simp
next
  case (Suc n)
  have "\<exists>s S'. S = insert s S' \<and> s \<notin> S'"
    by (metis Suc.hyps(2) card_le_Suc_iff order_refl)
  then obtain s S' where g1: "S = insert s S'" and g2: "s \<notin> S'"
    by blast
  have "card S' = n"
    using Suc.hyps(2) Suc.prems(2) g1 g2 by auto
  moreover have "finite S'"
    using Suc.prems(2) g1 by auto
  moreover have "complex_vector.independent S'"
    by (metis Complex_Vector_Spaces.dependent_raw_def Suc.prems(1) complex_vector.independent_insert g1 g2)
  ultimately have "real_vector.independent S'"
    by (simp add: Real_Vector_Spaces.dependent_raw_def Suc.hyps(1))
  moreover have "s \<notin> real_vector.span S'"
  proof(rule classical)
    assume "\<not>(s \<notin> real_vector.span S')"
    hence "s \<in> real_vector.span S'"
      by blast
    hence "\<exists> r R. s = (sum (\<lambda>s'. r s' *\<^sub>R s' ) R) \<and> R \<subseteq> S'"
      by (smt mem_Collect_eq real_vector.span_explicit real_vector.span_explicit')
    then obtain r R where s1: "s = (sum (\<lambda>s'. r s' *\<^sub>R s' ) R)" and s2: "R \<subseteq> S'"
      by blast
    have "s = (sum (\<lambda>s'. r s' *\<^sub>C s' ) R)"
      using s1
      by (metis (no_types, lifting) scaleR_scaleC sum.cong) 
    hence "s \<in> complex_vector.span S'"
      using  s2
      by (meson complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset in_mono) 
    thus ?thesis 
      by (smt Complex_Vector_Spaces.dependent_raw_def Suc.prems(1) complex_vector.independent_insert 
          g1 g2)
  qed
  ultimately show ?case 
    by (smt Real_Vector_Spaces.dependent_raw_def g1 real_vector.independent_insertI)
qed


end
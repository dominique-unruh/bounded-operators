section \<open>Complex Vector Spaces\<close>

(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)

theory Complex_Vector_Spaces
  imports 
    "HOL-Analysis.Elementary_Topology"
    "HOL-Analysis.Operator_Norm"
    "HOL-Analysis.Elementary_Normed_Spaces"
    "HOL-Library.Set_Algebras"
    "HOL-Analysis.Starlike"
    "HOL-Types_To_Sets.Types_To_Sets"

    "Bounded_Operators-Extra.Extra_Nonstandard_Analysis"
    "Bounded_Operators-Extra.Extra_Vector_Spaces"
    "Bounded_Operators-Extra.Extra_Ordered_Fields"
    "Bounded_Operators-Extra.Extra_Lattice"
    "Bounded_Operators-Extra.Extra_General"

    Complex_Vector_Spaces0
begin

bundle notation_norm begin
notation norm ("\<parallel>_\<parallel>")
end

lemma scaleC_real (in scaleC): assumes "r\<in>\<real>" shows "r *\<^sub>C x = Re r *\<^sub>R x"
  unfolding scaleR_scaleC using assms by simp

subclass (in complex_vector) real_vector
  by (standard, simp_all add: scaleR_scaleC scaleC_add_right scaleC_add_left)

subclass (in complex_algebra) real_algebra
  by (standard, simp_all add: scaleR_scaleC)


subclass (in complex_algebra_1) real_algebra_1 ..

subclass (in complex_div_algebra) real_div_algebra ..

class complex_field = complex_div_algebra + field

subclass (in complex_field) real_field ..

subsection \<open>Bounded Linear and Bilinear Operators\<close>


lemma sum_constant_scaleC: "(\<Sum>x\<in>A. y) = of_nat (card A) *\<^sub>C y"
  for y :: "'a::complex_vector"
  by (induct A rule: infinite_finite_induct) (simp_all add: algebra_simps)

subsection \<open>Embedding of the Complex Numbers into any \<open>complex_algebra_1\<close>: \<open>of_complex\<close>\<close>





text \<open>Collapse nested embeddings.\<close>

lemma of_complex_of_real_eq [simp]: "of_complex (of_real n) = of_real n"
  unfolding of_complex_def of_real_def unfolding scaleR_scaleC by simp






subsection \<open>The Set of Complex Numbers\<close>


lemma Complexs_of_real [simp]: "of_real r \<in> \<complex>"
  unfolding Complexs_def of_real_def of_complex_def 
  apply (subst scaleR_scaleC) by simp

lemma Reals_in_Complexs: "\<real> \<subseteq> \<complex>"
  unfolding Reals_def by auto

lemma Complexs_cases [cases set: Complexs]:
  assumes "q \<in> \<complex>"
  obtains (of_complex) r where "q = of_complex r"
  unfolding Complexs_def
proof -
  from \<open>q \<in> \<complex>\<close> have "q \<in> range of_complex" unfolding Complexs_def .
  then obtain r where "q = of_complex r" ..
  thus thesis ..
qed

subsection \<open>Ordered complex vector spaces\<close>


subclass (in ordered_complex_vector) ordered_real_vector
proof
  show "a *\<^sub>R x \<le> a *\<^sub>R y"
    if "x \<le> y"
      and "0 \<le> a"
    for x :: 'a
      and y :: 'a
      and a :: real
    using that
    by (simp add: local.scaleC_left_mono local.scaleR_scaleC) 
  show "a *\<^sub>R x \<le> b *\<^sub>R x"
    if "a \<le> b"
      and "0 \<le> x"
    for a :: real
      and b :: real
      and x :: 'a
    using that
    by (simp add: local.scaleC_right_mono local.scaleR_scaleC) 
qed

(* lemma pos_le_divideRI:
  assumes "0 < c"
    and "c *\<^sub>C a \<le> b"
  shows "a \<le> b /\<^sub>C c"
proof -
  have "a = inverse c *\<^sub>C c *\<^sub>C a" using assms(1)
    by (smt (verit, best) local.scaleC_one local.scaleC_scaleC mult.commute preorder_class.less_irrefl right_inverse)
  also have "\<dots> \<le> inverse c *\<^sub>C b"
  proof (rule scaleC_left_mono)
    show "c *\<^sub>C a \<le> b"
      by (simp add: assms(2))    
    show "0 \<le> inverse c"
      using assms(1) by force
  qed 
  finally show ?thesis by simp
qed *)

end (* class ordered_complex_vector *)

lemma reals_zero_comparable_iff:
  "(x::complex)\<in>\<real> \<longleftrightarrow> x \<le> 0 \<or> x \<ge> 0"
  unfolding complex_is_Real_iff less_eq_complex_def
  by auto

lemma reals_zero_comparable:
  fixes x::complex
  assumes "x\<in>\<real>"
  shows "x \<le> 0 \<or> x \<ge> 0"
  using assms unfolding reals_zero_comparable_iff by assumption

subsection \<open>Complex normed vector spaces\<close>

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
proof
  show "cmod (a *\<^sub>C x) = cmod a * cmod x"
    for a :: complex
      and x :: complex
    by (simp add: norm_mult)
qed

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
proof (rule linearI)
  show "f (b1 + b2) = f b1 + f b2"
    for b1 :: 'a
      and b2 :: 'a
    by (simp add: add)    
  show "f (r *\<^sub>R b) = r *\<^sub>R f b"
    for r :: real
      and b :: 'a
    unfolding scaleR_scaleC by (subst scaleC, simp)  
qed

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

(* TODO: remove *)
(* lemma csemilinear_times_of_complex: "csemilinear (\<lambda>x. cnj (a * of_complex x))"
proof (simp add: csemilinear_def additive_def csemilinear_axioms_def)
  show "Modules.additive (\<lambda>x. cnj a * cnj x)"
    by (simp add: distrib_left additive.intro)
qed *)


lemma csemilinearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>C x) = cnj c *\<^sub>C f x"
  shows "csemilinear f"
  by standard (rule assms)+



lemma csemilinear_csemilinear: "csemilinear f \<Longrightarrow> csemilinear g \<Longrightarrow> clinear (g o f)"
  apply (rule clinearI)
  apply (simp add: additive.add csemilinear_def)
  by (simp add: csemilinear.scaleC)

lemma csemilinear_clinear: "csemilinear f \<Longrightarrow> clinear g \<Longrightarrow> csemilinear (g o f)"
  apply (rule csemilinearI)
  apply (simp add: additive.add clinear_additive_D csemilinear_def)
  by (simp add: complex_vector.linear_scale csemilinear.scaleC)

lemma clinear_csemilinear: "clinear f \<Longrightarrow> csemilinear g \<Longrightarrow> csemilinear (g o f)"
  apply (rule csemilinearI)
  apply (simp add: additive.add clinear_additive_D csemilinear_def)
  by (simp add: complex_vector.linear_scale csemilinear.scaleC)


locale bounded_csemilinear = csemilinear f for f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
begin

sublocale bounded_linear
proof
  show "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
    by (fact bounded) 
qed


lemma bounded_linear: "bounded_linear f"
  by (fact bounded_linear)

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
proof (rule bounded_csemilinear_intro [where K = 1])
  show "cnj (x + y) = cnj x + cnj y"
    for x :: complex
      and y :: complex
    by simp    
  show "cnj (r *\<^sub>C x) = cnj r *\<^sub>C cnj x"
    for r :: complex
      and x :: complex
    by simp    
  show "cmod (cnj x) \<le> cmod x * 1"
    for x :: complex
    by simp    
qed


lemma bounded_csemilinear_compose1:
  assumes "bounded_csemilinear f"
    and "bounded_csemilinear g"
  shows "cbounded_linear (\<lambda>x. f (g x))"
proof-
  interpret f: bounded_csemilinear f by fact
  interpret g: bounded_csemilinear g by fact
  show ?thesis
  proof 

    have "f (g (b1 + b2)) = f (g b1) + f (g b2)"
      for b1 :: 'c
        and b2 :: 'c
      by (simp add: f.add g.add)
    moreover have "f (g (r *\<^sub>C b)) = r *\<^sub>C f (g b)"
      for r :: complex
        and b :: 'c
      by (simp add: f.scaleC g.scaleC)
    ultimately have "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) (\<lambda>x. f (g x))"
      by (meson clinearI clinear_def)      
    thus "clinear (\<lambda>x. f (g x))"
      unfolding clinear_def
      by blast
    have "\<exists> Kf. \<forall>x. norm (f (g x)) \<le> norm (g x) * Kf"
      using f.pos_bounded by auto
    then obtain Kf where \<open>\<forall>x. norm (f (g x)) \<le> norm (g x) * Kf\<close>
      by blast        
    have "\<exists> Kg. \<forall>x. norm (g x) * Kf \<le> (norm x * Kg) * Kf"
      by (metis g.pos_bounded le_cases mult.commute mult_left_mono norm_ge_zero vector_space_over_itself.scale_zero_left)
    then obtain Kg where \<open>\<forall>x. norm (g x) * Kf \<le> (norm x * Kg) * Kf\<close>
      by blast
    have \<open>\<forall>x. (norm x * Kg) * Kf = norm x * (Kg * Kf)\<close>
      using mult.assoc
      by simp 
    define  K where \<open>K = Kg * Kf\<close>
    have  \<open>\<forall>x. norm (f (g x)) \<le> norm x * K\<close>
      unfolding K_def
      by (metis K_def \<open>\<forall>x. norm (f (g x)) \<le> norm (g x) * Kf\<close> \<open>\<forall>x. norm (g x) * Kf \<le> norm x * Kg * Kf\<close> \<open>\<forall>x. norm x * Kg * Kf = norm x * (Kg * Kf)\<close> dual_order.trans) 
    thus "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
      by blast
  qed
qed

lemma bounded_csemilinear_compose2:
  assumes "bounded_csemilinear f"
    and "cbounded_linear g"
  shows "bounded_csemilinear (\<lambda>x. f (g x))"
proof -
  interpret f: bounded_csemilinear f by fact
  interpret g: cbounded_linear g by fact
  from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
    by blast
  from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
    by blast
  define K where "K = Kg * Kf"
  have x: "norm (f (g x)) \<le> norm x * K" 
    for x
  proof-
    have "norm (f (g x)) \<le> norm (g x) * Kf"
      using f .
    also have "\<dots> \<le> (norm x * Kg) * Kf"
      using g Kf [THEN order_less_imp_le] by (rule mult_right_mono)
    also have "(norm x * Kg) * Kf = norm x * (Kg * Kf)"
      by (rule mult.assoc)
    finally show "norm (f (g x)) \<le> norm x * K"
      unfolding K_def.
  qed

  have "f (g (x + y)) = f (g x) + f (g y)" for x y
    by (simp only: f.add g.add)
  moreover have "f (g (scaleC r x)) = scaleC (cnj r) (f (g x))" for r x
    by (simp add: complex_vector.linear_scale f.scaleC g.is_clinear)    
  moreover have "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    using x by (intro exI allI)
  ultimately  show ?thesis
    by (meson bounded_csemilinear_intro)  
qed

lemma bounded_csemilinear_compose3:
  assumes "cbounded_linear f"
    and "bounded_csemilinear g"
  shows "bounded_csemilinear (\<lambda>x. f (g x))"
proof -
  interpret f: cbounded_linear f by fact
  interpret g: bounded_csemilinear g by fact

  have s3: "f (g (x + y)) = f (g x) + f (g y)" for x y
    by (simp only: f.add g.add)
  have s2: "f (g (scaleC r x)) = scaleC (cnj r) (f (g x))" for r x
    using complex_vector.linear_scale f.is_clinear g.scaleC by auto
  from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
    by blast
  from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
    by blast
  have s1: "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
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
  show ?thesis
    apply unfold_locales
    using s1 s2 s3 by auto
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
proof
  show "prod (a + a') b = prod a b + prod a' b"
    for a :: 'a
      and a' :: 'a
      and b :: 'b
    by (simp add: add_left)

  show "prod a (b + b') = prod a b + prod a b'"
    for a :: 'a
      and b :: 'b
      and b' :: 'b
    by (simp add: add_right)

  show "prod (r *\<^sub>R a) b = r *\<^sub>R prod a b"
    for r :: real
      and a :: 'a
      and b :: 'b
    unfolding scaleR_scaleC
    by (fact scaleC_left)

  show "prod a (r *\<^sub>R b) = r *\<^sub>R prod a b"
    for a :: 'a
      and r :: real
      and b :: 'b
    unfolding scaleR_scaleC
    by (fact scaleC_right)

  show "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    by (fact bounded)
qed


lemma bounded_bilinear: "bounded_bilinear prod"
  by (simp add: bounded_bilinear_axioms)

lemma cbounded_linear_left: "cbounded_linear (\<lambda>a. prod a b)"
proof (insert bounded)
  have a1: "cbounded_linear (\<lambda>a. prod a b)"
    if "\<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    for K :: real
  proof
    have "prod (b1 + b2) b = prod b1 b + prod b2 b"
      for b1 :: 'a
        and b2 :: 'a
      by (simp add: add_left)      
    moreover have "prod (r *\<^sub>C x) b = r *\<^sub>C prod x b"
      for r :: complex
        and x :: 'a
      by (simp add: scaleC_left)      
    ultimately show "clinear (\<lambda>a. prod a b)"
      unfolding clinear_def
      by (meson clinearI clinear_def) 
    show "\<exists>K. \<forall>x. norm (prod x b) \<le> norm x * K"
      using ab_semigroup_mult_class.mult_ac(1)
      by (metis that)
  qed
  show "cbounded_linear (\<lambda>a. prod a b)"
    if "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    using a1 that by blast
qed

lemma cbounded_linear_right: "cbounded_linear (\<lambda>b. prod a b)"
proof (insert bounded)
  have "cbounded_linear (prod a)"
    if "\<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    for K :: real
    using that 
  proof (rule_tac K = "norm a * K" in cbounded_linear_intro)
    show "prod a (x + y) = prod a x + prod a y"
      if "\<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
      for x :: 'b
        and y :: 'b
      using that add_right by auto 
    show "prod a (r *\<^sub>C x) = r *\<^sub>C prod a x"
      if "\<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
      for r :: complex
        and x :: 'b
      using that
      by (simp add: scaleC_right) 
    show "norm (prod a x) \<le> norm x * (norm a * K)"
      if "\<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
      for x :: 'b
      using that
      by (simp add: ab_semigroup_mult_class.mult_ac(1) mult.left_commute) 
  qed
  thus "cbounded_linear (prod a)"
    if "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    using that by auto
qed

lemma flip: "bounded_cbilinear (\<lambda>x y. prod y x)"
proof
  show "prod b (a + a') = prod b a + prod b a'"
    for a :: 'b
      and a' :: 'b
      and b :: 'a
    by (simp add: add_right)

  show "prod (b + b') a = prod b a + prod b' a"
    for a :: 'b
      and b :: 'a
      and b' :: 'a
    by (simp add: add_left)

  show "prod b (r *\<^sub>C a) = r *\<^sub>C prod b a"
    for r :: complex
      and a :: 'b
      and b :: 'a
    by (simp add: scaleC_right)

  show "prod (r *\<^sub>C b) a = r *\<^sub>C prod b a"
    for a :: 'b
      and r :: complex
      and b :: 'a
    by (simp add: bounded_cbilinear.scaleC_left bounded_cbilinear_axioms)

  show "\<exists>K. \<forall>a b. norm (prod b a) \<le> norm a * norm b * K"
    by (metis pos_bounded vector_space_over_itself.scale_left_commute 
        vector_space_over_itself.scale_scale)    
qed


lemma comp1:
  assumes "cbounded_linear g"
  shows "bounded_cbilinear (\<lambda>x. prod (g x))"
proof unfold_locales
  interpret g: cbounded_linear g by fact
  write prod (infixl "***" 70)
  show "\<And>a a' b. g (a + a') *** b = g a *** b + g a' *** b"
    by (simp add: add_left g.add)
  show "\<And>a b b'. g a *** (b + b') = g a *** b + g a *** b'"
    by (simp add: add_right)
  show "\<And>r a b. g (r *\<^sub>C a) *** b = r *\<^sub>C (g a *** b)"
    by (simp add: complex_vector.linear_scale g.is_clinear scaleC_left)
  show  "\<And>a r b. g a *** (r *\<^sub>C b) = r *\<^sub>C (g a *** b)"
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
proof auto
  show "clinear (id::'a \<Rightarrow> _)"
    by (simp add: complex_vector.module_hom_id)

  show "\<exists>K. \<forall>x. norm (x::'a) \<le> norm x * K"
    using less_eq_real_def by auto    
qed

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
  have a1: "clinear (\<lambda>x. f x + g x)"
    by (simp add: clinearI complex_vector.linear_scale f.add f.is_clinear g.add g.is_clinear 
        scaleC_add_right)
  have a2: "\<exists>K. \<forall>x. norm (f x + g x) \<le> norm x * K"
    using add_mono[OF Kf Kg]
    by (intro exI[of _ "Kf + Kg"]) (auto simp: field_simps intro: norm_triangle_ineq order_trans)
  show ?thesis
    using a1 a2
    by (simp add: cbounded_linear_def) 
qed

lemma cbounded_linear_minus:
  assumes "cbounded_linear f"
  shows "cbounded_linear (\<lambda>x. - f x)"
proof -
  interpret f: cbounded_linear f by fact
  have "clinear (\<lambda>x. - f x)"
    by (simp add: complex_vector.linear_compose_neg f.is_clinear)
  moreover have "\<exists>K. \<forall>x. norm (- f x) \<le> norm x * K"
    using f.pos_bounded by auto    
  ultimately show ?thesis
    by (simp add: cbounded_linear_def)
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

  have "f (g (b1 + b2)) = f (g b1) + f (g b2)"
    for b1 :: 'c
      and b2 :: 'c
    by (simp add: f.add g.add)
  moreover have "f (g (r *\<^sub>C b)) = r *\<^sub>C f (g b)"
    for r :: complex
      and b :: 'c
    by (simp add: complex_vector.linear_scale f.is_clinear g.is_clinear)
  ultimately have u1: "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) (\<lambda>x. f (g x))"
    by (meson clinearI clinear_def)    
  hence u3:"clinear (\<lambda>x. f (g x))"
    unfolding clinear_def
    by auto

  from f.pos_bounded obtain Kf where f: "\<And>x. norm (f x) \<le> norm x * Kf" and Kf: "0 < Kf"
    by blast
  from g.pos_bounded obtain Kg where g: "\<And>x. norm (g x) \<le> norm x * Kg"
    by blast
  have u2: "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
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

  show ?thesis
  proof
    show "clinear (\<lambda>x. f (g x))"
      using u3.
    show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
      using u2.   
  qed  
qed


lemma bounded_cbilinear_mult: "bounded_cbilinear ((*) :: 'a \<Rightarrow> 'a \<Rightarrow> 'a::complex_normed_algebra)"
proof (rule bounded_cbilinear.intro)
  show "(a + a') * b = a * b + a' * b"
    for a :: 'a
      and a' :: 'a
      and b :: 'a
    by (simp add: distrib_right)

  show "a * (b + b') = a * b + a * b'"
    for a :: 'a
      and b :: 'a
      and b' :: 'a
    by (simp add: distrib_left)

  show "r *\<^sub>C a * b = r *\<^sub>C (a * b)"
    for r :: complex
      and a :: 'a
      and b :: 'a
    by simp

  show "a * r *\<^sub>C b = r *\<^sub>C (a * b)"
    for a :: 'a
      and r :: complex
      and b :: 'a
    by simp

  show "\<exists>K. \<forall>a b. norm ((a::'a) * b) \<le> norm a * norm b * K"
  proof (rule_tac x = "1" in exI)
    show "\<forall>a b. norm ((a::'a) * b) \<le> norm a * norm b * 1"
      by (simp add: norm_mult_ineq)
  qed
qed


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
proof (rule bounded_cbilinear.intro)
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

  show "(r *\<^sub>C a) *\<^sub>C b = r *\<^sub>C a *\<^sub>C b"
    for r :: complex
      and a :: complex
      and b :: 'a
    by simp

  show "a *\<^sub>C r *\<^sub>C b = r *\<^sub>C a *\<^sub>C b"
    for a :: complex
      and r :: complex
      and b :: 'a
    by simp

  show "\<exists>K. \<forall>a b::'a. norm (a *\<^sub>C b) \<le> cmod a * norm b * K"
    by (metis eq_iff mult.commute norm_scaleC vector_space_over_itself.scale_one)    
qed

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
proof
  show "\<exists>c. f = (\<lambda>x. x * c)"
    if "cbounded_linear f"
    using that complex_scaleC_def complex_vector.linear_scale 
      mult.comm_neutral
    by (metis (no_types, hide_lams) cbounded_linear.is_clinear)

  show "cbounded_linear f"
    if "\<exists>c. f = (\<lambda>x. x * c)"
    using that cbounded_linear_mult_left by auto 
qed

lemma bij_clinear_imp_inv_clinear: "clinear (inv f)"
  if a1: "clinear f" and a2: "bij f"
proof-
  have "f a + f b = f (a + b)"
    for a b
    by (simp add: a1 complex_vector.linear_add)    
  hence t1: "inv f (b1 + b2) = inv f b1 + inv f b2"
    for b1 :: 'b
      and b2 :: 'b
    by (metis (no_types) bij_inv_eq_iff that(2))
  have t2: "inv f (r *\<^sub>C b) = r *\<^sub>C inv f b"
    if "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) f"
      and "bij f"
    for r :: complex
      and b :: 'b
    using that
    by (smt bij_inv_eq_iff clinear_def complex_vector.linear_scale) 
  show ?thesis
    unfolding clinear_def
    by (meson clinearI clinear_def a1 a2 t1 t2)
qed

locale bounded_sesquilinear =
  fixes 
    prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleC_left: "prod (r *\<^sub>C a) b = (cnj r) *\<^sub>C (prod a b)"
    and scaleC_right: "prod a (r *\<^sub>C b) = r *\<^sub>C (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
begin

sublocale bounded_bilinear
proof
  show "prod (a + a') b = prod a b + prod a' b"
    for a :: 'a
      and a' :: 'a
      and b :: 'b
    by (simp add: add_left)

  show "prod a (b + b') = prod a b + prod a b'"
    for a :: 'a
      and b :: 'b
      and b' :: 'b
    by (simp add: add_right)

  show "prod (r *\<^sub>R a) b = r *\<^sub>R prod a b"
    for r :: real
      and a :: 'a
      and b :: 'b
    unfolding scaleR_scaleC
    by (simp add: scaleC_left)

  show "prod a (r *\<^sub>R b) = r *\<^sub>R prod a b"
    for a :: 'a
      and r :: real
      and b :: 'b
    unfolding scaleR_scaleC
    by (fact scaleC_right)

  show "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    unfolding scaleR_scaleC
    by (fact bounded)
qed


lemma bounded_bilinear: "bounded_bilinear prod" by (fact bounded_bilinear_axioms)

lemma bounded_csemilinear_left: "bounded_csemilinear (\<lambda>a. prod a b)"
proof (insert bounded)

  have "prod (x + y) b = prod x b + prod y b"
    for x :: 'a
      and y :: 'a
    by (simp add: add_left)      
  moreover have "prod (r *\<^sub>C x) b = cnj r *\<^sub>C prod x b"
    for r :: complex
      and x :: 'a
    by (simp add: scaleC_left)      
  moreover have "norm (prod x b) \<le> norm x * (norm b * K)"
    if "\<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    for K :: real and x :: 'a
    by (simp add: that vector_space_over_itself.scale_scale)
  ultimately  have "bounded_csemilinear (\<lambda>a. prod a b)"
    if "\<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    for K :: real
    by (meson bounded_csemilinear_intro that) 
  thus "bounded_csemilinear (\<lambda>a. prod a b)"
    if "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    using that by safe    
qed

lemma cbounded_linear_right: "cbounded_linear (\<lambda>b. prod a b)"
proof (insert bounded)
  have "prod a (x + y) = prod a x + prod a y"
    for x :: 'b
      and y :: 'b
    by (simp add: add_right)    
  moreover have "prod a (r *\<^sub>C x) = r *\<^sub>C prod a x"
    for r :: complex
      and x :: 'b
    by (simp add: scaleC_right)    
  moreover have "norm (prod a x) \<le> norm x * (norm a * K)"
    if "\<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    for x :: 'b and K
    by (simp add: that vector_space_over_itself.scale_left_commute 
        vector_space_over_itself.scale_scale)        
  ultimately have "cbounded_linear (prod a)"
    if "\<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    for K
    by (meson cbounded_linear_intro nonneg_bounded)    
  thus "cbounded_linear (prod a)"
    if "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"
    using that
    by blast
qed

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
      using nonneg_bounded by blast    
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
      using nonneg_bounded by auto    
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
        using  \<open>\<And> a. norm (g a) \<le> norm a * M\<close> \<open>M \<ge> 0\<close> \<open>N \<ge> 0\<close>
        by (simp add: mult_mono)
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
proof
  show "((*\<^sub>R) r::'a star \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
    by (simp add: scaleR_scaleC star_scaleC_def star_scaleR_def)    
qed

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
  show "\<And>x y::'a star. a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
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

lemma cCauchy_iff2: 
  "Cauchy X \<longleftrightarrow> (\<forall>j. (\<exists>M. \<forall>m \<ge> M. \<forall>n \<ge> M. cmod (X m - X n) < inverse (real (Suc j))))"
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
  shows \<open>closed ((*\<^sub>C) a ` S)\<close>
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
      ultimately have t2: \<open>((\<lambda> v. scaleC (inverse a) v) \<circ> x) \<longlonglongrightarrow> (\<lambda> v. scaleC (inverse a) v) l\<close>
        using Elementary_Topology.continuous_at_sequentially
        by auto
      have \<open>(\<lambda> v. scaleC (inverse a) v) \<circ> x = (\<lambda> n. scaleC (inverse a) (x n))\<close>
        by auto
      hence t1: \<open>(\<lambda> v. scaleC (inverse a) v) \<circ> x = t\<close> using \<open>\<forall>n. t n = scaleC (inverse a) (x n)\<close>
        by auto
      have \<open>t \<longlonglongrightarrow> (\<lambda> v. scaleC (inverse a) v) l\<close>
        using t2 t1 by auto        
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

  have "x \<in> closure ((*\<^sub>C) a ` S)"
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
  thus "(*\<^sub>C) a ` closure S \<subseteq> closure ((*\<^sub>C) a ` S)" by blast
qed

lemma onorm_scalarC:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes a1: \<open>cbounded_linear f\<close>
  shows  \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (cmod r) * onorm f\<close>
proof-
  have \<open>(norm (f x)) / norm x \<le> onorm f\<close>
    for x
    using a1
    by (simp add: cbounded_linear.bounded_linear le_onorm)        
  hence t2: \<open>bdd_above {(norm (f x)) / norm x | x. True}\<close>
    by fastforce 
  have \<open>continuous_on UNIV ( (*) w ) \<close>
    for w::real
    by simp
  hence \<open>isCont ( ((*) (cmod r)) ) x\<close>
    for x
    by simp    
  hence t3: \<open>continuous (at_left (Sup {(norm (f x)) / norm x | x. True})) ((*) (cmod r))\<close>
    using Elementary_Topology.continuous_at_imp_continuous_within
    by blast
  have \<open>{(norm (f x)) / norm x | x. True} \<noteq> {}\<close>
    by blast      
  moreover have \<open>mono ((*) (cmod r))\<close>
    by (simp add: monoI ordered_comm_semiring_class.comm_mult_left_mono)      
  ultimately have \<open>Sup {((*) (cmod r)) ((norm (f x)) / norm x) | x. True}
         = ((*) (cmod r)) (Sup {(norm (f x)) / norm x | x. True})\<close>
    using t2 t3
    by (simp add:  continuous_at_Sup_mono full_SetCompr_eq image_image)      
  hence  \<open>Sup {(cmod r) * ((norm (f x)) / norm x) | x. True}
         = (cmod r) * (Sup {(norm (f x)) / norm x | x. True})\<close>
    by blast
  moreover have \<open>Sup {(cmod r) * ((norm (f x)) / norm x) | x. True}
                = (SUP x. cmod r * norm (f x) / norm x)\<close>
    by (simp add: full_SetCompr_eq)            
  moreover have \<open>(Sup {(norm (f x)) / norm x | x. True})
                = (SUP x. norm (f x) / norm x)\<close>
    by (simp add: full_SetCompr_eq)      
  ultimately have t1: "(SUP x. cmod r * norm (f x) / norm x) 
      = cmod r * (SUP x. norm (f x) / norm x)"
    by simp 
  have \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (SUP x. norm ( (\<lambda> t. r *\<^sub>C (f t)) x) / norm x)\<close>
    by (simp add: onorm_def)
  hence \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (SUP x. (cmod r) * (norm (f x)) / norm x)\<close>
    by simp
  also have \<open>... = (cmod r) * (SUP x. (norm (f x)) / norm x)\<close>
    using t1.
  finally show ?thesis
    by (simp add: onorm_def) 
qed

lemma onorm_scaleC_left_lemma:
  fixes f :: "'a::complex_normed_vector"
  assumes r: "cbounded_linear r"
  shows "onorm (\<lambda>x. r x *\<^sub>C f) \<le> onorm r * norm f"
proof (rule onorm_bound)
  fix x
  have "norm (r x *\<^sub>C f) = norm (r x) * norm f"
    by simp
  also have "\<dots> \<le> onorm r * norm x * norm f"
    by (simp add: cbounded_linear.bounded_linear mult.commute mult_left_mono onorm r)
  finally show "norm (r x *\<^sub>C f) \<le> onorm r * norm f * norm x"
    by (simp add: ac_simps)
  show "0 \<le> onorm r * norm f"
    by (simp add: cbounded_linear.bounded_linear onorm_pos_le r)
qed

lemma onorm_scaleC_left:
  fixes f :: "'a::complex_normed_vector"
  assumes f: "cbounded_linear r"
  shows "onorm (\<lambda>x. r x *\<^sub>C f) = onorm r * norm f"
proof (cases "f = 0")
  assume "f \<noteq> 0"
  show ?thesis
  proof (rule order_antisym)
    show "onorm (\<lambda>x. r x *\<^sub>C f) \<le> onorm r * norm f"
      using f by (rule onorm_scaleC_left_lemma)
  next
    have bl1: "cbounded_linear (\<lambda>x. r x *\<^sub>C f)"
      by (metis cbounded_linear_scaleC_const f)
    have x1:"cbounded_linear (\<lambda>x. r x * norm f)"
      by (metis cbounded_linear_mult_const f)

    have "onorm r \<le> onorm (\<lambda>x. r x * complex_of_real (norm f)) / norm f"
      if "onorm r \<le> onorm (\<lambda>x. r x * complex_of_real (norm f)) * cmod (1 / complex_of_real (norm f))"
        and "f \<noteq> 0"
      using that
      by (metis complex_of_real_cmod complex_of_real_nn_iff field_class.field_divide_inverse 
          inverse_eq_divide nice_ordered_field_class.zero_le_divide_1_iff norm_ge_zero of_real_1 
          of_real_divide of_real_eq_iff) 
    hence "onorm r \<le> onorm (\<lambda>x. r x * norm f) * inverse (norm f)"
      using \<open>f \<noteq> 0\<close> onorm_scaleC_left_lemma[OF x1, of "inverse (norm f)"]
      by (simp add: inverse_eq_divide)
    also have "onorm (\<lambda>x. r x * norm f) \<le> onorm (\<lambda>x. r x *\<^sub>C f)"
    proof (rule onorm_bound)
      have "bounded_linear (\<lambda>x. r x *\<^sub>C f)"
        using bl1 cbounded_linear.bounded_linear by auto
      thus "0 \<le> onorm (\<lambda>x. r x *\<^sub>C f)"
        by (rule Operator_Norm.onorm_pos_le)
      show "cmod (r x * complex_of_real (norm f)) \<le> onorm (\<lambda>x. r x *\<^sub>C f) * norm x"
        for x :: 'b
        by (smt \<open>bounded_linear (\<lambda>x. r x *\<^sub>C f)\<close> complex_of_real_cmod complex_of_real_nn_iff 
            complex_scaleC_def norm_ge_zero norm_scaleC of_real_eq_iff onorm)      
    qed
    finally show "onorm r * norm f \<le> onorm (\<lambda>x. r x *\<^sub>C f)"
      using \<open>f \<noteq> 0\<close>
      by (simp add: inverse_eq_divide pos_le_divide_eq mult.commute)
  qed
qed (simp add: onorm_zero)

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
        complex_vector.subspace_def csubspace_raw_def
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
  assumes a1: "\<forall>A\<in>\<A>. closed_subspace A"
  shows "closed_subspace (\<Inter>\<A>)"
proof-
  have \<open>complex_vector.subspace (\<Inter>\<A>)\<close>
    by (simp add: assms closed_subspace.subspace complex_vector.subspace_Inter)    
  moreover have \<open>closed (\<Inter>\<A>)\<close>
    by (simp add: assms closed_Inter closed_subspace.closed)
  ultimately show ?thesis 
    by (simp add: closed_subspace.intro)
qed


subsection \<open>Linear space\<close>


typedef (overloaded) ('a::"{complex_vector,topological_space}") 
  clinear_space = \<open>{S::'a set. closed_subspace S}\<close>
  morphisms space_as_set Abs_clinear_space
  using Complex_Vector_Spaces.subspace_UNIV by blast


setup_lifting type_definition_clinear_space

lemma subspace_image:
  assumes "clinear f" and "complex_vector.subspace S"
  shows "complex_vector.subspace (f ` S)"
  by (simp add: assms(1) assms(2) complex_vector.linear_subspace_image)


instantiation clinear_space :: (complex_normed_vector) scaleC begin
lift_definition scaleC_clinear_space :: "complex \<Rightarrow> 'a clinear_space \<Rightarrow> 'a clinear_space" is
  "\<lambda>c S. (*\<^sub>C) c ` S"
proof
  show "csubspace ((*\<^sub>C) c ` S)"
    if "closed_subspace S"
    for c :: complex
      and S :: "'a set"
    using that
    by (simp add: closed_subspace.subspace complex_vector.linear_subspace_image) 
  show "closed ((*\<^sub>C) c ` S)"
    if "closed_subspace S"
    for c :: complex
      and S :: "'a set"
    using that
    by (simp add: closed_scaleC closed_subspace.closed) 
qed

lift_definition scaleR_clinear_space :: "real \<Rightarrow> 'a clinear_space \<Rightarrow> 'a clinear_space" is
  "\<lambda>c S. (*\<^sub>R) c ` S"
proof
  show "csubspace ((*\<^sub>R) r ` S)"
    if "closed_subspace S"
    for r :: real
      and S :: "'a set"
    using that   using cbounded_linear_def cbounded_linear_scaleC_right scaleR_scaleC
    by (simp add: scaleR_scaleC closed_subspace.subspace complex_vector.linear_subspace_image)
  show "closed ((*\<^sub>R) r ` S)"
    if "closed_subspace S"
    for r :: real
      and S :: "'a set"
    using that 
    by (simp add: closed_scaling closed_subspace.closed)
qed

instance 
proof
  show "((*\<^sub>R) r::'a clinear_space \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
    by (simp add: scaleR_scaleC scaleC_clinear_space_def scaleR_clinear_space_def)    
qed

end

instantiation clinear_space :: ("{complex_vector,t1_space}") bot begin
lift_definition bot_clinear_space :: \<open>'a clinear_space\<close> is \<open>{0}\<close>
  by simp
instance..
end


lemma timesScalarSpace_0[simp]: "0 *\<^sub>C S = bot" for S :: "_ clinear_space"
proof transfer
  have "(0::'b) \<in> (\<lambda>x. 0) ` S"
    if "closed_subspace S"
    for S::"'b set"
    using that unfolding closed_subspace_def
    by (simp add: complex_vector.linear_subspace_image complex_vector.module_hom_zero 
        complex_vector.subspace_0)
  thus "(*\<^sub>C) 0 ` S = {0::'b}"
    if "closed_subspace (S::'b set)"
    for S :: "'b set"
    using that 
    by (auto intro !: exI [of _ 0])
qed

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


lemma timesScalarSpace_not0[simp]: "a \<noteq> 0 \<Longrightarrow> a *\<^sub>C S = S" for S :: "_ clinear_space"
proof transfer
  show "(*\<^sub>C) a ` S = S"
    if "(a::complex) \<noteq> 0"
      and "closed_subspace S"
    for a :: complex
      and S :: "'b set"
    using that by (simp add: subspace_scale_invariant) 
qed


instantiation clinear_space :: ("{complex_vector,topological_space}") "top"
begin
lift_definition top_clinear_space :: \<open>'a clinear_space\<close> is \<open>UNIV\<close>
  by simp

instance ..
end

instantiation clinear_space :: ("{complex_vector,topological_space}") "Inf"
begin
lift_definition Inf_clinear_space::\<open>'a clinear_space set \<Rightarrow> 'a clinear_space\<close>
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

lift_definition Span :: "'a::complex_normed_vector set \<Rightarrow> 'a clinear_space"
  is "\<lambda>G. closure (complex_vector.span G)"
proof (rule closed_subspace.intro)
  show "csubspace (closure (cspan S))"
    for S :: "'a set"
    by (simp add: subspace_cl)    
  show "closed (closure (cspan S))"
    for S :: "'a set"
    by simp
qed

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
    hence "x \<in> closure (cspan A)"
      by (simp add: Span.rep_eq)
    hence \<open>x \<in> closure (complex_vector.span A)\<close>
      unfolding Span_def
      by simp     
    hence \<open>\<exists> y::nat \<Rightarrow> 'a. (\<forall> n. y n \<in> (complex_vector.span A)) \<and> y \<longlonglongrightarrow> x\<close>
      by (simp add: closure_sequential)
    then obtain y where \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close> and \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>y n \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S}\<close>
      for n
      using  \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close>
      by auto

    have \<open>closed_subspace S \<Longrightarrow> closed S\<close>
      for S::\<open>'a set\<close>
      by (simp add: closed_subspace.closed)
    hence \<open>closed ( \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S})\<close>
      by simp
    hence \<open>x \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S}\<close> using \<open>y \<longlonglongrightarrow> x\<close>
      using \<open>\<And>n. y n \<in> \<Inter> {S. complex_vector.span A \<subseteq> S \<and> closed_subspace S}\<close> closed_sequentially 
      by blast
    moreover have \<open>{S. A \<subseteq> S \<and> closed_subspace S} \<subseteq> {S. (complex_vector.span A) \<subseteq> S \<and> closed_subspace S}\<close>
      using Collect_mono_iff
      by (simp add: Collect_mono_iff subspace_span_A)  
    ultimately have \<open>x \<in> \<Inter> {S. A \<subseteq> S \<and> closed_subspace S}\<close>
      by blast     
    moreover have "(x::'a) \<in> \<Inter> {x. A \<subseteq> x \<and> closed_subspace x}"
      if "(x::'a) \<in> \<Inter> {S. A \<subseteq> S \<and> closed_subspace S}"
      for x :: 'a
        and A :: "'a set"
      using that
      by simp
    ultimately show \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close> 
      apply transfer.
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

lemma span_mult[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> cspan { a *\<^sub>C \<psi> } = cspan {\<psi>}"
  for \<psi>::"'a::complex_vector"
  by (smt complex_vector.dependent_single complex_vector.independent_insert 
      complex_vector.scale_eq_0_iff complex_vector.span_base complex_vector.span_redundant 
      complex_vector.span_scale doubleton_eq_iff insert_absorb insert_absorb2 insert_commute 
      singletonI)

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

instantiation clinear_space :: ("{complex_vector,topological_space}") "order"
begin
lift_definition less_eq_clinear_space :: \<open>'a clinear_space \<Rightarrow> 'a clinear_space \<Rightarrow> bool\<close>
  is  \<open>(\<subseteq>)\<close>.
declare less_eq_clinear_space_def[code del]
lift_definition less_clinear_space :: \<open>'a clinear_space \<Rightarrow> 'a clinear_space \<Rightarrow> bool\<close>
  is \<open>(\<subset>)\<close>.
declare less_clinear_space_def[code del]
instance
proof
  show "((x::'a clinear_space) < y) = (x \<le> y \<and> \<not> y \<le> x)"
    for x :: "'a clinear_space"
      and y :: "'a clinear_space"
    by (simp add: less_eq_clinear_space.rep_eq less_le_not_le less_clinear_space.rep_eq)    
  show "(x::'a clinear_space) \<le> x"
    for x :: "'a clinear_space"
    by (simp add: less_eq_clinear_space.rep_eq)    
  show "(x::'a clinear_space) \<le> z"
    if "(x::'a clinear_space) \<le> y"
      and "(y::'a clinear_space) \<le> z"
    for x :: "'a clinear_space"
      and y :: "'a clinear_space"
      and z :: "'a clinear_space"
    using that
    using less_eq_clinear_space.rep_eq by auto 
  show "(x::'a clinear_space) = y"
    if "(x::'a clinear_space) \<le> y"
      and "(y::'a clinear_space) \<le> x"
    for x :: "'a clinear_space"
      and y :: "'a clinear_space"
    using that
    by (simp add: space_as_set_inject less_eq_clinear_space.rep_eq) 
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
    using \<open>complex_vector.dependent V\<close> \<open>finite V\<close> complex_vector.independent_if_scalars_zero 
    by fastforce
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

definition cbilinear :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector) \<Rightarrow> bool\<close>
  where \<open>cbilinear \<equiv> (\<lambda> f. (\<forall> y. clinear (\<lambda> x. f x y)) \<and> (\<forall> x. clinear (\<lambda> y. f x y)) )\<close>

lemma cbilinear_from_product_clinear:
  fixes g' :: \<open>'a::complex_vector \<Rightarrow> complex\<close> and g :: \<open>'b::complex_vector \<Rightarrow> complex\<close>
  assumes \<open>\<And> x y. h x y = (g' x)*(g y)\<close> and \<open>clinear g\<close> and \<open>clinear g'\<close>
  shows \<open>cbilinear h\<close>
proof-
  have w1: "h (b1 + b2) y = h b1 y + h b2 y"
    for b1 :: 'a
      and b2 :: 'a
      and y
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
  have w2: "h (r *\<^sub>C b) y = r *\<^sub>C h b y"
    for r :: complex
      and b :: 'a
      and y
  proof-
    have \<open>h (r *\<^sub>C b) y = g' (r *\<^sub>C b) * g y\<close>
      by (simp add: assms(1))
    also have \<open>\<dots> = r *\<^sub>C (g' b * g y)\<close>
      by (simp add: assms(3) complex_vector.linear_scale)
    also have \<open>\<dots> = r *\<^sub>C (h b y)\<close>
      by (simp add: assms(1))          
    finally show ?thesis by blast
  qed
  have "clinear (\<lambda>x. h x y)"
    for y :: 'b
    unfolding clinear_def
    by (meson clinearI clinear_def w1 w2)
  hence t2: "\<forall>y. clinear (\<lambda>x. h x y)"
    by simp
  have v1: "h x (b1 + b2) = h x b1 + h x b2"
    for b1 :: 'b
      and b2 :: 'b
      and x
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

  have v2:  "h x (r *\<^sub>C b) = r *\<^sub>C h x b"
    for r :: complex
      and b :: 'b
      and x
  proof-
    have \<open>h x (r *\<^sub>C b) =  g' x * g (r *\<^sub>C b)\<close>
      by (simp add: assms(1))
    also have \<open>\<dots> = r *\<^sub>C (g' x * g b)\<close>
      by (simp add: assms(2) complex_vector.linear_scale)
    also have \<open>\<dots> = r *\<^sub>C (h x b)\<close>
      by (simp add: assms(1))          
    finally show ?thesis by blast
  qed
  have "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) (h x)"
    for x :: 'a
    using v1 v2
    by (meson clinearI clinear_def) 
  hence t1: "\<forall>x. clinear (h x)"
    unfolding clinear_def
    by simp
  show ?thesis
    unfolding cbilinear_def
    by (simp add: t1 t2)    
qed

lemma bilinear_Kronecker_delta:
  fixes u::\<open>'a::complex_vector\<close> and v::\<open>'b::complex_vector\<close>
  assumes \<open>complex_vector.independent A\<close> and \<open>complex_vector.independent B\<close>
    and \<open>u \<in> A\<close> and \<open>v \<in> B\<close>
  shows \<open>\<exists> h::_\<Rightarrow>_\<Rightarrow>complex. cbilinear h \<and> (h u v = 1) \<and>
    (\<forall>x\<in>A. \<forall>y\<in>B. (x,y) \<noteq> (u,v) \<longrightarrow> h x y = 0)\<close>
proof-
  define f where \<open>f x = (if x = v then (1::complex) else 0)\<close> 
    for x
  have \<open>\<exists>g. clinear g \<and> (\<forall>x\<in>B. g x = f x)\<close>
    using \<open>complex_vector.independent B\<close> complex_vector.linear_independent_extend
    by (simp add: complex_vector.linear_independent_extend Complex_Vector_Spaces.cdependent_raw_def) 
  then obtain g where \<open>clinear g\<close> and \<open>\<forall>x\<in>B. g x = f x\<close>
    by blast
  define f' where \<open>f' x = (if x = u then (1::complex) else 0)\<close> for x
  hence \<open>\<exists>g'. clinear g' \<and> (\<forall>x\<in>A. g' x = f' x)\<close>
    by (simp add: Complex_Vector_Spaces.cdependent_raw_def assms(1) complex_vector.linear_independent_extend)    
  then obtain g' where \<open>clinear g'\<close> and \<open>\<forall>x\<in>A. g' x = f' x\<close>
    by blast
  define h where \<open>h x y = (g' x)*(g y)\<close> for x y
  have t1: \<open>x\<in>A \<Longrightarrow> y\<in>B \<Longrightarrow> (x,y) \<noteq> (u,v) \<Longrightarrow> h x y = 0\<close>
    for x y
  proof-
    assume \<open>x\<in>A\<close> and \<open>y\<in>B\<close> and \<open>(x,y) \<noteq> (u,v)\<close>
    have r1:  \<open>x \<noteq> u \<Longrightarrow> h x y = 0\<close>
    proof-
      assume \<open>x \<noteq> u\<close>
      hence \<open>g' x = 0\<close>
        by (simp add: \<open>\<forall>x\<in>A. g' x = f' x\<close> \<open>x \<in> A\<close> f'_def)
      thus ?thesis
        by (simp add: \<open>h \<equiv> \<lambda>x y. g' x * g y\<close>) 
    qed
    have r2: \<open>y \<noteq> v \<Longrightarrow> h x y = 0\<close>
    proof-
      assume \<open>y \<noteq> v\<close>
      hence \<open>g y = 0\<close>
        using \<open>\<forall>x\<in>B. g x = f x\<close> \<open>y \<in> B\<close> f_def by auto
      thus ?thesis
        by (simp add: \<open>h \<equiv> \<lambda>x y. g' x * g y\<close>) 
    qed
    from \<open>(x,y) \<noteq> (u,v)\<close>
    have \<open>x \<noteq> u \<or> y \<noteq> v\<close>
      by simp    
    thus ?thesis using r1 r2
      by auto 
  qed
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
  ultimately show ?thesis 
    using t1 by blast
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
  hence \<open>x = (\<Sum>s\<in>S. t s *\<^sub>C s)\<close>
    using \<open>x = (\<Sum>s\<in>T. t' s *\<^sub>C s)\<close> t_def by auto
  thus ?thesis by blast
qed

setup \<open>Sign.add_const_constraint ("Complex_Vector_Spaces.cindependent", SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cdependent\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cspan\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> 'a set\<close>)\<close>

class cfinite_dim = complex_vector +
  assumes finite_basis: "\<exists>basis::'a set. finite basis \<and> cindependent basis \<and> cspan basis = UNIV"

class basis_enum = complex_vector +
  fixes canonical_basis :: "'a list"
  (* TODO: Remove canonical_basis_length. Can use CARD(...) instead. *)
    and canonical_basis_length :: "'a itself \<Rightarrow> nat"
  assumes distinct_canonical_basis[simp]: 
    "distinct canonical_basis"
    and is_cindependent_set:
    "cindependent (set canonical_basis)"
    and is_generator_set:
    "cspan (set canonical_basis) = UNIV" 
    and canonical_basis_length_eq:
    "canonical_basis_length TYPE('a) = length canonical_basis"

setup \<open>Sign.add_const_constraint ("Complex_Vector_Spaces.cindependent", SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cdependent\<close>, SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cspan\<close>, SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> 'a set\<close>)\<close>

instance basis_enum \<subseteq> cfinite_dim
  apply intro_classes
  apply (rule exI[of _ \<open>set canonical_basis\<close>])
  using is_cindependent_set is_generator_set by auto

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


lemma clinear_space_leI:
  assumes t1: "\<And>x. x \<in> space_as_set A \<Longrightarrow> x \<in> space_as_set B"
  shows "A \<le> B"
  using t1  proof transfer
  show "A \<subseteq> B"
    if "closed_subspace A"
      and "closed_subspace B"
      and "\<And>x::'a. x \<in> A \<Longrightarrow> x \<in> B"
    for A :: "'a set"
      and B :: "'a set"
    using that
    by (simp add: subsetI) 
qed 

lemma finite_sum_tendsto:
  fixes A::\<open>'a set\<close> and r :: "'a \<Rightarrow> nat \<Rightarrow> 'b::{comm_monoid_add,topological_monoid_add}"
  assumes t1: \<open>\<And>a. a \<in> A \<Longrightarrow> r a \<longlonglongrightarrow> \<phi> a\<close> 
    and t2: \<open>finite A\<close>
  shows \<open>(\<lambda> n. (\<Sum>a\<in>A. r a n)) \<longlonglongrightarrow>  (\<Sum>a\<in>A. \<phi> a)\<close>
proof-
  have "(\<lambda>n. \<Sum>a\<in>A. r a n) \<longlonglongrightarrow> sum \<phi> A"
    if  \<open>finite A\<close> and \<open>\<And>a. a \<in> A \<Longrightarrow> r a \<longlonglongrightarrow> \<phi> a\<close>
    for A
    using that
  proof induction
    case empty
    show ?case 
      by auto
  next
    case (insert x F)
    hence "r x \<longlonglongrightarrow> \<phi> x" and "(\<lambda>n. \<Sum>a\<in>F. r a n) \<longlonglongrightarrow> sum \<phi> F"
      by auto
    hence "(\<lambda>n. r x n + (\<Sum>a\<in>F. r a n)) \<longlonglongrightarrow> \<phi> x + sum \<phi> F"
      using tendsto_add by blast
    thus ?case 
      using sum.insert insert by auto
  qed
  thus ?thesis
    using t1 t2 by blast    
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
    by (metis dependent_raw_def real_vector.independent_empty)    
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
    by (metis Complex_Vector_Spaces.cdependent_raw_def Suc.prems(1) complex_vector.independent_insert g1 g2)
  ultimately have "real_vector.independent S'"
    by (simp add: Suc.hyps(1))
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
      by (smt Complex_Vector_Spaces.cdependent_raw_def Suc.prems(1) complex_vector.independent_insert 
          g1 g2)
  qed
  ultimately show ?case 
    by (smt dependent_raw_def g1 real_vector.independent_insertI)

qed

lemma cspan_singleton:
  fixes x y::"'a::complex_vector"
  assumes a1: "x \<in> cspan {y}"
  shows "\<exists>\<alpha>. x = \<alpha> *\<^sub>C y"
proof-
  have "\<exists>t r. x = (\<Sum>j\<in>t. r j *\<^sub>C j) \<and> finite t \<and> t \<subseteq> {y}"
    using a1 using complex_vector.span_explicit[where b = "{y}"]
    by (smt  mem_Collect_eq)
  then obtain t r where b1: "x = (\<Sum>j\<in>t. r j *\<^sub>C j)" and b2: "finite t" and b3: "t \<subseteq> {y}"
    by blast
  show ?thesis
  proof(cases "t = {}")
    case True
    hence "(\<Sum>j\<in>t. r j *\<^sub>C j) = 0"
      using b2
      by simp
    thus ?thesis using b1 by simp
  next
    case False
    hence "t = {y}"
      using b3 by auto
    moreover have "(\<Sum>j\<in>{y}. r j *\<^sub>C j) = r y *\<^sub>C y"
      by auto
    ultimately show  ?thesis using b1 by blast
  qed
qed

lemma Span_empty[simp]: "Span {} = bot"
proof transfer
  show "closure (cspan {}) = {0::'a}"
    by simp
qed



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
  shows \<open>\<forall>t. finite t \<and> card t = n \<longrightarrow> B (\<Sum>a\<in>t. (r a) *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)\<close>
proof(induction n)
  case 0 thus ?case
    using assms bounded_sesquilinear_0_left by fastforce 
next
  case (Suc n)
  have \<open>B (\<Sum>a\<in>t. r a *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)\<close>
    if \<open>finite t\<close> and \<open>card t = Suc n\<close>
    for t
  proof-
    have \<open>\<exists> k s. finite s \<and> card s = n \<and> insert k s = t\<close>
      by (metis card_Suc_eq finite_insert that(1) that(2))      
    then obtain k s where \<open>finite s\<close> and \<open>card s = n\<close> and \<open>insert k s = t\<close>
      by blast
    have "card (insert k s) = Suc n"
      by (metis \<open>card t = Suc n\<close> \<open>insert k s = t\<close>)
    hence "k \<notin> s"
      by (metis \<open>card s = n\<close> \<open>finite s\<close> card_insert_if n_not_Suc_n)
    hence \<open>(\<Sum>a\<in>t. r a *\<^sub>C a) = (\<Sum>a\<in>s. r a *\<^sub>C a) +  r k *\<^sub>C k\<close>
      using \<open>finite s\<close> \<open>insert k s = t\<close> by auto
    hence \<open>B (\<Sum>a\<in>t. r a *\<^sub>C a) y = B (\<Sum>a\<in>s. r a *\<^sub>C a) y + B (r k *\<^sub>C k) y\<close>
      by (simp add: assms bounded_sesquilinear.add_left)
    hence \<open>B (\<Sum>a\<in>t. r a *\<^sub>C a) y = B (\<Sum>a\<in>s. r a *\<^sub>C a) y +  cnj (r k) *\<^sub>C B k y\<close>
      by (simp add: assms bounded_sesquilinear.scaleC_left)
    moreover have \<open>(\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y) = (\<Sum>a\<in>s. cnj (r a) *\<^sub>C B a y) +  cnj (r k) *\<^sub>C B k y\<close>
      by (metis (no_types, lifting) \<open>card s = n\<close> \<open>card t = Suc n\<close> \<open>finite s\<close> \<open>insert k s = t\<close> add.commute card_insert_if n_not_Suc_n sum.insert)
    moreover have \<open>B (\<Sum>a\<in>s. r a *\<^sub>C a) y = (\<Sum>a\<in>s. cnj (r a) *\<^sub>C B a y)\<close>
      using \<open>card s = n\<close> \<open>finite s\<close> Suc.IH by blast 
    ultimately show ?thesis by simp
  qed
  thus ?case by blast
qed


lemma sesquilinear_finite_sum:                     
  assumes \<open>bounded_sesquilinear B\<close> and \<open>finite t\<close>
  shows \<open>B (\<Sum>a\<in>t. (r a) *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)\<close>
  by (simp add: sesquilinear_finite_sum_induction assms(1) assms(2))

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


lemma sesquilinear_superposition:
  assumes a1: "bounded_sesquilinear B" and a2: "\<And> p q. p \<in> S_left \<Longrightarrow> q \<in> S_right \<Longrightarrow> B p q = 0"
    and a3: "x \<in> complex_vector.span S_left" and a4: "y \<in> complex_vector.span S_right"
  shows \<open>B x y = 0\<close>
proof-
  have b1: "(0::'c) \<in> complex_vector.span {0}"
    by auto
  have r1: \<open>B p t = 0\<close>
    if e1: "t \<in> complex_vector.span S_right"
      and d1: "p\<in>S_left"
    for p t
  proof (rule complex_vector.span_induct)
    show "(0::'c) \<in> complex_vector.span {0}"
      by auto
    have "0 \<in> Collect ((=) (B p t)) \<and>
    (\<forall>x\<in>Collect ((=) (B p t)).
        \<forall>y\<in>Collect ((=) (B p t)).
           x + y \<in> Collect ((=) (B p t))) \<and>
    (\<forall>c. \<forall>x\<in>Collect ((=) (B p t)).
            c *\<^sub>C x \<in> Collect ((=) (B p t)))"
    proof
      have "clinear (B p)"
        by (meson assms(1) bounded_sesquilinear.add_right bounded_sesquilinear.scaleC_right clinearI)
      hence "B p t = 0"
        using a2 d1 equal_span_0 that by blast            
      thus "0 \<in> Collect ((=) (B p t))"
        by (metis (full_types) mem_Collect_eq)
      have "\<forall>x\<in>Collect ((=) (B p t)). \<forall>y\<in>Collect ((=) (B p t)). x + y \<in> Collect ((=) (B p t))"
        using \<open>0 \<in> Collect ((=) (B p t))\<close> by auto              
      moreover have "\<forall>c. \<forall>x\<in>Collect ((=) (B p t)). c *\<^sub>C x \<in> Collect ((=) (B p t))"
        using \<open>0 \<in> Collect ((=) (B p t))\<close> by auto              
      ultimately show "(\<forall>x\<in>Collect ((=) (B p t)). \<forall>y\<in>Collect ((=) (B p t)). x + y \<in> Collect ((=) (B p t)))
           \<and> (\<forall>c. \<forall>x\<in>Collect ((=) (B p t)). c *\<^sub>C x \<in> Collect ((=) (B p t)))"
        by blast
    qed
    show " \<And>x. x \<in> {0} \<Longrightarrow> B p t = x"
      using \<open>0 \<in> Collect ((=) (B p t)) \<and> (\<forall>x\<in>Collect ((=) (B p t)). \<forall>y\<in>Collect ((=) (B p t)). 
          x + y \<in> Collect ((=) (B p t))) \<and> (\<forall>c. \<forall>x\<in>Collect ((=) (B p t)). 
            c *\<^sub>C x \<in> Collect ((=) (B p t)))\<close> by blast       
    show "csubspace {a. B p t = a}"
      using \<open>0 \<in> Collect ((=) (B p t)) \<and> (\<forall>x\<in>Collect ((=) (B p t)). \<forall>y\<in>Collect ((=) (B p t)). x + y \<in> Collect ((=) (B p t))) \<and> (\<forall>c. \<forall>x\<in>Collect ((=) (B p t)). c *\<^sub>C x \<in> Collect ((=) (B p t)))\<close> by auto
  qed
  have \<open>B p y = 0\<close>
    if d1: "p\<in>S_left"
    for p
    by (simp add: a4 r1 that)
  hence c1: "0 \<in> {a. \<forall>p\<in>S_left. B p y = a}"
    by simp
  hence "(\<forall>a\<in>{a. \<forall>p\<in>S_left. B p y = a}. \<forall>b\<in>{a. \<forall>p\<in>S_left. B p y = a}. a + b \<in> {a. \<forall>p\<in>S_left. B p y = a})
   \<and> (\<forall>c. \<forall>a\<in>{a. \<forall>p\<in>S_left. B p y = a}. c *\<^sub>C a \<in> {a. \<forall>p\<in>S_left. B p y = a})"
    by auto          
  hence b2: "complex_vector.subspace {a. \<forall>p\<in>S_left. B p y = a}" 
    unfolding complex_vector.subspace_def
    using c1 by blast
  have b3: "\<forall>p\<in>S_left. B p y = x"
    if "y \<in> complex_vector.span S_right"
      and "(x::'c) \<in> {0}"
    for x :: 'c
    using b2 complex_vector.span_induct that(2) by force    
  have \<open>\<forall> p \<in> S_left. B p y = 0\<close>
    by (simp add: a4 b3)       
  hence \<open>\<forall> p \<in> S_left. B p y = 0\<close>
    by blast
  hence w1: \<open>\<forall> p \<in> S_left. B p y = 0\<close>
    by blast
  have "B p y = 0"
    if "p \<in> complex_vector.span S_left"
    for  p
  proof-
    have \<open>\<exists> t r. finite t \<and> t \<subseteq> S_left \<and> p = (\<Sum>a\<in>t. (r a) *\<^sub>C a)\<close>
      using complex_vector.span_explicit
      by (smt mem_Collect_eq that(1)) 
    then obtain t r where t1: \<open>finite t\<close> and t2: \<open>t \<subseteq> S_left\<close> and t3: \<open>p = (\<Sum>a\<in>t. (r a) *\<^sub>C a)\<close>
      by blast
    have \<open>B p y = B (\<Sum>a\<in>t. (r a) *\<^sub>C a) y\<close>
      using t3 by auto
    also have \<open>\<dots> = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)\<close>
      using sesquilinear_finite_sum a1 t1 by auto      
    also have \<open>\<dots> = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C 0)\<close>
      using subsetD w1 t2 by fastforce 
    also have \<open>\<dots> = (\<Sum>a\<in>t. 0)\<close>
      by simp
    also have \<open>\<dots> = 0\<close>
      by simp
    finally show ?thesis
      by blast
  qed
  thus ?thesis
    by (simp add: a3 a4)
qed


definition closed_sum:: \<open>'a::{complex_vector,topological_space} set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>closed_sum A B = closure (A + B)\<close>

notation closed_sum (infixl "+\<^sub>M" 65)

lemma subspace_closed_plus:
  fixes A B::"('a::complex_normed_vector) set"
  assumes a1: \<open>closed_subspace A\<close> and a2: \<open>closed_subspace B\<close>
  shows \<open>closed_subspace (A +\<^sub>M B)\<close>
  using a1 a2 closed_sum_def 
  by (metis closed_subspace.subspace subspace_I subspace_plus)


instantiation clinear_space :: (complex_normed_vector) sup begin
lift_definition sup_clinear_space :: "'a clinear_space \<Rightarrow> 'a clinear_space \<Rightarrow> 'a clinear_space" 
  is "\<lambda>A B::'a set. A +\<^sub>M B"
  by (simp add: subspace_closed_plus) 
instance .. 
end

lemma Span_union: "Span A \<squnion> Span B = Span (A \<union> B)"
proof (transfer, auto)
  have p0: "Complex_Vector_Spaces.span (A \<union> B) = 
      Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B"
    for A B::"'a set"
    using Complex_Vector_Spaces.complex_vector.span_Un
    by (smt Collect_cong set_plus_def)
  hence p1: "closure (Complex_Vector_Spaces.span (A \<union> B)) = 
             closure (Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B)"
    for A B::"'a set"
    by simp

  show "x \<in> closure (Complex_Vector_Spaces.span (A \<union> B))"
    if "x \<in> closure (Complex_Vector_Spaces.span A) +\<^sub>M
            closure (Complex_Vector_Spaces.span B)"
    for x::'a and A B
  proof-
    have "closure (Complex_Vector_Spaces.span A) + closure (Complex_Vector_Spaces.span B) \<subseteq>
          closure (Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B)"
      using Starlike.closure_sum by auto
    hence "closure (Complex_Vector_Spaces.span A) + closure (Complex_Vector_Spaces.span B)
        \<subseteq> closure (Complex_Vector_Spaces.span (A \<union> B))"
      by (metis \<open>closure (Complex_Vector_Spaces.span A) + closure (Complex_Vector_Spaces.span B)
           \<subseteq> closure (Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B)\<close> p1)
    thus ?thesis by (smt closed_sum_def closure_closure closure_mono subsetD that)
  qed

  show "x \<in> closure (Complex_Vector_Spaces.span A) +\<^sub>M
            closure (Complex_Vector_Spaces.span B)"
    if "x \<in> closure (Complex_Vector_Spaces.span (A \<union> B))"
    for x::'a and A B
  proof-
    have "Complex_Vector_Spaces.span (A \<union> B) \<subseteq>
           closure (Complex_Vector_Spaces.span A) +
           closure (Complex_Vector_Spaces.span B)"
      apply auto
      by (metis closure_subset p0 set_plus_mono2_b) 
    hence "closure (Complex_Vector_Spaces.span (A \<union> B)) \<subseteq>
           closure (closure (Complex_Vector_Spaces.span A) +
                    closure (Complex_Vector_Spaces.span B))"
      by (smt closure_mono)
    thus ?thesis by (smt closed_sum_def in_mono that)
  qed
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


lemma finite_span_representation_bounded:
  fixes B :: "'a::real_normed_vector set"
  assumes "finite B" and "independent B"
  shows "\<exists>D>0. \<forall>\<psi> b. abs (real_vector.representation B \<psi> b) \<le> norm \<psi> * D"

  text \<open>
  Assume $B$ is a finite linear independent set of vectors (in a real normed vector space).
  Let $\alpha^\psi_b$ be the coefficients of $\psi$ expressed as a linear combination over $B$.
  Then $\alpha$ is is uniformly cblinfun (i.e., $\lvert\alpha^\psi_b \leq D \lVert\psi\rVert\psi$
  for some $D$ independent of $\psi,b$).

  (This also holds when $b$ is not in the span of $B$ because of the way \<open>real_vector.representation\<close>
  is defined in this corner case.)\<close>

proof (cases "B\<noteq>{}")
  case True

(* The following generalizes finite_span_complete_aux to hold without the assumption
     that 'basis has type class finite *)
  define repr  where "repr = real_vector.representation B"
  {
    (* Step 1: Create a fake type definition by introducing a new type variable 'basis
               and then assuming the existence of the morphisms Rep/Abs to B
               This is then roughly equivalent to "typedef 'basis = B" *)
    (* The type variable 'basisT must not be the same as the one used in finite_span_complete_aux
       (I.e., we cannot call it 'basis) *)
    assume "\<exists>(Rep :: 'basisT\<Rightarrow>'a) Abs. type_definition Rep Abs B"
    then obtain rep :: "'basisT \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'basisT" where t: "type_definition rep abs B"
      by auto
        (* Step 2: We show that our fake typedef 'basisT could be instantiated as type class finite *)
    have basisT_finite: "class.finite TYPE('basisT)"
      apply intro_classes 
      using \<open>finite B\<close> t
      by (metis (mono_tags, hide_lams) ex_new_if_finite finite_imageI image_eqI type_definition_def)
        (* Step 3: We take the finite_span_complete_aux and remove the requirement that 'basis::finite
               (instead, a precondition "class.finite TYPE('basisT)" is introduced) *)
    note finite_span_complete_aux(1)[internalize_sort "'basis::finite"]
      (* Step 4: We instantiate the premises *)
    note this[OF basisT_finite t]
  }
    (* Now we have the desired fact, except that it still assumes that B is isomorphic to some type 'basis
     together with the assumption that there are morphisms between 'basis and B. 'basis and that premise
     are removed using cancel_type_definition
  *)
  note this[cancel_type_definition, OF True \<open>finite B\<close> _ \<open>independent B\<close>]

  hence d2:"\<exists>D. \<forall>\<psi>. D>0 \<and> norm (repr \<psi> b) \<le> norm \<psi> * D" if \<open>b\<in>B\<close> for b
    by (simp add: repr_def that True)
  have d1: " (\<And>b. b \<in> B \<Longrightarrow>
          \<exists>D. \<forall>\<psi>. 0 < D \<and> norm (repr \<psi> b) \<le> norm \<psi> * D) \<Longrightarrow>
    \<exists>D. \<forall>b \<psi>. b \<in> B \<longrightarrow>
               0 < D b \<and> norm (repr \<psi> b) \<le> norm \<psi> * D b"
    apply (rule choice) by auto
  then obtain D where D: "D b > 0 \<and> norm (repr \<psi> b) \<le> norm \<psi> * D b" if "b\<in>B" for b \<psi>
    apply atomize_elim
    using d2 by blast

  hence Dpos: "D b > 0" and Dbound: "norm (repr \<psi> b) \<le> norm \<psi> * D b" 
    if "b\<in>B" for b \<psi>
    using that by auto
  define Dall where "Dall = Max (D`B)"
  have "Dall > 0"
    unfolding Dall_def using \<open>finite B\<close> \<open>B\<noteq>{}\<close> Dpos
    by (metis (mono_tags, lifting) Max_in finite_imageI image_iff image_is_empty)
  have "Dall \<ge> D b" if "b\<in>B" for b
    unfolding Dall_def using \<open>finite B\<close> that by auto
  with Dbound
  have "norm (repr \<psi> b) \<le> norm \<psi> * Dall" if "b\<in>B" for b \<psi>
    using that
    by (smt mult_left_mono norm_not_less_zero) 
  moreover have "norm (repr \<psi> b) \<le> norm \<psi> * Dall" if "b\<notin>B" for b \<psi>
    unfolding repr_def using real_vector.representation_ne_zero True
    by (metis calculation empty_subsetI less_le_trans local.repr_def norm_ge_zero norm_zero not_less 
        subsetI subset_antisym)
  ultimately show "\<exists>D>0. \<forall>\<psi> b. abs (repr \<psi> b) \<le> norm \<psi> * D"
    using \<open>Dall > 0\<close> real_norm_def by metis
next
  case False
  thus ?thesis
    unfolding repr_def using real_vector.representation_ne_zero[of B]
    using nice_ordered_field_class.linordered_field_no_ub by fastforce
qed

hide_fact finite_span_complete_aux

lemma complex_real_span:
  "complex_vector.span (B::'a::complex_vector set) = real_vector.span (B \<union> scaleC \<i> ` B)"
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

subsection \<open>Conjugate space\<close>

typedef 'a conjugate_space = "UNIV :: 'a set"
  morphisms from_conjugate_space to_conjugate_space ..
setup_lifting type_definition_conjugate_space

instantiation conjugate_space :: (complex_vector) complex_vector begin
lift_definition scaleC_conjugate_space :: \<open>complex \<Rightarrow> 'a conjugate_space \<Rightarrow> 'a conjugate_space\<close> is \<open>\<lambda>c x. cnj c *\<^sub>C x\<close>.
lift_definition scaleR_conjugate_space :: \<open>real \<Rightarrow> 'a conjugate_space \<Rightarrow> 'a conjugate_space\<close> is \<open>\<lambda>r x. r *\<^sub>R x\<close>.
lift_definition plus_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space \<Rightarrow> 'a conjugate_space" is "(+)".
lift_definition uminus_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space" is \<open>\<lambda>x. -x\<close>.
lift_definition zero_conjugate_space :: "'a conjugate_space" is 0.
lift_definition minus_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space \<Rightarrow> 'a conjugate_space" is "(-)".
instance
  apply (intro_classes; transfer)
  by (simp_all add: scaleR_scaleC scaleC_add_right scaleC_left.add)
end

instantiation conjugate_space :: (complex_normed_vector) complex_normed_vector begin
lift_definition sgn_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space" is "sgn".
lift_definition norm_conjugate_space :: "'a conjugate_space \<Rightarrow> real" is norm.
lift_definition dist_conjugate_space :: "'a conjugate_space \<Rightarrow> 'a conjugate_space \<Rightarrow> real" is dist.
lift_definition uniformity_conjugate_space :: "('a conjugate_space \<times> 'a conjugate_space) filter" is uniformity.
lift_definition  open_conjugate_space :: "'a conjugate_space set \<Rightarrow> bool" is "open".
instance 
  apply (intro_classes; transfer)
  by (simp_all add: dist_norm sgn_div_norm open_uniformity uniformity_dist norm_triangle_ineq)
end

instantiation conjugate_space :: (cbanach) cbanach begin
instance 
  apply intro_classes
  unfolding Cauchy_def convergent_def LIMSEQ_def apply transfer
  using Cauchy_convergent unfolding Cauchy_def convergent_def LIMSEQ_def by metis
end


lemma csemilinear_to_conjugate_space: \<open>csemilinear to_conjugate_space\<close>
  by (rule csemilinearI; transfer, auto)

lemma csemilinear_from_conjugate_space: \<open>csemilinear from_conjugate_space\<close>
  by (rule csemilinearI; transfer, auto)

lemma cspan_to_conjugate_space[simp]: "cspan (to_conjugate_space ` X) = to_conjugate_space ` cspan X"
  unfolding complex_vector.span_def complex_vector.subspace_def hull_def
  apply transfer
  apply simp
  by (metis (no_types, hide_lams) complex_cnj_cnj)

lemma surj_to_conjugate_space[simp]: "surj to_conjugate_space"
  by (meson surj_def to_conjugate_space_cases)


end

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

    "Bounded_Operators-Extra.Extra_Vector_Spaces"
    "Bounded_Operators-Extra.Extra_Ordered_Fields"
    "Bounded_Operators-Extra.Extra_Lattice"
    "Bounded_Operators-Extra.Extra_General"

    Complex_Vector_Spaces0
begin

bundle notation_norm begin
notation norm ("\<parallel>_\<parallel>")
end

subsection \<open>Misc\<close>

lemma (in scaleC) scaleC_real: assumes "r\<in>\<real>" shows "r *\<^sub>C x = Re r *\<^sub>R x"
  unfolding scaleR_scaleC using assms by simp

lemma of_complex_of_real_eq [simp]: "of_complex (of_real n) = of_real n"
  unfolding of_complex_def of_real_def unfolding scaleR_scaleC by simp

lemma Complexs_of_real [simp]: "of_real r \<in> \<complex>"
  unfolding Complexs_def of_real_def of_complex_def 
  apply (subst scaleR_scaleC) by simp

lemma Reals_in_Complexs: "\<real> \<subseteq> \<complex>"
  unfolding Reals_def by auto

lemma (in clinear) "linear f"
  apply standard
  by (simp_all add: add scaleC scaleR_scaleC)
    
lemma (in bounded_clinear) bounded_linear: "bounded_linear f"
  by (simp add: add bounded bounded_linear.intro bounded_linear_axioms.intro linearI scaleC scaleR_scaleC)

lemma clinear_times: "clinear (\<lambda>x. c * x)"
  for c :: "'a::complex_algebra"
  by (auto simp: clinearI distrib_left)

lemma (in clinear) linear:
  shows \<open>linear f\<close>
  by (simp add: add linearI scaleC scaleR_scaleC)

subsection \<open>Antilinear maps and friends\<close>

locale antilinear = additive f for f :: "'a::complex_vector \<Rightarrow> 'b::complex_vector" +
  assumes scaleC: "f (scaleC r x) = cnj r *\<^sub>C f x"

sublocale antilinear \<subseteq> linear
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

lemma antilinear_imp_scaleC:
  fixes D :: "complex \<Rightarrow> 'a::complex_vector"
  assumes "antilinear D"
  obtains d where "D = (\<lambda>x. cnj x *\<^sub>C d)"
proof -
  interpret clinear "D o cnj"
    apply standard apply auto
    apply (simp add: additive.add assms antilinear.axioms(1))
    using assms antilinear.scaleC by fastforce
  obtain d where "D o cnj = (\<lambda>x. x *\<^sub>C d)"
    using clinear_axioms complex_vector.linear_imp_scale by blast
  then have \<open>D = (\<lambda>x. cnj x *\<^sub>C d)\<close>
    by (metis comp_apply complex_cnj_cnj)
  then show ?thesis
    by (rule that)
qed

corollary complex_antilinearD:
  fixes f :: "complex \<Rightarrow> complex"
  assumes "antilinear f" obtains c where "f = (\<lambda>x. c * cnj x)"
  by (rule antilinear_imp_scaleC [OF assms]) (force simp: scaleC_conv_of_complex)

lemma antilinearI:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>c x. f (c *\<^sub>C x) = cnj c *\<^sub>C f x"
  shows "antilinear f"
  by standard (rule assms)+

lemma antilinear_o_antilinear: "antilinear f \<Longrightarrow> antilinear g \<Longrightarrow> clinear (g o f)"
  apply (rule clinearI)
  apply (simp add: additive.add antilinear_def)
  by (simp add: antilinear.scaleC)

lemma clinear_o_antilinear: "antilinear f \<Longrightarrow> clinear g \<Longrightarrow> antilinear (g o f)"
  apply (rule antilinearI)
  apply (simp add: additive.add complex_vector.linear_add antilinear_def)
  by (simp add: complex_vector.linear_scale antilinear.scaleC)

lemma antilinear_o_clinear: "clinear f \<Longrightarrow> antilinear g \<Longrightarrow> antilinear (g o f)"
  apply (rule antilinearI)
  apply (simp add: additive.add complex_vector.linear_add antilinear_def)
  by (simp add: complex_vector.linear_scale antilinear.scaleC)

locale bounded_antilinear = antilinear f for f :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" +
  assumes bounded: "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"

sublocale bounded_antilinear \<subseteq> bounded_linear
  apply standard by (fact bounded)

lemma (in bounded_antilinear) bounded_linear: "bounded_linear f"
  by (fact bounded_linear)

lemma (in bounded_antilinear) antilinear: "antilinear f"
  by (fact antilinear_axioms)

lemma bounded_antilinear_intro:
  assumes "\<And>x y. f (x + y) = f x + f y"
    and "\<And>r x. f (scaleC r x) = scaleC (cnj r) (f x)"
    and "\<And>x. norm (f x) \<le> norm x * K"
  shows "bounded_antilinear f"
  by standard (blast intro: assms)+

lemma cnj_bounded_antilinear[simp]: "bounded_antilinear cnj"
  apply (rule bounded_antilinear_intro [where K = 1])
  by auto

lemma bounded_antilinear_o_bounded_antilinear:
  assumes "bounded_antilinear f"
    and "bounded_antilinear g"
  shows "bounded_clinear (\<lambda>x. f (g x))"
proof
  interpret f: bounded_antilinear f by fact
  interpret g: bounded_antilinear g by fact
  fix b1 b2 b r
  show "f (g (b1 + b2)) = f (g b1) + f (g b2)"
    by (simp add: f.add g.add)
  show "f (g (r *\<^sub>C b)) = r *\<^sub>C f (g b)"
    by (simp add: f.scaleC g.scaleC)
  have "bounded_linear (\<lambda>x. f (g x))"
    using f.bounded_linear g.bounded_linear by (rule bounded_linear_compose)
  then show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    by (rule bounded_linear.bounded)
qed

lemma bounded_antilinear_o_bounded_clinear:
  assumes "bounded_antilinear f"
    and "bounded_clinear g"
  shows "bounded_antilinear (\<lambda>x. f (g x))"
proof
  interpret f: bounded_antilinear f by fact
  interpret g: bounded_clinear g by fact
  show "f (g (x + y)) = f (g x) + f (g y)" for x y
    by (simp only: f.add g.add)
  show "f (g (scaleC r x)) = scaleC (cnj r) (f (g x))" for r x
    by (simp add: f.scaleC g.scaleC)
  have "bounded_linear (\<lambda>x. f (g x))"
    using f.bounded_linear g.bounded_linear by (rule bounded_linear_compose)
  then show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    by (rule bounded_linear.bounded)
qed

lemma bounded_clinear_o_bounded_antilinear:
  assumes "bounded_clinear f"
    and "bounded_antilinear g"
  shows "bounded_antilinear (\<lambda>x. f (g x))"
proof
  interpret f: bounded_clinear f by fact
  interpret g: bounded_antilinear g by fact
  show "f (g (x + y)) = f (g x) + f (g y)" for x y
    by (simp only: f.add g.add)
  show "f (g (scaleC r x)) = scaleC (cnj r) (f (g x))" for r x
    using f.scaleC g.scaleC by fastforce
  have "bounded_linear (\<lambda>x. f (g x))"
    using f.bounded_linear g.bounded_linear by (rule bounded_linear_compose)
  then show "\<exists>K. \<forall>x. norm (f (g x)) \<le> norm x * K"
    by (rule bounded_linear.bounded)
qed

(* lemma (in bounded_cbilinear) bounded_bilinear: "bounded_bilinear prod"
  by (simp add: bounded_bilinear_axioms) *)

lemma bij_clinear_imp_inv_clinear: "clinear (inv f)"
  if a1: "clinear f" and a2: "bij f"
proof
  fix b1 b2 r b
  show "inv f (b1 + b2) = inv f b1 + inv f b2"
    by (simp add: a1 a2 bij_is_inj bij_is_surj complex_vector.linear_add inv_f_eq surj_f_inv_f)
  show "inv f (r *\<^sub>C b) = r *\<^sub>C inv f b"
    using that
    by (smt bij_inv_eq_iff clinear_def complex_vector.linear_scale) 
qed

locale bounded_sesquilinear =
  fixes 
    prod :: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector"
      (infixl "**" 70)
  assumes add_left: "prod (a + a') b = prod a b + prod a' b"
    and add_right: "prod a (b + b') = prod a b + prod a b'"
    and scaleC_left: "prod (r *\<^sub>C a) b = (cnj r) *\<^sub>C (prod a b)"
    and scaleC_right: "prod a (r *\<^sub>C b) = r *\<^sub>C (prod a b)"
    and bounded: "\<exists>K. \<forall>a b. norm (prod a b) \<le> norm a * norm b * K"

sublocale bounded_sesquilinear \<subseteq> bounded_bilinear
  apply standard
  by (auto simp: add_left add_right scaleC_left scaleC_right bounded scaleR_scaleC)

lemma (in bounded_sesquilinear) bounded_bilinear[simp]: "bounded_bilinear prod" 
  by (fact bounded_bilinear_axioms)

lemma (in bounded_sesquilinear) bounded_antilinear_left: "bounded_antilinear (\<lambda>a. prod a b)"
  apply standard
    apply (auto simp add: scaleC_left add_left)
  by (metis ab_semigroup_mult_class.mult_ac(1) bounded)

lemma (in bounded_sesquilinear) bounded_clinear_right: "bounded_clinear (\<lambda>b. prod a b)"
  apply standard
    apply (auto simp add: scaleC_right add_right)
  by (metis ab_semigroup_mult_class.mult_ac(1) ordered_field_class.sign_simps(34) pos_bounded)

lemma (in bounded_sesquilinear) comp1:
  assumes \<open>bounded_clinear g\<close>
  shows \<open>bounded_sesquilinear (\<lambda>x. prod (g x))\<close>
proof
  interpret bounded_clinear g by fact
  fix a a' b b' r
  show "prod (g (a + a')) b = prod (g a) b + prod (g a') b"
    by (simp add: add add_left)
  show "prod (g a) (b + b') = prod (g a) b + prod (g a) b'"
    by (simp add: add add_right)
  show "prod (g (r *\<^sub>C a)) b = cnj r *\<^sub>C prod (g a) b"
    by (simp add: scaleC scaleC_left)
  show "prod (g a) (r *\<^sub>C b) = r *\<^sub>C prod (g a) b"
    by (simp add: scaleC_right)
  interpret bounded_bilinear \<open>(\<lambda>x. prod (g x))\<close>
    by (simp add: bounded_linear comp1)
  show "\<exists>K. \<forall>a b. norm (prod (g a) b) \<le> norm a * norm b * K"
    using bounded by blast
qed

lemma (in bounded_sesquilinear) comp2:
  assumes \<open>bounded_clinear g\<close>
  shows \<open>bounded_sesquilinear (\<lambda>x y. prod x (g y))\<close>
proof
  interpret bounded_clinear g by fact
  fix a a' b b' r
  show "prod (a + a') (g b) = prod a (g b) + prod a' (g b)"
    by (simp add: add add_left)
  show "prod a (g (b + b')) = prod a (g b) + prod a (g b')"
    by (simp add: add add_right)
  show "prod (r *\<^sub>C a) (g b) = cnj r *\<^sub>C prod a (g b)"
    by (simp add: scaleC scaleC_left)
  show "prod a (g (r *\<^sub>C b)) = r *\<^sub>C prod a (g b)"
    by (simp add: scaleC scaleC_right)
  interpret bounded_bilinear \<open>(\<lambda>x y. prod x (g y))\<close>
    apply (rule bounded_bilinear.flip)
    using _ bounded_linear apply (rule bounded_bilinear.comp1)
    using bounded_bilinear by (rule bounded_bilinear.flip)
  show "\<exists>K. \<forall>a b. norm (prod a (g b)) \<le> norm a * norm b * K"
    using bounded by blast
qed

lemma (in bounded_sesquilinear) comp: "bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_sesquilinear (\<lambda>x y. prod (f x) (g y))" 
  using comp1 bounded_sesquilinear.comp2 by auto

lemma scalarR_bounded_clinear: (* TODO rename \<rightarrow> bounded_clinear_const_scaleR *)
  fixes c :: real
  assumes \<open>bounded_clinear f\<close>
  shows \<open>bounded_clinear (\<lambda> x. c *\<^sub>R f x )\<close>
proof-
  have  \<open>bounded_clinear (\<lambda> x. (complex_of_real c) *\<^sub>C f x )\<close>
    by (simp add: assms bounded_clinear_const_scaleC)
  thus ?thesis
    by (simp add: scaleR_scaleC) 
qed

lemma bounded_linear_bounded_clinear:
  \<open>bounded_linear A \<Longrightarrow> \<forall>c x. A (c *\<^sub>C x) = c *\<^sub>C A x \<Longrightarrow> bounded_clinear A\<close>
  apply standard
  by (simp_all add: linear_simps bounded_linear.bounded)

lemma comp_bounded_clinear:
  fixes  A :: \<open>'b::complex_normed_vector \<Rightarrow> 'c::complex_normed_vector\<close> 
    and B :: \<open>'a::complex_normed_vector \<Rightarrow> 'b\<close>
  assumes \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close>
  shows \<open>bounded_clinear (A \<circ> B)\<close>
  by (metis clinear_compose assms(1) assms(2) bounded_clinear_axioms_def bounded_clinear_compose bounded_clinear_def o_def)


lemmas isCont_scaleC [simp] =
  bounded_bilinear.isCont [OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]

(* Use isCont_scaleC instead
lemma isCont_scaleC:
  fixes l :: \<open>'a::complex_normed_vector\<close>
  shows \<open>isCont (\<lambda> v. scaleC a v) l\<close>
  apply (rule linear_continuous_at)
  by (simp add: Complex_Vector_Spaces0.bounded_clinear.bounded_linear bounded_clinear_scaleC_right)
*)

subsection \<open>Cauchy sequences\<close>

lemma (in bounded_clinear) Cauchy: "Cauchy X \<Longrightarrow> Cauchy (\<lambda>n. f (X n))"
  by (simp add: bounded_linear bounded_linear.Cauchy)

subsection \<open>Cauchy Sequences are Convergent\<close>

subsection \<open>The set of complex numbers is a complete metric space\<close>

lemmas sums_of_complex = bounded_linear.sums [OF bounded_clinear_of_complex[THEN bounded_clinear.bounded_linear]]
lemmas summable_of_complex = bounded_linear.summable [OF bounded_clinear_of_complex[THEN bounded_clinear.bounded_linear]]
lemmas suminf_of_complex = bounded_linear.suminf [OF bounded_clinear_of_complex[THEN bounded_clinear.bounded_linear]]

lemmas sums_scaleC_left = bounded_linear.sums[OF bounded_clinear_scaleC_left[THEN bounded_clinear.bounded_linear]]
lemmas summable_scaleC_left = bounded_linear.summable[OF bounded_clinear_scaleC_left[THEN bounded_clinear.bounded_linear]]
lemmas suminf_scaleC_left = bounded_linear.suminf[OF bounded_clinear_scaleC_left[THEN bounded_clinear.bounded_linear]]

lemmas sums_scaleC_right = bounded_linear.sums[OF bounded_clinear_scaleC_right[THEN bounded_clinear.bounded_linear]]
lemmas summable_scaleC_right = bounded_linear.summable[OF bounded_clinear_scaleC_right[THEN bounded_clinear.bounded_linear]]
lemmas suminf_scaleC_right = bounded_linear.suminf[OF bounded_clinear_scaleC_right[THEN bounded_clinear.bounded_linear]]

subsection \<open>Miscellany\<close>

lemma closed_scaleC: 
  fixes S::\<open>'a::complex_normed_vector set\<close> and a :: complex
  assumes \<open>closed S\<close>
  shows \<open>closed ((*\<^sub>C) a ` S)\<close>
proof (cases \<open>a = 0\<close>)
  case True
  then show ?thesis 
    apply (cases \<open>S = {}\<close>)
    by (auto simp: image_constant)
next
  case False
  then have \<open>(*\<^sub>C) a ` S = (*\<^sub>C) (inverse a) -` S\<close>
    by (auto simp add: rev_image_eqI)
  moreover have \<open>closed ((*\<^sub>C) (inverse a) -` S)\<close>
    by (simp add: assms continuous_closed_vimage)
  ultimately show ?thesis
    by simp
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
        by simp
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
  assumes a1: \<open>bounded_clinear f\<close>
  shows  \<open>onorm (\<lambda> x. r *\<^sub>C (f x)) = (cmod r) * onorm f\<close>
proof-
  have \<open>(norm (f x)) / norm x \<le> onorm f\<close>
    for x
    using a1
    by (simp add: bounded_clinear.bounded_linear le_onorm)        
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
  assumes r: "bounded_clinear r"
  shows "onorm (\<lambda>x. r x *\<^sub>C f) \<le> onorm r * norm f"
proof (rule onorm_bound)
  fix x
  have "norm (r x *\<^sub>C f) = norm (r x) * norm f"
    by simp
  also have "\<dots> \<le> onorm r * norm x * norm f"
    by (simp add: bounded_clinear.bounded_linear mult.commute mult_left_mono onorm r)
  finally show "norm (r x *\<^sub>C f) \<le> onorm r * norm f * norm x"
    by (simp add: ac_simps)
  show "0 \<le> onorm r * norm f"
    by (simp add: bounded_clinear.bounded_linear onorm_pos_le r)
qed

lemma onorm_scaleC_left:
  fixes f :: "'a::complex_normed_vector"
  assumes f: "bounded_clinear r"
  shows "onorm (\<lambda>x. r x *\<^sub>C f) = onorm r * norm f"
proof (cases "f = 0")
  assume "f \<noteq> 0"
  show ?thesis
  proof (rule order_antisym)
    show "onorm (\<lambda>x. r x *\<^sub>C f) \<le> onorm r * norm f"
      using f by (rule onorm_scaleC_left_lemma)
  next
    have bl1: "bounded_clinear (\<lambda>x. r x *\<^sub>C f)"
      by (metis bounded_clinear_scaleC_const f)
    have x1:"bounded_clinear (\<lambda>x. r x * norm f)"
      by (metis bounded_clinear_mult_const f)

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
        using bl1 bounded_clinear.bounded_linear by auto
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

locale closed_csubspace =
  fixes A::"('a::{complex_vector,topological_space}) set"
  assumes subspace: "csubspace A"
  assumes closed: "closed A"

declare closed_csubspace.subspace[simp]
(* declare closed_csubspace.closed[simp] *)

lemma closure_is_csubspace[simp]:
  fixes A::"('a::complex_normed_vector) set"
  assumes \<open>csubspace A\<close>
  shows \<open>csubspace (closure A)\<close>
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
      using \<open>\<forall>n. xx n \<in> A\<close> \<open>\<forall>n. yy n \<in> A\<close> assms complex_vector.subspace_def
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
      using bounded_clinear.bounded_linear bounded_clinear_scaleC_right linear_continuous_at by auto
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

lemma csubspace_set_plus:
  assumes \<open>csubspace A\<close> and \<open>csubspace B\<close>
  shows \<open>csubspace (A + B)\<close>
proof -
  define C where \<open>C = {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}\<close>
  have  "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> x+y\<in>C" for x y
    using C_def assms(1) assms(2) complex_vector.subspace_add complex_vector.subspace_sums by blast
  moreover have "c *\<^sub>C x \<in> C" if \<open>x\<in>C\<close> for x c
  proof -
    have "csubspace C"
      by (simp add: C_def assms(1) assms(2) complex_vector.subspace_sums)
    then show ?thesis
      using that by (simp add: complex_vector.subspace_def)
  qed
  moreover have  "0 \<in> C"
    using  \<open>C = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close> add.inverse_neutral add_uminus_conv_diff assms(1) assms(2) diff_0  mem_Collect_eq
      add.right_inverse
    by (metis (mono_tags, lifting) complex_vector.subspace_0)
  ultimately show ?thesis
    unfolding C_def complex_vector.subspace_def
    by (smt mem_Collect_eq set_plus_elim set_plus_intro)    
qed

lemma closed_csubspace_0[simp]:
  "closed_csubspace ({0} :: ('a::{complex_vector,t1_space}) set)"
proof-
  have \<open>csubspace {0}\<close>
    using add.right_neutral complex_vector.subspace_def scaleC_right.zero
    by blast    
  moreover have "closed ({0} :: 'a set)"
    by simp 
  ultimately show ?thesis 
    by (simp add: closed_csubspace_def)
qed

lemma closed_csubspace_UNIV[simp]: "closed_csubspace (UNIV::('a::{complex_vector,topological_space}) set)"
proof-
  have \<open>csubspace UNIV\<close>
    by simp  
  moreover have \<open>closed UNIV\<close>
    by simp
  ultimately show ?thesis 
    unfolding closed_csubspace_def by auto
qed

lemma closed_csubspace_inter[simp]:
  assumes "closed_csubspace A" and "closed_csubspace B"
  shows "closed_csubspace (A\<inter>B)"
proof-
  obtain C where \<open>C = A \<inter> B\<close> by blast
  have \<open>csubspace C\<close>
  proof-
    have "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> x+y\<in>C" for x y
      by (metis IntD1 IntD2 IntI \<open>C = A \<inter> B\<close> assms(1) assms(2) complex_vector.subspace_def closed_csubspace_def)
    moreover have "x\<in>C \<Longrightarrow> c *\<^sub>C x \<in> C" for x c
      by (metis IntD1 IntD2 IntI \<open>C = A \<inter> B\<close> assms(1) assms(2) complex_vector.subspace_def closed_csubspace_def)
    moreover have "0 \<in> C" 
      using  \<open>C = A \<inter> B\<close> assms(1) assms(2) complex_vector.subspace_def closed_csubspace_def by fastforce
    ultimately show ?thesis 
      by (simp add: complex_vector.subspace_def)
  qed
  moreover have \<open>closed C\<close>
    using  \<open>C = A \<inter> B\<close>
    by (simp add: assms(1) assms(2) closed_Int closed_csubspace.closed)
  ultimately show ?thesis
    using  \<open>C = A \<inter> B\<close>
    by (simp add: closed_csubspace_def)
qed


lemma closed_csubspace_INF[simp]:
  assumes a1: "\<forall>A\<in>\<A>. closed_csubspace A"
  shows "closed_csubspace (\<Inter>\<A>)"
proof-
  have \<open>csubspace (\<Inter>\<A>)\<close>
    by (simp add: assms closed_csubspace.subspace complex_vector.subspace_Inter)
  moreover have \<open>closed (\<Inter>\<A>)\<close>
    by (simp add: assms closed_Inter closed_csubspace.closed)
  ultimately show ?thesis 
    by (simp add: closed_csubspace.intro)
qed


subsection \<open>Linear space\<close>


typedef (overloaded) ('a::"{complex_vector,topological_space}") 
  ccsubspace = \<open>{S::'a set. closed_csubspace S}\<close>
  morphisms space_as_set Abs_clinear_space
  using Complex_Vector_Spaces.closed_csubspace_UNIV by blast


setup_lifting type_definition_ccsubspace

instantiation ccsubspace :: (complex_normed_vector) scaleC begin
lift_definition scaleC_ccsubspace :: "complex \<Rightarrow> 'a ccsubspace \<Rightarrow> 'a ccsubspace" is
  "\<lambda>c S. (*\<^sub>C) c ` S"
proof
  show "csubspace ((*\<^sub>C) c ` S)"
    if "closed_csubspace S"
    for c :: complex
      and S :: "'a set"
    using that
    by (simp add: closed_csubspace.subspace complex_vector.linear_subspace_image) 
  show "closed ((*\<^sub>C) c ` S)"
    if "closed_csubspace S"
    for c :: complex
      and S :: "'a set"
    using that
    by (simp add: closed_scaleC closed_csubspace.closed) 
qed

lift_definition scaleR_ccsubspace :: "real \<Rightarrow> 'a ccsubspace \<Rightarrow> 'a ccsubspace" is
  "\<lambda>c S. (*\<^sub>R) c ` S"
proof
  show "csubspace ((*\<^sub>R) r ` S)"
    if "closed_csubspace S"
    for r :: real
      and S :: "'a set"
    using that   using bounded_clinear_def bounded_clinear_scaleC_right scaleR_scaleC
    by (simp add: scaleR_scaleC closed_csubspace.subspace complex_vector.linear_subspace_image)
  show "closed ((*\<^sub>R) r ` S)"
    if "closed_csubspace S"
    for r :: real
      and S :: "'a set"
    using that 
    by (simp add: closed_scaling closed_csubspace.closed)
qed

instance 
proof
  show "((*\<^sub>R) r::'a ccsubspace \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)" for r :: real
    by (simp add: scaleR_scaleC scaleC_ccsubspace_def scaleR_ccsubspace_def)    
qed
end

instantiation ccsubspace :: ("{complex_vector,t1_space}") bot begin
lift_definition bot_ccsubspace :: \<open>'a ccsubspace\<close> is \<open>{0}\<close>
  by simp
instance..
end

lemma zero_scaleC_ccsubspace[simp]: "0 *\<^sub>C S = bot" for S :: "_ ccsubspace"
proof transfer
  have "(0::'b) \<in> (\<lambda>x. 0) ` S"
    if "closed_csubspace S"
    for S::"'b set"
    using that unfolding closed_csubspace_def
    by (simp add: complex_vector.linear_subspace_image complex_vector.module_hom_zero 
        complex_vector.subspace_0)
  thus "(*\<^sub>C) 0 ` S = {0::'b}"
    if "closed_csubspace (S::'b set)"
    for S :: "'b set"
    using that 
    by (auto intro !: exI [of _ 0])
qed

lemma csubspace_scaleC_invariant: 
  fixes a S
  assumes \<open>a \<noteq> 0\<close> and \<open>csubspace S\<close>
  shows \<open>(*\<^sub>C) a ` S = S\<close>
proof-
  have  \<open>x \<in> (*\<^sub>C) a ` S \<Longrightarrow> x \<in> S\<close>
    for x
    using assms(2) complex_vector.subspace_scale by blast 
  moreover have  \<open>x \<in> S \<Longrightarrow> x \<in> (*\<^sub>C) a ` S\<close>
    for x
  proof -
    assume "x \<in> S"
    hence "\<exists>c aa. (c / a) *\<^sub>C aa \<in> S \<and> c *\<^sub>C aa = x"
      using assms(2) complex_vector.subspace_def scaleC_one by metis
    hence "\<exists>aa. aa \<in> S \<and> a *\<^sub>C aa = x"
      using assms(1) by auto
    thus ?thesis
      by (meson image_iff)
  qed 
  ultimately show ?thesis by blast
qed


lemma ccsubspace_scaleC_invariant[simp]: "a \<noteq> 0 \<Longrightarrow> a *\<^sub>C S = S" for S :: "_ ccsubspace"
  apply transfer
  by (simp add: closed_csubspace.subspace csubspace_scaleC_invariant)


instantiation ccsubspace :: ("{complex_vector,topological_space}") "top"
begin
lift_definition top_ccsubspace :: \<open>'a ccsubspace\<close> is \<open>UNIV\<close>
  by simp

instance ..
end

lemma ccsubspace_top_not_bot[simp]: 
  "(top::'a::{complex_vector,t1_space,not_singleton} ccsubspace) \<noteq> bot"
  (* The type class t1_space is needed because the definition of bot in ccsubspace needs it *)
  by (metis UNIV_not_singleton bot_ccsubspace.rep_eq top_ccsubspace.rep_eq)

lemma ccsubspace_bot_not_top[simp]:
  "(bot::'a::{complex_vector,t1_space,not_singleton} ccsubspace) \<noteq> top"
  using ccsubspace_top_not_bot by metis

instantiation ccsubspace :: ("{complex_vector,topological_space}") "Inf"
begin
lift_definition Inf_ccsubspace::\<open>'a ccsubspace set \<Rightarrow> 'a ccsubspace\<close>
  is \<open>\<lambda> S. \<Inter> S\<close>
proof
  fix S :: "'a set set"
  assume closed: "closed_csubspace x" if \<open>x \<in> S\<close> for x
  show "csubspace (\<Inter> S::'a set)"
    by (simp add: closed closed_csubspace.subspace) 
  show "closed (\<Inter> S::'a set)"
    by (simp add: closed closed_csubspace.closed) 
qed

instance ..
end


subsection \<open>ccspan\<close>

lift_definition ccspan :: "'a::complex_normed_vector set \<Rightarrow> 'a ccsubspace"
  is "\<lambda>G. closure (cspan G)"
proof (rule closed_csubspace.intro)
  fix S :: "'a set"
  show "csubspace (closure (cspan S))"
    by (simp add: closure_is_csubspace)    
  show "closed (closure (cspan S))"
    by simp
qed

(* Replaced by complex_vector.span_minimal *)
(* lemma cspan_inside_closed_csubspace:
  assumes \<open>closed_csubspace S\<close> and \<open>A \<subseteq> S\<close>
  shows \<open>cspan A \<subseteq> S\<close> *)

(* Use complex_vector.span_superset instead *)
(* lemma cspan_inside_closed_csubspace_converse:
  assumes \<open>closed_csubspace S\<close> and \<open>cspan A \<subseteq> S\<close>
  shows \<open>A \<subseteq> S\<close> *)

lemma ccspan_Inf_def: \<open>ccspan A = Inf {S. A \<subseteq> space_as_set S}\<close>
  for A::\<open>('a::cbanach) set\<close>
proof-
  have \<open>x \<in> space_as_set (ccspan A) 
    \<Longrightarrow> x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
    for x::'a
  proof-
    assume \<open>x \<in> space_as_set (ccspan A)\<close>
    hence "x \<in> closure (cspan A)"
      by (simp add: ccspan.rep_eq)
    hence \<open>x \<in> closure (complex_vector.span A)\<close>
      unfolding ccspan_def
      by simp
    hence \<open>\<exists> y::nat \<Rightarrow> 'a. (\<forall> n. y n \<in> (complex_vector.span A)) \<and> y \<longlonglongrightarrow> x\<close>
      by (simp add: closure_sequential)
    then obtain y where \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close> and \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>y n \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S}\<close>
      for n
      using  \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close>
      by auto

    have \<open>closed_csubspace S \<Longrightarrow> closed S\<close>
      for S::\<open>'a set\<close>
      by (simp add: closed_csubspace.closed)
    hence \<open>closed ( \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S})\<close>
      by simp
    hence \<open>x \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S}\<close> using \<open>y \<longlonglongrightarrow> x\<close>
      using \<open>\<And>n. y n \<in> \<Inter> {S. complex_vector.span A \<subseteq> S \<and> closed_csubspace S}\<close> closed_sequentially 
      by blast
    moreover have \<open>{S. A \<subseteq> S \<and> closed_csubspace S} \<subseteq> {S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S}\<close>
      using Collect_mono_iff
      by (simp add: Collect_mono_iff closed_csubspace.subspace complex_vector.span_minimal)
    ultimately have \<open>x \<in> \<Inter> {S. A \<subseteq> S \<and> closed_csubspace S}\<close>
      by blast     
    moreover have "(x::'a) \<in> \<Inter> {x. A \<subseteq> x \<and> closed_csubspace x}"
      if "(x::'a) \<in> \<Inter> {S. A \<subseteq> S \<and> closed_csubspace S}"
      for x :: 'a
        and A :: "'a set"
      using that
      by simp
    ultimately show \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close> 
      apply transfer.
  qed
  moreover have \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})
             \<Longrightarrow> x \<in> space_as_set (ccspan A)\<close>
    for x::'a
  proof-
    assume \<open>x \<in> space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
    hence \<open>x \<in> \<Inter> {S. A \<subseteq> S \<and> closed_csubspace S}\<close>
      apply transfer
      by blast
    moreover have \<open>{S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S} \<subseteq> {S. A \<subseteq> S \<and> closed_csubspace S}\<close>
      using Collect_mono_iff complex_vector.span_superset by fastforce
    ultimately have \<open>x \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> closed_csubspace S}\<close>
      by blast 
    thus \<open>x \<in> space_as_set (ccspan A)\<close>
      by (metis (no_types, lifting) Inter_iff space_as_set closure_subset mem_Collect_eq ccspan.rep_eq)      
  qed
  ultimately have \<open>space_as_set (ccspan A) = space_as_set (Inf {S. A \<subseteq> space_as_set S})\<close>
    by blast
  thus ?thesis
    using space_as_set_inject by auto 
qed

lemma cspan_singleton_scaleC[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> cspan { a *\<^sub>C \<psi> } = cspan {\<psi>}"
  for \<psi>::"'a::complex_vector"
  by (smt complex_vector.dependent_single complex_vector.independent_insert 
      complex_vector.scale_eq_0_iff complex_vector.span_base complex_vector.span_redundant 
      complex_vector.span_scale doubleton_eq_iff insert_absorb insert_absorb2 insert_commute 
      singletonI)

lemma closure_is_closed_csubspace:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes \<open>csubspace S\<close>
  shows \<open>closed_csubspace (closure S)\<close>
proof-
  fix x y :: 'a and c :: complex
  have "x + y \<in> closure S"
    if "x \<in> closure S"
      and "y \<in> closure S"
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
      by (simp add: complex_vector.subspace_add) 
  qed
  moreover have "c *\<^sub>C x \<in> closure S"
    if "x \<in> closure S"
  proof-
    have \<open>\<exists> y. (\<forall> n::nat. y n \<in> S) \<and> y \<longlonglongrightarrow> x\<close>
      using Elementary_Topology.closure_sequential that by auto
    then obtain y where \<open>\<forall> n::nat. y n \<in> S\<close> and \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>isCont (scaleC c) x\<close>
      by simp
    hence \<open>(\<lambda> n. scaleC c (y n)) \<longlonglongrightarrow> scaleC c x\<close>
      using  \<open>y \<longlonglongrightarrow> x\<close>
      by (simp add: isCont_tendsto_compose) 
    from  \<open>\<forall> n::nat. y n \<in> S\<close>
    have  \<open>\<forall> n::nat. scaleC c (y n) \<in> S\<close>
      using assms complex_vector.subspace_scale by auto
    thus ?thesis
      using assms that
      by (simp add: complex_vector.subspace_scale) 
  qed
  moreover have "0 \<in> closure S"
    by (simp add: assms complex_vector.subspace_0)
  moreover have "closed (closure S)"
    by auto
  ultimately show ?thesis
    by (simp add: assms closed_csubspace_def)
qed

lemma clinear_continuous_at:
  assumes \<open>bounded_clinear f\<close> 
  shows \<open>isCont f x\<close>
  by (simp add: assms bounded_clinear.bounded_linear linear_continuous_at)

lemma clinear_continuous_within:
  assumes \<open>bounded_clinear f\<close> 
  shows \<open>continuous (at x within s) f\<close>
  by (simp add: assms bounded_clinear.bounded_linear linear_continuous_within)

lemma antilinear_continuous_at:
  assumes \<open>bounded_antilinear f\<close> 
  shows \<open>isCont f x\<close>
  by (simp add: assms bounded_antilinear.bounded_linear linear_continuous_at)

lemma antilinear_continuous_within:
  assumes \<open>bounded_antilinear f\<close> 
  shows \<open>continuous (at x within s) f\<close>
  by (simp add: assms bounded_antilinear.bounded_linear linear_continuous_within)


(* Use complex_vector.linear_eq_0_on_span instead *)
(* lemma equal_span_0:
  fixes f::\<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close> 
    and S::\<open>'a set\<close> and x::'a
  assumes \<open>clinear f\<close> and \<open>\<forall> t \<in> S. f t = 0\<close> and xS: \<open>x \<in> cspan S\<close> 
  shows \<open>f x = 0\<close> *)

instantiation ccsubspace :: ("{complex_vector,topological_space}") "order"
begin
lift_definition less_eq_ccsubspace :: \<open>'a ccsubspace \<Rightarrow> 'a ccsubspace \<Rightarrow> bool\<close>
  is  \<open>(\<subseteq>)\<close>.
declare less_eq_ccsubspace_def[code del]
lift_definition less_ccsubspace :: \<open>'a ccsubspace \<Rightarrow> 'a ccsubspace \<Rightarrow> bool\<close>
  is \<open>(\<subset>)\<close>.
declare less_ccsubspace_def[code del]
instance
proof
  fix x y z :: "'a ccsubspace"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (simp add: less_eq_ccsubspace.rep_eq less_le_not_le less_ccsubspace.rep_eq)    
  show "x \<le> x"
    by (simp add: less_eq_ccsubspace.rep_eq)    
  show "x \<le> z" if "x \<le> y" and "y \<le> z"
    using that less_eq_ccsubspace.rep_eq by auto 
  show "x = y" if "x \<le> y" and "y \<le> x"
    using that by (simp add: space_as_set_inject less_eq_ccsubspace.rep_eq) 
qed
end

lemma bounded_clinear_id[simp]: \<open>bounded_clinear id\<close>
  by (simp add: id_def)

lemma bounded_sesquilinear_add:
  \<open>bounded_sesquilinear (\<lambda> x y. A x y + B x y)\<close> if \<open>bounded_sesquilinear A\<close> and \<open>bounded_sesquilinear B\<close>
proof
  fix a a' :: 'a and b b' :: 'b and r :: complex
  show "A (a + a') b + B (a + a') b = (A a b + B a b) + (A a' b + B a' b)"
    by (simp add: bounded_sesquilinear.add_left that(1) that(2))
  show \<open>A a (b + b') + B a (b + b') = (A a b + B a b) + (A a b' + B a b')\<close>
    by (simp add: bounded_sesquilinear.add_right that(1) that(2))
  show \<open>A (r *\<^sub>C a) b + B (r *\<^sub>C a) b = cnj r *\<^sub>C (A a b + B a b)\<close>
    by (simp add: bounded_sesquilinear.scaleC_left scaleC_add_right that(1) that(2))
  show \<open>A a (r *\<^sub>C b) + B a (r *\<^sub>C b) = r *\<^sub>C (A a b + B a b)\<close>
    by (simp add: bounded_sesquilinear.scaleC_right scaleC_add_right that(1) that(2))
  show \<open>\<exists>K. \<forall>a b. norm (A a b + B a b) \<le> norm a * norm b * K\<close>
  proof-
    have \<open>\<exists> KA. \<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
      by (simp add: bounded_sesquilinear.bounded that(1))
    then obtain KA where \<open>\<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
      by blast
    have \<open>\<exists> KB. \<forall> a b. norm (B a b) \<le> norm a * norm b * KB\<close>
      by (simp add: bounded_sesquilinear.bounded that(2))
    then obtain KB where \<open>\<forall> a b. norm (B a b) \<le> norm a * norm b * KB\<close>
      by blast
    have \<open>norm (A a b + B a b) \<le> norm a * norm b * (KA + KB)\<close>
      for a b
    proof-
      have \<open>norm (A a b + B a b) \<le> norm (A a b) +  norm (B a b)\<close>
        using norm_triangle_ineq by blast
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

lemma bounded_sesquilinear_uminus:
  \<open>bounded_sesquilinear (\<lambda> x y. - A x y)\<close> if \<open>bounded_sesquilinear A\<close>
proof
  fix a a' :: 'a and b b' :: 'b and r :: complex
  show "- A (a + a') b = (- A a b) + (- A a' b)"
    by (simp add: bounded_sesquilinear.add_left that)
  show \<open>- A a (b + b') = (- A a b) + (- A a b')\<close>
    by (simp add: bounded_sesquilinear.add_right that)
  show \<open>- A (r *\<^sub>C a) b = cnj r *\<^sub>C (- A a b)\<close>
    by (simp add: bounded_sesquilinear.scaleC_left that)
  show \<open>- A a (r *\<^sub>C b) = r *\<^sub>C (- A a b)\<close>
    by (simp add: bounded_sesquilinear.scaleC_right that)
  show \<open>\<exists>K. \<forall>a b. norm (- A a b) \<le> norm a * norm b * K\<close>
  proof-
    have \<open>\<exists> KA. \<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
      by (simp add: bounded_sesquilinear.bounded that(1))
    then obtain KA where \<open>\<forall> a b. norm (A a b) \<le> norm a * norm b * KA\<close>
      by blast
    have \<open>norm (- A a b) \<le> norm a * norm b * KA\<close>
      for a b
      by (simp add: \<open>\<forall>a b. norm (A a b) \<le> norm a * norm b * KA\<close>)
    thus ?thesis by blast
  qed
qed

lemma bounded_sesquilinear_diff:
  \<open>bounded_sesquilinear (\<lambda> x y. A x y - B x y)\<close> if \<open>bounded_sesquilinear A\<close> and \<open>bounded_sesquilinear B\<close>
proof -
  have \<open>bounded_sesquilinear (\<lambda> x y. - B x y)\<close>
    using that(2) by (rule bounded_sesquilinear_uminus)
  then have \<open>bounded_sesquilinear (\<lambda> x y. A x y + (- B x y))\<close>
    using that(1) by (rule bounded_sesquilinear_add[rotated])
  then show ?thesis
    by auto
qed

subsection \<open>Unsorted\<close>


(* lemma complex_dependent_isolation:
  assumes \<open>cdependent V\<close> and \<open>finite V\<close>
  shows \<open>\<exists> f. \<exists> s\<in>V. s = (\<Sum>v\<in>V-{s}. f v *\<^sub>C v )\<close>
proof-
  from \<open>cdependent V\<close>
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
    using complex_vector.scale_sum_right
      [where f = "(\<lambda> i. f i *\<^sub>C i)" and A = "V - {s}" and a = "inverse (- f s)"]
    by auto
  finally have \<open>s = (\<Sum>i\<in>V-{s}. ((f i) /\<^sub>C (- f s)) *\<^sub>C i)\<close>
    by blast
  thus ?thesis 
    using \<open>s \<in> V\<close> 
    by metis
qed *)

definition cbilinear :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector) \<Rightarrow> bool\<close>
  where \<open>cbilinear = (\<lambda> f. (\<forall> y. clinear (\<lambda> x. f x y)) \<and> (\<forall> x. clinear (\<lambda> y. f x y)) )\<close>

lemma cbilinear_times:
  fixes g' :: \<open>'a::complex_vector \<Rightarrow> complex\<close> and g :: \<open>'b::complex_vector \<Rightarrow> complex\<close>
  assumes \<open>\<And> x y. h x y = (g' x)*(g y)\<close> and \<open>clinear g\<close> and \<open>clinear g'\<close>
  shows \<open>cbilinear h\<close>
proof -
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

(* lemma bilinear_Kronecker_delta:
  fixes u::\<open>'a::complex_vector\<close> and v::\<open>'b::complex_vector\<close>
  assumes \<open>cindependent A\<close> and \<open>cindependent B\<close>
    and \<open>u \<in> A\<close> and \<open>v \<in> B\<close>
  shows \<open>\<exists> h::_\<Rightarrow>_\<Rightarrow>complex. cbilinear h \<and> (h u v = 1) \<and>
    (\<forall>x\<in>A. \<forall>y\<in>B. (x,y) \<noteq> (u,v) \<longrightarrow> h x y = 0)\<close>
proof-
  define f where \<open>f x = (if x = v then (1::complex) else 0)\<close> 
    for x
  have \<open>\<exists>g. clinear g \<and> (\<forall>x\<in>B. g x = f x)\<close>
    using \<open>complex_vector.independent B\<close> complex_vector.linear_independent_extend
    by (simp add: complex_vector.linear_independent_extend cdependent_raw_def) 
  then obtain g where \<open>clinear g\<close> and \<open>\<forall>x\<in>B. g x = f x\<close>
    by blast
  define f' where \<open>f' x = (if x = u then (1::complex) else 0)\<close> for x
  hence \<open>\<exists>g'. clinear g' \<and> (\<forall>x\<in>A. g' x = f' x)\<close>
    by (simp add: cdependent_raw_def assms(1) complex_vector.linear_independent_extend)    
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
    by (simp add: \<open>clinear g'\<close> \<open>clinear g\<close> cbilinear_times h_def)
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
qed *)



lemma vector_finitely_spanned:
  assumes \<open>z \<in> cspan T\<close>
  shows \<open>\<exists> S. finite S \<and> S \<subseteq> T \<and> z \<in> cspan S\<close>
proof-
  have \<open>\<exists> S r. finite S \<and> S \<subseteq> T \<and> z = (\<Sum>a\<in>S. r a *\<^sub>C a)\<close>
    using complex_vector.span_explicit[where b = "T"]
      assms by auto
  then obtain S r where \<open>finite S\<close> and \<open>S \<subseteq> T\<close> and \<open>z = (\<Sum>a\<in>S. r a *\<^sub>C a)\<close>
    by blast
  thus ?thesis
    by (meson complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset subset_iff) 
qed

(* Use complex_vector.span_finite instead
lemma span_explicit_finite:
  assumes a1: \<open>x \<in> cspan S\<close> 
    and a2: \<open>complex_vector.independent S\<close>
    and a3: \<open>finite S\<close>
  shows \<open>\<exists> t. x = (\<Sum>s\<in>S. t s *\<^sub>C s)\<close>
*)

setup \<open>Sign.add_const_constraint ("Complex_Vector_Spaces0.cindependent", SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cdependent\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cspan\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> 'a set\<close>)\<close>

class cfinite_dim = complex_vector +
  assumes cfinitely_spanned: "\<exists>S::'a set. finite S \<and> cspan S = UNIV"

class basis_enum = complex_vector +
  fixes canonical_basis :: "'a list"
  assumes distinct_canonical_basis[simp]: 
    "distinct canonical_basis"
    and is_cindependent_set:
    "cindependent (set canonical_basis)"
    and is_generator_set:
    "cspan (set canonical_basis) = UNIV" 

setup \<open>Sign.add_const_constraint ("Complex_Vector_Spaces0.cindependent", SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cdependent\<close>, SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> bool\<close>)\<close>
setup \<open>Sign.add_const_constraint (\<^const_name>\<open>cspan\<close>, SOME \<^typ>\<open>'a::complex_vector set \<Rightarrow> 'a set\<close>)\<close>

(* TODO: remove *)
abbreviation (input) canonical_basis_length :: "'a::basis_enum itself \<Rightarrow> nat" where \<open>canonical_basis_length _ \<equiv> length (canonical_basis::'a list)\<close>

lemma ccspan_canonical_basis[simp]: "ccspan (set canonical_basis) = top"
  using ccspan.rep_eq space_as_set_inject top_ccsubspace.rep_eq
    closure_UNIV is_generator_set
  by metis

lemma finite_basis: "\<exists>basis::'a::cfinite_dim set. finite basis \<and> cindependent basis \<and> cspan basis = UNIV"
proof -
  from cfinitely_spanned
  obtain S :: \<open>'a set\<close> where \<open>finite S\<close> and \<open>cspan S = UNIV\<close>
    by auto
  from complex_vector.maximal_independent_subset
  obtain B :: \<open>'a set\<close> where \<open>B \<subseteq> S\<close> and \<open>cindependent B\<close> and \<open>S \<subseteq> cspan B\<close>
    by metis
  moreover have \<open>finite B\<close>
    using \<open>B \<subseteq> S\<close> \<open>finite S\<close>
    by (meson finite_subset) 
  moreover have \<open>cspan B = UNIV\<close>
    using \<open>cspan S = UNIV\<close> \<open>S \<subseteq> cspan B\<close>
    by (metis complex_vector.span_eq top_greatest)
  ultimately show ?thesis
    by auto
qed

instance basis_enum \<subseteq> cfinite_dim
  apply intro_classes
  apply (rule exI[of _ \<open>set canonical_basis\<close>])
  using is_cindependent_set is_generator_set by auto

lemma cindependent_cfinite_dim_finite:
  assumes \<open>cindependent (S::'a::cfinite_dim set)\<close>
  shows \<open>finite S\<close>
  by (metis assms cfinitely_spanned complex_vector.independent_span_bound top_greatest)

lemma ccsubspace_leI:
  assumes t1: "space_as_set A \<subseteq> space_as_set B"
  shows "A \<le> B"
  using t1 apply transfer by -

(* Use tendsto_sum instead *)
(* lemma finite_sum_tendsto:
  fixes A::\<open>'a set\<close> and r :: "'a \<Rightarrow> nat \<Rightarrow> 'b::{comm_monoid_add,topological_monoid_add}"
  assumes t1: \<open>\<And>a. a \<in> A \<Longrightarrow> r a \<longlonglongrightarrow> \<phi> a\<close> 
    and t2: \<open>finite A\<close>
  shows \<open>(\<lambda> n. (\<Sum>a\<in>A. r a n)) \<longlonglongrightarrow>  (\<Sum>a\<in>A. \<phi> a)\<close> *)

context bounded_cbilinear begin
interpretation bounded_bilinear prod by simp
lemmas tendsto = tendsto
lemmas isCont = isCont
end

context bounded_sesquilinear begin
interpretation bounded_bilinear prod by simp
lemmas tendsto = tendsto
lemmas isCont = isCont
end



lemmas tendsto_scaleC [tendsto_intros] =
  bounded_cbilinear.tendsto [OF bounded_cbilinear_scaleC]

lemma csubspace_is_subspace: "csubspace A \<Longrightarrow> subspace A"
  apply (rule subspaceI) 
  by (auto simp: complex_vector.subspace_def scaleR_scaleC)

lemma span_subset_cspan: "span A \<subseteq> cspan A"
  unfolding span_def complex_vector.span_def
  by (simp add: csubspace_is_subspace hull_antimono)

lemma cindependent_implies_independent: 
  assumes "cindependent (S::'a::complex_vector set)"
  shows "independent S"
  using assms unfolding dependent_def complex_vector.dependent_def
  using span_subset_cspan by blast

lemma cspan_singleton: "cspan {x} = {\<alpha> *\<^sub>C x| \<alpha>. True}"
(* Was:
lemma cspan_singleton:
  fixes x y::"'a::complex_vector"
  assumes a1: "x \<in> cspan {y}"
  shows "\<exists>\<alpha>. x = \<alpha> *\<^sub>C y"
*)
proof -
  have \<open>cspan {x} = {y. y\<in>cspan {x}}\<close>
    by auto
  also have \<open>\<dots> = {\<alpha> *\<^sub>C x| \<alpha>. True}\<close>
    apply (subst complex_vector.span_breakdown_eq)
    by auto
  finally show ?thesis
    by -
qed

lemma ccspan_of_empty[simp]: "ccspan {} = bot"
proof transfer
  show "closure (cspan {}) = {0::'a}"
    by simp
qed


(* Use bounded_bilinear.zero_left instead *)
(* lemma bounded_sesquilinear_0_left:
  assumes \<open>bounded_sesquilinear B\<close>
  shows \<open>B 0 y = 0\<close> *)


(* lemma sesquilinear_finite_sum_induction:
  assumes \<open>bounded_sesquilinear B\<close>
  shows \<open>\<forall>t. finite t \<and> card t = n \<longrightarrow> B (\<Sum>a\<in>t. (r a) *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)\<close>
proof(induction n)
  case 0 thus ?case
    by (metis (no_types, lifting) assms bounded_sesquilinear.scaleC_left card_eq_0_iff complex_cnj_zero complex_vector.scale_eq_0_iff sum_clauses(1))
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
 *)


(* Use bounded_bilinear.sum_left and bounded_sesquilinear.scaleC_left instead *)
(* lemma sesquilinear_finite_sum:                     
  assumes \<open>bounded_sesquilinear B\<close> and \<open>finite t\<close>
  shows \<open>B (\<Sum>a\<in>t. (r a) *\<^sub>C a) y = (\<Sum>a\<in>t. cnj (r a) *\<^sub>C B a y)\<close> *)

(* lemma bounded_sesquilinear_continuous:
  includes nsa_notation
  assumes \<open>bounded_sesquilinear B\<close>
    and \<open>star_of x \<approx> u\<close> and \<open>star_of y \<approx> v\<close>
  shows \<open>( *f2* B) (star_of x) (star_of y) \<approx> ( *f2* B) u v\<close>
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
  hence \<open>\<forall> p q. ( *f2* B) (star_of x) (star_of y) = ( *f2* B) (star_of x - p) (star_of y - q)
     + (( *f2* B) (star_of x) q - ( *f2* B) p q)
     + (( *f2* B) p (star_of y) - ( *f2* B) p q) + ( *f2* B) p q\<close>
    by StarDef.transfer
  hence \<open>( *f2* B) (star_of x) (star_of y) \<approx>
     ( *f2* B) (star_of x - p) (star_of y - q)
   + (( *f2* B) (star_of x) q - ( *f2* B) p q)
   + (( *f2* B) p (star_of y) - ( *f2* B) p q) + ( *f2* B) p q\<close>
    for p q
    by auto
  moreover have \<open>( *f2* B) (star_of x - u) (star_of y - v) \<approx> 0\<close>
  proof-
    have \<open>\<exists> K. \<forall> p q. norm (B (x - p) (y - q)) \<le> norm (x - p) * norm (y - q) * K\<close>
      using assms(1) bounded_sesquilinear.bounded by blast
    then obtain K where \<open>\<forall> p q. norm (B (x - p) (y - q)) \<le> norm (x - p) * norm (y - q) * K\<close>
      by blast
    hence  \<open>\<forall> p q. hnorm (( *f2* B) (star_of x - p) (star_of y - q))
         \<le> hnorm (star_of x - p) * hnorm (star_of y - q) * (star_of K)\<close>
      by StarDef.transfer
    hence \<open>hnorm (( *f2* B) (star_of x - u) (star_of y - v)) 
      \<le> hnorm (star_of x - u) * hnorm (star_of y - v) * (star_of K)\<close>
      by blast
    moreover have \<open>hnorm (star_of x - u) * hnorm (star_of y - v) * (star_of K) \<in> Infinitesimal\<close>
      by (simp add: Infinitesimal_approx_minus Infinitesimal_hnorm_iff Infinitesimal_mult Infinitesimal_star_of_mult assms(2) assms(3))
    ultimately show ?thesis
      using hnorm_le_Infinitesimal mem_infmal_iff by blast 
  qed
  moreover have \<open>( *f2* B) (star_of x) v - ( *f2* B) u v \<approx> 0\<close>
  proof-
    have \<open>( *f2* B) (star_of x) v - ( *f2* B) u v
        = ( *f2* B) (star_of x - u) v\<close>
    proof-
      have \<open>\<forall> p q. B x q - B p q = B (x - p) q\<close>
        by (metis (mono_tags, lifting) assms(1) bounded_sesquilinear.add_left eq_diff_eq)
      hence \<open>\<forall> p q. ( *f2* B) (star_of x) q - ( *f2* B) p q = ( *f2* B) (star_of x - p) q\<close>
        by StarDef.transfer
      thus ?thesis by blast
    qed
    moreover have \<open>( *f2* B) (star_of x - u) v \<approx> 0\<close>
    proof-
      have \<open>\<exists> K. \<forall> p q. norm (B (x - p) q) \<le> norm (x - p) * norm q * K\<close>
        using assms(1) bounded_sesquilinear.bounded by blast
      then obtain K where \<open>\<forall> p q. norm (B (x - p) q) \<le> norm (x - p) * norm q * K\<close>
        by blast
      from  \<open>\<forall> p q. norm (B (x - p) q) \<le> norm (x - p) * norm q * K\<close>
      have  \<open>\<forall> p q. hnorm (( *f2* B) (star_of x - p) q)
           \<le> hnorm (star_of x - p) * hnorm q * (star_of K)\<close>
        by StarDef.transfer
      hence \<open>hnorm (( *f2* B) (star_of x - u) v)
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
  moreover have \<open>(( *f2* B) u (star_of y) - ( *f2* B) u v) \<approx> 0\<close>
  proof-
    have \<open>\<exists> K. \<forall> p q. norm (B p (y - q)) \<le> norm p * norm (y - q) * K\<close>
      using assms(1) bounded_sesquilinear.bounded by blast
    then obtain K where \<open>\<forall> p q. norm (B p (y - q)) \<le> norm p * norm (y - q) * K\<close>
      by blast
    from  \<open>\<forall> p q. norm (B p (y - q)) \<le> norm p * norm (y - q) * K\<close>
    have  \<open>\<forall> p q. hnorm (( *f2* B) p (star_of y - q))
           \<le> hnorm p * hnorm (star_of y - q) * (star_of K)\<close>
      by StarDef.transfer
    hence \<open>hnorm (( *f2* B) u (star_of y - v))
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
    ultimately have \<open>( *f2* B) u (star_of y - v) \<in> Infinitesimal\<close>
      using hnorm_le_Infinitesimal   
      by blast
    moreover have \<open>( *f2* B) u (star_of y) - ( *f2* B) u v
        = ( *f2* B) u (star_of y - v)\<close>
    proof-
      have \<open>\<forall> p q. B p y - B p q = B p (y - q)\<close>
        by (metis (mono_tags, lifting) assms(1) bounded_sesquilinear.add_right eq_diff_eq)
      hence \<open>\<forall> p q. ( *f2* B) p (star_of y) - ( *f2* B) p q = ( *f2* B) p (star_of y - q)\<close>
        by StarDef.transfer
      thus ?thesis by blast
    qed
    ultimately show ?thesis
      by (simp add: mem_infmal_iff) 
  qed
  ultimately show \<open>( *f2* B) (star_of x) (star_of y) \<approx> ( *f2* B) u v\<close>
  proof -
    have f1: "monad (( *f2* B) (star_of x) (star_of y)) = monad (( *f2* B) (star_of x - u) (star_of y - v) + (( *f2* B) (star_of x) v - ( *f2* B) u v) + (( *f2* B) u (star_of y) - ( *f2* B) u v) + ( *f2* B) u v)"
      by (meson \<open>\<And>q p. ( *f2* B) (star_of x) (star_of y) \<approx> ( *f2* B) (star_of x - p) (star_of y - q) + (( *f2* B) (star_of x) q - ( *f2* B) p q) + (( *f2* B) p (star_of y) - ( *f2* B) p q) + ( *f2* B) p q\<close> approx_monad_iff)
    have "(0::'c star) \<in> monad 0"
      by (meson Infinitesimal_monad_zero_iff Infinitesimal_zero)
    hence "monad (( *f2* B) u v + (( *f2* B) u (star_of y) - ( *f2* B) u v + (( *f2* B) (star_of x - u) (star_of y - v) + (( *f2* B) (star_of x) v - ( *f2* B) u v)))) = monad (( *f2* B) u v)"
      by (meson Infinitesimal_add Infinitesimal_monad_eq Infinitesimal_monad_zero_iff \<open>( *f2* B) (star_of x - u) (star_of y - v) \<approx> 0\<close> \<open>( *f2* B) (star_of x) v - ( *f2* B) u v \<approx> 0\<close> \<open>( *f2* B) u (star_of y) - ( *f2* B) u v \<approx> 0\<close> approx_mem_monad_zero approx_sym)
    thus ?thesis
      using f1 by (simp add: approx_monad_iff ordered_field_class.sign_simps(2))
  qed
qed *)


(* lemma sesquilinear_superposition:
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
        using a2 d1 that complex_vector.linear_eq_0_on_span by blast
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
  hence b2: "csubspace {a. \<forall>p\<in>S_left. B p y = a}" 
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
qed *)


definition closed_sum:: \<open>'a::{semigroup_add,topological_space} set \<Rightarrow> 'a set \<Rightarrow> 'a set\<close> where
  \<open>closed_sum A B = closure (A + B)\<close>

notation closed_sum (infixl "+\<^sub>M" 65)

lemma closed_sum_comm: \<open>A +\<^sub>M B = B +\<^sub>M A\<close> for A B :: "_::ab_semigroup_add"
  by (simp add: add.commute closed_sum_def)

lemma closed_sum_left_subset: \<open>0 \<in> B \<Longrightarrow> A \<subseteq> A +\<^sub>M B\<close> for A B :: "_::monoid_add"
  by (metis add.right_neutral closed_sum_def closure_subset in_mono set_plus_intro subsetI)

lemma closed_sum_right_subset: \<open>0 \<in> A \<Longrightarrow> B \<subseteq> A +\<^sub>M B\<close> for A B :: "_::monoid_add"
  by (metis add.left_neutral closed_sum_def closure_subset set_plus_intro subset_iff)

lemma closed_sum_is_sup:
  fixes A B C:: \<open>('a::{complex_vector,topological_space}) set\<close>
  assumes \<open>closed_csubspace C\<close>
  assumes \<open>A \<subseteq> C\<close> and \<open>B \<subseteq> C\<close>
  shows \<open>(A +\<^sub>M B) \<subseteq> C\<close>
proof -
  have \<open>A + B \<subseteq> C\<close>
    using assms unfolding set_plus_def
    using closed_csubspace.subspace complex_vector.subspace_add by blast
  then show \<open>(A +\<^sub>M B) \<subseteq> C\<close>
    unfolding closed_sum_def
    using \<open>closed_csubspace C\<close>
    by (simp add: closed_csubspace.closed closure_minimal)
qed

lemma closed_subspace_closed_sum:
  fixes A B::"('a::complex_normed_vector) set"
  assumes a1: \<open>csubspace A\<close> and a2: \<open>csubspace B\<close>
  shows \<open>closed_csubspace (A +\<^sub>M B)\<close>
  using a1 a2 closed_sum_def 
  by (metis closure_is_closed_csubspace csubspace_set_plus)


lemma closed_sum_assoc:
  fixes A B C::"'a::real_normed_vector set"
  shows \<open>A +\<^sub>M (B +\<^sub>M C) = (A +\<^sub>M B) +\<^sub>M C\<close>
proof -
  have \<open>A + closure B \<subseteq> closure (A + B)\<close> for A B :: "'a set"
    by (meson closure_subset closure_sum dual_order.trans order_refl set_plus_mono2)
  then have \<open>A +\<^sub>M (B +\<^sub>M C) = closure (A + (B + C))\<close>
    unfolding closed_sum_def
    by (meson antisym_conv closed_closure closure_minimal closure_mono closure_subset equalityD1 set_plus_mono2)
  moreover 
  have \<open>closure A + B \<subseteq> closure (A + B)\<close> for A B :: "'a set"
    by (meson closure_subset closure_sum dual_order.trans order_refl set_plus_mono2)
  then have \<open>(A +\<^sub>M B) +\<^sub>M C = closure ((A + B) + C)\<close>
    unfolding closed_sum_def
    by (meson closed_closure closure_minimal closure_mono closure_subset eq_iff set_plus_mono2)
  ultimately show ?thesis
    by (simp add: ab_semigroup_add_class.add_ac(1))
qed


lemma closed_sum_zero_left:
  fixes A :: \<open>('a::{monoid_add, topological_space}) set\<close>
  assumes \<open>closed A\<close>
  shows \<open>{0} +\<^sub>M A = A\<close>
  unfolding closed_sum_def
  by (metis add.left_neutral assms closure_eq set_zero)

lemma closed_sum_zero_right:
  fixes A :: \<open>('a::{monoid_add, topological_space}) set\<close>
  assumes \<open>closed A\<close>
  shows \<open>A +\<^sub>M {0} = A\<close>
  unfolding closed_sum_def
  by (metis add.right_neutral assms closure_eq set_zero)


lemma closed_sum_mono_left:
  assumes \<open>A \<subseteq> B\<close>
  shows \<open>A +\<^sub>M C \<subseteq> B +\<^sub>M C\<close>
  by (simp add: assms closed_sum_def closure_mono set_plus_mono2)

lemma closed_sum_mono_right:
  assumes \<open>A \<subseteq> B\<close>
  shows \<open>C +\<^sub>M A \<subseteq> C +\<^sub>M B\<close>
  by (simp add: assms closed_sum_def closure_mono set_plus_mono2)

instantiation ccsubspace :: (complex_normed_vector) sup begin
lift_definition sup_ccsubspace :: "'a ccsubspace \<Rightarrow> 'a ccsubspace \<Rightarrow> 'a ccsubspace" 
  is "\<lambda>A B::'a set. A +\<^sub>M B"
  by (simp add: closed_subspace_closed_sum) 
instance .. 
end

lemma closed_sum_cspan:
  \<open>closure (cspan A) +\<^sub>M closure (cspan B) = closure (cspan (A \<union> B))\<close> for A B :: \<open>'a::complex_normed_vector set\<close>
proof auto
  have p0: "cspan (A \<union> B) = 
      cspan A + cspan B"
    for A B::"'a set"
    using complex_vector.span_Un
    by (smt Collect_cong set_plus_def)
  hence p1: "closure (cspan (A \<union> B)) = 
             closure (cspan A + cspan B)"
    for A B::"'a set"
    by simp

  show "x \<in> closure (cspan (A \<union> B))"
    if "x \<in> closure (cspan A) +\<^sub>M
            closure (cspan B)"
    for x::'a and A B
  proof-
    have "closure (cspan A) + closure (cspan B) \<subseteq>
          closure (cspan A + cspan B)"
      using Starlike.closure_sum by auto
    hence "closure (cspan A) + closure (cspan B)
        \<subseteq> closure (cspan (A \<union> B))"
      by (metis \<open>closure (cspan A) + closure (cspan B)
           \<subseteq> closure (cspan A + cspan B)\<close> p1)
    thus ?thesis by (smt closed_sum_def closure_closure closure_mono subsetD that)
  qed

  show "x \<in> closure (cspan A) +\<^sub>M
            closure (cspan B)"
    if "x \<in> closure (cspan (A \<union> B))"
    for x::'a and A B
  proof-
    have "cspan (A \<union> B) \<subseteq>
           closure (cspan A) +
           closure (cspan B)"
      apply auto
      by (metis closure_subset p0 set_plus_mono2_b) 
    hence "closure (cspan (A \<union> B)) \<subseteq>
           closure (closure (cspan A) +
                    closure (cspan B))"
      by (smt closure_mono)
    thus ?thesis by (smt closed_sum_def in_mono that)
  qed
qed

lemma ccspan_union: "ccspan A \<squnion> ccspan B = ccspan (A \<union> B)"
  apply  transfer by (rule closed_sum_cspan)

instantiation ccsubspace :: (complex_normed_vector) "Sup"
begin
lift_definition Sup_ccsubspace::\<open>'a ccsubspace set \<Rightarrow> 'a ccsubspace\<close>
  is \<open>\<lambda>S. closure (complex_vector.span (Union S))\<close>
proof
  show "csubspace (closure (complex_vector.span (\<Union> S::'a set)))"
    if "\<And>x::'a set. x \<in> S \<Longrightarrow> closed_csubspace x"
    for S :: "'a set set"
    using that
    by (simp add: closure_is_closed_csubspace) 
  show "closed (closure (complex_vector.span (\<Union> S::'a set)))"
    if "\<And>x. (x::'a set) \<in> S \<Longrightarrow> closed_csubspace x"
    for S :: "'a set set"
    using that
    by simp 
qed

instance..
end


instantiation ccsubspace :: ("{complex_vector,topological_space}") inf begin 
lift_definition inf_ccsubspace :: "'a ccsubspace \<Rightarrow> 'a ccsubspace \<Rightarrow> 'a ccsubspace" 
  is "(\<inter>)" by simp
instance .. end

lemma space_as_set_inf[simp]: "space_as_set (A \<sqinter> B) = space_as_set A \<inter> space_as_set B"
  by (rule inf_ccsubspace.rep_eq)

instantiation ccsubspace :: ("{complex_vector,topological_space}") order_top begin
instance 
proof
  show "a \<le> \<top>"
    for a :: "'a ccsubspace"
    apply transfer
    by simp
qed
end


instantiation ccsubspace :: ("{complex_vector,t1_space}") order_bot begin
instance 
proof
  show "(\<bottom>::'a ccsubspace) \<le> a"
    for a :: "'a ccsubspace"
    apply transfer
    apply auto
    using closed_csubspace.subspace complex_vector.subspace_0 by blast
qed
end

instantiation ccsubspace :: ("{complex_vector,topological_space}") semilattice_inf begin
instance 
proof
  show "x \<sqinter> y \<le> x"
    for x :: "'a ccsubspace"
      and y :: "'a ccsubspace"
    apply transfer
    by simp

  show "x \<sqinter> y \<le> y"
    for x :: "'a ccsubspace"
      and y :: "'a ccsubspace"
    apply transfer
    by simp

  show "x \<le> y \<sqinter> z"
    if "x \<le> y"
      and "x \<le> z"
    for x :: "'a ccsubspace"
      and y :: "'a ccsubspace"
      and z :: "'a ccsubspace"
    using that 
    apply transfer
    by simp
qed  
end


instance ccsubspace :: ("{complex_normed_vector}") semilattice_sup
proof
  fix x y z :: \<open>'a ccsubspace\<close>
  show \<open>x \<le> sup x y\<close>
    apply transfer
    by (simp add: closed_csubspace_def closed_sum_left_subset complex_vector.subspace_0)

  show "y \<le> sup x y"
    apply transfer
    by (simp add: closed_csubspace_def closed_sum_right_subset complex_vector.subspace_0)

  show "sup x y \<le> z" if "x \<le> z" and "y \<le> z"
    using that apply transfer
    apply (rule closed_sum_is_sup) by auto
qed

instance ccsubspace :: ("{complex_normed_vector}") complete_lattice
proof
  show "Inf A \<le> x"
    if "x \<in> A"
    for x :: "'a ccsubspace"
      and A :: "'a ccsubspace set"
    using that 
    apply transfer
    by auto

  have b1: "z \<subseteq> \<Inter> A"
    if "Ball A closed_csubspace" and
      "closed_csubspace z" and
      "(\<And>x. closed_csubspace x \<Longrightarrow> x \<in> A \<Longrightarrow> z \<subseteq> x)"
    for z::"'a set" and A
    using that
    by auto 
  show "z \<le> Inf A"
    if "\<And>x::'a ccsubspace. x \<in> A \<Longrightarrow> z \<le> x"
    for A :: "'a ccsubspace set"
      and z :: "'a ccsubspace"
    using that 
    apply transfer
    using b1 by blast

  show "x \<le> Sup A"
    if "x \<in> A"
    for x :: "'a ccsubspace"
      and A :: "'a ccsubspace set"
    using that 
    apply transfer
    by (meson Union_upper closure_subset complex_vector.span_superset dual_order.trans)  

  show "Sup A \<le> z"
    if "\<And>x::'a ccsubspace. x \<in> A \<Longrightarrow> x \<le> z"
    for A :: "'a ccsubspace set"
      and z :: "'a ccsubspace"
    using that apply transfer
  proof -
    fix A :: "'a set set" and z :: "'a set"
    assume A_closed: "Ball A closed_csubspace"
    assume "closed_csubspace z"
    assume in_z: "\<And>x. closed_csubspace x \<Longrightarrow> x \<in> A \<Longrightarrow> x \<subseteq> z"
    from A_closed in_z
    have \<open>V \<subseteq> z\<close> if \<open>V \<in> A\<close> for V
      by (simp add: that)
    then have \<open>\<Union> A \<subseteq> z\<close>
      by (simp add: Sup_le_iff)
    with \<open>closed_csubspace z\<close>
    show "closure (cspan (\<Union> A)) \<subseteq> z"
      by (simp add: closed_csubspace_def closure_minimal complex_vector.span_def subset_hull)
  qed

  show "Inf {} = (top::'a ccsubspace)"
    using \<open>\<And>z A. (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A\<close> top.extremum_uniqueI by auto

  show "Sup {} = (bot::'a ccsubspace)"
    using \<open>\<And>z A. (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z\<close> bot.extremum_uniqueI by auto 
qed

lemma finite_span_complete_aux:
  fixes b :: "'b::real_normed_vector" and B :: "'b set"
    and  rep :: "'basis::finite \<Rightarrow> 'b" and abs :: "'b \<Rightarrow> 'basis"
  assumes t: "type_definition rep abs B"
    and t1: "finite B" and t2: "b\<in>B" and t3: "independent B"
  shows "\<exists>D>0. \<forall>\<psi>. norm (representation B \<psi> b) \<le> norm \<psi> * D"
    and "complete (span B)"

  text \<open>This auxiliary lemma shows more or less the same as \<open>finite_span_representation_bounded\<close>,
     \<open>finite_span_complete\<close> below (see there for an intuition about the mathematical 
     content of the lemmas). However, there is one difference: Here we additionally assume here
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
    (\<Sum>b\<in>B. x b *\<^sub>R b)" for x
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
  have sphere: "compact (sphere 0 d :: 'basis euclidean_space set)" for d
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
      unfolding span_finite[OF \<open>finite B\<close>] comb_def
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

lemma finite_span_complete[simp]:
  fixes A :: "'a::real_normed_vector set"
  assumes "finite A"
  shows "complete (span A)"
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
  shows "\<exists>D>0. \<forall>\<psi> b. abs (representation B \<psi> b) \<le> norm \<psi> * D"

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

lemma cspan_as_span:
  "cspan (B::'a::complex_vector set) = span (B \<union> scaleC \<i> ` B)"
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


lemma finite_cspan_complete[simp]: 
  fixes B :: "'a::complex_normed_vector set"
  assumes "finite B"
  shows "complete (cspan B)"
  by (simp add: assms cspan_as_span)


lemma finite_span_closed[simp]:
  fixes B :: "'a::real_normed_vector set"
  assumes "finite B"
  shows "closed (real_vector.span B)"
  by (simp add: assms complete_imp_closed)


lemma finite_cspan_closed[simp]:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes a1: \<open>finite S\<close>
  shows \<open>closed (cspan S)\<close>  
  by (simp add: assms complete_imp_closed)

lemma closure_finite_cspan:
  fixes T::\<open>'a::complex_normed_vector set\<close>
  assumes \<open>finite T\<close>
  shows \<open>closure (cspan T)  = cspan T\<close>
  by (simp add: assms)

lemma finite_cspan_closed_csubspace:
  assumes "finite (S::'a::complex_normed_vector set)"
  shows "closed_csubspace (cspan S)"
  by (simp add: assms closed_csubspace.intro)

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


lemma antilinear_to_conjugate_space[simp]: \<open>antilinear to_conjugate_space\<close>
  by (rule antilinearI; transfer, auto)

lemma antilinear_from_conjugate_space[simp]: \<open>antilinear from_conjugate_space\<close>
  by (rule antilinearI; transfer, auto)

lemma cspan_to_conjugate_space[simp]: "cspan (to_conjugate_space ` X) = to_conjugate_space ` cspan X"
  unfolding complex_vector.span_def complex_vector.subspace_def hull_def
  apply transfer
  apply simp
  by (metis (no_types, hide_lams) complex_cnj_cnj)

lemma surj_to_conjugate_space[simp]: "surj to_conjugate_space"
  by (meson surj_def to_conjugate_space_cases)

lemmas has_derivative_scaleC[simp, derivative_intros] =
  bounded_bilinear.FDERIV[OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]

instantiation complex :: basis_enum begin
definition "canonical_basis = [1::complex]"
instance
proof
  show "distinct (canonical_basis::complex list)"
    by (simp add: canonical_basis_complex_def)    
  show "cindependent (set (canonical_basis::complex list))"
    unfolding canonical_basis_complex_def
    by auto
  show "cspan (set (canonical_basis::complex list)) = UNIV"
    unfolding canonical_basis_complex_def 
    apply (auto simp add: cspan_raw_def vector_space_over_itself.span_Basis)
    by (metis complex_scaleC_def complex_vector.span_base complex_vector.span_scale cspan_raw_def insertI1 mult.right_neutral)
qed
end

instantiation ccsubspace :: ("{complex_vector,t1_space}") zero begin
definition zero_ccsubspace :: "'a ccsubspace" where [simp]: "zero_ccsubspace = bot"
lemma zero_ccsubspace_transfer[transfer_rule]: \<open>pcr_ccsubspace (=) {0} 0\<close>
  unfolding zero_ccsubspace_def by transfer_prover
instance ..
end

lemma csubspace_is_convex[simp]:
  assumes a1: "csubspace M"
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

lemma kernel_is_csubspace[simp]:
  assumes a1: "clinear f"
  shows "csubspace  (f -` {0})"
proof-
  have w3: \<open>t *\<^sub>C x \<in> {x. f x = 0}\<close> 
    if b1: "x \<in> {x. f x = 0}"
    for x t
    by (metis assms complex_vector.linear_subspace_kernel complex_vector.subspace_def that)
  have \<open>f 0 = 0\<close>
    by (simp add: assms complex_vector.linear_0)
  hence s2: \<open>0 \<in> {x. f x = 0}\<close>
    by blast

  have w4: "x + y \<in> {x. f x = 0}"
    if c1: "x \<in> {x. f x = 0}" and c2: "y \<in> {x. f x = 0}"
    for x y
    using assms c1 c2 complex_vector.linear_add by fastforce
  have s4: \<open>c *\<^sub>C t \<in> {x. f x = 0}\<close> 
    if "t \<in> {x. f x = 0}"
    for t c
    using that w3 by auto
  have s5: "u + v \<in> {x. f x = 0}"
    if "u \<in> {x. f x = 0}" and "v \<in> {x. f x = 0}"
    for u v
    using w4 that(1) that(2) by auto    
  have f3: "f -` {b. b = 0 \<or> b \<in> {}} = {a. f a = 0}"
    by blast
  have "csubspace {a. f a = 0}"
    by (metis complex_vector.subspace_def s2 s4 s5)
  thus ?thesis
    using f3 by auto
qed


lemma kernel_is_closed_csubspace[simp]:
  assumes a1: "bounded_clinear f"
  shows "closed_csubspace (f -` {0})"
proof-
  have \<open>csubspace (f -` {0})\<close>
    using assms bounded_clinear.clinear complex_vector.linear_subspace_vimage complex_vector.subspace_single_0 by blast
  have "L \<in> {x. f x = 0}"
    if "r \<longlonglongrightarrow> L" and "\<forall> n. r n \<in> {x. f x = 0}"
    for r and  L 
  proof-
    have d1: \<open>\<forall> n. f (r n) = 0\<close>
      using that(2) by auto
    have \<open>(\<lambda> n. f (r n)) \<longlonglongrightarrow> f L\<close>
      using assms clinear_continuous_at continuous_within_tendsto_compose' that(1) 
      by fastforce
    hence \<open>(\<lambda> n. 0) \<longlonglongrightarrow> f L\<close>
      using d1 by simp        
    hence \<open>f L = 0\<close>
      using limI by fastforce
    thus ?thesis by blast
  qed
  then have s3: \<open>closed (f -` {0})\<close>
    using closed_sequential_limits by force
  with \<open>csubspace (f -` {0})\<close>
  show ?thesis
    using closed_csubspace.intro by blast
qed

lemma range_is_clinear[simp]:
  assumes a1: "clinear f"
  shows "csubspace (range f)"
  using assms complex_vector.linear_subspace_image complex_vector.subspace_UNIV by blast

lemma ccspan_superset:
  \<open>A \<subseteq> space_as_set (ccspan A)\<close> 
  for A :: \<open>'a::complex_normed_vector set\<close>
  apply transfer
  by (meson closure_subset complex_vector.span_superset subset_trans)


subsection \<open>Product is a Complex Vector Space\<close>

(* Follows closely Product_Vector.thy *)

instantiation prod :: (complex_vector, complex_vector) complex_vector
begin

definition scaleC_prod_def:
  "scaleC r A = (scaleC r (fst A), scaleC r (snd A))"

lemma fst_scaleC [simp]: "fst (scaleC r A) = scaleC r (fst A)"
  unfolding scaleC_prod_def by simp

lemma snd_scaleC [simp]: "snd (scaleC r A) = scaleC r (snd A)"
  unfolding scaleC_prod_def by simp

proposition scaleC_Pair [simp]: "scaleC r (a, b) = (scaleC r a, scaleC r b)"
  unfolding scaleC_prod_def by simp

instance
proof
  fix a b :: complex and x y :: "'a \<times> 'b"
  show "scaleC a (x + y) = scaleC a x + scaleC a y"
    by (simp add: scaleC_add_right scaleC_prod_def)
  show "scaleC (a + b) x = scaleC a x + scaleC b x"
    by (simp add: Complex_Vector_Spaces.scaleC_prod_def scaleC_left.add)
  show "scaleC a (scaleC b x) = scaleC (a * b) x"
    by (simp add: prod_eq_iff)
  show "scaleC 1 x = x"
    by (simp add: prod_eq_iff)
  show \<open>(scaleR :: _ \<Rightarrow> _ \<Rightarrow> 'a*'b) r = (*\<^sub>C) (complex_of_real r)\<close> for r
    by (auto intro!: ext simp: scaleR_scaleC scaleC_prod_def scaleR_prod_def)
qed

end

lemma module_prod_scale_eq_scaleC: "module_prod.scale (*\<^sub>C) (*\<^sub>C) = scaleC"
  apply (rule ext) apply (rule ext)
  apply (subst module_prod.scale_def)
  subgoal by unfold_locales
  by (simp add: scaleC_prod_def)

interpretation complex_vector?: vector_space_prod "scaleC::_\<Rightarrow>_\<Rightarrow>'a::complex_vector" "scaleC::_\<Rightarrow>_\<Rightarrow>'b::complex_vector"
  rewrites "scale = ((*\<^sub>C)::_\<Rightarrow>_\<Rightarrow>('a \<times> 'b))"
    and "module.dependent (*\<^sub>C) = cdependent"
    and "module.representation (*\<^sub>C) = crepresentation"
    and "module.subspace (*\<^sub>C) = csubspace"
    and "module.span (*\<^sub>C) = cspan"
    and "vector_space.extend_basis (*\<^sub>C) = cextend_basis"
    and "vector_space.dim (*\<^sub>C) = cdim"
    and "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
  subgoal by unfold_locales
  subgoal by (fact module_prod_scale_eq_scaleC)
  unfolding cdependent_raw_def crepresentation_raw_def csubspace_raw_def cspan_raw_def
    cextend_basis_raw_def cdim_raw_def clinear_def
  by (rule refl)+


subsection \<open>Copying existing theorems into sublocales\<close>

context bounded_clinear begin
interpretation bounded_linear f by (rule bounded_linear)
lemmas continuous = continuous
lemmas uniform_limit = uniform_limit
end

context bounded_antilinear begin
interpretation bounded_linear f by (rule bounded_linear)
lemmas continuous = continuous
lemmas uniform_limit = uniform_limit
end




end

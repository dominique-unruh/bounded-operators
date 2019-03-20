(*  Title:      Bounded-Operators/Complex_L2.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

References:

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}

*)


theory Complex_L2
  imports "HOL-Analysis.L2_Norm" "HOL-Library.Rewrite" "HOL-Analysis.Infinite_Set_Sum"
    Complex_Inner_Product Infinite_Set_Sum_Missing Complex_Main
    Extended_Sorry
begin

section \<open>Preliminaries\<close>

hide_const (open) span

section \<open>l2 norm - untyped\<close>

definition "has_ell2_norm x = bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)"

lemma has_ell2_norm_infsetsum: "has_ell2_norm x \<longleftrightarrow> (\<lambda>i. (cmod (x i))\<^sup>2) abs_summable_on UNIV"
proof
  define f where "f i = (cmod (x i))\<^sup>2" for i
  assume fsums: "f abs_summable_on UNIV"
  define bound where "bound = infsetsum f UNIV"
  have "sum f F \<le> bound" if "finite F" for F
  proof -
    have "sum f F = infsetsum f F"
      using that by (rule infsetsum_finite[symmetric])
    also have "infsetsum f F \<le> infsetsum f UNIV"
      apply (rule infsetsum_mono_neutral_left)
      using fsums that f_def by auto
    finally show ?thesis 
      unfolding bound_def by assumption
  qed
  then show "has_ell2_norm x"
    unfolding has_ell2_norm_def f_def
    by (rule bdd_aboveI2[where M=bound], simp)
next
  assume "has_ell2_norm x"
  then obtain B where "(\<Sum>xa\<in>F. norm ((cmod (x xa))\<^sup>2)) < B" if "finite F" for F
    apply atomize_elim unfolding has_ell2_norm_def unfolding bdd_above_def apply auto
    by (meson gt_ex le_less_trans)
  then show "(\<lambda>i. (cmod (x i))\<^sup>2) abs_summable_on UNIV"
    apply (rule_tac abs_summable_finiteI[where B=B]) by fastforce 
qed

lemma has_ell2_norm_L2_set: "has_ell2_norm x = bdd_above (L2_set (norm o x) ` Collect finite)"
proof -
  have bdd_above_image_mono': "(\<And>x y. x\<le>y \<Longrightarrow> x:A \<Longrightarrow> y:A \<Longrightarrow> f x \<le> f y) \<Longrightarrow> (\<exists>M\<in>A. \<forall>x \<in> A. x \<le> M) \<Longrightarrow> bdd_above (f`A)" for f::"'a set\<Rightarrow>real" and A
    unfolding bdd_above_def by auto

  have "bdd_above X \<Longrightarrow> bdd_above (sqrt ` X)" for X
    by (meson bdd_aboveI2 bdd_above_def real_sqrt_le_iff)
  moreover have "bdd_above X" if bdd_sqrt: "bdd_above (sqrt ` X)" for X
  proof -
    obtain y where y:"y \<ge> sqrt x" if "x:X" for x 
      using bdd_sqrt unfolding bdd_above_def by auto
    have "y*y \<ge> x" if "x:X" for x
      by (metis power2_eq_square sqrt_le_D that y)
    then show "bdd_above X"
      unfolding bdd_above_def by auto
  qed
  ultimately have bdd_sqrt: "bdd_above X \<longleftrightarrow> bdd_above (sqrt ` X)" for X
    by rule

  show "has_ell2_norm x \<longleftrightarrow> bdd_above (L2_set (norm o x) ` Collect finite)"
    unfolding has_ell2_norm_def unfolding L2_set_def
    apply (rewrite asm_rl[of "(\<lambda>A. sqrt (sum (\<lambda>i. ((cmod \<circ> x) i)\<^sup>2) A)) ` Collect finite 
                            = sqrt ` (\<lambda>A. (\<Sum>i\<in>A. (cmod (x i))\<^sup>2)) ` Collect finite"])
     apply auto[1]
    apply (subst bdd_sqrt[symmetric])
    by (simp add: monoI)
qed

section \<open>Subspaces\<close>

notation
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) 


(* TODO: rename *)
typedef 'a vector = "{x::'a\<Rightarrow>complex. has_ell2_norm x}"
  unfolding has_ell2_norm_def by (rule exI[of _ "\<lambda>_.0"], auto)
setup_lifting type_definition_vector
  (* derive universe vector *)

lemma SUP_max:
  fixes f::"'a::order\<Rightarrow>'b::conditionally_complete_lattice"
  assumes "mono f"
  assumes "\<And>x. x:M \<Longrightarrow> x\<le>m"
  assumes "m:M"
  shows "(SUP x:M. f x) = f m"
  apply (rule antisym)
   apply (metis assms(1) assms(2) assms(3) cSUP_least empty_iff monoD)
  by (metis assms(1) assms(2) assms(3) bdd_aboveI bdd_above_image_mono cSUP_upper)


definition "ell2_norm x = sqrt (SUP F:{F. finite F}. sum (\<lambda>i. (norm(x i))^2) F)"

lemma ell2_norm_L2_set: 
  assumes "has_ell2_norm x"
  shows "ell2_norm x = (SUP F:{F. finite F}. L2_set (norm o x) F)"
  unfolding ell2_norm_def L2_set_def o_def apply (subst continuous_at_Sup_mono)
  using monoI real_sqrt_le_mono apply blast
  using continuous_at_split isCont_real_sqrt apply blast
  using assms unfolding has_ell2_norm_def by auto

lemma ell2_norm_infsetsum:
  assumes "has_ell2_norm x"
  shows "ell2_norm x = sqrt (infsetsum (\<lambda>i. (norm(x i))^2) UNIV)"
  unfolding ell2_norm_def apply (subst infsetsum_nonneg_is_SUPREMUM)
  using assms has_ell2_norm_infsetsum by auto

lemma has_ell2_norm_finite[simp]: "has_ell2_norm (x::'a::finite\<Rightarrow>_)"
  unfolding has_ell2_norm_def by simp

lemma ell2_norm_finite_def: "ell2_norm (x::'a::finite\<Rightarrow>complex) = sqrt (sum (\<lambda>i. (norm(x i))^2) UNIV)"
proof -
  have mono: "mono (sum (\<lambda>i. (cmod (x i))\<^sup>2))"
    unfolding mono_def apply auto apply (subst sum_mono2) by auto
  show ?thesis
    unfolding ell2_norm_def apply (subst SUP_max[where m=UNIV])
    using mono by auto
qed

lemma L2_set_mono2:
  assumes "finite L"
  assumes "K \<le> L"
  shows "L2_set f K \<le> L2_set f L"
  unfolding L2_set_def apply (rule real_sqrt_le_mono)
  apply (rule sum_mono2)
  using assms by auto

lemma ell2_norm_finite_def': "ell2_norm (x::'a::finite\<Rightarrow>complex) = L2_set (norm o x) UNIV"
  apply (subst ell2_norm_L2_set) apply simp
  apply (subst SUP_max[where m=UNIV])
  by (auto simp: mono_def intro!: L2_set_mono2)

lemma ell2_1: assumes  "finite F" shows "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) \<le> 1"
proof - 
  have "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 0" if "a\<notin>F"
    apply (subst sum.cong[where B=F and h="\<lambda>_. 0"]) using that by auto
  moreover have "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 1" if "a\<in>F"
  proof -
    obtain F0 where "a\<notin>F0" and F_F0: "F=insert a F0"
      by (meson \<open>a \<in> F\<close> mk_disjoint_insert) 
    show "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 1"
      unfolding F_F0
      apply (subst sum.insert_remove)
      using F_F0 assms apply auto
      apply (subst sum.cong[where B=F0 and h="\<lambda>_. 0"])
        apply (simp add: \<open>a \<notin> F0\<close>)
      using \<open>a \<notin> F0\<close> apply auto[1]
      by simp
  qed
  ultimately show "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) \<le> 1"
    by linarith
qed


lemma cSUP_leD: "bdd_above (f`A) \<Longrightarrow> (SUP i:A. f i) \<le> y \<Longrightarrow> i \<in> A \<Longrightarrow> f i \<le> y" for y :: "'a::conditionally_complete_lattice"
  by (meson cSUP_upper order_trans)

lemma ell2_norm_0:
  assumes "has_ell2_norm x"
  shows "(ell2_norm x = 0) = (x = (\<lambda>_. 0))"
proof
  assume "x = (\<lambda>_. 0)"
  then show "ell2_norm x = 0"
    unfolding ell2_norm_def apply auto
    by (metis cSUP_const empty_Collect_eq finite.emptyI)
next
  assume norm0: "ell2_norm x = 0"
  show "x = (\<lambda>_. 0)"
  proof
    fix i
    have "sum (\<lambda>i. (cmod (x i))\<^sup>2) {i} \<le> 0" 
      apply (rule cSUP_leD[where A="Collect finite"])
      using norm0 assms unfolding has_ell2_norm_def ell2_norm_def by auto
    then show "x i = 0" by auto
  qed
qed

lemma ell2_norm_smult:
  assumes "has_ell2_norm x"
  shows "has_ell2_norm (\<lambda>i. c * x i)" and "ell2_norm (\<lambda>i. c * x i) = cmod c * ell2_norm x"
proof -
  have L2_set_mul: "L2_set (cmod \<circ> (\<lambda>i. c * x i)) F = cmod c * L2_set (cmod \<circ> x) F" for F
  proof -
    have "L2_set (cmod \<circ> (\<lambda>i. c * x i)) F = L2_set (\<lambda>i. (cmod c * (cmod o x) i)) F"
      by (metis comp_def norm_mult)
    also have "\<dots> = cmod c * L2_set (cmod o x) F"
      by (metis norm_ge_zero L2_set_right_distrib)
    finally show ?thesis .
  qed

  from assms obtain M where M: "M \<ge> L2_set (cmod o x) F" if "finite F" for F
    unfolding has_ell2_norm_L2_set bdd_above_def by auto
  then have "cmod c * M \<ge> L2_set (cmod o (\<lambda>i. c * x i)) F" if "finite F" for F
    unfolding L2_set_mul
    by (simp add: ordered_comm_semiring_class.comm_mult_left_mono that) 
  then show has: "has_ell2_norm (\<lambda>i. c * x i)"
    unfolding has_ell2_norm_L2_set bdd_above_def using L2_set_mul[symmetric] by auto

  have "ell2_norm (\<lambda>i. c * x i) = SUPREMUM (Collect finite) (L2_set (cmod \<circ> (\<lambda>i. c * x i)))"
    apply (rule ell2_norm_L2_set) by (rule has)
  also have "\<dots> = SUPREMUM (Collect finite) (\<lambda>F. cmod c * L2_set (cmod \<circ> x) F)"
    apply (rule SUP_cong) apply auto by (rule L2_set_mul)
  also have "\<dots> = cmod c * ell2_norm x" 
    apply (subst ell2_norm_L2_set) apply (fact assms)
    apply (subst continuous_at_Sup_mono[where f="\<lambda>x. cmod c * x"])
        apply (simp add: mono_def ordered_comm_semiring_class.comm_mult_left_mono)
       apply (rule continuous_mult)
    using continuous_const apply blast
       apply simp
      apply blast
     apply (meson assms has_ell2_norm_L2_set)
    by auto
  finally show "ell2_norm (\<lambda>i. c * x i) = cmod c * ell2_norm x" .
qed


lemma ell2_norm_triangle:
  assumes "has_ell2_norm x" and "has_ell2_norm y"
  shows "has_ell2_norm (\<lambda>i. x i + y i)" and "ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
proof -
  have triangle: "L2_set (cmod \<circ> (\<lambda>i. x i + y i)) F \<le> L2_set (cmod \<circ> x) F + L2_set (cmod \<circ> y) F" (is "?lhs\<le>?rhs") 
    if "finite F" for F
  proof -
    have "?lhs \<le> L2_set (\<lambda>i. (cmod o x) i + (cmod o y) i) F"
      apply (rule L2_set_mono)
      by (auto simp: norm_triangle_ineq)
    also have "\<dots> \<le> ?rhs"
      by (rule L2_set_triangle_ineq)
    finally show ?thesis .
  qed

  obtain Mx My where Mx: "Mx \<ge> L2_set (cmod o x) F" and My: "My \<ge> L2_set (cmod o y) F" if "finite F" for F
    using assms unfolding has_ell2_norm_L2_set bdd_above_def by auto
  then have MxMy: "Mx + My \<ge> L2_set (cmod \<circ> x) F + L2_set (cmod \<circ> y) F" if "finite F" for F
    using that by fastforce
  then have bdd_plus: "bdd_above ((\<lambda>xa. L2_set (cmod \<circ> x) xa + L2_set (cmod \<circ> y) xa) ` Collect finite)"
    unfolding bdd_above_def by auto
  from MxMy have MxMy': "Mx + My \<ge> L2_set (cmod \<circ> (\<lambda>i. x i + y i)) F" if "finite F" for F 
    using triangle that by fastforce
  then show has: "has_ell2_norm (\<lambda>i. x i + y i)"
    unfolding has_ell2_norm_L2_set bdd_above_def by auto

  have SUP_plus: "(SUP x:A. f x + g x) \<le> (SUP x:A. f x) + (SUP x:A. g x)" 
    if notempty: "A\<noteq>{}" and bddf: "bdd_above (f`A)"and bddg: "bdd_above (g`A)"
    for f g :: "'a set \<Rightarrow> real" and A
  proof -
    have xleq: "x \<le> (SUP x:A. f x) + (SUP x:A. g x)" if x: "x \<in> (\<lambda>x. f x + g x) ` A" for x
    proof -
      obtain a where aA: "a:A" and ax: "x = f a + g a"
        using x by blast
      have fa: "f a \<le> (SUP x:A. f x)"
        by (simp add: bddf aA cSUP_upper)
      moreover have "g a \<le> (SUP x:A. g x)"
        by (simp add: bddg aA cSUP_upper)
      ultimately have "f a + g a \<le> (SUP x:A. f x) + (SUP x:A. g x)" by simp
      with ax show ?thesis by simp
    qed
    show ?thesis
      apply (rule cSup_least) using notempty xleq by auto
  qed

  show "ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
    apply (subst ell2_norm_L2_set, fact has)
    apply (subst ell2_norm_L2_set, fact assms)+
    apply (rule order.trans[rotated])
     apply (rule SUP_plus)
       apply auto[1]
      apply (meson assms(1) has_ell2_norm_L2_set)
     apply (meson assms(2) has_ell2_norm_L2_set)
    apply (rule cSUP_subset_mono)
       apply auto
    using MxMy unfolding bdd_above_def apply auto[1]
    using triangle by fastforce
qed



lift_definition ket :: "'a \<Rightarrow> 'a vector" is "\<lambda>x y. if x=y then 1 else 0"
  unfolding has_ell2_norm_def bdd_above_def apply simp
  apply (rule exI[of _ 1], rule allI, rule impI)
  by (rule ell2_1)

lemma cSUP_eq_maximum:
  fixes z :: "_::conditionally_complete_lattice"
  assumes "\<exists>x\<in>X. f x = z"
  assumes "\<And>x. x \<in> X \<Longrightarrow> f x \<le> z"
  shows "(SUP x:X. f x) = z"
  by (metis (mono_tags, hide_lams) assms(1) assms(2) cSup_eq_maximum imageE image_eqI)


instantiation vector :: (type)complex_vector begin
lift_definition zero_vector :: "'a vector" is "\<lambda>_.0" by (auto simp: has_ell2_norm_def)
lift_definition uminus_vector :: "'a vector \<Rightarrow> 'a vector" is uminus by (simp add: has_ell2_norm_def)
lift_definition plus_vector :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is "\<lambda>f g x. f x + g x"
  by (rule ell2_norm_triangle) 
lift_definition minus_vector :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is "\<lambda>f g x. f x - g x"
  apply (subst ab_group_add_class.ab_diff_conv_add_uminus)
  apply (rule ell2_norm_triangle) 
   apply auto by (simp add: has_ell2_norm_def)
lift_definition scaleR_vector :: "real \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is "\<lambda>r f x. complex_of_real r * f x"
  by (rule ell2_norm_smult)
lift_definition scaleC_vector :: "complex \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is "\<lambda>c f x. c * f x"
  by (rule ell2_norm_smult)

instance apply intro_classes
           apply (transfer; rule ext; simp)
           apply (transfer; rule ext; simp)
          apply (transfer; rule ext; simp)
         apply (transfer; rule ext; simp)
        apply (transfer; rule ext; simp)
       apply (transfer; rule ext; simp)
      apply (transfer; subst ab_group_add_class.ab_diff_conv_add_uminus; simp)
     apply (transfer; rule ext; simp add: distrib_left)
    apply (transfer; rule ext; simp add: distrib_right)
   apply (transfer; rule ext; simp)
  by (transfer; rule ext; simp)
end

instantiation vector :: (type)complex_normed_vector begin
lift_definition norm_vector :: "'a vector \<Rightarrow> real" is ell2_norm .
definition "dist x y = norm (x - y)" for x y::"'a vector"
definition "sgn x = x /\<^sub>R norm x" for x::"'a vector"
definition "uniformity = (INF e:{0<..}. principal {(x::'a vector, y). norm (x - y) < e})"
definition "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e:{0<..}. principal {(x, y). norm (x - y) < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "'a vector set"
instance apply intro_classes
  unfolding dist_vector_def sgn_vector_def uniformity_vector_def open_vector_def apply simp_all
     apply transfer apply (fact ell2_norm_0)
    apply transfer apply (fact ell2_norm_triangle)
   apply transfer apply (subst ell2_norm_smult) apply (simp_all add: abs_complex_def)[2]
  apply transfer by (simp add: ell2_norm_smult(2)) 
end


(* TODO: move *)
lemma cnj_x_x: "cnj x * x = (abs x)\<^sup>2"
  apply (cases x)
  by (auto simp: complex_cnj complex_mult abs_complex_def complex_norm power2_eq_square complex_of_real_def)

lemma cnj_x_x_geq0[simp]: "cnj x * x \<ge> 0"
  apply (cases x)
  by (auto simp: complex_cnj complex_mult complex_of_real_def less_eq_complex_def)


instantiation vector :: (type) complex_inner begin
lift_definition cinner_vector :: "'a vector \<Rightarrow> 'a vector \<Rightarrow> complex" is 
  "\<lambda>x y. infsetsum (\<lambda>i. (cnj (x i) * y i)) UNIV" .
instance
proof standard
  fix x y z :: "'a vector" fix c :: complex
  show "cinner x y = cnj (cinner y x)"
  proof transfer
    fix x y :: "'a\<Rightarrow>complex" assume "has_ell2_norm x" and "has_ell2_norm y"
    have "(\<Sum>\<^sub>ai. cnj (x i) * y i) = (\<Sum>\<^sub>ai. cnj (cnj (y i) * x i))"
      by (metis complex_cnj_cnj complex_cnj_mult mult.commute)
    also have "\<dots> = cnj (\<Sum>\<^sub>ai. cnj (y i) * x i)"
      by (metis infsetsum_cnj) 
    finally show "(\<Sum>\<^sub>ai. cnj (x i) * y i) = cnj (\<Sum>\<^sub>ai. cnj (y i) * x i)" .
  qed

  show "cinner (x + y) z = cinner x z + cinner y z"
  proof transfer
    fix x y z :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    then have cnj_x: "(\<lambda>i. cnj (x i) * cnj (x i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    assume "has_ell2_norm y"
    then have cnj_y: "(\<lambda>i. cnj (y i) * cnj (y i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    assume "has_ell2_norm z"
    then have z: "(\<lambda>i. z i * z i) abs_summable_on UNIV" 
      by (simp add: norm_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    have cnj_x_z:"(\<lambda>i. cnj (x i) * z i) abs_summable_on UNIV"
      using cnj_x z by (rule abs_summable_product) 
    have cnj_y_z:"(\<lambda>i. cnj (y i) * z i) abs_summable_on UNIV"
      using cnj_y z by (rule abs_summable_product) 

    show "(\<Sum>\<^sub>ai. cnj (x i + y i) * z i) = (\<Sum>\<^sub>ai. cnj (x i) * z i) + (\<Sum>\<^sub>ai. cnj (y i) * z i)"
      apply (subst infsetsum_add[symmetric])
        apply (fact cnj_x_z)
       apply (fact cnj_y_z)
      by (simp add: distrib_left mult.commute)
  qed

  show "cinner (c *\<^sub>C x) y = cnj c * cinner x y"
  proof transfer
    fix x y :: "'a \<Rightarrow> complex" and c :: complex
    assume "has_ell2_norm x"
    then have cnj_x: "(\<lambda>i. cnj (x i) * cnj (x i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    assume "has_ell2_norm y"
    then have y: "(\<lambda>i. y i * y i) abs_summable_on UNIV" 
      by (simp add: norm_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    have cnj_x_y:"(\<lambda>i. cnj (x i) * y i) abs_summable_on UNIV"
      using cnj_x y by (rule abs_summable_product) 
    then show "(\<Sum>\<^sub>ai. cnj (c * x i) * y i) = cnj c * (\<Sum>\<^sub>ai. cnj (x i) * y i)"
      apply (subst infsetsum_cmult_right[symmetric])
      by (auto simp: mult.commute mult.left_commute)
  qed

  show "0 \<le> cinner x x"
  proof transfer
    fix x :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    then have sum: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      unfolding has_ell2_norm_infsetsum power2_eq_square
      apply (subst abs_summable_on_norm_iff[symmetric])
      by (simp del: abs_summable_on_norm_iff add: norm_mult has_ell2_norm_infsetsum power2_eq_square)
    have "0 = (\<Sum>\<^sub>ai::'a. 0)" by auto
    also have "\<dots> \<le> (\<Sum>\<^sub>ai. cnj (x i) * x i)"
      apply (rule infsetsum_mono_complex)
      using sum by auto
    finally show "0 \<le> (\<Sum>\<^sub>ai. cnj (x i) * x i)" by assumption
  qed

  show "(cinner x x = 0) = (x = 0)"
  proof (transfer, auto)
    fix x :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    then have cmod_x2: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      unfolding has_ell2_norm_infsetsum power2_eq_square 
      apply (subst abs_summable_on_norm_iff[symmetric])
      by (simp del: abs_summable_on_norm_iff add: norm_mult)
    assume eq0: "(\<Sum>\<^sub>ai. cnj (x i) * x i) = 0"
    show "x = (\<lambda>_. 0)"
    proof (rule ccontr)
      assume "x \<noteq> (\<lambda>_. 0)"
      then obtain i where "x i \<noteq> 0" by auto
      then have "0 < cnj (x i) * x i"
        using le_less by fastforce
      also have "\<dots> = (\<Sum>\<^sub>ai\<in>{i}. cnj (x i) * x i)" by auto
      also have "\<dots> \<le> (\<Sum>\<^sub>ai. cnj (x i) * x i)"
        apply (rule infsetsum_subset_complex)
          apply (fact cmod_x2)
        by auto
      also from eq0 have "\<dots> = 0" by assumption
      finally show False by simp
    qed
  qed

  show "norm x = sqrt (cmod (cinner x x))"
  proof transfer 
    fix x :: "'a \<Rightarrow> complex" 
    assume x: "has_ell2_norm x"
    then have sum: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      unfolding has_ell2_norm_infsetsum power2_eq_square
      apply (subst abs_summable_on_norm_iff[symmetric])
      by (simp del: abs_summable_on_norm_iff add: norm_mult has_ell2_norm_infsetsum power2_eq_square)

    from x have "ell2_norm x = sqrt (\<Sum>\<^sub>ai. (cmod (x i))\<^sup>2)"
      apply (subst ell2_norm_infsetsum) by auto
    also have "\<dots> = sqrt (\<Sum>\<^sub>ai. cmod (cnj (x i) * x i))"
      unfolding norm_complex_def power2_eq_square by auto
    also have "\<dots> = sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i))"
      apply (subst infsetsum_cmod) using sum by auto
    finally show "ell2_norm x = sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i))" by assumption
  qed
qed
end

lemma norm_vector_component: "norm (Rep_vector x i) \<le> norm x"
proof transfer
  fix x :: "'a \<Rightarrow> complex" and i
  assume has: "has_ell2_norm x"
  have "cmod (x i) = L2_set (cmod \<circ> x) {i}" by auto
  also have "\<dots> \<le> ell2_norm x"
    apply (subst ell2_norm_L2_set, fact has)
    apply (rule cSUP_upper)
     apply simp
    using has unfolding has_ell2_norm_L2_set by simp
  finally show "cmod (x i) \<le> ell2_norm x" by assumption
qed

lemma Cauchy_vector_component: 
  fixes X
  defines "x i == Rep_vector (X i)"
  shows "Cauchy X \<Longrightarrow> Cauchy (\<lambda>i. x i j)"
proof -
  assume "Cauchy X"
  have "dist (x i j) (x i' j) \<le> dist (X i) (X i')" for i i'
  proof -
    have "dist (X i) (X i') = norm (X i - X i')"
      unfolding dist_norm by simp
    also have "norm (X i - X i') \<ge> norm (Rep_vector (X i - X i') j)"
      by (rule norm_vector_component)
    also have "Rep_vector (X i - X i') j = x i j - x i' j"
      unfolding x_def
      by (metis add_implies_diff diff_add_cancel plus_vector.rep_eq) 
    also have "norm (x i j - x i' j) = dist (x i j) (x i' j)"
      unfolding dist_norm by simp
    finally show ?thesis by assumption
  qed
  then show ?thesis
    unfolding Cauchy_def
    using \<open>Cauchy X\<close> unfolding Cauchy_def
    by (meson le_less_trans) 
qed

instantiation vector :: (type) chilbert_space begin
instance by (cheat vector_chilbert_space)
    (* proof intro_classes
  fix X :: "nat \<Rightarrow> 'a vector"
  assume "Cauchy X"
  define x where "x i = Rep_vector (X i)" for i
  then have [transfer_rule]: "rel_fun (=) (pcr_vector (=)) x X"
    unfolding vector.pcr_cr_eq cr_vector_def rel_fun_def by simp

  from \<open>Cauchy X\<close> have "Cauchy (\<lambda>i. x i j)" for j
    unfolding x_def
    by (rule Cauchy_vector_component)
  hence "convergent (\<lambda>i. x i j)" for j
    by (simp add: Cauchy_convergent_iff)
  then obtain Lx where "(\<lambda>i. x i j) \<longlonglongrightarrow> Lx j" for j
    unfolding convergent_def by metis

  define L where "L = Abs_vector Lx"
  have "has_ell2_norm Lx" by cheat
  then have [transfer_rule]: "pcr_vector (=) Lx L"
    unfolding vector.pcr_cr_eq cr_vector_def
    unfolding L_def apply (subst Abs_vector_inverse) by auto

  have XL: "X \<longlonglongrightarrow> L"
  proof (rule LIMSEQ_I)
    fix r::real assume "0<r"
    show "\<exists>no. \<forall>n\<ge>no. norm (X n - L) < r"
      apply transfer
      by cheat
  qed

  show "convergent X"
    using XL by (rule convergentI)
qed *)
end

(* TODO remove and document *)
abbreviation "timesScalarVec \<equiv> (scaleC :: complex \<Rightarrow> 'a vector \<Rightarrow> 'a vector)"

(* lift_definition timesScalarVec :: "complex \<Rightarrow> 'a vector \<Rightarrow> 'a vector" is "\<lambda>c x i. c * x i"
  by (fact ell2_norm_smult) *)
(* scaleC_scaleC: lemma timesScalarVec_twice[simp]: "timesScalarVec a (timesScalarVec b \<psi>) = timesScalarVec (a*b) \<psi>"
  by (transfer, auto) *)

(* scaleC_minus1_left - lemma uminus_vector: "(-\<psi>) = timesScalarVec (-1) \<psi>"
  apply transfer by auto *)

(* scaleC_one - lemma one_times_vec[simp]: "timesScalarVec 1 \<psi> = \<psi>"
  apply transfer by simp *)

(* scaleC_zero_right -- lemma times_zero_vec[simp]: "timesScalarVec c 0 = 0"
  apply transfer by simp *)

(* scaleC_add_right -- lemma timesScalarVec_add_right: "timesScalarVec c (x+y) = timesScalarVec c x + timesScalarVec c y" 
  apply transfer apply (rule ext) by algebra *)

(* scaleC_add_left - lemma timesScalarVec_add_left: "timesScalarVec (c+d) x = timesScalarVec c x + timesScalarVec d x"
  apply transfer apply (rule ext) by algebra *)

lemma ell2_ket[simp]: "norm (ket i) = 1"
  apply transfer unfolding ell2_norm_def real_sqrt_eq_1_iff
  apply (rule cSUP_eq_maximum)
   apply (rule_tac x="{i}" in bexI)
    apply auto
  by (rule ell2_1)

abbreviation cinner_Dirac::"'a::complex_inner \<Rightarrow> 'a \<Rightarrow> complex" ( "\<langle>_ | _\<rangle> " )
  where \<open>\<langle> x | y \<rangle> \<equiv> cinner x y\<close>

definition "is_orthogonal x y = (\<langle> x | y \<rangle> = 0)"

abbreviation is_orthogonal_abbr::"'a::complex_inner \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<bottom>" 50)
  where \<open>x \<bottom> y \<equiv> is_orthogonal x y\<close>

definition "orthogonal_complement S = {x. \<forall>y\<in>S. x \<bottom> y}" 

lemma orthogonal_comm: "(\<psi> \<bottom> \<phi>) = (\<phi> \<bottom> \<psi>)"
  unfolding is_orthogonal_def apply (subst cinner_commute) by blast

(* TODO: move \<rightarrow> Complex_Vector_Space *)
locale is_subspace =
  fixes A::"'a::complex_normed_vector set"
  assumes additive_closed: "x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x+y\<in>A"
  assumes smult_closed: "x\<in>A \<Longrightarrow> c *\<^sub>C x \<in> A"
  assumes closed: "closed A"
  assumes zero: "0 \<in> A"

lemma is_subspace_0[simp]: "is_subspace {0}"
  apply (rule is_subspace.intro) by auto

lemma is_subspace_UNIV[simp]: "is_subspace UNIV"
  apply (rule is_subspace.intro) by auto

lemma is_subspace_inter[simp]: assumes "is_subspace A" and "is_subspace B" shows "is_subspace (A\<inter>B)"
  apply (rule is_subspace.intro) 
  using assms[unfolded is_subspace_def]
  by auto

lemma is_subspace_contains_0: "is_subspace A \<Longrightarrow> 0 \<in> A"
  unfolding is_subspace_def by auto

(* lemma is_subspace_plus: assumes "is_subspace A" and "is_subspace B" shows "is_subspace {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}"
  apply (rule is_subspace.intro) 
proof -
  fix x y c assume x: "x \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}" and y: "y \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}"
  from x y show "x + y \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}"
    using assms[unfolded is_subspace_def]
    by (smt add.assoc add.commute mem_Collect_eq)
  from x obtain xA xB where sum: "x = xA + xB" and "xA : A" and "xB : B"
    by auto
  have cxA: "timesScalarVec c xA : A"
    by (simp add: \<open>xA \<in> A\<close> assms(1) is_subspace.smult_closed)
  have cxB: "timesScalarVec c xB : B"
    by (simp add: \<open>xB \<in> B\<close> assms(2) is_subspace.smult_closed)
  show "timesScalarVec c x \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}" 
    unfolding sum timesScalarVec_add_right using cxA cxB by auto
next
  show "closed {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}" by auto
  show "0 \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}" 
    using assms[unfolded is_subspace_def] apply auto by force
qed *)

lemma is_subspace_INF[simp]: "(\<And>x. x \<in> AA \<Longrightarrow> is_subspace x) \<Longrightarrow> is_subspace (\<Inter>AA)"
  apply (rule is_subspace.intro) unfolding is_subspace_def by auto

lemma is_subspace_orthog[simp]: "is_subspace A \<Longrightarrow> is_subspace (orthogonal_complement A)"
  by (cheat TODO6)

lemma is_subspace_plus: "is_subspace A \<Longrightarrow> is_subspace B \<Longrightarrow> is_subspace {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}" (* Proof above has only one missing step *)
  for A B :: "'a vector set"
  by (cheat TODO6)

typedef 'a subspace = "{A::'a vector set. is_subspace A}"
  morphisms subspace_to_set Abs_subspace
  apply (rule exI[of _ "{0}"]) by simp
setup_lifting type_definition_subspace
  (* derive universe subspace *)

instantiation subspace :: (type)zero begin (* The subspace {0} *)
lift_definition zero_subspace :: "'a subspace" is "{0::'a vector}" by simp
instance .. end

instantiation subspace :: (type)top begin  (* The full space *)
lift_definition top_subspace :: "'a subspace" is "UNIV::'a vector set" by simp
instance .. end

instantiation subspace :: (type)inf begin  (* Intersection *)
lift_definition inf_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace" is "(\<inter>)" by simp
instance .. end

instantiation subspace :: (type)sup begin  (* Sum of spaces *)
lift_definition sup_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace" is "\<lambda>A B::'a vector set. {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}" 
  by (rule is_subspace_plus)
instance .. end
instantiation subspace :: (type)plus begin  (* Sum of spaces *)
lift_definition plus_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace" is "\<lambda>A B::'a vector set. {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}"
  by (rule is_subspace_plus)
instance .. end

lemma subspace_sup_plus: "(sup :: 'a subspace \<Rightarrow> _ \<Rightarrow> _) = (+)" 
  unfolding sup_subspace_def plus_subspace_def by simp

instantiation subspace :: (type)Inf begin  (* Intersection *)
lift_definition Inf_subspace :: "'a subspace set \<Rightarrow> 'a subspace" is "Inf :: 'a vector set set \<Rightarrow> 'a vector set" by simp
instance .. end

instantiation subspace :: (type)ord begin  
lift_definition less_eq_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> bool" is "(\<subseteq>)". (* \<le> means inclusion *)
lift_definition less_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> bool" is "(\<subset>)". (* \<le> means inclusion *)
instance .. end

instantiation subspace :: (type)Sup begin (* Sum of spaces *)
definition "Sup_subspace AA = (Inf {B::'a subspace. \<forall>A\<in>AA. B \<ge> A})"
  (* lift_definition Sup_subspace :: "'a subspace set \<Rightarrow> 'a subspace" is "\<lambda>AA. Inf (A" by simp *)
  (* lift_definition Sup_subspace :: "\<Sqinter>A\<in>{A."  *)
instance .. end

lemma subspace_zero_not_top[simp]: "(0::'a subspace) \<noteq> top"
proof transfer 
  have "ket undefined \<noteq> (0::'a vector)"
    apply transfer
    by (meson one_neq_zero)
  thus "{0::'a vector} \<noteq> UNIV" by auto
qed


instantiation subspace :: (type)order begin
instance apply intro_classes
     apply transfer apply (simp add: subset_not_subset_eq)
    apply transfer apply simp
   apply transfer apply simp
  apply transfer by simp
end

instantiation subspace :: (type)order_top begin
instance apply intro_classes
  apply transfer by simp
end

instantiation subspace :: (type)order_bot begin
lift_definition bot_subspace :: "'a subspace" is "{0::'a vector}" by (fact is_subspace_0)
instance apply intro_classes
  apply transfer by (simp add: is_subspace_contains_0)
end
lemma subspace_zero_bot: "(0::_ subspace) = bot" 
  unfolding zero_subspace_def bot_subspace_def by simp

instantiation subspace :: (type)ab_semigroup_add begin
instance apply intro_classes
   apply transfer apply auto using add.assoc apply blast apply (metis add.semigroup_axioms semigroup.assoc)
  apply transfer apply auto using add.commute by blast+
end

instantiation subspace :: (type)ordered_ab_semigroup_add begin
instance apply intro_classes
  apply transfer by auto
end

instantiation subspace :: (type)comm_monoid_add begin
instance apply intro_classes
  apply transfer by auto
end

instantiation subspace :: (type)semilattice_sup begin
instance proof intro_classes
  fix x y z :: "'a subspace"
  show "x \<le> x \<squnion> y"
    apply transfer apply auto apply (rule exI, rule exI[of _ 0]) using is_subspace_contains_0 by auto
  show "y \<le> x \<squnion> y"
    apply transfer apply auto apply (rule exI[of _ 0]) using is_subspace_contains_0 by auto
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    apply transfer apply auto
    apply (rule is_subspace.additive_closed)
    by auto
qed
end

instantiation subspace :: (type)canonically_ordered_monoid_add begin
instance apply intro_classes
  unfolding subspace_sup_plus[symmetric]
  apply auto apply (rule_tac x=b in exI)
  by (simp add: sup.absorb2) 
end

instantiation subspace :: (type)semilattice_inf begin
instance apply intro_classes
    apply transfer apply simp
   apply transfer apply simp
  apply transfer by simp
end

instantiation subspace :: (type)lattice begin
instance ..
end

lemma  subspace_plus_sup: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y + z \<le> x" for x y z :: "'a subspace"
  unfolding subspace_sup_plus[symmetric] by auto

instantiation subspace :: (type)complete_lattice begin
instance proof intro_classes
  fix x z :: "'a subspace" and A
  show Inf_le: "x \<in> A \<Longrightarrow> Inf A \<le> x" for A and x::"'a subspace"
    apply transfer by auto
  show le_Inf: "(\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A" for A and z::"'a subspace"
    apply transfer by auto
  show "Inf {} = (top::'a subspace)"
    apply transfer by auto
  show "x \<le> Sup A" if "x \<in> A"
    unfolding Sup_subspace_def 
    apply (rule le_Inf)
    using that by auto
  show "(\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z" 
    unfolding Sup_subspace_def
    apply (rule Inf_le)
    by auto
  have "Inf UNIV = (bot::'a subspace)"    
    apply (rule antisym)
     apply (rule Inf_le) apply simp
    apply (rule le_Inf) by simp
  thus "Sup {} = (bot::'a subspace)"
    unfolding Sup_subspace_def by auto
qed
end

lemma subspace_empty_Sup: "Sup {} = (0::'a subspace)"
  unfolding subspace_zero_bot by auto

lemma top_not_bot[simp]: "(top::'a subspace) \<noteq> bot"
  by (metis subspace_zero_bot subspace_zero_not_top) 
lemma bot_not_top[simp]: "(bot::'a subspace) \<noteq> top"
  by (metis top_not_bot)

lemma inf_assoc_subspace[simp]: "A \<sqinter> B \<sqinter> C = A \<sqinter> (B \<sqinter> C)" for A B C :: "_ subspace"
  unfolding inf.assoc by simp
lemma inf_left_commute[simp]: "A \<sqinter> (B \<sqinter> C) = B \<sqinter> (A \<sqinter> C)" for A B C :: "_ subspace"
  using inf.left_commute by auto

lemma bot_plus[simp]: "bot + x = x" for x :: "'a subspace"
  apply transfer
  unfolding sup_subspace_def[symmetric] by simp
lemma plus_bot[simp]: "x + bot = x" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp
lemma top_plus[simp]: "top + x = top" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp
lemma plus_top[simp]: "x + top = top" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp


(* TODO remove *)
abbreviation subspace_as_set :: "'a subspace \<Rightarrow> 'a vector set" where "subspace_as_set == subspace_to_set"


definition [code del]: "span A = Inf {S. A \<subseteq> subspace_as_set S}"
  (* definition [code del]: "spanState A = Inf {S. state_to_vector ` A \<subseteq> subspace_as_set S}" *)
  (* consts span :: "'a set \<Rightarrow> 'b subspace"
adhoc_overloading span (* spanState *) spanVector *)

(* lemma span_vector_state: "spanState A = spanVector (state_to_vector ` A)"
  by (simp add: spanState_def spanVector_def)  *)

lemma span_mult[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> span { timesScalarVec a \<psi> } = span {\<psi>}"
  for \<psi>::"'a vector"
  by (cheat TODO6)

lemma leq_INF[simp]:
  fixes V :: "'a \<Rightarrow> 'b subspace"
  shows "(A \<le> (INF x. V x)) = (\<forall>x. A \<le> V x)"
  by (simp add: le_Inf_iff)

lemma leq_plus_subspace[simp]: "a \<le> a + c" for a::"'a subspace"
  by (simp add: add_increasing2)
lemma leq_plus_subspace2[simp]: "a \<le> c + a" for a::"'a subspace"
  by (simp add: add_increasing)

lift_definition ortho :: "'a subspace \<Rightarrow> 'a subspace" is orthogonal_complement 
  by (fact is_subspace_orthog)

lemma span_superset:
  \<open>A \<subseteq> subspace_as_set (span A)\<close> for A :: \<open>('a vector) set\<close>
proof-
  have \<open>\<forall> S. S \<in> {S. A \<subseteq> subspace_as_set S} \<longrightarrow> A \<subseteq> subspace_as_set S\<close>
    by simp
  hence \<open>A \<subseteq> \<Inter> {subspace_as_set S| S. A \<subseteq> subspace_as_set S}\<close>
    by blast
  hence \<open>A \<subseteq> subspace_as_set( Inf {S| S. A \<subseteq> subspace_as_set S})\<close>
    by (metis (no_types, lifting)  INF_greatest Inf_subspace.rep_eq \<open>\<forall>S. S \<in> {S. A \<subseteq> subspace_as_set S} \<longrightarrow> A \<subseteq> subspace_as_set S\<close>)
  thus ?thesis using span_def by metis
qed


thm LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1]


subsection {* There exists a unique point k in M such that the distance between h and M reaches
 its minimum at k *}


definition is_arg_min_on :: \<open>('a \<Rightarrow> 'b :: ord) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>is_arg_min_on f M x = (is_arg_min f (\<lambda> t. t \<in> M) x)\<close>


lemma ExistenceUniquenessMinNorm:
  fixes M :: \<open>('a::{complex_inner, complete_space}) set\<close>  
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>! k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) M k\<close>
(*
It is not possible to generalize to Banach spaces, at least in the obvious way, the results from 
Conway's book, in which the parallelogram law is involved, because a Banach space in which this 
identity holds is automatically a Hilbert space.
*)

proof-
  have \<open>\<exists> k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) M k\<close>
  proof-
    have \<open>\<exists> k. is_arg_min_on (\<lambda> x. (\<parallel>x\<parallel>)^2) M k\<close>
    proof-
      obtain d where \<open>d = Inf { (\<parallel>x\<parallel>)^2 | x. x \<in> M }\<close>
        by blast
      have \<open>{ (\<parallel>x\<parallel>)^2 | x. x \<in> M } \<noteq> {}\<close>
        by (simp add: assms(3))
      have \<open>\<forall> x. (\<parallel>x\<parallel>)^2 \<ge> 0\<close>
        by simp
      hence \<open>bdd_below  { (\<parallel>x\<parallel>)^2 | x. x \<in> M }\<close>
        by fastforce
      have \<open>x \<in> M \<Longrightarrow> d \<le> (\<parallel>x\<parallel>)^2\<close> for x
      proof -
        assume a1: "x \<in> M"
        have "\<forall>v. (\<exists>va. Re (\<langle>v | v\<rangle> ) = (\<parallel>va\<parallel>)\<^sup>2 \<and> va \<in> M) \<or> v \<notin> M"
          by (metis (no_types) Re_complex_of_real power2_norm_eq_cinner')
        then have "Re (\<langle>x | x\<rangle> ) \<in> {(\<parallel>v\<parallel>)\<^sup>2 |v. v \<in> M}"
          using a1 by blast
        then show ?thesis
          by (metis (lifting) Re_complex_of_real \<open>bdd_below {(\<parallel>x\<parallel>)\<^sup>2 |x. x \<in> M}\<close> \<open>d = Inf {(\<parallel>x\<parallel>)\<^sup>2 |x. x \<in> M}\<close> cInf_lower power2_norm_eq_cinner')
      qed
      have  \<open>\<forall> n::nat. \<exists> x \<in> M.  (\<parallel>x\<parallel>)^2 < d + 1/(n+1)\<close>
      proof-
        have \<open>\<forall> \<epsilon> > 0. \<exists> t \<in> { (\<parallel>x\<parallel>)^2 | x. x \<in> M }.  t < d + \<epsilon>\<close>
          using \<open>d = Inf { (\<parallel>x\<parallel>)^2 | x. x \<in> M }\<close>  \<open>{ (\<parallel>x\<parallel>)^2 | x. x \<in> M } \<noteq> {}\<close>  \<open>bdd_below  { (\<parallel>x\<parallel>)^2 | x. x \<in> M }\<close>
          by (meson cInf_lessD less_add_same_cancel1)
        hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  (\<parallel>x\<parallel>)^2 < d + \<epsilon>\<close>
          by auto    
        hence \<open>\<forall> \<epsilon> > 0. \<exists> x \<in> M.  (\<parallel>x\<parallel>)^2 < d + \<epsilon>\<close>
          by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> (\<parallel>x\<parallel>)\<^sup>2\<close>)
        thus ?thesis by auto
      qed
      then obtain r::\<open>nat \<Rightarrow> 'a::{complex_inner, complete_space}\<close> where \<open>\<forall> n. r n \<in> M \<and>  (\<parallel> r n \<parallel>)^2 < d + 1/(n+1)\<close>
        by metis
      have \<open>\<forall> n. r n \<in> M\<close> 
        by (simp add: \<open>\<forall>n. r n \<in> M \<and>  (\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / (real n + 1)\<close>)
      have \<open>\<forall> n. (\<parallel> r n \<parallel>)^2 < d + 1/(n+1)\<close>
        by (simp add: \<open>\<forall>n. r n \<in> M \<and> (\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / (real n + 1)\<close>)    
      have \<open>(\<parallel> (r n) - (r m) \<parallel>)^2 < 2*(1/(n+1) + 1/(m+1))\<close> for m n 
      proof-
        have \<open> (\<parallel> r n \<parallel>)^2 < d + 1/(n+1)\<close>
          by (metis \<open>\<forall>n. r n \<in> M \<and> (\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / (real n + 1)\<close>  of_nat_1 of_nat_add)
        have \<open> (\<parallel> r m \<parallel>)^2 < d + 1/(m+1)\<close>
          by (metis \<open>\<forall>n. r n \<in> M \<and> (\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / (real n + 1)\<close>  of_nat_1 of_nat_add)
        have \<open>(r n) \<in> M\<close> 
          by (simp add: \<open>\<forall>n. r n \<in> M\<close>)
        moreover have \<open>(r m) \<in> M\<close> 
          by (simp add: \<open>\<forall>n. r n \<in> M\<close>)
        ultimately have \<open>(1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<in> M\<close>
          using \<open>convex M\<close> 
          by (simp add: convexD)
        hence \<open> (\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>)^2 \<ge> d\<close>
          by (simp add: \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> (\<parallel>x\<parallel>)\<^sup>2\<close>)
        have \<open>(\<parallel> (1/2) *\<^sub>R (r n) - (1/2) *\<^sub>R (r m) \<parallel>)^2
              = (1/2)*( (\<parallel> r n \<parallel>)^2 + (\<parallel> r m \<parallel>)^2 ) - (\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>)^2\<close> 
          using  ParallelogramLawVersion1 
          by (simp add: ParallelogramLawVersion1 scaleR_scaleC)
        also have  \<open>...  
              < (1/2)*( d + 1/(n+1) + (\<parallel> r m \<parallel>)^2 ) - (\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>)^2\<close>
          using \<open>(\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / real (n + 1)\<close> by auto
        also have  \<open>...  
              < (1/2)*( d + 1/(n+1) + d + 1/(m+1) ) - (\<parallel> (1/2) *\<^sub>R (r n) + (1/2) *\<^sub>R (r m) \<parallel>)^2\<close>
          using \<open>(\<parallel>r m\<parallel>)\<^sup>2 < d + 1 / real (m + 1)\<close> by auto
        also have  \<open>...  
              \<le> (1/2)*( d + 1/(n+1) + d + 1/(m+1) ) - d\<close>
          by (simp add: \<open>d \<le> (\<parallel>(1 / 2) *\<^sub>R r n + (1 / 2) *\<^sub>R r m\<parallel>)\<^sup>2\<close>)
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
        finally have \<open> (\<parallel>(1 / 2) *\<^sub>R r n - (1 / 2) *\<^sub>R r m\<parallel>)\<^sup>2 < 1 / 2 * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by blast
        hence \<open> (\<parallel>(1 / 2) *\<^sub>R (r n - r m) \<parallel>)\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by (simp add: scale_right_diff_distrib)
        hence \<open> ((1 / 2)*(\<parallel> (r n - r m) \<parallel>))\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by simp
        hence \<open> (1 / 2)^2*((\<parallel> (r n - r m) \<parallel>))\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by (metis power_mult_distrib)
        hence \<open> (1 / 4) *((\<parallel> (r n - r m) \<parallel>))\<^sup>2 < (1 / 2) * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by (simp add: power_divide)
        hence \<open> (\<parallel> (r n - r m) \<parallel>)\<^sup>2 < 2 * (1 / real (n + 1) + 1 / real (m + 1)) \<close>
          by simp
        thus ?thesis 
          by (metis of_nat_1 of_nat_add)
      qed
      hence  \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> (\<parallel> (r n) - (r m) \<parallel>)^2 < \<epsilon>^2\<close> for \<epsilon>
      proof-
        assume \<open>\<epsilon> > 0\<close>
        obtain N::nat where \<open>1/(N + 1) < \<epsilon>^2/4\<close>
          using LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1]
          by (metis Suc_eq_plus1 \<open>0 < \<epsilon>\<close> nat_approx_posE zero_less_divide_iff zero_less_numeral zero_less_power )
        hence \<open>4/(N + 1) < \<epsilon>^2\<close>
          by simp
        have \<open>n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> 2*(1/(n+1) + 1/(m+1)) < \<epsilon>^2\<close> for m n::nat
        proof-
          assume \<open>n \<ge> N\<close>
          hence \<open>1/(n+1) \<le> 1/(N+1)\<close> 
            by (simp add: linordered_field_class.frac_le)
          assume \<open>m \<ge> N\<close>
          hence \<open>1/(m+1) \<le> 1/(N+1)\<close> 
            by (simp add: linordered_field_class.frac_le)
          have  \<open>2*(1/(n+1) + 1/(m+1)) \<le> 4/(N+1)\<close>
            using  \<open>1/(n+1) \<le> 1/(N+1)\<close>  \<open>1/(m+1) \<le> 1/(N+1)\<close>
            by simp
          thus ?thesis using \<open>4/(N + 1) < \<epsilon>^2\<close> 
            by linarith
        qed
        hence \<open> n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> (\<parallel> (r n) - (r m) \<parallel>)^2 < \<epsilon>^2\<close> for m n::nat
          by (smt \<open>\<And>n m. (\<parallel>r n - r m\<parallel>)\<^sup>2 < 2 * (1 / (real n + 1) + 1 / (real m + 1))\<close> of_nat_1 of_nat_add)
        thus ?thesis 
          by blast
      qed
      hence  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> (\<parallel> (r n) - (r m) \<parallel>)^2 < \<epsilon>^2\<close>
        by blast
      hence  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n m::nat. n \<ge> N \<and> m \<ge> N \<longrightarrow> (\<parallel> (r n) - (r m) \<parallel>) < \<epsilon>\<close>
        by (meson less_eq_real_def power_less_imp_less_base)
      hence \<open>Cauchy r\<close>
        using CauchyI by fastforce
      then obtain k where \<open>r \<longlonglongrightarrow> k\<close>
        using  convergent_eq_Cauchy by auto
      have \<open>k \<in> M\<close> using \<open>closed M\<close>
        using \<open>\<forall>n. r n \<in> M\<close> \<open>r \<longlonglongrightarrow> k\<close> closed_sequentially by auto
      have  \<open>(\<lambda> n.  (\<parallel> r n \<parallel>)^2) \<longlonglongrightarrow>  (\<parallel> k \<parallel>)^2\<close>
        by (simp add: \<open>r \<longlonglongrightarrow> k\<close> tendsto_norm tendsto_power)
      moreover  have  \<open>(\<lambda> n.  (\<parallel> r n \<parallel>)^2) \<longlonglongrightarrow>  d\<close>
      proof-
        have \<open>\<bar>(\<parallel> r n \<parallel>)^2 - d\<bar> < 1/(n+1)\<close> for n :: nat
          by (smt \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> (\<parallel>x\<parallel>)\<^sup>2\<close> \<open>\<forall>n. r n \<in> M \<and> (\<parallel>r n\<parallel>)\<^sup>2 < d + 1 / (real n + 1)\<close> of_nat_1 of_nat_add)
        moreover have \<open>(\<lambda>n. 1 / real (n + 1)) \<longlonglongrightarrow> 0\<close> 
          using  LIMSEQ_ignore_initial_segment[OF lim_inverse_n', where k=1] by blast        
        ultimately have \<open>(\<lambda> n. \<bar>(\<parallel> r n \<parallel>)^2 - d\<bar> ) \<longlonglongrightarrow> 0\<close> 
          by (simp add: LIMSEQ_norm_0)
        hence \<open>(\<lambda> n. (\<parallel> r n \<parallel>)^2 - d ) \<longlonglongrightarrow> 0\<close> 
          by (simp add: tendsto_rabs_zero_iff)
        moreover have \<open>(\<lambda> n. d ) \<longlonglongrightarrow> d\<close>
          by simp
        ultimately have \<open>(\<lambda> n. ((\<parallel> r n \<parallel>)^2 - d)+d ) \<longlonglongrightarrow> 0+d\<close> 
          using tendsto_add by fastforce
        thus ?thesis by simp
      qed
      ultimately have \<open>d = (\<parallel> k \<parallel>)^2\<close>
        using LIMSEQ_unique by auto
      hence \<open>t \<in> M \<Longrightarrow> (\<parallel> k \<parallel>)^2 \<le> (\<parallel> t \<parallel>)^2\<close> for t
        using \<open>\<And>x. x \<in> M \<Longrightarrow> d \<le> (\<parallel>x\<parallel>)\<^sup>2\<close> by auto
      thus ?thesis using \<open>k \<in> M\<close>
        unfolding is_arg_min_on_def
        using is_arg_min_def \<open>d = (\<parallel>k\<parallel>)\<^sup>2\<close>
        by smt
    qed

    thus ?thesis 
      unfolding is_arg_min_on_def
      by (smt is_arg_min_def norm_ge_zero power2_eq_square power2_le_imp_le)
  qed
  moreover have \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r \<Longrightarrow> is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s \<Longrightarrow> r = s\<close> for r s
  proof-
    assume \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close>
    assume \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>
    have \<open>(\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>)^2
      = (1/2)*( (\<parallel>r\<parallel>)^2 + (\<parallel>s\<parallel>)^2 ) - (\<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>)^2\<close> 
      using  ParallelogramLawVersion1 
      by (simp add: ParallelogramLawVersion1 scaleR_scaleC)
    moreover have \<open>(\<parallel>r\<parallel>)^2 \<le> (\<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>)^2\<close>
    proof-
      have \<open>r \<in> M\<close> 
        using \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close>
        by (simp add: is_arg_min_def is_arg_min_on_def)
      moreover have \<open>s \<in> M\<close> 
        using \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>
        by (simp add: is_arg_min_def is_arg_min_on_def)
      ultimately have \<open>((1/2) *\<^sub>R r + (1/2) *\<^sub>R s) \<in> M\<close> using \<open>convex M\<close>
        by (simp add: convexD)
      hence \<open> (\<parallel>r\<parallel>) \<le> (\<parallel> (1/2) *\<^sub>R r + (1/2) *\<^sub>R s \<parallel>)\<close>
        using  \<open>is_arg_min_on norm_abbr M r\<close>
        unfolding is_arg_min_on_def
        by (smt is_arg_min_def)
      thus ?thesis
        using norm_ge_zero power_mono by blast
    qed
    moreover have \<open>(\<parallel>r\<parallel>) = (\<parallel>s\<parallel>)\<close>
    proof-
      have \<open>(\<parallel>r\<parallel>) \<le> (\<parallel>s\<parallel>)\<close> 
        using  \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close> \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>  is_arg_min_def 
        unfolding is_arg_min_on_def
        by smt

      moreover have \<open>(\<parallel>s\<parallel>) \<le> (\<parallel>r\<parallel>)\<close>
        using  \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M r\<close> \<open>is_arg_min_on (\<lambda>x. \<parallel>x\<parallel>) M s\<close>  is_arg_min_def 
        unfolding is_arg_min_on_def
        by smt

      ultimately show ?thesis by simp
    qed
    ultimately have \<open>(\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>)^2 \<le> 0\<close>
      by simp
    hence \<open>(\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>)^2 = 0\<close>
      by simp
    hence \<open>(\<parallel> (1/2) *\<^sub>R r - (1/2) *\<^sub>R s \<parallel>) = 0\<close>
      by auto
    hence \<open>(1/2) *\<^sub>R r - (1/2) *\<^sub>R s = 0\<close>
      using norm_eq_zero by blast
    thus ?thesis by simp
  qed
  ultimately show ?thesis 
    by auto
qed

(* Connected.closed_translation shows the same thing, but only for 'a::real_normed_vector *)
lemma TransClosed:
  \<open>closed (S::('a::{topological_ab_group_add,t2_space,first_countable_topology}) set) \<Longrightarrow> closed {s + h| s. s \<in> S}\<close>
proof-
  assume \<open>closed S\<close>
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. r n \<in> S) \<longrightarrow> lim r \<in> S\<close>
    using closed_sequentially convergent_LIMSEQ_iff by blast
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. r n \<in>  {s | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n)) \<in>  {s | s. s \<in> S}\<close>
    by simp
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n) \<in>  {s | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+h \<in>  {s+h | s. s \<in> S}\<close>
    by blast
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+h \<in>  {s+h | s. s \<in> S}\<close>
    by simp
  hence \<open>\<forall> r::nat \<Rightarrow> 'a. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+lim (\<lambda> n. h) \<in>  {s+h | s. s \<in> S}\<close>
    by auto
  have \<open>convergent r \<Longrightarrow>  (lim r) + h = lim (\<lambda> n. (r n)+h)\<close> for r::\<open>nat \<Rightarrow> 'a\<close>
  proof-
    assume \<open>convergent r\<close>
    then obtain R where \<open>r \<longlonglongrightarrow> R\<close>
      using convergent_def by auto
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
  have \<open> \<forall>r. convergent (\<lambda>n. r n + (h::'a)) \<and> (\<forall>n. r n \<in> S)
 \<longrightarrow> (\<exists>s. lim (\<lambda>n. r n + h) = s + h \<and> s \<in> S)
 \<Longrightarrow>   convergent t \<Longrightarrow> \<forall>n. \<exists>s. t n = s + h \<and> s \<in> S \<Longrightarrow> \<exists>s. lim t = s + h \<and> s \<in> S \<close> for t
  proof-
    assume \<open> \<forall>r. convergent (\<lambda>n. r n + h) \<and> (\<forall>n. r n \<in> S) \<longrightarrow> (\<exists>s. lim (\<lambda>n. r n + h) = s + h \<and> s \<in> S) \<close>
    assume \<open>convergent t\<close>
    assume \<open>\<forall>n. \<exists>s. t n = s + h \<and> s \<in> S\<close>
    obtain r::\<open>nat \<Rightarrow> 'a\<close> where \<open>\<forall>n. t n = (r n) + h \<and> r n \<in> S\<close> using  \<open>\<forall>n. \<exists>s. t n = s + h \<and> s \<in> S\<close>
      by metis
    from  \<open>\<forall>n. t n = (r n) + h \<and> r n \<in> S\<close>
    have  \<open>\<forall>n. t n = (r n) + h\<close> by simp
    from  \<open>\<forall>n. t n = (r n) + h \<and> r n \<in> S\<close>
    have  \<open>\<forall>n. r n \<in> S\<close> by simp
    have \<open> convergent (\<lambda>n. t n) \<close> using  \<open>convergent t\<close> by blast
    hence \<open> convergent (\<lambda>n. (r n) + h) \<close> using   \<open>\<forall>n. t n = (r n) + h\<close> 
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


theorem ExistenceUniquenessMinDist:
  fixes M :: \<open>('a::{complex_inner, complete_space}) set\<close> and h :: 'a 
  assumes \<open>convex M\<close> and \<open>closed M\<close> and \<open>M \<noteq> {}\<close>
  shows  \<open>\<exists>! k. is_arg_min_on (\<lambda> x. dist x h) M k\<close>
    (* Reference: Theorem 2.5 in conway2013course *)
proof-
  have \<open>{m - h| m. m \<in> M} \<noteq> {}\<close>
    by (simp add: assms(3))
  moreover have \<open>closed {m - h| m. m \<in> M}\<close>
  proof-
    have \<open>closed {m + (- h)| m. m \<in> M}\<close>
      using  \<open>closed M\<close> TransClosed by blast
    thus ?thesis by simp
  qed
  moreover have \<open>convex {m - h| m. m \<in> M}\<close>
  proof-
    have \<open>convex ((\<lambda>x. -h + x) ` M)\<close>
      using convex_translation \<open>convex M\<close> by blast
    hence \<open>convex ((\<lambda>x.  x - h) ` M)\<close> by simp
    moreover have \<open>{(\<lambda>x.  x - h) m | m. m \<in> M} = ((\<lambda>x.  x - h) ` M)\<close>
      by auto
    ultimately show ?thesis by simp
  qed
  ultimately have \<open>\<exists>! k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h| m. m \<in> M} k\<close>
    by (simp add: ExistenceUniquenessMinNorm)
  have \<open>\<exists>! k. is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M k\<close>
  proof-
    have \<open>\<exists> k. is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M k\<close>
    proof-
      obtain k where \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h| m. m \<in> M} k\<close>
        using  \<open>\<exists>! k. is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h| m. m \<in> M} k\<close> by blast
      have \<open>(\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k\<parallel>) \<le> (\<parallel>t\<parallel>)) \<and> k \<in> {m - h |m. m \<in> M}\<close>
        using is_arg_min_def  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h| m. m \<in> M} k\<close>
        unfolding is_arg_min_on_def
        by smt

      hence \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k\<parallel>) \<le> (\<parallel>t\<parallel>)\<close>
        by blast
      hence \<open>\<forall>t. t + h \<in> M \<longrightarrow> (\<parallel>k\<parallel>) \<le> (\<parallel>t\<parallel>)\<close>
        by auto
      hence \<open>\<forall>t. t \<in> M \<longrightarrow> (\<parallel>k\<parallel>) \<le> (\<parallel>t - h\<parallel>)\<close>
        by auto
      hence \<open>\<forall>t. t \<in> M \<longrightarrow> (\<parallel>(k+h)-h\<parallel>) \<le> (\<parallel>t - h\<parallel>)\<close>
        by auto
      from \<open>(\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k\<parallel>) \<le> (\<parallel>t\<parallel>)) \<and> k \<in> {m - h |m. m \<in> M}\<close>
      have  \<open>k \<in> {m - h |m. m \<in> M}\<close>
        by blast
      hence  \<open>k + h \<in> M\<close>
        by auto

      have \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) {m| m. m \<in> M} (k + h)\<close>
      proof-
        have \<open>\<nexists>y. y \<in> {m |m. m \<in> M} \<and> \<parallel>y - h\<parallel> < \<parallel>(k + h) - h\<parallel>\<close>
          using \<open>\<forall>t. t \<in> M \<longrightarrow> (\<parallel>(k+h)-h\<parallel>) \<le> (\<parallel>t - h\<parallel>)\<close>  
          by auto
        thus ?thesis
          using \<open>k + h \<in> M\<close>
          unfolding is_arg_min_on_def
          by (simp add: is_arg_min_def)
      qed
      thus ?thesis 
        by auto
    qed 
    moreover have \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  k \<Longrightarrow> is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  t
                    \<Longrightarrow> k = t\<close> for k t
    proof-
      have \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  k \<Longrightarrow> is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h |m. m \<in> M} (k - h)\<close> for k
      proof-
        assume \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  k \<close>
        hence \<open>\<forall>t. t \<in> M \<longrightarrow> (\<parallel>k - h\<parallel>) \<le> (\<parallel>t - h\<parallel>)\<close>
          unfolding is_arg_min_on_def
          by (meson is_arg_min_linorder)

        hence \<open>\<forall>t. t - h \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k - h\<parallel>) \<le> (\<parallel>t - h\<parallel>)\<close>
          by auto
        hence \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k - h\<parallel>) \<le> (\<parallel>t\<parallel>)\<close>
          by blast
        have \<open>k \<in> M\<close>
          using  \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M  k \<close>
          unfolding is_arg_min_on_def
          using is_arg_min_def
          by (simp add: is_arg_min_linorder)

        hence \<open>k - h \<in> {m - h |m. m \<in> M}\<close>
          by auto
        have  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>) {m - h |m. m \<in> M} (k - h)\<close>
          using  \<open>\<forall>t. t \<in> {m - h |m. m \<in> M} \<longrightarrow> (\<parallel>k - h\<parallel>) \<le> (\<parallel>t\<parallel>)\<close>
            \<open>k - h \<in> {m - h |m. m \<in> M}\<close>
            is_arg_min_def
          unfolding is_arg_min_on_def
          by smt
        thus ?thesis by blast
      qed

      assume \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M k\<close>
      hence  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>)  {m - h |m. m \<in> M} (k - h)\<close>
        by (simp add: \<open>\<And>k. is_arg_min_on (\<lambda>x. \<parallel>x - h\<parallel>) M k \<Longrightarrow> is_arg_min_on norm_abbr {m - h |m. m \<in> M} (k - h)\<close>)

      assume  \<open>is_arg_min_on (\<lambda> x. \<parallel>x - h\<parallel>) M t\<close> 
      hence  \<open>is_arg_min_on (\<lambda> x. \<parallel>x\<parallel>)  {m - h |m. m \<in> M} (t - h)\<close>
        using \<open>\<And>k. is_arg_min_on (\<lambda>x. \<parallel>x - h\<parallel>) M k \<Longrightarrow> is_arg_min_on norm_abbr {m - h |m. m \<in> M} (k - h)\<close> by auto

      show ?thesis 
        by (metis (no_types, lifting) \<open>\<exists>!k. is_arg_min_on norm_abbr {m - h |m. m \<in> M} k\<close> \<open>is_arg_min_on norm_abbr {m - h |m. m \<in> M} (k - h)\<close> \<open>is_arg_min_on norm_abbr {m - h |m. m \<in> M} (t - h)\<close> diff_add_cancel)

    qed
    ultimately show ?thesis by blast
  qed
  moreover have \<open>(\<lambda> x. dist x h) = (\<lambda> x. \<parallel>x - h\<parallel>)\<close>
    by (simp add: dist_norm)
  ultimately show ?thesis by simp
qed

theorem DistMinOrtho:
  fixes M :: \<open>('a::{complex_inner, complete_space}) set\<close> and h k::\<open>'a\<close> 
  assumes "is_subspace M"
  shows  \<open>(is_arg_min_on (\<lambda> x. dist x h) M k)
       \<longleftrightarrow> h - k \<in> (orthogonal_complement M) \<and> k \<in> M\<close>
    (* Reference: Theorem 2.6 in conway2013course *)
proof-
  have \<open>is_arg_min_on (\<lambda> x. dist x h) M k
     \<Longrightarrow>  h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
  proof-
    assume \<open>is_arg_min_on (\<lambda> x. dist x h) M k\<close>
    hence  \<open>k \<in> M\<close>
      unfolding is_arg_min_on_def
      by (simp add: is_arg_min_def)
    moreover have \<open>h - k \<in> orthogonal_complement M\<close>
    proof-
      have \<open>f \<in> M \<Longrightarrow> \<langle> h - k | f \<rangle> = 0\<close> for f
      proof-
        assume \<open>f \<in> M\<close>
        hence  \<open>\<forall> c. c *\<^sub>R f \<in> M\<close>
          by (simp add: assms is_subspace.smult_closed scaleR_scaleC)
        have \<open>f \<in> M \<Longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<le> (\<parallel> f \<parallel>)^2\<close> for f
        proof-
          assume \<open>f \<in>  M\<close>             
          hence \<open>k + f \<in>  M\<close> 
            by (simp add: assms calculation is_subspace.additive_closed)
          hence \<open>dist h k \<le> dist  h (k + f)\<close>
          proof -
            have "\<forall>f A a aa. \<not> is_arg_min_on f A (a::'a) \<or> (f a::real) \<le> f aa \<or> aa \<notin> A"
              by (metis (no_types) is_arg_min_linorder is_arg_min_on_def)
            then have "dist k h \<le> dist (f + k) h"
              by (metis \<open>is_arg_min_on (\<lambda>x. dist x h) M k\<close> \<open>k + f \<in> M\<close> add.commute)
            then show ?thesis
              by (simp add: add.commute dist_commute)
          qed
          hence \<open>(\<parallel> h - k \<parallel>) \<le> (\<parallel> h - (k + f) \<parallel>)\<close>
            by (simp add: dist_norm)
          hence \<open>(\<parallel> h - k \<parallel>)^2 \<le> (\<parallel> h - (k + f) \<parallel>)^2\<close>
            by (simp add: power_mono)
          also have \<open>... \<le> (\<parallel> (h - k) - f \<parallel>)^2\<close>
            by (simp add: diff_diff_add)
          also have \<open>... \<le> (\<parallel> (h - k) \<parallel>)^2 + (\<parallel> f \<parallel>)^2 -  2 * Re (\<langle> h - k | f \<rangle>)\<close>
            by (simp add: polarization_identity_minus)
          finally have \<open>(\<parallel> (h - k) \<parallel>)^2 \<le> (\<parallel> (h - k) \<parallel>)^2 + (\<parallel> f \<parallel>)^2 -  2 * Re (\<langle> h - k | f \<rangle>)\<close>
            by simp
          thus ?thesis by simp
        qed
        hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<le> (\<parallel> f \<parallel>)^2\<close>
          by blast
        hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (\<langle> h - k | f \<rangle>) = 0\<close>
        proof-
          have \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real.  2 * Re (\<langle> h - k | c *\<^sub>R f \<rangle>) \<le> (\<parallel> c *\<^sub>R f \<parallel>)^2)\<close>
            by (metis \<open>\<And>f. f \<in> M \<Longrightarrow> 2 * Re \<langle>h - k | f\<rangle> \<le> \<parallel>f\<parallel>\<^sup>2\<close> assms is_subspace.smult_closed scaleR_scaleC)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (\<langle> h - k | f \<rangle>)) \<le> (\<parallel> c *\<^sub>R f \<parallel>)^2)\<close>
            by (metis Re_complex_of_real cinner_scaleC_right complex_add_cnj complex_cnj_complex_of_real complex_cnj_mult of_real_mult scaleR_scaleC semiring_normalization_rules(34))
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c * (2 * Re (\<langle> h - k | f \<rangle>)) \<le> \<bar>c\<bar>^2*(\<parallel> f \<parallel>)^2)\<close>
            by (simp add: power_mult_distrib)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c * (2 * Re (\<langle> h - k | f \<rangle>)) \<le> c^2*(\<parallel> f \<parallel>)^2)\<close>
            by auto
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> c * (2 * Re (\<langle> h - k | f \<rangle>)) \<le> c^2*(\<parallel> f \<parallel>)^2)\<close>
            by simp
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> c*(2 * Re (\<langle> h - k | f \<rangle>)) \<le> c*(c*(\<parallel> f \<parallel>)^2))\<close>
            by (simp add: power2_eq_square)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<le> c*(\<parallel> f \<parallel>)^2)\<close>
            by simp 
          have \<open>f \<in>  M \<Longrightarrow> \<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<le> 0\<close> for f
          proof-
            assume \<open>f \<in>  M\<close> 
            hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k | f \<rangle>) \<le> c*(\<parallel> f \<parallel>)^2\<close>
              by (simp add: \<open>\<forall>f. f \<in> M \<longrightarrow> (\<forall>c>0. 2 * Re \<langle>h - k | f\<rangle> \<le> c * \<parallel>f\<parallel>\<^sup>2)\<close>)
            hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k | f \<rangle>) \<le> c\<close>
            proof (cases \<open>(\<parallel> f \<parallel>)^2 > 0\<close>)
              case True
              hence \<open>\<forall> c > 0.  2 * Re (\<langle> h - k | f \<rangle>) \<le> (c/(\<parallel> f \<parallel>)^2)*(\<parallel> f \<parallel>)^2\<close>
                using \<open>\<forall>c>0. 2 * Re (\<langle>h - k | f\<rangle> ) \<le> c * (\<parallel>f\<parallel>)\<^sup>2\<close> linordered_field_class.divide_pos_pos by blast
              then show ?thesis 
                using True by auto
            next
              case False
              hence \<open>(\<parallel> f \<parallel>)^2 = 0\<close> 
                by simp
              then show ?thesis 
                by auto
            qed
            thus ?thesis 
              by smt
          qed
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<le> 0)\<close>
            by simp
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> (2 * Re (\<langle> h - k | (-1) *\<^sub>R f \<rangle>)) \<le> 0)\<close>
            by (metis assms is_subspace.smult_closed scaleR_scaleC)
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow>
                (\<forall> c::real. c > 0 \<longrightarrow> -(2 * Re (\<langle> h - k | f \<rangle>)) \<le> 0)\<close>
            by simp
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) \<ge> 0)\<close>
            by simp
          hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) = 0)\<close>
            using  \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                (\<forall> c::real. c > 0 \<longrightarrow> (2 * Re (\<langle> h - k | f \<rangle>)) \<le> 0)\<close>
            by fastforce
          hence \<open>\<forall> f. f \<in>  M \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) = 0\<close>
          proof-
            have \<open>\<forall> f. f \<in>  M \<longrightarrow> 
                 ((1::real) > 0 \<longrightarrow> 2 * Re (\<langle> h - k | f \<rangle>) = 0)\<close>
              using \<open>\<forall>f. f \<in>  M \<longrightarrow> (\<forall>c>0. 2 * Re (\<langle>h - k | f\<rangle> ) = 0)\<close> by blast
            thus ?thesis by auto
          qed
          thus ?thesis by simp
        qed
        also have \<open>\<forall> f. f \<in>  M \<longrightarrow> Im (\<langle> h - k | f \<rangle>) = 0\<close>
        proof-
          have  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re (\<langle> h - k | (Complex 0 (-1)) *\<^sub>C f \<rangle>) = 0\<close>
            using assms calculation is_subspace.smult_closed by blast
          hence  \<open>\<forall> f. f \<in>  M \<longrightarrow> Re ( (Complex 0 (-1))*(\<langle> h - k | f \<rangle>) ) = 0\<close>
            by simp
          thus ?thesis 
            using Complex_eq_neg_1 Re_i_times cinner_scaleC_right complex_of_real_def by auto
        qed
        ultimately have \<open>\<forall> f. f \<in>  M \<longrightarrow> (\<langle> h - k | f \<rangle>) = 0\<close>
          by (simp add: complex_eq_iff)
        thus ?thesis 
          by (simp add: \<open>f \<in>  M\<close>)
      qed
      thus ?thesis 
        by (simp add: is_orthogonal_def ortho.rep_eq orthogonal_complement_def)
    qed
    ultimately show ?thesis 
      by simp
  qed
  also have  \<open>h - k \<in> orthogonal_complement M \<and> k \<in>  M 
     \<Longrightarrow> ( is_arg_min_on (\<lambda> x. dist x h) M k )\<close>
  proof-
    assume \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close>
    hence \<open>h - k \<in> orthogonal_complement M\<close>
      by blast
    have \<open>k \<in> M\<close> using \<open>h - k \<in> orthogonal_complement M \<and> k \<in>  M\<close>
      by blast
    have \<open>f \<in> M \<Longrightarrow> dist h k \<le> dist h f \<close> for f
    proof-
      assume \<open>f \<in>  M\<close>
      hence \<open>h - k \<bottom> k - f\<close>
        by (smt \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close> cinner_diff_right eq_iff_diff_eq_0 is_orthogonal_def mem_Collect_eq orthogonal_complement_def)
      have \<open>(\<parallel> h - f \<parallel>)^2 = (\<parallel> (h - k) + (k - f) \<parallel>)^2\<close>
        by simp
      also have \<open>... = (\<parallel> h - k \<parallel>)^2 + (\<parallel> k - f \<parallel>)^2\<close>
        using  \<open>h - k \<bottom> k - f\<close> PythagoreanId 
        using is_orthogonal_def by blast
      also have \<open>... \<ge> (\<parallel> h - k \<parallel>)^2\<close>
        by simp
      finally have \<open>(\<parallel>h - k\<parallel>)\<^sup>2 \<le> (\<parallel>h - f\<parallel>)\<^sup>2 \<close>
        by blast
      hence \<open>(\<parallel>h - k\<parallel>) \<le> (\<parallel>h - f\<parallel>)\<close>
        using norm_ge_zero power2_le_imp_le by blast
      thus ?thesis 
        by (simp add: dist_norm)
    qed
    thus ?thesis 
      by (simp add: \<open>h - k \<in> orthogonal_complement M \<and> k \<in> M\<close> dist_commute is_arg_min_linorder is_arg_min_on_def)
  qed
  ultimately show ?thesis by blast
qed

lemma SubspaceConvex:
  \<open>is_subspace M \<Longrightarrow> convex M\<close> 
proof-
  assume \<open>is_subspace M\<close>
  hence \<open>\<forall>x\<in>M. \<forall>y\<in> M. \<forall>u. \<forall>v. u *\<^sub>C x + v *\<^sub>C y \<in>  M\<close>
    by (metis is_subspace.additive_closed is_subspace.smult_closed)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u::real. \<forall>v::real. u *\<^sub>R x + v *\<^sub>R y \<in> M\<close>
    by (simp add: scaleR_scaleC)
  hence \<open>\<forall>x\<in>M. \<forall>y\<in>M. \<forall>u\<ge>0. \<forall>v\<ge>0. u + v = 1 \<longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in>M\<close>
    by blast
  thus ?thesis using convex_def by blast
qed

corollary ExistenceUniquenessProj:
  fixes M :: \<open>('a::{complex_inner, complete_space}) set\<close> 
  assumes \<open>is_subspace M\<close>
  shows  \<open>\<forall> h. \<exists>! k. (h - k) \<in> orthogonal_complement M \<and> k \<in> M\<close>
proof-  
  have \<open>0 \<in> M\<close> 
    using  \<open>is_subspace M\<close>
    by (simp add: is_subspace_contains_0)
  hence \<open>M \<noteq> {}\<close> by blast
  have \<open>closed  M\<close>
    using  \<open>is_subspace M\<close>
    by (simp add: is_subspace.closed)
  have \<open>convex  M\<close>
    using  \<open>is_subspace M\<close>
    by (simp add: SubspaceConvex)
  have \<open>\<forall> h. \<exists>! k.  is_arg_min_on (\<lambda> x. dist x h) M k\<close>
    by (simp add: ExistenceUniquenessMinDist \<open>closed M\<close> \<open>convex M\<close> \<open>M \<noteq> {}\<close>)
  thus ?thesis
    using DistMinOrtho 
    by (smt Collect_cong Collect_empty_eq_bot ExistenceUniquenessMinDist \<open>M \<noteq> {}\<close> \<open>closed M\<close> \<open>convex M\<close> assms bot_set_def empty_Collect_eq empty_Diff insert_Diff1 insert_compr is_subspace_contains_0 is_subspace_orthog orthogonal_complement_def set_diff_eq singleton_conv2 someI_ex)
qed

(* Definition of projection onto the subspace M *)
definition proj :: \<open>('a::{complex_inner, complete_space}) set \<Rightarrow> (('a::{complex_inner, complete_space}) \<Rightarrow> ('a::{complex_inner, complete_space}))\<close> where (* using 'a::something set, 'a\<Rightarrow>'a *)
  \<open>proj \<equiv> \<lambda> M. \<lambda> h. THE k. ((h - k) \<in> orthogonal_complement M \<and> k \<in>  M)\<close>

lemma proj_intro1:
  \<open>is_subspace M  \<Longrightarrow> h - (proj M) h \<in> orthogonal_complement M\<close>
  by (metis (no_types, lifting) Complex_L2.proj_def ExistenceUniquenessProj theI)

lemma proj_intro2:
  \<open>is_subspace M  \<Longrightarrow> (proj M) h \<in> M\<close>
  by (metis (no_types, lifting) Complex_L2.proj_def ExistenceUniquenessProj theI)

lemma proj_uniq:
  assumes  \<open>is_subspace M\<close> and \<open>h - x \<in> orthogonal_complement M\<close> and \<open>x \<in> M\<close>
    shows \<open>(proj M) h = x\<close>
  by (smt ExistenceUniquenessProj add.commute assms(1) assms(2) assms(3) orthogonal_complement_def proj_intro1 proj_intro2 uminus_add_conv_diff)

lemma proj_fixed_points:                         
  \<open>is_subspace M  \<Longrightarrow> x \<in> M \<Longrightarrow> (proj M) x = x\<close>
  by (simp add: is_subspace_contains_0 proj_uniq)


term bounded_clinear
(* Bounded operator*)
(* TODO: Use bounded_clinear, and clinear *)

find_theorems "open ?S" "open (?f -` ?S)"
find_theorems "?r \<longlonglongrightarrow> ?L"  "(\<lambda> n. ?f (?r n)) \<longlonglongrightarrow> ?f ?L"
find_theorems isCont "_ \<longlonglongrightarrow> _"

thm continuous_at_sequentiallyI

lemma bounded_linear_continuous:
  assumes \<open>bounded_clinear f\<close> 
  shows "isCont f x"
  by (simp add: assms bounded_clinear.bounded_linear linear_continuous_at)

(*
lemma bounded_linear_continuous:
  \<open>bounded_linear_op f  \<Longrightarrow> r \<longlonglongrightarrow> L  \<Longrightarrow> (\<lambda> n. f (r n)) \<longlonglongrightarrow> f L\<close> 
*)

(*
(* TODO state on sets, or remove *)
lemma linear_set_span:
  \<open>is_subspace A \<Longrightarrow> span A = A\<close> for A :: \<open>('a::{complex_inner, complete_space}) set\<close>
proof-                
  assume \<open>closed_linear_set A\<close>
  have \<open>x \<in> A \<Longrightarrow> x \<in> subspace_as_set (span A)\<close> for x
    using Complex_L2.span_superset by auto
  moreover have \<open>x \<in> subspace_as_set (span A) \<Longrightarrow> x \<in> A\<close> for x
  proof-
    assume \<open>x \<in> subspace_as_set (span A)\<close>
    hence \<open>\<forall> S \<in> {S. A \<subseteq> subspace_as_set S}. x \<in> subspace_as_set S\<close>
      by (metis (mono_tags, lifting)  Complex_L2.span_def INT_iff Inf_subspace.rep_eq)
    obtain S where \<open>subspace_as_set S = A\<close> 
      using \<open>closed_linear_set A\<close> linear_set_as_subspace by auto
    show ?thesis 
      using \<open>\<forall>S\<in>{S. A \<subseteq> subspace_as_set S}. x \<in> subspace_as_set S\<close> \<open>subspace_as_set S = A\<close> by auto
  qed
  ultimately show ?thesis by blast
qed
*)

theorem projPropertiesB:
  \<open>is_subspace M  \<Longrightarrow> \<parallel> (proj M) h \<parallel> \<le> \<parallel> h \<parallel>\<close>
  (* Reference: Theorem 2.7 in conway2013course *)
proof-
  assume \<open>is_subspace M\<close>
  hence \<open>h - (proj M) h \<in> orthogonal_complement M\<close> 
    by (simp add: proj_intro1)
  hence \<open>\<forall> k \<in>  M.  (h - (proj M) h) \<bottom> k\<close>
    by (simp add: ortho.rep_eq orthogonal_complement_def)
  hence \<open>\<forall> k \<in> M. \<langle>  h - (proj M) h | k \<rangle> = 0\<close>
    using is_orthogonal_def by blast
  also have \<open>(proj M) h \<in>  M\<close>
    using  \<open>is_subspace M\<close>
    by (simp add: proj_intro2)
  ultimately have \<open>\<langle>  h - (proj M) h | (proj M) h \<rangle> = 0\<close>
    by auto
  hence \<open>(\<parallel> (proj M) h \<parallel>)^2 + (\<parallel> h - (proj M) h \<parallel>)^2 = (\<parallel> h \<parallel>)^2\<close>
    using PythagoreanId by fastforce
  hence \<open>(\<parallel> (proj M) h \<parallel>)^2 \<le> (\<parallel> h \<parallel>)^2\<close>
    by (smt zero_le_power2)    
  thus ?thesis 
    using norm_ge_zero power2_le_imp_le by blast
qed

theorem projPropertiesA:
  \<open>is_subspace M \<Longrightarrow> bounded_clinear (proj M)\<close> 
  (* Reference: Theorem 2.7 (version) in conway2013course *)
proof-
  assume \<open>is_subspace M\<close>
  hence \<open>is_subspace (orthogonal_complement M)\<close>
    by simp
  have \<open>(proj M) (c *\<^sub>C x) = c *\<^sub>C ((proj M) x)\<close> for x c
  proof-                   
    have  \<open>\<forall> x.  ((proj M) x) \<in> M\<close>
      using  \<open>is_subspace M\<close>
      by (simp add: proj_intro2)
    hence  \<open>\<forall> x. \<forall> t.  t *\<^sub>C ((proj M) x) \<in> M\<close>
      using  \<open>is_subspace M\<close> is_subspace.smult_closed subspace_to_set by fastforce
    have  \<open>\<forall> x. \<forall> t. ((proj M) (t *\<^sub>C x)) \<in>  M\<close>
      using  \<open>is_subspace M\<close>
      by (simp add: proj_intro2)
    have \<open>\<forall> x. \<forall> t. (t *\<^sub>C x) - (proj M) (t *\<^sub>C x) \<in> orthogonal_complement M\<close>
      using  \<open>is_subspace M\<close>
      by (simp add: proj_intro1)
    have \<open>\<forall> x. x - (proj M) x \<in> orthogonal_complement M\<close>
      using  \<open>is_subspace M\<close>
      by (simp add: proj_intro1)
    hence \<open>\<forall> x. \<forall> t. t *\<^sub>C (x - (proj M) x) \<in> orthogonal_complement M\<close>
      using  \<open>is_subspace (orthogonal_complement M)\<close> is_subspace.smult_closed subspace_to_set by fastforce
    hence \<open>\<forall> x. \<forall> t.  t *\<^sub>C x - t *\<^sub>C ((proj M) x) \<in> orthogonal_complement M\<close>
      by (simp add: complex_vector.scale_right_diff_distrib)
    from  \<open>\<forall> x. \<forall> t. t *\<^sub>C x - (proj M) (t *\<^sub>C x) \<in> orthogonal_complement M\<close>
      \<open>\<forall> x. \<forall> t.  t *\<^sub>C x - t *\<^sub>C ((proj M) x) \<in> orthogonal_complement M\<close>
    have \<open>\<forall> x. \<forall> t. (t *\<^sub>C x - t *\<^sub>C ((proj M) x)) - (t *\<^sub>C x - (proj M) (t *\<^sub>C x)) \<in> orthogonal_complement M\<close>
      by (metis \<open>\<forall>x t. t *\<^sub>C proj M x \<in> M\<close> \<open>is_subspace (orthogonal_complement M)\<close> \<open>is_subspace M\<close> cancel_comm_monoid_add_class.diff_cancel is_subspace_contains_0 proj_uniq)

    hence \<open>\<forall> x. \<forall> t. (proj M) (t *\<^sub>C x) - t *\<^sub>C ((proj M) x) \<in> orthogonal_complement M\<close>
      by simp
    moreover have \<open>\<forall> x. \<forall> t. (proj M) (t *\<^sub>C x) - t *\<^sub>C ((proj M) x) \<in>  M\<close>         
      using  \<open>\<forall> x. \<forall> t.  t *\<^sub>C ((proj M) x) \<in>  M\<close>  \<open>\<forall> x. \<forall> t. ((proj M) (t *\<^sub>C x)) \<in>  M\<close>
      by (metis \<open>\<forall>x t. t *\<^sub>C x - t *\<^sub>C proj M x \<in> orthogonal_complement M\<close> \<open>is_subspace M\<close> cancel_comm_monoid_add_class.diff_cancel is_subspace_contains_0 proj_uniq)
    ultimately have  \<open>\<forall> x. \<forall> t. (proj M) (t *\<^sub>C x) = t *\<^sub>C ((proj M) x)\<close>
      by (simp add: \<open>\<forall>x t. t *\<^sub>C proj M x \<in> M\<close> \<open>\<forall>x t. t *\<^sub>C x - t *\<^sub>C proj M x \<in> orthogonal_complement M\<close> \<open>is_subspace M\<close> proj_uniq)
    thus ?thesis
      by simp
  qed
  moreover have \<open>Modules.additive (proj M)\<close>
  proof-                   
    have  \<open>\<forall> x.  ((proj M) x) \<in>  M\<close>
      using \<open>is_subspace M\<close>
      by (simp add: proj_intro2) 
    hence  \<open>\<forall> x. \<forall> y. ((proj M) x) + ((proj M) y) \<in>  M\<close>
      by (simp add: \<open>is_subspace M\<close> is_subspace.additive_closed)
    have  \<open>\<forall> x. \<forall> y. ((proj M) (x + y)) \<in> M\<close>
      using \<open>is_subspace M\<close>
      by (simp add: proj_intro2)
    have  \<open>\<forall> x. \<forall> y. (x + y) - (proj M) (x + y) \<in> orthogonal_complement M\<close>
      using \<open>is_subspace M\<close>
      by (simp add: proj_intro1)
    have \<open>\<forall> x. x - (proj M) x \<in> orthogonal_complement M\<close>
      using \<open>is_subspace M\<close>
      by (simp add: proj_intro1)
    hence \<open>\<forall> x. \<forall> y. (x + y) - ((proj M) x + (proj M) y) \<in> orthogonal_complement M\<close>
      by (simp add: \<open>is_subspace (orthogonal_complement M)\<close> add_diff_add is_subspace.additive_closed)
    from  \<open>\<forall> x. \<forall> y. (x + y) - ((proj M) x + (proj M) y) \<in>  orthogonal_complement M\<close>
      \<open>\<forall> x. \<forall> y. (x + y) - ((proj M) (x + y)) \<in>  orthogonal_complement M\<close>
    have  \<open>\<forall> x. \<forall> y. ( (x + y) - ((proj M) x + (proj M) y) ) - ( (x + y) - ((proj M) (x + y)) ) \<in>  orthogonal_complement M\<close>
      by (metis \<open>\<forall>x y. proj M x + proj M y \<in> M\<close> \<open>is_subspace M\<close> cancel_comm_monoid_add_class.diff_cancel proj_fixed_points proj_uniq)
    hence \<open>\<forall> x. \<forall> y. (proj M) (x + y) -  ((proj M) x + (proj M) y) \<in> orthogonal_complement M\<close>
      by (metis (no_types, lifting) add_diff_cancel_left diff_minus_eq_add uminus_add_conv_diff)
    moreover have \<open>\<forall> x. \<forall> y. (proj M) (x + y) -  ((proj M) x + (proj M) y) \<in> M\<close>       
      by (metis \<open>\<forall>x y. proj M x + proj M y \<in> M\<close> \<open>\<forall>x y. x + y - (proj M x + proj M y) \<in> orthogonal_complement M\<close> \<open>is_subspace M\<close> cancel_comm_monoid_add_class.diff_cancel is_subspace_contains_0 proj_uniq)
    ultimately have \<open>\<forall> x. \<forall> y. (proj M) (x + y) - ( ((proj M) x) + ((proj M) y) ) = 0\<close>
      using \<open>\<forall>x y. proj M x + proj M y \<in> M\<close> \<open>\<forall>x y. x + y - (proj M x + proj M y) \<in> orthogonal_complement M\<close> \<open>is_subspace M\<close> proj_uniq by fastforce
    hence  \<open>\<forall> x. \<forall> y. (proj M) (x + y) =  ((proj M) x) + ((proj M) y)\<close>
      by auto
    thus ?thesis
      by (simp add: Modules.additive_def)
  qed

  ultimately have \<open>clinear (proj M)\<close> 
    by (simp add: Modules.additive_def clinearI)
  moreover have \<open>bounded_clinear_axioms (proj M)\<close>
    using projPropertiesB  \<open>is_subspace M\<close> 
    unfolding bounded_clinear_axioms_def
    by (metis mult.commute mult.left_neutral)
  ultimately show ?thesis
    using  bounded_clinear_def
    by auto 
qed


theorem projPropertiesC:
  \<open>is_subspace M \<Longrightarrow> (proj M) \<circ> (proj M) = proj M\<close>
  (* Reference: Theorem 2.7 in conway2013course *)
  using proj_fixed_points proj_intro2 by fastforce

(* Kernet of an operator *)
(* TODO define on sets *)
definition ker_op :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 'a set\<close> where
  \<open>ker_op \<equiv> \<lambda> f. {x. f x = 0}\<close>

(* TODO: remove (but keep some subproofs, e.g. is_subspace (ker_op S?) )  *)
lemma ker_op_lin:
  \<open>bounded_clinear f \<Longrightarrow> is_subspace (ker_op f)\<close>
proof-
  assume \<open>bounded_clinear f\<close>
  have \<open>x \<in>  {x. f x = 0} \<Longrightarrow> t *\<^sub>C x \<in> {x. f x = 0}\<close> for x t
  proof-
    assume \<open>x \<in>  {x. f x = 0}\<close>
    hence \<open>f x = 0\<close>
      by blast
    hence  \<open>f  (t *\<^sub>C x) = 0\<close>
      by (simp add: \<open>bounded_clinear f\<close> bounded_clinear.clinear clinear.scaleC)
    hence \<open> t *\<^sub>C x \<in> {x. f x = 0}\<close>
      by simp
    show ?thesis 
      using \<open>t *\<^sub>C x \<in> {x. f x = 0}\<close> by auto
  qed

  have \<open>x \<in> {x. f x = 0} \<Longrightarrow> y \<in> {x. f x = 0} \<Longrightarrow> x + y \<in> {x. f x = 0}\<close> for x y
  proof-
    assume \<open>x \<in>  {x. f x = 0}\<close> and \<open>y \<in> {x. f x = 0}\<close>
    have \<open>f x = 0\<close> 
      using \<open>x \<in> {x. f x = 0}\<close> by auto
    have  \<open>f y = 0\<close>
      using \<open>y \<in> {x. f x = 0}\<close> by auto
    have  \<open>f (x + y) = f x + f y\<close>
      using \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def clinear_def
      using Modules.additive_def
      by blast
    hence  \<open>f (x + y) = 0\<close>
      by (simp add: \<open>f x = 0\<close> \<open>f y = 0\<close>)
    hence \<open>x + y \<in>  {x. f x = 0}\<close>
      by simp
    show ?thesis 
      using \<open>x + y \<in> {x. f x = 0}\<close> by auto
  qed

  have \<open>t \<in> {x. f x = 0} \<Longrightarrow> c *\<^sub>C t \<in> {x. f x = 0}\<close> for t c
    using \<open>\<And>x t. x \<in> {x. f x = 0} \<Longrightarrow> t *\<^sub>C x \<in> {x. f x = 0}\<close> by auto
  moreover have \<open>u \<in> {x. f x = 0} \<Longrightarrow> v \<in> {x. f x = 0} \<Longrightarrow> u + v \<in> {x. f x = 0}\<close> for u v
    using \<open>\<And>y x. \<lbrakk>x \<in> {x. f x = 0}; y \<in> {x. f x = 0}\<rbrakk> \<Longrightarrow> x + y \<in> {x. f x = 0}\<close> by auto

  moreover have \<open>closed {x. f x = 0}\<close>
  proof-
    have \<open>r \<longlonglongrightarrow> L \<Longrightarrow> \<forall> n. r n \<in> {x. f x = 0} \<Longrightarrow> L \<in> {x. f x = 0}\<close> for r and  L 
    proof-
      assume \<open>r \<longlonglongrightarrow> L\<close>
      assume \<open>\<forall> n. r n \<in> {x. f x = 0}\<close>
      hence \<open>\<forall> n. f (r n) = 0\<close>
        by simp
      from \<open>bounded_clinear f\<close> 
      have \<open>(\<lambda> n. f (r n)) \<longlonglongrightarrow> f L\<close>
        using \<open>r \<longlonglongrightarrow> L\<close> bounded_linear_continuous continuous_at_sequentiallyI
        unfolding isCont_def
        using tendsto_compose by fastforce

      hence \<open>(\<lambda> n. 0) \<longlonglongrightarrow> f L\<close>
        using \<open>\<forall> n. f (r n) = 0\<close> by simp        
      hence \<open>f L = 0\<close>
        using limI by fastforce
      thus ?thesis by blast
    qed
    thus ?thesis 
      using closed_sequential_limits by blast
  qed
  ultimately show ?thesis
    using  \<open>bounded_clinear f\<close> bounded_clinear_def clinear.scaleC complex_vector.scale_eq_0_iff is_subspace.intro ker_op_def
      bounded_clinear.clinear 
    by (smt Collect_cong mem_Collect_eq)
qed


theorem projPropertiesD:
  \<open>is_subspace M \<Longrightarrow> ker_op  (proj M) = orthogonal_complement M\<close>
  (* Reference: Theorem 2.7 in conway2013course *)
proof-
  assume \<open>is_subspace M\<close> 

  have \<open>x \<in> orthogonal_complement M \<Longrightarrow> x \<in>  (ker_op  (proj M))\<close> for x
  proof-
    assume \<open>x \<in> orthogonal_complement M\<close>
    hence \<open>(proj M) x = 0\<close>
      using  \<open>is_subspace M\<close>
      by (metis ExistenceUniquenessProj diff_zero is_subspace_contains_0  proj_intro1 proj_intro2)
    hence \<open>x \<in> (ker_op  (proj M))\<close>
      using ker_op_lin projPropertiesA
      by (simp add: ker_op_def)
    thus ?thesis
      by simp
  qed

  moreover have \<open>x \<in> ker_op  (proj M) \<Longrightarrow> x \<in> orthogonal_complement M\<close> for x
  proof-
    assume \<open>x \<in> ker_op  (proj M)\<close>
    hence  \<open>x \<in> {y.  (proj M) x = 0}\<close>
      using ker_op_lin  projPropertiesA \<open>is_subspace M\<close>
      by (simp add: ker_op_def)

    hence \<open>(proj M) x = 0\<close>
      by (metis (mono_tags, lifting) mem_Collect_eq)
    hence  \<open>x \<in> orthogonal_complement M\<close>
      using \<open>is_subspace M\<close>
      by (metis  diff_zero proj_intro1)   
    thus ?thesis
      by simp
  qed

  ultimately have \<open>orthogonal_complement M = ker_op  (proj M)\<close>         
    by blast
  thus ?thesis 
    using subspace_to_set_inject by blast
qed


(* Range of an operator *)
(* TODO using sets *)
definition ran_op :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> 'b set\<close> where
  \<open>ran_op \<equiv> \<lambda> f. {x. \<exists> y. f y = x}\<close>

lemma ran_op_lin:
  \<open>bounded_clinear f \<Longrightarrow> is_subspace ( closure (ran_op f) )\<close>
  sorry

theorem projPropertiesE:
  \<open>is_subspace M \<Longrightarrow> ran_op  (proj M) = M\<close>
  (* TODO using sets *)
  (* Reference: Theorem 2.7 in conway2013course *)
  sorry

lemma pre_ortho_twice: "is_subspace M \<Longrightarrow> M \<subseteq> orthogonal_complement (orthogonal_complement M)" 
  sorry
(*
proof-
  have \<open>x \<in> subspace_as_set M \<Longrightarrow> x \<in> subspace_as_set ( ortho (ortho M) )\<close> for x
  proof-
    assume \<open>x \<in> subspace_as_set M\<close>
    hence \<open>\<forall> y \<in> subspace_as_set (ortho M). x \<bottom> y\<close>
      by (simp add: ortho.rep_eq orthogonal_comm orthogonal_complement_def)
    hence \<open>x \<in> subspace_as_set (ortho (ortho M))\<close>
      by (simp add: ortho.rep_eq orthogonal_complement_def)
    thus ?thesis by blast
  qed
  thus ?thesis 
    by (simp add: less_eq_subspace.rep_eq subsetI)
qed
*)

lemma ProjOntoOrtho:
  \<open>is_subspace M \<Longrightarrow> id -  proj M = proj (orthogonal_complement M) \<close>
  (* Reference: Exercice 2 (section 2, chapter I) in conway2013course *)
proof-
  assume \<open>is_subspace M\<close>
  have   \<open> (id -  proj M) x = (proj (orthogonal_complement M)) x \<close> for x
  proof-
    have \<open>x - (proj M) x \<in> orthogonal_complement M\<close>
      using \<open>is_subspace M\<close> proj_intro1 by auto
    hence \<open>(id -  proj M) x \<in> orthogonal_complement M\<close>
      by simp
    have \<open>(proj M) x \<in>  M\<close> 
      by (simp add: \<open>is_subspace M\<close> proj_intro2)
    hence  \<open>x - (id -  proj M) x \<in>  M\<close>
      by simp
    hence \<open>(proj M) x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      using pre_ortho_twice  \<open>is_subspace M\<close>  \<open>(proj M) x \<in>  M\<close> by auto 
    hence  \<open>x - (id -  proj M) x \<in>  (orthogonal_complement (orthogonal_complement M))\<close>
      by simp
    thus ?thesis
      using ExistenceUniquenessProj proj_intro1 proj_intro2 
      by (metis \<open>(id - proj M) x \<in> orthogonal_complement M\<close> \<open>is_subspace M\<close> diff_0 diff_0_right id_apply is_subspace_orthog minus_diff_eq proj_uniq)
  qed
  thus ?thesis by blast
qed

corollary ortho_twice[simp]: "orthogonal_complement (orthogonal_complement M) = M"
  sorry
    (* Reference: Corollary 2.8 in conway2013course *)
(*
proof-
  have \<open>ortho (ortho M) = ker_op (proj (ortho M))\<close>
    by (metis  projPropertiesD)
  also have \<open>... = ker_op ( IdV - (proj M) )\<close>
    by (simp add: ProjOntoOrtho)
  also have \<open>... = M\<close>
  proof-
    have \<open>x \<in> subspace_as_set M \<Longrightarrow> x \<in> subspace_as_set ( ker_op ( IdV - (proj M) ) )\<close> for x
    proof-
      assume \<open>x \<in> subspace_as_set M\<close>
      hence \<open>(proj M) x = x\<close>
        using proj_fixed_points by blast
      hence \<open>(IdV - (proj M)) x = 0\<close> 
        by (simp add: IdV_def)
      hence \<open>x \<in> {v. (IdV - (proj M)) v = 0}\<close>
        by simp
      hence \<open>x \<in> subspace_as_set (span {v. (IdV - (proj M)) v = 0})\<close>
        using span_superset 
        by fastforce
      hence \<open>x \<in> subspace_as_set ( ker_op ( IdV - (proj M) ) )\<close> 
        by (metis  ker_op_def)
      thus ?thesis 
        by simp                  
    qed
    moreover have \<open>x \<in> subspace_as_set ( ker_op ( IdV - (proj M) ) ) \<Longrightarrow> x \<in> subspace_as_set M\<close> for x
    proof-
      assume \<open>x \<in> subspace_as_set ( ker_op ( IdV - (proj M) ) )\<close>
      hence \<open>(IdV - (proj M)) x = 0\<close>
        by (metis IdV_def proj_fixed_points ProjOntoOrtho \<open>ker_op (proj (ortho M)) = ker_op (IdV - proj M)\<close> diff_right_commute  eq_iff_diff_eq_0 minus_apply projPropertiesD)
      hence \<open>(proj M) x = x\<close>
        by (metis IdV_def add.inverse_neutral diff_0 diff_eq_diff_eq minus_apply)
      hence \<open>(proj M) x \<in> subspace_as_set M\<close> 
        using projPropertiesE
        by (metis (mono_tags, lifting) Abs_subspace_cases Abs_subspace_inverse  Complex_L2.span_superset mem_Collect_eq ran_op_def subsetCE)
      hence \<open>x \<in> subspace_as_set M\<close>
        using  \<open>(proj M) x = x\<close> 
        by simp
      thus ?thesis by blast
    qed
    ultimately have \<open>x \<in> subspace_as_set M \<longleftrightarrow> x \<in> subspace_as_set ( ker_op ( IdV - (proj M) ) )\<close> for x
      by blast
    hence \<open>subspace_as_set ( ker_op ( IdV - (proj M) ) ) = subspace_as_set M\<close>
      by blast
    thus ?thesis 
      using subspace_to_set_inject by auto
  qed     
  finally show ?thesis by blast
qed
*)

(* TODO as sets, but keep this one as corollary! *)
lemma ortho_leq[simp]: "ortho A \<le> ortho B \<longleftrightarrow> A \<ge> B"
proof 
  show d1: "B \<le> A \<Longrightarrow> ortho A \<le> ortho B" for A B :: "'a subspace"
  proof-
    assume "B \<le> A"
    hence \<open>subspace_as_set B \<subseteq> subspace_as_set A\<close>
      using less_eq_subspace.rep_eq by auto
    hence \<open>x \<in> subspace_as_set (ortho A) \<Longrightarrow> x \<in> subspace_as_set (ortho B)\<close> for x
    proof-
      assume \<open>x \<in> subspace_as_set (ortho A)\<close>
      hence \<open>\<forall> y \<in> subspace_as_set A. x \<bottom> y\<close> 
        by (simp add: ortho.rep_eq orthogonal_complement_def)
      hence \<open>\<forall> y \<in> subspace_as_set B. x \<bottom> y\<close> 
        using  \<open>subspace_as_set B \<subseteq> subspace_as_set A\<close> 
        by (simp add: subset_eq)
      thus ?thesis
        using ortho.rep_eq orthogonal_complement_def by fastforce
    qed
    hence \<open>subspace_as_set (ortho A) \<le> subspace_as_set (ortho B)\<close>
      by blast
    show ?thesis 
      by (simp add: \<open>subspace_as_set (ortho A) \<subseteq> subspace_as_set (ortho B)\<close> less_eq_subspace.rep_eq)
  qed
  show "ortho A \<le> ortho B \<Longrightarrow> B \<le> A"
    apply (subst ortho_twice[symmetric, of A])
    apply (subst ortho_twice[symmetric, of B])
    by (rule d1)
qed

lemma ortho_top[simp]: "ortho top = bot"
  apply (rule le_bot)
  apply (subst ortho_twice[symmetric, of bot])
  apply (subst ortho_leq)
  by simp

lemma ortho_bot[simp]: "ortho bot = top"
  apply (rule top_le)
  apply (subst ortho_twice[symmetric, of top])
  apply (subst ortho_leq)
  by simp


corollary orthogonal_complement_twice:
  fixes M :: "('a vector) set" 
  assumes "is_subspace M"
  shows "orthogonal_complement (orthogonal_complement M) = M"
  by (metis Abs_subspace_inverse assms mem_Collect_eq ortho.rep_eq ortho_twice)

corollary orthogonal_complement_is_subspace:
  assumes "is_subspace M"
  shows "is_subspace (orthogonal_complement M)"
  by (simp add: assms)

corollary "subspace_as_set (ortho M) = orthogonal_complement (subspace_as_set M)"
  using Complex_L2.ortho.rep_eq by auto


end

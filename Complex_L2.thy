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

typedef 'a ell2 = "{x::'a\<Rightarrow>complex. has_ell2_norm x}"
  unfolding has_ell2_norm_def by (rule exI[of _ "\<lambda>_.0"], auto)
setup_lifting type_definition_ell2
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
    (* TODO: doesn't work in Isabelle2019. Probably best to be just redone in nice Isar style *)
  unfolding ell2_norm_def L2_set_def o_def apply (subst continuous_at_Sup_mono)
  using monoI real_sqrt_le_mono apply blast
  using continuous_at_split isCont_real_sqrt apply blast
  using assms unfolding has_ell2_norm_def by (auto simp: image_image)

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
    by (metis image_image)
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



lift_definition ket :: "'a \<Rightarrow> 'a ell2" is "\<lambda>x y. if x=y then 1 else 0"
  unfolding has_ell2_norm_def bdd_above_def apply simp
  apply (rule exI[of _ 1], rule allI, rule impI)
  by (rule ell2_1)

lemma cSUP_eq_maximum:
  fixes z :: "_::conditionally_complete_lattice"
  assumes "\<exists>x\<in>X. f x = z"
  assumes "\<And>x. x \<in> X \<Longrightarrow> f x \<le> z"
  shows "(SUP x:X. f x) = z"
  by (metis (mono_tags, hide_lams) assms(1) assms(2) cSup_eq_maximum imageE image_eqI)


instantiation ell2 :: (type)complex_vector begin
lift_definition zero_ell2 :: "'a ell2" is "\<lambda>_. 0" by (auto simp: has_ell2_norm_def)
lift_definition uminus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2" is uminus by (simp add: has_ell2_norm_def)
lift_definition plus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>f g x. f x + g x"
  by (rule ell2_norm_triangle) 
lift_definition minus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>f g x. f x - g x"
  apply (subst ab_group_add_class.ab_diff_conv_add_uminus)
  apply (rule ell2_norm_triangle) 
   apply auto by (simp add: has_ell2_norm_def)
lift_definition scaleR_ell2 :: "real \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>r f x. complex_of_real r * f x"
  by (rule ell2_norm_smult)
lift_definition scaleC_ell2 :: "complex \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>c f x. c * f x"
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


instantiation ell2 :: (type)complex_normed_vector begin
lift_definition norm_ell2 :: "'a ell2 \<Rightarrow> real" is ell2_norm .
definition "dist x y = norm (x - y)" for x y::"'a ell2"
definition "sgn x = x /\<^sub>R norm x" for x::"'a ell2"
definition "uniformity = (INF e:{0<..}. principal {(x::'a ell2, y). norm (x - y) < e})"
definition "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e:{0<..}. principal {(x, y). norm (x - y) < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "'a ell2 set"
instance apply intro_classes
  unfolding dist_ell2_def sgn_ell2_def uniformity_ell2_def open_ell2_def apply simp_all
     apply transfer apply (fact ell2_norm_0)
    apply transfer apply (fact ell2_norm_triangle)
   apply transfer apply (subst ell2_norm_smult) apply (simp_all add: abs_complex_def)[2]
  apply transfer by (simp add: ell2_norm_smult(2)) 
end


instantiation ell2 :: (type) complex_inner begin
lift_definition cinner_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> complex" is 
  "\<lambda>x y. infsetsum (\<lambda>i. (cnj (x i) * y i)) UNIV" .
instance
proof standard
  fix x y z :: "'a ell2" fix c :: complex
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
      using sum 
        apply simp
       apply (simp add: sum)
      by (simp add: less_eq_complex_def)
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
        using le_less less_eq_complex_def by fastforce

      also have "\<dots> = (\<Sum>\<^sub>ai\<in>{i}. cnj (x i) * x i)" by auto
      also have "\<dots> \<le> (\<Sum>\<^sub>ai. cnj (x i) * x i)"
        apply (rule infsetsum_subset_complex)
          apply (fact cmod_x2)
         apply simp
        by (simp add: less_eq_complex_def)

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
      apply (subst infsetsum_cmod) using sum 
        apply simp 
       apply (simp add: less_eq_complex_def)
      by auto

    finally show "ell2_norm x = sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i))" by assumption
  qed
qed
end

lemma norm_ell2_component: "norm (Rep_ell2 x i) \<le> norm x"
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

lemma Cauchy_ell2_component: 
  fixes X
  defines "x i == Rep_ell2 (X i)"
  shows "Cauchy X \<Longrightarrow> Cauchy (\<lambda>i. x i j)"
proof -
  assume "Cauchy X"
  have "dist (x i j) (x i' j) \<le> dist (X i) (X i')" for i i'
  proof -
    have "dist (X i) (X i') = norm (X i - X i')"
      unfolding dist_norm by simp
    also have "norm (X i - X i') \<ge> norm (Rep_ell2 (X i - X i') j)"
      by (rule norm_ell2_component)
    also have "Rep_ell2 (X i - X i') j = x i j - x i' j"
      unfolding x_def
      by (metis add_implies_diff diff_add_cancel plus_ell2.rep_eq) 
    also have "norm (x i j - x i' j) = dist (x i j) (x i' j)"
      unfolding dist_norm by simp
    finally show ?thesis by assumption
  qed
  then show ?thesis
    unfolding Cauchy_def
    using \<open>Cauchy X\<close> unfolding Cauchy_def
    by (meson le_less_trans) 
qed


definition pointwise_convergent_to :: 
  \<open>( nat \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) ) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> where
  \<open>pointwise_convergent_to x l = (\<forall> t::'a. (\<lambda> n. (x n) t ) \<longlonglongrightarrow> l t)\<close>

abbreviation pointwise_convergent_to_abbr :: 
  \<open>( nat \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) ) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>  ("/_/ \<midarrow>pointwise\<rightarrow> /_/") where
  \<open>x \<midarrow>pointwise\<rightarrow> l \<equiv> pointwise_convergent_to x l\<close>

definition pointwise_convergent::\<open>( nat \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) ) \<Rightarrow> bool\<close> where
  \<open>pointwise_convergent x = (\<exists> l. (x \<midarrow>pointwise\<rightarrow> l) )\<close>

lemma has_ell2_norm_explicit:
  \<open>has_ell2_norm f \<longleftrightarrow> ( \<exists> M::real. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod (f x))^2) \<le> M )\<close>
  for f::\<open>'a \<Rightarrow> complex\<close>
proof-
  have \<open>has_ell2_norm f \<Longrightarrow> ( \<exists> M::real. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod (f x))^2) \<le> M )\<close>
    by (simp add: bdd_above_def has_ell2_norm_def)
  moreover have \<open>( \<exists> M::real. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod (f x))^2) \<le> M ) \<Longrightarrow> has_ell2_norm f\<close>
    by (simp add: bdd_above_def has_ell2_norm_def)
  ultimately show ?thesis
    by auto
qed


(* NEW *)
lemma triangIneq_ell2:
  fixes S :: \<open>'a set\<close> and f g :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>finite S\<close>
  shows \<open>sqrt (\<Sum> x\<in>S. (cmod (f x + g x))^2)
   \<le> sqrt (\<Sum> x\<in>S. (cmod (f x))^2) + sqrt (\<Sum> x\<in>S. (cmod (g x))^2)\<close>
  sorry

(* NEW *)
lemma triangIneq_ell2Minus:
  fixes S :: \<open>'a set\<close> and f g :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>finite S\<close>
  shows \<open>sqrt (\<Sum> x\<in>S.  (cmod (f x) )^2) 
   \<le> sqrt (\<Sum> x\<in>S. (cmod (f x - g x))^2) + sqrt (\<Sum> x\<in>S. ( cmod (g x) )^2)\<close>
proof-
  have \<open>sqrt (\<Sum> x\<in>S.  (cmod (f x) )^2) = sqrt (\<Sum> x\<in>S. (cmod ((f x - g x) + g x) )^2)\<close>
    by auto
  hence \<open>... = sqrt (\<Sum> x\<in>S. (cmod ((\<lambda> t. f t - g t) x + g x) )^2)\<close>
    by auto
  hence \<open>... \<le> sqrt (\<Sum> x\<in>S. (cmod ((\<lambda> t. f t - g t) x) )^2)
             + sqrt (\<Sum> x\<in>S. (cmod (g x) )^2)\<close>
    using triangIneq_ell2  \<open>finite S\<close>
    by (metis (no_types) triangIneq_ell2 assms)
  hence \<open>... \<le> sqrt (\<Sum> x\<in>S. (cmod (f x - g x) )^2)
             + sqrt (\<Sum> x\<in>S. (cmod (g x) )^2)\<close>
    by auto
  show ?thesis  
    using \<open>sqrt (\<Sum>x\<in>S. (cmod (f x - g x + g x))\<^sup>2) \<le> sqrt (\<Sum>x\<in>S. (cmod (f x - g x))\<^sup>2) + sqrt (\<Sum>x\<in>S. (cmod (g x))\<^sup>2)\<close> \<open>sqrt (\<Sum>x\<in>S. (cmod (f x))\<^sup>2) = sqrt (\<Sum>x\<in>S. (cmod (f x - g x + g x))\<^sup>2)\<close> by linarith
qed


(* NEW *)
lemma CauchyImplies_ell2Bounded:                         
  fixes a :: \<open>nat \<Rightarrow> ('a \<Rightarrow> complex)\<close>
  assumes \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
    and \<open>\<forall> k::nat. has_ell2_norm (a k)\<close>    
  shows \<open>\<exists> M::real. \<forall> m. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close>
  sorry
(*
proof-
  from  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow>  (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)   \<le> \<epsilon>\<close>
  obtain N::nat where \<open> \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow>  (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)   \<le> (1::real)\<close>
    using less_numeral_extra(1) by blast
  from \<open>\<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow>  (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)   \<le> (1::real)\<close>
  have \<open>\<forall> m \<ge> N.  \<forall> S::'a set. finite S \<longrightarrow>  (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> (1::real)\<close>
    by blast
  have  \<open>m \<ge> N \<Longrightarrow> \<exists> M::real. \<forall> S::'a set. finite S \<longrightarrow>  (\<Sum> x\<in>S. (cmod ((a m) x))^2)  \<le> M\<close>
  proof-
    assume \<open>m \<ge> N\<close>
    have \<open>\<forall> S::'a set. finite S \<longrightarrow>  (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> (1::real)\<close>
      using \<open>N \<le> m\<close> \<open>\<forall>m\<ge>N. \<forall>S. finite S \<longrightarrow> (\<Sum>x\<in>S. (cmod (a m x - a N x))\<^sup>2) \<le> 1\<close> by blast
    hence \<open>\<forall> S::'a set. finite S \<longrightarrow>  sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> (1::real)\<close>
      by simp
    have \<open>has_ell2_norm (a N)\<close>
      by (simp add: assms(2))
    then obtain C::real
      where \<open>\<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( (a N) x ) )^2) \<le> C\<close>
      by (metis assms(2) has_ell2_norm_explicit real_sqrt_le_iff)
    have  \<open>\<forall> S::'a set. finite S \<longrightarrow>  
       sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) ) )^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) + sqrt (\<Sum> x\<in>S. ( cmod ( (a N) x ) )^2)\<close>
    proof-
      have \<open>\<forall> S::'a set. finite S \<longrightarrow>  
       sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) ) )^2) = sqrt (\<Sum> x\<in>S. ( cmod ( (((a m) x) - ((a N) x)) +  ((a N) x) ) )^2)\<close>
        by auto
      moreover have \<open>finite S \<Longrightarrow>  
         sqrt (\<Sum> x\<in>S. ( cmod ( (((a m) x) - ((a N) x)) + ((a N) x) ) )^2) \<le>
         sqrt (\<Sum> x\<in>S. ( cmod ( (((a m) x) - ((a N) x)) ) )^2) +  sqrt (\<Sum> x\<in>S. ( cmod ( (a N) x ) )^2)\<close>
        for S::\<open>'a set\<close>
      proof-
        assume \<open>finite S\<close>
        hence  \<open>sqrt (\<Sum> x\<in>S. ( (cmod (f x + g x)) )^2)
   \<le> sqrt (\<Sum> x\<in>S. ( (cmod (f x)) )^2) + sqrt (\<Sum> x\<in>S. ( (cmod (g x)) )^2)\<close>
          for f g :: \<open>'a \<Rightarrow> complex\<close>
          using triangIneq_ell2 by blast
        hence  \<open>sqrt (\<Sum> x\<in>S. ( (cmod (f x + (a N) x)) )^2)
   \<le> sqrt (\<Sum> x\<in>S. ( (cmod (f x)) )^2) + sqrt (\<Sum> x\<in>S. ( (cmod ((a N) x)) )^2)\<close>
          for f :: \<open>'a \<Rightarrow> complex\<close>           
          by blast
        hence  \<open>sqrt (\<Sum> x\<in>S. ( (cmod ((\<lambda> t::'a. (a m) t - (a N) t) x + (a N) x)) )^2)
   \<le> sqrt (\<Sum> x\<in>S. ( (cmod ((\<lambda> t::'a. (a m) t - (a N) t) x)) )^2) + sqrt (\<Sum> x\<in>S. ( (cmod ((a N) x)) )^2)\<close>
          by fastforce
        hence  \<open>sqrt (\<Sum> x\<in>S. ( (cmod ( ((a m) x - (a N) x)  + (a N) x)) )^2)
   \<le> sqrt (\<Sum> x\<in>S. ( (cmod ( (a m) x - (a N) x )) )^2) + sqrt (\<Sum> x\<in>S. ( (cmod ((a N) x)) )^2)\<close>
          by simp
        thus ?thesis
          by blast 
      qed
      ultimately show ?thesis
        by presburger 
    qed
    hence  \<open>\<forall> S::'a set. finite S \<longrightarrow>  
       sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) ) )^2) \<le> (1::real) + C\<close>
      by (smt \<open>\<forall>S. finite S \<longrightarrow> sqrt (\<Sum>x\<in>S. (cmod (a N x))\<^sup>2) \<le> C\<close> \<open>\<forall>S. finite S \<longrightarrow> sqrt (\<Sum>x\<in>S. (cmod (a m x - a N x))\<^sup>2) \<le> 1\<close>)
    thus ?thesis
      using sqrt_le_D by auto
  qed
  moreover have \<open>m < N \<Longrightarrow> \<exists> M::real. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close>
  proof(cases \<open>N = 0\<close>)
    case True
    then show ?thesis 
      using calculation by blast
  next
    case False
    from \<open>\<forall> k::nat. has_ell2_norm (a k)\<close>
    have \<open>\<forall> k::nat. \<exists> M::real. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a k) x))^2) \<le> M\<close>
      using has_ell2_norm_explicit
      by auto
    then obtain MM::\<open>nat \<Rightarrow> real\<close> where
      \<open>\<forall> k::nat. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a k) x))^2) \<le> MM k\<close>
      by metis
    have \<open>finite {MM k| k::nat. k < N}\<close> by auto
    moreover have \<open>{MM k| k::nat. k < N} \<noteq> {}\<close>
      using False by auto
    ultimately obtain C where \<open>C = Sup {MM k| k::nat. k < N}\<close>
      by blast
    assume \<open>m < N\<close>
    have \<open>\<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> MM m\<close>  
      using \<open>\<forall> k::nat. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a k) x))^2) \<le> MM k\<close>
      by blast
    moreover have  \<open>MM m \<le> C\<close>
      using  \<open>C = Sup {MM k| k::nat. k < N}\<close> \<open>finite {MM k| k::nat. k < N}\<close> 
        \<open>{MM k| k::nat. k < N} \<noteq> {}\<close>  \<open>m < N\<close>  
      using le_cSup_finite by blast
    ultimately have  \<open>\<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> C\<close>
      by auto      
    thus ?thesis by auto
  qed
  ultimately show ?thesis by fastforce
qed
*)

(* NEW *)
lemma convergence_pointwise_to_ell2_same_limit:
  fixes a :: \<open>nat \<Rightarrow> ('a \<Rightarrow> complex)\<close> and l :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>a \<midarrow>pointwise\<rightarrow> l\<close> and \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> 
    and \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
  shows \<open>has_ell2_norm l \<and> ( \<lambda> k. ell2_norm ( (a k) - l ) ) \<longlonglongrightarrow> 0\<close> 
proof-
  have \<open>has_ell2_norm l\<close>
  proof-
    have \<open>\<exists> M::real. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod (l x))^2) \<le> M\<close>
    proof-
      have \<open>\<exists> M::real. \<forall> S::'a set. \<exists> m. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M\<close> 
      proof-            
        have \<open>\<exists> M::real. \<forall> S::'a set. \<exists> m. M\<ge>0 \<and> ( finite' S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M )\<close> 
        proof-
          from \<open>a \<midarrow>pointwise\<rightarrow> l\<close> 
          have \<open>\<forall> x::'a. (\<lambda> m. (a m) x) \<longlonglongrightarrow> l x\<close>
            by (simp add: pointwise_convergent_to_def)
          hence  \<open>\<forall> x::'a. \<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N.  dist (l x) ((a m) x) < \<epsilon>\<close>
            by (meson LIMSEQ_iff_nz dist_commute_lessI)
          hence  \<open>\<forall> x::'a. \<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. (cmod (l x - (a m) x)) < \<epsilon>\<close>
            by (simp add: dist_norm)
          hence  \<open>\<exists> NN:: 'a \<Rightarrow> real \<Rightarrow> nat. \<forall> x::'a. \<forall> \<epsilon>::real. \<forall> m::nat. 
                    \<epsilon> > 0 \<and> m \<ge> NN x \<epsilon> \<longrightarrow> (cmod (l x - (a m) x)) < \<epsilon>\<close>
            by metis
          then obtain NN where \<open>\<forall> x::'a. \<forall> \<epsilon>::real. \<forall> m::nat. 
                    \<epsilon> > 0 \<and> m \<ge> NN x \<epsilon> \<longrightarrow> (cmod (l x - (a m) x)) < \<epsilon>\<close>
            by blast                 
          have \<open>S \<noteq> {} \<Longrightarrow> {NN x (1/(card S))| x. x \<in> S} \<noteq> {}\<close> for S::\<open>'a set\<close>
            by blast
          have \<open>finite S \<Longrightarrow> finite {NN x (1/(card S))| x. x \<in> S}\<close> for S::\<open>'a set\<close>
            by simp
          obtain NS where \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow> NS S = Sup {NN x (1/(card S))| x. x \<in> S}\<close>
            by fastforce
          have  \<open>\<forall> S::'a set.  finite S \<and> S \<noteq> {} \<longrightarrow> 
             (\<forall> x \<in> S. (cmod (l x - (a (NS S)) x)) < 1/(card S) )\<close>
            sorry
          hence  \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow>
                    (\<forall> x \<in> S. (cmod (l x - (a  (NS S)) x))^2 < (1/(card S))^2 )\<close>
            by (simp add: power_strict_mono)
          hence  \<open>\<forall> S::'a set.  finite S \<and> S \<noteq> {} \<longrightarrow>
             (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < (\<Sum> x \<in> S. (1/(card S))^2 )\<close>
            sorry
          hence  \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow>
             (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < (1/(card S))^2*(card S)\<close>
            by (simp add: ordered_field_class.sign_simps(24))
          hence \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow>
            (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < 1/(card S)\<close>
            sorry
          hence \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow>
            (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < 1\<close>
            sorry
          hence \<open>\<forall> S::'a set. finite' S \<longrightarrow>
            (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) \<le> (1::real)\<close>
            by fastforce
          hence \<open>\<forall> S::'a set. finite' S \<longrightarrow>
            sqrt (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) \<le> (1::real)\<close>
            by simp
          moreover have \<open>(1::real) \<ge> 0\<close>
            by simp
          ultimately have \<open> \<forall> S::'a set. (1::real)\<ge>0 \<and> ( finite' S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a (NS S)) x))^2) \<le> (1::real) )\<close> 
            by auto
          hence \<open> \<exists> M. \<forall> S::'a set. M\<ge>0 \<and> ( finite' S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a (NS S)) x))^2) \<le> M)\<close>
            by blast
          hence \<open>\<exists> M. \<forall> S::'a set. \<exists> m.  M\<ge>0 \<and> ( finite' S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M)\<close>
            by blast
          thus ?thesis
            by blast
        qed 
        moreover have \<open>\<forall> S::'a set.  S = {} \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> 0\<close> 
          for m
          by simp
        ultimately show ?thesis
          by (metis (full_types) real_sqrt_zero sum.empty)
      qed 
      then obtain m::\<open>'a set \<Rightarrow> nat\<close> and U::real where 
        \<open>\<forall> S::'a set.  finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a (m S)) x))^2) \<le> U\<close>
        by metis
      have \<open>\<exists> M::real. \<forall> m. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close>
      proof-
        have \<open>\<exists> M::real. \<forall> m. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close>
          using  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
            \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> CauchyImplies_ell2Bounded
          by blast
        thus ?thesis
          by (meson real_sqrt_le_iff) 
      qed
      then obtain V where
        \<open>\<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a (m S)) x))^2) \<le> V\<close>
        by blast
      have \<open>finite S \<Longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x))^2) \<le> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) + sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2)\<close>
        for m::nat and S :: \<open>'a set\<close>
        using triangIneq_ell2Minus 
        by blast
      hence \<open>finite S \<Longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x))^2) \<le>  U + V\<close>
        for  S :: \<open>'a set\<close>
      proof-
        assume \<open>finite S\<close>
        hence \<open>sqrt (\<Sum> x\<in>S. (cmod ((a (m S)) x))^2) \<le> V\<close>
          using \<open>\<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a (m S)) x))^2) \<le> V\<close>
          by blast
        have \<open>sqrt (\<Sum> x\<in>S. (cmod (l x - (a (m S)) x))^2) \<le> U\<close>
          using \<open>finite S\<close> \<open>\<forall> S::'a set.  finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a (m S)) x))^2) \<le> U\<close>
          by blast
        have \<open>sqrt (\<Sum> x\<in>S. (cmod (l x))^2)
           \<le>   sqrt (\<Sum> x\<in>S. (cmod (l x - (a (m S)) x))^2)
             + sqrt (\<Sum> x\<in>S. (cmod ((a (m S)) x))^2)\<close>
          by (simp add: \<open>finite S\<close> triangIneq_ell2Minus)
        thus ?thesis using  \<open>sqrt (\<Sum> x\<in>S. (cmod ((a (m S)) x))^2) \<le> V\<close>  \<open>sqrt (\<Sum> x\<in>S. (cmod (l x - (a (m S)) x))^2) \<le> U\<close>
          by linarith
      qed
      hence \<open>\<exists> M. \<forall> S::'a set. finite S \<longrightarrow>  (\<Sum> x\<in>S. (cmod (l x))^2) \<le> M\<close>
        using sqrt_le_D by auto
      thus ?thesis by blast
    qed
    thus ?thesis using has_ell2_norm_explicit by auto 
  qed
  moreover have \<open> ( \<lambda> k. ell2_norm ( (a k) - l ) ) \<longlonglongrightarrow> 0 \<close>
    sorry
  ultimately show ?thesis by blast
qed

(*
proof-
  have \<open>has_ell2_norm l\<close>
  proof-
    have \<open>\<exists> M::real. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod (l x))^2) \<le> M\<close>
    proof-
      have \<open>\<exists> M::real. \<exists> N::nat. \<forall> m::nat. \<forall> S::'a set. m \<ge> N \<and> finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M\<close>
      proof-
        have \<open>\<exists> M::real. \<exists> N::nat. \<forall> m::nat. \<forall> S::'a set. m \<ge> N \<and> finite S \<and> S \<noteq> {} \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M\<close>
        proof- (* begin *)
          have \<open>\<exists> M::real. \<exists> N::nat. \<forall> m::nat. \<forall> S::'a set. m \<ge> N \<and> finite S \<and> S \<noteq> {} \<longrightarrow> (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M\<close>
          proof-
            from \<open>a \<midarrow>pointwise\<rightarrow> l\<close> 
            have \<open>\<forall> x::'a. (\<lambda> m. (a m) x) \<longlonglongrightarrow> l x\<close>
              by (simp add: pointwise_convergent_to_def)
            hence  \<open>\<forall> x::'a. \<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N.  dist (l x) ((a m) x) < \<epsilon>\<close>
              by (meson LIMSEQ_iff_nz dist_commute_lessI)
            hence  \<open>\<forall> x::'a. \<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. (cmod (l x - (a m) x)) < \<epsilon>\<close>
              by (simp add: dist_norm)
            hence  \<open>\<exists> NN:: 'a \<Rightarrow> real \<Rightarrow> nat. \<forall> x::'a. \<forall> \<epsilon>::real. \<forall> m::nat. 
                    \<epsilon> > 0 \<and> m \<ge> NN x \<epsilon> \<longrightarrow> (cmod (l x - (a m) x)) < \<epsilon>\<close>
              by metis
            then obtain NN where \<open>\<forall> x::'a. \<forall> \<epsilon>::real. \<forall> m::nat. 
                    \<epsilon> > 0 \<and> m \<ge> NN x \<epsilon> \<longrightarrow> (cmod (l x - (a m) x)) < \<epsilon>\<close>
              by blast                 
            have \<open>S \<noteq> {} \<Longrightarrow> {NN x (1/(card S))| x. x \<in> S} \<noteq> {}\<close> for S::\<open>'a set\<close>
              by blast
            have \<open>finite S \<Longrightarrow> finite {NN x (1/(card S))| x. x \<in> S}\<close> for S::\<open>'a set\<close>
              by simp
            obtain NS where \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow> NS S = Sup {NN x (1/(card S))| x. x \<in> S}\<close>
              by fastforce
            have  \<open>\<forall> S::'a set. \<forall> m::nat.  finite S \<and> S \<noteq> {} \<longrightarrow> 
              ( m \<ge> NS S \<longrightarrow> (\<forall> x \<in> S. (cmod (l x - (a m) x)) < 1/(card S) ) )\<close>
              sorry
            hence  \<open>\<forall> S::'a set. \<forall> m::nat.  finite S \<and> S \<noteq> {} \<longrightarrow>
                   ( m \<ge> NS S \<longrightarrow> (\<forall> x \<in> S. (cmod (l x - (a m) x))^2 < (1/(card S))^2 ) )\<close>
              by (simp add: power_strict_mono)
            hence  \<open>\<forall> S::'a set. \<forall> m::nat.  finite S \<and> S \<noteq> {} \<longrightarrow>
            ( m \<ge> NS S \<longrightarrow> (\<Sum> x \<in> S. (cmod (l x - (a m) x))^2) < (\<Sum> x \<in> S. (1/(card S))^2 ) )\<close>
              sorry
            hence  \<open>\<forall> S::'a set. \<forall> m::nat.  finite S \<and> S \<noteq> {} \<longrightarrow>
            ( m \<ge> NS S \<longrightarrow> (\<Sum> x \<in> S. (cmod (l x - (a m) x))^2) < (1/(card S))^2*(card S) )\<close>
              by (simp add: ordered_field_class.sign_simps(24))
            hence \<open>\<forall> S::'a set. \<forall> m::nat. finite S \<and> S \<noteq> {} \<longrightarrow>
            ( m \<ge> NS S \<longrightarrow> (\<Sum> x \<in> S. (cmod (l x - (a m) x))^2) < 1/(card S) )\<close>
              sorry
            have \<open>\<exists>M N. \<forall>m S. m \<ge> N \<and> finite' S \<longrightarrow> (\<Sum>x\<in>S. (cmod (l x - a m x))\<^sup>2) \<le> M\<close>
              sorry
            thus ?thesis
              by blast 
          qed
          thus ?thesis
            by (meson real_sqrt_le_iff) 
        qed (* end *)
        show ?thesis
        proof-
          obtain M N where \<open>\<forall> m::nat. \<forall> S::'a set. m \<ge> N \<and> finite S \<and> S \<noteq> {} \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M\<close>
            using \<open>\<exists>M N. \<forall>m S. N \<le> m \<and> finite' S \<longrightarrow> sqrt (\<Sum>x\<in>S. (cmod (l x - a m x))\<^sup>2) \<le> M\<close> by auto
          have  \<open>\<forall> m::nat. \<forall> S::'a set. m \<ge> N \<and> finite S \<and> S = {} \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M\<close>
          proof-
            have \<open>m \<ge> N \<Longrightarrow> finite S \<Longrightarrow> S = {} \<Longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M\<close>
              for m S
            proof-
              assume \<open>m \<ge> N\<close>
              assume \<open>finite S\<close>
              assume \<open>S = {}\<close>
              hence \<open>( \<Sum> x\<in>S. (cmod (l x - (a m) x))^2 ) = 0\<close>
                by simp
              hence \<open>sqrt ( \<Sum> x\<in>S. (cmod (l x - (a m) x))^2 ) = 0\<close>
                by simp
              moreover have \<open>M \<ge> 0\<close>
              proof-
                have  \<open>\<forall> m::nat. \<forall> S::'a set. m \<ge> N \<and> finite S \<and> S \<noteq> {}
                             \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<ge> 0\<close>
                  by (simp add: sum_nonneg) 
                have \<open>\<exists> K::'a set. finite K \<and> K \<noteq> {}\<close>
                  by auto
                then obtain K::\<open>'a set\<close> where \<open>finite K\<close> and \<open>K \<noteq> {}\<close>
                  by blast
                have \<open>sqrt (\<Sum> x\<in>K. (cmod (l x - (a m) x))^2) \<le> M\<close>
                  by (simp add: \<open>K \<noteq> {}\<close> \<open>N \<le> m\<close> \<open>\<forall>m S. N \<le> m \<and> finite' S \<longrightarrow> sqrt (\<Sum>x\<in>S. (cmod (l x - a m x))\<^sup>2) \<le> M\<close> \<open>finite K\<close>)
                moreover have \<open>0 \<le> sqrt (\<Sum> x\<in>K. (cmod (l x - (a m) x))^2)\<close>
                  by (simp add: sum_nonneg)
                ultimately show ?thesis
                  by linarith 
              qed
              thus ?thesis
                by (simp add: calculation)   
            qed
            thus ?thesis
              by blast 
          qed
          thus ?thesis using  \<open>\<forall> m::nat. \<forall> S::'a set. m \<ge> N \<and> finite S \<and> S \<noteq> {} \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M\<close>
            by blast
        qed
      qed
      moreover have \<open>\<exists> M::real. \<forall> S::'a set.  finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close> 
        for m :: nat
      proof-
        have \<open>\<exists> M::real. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close> for m :: nat
          using  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
            \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> CauchyImplies_ell2Bounded
          by blast
        thus ?thesis
          by (meson real_sqrt_le_iff) 
      qed
      moreover have \<open>finite S \<Longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x))^2) \<le> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) + sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2)\<close>
        for m::nat and S :: \<open>'a set\<close>
        using triangIneq_ell2Minus 
        by blast
      ultimately show ?thesis 
      proof-
        obtain U N where
          \<open>\<forall> S::'a set. m \<ge> N \<and> finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> U \<close> for m::nat
          using \<open>\<exists>M N. \<forall>m S. N \<le> m \<and> finite S \<longrightarrow> sqrt (\<Sum>x\<in>S. (cmod (l x - a m x))\<^sup>2) \<le> M\<close> by auto
        moreover have \<open>N \<ge> N\<close> by simp
        ultimately have \<open>\<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a N) x))^2) \<le> U\<close> 
          by auto
        have \<open>\<exists> M::real. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close> for m :: nat
        proof-
          have \<open>\<exists> M::real. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close> for m :: nat
            using CauchyImplies_ell2Bounded assms(2) has_ell2_norm_explicit by fastforce
          thus ?thesis  by (meson real_sqrt_le_iff)
        qed 
        hence \<open>\<exists> M::real. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> M\<close>
          by blast
        then obtain V where \<open>\<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> V\<close>
          by blast
        have \<open>\<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x))^2) \<le> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) + sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2)\<close> for m :: nat
          using triangIneq_ell2Minus by auto
        moreover have  \<open>\<forall> S::'a set. finite S \<longrightarrow>
  sqrt (\<Sum> x\<in>S. (cmod (l x - (a N) x))^2) + sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> U + V\<close>       
          using  \<open>\<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> V\<close>
            \<open>\<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a N) x))^2) \<le> U\<close> 
          by (simp add: add_mono_thms_linordered_semiring(1))
        ultimately have  \<open>\<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x))^2) \<le> U + V\<close>
        proof -
          { fix AA :: "'a set"
            have ff1: "\<forall>A. sqrt (\<Sum>aa\<in>A. (cmod (a N aa))\<^sup>2) + sqrt (\<Sum>aa\<in>A. (cmod (l aa - a N aa))\<^sup>2) \<le> U + V \<or> infinite A"
              using \<open>\<forall>S. finite S \<longrightarrow> sqrt (\<Sum>x\<in>S. (cmod (l x - a N x))\<^sup>2) + sqrt (\<Sum>x\<in>S. (cmod (a N x))\<^sup>2) \<le> U + V\<close> add.commute by fastforce
            have ff2: "\<forall>n A. sqrt (\<Sum>a\<in>A. (cmod (l a))\<^sup>2) \<le> sqrt (\<Sum>aa\<in>A. (cmod (a n aa))\<^sup>2) + sqrt (\<Sum>aa\<in>A. (cmod (l aa - a n aa))\<^sup>2) \<or> infinite A"
              by (metis (no_types) \<open>\<And>m. \<forall>S. finite S \<longrightarrow> sqrt (\<Sum>x\<in>S. (cmod (l x))\<^sup>2) \<le> sqrt (\<Sum>x\<in>S. (cmod (l x - a m x))\<^sup>2) + sqrt (\<Sum>x\<in>S. (cmod (a m x))\<^sup>2)\<close> add.commute)
            have "\<forall>r ra rb. (rb::real) \<le> ra \<or> \<not> rb + r \<le> r + ra"
              by (metis add.commute add_le_cancel_left)
            then have "infinite AA \<or> sqrt (\<Sum>a\<in>AA. (cmod (l a))\<^sup>2) \<le> U + V"
              using ff2 ff1 by (meson add_mono_thms_linordered_semiring(1)) }
          then show ?thesis
            by meson
        qed
        thus ?thesis
          using sqrt_le_D by auto 
      qed 
    qed
    thus ?thesis using has_ell2_norm_explicit by auto
  qed
  moreover have \<open>( \<lambda> k. ell2_norm ( (a k) - l ) ) \<longlonglongrightarrow> 0\<close>
    sorry
  ultimately show ?thesis by auto
qed
*)


instantiation ell2 :: (type) chilbert_space
begin
instance
proof  
  (*   fix x :: \<open>nat \<Rightarrow> 'a ell2\<close>
  assume \<open>Cauchy x\<close>
  then have "\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (x m - x n) < e"
    by (simp add: dist_norm Cauchy_def)
  then have "\<exists>L. \<forall>r>0. \<exists>no. \<forall>n\<ge>no. \<parallel>x n - L \<parallel> < r"
  proof transfer
    fix x :: "nat \<Rightarrow> ('a \<Rightarrow> complex)"
    assume "pred_fun top has_ell2_norm x"
    assume "\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. ell2_norm (\<lambda>xa. x m xa - x n xa) < e"
    show "\<exists>L\<in>Collect has_ell2_norm. \<forall>r>0. \<exists>no. \<forall>n\<ge>no. ell2_norm (\<lambda>xa. x n xa - L xa) < r"
      sorry
  qed
  thus \<open>convergent x\<close>
    by (simp add: LIMSEQ_iff convergent_def)
 *)
  fix x :: \<open>nat \<Rightarrow> 'a ell2\<close>
  have \<open>\<forall> n::nat. has_ell2_norm ( Rep_ell2 (x n) )\<close>
    using Rep_ell2 by auto
  assume \<open>Cauchy x\<close>
  have \<open>\<forall> t::'a. Cauchy (\<lambda> n::nat. (Rep_ell2 (x n)) t)\<close>
    by (simp add: Cauchy_ell2_component \<open>Cauchy x\<close>)
  hence \<open>convergent (\<lambda> n::nat. (Rep_ell2 (x n)) t)\<close> for t ::'a
    by (simp add: Cauchy_convergent)
  then have \<open>\<forall> t::'a. \<exists> s. (\<lambda> n. (Rep_ell2 (x n)) t ) \<longlonglongrightarrow> s\<close>
    by (simp add: convergentD)
  hence  \<open>\<exists> l. ( (\<lambda> n. Rep_ell2 (x n)) \<midarrow>pointwise\<rightarrow> l)\<close>
    using pointwise_convergent_to_def
    by metis
  then obtain l where \<open>(\<lambda> n. Rep_ell2 (x n)) \<midarrow>pointwise\<rightarrow> l\<close>
    by auto
  hence  \<open>has_ell2_norm l \<and> (\<lambda> n. ell2_norm ( (Rep_ell2 (x n)) - l ) ) \<longlonglongrightarrow> 0\<close>
    using  \<open>\<forall> n::nat. has_ell2_norm ( Rep_ell2 (x n) )\<close>
      convergence_pointwise_to_ell2_same_limit 
    sorry
  obtain L::\<open>'a ell2\<close> where \<open>(\<lambda> n. ell2_norm ( (Rep_ell2 (x n)) - Rep_ell2 L ) ) \<longlonglongrightarrow> 0\<close>
    using Rep_ell2_cases \<open>has_ell2_norm l \<and> (\<lambda>n. ell2_norm (Rep_ell2 (x n) - l)) \<longlonglongrightarrow> 0\<close>
    by auto
  have \<open>\<forall> \<epsilon>>0. \<exists> N::nat. \<forall> n\<ge>N. abs ( ell2_norm ( (Rep_ell2 (x n)) - Rep_ell2 L ) )  < \<epsilon>\<close>
    using  \<open>(\<lambda> n. ell2_norm ( (Rep_ell2 (x n)) - Rep_ell2 L ) ) \<longlonglongrightarrow> 0\<close>
    by (simp add: LIMSEQ_iff)
  hence \<open>\<forall> \<epsilon>>0. \<exists> N::nat. \<forall> n\<ge>N.  norm ( (x n) - L ) < \<epsilon>\<close>
    (* TODO *)
    apply transfer apply (simp add: fun_diff_def)
    apply (subst (asm) abs_of_nonneg)
     apply auto
    by (cheat fixme)
  thus \<open>convergent x\<close>
    by (simp add: LIMSEQ_iff convergentI)
qed

(*
proof  
  fix x :: \<open>nat \<Rightarrow> 'a ell2\<close>
  have \<open>\<forall> n::nat. has_ell2_norm ( Rep_ell2 (x n) )\<close>
    using Rep_ell2 by auto
  assume \<open>Cauchy x\<close>
  have \<open>Cauchy (\<lambda> n::nat. (Rep_ell2 (x n)) t)\<close> for t::'a
    by (simp add: Cauchy_ell2_component \<open>Cauchy x\<close>)
  hence \<open>convergent (\<lambda> n::nat. (Rep_ell2 (x n)) t)\<close> for t ::'a
    by (simp add: Cauchy_convergent)
  then have \<open>\<forall> t::'a. \<exists> s. (\<lambda> n. (Rep_ell2 (x n)) t ) \<longlonglongrightarrow> s\<close>
    by (simp add: convergentD)
  hence  \<open>\<exists> l. ( (\<lambda> n. Rep_ell2 (x n)) \<midarrow>pointwise\<rightarrow> l)\<close>
    using pointwise_convergent_to_def
    by metis
  then obtain l where \<open>(\<lambda> n. Rep_ell2 (x n)) \<midarrow>pointwise\<rightarrow> l\<close>
    by auto
  hence  \<open>has_ell2_norm l \<and> (\<lambda> n. ell2_norm ( (Rep_ell2 (x n)) - l ) ) \<longlonglongrightarrow> 0\<close>
  using  \<open>\<forall> n::nat. has_ell2_norm ( Rep_ell2 (x n) )\<close>
    convergence_pointwise_to_ell2_same_limit 
  by blast
  obtain L::\<open>'a ell2\<close> where \<open>(\<lambda> n. ell2_norm ( (Rep_ell2 (x n)) - Rep_ell2 L ) ) \<longlonglongrightarrow> 0\<close>
    using Rep_ell2_cases \<open>has_ell2_norm l \<and> (\<lambda>n. ell2_norm (Rep_ell2 (x n) - l)) \<longlonglongrightarrow> 0\<close>
    by auto
  have \<open>\<forall> \<epsilon>>0. \<exists> N::nat. \<forall> n\<ge>N. abs ( ell2_norm ( (Rep_ell2 (x n)) - Rep_ell2 L ) )  < \<epsilon>\<close>
    using  \<open>(\<lambda> n. ell2_norm ( (Rep_ell2 (x n)) - Rep_ell2 L ) ) \<longlonglongrightarrow> 0\<close>
    by (simp add: LIMSEQ_iff)
  hence \<open>\<forall> \<epsilon>>0. \<exists> N::nat. \<forall> n\<ge>N.  norm ( (x n) - L ) < \<epsilon>\<close>
    by (cheat fixme)
  thus \<open>convergent x\<close>
    by (simp add: LIMSEQ_iff convergentI)
qed
*)

end

(* (* Old proof *)
 (* by (cheat vector_chilbert_space) *)
  fix X :: "nat \<Rightarrow> 'a ell2"
  assume "Cauchy X"
  define x where "x i = Rep_ell2 (X i)" for i
  then have [transfer_rule]: "rel_fun (=) (pcr_ell2 (=)) x X"
    unfolding vector.pcr_cr_eq cr_ell2_def rel_fun_def by simp
  from \<open>Cauchy X\<close> have "Cauchy (\<lambda>i. x i j)" for j
    unfolding x_def
    by (rule Cauchy_ell2_component)
  hence "convergent (\<lambda>i. x i j)" for j
    by (simp add: Cauchy_convergent_iff)
  then obtain Lx where "(\<lambda>i. x i j) \<longlonglongrightarrow> Lx j" for j
    unfolding convergent_def by metis
  define L where "L = Abs_ell2 Lx"
  have "has_ell2_norm Lx"
    by (cheat fixme)
  then have [transfer_rule]: "pcr_ell2 (=) Lx L"
    unfolding vector.pcr_cr_eq cr_ell2_def
    unfolding L_def apply (subst Abs_ell2_inverse) by auto
  have XL: "X \<longlonglongrightarrow> L"
  proof (rule LIMSEQ_I)
    fix r::real assume "0<r"
    show "\<exists>no. \<forall>n\<ge>no. norm (X n - L) < r"
      by (cheat fixme)
  qed
  show "convergent X"
    using XL by (rule convergentI) 
qed
*)


(*
(* TODO remove and document *)
abbreviation "timesScalarVec \<equiv> (scaleC :: complex \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2)"
replacement of timesScalarVec by scaleC (Occam's razor)
*)

(* lift_definition scaleC :: "complex \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>c x i. c * x i"
  by (fact ell2_norm_smult) *)
(* scaleC_scaleC: lemma scaleC_twice[simp]: "scaleC a (scaleC b \<psi>) = scaleC (a*b) \<psi>"
  by (transfer, auto) *)

(* scaleC_minus1_left - lemma uminus_ell2: "(-\<psi>) = scaleC (-1) \<psi>"
  apply transfer by auto *)

(* scaleC_one - lemma one_times_vec[simp]: "scaleC 1 \<psi> = \<psi>"
  apply transfer by simp *)

(* scaleC_zero_right -- lemma times_zero_vec[simp]: "scaleC c 0 = 0"
  apply transfer by simp *)

(* scaleC_add_right -- lemma scaleC_add_right: "scaleC c (x+y) = scaleC c x + scaleC c y" 
  apply transfer apply (rule ext) by algebra *)

(* scaleC_add_left - lemma scaleC_add_left: "scaleC (c+d) x = scaleC c x + scaleC d x"
  apply transfer apply (rule ext) by algebra *)

lemma ell2_ket[simp]: "norm (ket i) = 1"
  apply transfer unfolding ell2_norm_def real_sqrt_eq_1_iff
  apply (rule cSUP_eq_maximum)
   apply (rule_tac x="{i}" in bexI)
    apply auto
  by (rule ell2_1)


typedef 'a subspace = "{A::'a ell2 set. is_subspace A}"
  morphisms subspace_to_set Abs_subspace
  apply (rule exI[of _ "{0}"]) by simp
setup_lifting type_definition_subspace
  (* derive universe subspace *)

instantiation subspace :: (type)zero begin (* The subspace {0} *)
lift_definition zero_subspace :: "'a subspace" is "{0::'a ell2}" by simp
instance .. end

instantiation subspace :: (type)top begin  (* The full space *)
lift_definition top_subspace :: "'a subspace" is "UNIV::'a ell2 set" by simp
instance .. end

instantiation subspace :: (type)inf begin  (* Intersection *)
lift_definition inf_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace" is "(\<inter>)" by simp
instance .. end

instantiation subspace :: (type)sup begin  (* Sum of spaces *)
lift_definition sup_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace" is "\<lambda>A B::'a ell2 set. closure {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}" 
  using is_subspace_closed_plus
  unfolding closed_sum_def
  unfolding general_sum_def
  by auto

instance .. end
instantiation subspace :: (type)plus begin  (* Sum of spaces *)
lift_definition plus_subspace :: "'a subspace \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace" is "\<lambda>A B::'a ell2 set. closure {\<psi>+\<phi>| \<psi> \<phi>. \<psi>\<in>A \<and> \<phi>\<in>B}"
  using is_subspace_closed_plus
  unfolding closed_sum_def
  unfolding general_sum_def
  by auto

instance .. end

lemma subspace_sup_plus: "(sup :: 'a subspace \<Rightarrow> _ \<Rightarrow> _) = (+)" 
  unfolding sup_subspace_def plus_subspace_def by simp

instantiation subspace :: (type)Inf begin  (* Intersection *)
lift_definition Inf_subspace :: "'a subspace set \<Rightarrow> 'a subspace" is "Inf :: 'a ell2 set set \<Rightarrow> 'a ell2 set" by simp
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
  have "ket undefined \<noteq> (0::'a ell2)"
    apply transfer
    by (meson one_neq_zero)
  thus "{0::'a ell2} \<noteq> UNIV" by auto
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
lift_definition bot_subspace :: "'a subspace" is "{0::'a ell2}" by (fact is_subspace_0)
instance apply intro_classes
  apply transfer 
  using is_subspace_0 ortho_bot ortho_leq by blast

end
lemma subspace_zero_bot: "(0::_ subspace) = bot" 
  unfolding zero_subspace_def bot_subspace_def by simp

instantiation subspace :: (type)ab_semigroup_add begin
instance
  apply intro_classes
   apply transfer
  using is_closed_subspace_asso
  unfolding closed_sum_def 
  unfolding general_sum_def
   apply blast

  apply transfer
  using is_closed_subspace_comm
  unfolding closed_sum_def 
  unfolding general_sum_def
  apply blast
  done
end

instantiation subspace :: (type)ordered_ab_semigroup_add begin
instance apply intro_classes apply transfer
  using is_closed_subspace_ord 
  by (smt Collect_mono_iff closure_mono subset_iff)

end

instantiation subspace :: (type)comm_monoid_add begin
instance apply intro_classes
  apply transfer
  using is_closed_subspace_zero
  unfolding closed_sum_def
  unfolding general_sum_def
  by fastforce
end

instantiation subspace :: (type)semilattice_sup begin
instance proof intro_classes
  fix x y z :: "'a subspace"
  show "x \<le> x \<squnion> y"
    apply transfer
    using is_closed_subspace_universal_inclusion_left
    unfolding closed_sum_def
    unfolding general_sum_def
    by blast
  show "y \<le> x \<squnion> y"
    apply transfer
    using is_closed_subspace_universal_inclusion_right
    unfolding closed_sum_def
    unfolding general_sum_def
    by blast

  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    apply transfer
    using is_closed_subspace_universal_inclusion_inverse
    unfolding closed_sum_def
    unfolding general_sum_def
    by blast
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
  unfolding sup_subspace_def[symmetric] 
  using is_closed_subspace_zero
  unfolding closed_sum_def
  unfolding general_sum_def
  by blast

lemma plus_bot[simp]: "x + bot = x" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp
lemma top_plus[simp]: "top + x = top" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp
lemma plus_top[simp]: "x + top = top" for x :: "'a subspace" unfolding subspace_sup_plus[symmetric] by simp

(* (* TODO remove *)
abbreviation subspace_to_set :: "'a subspace \<Rightarrow> 'a ell2 set" where "subspace_as_set == subspace_to_set"

removed
*)

definition [code del]: "span A = Inf {S. A \<subseteq> subspace_to_set S}"
  (* definition [code del]: "spanState A = Inf {S. state_to_ell2 ` A \<subseteq> subspace_to_set S}" *)
  (* consts span :: "'a set \<Rightarrow> 'b subspace"
adhoc_overloading span (* spanState *) spanVector *)

(* lemma span_ell2_state: "spanState A = spanVector (state_to_ell2 ` A)"
  by (simp add: spanState_def spanVector_def)  *)

lemma span_mult[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> span { a *\<^sub>C \<psi> } = span {\<psi>}"
  for \<psi>::"'a ell2"

proof-
  assume \<open>a \<noteq> 0\<close>
  have \<open>span {\<psi>} = Inf {S | S::'a subspace. {\<psi>} \<subseteq> subspace_to_set S }\<close>
    by (metis Complex_L2.span_def)
  also have \<open>... = Inf {S | S::'a subspace. \<psi> \<in> subspace_to_set S }\<close>
    by simp
  also have \<open>... = Inf {S | S::'a subspace. a *\<^sub>C \<psi> \<in> subspace_to_set S }\<close>
  proof-
    have \<open>\<psi> \<in> subspace_to_set S \<longleftrightarrow>  a *\<^sub>C \<psi> \<in> subspace_to_set S\<close> for S
    proof-
      have \<open>(subspace_to_set S) is-a-closed-subspace \<close>
        using subspace_to_set by auto
      hence \<open>\<psi> \<in> subspace_to_set S \<Longrightarrow>  a *\<^sub>C \<psi> \<in> subspace_to_set S\<close> for S
        by (metis Abs_subspace_cases Abs_subspace_inverse is_general_subspace.smult_closed is_subspace.subspace mem_Collect_eq)
      moreover have  \<open>a *\<^sub>C \<psi> \<in> subspace_to_set S \<Longrightarrow> \<psi> \<in> subspace_to_set S\<close> for S
      proof-
        assume \<open>a *\<^sub>C \<psi> \<in> subspace_to_set S\<close>
        obtain b where \<open>b * a = 1\<close> using \<open>a \<noteq> 0\<close> 
          by (metis divide_complex_def divide_self_if mult.commute)
        have \<open>b *\<^sub>C (a *\<^sub>C \<psi>) \<in> subspace_to_set S\<close> 
          using  \<open>a *\<^sub>C \<psi> \<in> subspace_to_set S\<close> is_general_subspace.smult_closed
            is_subspace.subspace subspace_to_set
          by fastforce
        hence  \<open>(b *\<^sub>C a) *\<^sub>C \<psi> \<in> subspace_to_set S\<close> 
          by simp
        thus ?thesis using  \<open>b * a = 1\<close> by simp
      qed                       
      ultimately show ?thesis by blast
    qed
    thus ?thesis by simp
  qed
  also have \<open>... = Inf {S | S::'a subspace. {a *\<^sub>C \<psi>} \<subseteq> subspace_to_set S }\<close>
    by auto
  also have \<open>... = span {a *\<^sub>C \<psi>}\<close> 
    by (metis Complex_L2.span_def)
  finally have  \<open>span {\<psi>} = span {a *\<^sub>C \<psi>}\<close>
    by blast
  thus ?thesis by auto
qed

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
  \<open>A \<subseteq> subspace_to_set (span A)\<close> for A :: \<open>('a ell2) set\<close>
proof-
  have \<open>\<forall> S. S \<in> {S. A \<subseteq> subspace_to_set S} \<longrightarrow> A \<subseteq> subspace_to_set S\<close>
    by simp
  hence \<open>A \<subseteq> \<Inter> {subspace_to_set S| S. A \<subseteq> subspace_to_set S}\<close>
    by blast
  hence \<open>A \<subseteq> subspace_to_set( Inf {S| S. A \<subseteq> subspace_to_set S})\<close>
    by (metis (no_types, lifting)  INF_greatest Inf_subspace.rep_eq \<open>\<forall>S. S \<in> {S. A \<subseteq> subspace_to_set S} \<longrightarrow> A \<subseteq> subspace_to_set S\<close>)
  thus ?thesis using span_def by metis
qed

lemma ortho_bot[simp]: "ortho bot = top"
  apply transfer by simp

lemma ortho_top[simp]: "ortho top = bot"
  apply transfer by simp

lemma ortho_twice[simp]: "ortho (ortho S) = S"
  apply transfer
  using orthogonal_complement_twice by blast 
end

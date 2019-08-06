(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

theory Complex_L2
  imports "HOL-Analysis.L2_Norm" "HOL-Library.Rewrite" "HOL-Analysis.Infinite_Set_Sum"
    Complex_Inner_Product Infinite_Set_Sum_Missing Bounded_Operators Complex_Main
    Extended_Sorry
    "HOL-ex.Sketch_and_Explore"
    (* This theory allows to write "sketch -" to get a proof outline (click on the outline to insert).
Or "sketch bla" for a proof outline starting with "proof bla" *)
begin

unbundle bounded_notation

section \<open>Preliminaries\<close>

hide_const (open) Real_Vector_Spaces.span

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

(* TODO rename to l2? *)
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


definition "ell2_norm x = sqrt (SUP F:{F. finite F}. sum (\<lambda>i. norm (x i)^2) F)"

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
definition [code del]: "uniformity = (INF e:{0<..}. principal {(x::'a ell2, y). norm (x - y) < e})"
definition [code del]: "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e:{0<..}. principal {(x, y). norm (x - y) < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "'a ell2 set"
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



lemma ellnorm_as_sup_set: 
  fixes f :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>has_ell2_norm f\<close>
  shows \<open>ell2_norm f = Sup { sqrt (\<Sum> i \<in> S. (cmod (f i))\<^sup>2)  | S::'a set. finite S }\<close>
proof-
  have  \<open>S \<noteq> {} \<Longrightarrow> bdd_above S  \<Longrightarrow> \<forall> x \<in> S. x \<ge> 0 \<Longrightarrow> Sup (sqrt ` S) = sqrt (Sup S)\<close>
    for S :: \<open>real set\<close>
  proof-
    have \<open>S \<noteq> {} \<Longrightarrow> bdd_above S \<Longrightarrow> \<forall> x \<in> S. x \<ge> 0 \<Longrightarrow> Sup (power2 ` S) \<le> power2 (Sup S)\<close>
      for S :: \<open>real set\<close>
    proof-
      assume \<open>S \<noteq> {}\<close> and \<open>bdd_above S\<close> and \<open>\<forall> x \<in> S. x \<ge> 0\<close>
      have \<open>x \<in> (power2 ` S) \<Longrightarrow> x \<le> power2 (Sup S)\<close>
        for x
      proof-
        assume \<open>x \<in> (power2 ` S)\<close>
        then obtain y where \<open>x = power2 y\<close> and \<open>y \<in> S\<close> by blast
        have \<open>y \<le> Sup S\<close> using  \<open>y \<in> S\<close>  \<open>S \<noteq> {}\<close> \<open>bdd_above S\<close>
          by (simp add: cSup_upper)
        hence \<open>power2 y \<le> power2 (Sup S)\<close>
          by (simp add: \<open>y \<in> S\<close>  \<open>\<forall> x \<in> S. x \<ge> 0\<close> power_mono)
        thus ?thesis using  \<open>x = power2 y\<close> by blast
      qed
      thus ?thesis using cSup_le_iff \<open>S \<noteq> {}\<close> \<open>bdd_above S\<close>
        by (simp add: cSup_least)
    qed 
    assume \<open>S \<noteq> {}\<close> and \<open>bdd_above S\<close> and \<open>\<forall> x \<in> S. x \<ge> 0\<close>
    have \<open>mono sqrt\<close>
      by (simp add: mono_def) 
    have \<open>Sup (sqrt ` S) \<le> sqrt (Sup S)\<close>
      using  \<open>mono sqrt\<close>
      by (simp add: \<open>S \<noteq> {}\<close> \<open>bdd_above S\<close> bdd_above_image_mono cSUP_le_iff cSup_upper) 
    moreover have \<open>sqrt (Sup S) \<le> Sup (sqrt ` S)\<close>
    proof- 
      have \<open>(Sup ( power2 ` (sqrt ` S) )) \<le> power2 (Sup (sqrt ` S))\<close>
      proof-
        have \<open>sqrt ` S \<noteq> {}\<close>
          by (simp add: \<open>S \<noteq> {}\<close>) 
        moreover have \<open>bdd_above (sqrt ` S)\<close>
          by (meson  \<open>bdd_above S\<close> bdd_aboveI2 bdd_above_def real_sqrt_le_iff)   
        ultimately show ?thesis 
          using \<open>\<And> S. S \<noteq> {} \<Longrightarrow> bdd_above S \<Longrightarrow> \<forall> x \<in> S. x \<ge> 0 \<Longrightarrow> Sup (power2 ` S) \<le> power2 (Sup S)\<close>
          by (simp add: \<open>\<forall> x \<in> S. x \<ge> 0\<close>) 
      qed
      hence \<open>(Sup ( (\<lambda> t. t^2) ` (sqrt ` S) )) \<le> (Sup (sqrt ` S))^2\<close>
        by simp
      moreover have \<open>(\<lambda> t. t^2) ` (sqrt ` S) = S\<close>
      proof-
        have  \<open>(\<lambda> t. t^2) ` (sqrt ` S) \<subseteq> S\<close>
          by (simp add: \<open>\<forall> x \<in> S. x \<ge> 0\<close> image_subset_iff)
        moreover have  \<open>S \<subseteq> (\<lambda> t. t^2) ` (sqrt ` S)\<close>
          by (simp add: \<open>\<forall> x \<in> S. x \<ge> 0\<close> image_iff subsetI)
        ultimately show ?thesis by blast
      qed
      ultimately have \<open>(Sup S) \<le> (Sup (sqrt ` S))^2\<close>
        by simp
      moreover have \<open>Sup S \<ge> 0\<close>
        using \<open>\<forall> x \<in> S. x \<ge> 0\<close>
          \<open>S \<noteq> {}\<close> \<open>bdd_above S\<close> cSup_upper2 by auto 
      ultimately show ?thesis
        by (metis all_not_in_conv  \<open>S \<noteq> {}\<close>  \<open>bdd_above S\<close>  \<open>\<forall> x \<in> S. x \<ge> 0\<close> bdd_aboveI2 bdd_above_def cSup_upper2 empty_is_image image_iff real_le_lsqrt real_sqrt_ge_0_iff real_sqrt_le_iff)  
    qed 
    ultimately show ?thesis by simp
  qed
  have \<open>ell2_norm f = sqrt (Sup { \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S })\<close>
    by (simp add: ell2_norm_def setcompr_eq_image)
  have \<open>{ \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S } \<noteq> {}\<close>
    by auto
  moreover have \<open>bdd_above { \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S }\<close>
    by (metis (no_types) assms has_ell2_norm_def setcompr_eq_image)
  moreover have \<open>\<forall> x \<in> { \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S }. x \<ge> 0\<close>
  proof-
    have \<open>finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod (f i))\<^sup>2) \<ge> 0 \<close>
      for S::\<open>'a set\<close>
      by (simp add: sum_nonneg)
    thus ?thesis by blast
  qed 
  ultimately have \<open>Sup (sqrt ` { \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S })
 = sqrt (Sup ({ \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S }))\<close>
    by (simp add:  \<open>\<And> S. S \<noteq> {} \<Longrightarrow> bdd_above S  \<Longrightarrow> \<forall> x \<in> S. x \<ge> 0 \<Longrightarrow> Sup (sqrt ` S) = sqrt (Sup S)\<close>)
  thus ?thesis using \<open>ell2_norm f = sqrt (Sup { \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S })\<close>
    by (simp add: image_image setcompr_eq_image)
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
  unfolding bdd_above_def L2_set_def
proof-
  have \<open>has_ell2_norm f \<Longrightarrow> ( \<exists> M::real. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod (f x))^2) \<le> M )\<close>
    by (simp add: bdd_above_def has_ell2_norm_def)
  moreover have \<open>( \<exists> M::real. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod (f x))^2) \<le> M ) \<Longrightarrow> has_ell2_norm f\<close>
    by (simp add: bdd_above_def has_ell2_norm_def)
  ultimately show ?thesis
    by auto
qed


lemma triangIneq_ell2:
  fixes S :: \<open>'a set\<close> and f g :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>sqrt (\<Sum> x\<in>S. (cmod (f x + g x))^2)
   \<le> sqrt (\<Sum> x\<in>S. (cmod (f x))^2) + sqrt (\<Sum> x\<in>S. (cmod (g x))^2)\<close>
proof (cases \<open>finite S\<close>)
  case False
  then show ?thesis
    by auto
next
  case True
    (* Reduction from the complex case to the real case, which was already proved
     in L2_set_triangle_ineq *)
  define SB :: \<open>('a\<times>bool) set\<close> where
    \<open>SB = {(x, True) | x. x \<in> S} \<union> {(x, False) | x. x \<in> S}\<close>
  have \<open>{(x, True) | x. x \<in> S} \<inter> {(x, False) | x. x \<in> S} = {}\<close>
    by blast
  have \<open>finite {(x, True) | x. x \<in> S}\<close>
    using \<open>finite S\<close>
    by simp
  have \<open>finite {(x, False) | x. x \<in> S}\<close>
    using \<open>finite S\<close>
    by simp
  have \<open>{(x, True) | x. x \<in> S} =  (\<lambda> t. (t, True))`S\<close>
    by auto      
  have \<open>{(x, False) | x. x \<in> S} =  (\<lambda> t. (t, False))`S\<close>
    by auto      
  have \<open>inj (\<lambda> x. (x, True))\<close>
    by (meson Pair_inject injI)
  have \<open>inj (\<lambda> x. (x, False))\<close>
    by (meson Pair_inject injI)
  define F::\<open>'a\<times>bool \<Rightarrow> real\<close> where 
    \<open>F z = (if snd z then  Re (f (fst z)) else Im (f (fst z)) )\<close>
  for z::\<open>'a\<times>bool\<close>
  define G::\<open>'a\<times>bool \<Rightarrow> real\<close> where 
    \<open>G z = (if snd z then  Re (g (fst z)) else Im (g (fst z)) )\<close>
  for z::\<open>'a\<times>bool\<close>
  have \<open>sqrt (\<Sum> x\<in>S. (cmod (f x + g x))^2)
       = sqrt (\<Sum> x\<in>S. ( (Re (f x) + Re (g x))^2 + (Im (f x) + Im (g x))^2 ))\<close>
  proof-
    have  \<open>sqrt (\<Sum> x\<in>S. (cmod (f x + g x))^2)
      = sqrt (\<Sum> x\<in>S. (cmod ( Complex (Re (f x) + Re (g x)) (Im (f x) + Im (g x)) ))^2)\<close>
      by (simp add: plus_complex.code)
    also have  \<open>...
   = sqrt (\<Sum> x\<in>S. ( sqrt ( (Re (f x) + Re (g x))^2 + (Im (f x) + Im (g x))^2 ) )^2)\<close>
      using complex_norm by auto
    finally show ?thesis by simp
  qed
  also have \<open>...
       = sqrt ( (\<Sum> x\<in>S.  (Re (f x) + Re (g x))^2) + (\<Sum> x\<in>S.  (Im (f x) + Im (g x))^2)  )\<close>
    by (simp add: sum.distrib)
  also have \<open>...
       = sqrt ( (\<Sum> x\<in>S.  (F (x, True) + G (x, True))^2) 
            +  (\<Sum> x\<in>S.  (F (x, False) + G (x, False))^2) )\<close>
    using     \<open>\<And> z. F z = (if snd z then  Re (f (fst z)) else Im (f (fst z)) )\<close>
      \<open>\<And> z. G z = (if snd z then  Re (g (fst z)) else Im (g (fst z)) )\<close>
    by simp
  also have \<open>...
       = sqrt ( (\<Sum> z \<in> (\<lambda> t. (t, True))`S.  (F z + G z)^2) 
            +  (\<Sum> z \<in> (\<lambda> t. (t, False))`S.  (F z + G z)^2) )\<close>
  proof-
    have  \<open>(\<Sum> x\<in>S. (F (x, True) + G (x, True))^2) 
        = (\<Sum> z \<in> (\<lambda> t. (t, True))`S.  (F z + G z)^2)\<close>
    proof -
      have f1: "\<not> inj_on (\<lambda>a. (a, True)) S \<or> v5_22 (\<lambda>a. (F (a, True) + G (a, True))\<^sup>2) (\<lambda>p. (F p + G p)\<^sup>2) S (\<lambda>a. (a::'a, True)) \<in> S \<and> (F (v5_22 (\<lambda>a. (F (a, True) + G (a, True))\<^sup>2) (\<lambda>p. (F p + G p)\<^sup>2) S (\<lambda>a. (a, True)), True) + G (v5_22 (\<lambda>a. (F (a, True) + G (a, True))\<^sup>2) (\<lambda>p. (F p + G p)\<^sup>2) S (\<lambda>a. (a, True)), True))\<^sup>2 \<noteq> (F (v5_22 (\<lambda>a. (F (a, True) + G (a, True))\<^sup>2) (\<lambda>p. (F p + G p)\<^sup>2) S (\<lambda>a. (a, True)), True) + G (v5_22 (\<lambda>a. (F (a, True) + G (a, True))\<^sup>2) (\<lambda>p. (F p + G p)\<^sup>2) S (\<lambda>a. (a, True)), True))\<^sup>2 \<or> (\<Sum>p\<in>(\<lambda>a. (a, True)) ` S. (F p + G p)\<^sup>2) = (\<Sum>a\<in>S. (F (a, True) + G (a, True))\<^sup>2)"
        by (simp add: sum.reindex_cong)
      have f2: "\<forall>A f. (\<exists>a aa. ((a::'a) \<in> A \<and> aa \<in> A \<and> (f a::'a \<times> bool) = f aa) \<and> a \<noteq> aa) \<or> inj_on f A"
        by (meson inj_onI)
      have "\<forall>f a aa. \<not> inj f \<or> ((f (a::'a)::'a \<times> bool) = f aa) = (a = aa)"
        by (metis inj_eq)
      then have "inj_on (\<lambda>a. (a, True)) S"
        using f2 by (metis (no_types) \<open>inj (\<lambda>x. (x, True))\<close>)
      then show ?thesis
        using f1 by linarith
    qed
    moreover have  \<open>(\<Sum> x\<in>S. (F (x, False) + G (x, False))^2) 
        = (\<Sum> z \<in> (\<lambda> t. (t, False))`S.  (F z + G z)^2)\<close>
      using \<open>inj (\<lambda> x. (x, False))\<close> \<open>finite S\<close>
        inj_eq inj_onI sum.reindex_cong
    proof - (* Sledgehammer proof *)
      have f1: "\<not> inj_on (\<lambda>a. (a, False)) S \<or> v5_22 (\<lambda>a. (F (a, False) + G (a, False))\<^sup>2) (\<lambda>p. (F p + G p)\<^sup>2) S (\<lambda>a. (a::'a, False)) \<in> S \<and> (F (v5_22 (\<lambda>a. (F (a, False) + G (a, False))\<^sup>2) (\<lambda>p. (F p + G p)\<^sup>2) S (\<lambda>a. (a, False)), False) + G (v5_22 (\<lambda>a. (F (a, False) + G (a, False))\<^sup>2) (\<lambda>p. (F p + G p)\<^sup>2) S (\<lambda>a. (a, False)), False))\<^sup>2 \<noteq> (F (v5_22 (\<lambda>a. (F (a, False) + G (a, False))\<^sup>2) (\<lambda>p. (F p + G p)\<^sup>2) S (\<lambda>a. (a, False)), False) + G (v5_22 (\<lambda>a. (F (a, False) + G (a, False))\<^sup>2) (\<lambda>p. (F p + G p)\<^sup>2) S (\<lambda>a. (a, False)), False))\<^sup>2 \<or> (\<Sum>p\<in>(\<lambda>a. (a, False)) ` S. (F p + G p)\<^sup>2) = (\<Sum>a\<in>S. (F (a, False) + G (a, False))\<^sup>2)"
        by (simp add: sum.reindex_cong)
      have f2: "\<forall>A f. (\<exists>a aa. ((a::'a) \<in> A \<and> aa \<in> A \<and> (f a::'a \<times> bool) = f aa) \<and> a \<noteq> aa) \<or> inj_on f A"
        by (meson inj_onI)
      have "\<forall>f a aa. \<not> inj f \<or> ((f (a::'a)::'a \<times> bool) = f aa) = (a = aa)"
        by (metis inj_eq)
      then have "inj_on (\<lambda>a. (a, False)) S"
        using f2 by (metis (no_types) \<open>inj (\<lambda>x. (x, False))\<close>)
      then show ?thesis
        using f1 by linarith
    qed
    ultimately show ?thesis
      by simp 
  qed 
  also have \<open>...
       = sqrt ( (\<Sum> z\<in>{(x, True) | x. x \<in> S}.  (F z + G z)^2) 
            +  (\<Sum> z\<in>{(x, False) | x. x \<in> S}.  (F z + G z)^2) )\<close>
    by (simp add: Setcompr_eq_image)
  also have \<open>...
        = sqrt ( \<Sum> z\<in>SB. (F z + G z)^2 )\<close>
    using \<open>SB = {(x, True) | x. x \<in> S} \<union> {(x, False) | x. x \<in> S}\<close>
      \<open>{(x, True) | x. x \<in> S} \<inter> {(x, False) | x. x \<in> S} = {}\<close>
      \<open>finite {(x, True) | x. x \<in> S}\<close>
      \<open>finite {(x, False) | x. x \<in> S}\<close>
    by (simp add: sum.union_disjoint)
  also have \<open>... \<le> sqrt ( \<Sum> z\<in>SB. (F z)^2 ) +  sqrt ( \<Sum> z\<in>SB. (G z)^2 )\<close>
    using L2_set_triangle_ineq
    by (metis L2_set_def)
  also have \<open>... = sqrt ( (\<Sum> z\<in>{(x, True) | x. x \<in> S}. (F z)^2)
                    +(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (F z)^2) )
                   + sqrt ( (\<Sum> z\<in>{(x, True) | x. x \<in> S}. (G z)^2)
                    +(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (G z)^2) )\<close>
  proof-
    have \<open>(\<Sum> z\<in>SB. (F z)^2) = (\<Sum> z\<in>{(x, True) | x. x \<in> S}. (F z)^2)
                    +(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (F z)^2)\<close>
      using  \<open>SB = {(x, True) | x. x \<in> S} \<union> {(x, False) | x. x \<in> S}\<close>
        \<open>{(x, True) | x. x \<in> S} \<inter> {(x, False) | x. x \<in> S} = {}\<close>
        \<open>finite {(x, True) | x. x \<in> S}\<close>  \<open>finite {(x, False) | x. x \<in> S}\<close>
      by (simp add: sum.union_disjoint)    
    moreover have  \<open>(\<Sum> z\<in>SB. (G z)^2) = (\<Sum> z\<in>{(x, True) | x. x \<in> S}. (G z)^2)
                    +(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (G z)^2)\<close>
      using  \<open>SB = {(x, True) | x. x \<in> S} \<union> {(x, False) | x. x \<in> S}\<close>
        \<open>{(x, True) | x. x \<in> S} \<inter> {(x, False) | x. x \<in> S} = {}\<close>
        \<open>finite {(x, True) | x. x \<in> S}\<close>  \<open>finite {(x, False) | x. x \<in> S}\<close>
      by (simp add: sum.union_disjoint)
    ultimately show ?thesis 
      using \<open>sqrt (\<Sum>z\<in>SB. (F z + G z)\<^sup>2) \<le> sqrt (\<Sum>z\<in>SB. (F z)\<^sup>2) + sqrt (\<Sum>z\<in>SB. (G z)\<^sup>2)\<close>
      by simp   
  qed  
  also have \<open>... = sqrt ( (\<Sum> x\<in>S. (F (x, True))^2)+(\<Sum> x\<in>S. (F (x, False))^2) ) + sqrt ( (\<Sum> x\<in>S. (G (x, True))^2)+(\<Sum> x\<in>S. (G (x, False))^2) )\<close>
  proof- 
    have \<open>(\<Sum> z\<in>{(x, True) | x. x \<in> S}. (F z)^2) = (\<Sum> x\<in>S. (F (x, True))^2)\<close>
    proof-
      have \<open>(\<Sum> z\<in>{(x, True) | x. x \<in> S}. (F z)^2)
            = (\<Sum> x\<in>S. (F ( (\<lambda> t. (t, True)) x ))^2)\<close>
        using Pair_inject  sum.eq_general image_iff \<open>{(x, True) | x. x \<in> S} =  (\<lambda> t. (t, True))`S\<close>
        by smt
      thus ?thesis 
        by blast        
    qed
    moreover have \<open>(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (F z)^2) = (\<Sum> x\<in>S. (F (x, False))^2)\<close>
    proof-
      have \<open>(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (F z)^2)
            = (\<Sum> x\<in>S. (F ( (\<lambda> t. (t, False)) x ))^2)\<close>
        using Pair_inject  sum.eq_general image_iff \<open>{(x, False) | x. x \<in> S} =  (\<lambda> t. (t, False))`S\<close>
        by smt
      thus ?thesis 
        by blast        
    qed
    moreover have \<open>(\<Sum> z\<in>{(x, True) | x. x \<in> S}. (G z)^2) = (\<Sum> x\<in>S. (G (x, True))^2)\<close>
    proof-
      have \<open>(\<Sum> z\<in>{(x, True) | x. x \<in> S}. (G z)^2)
            = (\<Sum> x\<in>S. (G ( (\<lambda> t. (t, True)) x ))^2)\<close>
        using Pair_inject  sum.eq_general image_iff \<open>{(x, True) | x. x \<in> S} =  (\<lambda> t. (t, True))`S\<close>
        by smt
      thus ?thesis 
        by blast        
    qed
    moreover have \<open>(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (G z)^2) = (\<Sum> x\<in>S. (G (x, False))^2)\<close>
    proof-
      have \<open>(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (G z)^2)
            = (\<Sum> x\<in>S. (G ( (\<lambda> t. (t, False)) x ))^2)\<close>
        using Pair_inject  sum.eq_general image_iff \<open>{(x, False) | x. x \<in> S} =  (\<lambda> t. (t, False))`S\<close>
        by smt
      thus ?thesis 
        by blast        
    qed
    ultimately show ?thesis 
      using \<open>sqrt (\<Sum>z\<in>SB. (F z)\<^sup>2) + sqrt (\<Sum>z\<in>SB. (G z)\<^sup>2) =
    sqrt
     ((\<Sum>z\<in>{(x, True) |x. x \<in> S}. (F z)\<^sup>2) +
      (\<Sum>z\<in>{(x, False) |x. x \<in> S}. (F z)\<^sup>2)) +
    sqrt
     ((\<Sum>z\<in>{(x, True) |x. x \<in> S}. (G z)\<^sup>2) + (\<Sum>z\<in>{(x, False) |x. x \<in> S}. (G z)\<^sup>2))\<close>
      by simp
  qed 
  also have \<open>... = sqrt ( (\<Sum> x\<in>S. (F (x, True))^2 +  (F (x, False))^2) ) +
                   sqrt ( (\<Sum> x\<in>S. (G (x, True))^2 +  (G (x, False))^2) )\<close>
    by (simp add: sum.distrib)
  also have  \<open>... = sqrt ( \<Sum> x\<in>S. ( (Re (f x))^2 + (Im (f x))^2 ) )
             +  sqrt ( \<Sum> x\<in>S. ( (Re (g x))^2 + (Im (g x))^2 ) )\<close>
    using \<open>\<And> z. F z = (if snd z then  Re (f (fst z)) else Im (f (fst z)) )\<close>
      \<open>\<And> z. G z = (if snd z then  Re (g (fst z)) else Im (g (fst z)) )\<close>
    by simp
  also have  \<open>... = sqrt ( \<Sum> x\<in>S. ( cmod ( Complex (Re (f x)) (Im (f x)) ) )^2 )
          + sqrt ( \<Sum> x\<in>S. ( cmod ( Complex (Re (g x)) (Im (g x)) ) )^2 )\<close>
    using cmod_def
    by simp
  also have \<open>... = sqrt (\<Sum> x\<in>S. (cmod (f x))^2) + sqrt (\<Sum> x\<in>S. (cmod (g x))^2)\<close>
    by simp
  finally show ?thesis by blast
qed

lemma triangIneq_ell2InsideMinus:
  fixes S :: \<open>'a set\<close> and f g :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>sqrt (\<Sum> x\<in>S. (cmod (f x - g x))^2)
   \<le> sqrt (\<Sum> x\<in>S. (cmod (f x))^2) + sqrt (\<Sum> x\<in>S. (cmod (g x))^2)\<close>
proof-
  have  \<open>sqrt (\<Sum> x\<in>S. (cmod (f x - g x))^2)
      = sqrt (\<Sum> x\<in>S. (cmod (f x + (- g x)))^2)\<close>
    by simp
  also have \<open>... \<le>  sqrt (\<Sum> x\<in>S. (cmod (f x))^2) + sqrt (\<Sum> x\<in>S. (cmod (- g x))^2)\<close>
    by (metis (no_types) triangIneq_ell2)
  also have \<open>... \<le>  sqrt (\<Sum> x\<in>S. (cmod (f x))^2) + sqrt (\<Sum> x\<in>S. (cmod (g x))^2)\<close>
    by auto
  finally show ?thesis by blast
qed

lemma triangIneq_ell2Minus:
  fixes S :: \<open>'a set\<close> and f g :: \<open>'a \<Rightarrow> complex\<close>
  shows \<open>sqrt (\<Sum> x\<in>S.  (cmod (f x) )^2) 
   \<le> sqrt (\<Sum> x\<in>S. (cmod (f x - g x))^2) + sqrt (\<Sum> x\<in>S. ( cmod (g x) )^2)\<close>
proof-
  have \<open>sqrt (\<Sum> x\<in>S.  (cmod (f x) )^2) = sqrt (\<Sum> x\<in>S. (cmod ((f x - g x) + g x) )^2)\<close>
    by auto
  hence \<open>... = sqrt (\<Sum> x\<in>S. (cmod ((\<lambda> t. f t - g t) x + g x) )^2)\<close>
    by auto
  hence \<open>... \<le> sqrt (\<Sum> x\<in>S. (cmod ((\<lambda> t. f t - g t) x) )^2)
             + sqrt (\<Sum> x\<in>S. (cmod (g x) )^2)\<close>
    using triangIneq_ell2
    by (metis (no_types) triangIneq_ell2)
  hence \<open>... \<le> sqrt (\<Sum> x\<in>S. (cmod (f x - g x) )^2)
             + sqrt (\<Sum> x\<in>S. (cmod (g x) )^2)\<close>
    by auto
  show ?thesis  
    using \<open>sqrt (\<Sum>x\<in>S. (cmod (f x - g x + g x))\<^sup>2) \<le> sqrt (\<Sum>x\<in>S. (cmod (f x - g x))\<^sup>2) + sqrt (\<Sum>x\<in>S. (cmod (g x))\<^sup>2)\<close> \<open>sqrt (\<Sum>x\<in>S. (cmod (f x))\<^sup>2) = sqrt (\<Sum>x\<in>S. (cmod (f x - g x + g x))\<^sup>2)\<close> by linarith
qed

lemma CauchyImplies_ell2Bounded:                         
  fixes a :: \<open>nat \<Rightarrow> ('a \<Rightarrow> complex)\<close>
  assumes \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
    and \<open>\<forall> k::nat. has_ell2_norm (a k)\<close>    
  shows \<open>\<exists> M::real. \<forall> m. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close>
proof-
  from  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
  have  \<open>\<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> (1::real)\<close>
    by auto
  then obtain N where
    \<open> \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2) \<le> (1::real)\<close>
    by blast
  hence \<open> \<forall> m \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> (1::real)\<close>
    by blast
  have \<open>\<exists> K. \<forall> m. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K\<close>
  proof-       
    have  \<open>\<exists> K. \<forall> m. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K\<close>
    proof- 
      have  \<open>\<exists> K. \<forall> m. \<forall> S::'a set. m < N \<longrightarrow> (finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K)\<close>
      proof(cases \<open>N = 0\<close>)
        case True
        then show ?thesis by blast
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
        have \<open>\<forall> m < N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> MM m\<close>  
          using \<open>\<forall> k::nat. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a k) x))^2) \<le> MM k\<close>
          by blast
        moreover have  \<open>\<forall> m < N. MM m \<le> C\<close>
          using  \<open>C = Sup {MM k| k::nat. k < N}\<close> \<open>finite {MM k| k::nat. k < N}\<close> 
            \<open>{MM k| k::nat. k < N} \<noteq> {}\<close>   
          using le_cSup_finite by blast
        ultimately have  \<open>\<forall> m < N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> C\<close>
          by fastforce
        obtain D where \<open>\<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> D\<close>
          using \<open>\<forall>k. \<exists>M. \<forall>S. finite S \<longrightarrow> (\<Sum>x\<in>S. (cmod (a k x))\<^sup>2) \<le> M\<close> by blast
        have  \<open>finite S \<Longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) + sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2)\<close>
          for m ::nat and S::\<open>'a set\<close>
          by (simp add: triangIneq_ell2InsideMinus)
        have  \<open>m < N \<Longrightarrow> finite S \<Longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> sqrt C + sqrt D\<close>
          for m::nat and S::\<open>'a set\<close>
        proof- 
          assume \<open>m < N\<close>
          assume \<open>finite S\<close>
          have \<open>sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) + sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2)\<close>
            by (simp add: \<open>\<And>m S. finite S \<Longrightarrow> sqrt (\<Sum>x\<in>S. (cmod (a m x - a N x))\<^sup>2) \<le> sqrt (\<Sum>x\<in>S. (cmod (a m x))\<^sup>2) + sqrt (\<Sum>x\<in>S. (cmod (a N x))\<^sup>2)\<close> \<open>finite S\<close>)
          moreover have \<open>(\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> C\<close>
            using  \<open>\<forall> m < N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> C\<close>
              \<open>finite S\<close> \<open>m < N\<close> by blast
          moreover have \<open>(\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> D\<close>
            using   \<open>\<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> D\<close>
              \<open>finite S\<close> by blast 
          ultimately show ?thesis
            by (smt real_sqrt_le_mono)            
        qed 
        hence  \<open>m < N \<Longrightarrow> finite S \<Longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> (sqrt C + sqrt D)^2\<close>
          for m::nat and S::\<open>'a set\<close>
          by (simp add: sqrt_le_D)
        thus ?thesis
          by blast 
      qed 
      moreover have  \<open>\<exists> K. \<forall> m. \<forall> S::'a set. m \<ge> N \<longrightarrow> (finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K)\<close>
        using  \<open> \<forall> m \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> (1::real)\<close>
        by blast
      ultimately have \<open>\<exists> K. \<forall> m. \<forall> S::'a set. (m < N \<or> m \<ge> N) \<longrightarrow> (finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K)\<close>
        by smt
      moreover have \<open>(m < N \<or> m \<ge> N)\<close>
        for m :: nat
        by auto
      ultimately show ?thesis
        by simp 
    qed 
    thus ?thesis
      by (meson real_sqrt_le_iff) 
  qed
  then obtain K where \<open>\<forall> m. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K\<close>
    by auto
  have \<open>finite S \<Longrightarrow>  sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2) + sqrt (\<Sum> x\<in>S. (cmod ((a n) x))^2)\<close>
    for m n :: nat and S::\<open>'a set\<close>
    by (simp add: triangIneq_ell2Minus) 
  hence \<open>finite S \<Longrightarrow>  sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) + sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2)\<close>
    for m :: nat and S::\<open>'a set\<close>
    by blast
  have \<open>\<exists> M. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> M\<close>
    using \<open>\<forall> k::nat. has_ell2_norm (a k)\<close>   
    unfolding has_ell2_norm_def
    by (metis assms(2) has_ell2_norm_explicit real_sqrt_le_iff)
  then obtain M where \<open> \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> M\<close>
    by blast
  have \<open>finite S \<Longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> K + M\<close>
    for S::\<open>'a set\<close> and m::nat
  proof-
    assume \<open>finite  S\<close>
    hence \<open>sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) + sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2)\<close>
      using  \<open>\<And> S::'a set. \<And>m::nat.  finite S \<Longrightarrow>  sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) + sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2)\<close>
      by blast
    moreover have \<open>sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> M\<close>
      using  \<open> \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> M\<close>  \<open>finite  S\<close>
      by blast
    ultimately have \<open>sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) + M\<close>
      by simp
    moreover have \<open>sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K\<close>
      using  \<open>\<forall> m. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K\<close>
        \<open>finite S\<close> by blast
    ultimately show ?thesis
      by linarith 
  qed
  hence \<open>finite S \<Longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> (K + M)^2\<close>
    for S::\<open>'a set\<close> and m::nat
    using \<open>\<And>m S. finite S \<Longrightarrow> sqrt (\<Sum>x\<in>S. (cmod (a m x))\<^sup>2) \<le> K + M\<close> sqrt_le_D by blast
  thus ?thesis
    by blast 
qed                                                                     


lemma convergence_pointwise_ell2_norm_exists:
  fixes a :: \<open>nat \<Rightarrow> ('a \<Rightarrow> complex)\<close> and l :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>a \<midarrow>pointwise\<rightarrow> l\<close> and \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> 
    and \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
  shows \<open>has_ell2_norm l\<close>
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
        obtain NS where \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow> NS S = Sup {NN x (1/(card S))| x. x \<in> S}\<close>
          by fastforce
        have  \<open>\<forall> S::'a set.  finite S \<and> S \<noteq> {} \<longrightarrow> 
             (\<forall> x \<in> S. (cmod (l x - (a (NS S)) x)) < 1/(card S) )\<close>
        proof- 
          have  \<open>finite S \<Longrightarrow> S \<noteq> {}
             \<Longrightarrow> x \<in> S \<Longrightarrow> (cmod (l x - (a (NS S)) x)) < 1/(card S)\<close>
            for S::\<open>'a set\<close> and x::'a
          proof- 
            assume \<open>finite S\<close>
            hence \<open>finite {NN x (1/(card S))| x. x \<in> S}\<close>
              by auto
            assume \<open>S \<noteq> {}\<close>
            hence \<open>{NN x (1/(card S))| x. x \<in> S} \<noteq> {}\<close>
              by auto
            assume \<open>x \<in> S\<close>
            hence \<open>\<forall> \<epsilon>::real. \<forall> m::nat. 
                    \<epsilon> > 0 \<and> m \<ge> NN x \<epsilon> \<longrightarrow> (cmod (l x - (a m) x)) < \<epsilon>\<close>
              using   \<open>\<forall> x::'a. \<forall> \<epsilon>::real. \<forall> m::nat. 
                    \<epsilon> > 0 \<and> m \<ge> NN x \<epsilon> \<longrightarrow> (cmod (l x - (a m) x)) < \<epsilon>\<close>
              by blast
            hence \<open>\<forall> m::nat. 
                     1/(card S) > 0 \<and> m \<ge> NN x (1/(card S)) \<longrightarrow> (cmod (l x - (a m) x)) < 1/(card S)\<close>
              by blast
            hence \<open>\<forall> m::nat. 
                      m \<ge> NN x (1/(card S)) \<longrightarrow> (cmod (l x - (a m) x)) < 1/(card S)\<close>
              using \<open>S \<noteq> {}\<close> \<open>finite S\<close> card_0_eq by auto
            moreover have \<open>NS S \<ge> NN x (1/(card S))\<close>
            proof- 
              from \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow> NS S = Sup {NN x (1/(card S))| x. x \<in> S}\<close>
              have \<open>NS S = Sup {NN x (1/(card S))| x. x \<in> S}\<close>
                using \<open>S \<noteq> {}\<close> \<open>finite S\<close> by auto   
              hence \<open>NS S \<ge> NN x (1/(card S))\<close>
                using \<open>x \<in> S\<close> \<open>{NN x (1/(card S))| x. x \<in> S} \<noteq> {}\<close>
                  \<open>finite {NN x (1/(card S))| x. x \<in> S}\<close>
                  le_cSup_finite by auto
              thus ?thesis by blast
            qed 
            ultimately have  \<open>(cmod (l x - (a (NS S)) x)) < 1/(card S)\<close>
              by simp
            thus ?thesis by blast
          qed
          thus ?thesis by blast
        qed 
        hence  \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow>
                    (\<forall> x \<in> S. (cmod (l x - (a  (NS S)) x))^2 < (1/(card S))^2 )\<close>
          by (simp add: power_strict_mono)
        hence  \<open>\<forall> S::'a set.  finite S \<and> S \<noteq> {} \<longrightarrow>
             (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < (\<Sum> x \<in> S. (1/(card S))^2 )\<close>
          by (meson sum_strict_mono)
        hence  \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow>
             (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < (1/(card S))^2*(card S)\<close>
          by (simp add: ordered_field_class.sign_simps)
        hence \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow>
            (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < 1/(card S)\<close>
          by (metis (no_types, lifting) mult_of_nat_commute power_one_over real_divide_square_eq semiring_normalization_rules(29) times_divide_eq_right)            
        have \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow>
            (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < (1::real)\<close>
        proof-
          have \<open>finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow>
            (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < (1::real)\<close>
            for  S::\<open>'a set\<close>
          proof-
            assume \<open>finite S\<close>
            assume \<open>S \<noteq> {}\<close>
            have \<open>(\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < 1/(card S)\<close>
              using \<open>S \<noteq> {}\<close> \<open>\<forall>S. finite' S \<longrightarrow> (\<Sum>x\<in>S. (cmod (l x - a (NS S) x))\<^sup>2) < 1 / real (card S)\<close> \<open>finite S\<close> by blast
            moreover have \<open>1/(card S) \<le> 1\<close>
              using  \<open>finite S\<close>  \<open>S \<noteq> {}\<close>
                card_0_eq by fastforce
            ultimately show ?thesis by auto
          qed 
          thus ?thesis by blast
        qed
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
      thus ?thesis
        by smt
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

lemma has_ell2_norm_diff: \<open>has_ell2_norm a \<Longrightarrow> has_ell2_norm b \<Longrightarrow> has_ell2_norm (a - b)\<close>
  for a b :: \<open>'a \<Rightarrow> complex\<close>
proof-
  assume \<open>has_ell2_norm b\<close> 
  hence \<open>has_ell2_norm (\<lambda> x. (-1::complex) * b x)\<close>
    using ell2_norm_smult
    by blast 
  hence \<open>has_ell2_norm (\<lambda> x. - b x)\<close>
    by simp
  hence \<open>has_ell2_norm (- b)\<close>
    by (metis Rep_ell2 Rep_ell2_cases \<open>has_ell2_norm b\<close> mem_Collect_eq uminus_ell2.rep_eq)
  moreover assume \<open>has_ell2_norm a\<close>
  ultimately have \<open>has_ell2_norm (\<lambda> x. a x + (- b) x)\<close>
    using ell2_norm_triangle
    by blast
  hence \<open>has_ell2_norm (\<lambda> x. a x - b x)\<close>
    by simp
  hence \<open>has_ell2_norm (\<lambda> x. (a - b) x)\<close>
    by simp
  thus ?thesis
    by (simp add: \<open>has_ell2_norm (a - b)\<close>)
qed

lemma convergence_pointwise_to_ell2_same_limit:
  fixes a :: \<open>nat \<Rightarrow> ('a \<Rightarrow> complex)\<close> and l :: \<open>'a \<Rightarrow> complex\<close>
  assumes \<open>a \<midarrow>pointwise\<rightarrow> l\<close> and \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> 
    and \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2) \<le> \<epsilon>\<close>
  shows \<open>( \<lambda> k. ell2_norm ( (a k) - l ) ) \<longlonglongrightarrow> 0\<close>
proof-
  have \<open>bdd_above (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite)\<close>
    for k::nat
  proof-
    have \<open>has_ell2_norm ((a k) - l)\<close>
    proof- 
      have \<open>has_ell2_norm (a k)\<close>
        using  \<open>\<forall> k::nat. has_ell2_norm (a k)\<close>
        by blast
      moreover have \<open>has_ell2_norm l\<close>
        using convergence_pointwise_ell2_norm_exists
          \<open>a \<midarrow>pointwise\<rightarrow> l\<close> \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> 
          \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
        by blast          
      ultimately show ?thesis using has_ell2_norm_diff
        by auto 
    qed 
    thus ?thesis unfolding has_ell2_norm_def
      by auto     
  qed 
  have \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) \<le> \<epsilon>\<close>
    for \<epsilon> :: real
  proof-
    assume \<open>(\<epsilon>::real) > (0::real)\<close>
    have \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) \<le> \<epsilon>\<close>
    proof-                             
      have \<open>\<forall> S::'a set. \<exists> M::nat. \<forall> n \<ge> M.
         finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>/2\<close>
      proof-
        have \<open>\<epsilon> > 0 \<Longrightarrow> \<forall> S::'a set. \<exists> M::nat. \<forall> n \<ge> M.
           finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
          for \<epsilon>::real
        proof-
          assume \<open>\<epsilon> > 0\<close>
          have \<open>\<exists> M::nat. \<forall> n \<ge> M.
           finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
            for S :: \<open>'a set\<close>
          proof- 
            from \<open>a \<midarrow>pointwise\<rightarrow> l\<close>
            have \<open>(\<lambda> n. (a n) x) \<longlonglongrightarrow> l x\<close>
              for x::'a
              by (simp add: pointwise_convergent_to_def)
            hence \<open>\<forall> x::'a. \<forall> \<epsilon> > 0. \<exists> N. \<forall> n \<ge> N. dist ((a n) x) (l x) < \<epsilon>\<close>
              by (meson LIMSEQ_iff_nz)
            hence \<open>\<forall> x::'a. \<forall> \<epsilon> > 0. \<exists> N. \<forall> n \<ge> N. cmod ( ((a n) x) - (l x) ) < \<epsilon>\<close>
              by (simp add: dist_norm)
            then obtain NN where \<open>\<forall> x::'a. \<forall> \<epsilon> > 0. \<forall> n \<ge>  NN x \<epsilon>. cmod ( ((a n) x) - (l x) ) < \<epsilon>\<close>
              by metis
            define NS::\<open>'a set \<Rightarrow> real \<Rightarrow> nat\<close> where
              \<open>NS \<equiv> (\<lambda> S. \<lambda> \<epsilon>. Sup {NN x (\<epsilon>/(card S))| x. x \<in> S})\<close>
            have \<open>n \<ge> NS S \<epsilon> \<Longrightarrow> finite' S \<Longrightarrow>
                 sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>/(sqrt (card S))\<close>
              for n
            proof- 
              assume \<open>n \<ge> NS S \<epsilon>\<close>
              assume \<open>finite' S\<close>
              hence \<open>{NN x (\<epsilon>/(card S))| x. x \<in> S} \<noteq> {}\<close>
                by simp
              have \<open>bdd_above {NN x (\<epsilon>/(card S))| x. x \<in> S}\<close>
                using \<open>finite' S\<close> by simp
              have \<open>card S \<noteq> 0\<close> 
                using \<open>finite' S\<close> by simp
              hence \<open>\<forall> x::'a. \<forall> \<epsilon> > 0. \<forall> n \<ge> NN x (\<epsilon>/(card S)). cmod ( ((a n) x) - (l x) ) < \<epsilon>/(card S)\<close>
                using \<open>\<forall>x \<epsilon>. 0 < \<epsilon> \<longrightarrow> (\<forall>n\<ge>NN x \<epsilon>. cmod (a n x - l x) < \<epsilon>)\<close> by auto
              hence \<open>\<forall> x::'a. \<forall> n \<ge> NN x (\<epsilon>/(card S)). cmod ( ((a n) x) - (l x) ) < \<epsilon>/(card S)\<close>
                using \<open>\<epsilon> > 0\<close> by blast
              hence \<open>\<forall> x\<in>S. \<forall> n \<ge> NN x (\<epsilon>/(card S)). cmod ( ((a n) x) - (l x) ) < \<epsilon>/(card S)\<close>
                by blast
              hence \<open>\<forall> x\<in>S. \<forall> n \<ge> NS S \<epsilon>. cmod ( ((a n) x) - (l x) ) < \<epsilon>/(card S)\<close>
              proof-
                have \<open>x\<in>S \<Longrightarrow> n \<ge> NS S \<epsilon> \<Longrightarrow> cmod ( ((a n) x) - (l x) ) < \<epsilon>/(card S)\<close>
                  for x n
                proof-
                  assume \<open>x \<in> S\<close>
                  assume \<open>n \<ge> NS S \<epsilon>\<close>
                  hence \<open>n \<ge> NN x (\<epsilon>/(card S))\<close>
                    using  \<open>{NN x (\<epsilon>/(card S))| x. x \<in> S} \<noteq> {}\<close>
                      \<open>bdd_above {NN x (\<epsilon>/(card S))| x. x \<in> S}\<close>
                    by (metis (mono_tags, lifting) NS_def \<open>x \<in> S\<close> cSup_upper mem_Collect_eq order.trans)
                  thus ?thesis 
                    using  \<open>\<forall> x\<in>S. \<forall> n \<ge> NN x (\<epsilon>/(card S)). cmod ( ((a n) x) - (l x) ) < \<epsilon>/(card S)\<close>
                      \<open>x \<in> S\<close> by blast
                qed
                thus ?thesis by blast
              qed
              hence \<open>\<forall> n \<ge> NS S \<epsilon>. (\<forall> x\<in>S. cmod ( ((a n) x) - (l x) ) < \<epsilon>/(card S))\<close>
                by blast
              hence \<open>\<forall> n \<ge> NS S \<epsilon>. (\<forall> x\<in>S. (cmod ( ((a n) x) - (l x) ))^2 < (\<epsilon>/(card S))^2)\<close>
                by (simp add: power_strict_mono)
              hence \<open>n \<ge> NS S \<epsilon> \<Longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ( ((a n) x) - (l x) ))^2) < \<epsilon>/ (sqrt (card S))\<close>
                for n
              proof-
                assume \<open>n \<ge> NS S \<epsilon>\<close>
                hence \<open>x\<in>S \<Longrightarrow> (cmod ( ((a n) x) - (l x) ))^2 < (\<epsilon>/(card S))^2\<close>
                  for x
                  by (simp add: \<open>\<forall>n\<ge>NS S \<epsilon>. \<forall>x\<in>S. (cmod (a n x - l x))\<^sup>2 < (\<epsilon> / real (card S))\<^sup>2\<close>)
                hence \<open>(\<Sum> x \<in> S. (cmod ( ((a n) x) - (l x) ))^2) < (\<Sum> x \<in> S. (\<epsilon>/(card S))^2)\<close>
                  using \<open>finite' S\<close> sum_strict_mono
                  by smt
                hence \<open>(\<Sum> x \<in> S. (cmod ( ((a n) x) - (l x) ))^2) < (card S) * (\<epsilon>/(card S))^2\<close>
                  by simp
                hence \<open> (\<Sum> x \<in> S. (cmod ( ((a n) x) - (l x) ))^2) < (card S) * \<epsilon>^2/(card S)^2\<close>
                  by (simp add: power_divide) 
                hence \<open> (\<Sum> x \<in> S. (cmod ( ((a n) x) - (l x) ))^2) < \<epsilon>^2/(card S)\<close>
                  by (metis (no_types, lifting) of_nat_power power2_eq_square real_divide_square_eq)
                hence \<open>sqrt (\<Sum> x \<in> S. (cmod ( ((a n) x) - (l x) ))^2) < sqrt (\<epsilon>^2/(card S))\<close>
                  using real_sqrt_less_iff by blast
                hence \<open>sqrt (\<Sum> x \<in> S. (cmod ( ((a n) x) - (l x) ))^2) < (sqrt (\<epsilon>^2))/ (sqrt (card S))\<close>
                  by (simp add: real_sqrt_divide)
                hence \<open>sqrt (\<Sum> x \<in> S. (cmod ( ((a n) x) - (l x) ))^2) < \<epsilon>/ (sqrt (card S))\<close>
                  using \<open>\<epsilon> > 0\<close> by simp
                thus ?thesis by blast
              qed
              thus ?thesis using \<open>NS S \<epsilon> \<le> n\<close>
                by auto
            qed 
            hence \<open>n \<ge> NS S \<epsilon> \<Longrightarrow> finite' S \<Longrightarrow>
                 sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
              for n
            proof-
              assume \<open>n \<ge> NS S \<epsilon>\<close>
              moreover assume \<open>finite' S\<close>
              ultimately have \<open>sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>/(sqrt (card S))\<close>
                using \<open>\<And>n. \<lbrakk>NS S \<epsilon> \<le> n; finite' S\<rbrakk> \<Longrightarrow> sqrt (\<Sum>x\<in>S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon> / sqrt (real (card S))\<close> by auto
              moreover have \<open>sqrt (card S) \<ge> 1\<close>
              proof-
                have \<open>card S \<ge> 1\<close> using \<open>finite' S\<close>
                  by (simp add: leI)
                thus ?thesis by simp
              qed
              ultimately show ?thesis
              proof -
                have f1: "\<not> (1::real) \<le> 0"
                  by auto
                have f2: "\<forall>x1. ((0::real) < x1) = (\<not> x1 \<le> 0)"
                  by auto
                have f3: "\<forall>x0 x1 x2 x3. ((x3::real) / x0 \<le> x2 / x1) = (x3 / x0 + - 1 * (x2 / x1) \<le> 0)"
                  by auto
                have "0 \<le> \<epsilon>"
                  using \<open>0 < \<epsilon>\<close> by linarith
                then have "\<epsilon> / sqrt (real (card S)) + - 1 * (\<epsilon> / 1) \<le> 0"
                  using f3 f2 f1 \<open>1 \<le> sqrt (real (card S))\<close> nice_ordered_field_class.frac_le by blast
                then show ?thesis
                  using \<open>sqrt (\<Sum>x\<in>S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon> / sqrt (real (card S))\<close> by force
              qed 
            qed
            thus ?thesis
              by blast 
          qed  
          thus ?thesis by blast
        qed
        moreover have \<open>\<epsilon>/2 > 0\<close> using \<open>\<epsilon> > 0\<close> by simp
        thus ?thesis
          using calculation by blast 
      qed
      moreover have \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. 
        finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) < \<epsilon>/2\<close>
      proof-
        have \<open>\<epsilon>/2 > (0::real)\<close>
          using \<open>\<epsilon> > (0::real)\<close>
          by auto
        have \<open>(\<epsilon>/4)^2 > (0::real)\<close>
          using \<open>\<epsilon> > (0::real)\<close>
          by auto
        have \<open>(\<epsilon>/4) < (\<epsilon>/2)\<close>
          using \<open>\<epsilon> > (0::real)\<close>
          by auto
        hence \<open>(\<epsilon>/4)^2 < (\<epsilon>/2)^2\<close>
          by (smt \<open>0 < \<epsilon>\<close> divide_less_0_iff power2_eq_iff_nonneg power2_less_imp_less)  
        hence \<open>\<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> (\<epsilon>/4)^2\<close>
          using \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
            \<open>(\<epsilon>/4)^2 > (0::real)\<close> by smt
        hence \<open>\<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2) < (\<epsilon>/2)^2\<close>
          using \<open>(\<epsilon>/4)^2 < (\<epsilon>/2)^2\<close> by smt
        hence \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite' S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a k) - (a n)) x ) )^2) < (\<epsilon>/2)^2\<close>
          by auto
        hence  \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite' S
     \<longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a k) - (a n)) x ) )^2) < sqrt ((\<epsilon>/2)^2)\<close>
          using real_sqrt_less_iff by presburger 
        moreover have \<open> sqrt ((\<epsilon>/2)^2) = \<epsilon>/2\<close>
          using \<open>\<epsilon>/2 > 0\<close> by simp
        ultimately show ?thesis by simp
      qed
      ultimately have \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> M. \<forall> n \<ge> M. finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
      proof-
        have \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> M::nat. \<forall> n. 
       n \<ge> N \<and> n \<ge> M \<and>  finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>/2 + \<epsilon>/2\<close>
        proof-
          have  \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<forall> n. 
        n \<ge> N \<and> finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) < \<epsilon>/2\<close>
            using \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. 
        finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) < \<epsilon>/2\<close>
            by blast
          thus ?thesis using
              \<open>\<forall> S::'a set. \<exists> M::nat. \<forall> n \<ge> M.
         finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>/2\<close>
            by smt
        qed 
        hence  \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> M::nat. \<forall> n. 
       n \<ge> N \<and> n \<ge> M \<and>  finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
          using add_le_same_cancel2 by auto
        hence \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> M::nat. \<forall> n::nat. 
       n \<ge> Sup {N, M} \<and>  finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
        proof-
          have \<open>n \<ge> Sup {N, M} \<Longrightarrow> n \<ge> N \<and> n \<ge> M\<close>
            for n N M :: nat
            by (simp add: cSup_le_iff)
          thus ?thesis using \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> M::nat. \<forall> n. 
       n \<ge> N \<and> n \<ge> M \<and>  finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
            by metis
        qed
        hence \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> K::nat. \<forall> n. 
       n \<ge> K \<and> finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
          by metis
        hence \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> K::nat. \<forall> n. 
       n \<ge> K \<and> finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
          by auto
        thus ?thesis
          by meson 
      qed
      moreover have \<open> 
        finite' S \<Longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) \<le> 
          sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2)\<close>
        for k n :: nat and S::\<open>'a set\<close>
      proof-
        assume \<open>finite' S\<close>
        hence \<open>finite S\<close> by simp
        define f where
          \<open>f \<equiv>  ((a k)  - (a n))\<close>
        define g where
          \<open>g \<equiv>  ((a n)  - l)\<close>
        have \<open>sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2)
        =  sqrt (\<Sum> x \<in> S. (cmod ( ((a k)  - (a n) ) x + ((a n)  - l ) x ))\<^sup>2)\<close>
          by simp
        also have \<open>...
        =  sqrt (\<Sum> x \<in> S. (cmod ( f x + g x ))\<^sup>2)\<close>
          using  \<open>f \<equiv>  ((a k)  - (a n))\<close>  \<open>g \<equiv>  ((a n)  - l)\<close>
          by simp
        also have  \<open>... \<le>  sqrt (\<Sum> x \<in> S. (cmod ( f x ))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod (g x))\<^sup>2)\<close>
          using  \<open>finite S\<close> triangIneq_ell2 
          by blast
        also have \<open>... \<le>  sqrt (\<Sum> x \<in> S. (cmod ( ((a k) - (a n)) x ))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod (((a n) - l) x))\<^sup>2)\<close>
          using  \<open>f \<equiv>  ((a k)  - (a n))\<close>  \<open>g \<equiv>  ((a n)  - l)\<close>
          by simp
        finally show ?thesis by blast
      qed
      ultimately have \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) < \<epsilon>\<close>
      proof-
        obtain N where
          \<open>\<forall> k \<ge> N. \<forall> S::'a set. \<exists> M. \<forall> n \<ge> M. finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
          using \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> M. \<forall> n \<ge> M. finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
          by blast
        have \<open>k \<ge> N \<Longrightarrow> \<forall> S::'a set. finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) < \<epsilon>\<close>
          for k::nat
        proof-
          assume \<open>k \<ge> N\<close>
          have \<open>finite' S \<Longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) < \<epsilon>\<close>
            for S::\<open>'a set\<close>
          proof-
            assume \<open>finite' S\<close>
            obtain M where \<open>\<forall> n \<ge> M. sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
              using \<open>\<forall> k \<ge> N. \<forall> S::'a set. \<exists> M. \<forall> n \<ge> M. finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
                \<open>finite' S\<close> \<open>k \<ge> N\<close>
              by metis
            from \<open>finite' S\<close>
            have \<open>sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) \<le> 
          sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2)\<close>
              for n::nat
              using \<open>\<And>n k S. finite' S \<Longrightarrow> sqrt (\<Sum>x\<in>S. (cmod ((a k - l) x))\<^sup>2) \<le> sqrt (\<Sum>x\<in>S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum>x\<in>S. (cmod ((a n - l) x))\<^sup>2)\<close>
              by blast               
            hence \<open>\<forall> n \<ge> M. sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) < \<epsilon>\<close>              
              using \<open>\<forall> n \<ge> M. sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
              by smt              
            thus ?thesis by blast
          qed
          thus ?thesis by blast
        qed
        thus ?thesis by blast
      qed
      thus ?thesis by smt
    qed 
    thus ?thesis
      by (metis (mono_tags) \<open>0 < \<epsilon>\<close> assms(3) real_sqrt_zero sum.empty) 
  qed
  have \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> k \<ge> N. Sup { sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2)  | S::'a set. finite S } \<le> \<epsilon>\<close>
    for \<epsilon> :: real
  proof-
    assume \<open>\<epsilon> > 0\<close>
    hence \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  \<le> \<epsilon>\<close>
      using  \<open>\<And> \<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  \<le> \<epsilon>\<close>
      by blast
    then obtain N where \<open>\<forall> k \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2) \<le> \<epsilon>\<close>
      by blast
    have \<open>{ sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } \<noteq> {}\<close>
      for k::nat
      by blast
    moreover have \<open>bdd_above { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S }\<close>
      for k::nat
    proof- 
      from \<open>\<And> k::nat. bdd_above (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite)\<close>
      have \<open>bdd_above { (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S }\<close>
        by (simp add: setcompr_eq_image)
      then obtain M where  \<open>\<forall> S::'a set. finite S \<longrightarrow> (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2) \<le> M\<close>
        using bdd_above_def
          \<open>\<And>k. bdd_above (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite)\<close> has_ell2_norm_def has_ell2_norm_explicit by fastforce 
      hence  \<open>\<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2) \<le> sqrt M\<close>
        by simp
      thus ?thesis  using bdd_above_def
        by (smt mem_Collect_eq) 
    qed 
    ultimately have \<open>(Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } \<le> \<epsilon>) 
\<longleftrightarrow> (\<forall> x \<in> { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S }. x \<le> \<epsilon>)\<close>
      for k :: nat
      by (simp add: cSup_le_iff)
    have \<open>\<forall> k \<ge> N. \<forall> x \<in> { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S }. x \<le> \<epsilon>\<close>
      using  \<open>\<forall> k \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2) \<le> \<epsilon>\<close>
      by auto
    thus ?thesis using  \<open>\<And> k. (Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } \<le> \<epsilon>) 
\<longleftrightarrow> (\<forall> x \<in> { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S }. x \<le> \<epsilon>)\<close>
      by blast
  qed 
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> k \<ge> N. Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } \<le> \<epsilon>\<close>
    by blast
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> k \<ge> N. Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } < \<epsilon>\<close>
  proof-
    from \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> k \<ge> N. Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } \<le> \<epsilon>\<close>
    have \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> k \<ge> N. Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } \<le> \<epsilon>/2\<close>
      using half_gt_zero_iff by blast
    moreover have \<open>\<forall> (\<epsilon>::real) > 0. \<epsilon> / 2 < \<epsilon>\<close>
      by simp
    ultimately show ?thesis by fastforce
  qed
  moreover have \<open>ell2_norm (a k - l) = Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S }\<close>
    for k::nat
  proof-
    have \<open>has_ell2_norm l\<close>
      using convergence_pointwise_ell2_norm_exists
        \<open>a \<midarrow>pointwise\<rightarrow> l\<close> \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> 
        \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
      by blast
    hence \<open>has_ell2_norm (a k - l)\<close>
      using  \<open>\<forall> k::nat. has_ell2_norm (a k)\<close>
        has_ell2_norm_diff
      by blast
    thus ?thesis using ellnorm_as_sup_set
      by blast 
  qed
  ultimately have \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> k \<ge> N. ell2_norm (a k - l) < \<epsilon>\<close>
    by simp
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> k \<ge> N. (sqrt (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))) < \<epsilon>\<close>
    using ell2_norm_def by metis
  have \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> k \<ge> N. \<bar> (sqrt (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))) \<bar> < \<epsilon>\<close>
  proof-
    obtain x where
      \<open>x \<in> (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite)\<close>
    for k::nat
      by (metis finite.emptyI image_iff mem_Collect_eq sum.empty)      
    moreover have \<open>(0::real) \<le> x\<close>
    proof-
      from \<open>\<And> k. x \<in> (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite)\<close>
      obtain S k where \<open>x = sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) S\<close>
        by (meson image_iff)
      have  \<open>\<forall> i\<in>S. (cmod ((a k - l) i))\<^sup>2 \<ge> 0\<close>
        by simp
      thus ?thesis
        by (simp add: \<open>x = (\<Sum>i\<in>S. (cmod ((a k - l) i))\<^sup>2)\<close> sum_nonneg)
    qed 
    ultimately have \<open>(0::real) \<le> (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))\<close>
      for k::nat 
      using \<open>\<And> k::nat. bdd_above (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite)\<close>
        cSup_upper2
      by blast  
    thus ?thesis 
      using NthRoot.real_sqrt_ge_zero  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> k \<ge> N. (sqrt (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))) < \<epsilon>\<close>
      by simp
  qed
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> k \<ge> N. dist (sqrt (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))) 0 < \<epsilon>\<close>
    by simp
  hence \<open>(\<lambda>k. sqrt (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))) \<longlonglongrightarrow> 0\<close>
    by (simp add: metric_LIMSEQ_I)
  thus ?thesis unfolding ell2_norm_def by blast 
qed


lemma ell2_Cauchy_pointwiseConverges:
  fixes a :: \<open>nat \<Rightarrow> ('a \<Rightarrow> complex)\<close>
  assumes  \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> 
    and \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
  shows \<open>\<exists> l. (a \<midarrow>pointwise\<rightarrow> l)\<close>
proof-
  have \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( ((a m) x) - ((a n) x) ) \<le> \<epsilon>\<close>
    for \<epsilon> :: real and x::'a 
  proof-
    assume \<open>\<epsilon> > 0\<close>
    hence \<open>\<epsilon>^2 > 0\<close>
      by simp
    hence \<open>\<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>^2\<close>
      using  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
      by blast
    then obtain N
      where \<open>\<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>^2\<close>
      by blast
    have \<open>m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> cmod ( ((a m) x) - ((a n) x) ) \<le> \<epsilon>\<close>
      for m n
    proof- 
      assume \<open>m \<ge> N\<close>
      moreover assume \<open>n \<ge> N\<close>
      ultimately have \<open>\<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>^2\<close>
        using \<open>\<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>^2\<close>
        by blast
      moreover have \<open>finite {x}\<close>
        by auto
      ultimately have \<open>(\<Sum> t\<in>{x}. ( cmod ( ((a m) t) - ((a n) t) ) )^2)  \<le> \<epsilon>^2\<close>        
        by blast
      hence \<open> ( cmod ( ((a m) x) - ((a n) x) ) )^2  \<le> \<epsilon>^2\<close>        
        by simp
      moreover have \<open> cmod ( ((a m) x) - ((a n) x) ) \<ge> 0\<close>
        by simp
      ultimately have \<open> ( cmod ( ((a m) x) - ((a n) x) ) )  \<le> \<epsilon>\<close>        
        using \<open>\<epsilon> > 0\<close>
        using power2_le_imp_le by fastforce   
      thus ?thesis by blast
    qed 
    thus ?thesis by blast
  qed 
  hence \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) \<le> \<epsilon>\<close>
    for \<epsilon> :: real and x::'a 
    by blast
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) \<le> \<epsilon>\<close>
    for x::'a 
    by blast
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) < \<epsilon>\<close>
    for x::'a 
  proof-
    from \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) \<le> \<epsilon>\<close>
    have \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) \<le> \<epsilon>/2\<close>
      using half_gt_zero by blast
    hence \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) < \<epsilon>\<close>
      for \<epsilon>::real
    proof-
      assume \<open>\<epsilon> > 0\<close>
      hence \<open> \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) \<le> \<epsilon>/2\<close>
        using  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) \<le> \<epsilon>/2\<close>
        by blast
      moreover have \<open>\<epsilon>/2 < \<epsilon>\<close>
        using \<open>\<epsilon> > 0\<close>
        by simp
      ultimately show ?thesis by smt
    qed
    thus ?thesis 
      by blast
  qed
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  dist ((\<lambda> k. (a k) x) m) ((\<lambda> k. (a k) x) n)  < \<epsilon>\<close>
    for x::'a
    by (simp add: dist_norm)  
  hence \<open>Cauchy (\<lambda> k. (a k) x)\<close>
    for x::'a
    using Cauchy_altdef2 by fastforce     
  hence \<open>\<exists> r::complex. (\<lambda> n. (a n) x ) \<longlonglongrightarrow> r\<close>
    for x::'a
    by (simp add: convergent_eq_Cauchy) 
  hence \<open>\<exists> l::'a \<Rightarrow> complex. \<forall> x::'a. (\<lambda> n. (a n) x ) \<longlonglongrightarrow> l x\<close>
    by metis                                        
  thus ?thesis 
    unfolding pointwise_convergent_to_def
    by blast    
qed


lemma completeness_ell2:
  fixes a :: \<open>nat \<Rightarrow> ('a \<Rightarrow> complex)\<close>
  assumes  \<open>\<forall> k::nat. has_ell2_norm (a k)\<close>
    \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a m x - a n x) < \<epsilon>\<close>
  shows "\<exists>l. has_ell2_norm l \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a n x - l x) < \<epsilon>)" 
proof-
  have  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
  proof-
    have \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
      for \<epsilon>::real
    proof-
      assume \<open>\<epsilon> > 0\<close>
      hence \<open>sqrt \<epsilon> > 0\<close> by simp
      then obtain N where \<open>\<forall>m\<ge>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a m x - a n x) < sqrt \<epsilon>\<close>
        using \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a m x - a n x) < \<epsilon>\<close>
        by smt
      hence  \<open>\<forall>m\<ge>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a m x - a n x) \<le> sqrt \<epsilon>\<close>
        by fastforce
      have  \<open>m\<ge>N \<Longrightarrow> n\<ge>N \<Longrightarrow> \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
        for m n
      proof-
        assume \<open>m \<ge> N\<close>
        assume \<open>n \<ge> N\<close>
        have \<open>ell2_norm (\<lambda>x. a m x - a n x) \<le> sqrt \<epsilon>\<close>
          using  \<open>\<forall>m\<ge>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a m x - a n x) \<le> sqrt \<epsilon>\<close>
            \<open>m \<ge> N\<close>  \<open>n \<ge> N\<close>
          by blast
        have \<open>has_ell2_norm (a m)\<close>
          by (simp add: assms(1))          
        moreover have \<open>has_ell2_norm (a n)\<close>
          by (simp add: assms(1))
        ultimately have \<open>has_ell2_norm (a m - a n)\<close>
          by (simp add: has_ell2_norm_diff)
        hence  \<open>ell2_norm (a m - a n) = Sup { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S }\<close>
          using ellnorm_as_sup_set
          by blast
        have \<open>{ sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S } \<noteq> {}\<close>
          by blast
        have \<open>bdd_above { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S }\<close>
        proof-
          have \<open>bdd_above (sum (\<lambda>i. (cmod ((a m - a n) i))\<^sup>2) ` Collect finite)\<close>
            using  \<open>has_ell2_norm (a m - a n)\<close>
            unfolding has_ell2_norm_def
            by blast
          hence \<open>bdd_above { (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S }\<close>
            by (simp add: setcompr_eq_image)
          then obtain M where \<open> finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> M \<close>
            for S::\<open>'a set\<close>
            using \<open>has_ell2_norm (a m - a n)\<close> has_ell2_norm_explicit by blast
          have \<open>finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<ge> 0\<close> 
            for S :: \<open>'a set\<close>
            by (simp add: sum_nonneg)
          have \<open>finite S \<Longrightarrow> M \<ge> 0\<close>
            for S::\<open>'a set\<close>
            using  \<open>\<And> S. finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> M \<close>
              \<open>\<And> S. finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<ge> 0\<close> 
            by force
          hence \<open>M \<ge> 0\<close>
            by blast
          have  \<open> finite S \<Longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> sqrt M \<close>
            for S::\<open>'a set\<close>
            using  \<open>M \<ge> 0\<close>  \<open>\<And> S. finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> M \<close>
              \<open>\<And> S. finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<ge> 0\<close>
            by simp
          thus ?thesis
            by (smt bdd_aboveI mem_Collect_eq)   
        qed
        have \<open>(\<lambda> x. a m x - a n x) = a m - a n\<close>
          by auto
        hence \<open>ell2_norm (a m - a n) \<le> sqrt \<epsilon>\<close> 
          using  \<open>ell2_norm (\<lambda> x. a m x - a n x) \<le> sqrt \<epsilon>\<close> 
          by simp
        hence \<open>Sup { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S } \<le> sqrt \<epsilon>\<close>
          using  \<open>ell2_norm (a m - a n) \<le> sqrt \<epsilon>\<close>  \<open>ell2_norm (a m - a n) = Sup { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S }\<close>
          by simp
        moreover have \<open>finite S \<Longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> Sup { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S }\<close>
          for S::\<open>'a set\<close>
        proof-
          assume \<open>finite S\<close>
          hence \<open>sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<in> { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S }\<close>
            by blast
          thus ?thesis
            by (metis (no_types, lifting) \<open>bdd_above {sqrt (\<Sum>i\<in>S. (cmod ((a m - a n) i))\<^sup>2) |S. finite S}\<close> cSup_upper)  
        qed 
        ultimately have \<open>finite S \<Longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> sqrt \<epsilon>\<close>
          for S :: \<open>'a set \<close>
          by (smt \<open>0 < \<epsilon>\<close> real_sqrt_le_mono sum.infinite)
        hence  \<open>finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> \<epsilon>\<close>
          for S :: \<open>'a set \<close>
          by simp
        thus ?thesis by auto 
      qed
      thus ?thesis
        by blast 
    qed
    thus ?thesis by blast
  qed
  have  \<open>\<exists> l. (a \<midarrow>pointwise\<rightarrow> l)\<close>
    using ell2_Cauchy_pointwiseConverges
      \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
      \<open>\<forall> k::nat. has_ell2_norm (a k)\<close>
    by blast
  then   obtain l :: \<open>'a \<Rightarrow> complex\<close> where  \<open>a \<midarrow>pointwise\<rightarrow> l\<close>
    by blast
  have \<open>has_ell2_norm l\<close> using convergence_pointwise_ell2_norm_exists 
    using  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
      \<open>a \<midarrow>pointwise\<rightarrow> l\<close>  \<open>\<forall> k::nat. has_ell2_norm (a k)\<close>
    by blast
  moreover have \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a n x - l x) < \<epsilon>\<close> 
  proof-
    have  \<open>( \<lambda> k. ell2_norm ( (a k) - l ) ) \<longlonglongrightarrow> 0\<close>
      using convergence_pointwise_to_ell2_same_limit  
        \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
        \<open>a \<midarrow>pointwise\<rightarrow> l\<close>  \<open>\<forall> k::nat. has_ell2_norm (a k)\<close>
      by blast
    hence  \<open>\<forall> \<epsilon>>0. \<exists> N. \<forall> k \<ge> N. dist ( ell2_norm ( (a k) - l ) ) 0 < \<epsilon>\<close>
      using metric_LIMSEQ_D by blast
    hence  \<open>\<forall> \<epsilon>>0. \<exists> N. \<forall> k \<ge> N.  \<bar>ell2_norm ( (a k) - l ) \<bar>  < \<epsilon>\<close>
      by simp
    hence  \<open>\<forall> \<epsilon>>0. \<exists> N. \<forall> k \<ge> N.  ell2_norm ( (a k) - l )   < \<epsilon>\<close>
      by (metis diff_zero dist_commute dist_real_def lemma_interval_lt nice_ordered_field_class.linordered_field_no_lb)
    hence \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. ell2_norm (\<lambda>x. (a k - l) x) < \<epsilon>\<close>
      by smt
    thus ?thesis by simp
  qed 
  ultimately show ?thesis by blast
qed                                                    

instantiation ell2 :: (type) chilbert_space
begin
instance
proof
  fix X :: "nat \<Rightarrow> 'a ell2"
  assume cauchy: "Cauchy (X::nat \<Rightarrow> 'a ell2)"
  then have "\<exists>l. X \<longlonglongrightarrow> l"
    unfolding LIMSEQ_def Cauchy_def dist_norm
    apply transfer apply simp
    apply (rule completeness_ell2)
    by auto
  thus "convergent (X::nat \<Rightarrow> 'a ell2)"
    using convergent_def by blast
qed
end

lemma ell2_ket[simp]: "norm (ket i) = 1"
  apply transfer unfolding ell2_norm_def real_sqrt_eq_1_iff
  apply (rule cSUP_eq_maximum)
   apply (rule_tac x="{i}" in bexI)
    apply auto
  by (rule ell2_1)

type_synonym 'a subspace = "'a ell2 linear_space"

instance ell2 :: (type) not_singleton
proof standard
  have "ket undefined \<noteq> (0::'a ell2)"
    apply transfer
    thm one_neq_zero
    by (meson one_neq_zero)
  thus "CARD('a ell2) \<noteq> 1"
    by (metis (full_types) UNIV_I card_1_singletonE singletonD the_elem_eq)
qed


instantiation ell2 :: (enum) basis_enum begin
definition "canonical_basis_ell2 = map ket Enum.enum"
definition "canonical_basis_length_ell2 (_::'a ell2 itself) = CARD('a)"
instance
proof
  show "distinct (canonical_basis::'a ell2 list)"
    unfolding distinct_def canonical_basis_ell2_def 
    apply transfer
    apply (induction enum_class.enum)    
    by (cheat ell2_basis_enum)

  show "is_onb (set (canonical_basis::'a ell2 list))"
    by (cheat ell2_basis_enum)
  show "canonical_basis_length (TYPE('a ell2)::'a ell2 itself) = length (canonical_basis::'a ell2 list)"
    by (cheat ell2_basis_enum)
qed
end

definition left_shift :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)\<close> where
  \<open>left_shift x = (\<lambda> n. x (Suc n))\<close>

lift_definition left_shift_ell2 :: \<open>nat ell2 \<Rightarrow> nat ell2\<close> is left_shift
proof-
  fix x :: \<open>nat \<Rightarrow> complex\<close>
  show \<open>has_ell2_norm x \<Longrightarrow> has_ell2_norm (left_shift x)\<close>
  proof-
    define f where \<open>f n = (cmod (x n))^2\<close> for n :: nat
    define g :: \<open>nat \<Rightarrow> real\<close>  where \<open>g \<equiv> (\<lambda> n. (cmod (x (Suc n)))^2)\<close>
    assume \<open>has_ell2_norm x\<close>
    hence \<open>(\<lambda> n. (cmod (x n))^2) abs_summable_on UNIV\<close>
      using has_ell2_norm_infsetsum by fastforce
    hence \<open>summable (\<lambda> m. (cmod (x m))^2)\<close>
      using abs_summable_on_nat_iff' summable_norm_cancel by blast
    hence \<open>summable f\<close>
      unfolding f_def by blast
    hence \<open>summable (\<lambda> n::nat. f (Suc n))\<close>
      using Series.summable_Suc_iff by blast
    hence \<open>summable (\<lambda> n. (\<lambda> m. (cmod (x m))^2) (Suc n))\<close>
      unfolding f_def by blast     
    hence \<open>summable (\<lambda> n. (cmod (x (Suc n)))^2)\<close>
      by blast
    hence \<open>summable (\<lambda> n. g n)\<close>
      using g_def by blast
    have \<open>summable (\<lambda> n. norm (g n))\<close>
    proof-
      have \<open>norm (g n) = g n\<close>
        for n
      proof-
        have \<open>g n \<ge> 0\<close>
          unfolding g_def
          by simp 
        thus ?thesis by auto
      qed
      thus ?thesis
        by (simp add: \<open>summable g\<close>) 
    qed
    hence \<open>g abs_summable_on UNIV\<close>
      by (simp add: abs_summable_on_nat_iff')
    hence \<open> (\<lambda> n. (cmod (x (Suc n)))^2) abs_summable_on UNIV\<close>
      using g_def by blast      
    hence \<open>has_ell2_norm (left_shift x)\<close>
      by (simp add: \<open>(\<lambda>n. (cmod (x (Suc n)))\<^sup>2) abs_summable_on UNIV\<close> has_ell2_norm_infsetsum left_shift_def)
    thus ?thesis
      by simp 
  qed
qed

lemma left_shift_ell2_clinear:
  \<open>clinear left_shift_ell2\<close>
  unfolding clinear_def
proof
  show "left_shift_ell2 (b1 + b2) = left_shift_ell2 b1 + left_shift_ell2 b2"
    for b1 :: "nat ell2"
      and b2 :: "nat ell2"
    apply transfer
    unfolding left_shift_def
    by simp
  show "left_shift_ell2 (r *\<^sub>C b) = r *\<^sub>C left_shift_ell2 b"
    for r :: complex
      and b :: "nat ell2"
    apply transfer
    unfolding left_shift_def
    by simp
qed

lemma shift_ket:
  fixes n :: nat
  shows \<open>left_shift_ell2 (ket (Suc n)) = ket n\<close>
  apply transfer
  unfolding left_shift_def ket_def
  by auto


lemma shift_ket0:
  \<open>left_shift_ell2 (ket (0::nat)) = 0\<close>
  apply transfer
  unfolding left_shift_def ket_def
  by auto


lemma ket_Kronecker_delta_eq:
  \<open>\<langle>ket i, ket i\<rangle> = 1\<close>
proof-
  have \<open>norm (ket i) = 1\<close>
    by simp
  hence \<open>sqrt (cmod \<langle>ket i, ket i\<rangle>) = 1\<close>
    by (metis norm_eq_sqrt_cinner)
  hence \<open>cmod \<langle>ket i, ket i\<rangle> = 1\<close>
    using real_sqrt_eq_1_iff by blast
  moreover have \<open>\<langle>ket i, ket i\<rangle> = cmod \<langle>ket i, ket i\<rangle>\<close>
  proof-
    have \<open>\<langle>ket i, ket i\<rangle> \<in> \<real>\<close>
      by (simp add: cinner_real)      
    thus ?thesis 
      by (metis cinner_ge_zero complex_of_real_cmod) 
  qed
  ultimately show ?thesis by simp
qed

lemma ket_Kronecker_delta_neq:
  \<open>i \<noteq> j \<Longrightarrow> \<langle>ket i, ket j\<rangle> = 0\<close>
proof-
  assume \<open>i \<noteq> j\<close>
  have \<open>\<langle>ket i, ket j\<rangle> = (\<Sum>\<^sub>ak. cnj (if i = k then 1 else 0) * (if j = k then 1 else 0))\<close>
    apply transfer
    by blast
  moreover have \<open>cnj (if i = k then 1 else 0) * (if j = k then 1 else 0) = 0\<close>
    for k
    using \<open>i \<noteq> j\<close> by auto    
  ultimately show ?thesis
    by simp 
qed



section \<open>CARD_1\<close>

(* TODO: Remove this definition. CARD_1 already exists. Instead of the_single, we can use undefined *)
class CARD_1 = 
  fixes the_single :: "'a" 
  assumes everything_the_single: "x=the_single" 
begin
lemma singleton_UNIV: "UNIV = {the_single}"
  using everything_the_single by auto

lemma everything_the_same: "(x::'a)=y"
  apply (subst everything_the_single, subst (2) everything_the_single) by simp

lemma singleton_ext: "x (a::'a) = y b \<Longrightarrow> x = y"
  apply (rule ext) 
  apply (subst (asm) everything_the_same[where x=a])
  apply (subst (asm) everything_the_same[where x=b])
  by simp

lemma CARD_singleton[simp]: "CARD('a) = 1"
  by (simp add: singleton_UNIV)

subclass finite apply standard unfolding singleton_UNIV by simp
end


instantiation unit :: CARD_1
begin
definition "singleton = ()"
instance 
  apply standard 
  by auto
end


instantiation ell2 :: (CARD_1) complex_algebra_1 
begin
lift_definition one_ell2 :: "'a ell2" is "\<lambda>_. 1" by simp
lift_definition times_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a b _. a the_single * b the_single" by simp
instance 
proof
  show "(a::'a ell2) * b * c = a * (b * c)"
    for a :: "'a ell2"
      and b :: "'a ell2"
      and c :: "'a ell2"
    by (transfer, auto)
  show "((a::'a ell2) + b) * c = a * c + b * c"
    for a :: "'a ell2"
      and b :: "'a ell2"
      and c :: "'a ell2"
    apply (transfer, rule ext, auto)
    by (simp add: distrib_left mult.commute)
  show "(a::'a ell2) * (b + c) = a * b + a * c"
    for a :: "'a ell2"
      and b :: "'a ell2"
      and c :: "'a ell2"
    apply transfer apply (rule ext) apply auto
    using distrib_left by blast
  show "a *\<^sub>C (x::'a ell2) * y = a *\<^sub>C (x * y)"
    for a :: complex
      and x :: "'a ell2"
      and y :: "'a ell2"
    by (transfer, auto)
  show "(x::'a ell2) * a *\<^sub>C y = a *\<^sub>C (x * y)"
    for x :: "'a ell2"
      and a :: complex
      and y :: "'a ell2"
    by (transfer, auto)
  show "(1::'a ell2) * a = a"
    for a :: "'a ell2"
    apply (transfer, rule ext, auto simp: everything_the_single)
    by (metis (full_types) everything_the_single)
  show "(a::'a ell2) * 1 = a"
    for a :: "'a ell2"
    apply (transfer, rule ext, auto simp: everything_the_single)
    by (metis (full_types) everything_the_single)
  show "(0::'a ell2) \<noteq> 1"
    apply transfer
    by (meson zero_neq_one)
qed
end

lift_definition C1_to_complex :: "'a::CARD_1 ell2 \<Rightarrow> complex" is
  "\<lambda>\<psi>. \<psi> the_single" .

abbreviation "complex_to_C1 :: complex \<Rightarrow> 'a::CARD_1 ell2 == of_complex"

lemma C1_to_complex_one[simp]: "C1_to_complex 1 = 1"
  apply transfer by simp

lemma C1_to_complex_inverse[simp]: "complex_to_C1 (C1_to_complex \<psi>) = \<psi>"
  unfolding of_complex_def apply transfer apply (rule singleton_ext) by auto

lemma complex_to_C1_inverse[simp]: "C1_to_complex (complex_to_C1 \<psi>) = \<psi>"
  unfolding of_complex_def apply transfer by simp

lemma bounded_clinear_complex_to_C1: "bounded_clinear complex_to_C1"
  by (rule Complex_Vector_Spaces.bounded_clinear_of_complex)

lemma bounded_clinear_C1_to_complex: "bounded_clinear C1_to_complex"
  apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def singleton_UNIV)+

lift_definition ell2_to_bounded :: "'a::chilbert_space \<Rightarrow> (unit ell2,'a) bounded" is
  "\<lambda>(\<psi>::'a) (x::unit ell2). C1_to_complex x *\<^sub>C \<psi>"
  by (simp add: bounded_clinear_C1_to_complex bounded_clinear_scaleC_const)

lemma ell2_to_bounded_applyOp:
  fixes A::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close>
  shows \<open>ell2_to_bounded (Rep_bounded A \<psi>) = A *\<^sub>o ell2_to_bounded \<psi>\<close>
proof-
  have \<open>bounded_clinear (Rep_bounded A)\<close>
    using Rep_bounded by blast
  hence \<open>(\<lambda> x. C1_to_complex x *\<^sub>C (Rep_bounded A \<psi>))
     =  (\<lambda> x. (Rep_bounded A) ( C1_to_complex x *\<^sub>C \<psi>) )\<close>
    using bounded_clinear_def
    by simp 
  also have \<open>(\<lambda> x. (Rep_bounded A) ( C1_to_complex x *\<^sub>C \<psi>) )
    = (Rep_bounded A) \<circ> (\<lambda> x. C1_to_complex x *\<^sub>C \<psi>)\<close>
    unfolding comp_def
    by blast
  finally have \<open>(\<lambda> x. C1_to_complex x *\<^sub>C (Rep_bounded A \<psi>))
     = (Rep_bounded A) \<circ> (\<lambda> x. C1_to_complex x *\<^sub>C \<psi>)\<close>
    by blast
  moreover have \<open>Rep_bounded (ell2_to_bounded (Rep_bounded A \<psi>))
       = (\<lambda> x. C1_to_complex x *\<^sub>C (Rep_bounded A \<psi>))\<close>
    using Complex_L2.ell2_to_bounded.rep_eq
    by blast
  ultimately have \<open>Rep_bounded (ell2_to_bounded (Rep_bounded A \<psi>))
     = (Rep_bounded A) \<circ> (\<lambda> x. C1_to_complex x *\<^sub>C \<psi>)\<close>
    by simp
  moreover have \<open>Rep_bounded (ell2_to_bounded \<psi>) = (\<lambda> x. C1_to_complex x *\<^sub>C \<psi>)\<close>
    using Complex_L2.ell2_to_bounded.rep_eq
    by blast
  ultimately have \<open>Rep_bounded (ell2_to_bounded (Rep_bounded A \<psi>))
     = (Rep_bounded A) \<circ> (Rep_bounded (ell2_to_bounded \<psi>))\<close>
    by simp
  thus ?thesis
    apply transfer
    by simp
qed

lemma ell2_to_bounded_scalar_times: "ell2_to_bounded (a *\<^sub>C \<psi>) = a *\<^sub>C ell2_to_bounded \<psi>" 
  for a::complex
  apply (transfer fixing: a) by auto

section \<open>Classical operators\<close>

lift_definition classical_operator':: 
  "('a \<Rightarrow> 'b option) \<Rightarrow> ('a ell2 \<Rightarrow> 'b ell2)" 
  is "\<lambda>\<pi> \<psi> b. case inv_option \<pi> b of Some a \<Rightarrow> \<psi> a | None \<Rightarrow> 0"
proof-
  show \<open>has_ell2_norm \<psi> \<Longrightarrow>
        has_ell2_norm (\<lambda>b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x)\<close>
    for \<pi>::\<open>'a \<Rightarrow> 'b option\<close> and \<psi>::\<open>'a \<Rightarrow> complex\<close>
  proof-
    assume \<open>has_ell2_norm \<psi>\<close>
    hence \<open>bdd_above (sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) ` Collect finite)\<close>
      unfolding has_ell2_norm_def
      by blast
    hence \<open>\<exists> M. \<forall> S. finite S \<longrightarrow> ( sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) S ) \<le> M\<close>
      by (simp add: bdd_above_def)
    then obtain M::real where \<open>\<And> S::'a set. finite S \<Longrightarrow> ( sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) S ) \<le> M\<close>
      by blast
    define \<phi>::\<open>'b \<Rightarrow> complex\<close> where
      \<open>\<phi> b = (case inv_option \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x)\<close> for b
    have \<open>\<lbrakk>finite R; \<forall>i\<in>R. \<phi> i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> M\<close>
      for R::\<open>'b set\<close>
    proof-
      assume \<open>finite R\<close> and \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
      from  \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
      have  \<open>\<forall>i\<in>R. \<exists> x. Some x = inv_option \<pi> i\<close>
        unfolding \<phi>_def
        by (metis option.case_eq_if option.collapse)
      hence  \<open>\<exists> f. \<forall>i\<in>R. Some (f i) = inv_option \<pi> i\<close>
        by metis
      then obtain f::\<open>'b\<Rightarrow>'a\<close> where \<open>\<forall>i\<in>R. Some (f i) = inv_option \<pi> i\<close> 
        by blast
      define S::\<open>'a set\<close> where \<open>S = f ` R\<close>
      have \<open>finite S\<close>
        using \<open>finite R\<close>
        by (simp add: S_def)
      moreover have \<open>(\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) =  (\<Sum>i\<in>S. (cmod (\<psi> i))\<^sup>2)\<close>
      proof-
        have \<open>inj_on f R\<close>
        proof(rule inj_onI)
          fix x y :: 'b
          assume \<open>x \<in> R\<close> and \<open>y \<in> R\<close> and \<open>f x = f y\<close>
          from \<open>\<forall>i\<in>R. Some (f i) = inv_option \<pi> i\<close> 
          have \<open>\<forall>i\<in>R. Some (f i) = Some (inv \<pi> (Some i))\<close>
            by (metis inv_option_def option.distinct(1))
          hence \<open>\<forall>i\<in>R. f i = inv \<pi> (Some i)\<close>
            by blast
          hence \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close>
            by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_option \<pi> i\<close> f_inv_into_f inv_option_def option.distinct(1)) 
          have \<open>\<pi> (f x) = Some x\<close>
            using \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close> \<open>x\<in>R\<close> by blast
          moreover have \<open>\<pi> (f y) = Some y\<close>
            using \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close> \<open>y\<in>R\<close> by blast
          ultimately have \<open>Some x = Some y\<close>
            using \<open>f x = f y\<close> by metis
          thus \<open>x = y\<close> by simp
        qed
        moreover have \<open>i \<in> R \<Longrightarrow> (cmod (\<phi> i))\<^sup>2 = (cmod (\<psi> (f i)))\<^sup>2\<close>
          for i
        proof-
          assume \<open>i \<in> R\<close>
          hence \<open>\<phi> i = \<psi> (f i)\<close>
            unfolding \<phi>_def
            by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_option \<pi> i\<close> option.simps(5))
          thus ?thesis
            by simp 
        qed
        ultimately show ?thesis unfolding S_def
          by (metis (mono_tags, lifting) sum.reindex_cong)
      qed
      ultimately show ?thesis
        by (simp add: \<open>\<And>S. finite S \<Longrightarrow> (\<Sum>i\<in>S. (cmod (\<psi> i))\<^sup>2) \<le> M\<close>) 
    qed     
    have \<open>finite R \<Longrightarrow> ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) \<le> M\<close>
      for R::\<open>'b set\<close>
    proof-
      assume \<open>finite R\<close>
      define U::\<open>'b set\<close> where \<open>U = {i | i::'b. i \<in> R \<and>  \<phi> i \<noteq> 0 }\<close>
      define V::\<open>'b set\<close> where \<open>V = {i | i::'b. i \<in> R \<and>  \<phi> i = 0 }\<close>
      have \<open>U \<inter> V = {}\<close>
        unfolding U_def V_def by blast
      moreover have \<open>U \<union> V = R\<close>
        unfolding U_def V_def by blast
      ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U ) + 
            ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) V )\<close>
        using \<open>finite R\<close> sum.union_disjoint by auto
      moreover have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) V ) = 0\<close>
        unfolding V_def by auto
      ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U )\<close>
        by simp
      moreover have \<open>\<forall> i \<in> U. \<phi> i \<noteq> 0\<close>
        by (simp add: U_def)
      moreover have \<open>finite U\<close>
        unfolding U_def using \<open>finite R\<close>
        by simp
      ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U ) \<le> M\<close>
        using \<open>\<And>R. \<lbrakk>finite R; \<forall>i\<in>R. \<phi> i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> M\<close> by blast        
      thus ?thesis using \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U )\<close>
        by simp
    qed
    hence  \<open>bdd_above (sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) ` Collect finite)\<close>
      unfolding bdd_above_def
      by blast
    thus ?thesis
      using \<open>\<phi> \<equiv> \<lambda>b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x\<close> has_ell2_norm_def by blast 
  qed
qed

lift_definition classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> ('a ell2,'b ell2) bounded" is
  "classical_operator'"
  unfolding bounded_clinear_def clinear_def Vector_Spaces.linear_def
  apply auto
     apply (simp add: complex_vector.vector_space_axioms)
    apply (simp add: complex_vector.vector_space_axioms)
  unfolding module_hom_def module_hom_axioms_def module_def
   apply auto
        apply (simp add: scaleC_add_right)
  using scaleC_left.add apply auto[1]
      apply (simp add: scaleC_add_right)
     apply (simp add: scaleC_left.add)
    apply transfer
proof

  show "(case inv_option S (b::'b) of None \<Rightarrow> 0::complex | Some (a::'a) \<Rightarrow> b1 a + b2 a) = (case inv_option S b of None \<Rightarrow> 0 | Some x \<Rightarrow> b1 x) + (case inv_option S b of None \<Rightarrow> 0 | Some x \<Rightarrow> b2 x)"
    if "has_ell2_norm (b1::'a \<Rightarrow> complex)"
      and "has_ell2_norm (b2::'a \<Rightarrow> complex)"
    for S :: "'a \<Rightarrow> 'b option"
      and b1 :: "'a \<Rightarrow> complex"
      and b2 :: "'a \<Rightarrow> complex"
      and b :: 'b
  proof-
    have "classical_operator' \<pi> ((x::'a ell2) + y) = (classical_operator' \<pi> x::'b ell2) + classical_operator' \<pi> y"
      for \<pi> :: "'a \<Rightarrow> 'b option"
        and x :: "'a ell2"
        and y :: "'a ell2"
    proof transfer
      fix  \<pi> :: "'a \<Rightarrow> 'b option"
        and x :: "'a \<Rightarrow> complex"
        and y :: "'a \<Rightarrow> complex"
      assume \<open>has_ell2_norm x\<close> and \<open>has_ell2_norm y\<close>
      have \<open>(\<lambda>b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some a \<Rightarrow> x a + y a) b =
       (\<lambda>b. (case inv_option \<pi> b of None \<Rightarrow> 0 | Some c \<Rightarrow> x c) +
             (case inv_option \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> y x)) b\<close>
        for b
      proof(induction \<open>inv_option \<pi> b\<close>)
        case None
        thus ?case
          by auto 
      next
        case (Some x)
        thus ?case
          by (metis option.simps(5)) 
      qed
      thus \<open>(\<lambda>b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some a \<Rightarrow> x a + y a) =
       (\<lambda>b. (case inv_option \<pi> b of None \<Rightarrow> 0 | Some c \<Rightarrow> x c) +
             (case inv_option \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> y x))\<close>
        by blast
    qed
    thus ?thesis
    proof - (* sledgehammer *)
      have f1: "\<forall>b f fa. (case inv_option f (b::'b) of None \<Rightarrow> 0 | Some (x::'a) \<Rightarrow> fa x) = Rep_ell2 (classical_operator' f (Abs_ell2 fa)) b \<or> \<not> has_ell2_norm fa"
        by (metis (no_types) Abs_ell2_inverse classical_operator'.rep_eq mem_Collect_eq)
      have "\<forall>f fa. (Abs_ell2 (\<lambda>a. fa (a::'a) + f a) = Abs_ell2 fa + Abs_ell2 f \<or> \<not> has_ell2_norm f) \<or> \<not> has_ell2_norm fa"
        by (metis (no_types) eq_onp_same_args plus_ell2.abs_eq)
      then have "(case inv_option S b of None \<Rightarrow> 0 | Some a \<Rightarrow> b1 a + b2 a) = Rep_ell2 (classical_operator' S (Abs_ell2 b1 + Abs_ell2 b2)) b"
        using f1 by (metis (no_types) ell2_norm_triangle(1) that(1) that(2))
      then show ?thesis
        using f1 by (metis (full_types) \<open>\<And>y x \<pi>. classical_operator' \<pi> (x + y) = classical_operator' \<pi> x + classical_operator' \<pi> y\<close> plus_ell2.rep_eq that(1) that(2))
    qed
  qed

  show "classical_operator' S (r *\<^sub>C (b::'a ell2)) = r *\<^sub>C (classical_operator' S b::'b ell2)"
    for S :: "'a \<Rightarrow> 'b option"
      and r :: complex
      and b :: "'a ell2"
  proof transfer
    fix  \<pi> :: "'a \<Rightarrow> 'b option"
      and r :: complex
      and x :: "'a \<Rightarrow> complex"
    assume \<open>has_ell2_norm x\<close>
    have \<open>(\<lambda>b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some a \<Rightarrow> r * x a) b =
       (\<lambda>b. r * (case inv_option \<pi> b of None \<Rightarrow> 0 | Some b \<Rightarrow> x b)) b\<close>
      for b
    proof(induction \<open>inv_option \<pi> b\<close>)
      case None
      thus ?case
        by auto 
    next
      case (Some x)
      thus ?case
        by (metis option.simps(5)) 
    qed
    thus \<open>(\<lambda>b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some a \<Rightarrow> r * x a) =
       (\<lambda>b. r * (case inv_option \<pi> b of None \<Rightarrow> 0 | Some b \<Rightarrow> x b))\<close>
      by blast
  qed

  show "\<exists>K. \<forall>x. norm (classical_operator' S (x::'a ell2)::'b ell2) \<le> norm x * K"
    for S :: "'a \<Rightarrow> 'b option"
  proof transfer
    fix  \<pi> :: "'a \<Rightarrow> 'b option"
    show \<open>\<exists>K. \<forall>x\<in>Collect has_ell2_norm.
                ell2_norm (\<lambda>b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some t \<Rightarrow> x t)
                \<le> ell2_norm x * K\<close>
    proof
      have \<open>has_ell2_norm \<psi> \<Longrightarrow> ell2_norm (\<lambda>b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some t \<Rightarrow> \<psi> t)
           \<le> ell2_norm \<psi>\<close>
        for \<psi>  
      proof-
        assume \<open>has_ell2_norm \<psi>\<close>
        have \<open>\<forall> S. finite S \<longrightarrow> ( sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) S ) \<le> (ell2_norm \<psi>)^2\<close>
          using \<open>has_ell2_norm \<psi>\<close> ell2_norm_def
          by (smt cSUP_upper has_ell2_norm_def mem_Collect_eq sqrt_le_D sum.cong)
        define \<phi>::\<open>'b \<Rightarrow> complex\<close> where
          \<open>\<phi> b = (case inv_option \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x)\<close> for b
        have \<open>\<lbrakk>finite R; \<forall>i\<in>R. \<phi> i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le>  (ell2_norm \<psi>)^2\<close>
          for R::\<open>'b set\<close>
        proof-
          assume \<open>finite R\<close> and \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
          from  \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
          have  \<open>\<forall>i\<in>R. \<exists> x. Some x = inv_option \<pi> i\<close>
            unfolding \<phi>_def
            by (metis option.case_eq_if option.collapse)
          hence  \<open>\<exists> f. \<forall>i\<in>R. Some (f i) = inv_option \<pi> i\<close>
            by metis
          then obtain f::\<open>'b\<Rightarrow>'a\<close> where \<open>\<forall>i\<in>R. Some (f i) = inv_option \<pi> i\<close> 
            by blast
          define S::\<open>'a set\<close> where \<open>S = f ` R\<close>
          have \<open>finite S\<close>
            using \<open>finite R\<close>
            by (simp add: S_def)
          moreover have \<open>(\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) =  (\<Sum>i\<in>S. (cmod (\<psi> i))\<^sup>2)\<close>
          proof-
            have \<open>inj_on f R\<close>
            proof(rule inj_onI)
              fix x y :: 'b
              assume \<open>x \<in> R\<close> and \<open>y \<in> R\<close> and \<open>f x = f y\<close>
              from \<open>\<forall>i\<in>R. Some (f i) = inv_option \<pi> i\<close> 
              have \<open>\<forall>i\<in>R. Some (f i) = Some (inv \<pi> (Some i))\<close>
                by (metis inv_option_def option.distinct(1))
              hence \<open>\<forall>i\<in>R. f i = inv \<pi> (Some i)\<close>
                by blast
              hence \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close>
                by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_option \<pi> i\<close> f_inv_into_f inv_option_def option.distinct(1)) 
              have \<open>\<pi> (f x) = Some x\<close>
                using \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close> \<open>x\<in>R\<close> by blast
              moreover have \<open>\<pi> (f y) = Some y\<close>
                using \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close> \<open>y\<in>R\<close> by blast
              ultimately have \<open>Some x = Some y\<close>
                using \<open>f x = f y\<close> by metis
              thus \<open>x = y\<close> by simp
            qed
            moreover have \<open>i \<in> R \<Longrightarrow> (cmod (\<phi> i))\<^sup>2 = (cmod (\<psi> (f i)))\<^sup>2\<close>
              for i
            proof-
              assume \<open>i \<in> R\<close>
              hence \<open>\<phi> i = \<psi> (f i)\<close>
                unfolding \<phi>_def
                by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_option \<pi> i\<close> option.simps(5))
              thus ?thesis
                by simp 
            qed
            ultimately show ?thesis unfolding S_def
              by (metis (mono_tags, lifting) sum.reindex_cong)
          qed
          ultimately show ?thesis
            by (simp add: \<open>\<forall>S. finite S \<longrightarrow> (\<Sum>i\<in>S. (cmod (\<psi> i))\<^sup>2) \<le> (ell2_norm \<psi>)\<^sup>2\<close>)
        qed     
        have \<open>finite R \<Longrightarrow> ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) \<le> (ell2_norm \<psi>)\<^sup>2\<close>
          for R::\<open>'b set\<close>
        proof-
          assume \<open>finite R\<close>
          define U::\<open>'b set\<close> where \<open>U = {i | i::'b. i \<in> R \<and>  \<phi> i \<noteq> 0 }\<close>
          define V::\<open>'b set\<close> where \<open>V = {i | i::'b. i \<in> R \<and>  \<phi> i = 0 }\<close>
          have \<open>U \<inter> V = {}\<close>
            unfolding U_def V_def by blast
          moreover have \<open>U \<union> V = R\<close>
            unfolding U_def V_def by blast
          ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U ) + 
            ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) V )\<close>
            using \<open>finite R\<close> sum.union_disjoint by auto
          moreover have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) V ) = 0\<close>
            unfolding V_def by auto
          ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U )\<close>
            by simp
          moreover have \<open>\<forall> i \<in> U. \<phi> i \<noteq> 0\<close>
            by (simp add: U_def)
          moreover have \<open>finite U\<close>
            unfolding U_def using \<open>finite R\<close>
            by simp
          ultimately have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U ) \<le>  (ell2_norm \<psi>)\<^sup>2\<close>
            using \<open>\<And>R. \<lbrakk>finite R; \<forall>i\<in>R. \<phi> i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le>  (ell2_norm \<psi>)\<^sup>2\<close> by blast        
          thus ?thesis using \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) U )\<close>
            by simp
        qed
        hence \<open>finite R \<Longrightarrow> sqrt (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> ell2_norm \<psi>\<close>
          for R
        proof-
          assume \<open>finite R\<close>
          hence \<open>(\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> (ell2_norm \<psi>)^2\<close>
            by (simp add: \<open>\<And>R. finite R \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> (ell2_norm \<psi>)\<^sup>2\<close>)
          hence \<open>sqrt (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> sqrt ((ell2_norm \<psi>)^2)\<close>
            using real_sqrt_le_iff by blast
          moreover have \<open>sqrt ((ell2_norm \<psi>)^2) = ell2_norm \<psi>\<close>
          proof-
            have \<open>ell2_norm \<psi> \<ge> 0\<close>
            proof-
              obtain X where \<open>Rep_ell2 X = \<psi>\<close>
                using Rep_ell2_cases \<open>has_ell2_norm \<psi>\<close> by auto
              have \<open>norm X \<ge> 0\<close>
                by simp
              thus \<open>ell2_norm \<psi> \<ge> 0\<close> 
                using \<open>Rep_ell2 X = \<psi>\<close>
                by (simp add: norm_ell2.rep_eq) 
            qed
            thus ?thesis
              by simp 
          qed
          ultimately show ?thesis
            by linarith 
        qed
        hence \<open>\<forall> L \<in> { sqrt (sum (\<lambda>i. norm (\<phi> i)^2) F) | F. F\<in>{F. finite F} }. L \<le> ell2_norm \<psi>\<close>
          by blast
        moreover have \<open>{ sqrt (sum (\<lambda>i. norm (\<phi> i)^2) F) | F. F\<in>{F. finite F} } \<noteq> {}\<close>
          by force
        ultimately have \<open>Sup { sqrt (sum (\<lambda>i. norm (\<phi> i)^2) F) | F. F\<in>{F. finite F} } \<le> ell2_norm \<psi>\<close>
          by (meson cSup_least)
        moreover have \<open>sqrt ( Sup { sum (\<lambda>i. norm (\<phi> i)^2) F | F. F\<in>{F. finite F} } )
          = Sup { sqrt (sum (\<lambda>i. norm (\<phi> i)^2) F) | F. F\<in>{F. finite F}  }\<close>
        proof-
          define T where \<open>T = { sum (\<lambda>i. norm (\<phi> i)^2) F | F. F\<in>{F. finite F} }\<close>
          have \<open>mono sqrt\<close>
            by (simp add: monoI)
          moreover have \<open>continuous (at_left (Sup T)) sqrt\<close>
            by (simp add: continuous_at_imp_continuous_at_within isCont_real_sqrt)      
          moreover have \<open>T \<noteq> {}\<close>
            unfolding T_def
            by blast
          moreover have \<open>bdd_above T\<close>
          proof(rule bdd_aboveI)
            fix x
            assume \<open>x \<in> T\<close>
            hence \<open>\<exists> R. finite R \<and> x = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R )\<close>
              unfolding T_def
              by blast
            then obtain R where \<open>finite R\<close> and \<open>x = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R )\<close>
              by blast
            from  \<open>finite R\<close>
            have \<open>( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R ) \<le>  (ell2_norm \<psi>)^2\<close>
              by (simp add: \<open>\<And>R. finite R \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> (ell2_norm \<psi>)\<^sup>2\<close>)
            thus \<open>x \<le> (ell2_norm \<psi>)^2\<close>
              using  \<open>x = ( sum (\<lambda>i. (cmod (\<phi> i))\<^sup>2) R )\<close> by simp
          qed
          ultimately have \<open>sqrt (Sup T) = Sup (sqrt ` T)\<close>
            by (rule Topological_Spaces.continuous_at_Sup_mono)
          moreover have \<open>sqrt ` {\<Sum>i\<in>F. (cmod (\<phi> i))\<^sup>2 |F. F \<in> Collect finite}
             =  {sqrt (\<Sum>i\<in>F. (cmod (\<phi> i))\<^sup>2) |F. F \<in> Collect finite}\<close>
            by auto
          ultimately show ?thesis 
            unfolding T_def
            by simp
        qed
        ultimately have \<open>sqrt ( Sup { sum (\<lambda>i. norm (\<phi> i)^2) F | F. F\<in>{F. finite F} } ) \<le> ell2_norm \<psi>\<close>
          by simp
        moreover have \<open>ell2_norm \<phi> = sqrt ( Sup { sum (\<lambda>i. norm (\<phi> i)^2) F | F. F\<in>{F. finite F} } )\<close>
          unfolding ell2_norm_def
          by (metis Setcompr_eq_image)
        ultimately have \<open>ell2_norm \<phi> \<le> ell2_norm \<psi>\<close>
          by simp
        thus ?thesis
          using \<open>\<phi> \<equiv> \<lambda>b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x\<close> 
          by simp
      qed
      thus "\<forall>x\<in>Collect has_ell2_norm. ell2_norm (\<lambda>b. case inv_option \<pi> b of None \<Rightarrow> 0 | Some t \<Rightarrow> x t)
           \<le> ell2_norm x * 1"
        by simp
    qed
  qed
qed


lemma classical_operator_basis: "inj_option \<pi> \<Longrightarrow>
      (classical_operator \<pi>) *\<^sub>v (ket x) = (case \<pi> x of Some y \<Rightarrow> ket y | None \<Rightarrow> 0)"
  by (cheat TODO)

lemma classical_operator_adjoint[simp]: 
  "inj_option \<pi> \<Longrightarrow> adjoint (classical_operator \<pi>) = classical_operator (inv_option \<pi>)"
  for \<pi> :: "'a \<Rightarrow> 'b option"
  by (cheat TODO1)

lemma classical_operator_mult[simp]:
  "inj_option \<pi> \<Longrightarrow> inj_option \<rho> \<Longrightarrow> classical_operator \<pi> *\<^sub>o classical_operator \<rho> = classical_operator (map_comp \<pi> \<rho>)"
  by (cheat TODO)
    (*
  apply (rule equal_basis)
  unfolding timesOp_assoc_linear_space
  apply (subst classical_operator_basis, simp)+
  apply (case_tac "\<rho> x")
  apply auto
  apply (subst classical_operator_basis, simp)
  by auto
*)

lemma classical_operator_Some[simp]: "classical_operator Some = idOp"
  by (cheat TODO)
    (*
  apply (rule equal_basis) apply (subst classical_operator_basis) apply simp by auto
*)

lemma isometry_classical_operator[simp]:
  assumes "inj \<pi>"
  shows "isometry (classical_operator (Some o \<pi>))"
proof -
  have comp: "inv_option (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>) = Some" 
    apply (rule ext) unfolding inv_option_def o_def 
    using assms unfolding inj_def inv_def by auto

  show ?thesis
    unfolding isometry_def
    apply (subst classical_operator_adjoint) using assms apply simp
    apply (subst classical_operator_mult) using assms apply auto[2]
    apply (subst comp)
    by simp
qed

lemma unitary_classical_operator[simp]:
  assumes "bij \<pi>"
  shows "unitary (classical_operator (Some o \<pi>))"
  by (cheat TODO)
    (*
proof (unfold unitary_def, rule conjI)
  have "isometry (classical_operator (Some o \<pi>))"
    by (simp add: assms bij_is_inj)
  hence "classical_operator (Some \<circ> \<pi>)* \<cdot>\<^sub>o classical_operator (Some \<circ> \<pi>) = idOp"
    unfolding isometry_def by simp
  thus ?thesis by (cheat TODO)
next
  have "inj \<pi>"
    by (simp add: assms bij_is_inj)
  have comp: "Some \<circ> \<pi> \<circ>\<^sub>m inv_option (Some \<circ> \<pi>) = Some"
    apply (rule ext)
    unfolding inv_option_def o_def map_comp_def
    unfolding inv_def apply auto
    apply (metis \<open>inj \<pi>\<close> inv_def inv_f_f)
    by (metis assms bij_def image_iff range_eqI)

  show "classical_operator (Some \<circ> \<pi>) \<cdot> classical_operator (Some \<circ> \<pi>)* = idOp"
    by (simp add: comp \<open>inj \<pi>\<close>)
qed
*)

unbundle no_bounded_notation

end

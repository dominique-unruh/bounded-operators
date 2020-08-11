section \<open>Lebesgue space of square-summable functions\<close>

(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

theory Complex_L2
  imports 
    "HOL-Analysis.L2_Norm"
    "HOL-Library.Rewrite"
    "HOL-Analysis.Infinite_Set_Sum"
    Complex_Inner_Product
    Bounded_Operators
    "HOL-ex.Sketch_and_Explore"
    Preliminaries
begin

unbundle cblinfun_notation
unbundle no_notation_blinfun_apply

subsection \<open>Preliminaries\<close>

hide_const (open) Real_Vector_Spaces.span

subsection \<open>l2 norm - untyped\<close>

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
  thus "has_ell2_norm x"
    unfolding has_ell2_norm_def f_def
    by (rule bdd_aboveI2[where M=bound], simp)
next
  assume "has_ell2_norm x"
  then obtain B where "(\<Sum>xa\<in>F. norm ((cmod (x xa))\<^sup>2)) < B" if "finite F" for F
    apply atomize_elim unfolding has_ell2_norm_def unfolding bdd_above_def apply auto
    by (meson gt_ex le_less_trans)
  thus "(\<lambda>i. (cmod (x i))\<^sup>2) abs_summable_on UNIV"
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
    thus "bdd_above X"
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

subsection \<open>Subspaces\<close>

notation
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) 


typedef 'a ell2 = "{x::'a\<Rightarrow>complex. has_ell2_norm x}"
  unfolding has_ell2_norm_def by (rule exI[of _ "\<lambda>_.0"], auto)
setup_lifting type_definition_ell2
  (* TODO: derive universe vector *)
  (* Ask to Dominique: I do not understand *)

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
  thus "ell2_norm x = 0"
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
    thus "x i = 0" by auto
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
  hence "cmod c * M \<ge> L2_set (cmod o (\<lambda>i. c * x i)) F" if "finite F" for F
    unfolding L2_set_mul
    by (simp add: ordered_comm_semiring_class.comm_mult_left_mono that) 
  thus has: "has_ell2_norm (\<lambda>i. c * x i)"
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
  hence MxMy: "Mx + My \<ge> L2_set (cmod \<circ> x) F + L2_set (cmod \<circ> y) F" if "finite F" for F
    using that by fastforce
  hence bdd_plus: "bdd_above ((\<lambda>xa. L2_set (cmod \<circ> x) xa + L2_set (cmod \<circ> y) xa) ` Collect finite)"
    unfolding bdd_above_def by auto
  from MxMy have MxMy': "Mx + My \<ge> L2_set (cmod \<circ> (\<lambda>i. x i + y i)) F" if "finite F" for F 
    using triangle that by fastforce
  thus has: "has_ell2_norm (\<lambda>i. x i + y i)"
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
declare norm_ell2_def[code del]
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
declare cinner_ell2_def[code del]

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
    hence cnj_x: "(\<lambda>i. cnj (x i) * cnj (x i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    assume "has_ell2_norm y"
    hence cnj_y: "(\<lambda>i. cnj (y i) * cnj (y i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    assume "has_ell2_norm z"
    hence z: "(\<lambda>i. z i * z i) abs_summable_on UNIV" 
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
    hence cnj_x: "(\<lambda>i. cnj (x i) * cnj (x i)) abs_summable_on UNIV"
      by (simp del: complex_cnj_mult add: norm_mult[symmetric] complex_cnj_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    assume "has_ell2_norm y"
    hence y: "(\<lambda>i. y i * y i) abs_summable_on UNIV" 
      by (simp add: norm_mult[symmetric] has_ell2_norm_infsetsum power2_eq_square)
    have cnj_x_y:"(\<lambda>i. cnj (x i) * y i) abs_summable_on UNIV"
      using cnj_x y by (rule abs_summable_product) 
    thus "(\<Sum>\<^sub>ai. cnj (c * x i) * y i) = cnj c * (\<Sum>\<^sub>ai. cnj (x i) * y i)"
      apply (subst infsetsum_cmult_right[symmetric])
      by (auto simp: mult.commute mult.left_commute)
  qed

  show "0 \<le> cinner x x"
  proof transfer
    fix x :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    hence sum: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
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
    hence cmod_x2: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      unfolding has_ell2_norm_infsetsum power2_eq_square 
      apply (subst abs_summable_on_norm_iff[symmetric])
      by (simp del: abs_summable_on_norm_iff add: norm_mult)
    assume eq0: "(\<Sum>\<^sub>ai. cnj (x i) * x i) = 0"
    show "x = (\<lambda>_. 0)"
    proof (rule ccontr)
      assume "x \<noteq> (\<lambda>_. 0)"
      then obtain i where "x i \<noteq> 0" by auto
      hence "0 < cnj (x i) * x i"
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
    hence sum: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
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
  thus ?thesis
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

(* NOTE: moved to Banach_Steinhaus *)
(* definition pointwise_convergent_to :: 
  \<open>( nat \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) ) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> where
  \<open>pointwise_convergent_to x l = (\<forall> t::'a. (\<lambda> n. (x n) t ) \<longlonglongrightarrow> l t)\<close>

abbreviation pointwise_convergent_to_abbr :: 
  \<open>( nat \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) ) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>  ("/_/ \<midarrow>pointwise\<rightarrow> /_/") where
  \<open>x \<midarrow>pointwise\<rightarrow> l \<equiv> pointwise_convergent_to x l\<close> *)

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
  thus ?thesis
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
      hence "inj_on (\<lambda>a. (a, True)) S"
        using f2 by (metis (no_types) \<open>inj (\<lambda>x. (x, True))\<close>)
      thus ?thesis
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
      hence "inj_on (\<lambda>a. (a, False)) S"
        using f2 by (metis (no_types) \<open>inj (\<lambda>x. (x, False))\<close>)
      thus ?thesis
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

lemma CauchyImplies_ell2Cblinfun:                         
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
        thus ?thesis by blast
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
          \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> CauchyImplies_ell2Cblinfun
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
                hence "\<epsilon> / sqrt (real (card S)) + - 1 * (\<epsilon> / 1) \<le> 0"
                  using f3 f2 f1 \<open>1 \<le> sqrt (real (card S))\<close> nice_ordered_field_class.frac_le by blast
                thus ?thesis
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
            \<open>(\<epsilon>/4)^2 > (0::real)\<close>
          by blast 
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
  hence "\<exists>l. X \<longlonglongrightarrow> l"
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

type_synonym 'a ell2_clinear_space = "'a ell2 clinear_space"

lemma subspace_zero_not_top[simp]: 
  "(0::'a::{complex_vector,t1_space,not_singleton} clinear_space) \<noteq> top"
  by simp

instance ell2 :: (type) not_singleton
proof standard
  have "ket undefined \<noteq> (0::'a ell2)"
    apply transfer
    by (meson one_neq_zero)
  thus \<open>\<exists>x y::'a ell2. x \<noteq> y\<close>
    by blast    
qed


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


lemma ell2_norm_explicit_finite_support:
  assumes  \<open>finite S\<close> \<open>\<And> i. i \<notin> S \<Longrightarrow> Rep_ell2 x i = 0\<close>
  shows \<open>norm x = sqrt ((sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S)\<close>
proof-
  have \<open>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S \<le> (Sup (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite))\<close>
  proof-
    have \<open>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S \<in>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite)\<close>
      using \<open>finite S\<close>
      by simp
    moreover have \<open>bdd_above (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite)\<close>
      using Rep_ell2 unfolding has_ell2_norm_def
      by auto
    ultimately show ?thesis using cSup_upper by simp
  qed
  moreover have \<open>(Sup (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite)) \<le> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S\<close>
  proof-
    have \<open>t \<in> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite) \<Longrightarrow> t \<le> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S\<close>
      for t
    proof-
      assume \<open>t \<in> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite)\<close>
      hence \<open>\<exists> R \<in> (Collect finite). t = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) R\<close> 
        by blast
      then obtain R where \<open>R \<in> (Collect finite)\<close> and \<open>t = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) R\<close>
        by blast
      from \<open>R \<in> (Collect finite)\<close>
      have \<open>finite R\<close>
        by blast
      have \<open>R = (R - S) \<union> (R \<inter> S)\<close>
        by (simp add: Un_Diff_Int)
      moreover have \<open>(R - S) \<inter> (R \<inter> S) = {}\<close>
        by auto
      ultimately have  \<open>t = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) (R - S)
         + (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) (R \<inter> S)\<close>
        using \<open>t = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) R\<close> and \<open>finite R\<close>
        by (smt sum.Int_Diff)
      moreover have \<open>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) (R - S) = 0\<close>
      proof-
        have \<open>r \<in> R - S \<Longrightarrow> (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) r = 0\<close>
          for r
          by (simp add: assms(2))        
        thus ?thesis
          by simp 
      qed
      ultimately have \<open>t = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) (R \<inter> S)\<close>
        by simp
      moreover have \<open>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) (R \<inter> S) \<le> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S\<close>
      proof-
        have \<open>R \<inter> S \<subseteq> S\<close>
          by simp        
        moreover have \<open>(\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) i \<ge> 0\<close>
          for i
          by auto        
        ultimately show ?thesis
          by (simp add: assms(1) sum_mono2) 
      qed
      ultimately show \<open>t \<le> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S\<close> by simp
    qed
    moreover have \<open>(sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite) \<noteq> {}\<close>
      by auto      
    ultimately show ?thesis
      by (simp add: cSup_least) 
  qed
  ultimately have \<open>(Sup (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite)) = (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S\<close>
    by simp
  thus ?thesis
    by (metis ell2_norm_def norm_ell2.rep_eq) 
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


lemma ket_distinct:
  \<open>i \<noteq> j \<Longrightarrow> ket i \<noteq> ket j\<close>
  by (metis ket_Kronecker_delta_eq ket_Kronecker_delta_neq zero_neq_one)

lift_definition trunc_ell2:: \<open>'a set \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2\<close>
  is \<open>\<lambda> S x. (\<lambda> i. (if i \<in> S then (Rep_ell2 x) i else 0))\<close>
proof transfer
  show "has_ell2_norm (\<lambda>i. if (i::'a) \<in> S then x i else 0)"
    if "has_ell2_norm (x::'a \<Rightarrow> complex)"
    for S :: "'a set"
      and x :: "'a \<Rightarrow> complex"
  proof-
    from \<open>has_ell2_norm (x::'a \<Rightarrow> complex)\<close>
    have \<open>bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)\<close>
      unfolding has_ell2_norm_def
      by blast
    hence \<open>\<exists> K. \<forall> R. finite R \<longrightarrow> (sum (\<lambda>i. (cmod (x i))\<^sup>2) R) \<le> K\<close>
      unfolding bdd_above_def
      by blast
    then obtain K where \<open>\<forall> R. finite R \<longrightarrow> (sum (\<lambda>i. (cmod (x i))\<^sup>2) R) \<le> K\<close>
      by blast
    have \<open>finite R \<Longrightarrow> (sum (\<lambda>i. (cmod (if i \<in> S then x i else 0))\<^sup>2) R) \<le> K\<close>
      for R
    proof-
      assume \<open>finite R\<close>
      have \<open>(cmod (if i \<in> S then x i else 0))\<^sup>2 \<le> (cmod (x i))\<^sup>2\<close>
        for i                                 
      proof (cases \<open>i \<in> S\<close>)
        show "(cmod (if i \<in> S then x i else 0))\<^sup>2 \<le> (cmod (x i))\<^sup>2"
          if "i \<in> S"
          using that
          by simp 
        show "(cmod (if i \<in> S then x i else 0))\<^sup>2 \<le> (cmod (x i))\<^sup>2"
          if "i \<notin> S"
          using that
          by auto 
      qed    
      hence \<open>(sum (\<lambda>i. (cmod (if i \<in> S then x i else 0))\<^sup>2) R)
          \<le> (sum (\<lambda>i. (cmod (x i))\<^sup>2) R)\<close>
        by (simp add: ordered_comm_monoid_add_class.sum_mono)
      thus ?thesis
        using \<open>\<forall>R. finite R \<longrightarrow> (\<Sum>i\<in>R. (cmod (x i))\<^sup>2) \<le> K\<close> \<open>finite R\<close> by fastforce
    qed
    hence \<open>\<forall> R. finite R \<longrightarrow> (sum (\<lambda>i. (cmod (if i \<in> S then x i else 0))\<^sup>2) R) \<le> K\<close>
      by blast
    hence \<open>\<forall> t \<in> {sum (\<lambda>i. (cmod (if i \<in> S then x i else 0))\<^sup>2) R | R. finite R}. t \<le> K\<close>
      by blast      
    moreover have \<open>{sum (\<lambda>i. (cmod (if i \<in> S then x i else 0))\<^sup>2) R | R. finite R }
          = (sum (\<lambda>i. (cmod (if i \<in> S then x i else 0))\<^sup>2) ` Collect finite)\<close>  
      by blast
    ultimately have \<open>\<forall> t \<in> (sum (\<lambda>i. (cmod (if i \<in> S then x i else 0))\<^sup>2) ` Collect finite). t \<le> K\<close>
      by auto     
    hence \<open>bdd_above (sum (\<lambda>i. (cmod (if i \<in> S then x i else 0))\<^sup>2) ` Collect finite)\<close>
      unfolding bdd_above_def 
      by auto
    thus ?thesis 
      unfolding has_ell2_norm_def by blast
  qed
qed

lemma truc_ell2_insert:
  \<open>k \<notin> R \<Longrightarrow> trunc_ell2 (insert k R) w = trunc_ell2 R w + (Rep_ell2 w k) *\<^sub>C (ket k)\<close>
proof-
  assume \<open>k \<notin> R\<close>  
  have \<open>(if i \<in> insert k R then Rep_ell2 w i else 0) =
        (if i \<in> R then Rep_ell2 w i else 0)
      + (if i = k then Rep_ell2 w i else 0)\<close>
    for i
  proof (cases \<open>i \<in> insert k R\<close>)
    show "(if i \<in> insert k R then Rep_ell2 w i else 0) = (if i \<in> R then Rep_ell2 w i else 0) + (if i = k then Rep_ell2 w i else 0)"
      if "i \<in> insert k R"
      using that proof (cases \<open>i \<in> R\<close>)
      show "(if i \<in> insert k R then Rep_ell2 w i else 0) = (if i \<in> R then Rep_ell2 w i else 0) + (if i = k then Rep_ell2 w i else 0)"
        if "i \<in> insert k R"
          and "i \<in> R"
        using that \<open>k \<notin> R\<close> by auto 
      show "(if i \<in> insert k R then Rep_ell2 w i else 0) = (if i \<in> R then Rep_ell2 w i else 0) + (if i = k then Rep_ell2 w i else 0)"
        if "i \<in> insert k R"
          and "i \<notin> R"
        using that
        by auto 
    qed
    show "(if i \<in> insert k R then Rep_ell2 w i else 0) = (if i \<in> R then Rep_ell2 w i else 0) + (if i = k then Rep_ell2 w i else 0)"
      if "i \<notin> insert k R"
      using that
      by simp 
  qed
  moreover have \<open>Rep_ell2 (trunc_ell2 (insert k R) w) = (\<lambda> i. if i \<in> insert k R then Rep_ell2 w i else 0)\<close>
    by (simp add: trunc_ell2.rep_eq)
  moreover have \<open>Rep_ell2 (trunc_ell2 R w) = (\<lambda> i. if i \<in> R then Rep_ell2 w i else 0)\<close>
    by (simp add: trunc_ell2.rep_eq)
  moreover have \<open>Rep_ell2 ( (Rep_ell2 w k) *\<^sub>C (ket k) ) = (\<lambda> i. if i = k then Rep_ell2 w i else 0)\<close>
  proof -
    have "\<forall>a aa. a = k \<and> aa \<noteq> k \<or> Rep_ell2 (Rep_ell2 w k *\<^sub>C ket k) a = 0 \<and> aa \<noteq> k \<or> a = k \<and> Rep_ell2 (Rep_ell2 w k *\<^sub>C ket k) aa = Rep_ell2 w aa \<or> Rep_ell2 (Rep_ell2 w k *\<^sub>C ket k) a = 0 \<and> Rep_ell2 (Rep_ell2 w k *\<^sub>C ket k) aa = Rep_ell2 w aa"
      by (simp add: ket.rep_eq scaleC_ell2.rep_eq)
    thus ?thesis
      by meson
  qed
  ultimately have \<open>Rep_ell2 (trunc_ell2 (insert k R) w) i = Rep_ell2 (trunc_ell2 R w) i + Rep_ell2 ((Rep_ell2 w k) *\<^sub>C (ket k)) i\<close>
    for i
    by (simp add: \<open>\<And>i. (if i \<in> insert k R then Rep_ell2 w i else 0) = (if i \<in> R then Rep_ell2 w i else 0) + (if i = k then Rep_ell2 w i else 0)\<close> \<open>k \<notin> R\<close>)
  hence \<open>Rep_ell2 (trunc_ell2 (insert k R) w) i =
        Rep_ell2 ((trunc_ell2 R w) + ((Rep_ell2 w k) *\<^sub>C (ket k)) ) i\<close>
    for i
    by (simp add: plus_ell2.rep_eq)
  hence \<open>Rep_ell2 (trunc_ell2 (insert k R) w) =
        Rep_ell2 ((trunc_ell2 R w) + ((Rep_ell2 w k) *\<^sub>C (ket k)) )\<close>
    by blast
  thus \<open>trunc_ell2 (insert k R) w = trunc_ell2 R w + (Rep_ell2 w k) *\<^sub>C (ket k)\<close>
    using Rep_ell2_inject
    by blast
qed


lemma ell2_ortho:
  assumes \<open>\<And> i. Rep_ell2 x i = 0 \<or> Rep_ell2 y i = 0\<close>
  shows \<open>\<langle>x, y\<rangle> = 0\<close>
  using assms apply transfer
  by (simp add: infsetsum_all_0)

lemma trunc_ell2_norm_diff:
  \<open>(norm (x - trunc_ell2 S x))^2 = (norm x)^2 - (norm (trunc_ell2 S x))^2\<close>
proof-
  have \<open>Rep_ell2 (trunc_ell2 S x) i = 0 \<or> Rep_ell2 (x - trunc_ell2 S x) i = 0\<close>
    for i
  proof (cases \<open>i \<in> S\<close>)
    show "Rep_ell2 (trunc_ell2 S x) i = 0 \<or> Rep_ell2 (x - trunc_ell2 S x) i = 0"
      if "i \<in> S"
      using that
      by (simp add: minus_ell2.rep_eq trunc_ell2.rep_eq) 
    show "Rep_ell2 (trunc_ell2 S x) i = 0 \<or> Rep_ell2 (x - trunc_ell2 S x) i = 0"
      if "i \<notin> S"
      using that
      by (simp add: trunc_ell2.rep_eq) 
  qed
  hence \<open>\<langle> (trunc_ell2 S x), (x - trunc_ell2 S x) \<rangle> = 0\<close>
    using ell2_ortho by blast
  hence \<open>(norm x)^2 = (norm (trunc_ell2 S x))^2 + (norm (x - trunc_ell2 S x))^2\<close>
    using PythagoreanId by fastforce    
  thus ?thesis by simp
qed


lemma trunc_ell2_norm_explicit:
  \<open>finite S \<Longrightarrow> (norm (trunc_ell2 S x)) = sqrt ((sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S)\<close>
proof-
  assume \<open>finite S\<close>
  moreover have \<open>\<And> i. i \<notin> S \<Longrightarrow> Rep_ell2 ((trunc_ell2 S x)) i = 0\<close>
    by (simp add: trunc_ell2.rep_eq)    
  ultimately have \<open>(norm (trunc_ell2 S x)) = sqrt ((sum (\<lambda>i. (cmod (Rep_ell2 ((trunc_ell2 S x)) i))\<^sup>2)) S)\<close>
    using ell2_norm_explicit_finite_support
    by blast 
  moreover have \<open>\<And> i. i \<in> S \<Longrightarrow> Rep_ell2 ((trunc_ell2 S x)) i = Rep_ell2 x i\<close>
    by (simp add: trunc_ell2.rep_eq)
  ultimately show ?thesis by simp
qed

lemma trunc_ell2_lim:
  includes nsa_notation
  shows \<open>\<exists> S. hypfinite S \<and> (*f2* trunc_ell2) S (star_of x) \<approx> star_of x\<close>
proof-
  define f where \<open>f = sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)\<close>
  have \<open>norm x = sqrt (Sup (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2) ` Collect finite))\<close>
    apply transfer unfolding ell2_norm_def by blast
  hence \<open>(norm x)^2 = Sup (f ` Collect finite)\<close>
    unfolding f_def
    by (smt norm_not_less_zero real_sqrt_ge_0_iff real_sqrt_pow2) 
  have \<open>Sup (f ` Collect finite) \<in> closure (f ` Collect finite)\<close>
  proof (rule Borel_Space.closure_contains_Sup)
    show "f ` Collect finite \<noteq> {}"
      by blast      
    show "bdd_above (f ` Collect finite)"
    proof-
      have \<open>has_ell2_norm (Rep_ell2 x)\<close>
        using Rep_ell2 by blast
      thus ?thesis unfolding has_ell2_norm_def f_def
        by simp
    qed
  qed
  hence \<open>(norm x)^2 \<in> closure (f ` Collect finite)\<close>
    by (simp add: \<open>(norm x)\<^sup>2 = Sup (f ` Collect finite)\<close>)
  hence \<open>\<exists> t\<in>*s* (f ` Collect finite). t \<approx> star_of ((norm x)^2)\<close>
    using approx_sym nsclosure_I by blast
  then obtain t where \<open>t\<in>*s* (f ` Collect finite)\<close> and \<open>t \<approx> star_of ((norm x)^2)\<close>
    by blast
  from \<open>t\<in>*s* (f ` Collect finite)\<close>
  have \<open>\<exists> S \<in> (*s* (Collect finite)). t = (*f* f) S\<close>
    by (simp add: image_iff)
  then obtain S where \<open>S \<in> (*s* (Collect finite))\<close> and \<open>t = (*f* f) S\<close>
    by blast
  from  \<open>t \<approx> star_of ((norm x)^2)\<close>  \<open>t = (*f* f) S\<close>
  have \<open>(*f* f) S \<approx> star_of ((norm x)^2)\<close>
    by simp
  hence \<open>(*f* f) S \<approx> (hnorm (star_of x))^2\<close>
    by simp    
  have \<open>hypfinite S\<close>
  proof-
    have \<open>\<forall> S. S \<in> Collect finite \<longleftrightarrow> finite S\<close>
      by blast
    hence \<open>\<forall> S. S \<in>*s* (Collect finite) \<longleftrightarrow> hypfinite S\<close>
      unfolding hypfinite_def
      by StarDef.transfer
    thus ?thesis
      using \<open>S \<in> *s* Collect finite\<close> by blast 
  qed
  moreover have \<open>(*f2* trunc_ell2) S (star_of x) \<approx> star_of x\<close>
  proof-
    have \<open>hnorm (star_of x - (*f2* trunc_ell2) S (star_of x)) \<in> Infinitesimal\<close>
    proof-
      have \<open>\<forall> S. (norm (x - trunc_ell2 S x))^2 = (norm x)^2 - (norm (trunc_ell2 S x))^2\<close>
        by (simp add: trunc_ell2_norm_diff)        
      hence \<open>\<forall> S. (hnorm (star_of x - (*f2* trunc_ell2) S (star_of x)))^2 = (hnorm (star_of x))^2 - (hnorm ((*f2* trunc_ell2) S (star_of x)))^2\<close>
        by StarDef.transfer
      hence \<open>(hnorm (star_of x - (*f2* trunc_ell2) S (star_of x)))^2 = (hnorm (star_of x))^2 - (hnorm ((*f2* trunc_ell2) S (star_of x)))^2\<close>
        by blast
      moreover have \<open>(hnorm (star_of x))^2 \<approx> (hnorm ((*f2* trunc_ell2) S (star_of x)))^2\<close>
      proof-
        have \<open>\<forall> S. finite S \<longrightarrow> sqrt ((sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S) = (norm (trunc_ell2 S x))\<close>
          using trunc_ell2_norm_explicit
          by metis          
        hence \<open>\<forall> S. finite S \<longrightarrow> (sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S = (norm (trunc_ell2 S x))\<^sup>2\<close>
          using real_sqrt_eq_iff
          by (smt norm_le_zero_iff norm_zero real_sqrt_unique)           
        hence \<open>\<forall> S. hypfinite S \<longrightarrow> (*f* sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S = (hnorm ((*f2* trunc_ell2) S (star_of x)))\<^sup>2\<close>
          unfolding hypfinite_def
          by StarDef.transfer
        hence \<open>(*f* sum (\<lambda>i. (cmod (Rep_ell2 x i))\<^sup>2)) S = (hnorm ((*f2* trunc_ell2) S (star_of x)))\<^sup>2\<close>
          using \<open>hypfinite S\<close> by blast
        hence \<open>(*f* f) S = (hnorm ((*f2* trunc_ell2) S (star_of x)))^2\<close>
          unfolding f_def by blast
        thus ?thesis using \<open>(*f* f) S \<approx> (hnorm (star_of x))^2\<close>
          by (simp add: approx_reorient)          
      qed
      ultimately have \<open>(hnorm (star_of x - (*f2* trunc_ell2) S (star_of x)))^2 \<approx> 0\<close>
        using approx_minus_iff by auto
      hence \<open>(hnorm (star_of x - (*f2* trunc_ell2) S (star_of x)))^2 \<in> Infinitesimal\<close>
        by (simp add: mem_infmal_iff)       
      hence \<open>hnorm (star_of x - (*f2* trunc_ell2) S (star_of x)) \<in> Infinitesimal\<close>
        using infinitesimal_square by blast        
      thus ?thesis
        by simp 
    qed
    thus ?thesis
      by (meson Infinitesimal_hnorm_iff approx_sym bex_Infinitesimal_iff) 
  qed
  ultimately show ?thesis
    by blast
qed

lemma trunc_ell2_complex_span_induct:
  \<open>\<forall> S. finite S \<and> card S = n \<longrightarrow> trunc_ell2 S x \<in> (complex_vector.span (range (ket::('a \<Rightarrow>'a ell2))))\<close>
proof (induction n)
  show "\<forall>S. finite S \<and> card S = 0 \<longrightarrow> trunc_ell2 S x \<in> complex_vector.span (range ket)"
  proof
    show "finite S \<and> card S = 0 \<longrightarrow> trunc_ell2 S x \<in> complex_vector.span (range ket)"
      for S :: "'a set"
    proof
      show "trunc_ell2 S x \<in> complex_vector.span (range ket)"
        if "finite S \<and> card S = 0"
        using that proof
        show "trunc_ell2 S x \<in> complex_vector.span (range ket)"
          if "finite S"
            and "card S = 0"
        proof-
          have \<open>S = {}\<close>
            using card_0_eq that(1) that(2) by blast
          hence \<open>trunc_ell2 S x = 0\<close>
            apply transfer
            by simp
          thus ?thesis
            by (simp add: complex_vector.span_zero) 
        qed
      qed
    qed
  qed
  show "\<forall>S. finite S \<and> card S = Suc n \<longrightarrow> trunc_ell2 S x \<in> complex_vector.span (range ket)"
    if "\<forall>S. finite S \<and> card S = n \<longrightarrow> trunc_ell2 S x \<in> complex_vector.span (range ket)"
    for n :: nat
  proof-
    have \<open>finite S \<Longrightarrow> card S = Suc n \<Longrightarrow> trunc_ell2 S x \<in> complex_vector.span (range ket)\<close>
      for S
    proof-
      assume \<open>finite S\<close> and \<open>card S = Suc n\<close>
      hence \<open>\<exists> R k. S = insert k R \<and> card R = n\<close>
        by (meson card_Suc_eq)
      then obtain R k where \<open>S = insert k R\<close> and \<open>card R = n\<close>
        by blast
      hence \<open>finite R\<close>
        using \<open>finite S\<close>
        by simp
      have \<open>k \<notin> R\<close>
        using \<open>S = insert k R\<close> \<open>card R = n\<close> \<open>card S = Suc n\<close> insert_absorb by fastforce
      hence \<open>trunc_ell2 S x = trunc_ell2 R x + (Rep_ell2 x k) *\<^sub>C ket k\<close>
        using \<open>S = insert k R\<close> truc_ell2_insert
        by (simp add: truc_ell2_insert) 
      moreover have \<open>trunc_ell2 R x \<in> complex_vector.span (range ket)\<close>
        by (simp add: \<open>card R = n\<close> \<open>finite R\<close> that)
      ultimately show \<open>trunc_ell2 S x \<in> complex_vector.span (range ket)\<close>
        by (simp add: complex_vector.span_add complex_vector.span_base complex_vector.span_scale)        
    qed
    thus ?thesis by blast
  qed
qed


lemma trunc_ell2_complex_span:
  \<open>finite S \<Longrightarrow> trunc_ell2 S x \<in> (complex_vector.span (range (ket::('a \<Rightarrow>'a ell2))))\<close>
  using trunc_ell2_complex_span_induct by auto

lemma ket_ell2_span:
  \<open>closure (complex_vector.span (range (ket::('a \<Rightarrow>'a ell2)))) = UNIV\<close>
proof
  include nsa_notation
  show "closure (complex_vector.span (range ket)) \<subseteq> (UNIV::'a ell2 set)"
    by simp    
  show "(UNIV::'a ell2 set) \<subseteq> closure (complex_vector.span (range ket))"
  proof
    show "(x::'a ell2) \<in> closure (complex_vector.span (range ket))"
      if "(x::'a ell2) \<in> UNIV"
      for x :: "'a ell2"
    proof-
      have \<open>\<exists> a \<in> *s* (complex_vector.span (range ket)). star_of x \<approx> a\<close>
      proof-
        have \<open>\<exists> S. hypfinite S \<and> (*f2* trunc_ell2) S (star_of x) \<approx> star_of x\<close>
          using trunc_ell2_lim by auto
        then obtain S where \<open>hypfinite S\<close> and \<open>(*f2* trunc_ell2) S (star_of x) \<approx> star_of x\<close>
          by blast
        have \<open>(*f2* trunc_ell2) S (star_of x) \<in> *s* (complex_vector.span (range ket))\<close>
        proof-
          have \<open>\<forall> S. finite S \<longrightarrow> trunc_ell2 S x \<in> (complex_vector.span (range (ket::('a \<Rightarrow>'a ell2))))\<close>
            by (simp add: trunc_ell2_complex_span)
          hence \<open>\<forall> S. hypfinite S \<longrightarrow> (*f2* trunc_ell2) S (star_of x) \<in> *s* (complex_vector.span (range (ket::('a \<Rightarrow>'a ell2))))\<close>
            unfolding hypfinite_def
            by StarDef.transfer
          thus ?thesis
            by (simp add: \<open>hypfinite S\<close>) 
        qed
        thus ?thesis using \<open>(*f2* trunc_ell2) S (star_of x) \<approx> star_of x\<close>
          using approx_sym by blast          
      qed
      thus ?thesis using nsclosure_iff
        by blast
    qed
  qed
qed


instantiation ell2 :: (enum) onb_enum begin
definition "canonical_basis_ell2 = map ket Enum.enum"
definition "canonical_basis_length_ell2 (_::'a ell2 itself) = CARD('a)"
instance
proof
  show "distinct (canonical_basis::'a ell2 list)"
  proof-
    have \<open>finite (UNIV::'a set)\<close>
      by simp
    have \<open>distinct (enum_class.enum::'a list)\<close>
      using enum_distinct by blast
    moreover have \<open>inj_on ket (set enum_class.enum)\<close>
      by (meson inj_onI ket_distinct)         
    ultimately show ?thesis
      unfolding canonical_basis_ell2_def
      using distinct_map
      by blast
  qed    
  show "is_ortho_set (set (canonical_basis::'a ell2 list))"
  proof-
    have \<open>x\<in>set (canonical_basis::'a ell2 list) \<Longrightarrow> y\<in>set canonical_basis 
      \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<langle>x, y\<rangle> = 0\<close>
      for x y
    proof-
      assume \<open>x\<in>set (canonical_basis::'a ell2 list)\<close> and \<open>y\<in>set canonical_basis\<close>
        and \<open>x \<noteq> y\<close>
      from \<open>x\<in>set (canonical_basis::'a ell2 list)\<close>
      have \<open>\<exists> i. x = ket i\<close>
        unfolding canonical_basis_ell2_def
        by auto
      then obtain i where \<open>x = ket i\<close>
        by blast
      from \<open>y\<in>set (canonical_basis::'a ell2 list)\<close>
      have \<open>\<exists> j. y = ket j\<close>
        unfolding canonical_basis_ell2_def
        by auto
      then obtain j where \<open>y = ket j\<close>
        by blast
      have \<open>i \<noteq> j\<close>
        using \<open>x \<noteq> y\<close>  \<open>x = ket i\<close>  \<open>y = ket j\<close>
        by auto
      hence \<open>\<langle>ket i, ket j\<rangle> = 0\<close>
        by (simp add: ket_Kronecker_delta_neq)
      thus \<open>\<langle>x, y\<rangle> = 0\<close>
        using  \<open>x = ket i\<close>  \<open>y = ket j\<close>
        by simp
    qed
    thus ?thesis
      unfolding is_ortho_set_def
      by blast
  qed

  show "is_basis (set (canonical_basis::'a ell2 list))"
  proof-
    show "is_basis (set (canonical_basis::'a ell2 list))"
      unfolding canonical_basis_ell2_def is_basis_def
    proof
      show "complex_vector.independent (set (map ket (enum_class.enum::'a list)))"
      proof-
        have \<open>0 \<notin> set (canonical_basis::'a ell2 list)\<close>
        proof (rule classical)
          assume \<open>\<not> (0::'a ell2) \<notin> set canonical_basis\<close>
          hence \<open>(0::'a ell2) \<in> set canonical_basis\<close>
            by blast
          hence \<open>\<exists> i. (0::'a ell2) = ket i\<close>
            unfolding canonical_basis_ell2_def
            by auto
          then obtain i where \<open>(0::'a ell2) = ket i\<close>
            by blast
          hence \<open>Rep_ell2 (0::'a ell2) i = Rep_ell2 (ket i) i\<close>
            by simp
          moreover have \<open>Rep_ell2 (0::'a ell2) i = 0\<close>
            apply transfer by blast
          moreover have \<open>Rep_ell2 (ket i) i = 1\<close>
            apply transfer by auto
          ultimately show ?thesis by simp
        qed
        thus ?thesis 
          using  \<open>is_ortho_set (set (canonical_basis::'a ell2 list))\<close> is_ortho_set_independent
          unfolding canonical_basis_ell2_def
          by (metis Complex_Vector_Spaces.dependent_raw_def)            
      qed
      show "closure (complex_vector.span (set (map ket (enum_class.enum::'a list)))) = UNIV"
      proof-
        have \<open>closure
              (complex_vector.span (ket ` UNIV)) = UNIV\<close>
          by (simp add: ket_ell2_span)
        moreover have \<open>set (enum_class.enum::'a list) = UNIV\<close>
          using UNIV_enum
          by blast
        ultimately have \<open>closure
              (complex_vector.span (ket ` set (enum_class.enum::'a list))) = UNIV\<close>
          by simp
        thus ?thesis
          by auto
      qed
    qed
  qed
  show "canonical_basis_length (TYPE('a ell2)::'a ell2 itself) = length (canonical_basis::'a ell2 list)"
    unfolding canonical_basis_length_ell2_def canonical_basis_ell2_def
    using card_UNIV_length_enum
    by auto
  show "norm (x::'a ell2) = 1"
    if "(x::'a ell2) \<in> set canonical_basis"
    for x :: "'a ell2"
    using that unfolding canonical_basis_ell2_def 
    by auto
qed

end

(* TODO: move *)
(* Ask to Dominique: where? *)
instantiation unit :: CARD_1
begin
instance 
  apply standard 
  by auto
end


(* TODO remove (is obsolete because of \<open>instantiation ell2 :: (CARD_1) one_dim\<close>). *)
(* Jose: If I remove it, I obtain errors *)
(* TODO: probably because \<open>instantiation ell2 :: (CARD_1) one_dim\<close> is only at the end of the file
   if you move it forward to here, things should work. Any other unfixable errors?
  Ask to Dominique: Could we delete it right now in order to see what happens?
 *)
instantiation ell2 :: (CARD_1) complex_algebra_1 
begin
lift_definition one_ell2 :: "'a ell2" is "\<lambda>_. 1" by simp
lift_definition times_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a b x. a x * b x"
  by simp   
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
    by (transfer, rule ext, auto)
  show "(a::'a ell2) * 1 = a"
    for a :: "'a ell2"
    by (transfer, rule ext, auto)
  show "(0::'a ell2) \<noteq> 1"
    apply transfer
    by (meson zero_neq_one)
qed
end


lemma superposition_principle_linear_ket:
  fixes A B :: \<open>('a::cbanach ell2, 'b::cbanach) cblinfun\<close>
  shows \<open>(\<And> x. cblinfun_apply A (ket x) = cblinfun_apply B (ket x)) \<Longrightarrow> A = B\<close>
proof-
  assume \<open>\<And> x. cblinfun_apply A (ket x) = cblinfun_apply B (ket x)\<close>
  define S::\<open>('a ell2) set\<close> where \<open>S = range ket\<close>
  have \<open>\<And>x. x \<in> S \<Longrightarrow> cblinfun_apply A x = cblinfun_apply B x\<close>
    using S_def \<open>\<And>x. cblinfun_apply A (ket x) = cblinfun_apply B (ket x)\<close> by blast
  have \<open>cblinfun_apply A t = cblinfun_apply B t\<close>
    for t
  proof-
    have \<open>t \<in> closure (complex_vector.span S)\<close>
    proof-
      have \<open>closure (complex_vector.span S) = UNIV\<close>
        by (simp add: S_def ket_ell2_span)        
      thus ?thesis by blast
    qed
    thus ?thesis
      using Span.rep_eq \<open>\<And>x. x \<in> S \<Longrightarrow> cblinfun_apply A x = cblinfun_apply B x\<close> applyOpSpace_span
      by smt
  qed
  hence \<open>cblinfun_apply A = cblinfun_apply B\<close>
    by blast
  thus ?thesis using cblinfun_apply_inject by auto
qed



lemma superposition_principle_bounded_sesquilinear_ket:
  \<open>bounded_sesquilinear B \<Longrightarrow> (\<And> i j. B (ket i) (ket j) = 0) \<Longrightarrow> (\<And> x y. B x y = 0)\<close>
proof-
  include nsa_notation
  assume \<open>bounded_sesquilinear B\<close>
    and \<open>\<And> i j. B (ket i) (ket j) = 0\<close>
  show \<open>B x y = 0\<close>
    for x y
  proof-
    have \<open>x \<in> closure (complex_vector.span (range ket))\<close>
      by (metis iso_tuple_UNIV_I ket_ell2_span)      
    hence \<open>\<exists> u\<in>*s* (complex_vector.span (range ket)). star_of x \<approx> u\<close>
      using nsclosure_I by blast
    then obtain u where \<open>u\<in>*s* (complex_vector.span (range ket))\<close> and \<open>star_of x \<approx> u\<close>
      by blast
    have \<open>y \<in> closure (complex_vector.span (range ket))\<close>
      by (simp add: ket_ell2_span)      
    hence \<open>\<exists> v\<in>*s* (complex_vector.span (range ket)). star_of y \<approx> v\<close>
      using nsclosure_I by blast
    then obtain v where \<open>v\<in>*s* (complex_vector.span (range ket))\<close> and \<open>star_of y \<approx> v\<close>
      by blast
    have \<open>(*f2* B) u v = 0\<close>
    proof-
      have  \<open>p \<in> (complex_vector.span (range ket)) \<Longrightarrow> q \<in> (complex_vector.span (range ket))
        \<Longrightarrow> B p q = 0\<close>
        for p q
      proof-
        assume \<open>p \<in> (complex_vector.span (range ket))\<close>
          and \<open>q \<in> (complex_vector.span (range ket))\<close>
        define S_left::\<open>('a ell2) set\<close> where \<open>S_left = range (ket)\<close>
        define S_right::\<open>('b ell2) set\<close> where \<open>S_right = range (ket)\<close>
        from \<open>\<And> i j. B (ket i) (ket j) = 0\<close>
        have \<open>\<And>p q. p \<in> S_left \<Longrightarrow> q \<in> S_right \<Longrightarrow> B p q = 0\<close>
          using S_left_def S_right_def by blast          
        thus \<open>B p q = 0\<close>
          using  \<open>bounded_sesquilinear B\<close> sesquilinear_superposition
            S_left_def S_right_def \<open>p \<in> complex_vector.span (range ket)\<close> 
            \<open>q \<in> complex_vector.span (range ket)\<close>
          by smt (* > 1s *)
      qed
      hence  \<open>\<forall> p \<in> (complex_vector.span (range ket)). \<forall> q \<in> (complex_vector.span (range ket)). B p q = 0\<close>
        by blast
      hence \<open>\<forall> p \<in> *s* (complex_vector.span (range ket)). \<forall> q \<in> *s* (complex_vector.span (range ket)). (*f2* B) p q = 0\<close>
        by StarDef.transfer
      thus ?thesis
        using \<open>u \<in> *s* Complex_Vector_Spaces.complex_vector.span (range ket)\<close> \<open>v \<in> *s* Complex_Vector_Spaces.complex_vector.span (range ket)\<close> by blast 
    qed
    moreover have \<open>(*f2* B) (star_of x) (star_of y) \<approx> (*f2* B) u v\<close>
      using bounded_sesquilinear_continuous  \<open>bounded_sesquilinear B\<close>
        \<open>star_of x \<approx> u\<close> \<open>star_of y \<approx> v\<close> by blast
    ultimately have \<open>(*f2* B) (star_of x) (star_of y) \<approx> 0\<close>
      by simp
    hence \<open>(*f2* B) (star_of x) (star_of y) \<in> Infinitesimal\<close>
      by simp
    thus \<open>B x y = 0\<close>
      by simp
  qed
qed


lemma equal_basis_0:
  assumes \<open>\<And> j. cblinfun_apply A (ket j) = 0\<close>
  shows \<open>A = 0\<close>
proof-
  include nsa_notation
  have \<open>x \<in> closure (complex_vector.span (range ket)) \<Longrightarrow> cblinfun_apply A x = 0\<close>
    for x
  proof-
    assume \<open>x \<in> closure (complex_vector.span (range ket))\<close>
    hence \<open>\<exists> r \<in> *s* (complex_vector.span (range ket)). r \<approx> star_of x\<close>
      using approx_sym nsclosure_I by blast
    then obtain r where \<open>r \<in> *s* (complex_vector.span (range ket))\<close> and \<open>r \<approx> star_of x\<close>
      by blast
    have \<open>cbounded_linear (cblinfun_apply A)\<close>
      using cblinfun_apply by blast
    hence \<open>isCont (cblinfun_apply A) x\<close>
      by simp
    hence \<open>isNSCont (cblinfun_apply A) x\<close>
      by (simp add: isCont_isNSCont)
    have \<open>x \<in> complex_vector.span (range ket) \<Longrightarrow> cblinfun_apply A x = 0\<close>
      for x
    proof-
      assume \<open>x \<in> complex_vector.span (range ket)\<close>
      have \<open>\<exists> t r. finite t \<and> t \<subseteq> (range ket) \<and> x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        using complex_vector.span_explicit
        by (smt \<open>x \<in> complex_vector.span (range ket)\<close> mem_Collect_eq)
      then obtain t r where  \<open>finite t\<close> and \<open>t \<subseteq> (range ket)\<close> and \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        by blast
      from  \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      have  \<open>cblinfun_apply A x = (\<Sum>a\<in>t. r a *\<^sub>C (cblinfun_apply A a))\<close>
        unfolding cbounded_linear_def
        using cblinfun_apply \<open>finite t\<close>
          Finite_Cartesian_Product.sum_cong_aux assms complex_vector.linear_scale
          complex_vector.linear_sum
          \<open>cbounded_linear (cblinfun_apply A)\<close> cbounded_linear.is_clinear
        by smt
      moreover have \<open>\<forall> a\<in>t. r a *\<^sub>C (cblinfun_apply A a) = 0\<close>
        using \<open>t \<subseteq> (range ket)\<close> \<open>\<And> j. cblinfun_apply A (ket j) = 0\<close>
          complex_vector.scale_eq_0_iff by blast
      ultimately show \<open>cblinfun_apply A x = 0\<close>
        by simp
    qed
    hence \<open>\<forall> x \<in> complex_vector.span (range ket). (cblinfun_apply A) x = 0\<close>
      by blast
    hence \<open>\<forall> x \<in>*s* (complex_vector.span (range ket)). (*f* (cblinfun_apply A)) x = 0\<close>
      by StarDef.transfer
    hence \<open>(*f* (cblinfun_apply A)) r = 0\<close>
      using \<open>r \<in> *s* (complex_vector.span (range ket))\<close>
      by blast
    moreover have \<open>(*f* (cblinfun_apply A)) r \<approx> (*f* (cblinfun_apply A)) (star_of x)\<close>
      using \<open>r \<approx> star_of x\<close> \<open>isNSCont (cblinfun_apply A) x\<close>
      by (simp add: isNSContD)
    ultimately have \<open>(*f* (cblinfun_apply A)) (star_of x) \<approx> 0\<close>
      by simp
    hence \<open>norm ( (cblinfun_apply A) x ) = 0\<close>
      by auto
    thus \<open>cblinfun_apply A x = 0\<close>
      by auto
  qed
  moreover have \<open>closure (complex_vector.span (range ket)) = UNIV\<close>
    by (simp add: ket_ell2_span)        
  ultimately have \<open>cblinfun_apply A x = 0\<close>
    for x
    by blast
  hence \<open>cblinfun_apply A = (\<lambda> _. 0)\<close>
    by blast
  thus ?thesis using cblinfun_apply_inject
    by fastforce 
qed

lemma equal_basis:
  assumes \<open>\<And> j. cblinfun_apply A (ket j) = cblinfun_apply B (ket j)\<close>
  shows \<open>A = B\<close>
proof-
  have \<open>\<And> j. cblinfun_apply A (ket j) - cblinfun_apply B (ket j) = 0\<close>
    using \<open>\<And> j. cblinfun_apply A (ket j) = cblinfun_apply B (ket j)\<close> by simp
  hence \<open>\<And> j. cblinfun_apply (A - B) (ket j) = 0\<close>
    by (simp add: minus_cblinfun.rep_eq)
  hence \<open>A - B = 0\<close>
    using equal_basis_0 by blast
  thus ?thesis by simp
qed


subsection \<open>Recovered theorems\<close>

lemma cnj_x_x: "cnj x * x = (abs x)\<^sup>2"
  apply (cases x)
  by (auto simp: complex_cnj complex_mult abs_complex_def complex_norm power2_eq_square complex_of_real_def)

lemma cnj_x_x_geq0[simp]: "cnj x * x \<ge> 0"
  apply (cases x)
  by (auto simp: complex_cnj complex_mult complex_of_real_def less_eq_complex_def)

lemma norm_vector_component: "norm (Rep_ell2 x i) \<le> norm x"
  using norm_ell2_component
  by (simp add: norm_ell2_component) 

lemma Cauchy_vector_component: 
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
      by (rule norm_vector_component)
    also have "Rep_ell2 (X i - X i') j = x i j - x i' j"
      unfolding x_def
      by (simp add: minus_ell2.rep_eq)       
    also have "norm (x i j - x i' j) = dist (x i j) (x i' j)"
      unfolding dist_norm by simp
    finally show ?thesis by assumption
  qed
  thus ?thesis
    unfolding Cauchy_def
    using \<open>Cauchy X\<close> unfolding Cauchy_def
    by (meson le_less_trans) 
qed

lemma subspace_inter[simp]: 
  assumes "complex_vector.subspace A" and "complex_vector.subspace B" 
  shows "complex_vector.subspace (A\<inter>B)"
  by (simp add: assms(1) assms(2) complex_vector.subspace_inter)

lemma subspace_contains_0: "complex_vector.subspace A \<Longrightarrow> 0 \<in> A"
  unfolding complex_vector.subspace_def by auto

lemma subspace_INF[simp]: "(\<And>x. x \<in> AA \<Longrightarrow> complex_vector.subspace x) \<Longrightarrow> complex_vector.subspace (\<Inter>AA)"
  by (simp add: complex_vector.subspace_Inter)

lemma subspace_sup_plus: "(sup :: 'a ell2_clinear_space \<Rightarrow> _ \<Rightarrow> _) = (+)"
  by simp 



lemma subspace_zero_bot: "(0::_ ell2_clinear_space) = bot" 
  by simp

lemma  subspace_plus_sup: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y + z \<le> x" 
  for x y z :: "'a ell2_clinear_space"
  unfolding subspace_sup_plus[symmetric] by auto

lemma subspace_empty_Sup: "Sup {} = (0::'a ell2_clinear_space)"
  unfolding subspace_zero_bot by auto

lemma top_not_bot[simp]: "(top::'a ell2_clinear_space) \<noteq> bot"
  by (metis subspace_zero_bot subspace_zero_not_top) 

lemma bot_not_top[simp]: "(bot::'a ell2_clinear_space) \<noteq> top"
  using top_not_bot
  by simp 

lemma inf_assoc_subspace[simp]: "A \<sqinter> B \<sqinter> C = A \<sqinter> (B \<sqinter> C)" 
  for A B C :: "_ ell2_clinear_space"
  unfolding inf.assoc by simp

lemma inf_left_commute[simp]: "A \<sqinter> (B \<sqinter> C) = B \<sqinter> (A \<sqinter> C)" for A B C :: "_ ell2_clinear_space"
  using inf.left_commute by auto

lemma bot_plus[simp]: "bot + x = x" 
  for x :: "'a ell2_clinear_space"
  by simp

lemma plus_bot[simp]: "x + bot = x" for x :: "'a ell2_clinear_space" unfolding subspace_sup_plus[symmetric] by simp
lemma top_plus[simp]: "top + x = top" for x :: "'a ell2_clinear_space" unfolding subspace_sup_plus[symmetric] by simp
lemma plus_top[simp]: "x + top = top" for x :: "'a ell2_clinear_space" unfolding subspace_sup_plus[symmetric] by simp


lemma leq_plus_subspace[simp]: "a \<le> a + c" for a::"'a ell2_clinear_space"
  by (simp add: add_increasing2)
lemma leq_plus_subspace2[simp]: "a \<le> c + a" for a::"'a ell2_clinear_space"
  by (simp add: add_increasing)

lemma ket_is_orthogonal[simp]:
  "is_orthogonal (ket x) (ket y) \<longleftrightarrow> x \<noteq> y"
  unfolding is_orthogonal_def
  by (metis ket_Kronecker_delta_eq ket_Kronecker_delta_neq zero_neq_one) 

lemma Span_range_ket[simp]: "Span (range ket) = (top::('a ell2_clinear_space))"
proof-
  have \<open>closure (complex_vector.span (range ket)) = (UNIV::'a ell2 set)\<close>
    using Complex_L2.ket_ell2_span by blast
  thus ?thesis
    by (simp add: Span.abs_eq top_clinear_space.abs_eq)
qed

lemma [simp]: "ket i \<noteq> 0"
  using ell2_ket[of i] by force

lemma equal_ket:
  includes cblinfun_notation
  assumes "\<And>x. cblinfun_apply A (ket x) = cblinfun_apply B (ket x)"
  shows "A = B"
  by (simp add: assms equal_basis)


lemma enum_CARD_1: "(Enum.enum :: 'a::{CARD_1,enum} list) = [a]"
proof -
  let ?enum = "Enum.enum :: 'a::{CARD_1,enum} list"
  have "length ?enum = 1"
    apply (subst card_UNIV_length_enum[symmetric])
    by (rule CARD_1)
  then obtain b where "?enum = [b]"
    apply atomize_elim
    apply (cases ?enum, auto)
    by (metis length_0_conv length_Cons nat.inject)
  then show "?enum = [a]"
    by (subst everything_the_same[of _ b], simp)
qed

instantiation ell2 :: ("{enum,CARD_1}") one_dim begin
text \<open>Note: enum is not really needed, but without it this instantiation
clashes with \<open>instantiation ell2 :: (enum) onb_enum\<close>\<close>
instance
proof
  show "canonical_basis = [1::'a ell2]"
    unfolding canonical_basis_ell2_def
    apply transfer
    by (simp add: enum_CARD_1[of undefined])
  show "a *\<^sub>C 1 * b *\<^sub>C 1 = (a * b) *\<^sub>C (1::'a ell2)" for a b
    apply (transfer fixing: a b) by simp
qed

end

subsection \<open>Classical operators\<close>

definition classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L'b ell2" where
  "classical_operator \<pi> = 
    (let f = (\<lambda>t. (case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i))
     in
      cblinfun_extension (range (ket::'a\<Rightarrow>_)) f
    )"


lemma classical_operator_basis:
  defines  "classical_function  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i)"
  assumes a1:"cblinfun_extension_exists (range (ket::'a\<Rightarrow>_)) (classical_function \<pi>)"
  shows "(classical_operator \<pi>) *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  unfolding classical_operator_def 
  using    f_inv_into_f ket_distinct rangeI
  by (metis (mono_tags, lifting) a1 cblinfun_extension_exists cblinfun_extension_exists_def 
      classical_function_def)

lemma ket_nonzero: "(ket::'a\<Rightarrow>_) i \<noteq> 0"
  apply transfer
  by (metis zero_neq_one)

lemma complex_independent_ket:
  "complex_independent (range (ket::'a\<Rightarrow>_))"
proof-
  define S where "S = range (ket::'a\<Rightarrow>_)"
  have "is_ortho_set S"
    unfolding S_def is_ortho_set_def apply auto
    by (metis ket_Kronecker_delta_neq)
  moreover have "0 \<notin> S"
    unfolding S_def
    using ket_nonzero
    by (simp add: image_iff)
  ultimately show ?thesis
    using is_ortho_set_independent[where S = S] unfolding S_def 
    by blast
qed

lemma classical_operator_finite:
  "(classical_operator \<pi>) *\<^sub>V (ket (x::'a::finite)) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
proof -
  have 1: "complex_independent (range (ket::'a\<Rightarrow>_))"
    by (simp add: complex_independent_ket)    
  have 2: "complex_vector.span (range (ket::'a\<Rightarrow>_)) = UNIV"
    using finite_class.finite_UNIV finite_imageI ket_ell2_span span_finite_dim by blast    
  show ?thesis
    apply (rule classical_operator_basis)
    apply (rule cblinfun_extension_exists_finite)
    using 1 2 by auto
qed

lemma cinner_ket_adjointI:
  fixes F::"'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _" and G::"'b ell2 \<Rightarrow>\<^sub>C\<^sub>L_"
  assumes a1: "\<And> i j. \<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>ket i, G *\<^sub>V ket j\<rangle>"
  shows "F = G*" 
proof-
  have "\<langle>F *\<^sub>V x, y\<rangle> = \<langle>x, G *\<^sub>V y\<rangle>"
    for x::"'a ell2" and y::"'b ell2"
  proof-
    define H where "H u v = \<langle>F *\<^sub>V u, v\<rangle> - \<langle>u, G *\<^sub>V v\<rangle>" for u v
    define SA where "SA = range (ket::'a\<Rightarrow>_)"
    define SB where "SB = range (ket::'b\<Rightarrow>_)"
    have u1: "closure (complex_vector.span SA) = UNIV"
      unfolding SA_def using ket_ell2_span by blast
    hence v1: "x \<in> closure (complex_vector.span (range ket))"
      unfolding SA_def by blast
    have u2: "closure (complex_vector.span SB) = UNIV"
      unfolding SB_def using ket_ell2_span by blast
    hence v2: "y \<in> closure (complex_vector.span (range ket))"
      unfolding SB_def by blast
    have "H (ket i) (ket j) = 0"
      for i j
      unfolding H_def using a1 by simp
    moreover have q1: "cbounded_linear (H (ket i))"
      for i
    proof-
      have "cbounded_linear (\<lambda>v. \<langle>F *\<^sub>V (ket i), v\<rangle>)"
        by (simp add: cbounded_linear_cinner_right)      
      moreover have "cbounded_linear (\<lambda>v. \<langle>ket i, G *\<^sub>V v\<rangle>)"
        using cblinfun_apply cbounded_linear_cinner_right_comp by auto      
      ultimately show ?thesis unfolding H_def using cbounded_linear_sub by blast
    qed
    moreover have z1: "cbounded_linear (\<lambda>_. (0::complex))"
      by simp    
    ultimately have "H (ket i) v = 0"
      if "v \<in> complex_vector.span SB"
      for i v
      using equal_span_applyOpSpace[where G = SB and A = "H (ket i)" and B = "\<lambda>_. (0::complex)"]
      by (smt SB_def UNIV_I rangeE u2)
    moreover have "continuous_on (closure (complex_vector.span SB)) (H (ket i))"
      for i
      by (simp add: q1 bounded_linear_continuous continuous_at_imp_continuous_on)
    ultimately have "H (ket i) v = 0"
      if "v \<in> closure (complex_vector.span SB)"
      for i v
      using continuous_constant_on_closure that
      by smt
    hence "H (ket i) v = 0"
      for i v
      by (smt UNIV_I u2)
    moreover have jj: "cbounded_linear (\<lambda>u. cnj (H u v))"
      for v
    proof-
      have "cbounded_linear (\<lambda>u. cnj \<langle>F *\<^sub>V u, v\<rangle>)"
        using bounded_csemilinear_compose1 cblinfun_apply cbounded_linear_cinner_left_comp 
          cnj_bounded_csemilinear by blast      
      moreover have "cbounded_linear (\<lambda>u. cnj \<langle>u, G *\<^sub>V v\<rangle>)"
        using bounded_csemilinear_cinner_left bounded_csemilinear_compose1 cnj_bounded_csemilinear 
        by blast      
      ultimately show ?thesis unfolding H_def 
        using cbounded_linear_sub [where f = "\<lambda>u. cnj \<langle>F *\<^sub>V u, v\<rangle>" and g = "\<lambda>u. cnj \<langle>u, G *\<^sub>V v\<rangle>"]
        by auto      
    qed
    ultimately have cHu0: "cnj (H u v) = 0"
      if "u \<in> complex_vector.span SA"
      for u v
      using z1 SA_def equal_span_applyOpSpace iso_tuple_UNIV_I rangeE u1 complex_cnj_zero
      by smt (* > 1s *)
    hence Hu0: "H u v = 0"
      if "u \<in> complex_vector.span SA"
      for u v
      by (smt complex_cnj_zero_iff that) 
    moreover have "continuous_on (closure (complex_vector.span SA)) (\<lambda>u. H u v)"
      for v
      using jj bounded_linear_continuous continuous_at_imp_continuous_on
        cHu0 complex_cnj_cancel_iff complex_cnj_zero complex_vector.span_span continuous_on_cong 
        equal_span_applyOpSpace z1
      by smt (* > 1s *)
    ultimately have "H u v = 0"
      if "u \<in> closure (complex_vector.span SA)"
      for u v
      using continuous_constant_on_closure that
      by smt
    hence "H u v = 0"
      for u v
      by (smt UNIV_I u1)
    thus "\<langle>F *\<^sub>V x, y\<rangle> = \<langle>x, G *\<^sub>V y\<rangle>"
      unfolding H_def by simp
  qed
  thus ?thesis
    using adjoint_D by auto 
qed

(* TODO: finite dimensional corollary as a simp-rule
  Ask to Dominique: I do not understand this TODO.
*)
lemma classical_operator_adjoint[simp]:
  fixes \<pi> :: "'a \<Rightarrow> 'b option"
  defines  "classical_function  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i)"
      and  "classical_function'  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'b\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'a ell2) 
                          | Some i \<Rightarrow> ket i)"
  assumes a1: "inj_option \<pi>"
    and a2:"cblinfun_extension_exists (range (ket::'a\<Rightarrow>_)) (classical_function \<pi>)"
    and a3:"cblinfun_extension_exists (range (ket::'b\<Rightarrow>_)) (classical_function' (inv_option \<pi>))"
  shows  "(classical_operator \<pi>)* = classical_operator (inv_option \<pi>)"
proof-
  define F where "F = classical_operator (inv_option \<pi>)"
  define G where "G = classical_operator \<pi>"
  have "\<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>ket i, G *\<^sub>V ket j\<rangle>" for i j
  proof-
    have w1: "(classical_operator (inv_option \<pi>)) *\<^sub>V (ket i)
     = (case inv_option \<pi> i of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)"
      using a3 classical_function'_def classical_operator_basis by fastforce
    have w2: "(classical_operator \<pi>) *\<^sub>V (ket j)
     = (case \<pi> j of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)"
      using a2 classical_function_def classical_operator_basis by fastforce
    have "\<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>classical_operator (inv_option \<pi>) *\<^sub>V ket i, ket j\<rangle>"
      unfolding F_def by blast
    also have "\<dots> = \<langle>(case inv_option \<pi> i of Some k \<Rightarrow> ket k | None \<Rightarrow> 0), ket j\<rangle>"
      using w1 by simp
    also have "\<dots> = \<langle>ket i, (case \<pi> j of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)\<rangle>"
    proof(induction "inv_option \<pi> i")
      case None
      hence pi1: "None = inv_option \<pi> i".
      show ?case 
      proof (induction "\<pi> j")
        case None
        thus ?case
          using pi1 by auto
      next
        case (Some c)
        have "c \<noteq> i"
        proof(rule classical)
          assume "\<not>(c \<noteq> i)"
          hence "c = i"
            by blast
          hence "inv_option \<pi> c = inv_option \<pi> i"
            by simp
          hence "inv_option \<pi> c = None"
            by (simp add: pi1)
          moreover have "inv_option \<pi> c = Some j"
            using Some.hyps unfolding inv_option_def
            apply auto
            by (metis a1 f_inv_into_f inj_option_def option.distinct(1) rangeI)
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          by (metis None.hyps Some.hyps cinner_zero_left ket_Kronecker_delta_neq option.simps(4) 
              option.simps(5)) 
      qed       
    next
      case (Some d)
      hence s1: "Some d = inv_option \<pi> i".
      show "\<langle>case inv_option \<pi> i of 
            None \<Rightarrow> 0
        | Some a \<Rightarrow> ket a, ket j\<rangle> =
       \<langle>ket i, case \<pi> j of 
            None \<Rightarrow> 0 
        | Some a \<Rightarrow> ket a\<rangle>" 
      proof(induction "\<pi> j")
        case None
        have "d \<noteq> j"
        proof(rule classical)
          assume "\<not>(d \<noteq> j)"
          hence "d = j"
            by blast
          hence "\<pi> d = \<pi> j"
            by simp
          hence "\<pi> d = None"
            by (simp add: None.hyps)
          moreover have "\<pi> d = Some i"
            using Some.hyps unfolding inv_option_def
            apply auto
            by (metis f_inv_into_f option.distinct(1) option.inject)
          ultimately show ?thesis 
            by simp
        qed
        thus ?case
          by (metis None.hyps Some.hyps cinner_zero_right ket_Kronecker_delta_neq option.case_eq_if 
              option.simps(5)) 
      next
        case (Some c)
        hence s2: "\<pi> j = Some c" by simp
        have "\<langle>ket d, ket j\<rangle> = \<langle>ket i, ket c\<rangle>"
        proof(cases "\<pi> j = Some i")
          case True
          hence ij: "Some j = inv_option \<pi> i"
            unfolding inv_option_def apply auto
             apply (metis a1 f_inv_into_f inj_option_def option.discI range_eqI)
            by (metis range_eqI)
          have "i = c"
            using True s2 by auto
          moreover have "j = d"
            by (metis option.inject s1 ij)
          ultimately show ?thesis
            by (simp add: ket_Kronecker_delta_eq) 
        next
          case False
          moreover have "\<pi> d = Some i"
            using s1 unfolding inv_option_def
            by (metis f_inv_into_f option.distinct(1) option.inject)            
          ultimately have "j \<noteq> d"
            by auto            
          moreover have "i \<noteq> c"
            using False s2 by auto            
          ultimately show ?thesis
            by (metis ket_Kronecker_delta_neq) 
        qed
        hence "\<langle>case Some d of None \<Rightarrow> 0
        | Some a \<Rightarrow> ket a, ket j\<rangle> =
       \<langle>ket i, case Some c of None \<Rightarrow> 0 | Some a \<Rightarrow> ket a\<rangle>"
          by simp          
        thus "\<langle>case inv_option \<pi> i of None \<Rightarrow> 0
        | Some a \<Rightarrow> ket a, ket j\<rangle> =
       \<langle>ket i, case \<pi> j of None \<Rightarrow> 0 | Some a \<Rightarrow> ket a\<rangle>"
          by (simp add: Some.hyps s1)          
      qed
    qed
    also have "\<dots> = \<langle>ket i, classical_operator \<pi> *\<^sub>V ket j\<rangle>"
      by (simp add: w2)
    also have "\<dots> = \<langle>ket i, G *\<^sub>V ket j\<rangle>"
      unfolding G_def by blast
    finally show ?thesis .
  qed
  hence "G* = F"
    using cinner_ket_adjointI
    by auto
  thus ?thesis unfolding G_def F_def .
qed

(* TODO: finite dimensional corollary as a simp-rule
  Ask to Dominique: I do not understand this TODO.
*)
lemma classical_operator_mult[simp]:
  fixes \<pi>::"'b \<Rightarrow> 'c option" and \<rho>::"'a \<Rightarrow> 'b option"
  defines  "classical_function  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i)"
  defines  "classical_function'  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'b\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'c ell2) 
                          | Some i \<Rightarrow> ket i)"
  defines  "classical_function''  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'c ell2) 
                          | Some i \<Rightarrow> ket i)"
  assumes a1: "inj_option \<pi>" 
    and a2: "inj_option \<rho>"  
    and a3:"cblinfun_extension_exists (range ket) (classical_function' \<pi>)"
    and a4:"cblinfun_extension_exists (range ket) (classical_function \<rho>)"
    and a5: "cblinfun_extension_exists (range ket) (classical_function'' (\<pi> \<circ>\<^sub>m \<rho>))" 
  shows "classical_operator \<pi> o\<^sub>C\<^sub>L classical_operator \<rho> = classical_operator (\<pi> \<circ>\<^sub>m \<rho>)"
proof-
  have "(classical_operator \<pi> o\<^sub>C\<^sub>L classical_operator \<rho>) *\<^sub>V (ket i)
      = (classical_operator (\<pi> \<circ>\<^sub>m \<rho>)) *\<^sub>V ket i"
    for i
  proof-
    have "(classical_operator \<pi> o\<^sub>C\<^sub>L classical_operator \<rho>) *\<^sub>V (ket i)
        = (classical_operator \<pi>) *\<^sub>V ((classical_operator \<rho>) *\<^sub>V (ket i))"
      by (simp add: times_applyOp)
    also have "\<dots> = (classical_operator \<pi>) *\<^sub>V (case \<rho> i of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)"
      using a4 classical_function_def classical_operator_basis by fastforce
    also have "\<dots> = (case \<rho> i of Some k \<Rightarrow> (classical_operator \<pi>) *\<^sub>V (ket k) 
        | None \<Rightarrow> (classical_operator \<pi>) *\<^sub>V 0)"
      by (metis option.case_distrib)
    also have "\<dots> = (case \<rho> i of Some k \<Rightarrow> (classical_operator \<pi>) *\<^sub>V (ket k) 
        | None \<Rightarrow> 0)"
      by (metis applyOp_scaleC2 complex_vector.scale_zero_left)
    also have "\<dots> = (case \<rho> i of Some k \<Rightarrow> (case \<pi> k of Some j \<Rightarrow> ket j | None \<Rightarrow> 0) 
        | None \<Rightarrow> 0)"
      using a3 classical_operator_basis
      unfolding classical_function'_def by metis
    also have "\<dots> = (case (\<pi> \<circ>\<^sub>m \<rho>) i of Some t \<Rightarrow> ket t | None \<Rightarrow> 0)"
    proof(induction "\<rho> i")
      case None
      thus ?case
        by auto 
    next
      case (Some c)
      thus ?case
        by (metis map_comp_simps(2) option.simps(5)) 
    qed
    also have "\<dots> = (classical_operator (\<pi> \<circ>\<^sub>m \<rho>)) *\<^sub>V (ket i)"
      using a5 classical_operator_basis unfolding classical_function''_def by metis
    finally show ?thesis .
  qed
  thus ?thesis
    by (simp add: equal_basis) 
qed

(* TODO

lemma classical_operator_eqI:
  assume "\<And>x. C *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  shows "classical_operator \<pi> = C" and maybe "cblinfun_extension_exists ..."

Useful for showing classical_operator_Some, 
   maybe also classical_operator_mult with less assumptions


*)

(* TODO:

lemma
assumes "inj \<pi>"
shows "cblinfun_extension_exists ..."

Reason: we can use the *old* definition of classical_operator and
        classical_operator_eqI to show that the classical_operator exists

This allows to remove cblinfun_extension_exists in lemmas that assume inj \<pi>

*)

lemma classical_operator_Some[simp]: 
  defines  "classical_function  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'a ell2) 
                          | Some i \<Rightarrow> ket i)"
  shows "classical_operator (Some::'a\<Rightarrow>_) = idOp"
proof-
  have "(classical_operator Some) *\<^sub>V (ket i)  = idOp *\<^sub>V (ket i)"
    for i::'a
  proof-
    have a1: "cblinfun_extension_exists (range ket) (classical_function (Some::'a\<Rightarrow>_))"
      unfolding cblinfun_extension_exists_def classical_function_def
      by (metis apply_idOp f_inv_into_f option.simps(5))
    have "(classical_operator Some) *\<^sub>V (ket i) = (case Some i of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)"
      using a1 classical_operator_basis unfolding classical_function_def by metis
    also have "\<dots> = ket i"
      by simp
    also have "\<dots> = idOp *\<^sub>V (ket i)"
      by simp      
    finally show ?thesis .
  qed
  thus ?thesis
    using equal_ket[where A = "classical_operator (Some::'a \<Rightarrow> _ option)"
        and B = "idOp::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _"]
    by blast
qed

lemma isometry_classical_operator[simp]:
  fixes \<pi>::"'a \<Rightarrow> 'b"
  defines  "classical_function  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i)"
      and  "classical_function'  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'b\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'a ell2) 
                          | Some i \<Rightarrow> ket i)"
      and  "classical_function''  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'a ell2) 
                          | Some i \<Rightarrow> ket i)"
  assumes a1: "inj \<pi>"
    and a2: "cblinfun_extension_exists (range ket) (classical_function (Some \<circ> \<pi>))"
    and a3: "cblinfun_extension_exists (range ket)
     (classical_function' (inv_option (Some \<circ> \<pi>)))" 
    and a4: "cblinfun_extension_exists (range ket) (classical_function'' (Some::'a\<Rightarrow>_))"
(* TODO: remove assumptions a2-a4 because we have that \<pi> inj 
  Ask to Dominique: I am not convinced that this is possible
*)
  shows "isometry (classical_operator (Some o \<pi>))"
proof -
  have b0: "inj_option (Some \<circ> \<pi>)"
    by (simp add: a1)
  have b0': "inj_option (inv_option (Some \<circ> \<pi>))"
    by simp
  have b1: "inv_option (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>) = Some" 
    apply (rule ext) unfolding inv_option_def o_def 
    using assms unfolding inj_def inv_def by auto
  hence b2: "cblinfun_extension_exists (range ket)
     (classical_function''
       (inv_option (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>)))"
    using a4 by simp
  have b3: "classical_operator (inv_option (Some \<circ> \<pi>)) o\<^sub>C\<^sub>L
            classical_operator (Some \<circ> \<pi>) = classical_operator (inv_option (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>))"
    using classical_operator_mult[where \<pi> = "inv_option (Some \<circ> \<pi>)" and \<rho> = "Some \<circ> \<pi>"]   
      b0 b0' a2 a3 b2 unfolding classical_function_def classical_function'_def 
      classical_function''_def by blast
  show ?thesis
    unfolding isometry_def
    apply (subst classical_operator_adjoint) using assms apply simp
      apply (simp add: a2)
    using a3 unfolding classical_function'_def
      apply simp
    using a2 classical_function_def apply auto[1]
    using a3 classical_function'_def apply auto[1]
    using a4 b1 b3 unfolding classical_function''_def
    by auto 
qed


(* TODO remove cblinfun-extension_exists assms because \<pi> bij 
  Ask to Dominique: I am not convinced that this is possible
*)
lemma unitary_classical_operator[simp]:
  fixes \<pi>::"'a \<Rightarrow> 'b"
  defines  "classical_function  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i)"
  and "classical_function'  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'b\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'a ell2) 
                          | Some i \<Rightarrow> ket i)"
  and  "classical_functionA  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'a ell2) 
                          | Some i \<Rightarrow> ket i)"
  and  "classical_functionB  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'b\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i)"
  assumes a1: "bij \<pi>"
    and a2: "cblinfun_extension_exists (range ket) (classical_function (Some \<circ> \<pi>))"
    and a3: "cblinfun_extension_exists (range ket)
     (classical_function' (inv_option (Some \<circ> \<pi>)))"
    and a4: "cblinfun_extension_exists (range ket) (classical_functionA (Some::'a\<Rightarrow>_))"
    and a5: "cblinfun_extension_exists (range ket) (classical_functionB (Some::'b\<Rightarrow>_))"
  shows "unitary (classical_operator (Some o \<pi>))"
proof (unfold unitary_def, rule conjI)
  have "inj \<pi>"
    using a1 bij_betw_imp_inj_on by auto
  hence "isometry (classical_operator (Some o \<pi>))"
    using a2 a3 a4 unfolding classical_function_def classical_function'_def classical_functionA_def
    by auto
  hence "classical_operator (Some \<circ> \<pi>)* o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>) = idOp"
    unfolding isometry_def by simp
  thus \<open>classical_operator (Some \<circ> \<pi>)* o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>) = idOp\<close>
    by simp 
next
  have "inj \<pi>"
    by (simp add: assms bij_is_inj)
  have comp: "Some \<circ> \<pi> \<circ>\<^sub>m inv_option (Some \<circ> \<pi>) = Some"
    apply (rule ext)
    unfolding inv_option_def o_def map_comp_def
    unfolding inv_def apply auto
     apply (metis \<open>inj \<pi>\<close> inv_def inv_f_f)
    using bij_def image_iff range_eqI
    by (metis a1)
  have "classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>)*
      = classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (inv_option (Some \<circ> \<pi>))"
    using \<open>inj \<pi>\<close> a2 a3 unfolding classical_function_def classical_function'_def
    by auto
  also have "\<dots> = classical_operator ((Some \<circ> \<pi>) \<circ>\<^sub>m (inv_option (Some \<circ> \<pi>)))"
    using classical_operator_mult a2 a3 a5 \<open>inj \<pi>\<close> comp
    unfolding classical_function_def classical_function'_def classical_functionB_def
    by auto
  also have "\<dots> = classical_operator (Some::'b\<Rightarrow>_)"
    using comp
    by simp 
  also have "\<dots> = (idOp:: 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L _)"
    using a5 unfolding classical_functionB_def by auto
  finally show "classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>)* = idOp".
qed

lemma ell2_norm_cinner:
  fixes a b :: "'a \<Rightarrow> complex" and X :: "'a set"
  assumes h1: "finite X"
  defines "x == (\<Sum>t\<in>X. a t *\<^sub>C ket t)" and "y == (\<Sum>t\<in>X. b t *\<^sub>C ket t)"
  shows "\<langle>x, y\<rangle> = (\<Sum>t\<in>X. (cnj (a t)) * b t)"
proof-
  have "\<langle>x, y\<rangle> = \<langle>(\<Sum>t\<in>X. a t *\<^sub>C ket t), (\<Sum>s\<in>X. b s *\<^sub>C ket s)\<rangle>"
    unfolding x_def y_def by blast
  also have "\<dots> = (\<Sum>t\<in>X. \<langle>a t *\<^sub>C ket t, (\<Sum>s\<in>X. b s *\<^sub>C ket s)\<rangle>)"
    using cinner_sum_left by blast
  also have "\<dots> = (\<Sum>t\<in>X. (\<Sum>s\<in>X. \<langle>a t *\<^sub>C ket t, b s *\<^sub>C ket s\<rangle>))"
    by (simp add: cinner_sum_right)
  also have "\<dots> = (\<Sum>t\<in>X. (\<Sum>s\<in>X. (cnj (a t)) * \<langle>ket t, b s *\<^sub>C ket s\<rangle>))"
    by (meson cinner_scaleC_left sum.cong)
  also have "\<dots> = (\<Sum>t\<in>X. (\<Sum>s\<in>X. (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle>))"
    by (metis (mono_tags, lifting) cinner_scaleC_right sum.cong vector_space_over_itself.scale_scale)
  also have "\<dots> = (\<Sum>t\<in>X. (cnj (a t)) * b t * \<langle>ket t, ket t\<rangle> + (\<Sum>s\<in>X-{t}. (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle>))"
  proof-
    have "t\<in>X \<Longrightarrow> (\<Sum>s\<in>X. (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle>) = (cnj (a t)) * b t * \<langle>ket t, ket t\<rangle> + (\<Sum>s\<in>X-{t}. (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle>)"
      for t
      using h1 Groups_Big.comm_monoid_add_class.sum.remove
      by (simp add: sum.remove)
    thus ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>t\<in>X. (cnj (a t)) * b t * \<langle>ket t, ket t\<rangle>)"
  proof-
    have "s\<in>X-{t} \<Longrightarrow> (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle> = 0"
      for s t
      by (metis DiffD2 ket_Kronecker_delta_neq mult_not_zero singletonI) 
    hence "(\<Sum>s\<in>X-{t}. (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle>) = 0" for t
      by (simp add: \<open>\<And>t s. s \<in> X - {t} \<Longrightarrow> cnj (a t) * b s * \<langle>ket t, ket s\<rangle> = 0\<close>)      
    thus ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>t\<in>X. (cnj (a t)) * b t)"
  proof-
    have "\<langle>ket t, ket t\<rangle> = 1" for t::'a
      by (simp add: ket_Kronecker_delta_eq)      
    thus ?thesis
      by auto 
  qed
  finally show ?thesis .
qed

lemma ell2_norm_list:
  fixes a :: "'a \<Rightarrow> complex" and X :: "'a set"
  assumes h1: "finite X"
  defines "x == (\<Sum>t\<in>X. a t *\<^sub>C ket t)"
  shows "norm x = sqrt (\<Sum>t\<in>X. (norm (a t))\<^sup>2)"
proof-
  have "(norm x)^2 = \<langle>x, x\<rangle>"
    using power2_norm_eq_cinner' by auto
  also have "\<dots> = (\<Sum>t\<in>X. (cnj (a t)) * (a t))"   
    using h1 ell2_norm_cinner[where X = X and a = a and b = a]
    using x_def by blast    
  also have "\<dots> = (\<Sum>t\<in>X. (norm (a t))\<^sup>2)"   
  proof-
    have "(cnj (a t)) * (a t) = (norm (a t))\<^sup>2" for t
      using complex_norm_square by auto      
    thus ?thesis by simp
  qed
  finally have "(norm x)^2 = (\<Sum>t\<in>X. (norm (a t))\<^sup>2)"
    using of_real_eq_iff by blast    
  thus ?thesis
    by (metis abs_norm_cancel real_sqrt_abs) 
qed


lemma Cauchy_Schwarz_complex:
  fixes a b :: "'a \<Rightarrow> complex"
  assumes h1: "finite X"
  shows "norm (\<Sum>t\<in>X. (cnj (a t)) * b t) \<le> sqrt (\<Sum>t\<in>X. (norm (a t))\<^sup>2) * sqrt (\<Sum>t\<in>X. (norm (b t))\<^sup>2)"
proof-
  define x where "x = (\<Sum>t\<in>X. a t *\<^sub>C ket t)"
  define y where "y = (\<Sum>t\<in>X. b t *\<^sub>C ket t)"
  have "\<langle>x, y\<rangle> = (\<Sum>t\<in>X. (cnj (a t)) * b t)"
    using h1 ell2_norm_cinner[where X = X and a = a and b = b]
      x_def y_def by blast    
  hence "norm \<langle>x, y\<rangle> = norm (\<Sum>t\<in>X. (cnj (a t)) * b t)"
    by simp
  moreover have "norm x = sqrt (\<Sum>t\<in>X. (norm (a t))\<^sup>2)"
    using h1 ell2_norm_list x_def by blast        
  moreover have "norm y = sqrt (\<Sum>t\<in>X. (norm (b t))\<^sup>2)"
    using h1 ell2_norm_list y_def by blast        
  moreover have "norm \<langle>x, y\<rangle> \<le> norm x * norm y"
    by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)    
  ultimately show ?thesis by simp
qed


lemma Cauchy_Schwarz_real:
  fixes a b :: "'a \<Rightarrow> real"
  assumes "finite X"
  shows "norm (\<Sum>t\<in>X. a t * b t) \<le> sqrt (\<Sum>t\<in>X. (a t)\<^sup>2) * sqrt (\<Sum>t\<in>X. (b t)\<^sup>2)"
proof-
  have "norm (\<Sum>t\<in>X. cnj (complex_of_real (a t)) * complex_of_real (b t))
    \<le> sqrt (\<Sum>t\<in>X. (cmod (complex_of_real (a t)))\<^sup>2) *
      sqrt (\<Sum>t\<in>X. (cmod (complex_of_real (b t)))\<^sup>2)"
    using assms Cauchy_Schwarz_complex [where X = X and a = a and b = b]
    by simp
  moreover have "norm (\<Sum>t\<in>X. (a t) * (b t)) = norm (\<Sum>t\<in>X. cnj (complex_of_real (a t)) * complex_of_real (b t))"
  proof-
    have "(a t) * (b t) = cnj (complex_of_real (a t)) * complex_of_real (b t)"
      for t
      by simp      
    hence "(\<Sum>t\<in>X. (a t) * (b t)) = (\<Sum>t\<in>X. cnj (complex_of_real (a t)) * complex_of_real (b t))"
      by simp
    moreover have "norm (complex_of_real (\<Sum>t\<in>X. (a t) * (b t))) = norm (\<Sum>t\<in>X. (a t) * (b t))"
    proof-
      have "cmod (complex_of_real r) = norm r" for r::real
        by auto
      thus ?thesis
        by blast 
    qed
    ultimately show ?thesis by simp
  qed
  moreover have "sqrt (\<Sum>t\<in>X. (cmod (complex_of_real (a t)))\<^sup>2) = sqrt (\<Sum>t\<in>X.  (a t)\<^sup>2)"
    by simp
  moreover have "sqrt (\<Sum>t\<in>X. (cmod (complex_of_real (b t)))\<^sup>2) = sqrt (\<Sum>t\<in>X.  (b t)\<^sup>2)"
    by simp    
  ultimately show ?thesis 
    by simp    
qed


lemma clinear_cbounded_linear_onb_enum: 
  fixes f::"'a::onb_enum \<Rightarrow> 'b::onb_enum"
  assumes "clinear f"
  shows "cbounded_linear f"
  using assms unfolding cbounded_linear_def
proof auto
  assume "clinear f"
  define basis where "basis = (canonical_basis::'a list)"
  define K::real where "K = sqrt (\<Sum>t\<in>set basis. norm (f t)^2)"

  have "norm (f x) \<le> norm x * K" for x
  proof-
    define c where "c t = complex_vector.representation (set basis) x t" for t
    have c1: "c t \<noteq> 0 \<Longrightarrow> t \<in> set basis" for t
      by (simp add: c_def complex_vector.representation_ne_zero)      
    have c2: "finite {t. c t \<noteq> 0}"
      by (metis (mono_tags, lifting) Collect_cong List.finite_set Set.filter_def c1 finite_filter)
    have basis_finite: "finite (set basis)"
      by simp
    have c3: "(\<Sum>t | c t \<noteq> 0. c t *\<^sub>C t) = x"
      unfolding c_def Complex_Vector_Spaces.representation_def
      apply auto
      subgoal
      proof-
        assume a1: "complex_independent (set basis)"
        assume a2: "x \<in> Complex_Vector_Spaces.span (set basis)"
        then have f3: "(\<Sum>a | Complex_Vector_Spaces.representation (set basis) x a \<noteq> 0. Complex_Vector_Spaces.representation (set basis) x a *\<^sub>C a) = x"
          using a1 complex_vector.sum_nonzero_representation_eq by blast
        have "Complex_Vector_Spaces.representation (set basis) x = (SOME f. (\<forall>a. f a \<noteq> 0 \<longrightarrow> a \<in> set basis) \<and> finite {a. f a \<noteq> 0} \<and> (\<Sum>a | f a \<noteq> 0. f a *\<^sub>C a) = x)"
          using a2 a1 by (simp add: complex_vector.representation_def)
        thus "(\<Sum>a | (SOME f. (\<forall>a. f a \<noteq> 0 \<longrightarrow> a \<in> set basis) \<and> finite {a. f a \<noteq> 0} \<and> (\<Sum>a | f a \<noteq> 0. f a *\<^sub>C a) = x) a \<noteq> 0. (SOME f. (\<forall>a. f a \<noteq> 0 \<longrightarrow> a \<in> set basis) \<and> finite {a. f a \<noteq> 0} \<and> (\<Sum>a | f a \<noteq> 0. f a *\<^sub>C a) = x) a *\<^sub>C a) = x"
          using f3 by presburger
      qed
      using basis_def canonical_basis_non_zero is_ortho_set_independent is_orthonormal apply auto[1]
      subgoal
      proof-
        assume "x \<notin> Complex_Vector_Spaces.span (set basis)"
        moreover have "Complex_Vector_Spaces.span (set basis) = UNIV"
        proof-
          have "Complex_Vector_Spaces.span (set basis) 
              = closure (Complex_Vector_Spaces.span (set basis))"
            by (simp add: span_finite_dim)
          thus ?thesis
            using is_basis_set
            unfolding basis_def is_basis_def
            by blast          
        qed
        ultimately show ?thesis
          by auto
      qed
      done
    hence "x = (\<Sum>t | c t \<noteq> 0. c t *\<^sub>C t)"
      by simp
    also have "\<dots> = (\<Sum>t\<in>set basis. c t *\<^sub>C t)"
      using DiffD2 List.finite_set c1 complex_vector.scale_eq_0_iff mem_Collect_eq subsetI 
        sum.mono_neutral_cong_left
      by smt (* > 1s *)
    finally have c4: "x = (\<Sum>t\<in>set basis. c t *\<^sub>C t)"
      by blast
    hence "f x = (\<Sum>t\<in>set basis. c t *\<^sub>C f t)"
      by (smt assms complex_vector.linear_scale complex_vector.linear_sum sum.cong)
    hence "norm (f x) = norm (\<Sum>t\<in>set basis. c t *\<^sub>C f t)"
      by simp
    also have "\<dots> \<le> (\<Sum>t\<in>set basis. norm (c t *\<^sub>C f t))"
      by (simp add: sum_norm_le)
    also have "\<dots> = (\<Sum>t\<in>set basis. norm (c t) * norm (f t))"
      by auto
    also have "\<dots> = norm (\<Sum>t\<in>set basis. norm (c t) * norm (f t))"
    proof-
      have "(\<Sum>t\<in>set basis. norm (c t) * norm (f t)) \<ge> 0"
        by (smt calculation norm_ge_zero)        
      thus ?thesis by simp
    qed
    also have "\<dots> \<le> sqrt (\<Sum>t\<in>set basis. (norm (c t))^2) * sqrt (\<Sum>t\<in>set basis. (norm (f t))^2)"
      using Cauchy_Schwarz_real
      by fastforce
    also have "\<dots> \<le> norm x * K"
    proof-
      have "(norm x)^2 = \<langle>x, x\<rangle>"
        using power2_norm_eq_cinner' by blast
      also have "\<dots> = \<langle>(\<Sum>t\<in>set basis. c t *\<^sub>C t), (\<Sum>s\<in>set basis. c s *\<^sub>C s)\<rangle>"
        using c4
        by simp 
      also have "\<dots> = (\<Sum>t\<in>set basis. \<langle>c t *\<^sub>C t, (\<Sum>s\<in>set basis. c s *\<^sub>C s)\<rangle>)"
        using cinner_sum_left by blast
      also have "\<dots> = (\<Sum>t\<in>set basis. (\<Sum>s\<in>set basis. \<langle>c t *\<^sub>C t, c s *\<^sub>C s\<rangle>))"
        by (metis (mono_tags, lifting) cinner_sum_right sum.cong)
      also have "\<dots> = (\<Sum>t\<in>set basis. (\<Sum>s\<in>set basis. c s * \<langle>c t *\<^sub>C t,  s\<rangle>))"
        by simp
      also have "\<dots> = (\<Sum>t\<in>set basis. (\<Sum>s\<in>set basis. c s * cnj (c t) * \<langle>t,  s\<rangle>))"
        by (metis (no_types, lifting) cinner_scaleC_left sum.cong vector_space_over_itself.scale_scale)
      also have "\<dots> = (\<Sum>t\<in>set basis. (norm (c t))^2 + (\<Sum>s\<in>(set basis)-{t}. c s * cnj (c t) * \<langle>t,  s\<rangle>))"
      proof-
        have "(\<Sum>s\<in>set basis. c s * cnj (c t) * \<langle>t,  s\<rangle>) = (norm (c t))^2 + (\<Sum>s\<in>(set basis)-{t}. c s * cnj (c t) * \<langle>t,  s\<rangle>)"
          if "t \<in> set basis" for t
        proof-         
          have "(\<Sum>s\<in>set basis. c s * cnj (c t) * \<langle>t,  s\<rangle>) =  c t * cnj (c t) * \<langle>t,  t\<rangle> + (\<Sum>s\<in>(set basis)-{t}. c s * cnj (c t) * \<langle>t,  s\<rangle>)"
            using that basis_finite
              Groups_Big.comm_monoid_add_class.sum.remove
            by (metis (no_types, lifting))
          moreover have "\<langle>t,  t\<rangle> = 1"
          proof-
            have "norm t = 1"
              using that is_normal[where x = t] unfolding basis_def is_basis_def
              by blast
            hence "(norm t)^2 = 1"
              by simp
            thus ?thesis
              by (metis of_real_1 power2_norm_eq_cinner') 
          qed
          ultimately show ?thesis
            using complex_norm_square by auto 
        qed
        thus ?thesis by simp
      qed
      also have "\<dots> = (\<Sum>t\<in>set basis. (norm (c t))^2)"
      proof-
        have "s\<in>(set basis)-{t} \<Longrightarrow> c s * cnj (c t) * \<langle>t,  s\<rangle> = 0"
          for s t
          by (metis DiffD2 basis_def c1 complex_cnj_zero_iff is_ortho_set_def is_orthonormal mult_not_zero singleton_iff)          
        hence " (\<Sum>s\<in>(set basis)-{t}. c s * cnj (c t) * \<langle>t,  s\<rangle>) = 0"
          for t
          by (simp add: \<open>\<And>t s. s \<in> set basis - {t} \<Longrightarrow> c s * cnj (c t) * \<langle>t, s\<rangle> = 0\<close>) 
        thus ?thesis by simp
      qed
      finally have "(norm x)^2 = (\<Sum>t\<in>set basis. (norm (c t))^2)"
        using of_real_eq_iff by blast        
      hence "norm x = sqrt (\<Sum>t\<in>set basis. norm (c t)^2)"
        using real_sqrt_unique by auto        
      thus ?thesis 
        unfolding K_def by simp
    qed
    finally show ?thesis by blast
  qed
  thus "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K" 
    by blast
qed



unbundle no_cblinfun_notation

end


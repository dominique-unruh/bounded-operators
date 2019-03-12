theory Complex_L2
  imports "HOL-Analysis.L2_Norm" "HOL-Library.Rewrite" "HOL-Analysis.Infinite_Set_Sum"
    Complex_Inner_Product Infinite_Set_Sum_Missing Complex_Main
    Extended_Sorry
begin

section \<open>Preliminaries\<close>

lemma polar_form:
  \<open>z \<noteq> (0::complex) \<Longrightarrow> \<exists> r::real. \<exists> u::complex.
 r > (0::real) \<and>  abs u = (1::real) \<and> (z::complex) = (complex_of_real r)*u\<close>
proof-
  assume \<open>z \<noteq> (0::complex)\<close> 
  obtain r::real where \<open>r = abs z\<close> 
    by (simp add: abs_complex_def)
  have \<open>r \<ge> 0\<close> 
    using \<open>complex_of_real r = \<bar>z\<bar>\<close> abs_nn complex_of_real_nn_iff by fastforce
  hence \<open>r > 0\<close> using  \<open>z \<noteq> (0::complex)\<close> 
    by (smt Re_complex_of_real \<open>complex_of_real r = \<bar>z\<bar>\<close> abs_complex_def norm_le_zero_iff o_apply)
  obtain u :: complex where \<open>u = z/r\<close> 
    by simp
  from \<open>u = z/r\<close>  \<open>r > 0\<close>  \<open>r = abs z\<close>
  have \<open>abs u = (1::real)\<close> 
    by auto
  show ?thesis 
    by (metis \<open>0 < r\<close> \<open>\<bar>u\<bar> = complex_of_real 1\<close> \<open>complex_of_real r = \<bar>z\<bar>\<close> \<open>u = z / complex_of_real r\<close> abs_mult divide_inverse division_ring_divide_zero nonzero_eq_divide_eq of_real_1 one_neq_zero ordered_field_class.sign_simps(5))
qed

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

definition "is_orthogonal x y = (cinner x y = 0)"

lemma orthogonal_comm: "is_orthogonal \<psi> \<phi> = is_orthogonal \<phi> \<psi>"
  unfolding is_orthogonal_def apply (subst cinner_commute) by blast

locale is_subspace =
  fixes A::"'a vector set"
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



lemma is_subspace_orthog[simp]: "is_subspace A \<Longrightarrow> is_subspace {\<psi>. (\<forall>\<phi>\<in>A. is_orthogonal \<psi> \<phi>)}"
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

lift_definition ortho :: "'a subspace \<Rightarrow> 'a subspace" is (* Orthogonal complement *)
  "\<lambda>S. {x::'a vector. \<forall>y\<in>S. is_orthogonal x y}" 
  by (fact is_subspace_orthog)

lemma subspace_as_set_scalar:
  \<open>r \<in> subspace_as_set M \<Longrightarrow> (c::complex) *\<^sub>C r \<in> subspace_as_set M\<close>
  using is_subspace.smult_closed subspace_to_set by auto

lemma subspace_as_set_opp:
  \<open>r \<in> subspace_as_set M \<Longrightarrow> - r \<in> subspace_as_set M\<close>
  using subspace_as_set_scalar 
  by (metis scaleC_minus1_left)

lemma subspace_as_set_minus:
  \<open>r \<in> subspace_as_set M \<Longrightarrow> s \<in> subspace_as_set M \<Longrightarrow> r - s \<in> subspace_as_set M\<close>
  using is_subspace.additive_closed subspace_as_set_opp subspace_to_set by fastforce

lemma polar_normPlus:
  \<open>(norm (x + y))^2 = (norm x)^2 + (norm y)^2 + 2*Re (cinner x y)\<close>
proof-
  have \<open> cinner x y + cinner y x =  cinner x y + cnj (cinner x y)\<close>
    by simp
  hence \<open> cinner x y + cinner y x = 2* Re ( cinner x y ) \<close>
    using complex_add_cnj by presburger

  have \<open>(norm (x + y))^2 = cinner (x+y) (x+y)\<close> 
    using power2_norm_eq_cinner' by auto
  hence \<open>(norm (x + y))^2 = cinner x x + cinner x y + cinner y x + cinner y y\<close>
    by (simp add: cinner_left_distrib cinner_right_distrib)
  thus ?thesis using  \<open> cinner x y + cinner y x = 2* Re ( cinner x y ) \<close>
    by (smt Re_complex_of_real cinner_norm_sq plus_complex.simps(1))  
qed

lemma polar_norm:
  \<open>(norm (x - y))^2 = (norm x)^2 + (norm y)^2 - 2*Re (cinner x y)\<close>
proof-
  have \<open>norm (x + (-y))^2 = (norm x)^2 + (norm (-y))^2 + 2*Re (cinner x (-y))\<close>
    using polar_normPlus by blast
  hence \<open>norm (x -y)^2 = (norm x)^2 + (norm y)^2 - 2*Re (cinner x y)\<close>
    by simp
  thus ?thesis 
    by blast
qed

lemma ParallelogramLaw:
  fixes x y :: \<open>'a vector\<close>
  shows  \<open>(norm (x+y))^2 + (norm (x-y))^2 = 2*((norm x)^2 + (norm y)^2)\<close>
  by (simp add: polar_norm polar_normPlus)

lemma LimSumConst:
  fixes r::\<open>nat \<Rightarrow> 'a vector\<close> and h R::\<open>'a vector\<close>
  assumes \<open>r \<longlonglongrightarrow> R\<close>
  shows \<open> (\<lambda> n::nat. (r n) + h)  \<longlonglongrightarrow> R + h \<close>
proof-
  from \<open>r \<longlonglongrightarrow> R\<close> 
  have \<open>\<forall> \<epsilon> > 0. \<exists> N. \<forall> n. n \<ge> N \<longrightarrow> norm ( (r n) - R ) < \<epsilon>\<close>
    by (simp add: LIMSEQ_iff)
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N. \<forall> n. n \<ge> N \<longrightarrow> norm ( ((r n)+h) - (R+h) ) < \<epsilon>\<close>
    by simp
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N. \<forall> n. n \<ge> N \<longrightarrow> norm ( (\<lambda> m. (r m)+h) n - (R+h) ) < \<epsilon>\<close>
    by simp
  thus ?thesis using  LIMSEQ_iff by fastforce
qed

lemma OneOverNConvZ: \<open>( \<lambda> n::nat.   1/(n+1) ) \<longlonglongrightarrow> (0::real)\<close>
proof-
  have \<open>( \<lambda> n::nat.   1/n ) \<longlonglongrightarrow> (0::real)\<close>
    by (simp add: lim_inverse_n')
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n::nat. n \<ge> N \<longrightarrow> norm ( 1/n ) < \<epsilon>\<close> 
    by (simp add: LIMSEQ_iff)
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n::nat. n+1 \<ge> N \<longrightarrow> norm ( 1/(n+1) ) < \<epsilon>\<close> 
    using Suc_eq_plus1 by blast
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n::nat. n+1 \<ge> N+1 \<longrightarrow> norm ( 1/(n+1) ) < \<epsilon>\<close> 
    by (metis (mono_tags, hide_lams) Suc_eq_plus1 Suc_le_mono inverse_eq_divide le_less_trans less_add_one less_le real_norm_def)
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n::nat. n \<ge> N \<longrightarrow> norm ( 1/(n+1) ) < \<epsilon>\<close> 
    by simp
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> n::nat. n \<ge> N \<longrightarrow> dist (1/ (real (n+1))) (0::real) < \<epsilon>\<close> 
    by (simp add: add.commute)
  hence \<open>( \<lambda> n::nat.   1/(n+1) ) \<longlonglongrightarrow> (0::real)\<close> 
    by (simp add: lim_sequentially)
  thus ?thesis by blast
qed

(* There exists a unique point k in M such that the distance between h and M reaches
 its minimum at k *)


definition convex:: \<open>'a vector set \<Rightarrow> bool\<close> where
  \<open>convex \<equiv> \<lambda> S. \<forall> x::'a vector. \<forall> y::'a vector. \<forall> t::real.
(x \<in> S \<and> y \<in> S \<and> 0 < t \<and> t < 1) \<longrightarrow> t *\<^sub>C x + (1 - t) *\<^sub>C y \<in> S\<close>


lemma OneOverNConvZ_left_add: \<open>(\<lambda> n::nat. dd + (1/(n+1))) \<longlonglongrightarrow> (dd::real)\<close>
  by (metis OneOverNConvZ add.right_neutral tendsto_add_const_iff)

lemma MonotLim:
  fixes r s :: \<open>nat \<Rightarrow> real\<close>
  assumes  \<open>\<forall> n::nat. r n \<le> s n\<close> and \<open>r \<longlonglongrightarrow> (R::real)\<close> and  \<open>s \<longlonglongrightarrow> (S::real)\<close>
  shows \<open>R \<le> S\<close>
  using assms(1) assms(2) assms(3) lim_mono by blast

lemma DistMinExistsConvexZ:
  \<open>convex S \<Longrightarrow> closed S \<Longrightarrow> S \<noteq> {}  \<Longrightarrow> \<exists> k. (\<forall> t. t \<in> S \<longrightarrow> norm k \<le> norm t) \<and> k \<in> S\<close>
proof-
  assume \<open>S \<noteq> {}\<close>
  have \<open>{(norm t)^2| t. t \<in> S} \<noteq> {}\<close>
    by (simp add: \<open>S \<noteq> {}\<close>)
  have \<open>\<forall> t. (norm t)^2 \<ge> 0\<close>
    by simp
  hence \<open>bdd_below {(norm t)^2| t. t \<in> S}\<close>
    by (smt bdd_belowI  mem_Collect_eq)
  obtain dd::real where \<open>dd = Inf {(norm t)^2| t. t \<in> S}\<close>
    by auto 
  have \<open>dd \<ge> 0\<close>
    using  \<open>\<forall> t. (norm t)^2 \<ge> 0\<close>  \<open>dd = Inf {(norm t)^2| t. t \<in> S}\<close>  \<open>{(norm t)^2| t. t \<in> S} \<noteq> {}\<close>
    by (smt cInf_greatest mem_Collect_eq norm_ge_zero vector_choose_size zero_le_power2)
  then obtain d :: real where \<open>d^2 = dd\<close> and \<open>d \<ge> (0::real)\<close> 
    using real_sqrt_pow2 
    by (metis Inner_Product.norm_eq_square norm_imp_pos_and_ge  real_norm_def real_sqrt_abs real_sqrt_power real_sqrt_unique)
  have \<open>\<forall> \<epsilon> > 0. \<exists> v \<in> {(norm t)^2| t. t \<in> S}. v < dd + \<epsilon>\<close>
    using  \<open>dd = Inf {(norm t)^2| t. t \<in> S}\<close>  \<open>{(norm t)^2 |t. t \<in> S} \<noteq> {}\<close>  
    by (meson cInf_lessD less_add_same_cancel1)
  hence \<open>\<forall> \<epsilon> > 0. \<exists> t \<in> S. (norm t)^2 < dd + \<epsilon>\<close>
    by auto
  then obtain f::\<open>real \<Rightarrow> 'a vector\<close> where \<open>\<forall> \<epsilon> > 0. (f \<epsilon>) \<in> S \<and> (norm (f \<epsilon>))^2 < dd + \<epsilon>\<close>
    by metis
  obtain r::\<open>nat \<Rightarrow> 'a vector\<close> where \<open>r \<equiv> \<lambda> n::nat. f (1/(n+1))\<close>
    by blast
  have \<open>\<forall> n::nat. r n = f (1/(n+1)) \<close> 
    by (metis \<open>r \<equiv> \<lambda>x. f (1 / (real x + 1))\<close> of_nat_1 of_nat_add)
  hence  \<open>\<forall> n::nat. r n \<in> S \<and> (norm (r n))^2 < dd + (1/(n+1))\<close>
    by (simp add: \<open>\<forall>\<epsilon>>0. f \<epsilon> \<in> S \<and> (norm (f \<epsilon>))\<^sup>2 < dd + \<epsilon>\<close> zero_less_Fract_iff)
  hence \<open>\<forall> n. r n \<in> S\<close> 
    by simp
  have \<open>\<forall> n. (norm (r n))^2 < dd + (1/(n+1))\<close>
    using  \<open>\<forall> n::nat. r n \<in> S \<and> (norm (r n))^2 < dd + (1/(n+1))\<close>
    by (simp add: add.commute)
  have \<open>\<forall> m n. (norm ((1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m)))^2 + (norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2 
    = 2*((norm ((1/2)*\<^sub>C(r n)))^2 + (norm ((1/2)*\<^sub>C(r m)))^2)\<close>
    by (simp add: ParallelogramLaw)
  hence \<open>\<forall> m n. ((norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2 + (norm ((1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m)))^2)
 - (norm ((1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m)))^2 
    = 2*((norm ((1/2)*\<^sub>C(r n)))^2 + (norm ((1/2)*\<^sub>C(r m)))^2) - (norm ((1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m)))^2\<close>
    by smt
  hence \<open>\<forall> m n. (norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2
    = 2*((norm ((1/2)*\<^sub>C(r n)))^2 + (norm ((1/2)*\<^sub>C(r m)))^2) - (norm ((1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m)))^2\<close>
    by auto
  hence \<open>\<forall> m n. (norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2
    = 2*(((1/2)*(norm (r n)))^2 + ((1/2)*(norm (r m)))^2) - (norm ((1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m)))^2\<close>
    by simp
  hence \<open>\<forall> m n. (norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2
    = 2*((1/4)*((norm (r n)))^2 + (1/4)*((norm (r m)))^2) - (norm ((1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m)))^2\<close>
    by (simp add: power_divide)
  hence \<open>\<forall> m n. (norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2
    = ((1/2)*((norm (r n)))^2 + (1/2)*((norm (r m)))^2) - (norm ((1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m)))^2\<close>
    by simp
  have \<open>(0::real) < (1/2)\<close> by simp 
  have \<open>(1/2) < (1::real)\<close> by simp 
  have \<open>\<forall> p \<in> {(norm t)^2| t. t \<in> S}. p \<ge> dd\<close>
    using  \<open>bdd_below {(norm t)^2| t. t \<in> S}\<close>  \<open>dd = Inf {(norm t)^2| t. t \<in> S}\<close>
    by (simp add: cInf_lower)
  hence \<open>\<forall> t \<in> S. (norm t)^2 \<ge> dd\<close> 
    by blast
  have \<open>\<forall> n::nat. dd \<le> (norm (r n))^2\<close>  
    by (simp add: \<open>\<forall>n. r n \<in> S\<close> \<open>\<forall>t\<in>S. dd \<le> (norm t)\<^sup>2\<close>)
  assume \<open>convex S\<close>
  hence \<open>\<forall> m n. \<forall> t::real. 0 < t \<and> t < 1 \<longrightarrow>  t*\<^sub>C(r n) + (1 - t)*\<^sub>C(r m) \<in> S\<close>
    by (simp add: Complex_L2.convex_def \<open>\<forall>n. r n \<in> S\<close>)
  hence \<open>\<forall> m n. (1/2)*\<^sub>C(r n) + (1 - (1/2))*\<^sub>C(r m) \<in> S\<close>
    using \<open>(0::real) < (1/2)\<close> \<open>(1/2) < (1::real)\<close> 
    by (smt add_diff_cancel_right' complex_of_real_pos_iff diff_numeral_special(9) nice_ordered_field_class.gt_half_sum of_real_1 of_real_add of_real_divide one_add_one ordered_field_class.sign_simps(34))
  hence \<open>\<forall> m n. ( norm ( (1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m) ) )^2 \<ge> dd\<close>
    using  \<open>\<forall> t \<in> S. (norm t)^2 \<ge> dd\<close> by auto      
  hence \<open>\<forall> m n. (norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2
    \<le> ((1/2)*((norm (r n)))^2 + (1/2)*((norm (r m)))^2) - dd\<close>
    using  \<open>\<forall> m n. (norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2
    = ((1/2)*((norm (r n)))^2 + (1/2)*((norm (r m)))^2) - (norm ((1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m)))^2\<close>
    by simp
  hence \<open>\<forall> m n. ((1/2)*((norm (r n)))^2 + (1/2)*((norm (r m)))^2) - (norm ((1/2)*\<^sub>C(r n) + (1/2)*\<^sub>C(r m)))^2
    < ((1/2)*( dd + (1/(n+1)) ) + (1/2)*( dd + (1/(m+1)) )) - dd\<close>
    using \<open>\<forall> n. (norm (r n))^2 < dd + (1/(n+1))\<close> 
    by (smt \<open>0 < 1 / 2\<close> \<open>\<forall>m n. dd \<le> (norm (timesScalarVec (1 / 2) (r n) + timesScalarVec (1 / 2) (r m)))\<^sup>2\<close> real_mult_le_cancel_iff2)
  hence \<open>\<forall> m n. (norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2
    < ((1/2)*( dd + (1/(n+1)) ) + (1/2)*( dd + (1/(m+1))))  - dd\<close>
    by (simp add: \<open>\<forall>m n. (norm (timesScalarVec (1 / 2) (r n) - timesScalarVec (1 / 2) (r m)))\<^sup>2 = 1 / 2 * (norm (r n))\<^sup>2 + 1 / 2 * (norm (r m))\<^sup>2 - (norm (timesScalarVec (1 / 2) (r n) + timesScalarVec (1 / 2) (r m)))\<^sup>2\<close>)
  hence \<open>\<forall> m n. (norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2
    < (1/2)* dd + (1/2)*(1/(n+1))  + (1/2)* dd + (1/2)*(1/(m+1)) - dd\<close>
    by (simp add: distrib_left)
  hence \<open>\<forall> m n. (norm ( (1/2)*\<^sub>C(r n) - (1/2)*\<^sub>C(r m) ) )^2
    <  (1/2)*(1/(n+1)) + (1/2)*(1/(m+1))\<close> 
    by simp
  hence \<open>\<forall> m n. (norm ( (1/2)*\<^sub>C( (r n) - (r m) ) ) )^2
    <  (1/2)*(1/(n+1)) + (1/2)*(1/(m+1))\<close> 
    by (simp add: complex_vector.scale_right_diff_distrib)  
  hence \<open>\<forall> m n. (1/4)*((norm ( (r n) - (r m) ) ))^2
    <  (1/2)*(1/(n+1)) + (1/2)*(1/(m+1))\<close> 
    by (simp add: power_divide)
  hence \<open>\<forall> m n. ((norm ( (r n) - (r m) ) ))^2  < 4*( (1/2)*(1/(n+1)) + (1/2)*(1/(m+1)) )\<close> 
    by simp
  hence \<open>\<forall> m n. ((norm ( (r n) - (r m) ) ))^2  < 4*( (1/2)*(1/(n+1)) ) + 4*( (1/2)*(1/(m+1)) )\<close> 
    by simp
  hence \<open>\<forall> m n. ((norm ( (r n) - (r m) ) ))^2  < (4*(1/2) )*(1/(n+1))  + (4* (1/2))*(1/(m+1)) \<close> 
    by (metis (mono_tags, hide_lams) Groups.add_ac(2) Groups.mult_ac(1) \<open>\<forall>m n. (norm (r n - r m))\<^sup>2 < 4 * (1 / 2 * (1 / (real n + 1)) + 1 / 2 * (1 / (real m + 1)))\<close> distrib_left norm_minus_commute)
  hence \<open>\<forall> m n. ((norm ( (r n) - (r m) ) ))^2  < 2*(1/(n+1))  + 2*(1/(m+1)) \<close> 
    by simp
  hence \<open>\<forall> N. \<forall> m n. m+1 \<ge> N+1 \<and> n+1 \<ge> N+1 \<longrightarrow>((norm ( (r n) - (r m) ) ))^2 < 2*(1/(n+1))  + 2*(1/(m+1)) \<close> 
    by blast
  hence \<open>\<forall> N::nat. \<forall> m n. m+1 \<ge> N+1 \<and> n+1 \<ge> N+1 \<longrightarrow>((norm ( (r n) - (r m) ) ))^2 < 2*(1/(N+1))  + 2*(1/(N+1)) \<close> 
    using Suc_eq_plus1 inverse_of_nat_le nat.simps(3) of_nat_1 of_nat_add
    by smt
  hence \<open>\<forall> N::nat. \<forall> m n. m \<ge> N \<and> n \<ge> N \<longrightarrow>((norm ( (r n) - (r m) ) ))^2 < 2*(1/(N+1))  + 2*(1/(N+1)) \<close> 
    by simp
  hence \<open>\<forall> N::nat. \<forall> m n. m \<ge> N \<and> n \<ge> N \<longrightarrow>((norm ( (r n) - (r m) ) ))^2 < 4/(N+1)\<close> 
    by simp
  have \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. 1/(N+1) < \<epsilon>/4\<close>
    by (metis Suc_eq_plus1 nat_approx_posE  zero_less_divide_iff zero_less_numeral)
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. 4*( 1/(N+1) ) < \<epsilon>\<close>
    by (metis Suc_eq_plus1 less_divide_eq_numeral1(1) mult.commute)
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. 4/(N+1)  < \<epsilon>\<close>
    by simp
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. 4/(N+1)  < \<epsilon> \<and> ( \<forall> m n. m \<ge> N \<and> n \<ge> N \<longrightarrow>((norm ( (r n) - (r m) ) ))^2 < 4/(N+1) )\<close> 
    using  \<open>\<forall> N::nat. \<forall> m n. m \<ge> N \<and> n \<ge> N \<longrightarrow>((norm ( (r n) - (r m) ) ))^2 < 4/(N+1)\<close>
    by meson
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat.  \<forall> m n. m \<ge> N \<and> n \<ge> N \<longrightarrow>((norm ( (r n) - (r m) ) ))^2  < \<epsilon>\<close> 
    by fastforce
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat.  \<forall> m n. m \<ge> N \<and> n \<ge> N \<longrightarrow>((norm ( (r n) - (r m) ) ))^2  < \<epsilon>^2\<close> 
    by simp
  have \<open> \<forall> m n. norm ( (r n) - (r m) ) \<ge> 0\<close>
    by simp
  hence \<open>\<forall> \<epsilon> > 0. \<exists> N::nat.  \<forall> m n. m \<ge> N \<and> n \<ge> N \<longrightarrow>(norm ( (r n) - (r m) ) )  < \<epsilon>\<close> 
    using  \<open>\<forall> \<epsilon> > 0. \<exists> N::nat.  \<forall> m n. m \<ge> N \<and> n \<ge> N \<longrightarrow>((norm ( (r n) - (r m) ) ))^2  < \<epsilon>^2\<close> 
    by (meson less_le power2_less_imp_less)
  hence \<open>Cauchy r\<close> 
    by (metis Cauchy_def dist_norm)
  hence \<open>convergent r\<close> 
    using Cauchy_convergent_iff by auto
  assume \<open>closed S\<close>
  hence \<open>lim r \<in> S\<close> using \<open>convergent r\<close> 
    using \<open>\<forall>n. r n \<in> S\<close> closed_sequentially convergent_LIMSEQ_iff by blast
  have \<open>\<forall> t \<in> S. d^2 \<le> (norm t)^2 \<close>
    by (simp add: \<open>\<forall>t\<in>S. dd \<le> (norm t)\<^sup>2\<close> \<open>d\<^sup>2 = dd\<close>)
  hence \<open>\<forall> t \<in> S. d \<le> (norm t)\<close>
    using norm_ge_zero power2_le_imp_le by blast    
  obtain k::\<open>'a vector\<close> where  \<open>r \<longlonglongrightarrow> k\<close>
    using \<open>convergent r\<close> convergentD by auto
  have \<open>(\<lambda> n. (norm (r n))) \<longlonglongrightarrow> norm k\<close>
    by (simp add: \<open>r \<longlonglongrightarrow> k\<close> tendsto_norm)
  hence \<open>(\<lambda> n. (norm (r n))^2) \<longlonglongrightarrow> (norm k)^2\<close>
    by (simp add: tendsto_power)
  have \<open>dd \<le> (norm k)^2\<close> 
    using \<open>\<forall>t\<in>S. dd \<le> (norm t)\<^sup>2\<close> \<open>lim r \<in> S\<close> \<open>r \<longlonglongrightarrow> k\<close> limI by auto
  have \<open>(\<lambda> n::nat. dd + (1/(real (n+1)))) \<longlonglongrightarrow> (dd::real)\<close>
    using OneOverNConvZ_left_add by blast
  from \<open>\<forall> n. (norm (r n))^2 < dd + (1/(n+1))\<close>
  have \<open>\<forall> n. (norm (r n))^2 \<le> dd + (1/(n+1))\<close>
    by smt
  hence  \<open>\<forall> n. (norm (r n))^2 \<le> dd + (1/(real (n+1)))\<close> 
    by (metis Groups.add_ac(2) Suc_eq_plus1 \<open>\<forall>n. (norm (r n))\<^sup>2 < dd + 1 / (real n + 1)\<close> less_eq_real_def linorder_not_le semiring_1_class.of_nat_simps(2))
  have \<open>(norm k)^2 \<le> dd\<close> 
    using  \<open>\<forall> n. (norm (r n))^2 \<le> dd + (1/(real (n+1)))\<close>
      \<open>(\<lambda> n::nat. dd + (1/(real (n+1)))) \<longlonglongrightarrow> (dd::real)\<close> \<open>(\<lambda> n. (norm (r n))^2) \<longlonglongrightarrow> (norm k)^2\<close>
    by (simp add: MonotLim)
  have  \<open>(norm k)^2 = dd\<close> 
    using \<open>(norm k)\<^sup>2 \<le> dd\<close> \<open>dd \<le> (norm k)\<^sup>2\<close> by linarith  
  hence  \<open>(norm k)^2 = d^2\<close> 
    by (simp add: \<open>d\<^sup>2 = dd\<close>)
  hence  \<open>norm k = d\<close> 
    using \<open>0 \<le> d\<close> by auto
  have \<open>\<forall> t\<in>S. norm k \<le> norm t\<close>
    by (simp add: \<open>\<forall>t\<in>S. d \<le> norm t\<close> \<open>norm k = d\<close>)
  thus ?thesis 
    using \<open>lim r \<in> S\<close> \<open>r \<longlonglongrightarrow> k\<close> limI by blast
qed

lemma TransConvex:
  \<open>convex S \<Longrightarrow> convex {s + h| s. s \<in> S}\<close>
proof-
  assume \<open>convex S\<close>
  hence \<open>\<forall> x::'a vector. \<forall> y::'a vector. \<forall> t::real.
  (x \<in> S \<and> y \<in> S \<and> 0 < t \<and> t < 1) \<longrightarrow> t *\<^sub>C x + (1 - t) *\<^sub>C y \<in> S\<close> 
    by (simp add: Complex_L2.convex_def)
  hence \<open>\<forall> x::'a vector. \<forall> y::'a vector. \<forall> t::real.
  (x \<in> S \<and> y \<in> S \<and> 0 < t \<and> t < 1) \<longrightarrow> (t *\<^sub>C x + (1 - t) *\<^sub>C y) + h \<in> {s + h| s. s \<in> S}\<close> 
    by blast
  hence \<open>\<forall> x::'a vector. \<forall> y::'a vector. \<forall> t::real.
  (x \<in> S \<and> y \<in> S \<and> 0 < t \<and> t < 1) \<longrightarrow> (t *\<^sub>C x + (1 - t) *\<^sub>C y) + (t *\<^sub>C h + (1 - t) *\<^sub>C h) \<in> {s + h| s. s \<in> S}\<close> 
    by (metis (no_types, lifting) add.commute scaleC_collapse)
  hence \<open>\<forall> x::'a vector. \<forall> y::'a vector. \<forall> t::real.
  (x \<in> S \<and> y \<in> S \<and> 0 < t \<and> t < 1) \<longrightarrow> t *\<^sub>C x + ( (1 - t) *\<^sub>C y + t *\<^sub>C h ) + (1 - t) *\<^sub>C h \<in> {s + h| s. s \<in> S}\<close> 
    by (simp add: add.assoc)
  hence \<open>\<forall> x::'a vector. \<forall> y::'a vector. \<forall> t::real.
  (x \<in> S \<and> y \<in> S \<and> 0 < t \<and> t < 1) \<longrightarrow> t *\<^sub>C x + ( t *\<^sub>C h + (1 - t) *\<^sub>C y ) + (1 - t) *\<^sub>C h \<in> {s + h| s. s \<in> S}\<close> 
    by (simp add: add.commute)
  hence \<open>\<forall> x::'a vector. \<forall> y::'a vector. \<forall> t::real.
  (x \<in> S \<and> y \<in> S \<and> 0 < t \<and> t < 1) \<longrightarrow> (t *\<^sub>C x +  t *\<^sub>C h) + ((1 - t) *\<^sub>C y  + (1 - t) *\<^sub>C h) \<in> {s + h| s. s \<in> S}\<close> 
    by (simp add: add.assoc)
  hence \<open>\<forall> x::'a vector. \<forall> y::'a vector. \<forall> t::real.
  (x \<in> S \<and> y \<in> S \<and> 0 < t \<and> t < 1) \<longrightarrow> t *\<^sub>C (x +  h) + (1 - t) *\<^sub>C (y  + h) \<in> {s + h| s. s \<in> S}\<close> 
    by (simp add: scaleC_add_right)
  hence \<open>\<forall> x::'a vector. \<forall> y::'a vector. \<forall> t::real.
  (x + h \<in> {s + h| s. s \<in> S} \<and> y \<in> S \<and> 0 < t \<and> t < 1) \<longrightarrow> t *\<^sub>C (x +  h) + (1 - t) *\<^sub>C (y  + h) \<in> {s + h| s. s \<in> S}\<close> 
    by simp
  hence \<open>\<forall> x::'a vector. \<forall> y::'a vector. \<forall> t::real.
  (x + h \<in> {s + h| s. s \<in> S} \<and> y + h \<in> {s + h| s. s \<in> S}  \<and> 0 < t \<and> t < 1) \<longrightarrow> t *\<^sub>C (x +  h) + (1 - t) *\<^sub>C (y  + h) \<in> {s + h| s. s \<in> S}\<close> 
    by simp
  hence \<open>\<forall> u::'a vector. \<forall> v::'a vector. \<forall> t::real.
  (u \<in> {s + h| s. s \<in> S} \<and> v \<in> {s + h| s. s \<in> S}  \<and> 0 < t \<and> t < 1) \<longrightarrow> t *\<^sub>C u + (1 - t) *\<^sub>C v \<in> {s + h| s. s \<in> S}\<close> 
    by blast
  thus ?thesis 
    by (simp add: Complex_L2.convex_def)
qed


lemma preTransClosed:
\<open> \<forall>r. convergent (\<lambda>n. r n + (h::'a vector)) \<and> (\<forall>n. r n \<in> S) \<longrightarrow> (\<exists>s. lim (\<lambda>n. r n + h) = s + h \<and> s \<in> S) \<Longrightarrow>
         convergent t \<Longrightarrow> \<forall>n. \<exists>s. t n = s + h \<and> s \<in> S \<Longrightarrow> \<exists>s. lim t = s + h \<and> s \<in> S \<close>
proof-
  assume \<open> \<forall>r. convergent (\<lambda>n. r n + h) \<and> (\<forall>n. r n \<in> S) \<longrightarrow> (\<exists>s. lim (\<lambda>n. r n + h) = s + h \<and> s \<in> S) \<close>
  assume \<open>convergent t\<close>
  assume \<open>\<forall>n. \<exists>s. t n = s + h \<and> s \<in> S\<close>
  obtain r::\<open>nat \<Rightarrow> 'a vector\<close> where \<open>\<forall>n. t n = (r n) + h \<and> r n \<in> S\<close> using  \<open>\<forall>n. \<exists>s. t n = s + h \<and> s \<in> S\<close>
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

lemma TransClosed:
  \<open>closed (S::('a vector) set) \<Longrightarrow> closed {s + h| s. s \<in> S}\<close>
proof-
  assume \<open>closed S\<close>
  hence \<open>\<forall> r::nat \<Rightarrow> 'a vector. convergent r \<and> (\<forall> n::nat. r n \<in> S) \<longrightarrow> lim r \<in> S\<close>
    using closed_sequentially convergent_LIMSEQ_iff by blast
  hence \<open>\<forall> r::nat \<Rightarrow> 'a vector. convergent r \<and> (\<forall> n::nat. r n \<in>  {s | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n)) \<in>  {s | s. s \<in> S}\<close>
    by simp
  hence \<open>\<forall> r::nat \<Rightarrow> 'a vector. convergent r \<and> (\<forall> n::nat. (r n) \<in>  {s | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+h \<in>  {s+h | s. s \<in> S}\<close>
    by blast
  hence \<open>\<forall> r::nat \<Rightarrow> 'a vector. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+h \<in>  {s+h | s. s \<in> S}\<close>
    by simp
  hence \<open>\<forall> r::nat \<Rightarrow> 'a vector. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+lim (\<lambda> n. h) \<in>  {s+h | s. s \<in> S}\<close>
    by auto
  have \<open>\<forall> r::nat \<Rightarrow> 'a vector. convergent r \<longrightarrow>  (lim r) + h = lim (\<lambda> n. (r n)+h)\<close>
  proof -
    have "\<forall>f v. \<not> f \<longlonglongrightarrow> (v::'a vector) \<or> (THE v. f \<longlonglongrightarrow> v) = v"
      by (metis limI lim_def)
    then show ?thesis
      by (metis LimSumConst convergent_def lim_def)
  qed
  hence \<open>\<forall> r::nat \<Rightarrow> 'a vector. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n)+h) \<in>  {s+h | s. s \<in> S}\<close>
    using  \<open>\<forall> r::nat \<Rightarrow> 'a vector. convergent r \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n))+lim (\<lambda> n. h) \<in> {s+h | s. s \<in> S}\<close>
     add_diff_cancel_left' by auto
  hence \<open>\<forall> r::nat \<Rightarrow> 'a vector. convergent (\<lambda> n. (r n)+h) \<and> (\<forall> n::nat. (r n)+h \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. (r n)+h) \<in> {s+h | s. s \<in> S}\<close>
    using convergent_add_const_right_iff by blast
  hence \<open>\<forall> t::nat \<Rightarrow> 'a vector. convergent (\<lambda> n. t n) \<and> (\<forall> n::nat. t n \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim (\<lambda> n. t n) \<in> {s+h | s. s \<in> S}\<close>
    using preTransClosed by auto
  hence \<open>\<forall> t::nat \<Rightarrow> 'a vector. convergent t \<and> (\<forall> n::nat. t n \<in>  {s+h | s. s \<in> S}) \<longrightarrow> lim t \<in> {s+h | s. s \<in> S}\<close>
    by simp
  thus ?thesis using  convergent_LIMSEQ_iff 
    by (metis (no_types, lifting) closed_sequential_limits limI)
qed
                                        
lemma TransNonEmpty:
  \<open>(S::('a vector) set) \<noteq> {} \<Longrightarrow> {s + h| s. s \<in> S} \<noteq> {}\<close>
  by simp

lemma DistMinExistsConvex:
  \<open>convex S \<Longrightarrow> closed S \<Longrightarrow> S \<noteq> {}  \<Longrightarrow> \<exists> k. (\<forall> t. t \<in> S \<longrightarrow> dist h k \<le> dist h t) \<and> k \<in> S\<close>
proof-
  assume \<open>convex S\<close>
  hence \<open>\<forall> h. convex {s + h| s. s \<in> S}\<close> using TransConvex by auto
  hence \<open>convex {s + (-h)| s. s \<in> S}\<close> by blast
  assume \<open>closed S\<close>
  hence \<open>\<forall> h. closed {s + h| s. s \<in> S}\<close> using TransClosed by auto
  hence \<open>closed {s + (-h)| s. s \<in> S}\<close> by blast
  assume \<open>S \<noteq> {}\<close>
  hence \<open>\<forall> h. {s + h| s. s \<in> S} \<noteq> {}\<close> using TransNonEmpty by auto
  hence \<open>{s + (-h)| s. s \<in> S} \<noteq> {}\<close> by blast
  have \<open>\<exists> k. (\<forall> t. t \<in> {s + (-h)| s. s \<in> S} \<longrightarrow> norm k \<le> norm t) \<and> k \<in> {s + (-h)| s. s \<in> S}\<close>
    using DistMinExistsConvexZ \<open>Complex_L2.convex {s + - h |s. s \<in> S}\<close> \<open>closed {s + - h |s. s \<in> S}\<close> \<open>{s + - h |s. s \<in> S} \<noteq> {}\<close> by blast
  have \<open>\<forall> t. t \<in> {s + (-h)| s. s \<in> S} \<longleftrightarrow> t + h \<in> {s | s. s \<in> S}\<close>
    by force
  hence  \<open>\<exists> k. (\<forall> t. t + h \<in> {s| s. s \<in> S} \<longrightarrow> norm k \<le> norm t) \<and> k \<in> {s + (-h)| s. s \<in> S}\<close>
    using  \<open>\<exists> k. (\<forall> t. t \<in> {s + (-h)| s. s \<in> S} \<longrightarrow> norm k \<le> norm t) \<and> k \<in> {s + (-h)| s. s \<in> S}\<close>
    by auto
  hence  \<open>\<exists> k. (\<forall> t. t + h \<in> {s| s. s \<in> S} \<longrightarrow> norm k \<le> norm t) \<and> k + h \<in> {s| s. s \<in> S}\<close>
    using  \<open>\<forall> t. t \<in> {s + (-h)| s. s \<in> S} \<longleftrightarrow> t + h \<in> {s | s. s \<in> S}\<close>
    by auto
  hence  \<open>\<exists> k. (\<forall> t. t + h \<in> S \<longrightarrow> norm k \<le> norm t) \<and> k + h \<in> {s| s. s \<in> S}\<close>
    by auto
  hence  \<open>\<exists> k. (\<forall> t. t + h \<in> S \<longrightarrow> norm k \<le> norm t) \<and> k + h \<in> S\<close>
    by auto
  hence  \<open>\<exists> kk. (\<forall> t. t + h \<in> S \<longrightarrow> norm (kk - h) \<le> norm t) \<and> (kk - h) + h \<in> S\<close>
    by (metis add_diff_cancel diff_add_cancel)
  hence  \<open>\<exists> kk. (\<forall> t. t + h \<in> S \<longrightarrow> norm (kk - h) \<le> norm t) \<and> kk \<in> S\<close>
    by simp
  hence  \<open>\<exists> kk. (\<forall> tt. (tt - h) + h \<in> S \<longrightarrow> norm (kk - h) \<le> norm (tt - h)) \<and> kk \<in> S\<close>
    by metis
  hence  \<open>\<exists> kk. (\<forall> tt. tt \<in> S \<longrightarrow> norm (kk - h) \<le> norm (tt - h)) \<and> kk \<in> S\<close>
    by simp
  hence  \<open>\<exists> kk. (\<forall> tt. tt \<in> S \<longrightarrow> dist kk h \<le> dist tt h) \<and> kk \<in> S\<close>
    using Real_Vector_Spaces.dist_norm_class.dist_norm by metis
  hence  \<open>\<exists> kk. (\<forall> tt. tt \<in> S \<longrightarrow> dist h kk \<le> dist h tt) \<and> kk \<in> S\<close>
    using Real_Vector_Spaces.metric_space_class.dist_commute 
    by metis
  thus ?thesis by blast
qed

lemma SubspaceConvex:
  \<open>convex (subspace_as_set M)\<close>
  by (metis Complex_L2.convex_def is_subspace.additive_closed mem_Collect_eq subspace_as_set_scalar subspace_to_set)

lemma DistMinExists:
  \<open>\<forall> h. \<exists> k. (\<forall> t. t \<in> subspace_as_set M \<longrightarrow> dist h k \<le> dist h t) 
 \<and> k \<in> subspace_as_set M\<close>
proof-
  have \<open>convex (subspace_as_set M)\<close> 
    by (simp add: SubspaceConvex)
  have \<open>closed (subspace_as_set M)\<close> 
    using is_subspace.closed subspace_to_set by auto
  have \<open>subspace_as_set M \<noteq> {}\<close> 
    using is_subspace_contains_0 subspace_to_set by auto
  from  \<open>convex (subspace_as_set M)\<close> \<open>closed (subspace_as_set M)\<close> \<open>subspace_as_set M \<noteq> {}\<close>
  show ?thesis using DistMinExistsConvex by metis
qed

(* Definition of projection using distance *)
definition DProjDefProp:: \<open>('a subspace \<Rightarrow> ('a vector \<Rightarrow> 'a vector)) \<Rightarrow> bool\<close> where
  \<open> DProjDefProp \<equiv>
 \<lambda> P. \<forall> M. \<forall> h.  (\<forall> t. t \<in> subspace_as_set M \<longrightarrow> dist h ((P M) h) \<le> dist h t) 
 \<and> (P M) h \<in> subspace_as_set M\<close>

(* Existence of projection onto a subspace defined via distance *)
lemma DProjDefPropE: 
  \<open>\<exists> P. DProjDefProp P\<close>
  using DProjDefProp_def DistMinExists 
  by metis

definition dproj :: \<open>'a subspace \<Rightarrow> ('a vector \<Rightarrow> 'a vector)\<close> where
  \<open>dproj \<equiv> SOME P. DProjDefProp P\<close>

lemma DProjDefPropE_explicit: 
  \<open>DProjDefProp (dproj)\<close>
  unfolding dproj_def
  by (simp add: DProjDefPropE someI_ex)

lemma dproj_ex1:
  \<open>(dproj M) h \<in> subspace_as_set M\<close>
  using DProjDefPropE_explicit 
  by (metis DProjDefProp_def)

lemma dproj_ex2:
  \<open> t \<in> subspace_as_set M \<Longrightarrow> dist h ((dproj M) h) \<le> dist h t\<close>
  using DProjDefPropE_explicit 
  by (metis DProjDefProp_def)

lemma predProjExistsA:
  \<open>f \<in> subspace_as_set M \<Longrightarrow> 2 * Re ( cinner f ( h - ((dproj M) h) ) ) \<le> (norm f)^2\<close>
  for M :: \<open>'a subspace\<close>
proof-
  assume \<open>f \<in> subspace_as_set M\<close>
  have \<open>(dproj M) h \<in> subspace_as_set M\<close>
    by (simp add: dproj_ex1)
  hence \<open>(f + (dproj M) h) \<in> subspace_as_set M\<close> using \<open>f \<in> subspace_as_set M\<close> 
    using is_subspace.additive_closed subspace_to_set by auto
  hence \<open>dist h ((dproj M) h) \<le> dist h (f + (dproj M) h)\<close>
    by (simp add: dproj_ex2)
  hence \<open>norm (h - ((dproj M) h)) \<le> norm ( h - (f + (dproj M) h) )\<close>
    by (simp add: dist_vector_def)
  hence \<open>norm (h - ((dproj M) h))^2 \<le> norm ( h - (f + (dproj M) h) )^2\<close>
    using norm_ge_zero power_mono by blast
  hence \<open>norm (h - ((dproj M) h))^2 \<le> norm ( (h - (dproj M) h) - f )^2\<close>
    by (simp add: diff_add_eq_diff_diff_swap)
  hence \<open>norm (h - ((dproj M) h))^2 \<le> 
    ( norm (h - ((dproj M) h)) )^2 + (norm f)^2 - 2*Re (cinner (h - (dproj M) h) f)\<close>
    by (simp add: polar_norm)
  hence \<open>0 \<le> (norm f)^2 - 2*Re (cinner (h - (dproj M) h) f)\<close>  by linarith
  hence \<open>2*Re (cinner (h - (dproj M) h) f) \<le> (norm f)^2\<close>  by simp
  thus ?thesis  
    by (smt norm_minus_commute polar_norm)
qed


lemma NormScalar:
  \<open>norm (k *\<^sub>C f) = (abs k) *(norm f)\<close>
  by (metis norm_scaleR scaleR_scaleC)

lemma predProjExistsInv:
  \<open>f \<in> subspace_as_set M \<Longrightarrow> cinner f (h - ((dproj M) h)) = 0\<close>
  for M :: \<open>'a subspace\<close>
proof(rule classical)
  assume \<open>f \<in> subspace_as_set M\<close>
  assume \<open>\<not> (cinner f ( h - ((dproj M) h) ) = 0)\<close>
  hence  \<open>cinner f ( h - ((dproj M) h) ) \<noteq> 0\<close> by blast
  then obtain r::real and u::complex where \<open>r > (0::real)\<close> and \<open>abs u = (1::real)\<close> 
    and \<open>cinner f ( h - ((dproj M) h) ) = (complex_of_real r) * u\<close>
    using polar_form by blast
  have \<open>\<forall> t::real. ((complex_of_real t)*u) *\<^sub>C f \<in> subspace_as_set M\<close>
    using \<open>f \<in> subspace_as_set M\<close> is_subspace.smult_closed subspace_to_set by auto
  hence \<open>\<forall> t::real. 2 * Re ( cinner ( ((complex_of_real t)*u) *\<^sub>C f ) ( h - ((dproj M) h) ) )
       \<le> (norm ( ((complex_of_real t)*u) *\<^sub>C f ))^2\<close>
    using predProjExistsA by blast
  hence \<open>\<forall> t::real. 2 * Re ( cinner ( ((complex_of_real t)*u) *\<^sub>C f ) ( h - ((dproj M) h) ) )
       \<le> ( abs((complex_of_real t)*u) * (norm f) )^2\<close>
    by (simp add: abs_complex_def less_eq_complex_def)
  hence \<open>\<forall> t::real. 2 * Re ( cinner ( ((complex_of_real t)*u) *\<^sub>C f ) ( h - ((dproj M) h) ) )
       \<le> ( (abs (complex_of_real t))*(abs u) * (norm f) )^2\<close>
    by (simp add: abs_mult)
  hence \<open>\<forall> t::real. 2 * Re ( cinner ( ((complex_of_real t)*u) *\<^sub>C f ) ( h - ((dproj M) h) ) )
       \<le> ( (abs (complex_of_real t)) * (norm f) )^2\<close>
    by (simp add: \<open>\<bar>u\<bar> = complex_of_real 1\<close>)
  hence \<open>\<forall> t::real. 2 * Re ( cinner ( ((complex_of_real t)*u) *\<^sub>C f ) ( h - ((dproj M) h) ) )
       \<le> ( t * (norm f) )^2\<close>
    using   complex_of_real_mono_iff of_real_mult of_real_power
  proof -
    have f1: "\<forall>r. r\<^sup>2 = (norm (of_real r::real))\<^sup>2"
      by (metis norm_of_real power2_abs)
    have f2: "1 = \<bar>u\<bar>"
      by (simp add: \<open>\<bar>u\<bar> = complex_of_real 1\<close>)
    have f3: "\<forall>v r. norm (timesScalarVec (complex_of_real r) (v::'a vector)) = norm (of_real (r * norm v)::real)"
      by (simp add: abs_mult)
    have "\<forall>c v. norm (timesScalarVec c (v::'a vector)) = norm (timesScalarVec \<bar>c\<bar> v)"
      by (simp add: abs_complex_def)
    then show ?thesis
      using f3 f2 f1 by (metis (no_types) \<open>\<forall>t. 2 * Re (cinner (timesScalarVec (complex_of_real t * u) f) (h - dproj M h)) \<le> (norm (timesScalarVec (complex_of_real t * u) f))\<^sup>2\<close> mult.right_neutral scaleC_scaleC)
  qed

  hence \<open>\<forall> t::real. 2 * Re ( cinner ( ((complex_of_real t)*u) *\<^sub>C f ) ( h - ((dproj M) h) ) )
       \<le> t^2 * (norm f)^2\<close>
    by (simp add: power_mult_distrib)
  hence \<open>\<forall> t::real. 2 * Re ( cnj ((complex_of_real t)*u) * cinner f ( h - ((dproj M) h) ) )
       \<le> t^2 * (norm f)^2\<close>
    by simp
  hence \<open>\<forall> t::real. 2 * Re ( (complex_of_real t) * cnj u * cinner f ( h - ((dproj M) h) ) )
       \<le> t^2 * (norm f)^2\<close>
    by simp
  hence \<open>\<forall> t::real. 2 * Re ( (complex_of_real t) * cnj u * (complex_of_real r)*u )
       \<le> t^2 * (norm f)^2\<close>
    by (metis \<open>cinner f (h - dproj M h) = complex_of_real r * u\<close> complex_scaleC_def mult_scaleC_left)
  hence \<open>\<forall> t::real. 2 * Re ( (complex_of_real t) * (complex_of_real r) * (cnj u * u) )
       \<le> t^2 * (norm f)^2\<close>
    by (metis \<open>\<forall>t. 2 * Re (complex_of_real t * cnj u * cinner f (h - dproj M h)) \<le> t\<^sup>2 * (norm f)\<^sup>2\<close> \<open>cinner f (h - dproj M h) = complex_of_real r * u\<close> semiring_normalization_rules(13))
  hence \<open>\<forall> t::real. 2 * Re ( (complex_of_real t) * (complex_of_real r) )
       \<le> t^2 * (norm f)^2\<close>
    using \<open>\<bar>u\<bar> = complex_of_real 1\<close> cnj_x_x by auto
  hence \<open>\<forall> t::real. 2 * t * r \<le> t^2 * (norm f)^2\<close>
  proof -
    have "\<forall>ra. 2 * Re (complex_of_real ra * cnj u * (complex_of_real r * u)) \<le> (ra * norm f)\<^sup>2"
      by (metis (no_types) \<open>\<forall>t. 2 * Re (complex_of_real t * cnj u * cinner f (h - dproj M h)) \<le> t\<^sup>2 * (norm f)\<^sup>2\<close> \<open>cinner f (h - dproj M h) = complex_of_real r * u\<close> power_mult_distrib)
    then have f1: "\<forall>ra. 2 * Re (u * cnj u * complex_of_real (r * ra)) \<le> (ra * norm f)\<^sup>2"
      by (simp add: mult.commute semiring_normalization_rules(13))
    have f2: "\<forall>r. (1::real) * r = r"
      by (metis mult.right_neutral mult_numeral_1)
    have f3: "(1::complex) = 1\<^sup>2"
      by auto
    have "\<forall>c. \<bar>c\<bar>\<^sup>2 = c * cnj c"
      by (metis cnj_x_x mult.commute)
    then have "\<forall>ra. r * (2 * ra) \<le> (ra * norm f)\<^sup>2"
      using f3 f2 f1 by (metis Re_complex_of_real \<open>\<bar>u\<bar> = complex_of_real 1\<close> of_real_1 of_real_mult semiring_normalization_rules(13))
    then show ?thesis
      by (simp add: mult.commute power_mult_distrib)
  qed
  hence \<open>\<forall> t::real. t > 0 \<longrightarrow> 2 * t * r \<le> t^2 * (norm f)^2\<close>
    by simp
  hence \<open>\<forall> t::real. t > 0 \<longrightarrow> (2 * r)*t \<le> (t * (norm f)^2)*t\<close>
    by (simp add: power2_eq_square)
  hence \<open>\<forall> t::real. t > 0 \<longrightarrow> (2 * r) \<le> (t * (norm f)^2)\<close>
    by simp

  hence \<open>\<forall> t::real. t > 0 \<longrightarrow> r \<le> t * ( (norm f)^2/2 )\<close>
    by auto
  have \<open>r / ( (norm f)^2) > 0\<close> 
    using \<open>0 < r\<close> \<open>\<forall>t>0. r \<le> t * ((norm f)\<^sup>2 / 2)\<close> zero_less_divide_iff by fastforce
  hence \<open>r \<le> (r / ( (norm f)^2)) * ( (norm f)^2/2 )\<close>
    using  \<open>\<forall> t::real. t > 0 \<longrightarrow> r \<le> t * ( (norm f)^2/2 )\<close>
    by blast
  hence \<open>1 \<le> 1/2\<close> 
    by (smt \<open>0 < r / (norm f)\<^sup>2\<close> \<open>0 < r\<close> \<open>\<forall>t>0. 2 * r \<le> t * (norm f)\<^sup>2\<close> eq_divide_eq)
  thus ?thesis 
    by (smt half_bounded_equal)
qed


lemma predProjExists:
  \<open>f \<in> subspace_as_set M \<Longrightarrow> cinner (h - ((dproj M) h)) f = 0\<close>
  for M :: \<open>'a subspace\<close>
  using predProjExistsInv 
  by (metis cinner_commute complex_cnj_zero)

lemma dProjExists:
  \<open>h - ((dproj M) h) \<in> subspace_as_set (ortho M)\<close>
  for M :: \<open>'a subspace\<close>
  using predProjExists 
  by (simp add: predProjExists is_orthogonal_def ortho.rep_eq)

(* Existence of the projection onto a subspace *)
lemma ProjExists:
  \<open>\<exists> k::'a vector. h - k \<in> subspace_as_set (ortho M) \<and> k \<in> subspace_as_set M\<close>
  for M :: \<open>'a subspace\<close>
  using dProjExists dproj_ex1 by blast


lemma SubspaceAndOrthoEq0A:
  \<open>(0::'a vector) \<in> (subspace_as_set M) \<inter> (subspace_as_set (ortho M))\<close>
  using is_subspace_contains_0 subspace_to_set by auto

lemma SubspaceAndOrthoEq0B:
  \<open>x \<in> (subspace_as_set M) \<inter> (subspace_as_set (ortho M)) \<Longrightarrow> x = (0::'a vector)\<close>
proof-
  assume \<open>x \<in> (subspace_as_set M) \<inter> (subspace_as_set (ortho M))\<close>
  hence \<open>x \<in> subspace_as_set M\<close> 
    by auto
  have \<open>x \<in> subspace_as_set (ortho M)\<close> 
    using \<open>x \<in> subspace_as_set M \<inter> subspace_as_set (ortho M)\<close> by auto
  hence \<open>cinner x x = 0\<close> 
    by (simp add: \<open>x \<in> subspace_as_set M\<close> is_orthogonal_def ortho.rep_eq) 
  thus ?thesis 
    by auto
qed

lemma SubspaceAndOrthoEq0AA:
  \<open>(subspace_as_set M) \<inter> (subspace_as_set (ortho M)) \<supseteq> { (0::'a vector) } \<close>
  using SubspaceAndOrthoEq0A
  by blast

lemma SubspaceAndOrthoEq0BB:
  \<open>(subspace_as_set M) \<inter> (subspace_as_set (ortho M)) \<subseteq> { (0::'a vector) } \<close>
  using SubspaceAndOrthoEq0B
  by blast

lemma SubspaceAndOrthoEq0:
  \<open>(subspace_as_set M) \<inter> (subspace_as_set (ortho M)) = { (0::'a vector) } \<close>
  using SubspaceAndOrthoEq0AA SubspaceAndOrthoEq0BB
  by blast

lemma SubspaceAndOrtho:
  \<open>r - s \<in> (subspace_as_set M) \<inter> (subspace_as_set (ortho M)) \<Longrightarrow> r = s\<close>
  by (metis SubspaceAndOrthoEq0 eq_iff_diff_eq_0 singletonD subspace_zero_bot zero_subspace.rep_eq)

(* Uniqueness of the projection onto a subspace *)
lemma ProjUnique:
  \<open>h - r \<in> subspace_as_set (ortho M) \<and> r \<in> subspace_as_set M \<Longrightarrow>
 h - s \<in> subspace_as_set (ortho M) \<and> s \<in> subspace_as_set M \<Longrightarrow>
r = s\<close>
  for M :: \<open>'a subspace\<close>
proof-
  assume \<open>h - r \<in> subspace_as_set (ortho M) \<and> r \<in> subspace_as_set M\<close>
  assume \<open>h - s \<in> subspace_as_set (ortho M) \<and> s \<in> subspace_as_set M\<close>
  have \<open>h - r \<in> subspace_as_set (ortho M)\<close> 
    by (simp add: \<open>h - r \<in> subspace_as_set (ortho M) \<and> r \<in> subspace_as_set M\<close>)
  have \<open>h - s \<in> subspace_as_set (ortho M)\<close>
    by (simp add: \<open>h - s \<in> subspace_as_set (ortho M) \<and> s \<in> subspace_as_set M\<close>)
  have \<open>r \<in> subspace_as_set M\<close>
    by (simp add: \<open>h - r \<in> subspace_as_set (ortho M) \<and> r \<in> subspace_as_set M\<close>)
  have \<open>s \<in> subspace_as_set M\<close>
    by (simp add: \<open>h - s \<in> subspace_as_set (ortho M) \<and> s \<in> subspace_as_set M\<close>)
  have \<open>r - s \<in> subspace_as_set M\<close>
    by (simp add: \<open>h - r \<in> subspace_as_set (ortho M) \<and> r \<in> subspace_as_set M\<close> \<open>s \<in> subspace_as_set M\<close> subspace_as_set_minus)
  have \<open>(h - s) - (h - r) \<in> subspace_as_set (ortho M)\<close>    
    using \<open>h - s \<in> subspace_as_set (ortho M)\<close> \<open>h - r \<in> subspace_as_set (ortho M)\<close> subspace_as_set_minus
    by metis
  hence \<open>r - s \<in> subspace_as_set (ortho M)\<close>
    by simp
  hence \<open>r - s \<in> (subspace_as_set M) \<inter> (subspace_as_set (ortho M))\<close>
    using  \<open>r - s \<in> subspace_as_set M\<close>
    by simp
  thus ?thesis
    using SubspaceAndOrtho by auto
qed

(* Existence and uniqueness of the projection onto a subspace *)
lemma preProjExistsUnique:
  \<open>\<forall> h::'a vector. \<exists>! k::'a vector. h - k \<in> subspace_as_set (ortho M) \<and> k \<in> subspace_as_set M\<close>
  for M :: \<open>'a subspace\<close>
  apply auto
  using ProjExists apply blast
  using ProjUnique by auto

(* Defining property of the projection *)
definition ProjDefProp:: \<open>('a subspace \<Rightarrow> ('a vector \<Rightarrow> 'a vector)) \<Rightarrow> bool\<close> where
  \<open>ProjDefProp \<equiv>
 \<lambda> P. \<forall> M. \<forall> h. h - (P M) h \<in> subspace_as_set (ortho M) \<and> (P M) h \<in> subspace_as_set M\<close>

lemma ProjExistsUnique:
  \<open>\<exists> P. ProjDefProp P\<close>
  using preProjExistsUnique ProjDefProp_def
  by metis

definition proj:: \<open>'a subspace \<Rightarrow> ('a vector \<Rightarrow> 'a vector)\<close> where
  \<open>proj \<equiv> SOME P. ProjDefProp P\<close>

lemma ProjExistsUniqueI_ex:
  \<open>ProjDefProp proj\<close>
  unfolding proj_def  
  by (simp add: ProjExistsUnique exE_some)

lemma projE1:
  \<open>h - (proj M) h \<in> subspace_as_set (ortho M)\<close>
  using ProjExistsUniqueI_ex
  by (metis ProjDefProp_def)

lemma projE2:
  \<open>(proj M) h \<in> subspace_as_set M\<close>
  using ProjExistsUniqueI_ex
  by (metis ProjDefProp_def)

lemma proj_kernelA:
  \<open>h \<in> subspace_as_set (ortho M) \<Longrightarrow> (proj M) h = (0::'a vector)\<close>
  by (metis diff_zero is_subspace_contains_0 mem_Collect_eq preProjExistsUnique projE1 projE2 subspace_to_set)

lemma proj_kernelB:
  \<open>(proj M) h = (0::'a vector)  \<Longrightarrow> h \<in> subspace_as_set (ortho M)\<close>
  by (metis diff_zero projE1)

lemma proj_kernel:
  \<open>(proj M) h = (0::'a vector)  \<longleftrightarrow> h \<in> subspace_as_set (ortho M)\<close>
  using proj_kernelA proj_kernelB
  by blast

lemma proj_idempotency:
  \<open>(proj M) ((proj M) h) = (proj M) h\<close>
  by (metis cancel_comm_monoid_add_class.diff_cancel is_subspace_contains_0 mem_Collect_eq preProjExistsUnique projE1 projE2 proj_kernelA subspace_to_set)

lemma proj_ranAA:
  \<open>(proj M) h \<in> subspace_as_set M\<close>
  by (simp add: projE2)

lemma proj_ranA:
  \<open>\<exists> k ::'a vector. h = (proj M) k \<Longrightarrow> h \<in> subspace_as_set M\<close>
  using proj_ranAA
  by auto

lemma proj_ranB:
  \<open>h \<in> subspace_as_set M \<Longrightarrow> (\<exists> k ::'a vector. h = (proj M) k)\<close>
  by (metis Abs_subspace_cases Abs_subspace_inverse cancel_comm_monoid_add_class.diff_cancel  preProjExistsUnique projE1  proj_kernel proj_ranA)

lemma proj_ran:
  \<open>(\<exists> k ::'a vector. h = (proj M) k) \<longleftrightarrow> h \<in> subspace_as_set M\<close>
  using proj_ranA proj_ranB
  by blast

lemma ortho_twice[simp]: "ortho (ortho x) = x"
  for x :: "'a subspace"
  sorry


lemma ortho_leq[simp]: "ortho a \<le> ortho b \<longleftrightarrow> a \<ge> b"
proof 
  show d1: "b \<le> a \<Longrightarrow> ortho a \<le> ortho b" for a b :: "'a subspace"
    apply transfer by auto
  show "ortho a \<le> ortho b \<Longrightarrow> b \<le> a"
    apply (subst ortho_twice[symmetric, of a])
    apply (subst ortho_twice[symmetric, of b])
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


end

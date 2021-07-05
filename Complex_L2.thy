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

    "Bounded_Operators-Extra.Extra_Infinite_Set_Sum"
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
    proof (rule infsetsum_mono_neutral_left)
      show "f abs_summable_on F"
        by (simp add: that)        
      show "f abs_summable_on UNIV"
        by (simp add: fsums)      
      show "f x \<le> f x"
        if "x \<in> F"
        for x :: 'a
        using that
        by simp 
      show "F \<subseteq> UNIV"
        by simp        
      show "0 \<le> f x"
        if "x \<in> UNIV - F"
        for x :: 'a
        using that f_def by auto
    qed
    finally show ?thesis 
      unfolding bound_def by assumption
  qed
  thus "has_ell2_norm x"
    unfolding has_ell2_norm_def f_def
    by (rule bdd_aboveI2[where M=bound], simp)
next
  have x1: "\<exists>B. \<forall>F. finite F \<longrightarrow> (\<Sum>s\<in>F. (cmod (x s))\<^sup>2) < B"
    if "\<And>t. finite t \<Longrightarrow> (\<Sum>i\<in>t. (cmod (x i))\<^sup>2) \<le> M"
    for M
    using that by (meson gt_ex le_less_trans)
  assume "has_ell2_norm x"
  then obtain B where "(\<Sum>xa\<in>F. norm ((cmod (x xa))\<^sup>2)) < B" if "finite F" for F
  proof atomize_elim    
    show "\<exists>B. \<forall>F. finite F \<longrightarrow> (\<Sum>xa\<in>F. norm ((cmod (x xa))\<^sup>2)) < B"
      if "has_ell2_norm x"
      using that x1
      unfolding has_ell2_norm_def unfolding bdd_above_def
      by auto
  qed 
  thus "(\<lambda>i. (cmod (x i))\<^sup>2) abs_summable_on UNIV"
  proof (rule_tac abs_summable_finiteI [where B = B])
    show "(\<Sum>t\<in>F. norm ((cmod (x t))\<^sup>2)) \<le> B"
      if "\<And>F. finite F \<Longrightarrow> (\<Sum>s\<in>F. norm ((cmod (x s))\<^sup>2)) < B"
        and "finite F" and "F \<subseteq> UNIV"
      for F :: "'a set"
      using that by fastforce
  qed     
qed

lemma has_ell2_norm_L2_set: "has_ell2_norm x = bdd_above (L2_set (norm o x) ` Collect finite)"
proof-
  have bdd_above_image_mono': "bdd_above (f`A)"
    if "\<And>x y. x\<le>y \<Longrightarrow> x:A \<Longrightarrow> y:A \<Longrightarrow> f x \<le> f y"
      and "\<exists>M\<in>A. \<forall>x \<in> A. x \<le> M"
    for f::"'a set\<Rightarrow>real" and A
    using that
    unfolding bdd_above_def by auto
  have t3: "bdd_above X \<Longrightarrow> bdd_above (sqrt ` X)" for X
    by (meson bdd_aboveI2 bdd_above_def real_sqrt_le_iff)
  moreover have t2: "bdd_above X" if bdd_sqrt: "bdd_above (sqrt ` X)" for X
  proof-
    obtain y where y:"y \<ge> sqrt x" if "x:X" for x 
      using bdd_sqrt unfolding bdd_above_def by auto
    have "y*y \<ge> x" if "x:X" for x
      by (metis power2_eq_square sqrt_le_D that y)
    thus "bdd_above X"
      unfolding bdd_above_def by auto
  qed
  ultimately have bdd_sqrt: "bdd_above X \<longleftrightarrow> bdd_above (sqrt ` X)" for X
    by rule
  have t1: "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite) =
            bdd_above ((\<lambda>A. sqrt (\<Sum>i\<in>A. ((cmod \<circ> x) i)\<^sup>2)) ` Collect finite)"
  proof (rewrite asm_rl [of "(\<lambda>A. sqrt (sum (\<lambda>i. ((cmod \<circ> x) i)\<^sup>2) A)) ` Collect finite 
                            = sqrt ` (\<lambda>A. (\<Sum>i\<in>A. (cmod (x i))\<^sup>2)) ` Collect finite"])
    show "(\<lambda>A. sqrt (\<Sum>i\<in>A. ((cmod \<circ> x) i)\<^sup>2)) ` Collect finite = sqrt ` sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite"
      by auto      
    show "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite) = bdd_above (sqrt ` sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)"
      by (meson t2 t3)      
  qed
  show "has_ell2_norm x \<longleftrightarrow> bdd_above (L2_set (norm o x) ` Collect finite)"
    unfolding has_ell2_norm_def L2_set_def
    using t1.
qed

subsection \<open>Subspaces\<close>

notation
  inf (infixl "\<sqinter>" 70) and
  sup (infixl "\<squnion>" 65) 

typedef 'a ell2 = "{x::'a\<Rightarrow>complex. has_ell2_norm x}"
  unfolding has_ell2_norm_def by (rule exI[of _ "\<lambda>_.0"], auto)
setup_lifting type_definition_ell2

lemma SUP_max:
  fixes f::"'a::order\<Rightarrow>'b::conditionally_complete_lattice"
  assumes "mono f"
    and "\<And>x. x:M \<Longrightarrow> x\<le>m"
    and "m:M"
  shows "(SUP x\<in>M. f x) = f m"
proof (rule antisym)
  show "\<Squnion> (f ` M) \<le> f m"
    by (metis assms(1) assms(2) assms(3) cSUP_least equals0D mono_def)    
  show "f m \<le> \<Squnion> (f ` M)"
    by (smt assms(1) assms(2) assms(3) cSup_eq_maximum image_iff monoE)    
qed



definition "ell2_norm x = sqrt (SUP F\<in>{F. finite F}. sum (\<lambda>i. norm (x i)^2) F)"

lemma ell2_norm_L2_set: 
  assumes "has_ell2_norm x"
  shows "ell2_norm x = (SUP F\<in>{F. finite F}. L2_set (norm o x) F)"
proof-
  have "sqrt (\<Squnion> (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)) =
      (SUP F\<in>{F. finite F}. sqrt (\<Sum>i\<in>F. (cmod (x i))\<^sup>2))"
  proof (subst continuous_at_Sup_mono)
    show "mono sqrt"
      by (simp add: mono_def)      
    show "continuous (at_left (\<Squnion> (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite))) sqrt"
      using continuous_at_split isCont_real_sqrt by blast    
    show "sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite \<noteq> {}"
      by auto      
    show "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)"
      by (metis assms has_ell2_norm_def)      
    show "\<Squnion> (sqrt ` sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite) = (SUP F\<in>Collect finite. sqrt (\<Sum>i\<in>F. (cmod (x i))\<^sup>2))"
      by (metis image_image)      
  qed  
  thus ?thesis 
    unfolding ell2_norm_def L2_set_def o_def.
qed

lemma ell2_norm_infsetsum:
  assumes "has_ell2_norm x"
  shows "ell2_norm x = sqrt (infsetsum (\<lambda>i. (norm(x i))^2) UNIV)"
proof-
  have "ell2_norm x = sqrt (\<Sum>\<^sub>ai. (cmod (x i))\<^sup>2)"
  proof (subst infsetsum_nonneg_is_SUPREMUM)
    show "(\<lambda>i. (cmod (x i))\<^sup>2) abs_summable_on UNIV"
      using assms has_ell2_norm_infsetsum by fastforce      
    show "0 \<le> (cmod (x t))\<^sup>2"
      if "t \<in> UNIV"
      for t :: 'a
      using that
      by simp 
    show "ell2_norm x = sqrt (\<Squnion> (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` {F. finite F \<and> F \<subseteq> UNIV}))"
      unfolding ell2_norm_def by auto   
  qed
  thus ?thesis 
    by auto
qed

lemma has_ell2_norm_finite[simp]: "has_ell2_norm (x::'a::finite\<Rightarrow>_)"
  unfolding has_ell2_norm_def by simp

lemma ell2_norm_finite_def: 
  "ell2_norm (x::'a::finite\<Rightarrow>complex) = sqrt (sum (\<lambda>i. (norm(x i))^2) UNIV)"
proof-    
  have "(\<Sum>i\<in>t. (cmod (x i))\<^sup>2) \<le> (\<Sum>i\<in>y. (cmod (x i))\<^sup>2)"
    if "t \<subseteq> y"
    for t y
  proof (subst sum_mono2)
    show "finite y"
      by simp      
    show "t \<subseteq> y"
      using that.
    show "0 \<le> (cmod (x b))\<^sup>2"
      if "b \<in> y - t"
      for b :: 'a
      using that
      by simp 
    show True by blast
  qed
  hence mono: "mono (sum (\<lambda>i. (cmod (x i))\<^sup>2))"
    unfolding mono_def
    by blast 
  show ?thesis
    unfolding ell2_norm_def apply (subst SUP_max[where m=UNIV])
    using mono by auto
qed

lemma L2_set_mono2:
  assumes a1: "finite L" and a2: "K \<le> L"
  shows "L2_set f K \<le> L2_set f L"
proof-
  have "(\<Sum>i\<in>K. (f i)\<^sup>2) \<le> (\<Sum>i\<in>L. (f i)\<^sup>2)"
  proof (rule sum_mono2)
    show "finite L"
      using a1.
    show "K \<subseteq> L"
      using a2.
    show "0 \<le> (f b)\<^sup>2"
      if "b \<in> L - K"
      for b :: 'a
      using that
      by simp 
  qed
  hence "sqrt (\<Sum>i\<in>K. (f i)\<^sup>2) \<le> sqrt (\<Sum>i\<in>L. (f i)\<^sup>2)"
    by (rule real_sqrt_le_mono)
  thus ?thesis
    unfolding L2_set_def.
qed

lemma ell2_norm_finite_def': "ell2_norm (x::'a::finite\<Rightarrow>complex) = L2_set (norm o x) UNIV"
proof (subst ell2_norm_L2_set)
  show "has_ell2_norm x"
    by simp    
  show "\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite) = L2_set (cmod \<circ> x) UNIV"
  proof (subst SUP_max [where m = UNIV])
    show "mono (L2_set (cmod \<circ> x))"
      by (auto simp: mono_def intro!: L2_set_mono2)
    show "(x::'a set) \<subseteq> UNIV"
      if "(x::'a set) \<in> Collect finite"
      for x :: "'a set"
      using that
      by simp 
    show "(UNIV::'a set) \<in> Collect finite"
      by simp      
    show "L2_set (cmod \<circ> x) UNIV = L2_set (cmod \<circ> x) UNIV"
      by simp
  qed
qed 


lemma ell2_1: 
  assumes  "finite F" 
  shows "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) \<le> 1"
proof - 
  have "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 0" if "a\<notin>F"
  proof (subst sum.cong [where B = F and h = "\<lambda>_. 0"])
    show "F = F"
      by blast
    show "(cmod (if a = x then 1 else 0))\<^sup>2 = 0"
      if "x \<in> F"
      for x :: 'a
      using that \<open>a \<notin> F\<close> by auto 
    show "(\<Sum>_\<in>F. (0::real)) = 0"
      by simp
  qed 
  moreover have "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 1" if "a\<in>F"
  proof -
    obtain F0 where "a\<notin>F0" and F_F0: "F=insert a F0"
      by (meson \<open>a \<in> F\<close> mk_disjoint_insert) 
    have "(\<Sum>i\<in>insert a F0. (cmod (if a = i then 1 else 0))\<^sup>2) = 1"
    proof (subst sum.insert_remove)
      show "finite F0"
        using F_F0 assms by auto
      show "(cmod (if a = a then 1 else 0))\<^sup>2 + (\<Sum>i\<in>F0 - {a}. (cmod (if a = i then 1 else 0))\<^sup>2) = 1"
        using sum.not_neutral_contains_not_neutral by fastforce        
    qed
    thus "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) = 1"
      unfolding F_F0.
  qed
  ultimately show "(\<Sum>i\<in>F. (cmod (if a = i then 1 else 0))\<^sup>2) \<le> 1"
    by linarith
qed


lemma cSUP_leD: "bdd_above (f`A) \<Longrightarrow> (SUP i\<in>A. f i) \<le> y \<Longrightarrow> i \<in> A \<Longrightarrow> f i \<le> y" 
  for y :: "'a::conditionally_complete_lattice"
  by (meson cSUP_upper order_trans)

lemma ell2_norm_0:
  assumes "has_ell2_norm x"
  shows "(ell2_norm x = 0) = (x = (\<lambda>_. 0))"
proof
  assume u1: "x = (\<lambda>_. 0)"
  have u2: "(SUP x::'a set\<in>Collect finite. (0::real)) = 0"
    if "x = (\<lambda>_. 0)"
    by (metis cSUP_const empty_Collect_eq finite.emptyI)
  show "ell2_norm x = 0"
    unfolding ell2_norm_def
    using u1 u2 by auto 
next
  assume norm0: "ell2_norm x = 0"
  show "x = (\<lambda>_. 0)"
  proof
    fix i
    have "sum (\<lambda>i. (cmod (x i))\<^sup>2) {i} \<le> 0" 
    proof (rule cSUP_leD [where A = "Collect finite"])
      show "bdd_above (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite)"
        by (metis assms has_ell2_norm_def)        
      show "\<Squnion> (sum (\<lambda>i. (cmod (x i))\<^sup>2) ` Collect finite) \<le> 0"
        using norm0  unfolding has_ell2_norm_def ell2_norm_def by auto
      show "{i} \<in> Collect finite"
        by simp        
    qed
    thus "x i = 0" by auto
  qed
qed


lemma ell2_norm_smult:
  assumes "has_ell2_norm x"
  shows "has_ell2_norm (\<lambda>i. c * x i)" and "ell2_norm (\<lambda>i. c * x i) = cmod c * ell2_norm x"
proof -
  have L2_set_mul: "L2_set (cmod \<circ> (\<lambda>i. c * x i)) F = cmod c * L2_set (cmod \<circ> x) F" for F
  proof-
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
  have "ell2_norm (\<lambda>i. c * x i) = (SUP F \<in> Collect finite. (L2_set (cmod \<circ> (\<lambda>i. c * x i)) F))"
    by (simp add: ell2_norm_L2_set has)
  also have "\<dots> = (SUP F \<in> Collect finite. (cmod c * L2_set (cmod \<circ> x) F))"
    using L2_set_mul by auto   
  also have "\<dots> = cmod c * ell2_norm x" 
  proof (subst ell2_norm_L2_set)
    show "has_ell2_norm x"
      by (simp add: assms)      
    show "(SUP F\<in>Collect finite. cmod c * L2_set (cmod \<circ> x) F) = cmod c * \<Squnion> (L2_set (cmod \<circ> x) ` Collect finite)"
    proof (subst continuous_at_Sup_mono [where f = "\<lambda>x. cmod c * x"])
      show "mono ((*) (cmod c))"
        by (simp add: mono_def ordered_comm_semiring_class.comm_mult_left_mono)
      show "continuous (at_left (\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite))) ((*) (cmod c))"
      proof (rule continuous_mult)
        show "continuous (at_left (\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite))) (\<lambda>x. cmod c)"
          by simp
        show "continuous (at_left (\<Squnion> (L2_set (cmod \<circ> x) ` Collect finite))) (\<lambda>x. x)"
          by simp
      qed    
      show "L2_set (cmod \<circ> x) ` Collect finite \<noteq> {}"
        by auto        
      show "bdd_above (L2_set (cmod \<circ> x) ` Collect finite)"
        by (meson assms has_ell2_norm_L2_set)        
      show "(SUP F\<in>Collect finite. cmod c * L2_set (cmod \<circ> x) F) = \<Squnion> ((*) (cmod c) ` L2_set (cmod \<circ> x) ` Collect finite)"
        by (metis image_image)        
    qed   
  qed     
  finally show "ell2_norm (\<lambda>i. c * x i) = cmod c * ell2_norm x".
qed


lemma ell2_norm_triangle:
  assumes "has_ell2_norm x" and "has_ell2_norm y"
  shows "has_ell2_norm (\<lambda>i. x i + y i)" and "ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
proof -
  have triangle: "L2_set (cmod \<circ> (\<lambda>i. x i + y i)) F \<le> L2_set (cmod \<circ> x) F + L2_set (cmod \<circ> y) F" 
    (is "?lhs\<le>?rhs") 
    if "finite F" for F
  proof -
    have "?lhs \<le> L2_set (\<lambda>i. (cmod o x) i + (cmod o y) i) F"
    proof (rule L2_set_mono)
      show "(cmod \<circ> (\<lambda>i. x i + y i)) i \<le> (cmod \<circ> x) i + (cmod \<circ> y) i"
        if "i \<in> F"
        for i :: 'a
        using that norm_triangle_ineq by auto 
      show "0 \<le> (cmod \<circ> (\<lambda>i. x i + y i)) i"
        if "i \<in> F"
        for i :: 'a
        using that
        by simp 
    qed
    also have "\<dots> \<le> ?rhs"
      by (rule L2_set_triangle_ineq)
    finally show ?thesis .
  qed
  obtain Mx My where Mx: "Mx \<ge> L2_set (cmod o x) F" and My: "My \<ge> L2_set (cmod o y) F" 
    if "finite F" for F
    using assms unfolding has_ell2_norm_L2_set bdd_above_def by auto
  hence MxMy: "Mx + My \<ge> L2_set (cmod \<circ> x) F + L2_set (cmod \<circ> y) F" if "finite F" for F
    using that by fastforce
  hence bdd_plus: "bdd_above ((\<lambda>xa. L2_set (cmod \<circ> x) xa + L2_set (cmod \<circ> y) xa) ` Collect finite)"
    unfolding bdd_above_def by auto
  from MxMy have MxMy': "Mx + My \<ge> L2_set (cmod \<circ> (\<lambda>i. x i + y i)) F" if "finite F" for F 
    using triangle that by fastforce
  thus has: "has_ell2_norm (\<lambda>i. x i + y i)"
    unfolding has_ell2_norm_L2_set bdd_above_def by auto
  have SUP_plus: "(SUP x\<in>A. f x + g x) \<le> (SUP x\<in>A. f x) + (SUP x\<in>A. g x)" 
    if notempty: "A\<noteq>{}" and bddf: "bdd_above (f`A)"and bddg: "bdd_above (g`A)"
    for f g :: "'a set \<Rightarrow> real" and A
  proof-
    have xleq: "x \<le> (SUP x\<in>A. f x) + (SUP x\<in>A. g x)" if x: "x \<in> (\<lambda>x. f x + g x) ` A" for x
    proof -
      obtain a where aA: "a:A" and ax: "x = f a + g a"
        using x by blast
      have fa: "f a \<le> (SUP x\<in>A. f x)"
        by (simp add: bddf aA cSUP_upper)
      moreover have "g a \<le> (SUP x\<in>A. g x)"
        by (simp add: bddg aA cSUP_upper)
      ultimately have "f a + g a \<le> (SUP x\<in>A. f x) + (SUP x\<in>A. g x)" by simp
      with ax show ?thesis by simp
    qed
    have "(\<lambda>x. f x + g x) ` A \<noteq> {}"
      using notempty by auto        
    moreover have "x \<le> \<Squnion> (f ` A) + \<Squnion> (g ` A)"
      if "x \<in> (\<lambda>x. f x + g x) ` A"
      for x :: real
      using that
      by (simp add: xleq) 
    ultimately show ?thesis
      by (meson bdd_above_def cSup_le_iff)      
  qed
  have a2: "bdd_above (L2_set (cmod \<circ> x) ` Collect finite)"
    by (meson assms(1) has_ell2_norm_L2_set)    
  have a3: "bdd_above (L2_set (cmod \<circ> y) ` Collect finite)"
    by (meson assms(2) has_ell2_norm_L2_set)    
  have a1: "Collect finite \<noteq> {}"
    by auto    
  have a4: "\<Squnion> (L2_set (cmod \<circ> (\<lambda>i. x i + y i)) ` Collect finite)
    \<le> (SUP xa\<in>Collect finite.
           L2_set (cmod \<circ> x) xa + L2_set (cmod \<circ> y) xa)"
    by (metis (mono_tags, lifting) a1 bdd_plus cSUP_mono mem_Collect_eq triangle)    
  have "\<forall>r. \<Squnion> (L2_set (cmod \<circ> (\<lambda>a. x a + y a)) ` Collect finite) \<le> r \<or> \<not> (SUP A\<in>Collect finite. L2_set (cmod \<circ> x) A + L2_set (cmod \<circ> y) A) \<le> r"
    using a4 by linarith
  hence "\<Squnion> (L2_set (cmod \<circ> (\<lambda>i. x i + y i)) ` Collect finite)
    \<le> \<Squnion> (L2_set (cmod \<circ> x) ` Collect finite) +
       \<Squnion> (L2_set (cmod \<circ> y) ` Collect finite)"
    by (metis (no_types) SUP_plus a1 a2 a3)
  hence "\<Squnion> (L2_set (cmod \<circ> (\<lambda>i. x i + y i)) ` Collect finite) \<le> ell2_norm x + ell2_norm y"
    by (simp add: assms(1) assms(2) ell2_norm_L2_set)
  thus "ell2_norm (\<lambda>i. x i + y i) \<le> ell2_norm x + ell2_norm y"
    by (simp add: ell2_norm_L2_set has)  
qed


lift_definition ket :: "'a \<Rightarrow> 'a ell2" is "\<lambda>x y. if x=y then 1 else 0"
proof-
  have "\<exists>M. \<forall>x\<in>sum (\<lambda>i. (cmod (if a = i then 1 else 0))\<^sup>2) `
                Collect finite.
                x \<le> M"
    for a::'a
  proof simp
    show "\<exists>M. \<forall>x. finite x \<longrightarrow> (\<Sum>i\<in>x. (cmod (if a = i then 1 else 0))\<^sup>2) \<le> M"
      by (metis ell2_1)      
  qed
  thus "has_ell2_norm (\<lambda>y. if a = y then 1 else 0)"
    for a::'a
    unfolding has_ell2_norm_def bdd_above_def
    by auto
qed

lemma cSUP_eq_maximum:
  fixes z :: "_::conditionally_complete_lattice"
  assumes "\<exists>x\<in>X. f x = z" and "\<And>x. x \<in> X \<Longrightarrow> f x \<le> z"
  shows "(SUP x\<in>X. f x) = z"
  by (metis (mono_tags, hide_lams) assms(1) assms(2) cSup_eq_maximum imageE image_eqI)


instantiation ell2 :: (type)complex_vector begin
lift_definition zero_ell2 :: "'a ell2" is "\<lambda>_. 0" by (auto simp: has_ell2_norm_def)
lift_definition uminus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2" is uminus by (simp add: has_ell2_norm_def)
lift_definition plus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>f g x. f x + g x"
  by (rule ell2_norm_triangle) 
lift_definition minus_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>f g x. f x - g x"
proof-
  have "has_ell2_norm (\<lambda>x::'a. f x + - g x)"
    if "has_ell2_norm f" and "has_ell2_norm g"
    for f g ::"'a \<Rightarrow> complex"
  proof (rule ell2_norm_triangle)
    show "has_ell2_norm f"
      by (simp add: that(1))
    have "bdd_above (sum (\<lambda>i. (cmod (g i))\<^sup>2) ` Collect finite)"
      using that(2)
      unfolding has_ell2_norm_def
      by auto
    thus "has_ell2_norm (\<lambda>i. - g i)"
      unfolding has_ell2_norm_def
      by auto
  qed 
  thus "has_ell2_norm (\<lambda>x. f x - g x)"
    if "has_ell2_norm f" and "has_ell2_norm g"
    for f g::"'a \<Rightarrow> complex"
    using that
    by auto
qed

lift_definition scaleR_ell2 :: "real \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>r f x. complex_of_real r * f x"
  by (rule ell2_norm_smult)
lift_definition scaleC_ell2 :: "complex \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>c f x. c * f x"
  by (rule ell2_norm_smult)

instance
proof
  show "((*\<^sub>R) r::'a ell2 \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
  proof (transfer ; rule ext ; simp)
    show "r *\<^sub>R (x::'a ell2) = complex_of_real r *\<^sub>C x"
      for r :: real
        and x :: "'a ell2"
      apply transfer
      by simp
  qed

  show "a + b + c = a + (b + c)"
    for a :: "'a ell2"
      and b :: "'a ell2"
      and c :: "'a ell2"
    by (transfer ; rule ext ; simp)

  show "a + b = b + a"
    for a :: "'a ell2"
      and b :: "'a ell2"
    by (transfer ; rule ext ; simp)
  show "0 + a = a"
    for a :: "'a ell2"
    by (transfer ; rule ext ; simp)
  show "- a + a = 0"
    for a :: "'a ell2"
    by (transfer ; rule ext ; simp)
  show "a - b = a + - b"
    for a :: "'a ell2"
      and b :: "'a ell2"
    by (transfer ; rule ext ; simp)
  show "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a ell2"
      and y :: "'a ell2"
  proof (transfer ; rule ext ; simp)
    show "a * (x t + y t) = a * x t + a * y t"
      if "has_ell2_norm x"
        and "has_ell2_norm y"
      for a :: complex
        and x y:: "'a \<Rightarrow> complex"
        and t :: 'a
      using that
      by (simp add: ring_class.ring_distribs(1)) 
  qed

  show "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x"
    for a b :: complex
      and x :: "'a ell2"
  proof (transfer ; rule ext ; simp)
    show "(a + b) * x t = a * x t + b * x t"
      if "has_ell2_norm x"
      for a b:: complex
        and x :: "'a \<Rightarrow> complex"
        and t :: 'a
      using that
      by (simp add: ring_class.ring_distribs(2)) 
  qed
  show "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x"
    for a b :: complex
      and x :: "'a ell2"
    by (transfer ; rule ext ; simp)
  show "1 *\<^sub>C x = x"
    for x :: "'a ell2"
    by (transfer ; rule ext ; simp)
qed
end

instantiation ell2 :: (type)complex_normed_vector begin
lift_definition norm_ell2 :: "'a ell2 \<Rightarrow> real" is ell2_norm .
declare norm_ell2_def[code del]
definition "dist x y = norm (x - y)" for x y::"'a ell2"
definition "sgn x = x /\<^sub>R norm x" for x::"'a ell2"
definition [code del]: "uniformity = (INF e\<in>{0<..}. principal {(x::'a ell2, y). norm (x - y) < e})"
definition [code del]: "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in INF e\<in>{0<..}. principal {(x, y). norm (x - y) < e}. x' = x \<longrightarrow> y \<in> U)" for U :: "'a ell2 set"
instance
proof
  show "dist x y = norm (x - y)"
    for x y :: "'a ell2"
    by (simp add: dist_ell2_def)    
  show "sgn x = x /\<^sub>R norm x"
    for x :: "'a ell2"
    by (simp add: sgn_ell2_def)    
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a ell2) y < e})"
    unfolding dist_ell2_def  uniformity_ell2_def by simp
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a ell2) = x \<longrightarrow> y \<in> U)"
    for U :: "'a ell2 set"
    unfolding uniformity_ell2_def open_ell2_def by simp_all        
  show "(norm x = 0) = (x = 0)"
    for x :: "'a ell2"
    apply transfer by (fact ell2_norm_0)    
  show "norm (x + y) \<le> norm x + norm y"
    for x :: "'a ell2"
      and y :: "'a ell2"
    apply transfer by (fact ell2_norm_triangle)
  show "norm (a *\<^sub>R (x::'a ell2)) = \<bar>a\<bar> * norm x"
    for a :: real
      and x :: "'a ell2"
  proof transfer
    show "ell2_norm (\<lambda>x. complex_of_real a * f (x::'a)) = \<bar>a\<bar> * ell2_norm f"
      if "has_ell2_norm (f::'a \<Rightarrow> complex)"
      for a :: real
        and f :: "'a \<Rightarrow> complex"
      using that
      by (simp add: ell2_norm_smult(2)) 
  qed
  show "norm (a *\<^sub>C x) = cmod a * norm x"
    for a :: complex
      and x :: "'a ell2"
  proof transfer
    show "ell2_norm (\<lambda>x. a * f x) = cmod a * ell2_norm f"
      if "has_ell2_norm f"
      for a :: complex
        and f :: "'a \<Rightarrow> complex"
      using that
      by (simp add: ell2_norm_smult(2)) 
  qed
qed  

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
    proof (subst infsetsum_add [symmetric])
      show "(\<lambda>i. cnj (x i) * z i) abs_summable_on UNIV"
        by (simp add: cnj_x_z)        
      show "(\<lambda>i. cnj (y i) * z i) abs_summable_on UNIV"
        by (simp add: cnj_y_z)        
      show "(\<Sum>\<^sub>ai. cnj (x i + y i) * z i) = (\<Sum>\<^sub>ai. cnj (x i) * z i + cnj (y i) * z i)"
        by (metis complex_cnj_add distrib_right)
    qed
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
    proof (subst infsetsum_cmult_right [symmetric])
      show "(\<lambda>i. cnj (x i) * y i) abs_summable_on UNIV"
        if "(\<lambda>i. cnj (x i) * y i) abs_summable_on UNIV"
          and "cnj c \<noteq> 0"
        using that
        by simp 
      show "(\<Sum>\<^sub>ai. cnj (c * x i) * y i) = (\<Sum>\<^sub>ai. cnj c * (cnj (x i) * y i))"
        if "(\<lambda>i. cnj (x i) * y i) abs_summable_on UNIV"
        using that
        by (metis complex_cnj_mult vector_space_over_itself.scale_scale) 
    qed
  qed

  show "0 \<le> cinner x x"
  proof transfer
    fix x :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    hence "(\<lambda>i. cmod (cnj (x i) * x i)) abs_summable_on UNIV"
      by (simp del: abs_summable_on_norm_iff add: norm_mult has_ell2_norm_infsetsum power2_eq_square)
    hence "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      by (subst abs_summable_on_norm_iff[symmetric])      
    hence sum: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      unfolding has_ell2_norm_infsetsum power2_eq_square.
    have "0 = (\<Sum>\<^sub>ai::'a. 0)" by auto
    also have "\<dots> \<le> (\<Sum>\<^sub>ai. cnj (x i) * x i)"
    proof (rule infsetsum_mono_complex)
      show "(\<lambda>i. 0::complex) abs_summable_on (UNIV::'a set)"
        by simp        
      show "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
        by (simp add: sum)        
      show "0 \<le> cnj (f x) * f x"
        if "x \<in> UNIV"
        for x :: 'a and f :: "'a \<Rightarrow>_"
        using that
        by simp 
    qed
    finally show "0 \<le> (\<Sum>\<^sub>ai. cnj (x i) * x i)" by assumption
  qed

  show "(cinner x x = 0) = (x = 0)"
  proof (transfer, auto)
    fix x :: "'a \<Rightarrow> complex"
    assume "has_ell2_norm x"
    hence "(\<lambda>i::'a. cmod (cnj (x i) * x i)) abs_summable_on UNIV"
      unfolding has_ell2_norm_infsetsum power2_eq_square
      by (metis (no_types, lifting) abs_summable_on_cong complex_mod_cnj norm_mult) 
    hence cmod_x2: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      unfolding has_ell2_norm_infsetsum power2_eq_square
      by simp
    assume eq0: "(\<Sum>\<^sub>ai. cnj (x i) * x i) = 0"
    show "x = (\<lambda>_. 0)"
    proof (rule ccontr)
      assume "x \<noteq> (\<lambda>_. 0)"
      then obtain i where "x i \<noteq> 0" by auto
      hence "0 < cnj (x i) * x i"
        by (metis le_less cnj_x_x_geq0 complex_cnj_zero_iff vector_space_over_itself.scale_eq_0_iff)
      also have "\<dots> = (\<Sum>\<^sub>ai\<in>{i}. cnj (x i) * x i)" by auto
      also have "\<dots> \<le> (\<Sum>\<^sub>ai. cnj (x i) * x i)"
      proof (rule infsetsum_subset_complex)
        show "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
          by (simp add: cmod_x2)          
        show "{i} \<subseteq> UNIV"
          by simp          
        show "0 \<le> cnj (f x) * f x"
          if "x \<notin> {i}"
          for x :: 'a and f::"'a \<Rightarrow> _"
          using that
          by simp 
      qed
      also from eq0 have "\<dots> = 0" by assumption
      finally show False by simp
    qed
  qed

  show "norm x = sqrt (cmod (cinner x x))"
  proof transfer 
    fix x :: "'a \<Rightarrow> complex" 
    assume x: "has_ell2_norm x"
    have "(\<lambda>i::'a. cmod (x i) * cmod (x i)) abs_summable_on UNIV \<Longrightarrow>
    (\<lambda>i::'a. cmod (cnj (x i) * x i)) abs_summable_on UNIV"
      by (simp del: abs_summable_on_norm_iff add: norm_mult has_ell2_norm_infsetsum power2_eq_square)
    hence sum: "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
      using x
      unfolding has_ell2_norm_infsetsum power2_eq_square
      by auto
    from x have "ell2_norm x = sqrt (\<Sum>\<^sub>ai. (cmod (x i))\<^sup>2)"
    proof (subst ell2_norm_infsetsum)
      show "has_ell2_norm x"
        if "has_ell2_norm x"
        using that.
      show "sqrt (\<Sum>\<^sub>ai. (cmod (x i))\<^sup>2) = sqrt (\<Sum>\<^sub>ai. (cmod (x i))\<^sup>2)"
        if "has_ell2_norm x"
        using that
        by simp 
    qed
    also have "\<dots> = sqrt (\<Sum>\<^sub>ai. cmod (cnj (x i) * x i))"
      unfolding norm_complex_def power2_eq_square by auto
    also have "\<dots> = sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i))"
    proof (subst infsetsum_cmod)
      show "(\<lambda>i. cnj (x i) * x i) abs_summable_on UNIV"
        by (simp add: sum)        
      show "0 \<le> cnj (f x) * f x"
        if "(x::'a) \<in> UNIV"
        for x :: 'a and f::"'a \<Rightarrow> _"
        using that
        by simp 
      show "sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i)) = sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i))"
        by simp        
    qed
    finally show "ell2_norm x = sqrt (cmod (\<Sum>\<^sub>ai. cnj (x i) * x i))" by assumption
  qed
qed
end

lemma norm_ell2_component: "norm (Rep_ell2 x i) \<le> norm x"
proof transfer
  fix x :: "'a \<Rightarrow> complex" and i
  assume has: "has_ell2_norm x"
  have a1: "L2_set (cmod \<circ> x) {i}
    \<le> \<Squnion> (L2_set (cmod \<circ> x) ` Collect finite)"
    by (metis cSup_upper finite.emptyI finite_insert has has_ell2_norm_L2_set imageI mem_Collect_eq)
  have "cmod (x i) = L2_set (cmod \<circ> x) {i}" by auto
  also have "\<dots> \<le> ell2_norm x"
    using has a1
    by (simp add: ell2_norm_L2_set)   
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
  have d1: \<open>Sup (power2 ` S) \<le> power2 (Sup S)\<close>
    if \<open>S \<noteq> {}\<close> and \<open>bdd_above S\<close> and \<open>\<forall> x \<in> S. x \<ge> 0\<close>
    for S :: \<open>real set\<close>
  proof-
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
  have d2: \<open>S \<noteq> {} \<Longrightarrow> bdd_above S  \<Longrightarrow> \<forall> x \<in> S. x \<ge> 0 \<Longrightarrow> Sup (sqrt ` S) = sqrt (Sup S)\<close>
    for S :: \<open>real set\<close>
  proof-     
    assume \<open>S \<noteq> {}\<close> and \<open>bdd_above S\<close> and \<open>\<forall> x \<in> S. x \<ge> 0\<close>
    have \<open>mono sqrt\<close>
      by (simp add: mono_def) 
    have a1: \<open>Sup (sqrt ` S) \<le> sqrt (Sup S)\<close>
      using  \<open>mono sqrt\<close>
      by (simp add: \<open>S \<noteq> {}\<close> \<open>bdd_above S\<close> bdd_above_image_mono cSUP_le_iff cSup_upper) 
    have \<open>sqrt ` S \<noteq> {}\<close>
      by (simp add: \<open>S \<noteq> {}\<close>) 
    moreover have \<open>bdd_above (sqrt ` S)\<close>
      by (meson  \<open>bdd_above S\<close> bdd_aboveI2 bdd_above_def real_sqrt_le_iff)   
    ultimately have \<open>(Sup ( power2 ` (sqrt ` S) )) \<le> power2 (Sup (sqrt ` S))\<close>
      using d1
      by (simp add: \<open>\<forall> x \<in> S. x \<ge> 0\<close>)
    hence b1: \<open>(Sup ( (\<lambda> t. t^2) ` (sqrt ` S) )) \<le> (Sup (sqrt ` S))^2\<close>
      by simp
    have  \<open>(\<lambda> t. t^2) ` (sqrt ` S) \<subseteq> S\<close>
      by (simp add: \<open>\<forall> x \<in> S. x \<ge> 0\<close> image_subset_iff)
    moreover have  \<open>S \<subseteq> (\<lambda> t. t^2) ` (sqrt ` S)\<close>
      by (simp add: \<open>\<forall> x \<in> S. x \<ge> 0\<close> image_iff subsetI)
    ultimately have b2: \<open>(\<lambda> t. t^2) ` (sqrt ` S) = S\<close> by blast
    have \<open>(Sup S) \<le> (Sup (sqrt ` S))^2\<close>
      using b1 b2
      by simp
    moreover have \<open>Sup S \<ge> 0\<close>
      using \<open>\<forall> x \<in> S. x \<ge> 0\<close>
        \<open>S \<noteq> {}\<close> \<open>bdd_above S\<close> cSup_upper2 by auto 
    ultimately have a2: \<open>sqrt (Sup S) \<le> Sup (sqrt ` S)\<close>
      by (metis all_not_in_conv  \<open>S \<noteq> {}\<close>  \<open>bdd_above S\<close>  \<open>\<forall> x \<in> S. x \<ge> 0\<close> bdd_aboveI2 bdd_above_def cSup_upper2 empty_is_image image_iff real_le_lsqrt real_sqrt_ge_0_iff real_sqrt_le_iff)
    show ?thesis using a1 a2 by simp
  qed
  have \<open>ell2_norm f = sqrt (Sup { \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S })\<close>
    by (simp add: ell2_norm_def setcompr_eq_image)
  have "0 \<le> (\<Sum>a\<in>A. (cmod (f a))\<^sup>2)"
    for A
    by (meson sum_nonneg zero_le_power2)
  hence g1: "r \<notin> {\<Sum>a\<in>A. (cmod (f a))\<^sup>2 |A. finite A} \<or> 0 \<le> r"
    for r
    by blast
  have \<open>{ \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S } \<noteq> {}\<close>
    by auto
  moreover have \<open>bdd_above { \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S }\<close>
    by (metis (no_types) assms has_ell2_norm_def setcompr_eq_image)
  moreover have "x \<ge> 0"
    if "x \<in> { \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S }"
    for x
    using g1 that by auto
  ultimately have \<open>Sup (sqrt ` { \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S })
       = sqrt (Sup ({ \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S }))\<close>
    by (simp add: d2)
  thus ?thesis using \<open>ell2_norm f = sqrt (Sup { \<Sum> i \<in> S. (cmod (f i))\<^sup>2  | S::'a set. finite S })\<close>
    by (simp add: image_image setcompr_eq_image)
qed

definition pointwise_convergent::\<open>( nat \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) ) \<Rightarrow> bool\<close> where
  \<open>pointwise_convergent x = (\<exists> l. (x \<midarrow>pointwise\<rightarrow> l) )\<close>

lemma has_ell2_norm_explicit:
  \<open>has_ell2_norm f \<longleftrightarrow> ( \<exists> M::real. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod (f x))^2) \<le> M )\<close>
  for f::\<open>'a \<Rightarrow> complex\<close>
proof-
  have \<open>has_ell2_norm f \<Longrightarrow> ( \<exists> M::real. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod (f x))^2) \<le> M )\<close>
    by (simp add: bdd_above_def has_ell2_norm_def)
  moreover have "has_ell2_norm f"
    if \<open>\<exists>M. \<forall> S. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod (f x))^2) \<le> M\<close>
    using that
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
  have f2: "(\<exists>a b. ((a::'a) \<in> A \<and> b \<in> A \<and> (f a::'a \<times> bool) = f b) \<and> a \<noteq> b) \<or> inj_on f A"
    for A f
    by (meson inj_onI)
  have "\<not> inj f \<or> ((f (a::'a)::'a \<times> bool) = f b) = (a = b)"
    for f a b
    by (metis inj_eq)
  hence "inj_on (\<lambda>a. (a, True)) S"
    using f2 by (metis (no_types) \<open>inj (\<lambda>x. (x, True))\<close>)
  hence z2: \<open>(\<Sum> x\<in>S. (F (x, True) + G (x, True))^2) 
        = (\<Sum> z \<in> (\<lambda> t. (t, True))`S.  (F z + G z)^2)\<close>
    by (metis (no_types, lifting) sum.reindex_cong)      
  have f2: "(\<exists>a b. ((a::'a) \<in> A \<and> b \<in> A \<and> (f a::'a \<times> bool) = f b) \<and> a \<noteq> b) \<or> inj_on f A"
    for A f
    by (meson inj_onI)
  have "\<not> inj f \<or> ((f (a::'a)::'a \<times> bool) = f b) = (a = b)"
    for f a b
    by (metis inj_eq)
  hence "inj_on (\<lambda>a. (a, False)) S"
    using f2 by (metis (no_types) \<open>inj (\<lambda>x. (x, False))\<close>)
  hence z1: \<open>(\<Sum> x\<in>S. (F (x, False) + G (x, False))^2) 
          = (\<Sum> z \<in> (\<lambda> t. (t, False))`S.  (F z + G z)^2)\<close>
    by (metis (no_types, lifting) sum.reindex_cong)      
  have y1: \<open>(\<Sum> z\<in>SB. (F z)^2) = (\<Sum> z\<in>{(x, True) | x. x \<in> S}. (F z)^2)
                    +(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (F z)^2)\<close>
    using  \<open>SB = {(x, True) | x. x \<in> S} \<union> {(x, False) | x. x \<in> S}\<close>
      \<open>{(x, True) | x. x \<in> S} \<inter> {(x, False) | x. x \<in> S} = {}\<close>
      \<open>finite {(x, True) | x. x \<in> S}\<close>  \<open>finite {(x, False) | x. x \<in> S}\<close>
    by (simp add: sum.union_disjoint)    
  have y2: \<open>(\<Sum> z\<in>SB. (G z)^2) = (\<Sum> z\<in>{(x, True) | x. x \<in> S}. (G z)^2)
                    +(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (G z)^2)\<close>
    using  \<open>SB = {(x, True) | x. x \<in> S} \<union> {(x, False) | x. x \<in> S}\<close>
      \<open>{(x, True) | x. x \<in> S} \<inter> {(x, False) | x. x \<in> S} = {}\<close>
      \<open>finite {(x, True) | x. x \<in> S}\<close>  \<open>finite {(x, False) | x. x \<in> S}\<close>
    by (simp add: sum.union_disjoint)
  have \<open>(\<Sum> z\<in>{(x, True) | x. x \<in> S}. (F z)^2)
            = (\<Sum> x\<in>S. (F ( (\<lambda> t. (t, True)) x ))^2)\<close>
    using Pair_inject  sum.eq_general image_iff \<open>{(x, True) | x. x \<in> S} =  (\<lambda> t. (t, True))`S\<close>
    by smt
  hence x4: \<open>(\<Sum> z\<in>{(x, True) | x. x \<in> S}. (F z)^2) = (\<Sum> x\<in>S. (F (x, True))^2)\<close>
    by blast
  have \<open>(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (F z)^2)
            = (\<Sum> x\<in>S. (F ( (\<lambda> t. (t, False)) x ))^2)\<close>
    using Pair_inject  sum.eq_general image_iff \<open>{(x, False) | x. x \<in> S} =  (\<lambda> t. (t, False))`S\<close>
    by smt
  hence x3: \<open>(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (F z)^2) = (\<Sum> x\<in>S. (F (x, False))^2)\<close>
    by blast
  have \<open>(\<Sum> z\<in>{(x, True) | x. x \<in> S}. (G z)^2)
            = (\<Sum> x\<in>S. (G ( (\<lambda> t. (t, True)) x ))^2)\<close>
    using Pair_inject  sum.eq_general image_iff \<open>{(x, True) | x. x \<in> S} =  (\<lambda> t. (t, True))`S\<close>
    by smt
  hence x2: \<open>(\<Sum> z\<in>{(x, True) | x. x \<in> S}. (G z)^2) = (\<Sum> x\<in>S. (G (x, True))^2)\<close>
    by blast
  have \<open>(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (G z)^2)
            = (\<Sum> x\<in>S. (G ( (\<lambda> t. (t, False)) x ))^2)\<close>
    using Pair_inject  sum.eq_general image_iff \<open>{(x, False) | x. x \<in> S} =  (\<lambda> t. (t, False))`S\<close>
    by smt
  hence x1: \<open>(\<Sum> z\<in>{(x, False) | x. x \<in> S}. (G z)^2) = (\<Sum> x\<in>S. (G (x, False))^2)\<close>
    by blast
  have  \<open>sqrt (\<Sum> x\<in>S. (cmod (f x + g x))^2)
       = sqrt (\<Sum> x\<in>S. (cmod ( Complex (Re (f x) + Re (g x)) (Im (f x) + Im (g x)) ))^2)\<close>
    by (simp add: plus_complex.code)
  also have  \<open>...
   = sqrt (\<Sum> x\<in>S. ( sqrt ( (Re (f x) + Re (g x))^2 + (Im (f x) + Im (g x))^2 ) )^2)\<close>
    using complex_norm by auto
  finally have \<open>sqrt (\<Sum> x\<in>S. (cmod (f x + g x))^2)
       = sqrt (\<Sum> x\<in>S. ( (Re (f x) + Re (g x))^2 + (Im (f x) + Im (g x))^2 ))\<close>
    by simp
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
    using z1 z2 by simp 
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
    using y1 y2 \<open>sqrt (\<Sum>z\<in>SB. (F z + G z)\<^sup>2) \<le> sqrt (\<Sum>z\<in>SB. (F z)\<^sup>2) + sqrt (\<Sum>z\<in>SB. (G z)\<^sup>2)\<close>
    by simp       
  also have \<open>... = sqrt ( (\<Sum> x\<in>S. (F (x, True))^2)+(\<Sum> x\<in>S. (F (x, False))^2) )
                   + sqrt ( (\<Sum> x\<in>S. (G (x, True))^2)+(\<Sum> x\<in>S. (G (x, False))^2) )\<close>
    by (simp add: x1 x2 x3 x4) 
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
    using cmod_def by simp
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
   \<le> sqrt (\<Sum> x\<in>S. (cmod (f x - g x))^2) + sqrt (\<Sum> x\<in>S. (cmod (g x))^2)\<close>
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
  assumes a1: \<open>\<And>\<epsilon>. \<epsilon>>0 \<Longrightarrow> \<exists>N::nat. \<forall>m \<ge> N. \<forall>n \<ge> N. \<forall>S::'a set. 
    finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2) \<le> \<epsilon>\<close>
    and a2: \<open>\<And>k::nat. has_ell2_norm (a k)\<close>    
  shows \<open>\<exists> M::real. \<forall> m. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close>
proof-
  from  a1
  have  \<open>\<exists>N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. 
      finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> (1::real)\<close>
    by auto
  then obtain N where
    N_def: \<open>\<And>m n S. m \<ge> N \<Longrightarrow> n \<ge> N \<Longrightarrow> finite S
       \<Longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2) \<le> (1::real)\<close>
    by blast
  hence \<open>\<And>m S. m \<ge> N \<Longrightarrow> finite S \<Longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> (1::real)\<close>
    by blast

  have  \<open>\<exists> K. \<forall> m. \<forall> S::'a set. m < N \<longrightarrow> (finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K)\<close>
  proof(cases \<open>N = 0\<close>)
    case True
    thus ?thesis by blast
  next
    case False    
    have \<open>\<exists>M. \<forall> S:: 'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a k) x))^2) \<le> M\<close>
      for k
      using has_ell2_norm_explicit a2 by blast
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
      using \<open>\<And>k. \<exists>M. \<forall>S. finite S \<longrightarrow> (\<Sum>x\<in>S. (cmod (a k x))\<^sup>2) \<le> M\<close> by auto  
    have  \<open>finite S \<Longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) + sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2)\<close>
      for m ::nat and S::\<open>'a set\<close>
      by (simp add: triangIneq_ell2InsideMinus)
    have  \<open>m < N \<Longrightarrow> finite S \<Longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> sqrt C + sqrt D\<close>
      for m::nat and S::\<open>'a set\<close>
    proof- 
      assume \<open>m < N\<close> and \<open>finite S\<close>
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
    using \<open>\<And>m S. \<lbrakk>N \<le> m; finite S\<rbrakk> \<Longrightarrow> (\<Sum>x\<in>S. (cmod (a m x - a N x))\<^sup>2) \<le> 1\<close> by blast
  ultimately have \<open>\<exists> K. \<forall> m. \<forall> S::'a set. (m < N \<or> m \<ge> N) \<longrightarrow> (finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K)\<close>
    by smt
  moreover have \<open>(m < N \<or> m \<ge> N)\<close>
    for m :: nat
    by auto
  ultimately have
    \<open>\<exists> K. \<forall> m. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K\<close>
    by simp
  hence \<open>\<exists>K. \<forall>m. \<forall>S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K\<close>
    by (meson real_sqrt_le_iff) 
  then obtain K where 
    K_def: \<open>\<And> m S. finite S \<Longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K\<close>
    by auto
  have \<open>finite S \<Longrightarrow>  sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2) + sqrt (\<Sum> x\<in>S. (cmod ((a n) x))^2)\<close>
    for m n :: nat and S::\<open>'a set\<close>
    by (simp add: triangIneq_ell2Minus) 
  hence \<open>finite S \<Longrightarrow>  sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) + sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2)\<close>
    for m :: nat and S::\<open>'a set\<close>
    by blast
  have \<open>\<exists> M. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> M\<close>
    using \<open>\<And> k::nat. has_ell2_norm (a k)\<close>   
    unfolding has_ell2_norm_def
    by (metis assms(2) has_ell2_norm_explicit real_sqrt_le_iff)
  then obtain M where M_def: \<open>\<And>S::'a set. finite S \<Longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> M\<close>
    by blast
  have \<open>sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> K + M\<close>
    if a1: \<open>finite S\<close>
    for S::\<open>'a set\<close> and m::nat
  proof-
    have \<open>sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) + sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2)\<close>
      using a1  \<open>\<And> S::'a set. \<And>m::nat.  finite S \<Longrightarrow>  sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) + sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2)\<close>
      by blast
    moreover have \<open>sqrt (\<Sum> x\<in>S. (cmod ((a N) x))^2) \<le> M\<close>
      using M_def \<open>finite  S\<close>
      by blast
    ultimately have \<open>sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) + M\<close>
      by simp
    moreover have \<open>sqrt (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a N) x) ) )^2) \<le> K\<close>
      by (simp add: K_def \<open>finite S\<close>) 
    ultimately show ?thesis
      by linarith 
  qed
  hence \<open>(\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> (K + M)^2\<close>
    if "finite S"
    for S::\<open>'a set\<close> and m::nat
    using that \<open>\<And>m S. finite S \<Longrightarrow> sqrt (\<Sum>x\<in>S. (cmod (a m x))\<^sup>2) \<le> K + M\<close> sqrt_le_D by blast
  thus ?thesis
    by blast 
qed                                                                     


lemma convergence_pointwise_ell2_norm_exists:
  fixes a :: \<open>nat \<Rightarrow> ('a \<Rightarrow> complex)\<close> and l :: \<open>'a \<Rightarrow> complex\<close>
  assumes a1: \<open>a \<midarrow>pointwise\<rightarrow> l\<close> and a2: \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> 
    and a3: \<open>\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists>N. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S 
  \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
  shows \<open>has_ell2_norm l\<close>
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
    hence \<open>\<forall>\<epsilon>::real. \<forall>m::nat. 
                    \<epsilon> > 0 \<and> m \<ge> NN x \<epsilon> \<longrightarrow> (cmod (l x - (a m) x)) < \<epsilon>\<close>
      using   \<open>\<forall> x::'a. \<forall> \<epsilon>::real. \<forall> m::nat. 
                    \<epsilon> > 0 \<and> m \<ge> NN x \<epsilon> \<longrightarrow> (cmod (l x - (a m) x)) < \<epsilon>\<close>
      by blast
    hence \<open>\<forall>m::nat. 
                     1/(card S) > 0 \<and> m \<ge> NN x (1/(card S)) \<longrightarrow> (cmod (l x - (a m) x)) < 1/(card S)\<close>
      by blast
    hence y1: \<open>\<forall>m::nat. 
                      m \<ge> NN x (1/(card S)) \<longrightarrow> (cmod (l x - (a m) x)) < 1/(card S)\<close>
      using \<open>S \<noteq> {}\<close> \<open>finite S\<close> card_0_eq by auto

    from \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow> NS S = Sup {NN x (1/(card S))| x. x \<in> S}\<close>
    have \<open>NS S = Sup {NN x (1/(card S))| x. x \<in> S}\<close>
      using \<open>S \<noteq> {}\<close> \<open>finite S\<close> by auto   
    hence \<open>NS S \<ge> NN x (1/(card S))\<close>
      using \<open>x \<in> S\<close> \<open>{NN x (1/(card S))| x. x \<in> S} \<noteq> {}\<close>
        \<open>finite {NN x (1/(card S))| x. x \<in> S}\<close>
        le_cSup_finite by auto
    hence y2: \<open>NS S \<ge> NN x (1/(card S))\<close>
      by blast
    have  \<open>(cmod (l x - (a (NS S)) x)) < 1/(card S)\<close>
      using y1 y2
      by simp
    thus ?thesis by blast
  qed
  hence  \<open>\<forall> S::'a set.  finite S \<and> S \<noteq> {} \<longrightarrow> 
             (\<forall> x \<in> S. (cmod (l x - (a (NS S)) x)) < 1/(card S) )\<close>
    by blast
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
    by (metis (no_types, lifting) mult_of_nat_commute power_one_over real_divide_square_eq 
        semiring_normalization_rules(29) times_divide_eq_right)
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
  hence \<open>\<forall> S::'a set. finite S \<and> S \<noteq> {} \<longrightarrow>
            (\<Sum> x \<in> S. (cmod (l x - (a (NS S)) x))^2) < (1::real)\<close>
    by blast
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
  hence \<open>\<exists> M::real. \<forall> S::'a set. \<exists> m. M\<ge>0 
    \<and> ( finite' S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M )\<close> 
    by blast
  hence \<open>\<exists> M::real. \<forall> S::'a set. \<exists> m. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a m) x))^2) \<le> M\<close>
    by (smt real_sqrt_zero sum.empty)
  then obtain m::\<open>'a set \<Rightarrow> nat\<close> and U::real where 
    \<open>\<forall> S::'a set.  finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod (l x - (a (m S)) x))^2) \<le> U\<close>
    by metis
  have \<open>\<exists> M::real. \<forall> m. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close>
    using  \<open>\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
      \<open>\<forall> k::nat. has_ell2_norm (a k)\<close> CauchyImplies_ell2Cblinfun
    by blast
  hence \<open>\<exists> M::real. \<forall> m. \<forall> S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x\<in>S. (cmod ((a m) x))^2) \<le> M\<close>
    by (meson real_sqrt_le_iff) 
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
  thus ?thesis using has_ell2_norm_explicit by auto 
qed



lemma has_ell2_norm_diff: 
  fixes a b :: \<open>'a \<Rightarrow> complex\<close>
  assumes a1: "has_ell2_norm a" and a2: "has_ell2_norm b"
  shows "has_ell2_norm (a - b)"
proof-
  have \<open>has_ell2_norm (\<lambda> x. (-1::complex) * b x)\<close>
    using a2 ell2_norm_smult
    by blast 
  hence \<open>has_ell2_norm (\<lambda> x. - b x)\<close>
    by simp
  hence \<open>has_ell2_norm (- b)\<close>
    by (metis Rep_ell2 Rep_ell2_cases \<open>has_ell2_norm b\<close> mem_Collect_eq uminus_ell2.rep_eq)
  hence \<open>has_ell2_norm (\<lambda> x. a x + (- b) x)\<close>
    using a1 ell2_norm_triangle
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
  assumes a1: \<open>a \<midarrow>pointwise\<rightarrow> l\<close> and a2: \<open>\<And>k::nat. has_ell2_norm (a k)\<close>
    and a3: \<open>\<And>\<epsilon>. \<epsilon> > 0 \<Longrightarrow> \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S
               \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2) \<le> \<epsilon>\<close>
  shows \<open>( \<lambda> k. ell2_norm ( (a k) - l ) ) \<longlonglongrightarrow> 0\<close>
proof-
  have z1: \<open>bdd_above (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite)\<close>
    for k::nat
  proof-
    have \<open>has_ell2_norm (a k)\<close>
      by (simp add: a2)
    moreover have \<open>has_ell2_norm l\<close>
      using convergence_pointwise_ell2_norm_exists
        \<open>a \<midarrow>pointwise\<rightarrow> l\<close> a2 a3
      by blast
    ultimately have \<open>has_ell2_norm ((a k) - l)\<close>
      using has_ell2_norm_diff
      by auto 
    thus ?thesis unfolding has_ell2_norm_def
      by auto     
  qed 
  have z2: \<open>\<exists>N::nat. \<forall>k \<ge> N. \<forall>S::'a set. finite S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) \<le> \<epsilon>\<close>
    if \<open>\<epsilon> > 0\<close>
    for \<epsilon> :: real
  proof-
    have \<open>\<exists> M::nat. \<forall> n \<ge> M.
           finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
      if \<open>\<epsilon> > 0\<close>
      for \<epsilon>::real and S::"'a set"
    proof-
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
          have \<open>sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>/(sqrt (card S))\<close>
            if p1: \<open>n \<ge> NS S \<epsilon>\<close> and p2: \<open>finite' S\<close>
            for n
          proof- 
            have \<open>{NN x (\<epsilon>/(card S))| x. x \<in> S} \<noteq> {}\<close>
              by (simp add: p2)              
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
            hence \<open>\<forall>x\<in>S. \<forall>n\<ge>NS S \<epsilon>. cmod ( ((a n) x) - (l x) ) < \<epsilon>/(card S)\<close>
            proof-
              have \<open>cmod ( ((a n) x) - (l x) ) < \<epsilon>/(card S)\<close>
                if r1: \<open>x \<in> S\<close> and r2: \<open>n \<ge> NS S \<epsilon>\<close>
                for x n
              proof-
                have \<open>n \<ge> NN x (\<epsilon>/(card S))\<close>
                  using r2 \<open>{NN x (\<epsilon>/(card S))| x. x \<in> S} \<noteq> {}\<close>
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
            hence \<open>sqrt (\<Sum> x \<in> S. (cmod ( ((a n) x) - (l x) ))^2) < \<epsilon>/ (sqrt (card S))\<close>
              if r: \<open>n \<ge> NS S \<epsilon>\<close>
              for n
            proof-
              have \<open>x\<in>S \<Longrightarrow> (cmod ( ((a n) x) - (l x) ))^2 < (\<epsilon>/(card S))^2\<close>
                for x
                by (simp add: r \<open>\<forall>n\<ge>NS S \<epsilon>. \<forall>x\<in>S. (cmod (a n x - l x))\<^sup>2 < (\<epsilon> / real (card S))\<^sup>2\<close>)
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
          hence \<open>sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
            if \<open>n \<ge> NS S \<epsilon>\<close> and \<open>finite' S\<close>
            for n
          proof-
            have b1: \<open>card S \<ge> 1\<close> 
              using \<open>finite' S\<close>
              by (simp add: leI)
            have b2:\<open>sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>/(sqrt (card S))\<close>
              using \<open>\<And>n. \<lbrakk>NS S \<epsilon> \<le> n; finite' S\<rbrakk> \<Longrightarrow> sqrt (\<Sum>x\<in>S. (cmod ((a n - l) x))\<^sup>2) 
                    < \<epsilon> / sqrt (real (card S))\<close> that(1) that(2) by auto              
            have b3:\<open>sqrt (card S) \<ge> 1\<close>
              using b1 by auto
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
              using \<open>sqrt (\<Sum>x\<in>S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon> / sqrt (real (card S))\<close> 
              by force
          qed
          thus ?thesis
            by blast 
        qed  
        thus ?thesis by blast
      qed
      moreover have \<open>\<epsilon>/2 > 0\<close> using \<open>\<epsilon> > 0\<close> 
        by simp
      hence \<open>\<forall> S::'a set. \<exists> M::nat. \<forall> n \<ge> M.
         finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>/2\<close>
        using calculation by blast 
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
      using \<open>0 < (\<epsilon> / 4)\<^sup>2\<close> a3 by blast           
    hence \<open>\<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2) < (\<epsilon>/2)^2\<close>
      using \<open>(\<epsilon>/4)^2 < (\<epsilon>/2)^2\<close> by smt
    hence \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite' S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a k) - (a n)) x ) )^2) < (\<epsilon>/2)^2\<close>
      by auto
    hence  \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite' S
     \<longrightarrow> sqrt (\<Sum> x\<in>S. ( cmod ( ((a k) - (a n)) x ) )^2) < sqrt ((\<epsilon>/2)^2)\<close>
      using real_sqrt_less_iff by presburger 
    moreover have \<open> sqrt ((\<epsilon>/2)^2) = \<epsilon>/2\<close>
      using \<open>\<epsilon>/2 > 0\<close> by simp      
    ultimately have \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set.
        finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) < \<epsilon>/2\<close>
      by simp
    have  \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<forall> n. 
        n \<ge> N \<and> finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) < \<epsilon>/2\<close>
      using \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. 
        finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) < \<epsilon>/2\<close>
      by blast
    hence \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> M::nat. \<forall> n. 
       n \<ge> N \<and> n \<ge> M \<and>  finite' S \<longrightarrow> 
      sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>/2 + \<epsilon>/2\<close>
      using \<open>\<forall> S::'a set. \<exists> M::nat. \<forall> n \<ge> M.
         finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>/2\<close>
      by smt
    hence  \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> M::nat. \<forall> n. 
       n \<ge> N \<and> n \<ge> M \<and>  finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
      using add_le_same_cancel2 by auto
    have \<open>n \<ge> Sup {N, M} \<Longrightarrow> n \<ge> N \<and> n \<ge> M\<close>
      for n N M :: nat
      by (simp add: cSup_le_iff)
    hence \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> M::nat. \<forall> n::nat. 
       n \<ge> Sup {N, M} \<and>  finite' S 
        \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
      by (metis \<open>\<exists>N. \<forall>k\<ge>N. \<forall>S. \<exists>M. \<forall>n. N \<le> n \<and> M \<le> n \<and> finite' S \<longrightarrow>
         sqrt (\<Sum>x\<in>S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum>x\<in>S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>)         
    hence \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> K::nat. \<forall> n. 
       n \<ge> K \<and> finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
      by metis
    hence \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> K::nat. \<forall> n. 
       n \<ge> K \<and> finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2)+ sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
      by auto
    hence \<open>\<exists> N::nat. \<forall>k\<ge>N. \<forall>S::'a set. \<exists>M. \<forall>n \<ge> M. 
        finite' S \<longrightarrow> 
          sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
      by meson 
    moreover have \<open> 
        sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) \<le> 
          sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2)\<close>
      if \<open>finite' S\<close>
      for k n :: nat and S::\<open>'a set\<close>
    proof-
      have \<open>finite S\<close> 
        using that
        by simp
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
    obtain N where
      \<open>\<forall> k \<ge> N. \<forall> S::'a set. \<exists> M. \<forall> n \<ge> M. finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
      using \<open>\<exists> N::nat. \<forall> k \<ge> N. \<forall> S::'a set. \<exists> M. \<forall> n \<ge> M. finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - a n) x))\<^sup>2) + sqrt (\<Sum> x \<in> S. (cmod ((a n - l) x))\<^sup>2) < \<epsilon>\<close>
      by blast
    have \<open>sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) < \<epsilon>\<close>
      if "finite' S" and \<open>k \<ge> N\<close>
      for k::nat and S::"'a set"
    proof-
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
      thus ?thesis 
        by blast
    qed
    hence \<open>\<exists>N::nat. \<forall> k \<ge> N. \<forall> S::'a set. finite' S \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) < \<epsilon>\<close>
      by blast
    hence \<open>\<exists>N::nat. \<forall> k \<ge> N. \<forall> S::'a set. finite' S 
          \<longrightarrow> sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2) \<le> \<epsilon>\<close>
      by smt
    thus ?thesis
      by (metis (mono_tags) \<open>0 < \<epsilon>\<close> assms(3) real_sqrt_zero sum.empty) 
  qed  
  have z3: \<open>\<exists>N::nat. \<forall>k\<ge>N. Sup { sqrt (\<Sum> x \<in> S. (cmod ((a k - l) x))\<^sup>2)  | S::'a set. finite S } \<le> \<epsilon>\<close>
    if e: \<open>\<epsilon> > 0\<close>
    for \<epsilon> :: real
  proof-
    have \<open>\<exists>N::nat. \<forall>k\<ge>N. \<forall>S::'a set. finite S \<longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  \<le> \<epsilon>\<close>
      using e z2 by blast  
    then obtain N where 
      \<open>\<And>k S. k \<ge> N \<Longrightarrow> finite (S::'a set) \<Longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2) \<le> \<epsilon>\<close>
      by blast
    have \<open>{ sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } \<noteq> {}\<close>
      for k::nat
      by blast
    moreover have \<open>bdd_above { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S }\<close>
      for k::nat
    proof-       
      have \<open>bdd_above { (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S }\<close>
        using setcompr_eq_image
        by (metis z1) 
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
      using \<open>\<And>k S. \<lbrakk>N \<le> k; finite S\<rbrakk> \<Longrightarrow> sqrt (\<Sum>i\<in>S. (cmod ((a k - l) i))\<^sup>2) \<le> \<epsilon>\<close> by blast
    thus ?thesis using  \<open>\<And> k. (Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } \<le> \<epsilon>) 
\<longleftrightarrow> (\<forall> x \<in> { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S }. x \<le> \<epsilon>)\<close>
      by blast
  qed 
  hence z4: \<open>\<exists>N::nat. \<forall>k\<ge>N. 
      Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } \<le> \<epsilon>\<close>
    if "\<epsilon> > 0"
    for \<epsilon>
    using that by blast    
  have \<open>\<exists>N. \<forall>k\<ge>N. Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } \<le> \<epsilon>/2\<close>
    if "\<epsilon> > 0"
    for \<epsilon>
    using that half_gt_zero_iff z4 by blast 
  moreover have \<open>\<forall>\<epsilon> > (0::real). \<epsilon> / 2 < \<epsilon>\<close>
    by simp
  ultimately have 
    \<open>\<exists>N. \<forall>k\<ge>N. Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S } < \<epsilon>\<close>
    if "\<epsilon> > 0"
    for \<epsilon>
    using that
    by fastforce
  moreover have 
    \<open>ell2_norm (a k - l) = Sup { sqrt (\<Sum> i \<in> S. (cmod ((a k - l) i))\<^sup>2)  | S::'a set. finite S }\<close>
    for k::nat
  proof-
    have \<open>has_ell2_norm l\<close>
      using convergence_pointwise_ell2_norm_exists
        \<open>a \<midarrow>pointwise\<rightarrow> l\<close> a2 a3
      by blast
    hence \<open>has_ell2_norm (a k - l)\<close>
      using  a2 has_ell2_norm_diff
      by blast
    thus ?thesis using ellnorm_as_sup_set
      by blast 
  qed  
  ultimately have z5: \<open>\<exists> N::nat. \<forall> k \<ge> N. ell2_norm (a k - l) < \<epsilon>\<close>
    if "\<epsilon> > 0"
    for \<epsilon>
    using that
    by simp
  hence \<open>\<exists>N::nat. \<forall>k \<ge> N. (sqrt (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))) < \<epsilon>\<close>
    if "\<epsilon> > 0"
    for \<epsilon>
    using that ell2_norm_def by metis
  obtain x where
    \<open>x \<in> (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite)\<close>
  for k::nat
    by (metis finite.emptyI image_iff mem_Collect_eq sum.empty)
  obtain S k where \<open>x = sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) S\<close>
    using image_iff \<open>\<And>k. x \<in> sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite\<close> by fastforce
  have  \<open>\<forall> i\<in>S. (cmod ((a k - l) i))\<^sup>2 \<ge> 0\<close>
    by simp
  hence t1: \<open>(0::real) \<le> x\<close>
    by (simp add: \<open>x = (\<Sum>i\<in>S. (cmod ((a k - l) i))\<^sup>2)\<close> sum_nonneg)     
  hence \<open>0 \<le> (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))\<close>
    for k::nat 
    using \<open>\<And> k::nat. bdd_above (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite)\<close>
      cSup_upper2 \<open>\<And>k. x \<in> sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite\<close> by blast
  hence \<open>\<exists>N. \<forall>k\<ge>N. \<bar> (sqrt (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))) \<bar> < \<epsilon>\<close>
    if "\<epsilon>>0"
    for \<epsilon>
    using that NthRoot.real_sqrt_ge_zero
    by (metis z5 ell2_norm_def real_sqrt_abs real_sqrt_pow2)        
  hence \<open>\<exists>N. \<forall>k\<ge>N. dist (sqrt (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))) 0 < \<epsilon>\<close>
    if "\<epsilon> > 0"
    for \<epsilon>
    using that
    by simp
  hence \<open>(\<lambda>k. sqrt (Sup (sum (\<lambda>i. (cmod ((a k - l) i))\<^sup>2) ` Collect finite))) \<longlonglongrightarrow> 0\<close>
    by (simp add: metric_LIMSEQ_I)
  thus ?thesis unfolding ell2_norm_def by blast
qed


lemma ell2_Cauchy_pointwiseConverges:
  fixes a :: \<open>nat \<Rightarrow> ('a \<Rightarrow> complex)\<close>
  assumes a1: \<open>\<And>k. has_ell2_norm (a k)\<close> 
      and a2: \<open>\<And>\<epsilon>. \<epsilon>>0 \<Longrightarrow> \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>S. finite S 
      \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( a m x - a n x ) )^2)  \<le> \<epsilon>\<close>
  shows \<open>\<exists> l. (a \<midarrow>pointwise\<rightarrow> l)\<close>
proof-
  have \<open>\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.  cmod ( a m x - a n x ) \<le> \<epsilon>\<close>
    if e1: \<open>\<epsilon> > 0\<close>
    for \<epsilon> and x::'a 
  proof-
    have \<open>\<epsilon>^2 > 0\<close>
      using e1
      by simp
    hence \<open>\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>S. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( a m x - a n x ) )^2)  \<le> \<epsilon>^2\<close>
      by (simp add: a2)
    then obtain N
      where \<open>\<forall>m\<ge>N. \<forall>n \<ge>N. \<forall>S. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( a m x - a n x ) )^2)  \<le> \<epsilon>^2\<close>
      by blast
    have \<open>cmod ( a m x - a n x ) \<le> \<epsilon>\<close>
      if r1: \<open>m \<ge> N\<close> and r2: \<open>n \<ge> N\<close>
      for m n
    proof- 
      have "(\<Sum> x\<in>S. ( cmod ( a m x - a n x ) )^2)  \<le> \<epsilon>^2"
        if "finite S"
        for S
        using that r1 r2 \<open>\<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>^2\<close>
        by blast
      moreover have \<open>finite {x}\<close>
        by auto
      ultimately have \<open>(\<Sum> t\<in>{x}. ( cmod ( a m t - a n t ) )^2) \<le> \<epsilon>^2\<close>
        by blast
      hence \<open>( cmod ( a m x - a n x ) )^2  \<le> \<epsilon>^2\<close>        
        by simp
      moreover have \<open>cmod ( a m x - a n x ) \<ge> 0\<close>
        by simp
      ultimately have \<open>( cmod ( a m x - a n x ) )  \<le> \<epsilon>\<close>        
        using \<open>\<epsilon> > 0\<close>
        using power2_le_imp_le by fastforce   
      thus ?thesis by blast
    qed 
    thus ?thesis by blast
  qed 
  hence \<open>\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.  cmod ( (\<lambda> k. a k x) m - (\<lambda> k. a k x) n ) \<le> \<epsilon>\<close>
    if "\<epsilon>>0"
    for \<epsilon> and x
    using that
    by blast
  hence "\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.  cmod ( (\<lambda> k. a k x) m - (\<lambda> k. a k x) n ) \<le> \<epsilon>"
    if "\<epsilon>>0"
    for x::'a and \<epsilon>
    using that
    by blast
  hence \<open>\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.  cmod ( (\<lambda> k. a k x) m - (\<lambda> k. a k x) n ) < \<epsilon>\<close>
    if s1: "\<epsilon>>0"
    for \<epsilon> and x::'a 
  proof-
    have \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) \<le> \<epsilon>/2\<close>
      using half_gt_zero
        \<open>\<And>x \<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. cmod (a m x - a n x) \<le> \<epsilon>\<close> by blast 
      have \<open>\<exists>N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) \<le> \<epsilon>/2\<close>
        using s1 \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N.  cmod ( (\<lambda> k. (a k) x) m - (\<lambda> k. (a k) x) n ) \<le> \<epsilon>/2\<close>
        by blast
      moreover have \<open>\<epsilon>/2 < \<epsilon>\<close>
        using \<open>\<epsilon> > 0\<close>
        by simp
      ultimately have \<open>\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.  cmod ( (\<lambda> k. a k x) m - (\<lambda> k. a k x) n ) < \<epsilon>\<close>
        by fastforce
    thus ?thesis 
      by blast
  qed
  hence \<open>\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N.  dist ((\<lambda>k. a k x) m) ((\<lambda>k. a k x) n) < \<epsilon>\<close>
    if "\<epsilon>>0"
    for \<epsilon> and x
    by (simp add: that dist_norm)  
  hence \<open>Cauchy (\<lambda> k. (a k) x)\<close>
    for x::'a
    using Cauchy_altdef2 by fastforce     
  hence \<open>\<exists>r. (\<lambda> n. a n x ) \<longlonglongrightarrow> r\<close>
    for x::'a
    by (simp add: convergent_eq_Cauchy) 
  hence \<open>\<exists>l. \<forall>x. (\<lambda> n. (a n) x) \<longlonglongrightarrow> l x\<close>
    by metis                                        
  thus ?thesis 
    unfolding pointwise_convergent_to_def
    by blast    
qed


lemma completeness_ell2:
  fixes a :: \<open>nat \<Rightarrow> ('a \<Rightarrow> complex)\<close>
  assumes a1: \<open>\<And>k. has_ell2_norm (a k)\<close> and
    a2: \<open>\<And>\<epsilon>. \<epsilon>>0 \<Longrightarrow> \<exists>N.\<forall>m\<ge>N.\<forall>n\<ge>N. ell2_norm (\<lambda>x. a m x - a n x) < \<epsilon>\<close>
  shows "\<exists>l. has_ell2_norm l \<and> (\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a n x - l x) < \<epsilon>)"
proof-
  have \<open>\<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall> S. finite S 
  \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( a m x - a n x ) )^2)  \<le> \<epsilon>\<close>
    if s1: "\<epsilon> > 0"
      for \<epsilon>::real
    proof-
      have \<open>sqrt \<epsilon> > 0\<close> using s1 
        by simp
      then obtain N where \<open>\<forall>m\<ge>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a m x - a n x) < sqrt \<epsilon>\<close>
        using a2 by blast        
      hence  \<open>\<forall>m\<ge>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a m x - a n x) \<le> sqrt \<epsilon>\<close>
        by fastforce
      have  \<open>(\<Sum>x\<in>S. ( cmod ( a m x - a n x ) )^2)  \<le> \<epsilon>\<close>
        if \<open>m \<ge> N\<close> and \<open>n \<ge> N\<close> and "finite S"
        for m n S
      proof-
        have \<open>ell2_norm (\<lambda>x. a m x - a n x) \<le> sqrt \<epsilon>\<close>
          using \<open>\<forall>m\<ge>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a m x - a n x) \<le> sqrt \<epsilon>\<close>
            \<open>m \<ge> N\<close>  \<open>n \<ge> N\<close>
          by blast
        have \<open>has_ell2_norm (a m)\<close>
          by (simp add: assms(1))          
        moreover have \<open>has_ell2_norm (a n)\<close>
          by (simp add: assms(1))
        ultimately have \<open>has_ell2_norm (a m - a n)\<close>
          by (simp add: has_ell2_norm_diff)
        hence \<open>ell2_norm (a m - a n) = Sup { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S.
                                             finite S }\<close>
          using ellnorm_as_sup_set
          by blast
        have \<open>{ sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S. finite S } \<noteq> {}\<close>
          by blast
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
        have \<open>M \<ge> 0\<close>
          for S::\<open>'a set\<close>
          using  \<open>\<And> S. finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> M\<close>            
          by force
        have  \<open>finite S \<Longrightarrow> sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> sqrt M\<close>
          for S::\<open>'a set\<close>
          using  \<open>M \<ge> 0\<close>  \<open>\<And> S. finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> M \<close>
            \<open>\<And> S. finite S \<Longrightarrow> (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<ge> 0\<close>
          by simp
        hence \<open>bdd_above { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S}\<close>
          by (smt bdd_aboveI mem_Collect_eq)   
        have \<open>(\<lambda> x. a m x - a n x) = a m - a n\<close>
          by auto
        hence \<open>ell2_norm (a m - a n) \<le> sqrt \<epsilon>\<close> 
          using  \<open>ell2_norm (\<lambda> x. a m x - a n x) \<le> sqrt \<epsilon>\<close> 
          by simp
        hence \<open>Sup { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S } \<le> sqrt \<epsilon>\<close>
          using  \<open>ell2_norm (a m - a n) \<le> sqrt \<epsilon>\<close>  \<open>ell2_norm (a m - a n) = Sup { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. finite S }\<close>
          by simp
        moreover have \<open>sqrt (\<Sum> i \<in> S. 
          (cmod ((a m - a n) i))\<^sup>2) \<le> Sup { sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  | S::'a set. 
            finite S }\<close>
          if fs: \<open>finite S\<close>
          for S::\<open>'a set\<close>
        proof-
          have \<open>sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)\<in>{ sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2)  
                  | S::'a set. finite S }\<close>
            using fs by blast
          thus ?thesis
            by (metis (no_types, lifting) \<open>bdd_above {sqrt (\<Sum>i\<in>S. (cmod ((a m - a n) i))\<^sup>2) 
                |S. finite S}\<close> cSup_upper)  
        qed 
        ultimately have \<open>sqrt (\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> sqrt \<epsilon>\<close>
          for S :: \<open>'a set \<close>
          by (smt \<open>0 < \<epsilon>\<close> real_sqrt_le_mono sum.infinite)
        hence  \<open>(\<Sum> i \<in> S. (cmod ((a m - a n) i))\<^sup>2) \<le> \<epsilon>\<close>
          for S :: \<open>'a set \<close>
          by simp
        thus ?thesis by auto 
      qed
      thus ?thesis
        by blast 
    qed
    hence  \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>S. finite S
         \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
      by blast
  have  \<open>\<exists> l. a \<midarrow>pointwise\<rightarrow> l\<close>
    using ell2_Cauchy_pointwiseConverges
    by (simp add: ell2_Cauchy_pointwiseConverges \<open>\<And>\<epsilon>. 0 < \<epsilon> \<Longrightarrow> \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>S. finite S
   \<longrightarrow> (\<Sum>x\<in>S. (cmod (a m x - a n x))\<^sup>2) \<le> \<epsilon>\<close> a1)
  then obtain l :: \<open>'a \<Rightarrow> complex\<close> where \<open>a \<midarrow>pointwise\<rightarrow> l\<close>
    by blast
  have a1: \<open>has_ell2_norm l\<close> using convergence_pointwise_ell2_norm_exists 
    using  \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>m\<ge>N. \<forall>n\<ge>N. \<forall>S::'a set. finite S
       \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( a m x - a n x ) )^2)  \<le> \<epsilon>\<close>
      \<open>a \<midarrow>pointwise\<rightarrow> l\<close>  \<open>\<And>k. has_ell2_norm (a k)\<close>
    by blast
  have  \<open>(\<lambda>k. ell2_norm (a k - l) ) \<longlonglongrightarrow> 0\<close>
    using convergence_pointwise_to_ell2_same_limit  
        \<open>\<forall> \<epsilon> > 0. \<exists> N::nat. \<forall> m \<ge> N. \<forall> n \<ge> N. \<forall> S::'a set. finite S \<longrightarrow> (\<Sum> x\<in>S. ( cmod ( ((a m) x) - ((a n) x) ) )^2)  \<le> \<epsilon>\<close>
        \<open>a \<midarrow>pointwise\<rightarrow> l\<close>  \<open>\<And>k::nat. has_ell2_norm (a k)\<close>
      by blast
    hence  \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. dist ( ell2_norm ( (a k) - l ) ) 0 < \<epsilon>\<close>
      using metric_LIMSEQ_D by blast
    hence  \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N.  \<bar>ell2_norm ( (a k) - l ) \<bar>  < \<epsilon>\<close>
      by simp
    hence  \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall> k \<ge> N.  ell2_norm ( (a k) - l )   < \<epsilon>\<close>
      by (metis diff_zero dist_commute dist_real_def lemma_interval_lt nice_ordered_field_class.linordered_field_no_lb)
    hence \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>k\<ge>N. ell2_norm (\<lambda>x. (a k - l) x) < \<epsilon>\<close>
      by smt
    hence a2: \<open>\<forall>\<epsilon>>0. \<exists>N. \<forall>n\<ge>N. ell2_norm (\<lambda>x. a n x - l x) < \<epsilon>\<close> 
      by simp 
    show ?thesis 
      using a1 a2 by blast
qed                                                    

instantiation ell2 :: (type) chilbert_space
begin
instance
proof
  fix X :: "nat \<Rightarrow> 'a ell2"
  have x:"\<And>X::nat \<Rightarrow> 'a \<Rightarrow> complex.
       \<forall>x. has_ell2_norm (X x) \<Longrightarrow>
       \<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. ell2_norm (\<lambda>x. X m x - X n x) < e \<Longrightarrow>
       \<exists>l. has_ell2_norm l \<and>
          (\<forall>r>0. \<exists>no. \<forall>n\<ge>no. ell2_norm (\<lambda>x::'a. X n x - l x) < r)"
  proof (rule completeness_ell2)
    show "has_ell2_norm (\<lambda>x. X k x)"
      if "\<forall>x::nat. has_ell2_norm (X x)"
        and "\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. ell2_norm (\<lambda>x. X m x - X n x) < e"
      for X :: "nat \<Rightarrow> 'a \<Rightarrow> complex"
        and k :: nat
      using that
      by blast 
    show "\<exists>no. \<forall>m\<ge>no. \<forall>n\<ge>no. ell2_norm (\<lambda>x. X m x - X n x) < r"
      if "\<forall>x. has_ell2_norm (X x)"
        and "\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. ell2_norm (\<lambda>x. X m x - X n x) < e"
        and "0 < r"
      for X :: "nat \<Rightarrow> 'a \<Rightarrow> complex"
        and r :: real
      using that
      by blast 
  qed
  assume cauchy: "Cauchy X"
  hence "\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (X m - X n) < e"
    unfolding Cauchy_def dist_norm.
  hence "\<exists>l. \<forall>r>0. \<exists>no. \<forall>n\<ge>no. norm (X n - l) < r"
    apply transfer
    using x
    by simp
  hence "\<exists>l. \<forall>r>0. \<exists>no. \<forall>n\<ge>no. dist (X n) l < r"
    unfolding dist_norm.    
  hence "\<exists>l. X \<longlonglongrightarrow> l"
    unfolding LIMSEQ_def.
  thus "convergent (X::nat \<Rightarrow> 'a ell2)"
    using convergent_def by blast
qed
end

abbreviation bra :: "'a \<Rightarrow> (_,complex) cblinfun" where "bra i \<equiv> vector_to_cblinfun (ket i)*" for i

lemma cinner_ket_left: \<open>\<langle>ket i, \<psi>\<rangle> = Rep_ell2 \<psi> i\<close>
  apply (transfer fixing: i)
  apply (subst infsetsum_cong_neutral[where B=\<open>{i}\<close>])
  by auto

lemma cinner_ket_right: \<open>\<langle>\<psi>, ket i\<rangle> = cnj (Rep_ell2 \<psi> i)\<close>
  apply (transfer fixing: i)
  apply (subst infsetsum_cong_neutral[where B=\<open>{i}\<close>])
  by auto

lemma ell2_ket[simp]: "norm (ket i) = 1"
proof transfer
  show "ell2_norm (\<lambda>y. if i = y then 1::complex else 0) = 1"
    for i :: 'a
    unfolding ell2_norm_def real_sqrt_eq_1_iff
  proof (rule cSUP_eq_maximum)
    show "\<exists>x\<in>Collect finite. (\<Sum>j\<in>x. (cmod (if i = j then 1 else 0))\<^sup>2) = 1"
    proof (rule_tac x = "{i}" in bexI)
      show "(\<Sum>j\<in>{i}. (cmod (if i = j then 1 else 0))\<^sup>2) = 1"
        by simp
      show "{i} \<in> Collect finite"
        by blast
    qed    

    have "(\<Sum>j\<in>x. (cmod (if i = j then 1 else 0))\<^sup>2) \<le> 1"
      if "finite x"
      for x :: "'a set"
      using that ell2_1[where F = x] by auto 
    thus "(\<Sum>j\<in>x. (cmod (if i = j then 1 else 0))\<^sup>2) \<le> 1"
      if "x \<in> Collect finite"
      for x :: "'a set"
      using that
      by blast 
  qed
qed 
  
type_synonym 'a ell2_clinear_space = "'a ell2 ccsubspace"

lemma subspace_zero_not_top[simp]: 
  "(0::'a::{complex_vector,t1_space,not_singleton} ccsubspace) \<noteq> top"
  by simp

instance ell2 :: (type) not_singleton
proof standard
  have "ket undefined \<noteq> (0::'a ell2)"
  proof transfer
    show "(\<lambda>y. if (undefined::'a) = y then 1::complex else 0) \<noteq> (\<lambda>_. 0)"
      by (meson one_neq_zero)
  qed   
  thus \<open>\<exists>x y::'a ell2. x \<noteq> y\<close>
    by blast    
qed


definition left_shift :: \<open>(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)\<close> where
  \<open>left_shift x = (\<lambda> n. x (Suc n))\<close>

lift_definition left_shift_ell2 :: \<open>nat ell2 \<Rightarrow> nat ell2\<close> is left_shift
proof-
  fix x :: "nat \<Rightarrow> complex"
  show "has_ell2_norm (left_shift x)"
    if "has_ell2_norm x"
  proof-
    define f where \<open>f n = (cmod (x n))^2\<close> for n :: nat
    define g :: \<open>nat \<Rightarrow> real\<close>  where \<open>g \<equiv> (\<lambda> n. (cmod (x (Suc n)))^2)\<close>
    have \<open>(\<lambda> n. (cmod (x n))^2) abs_summable_on UNIV\<close>
      using that has_ell2_norm_infsetsum by fastforce
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
    have \<open>norm (g n) = g n\<close>
      for n
    proof-
      have \<open>g n \<ge> 0\<close>
        unfolding g_def
        by simp 
      thus ?thesis by auto
    qed
    hence \<open>summable (\<lambda> n. norm (g n))\<close>
      by (simp add: \<open>summable g\<close>)
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

(*here*)
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


(* TODO [simp] *)
lemma ket_Kronecker_delta_eq[simp]:
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

(* TODO: remove? ket_Kronecker_delta enough I think *)
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

lemma ket_Kronecker_delta: \<open>\<langle>ket i, ket j\<rangle> = (if i=j then 1 else 0)\<close>
  by (simp add: ket_Kronecker_delta_eq ket_Kronecker_delta_neq)

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
    using pythagorean_theorem by fastforce    
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

(* TODO remove (merge into trunc_ell2_cspan) *)
lemma trunc_ell2_cspan_induct:
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


lemma trunc_ell2_cspan:
  \<open>finite S \<Longrightarrow> trunc_ell2 S x \<in> (cspan (range (ket::('a \<Rightarrow>'a ell2))))\<close>
  using trunc_ell2_cspan_induct by auto

lemma trunc_ell2_norm_sup:
  \<open>(SUP S\<in>Collect finite. (norm (trunc_ell2 S \<psi>))) = norm \<psi>\<close>
proof -
  define N where \<open>N S = sqrt (\<Sum>i\<in>S. (cmod (Rep_ell2 \<psi> i))\<^sup>2)\<close> for S
  have \<open>(SUP S\<in>Collect finite. (norm (trunc_ell2 S \<psi>))) = (SUP (S::'a set)\<in>Collect finite. N S)\<close>
    apply (rule SUP_cong)
    by (auto simp: N_def trunc_ell2_norm_explicit)
  also have \<open>\<dots> = norm \<psi>\<close>
    unfolding N_def apply transfer
    unfolding ellnorm_as_sup_set
    by (simp add: setcompr_eq_image)
  finally show ?thesis
    by -
qed

lemma trunc_ell2_norm_lim:
  \<open>((\<lambda>S. norm (trunc_ell2 S \<psi>)) \<longlongrightarrow> norm \<psi>) (finite_subsets_at_top UNIV)\<close>
proof -
  define f where \<open>f i = (cmod (Rep_ell2 \<psi> i))\<^sup>2\<close> for i

  have has: \<open>has_ell2_norm (Rep_ell2 \<psi>)\<close>
    using Rep_ell2 by blast
  then have summable: "f abs_summable_on UNIV"
    using f_def has_ell2_norm_infsetsum by fastforce
  
  have \<open>norm \<psi> = (ell2_norm (Rep_ell2 \<psi>))\<close>
    apply transfer by simp
  also have \<open>\<dots> = sqrt (infsetsum' f UNIV)\<close>
    unfolding ell2_norm_infsetsum[OF has] f_def[symmetric]
    using summable by (simp add: infsetsum_infsetsum')
  finally have norm\<psi>: \<open>norm \<psi> = sqrt (infsetsum' f UNIV)\<close>
    by -

  have norm_trunc: \<open>norm (trunc_ell2 S \<psi>) = sqrt (sum f S)\<close> if \<open>finite S\<close> for S
    using f_def that trunc_ell2_norm_explicit by fastforce

  have \<open>(sum f \<longlongrightarrow> infsetsum' f UNIV) (finite_subsets_at_top UNIV)\<close>
    by (simp add: abs_summable_infsetsum'_converges infsetsum'_tendsto summable)
  then have \<open>((\<lambda>S. sqrt (sum f S)) \<longlongrightarrow> sqrt (infsetsum' f UNIV)) (finite_subsets_at_top UNIV)\<close>
    using tendsto_real_sqrt by blast
  then show \<open>((\<lambda>S. norm (trunc_ell2 S \<psi>)) \<longlongrightarrow> norm \<psi>) (finite_subsets_at_top UNIV)\<close>
    apply (subst tendsto_cong[where g=\<open>\<lambda>S. sqrt (sum f S)\<close>])
    by (auto simp add: eventually_finite_subsets_at_top_weakI norm_trunc norm\<psi>)
qed

lemma trunc_ell2_limit:
  \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
proof -
  have \<open>((\<lambda>S. norm (trunc_ell2 S \<psi>)) \<longlongrightarrow> norm \<psi>) (finite_subsets_at_top UNIV)\<close>
    by (rule trunc_ell2_norm_lim)
  then have \<open>((\<lambda>S. (norm (trunc_ell2 S \<psi>))\<^sup>2) \<longlongrightarrow> (norm \<psi>)\<^sup>2) (finite_subsets_at_top UNIV)\<close>
    by (simp add: tendsto_power)
  then have \<open>((\<lambda>S. (norm \<psi>)\<^sup>2 - (norm (trunc_ell2 S \<psi>))\<^sup>2) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    apply (rule tendsto_diff[where a=\<open>(norm \<psi>)^2\<close> and b=\<open>(norm \<psi>)^2\<close>, simplified, rotated])
    by auto
  then have \<open>((\<lambda>S. (norm (\<psi> - trunc_ell2 S \<psi>))\<^sup>2) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    unfolding trunc_ell2_norm_diff by simp
  then have \<open>((\<lambda>S. norm (\<psi> - trunc_ell2 S \<psi>)) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    by auto
  then have \<open>((\<lambda>S. \<psi> - trunc_ell2 S \<psi>) \<longlongrightarrow> 0) (finite_subsets_at_top UNIV)\<close>
    by (rule tendsto_norm_zero_cancel)
  then show ?thesis
    apply (rule Lim_transform2[where f=\<open>\<lambda>_. \<psi>\<close>, rotated])
    by simp
qed

lemma ket_ell2_span:
  \<open>closure (cspan (range ket)) = UNIV\<close>
proof (intro set_eqI iffI UNIV_I closure_approachable[THEN iffD2] allI impI)
  fix \<psi> :: \<open>'a ell2\<close>
  fix e :: real assume \<open>e > 0\<close>
  have \<open>((\<lambda>S. trunc_ell2 S \<psi>) \<longlongrightarrow> \<psi>) (finite_subsets_at_top UNIV)\<close>
    by (rule trunc_ell2_limit)
  then obtain F where \<open>finite F\<close> and \<open>dist (trunc_ell2 F \<psi>) \<psi> < e\<close>
    apply (drule_tac tendstoD[OF _ \<open>e > 0\<close>])
    by (auto dest: simp: eventually_finite_subsets_at_top)
  moreover have \<open>trunc_ell2 F \<psi> \<in> cspan (range ket)\<close>
    using \<open>finite F\<close> trunc_ell2_cspan by blast
  ultimately show \<open>\<exists>\<phi>\<in>cspan (range ket). dist \<phi> \<psi> < e\<close>
    by auto
qed

lemma cspan_ket_finite[simp]: "cspan (range ket :: 'a::finite ell2 set) = UNIV"
  by (metis ket_ell2_span closure_finite_cspan finite_class.finite_UNIV finite_imageI)

instance ell2 :: (finite) cfinite_dim
proof
  define basis :: \<open>'a ell2 set\<close> where \<open>basis = range ket\<close>
  have \<open>finite basis\<close>
    unfolding basis_def by simp
  moreover have \<open>cspan basis = UNIV\<close>
    by (simp add: basis_def)
  ultimately show \<open>\<exists>basis::'a ell2 set. finite basis \<and> cspan basis = UNIV\<close>
    by auto
qed

instantiation ell2 :: (enum) onb_enum begin
definition "canonical_basis_ell2 = map ket Enum.enum"
(* definition "canonical_basis_length_ell2 (_::'a ell2 itself) = CARD('a)" (* TODO: [simp] *) *)
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
    apply (auto simp: canonical_basis_ell2_def enum_UNIV)
    by (smt (z3) ell2_ket f_inv_into_f is_ortho_set_def ket_Kronecker_delta_neq norm_zero)

  show "cindependent (set (canonical_basis::'a ell2 list))"
    apply (auto simp: canonical_basis_ell2_def enum_UNIV)
    by (smt (verit, best) ell2_ket f_inv_into_f is_ortho_set_def is_ortho_set_cindependent ket_Kronecker_delta_neq norm_zero)

  show "cspan (set (canonical_basis::'a ell2 list)) = UNIV"
    by (auto simp: canonical_basis_ell2_def enum_UNIV)

(*   show "canonical_basis_length (TYPE('a ell2)::'a ell2 itself) = length (canonical_basis::'a ell2 list)"
    unfolding canonical_basis_length_ell2_def canonical_basis_ell2_def
    using card_UNIV_length_enum
    by auto *)

  show "norm (x::'a ell2) = 1"
    if "(x::'a ell2) \<in> set canonical_basis"
    for x :: "'a ell2"
    using that unfolding canonical_basis_ell2_def 
    by auto
qed

end

lemma canonical_basis_length_ell2[code_unfold, simp]: "canonical_basis_length (_::'a::enum ell2 itself) = CARD('a)"
  unfolding canonical_basis_ell2_def apply simp
    using card_UNIV_length_enum by metis

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

instantiation ell2 :: (CARD_1) field begin
lift_definition divide_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a b x. a x / b x"
  by simp   
lift_definition inverse_ell2 :: "'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a x. inverse (a x)"
  by simp
instance
proof (intro_classes; transfer)
  fix a :: "'a \<Rightarrow> complex"
  assume "a \<noteq> (\<lambda>_. 0)"
  then obtain y where ay: "a y \<noteq> 0"
    by auto
  show "(\<lambda>x. inverse (a x) * a x) = (\<lambda>_. 1)"
  proof (rule ext)
    fix x
    have "x = y"
      by auto
    with ay have "a x \<noteq> 0"
      by metis
    then show "inverse (a x) * a x = 1"
      by auto
  qed
qed (auto simp add: divide_complex_def mult.commute ring_class.ring_distribs)
end

lemma equal_ket:
  fixes A B :: \<open>('a ell2, 'b::complex_normed_vector) cblinfun\<close>
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
      using ccspan.rep_eq \<open>\<And>x. x \<in> S \<Longrightarrow> cblinfun_apply A x = cblinfun_apply B x\<close> cblinfun_eq_on by blast
  qed
  hence \<open>cblinfun_apply A = cblinfun_apply B\<close>
    by blast
  thus ?thesis using cblinfun_apply_inject by auto
qed



lemma clinear_equal_ket:
  fixes f g :: \<open>'a::finite ell2 \<Rightarrow> _\<close>
  assumes \<open>clinear f\<close>
  assumes \<open>clinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
  apply (rule ext)
  apply (rule complex_vector.linear_eq_on_span[where f=f and g=g and B=\<open>range ket\<close>])
  using assms by auto

lemma antilinear_equal_ket:
  fixes f g :: \<open>'a::finite ell2 \<Rightarrow> _\<close>
  assumes \<open>antilinear f\<close>
  assumes \<open>antilinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
proof -
  have [simp]: \<open>clinear (f \<circ> from_conjugate_space)\<close>
    apply (rule antilinear_o_antilinear)
    using assms by (simp_all add: antilinear_from_conjugate_space)
  have [simp]: \<open>clinear (g \<circ> from_conjugate_space)\<close>
    apply (rule antilinear_o_antilinear)
    using assms by (simp_all add: antilinear_from_conjugate_space)
  have [simp]: \<open>cspan (to_conjugate_space ` (range ket :: 'a ell2 set)) = UNIV\<close>
    by simp
  have "f o from_conjugate_space = g o from_conjugate_space"
    apply (rule ext)
    apply (rule complex_vector.linear_eq_on_span[where f="f o from_conjugate_space" and g="g o from_conjugate_space" and B=\<open>to_conjugate_space ` range ket\<close>])
       apply (simp, simp)
    using assms(3) by (auto simp: to_conjugate_space_inverse)
  then show "f = g"
    by (smt (verit) UNIV_I from_conjugate_space_inverse surj_def surj_fun_eq to_conjugate_space_inject) 
qed


subsection \<open>Recovered theorems\<close>

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

lemma closed_csubspace_INF[simp]: "(\<And>x. x \<in> AA \<Longrightarrow> csubspace x) \<Longrightarrow> csubspace (\<Inter>AA)"
  by (simp add: complex_vector.subspace_Inter)

lemma subspace_sup_plus: "(sup :: 'a ell2_clinear_space \<Rightarrow> _ \<Rightarrow> _) = (+)"
  by simp 

lemma subspace_plus_sup: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y + z \<le> x" 
  for x y z :: "'a ell2_clinear_space"
  unfolding subspace_sup_plus[symmetric] by auto

lemma subspace_empty_Sup: "Sup {} = (0::'a ell2_clinear_space)"
  unfolding zero_ccsubspace_def by auto

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
  by (metis ket_Kronecker_delta_eq ket_Kronecker_delta_neq zero_neq_one) 

lemma Span_range_ket[simp]: "ccspan (range ket) = (top::('a ell2_clinear_space))"
proof-
  have \<open>closure (complex_vector.span (range ket)) = (UNIV::'a ell2 set)\<close>
    using Complex_L2.ket_ell2_span by blast
  thus ?thesis
    by (simp add: ccspan.abs_eq top_ccsubspace.abs_eq)
qed

lemma [simp]: "ket i \<noteq> 0"
  using ell2_ket[of i] by force

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
  thus "?enum = [a]"
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
  show "x / y = x * inverse y" for x y :: "'a ell2"
    by (simp add: divide_inverse)
  show "inverse (c *\<^sub>C 1) = inverse c *\<^sub>C (1::'a ell2)" for c :: complex
    apply transfer by auto
qed
end

lemma ket_nonzero: "(ket::'a\<Rightarrow>_) i \<noteq> 0"
  apply transfer
  by (metis zero_neq_one)


lemma cindependent_ket:
  "cindependent (range (ket::'a\<Rightarrow>_))"
proof-
  define S where "S = range (ket::'a\<Rightarrow>_)"
  have "is_ortho_set S"
    unfolding S_def is_ortho_set_def by auto
  moreover have "0 \<notin> S"
    unfolding S_def
    using ket_nonzero
    by (simp add: image_iff)
  ultimately show ?thesis
    using is_ortho_set_cindependent[where A = S] unfolding S_def 
    by blast
qed

(* TODO rename \<rightarrow> sum_butterfly_ket *)
lemma sum_butter[simp]: \<open>(\<Sum>(i::'a::finite)\<in>UNIV. butterfly (ket i) (ket i)) = idOp\<close>
  apply (rule equal_ket)
  apply (subst complex_vector.linear_sum[where f=\<open>\<lambda>y. y *\<^sub>V ket _\<close>])
  apply (auto simp add: scaleC_cblinfun.rep_eq apply_cblinfun_distr_left clinearI butterfly_def cblinfun_compose_image ket_Kronecker_delta)
  apply (subst sum.mono_neutral_cong_right[where S=\<open>{_}\<close>])
  by auto


subsection \<open>Classical operators\<close>

definition classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> 'a ell2 \<Rightarrow>\<^sub>C\<^sub>L'b ell2" where
  "classical_operator \<pi> = 
    (let f = (\<lambda>t. (case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i))
     in
      cblinfun_extension (range (ket::'a\<Rightarrow>_)) f
    )"


definition "classical_operator_exists \<pi> \<longleftrightarrow>
  cblinfun_extension_exists (range ket)
    (\<lambda>t. case \<pi> (inv ket t) of None \<Rightarrow> 0 | Some i \<Rightarrow> ket i)"

lemma inj_ket: "inj ket"
  by (meson injI ket_distinct)

lemma classical_operator_existsI:
  assumes "\<And>x. B *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  shows "classical_operator_exists \<pi>"
  unfolding classical_operator_exists_def
  apply (rule cblinfun_extension_existsI[of _ B])
  using assms 
  by (auto simp: inv_f_f[OF inj_ket])

lemma classical_operator_exists_inj:
  assumes "inj_map \<pi>"
  shows "classical_operator_exists \<pi>"
proof -
  define C0 where "C0 \<psi> = (\<lambda>b. case inv_map \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x)" for \<psi> :: "'a\<Rightarrow>complex"

  have has_ell2_norm_C0: \<open>has_ell2_norm \<psi> \<Longrightarrow> has_ell2_norm (C0 \<psi>)\<close> for \<psi>
  proof -
    assume \<open>has_ell2_norm \<psi>\<close>
    hence \<open>bdd_above (sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) ` Collect finite)\<close>
      unfolding has_ell2_norm_def
      by blast
    hence \<open>\<exists> M. \<forall> S. finite S \<longrightarrow> ( sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) S ) \<le> M\<close>
      by (simp add: bdd_above_def)
    then obtain M::real where \<open>\<And> S::'a set. finite S \<Longrightarrow> ( sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) S ) \<le> M\<close>
      by blast
    define \<phi>::\<open>'b \<Rightarrow> complex\<close> where
      \<open>\<phi> b = (case inv_map \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x)\<close> for b
    have \<open>\<lbrakk>finite R; \<forall>i\<in>R. \<phi> i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le> M\<close>
      for R::\<open>'b set\<close>
    proof-
      assume \<open>finite R\<close> and \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
      from  \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
      have  \<open>\<forall>i\<in>R. \<exists> x. Some x = inv_map \<pi> i\<close>
        unfolding \<phi>_def
        by (metis option.case_eq_if option.collapse)
      hence  \<open>\<exists> f. \<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close>
        by metis
      then obtain f::\<open>'b\<Rightarrow>'a\<close> where \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> 
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
          from \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> 
          have \<open>\<forall>i\<in>R. Some (f i) = Some (inv \<pi> (Some i))\<close>
            by (metis inv_map_def option.distinct(1))
          hence \<open>\<forall>i\<in>R. f i = inv \<pi> (Some i)\<close>
            by blast
          hence \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close>
            by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> f_inv_into_f inv_map_def option.distinct(1)) 
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
            by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> option.simps(5))
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
      unfolding \<phi>_def C0_def using has_ell2_norm_def by blast
  qed

  define C1 :: "('a ell2 \<Rightarrow> 'b ell2)"
    where "C1 \<psi> = Abs_ell2 (C0 (Rep_ell2 \<psi>))" for \<psi>
  have [transfer_rule]: "rel_fun (pcr_ell2 (=)) (pcr_ell2 (=)) C0 C1" 
    apply (rule rel_funI)
    unfolding ell2.pcr_cr_eq cr_ell2_def C1_def 
    apply (subst Abs_ell2_inverse)
    using has_ell2_norm_C0 Rep_ell2 by blast+

  have add: "C1 (x + y) = C1 x + C1 y" for x y
    apply transfer unfolding C0_def 
    apply (rule ext, rename_tac b)
    apply (case_tac "inv_map \<pi> b")
    by auto

  have scaleC: "C1 (c *\<^sub>C x) = c *\<^sub>C C1 x" for c x
    apply transfer unfolding C0_def 
    apply (rule ext, rename_tac b)
    apply (case_tac "inv_map \<pi> b")
    by auto

  have "clinear C1"
    using add scaleC by (rule clinearI)

  have bounded_C0: \<open>ell2_norm (C0 \<psi>) \<le> ell2_norm \<psi>\<close> if \<open>has_ell2_norm \<psi>\<close> for \<psi>  
  proof-
    have \<open>\<forall> S. finite S \<longrightarrow> ( sum (\<lambda>i. (cmod (\<psi> i))\<^sup>2) S ) \<le> (ell2_norm \<psi>)^2\<close>
      using \<open>has_ell2_norm \<psi>\<close> ell2_norm_def
      by (smt cSUP_upper has_ell2_norm_def mem_Collect_eq sqrt_le_D sum.cong)
    define \<phi>::\<open>'b \<Rightarrow> complex\<close> where
      \<open>\<phi> b = (case inv_map \<pi> b of None \<Rightarrow> 0 | Some x \<Rightarrow> \<psi> x)\<close> for b
    have \<open>\<lbrakk>finite R; \<forall>i\<in>R. \<phi> i \<noteq> 0\<rbrakk> \<Longrightarrow> (\<Sum>i\<in>R. (cmod (\<phi> i))\<^sup>2) \<le>  (ell2_norm \<psi>)^2\<close>
      for R::\<open>'b set\<close>
    proof-
      assume \<open>finite R\<close> and \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
      from  \<open>\<forall>i\<in>R. \<phi> i \<noteq> 0\<close>
      have  \<open>\<forall>i\<in>R. \<exists> x. Some x = inv_map \<pi> i\<close>
        unfolding \<phi>_def
        by (metis option.case_eq_if option.collapse)
      hence  \<open>\<exists> f. \<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close>
        by metis
      then obtain f::\<open>'b\<Rightarrow>'a\<close> where \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> 
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
          from \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> 
          have \<open>\<forall>i\<in>R. Some (f i) = Some (inv \<pi> (Some i))\<close>
            by (metis inv_map_def option.distinct(1))
          hence \<open>\<forall>i\<in>R. f i = inv \<pi> (Some i)\<close>
            by blast
          hence \<open>\<forall>i\<in>R. \<pi> (f i) = Some i\<close>
            by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> f_inv_into_f inv_map_def option.distinct(1)) 
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
            by (metis \<open>\<forall>i\<in>R. Some (f i) = inv_map \<pi> i\<close> option.simps(5))
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
      unfolding C0_def \<phi>_def by simp
  qed

  hence bounded_C1: "\<exists>K. \<forall>x. norm (C1 x) \<le> norm x * K"
    apply transfer apply (rule exI[of _ 1]) by auto

  have "bounded_clinear C1"
    using \<open>clinear C1\<close> bounded_C1
    using add bounded_clinear_intro scaleC by blast

  define C where "C = cBlinfun C1"
  have [transfer_rule]: "pcr_cblinfun (=) (=) C1 C"
    unfolding C_def unfolding cblinfun.pcr_cr_eq cr_cblinfun_def
    apply (subst cBlinfun_inverse)
    using \<open>bounded_clinear C1\<close> by auto

  have C1_ket: "C1 (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    apply (transfer fixing: \<pi> x) unfolding C0_def
    apply (rule ext, rename_tac b)
    apply (case_tac "inv_map \<pi> b"; cases "\<pi> x")
    apply auto
    apply (metis inv_map_def option.simps(3) range_eqI)
    apply (metis f_inv_into_f inv_map_def option.distinct(1) option.sel)
    apply (metis f_inv_into_f inv_map_def option.sel option.simps(3))
    by (metis (no_types, lifting) assms f_inv_into_f inj_map_def inv_map_def option.sel option.simps(3))

  have "C *\<^sub>V ket x = (case \<pi> x of None \<Rightarrow> 0 | Some i \<Rightarrow> ket i)" for x
    using ket.transfer[transfer_rule del] zero_ell2.transfer[transfer_rule del] 
    apply (tactic \<open>all_tac\<close>)
    apply (transfer fixing: \<pi>)
    by (fact C1_ket)

  thus "classical_operator_exists \<pi>"
    by (rule classical_operator_existsI[of C])
qed

lemma classical_operator_exists_finite[simp]: "classical_operator_exists (\<pi> :: _::finite \<Rightarrow> _)"
  unfolding classical_operator_exists_def
  apply (rule cblinfun_extension_exists_finite_dim)
  using cindependent_ket apply blast
  using finite_class.finite_UNIV finite_imageI ket_ell2_span closure_finite_cspan apply blast
  by simp

lemma classical_operator_basis:
  (*   defines  "classical_function  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'b ell2) 
                          | Some i \<Rightarrow> ket i)"
  assumes a1:"cblinfun_extension_exists (range (ket::'a\<Rightarrow>_)) (classical_function \<pi>)" *)
  assumes "classical_operator_exists \<pi>"
  shows "(classical_operator \<pi>) *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  unfolding classical_operator_def 
  using    f_inv_into_f ket_distinct rangeI
  by (metis (mono_tags, lifting) assms cblinfun_extension_exists classical_operator_exists_def)

lemma classical_operator_finite:
  "(classical_operator \<pi>) *\<^sub>V (ket (x::'a::finite)) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)"
  by (rule classical_operator_basis, simp)

lemma cinner_ket_adjointI:
  fixes F::"'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _" and G::"'b ell2 \<Rightarrow>\<^sub>C\<^sub>L_"
  assumes a1: "\<And> i j. \<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>ket i, G *\<^sub>V ket j\<rangle>"
  shows "F = G*" 
(* TODO redo from scratch (should be very simple) *)
  sorry
(* proof-
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
    moreover have q1: "bounded_clinear (H (ket i))"
      for i
    proof-
      have "bounded_clinear (\<lambda>v. \<langle>F *\<^sub>V (ket i), v\<rangle>)"
        by (simp add: bounded_clinear_cinner_right) 
      moreover have "bounded_clinear (\<lambda>v. \<langle>ket i, G *\<^sub>V v\<rangle>)"
        using cblinfun_apply bounded_clinear_cinner_right_comp by auto      
      ultimately show ?thesis unfolding H_def using bounded_clinear_sub by blast
    qed
    moreover have z1: "bounded_clinear (\<lambda>_. (0::complex))"
      by simp    
    ultimately have "H (ket i) v = 0"
      if "v \<in> complex_vector.span SB"
      for i v
      using equal_span_applyOpSpace[where G = SB and A = "H (ket i)" and B = "\<lambda>_. (0::complex)"]
      by (smt SB_def UNIV_I rangeE u2)
    moreover have "continuous_on (closure (complex_vector.span SB)) (H (ket i))"
      for i
      by (simp add: q1 clinear_continuous_at continuous_at_imp_continuous_on)
    ultimately have "H (ket i) v = 0"
      if "v \<in> closure (complex_vector.span SB)"
      for i v
      using continuous_constant_on_closure that
      by smt
    hence "H (ket i) v = 0"
      for i v
      by (smt UNIV_I u2)
    moreover have jj: "bounded_clinear (\<lambda>u. cnj (H u v))"
      for v
    proof-
      have "bounded_clinear (\<lambda>u. cnj \<langle>F *\<^sub>V u, v\<rangle>)"
        using bounded_antilinear_o_bounded_antilinear cblinfun_apply bounded_antilinear_cinner_left_comp 
          cnj_bounded_antilinear by blast      
      moreover have "bounded_clinear (\<lambda>u. cnj \<langle>u, G *\<^sub>V v\<rangle>)"
        using bounded_antilinear_cinner_left bounded_antilinear_o_bounded_antilinear cnj_bounded_antilinear 
        by blast
      ultimately show ?thesis unfolding H_def 
        using bounded_clinear_sub [where f = "\<lambda>u. cnj \<langle>F *\<^sub>V u, v\<rangle>" and g = "\<lambda>u. cnj \<langle>u, G *\<^sub>V v\<rangle>"]
        by auto      
    qed
    ultimately have cHu0: "cnj (H u v) = 0"
      if "u \<in> complex_vector.span SA"
      for u v
      using z1 SA_def  iso_tuple_UNIV_I rangeE u1 complex_cnj_zero
      by smt (* > 1s *)
    hence Hu0: "H u v = 0"
      if "u \<in> complex_vector.span SA"
      for u v
      by (smt complex_cnj_zero_iff that) 
    moreover have "continuous_on (closure (complex_vector.span SA)) (\<lambda>u. H u v)"
      for v
      using jj clinear_continuous_at continuous_at_imp_continuous_on
        cHu0 complex_cnj_cancel_iff complex_cnj_zero complex_vector.span_span continuous_on_cong 
         z1
      sorry
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
    using adjoint_eqI by auto 
qed *)

lemma classical_operator_adjoint[simp]:
  fixes \<pi> :: "'a \<Rightarrow> 'b option"
  assumes a1: "inj_map \<pi>"
  shows  "(classical_operator \<pi>)* = classical_operator (inv_map \<pi>)"
proof-
  define F where "F = classical_operator (inv_map \<pi>)"
  define G where "G = classical_operator \<pi>"
  have "\<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>ket i, G *\<^sub>V ket j\<rangle>" for i j
  proof-
    have w1: "(classical_operator (inv_map \<pi>)) *\<^sub>V (ket i)
     = (case inv_map \<pi> i of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)"
      by (simp add: classical_operator_basis classical_operator_exists_inj)
    have w2: "(classical_operator \<pi>) *\<^sub>V (ket j)
     = (case \<pi> j of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)"
      by (simp add: assms classical_operator_basis classical_operator_exists_inj)
    have "\<langle>F *\<^sub>V ket i, ket j\<rangle> = \<langle>classical_operator (inv_map \<pi>) *\<^sub>V ket i, ket j\<rangle>"
      unfolding F_def by blast
    also have "\<dots> = \<langle>(case inv_map \<pi> i of Some k \<Rightarrow> ket k | None \<Rightarrow> 0), ket j\<rangle>"
      using w1 by simp
    also have "\<dots> = \<langle>ket i, (case \<pi> j of Some k \<Rightarrow> ket k | None \<Rightarrow> 0)\<rangle>"
    proof(induction "inv_map \<pi> i")
      case None
      hence pi1: "None = inv_map \<pi> i".
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
          hence "inv_map \<pi> c = inv_map \<pi> i"
            by simp
          hence "inv_map \<pi> c = None"
            by (simp add: pi1)
          moreover have "inv_map \<pi> c = Some j"
            using Some.hyps unfolding inv_map_def
            apply auto
            by (metis a1 f_inv_into_f inj_map_def option.distinct(1) rangeI)
          ultimately show ?thesis by simp
        qed
        thus ?thesis
          by (metis None.hyps Some.hyps cinner_zero_left ket_Kronecker_delta_neq option.simps(4) 
              option.simps(5)) 
      qed       
    next
      case (Some d)
      hence s1: "Some d = inv_map \<pi> i".
      show "\<langle>case inv_map \<pi> i of 
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
            using Some.hyps unfolding inv_map_def
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
          hence ij: "Some j = inv_map \<pi> i"
            unfolding inv_map_def apply auto
            apply (metis a1 f_inv_into_f inj_map_def option.discI range_eqI)
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
            using s1 unfolding inv_map_def
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
        thus "\<langle>case inv_map \<pi> i of None \<Rightarrow> 0
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

lemma
  fixes \<pi>::"'b \<Rightarrow> 'c option" and \<rho>::"'a \<Rightarrow> 'b option"
  assumes "classical_operator_exists \<pi>"
  assumes "classical_operator_exists \<rho>"
  shows classical_operator_exists_comp[simp]: "classical_operator_exists (\<pi> \<circ>\<^sub>m \<rho>)"
    and classical_operator_mult[simp]: "classical_operator \<pi> o\<^sub>C\<^sub>L classical_operator \<rho> = classical_operator (\<pi> \<circ>\<^sub>m \<rho>)"
proof -
  define C\<pi> C\<rho> C\<pi>\<rho> where "C\<pi> = classical_operator \<pi>" and "C\<rho> = classical_operator \<rho>" 
    and "C\<pi>\<rho> = classical_operator (\<pi> \<circ>\<^sub>m \<rho>)"
  have C\<pi>x: "C\<pi> *\<^sub>V (ket x) = (case \<pi> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    unfolding C\<pi>_def using \<open>classical_operator_exists \<pi>\<close> by (rule classical_operator_basis)
  have C\<rho>x: "C\<rho> *\<^sub>V (ket x) = (case \<rho> x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    unfolding C\<rho>_def using \<open>classical_operator_exists \<rho>\<close> by (rule classical_operator_basis)
  have C\<pi>\<rho>x': "(C\<pi> o\<^sub>C\<^sub>L C\<rho>) *\<^sub>V (ket x) = (case (\<pi> \<circ>\<^sub>m \<rho>) x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    apply (simp add: scaleC_cblinfun.rep_eq C\<rho>x)
    apply (cases "\<rho> x")
    by (auto simp: C\<pi>x)
  thus \<open>classical_operator_exists (\<pi> \<circ>\<^sub>m \<rho>)\<close>
    by (rule classical_operator_existsI)
  hence "C\<pi>\<rho> *\<^sub>V (ket x) = (case (\<pi> \<circ>\<^sub>m \<rho>) x of Some i \<Rightarrow> ket i | None \<Rightarrow> 0)" for x
    unfolding C\<pi>\<rho>_def
    by (rule classical_operator_basis)
  with C\<pi>\<rho>x' have "(C\<pi> o\<^sub>C\<^sub>L C\<rho>) *\<^sub>V (ket x) = C\<pi>\<rho> *\<^sub>V (ket x)" for x
    by simp
  thus "C\<pi> o\<^sub>C\<^sub>L C\<rho> = C\<pi>\<rho>"
    by (simp add: equal_ket)
qed

lemma classical_operator_Some[simp]: 
  defines  "classical_function  == (\<lambda> \<pi> t. case \<pi> (inv (ket::'a\<Rightarrow>_) t) 
                           of None \<Rightarrow> (0::'a ell2) 
                          | Some i \<Rightarrow> ket i)"
  shows "classical_operator (Some::'a\<Rightarrow>_) = idOp"
proof-
  have "(classical_operator Some) *\<^sub>V (ket i)  = idOp *\<^sub>V (ket i)"
    for i::'a
    apply (subst classical_operator_basis)
    apply (rule classical_operator_exists_inj)
    by auto
  thus ?thesis
    using equal_ket[where A = "classical_operator (Some::'a \<Rightarrow> _ option)"
        and B = "idOp::'a ell2 \<Rightarrow>\<^sub>C\<^sub>L _"]
    by blast
qed

lemma isometry_classical_operator[simp]:
  fixes \<pi>::"'a \<Rightarrow> 'b"
  assumes a1: "inj \<pi>"
  shows "isometry (classical_operator (Some o \<pi>))"
proof -
  have b0: "inj_map (Some \<circ> \<pi>)"
    by (simp add: a1)
  have b0': "inj_map (inv_map (Some \<circ> \<pi>))"
    by simp
  have b1: "inv_map (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>) = Some" 
    apply (rule ext) unfolding inv_map_def o_def 
    using assms unfolding inj_def inv_def by auto
  have b3: "classical_operator (inv_map (Some \<circ> \<pi>)) o\<^sub>C\<^sub>L
            classical_operator (Some \<circ> \<pi>) = classical_operator (inv_map (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>))"
    by (metis b0 b0' b1 classical_operator_Some classical_operator_exists_inj 
        classical_operator_mult)
  show ?thesis
    unfolding isometry_def
    apply (subst classical_operator_adjoint)
    using b0 by (auto simp add: b1 b3)
qed

lemma unitary_classical_operator[simp]:
  fixes \<pi>::"'a \<Rightarrow> 'b"
  assumes a1: "bij \<pi>"
  shows "unitary (classical_operator (Some o \<pi>))"
proof (unfold unitary_def, rule conjI)
  have "inj \<pi>"
    using a1 bij_betw_imp_inj_on by auto
  hence "isometry (classical_operator (Some o \<pi>))"
    by simp
  hence "classical_operator (Some \<circ> \<pi>)* o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>) = idOp"
    unfolding isometry_def by simp
  thus \<open>classical_operator (Some \<circ> \<pi>)* o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>) = idOp\<close>
    by simp 
next
  have "inj \<pi>"
    by (simp add: assms bij_is_inj)
  have comp: "Some \<circ> \<pi> \<circ>\<^sub>m inv_map (Some \<circ> \<pi>) = Some"
    apply (rule ext)
    unfolding inv_map_def o_def map_comp_def
    unfolding inv_def apply auto
    apply (metis \<open>inj \<pi>\<close> inv_def inv_f_f)
    using bij_def image_iff range_eqI
    by (metis a1)
  have "classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (Some \<circ> \<pi>)*
      = classical_operator (Some \<circ> \<pi>) o\<^sub>C\<^sub>L classical_operator (inv_map (Some \<circ> \<pi>))"
    by (simp add: \<open>inj \<pi>\<close>)
  also have "\<dots> = classical_operator ((Some \<circ> \<pi>) \<circ>\<^sub>m (inv_map (Some \<circ> \<pi>)))"
    by (simp add: \<open>inj \<pi>\<close> classical_operator_exists_inj)
  also have "\<dots> = classical_operator (Some::'b\<Rightarrow>_)"
    using comp
    by simp 
  also have "\<dots> = (idOp:: 'b ell2 \<Rightarrow>\<^sub>C\<^sub>L _)"
    by simp
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
    by (simp add: cdot_square_norm)
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




unbundle no_cblinfun_notation

end


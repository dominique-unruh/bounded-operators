(*  Title:      Bounded_Operators.thy
    Author:     Dominique Unruh (University of Tartu)
    Author:     Jose Manuel Rodriguez Caballero (University of Tartu)
*)

section \<open>Bounded Complex-Linear Function\<close>

theory Bounded_Operators

imports
  Complex_Vector_Spaces
  Complex_Inner_Product
  Complex_Euclidean_Space
  "HOL-Analysis.Bounded_Linear_Function"

begin
unbundle notation_norm

lemma c_onorm_componentwise:
  assumes "bounded_clinear f"
  shows "onorm f \<le> (\<Sum>i\<in>Basis. \<parallel>f i\<parallel>)"
  using assms bounded_clinear_is_bounded_linear onorm_componentwise by fastforce

subsection\<^marker>\<open>tag unimportant\<close> \<open>Intro rules for \<^term>\<open>bounded_clinear\<close>\<close>

named_theorems bounded_clinear_intros

lemma c_onorm_inner_left:
  assumes "bounded_clinear r"
  shows "onorm (\<lambda>x. r x \<bullet> f) \<le> onorm r * \<parallel>f\<parallel>"
  by (simp add: assms bounded_clinear_is_bounded_linear onorm_inner_left)


lemma c_onorm_inner_right:
  assumes "bounded_clinear r"
  shows "onorm (\<lambda>x. f \<bullet> r x) \<le> \<parallel>f\<parallel> * onorm r"
  by (simp add: assms bounded_clinear_is_bounded_linear onorm_inner_right)


lemmas [bounded_clinear_intros] =
  bounded_clinear_zero
  bounded_clinear_add
  bounded_clinear_const_mult
  bounded_clinear_mult_const
  bounded_clinear_ident
  bounded_clinear_sum
  bounded_clinear_sub

subsection \<open>Type of bounded complex-linear functions\<close>

typedef\<^marker>\<open>tag important\<close> (overloaded) ('a, 'b) bounded ("(_ \<Rightarrow>\<^sub>B /_)" [22, 21] 21) =
  "{f::'a::complex_normed_vector \<Rightarrow>'b::complex_normed_vector. bounded_clinear f}"
  morphisms bounded_apply BOUNDED
  using bounded_clinear_zero by blast

declare [[coercion
      "bounded_apply :: ('a::complex_normed_vector \<Rightarrow>\<^sub>B'b::complex_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'b"]]

lemma bounded_apply_blinfun_apply:
  "\<exists>f. bounded_apply F = blinfun_apply f"
proof-
  have \<open>bounded_clinear (bounded_apply F)\<close>
    using bounded_apply by blast
  hence \<open>bounded_linear (bounded_apply F)\<close>
    by (simp add: bounded_clinear_is_bounded_linear)
  thus ?thesis by (metis bounded_linear_Blinfun_apply) 
qed

lemma bounded_clinear_bounded_apply[bounded_clinear_intros]:
  "bounded_clinear g \<Longrightarrow> bounded_clinear (\<lambda>x. bounded_apply f (g x))"
  apply transfer
  using bounded_apply bounded_clinear_compose by blast 

setup_lifting type_definition_bounded

lemma bounded_eqI: "(\<And>i. bounded_apply x i = bounded_apply y i) \<Longrightarrow> x = y"
  by transfer auto

lemma bounded_linear_BOUNDED_apply: "bounded_clinear f \<Longrightarrow> bounded_apply (BOUNDED f) = f"
  by (simp add: BOUNDED_inverse)

subsection \<open>Type class instantiations\<close>

instantiation bounded :: (complex_normed_vector, complex_normed_vector) complex_normed_vector
begin

lift_definition\<^marker>\<open>tag important\<close> norm_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> real" is onorm .

lift_definition minus_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  is "\<lambda>f g x. f x - g x"
  by (simp add: bounded_clinear_sub)


definition dist_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> real"
  where "dist_bounded a b = \<parallel>a - b\<parallel>"

definition [code del]:
  "(uniformity :: (('a \<Rightarrow>\<^sub>B 'b) \<times> ('a \<Rightarrow>\<^sub>B 'b)) filter) = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"

definition open_bounded :: "('a \<Rightarrow>\<^sub>B 'b) set \<Rightarrow> bool"
  where [code del]: "open_bounded S = (\<forall>x\<in>S. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> S)"

lift_definition uminus_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b" is "\<lambda>f x. - f x"
  by (simp add: bounded_clinear_minus)  

lift_definition\<^marker>\<open>tag important\<close> zero_bounded :: "'a \<Rightarrow>\<^sub>B 'b" is "\<lambda>x. 0"
  by simp

lift_definition\<^marker>\<open>tag important\<close> plus_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  is "\<lambda>f g x. f x + g x"
  by (simp add: bounded_clinear_add)

lift_definition\<^marker>\<open>tag important\<close> scaleR_bounded::"real \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b" is "\<lambda>r f x. r *\<^sub>R f x"
  by (simp add: scalarR_bounded_clinear)

lift_definition\<^marker>\<open>tag important\<close> scaleC_bounded::"complex \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b" 
  is "\<lambda>r f x. r *\<^sub>C f x"
  by (simp add: bounded_clinear_compose bounded_clinear_scaleR_right)

definition sgn_bounded :: "'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  where "sgn_bounded x = (inverse \<parallel>x\<parallel>) *\<^sub>R x"

instance
proof
  show "a + b + c = a + (b + c)"
    for a :: "'a \<Rightarrow>\<^sub>B 'b"
      and b :: "'a \<Rightarrow>\<^sub>B 'b"
      and c :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer by auto
  show "a + b = b + a"
    for a :: "'a \<Rightarrow>\<^sub>B 'b"
      and b :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer by auto
  show "(0::'a \<Rightarrow>\<^sub>B 'b) + a = a"
    for a :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer by auto
  show "- a + a = 0"
    for a :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer by auto
  show "a - b = a + - b"
    for a :: "'a \<Rightarrow>\<^sub>B 'b"
      and b :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer by auto
  show "a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
      and y :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: pth_6) 
  show "(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    using scaleR_left.add by auto 
  show "a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by simp 
  show "1 *\<^sub>R x = x"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer by simp
  show "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
      and y :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: scaleC_add_right) 
  show "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: scaleC_left.add) 
  show "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by simp 
  show "1 *\<^sub>C x = x"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer by simp
  show "((*\<^sub>R) r::'a \<Rightarrow>\<^sub>B 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
  proof
    show "r *\<^sub>R (x::'a \<Rightarrow>\<^sub>B 'b) = complex_of_real r *\<^sub>C x"
      for x :: "'a \<Rightarrow>\<^sub>B 'b"
      by (simp add: Bounded_Operators.scaleC_bounded.rep_eq Bounded_Operators.scaleR_bounded.rep_eq 
          bounded_eqI scaleR_scaleC)      
  qed
  show "dist x y = \<parallel>x - y\<parallel>"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
      and y :: "'a \<Rightarrow>\<^sub>B 'b"
    by (simp add: dist_bounded_def)

  show "sgn x = inverse \<parallel>x\<parallel> *\<^sub>R x"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
    by (simp add: sgn_bounded_def)

  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a \<Rightarrow>\<^sub>B 'b) y < e})"
    by (simp add: uniformity_bounded_def)

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
    for U :: "('a \<Rightarrow>\<^sub>B 'b) set"
    by (simp add: Bounded_Operators.open_bounded_def)

  show "(\<parallel>x\<parallel> = 0) = (x = 0)"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
  proof
    show "x = 0"
      if "\<parallel>x\<parallel> = 0"
      using that apply transfer
      by (metis (no_types) bounded_clinear_is_bounded_linear less_numeral_extra(3) onorm_pos_lt)
    show "\<parallel>x\<parallel> = 0"
      if "x = 0"
      using that apply transfer
      by (simp add: onorm_eq_0) 
  qed
  show "\<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>"
    for x :: "'a \<Rightarrow>\<^sub>B 'b"
      and y :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: bounded_clinear_is_bounded_linear onorm_triangle)
  show "\<parallel>a *\<^sub>R x\<parallel> = \<bar>a\<bar> * \<parallel>x\<parallel>"
    for a :: real
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: bounded_clinear_is_bounded_linear onorm_scaleR) 
  show "\<parallel>a *\<^sub>C x\<parallel> = \<parallel>a\<parallel> * \<parallel>x\<parallel>"
    for a :: complex
      and x :: "'a \<Rightarrow>\<^sub>B 'b"
    apply transfer
    by (simp add: onorm_scalarC) 
qed
end


declare uniformity_Abort[where 'a="('a :: complex_normed_vector) \<Rightarrow>\<^sub>L ('b :: complex_normed_vector)", code]

lemma norm_bounded_eqI:
  assumes "n \<le> \<parallel>bounded_apply f x\<parallel> / \<parallel>x\<parallel>"
  assumes "\<And>x. \<parallel>bounded_apply f x\<parallel> \<le> n * \<parallel>x\<parallel>"
  assumes "0 \<le> n"
  shows "\<parallel>f\<parallel> = n"
  using norm_blinfun_eqI bounded_apply_blinfun_apply
  by (metis assms(1) assms(2) assms(3) norm_blinfun.rep_eq norm_bounded.rep_eq)

lemma norm_bounded: "\<parallel>bounded_apply f x\<parallel> \<le> \<parallel>f\<parallel> * \<parallel>x\<parallel>"
  apply transfer
  by (simp add: bounded_clinear_is_bounded_linear onorm)  

lemma norm_bounded_bound: "0 \<le> b \<Longrightarrow> (\<And>x. \<parallel>bounded_apply f x\<parallel> \<le> b * \<parallel>x\<parallel>) \<Longrightarrow> \<parallel>f\<parallel> \<le> b"
  by transfer (rule onorm_bound)


lemma bounded_linear_scaleC_lim:
  fixes l::"'a::complex_normed_vector \<Rightarrow>\<^sub>L 'b::complex_normed_vector"
  assumes a1: "f \<longlonglongrightarrow> l" 
    and a2: "\<And>i.  blinfun_apply (f i) (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply (f i) x)"
  shows "blinfun_apply l (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply l x)"
proof-
  have diff_to_0: "(\<lambda>i. f i - l) \<longlonglongrightarrow> 0"
    using a1 by (simp add: LIM_zero)
  have "(\<lambda>i. \<parallel>(blinfun_apply (f i) x) - blinfun_apply l x\<parallel>) \<longlonglongrightarrow> 0" for x
  proof-
    have "\<parallel>(blinfun_apply (f i) x) - blinfun_apply l x\<parallel> \<le> \<parallel>f i - l\<parallel> * \<parallel>x\<parallel>" for i
      by (metis blinfun.diff_left norm_blinfun)      
    thus ?thesis using Limits.tendsto_0_le[where f = "\<lambda>i. f i - l" 
          and g = "\<lambda>i. \<parallel>(blinfun_apply (f i) x) - blinfun_apply l x\<parallel>"
          and K = "\<parallel>x\<parallel>" and F = "sequentially"] diff_to_0 by simp      
  qed
  hence "(\<lambda>i. (blinfun_apply (f i) x) - blinfun_apply l x) \<longlonglongrightarrow> 0" for x
    by (simp add: tendsto_norm_zero_iff)    
  hence b1: "(\<lambda>i. (blinfun_apply (f i) x)) \<longlonglongrightarrow> (blinfun_apply l x)" for x
    by (simp add: LIM_zero_cancel)    
  hence "(\<lambda>i. blinfun_apply (f i) (c *\<^sub>C x)) \<longlonglongrightarrow> blinfun_apply l (c *\<^sub>C x)"
    by simp 
  moreover have "(\<lambda>i. c *\<^sub>C (blinfun_apply (f i) x)) \<longlonglongrightarrow> c *\<^sub>C (blinfun_apply l x)"
    using b1 by (simp add: tendsto_scaleC_left)    
  moreover have "(\<lambda>i. blinfun_apply (f i) (c *\<^sub>C x)) = (\<lambda>i. c *\<^sub>C (blinfun_apply (f i) x))"
    using a2 by auto
  ultimately show ?thesis by (metis limI)     
qed

instance bounded :: (complex_normed_vector, cbanach) cbanach
proof
  show "convergent X"
    if "Cauchy X"
    for X :: "nat \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  proof-
    have "\<exists>f. bounded_apply (X i) = blinfun_apply f" for i
      by (simp add: bounded_apply_blinfun_apply)      
    then obtain Y where Cauchy1:"bounded_apply (X i) = blinfun_apply (Y i)" for i
      by metis
    have "bounded_clinear (bounded_apply (X i))" for i
      using bounded_apply by blast
    hence scaleC1: "blinfun_apply (Y i) (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply (Y i) x)" for i c x
      using Cauchy1
      by (simp add: bounded_clinear_scaleC) 
    hence bounded_clinear1: "bounded_clinear (blinfun_apply (Y i))" for i
      using Cauchy1 \<open>\<And>i. bounded_clinear (bounded_apply (X i))\<close> by auto      
    have "dist (X m) (X n) = dist (Y m) (Y n)" for m n
      using Cauchy1 unfolding dist_bounded_def dist_blinfun_def
      by (metis blinfun.diff_left blinfun_eqI bounded_apply_blinfun_apply minus_bounded.rep_eq 
          norm_blinfun.rep_eq norm_bounded.rep_eq)       
    hence "Cauchy Y"
      using that unfolding Cauchy_def by auto
    hence "convergent Y"
      by (simp add: Cauchy_convergent_iff)
    hence "\<exists>l. Y \<longlonglongrightarrow> l"
      by (simp add: convergentD)
    then obtain l where l1: "Y \<longlonglongrightarrow> l"
      by blast
    have "(\<lambda>i. Y i - l) \<longlonglongrightarrow> 0"
      using l1 by (simp add: LIM_zero)
    hence "(\<lambda>i. \<parallel>Y i - l\<parallel>) \<longlonglongrightarrow> 0"
      by (simp add: tendsto_norm_zero)
    moreover have "\<parallel>Y i - l\<parallel> = \<parallel>X i - BOUNDED l\<parallel>" for i
    proof-
      have  "onorm (\<lambda>x. Y i x - l x) = onorm (bounded_apply (X i - BOUNDED l))"
        for i :: nat 
      proof-
        have "l (c *\<^sub>C x) = c *\<^sub>C l x" for c and x
          apply (rule bounded_linear_scaleC_lim[where f = Y])
          using l1
          apply simp
          by (simp add: scaleC1) 
        moreover have "bounded_linear l"
          by (simp add: blinfun.bounded_linear_right)          
        ultimately have "bounded_clinear l"
          by (simp add: bounded_linear_bounded_clinear)          
        hence "Y i x - l x = bounded_apply (X i - BOUNDED l) x" for x
          by (simp add: Cauchy1 bounded_linear_BOUNDED_apply minus_bounded.rep_eq)          
        thus ?thesis by simp
      qed
      thus ?thesis using Cauchy1 apply transfer unfolding norm_bounded_def by auto        
    qed
    ultimately have "(\<lambda>i. \<parallel>X i - BOUNDED (blinfun_apply l)\<parallel>) \<longlonglongrightarrow> 0"
      by simp
    thus ?thesis using LIM_zero_cancel convergent_def tendsto_norm_zero_iff by blast 
  qed
qed


lift_definition
  bounded_of_matrix::"('b::complex_euclidean_space \<Rightarrow> 'a::complex_euclidean_space \<Rightarrow> complex) 
  \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  is "\<lambda>a x. \<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, x\<rangle> * a i j) *\<^sub>C i"
proof
  show "(\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, b1 + b2\<rangle> * f i j) *\<^sub>C i) = 
          (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, b1\<rangle> * f i j) *\<^sub>C i)
        + (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, b2\<rangle> * f i j) *\<^sub>C i)"
    for f :: "'b \<Rightarrow> 'a \<Rightarrow> complex"
      and b1 :: 'a
      and b2 :: 'a
  proof-
    have "(\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, b1 + b2\<rangle> * f i j) *\<^sub>C i) = 
          (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. ((\<langle>j, b1\<rangle> + \<langle>j, b2\<rangle>) * f i j) *\<^sub>C i)"
      by (metis (no_types, lifting) Finite_Cartesian_Product.sum_cong_aux cinner_right_distrib)
    also have "\<dots> = 
          (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, b1\<rangle> * f i j + \<langle>j, b2\<rangle> * f i j) *\<^sub>C i)"
      by (metis (mono_tags, lifting) sum.cong vector_space_over_itself.scale_left_distrib)
    also have "\<dots> = 
          (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. ((\<langle>j, b1\<rangle> * f i j) *\<^sub>C i + (\<langle>j, b2\<rangle> * f i j) *\<^sub>C i))"
      by (meson scaleC_left.add sum.cong)
    also have "\<dots> = 
          (\<Sum>i\<in>cBasis. (\<Sum>j\<in>cBasis. ((\<langle>j, b1\<rangle> * f i j) *\<^sub>C i))
        + (\<Sum>j\<in>cBasis. ((\<langle>j, b2\<rangle> * f i j) *\<^sub>C i)) )"
      by (simp add: sum.distrib)
    also have "\<dots> = 
           (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. ((\<langle>j, b1\<rangle> * f i j) *\<^sub>C i))
         + (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. ((\<langle>j, b2\<rangle> * f i j) *\<^sub>C i)) "
      by (simp add: sum.distrib)
    finally show ?thesis by blast
  qed
  show "(\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, r *\<^sub>C b\<rangle> * f i j) *\<^sub>C i) 
   =  r *\<^sub>C (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, b\<rangle> * f i j) *\<^sub>C i)"
    for f :: "'b \<Rightarrow> 'a \<Rightarrow> complex"
      and r :: complex
      and b :: 'a
  proof-
    have "(\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, r *\<^sub>C b\<rangle> * f i j) *\<^sub>C i) 
         =  (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (r * \<langle>j, b\<rangle> * f i j) *\<^sub>C i)"
      by (metis (no_types, lifting) cinner_cnj_commute cinner_scaleC_left complex_cnj_cnj
          complex_cnj_mult sum.cong)      
    also have "...  
         =  (\<Sum>i\<in>cBasis. (\<Sum>j\<in>cBasis. r *\<^sub>C (\<langle>j, b\<rangle> * f i j) *\<^sub>C i))"
      by (smt Finite_Cartesian_Product.sum_cong_aux cinner_cnj_commute complex_scaleC_def 
          mult_commute_abs scaleC_scaleC vector_space_over_itself.scale_scale)
    also have "...  
         =  (\<Sum>i\<in>cBasis. r *\<^sub>C (\<Sum>j\<in>cBasis. (\<langle>j, b\<rangle> * f i j) *\<^sub>C i))"
      by (simp add: complex_vector.scale_sum_right)
    also have "...  
         = r *\<^sub>C  (\<Sum>i\<in>cBasis. (\<Sum>j\<in>cBasis. (\<langle>j, b\<rangle> * f i j) *\<^sub>C i))"
      by (metis (no_types, lifting) Finite_Cartesian_Product.sum_cong_aux scaleC_right.sum)
    finally show ?thesis by blast
  qed
  show "\<exists>K. \<forall>x. \<parallel>\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, x\<rangle> * f i j) *\<^sub>C i\<parallel> \<le> \<parallel>x\<parallel> * K"
    for f :: "'b \<Rightarrow> 'a \<Rightarrow> complex"
  proof-
    define K where "K = (\<Sum>i\<in>cBasis. (\<Sum>j\<in>cBasis. \<parallel>f i j\<parallel>))"
    have "\<parallel>\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, x\<rangle> * f i j) *\<^sub>C i\<parallel> \<le> \<parallel>x\<parallel> * K" for x::'a
    proof-
      have "\<parallel>\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, x\<rangle> * f i j) *\<^sub>C i\<parallel>
      \<le> (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. \<parallel>(\<langle>j, x\<rangle> * f i j) *\<^sub>C i\<parallel>)"
        by (simp add: sum_norm_le)
      also have "\<dots>
      = (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. \<parallel>\<langle>j, x\<rangle> * f i j\<parallel> * \<parallel>i\<parallel>)"
        by auto
      also have "\<dots>
      = (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. \<parallel>\<langle>j, x\<rangle> * f i j\<parallel>)"
      proof-
        have "i\<in>cBasis \<Longrightarrow> \<parallel>i\<parallel> = 1" for i::'a
          by simp        
        thus ?thesis by auto 
      qed
      also have "\<dots>
      = (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. \<parallel>\<langle>j, x\<rangle>\<parallel> * \<parallel>f i j\<parallel>)"
      proof-
        have "\<parallel>\<langle>j, x\<rangle> * f i j\<parallel> = \<parallel>\<langle>j, x\<rangle>\<parallel> * \<parallel>f i j\<parallel>" for i j
          by (simp add: norm_mult)        
        thus ?thesis by simp
      qed
      also have "\<dots> \<le> \<parallel>x\<parallel> * K"
      proof-
        have "j\<in>cBasis \<Longrightarrow> \<parallel>\<langle>j, x\<rangle>\<parallel> \<le> \<parallel>x\<parallel>" for j
          by (metis cinner_same_cBasis complex_inner_class.Cauchy_Schwarz_ineq 
              complex_norm_eq_1 mult_cancel_right1 real_normed_algebra_1_class.norm_one)          
        moreover have "\<parallel>f i j\<parallel> \<ge> 0" for i j
          by simp
        ultimately have "(\<Sum>j\<in>cBasis. \<parallel>\<langle>j, x\<rangle>\<parallel> * \<parallel>f i j\<parallel>) \<le> (\<Sum>j\<in>cBasis. \<parallel>x\<parallel> * \<parallel>f i j\<parallel>)" for i
          by (simp add: mult_right_mono sum_mono)
        hence "(\<Sum>j\<in>cBasis. \<parallel>\<langle>j, x\<rangle>\<parallel> * \<parallel>f i j\<parallel>) \<le> \<parallel>x\<parallel> * (\<Sum>j\<in>cBasis. \<parallel>f i j\<parallel>)" for i
          by (simp add: sum_distrib_left)
        hence "(\<Sum>i\<in>cBasis. (\<Sum>j\<in>cBasis. \<parallel>\<langle>j, x\<rangle>\<parallel> * \<parallel>f i j\<parallel>)) 
          \<le> (\<Sum>i\<in>cBasis. \<parallel>x\<parallel> * (\<Sum>j\<in>cBasis. \<parallel>f i j\<parallel>))"
          by (simp add: sum_mono) 
        hence "(\<Sum>i\<in>cBasis. (\<Sum>j\<in>cBasis. \<parallel>\<langle>j, x\<rangle>\<parallel> * \<parallel>f i j\<parallel>)) 
          \<le> \<parallel>x\<parallel> * (\<Sum>i\<in>cBasis. (\<Sum>j\<in>cBasis. \<parallel>f i j\<parallel>))"
          by (simp add: sum_distrib_left)
        thus ?thesis unfolding K_def by blast
      qed
      finally show ?thesis by blast
    qed
    thus ?thesis by blast
  qed
qed

lemma bounded_complex_euclidean_eqI: 
  fixes f::"'a::complex_euclidean_space \<Rightarrow>\<^sub>B 'b::complex_euclidean_space"
  assumes f1: "\<And>x. x\<in>cBasis \<Longrightarrow> bounded_apply f x = bounded_apply g x"
  shows "f = g"
proof-
  have " \<And>i. (\<And>x. x \<in> cBasis \<Longrightarrow> bounded_apply f x = bounded_apply g x) \<Longrightarrow>
         bounded_apply f (\<Sum>b\<in>cBasis. cnj \<langle>i, b\<rangle> *\<^sub>C b) =
         bounded_apply g (\<Sum>b\<in>cBasis. cnj \<langle>i, b\<rangle> *\<^sub>C b)"
  proof-
    assume a1: "\<And>x. x \<in> cBasis \<Longrightarrow> bounded_apply f x = bounded_apply g x"
    show "bounded_apply f (\<Sum>b\<in>cBasis. cnj \<langle>i, b\<rangle> *\<^sub>C b) =
         bounded_apply g (\<Sum>b\<in>cBasis. cnj \<langle>i, b\<rangle> *\<^sub>C b)" for i
    proof-
      have "bounded_apply f (\<Sum>b\<in>cBasis. cnj \<langle>i, b\<rangle> *\<^sub>C b) 
        = (\<Sum>b\<in>cBasis. (cnj \<langle>i, b\<rangle> *\<^sub>C (bounded_apply f b)))"
        apply transfer
        by (smt Finite_Cartesian_Product.sum_cong_aux bounded_clinear.axioms(1)
            bounded_clinear_scaleC complex_vector.linear_sum)
      also have "\<dots> = (\<Sum>b\<in>cBasis. (cnj \<langle>i, b\<rangle> *\<^sub>C (bounded_apply g b)))"
        using f1 by auto
      also have "\<dots> = bounded_apply g (\<Sum>b\<in>cBasis. cnj \<langle>i, b\<rangle> *\<^sub>C b)"
        apply transfer 
        by (smt bounded_clinear.axioms(1) bounded_clinear_scaleC complex_vector.linear_sum sum.cong) 
      finally show ?thesis by blast
    qed
  qed
  thus ?thesis
    by (simp add: bounded_eqI complex_euclidean_representation f1)
qed

lemma bounded_of_matrix_works:
  fixes f::"'a::complex_euclidean_space \<Rightarrow>\<^sub>B 'b::complex_euclidean_space"
  shows "bounded_of_matrix (\<lambda>i j. \<langle>i, f j\<rangle>) = f"
proof-
  have "x \<in> cBasis \<Longrightarrow> bounded_apply (bounded_of_matrix (\<lambda>i j. \<langle>i, (f j)\<rangle>)) x = bounded_apply f x" 
    for x
  proof-
    assume x_basis: "x \<in> cBasis"
    have "bounded_apply (bounded_of_matrix (\<lambda>i j. \<langle>i, (f j)\<rangle>)) x 
       = (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, x\<rangle> * \<langle>i, (f j)\<rangle>) *\<^sub>C i)"
      by (metis (no_types, lifting) bounded_of_matrix.rep_eq sum.cong)
    also have "\<dots> = (\<Sum>i\<in>cBasis. (\<langle>x, x\<rangle> * \<langle>i, (f x)\<rangle>) *\<^sub>C i)"
    proof-
      have "(\<Sum>j\<in>cBasis. (\<langle>j, x\<rangle> * \<langle>i, f j\<rangle>) *\<^sub>C i) =  (\<langle>x, x\<rangle> * \<langle>i, f x\<rangle>) *\<^sub>C i" for i
      proof-
        have "\<exists>cBasis'. cBasis = insert x cBasis' \<and> x \<notin> cBasis'"
          using x_basis by (simp add: mk_disjoint_insert) 
        then obtain cBasis' 
          where c1: "cBasis = insert x cBasis'" and c2: "x \<notin> cBasis'"
          by blast
        have "(\<Sum>j\<in>cBasis. (\<langle>j, x\<rangle> * \<langle>i, f j\<rangle>) *\<^sub>C i) = 
              (\<langle>x, x\<rangle> * \<langle>i, f x\<rangle>) *\<^sub>C i + (\<Sum>j\<in>cBasis'. (\<langle>j, x\<rangle> * \<langle>i, f j\<rangle>) *\<^sub>C i)"
          using c1 c2 by (metis (no_types, lifting) complex_finite_cBasis finite_insert sum.insert) 
        also have d1: "\<dots> = \<langle>i, f x\<rangle> *\<^sub>C i + (\<Sum>j\<in>cBasis'. (\<langle>j, x\<rangle> * \<langle>i, f j\<rangle>) *\<^sub>C i)"
          using x_basis by simp
        also have "\<dots> = \<langle>i, f x\<rangle> *\<^sub>C i"
        proof-
          have "j\<in>cBasis' \<Longrightarrow> (\<langle>j, x\<rangle> * \<langle>i, f j\<rangle>) *\<^sub>C i = 0" for j
            by (metis c1 c2 cinner_not_same_cBasis complex_vector.scale_eq_0_iff insert_iff 
                mult_not_zero)            
          hence "(\<Sum>j\<in>cBasis'. (\<langle>j, x\<rangle> * \<langle>i, f j\<rangle>) *\<^sub>C i) = 0"
            by (simp add: sum.neutral)            
          thus ?thesis by simp
        qed
        finally show ?thesis using d1 by auto 
      qed
      thus ?thesis by simp
    qed
    also have "\<dots> = (\<Sum>i\<in>cBasis. \<langle>i, f x\<rangle> *\<^sub>C i)"
      using x_basis by simp
    also have "\<dots> = f x"
      using complex_euclidean_representation' by blast
    finally show ?thesis by blast
  qed
  hence "bounded_apply (bounded_of_matrix (\<lambda>i j. \<langle>i, (f j)\<rangle>)) x = bounded_apply f x" for x
    using bounded_complex_euclidean_eqI by metis 
  thus ?thesis by (simp add: bounded_eqI) 
qed

lemma bounded_of_matrix_apply:
  "bounded_of_matrix a x = (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. (\<langle>j, x\<rangle> * a i j) *\<^sub>C i)"
  by transfer simp

lemma bounded_of_matrix_minus: 
  "bounded_of_matrix x - bounded_of_matrix y = bounded_of_matrix (x - y)"
  by transfer (auto simp: algebra_simps sum_subtractf)

lemma norm_bounded_of_matrix:
  "\<parallel>bounded_of_matrix a\<parallel> \<le> (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. \<parallel>a i j\<parallel>)"
proof-
  have a1: "n \<in> cBasis \<Longrightarrow>
       m \<in> cBasis \<Longrightarrow> cmod (\<langle>m, x\<rangle> * a n m) \<le> \<parallel>x\<parallel> * cmod (a n m)"
    for n::'b and m::'a and x::'a
  proof-
    assume c1: "n \<in> cBasis" and c2: "m \<in> cBasis"
    hence b1: "\<parallel>\<langle>m, x\<rangle>\<parallel> \<le> \<parallel>x\<parallel>"
      by (metis cinner_same_cBasis complex_inner_class.Cauchy_Schwarz_ineq 
          mult_cancel_right1 norm_eq_sqrt_cinner real_normed_algebra_1_class.norm_one real_sqrt_one)
    have e1: "\<parallel>a n m\<parallel> \<ge> 0"
      by simp
    have "\<parallel>\<langle>m, x\<rangle> * a n m\<parallel> = \<parallel>\<langle>m, x\<rangle>\<parallel> * \<parallel>a n m\<parallel>"
      using norm_mult by auto
    also have "\<dots> \<le> \<parallel>x\<parallel> * \<parallel>a n m\<parallel>"
      using b1 e1 mult_right_mono by blast 
    finally show "\<parallel>\<langle>m, x\<rangle> * a n m\<parallel> \<le> \<parallel>x\<parallel> * \<parallel>a n m\<parallel>" 
      using b1 by blast
  qed
  show ?thesis
    apply (rule norm_bounded_bound)
     apply (simp add: sum_nonneg)
    apply (simp only: bounded_of_matrix_apply sum_distrib_right)
    apply (rule order_trans[OF norm_sum sum_mono])
    apply (rule order_trans[OF norm_sum sum_mono])
    apply (simp add: abs_mult mult_right_mono)
    apply (simp add: ac_simps)
    using a1 by blast
qed

lemma tendsto_bounded_of_matrix:
  assumes a1: "\<And>i j. i \<in> cBasis \<Longrightarrow> j \<in> cBasis \<Longrightarrow> ((\<lambda>n. b n i j) \<longlongrightarrow> a i j) F"
  shows "((\<lambda>n. bounded_of_matrix (b n)) \<longlongrightarrow> bounded_of_matrix a) F"
proof -
  have b1: "\<And>i j. i \<in> cBasis \<Longrightarrow> j \<in> cBasis \<Longrightarrow> Zfun (\<lambda>x. \<parallel>b x i j - a i j\<parallel>) F"
    using assms unfolding tendsto_Zfun_iff Zfun_norm_iff .
  have "\<And>i. i \<in> cBasis \<Longrightarrow> Zfun (\<lambda>x. \<Sum>j\<in>cBasis. \<parallel>b x i j - a i j\<parallel>) F"
  proof-
    fix i::'a
    assume "i \<in> cBasis"
    hence "j \<in> cBasis \<Longrightarrow> Zfun (\<lambda>x. \<parallel>b x i j - a i j\<parallel>) F" for j
      using b1 by simp 
    thus "Zfun (\<lambda>x. \<Sum>j\<in>cBasis. \<parallel>b x i j - a i j\<parallel>) F"
      using Zfun_sum[where s = cBasis and F = F and f = "(\<lambda>j x. cmod (b x i j - a i j))"]
      by (simp add: \<open>\<And>j. j \<in> cBasis \<Longrightarrow> Zfun (\<lambda>x. cmod (b x i j - a i j)) F\<close> 
          \<open>\<lbrakk>finite cBasis; \<And>ia. ia \<in> cBasis \<Longrightarrow> Zfun (\<lambda>x. cmod (b x i ia - a i ia)) F\<rbrakk> 
          \<Longrightarrow> Zfun (\<lambda>x. \<Sum>ia\<in>cBasis. cmod (b x i ia - a i ia)) F\<close>)
  qed
  hence "Zfun (\<lambda>x. (\<Sum>i\<in>cBasis. \<Sum>j\<in>cBasis. \<parallel>b x i j - a i j\<parallel>)) F"
    using Zfun_sum[where s = cBasis and F = F and f = "(\<lambda>i x. \<Sum>j\<in>cBasis. \<parallel>b x i j - a i j\<parallel>)"]
    by auto
  thus ?thesis
    unfolding tendsto_Zfun_iff bounded_of_matrix_minus
    apply (rule Zfun_le) apply auto
    by (smt Finite_Cartesian_Product.sum_cong_aux fun_diff_def norm_bounded_of_matrix)
qed

lemma ctendsto_componentwise:
  fixes a::"'a::complex_euclidean_space \<Rightarrow>\<^sub>B 'b::complex_euclidean_space"
    and b::"'c \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  shows "(\<And>i j. i \<in> cBasis \<Longrightarrow> j \<in> cBasis \<Longrightarrow> ((\<lambda>n. \<langle>i, b n j\<rangle>) \<longlongrightarrow> \<langle>i, a j\<rangle>) F) \<Longrightarrow> (b \<longlongrightarrow> a) F"
  apply (subst bounded_of_matrix_works[of a, symmetric])
  apply (subst bounded_of_matrix_works[of "b x" for x, symmetric, abs_def])
  by (rule tendsto_bounded_of_matrix)

lemma norm_bounded_complex_euclidean_le:
  fixes a::"'a::complex_euclidean_space \<Rightarrow>\<^sub>B 'b::complex_normed_vector"
  shows "\<parallel>a\<parallel> \<le> sum (\<lambda>x. \<parallel>a x\<parallel>) cBasis"
proof-
  have "\<parallel>bounded_apply a (\<Sum>b\<in>cBasis. cnj \<langle>x, b\<rangle> *\<^sub>C b)\<parallel>
         \<le> (\<Sum>x\<in>cBasis. \<parallel>bounded_apply a x\<parallel>) * \<parallel>x\<parallel>" for x
  proof-
    have "bounded_apply a (\<Sum>b\<in>cBasis. cnj \<langle>x, b\<rangle> *\<^sub>C b)
        = (\<Sum>b\<in>cBasis. cnj \<langle>x, b\<rangle> *\<^sub>C bounded_apply a b)"
      apply transfer
      by (smt bounded_clinear.axioms(1) bounded_clinear_scaleC complex_vector.linear_sum sum.cong) 
    hence "\<parallel>bounded_apply a (\<Sum>b\<in>cBasis. cnj \<langle>x, b\<rangle> *\<^sub>C b)\<parallel>
        = \<parallel>(\<Sum>b\<in>cBasis. cnj \<langle>x, b\<rangle> *\<^sub>C bounded_apply a b)\<parallel>"
      by simp
    also have  "\<dots> \<le> (\<Sum>b\<in>cBasis. \<parallel>cnj \<langle>x, b\<rangle> *\<^sub>C bounded_apply a b\<parallel>)"
      by (simp add: sum_norm_le)
    also have  "\<dots> \<le> (\<Sum>b\<in>cBasis. \<parallel>\<langle>x, b\<rangle>\<parallel> * \<parallel>bounded_apply a b\<parallel>)"
    proof-
      have "\<parallel>cnj \<langle>x, b\<rangle> *\<^sub>C bounded_apply a b\<parallel> = \<parallel>\<langle>x, b\<rangle>\<parallel> * \<parallel>bounded_apply a b\<parallel>" for b
        by auto
      thus ?thesis by auto
    qed
    also have  "\<dots> \<le> (\<Sum>b\<in>cBasis. \<parallel>x\<parallel> * \<parallel>bounded_apply a b\<parallel>)"
    proof-
      have "b\<in>cBasis \<Longrightarrow> \<parallel>\<langle>x, b\<rangle>\<parallel> \<le> \<parallel>x\<parallel>" for b
        by (simp add: cBasis_le_norm)
      thus ?thesis
        by (simp add: mult_right_mono sum_mono) 
    qed
    finally show ?thesis by (simp add: mult.commute sum_distrib_left) 
  qed
  thus ?thesis
  proof -
    have f1: "\<forall>A f. 0 \<le> (\<Sum>a\<in>A. \<parallel>f (a::'a)::'b\<parallel>)"
      using norm_ge_zero norm_sum order_trans by blast
    have "\<forall>b. \<parallel>bounded_apply a b\<parallel> \<le> (\<Sum>b\<in>cBasis. \<parallel>bounded_apply a b\<parallel>) * \<parallel>b\<parallel>"
      by (metis (no_types) \<open>\<And>x. \<parallel>bounded_apply a (\<Sum>b\<in>cBasis. cnj \<langle>x, b\<rangle> *\<^sub>C b)\<parallel> 
      \<le> (\<Sum>x\<in>cBasis. \<parallel>bounded_apply a x\<parallel>) * \<parallel>x\<parallel>\<close> complex_euclidean_representation)
    thus ?thesis using f1 by (meson norm_bounded_bound)
  qed
qed

lemma ctendsto_componentwise1:
  fixes a::"'a::complex_euclidean_space \<Rightarrow>\<^sub>B 'b::complex_normed_vector"
    and b::"'c \<Rightarrow> 'a \<Rightarrow>\<^sub>B 'b"
  assumes "(\<And>j. j \<in> cBasis \<Longrightarrow> ((\<lambda>n. b n j) \<longlongrightarrow> a j) F)"
  shows "(b \<longlongrightarrow> a) F"
proof -
  have "\<And>j. j \<in> cBasis \<Longrightarrow> Zfun (\<lambda>x. norm (b x j - a j)) F"
    using assms unfolding tendsto_Zfun_iff Zfun_norm_iff .
  hence "Zfun (\<lambda>x. \<Sum>j\<in>cBasis. norm (b x j - a j)) F"
    by (auto intro!: Zfun_sum)
  thus ?thesis
    unfolding tendsto_Zfun_iff
    apply (rule Zfun_le)
    apply (auto intro!: order_trans[OF norm_bounded_complex_euclidean_le] )
    by (smt minus_bounded.rep_eq sum.cong)    
qed


lemma continuous_bounded_componentwiseI:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::complex_euclidean_space \<Rightarrow>\<^sub>B 'c::complex_euclidean_space"
  assumes "\<And>i j. i \<in> cBasis \<Longrightarrow> j \<in> cBasis \<Longrightarrow> continuous F (\<lambda>x. \<langle>i, (f x) j\<rangle>)"
  shows "continuous F f"
  using assms by (auto simp: continuous_def intro!: ctendsto_componentwise)

lemma continuous_bounded_componentwiseI1:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::complex_euclidean_space \<Rightarrow>\<^sub>B 'c::complex_normed_vector"
  assumes "\<And>i. i \<in> cBasis \<Longrightarrow> continuous F (\<lambda>x. f x i)"
  shows "continuous F f"
  using assms apply (auto simp: continuous_def) 
  by (simp add: ctendsto_componentwise1) 

lemma continuous_on_bounded_componentwise:
  fixes f:: "'d::t2_space \<Rightarrow> 'e::complex_euclidean_space \<Rightarrow>\<^sub>B 'f::complex_normed_vector"
  assumes "\<And>i. i \<in> cBasis \<Longrightarrow> continuous_on s (\<lambda>x. f x i)"
  shows "continuous_on s f"
  using assms
  by (auto intro!: continuous_at_imp_continuous_on intro!: ctendsto_componentwise1
    simp: continuous_on_eq_continuous_within continuous_def)

lemma bounded_clinear_bounded_matrix: "bounded_clinear (\<lambda>x. \<langle>j, bounded_apply (x::_\<Rightarrow>\<^sub>B _) i\<rangle>)"
  proof
  show "\<langle>j, bounded_apply (b1 + b2) i\<rangle> = \<langle>j, bounded_apply b1 i\<rangle> + \<langle>j, bounded_apply b2 i\<rangle>"
    for b1 :: "'a \<Rightarrow>\<^sub>B 'b"
      and b2 :: "'a \<Rightarrow>\<^sub>B 'b"
    by (simp add: cinner_right_distrib plus_bounded.rep_eq)    
  show "\<langle>j, bounded_apply (r *\<^sub>C b) i\<rangle> = r *\<^sub>C \<langle>j, bounded_apply b i\<rangle>"
    for r :: complex
      and b :: "'a \<Rightarrow>\<^sub>B 'b"
    by (metis cinner_cnj_commute cinner_scaleC_left complex_cnj_cnj complex_cnj_mult 
        complex_scaleC_def scaleC_bounded.rep_eq)    
  show "\<exists>K. \<forall>x. \<parallel>\<langle>j, bounded_apply x i\<rangle>\<parallel> \<le> \<parallel>x\<parallel> * K"
  proof-
    have  "bounded_clinear x \<Longrightarrow> \<parallel>\<langle>j, x i\<rangle>\<parallel> \<le> onorm x * \<parallel>j\<parallel> * \<parallel>i\<parallel>" for j::'b and i::'a and x
    proof-
      assume bc: "bounded_clinear x"
      hence "\<parallel>x i\<parallel> \<le> onorm x * \<parallel>i\<parallel>"
        by (simp add: bounded_clinear_is_bounded_linear onorm)
      moreover have "\<parallel>\<langle>j, x i\<rangle>\<parallel> \<le> \<parallel>j\<parallel>*\<parallel>x i\<parallel>"
        by (simp add: complex_inner_class.Cauchy_Schwarz_ineq)
      ultimately have "\<parallel>\<langle>j, x i\<rangle>\<parallel> \<le> \<parallel>j\<parallel> * onorm x * \<parallel>i\<parallel>"
        by (smt norm_ge_zero ordered_comm_semiring_class.comm_mult_left_mono 
            vector_space_over_itself.scale_scale)
      thus ?thesis by (simp add: mult.commute) 
    qed
    hence f1: "\<exists>K. \<forall>x. bounded_clinear x \<longrightarrow> \<parallel>\<langle>j, x i\<rangle>\<parallel> \<le> onorm x * K" for j::'b and i::'a
      by (metis vector_space_over_itself.scale_scale)              
    show ?thesis apply transfer apply auto by (rule f1)
  qed
qed

lemma (in bounded_clinear) tendsto: "(g \<longlongrightarrow> a) F \<Longrightarrow> ((\<lambda>x. f (g x)) \<longlongrightarrow> f a) F"
  using bounded_clinear_is_bounded_linear  bounded_clinear_axioms bounded_linear.tendsto by blast
  
lemma (in bounded_clinear) continuous: "continuous F g \<Longrightarrow> continuous F (\<lambda>x. f (g x))"
  using bounded_clinear_is_bounded_linear bounded_clinear_axioms bounded_linear.continuous by blast

lemma (in bounded_clinear) continuous_on: "continuous_on s g \<Longrightarrow> continuous_on s (\<lambda>x. f (g x))"
  using bounded_clinear_is_bounded_linear bounded_clinear_axioms bounded_linear.continuous_on 
  by blast

lemma (in bounded_clinear) tendsto_zero: "(g \<longlongrightarrow> 0) F \<Longrightarrow> ((\<lambda>x. f (g x)) \<longlongrightarrow> 0) F"
  using bounded_clinear_is_bounded_linear tendsto by force

lemma continuous_bounded_matrix:
  fixes f:: "'b::t2_space \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>B 'c::complex_inner"
  assumes f1:"continuous F f"
  shows "continuous F (\<lambda>x. \<langle>j, bounded_apply (f x) i\<rangle>)"
  by (rule bounded_clinear.continuous[OF bounded_clinear_bounded_matrix assms])


unbundle no_notation_norm

end

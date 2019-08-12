(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Main results:
- bounded: Definition of complex bounded operators. Instantiation as a complex Banach space.

*)


theory Bounded_Operators
  imports Complex_Inner_Product Real_Bounded_Operators 
    Lattice_Missing Extended_Sorry

begin
section \<open>Complex bounded operators\<close>

typedef (overloaded) ('a::complex_normed_vector, 'b::complex_normed_vector) bounded
  = \<open>{A::'a \<Rightarrow> 'b. bounded_clinear A}\<close>
  morphisms times_bounded_vec Abs_bounded
  using bounded_clinear_zero by blast

notation times_bounded_vec (infixr "*\<^sub>v" 70)

setup_lifting type_definition_bounded

lift_definition rbounded_of_bounded::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded
\<Rightarrow> ('a,'b) rbounded\<close> is "id"
  apply transfer apply auto
  by (simp add: bounded_clinear.bounded_linear)

lemma rbounded_of_bounded_inj:
  \<open>rbounded_of_bounded f = rbounded_of_bounded g \<Longrightarrow> f = g\<close>
  by (metis times_bounded_vec_inject rbounded_of_bounded.rep_eq)

lemma rbounded_of_bounded_inv:
  \<open>\<forall> c. \<forall> x. times_rbounded_vec f (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec f x) \<Longrightarrow> \<exists> g. rbounded_of_bounded g = f\<close>
  apply transfer apply auto
  by (simp add: bounded_linear_bounded_clinear)

lemma rbounded_of_bounded_inv_uniq:
  \<open>\<forall> c. \<forall> x. times_rbounded_vec f (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec f x) \<Longrightarrow> \<exists>! g. rbounded_of_bounded g = f\<close>
  using rbounded_of_bounded_inv rbounded_of_bounded_inj
  by blast

lemma rbounded_of_bounded_prelim:
  \<open>\<forall> c. \<forall> x. times_rbounded_vec (rbounded_of_bounded g) (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec (rbounded_of_bounded g) x)\<close>
  apply transfer
  apply auto
  using bounded_clinear_def
  by (simp add: bounded_clinear_def complex_vector.linear_scale)


definition bounded_of_rbounded::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) rbounded \<Rightarrow>
('a, 'b) bounded\<close> where
  \<open>bounded_of_rbounded = inv rbounded_of_bounded\<close>

lemma bounded_rbounded:
  \<open>bounded_of_rbounded (rbounded_of_bounded f) = f\<close>
  by (metis (no_types, hide_lams) times_bounded_vec_inverse UNIV_I bounded_of_rbounded_def f_inv_into_f image_iff rbounded_of_bounded.rep_eq)

lemma rbounded_bounded:
  \<open>\<forall> c. \<forall> x. times_rbounded_vec f (c *\<^sub>C x)
 = c *\<^sub>C (times_rbounded_vec f x)
 \<Longrightarrow> rbounded_of_bounded (bounded_of_rbounded f) = f\<close> 
  by (metis Abs_bounded_inverse times_rbounded_vec times_rbounded_vec_inject bounded_linear_bounded_clinear bounded_rbounded mem_Collect_eq rbounded_of_bounded.rep_eq)


instantiation bounded :: (complex_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
lift_definition zero_bounded::"('a,'b) bounded" is "\<lambda>_. 0" by simp

lemma bounded_of_rbounded_zero:
  "(0::('a::complex_normed_vector,'b::complex_normed_vector) bounded) = bounded_of_rbounded (0::('a,'b) rbounded)" 
proof-
  have \<open>times_bounded_vec 0 t  = times_bounded_vec (SOME x. Abs_rbounded (times_bounded_vec x) = 0) t\<close>
    for t
  proof-
    have \<open>times_bounded_vec (SOME x. Abs_rbounded (times_bounded_vec x) = 0) t = 0\<close>
      by (metis (mono_tags, lifting) Abs_bounded_inverse times_rbounded_vec_inverse bounded_clinear_zero mem_Collect_eq rbounded_of_bounded.rep_eq tfl_some zero_rbounded.abs_eq)
    moreover have \<open>times_bounded_vec 0 t = 0\<close>
      apply transfer by blast
    ultimately show ?thesis by simp
  qed
  hence \<open>times_bounded_vec 0  = times_bounded_vec (SOME x. Abs_rbounded (times_bounded_vec x) = 0) \<close>
    by blast
  hence \<open>0 = (SOME x. Abs_rbounded (times_bounded_vec x) = 0)\<close>
    using times_bounded_vec_inject
    by blast
  hence \<open>0 = inv (Abs_rbounded \<circ> times_bounded_vec) 0\<close>
    unfolding inv_def
    by auto
  hence \<open>0 = inv (map_fun times_bounded_vec Abs_rbounded id) 0\<close>
    unfolding map_fun_def 
    by auto
  thus ?thesis
    unfolding bounded_of_rbounded_def rbounded_of_bounded_def inv_def
    by blast
qed

lemma rbounded_of_bounded_zero:
  \<open>rbounded_of_bounded 0 = 0\<close>
  apply transfer by simp


lift_definition plus_bounded::"('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>f g x. f x + g x"
  by (rule bounded_clinear_add)

lemma rbounded_of_bounded_plus:
  fixes f g :: \<open>('a,'b) bounded\<close> 
  shows "rbounded_of_bounded (f + g) =  (rbounded_of_bounded f)+(rbounded_of_bounded g)"
  unfolding bounded_of_rbounded_def rbounded_of_bounded_def inv_def
  apply auto
  apply transfer
  by (simp add: bounded_clinear.bounded_linear eq_onp_same_args plus_rbounded.abs_eq)

lemma bounded_of_rbounded_plus:
  assumes \<open>\<forall> c. \<forall> x. times_rbounded_vec f (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec f x)\<close>
    and \<open>\<forall> c. \<forall> x. times_rbounded_vec g (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec g x)\<close>
  shows \<open>bounded_of_rbounded (f + g) = bounded_of_rbounded f + bounded_of_rbounded g\<close>
  using assms
  by (metis rbounded_of_bounded_plus rbounded_bounded rbounded_of_bounded_inj rbounded_of_bounded_prelim)

lift_definition uminus_bounded::"('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>f x. - f x"
  by (rule Complex_Vector_Spaces.bounded_clinear_minus)

lemma rbounded_of_bounded_uminus:
  \<open>rbounded_of_bounded (- f) = - (rbounded_of_bounded f) \<close>
  apply transfer
  by auto

lemma bounded_of_rbounded_uminus:
  assumes \<open>\<forall> c. \<forall> x. times_rbounded_vec f (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec f x)\<close>
  shows  \<open>bounded_of_rbounded (- f) = - (bounded_of_rbounded f)\<close>
  using assms
  by (metis (mono_tags) rbounded_bounded rbounded_of_bounded_inj rbounded_of_bounded_prelim rbounded_of_bounded_uminus)

lift_definition minus_bounded::"('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>f g x. f x - g x"
  by (rule Complex_Vector_Spaces.bounded_clinear_sub)

lemma rbounded_of_bounded_minus:
  \<open>rbounded_of_bounded (f - g) = rbounded_of_bounded f - rbounded_of_bounded g\<close>
  apply transfer
  by auto

lemma bounded_of_rbounded_minus:
  assumes \<open>\<forall> c. \<forall> x. times_rbounded_vec f (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec f x)\<close>
    and \<open>\<forall> c. \<forall> x. times_rbounded_vec g (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec g x)\<close>
  shows \<open>bounded_of_rbounded (f - g) = bounded_of_rbounded f - bounded_of_rbounded g\<close>
  using assms
  unfolding bounded_of_rbounded_def inv_def
  by (smt bounded_rbounded rbounded_bounded rbounded_of_bounded_minus someI_ex)

lift_definition scaleC_bounded :: \<open>complex \<Rightarrow> ('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded\<close>
  is  "\<lambda> c f x. c *\<^sub>C (f x)"
  by (rule Complex_Vector_Spaces.bounded_clinear_const_scaleC)


lemma rbounded_of_bounded_scaleC:
  \<open>rbounded_of_bounded ( c *\<^sub>C f ) = c *\<^sub>C (rbounded_of_bounded f)\<close>
  apply transfer
  by auto

lemma bounded_of_rbounded_scaleC:
  assumes \<open>\<forall> c. \<forall> x. times_rbounded_vec f (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec f x)\<close>
  shows \<open>bounded_of_rbounded ( c *\<^sub>C f ) = c *\<^sub>C (bounded_of_rbounded f)\<close>
  using assms
  by (metis (mono_tags) bounded_rbounded rbounded_bounded rbounded_of_bounded_scaleC)


lift_definition scaleR_bounded :: \<open>real \<Rightarrow> ('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded\<close>
  is  "\<lambda> c f x. c *\<^sub>R (f x)"
  by (rule Complex_Vector_Spaces.scalarR_bounded_clinear)

lemma rbounded_of_bounded_scaleR:
  \<open>rbounded_of_bounded (c *\<^sub>R f) = c *\<^sub>R (rbounded_of_bounded f)\<close>
  apply transfer by auto

lemma bounded_of_rbounded_scaleR:
  assumes \<open>\<forall> c. \<forall> x. times_rbounded_vec f (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec f x)\<close>
  shows \<open>bounded_of_rbounded ( c *\<^sub>R f ) = c *\<^sub>R (bounded_of_rbounded f)\<close>
  using assms
  by (metis (mono_tags) bounded_rbounded rbounded_bounded rbounded_of_bounded_scaleR)

lemma bounded_of_rbounded_Abs_rbounded:
  \<open>bounded_of_rbounded ( Abs_rbounded (times_bounded_vec f) ) = f\<close>
  by (metis Quotient_bounded Quotient_rel_rep times_bounded_vec_inverse bounded_rbounded rbounded_of_bounded.abs_eq)

lift_definition norm_bounded :: \<open>('a, 'b) bounded \<Rightarrow> real\<close>
  is onorm.

lemma rbounded_of_bounded_norm:
  fixes f::\<open>('a, 'b) bounded\<close>
  shows \<open>norm f = norm (rbounded_of_bounded f)\<close>
  apply transfer
  by auto


lift_definition dist_bounded :: \<open>('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. onorm (\<lambda> x. f x - g x)\<close>.

lemma rbounded_of_bounded_dist:
  fixes f::\<open>('a, 'b) bounded\<close>
  shows \<open>dist f g = dist (rbounded_of_bounded f) (rbounded_of_bounded g)\<close>
  apply transfer
  by auto

lift_definition sgn_bounded :: \<open>('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded\<close>
  is \<open>\<lambda> f x. (inverse (onorm f)) *\<^sub>R (f x)\<close>
  apply transfer
  by (simp add: scalarR_bounded_clinear)

lemma rbounded_of_bounded_sgn:
  \<open>rbounded_of_bounded (sgn f) =   (sgn (rbounded_of_bounded f))\<close>
  apply transfer
  by auto


definition uniformity_bounded :: \<open>( ('a, 'b) bounded \<times> ('a, 'b) bounded ) filter\<close>
  where \<open>uniformity_bounded = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a, 'b) bounded) y < e})\<close>

definition open_bounded :: \<open>(('a, 'b) bounded) set \<Rightarrow> bool\<close>
  where \<open>open_bounded U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::('a, 'b) bounded) = x \<longrightarrow> y \<in> U)\<close>

instance
proof
  show \<open>a + b + c = a + (b + c)\<close>
    for a :: "('a, 'b) bounded"
      and b :: "('a, 'b) bounded"
      and c :: "('a, 'b) bounded"
  proof -
    have f1: "\<forall>r ra. ((\<exists>c a. times_rbounded_vec r (c *\<^sub>C (a::'a)) \<noteq> c *\<^sub>C (times_rbounded_vec r a::'b)) \<or> (\<exists>c a. times_rbounded_vec ra (c *\<^sub>C a) \<noteq> c *\<^sub>C times_rbounded_vec ra a)) \<or> bounded_of_rbounded (r + ra) = bounded_of_rbounded r + bounded_of_rbounded ra"
      using bounded_of_rbounded_plus by blast
    obtain cc :: "('a, 'b) rbounded \<Rightarrow> complex" and aa :: "('a, 'b) rbounded \<Rightarrow> 'a" where
      "\<forall>x0. (\<exists>v2 v3. times_rbounded_vec x0 (v2 *\<^sub>C v3) \<noteq> v2 *\<^sub>C times_rbounded_vec x0 v3) = (times_rbounded_vec x0 (cc x0 *\<^sub>C aa x0) \<noteq> cc x0 *\<^sub>C times_rbounded_vec x0 (aa x0))"
      by moura
    then obtain cca :: "('a, 'b) rbounded \<Rightarrow> complex" and aaa :: "('a, 'b) rbounded \<Rightarrow> 'a" where
      f2: "\<forall>r ra. (times_rbounded_vec r (cca r *\<^sub>C aaa r) \<noteq> cca r *\<^sub>C times_rbounded_vec r (aaa r) \<or> times_rbounded_vec ra (cc ra *\<^sub>C aa ra) \<noteq> cc ra *\<^sub>C times_rbounded_vec ra (aa ra)) \<or> bounded_of_rbounded (r + ra) = bounded_of_rbounded r + bounded_of_rbounded ra"
      using f1 by simp
    then have "bounded_of_rbounded (rbounded_of_bounded a + rbounded_of_bounded b + rbounded_of_bounded c) = bounded_of_rbounded (rbounded_of_bounded a + rbounded_of_bounded b) + bounded_of_rbounded (rbounded_of_bounded c)"
      by (simp add: plus_rbounded.rep_eq rbounded_of_bounded_prelim scaleC_add_right)
    then have f3: "bounded_of_rbounded (rbounded_of_bounded a + (rbounded_of_bounded b + rbounded_of_bounded c)) = a + b + c"
      by (metis (mono_tags, lifting) ab_semigroup_add_class.add_ac(1) bounded_rbounded rbounded_of_bounded_plus)
    have "bounded_of_rbounded (rbounded_of_bounded a) + bounded_of_rbounded (rbounded_of_bounded b + rbounded_of_bounded c) = a + (b + c)"
      by (metis bounded_rbounded rbounded_of_bounded_plus)
    then show ?thesis
      using f3 f2 by (simp add: plus_rbounded.rep_eq rbounded_of_bounded_prelim scaleC_add_right)
  qed

  show \<open>(0::('a, 'b) bounded) + a = a\<close>
    for a :: "('a, 'b) bounded"
  proof -
    have "rbounded_of_bounded (map_fun times_bounded_vec (map_fun times_bounded_vec Abs_bounded) (\<lambda>f fa a. f a + fa a) 0 a) = rbounded_of_bounded 0 + rbounded_of_bounded a"
      using Bounded_Operators.rbounded_of_bounded_plus plus_bounded_def by auto
    hence "map_fun times_bounded_vec (map_fun times_bounded_vec Abs_bounded) (\<lambda>f fa a. f a + fa a) 0 a = a"
      by (simp add: Bounded_Operators.rbounded_of_bounded_zero rbounded_of_bounded_inj)
    thus ?thesis
      unfolding plus_bounded_def
      by blast
  qed

  show \<open>a + b = b + a\<close>
    for a :: "('a, 'b) bounded"
      and b :: "('a, 'b) bounded"
    by (simp add: add.commute plus_bounded_def)

  show \<open>- a + a = 0\<close>
    for a :: "('a, 'b) bounded"
    by (metis (mono_tags) add.left_inverse bounded_of_rbounded_zero bounded_rbounded rbounded_of_bounded_plus rbounded_of_bounded_uminus)

  show \<open>a - b = a + - b\<close>
    for a :: "('a, 'b) bounded"
      and b :: "('a, 'b) bounded"
    by (metis (mono_tags, lifting) ab_group_add_class.ab_diff_conv_add_uminus rbounded_of_bounded_inj rbounded_of_bounded_minus rbounded_of_bounded_plus rbounded_of_bounded_uminus)

  show \<open>((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
    for r :: real
  proof-
    have \<open>r *\<^sub>R times_bounded_vec f t =
          complex_of_real r *\<^sub>C times_bounded_vec f t\<close>
      for f::\<open>('a, 'b) bounded\<close> and t
      by (simp add: scaleR_scaleC)      
    hence \<open>(\<lambda>t. r *\<^sub>R times_bounded_vec f t) t =
          (\<lambda>t. complex_of_real r *\<^sub>C times_bounded_vec f t) t\<close>
      for f::\<open>('a, 'b) bounded\<close> and t
      by simp      
    hence \<open>(\<lambda>t. r *\<^sub>R times_bounded_vec f t) =
          (\<lambda>t. complex_of_real r *\<^sub>C times_bounded_vec f t)\<close>
      for f::\<open>('a, 'b) bounded\<close>
      by simp
    hence \<open>Abs_bounded (\<lambda>t. r *\<^sub>R times_bounded_vec f t) =
    Abs_bounded
          (\<lambda>t. complex_of_real r *\<^sub>C times_bounded_vec f t)\<close>
      for f::\<open>('a, 'b) bounded\<close>
      by simp
    hence \<open>(\<lambda>f. Abs_bounded (\<lambda>t. r *\<^sub>R times_bounded_vec f t)) f =
    (\<lambda>f. Abs_bounded
          (\<lambda>t. complex_of_real r *\<^sub>C times_bounded_vec f t)) f\<close>
      for f::\<open>('a, 'b) bounded\<close>
      by blast
    hence \<open>(\<lambda>f. Abs_bounded (\<lambda>t. r *\<^sub>R times_bounded_vec f t)) =
    (\<lambda>f. Abs_bounded
          (\<lambda>t. complex_of_real r *\<^sub>C times_bounded_vec f t))\<close>
      by (simp add: scaleR_scaleC)      
    thus ?thesis
      unfolding scaleR_bounded_def scaleC_bounded_def o_def rbounded_of_bounded_def map_fun_def
      by auto
  qed
  show \<open>a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    for a :: complex
      and x :: "('a, 'b) bounded"
      and y :: "('a, 'b) bounded"
    by (simp add: rbounded_of_bounded_inj rbounded_of_bounded_plus rbounded_of_bounded_scaleC scaleC_add_right)

  show \<open>(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x\<close>
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) bounded"
    by (simp add: rbounded_of_bounded_inj rbounded_of_bounded_plus rbounded_of_bounded_scaleC scaleC_left.add)

  show \<open>a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x\<close>
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) bounded"
    by (simp add: rbounded_of_bounded_inj rbounded_of_bounded_scaleC)

  show \<open>1 *\<^sub>C x = x\<close>
    for x :: "('a, 'b) bounded"
    by (simp add: rbounded_of_bounded_inj rbounded_of_bounded_scaleC)

  show \<open>dist x y = norm (x - y)\<close>
    for x :: "('a, 'b) bounded"
      and y :: "('a, 'b) bounded"
    by (simp add: dist_norm rbounded_of_bounded_dist rbounded_of_bounded_minus rbounded_of_bounded_norm)

  show \<open>sgn x = (inverse (norm x)) *\<^sub>R x\<close>
    for x :: "('a, 'b) bounded"
    by (simp add: norm_bounded_def scaleR_bounded_def sgn_bounded_def sgn_div_norm)

  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a, 'b) bounded) y < e})\<close>
    by (simp add: Bounded_Operators.uniformity_bounded_def)

  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::('a, 'b) bounded) = x \<longrightarrow> y \<in> U)\<close>
    for U :: "('a, 'b) bounded set"
    by (simp add: Bounded_Operators.open_bounded_def)

  show \<open>(norm x = 0) = (x = 0)\<close>
    for x :: "('a, 'b) bounded"
  proof -
    have f1: "bounded_of_rbounded (0::('a, 'b) rbounded) = 0"
      by (simp add: bounded_of_rbounded_zero)

    { assume "x \<noteq> 0"
      then have "x \<noteq> 0 \<and> bounded_of_rbounded 0 \<noteq> x"
        using f1 by meson
      hence ?thesis
        by (metis bounded_rbounded norm_eq_zero rbounded_of_bounded_norm)
    }
    thus ?thesis
      using rbounded_of_bounded_norm rbounded_of_bounded_zero by auto     
  qed

  show \<open>norm (x + y) \<le> norm x + norm y\<close>
    for x :: "('a, 'b) bounded"
      and y :: "('a, 'b) bounded"
    by (simp add: norm_triangle_ineq rbounded_of_bounded_norm rbounded_of_bounded_plus)

  show \<open>norm (a *\<^sub>C x) = cmod a * norm x\<close>
    for a :: complex
      and x :: "('a, 'b) bounded"
    using rbounded_of_bounded_norm rbounded_of_bounded_scaleC by auto


  show \<open>norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x\<close>
    for a :: real
      and x :: "('a, 'b) bounded"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x a. norm (a *\<^sub>C x) = cmod a * norm (x::('a, 'b) bounded)\<close>
      of_real_mult
    by simp

  show \<open>a *\<^sub>R (x + y) = a *\<^sub>R x +  a *\<^sub>R y\<close>
    for a :: real
      and x y :: "('a, 'b) bounded"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x y a. a *\<^sub>C (x + y) = a *\<^sub>C x +  a *\<^sub>C (y::('a, 'b) bounded)\<close>
      of_real_mult
    by simp

  show \<open>(a + b) *\<^sub>R x = a *\<^sub>R x +  b *\<^sub>R x\<close>
    for a b :: real
      and x :: "('a, 'b) bounded"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x b a. (a + b) *\<^sub>C (x::('a,'b) bounded) = a *\<^sub>C x +  b *\<^sub>C x\<close>
      of_real_mult
    by simp

  show \<open>a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x\<close>
    for a b :: real
      and x :: "('a, 'b) bounded"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x b a. a *\<^sub>C b *\<^sub>C (x::('a, 'b) bounded) = (a * b) *\<^sub>C x\<close>
      of_real_mult
    by simp

  show \<open>1 *\<^sub>R x = x\<close>
    for x :: "('a, 'b) bounded"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x. 1 *\<^sub>C (x::('a, 'b) bounded) = x\<close> of_real_1
    by simp

qed

end


instantiation bounded :: (complex_normed_vector, cbanach) "cbanach"
begin
lemma rbounded_of_bounded_Cauchy:
  assumes \<open>Cauchy f\<close>
  shows \<open>Cauchy (\<lambda> n. rbounded_of_bounded (f n))\<close>
  using assms unfolding Cauchy_def
  by (simp add: rbounded_of_bounded_dist)  


lemma bounded_of_rbounded_Cauchy:
  assumes \<open>Cauchy f\<close> and
    \<open>\<And> n::nat. \<forall> c. \<forall> x. times_rbounded_vec (f n) (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec (f n) x)\<close>
  shows \<open>Cauchy (\<lambda> n. bounded_of_rbounded (f n))\<close>
  using assms  unfolding Cauchy_def 
  using rbounded_of_bounded_dist
  apply auto
  by (simp add: rbounded_bounded rbounded_of_bounded_dist)

lemma rbounded_of_bounded_lim:
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda> n. rbounded_of_bounded (f n)) \<longlonglongrightarrow> rbounded_of_bounded l\<close>
proof
  show "\<forall>\<^sub>F x in sequentially. dist (rbounded_of_bounded (f x)) (rbounded_of_bounded l) < e"
    if "(0::real) < e"
    for e :: real
  proof-
    from \<open>f \<longlonglongrightarrow> l\<close>
    have \<open>\<forall>\<^sub>F x in sequentially. dist (f x) l < e\<close>
      by (simp add: tendstoD that)
    thus ?thesis 
      unfolding rbounded_of_bounded_dist by blast
  qed
qed

lemma bounded_of_rbounded_complex_lim:
  fixes f::\<open>nat \<Rightarrow> ('a::complex_normed_vector, 'b::cbanach) rbounded\<close>
    and l::\<open>('a, 'b) rbounded\<close>
  assumes  \<open>f \<longlonglongrightarrow> l\<close> and
    \<open>\<And> n::nat. \<forall> c. \<forall> x. times_rbounded_vec (f n) (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec (f n) x)\<close> 
  shows \<open>\<forall> c. \<forall> x. times_rbounded_vec l (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec l x)\<close>
proof-
  have \<open>times_rbounded_vec l (c *\<^sub>C x) = c *\<^sub>C times_rbounded_vec l x\<close>
    for c::complex and x
  proof-
    have \<open>(\<lambda> n. times_rbounded_vec (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> times_rbounded_vec l (c *\<^sub>C x)\<close>
      by (simp add: assms(1) onorm_strong)        
    moreover have \<open>(\<lambda> n. c *\<^sub>C (times_rbounded_vec (f n) x) ) \<longlonglongrightarrow> c *\<^sub>C (times_rbounded_vec l x)\<close>
    proof-
      have \<open>isCont ((*\<^sub>C) c) y\<close>
        for y::'b
        using isCont_scaleC by auto
      hence \<open>isCont ((*\<^sub>C) c) (times_rbounded_vec l x)\<close>
        by simp
      thus ?thesis
        using assms(1) isCont_tendsto_compose onorm_strong by blast 
    qed
    moreover have \<open>times_rbounded_vec (f n) (c *\<^sub>C x) =  c *\<^sub>C (times_rbounded_vec (f n) x)\<close>
      for n
      by (simp add: assms(2))
    ultimately have \<open>(\<lambda> n. times_rbounded_vec (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> c *\<^sub>C (times_rbounded_vec l x)\<close>
      by simp
    thus ?thesis
      using  \<open>(\<lambda> n. times_rbounded_vec (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> times_rbounded_vec l (c *\<^sub>C x)\<close> LIMSEQ_unique 
      by blast
  qed
  thus ?thesis by blast
qed  

lemma bounded_of_rbounded_lim:
  fixes f::\<open>nat \<Rightarrow> ('a::complex_normed_vector, 'b::cbanach) rbounded\<close>
    and l::\<open>('a, 'b) rbounded\<close>
  assumes  \<open>f \<longlonglongrightarrow> l\<close> and
    \<open>\<And> n::nat. \<forall> c. \<forall> x. times_rbounded_vec (f n) (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec (f n) x)\<close>
  shows \<open>(\<lambda> n. bounded_of_rbounded (f n)) \<longlonglongrightarrow> bounded_of_rbounded l\<close>
proof
  show "\<forall>\<^sub>F x in sequentially. dist (bounded_of_rbounded (f x)) (bounded_of_rbounded l) < e"
    if "(0::real) < e"
    for e :: real
  proof-
    from \<open>f \<longlonglongrightarrow> l\<close>
    have \<open>\<forall>\<^sub>F x in sequentially. dist (f x) l < e\<close>
      by (simp add: tendstoD that)
    moreover have \<open>rbounded_of_bounded (bounded_of_rbounded (f n)) = f n\<close>
      for n
      by (simp add: assms(2) rbounded_bounded)
    moreover have \<open>rbounded_of_bounded (bounded_of_rbounded l) = l\<close>
    proof-
      have \<open>\<forall> c. \<forall> x. times_rbounded_vec l (c *\<^sub>C x) = c *\<^sub>C (times_rbounded_vec l x)\<close>
        using assms(1) assms(2) bounded_of_rbounded_complex_lim by blast        
      thus ?thesis
        by (simp add: rbounded_bounded) 
    qed
    ultimately show ?thesis 
      unfolding rbounded_of_bounded_dist
      by simp  
  qed    
qed

instance 
proof
  show "convergent f"
    if "Cauchy f"
    for f :: "nat \<Rightarrow> ('a, 'b) bounded"
  proof-
    have \<open>Cauchy (\<lambda> n. rbounded_of_bounded (f n))\<close>
      by (simp add: rbounded_of_bounded_Cauchy that)
    hence \<open>convergent (\<lambda> n. rbounded_of_bounded (f n))\<close>
      by (simp add: Cauchy_convergent_iff)
    hence \<open>\<exists> l. (\<lambda> n. rbounded_of_bounded (f n)) \<longlonglongrightarrow> rbounded_of_bounded l\<close>
      by (metis (no_types, lifting) Bounded_Operators.bounded_of_rbounded_complex_lim convergent_LIMSEQ_iff rbounded_bounded rbounded_of_bounded_prelim)
    then obtain l where \<open>(\<lambda> n. rbounded_of_bounded (f n)) \<longlonglongrightarrow> rbounded_of_bounded l\<close>
      by blast
    hence \<open>(\<lambda> n. bounded_of_rbounded (rbounded_of_bounded (f n))) \<longlonglongrightarrow> bounded_of_rbounded (rbounded_of_bounded l)\<close>
      by (simp add: Bounded_Operators.bounded_of_rbounded_lim rbounded_of_bounded_prelim)
    hence \<open>f \<longlonglongrightarrow> l\<close>
      by (simp add: bounded_rbounded)
    thus ?thesis
      using convergent_def by blast 
  qed
qed
end


section \<open>Adjoint\<close>

lift_definition
  adjoint :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> ('b,'a) bounded" ("_*" [99] 100)
  is Adj by (fact Adj_bounded_clinear)

lemma adjoint_I:
  fixes G :: "('b::chilbert_space, 'a::chilbert_space) bounded"
  shows \<open>\<forall>x. \<forall>y. \<langle>(G*) *\<^sub>v x, y\<rangle> = \<langle>x, G *\<^sub>v y\<rangle>\<close>
  apply transfer using Adj_I by blast

lemma adjoint_D:
  fixes G:: \<open>('b::chilbert_space, 'a::chilbert_space) bounded\<close>
    and F:: \<open>('a, 'b) bounded\<close>
  assumes \<open>\<And>x y. \<langle>(times_bounded_vec F) x, y\<rangle> = \<langle>x, (times_bounded_vec G) y\<rangle>\<close>
  shows \<open>F = G*\<close>
  using assms apply transfer using Adj_D by auto

lemma adjoint_twice[simp]: "(U*)* = U" 
  for U :: "('a::chilbert_space,'b::chilbert_space) bounded"
  apply transfer
  using dagger_dagger_id by blast

lift_definition idOp::\<open>('a::complex_normed_vector,'a) bounded\<close> is id
  using id_bounded_clinear by blast

lemma idOp_adjoint[simp]: "idOp* = idOp"
  apply transfer using id_dagger by blast

lemma scalar_times_adj[simp]: "(a *\<^sub>C A)* = (cnj a) *\<^sub>C (A*)" 
  for A::"('a::chilbert_space,'b::chilbert_space) bounded"
    and a :: complex 
proof-
  have \<open>bounded_clinear ((times_bounded_vec A))\<close>
    using times_bounded_vec by blast
  hence \<open>(\<lambda> t. a *\<^sub>C ((times_bounded_vec A) t))\<^sup>\<dagger> = (\<lambda> s. (cnj a) *\<^sub>C (((times_bounded_vec A)\<^sup>\<dagger>) s))\<close>
    using scalar_times_adjc_flatten
    unfolding bounded_clinear_def 
      scalar_times_adjc_flatten \<open>bounded_clinear (times_bounded_vec A)\<close> bounded_clinear.bounded_linear
    by (simp add: scalar_times_adjc_flatten \<open>bounded_clinear ((*\<^sub>v) A)\<close> bounded_clinear.bounded_linear complex_vector.linear_scale)

  moreover have \<open>times_bounded_vec ((a *\<^sub>C A)*) = (\<lambda> t. a *\<^sub>C ((times_bounded_vec A) t))\<^sup>\<dagger>\<close>
    unfolding Adj_def
    apply auto
    by (smt Adj_def Eps_cong adjoint.rep_eq cinner_scaleC_right scaleC_bounded.rep_eq)
  moreover have \<open>times_bounded_vec (cnj a *\<^sub>C (A*)) = (\<lambda> s. (cnj a) *\<^sub>C (((times_bounded_vec A)\<^sup>\<dagger>) s))\<close>
    unfolding Adj_def
    by (simp add: Adj_def adjoint.rep_eq scaleC_bounded.rep_eq)    
  ultimately show ?thesis
    using times_bounded_vec_inject
    by fastforce 
qed

lemma Adj_bounded_plus:
  fixes A B :: \<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close>
  shows \<open>(A + B)* = (A*) + (B*)\<close>
proof transfer
  fix A B::\<open>'a \<Rightarrow> 'b\<close>
  assume \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close>
  define F where \<open>F = (\<lambda>x. (A\<^sup>\<dagger>) x + (B\<^sup>\<dagger>) x)\<close>
  define G where \<open>G = (\<lambda>x. A x + B x)\<close>
  have \<open>bounded_clinear G\<close>
    unfolding G_def
    by (simp add: \<open>bounded_clinear A\<close> \<open>bounded_clinear B\<close> bounded_clinear_add)
  moreover have \<open>\<langle>  F u,  v \<rangle> = \<langle> u, G v \<rangle>\<close>
    for u::'b and v::'a
    unfolding F_def G_def
    by (simp add: Adj_I \<open>bounded_clinear A\<close> \<open>bounded_clinear B\<close> bounded_sesquilinear.add_right bounded_sesquilinear_cinner cinner_left_distrib)
  ultimately have \<open>F = G\<^sup>\<dagger> \<close>
    by (rule Adj_D)
  thus \<open>(\<lambda>x. A x + B x)\<^sup>\<dagger> = (\<lambda>x. (A\<^sup>\<dagger>) x + (B\<^sup>\<dagger>) x)\<close>
    unfolding F_def G_def
    by auto
qed

lemma Adj_bounded_uminus[simp]:
  \<open>(- A)* = - (A*)\<close>
  by (metis (no_types, lifting) Adj_bounded_plus  add_cancel_left_right diff_0 ordered_field_class.sign_simps(9))

lemma Adj_bounded_minus[simp]:
  \<open>(A - B)* = (A*) - (B*)\<close>
  by (metis Adj_bounded_plus add_right_cancel diff_add_cancel)


lemma Adj_bounded_zero[simp]:
  \<open>0* = 0\<close>
  by (metis Adj_bounded_plus add_cancel_right_right)

section \<open>Composition\<close>

lift_definition timesOp:: 
  "('b::complex_normed_vector,'c::complex_normed_vector) bounded
     \<Rightarrow> ('a::complex_normed_vector,'b) bounded \<Rightarrow> ('a,'c) bounded"
  is "(o)"
  unfolding o_def 
  by (rule bounded_clinear_compose, simp_all)

(* Closure is necessary. See thunderlink://messageid=47a3bb3d-3cc3-0934-36eb-3ef0f7b70a85@ut.ee *)
lift_definition applyOpSpace::\<open>('a::complex_normed_vector,'b::complex_normed_vector) bounded
\<Rightarrow> 'a linear_space \<Rightarrow> 'b linear_space\<close> 
  is "\<lambda>A S. closure (A ` S)"
  using  bounded_clinear_def closed_closure  closed_subspace.intro
  by (simp add: bounded_clinear_def closed_subspace.subspace complex_vector.linear_subspace_image subspace_I) 

bundle bounded_notation begin
notation timesOp (infixl "*\<^sub>o" 69)
notation times_bounded_vec (infixr "*\<^sub>v" 70)
notation applyOpSpace (infixr "*\<^sub>s" 70)
notation adjoint ("_*" [99] 100)
end

bundle no_bounded_notation begin
no_notation timesOp (infixl "*\<^sub>o" 69)
no_notation times_bounded_vec (infixr "*\<^sub>v" 70)
no_notation applyOpSpace (infixr "*\<^sub>s" 70)
no_notation adjoint ("_*" [99] 100)
end

unbundle bounded_notation

lemma rbounded_of_bounded_timesOp:
  fixes f::\<open>('b::complex_normed_vector,'c::complex_normed_vector) bounded\<close>
    and g::\<open>('a::complex_normed_vector,'b) bounded\<close>
  shows \<open>rbounded_of_bounded (f *\<^sub>o g) = times_rbounded (rbounded_of_bounded f) (rbounded_of_bounded g)\<close> 
  apply transfer
  by auto

lemma timesOp_assoc: 
  shows "(A *\<^sub>o B) *\<^sub>o C = A  *\<^sub>o (B  *\<^sub>o C)"
  by (metis (no_types, lifting) times_bounded_vec_inject fun.map_comp timesOp.rep_eq)


lemma timesOp_dist1:  
  fixes a b :: "('b::complex_normed_vector, 'c::complex_normed_vector) bounded"
    and c :: "('a::complex_normed_vector, 'b) bounded"
  shows "(a + b) *\<^sub>o c = (a *\<^sub>o c) + (b *\<^sub>o c)"
  using rbounded_of_bounded_inj rbounded_of_bounded_plus rbounded_of_bounded_timesOp
  by (simp add: rbounded_of_bounded_inj rbounded_of_bounded_plus rbounded_of_bounded_timesOp times_rbounded_dist1)


lemma timesOp_dist2:  
  fixes a b :: "('a::complex_normed_vector, 'b::complex_normed_vector) bounded"
    and c :: "('b, 'c::complex_normed_vector) bounded"
  shows "c *\<^sub>o (a + b) = (c *\<^sub>o a) + (c *\<^sub>o b)"
  using  rbounded_of_bounded_inj rbounded_of_bounded_plus rbounded_of_bounded_timesOp
  by (simp add: rbounded_of_bounded_inj rbounded_of_bounded_plus rbounded_of_bounded_timesOp times_rbounded_dist2)


lemma timesOp_minus:
  \<open>A *\<^sub>o (B - C) = A *\<^sub>o B - A *\<^sub>o C\<close>
  apply transfer
  using  bounded_clinear_def
  by (metis comp_apply complex_vector.linear_diff)


lemma times_adjoint[simp]:
  fixes B::\<open>('a::chilbert_space,'b::chilbert_space) bounded\<close>
    and A::\<open>('b,'c::chilbert_space) bounded\<close> 
  shows "(A *\<^sub>o B)* =  (B*) *\<^sub>o (A*)"
proof transfer
  fix  A :: \<open>'b\<Rightarrow>'c\<close> and B :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close>
  hence \<open>bounded_clinear (A \<circ> B)\<close>
    by (simp add: comp_bounded_clinear)
  have \<open>\<langle> (A \<circ> B) u, v \<rangle> = \<langle> u, (B\<^sup>\<dagger> \<circ> A\<^sup>\<dagger>) v \<rangle>\<close>
    for u v
    by (metis (no_types, lifting) Adj_I \<open>bounded_clinear A\<close> \<open>bounded_clinear B\<close> cinner_commute' comp_def)    
  thus \<open>(A \<circ> B)\<^sup>\<dagger> = B\<^sup>\<dagger> \<circ> A\<^sup>\<dagger>\<close>
    using \<open>bounded_clinear (A \<circ> B)\<close>
    by (metis Adj_D cinner_commute')
qed

lemma times_bounded_vec_0[simp]:  
  fixes U::\<open>('a::complex_normed_vector,'b::complex_normed_vector) bounded\<close>
  shows  "U *\<^sub>v 0 = 0"
  apply transfer
  unfolding bounded_clinear_def
  by (simp add: complex_vector.linear_0)


lemma applyOp_0[simp]:  
  fixes U::\<open>('a::complex_normed_vector,'b::complex_normed_vector) bounded\<close>
  shows   "U *\<^sub>s (0::'a linear_space) = (0::'b linear_space)"
proof-
  {
    have \<open>bounded_clinear U \<Longrightarrow>
          (closure
            (U ` {0})) = {0}\<close>
      for U::\<open>'a\<Rightarrow>'b\<close>
    proof-
      assume \<open>bounded_clinear U\<close>
      have \<open>U ` {0} = {U 0}\<close>
        by auto
      moreover have \<open>U 0 = 0\<close>
        using \<open>bounded_clinear U\<close>
        unfolding bounded_clinear_def
        by (simp add: complex_vector.linear_0)
      ultimately have \<open>U ` {0} = {0}\<close>
        by simp
      thus ?thesis
        by simp 
    qed
    hence \<open>bounded_clinear U \<Longrightarrow>
         Abs_linear_space
          (closure
            (U ` {0})) =
         Abs_linear_space {0}\<close>
      for U::\<open>'a\<Rightarrow>'b\<close>
      using Abs_linear_space_inject
      by presburger
    hence \<open>bounded_clinear U \<Longrightarrow>
         Abs_linear_space
          (closure (U ` space_as_set (Abs_linear_space {0}))) =
         Abs_linear_space {0}\<close>
      for U::\<open>'a\<Rightarrow>'b\<close>
      by (simp add: Abs_linear_space_inverse)  } note 1 = this
  thus ?thesis
    unfolding zero_linear_space_def applyOpSpace_def
    apply auto
    using 1
    by (metis times_bounded_vec_0 bot_linear_space.abs_eq bot_linear_space.rep_eq closure_empty closure_insert image_empty image_insert)  
qed

lemma times_comp: \<open>\<And>A B \<psi>.
       bounded_clinear A \<Longrightarrow>
       bounded_clinear B \<Longrightarrow>
       closed_subspace \<psi> \<Longrightarrow>
       closure ( (A \<circ> B) ` \<psi>) = closure (A ` closure (B ` \<psi>))\<close>
proof
  show "closure ((A \<circ> B) ` (\<psi>::'c set)::'b set) \<subseteq> closure (A ` closure (B ` \<psi>::'a set))"
    if "bounded_clinear (A::'a \<Rightarrow> 'b)"
      and "bounded_clinear (B::'c \<Rightarrow> 'a)"
      and "closed_subspace (\<psi>::'c set)"
    for A :: "'a \<Rightarrow> 'b"
      and B :: "'c \<Rightarrow> 'a"
      and \<psi> :: "'c set"
    using that
    by (metis closure_mono closure_subset image_comp image_mono) 
  show "closure (A ` closure (B ` (\<psi>::'c set)::'a set)) \<subseteq> closure ((A \<circ> B) ` \<psi>::'b set)"
    if "bounded_clinear (A::'a \<Rightarrow> 'b)"
      and "bounded_clinear (B::'c \<Rightarrow> 'a)"
      and "closed_subspace (\<psi>::'c set)"
    for A :: "'a \<Rightarrow> 'b"
      and B :: "'c \<Rightarrow> 'a"
      and \<psi> :: "'c set"
    using that 
  proof-
    have \<open>A ` closure (B ` \<psi>) \<subseteq> closure ((A \<circ> B) ` \<psi>)\<close>
    proof
      show "x \<in> closure ((A \<circ> B) ` \<psi>)"
        if "x \<in> A ` closure (B ` \<psi>)"
        for x :: 'b
        using that
      proof-
        have \<open>\<exists> t::nat \<Rightarrow> 'b. (\<forall> n. t n \<in> (A \<circ> B) ` \<psi>) \<and> (t \<longlonglongrightarrow> x)\<close>
        proof-
          have \<open>\<exists> y\<in>closure (B ` \<psi>). x = A y\<close>
            using that by blast
          then obtain y where \<open>y\<in>closure (B ` \<psi>)\<close> and \<open>x = A y\<close>
            by blast
          from \<open>y\<in>closure (B ` \<psi>)\<close>
          have \<open>\<exists> s::nat \<Rightarrow> 'a. (\<forall>n. s n \<in> B ` \<psi>) \<and> s \<longlonglongrightarrow> y\<close>
            using closure_sequential by blast
          then obtain s::\<open>nat\<Rightarrow>'a\<close> where \<open>\<forall>n. s n \<in> B ` \<psi>\<close> and \<open>s \<longlonglongrightarrow> y\<close>
            by blast
          define t::"nat \<Rightarrow> 'b" where \<open>t n = A (s n)\<close> for n::nat
          have \<open>\<forall>n. t n \<in> (A \<circ> B) ` \<psi>\<close>
            by (metis \<open>\<forall>n. s n \<in> B ` \<psi>\<close> imageI image_comp t_def)
          moreover have \<open>t \<longlonglongrightarrow> x\<close>
          proof-
            have \<open>isCont A y\<close>
              using \<open>bounded_clinear A\<close>
              by (simp add: bounded_linear_continuous) 
            thus ?thesis unfolding t_def using \<open>s \<longlonglongrightarrow> y\<close>
              by (simp add: \<open>x = A y\<close> isCont_tendsto_compose) 
          qed
          ultimately have "(\<forall>n. t n \<in> (A \<circ> B) ` \<psi>) \<and> t \<longlonglongrightarrow> x"
            by blast
          thus ?thesis by blast
        qed
        thus ?thesis
          using closure_sequential by blast 
      qed
    qed
    thus ?thesis
      by (metis closure_closure closure_mono) 
  qed
qed

lemma timesOp_assoc_linear_space: 
  shows  \<open>(A *\<^sub>o B) *\<^sub>s \<psi> =  A *\<^sub>s (B *\<^sub>s \<psi>)\<close>
proof-
  have \<open>bounded_clinear (times_bounded_vec A)\<close>
    using times_bounded_vec by auto
  moreover have \<open>bounded_clinear (times_bounded_vec B)\<close>
    using times_bounded_vec by auto
  moreover have \<open>closed_subspace (space_as_set \<psi>)\<close>
    using space_as_set by auto
  ultimately have  \<open>
     (closure
       ( (times_bounded_vec A \<circ> times_bounded_vec B) ` space_as_set \<psi>)) =
     (closure
       (times_bounded_vec A `
      closure (times_bounded_vec B ` space_as_set \<psi>)))\<close>
    using times_comp by blast
  hence  \<open>
     (closure
       ( (times_bounded_vec A \<circ> times_bounded_vec B) ` space_as_set \<psi>)) =
     (closure
       (times_bounded_vec A `
        space_as_set
         (Abs_linear_space
           (closure (times_bounded_vec B ` space_as_set \<psi>)))))\<close>
    by (metis space_as_set_inverse applyOpSpace.rep_eq)    
  hence  \<open>
     (closure
       (times_bounded_vec (timesOp A B) ` space_as_set \<psi>)) =
     (closure
       (times_bounded_vec A `
        space_as_set
         (Abs_linear_space
           (closure (times_bounded_vec B ` space_as_set \<psi>)))))\<close>
    by (simp add: timesOp.rep_eq)    
  hence \<open> Abs_linear_space
     (closure
       (times_bounded_vec (timesOp A B) ` space_as_set \<psi>)) =
    Abs_linear_space
     (closure
       (times_bounded_vec A `
        space_as_set
         (Abs_linear_space
           (closure (times_bounded_vec B ` space_as_set \<psi>)))))\<close>
    using Abs_linear_space_inject by auto
  thus ?thesis
    unfolding applyOpSpace_def
    by auto
qed


lemmas assoc_left = timesOp_assoc[symmetric] timesOp_assoc_linear_space[symmetric] add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded", symmetric]
lemmas assoc_right = timesOp_assoc timesOp_assoc_linear_space add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded"]

lemma scalar_times_op_add[simp]: "a *\<^sub>C (A+B) = a *\<^sub>C A + a *\<^sub>C B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  by (simp add: scaleC_add_right)

lemma scalar_times_op_minus[simp]: "a *\<^sub>C (A-B) =  a *\<^sub>C A - a *\<^sub>C B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  by (simp add: complex_vector.scale_right_diff_distrib)


lemma applyOp_bot[simp]:
fixes U::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> 
shows "U *\<^sub>s bot = bot"
proof-
  have \<open>closed {0::'a}\<close>
    using Topological_Spaces.t1_space_class.closed_singleton by blast
  hence \<open>closure {0::'a} = {0}\<close>
    by (simp add: closure_eq)    
  moreover have \<open>times_bounded_vec U ` {0::'a} = {0}\<close>
  proof-
    have \<open>bounded_clinear (times_bounded_vec U)\<close>
      using times_bounded_vec by auto
    hence  \<open>times_bounded_vec U 0 = 0\<close>
      by (simp add: bounded_clinear.clinear clinear_zero)
    thus ?thesis
      by simp 
  qed
  ultimately have \<open>closure (times_bounded_vec U ` {0}) = {0}\<close>
    by simp
  hence \<open>(closure (times_bounded_vec U ` space_as_set (Abs_linear_space {0}))) = {0}\<close>
    by (metis bot_linear_space.abs_eq bot_linear_space.rep_eq) 
  thus ?thesis
    unfolding applyOpSpace_def bot_linear_space_def by simp
qed



lemma cdot_plus_distrib_transfer:
  \<open>bounded_clinear U \<Longrightarrow>
       closed_subspace A \<Longrightarrow>
       closed_subspace B \<Longrightarrow>
        (closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
  for U::\<open>'a::complex_normed_vector\<Rightarrow>'b::complex_normed_vector\<close> and A B::\<open>'a set\<close>
proof-
  assume \<open>bounded_clinear U\<close> and \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close> 
  have \<open>(closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
  proof-
    have \<open>U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} \<subseteq>
          {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
    proof-
      have \<open>U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} = {U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
        by auto
      moreover have \<open> {U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}
                      = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}\<close>
      proof-
        have \<open>{U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} = {U \<psi> + U \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
          using \<open>bounded_clinear U\<close>
          unfolding bounded_clinear_def
          by (metis (no_types, lifting) complex_vector.linear_add) 

        also have \<open>{U \<psi> + U \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} 
            = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}\<close>
          by blast
        finally show ?thesis by blast
      qed
      moreover have \<open>{\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}
           \<subseteq> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
        by (smt Collect_mono_iff closure_subset subsetD)
      ultimately show ?thesis
        by simp 
    qed
    hence \<open>closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
      by (simp add: closure_mono)      
    moreover have \<open>(U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})
            \<subseteq> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
    proof-
      define S where \<open>S = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
      from  \<open>bounded_clinear U\<close>
      have \<open>isCont U x\<close>
        for x
        by (simp add: bounded_linear_continuous)
      hence \<open>continuous_on (closure S) U\<close>
        by (simp add: continuous_at_imp_continuous_on)
      hence \<open>U ` (closure S) \<subseteq> closure (U ` S)\<close>
        using Abstract_Topology_2.image_closure_subset
        by (simp add: image_closure_subset closure_subset)
      thus ?thesis unfolding S_def by blast
    qed
    ultimately have \<open>(U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
      by blast
    thus ?thesis
      by (metis (no_types, lifting) closure_closure closure_mono) 
  qed
  moreover have \<open>(closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})
      \<subseteq> closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
  proof-
    have \<open>x \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}
      \<Longrightarrow> x \<in> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
      for x
    proof-
      assume \<open>x \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
      then obtain \<psi> \<phi> where \<open>x =  \<psi> + \<phi>\<close>  and \<open>\<psi> \<in> closure (U ` A)\<close> and \<open>\<phi> \<in> closure (U ` B)\<close>
        by blast
      from  \<open>\<psi> \<in> closure (U ` A)\<close>
      have \<open>\<exists> psiU. (\<forall> n. psiU n \<in> (U ` A)) \<and> (\<lambda> n. psiU n) \<longlonglongrightarrow> \<psi>\<close>
        using closure_sequential by blast
      then obtain psiU where \<open>\<forall> n. psiU n \<in> (U ` A)\<close> and \<open>(\<lambda> n. psiU n) \<longlonglongrightarrow> \<psi>\<close>
        by blast
      from \<open>\<forall> n. psiU n \<in> (U ` A)\<close>
      have \<open>\<forall> n. \<exists> psi.  psiU n = U psi \<and> psi \<in> A\<close>
        by blast
      hence \<open>\<exists> psi. \<forall> n. psiU n = U (psi n) \<and> psi n \<in> A\<close>
        by metis
      then obtain psi where \<open>\<forall> n. psiU n = U (psi n)\<close> and \<open>\<forall> n. psi n \<in> A\<close>
        by blast
      have  \<open>(\<lambda> n. U (psi n)) \<longlonglongrightarrow> \<psi>\<close>
        using \<open>(\<lambda> n. psiU n) \<longlonglongrightarrow> \<psi>\<close> \<open>\<forall> n. psiU n = U (psi n)\<close>
        by simp
      from  \<open>\<phi> \<in> closure (U ` B)\<close>
      have \<open>\<exists> phiU. (\<forall> n. phiU n \<in> (U ` B)) \<and> (\<lambda> n. phiU n) \<longlonglongrightarrow> \<phi>\<close>
        using closure_sequential by blast
      then obtain phiU where \<open>\<forall> n. phiU n \<in> (U ` B)\<close> and \<open>(\<lambda> n. phiU n) \<longlonglongrightarrow> \<phi>\<close>
        by blast
      from \<open>\<forall> n. phiU n \<in> (U ` B)\<close>
      have \<open>\<forall> n. \<exists> phi.  phiU n = U phi \<and> phi \<in> B\<close>
        by blast
      hence \<open>\<exists> phi. \<forall> n. phiU n = U (phi n) \<and> phi n \<in> B\<close>
        by metis
      then obtain phi where \<open>\<forall> n. phiU n = U (phi n)\<close> and \<open>\<forall> n. phi n \<in> B\<close>
        by blast
      have  \<open>(\<lambda> n. U (phi n)) \<longlonglongrightarrow> \<phi>\<close>
        using \<open>(\<lambda> n. phiU n) \<longlonglongrightarrow> \<phi>\<close> \<open>\<forall> n. phiU n = U (phi n)\<close>
        by simp
      from  \<open>(\<lambda> n. U (psi n)) \<longlonglongrightarrow> \<psi>\<close> \<open>(\<lambda> n. U (phi n)) \<longlonglongrightarrow> \<phi>\<close>
      have \<open>(\<lambda> n. U (psi n) +  U (phi n) ) \<longlonglongrightarrow> \<psi> + \<phi>\<close>
        by (simp add: tendsto_add)
      hence \<open>(\<lambda> n. U ( (psi n) +  (phi n)) ) \<longlonglongrightarrow> \<psi> + \<phi>\<close>
      proof-
        have \<open>U (psi n) +  U (phi n) =  U ( (psi n) +  (phi n))\<close>
          for n
          using \<open>bounded_clinear U\<close>
          unfolding bounded_clinear_def clinear_def Vector_Spaces.linear_def
            module_hom_def module_hom_axioms_def
          by auto
        thus ?thesis 
          using  \<open>(\<lambda> n. U (psi n) +  U (phi n) ) \<longlonglongrightarrow> \<psi> + \<phi>\<close>
          by auto
      qed
      hence \<open>(\<lambda> n. U ( (psi n) +  (phi n)) ) \<longlonglongrightarrow> x\<close>
        by (simp add: \<open>x = \<psi> + \<phi>\<close>)
      hence \<open>x \<in> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
        by (smt \<open>\<forall>n. phi n \<in> B\<close> \<open>\<forall>n. psi n \<in> A\<close> closure_sequential mem_Collect_eq setcompr_eq_image)
      thus ?thesis by blast
    qed
    moreover have \<open>closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})
        \<subseteq> closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
      by (simp add: closure_mono closure_subset image_mono)
    ultimately show ?thesis
      using closure_mono
      by (metis (no_types, lifting) closure_closure dual_order.trans subsetI)  
  qed
  ultimately show ?thesis by blast
qed

lemma cdot_plus_distrib[simp]:   
  fixes A B :: \<open>('a::chilbert_space) linear_space\<close> and U :: "('a,'b::chilbert_space) bounded"
  shows \<open>U *\<^sub>s (sup A B) = sup (U *\<^sub>s A) (U *\<^sub>s B)\<close>
proof-
  {  have   \<open>
       bounded_clinear U \<Longrightarrow>
       closed_subspace A \<Longrightarrow>
       closed_subspace B \<Longrightarrow>
       Abs_linear_space
        (closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
       Abs_linear_space
        (closure
          {\<psi> + \<phi> |\<psi> \<phi>.
           \<psi> \<in> space_as_set (Abs_linear_space (closure (U ` A))) \<and>
           \<phi> \<in> space_as_set (Abs_linear_space (closure (U ` B)))})\<close>
      for U::\<open>'a\<Rightarrow>'b\<close> and A B::\<open>'a set\<close>
    proof-
      assume \<open>bounded_clinear U\<close> and \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close> 
      hence \<open>(closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
        (closure {\<psi> + \<phi> |\<psi> \<phi>.
           \<psi> \<in> closure (U ` A) \<and>
           \<phi> \<in> closure (U ` B)})\<close>
        using cdot_plus_distrib_transfer by blast
      hence \<open>Abs_linear_space (closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
        Abs_linear_space (closure {\<psi> + \<phi> |\<psi> \<phi>.
           \<psi> \<in> closure (U ` A) \<and>
           \<phi> \<in> closure (U ` B)})\<close>
        by simp
      thus ?thesis using Abs_linear_space_inverse
        by (smt Collect_cong times_bounded_vec_cases space_as_set \<open>bounded_clinear U\<close> \<open>closed_subspace A\<close> \<open>closed_subspace B\<close> applyOpSpace.rep_eq mem_Collect_eq)
    qed    
  } note 1 = this

  show ?thesis 
    unfolding plus_bounded_def applyOpSpace_def apply auto apply transfer 
    unfolding closed_sum_def Minkoswki_sum_def
    apply auto
    unfolding  closed_sum_def Minkoswki_sum_def
    using 1 
    apply auto
  proof - (* sledgehammer *)
    fix Ua :: "'a \<Rightarrow> 'b" and Aa :: "'a set" and Ba :: "'a set"
    have "\<And>B Ba. B +\<^sub>M Ba = closure {b. \<exists>ba bb. (b::'b) = ba + bb \<and> ba \<in> B \<and> bb \<in> Ba}"
      by (simp add: Minkoswki_sum_def closed_sum_def)
    then show "Abs_linear_space (closure {b + ba |b ba. b \<in> space_as_set (Abs_linear_space (closure (Ua ` Aa))) \<and> ba \<in> space_as_set (Abs_linear_space (closure (Ua ` Ba)))}) = sup (Abs_linear_space (closure (Ua ` Aa))) (Abs_linear_space (closure (Ua ` Ba)))"
      by (metis (no_types) space_as_set_inverse sup_linear_space.rep_eq)
  qed

qed

lemma scalar_op_linear_space_assoc [simp]: 

fixes A::\<open>('a::chilbert_space,'b::chilbert_space) bounded\<close>
  and S::\<open>'a linear_space\<close> and \<alpha>::complex
shows \<open>(\<alpha> *\<^sub>C A) *\<^sub>s S  = \<alpha> *\<^sub>C (A *\<^sub>s S)\<close>
proof-
  have \<open>closure ( ( ((*\<^sub>C) \<alpha>) \<circ> (times_bounded_vec A) ) ` space_as_set S) =
   ((*\<^sub>C) \<alpha>) ` (closure (times_bounded_vec A ` space_as_set S))\<close>
    by (metis closure_scaleC image_comp)    
  hence \<open>(closure (times_bounded_vec (\<alpha> *\<^sub>C A) ` space_as_set S)) =
   ((*\<^sub>C) \<alpha>) ` (closure (times_bounded_vec A ` space_as_set S))\<close>
    by (metis (mono_tags, lifting) comp_apply image_cong scaleC_bounded.rep_eq)
  hence \<open>Abs_linear_space
     (closure (times_bounded_vec (\<alpha> *\<^sub>C A) ` space_as_set S)) =
    \<alpha> *\<^sub>C
    Abs_linear_space (closure (times_bounded_vec A ` space_as_set S))\<close>
    by (metis space_as_set_inverse applyOpSpace.rep_eq scaleC_linear_space.rep_eq)    
  show ?thesis 
    unfolding applyOpSpace_def apply auto
    using \<open>Abs_linear_space
     (closure (times_bounded_vec (\<alpha> *\<^sub>C A) ` space_as_set S)) =
    \<alpha> *\<^sub>C Abs_linear_space (closure (times_bounded_vec A ` space_as_set S))\<close>
    by blast
qed

lemma applyOpSpace_id[simp]: 
 "idOp *\<^sub>s \<psi> = \<psi>"
proof-
  have \<open>closed_subspace ( space_as_set \<psi>)\<close>
    using space_as_set by blast    
  hence \<open>closed ( space_as_set \<psi>)\<close>
    unfolding closed_subspace_def by blast
  hence \<open>closure ( space_as_set \<psi>) = space_as_set \<psi>\<close>
    by simp    
  hence \<open>(closure ( id ` space_as_set \<psi>)) = space_as_set \<psi>\<close>
    by simp    
  hence \<open>(closure (times_bounded_vec (Abs_bounded id) ` space_as_set \<psi>)) = space_as_set \<psi>\<close>
    by (metis idOp.abs_eq idOp.rep_eq)    
  hence \<open>Abs_linear_space
     (closure (times_bounded_vec (Abs_bounded id) ` space_as_set \<psi>)) = \<psi>\<close>
    by (simp add: space_as_set_inverse)    
  show ?thesis
    unfolding applyOpSpace_def idOp_def
    apply auto
    using  \<open>Abs_linear_space
     (closure (times_bounded_vec (Abs_bounded id) ` space_as_set \<psi>)) = \<psi>\<close>
    by blast
qed

lemma scalar_op_op[simp]:
  fixes A::"('b::complex_normed_vector,'c::complex_normed_vector) bounded"
    and B::"('a::complex_normed_vector, 'b) bounded"
  shows \<open>(a *\<^sub>C A) *\<^sub>o B = a *\<^sub>C (A *\<^sub>o B)\<close>
proof-
  have \<open>(times_rbounded (a *\<^sub>C (rbounded_of_bounded A))
       (rbounded_of_bounded B)) =
   ( a *\<^sub>C  (times_rbounded (rbounded_of_bounded A) (rbounded_of_bounded B)) )\<close>
    by (simp add: rscalar_op_op)
  hence \<open>(times_rbounded (rbounded_of_bounded (a *\<^sub>C A))
       (rbounded_of_bounded B)) =
   ( a *\<^sub>C  (times_rbounded (rbounded_of_bounded A) (rbounded_of_bounded B)) )\<close>
    by (simp add: rbounded_of_bounded_scaleC)    
  hence \<open>bounded_of_rbounded
     (times_rbounded (rbounded_of_bounded (a *\<^sub>C A))
       (rbounded_of_bounded B)) =
    bounded_of_rbounded
   ( a *\<^sub>C  (times_rbounded (rbounded_of_bounded A) (rbounded_of_bounded B)) )\<close>
    by simp    
  hence \<open>bounded_of_rbounded
     (times_rbounded (rbounded_of_bounded (a *\<^sub>C A))
       (rbounded_of_bounded B)) =
    a *\<^sub>C bounded_of_rbounded
     (times_rbounded (rbounded_of_bounded A) (rbounded_of_bounded B))\<close>
    by (simp add: bounded_of_rbounded_scaleC rbounded_of_bounded_prelim times_rbounded_scaleC)  
  thus ?thesis
    by (metis bounded_rbounded rbounded_of_bounded_timesOp)   
qed


lemma op_scalar_op[simp]:
  fixes A::"('b::complex_normed_vector,'c::complex_normed_vector) bounded" 
    and B::"('a::complex_normed_vector, 'b) bounded"
  shows \<open>A *\<^sub>o (a *\<^sub>C B) = a *\<^sub>C (A *\<^sub>o B)\<close>
  using op_rscalar_op
  by (simp add: op_rscalar_op rbounded_of_bounded_inj rbounded_of_bounded_prelim rbounded_of_bounded_scaleC rbounded_of_bounded_timesOp)

lemma times_idOp1[simp]: 
  shows "U *\<^sub>o idOp = U"
  by (metis times_bounded_vec_inject comp_id idOp.rep_eq timesOp.rep_eq)

lemma times_idOp2[simp]: 
  shows "idOp *\<^sub>o U  = U"
  by (metis times_bounded_vec_inject idOp.rep_eq id_comp timesOp.rep_eq)

lemma mult_INF1[simp]:
  fixes U :: "('b::complex_normed_vector,'c::cbanach) bounded"
    and V :: "'a \<Rightarrow> 'b linear_space" 
  shows \<open>U *\<^sub>s (INF i. V i) \<le> (INF i. U *\<^sub>s (V i))\<close>
proof-
  have \<open>bounded_clinear U \<Longrightarrow>
       \<forall>j. closed_subspace (V j) \<Longrightarrow> closure (U ` \<Inter> (range V)) \<subseteq> closure (U ` V i)\<close>
    for U::\<open>'b\<Rightarrow>'c\<close> and V::\<open>'a \<Rightarrow> 'b set\<close> and x::'c and i::'a
  proof-
    assume \<open>bounded_clinear U\<close> and \<open>\<forall>j. closed_subspace (V j)\<close> 
    have \<open>U ` \<Inter> (range V) \<subseteq> U ` (V i)\<close>
      by (simp add: Inter_lower image_mono)    
    thus ?thesis
      by (simp add: closure_mono) 
  qed
  thus ?thesis
    apply transfer
    by auto
qed

(* For mult_INF2:

I have a proof sketch for a slightly more restricted version of mult_INF2:

Assume that V_i is orthogonal to ker U for all i.

Let W be the pseudoinverse of U (exists according to https://en.wikipedia.org/wiki/Moore%E2%80%93Penrose_inverse#Generalizations).


Then (1) UW is the projector onto the range of U, and (2) WU the projector onto the orthogonal complement of ker U.


Then


INF (U*Vi)

= (1)

UW INF (U*Vi)

<= (INF_mult1)

U INF (WU*Vi)

= (2)

U INF Vi.


Of course, I don't know how difficult it is to show the existence of the pseudoinverse. An easy special case would be U=isometry, in which case W=U*.

 *)

lemma mult_inf_distrib':
  fixes U::\<open>('a::chilbert_space,'b::chilbert_space) bounded\<close> and B C::"'a linear_space"
  shows "U *\<^sub>s (inf B  C) \<le> inf (U *\<^sub>s B) (U *\<^sub>s C)"
proof-
  have \<open>bounded_clinear U \<Longrightarrow>
       closed_subspace B \<Longrightarrow>
       closed_subspace C \<Longrightarrow>
       closure (U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
    for U::\<open>'a\<Rightarrow>'b\<close> and B C::\<open>'a set\<close>
  proof-
    assume \<open>bounded_clinear U\<close> and \<open>closed_subspace B\<close> and \<open>closed_subspace C\<close>
    have \<open>(U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
      using closure_subset by force      
    moreover have \<open>closed ( closure (U ` B) \<inter> closure (U ` C) )\<close>
      by blast      
    ultimately show ?thesis
      by (simp add: closure_minimal) 
  qed
  show ?thesis 
    apply transfer
    using \<open>\<And>U B C.
       bounded_clinear U \<Longrightarrow>
       closed_subspace B \<Longrightarrow>
       closed_subspace C \<Longrightarrow>
       closure (U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
    by blast
qed



lemma equal_span:
  fixes A B :: "'a::cbanach \<Rightarrow> 'b::cbanach"
  assumes \<open>clinear A\<close> and \<open>bounded_clinear B\<close> and
    \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and \<open>t \<in> (complex_vector.span G)\<close>
  shows \<open>A t = B t\<close>
  using assms(1) assms(2) assms(3) assms(4) bounded_clinear.is_clinear 
    complex_vector.module_hom_eq_on_span by blast

lemma equal_span_applyOpSpace:
  fixes A B :: "'a::cbanach \<Rightarrow> 'b::cbanach"
  assumes \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close> and
    \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and \<open>t \<in> closure (complex_vector.span G)\<close>
  shows \<open>A t = B t\<close>
  using assms 
proof transfer
  fix A B::\<open>'a \<Rightarrow> 'b\<close> and G::\<open>'a set\<close> and t::'a
  assume \<open>bounded_clinear A\<close> and
    \<open>bounded_clinear B\<close> and
    \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and
    \<open>t \<in> closure (complex_vector.span G)\<close>
  define F where \<open>F = (\<lambda> x. A x - B x)\<close>
  have \<open>bounded_linear F\<close>
    unfolding F_def
    using \<open>bounded_clinear A\<close> \<open>bounded_clinear B\<close>
      bounded_clinear.bounded_linear bounded_linear_sub by auto
  hence \<open>isCont F t\<close>
    by (simp add: linear_continuous_at)
  hence \<open>isNSCont F t\<close>
    by (simp add: isCont_isNSCont)
  from \<open>t \<in> closure (complex_vector.span G)\<close>
  have \<open>\<exists> T \<in> *s* (complex_vector.span G). T \<approx> star_of t\<close>
    using approx_sym nsclosure_I by blast
  then obtain T where \<open>T \<in> *s* (complex_vector.span G)\<close> and \<open>T \<approx> star_of t\<close>
    by blast
  have \<open>(*f* F) T \<approx> (*f* F) (star_of t)\<close>
    using \<open>T \<approx> star_of t\<close>  \<open>isNSCont F t\<close>
    by (simp add: isNSCont_def)
  moreover have \<open>(*f* F) T \<approx> 0\<close>
  proof-
    from  \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close>
    have  \<open>\<And>x. x \<in> complex_vector.span G \<Longrightarrow> A x = B x\<close>
      using \<open>bounded_clinear A\<close> \<open>bounded_clinear B\<close> bounded_clinear.is_clinear equal_span by blast
    hence \<open>\<forall>x.  x \<in> complex_vector.span G \<longrightarrow> F x = 0\<close>
      unfolding F_def
      by simp
    hence \<open>\<forall> x. x \<in> *s* (complex_vector.span G) \<longrightarrow> (*f* F) x = 0\<close>
      by StarDef.transfer
    thus ?thesis
      using \<open>T \<in> *s* complex_vector.span G\<close> by auto 
  qed
  hence \<open>F t = 0\<close>
    using approx_sym approx_trans calculation by fastforce    
  thus \<open>A t = B t\<close>
    unfolding F_def
    by auto
qed

lemma applyOpSpace_span:
  fixes A B :: "('a::cbanach,'b::cbanach) bounded"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>v x = B *\<^sub>v x" and \<open>t \<in> space_as_set (Span G)\<close>
  shows "A *\<^sub>v t = B *\<^sub>v t"
  using assms
  apply transfer
  using equal_span_applyOpSpace by blast

lemma applyOpSpace_less_eq:
  fixes S :: "'a::cbanach linear_space" 
    and A B :: "('a::cbanach,'b::cbanach) bounded"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>v x = B *\<^sub>v x" and "Span G \<ge> S"
  shows "A *\<^sub>s S \<le> B *\<^sub>s S"
  using assms
  apply transfer
proof - (* sledgehammer *)
  fix Ga :: "'a set" and Aa :: "'a \<Rightarrow> 'b" and Ba :: "'a \<Rightarrow> 'b" and Sa :: "'a set"
  assume a1: "bounded_clinear Aa"
  assume a2: "bounded_clinear Ba"
  assume a3: "\<And>x. x \<in> Ga \<Longrightarrow> Aa x = Ba x"
  assume a4: "Sa \<subseteq> closure (complex_vector.span Ga)"
  have f5: "\<forall>A Aa f fa. (A \<noteq> Aa \<or> (\<exists>a. (a::'a) \<in> Aa \<and> (f a::'b) \<noteq> fa a)) \<or> f ` A = fa ` Aa"
    by (meson image_cong)
  obtain aa :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a" where
    "\<forall>x0 x1 x2. (\<exists>v4. v4 \<in> x2 \<and> x1 v4 \<noteq> x0 v4) = (aa x0 x1 x2 \<in> x2 \<and> x1 (aa x0 x1 x2) \<noteq> x0 (aa x0 x1 x2))"
    by moura
  then have f6: "aa Ba Aa Sa \<in> Sa \<and> Aa (aa Ba Aa Sa) \<noteq> Ba (aa Ba Aa Sa) \<or> Aa ` Sa = Ba ` Sa"
    using f5 by presburger
  have f7: "\<forall>f fa A a. (\<not> bounded_clinear f \<or> \<not> bounded_clinear fa \<or> (\<exists>a. (a::'a) \<in> A \<and> (f a::'b) \<noteq> fa a) \<or> a \<notin> closure (complex_vector.span A)) \<or> f a = fa a"
    using equal_span_applyOpSpace by blast
  obtain aaa :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a" where
    "\<forall>x1 x2 x3. (\<exists>v4. v4 \<in> x1 \<and> x3 v4 \<noteq> x2 v4) = (aaa x1 x2 x3 \<in> x1 \<and> x3 (aaa x1 x2 x3) \<noteq> x2 (aaa x1 x2 x3))"
    by moura
  then have "\<forall>f fa A a. (\<not> bounded_clinear f \<or> \<not> bounded_clinear fa \<or> aaa A fa f \<in> A \<and> f (aaa A fa f) \<noteq> fa (aaa A fa f) \<or> a \<notin> closure (complex_vector.span A)) \<or> f a = fa a"
    using f7 by presburger
  then have "Aa ` Sa = Ba ` Sa"
    using f6 a4 a3 a2 a1 by blast
  then show "closure (Aa ` Sa) \<subseteq> closure (Ba ` Sa)"
    by (metis equalityE)
qed

lemma applyOpSpace_eq:
  fixes S :: "'a::chilbert_space linear_space" 
    and A B :: "('a::chilbert_space,'b::chilbert_space) bounded"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>v x = B *\<^sub>v x" and "Span G \<ge> S"
  shows "A *\<^sub>s S = B *\<^sub>s S"
  by (metis applyOpSpace_less_eq assms(1) assms(2) dual_order.antisym)

section \<open>Unitary\<close>

definition isometry::\<open>('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> bool\<close> where
  \<open>isometry U \<longleftrightarrow> U* *\<^sub>o  U = idOp\<close>

definition unitary::\<open>('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> bool\<close> where
  \<open>unitary U \<longleftrightarrow> U* *\<^sub>o  U  = idOp \<and> U *\<^sub>o U* = idOp\<close>

lemma unitary_def': "unitary U \<longleftrightarrow> isometry U \<and> isometry (U*)"
  unfolding unitary_def isometry_def by simp

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* *\<^sub>o U = idOp" 
  unfolding isometry_def 
  by simp

lemma UadjU[simp]: "unitary U \<Longrightarrow> U *\<^sub>o U* = idOp"
  unfolding unitary_def isometry_def by simp


lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"(_,_)bounded"
  unfolding unitary_def by auto

lemma isometry_times[simp]: "isometry A \<Longrightarrow> isometry B \<Longrightarrow> isometry (A *\<^sub>o B)"
  unfolding isometry_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma unitary_times[simp]: "unitary A \<Longrightarrow> unitary B \<Longrightarrow> unitary (A *\<^sub>o B)"
  unfolding unitary_def' by simp

lemma unitary_surj: "unitary U \<Longrightarrow> surj (times_bounded_vec U)"
proof-
  assume \<open>unitary U\<close>
  have \<open>\<exists> t. (times_bounded_vec U) t = x\<close>
    for x
  proof-
    have \<open>(times_bounded_vec U) ((times_bounded_vec (U*)) x) = x\<close>
    proof-
      have \<open>(times_bounded_vec U) ((times_bounded_vec (U*)) x)
          = ((times_bounded_vec U) \<circ> (times_bounded_vec (U*))) x\<close>
        by simp        
      also have \<open>\<dots>
          = (times_bounded_vec ( U *\<^sub>o (U*) )) x\<close>
        by (simp add: timesOp.rep_eq)
      also have \<open>\<dots>
          = (times_bounded_vec ( idOp )) x\<close>
        by (simp add: \<open>unitary U\<close>)
      also have \<open>\<dots> =  x\<close>
        by (simp add: idOp.rep_eq)        
      finally show ?thesis
        by simp 
    qed
    thus ?thesis
      by blast 
  qed
  thus ?thesis
    by (metis surj_def) 
qed

lemma unitary_image[simp]: "unitary U \<Longrightarrow> U *\<^sub>s top = top"
proof-
  assume \<open>unitary U\<close>
  hence \<open>surj (times_bounded_vec U)\<close>
    using unitary_surj by blast
  hence \<open>range (times_bounded_vec U)  = UNIV\<close>
    by simp
  hence \<open>closure (range (times_bounded_vec U))  = UNIV\<close>
    by simp
  thus ?thesis
    apply transfer
    by blast
qed

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def
  by (simp add: isometry_def) 


section \<open>Projectors\<close>

lift_definition Proj :: "('a::chilbert_space) linear_space \<Rightarrow> ('a,'a) bounded"
  is \<open>projection\<close>
  by (rule Complex_Inner_Product.projectionPropertiesA)


lemma imageOp_Proj[simp]: "(Proj S) *\<^sub>s top = S"
  apply transfer
proof
  show "closure (range (projection (S::'a set))) \<subseteq> S"
    if "closed_subspace (S::'a set)"
    for S :: "'a set"
    using that OrthoClosedEq orthogonal_complement_twice 
    by (metis closed_subspace.subspace pre_ortho_twice projectionPropertiesE subspace_cl)

  show "(S::'a set) \<subseteq> closure (range (projection S))"
    if "closed_subspace (S::'a set)"
    for S :: "'a set"
    using that
    by (metis (no_types, lifting) closure_subset image_subset_iff in_mono projection_fixed_points subsetI subset_UNIV) 
qed


lemma Proj_D1: \<open>(Proj M) = (Proj M)*\<close>
  apply transfer
  by (rule projection_D1)


lemma Proj_D2[simp]: \<open>(Proj M) *\<^sub>o (Proj M) = (Proj M)\<close>
proof-
  have \<open>(times_bounded_vec (Proj M)) = projection (space_as_set M)\<close>
    apply transfer
    by blast
  moreover have \<open>(projection (space_as_set M))\<circ>(projection (space_as_set M))
                = (projection (space_as_set M)) \<close>
  proof-
    have \<open>closed_subspace (space_as_set M)\<close>
      using space_as_set by auto
    thus ?thesis
      by (simp add: projectionPropertiesC) 
  qed
  ultimately have \<open>(times_bounded_vec (Proj M)) \<circ> (times_bounded_vec (Proj M)) = times_bounded_vec (Proj M)\<close>
    by simp    
  hence \<open>times_bounded_vec ((Proj M) *\<^sub>o (Proj M)) = times_bounded_vec (Proj M)\<close>
    by (simp add: timesOp.rep_eq)
  thus ?thesis using times_bounded_vec_inject
    by auto 
qed

lift_definition isProjector::\<open>('a::chilbert_space, 'a) bounded \<Rightarrow> bool\<close> is
  \<open>\<lambda> P. \<exists> M. closed_subspace M \<and> is_projection_on P M\<close>.

lemma Proj_I:
  \<open>P *\<^sub>o P = P \<Longrightarrow> P = P* \<Longrightarrow> \<exists> M. P = Proj M \<and> space_as_set M = range (times_bounded_vec P)\<close>
  for P :: \<open>('a::chilbert_space,'a) bounded\<close>
proof-
  assume \<open>P *\<^sub>o P = P\<close> and \<open>P = P*\<close>
  have \<open>closed (range (times_bounded_vec P))\<close>
  proof-
    have \<open>range (times_bounded_vec P) = (\<lambda> x. x - times_bounded_vec P x) -` {0}\<close>
    proof
      show "range (times_bounded_vec P) \<subseteq> (\<lambda>x. x - times_bounded_vec P x) -` {0}"
      proof
        show "x \<in> (\<lambda>x. x - times_bounded_vec P x) -` {0}"
          if "x \<in> range (times_bounded_vec P)"
          for x :: 'a
        proof-
          have \<open>\<exists> t. times_bounded_vec P t = x\<close>
            using that by blast
          then obtain t where \<open>times_bounded_vec P t = x\<close>
            by blast 
          hence \<open>x - times_bounded_vec P x = x - times_bounded_vec P (times_bounded_vec P t)\<close>
            by simp
          also have \<open>\<dots> = x - (times_bounded_vec P t)\<close>
          proof-
            have \<open>times_bounded_vec P \<circ> times_bounded_vec P = times_bounded_vec P\<close>
              by (metis \<open>P *\<^sub>o P = P\<close> timesOp.rep_eq)
            thus ?thesis
              by (metis comp_apply) 
          qed
          also have \<open>\<dots> = 0\<close>
            by (simp add: \<open>times_bounded_vec P t = x\<close>)
          finally have \<open>x - times_bounded_vec P x = 0\<close>
            by blast
          thus ?thesis
            by simp 
        qed
      qed
      show "(\<lambda>x. x - times_bounded_vec P x) -` {0} \<subseteq> range (times_bounded_vec P)"
      proof
        show "x \<in> range (times_bounded_vec P)"
          if "x \<in> (\<lambda>x. x - times_bounded_vec P x) -` {0}"
          for x :: 'a
        proof-
          have \<open>x - times_bounded_vec P x = 0\<close>
            using that by blast
          hence \<open>x = times_bounded_vec P x\<close>
            by (simp add: \<open>x - times_bounded_vec P x = 0\<close> eq_iff_diff_eq_0)
          thus ?thesis
            by blast 
        qed
      qed
    qed
    moreover have \<open>closed ( (\<lambda> x. x - times_bounded_vec P x) -` {0} )\<close>
    proof-
      have \<open>closed {(0::'a)}\<close>
        by simp        
      moreover have \<open>continuous (at x) (\<lambda> x. x - times_bounded_vec P x)\<close>
        for x
      proof-
        have \<open>times_bounded_vec (idOp - P) = (\<lambda> x. x - times_bounded_vec P x)\<close>
          by (simp add: idOp.rep_eq minus_bounded.rep_eq)                 
        hence \<open>bounded_clinear (times_bounded_vec (idOp - P))\<close>
          using times_bounded_vec
          by blast 
        hence \<open>continuous (at x) (times_bounded_vec (idOp - P))\<close>
          by (simp add: bounded_linear_continuous)          
        thus ?thesis
          using \<open>times_bounded_vec (idOp - P) = (\<lambda> x. x - times_bounded_vec P x)\<close>
          by simp
      qed
      ultimately show ?thesis  
        by (rule Abstract_Topology.continuous_closed_vimage)               
    qed
    ultimately show ?thesis
      by simp  
  qed
  have \<open>bounded_clinear (times_bounded_vec P)\<close>
    using times_bounded_vec by auto
  hence \<open>closed_subspace ( range (times_bounded_vec P) )\<close>
    using \<open>closed (range (times_bounded_vec P))\<close>
      bounded_clinear.clinear  closed_subspace.intro
    using complex_vector.linear_subspace_image complex_vector.subspace_UNIV by blast        
  hence \<open>\<exists> M. space_as_set M = (range (times_bounded_vec P))\<close>
    using  \<open>closed (range (times_bounded_vec P))\<close>
    by (metis applyOpSpace.rep_eq closure_eq top_linear_space.rep_eq)    
  then obtain M where \<open>space_as_set M = (range (times_bounded_vec P))\<close>
    by blast
  have \<open>times_bounded_vec P x \<in> space_as_set M\<close>
    for x
    by (simp add: \<open>space_as_set M = range (times_bounded_vec P)\<close>)
  moreover have \<open>x - times_bounded_vec P x \<in> orthogonal_complement ( space_as_set M)\<close>
    for x
  proof-
    have \<open>y \<in> space_as_set M \<Longrightarrow> \<langle> x - times_bounded_vec P x, y \<rangle> = 0\<close>
      for y
    proof-
      assume \<open>y \<in> space_as_set M\<close>
      hence \<open>\<exists> t. y = times_bounded_vec P t\<close>
        by (simp add: \<open>space_as_set M = range (times_bounded_vec P)\<close> image_iff)
      then obtain t where \<open>y = times_bounded_vec P t\<close>
        by blast
      have \<open>\<langle> x - times_bounded_vec P x, y \<rangle> = \<langle> x - times_bounded_vec P x, times_bounded_vec P t \<rangle>\<close>
        by (simp add: \<open>y = times_bounded_vec P t\<close>)
      also have \<open>\<dots> = \<langle> times_bounded_vec P (x - times_bounded_vec P x), t \<rangle>\<close>
        by (metis \<open>P = P*\<close> adjoint_I)
      also have \<open>\<dots> = \<langle> times_bounded_vec P x - times_bounded_vec P (times_bounded_vec P x), t \<rangle>\<close>
        by (metis \<open>P = P*\<close> adjoint_I cinner_diff_left)
      also have \<open>\<dots> = \<langle> times_bounded_vec P x - times_bounded_vec P x, t \<rangle>\<close>
      proof-
        have \<open>(times_bounded_vec P) \<circ> (times_bounded_vec P) = (times_bounded_vec P)\<close>
          using  \<open>P *\<^sub>o P = P\<close>
          by (metis timesOp.rep_eq)
        thus ?thesis
          using comp_eq_dest_lhs by fastforce 
      qed
      also have \<open>\<dots> = \<langle> 0, t \<rangle>\<close>
        by simp
      also have \<open>\<dots> = 0\<close>
        by simp
      finally show ?thesis by blast
    qed
    thus ?thesis
      by (simp add: orthogonal_complement_I2) 
  qed
  ultimately have \<open>P = Proj M\<close>
  proof - (* sledgehammer *)
    have "closed_subspace (space_as_set M)"
      by (metis \<open>space_as_set M = range (times_bounded_vec P)\<close> \<open>closed_subspace (range (times_bounded_vec P))\<close>)
    then have f1: "\<forall>a. times_bounded_vec (Proj M) a = times_bounded_vec P a"
      by (simp add: Proj.rep_eq \<open>\<And>x. times_bounded_vec P x \<in> space_as_set M\<close> \<open>\<And>x. x - times_bounded_vec P x \<in> orthogonal_complement (space_as_set M)\<close> projection_uniq)
    have "\<forall>a. (+) ((a::'a) - a) = id"
      by force
    then have "\<forall>a. (+) (times_bounded_vec (P - Proj M) a) = id"
      using f1
      by (simp add: minus_bounded.rep_eq) 
    then have "\<forall>a aa. aa - aa = times_bounded_vec (P - Proj M) a"
      by (metis (no_types) add_diff_cancel_right' id_apply)
    then have "\<forall>a. times_bounded_vec (idOp - (P - Proj M)) a = a"
      by (simp add: idOp.rep_eq minus_bounded.rep_eq)      
    then show ?thesis
      by (metis (no_types) times_bounded_vec_inject diff_diff_eq2 diff_eq_diff_eq eq_id_iff idOp.rep_eq)
  qed
  thus ?thesis
    using \<open>space_as_set M = range (times_bounded_vec P)\<close> by blast 
qed

lemma Pro_isProjector:
  fixes M::\<open>'a::chilbert_space linear_space\<close>
  shows \<open>isProjector (Proj M)\<close>
  unfolding isProjector_def
  apply auto
proof
  show "closed_subspace (space_as_set M) \<and> is_projection_on ((*\<^sub>v) (Proj M)) (space_as_set M)"
  proof
    show "closed_subspace (space_as_set M)"
      using space_as_set by blast
    show "is_projection_on ((*\<^sub>v) (Proj M)) (space_as_set M)"
      unfolding is_projection_on_def
      apply auto
       apply (simp add: Proj.rep_eq \<open>closed_subspace (space_as_set M)\<close> projection_intro1)
      by (metis Proj.rep_eq \<open>closed_subspace (space_as_set M)\<close> projectionPropertiesE range_eqI)
  qed
qed

lemma isProjector_algebraic: 
  fixes P::\<open>('a::chilbert_space, 'a) bounded\<close>
  shows \<open>isProjector P \<longleftrightarrow> P *\<^sub>o P = P \<and> P = P*\<close>
proof
  show "P *\<^sub>o P = P \<and> P = P*"
    if "isProjector P"
  proof
    show "P *\<^sub>o P = P"
      using that apply transfer
      using  projectionPropertiesC'
      by auto
    show "P = P*"
      using that apply transfer
      using projection_D1'
      by blast
  qed
  show "isProjector P"
    if "P *\<^sub>o P = P \<and> P = P*"
    using that Proj_I Pro_isProjector
    by auto
qed


lemma Proj_leq: "(Proj S) *\<^sub>s A \<le> S"
proof -
  have "top = sup top A"
    by (meson sup.orderE top_a_linear_space)
  then have "sup S (Proj S *\<^sub>s A) = S"
    by (metis (full_types) cdot_plus_distrib imageOp_Proj)
  then show ?thesis
    by (meson sup.absorb_iff1)
qed


lemma Proj_times: "isometry A \<Longrightarrow> A *\<^sub>o (Proj S) *\<^sub>o (A*) = Proj (A *\<^sub>s S)" 
  for A::"('a::chilbert_space,'b::chilbert_space) bounded"
proof-
  assume \<open>isometry A\<close>
  define P where \<open>P = A *\<^sub>o (Proj S) *\<^sub>o (A*)\<close>
  have \<open>P *\<^sub>o P = P\<close>
    using  \<open>isometry A\<close>
    unfolding P_def isometry_def
    by (metis (no_types, lifting) Proj_D2 timesOp_assoc times_idOp2)
  moreover have \<open>P = P*\<close>
    unfolding P_def
    by (metis Proj_D1 adjoint_twice timesOp_assoc times_adjoint)
  ultimately have 
    \<open>\<exists> M. P = Proj M \<and> space_as_set M = range (times_bounded_vec (A *\<^sub>o (Proj S) *\<^sub>o (A*)))\<close>
    using P_def Proj_I by blast
  then obtain M where \<open>P = Proj M\<close>
    and \<open>space_as_set M = range (times_bounded_vec (A *\<^sub>o (Proj S) *\<^sub>o (A*)))\<close>
    by blast
  have \<open>M = A *\<^sub>s S\<close>
  proof - (* sledgehammer *)
    have f1: "\<forall>l. A *\<^sub>s Proj S *\<^sub>s A* *\<^sub>s l = P *\<^sub>s l"
      by (simp add: P_def timesOp_assoc_linear_space)
    have f2: "\<forall>l b. b* *\<^sub>s (b *\<^sub>s (l::'a linear_space)::'b linear_space) = idOp *\<^sub>s l \<or> \<not> isometry b"
      by (metis (no_types) adjUU timesOp_assoc_linear_space)
    have f3: "\<forall>l b. b *\<^sub>s idOp *\<^sub>s (l::'a linear_space) = (b *\<^sub>s l::'a linear_space)"
      by (metis timesOp_assoc_linear_space times_idOp1)
    have "\<forall>l la. sup (Proj (la::'a linear_space) *\<^sub>s l) la = la"
      by (metis Proj_leq sup.absorb_iff2)
    then show ?thesis
      using f3 f2 f1 by (metis Proj_leq \<open>P = Proj M\<close> \<open>isometry A\<close> cdot_plus_distrib imageOp_Proj sup.order_iff)
  qed 
  thus ?thesis
    using \<open>P = Proj M\<close>
    unfolding P_def
    by blast
qed

abbreviation proj :: "'a::chilbert_space \<Rightarrow> ('a,'a) bounded" where "proj \<psi> \<equiv> Proj (Span {\<psi>})"

lemma projection_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" for a::complex and \<psi>::"'a::chilbert_space"
  by (metis Complex_Vector_Spaces.span_raw_def Span.abs_eq span_mult)


lemma move_plus:
  "(Proj (- C)) *\<^sub>s A \<le> B \<Longrightarrow> A \<le> sup B C"
  for A B C::"'a::chilbert_space linear_space"
proof-
  assume \<open>(Proj (- C)) *\<^sub>s A \<le> B\<close>
  hence \<open>Abs_bounded
     (projection
       (space_as_set
         (Abs_linear_space (orthogonal_complement (space_as_set C))))) *\<^sub>s A \<le> B\<close>
    unfolding Proj_def  less_eq_linear_space_def
    by (simp add: uminus_linear_space_def)

  hence proj_ortho_CAB: \<open>Abs_bounded (projection (orthogonal_complement (space_as_set C))) *\<^sub>s A \<le> B\<close>
    using Proj_def \<open>Proj (- C) *\<^sub>s A \<le> B\<close> map_fun_apply
    by (simp add: Proj_def uminus_linear_space.rep_eq) 

  hence \<open>x \<in> space_as_set
              (Abs_linear_space
                (closure
                  (times_bounded_vec
                    (Abs_bounded
                      (projection (orthogonal_complement (space_as_set C)))) `
                   space_as_set A))) \<Longrightarrow>
         x \<in> space_as_set B\<close>
    for x
    unfolding applyOpSpace_def less_eq_linear_space_def
    by auto
  hence \<open>x \<in>  closure (times_bounded_vec (Abs_bounded
                      (projection (orthogonal_complement (space_as_set C)))) `
                   space_as_set A) \<Longrightarrow>
         x \<in> space_as_set B\<close>
    for x
    using proj_ortho_CAB
      applyOpSpace.rep_eq less_eq_linear_space.rep_eq by blast
  hence \<open>x \<in>  closure ( (projection (orthogonal_complement (space_as_set C))) `
                   space_as_set A) \<Longrightarrow>
         x \<in> space_as_set B\<close>
    for x
    using Proj.rep_eq Proj_def map_fun_apply
    by (metis (full_types) uminus_linear_space.rep_eq)

  hence \<open>x \<in> space_as_set A \<Longrightarrow>
    x \<in> closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set B \<and> \<phi> \<in> space_as_set C}\<close>
    for x
  proof-
    assume \<open>x \<in> space_as_set A\<close>
    have \<open>closed_subspace (space_as_set C)\<close>
      using space_as_set by auto
    hence \<open>x = (projection (space_as_set C)) x
       + (projection (orthogonal_complement (space_as_set C))) x\<close>
      by (simp add: ortho_decomp)
    hence \<open>x = (projection (orthogonal_complement (space_as_set C))) x
              + (projection (space_as_set C)) x\<close>
      by (metis ordered_field_class.sign_simps(2))
    moreover have \<open>(projection (orthogonal_complement (space_as_set C))) x \<in> space_as_set B\<close>
      using \<open>x \<in>  closure ( (projection (orthogonal_complement (space_as_set C))) `
                   space_as_set A) \<Longrightarrow> x \<in> space_as_set B\<close>
      by (meson \<open>\<And>x. x \<in> closure (projection (orthogonal_complement (space_as_set C)) ` space_as_set A) \<Longrightarrow> x \<in> space_as_set B\<close> \<open>x \<in> space_as_set A\<close> closure_subset image_subset_iff)
    moreover have \<open>(projection (space_as_set C)) x \<in> space_as_set C\<close>
      by (simp add: \<open>closed_subspace (space_as_set C)\<close> projection_intro2)
    ultimately show ?thesis
      using closure_subset by fastforce 
  qed
  hence \<open>x \<in> space_as_set A \<Longrightarrow>
        x \<in> (space_as_set B +\<^sub>M space_as_set C)\<close>
    for x
    unfolding closed_sum_def Minkoswki_sum_def
    by blast
  hence \<open> x \<in> space_as_set A \<Longrightarrow>
         x \<in> space_as_set
               (Abs_linear_space (space_as_set B +\<^sub>M space_as_set C))\<close>
    for x
    by (metis space_as_set_inverse sup_linear_space.rep_eq)
  thus ?thesis 
    by (simp add: \<open>\<And>x. x \<in> space_as_set A \<Longrightarrow> x \<in> space_as_set B +\<^sub>M space_as_set C\<close> less_eq_linear_space.rep_eq subset_eq sup_linear_space.rep_eq)    
qed


section \<open>Kernel\<close>

lift_definition kernel :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> 'a linear_space" 
  is "\<lambda> f. f -` {0}"
  by (metis ker_op_lin)

definition eigenspace :: "complex \<Rightarrow> ('a::chilbert_space,'a) bounded \<Rightarrow> 'a linear_space" where
  "eigenspace a A = kernel (A - a *\<^sub>C idOp)" 

lemma kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a *\<^sub>C A) = kernel A"
  for a :: complex and A :: "(_,_) bounded"
  apply transfer
  using complex_vector.scale_eq_0_iff by blast


lemma kernel_0[simp]: "kernel 0 = top"
proof-
  have \<open>(\<lambda> _. 0) -` {0} = UNIV\<close>
    using Collect_cong UNIV_def
    by blast
  hence \<open>(times_bounded_vec (bounded_of_rbounded 0)) -` {0} = UNIV\<close>
    by (metis bounded_of_rbounded_zero cr_rbounded_def rbounded.pcr_cr_eq rbounded_of_bounded.rep_eq rbounded_of_bounded_zero zero_rbounded.transfer)
  hence \<open>Abs_linear_space ( (times_bounded_vec (bounded_of_rbounded 0)) -` {0} ) = Abs_linear_space UNIV\<close>
    using Abs_linear_space_inject
    by (simp add: \<open>(times_bounded_vec (bounded_of_rbounded 0)) -` {0} = UNIV\<close>)
  thus ?thesis
    unfolding kernel_def zero_bounded_def top_linear_space_def
    by (simp add: Abs_bounded_inverse \<open>(\<lambda>_. 0) -` {0} = UNIV\<close>)   
qed

lemma kernel_id[simp]: "kernel idOp = 0"
  apply transfer  by simp

lemma [simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a *\<^sub>C A) = eigenspace (b/a) A"
proof -
  assume a1: "a \<noteq> 0"
  hence "b *\<^sub>C (idOp::('a, _) bounded) = a *\<^sub>C (b / a) *\<^sub>C idOp"
    by (metis Complex_Vector_Spaces.eq_vector_fraction_iff)
  hence "kernel (a *\<^sub>C A - b *\<^sub>C idOp) = kernel (A - (b / a) *\<^sub>C idOp)"
    using a1 by (metis (no_types) complex_vector.scale_right_diff_distrib kernel_scalar_times)
  thus ?thesis 
    unfolding eigenspace_def 
    by blast
qed

section \<open>Option\<close>

definition "inj_option \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"

definition 
  "inv_option \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (Hilbert_Choice.inv \<pi> (Some y)) else None)"

lemma inj_option_Some_pi[simp]: "inj_option (Some o \<pi>) = inj \<pi>"
  unfolding inj_option_def inj_def by simp

lemma inj_option_Some[simp]: "inj_option Some"
  using[[show_consts,show_types,show_sorts]]
  by (simp add: inj_option_def)

lemma inv_option_Some: "surj \<pi> \<Longrightarrow> inv_option (Some o \<pi>) = Some o (Hilbert_Choice.inv \<pi>)"
  unfolding inv_option_def o_def inv_def apply (rule ext) by auto

lemma inj_option_map_comp[simp]: "inj_option f \<Longrightarrow> inj_option g \<Longrightarrow> inj_option (f \<circ>\<^sub>m g)"
  unfolding inj_option_def apply auto
  using map_comp_Some_iff by smt

lemma inj_option_inv_option[simp]: "inj_option (inv_option \<pi>)"
proof (unfold inj_option_def, rule allI, rule allI, rule impI, erule conjE)
  fix x y
  assume same: "inv_option \<pi> x = inv_option \<pi> y"
    and pix_not_None: "inv_option \<pi> x \<noteq> None"
  have x_pi: "Some x \<in> range \<pi>" 
    using pix_not_None unfolding inv_option_def apply auto
    by (meson option.distinct(1))
  have y_pi: "Some y \<in> range \<pi>" 
    using pix_not_None unfolding same unfolding inv_option_def apply auto
    by (meson option.distinct(1))
  have "inv_option \<pi> x = Some (Hilbert_Choice.inv \<pi> (Some x))"
    unfolding inv_option_def using x_pi by simp
  moreover have "inv_option \<pi> y = Some (Hilbert_Choice.inv \<pi> (Some y))"
    unfolding inv_option_def using y_pi by simp
  ultimately have "Hilbert_Choice.inv \<pi> (Some x) = Hilbert_Choice.inv \<pi> (Some y)"
    using same by simp
  then show "x = y"
    by (meson inv_into_injective option.inject x_pi y_pi)
qed

section \<open>New/restored things\<close>


lemma isProjector_D1: \<open>isProjector P \<Longrightarrow> P *\<^sub>o P = P\<close>
  unfolding isProjector_def
  apply auto
  by (metis projectionPropertiesC' timesOp.rep_eq times_bounded_vec_inject)

lemma isProjector_D2: \<open>isProjector P \<Longrightarrow> P* = P\<close>
  unfolding isProjector_def
  by (metis isProjector_algebraic isProjector_def) 


lemma isProjector_I: \<open>P *\<^sub>o P = P \<Longrightarrow> P* = P \<Longrightarrow> isProjector P\<close>
  unfolding isProjector_def
  by (metis (mono_tags, lifting) isProjector_algebraic isProjector_def) 

lemma isProjector0[simp]: "isProjector ( 0::('a::chilbert_space, 'a) bounded )"
  unfolding isProjector_def is_projection_on_def
  apply auto
proof
  define M where \<open>M = {(0::'a::chilbert_space)}\<close>
  show "closed_subspace M \<and> (\<forall>h. (h::'a) - 0 *\<^sub>v h \<in> orthogonal_complement M \<and> 0 *\<^sub>v h \<in> M)"
    unfolding M_def
  proof
    show "closed_subspace {0::'a}"
      by simp

    show "\<forall>h. (h::'a) - 0 *\<^sub>v h \<in> orthogonal_complement {0} \<and> 0 *\<^sub>v h \<in> {0::'a}"
      by (simp add: zero_bounded.rep_eq)    
  qed
qed

lemma isProjectoridMinus[simp]: "isProjector P \<Longrightarrow> isProjector (idOp-P)"
proof (rule isProjector_I)
  show "(idOp - P) *\<^sub>o (idOp - P) = idOp - P"
    if "isProjector P"
  proof -
    have f1: "P *\<^sub>o P = P \<and> P* = P"
      using isProjector_algebraic that by auto

    then have "(idOp - P) *\<^sub>o (idOp - P) = ((idOp - P) *\<^sub>o (idOp - P))*"
      by auto
    then show ?thesis
      using f1 by (simp add: timesOp_minus)
  qed    
  show "(idOp - P)* = idOp - P"
    if "isProjector P"
    using that
    by (simp add: isProjector_algebraic)
qed

lemma applyOp0[simp]: "times_bounded_vec 0 \<psi> = 0"
  apply transfer by simp

lemma apply_idOp[simp]: "times_bounded_vec idOp \<psi> = \<psi>"
  apply transfer by simp

(* NEW *)
lemma rel_interior_sing_generalized:
  fixes a :: "'n::chilbert_space"
  shows "rel_interior {a} = {a}"
  apply (auto simp: rel_interior_ball)
  by (metis affine_sing gt_ex le_infI2 subset_hull subset_singleton_iff)


(* Move to Missing *)
lemma subspace_rel_interior:
  fixes S::\<open>'a::chilbert_space set\<close>
  assumes \<open>complex_vector.subspace S\<close>
  shows \<open>0 \<in> rel_interior S\<close>
proof-
  {  assume a1: "affine hull S \<subseteq> S"
    have f2: "\<not> (1::real) \<le> 0"
      by auto
    have "\<forall>x0. ((0::real) < x0) = (\<not> x0 \<le> 0)"
      by auto
    hence "\<exists>r>0. ball 0 r \<inter> affine hull S \<subseteq> S"
      using f2 a1 by (metis inf.coboundedI2)
  } note 1 = this

  have \<open>affine S\<close>
  proof-
    have \<open>x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow>  u + v = 1 \<Longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> S\<close>
      for x y u v
    proof-
      assume \<open>x\<in>S\<close> and \<open>y\<in>S\<close> and \<open>u + v = 1\<close>
      have \<open>(u::complex) *\<^sub>C x \<in> S\<close>
        using \<open>complex_vector.subspace S\<close>
        unfolding complex_vector.subspace_def
        by (simp add: \<open>x \<in> S\<close>)
      hence \<open>u *\<^sub>R x \<in> S\<close>
        by (simp add: scaleR_scaleC)
      have \<open>(v::complex) *\<^sub>C y \<in> S\<close>
        using \<open>complex_vector.subspace S\<close>
        unfolding complex_vector.subspace_def
        by (simp add: \<open>y \<in> S\<close>)
      hence \<open>v *\<^sub>R y \<in> S\<close>
        by (simp add: scaleR_scaleC)
      show \<open> u *\<^sub>R x + v *\<^sub>R y \<in> S\<close> 
        using \<open>complex_vector.subspace S\<close>
        unfolding complex_vector.subspace_def
        by (simp add:  \<open>u *\<^sub>R x \<in> S\<close>  \<open>v *\<^sub>R y \<in> S\<close>)
    qed
    thus ?thesis 
      unfolding affine_def by blast
  qed
  hence \<open>affine hull S \<subseteq> S\<close>
    unfolding  hull_def by auto
  thus ?thesis 
    apply (auto simp: rel_interior_ball)
    using assms
    apply (simp add: complex_vector.subspace_0)
    apply (rule 1)
    by blast
qed


(*
lemma mult_INF_less_eq_transfer_bij:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space set" 
    and U :: "'b \<Rightarrow>'c::chilbert_space"
  assumes \<open>bounded_clinear U\<close> 
       and \<open>\<forall>i. closed_subspace (V i)\<close>  
       and \<open>bij U\<close>
  shows \<open>\<Inter> (range (\<lambda> i. closure (U ` V i))) = closure (U ` \<Inter> (range V))\<close>
proof-
  define I where \<open>I = range (\<lambda> i. U ` (V i))\<close>
  have \<open>S\<in>I \<Longrightarrow> complex_vector.subspace S\<close>
    for S
  proof-
    assume \<open>S\<in>I\<close>
    hence \<open>\<exists> i. S = U ` (V i)\<close>
      unfolding I_def by auto
    then obtain i where \<open>S = U ` (V i)\<close>
      by blast
    have \<open>closed_subspace (V i)\<close>
      by (simp add: assms(2))
    thus \<open>complex_vector.subspace S\<close>
      using  \<open>S = U ` (V i)\<close> \<open>bounded_clinear U\<close>
      by (simp add: bounded_clinear.clinear complex_vector.subspace_image closed_subspace.complex_vector.subspace)
  qed
  hence \<open>\<forall>S\<in>I. convex S\<close>
    using linear_manifold_Convex by blast
  moreover have \<open>\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}\<close>
  proof-
    have \<open>S \<in> I \<Longrightarrow> 0 \<in> rel_interior S\<close>
      for S
    proof-
      assume \<open>S \<in> I\<close>
      hence \<open>complex_vector.subspace S\<close>
        by (simp add: \<open>\<And>S. S \<in> I \<Longrightarrow> complex_vector.subspace S\<close>)
      thus ?thesis using complex_vector.subspace_rel_interior
        by (simp add: complex_vector.subspace_rel_interior) 
    qed
    thus ?thesis by blast
  qed
  ultimately have "closure (\<Inter>I) = \<Inter>{closure S |S. S \<in> I}"
    by (rule convex_closure_inter_generalized)
  moreover have \<open>closure (\<Inter>I) = closure (U ` \<Inter> (range V))\<close>
  proof-
    have \<open>U ` \<Inter> (range V) = (\<Inter>i. U ` V i)\<close>
      using \<open>bij U\<close>  Complete_Lattices.bij_image_INT
      by metis      
    hence \<open>(\<Inter>I) = (U ` \<Inter> (range V))\<close>
      unfolding I_def
      by auto
    thus ?thesis
      by simp 
  qed
  moreover have \<open>\<Inter>{closure S |S. S \<in> I} = \<Inter> (range (\<lambda> i. closure (U ` V i)))\<close>
    unfolding I_def
    by (simp add: Setcompr_eq_image)
  ultimately show ?thesis by simp
qed

lift_definition BIJ::\<open>('a::complex_normed_vector,'b::complex_normed_vector) bounded \<Rightarrow> bool\<close> 
is bij.
*)

lemma isCont_applyOp[simp]: "isCont ((*\<^sub>v) A) \<psi>"
  apply transfer
  by (simp add: bounded_linear_continuous) 

lemma applyOpSpace_mono:
  "S \<le> T \<Longrightarrow> A *\<^sub>s S \<le> A *\<^sub>s T"
  by (simp add: applyOpSpace.rep_eq closure_mono image_mono less_eq_linear_space.rep_eq)

lemma apply_left_neutral:
  assumes "A *\<^sub>o B = B"
  assumes "\<psi> \<in> space_as_set (B *\<^sub>s top)"
  shows "A *\<^sub>v \<psi> = \<psi>" 
proof -
  define rangeB rangeB' where "rangeB = space_as_set (B *\<^sub>s top)" and "rangeB' = range (times_bounded_vec B)"
  from assms have "\<psi> \<in> closure rangeB'"
    unfolding rangeB'_def apply (transfer fixing: \<psi>) by simp
  then obtain \<psi>i where \<psi>i_lim: "\<psi>i \<longlonglongrightarrow> \<psi>" and \<psi>i_B: "\<psi>i i \<in> rangeB'" for i
    apply atomize_elim using closure_sequential by blast
  have A_invariant: "A *\<^sub>v \<psi>i i = \<psi>i i" for i
  proof -
    from \<psi>i_B obtain \<phi> where \<phi>: "\<psi>i i = B *\<^sub>v \<phi>"
      apply atomize_elim unfolding rangeB'_def apply transfer by auto
    then have "A *\<^sub>v \<psi>i i = (A *\<^sub>o B) *\<^sub>v \<phi>"
      by (simp add: timesOp.rep_eq)
    also have "\<dots> = B *\<^sub>v \<phi>"
      by (simp add: assms)
    also have "\<dots> = \<psi>i i"
      by (simp add: \<phi>)
    finally show ?thesis
      by -
  qed
  from \<psi>i_lim have "(\<lambda>i. A *\<^sub>v (\<psi>i i)) \<longlonglongrightarrow> A *\<^sub>v \<psi>"
    by (rule isCont_tendsto_compose[rotated], simp)
  with A_invariant have "(\<lambda>i. \<psi>i i) \<longlonglongrightarrow> A *\<^sub>v \<psi>"
    by auto
  with \<psi>i_lim show "A *\<^sub>v \<psi> = \<psi>"
    using LIMSEQ_unique by blast
qed

lemma range_adjoint_isometry:
  assumes "isometry U"
  shows "U* *\<^sub>s top = top"
proof -
  from assms have "top = U* *\<^sub>s U *\<^sub>s top"
    by (metis adjUU applyOpSpace_id timesOp_assoc_linear_space)
  also have "\<dots> \<le> U* *\<^sub>s top"
    by (simp add: applyOpSpace_mono)
  finally show ?thesis
    using top.extremum_unique by blast
qed


lemma mult_INF_general[simp]: 
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space linear_space"
    and U :: "('b,'c::chilbert_space) bounded"
    and Uinv :: "('c,'b) bounded" 
  assumes UinvUUinv: "Uinv *\<^sub>o U *\<^sub>o Uinv = Uinv"
    and UUinvU: "U *\<^sub>o Uinv *\<^sub>o U = U"
    and V: "\<And>i. V i \<le> Uinv *\<^sub>s top"
  shows "U *\<^sub>s (INF i. V i) = (INF i. U *\<^sub>s V i)"
proof (rule antisym)
  show "U *\<^sub>s (INF i. V i) \<le> (INF i. U *\<^sub>s V i)"
    by (rule mult_INF1)
next
  define rangeU rangeUinv where "rangeU = U *\<^sub>s top" and "rangeUinv = Uinv *\<^sub>s top"
  define INFUV INFV where "INFUV = (INF i. U *\<^sub>s V i)" and "INFV = (INF i. V i)"
  have "INFUV = U *\<^sub>s Uinv *\<^sub>s INFUV"
  proof -
    have "U *\<^sub>s V i \<le> rangeU" for i
      unfolding rangeU_def apply transfer apply auto
      by (meson closure_mono image_mono subsetD top_greatest)
    then have "INFUV \<le> rangeU"
      unfolding INFUV_def by (meson INF_lower UNIV_I order_trans)
    moreover have "(U *\<^sub>o Uinv) *\<^sub>v \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeU" for \<psi>
      apply (rule apply_left_neutral[where B=U])
      using assms that rangeU_def by auto
    ultimately have "(U *\<^sub>o Uinv) *\<^sub>v \<psi> = \<psi>" if "\<psi> \<in> space_as_set INFUV" for \<psi>
      by (simp add: in_mono less_eq_linear_space.rep_eq that)
    then have "(U *\<^sub>o Uinv) *\<^sub>s INFUV = INFUV"
      apply transfer apply auto
      apply (metis closed_sum_def closure_closure is_closed_subspace_zero)
      using closure_subset by blast
    then show ?thesis
      by (simp add: timesOp_assoc_linear_space)
  qed
  also have "\<dots> \<le> U *\<^sub>s (INF i. Uinv *\<^sub>s U *\<^sub>s V i)"
    unfolding INFUV_def
    apply (rule applyOpSpace_mono)
    by (rule mult_INF1)
  also have "\<dots> = U *\<^sub>s INFV"
  proof -
    from assms have "V i \<le> rangeUinv" for i
      unfolding rangeUinv_def by simp
    moreover have "(Uinv *\<^sub>o U) *\<^sub>v \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeUinv" for \<psi>
      apply (rule apply_left_neutral[where B=Uinv])
      using assms that rangeUinv_def by auto
    ultimately have "(Uinv *\<^sub>o U) *\<^sub>v \<psi> = \<psi>" if "\<psi> \<in> space_as_set (V i)" for \<psi> i
      using less_eq_linear_space.rep_eq that by blast
    then have "(Uinv *\<^sub>o U) *\<^sub>s (V i) = (V i)" for i
      apply transfer apply auto
      apply (metis closed_sum_def closure_closure is_closed_subspace_zero)
      using closure_subset by blast
    thus ?thesis
      unfolding INFV_def
      by (simp add: timesOp_assoc_linear_space)
  qed
  finally show "INFUV \<le> U *\<^sub>s INFV".
qed

lemma mult_INF[simp]: 
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space linear_space" and U :: "('b,'c::chilbert_space) bounded"
  assumes \<open>isometry U\<close>
  shows "U *\<^sub>s (INF i. V i) = (INF i. U *\<^sub>s V i)"
proof -
  from \<open>isometry U\<close> have "U* *\<^sub>o U *\<^sub>o U* = U*"
    unfolding isometry_def by simp
  moreover from \<open>isometry U\<close> have "U *\<^sub>o U* *\<^sub>o U = U"
    unfolding isometry_def
    by (simp add: timesOp_assoc)
  moreover have "V i \<le> U* *\<^sub>s top" for i
    by (simp add: range_adjoint_isometry assms)
  ultimately show ?thesis
    by (rule mult_INF_general)
qed

lemma leq_INF[simp]:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space linear_space"
  shows "(A \<le> (INF x. V x)) = (\<forall>x. A \<le> V x)"
  by (simp add: le_Inf_iff)

lemma times_applyOp: "(A *\<^sub>o B) *\<^sub>v \<psi> = A *\<^sub>v (B *\<^sub>v \<psi>)"
  apply transfer by simp

lemma mult_inf_distrib[simp]:
  fixes U::\<open>('a::chilbert_space,'b::chilbert_space) bounded\<close>
    and B C::"'a linear_space"
  assumes "isometry U"
  shows "U *\<^sub>s (inf B C) = inf (U *\<^sub>s B) (U *\<^sub>s C)"
  using mult_INF[where V="\<lambda>b. if b then B else C" and U=U]
  unfolding INF_UNIV_bool_expand
  using assms by auto

lemma applyOp_scaleC1[simp]: "(c *\<^sub>C A) *\<^sub>v \<psi> = c *\<^sub>C (A *\<^sub>v \<psi>)"
  apply transfer by simp

lemma applyOp_scaleC2[simp]: "A *\<^sub>v (c *\<^sub>C \<psi>) = c *\<^sub>C (A *\<^sub>v \<psi>)"
  apply transfer 
  using bounded_clinear.clinear
  by (simp add: bounded_clinear.is_clinear complex_vector.linear_scale)


unbundle no_bounded_notation


end

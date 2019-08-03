(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Main results:
- bounded: Definition of complex bounded operators. Instantiation as a complex Banach space.

*)


theory Bounded_Operators
  imports Complex_Inner_Product Real_Bounded_Operators Extended_Sorry
begin

unbundle rbounded_notation

section \<open>Complex bounded operators\<close>

(* TODO: Rename Rep_bounded \<rightarrow> times_bounded_vec *)
typedef (overloaded) ('a::complex_normed_vector, 'b::complex_normed_vector) bounded
  = \<open>{A::'a \<Rightarrow> 'b. bounded_clinear A}\<close>
  morphisms Rep_bounded Abs_bounded
  using bounded_clinear_zero by blast

(* TODO: Replace \<cdot>\<^sub>v by *\<^sub>v    *)
notation Rep_bounded (infixr "\<cdot>\<^sub>v" 70)

setup_lifting type_definition_bounded

lift_definition rbounded_of_bounded::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded
\<Rightarrow> ('a,'b) rbounded\<close> is "id"
  apply transfer apply auto
  by (simp add: bounded_clinear.bounded_linear)

lemma rbounded_of_bounded_inj:
  \<open>rbounded_of_bounded f = rbounded_of_bounded g \<Longrightarrow> f = g\<close>
  by (metis Rep_bounded_inject rbounded_of_bounded.rep_eq)

lemma rbounded_of_bounded_inv:
  \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x) \<Longrightarrow> \<exists> g. rbounded_of_bounded g = f\<close>
  apply transfer apply auto
  by (simp add: bounded_linear_bounded_clinear)

lemma rbounded_of_bounded_inv_uniq:
  \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x) \<Longrightarrow> \<exists>! g. rbounded_of_bounded g = f\<close>
  using rbounded_of_bounded_inv rbounded_of_bounded_inj
  by blast

lemma rbounded_of_bounded_prelim:
  \<open>\<forall> c. \<forall> x. Rep_rbounded (rbounded_of_bounded g) (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded (rbounded_of_bounded g) x)\<close>
  apply transfer
  apply auto
  by (simp add: bounded_clinear_def clinear.scaleC)

definition bounded_of_rbounded::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) rbounded \<Rightarrow>
('a, 'b) bounded\<close> where
  \<open>bounded_of_rbounded = inv rbounded_of_bounded\<close>

lemma bounded_rbounded:
  \<open>bounded_of_rbounded (rbounded_of_bounded f) = f\<close>
  by (metis (no_types, hide_lams) Rep_bounded_inverse UNIV_I bounded_of_rbounded_def f_inv_into_f image_iff rbounded_of_bounded.rep_eq)

lemma rbounded_bounded:
  \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x)
 = c *\<^sub>C (Rep_rbounded f x)
 \<Longrightarrow> rbounded_of_bounded (bounded_of_rbounded f) = f\<close> 
  by (metis Abs_bounded_inverse Rep_rbounded Rep_rbounded_inject bounded_linear_bounded_clinear bounded_rbounded mem_Collect_eq rbounded_of_bounded.rep_eq)


instantiation bounded :: (complex_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
lift_definition zero_bounded::"('a,'b) bounded" is "\<lambda>_. 0" by simp

lemma bounded_of_rbounded_zero:
 "(0::('a::complex_normed_vector,'b::complex_normed_vector) bounded) = bounded_of_rbounded (0::('a,'b) rbounded)" 
proof-
  have \<open>Rep_bounded 0 t  = Rep_bounded (SOME x. Abs_rbounded (Rep_bounded x) = 0) t\<close>
    for t
  proof-
    have \<open>Rep_bounded (SOME x. Abs_rbounded (Rep_bounded x) = 0) t = 0\<close>
      by (metis (mono_tags, lifting) Abs_bounded_inverse Rep_rbounded_inverse bounded_clinear_zero mem_Collect_eq rbounded_of_bounded.rep_eq tfl_some zero_rbounded.abs_eq)
    moreover have \<open>Rep_bounded 0 t = 0\<close>
      apply transfer by blast
    ultimately show ?thesis by simp
  qed
  hence \<open>Rep_bounded 0  = Rep_bounded (SOME x. Abs_rbounded (Rep_bounded x) = 0) \<close>
    by blast
  hence \<open>0 = (SOME x. Abs_rbounded (Rep_bounded x) = 0)\<close>
    using Rep_bounded_inject
    by blast
  hence \<open>0 = inv (Abs_rbounded \<circ> Rep_bounded) 0\<close>
    unfolding inv_def
    by auto
  hence \<open>0 = inv (map_fun Rep_bounded Abs_rbounded id) 0\<close>
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
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
    and \<open>\<forall> c. \<forall> x. Rep_rbounded g (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded g x)\<close>
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
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
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
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
    and \<open>\<forall> c. \<forall> x. Rep_rbounded g (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded g x)\<close>
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
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
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
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
  shows \<open>bounded_of_rbounded ( c *\<^sub>R f ) = c *\<^sub>R (bounded_of_rbounded f)\<close>
  using assms
  by (metis (mono_tags) bounded_rbounded rbounded_bounded rbounded_of_bounded_scaleR)

lemma bounded_of_rbounded_Abs_rbounded:
  \<open>bounded_of_rbounded ( Abs_rbounded (Rep_bounded f) ) = f\<close>
  by (metis Quotient_bounded Quotient_rel_rep Rep_bounded_inverse bounded_rbounded rbounded_of_bounded.abs_eq)

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
    have f1: "\<forall>r ra. ((\<exists>c a. Rep_rbounded r (c *\<^sub>C (a::'a)) \<noteq> c *\<^sub>C (Rep_rbounded r a::'b)) \<or> (\<exists>c a. Rep_rbounded ra (c *\<^sub>C a) \<noteq> c *\<^sub>C Rep_rbounded ra a)) \<or> bounded_of_rbounded (r + ra) = bounded_of_rbounded r + bounded_of_rbounded ra"
      using bounded_of_rbounded_plus by blast
    obtain cc :: "('a, 'b) rbounded \<Rightarrow> complex" and aa :: "('a, 'b) rbounded \<Rightarrow> 'a" where
      "\<forall>x0. (\<exists>v2 v3. Rep_rbounded x0 (v2 *\<^sub>C v3) \<noteq> v2 *\<^sub>C Rep_rbounded x0 v3) = (Rep_rbounded x0 (cc x0 *\<^sub>C aa x0) \<noteq> cc x0 *\<^sub>C Rep_rbounded x0 (aa x0))"
      by moura
    then obtain cca :: "('a, 'b) rbounded \<Rightarrow> complex" and aaa :: "('a, 'b) rbounded \<Rightarrow> 'a" where
      f2: "\<forall>r ra. (Rep_rbounded r (cca r *\<^sub>C aaa r) \<noteq> cca r *\<^sub>C Rep_rbounded r (aaa r) \<or> Rep_rbounded ra (cc ra *\<^sub>C aa ra) \<noteq> cc ra *\<^sub>C Rep_rbounded ra (aa ra)) \<or> bounded_of_rbounded (r + ra) = bounded_of_rbounded r + bounded_of_rbounded ra"
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
    have "rbounded_of_bounded (map_fun Rep_bounded (map_fun Rep_bounded Abs_bounded) (\<lambda>f fa a. f a + fa a) 0 a) = rbounded_of_bounded 0 + rbounded_of_bounded a"
      using Bounded_Operators.rbounded_of_bounded_plus plus_bounded_def by auto
    hence "map_fun Rep_bounded (map_fun Rep_bounded Abs_bounded) (\<lambda>f fa a. f a + fa a) 0 a = a"
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
    have \<open>r *\<^sub>R Rep_bounded f t =
          complex_of_real r *\<^sub>C Rep_bounded f t\<close>
      for f::\<open>('a, 'b) bounded\<close> and t
      by (simp add: scaleR_scaleC)      
    hence \<open>(\<lambda>t. r *\<^sub>R Rep_bounded f t) t =
          (\<lambda>t. complex_of_real r *\<^sub>C Rep_bounded f t) t\<close>
      for f::\<open>('a, 'b) bounded\<close> and t
      by simp      
    hence \<open>(\<lambda>t. r *\<^sub>R Rep_bounded f t) =
          (\<lambda>t. complex_of_real r *\<^sub>C Rep_bounded f t)\<close>
      for f::\<open>('a, 'b) bounded\<close>
      by simp
    hence \<open>Abs_bounded (\<lambda>t. r *\<^sub>R Rep_bounded f t) =
    Abs_bounded
          (\<lambda>t. complex_of_real r *\<^sub>C Rep_bounded f t)\<close>
      for f::\<open>('a, 'b) bounded\<close>
      by simp
    hence \<open>(\<lambda>f. Abs_bounded (\<lambda>t. r *\<^sub>R Rep_bounded f t)) f =
    (\<lambda>f. Abs_bounded
          (\<lambda>t. complex_of_real r *\<^sub>C Rep_bounded f t)) f\<close>
      for f::\<open>('a, 'b) bounded\<close>
      by blast
    hence \<open>(\<lambda>f. Abs_bounded (\<lambda>t. r *\<^sub>R Rep_bounded f t)) =
    (\<lambda>f. Abs_bounded
          (\<lambda>t. complex_of_real r *\<^sub>C Rep_bounded f t))\<close>
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
    \<open>\<And> n::nat. \<forall> c. \<forall> x. Rep_rbounded (f n) (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded (f n) x)\<close>
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
    \<open>\<And> n::nat. \<forall> c. \<forall> x. Rep_rbounded (f n) (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded (f n) x)\<close> 
  shows \<open>\<forall> c. \<forall> x. Rep_rbounded l (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded l x)\<close>
proof-
  have \<open>Rep_rbounded l (c *\<^sub>C x) = c *\<^sub>C Rep_rbounded l x\<close>
    for c::complex and x
  proof-
    have \<open>(\<lambda> n. Rep_rbounded (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> Rep_rbounded l (c *\<^sub>C x)\<close>
      by (simp add: assms(1) onorm_strong)        
    moreover have \<open>(\<lambda> n. c *\<^sub>C (Rep_rbounded (f n) x) ) \<longlonglongrightarrow> c *\<^sub>C (Rep_rbounded l x)\<close>
    proof-
      have \<open>isCont ((*\<^sub>C) c) y\<close>
        for y::'b
        using isCont_scaleC by auto
      hence \<open>isCont ((*\<^sub>C) c) (Rep_rbounded l x)\<close>
        by simp
      thus ?thesis
        using assms(1) isCont_tendsto_compose onorm_strong by blast 
    qed
    moreover have \<open>Rep_rbounded (f n) (c *\<^sub>C x) =  c *\<^sub>C (Rep_rbounded (f n) x)\<close>
      for n
      by (simp add: assms(2))
    ultimately have \<open>(\<lambda> n. Rep_rbounded (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> c *\<^sub>C (Rep_rbounded l x)\<close>
      by simp
    thus ?thesis
      using  \<open>(\<lambda> n. Rep_rbounded (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> Rep_rbounded l (c *\<^sub>C x)\<close> LIMSEQ_unique 
      by blast
  qed
  thus ?thesis by blast
qed  

lemma bounded_of_rbounded_lim:
  fixes f::\<open>nat \<Rightarrow> ('a::complex_normed_vector, 'b::cbanach) rbounded\<close>
    and l::\<open>('a, 'b) rbounded\<close>
  assumes  \<open>f \<longlonglongrightarrow> l\<close> and
    \<open>\<And> n::nat. \<forall> c. \<forall> x. Rep_rbounded (f n) (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded (f n) x)\<close>
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
      have \<open>\<forall> c. \<forall> x. Rep_rbounded l (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded l x)\<close>
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
  shows \<open>\<forall>x. \<forall>y. \<langle>(G*) \<cdot>\<^sub>v x, y\<rangle> = \<langle>x, G \<cdot>\<^sub>v y\<rangle>\<close>
  apply transfer using Adj_I by blast

lemma adjoint_D:
  fixes G:: \<open>('b::chilbert_space, 'a::chilbert_space) bounded\<close>
    and F:: \<open>('a, 'b) bounded\<close>
  assumes \<open>\<And>x y. \<langle>(Rep_bounded F) x, y\<rangle> = \<langle>x, (Rep_bounded G) y\<rangle>\<close>
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
  have \<open>bounded_clinear ((Rep_bounded A))\<close>
    using Rep_bounded by blast
  hence \<open>(\<lambda> t. a *\<^sub>C ((Rep_bounded A) t))\<^sup>\<dagger> = (\<lambda> s. (cnj a) *\<^sub>C (((Rep_bounded A)\<^sup>\<dagger>) s))\<close>
    using scalar_times_adjc_flatten
    unfolding bounded_clinear_def 
      scalar_times_adjc_flatten \<open>bounded_clinear (Rep_bounded A)\<close> bounded_clinear.bounded_linear
    by (simp add: scalar_times_adjc_flatten \<open>bounded_clinear ((\<cdot>\<^sub>v) A)\<close> bounded_clinear.bounded_linear complex_vector.linear_scale)

  moreover have \<open>Rep_bounded ((a *\<^sub>C A)*) = (\<lambda> t. a *\<^sub>C ((Rep_bounded A) t))\<^sup>\<dagger>\<close>
    unfolding Adj_def
    apply auto
    by (smt Adj_def Eps_cong adjoint.rep_eq cinner_scaleC_right scaleC_bounded.rep_eq)
  moreover have \<open>Rep_bounded (cnj a *\<^sub>C (A*)) = (\<lambda> s. (cnj a) *\<^sub>C (((Rep_bounded A)\<^sup>\<dagger>) s))\<close>
    unfolding Adj_def
    by (simp add: Adj_def adjoint.rep_eq scaleC_bounded.rep_eq)    
  ultimately show ?thesis
    using Rep_bounded_inject
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

(* TODO: Replace \<cdot>\<^sub>o \<rightarrow> *\<^sub>o    *)
lift_definition timesOp:: 
  "('b::complex_normed_vector,'c::complex_normed_vector) bounded
     \<Rightarrow> ('a::complex_normed_vector,'b) bounded \<Rightarrow> ('a,'c) bounded" (infixl "\<cdot>\<^sub>o" 69)
  is "(o)"
  unfolding o_def 
  by (rule bounded_clinear_compose, simp_all)

(* TODO: Replace \<cdot>\<^sub>s \<rightarrow> *\<^sub>s    *)
(* Closure is necessary. See thunderlink://messageid=47a3bb3d-3cc3-0934-36eb-3ef0f7b70a85@ut.ee *)
lift_definition applyOpSpace::\<open>('a::complex_normed_vector,'b::complex_normed_vector) bounded
\<Rightarrow> 'a linear_space \<Rightarrow> 'b linear_space\<close>  (infixr "\<cdot>\<^sub>s" 70)
  is "\<lambda>A S. closure (A ` S)"
  using  bounded_clinear_def is_subspace.subspace
  by (metis closed_closure is_linear_manifold_image is_subspace.intro is_subspace_cl) 


lemma rbounded_of_bounded_timesOp:
  fixes f::\<open>('b::complex_normed_vector,'c::complex_normed_vector) bounded\<close>
     and g::\<open>('a::complex_normed_vector,'b) bounded\<close>
   shows \<open>rbounded_of_bounded (f \<cdot>\<^sub>o g) =  (rbounded_of_bounded f) \<cdot>\<^sub>r\<^sub>o (rbounded_of_bounded g)\<close> 
  apply transfer
  by auto

lemma timesOp_assoc: 
  shows "(A \<cdot>\<^sub>o B) \<cdot>\<^sub>o C = A  \<cdot>\<^sub>o (B  \<cdot>\<^sub>o C)"
  by (metis (no_types, lifting) Rep_bounded_inject fun.map_comp timesOp.rep_eq)


lemma timesOp_dist1:  
  fixes a b :: "('b::complex_normed_vector, 'c::complex_normed_vector) bounded"
      and c :: "('a::complex_normed_vector, 'b) bounded"
shows "(a + b) \<cdot>\<^sub>o c = (a \<cdot>\<^sub>o c) + (b \<cdot>\<^sub>o c)"
  using rtimesOp_dist1
  by (simp add: rtimesOp_dist1 rbounded_of_bounded_inj rbounded_of_bounded_plus rbounded_of_bounded_timesOp)

lemma timesOp_dist2:  
  fixes a b :: "('a::complex_normed_vector, 'b::complex_normed_vector) bounded"
    and c :: "('b, 'c::complex_normed_vector) bounded"
  shows "c \<cdot>\<^sub>o (a + b) = (c \<cdot>\<^sub>o a) + (c \<cdot>\<^sub>o b)"
  using rtimesOp_dist2
  by (simp add: rtimesOp_dist2 rbounded_of_bounded_inj rbounded_of_bounded_plus rbounded_of_bounded_timesOp)


lemma timesOp_minus:
  \<open>A \<cdot>\<^sub>o (B - C) = A \<cdot>\<^sub>o B - A \<cdot>\<^sub>o C\<close>
  apply transfer
  using additive.diff bounded_clinear_def
  sorry


lemma times_adjoint[simp]:
  fixes B::\<open>('a::chilbert_space,'b::chilbert_space) bounded\<close>
    and A::\<open>('b,'c::chilbert_space) bounded\<close> 
  shows "(A \<cdot>\<^sub>o B)* =  (B*) \<cdot>\<^sub>o (A*)"
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


lemma applyOp_0[simp]:  
   "U \<cdot>\<^sub>s 0 = 0"
  apply transfer
  by (simp add: additive.zero bounded_clinear_def clinear.axioms(1))

lemma times_comp: \<open>\<And>A B \<psi>.
       bounded_clinear A \<Longrightarrow>
       bounded_clinear B \<Longrightarrow>
       is_subspace \<psi> \<Longrightarrow>
       closure ( (A \<circ> B) ` \<psi>) = closure (A ` closure (B ` \<psi>))\<close>
proof
  show "closure ((A \<circ> B) ` (\<psi>::'c set)::'b set) \<subseteq> closure (A ` closure (B ` \<psi>::'a set))"
    if "bounded_clinear (A::'a \<Rightarrow> 'b)"
      and "bounded_clinear (B::'c \<Rightarrow> 'a)"
      and "is_subspace (\<psi>::'c set)"
    for A :: "'a \<Rightarrow> 'b"
      and B :: "'c \<Rightarrow> 'a"
      and \<psi> :: "'c set"
    using that
    by (metis closure_mono closure_subset image_comp image_mono) 
  show "closure (A ` closure (B ` (\<psi>::'c set)::'a set)) \<subseteq> closure ((A \<circ> B) ` \<psi>::'b set)"
    if "bounded_clinear (A::'a \<Rightarrow> 'b)"
      and "bounded_clinear (B::'c \<Rightarrow> 'a)"
      and "is_subspace (\<psi>::'c set)"
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
shows  \<open>(A \<cdot>\<^sub>o B) \<cdot>\<^sub>s \<psi> =  A \<cdot>\<^sub>s (B \<cdot>\<^sub>s \<psi>)\<close>
proof-
  have \<open>bounded_clinear (Rep_bounded A)\<close>
    using Rep_bounded by auto
  moreover have \<open>bounded_clinear (Rep_bounded B)\<close>
    using Rep_bounded by auto
  moreover have \<open>is_subspace (Rep_linear_space \<psi>)\<close>
    using Rep_linear_space by auto
  ultimately have  \<open>
     (closure
       ( (Rep_bounded A \<circ> Rep_bounded B) ` Rep_linear_space \<psi>)) =
     (closure
       (Rep_bounded A `
      closure (Rep_bounded B ` Rep_linear_space \<psi>)))\<close>
    using times_comp by blast
  hence  \<open>
     (closure
       ( (Rep_bounded A \<circ> Rep_bounded B) ` Rep_linear_space \<psi>)) =
     (closure
       (Rep_bounded A `
        Rep_linear_space
         (Abs_linear_space
           (closure (Rep_bounded B ` Rep_linear_space \<psi>)))))\<close>
    by (metis Rep_linear_space_inverse applyOpSpace.rep_eq)    
  hence  \<open>
     (closure
       (Rep_bounded (timesOp A B) ` Rep_linear_space \<psi>)) =
     (closure
       (Rep_bounded A `
        Rep_linear_space
         (Abs_linear_space
           (closure (Rep_bounded B ` Rep_linear_space \<psi>)))))\<close>
    by (simp add: timesOp.rep_eq)    
  hence \<open> Abs_linear_space
     (closure
       (Rep_bounded (timesOp A B) ` Rep_linear_space \<psi>)) =
    Abs_linear_space
     (closure
       (Rep_bounded A `
        Rep_linear_space
         (Abs_linear_space
           (closure (Rep_bounded B ` Rep_linear_space \<psi>)))))\<close>
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
  shows "U \<cdot>\<^sub>s bot = bot"
proof-
  have \<open>closed {0::'a}\<close>
    using Topological_Spaces.t1_space_class.closed_singleton by blast
  hence \<open>closure {0::'a} = {0}\<close>
    by (simp add: closure_eq)    
  moreover have \<open>Rep_bounded U ` {0::'a} = {0}\<close>
  proof-
    have \<open>bounded_clinear (Rep_bounded U)\<close>
      using Rep_bounded by auto
    hence  \<open>Rep_bounded U 0 = 0\<close>
      by (simp add: bounded_clinear.clinear clinear_zero)
    thus ?thesis
      by simp 
  qed
  ultimately have \<open>closure (Rep_bounded U ` {0}) = {0}\<close>
    by simp
  hence \<open>(closure (Rep_bounded U ` Rep_linear_space (Abs_linear_space {0}))) = {0}\<close>
    by (metis bot_linear_space.abs_eq bot_linear_space.rep_eq) 
  thus ?thesis
    unfolding applyOpSpace_def bot_linear_space_def by simp
qed

(* TODO: remove chilbert_space *)
(* TODO: remove (equal_span can be proven more elegantly using induction over the span) *)
lemma equal_span_0_n:
  fixes f::\<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close> and S::\<open>'a set\<close>
  shows \<open>\<forall> x::'a.
x \<in> partial_span n S \<longrightarrow>
 bounded_clinear f \<longrightarrow>
(\<forall> t \<in> S. f t = 0) \<longrightarrow> 
f x = 0\<close>
proof(induction n)
  case 0
  have \<open>x \<in> partial_span 0 S \<Longrightarrow> bounded_clinear f \<Longrightarrow> \<forall> t \<in> S. f t = 0 \<Longrightarrow> f x = 0\<close>
    for x::'a
  proof-
    assume \<open>x \<in> partial_span 0 S\<close> and \<open>bounded_clinear f\<close> and \<open>\<forall> t \<in> S. f t = 0\<close>
    from \<open>x \<in> partial_span 0 S\<close>
    have \<open>x = 0\<close>
      by simp
    thus ?thesis using \<open>bounded_clinear f\<close>
      by (simp add: bounded_clinear.clinear clinear_zero) 
  qed
  thus ?case by blast
next
  case (Suc n) 
  have \<open>x \<in> partial_span (Suc n) S \<Longrightarrow> bounded_clinear f \<Longrightarrow> \<forall> t \<in> S. f t = 0 \<Longrightarrow> f x = 0\<close>
    for x
  proof-
    assume \<open>x \<in> partial_span (Suc n) S\<close> and \<open>bounded_clinear f\<close> and \<open>\<forall> t \<in> S. f t = 0\<close>
    from \<open>x \<in> partial_span (Suc n) S\<close>
    have \<open>x \<in> {t + a *\<^sub>C y | a t y. t \<in> partial_span n S \<and> y \<in> S}\<close>
      by simp
    hence \<open>\<exists> a t y. t \<in> partial_span n S \<and> y \<in> S \<and> x = t + a *\<^sub>C y\<close>
      by blast
    then obtain a t y where \<open>t \<in> partial_span n S\<close> and \<open>y \<in> S\<close> and \<open>x = t + a *\<^sub>C y\<close>
      by blast
    have \<open>f t = 0\<close>
      using  \<open>t \<in> partial_span n S\<close> \<open>bounded_clinear f\<close> \<open>\<forall> t \<in> S. f t = 0\<close> Suc.IH by blast
    moreover have \<open>f y = 0\<close>
      using \<open>y \<in> S\<close>  \<open>\<forall> t \<in> S. f t = 0\<close>  by blast
    moreover have  \<open>f x = f t + f (a *\<^sub>C y)\<close>
      using \<open>bounded_clinear f\<close>  \<open>x = t + a *\<^sub>C y\<close>
      unfolding bounded_clinear_def clinear_def Modules.additive_def by simp    
    hence  \<open>f x = f t + a *\<^sub>C f y\<close>
      using \<open>bounded_clinear f\<close>  
      unfolding bounded_clinear_def clinear_def 
      by simp
    ultimately show ?thesis by simp
  qed
  thus ?case by blast
qed

(* TODO: remove chilbert_space (instead: complex_vector) *)
(* TODO: much simpler proof using rule complex_vector.span_induct *)
(* TODO: move to Complex_Vector_Spaces *)
(* TODO: After updating Complex_Vector_Spaces, possibly this theorem will already exist *)
lemma equal_span_0:
  fixes f::\<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close> 
    and S::\<open>'a set\<close> and x::'a
(* TODO: clinear f sufficient *) 
  assumes \<open>bounded_clinear f\<close> and \<open>\<forall> t \<in> S. f t = 0\<close> and xS: \<open>x \<in> complex_vector.span S\<close> 
(* TODO: remove S\<noteq>{} *)
    and \<open>S \<noteq> {}\<close>
  shows \<open>f x = 0\<close>
  (* TODO: use proof (rule complex_vector.span_induct[where S=S]) *)
proof -
  have \<open>x \<in> closure (complex_vector.span S)\<close>
    using  \<open>x \<in> complex_vector.span S\<close> closure_subset by auto
  hence \<open>x \<in> closure (\<Union> n::nat. partial_span n S)\<close>
    using  \<open>S \<noteq> {}\<close> partial_span_lim by blast
  hence \<open>\<exists> y::nat \<Rightarrow> _. (\<forall> k. y k \<in> (\<Union> n::nat. partial_span n S)) \<and> y \<longlonglongrightarrow> x\<close>
    using closure_sequential by blast
  then obtain y 
    where \<open>\<forall> k. y k \<in> (\<Union> n::nat. partial_span n S)\<close> and \<open>y \<longlonglongrightarrow> x\<close>
    by blast
  hence \<open>\<forall> k. \<exists> n. y k \<in> partial_span n S\<close>
    by blast
  then obtain n where \<open>\<forall> k. y k \<in> partial_span (n k) S\<close>
    by metis
  hence \<open>\<forall> k. f (y k) = 0\<close>
    using assms(1) assms(2) equal_span_0_n by blast
  have \<open>isCont f x\<close>
    using \<open>bounded_clinear f\<close>
    by (simp add: bounded_linear_continuous)
  hence  \<open>(\<lambda> k. f (y k)) \<longlonglongrightarrow> f x\<close>
    using \<open>y \<longlonglongrightarrow> x\<close> isCont_tendsto_compose by auto 
  hence \<open>(\<lambda> k. 0) \<longlonglongrightarrow> f x\<close>
    using  \<open>\<forall> k. f (y k) = 0\<close> 
    by simp
  moreover have  \<open>(\<lambda> k. 0) \<longlonglongrightarrow> (0::'b)\<close>
    by simp
  ultimately show ?thesis
    using LIMSEQ_unique by blast
qed

(* TODO: remove chilbert_space *)
lemma equal_generator_0:
  fixes A::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and S::\<open>'a set\<close>
  assumes \<open>cgenerator S\<close> and \<open>\<And>x. x \<in> S \<Longrightarrow> A \<cdot>\<^sub>v x = 0\<close> and  \<open>S \<noteq> {}\<close>
  shows  \<open>A = 0\<close>
proof-
  have \<open>Rep_bounded A = Rep_bounded (0::('a,'b) bounded)\<close>
  proof
    show "Rep_bounded A x = Rep_bounded 0 x"
      for x :: 'a
    proof-
      have \<open>Rep_bounded (0::('a, 'b) bounded) x = 0\<close>
        by (simp add: zero_bounded.rep_eq)        
      moreover have \<open>Rep_bounded A x = 0\<close>
      proof-
        have \<open>bounded_clinear (Rep_bounded A)\<close>
          using Rep_bounded by auto          
        have \<open>Abs_linear_space (closure (complex_vector.span S)) =
                Abs_linear_space UNIV\<close>
          using  \<open>cgenerator S\<close>  
          unfolding cgenerator_def top_linear_space_def Complex_Inner_Product.span_def
          by auto          
        hence \<open>closure (complex_vector.span S) = UNIV\<close>
          by (metis assms(1) cgenerator_def span.rep_eq top_linear_space.rep_eq)          
        hence  \<open>x \<in> closure (complex_vector.span S)\<close>
          by blast
        hence \<open>\<exists> y. (\<forall> n::nat. y n \<in> complex_vector.span S) \<and> y \<longlonglongrightarrow> x\<close>
          using closure_sequential by auto
        then obtain y where \<open>\<forall> n::nat. y n \<in> complex_vector.span S\<close> and \<open>y \<longlonglongrightarrow> x\<close>
          by blast
        have \<open>isCont (Rep_bounded A) x\<close>
          using \<open>bounded_clinear (Rep_bounded A)\<close>
          by (simp add: bounded_linear_continuous) 
        hence \<open>(\<lambda> n.  Rep_bounded A (y n)) \<longlonglongrightarrow> Rep_bounded A x\<close>
          using \<open>y \<longlonglongrightarrow> x\<close>
          by (simp add: isCont_tendsto_compose)
        moreover have \<open>Rep_bounded A (y n) = 0\<close>
          for n
        proof-
          from \<open>\<forall> n::nat. y n \<in> complex_vector.span S\<close>
          have \<open>y n \<in> complex_vector.span S\<close>
            by blast
          thus ?thesis using equal_span_0
            using assms(2)
            using \<open>bounded_clinear (Rep_bounded A)\<close>  \<open>S \<noteq> {}\<close> by auto  
        qed
        ultimately have \<open>(\<lambda> n.  0) \<longlonglongrightarrow> Rep_bounded A x\<close>
          by simp
        thus \<open>Rep_bounded A x = 0\<close>
          by (simp add: LIMSEQ_const_iff)
      qed
      ultimately show ?thesis by simp
    qed
  qed
  thus ?thesis using Rep_bounded_inject by blast 
qed

lemma equal_generator:
  fixes A B::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and S::\<open>'a set\<close>
  assumes \<open>cgenerator S\<close> and \<open>\<And>x. x \<in> S \<Longrightarrow> Rep_bounded A x = Rep_bounded B x\<close> and  \<open>S \<noteq> {}\<close>
  shows \<open>A = B\<close>
proof-
  have \<open>A - B = 0\<close>
  proof-
    have \<open>x \<in> S \<Longrightarrow> Rep_bounded (A - B) x = 0\<close>
      for x
    proof-
      assume \<open>x \<in> S\<close>
      hence \<open>Rep_bounded A x = Rep_bounded B x\<close>
        using \<open>x \<in> S \<Longrightarrow> Rep_bounded A x = Rep_bounded B x\<close>
        by blast
      hence \<open>Rep_bounded A x - Rep_bounded B x = 0\<close>
        by simp
      hence \<open>(Rep_bounded A - Rep_bounded B) x = 0\<close>
        by simp
      moreover have \<open>Rep_bounded (A - B) = (\<lambda> t. Rep_bounded A t - Rep_bounded B t)\<close>
        by (simp add: minus_bounded.rep_eq)        
      ultimately have \<open>Rep_bounded (A - B) x = 0\<close>
        by simp
      thus ?thesis by simp 
    qed
    thus ?thesis
      using assms(1) equal_generator_0  \<open>S \<noteq> {}\<close> by blast 
  qed
  thus ?thesis by simp
qed

lemma cdot_plus_distrib_transfer:
  \<open>bounded_clinear U \<Longrightarrow>
       is_subspace A \<Longrightarrow>
       is_subspace B \<Longrightarrow>
        (closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
  for U::\<open>'a::complex_normed_vector\<Rightarrow>'b::complex_normed_vector\<close> and A B::\<open>'a set\<close>
proof-
  assume \<open>bounded_clinear U\<close> and \<open>is_subspace A\<close> and \<open>is_subspace B\<close> 
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
          unfolding bounded_clinear_def clinear_def Modules.additive_def
          by auto
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
        using \<open>bounded_clinear U\<close>
        unfolding bounded_clinear_def clinear_def Modules.additive_def
        by auto
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
  shows \<open> U \<cdot>\<^sub>s (A + B) = (U \<cdot>\<^sub>s A) + (U \<cdot>\<^sub>s B)\<close>
proof-
  {  have   \<open>
       bounded_clinear U \<Longrightarrow>
       is_subspace A \<Longrightarrow>
       is_subspace B \<Longrightarrow>
       Abs_linear_space
        (closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
       Abs_linear_space
        (closure
          {\<psi> + \<phi> |\<psi> \<phi>.
           \<psi> \<in> Rep_linear_space (Abs_linear_space (closure (U ` A))) \<and>
           \<phi> \<in> Rep_linear_space (Abs_linear_space (closure (U ` B)))})\<close>
      for U::\<open>'a\<Rightarrow>'b\<close> and A B::\<open>'a set\<close>
    proof-
      assume \<open>bounded_clinear U\<close> and \<open>is_subspace A\<close> and \<open>is_subspace B\<close> 
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
        by (smt Collect_cong Rep_bounded_cases Rep_linear_space \<open>bounded_clinear U\<close> \<open>is_subspace A\<close> \<open>is_subspace B\<close> applyOpSpace.rep_eq mem_Collect_eq)
    qed    
  } note 1 = this

  show ?thesis 
    unfolding plus_bounded_def applyOpSpace_def apply auto apply transfer 
    unfolding closed_sum_def Minkoswki_sum_def
    apply auto
    unfolding plus_linear_space_def closed_sum_def Minkoswki_sum_def
    apply auto
    apply (rule 1) 
    by blast
qed

lemma scalar_op_linear_space_assoc [simp]: 
  
  fixes A::\<open>('a::chilbert_space,'b::chilbert_space) bounded\<close>
    and S::\<open>'a linear_space\<close> and \<alpha>::complex
  shows \<open>(\<alpha> *\<^sub>C A) \<cdot>\<^sub>s S  = \<alpha> *\<^sub>C (A \<cdot>\<^sub>s S)\<close>
proof-
  have \<open>closure ( ( ((*\<^sub>C) \<alpha>) \<circ> (Rep_bounded A) ) ` Rep_linear_space S) =
   ((*\<^sub>C) \<alpha>) ` (closure (Rep_bounded A ` Rep_linear_space S))\<close>
    by (metis closure_scaleC image_comp)    
  hence \<open>(closure (Rep_bounded (\<alpha> *\<^sub>C A) ` Rep_linear_space S)) =
   ((*\<^sub>C) \<alpha>) ` (closure (Rep_bounded A ` Rep_linear_space S))\<close>
    by (metis (mono_tags, lifting) comp_apply image_cong scaleC_bounded.rep_eq)
  hence \<open>Abs_linear_space
     (closure (Rep_bounded (\<alpha> *\<^sub>C A) ` Rep_linear_space S)) =
    \<alpha> *\<^sub>C
    Abs_linear_space (closure (Rep_bounded A ` Rep_linear_space S))\<close>
    by (metis Rep_linear_space_inverse applyOpSpace.rep_eq scaleC_linear_space.rep_eq)    
  show ?thesis 
    unfolding applyOpSpace_def apply auto
    using \<open>Abs_linear_space
     (closure (Rep_bounded (\<alpha> *\<^sub>C A) ` Rep_linear_space S)) =
    \<alpha> *\<^sub>C Abs_linear_space (closure (Rep_bounded A ` Rep_linear_space S))\<close>
    by blast
qed

lemma applyOpSpace_id[simp]: 

shows "idOp \<cdot>\<^sub>s \<psi> = \<psi>"
proof-
  have \<open>is_subspace ( Rep_linear_space \<psi>)\<close>
    using Rep_linear_space by blast    
  hence \<open>closed ( Rep_linear_space \<psi>)\<close>
    unfolding is_subspace_def by blast
  hence \<open>closure ( Rep_linear_space \<psi>) = Rep_linear_space \<psi>\<close>
    by simp    
  hence \<open>(closure ( id ` Rep_linear_space \<psi>)) = Rep_linear_space \<psi>\<close>
    by simp    
  hence \<open>(closure (Rep_bounded (Abs_bounded id) ` Rep_linear_space \<psi>)) = Rep_linear_space \<psi>\<close>
    by (metis idOp.abs_eq idOp.rep_eq)    
  hence \<open>Abs_linear_space
     (closure (Rep_bounded (Abs_bounded id) ` Rep_linear_space \<psi>)) = \<psi>\<close>
    by (simp add: Rep_linear_space_inverse)    
  show ?thesis
    unfolding applyOpSpace_def idOp_def
    apply auto
    using  \<open>Abs_linear_space
     (closure (Rep_bounded (Abs_bounded id) ` Rep_linear_space \<psi>)) = \<psi>\<close>
    by blast
qed

lemma scalar_op_op[simp]:
  fixes A::"('b::complex_normed_vector,'c::complex_normed_vector) bounded"
    and B::"('a::complex_normed_vector, 'b) bounded"
  shows \<open>(a *\<^sub>C A) \<cdot>\<^sub>o B = a *\<^sub>C (A \<cdot>\<^sub>o B)\<close>
proof-
  have \<open>(rtimesOp (a *\<^sub>C (rbounded_of_bounded A))
       (rbounded_of_bounded B)) =
   ( a *\<^sub>C  (rtimesOp (rbounded_of_bounded A) (rbounded_of_bounded B)) )\<close>
    by (simp add: rscalar_op_op)
  hence \<open>(rtimesOp (rbounded_of_bounded (a *\<^sub>C A))
       (rbounded_of_bounded B)) =
   ( a *\<^sub>C  (rtimesOp (rbounded_of_bounded A) (rbounded_of_bounded B)) )\<close>
    by (simp add: rbounded_of_bounded_scaleC)    
  hence \<open>bounded_of_rbounded
     (rtimesOp (rbounded_of_bounded (a *\<^sub>C A))
       (rbounded_of_bounded B)) =
    bounded_of_rbounded
   ( a *\<^sub>C  (rtimesOp (rbounded_of_bounded A) (rbounded_of_bounded B)) )\<close>
    by simp    
  hence \<open>bounded_of_rbounded
     (rtimesOp (rbounded_of_bounded (a *\<^sub>C A))
       (rbounded_of_bounded B)) =
    a *\<^sub>C bounded_of_rbounded
     (rtimesOp (rbounded_of_bounded A) (rbounded_of_bounded B))\<close>
    by (simp add: bounded_of_rbounded_scaleC rbounded_of_bounded_prelim rtimesOp_scaleC)  
  thus ?thesis
    by (metis bounded_rbounded rbounded_of_bounded_timesOp)   
qed


lemma op_scalar_op[simp]:
  fixes A::"('b::complex_normed_vector,'c::complex_normed_vector) bounded" 
    and B::"('a::complex_normed_vector, 'b) bounded"
  shows \<open>A \<cdot>\<^sub>o (a *\<^sub>C B) = a *\<^sub>C (A \<cdot>\<^sub>o B)\<close>
  using op_rscalar_op
  by (simp add: op_rscalar_op rbounded_of_bounded_inj rbounded_of_bounded_prelim rbounded_of_bounded_scaleC rbounded_of_bounded_timesOp)

lemma times_idOp1[simp]: 
  shows "U \<cdot>\<^sub>o idOp = U"
  by (metis Rep_bounded_inject comp_id idOp.rep_eq timesOp.rep_eq)

lemma times_idOp2[simp]: 
  shows "idOp \<cdot>\<^sub>o U  = U"
  by (metis Rep_bounded_inject idOp.rep_eq id_comp timesOp.rep_eq)

lemma mult_INF1[simp]:
  fixes U :: "('b::complex_normed_vector,'c::cbanach) bounded"
    and V :: "'a \<Rightarrow> 'b linear_space" 
  shows \<open>U \<cdot>\<^sub>s (INF i. V i) \<le> (INF i. U \<cdot>\<^sub>s (V i))\<close>
proof-
  have \<open>bounded_clinear U \<Longrightarrow>
       \<forall>j. is_subspace (V j) \<Longrightarrow> closure (U ` \<Inter> (range V)) \<subseteq> closure (U ` V i)\<close>
    for U::\<open>'b\<Rightarrow>'c\<close> and V::\<open>'a \<Rightarrow> 'b set\<close> and x::'c and i::'a
  proof-
    assume \<open>bounded_clinear U\<close> and \<open>\<forall>j. is_subspace (V j)\<close> 
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

(* TODO: in this form, this doesn't work well as a simp-rule (there was an = before).
        (see mult_inf_distrib' at end of file)
   TODO: state using \<sqinter>/inf, not *
*)
lemma mult_inf_distrib:
  fixes U::\<open>('a::chilbert_space,'b::chilbert_space) bounded\<close> and B C::"'a linear_space"
  shows "U \<cdot>\<^sub>s (B * C) \<le> (U \<cdot>\<^sub>s B) * (U \<cdot>\<^sub>s C)"
proof-
  have \<open>bounded_clinear U \<Longrightarrow>
       is_subspace B \<Longrightarrow>
       is_subspace C \<Longrightarrow>
       closure (U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
    for U::\<open>'a\<Rightarrow>'b\<close> and B C::\<open>'a set\<close>
  proof-
    assume \<open>bounded_clinear U\<close> and \<open>is_subspace B\<close> and \<open>is_subspace C\<close>
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
       is_subspace B \<Longrightarrow>
       is_subspace C \<Longrightarrow>
       closure (U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
    by blast
qed


(* TODO: remove (this is the same as equal_span_0) *)
lemma applyOpSpace_span_transfer0:
  fixes A :: "'a::chilbert_space \<Rightarrow> 'b::chilbert_space"
(* TODO needs only clinear *)
  assumes \<open>bounded_clinear A\<close> and
    \<open>\<And>x. x \<in> G \<Longrightarrow> A x = 0\<close> and \<open>t \<in> (complex_vector.span G)\<close>
  shows \<open>A t = 0\<close>
  thm equal_span_0
proof(cases \<open>G = {}\<close>)
  case True
  hence \<open>(complex_vector.span G) = {0}\<close>
    by simp
  hence \<open>t = 0\<close>
    using assms(3) by blast
  moreover have \<open>A 0 = 0\<close>
    by (metis True assms(1) assms(3) calculation complex_vector.span_empty empty_iff equal_span_0_n partial_span.simps(1))
  ultimately show ?thesis
    by simp 
next
case False
  thus ?thesis
    using assms(1) assms(2) assms(3) equal_span_0 by blast 
qed

(* TODO: Rename to equal_span *)
lemma applyOpSpace_span_transfer:
  fixes A B :: "'a::chilbert_space \<Rightarrow> 'b::chilbert_space"
(* TODO: clinear is sufficient *)
  assumes \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close> and
       \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and \<open>t \<in> (complex_vector.span G)\<close>
  shows \<open>A t = B t\<close>
proof-
  define F where \<open>F = (\<lambda> x. A x - B x)\<close>
  hence \<open>bounded_clinear F\<close>
    using  \<open>bounded_clinear A\<close>  \<open>bounded_clinear B\<close>  Complex_Vector_Spaces.bounded_clinear_sub
    by auto
  moreover have \<open>\<And>x. x \<in> G \<Longrightarrow> F x = 0\<close>
    by (simp add: F_def assms(3))
  ultimately have \<open>F t = 0\<close>
    using \<open>t \<in> (complex_vector.span G)\<close>
    using applyOpSpace_span_transfer0 by blast
  thus ?thesis
    using F_def by auto 
qed

(* TODO: Remove chilbert_space *)
(* TODO: Rename to equal_span-something *)
lemma applyOpSpace_closure_span_transfer:
  fixes A B :: "'a::chilbert_space \<Rightarrow> 'b::chilbert_space"
  assumes \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close> and
       \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and \<open>t \<in> closure (complex_vector.span G)\<close>
  shows \<open>A t = B t\<close>
proof-
  define F where \<open>F x = A x - B x\<close> for x
  hence \<open>F = (\<lambda>x. A x - B x)\<close>
    by blast
  hence \<open>bounded_clinear F\<close>
    using \<open>bounded_clinear A\<close>  \<open>bounded_clinear B\<close> Complex_Vector_Spaces.bounded_clinear_sub
    by blast
  hence \<open>isCont F x\<close>
    for x
    by (simp add: bounded_linear_continuous)    
  hence \<open>continuous_on UNIV F\<close>
    by (simp add: continuous_at_imp_continuous_on)    
  hence \<open>continuous_on (closure (complex_vector.span G)) F\<close>
    using continuous_on_subset by blast    
  moreover have \<open>\<And> s. s \<in> (complex_vector.span G) \<Longrightarrow> F s = 0\<close>
    using \<open>F \<equiv> \<lambda>x. A x - B x\<close> applyOpSpace_span_transfer assms(1) assms(2) assms(3) by auto    
  ultimately have \<open>F t = 0\<close>
    using \<open>t \<in> closure (complex_vector.span G)\<close> 
      by (rule Abstract_Topology_2.continuous_constant_on_closure)
    thus ?thesis
      using F_def by auto 
qed

(* TODO: Remove chilbert_space *)
lemma applyOpSpace_span:
  fixes A B :: "('a::chilbert_space,'b::chilbert_space) bounded"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A \<cdot>\<^sub>v x = B \<cdot>\<^sub>v x" and \<open>t \<in> Rep_linear_space (span G)\<close>
  shows "A \<cdot>\<^sub>v t = B \<cdot>\<^sub>v t"
  using assms
  apply transfer
  using applyOpSpace_closure_span_transfer by blast

(* TODO: Remove chilbert_space? *)
lemma applyOpSpace_less_eq:
  fixes S :: "'a::chilbert_space linear_space" 
    and A B :: "('a::chilbert_space,'b::chilbert_space) bounded"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A \<cdot>\<^sub>v x = B \<cdot>\<^sub>v x" and "span G \<ge> S"
  shows "A \<cdot>\<^sub>s S \<le> B \<cdot>\<^sub>s S"
proof-
  have \<open>t \<in> ((\<cdot>\<^sub>v) A ` Rep_linear_space S) \<Longrightarrow> t \<in> ((\<cdot>\<^sub>v) B ` Rep_linear_space S)\<close>
    for t
  proof-
    assume \<open>t \<in> ((\<cdot>\<^sub>v) A ` Rep_linear_space S)\<close>
    hence \<open>\<exists> x\<in>Rep_linear_space S. t = A \<cdot>\<^sub>v x\<close>
      by blast
    then obtain x where \<open>x\<in>Rep_linear_space S\<close> and \<open>t = A \<cdot>\<^sub>v x\<close>
      by blast
    have \<open>x \<in> Rep_linear_space (span G)\<close>
      using  \<open>x\<in>Rep_linear_space S\<close> assms(2) less_eq_linear_space.rep_eq by blast
    hence \<open>A \<cdot>\<^sub>v x = B \<cdot>\<^sub>v x\<close>
      using applyOpSpace_span assms(1) by blast
    thus ?thesis
      by (simp add: \<open>t = A \<cdot>\<^sub>v x\<close> \<open>x \<in> Rep_linear_space S\<close>)      
  qed
  hence \<open>((\<cdot>\<^sub>v) A ` Rep_linear_space S) \<subseteq> ((\<cdot>\<^sub>v) B ` Rep_linear_space S)\<close>
    by blast
  have \<open>t \<in> Rep_linear_space (A \<cdot>\<^sub>s S) \<Longrightarrow> t \<in> Rep_linear_space (B \<cdot>\<^sub>s S)\<close>
    for t
  proof-
    assume \<open>t \<in> Rep_linear_space (A \<cdot>\<^sub>s S)\<close>
    hence  \<open>t \<in> Rep_linear_space
          (Abs_linear_space (closure ((\<cdot>\<^sub>v) A ` Rep_linear_space S)))\<close>
      unfolding applyOpSpace_def
      by  auto
    hence  \<open>t \<in> closure ((\<cdot>\<^sub>v) A ` Rep_linear_space S)\<close>
      using Abs_linear_space_inverse \<open>t \<in> Rep_linear_space (A \<cdot>\<^sub>s S)\<close> applyOpSpace.rep_eq by blast
    moreover have \<open>closure ((\<cdot>\<^sub>v) A ` Rep_linear_space S) \<subseteq>  closure ((\<cdot>\<^sub>v) B ` Rep_linear_space S)\<close>
      using  \<open>((\<cdot>\<^sub>v) A ` Rep_linear_space S) \<subseteq> ((\<cdot>\<^sub>v) B ` Rep_linear_space S)\<close>
        by (simp add: closure_mono) 
    ultimately have  \<open>t \<in> closure ((\<cdot>\<^sub>v) B ` Rep_linear_space S)\<close>
      by blast      
    hence  \<open>t \<in> Rep_linear_space
          (Abs_linear_space (closure ((\<cdot>\<^sub>v) B ` Rep_linear_space S)))\<close>
      by (metis Rep_linear_space_inverse applyOpSpace.rep_eq)      
    thus ?thesis
      by (simp add: \<open>t \<in> closure ((\<cdot>\<^sub>v) B ` Rep_linear_space S)\<close> applyOpSpace.rep_eq) 
  qed
  hence \<open>Rep_linear_space (A \<cdot>\<^sub>s S) \<subseteq> Rep_linear_space (B \<cdot>\<^sub>s S)\<close>
    by blast
  thus ?thesis
    by (simp add: less_eq_linear_space.rep_eq) 
qed

(* TODO: Remove chilbert_space? *)
lemma applyOpSpace_eq:
  fixes S :: "'a::chilbert_space linear_space" 
    and A B :: "('a::chilbert_space,'b::chilbert_space) bounded"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A \<cdot>\<^sub>v x = B \<cdot>\<^sub>v x" and "span G \<ge> S"
  shows "A \<cdot>\<^sub>s S = B \<cdot>\<^sub>s S"
  using applyOpSpace_less_eq
  by (metis assms(1) assms(2) order_class.order.antisym)


(* NEW *)
section \<open>Endomorphism algebra\<close>

(* https://en.wikipedia.org/wiki/Endomorphism_ring  *)
(* TODO Rename: endo \<rightarrow> Bounded *)
typedef (overloaded) ('a::complex_normed_vector) endo 
  = \<open>{f :: 'a\<Rightarrow>'a. bounded_clinear f}\<close>
  (* = \<open>UNIV::('a,'a) bounded set\<close> *)
  using bounded_clinear_ident by blast

(* Example:
setup_lifting type_definition_endo

lift_definition times_endo :: "'a::complex_normed_vector endo \<Rightarrow> 'a endo \<Rightarrow> 'a endo"
  is "timesOp".

lemma
  fixes a b :: "_ endo"
  shows "times_endo a b = times_endo b a"
  apply transfer
  using [[show_sorts]]
*)

definition bounded_of_endo:: \<open>'a::complex_normed_vector endo \<Rightarrow> ('a, 'a) bounded\<close>  where 
\<open>bounded_of_endo f = Abs_bounded (Rep_endo f)\<close>

definition endo_of_bounded:: \<open>('a::complex_normed_vector, 'a) bounded \<Rightarrow> 'a endo\<close>  where 
\<open>endo_of_bounded f = Abs_endo (Rep_bounded f)\<close>

lemma endo_of_bounded_inj:
\<open>endo_of_bounded f = endo_of_bounded g \<Longrightarrow> f = g\<close>
  by (metis Abs_endo_inject endo_of_bounded_def Rep_bounded Rep_bounded_inject)

lemma bounded_of_endo_inj:
\<open>bounded_of_endo f = bounded_of_endo g \<Longrightarrow> f = g\<close>
  by (metis Abs_bounded_inject Rep_endo Rep_endo_inject bounded_of_endo_def)

lemma endo_of_bounded_inv:
\<open>bounded_of_endo (endo_of_bounded f) = f\<close>
  by (metis Abs_endo_inverse endo_of_bounded_def Rep_bounded Rep_bounded_inverse bounded_of_endo_def)

lemma bounded_of_endo_inv:
\<open>endo_of_bounded (bounded_of_endo f) = f\<close>
  using endo_of_bounded_inv bounded_of_endo_inj by auto

instantiation endo :: (complex_normed_vector) \<open>complex_normed_vector\<close>
begin

definition zero_endo::"'a endo" 
  where "zero_endo = endo_of_bounded (0::('a,'a) bounded)"

definition plus_endo::"'a endo \<Rightarrow> 'a endo \<Rightarrow> 'a endo" 
  where "plus_endo f g =  endo_of_bounded ( (bounded_of_endo f)+(bounded_of_endo g) )"

definition uminus_endo::"'a endo \<Rightarrow> 'a endo" 
  where "uminus_endo f =  endo_of_bounded (- (bounded_of_endo f))"

definition minus_endo::"'a endo \<Rightarrow> 'a endo \<Rightarrow> 'a endo" 
  where "minus_endo f g =  endo_of_bounded ( (bounded_of_endo f)-(bounded_of_endo g) )"

definition scaleC_endo :: \<open>complex \<Rightarrow> 'a endo \<Rightarrow> 'a endo\<close>
  where "scaleC_endo c f =  endo_of_bounded ( c *\<^sub>C (bounded_of_endo f) )"

definition scaleR_endo :: \<open>real \<Rightarrow> 'a endo \<Rightarrow> 'a endo\<close>
  where "scaleR_endo c f =  endo_of_bounded ( c *\<^sub>R (bounded_of_endo f) )"

definition norm_endo :: \<open>'a endo \<Rightarrow> real\<close>
  where \<open>norm_endo f = norm (bounded_of_endo f)\<close>

definition dist_endo :: \<open>'a endo \<Rightarrow> 'a endo \<Rightarrow> real\<close>
  where \<open>dist_endo f g = dist (bounded_of_endo f) (bounded_of_endo g)\<close>

definition sgn_endo :: \<open>'a endo \<Rightarrow> 'a endo\<close>
  where \<open>sgn_endo f =  endo_of_bounded ( sgn (bounded_of_endo f))\<close>

definition uniformity_endo :: \<open>( 'a  endo \<times> 'a endo ) filter\<close>
  where \<open>uniformity_endo = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a endo) y < e})\<close>

definition open_endo :: \<open>('a endo) set \<Rightarrow> bool\<close>
  where \<open>open_endo U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a endo) = x \<longrightarrow> y \<in> U)\<close>

instance
  proof
  show \<open>((*\<^sub>R) r::'a endo \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
    for r :: real
    unfolding scaleR_endo_def scaleC_endo_def
    by (simp add: scaleR_scaleC)
    
  show "(a::'a endo) + b + c = a + (b + c)"
    for a :: "'a endo"
      and b :: "'a endo"
      and c :: "'a endo"
    by (simp add: endo_of_bounded_inv ab_semigroup_add_class.add_ac(1) plus_endo_def)


  show "(a::'a endo) + b = b + a"
    for a :: "'a endo"
      and b :: "'a endo"
    by (simp add: add.commute plus_endo_def)
    
  show "(0::'a endo) + a = a"
    for a :: "'a endo"
    by (simp add: endo_of_bounded_inv Bounded_Operators.plus_endo_def Bounded_Operators.zero_endo_def bounded_of_endo_inv)
    
  show "- (a::'a endo) + a = 0"
    for a :: "'a endo"
    by (simp add: endo_of_bounded_inv plus_endo_def uminus_endo_def zero_endo_def)

  show "(a::'a endo) - b = a + - b"
    for a :: "'a endo"
      and b :: "'a endo"
    by (metis (full_types) endo_of_bounded_inv ab_group_add_class.ab_diff_conv_add_uminus minus_endo_def plus_endo_def uminus_endo_def)
    
  show \<open>a *\<^sub>C ((x::'a endo) + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    for a :: complex
      and x :: "'a endo"
      and y :: "'a endo"
    by (simp add: endo_of_bounded_inv plus_endo_def scaleC_endo_def scaleC_add_right)

  show "(a + b) *\<^sub>C (x::'a endo) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a endo"
    by (simp add: endo_of_bounded_inv Bounded_Operators.plus_endo_def Bounded_Operators.scaleC_endo_def scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::'a endo) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a endo"
    by (simp add: endo_of_bounded_inv scaleC_endo_def)

  show "1 *\<^sub>C (x::'a endo) = x"
    for x :: "'a endo"
    by (simp add: bounded_of_endo_inv scaleC_endo_def)    

  show "dist (x::'a endo) y = norm (x - y)"
    for x :: "'a endo"
      and y :: "'a endo"
    by (simp add: endo_of_bounded_inv Bounded_Operators.minus_endo_def Bounded_Operators.norm_endo_def dist_endo_def dist_norm)

  show "a *\<^sub>R ((x::'a endo) + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real
      and x :: "'a endo"
      and y :: "'a endo"
    using \<open>\<And>r. ((*\<^sub>R) r::'a endo \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
      \<open>\<And> y x a. a *\<^sub>C ((x::'a endo) + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    by fastforce

  show "(a + b) *\<^sub>R (x::'a endo) = a *\<^sub>R x + b *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a endo"
    using  \<open>\<And>r. ((*\<^sub>R) r::'a endo \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
      \<open>\<And> a b x. (a + b) *\<^sub>C (x::'a endo) = a *\<^sub>C x + b *\<^sub>C x\<close>
    by fastforce

  show "a *\<^sub>R b *\<^sub>R (x::'a endo) = (a * b) *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a endo"
    using  \<open>\<And>r. ((*\<^sub>R) r::'a endo \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
      \<open>\<And> a b x. a *\<^sub>C b *\<^sub>C (x::'a endo) = (a * b) *\<^sub>C x\<close>
    by fastforce

  show "1 *\<^sub>R (x::'a endo) = x"
    for x :: "'a endo"
    using  \<open>\<And>r. ((*\<^sub>R) r::'a endo \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
        \<open>1 *\<^sub>C (x::'a endo) = x\<close>
    by fastforce

  show "sgn (x::'a endo) = inverse (norm x) *\<^sub>R x"
    for x :: "'a endo"
    by (simp add: Bounded_Operators.norm_endo_def Bounded_Operators.scaleR_endo_def Bounded_Operators.sgn_endo_def sgn_div_norm)
    
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a endo) y < e})"
    using Bounded_Operators.uniformity_endo_def by auto    

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a endo) = x \<longrightarrow> y \<in> U)"
    for U :: "'a endo set"
    using Bounded_Operators.open_endo_def by auto    

  show "(norm (x::'a endo) = 0) = (x = 0)"
    for x :: "'a endo"
  proof -
    have f1: "\<not> (0::real) < 0"
      by (metis norm_zero zero_less_norm_iff)
    have "bounded_of_endo x = 0 \<longrightarrow> norm (bounded_of_endo x) = 0"
      by auto
    then show ?thesis
      using f1 by (metis (mono_tags) endo_of_bounded_inv Bounded_Operators.zero_endo_def bounded_of_endo_inv norm_endo_def zero_less_norm_iff)
  qed

  show "norm ((x::'a endo) + y) \<le> norm x + norm y"
    for x :: "'a endo"
      and y :: "'a endo"
    by (simp add: endo_of_bounded_inv norm_endo_def norm_triangle_ineq plus_endo_def)
    
  show "norm (a *\<^sub>R (x::'a endo)) = \<bar>a\<bar> * norm x"
    for a :: real
      and x :: "'a endo"
    by (simp add: endo_of_bounded_inv norm_endo_def scaleR_endo_def)
    
  show "norm (a *\<^sub>C (x::'a endo)) = cmod a * norm x"
    for a :: complex
      and x :: "'a endo"
    by (simp add: endo_of_bounded_inv norm_endo_def scaleC_endo_def)
    
qed

end

instantiation endo :: (cbanach) \<open>cbanach\<close>
begin

lemma bounded_of_endo_Cauchy:
  \<open>Cauchy f \<Longrightarrow> Cauchy (\<lambda> n. bounded_of_endo (f n))\<close>
  unfolding Cauchy_def dist_endo_def by blast

lemma endo_of_bounded_tendsto:
  \<open>f \<longlonglongrightarrow> l \<Longrightarrow> (\<lambda> n. endo_of_bounded (f n)) \<longlonglongrightarrow> endo_of_bounded l\<close>
proof-
  assume \<open>f \<longlonglongrightarrow> l\<close>
  hence \<open>N\<in>HNatInfinite \<Longrightarrow> (*f* f) N \<approx> star_of l\<close>
    for N
    by (simp add: LIMSEQ_NSLIMSEQ NSLIMSEQ_D)
  hence \<open>N\<in>HNatInfinite \<Longrightarrow> hnorm ((*f* f) N - star_of l) \<in> Infinitesimal\<close>
    for N
    using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by auto
  moreover have \<open>hnorm ((*f* f) N - star_of l) =
     hnorm ( (*f* (\<lambda> n. endo_of_bounded (f n))) N - star_of (endo_of_bounded l) ) \<close>
    for N
  proof-
    have \<open>\<forall> N. norm (f N -  l) =
     norm (  (\<lambda> n. endo_of_bounded (f n)) N -  (endo_of_bounded l) )\<close>
      unfolding norm_endo_def
      by (simp add: endo_of_bounded_inv minus_endo_def)
    hence \<open>\<forall> N. hnorm ((*f* f) N - star_of l) =
     hnorm ( (*f* (\<lambda> n. endo_of_bounded (f n))) N - star_of (endo_of_bounded l) )\<close>
      by StarDef.transfer
    thus ?thesis by blast
  qed
  ultimately have  \<open>N\<in>HNatInfinite \<Longrightarrow>
   hnorm ( (*f* (\<lambda> n. endo_of_bounded (f n))) N - star_of (endo_of_bounded l) ) \<in> Infinitesimal\<close>
    for N
    by simp    
  hence \<open>N\<in>HNatInfinite \<Longrightarrow> (*f* (\<lambda> n. endo_of_bounded (f n))) N \<approx> star_of  (endo_of_bounded l)\<close>
    for N
    by (simp add: Infinitesimal_approx_minus Infinitesimal_hnorm_iff)    
  hence \<open>(\<lambda> n. endo_of_bounded (f n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S endo_of_bounded l\<close>
    by (simp add: NSLIMSEQ_I)    
  thus ?thesis
    by (simp add: NSLIMSEQ_LIMSEQ)
qed

instance
  proof
  show "convergent (X::nat \<Rightarrow> 'a endo)"
    if "Cauchy (X::nat \<Rightarrow> 'a endo)"
    for X :: "nat \<Rightarrow> 'a endo"
  proof-
    have \<open>Cauchy (\<lambda> n. bounded_of_endo (X n))\<close>
      using that
      by (simp add: bounded_of_endo_Cauchy) 
    hence \<open>convergent (\<lambda> n. bounded_of_endo (X n))\<close>
      by (simp add: Cauchy_convergent)
    then obtain l where \<open>(\<lambda> n. bounded_of_endo (X n)) \<longlonglongrightarrow> l\<close>
      unfolding convergent_def by blast
    hence \<open>(\<lambda> n. endo_of_bounded ( (\<lambda> m. bounded_of_endo (X m)) n) )
             \<longlonglongrightarrow> endo_of_bounded l\<close>
      using endo_of_bounded_tendsto
      by (simp add: endo_of_bounded_tendsto)
    moreover have \<open>endo_of_bounded ( (\<lambda> m. bounded_of_endo (X m)) n) = X n\<close>
      for n
      by (simp add: bounded_of_endo_inv)      
    ultimately show ?thesis
      by (simp add: convergentI) 
  qed
qed
end

instantiation endo::(complex_normed_vector) \<open>ring\<close>
begin 

definition times_endo::\<open>'a endo \<Rightarrow> 'a endo \<Rightarrow> 'a endo\<close> where
\<open>times_endo A B = endo_of_bounded ((bounded_of_endo A) \<cdot>\<^sub>o (bounded_of_endo B))\<close>

instance
  proof
  show "(a::'a endo) * b * c = a * (b * c)"
    for a :: "'a endo"
      and b :: "'a endo"
      and c :: "'a endo"
    by (simp add: endo_of_bounded_inv Bounded_Operators.times_endo_def timesOp_assoc)
    
  show "((a::'a endo) + b) * c = a * c + b * c"
    for a :: "'a endo"
      and b :: "'a endo"
      and c :: "'a endo"
    by (simp add: endo_of_bounded_inv plus_endo_def timesOp_dist1 times_endo_def)
    
  show "(a::'a endo) * (b + c) = a * b + a * c"
    for a :: "'a endo"
      and b :: "'a endo"
      and c :: "'a endo"
        by (simp add: endo_of_bounded_inv plus_endo_def timesOp_dist2 times_endo_def)
qed
end

(* TODO replace perfect_space by the simpler not_singleton *)
instantiation endo::("{complex_normed_vector, perfect_space}") \<open>ring_1\<close>
begin
definition one_endo::\<open>'a endo\<close> where
  \<open>one_endo = endo_of_bounded idOp\<close>

instance
  proof
  show "(1::'a endo) * a = a"
    for a :: "'a endo"
    unfolding one_endo_def times_endo_def
    by (simp add: endo_of_bounded_inv bounded_of_endo_inj)
    
  show "(a::'a endo) * 1 = a"
    for a :: "'a endo"
    unfolding one_endo_def times_endo_def
    by (simp add: endo_of_bounded_inv bounded_of_endo_inj)

  show "(0::'a endo) \<noteq> 1"
  proof-
    have \<open>(0::('a,'a) bounded) \<noteq> idOp\<close>
    proof-
      have \<open>\<exists> x::'a. x \<noteq> 0\<close>
        using UNIV_not_singleton
        by auto
      then obtain x::'a where \<open>x \<noteq> 0\<close>
        by blast
      moreover have \<open>Rep_bounded ((0::('a,'a) bounded)) x = 0\<close>
        by (simp add: zero_bounded.rep_eq)            
      moreover have \<open>Rep_bounded (idOp) x = x\<close>
        by (simp add: idOp.rep_eq)       
      ultimately have \<open>Rep_bounded ((0::('a,'a) bounded)) \<noteq> Rep_bounded (idOp)\<close>
        by auto        
      thus ?thesis using Rep_bounded_inject
        by (simp add: Rep_bounded_inject)
    qed
    thus ?thesis
      unfolding one_endo_def zero_endo_def
      using endo_of_bounded_inj by blast
  qed
qed

end

(* TODO: use same notation ( _* ) as for bounded, and use bundles to disambiguate *)
definition Adj_endo :: "'a::chilbert_space endo \<Rightarrow> 'a endo"  ("_\<^sup>a\<^sup>d\<^sup>j" [99] 100)  where
\<open>Adj_endo A = endo_of_bounded ( (bounded_of_endo A)* )\<close>

lemma Adj_endo_times[simp]:
\<open>(A * B)\<^sup>a\<^sup>d\<^sup>j = (B\<^sup>a\<^sup>d\<^sup>j) * (A\<^sup>a\<^sup>d\<^sup>j)\<close>
  unfolding Adj_endo_def times_endo_def
  by (simp add: endo_of_bounded_inv)

lemma Adj_endo_twices[simp]:
\<open>(A\<^sup>a\<^sup>d\<^sup>j)\<^sup>a\<^sup>d\<^sup>j = A\<close>
  unfolding Adj_endo_def
  by (simp add: bounded_of_endo_inj endo_of_bounded_inv)

lemma Adj_endo_scaleC[simp]:
\<open>(c *\<^sub>C A)\<^sup>a\<^sup>d\<^sup>j = (cnj c) *\<^sub>C (A\<^sup>a\<^sup>d\<^sup>j)\<close>
  by (simp add: Adj_endo_def endo_of_bounded_inv scaleC_endo_def)

lemma Adj_endo_plus[simp]:
\<open>(A + B)\<^sup>a\<^sup>d\<^sup>j = (A\<^sup>a\<^sup>d\<^sup>j) + (B\<^sup>a\<^sup>d\<^sup>j)\<close>
  unfolding Adj_endo_def plus_endo_def
  using Adj_bounded_plus
  by (simp add: Adj_bounded_plus endo_of_bounded_inv)

lemma Adj_endo_uminus[simp]:
\<open>(- A)\<^sup>a\<^sup>d\<^sup>j = - (A\<^sup>a\<^sup>d\<^sup>j)\<close>
  by (metis Adj_endo_plus add.group_axioms add.left_inverse add_cancel_right_left group.right_cancel)

lemma Adj_endo_minus[simp]:
\<open>(A - B)\<^sup>a\<^sup>d\<^sup>j = (A\<^sup>a\<^sup>d\<^sup>j) - (B\<^sup>a\<^sup>d\<^sup>j)\<close>
  by (simp add: additive.diff additive.intro)

lemma Adj_endo_zero[simp]:
\<open>0\<^sup>a\<^sup>d\<^sup>j = 0\<close>
  by (metis Adj_endo_plus Adj_endo_uminus add.right_inverse)

lemma Adj_endo_unit[simp]:
\<open>1\<^sup>a\<^sup>d\<^sup>j = 1\<close>
  by (metis (no_types, lifting) Adj_endo_times Adj_endo_twices Adj_endo_uminus add.inverse_inverse mult_minus1_right)

section \<open>Unitary\<close>

definition isometry::\<open>('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> bool\<close> where
  \<open>isometry U \<longleftrightarrow> U* \<cdot>\<^sub>o  U = idOp\<close>

definition unitary::\<open>('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> bool\<close> where
  \<open>unitary U \<longleftrightarrow> U* \<cdot>\<^sub>o  U  = idOp \<and> U \<cdot>\<^sub>o U* = idOp\<close>

lemma unitary_def': "unitary U \<longleftrightarrow> isometry U \<and> isometry (U*)"
  unfolding unitary_def isometry_def by simp

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* \<cdot>\<^sub>o U = idOp" 
  unfolding isometry_def 
  by simp

lemma UadjU[simp]: "unitary U \<Longrightarrow> U \<cdot>\<^sub>o U* = idOp"
  unfolding unitary_def isometry_def by simp


lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"(_,_)bounded"
  unfolding unitary_def by auto

lemma isometry_times[simp]: "isometry A \<Longrightarrow> isometry B \<Longrightarrow> isometry (A \<cdot>\<^sub>o B)"
  unfolding isometry_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma unitary_times[simp]: "unitary A \<Longrightarrow> unitary B \<Longrightarrow> unitary (A \<cdot>\<^sub>o B)"
  unfolding unitary_def' by simp

lemma unitary_surj: "unitary U \<Longrightarrow> surj (Rep_bounded U)"
proof-
  assume \<open>unitary U\<close>
  have \<open>\<exists> t. (Rep_bounded U) t = x\<close>
    for x
  proof-
    have \<open>(Rep_bounded U) ((Rep_bounded (U*)) x) = x\<close>
    proof-
      have \<open>(Rep_bounded U) ((Rep_bounded (U*)) x)
          = ((Rep_bounded U) \<circ> (Rep_bounded (U*))) x\<close>
        by simp        
      also have \<open>\<dots>
          = (Rep_bounded ( U \<cdot>\<^sub>o (U*) )) x\<close>
        by (simp add: timesOp.rep_eq)
      also have \<open>\<dots>
          = (Rep_bounded ( idOp )) x\<close>
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

lemma unitary_image[simp]: "unitary U \<Longrightarrow> U \<cdot>\<^sub>s top = top"
proof-
  assume \<open>unitary U\<close>
  hence \<open>surj (Rep_bounded U)\<close>
    using unitary_surj by blast
  hence \<open>range (Rep_bounded U)  = UNIV\<close>
    by simp
  hence \<open>closure (range (Rep_bounded U))  = UNIV\<close>
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

definition Proj_endo :: "('a::chilbert_space) linear_space \<Rightarrow> 'a endo" 
 ("\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o_" [99] 100)  where
\<open>Proj_endo S = endo_of_bounded (Proj S)\<close>

lemma imageOp_Proj[simp]: "(Proj S) \<cdot>\<^sub>s top = S"
  apply transfer
  proof
  show "closure (range (projection (S::'a set))) \<subseteq> S"
    if "is_subspace (S::'a set)"
    for S :: "'a set"
    using that
    by (metis (full_types) OrthoClosedEq closure_mono image_subsetI is_subspace.subspace is_subspace_I orthogonal_complement_twice projection_intro2) 
  show "(S::'a set) \<subseteq> closure (range (projection S))"
    if "is_subspace (S::'a set)"
    for S :: "'a set"
    using that
    by (metis (no_types, lifting) closure_subset image_subset_iff in_mono projection_fixed_points subsetI subset_UNIV) 
qed

lemma projection_D1:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_subspace M\<close>
  shows \<open>projection M = (projection M)\<^sup>\<dagger>\<close>
proof-
  have \<open>(projection M) x = ((projection M)\<^sup>\<dagger>) x\<close>
    for x
  proof (rule projection_uniq)
    show \<open>is_subspace M\<close>
      by (simp add: assms)
    show \<open>((projection M)\<^sup>\<dagger>) x \<in> M\<close>
    proof-
      have "y \<in> orthogonal_complement M \<Longrightarrow> \<langle> ((projection M)\<^sup>\<dagger>) x, y \<rangle> = 0"
        for y
      proof-
        assume \<open>y \<in> orthogonal_complement M\<close>
        hence \<open>(projection M) y = 0\<close>
          by (metis add_cancel_right_right assms is_subspace_orthog ortho_decomp orthogonal_complement_twice projection_fixed_points)          
        hence \<open>\<langle> x, (projection M) y \<rangle> = 0\<close>
          by simp          
        thus ?thesis
          by (simp add: Adj_I assms projectionPropertiesA) 
      qed
      hence "((projection M)\<^sup>\<dagger>) x \<in> orthogonal_complement (orthogonal_complement M)"
        unfolding orthogonal_complement_def is_orthogonal_def
        by blast
      thus ?thesis
        by (simp add: assms orthogonal_complement_twice) 
    qed
    show \<open>x - ((projection M)\<^sup>\<dagger>) x \<in> orthogonal_complement M\<close>
    proof (rule orthogonal_complement_I2)
      show "\<langle>x - (projection M\<^sup>\<dagger>) x, y\<rangle> = 0"
        if "y \<in> M"
        for y :: 'a
      proof-
        have \<open>y = projection M y\<close>
          using that(1)
          by (simp add: assms projection_fixed_points)
        hence \<open>y - projection M y = 0\<close>
          by simp
        have \<open>\<langle>x - (projection M\<^sup>\<dagger>) x, y\<rangle> = \<langle>x, y\<rangle> - \<langle>(projection M\<^sup>\<dagger>) x, y\<rangle>\<close>
          by (simp add: cinner_diff_left)
        also have \<open>... = \<langle>x, y\<rangle> - \<langle>x, (projection M) y\<rangle>\<close>
          by (simp add: Adj_I assms projectionPropertiesA)
        also have \<open>... = \<langle>x, y - (projection M) y\<rangle>\<close>
          by (simp add: cinner_diff_right)
        also have \<open>... = \<langle>x, 0\<rangle>\<close>
          using  \<open>y - projection M y = 0\<close>
          by simp
        also have \<open>... = 0\<close>
          by simp          
        finally show ?thesis
          by simp 
      qed
    qed
  qed
  thus ?thesis by blast 
qed

lemma Proj_D1: \<open>(Proj M) = (Proj M)*\<close>
  apply transfer
  by (rule projection_D1)

lemma Proj_endo_D1[simp]:
\<open>(\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M) = (\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M)\<^sup>a\<^sup>d\<^sup>j\<close>
  by (metis Adj_endo_def Proj_D1 Proj_endo_def endo_of_bounded_inv)

lemma Proj_D2[simp]: \<open>(Proj M) \<cdot>\<^sub>o (Proj M) = (Proj M)\<close>
proof-
  have \<open>(Rep_bounded (Proj M)) = projection (Rep_linear_space M)\<close>
    apply transfer
    by blast
  moreover have \<open>(projection (Rep_linear_space M))\<circ>(projection (Rep_linear_space M))
                = (projection (Rep_linear_space M)) \<close>
  proof-
    have \<open>is_subspace (Rep_linear_space M)\<close>
      using Rep_linear_space by auto
    thus ?thesis
      by (simp add: projectionPropertiesC) 
  qed
  ultimately have \<open>(Rep_bounded (Proj M)) \<circ> (Rep_bounded (Proj M)) = Rep_bounded (Proj M)\<close>
    by simp    
  hence \<open>Rep_bounded ((Proj M) \<cdot>\<^sub>o (Proj M)) = Rep_bounded (Proj M)\<close>
    by (simp add: timesOp.rep_eq)
  thus ?thesis using Rep_bounded_inject
    by auto 
qed

lemma Proj_endo_D2[simp]:
\<open>(\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M) * (\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M) = (\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M)\<close>
  unfolding Proj_endo_def times_endo_def
  by (simp add: endo_of_bounded_inv)

(* TODO: Define isProjector as 
    isProjector P \<longleftrightarrow> \<exists> M. is_projection_on P M

    then prove isProjector P \<longleftrightarrow> P \<cdot>\<^sub>o P = P \<and> P = P*
*)

lemma Proj_I:
\<open>P \<cdot>\<^sub>o P = P \<Longrightarrow> P = P* \<Longrightarrow> \<exists> M. P = Proj M \<and> Rep_linear_space M = range (Rep_bounded P)\<close>
  for P :: \<open>('a::chilbert_space,'a) bounded\<close>
proof-
  assume \<open>P \<cdot>\<^sub>o P = P\<close> and \<open>P = P*\<close>
  have \<open>closed (range (Rep_bounded P))\<close>
  proof-
    have \<open>range (Rep_bounded P) = (\<lambda> x. x - Rep_bounded P x) -` {0}\<close>
    proof
      show "range (Rep_bounded P) \<subseteq> (\<lambda>x. x - Rep_bounded P x) -` {0}"
      proof
        show "x \<in> (\<lambda>x. x - Rep_bounded P x) -` {0}"
          if "x \<in> range (Rep_bounded P)"
          for x :: 'a
        proof-
          have \<open>\<exists> t. Rep_bounded P t = x\<close>
            using that by blast
          then obtain t where \<open>Rep_bounded P t = x\<close>
            by blast 
          hence \<open>x - Rep_bounded P x = x - Rep_bounded P (Rep_bounded P t)\<close>
            by simp
          also have \<open>\<dots> = x - (Rep_bounded P t)\<close>
          proof-
            have \<open>Rep_bounded P \<circ> Rep_bounded P = Rep_bounded P\<close>
              by (metis \<open>P \<cdot>\<^sub>o P = P\<close> timesOp.rep_eq)
            thus ?thesis
              by (metis comp_apply) 
          qed
          also have \<open>\<dots> = 0\<close>
            by (simp add: \<open>Rep_bounded P t = x\<close>)
          finally have \<open>x - Rep_bounded P x = 0\<close>
            by blast
          thus ?thesis
            by simp 
        qed
      qed
      show "(\<lambda>x. x - Rep_bounded P x) -` {0} \<subseteq> range (Rep_bounded P)"
      proof
        show "x \<in> range (Rep_bounded P)"
          if "x \<in> (\<lambda>x. x - Rep_bounded P x) -` {0}"
          for x :: 'a
        proof-
          have \<open>x - Rep_bounded P x = 0\<close>
            using that by blast
          hence \<open>x = Rep_bounded P x\<close>
            by (simp add: \<open>x - Rep_bounded P x = 0\<close> eq_iff_diff_eq_0)
          thus ?thesis
            by blast 
        qed
      qed
    qed
    moreover have \<open>closed ( (\<lambda> x. x - Rep_bounded P x) -` {0} )\<close>
    proof-
      have \<open>closed {(0::'a)}\<close>
        by simp        
      moreover have \<open>continuous (at x) (\<lambda> x. x - Rep_bounded P x)\<close>
        for x
      proof-
        have \<open>Rep_bounded (idOp - P) = (\<lambda> x. x - Rep_bounded P x)\<close>
          by (simp add: idOp.rep_eq minus_bounded.rep_eq)                 
        hence \<open>bounded_clinear (Rep_bounded (idOp - P))\<close>
          using Rep_bounded
          by blast 
        hence \<open>continuous (at x) (Rep_bounded (idOp - P))\<close>
          by (simp add: bounded_linear_continuous)          
        thus ?thesis
          using \<open>Rep_bounded (idOp - P) = (\<lambda> x. x - Rep_bounded P x)\<close>
          by simp
      qed
      ultimately show ?thesis  
        by (rule Abstract_Topology.continuous_closed_vimage)               
    qed
    ultimately show ?thesis
      by simp  
  qed
  have \<open>bounded_clinear (Rep_bounded P)\<close>
    using Rep_bounded by auto
  hence \<open>is_subspace ( range (Rep_bounded P) )\<close>
    using \<open>closed (range (Rep_bounded P))\<close>
     bounded_clinear.clinear is_linear_manifold_image is_subspace.intro 
      is_subspace.subspace is_subspace_UNIV by blast
  hence \<open>\<exists> M. Rep_linear_space M = (range (Rep_bounded P))\<close>
    using  \<open>closed (range (Rep_bounded P))\<close>
    by (metis applyOpSpace.rep_eq closure_eq top_linear_space.rep_eq)    
  then obtain M where \<open>Rep_linear_space M = (range (Rep_bounded P))\<close>
    by blast
  have \<open>Rep_bounded P x \<in> Rep_linear_space M\<close>
    for x
    by (simp add: \<open>Rep_linear_space M = range (Rep_bounded P)\<close>)
  moreover have \<open>x - Rep_bounded P x \<in> orthogonal_complement ( Rep_linear_space M)\<close>
    for x
  proof-
    have \<open>y \<in> Rep_linear_space M \<Longrightarrow> \<langle> x - Rep_bounded P x, y \<rangle> = 0\<close>
      for y
    proof-
      assume \<open>y \<in> Rep_linear_space M\<close>
      hence \<open>\<exists> t. y = Rep_bounded P t\<close>
        by (simp add: \<open>Rep_linear_space M = range (Rep_bounded P)\<close> image_iff)
      then obtain t where \<open>y = Rep_bounded P t\<close>
        by blast
      have \<open>\<langle> x - Rep_bounded P x, y \<rangle> = \<langle> x - Rep_bounded P x, Rep_bounded P t \<rangle>\<close>
        by (simp add: \<open>y = Rep_bounded P t\<close>)
      also have \<open>\<dots> = \<langle> Rep_bounded P (x - Rep_bounded P x), t \<rangle>\<close>
        by (metis \<open>P = P*\<close> adjoint_I)
      also have \<open>\<dots> = \<langle> Rep_bounded P x - Rep_bounded P (Rep_bounded P x), t \<rangle>\<close>
        by (metis \<open>P = P*\<close> adjoint_I cinner_diff_left)
      also have \<open>\<dots> = \<langle> Rep_bounded P x - Rep_bounded P x, t \<rangle>\<close>
      proof-
        have \<open>(Rep_bounded P) \<circ> (Rep_bounded P) = (Rep_bounded P)\<close>
          using  \<open>P \<cdot>\<^sub>o P = P\<close>
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
    have "is_subspace (Rep_linear_space M)"
      by (metis \<open>Rep_linear_space M = range (Rep_bounded P)\<close> \<open>is_subspace (range (Rep_bounded P))\<close>)
    then have f1: "\<forall>a. Rep_bounded (Proj M) a = Rep_bounded P a"
      by (simp add: Proj.rep_eq \<open>\<And>x. Rep_bounded P x \<in> Rep_linear_space M\<close> \<open>\<And>x. x - Rep_bounded P x \<in> orthogonal_complement (Rep_linear_space M)\<close> projection_uniq)
    have "\<forall>a. (+) ((a::'a) - a) = id"
      by force
    then have "\<forall>a. (+) (Rep_bounded (P - Proj M) a) = id"
      using f1
      by (simp add: minus_bounded.rep_eq) 
    then have "\<forall>a aa. aa - aa = Rep_bounded (P - Proj M) a"
      by (metis (no_types) add_diff_cancel_right' id_apply)
    then have "\<forall>a. Rep_bounded (idOp - (P - Proj M)) a = a"
      by (simp add: idOp.rep_eq minus_bounded.rep_eq)      
    then show ?thesis
      by (metis (no_types) Rep_bounded_inject diff_diff_eq2 diff_eq_diff_eq eq_id_iff idOp.rep_eq)
  qed
  thus ?thesis
    using \<open>Rep_linear_space M = range (Rep_bounded P)\<close> by blast 
qed

lemma Proj_endo_I:
\<open>P * P = P \<Longrightarrow> P = P\<^sup>a\<^sup>d\<^sup>j \<Longrightarrow> \<exists> M. P = (\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M)\<close>
  using Proj_I
  unfolding Adj_endo_def times_endo_def
  by (metis Proj_endo_def endo_of_bounded_inv)

lemma Proj_leq: "(Proj S) \<cdot>\<^sub>s A \<le> S"
  by (metis cdot_plus_distrib imageOp_Proj le_iff_add top_greatest xsupxy_linear_space)

lemma Proj_times: "isometry A \<Longrightarrow> A \<cdot>\<^sub>o (Proj S) \<cdot>\<^sub>o (A*) = Proj (A \<cdot>\<^sub>s S)" 
  for A::"('a::chilbert_space,'b::chilbert_space) bounded"
proof-
  assume \<open>isometry A\<close>
  define P where \<open>P = A \<cdot>\<^sub>o (Proj S) \<cdot>\<^sub>o (A*)\<close>
  have \<open>P \<cdot>\<^sub>o P = P\<close>
    using  \<open>isometry A\<close>
    unfolding P_def isometry_def
    by (metis (no_types, lifting) Proj_D2 timesOp_assoc times_idOp2)
  moreover have \<open>P = P*\<close>
    unfolding P_def
    by (metis Proj_D1 adjoint_twice timesOp_assoc times_adjoint)
  ultimately have 
    \<open>\<exists> M. P = Proj M \<and> Rep_linear_space M = range (Rep_bounded (A \<cdot>\<^sub>o (Proj S) \<cdot>\<^sub>o (A*)))\<close>
    using P_def Proj_I by blast
  then obtain M where \<open>P = Proj M\<close>
    and \<open>Rep_linear_space M = range (Rep_bounded (A \<cdot>\<^sub>o (Proj S) \<cdot>\<^sub>o (A*)))\<close>
    by blast
  have \<open>M = A \<cdot>\<^sub>s S\<close>
  proof - (* sledgehammer *)
    have f1: "\<forall>l. A \<cdot>\<^sub>s (Proj S \<cdot>\<^sub>s (A* \<cdot>\<^sub>s l)) = P \<cdot>\<^sub>s l"
      by (simp add: P_def timesOp_assoc_linear_space)
    have f2: "\<forall>l b. b* \<cdot>\<^sub>s (b \<cdot>\<^sub>s (l::'a linear_space)::'b linear_space) = idOp \<cdot>\<^sub>s l \<or> \<not> isometry b"
      by (metis (no_types) isometry_def timesOp_assoc_linear_space)
    have f3: "\<forall>l b. b \<cdot>\<^sub>s (idOp \<cdot>\<^sub>s (l::'a linear_space)) = (b \<cdot>\<^sub>s l::'a linear_space)"
      by auto
    have f4: "\<forall>l. (0::'b linear_space) \<le> l"
      by (metis add.left_neutral le_iff_add)
    have "\<forall>l. (top::'a linear_space) + l = top"
      by (simp add: top_add)
    then show ?thesis
      using f4 f3 f2 f1 by (metis \<open>P = Proj M\<close> \<open>isometry A\<close> add.commute cdot_plus_distrib imageOp_Proj top_add)
  qed  
  thus ?thesis
    using \<open>P = Proj M\<close>
    unfolding P_def
    by blast
qed

abbreviation proj :: "'a::chilbert_space \<Rightarrow> ('a,'a) bounded" where "proj \<psi> \<equiv> Proj (span {\<psi>})"

lift_definition ortho :: \<open>'a::chilbert_space linear_space \<Rightarrow> 'a linear_space\<close>
is \<open>orthogonal_complement\<close>
  by (rule Complex_Inner_Product.is_subspace_orthog)

lemma projection_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" for a::complex and \<psi>::"'a::chilbert_space"
  by simp  

lemma move_plus:
  "(Proj (ortho C)) \<cdot>\<^sub>s A \<le> B \<Longrightarrow> A \<le> B + C"
  for A B C::"'a::chilbert_space linear_space"
proof-
  assume \<open>(Proj (ortho C)) \<cdot>\<^sub>s A \<le> B\<close>
  hence \<open>Abs_bounded
     (projection
       (Rep_linear_space
         (Abs_linear_space (orthogonal_complement (Rep_linear_space C))))) \<cdot>\<^sub>s A \<le> B\<close>
    unfolding Proj_def ortho_def less_eq_linear_space_def
    by auto
  hence proj_ortho_CAB: \<open>Abs_bounded (projection (orthogonal_complement (Rep_linear_space C))) \<cdot>\<^sub>s A \<le> B\<close>
    by (metis Proj_def \<open>Proj (ortho C) \<cdot>\<^sub>s A \<le> B\<close> map_fun_apply ortho.rep_eq)
  hence \<open>x \<in> Rep_linear_space
              (Abs_linear_space
                (closure
                  (Rep_bounded
                    (Abs_bounded
                      (projection (orthogonal_complement (Rep_linear_space C)))) `
                   Rep_linear_space A))) \<Longrightarrow>
         x \<in> Rep_linear_space B\<close>
    for x
    unfolding applyOpSpace_def less_eq_linear_space_def
    by auto
  hence \<open>x \<in>  closure (Rep_bounded (Abs_bounded
                      (projection (orthogonal_complement (Rep_linear_space C)))) `
                   Rep_linear_space A) \<Longrightarrow>
         x \<in> Rep_linear_space B\<close>
  for x
    using proj_ortho_CAB
          applyOpSpace.rep_eq less_eq_linear_space.rep_eq by blast
  hence \<open>x \<in>  closure ( (projection (orthogonal_complement (Rep_linear_space C))) `
                   Rep_linear_space A) \<Longrightarrow>
         x \<in> Rep_linear_space B\<close>
  for x
    by (metis (full_types) Proj.rep_eq Proj_def map_fun_apply ortho.rep_eq)

  hence \<open>x \<in> Rep_linear_space A \<Longrightarrow>
    x \<in> closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> Rep_linear_space B \<and> \<phi> \<in> Rep_linear_space C}\<close>
    for x
  proof-
    assume \<open>x \<in> Rep_linear_space A\<close>
    have \<open>is_subspace (Rep_linear_space C)\<close>
      using Rep_linear_space by auto
    hence \<open>x = (projection (Rep_linear_space C)) x
       + (projection (orthogonal_complement (Rep_linear_space C))) x\<close>
      by (simp add: ortho_decomp)
    hence \<open>x = (projection (orthogonal_complement (Rep_linear_space C))) x
              + (projection (Rep_linear_space C)) x\<close>
      by (metis ordered_field_class.sign_simps(2))
    moreover have \<open>(projection (orthogonal_complement (Rep_linear_space C))) x \<in> Rep_linear_space B\<close>
      using \<open>x \<in>  closure ( (projection (orthogonal_complement (Rep_linear_space C))) `
                   Rep_linear_space A) \<Longrightarrow> x \<in> Rep_linear_space B\<close>
      by (meson \<open>\<And>x. x \<in> closure (projection (orthogonal_complement (Rep_linear_space C)) ` Rep_linear_space A) \<Longrightarrow> x \<in> Rep_linear_space B\<close> \<open>x \<in> Rep_linear_space A\<close> closure_subset image_subset_iff)
    moreover have \<open>(projection (Rep_linear_space C)) x \<in> Rep_linear_space C\<close>
      by (simp add: \<open>is_subspace (Rep_linear_space C)\<close> projection_intro2)
    ultimately show ?thesis
      using closure_subset by fastforce 
  qed
  hence \<open>x \<in> Rep_linear_space A \<Longrightarrow>
        x \<in> (Rep_linear_space B +\<^sub>M Rep_linear_space C)\<close>
    for x
    unfolding closed_sum_def Minkoswki_sum_def
    by blast
  hence \<open> x \<in> Rep_linear_space A \<Longrightarrow>
         x \<in> Rep_linear_space
               (Abs_linear_space (Rep_linear_space B +\<^sub>M Rep_linear_space C))\<close>
    for x
    by (metis Rep_linear_space_inverse plus_linear_space.rep_eq)    
  thus ?thesis 
  unfolding Proj_def ortho_def less_eq_linear_space_def plus_linear_space_def
  by auto
qed


section \<open>Kernel\<close>

lift_definition kernel :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> 'a linear_space" 
  is ker_op
  by (metis ker_op_lin)

definition eigenspace :: "complex \<Rightarrow> ('a::chilbert_space,'a) bounded \<Rightarrow> 'a linear_space" where
  "eigenspace a A = kernel (A - a *\<^sub>C idOp)" 

lemma kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a *\<^sub>C A) = kernel A"
  for a :: complex and A :: "(_,_) bounded"
  unfolding kernel_def ker_op_def
  apply auto
  by (metis complex_vector.scale_eq_0_iff scaleC_bounded.rep_eq)

lemma kernel_0[simp]: "kernel 0 = top"
proof-
  have \<open>ker_op (\<lambda> _. 0) = UNIV\<close>
    by (metis (mono_tags, lifting) Collect_cong UNIV_def ker_op_def)
  hence \<open>ker_op (Rep_bounded (bounded_of_rbounded 0)) = UNIV\<close>
    by (metis bounded_of_rbounded_zero cr_rbounded_def rbounded.pcr_cr_eq rbounded_of_bounded.rep_eq rbounded_of_bounded_zero zero_rbounded.transfer)
  hence \<open>Abs_linear_space (ker_op (Rep_bounded (bounded_of_rbounded 0))) = Abs_linear_space UNIV\<close>
    using Abs_linear_space_inject
    by (simp add: \<open>ker_op (Rep_bounded (bounded_of_rbounded 0)) = UNIV\<close>)
  thus ?thesis
    unfolding kernel_def zero_bounded_def top_linear_space_def
    by (simp add: Abs_bounded_inverse \<open>ker_op (\<lambda>_. 0) = UNIV\<close>)   
qed

lemma kernel_id[simp]: "kernel idOp = 0"
  apply transfer unfolding ker_op_def by simp

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

(* TODO probably needs less than chilbert_space *)
(* TODO: move to Complex_Vector_Spaces *)
instantiation linear_space :: (chilbert_space) complete_lattice begin
instance 
  proof
  show "Inf A \<le> (x::'a linear_space)"
    if "(x::'a linear_space) \<in> A"
    for x :: "'a linear_space"
      and A :: "'a linear_space set"
    using that 
    apply transfer
    by auto

  show "(z::'a linear_space) \<le> Inf A"
    if "\<And>x. (x::'a linear_space) \<in> A \<Longrightarrow> z \<le> x"
    for A :: "'a linear_space set"
      and z :: "'a linear_space"
    using that 
    apply transfer
    by auto

  show "(x::'a linear_space) \<le> Sup A"
    if "(x::'a linear_space) \<in> A"
    for x :: "'a linear_space"
      and A :: "'a linear_space set"
    using that 
    apply transfer
    by (meson Union_upper closure_subset complex_vector.span_superset dual_order.trans)

  show "Sup A \<le> (z::'a linear_space)"
    if "\<And>x. (x::'a linear_space) \<in> A \<Longrightarrow> x \<le> z"
    for A :: "'a linear_space set"
      and z :: "'a linear_space"
    using that 
    apply transfer
    apply auto
    by (metis OrthoClosedEq Sup_le_iff closure_mono is_subspace.subspace is_subspace_I is_subspace_span_A orthogonal_complement_twice subset_iff)

  show "Inf {} = (top::'a linear_space)"
    using \<open>\<And>z A. (\<And>x. x \<in> A \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf A\<close> top.extremum_uniqueI by auto
  show "Sup {} = (bot::'a linear_space)"
    using \<open>\<And>z A. (\<And>x. x \<in> A \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup A \<le> z\<close> bot.extremum_uniqueI by auto    
qed
end

(* TODO: move to Missing or similar *)
(* Following https://en.wikipedia.org/wiki/Complemented_lattice#Definition_and_basic_properties 
   and using the conventions from the definition of @{class boolean_algebra} *)
class complemented_lattice = bounded_lattice + uminus + minus + 
  assumes inf_compl_bot: "inf x (-x) = bot"
    and sup_compl_top: "sup x (-x) = top"
  assumes diff_eq: "x - y = inf x (-y)"

(* TODO: move to Missing or similar *)
class complete_complemented_lattice = complemented_lattice + complete_lattice 

(* TODO: move to Missing or similar *)
(* Following https://en.wikipedia.org/wiki/Complemented_lattice#Orthocomplementation *)
class orthocomplemented_lattice = complemented_lattice +
  assumes ortho_involution: "- (- x) = x"
  assumes ortho_antimono: "x \<le> y \<Longrightarrow> -x \<ge> -y"

(* TODO: move to Missing or similar *)
class complete_orthocomplemented_lattice = orthocomplemented_lattice + complete_lattice

(* TODO: move to Missing or similar *)
instance complete_orthocomplemented_lattice \<subseteq> complete_complemented_lattice
  by intro_classes

(* TODO: move to Missing or similar *)
(* Following https://en.wikipedia.org/wiki/Complemented_lattice#Orthomodular_lattices *)
class orthomodular_lattice = orthocomplemented_lattice +
  assumes orthomodular: "x \<le> y \<Longrightarrow> sup x (inf (-x) y) = y"

(* TODO: move to Missing or similar *)
class complete_orthomodular_lattice = orthomodular_lattice + complete_lattice

(* TODO: move to Missing or similar *)
instance complete_orthomodular_lattice \<subseteq> complete_orthocomplemented_lattice
  by intro_classes

(* TODO: move to Missing or similar *)
instance boolean_algebra \<subseteq> orthomodular_lattice
  apply intro_classes
       apply auto
   apply (simp add: boolean_algebra_class.diff_eq)
  by (simp add: sup.absorb_iff2 sup_inf_distrib1)

(* TODO: move to Missing or similar *)
instance complete_boolean_algebra \<subseteq> complete_orthomodular_lattice
  by intro_classes

(* TODO: move to Complex_Inner_Product *)
instance linear_space :: (chilbert_space) complete_orthomodular_lattice 
  apply intro_classes
  apply (metis bot.extremum_uniqueI inf_sup_ord(1) inf_sup_ord(2) infxminusxbot xinfyz_linear_space) 
  sorry

(* TODO: Remove constant ortho, subsumed by uminus *)

(* TODO: move to Complex_Vector_Spaces *)
lemma ortho_bot[simp]: "ortho bot = top"
  by (metis comm_monoid_add_class.add_0 linear_space_zero_bot ortho_def supxminusxtop uminus_linear_space_def)

lemma ortho_top[simp]: "ortho top = bot"
  by (metis Bounded_Operators.ortho_bot linear_space_ortho_ortho ortho_def uminus_linear_space_def)
(* TODO: move to Complex_Vector_Spaces *)

lemma top_plus[simp]: "top + x = top" for x :: "_ linear_space"
  by (simp add: top.extremum_uniqueI xsupxy_linear_space)
(* TODO: move to Complex_Vector_Spaces *)

lemma plus_top[simp]: "x + top = top" for x :: "_ linear_space"
  by (simp add: add.commute)

lemma ortho_ortho[simp]: "ortho (ortho S) = S"
  by (metis linear_space_ortho_ortho ortho_def uminus_linear_space_def)

definition "isProjector P \<longleftrightarrow> P \<cdot>\<^sub>o P = P \<and> P* = P"

lemma isProjector_D1: \<open>isProjector P \<Longrightarrow> P \<cdot>\<^sub>o P = P\<close>
  unfolding isProjector_def by blast 

lemma isProjector_D2: \<open>isProjector P \<Longrightarrow> P* = P\<close>
  unfolding isProjector_def by blast

lemma isProjector_I: \<open>P \<cdot>\<^sub>o P = P \<Longrightarrow> P* = P \<Longrightarrow> isProjector P\<close>
  unfolding isProjector_def by blast 


lemma isProjector0[simp]: "isProjector 0"
  unfolding isProjector_def
  by (metis Adj_bounded_zero endo_of_bounded_inv mult_zero_left times_endo_def zero_endo_def) 


lemma isProjectoridMinus[simp]: "isProjector P \<Longrightarrow> isProjector (idOp-P)"
  proof (rule isProjector_I)
  show "(idOp - P) \<cdot>\<^sub>o (idOp - P) = idOp - P"
    if "isProjector P"
  proof -
    have f1: "P \<cdot>\<^sub>o P = P \<and> P* = P"
      by (metis isProjector_def that)
    then have "(idOp - P) \<cdot>\<^sub>o (idOp - P) = ((idOp - P) \<cdot>\<^sub>o (idOp - P))*"
      by auto
    then show ?thesis
      using f1 by (simp add: timesOp_minus)
  qed    
  show "(idOp - P)* = idOp - P"
    if "isProjector P"
    using that
    by (simp add: isProjector_def) 
qed

lemma applyOp0[simp]: "Rep_bounded 0 \<psi> = 0"
  apply transfer by simp

lemma apply_idOp[simp]: "Rep_bounded idOp \<psi> = \<psi>"
  apply transfer by simp

(* NEW *)
lemma rel_interior_sing_generalized:
  fixes a :: "'n::chilbert_space"
  shows "rel_interior {a} = {a}"
  apply (auto simp: rel_interior_ball)
  by (metis affine_sing gt_ex le_infI2 subset_hull subset_singleton_iff)


(* NEW *)
(* Generalization of convex_closure_inter *)
lemma convex_closure_inter_generalized:
  assumes "\<forall>S\<in>I. convex (S :: 'n::chilbert_space set)"
    and "\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}"
  shows "closure (\<Inter>I) = \<Inter>{closure S |S. S \<in> I}"
  sorry

lemma is_linear_manifold_rel_interior:
  fixes S::\<open>'a::chilbert_space set\<close>
  assumes \<open>is_linear_manifold S\<close>
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
        using \<open>is_linear_manifold S\<close>
        unfolding is_linear_manifold_def
        by (simp add: \<open>x \<in> S\<close>)
      hence \<open>u *\<^sub>R x \<in> S\<close>
        by (simp add: scaleR_scaleC)
      have \<open>(v::complex) *\<^sub>C y \<in> S\<close>
        using \<open>is_linear_manifold S\<close>
        unfolding is_linear_manifold_def
        by (simp add: \<open>y \<in> S\<close>)
      hence \<open>v *\<^sub>R y \<in> S\<close>
        by (simp add: scaleR_scaleC)
      show \<open> u *\<^sub>R x + v *\<^sub>R y \<in> S\<close> 
        using \<open>is_linear_manifold S\<close>
        unfolding is_linear_manifold_def
        by (simp add:  \<open>u *\<^sub>R x \<in> S\<close>  \<open>v *\<^sub>R y \<in> S\<close>)
    qed
    thus ?thesis 
      unfolding affine_def by blast
  qed
  hence \<open>affine hull S \<subseteq> S\<close>
    unfolding  hull_def by auto
  thus ?thesis 
    apply (auto simp: rel_interior_ball)
     apply (simp add: assms is_linear_manifold.zero)
    apply (rule 1)
    by blast
qed


(*
lemma mult_INF_less_eq_transfer_bij:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space set" 
    and U :: "'b \<Rightarrow>'c::chilbert_space"
  assumes \<open>bounded_clinear U\<close> 
       and \<open>\<forall>i. is_subspace (V i)\<close>  
       and \<open>bij U\<close>
  shows \<open>\<Inter> (range (\<lambda> i. closure (U ` V i))) = closure (U ` \<Inter> (range V))\<close>
proof-
  define I where \<open>I = range (\<lambda> i. U ` (V i))\<close>
  have \<open>S\<in>I \<Longrightarrow> is_linear_manifold S\<close>
    for S
  proof-
    assume \<open>S\<in>I\<close>
    hence \<open>\<exists> i. S = U ` (V i)\<close>
      unfolding I_def by auto
    then obtain i where \<open>S = U ` (V i)\<close>
      by blast
    have \<open>is_subspace (V i)\<close>
      by (simp add: assms(2))
    thus \<open>is_linear_manifold S\<close>
      using  \<open>S = U ` (V i)\<close> \<open>bounded_clinear U\<close>
      by (simp add: bounded_clinear.clinear is_linear_manifold_image is_subspace.subspace)
  qed
  hence \<open>\<forall>S\<in>I. convex S\<close>
    using linear_manifold_Convex by blast
  moreover have \<open>\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}\<close>
  proof-
    have \<open>S \<in> I \<Longrightarrow> 0 \<in> rel_interior S\<close>
      for S
    proof-
      assume \<open>S \<in> I\<close>
      hence \<open>is_linear_manifold S\<close>
        by (simp add: \<open>\<And>S. S \<in> I \<Longrightarrow> is_linear_manifold S\<close>)
      thus ?thesis using is_linear_manifold_rel_interior
        by (simp add: is_linear_manifold_rel_interior) 
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

lemma isCont_applyOp[simp]: "isCont ((\<cdot>\<^sub>v) A) \<psi>"
  sorry

lemma applyOpSpace_mono:
  "S \<le> T \<Longrightarrow> A \<cdot>\<^sub>s S \<le> A \<cdot>\<^sub>s T"
  by (simp add: applyOpSpace.rep_eq closure_mono image_mono less_eq_linear_space.rep_eq)

lemma apply_left_neutral:
  assumes "A \<cdot>\<^sub>o B = B"
  assumes "\<psi> \<in> Rep_linear_space (B \<cdot>\<^sub>s top)"
  shows "A \<cdot>\<^sub>v \<psi> = \<psi>" 
proof -
  define rangeB rangeB' where "rangeB = Rep_linear_space (B \<cdot>\<^sub>s top)" and "rangeB' = range (Rep_bounded B)"
  from assms have "\<psi> \<in> closure rangeB'"
    unfolding rangeB'_def apply (transfer fixing: \<psi>) by simp
  then obtain \<psi>i where \<psi>i_lim: "\<psi>i \<longlonglongrightarrow> \<psi>" and \<psi>i_B: "\<psi>i i \<in> rangeB'" for i
        apply atomize_elim using closure_sequential by blast
  have A_invariant: "A \<cdot>\<^sub>v \<psi>i i = \<psi>i i" for i
  proof -
    from \<psi>i_B obtain \<phi> where \<phi>: "\<psi>i i = B \<cdot>\<^sub>v \<phi>"
      apply atomize_elim unfolding rangeB'_def apply transfer by auto
    then have "A \<cdot>\<^sub>v \<psi>i i = (A \<cdot>\<^sub>o B) \<cdot>\<^sub>v \<phi>"
      by (simp add: timesOp.rep_eq)
    also have "\<dots> = B \<cdot>\<^sub>v \<phi>"
      by (simp add: assms)
    also have "\<dots> = \<psi>i i"
      by (simp add: \<phi>)
    finally show ?thesis
      by -
  qed
  from \<psi>i_lim have "(\<lambda>i. A \<cdot>\<^sub>v (\<psi>i i)) \<longlonglongrightarrow> A \<cdot>\<^sub>v \<psi>"
    by (rule isCont_tendsto_compose[rotated], simp)
  with A_invariant have "(\<lambda>i. \<psi>i i) \<longlonglongrightarrow> A \<cdot>\<^sub>v \<psi>"
    by auto
  with \<psi>i_lim show "A \<cdot>\<^sub>v \<psi> = \<psi>"
    using LIMSEQ_unique by blast
qed

lemma range_adjoint_isometry:
  assumes "isometry U"
  shows "U* \<cdot>\<^sub>s top = top"
proof -
  from assms have "top = U* \<cdot>\<^sub>s U \<cdot>\<^sub>s top"
    by (metis adjUU applyOpSpace_id timesOp_assoc_linear_space)
  also have "\<dots> \<le> U* \<cdot>\<^sub>s top"
    by (simp add: applyOpSpace_mono)
  finally show ?thesis
    using top.extremum_unique by blast
qed


lemma mult_INF_general[simp]: 
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space linear_space" and U :: "('b,'c::chilbert_space) bounded"
    and Uinv :: "('c,'b) bounded" 
  assumes UinvUUinv: "Uinv \<cdot>\<^sub>o U \<cdot>\<^sub>o Uinv = Uinv"
  assumes UUinvU: "U \<cdot>\<^sub>o Uinv \<cdot>\<^sub>o U = U"
  assumes V: "\<And>i. V i \<le> Uinv \<cdot>\<^sub>s top"
  shows "U \<cdot>\<^sub>s (INF i. V i) = (INF i. U \<cdot>\<^sub>s V i)"
proof (rule antisym)
  show "U \<cdot>\<^sub>s (INF i. V i) \<le> (INF i. U \<cdot>\<^sub>s V i)"
    by (rule mult_INF1)
next
  define rangeU rangeUinv where "rangeU = U \<cdot>\<^sub>s top" and "rangeUinv = Uinv \<cdot>\<^sub>s top"
  define INFUV INFV where "INFUV = (INF i. U \<cdot>\<^sub>s V i)" and "INFV = (INF i. V i)"
  have "INFUV = U \<cdot>\<^sub>s Uinv \<cdot>\<^sub>s INFUV"
  proof -
    have "U \<cdot>\<^sub>s V i \<le> rangeU" for i
      unfolding rangeU_def apply transfer apply auto
      by (meson closure_mono image_mono subsetD top_greatest)
    then have "INFUV \<le> rangeU"
      unfolding INFUV_def by (meson INF_lower UNIV_I order_trans)
    moreover have "(U \<cdot>\<^sub>o Uinv) \<cdot>\<^sub>v \<psi> = \<psi>" if "\<psi> \<in> Rep_linear_space rangeU" for \<psi>
      apply (rule apply_left_neutral[where B=U])
      using assms that rangeU_def by auto
    ultimately have "(U \<cdot>\<^sub>o Uinv) \<cdot>\<^sub>v \<psi> = \<psi>" if "\<psi> \<in> Rep_linear_space INFUV" for \<psi>
      by (simp add: in_mono less_eq_linear_space.rep_eq that)
    then have "(U \<cdot>\<^sub>o Uinv) \<cdot>\<^sub>s INFUV = INFUV"
      apply transfer apply auto
       apply (metis OrthoClosedEq is_subspace.subspace is_subspace_I orthogonal_complement_twice)
      using closure_subset by blast
    then show ?thesis
      by (simp add: timesOp_assoc_linear_space)
  qed
  also have "\<dots> \<le> U \<cdot>\<^sub>s (INF i. Uinv \<cdot>\<^sub>s U \<cdot>\<^sub>s V i)"
    unfolding INFUV_def
    apply (rule applyOpSpace_mono)
    by (rule mult_INF1)
  also have "\<dots> = U \<cdot>\<^sub>s INFV"
  proof -
    from assms have "V i \<le> rangeUinv" for i
      unfolding rangeUinv_def by simp
    moreover have "(Uinv \<cdot>\<^sub>o U) \<cdot>\<^sub>v \<psi> = \<psi>" if "\<psi> \<in> Rep_linear_space rangeUinv" for \<psi>
      apply (rule apply_left_neutral[where B=Uinv])
      using assms that rangeUinv_def by auto
    ultimately have "(Uinv \<cdot>\<^sub>o U) \<cdot>\<^sub>v \<psi> = \<psi>" if "\<psi> \<in> Rep_linear_space (V i)" for \<psi> i
      using less_eq_linear_space.rep_eq that by blast
    then have "(Uinv \<cdot>\<^sub>o U) \<cdot>\<^sub>s (V i) = (V i)" for i
      apply transfer apply auto
       apply (metis OrthoClosedEq is_subspace.subspace is_subspace_I orthogonal_complement_twice)
      using closure_subset by blast
    then show ?thesis
      unfolding INFV_def
      by (simp add: timesOp_assoc_linear_space)
  qed
  finally show "INFUV \<le> U \<cdot>\<^sub>s INFV"
    by -
qed

lemma mult_INF[simp]: 
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space linear_space" and U :: "('b,'c::chilbert_space) bounded"
  assumes \<open>isometry U\<close>
  shows "U \<cdot>\<^sub>s (INF i. V i) = (INF i. U \<cdot>\<^sub>s V i)"
proof -
  from \<open>isometry U\<close> have "U* \<cdot>\<^sub>o U \<cdot>\<^sub>o U* = U*"
    unfolding isometry_def by simp
  moreover from \<open>isometry U\<close> have "U \<cdot>\<^sub>o U* \<cdot>\<^sub>o U = U"
    unfolding isometry_def
    by (simp add: timesOp_assoc)
  moreover have "V i \<le> U* \<cdot>\<^sub>s top" for i
    by (simp add: range_adjoint_isometry assms)
  ultimately show ?thesis
    by (rule mult_INF_general)
qed
(* proof-
  have \<open>U \<cdot>\<^sub>s (INF x. V x) \<le> (INF x. U \<cdot>\<^sub>s V x)\<close>
    by simp
  moreover have \<open>(INF x. U \<cdot>\<^sub>s V x) \<le> U \<cdot>\<^sub>s (INF x. V x)\<close> 
    using assms
    apply transfer
    apply auto
    by (metis INT_I mult_INF_less_eq_transfer_bij)   
  ultimately show ?thesis
    using dual_order.antisym by blast 
qed *)

lemma leq_INF[simp]:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space linear_space"
  shows "(A \<le> (INF x. V x)) = (\<forall>x. A \<le> V x)"
    by (simp add: le_Inf_iff)

lemma times_applyOp: "(A \<cdot>\<^sub>o B) \<cdot>\<^sub>v \<psi> = A \<cdot>\<^sub>v (B \<cdot>\<^sub>v \<psi>)"
  apply transfer by simp

(* TODO: this one should probably be called mult_inf_distrib, and the above one renamed *)
lemma mult_inf_distrib'[simp]:
  fixes U::\<open>('a::chilbert_space,'b::chilbert_space) bounded\<close> and B C::"'a linear_space"
  assumes "isometry U"
  shows "U \<cdot>\<^sub>s (inf B C) = inf (U \<cdot>\<^sub>s B) (U \<cdot>\<^sub>s C)"
  using mult_INF[where V="\<lambda>b. if b then B else C" and U=U]
  unfolding INF_UNIV_bool_expand
  using assms by auto

lemma applyOp_scaleC1[simp]: "(c *\<^sub>C A) \<cdot>\<^sub>v \<psi> = c *\<^sub>C (A \<cdot>\<^sub>v \<psi>)"
  apply transfer by simp

lemma applyOp_scaleC2[simp]: "A \<cdot>\<^sub>v (c *\<^sub>C \<psi>) = c *\<^sub>C (A \<cdot>\<^sub>v \<psi>)"
  apply transfer 
  by (simp add: clinear.scaleC bounded_clinear.clinear)


section \<open>On-demand syntax\<close>

bundle bounded_notation begin
notation timesOp (infixl "\<cdot>\<^sub>o" 69)
notation Rep_bounded (infixr "\<cdot>\<^sub>v" 70)
notation applyOpSpace (infixr "\<cdot>\<^sub>s" 70)
notation adjoint ("_*" [99] 100)
end

bundle no_bounded_notation begin
no_notation timesOp (infixl "\<cdot>\<^sub>o" 69)
no_notation Rep_bounded (infixr "\<cdot>\<^sub>v" 70)
no_notation applyOpSpace (infixr "\<cdot>\<^sub>s" 70)
no_notation adjoint ("_*" [99] 100)
end

unbundle no_rbounded_notation

unbundle no_bounded_notation


end

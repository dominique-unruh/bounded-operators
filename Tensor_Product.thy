(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Tensor_Product
  imports
    Bounded_Operators
    Complex_L2 
    "HOL-Library.Adhoc_Overloading" 
    Completion
    Algebraic_Tensor_Product

begin
unbundle bounded_notation

section \<open>Hilbert tensor product\<close>

text\<open>Hilbert tensor product as defined in @{cite Helemskii} chapter 2, section 8\<close>
typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) htensor
  = \<open>(UNIV::(('a \<otimes>\<^sub>a 'b) completion) set)\<close>
  by auto

setup_lifting type_definition_htensor

(* "h" is for Hilbert *)
type_notation 
  htensor  ("(_ \<otimes>\<^sub>h/ _)" [21, 20] 20)

instantiation htensor :: (chilbert_space, chilbert_space) complex_inner
begin
lift_definition cinner_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> complex\<close>
  is "\<lambda> x y. \<langle> x, y \<rangle>".

lift_definition scaleC_htensor :: \<open>complex \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is "\<lambda> c x. c *\<^sub>C x".

lift_definition uminus_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is "\<lambda> x. -x".

lift_definition zero_htensor :: \<open>'a \<otimes>\<^sub>h 'b\<close>
  is "0".

lift_definition minus_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is \<open>\<lambda> x y. x - y\<close>.

lift_definition plus_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is \<open>\<lambda> x y. x + y\<close>.

lift_definition sgn_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is \<open>\<lambda> x.  x /\<^sub>R (norm x)\<close>.

lift_definition norm_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> real\<close>
  is \<open>\<lambda> x. norm x\<close>.

lift_definition scaleR_htensor :: \<open>real \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>
  is "\<lambda> c x. c *\<^sub>R x".

lift_definition dist_htensor :: \<open>'a \<otimes>\<^sub>h 'b \<Rightarrow> 'a \<otimes>\<^sub>h 'b \<Rightarrow> real\<close>
  is \<open>\<lambda> x y. dist x y\<close>.

definition uniformity_htensor :: \<open>(('a \<otimes>\<^sub>h 'b) \<times> 'a \<otimes>\<^sub>h 'b) filter\<close> where
  "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a \<otimes>\<^sub>h 'b) y < e})"

definition open_htensor :: \<open>('a \<otimes>\<^sub>h 'b) set \<Rightarrow> bool\<close> where
  "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a \<otimes>\<^sub>h 'b) = x \<longrightarrow> y \<in> U)"
instance
proof
(* TODO: more readable to fix variable names via "fix" once and for all throught the proof, imho *)
(* TODO: clean up superfluous type information *)
  show "((*\<^sub>R) r::'a \<otimes>\<^sub>h 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
    apply transfer
    by (simp add: scaleR_scaleC)

  show "(a::'a \<otimes>\<^sub>h 'b) + b + c = a + (b + c)"
    for a :: "'a \<otimes>\<^sub>h 'b"
      and b :: "'a \<otimes>\<^sub>h 'b"
      and c :: "'a \<otimes>\<^sub>h 'b"
    by (metis (mono_tags, lifting) Rep_htensor_inject ab_semigroup_add_class.add_ac(1) plus_htensor.rep_eq)

  show "(a::'a \<otimes>\<^sub>h 'b) + b = b + a"
    for a :: "'a \<otimes>\<^sub>h 'b"
      and b :: "'a \<otimes>\<^sub>h 'b"
    by (metis (mono_tags, lifting) Rep_htensor_inject Tensor_Product.plus_htensor.rep_eq ordered_field_class.sign_simps(2))

  show "(0::'a \<otimes>\<^sub>h 'b) + a = a"
    for a :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject plus_htensor.rep_eq zero_htensor.rep_eq by fastforce

  show "- (a::'a \<otimes>\<^sub>h 'b) + a = 0"
    for a :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject plus_htensor.rep_eq uminus_htensor.rep_eq zero_htensor.rep_eq by fastforce

  show "(a::'a \<otimes>\<^sub>h 'b) - b = a + - b"
    for a :: "'a \<otimes>\<^sub>h 'b"
      and b :: "'a \<otimes>\<^sub>h 'b"
    by (metis (mono_tags, lifting) Rep_htensor_inverse Tensor_Product.minus_htensor.rep_eq Tensor_Product.plus_htensor.rep_eq Tensor_Product.uminus_htensor.rep_eq pth_2)

  show "a *\<^sub>C ((x::'a \<otimes>\<^sub>h 'b) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
    by (metis (mono_tags, lifting) Rep_htensor_inject plus_htensor.rep_eq scaleC_add_right scaleC_htensor.rep_eq)

  show "(a + b) *\<^sub>C (x::'a \<otimes>\<^sub>h 'b) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<otimes>\<^sub>h 'b"
    by (metis (mono_tags, lifting) Rep_htensor_inverse Tensor_Product.plus_htensor.abs_eq Tensor_Product.scaleC_htensor.rep_eq scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::'a \<otimes>\<^sub>h 'b) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject scaleC_htensor.rep_eq by fastforce

  show "1 *\<^sub>C (x::'a \<otimes>\<^sub>h 'b) = x"
    for x :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject scaleC_htensor.rep_eq by fastforce

  show "dist (x::'a \<otimes>\<^sub>h 'b) y = norm (x - y)"
    for x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: dist_htensor.rep_eq dist_norm minus_htensor.rep_eq norm_htensor.rep_eq)

  show "sgn (x::'a \<otimes>\<^sub>h 'b) = inverse (norm x) *\<^sub>R x"
    for x :: "'a \<otimes>\<^sub>h 'b"
    using Rep_htensor_inject norm_htensor.rep_eq scaleR_htensor.rep_eq sgn_htensor.rep_eq 
    by fastforce

  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a \<otimes>\<^sub>h 'b) y < e})"
    by (simp add: Tensor_Product.uniformity_htensor_def)

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a \<otimes>\<^sub>h 'b) = x \<longrightarrow> y \<in> U)"
    for U :: "('a \<otimes>\<^sub>h 'b) set"
    by (simp add: Tensor_Product.open_htensor_def)

  show "\<langle>x::'a \<otimes>\<^sub>h 'b, y\<rangle> = cnj \<langle>y, x\<rangle>"
    for x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: cinner_htensor.rep_eq)

  show "\<langle>(x::'a \<otimes>\<^sub>h 'b) + y, z\<rangle> = \<langle>x, z\<rangle> + \<langle>y, z\<rangle>"
    for x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
      and z :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: Tensor_Product.cinner_htensor.rep_eq Tensor_Product.plus_htensor.rep_eq cinner_left_distrib)

  show "\<langle>r *\<^sub>C (x::'a \<otimes>\<^sub>h 'b), y\<rangle> = cnj r * \<langle>x, y\<rangle>"
    for r :: complex
      and x :: "'a \<otimes>\<^sub>h 'b"
      and y :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: Tensor_Product.cinner_htensor.rep_eq Tensor_Product.scaleC_htensor.rep_eq)

  show "0 \<le> \<langle>x::'a \<otimes>\<^sub>h 'b, x\<rangle>"
    for x :: "'a \<otimes>\<^sub>h 'b"
    by (simp add: cinner_htensor.rep_eq)

  show "(\<langle>x::'a \<otimes>\<^sub>h 'b, x\<rangle> = 0) = (x = 0)"
    for x :: "'a \<otimes>\<^sub>h 'b"
  proof
    show "x = 0"
      if "\<langle>x, x\<rangle> = 0"
      using that
      using Rep_htensor_inject cinner_htensor.rep_eq zero_htensor.rep_eq by fastforce 
    show "\<langle>x, x\<rangle> = 0"
      if "x = 0"
      using that
      by (simp add: cinner_htensor.abs_eq zero_htensor_def) 
  qed
  show "norm (x::'a \<otimes>\<^sub>h 'b) = sqrt (cmod \<langle>x, x\<rangle>)"
    for x :: "'a \<otimes>\<^sub>h 'b"
    using cinner_htensor.rep_eq norm_eq_sqrt_cinner norm_htensor.rep_eq by auto

qed
end

instantiation htensor :: (chilbert_space, chilbert_space) chilbert_space
begin 
instance
proof
  show "convergent X"
    if "Cauchy X"
    for X :: "nat \<Rightarrow> 'a \<otimes>\<^sub>h 'b"
  proof-
    from \<open>Cauchy X\<close>
    have \<open>Cauchy (\<lambda> n. Rep_htensor (X n))\<close>
      unfolding Cauchy_def dist_htensor_def
      by auto
    hence \<open>convergent (\<lambda> n. Rep_htensor (X n))\<close>
      using Cauchy_convergent by auto
    hence \<open>\<exists> l. \<forall> e>0. \<exists> N. \<forall> n\<ge>N. dist (Rep_htensor (X n)) l < e\<close>
      unfolding convergent_def
      using metric_LIMSEQ_D by blast
    then obtain l where \<open>\<forall> e>0. \<exists> N. \<forall> n\<ge>N. dist (Rep_htensor (X n)) l < e\<close>
      by blast
    have \<open>\<exists> L. Rep_htensor L = l\<close>
      by (metis Rep_htensor_inverse dist_eq_0_iff dist_htensor.abs_eq)
    then obtain L where \<open>Rep_htensor L = l\<close> by blast
    have \<open>\<forall> e>0. \<exists> N. \<forall> n\<ge>N. dist (Rep_htensor (X n)) (Rep_htensor L) < e\<close>
      by (simp add: \<open>Rep_htensor L = l\<close> \<open>\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (Rep_htensor (X n)) l < e\<close>)
    hence \<open>\<forall> e>0. \<exists> N. \<forall> n\<ge>N. dist (X n) L < e\<close>
      by (simp add: dist_htensor.rep_eq)
    hence \<open>X \<longlonglongrightarrow> L\<close>
      by (simp add: metric_LIMSEQ_I)
    thus ?thesis unfolding convergent_def by blast
  qed
qed
end

lift_definition htensor_op:: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space \<Rightarrow> 'a \<otimes>\<^sub>h 'b\<close>  (infixl "\<otimes>\<^sub>h" 70)
  is \<open>\<lambda> x::'a. \<lambda> y::'b. inclusion_completion (x \<otimes>\<^sub>a y)\<close>.

lemma hilbert_tensor_existence_left:
  fixes S :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close>
  assumes \<open>bounded_clinear S\<close> 
  shows \<open>\<exists> H :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h ('c::chilbert_space). 
  bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy) \<and> onorm H \<le> onorm S\<close>
  sorry

lemma hilbert_tensor_existence_right:
  fixes T :: \<open>'c::chilbert_space \<Rightarrow> 'd::chilbert_space\<close>
  assumes \<open>bounded_clinear T\<close> 
  shows \<open>\<exists> H :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> ('a::chilbert_space) \<otimes>\<^sub>h 'd. 
  bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)) \<and> onorm H \<le> onorm T\<close>
  sorry


text \<open>Theorem 1, page 189 in @{cite Helemskii}\<close>

(* TODO: Restructure proofs

 - remove hilbert_tensor_existence_uniqueness
 - remove htensorOp_existence 
 - show htensorOp_existence inside proof of htensorOp_separation
   (we don't need htensorOp_existence then because htensorOp_separation implies existence)
 - show the uniqueness without existence as
   (H satisfies the property) \<Longrightarrow> H=htensorOp

 (Alternatively, if the existence proof is constructive, define htensorOp constructively (without SOME))

*)

lemma hilbert_tensor_existence':
  fixes S :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close> and 
        T :: \<open>'c::chilbert_space \<Rightarrow> 'd::chilbert_space\<close>
  assumes \<open>bounded_clinear S\<close> and  \<open>bounded_clinear T\<close>
  shows \<open>\<exists> H :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd. 
  bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>h(T y)) \<and> onorm H \<le> onorm S * onorm T\<close>
proof-
  have \<open>\<exists> HS :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h ('c::chilbert_space). 
  bounded_clinear HS \<and> (\<forall> x y. HS (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy) \<and> onorm HS \<le> onorm S\<close>
    by (simp add: hilbert_tensor_existence_left assms(1))
  then obtain HS::\<open>'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'c\<close> where \<open>bounded_clinear HS\<close> and 
  \<open>\<forall> x y. HS (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy\<close> and \<open>onorm HS \<le> onorm S\<close> by blast
  have \<open>\<exists> HT :: 'b \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd. 
  bounded_clinear HT \<and> (\<forall> x y. HT (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)) \<and> onorm HT \<le> onorm T\<close>
    by (simp add: hilbert_tensor_existence_right assms(2))
  then obtain HT::\<open>'b \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd\<close> where \<open>bounded_clinear HT\<close> and 
  \<open>\<forall> x y. HT (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)\<close> and \<open>onorm HT \<le> onorm T\<close> by blast
  define H where \<open>H = HT \<circ> HS\<close>
  have \<open>bounded_clinear H\<close>
    unfolding H_def
    using \<open>bounded_clinear HT\<close> \<open>bounded_clinear HS\<close>
      Complex_Vector_Spaces.comp_bounded_clinear[where A = "HT" and B = "HS"]
    by blast
  moreover have \<open>\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>h(T y)\<close>
    using \<open>\<forall> x y. HS (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy\<close> \<open>\<forall> x y. HT (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)\<close> H_def 
    by auto
  moreover have \<open>onorm H \<le> onorm S * onorm T\<close>
    using \<open>onorm HS \<le> onorm S\<close> \<open>onorm HT \<le> onorm T\<close>
    by (smt H_def \<open>bounded_clinear HS\<close> \<open>bounded_clinear HT\<close> bounded_clinear.bounded_linear mult_mono' onorm_compose onorm_pos_le ordered_field_class.sign_simps(5))
  ultimately show ?thesis by blast
qed


lemma hilbert_tensor_existence:
  fixes S :: \<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and 
    T :: \<open>('c::chilbert_space, 'd::chilbert_space) bounded\<close>
  shows \<open>\<exists> H :: ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded.  (\<forall> x y. H *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> 
          norm H \<le> norm S * norm T\<close>
proof-
  have \<open>bounded_clinear (times_bounded_vec S)\<close>
    using times_bounded_vec by blast
  moreover have \<open>bounded_clinear (times_bounded_vec T)\<close>
    using times_bounded_vec by blast
  ultimately have \<open>\<exists> h :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd. 
  bounded_clinear h \<and> (\<forall> x y. h (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and>
      onorm h \<le> onorm (times_bounded_vec S) * onorm (times_bounded_vec T)\<close>
    using hilbert_tensor_existence' by blast
  then obtain h :: \<open>'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd\<close> where
    \<open>bounded_clinear h\<close> and \<open>\<forall> x y. h (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)\<close>
     and \<open>onorm h \<le> onorm (times_bounded_vec S) * onorm (times_bounded_vec T)\<close>
    by blast
  from \<open>bounded_clinear h\<close>
  have \<open>\<exists> H. times_bounded_vec H = h\<close>
    using times_bounded_vec_cases by auto
  then obtain H where \<open>times_bounded_vec H = h\<close>
    by blast
  have \<open>\<forall>x y. H *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y)\<close>
    using \<open>times_bounded_vec H = h\<close> \<open>\<forall> x y. h (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)\<close>
    by auto
  moreover have \<open>norm H \<le> norm S * norm T\<close>
    using \<open>times_bounded_vec H = h\<close> \<open>onorm h \<le> onorm (times_bounded_vec S) * onorm (times_bounded_vec T)\<close>
    by (simp add: norm_bounded.rep_eq)
  ultimately show ?thesis by blast
qed

lemma htensorOp_existence:
  \<open>\<exists> H :: ('a::chilbert_space, 'b::chilbert_space) bounded \<Rightarrow>
  ('c::chilbert_space, 'd::chilbert_space) bounded \<Rightarrow>
  ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded. \<forall> S T.
   (\<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> norm (H S T) \<le> norm S * norm T\<close>
  using hilbert_tensor_existence by metis

definition htensorOp :: \<open>('a::chilbert_space, 'b::chilbert_space) bounded
 \<Rightarrow> ('c::chilbert_space, 'd::chilbert_space ) bounded
 \<Rightarrow> (('a \<otimes>\<^sub>h 'c),  ('b \<otimes>\<^sub>h 'd)) bounded\<close> (infixl "\<otimes>\<^sub>H" 70)
  where \<open>htensorOp = (SOME H :: ('a, 'b) bounded \<Rightarrow> ('c, 'd) bounded \<Rightarrow> 
    ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded. (
    \<forall> S T. \<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y) \<and> 
    norm (H S T) \<le> norm S * norm T
))\<close> 

lemma htensorOp_I1:
  fixes S::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and
        T::\<open>('c::chilbert_space, 'd::chilbert_space) bounded\<close>
  shows \<open>(S \<otimes>\<^sub>H T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y)\<close>
proof-
  define P::\<open>(('a, 'b) bounded \<Rightarrow> ('c, 'd) bounded \<Rightarrow> ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded) \<Rightarrow> bool\<close> where 
 \<open>P H = (\<forall> S T. (\<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> 
        norm (H S T) \<le> norm S * norm T)\<close> for H
  have  \<open>\<exists> H. P H\<close>
    unfolding P_def
    by (simp add: htensorOp_existence)
  hence  \<open>P (\<lambda> S T. S \<otimes>\<^sub>H T)\<close>
    by (smt someI_ex htensorOp_def P_def) 
      (* > 1 s *)
  thus ?thesis
    by (simp add: P_def) 
qed
  
lemma htensorOp_I2:
  fixes S::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and
        T::\<open>('c::chilbert_space, 'd::chilbert_space) bounded\<close>
  shows \<open>norm (S \<otimes>\<^sub>H T) \<le> norm S * norm T\<close>
proof-
  define P::\<open>(('a, 'b) bounded \<Rightarrow> ('c, 'd) bounded \<Rightarrow> ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded) \<Rightarrow> bool\<close> where 
 \<open>P H = (\<forall> S T. (\<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> 
        norm (H S T) \<le> norm S * norm T)\<close> for H
  have  \<open>\<exists> H. P H\<close>
    unfolding P_def
    by (simp add: htensorOp_existence)
  hence  \<open>P (\<lambda> S T. S \<otimes>\<^sub>H T)\<close>
    by (smt someI_ex htensorOp_def P_def) 
      (* > 1 s *)
  thus ?thesis
    by (simp add: P_def) 
qed



(* TODO:
- Develop htensorVec (not sure about the name) htensorOp as you proposed. (In Tensor_Product.thy.)
- Derive all relevant laws with respect to htensorOp. (In Tensor_Product.thy.)
- Define and prove the isomorphism i ('a ell2 \otimes 'b ell2) -> ('a*'b) ell2). (In Tensor_Product_L2.thy.)
- Define tensorVec as "tensorVec a b = i (htensorVec a b)" and "tensorOp A B psi = i (htensorOp a b (inv i))". (In Tensor_Product_L2.thy.)
- Define some suitable transfer rules (we can discuss that in more details when you reach that point).
- Derive properties of tensorVec and tensorOp directly from those in Tensor_Product.thy using the transfer method.

*)

section \<open>Tensor product ell2\<close>

unbundle bounded_notation

consts "tensorOp" :: "('a ell2,'b ell2) bounded \<Rightarrow> ('c ell2,'d ell2) bounded \<Rightarrow> (('a*'c) ell2,('b*'d) ell2) bounded"

type_synonym ('a, 'b) l2bounded = "('a ell2,'b ell2) bounded"

lift_definition "tensorVec" :: "'a ell2 \<Rightarrow> 'c ell2 \<Rightarrow> ('a*'c) ell2" is
  "\<lambda>\<psi> \<phi> (x,y). \<psi> x * \<phi> y"
  by (cheat tensorVec)

definition tensorSpace :: "'a ell2 linear_space \<Rightarrow> 'b ell2 linear_space \<Rightarrow> ('a*'b) ell2 linear_space" where
  "tensorSpace A B = Span {tensorVec \<psi> \<phi>| \<psi> \<phi>. \<psi> \<in> space_as_set A \<and> \<phi> \<in> space_as_set B}"

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<otimes>" 71)
adhoc_overloading tensor tensorOp tensorSpace tensorVec

lemma idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"
  by (cheat TODO2)

definition "comm_op" :: "(('a*'b) ell2, ('b*'a) ell2) bounded" where
  "comm_op = classical_operator (\<lambda>(a,b). Some (b,a))"

lemma adj_comm_op[simp]: "adjoint comm_op = comm_op"
  by (cheat TODO2)

lemma
  comm_op_swap[simp]: "comm_op *\<^sub>o (A\<otimes>B) *\<^sub>o comm_op = B\<otimes>A"
  for A::"('a ell2,'b ell2) bounded" and B::"('c ell2,'d ell2) bounded"
  by (cheat TODO3)

lemma comm_op_times_comm_op[simp]: "comm_op  *\<^sub>o comm_op = idOp"
proof -
  have "comm_op  *\<^sub>o (idOp \<otimes> idOp)  *\<^sub>o comm_op = idOp \<otimes> idOp" by (simp del: idOp_tensor_idOp)
  then show ?thesis by simp
qed

lemma unitary_comm_op[simp]: "unitary comm_op"
  unfolding unitary_def by (cheat TODO)

definition "assoc_op" :: "(('a*('b*'c)) ell2, (('a*'b)*'c) ell2) bounded" where
  "assoc_op = classical_operator (\<lambda>(a,(b,c)). Some ((a,b),c))"

lemma unitary_assoc_op[simp]: "unitary assoc_op"
  by (cheat TODO5)

lemma tensor_scalar_mult1[simp]: "(a *\<^sub>C A) \<otimes> B = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)
lemma tensor_scalar_mult1_ell2[simp]: "(a *\<^sub>C A) \<otimes> B = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"_ ell2" and B::"_ ell2"
  by (cheat TODO3)
lemma tensor_scalar_mult2[simp]: "A \<otimes> (a *\<^sub>C B) = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)
lemma tensor_scalar_mult2_ell2[simp]: "A \<otimes> (a *\<^sub>C B) = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"_ ell2" and B::"_ ell2"
  by (cheat TODO3)
lemma tensor_plus: "(A+B) \<otimes> C = A \<otimes> C + B \<otimes> C" for A B C :: "(_,_)bounded"
  by (cheat tensor_plus)
lemma tensor_plus_ell2: "(A+B) \<otimes> C = A \<otimes> C + B \<otimes> C" for A B C :: "_ ell2"
  by (cheat tensor_plus)
lemma tensor_norm_ell2: "norm (\<psi> \<otimes> \<phi>) = norm \<psi> * norm \<phi>" for \<psi> \<phi> :: "_ ell2"
  by (cheat tensor_norm_ell2)

lemma tensor_times[simp]: "(U1 \<otimes> U2) *\<^sub>o (V1 \<otimes> V2) = (U1 *\<^sub>o V1) \<otimes> (U2 *\<^sub>o V2)"
  for V1 :: "('a1,'b1) l2bounded" and U1 :: "('b1,'c1) l2bounded"
    and V2 :: "('a2,'b2) l2bounded" and U2 :: "('b2,'c2) l2bounded"
  by (cheat TODO3)

lift_definition addState :: "'a ell2 \<Rightarrow> ('b ell2,('b*'a) ell2) bounded" is
  \<open>\<lambda>\<psi> \<phi>. tensorVec \<phi> \<psi>\<close>
  apply (rule_tac K="norm ell2" in bounded_clinear_intro)
  by (auto simp: tensor_norm_ell2 tensor_plus_ell2)


(* TODO: this is simply the adjoint of addState (1::unit ell2), and addState y is best defined as x \<rightarrow> x \<otimes> y (lifted).
   Do we even use remove_qvar_unit_op then? *)
consts remove_qvar_unit_op :: "(('a*unit) ell2,'a ell2) bounded"


(* definition addState :: "'a ell2 \<Rightarrow> ('b,'b*'a) l2bounded" where
  "addState \<psi> = idOp \<otimes> (ell2_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*" *)

lemma addState_times_scalar[simp]: "addState (a *\<^sub>C \<psi>) = a *\<^sub>C addState \<psi>"
  for a::complex and \<psi>::"'a ell2"
  by (cheat TODO)

lemma tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)"
  for U :: "('a,'b) l2bounded" and V :: "('c,'d) l2bounded"
  by (cheat TODO3)

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

lemma tensor_isometry[simp]: 
  assumes "isometry U" and "isometry V"
  shows "isometry (U\<otimes>V)"
  using assms unfolding isometry_def by simp

unbundle no_bounded_notation

end

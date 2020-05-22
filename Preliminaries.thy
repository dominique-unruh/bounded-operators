section\<open>Preliminaries\<close>

theory Preliminaries
  imports
    Complex_Main            
    "HOL-Analysis.Infinite_Set_Sum"
    "HOL-ex.Sketch_and_Explore" 
    HOL.Groups
    "HOL-Nonstandard_Analysis.Nonstandard_Analysis"    
    "HOL-Library.Rewrite" 
    Containers.Containers_Auxiliary
    "HOL.Complex" 
    "Jordan_Normal_Form.Conjugate" 
    HOL.Complete_Lattices
    Complex_Main
    Banach_Steinhaus.Banach_Steinhaus
    "HOL-Analysis.Operator_Norm"
    "HOL-ex.Sketch_and_Explore"
    "HOL.Real_Vector_Spaces"
    "HOL-Analysis.Uniform_Limit"
    

begin

subsection\<open>\<open>Unobtrusive_NSA\<close> -- Cleaning up syntax from \<open>Nonstandard_Analysis\<close>\<close>

text \<open>
Load this theory instead of \<^theory>\<open>HOL-Nonstandard_Analysis.Nonstandard_Analysis\<close>. 
This will not include the syntax from \<^theory>\<open>HOL-Nonstandard_Analysis.Nonstandard_Analysis\<close>
(which is somewhat intrusive because it overwrites, e.g., the letters \<open>\<epsilon>\<close> and \<open>\<omega>\<close>).

Reactivate the notation locally via "@{theory_text \<open>includes nsa_notation\<close>}" in a lemma statement.
(Or sandwich a declaration using that notation between "@{theory_text \<open>unbundle nsa_notation ... unbundle no_nsa_notation\<close>}.)
\<close>

bundle no_nsa_notation begin
no_notation HyperDef.epsilon ("\<epsilon>")
no_notation HyperDef.omega ("\<omega>")
no_notation NSA.approx (infixl "\<approx>" 50)
no_notation HyperDef.pow (infixr "pow" 80)
no_notation HLim.NSLIM ("((_)/ \<midarrow>(_)/\<rightarrow>\<^sub>N\<^sub>S (_))" [60, 0, 60] 60)
no_notation HLog.powhr (infixr "powhr" 80)
no_notation HSEQ.NSLIMSEQ ("((_)/ \<longlonglongrightarrow>\<^sub>N\<^sub>S (_))" [60, 60] 60)
no_notation HSeries.NSsums (infixr "NSsums" 80)
no_notation Star.starfun_n ("*fn* _" [80] 80)
no_notation StarDef.FreeUltrafilterNat (\<open>\<U>\<close>)
no_notation StarDef.Ifun (\<open>(_ \<star>/ _)\<close> [300, 301] 300)
no_notation StarDef.starfun (\<open>*f* _\<close> [80] 80)
no_notation StarDef.starfun2 (\<open>*f2* _\<close> [80] 80)
no_notation StarDef.starP (\<open>*p* _\<close> [80] 80)
no_notation StarDef.starP2 (\<open>*p2* _\<close> [80] 80)
no_notation StarDef.starset (\<open>*s* _\<close> [80] 80)
end

bundle nsa_notation begin
notation HyperDef.epsilon ("\<epsilon>")
notation HyperDef.omega ("\<omega>")
notation NSA.approx (infixl "\<approx>" 50)
notation HyperDef.pow (infixr "pow" 80)
notation HLim.NSLIM ("((_)/ \<midarrow>(_)/\<rightarrow>\<^sub>N\<^sub>S (_))" [60, 0, 60] 60)
notation HLog.powhr (infixr "powhr" 80)
notation HSEQ.NSLIMSEQ ("((_)/ \<longlonglongrightarrow>\<^sub>N\<^sub>S (_))" [60, 60] 60)
notation HSeries.NSsums (infixr "NSsums" 80)
notation Star.starfun_n ("*fn* _" [80] 80)
notation StarDef.FreeUltrafilterNat (\<open>\<U>\<close>)
notation StarDef.Ifun (\<open>(_ \<star>/ _)\<close> [300, 301] 300)
notation StarDef.starfun (\<open>*f* _\<close> [80] 80)
notation StarDef.starfun2 (\<open>*f2* _\<close> [80] 80)
notation StarDef.starP (\<open>*p* _\<close> [80] 80)
notation StarDef.starP2 (\<open>*p2* _\<close> [80] 80)
notation StarDef.starset (\<open>*s* _\<close> [80] 80)
end

unbundle no_nsa_notation

text \<open>The following restores the method transfer under the name transfer.
      Use @{method StarDef.transfer} for the transfer method for nonstandard analysis.\<close>

method_setup transfer = \<open>
  let val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
        error ("Bad free variable: " ^ Syntax.string_of_term ctxt t))
      val fixing = Scan.optional (Scan.lift (Args.$$$ "fixing" -- Args.colon)
        |-- Scan.repeat free) []
      fun transfer_method equiv : (Proof.context -> Proof.method) context_parser =
        fixing >> (fn vs => fn ctxt =>
          SIMPLE_METHOD' (Transfer.gen_frees_tac vs ctxt THEN' Transfer.transfer_tac equiv ctxt))
  in
    transfer_method true
  end\<close>


subsection\<open>General Results Missing\<close>
(* TODO: Never used in Bounded Operators. Move to tensor product. *)
(* Jose: I do not know how to move information from one library to another *)
(* TODO: Should be possible now because you have both libraries in GitHub Desktop now *)
lemma big_sum_reordering_fst:
  fixes  S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. f z) = (\<Sum>u\<in>fst ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>S}. f (u, v)))\<close>
proof-
  define g where \<open>g z = (if z \<in> S then f z else 0)\<close>
    for z
  have \<open>(\<Sum>z\<in>S. f z) = (\<Sum>z\<in>S. g z)\<close>
    unfolding g_def
    by auto
  also have \<open>\<dots>  = (\<Sum>z\<in>((fst ` S) \<times> (snd ` S)). g z)\<close>
  proof-
    have \<open>S \<subseteq> ((fst ` S) \<times> (snd ` S))\<close>
      by (simp add: subset_fst_snd)
    thus ?thesis unfolding g_def
      by (smt DiffD2 assms finite_SigmaI finite_imageI sum.mono_neutral_right)
        (* > 1s *)
  qed
  also have \<open>\<dots>  = (\<Sum>u\<in>(fst ` S). (\<Sum>v\<in>(snd ` S). g (u,v)))\<close>
    by (simp add: sum.cartesian_product)
  also have \<open>\<dots>  = (\<Sum>u\<in>(fst ` S). (\<Sum>v\<in>{v|v. (u,v)\<in>S}.  f (u, v)) )\<close>
  proof-
    have \<open>u \<in> fst ` S \<Longrightarrow> (\<Sum>v\<in>(snd ` S). g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}.  f (u, v))\<close>
      for u
    proof-
      have \<open>{v|v. (u,v)\<in>S} \<subseteq> (snd ` S)\<close>
        using image_iff by fastforce
      hence \<open>(\<Sum>v\<in>(snd ` S). g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}. g (u,v))
             + (\<Sum>v\<in>(snd ` S)-{v|v. (u,v)\<in>S}. g (u,v))\<close>
        by (simp add: add.commute assms sum.subset_diff)
      moreover have \<open>(\<Sum>v\<in>(snd ` S)-{v|v. (u,v)\<in>S}. g (u,v)) = 0\<close>
        by (simp add: g_def)        
      moreover have \<open>(\<Sum>v\<in>{v|v. (u,v)\<in>S}. g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}. f (u,v))\<close>
        unfolding g_def
        by auto
      ultimately show ?thesis by auto
    qed
    thus ?thesis
      by auto 
  qed
  finally show ?thesis by blast
qed

(* TODO: Never used in Bounded Operators. Move to tensor product. *)
lemma swap_set_fst:
  \<open>fst ` (prod.swap ` S) = snd ` S\<close>
  unfolding prod.swap_def apply auto
   apply (simp add: rev_image_eqI)
  by (metis (no_types, lifting) fst_conv image_cong image_eqI pair_in_swap_image prod.swap_def)

(* TODO: Never used in Bounded Operators. Move to tensor product. *)
lemma swap_set_snd:
  \<open>snd ` (prod.swap ` S) = fst ` S\<close>
  unfolding prod.swap_def apply auto
   apply (simp add: rev_image_eqI)
  using image_iff by fastforce

(* TODO: Never used in Bounded Operators. Move to tensor product. *)
lemma big_sum_reordering_snd:
  fixes  S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. f z) = (\<Sum>v\<in>snd ` S. (\<Sum>u\<in>{u|u. (u,v)\<in>S}. f (u, v)))\<close>
proof-
  have \<open>prod.swap \<circ> (prod.swap::('a \<times> 'b \<Rightarrow> 'b \<times> 'a)) = id\<close>
    by simp    
  hence \<open>(\<Sum>z\<in>S. f z) = (\<Sum>z\<in>prod.swap ` (prod.swap ` S). f z)\<close>
    by (simp add: \<open>prod.swap \<circ> prod.swap = id\<close> image_comp)
  also have \<open>\<dots> = (\<Sum>z\<in>(prod.swap ` S). (f \<circ> prod.swap) z)\<close>
  proof-
    have \<open>inj prod.swap\<close>
      by simp      
    show ?thesis
      by (meson \<open>inj prod.swap\<close> inj_def inj_on_def sum.reindex)    
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>fst ` (prod.swap ` S). (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. (f \<circ> prod.swap) (u,v)))\<close>
  proof-
    have \<open>finite (prod.swap ` S)\<close>
      using \<open>finite S\<close> by simp
    thus ?thesis
      using big_sum_reordering_fst[where S = "prod.swap ` S" and f = "f \<circ> prod.swap"]
      by blast
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. (f \<circ> prod.swap) (u,v)))\<close>
  proof-
    have \<open>fst ` (prod.swap ` S) = snd ` S\<close>
      by (simp add: swap_set_fst) 
    thus ?thesis by simp
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. f (v,u) ))\<close>
  proof-
    have \<open>prod.swap (u, v) = (v, u)\<close>
      for u::'a and v::'b
      unfolding prod.swap_def by auto
    hence \<open>(f \<circ> prod.swap) (u, v) = f (v, u)\<close>
      for v::'a and u::'b
      by simp
    thus ?thesis by simp      
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (v,u)\<in>S}. f (v,u) ))\<close>
  proof-
    have \<open>(u,v)\<in>(prod.swap ` S) \<longleftrightarrow> (v,u)\<in>S\<close>
      for u v
      by simp
    thus ?thesis by simp
  qed
  finally show ?thesis by blast
qed

class not_singleton =
  assumes not_singleton_card: "\<exists>x y. x \<noteq> y"

lemma not_singleton_existence[simp]:
  \<open>\<exists> x::('a::not_singleton). x \<noteq> t\<close>
proof (rule classical)
  assume \<open>\<nexists>x. (x::'a) \<noteq> t\<close> 
  have \<open>\<exists> x::'a. \<exists> y::'a. x \<noteq> y\<close>
    using not_singleton_card
    by blast
  then obtain x y::'a where \<open>x \<noteq> y\<close>
    by blast
  have \<open>\<forall> x::'a. x = t\<close>
    using \<open>\<nexists>x. (x::'a) \<noteq> t\<close> by simp
  hence \<open>x = t\<close>
    by blast
  moreover have \<open>y = t\<close>
    using \<open>\<forall> x::'a. x = t\<close>
    by blast
  ultimately have \<open>x = y\<close>
    by simp
  thus ?thesis using \<open>x \<noteq> y\<close> by blast
qed

lemma UNIV_not_singleton[simp]: "(UNIV::_::not_singleton set) \<noteq> {x}"
  using not_singleton_existence[of x] by blast

(* lemma UNIV_not_singleton_converse: "(\<And> x. (UNIV::'a set) \<noteq> {x}) \<Longrightarrow> \<exists>x::'a. \<exists>y::'a. x \<noteq> y"
  by fastforce *)

(* lemma UNIV_not_singleton_converse_zero: "((UNIV::('a::real_normed_vector) set) \<noteq> {0}) \<Longrightarrow> \<exists>x::'a. \<exists>y::'a. x \<noteq> y"
  using UNIV_not_singleton_converse
  by fastforce  *)

subclass (in card2) not_singleton
  apply standard using two_le_card
  by (meson card_2_exists ex_card) 


typedef 'a euclidean_space = "UNIV :: ('a \<Rightarrow> real) set" ..
setup_lifting type_definition_euclidean_space

instantiation euclidean_space :: (type) real_vector begin
lift_definition plus_euclidean_space :: "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" is "\<lambda>f g x. f x + g x" .
lift_definition zero_euclidean_space :: "'a euclidean_space" is "\<lambda>_. 0" .
lift_definition uminus_euclidean_space :: "'a euclidean_space \<Rightarrow> 'a euclidean_space" is "\<lambda>f x. - f x" .
lift_definition minus_euclidean_space :: "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" is "\<lambda>f g x. f x - g x" .
lift_definition scaleR_euclidean_space :: "real \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" is "\<lambda>c f x. c * f x" .
instance
  apply intro_classes
  by (transfer; auto intro: distrib_left distrib_right)+
end

instantiation euclidean_space :: (finite) real_inner begin
lift_definition inner_euclidean_space :: "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> real"
  is "\<lambda>f g. \<Sum>x\<in>UNIV. f x * g x :: real" .
definition "norm_euclidean_space (x::'a euclidean_space) = sqrt (x \<bullet> x)"
definition "dist_euclidean_space (x::'a euclidean_space) y = norm (x-y)"
definition "sgn x = x /\<^sub>R norm x" for x::"'a euclidean_space"
definition "uniformity = (INF e\<in>{0<..}. principal {(x::'a euclidean_space, y). dist x y < e})"
definition "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x'::'a euclidean_space, y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
instance
proof intro_classes
  fix x :: "'a euclidean_space"
    and y :: "'a euclidean_space"
      and z :: "'a euclidean_space"
  show "dist (x::'a euclidean_space) y = norm (x - y)"
    and "sgn (x::'a euclidean_space) = x /\<^sub>R norm x"
    and "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a euclidean_space) y < e})"
    and "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a euclidean_space) = x \<longrightarrow> y \<in> U)"
    and "norm x = sqrt (x \<bullet> x)" for U
    unfolding dist_euclidean_space_def norm_euclidean_space_def sgn_euclidean_space_def
      uniformity_euclidean_space_def open_euclidean_space_def
    by simp_all

  show "x \<bullet> y = y \<bullet> x"
    apply transfer
    by (simp add: mult.commute)
  show "(x + y) \<bullet> z = x \<bullet> z + y \<bullet> z"
    apply transfer
    apply (subst sum.distrib[symmetric])
    by (simp add: distrib_left mult.commute)
  show "r *\<^sub>R x \<bullet> y = r * (x \<bullet> y)" for r :: real
    apply transfer
    apply (subst sum_distrib_left)
    by (simp add: mult.assoc)
  show "0 \<le> x \<bullet> x"
    apply transfer
    by (simp add: sum_nonneg)
  show "(x \<bullet> x = 0) = (x = 0)"
    thm sum_nonneg_eq_0_iff
  proof (transfer, rule)
    fix f :: "'a \<Rightarrow> real"
    assume "(\<Sum>xa\<in>UNIV. f xa * f xa) = 0"
    then have "f x * f x = 0" for x
      apply (rule_tac sum_nonneg_eq_0_iff[THEN iffD1, rule_format, where A=UNIV and x=x])
      by auto
    then show "f = (\<lambda>_. 0)"
      by auto
  qed auto
qed
end

instantiation euclidean_space :: (finite) euclidean_space begin
lift_definition euclidean_space_basis_vector :: "'a \<Rightarrow> 'a euclidean_space" is
  "\<lambda>x. indicator {x}" .
definition "Basis_euclidean_space == (euclidean_space_basis_vector ` UNIV)"
instance
proof intro_classes
  fix u :: "'a euclidean_space"
    and v :: "'a euclidean_space"
  show "(Basis::'a euclidean_space set) \<noteq> {}"
    unfolding Basis_euclidean_space_def by simp
  show "finite (Basis::'a euclidean_space set)"
    unfolding Basis_euclidean_space_def by simp
  show "u \<bullet> v = (if u = v then 1 else 0)"
    if "u \<in> Basis" and "v \<in> Basis"
    using that unfolding Basis_euclidean_space_def
    apply transfer apply auto
    by (auto simp: indicator_def)
  show "(\<forall>v\<in>Basis. (u::'a euclidean_space) \<bullet> v = 0) = (u = 0)"
    unfolding Basis_euclidean_space_def
    apply transfer
    by auto
qed
end

(* TODO move somewhere appropriate *)
lemma (in vector_space) span_finite_basis_exists:
  assumes "finite A"
  shows "\<exists>B. finite B \<and> independent B \<and> span B = span A \<and> card B = dim A"
proof -
  obtain B where BT1: "B \<subseteq> span A" 
    and BT2: "span A \<subseteq> span B"
    and indep: "independent B"  
    and card: "card B = dim (span A)"
    using basis_exists[where V="span A"]
    by metis
  have "finite B"
    using assms indep BT1 by (rule independent_span_bound[THEN conjunct1])
  moreover from BT1 BT2 have BT: "span B = span A"
    using span_mono span_span by blast
  moreover from card have "card B = dim (span A)"
    by auto
  moreover note indep
  ultimately show ?thesis
    by auto
qed


subsection\<open>Ordered Fields\<close>
text \<open>In this section we introduce some type classes for ordered rings/fields/etc.
that are weakenings of existing classes. Most theorems in this section are 
copies of the eponymous theorems from Isabelle/HOL, except that they are now proven 
requiring weaker type classes (usually the need for a total order is removed).

Since the lemmas are identical to the originals except for weaker type constraints, 
we use the same names as for the original lemmas. (In fact, the new lemmas could replace
the original ones in Isabelle/HOL with at most minor incompatibilities.\<close>

subsection \<open>Missing from Orderings.thy\<close>

text \<open>This class is analogous to \<^class>\<open>unbounded_dense_linorder\<close>, except that it does not require a total order\<close>

class unbounded_dense_order = dense_order + no_top + no_bot

instance unbounded_dense_linorder \<subseteq> unbounded_dense_order ..

subsection \<open>Missing from Rings.thy\<close>

text \<open>The existing class \<^class>\<open>abs_if\<close> requires \<^term>\<open>\<bar>a\<bar> = (if a < 0 then - a else a)\<close>.
However, if \<^term>\<open>(<)\<close> is not a total order, this condition is too strong when \<^term>\<open>a\<close> 
is incomparable with \<^term>\<open>0\<close>. (Namely, it requires the absolute value to be
the identity on such elements. E.g., the absolute value for complex numbers does not 
satisfy this.) The following class \<open>partial_abs_if\<close> is analogous to \<^class>\<open>abs_if\<close>
but does not require anything if \<^term>\<open>a\<close> is incomparable with \<^term>\<open>0\<close>.\<close>


class partial_abs_if = minus + uminus + ord + zero + abs +
  assumes abs_neg: "a \<le> 0 \<Longrightarrow> abs a = -a"
  assumes abs_pos: "a \<ge> 0 \<Longrightarrow> abs a = a"

class ordered_semiring_1 = ordered_semiring + semiring_1
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_semiring_1\<close> without requiring a total order\<close>
begin

lemma convex_bound_le:
  assumes "x \<le> a" "y \<le> a" "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "u * x + v * y \<le> a"
proof-
  from assms have "u * x + v * y \<le> u * a + v * a"
    by (simp add: add_mono mult_left_mono)
  with assms show ?thesis
    unfolding distrib_right[symmetric] by simp
qed

end

subclass (in linordered_semiring_1) ordered_semiring_1 ..

class ordered_semiring_strict = semiring + comm_monoid_add + ordered_cancel_ab_semigroup_add +
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_semiring_strict\<close> without requiring a total order\<close>
  assumes mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  assumes mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"
begin

subclass semiring_0_cancel ..

subclass ordered_semiring
proof
  fix a b c :: 'a
  assume *: "a \<le> b" "0 \<le> c"
  thus "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
  from * show "a * c \<le> b * c"
    unfolding le_less
    using mult_strict_right_mono by (cases "c = 0") auto
qed

lemma mult_pos_pos[simp]: "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a * b"
  using mult_strict_left_mono [of 0 b a] by simp

lemma mult_pos_neg: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> a * b < 0"
  using mult_strict_left_mono [of b 0 a] by simp

lemma mult_neg_pos: "a < 0 \<Longrightarrow> 0 < b \<Longrightarrow> a * b < 0"
  using mult_strict_right_mono [of a 0 b] by simp


text \<open>Strict monotonicity in both arguments\<close>
lemma mult_strict_mono:
  assumes "a < b" and "c < d" and "0 < b" and "0 \<le> c"
  shows "a * c < b * d"
  using assms
  apply (cases "c = 0")
   apply simp
  apply (erule mult_strict_right_mono [THEN less_trans])
   apply (auto simp add: le_less)
  apply (erule (1) mult_strict_left_mono)
  done

text \<open>This weaker variant has more natural premises\<close>
lemma mult_strict_mono':
  assumes "a < b" and "c < d" and "0 \<le> a" and "0 \<le> c"
  shows "a * c < b * d"
  by (rule mult_strict_mono) (insert assms, auto)

lemma mult_less_le_imp_less:
  assumes "a < b" and "c \<le> d" and "0 \<le> a" and "0 < c"
  shows "a * c < b * d"
  using assms
  apply (subgoal_tac "a * c < b * c")
   apply (erule less_le_trans)
   apply (erule mult_left_mono)
   apply simp
  by (erule (1) mult_strict_right_mono)


lemma mult_le_less_imp_less:
  assumes "a \<le> b" and "c < d" and "0 < a" and "0 \<le> c"
  shows "a * c < b * d"
  using assms
  apply (subgoal_tac "a * c \<le> b * c")
   apply (erule le_less_trans)
   apply (erule mult_strict_left_mono)
   apply simp
  by (erule (1) mult_right_mono)

end




subclass (in linordered_semiring_strict) ordered_semiring_strict 
  apply standard
   apply (simp add: local.mult_strict_left_mono)
  by (simp add: local.mult_strict_right_mono)


class ordered_semiring_1_strict = ordered_semiring_strict + semiring_1
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_semiring_1_strict\<close> without requiring a total order\<close>
begin

subclass ordered_semiring_1 ..

lemma convex_bound_lt:
  assumes "x < a" "y < a" "0 \<le> u" "0 \<le> v" "u + v = 1"
  shows "u * x + v * y < a"
proof -
  from assms have "u * x + v * y < u * a + v * a"
    by (cases "u = 0") (auto intro!: add_less_le_mono mult_strict_left_mono mult_left_mono)
  with assms show ?thesis
    unfolding distrib_right[symmetric] by simp
qed

end

subclass (in linordered_semiring_1_strict) ordered_semiring_1_strict .. 

class ordered_comm_semiring_strict = comm_semiring_0 + ordered_cancel_ab_semigroup_add +
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_comm_semiring_strict\<close> without requiring a total order\<close>
  assumes comm_mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
begin

subclass ordered_semiring_strict
proof
  fix a b c :: 'a
  assume "a < b" "0 < c"
  thus "c * a < c * b"
    by (rule comm_mult_strict_left_mono)
  thus "a * c < b * c"
    by (simp only: mult.commute)
qed

subclass ordered_cancel_comm_semiring
proof
  fix a b c :: 'a
  assume "a \<le> b" "0 \<le> c"
  thus "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
qed

end

subclass (in linordered_comm_semiring_strict) ordered_comm_semiring_strict 
  apply standard
  by (simp add: local.mult_strict_left_mono)


class ordered_ring_strict = ring + ordered_semiring_strict
  + ordered_ab_group_add + partial_abs_if
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_ring_strict\<close> without requiring a total order\<close>
begin

subclass ordered_ring ..

lemma mult_strict_left_mono_neg: "b < a \<Longrightarrow> c < 0 \<Longrightarrow> c * a < c * b"
  using mult_strict_left_mono [of b a "- c"] by simp

lemma mult_strict_right_mono_neg: "b < a \<Longrightarrow> c < 0 \<Longrightarrow> a * c < b * c"
  using mult_strict_right_mono [of b a "- c"] by simp

lemma mult_neg_neg: "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> 0 < a * b"
  using mult_strict_right_mono_neg [of a 0 b] by simp

end

lemmas mult_sign_intros =
  mult_nonneg_nonneg mult_nonneg_nonpos
  mult_nonpos_nonneg mult_nonpos_nonpos
  mult_pos_pos mult_pos_neg
  mult_neg_pos mult_neg_neg


subsection \<open>Ordered fields\<close>

class ordered_field = field + order + ordered_comm_semiring_strict + ordered_ab_group_add + partial_abs_if 
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_field\<close> without requiring a total order\<close>
begin

lemma frac_less_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y < w / z \<longleftrightarrow> (x * z - w * y) / (y * z) < 0"
  by (subst less_iff_diff_less_0) (simp add: diff_frac_eq )

lemma frac_le_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y \<le> w / z \<longleftrightarrow> (x * z - w * y) / (y * z) \<le> 0"
  by (subst le_iff_diff_le_0) (simp add: diff_frac_eq )


lemmas sign_simps = algebra_simps zero_less_mult_iff mult_less_0_iff

lemmas (in -) sign_simps = algebra_simps zero_less_mult_iff mult_less_0_iff


text \<open>Division and the Number One\<close>

text\<open>Simplify expressions equated with 1\<close>

lemma zero_eq_1_divide_iff [simp]: "0 = 1 / a \<longleftrightarrow> a = 0"
  by (cases "a = 0") (auto simp: field_simps)

lemma one_divide_eq_0_iff [simp]: "1 / a = 0 \<longleftrightarrow> a = 0"
  using zero_eq_1_divide_iff[of a] by simp

text\<open>Simplify expressions such as \<open>0 < 1/x\<close> to \<open>0 < x\<close>\<close>

text\<open>Simplify quotients that are compared with the value 1.\<close>

text \<open>Conditional Simplification Rules: No Case Splits\<close>

lemma eq_divide_eq_1 [simp]:
  "(1 = b/a) = ((a \<noteq> 0 & a = b))"
  by (auto simp add: eq_divide_eq)

lemma divide_eq_eq_1 [simp]:
  "(b/a = 1) = ((a \<noteq> 0 & a = b))"
  by (auto simp add: divide_eq_eq)

end

text \<open>The following type class intends to capture some important properties 
  that are common both to the real and the complex numbers. The purpose is
  to be able to state and prove lemmas that apply both to the real and the complex 
  numbers without needing to state the lemma twice.
\<close>

class nice_ordered_field = ordered_field + zero_less_one + idom_abs_sgn +
  assumes positive_imp_inverse_positive: "0 < a \<Longrightarrow> 0 < inverse a"
    and inverse_le_imp_le: "inverse a \<le> inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b \<le> a"
    and dense_le: "(\<And>x. x < y \<Longrightarrow> x \<le> z) \<Longrightarrow> y \<le> z"
    and nn_comparable: "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a \<le> b \<or> b \<le> a"
    and abs_nn: "abs x \<ge> 0"
begin

subclass (in linordered_field) nice_ordered_field
  apply standard
        apply auto
  using local.inverse_le_imp_le apply blast
  using local.dense_le by blast

lemma comparable:
  assumes "a \<le> c \<or> a \<ge> c"
    and "b \<le> c \<or> b \<ge> c"
  shows "a \<le> b \<or> b \<le> a"
  using assms 
proof auto
  assume "a \<le> c" and "b \<le> c"
  hence "0 \<le> c-a" and "0 \<le> c-b" by auto
  hence "c-a \<le> c-b \<or> c-a \<ge> c-b" by (rule nn_comparable)
  hence "-a \<le> -b \<or> -a \<ge> -b"
    using local.add_le_imp_le_right local.uminus_add_conv_diff by presburger
  moreover assume "\<not> b \<le> a"
  ultimately show "a \<le> b" by simp
  thm nn_comparable
next
  assume "c \<le> a" and "b \<le> c"
  hence "b \<le> a" by auto
  moreover assume "\<not> b \<le> a"
  ultimately have False by simp
  thus "a \<le> b" by simp
next
  assume "a \<ge> c" and "b \<ge> c"
  hence "0 \<le> a-c" and "0 \<le> b-c" by auto
  hence "a-c \<le> b-c \<or> a-c \<ge> b-c" by (rule nn_comparable)
  hence "a \<le> b \<or> a \<ge> b"
    by (simp add: local.le_diff_eq)
  moreover assume "\<not> b \<le> a"
  ultimately show "a \<le> b" by simp
qed

lemma negative_imp_inverse_negative:
  "a < 0 \<Longrightarrow> inverse a < 0"
  by (insert positive_imp_inverse_positive [of "-a"],
      simp add: nonzero_inverse_minus_eq less_imp_not_eq)


lemma inverse_positive_imp_positive:
  assumes inv_gt_0: "0 < inverse a" and nz: "a \<noteq> 0"
  shows "0 < a"
proof -
  have "0 < inverse (inverse a)"
    using inv_gt_0 by (rule positive_imp_inverse_positive)
  thus "0 < a"
    using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma inverse_negative_imp_negative:
  assumes inv_less_0: "inverse a < 0" and nz: "a \<noteq> 0"
  shows "a < 0"
proof -
  have "inverse (inverse a) < 0"
    using inv_less_0 by (rule negative_imp_inverse_negative)
  thus "a < 0" using nz by (simp add: nonzero_inverse_inverse_eq)
qed

lemma linordered_field_no_lb:
  "\<forall>x. \<exists>y. y < x"
proof
  fix x::'a
  have m1: "- (1::'a) < 0" by simp
  from add_strict_right_mono[OF m1, where c=x]
  have "(- 1) + x < x" by simp
  thus "\<exists>y. y < x" by blast
qed

lemma linordered_field_no_ub:
  "\<forall> x. \<exists>y. y > x"
proof
  fix x::'a
  have m1: " (1::'a) > 0" by simp
  from add_strict_right_mono[OF m1, where c=x]
  have "1 + x > x" by simp
  thus "\<exists>y. y > x" by blast
qed

lemma less_imp_inverse_less:
  assumes less: "a < b" and apos:  "0 < a"
  shows "inverse b < inverse a"
  using assms by (metis local.dual_order.strict_iff_order local.inverse_inverse_eq local.inverse_le_imp_le local.positive_imp_inverse_positive)

lemma inverse_less_imp_less:
  "inverse a < inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b < a"
  apply (simp add: less_le [of "inverse a"] less_le [of "b"])
  by (force dest!: inverse_le_imp_le nonzero_inverse_eq_imp_eq)

text\<open>Both premises are essential. Consider -1 and 1.\<close>
lemma inverse_less_iff_less [simp]:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
  by (blast intro: less_imp_inverse_less dest: inverse_less_imp_less)

lemma le_imp_inverse_le:
  "a \<le> b \<Longrightarrow> 0 < a \<Longrightarrow> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less)

lemma inverse_le_iff_le [simp]:
  "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le dest: inverse_le_imp_le)


text\<open>These results refer to both operands being negative.  The opposite-sign
case is trivial, since inverse preserves signs.\<close>
lemma inverse_le_imp_le_neg:
  "inverse a \<le> inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b \<le> a"
  by (metis local.inverse_le_imp_le local.inverse_minus_eq local.neg_0_less_iff_less local.neg_le_iff_le)

lemma inverse_less_imp_less_neg:
  "inverse a < inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b < a"
  using local.dual_order.strict_iff_order local.inverse_le_imp_le_neg by blast

lemma inverse_less_iff_less_neg [simp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
  apply (insert inverse_less_iff_less [of "-b" "-a"])
  by (simp del: inverse_less_iff_less
      add: nonzero_inverse_minus_eq)

lemma le_imp_inverse_le_neg:
  "a \<le> b \<Longrightarrow> b < 0 ==> inverse b \<le> inverse a"
  by (force simp add: le_less less_imp_inverse_less_neg)

lemma inverse_le_iff_le_neg [simp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a \<le> inverse b \<longleftrightarrow> b \<le> a"
  by (blast intro: le_imp_inverse_le_neg dest: inverse_le_imp_le_neg)

lemma one_less_inverse:
  "0 < a \<Longrightarrow> a < 1 \<Longrightarrow> 1 < inverse a"
  using less_imp_inverse_less [of a 1, unfolded inverse_1] .

lemma one_le_inverse:
  "0 < a \<Longrightarrow> a \<le> 1 \<Longrightarrow> 1 \<le> inverse a"
  using le_imp_inverse_le [of a 1, unfolded inverse_1] .

lemma pos_le_divide_eq [field_simps]:
  assumes "0 < c"
  shows "a \<le> b / c \<longleftrightarrow> a * c \<le> b"
  using assms by (metis local.divide_eq_imp local.divide_inverse_commute local.dual_order.order_iff_strict local.dual_order.strict_iff_order local.mult_right_mono local.mult_strict_left_mono local.nonzero_divide_eq_eq local.order.strict_implies_order local.positive_imp_inverse_positive)

lemma pos_less_divide_eq [field_simps]:
  assumes "0 < c"
  shows "a < b / c \<longleftrightarrow> a * c < b"
  using assms local.dual_order.strict_iff_order local.nonzero_divide_eq_eq local.pos_le_divide_eq by auto

lemma neg_less_divide_eq [field_simps]:
  assumes "c < 0"
  shows "a < b / c \<longleftrightarrow> b < a * c"
  by (metis assms local.minus_divide_divide local.mult_minus_right local.neg_0_less_iff_less local.neg_less_iff_less local.pos_less_divide_eq)

lemma neg_le_divide_eq [field_simps]:
  assumes "c < 0"
  shows "a \<le> b / c \<longleftrightarrow> b \<le> a * c"
  by (metis assms local.dual_order.order_iff_strict local.dual_order.strict_iff_order local.neg_less_divide_eq local.nonzero_divide_eq_eq)

lemma pos_divide_le_eq [field_simps]:
  assumes "0 < c"
  shows "b / c \<le> a \<longleftrightarrow> b \<le> a * c"
  by (metis assms local.dual_order.strict_iff_order local.nonzero_eq_divide_eq local.pos_le_divide_eq)

lemma pos_divide_less_eq [field_simps]:
  assumes "0 < c"
  shows "b / c < a \<longleftrightarrow> b < a * c"
  by (metis assms local.minus_divide_left local.mult_minus_left local.neg_less_iff_less local.pos_less_divide_eq)

lemma neg_divide_le_eq [field_simps]:
  assumes "c < 0"
  shows "b / c \<le> a \<longleftrightarrow> a * c \<le> b"
  by (metis assms local.minus_divide_left local.mult_minus_left local.neg_le_divide_eq local.neg_le_iff_le)

lemma neg_divide_less_eq [field_simps]:
  assumes "c < 0"
  shows "b / c < a \<longleftrightarrow> a * c < b"
  using assms local.dual_order.strict_iff_order local.neg_divide_le_eq by auto

text\<open>The following \<open>field_simps\<close> rules are necessary, as minus is always moved atop of
division but we want to get rid of division.\<close>

lemma pos_le_minus_divide_eq [field_simps]: "0 < c \<Longrightarrow> a \<le> - (b / c) \<longleftrightarrow> a * c \<le> - b"
  unfolding minus_divide_left by (rule pos_le_divide_eq)

lemma neg_le_minus_divide_eq [field_simps]: "c < 0 \<Longrightarrow> a \<le> - (b / c) \<longleftrightarrow> - b \<le> a * c"
  unfolding minus_divide_left by (rule neg_le_divide_eq)

lemma pos_less_minus_divide_eq [field_simps]: "0 < c \<Longrightarrow> a < - (b / c) \<longleftrightarrow> a * c < - b"
  unfolding minus_divide_left by (rule pos_less_divide_eq)

lemma neg_less_minus_divide_eq [field_simps]: "c < 0 \<Longrightarrow> a < - (b / c) \<longleftrightarrow> - b < a * c"
  unfolding minus_divide_left by (rule neg_less_divide_eq)

lemma pos_minus_divide_less_eq [field_simps]: "0 < c \<Longrightarrow> - (b / c) < a \<longleftrightarrow> - b < a * c"
  unfolding minus_divide_left by (rule pos_divide_less_eq)

lemma neg_minus_divide_less_eq [field_simps]: "c < 0 \<Longrightarrow> - (b / c) < a \<longleftrightarrow> a * c < - b"
  unfolding minus_divide_left by (rule neg_divide_less_eq)

lemma pos_minus_divide_le_eq [field_simps]: "0 < c \<Longrightarrow> - (b / c) \<le> a \<longleftrightarrow> - b \<le> a * c"
  unfolding minus_divide_left by (rule pos_divide_le_eq)

lemma neg_minus_divide_le_eq [field_simps]: "c < 0 \<Longrightarrow> - (b / c) \<le> a \<longleftrightarrow> a * c \<le> - b"
  unfolding minus_divide_left by (rule neg_divide_le_eq)

lemma frac_less_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y < w / z \<longleftrightarrow> (x * z - w * y) / (y * z) < 0"
  by (subst less_iff_diff_less_0) (simp add: diff_frac_eq )

lemma frac_le_eq:
  "y \<noteq> 0 \<Longrightarrow> z \<noteq> 0 \<Longrightarrow> x / y \<le> w / z \<longleftrightarrow> (x * z - w * y) / (y * z) \<le> 0"
  by (subst le_iff_diff_le_0) (simp add: diff_frac_eq )


text\<open>Lemmas \<open>sign_simps\<close> is a first attempt to automate proofs
of positivity/negativity needed for \<open>field_simps\<close>. Have not added \<open>sign_simps\<close> to \<open>field_simps\<close> because the former can lead to case
explosions.\<close>

lemma divide_pos_pos[simp]:
  "0 < x ==> 0 < y ==> 0 < x / y"
  by(simp add:field_simps)

lemma divide_nonneg_pos:
  "0 <= x ==> 0 < y ==> 0 <= x / y"
  by(simp add:field_simps)

lemma divide_neg_pos:
  "x < 0 ==> 0 < y ==> x / y < 0"
  by(simp add:field_simps)

lemma divide_nonpos_pos:
  "x <= 0 ==> 0 < y ==> x / y <= 0"
  by(simp add:field_simps)

lemma divide_pos_neg:
  "0 < x ==> y < 0 ==> x / y < 0"
  by(simp add:field_simps)

lemma divide_nonneg_neg:
  "0 <= x ==> y < 0 ==> x / y <= 0"
  by(simp add:field_simps)

lemma divide_neg_neg:
  "x < 0 ==> y < 0 ==> 0 < x / y"
  by(simp add:field_simps)

lemma divide_nonpos_neg:
  "x <= 0 ==> y < 0 ==> 0 <= x / y"
  by(simp add:field_simps)

lemma divide_strict_right_mono:
  "[|a < b; 0 < c|] ==> a / c < b / c"
  by (simp add: less_imp_not_eq2 divide_inverse mult_strict_right_mono
      positive_imp_inverse_positive)


lemma divide_strict_right_mono_neg:
  "[|b < a; c < 0|] ==> a / c < b / c"
  apply (drule divide_strict_right_mono [of _ _ "-c"], simp)
  by (simp add: less_imp_not_eq nonzero_minus_divide_right [symmetric])

text\<open>The last premise ensures that \<^term>\<open>a\<close> and \<^term>\<open>b\<close>
      have the same sign\<close>
lemma divide_strict_left_mono:
  "[|b < a; 0 < c; 0 < a*b|] ==> c / a < c / b"
  by (metis local.divide_neg_pos local.dual_order.strict_iff_order local.frac_less_eq local.less_iff_diff_less_0 local.mult_not_zero local.mult_strict_left_mono)

lemma divide_left_mono:
  "[|b \<le> a; 0 \<le> c; 0 < a*b|] ==> c / a \<le> c / b"
  using local.divide_cancel_left local.divide_strict_left_mono local.dual_order.order_iff_strict by auto

lemma divide_strict_left_mono_neg:
  "[|a < b; c < 0; 0 < a*b|] ==> c / a < c / b"
  by (metis local.divide_strict_left_mono local.minus_divide_left local.neg_0_less_iff_less local.neg_less_iff_less mult_commute)

lemma mult_imp_div_pos_le: "0 < y ==> x <= z * y ==>
    x / y <= z"
  by (subst pos_divide_le_eq, assumption+)

lemma mult_imp_le_div_pos: "0 < y ==> z * y <= x ==>
    z <= x / y"
  by(simp add:field_simps)

lemma mult_imp_div_pos_less: "0 < y ==> x < z * y ==>
    x / y < z"
  by(simp add:field_simps)

lemma mult_imp_less_div_pos: "0 < y ==> z * y < x ==>
    z < x / y"
  by(simp add:field_simps)

lemma frac_le: "0 <= x ==>
    x <= y ==> 0 < w ==> w <= z  ==> x / z <= y / w"
  apply (rule mult_imp_div_pos_le)
   apply simp
  apply (subst times_divide_eq_left)
  apply (rule mult_imp_le_div_pos, assumption)
  apply (rule mult_mono)
  by simp_all


lemma frac_less: "0 <= x ==>
    x < y ==> 0 < w ==> w <= z  ==> x / z < y / w"
  apply (rule mult_imp_div_pos_less)
   apply simp
  apply (subst times_divide_eq_left)
  apply (rule mult_imp_less_div_pos, assumption)
  apply (erule mult_less_le_imp_less)
  by simp_all


lemma frac_less2: "0 < x ==>
    x <= y ==> 0 < w ==> w < z  ==> x / z < y / w"
  apply (rule mult_imp_div_pos_less)
   apply simp_all
  apply (rule mult_imp_less_div_pos, assumption)
  apply (erule mult_le_less_imp_less)
  by simp_all


lemma less_half_sum: "a < b ==> a < (a+b) / (1+1)"
  by (metis local.add_pos_pos local.add_strict_left_mono local.mult_imp_less_div_pos local.semiring_normalization_rules(4) local.zero_less_one mult_commute)

lemma gt_half_sum: "a < b ==> (a+b)/(1+1) < b"
  by (metis local.add_pos_pos local.add_strict_left_mono local.mult_imp_div_pos_less local.semiring_normalization_rules(24) local.semiring_normalization_rules(4) local.zero_less_one mult_commute)

subclass unbounded_dense_order
proof
  fix x y :: 'a
  have less_add_one: "a < a + 1" for a::'a by auto
  from less_add_one show "\<exists>y. x < y" apply (rule_tac exI[of _ "x+1"]) by auto
  from less_add_one have "x + (- 1) < (x + 1) + (- 1)"
    by (rule add_strict_right_mono)
  hence "x - 1 < x + 1 - 1" by simp
  hence "x - 1 < x" by (simp add: algebra_simps)
  thus "\<exists>y. y < x" ..
  show "x < y \<Longrightarrow> \<exists>z>x. z < y" by (blast intro!: less_half_sum gt_half_sum)
qed


lemma dense_le_bounded:
  fixes x y z :: 'a
  assumes "x < y"
  assumes *: "\<And>w. \<lbrakk> x < w ; w < y \<rbrakk> \<Longrightarrow> w \<le> z"
  shows "y \<le> z"
proof (rule dense_le)
  fix w assume "w < y"
  from dense[OF \<open>x < y\<close>] obtain u where "x < u" "u < y" by safe
  have "u \<le> w \<or> w \<le> u"
    apply (rule comparable[of _ y])
    using \<open>w<y\<close> \<open>u<y\<close> by auto
  thus "w \<le> z"
  proof (rule disjE)
    assume "u \<le> w"
    from less_le_trans[OF \<open>x < u\<close> \<open>u \<le> w\<close>] \<open>w < y\<close>
    show "w \<le> z" by (rule *)
  next
    assume "w \<le> u"
    from \<open>w \<le> u\<close> *[OF \<open>x < u\<close> \<open>u < y\<close>]
    show "w \<le> z" by (rule order_trans)
  qed
qed

subclass field_abs_sgn ..


lemma nonzero_abs_inverse:
  "a \<noteq> 0 ==> \<bar>inverse a\<bar> = inverse \<bar>a\<bar>"
  by (rule abs_inverse)

lemma nonzero_abs_divide:
  "b \<noteq> 0 ==> \<bar>a / b\<bar> = \<bar>a\<bar> / \<bar>b\<bar>"
  by (rule abs_divide)

lemma field_le_epsilon:
  assumes e: "\<And>e. 0 < e \<Longrightarrow> x \<le> y + e"
  shows "x \<le> y"
proof (rule dense_le)
  fix t assume "t < x"
  hence "0 < x - t" by (simp add: less_diff_eq)
  from e [OF this] have "x + 0 \<le> x + (y - t)" by (simp add: algebra_simps)
  hence "0 \<le> y - t" by (simp only: add_le_cancel_left)
  thus "t \<le> y" by (simp add: algebra_simps)
qed

lemma inverse_positive_iff_positive [simp]:
  "(0 < inverse a) = (0 < a)"
  apply (cases "a = 0", simp)
  by (blast intro: inverse_positive_imp_positive positive_imp_inverse_positive)


lemma inverse_negative_iff_negative [simp]:
  "(inverse a < 0) = (a < 0)"
  apply (cases "a = 0", simp)
  by (blast intro: inverse_negative_imp_negative negative_imp_inverse_negative)


lemma inverse_nonnegative_iff_nonnegative [simp]:
  "0 \<le> inverse a \<longleftrightarrow> 0 \<le> a"
  by (simp add: local.dual_order.order_iff_strict)

lemma inverse_nonpositive_iff_nonpositive [simp]:
  "inverse a \<le> 0 \<longleftrightarrow> a \<le> 0"
  using local.inverse_nonnegative_iff_nonnegative local.neg_0_le_iff_le by fastforce

lemma one_less_inverse_iff: "1 < inverse x \<longleftrightarrow> 0 < x \<and> x < 1"
  using less_trans[of 1 x 0 for x]
  by (metis local.dual_order.strict_trans local.inverse_1 local.inverse_less_imp_less local.inverse_positive_iff_positive local.one_less_inverse local.zero_less_one)

lemma one_le_inverse_iff: "1 \<le> inverse x \<longleftrightarrow> 0 < x \<and> x \<le> 1"
  by (metis local.dual_order.strict_trans1 local.inverse_1 local.inverse_le_imp_le local.inverse_positive_iff_positive local.one_le_inverse local.zero_less_one)

lemma inverse_less_1_iff: "inverse x < 1 \<longleftrightarrow> x \<le> 0 \<or> 1 < x"
proof (rule)
  assume invx1: "inverse x < 1"
  have "inverse x \<le> 0 \<or> inverse x \<ge> 0"
    apply (rule comparable[where c=1]) 
     apply (rule disjI1) using invx1 apply simp
    using zero_less_one
    by (simp add: local.order.strict_iff_order)
  then consider (leq0) "inverse x \<le> 0" | (pos) "inverse x > 0" | (zero) "inverse x = 0"
    apply atomize_elim by auto
  thus "x \<le> 0 \<or> 1 < x"
  proof cases
    case leq0
      (* hence "x \<le> 0" by auto *)
    thus ?thesis by simp
  next
    case pos
    hence "x > 0" by auto
    moreover from invx1 have "inverse x < inverse 1" by auto
    ultimately have "x > 1"
      using local.inverse_less_imp_less by blast
    thus ?thesis by simp
  next
    case zero thus ?thesis by simp
  qed
next
  assume "x \<le> 0 \<or> 1 < x"
  then consider (neg) "x \<le> 0" | (g1) "1 < x" by auto
  thus "inverse x < 1"
  proof cases
    case neg
    thus ?thesis
      by (metis local.dual_order.order_iff_strict local.dual_order.strict_trans local.inverse_negative_iff_negative local.inverse_zero local.zero_less_one)
  next
    case g1
    thus ?thesis
      using local.less_imp_inverse_less by fastforce
  qed
qed

lemma inverse_le_1_iff: "inverse x \<le> 1 \<longleftrightarrow> x \<le> 0 \<or> 1 \<le> x"
  by (metis local.dual_order.order_iff_strict local.inverse_1 local.inverse_le_iff_le local.inverse_less_1_iff local.one_le_inverse_iff)

text\<open>Simplify expressions such as \<open>0 < 1/x\<close> to \<open>0 < x\<close>\<close>

lemma zero_le_divide_1_iff [simp]:
  "0 \<le> 1 / a \<longleftrightarrow> 0 \<le> a"
  using local.dual_order.order_iff_strict local.inverse_eq_divide local.inverse_positive_iff_positive by auto

lemma zero_less_divide_1_iff [simp]:
  "0 < 1 / a \<longleftrightarrow> 0 < a"
  by (simp add: local.dual_order.strict_iff_order)

lemma divide_le_0_1_iff [simp]:
  "1 / a \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (smt comparable local.dual_order.order_iff_strict local.eq_iff local.inverse_eq_divide local.inverse_le_1_iff local.one_divide_eq_0_iff local.one_le_inverse_iff local.zero_less_divide_1_iff)

lemma divide_less_0_1_iff [simp]:
  "1 / a < 0 \<longleftrightarrow> a < 0"
  using local.dual_order.strict_iff_order by auto

lemma divide_right_mono:
  "[|a \<le> b; 0 \<le> c|] ==> a/c \<le> b/c"
  using local.divide_cancel_right local.divide_strict_right_mono local.dual_order.order_iff_strict by blast

lemma divide_right_mono_neg: "a <= b
    ==> c <= 0 ==> b / c <= a / c"
  by (metis local.divide_cancel_right local.divide_strict_right_mono_neg local.dual_order.strict_implies_order local.eq_refl local.le_imp_less_or_eq)

lemma divide_left_mono_neg: "a <= b
    ==> c <= 0 ==> 0 < a * b ==> c / a <= c / b"  
  by (metis local.divide_left_mono local.minus_divide_left local.neg_0_le_iff_le local.neg_le_iff_le mult_commute)

lemma divide_nonneg_nonneg [simp]:
  "0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> 0 \<le> x / y"
  using local.divide_eq_0_iff local.divide_nonneg_pos local.dual_order.order_iff_strict by blast

lemma divide_nonpos_nonpos:
  "x \<le> 0 \<Longrightarrow> y \<le> 0 \<Longrightarrow> 0 \<le> x / y"
  using local.divide_nonpos_neg local.dual_order.order_iff_strict by auto

lemma divide_nonneg_nonpos:
  "0 \<le> x \<Longrightarrow> y \<le> 0 \<Longrightarrow> x / y \<le> 0"
  by (metis local.divide_eq_0_iff local.divide_nonneg_neg local.dual_order.order_iff_strict)

lemma divide_nonpos_nonneg:
  "x \<le> 0 \<Longrightarrow> 0 \<le> y \<Longrightarrow> x / y \<le> 0"
  using local.divide_nonpos_pos local.dual_order.order_iff_strict by auto

text \<open>Conditional Simplification Rules: No Case Splits\<close>

lemma le_divide_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (1 \<le> b/a) = (a \<le> b)"
  by (simp add: local.pos_le_divide_eq)

lemma le_divide_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (1 \<le> b/a) = (b \<le> a)"
  by (metis local.le_divide_eq_1_pos local.minus_divide_divide local.neg_0_less_iff_less local.neg_le_iff_le)

lemma divide_le_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (b/a \<le> 1) = (b \<le> a)"
  using local.pos_divide_le_eq by auto

lemma divide_le_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (b/a \<le> 1) = (a \<le> b)"
  by (metis local.divide_le_eq_1_pos local.minus_divide_divide local.neg_0_less_iff_less local.neg_le_iff_le)

lemma less_divide_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (1 < b/a) = (a < b)"
  by (simp add: local.dual_order.strict_iff_order)

lemma less_divide_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> (1 < b/a) = (b < a)"
  using local.dual_order.strict_iff_order by auto

lemma divide_less_eq_1_pos [simp]:
  "0 < a \<Longrightarrow> (b/a < 1) = (b < a)"
  using local.divide_le_eq_1_pos local.dual_order.strict_iff_order by auto

lemma divide_less_eq_1_neg [simp]:
  "a < 0 \<Longrightarrow> b/a < 1 \<longleftrightarrow> a < b"
  using local.dual_order.strict_iff_order by auto

lemma abs_div_pos: "0 < y ==>
    \<bar>x\<bar> / y = \<bar>x / y\<bar>"
  by (simp add: local.abs_pos)


lemma zero_le_divide_abs_iff [simp]: "(0 \<le> a / \<bar>b\<bar>) = (0 \<le> a | b = 0)"
proof 
  assume assm: "0 \<le> a / \<bar>b\<bar>"
  have absb: "abs b \<ge> 0" by (fact abs_nn)
  hence eq: "0 * abs b \<le> a / abs b * abs b"
    using assm local.mult_right_mono by blast
  show "0 \<le> a \<or> b = 0"
  proof (cases "b=0")
    case False
    hence absb0: "abs b \<noteq> 0"
      by (simp add: local.abs_eq_0_iff)
    hence "a / abs b * abs b = a" by simp
    with eq absb0 have "0 \<le> a" by auto
    thus ?thesis by simp
  next
    case True
    thus ?thesis by simp
  qed
next
  assume "0 \<le> a \<or> b = 0"
  then consider (a) "0 \<le> a" | (b) "b = 0" by atomize_elim auto
  thus "0 \<le> a / \<bar>b\<bar>"
  proof cases
    case a
    thus ?thesis using abs_nn by auto
  next
    case b
    thus ?thesis by auto
  qed
qed


lemma divide_le_0_abs_iff [simp]: "(a / \<bar>b\<bar> \<le> 0) = (a \<le> 0 | b = 0)"
  by (metis local.minus_divide_left local.neg_0_le_iff_le local.zero_le_divide_abs_iff)


text\<open>For creating values between \<^term>\<open>u\<close> and \<^term>\<open>v\<close>.\<close>
lemma scaling_mono:
  assumes "u \<le> v" "0 \<le> r" "r \<le> s"
  shows "u + r * (v - u) / s \<le> v"
proof -
  have "r/s \<le> 1" using assms
    by (metis local.divide_le_eq_1_pos local.division_ring_divide_zero local.dual_order.order_iff_strict local.dual_order.trans local.zero_less_one)
  hence "(r/s) * (v - u) \<le> 1 * (v - u)"
    apply (rule mult_right_mono)
    using assms by simp
  thus ?thesis
    by (simp add: field_simps)
qed

end


code_identifier
  code_module Ordered_Fields \<rightharpoonup> (SML) Arith and (OCaml) Arith and (Haskell) Arith



subsection\<open>Ordered Complex\<close>

declare Conjugate.less_eq_complex_def[simp del]
declare Conjugate.less_complex_def[simp del]

subsection \<open>Ordering on complex numbers\<close>

instantiation complex :: nice_ordered_field begin
instance
proof intro_classes
  note defs = less_eq_complex_def less_complex_def abs_complex_def
  fix x y z a b c :: complex
  show "a \<le> 0 \<Longrightarrow> \<bar>a\<bar> = - a" unfolding defs
    by (simp add: cmod_eq_Re complex_is_Real_iff)
  show "0 \<le> a \<Longrightarrow> \<bar>a\<bar> = a"
    unfolding defs
    by (metis abs_of_nonneg cmod_eq_Re comp_apply complex.exhaust_sel complex_of_real_def zero_complex.simps(1) zero_complex.simps(2))
  show "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b" unfolding defs by auto
  show "0 < (1::complex)" unfolding defs by simp
  show "0 < a \<Longrightarrow> 0 < inverse a" unfolding defs by auto
  define ra ia rb ib rc ic where "ra = Re a" "ia = Im a" "rb = Re b" "ib = Im b" "rc = Re c" "ic = Im c"
  note ri = this[symmetric]
  hence "a = Complex ra ia" "b = Complex rb ib" "c = Complex rc ic" by auto
  note ri = this ri
  show "inverse a \<le> inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b \<le> a" unfolding defs ri
    apply (auto simp: power2_eq_square) apply (cases "rb=0") 
     apply auto
    by (metis divide_eq_0_iff divide_le_eq_1 eq_iff less_eq_real_def less_le nice_ordered_field_class.frac_le nice_ordered_field_class.frac_less2 not_le)
  show "(\<And>a. a < b \<Longrightarrow> a \<le> c) \<Longrightarrow> b \<le> c" unfolding defs ri
    apply auto
     apply (metis complex.sel(1) complex.sel(2) lt_ex)
    by (metis complex.sel(1) complex.sel(2) dense not_less)
  show "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a \<le> b \<or> b \<le> a" unfolding defs by auto
  show "0 \<le> \<bar>x\<bar>" unfolding defs by auto
qed
end

lemma less_eq_complexI: "Re x \<le> Re y \<Longrightarrow> Im x = Im y \<Longrightarrow> x\<le>y" unfolding less_eq_complex_def by simp
lemma less_complexI: "Re x < Re y \<Longrightarrow> Im x = Im y \<Longrightarrow> x<y" unfolding less_complex_def by simp


lemma complex_of_real_mono:
  "x \<le> y \<Longrightarrow> complex_of_real x \<le> complex_of_real y"
  unfolding less_eq_complex_def by auto

lemma complex_of_real_mono_iff[simp]:
  "complex_of_real x \<le> complex_of_real y \<longleftrightarrow> x \<le> y"
  unfolding less_eq_complex_def by auto

lemma complex_of_real_strict_mono_iff[simp]:
  "complex_of_real x < complex_of_real y \<longleftrightarrow> x < y"
  unfolding less_complex_def by auto

lemma complex_of_real_nn_iff[simp]:
  "0 \<le> complex_of_real y \<longleftrightarrow> 0 \<le> y"
  unfolding less_eq_complex_def by auto

lemma complex_of_real_pos_iff[simp]:
  "0 < complex_of_real y \<longleftrightarrow> 0 < y"
  unfolding less_complex_def by auto

lemma Re_mono: "x \<le> y \<Longrightarrow> Re x \<le> Re y"
  unfolding less_eq_complex_def by simp

lemma comp_Im_same: "x \<le> y \<Longrightarrow> Im x = Im y"
  unfolding less_eq_complex_def by simp


lemma Re_strict_mono: "x < y \<Longrightarrow> Re x < Re y"
  unfolding less_complex_def by simp

lemma complex_of_real_cmod: assumes "x \<ge> 0" shows "complex_of_real (cmod x) = x"
  by (metis Reals_cases abs_of_nonneg assms comp_Im_same complex_is_Real_iff complex_of_real_nn_iff norm_of_real zero_complex.simps(2))


subsection\<open>Infinite Set Sum Missing\<close>


definition "infsetsum'_converges f A = (\<exists>x. (sum f \<longlongrightarrow> x) (finite_subsets_at_top A))"

definition infsetsum' :: "('a \<Rightarrow> 'b::{comm_monoid_add,t2_space}) \<Rightarrow> 'a set \<Rightarrow> 'b" where
  "infsetsum' f A = (if infsetsum'_converges f A then Lim (finite_subsets_at_top A) (sum f) else 0)"


lemma infsetsum'_converges_cong: 
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsetsum'_converges f A = infsetsum'_converges g A"
  unfolding infsetsum'_converges_def
  apply (rule ex_cong1)
  apply (rule tendsto_cong)
  apply (rule eventually_finite_subsets_at_top_weakI)
  using assms
  by (meson subset_eq sum.cong) 

lemma infsetsum'_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsetsum' f A = infsetsum' g A"
proof -
  have "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A) \<longleftrightarrow> (sum g \<longlongrightarrow> x) (finite_subsets_at_top A)" for x
    apply (rule tendsto_cong)
    apply (rule eventually_finite_subsets_at_top_weakI)
    using assms
    by (meson subset_eq sum.cong)
  hence "Lim (finite_subsets_at_top A) (sum f) = Lim (finite_subsets_at_top A) (sum g)"
    unfolding Topological_Spaces.Lim_def[abs_def]
    by auto
  thus ?thesis
    unfolding infsetsum'_def
    apply (subst infsetsum'_converges_cong[OF assms])
    by auto
qed


lemma abs_summable_finiteI0:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
    and "B \<ge> 0"
  shows "f abs_summable_on S" and "infsetsum (\<lambda>x. norm (f x)) S \<le> B"
  unfolding atomize_conj
proof (cases "S={}")
  case True
  thus "f abs_summable_on S \<and> infsetsum (\<lambda>x. norm (f x)) S \<le> B" 
    using assms by auto
next
  case False
  define M normf where "M = count_space S" and "normf x = ennreal (norm (f x))" for x

  have normf_B: "finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum normf F \<le> ennreal B" for F
        using assms[THEN ennreal_leI] 
        apply (subst (asm) sum_ennreal[symmetric], simp)
        unfolding normf_def[symmetric] by simp

  have "integral\<^sup>S M g \<le> B" if "simple_function M g" and "g \<le> normf" for g 
  proof -
    define gS where "gS = g ` S"
    have "finite gS"
      using that unfolding gS_def M_def simple_function_count_space by simp
    have "gS \<noteq> {}" unfolding gS_def using False by auto
    define part where "part r = g -` {r} \<inter> S" for r
    have r_finite: "r < \<infinity>" if "r : gS" for r 
      using \<open>g \<le> normf\<close> that unfolding gS_def le_fun_def normf_def apply auto
      using ennreal_less_top neq_top_trans top.not_eq_extremum by blast
    define B' where "B' r = (SUP F:{F. finite F \<and> F\<subseteq>part r}. sum normf F)" for r
    have B'fin: "B' r < \<infinity>" for r
    proof -
      have "B' r \<le> (SUP F:{F. finite F \<and> F\<subseteq>part r}. sum normf F)"
        unfolding B'_def
        by (metis (mono_tags, lifting) SUP_least SUP_upper)
      also have "\<dots> \<le> B"
        using normf_B unfolding part_def
        by (metis (no_types, lifting) Int_subset_iff SUP_least mem_Collect_eq)
      also have "\<dots> < \<infinity>"
        by simp
      finally show ?thesis by simp
    qed
    have sumB': "sum B' gS \<le> ennreal B + \<epsilon>" if "\<epsilon>>0" for \<epsilon>
    proof -
      define N \<epsilon>N where "N = card gS" and "\<epsilon>N = \<epsilon> / N"
      have "N > 0" 
        unfolding N_def using \<open>gS\<noteq>{}\<close> \<open>finite gS\<close>
        by (simp add: card_gt_0_iff)
      from \<epsilon>N_def that have "\<epsilon>N > 0"
        by (simp add: ennreal_of_nat_eq_real_of_nat ennreal_zero_less_divide)
      obtain F where F: "sum normf (F r) + \<epsilon>N \<ge> B' r" and Ffin: "finite (F r)" and Fpartr: "F r \<subseteq> part r" for r
        apply atomize_elim apply (subst all_conj_distrib[symmetric])+ apply (rule choice) apply (rule allI)
        apply (rename_tac r) apply (case_tac "B' r = 0") 
      proof -
        fix r assume "B' r = 0" 
        thus "\<exists>F. B' r \<le> sum normf F + \<epsilon>N \<and> finite F \<and> F \<subseteq> part r" by auto
      next
        fix r :: ennreal
        assume "B' r \<noteq> 0"
        with \<open>\<epsilon>N > 0\<close> B'fin have "B' r - \<epsilon>N < B' r"
          by (metis ennreal_between infinity_ennreal_def le_zero_eq not_le)
        then obtain F where "B' r - \<epsilon>N \<le> sum normf F" and "finite F" and "F \<subseteq> part r"
          apply atomize_elim apply (subst (asm) (2) B'_def)
          by (metis (no_types, lifting) leD le_cases less_SUP_iff mem_Collect_eq)
        thus "\<exists>F. B' r \<le> sum normf F + \<epsilon>N \<and> finite F \<and> F \<subseteq> part r"
          by (metis add.commute ennreal_minus_le_iff)
      qed
      have "sum B' gS \<le> (\<Sum>r\<in>gS. sum normf (F r) + \<epsilon>N)"
        using F by (simp add: sum_mono)
      also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (\<Sum>r\<in>gS. \<epsilon>N)"
        by (simp add: sum.distrib)
      also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (card gS * \<epsilon>N)"
        by auto
      also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + \<epsilon>"
        unfolding \<epsilon>N_def N_def[symmetric] using \<open>N>0\<close> 
        by (simp add: ennreal_times_divide mult.commute mult_divide_eq_ennreal)
      also have "\<dots> = sum normf (UNION gS F) + \<epsilon>" 
        apply (subst sum.UNION_disjoint[symmetric])
        using \<open>finite gS\<close> apply assumption
        using Ffin apply simp
        using Fpartr[unfolded part_def] apply auto[1]
        apply (metis subsetCE vimage_singleton_eq)
        by simp
      also have "\<dots> \<le> B + \<epsilon>"
        apply (rule add_right_mono)
        apply (rule normf_B)
        using \<open>finite gS\<close> Ffin Fpartr unfolding part_def by auto
      finally show ?thesis
        by auto
    qed
    hence sumB': "sum B' gS \<le> B"
      using ennreal_le_epsilon ennreal_less_zero_iff by blast
    obtain B'' where B'': "B' r = ennreal (B'' r)" if "r \<in> gS" for r
      apply atomize_elim apply (rule_tac choice) 
      using B'fin apply auto using less_top_ennreal by blast
    have cases[case_names zero finite infinite]: "P" if "r=0 \<Longrightarrow> P" and "finite (part r) \<Longrightarrow> P"
        and "infinite (part r) \<Longrightarrow> r\<noteq>0 \<Longrightarrow> P" for P r
      using that by metis
    have emeasure_B': "r * emeasure M (part r) \<le> B' r" if "r : gS" for r
    proof (cases rule:cases[of r])
      case zero
      thus ?thesis by simp
    next
      case finite
      have "r * of_nat (card (part r)) = r * (\<Sum>x\<in>part r. 1)" by simp
      also have "\<dots> = (\<Sum>x\<in>part r. r)"
        using mult.commute by auto
      also have "\<dots> = (\<Sum>x\<in>part r. g x)"
        unfolding part_def by auto
      also have "\<dots> \<le> (SUP F:{F. finite F \<and> F\<subseteq>part r}. sum g F)"
        using finite apply auto
        by (simp add: Sup_upper)
      also have "\<dots> \<le> B' r"
        unfolding B'_def
        apply (rule SUP_subset_mono, simp) 
        apply (rule sum_mono) 
        using \<open>g \<le> normf\<close>
        by (simp add: le_fun_def) 
      finally have "r * of_nat (card (part r)) \<le> B' r" by assumption
      thus ?thesis
        unfolding M_def
        apply (subst emeasure_count_space_finite)
        using part_def finite by auto
    next
      case infinite
      from r_finite[OF \<open>r : gS\<close>] obtain r' where r': "r = ennreal r'"
        using ennreal_cases by auto
      with infinite have "r' > 0"
        using ennreal_less_zero_iff not_gr_zero by blast
      obtain N::nat where N:"N > B / r'" and "real N > 0" apply atomize_elim
        using reals_Archimedean2
        by (metis less_trans linorder_neqE_linordered_idom)
      obtain F where "finite F" and "card F = N" and "F \<subseteq> part r"
        apply atomize_elim using infinite
        by (simp add: infinite_arbitrarily_large)
      from \<open>F \<subseteq> part r\<close> have "F \<subseteq> S" unfolding part_def by simp
      have "B < r * N"
        using N unfolding r' ennreal_of_nat_eq_real_of_nat
        apply (subst ennreal_mult[symmetric])
        using ennreal_le_iff2 ennreal_neg infinite(2) r' apply blast
         apply simp
        apply (rule ennreal_lessI)
        using \<open>r' > 0\<close> \<open>real N > 0\<close> apply simp
        using \<open>r' > 0\<close> by (simp add: linordered_field_class.pos_divide_less_eq mult.commute)
      also have "r * N = (\<Sum>x\<in>F. r)"
        using \<open>card F = N\<close> by (simp add: mult.commute)
      also have "(\<Sum>x\<in>F. r) = (\<Sum>x\<in>F. g x)"
        apply (rule sum.cong)
        using \<open>F \<subseteq> part r\<close> using part_def by auto
      also have "(\<Sum>x\<in>F. g x) \<le> (\<Sum>x\<in>F. ennreal (norm (f x)))"
        apply (rule sum_mono) using \<open>g \<le> normf\<close> unfolding normf_def le_fun_def by auto
      also have "(\<Sum>x\<in>F. ennreal (norm (f x))) \<le> B" 
         apply auto using assms(1)[OF \<open>finite F\<close> \<open>F \<subseteq> S\<close>] by (rule ennreal_leI)
      finally have "B < B" by auto
      thus ?thesis by simp
    qed

    have "integral\<^sup>S M g = (\<Sum>r \<in> gS. r * emeasure M (part r))"
      unfolding simple_integral_def gS_def M_def part_def by simp
    also have "\<dots> \<le> (\<Sum>r \<in> gS. B' r)"
      apply (rule sum_mono) using emeasure_B' by auto
    also have "\<dots> \<le> B"
      using sumB' by blast
    finally show ?thesis by assumption
  qed
  hence int_leq_B: "integral\<^sup>N M normf \<le> B"
    unfolding nn_integral_def by (metis (no_types, lifting) SUP_least mem_Collect_eq)
  hence "integral\<^sup>N M normf < \<infinity>"
    using le_less_trans by fastforce
  hence "integrable M f"
    unfolding M_def normf_def by (rule integrableI_bounded[rotated], simp)
  hence f_sum_S: "f abs_summable_on S"
    unfolding abs_summable_on_def M_def by simp
  have "infsetsum (\<lambda>x. norm (f x)) S \<le> B"
    apply (subst ennreal_le_iff[symmetric], simp add: assms)
    apply (subst nn_integral_conv_infsetsum[symmetric])
    using f_sum_S int_leq_B 
    unfolding normf_def M_def by auto
  with f_sum_S
  show "f abs_summable_on S \<and> infsetsum (\<lambda>x. norm (f x)) S \<le> B" by simp
qed

lemma abs_summable_finiteI:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
  shows "f abs_summable_on S"
proof -
  from assms have "sum (\<lambda>x. norm (f x)) {} \<le> B" by blast
  hence "0 \<le> B" by simp
  thus ?thesis 
    using assms by (rule abs_summable_finiteI0[rotated])
qed

lemma infsetsum_finite_sets:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
    and "B \<ge> 0" and "\<And>x. f x \<ge> 0"
  shows "infsetsum f S \<le> B"
  using abs_summable_finiteI0(2)[where f=f and S=S, OF assms(1-2), simplified]
  using assms(3) by auto

lemma abs_summable_finiteI_converse:
  assumes f_sum_S: "f abs_summable_on S"
  defines "B \<equiv> (infsetsum (\<lambda>x. norm (f x)) S)"
  assumes finite_F: "finite F" and FS: "F\<subseteq>S"
  shows "sum (\<lambda>x. norm (f x)) F \<le> B"
proof -
  have "sum (\<lambda>x. norm (f x)) F = infsetsum (\<lambda>x. norm (f x)) F"
    apply (rule infsetsum_finite[symmetric]) by (fact finite_F)
  also have "infsetsum (\<lambda>x. norm (f x)) F \<le> B"
    unfolding B_def 
    apply (rule infsetsum_mono_neutral_left)
    using finite_F apply (rule abs_summable_on_finite)
    using f_sum_S apply (rule abs_summable_on_normI)
    apply (rule order.refl)
    apply (fact FS)
    by (rule norm_ge_zero)
  finally show ?thesis by assumption
qed

lemma abs_summable_countable:
  fixes \<mu> :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes "\<mu> abs_summable_on T"
  shows "countable {x\<in>T. 0 \<noteq> \<mu> x}"
proof -
  define B where "B = infsetsum (\<lambda>x. norm (\<mu> x)) T"
  have \<mu>sum: "sum (\<lambda>x. norm (\<mu> x)) F \<le> B" if "finite F" and "F \<subseteq> T" for F
    unfolding B_def apply (rule abs_summable_finiteI_converse)
    using assms that by auto
  define S where "S i = {x\<in>T. 1/real (Suc i) < norm (\<mu> x)}" for i::nat
  have "\<exists>i. x \<in> S i" if "0 < norm (\<mu> x)" and "x \<in> T" for x
    using that unfolding S_def apply (auto simp del: real_norm_def)
    by (metis inverse_eq_divide not0_implies_Suc of_nat_Suc real_arch_inverse that(1))
  hence union: "{x\<in>T. 0 < norm (\<mu> x)} = (\<Union>i. S i)"
    unfolding S_def by auto
  have finiteS: "finite (S i)" for i
  proof (rule ccontr)
    assume "infinite (S i)"
    then obtain F where F_Si: "F \<subseteq> S i" and cardF: "card F > (Suc i)*B" and finiteF: "finite F"
      by (metis One_nat_def ex_less_of_nat_mult infinite_arbitrarily_large lessI mult.commute mult.left_neutral of_nat_0_less_iff of_nat_1)
    from F_Si have F_T: "F \<subseteq> T" 
      unfolding S_def by blast
    from finiteF \<mu>sum F_T have sumF: "sum (\<lambda>x. norm (\<mu> x)) F \<le> B" by simp
    have "sum (\<lambda>x. norm (\<mu> x)) F \<ge> sum (\<lambda>_. 1/real (Suc i)) F" (is "_ \<ge> \<dots>")
      apply (rule sum_mono)
      using F_Si S_def by auto
    moreover have "\<dots> = real (card F) / (Suc i)"
      by (subst sum_constant_scale, auto)
    moreover have "\<dots> > B"
      using cardF
      by (simp add: linordered_field_class.mult_imp_less_div_pos ordered_field_class.sign_simps)
    ultimately have "sum (\<lambda>x. norm (\<mu> x)) F > B"
      by linarith 
    with sumF show False by simp
  qed
  have "countable (\<Union>i. S i)"
    apply (rule countable_UN, simp)
    apply (rule countable_finite)
    using finiteS by simp
  hence "countable {x\<in>T. 0 < norm (\<mu> x)}"
    unfolding union by simp
  thus ?thesis
    by simp
qed


lemma infsetsum_cnj[simp]: "infsetsum (\<lambda>x. cnj (f x)) M = cnj (infsetsum f M)"
  unfolding infsetsum_def by (rule integral_cnj)

lemma infsetsum_Re: 
  assumes "f abs_summable_on M"
  shows "infsetsum (\<lambda>x. Re (f x)) M = Re (infsetsum f M)"
  unfolding infsetsum_def apply (rule integral_Re)
  using assms by (simp add: abs_summable_on_def)
  
lemma infsetsum_Im: 
  assumes "f abs_summable_on M"
  shows "infsetsum (\<lambda>x. Im (f x)) M = Im (infsetsum f M)"
  unfolding infsetsum_def apply (rule integral_Im)
  using assms by (simp add: abs_summable_on_def)

lemma infsetsum_mono_complex:
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f_sum: "f abs_summable_on A" and g_sum: "g abs_summable_on A"
  assumes "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows   "infsetsum f A \<le> infsetsum g A"
proof -
  have "infsetsum f A = Complex (Re (infsetsum f A)) (Im (infsetsum f A))" by auto
  also have "Re (infsetsum f A) = infsetsum (\<lambda>x. Re (f x)) A"
    unfolding infsetsum_def apply (rule integral_Re[symmetric])
    using assms by (simp add: abs_summable_on_def)
  also have "Im (infsetsum f A) = infsetsum (\<lambda>x. Im (f x)) A"
    using f_sum by (rule infsetsum_Im[symmetric])
  finally have fsplit: "infsetsum f A = Complex (\<Sum>\<^sub>ax\<in>A. Re (f x)) (\<Sum>\<^sub>ax\<in>A. Im (f x))" by assumption

  have "infsetsum g A = Complex (Re (infsetsum g A)) (Im (infsetsum g A))" by auto
  also have "Re (infsetsum g A) = infsetsum (\<lambda>x. Re (g x)) A"
    using g_sum by (rule infsetsum_Re[symmetric])
  also have "Im (infsetsum g A) = infsetsum (\<lambda>x. Im (g x)) A "
    using g_sum by (rule infsetsum_Im[symmetric])
  finally have gsplit: "infsetsum g A = Complex (\<Sum>\<^sub>ax\<in>A. Re (g x)) (\<Sum>\<^sub>ax\<in>A. Im (g x))" by assumption

  have Re_leq: "Re (f x) \<le> Re (g x)" if "x\<in>A" for x
    using that assms unfolding less_eq_complex_def by simp
  have Im_eq: "Im (f x) = Im (g x)" if "x\<in>A" for x
    using that assms 
    unfolding less_eq_complex_def by simp

  have Refsum: "(\<lambda>x. Re (f x)) abs_summable_on A"
    using assms(1) apply (rule abs_summable_on_comparison_test[where g=f])
    using abs_Re_le_cmod by auto
  have Regsum: "(\<lambda>x. Re (g x)) abs_summable_on A"
    using assms(2) apply (rule abs_summable_on_comparison_test[where g=g])
    using abs_Re_le_cmod by auto
    
  show "infsetsum f A \<le> infsetsum g A"
    unfolding fsplit gsplit
    apply (rule less_eq_complexI; simp)
    using Refsum Regsum Re_leq apply (rule infsetsum_mono)
    using Im_eq by auto
qed

lemma infsetsum_subset_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f abs_summable_on B" and "A \<subseteq> B" and "\<And>x. x\<notin>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A \<le> infsetsum f B"
proof -
  have fBA: "f abs_summable_on B - A"
    by (meson Diff_subset abs_summable_on_subset assms(1))

  have "0 = infsetsum (\<lambda>_.0) (B-A)" by auto
  also have "... \<le> infsetsum f (B - A)"
    apply (rule infsetsum_mono_complex)
    using assms fBA by auto
  also have "... = infsetsum f B - infsetsum f A"
    apply (rule infsetsum_Diff)
    using assms by auto
  finally show ?thesis by auto
qed

lemma infsetsum_subset_real:
  fixes f :: "'a \<Rightarrow> real"
  assumes "f abs_summable_on B" and "A \<subseteq> B" and "\<And>x. x\<notin>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A \<le> infsetsum f B"
proof -
  have fBA: "f abs_summable_on B - A"
    by (meson Diff_subset abs_summable_on_subset assms(1))

  have "0 = infsetsum (\<lambda>_.0) (B-A)" by auto
  also have "... \<le> infsetsum f (B - A)"
    apply (rule infsetsum_mono)
    using assms fBA by auto
  also have "... = infsetsum f B - infsetsum f A"
    apply (rule infsetsum_Diff)
    using assms by auto
  finally show ?thesis by auto
qed

lemma abs_summable_product:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra,banach,second_countable_topology}"
  assumes x2_sum: "(\<lambda>i. (x i) * (x i)) abs_summable_on A"
  and y2_sum: "(\<lambda>i. (y i) * (y i)) abs_summable_on A"
  shows "(\<lambda>i. x i * y i) abs_summable_on A"
proof (rule abs_summable_finiteI)
  have aux: "a\<le>a' \<Longrightarrow> b\<le>b' \<Longrightarrow> a+b \<le> a'+b'" for a b a' b' :: real by simp
  fix F assume "finite F" and "F \<subseteq> A"
  define B :: real where "B = (\<Sum>\<^sub>ai\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>A. norm (y i * y i))"
  have "norm (x i * y i) \<le> norm (x i * x i) + norm (y i * y i)" for i
    unfolding norm_mult
    by (smt mult_left_mono mult_nonneg_nonneg mult_right_mono norm_ge_zero)
  hence "(\<Sum>i\<in>F. norm (x i * y i)) \<le> (\<Sum>i\<in>F. norm (x i * x i) + norm (y i * y i))"
    by (simp add: sum_mono)
  also have "\<dots> = (\<Sum>i\<in>F. norm (x i * x i)) + (\<Sum>i\<in>F. norm (y i * y i))"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>\<^sub>ai\<in>F. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>F. norm (y i * y i))" 
    apply (subst infsetsum_finite[OF \<open>finite F\<close>])+ by rule
  also have "\<dots> \<le> (\<Sum>\<^sub>ai\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>A. norm (y i * y i))" 
    apply (rule aux)
     apply (rule infsetsum_mono_neutral_left)
    using \<open>finite F\<close> apply (rule abs_summable_on_finite)
    using x2_sum apply (rule abs_summable_on_normI)
       apply (rule order.refl)
      apply (fact \<open>F \<subseteq> A\<close>)
     apply (rule norm_ge_zero)
    apply (rule infsetsum_mono_neutral_left)
    using \<open>finite F\<close> apply (rule abs_summable_on_finite)
    using y2_sum apply (rule abs_summable_on_normI)
      apply (rule order.refl)
     apply (fact \<open>F \<subseteq> A\<close>)
    by (rule norm_ge_zero)
  also have "\<dots> = B"
    unfolding B_def by simp
  finally show "(\<Sum>i\<in>F. norm (x i * y i)) \<le> B" by assumption
qed

lemma abs_summable_cnj_iff[simp]:
  "(\<lambda>i. cnj (f i)) abs_summable_on A \<longleftrightarrow> f abs_summable_on A"
  apply (subst (1) abs_summable_on_norm_iff[symmetric])
  apply (subst (2) abs_summable_on_norm_iff[symmetric])
  by simp

lemma ennreal_Sup:
  assumes "bdd_above A" and nonempty: "A\<noteq>{}"
  shows "ennreal (Sup A) = Sup (ennreal ` A)"
proof (rule Sup_eqI[symmetric])
  fix y assume "y \<in> ennreal ` A" thus "y \<le> ennreal (Sup A)"
    using assms cSup_upper ennreal_leI by auto
next
  fix y assume asm: "\<And>z. z \<in> ennreal ` A \<Longrightarrow> z \<le> y"
  show "ennreal (Sup A) \<le> y"
  proof (cases y)
    case (real r)
    with asm show ?thesis 
      apply auto
      apply (rule cSup_least)
      using nonempty apply auto
      using ennreal_le_iff by blast
  next
    case top
    thus ?thesis by auto
  qed
qed

lemma infsetsum_nonneg_is_SUPREMUM_ennreal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
  assumes fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ennreal (infsetsum f A) = SUPREMUM {F. finite F \<and> F \<subseteq> A} (\<lambda>F. ennreal (sum f F))"
proof -
  have sum_F_A: "sum f F \<le> infsetsum f A" if "F : {F. finite F \<and> F \<subseteq> A}" for F
  proof -
    from that have "finite F" and "F \<subseteq> A" by auto
    from \<open>finite F\<close> have "sum f F = infsetsum f F" by auto
    also have "\<dots> \<le> infsetsum f A"
      apply (rule infsetsum_mono_neutral_left)
      using fnn summable \<open>F\<subseteq>A\<close> \<open>finite F\<close> by auto
    finally show ?thesis by assumption
  qed
  hence geq: "ennreal (infsetsum f A) \<ge> SUPREMUM {F. finite F \<and> F \<subseteq> A} (\<lambda>F. ennreal (sum f F))"
    by (meson SUP_least ennreal_leI)

  define fe where "fe x = ennreal (f x)" for x

  have sum_f_int: "infsetsum f A = \<integral>\<^sup>+ x. fe x \<partial>(count_space A)"
    unfolding infsetsum_def fe_def
    apply (rule nn_integral_eq_integral[symmetric])
    using assms by (simp_all add: abs_summable_on_def AE_count_space)
  also have "\<dots> = (SUP g : {g. finite (g`A) \<and> g \<le> fe}. integral\<^sup>S (count_space A) g)"
    unfolding nn_integral_def simple_function_count_space by simp
  also have "\<dots> \<le> SUPREMUM {F. finite F \<and> F \<subseteq> A} (\<lambda>F. ennreal (sum f F))"
  proof (rule Sup_least)
    fix x assume "x \<in> integral\<^sup>S (count_space A) ` {g. finite (g ` A) \<and> g \<le> fe}"
    then obtain g where xg: "x = integral\<^sup>S (count_space A) g" and fin_gA: "finite (g`A)" and g_fe: "g \<le> fe" by auto
    define F where "F = {z:A. g z \<noteq> 0}"
    hence "F \<subseteq> A" by simp

    have fin: "finite {z:A. g z = t}" if "t \<noteq> 0" for t
    proof (rule ccontr)
      assume inf: "infinite {z:A. g z = t}"
      hence tgA: "t \<in> g ` A"
        by (metis (mono_tags, lifting) image_eqI not_finite_existsD)
      have "x = (\<Sum>x \<in> g ` A. x * emeasure (count_space A) (g -` {x} \<inter> A))"
        unfolding xg simple_integral_def space_count_space by simp
      also have "\<dots> \<ge> (\<Sum>x \<in> {t}. x * emeasure (count_space A) (g -` {x} \<inter> A))" (is "_ \<ge> \<dots>")
        apply (rule sum_mono2)
        using fin_gA inf tgA by auto
      also have "\<dots> = t * emeasure (count_space A) (g -` {t} \<inter> A)"
        by auto
      also have "\<dots> = t * \<infinity>"
        apply (subst emeasure_count_space_infinite)
        using inf apply auto
        by (smt Collect_cong Int_def vimage_singleton_eq) 
      also have "\<dots> = \<infinity>" using \<open>t \<noteq> 0\<close>
        by (simp add: ennreal_mult_eq_top_iff)
      finally have x_inf: "x = \<infinity>"
        using neq_top_trans by auto

      have "x = integral\<^sup>S (count_space A) g" by (fact xg)
      also have "\<dots> = integral\<^sup>N (count_space A) g"
        by (simp add: fin_gA nn_integral_eq_simple_integral)
      also have "\<dots> \<le> integral\<^sup>N (count_space A) fe"
        using g_fe
        by (simp add: le_funD nn_integral_mono)
      also have "\<dots> < \<infinity>"
        by (metis sum_f_int ennreal_less_top infinity_ennreal_def) 
      finally have x_fin: "x < \<infinity>" by simp

      from x_inf x_fin show False by simp
    qed
    have "finite F"
    proof -
      have F: "F = (\<Union>t\<in>g`A-{0}. {z\<in>A. g z = t})"
        unfolding F_def by auto
      show "finite F"
        unfolding F using fin_gA fin by auto
    qed

    have "x = integral\<^sup>N (count_space A) g"
      unfolding xg
      by (simp add: fin_gA nn_integral_eq_simple_integral)
    also have "\<dots> = set_nn_integral (count_space UNIV) A g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = set_nn_integral (count_space UNIV) F g"
      unfolding F_def indicator_def apply auto
      by (smt mult.right_neutral mult_zero_right nn_integral_cong) 
    also have "\<dots> = integral\<^sup>N (count_space F) g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = sum g F" 
      using \<open>finite F\<close> by (rule nn_integral_count_space_finite)
    also have "sum g F \<le> sum fe F"
      apply (rule sum_mono) using g_fe unfolding le_fun_def by simp
    also have "\<dots> \<le> SUPREMUM {F. finite F \<and> F \<subseteq> A} (sum fe)"
      using \<open>finite F\<close> \<open>F\<subseteq>A\<close>
      by (simp add: SUP_upper)
    also have "\<dots> = SUPREMUM {F. finite F \<and> F \<subseteq> A} (\<lambda>F. ennreal (sum f F))"
      apply (rule SUP_cong[OF refl]) unfolding fe_def apply auto
      by (metis fnn subsetCE sum_ennreal)
    finally show "x \<le> \<dots>" by simp
  qed
  finally have leq: "ennreal (infsetsum f A) \<le> SUPREMUM {F. finite F \<and> F \<subseteq> A} (\<lambda>F. (ennreal (sum f F)))"
    by assumption

  from leq geq show ?thesis by simp
qed


lemma infsetsum_nonneg_is_SUPREMUM_ereal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
  assumes fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ereal (infsetsum f A) = SUPREMUM {F. finite F \<and> F \<subseteq> A} (\<lambda>F. ereal (sum f F))"
proof -
  have "ereal (infsetsum f A) = enn2ereal (ennreal (infsetsum f A))"
    by (simp add: fnn infsetsum_nonneg)
  also have "\<dots> = enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F))"
    apply (subst infsetsum_nonneg_is_SUPREMUM_ennreal)
    using assms by auto
  also have "\<dots> = SUPREMUM {F. finite F \<and> F \<subseteq> A} (\<lambda>F. ereal (sum f F))"
    apply (simp add: image_def Sup_ennreal.rep_eq)
    apply (subst max_absorb2)
     apply (metis (mono_tags, lifting) Sup_upper empty_subsetI ennreal_0 finite.emptyI
        mem_Collect_eq sum.empty zero_ennreal.rep_eq)
    by (metis (mono_tags, lifting) enn2ereal_ennreal fnn in_mono sum_nonneg)
  finally show ?thesis
    by simp
qed

lemma infsetsum_nonneg_is_SUPREMUM:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
  assumes fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A = SUPREMUM {F. finite F \<and> F \<subseteq> A} (sum f)"
proof -
  have "ereal (infsetsum f A) = SUPREMUM {F. finite F \<and> F \<subseteq> A} (\<lambda>F. ereal (sum f F))"
    using assms by (rule infsetsum_nonneg_is_SUPREMUM_ereal)
  also have "\<dots> = ereal (SUPREMUM {F. finite F \<and> F \<subseteq> A} (sum f))"
    apply (subst ereal_SUP)
    using calculation by fastforce+
  finally show ?thesis by simp
qed

lemma infsetsum_geq0_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f abs_summable_on M"
  assumes fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsetsum f M \<ge> 0" (is "?lhs \<ge> _")
proof -
  have "?lhs \<ge> infsetsum (\<lambda>x. 0) M" (is "_ \<ge> \<dots>")
    apply (rule infsetsum_mono_complex)
    using assms by auto
  also have "\<dots> = 0"
    by auto
  finally show ?thesis by assumption
qed

lemma infsetsum_cmod:
  assumes "f abs_summable_on M"
  assumes fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsetsum (\<lambda>x. cmod (f x)) M = cmod (infsetsum f M)"
proof -
  have nn: "infsetsum f M \<ge> 0" 
    using assms by (rule infsetsum_geq0_complex) 
  have "infsetsum (\<lambda>x. cmod (f x)) M = infsetsum (\<lambda>x. Re (f x)) M"
    using fnn cmod_eq_Re less_eq_complex_def by auto
  also have "\<dots> = Re (infsetsum f M)"
    using assms(1) infsetsum_Re by blast
  also have "\<dots> = cmod (infsetsum f M)" using nn cmod_eq_Re less_eq_complex_def by auto
  finally show ?thesis by assumption
qed

theorem infsetsum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes summable: "f abs_summable_on (Sigma A B)"
  shows   "infsetsum f (Sigma A B) = infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) (B x)) A"
proof -
  from summable have countable_Sigma: "countable {x \<in> Sigma A B. 0 \<noteq> f x}"
    by (rule abs_summable_countable)
  define A' where "A' = fst ` {x \<in> Sigma A B. 0 \<noteq> f x}"
  have countA': "countable A'"
    using countable_Sigma unfolding A'_def by auto

  define B' where "B' a = snd ` ({x \<in> Sigma A B. 0 \<noteq> f x} \<inter> {(a,b) | b. True})" for a
  have countB': "countable (B' a)" for a
    using countable_Sigma unfolding B'_def by auto

  have Sigma_eq: "x \<in> Sigma A B \<longleftrightarrow> x \<in> Sigma A' B'" if "f x \<noteq> 0" for x
    unfolding A'_def B'_def Sigma_def apply auto
    using that by force

  have Sigma'_smaller: "Sigma A' B' \<subseteq> Sigma A B"
    unfolding A'_def B'_def by auto
  with summable have summable': "f abs_summable_on Sigma A' B'"
    using abs_summable_on_subset by blast

  have A'_smaller: "A' \<subseteq> A"
    unfolding A'_def by auto
  have B'_smaller: "B' a \<subseteq> B a" for a
    unfolding B'_def by auto

  have "infsetsum f (Sigma A B) = infsetsum f (Sigma A' B')"
    apply (rule infsetsum_cong_neutral) using Sigma_eq by auto
  also from countA' countB' summable' have "\<dots> = (\<Sum>\<^sub>aa\<in>A'. \<Sum>\<^sub>ab\<in>B' a. f (a, b))"
    by (rule infsetsum_Sigma)
  also have "\<dots> = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B' a. f (a, b))" (is "_ = (\<Sum>\<^sub>aa\<in>A. ?inner a)" is "_ = ?rhs")
    apply (rule infsetsum_cong_neutral)
    using A'_smaller apply auto
    unfolding A'_def B'_def Sigma_def apply auto
    by (smt Int_Collect fst_conv image_iff infsetsum_all_0)
  also have "?inner a = (\<Sum>\<^sub>ab\<in>B a. f (a, b))" if "a\<in>A" for a
    apply (rule infsetsum_cong_neutral)
    using that unfolding A'_def B'_def Sigma_def apply auto
    by (smt Int_Collect image_iff mem_Collect_eq snd_conv)
  hence "?rhs = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B a. f (a, b))"
    by (rule infsetsum_cong, auto)
  finally show ?thesis 
    by simp
qed

lemma infsetsum_Sigma':
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on (Sigma A B)"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) (B x)) A = infsetsum (\<lambda>(x,y). f x y) (Sigma A B)"
  using assms by (subst infsetsum_Sigma) auto

lemma infsetsum_Times:
  fixes A :: "'a set" and B :: "'b set"
  assumes summable: "f abs_summable_on (A \<times> B)"
  shows   "infsetsum f (A \<times> B) = infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) B) A"
  using assms by (subst infsetsum_Sigma) auto

lemma infsetsum_Times':
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on (A \<times> B)"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>(x,y). f x y) (A \<times> B)"
  using assms by (subst infsetsum_Times) auto

lemma infsetsum_swap:
  fixes A :: "'a set" and B :: "'b set"
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {banach, second_countable_topology}"
  assumes summable: "(\<lambda>(x,y). f x y) abs_summable_on A \<times> B"
  shows   "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
proof -
  from summable have summable': "(\<lambda>(x,y). f y x) abs_summable_on B \<times> A"
    by (subst abs_summable_on_Times_swap) auto
  have bij: "bij_betw (\<lambda>(x, y). (y, x)) (B \<times> A) (A \<times> B)"
    by (auto simp: bij_betw_def inj_on_def)
  have "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>(x,y). f x y) (A \<times> B)"
    using summable by (subst infsetsum_Times) auto
  also have "\<dots> = infsetsum (\<lambda>(x,y). f y x) (B \<times> A)"
    by (subst infsetsum_reindex_bij_betw[OF bij, of "\<lambda>(x,y). f x y", symmetric])
       (simp_all add: case_prod_unfold)
  also have "\<dots> = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
    using summable' by (subst infsetsum_Times) auto
  finally show ?thesis .
qed

(* TODO move *)
lemma cauchy_filter_metricI:
  fixes F :: "'a::metric_space filter"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)"
  shows "cauchy_filter F"
proof (unfold cauchy_filter_def le_filter_def, auto)
  fix P :: "'a \<times> 'a \<Rightarrow> bool"
  assume "eventually P uniformity"
  then obtain e where e: "e > 0" and P: "dist x y < e \<Longrightarrow> P (x, y)" for x y
    unfolding eventually_uniformity_metric by auto
  from assms e obtain P' where evP': "eventually P' F" and P'_dist: "P' x \<and> P' y \<Longrightarrow> dist x y < e" for x y
    apply atomize_elim by auto
  from evP' P'_dist P
  show "eventually P (F \<times>\<^sub>F F)"
    unfolding eventually_uniformity_metric eventually_prod_filter eventually_filtermap by metis
qed

(* TODO move *)
lemma cauchy_filter_metric_filtermapI:
  fixes F :: "'a filter" and f :: "'a\<Rightarrow>'b::metric_space"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist (f x) (f y) < e)"
  shows "cauchy_filter (filtermap f F)"
proof (rule cauchy_filter_metricI)
  fix e :: real assume e: "e > 0"
  with assms obtain P where evP: "eventually P F" and dist: "P x \<and> P y \<Longrightarrow> dist (f x) (f y) < e" for x y
    by atomize_elim auto
  define P' where "P' y = (\<exists>x. P x \<and> y = f x)" for y
  have "eventually P' (filtermap f F)"
    unfolding eventually_filtermap P'_def 
    using evP
    by (smt eventually_mono) 
  moreover have "P' x \<and> P' y \<longrightarrow> dist x y < e" for x y
    unfolding P'_def using dist by metis
  ultimately show "\<exists>P. eventually P (filtermap f F) \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)"
    by auto
qed


lemma abs_summable_infsetsum'_converges:
  fixes f :: "'a\<Rightarrow>'b::{second_countable_topology,banach}" and A :: "'a set"
  assumes "f abs_summable_on A"
  shows "infsetsum'_converges f A"
proof -
  define F where "F = filtermap (sum f) (finite_subsets_at_top A)"
  have F_not_bot: "F \<noteq> bot"
    unfolding F_def filtermap_bot_iff by simp
  have cauchy: "cauchy_filter F"
    unfolding F_def 
  proof (rule cauchy_filter_metric_filtermapI)
    fix e :: real assume e: "e>0"
    have is_SUP: "ereal (\<Sum>\<^sub>ax\<in>A. norm (f x)) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x)))"
      apply (rule infsetsum_nonneg_is_SUPREMUM_ereal) using assms by auto
    obtain F0 where "F0\<in>{F. finite F \<and> F \<subseteq> A}" and "ereal (\<Sum>x\<in>F0. norm (f x)) > ereal (\<Sum>\<^sub>ax\<in>A. norm (f x)) - ereal e"
      apply atomize_elim unfolding is_SUP Bex_def[symmetric]
      apply (subst less_SUP_iff[symmetric]) using e
      by (metis diff_strict_left_mono diff_zero ereal_minus(1) is_SUP less_ereal.simps(1)) 
    hence [simp]: "finite F0" and [simp]: "F0 \<subseteq> A" 
      and sum_diff: "sum (\<lambda>x. norm (f x)) F0 > infsetsum (\<lambda>x. norm (f x)) A - e"
      by auto
    define P where "P F \<longleftrightarrow> finite F \<and> F \<supseteq> F0 \<and> F \<subseteq> A" for F
    have "dist (sum f F1) (sum f F2) < e" if "P F1" and "P F2" for F1 F2
    proof -
      from that(1) have "finite F1" and "F1 \<supseteq> F0" and "F1 \<subseteq> A" unfolding P_def by auto
      from that(2) have "finite F2" and "F2 \<supseteq> F0" and "F2 \<subseteq> A" unfolding P_def by auto
      have "dist (sum f F1) (sum f F2) = norm (sum f (F1-F2) - sum f (F2-F1))"
        unfolding dist_norm
        by (smt \<open>finite F1\<close> \<open>finite F2\<close> add_diff_cancel_left' add_diff_cancel_right' ordered_field_class.sign_simps(12) sum.Int_Diff sum.union_diff2 sum.union_inter) 
      also have "\<dots> \<le> sum (\<lambda>x. norm (f x)) (F1-F2) + sum (\<lambda>x. norm (f x)) (F2-F1)"
        by (smt norm_triangle_ineq4 sum_norm_le)
      also have "\<dots> = infsetsum (\<lambda>x. norm (f x)) (F1-F2) + infsetsum (\<lambda>x. norm (f x)) (F2-F1)"
        by (simp add: \<open>finite F1\<close> \<open>finite F2\<close>)
      also have "\<dots> = infsetsum (\<lambda>x. norm (f x)) ((F1-F2)\<union>(F2-F1))"
        apply (rule infsetsum_Un_disjoint[symmetric])
            apply (simp_all add: \<open>finite F1\<close> \<open>finite F2\<close>)
        by blast
      also have "\<dots> \<le> infsetsum (\<lambda>x. norm (f x)) (A-F0)"
        apply (rule infsetsum_mono_neutral_left)
            apply (simp add: \<open>finite F1\<close> \<open>finite F2\<close>)
           using abs_summable_on_subset assms apply fastforce
          using \<open>F1 \<supseteq> F0\<close> \<open>F2 \<supseteq> F0\<close> \<open>F1 \<subseteq> A\<close> \<open>F2 \<subseteq> A\<close> by auto
      also have "\<dots> = infsetsum (\<lambda>x. norm (f x)) A - infsetsum (\<lambda>x. norm (f x)) F0"
        by (simp add: assms infsetsum_Diff)
      also have "\<dots> < e"
        using local.sum_diff by auto
      finally show "dist (sum f F1) (sum f F2) < e" by assumption
    qed
    moreover have "eventually P (finite_subsets_at_top A)"
      unfolding P_def eventually_finite_subsets_at_top apply (rule exI[of _ F0]) by simp
    ultimately show "\<exists>P. eventually P (finite_subsets_at_top A) \<and> (\<forall>F1 F2. P F1 \<and> P F2 \<longrightarrow> dist (sum f F1) (sum f F2) < e)"
      by auto
  qed
  from complete_UNIV have "F\<le>principal UNIV \<Longrightarrow> F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> (\<exists>x. F \<le> nhds x)"
    unfolding complete_uniform
    by auto
  then obtain x where Fx: "F \<le> nhds x"
    apply atomize_elim using cauchy F_not_bot by simp
  hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    unfolding F_def
    by (simp add: filterlim_def)
  thus ?thesis
    unfolding infsetsum'_converges_def by auto
qed

(* Limits.tendsto_add_const_iff is the same but with a more restrictive sort *)
lemma tendsto_add_const_iff:
  "((\<lambda>x. c + f x :: 'a::topological_group_add) \<longlongrightarrow> c + d) F \<longleftrightarrow> (f \<longlongrightarrow> d) F"
  using tendsto_add[OF tendsto_const[of c], of f d]
    and tendsto_add[OF tendsto_const[of "-c"], of "\<lambda>x. c + f x" "c + d"] by auto

lemma infsetsum'_converges_cofin_subset:
  fixes f :: "'a \<Rightarrow> 'b::topological_ab_group_add"
  assumes "infsetsum'_converges f A" and [simp]: "finite F"
  shows "infsetsum'_converges f (A-F)"
proof -
  from assms(1) obtain x where lim_f: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    unfolding infsetsum'_converges_def by auto
  define F' where "F' = F\<inter>A"
  with assms have "finite F'" and "A-F = A-F'"
    by auto
  have "filtermap ((\<union>)F') (finite_subsets_at_top (A-F))
      \<le> finite_subsets_at_top A"
  proof (rule filter_leI)
    fix P assume "eventually P (finite_subsets_at_top A)"
    then obtain X where [simp]: "finite X" and XA: "X \<subseteq> A" and P: "\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P Y"
      unfolding eventually_finite_subsets_at_top by auto
    define X' where "X' = X-F"
    hence [simp]: "finite X'" and [simp]: "X' \<subseteq> A-F"
      using XA by auto
    hence "finite Y \<and> X' \<subseteq> Y \<and> Y \<subseteq> A - F \<longrightarrow> P (F' \<union> Y)" for Y
      using P XA unfolding X'_def using F'_def \<open>finite F'\<close> by blast
    thus "eventually P (filtermap ((\<union>) F') (finite_subsets_at_top (A - F)))"
      unfolding eventually_filtermap eventually_finite_subsets_at_top
      by (rule_tac x=X' in exI, simp)
  qed

  with lim_f have "(sum f \<longlongrightarrow> x) (filtermap ((\<union>)F') (finite_subsets_at_top (A-F)))"
    using tendsto_mono by blast

  hence "((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A-F))"
    apply (subst (asm) tendsto_compose_filtermap[symmetric])
    unfolding o_def by simp

  hence "((\<lambda>G. sum f F' + sum f G) \<longlongrightarrow> x) (finite_subsets_at_top (A-F))"
    apply (rule tendsto_cong[THEN iffD1, rotated])
    unfolding eventually_finite_subsets_at_top
    apply (rule exI[where x="{}"], simp)
    by (metis Diff_disjoint Int_Diff \<open>A - F = A - F'\<close> \<open>finite F'\<close> inf.orderE sum.union_disjoint)

  hence "((\<lambda>G. sum f F' + sum f G) \<longlongrightarrow> sum f F' + (x-sum f F')) (finite_subsets_at_top (A-F))"
    by simp
  
  hence "(sum f \<longlongrightarrow> x - sum f F') (finite_subsets_at_top (A-F))"
    apply (subst (asm) tendsto_add_const_iff) by simp

  thus "infsetsum'_converges f (A - F)"
    unfolding infsetsum'_converges_def by auto
qed

lemma finite_subsets_at_top_inter: 
  assumes "A\<subseteq>B"
  shows "filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B) \<le> finite_subsets_at_top A"
  apply (rule filter_leI)
  unfolding eventually_filtermap
  unfolding eventually_finite_subsets_at_top
  by (metis Int_subset_iff assms finite_Int inf_le2 subset_trans)
  
lemma finite_subsets_at_top_minus: 
  assumes "A\<subseteq>B"
  shows "finite_subsets_at_top (B - A) \<le> filtermap (\<lambda>F. F - A) (finite_subsets_at_top B)"
proof (rule filter_leI)
  fix P assume "eventually P (filtermap (\<lambda>F. F - A) (finite_subsets_at_top B))"
  then obtain X where "finite X" and "X \<subseteq> B" 
    and P: "finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> B \<longrightarrow> P (Y - A)" for Y
    unfolding eventually_filtermap eventually_finite_subsets_at_top by auto

  hence "finite (X-A)" and "X-A \<subseteq> B - A"
    by auto
  moreover have "finite Y \<and> X-A \<subseteq> Y \<and> Y \<subseteq> B - A \<longrightarrow> P Y" for Y
    using P[where Y="Y\<union>X"] \<open>finite X\<close> \<open>X \<subseteq> B\<close>
    by (metis Diff_subset Int_Diff Un_Diff finite_Un inf.orderE le_sup_iff sup.orderE sup_ge2)
  ultimately show "eventually P (finite_subsets_at_top (B - A))"
    unfolding eventually_finite_subsets_at_top by meson
qed



lemma 
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,t2_space}"
  assumes "\<And>x. x\<in>(A-B)\<union>(B-A) \<Longrightarrow> f x = 0"
  shows infsetsum'_subset_zero: "infsetsum' f A = infsetsum' f B"
    and infsetsum'_converges_subset_zero: "infsetsum'_converges f A = infsetsum'_converges f B"
proof -
  have convB: "infsetsum'_converges f B" and eq: "infsetsum' f A = infsetsum' f B"
    if convA: "infsetsum'_converges f A" and f0: "\<And>x. x\<in>(A-B)\<union>(B-A) \<Longrightarrow> f x = 0" for A B
  proof -
    define D where "D = (A-B)"
    define D' where "D' = B-A"

    from convA obtain x where limA: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
      using infsetsum'_converges_def by blast
    hence "((\<lambda>F. sum f (F-D)) \<longlongrightarrow> x) (finite_subsets_at_top A)"
      apply (rule tendsto_cong[THEN iffD1, rotated])
      apply (rule eventually_finite_subsets_at_top_weakI)
      using f0 D_def by (simp add: subset_iff sum.mono_neutral_cong_right)
    hence "(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F-D) (finite_subsets_at_top A))"
      apply (rewrite at "(\<lambda>F. sum f (F-D))" in asm to "sum f o (\<lambda>F. F-D)" DEADID.rel_mono_strong)
       apply (simp add: o_def inf_assoc)
      by (subst (asm) tendsto_compose_filtermap)
    hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top (A-D))"
      apply (rule tendsto_mono[rotated])
      apply (rule finite_subsets_at_top_minus) 
      (* using finite_subsets_at_top_minus[where A=D and B=A] *)
      unfolding D_def by simp
    hence "(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F \<inter> (A - D)) (finite_subsets_at_top B))"
      apply (rule tendsto_mono[rotated])
      apply (rule finite_subsets_at_top_inter[where B=B and A="A-D"])
      unfolding D_def by auto
    hence "((\<lambda>F. sum f (F \<inter> (A - D))) \<longlongrightarrow> x) (finite_subsets_at_top B)"
      apply (subst (asm) tendsto_compose_filtermap[symmetric])
      by (simp add: o_def inf_assoc)
    hence limB: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top B)"
      apply (rule tendsto_cong[THEN iffD1, rotated])
      apply (rule eventually_finite_subsets_at_top_weakI)
      apply (rule sum.mono_neutral_cong)
      using f0 unfolding D_def by auto

    thus "infsetsum'_converges f B"
      unfolding infsetsum'_converges_def by auto
    thus "infsetsum' f A = infsetsum' f B"
      unfolding infsetsum'_def apply (simp add: convA)
      using limA limB
      using finite_subsets_at_top_neq_bot tendsto_Lim by blast 
  qed
  with assms show "infsetsum'_converges f A = infsetsum'_converges f B"
    by (metis Un_commute)
  thus "infsetsum' f A = infsetsum' f B"
    using assms convB eq
    by (metis infsetsum'_def)
qed

lemma
  fixes f :: "'a \<Rightarrow> 'b::{topological_ab_group_add,t2_space}"
  assumes "infsetsum'_converges f B" and "infsetsum'_converges f A" and AB: "A \<subseteq> B"
  shows infsetsum'_Diff: "infsetsum' f (B - A) = infsetsum' f B - infsetsum' f A"
    and infsetsum'_converges_Diff: "infsetsum'_converges f (B-A)"
proof -
  define limA limB where "limA = infsetsum' f A" and "limB = infsetsum' f B"
  from assms(1) have limB: "(sum f \<longlongrightarrow> limB) (finite_subsets_at_top B)"
    unfolding infsetsum'_converges_def infsetsum'_def limB_def
    by (auto simp: tendsto_Lim)
  from assms(2) have limA: "(sum f \<longlongrightarrow> limA) (finite_subsets_at_top A)"
    unfolding infsetsum'_converges_def infsetsum'_def limA_def
    by (auto simp: tendsto_Lim)


  have "((\<lambda>F. sum f (F\<inter>A)) \<longlongrightarrow> limA) (finite_subsets_at_top B)"
    apply (rewrite asm_rl[of "(\<lambda>F. sum f (F\<inter>A)) = sum f o (\<lambda>F. F\<inter>A)"])
     apply (simp add: o_def)
    apply (subst tendsto_compose_filtermap)
    using finite_subsets_at_top_inter[OF AB] limA by (rule tendsto_mono)

  with limB have "((\<lambda>F. sum f F - sum f (F\<inter>A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)"
    using tendsto_diff by blast

  hence "((\<lambda>F. sum f (F-A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)"
    apply (rule tendsto_cong[THEN iffD1, rotated])
    apply (rule eventually_finite_subsets_at_top_weakI)
    by (metis add_diff_cancel_left' sum.Int_Diff)

  hence "(sum f \<longlongrightarrow> limB - limA) (filtermap (\<lambda>F. F-A) (finite_subsets_at_top B))"
    by (subst tendsto_compose_filtermap[symmetric], simp add: o_def)

  hence limBA: "(sum f \<longlongrightarrow> limB - limA) (finite_subsets_at_top (B-A))"
    using finite_subsets_at_top_minus[OF AB] by (rule tendsto_mono[rotated])

  thus "infsetsum'_converges f (B-A)"
    unfolding infsetsum'_converges_def by auto

  with limBA show "infsetsum' f (B - A) = limB - limA"
    unfolding infsetsum'_def by (simp add: tendsto_Lim) 
qed

lemma infsetsum'_mono_set:
  fixes f :: "'a\<Rightarrow>'b::{ordered_comm_monoid_add,linorder_topology}"
  assumes fx0: "\<And>x. x\<in>B-A \<Longrightarrow> f x \<ge> 0"
  assumes "A \<subseteq> B"
  assumes "infsetsum'_converges f A"
  assumes "infsetsum'_converges f B"
  shows "infsetsum' f B \<ge> infsetsum' f A"
proof -
  define limA limB f' where "limA = infsetsum' f A" and "limB = infsetsum' f B"
    and "f' x = (if x \<in> A then f x else 0)" for x
  have limA_def': "limA = infsetsum' f' B"
    unfolding limA_def
    apply (subst infsetsum'_subset_zero[where f=f' and B=A])
    unfolding f'_def using \<open>A\<subseteq>B\<close> apply auto[1]
    by (rule infsetsum'_cong, simp)
  have convA': "infsetsum'_converges f' B"
    apply (rule infsetsum'_converges_subset_zero[THEN iffD1, where A1=A])
    unfolding f'_def using \<open>A\<subseteq>B\<close> apply auto[1]
    apply (rule infsetsum'_converges_cong[THEN iffD1, where f1=f])
    unfolding f'_def apply simp
    using assms by simp

  from assms have limA: "(sum f \<longlongrightarrow> limA) (finite_subsets_at_top A)" 
    and limB: "(sum f \<longlongrightarrow> limB) (finite_subsets_at_top B)"
    by (auto simp: limA_def limB_def infsetsum'_converges_def infsetsum'_def tendsto_Lim)

  have limA': "(sum f' \<longlongrightarrow> limA) (finite_subsets_at_top B)"
    unfolding limA_def' using convA' unfolding infsetsum'_def 
    apply simp unfolding infsetsum'_converges_def
    using finite_subsets_at_top_neq_bot tendsto_Lim by blast

  have sumf'_leq_sumf: "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f' x \<le> sum f x"
    apply (rule eventually_finite_subsets_at_top_weakI)
    apply (rule sum_mono)
    unfolding f'_def using fx0
    by (simp add: subsetD)

  show "limA \<le> limB"
    using _ limB limA' sumf'_leq_sumf apply (rule tendsto_le) by auto
qed

lemma tendsto_principal_singleton:
  shows "(f \<longlongrightarrow> f x) (principal {x})"
  unfolding tendsto_def eventually_principal by simp

lemma infsetsum'_converges_finite[simp]:
  assumes "finite F"
  shows "infsetsum'_converges f F"
  unfolding infsetsum'_converges_def finite_subsets_at_top_finite[OF assms]
  using tendsto_principal_singleton by fastforce 

lemma infsetsum'_finite[simp]:
  assumes "finite F"
  shows "infsetsum' f F = sum f F"
  using assms by (auto intro: tendsto_Lim simp: finite_subsets_at_top_finite infsetsum'_def principal_eq_bot_iff tendsto_principal_singleton)

lemma infsetsum'_approx_sum:
  fixes f :: "'a \<Rightarrow> 'b::{comm_monoid_add,metric_space}"
  assumes "infsetsum'_converges f A"
  assumes "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (sum f F) (infsetsum' f A) \<le> \<epsilon>"
proof -
  from assms
  have "(sum f \<longlongrightarrow> infsetsum' f A) (finite_subsets_at_top A)"
    unfolding infsetsum'_def apply simp unfolding infsetsum'_converges_def
    using Lim_trivial_limit tendsto_Lim by blast
  hence "\<forall>\<^sub>F F in (finite_subsets_at_top A). dist (sum f F) (infsetsum' f A) < \<epsilon>"
    using assms(2) by (rule tendstoD)
  thus ?thesis
    apply (simp add: eventually_finite_subsets_at_top) apply meson
    apply (rule_tac x=X in exI) by auto
qed

theorem norm_infsetsum'_bound:
  fixes f :: "'b \<Rightarrow> 'a::real_normed_vector"
    and A :: "'b set"
  assumes "infsetsum'_converges (\<lambda>x. norm (f x)) A"
  assumes "infsetsum'_converges f A" (* TODO: can this be removed? *)
  shows "norm (infsetsum' f A) \<le> (infsetsum' (\<lambda>x. norm (f x)) A)"
proof -
  have "norm (infsetsum' f A) \<le> (infsetsum' (\<lambda>x. norm (f x)) A) + \<epsilon>" if "\<epsilon>>0" for \<epsilon>
  proof -
    obtain F where "norm (infsetsum' f A - sum f F) \<le> \<epsilon>"
      and "finite F" and "F \<subseteq> A"
      apply atomize_elim
      using infsetsum'_approx_sum[where A=A and f=f and \<epsilon>="\<epsilon>"]
      using assms \<open>0 < \<epsilon>\<close> apply auto
      by (metis dist_commute dist_norm)
    hence "norm (infsetsum' f A) \<le> norm (sum f F) + \<epsilon>"
      by (smt norm_triangle_sub)
    also have "\<dots> \<le> sum (\<lambda>x. norm (f x)) F + \<epsilon>"
      using norm_sum by auto
    also have "\<dots> \<le> (infsetsum' (\<lambda>x. norm (f x)) A) + \<epsilon>"
      apply (simp_all flip: infsetsum'_finite add: \<open>finite F\<close>)
      apply (rule infsetsum'_mono_set)
      using \<open>F \<subseteq> A\<close> \<open>finite F\<close> assms by auto
    finally show ?thesis 
      by assumption
  qed
  thus ?thesis
    using linordered_field_class.field_le_epsilon by blast
qed

lemma
  assumes "f abs_summable_on A"
  shows "infsetsum f A = infsetsum' f A"
proof -
  have conv_sum_norm[simp]: "infsetsum'_converges (\<lambda>x. norm (f x)) A"
    apply (rule abs_summable_infsetsum'_converges)
    using assms by simp
  have "norm (infsetsum f A - infsetsum' f A) \<le> \<epsilon>" if "\<epsilon>>0" for \<epsilon>
  proof -
    define \<delta> where "\<delta> = \<epsilon>/2"
    with that have [simp]: "\<delta> > 0" by simp
    obtain F1 where F1A: "F1 \<subseteq> A" and finF1: "finite F1" and leq_eps: "infsetsum (\<lambda>x. norm (f x)) (A-F1) \<le> \<delta>"
    proof -
      have sum_SUP: "ereal (infsetsum (\<lambda>x. norm (f x)) A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum (\<lambda>x. norm (f x)) F))"
        (is "_ = ?SUP")
        apply (rule  infsetsum_nonneg_is_SUPREMUM_ereal)
        by (simp_all add: assms)
      obtain F where "F\<in>{F. finite F \<and> F \<subseteq> A}" and "ereal (sum (\<lambda>x. norm (f x)) F) > ?SUP - ereal (\<delta>)"
        apply atomize_elim unfolding Bex_def[symmetric]
        apply (subst less_SUP_iff[symmetric]) 
        using \<open>\<delta>>0\<close>
        by (metis diff_strict_left_mono diff_zero ereal_less_eq(3) ereal_minus(1) not_le sum_SUP)
      hence "sum (\<lambda>x. norm (f x)) F > infsetsum (\<lambda>x. norm (f x)) A -  (\<delta>)"
        unfolding sum_SUP[symmetric] by auto
      hence "\<delta> > infsetsum (\<lambda>x. norm (f x)) (A-F)"
        apply (subst infsetsum_Diff)
        using abs_summable_on_norm_iff assms 
        using \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> by auto
      thus ?thesis using that 
        apply atomize_elim
        using \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> less_imp_le by blast
    qed
    obtain F2 where F2A: "F2 \<subseteq> A" and finF2: "finite F2"
      and dist: "dist (sum (\<lambda>x. norm (f x)) F2) (infsetsum' (\<lambda>x. norm (f x)) A) \<le> \<delta>"
      apply atomize_elim
      using infsetsum'_approx_sum[where f="(\<lambda>x. norm (f x))" and A=A and \<epsilon>=\<delta>]
      using abs_summable_infsetsum'_converges assms by auto
    have  leq_eps': "infsetsum' (\<lambda>x. norm (f x)) (A-F2) \<le> \<delta>"
      apply (subst infsetsum'_Diff) using F2A dist finF2
      by (auto simp: dist_norm)

    define F where "F = F1 \<union> F2"

    have FA: "F \<subseteq> A" and finF: "finite F" 
      unfolding F_def using F1A F2A finF1 finF2 by auto
    have leq_eps: "infsetsum (\<lambda>x. norm (f x)) (A-F) \<le> \<delta>"
      unfolding F_def 
      apply (rule order.trans[OF _ leq_eps])
      apply (rule infsetsum_mono_neutral_left)
      using assms by (auto intro: abs_summable_on_subset)
    have leq_eps': "infsetsum' (\<lambda>x. norm (f x)) (A-F) \<le> \<delta>"
      unfolding F_def 
      apply (rule order.trans[OF _ leq_eps'])
      apply (rule infsetsum'_mono_set)
      apply auto
      using F_def conv_sum_norm finF infsetsum'_converges_cofin_subset by blast+

    have "norm (infsetsum f A - infsetsum f F) =
        norm (infsetsum f (A-F))"
      apply (subst infsetsum_Diff[symmetric])
      by (simp_all add: FA assms \<delta>_def)
    also have "\<dots> \<le> infsetsum (\<lambda>x. norm (f x)) (A-F)"
      using norm_infsetsum_bound by blast
    also have "\<dots> \<le> \<delta>"
      using leq_eps by simp
    finally have diff1: "norm (infsetsum f A - infsetsum f F) \<le> \<delta>"
      by assumption

    have "norm (infsetsum' f A - infsetsum' f F) =
        norm (infsetsum' f (A-F))"
      apply (subst infsetsum'_Diff[symmetric])
         apply (rule abs_summable_infsetsum'_converges)
      using assms FA finF by auto
    also have "\<dots> \<le> infsetsum' (\<lambda>x. norm (f x)) (A-F)"
      apply (rule norm_infsetsum'_bound[where A="A-F"])
      apply (rule abs_summable_infsetsum'_converges)
      using assms
      using abs_summable_on_subset apply fastforce
      by (simp add: abs_summable_infsetsum'_converges assms finF infsetsum'_converges_cofin_subset)
    also have "\<dots> \<le> \<delta>"
      using leq_eps' by simp
    finally have diff2: "norm (infsetsum' f A - infsetsum' f F) \<le> \<delta>"
      by assumption

    have "infsetsum f F = infsetsum' f F"
      using finF by simp
    hence "norm (infsetsum f A - infsetsum' f A) \<le> norm (infsetsum f A - infsetsum f F) + norm (infsetsum' f A - infsetsum' f F)"
      apply (rule_tac norm_diff_triangle_le)
      apply auto
      by (simp_all add: norm_minus_commute)
    also have "\<dots> \<le> \<epsilon>"
      using diff1 diff2 \<delta>_def by linarith
    finally show ?thesis
      by assumption
  qed
  hence "norm (infsetsum f A - infsetsum' f A) = 0"
    by (meson antisym_conv1 dense_ge norm_not_less_zero)
  thus ?thesis
    by auto
qed

lemma abs_summable_partition:
  fixes T :: "'b set" and I :: "'a set"
  assumes "\<And>i. f abs_summable_on S i"
  assumes "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on I"
  assumes "T \<subseteq> (\<Union>i\<in>I. S i)"
  shows "f abs_summable_on T"
proof (rule abs_summable_finiteI)
  fix F assume finite_F: "finite F" and FT: "F \<subseteq> T"
  define index where "index s = (SOME i. i\<in>I \<and> s\<in>S i)" for s
  then have index_I: "index s \<in> I" and S_index: "s \<in> S (index s)" if "s \<in> (\<Union>i\<in>I. S i)" for s
     apply auto
    by (metis (no_types, lifting) UN_E someI_ex that)+
  define S' where "S' i = {s\<in>S i. i = index s}" for i
  have S'_S: "S' i \<subseteq> S i" for i
    unfolding S'_def by simp
  then have f_sum_S': "f abs_summable_on S' i" for i
    by (meson abs_summable_on_subset assms(1))
  with assms(1) S'_S have "(\<Sum>\<^sub>ax\<in>S' i. norm (f x)) \<le> (\<Sum>\<^sub>ax\<in>S i. norm (f x))" for i
    by (simp add: infsetsum_mono_neutral_left)
  with assms(2) have sum_I: "(\<lambda>i. \<Sum>\<^sub>ax\<in>S' i. norm (f x)) abs_summable_on I"
    by (smt abs_summable_on_comparison_test' infsetsum_cong norm_ge_zero norm_infsetsum_bound real_norm_def)
  have "(\<Union>i\<in>I. S i) = (\<Union>i\<in>I. S' i)"
    unfolding S'_def by (auto intro!: index_I S_index)
  with assms(3) have T_S': "T \<subseteq> (\<Union>i\<in>I. S' i)"
    by simp
  have S'_disj: "(S' i) \<inter> (S' j) = {}" if "i\<noteq>j" for i j
    unfolding S'_def disjnt_def using that by auto
  
  define B where "B i = (\<Sum>\<^sub>ax\<in>S i. norm (f x))" for i
  have sum_FS'_B: "(\<Sum>x\<in>F\<inter>S' i. norm (f x)) \<le> B i" for i
    unfolding B_def using f_sum_S' finite_F FT
    by (metis S'_S abs_summable_finiteI_converse assms(1) finite_Int le_inf_iff order_refl subset_antisym)
  have B_pos[simp]: "B i \<ge> 0" for i
    unfolding B_def by (rule infsetsum_nonneg, simp)
  have B_sum_I[simp]: "B abs_summable_on I"
    by (simp add: B_def assms(2))

  define J where "J = {i\<in>I. F\<inter>S' i \<noteq> {}}"
  have finite_J[simp]: "finite J"
  proof -
    define a where "a i = (SOME x. x\<in>F\<inter>S' i)" for i
    then have a: "a i \<in> F\<inter>S' i" if "i \<in> J" for i
      unfolding J_def
      by (metis (mono_tags) Collect_conj_eq Int_Collect J_def some_in_eq that)
    have "inj_on a J"
      apply (rule inj_onI)
      using a S'_disj apply auto
      by (metis S'_disj disjoint_iff_not_equal)
    moreover have "a ` J \<subseteq> F"
      using a by auto
    ultimately show "finite J"
      using finite_F
      using Finite_Set.inj_on_finite by blast
  qed
  have JI[simp]: "J \<subseteq> I"
    unfolding J_def by simp

  have "F = (\<Union>i\<in>J. F\<inter>S' i)"
    unfolding J_def apply auto
    by (metis FT T_S' UN_E disjoint_iff_not_equal subsetD)
  then have "(\<Sum>x\<in>F. norm (f x)) = (\<Sum>x\<in>(\<Union>i\<in>J. F\<inter>S' i). norm (f x))"
    by simp
  also have "\<dots> = (\<Sum>i\<in>J. \<Sum>x\<in>F \<inter> S' i. norm (f x))"
    apply (rule sum.UNION_disjoint)
    using finite_J finite_F S'_disj by auto
  also have "\<dots> \<le> (\<Sum>i\<in>J. B i)"
    using sum_FS'_B
    by (simp add: ordered_comm_monoid_add_class.sum_mono)
  also have "\<dots> = (\<Sum>\<^sub>ai\<in>J. B i)"
    by simp
  also have "\<dots> \<le> (\<Sum>\<^sub>ai\<in>I. B i)"
    apply (rule infsetsum_mono_neutral_left)
    by auto
  finally show "(\<Sum>x\<in>F. norm(f x)) \<le> (\<Sum>\<^sub>ai\<in>I. B i)"
    by simp
qed


lemma abs_summable_product':
  fixes X :: "'a set" and Y :: "'b set"
  assumes "\<And>x. (\<lambda>y. f (x,y)) abs_summable_on Y"
  assumes "(\<lambda>x. \<Sum>\<^sub>ay\<in>Y. norm (f (x,y))) abs_summable_on X"
  shows "f abs_summable_on X\<times>Y"
proof -
  define S where "S x = {x} \<times> Y" for x :: 'a
  have bij[simp]: "bij_betw (Pair x) Y (S x)" for x
    apply (rule bij_betwI[where g=snd])
    apply (simp_all add: S_def)
    using SigmaE by auto
  have "f abs_summable_on S x" for x
    apply (subst abs_summable_on_reindex_bij_betw[symmetric, where A=Y and g="\<lambda>y. (x,y)"])
    using assms(1) by simp_all
  moreover 
  have "(\<Sum>\<^sub>ay\<in>Y. norm (f (x, y))) = (\<Sum>\<^sub>ay\<in>S x. norm (f y))" for x
    apply (rule infsetsum_reindex_bij_betw)
    unfolding S_def using bij_betw_def
    using S_def bij by auto 
  then have "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on X"
    using assms(2) by simp
  then have "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on X"
    by auto
  moreover have "X \<times> Y \<subseteq> (\<Union>i\<in>X. S i)"
    unfolding S_def by auto
  ultimately show ?thesis
    by (rule abs_summable_partition[where S=S and I=X])
qed

lemma infsetsum_prod_PiE:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {real_normed_field,banach,second_countable_topology}"
  assumes finite: "finite A"
  assumes summable: "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B x"
  shows   "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) = (\<Prod>x\<in>A. infsetsum (f x) (B x))"
proof -
  define B' where "B' x = {y\<in>B x. 0 \<noteq> f x y}" for x
  have [simp]: "B' x \<subseteq> B x" for x
    unfolding B'_def by simp
  have PiE_subset: "Pi\<^sub>E A B' \<subseteq> Pi\<^sub>E A B"
    apply (rule PiE_mono) by simp
  have countable: "countable (B' x)" if "x\<in>A" for x
    unfolding B'_def apply (rule abs_summable_countable)
    using that by (rule summable)
  have summable: "f x abs_summable_on B' x" if "x\<in>A" for x
    using summable apply (rule abs_summable_on_subset)
    using that by auto
  have 0: "(\<Prod>x\<in>A. f x (g x)) = 0" if "g \<in> Pi\<^sub>E A B - Pi\<^sub>E A B'" for g
  proof -
    from that have "g \<in> extensional A"
      by (simp add: PiE_def)
    from that have "g \<notin> Pi\<^sub>E A B'"
      by simp
    with \<open>g \<in> extensional A\<close> have "g \<notin> Pi A B'"
      unfolding PiE_def by simp
    then obtain x where "x\<in>A" and "g x \<notin> B' x"
      unfolding Pi_def by auto
    then have "f x (g x) = 0"
      unfolding B'_def using that by auto
    with finite show ?thesis
      using finite apply (rule_tac prod_zero)
      using \<open>x\<in>A\<close> by auto
  qed

  have "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B)
      = infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B')"
    apply (rule infsetsum_cong_neutral)
    using 0 PiE_subset by auto
  also have "\<dots> = (\<Prod>x\<in>A. infsetsum (f x) (B' x))"
    using finite countable summable by (rule infsetsum_prod_PiE)
  also have "\<dots> = (\<Prod>x\<in>A. infsetsum (f x) (B x))"
    apply (rule prod.cong, simp)
    apply (rule infsetsum_cong_neutral)
    unfolding B'_def by auto
  finally show ?thesis
    by -
qed


lemma infsetsum_0D:
  fixes f :: "'a \<Rightarrow> real"
  assumes "infsetsum f A = 0"
  assumes abs_sum: "f abs_summable_on A"
  assumes nneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
  assumes "x \<in> A"
  shows "f x = 0"
proof -
  from abs_sum have [simp]: "f abs_summable_on (A-{x})"
    by (meson Diff_subset abs_summable_on_subset)
  from abs_sum \<open>x\<in>A\<close> have [simp]: "f abs_summable_on {x}"
    by auto
  from assms have "0 = infsetsum f A"
    by simp
  also have "\<dots> = infsetsum f (A-{x}) + infsetsum f {x}"
    apply (subst infsetsum_Un_disjoint[symmetric])
    using \<open>x\<in>A\<close> by (auto simp add: insert_absorb)
  also have "\<dots> \<ge> 0 + infsetsum f {x}" (is "_ \<ge> \<dots>")
    apply (rule add_right_mono)
    using nneg apply (rule infsetsum_nonneg)
    by simp
  also have "\<dots> = f x"
    by simp
  finally have "f x \<le> 0"
    by -
  with nneg[OF \<open>x\<in>A\<close>] show "f x = 0"
    by auto
qed

lemma sum_leq_infsetsum:
  fixes f :: "_ \<Rightarrow> real"
  assumes "f abs_summable_on N"
  assumes "finite M"
  assumes "M \<subseteq> N"
  assumes "\<And>x. x\<in>N-M \<Longrightarrow> f x \<ge> 0"
  shows "sum f M \<le> infsetsum f N"
proof -
  have "infsetsum f M \<le> infsetsum f N"
    apply (rule infsetsum_mono_neutral_left)
    using assms by auto
  then show ?thesis
    using assms by auto
qed



lemma infsetsum_cmult_left':
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra, second_countable_topology, division_ring}"
  (* assumes "c \<noteq> 0 \<Longrightarrow> f abs_summable_on A" *)
  shows   "infsetsum (\<lambda>x. f x * c) A = infsetsum f A * c"
proof (cases "c \<noteq> 0 \<longrightarrow> f abs_summable_on A")
  case True
  then show ?thesis 
    apply auto
    by (rule infsetsum_cmult_left)
next
  case False
  then have "c\<noteq>0" and "\<not> f abs_summable_on A"
    by auto
  have "\<not> (\<lambda>x. f x * c) abs_summable_on A"
  proof (rule notI)
    assume "(\<lambda>x. f x * c) abs_summable_on A"
    then have "(\<lambda>x. (f x * c) * inverse c) abs_summable_on A"
      by (rule abs_summable_on_cmult_left)
    with \<open>\<not> f abs_summable_on A\<close> show False
      apply auto
      by (metis (no_types, lifting) False Groups.mult_ac(1) abs_summable_on_cong mult_1_right right_inverse)
  qed
  with \<open>\<not> f abs_summable_on A\<close>
  show ?thesis 
    by (simp add: not_summable_infsetsum_eq)
qed

lemma abs_summable_on_zero_diff:
  assumes "f abs_summable_on A"
  assumes "\<And>x. x \<in> B - A \<Longrightarrow> f x = 0"
  shows "f abs_summable_on B"
  apply (rewrite at B DEADID.rel_mono_strong[of _ "(B-A) \<union> (A\<inter>B)"])
   apply auto[1]
  apply (rule abs_summable_on_union)
   apply (rule abs_summable_on_comparison_test'[where g="\<lambda>x. 0"])
    apply simp
  using assms(2) apply auto[1]
  using assms(1) apply (rule abs_summable_on_subset)
  by simp

theorem abs_summable_on_Sigma_iff:
  shows   "f abs_summable_on Sigma A B \<longleftrightarrow>
             (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x) \<and>
             ((\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A)"
proof auto
  assume sum_AB: "f abs_summable_on Sigma A B"
  define S' where "S' = {x\<in>Sigma A B. 0 \<noteq> f x}"
  from sum_AB have "countable S'"
    unfolding S'_def by (rule abs_summable_countable)
  define A' B' where "A' = fst ` S'"
    and "B' x = B x \<inter> snd ` S'" for x
  have A'A: \<open>A' \<subseteq> A\<close> and B'B: \<open>B' x \<subseteq> B x\<close> for x
    unfolding A'_def B'_def S'_def by auto
  have  cntA: "countable A'" and cntB: "countable (B' x)" for x
    unfolding A'_def B'_def using \<open>countable S'\<close> by auto
  have f0: "f (x,y) = 0" if "x \<in> A - A'" and "y \<in> B x" for x y
  proof -
    from that have "(x,y) \<in> Sigma A B"
      by auto
    moreover from that have "(x,y) \<notin> S'"
      unfolding A'_def
      by (metis image_eqI mem_simps(6) prod.sel(1)) 
    ultimately show "f (x,y) = 0"
      unfolding S'_def by auto
  qed
  have f0': "f (x,y) = 0" if "x \<in> A" and "y \<in> B x - B' x" for x y
  proof -
    from that have "(x,y) \<in> Sigma A B"
      by auto
    moreover from that have "(x,y) \<notin> S'"
      unfolding B'_def
      by (auto simp add: rev_image_eqI)
    ultimately show "f (x,y) = 0"
      unfolding S'_def by auto
  qed
  from sum_AB have sum_A'B': "f abs_summable_on Sigma A' B'"
    apply (rule abs_summable_on_subset)
    using A'A B'B by (rule Sigma_mono)

  from sum_A'B' have "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x \<in> A'" for x
    using abs_summable_on_Sigma_iff[OF cntA cntB, where f=f]
    using that by auto
  moreover have "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x \<in> A - A'" for x
    apply (subst abs_summable_on_zero_diff[where A="{}"])
    apply auto apply (subst f0) using that apply auto
    using f0 that B'B by auto
  ultimately have "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x \<in> A" for x
    using that by auto
  then show "(\<lambda>y. f (x, y)) abs_summable_on B x" if "x \<in> A" for x
    apply (rule abs_summable_on_zero_diff)
    using that f0' by auto

  from sum_A'B' have "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B' x)) abs_summable_on A'"
    using abs_summable_on_Sigma_iff[OF cntA cntB, where f=f] by auto
  then have "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B' x)) abs_summable_on A"
    apply (rule abs_summable_on_zero_diff)
    apply (subst infsetsum_cong[where g=\<open>\<lambda>x. 0\<close> and B="B' _"])
    using f0 B'B by auto
  then show "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A"
    apply (rule abs_summable_on_cong[THEN iffD1, rotated 2])
     apply (rule infsetsum_cong_neutral)
    using B'B f0' by auto 
next
  assume sum_B: "\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x"
  assume sum_A: "(\<lambda>x. \<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) abs_summable_on A"
  define B' where "B' x = {y\<in>B x. 0 \<noteq> f (x,y)}" for x
  from sum_B have cnt_B': "countable (B' x)" if "x\<in>A" for x
    unfolding B'_def apply (rule_tac abs_summable_countable)
    using that by auto
  define A' where "A' = {x\<in>A. 0 \<noteq> (\<Sum>\<^sub>ay\<in>B x. norm (f (x, y)))}"
  from sum_A have cnt_A': "countable A'"
    unfolding A'_def by (rule abs_summable_countable)
  have A'A: "A' \<subseteq> A" and B'B: "B' x \<subseteq> B x" for x
    unfolding A'_def B'_def by auto
  have f0': "f (x,y) = 0" if (* "x \<in> A" and *) "y \<in> B x - B' x" for x y
    using that unfolding B'_def by auto
  have f0: "f (x,y) = 0" if "x \<in> A - A'" and "y \<in> B x" for x y
  proof -
    have "(\<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) = 0"
      using that unfolding A'_def by auto
    then have "norm (f (x, y)) = 0"
      apply (rule infsetsum_0D)
      using sum_B that by auto
    then show ?thesis
      by auto
  qed

  from sum_B have sum_B': "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x\<in>A" for x
    apply (rule_tac abs_summable_on_subset[where B="B x"]) using B'B that by auto
  have *: "(\<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) = (\<Sum>\<^sub>ay\<in>B' x. norm (f (x, y)))" if "x\<in>A" for x
    apply (rule infsetsum_cong_neutral)
    using f0' B'B that by auto
  have sum_A': "(\<lambda>x. \<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) abs_summable_on A'"
    using _ A'A apply (rule abs_summable_on_subset[where B=A])
    apply (subst abs_summable_on_cong)
      apply (rule *[symmetric])
    using sum_A by auto

  from sum_A' sum_B'
  have "f abs_summable_on Sigma A' B'"
    using abs_summable_on_Sigma_iff[where A=A' and B=B' and f=f, OF cnt_A' cnt_B'] 
    using A'A by auto
  then show "f abs_summable_on Sigma A B"
    apply (rule abs_summable_on_zero_diff)
    using f0 f0' by auto
qed

lemma
  fixes f :: "'a \<Rightarrow> 'c :: {banach, real_normed_field, second_countable_topology}"
  assumes "f abs_summable_on A" and "g abs_summable_on B"
  shows   abs_summable_on_product: "(\<lambda>(x,y). f x * g y) abs_summable_on A \<times> B"
    and   infsetsum_product: "infsetsum (\<lambda>(x,y). f x * g y) (A \<times> B) =
                                infsetsum f A * infsetsum g B"
proof -
  from assms show "(\<lambda>(x,y). f x * g y) abs_summable_on A \<times> B"
    by (subst abs_summable_on_Sigma_iff)
       (auto simp: norm_mult infsetsum_cmult_right)
  with assms show "infsetsum (\<lambda>(x,y). f x * g y) (A \<times> B) = infsetsum f A * infsetsum g B"
    by (subst infsetsum_Sigma)
       (auto simp: infsetsum_cmult_left infsetsum_cmult_right)
qed

subsection\<open>\<open>Lattice_Missing\<close> -- Miscellaneous missing facts about lattices\<close>

text \<open>Two bundles to activate and deactivate lattice specific notation (e.g., \<open>\<sqinter>\<close> etc.).
  Activate the notation locally via "@{theory_text \<open>includes lattice_notation\<close>}" in a lemma statement.
  (Or sandwich a declaration using that notation between "@{theory_text \<open>unbundle lattice_notation ... unbundle no_lattice_notation\<close>}.)\<close>

bundle lattice_notation begin
notation inf (infixl "\<sqinter>" 70)
notation sup (infixl "\<squnion>" 65)
notation Inf ("\<Sqinter>")
notation Sup ("\<Squnion>")
notation bot ("\<bottom>")
notation top ("\<top>")
end

bundle no_lattice_notation begin
notation inf (infixl "\<sqinter>" 70)
notation sup (infixl "\<squnion>" 65)
notation Inf ("\<Sqinter>")
notation Sup ("\<Squnion>")
notation bot ("\<bottom>")
notation top ("\<top>")
end

unbundle lattice_notation

text \<open>The following class \<open>complemented_lattice\<close> describes complemented lattices (with
  \<^const>\<open>uminus\<close> for the complement). The definition follows 
  \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Definition_and_basic_properties\<close>.
  Additionally, it adopts the convention from \<^class>\<open>boolean_algebra\<close> of defining 
  \<^const>\<open>minus\<close> in terms of the complement.\<close>

class complemented_lattice = bounded_lattice + uminus + minus + 
  assumes inf_compl_bot[simp]: "inf x (-x) = bot"
    and sup_compl_top[simp]: "sup x (-x) = top"
    and diff_eq:  "x - y = inf x (- y)" begin

lemma dual_complemented_lattice:
  "class.complemented_lattice (\<lambda>x y. x \<squnion> (- y)) uminus sup greater_eq greater inf \<top> \<bottom>"
  apply (rule class.complemented_lattice.intro)
  apply (rule dual_bounded_lattice)
  by (unfold_locales, auto simp add: diff_eq)

lemma compl_inf_bot [simp]: "inf (- x) x = bot"
  by (simp add: inf_commute)

lemma compl_sup_top [simp]: "sup (- x) x = top"
  by (simp add: sup_commute)

end

class complete_complemented_lattice = complemented_lattice + complete_lattice 

text \<open>The following class \<open>complemented_lattice\<close> describes orthocomplemented lattices,
  following   \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Orthocomplementation\<close>.\<close>
class orthocomplemented_lattice = complemented_lattice +
  assumes ortho_involution[simp]: "- (- x) = x"
    and ortho_antimono: "x \<le> y \<Longrightarrow> -x \<ge> -y" begin

lemma dual_orthocomplemented_lattice:
  "class.orthocomplemented_lattice (\<lambda>x y. x \<squnion> - y) uminus sup greater_eq greater inf \<top> \<bottom>"
  apply (rule class.orthocomplemented_lattice.intro)
  apply (rule dual_complemented_lattice)
  by (unfold_locales, auto simp add: diff_eq intro: ortho_antimono)

lemma compl_eq_compl_iff [simp]: "- x = - y \<longleftrightarrow> x = y"
  by (metis ortho_involution)

lemma compl_bot_eq [simp]: "- bot = top"
  by (metis inf_compl_bot inf_top_left ortho_involution)

lemma compl_top_eq [simp]: "- top = bot"
  using compl_bot_eq ortho_involution by blast

text \<open>De Morgan's law\<close>
(* Proof from: https://planetmath.org/orthocomplementedlattice *)
lemma compl_sup [simp]: "- (x \<squnion> y) = - x \<sqinter> - y"
proof -
  have "- (x \<squnion> y) \<le> - x"
    by (simp add: ortho_antimono)
  moreover have "- (x \<squnion> y) \<le> - y"
    by (simp add: ortho_antimono)
  ultimately have 1: "- (x \<squnion> y) \<le> - x \<sqinter> - y"
    by (simp add: sup.coboundedI1)
  have \<open>x \<le> - (-x \<sqinter> -y)\<close>
    by (metis inf.cobounded1 ortho_antimono ortho_involution)
  moreover have \<open>y \<le> - (-x \<sqinter> -y)\<close>
    by (metis inf.cobounded2 ortho_antimono ortho_involution)
  ultimately have \<open>x \<squnion> y \<le> - (-x \<sqinter> -y)\<close>
    by auto
  then have 2: \<open>-x \<sqinter> -y \<le> - (x \<squnion> y)\<close>
    using ortho_antimono by fastforce
  from 1 2 show ?thesis
    by (simp add: eq_iff)
qed

text \<open>De Morgan's law\<close>
lemma compl_inf [simp]: "- (x \<sqinter> y) = - x \<squnion> - y"
  using compl_sup
  by (metis ortho_involution)

lemma compl_mono:
  assumes "x \<le> y"
  shows "- y \<le> - x"
  by (simp add: assms local.ortho_antimono)
  
lemma compl_le_compl_iff [simp]: "- x \<le> - y \<longleftrightarrow> y \<le> x"
  by (auto dest: compl_mono)

lemma compl_le_swap1:
  assumes "y \<le> - x"
  shows "x \<le> -y"
  using assms ortho_antimono by fastforce

lemma compl_le_swap2:
  assumes "- y \<le> x"
  shows "- x \<le> y"
  using assms local.ortho_antimono by fastforce

lemma compl_less_compl_iff[simp]: "- x < - y \<longleftrightarrow> y < x"
  by (auto simp add: less_le)

lemma compl_less_swap1:
  assumes "y < - x"
  shows "x < - y"
  using assms compl_less_compl_iff by fastforce

lemma compl_less_swap2:
  assumes "- y < x"
  shows "- x < y"
  using assms compl_le_swap1 compl_le_swap2 less_le_not_le by auto

lemma sup_cancel_left1: "sup (sup x a) (sup (- x) b) = top"
  by (simp add: sup_commute sup_left_commute)

lemma sup_cancel_left2: "sup (sup (- x) a) (sup x b) = top"
  by (simp add: sup.commute sup_left_commute)

lemma inf_cancel_left1: "inf (inf x a) (inf (- x) b) = bot"
  by (simp add: inf.left_commute inf_commute)

lemma inf_cancel_left2: "inf (inf (- x) a) (inf x b) = bot"
  using inf.left_commute inf_commute by auto

lemma sup_compl_top_left1 [simp]: "sup (- x) (sup x y) = top"
  by (simp add: sup_assoc[symmetric])

lemma sup_compl_top_left2 [simp]: "sup x (sup (- x) y) = top"
  using sup_compl_top_left1[of "- x" y] by simp

lemma inf_compl_bot_left1 [simp]: "inf (- x) (inf x y) = bot"
  by (simp add: inf_assoc[symmetric])

lemma inf_compl_bot_left2 [simp]: "inf x (inf (- x) y) = bot"
  using inf_compl_bot_left1[of "- x" y] by simp

lemma inf_compl_bot_right [simp]: "inf x (inf y (- x)) = bot"
  by (subst inf_left_commute) simp

end

class complete_orthocomplemented_lattice = orthocomplemented_lattice + complete_lattice

instance complete_orthocomplemented_lattice \<subseteq> complete_complemented_lattice
  by intro_classes

text \<open>The following class \<open>orthomodular_lattice\<close> describes orthomodular lattices,
following   \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Orthomodular_lattices\<close>.\<close>
class orthomodular_lattice = orthocomplemented_lattice +
  assumes orthomodular: "x \<le> y \<Longrightarrow> sup x (inf (-x) y) = y" begin

lemma dual_orthomodular_lattice:
  "class.orthomodular_lattice (\<lambda>x y. x \<squnion> - y) uminus sup greater_eq greater inf \<top> \<bottom>"
  apply (rule class.orthomodular_lattice.intro)
  apply (rule dual_orthocomplemented_lattice)
  apply (unfold_locales)
  using local.compl_eq_compl_iff local.ortho_antimono local.orthomodular by fastforce
end

class complete_orthomodular_lattice = orthomodular_lattice + complete_lattice begin

end

instance complete_orthomodular_lattice \<subseteq> complete_orthocomplemented_lattice
  by intro_classes


instance boolean_algebra \<subseteq> orthomodular_lattice
proof
  fix x y :: 'a  
  show "sup (x::'a) (inf (- x) y) = y"
    if "(x::'a) \<le> y"
    using that
    by (simp add: sup.absorb_iff2 sup_inf_distrib1) 
  show "x - y = inf x (- y)"
    by (simp add: boolean_algebra_class.diff_eq)
qed auto

instance complete_boolean_algebra \<subseteq> complete_orthomodular_lattice
  by intro_classes

unbundle no_lattice_notation

subsection \<open>\<open>Operator_Norm_Missing\<close> -- Miscellaneous results about the operator norm\<close>

text \<open>This theorem complements \<^theory>\<open>HOL-Analysis.Operator_Norm\<close>
      additional useful facts about operator norms.\<close>

subsection \<open>Characterization of the operator norm\<close>

lemma ex_norm1: 
  assumes \<open>(UNIV::'a::real_normed_vector set) \<noteq> {0}\<close>
  shows \<open>\<exists>x::'a. norm x = 1\<close>
proof-
  have \<open>\<exists>x::'a. x \<noteq> 0\<close>
    using assms by fastforce
  then obtain x::'a where \<open>x \<noteq> 0\<close>
    by blast
  hence \<open>norm x \<noteq> 0\<close>
    by simp
  hence \<open>(norm x) / (norm x) = 1\<close>
    by simp
  moreover have \<open>(norm x) / (norm x) = norm (x /\<^sub>R (norm x))\<close>
    by simp
  ultimately have \<open>norm (x /\<^sub>R (norm x)) = 1\<close>
    by simp
  thus ?thesis
    by blast 
qed

lemma bdd_above_norm_f:
  assumes "bounded_linear f"
  shows \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
proof-
  have \<open>\<exists>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f x) \<le> M\<close>
    using assms
    by (metis bounded_linear.axioms(2) bounded_linear_axioms_def)
  thus ?thesis by auto
qed

(* TODO: remove assumption "UNIV\<noteq>{0}" and add type class not_singleton instead *)
lemma onorm_sphere:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>(UNIV::'a set) \<noteq> {0}\<close> and  \<open>bounded_linear f\<close>
  shows \<open>onorm f = Sup {norm (f x) | x. norm x = 1}\<close>
proof(cases \<open>f = (\<lambda> _. 0)\<close>)
  case True
  have \<open>onorm f = 0\<close>
    by (simp add: True onorm_eq_0)  
  moreover have \<open>Sup {norm (f x) | x. norm x = 1} = 0\<close>
  proof-
    have \<open>\<exists>x::'a. norm x = 1\<close>
      using \<open>(UNIV::'a set) \<noteq> {0}\<close> ex_norm1
      by blast
    have \<open>norm (f x) = 0\<close>
      for x
      by (simp add: True)      
    hence \<open>{norm (f x) | x. norm x = 1} = {0}\<close>
      apply auto using \<open>\<exists>x. norm x = 1\<close> by blast 
    thus ?thesis
      by simp 
  qed
  ultimately show ?thesis by simp
next
  case False
  thus ?thesis 
  proof-
    have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) | x. norm x = 1}\<close>
    proof-
      have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) / norm x | x. True}\<close>
        by (simp add: full_SetCompr_eq)
      also have \<open>... = Sup {norm (f x) | x. norm x = 1}\<close>
      proof-
        have \<open>{norm (f x) / norm x |x. True} = {norm (f x) |x. norm x = 1} \<union> {0}\<close>
        proof-
          have \<open>y \<in> {norm (f x) / norm x |x. True} \<Longrightarrow> y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
            for y
          proof-
            assume \<open>y \<in> {norm (f x) / norm x |x. True}\<close>
            show ?thesis
            proof(cases \<open>y = 0\<close>)
              case True
              thus ?thesis
                by simp 
            next
              case False
              have \<open>\<exists> x. y = norm (f x) / norm x\<close>
                using \<open>y \<in> {norm (f x) / norm x |x. True}\<close> by auto
              then obtain x where \<open>y = norm (f x) / norm x\<close>
                by blast
              hence \<open>y = \<bar>(1/norm x)\<bar> * norm ( f x )\<close>
                by simp
              hence \<open>y = norm ( (1/norm x) *\<^sub>R f x )\<close>
                by simp
              hence \<open>y = norm ( f ((1/norm x) *\<^sub>R x) )\<close>
                by (simp add: assms linear_simps(5))
              moreover have \<open>norm ((1/norm x) *\<^sub>R x) = 1\<close>
                using False \<open>y = norm (f x) / norm x\<close> by auto              
              ultimately have \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
                by blast
              thus ?thesis by blast
            qed
          qed
          moreover have \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}
                     \<Longrightarrow> y \<in> {norm (f x) / norm x |x. True}\<close>
            for y
          proof(cases \<open>y = 0\<close>)
            case True
            thus ?thesis
              by auto 
          next
            case False
            hence \<open>y \<notin> {0}\<close>
              by simp
            moreover assume \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
            ultimately have \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
              by simp
            hence \<open>\<exists> x. norm x = 1 \<and> y = norm (f x)\<close>
              by auto
            then obtain x where \<open>norm x = 1\<close> and \<open>y = norm (f x)\<close>
              by auto
            have \<open>y = norm (f x) / norm x\<close> using  \<open>norm x = 1\<close>  \<open>y = norm (f x)\<close>
              by simp 
            thus ?thesis
              by auto 
          qed
          ultimately show ?thesis by blast
        qed
        hence \<open>Sup {norm (f x) / norm x |x. True} = Sup ({norm (f x) |x. norm x = 1} \<union> {0})\<close>
          by simp
        moreover have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
        proof-
          have \<open>\<exists> x::'a. norm x = 1 \<and> norm (f x) \<ge> 0\<close>
          proof-
            have \<open>\<exists> x::'a. norm x = 1\<close>
              by (metis (full_types) False assms(2) linear_simps(3) norm_sgn)              
            then obtain x::'a where \<open>norm x = 1\<close>
              by blast
            have \<open>norm (f x) \<ge> 0\<close>
              by simp
            thus ?thesis using \<open>norm x = 1\<close> by blast
          qed
          hence \<open>\<exists> y \<in> {norm (f x) |x. norm x = 1}. y \<ge> 0\<close>
            by blast
          then obtain y::real where \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> 
            and \<open>y \<ge> 0\<close>
            by auto
          have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
            using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> by blast         
          moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
            using bdd_above_norm_f
            by (metis (mono_tags, lifting) assms(2)) 
          ultimately have \<open>y \<le> Sup {norm (f x) |x. norm x = 1}\<close>
            using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
            by (simp add: cSup_upper) 
          thus ?thesis using \<open>y \<ge> 0\<close> by simp
        qed
        moreover have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {0}) = Sup {norm (f x) |x. norm x = 1}\<close>
        proof-
          have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
            by (simp add: assms(1) ex_norm1)
          moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
            using assms(2) bdd_above_norm_f by force
          have \<open>{0::real} \<noteq> {}\<close>
            by simp
          moreover have \<open>bdd_above {0::real}\<close>
            by simp
          ultimately have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {(0::real)})
             = max (Sup {norm (f x) |x. norm x = 1}) (Sup {0::real})\<close>
            by (metis (lifting) \<open>0 \<le> Sup {norm (f x) |x. norm x = 1}\<close> \<open>bdd_above {0}\<close> \<open>bdd_above {norm (f x) |x. norm x = 1}\<close> \<open>{0} \<noteq> {}\<close> \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close> cSup_singleton cSup_union_distrib max.absorb_iff1 sup.absorb_iff1)
          moreover have \<open>Sup {(0::real)} = (0::real)\<close>
            by simp          
          moreover have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
            by (simp add: \<open>0 \<le> Sup {norm (f x) |x. norm x = 1}\<close>)
          ultimately show ?thesis
            by simp
        qed
        moreover have \<open>Sup ( {norm (f x) |x. norm x = 1} \<union> {0})
           = max (Sup {norm (f x) |x. norm x = 1}) (Sup {0}) \<close>
          using calculation(2) calculation(3) by auto
        ultimately show ?thesis by simp 
      qed
      ultimately show ?thesis
        by linarith 
    qed
    thus ?thesis unfolding onorm_def by blast
  qed
qed


(* TODO: remove assumption "UNIV\<noteq>{0}" and add type class not_singleton instead *)
proposition onorm_Inf_bound:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes  \<open>(UNIV::'a set) \<noteq> {0}\<close> and \<open>bounded_linear f\<close>
  shows  \<open>onorm f = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
proof-
  have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Inf {K. (\<forall>x\<noteq>0. norm (f x)/ norm x \<le>  K)}\<close>
  proof-
    define A where \<open>A = {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
    have \<open>A \<noteq> {}\<close>
    proof-
      have \<open>\<exists> x::'a. x \<noteq> 0\<close>
        using \<open>UNIV \<noteq> {0}\<close> by auto
      thus ?thesis using A_def
        by simp 
    qed
    moreover have \<open>bdd_above A\<close>
    proof-
      have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
        using \<open>bounded_linear f\<close> le_onorm by auto
      thus ?thesis using A_def
        by auto 
    qed
    ultimately have \<open>Sup A = Inf {b. \<forall>a\<in>A. a \<le> b}\<close>
      using Complete_Lattices.complete_lattice_class.Sup_Inf
      by (simp add: cSup_cInf)  
    moreover have \<open>{b. \<forall>a\<in>A. a \<le> b} = {K. (\<forall>x\<noteq>0. norm (f x)/ norm x \<le>  K)}\<close>
    proof-
      have \<open>{b. \<forall>a\<in>A. a \<le> b} = {b. \<forall>a\<in>{norm (f x) / (norm x) | x. x \<noteq> 0}. a \<le> b}\<close>
        using A_def by blast
      also have \<open>... = {b. \<forall>x\<in>{x | x. x \<noteq> 0}. norm (f x) / (norm x) \<le> b}\<close>
        by auto
      also have \<open>... = {b. \<forall>x\<noteq>0. norm (f x) / (norm x) \<le> b}\<close>
        by auto
      finally show ?thesis by blast
    qed
    ultimately show ?thesis 
      using A_def
      by simp 
  qed
  moreover have \<open>(\<forall>x\<noteq>0. norm (f x) \<le> norm x * K) \<longleftrightarrow> (\<forall>x\<noteq>0. norm (f x)/ norm x \<le> K)\<close>
    for K
  proof
    show "\<forall>x\<noteq>0. norm (f x) / norm x \<le> K"
      if "\<forall>x\<noteq>0. norm (f x) \<le> norm x * K"
      using divide_le_eq nonzero_mult_div_cancel_left norm_le_zero_iff that
      by (simp add: divide_le_eq mult.commute)

    show "\<forall>x\<noteq>0. norm (f x) \<le> norm x * K"
      if "\<forall>x\<noteq>0. norm (f x) / norm x \<le> K"
      using divide_le_eq nonzero_mult_div_cancel_left norm_le_zero_iff that
      by (simp add: divide_le_eq mult.commute)
  qed
  ultimately have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
    by simp
  moreover have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Sup {norm (f x) / (norm x) | x. True}\<close>
  proof-
    have \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0}  = {norm (f x) / (norm x) | x. True}\<close>
      using Collect_cong by blast
    hence \<open>Sup ({norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0}) = Sup {norm (f x) / (norm x) | x. True}\<close>
      by simp
    moreover have \<open>Sup ({norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0})
        = max (Sup {norm (f x) / (norm x) | x. x \<noteq> 0}) (Sup {norm (f x) / (norm x) | x. x = 0})\<close>
    proof-
      have \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<noteq> {}\<close>
      proof-
        have \<open>\<exists> x::'a. x \<noteq> 0\<close>
          using \<open>UNIV\<noteq>{0}\<close> by auto
        thus ?thesis
          by simp 
      qed
      moreover have \<open>bdd_above {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
      proof-
        have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
          using \<open>bounded_linear f\<close>
          by (metis \<open>\<And>K. (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) \<le> norm x * K) = (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) / norm x \<le> K)\<close> bounded_linear.nonneg_bounded mult_divide_mult_cancel_left_if norm_zero real_divide_square_eq)
        thus ?thesis
          by auto 
      qed
      moreover have \<open>{norm (f x) / (norm x) | x. x = 0} \<noteq> {}\<close>
        by simp
      moreover have \<open>bdd_above {norm (f x) / (norm x) | x. x = 0}\<close>
        by simp
      ultimately show ?thesis
        by (metis (no_types, lifting) cSup_union_distrib sup_max)  
    qed      
    moreover have \<open>Sup {norm (f x) / (norm x) | x. x = 0} = 0\<close>
    proof-
      have \<open>{norm (f x) / (norm x) | x. x = 0} = {norm (f 0) / (norm 0)}\<close>
        by simp
      thus ?thesis
        by simp 
    qed
    moreover have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} \<ge> 0\<close>
    proof-
      have \<open>norm (f x) / (norm x) \<ge> 0\<close>
        for x
        by simp
      hence \<open>\<forall> y\<in>{norm (f x) / (norm x) | x. x \<noteq> 0}. y \<ge> 0\<close>
        by blast
      moreover have \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<noteq> {}\<close>
      proof-
        have \<open>\<exists> x::'a. x \<noteq> 0\<close>
          using \<open>UNIV\<noteq>{0}\<close> by auto
        thus ?thesis 
          by auto
      qed
      moreover have \<open>bdd_above {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
      proof-
        have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
          using \<open>bounded_linear f\<close>
          by (metis \<open>\<And>K. (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) \<le> norm x * K) = (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) / norm x \<le> K)\<close> bounded_linear.nonneg_bounded mult_divide_mult_cancel_left_if norm_zero real_divide_square_eq)
        thus ?thesis
          by auto 
      qed
      ultimately show ?thesis
        by (metis (lifting) \<open>\<forall>y\<in>{norm (f x) / norm x |x. x \<noteq> 0}. 0 \<le> y\<close> \<open>bdd_above {norm (f x) / norm x |x. x \<noteq> 0}\<close> \<open>{norm (f x) / norm x |x. x \<noteq> 0} \<noteq> {}\<close> bot.extremum_uniqueI cSup_upper2 subset_emptyI)        
    qed
    ultimately show ?thesis
      by linarith 
  qed
  ultimately have \<open>(SUP x. norm (f x) / (norm x)) = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
    by (simp add: full_SetCompr_eq)
  thus ?thesis
    by (simp add: onorm_def)
qed


subsection \<open>Banach-Steinhaus theorem\<close>

lemma bounded_linear_ball:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
    and K :: real
  assumes \<open>linear f\<close> and \<open>\<And> x. norm x = 1 \<Longrightarrow> norm (f x) \<le> K\<close>
  shows \<open>bounded_linear f\<close>
proof-
  have \<open>norm (f x) \<le> norm x * K\<close>
    for x
  proof(cases \<open>x = 0\<close>)
    case True
    thus ?thesis
      by (simp add: assms(1) linear_0) 
  next
    case False
    hence \<open>norm x > 0\<close>
      by simp
    hence \<open>norm (inverse (norm x) *\<^sub>R x) = 1\<close>
      by auto
    hence \<open>norm (f (inverse (norm x) *\<^sub>R x)) \<le> K\<close>
      using \<open>\<And> x. norm x = 1 \<Longrightarrow> norm (f x) \<le> K\<close>
      by blast
    hence \<open>norm (inverse (norm x) *\<^sub>R  (f x)) \<le> K\<close>
      by (simp add: assms(1) linear_scale)
    hence \<open>\<bar>inverse (norm x)\<bar> * norm (f x) \<le> K\<close>
      by simp
    hence \<open>inverse (norm x) * norm (f x) \<le> K\<close>
      using \<open>norm x > 0\<close>
      by simp
    show ?thesis 
    proof-
      have \<open>inverse (norm x) \<ge> 0\<close>
        using \<open>norm x > 0\<close>
        by simp
      moreover have \<open>norm (f x) \<ge> 0\<close>
        by simp
      moreover have \<open>K \<ge> 0\<close>
        using \<open>inverse (norm x) * norm (f x) \<le> K\<close> \<open>inverse (norm x) \<ge> 0\<close> \<open>norm x > 0\<close>
          calculation(2) 
        by (metis \<open>norm (f (x /\<^sub>R norm x)) \<le> K\<close> dual_order.trans norm_ge_zero)
      ultimately show ?thesis  using \<open>inverse (norm x) * norm (f x) \<le> K\<close>
      proof -
        have "\<forall>r. norm x * (inverse (norm x) * r) = r"
          by (metis \<open>norm (x /\<^sub>R norm x) = 1\<close> ab_semigroup_mult_class.mult_ac(1) abs_inverse abs_norm_cancel mult.commute mult.left_neutral norm_scaleR)
        hence "norm (f x) \<le> K * norm x"
          by (metis (no_types) \<open>inverse (norm x) * norm (f x) \<le> K\<close> mult.commute norm_ge_zero real_scaleR_def scaleR_left_mono)
        thus ?thesis
          by (metis mult.commute)
      qed  
    qed
  qed
  thus ?thesis using \<open>linear f\<close> unfolding bounded_linear_def bounded_linear_axioms_def by blast
qed

(* TODO: remove assumption "UNIV\<noteq>{0}" and add type class not_singleton instead *)
lemma norm_unit_sphere:
  fixes f::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
  assumes \<open>(UNIV::'a set) \<noteq> {0}\<close> and \<open>bounded_linear f\<close> and \<open>e > 0\<close>
  shows \<open>\<exists> x\<in>(sphere 0 1). norm (norm(f x) - (onorm f)) < e\<close>
proof-
  define S::\<open>real set\<close> where \<open>S = { norm (f x)| x. x \<in> sphere 0 1 }\<close>
  have \<open>S\<noteq>{}\<close>
  proof-
    have \<open>\<exists>x::'a. x \<in> sphere 0 1\<close>
      unfolding sphere_def apply auto using \<open>(UNIV::'a set) \<noteq> {0}\<close> ex_norm1
      by auto      
    thus ?thesis unfolding S_def by auto
  qed
  hence \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. Sup S - e < y\<close>
    for e
    by (simp add: less_cSupD)
  moreover have \<open>Sup S = onorm f\<close>
  proof-
    have \<open>onorm f = Sup { norm (f x)| x. norm x = 1 }\<close>
      using  \<open>(UNIV::'a set) \<noteq> {0}\<close> \<open>bounded_linear f\<close> onorm_sphere
      by blast
    hence \<open>onorm f = Sup { norm (f x)| x. x \<in> sphere 0 1 }\<close>
      unfolding sphere_def
      by simp
    thus ?thesis unfolding S_def by auto
  qed
  ultimately have \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. (onorm f) - e < y\<close>
    for e
    by simp
  hence \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. (onorm f) - y  < e\<close>
    for e
    by force
  hence \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. norm ((onorm f) - y)  < e\<close>
    for e
  proof-
    assume \<open>e > 0\<close>
    have \<open>\<exists> y \<in> S. (onorm f) - y  < e\<close>
      using \<open>0 < e\<close> \<open>\<And>e. 0 < e \<Longrightarrow> \<exists>y\<in>S. onorm f - y < e\<close> by auto
    then obtain y where \<open>y \<in> S\<close> and \<open>(onorm f) - y  < e\<close>
      by blast
    have  \<open>bdd_above S\<close>
    proof-
      have \<open>y \<in> {norm (f x) |x. x \<in> sphere 0 1} \<Longrightarrow> y \<le> onorm f\<close>
      proof-
        assume \<open>y \<in> {norm (f x) |x. x \<in> sphere 0 1}\<close>
        hence \<open>\<exists> x \<in> sphere 0 1. y = norm (f x)\<close>
          by blast
        then obtain x where \<open>x \<in> sphere 0 1\<close> and \<open>y = norm (f x)\<close>
          by blast
        from \<open>y = norm (f x)\<close>
        have \<open>y \<le> onorm f * norm x\<close>
          using assms(2) onorm by auto
        moreover have \<open>norm x = 1\<close>
          using  \<open>x \<in> sphere 0 1\<close> unfolding sphere_def by auto
        ultimately show ?thesis by simp
      qed
      hence \<open>bdd_above {norm (f x) |x. x \<in> sphere 0 1}\<close>
        using assms(2) bdd_above_norm_f by force
      thus ?thesis unfolding S_def by blast 
    qed
    hence \<open>y \<le> Sup S\<close>
      using \<open>y \<in> S\<close> \<open>S \<noteq> {}\<close> cSup_upper
      by blast
    hence \<open>0 \<le> Sup S - y\<close>
      by simp
    hence \<open>0 \<le> onorm f - y\<close>
      using \<open>Sup S = onorm f\<close>
      by simp
    hence \<open>\<bar> (onorm f - y) \<bar> = onorm f - y\<close>
      by simp
    hence \<open>norm (onorm f - y)  = onorm f - y\<close>
      by auto
    thus ?thesis
      using \<open>onorm f - y < e\<close> \<open>y \<in> S\<close> by force 
  qed
  hence \<open> 0 < e \<Longrightarrow> \<exists>y\<in>{norm (f x) |x. x \<in> sphere 0 1}. norm (onorm f - y) < e\<close>
    for e
    unfolding S_def by blast
  thus ?thesis 
  proof -
    assume a1: "\<And>e. 0 < e \<Longrightarrow> \<exists>y\<in>{norm (f x) |x. x \<in> sphere 0 1}. norm (onorm f - y) < e"
    have "\<forall>r. r \<notin> S \<or> (\<exists>a. r = norm (f a) \<and> a \<in> sphere 0 1)"
      using S_def by blast
    thus ?thesis
      using a1 \<open>\<And>e. 0 < e \<Longrightarrow> \<exists>y\<in>S. norm (onorm f - y) < e\<close> assms(3) by force 
  qed 
qed

lemma sphere_nonzero:
  assumes \<open>S \<subseteq> sphere 0 r\<close> and \<open>r > 0\<close> and \<open>x \<in> S\<close>
  shows \<open>x \<noteq> 0\<close>
proof-
  from \<open>S \<subseteq> sphere 0 r\<close> and  \<open>x \<in> S\<close>
  have  \<open>x \<in> sphere 0 r\<close>
    by blast
  hence \<open>dist x 0 = r\<close>
    by (simp add: dist_commute)     
  thus ?thesis using \<open>r > 0\<close>
    by auto
qed

subsection \<open>Uniform_limit_Missing\<close>

unbundle nsa_notation

abbreviation uniform_convergence_abbr::
  \<open>'a set \<Rightarrow> (nat \<Rightarrow> ('a \<Rightarrow>'b::metric_space)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  (\<open>(_): ((_)/ \<midarrow>uniformly\<rightarrow> (_))\<close> [60, 60, 60] 60)
  where \<open>S: f \<midarrow>uniformly\<rightarrow> l \<equiv> (  uniform_limit S f l sequentially )\<close>

subsection \<open>Nonstandard analog of uniform convergence\<close>

lemma nsuniform_convergence_D:
  fixes l::\<open>'a \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
    and S :: \<open>'a set\<close> and N::hypnat and x::\<open>'a star\<close>
  assumes \<open>S: f \<midarrow>uniformly\<rightarrow> l\<close> and \<open>N\<in>HNatInfinite\<close> and \<open>x\<in>*s* S\<close>
  shows \<open>(*f2* f) N x \<approx> (*f* l) x\<close>
proof-
  have \<open>(*f2* f) N x - (*f* l) x \<in> Infinitesimal\<close>
  proof (rule InfinitesimalI2)
    fix r :: real
    assume \<open>0 < r\<close>
    have \<open>\<exists> no. \<forall> n \<ge> no. \<forall> x\<in>S. norm (f n x - l x) < r\<close>
      using \<open>S: f \<midarrow>uniformly\<rightarrow> l\<close> \<open>0 < r\<close>
        dist_norm uniform_limit_sequentially_iff by metis
    then obtain no where \<open>\<forall> n \<ge> no. \<forall> x\<in>S. norm (f n x - l x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> no. \<forall> x\<in>S. norm ( f n x - l x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> hypnat_of_nat no. \<forall> x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x) < hypreal_of_real r\<close>
      by StarDef.transfer
    thus \<open>hnorm ((*f2* f) N x- (*f* l) x) < hypreal_of_real r\<close>
      using star_of_le_HNatInfinite \<open>N \<in> HNatInfinite\<close>
      by (simp add: \<open>x\<in>*s* S\<close>)
  qed
  thus \<open>(*f2* f) N x \<approx> (*f* l) x\<close>
    by (simp only: approx_def)
qed

lemma nsuniform_convergence_I:
  fixes l::\<open>'a \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
    and S :: \<open>'a set\<close>
  assumes \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x\<close>
  shows \<open>S: f \<midarrow>uniformly\<rightarrow> l\<close>
proof-
  have \<open>r > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>S. norm (f n x - l x) < r\<close>
    for r::real
  proof-
    assume \<open>r > 0\<close>
    from \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x\<close>
    have \<open>\<forall>n\<in>HNatInfinite.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
      by (simp add: InfinitesimalD2 Infinitesimal_approx_minus \<open>r > 0\<close>)
    have \<open>\<exists> no. \<forall>n \<ge> no.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
    proof-
      have \<open>n \<ge> whn \<Longrightarrow>
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
        for n
        using HNatInfinite_upward_closed HNatInfinite_whn
          \<open>\<forall>n\<in>HNatInfinite. \<forall>x\<in>*s* S. hnorm ((*f2* f) n x - (*f* l) x) < hypreal_of_real r\<close> 
        by blast     
      thus ?thesis by blast
    qed
    thus \<open>\<exists> no. \<forall>n \<ge> no. \<forall>x\<in>S. norm ( f n x - l x ) < r\<close>
      by StarDef.transfer
  qed
  thus ?thesis
    using dist_norm uniform_limit_sequentially_iff by metis
qed

proposition nsuniform_convergence_iff:
  fixes l::\<open>'a\<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
    and S :: \<open>'a set\<close>
  shows \<open>(S: f \<midarrow>uniformly\<rightarrow> l)\<longleftrightarrow>(\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x)\<close>
proof
  show "\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x"
    if "S: f \<midarrow>uniformly\<rightarrow> l"
    using that
    using nsuniform_convergence_D by blast 
  show "S: f \<midarrow>uniformly\<rightarrow> l"
    if "\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x"
    using that
    by (simp add: nsuniform_convergence_I) 
qed


lemma nsuniformly_Cauchy_on_D:
  fixes f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector)\<close> and S::\<open>'a set\<close> 
    and N::hypnat and x::\<open>'a star\<close>
  assumes  \<open>uniformly_Cauchy_on S f\<close> and \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close> and \<open>x\<in>*s* S\<close>
  shows \<open>(*f2* f) N x \<approx> (*f2* f) M x\<close>
proof-
  have \<open>(*f2* f) N x - (*f2* f) M x \<in> Infinitesimal\<close>
  proof (rule InfinitesimalI2)
    fix r :: real
    assume \<open>0 < r\<close>
    have \<open>\<exists> no. \<forall> n \<ge> no. \<forall> m \<ge> no. \<forall> x\<in>S. norm (f n x - f m x) < r\<close>
      using \<open>uniformly_Cauchy_on S f\<close> \<open>0 < r\<close>
      using dist_norm
      unfolding uniformly_Cauchy_on_def
      by metis
    then obtain no where \<open>\<forall> n \<ge> no. \<forall> m \<ge> no. \<forall> x\<in>S. norm (f n x - f m x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> no. \<forall> m \<ge> no. \<forall> x\<in>S. norm (f n x - f m x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> hypnat_of_nat no. \<forall> m \<ge> hypnat_of_nat no. 
      \<forall> x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x) < hypreal_of_real r\<close>
      by StarDef.transfer
    thus \<open>hnorm ((*f2* f) N x- (*f2* f) M x) < hypreal_of_real r\<close>
      using star_of_le_HNatInfinite \<open>N \<in> HNatInfinite\<close> \<open>M \<in> HNatInfinite\<close>
      by (simp add: \<open>x\<in>*s* S\<close>)
  qed
  thus \<open>(*f2* f) N x \<approx> (*f2* f) M x\<close>
    by (simp only: approx_def)
qed

lemma nsuniformly_Cauchy_on_I:
  fixes  f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector)\<close> and S::\<open>'a set\<close>
  assumes \<open>\<forall>N\<in>HNatInfinite. \<forall> M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x\<close>
  shows \<open>uniformly_Cauchy_on S f\<close>
proof-
  have \<open>r > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<forall> m\<ge>N. \<forall>x\<in>S. norm (f n x - f m x) < r\<close>
    for r::real
  proof-
    assume \<open>r > 0\<close>
    from \<open>\<forall>N\<in>HNatInfinite. \<forall> M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x\<close>
    have \<open>\<forall>n\<in>HNatInfinite. \<forall> m\<in>HNatInfinite.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x ) < hypreal_of_real r\<close>
      by (simp add: InfinitesimalD2 Infinitesimal_approx_minus \<open>r > 0\<close>)
    have \<open>\<exists> no. \<forall>n \<ge> no. \<forall> m \<ge> no.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x ) < hypreal_of_real r\<close>
    proof-
      have \<open>n \<ge> whn \<Longrightarrow> m \<ge> whn \<Longrightarrow>
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x ) < hypreal_of_real r\<close>
        for n m
        using HNatInfinite_upward_closed HNatInfinite_whn
          \<open>\<forall>n\<in>HNatInfinite. \<forall> m\<in>HNatInfinite. \<forall>x\<in>*s* S. hnorm ((*f2* f) n x - (*f2* f) m x) < hypreal_of_real r\<close> 
        by blast     
      thus ?thesis by blast
    qed
    thus \<open>\<exists> no. \<forall>n \<ge> no. \<forall> m \<ge> no. \<forall>x\<in>S. norm ( f n x - f m x ) < r\<close>
      by StarDef.transfer
  qed
  thus ?thesis
    using  dist_norm
    unfolding uniformly_Cauchy_on_def
    by metis
qed


proposition nsuniformly_Cauchy_on_iff:
  fixes  f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector)\<close> and S::\<open>'a set\<close>
  shows \<open>(uniformly_Cauchy_on S f) \<longleftrightarrow> 
    (\<forall>N\<in>HNatInfinite. \<forall> M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x)\<close>
proof
  show "\<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x"
    if "uniformly_Cauchy_on S f"
    using that
    using nsuniformly_Cauchy_on_D by blast 
  show "uniformly_Cauchy_on S f"
    if "\<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x"
    using that
    using nsuniformly_Cauchy_on_I by metis 
qed

subsection \<open>Nonstandard analog of uniform convergence on the unit (sphere 0 1) \<close>

lemma sphere_iff:
  \<open>x\<in>*s*(sphere 0 1) \<longleftrightarrow> hnorm x = 1\<close>
proof-
  have \<open>\<forall> xx.  xx\<in>(sphere 0 1) \<longleftrightarrow> norm xx = 1\<close>
    by simp
  hence \<open>\<forall> xx.  xx\<in>*s*(sphere 0 1) \<longleftrightarrow> hnorm xx = 1\<close>
    by StarDef.transfer
  thus ?thesis by blast
qed

lemma nsupointwise_convergence_I: 
  \<open>( \<And>N. \<And> x. N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x  \<approx> (*f* l) x )
   \<Longrightarrow> (sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close> 
proof-
  assume \<open>\<And>N x. N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
  hence \<open>\<forall>N\<in>HNatInfinite. \<forall>x. hnorm x = 1 \<longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
    by blast                
  hence \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s*(sphere 0 1).  (*f2* f) N x \<approx> (*f* l) x\<close>
    using sphere_iff by auto
  hence \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close>
    by (simp add: nsuniform_convergence_I)
  thus \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close>
    by blast
qed

lemma nsupointwise_convergence_D:
  \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l \<Longrightarrow> N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 
  \<Longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
proof-
  assume \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  have \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s*(sphere 0 1). (*f2* f) N x \<approx> (*f* l) x\<close>
    using nsuniform_convergence_D \<open>sphere 0 1: f \<midarrow>uniformly\<rightarrow> l\<close> by blast                     
  thus \<open>(*f2* f) N x \<approx> (*f* l) x\<close>
    by (simp add: \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> sphere_iff)
qed

lemma bounded_linear_HFinite:
  \<open>bounded_linear a \<Longrightarrow> hnorm x = 1 \<Longrightarrow> ((*f* a) x) \<in> HFinite\<close>
proof-
  {
    assume \<open>bounded_linear a\<close> and \<open>hnorm x = 1\<close>
    have \<open>\<And> t. norm t = 1 \<Longrightarrow> norm (a t) \<le> onorm a\<close>
      using \<open>bounded_linear a\<close> by (metis mult_cancel_left2 onorm)      
    hence  \<open>\<And> t. norm t = 1 \<Longrightarrow> norm (a t) < onorm a + 1\<close>
      by fastforce      
    hence  \<open>\<And> t. hnorm t = 1 \<Longrightarrow> hnorm ((*f* a) t) < star_of (onorm a + 1)\<close>
      by StarDef.transfer
    hence  \<open>hnorm ((*f* a) x) < star_of (onorm a + 1)\<close>
      using \<open>hnorm x = 1\<close>
      by auto
    hence \<open>\<exists>xa\<in>\<real>. hnorm ((*f* a) x) < xa\<close> by auto
  } note 1 = this
  assume \<open>bounded_linear a\<close> and \<open>hnorm x = 1\<close>
  thus ?thesis
    unfolding HFinite_def
    apply auto
    apply (rule 1)
    by auto
qed

lemma nsupointwise_convergence_mult: 
  fixes a b :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes \<open>sphere 0 1: X \<midarrow>uniformly\<rightarrow> a\<close> and \<open>sphere 0 1: Y \<midarrow>uniformly\<rightarrow> b\<close>
    and \<open>bounded_linear a\<close> and \<open>bounded_linear b\<close>
  shows \<open>sphere 0 1: (\<lambda>n. (\<lambda> t. X n t * Y n t)) \<midarrow>uniformly\<rightarrow> (\<lambda> t. a t * b t)\<close>
proof(rule nsupointwise_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using  \<open>sphere 0 1: X \<midarrow>uniformly\<rightarrow> a\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsupointwise_convergence_D by blast 
  moreover have \<open>(*f2* Y) N x \<approx> (*f* b) x\<close>
    using \<open>sphere 0 1: Y \<midarrow>uniformly\<rightarrow> b\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsupointwise_convergence_D by blast 
  moreover have \<open>((*f* a) x) \<in> HFinite\<close>
    using \<open>bounded_linear a\<close> \<open>hnorm x = 1\<close>
    by (simp add: bounded_linear_HFinite) 
  moreover have \<open>((*f* b) x) \<in> HFinite\<close>
    using \<open>bounded_linear b\<close> \<open>hnorm x = 1\<close>
    by (simp add: bounded_linear_HFinite)
  ultimately have \<open>(*f2* X) N x * (*f2* Y) N x \<approx> (*f* a) x * (*f* b) x\<close>
    using approx_mult_HFinite by auto
  moreover have \<open>(*f2* X) N x * (*f2* Y) N x = (*f2* (\<lambda>n t. X n t * Y n t)) N x\<close>
  proof-
    have \<open>\<forall> NN. \<forall> xx. X NN xx * Y NN xx = (\<lambda>n t. X n t * Y n t) NN xx\<close>
      by auto
    hence \<open>\<forall> NN. \<forall> xx. (*f2* X) NN xx * (*f2* Y) NN xx = (*f2* (\<lambda>n t. X n t * Y n t)) NN xx\<close>
      apply StarDef.transfer
      by auto
    thus ?thesis
      by simp  
  qed
  moreover have \<open>(*f* a) x * (*f* b) x = (*f* (\<lambda>t. a t * b t)) x\<close>
    by simp
  ultimately show \<open>(*f2* (\<lambda>n t. X n t * Y n t)) N x \<approx> (*f* (\<lambda>t. a t * b t)) x\<close>
    by metis
qed

lemma linear_ball_zero:
  \<open>linear f \<Longrightarrow>  \<forall> x. norm x = 1 \<longrightarrow> f x = 0 \<Longrightarrow> f = (\<lambda> _. 0)\<close>
proof
  show "f u = 0"
    if "linear f"
      and "\<forall>x. norm x = 1 \<longrightarrow> f x = 0"
    for u :: 'a
  proof(cases \<open>u = 0\<close>)
    case True
    thus ?thesis
      by (simp add: linear_0 that(1))
  next
    case False
    have \<open>norm ( (inverse (norm u)) *\<^sub>R u ) = 1\<close>
      by (simp add: False)
    hence \<open>f ( (inverse (norm u)) *\<^sub>R u ) = 0\<close>
      by (simp add: that(2))
    moreover have \<open>f ( (inverse (norm u)) *\<^sub>R u ) = (inverse (norm u)) *\<^sub>R (f  u)\<close>
      using \<open>linear f\<close> unfolding linear_def
      by (simp add: Real_Vector_Spaces.linear_def linear_scale) 
    ultimately have \<open>(inverse (norm u)) *\<^sub>R (f  u) = 0\<close>
      by simp
    moreover have \<open>(inverse (norm u)) \<noteq> 0\<close>
      using \<open>norm (u /\<^sub>R norm u) = 1\<close> by auto
    ultimately show ?thesis by simp
  qed
qed

lemma linear_ball_uniq:
  \<open>linear f \<Longrightarrow> linear g \<Longrightarrow> \<forall> x. norm x = 1 \<longrightarrow> f x = g x \<Longrightarrow> f = g\<close>
proof
  show "f x = g x"
    if "linear f"
      and "linear g"
      and "\<forall>x. norm x = 1 \<longrightarrow> f x = g x"
    for x :: 'a
  proof-
    have "\<forall>x. norm x = 1 \<longrightarrow> (\<lambda> t. f t - g t) x = 0"
      by (simp add: that(3))
    moreover have \<open>linear (\<lambda> t. f t - g t)\<close>
      using \<open>linear f\<close> \<open>linear g\<close>
      by (simp add: linear_compose_sub) 
    ultimately have \<open>(\<lambda> t. f t - g t) = (\<lambda> _. 0)\<close>
      using linear_ball_zero by fastforce
    thus ?thesis
      by (meson eq_iff_diff_eq_0) 
  qed
qed

lemma nsupointwise_convergence_unique: 
  fixes a b :: \<open>'a::real_normed_vector\<Rightarrow>'b::real_normed_vector\<close>
  assumes \<open>sphere 0 1:X \<midarrow>uniformly\<rightarrow> a\<close> and \<open>sphere 0 1:X \<midarrow>uniformly\<rightarrow> b\<close>
    and \<open>linear a\<close> and \<open>linear b\<close>
  shows \<open>a = b\<close>
proof-
  have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow>(*f2* X) N x \<approx> (*f* a) x\<close>
    using  \<open>sphere 0 1:X \<midarrow>uniformly\<rightarrow> a\<close>
    by (simp add: nsupointwise_convergence_D)
  moreover have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow> (*f2* X) N x \<approx> (*f* b) x\<close>
    using  \<open>sphere 0 1:X \<midarrow>uniformly\<rightarrow> b\<close>
    by (simp add: nsupointwise_convergence_D)
  ultimately have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow> (*f* a) x \<approx> (*f* b) x\<close>
    by (simp add: approx_monad_iff)
  hence \<open>\<forall> x. hnorm x = 1 \<longrightarrow> (*f* a) x \<approx> (*f* b) x\<close>
    by (meson NSLIMSEQ_def NSLIMSEQ_unique zero_neq_one)
  have \<open>norm t = 1 \<Longrightarrow> a t = b t\<close>
    for t
  proof-
    assume \<open>norm t = 1\<close>
    hence \<open>hnorm (star_of t) = 1\<close>
      by (metis star_of_norm star_one_def)
    hence \<open>(*f* a) (star_of t) \<approx> (*f* b) (star_of t)\<close>
      using \<open>\<forall>x. hnorm x = 1 \<longrightarrow> (*f* a) x \<approx> (*f* b) x\<close> by blast
    thus ?thesis
      by simp 
  qed
  thus ?thesis using linear_ball_uniq  \<open>linear a\<close>  \<open>linear b\<close>
    by blast
qed

unbundle no_nsa_notation


end

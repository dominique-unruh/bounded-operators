section\<open>Preliminaries\<close>

theory Preliminaries
  imports
    Complex_Main            
    "HOL-Analysis.Infinite_Set_Sum"
    "HOL-ex.Sketch_and_Explore" 
    HOL.Groups
    (* "HOL-Nonstandard_Analysis.Nonstandard_Analysis"     *)
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

  Extra_General

begin

subsection\<open>General Results Missing\<close>

typedef 'a euclidean_space = "UNIV :: ('a \<Rightarrow> real) set" ..
setup_lifting type_definition_euclidean_space

instantiation euclidean_space :: (type) real_vector begin
lift_definition plus_euclidean_space ::
  "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space"
  is "\<lambda>f g x. f x + g x" .
lift_definition zero_euclidean_space :: "'a euclidean_space" is "\<lambda>_. 0" .
lift_definition uminus_euclidean_space :: 
  "'a euclidean_space \<Rightarrow> 'a euclidean_space" 
  is "\<lambda>f x. - f x" .
lift_definition minus_euclidean_space :: 
  "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" 
  is "\<lambda>f g x. f x - g x".
lift_definition scaleR_euclidean_space :: 
  "real \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" 
  is "\<lambda>c f x. c * f x" .
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
  proof transfer
    fix x y z::"'a \<Rightarrow> real"
    have "(\<Sum>i\<in>UNIV. (x i + y i) * z i) = (\<Sum>i\<in>UNIV. x i * z i + y i * z i)"
      by (simp add: distrib_left mult.commute)
    thus "(\<Sum>i\<in>UNIV. (x i + y i) * z i) = (\<Sum>j\<in>UNIV. x j * z j) + (\<Sum>k\<in>UNIV. y k * z k)"
      by (subst sum.distrib[symmetric])      
  qed

  show "r *\<^sub>R x \<bullet> y = r * (x \<bullet> y)" for r
  proof transfer
    fix r and x y::"'a\<Rightarrow>real"
    have "(\<Sum>i\<in>UNIV. r * x i * y i) = (\<Sum>i\<in>UNIV. r * (x i * y i))"
      by (simp add: mult.assoc)
    thus "(\<Sum>i\<in>UNIV. r * x i * y i) = r * (\<Sum>j\<in>UNIV. x j * y j)"
      by (subst sum_distrib_left)
  qed
  show "0 \<le> x \<bullet> x"
    apply transfer
    by (simp add: sum_nonneg)
  show "(x \<bullet> x = 0) = (x = 0)"
  proof (transfer, rule)
    fix f :: "'a \<Rightarrow> real"
    assume "(\<Sum>i\<in>UNIV. f i * f i) = 0"
    hence "f x * f x = 0" for x
      apply (rule_tac sum_nonneg_eq_0_iff[THEN iffD1, rule_format, where A=UNIV and x=x])
      by auto
    thus "f = (\<lambda>_. 0)"
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
  assumes "x \<le> a" and "y \<le> a" and "0 \<le> u" and "0 \<le> v" and "u + v = 1"
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
  assume t1: "a \<le> b" and t2: "0 \<le> c"
  thus "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
  from t2 show "a * c \<le> b * c"
    unfolding le_less
    by (metis local.antisym_conv2 local.mult_not_zero local.mult_strict_right_mono t1)    
qed

lemma mult_pos_pos[simp]: "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a * b"
  using mult_strict_left_mono [of 0 b a] by simp

lemma mult_pos_neg: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> a * b < 0"
  using mult_strict_left_mono [of b 0 a] by simp

lemma mult_neg_pos: "a < 0 \<Longrightarrow> 0 < b \<Longrightarrow> a * b < 0"
  using mult_strict_right_mono [of a 0 b] by simp

text \<open>Strict monotonicity in both arguments\<close>
lemma mult_strict_mono:
  assumes t1: "a < b" and t2: "c < d" and t3: "0 < b" and t4: "0 \<le> c"
  shows "a * c < b * d"
proof-
  have "a * c < b * d"
    by (metis local.dual_order.order_iff_strict local.dual_order.strict_trans2 
        local.mult_strict_left_mono local.mult_strict_right_mono local.mult_zero_right t1 t2 t3 t4)        
  thus ?thesis
    using assms by blast
qed


text \<open>This weaker variant has more natural premises\<close>
lemma mult_strict_mono':
  assumes "a < b" and "c < d" and "0 \<le> a" and "0 \<le> c"
  shows "a * c < b * d"
  by (rule mult_strict_mono) (insert assms, auto)

lemma mult_less_le_imp_less:
  assumes t1: "a < b" and t2: "c \<le> d" and t3: "0 \<le> a" and t4: "0 < c"
  shows "a * c < b * d"
  using local.mult_strict_mono' local.mult_strict_right_mono local.order.order_iff_strict 
    t1 t2 t3 t4 by auto

lemma mult_le_less_imp_less:
  assumes "a \<le> b" and "c < d" and "0 < a" and "0 \<le> c"
  shows "a * c < b * d"
  by (metis assms(1) assms(2) assms(3) assms(4) local.antisym_conv2 local.dual_order.strict_trans1 
      local.mult_strict_left_mono local.mult_strict_mono)

end

subclass (in linordered_semiring_strict) ordered_semiring_strict 
proof
  show "c * a < c * b"
    if "a < b"
      and "0 < c"
    for a :: 'a
      and b 
      and c 
    using that
    by (simp add: local.mult_strict_left_mono) 
  show "a * c < b * c"
    if "a < b"
      and "0 < c"
    for a :: 'a
      and b 
      and c 
    using that
    by (simp add: local.mult_strict_right_mono) 
qed

class ordered_semiring_1_strict = ordered_semiring_strict + semiring_1
  \<comment> \<open>missing class analogous to \<^class>\<open>linordered_semiring_1_strict\<close> without requiring 
  a total order\<close>
begin

subclass ordered_semiring_1 ..

lemma convex_bound_lt:
  assumes "x < a" and "y < a" and "0 \<le> u" and "0 \<le> v" and "u + v = 1"
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
  assume "a < b" and "0 < c"
  thus "c * a < c * b"
    by (rule comm_mult_strict_left_mono)
  thus "a * c < b * c"
    by (simp only: mult.commute)
qed

subclass ordered_cancel_comm_semiring
proof
  fix a b c :: 'a
  assume "a \<le> b" and "0 \<le> c"
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

class ordered_field = field + order + ordered_comm_semiring_strict + ordered_ab_group_add 
  + partial_abs_if 
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
    and abs_nn: "\<bar>x\<bar> \<ge> 0"
begin

subclass (in linordered_field) nice_ordered_field
proof
  show "\<bar>a\<bar> = - a"
    if "a \<le> 0"
    for a :: 'a
    using that
    by simp 
  show "\<bar>a\<bar> = a"
    if "0 \<le> a"
    for a :: 'a
    using that
    by simp 
  show "0 < inverse a"
    if "0 < a"
    for a :: 'a
    using that
    by simp 
  show "b \<le> a"
    if "inverse a \<le> inverse b"
      and "0 < a"
    for a :: 'a
      and b
    using that
    using local.inverse_le_imp_le by blast 
  show "y \<le> z"
    if "\<And>x::'a. x < y \<Longrightarrow> x \<le> z"
    for y
      and z
    using that
    using local.dense_le by blast 
  show "a \<le> b \<or> b \<le> a"
    if "0 \<le> a"
      and "0 \<le> b"
    for a :: 'a
      and b
    using that
    by auto 
  show "0 \<le> \<bar>x\<bar>"
    for x :: 'a
    by simp    
qed

lemma comparable:
  assumes h1: "a \<le> c \<or> a \<ge> c"
    and h2: "b \<le> c \<or> b \<ge> c"
  shows "a \<le> b \<or> b \<le> a"
proof-
  have "a \<le> b"
    if t1: "\<not> b \<le> a" and t2: "a \<le> c" and t3: "b \<le> c"
  proof-
    have "0 \<le> c-a"
      by (simp add: t2)      
    moreover have "0 \<le> c-b"
      by (simp add: t3)      
    ultimately have "c-a \<le> c-b \<or> c-a \<ge> c-b" by (rule nn_comparable)
    hence "-a \<le> -b \<or> -a \<ge> -b"
      using local.add_le_imp_le_right local.uminus_add_conv_diff by presburger
    thus ?thesis
      by (simp add: t1)
  qed
  moreover have "a \<le> b"
    if t1: "\<not> b \<le> a" and t2: "c \<le> a" and t3: "b \<le> c"
  proof-
    have "b \<le> a"       
      using local.dual_order.trans t2 t3 by blast 
    thus ?thesis
      using t1 by auto
  qed
  moreover have "a \<le> b"
    if t1: "\<not> b \<le> a" and t2: "c \<le> a" and t3: "c \<le> b"
  proof-
    have "0 \<le> a-c"
      by (simp add: t2)        
    moreover have "0 \<le> b-c"
      by (simp add: t3)      
    ultimately have "a-c \<le> b-c \<or> a-c \<ge> b-c" by (rule nn_comparable)
    hence "a \<le> b \<or> a \<ge> b"
      by (simp add: local.le_diff_eq)
    thus ?thesis
      by (simp add: t1)
  qed
  ultimately show ?thesis using assms by auto
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
proof-
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
  "\<forall>x. \<exists>y. y > x"
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
  using assms by (metis local.dual_order.strict_iff_order 
      local.inverse_inverse_eq local.inverse_le_imp_le local.positive_imp_inverse_positive)

lemma inverse_less_imp_less:
  "inverse a < inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b < a"
  using local.inverse_le_imp_le local.order.strict_iff_order by blast

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
  by (metis local.inverse_le_imp_le local.inverse_minus_eq local.neg_0_less_iff_less 
      local.neg_le_iff_le)

lemma inverse_less_imp_less_neg:
  "inverse a < inverse b \<Longrightarrow> b < 0 \<Longrightarrow> b < a"
  using local.dual_order.strict_iff_order local.inverse_le_imp_le_neg by blast

lemma inverse_less_iff_less_neg [simp]:
  "a < 0 \<Longrightarrow> b < 0 \<Longrightarrow> inverse a < inverse b \<longleftrightarrow> b < a"
  by (metis local.antisym_conv2 local.inverse_less_imp_less_neg local.negative_imp_inverse_negative 
      local.nonzero_inverse_inverse_eq local.order.strict_implies_order)

lemma le_imp_inverse_le_neg:
  "a \<le> b \<Longrightarrow> b < 0 \<Longrightarrow> inverse b \<le> inverse a"
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
  using assms by (metis local.divide_eq_imp local.divide_inverse_commute 
      local.dual_order.order_iff_strict local.dual_order.strict_iff_order 
      local.mult_right_mono local.mult_strict_left_mono local.nonzero_divide_eq_eq 
      local.order.strict_implies_order local.positive_imp_inverse_positive)

lemma pos_less_divide_eq [field_simps]:
  assumes "0 < c"
  shows "a < b / c \<longleftrightarrow> a * c < b"
  using assms local.dual_order.strict_iff_order local.nonzero_divide_eq_eq local.pos_le_divide_eq 
  by auto

lemma neg_less_divide_eq [field_simps]:
  assumes "c < 0"
  shows "a < b / c \<longleftrightarrow> b < a * c"
  by (metis assms local.minus_divide_divide local.mult_minus_right local.neg_0_less_iff_less 
      local.neg_less_iff_less local.pos_less_divide_eq)

lemma neg_le_divide_eq [field_simps]:
  assumes "c < 0"
  shows "a \<le> b / c \<longleftrightarrow> b \<le> a * c"
  by (metis assms local.dual_order.order_iff_strict local.dual_order.strict_iff_order 
      local.neg_less_divide_eq local.nonzero_divide_eq_eq)

lemma pos_divide_le_eq [field_simps]:
  assumes "0 < c"
  shows "b / c \<le> a \<longleftrightarrow> b \<le> a * c"
  by (metis assms local.dual_order.strict_iff_order local.nonzero_eq_divide_eq 
      local.pos_le_divide_eq)

lemma pos_divide_less_eq [field_simps]:
  assumes "0 < c"
  shows "b / c < a \<longleftrightarrow> b < a * c"
  by (metis assms local.minus_divide_left local.mult_minus_left local.neg_less_iff_less 
      local.pos_less_divide_eq)

lemma neg_divide_le_eq [field_simps]:
  assumes "c < 0"
  shows "b / c \<le> a \<longleftrightarrow> a * c \<le> b"
  by (metis assms local.minus_divide_left local.mult_minus_left local.neg_le_divide_eq 
      local.neg_le_iff_le)

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
of positivity/negativity needed for \<open>field_simps\<close>. Have not added \<open>sign_simps\<close> to \<open>field_simps\<close> 
  because the former can lead to case explosions.\<close>

lemma divide_pos_pos[simp]:
  "0 < x \<Longrightarrow> 0 < y \<Longrightarrow> 0 < x / y"
  by(simp add:field_simps)

lemma divide_nonneg_pos:
  "0 \<le> x \<Longrightarrow> 0 < y \<Longrightarrow> 0 \<le> x / y"
  by(simp add:field_simps)

lemma divide_neg_pos:
  "x < 0 \<Longrightarrow> 0 < y \<Longrightarrow> x / y < 0"
  by(simp add:field_simps)

lemma divide_nonpos_pos:
  "x \<le> 0 \<Longrightarrow> 0 < y \<Longrightarrow> x / y \<le> 0"
  by(simp add:field_simps)

lemma divide_pos_neg:
  "0 < x \<Longrightarrow> y < 0 \<Longrightarrow> x / y < 0"
  by(simp add:field_simps)

lemma divide_nonneg_neg:
  "0 \<le> x \<Longrightarrow> y < 0 \<Longrightarrow> x / y \<le> 0"
  by(simp add:field_simps)

lemma divide_neg_neg:
  "x < 0 \<Longrightarrow> y < 0 \<Longrightarrow> 0 < x / y"
  by(simp add:field_simps)

lemma divide_nonpos_neg:
  "x \<le> 0 \<Longrightarrow> y < 0 \<Longrightarrow> 0 \<le> x / y"
  by(simp add:field_simps)

lemma divide_strict_right_mono:
  "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a / c < b / c"
  by (simp add: less_imp_not_eq2 divide_inverse mult_strict_right_mono
      positive_imp_inverse_positive)


lemma divide_strict_right_mono_neg:
  "b < a \<Longrightarrow> c < 0 \<Longrightarrow> a / c < b / c"
  by (simp add: local.neg_less_divide_eq)

text\<open>The last premise ensures that \<^term>\<open>a\<close> and \<^term>\<open>b\<close>
      have the same sign\<close>
lemma divide_strict_left_mono:
  "b < a \<Longrightarrow> 0 < c \<Longrightarrow> 0 < a*b \<Longrightarrow> c / a < c / b"
  by (metis local.divide_neg_pos local.dual_order.strict_iff_order local.frac_less_eq local.less_iff_diff_less_0 local.mult_not_zero local.mult_strict_left_mono)

lemma divide_left_mono:
  "b \<le> a \<Longrightarrow> 0 \<le> c \<Longrightarrow> 0 < a*b \<Longrightarrow> c / a \<le> c / b"
  using local.divide_cancel_left local.divide_strict_left_mono local.dual_order.order_iff_strict by auto

lemma divide_strict_left_mono_neg:
  "a < b \<Longrightarrow> c < 0 \<Longrightarrow> 0 < a*b \<Longrightarrow> c / a < c / b"
  by (metis local.divide_strict_left_mono local.minus_divide_left local.neg_0_less_iff_less local.neg_less_iff_less mult_commute)

lemma mult_imp_div_pos_le: "0 < y \<Longrightarrow> x \<le> z * y \<Longrightarrow> x / y \<le> z"
  by (subst pos_divide_le_eq, assumption+)

lemma mult_imp_le_div_pos: "0 < y \<Longrightarrow> z * y \<le> x \<Longrightarrow> z \<le> x / y"
  by(simp add:field_simps)

lemma mult_imp_div_pos_less: "0 < y \<Longrightarrow> x < z * y \<Longrightarrow> x / y < z"
  by(simp add:field_simps)

lemma mult_imp_less_div_pos: "0 < y \<Longrightarrow> z * y < x \<Longrightarrow> z < x / y"
  by(simp add:field_simps)

lemma frac_le: "0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> 0 < w \<Longrightarrow> w \<le> z  \<Longrightarrow> x / z \<le> y / w"
  using local.mult_imp_div_pos_le local.mult_imp_le_div_pos local.mult_mono by auto

lemma frac_less: "0 \<le> x \<Longrightarrow> x < y \<Longrightarrow> 0 < w \<Longrightarrow> w \<le> z \<Longrightarrow> x / z < y / w"
proof-
  assume a1: "w \<le> z"
  assume a2: "0 < w"
  assume a3: "0 \<le> x"
  assume a4: "x < y"
  have f5: "a = 0 \<or> (b = c / a) = (b * a = c)"
    for a b c::'a
    by (meson local.nonzero_eq_divide_eq)
  have f6: "0 < z"
    using a2 a1 by (meson local.order.ordering_axioms ordering.strict_trans2)
  have "z \<noteq> 0"
    using a2 a1 by (meson local.leD)
  moreover have "x / z \<noteq> y / w"
    using a1 a2 a3 a4 local.frac_eq_eq local.mult_less_le_imp_less by fastforce
  ultimately have "x / z \<noteq> y / w"
    using f5 by (metis (no_types))
  thus ?thesis
    using a4 a3 a2 a1 by (meson local.frac_le local.order.not_eq_order_implies_strict 
        local.order.strict_implies_order)
qed


lemma frac_less2: "0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> 0 < w \<Longrightarrow> w < z  \<Longrightarrow> x / z < y / w"
  by (metis local.antisym_conv2 local.divide_cancel_left local.dual_order.strict_implies_order 
      local.frac_le local.frac_less)

lemma less_half_sum: "a < b \<Longrightarrow> a < (a+b) / (1+1)"
  by (metis local.add_pos_pos local.add_strict_left_mono local.mult_imp_less_div_pos local.semiring_normalization_rules(4) local.zero_less_one mult_commute)

lemma gt_half_sum: "a < b \<Longrightarrow> (a+b)/(1+1) < b"
  by (metis local.add_pos_pos local.add_strict_left_mono local.mult_imp_div_pos_less local.semiring_normalization_rules(24) local.semiring_normalization_rules(4) local.zero_less_one mult_commute)

subclass unbounded_dense_order
proof
  fix x y :: 'a
  have less_add_one: "a < a + 1" for a::'a by auto
  from less_add_one show "\<exists>y. x < y"
    by blast 

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
    and *: "\<And>w. \<lbrakk> x < w ; w < y \<rbrakk> \<Longrightarrow> w \<le> z"
  shows "y \<le> z"
proof (rule dense_le)
  fix w assume "w < y"
  from dense[OF \<open>x < y\<close>] obtain u where "x < u" "u < y" by safe
  have "u \<le> w \<or> w \<le> u"
    using \<open>u < y\<close> \<open>w < y\<close> comparable local.order.strict_implies_order by blast
  thus "w \<le> z"
    using "*" \<open>u < y\<close> \<open>w < y\<close> \<open>x < u\<close> local.dual_order.trans local.order.strict_trans2 by blast
qed

subclass field_abs_sgn ..


lemma nonzero_abs_inverse:
  "a \<noteq> 0 \<Longrightarrow> \<bar>inverse a\<bar> = inverse \<bar>a\<bar>"
  by (rule abs_inverse)

lemma nonzero_abs_divide:
  "b \<noteq> 0 \<Longrightarrow> \<bar>a / b\<bar> = \<bar>a\<bar> / \<bar>b\<bar>"
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
  using local.positive_imp_inverse_positive by fastforce

lemma inverse_negative_iff_negative [simp]:
  "(inverse a < 0) = (a < 0)"
  using local.negative_imp_inverse_negative by fastforce

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
    using comparable invx1 local.order.strict_implies_order local.zero_less_one by blast
  then consider (leq0) "inverse x \<le> 0" | (pos) "inverse x > 0" | (zero) "inverse x = 0"
    using local.antisym_conv1 by blast
  thus "x \<le> 0 \<or> 1 < x"
    by (metis invx1 local.eq_iff local.inverse_1 local.inverse_less_imp_less 
        local.inverse_nonpositive_iff_nonpositive local.inverse_positive_imp_positive)
next
  assume "x \<le> 0 \<or> 1 < x"
  then consider (neg) "x \<le> 0" | (g1) "1 < x" by auto
  thus "inverse x < 1"
    by (metis local.dual_order.not_eq_order_implies_strict local.dual_order.strict_trans
        local.inverse_1 local.inverse_negative_iff_negative local.inverse_zero 
        local.less_imp_inverse_less local.zero_less_one)  
qed

lemma inverse_le_1_iff: "inverse x \<le> 1 \<longleftrightarrow> x \<le> 0 \<or> 1 \<le> x"
  by (metis local.dual_order.order_iff_strict local.inverse_1 local.inverse_le_iff_le 
      local.inverse_less_1_iff local.one_le_inverse_iff)

text\<open>Simplify expressions such as \<open>0 < 1/x\<close> to \<open>0 < x\<close>\<close>

lemma zero_le_divide_1_iff [simp]:
  "0 \<le> 1 / a \<longleftrightarrow> 0 \<le> a"
  using local.dual_order.order_iff_strict local.inverse_eq_divide 
    local.inverse_positive_iff_positive by auto

lemma zero_less_divide_1_iff [simp]:
  "0 < 1 / a \<longleftrightarrow> 0 < a"
  by (simp add: local.dual_order.strict_iff_order)

lemma divide_le_0_1_iff [simp]:
  "1 / a \<le> 0 \<longleftrightarrow> a \<le> 0"
  by (smt local.abs_0 local.abs_1 local.abs_divide local.abs_neg local.abs_nn 
      local.divide_cancel_left local.le_minus_iff local.minus_divide_right local.zero_neq_one)

lemma divide_less_0_1_iff [simp]:
  "1 / a < 0 \<longleftrightarrow> a < 0"
  using local.dual_order.strict_iff_order by auto

lemma divide_right_mono:
  "a \<le> b \<Longrightarrow> 0 \<le> c \<Longrightarrow> a/c \<le> b/c"
  using local.divide_cancel_right local.divide_strict_right_mono local.dual_order.order_iff_strict by blast

lemma divide_right_mono_neg: "a \<le> b
    \<Longrightarrow> c \<le> 0 \<Longrightarrow> b / c \<le> a / c"
  by (metis local.divide_cancel_right local.divide_strict_right_mono_neg local.dual_order.strict_implies_order local.eq_refl local.le_imp_less_or_eq)

lemma divide_left_mono_neg: "a \<le> b
    \<Longrightarrow> c \<le> 0 \<Longrightarrow> 0 < a * b \<Longrightarrow> c / a \<le> c / b"  
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
  by (metis local.divide_le_eq_1_pos local.minus_divide_divide local.neg_0_less_iff_less 
      local.neg_le_iff_le)

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

lemma abs_div_pos: "0 < y \<Longrightarrow>
    \<bar>x\<bar> / y = \<bar>x / y\<bar>"
  by (simp add: local.abs_pos)

lemma zero_le_divide_abs_iff [simp]: "(0 \<le> a / \<bar>b\<bar>) = (0 \<le> a | b = 0)"
proof 
  assume assm: "0 \<le> a / \<bar>b\<bar>"
  have absb: "abs b \<ge> 0" by (fact abs_nn)
  thus "0 \<le> a \<or> b = 0"
    using absb assm local.abs_eq_0_iff local.mult_nonneg_nonneg by fastforce
next
  assume "0 \<le> a \<or> b = 0"
  then consider (a) "0 \<le> a" | (b) "b = 0" by atomize_elim auto
  thus "0 \<le> a / \<bar>b\<bar>"
    by (metis local.abs_eq_0_iff local.abs_nn local.divide_eq_0_iff local.divide_nonneg_nonneg)
qed


lemma divide_le_0_abs_iff [simp]: "(a / \<bar>b\<bar> \<le> 0) = (a \<le> 0 | b = 0)"
  by (metis local.minus_divide_left local.neg_0_le_iff_le local.zero_le_divide_abs_iff)

text\<open>For creating values between \<^term>\<open>u\<close> and \<^term>\<open>v\<close>.\<close>
lemma scaling_mono:
  assumes "u \<le> v" and "0 \<le> r" and "r \<le> s"
  shows "u + r * (v - u) / s \<le> v"
proof -
  have "r/s \<le> 1" using assms
    by (metis local.divide_le_eq_1_pos local.division_ring_divide_zero 
        local.dual_order.order_iff_strict local.dual_order.trans local.zero_less_one)
  hence "(r/s) * (v - u) \<le> 1 * (v - u)"
    using assms(1) local.diff_ge_0_iff_ge local.mult_right_mono by blast
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
  have "rb \<le> ra"
    if "1 / ra \<le> (if rb = 0 then 0 else 1 / rb)" 
      and "ia = 0" and "0 < ra" and "ib = 0"
  proof(cases "rb = 0")
    case True
    thus ?thesis
      using that(3) by auto 
  next
    case False
    thus ?thesis
      by (smt nice_ordered_field_class.frac_less2 that(1) that(3)) 
  qed
  thus "inverse a \<le> inverse b \<Longrightarrow> 0 < a \<Longrightarrow> b \<le> a" unfolding defs ri
    by (auto simp: power2_eq_square) 
  show "(\<And>a. a < b \<Longrightarrow> a \<le> c) \<Longrightarrow> b \<le> c" unfolding defs ri
    by (metis complex.sel(1) complex.sel(2) dense less_le_not_le 
        nice_ordered_field_class.linordered_field_no_lb not_le_imp_less)    
  show "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> a \<le> b \<or> b \<le> a" unfolding defs by auto
  show "0 \<le> \<bar>x\<bar>" unfolding defs by auto
qed
end

lemma less_eq_complexI: "Re x \<le> Re y \<Longrightarrow> Im x = Im y \<Longrightarrow> x\<le>y" unfolding less_eq_complex_def 
  by simp
lemma less_complexI: "Re x < Re y \<Longrightarrow> Im x = Im y \<Longrightarrow> x<y" unfolding less_complex_def 
  by simp

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
  assumes t1: "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsetsum'_converges f A = infsetsum'_converges g A"
proof-
  have "sum f X = sum g X"
    if "finite X" and "X \<subseteq> A"
    for X
    by (meson Finite_Cartesian_Product.sum_cong_aux subsetD t1 that(2))    
  hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x = sum g x"
    by (simp add: eventually_finite_subsets_at_top_weakI)
  hence  "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A) =
         (sum g \<longlongrightarrow> x) (finite_subsets_at_top A)"
    for x
    by (simp add: filterlim_cong)
  thus ?thesis
    by (simp add: infsetsum'_converges_def)
qed

lemma infsetsum'_cong:
  assumes "\<And>x. x\<in>A \<Longrightarrow> f x = g x"
  shows "infsetsum' f A = infsetsum' g A"
proof-
  have "sum f X = sum g X"
    if "finite X" and "X \<subseteq> A"
    for X
    by (meson Finite_Cartesian_Product.sum_cong_aux assms in_mono that(2))    
  hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x = sum g x"
    by (rule eventually_finite_subsets_at_top_weakI)
  hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A) \<longleftrightarrow> (sum g \<longlongrightarrow> x) (finite_subsets_at_top A)" 
    for x
    by (rule tendsto_cong)
  hence "Lim (finite_subsets_at_top A) (sum f) = Lim (finite_subsets_at_top A) (sum g)"
    unfolding Topological_Spaces.Lim_def[abs_def]
    by auto
  thus ?thesis
    unfolding infsetsum'_def
    using assms infsetsum'_converges_cong by auto
qed

lemma abs_summable_finiteI0:
  assumes "\<And>F. finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum (\<lambda>x. norm (f x)) F \<le> B"
    and "B \<ge> 0"
  shows "f abs_summable_on S" and "infsetsum (\<lambda>x. norm (f x)) S \<le> B"
proof-
  have t1: "f abs_summable_on S \<and> infsetsum (\<lambda>x. norm (f x)) S \<le> B"
  proof(cases "S = {}")
    case True
    thus ?thesis
      by (simp add: assms(2)) 
  next
    case False
    define M normf where "M = count_space S" and "normf x = ennreal (norm (f x))" for x
    have "sum normf F \<le> ennreal B"
      if "finite F" and "F \<subseteq> S" and
        "\<And>F. finite F \<Longrightarrow> F \<subseteq> S \<Longrightarrow> (\<Sum>i\<in>F. ennreal (norm (f i))) \<le> ennreal B" and
        "ennreal 0 \<le> ennreal B"
      for F
      using that unfolding normf_def[symmetric] by simp    
    hence normf_B: "finite F \<Longrightarrow> F\<subseteq>S \<Longrightarrow> sum normf F \<le> ennreal B" for F
      using assms[THEN ennreal_leI] 
      by auto
    have "integral\<^sup>S M g \<le> B" if "simple_function M g" and "g \<le> normf" for g 
    proof -
      define gS where "gS = g ` S"
      have "finite gS"
        using that unfolding gS_def M_def simple_function_count_space by simp
      have "gS \<noteq> {}" unfolding gS_def False
        by (simp add: False) 
      define part where "part r = g -` {r} \<inter> S" for r
      have r_finite: "r < \<infinity>" if "r : gS" for r 
        using \<open>g \<le> normf\<close> that unfolding gS_def le_fun_def normf_def apply auto
        using ennreal_less_top neq_top_trans top.not_eq_extremum by blast
      define B' where "B' r = (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum normf F)" for r
      have B'fin: "B' r < \<infinity>" for r
      proof -
        have "B' r \<le> (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum normf F)"
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
        have c1: "\<exists>y. B' r \<le> sum normf y + \<epsilon>N \<and>
             finite y \<and> y \<subseteq> part r"
          if "B' r = 0"
          for r
          using that by auto
        have c2: "\<exists>y. B' r \<le> sum normf y + \<epsilon>N \<and>
             finite y \<and> y \<subseteq> part r"
          if "B' r \<noteq> 0"
          for r
        proof-
          have "B' r - \<epsilon>N < B' r"
            using B'fin \<open>0 < \<epsilon>N\<close> ennreal_between that by fastforce
          have "B' r - \<epsilon>N < Sup (sum normf ` {F. finite F \<and> F \<subseteq> part r}) \<Longrightarrow>
               \<exists>F. B' r - \<epsilon>N \<le> sum normf F \<and> finite F \<and> F \<subseteq> part r"
            by (metis (no_types, lifting) leD le_cases less_SUP_iff mem_Collect_eq)
          hence "B' r - \<epsilon>N < B' r \<Longrightarrow>
                \<exists>F. B' r - \<epsilon>N \<le> sum normf F \<and>
                finite F \<and> F \<subseteq> part r"
            by (subst (asm) (2) B'_def)
          then obtain F where "B' r - \<epsilon>N \<le> sum normf F" and "finite F" and "F \<subseteq> part r"
            using \<open>B' r - \<epsilon>N < B' r\<close> by auto  
          thus "\<exists>F. B' r \<le> sum normf F + \<epsilon>N \<and> finite F \<and> F \<subseteq> part r"
            by (metis add.commute ennreal_minus_le_iff)
        qed
        have "\<forall>x. \<exists>y. B' x \<le> sum normf y + \<epsilon>N \<and>
            finite y \<and> y \<subseteq> part x"
          using c1 c2
          by blast 
        hence "\<exists>F. \<forall>x. B' x \<le> sum normf (F x) + \<epsilon>N \<and> finite (F x) \<and> F x \<subseteq> part x"
          by metis 
        then obtain F where F: "sum normf (F r) + \<epsilon>N \<ge> B' r" and Ffin: "finite (F r)" and Fpartr: "F r \<subseteq> part r" for r
          using atomize_elim by auto
        have w1: "finite gS"
          by (simp add: \<open>finite gS\<close>)          
        have w2: "\<forall>i\<in>gS. finite (F i)"
          by (simp add: Ffin)          
        have False
          if "\<And>r. F r \<subseteq> g -` {r} \<and> F r \<subseteq> S"
            and "i \<in> gS" and "j \<in> gS" and "i \<noteq> j" and "x \<in> F i" and "x \<in> F j"
          for i j x
          by (metis subsetD that(1) that(4) that(5) that(6) vimage_singleton_eq)          
        hence w3: "\<forall>i\<in>gS. \<forall>j\<in>gS. i \<noteq> j \<longrightarrow> F i \<inter> F j = {}"
          using Fpartr[unfolded part_def] by auto          
        have w4: "sum normf (\<Union> (F ` gS)) + \<epsilon> = sum normf (\<Union> (F ` gS)) + \<epsilon>"
          by simp
        have "sum B' gS \<le> (\<Sum>r\<in>gS. sum normf (F r) + \<epsilon>N)"
          using F by (simp add: sum_mono)
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (\<Sum>r\<in>gS. \<epsilon>N)"
          by (simp add: sum.distrib)
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + (card gS * \<epsilon>N)"
          by auto
        also have "\<dots> = (\<Sum>r\<in>gS. sum normf (F r)) + \<epsilon>"
          unfolding \<epsilon>N_def N_def[symmetric] using \<open>N>0\<close> 
          by (simp add: ennreal_times_divide mult.commute mult_divide_eq_ennreal)
        also have "\<dots> = sum normf (\<Union> (F ` gS)) + \<epsilon>" 
          using w1 w2 w3 w4
          by (subst sum.UNION_disjoint[symmetric])
        also have "\<dots> \<le> B + \<epsilon>"
          using \<open>finite gS\<close> normf_B add_right_mono Ffin Fpartr unfolding part_def
          by (simp add: \<open>gS \<noteq> {}\<close> cSUP_least)          
        finally show ?thesis
          by auto
      qed
      hence sumB': "sum B' gS \<le> B"
        using ennreal_le_epsilon ennreal_less_zero_iff by blast
      have "\<forall>r. \<exists>y. r \<in> gS \<longrightarrow> B' r = ennreal y"
        using B'fin less_top_ennreal by auto
      hence "\<exists>B''. \<forall>r. r \<in> gS \<longrightarrow> B' r = ennreal (B'' r)"
        by (rule_tac choice) 
      then obtain B'' where B'': "B' r = ennreal (B'' r)" if "r \<in> gS" for r
        by atomize_elim 
      have cases[case_names zero finite infinite]: "P" if "r=0 \<Longrightarrow> P" and "finite (part r) \<Longrightarrow> P"
        and "infinite (part r) \<Longrightarrow> r\<noteq>0 \<Longrightarrow> P" for P r
        using that by metis
      have emeasure_B': "r * emeasure M (part r) \<le> B' r" if "r : gS" for r
      proof (cases rule:cases[of r])
        case zero
        thus ?thesis by simp
      next
        case finite
        have s1: "sum g F \<le> sum normf F"
          if "F \<in> {F. finite F \<and> F \<subseteq> part r}"
          for F
          using \<open>g \<le> normf\<close> 
          by (simp add: le_fun_def sum_mono)

        have "r * of_nat (card (part r)) = r * (\<Sum>x\<in>part r. 1)" by simp
        also have "\<dots> = (\<Sum>x\<in>part r. r)"
          using mult.commute by auto
        also have "\<dots> = (\<Sum>x\<in>part r. g x)"
          unfolding part_def by auto
        also have "\<dots> \<le> (SUP F\<in>{F. finite F \<and> F\<subseteq>part r}. sum g F)"
          using finite
          by (simp add: Sup_upper)
        also have "\<dots> \<le> B' r"        
          unfolding B'_def
          using s1 SUP_subset_mono by blast
        finally have "r * of_nat (card (part r)) \<le> B' r" by assumption
        thus ?thesis
          unfolding M_def
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
          using infinite(1) infinite_arbitrarily_large by blast
        from \<open>F \<subseteq> part r\<close> have "F \<subseteq> S" unfolding part_def by simp
        have "B < r * N"
          by (metis (mono_tags, hide_lams) N \<open>0 < r'\<close> assms(2) ennreal_less_iff ennreal_mult' 
              ennreal_of_nat_eq_real_of_nat less_eq_real_def 
              nice_ordered_field_class.pos_divide_less_eq ordered_field_class.sign_simps(47) r')
        also have "r * N = (\<Sum>x\<in>F. r)"
          using \<open>card F = N\<close> by (simp add: mult.commute)
        also have "(\<Sum>x\<in>F. r) = (\<Sum>x\<in>F. g x)"
          using \<open>F \<subseteq> part r\<close>  part_def sum.cong subsetD by fastforce
        also have "(\<Sum>x\<in>F. g x) \<le> (\<Sum>x\<in>F. ennreal (norm (f x)))"
          by (metis (mono_tags, lifting) \<open>g \<le> normf\<close> \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> le_fun_def 
              sum_mono)
        also have "(\<Sum>x\<in>F. ennreal (norm (f x))) \<le> B"
          using \<open>F \<subseteq> S\<close> \<open>finite F\<close> \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> normf_B by blast 
        finally have "B < B" by auto
        thus ?thesis by simp
      qed

      have "integral\<^sup>S M g = (\<Sum>r \<in> gS. r * emeasure M (part r))"
        unfolding simple_integral_def gS_def M_def part_def by simp
      also have "\<dots> \<le> (\<Sum>r \<in> gS. B' r)"
        by (simp add: emeasure_B' sum_mono)
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
    hence v1: "f abs_summable_on S"
      unfolding abs_summable_on_def M_def by simp  

    have "(\<lambda>x. norm (f x)) abs_summable_on S"
      using v1 Infinite_Set_Sum.abs_summable_on_norm_iff[where A = S and f = f]
      by auto
    moreover have "0 \<le> norm (f x)"
      if "x \<in> S" for x
      by simp    
    moreover have "(\<integral>\<^sup>+ x. ennreal (norm (f x)) \<partial>count_space S) \<le> ennreal B"
      using M_def \<open>normf \<equiv> \<lambda>x. ennreal (norm (f x))\<close> int_leq_B by auto    
    ultimately have "ennreal (\<Sum>\<^sub>ax\<in>S. norm (f x)) \<le> ennreal B"
      by (simp add: nn_integral_conv_infsetsum)    
    hence v2: "(\<Sum>\<^sub>ax\<in>S. norm (f x)) \<le> B"
      by (subst ennreal_le_iff[symmetric], simp add: assms)
    show ?thesis
      using v1 v2 by auto
  qed
  show "f abs_summable_on S"
    using t1 by blast
  show "(\<Sum>\<^sub>ax\<in>S. norm (f x)) \<le> B"
    using t1 by blast
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
    assms(3) by auto

lemma abs_summable_finiteI_converse:
  assumes f_sum_S: "f abs_summable_on S"
    and finite_F: "finite F" and FS: "F\<subseteq>S"
  defines "B \<equiv> (infsetsum (\<lambda>x. norm (f x)) S)"
  shows "sum (\<lambda>x. norm (f x)) F \<le> B"
proof-
  have a1: "(\<lambda>x. norm (f x)) abs_summable_on F"
    by (simp add: finite_F)    
  have a2: "(\<lambda>x. norm (f x)) abs_summable_on S"
    by (simp add: f_sum_S)    
  have a3: "x \<in> F \<Longrightarrow> norm (f x) \<le> norm (f x)"
    for x
    by simp
  have a4: "F \<subseteq> S"
    by (simp add: FS)    
  have a5: "x \<in> S - F \<Longrightarrow> 0 \<le> norm (f x)"
    for x
    by simp   
  have "sum (\<lambda>x. norm (f x)) F = infsetsum (\<lambda>x. norm (f x)) F"
    by (simp add: finite_F)    
  also have "infsetsum (\<lambda>x. norm (f x)) F \<le> B"
    unfolding B_def 
    using a1 a2 a3 a4 a5 
    by (simp add: infsetsum_mono_neutral_left)
  finally show ?thesis by assumption
qed

lemma abs_summable_countable:
  fixes \<mu> :: "'a \<Rightarrow> 'b::{banach,second_countable_topology}"
  assumes "\<mu> abs_summable_on T"
  shows "countable {x\<in>T. 0 \<noteq> \<mu> x}"
proof-
  define B where "B = infsetsum (\<lambda>x. norm (\<mu> x)) T"
  have \<mu>sum: "sum (\<lambda>x. norm (\<mu> x)) F \<le> B" if "finite F" and "F \<subseteq> T" for F
    unfolding B_def 
    using assms that abs_summable_finiteI_converse by auto
  define S where "S i = {x\<in>T. 1/real (Suc i) < norm (\<mu> x)}" for i::nat
  have "\<exists>i. x \<in> S i" if "0 < norm (\<mu> x)" and "x \<in> T" for x
    using that unfolding S_def
    by (metis (full_types, lifting) mem_Collect_eq nat_approx_posE)     
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
    have "1 / real (Suc i) \<le> norm (\<mu> x)"
      if "x \<in> F"
      for x
      using that F_Si S_def by auto
    hence "sum (\<lambda>x. norm (\<mu> x)) F \<ge> sum (\<lambda>_. 1/real (Suc i)) F" (is "_ \<ge> \<dots>")
      using sum_mono
      by metis       
    moreover have "\<dots> = real (card F) / (Suc i)"
      by (subst sum_constant_scale, auto)
    moreover have "\<dots> > B"
      using cardF
      by (simp add: linordered_field_class.mult_imp_less_div_pos ordered_field_class.sign_simps)
    ultimately have "sum (\<lambda>x. norm (\<mu> x)) F > B"
      by linarith 
    with sumF show False by simp
  qed

  have "countable (S i)"
    if "i \<in> UNIV"
    for i
    using finiteS by (simp add: countable_finite)
  hence "countable (\<Union>i. S i)"
    using countable_UN by simp
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
  unfolding infsetsum_def 
  using integral_Re assms by (simp add: abs_summable_on_def)

lemma infsetsum_Im: 
  assumes "f abs_summable_on M"
  shows "infsetsum (\<lambda>x. Im (f x)) M = Im (infsetsum f M)"
  unfolding infsetsum_def using assms by (simp add: abs_summable_on_def)

lemma infsetsum_mono_complex:
  fixes f g :: "'a \<Rightarrow> complex"
  assumes f_sum: "f abs_summable_on A" and g_sum: "g abs_summable_on A"
  assumes x: "\<And>x. x \<in> A \<Longrightarrow> f x \<le> g x"
  shows   "infsetsum f A \<le> infsetsum g A"
proof -
  have a1: "infsetsum f A = Complex (Re (infsetsum f A)) (Im (infsetsum f A))" by auto
  also have a2: "Re (infsetsum f A) = infsetsum (\<lambda>x. Re (f x)) A"
    unfolding infsetsum_def 
    using assms by (simp add: abs_summable_on_def)
  also have a3: "Im (infsetsum f A) = infsetsum (\<lambda>x. Im (f x)) A"
    using f_sum by (rule infsetsum_Im[symmetric])
  finally have fsplit: "infsetsum f A = Complex (\<Sum>\<^sub>ax\<in>A. Re (f x)) (\<Sum>\<^sub>ax\<in>A. Im (f x))" by assumption
  have "infsetsum g A = Complex (Re (infsetsum g A)) (Im (infsetsum g A))" by auto
  also have b2: "Re (infsetsum g A) = infsetsum (\<lambda>x. Re (g x)) A"
    using g_sum by (rule infsetsum_Re[symmetric])
  also have b1: "Im (infsetsum g A) = infsetsum (\<lambda>x. Im (g x)) A "
    using g_sum by (rule infsetsum_Im[symmetric])
  finally have gsplit: "infsetsum g A = Complex (\<Sum>\<^sub>ax\<in>A. Re (g x)) (\<Sum>\<^sub>ax\<in>A. Im (g x))" 
    by assumption
  have Re_leq: "Re (f x) \<le> Re (g x)" if "x\<in>A" for x
    using that assms unfolding less_eq_complex_def by simp
  have Im_eq: "Im (f x) = Im (g x)" if "x\<in>A" for x
    using that assms 
    unfolding less_eq_complex_def by simp
  have Refsum: "(\<lambda>x. Re (f x)) abs_summable_on A"
    using assms(1) abs_Re_le_cmod by (simp add: abs_summable_on_comparison_test[where g=f])
  have Regsum: "(\<lambda>x. Re (g x)) abs_summable_on A"
    using assms(2) abs_Re_le_cmod 
    by (simp add: abs_summable_on_comparison_test[where g=g])
  show "infsetsum f A \<le> infsetsum g A"
    unfolding fsplit gsplit
    by (metis (mono_tags, lifting) Im_eq Re_leq Refsum Regsum b1 b2 a2 a3 
        fsplit gsplit infsetsum_cong infsetsum_mono less_eq_complexI)
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
    using assms fBA infsetsum_mono_complex
    by (metis DiffD2 abs_summable_on_0)
  also have "... = infsetsum f B - infsetsum f A"
    using assms by (simp add: infsetsum_Diff)
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
    using assms fBA 
    by (metis DiffD2 calculation infsetsum_nonneg) 
  also have "... = infsetsum f B - infsetsum f A"
    using assms by (simp add: infsetsum_Diff)
  finally show ?thesis by auto
qed

lemma abs_summable_product:
  fixes x :: "'a \<Rightarrow> 'b::{real_normed_div_algebra,banach,second_countable_topology}"
  assumes x2_sum: "(\<lambda>i. (x i) * (x i)) abs_summable_on A"
    and y2_sum: "(\<lambda>i. (y i) * (y i)) abs_summable_on A"
  shows "(\<lambda>i. x i * y i) abs_summable_on A"
proof (rule abs_summable_finiteI)
  have aux: "a\<le>a' \<Longrightarrow> b\<le>b' \<Longrightarrow> a+b \<le> a'+b'" for a b a' b' :: real by simp
  fix F assume r1: "finite F" and b4: "F \<subseteq> A"
  define B :: real where "B = (\<Sum>\<^sub>ai\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>A. norm (y i * y i))"

  have a1: "(\<Sum>\<^sub>ai\<in>F. norm (x i * x i)) \<le> (\<Sum>\<^sub>ai\<in>A. norm (x i * x i))"
  proof (rule infsetsum_mono_neutral_left)
    show "(\<lambda>i. norm (x i * x i)) abs_summable_on F"
      by (simp add: r1)      
    show "(\<lambda>i. norm (x i * x i)) abs_summable_on A"
      by (simp add: x2_sum)      
    show "norm (x i * x i) \<le> norm (x i * x i)"
      if "i \<in> F"
      for i :: 'a
      by simp
    show "F \<subseteq> A"
      by (simp add: b4)     
    show "0 \<le> norm (x i * x i)"
      if "i \<in> A - F"
      for i :: 'a
      by simp 
  qed
  have "norm (x i * y i) \<le> norm (x i * x i) + norm (y i * y i)" for i
    unfolding norm_mult
    by (smt mult_left_mono mult_nonneg_nonneg mult_right_mono norm_ge_zero)
  hence "(\<Sum>i\<in>F. norm (x i * y i)) \<le> (\<Sum>i\<in>F. norm (x i * x i) + norm (y i * y i))"
    by (simp add: sum_mono)
  also have "\<dots> = (\<Sum>i\<in>F. norm (x i * x i)) + (\<Sum>i\<in>F. norm (y i * y i))"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>\<^sub>ai\<in>F. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>F. norm (y i * y i))"
    by (simp add: \<open>finite F\<close>)
  also have "\<dots> \<le> (\<Sum>\<^sub>ai\<in>A. norm (x i * x i)) + (\<Sum>\<^sub>ai\<in>A. norm (y i * y i))" 
    using aux a1
    by (simp add: aux \<open>F \<subseteq> A\<close> \<open>finite F\<close> abs_summable_finiteI_converse x2_sum y2_sum)
  also have "\<dots> = B"
    unfolding B_def by simp
  finally show "(\<Sum>i\<in>F. norm (x i * y i)) \<le> B" by assumption
qed

lemma abs_summable_cnj_iff[simp]:
  "(\<lambda>i. cnj (f i)) abs_summable_on A \<longleftrightarrow> f abs_summable_on A"
proof
  show "f abs_summable_on A"
    if "(\<lambda>i. cnj (f i)) abs_summable_on A"
    using that abs_summable_on_norm_iff[symmetric]
      abs_summable_on_comparison_test by fastforce    
  show "(\<lambda>i. cnj (f i)) abs_summable_on A"
    if "f abs_summable_on A"
    using that abs_summable_on_norm_iff[symmetric]
      abs_summable_on_comparison_test by fastforce 
qed

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
    show ?thesis      
      by (metis assms(1) cSup_le_iff ennreal_leI real(1) real(2) asm Sup_least bdd_above_top 
          cSUP_le_iff ennreal_le_iff nonempty)
  next
    case top
    thus ?thesis by auto
  qed
qed

lemma infsetsum_nonneg_is_SUPREMUM_ennreal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ennreal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
proof-
  have sum_F_A: "sum f F \<le> infsetsum f A" 
    if "F \<in> {F. finite F \<and> F \<subseteq> A}" 
    for F
  proof-
    from that have "finite F" and "F \<subseteq> A" by auto
    from \<open>finite F\<close> have "sum f F = infsetsum f F" by auto
    also have "\<dots> \<le> infsetsum f A"
    proof (rule infsetsum_mono_neutral_left)
      show "f abs_summable_on F"
        by (simp add: \<open>finite F\<close>)        
      show "f abs_summable_on A"
        by (simp add: local.summable)        
      show "f x \<le> f x"
        if "x \<in> F"
        for x :: 'a
        by simp 
      show "F \<subseteq> A"
        by (simp add: \<open>F \<subseteq> A\<close>)        
      show "0 \<le> f x"
        if "x \<in> A - F"
        for x :: 'a
        using that fnn by auto 
    qed
    finally show ?thesis by assumption
  qed 
  hence geq: "ennreal (infsetsum f A) \<ge> (SUP F\<in>{G. finite G \<and> G \<subseteq> A}. (ennreal (sum f F)))"
    by (meson SUP_least ennreal_leI)

  define fe where "fe x = ennreal (f x)" for x

  have sum_f_int: "infsetsum f A = \<integral>\<^sup>+ x. fe x \<partial>(count_space A)"
    unfolding infsetsum_def fe_def
  proof (rule nn_integral_eq_integral [symmetric])
    show "integrable (count_space A) f"
      using abs_summable_on_def local.summable by blast      
    show "AE x in count_space A. 0 \<le> f x"
      using fnn by auto      
  qed
  also have "\<dots> = (SUP g \<in> {g. finite (g`A) \<and> g \<le> fe}. integral\<^sup>S (count_space A) g)"
    unfolding nn_integral_def simple_function_count_space by simp
  also have "\<dots> \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
  proof (rule Sup_least)
    fix x assume "x \<in> integral\<^sup>S (count_space A) ` {g. finite (g ` A) \<and> g \<le> fe}"
    then obtain g where xg: "x = integral\<^sup>S (count_space A) g" and fin_gA: "finite (g`A)" 
      and g_fe: "g \<le> fe" by auto
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
      proof (rule sum_mono2)
        show "finite (g ` A)"
          by (simp add: fin_gA)          
        show "{t} \<subseteq> g ` A"
          by (simp add: tgA)          
        show "0 \<le> b * emeasure (count_space A) (g -` {b} \<inter> A)"
          if "b \<in> g ` A - {t}"
          for b :: ennreal
          using that
          by simp
      qed
      also have "\<dots> = t * emeasure (count_space A) (g -` {t} \<inter> A)"
        by auto
      also have "\<dots> = t * \<infinity>"
      proof (subst emeasure_count_space_infinite)
        show "g -` {t} \<inter> A \<subseteq> A"
          by simp             
        have "{a \<in> A. g a = t} = {a \<in> g -` {t}. a \<in> A}"
          by auto
        thus "infinite (g -` {t} \<inter> A)"
          by (metis (full_types) Int_def inf) 
        show "t * \<infinity> = t * \<infinity>"
          by simp
      qed
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
    have F: "F = (\<Union>t\<in>g`A-{0}. {z\<in>A. g z = t})"
      unfolding F_def by auto
    hence "finite F"
      unfolding F using fin_gA fin by auto
    have "x = integral\<^sup>N (count_space A) g"
      unfolding xg
      by (simp add: fin_gA nn_integral_eq_simple_integral)
    also have "\<dots> = set_nn_integral (count_space UNIV) A g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = set_nn_integral (count_space UNIV) F g"
    proof -
      have "\<forall>a. g a * (if a \<in> {a \<in> A. g a \<noteq> 0} then 1 else 0) = g a * (if a \<in> A then 1 else 0)"
        by auto
      hence "(\<integral>\<^sup>+ a. g a * (if a \<in> A then 1 else 0) \<partial>count_space UNIV)
           = (\<integral>\<^sup>+ a. g a * (if a \<in> {a \<in> A. g a \<noteq> 0} then 1 else 0) \<partial>count_space UNIV)"
        by presburger
      thus ?thesis unfolding F_def indicator_def
        using mult.right_neutral mult_zero_right nn_integral_cong
        by blast
    qed
    also have "\<dots> = integral\<^sup>N (count_space F) g"
      by (simp add: nn_integral_restrict_space[symmetric] restrict_count_space)
    also have "\<dots> = sum g F" 
      using \<open>finite F\<close> by (rule nn_integral_count_space_finite)
    also have "sum g F \<le> sum fe F"
      using g_fe unfolding le_fun_def
      by (simp add: sum_mono) 
    also have "\<dots> \<le> (SUP F \<in> {G. finite G \<and> G \<subseteq> A}. (sum fe F))"
      using \<open>finite F\<close> \<open>F\<subseteq>A\<close>
      by (simp add: SUP_upper)
    also have "\<dots> = (SUP F \<in> {F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
    proof (rule SUP_cong [OF refl])
      have "finite x \<Longrightarrow> x \<subseteq> A \<Longrightarrow> (\<Sum>x\<in>x. ennreal (f x)) = ennreal (sum f x)"
        for x
        by (metis fnn subsetCE sum_ennreal)
      thus "sum fe x = ennreal (sum f x)"
        if "x \<in> {G. finite G \<and> G \<subseteq> A}"
        for x :: "'a set"
        using that unfolding fe_def by auto      
    qed 
    finally show "x \<le> \<dots>" by simp
  qed
  finally have leq: "ennreal (infsetsum f A) \<le> (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ennreal (sum f F)))"
    by assumption
  from leq geq show ?thesis by simp
qed

lemma infsetsum_nonneg_is_SUPREMUM_ereal:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "ereal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
proof -
  have "ereal (infsetsum f A) = enn2ereal (ennreal (infsetsum f A))"
    by (simp add: fnn infsetsum_nonneg)
  also have "\<dots> = enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F))"
  proof (subst infsetsum_nonneg_is_SUPREMUM_ennreal)
    show "f abs_summable_on A"
      by (simp add: local.summable)      
    show "0 \<le> f x"
      if "x \<in> A"
      for x :: 'a
      using that
      by (simp add: fnn) 
    show "enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F)) = enn2ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ennreal (sum f F))"
      by simp      
  qed    
  also have "\<dots> = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
  proof (simp add: image_def Sup_ennreal.rep_eq)
    have "0 \<le> Sup {y. \<exists>x. (\<exists>xa. finite xa \<and> xa \<subseteq> A \<and> x = ennreal (sum f xa)) \<and>
                     y = enn2ereal x}"
      by (metis (mono_tags, lifting) Sup_upper empty_subsetI ennreal_0 finite.emptyI
          mem_Collect_eq sum.empty zero_ennreal.rep_eq)
    moreover have "Sup {y. \<exists>x. (\<exists>y. finite y \<and> y \<subseteq> A \<and> x = ennreal (sum f y)) \<and>
                y = enn2ereal x} = Sup {y. \<exists>x. finite x \<and> x \<subseteq> A \<and> y = ereal (sum f x)}"
      using enn2ereal_ennreal fnn in_mono sum_nonneg Collect_cong
      by smt (* > 1s *)
    ultimately show "max 0 (Sup {y. \<exists>x. (\<exists>xa. finite xa \<and> xa \<subseteq> A \<and> x
                                       = ennreal (sum f xa)) \<and> y = enn2ereal x})
         = Sup {y. \<exists>x. finite x \<and> x \<subseteq> A \<and> y = ereal (sum f x)}"
      by linarith
  qed   
  finally show ?thesis
    by simp
qed

lemma infsetsum_nonneg_is_SUPREMUM:
  fixes f :: "'a \<Rightarrow> real"
  assumes summable: "f abs_summable_on A"
    and fnn: "\<And>x. x\<in>A \<Longrightarrow> f x \<ge> 0"
  shows "infsetsum f A = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
proof -
  have "ereal (infsetsum f A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (ereal (sum f F)))"
    using assms by (rule infsetsum_nonneg_is_SUPREMUM_ereal)
  also have "\<dots> = ereal (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. (sum f F))"
  proof (subst ereal_SUP)
    show "\<bar>SUP a\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f a)\<bar> \<noteq> \<infinity>"
      using calculation by fastforce      
    show "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f F)) = (SUP a\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum f a))"
      by simp      
  qed
  finally show ?thesis by simp
qed

lemma infsetsum_geq0_complex:
  fixes f :: "'a \<Rightarrow> complex"
  assumes "f abs_summable_on M"
    and fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
  shows "infsetsum f M \<ge> 0" (is "?lhs \<ge> _")
proof -
  have "?lhs \<ge> infsetsum (\<lambda>x. 0) M" (is "_ \<ge> \<dots>")
  proof (rule infsetsum_mono_complex)
    show "(\<lambda>x. 0::complex) abs_summable_on M"
      by simp      
    show "f abs_summable_on M"
      by (simp add: assms(1))      
    show "0 \<le> f x"
      if "x \<in> M"
      for x :: 'a
      using that
      by (simp add: fnn) 
  qed
  also have "\<dots> = 0"
    by auto
  finally show ?thesis by assumption
qed

lemma infsetsum_cmod:
  assumes "f abs_summable_on M"
    and fnn: "\<And>x. x \<in> M \<Longrightarrow> 0 \<le> f x"
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

lemma infsetsum_Sigma:
  fixes A :: "'a set" and B :: "'a \<Rightarrow> 'b set"
  assumes summable: "f abs_summable_on (Sigma A B)"
  shows "infsetsum f (Sigma A B) = infsetsum (\<lambda>x. infsetsum (\<lambda>y. f (x, y)) (B x)) A"
proof-
  from summable have countable_Sigma: "countable {x \<in> Sigma A B. 0 \<noteq> f x}"
    by (rule abs_summable_countable)
  define A' where "A' = fst ` {x \<in> Sigma A B. 0 \<noteq> f x}"
  have countA': "countable A'"
    using countable_Sigma unfolding A'_def by auto

  define B' where "B' a = snd ` ({x \<in> Sigma A B. 0 \<noteq> f x} \<inter> {(a,b) | b. True})" for a
  have countB': "countable (B' a)" for a
    using countable_Sigma unfolding B'_def by auto

  have Sigma_eq: "x \<in> Sigma A B \<longleftrightarrow> x \<in> Sigma A' B'" if "f x \<noteq> 0" for x
    unfolding A'_def B'_def Sigma_def 
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
  proof (rule infsetsum_cong_neutral)
    show "f x = 0"
      if "x \<in> Sigma A B - Sigma A' B'"
      for x :: "'a \<times> 'b"
      using that
      by (meson DiffD1 DiffD2 Sigma_eq) 
    show "f x = 0"
      if "x \<in> Sigma A' B' - Sigma A B"
      for x :: "'a \<times> 'b"
      using that Sigma'_smaller by auto 
    show "f x = f x"
      if "x \<in> Sigma A B \<inter> Sigma A' B'"
      for x :: "'a \<times> 'b"
      using that
      by simp 
  qed 
  also from countA' countB' summable' have "\<dots> = (\<Sum>\<^sub>aa\<in>A'. \<Sum>\<^sub>ab\<in>B' a. f (a, b))"
    by (rule infsetsum_Sigma)
  also have "\<dots> = (\<Sum>\<^sub>aa\<in>A. \<Sum>\<^sub>ab\<in>B' a. f (a, b))" (is "_ = (\<Sum>\<^sub>aa\<in>A. ?inner a)" is "_ = ?rhs")
  proof (rule infsetsum_cong_neutral)
    show "(\<Sum>\<^sub>ab\<in>B' x. f (x, b)) = 0"
      if "x \<in> A' - A"
      for x :: 'a
      using that A'_smaller by blast 
    show "(\<Sum>\<^sub>ab\<in>B' x. f (x, b)) = 0"
      if "x \<in> A - A'"
      for x :: 'a
    proof -
      have f1: "x \<in> A"
        by (metis DiffD1 that)
      obtain bb :: "('b \<Rightarrow> 'c) \<Rightarrow> 'b set \<Rightarrow> 'b" where
        "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> x0 v2 \<noteq> 0) = (bb x0 x1 \<in> x1 \<and> x0 (bb x0 x1) \<noteq> 0)"
        by moura
      hence f2: "\<forall>B f. bb f B \<in> B \<and> f (bb f B) \<noteq> 0 \<or> infsetsum f B = 0"
        by (meson infsetsum_all_0)
      have "(x, bb (\<lambda>b. f (x, b)) (B' x)) \<notin> Sigma A' B'"
        by (meson DiffD2 SigmaE2 that)
      thus ?thesis
        using f2 f1 by (meson B'_smaller SigmaI Sigma_eq in_mono)
    qed 
    show "(\<Sum>\<^sub>ab\<in>B' x. f (x, b)) = (\<Sum>\<^sub>ab\<in>B' x. f (x, b))"
      if "x \<in> A' \<inter> A"
      for x :: 'a
      using that
      by simp 
  qed
  also have "?inner a = (\<Sum>\<^sub>ab\<in>B a. f (a, b))" if "a\<in>A" for a
  proof (rule infsetsum_cong_neutral)
    show "f (a, x) = 0"
      if "x \<in> B' a - B a"
      for x :: 'b
      using that B'_smaller by blast 
    show "f (a, x) = 0"
      if "x \<in> B a - B' a"
      for x :: 'b
      using that Sigma_eq \<open>a \<in> A\<close> by fastforce 
    show "f (a, x) = f (a, x)"
      if "x \<in> B' a \<inter> B a"
      for x :: 'b
      using that
      by simp 
  qed
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
  shows "infsetsum (\<lambda>x. infsetsum (\<lambda>y. f x y) B) A = infsetsum (\<lambda>y. infsetsum (\<lambda>x. f x y) A) B"
proof-
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
  finally show ?thesis.
qed

lemma cauchy_filter_metricI:
  fixes F :: "'a::metric_space filter"
  assumes "\<And>e. e>0 \<Longrightarrow> \<exists>P. eventually P F \<and> (\<forall>x y. P x \<and> P y \<longrightarrow> dist x y < e)"
  shows "cauchy_filter F"
proof (unfold cauchy_filter_def le_filter_def, auto)
  fix P :: "'a \<times> 'a \<Rightarrow> bool"
  assume "eventually P uniformity"
  then obtain e where e: "e > 0" and P: "dist x y < e \<Longrightarrow> P (x, y)" for x y
    unfolding eventually_uniformity_metric by auto

  obtain P' where evP': "eventually P' F" and P'_dist: "P' x \<and> P' y \<Longrightarrow> dist x y < e" for x y
    apply atomize_elim using assms e by auto
  
  from evP' P'_dist P
  show "eventually P (F \<times>\<^sub>F F)"
    unfolding eventually_uniformity_metric eventually_prod_filter eventually_filtermap by metis
qed

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
proof-
  define F where "F = filtermap (sum f) (finite_subsets_at_top A)"
  have F_not_bot: "F \<noteq> bot"
    unfolding F_def filtermap_bot_iff by simp

  have "\<exists>P. eventually P (finite_subsets_at_top A) \<and> (\<forall>x y. P x \<and> P y
         \<longrightarrow> dist (sum f x) (sum f y) < e)"
    if "0 < e"
    for e :: real
  proof-
    have is_SUP: "ereal (\<Sum>\<^sub>ax\<in>A. norm (f x)) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x)))"
    proof (rule infsetsum_nonneg_is_SUPREMUM_ereal)
      show "(\<lambda>x. norm (f x)) abs_summable_on A"
        by (simp add: assms)

      show "0 \<le> norm (f x)"
        if "x \<in> A"
        for x :: 'a
        using that
        by simp 
    qed 
    have "\<exists>F0\<in>{F. finite F \<and> F \<subseteq> A}.
       (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x))) - ereal e
       < ereal (\<Sum>x\<in>F0. norm (f x))"
      unfolding is_SUP Bex_def[symmetric]
      by (smt less_SUP_iff[symmetric] \<open>0 < e\<close> ereal_diff_le_self ereal_less_eq(5) ereal_minus(1) 
          is_SUP less_eq_ereal_def)
    then obtain F0 where "F0\<in>{F. finite F \<and> F \<subseteq> A}" and "ereal (\<Sum>x\<in>F0. norm (f x)) > ereal (\<Sum>\<^sub>ax\<in>A. norm (f x)) - ereal e"
      by (simp add: atomize_elim is_SUP) 
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
      proof (rule infsetsum_Un_disjoint [symmetric])
        show "(\<lambda>x. norm (f x)) abs_summable_on F1 - F2"
          by (simp add: \<open>finite F1\<close>)          
        show "(\<lambda>x. norm (f x)) abs_summable_on F2 - F1"
          by (simp add: \<open>finite F2\<close>)          
        show "(F1 - F2) \<inter> (F2 - F1) = {}"
          by (simp add: Diff_Int_distrib2)          
      qed
      also have "\<dots> \<le> infsetsum (\<lambda>x. norm (f x)) (A-F0)"
      proof (rule infsetsum_mono_neutral_left)
        show "(\<lambda>x. norm (f x)) abs_summable_on F1 - F2 \<union> (F2 - F1)"
          by (simp add: \<open>finite F1\<close> \<open>finite F2\<close>)          
        show "(\<lambda>x. norm (f x)) abs_summable_on A - F0"
          using abs_summable_on_subset assms by fastforce          
        show "norm (f x) \<le> norm (f x)"
          if "x \<in> F1 - F2 \<union> (F2 - F1)"
          for x :: 'a
          using that
          by simp 
        show "F1 - F2 \<union> (F2 - F1) \<subseteq> A - F0"
          by (simp add: Diff_mono \<open>F0 \<subseteq> F1\<close> \<open>F0 \<subseteq> F2\<close> \<open>F1 \<subseteq> A\<close> \<open>F2 \<subseteq> A\<close>)          
        show "0 \<le> norm (f x)"
          if "x \<in> A - F0 - (F1 - F2 \<union> (F2 - F1))"
          for x :: 'a
          by simp 
      qed
      also have "\<dots> = infsetsum (\<lambda>x. norm (f x)) A - infsetsum (\<lambda>x. norm (f x)) F0"
        by (simp add: assms infsetsum_Diff)
      also have "\<dots> < e"
        using local.sum_diff by auto
      finally show "dist (sum f F1) (sum f F2) < e" by assumption
    qed
    moreover have "eventually P (finite_subsets_at_top A)"
      unfolding P_def eventually_finite_subsets_at_top
      using \<open>F0 \<subseteq> A\<close> \<open>finite F0\<close> by blast      
    ultimately show "\<exists>P. eventually P (finite_subsets_at_top A) \<and> (\<forall>F1 F2. P F1 \<and> P F2 \<longrightarrow> dist (sum f F1) (sum f F2) < e)"
      by auto
  qed
  hence cauchy: "cauchy_filter F"
    unfolding F_def
    by (rule cauchy_filter_metric_filtermapI)  
  from complete_UNIV have "F\<le>principal UNIV \<Longrightarrow> F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> (\<exists>x. F \<le> nhds x)"
    unfolding complete_uniform
    by auto
  have "(F \<le> principal UNIV \<Longrightarrow> F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> \<exists>x. F \<le> nhds x) \<Longrightarrow>
    \<exists>x. F \<le> nhds x"
    using cauchy F_not_bot by simp
  then obtain x where Fx: "F \<le> nhds x"
    using \<open>\<lbrakk>F \<le> principal UNIV; F \<noteq> bot; cauchy_filter F\<rbrakk> \<Longrightarrow> \<exists>x. F \<le> nhds x\<close> by blast
  hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    unfolding F_def
    by (simp add: filterlim_def)
  thus ?thesis
    unfolding infsetsum'_converges_def by auto
qed

lemma tendsto_add_const_iff:
  \<comment> \<open>This is a generalization of \<open>Limits.tendsto_add_const_iff\<close>, 
      the only difference is that the sort here is more general.\<close>
  "((\<lambda>x. c + f x :: 'a::topological_group_add) \<longlongrightarrow> c + d) F \<longleftrightarrow> (f \<longlongrightarrow> d) F"
  using tendsto_add[OF tendsto_const[of c], of f d]
    and tendsto_add[OF tendsto_const[of "-c"], of "\<lambda>x. c + f x" "c + d"] by auto

lemma infsetsum'_converges_cofin_subset:
  fixes f :: "'a \<Rightarrow> 'b::topological_ab_group_add"
  assumes "infsetsum'_converges f A" and [simp]: "finite F"
  shows "infsetsum'_converges f (A-F)"
proof-
  from assms(1) obtain x where lim_f: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top A)"
    unfolding infsetsum'_converges_def by auto
  define F' where "F' = F\<inter>A"
  with assms have "finite F'" and "A-F = A-F'"
    by auto
  have "filtermap ((\<union>)F') (finite_subsets_at_top (A-F))
      \<le> finite_subsets_at_top A"
  proof (rule filter_leI)
    fix P assume "eventually P (finite_subsets_at_top A)"
    then obtain X where [simp]: "finite X" and XA: "X \<subseteq> A" 
      and P: "\<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> P Y"
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
  have "((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A - F))"
    if "((sum f \<circ> (\<union>) F') \<longlongrightarrow> x) (finite_subsets_at_top (A - F))"
    using that unfolding o_def by auto
  hence "((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A-F))"
    using tendsto_compose_filtermap [symmetric]
    by (simp add: \<open>(sum f \<longlongrightarrow> x) (filtermap ((\<union>) F') (finite_subsets_at_top (A - F)))\<close> 
        tendsto_compose_filtermap)
  have "\<forall>Y. finite Y \<and> Y \<subseteq> A - F \<longrightarrow> sum f (F' \<union> Y) = sum f F' + sum f Y"
    by (metis Diff_disjoint Int_Diff \<open>A - F = A - F'\<close> \<open>finite F'\<close> inf.orderE sum.union_disjoint)
  hence "\<forall>\<^sub>F x in finite_subsets_at_top (A - F). sum f (F' \<union> x) = sum f F' + sum f x"
    unfolding eventually_finite_subsets_at_top
    using exI [where x = "{}"]
    by (simp add: \<open>\<And>P. P {} \<Longrightarrow> \<exists>x. P x\<close>) 
  hence "((\<lambda>G. sum f F' + sum f G) \<longlongrightarrow> x) (finite_subsets_at_top (A-F))"
    using tendsto_cong [THEN iffD1 , rotated]
      \<open>((\<lambda>G. sum f (F' \<union> G)) \<longlongrightarrow> x) (finite_subsets_at_top (A - F))\<close> by fastforce
  hence "((\<lambda>G. sum f F' + sum f G) \<longlongrightarrow> sum f F' + (x-sum f F')) (finite_subsets_at_top (A-F))"
    by simp
  hence "(sum f \<longlongrightarrow> x - sum f F') (finite_subsets_at_top (A-F))"
    using Preliminaries.tendsto_add_const_iff by blast    
  thus "infsetsum'_converges f (A - F)"
    unfolding infsetsum'_converges_def by auto
qed

lemma finite_subsets_at_top_inter: 
  assumes "A\<subseteq>B"
  shows "filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B) \<le> finite_subsets_at_top A"
proof (rule filter_leI)
  show "eventually P (filtermap (\<lambda>F. F \<inter> A) (finite_subsets_at_top B))"
    if "eventually P (finite_subsets_at_top A)"
    for P :: "'a set \<Rightarrow> bool"
    using that unfolding eventually_filtermap
    unfolding eventually_finite_subsets_at_top
    by (metis Int_subset_iff assms finite_Int inf_le2 subset_trans)
qed

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
    have "sum f X = sum f (X - D)"
      if "finite (X::'a set)"
        and "X \<subseteq> A"
      for X :: "'a set"
      using that f0 D_def by (simp add: subset_iff sum.mono_neutral_cong_right)
    hence "\<forall>\<^sub>F x in finite_subsets_at_top A. sum f x = sum f (x - D)"
      by (rule eventually_finite_subsets_at_top_weakI)
    hence "((\<lambda>F. sum f (F-D)) \<longlongrightarrow> x) (finite_subsets_at_top A)"
      using tendsto_cong [THEN iffD1, rotated] limA by fastforce
    hence "(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F-D) (finite_subsets_at_top A))"
      by (simp add: filterlim_filtermap)
    have "D \<subseteq> A"
      unfolding D_def by simp
    hence "finite_subsets_at_top (A - D) \<le> filtermap (\<lambda>F. F - D) (finite_subsets_at_top A)"
      by (rule finite_subsets_at_top_minus)
    hence "(sum f \<longlongrightarrow> x) (finite_subsets_at_top (A-D))"
      using tendsto_mono [rotated] 
        \<open>(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F - D) (finite_subsets_at_top A))\<close>
      by blast
    have "A - D \<subseteq> B"
      unfolding D_def by auto
    hence "filtermap (\<lambda>F. F \<inter> (A - D)) (finite_subsets_at_top B) \<le> finite_subsets_at_top (A - D)"
      by (rule finite_subsets_at_top_inter [where B = B and A = "A-D"])
    hence "(sum f \<longlongrightarrow> x) (filtermap (\<lambda>F. F \<inter> (A - D)) (finite_subsets_at_top B))"
      using tendsto_mono [rotated] \<open>(sum f \<longlongrightarrow> x) (finite_subsets_at_top (A - D))\<close> by blast
    hence "((\<lambda>F. sum f (F \<inter> (A - D))) \<longlongrightarrow> x) (finite_subsets_at_top B)"
      by (simp add: filterlim_filtermap)
    have "sum f (X \<inter> (A - D)) = sum f X"
      if "finite (X::'a set)"
        and "X \<subseteq> B"
      for X :: "'a set"
    proof (rule sum.mono_neutral_cong)
      show "finite X"
        by (simp add: that(1))
      show "finite (X \<inter> (A - D))"
        by (simp add: that(1))
      show "f i = 0"
        if "i \<in> X - X \<inter> (A - D)"
        for i :: 'a
        using that D_def DiffD2 \<open>X \<subseteq> B\<close> f0 by auto 
      show "f i = 0"
        if "i \<in> X \<inter> (A - D) - X"
        for i :: 'a
        using that
        by auto 
      show "f x = f x"
        if "x \<in> X \<inter> (A - D) \<inter> X"
        for x :: 'a
        by simp
    qed
    hence "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f (x \<inter> (A - D)) = sum f x"
      by (rule eventually_finite_subsets_at_top_weakI)      
    hence limB: "(sum f \<longlongrightarrow> x) (finite_subsets_at_top B)"
      using tendsto_cong [THEN iffD1 , rotated]
        \<open>((\<lambda>F. sum f (F \<inter> (A - D))) \<longlongrightarrow> x) (finite_subsets_at_top B)\<close> by blast
    thus "infsetsum'_converges f B"
      unfolding infsetsum'_converges_def by auto
    have "Lim (finite_subsets_at_top A) (sum f) = Lim (finite_subsets_at_top B) (sum f)"
      if "infsetsum'_converges f B"
      using that    using limA limB
      using finite_subsets_at_top_neq_bot tendsto_Lim by blast
    thus "infsetsum' f A = infsetsum' f B"
      unfolding infsetsum'_def 
      using convA
      by (simp add: \<open>infsetsum'_converges f B\<close>)
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
  proof (rewrite asm_rl [of "(\<lambda>F. sum f (F\<inter>A)) = sum f o (\<lambda>F. F\<inter>A)"])
    show "(\<lambda>F. sum f (F \<inter> A)) = sum f \<circ> (\<lambda>F. F \<inter> A)"
      unfolding o_def by auto
    show "((sum f \<circ> (\<lambda>F. F \<inter> A)) \<longlongrightarrow> limA) (finite_subsets_at_top B)"
      unfolding o_def 
      using tendsto_compose_filtermap finite_subsets_at_top_inter[OF AB] limA tendsto_mono
        \<open>(\<lambda>F. sum f (F \<inter> A)) = sum f \<circ> (\<lambda>F. F \<inter> A)\<close> by fastforce
  qed
  with limB have "((\<lambda>F. sum f F - sum f (F\<inter>A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)"
    using tendsto_diff by blast
  have "sum f X - sum f (X \<inter> A) = sum f (X - A)"
    if "finite (X::'a set)"
      and "X \<subseteq> B"
    for X :: "'a set"
    using that by (metis add_diff_cancel_left' sum.Int_Diff)
  hence "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f x - sum f (x \<inter> A) = sum f (x - A)"
    by (rule eventually_finite_subsets_at_top_weakI)  
  hence "((\<lambda>F. sum f (F-A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)"
    using tendsto_cong [THEN iffD1 , rotated]
      \<open>((\<lambda>F. sum f F - sum f (F \<inter> A)) \<longlongrightarrow> limB - limA) (finite_subsets_at_top B)\<close> by fastforce
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
    and "A \<subseteq> B"
    and "infsetsum'_converges f A"
    and "infsetsum'_converges f B"
  shows "infsetsum' f B \<ge> infsetsum' f A"
proof -
  define limA limB f' where "limA = infsetsum' f A" and "limB = infsetsum' f B"
    and "f' x = (if x \<in> A then f x else 0)" for x
  have "infsetsum' f A = infsetsum' f' B"
  proof (subst infsetsum'_subset_zero [where f = f' and B = A])
    show "f' x = 0"
      if "x \<in> B - A \<union> (A - B)"
      for x :: 'a
      using that assms(2) f'_def by auto 
    show "infsetsum' f A = infsetsum' f' A"
      by (metis f'_def infsetsum'_cong)      
  qed
  hence limA_def': "limA = infsetsum' f' B"
    unfolding limA_def
    by auto
  have convA': "infsetsum'_converges f' B"
  proof (rule infsetsum'_converges_subset_zero [THEN iffD1 , where A1 = A])
    show "f' x = 0"
      if "x \<in> A - B \<union> (B - A)"
      for x :: 'a
      using that assms(2) f'_def by auto 
    show "infsetsum'_converges f' A"
      by (simp add: assms(3) f'_def infsetsum'_converges_cong)      
  qed
  from assms have limA: "(sum f \<longlongrightarrow> limA) (finite_subsets_at_top A)" 
    and limB: "(sum f \<longlongrightarrow> limB) (finite_subsets_at_top B)"
    by (auto simp: limA_def limB_def infsetsum'_converges_def infsetsum'_def tendsto_Lim)
  have limA': "(sum f' \<longlongrightarrow> limA) (finite_subsets_at_top B)"
    using finite_subsets_at_top_neq_bot tendsto_Lim convA'
    unfolding limA_def' infsetsum'_def  infsetsum'_converges_def
    by fastforce 
  have "f' i \<le> f i"
    if "i \<in> X" and "X \<subseteq> B"
    for i :: 'a and X
    unfolding f'_def using fx0 that
    using \<open>X \<subseteq> B\<close> by auto
  hence "sum f' X \<le> sum f X"
    if "finite (X::'a set)"
      and "X \<subseteq> B"
    for X :: "'a set"
    using sum_mono
    by (simp add: sum_mono that(2)) 
  hence sumf'_leq_sumf: "\<forall>\<^sub>F x in finite_subsets_at_top B. sum f' x \<le> sum f x"
    by (rule eventually_finite_subsets_at_top_weakI)
  show "limA \<le> limB"
    using _ limB limA' sumf'_leq_sumf  tendsto_le finite_subsets_at_top_neq_bot by blast
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
  assumes "infsetsum'_converges f A" and "\<epsilon> > 0"
  shows "\<exists>F. finite F \<and> F \<subseteq> A \<and> dist (sum f F) (infsetsum' f A) \<le> \<epsilon>"
proof-
  have "infsetsum'_converges f A \<Longrightarrow>
    0 < \<epsilon> \<Longrightarrow> (sum f \<longlongrightarrow> Lim (finite_subsets_at_top A) (sum f)) (finite_subsets_at_top A)"
    unfolding infsetsum'_converges_def
    using Lim_trivial_limit tendsto_Lim by blast
  hence "(sum f \<longlongrightarrow> infsetsum' f A) (finite_subsets_at_top A)"
    unfolding infsetsum'_def
    using assms
    by simp
  hence "\<forall>\<^sub>F F in (finite_subsets_at_top A). dist (sum f F) (infsetsum' f A) < \<epsilon>"
    using assms(2) by (rule tendstoD)
  have "finite X \<Longrightarrow>
         X \<subseteq> A \<Longrightarrow>
         \<forall>Y. finite Y \<and> X \<subseteq> Y \<and> Y \<subseteq> A \<longrightarrow> dist (sum f Y) (infsetsum' f A) < \<epsilon> \<Longrightarrow>
         \<exists>F. finite F \<and> F \<subseteq> A \<and> dist (sum f F) (infsetsum' f A) \<le> \<epsilon>"
    for X
    by fastforce    
  thus ?thesis
    using eventually_finite_subsets_at_top
    by (metis (no_types, lifting)
        \<open>\<forall>\<^sub>F F in finite_subsets_at_top A. dist (sum f F) (infsetsum' f A) < \<epsilon>\<close>)
qed

lemma norm_infsetsum'_bound:
  fixes f :: "'b \<Rightarrow> 'a::real_normed_vector"
    and A :: "'b set"
  assumes a1: "infsetsum'_converges (\<lambda>x. norm (f x)) A"
  shows "norm (infsetsum' f A) \<le> (infsetsum' (\<lambda>x. norm (f x)) A)"
proof(cases "infsetsum'_converges f A")
  case True
  have "norm (infsetsum' f A) \<le> (infsetsum' (\<lambda>x. norm (f x)) A) + \<epsilon>" if "\<epsilon>>0" for \<epsilon>
  proof-
    have "\<exists>F. norm (infsetsum' f A - sum f F) \<le> \<epsilon> \<and> finite F \<and> F \<subseteq> A"
      using infsetsum'_approx_sum[where A=A and f=f and \<epsilon>="\<epsilon>"] a1 True \<open>0 < \<epsilon>\<close>
      by (metis dist_commute dist_norm)
    then obtain F where "norm (infsetsum' f A - sum f F) \<le> \<epsilon>"
      and "finite F" and "F \<subseteq> A"
      by (simp add: atomize_elim)
    hence "norm (infsetsum' f A) \<le> norm (sum f F) + \<epsilon>"
      by (smt norm_triangle_sub)
    also have "\<dots> \<le> sum (\<lambda>x. norm (f x)) F + \<epsilon>"
      using norm_sum by auto
    also have "\<dots> \<le> (infsetsum' (\<lambda>x. norm (f x)) A) + \<epsilon>"
    proof-
      have "infsetsum' (\<lambda>x. norm (f x)) F \<le> infsetsum' (\<lambda>x. norm (f x)) A"
      proof (rule infsetsum'_mono_set)
        show "0 \<le> norm (f x)"
          if "x \<in> A - F"
          for x :: 'b
          using that
          by simp 
        show "F \<subseteq> A"
          by (simp add: \<open>F \<subseteq> A\<close>)          
        show "infsetsum'_converges (\<lambda>x. norm (f x)) F"
          using \<open>finite F\<close> by auto         
        show "infsetsum'_converges (\<lambda>x. norm (f x)) A"
          by (simp add: assms)          
      qed
      thus ?thesis
        by (simp_all flip: infsetsum'_finite add: \<open>finite F\<close>)
    qed
    finally show ?thesis 
      by assumption
  qed
  thus ?thesis
    using linordered_field_class.field_le_epsilon by blast
next
  case False
  obtain t where t_def: "(sum (\<lambda>x. norm (f x)) \<longlongrightarrow> t) (finite_subsets_at_top A)"
    using a1 unfolding infsetsum'_converges_def by blast
  have sumpos: "sum (\<lambda>x. norm (f x)) X \<ge> 0"
    for X
    by (simp add: sum_nonneg)
  have tgeq0:"t \<ge> 0"
  proof(rule ccontr)
    define S::"real set" where "S = {s. s < 0}"
    assume "\<not> 0 \<le> t"
    hence "t < 0" by simp
    hence "t \<in> S"
      unfolding S_def by blast
    moreover have "open S"
    proof-
      have "closed {s::real. s \<ge> 0}"
        using Elementary_Topology.closed_sequential_limits[where S = "{s::real. s \<ge> 0}"]
        by (metis Lim_bounded2 mem_Collect_eq)
      moreover have "{s::real. s \<ge> 0} = UNIV - S"
        unfolding S_def by auto
      ultimately have "closed (UNIV - S)"
        by simp
      thus ?thesis
        by (simp add: Compl_eq_Diff_UNIV open_closed) 
    qed
    ultimately have "\<forall>\<^sub>F X in finite_subsets_at_top A. (\<Sum>x\<in>X. norm (f x)) \<in> S"
      using t_def unfolding tendsto_def by blast
    hence "\<exists>X. (\<Sum>x\<in>X. norm (f x)) \<in> S"
      by (metis (no_types, lifting) False eventually_mono filterlim_iff infsetsum'_converges_def)
    then obtain X where "(\<Sum>x\<in>X. norm (f x)) \<in> S"
      by blast
    hence "(\<Sum>x\<in>X. norm (f x)) < 0"
      unfolding S_def by auto      
    thus False using sumpos by smt
  qed
  have "\<exists>!h. (sum (\<lambda>x. norm (f x)) \<longlongrightarrow> h) (finite_subsets_at_top A)"
    using t_def finite_subsets_at_top_neq_bot tendsto_unique by blast
  hence "t = (Topological_Spaces.Lim (finite_subsets_at_top A) (sum (\<lambda>x. norm (f x))))"
    using t_def unfolding Topological_Spaces.Lim_def
    by (metis the_equality)     
  hence "Lim (finite_subsets_at_top A) (sum (\<lambda>x. norm (f x))) \<ge> 0"
    using tgeq0 by blast
  thus ?thesis unfolding infsetsum'_def 
    using False by auto
qed


lemma
  assumes "f abs_summable_on A"
  shows "infsetsum f A = infsetsum' f A"
proof-
  have conv_sum_norm[simp]: "infsetsum'_converges (\<lambda>x. norm (f x)) A"
  proof (rule abs_summable_infsetsum'_converges)
    show "(\<lambda>x. norm (f x)) abs_summable_on A"
      using assms by simp
  qed    
  have "norm (infsetsum f A - infsetsum' f A) \<le> \<epsilon>" if "\<epsilon>>0" for \<epsilon>
  proof -
    define \<delta> where "\<delta> = \<epsilon>/2"
    with that have [simp]: "\<delta> > 0" by simp
    obtain F1 where F1A: "F1 \<subseteq> A" and finF1: "finite F1" and leq_eps: "infsetsum (\<lambda>x. norm (f x)) (A-F1) \<le> \<delta>"
    proof -
      have sum_SUP: "ereal (infsetsum (\<lambda>x. norm (f x)) A) = (SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (sum (\<lambda>x. norm (f x)) F))"
        (is "_ = ?SUP")
      proof (rule infsetsum_nonneg_is_SUPREMUM_ereal)
        show "(\<lambda>x. norm (f x)) abs_summable_on A"
          by (simp add: assms)          
        show "0 \<le> norm (f x)"
          if "x \<in> A"
          for x :: 'a
          using that
          by simp 
      qed

      have "(SUP F\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>F. norm (f x))) - ereal \<delta>
    < (SUP i\<in>{F. finite F \<and> F \<subseteq> A}. ereal (\<Sum>x\<in>i. norm (f x)))"
        using \<open>\<delta>>0\<close>
        by (metis diff_strict_left_mono diff_zero ereal_less_eq(3) ereal_minus(1) not_le sum_SUP)
      then obtain F where "F\<in>{F. finite F \<and> F \<subseteq> A}" and "ereal (sum (\<lambda>x. norm (f x)) F) > ?SUP - ereal (\<delta>)"
        by (meson less_SUP_iff)
        
      hence "sum (\<lambda>x. norm (f x)) F > infsetsum (\<lambda>x. norm (f x)) A -  (\<delta>)"
        unfolding sum_SUP[symmetric] by auto
      hence "\<delta> > infsetsum (\<lambda>x. norm (f x)) (A-F)"
      proof (subst infsetsum_Diff)
        show "(\<lambda>x. norm (f x)) abs_summable_on A"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that
          by (simp add: assms) 
        show "F \<subseteq> A"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> by blast 
        show "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - (\<Sum>\<^sub>ax\<in>F. norm (f x)) < \<delta>"
          if "(\<Sum>\<^sub>ax\<in>A. norm (f x)) - \<delta> < (\<Sum>x\<in>F. norm (f x))"
          using that \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> by auto 
      qed
      thus ?thesis using that 
        apply atomize_elim
        using \<open>F \<in> {F. finite F \<and> F \<subseteq> A}\<close> less_imp_le by blast
    qed
    have "\<exists>F2\<subseteq>A.
       finite F2 \<and>
       dist (\<Sum>x\<in>F2. norm (f x)) (infsetsum' (\<lambda>x. norm (f x)) A) \<le> \<delta>"
      using infsetsum'_approx_sum[where f="(\<lambda>x. norm (f x))" and A=A and \<epsilon>=\<delta>]
        abs_summable_infsetsum'_converges assms by auto
    then obtain F2 where F2A: "F2 \<subseteq> A" and finF2: "finite F2"
      and dist: "dist (sum (\<lambda>x. norm (f x)) F2) (infsetsum' (\<lambda>x. norm (f x)) A) \<le> \<delta>"
      by blast     
    have  leq_eps': "infsetsum' (\<lambda>x. norm (f x)) (A-F2) \<le> \<delta>"
    proof (subst infsetsum'_Diff)
      show "infsetsum'_converges (\<lambda>x. norm (f x)) A"
        by simp        
      show "infsetsum'_converges (\<lambda>x. norm (f x)) F2"
        by (simp add: finF2)        
      show "F2 \<subseteq> A"
        by (simp add: F2A)        
      show "infsetsum' (\<lambda>x. norm (f x)) A - infsetsum' (\<lambda>x. norm (f x)) F2 \<le> \<delta>"
        using dist finF2
        by (auto simp: dist_norm)
    qed 
    define F where "F = F1 \<union> F2"
    have FA: "F \<subseteq> A" and finF: "finite F" 
      unfolding F_def using F1A F2A finF1 finF2 by auto

    have "(\<Sum>\<^sub>ax\<in>A - (F1 \<union> F2). norm (f x)) \<le> (\<Sum>\<^sub>ax\<in>A - F1. norm (f x))"
    proof (rule infsetsum_mono_neutral_left)
      show "(\<lambda>x. norm (f x)) abs_summable_on A - (F1 \<union> F2)"
        using abs_summable_on_subset assms by fastforce        
      show "(\<lambda>x. norm (f x)) abs_summable_on A - F1"
        using abs_summable_on_subset assms by fastforce        
      show "norm (f x) \<le> norm (f x)"
        if "x \<in> A - (F1 \<union> F2)"
        for x :: 'a
        using that
        by auto 
      show "A - (F1 \<union> F2) \<subseteq> A - F1"
        by (simp add: Diff_mono)        
      show "0 \<le> norm (f x)"
        if "x \<in> A - F1 - (A - (F1 \<union> F2))"
        for x :: 'a
        using that
        by auto 
    qed
    hence leq_eps: "infsetsum (\<lambda>x. norm (f x)) (A-F) \<le> \<delta>"
      unfolding F_def
      using leq_eps by linarith
    have "infsetsum' (\<lambda>x. norm (f x)) (A - (F1 \<union> F2))
    \<le> infsetsum' (\<lambda>x. norm (f x)) (A - F2)"
    proof (rule infsetsum'_mono_set)
      show "0 \<le> norm (f x)"
        if "x \<in> A - F2 - (A - (F1 \<union> F2))"
        for x :: 'a
        using that
        by simp 
      show "A - (F1 \<union> F2) \<subseteq> A - F2"
        by (simp add: Diff_mono)        
      show "infsetsum'_converges (\<lambda>x. norm (f x)) (A - (F1 \<union> F2))"
        using F_def conv_sum_norm finF infsetsum'_converges_cofin_subset by blast        
      show "infsetsum'_converges (\<lambda>x. norm (f x)) (A - F2)"
        by (simp add: finF2 infsetsum'_converges_cofin_subset)        
    qed
    hence leq_eps': "infsetsum' (\<lambda>x. norm (f x)) (A-F) \<le> \<delta>"
      unfolding F_def 
      by (rule order.trans[OF _ leq_eps'])
    have "norm (infsetsum f A - infsetsum f F) = norm (infsetsum f (A-F))"
    proof (subst infsetsum_Diff [symmetric])
      show "f abs_summable_on A"
        by (simp add: assms)          
      show "F \<subseteq> A"
        by (simp add: FA)          
      show "norm (infsetsum f (A - F)) = norm (infsetsum f (A - F))"
        by simp          
    qed
    also have "\<dots> \<le> infsetsum (\<lambda>x. norm (f x)) (A-F)"
      using norm_infsetsum_bound by blast
    also have "\<dots> \<le> \<delta>"
      using leq_eps by simp
    finally have diff1: "norm (infsetsum f A - infsetsum f F) \<le> \<delta>"
      by assumption
    have "norm (infsetsum' f A - infsetsum' f F) = norm (infsetsum' f (A-F))"
    proof (subst infsetsum'_Diff [symmetric])
      show "infsetsum'_converges f A"
        by (simp add: abs_summable_infsetsum'_converges assms)        
      show "infsetsum'_converges f F"
        by (simp add: finF)        
      show "F \<subseteq> A"
        by (simp add: FA)        
      show "norm (infsetsum' f (A - F)) = norm (infsetsum' f (A - F))"
        by simp        
    qed
    also have "\<dots> \<le> infsetsum' (\<lambda>x. norm (f x)) (A-F)"
      by (simp add: finF infsetsum'_converges_cofin_subset norm_infsetsum'_bound)
    also have "\<dots> \<le> \<delta>"
      using leq_eps' by simp
    finally have diff2: "norm (infsetsum' f A - infsetsum' f F) \<le> \<delta>"
      by assumption

    have x1: "infsetsum f F = infsetsum' f F"
      using finF by simp
    have "norm (infsetsum f A - infsetsum' f A) \<le> norm (infsetsum f A - infsetsum f F) + norm (infsetsum' f A - infsetsum' f F)"
      apply (rule_tac norm_diff_triangle_le)
       apply auto
      by (simp_all add: x1 norm_minus_commute)
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
  and "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on I"
  and "T \<subseteq> (\<Union>i\<in>I. S i)"
  shows "f abs_summable_on T"
proof (rule abs_summable_finiteI)
  fix F assume finite_F: "finite F" and FT: "F \<subseteq> T"
  define index where "index s = (SOME i. i\<in>I \<and> s\<in>S i)" for s
  hence index_I: "index s \<in> I" and S_index: "s \<in> S (index s)" if "s \<in> (\<Union>i\<in>I. S i)" for s
  proof auto
    show "(SOME i. i \<in> I \<and> s \<in> S i) \<in> I"
      if "\<And>s. index s = (SOME i. i \<in> I \<and> s \<in> S i)"
      using that
      by (metis (no_types, lifting) UN_iff \<open>s \<in> \<Union> (S ` I)\<close> someI_ex) 
    show "s \<in> S (SOME i. i \<in> I \<and> s \<in> S i)"
      if "\<And>s. index s = (SOME i. i \<in> I \<and> s \<in> S i)"
      using that
      by (metis (no_types, lifting) UN_iff \<open>s \<in> \<Union> (S ` I)\<close> someI_ex) 
  qed
  define S' where "S' i = {s\<in>S i. i = index s}" for i
  have S'_S: "S' i \<subseteq> S i" for i
    unfolding S'_def by simp
  hence f_sum_S': "f abs_summable_on S' i" for i
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
    by (metis S'_S abs_summable_finiteI_converse assms(1) finite_Int le_inf_iff order_refl 
        subset_antisym)
  have B_pos[simp]: "B i \<ge> 0" for i
    unfolding B_def by (rule infsetsum_nonneg, simp)
  have B_sum_I[simp]: "B abs_summable_on I"
    by (simp add: B_def assms(2))
  define J where "J = {i\<in>I. F\<inter>S' i \<noteq> {}}"
  have finite_J[simp]: "finite J"
  proof -
    define a where "a i = (SOME x. x\<in>F\<inter>S' i)" for i
    hence a: "a i \<in> F\<inter>S' i" if "i \<in> J" for i
      unfolding J_def
      by (metis (mono_tags) Collect_conj_eq Int_Collect J_def some_in_eq that)
    have xy: "x = y"
      if "x \<in> J" and "y \<in> J" and "a x = a y" and "\<And>i. i \<in> J \<Longrightarrow> a i \<in> F \<and> a i \<in> S' i"
           and "\<And>i j. i \<noteq> j \<Longrightarrow> S' i \<inter> S' j = {}"
         for x y     
      using that a S'_disj
      by (metis S'_disj disjoint_iff_not_equal)
    hence "inj_on a J"
      unfolding inj_on_def
      using S'_disj a by auto 
    moreover have "a ` J \<subseteq> F"
      using a by auto
    ultimately show "finite J"
      using finite_F Finite_Set.inj_on_finite by blast
  qed
  have JI[simp]: "J \<subseteq> I"
    unfolding J_def by simp
  have "F = (\<Union>i\<in>J. F\<inter>S' i)"
    unfolding J_def apply auto
    by (metis FT T_S' UN_E disjoint_iff_not_equal subsetD)
  hence "(\<Sum>x\<in>F. norm (f x)) = (\<Sum>x\<in>(\<Union>i\<in>J. F\<inter>S' i). norm (f x))"
    by simp
  also have "\<dots> = (\<Sum>i\<in>J. \<Sum>x\<in>F \<inter> S' i. norm (f x))"
  proof (rule sum.UNION_disjoint)
    show "finite J"
      by simp      
    show "\<forall>i\<in>J. finite (F \<inter> S' i)"
      by (simp add: finite_F)      
    show "\<forall>i\<in>J. \<forall>j\<in>J. i \<noteq> j \<longrightarrow> F \<inter> S' i \<inter> (F \<inter> S' j) = {}"
      using S'_disj by auto      
  qed
  also have "\<dots> \<le> (\<Sum>i\<in>J. B i)"
    using sum_FS'_B
    by (simp add: ordered_comm_monoid_add_class.sum_mono)
  also have "\<dots> = (\<Sum>\<^sub>ai\<in>J. B i)"
    by simp
  also have "\<dots> \<le> (\<Sum>\<^sub>ai\<in>I. B i)"
  proof (rule infsetsum_mono_neutral_left)
    show "B abs_summable_on J"
      by simp      
    show "B abs_summable_on I"
      by simp
    show "B x \<le> B x"
      if "x \<in> J"
      for x :: 'a
      using that
      by simp 
    show "J \<subseteq> I"
      by simp      
    show "0 \<le> B x"
      if "x \<in> I - J"
      for x :: 'a
      using that
      by simp 
  qed    
  finally show "(\<Sum>x\<in>F. norm(f x)) \<le> (\<Sum>\<^sub>ai\<in>I. B i)"
    by simp
qed

lemma abs_summable_product':
  fixes X :: "'a set" and Y :: "'b set"
  assumes "\<And>x. (\<lambda>y. f (x,y)) abs_summable_on Y"
    and "(\<lambda>x. \<Sum>\<^sub>ay\<in>Y. norm (f (x,y))) abs_summable_on X"
  shows "f abs_summable_on X\<times>Y"
proof-
  define S where "S x = {x} \<times> Y" for x :: 'a
  have bij[simp]: "bij_betw (Pair x) Y (S x)" for x
  proof (rule bij_betwI [where g = snd])
    show "Pair x \<in> Y \<rightarrow> S x"
      by (simp add: S_def)      
    show "snd \<in> S x \<rightarrow> Y"
      using Pi_I' S_def by auto      
    show "snd (y, x::'b) = x"
      if "x \<in> Y"
      for x :: 'b and y::'a
      using that
      by simp 
    show "(x, snd y::'b) = y"
      if "y \<in> S x"
      for y :: "'a \<times> 'b"
      using that
      unfolding S_def
      by auto
  qed
  have "f abs_summable_on S x" for x
  proof (subst abs_summable_on_reindex_bij_betw [symmetric , where A = Y and g = "\<lambda>y. (x,y)"])
    show "bij_betw (Pair x) Y (S x)"
      by simp      
    show "(\<lambda>xa. f (x, xa)) abs_summable_on Y"
      using assms(1) by auto      
  qed
  moreover have "bij_betw (Pair x) Y (S x)"
    for x
    unfolding S_def using bij_betw_def
    using S_def bij by auto
  hence "(\<Sum>\<^sub>ay\<in>Y. norm (f (x, y))) = (\<Sum>\<^sub>ay\<in>S x. norm (f y))" for x
    by (rule infsetsum_reindex_bij_betw) 
  hence "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on X"
    using assms(2) by simp
  hence "(\<lambda>i. \<Sum>\<^sub>ax\<in>S i. norm (f x)) abs_summable_on X"
    by auto
  moreover have "X \<times> Y \<subseteq> (\<Union>i\<in>X. S i)"
    unfolding S_def by auto
  ultimately show ?thesis
    by (rule abs_summable_partition[where S=S and I=X])
qed

lemma infsetsum_prod_PiE:
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'c :: {real_normed_field,banach,second_countable_topology}"
  assumes finite: "finite A"
    and summable: "\<And>x. x \<in> A \<Longrightarrow> f x abs_summable_on B x"
  shows "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B) = (\<Prod>x\<in>A. infsetsum (f x) (B x))"
proof-
  define B' where "B' x = {y\<in>B x. 0 \<noteq> f x y}" for x
  have [simp]: "B' x \<subseteq> B x" for x
    unfolding B'_def by simp
  have PiE_subset: "Pi\<^sub>E A B' \<subseteq> Pi\<^sub>E A B"
    by (simp add: PiE_mono)
  have "f x abs_summable_on B x"
    if "x\<in>A"
    for x
    using that
    by (simp add: local.summable) 
  hence countable: "countable (B' x)" if "x\<in>A" for x
    unfolding B'_def using abs_summable_countable
    using that by blast
  have summable: "f x abs_summable_on B' x" if "x\<in>A" for x
    using that summable[where x = x] \<open>\<And>x. B' x \<subseteq> B x\<close> abs_summable_on_subset by blast
  have 0: "(\<Prod>x\<in>A. f x (g x)) = 0" if "g \<in> Pi\<^sub>E A B - Pi\<^sub>E A B'" for g
  proof-
    from that have "g \<in> extensional A"
      by (simp add: PiE_def)
    from that have "g \<notin> Pi\<^sub>E A B'"
      by simp
    with \<open>g \<in> extensional A\<close> have "g \<notin> Pi A B'"
      unfolding PiE_def by simp
    then obtain x where "x\<in>A" and "g x \<notin> B' x"
      unfolding Pi_def by auto
    hence "f x (g x) = 0"
      unfolding B'_def using that by auto
    with finite show ?thesis
    proof (rule_tac prod_zero)
      show "finite A"
        if "finite A"
          and "f x (g x) = 0"
        using that
        by simp 
      show "\<exists>a\<in>A. f a (g a) = 0"
        if "finite A"
          and "f x (g x) = 0"
        using that \<open>x \<in> A\<close> by blast 
    qed      
  qed

  have d: "infsetsum (f x) (B' x) = infsetsum (f x) (B x)"
    if "x \<in> A"
    for x
  proof (rule infsetsum_cong_neutral)
    show "f y x = 0"
      if "x \<in> B' y - B y"
      for x :: 'b and y :: 'a
      using that
      by (meson DiffD1 DiffD2 \<open>\<And>x. B' x \<subseteq> B x\<close> in_mono) 
    show "f y x = 0"
      if "x \<in> B y - B' y"
      for x :: 'b and y
      using that B'_def by auto 
    show "f y x = f y x"
      if "x \<in> B' y \<inter> B y"
      for x :: 'b and y
      using that
      by simp 
  qed    
  have "infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B)
      = infsetsum (\<lambda>g. \<Prod>x\<in>A. f x (g x)) (PiE A B')"
  proof (rule infsetsum_cong_neutral)
    show "(\<Prod>a\<in>A. f a (x a)) = 0"
      if "x \<in> Pi\<^sub>E A B - Pi\<^sub>E A B'"
      for x :: "'a \<Rightarrow> 'b"
      using that
      by (simp add: "0") 
    show "(\<Prod>a\<in>A. f a (x a)) = 0"
      if "x \<in> Pi\<^sub>E A B' - Pi\<^sub>E A B"
      for x :: "'a \<Rightarrow> 'b"
      using that PiE_subset by auto 
    show "(\<Prod>a\<in>A. f a (x a)) = (\<Prod>a\<in>A. f a (x a))"
      if "x \<in> Pi\<^sub>E A B \<inter> Pi\<^sub>E A B'"
      for x :: "'a \<Rightarrow> 'b"
      using that
      by simp 
  qed
  also have "\<dots> = (\<Prod>x\<in>A. infsetsum (f x) (B' x))"
    using finite countable summable by (rule infsetsum_prod_PiE)
  also have "\<dots> = (\<Prod>x\<in>A. infsetsum (f x) (B x))"
    using d
    by auto
  finally show ?thesis.
qed


lemma infsetsum_0D:
  fixes f :: "'a \<Rightarrow> real"
  assumes "infsetsum f A = 0"
  and abs_sum: "f abs_summable_on A"
  and nneg: "\<And>x. x \<in> A \<Longrightarrow> f x \<ge> 0"
  and "x \<in> A"
  shows "f x = 0"
proof -
  from abs_sum have [simp]: "f abs_summable_on (A-{x})"
    by (meson Diff_subset abs_summable_on_subset)
  from abs_sum \<open>x\<in>A\<close> have [simp]: "f abs_summable_on {x}"
    by auto
  have a: "\<And>a. a \<in> A - {x} \<Longrightarrow> a \<in> A"
    by simp   
  from assms have "0 = infsetsum f A"
    by simp
  also have "\<dots> = infsetsum f (A-{x}) + infsetsum f {x}"
  proof (subst infsetsum_Un_disjoint [symmetric])
    show "f abs_summable_on A - {x}"
      by simp      
    show "f abs_summable_on {x}"
      by simp      
    show "(A - {x}) \<inter> {x} = {}"
      by simp      
    show "infsetsum f A = infsetsum f (A - {x} \<union> {x})"
      using assms(4) insert_Diff by fastforce      
  qed
  also have "\<dots> \<ge> 0 + infsetsum f {x}" (is "_ \<ge> \<dots>")
    using a
    by (smt infsetsum_nonneg nneg)    
  also have "\<dots> = f x"
    by simp
  finally have "f x \<le> 0".
  with nneg[OF \<open>x\<in>A\<close>] show "f x = 0"
    by auto
qed

lemma sum_leq_infsetsum:
  fixes f :: "_ \<Rightarrow> real"
  assumes "f abs_summable_on N"
  and "finite M"
  and "M \<subseteq> N"
  and "\<And>x. x\<in>N-M \<Longrightarrow> f x \<ge> 0"
  shows "sum f M \<le> infsetsum f N"
proof -
  have "infsetsum f M \<le> infsetsum f N"
  proof (rule infsetsum_mono_neutral_left)
    show "f abs_summable_on M"
      by (simp add: assms(2))      
    show "f abs_summable_on N"
      by (simp add: assms(1))      
    show "f x \<le> f x"
      if "x \<in> M"
      for x :: 'b
      using that
      by simp 
    show "M \<subseteq> N"
      by (simp add: assms(3))      
    show "0 \<le> f x"
      if "x \<in> N - M"
      for x :: 'b
      using that
      by (simp add: assms(4)) 
  qed
  thus ?thesis
    using assms by auto
qed

lemma infsetsum_cmult_left':
  fixes f :: "'a \<Rightarrow> 'b :: {banach, real_normed_algebra, second_countable_topology, division_ring}"
  shows  "infsetsum (\<lambda>x. f x * c) A = infsetsum f A * c"
proof (cases "c \<noteq> 0 \<longrightarrow> f abs_summable_on A")
  case True
  have "(\<Sum>\<^sub>ax\<in>A. f x * c) = infsetsum f A * c"
    if "f abs_summable_on A"
    using infsetsum_cmult_left that by blast
  thus ?thesis
    using True by auto     
next
  case False
  hence "c\<noteq>0" and "\<not> f abs_summable_on A"
    by auto
  have "\<not> (\<lambda>x. f x * c) abs_summable_on A"
  proof (rule notI)
    assume "(\<lambda>x. f x * c) abs_summable_on A"
    hence "(\<lambda>x. (f x * c) * inverse c) abs_summable_on A"
      by (rule abs_summable_on_cmult_left)
    with \<open>\<not> f abs_summable_on A\<close> show False
      by (metis (no_types, lifting) False Groups.mult_ac(1) abs_summable_on_cong mult_1_right
          right_inverse)
  qed
  with \<open>\<not> f abs_summable_on A\<close>
  show ?thesis 
    by (simp add: not_summable_infsetsum_eq)
qed

lemma abs_summable_on_zero_diff:
  assumes "f abs_summable_on A"
  and "\<And>x. x \<in> B - A \<Longrightarrow> f x = 0"
  shows "f abs_summable_on B"
proof (rewrite at B DEADID.rel_mono_strong [of _ "(B-A) \<union> (A\<inter>B)"])
  show "B = B - A \<union> A \<inter> B"
    by auto
  have "(\<lambda>x. 0::real) abs_summable_on B - A"
    by simp    
  moreover have "norm (f x) \<le> 0"
    if "x \<in> B - A"
    for x :: 'a
    using that
    by (simp add: assms(2)) 
  ultimately have "f abs_summable_on B - A"
    by (rule abs_summable_on_comparison_test' [where g = "\<lambda>x. 0"])   
  moreover have "f abs_summable_on A \<inter> B"
      using abs_summable_on_subset assms(1) by blast
  ultimately show "f abs_summable_on B - A \<union> A \<inter> B"
    by (rule abs_summable_on_union)    
qed

lemma abs_summable_on_Sigma_iff:
  "f abs_summable_on Sigma A B \<longleftrightarrow>
             (\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x) \<and>
             ((\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A)"
proof auto
  assume sum_AB: "f abs_summable_on Sigma A B"
  define S' where "S' = {x\<in>Sigma A B. 0 \<noteq> f x}"
  from sum_AB have "countable S'"
    unfolding S'_def by (rule abs_summable_countable)
  define A' B' where "A' = fst ` S'" and "B' x = B x \<inter> snd ` S'" for x
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
  have "Sigma A' B' \<subseteq> Sigma A B"
    using A'A B'B by (rule Sigma_mono)
  hence sum_A'B': "f abs_summable_on Sigma A' B'"
    using sum_AB abs_summable_on_subset by auto 
  from sum_A'B' have "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x \<in> A'" for x
    using abs_summable_on_Sigma_iff[OF cntA cntB, where f=f] that by auto
  moreover have "(\<lambda>y. f (x, y)) abs_summable_on B' x" 
    if t:"x \<in> A - A'" 
    for x
  proof (subst abs_summable_on_zero_diff [where A = "{}"])
    show "(\<lambda>y. f (x, y)) abs_summable_on {}"
      by simp
    have "f (x, a) = 0"
      if "a \<in> B' x"
      for a
      using t f0 that B'B
      by auto
    thus "f (x, a) = 0"
      if "a \<in> B' x - {}"
      for a
      using that by auto 
    show True by blast
  qed     
  ultimately have "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x \<in> A" for x
    using that by auto
  thus "(\<lambda>y. f (x, y)) abs_summable_on B x" if "x \<in> A" for x
    apply (rule abs_summable_on_zero_diff)
    using that f0' by auto

  have Q: "\<And>x. x \<in> A - A' \<Longrightarrow> (\<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) = 0"
    apply (subst infsetsum_cong[where g=\<open>\<lambda>x. 0\<close> and B="B' _"])
    using f0 B'B by auto

  from sum_A'B' have "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B' x)) abs_summable_on A'"
    using abs_summable_on_Sigma_iff[OF cntA cntB, where f=f] by auto
  hence "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B' x)) abs_summable_on A"
    apply (rule abs_summable_on_zero_diff)
    using Q by auto
  have R: "\<And>x. x \<in> A \<Longrightarrow>
         (\<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) =
         (\<Sum>\<^sub>ay\<in>B x. norm (f (x, y)))"
  proof (rule infsetsum_cong_neutral)
    show "norm (f (x, a)) = 0"
      if "x \<in> A"
        and "a \<in> B' x - B x"
      for x :: 'a
        and a :: 'b
      using that B'B by blast 
    show "norm (f (x, a)) = 0"
      if "x \<in> A"
        and "a \<in> B x - B' x"
      for x :: 'a
        and a :: 'b
      using that
      by (simp add: f0') 
    show "norm (f (x, a)) = norm (f (x, a))"
      if "x \<in> A"
        and "a \<in> B' x \<inter> B x"
      for x :: 'a
        and a :: 'b
      using that
      by simp 
  qed
  thus "(\<lambda>x. infsetsum (\<lambda>y. norm (f (x, y))) (B x)) abs_summable_on A"    
    using \<open>(\<lambda>x. \<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) abs_summable_on A\<close> by auto 
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
    hence "norm (f (x, y)) = 0"
      apply (rule infsetsum_0D)
      using sum_B that by auto
    thus ?thesis
      by auto
  qed

  from sum_B have sum_B': "(\<lambda>y. f (x, y)) abs_summable_on B' x" if "x\<in>A" for x
  proof (rule_tac abs_summable_on_subset [where B = "B x"])
    show "(\<lambda>y. f (x, y)) abs_summable_on B x"
      if "\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x"
      using that \<open>x \<in> A\<close> by blast 
    show "B' x \<subseteq> B x"
      if "\<forall>x\<in>A. (\<lambda>y. f (x, y)) abs_summable_on B x"
      using that
      by (simp add: B'B) 
  qed
  have *: "(\<Sum>\<^sub>ay\<in>B x. norm (f (x, y))) = (\<Sum>\<^sub>ay\<in>B' x. norm (f (x, y)))" if "x\<in>A" for x
    using infsetsum_cong_neutral f0' B'B that
    by (metis (no_types, lifting) DiffD1 DiffD2 Int_iff inf.absorb_iff2 norm_zero)
  have "(\<lambda>x. \<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) abs_summable_on A"
    using abs_summable_on_cong sum_A "*" by auto
  hence sum_A': "(\<lambda>x. \<Sum>\<^sub>ay\<in>B' x. norm (f (x, y))) abs_summable_on A'"
    using _ A'A abs_summable_on_subset by blast 
  from sum_A' sum_B'
  have "f abs_summable_on Sigma A' B'"
    using abs_summable_on_Sigma_iff[where A=A' and B=B' and f=f, OF cnt_A' cnt_B'] A'A by auto
  moreover have "f x = 0"
    if "x \<in> Sigma A B - Sigma A' B'" for x
    using that f0 f0' by force     
  ultimately show "f abs_summable_on Sigma A B"
    by (rule abs_summable_on_zero_diff)
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
  proof (rule class.complemented_lattice.intro)
  show "class.bounded_lattice (\<squnion>) (\<lambda>x y. (y::'a) \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_bounded_lattice)
  show "class.complemented_lattice_axioms (\<lambda>x y. (x::'a) \<squnion> - y) uminus (\<squnion>) (\<sqinter>) \<top> \<bottom>"
    by (unfold_locales, auto simp add: diff_eq)
qed


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
  proof (rule class.orthocomplemented_lattice.intro)
  show "class.complemented_lattice (\<lambda>x y. (x::'a) \<squnion> - y) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_complemented_lattice)
  show "class.orthocomplemented_lattice_axioms uminus (\<lambda>x y. (y::'a) \<le> x)"
      by (unfold_locales, auto simp add: diff_eq intro: ortho_antimono)
qed



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
  hence 2: \<open>-x \<sqinter> -y \<le> - (x \<squnion> y)\<close>
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
proof (rule class.orthomodular_lattice.intro)
  show "class.orthocomplemented_lattice (\<lambda>x y. (x::'a) \<squnion> - y) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_orthocomplemented_lattice)
  show "class.orthomodular_lattice_axioms uminus (\<squnion>) (\<lambda>x y. (y::'a) \<le> x) (\<sqinter>)"
  proof (unfold_locales)
    show "(x::'a) \<sqinter> (- x \<squnion> y) = y"
      if "(y::'a) \<le> x"
      for x :: 'a
        and y :: 'a
      using that local.compl_eq_compl_iff local.ortho_antimono local.orthomodular by fastforce
  qed
    
qed


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

lemma onorm_sphere:
  fixes f :: "'a::{real_normed_vector, not_singleton} \<Rightarrow> 'b::real_normed_vector"
  assumes a1: "bounded_linear f"
  shows \<open>onorm f = Sup {norm (f x) | x. norm x = 1}\<close>
proof(cases \<open>f = (\<lambda> _. 0)\<close>)
  case True
  have \<open>(UNIV::'a set) \<noteq> {0}\<close>
    by simp
  hence \<open>\<exists>x::'a. norm x = 1\<close>
    using  ex_norm1
    by blast
  have \<open>norm (f x) = 0\<close>
    for x
    by (simp add: True)      
  hence \<open>{norm (f x) | x. norm x = 1} = {0}\<close>
    using \<open>\<exists>x. norm x = 1\<close> by auto
  hence v1: \<open>Sup {norm (f x) | x. norm x = 1} = 0\<close>
    by simp 
  have \<open>onorm f = 0\<close>
    by (simp add: True onorm_eq_0)  
  thus ?thesis using v1 by simp
next
  case False
  have \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
    if "y \<in> {norm (f x) / norm x |x. True}"
    for y
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
  moreover have "y \<in> {norm (f x) / norm x |x. True}"
    if \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
    for y
  proof(cases \<open>y = 0\<close>)
    case True
    thus ?thesis
      by auto 
  next
    case False
    hence \<open>y \<notin> {0}\<close>
      by simp
    hence \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
      using that by auto      
    hence \<open>\<exists> x. norm x = 1 \<and> y = norm (f x)\<close>
      by auto
    then obtain x where \<open>norm x = 1\<close> and \<open>y = norm (f x)\<close>
      by auto
    have \<open>y = norm (f x) / norm x\<close> using  \<open>norm x = 1\<close>  \<open>y = norm (f x)\<close>
      by simp 
    thus ?thesis
      by auto 
  qed
  ultimately have \<open>{norm (f x) / norm x |x. True} = {norm (f x) |x. norm x = 1} \<union> {0}\<close> 
    by blast
  hence \<open>Sup {norm (f x) / norm x |x. True} = Sup ({norm (f x) |x. norm x = 1} \<union> {0})\<close>
    by simp
  moreover have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
  proof-
    have \<open>\<exists> x::'a. norm x = 1\<close>
      by (metis (full_types) False a1 linear_simps(3) norm_sgn)              
    then obtain x::'a where \<open>norm x = 1\<close>
      by blast
    have \<open>norm (f x) \<ge> 0\<close>
      by simp
    hence \<open>\<exists> x::'a. norm x = 1 \<and> norm (f x) \<ge> 0\<close>
      using \<open>norm x = 1\<close> by blast
    hence \<open>\<exists> y \<in> {norm (f x) |x. norm x = 1}. y \<ge> 0\<close>
      by blast
    then obtain y::real where \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> 
      and \<open>y \<ge> 0\<close>
      by auto
    have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
      using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> by blast         
    moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
      using bdd_above_norm_f
      by (metis (mono_tags, lifting) a1) 
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
      using a1 bdd_above_norm_f by force
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
  ultimately have w1: "Sup {norm (f x) / norm x | x. True} = Sup {norm (f x) | x. norm x = 1}"
    by simp 

  have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) / norm x | x. True}\<close>
    by (simp add: full_SetCompr_eq)
  also have \<open>... = Sup {norm (f x) | x. norm x = 1}\<close>
    using w1 by auto
  ultimately  have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) | x. norm x = 1}\<close>
    by linarith
  thus ?thesis unfolding onorm_def by blast
qed


lemma onorm_Inf_bound:
  fixes f :: \<open>'a::{real_normed_vector,not_singleton} \<Rightarrow> 'b::real_normed_vector\<close>
  assumes a1: "bounded_linear f"
  shows "onorm f = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}"
proof-
  have a2: \<open>(UNIV::'a set) \<noteq> {0}\<close>
    by simp

  define A where \<open>A = {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
  have \<open>A \<noteq> {}\<close>
  proof-
    have \<open>\<exists> x::'a. x \<noteq> 0\<close>
      using a2 by auto
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
  ultimately have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} 
                    = Inf {K. (\<forall>x\<noteq>0. norm (f x)/ norm x \<le>  K)}\<close>
    using A_def
    by simp 
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
  ultimately have f1: \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
    by simp
  moreover 
  have t1: \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0}  = {norm (f x) / (norm x) | x. True}\<close>
    using Collect_cong by blast

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
      using \<open>bounded_linear f\<close> bounded_linear.nonneg_bounded 
        mult_divide_mult_cancel_left_if norm_zero real_divide_square_eq
      by (metis nice_ordered_field_class.mult_imp_div_pos_le ordered_field_class.sign_simps(5) 
          zero_less_norm_iff)
    thus ?thesis
      by auto 
  qed
  moreover have \<open>{norm (f x) / (norm x) | x. x = 0} \<noteq> {}\<close>
    by simp
  moreover have \<open>bdd_above {norm (f x) / (norm x) | x. x = 0}\<close>
    by simp
  ultimately 
  have d1: \<open>Sup ({norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0})
        = max (Sup {norm (f x) / (norm x) | x. x \<noteq> 0}) (Sup {norm (f x) / (norm x) | x. x = 0})\<close>
    by (metis (no_types, lifting) cSup_union_distrib sup_max)
  have g1: \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} \<ge> 0\<close>
  proof-
    have t2: \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<noteq> {}\<close>
    proof-
      have \<open>\<exists> x::'a. x \<noteq> 0\<close>
        using \<open>UNIV\<noteq>{0}\<close> by auto
      thus ?thesis 
        by auto
    qed
    have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
      using \<open>bounded_linear f\<close>
      by (metis \<open>\<And>K. (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) \<le> norm x * K) = (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) / norm x \<le> K)\<close> bounded_linear.nonneg_bounded mult_divide_mult_cancel_left_if norm_zero real_divide_square_eq)
    hence t3: \<open>bdd_above {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
      by auto
    have \<open>norm (f x) / (norm x) \<ge> 0\<close>
      for x
      by simp
    hence \<open>\<forall> y\<in>{norm (f x) / (norm x) | x. x \<noteq> 0}. y \<ge> 0\<close>
      by blast
    show ?thesis
      by (metis (lifting) \<open>\<forall>y\<in>{norm (f x) / norm x |x. x \<noteq> 0}. 0 \<le> y\<close> \<open>bdd_above {norm (f x) / norm x |x. x \<noteq> 0}\<close> \<open>{norm (f x) / norm x |x. x \<noteq> 0} \<noteq> {}\<close> bot.extremum_uniqueI cSup_upper2 subset_emptyI)
  qed
  hence r: \<open>Sup ({norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0}) 
         = Sup {norm (f x) / (norm x) | x. True}\<close>
    using t1 by auto
  have \<open>{norm (f x) / (norm x) | x. x = 0} = {norm (f 0) / (norm 0)}\<close>
    by simp
  hence \<open>Sup {norm (f x) / (norm x) | x. x = 0} = 0\<close>
    by simp
  have h1: \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Sup {norm (f x) / (norm x) | x. True}\<close>
    using d1 r g1 by auto 
  have \<open>(SUP x. norm (f x) / (norm x)) = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
    using full_SetCompr_eq
    by (metis \<open>\<Squnion> {norm (f x) / norm x |x. x \<noteq> 0} = \<Sqinter> {K. \<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) \<le> norm x * K}\<close> h1) 
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
    have t1: \<open>inverse (norm x) \<ge> 0\<close>
      using \<open>norm x > 0\<close>
      by simp
    have t2: \<open>norm (f x) \<ge> 0\<close>
      by simp
    have t3: \<open>K \<ge> 0\<close>
      using \<open>inverse (norm x) * norm (f x) \<le> K\<close> \<open>inverse (norm x) \<ge> 0\<close> \<open>norm x > 0\<close> t2
      by (metis \<open>norm (f (x /\<^sub>R norm x)) \<le> K\<close> dual_order.trans norm_ge_zero)
    have t4: "\<forall>r. norm x * (inverse (norm x) * r) = r"
      by (metis \<open>norm (x /\<^sub>R norm x) = 1\<close> ab_semigroup_mult_class.mult_ac(1) abs_inverse abs_norm_cancel mult.commute mult.left_neutral norm_scaleR)
    hence t5: "norm (f x) \<le> K * norm x"
      by (metis (no_types) \<open>inverse (norm x) * norm (f x) \<le> K\<close> mult.commute norm_ge_zero real_scaleR_def scaleR_left_mono)
    show ?thesis
      using mult.commute
      by (simp add: mult.commute t5)
  qed
  thus ?thesis using \<open>linear f\<close> unfolding bounded_linear_def bounded_linear_axioms_def by blast
qed

lemma norm_unit_sphere:
  includes notation_norm
  fixes f::\<open>'a::{real_normed_vector,not_singleton} \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
  assumes a1: "bounded_linear f" and a2: "e > 0"     
  shows \<open>\<exists>x\<in>(sphere 0 1). \<parallel> \<parallel>f *\<^sub>v x\<parallel> - \<parallel>f\<parallel> \<parallel> < e\<close>
proof-
  define S::"real set" where \<open>S = { norm (f x)| x. x \<in> sphere 0 1 }\<close>
  have "\<exists>x::'a. \<parallel>x\<parallel> = 1"
    by (simp add: ex_norm1)    
  hence \<open>\<exists>x::'a. x \<in> sphere 0 1\<close>
    by simp                
  hence \<open>S\<noteq>{}\<close>unfolding S_def 
    by auto 
  hence t1: \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. Sup S - e < y\<close>
    for e
    by (simp add: less_cSupD)
  have \<open>onorm f = Sup { norm (f x)| x. norm x = 1 }\<close>
    using \<open>bounded_linear f\<close> onorm_sphere
    by auto      
  hence \<open>onorm f = Sup { norm (f x)| x. x \<in> sphere 0 1 }\<close>
    unfolding sphere_def
    by simp
  hence t2: \<open>Sup S = onorm f\<close> unfolding S_def 
    by auto
  have s1: \<open>\<exists>y\<in>{norm (f x) |x. x \<in> sphere 0 1}. norm (onorm f - y) < e\<close>
    if "0 < e"
    for e
  proof-
    have \<open>\<exists> y \<in> S. (onorm f) - e < y\<close>
      using t1 t2 that by auto
    hence \<open>\<exists> y \<in> S. (onorm f) - y  < e\<close>
      using that
      by force
    have \<open>\<exists> y \<in> S. (onorm f) - y  < e\<close>
      using \<open>0 < e\<close> \<open>\<exists>y\<in>S. onorm f - y < e\<close> by auto
    then obtain y where \<open>y \<in> S\<close> and \<open>(onorm f) - y  < e\<close>
      by blast
    have \<open>y \<in> {norm (f x) |x. x \<in> sphere 0 1} \<Longrightarrow> y \<le> onorm f\<close>
    proof-
      assume \<open>y \<in> {norm (f x) |x. x \<in> sphere 0 1}\<close>
      hence \<open>\<exists> x \<in> sphere 0 1. y = norm (f x)\<close>
        by blast
      then obtain x where \<open>x \<in> sphere 0 1\<close> and \<open>y = norm (f x)\<close>
        by blast
      from \<open>y = norm (f x)\<close>
      have \<open>y \<le> onorm f * norm x\<close>
        using a1 onorm by auto
      moreover have \<open>norm x = 1\<close>
        using  \<open>x \<in> sphere 0 1\<close> unfolding sphere_def by auto
      ultimately show ?thesis by simp
    qed
    hence \<open>bdd_above {norm (f x) |x. x \<in> sphere 0 1}\<close>
      using a1 bdd_above_norm_f by force
    hence \<open>bdd_above S\<close> unfolding S_def 
      by blast
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
    hence \<open>\<exists> y \<in> S. norm ((onorm f) - y)  < e\<close>
      using \<open>onorm f - y < e\<close> \<open>y \<in> S\<close> by force    
    show ?thesis
      unfolding S_def
      using S_def \<open>\<exists>y\<in>S. \<parallel>onorm ((*\<^sub>v) f) - y\<parallel> < e\<close> by blast      
  qed
  have f2: "onorm ((*\<^sub>v) f) = \<Squnion> S"
    using S_def \<open>onorm ((*\<^sub>v) f) = \<Squnion> {\<parallel>f *\<^sub>v x\<parallel> |x. x \<in> sphere 0 1}\<close> by blast
  hence "\<exists>a. \<parallel>\<parallel>f *\<^sub>v a\<parallel> - \<Squnion> S\<parallel> < e \<and> a \<in> sphere 0 1"
    using a1 a2 s1 a2 t2 
    by force 
  thus ?thesis
    using f2 by (metis (full_types) norm_blinfun.rep_eq)  
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

subsection\<open>Unclassified\<close>

lemma complete_singleton: 
  "complete {s::'a::uniform_space}"
proof-
  have "\<And>F. F \<le> principal {s} \<Longrightarrow>
         F \<noteq> \<bottom> \<Longrightarrow> cauchy_filter F \<Longrightarrow> F \<le> nhds s"
    by (meson dual_order.trans empty_subsetI insert_subset le_nhds le_principal principal_le_iff)
  thus ?thesis
    unfolding complete_uniform
    by simp
qed

lemma onormI:
  assumes "\<And>x. norm (f x) \<le> b * norm x"
    and "x \<noteq> 0" and "norm (f x) = b * norm x"
  shows "onorm f = b"
proof (unfold onorm_def, rule cSup_eq_maximum)
  from assms(2) have "norm x \<noteq> 0"
    by auto
  with assms(3) 
  have "norm (f x) / norm x = b"
    by auto
  thus "b \<in> range (\<lambda>x. norm (f x) / norm x)"
    by auto
next
  fix y 
  assume "y \<in> range (\<lambda>x. norm (f x) / norm x)"
  then obtain x where y_def: "y = norm (f x) / norm x"
    by auto
  thus "y \<le> b"
    unfolding y_def using assms(1)[of x]
    by (metis assms(2) assms(3) divide_eq_0_iff linordered_field_class.pos_divide_le_eq norm_ge_zero norm_zero zero_less_norm_iff)
qed

lemmas has_derivative_of_real [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_of_real]

lemma cmod_Re:
  assumes "x \<ge> 0"
  shows "cmod x = Re x"
  using assms unfolding less_eq_complex_def cmod_def
  by auto


lemma class_not_singletonI_monoid_add:
  assumes "(UNIV::'a set) \<noteq> 0"
  shows "class.not_singleton TYPE('a::monoid_add)"
proof intro_classes
  let ?univ = "UNIV :: 'a set"
  from assms obtain x::'a where "x \<noteq> 0"
    by auto
  thus "\<exists>x y :: 'a. x \<noteq> y"
    by auto
qed

instantiation unit :: CARD_1
begin
instance 
  proof standard
  show "card (UNIV::unit set) = 1"
    by auto
qed 

end

lemma abs_complex_real[simp]: "abs x \<in> \<real>" for x :: complex
  by (simp add: abs_complex_def)

lemma Im_abs[simp]: "Im (abs x) = 0"
  using abs_complex_real complex_is_Real_iff by blast

fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"

lemma index_of_correct:
  assumes "x \<in> set y"
  shows "y ! index_of x y = x"
  using assms 
proof(induction y arbitrary: x)
  case Nil
  thus ?case by auto
next
  case (Cons a y)
  thus ?case by auto
qed

lemma enum_idx_correct: 
  "Enum.enum ! enum_idx i = i"
proof-
  have "i \<in> set enum_class.enum"
    using UNIV_enum by blast 
  thus ?thesis
    unfolding enum_idx_def
    using index_of_correct by metis
qed

lemma index_of_bound: 
  assumes "y \<noteq> []" and "x \<in> set y"
  shows "index_of x y < length y"
  using assms proof(induction y arbitrary: x)
  case Nil
  thus ?case by auto
next
  case (Cons a y)
  show ?case 
  proof(cases "a = x")
    case True
    thus ?thesis by auto
  next
    case False
    moreover have "a \<noteq> x \<Longrightarrow> index_of x y < length y"
      using Cons.IH Cons.prems(2) by fastforce      
    ultimately show ?thesis by auto
  qed
qed

lemma enum_idx_bound: "enum_idx x < length (Enum.enum :: 'a list)" for x :: "'a::enum"
proof-
  have p1: "False"
    if "(Enum.enum :: 'a list) = []"
  proof-
    have "(UNIV::'a set) = set ([]::'a list)"
      using that UNIV_enum by metis
    also have "\<dots> = {}"
      by blast
    finally have "(UNIV::'a set) = {}".
    thus ?thesis by simp
  qed    
  have p2: "x \<in> set (Enum.enum :: 'a list)"
    using UNIV_enum by auto
  moreover have "(enum_class.enum::'a list) \<noteq> []"
    using p2 by auto
  ultimately show ?thesis
    unfolding enum_idx_def     
    using index_of_bound [where x = x and y = "(Enum.enum :: 'a list)"]
    by auto   
qed

lemma index_of_nth:
  assumes "distinct xs"
  assumes "i < length xs"
  shows "index_of (xs ! i) xs = i"
  using assms
  by (metis gr_implies_not_zero index_of_bound index_of_correct length_0_conv nth_eq_iff_index_eq nth_mem)

lemma enum_idx_enum: 
  assumes \<open>i < CARD('a::enum)\<close>
  shows \<open>enum_idx (enum_class.enum ! i :: 'a) = i\<close>
  unfolding enum_idx_def apply (rule index_of_nth)
  using assms by (simp_all add: card_UNIV_length_enum enum_distinct)

lemma cnj_x_x: "cnj x * x = (abs x)\<^sup>2"
  proof (cases x)
  show "cnj x * x = \<bar>x\<bar>\<^sup>2"
    if "x = Complex x1 x2"
    for x1 :: real
      and x2 :: real
    using that   by (auto simp: complex_cnj complex_mult abs_complex_def 
        complex_norm power2_eq_square complex_of_real_def)
qed

lemma cnj_x_x_geq0[simp]: "cnj x * x \<ge> 0"
  proof (cases x)
  show "0 \<le> cnj x * x"
    if "x = Complex x1 x2"
    for x1 :: real
      and x2 :: real
    using that by (auto simp: complex_cnj complex_mult complex_of_real_def less_eq_complex_def)
qed


lemma map_filter_map: "List.map_filter f (map g l) = List.map_filter (f o g) l"
proof (induction l)
  show "List.map_filter f (map g []) = List.map_filter (f \<circ> g) []"
    by (simp add: map_filter_simps)
  show "List.map_filter f (map g (a # l)) = List.map_filter (f \<circ> g) (a # l)"
    if "List.map_filter f (map g l) = List.map_filter (f \<circ> g) l"
    for a :: 'c
      and l :: "'c list"
    using that  map_filter_simps(1)
    by (metis comp_eq_dest_lhs list.simps(9))
qed


lemma map_filter_Some[simp]: "List.map_filter (\<lambda>x. Some (f x)) l = map f l"
  proof (induction l)
  show "List.map_filter (\<lambda>x. Some (f x)) [] = map f []"
    by (simp add: map_filter_simps)
  show "List.map_filter (\<lambda>x. Some (f x)) (a # l) = map f (a # l)"
    if "List.map_filter (\<lambda>x. Some (f x)) l = map f l"
    for a :: 'b
      and l :: "'b list"
    using that by (simp add: map_filter_simps(1))
qed

lemma filter_Un: "Set.filter f (x \<union> y) = Set.filter f x \<union> Set.filter f y"
  unfolding Set.filter_def by auto

lemma Set_filter_unchanged: "Set.filter P X = X" if "\<And>x. x\<in>X \<Longrightarrow> P x" for P and X :: "'z set"
  using that unfolding Set.filter_def by auto

end

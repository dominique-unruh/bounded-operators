section \<open>General missing things\<close>

theory Extra_General
  imports "HOL-Library.Cardinality"
    "HOL-Analysis.Elementary_Topology"
    Jordan_Normal_Form.Conjugate
    "HOL-Analysis.Uniform_Limit"
    "HOL-Library.Set_Algebras"
begin

subsection \<open>Misc\<close>

lemma reals_zero_comparable_iff:
  "(x::complex)\<in>\<real> \<longleftrightarrow> x \<le> 0 \<or> x \<ge> 0"
  unfolding complex_is_Real_iff less_eq_complex_def
  by auto

(* TODO: move to extras *)
lemma reals_zero_comparable:
  fixes x::complex
  assumes "x\<in>\<real>"
  shows "x \<le> 0 \<or> x \<ge> 0"
  using assms unfolding reals_zero_comparable_iff by assumption

(* TODO: remove *)
abbreviation (input) uniform_convergence_abbr::
  \<open>'a set \<Rightarrow> (nat \<Rightarrow> ('a \<Rightarrow>'b::metric_space)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  (\<open>(_): ((_)/ \<midarrow>uniformly\<rightarrow> (_))\<close> [60, 60, 60] 60)
  where \<open>S: f \<midarrow>uniformly\<rightarrow> l \<equiv> (  uniform_limit S f l sequentially )\<close>

subsection \<open>Not singleton\<close>

class not_singleton =
  assumes not_singleton_card: "\<exists>x y. x \<noteq> y"

lemma not_singleton_existence[simp]:
  \<open>\<exists> x::('a::not_singleton). x \<noteq> t\<close>
proof (rule ccontr)
  assume \<open>\<nexists>x::'a. x \<noteq> t\<close> 
  have \<open>\<exists>x::'a. \<exists>y. x \<noteq> y\<close>
    using not_singleton_card
    by blast
  then obtain x y::'a where \<open>x \<noteq> y\<close>
    by blast
  have \<open>\<forall>x::'a. x = t\<close>
    using \<open>\<nexists>x::'a. x \<noteq> t\<close> by simp
  hence \<open>x = t\<close>
    by blast
  moreover have \<open>y = t\<close>
    using \<open>\<forall>x::'a. x = t\<close>
    by blast
  ultimately have \<open>x = y\<close>
    by simp
  thus False
    using \<open>x \<noteq> y\<close> by auto 
qed

lemma UNIV_not_singleton[simp]: "(UNIV::_::not_singleton set) \<noteq> {x}"
  using not_singleton_existence[of x] by blast

lemma UNIV_not_singleton_converse: 
  assumes"\<And>x::'a. UNIV \<noteq> {x}"
  shows "\<exists>x::'a. \<exists>y. x \<noteq> y"
  using assms
  by fastforce 

(* lemma UNIV_not_singleton_converse_zero: 
  assumes "UNIV \<noteq> {0::'a::real_normed_vector}"
  shows "\<exists>x::'a. \<exists>y. x \<noteq> y"
  using UNIV_not_singleton_converse assms
  by fastforce  *)

subclass (in card2) not_singleton
  apply standard using two_le_card
  by (meson card_2_iff' obtain_subset_with_card_n)

lemma class_not_singletonI_monoid_add:
  assumes "(UNIV::'a set) \<noteq> {0}"
  shows "class.not_singleton TYPE('a::monoid_add)"
proof intro_classes
  let ?univ = "UNIV :: 'a set"
  from assms obtain x::'a where "x \<noteq> 0"
    by auto
  thus "\<exists>x y :: 'a. x \<noteq> y"
    by auto
qed

subsection \<open>CARD_1\<close>

context CARD_1 begin

lemma everything_the_same[simp]: "(x::'a)=y"
  by (metis (full_types) UNIV_I card_1_singletonE empty_iff insert_iff local.CARD_1)

lemma CARD_1_UNIV: "UNIV = {x::'a}"
  by (metis (full_types) UNIV_I card_1_singletonE local.CARD_1 singletonD)

lemma CARD_1_ext: "x (a::'a) = y b \<Longrightarrow> x = y"
proof (rule ext)
  show "x t = y t"
    if "x a = y b"
    for t :: 'a
    using that  apply (subst (asm) everything_the_same[where x=a])
    apply (subst (asm) everything_the_same[where x=b])
    by simp
qed 

end

instance unit :: CARD_1
  apply standard by auto

instance prod :: (CARD_1, CARD_1) CARD_1
  apply intro_classes
  by (simp add: CARD_1)

instance "fun" :: (CARD_1, CARD_1) CARD_1
  apply intro_classes
  by (auto simp add: card_fun CARD_1)

subsection \<open>Topology\<close>

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


lemma tendsto_add_const_iff:
  \<comment> \<open>This is a generalization of \<open>Limits.tendsto_add_const_iff\<close>, 
      the only difference is that the sort here is more general.\<close>
  "((\<lambda>x. c + f x :: 'a::topological_group_add) \<longlongrightarrow> c + d) F \<longleftrightarrow> (f \<longlongrightarrow> d) F"
  using tendsto_add[OF tendsto_const[of c], of f d]
    and tendsto_add[OF tendsto_const[of "-c"], of "\<lambda>x. c + f x" "c + d"] by auto

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


lemma tendsto_principal_singleton:
  shows "(f \<longlongrightarrow> f x) (principal {x})"
  unfolding tendsto_def eventually_principal by simp

lemma complete_singleton: 
  "complete {s::'a::uniform_space}"
proof-
  have "F \<le> principal {s} \<Longrightarrow>
         F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> F \<le> nhds s" for F
    by (metis eventually_nhds eventually_principal le_filter_def singletonD)
  thus ?thesis
    unfolding complete_uniform
    by simp
qed

subsection \<open>Complex numbers\<close>

lemma cmod_Re:
  assumes "x \<ge> 0"
  shows "cmod x = Re x"
  using assms unfolding less_eq_complex_def cmod_def
  by auto

lemma abs_complex_real[simp]: "abs x \<in> \<real>" for x :: complex
  by (simp add: abs_complex_def)

lemma Im_abs[simp]: "Im (abs x) = 0"
  using abs_complex_real complex_is_Real_iff by blast


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
    using that by (auto simp: complex_cnj complex_mult complex_of_real_def)
qed


subsection \<open>List indices and enum\<close>


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

subsubsection \<open>Filtering lists/sets\<close>



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

lemma unique_choice: "\<forall>x. \<exists>!y. Q x y \<Longrightarrow> \<exists>!f. \<forall>x. Q x (f x)"
  apply (auto intro!: choice ext) by metis

lemma sum_single: 
  assumes "finite A"
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  shows "sum f A = (if i\<in>A then f i else 0)"
  apply (subst sum.mono_neutral_cong_right[where S=\<open>A \<inter> {i}\<close> and h=f])
  using assms by auto

lemma image_set_plus: 
  assumes \<open>linear U\<close>
  shows \<open>U ` (A + B) = U ` A + U ` B\<close>
  unfolding image_def set_plus_def
  using assms by (force simp: linear_add)

consts heterogenous_identity :: \<open>'a \<Rightarrow> 'b\<close>
overloading heterogenous_identity_id \<equiv> "heterogenous_identity :: 'a \<Rightarrow> 'a" begin
definition heterogenous_identity_def[simp]: \<open>heterogenous_identity_id = id\<close>
end

lemma bdd_above_image_mono:
  assumes \<open>\<And>x. x\<in>S \<Longrightarrow> f x \<le> g x\<close>
  assumes \<open>bdd_above (g ` S)\<close>
  shows \<open>bdd_above (f ` S)\<close>
  by (smt (verit, ccfv_threshold) assms(1) assms(2) bdd_aboveI2 bdd_above_def order_trans rev_image_eqI)

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


end

section\<open>Preliminaries\<close>

theory Preliminaries
  imports
    "Jordan_Normal_Form.Conjugate" 
    Banach_Steinhaus.Banach_Steinhaus
    "HOL.Real_Vector_Spaces"

    Extra_General
    Extra_Operator_Norm
begin

(* TODO: Split this into separate files *)


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
    by (metis Collect_empty_eq Extra_General.UNIV_not_singleton UNIV_I equalityI mem_Collect_eq norm_sgn singleton_conv subsetI)
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
  have f2: "onorm ((*\<^sub>v) f) = Sup S"
    using S_def \<open>onorm ((*\<^sub>v) f) = Sup {\<parallel>f *\<^sub>v x\<parallel> |x. x \<in> sphere 0 1}\<close> by blast
  hence "\<exists>a. \<parallel>\<parallel>f *\<^sub>v a\<parallel> - Sup S\<parallel> < e \<and> a \<in> sphere 0 1"
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
         F \<noteq> bot \<Longrightarrow> cauchy_filter F \<Longrightarrow> F \<le> nhds s"
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

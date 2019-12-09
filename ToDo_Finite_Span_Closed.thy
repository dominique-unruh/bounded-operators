theory ToDo_Finite_Span_Closed
  imports ToDo "HOL-Types_To_Sets.Types_To_Sets"
begin

(* TODO move definition and properties of euclidean_space somewhere appropriate (maybe General_Results_Missing) *)
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
    apply transfer using indicator_eq_0_iff by fastforce
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

lemma finite_span_complete_aux:
  fixes b :: "'b::real_normed_vector" and B :: "'b set"
    and  rep :: "'basis::finite \<Rightarrow> 'b" and abs :: "'b \<Rightarrow> 'basis"
  assumes t: "type_definition rep abs B"
  assumes "finite B" and "b\<in>B" and "independent B"
  (* shows "bounded_linear (\<lambda>\<psi>. real_vector.representation B \<psi> b)" *)
  shows "\<exists>D>0. \<forall>\<psi>. norm (real_vector.representation B \<psi> b) \<le> norm \<psi> * D"
    and "complete (real_vector.span B)"
proof -
  define repr  where "repr = real_vector.representation B"
  define repr' where "repr' \<psi> = Abs_euclidean_space (repr \<psi> o rep)" for \<psi>
  define comb  where "comb l = (\<Sum>b\<in>B. l b *\<^sub>R b)" for l
  define comb' where "comb' l = comb (Rep_euclidean_space l o abs)" for l

  have comb_cong: "comb x = comb y" if "\<And>z. z\<in>B \<Longrightarrow> x z = y z" for x y
    unfolding comb_def using that by auto
  have comb_repr[simp]: "comb (repr \<psi>) = \<psi>" if "\<psi> \<in> real_vector.span B" for \<psi>
    unfolding comb_def repr_def 
    apply (rule sum_representation_eq)
    using assms that by auto
  have repr_comb[simp]: "repr (comb x) = (\<lambda>b. if b\<in>B then x b else 0)" for x
    unfolding repr_def comb_def
    apply (rule representation_eqI)
    using \<open>independent B\<close> \<open>finite B\<close> apply (auto simp add: span_base span_scale span_sum)
    apply meson
    by (smt DiffD1 DiffD2 mem_Collect_eq scale_eq_0_iff subset_eq sum.mono_neutral_cong_left)
  have repr_bad[simp]: "repr \<psi> = (\<lambda>_. 0)" if "\<psi> \<notin> real_vector.span B" for \<psi>
    unfolding repr_def using that
    by (simp add: representation_def)
  have [simp]: "repr' \<psi> = 0" if "\<psi> \<notin> real_vector.span B" for \<psi>
    unfolding repr'_def repr_bad[OF that]
    by (transfer fixing: rep, simp)
  have comb'_repr'[simp]: "comb' (repr' \<psi>) = \<psi>" if "\<psi> \<in> real_vector.span B" for \<psi>
  proof -
    have "comb' (repr' \<psi>) = comb ((repr \<psi> \<circ> rep) \<circ> abs)"
      unfolding comb'_def repr'_def
      by (subst Abs_euclidean_space_inverse; simp)
    also have "\<dots> = comb (repr \<psi>)"
      apply (rule comb_cong) unfolding o_def
      by (subst type_definition.Abs_inverse[OF t]; simp)
    also have "\<dots> = \<psi>"
      using that by simp
    finally show ?thesis by -
  qed
  have repr'_comb'[simp]: "repr' (comb' x) = x" for x
    unfolding comb'_def repr'_def o_def
    apply simp
    apply (subst type_definition.Rep_inverse[OF t])
    using type_definition.Rep[OF t] apply simp
    apply (subst Rep_euclidean_space_inverse)
    by simp
  have sphere: "compact (sphere 0 d :: 'basis euclidean_space set)" for d
    using compact_sphere by blast
  
  have "complete (UNIV :: 'basis euclidean_space set)"
    by (simp add: complete_UNIV)

  have blin_comb': "bounded_linear comb'"
    unfolding comb_def comb'_def apply (rule bounded_linearI')
     apply (transfer fixing: abs)
     apply (simp add: scaleR_add_left sum.distrib)
    apply (transfer fixing: abs)
    by (simp add: scale_sum_right)
    
  then have "continuous_on X comb'" for X
    by (simp add: linear_continuous_on)

  then have "compact (comb' ` sphere 0 d)" for d
    using sphere
    apply (rule compact_continuous_image)
    by -

  then have compact_norm_comb': "compact (norm ` comb' ` sphere 0 1)"
    apply (rule compact_continuous_image[rotated])
    apply (rule continuous_on_norm)
    by auto
    
  have not0: "0 \<notin> norm ` comb' ` sphere 0 1"
  proof (rule ccontr, simp)
    assume "0 \<in> norm ` comb' ` sphere 0 1"
    then obtain x where nc0: "norm (comb' x) = 0" and x: "x \<in> sphere 0 1"
      by auto
    then have "comb' x = 0"
      by simp
    then have "repr' (comb' x) = 0"
      unfolding repr'_def o_def repr_def apply simp
      by (smt repr'_comb' blin_comb' dist_0_norm linear_simps(3) mem_sphere norm_zero x)
    then have "x = 0"
      by auto
    with x show False
      by simp
  qed
  have "\<exists>d>0. \<forall>x\<in>norm ` comb' ` sphere 0 1. d \<le> dist 0 x"
      apply (rule_tac separate_point_closed)
    using not0 compact_norm_comb'
     apply auto
    using compact_imp_closed by blast

  then obtain d where d: "x\<in>norm ` comb' ` sphere 0 1 \<Longrightarrow> d \<le> dist 0 x"  
    and "d > 0" for x
    by metis
  define D where "D = 1/d"
  then have "D > 0"
    using \<open>d>0\<close> unfolding D_def by auto
  from d have "x \<ge> d"  if "x\<in>norm ` comb' ` sphere 0 1" for x
    apply auto
    using that by fastforce
  then have *: "norm (comb' x) \<ge> d" if "norm x = 1" for x
    using that by auto
  have norm_comb': "norm (comb' x) \<ge> d * norm x" for x
    apply (cases "x=0")
     apply simp
    using *[of "(1/norm x) *\<^sub>R x"]
    unfolding linear_simps(5)[OF blin_comb']
    apply auto
    by (simp add: le_divide_eq)
  have *:  "norm (repr' \<psi>) \<le> norm \<psi> * D" for \<psi>
    apply (cases "\<psi> \<in> real_vector.span B")
    unfolding D_def
    using norm_comb'[of "repr' \<psi>"] \<open>d>0\<close>
    by (simp_all add: linordered_field_class.mult_imp_le_div_pos mult.commute)
  then have "norm (Rep_euclidean_space (repr' \<psi>) (abs b)) \<le> norm \<psi> * D" for \<psi>
  proof -
    have "(Rep_euclidean_space (repr' \<psi>) (abs b)) = repr' \<psi> \<bullet> euclidean_space_basis_vector (abs b)"
      apply (transfer fixing: abs b)
      apply auto by -
    also have "\<bar>\<dots>\<bar> \<le> norm (repr' \<psi>)"
      apply (rule Basis_le_norm)
      unfolding Basis_euclidean_space_def by simp
    also have "\<dots> \<le> norm \<psi> * D"
      using * by auto
    finally show ?thesis by simp
  qed
  then have "norm (repr \<psi> b) \<le> norm \<psi> * D" for \<psi>
    unfolding repr'_def apply (subst (asm) Abs_euclidean_space_inverse)
     apply auto
    unfolding type_definition.Abs_inverse[OF t \<open>b\<in>B\<close>] by simp
  then show "\<exists>D>0. \<forall>\<psi>. norm (repr \<psi> b) \<le> norm \<psi> * D"
    using \<open>D>0\<close> by auto

  have complete_comb': "complete (comb' ` UNIV)"
    using \<open>d>0\<close> apply (rule complete_isometric_image)
    using blin_comb' norm_comb' complete_UNIV by auto

  have range_comb': "comb' ` UNIV = real_vector.span B"
  proof (auto simp: image_def)
    show "comb' x \<in> real_vector.span B" for x
      by (metis comb'_def comb_cong comb_repr local.repr_def repr_bad repr_comb representation_zero span_zero)
  next
    fix \<psi> assume "\<psi> \<in> real_vector.span B"
    then obtain f where f: "comb f = \<psi>"
      apply atomize_elim
      unfolding real_vector.span_finite[OF \<open>finite B\<close>] comb_def
      by auto
    define f' where "f' b = (if b\<in>B then f b else 0)" for b :: 'b
    have f': "comb f' = \<psi>"
      unfolding f[symmetric]
      apply (rule comb_cong)
      unfolding f'_def by simp
    define x :: "'basis euclidean_space" where "x = Abs_euclidean_space (f' o rep)"
    have "\<psi> = comb' x"
      unfolding comb'_def x_def o_def
      apply (subst Abs_euclidean_space_inverse, simp)
      apply (subst comb_cong[of _ f'])
       apply (subst type_definition.Abs_inverse[OF t]; simp)
      using f' by simp
    then show "\<exists>x. \<psi> = comb' x"
      by auto
  qed

  from range_comb' complete_comb'
  show "complete (real_vector.span B)"
    by simp
qed

lemmas finite_span_complete_aux' = finite_span_complete_aux[internalize_sort "'basis::finite"]

lemma complete_singleton: 
  shows "complete {s::'a::uniform_space}"
  unfolding complete_uniform
  apply auto
  by (meson dual_order.trans empty_subsetI insert_subset le_nhds le_principal principal_le_iff)

lemma finate_span_representation_bounded: 
  fixes B :: "'a::real_normed_vector set"
  assumes "finite B" "independent B"
  shows "\<exists>D>0. \<forall>\<psi> b. norm (real_vector.representation B \<psi> b) \<le> norm \<psi> * D"
proof (cases "B\<noteq>{}")
  case True
  define repr  where "repr = real_vector.representation B"
  {
    assume "\<exists>(Rep :: 'basis\<Rightarrow>'a) Abs. type_definition Rep Abs B"
    then obtain rep :: "'basis \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'basis" where t: "type_definition rep abs B"
      by auto
    have *: "class.finite TYPE('basis)"
      apply intro_classes
      using \<open>finite B\<close> t
      by (metis (mono_tags, hide_lams) ex_new_if_finite finite_imageI image_eqI type_definition_def)
    note finite_span_complete_aux'(1)[OF this t \<open>finite B\<close> _ \<open>independent B\<close>]
  }
  note this[cancel_type_definition, OF True _]
  then have "\<exists>D. \<forall>\<psi>. D>0 \<and> norm (repr \<psi> b) \<le> norm \<psi> * D" if \<open>b\<in>B\<close> for b
    by (simp add: repr_def that True)
  then obtain D where D: "D b > 0 \<and> norm (repr \<psi> b) \<le> norm \<psi> * D b" if "b\<in>B" for b \<psi>
    apply atomize_elim apply (rule choice) by auto
  then have Dpos: "D b > 0" and Dbound: "norm (repr \<psi> b) \<le> norm \<psi> * D b" if "b\<in>B" for b \<psi>
    using that by auto
  define Dall where "Dall = Max (D`B)"
  have "Dall > 0"
    unfolding Dall_def using \<open>finite B\<close> \<open>B\<noteq>{}\<close> Dpos
    apply auto
    by (metis (mono_tags) Max_in True empty_is_image finite_imageI imageE)

  have "Dall \<ge> D b" if "b\<in>B" for b
    unfolding Dall_def using \<open>finite B\<close> that by auto
  with Dbound
  have "norm (repr \<psi> b) \<le> norm \<psi> * Dall" if "b\<in>B" for b \<psi>
    using that apply auto
    by (meson mult_left_mono norm_ge_zero order_trans)
  moreover have "norm (repr \<psi> b) \<le> norm \<psi> * Dall" if "b\<notin>B" for b \<psi>
    unfolding repr_def using representation_ne_zero True
    by (metis calculation empty_subsetI less_le_trans local.repr_def norm_ge_zero norm_zero not_less subsetI subset_antisym)
  ultimately show "\<exists>D>0. \<forall>\<psi> b. norm (repr \<psi> b) \<le> norm \<psi> * D"
    using \<open>Dall > 0\<close> by metis
next
  case False
  then show ?thesis
      unfolding repr_def using representation_ne_zero[of B]
      using nice_ordered_field_class.linordered_field_no_ub by fastforce
qed

lemma
  fixes A :: "'a::real_normed_vector set"
  assumes "finite A"
  shows finite_span_complete: "complete (real_vector.span A)"
proof (cases "A \<noteq> {} \<and> A \<noteq> {0}")
  case True
  obtain B where
    BT: "real_vector.span B = real_vector.span A"
    and "independent B"  
    and "finite B"
    using real_vector.span_finite_basis_exists[where A=A, OF assms]
    by metis

  have "B\<noteq>{}"
    apply (rule ccontr, simp)
    using BT True
    by (metis real_vector.span_superset span_empty subset_singletonD)

  define repr  where "repr = real_vector.representation B"
  {
    assume "\<exists>(Rep :: 'basis\<Rightarrow>'a) Abs. type_definition Rep Abs B"
    then obtain rep :: "'basis \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'basis" where t: "type_definition rep abs B"
      by auto
    have *: "class.finite TYPE('basis)"
      apply intro_classes
      using \<open>finite B\<close> t
      by (metis (mono_tags, hide_lams) ex_new_if_finite finite_imageI image_eqI type_definition_def)
    note finite_span_complete_aux'(2)[OF this t \<open>finite B\<close> _ \<open>independent B\<close>]
  }
  note this[cancel_type_definition, OF \<open>B\<noteq>{}\<close>]
  then have "complete (real_vector.span B)"
    using \<open>B\<noteq>{}\<close> by auto 
  then show "complete (real_vector.span A)"
    unfolding BT by simp
next
  case False
  then show ?thesis
    using complete_singleton by auto
qed

hide_fact finite_span_complete_aux

lemma finite_span_closed: 
  fixes B :: "'a::real_normed_vector set"
  assumes "finite B"
  shows "closed (real_vector.span B)"
  by (simp add: assms complete_imp_closed finite_span_complete)

lemma complex_real_span:
  "complex_vector.span B = real_vector.span (B \<union> scaleC \<i> ` B)"
proof auto
  let ?cspan = complex_vector.span
  let ?rspan = real_vector.span
  fix \<psi>
  assume cspan: "\<psi> \<in> ?cspan B"
  obtain B' r where "finite B'" and "B' \<subseteq> B" and \<psi>_explicit: "\<psi> = (\<Sum>b\<in>B'. r b *\<^sub>C b)"
    apply atomize_elim 
    using complex_vector.span_explicit[of B] cspan
    by auto
  define R where "R = B \<union> scaleC \<i> ` B"
(*   then have "R' \<subseteq> R" 
    using \<open>B' \<subseteq> B\<close> by auto *)
  have "r b *\<^sub>C b = Re (r b) *\<^sub>R b + Im (r b) *\<^sub>R \<i> *\<^sub>C b" for b
    by (metis (no_types, lifting) complex_eq ordered_field_class.sign_simps(28) scaleC_add_left scaleC_scaleC scaleR_scaleC)
  then have "\<psi> = (\<Sum>(b,i)\<in>(B'\<times>UNIV). if i then Im (r b) *\<^sub>R (\<i> *\<^sub>C b) else Re (r b) *\<^sub>R b)"
    apply (subst sum.cartesian_product[symmetric])
    by (simp add: UNIV_bool \<psi>_explicit)
  also have "\<dots> \<in> ?rspan R"
    unfolding R_def
    apply (rule real_vector.span_sum)
    using \<open>B' \<subseteq> B\<close> by (auto simp add: span_base span_scale subset_iff) 
  finally show "\<psi> \<in> ?rspan R" by -
next
  let ?cspan = complex_vector.span
  let ?rspan = real_vector.span
  define R where "R = B \<union> scaleC \<i> ` B"
  fix \<psi>
  assume rspan: "\<psi> \<in> ?rspan R"
  then show "\<psi> \<in> ?cspan B"
    apply induction
    apply (rule real_vector.subspaceI, auto simp add: complex_vector.span_zero complex_vector.span_add_eq2 complex_vector.span_scale scaleR_scaleC)
    using R_def complex_vector.span_base complex_vector.span_scale by fastforce 
qed

lemma finite_complex_span_complete: 
  fixes B :: "'a::complex_normed_vector set"
  assumes "finite B"
  shows "complete (complex_vector.span B)"
  apply (subst complex_real_span)
  apply (rule finite_span_complete)
  using assms by auto

lemma finite_complex_span_closed: 
  fixes B :: "'a::complex_normed_vector set"
  assumes "finite B"
  shows "closed (complex_vector.span B)"
  by (simp add: assms complete_imp_closed finite_complex_span_complete)

end

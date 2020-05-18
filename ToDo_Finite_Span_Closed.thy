theory ToDo_Finite_Span_Closed
  imports ToDo "HOL-Types_To_Sets.Types_To_Sets"
begin
unbundle no_notation_blinfun_apply
unbundle bounded_notation

lemma finite_span_complete_aux:
  fixes b :: "'b::real_normed_vector" and B :: "'b set"
    and  rep :: "'basis::finite \<Rightarrow> 'b" and abs :: "'b \<Rightarrow> 'basis"
  assumes t: "type_definition rep abs B"
  assumes "finite B" and "b\<in>B" and "independent B"
  shows "\<exists>D>0. \<forall>\<psi>. norm (real_vector.representation B \<psi> b) \<le> norm \<psi> * D"
    and "complete (real_vector.span B)"

  text \<open>This auxiliary lemma shows more or less the same as \<open>finite_span_representation_bounded\<close>
     \<open>finite_span_complete\<close> below (see there for an intuition about the mathematical 
     content of the lemmas. However, there is one difference: We additionally assume here
     that there is a bijection rep/abs between a finite type \<^typ>\<open>'basis\<close> and the set $B$.
     This is needed to be able to use results about euclidean spaces that are formulated w.r.t.
     the type class \<^class>\<open>finite\<close>

     Since we anyway assume that $B$ is finite, this added assumption does not make the lemma
     weaker. However, we cannot derive the existence of \<^typ>\<open>'basis\<close> inside the proof
     (HOL does not support such reasoning). Therefore we have the type \<^typ>\<open>'basis\<close> as
     an explicit assumption and remove it using @{attribute internalize_sort} after the proof.\<close>

proof -
  define repr  where "repr = real_vector.representation B"
  define repr' where "repr' \<psi> = Abs_euclidean_space (repr \<psi> o rep)" for \<psi>
  define comb  where "comb l = (\<Sum>b\<in>B. l b *\<^sub>R b)" for l
  define comb' where "comb' l = comb (Rep_euclidean_space l o abs)" for l

  have comb_cong: "comb x = comb y" if "\<And>z. z\<in>B \<Longrightarrow> x z = y z" for x y
    unfolding comb_def using that by auto
  have comb_repr[simp]: "comb (repr \<psi>) = \<psi>" if "\<psi> \<in> real_vector.span B" for \<psi>
    unfolding comb_def repr_def 
    apply (rule real_vector.sum_representation_eq)
    using assms that by auto
  have repr_comb[simp]: "repr (comb x) = (\<lambda>b. if b\<in>B then x b else 0)" for x
    unfolding repr_def comb_def
    apply (rule real_vector.representation_eqI)
    using \<open>independent B\<close> \<open>finite B\<close> apply (auto simp add: real_vector.span_base real_vector.span_scale real_vector.span_sum)
      (* Sledgehammer *)
     apply meson
    by (smt DiffD1 DiffD2 mem_Collect_eq real_vector.scale_eq_0_iff subset_eq sum.mono_neutral_cong_left)
  have repr_bad[simp]: "repr \<psi> = (\<lambda>_. 0)" if "\<psi> \<notin> real_vector.span B" for \<psi>
    unfolding repr_def using that
    by (simp add: real_vector.representation_def)
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
    by (simp add: real_vector.scale_sum_right)

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
      by (metis comb'_def comb_cong comb_repr local.repr_def repr_bad repr_comb real_vector.representation_zero real_vector.span_zero)
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

(* TODO: move to General_Results_Missing or similar *)
lemma complete_singleton: 
  shows "complete {s::'a::uniform_space}"
  unfolding complete_uniform
  apply auto
  by (meson dual_order.trans empty_subsetI insert_subset le_nhds le_principal principal_le_iff)

(* We do not need this theorem for our development but we get it almost for
   free as a side effect of the proof of finite_span_complete. *)
lemma finite_span_representation_bounded: 
  fixes B :: "'a::real_normed_vector set"
  assumes "finite B" "independent B"
  shows "\<exists>D>0. \<forall>\<psi> b. abs (real_vector.representation B \<psi> b) \<le> norm \<psi> * D"

  text \<open>
  Assume $B$ is a finite linear independent set of vectors (in a real normed vector space).
  Let $\<alpha>^\<psi>_b$ be the coefficients of $\<psi>$ expressed as a linear combination over $B$.
  Then $\<alpha>$ is is uniformly bounded (i.e., $\lvert\alpha^\<psi>_b \leq D \lVert\psi\rVert\psi for some $D$ independent of $\<psi>,b$).

  (This also holds when $b$ is not in the span of $B$ because of the way \<open>real_vector.representation\<close>
  is defined in this corner case.) \<close>

proof (cases "B\<noteq>{}")
  case True

(* The following generalizes finite_span_complete_aux to hold without the assumption
     that 'basis has type class finite *)
  define repr  where "repr = real_vector.representation B"
  {
    (* Step 1: Create a fake type definition by introducing a new type variable 'basis
               and then assuming the existence of the morphisms Rep/Abs to B
               This is then roughly equivalent to "typedef 'basis = B" *)
    (* The type variable 'basisT must not be the same as the one used in finite_span_complete_aux
       (I.e., we cannot call it 'basis) *)
    assume "\<exists>(Rep :: 'basisT\<Rightarrow>'a) Abs. type_definition Rep Abs B"
    then obtain rep :: "'basisT \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'basisT" where t: "type_definition rep abs B"
      by auto
        (* Step 2: We show that our fake typedef 'basisT could be instantiated as type class finite *)
    have basisT_finite: "class.finite TYPE('basisT)"
      apply intro_classes
      using \<open>finite B\<close> t
      by (metis (mono_tags, hide_lams) ex_new_if_finite finite_imageI image_eqI type_definition_def)
        (* Step 3: We take the finite_span_complete_aux and remove the requirement that 'basis::finite
               (instead, a precondition "class.finite TYPE('basisT)" is introduced) *)
    note finite_span_complete_aux(1)[internalize_sort "'basis::finite"]
      (* Step 4: We instantiate the premises *)
    note this[OF basisT_finite t]
  }
    (* Now we have the desired fact, except that it still assumes that B is isomorphic to some type 'basis
     together with the assumption that there are morphisms between 'basis and B. 'basis and that premise
     are removed using cancel_type_definition
  *)
  note this[cancel_type_definition, OF True \<open>finite B\<close> _ \<open>independent B\<close>]

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
    unfolding repr_def using real_vector.representation_ne_zero True
    by (metis calculation empty_subsetI less_le_trans local.repr_def norm_ge_zero norm_zero not_less subsetI subset_antisym)
  ultimately show "\<exists>D>0. \<forall>\<psi> b. abs (repr \<psi> b) \<le> norm \<psi> * D"
    using \<open>Dall > 0\<close> real_norm_def by metis
next
  case False
  then show ?thesis
    unfolding repr_def using real_vector.representation_ne_zero[of B]
    using nice_ordered_field_class.linordered_field_no_ub by fastforce
qed

lemma
  fixes A :: "'a::real_normed_vector set"
  assumes "finite A"
  shows finite_span_complete: "complete (real_vector.span A)"

  text \<open>The span of a finite set is complete.\<close>

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
    by (metis real_vector.span_superset real_vector.span_empty subset_singletonD)

(* The following generalizes finite_span_complete_aux to hold without the assumption
     that 'basis has type class finite *)
  {
    (* The type variable 'basisT must not be the same as the one used in finite_span_complete_aux,
       otherwise "internalize_sort" below fails *)
    assume "\<exists>(Rep :: 'basisT\<Rightarrow>'a) Abs. type_definition Rep Abs B"
    then obtain rep :: "'basisT \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'basisT" where t: "type_definition rep abs B"
      by auto
    have basisT_finite: "class.finite TYPE('basisT)"
      apply intro_classes
      using \<open>finite B\<close> t
      by (metis (mono_tags, hide_lams) ex_new_if_finite finite_imageI image_eqI type_definition_def)
    note finite_span_complete_aux(2)[internalize_sort "'basis::finite"]
    note this[OF basisT_finite t]
  }
  note this[cancel_type_definition, OF \<open>B\<noteq>{}\<close> \<open>finite B\<close> _ \<open>independent B\<close>]
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
  have "r b *\<^sub>C b = Re (r b) *\<^sub>R b + Im (r b) *\<^sub>R \<i> *\<^sub>C b" for b
    by (metis (no_types, lifting) complex_eq ordered_field_class.sign_simps(28) scaleC_add_left scaleC_scaleC scaleR_scaleC)
  then have "\<psi> = (\<Sum>(b,i)\<in>(B'\<times>UNIV). if i then Im (r b) *\<^sub>R (\<i> *\<^sub>C b) else Re (r b) *\<^sub>R b)"
    apply (subst sum.cartesian_product[symmetric])
    by (simp add: UNIV_bool \<psi>_explicit)
  also have "\<dots> \<in> ?rspan R"
    unfolding R_def
    apply (rule real_vector.span_sum)
    using \<open>B' \<subseteq> B\<close> by (auto simp add: real_vector.span_base real_vector.span_scale subset_iff) 
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

lemma bounded_operator_basis_zero_uniq:
  fixes basis::\<open>'a::chilbert_space set\<close> and \<phi>::\<open>'a \<Rightarrow> 'b::chilbert_space\<close>
  assumes a1: "complex_vector.span basis = UNIV"
    and a2: "complex_vector.independent basis"
    and a3: "finite basis" and a4: "\<And>s. s\<in>basis \<Longrightarrow> F *\<^sub>v s = 0"
  shows \<open>F = 0\<close>
proof-
  have "F *\<^sub>v w = 0" for w
  proof-
    have "w \<in> complex_vector.span basis"
      using a1 by blast
    hence "\<exists>t r. finite t \<and> t \<subseteq> basis \<and>  w = (\<Sum>a\<in>t. r a *\<^sub>C a)"
      using complex_vector.span_explicit by (smt mem_Collect_eq)
    then obtain t r where b1: "finite t" and b2: "t \<subseteq> basis" and b3: "w = (\<Sum>a\<in>t. r a *\<^sub>C a)"
      by blast
    have  "F *\<^sub>v w = (\<Sum>a\<in>t. r a *\<^sub>C (F *\<^sub>v a))"
      using b3
      by (smt \<open>\<And>thesis. (\<And>t r. \<lbrakk>finite t; t \<subseteq> basis; w = (\<Sum>a\<in>t. r a *\<^sub>C a)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> a4 b2 clinear_finite_sum complex_vector.scale_eq_0_iff in_mono sum.neutral)
    thus ?thesis using a4 b2
      by (simp add: subset_eq) 
  qed
  thus ?thesis by (simp add: bounded_ext) 
qed

lemma bounded_operator_basis_existence_uniq:
  fixes basis::\<open>'a::chilbert_space set\<close> and \<phi>::\<open>'a \<Rightarrow> 'b::chilbert_space\<close>
  assumes \<open>complex_vector.span basis = UNIV\<close> 
    and \<open>complex_vector.independent basis\<close>
    and \<open>finite basis\<close>
  shows \<open>\<exists>!F. \<forall>s\<in>basis. F *\<^sub>v s = \<phi> s\<close>
proof-
  have \<open>\<exists>F. \<forall>s\<in>basis. F *\<^sub>v s = \<phi> s\<close>
  proof-
    have f1: "Complex_Vector_Spaces.representation basis w =
        (if complex_independent basis \<and> w \<in> Complex_Vector_Spaces.span basis
         then SOME f.
         (\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> basis) \<and>
         finite {v. f v \<noteq> 0} \<and> (\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = w
       else (\<lambda>b. 0))" for w
      by (simp add: complex_vector.representation_def)
    define f::"'a \<Rightarrow> 'a \<Rightarrow> complex" where
      "f w v = Complex_Vector_Spaces.representation basis w v" for w v
    have f2: "\<forall>v. f w v \<noteq> 0 \<longrightarrow> v \<in> basis" for w
      using complex_vector.representation_ne_zero f_def by auto
    have f3: "finite {v. f w v \<noteq> 0}" for w
      by (metis \<open>f \<equiv> Complex_Vector_Spaces.representation basis\<close> complex_vector.finite_representation)
    have f4: "(\<Sum>v | f w v \<noteq> 0. f w v *\<^sub>C v) = w" for w
      using \<open>complex_vector.independent basis\<close> \<open>complex_vector.span basis = UNIV\<close>
        f1[where w = w] unfolding f_def
      using Complex_Vector_Spaces.dependent_raw_def complex_vector.sum_nonzero_representation_eq 
        iso_tuple_UNIV_I
    proof -
      have "complex_independent basis"
        by (metis Complex_Vector_Spaces.dependent_raw_def \<open>complex_vector.independent basis\<close>)
      thus "(\<Sum>a | Complex_Vector_Spaces.representation basis w a \<noteq> 0. 
            Complex_Vector_Spaces.representation basis w a *\<^sub>C a) = w"
        using \<open>Complex_Vector_Spaces.span basis = UNIV\<close> complex_vector.sum_nonzero_representation_eq iso_tuple_UNIV_I
        by metis (* > 1s *)
    qed
    have f5: "w \<in> basis \<Longrightarrow> f w w = 1" for w
      using complex_vector.representation_basis[where basis = basis and b = w]
      by (smt Complex_Vector_Spaces.dependent_raw_def \<open>f \<equiv> Complex_Vector_Spaces.representation basis\<close> assms(2))
    have f6: "w\<in>basis \<Longrightarrow> v \<noteq> w \<Longrightarrow> f w v = 0" for v w
      using complex_vector.representation_basis f1 f_def by fastforce
    define F where "F w = (\<Sum>v | f w v \<noteq> 0. f w v *\<^sub>C \<phi> v)" for w

    have f_def': "w = (\<Sum>v\<in>basis. f w v *\<^sub>C v)" for w
    proof- 
      have "basis = {v |v. f w v \<noteq> 0 \<and> v \<in> basis} \<union> {v |v. f w v = 0 \<and> v \<in> basis}"
        by blast
      moreover have "{v |v. f w v \<noteq> 0 \<and> v \<in> basis} \<inter> {v |v. f w v = 0 \<and> v \<in> basis} = {}"
        by blast
      ultimately have "(\<Sum>v\<in>basis. f w v *\<^sub>C v) =
                     (\<Sum>v\<in>{v |v. f w v \<noteq> 0 \<and> v \<in> basis}. f w v *\<^sub>C v)
                  +  (\<Sum>v\<in>{v |v. f w v = 0 \<and> v \<in> basis}. f w v *\<^sub>C v)"
        by (metis (no_types, lifting) assms(3) finite_Un sum.union_disjoint)
      moreover have "(\<Sum>v\<in>{v |v. f w v = 0 \<and> v \<in> basis}. f w v *\<^sub>C v) = 0"
        by simp        
      ultimately 
      have "(\<Sum>v\<in>basis. f w v *\<^sub>C v) = (\<Sum>v\<in>{v |v. f w v \<noteq> 0 \<and> v \<in> basis}. f w v *\<^sub>C v)"
        by simp
      also have "\<dots> = (\<Sum>v\<in>{v |v. f w v \<noteq> 0}. f w v *\<^sub>C v)"
        using f2 by meson  
      also have "\<dots> = w"
        using f4 by auto
      finally show ?thesis by simp
    qed
    have F_def': "F w = (\<Sum>v\<in>basis. f w v *\<^sub>C \<phi> v)" for w
    proof- 
      have "basis = {v |v. f w v \<noteq> 0 \<and> v \<in> basis} \<union> {v |v. f w v = 0 \<and> v \<in> basis}"
        by blast
      moreover have "{v |v. f w v \<noteq> 0 \<and> v \<in> basis} \<inter> {v |v. f w v = 0 \<and> v \<in> basis} = {}"
        by blast
      ultimately have "(\<Sum>v\<in>basis. f w v *\<^sub>C \<phi> v) =
                     (\<Sum>v\<in>{v |v. f w v \<noteq> 0 \<and> v \<in> basis}. f w v *\<^sub>C \<phi> v)
                  +  (\<Sum>v\<in>{v |v. f w v = 0 \<and> v \<in> basis}. f w v *\<^sub>C \<phi> v)"
        by (metis (no_types, lifting) assms(3) finite_Un sum.union_disjoint)
      moreover have "(\<Sum>v\<in>{v |v. f w v = 0 \<and> v \<in> basis}. f w v *\<^sub>C \<phi> v) = 0"
        by simp        
      ultimately 
      have "(\<Sum>v\<in>basis. f w v *\<^sub>C \<phi> v) = (\<Sum>v\<in>{v |v. f w v \<noteq> 0 \<and> v \<in> basis}. f w v *\<^sub>C \<phi> v)"
        by simp
      also have "\<dots> = (\<Sum>v\<in>{v |v. f w v \<noteq> 0}. f w v *\<^sub>C \<phi> v)"
        using f2 by meson  
      also have "\<dots> = F w"
        unfolding F_def by auto
      finally show ?thesis by simp
    qed
    have f_add: "v\<in>basis \<Longrightarrow> f (w1+w2) v = f w1 v + f w2 v" for w1 w2 v
    proof-
      have "w1 = (\<Sum>v | v\<in>basis. f w1 v *\<^sub>C v)"
        using f_def' by auto
      moreover have "w2 = (\<Sum>v | v\<in>basis. f w2 v *\<^sub>C v)"
        using f_def' by auto
      ultimately have "w1 + w2 = (\<Sum>v | v\<in>basis. f w1 v *\<^sub>C v) +  (\<Sum>v | v\<in>basis. f w2 v *\<^sub>C v)"
        by simp
      also have "\<dots> = (\<Sum>v | v\<in>basis. (f w1 v *\<^sub>C v + f w2 v *\<^sub>C v))"
        by (metis (no_types, lifting) sum.cong sum.distrib)
      also have "\<dots> = (\<Sum>v | v\<in>basis. ((f w1 v + f w2 v) *\<^sub>C v))"
        by (metis scaleC_add_left)
      finally have "w1 + w2 = (\<Sum>v | v\<in>basis. ((f w1 v + f w2 v) *\<^sub>C v))"
        by blast
      moreover have "w1 + w2 = (\<Sum>v | v\<in>basis. (f (w1 + w2) v *\<^sub>C v))"
        using f_def' by auto
      ultimately have "(\<Sum>v | v\<in>basis. (f (w1 + w2) v *\<^sub>C v)) = (\<Sum>v | v\<in>basis. ((f w1 v + f w2 v) *\<^sub>C v))"
        by simp
      hence "0 = (\<Sum>v | v\<in>basis. (f (w1 + w2) v *\<^sub>C v)) -  (\<Sum>v | v\<in>basis. ((f w1 v + f w2 v) *\<^sub>C v))"
        by simp
      also have "\<dots> = (\<Sum>v | v\<in>basis. (f (w1 + w2) v *\<^sub>C v)- (f w1 v + f w2 v) *\<^sub>C v)"
        by (simp add: sum_subtractf)
      also have "\<dots> = (\<Sum>v | v\<in>basis. (f (w1 + w2) v - f w1 v - f w2 v) *\<^sub>C v)"
        by (metis (no_types, lifting) diff_diff_add scaleC_left.diff)
      finally have "0 = (\<Sum>v | v\<in>basis. (f (w1 + w2) v - f w1 v - f w2 v) *\<^sub>C v)"
        by simp
      hence "(\<Sum>v | v\<in>basis. (f (w1 + w2) v - f w1 v - f w2 v) *\<^sub>C v) = 0"
        by simp
      hence "v\<in>basis \<Longrightarrow> f (w1 + w2) v - f w1 v - f w2 v = 0" for v
      proof -
        assume "v \<in> basis"
        then have f1: "\<And>f. (\<Sum>a\<in>basis. f a *\<^sub>C a) \<noteq> 0 \<or> Complex_Vector_Spaces.dependent basis \<or> f v = 0"
          using assms(3) complex_vector.dependent_finite by auto
        have "complex_independent basis"
          by (simp add: Complex_Vector_Spaces.dependent_raw_def \<open>complex_vector.independent basis\<close>)
        thus ?thesis
          using f1 \<open>(\<Sum>v | v \<in> basis. (f (w1 + w2) v - f w1 v - f w2 v) *\<^sub>C v) = 0\<close> by fastforce
      qed
      thus ?thesis
        by (metis add.commute eq_diff_eq eq_iff_diff_eq_0 f2) 
    qed
    have f_scaleC: "v\<in>basis \<Longrightarrow> f (r *\<^sub>C w) v = r * f w v" for w v r
    proof-
      have "w = (\<Sum>v | v\<in>basis. f w v *\<^sub>C v)"
        using f_def' by auto
      hence "r *\<^sub>C w = r *\<^sub>C (\<Sum>v | v\<in>basis. f w v *\<^sub>C v)"
        by simp
      also have "\<dots> = (\<Sum>v | v\<in>basis. r *\<^sub>C (f w v *\<^sub>C v))"
        using scaleC_right.sum by blast
      also have "\<dots> = (\<Sum>v | v\<in>basis. (r * f w v) *\<^sub>C v)"
        by simp
      finally have "r *\<^sub>C w = (\<Sum>v | v\<in>basis. (r * f w v) *\<^sub>C v)"
        by blast
      moreover have "r *\<^sub>C w = (\<Sum>v | v\<in>basis. f (r *\<^sub>C w) v *\<^sub>C v)"
        by (simp add: f_def')
      ultimately have "(\<Sum>v | v\<in>basis. f (r *\<^sub>C w) v *\<^sub>C v) =  (\<Sum>v | v\<in>basis. (r * f w v) *\<^sub>C v)"
        by simp
      hence "0 = (\<Sum>v | v\<in>basis. f (r *\<^sub>C w) v *\<^sub>C v) - (\<Sum>v | v\<in>basis. (r * f w v) *\<^sub>C v)"
        by simp
      also have "\<dots> = (\<Sum>v | v\<in>basis. f (r *\<^sub>C w) v *\<^sub>C v - (r * f w v) *\<^sub>C v)"
        by (simp add: sum_subtractf)
      also have "\<dots> = (\<Sum>v | v\<in>basis. (f (r *\<^sub>C w) v - r * f w v) *\<^sub>C v)"
        by (metis (no_types, lifting) scaleC_left.diff)
      finally have "0 = (\<Sum>v | v\<in>basis. (f (r *\<^sub>C w) v - r * f w v) *\<^sub>C v)"
        by blast
      hence \<open>(\<Sum>v | v\<in>basis. (f (r *\<^sub>C w) v - r * f w v) *\<^sub>C v) = 0\<close>
        by simp
      hence "v\<in>basis \<Longrightarrow> f (r *\<^sub>C w) v - r * f w v = 0" for v
      proof -
        assume "v \<in> basis"
        then have f1: "\<And>f. (\<Sum>a\<in>basis. f a *\<^sub>C a) \<noteq> 0 \<or> Complex_Vector_Spaces.dependent basis \<or> f v = 0"
          using assms(3) complex_vector.dependent_finite by auto
        have "complex_independent basis"
          by (simp add: Complex_Vector_Spaces.dependent_raw_def \<open>complex_vector.independent basis\<close>)
        thus ?thesis
          using f1 \<open>(\<Sum>v | v\<in>basis. (f (r *\<^sub>C w) v - r * f w v) *\<^sub>C v) = 0\<close> by fastforce
      qed
      thus ?thesis
        by (metis diff_eq_diff_eq diff_numeral_special(9) f2 mult_cancel_right1) 
    qed
    have f_bounded: "v\<in>basis \<Longrightarrow> \<exists>K. \<forall>w. norm (f w v) \<le> norm w * K" for v
      sorry
    have "clinear F" 
      unfolding clinear_def proof
      show "F (b1 + b2) = F b1 + F b2"
        for b1 :: 'a
          and b2 :: 'a
        using f_add 
        unfolding F_def'
        by (smt scaleC_add_left sum.cong sum.distrib)         

      show "F (r *\<^sub>C b) = r *\<^sub>C F b"
        for r :: complex
          and b :: 'a
      proof-
        have "F (r *\<^sub>C b) = (\<Sum>v\<in>basis. f (r *\<^sub>C b) v *\<^sub>C \<phi> v)"
          unfolding F_def' by blast
        also have "\<dots> = (\<Sum>v\<in>basis. (r * f b v) *\<^sub>C \<phi> v)"
          using f_scaleC by simp
        also have "\<dots> = (\<Sum>v\<in>basis. r *\<^sub>C (f b v *\<^sub>C \<phi> v))"
          by simp
        also have "\<dots> = r *\<^sub>C (\<Sum>v\<in>basis. f b v *\<^sub>C \<phi> v)"
          by (metis (full_types) scaleC_right.sum)          
        finally show ?thesis using F_def' by simp
      qed  
    qed
    moreover have "\<exists>K. \<forall>x. norm (F x) \<le> norm x * K"
    proof-
      from f_bounded
      obtain M where M_def: "\<And> w v. v \<in> basis \<Longrightarrow> cmod (f w v) \<le> norm w * M v"
        by metis
      define K where "K = (sum (\<lambda>v. M v * norm (\<phi> v)) basis)"
      have "norm (F x) \<le> norm x * K" for x
      proof-
        have "norm (F x) = norm (\<Sum>v\<in>basis. f x v *\<^sub>C \<phi> v)"
          unfolding F_def' by blast
        also have "\<dots> \<le> (\<Sum>v\<in>basis. norm (f x v *\<^sub>C \<phi> v))"
          by (simp add: sum_norm_le)
        also have "\<dots> = (\<Sum>v\<in>basis. norm (f x v) * norm (\<phi> v))"
          by auto
        also have "\<dots> \<le> (\<Sum>v\<in>basis. (norm x) * M v * norm (\<phi> v))"
          using M_def
          by (simp add: mult_right_mono sum_mono) 
        also have "\<dots> \<le> (norm x) * (\<Sum>v\<in>basis. M v * norm (\<phi> v))"
          by (smt sum.cong vector_space_over_itself.scale_scale vector_space_over_itself.scale_sum_right)
        also have "\<dots> \<le> (norm x) * K"
          unfolding K_def by simp
        finally show ?thesis by simp
      qed
      thus ?thesis by blast
    qed
    ultimately have "bounded_clinear F"
      unfolding bounded_clinear_def by blast
    moreover have "w\<in>basis \<Longrightarrow> F w = \<phi> w" for w
    proof-
      assume b1: "w\<in>basis"
      have "F w = (\<Sum>v | f w v \<noteq> 0 \<and> v = w. f w v *\<^sub>C \<phi> v)
                 +(\<Sum>v | f w v \<noteq> 0 \<and> v \<noteq> w. f w v *\<^sub>C \<phi> v)"
        by (smt Collect_cong F_def add.commute add_cancel_right_left b1 f6 mem_Collect_eq sum.cong 
            sum.neutral_const)
      moreover have "(\<Sum>v | f w v \<noteq> 0 \<and> v = w. f w v *\<^sub>C \<phi> v) = \<phi> w"
      proof-
        have "f w w \<noteq> 0"
          by (simp add: b1 f5)
        hence "(\<Sum>v | f w v \<noteq> 0 \<and> v = w. f w v *\<^sub>C \<phi> v) = (\<Sum>v | v = w. f w v *\<^sub>C \<phi> v)"
          by metis
        also have "\<dots> = f w w *\<^sub>C \<phi> w"
          using Collect_mem_eq add_cancel_right_left complex_vector.scale_cancel_right 
            complex_vector.scale_zero_right by auto          
        finally have "(\<Sum>v | f w v \<noteq> 0 \<and> v = w. f w v *\<^sub>C \<phi> v) = f w w *\<^sub>C \<phi> w"
          by blast
        thus ?thesis
          by (simp add: b1 f5) 
      qed
      moreover have "(\<Sum>v | f w v \<noteq> 0 \<and> v \<noteq> w. f w v *\<^sub>C \<phi> v) = 0"
        by (simp add: b1 f6)        
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis apply transfer
      by blast
  qed
  moreover have \<open>(\<And>s. s\<in>basis \<Longrightarrow> F *\<^sub>v s = \<phi> s) \<Longrightarrow> (\<And>s. s\<in>basis \<Longrightarrow> G *\<^sub>v s = \<phi> s) \<Longrightarrow> F = G\<close> for F G
  proof-
    assume a1: "\<And>s. s\<in>basis \<Longrightarrow> F *\<^sub>v s = \<phi> s" and a2: "\<And>s. s\<in>basis \<Longrightarrow> G *\<^sub>v s = \<phi> s"
    hence "s\<in>basis \<Longrightarrow> (F-G) *\<^sub>v s = 0" for s
      by (simp add: minus_bounded.rep_eq)
    hence "F - G = 0"
      using bounded_operator_basis_zero_uniq[where F = "F - G" and basis = basis]
        assms(1) assms(2) assms(3) by auto
    thus ?thesis by simp
  qed
  ultimately show ?thesis
    by auto 
qed

unbundle no_bounded_notation

end

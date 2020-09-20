section \<open>\<open>Bounded_Operators_Code\<close> -- Support for code generation\<close>

theory Bounded_Operators_Code
  imports
    Bounded_Operators_Matrices Containers.Set_Impl 
begin

no_notation "Lattice.meet" (infixl "\<sqinter>\<index>" 70)
no_notation "Lattice.join" (infixl "\<squnion>\<index>" 65)
hide_const (open) Coset.kernel
hide_const (open) Order.bottom Order.top

unbundle jnf_notation
unbundle cblinfun_notation


subsubsection\<open>Gram Schmidt sub\<close>

definition "vec_is_zero n v = (\<forall>i<n. v $ i = 0)"

lemma vec_is_zero: "dim_vec v = n \<Longrightarrow> vec_is_zero n v \<longleftrightarrow> v = 0\<^sub>v n"
  unfolding vec_is_zero_def apply auto
  by (metis index_zero_vec(1))

fun gram_schmidt_sub0
  where "gram_schmidt_sub0 n us [] = us"
  | "gram_schmidt_sub0 n us (w # ws) =
     (let w' = adjuster n w us + w in
      if vec_is_zero n w' then gram_schmidt_sub0 n us ws
                          else gram_schmidt_sub0 n (w' # us) ws)"

lemma (in cof_vec_space) adjuster_already_in_span:
  assumes "w \<in> carrier_vec n"
  assumes us_carrier: "set us \<subseteq> carrier_vec n"
  assumes "corthogonal us"
  assumes "w \<in> span (set us)"
  shows "adjuster n w us + w = 0\<^sub>v n"
proof -
  define v U where "v = adjuster n w us + w" and "U = set us"
  have span: "v \<in> span U"
    unfolding v_def U_def
    apply (rule adjust_preserves_span[THEN iffD1])
    using assms corthogonal_distinct by simp_all
  have v_carrier: "v \<in> carrier_vec n"
    by (simp add: v_def assms corthogonal_distinct)
  have "v \<bullet>c us!i = 0" if "i < length us" for i
    unfolding v_def
    apply (rule adjust_zero)
    using that assms by simp_all
  hence "v \<bullet>c u = 0" if "u \<in> U" for u
    by (metis assms(3) U_def corthogonal_distinct distinct_Ex1 that)
  hence ortho: "u \<bullet>c v = 0" if "u \<in> U" for u
    apply (subst conjugate_zero_iff[symmetric])
    apply (subst conjugate_vec_sprod_comm)
    using that us_carrier v_carrier apply (auto simp: U_def)[2]
    apply (subst conjugate_conjugate_sprod)
    using that us_carrier v_carrier by (auto simp: U_def)
  from span obtain a where v: "lincomb a U = v"
    apply atomize_elim apply (rule finite_in_span[simplified])
    unfolding U_def using us_carrier by auto
  have "v \<bullet>c v = (\<Sum>u\<in>U. (a u \<cdot>\<^sub>v u) \<bullet>c v)"
    apply (subst v[symmetric])
    unfolding lincomb_def
    apply (subst finsum_scalar_prod_sum)
    using U_def span us_carrier by auto
  also have "\<dots> = (\<Sum>u\<in>U. a u * (u \<bullet>c v))"
    using U_def assms(1) in_mono us_carrier v_def by fastforce
  also have "\<dots> = (\<Sum>u\<in>U. a u * conjugate 0)"
    apply (rule sum.cong, simp)
    using span span_closed U_def us_carrier ortho by auto
  also have "\<dots> = 0"
    by auto
  finally have "v \<bullet>c v = 0"
    by -
  thus "v = 0\<^sub>v n"
    using U_def conjugate_square_eq_0_vec span span_closed us_carrier by blast
qed


(* Following closely Gram_Schmidt.gram_schmidt_sub_result in Jordan_Normal_Form *)
lemma (in cof_vec_space) gram_schmidt_sub0_result:
  assumes "gram_schmidt_sub0 n us ws = us'"
    and "set ws \<subseteq> carrier_vec n"
    and "set us \<subseteq> carrier_vec n"
    and "distinct us"
    and "~ lin_dep (set us)"
    and "corthogonal us"
  shows "set us' \<subseteq> carrier_vec n \<and>
         distinct us' \<and>
         corthogonal us' \<and>
         span (set (us @ ws)) = span (set us')"  
  using assms
proof (induct ws arbitrary: us us')
  case (Cons w ws)
  show ?case
  proof (cases "w \<in> span (set us)")
    case False
    let ?v = "adjuster n w us"
    have wW[simp]: "set (w#ws) \<subseteq> carrier_vec n" using Cons by simp
    hence W[simp]: "set ws \<subseteq> carrier_vec n"
      and w[simp]: "w : carrier_vec n" by auto
    have U[simp]: "set us \<subseteq> carrier_vec n" using Cons by simp
    have UW: "set (us@ws) \<subseteq> carrier_vec n" by simp
    have wU: "set (w#us) \<subseteq> carrier_vec n" by simp
        (* have dist: "distinct (us @ w # ws)" using Cons by simp *)
    have dist_U: "distinct us" using Cons by simp
        (* and dist_W: "distinct ws" *)
        (* and dist_UW: "distinct (us @ ws)" *)
    have w_U: "w \<notin> set us" using False using span_mem by auto
        (* and w_W: "w \<notin> set ws" *)
        (* and w_UW: "w \<notin> set (us @ ws)" *)
        (* have ind: "~ lin_dep (set (us @ w # ws))" using Cons by simp *)
    have ind_U: "~ lin_dep (set us)"
      using Cons by simp
        (* and ind_W: "~ lin_dep (set ws)" *)
    have ind_wU: "~ lin_dep (insert w (set us))"
      apply (subst lin_dep_iff_in_span[simplified, symmetric])
      using w_U ind_U False by auto
    thm lin_dep_iff_in_span[simplified, symmetric]
    have corth: "corthogonal us" using Cons by simp
    have "?v + w \<noteq> 0\<^sub>v n"
      by (simp add: False adjust_nonzero dist_U)
    hence "\<not> vec_is_zero n (?v + w)"
      by (simp add: vec_is_zero)
    hence U'def: "gram_schmidt_sub0 n ((?v + w)#us) ws = us'" 
      using Cons by simp
    have v: "?v : carrier_vec n" using dist_U by auto
    hence vw: "?v + w : carrier_vec n" by auto
    hence vwU: "set ((?v + w) # us) \<subseteq> carrier_vec n" by auto
    have vsU: "?v : span (set us)" 
      apply (rule adjuster_in_span[OF w])
      using Cons by simp_all
    hence vsUW: "?v : span (set (us @ ws))"
      using span_is_monotone[of "set us" "set (us@ws)"] by auto
    have wsU: "w \<notin> span (set us)"
      using lin_dep_iff_in_span[OF U ind_U w w_U] ind_wU by auto
    hence vwU: "?v + w \<notin> span (set us)" using adjust_not_in_span[OF w U dist_U] by auto

    have span: "?v + w \<notin> span (set us)" 
      apply (subst span_add[symmetric])
      by (simp_all add: False vsU)
    hence vwUS: "?v + w \<notin> set us" using span_mem by auto
        (*     hence ind2: "~ lin_dep (set (((?v + w) # us) @ ws))"
      using lin_dep_iff_in_span[OF UW ind_UW vw] span by auto *)

    have vwU: "set ((?v + w) # us) \<subseteq> carrier_vec n" 
      using U w vw by simp
    have dist2: "distinct (((?v + w) # us))" 
      using vwUS
      by (simp add: dist_U)

    have orth2: "corthogonal ((adjuster n w us + w) # us)"
      using adjust_orthogonal[OF U corth w wsU].

    have ind_vwU: "~ lin_dep (set ((adjuster n w us + w) # us))"
      apply simp
      apply (subst lin_dep_iff_in_span[simplified, symmetric])
      by (simp_all add: ind_U vw vwUS span)

    have span_UwW_U': "span (set (us @ w # ws)) = span (set us')"
      using Cons(1)[OF U'def W vwU dist2 ind_vwU orth2] 
      using span_Un[OF vwU wU gram_schmidt_sub_span[OF w U dist_U] W W refl]
      by simp

    show ?thesis
      apply (intro conjI)
      using Cons(1)[OF U'def W vwU dist2 ind_vwU orth2] span_UwW_U' by simp_all
  next
    case True

    let ?v = "adjuster n w us"
    have "?v + w = 0\<^sub>v n"
      apply (rule adjuster_already_in_span)
      using True Cons by auto
    hence "vec_is_zero n (?v + w)"
      by (simp add: vec_is_zero)
    hence U'_def: "us' = gram_schmidt_sub0 n us ws"
      using Cons by simp
    have span: "span (set (us @ w # ws)) = span (set us')"
    proof -
      have wU_U: "span (set (w # us)) = span (set us)"
        apply (subst already_in_span[OF _ True, simplified])
        using Cons by auto
      have "span (set (us @ w # ws)) = span (set (w # us) \<union> set ws)"
        by simp
      also have "\<dots> = span (set us \<union> set ws)"
        apply (rule span_Un) using wU_U Cons by auto
      also have "\<dots> = local.span (set us')"
        using Cons U'_def by auto
      finally show ?thesis
        by -
    qed
    moreover have "set us' \<subseteq> carrier_vec n \<and> distinct us' \<and> corthogonal us'"
      unfolding U'_def using Cons by simp
    ultimately show ?thesis
      by auto
  qed
qed simp

definition "gram_schmidt0 n ws = gram_schmidt_sub0 n [] ws"

lemma (in cof_vec_space) gram_schmidt0_result:
  fixes ws
  defines "us' \<equiv> gram_schmidt0 n ws"
  assumes ws: "set ws \<subseteq> carrier_vec n"
  shows "set us' \<subseteq> carrier_vec n"        (is ?thesis1)
    and "distinct us'"                    (is ?thesis2)
    and "corthogonal us'"                 (is ?thesis3)
    and "span (set ws) = span (set us')"  (is ?thesis4)
proof -
  have carrier_empty: "set [] \<subseteq> carrier_vec n" by auto
  have distinct_empty: "distinct []" by simp
  have indep_empty: "lin_indpt (set [])"
    using basis_def subset_li_is_li unit_vecs_basis by auto
  have ortho_empty: "corthogonal []" by auto
  note gram_schmidt_sub0_result' = gram_schmidt_sub0_result
    [OF us'_def[symmetric, THEN meta_eq_to_obj_eq, unfolded gram_schmidt0_def] ws
      carrier_empty distinct_empty indep_empty ortho_empty]
  thus ?thesis1 ?thesis2 ?thesis3 ?thesis4
    by auto
qed

(* (* TODO: More to Preliminaries *)
lemma (in module) lin_indep_empty: "\<not> lin_dep {}"
  unfolding lin_dep_def by auto
 *)

locale complex_vec_space = cof_vec_space n "TYPE(complex)" for n :: nat

lemma (in complex_vec_space) module_span_complex_span:
  fixes X :: "'a::onb_enum set"
  assumes "canonical_basis_length TYPE('a) = n"
  shows "span (vec_of_onb_enum ` X) = vec_of_onb_enum ` complex_span X"
proof -
  have carrier: "vec_of_onb_enum ` X \<subseteq> carrier_vec n"
    by (metis assms canonical_basis_length_eq carrier_vecI dim_vec_of_onb_enum_list' image_subsetI)
  have lincomb_sum: "lincomb c A = vec_of_onb_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)" 
    if B_def: "B = onb_enum_of_vec ` A" and \<open>finite A\<close>
      and AX: "A \<subseteq> vec_of_onb_enum ` X" and c'_def: "\<And>b. c' b = c (vec_of_onb_enum b)"
    for c c' A and B::"'a set"
    unfolding B_def using \<open>finite A\<close> AX
  proof induction
    case empty
    then show ?case
      by (simp add: assms vec_of_onb_enum_zero)
  next
    case (insert x F)
    then have IH: "lincomb c F = vec_of_onb_enum (\<Sum>b\<in>onb_enum_of_vec ` F. c' b *\<^sub>C b)"
      (is "_ = ?sum")
      by simp
    have xx: "vec_of_onb_enum (onb_enum_of_vec x :: 'a) = x"
      apply (rule vec_of_onb_enum_inverse)
      using assms carrier carrier_vecD insert.prems by auto
    have "lincomb c (insert x F) = c x \<cdot>\<^sub>v x + lincomb c F"
      apply (rule lincomb_insert2)
      using insert.hyps insert.prems carrier by auto
    also have "c x \<cdot>\<^sub>v x = vec_of_onb_enum (c' (onb_enum_of_vec x) *\<^sub>C (onb_enum_of_vec x :: 'a))"
      by (simp add: xx vec_of_onb_enum_scaleC c'_def)
    also note IH
    also have
      "vec_of_onb_enum (c' (onb_enum_of_vec x) *\<^sub>C (onb_enum_of_vec x :: 'a)) + ?sum
          = vec_of_onb_enum (\<Sum>b\<in>onb_enum_of_vec ` insert x F. c' b *\<^sub>C b)"
      apply simp apply (rule sym)
      apply (subst sum.insert)
      using \<open>finite F\<close> \<open>x \<notin> F\<close> dim_vec_of_onb_enum_list' insert.prems 
        vec_of_onb_enum_add c'_def by auto
    finally show ?case
      by -
  qed

  show ?thesis
  proof auto
    fix x assume "x \<in> local.span (vec_of_onb_enum ` X)"
    then obtain c A where xA: "x = lincomb c A" and "finite A" and AX: "A \<subseteq> vec_of_onb_enum ` X"
      unfolding span_def by auto
    define B::"'a set" and c' where "B = onb_enum_of_vec ` A"
      and "c' b = c (vec_of_onb_enum b)" for b::'a
    note xA
    also have "lincomb c A = vec_of_onb_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)"
      using B_def \<open>finite A\<close> AX c'_def by (rule lincomb_sum)
    also have "\<dots> \<in> vec_of_onb_enum ` complex_span X"
      unfolding complex_vector.span_explicit
      apply (rule imageI) apply (rule CollectI)
      apply (rule exI) apply (rule exI)
      using \<open>finite A\<close> AX by (auto simp: B_def)
    finally show "x \<in> vec_of_onb_enum ` complex_span X"
      by -
  next
    fix x assume "x \<in> complex_span X" 
    then obtain c' B where x: "x = (\<Sum>b\<in>B. c' b *\<^sub>C b)" and "finite B" and BX: "B \<subseteq> X"
      unfolding span_explicit by auto
    define A and c where "A = vec_of_onb_enum ` B"
      and "c b = c' (onb_enum_of_vec b)" for b
    have "vec_of_onb_enum x = vec_of_onb_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)"
      using x by simp
    also have "\<dots> = lincomb c A"
      apply (rule lincomb_sum[symmetric])
      unfolding A_def c_def using BX \<open>finite B\<close>
      by (auto simp: image_image)
    also have "\<dots> \<in> span (vec_of_onb_enum ` X)"
      unfolding span_def apply (rule CollectI)
      apply (rule exI, rule exI)
      unfolding A_def using \<open>finite B\<close> BX by auto
    finally show "vec_of_onb_enum x \<in> local.span (vec_of_onb_enum ` X)"
      by -
  qed
qed

lemma (in complex_vec_space) module_span_complex_span':
  assumes "canonical_basis_length TYPE('a) = n"
  assumes "Y \<subseteq> carrier_vec n"
  shows "complex_span (onb_enum_of_vec ` Y :: 'a::onb_enum set) = onb_enum_of_vec ` local.span Y"
proof -
  define X::"'a set" where "X = onb_enum_of_vec ` Y"
  then have "complex_span (onb_enum_of_vec ` Y :: 'a set) = onb_enum_of_vec ` vec_of_onb_enum ` complex_span X"
    by (simp add: image_image)
  also have "\<dots> = onb_enum_of_vec ` local.span (vec_of_onb_enum ` X)"
    apply (subst module_span_complex_span)
    using assms by simp_all
  also have "vec_of_onb_enum ` X = Y"
    unfolding X_def image_image
    apply (rule image_cong[where g=id and M=Y and N=Y, simplified])
    using assms(1) assms(2) by auto
  finally show ?thesis
    by simp
qed

lemma Span_onb_enum_gram_schmidt0:
  defines "onb_enum == (onb_enum_of_vec :: _ \<Rightarrow> 'a::onb_enum)"
  defines "n == canonical_basis_length TYPE('a)"
  assumes "set ws \<subseteq> carrier_vec n"
  shows "Span (set (map onb_enum (gram_schmidt0 n ws)))
     = Span (set (map onb_enum ws))"
proof (transfer fixing: n ws onb_enum)
  interpret complex_vec_space.
  define gs where "gs = gram_schmidt0 n ws"
  have "closure (complex_span (set (map onb_enum gs)))
     = complex_span (set (map onb_enum gs))"
    apply (rule span_finite_dim)
    by simp
  also have "\<dots> = complex_span (onb_enum ` set gs)"
    by simp
  also have "\<dots> = onb_enum ` span (set gs)"
    unfolding onb_enum_def
    apply (rule module_span_complex_span')
    using n_def apply simp
    by (simp add: assms(3) cof_vec_space.gram_schmidt0_result(1) gs_def)
  also have "\<dots> = onb_enum ` span (set ws)"
    unfolding gs_def
    apply (subst gram_schmidt0_result(4)[where ws=ws, symmetric])
    using assms by auto
  also have "\<dots> = complex_span (onb_enum ` set ws)"
    unfolding onb_enum_def
    apply (rule module_span_complex_span'[symmetric])
    using n_def apply simp
    by (simp add: assms(3))
  also have "\<dots> = complex_span (set (map onb_enum ws))"
    by simp
  also have "\<dots> = closure (complex_span (set (map onb_enum ws)))"
    apply (rule span_finite_dim[symmetric])
    by simp
  finally show "closure (complex_span (set (map onb_enum gs)))
              = closure (complex_span (set (map onb_enum ws)))".
qed



subsection \<open>Code equations for cblinfun operators\<close>

text \<open>In this subsection, we define the code for all operations involving only 
  operators (no combinations of operators/vectors/subspaces)\<close>


text \<open>The following lemma registers cblinfun as an abstract datatype with 
  constructor \<^const>\<open>cblinfun_of_mat\<close>.
  That means that in generated code, all cblinfun operators will be represented
  as \<^term>\<open>cblinfun_of_mat X\<close> where X is a matrix.
  In code equations for operations involving operators (e.g., +), we
  can then write the equation directly in terms of matrices
  by writing, e.g., \<^term>\<open>mat_of_cblinfun (A+B)\<close> in the lhs,
  and in the rhs we define the matrix that corresponds to the sum of A,B.
  In the rhs, we can access the matrices corresponding to A,B by
  writing \<^term>\<open>mat_of_cblinfun B\<close>.
  (See, e.g., lemma \<open>cblinfun_of_mat_plusOp\<close> below).

  See [TODO: bibtex reference to code generation tutorial] for more information on 
  @{theory_text \<open>[code abstype]\<close>}.\<close>

declare mat_of_cblinfun_inverse [code abstype]


text \<open>This lemma defines addition. By writing \<^term>\<open>mat_of_cblinfun (M + N)\<close>
on the left hand side, we get access to the\<close>
  (* TODO: rename \<rightarrow> cblinfun_of_mat_plus *)
declare cblinfun_of_mat_plusOp'[code]
  (* TODO: rename (remove ') *)
declare cblinfun_of_mat_id'[code]
  (* TODO: rename (remove ') *)
declare mat_of_cblinfun_zero'[code]
  (* TODO: rename (remove ') *)
declare cblinfun_of_mat_uminusOp'[code]
  (* TODO: rename (remove ') *)
declare cblinfun_of_mat_minusOp'[code]
  (* TODO: rename (remove inj_option) *)
declare mat_of_cblinfun_classical_operator_inj_option[code]
declare cblinfun_of_mat_timesOp[code]
declare mat_of_cblinfun_scalarMult[code]
declare mat_of_cblinfun_scaleR[code]
declare cblinfun_of_mat_adjoint[code]

text \<open>This instantiation defines a code equation for equality tests for cblinfun operators.\<close>
instantiation cblinfun :: (onb_enum,onb_enum) equal begin
definition [code]: "equal_cblinfun M N \<longleftrightarrow> mat_of_cblinfun M = mat_of_cblinfun N" 
  for M N :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
instance 
  apply intro_classes
  unfolding equal_cblinfun_def 
  using mat_of_cblinfun_inj injD by fastforce
end

subsection \<open>Vectors\<close>


text \<open>In this section, we define code for operations on vectors. As with operators above,
  we do this by using an isomorphism between finite vectors
  (i.e., types T of sort \<open>complex_vector\<close>) and the type \<^typ>\<open>complex vec\<close> from
  \<^session>\<open>Jordan_Normal_Form\<close>. We have developed such an isomorphism in 
  \<^theory>\<open>Bounded_Operators.Bounded_Operators_Matrices\<close> for 
  any type T of sort \<open>onb_enum\<close> (i.e., any type with a finite canonical orthonormal basis)
  as was done above for bounded operators.
  Unfortunately, we cannot declare code equations for a type class, 
  code equations must be related to a specific type constructor.
  So we give code definition only for vectors of type \<^typ>\<open>'a ell2\<close> (where \<^typ>\<open>'a\<close>
  must be of sort \<open>enum\<close> to make make sure that  \<^typ>\<open>'a ell2\<close> is finite dimensional).
  
  The isomorphism between \<^typ>\<open>'a ell2\<close> is given by the constants \<open>ell2_of_vec\<close>
  and \<open>vec_of_ell2\<close> which are copies of the more general \<^const>\<open>onb_enum_of_vec\<close>
  and \<^const>\<open>vec_of_onb_enum\<close> but with a more restricted type to be usable in our code equations.
\<close>

definition ell2_of_vec :: "complex vec \<Rightarrow> 'a::enum ell2" where "ell2_of_vec = onb_enum_of_vec"
definition vec_of_ell2 :: "'a::enum ell2 \<Rightarrow> complex vec" where "vec_of_ell2 = vec_of_onb_enum"

text \<open>The following theorem registers the isomorphism \<open>ell2_of_vec\<close>/\<open>vec_of_ell2\<close>
  for code generation. From now on,
  code for operations on \<^typ>\<open>_ ell2\<close> can be expressed by declarations such
  as \<^term>\<open>vec_of_ell2 (f a b) = g (vec_of_ell2 a) (vec_of_ell2 b)\<close>
  if the operation f on \<^typ>\<open>_ ell2\<close> corresponds to the operation g on
  \<^typ>\<open>complex vec\<close>.\<close>

lemma vec_of_ell2_inverse [code abstype]:
  "ell2_of_vec (vec_of_ell2 B) = B" 
  unfolding ell2_of_vec_def vec_of_ell2_def
  by (rule onb_enum_of_vec_inverse)

instantiation ell2 :: (enum) equal begin
definition [code]: "equal_ell2 M N \<longleftrightarrow> vec_of_ell2 M = vec_of_ell2 N" 
  for M N :: "'a::enum ell2"
instance 
  apply intro_classes
  unfolding equal_ell2_def
  by (metis vec_of_ell2_inverse) 
end

lemma vec_of_ell2_zero[code]:
  "vec_of_ell2 (0::'a::enum ell2) = zero_vec (canonical_basis_length TYPE('a ell2))"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_zero)

(* TODO: To preliminaries *)
fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"


lemma index_of_length: "index_of x y \<le> length y"
proof(induction y)
  case Nil
  thus ?case by auto
next
  case (Cons a y)
  thus ?case by auto
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
    thus ?thesis apply auto
      using Cons.IH Cons.prems(2) by fastforce
  qed
qed

(* TODO: To preliminaries *)
definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"

(* TODO To preliminaries *)
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

(* TODO To preliminaries *)
lemma enum_idx_correct: 
  "Enum.enum ! enum_idx i = i"
proof-
  have "i \<in> set enum_class.enum"
    using UNIV_enum by blast 
  thus ?thesis
    unfolding enum_idx_def
    using index_of_correct by metis
qed

(* TODO: To Bounded_Operators_Matrices *)
lemma vec_of_ell2_ket:
  "vec_of_ell2 (ket i) = unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)" 
  for i::"'a::enum"
proof-
  have "dim_vec (vec_of_ell2 (ket i)) 
      = dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i))"
  proof-
    have "dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) 
      = canonical_basis_length TYPE('a ell2)"
      by simp     
    moreover have "dim_vec (vec_of_ell2 (ket i)) = canonical_basis_length TYPE('a ell2)"
      unfolding vec_of_ell2_def vec_of_onb_enum_def apply auto
      using canonical_basis_length_eq[where 'a = "'a ell2"] by auto
    ultimately show ?thesis by simp
  qed
  moreover have "vec_of_ell2 (ket i) $ j =
    (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) $ j"
    if "j < dim_vec (vec_of_ell2 (ket i))"
    for j
  proof-
    have j_bound: "j < length (canonical_basis::'a ell2 list)"
      by (metis dim_vec_of_onb_enum_list' that vec_of_ell2_def)
    have y1: "complex_independent (set (canonical_basis::'a ell2 list))"
      using canonical_basis_non_zero is_ortho_set_independent is_orthonormal by auto        
    have y2: "canonical_basis ! j \<in> set (canonical_basis::'a ell2 list)"
      using j_bound by auto
    have p1: "enum_class.enum ! enum_idx i = i"
      using enum_idx_correct by blast
    moreover have p2: "(canonical_basis::'a ell2 list) ! t  = ket ((enum_class.enum::'a list) ! t)"
      if "t < length (enum_class.enum::'a list)"
      for t
      unfolding canonical_basis_ell2_def 
      using that by auto
    moreover have p3: "enum_idx i < length (enum_class.enum::'a list)"
    proof-
      have "set (enum_class.enum::'a list) = UNIV"
        using UNIV_enum by blast
      hence "i \<in> set (enum_class.enum::'a list)"
        by blast
      thus ?thesis
        unfolding enum_idx_def
        by (metis index_of_bound length_greater_0_conv length_pos_if_in_set) 
    qed
    ultimately have p4: "(canonical_basis::'a ell2 list) ! (enum_idx i)  = ket i"
      by auto
    have "enum_idx i < length (enum_class.enum::'a list)"
      using p3
      by auto
    moreover have "length (enum_class.enum::'a list) = dim_vec (vec_of_ell2 (ket i))"
      unfolding vec_of_ell2_def canonical_basis_ell2_def
      using dim_vec_of_onb_enum_list'[where v = "ket i"]
      unfolding canonical_basis_ell2_def by simp              
    ultimately have "enum_idx i < dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) 
        (enum_idx i))"
      using \<open>dim_vec (vec_of_ell2 (ket i)) = dim_vec (unit_vec (canonical_basis_length 
        TYPE('a ell2)) (enum_idx i))\<close> by auto            
    hence r1: "(unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) $ j
        = (if enum_idx i = j then 1 else 0)"
      using \<open>dim_vec (vec_of_ell2 (ket i)) = dim_vec (unit_vec (canonical_basis_length 
        TYPE('a ell2)) (enum_idx i))\<close> that by auto
    moreover have "vec_of_ell2 (ket i) $ j = (if enum_idx i = j then 1 else 0)"
    proof(cases "enum_idx i = j")
      case True                        
      have "Complex_Vector_Spaces.representation (set (canonical_basis::'a ell2 list)) 
          ((canonical_basis::'a ell2 list) ! j) ((canonical_basis::'a ell2 list) ! j) = 1"        
        using y1 y2 Complex_Vector_Spaces.representation_basis[where 
            basis = "set (canonical_basis::'a ell2 list)" 
            and b = "(canonical_basis::'a ell2 list) ! j"]
        by (smt ) 

      hence "vec_of_onb_enum ((canonical_basis::'a ell2 list) ! j) $ j = 1"
        unfolding vec_of_onb_enum_def 
        by (metis True \<open>enum_idx i < dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) 
          (enum_idx i))\<close> canonical_basis_length_eq index_unit_vec(3) list_of_vec_index list_vec nth_map)
      hence "vec_of_onb_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) 
            $ enum_idx i = 1"
        using True by simp
      hence "vec_of_onb_enum (ket i) $ enum_idx i = 1"
        using p4
        by simp
      thus ?thesis using True unfolding vec_of_ell2_def by auto
    next
      case False
      have "Complex_Vector_Spaces.representation (set (canonical_basis::'a ell2 list)) 
          ((canonical_basis::'a ell2 list) ! (enum_idx i)) ((canonical_basis::'a ell2 list) ! j) = 0"        
        using y1 y2 Complex_Vector_Spaces.representation_basis[where 
            basis = "set (canonical_basis::'a ell2 list)" 
            and b = "(canonical_basis::'a ell2 list) ! j"]
          False \<open>enum_idx i < dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) 
          (enum_idx i))\<close> canonical_basis_length_eq 
          complex_vector.representation_basis distinct_canonical_basis index_unit_vec(3) 
          j_bound nth_eq_iff_index_eq nth_mem 
        by (metis ) 
      hence "vec_of_onb_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) $ j = 0"
        unfolding vec_of_onb_enum_def by (smt j_bound nth_map vec_of_list_index)        
      hence "vec_of_onb_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) 
            $ j = 0"
        by auto
      hence "vec_of_onb_enum (ket i) $ j = 0"
        using p4
        by simp
      thus ?thesis using False unfolding vec_of_ell2_def by simp
    qed
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis 
    using Matrix.eq_vecI
    by auto
qed

(* TODO: To preliminaries *)
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
  show ?thesis
    unfolding enum_idx_def apply (rule Bounded_Operators_Code.index_of_bound[where x = x 
          and y = "(Enum.enum :: 'a list)"])
    using p1 apply auto using p2 by auto
qed

(* TODO: To Bounded_Operators_Matrices *)
lemma vec_of_basis_vector:
  assumes "i < canonical_basis_length TYPE('a)"
  shows "vec_of_onb_enum (canonical_basis!i :: 'a)
       = unit_vec (canonical_basis_length TYPE('a::basis_enum)) i" 
proof-
  have "dim_vec (vec_of_onb_enum (canonical_basis!i :: 'a)) 
      = dim_vec (unit_vec (canonical_basis_length TYPE('a)) i)"
  proof-
    have "dim_vec (unit_vec (canonical_basis_length TYPE('a)) i) 
      = canonical_basis_length TYPE('a)"
      by simp     
    moreover have "dim_vec (vec_of_onb_enum (canonical_basis!i :: 'a)) 
        = canonical_basis_length TYPE('a)"
      unfolding vec_of_ell2_def vec_of_onb_enum_def apply auto
      using canonical_basis_length_eq[where 'a = "'a"] by auto
    ultimately show ?thesis by simp
  qed
  moreover have "vec_of_onb_enum (canonical_basis!i :: 'a) $ j =
    (unit_vec (canonical_basis_length TYPE('a)) i) $ j"
    if "j < dim_vec (vec_of_onb_enum (canonical_basis!i::'a))"
    for j
  proof-
    have j_bound: "j < length (canonical_basis::'a list)"
      by (metis dim_vec_of_onb_enum_list' that)
    have y1: "complex_independent (set (canonical_basis::'a list))"
      by (simp add: is_complex_independent_set)              
    have y2: "canonical_basis ! j \<in> set (canonical_basis::'a list)"
      using j_bound by auto    
    have "i < dim_vec (unit_vec (canonical_basis_length TYPE('a)) i)"
      by (simp add: assms)
    hence r1: "(unit_vec (canonical_basis_length TYPE('a)) i) $ j
        = (if i = j then 1 else 0)"
      by (simp add: canonical_basis_length_eq j_bound)
    have r2: "vec_of_onb_enum ((canonical_basis::'a list) ! i) $ j = (if i = j then 1 else 0)"
    proof(cases "i = j")
      case True
      have "\<not> Complex_Vector_Spaces.dependent (set (canonical_basis::'a list))"
        using is_complex_independent_set
        by (simp add: )       
      moreover have "canonical_basis ! i \<in> set (canonical_basis::'a list)"
        by (simp add: True y2)        
      ultimately have "(Complex_Vector_Spaces.representation
            (set (canonical_basis::'a list)) ((canonical_basis::'a list) ! i)) 
          ((canonical_basis::'a list) ! i) = 1"       
        using Complex_Vector_Spaces.representation_basis[where basis = "set (canonical_basis::'a list)" 
            and b = "(canonical_basis::'a list)!i"] by simp
      hence "vec_of_onb_enum ((canonical_basis::'a list) ! i) $ j = 1"
        unfolding vec_of_onb_enum_def using True by (smt j_bound nth_map vec_of_list_index)
      thus ?thesis using True by simp
    next
      case False
      have "\<not> Complex_Vector_Spaces.dependent (set (canonical_basis::'a list))"
        using is_complex_independent_set
        by (simp add: )     
      moreover have "canonical_basis ! j \<in> set (canonical_basis::'a list)"
        by (simp add: y2)
      ultimately have "(Complex_Vector_Spaces.representation
            (set (canonical_basis::'a list)) ((canonical_basis::'a list) ! i)) 
          ((canonical_basis::'a list) ! j) = 0"       
        using Complex_Vector_Spaces.representation_basis[where basis = 
            "set (canonical_basis::'a list)" 
            and b = "(canonical_basis::'a list)!i"] False 
        by (smt assms canonical_basis_length_eq distinct_canonical_basis j_bound nth_eq_iff_index_eq 
            nth_mem) 
      hence "vec_of_onb_enum ((canonical_basis::'a list) ! i) $ j = 0"
        unfolding vec_of_onb_enum_def using False by (smt j_bound nth_map vec_of_list_index)
      thus ?thesis using False by simp
    qed
    show ?thesis using r1 r2 by auto
  qed
  ultimately show ?thesis 
    using Matrix.eq_vecI
    by auto
qed


(* TODO: To Bounded_Operators_Matrices *)
lemma ket_canonical_basis: "ket x = canonical_basis ! enum_idx x"  
proof-
  have "x = (enum_class.enum::'a list) ! enum_idx x"
    using Bounded_Operators_Code.enum_idx_correct[where i = x] by simp
  hence p1: "ket x = ket ((enum_class.enum::'a list) ! enum_idx x)"
    by simp
  have "enum_idx x < length (enum_class.enum::'a list)"
    using Bounded_Operators_Code.enum_idx_bound[where x = x].
  hence "(map ket (enum_class.enum::'a list)) ! enum_idx x 
        = ket ((enum_class.enum::'a list) ! enum_idx x)"
    by auto      
  thus ?thesis
    unfolding canonical_basis_ell2_def using p1 by auto    
qed

declare vec_of_ell2_ket[code]

lemma vec_of_ell2_timesScalarVec[code]: "vec_of_ell2 (scaleC a \<psi>) = smult_vec a (vec_of_ell2 \<psi>)"
  for \<psi> :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_scaleC)

lemma vec_of_ell2_scaleR[code]: "vec_of_ell2 (scaleR a \<psi>) = smult_vec (complex_of_real a) (vec_of_ell2 \<psi>)"
  for \<psi> :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_scaleR)

lemma ell2_of_vec_plus[code]:
  "vec_of_ell2 (x + y) =  (vec_of_ell2 x) + (vec_of_ell2 y)" for x y :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_add) 

lemma ell2_of_vec_minus[code]:
  "vec_of_ell2 (x - y) =  (vec_of_ell2 x) - (vec_of_ell2 y)" for x y :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_minus)

lemma ell2_of_vec_uminus[code]:
  "vec_of_ell2 (- y) =  - (vec_of_ell2 y)" for y :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_uminus)

lemma cinner_ell2_code' [code]: "cinner \<psi> \<phi> = cscalar_prod (vec_of_ell2 \<phi>) (vec_of_ell2 \<psi>)"
  by (simp add: cinner_ell2_code vec_of_ell2_def)

lemma norm_ell2_code [code]: "norm \<psi> = 
  (let \<psi>' = vec_of_ell2 \<psi> in
    sqrt (\<Sum> i \<in> {0 ..< dim_vec \<psi>'}. let z = vec_index \<psi>' i in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
  by (simp add: norm_ell2_code vec_of_ell2_def)


lemma complex_span_singleton:
  fixes x y::"'a::complex_vector"
  assumes a1: "x \<in> complex_span {y}"
  shows "\<exists>\<alpha>. x = \<alpha> *\<^sub>C y"
proof-
  have "\<exists>t r. x = (\<Sum>j\<in>t. r j *\<^sub>C j) \<and> finite t \<and> t \<subseteq> {y}"
    using a1 using complex_vector.span_explicit[where b = "{y}"]
    by (smt  mem_Collect_eq)
  then obtain t r where b1: "x = (\<Sum>j\<in>t. r j *\<^sub>C j)" and b2: "finite t" and b3: "t \<subseteq> {y}"
    by blast
  show ?thesis
  proof(cases "t = {}")
    case True
    hence "(\<Sum>j\<in>t. r j *\<^sub>C j) = 0"
      using b2
      by simp
    thus ?thesis using b1 by simp
  next
    case False
    hence "t = {y}"
      using b3 by auto
    moreover have "(\<Sum>j\<in>{y}. r j *\<^sub>C j) = r y *\<^sub>C y"
      by auto
    ultimately show  ?thesis using b1 by blast
  qed

qed

(* TODO move to ..._Matrices *)
(* TODO better name *)
lemma times_ell2_code: 
  fixes \<psi> \<phi> :: "'a::{CARD_1,enum} ell2"
  shows "vec_of_ell2 (\<psi> * \<phi>)
   = vec_of_list [vec_index (vec_of_ell2 \<psi>) 0 * vec_index (vec_of_ell2 \<phi>) 0]"
proof-
  have "\<exists>i. i\<in>(UNIV::'a set)"
    by blast
  then obtain i where i_def: "i\<in>(UNIV::'a set)"
    by blast
  have "set (enum_class.enum::'a list) = UNIV"
    using UNIV_enum by blast
  moreover have "card (UNIV::'a set) = 1"
    by (simp add: CARD_1)      
  moreover have "distinct (enum_class.enum::'a list)"
    using enum_distinct by auto
  ultimately have "length (enum_class.enum::'a list) = 1"
    using distinct_card by fastforce      
  hence p0: "length (canonical_basis::'a ell2 list) = 1"
    unfolding canonical_basis_ell2_def by simp
  hence q1: "canonical_basis_length TYPE('a ell2) = 1"
    using canonical_basis_length_eq[where 'a = "'a ell2"] by simp
  have "vec_of_ell2 f = vec_of_list [vec_of_ell2 f $ 0]"
    for f::"'a ell2" 
  proof-
    have p1: "dim_vec (vec_of_ell2 f) = 1"
      using p0
      unfolding vec_of_ell2_def vec_of_onb_enum_def
      by auto
    have "(vec_of_ell2 f) $ k = vec_of_list [vec_of_ell2 f $ 0] $ k"
      if "k < dim_vec (vec_of_ell2 f)"
      for k
    proof-
      have "k = 0"
        using that p1 by auto
      moreover have "vec_of_list [vec_of_ell2 f $ 0] $ 0 = vec_of_ell2 f $ 0"
        by simp        
      ultimately show ?thesis by simp
    qed
    moreover have "dim_vec (vec_of_list [vec_of_ell2 f $ 0]) = 1"
    proof-
      have "length [vec_of_ell2 f $ 0] = 1"
        by simp
      thus ?thesis
        by simp 
    qed
    ultimately show ?thesis
      by (metis eq_vecI p1) 
  qed
  hence "vec_of_ell2 (\<psi> * \<phi>) = vec_of_list [vec_of_ell2 (\<psi> * \<phi>) $ 0]"
    by blast
  also have "\<dots> = vec_of_list [vec_of_ell2 \<psi> $ 0 * vec_of_ell2 \<phi> $ 0]"
  proof-
    have "Rep_ell2 (\<psi> * \<phi>) i = Rep_ell2 \<psi> i * Rep_ell2 \<phi> i"
      by (simp add: times_ell2.rep_eq)
    moreover have "vec_of_ell2 x $ 0 = Rep_ell2 x i"
      for x
    proof-
      have "(UNIV::'a set) = {i}"
        using CARD_1[where 'a = 'a] i_def by auto
      hence t1: "set (enum_class.enum::'a list) = {i}"
        using UNIV_enum by auto
      hence s0: "(enum_class.enum::'a list)!0 = i"
        by auto
      have "card (set (enum_class.enum::'a list)) = 1"
        using t1 by simp
      hence "length (enum_class.enum::'a list) = 1"
        using enum_distinct List.distinct_card by smt
      hence "(enum_class.enum::'a list) = [i]"
        by (metis s0 One_nat_def length_0_conv length_Suc_conv length_nth_simps(3))                    
      hence "map ket (enum_class.enum::'a list) = [ket i]"
        by (metis list.simps(8) list.simps(9))          
      hence "(map ket (enum_class.enum::'a list)) ! 0 = ket i"
        by simp
      hence ket_canonical_basis: "(canonical_basis::'a ell2 list)!0 = ket i"
        unfolding canonical_basis_ell2_def.
      have x_ket: "x = Rep_ell2 x i *\<^sub>C ket i"
      proof-
        have "x \<in> complex_span (range ket)"
          using finite_class.finite_UNIV finite_imageI ket_ell2_span span_finite_dim
          by (metis  iso_tuple_UNIV_I) 

        moreover have "range (ket::'a \<Rightarrow>_) = {ket i}"
          by (simp add: \<open>UNIV = {i}\<close>)
        ultimately have "x \<in> complex_span {ket i}"
          by simp
        hence "\<exists>\<alpha>. x = \<alpha> *\<^sub>C ket i"
          using complex_span_singleton by blast
        then obtain \<alpha> where "x = \<alpha> *\<^sub>C ket i"
          by blast
        hence "(Rep_ell2 x) i = (Rep_ell2 (\<alpha> *\<^sub>C ket i)) i"
          by simp
        moreover have "(Rep_ell2 (\<alpha> *\<^sub>C ket i)) i = \<alpha>"
          apply transfer
          by simp
        ultimately show ?thesis
          by (simp add: \<open>x = \<alpha> *\<^sub>C ket i\<close>) 
      qed
      have "x = Rep_ell2 x i *\<^sub>C (canonical_basis::'a ell2 list)!0"
        using i_def x_ket ket_canonical_basis by simp
      hence "vec_of_ell2 x = vec_of_ell2 (Rep_ell2 x i *\<^sub>C (canonical_basis::'a ell2 list)!0)"
        by simp
      also have "\<dots> = Rep_ell2 x i \<cdot>\<^sub>v vec_of_ell2 ((canonical_basis::'a ell2 list)!0)"
        by (simp add: vec_of_ell2_timesScalarVec)
      also have "\<dots> = Rep_ell2 x i \<cdot>\<^sub>v unit_vec (canonical_basis_length TYPE('a ell2)) 0"
        by (simp add: canonical_basis_length_ell2_def vec_of_basis_vector vec_of_ell2_def)
      finally have "vec_of_ell2 x
         = Rep_ell2 x i \<cdot>\<^sub>v unit_vec (canonical_basis_length TYPE('a ell2)) 0".
      hence "vec_of_ell2 x $ 0
         = (Rep_ell2 x i \<cdot>\<^sub>v unit_vec (canonical_basis_length TYPE('a ell2)) 0) $ 0"
        by simp
      also have "\<dots> = Rep_ell2 x i * ((unit_vec (canonical_basis_length TYPE('a ell2)) 0) $ 0)"
        by (simp add: canonical_basis_length_ell2_def)
      also have "\<dots> = Rep_ell2 x i"
      proof-
        have "(unit_vec (canonical_basis_length TYPE('a ell2)) 0) $ 0 = 1"
          using q1
          by auto
        thus ?thesis by auto
      qed
      finally show ?thesis.
    qed  
    ultimately have "vec_of_ell2 (\<psi> * \<phi>) $ 0 = vec_of_ell2 \<psi> $ 0 * vec_of_ell2 \<phi> $ 0"
      by auto
    thus ?thesis by simp
  qed
  finally show "vec_of_ell2 (\<psi> * \<phi>) =
        vec_of_list [vec_of_ell2 \<psi> $ 0 * vec_of_ell2 \<phi> $ 0]".
qed

declare times_ell2_code[code]

(* TODO move to ..._Matrices *)
(* TODO better name *)
lemma one_ell2_code: "vec_of_ell2 (1 :: 'a::{CARD_1,enum} ell2) = vec_of_list [1]"
proof-
  have "\<exists>i. i\<in>(UNIV::'a set)"
    by blast
  then obtain i where i_def: "i\<in>(UNIV::'a set)"
    by blast
  have "set (enum_class.enum::'a list) = UNIV"
    using UNIV_enum by blast
  moreover have "card (UNIV::'a set) = 1"
    by (simp add: CARD_1)      
  moreover have "distinct (enum_class.enum::'a list)"
    using enum_distinct by auto
  ultimately have "length (enum_class.enum::'a list) = 1"
    by (metis One_nat_def UNIV_witness \<open>\<exists>i. i \<in> UNIV\<close> card_num1 class_semiring.one_closed
        length_remdups_card_conv plus_1_eq_Suc remdups_id_iff_distinct top.extremum_unique)      
  hence p0: "length (canonical_basis::'a ell2 list) = 1"
    unfolding canonical_basis_ell2_def by simp
  have w1: "vec_of_ell2 f = vec_of_list [vec_of_ell2 f $ 0]"
    for f::"'a ell2" 
  proof-
    have p1: "dim_vec (vec_of_ell2 f) = 1"
      using p0 
      unfolding vec_of_ell2_def vec_of_onb_enum_def
      by auto
    have "(vec_of_ell2 f) $ k = vec_of_list [vec_of_ell2 f $ 0] $ k"
      if "k < dim_vec (vec_of_ell2 f)"
      for k
    proof-
      have "k = 0"
        using that p1 by auto
      moreover have "vec_of_list [vec_of_ell2 f $ 0] $ 0 = vec_of_ell2 f $ 0"
        by simp        
      ultimately show ?thesis by simp
    qed
    moreover have "dim_vec (vec_of_list [vec_of_ell2 f $ 0]) = 1"
    proof-
      have "length [vec_of_ell2 f $ 0] = 1"
        by simp
      thus ?thesis
        by simp 
    qed
    ultimately show ?thesis
      by (metis eq_vecI p1) 
  qed
  have "(Complex_Vector_Spaces.representation (set (canonical_basis::'a ell2 list)) 1) 
        ((canonical_basis::'a ell2 list)!0) = 1"
    by (simp add: complex_vector.representation_basis one_dim_canonical_basis)    
  hence "vec_of_ell2 (1 :: 'a::{CARD_1,enum} ell2) $ 0 = 1"
    unfolding vec_of_ell2_def vec_of_onb_enum_def vec_of_list_def id_def
    apply auto
    by (metis class_field.zero_not_one complex_vector.representation_ne_zero length_map 
        length_pos_if_in_set nth_map vec_of_list.abs_eq vec_of_list_index)
  thus ?thesis using w1[where f = "(1 :: 'a::{CARD_1,enum} ell2)"] by simp
qed


declare one_ell2_code[code]

subsection \<open>Vector/Matrix\<close>

(* TODO explain everything in this section *)

(* Wrapper class so that we can define a code datatype constructors for that type (does not work with type synonyms) *)
(* TODO: Find out if it's OK to remove the ell2 from the output (once QRHL compiles) *)
typedef ('a::enum,'b::enum) code_l2bounded = "UNIV::('a ell2, 'b ell2) cblinfun set" ..
setup_lifting type_definition_code_l2bounded

lift_definition l2bounded_of_mat' :: "complex mat \<Rightarrow> ('a::enum,'b::enum) code_l2bounded"
  is cblinfun_of_mat.
lift_definition mat_of_l2bounded' :: "('a::enum,'b::enum) code_l2bounded \<Rightarrow> complex mat"
  is mat_of_cblinfun.

lemma mat_of_cblinfun_inverse' [code abstype]:
  "l2bounded_of_mat' (mat_of_l2bounded' B) = B" 
  apply transfer
  using mat_of_cblinfun_inverse by blast

lemma [code]: "mat_of_l2bounded' (Abs_code_l2bounded X) = mat_of_cblinfun X"
  apply transfer by simp
lemma [code]: "mat_of_cblinfun (Rep_code_l2bounded X) = mat_of_l2bounded' X"
  apply transfer by simp


lift_definition applyOp_code :: "('a::enum, 'b::enum) code_l2bounded \<Rightarrow> 'a ell2 \<Rightarrow> 'b ell2" 
  is "cblinfun_apply :: ('a ell2,'b ell2) cblinfun \<Rightarrow> _ \<Rightarrow> _".

lemma [symmetric,code_abbrev]: "cblinfun_apply M = applyOp_code (Abs_code_l2bounded M)"
  apply transfer by simp

lemma ell2_of_vec_applyOp[code]:
  "vec_of_ell2 (applyOp_code M x) = (mult_mat_vec (mat_of_l2bounded' M) (vec_of_ell2 x))"
  by (simp add: applyOp_code.rep_eq mat_of_cblinfun_description mat_of_l2bounded'.rep_eq vec_of_ell2_def) 


(* TODO: move to ..._Matrices *)
lemma mat_of_cblinfun_ell2_to_l2bounded:
  "mat_of_cblinfun (vector_to_cblinfun \<psi>)
 = mat_of_cols (canonical_basis_length TYPE('a)) [vec_of_onb_enum \<psi>]"
  for \<psi>::"'a::onb_enum"  
proof-
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"
  have "nB = 1"
    unfolding nB_def 
    using one_dim_canonical_basis canonical_basis_length_eq
    apply auto
    by (simp add: canonical_basis_length_eq one_dim_canonical_basis)
  hence carrier_mat1: "mat_of_cols nA [vec_of_onb_enum \<psi>] \<in> carrier_mat nA nB"
    using mat_of_cols_carrier[where n = nA and vs = "[vec_of_onb_enum \<psi>]"]
    unfolding nA_def nB_def 
    by auto
  have t1: "mat_of_cols nA [vec_of_onb_enum \<psi>] \<in> carrier_mat nA nB"
    unfolding nA_def nB_def
    using carrier_mat1 nA_def nB_def by auto 
  have "one_dim_to_complex x *\<^sub>C \<psi> = (onb_enum_of_vec (mat_of_cols nA [vec_of_onb_enum \<psi>]
        *\<^sub>v vec_of_onb_enum x)::'a)"
    for x::'b
    using nA_def
  proof transfer
    fix x::'b and \<psi>::'a and nA::nat
    assume nA_def': "nA = canonical_basis_length TYPE('a)"
    have "length (canonical_basis::'b list) = 1"
      using one_dim_canonical_basis[where 'a = 'b]
      by (metis One_nat_def length_nth_simps(1) length_nth_simps(2)) 
    hence dim_vec_b: "dim_vec (vec_of_onb_enum x) = 1"
      by (simp add: dim_vec_of_onb_enum_list')            
    have "mat_of_cols nA [vec_of_onb_enum \<psi>] *\<^sub>v vec_of_onb_enum x
        = vec nA
     (\<lambda>i. scalar_prod (row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i) (vec_of_onb_enum x))"
      unfolding mult_mat_vec_def by auto
    also have "\<dots> = vec nA
     (\<lambda>i. \<Sum>j = 0..<1.
      row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i $ j * vec_of_onb_enum x $ j)"
      unfolding scalar_prod_def using dim_vec_b by auto
    also have "\<dots> = vec nA
     (\<lambda>i. \<Sum>j\<in>{0}.
      row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i $ j * vec_of_onb_enum x $ j)"
      by auto
    also have "\<dots> = vec nA
     (\<lambda>i. row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i $ 0 * vec_of_onb_enum x $ 0)"
      using VS_Connect.class_semiring.finsum_singleton_set by auto
    also have "\<dots> = vec nA
     (\<lambda>i. row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i $ 0 * one_dim_to_complex x)"
    proof-
      have "x = one_dim_to_complex x *\<^sub>C 1"
        by (simp add: one_dim_1_times_a_eq_a one_dim_to_complex_def)
      hence "vec_of_onb_enum x = vec_of_onb_enum (one_dim_to_complex x *\<^sub>C (1::'b))"
        by simp
      also have "\<dots> = one_dim_to_complex x \<cdot>\<^sub>v (vec_of_onb_enum (1::'b))"
        by (simp add: vec_of_onb_enum_scaleC)
      finally have "vec_of_onb_enum x = one_dim_to_complex x \<cdot>\<^sub>v (vec_of_onb_enum (1::'b))".
      hence "(vec_of_onb_enum x)$0 = (one_dim_to_complex x \<cdot>\<^sub>v (vec_of_onb_enum (1::'b)))$0"
        by auto
      also have "\<dots> = one_dim_to_complex x * ((vec_of_onb_enum (1::'b))$0)"
        using \<open>vec_of_onb_enum x = one_dim_to_complex x \<cdot>\<^sub>v vec_of_onb_enum 1\<close> dim_vec_b by auto
      also have "\<dots> = one_dim_to_complex x"
      proof-
        have "Complex_Vector_Spaces.representation
         (set (canonical_basis::'b list)) 1 ((canonical_basis::'b list)!0) = 1"
          by (simp add: complex_vector.representation_basis one_dim_canonical_basis)          
        hence "(vec_of_onb_enum (1::'b))$0 = 1"
          unfolding vec_of_onb_enum_def apply auto
          by (simp add: one_dim_canonical_basis) 
        thus ?thesis by simp
      qed
      finally have "vec_of_onb_enum x $ 0 = one_dim_to_complex x".
      thus ?thesis 
        unfolding one_dim_to_complex_def 
        by simp
    qed
    also have "\<dots> = vec nA
     (\<lambda>i. one_dim_to_complex x * (row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i) $ 0 )"
      by auto
    also have "\<dots> = vec nA
     (\<lambda>i. (one_dim_to_complex x \<cdot>\<^sub>v ( row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i) ) $ 0 )"
      by auto
    also have "\<dots> = vec nA
     (\<lambda>i. ( row (one_dim_to_complex x \<cdot>\<^sub>m mat_of_cols nA [vec_of_onb_enum \<psi>]) i) $ 0 )"
      by auto
    also have "\<dots> = vec nA
     (\<lambda>i. ( row (mat_of_cols nA [one_dim_to_complex x \<cdot>\<^sub>v vec_of_onb_enum \<psi>]) i) $ 0 )"
    proof-
      have sss: "a \<cdot>\<^sub>m mat_of_cols nA [y] = mat_of_cols nA [a \<cdot>\<^sub>v y]"
        if "dim_vec y = nA"
        for a and y::"complex vec"
      proof-
        have "(a \<cdot>\<^sub>m mat_of_cols nA [y]) $$ (i,j) = (mat_of_cols nA [a \<cdot>\<^sub>v y]) $$ (i,j)"
          if "i < dim_row (mat_of_cols nA [y])" and "j < dim_col (mat_of_cols nA [y])"
          for i j
          using that Matrix.index_smult_mat(1)[where i = i and j = j and a = a 
              and A = "mat_of_cols nA [y]"] apply auto
          by (simp add: \<open>dim_vec y = nA\<close> mat_of_cols_Cons_index_0)          
        thus ?thesis
          by auto
      qed
      have "dim_vec (vec_of_onb_enum \<psi>) = nA"
        by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list' nA_def')
      thus ?thesis
        using sss[where a = "one_dim_to_complex x" and y = "vec_of_onb_enum \<psi>"]
        by auto
    qed
    also have "\<dots> = vec nA
     (\<lambda>i. ( row (mat_of_cols nA [vec_of_onb_enum (one_dim_to_complex x *\<^sub>C \<psi>)]) i) $ 0 )"
      by (simp add: vec_of_onb_enum_scaleC)
    also have "\<dots> = vec_of_onb_enum (one_dim_to_complex x *\<^sub>C \<psi>)"
    proof-
      have ll: "vec nA (\<lambda>i. ( row (mat_of_cols nA [y]) i) $ 0 ) = y"
        if "dim_vec y = nA"
        for y::"complex vec"
      proof-
        have "vec nA (\<lambda>i. ( row (mat_of_cols nA [y]) i) $ 0 ) $ j = y $ j"
          if "j < dim_vec y"
          for j
        proof-
          have "vec nA (\<lambda>i. ( row (mat_of_cols nA [y]) i) $ 0 ) $ j
              = (row (mat_of_cols nA [y]) j) $ 0"
            using \<open>dim_vec y = nA\<close> index_vec that by blast            
          also have "\<dots> = y $ j"
            unfolding row_def apply auto unfolding mat_of_cols_def apply auto
            using \<open>dim_vec y = nA\<close> that by auto
          finally show ?thesis.
        qed
        thus ?thesis
          using dim_vec that by blast 
      qed
      have "dim_vec (vec_of_onb_enum (one_dim_to_complex (x::'b::one_dim) *\<^sub>C (\<psi>::'a::onb_enum))) 
            = (nA::nat)"
        by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list' nA_def')
      thus ?thesis using ll[where y = "vec_of_onb_enum (one_dim_to_complex x *\<^sub>C \<psi>)"]
        by blast
    qed
    finally have "mat_of_cols nA [vec_of_onb_enum \<psi>] *\<^sub>v vec_of_onb_enum x = 
              vec_of_onb_enum (one_dim_to_complex x *\<^sub>C \<psi>)". 
    thus "one_dim_to_complex x *\<^sub>C \<psi> =
          onb_enum_of_vec (mat_of_cols nA [vec_of_onb_enum \<psi>] *\<^sub>v vec_of_onb_enum x)" 
      by simp
  qed
  hence  "((vector_to_cblinfun \<psi>)::'b\<Rightarrow>\<^sub>C\<^sub>L'a) *\<^sub>V x
       = ((cblinfun_of_mat (mat_of_cols nA [vec_of_onb_enum \<psi>]))::'b\<Rightarrow>\<^sub>C\<^sub>L'a) *\<^sub>V x"
    for x
    using t1 
    unfolding nA_def nB_def apply auto
    by (simp add: cblinfun_of_mat.rep_eq)
  hence  "((vector_to_cblinfun \<psi>)::'b\<Rightarrow>\<^sub>C\<^sub>L'a)
       = ((cblinfun_of_mat (mat_of_cols nA [vec_of_onb_enum \<psi>]))::'b\<Rightarrow>\<^sub>C\<^sub>L'a)"
    using cblinfun_ext by blast        
  hence  "mat_of_cblinfun ((vector_to_cblinfun \<psi>)::'b\<Rightarrow>\<^sub>C\<^sub>L'a)
       = mat_of_cblinfun ((cblinfun_of_mat (mat_of_cols nA [vec_of_onb_enum \<psi>]))::'b\<Rightarrow>\<^sub>C\<^sub>L'a)"
    using [[show_sorts]]    
    by simp
  also have "mat_of_cblinfun
   (cblinfun_of_mat (mat_of_cols nA [vec_of_onb_enum \<psi>]) :: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a) =
                     mat_of_cols nA [vec_of_onb_enum \<psi>]"
    apply (rule cblinfun_of_mat_inverse[where 'a = 'b and 'b = 'a
          and M = "mat_of_cols nA [vec_of_onb_enum \<psi>]" and nA = nB and nB = nA])
    using carrier_mat1 nA_def nB_def by auto
  finally show ?thesis 
    unfolding nA_def by auto
qed

definition [code del,code_abbrev]: "vector_to_cblinfun_code (\<psi>::'a ell2) = (vector_to_cblinfun \<psi>)"

lemma mat_of_cblinfun_ell2_to_l2bounded_code[code]: 
  "mat_of_cblinfun (vector_to_cblinfun_code \<psi>) = mat_of_cols (CARD('a)) [vec_of_ell2 \<psi>]" 
  for \<psi>::"'a::enum ell2"
  by (simp add: mat_of_cblinfun_ell2_to_l2bounded canonical_basis_length_ell2_def vec_of_ell2_def vector_to_cblinfun_code_def)




subsection \<open>Subspaces\<close>

(* TODO add explanations *)

definition [code del]: "SPAN x = (let n = canonical_basis_length TYPE('a::onb_enum) in
    Span (onb_enum_of_vec ` Set.filter (\<lambda>v. dim_vec v = n) (set x)) :: 'a clinear_space)"
code_datatype SPAN


definition "mk_projector (S::'a::onb_enum clinear_space)
   = mat_of_cblinfun (Proj S)" 

(* TODO: move to ..._Matrices *)
text \<open>\<^term>\<open>mk_projector_orthog d L\<close> takes a list L of d-dimensional vectors
and returns the projector onto the span of L. (Assuming that all vectors in L are orthogonal
and nonzero.)\<close>

fun mk_projector_orthog :: "nat \<Rightarrow> complex vec list \<Rightarrow> complex mat" where
  "mk_projector_orthog d [] = zero_mat d d"
| "mk_projector_orthog d [v] = (let norm2 = cscalar_prod v v in
                                smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [conjugate v]))"
| "mk_projector_orthog d (v#vs) = (let norm2 = cscalar_prod v v in
                                   smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [conjugate v]) 
                                        + mk_projector_orthog d vs)"

lemma Span_insert:
  assumes "finite (S::'a'::complex_inner set)"
  shows "space_as_set (Span (insert a S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> space_as_set (Span S)}"
proof -
  have "closure (complex_span (insert a S)) = complex_span (insert a S)"
    by (metis assms finite_insert span_finite_dim)
  thus ?thesis
    by (simp add: Span.rep_eq assms complex_vector.span_insert span_finite_dim)
qed


lemma closed_subspace_complex_span_finite:
  assumes "finite (S::'a::chilbert_space set)"
  shows "closed_subspace (complex_span S)"
  unfolding closed_subspace_def apply auto
  by (simp add: assms closed_finite_dim)


lemma projection_singleton:
  assumes "(a::'a::chilbert_space) \<noteq> 0"
  shows "projection (complex_span {a}) u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
proof-
  define p where "p u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a" for u
  define M where "M = complex_span {a}"
  have "closed_subspace M"
    unfolding M_def 
    using closed_subspace_complex_span_finite
    by (simp add: closed_subspace_complex_span_finite)
  moreover have "u - p u \<in> orthogonal_complement M"
    unfolding p_def M_def orthogonal_complement_def
  proof auto
    fix y
    assume "y \<in> complex_span {a}" 
    hence "\<exists>c. y = c *\<^sub>C a"
      by (simp add: complex_span_singleton)
    then obtain c where c_def: "y = c *\<^sub>C a"
      by blast
    have "\<langle>u - (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, c *\<^sub>C a\<rangle> = 
          \<langle>u, c *\<^sub>C a\<rangle> - \<langle>(\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, c *\<^sub>C a\<rangle>"
      using cinner_diff_left by blast    
    also have "\<dots> = 0"
      by simp
    finally have "\<langle>u - (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, c *\<^sub>C a\<rangle> = 0".
    thus "\<langle>u - (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, y\<rangle> = 0"
      using c_def by simp
  qed
  moreover have "p u \<in> M"
    unfolding p_def M_def
    by (simp add: complex_vector.span_base complex_vector.span_scale)
  ultimately have "projection M u = p u"
    using projection_uniq[where x = "p u" and h = u and M = M] by blast
  thus ?thesis unfolding M_def p_def.
qed


lemma ortho_complex_span:
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> \<langle>a, s\<rangle> = 0" and a2: "finite (S::'a::chilbert_space set)"
    and a3: "x \<in> complex_span S"
  shows "\<langle>a, x\<rangle> = 0"
proof-
  have "\<exists>t r. finite t \<and> t \<subseteq> S \<and> (\<Sum>a\<in>t. r a *\<^sub>C a) = x"
    using complex_vector.span_explicit
    by (smt a3 mem_Collect_eq)
  then obtain t r where b1: "finite t" and b2: "t \<subseteq> S" and b3: "(\<Sum>a\<in>t. r a *\<^sub>C a) = x"
    by blast
  have x1: "\<langle>a, i\<rangle> = 0"
    if "i\<in>t" for i
    using b2 a1 that by blast
  have  "\<langle>a, x\<rangle> = \<langle>a, (\<Sum>i\<in>t. r i *\<^sub>C i)\<rangle>"
    by (simp add: b3) 
  also have  "\<dots> = (\<Sum>i\<in>t. r i *\<^sub>C \<langle>a, i\<rangle>)"
    by (simp add: cinner_sum_right)
  also have  "\<dots> = 0"
    using x1 by simp
  finally show ?thesis.
qed


lemma projection_insert:
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> \<langle>a, s\<rangle> = 0" and a2: "finite (S::'a::chilbert_space set)"
  shows "projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span S} u
        = projection (complex_span {a}) u
        + projection (complex_span S) u"
proof-
  define p where "p u = projection (complex_span {a}) u
                      + projection (complex_span S) u" for u
  define M where "M = {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span S}"
  have "projection (complex_span {a}) u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
    by (metis complex_vector.scale_zero_right complex_vector.span_empty complex_vector.span_insert_0 
        projection_singleton projection_zero_subspace)
  have "closed_subspace M"
    unfolding M_def
    by (metis (no_types) a2 closed_subspace_complex_span_finite complex_vector.span_insert 
        finite_insert) 
  moreover have "p u \<in> M"
    unfolding p_def M_def 
  proof auto 
    define k where "k = \<langle>a, u\<rangle>/\<langle>a, a\<rangle>"
    have "projection (complex_span {a}) u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
      by (simp add: \<open>projection (complex_span {a}) u = (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a\<close>)      
    hence "projection (complex_span {a}) u +
          projection (complex_span S) u - k *\<^sub>C a
          \<in> complex_span S"
      unfolding k_def
      by (simp add: a2 closed_subspace_complex_span_finite projection_intro2)      
    thus "\<exists>k. projection (complex_span {a}) u +
              projection (complex_span S) u - k *\<^sub>C a
              \<in> complex_span S"
      by blast
  qed
  moreover have "u - p u \<in> orthogonal_complement M"
    unfolding orthogonal_complement_def
  proof auto
    fix y
    assume b1: "y \<in> M"
    hence "\<exists>k. y - k *\<^sub>C a \<in> complex_span S"
      unfolding M_def by simp
    then obtain k where k_def: "y - k *\<^sub>C a \<in> complex_span S"
      by blast
    have "u - projection (complex_span S) u \<in> orthogonal_complement (complex_span S)"
      by (simp add: a2 closed_subspace_complex_span_finite projection_intro1)
    moreover have "projection (complex_span {a}) u \<in> orthogonal_complement (complex_span S)"
      unfolding orthogonal_complement_def
    proof auto
      fix y
      assume "y \<in> complex_span S"
      have "\<langle>a, y\<rangle> = 0"
        using ortho_complex_span
          \<open>y \<in> complex_span S\<close> a1 a2 by auto
      thus "\<langle>projection (complex_span {a}) u, y\<rangle> = 0"
        by (simp add: \<open>projection (complex_span {a}) u = (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a\<close>)         
    qed
    ultimately have "(u - projection (complex_span S) u)
                    - projection (complex_span {a}) u \<in> orthogonal_complement (complex_span S)"
      using Complex_Vector_Spaces.complex_vector.span_diff
      by (smt cinner_diff_left diff_zero orthogonal_complement_D1 orthogonal_complement_I2)
    hence "u - projection (complex_span {a}) u 
            - projection (complex_span S) u \<in> orthogonal_complement (complex_span S)"
      by (simp add: cancel_ab_semigroup_add_class.diff_right_commute)
    have "\<langle>u - projection (complex_span {a}) u 
         - projection (complex_span S) u, y - k *\<^sub>C a\<rangle> = 0"
      using \<open>u - projection (complex_span {a}) u - projection (complex_span S) u \<in> 
        orthogonal_complement (complex_span S)\<close> k_def orthogonal_complement_D1 by auto      
    moreover have "\<langle>u - projection (complex_span {a}) u 
         - projection (complex_span S) u, k *\<^sub>C a\<rangle> = 0"
    proof-
      have "u - projection (complex_span {a}) u \<in> orthogonal_complement (complex_span {a})"
        by (simp add: closed_subspace_complex_span_finite projection_intro1)
      moreover have "projection (complex_span S) u \<in> orthogonal_complement (complex_span {a})"
        unfolding orthogonal_complement_def
      proof auto
        fix y
        assume "y \<in> complex_span {a}"
        hence "\<exists>k. y = k *\<^sub>C a"
          by (simp add: complex_span_singleton)
        then obtain k where ky:"y = k *\<^sub>C a"
          by blast
        have "projection (complex_span S) u \<in> complex_span S"
          by (simp add: a2 closed_subspace_complex_span_finite projection_intro2)          
        hence "\<langle>projection (complex_span S) u, a\<rangle> = 0"
          by (meson a1 a2 ortho_complex_span orthogonal_complement_D2 orthogonal_complement_I2)          
        thus "\<langle>projection (complex_span S) u, y\<rangle> = 0"
          using ky
          by simp
      qed
      moreover have "complex_vector.subspace ( orthogonal_complement (complex_span {a}))"
        by (simp add: closed_subspace.subspace closed_subspace_complex_span_finite)

      ultimately have "(u - projection (complex_span {a}) u) - projection (complex_span S) u
                   \<in> orthogonal_complement (complex_span {a})"
        by (smt complex_vector.subspace_diff)
      thus ?thesis
        using complex_vector.span_base orthogonal_complement_D1 by fastforce 
    qed
    ultimately have "\<langle>u - projection (complex_span {a}) u 
         - projection (complex_span S) u, y\<rangle> = 0"
      by (metis cinner_right_distrib class_semiring.add.l_one 
          class_semiring.add.one_closed diff_add_cancel)      
    moreover have "\<langle>u - p u, y\<rangle> =
      \<langle>u - projection (complex_span {a}) u 
         - projection (complex_span S) u, y\<rangle>"
      unfolding p_def
      by (simp add: diff_diff_add) 
    ultimately show "\<langle>u - p u, y\<rangle> = 0" by simp
  qed
  ultimately have "projection M u = p u"
    using projection_uniq[where x = "p u" and h = u and M = M] by blast
  thus ?thesis 
    unfolding p_def M_def by auto
qed

(* TODO: replace by a more general lemma that show Proj (A\<union>B) = Proj A + Proj B
         under orthogonality assumptions *)
lemma Proj_Span_insert:
  fixes S :: "'a::{onb_enum, chilbert_space} list"
    and a::'a 
  assumes a1: "is_ortho_set (set (a#S))" and a2: "distinct (a#S)"
  shows "Proj (Span (set (a#S))) = Proj (Span {a}) + Proj (Span (set S))"
proof-
  define d where "d = canonical_basis_length TYPE('a)"
  hence IH': "is_ortho_set (set S)"
    using assms is_onb_delete by auto    
  have IH0: "distinct S"
    using a2 by auto   
  have "closure (complex_span (set S)) = complex_span (set S)"
    by (simp add: span_finite_dim)    
  have "complex_span (insert a (set S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}"
    using complex_vector.span_insert[where a = a and S = "(set S)"].
  moreover have "finite (insert a (set S))"
    by simp    
  ultimately have "closure (complex_span (insert a (set S))) = 
        complex_span {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}"
    by (metis complex_vector.span_span span_finite_dim)
  hence s2: "space_as_set (Abs_clinear_space (closure (complex_span (insert a (set S))))) 
        = complex_span {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}"
    by (metis Span.rep_eq space_as_set_inverse)
  have "closure (complex_span (set S)) = complex_span (set S)"
    by (simp add: span_finite_dim)    
  have ios: "is_ortho_set (set S)"
    by (simp add: IH')    
  have aS: "a \<notin> set S"
    using a2 by auto
  have "projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)} u
        = projection (complex_span {a}) u
        + projection (complex_span (set S)) u"
    for u   
    apply(rule projection_insert)
    using ios unfolding is_ortho_set_def
     apply (metis Set.set_insert Un_insert_left a1 aS insertI1 insert_union is_ortho_set_def list.simps(15))
    using aS
    by simp
  have s1: "projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)} u
        = projection (complex_span {a}) u + projection (complex_span (set S)) u"
    for u
    by (simp add: \<open>\<And>u. projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)} u
     = projection (complex_span {a}) u + projection (complex_span (set S)) u\<close>)
  have "Proj (Span (set (a#S))) = cBlinfun (projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)})"
    unfolding Proj_def Span_def id_def apply auto
    by (metis \<open>complex_span (insert a (set S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}\<close> 
        complex_vector.span_span s2)
  also have "\<dots> = (cBlinfun (\<lambda>u. projection (complex_span {a}) u
                   + projection (complex_span (set S)) u))"
    using s1
    by presburger 
  also have "\<dots> = cBlinfun (\<lambda>u. projection (complex_span {a}) u)
               +  cBlinfun (\<lambda>u. projection (complex_span (set S)) u)"
    unfolding plus_cblinfun_def apply auto
    by (metis (no_types, lifting) List.finite_set List.set_insert Proj.rep_eq Span.rep_eq
        cblinfun_apply_inverse finite.emptyI finite_list span_finite_dim)
  also have "\<dots> = Proj (Abs_clinear_space (complex_span {a}))
               +  Proj (Abs_clinear_space (complex_span (set S)))"
    unfolding Proj_def apply auto
    by (metis Span.rep_eq \<open>closure (complex_span (set S)) = complex_span (set S)\<close> finite.emptyI 
        finite.insertI space_as_set_inverse span_finite_dim)
  also have "\<dots> = Proj (Span {a}) + Proj (Span (set S))"
    by (simp add: Span.abs_eq span_finite_dim)
  finally show "Proj (Span (set (a#S))) = Proj (Span {a}) + Proj (Span (set S))".
qed


lemma mat_of_cblinfun_proj:
  fixes a::"'a::{onb_enum}"
  defines   "d == canonical_basis_length TYPE('a)"
    and "norm2 == (vec_of_onb_enum a) \<bullet>c (vec_of_onb_enum a)"
  shows  "mat_of_cblinfun (proj a) = 
      1 / norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a]
                 * mat_of_rows d [conjugate (vec_of_onb_enum a)])"
proof(cases "a = 0")
  case True
  have q1: \<open>mat_of_cblinfun (proj a) \<in> carrier_mat d d\<close>
    unfolding mat_of_cblinfun_def d_def
    by auto
  have"proj a = 0"
    using True
    apply transfer
    by (simp add: projection_zero_subspace)
  hence "mat_of_cblinfun (proj a) = 0\<^sub>m d d"
    by (metis q1 cancel_comm_monoid_add_class.diff_cancel 
        cblinfun_of_mat_minusOp' minus_r_inv_mat)
  moreover have "norm2 = 0"
    unfolding norm2_def
    by (metis Bounded_Operators_Matrices.cinner_ell2_code True cinner_zero_left) 
  ultimately show ?thesis by auto
next
  case False
  define basis where "basis = (canonical_basis :: 'a list)"
  have "mat_of_cols d [vec_of_onb_enum a] \<in> carrier_mat d 1"
    by auto
  moreover have "mat_of_rows d [vec_of_onb_enum a] \<in> carrier_mat 1 d"
    by auto
  ultimately have f1: "mat_of_cols d [vec_of_onb_enum a]
           * mat_of_rows d [conjugate (vec_of_onb_enum a)] \<in> carrier_mat d d"
    by auto
  have "mat_of_cblinfun (proj a) \<in> carrier_mat d d"
    unfolding d_def mat_of_cblinfun_def
    by auto
  moreover have "(1 / norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a]
             * mat_of_rows d [conjugate (vec_of_onb_enum a)]))
         \<in> carrier_mat d d"
  proof-
    have d1: "dim_vec (vec_of_onb_enum a) = d"
      by (simp add: canonical_basis_length_eq d_def dim_vec_of_onb_enum_list')
    hence d2: "mat_of_cols d [vec_of_onb_enum a] \<in> carrier_mat d 1"
      unfolding mat_of_cols_def by auto
    have d3: "mat_of_rows d [conjugate (vec_of_onb_enum a)] \<in> carrier_mat 1 d"
      using d1 unfolding mat_of_rows_def by auto
    have "mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)]
         \<in> carrier_mat d d"
      using d2 d3
      by simp 
    thus ?thesis
      by simp      
  qed
  moreover have "(mat_of_cblinfun (proj a)) $$ (i, j) = 
  (1 / norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)])) 
    $$ (i, j)"
    if "i < d" and "j < d" for i j
  proof-
    have norm2a: "norm2 = \<langle>a, a\<rangle>"
      unfolding norm2_def
      by (simp add: Bounded_Operators_Matrices.cinner_ell2_code)

    have "\<langle>a, basis ! j\<rangle> * cnj \<langle>a, basis ! i\<rangle>
        = (unit_vec d j \<bullet>c vec_of_onb_enum a) * cnj (unit_vec d i \<bullet>c vec_of_onb_enum a)"
    proof-
      have "\<langle>a, basis ! j\<rangle> = unit_vec d j \<bullet>c vec_of_onb_enum a"
        by (metis basis_def Bounded_Operators_Matrices.cinner_ell2_code d_def that(2) vec_of_basis_vector)
      moreover have "\<langle>a, basis ! i\<rangle> = unit_vec d i \<bullet>c vec_of_onb_enum a"
        by (metis basis_def Bounded_Operators_Matrices.cinner_ell2_code d_def that(1) vec_of_basis_vector)
      ultimately show ?thesis by simp
    qed
    have "\<dots> = (vec_of_onb_enum a $ i) * cnj (vec_of_onb_enum a $ j)"
    proof-
      have t1: "vec_of_onb_enum a \<in> carrier_vec d"
        by (metis add.right_neutral carrier_vec_dim_vec d_def index_add_vec(2) index_zero_vec(2) 
            vec_of_onb_enum_add vec_of_onb_enum_zero)
      hence "unit_vec d j \<bullet>c vec_of_onb_enum a = cnj (vec_of_onb_enum a $ j)"
        using Matrix.scalar_prod_left_unit that(2)
        by auto 
      moreover have "unit_vec d i \<bullet>c vec_of_onb_enum a = cnj (vec_of_onb_enum a $ i)"
        using t1 Matrix.scalar_prod_left_unit that(1)
        by auto
      ultimately show ?thesis by simp
    qed
    also have "\<dots> = ((mat_of_cols d [vec_of_onb_enum a] 
                    * mat_of_rows d [conjugate (vec_of_onb_enum a)])) $$ (i, j)" (is "?lhs = ?rhs")
    proof-
      have "?rhs = scalar_prod (Matrix.row (mat_of_cols d [vec_of_onb_enum a]) i) 
                   (Matrix.col (mat_of_rows d [conjugate (vec_of_onb_enum a)]) j)"
        apply (subst index_mult_mat)
        using \<open>j < d\<close> \<open>i < d\<close> by auto
      also have "\<dots> = Matrix.row (mat_of_cols d [vec_of_onb_enum a]) i $ 0 *
                 Matrix.col (mat_of_rows d [conjugate (vec_of_onb_enum a)]) j $ 0"
        unfolding scalar_prod_def
        apply (subgoal_tac "dim_vec (col (mat_of_rows d [conjugate (vec_of_onb_enum a)]) j) = 1")
        by auto
      also have "\<dots> = mat_of_cols d [vec_of_onb_enum a] $$ (i, 0) *
                 mat_of_rows d [conjugate (vec_of_onb_enum a)] $$ (0, j)"
        apply (subst index_row) using \<open>i < d\<close> apply auto[2]
        apply (subst index_col) using \<open>j < d\<close> by auto
      also have "\<dots> = vec_of_onb_enum a $ i * conjugate (vec_of_onb_enum a) $ j"
        apply (subst mat_of_cols_Cons_index_0) using \<open>i < d\<close> apply simp
        apply (subst mat_of_rows_index) using \<open>j < d\<close> by auto
      also have "\<dots> = vec_of_onb_enum a $ i * cnj (vec_of_onb_enum a $ j)"
        apply (subst vec_index_conjugate) using \<open>j < d\<close> apply auto
        by (simp add: assms(1) canonical_basis_length_eq dim_vec_of_onb_enum_list')
      finally show ?thesis
        by simp
    qed     
    have "\<langle>a, (canonical_basis::'a list) ! j\<rangle> * cnj \<langle>a, (canonical_basis::'a list) ! i\<rangle>
        = ((mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)])) 
      $$ (i, j)"
      using \<open>\<langle>a, basis ! j\<rangle> * cnj \<langle>a, basis ! i\<rangle> = unit_vec d j \<bullet>c vec_of_onb_enum a * cnj 
      (unit_vec d i \<bullet>c vec_of_onb_enum a)\<close> \<open>vec_of_onb_enum a $ i * cnj (vec_of_onb_enum a $ j)
       = (mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)]) 
      $$ (i, j)\<close> basis_def calculation by auto
    have x1: "proj a *\<^sub>V (canonical_basis::'a list) ! j = 
         (\<langle>a, (canonical_basis::'a list) ! j\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
      using projection_singleton[where a = a and u = "(canonical_basis::'a list)!j"] False
      apply transfer
      by (simp add: span_finite_dim)
    have x2: "(mat_of_cblinfun (proj a)) $$ (i, j) =
        \<langle>(canonical_basis::'a list) ! i, 
          proj a *\<^sub>V (canonical_basis::'a list) ! j\<rangle>"
      unfolding mat_of_cblinfun_def
      using d_def that(1) that(2) by auto
    have x3: "\<langle>(canonical_basis::'a list) ! i, 
          proj a *\<^sub>V (canonical_basis::'a list) ! j\<rangle> =
        \<langle>(canonical_basis::'a list) ! i, 
          (\<langle>a, (canonical_basis::'a list) ! j\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a\<rangle>"
      using x1 x2 by simp
    have x4: "(mat_of_cblinfun (proj a)) $$ (i, j)
          = \<langle>(canonical_basis::'a list) ! i, a\<rangle>*\<langle>a, (canonical_basis::'a list) ! j\<rangle>/norm2"
      using  x2 x3
      by (simp add: norm2a)
    have y1:"(mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)]) 
          $$ (i, j) = \<langle>(canonical_basis::'a list) ! i, a\<rangle>*\<langle>a, (canonical_basis::'a list) ! j\<rangle>"
      by (metis \<open>\<langle>a, canonical_basis ! j\<rangle> * cnj \<langle>a, canonical_basis ! i\<rangle> = (mat_of_cols d 
          [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)]) $$ (i, j)\<close> 
          cinner_commute' ordered_field_class.sign_simps(46))      
    have "(mat_of_cblinfun (proj a)) $$ (i, j)
          = ((mat_of_cols d [vec_of_onb_enum a]
           * mat_of_rows d [conjugate (vec_of_onb_enum a)])$$(i,j))/norm2"
      using y1 x4
      by simp      
    moreover have "((mat_of_cols d [vec_of_onb_enum a]
           * mat_of_rows d [conjugate (vec_of_onb_enum a)])$$(i,j))/norm2 = (1/norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a]
           * mat_of_rows d [conjugate (vec_of_onb_enum a)]))$$(i,j)"
    proof-
      have "p * (M $$ (i,j)) = (p \<cdot>\<^sub>m M) $$ (i,j)"
        if "M \<in> carrier_mat d d" and "i < d" and "j < d"
        for p::complex and  M::"complex mat" and i j::nat
        using that(1) that(2) that(3) by auto        
      moreover have f1: "mat_of_cols d [vec_of_onb_enum a]
           * mat_of_rows d [conjugate (vec_of_onb_enum a)] \<in> carrier_mat d d"
        by (simp add: f1)        
      ultimately show ?thesis
        by (metis mult.left_neutral that(1) that(2) times_divide_eq_left)            
    qed
    ultimately show ?thesis
      by simp
  qed  
  ultimately show ?thesis
    by auto 
qed

lemma mat_of_cblinfun_proj':
  fixes a b::"'a::{onb_enum, chilbert_space}" 
  defines "u == vec_of_onb_enum a"
    and "v == vec_of_onb_enum b"
    and "norm2 == vec_of_onb_enum a \<bullet>c vec_of_onb_enum a"
  shows   "mat_of_cblinfun (proj a) *\<^sub>v v = (v \<bullet>c u) / norm2 \<cdot>\<^sub>v u"
proof-
  define d where "d = canonical_basis_length TYPE('a)"
  have udim: "dim_vec u = d"
    unfolding u_def d_def
    by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list') 
  have vdim: "dim_vec v = d"
    unfolding v_def d_def
    by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list') 
  have "dim_col (mat_of_cols d [u]) = 1"
    by auto
  hence x1: "row (mat_of_cols d [u]) i $ 0 = u $ i"
    if "i < d"
    for i
    unfolding row_def mat_of_cols_def using that by auto
  have "dim_row (mat_of_rows d [conjugate u]) = 1"
    by auto  
  hence x3: "col (mat_of_rows d [conjugate u]) j $ 0 = cnj (u $ j)"
    if "j < d"
    for j
    unfolding col_def mat_of_rows_def using that
    by (simp add: udim)
  have "row (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k $ l = cnj (u $ l) * u $ k"
    if "k < d" and "l < d"
    for k l    
    by (simp add: that)    
  hence "row (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k $ l * v $ l =
        v $ l * cnj (u $ l) * u $ k"
    if "k < d" and "l < d"
    for k l
    by (simp add: that)
  moreover have "(\<And> k. k < d \<Longrightarrow> f k = g k) \<Longrightarrow> (\<Sum>k = 0..<d. f k) =  (\<Sum>k = 0..<d. g k)"
    for f g::"nat \<Rightarrow> complex"
    by auto    
  ultimately have "(\<Sum>l = 0..<d. row (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k $ l * v $ l) =
         (\<Sum>l = 0..<d. v $ l * cnj (u $ l) * u $ k)"
    if "k < d" 
    for k
    using that by presburger    
  hence "(\<Sum>i = 0..<d.
        row (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k $ i * v $ i) =
        (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) * u $ k"
    if "k < d"
    for k
    by (metis (mono_tags, lifting) sum.cong that vector_space_over_itself.scale_sum_left)    
  hence "scalar_prod (row (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k) v
      = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) * (u $ k)"
    if "k < d"
    for k
    unfolding scalar_prod_def vdim 
    apply auto                 
    using \<open>\<And>k. k < d \<Longrightarrow> (\<Sum>i = 0..<d. Matrix.row (Matrix.mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k
     $ i * v $ i) = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) * u $ k\<close> that by blast
  hence "mat d d (\<lambda>(i, j). u $ i * cnj (u $ j)) *\<^sub>v v = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) \<cdot>\<^sub>v u"
    unfolding mult_mat_vec_def apply auto
    by (smt \<open>\<And>k. k < d \<Longrightarrow> scalar_prod (row (Matrix.mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k) v = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) * u $ k\<close> dim_vec eq_vecI index_smult_vec(1) index_smult_vec(2) index_vec udim) 
  moreover have "mat d d (\<lambda>(i, j). row (mat_of_cols d [u]) i $ 0
                                 * col (mat_of_rows d [conjugate u]) j $ 0)
      = mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))"
  proof-
    have "(mat d d (\<lambda>(i, j). row (mat_of_cols d [u]) i $ 0
        * col (mat_of_rows d [conjugate u]) j $ 0)) $$ (i, j)
        = (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) $$ (i, j)"
      if "i < d" and "j < d"
      for i j
    proof-
      have "(mat d d (\<lambda>(i, j). row (mat_of_cols d [u]) i $ 0
        * col (mat_of_rows d [conjugate u]) j $ 0)) $$ (i, j)
       = row (mat_of_cols d [u]) i $ 0 * col (mat_of_rows d [conjugate u]) j $ 0"
        by (simp add: that)        
      moreover have "(mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) $$ (i, j) =  u $ i * cnj (u $ j)"
        by (simp add: that)        
      ultimately show ?thesis
        using x1 x3 that
        by auto
    qed
    thus ?thesis 
      by auto
  qed
  ultimately have "mat d d
     (\<lambda>(i, j). row (mat_of_cols d [u]) i $ 0 * col (mat_of_rows d [conjugate u]) j $ 0) *\<^sub>v
    v = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) \<cdot>\<^sub>v u"
    by simp
  hence "(mat_of_cols d [u] * mat_of_rows d [conjugate u]) *\<^sub>v v = (v \<bullet>c u) \<cdot>\<^sub>v u"
    unfolding times_mat_def scalar_prod_def apply auto
    using udim by blast
  moreover have "1 / norm2 \<cdot>\<^sub>m
      (mat_of_cols d [vec_of_onb_enum a] *
       mat_of_rows d [conjugate (vec_of_onb_enum a)]) *\<^sub>v v =
       1 / norm2 \<cdot>\<^sub>v
      ((mat_of_cols d [vec_of_onb_enum a] *
       mat_of_rows d [conjugate (vec_of_onb_enum a)]) *\<^sub>v v)"
  proof-
    have "mat_of_cols d [vec_of_onb_enum a] *
       mat_of_rows d [conjugate (vec_of_onb_enum a)] \<in> carrier_mat d d"
      unfolding d_def
      by (simp add: carrier_matI) 
    moreover have "v \<in> carrier_vec d"
      unfolding d_def v_def
      using carrier_vecI d_def v_def vdim by auto
    ultimately show ?thesis 
      using mult_mat_vec by auto
  qed
  ultimately have "1 / norm2 \<cdot>\<^sub>m
      (mat_of_cols d [vec_of_onb_enum a] *
       mat_of_rows d [conjugate (vec_of_onb_enum a)]) *\<^sub>v v =
       1 / norm2 \<cdot>\<^sub>v (v \<bullet>c u \<cdot>\<^sub>v u)"
    by (simp add: u_def)    
  hence "1 / norm2 \<cdot>\<^sub>m
      (mat_of_cols d [vec_of_onb_enum a] *
       mat_of_rows d [conjugate (vec_of_onb_enum a)]) *\<^sub>v v =
       v \<bullet>c u / norm2 \<cdot>\<^sub>v u"
    by auto
  thus ?thesis
    unfolding d_def norm2_def mat_of_cblinfun_proj[where 'a = 'a and a = a].
qed


lemma is_ortho_set_corthogonal:
  fixes S :: "'a::onb_enum list"
  defines  "R == map vec_of_onb_enum S"
  assumes a1: "is_ortho_set (set S)" and a2: "distinct S"
    and a3: "0 \<notin> set S" (* TODO: redundant assumption *)
  shows    "corthogonal R"
proof-
  have x1: "R ! i \<bullet>c R ! j = \<langle>S ! j, S ! i\<rangle>"
    if b1: "i < length R"
      and b2: "j < length R"
    for i j
    by (metis Bounded_Operators_Matrices.cinner_ell2_code R_def b1 b2 length_map nth_map)     
  have "R ! i \<bullet>c R ! j = 0"
    if b1: "i < length R"
      and b2: "j < length R"
      and b3: "i \<noteq> j"
    for i j 
  proof-
    have "S ! i \<in> set S"
      using R_def b1 by auto
    moreover have "S ! j \<in> set S"
      using R_def b2 by auto      
    moreover have "S ! j \<noteq> S ! i"
      using that a2 R_def nth_eq_iff_index_eq by auto
    ultimately have "\<langle>S ! j, S ! i\<rangle> = 0"
      using a1 unfolding is_ortho_set_def by blast
    thus ?thesis
      by (simp add: b1 b2 x1) 
  qed
  moreover have "i \<noteq> j"
    if b1: "i < length R"
      and b2: "j < length R"
      and b3: "R ! i \<bullet>c R ! j = 0"
    for i j 
  proof(rule ccontr)
    assume c1: "\<not> i \<noteq> j"
    hence  "i = j" by blast
    have "S ! i \<in> set S"
      using R_def b1 by auto
    have "S ! j \<in> set S"
      using R_def b2 by auto      
    have "S ! j = S ! i"
      using c1 by auto            
    hence "\<langle>S ! j, S ! i\<rangle> \<noteq> 0"
      using \<open>S ! i \<in> set S\<close> a3 by auto
    hence "R ! i \<bullet>c R ! j \<noteq> 0"
      using b2 c1 x1 by auto
    thus False using that(3) by blast
  qed
  ultimately show ?thesis by blast
qed

lemma corthogonal_is_ortho_set:
  fixes vs :: "'a::onb_enum list"
  assumes "corthogonal (map vec_of_onb_enum vs)"
  shows "is_ortho_set (set vs)"
proof (unfold is_ortho_set_def, intro conjI ballI impI)
  fix x y :: 'a
  assume "x \<in> set vs"
  then have "vec_of_onb_enum x \<bullet>c vec_of_onb_enum x \<noteq> 0"
    using assms unfolding corthogonal_def apply auto
    by (metis in_set_conv_nth)
  then have "\<langle>x, x\<rangle> \<noteq> 0"
    apply (subst cinner_ell2_code)
    by simp
  then show "x \<noteq> 0"
    by auto

  assume "y \<in> set vs" and "x \<noteq> y"
  then have "vec_of_onb_enum x \<bullet>c vec_of_onb_enum y = 0"
    using assms \<open>x \<in> set vs\<close> unfolding corthogonal_def apply auto
    by (metis in_set_conv_nth)
  then show "\<langle>x, y\<rangle> = 0"
    apply (subst cinner_ell2_code)
    by (metis cinner_commute cinner_ell2_code conjugate_complex_def conjugate_zero)
qed

(* TODO remove? *)
(* lemma exists_map_vec_of_onb_enum:
  fixes S::"'a::onb_enum list"
  defines "d \<equiv> canonical_basis_length TYPE('a)"
  shows "\<exists>S'::'a list. map vec_of_onb_enum S' = gram_schmidt0 d (map vec_of_onb_enum S)
        \<and> is_ortho_set (set S') \<and> distinct S'"
proof-
  define R where "R = map vec_of_onb_enum S"
  define S'::"'a list" where 
    "S' = map (onb_enum_of_vec::complex vec \<Rightarrow> 'a) (gram_schmidt0 d R)"
  have "dim_vec (vec_of_onb_enum x) = d"
    if "x \<in> set S"
    for x::'a
    unfolding d_def
    by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list')
  hence "set R \<subseteq> carrier_vec d"
    unfolding R_def d_def
    using carrier_vecI by auto 
  hence "LinearCombinations.module.span class_ring
  (module_vec TYPE(complex) d) (set R) =
  LinearCombinations.module.span class_ring
  (module_vec TYPE(complex) d) (set (gram_schmidt0 d R))"
    using Bounded_Operators_Code.cof_vec_space.gram_schmidt0_result(4)[where ws = R and n = d] 
    by blast
  have "map vec_of_onb_enum S' = map (vec_of_onb_enum::'a \<Rightarrow> complex vec) 
       (map (onb_enum_of_vec::complex vec \<Rightarrow> 'a) (gram_schmidt0 d (map vec_of_onb_enum S)))"
    unfolding S'_def R_def by blast
  also have "\<dots> =  
       (map ((vec_of_onb_enum::'a \<Rightarrow> complex vec) \<circ> (onb_enum_of_vec::complex vec \<Rightarrow> 'a)) 
       (gram_schmidt0 d (map vec_of_onb_enum S)))"
    by simp
  also have "\<dots> =  
       (map id (gram_schmidt0 d (map vec_of_onb_enum S)))"
    by (smt R_def \<open>set R \<subseteq> carrier_vec d\<close> carrier_vecD cof_vec_space.gram_schmidt0_result(1) 
        comp_apply d_def id_apply map_eq_conv subset_code(1) vec_of_onb_enum_inverse)
  also have "\<dots> = (gram_schmidt0 d (map vec_of_onb_enum S))"
    by simp
  finally have "map vec_of_onb_enum S' = gram_schmidt0 d (map vec_of_onb_enum S)". 
  moreover have "is_ortho_set (set S')"
    unfolding is_ortho_set_def
  proof auto
    show "x \<in> set S' \<Longrightarrow> y \<in> set S' \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<langle>x, y\<rangle> = 0"
      for x y
    proof-
      assume xs: "x \<in> set S'" and ys: "y \<in> set S'" and xy: "x \<noteq> y"
      have "\<exists>xx. x = (onb_enum_of_vec::complex vec \<Rightarrow> 'a) xx \<and> 
              xx \<in> set (gram_schmidt0 d R)"
        using xs unfolding S'_def by auto
      then obtain xx where xx_def: "x = (onb_enum_of_vec::complex vec \<Rightarrow> 'a) xx"
        and "xx \<in> set (gram_schmidt0 d R)"
        by blast
      have "\<exists>yy. y = (onb_enum_of_vec::complex vec \<Rightarrow> 'a) yy \<and> 
              yy \<in> set (gram_schmidt0 d R)"
        using ys unfolding S'_def by auto
      then obtain yy where yy_def: "y = (onb_enum_of_vec::complex vec \<Rightarrow> 'a) yy" 
        and "yy \<in> set (gram_schmidt0 d R)"
        by blast
      have "xx \<noteq> yy"
        using xy
        using \<open>x = onb_enum_of_vec xx\<close> \<open>y = onb_enum_of_vec yy\<close> by auto
      hence "yy \<bullet>c xx = 0"
      proof-
        have "set (gram_schmidt0 d R) \<subseteq> carrier_vec d"
          by (simp add: \<open>set R \<subseteq> carrier_vec d\<close> cof_vec_space.gram_schmidt0_result(1))        
        hence "corthogonal (gram_schmidt0 d (gram_schmidt0 d R))"
          using Bounded_Operators_Code.cof_vec_space.gram_schmidt0_result(3)
          by auto
        thus ?thesis
          unfolding corthogonal_def
          by (metis \<open>set R \<subseteq> carrier_vec d\<close> \<open>xx \<in> set (gram_schmidt0 d R)\<close> \<open>xx \<noteq> yy\<close> 
              \<open>yy \<in> set (gram_schmidt0 d R)\<close> cof_vec_space.gram_schmidt0_result(3) corthogonalD 
              in_set_conv_nth) 
      qed
      thus "\<langle>x, y\<rangle> = 0"
        using Bounded_Operators_Matrices.cinner_onb_enum_of_vec[where x = xx and y = yy]
          xx_def yy_def 
        by (smt \<open>set R \<subseteq> carrier_vec d\<close> \<open>xx \<in> set (gram_schmidt0 d R)\<close> \<open>yy \<in> set (gram_schmidt0 d R)\<close> 
            carrier_vecD cof_vec_space.gram_schmidt0_result(1) d_def subset_code(1)) 
    qed
    show False
      if "0 \<in> set S'"
      using that unfolding S'_def
    proof auto
      fix x::"complex vec"
      assume a1: "onb_enum_of_vec x = (0::'a)" and
        a2: "x \<in> set (gram_schmidt0 d R)" 
      have "vec_of_onb_enum (onb_enum_of_vec x ::'a) = vec_of_onb_enum (0::'a)"
        using a1 unfolding d_def by simp
      moreover have "vec_of_onb_enum (onb_enum_of_vec x ::'a) = x"
        by (metis \<open>set R \<subseteq> carrier_vec d\<close> a2 carrier_vecD cof_vec_space.gram_schmidt0_result(1) 
            d_def in_mono vec_of_onb_enum_inverse)        
      moreover have "vec_of_onb_enum (0::'a) = 0\<^sub>v d"
        by (simp add: d_def vec_of_onb_enum_zero)        
      ultimately have t1: "x = 0\<^sub>v d"
        by simp    
      have "set R \<subseteq> carrier_vec d"
        unfolding d_def
        using \<open>set R \<subseteq> carrier_vec d\<close> d_def by auto 
      hence "corthogonal (gram_schmidt0 d R)"
        using Bounded_Operators_Code.cof_vec_space.gram_schmidt0_result(3)
        by auto
      hence t2: "0\<^sub>v d \<notin> set (gram_schmidt0 d R)"
        unfolding corthogonal_def apply auto
        by (metis conjugate_square_eq_0_vec in_set_conv_nth zero_carrier_vec)
      show False using t1 t2 a2 by blast
    qed
  qed
  moreover have "distinct S'"
    unfolding S'_def R_def
    by (metis R_def S'_def \<open>set R \<subseteq> carrier_vec d\<close> calculation(1) 
        cof_vec_space.gram_schmidt0_result(2) distinct_map)    
  ultimately show ?thesis by auto
qed *)


(* fun nonzero_vec :: "(complex vec) list \<Rightarrow> (complex vec) list"
  where "nonzero_vec [] =  []"
  | "nonzero_vec (x#xs) = (if vec_is_zero (dim_vec x) x then xs else x#(nonzero_vec xs))" *)


lemma gram_schmidt0_corthogonal:
  assumes a1: "corthogonal R" 
    and a2: "\<And>x. x \<in> set R \<Longrightarrow> dim_vec x = d"
  shows "gram_schmidt0 d R = rev R"
proof -
  have "gram_schmidt_sub0 d U R = rev R @ U"
    if "corthogonal ((rev U) @ R)"
      and "\<And>x. x \<in> set U \<union> set R \<Longrightarrow> dim_vec x = d" for U
  proof (insert that, induction R arbitrary: U)
    case Nil
    show ?case 
      by auto
  next
    case (Cons a R)
    have "a \<in> set (rev U @ a # R)"
      by simp      
    moreover have uar: "corthogonal (rev U @ a # R)"
      by (simp add: Cons.prems(1))      
    ultimately have \<open>a \<noteq> 0\<^sub>v d\<close>
      unfolding corthogonal_def
      by (metis conjugate_zero_vec in_set_conv_nth scalar_prod_right_zero zero_carrier_vec)
    then have nonzero_a: "\<not> vec_is_zero d a"
      by (simp add: Cons.prems(2) vec_is_zero)
    define T where "T = rev U @ a # R"
    have "T ! length (rev U) = a"
      unfolding T_def
      by (meson nth_append_length) 
    moreover have "(T ! i \<bullet>c T ! j = 0) = (i \<noteq> j)"
      if "i<length T"
        and "j<length T"
      for i j
      using uar 
      unfolding corthogonal_def T_def
      apply auto
      using T_def that(2) apply auto[1]
      using T_def that(1) that(2) by auto     
    moreover have "length (rev U) < length T"
      by (simp add: T_def)
    ultimately have "(T ! (length (rev U)) \<bullet>c T ! j = 0) = (length (rev U) \<noteq> j)"
      if "j<length T"
      for j
      using that by blast    
    hence "T ! (length (rev U)) \<bullet>c T ! j = 0"
      if  "j<length T"
        and "j \<noteq> length (rev U)"
      for j
      using that(1) that(2) by blast
    hence "a \<bullet>c T ! j = 0"
      if   "j < length (rev U)"
      for j
      using \<open>T ! length (rev U) = a\<close> that(1)
        \<open>length (rev U) < length T\<close> dual_order.strict_trans by blast
    moreover have "T ! j = (rev U) ! j"
      if   "j < length (rev U)"
      for j
      by (smt T_def \<open>length (rev U) < length T\<close> dual_order.strict_trans list_update_append1
          list_update_id nth_list_update_eq that)
    ultimately have "a \<bullet>c u = 0"
      if "u \<in> set (rev U)"
      for u
      by (metis in_set_conv_nth that)
    hence "a \<bullet>c u = 0"
      if "u \<in> set U"
      for u
      by (simp add: that)
    moreover have "\<And>x. x \<in> set U \<Longrightarrow> dim_vec x = d"
      by (simp add: Cons.prems(2))      
    ultimately have "adjuster d a U = 0\<^sub>v d"
    proof(induction U)
      case Nil
      then show ?case by simp
    next
      case (Cons u U)
      moreover have "0 \<cdot>\<^sub>v u + 0\<^sub>v d = 0\<^sub>v d"
      proof-
        have "dim_vec u = d"
          by (simp add: calculation(3))          
        thus ?thesis
          by auto 
      qed
      ultimately show ?case by auto
    qed
    hence adjuster_a: "adjuster d a U + a = a"
      by (simp add: Cons.prems(2) carrier_vecI)      
    have "gram_schmidt_sub0 d U (a # R) = gram_schmidt_sub0 d (a # U) R"
      by (simp add: adjuster_a nonzero_a)
    also have "\<dots> = rev (a # R) @ U"
      apply (subst Cons.IH)
      using Cons.prems by simp_all
    finally show ?case
      by -
  qed
  from this[where U="[]"] show ?thesis
    unfolding gram_schmidt0_def using assms by auto
qed


(* (* TODO: probably remove in favor of Span_onb_enum_gram_schmidt0 *)
lemma Span_rev_gram_schmidt_sub0:
  defines "d==canonical_basis_length TYPE('a::onb_enum)"
    and "onb_of_vec == (onb_enum_of_vec::_\<Rightarrow>'a)"
  assumes a4: "set R \<subseteq> carrier_vec d"
    and  a5: "set T \<subseteq> carrier_vec d"
  shows "Span (set (map onb_of_vec (rev (gram_schmidt_sub0 d T R))))
       = Span (set (map onb_of_vec (T @ R)))"
  using assms
proof(induction R arbitrary: T)
  case Nil
  thus ?case by auto
next
  case (Cons a R)
  define w' where "w' = adjuster d a T + a"
  show ?case 
  proof (cases "vec_is_zero d w'")
    case True
    have "Span (onb_of_vec ` set (gram_schmidt_sub0 d T R)) =
    Span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
      using Cons(5) Cons(1) Cons.prems(1) d_def onb_of_vec_def by auto
    have "finite (onb_of_vec ` set (gram_schmidt_sub0 d T R))"
      by simp      
    hence "space_as_set (Span (onb_of_vec ` set (gram_schmidt_sub0 d T R)))
        = complex_span (onb_of_vec ` set (gram_schmidt_sub0 d T R))"
      apply transfer
      using span_finite_dim by blast
    have "finite (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
      by simp
    hence "space_as_set (Span (onb_of_vec ` set T \<union> onb_of_vec ` set R))
        = complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
      apply transfer
      using span_finite_dim by blast
    have "complex_span (onb_of_vec ` set (gram_schmidt_sub0 d T R)) =
          complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
      using \<open>Span (onb_of_vec ` set (gram_schmidt_sub0 d T R)) = Span (onb_of_vec ` set T 
      \<union> onb_of_vec ` set R)\<close> \<open>space_as_set (Span (onb_of_vec ` set (gram_schmidt_sub0 d T R)))
     = complex_span (onb_of_vec ` set (gram_schmidt_sub0 d T R))\<close> \<open>space_as_set (Span (
      onb_of_vec ` set T \<union> onb_of_vec ` set R)) = complex_span (onb_of_vec ` set T \<union> 
      onb_of_vec ` set R)\<close> by auto
    moreover have "onb_of_vec a \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
    proof-
      have "w' = 0\<^sub>v d"
        using True
        unfolding d_def
        by (metis Cons.prems(1) carrier_vecD d_def index_add_vec(2) list.set_intros(1) subsetD 
            vec_is_zero w'_def)
      moreover have "dim_vec a = d"
        by (metis calculation index_add_vec(2) index_zero_vec(2) w'_def)        
      moreover have "dim_vec (adjuster d a T) = d"
      proof(induction T)
        case Nil
        show ?case by auto
      next
        case (Cons a T)
        thus ?case by auto
      qed
      ultimately have "a = - adjuster d a T"
        unfolding  w'_def
        by (metis carrier_vecI comm_add_vec minus_add_minus_vec minus_cancel_vec minus_zero_vec 
            zero_minus_vec)  
      hence "onb_of_vec a = onb_of_vec (- adjuster d a T)"
        by simp
      moreover have "onb_of_vec (- adjuster d a T) = - onb_of_vec (adjuster d a T)"
        using onb_enum_of_vec_mult \<open>dim_vec (adjuster d a T) = d\<close>
        unfolding onb_of_vec_def d_def
        by (metis canonical_basis_length_eq scaleC_minus1_left scaleC_minus1_left_vec)
      ultimately have "onb_of_vec a = - onb_of_vec (adjuster d a T)"
        by simp
      moreover have "onb_of_vec (adjuster d a T)
            \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        using Cons(5)
      proof(induction T)
        case Nil
        have "onb_of_vec (0\<^sub>v d) = 0"
          by (metis d_def onb_enum_of_vec_inverse onb_of_vec_def vec_of_onb_enum_zero)                    
        thus ?case apply auto
          using complex_vector.span_zero by auto
      next
        case (Cons u T)
        have u_dim: "dim_vec u = length (canonical_basis::'a list)"
          using Cons.prems canonical_basis_length_eq d_def by auto

        have "onb_of_vec u
        \<in> complex_span (insert (onb_of_vec u) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
          by (simp add: complex_vector.span_base)          
        moreover have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u)
              = (- (a \<bullet>c u / (u \<bullet>c u))) *\<^sub>C (onb_of_vec u)"
          using u_dim onb_enum_of_vec_mult onb_of_vec_def
          by (simp add: onb_enum_of_vec_mult canonical_basis_length_eq)
        ultimately have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u)
        \<in> complex_span (insert (onb_of_vec u) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
          by (metis complex_vector.span_scale)          
        moreover have "onb_of_vec (adjuster d a T)
        \<in> complex_span (insert (onb_of_vec u) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
          by (metis Cons.IH Cons.prems complex_vector.span_mono insert_subset list.simps(15) 
              mk_disjoint_insert subset_insertI)          
        ultimately have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) + onb_of_vec (adjuster d a T)
        \<in> complex_span (insert (onb_of_vec u) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
          using complex_vector.span_add_eq2 by blast
        moreover have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) + onb_of_vec (adjuster d a T)
            = onb_of_vec ( (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) + (adjuster d a T) )"
        proof-
          have "dim_vec  (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) = d"
            using Cons.prems by auto            
          moreover have "dim_vec  (adjuster d a T) = d"
          proof(induction T)
            case Nil
            thus ?case by auto
          next
            case (Cons a T)
            thus ?case by auto
          qed
          ultimately show ?thesis
            
            (* by (simp add: onb_enum_of_vec_add onb_of_vec_def u_dim)  *)
        qed
        ultimately show ?case by auto
      qed
      ultimately show ?thesis
        by (simp add: complex_vector.span_neg) 
    qed
    ultimately have "complex_span (onb_of_vec ` set (gram_schmidt_sub0 d T R)) =
          complex_span (insert (onb_of_vec a) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
      using complex_vector.span_redundant by blast      
    hence "Span (onb_of_vec ` set (gram_schmidt_sub0 d T R)) =
    Span (insert (onb_of_vec a) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
      apply transfer
      by simp
    thus ?thesis using True
      by (simp add: w'_def) 
  next
    case False
    have x1: "finite (insert (onb_of_vec a) 
                                (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
      by auto
    have u1: "x \<in> space_as_set (Span (onb_of_vec ` set (w' # T) \<union> onb_of_vec ` set R))" 
      if "x \<in> space_as_set (Span (insert (onb_of_vec a) 
                                (onb_of_vec ` set T \<union> onb_of_vec ` set R)))"
      for x
    proof-
      have x0: "x \<in> complex_span (insert (onb_of_vec a) 
                                (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
        using that x1 closed_finite_dim
        by (simp add: Span.rep_eq span_finite_dim)
      have u1_1:"dim_vec (adjuster d a T) = length (canonical_basis::'a list)"
      proof(induction T)
        case Nil
        thus ?case
          by (simp add: canonical_basis_length_eq d_def) 
      next
        case (Cons u T)
        thus ?case by auto
      qed
      have "a \<in> carrier_vec d"
        using Cons
        by auto
      hence u1_2:"dim_vec a = length (canonical_basis::'a list)"
        using canonical_basis_length_eq unfolding d_def by auto

      have "\<exists>k. x - k*\<^sub>C (onb_of_vec a) \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        using x0
        using complex_vector.span_breakdown_eq by blast 
      then obtain k where 
        k_def: "x - k *\<^sub>C (onb_of_vec a) \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        by blast
      have "onb_of_vec (adjuster d a T)
            \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        using Cons(5)
      proof(induction T)
        case Nil
        have "onb_of_vec (0\<^sub>v d) = 0"
          by (metis \<open>a \<in> carrier_vec d\<close> add_cancel_right_right canonical_basis_length_eq d_def index_zero_vec(2) onb_enum_of_vec_add onb_of_vec_def right_zero_vec u1_2)          
        thus ?case apply auto
          using complex_vector.span_zero by auto
      next
        case (Cons u T)
        have u_dim: "dim_vec u = length (canonical_basis::'a list)"
          using Cons.prems canonical_basis_length_eq d_def by auto

        have "onb_of_vec u
        \<in> complex_span (insert (onb_of_vec u) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
          by (simp add: complex_vector.span_base)          
        moreover have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u)
              = (- (a \<bullet>c u / (u \<bullet>c u))) *\<^sub>C (onb_of_vec u)"
          using u_dim onb_enum_of_vec_mult onb_of_vec_def 
            
          (* by blast  *)
        ultimately have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u)
        \<in> complex_span (insert (onb_of_vec u) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
          by (metis complex_vector.span_scale)          
        moreover have "onb_of_vec (adjuster d a T)
        \<in> complex_span (insert (onb_of_vec u) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
          by (metis Cons.IH Cons.prems complex_vector.span_mono insert_subset list.simps(15) 
              mk_disjoint_insert subset_insertI)          
        ultimately have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) + onb_of_vec (adjuster d a T)
        \<in> complex_span (insert (onb_of_vec u) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
          using complex_vector.span_add_eq2 by blast
        moreover have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) + onb_of_vec (adjuster d a T)
            = onb_of_vec ( (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) + (adjuster d a T) )"
        proof-
          have "dim_vec  (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) = d"
            using Cons.prems by auto            
          moreover have "dim_vec  (adjuster d a T) = d"
          proof(induction T)
            case Nil
            thus ?case by auto
          next
            case (Cons a T)
            thus ?case by auto
          qed
          ultimately show ?thesis
            by (simp add: Cons.hyps(2) onb_enum_of_vec_add onb_of_vec_def)
        qed
        ultimately show ?case by auto
      qed
      hence "x - k *\<^sub>C (onb_of_vec a) - k *\<^sub>C (onb_of_vec (adjuster d a T))
            \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        using complex_vector.span_diff complex_vector.span_scale k_def by blast
      hence "x - k *\<^sub>C (onb_of_vec (adjuster d a T)) - k *\<^sub>C (onb_of_vec a)
            \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        by (simp add: cancel_ab_semigroup_add_class.diff_right_commute)
      hence "x - k *\<^sub>C ((onb_of_vec (adjuster d a T)) + (onb_of_vec a))
            \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        by (simp add: linordered_field_class.sign_simps(7) scaleC_add_right)
      hence "x - k *\<^sub>C onb_of_vec w'
            \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        unfolding w'_def
        using u1_1 u1_2 onb_enum_of_vec_add
        by (simp add: onb_enum_of_vec_add canonical_basis_length_eq onb_of_vec_def)
      hence "x \<in> complex_span (insert (onb_of_vec w') (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
        using complex_vector.span_breakdown_eq by blast
      hence "x \<in> complex_span (onb_of_vec ` set (w' # T) \<union> onb_of_vec ` set R)"
        unfolding w'_def
        by simp        
      thus ?thesis apply transfer
        using closure_subset by blast
    qed
    moreover have v1: "x \<in> space_as_set (Span (insert (onb_of_vec a) 
                                (onb_of_vec ` set T \<union> onb_of_vec ` set R)))" 
      if  "x \<in> space_as_set (Span (onb_of_vec ` set (w' # T) \<union> onb_of_vec ` set R))"
      for x
    proof-
      have "finite (onb_of_vec ` set (w' # T) \<union> onb_of_vec ` set R)"
        by auto
      hence "x \<in> complex_span (onb_of_vec ` set (w' # T) \<union> onb_of_vec ` set R)"
        using that  apply transfer using closed_finite_dim
        by (simp add: span_finite_dim)
      hence "x \<in> complex_span (insert (onb_of_vec w') 
                                (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
        by simp
      hence "\<exists>k. x - k *\<^sub>C onb_of_vec w' \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        using complex_vector.span_breakdown_eq by blast
      then obtain k where 
        "x - k *\<^sub>C onb_of_vec w' \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        by blast
      hence "x - k *\<^sub>C onb_of_vec (adjuster d a T + a) \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        unfolding w'_def by blast
      moreover have "k *\<^sub>C onb_of_vec (adjuster d a T + a)
          = k *\<^sub>C onb_of_vec (adjuster d a T) + k *\<^sub>C onb_of_vec a"
      proof-
        have "dim_vec a = d"
          using Cons.prems(1) by auto          
        moreover have "dim_vec (adjuster d a T) = d"
        proof(induction T)
          case Nil
          then show ?case by auto
        next
          case (Cons u T)
          then show ?case by auto
        qed
        ultimately have "onb_of_vec (adjuster d a T + a)
            = onb_of_vec (adjuster d a T) + onb_of_vec a"
          by (metis d_def onb_enum_of_vec_inverse onb_of_vec_def vec_of_onb_enum_add 
              vec_of_onb_enum_inverse)          
        thus ?thesis
          by (simp add: scaleC_add_right) 
      qed
      ultimately have "x - k *\<^sub>C onb_of_vec (adjuster d a T) - k *\<^sub>C onb_of_vec a
         \<in> complex_span (onb_of_vec ` set T \<union> onb_of_vec ` set R)"
        by (simp add: diff_diff_add)
      hence "x - k *\<^sub>C onb_of_vec (adjuster d a T) 
         \<in> complex_span (insert (onb_of_vec a) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
        using complex_vector.span_breakdown_eq by blast
      moreover have "onb_of_vec (adjuster d a T) 
         \<in> complex_span (insert (onb_of_vec a) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
        using Cons(5)
      proof(induction T)
        case Nil
        have "onb_of_vec (adjuster d a []) = 0"
          apply auto
          by (metis d_def onb_enum_of_vec_inverse onb_of_vec_def vec_of_onb_enum_zero)
        thus ?case
          by (simp add: complex_vector.span_zero) 
      next
        case (Cons u T)
        have "dim_vec u = d"
          using Cons.prems by auto          
        hence q1: "dim_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) = d"
          by simp          
        have q2: "dim_vec (adjuster d a T) = d"
        proof(induction T)
          case Nil
          thus ?case by auto
        next
          case (Cons a T)
          thus ?case by auto
        qed

        have "onb_of_vec u
              \<in> complex_span (insert (onb_of_vec a) (insert (onb_of_vec u) 
              (onb_of_vec ` set T \<union> onb_of_vec ` set R)))"
          by (simp add: complex_vector.span_base)          
        moreover have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u)
                    = (- (a \<bullet>c u / (u \<bullet>c u))) *\<^sub>C onb_of_vec u"
        proof-
          have "dim_vec u = canonical_basis_length TYPE('a)"
            by (simp add: \<open>dim_vec u = d\<close> d_def)            
          thus ?thesis
            using onb_enum_of_vec_mult
            by (simp add: onb_enum_of_vec_mult canonical_basis_length_eq onb_of_vec_def)            
        qed
        ultimately have s1: "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u)
              \<in> complex_span (insert (onb_of_vec a) (insert (onb_of_vec u) 
              (onb_of_vec ` set T \<union> onb_of_vec ` set R)))"
          by (metis complex_vector.span_scale)
        have "set T \<subseteq> carrier_vec d"
          using Cons(2) by auto
        hence s2: "onb_of_vec (adjuster d a T)
              \<in> complex_span (insert (onb_of_vec a) (insert (onb_of_vec u) 
              (onb_of_vec ` set T \<union> onb_of_vec ` set R)))"          
        proof(induction T)
          case Nil
          have "onb_of_vec (adjuster d a []) = 0"
            apply auto
            by (metis d_def onb_enum_of_vec_inverse onb_of_vec_def vec_of_onb_enum_zero)
          thus ?case
            by (simp add: complex_vector.span_zero) 
        next
          case (Cons v T)
          have "set T \<subseteq> carrier_vec d"
            using Cons.prems by auto
          hence "onb_of_vec (adjuster d a T)
            \<in> complex_span (insert (onb_of_vec a) (insert (onb_of_vec u) 
                              (onb_of_vec ` set T \<union> onb_of_vec ` set R)))"
            using Cons.IH by blast
          moreover have "insert (onb_of_vec a) (insert (onb_of_vec u) 
                              (onb_of_vec ` set T \<union> onb_of_vec ` set R))
          \<subseteq> (insert (onb_of_vec a)
             (insert (onb_of_vec u) (insert (onb_of_vec v)
             (onb_of_vec ` set T \<union> onb_of_vec ` set R))))"
            by blast            
          ultimately have "onb_of_vec (adjuster d a T)
            \<in> complex_span (insert (onb_of_vec a)
             (insert (onb_of_vec u) (insert (onb_of_vec v)
             (onb_of_vec ` set T \<union> onb_of_vec ` set R))))"
            by (metis (no_types, lifting) complex_vector.span_mono insert_subset mk_disjoint_insert)            
          moreover have "onb_of_vec (- (a \<bullet>c v / (v \<bullet>c v)) \<cdot>\<^sub>v v)
          \<in> complex_span (insert (onb_of_vec a)
             (insert (onb_of_vec u) (insert (onb_of_vec v)
             (onb_of_vec ` set T \<union> onb_of_vec ` set R))))"
          proof-
            have "onb_of_vec v
          \<in> complex_span (insert (onb_of_vec a) (insert (onb_of_vec u)
            (insert (onb_of_vec v) (onb_of_vec ` set T \<union> onb_of_vec ` set R))))"
              by (simp add: complex_vector.span_base)              
            moreover have "onb_of_vec (- (a \<bullet>c v / (v \<bullet>c v)) \<cdot>\<^sub>v v)
                          = (- (a \<bullet>c v / (v \<bullet>c v))) *\<^sub>C (onb_of_vec v)"
            proof-
              have "dim_vec v = d"
                using Cons.prems by auto                
              thus ?thesis unfolding d_def
                by (metis onb_enum_of_vec_inverse onb_of_vec_def vec_of_onb_enum_inverse 
                    vec_of_onb_enum_scaleC) 
            qed
            ultimately show ?thesis
              by (metis complex_vector.span_scale) 
          qed
          ultimately have  "onb_of_vec (- (a \<bullet>c v / (v \<bullet>c v)) \<cdot>\<^sub>v v) + onb_of_vec (adjuster d a T)
          \<in> complex_span (insert (onb_of_vec a) (insert (onb_of_vec u)
            (insert (onb_of_vec v) (onb_of_vec ` set T \<union> onb_of_vec ` set R))))"
            using Complex_Vector_Spaces.complex_vector.span_add[where S = "insert (onb_of_vec a)
             (insert (onb_of_vec u) (insert (onb_of_vec v)
             (onb_of_vec ` set T \<union> onb_of_vec ` set R)))"
                and x = "onb_of_vec (- (a \<bullet>c v / (v \<bullet>c v)) \<cdot>\<^sub>v v)"
                and y = "onb_of_vec (adjuster d a T)"]            
            by auto
          moreover have "onb_of_vec (- (a \<bullet>c v / (v \<bullet>c v)) \<cdot>\<^sub>v v + adjuster d a T)
                = onb_of_vec (- (a \<bullet>c v / (v \<bullet>c v)) \<cdot>\<^sub>v v) + onb_of_vec (adjuster d a T)"
          proof-
            have "dim_vec v = d"
              using Cons.prems by auto              
            hence "dim_vec (- (a \<bullet>c v / (v \<bullet>c v)) \<cdot>\<^sub>v v) = d"
              by auto
            moreover have "dim_vec (adjuster d a T) = d"
            proof(induction T)
              case Nil
              thus ?case by auto
            next
              case (Cons f T)
              thus ?case by auto
            qed
            ultimately show ?thesis unfolding onb_of_vec_def
              using onb_enum_of_vec_add unfolding d_def
              by (simp add: onb_enum_of_vec_add canonical_basis_length_eq) 
          qed
          ultimately show ?case by auto
        qed          

        have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) + onb_of_vec (adjuster d a T)
              \<in> complex_span (insert (onb_of_vec a) (insert (onb_of_vec u) 
              (onb_of_vec ` set T \<union> onb_of_vec ` set R)))"
          using s1 s2 complex_vector.span_add by blast 
        moreover have "onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u + (adjuster d a T))
                     = onb_of_vec (- (a \<bullet>c u / (u \<bullet>c u)) \<cdot>\<^sub>v u) + onb_of_vec (adjuster d a T)"
          using q1 q2 onb_enum_of_vec_add unfolding onb_of_vec_def d_def
          by (simp add: onb_enum_of_vec_add canonical_basis_length_eq)
        ultimately show ?case by auto
      qed
      ultimately have "x \<in> complex_span (insert (onb_of_vec a) 
                                (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
        by (metis complex_vector.span_add complex_vector.span_scale diff_add_cancel)        
      thus ?thesis apply transfer
        by (simp add: span_finite_dim)
    qed
    ultimately have w1: "space_as_set (Span (onb_of_vec ` set (w' # T) \<union> onb_of_vec ` set R)) =
    space_as_set (Span (insert (onb_of_vec a) (onb_of_vec ` set T \<union> onb_of_vec ` set R)))"
      by blast
    have "set R \<subseteq> carrier_vec d"
      using Cons
      by auto
    moreover have "set (w'#T) \<subseteq> carrier_vec d"
    proof-
      have "a \<in> carrier_vec d"
        using Cons.prems(1) by auto        
      moreover have "adjuster d a T \<in> carrier_vec d"
      proof(induction T)
        case Nil
        then show ?case by auto
      next
        case (Cons u T)
        then show ?case apply auto
          using carrier_dim_vec by fastforce
      qed
      ultimately have "w' \<in> carrier_vec d"
        unfolding w'_def
        by auto
      moreover have "set T \<subseteq> carrier_vec d"
        using Cons
        by auto
      ultimately show ?thesis by simp
    qed
    ultimately have "Span (onb_of_vec ` set (gram_schmidt_sub0 d (w' # T) R)) =
          Span (onb_of_vec ` set (w' # T) \<union> onb_of_vec ` set R)"
      using Cons by auto
    also have "\<dots> = Span (insert (onb_of_vec a) (onb_of_vec ` set T \<union> onb_of_vec ` set R))"
      using w1 apply auto
      using space_as_set_inject by auto
    finally have "Span (onb_of_vec ` set (gram_schmidt_sub0 d (w' # T) R)) =
                  Span (insert (onb_of_vec a) (onb_of_vec ` set T \<union> onb_of_vec ` set R))".
    thus ?thesis using False
      by (simp add: w'_def)
  qed
qed *)


(* (* TODO: probably remove in favor of Span_onb_enum_gram_schmidt0 *)
lemma Span_map_vec_of_onb_enum:
  fixes S S' :: "'a::onb_enum list"
  defines "R == map vec_of_onb_enum S"
    and "R' == map vec_of_onb_enum S'"
    and "d == canonical_basis_length TYPE('a)"
  assumes a1: "gram_schmidt0 d R = rev R'"
  shows "Span (set S) = Span (set S')"
proof- (* NEW *)
  define onb_of_vec where "onb_of_vec = (onb_enum_of_vec::_\<Rightarrow>'a)"

  have "map onb_of_vec R = S"
    unfolding R_def onb_of_vec_def apply auto
    by (simp add: map_idI)

  have "R' = rev (gram_schmidt0 d R)"
    using a1
    by simp

  have "map onb_of_vec (rev (gram_schmidt_sub0  d [] R)) =
        map onb_of_vec (rev (rev R'))"
    using a1
    unfolding gram_schmidt0_def
    by simp
  also have "\<dots> = map onb_of_vec  R'"
    by auto
  also have "\<dots> = S'"
    unfolding R'_def onb_of_vec_def
    apply auto 
    by (simp add: map_idI )
  finally have "map onb_of_vec (rev (gram_schmidt_sub0  d [] R)) = S'".
  have "dim_vec r = d" 
    if "r \<in> set R"
    for r
  proof-
    have "\<exists>s\<in>set S. r = vec_of_onb_enum s"
      using R_def that by auto
    then obtain s where "s\<in>set S" and "r = vec_of_onb_enum s"
      by blast
    have "dim_vec r = dim_vec (vec_of_onb_enum s)"
      by (simp add: \<open>r = vec_of_onb_enum s\<close>)
    also have "\<dots> = d"
      unfolding d_def
      by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list') 
    finally have "dim_vec r = d".
    thus ?thesis
      using that
      unfolding d_def R_def
      by auto
  qed
  hence "set R \<subseteq> carrier_vec d"
    unfolding d_def R_def
    using carrier_dim_vec by blast 
  moreover have "set [] \<subseteq> carrier_vec d"
    by auto
  ultimately have "Span  (set (map onb_of_vec (rev (gram_schmidt_sub0  d [] R)))) =
        Span (set (map onb_of_vec ([] @ R)))"
    unfolding onb_of_vec_def
    using Span_rev_gram_schmidt_sub0[where T = "[]" and R = R and 'a = 'a]
      d_def by blast    
  hence "Span  (set (map onb_of_vec (rev (gram_schmidt_sub0  d [] R)))) =
         Span (set (map onb_of_vec R))"
    by auto
  hence "Span  (set (map onb_of_vec (rev (gram_schmidt_sub0  d [] R)))) = Span (set S)"
    using \<open>map onb_of_vec R = S\<close> by blast
  hence "Span  (set S') = Span (set S)"
    using \<open>map onb_of_vec (rev (gram_schmidt_sub0 d [] R)) = S'\<close> by auto
  thus ?thesis
    by simp 
qed *)

instantiation complex :: basis_enum begin
definition "canonical_basis = [1::complex]"
definition "canonical_basis_length (_::complex itself) = 1"
instance
  apply intro_classes
  unfolding canonical_basis_complex_def canonical_basis_length_complex_def
  by (auto simp add: Complex_Vector_Spaces.span_raw_def vector_space_over_itself.span_Basis)
end

instance complex :: one_dim
  apply intro_classes
  unfolding canonical_basis_complex_def is_ortho_set_def
  by auto

definition butterfly_def': "butterfly (s::'a::chilbert_space)
   = vector_to_cblinfun s o\<^sub>C\<^sub>L (vector_to_cblinfun s :: complex \<Rightarrow>\<^sub>C\<^sub>L _)*"

lift_definition one_dim_isom :: "'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'b::one_dim" is
  "\<lambda>a. of_complex (one_dim_to_complex a)"
  apply (rule cbounded_linear_intro[where K=1])
  apply (auto simp: one_dim_to_complex_def cinner_add_right)
  apply (simp add: scaleC_conv_of_complex)
  by (smt cinner_scaleC_left complex_to_one_dim_inverse norm_eq_sqrt_cinner of_complex_def one_dim_1_times_a_eq_a)

lemma one_dim_isom_inverse[simp]: "one_dim_isom o\<^sub>C\<^sub>L one_dim_isom = idOp"
  by (transfer, rule ext, simp)

lemma one_dim_isom_adj[simp]: "one_dim_isom* = one_dim_isom"
  apply (rule adjoint_D[symmetric])
  apply transfer
  by (simp add: of_complex_def one_dim_to_complex_def)


lemma one_dim_isom_vector_to_cblinfun: 
  "(vector_to_cblinfun s :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L _) o\<^sub>C\<^sub>L one_dim_isom = (vector_to_cblinfun s :: 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)"
  by (transfer fixing: s, auto)



lemma butterfly_def: "butterfly s = (vector_to_cblinfun s :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)
                                 o\<^sub>C\<^sub>L (vector_to_cblinfun s :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)*"
    (is "_ = ?rhs")
proof -
  let ?isoAC = "one_dim_isom :: 'a \<Rightarrow>\<^sub>C\<^sub>L complex"
  let ?isoCA = "one_dim_isom :: complex \<Rightarrow>\<^sub>C\<^sub>L 'a"

  have "butterfly s =
    (vector_to_cblinfun s o\<^sub>C\<^sub>L ?isoCA) o\<^sub>C\<^sub>L (vector_to_cblinfun s o\<^sub>C\<^sub>L ?isoCA)*"
    unfolding butterfly_def' one_dim_isom_vector_to_cblinfun by simp
  also have "\<dots> = vector_to_cblinfun s o\<^sub>C\<^sub>L (?isoCA o\<^sub>C\<^sub>L ?isoCA*) o\<^sub>C\<^sub>L (vector_to_cblinfun s)*"
    by (simp add: timesOp_assoc del: one_dim_isom_adj)
  also have "\<dots> = ?rhs"
    by simp
  finally show ?thesis
    by simp
qed

lemma butterfly_apply: "butterfly \<psi> *\<^sub>V \<phi> = \<langle>\<psi>, \<phi>\<rangle> *\<^sub>C \<psi>"
  apply (subst butterfly_def)
  by (simp add: times_applyOp)

lemma vector_to_cblinfun_0[simp]: "vector_to_cblinfun 0 = 0"
  apply transfer by simp

lemma butterfly_0[simp]: "butterfly 0 = 0"
  apply (subst butterfly_def)
  by simp

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
  then show "b \<in> range (\<lambda>x. norm (f x) / norm x)"
    by auto
next
  fix y 
  assume "y \<in> range (\<lambda>x. norm (f x) / norm x)"
  then obtain x where y_def: "y = norm (f x) / norm x"
    by auto
  then show "y \<le> b"
    unfolding y_def using assms(1)[of x]
    by (metis assms(2) assms(3) divide_eq_0_iff linordered_field_class.pos_divide_le_eq norm_ge_zero norm_zero zero_less_norm_iff)
qed


lemma norm_butterfly: "norm (butterfly \<psi>) = norm \<psi> ^ 2"
proof (cases "\<psi>=0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis 
    unfolding norm_cblinfun.rep_eq
  proof (rule onormI[OF _ False])
    fix x 
    show "norm (butterfly \<psi> *\<^sub>V x) \<le> (norm \<psi>)\<^sup>2 * norm x"
      apply (simp add: butterfly_apply power2_eq_square)
      using norm_cauchy_schwarz[of \<psi> x]
      by (simp add: linordered_field_class.sign_simps(25) mult_left_mono ordered_field_class.sign_simps(5))
    show "norm (butterfly \<psi> *\<^sub>V \<psi>) = (norm \<psi>)\<^sup>2 * norm \<psi>"
      apply (simp add: butterfly_apply power2_eq_square)
      by (simp add: power2_norm_eq_cinner semiring_normalization_rules(29))
  qed
qed

lemma butterfly_scaleC: "butterfly (c *\<^sub>C \<psi>) = abs c ^ 2 *\<^sub>C butterfly \<psi>"
  unfolding butterfly_def' vector_to_cblinfun_scalar_times scalar_times_adj
  by (simp add: cnj_x_x)

lemma butterfly_scaleR: "butterfly (r *\<^sub>R \<psi>) = r ^ 2 *\<^sub>R butterfly \<psi>"
  unfolding scaleR_scaleC butterfly_scaleC power2_abs cnj_x_x[symmetric]
  unfolding power2_eq_square
  by auto

lemma inj_butterfly: 
  assumes "butterfly x = butterfly y"
  shows "\<exists>c. cmod c = 1 \<and> x = c *\<^sub>C y"
proof (cases "x = 0")
  case True
  from assms have "y = 0"
    using norm_butterfly
    by (metis True norm_eq_zero zero_less_power2)
  with True show ?thesis
    apply (rule_tac exI[of _ 1])
    by auto
next
  case False
  define c where "c = \<langle>y, x\<rangle> / \<langle>x, x\<rangle>"
  have "\<langle>x, x\<rangle> *\<^sub>C x = butterfly x *\<^sub>V x"
    by (simp add: butterfly_apply)
  also have "\<dots> = butterfly y *\<^sub>V x"
    using assms by simp
  also have "\<dots> = \<langle>y, x\<rangle> *\<^sub>C y"
    by (simp add: butterfly_apply)
  finally have xcy: "x = c *\<^sub>C y"
    by (simp add: c_def Complex_Vector_Spaces.eq_vector_fraction_iff)
  have "cmod c * norm x = cmod c * norm y"
    using assms norm_butterfly
    by (metis norm_eq_sqrt_cinner power2_norm_eq_cinner) 
  also have "cmod c * norm y = norm (c *\<^sub>C y)"
    by simp
  also have "\<dots> = norm x"
    unfolding xcy[symmetric] by simp
  finally have c: "cmod c = 1"
    by (simp add: False)
  from c xcy show ?thesis
    by auto
qed

lemma isometry_vector_to_cblinfun:
  assumes "norm x = 1"
  shows "isometry (vector_to_cblinfun x)"
  by (simp add: isometry_def cinner_norm_sq assms)

lemma image_vector_to_cblinfun[simp]: "vector_to_cblinfun x *\<^sub>S top = Span {x}"
  apply transfer
  apply (rule arg_cong[where f=closure])
  unfolding complex_vector.span_singleton
  apply auto
  by (smt UNIV_I complex_scaleC_def image_iff mult.right_neutral one_dim_to_complex_one one_dim_to_complex_scaleC)


lemma butterfly_proj:
  assumes "norm x = 1"
  shows "butterfly x = proj x"
proof -
  define B and \<phi> :: "complex \<Rightarrow>\<^sub>C\<^sub>L 'a"
    where "B = butterfly x" and "\<phi> = vector_to_cblinfun x"
  then have B: "B = \<phi> o\<^sub>C\<^sub>L \<phi>*"
    unfolding butterfly_def' by simp
  have \<phi>adj\<phi>: "\<phi>* o\<^sub>C\<^sub>L \<phi> = idOp"
    by (simp add: \<phi>_def cinner_norm_sq assms)
  have "B o\<^sub>C\<^sub>L B = \<phi> o\<^sub>C\<^sub>L (\<phi>* o\<^sub>C\<^sub>L \<phi>) o\<^sub>C\<^sub>L \<phi>*"
    unfolding B timesOp_assoc by rule
  also have "\<dots> = B"
    unfolding \<phi>adj\<phi> by (simp add: B)
  finally have idem: "B o\<^sub>C\<^sub>L B = B"
    by -
  have herm: "B = B*"
    unfolding B by simp
  from idem herm have BProj: "B = Proj (B *\<^sub>S top)"
    by (rule Proj_I)

  have "B *\<^sub>S top = Span {x}"
    unfolding B timesOp_assoc_subspace 
    by (simp add: \<phi>_def isometry_vector_to_cblinfun assms range_adjoint_isometry)

  with BProj show "B = proj x"
    by simp
qed


(* TODO: Move to the Complex_Vector_Spaces *)
lemma Span_empty[simp]: "Span {} = bot"
  apply transfer
  by simp

lemma Proj_bot[simp]: "Proj bot = 0"
  by (metis Bounded_Operators.timesScalarSpace_0 Proj_I imageOp_Proj isProjector0 isProjector_algebraic zero_clinear_space_def)

lemma mat_of_cblinfun_Proj_Span_aux_1:
  fixes S :: "'a::onb_enum list"
  defines "d == canonical_basis_length TYPE('a)"
  assumes ortho: "is_ortho_set (set S)" and distinct: "distinct S"
  shows "mk_projector_orthog d (map vec_of_onb_enum S) = mk_projector (Span (set S))"
proof -
  define Snorm where "Snorm = map (\<lambda>s. s /\<^sub>R norm s) S"
  
  have "distinct Snorm"
  proof (insert ortho distinct, unfold Snorm_def, induction S)
    case Nil
    show ?case by simp
  next
    case (Cons s S)
    then have "is_ortho_set (set S)" and "distinct S"
      unfolding is_ortho_set_def by auto
    note IH = Cons.IH[OF this]
    have "s /\<^sub>R norm s \<notin> (\<lambda>s. s /\<^sub>R norm s) ` set S"
    proof auto
      fix s' assume "s' \<in> set S" and same: "s /\<^sub>R norm s = s' /\<^sub>R norm s'"
      with Cons.prems have "s \<noteq> s'" by auto
      have "s \<noteq> 0"
        by (metis Cons.prems(1) is_ortho_set_def list.set_intros(1))
      then have "0 \<noteq> \<langle>s /\<^sub>R norm s, s /\<^sub>R norm s\<rangle>"
        by simp
      also have \<open>\<langle>s /\<^sub>R norm s, s /\<^sub>R norm s\<rangle> = \<langle>s /\<^sub>R norm s, s' /\<^sub>R norm s'\<rangle>\<close>
        by (simp add: same)
      also have \<open>\<langle>s /\<^sub>R norm s, s' /\<^sub>R norm s'\<rangle> = \<langle>s, s'\<rangle> / (norm s * norm s')\<close>
        by (simp add: scaleR_scaleC divide_inverse_commute)
      also from \<open>s' \<in> set S\<close> \<open>s \<noteq> s'\<close> have "\<dots> = 0"
        using Cons.prems unfolding is_ortho_set_def by simp
      finally show False
        by simp
    qed
    then show ?case
      using IH by simp
  qed

  have norm_Snorm: "norm s = 1" if "s \<in> set Snorm" for s
    using that ortho unfolding Snorm_def is_ortho_set_def by auto

  have ortho_Snorm: "is_ortho_set (set Snorm)"
    unfolding is_ortho_set_def
  proof (intro conjI ballI impI)
    fix x y
    show "x \<in> set Snorm \<Longrightarrow> x \<noteq> 0"
      using norm_Snorm[of 0] by auto
    assume "x \<in> set Snorm" and "y \<in> set Snorm" and "x \<noteq> y"
    from \<open>x \<in> set Snorm\<close>
    obtain x' where x: "x = x' /\<^sub>R norm x'" and x': "x' \<in> set S"
      unfolding Snorm_def by auto
    from \<open>y \<in> set Snorm\<close>
    obtain y' where y: "y = y' /\<^sub>R norm y'" and y': "y' \<in> set S"
      unfolding Snorm_def by auto
    from \<open>x \<noteq> y\<close> x y have \<open>x' \<noteq> y'\<close> by auto
    with x' y' ortho have "cinner x' y' = 0"
      unfolding is_ortho_set_def by auto
    then show "cinner x y = 0"
      unfolding x y scaleR_scaleC by auto
  qed

  have inj_butter: "inj_on butterfly (set Snorm)"
  proof (rule inj_onI)
    fix x y 
    assume "x \<in> set Snorm" and "y \<in> set Snorm"
    assume "butterfly x = butterfly y"
    then obtain c where xcy: "x = c *\<^sub>C y" and "cmod c = 1"
      using inj_butterfly by auto
    have "0 \<noteq> cmod (cinner x x)"
      using \<open>x \<in> set Snorm\<close> norm_Snorm
      by (simp add: cinner_norm_sq)
    also have "cmod (cinner x x) = cmod (c * \<langle>x, y\<rangle>)"
      apply (subst (2) xcy) by simp
    also have "\<dots> = cmod \<langle>x, y\<rangle>"
      using \<open>cmod c = 1\<close> by (simp add: norm_mult)
    finally have "\<langle>x, y\<rangle> \<noteq> 0"
      by simp
    then show "x = y"
      using ortho_Snorm \<open>x \<in> set Snorm\<close> \<open>y \<in> set Snorm\<close>
      unfolding is_ortho_set_def by auto
  qed

  from \<open>distinct Snorm\<close> inj_butter
  have distinct': "distinct (map butterfly Snorm)"
    unfolding distinct_map by simp

  have Span_Snorm: "Span (set Snorm) = Span (set S)"
    apply (transfer fixing: Snorm S)
    apply (simp add: scaleR_scaleC Snorm_def)
    apply (subst span_image_scale) 
    using is_ortho_set_def ortho by fastforce+

  have "mk_projector_orthog d (map vec_of_onb_enum S)
      = mat_of_cblinfun (sum_list (map butterfly Snorm))"
    unfolding Snorm_def
  proof (induction S)
    case Nil
    show ?case 
      by (simp add: d_def mat_of_cblinfun_zero')
  next
    case (Cons a S)
    define sumS where "sumS = sum_list (map butterfly (map (\<lambda>s. s /\<^sub>R norm s) S))"
    with Cons have IH: "mk_projector_orthog d (map vec_of_onb_enum S)
                  = mat_of_cblinfun sumS"
      by simp

    define factor where "factor = inverse ((complex_of_real (norm a))\<^sup>2)"
    have factor': "factor = 1 / (vec_of_onb_enum a \<bullet>c vec_of_onb_enum a)"
      unfolding factor_def cinner_ell2_code[symmetric]
      by (simp add: inverse_eq_divide power2_norm_eq_cinner'')

    have "mk_projector_orthog d (map vec_of_onb_enum (a # S))
          = factor \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a] 
                    * mat_of_rows d [conjugate (vec_of_onb_enum a)])
            + mat_of_cblinfun sumS"
      apply (cases S)
       apply (auto simp add: factor' sumS_def d_def mat_of_cblinfun_zero')[1]
      by (auto simp add: IH[symmetric] factor' d_def)

    also have "\<dots> = factor \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a] *
         adjoint_mat (mat_of_cols d [vec_of_onb_enum a])) + mat_of_cblinfun sumS"
      apply (rule arg_cong[where f="\<lambda>x. _ \<cdot>\<^sub>m (_ * x) + _"])
      apply (rule mat_eq_iff[THEN iffD2])
        apply (auto simp add: adjoint_mat_def)
      apply (subst mat_of_rows_index)
        apply auto
      apply (subst mat_of_cols_index)
        apply auto
      by (simp add: assms(1) canonical_basis_length_eq dim_vec_of_onb_enum_list')

    also have "\<dots> = mat_of_cblinfun (butterfly (a /\<^sub>R norm a)) + mat_of_cblinfun sumS"
      apply (simp add: butterfly_scaleR power_inverse mat_of_cblinfun_scaleR factor_def)
      by (simp add: butterfly_def' cblinfun_of_mat_timesOp
          cblinfun_of_mat_adjoint mat_of_cblinfun_ell2_to_l2bounded d_def)

    finally show ?case
      by (simp add: cblinfun_of_mat_plusOp' sumS_def)
  qed
  also have "\<dots> = mat_of_cblinfun (\<Sum>s\<in>set Snorm. butterfly s)"
    by (metis distinct' distinct_map sum.distinct_set_conv_list)
  also have "\<dots> = mat_of_cblinfun (\<Sum>s\<in>set Snorm. proj s)"
    apply (rule arg_cong[where f="mat_of_cblinfun"])
    apply (rule sum.cong[OF refl])
    apply (rule butterfly_proj)
    using norm_Snorm by simp
  also have "\<dots> = mat_of_cblinfun (Proj (Span (set Snorm)))"
    apply (rule arg_cong[of _ _ mat_of_cblinfun])
  proof (insert ortho_Snorm, insert \<open>distinct Snorm\<close>, induction Snorm)
    case Nil
    show ?case
      by simp
  next
    case (Cons a Snorm)
    from Cons.prems have [simp]: "a \<notin> set Snorm"
      by simp

    have "sum proj (set (a # Snorm))
        = proj a + sum proj (set Snorm)"
      by auto
    also have "\<dots> = proj a + Proj (Span (set Snorm))"
      apply (subst Cons.IH)
      using Cons.prems apply auto
      using is_onb_delete by blast
    also have "\<dots> = Proj (Span (set (a # Snorm)))"
      apply (rule Proj_Span_insert[symmetric])
      using Cons.prems by auto
    finally show ?case
      by -
  qed
  also have "\<dots> = mk_projector (Span (set S))"
    unfolding mk_projector_def Span_Snorm by simp
  finally show ?thesis
    by -
qed

(* TODO move to ..._Matrices *)
lemma mat_of_cblinfun_Proj_Span: 
  fixes S :: "'a::onb_enum list"
  shows "mat_of_cblinfun (Proj (Span (set S))) =
    (let d = canonical_basis_length TYPE('a) in 
      mk_projector_orthog d (gram_schmidt0 d (map vec_of_onb_enum S)))"
proof-
  define d gs 
    where "d = canonical_basis_length TYPE('a)"
      and "gs = gram_schmidt0 d (map vec_of_onb_enum S)"
  interpret complex_vec_space d.
  have gs_dim: "x \<in> set gs \<Longrightarrow> dim_vec x = d" for x
    by (smt canonical_basis_length_eq carrier_vecD carrier_vec_dim_vec d_def dim_vec_of_onb_enum_list' ex_map_conv gram_schmidt0_result(1) gs_def subset_code(1))
  have ortho_gs: "is_ortho_set (set (map onb_enum_of_vec gs :: 'a list))"
    apply (rule corthogonal_is_ortho_set)
    by (smt canonical_basis_length_eq carrier_dim_vec cof_vec_space.gram_schmidt0_result(1) d_def dim_vec_of_onb_enum_list' gram_schmidt0_result(3) gs_def imageE map_idI map_map o_apply set_map subset_code(1) vec_of_onb_enum_inverse)
  have distinct_gs: "distinct (map onb_enum_of_vec gs :: 'a list)"
    by (metis (mono_tags, hide_lams) canonical_basis_length_eq carrier_vec_dim_vec cof_vec_space.gram_schmidt0_result(2) d_def dim_vec_of_onb_enum_list' distinct_map gs_def gs_dim image_iff inj_on_inverseI set_map subsetI vec_of_onb_enum_inverse)

  have "mk_projector_orthog d gs 
      = mk_projector_orthog d (map vec_of_onb_enum (map onb_enum_of_vec gs :: 'a list))"
    apply simp
    apply (subst map_cong[where ys=gs and g=id], simp)
    using gs_dim by (auto intro!: vec_of_onb_enum_inverse simp: d_def)
  also have "\<dots> = mk_projector (Span (set (map onb_enum_of_vec gs :: 'a list)))"
    unfolding d_def
    apply (subst mat_of_cblinfun_Proj_Span_aux_1)
    using ortho_gs distinct_gs by auto
  also have "\<dots> = mk_projector (Span (set S))"
    apply (rule arg_cong[where f=mk_projector])
    unfolding gs_def d_def
    apply (subst Span_onb_enum_gram_schmidt0)
    by (auto simp add: canonical_basis_length_eq carrier_vecI dim_vec_of_onb_enum_list')
  also have "\<dots> = mat_of_cblinfun (Proj (Span (set S)))"
    unfolding mk_projector_def by simp
  finally show ?thesis
    unfolding d_def gs_def by auto
qed


lemma mk_projector_SPAN[code]: 
  "mk_projector (SPAN S :: 'a::onb_enum clinear_space) = 
    (let d = canonical_basis_length TYPE('a) in mk_projector_orthog d 
              (gram_schmidt0 d (filter (\<lambda>v. dim_vec v = d) S)))"
proof -
  (* note [[show_types, show_consts]] *)
  have *: "map_option vec_of_onb_enum (if dim_vec x = canonical_basis_length TYPE('a) then Some (onb_enum_of_vec x :: 'a) else None)
      = (if dim_vec x = canonical_basis_length TYPE('a) then Some x else None)" for x
    by auto
  show ?thesis
    unfolding mk_projector_def SPAN_def
    using mat_of_cblinfun_Proj_Span[where S = 
        "map onb_enum_of_vec (filter (\<lambda>v. dim_vec v = (canonical_basis_length TYPE('a))) S) :: 'a list"]
    apply (simp only: Let_def map_filter_map_filter filter_set image_set map_map_filter o_def)
    unfolding *
    by (simp add: map_filter_map_filter[symmetric])
qed

lemma [code]: "mat_of_cblinfun (Proj S) = mk_projector S" for S :: "'a::onb_enum clinear_space"
  unfolding mk_projector_def by simp

(* (* TODO move to ..._Matrices *)
definition "orthogonal_complement_vec n vs = 
  (let vs_ortho = gram_schmidt0 n vs in
   map (\<lambda>w. adjuster n w vs_ortho) (unit_vecs n))" *)

(* TODO: move to Preliminaries *)
lemma map_filter_map: "List.map_filter f (map g l) = List.map_filter (f o g) l"
  apply (induction l)
   apply (simp add: map_filter_simps)
  apply auto by (metis map_filter_simps(1))

(* TODO: move to Preliminaries *)
lemma map_filter_Some[simp]: "List.map_filter (\<lambda>x. Some (f x)) l = map f l"
  apply (induction l)
   apply (simp add: map_filter_simps)
  by (simp add: map_filter_simps(1))

(* (* TODO: move to Preliminaries *)
lemma map_filter_Some'[simp]: "List.map_filter (\<lambda>x. if f x then Some x else None) l = filter f l"
  apply (induction l)
   apply (simp add: map_filter_simps)
  by (simp add: map_filter_simps(1)) *)


lemma onb_enum_of_vec_unit_vec: "onb_enum_of_vec (unit_vec (canonical_basis_length TYPE('a)) i)
   = (canonical_basis!i :: 'a::onb_enum)"
  if "i < canonical_basis_length TYPE('a)"
  by (simp add: onb_enum_of_vec_unit_vec that)


(* TODO: Move to Complex_Inner_Product *)
lemma Span_canonical_basis[simp]: "Span (set canonical_basis) = top"
  using Span.rep_eq space_as_set_inject top_clinear_space.rep_eq
    closure_UNIV is_generator_set
  by metis


lemma top_as_span[code]: "(top::'a clinear_space) = 
  (let n = canonical_basis_length TYPE('a::onb_enum) in
    SPAN (unit_vecs n))"
  unfolding SPAN_def
  apply (simp only: index_unit_vec Let_def map_filter_map_filter filter_set image_set map_map_filter 
      map_filter_map o_def unit_vecs_def)
  apply (simp add: onb_enum_of_vec_unit_vec)
  apply (subst nth_image)
  by (auto simp: canonical_basis_length_eq)

lemma bot_as_span[code]: "(bot::'a::onb_enum clinear_space) = SPAN []"
  unfolding SPAN_def by (auto simp: Set.filter_def)

(* TODO: Move to the Complex_Vector_Spaces *)
lemma Span_union: "Span A \<squnion> Span B = Span (A \<union> B)"
proof (transfer, auto)
  have p0: "Complex_Vector_Spaces.span (A \<union> B) = 
      Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B"
    for A B::"'a set"
    using Complex_Vector_Spaces.complex_vector.span_Un
    by (smt Collect_cong set_plus_def)
  hence p1: "closure (Complex_Vector_Spaces.span (A \<union> B)) = 
             closure (Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B)"
    for A B::"'a set"
    by simp

  show "x \<in> closure (Complex_Vector_Spaces.span (A \<union> B))"
    if "x \<in> closure (Complex_Vector_Spaces.span A) +\<^sub>M
            closure (Complex_Vector_Spaces.span B)"
    for x::'a and A B
  proof-
    have "closure (Complex_Vector_Spaces.span A) + closure (Complex_Vector_Spaces.span B) \<subseteq>
          closure (Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B)"
      using Starlike.closure_sum by auto
    hence "closure (Complex_Vector_Spaces.span A) + closure (Complex_Vector_Spaces.span B)
        \<subseteq> closure (Complex_Vector_Spaces.span (A \<union> B))"
      by (metis \<open>closure (Complex_Vector_Spaces.span A) + closure (Complex_Vector_Spaces.span B)
           \<subseteq> closure (Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B)\<close> p1)
    thus ?thesis by (smt closed_sum_def closure_closure closure_mono subsetD that)
  qed

  show "x \<in> closure (Complex_Vector_Spaces.span A) +\<^sub>M
            closure (Complex_Vector_Spaces.span B)"
    if "x \<in> closure (Complex_Vector_Spaces.span (A \<union> B))"
    for x::'a and A B
  proof-
    have "Complex_Vector_Spaces.span (A \<union> B) \<subseteq>
           closure (Complex_Vector_Spaces.span A) +
           closure (Complex_Vector_Spaces.span B)"
      apply auto
      by (metis closure_subset p0 set_plus_mono2_b) 
    hence "closure (Complex_Vector_Spaces.span (A \<union> B)) \<subseteq>
           closure (closure (Complex_Vector_Spaces.span A) +
                    closure (Complex_Vector_Spaces.span B))"
      by (smt closure_mono)
    thus ?thesis by (smt closed_sum_def in_mono that)
  qed
qed


lemma filter_Un: "Set.filter f (x \<union> y) = Set.filter f x \<union> Set.filter f y"
  by (simp add: Int_Un_distrib2 Set_project_code)

lemma sup_spans[code]: "SPAN A \<squnion> SPAN B = SPAN (A @ B)"
  unfolding SPAN_def 
  by (auto simp: Span_union image_Un filter_Un Let_def)

(* lemma orthogonal_complementI:
  assumes "\<And>x y. x \<in> Y \<Longrightarrow> y \<in> X \<Longrightarrow> \<langle>x, y\<rangle> = 0"
  assumes "\<And>x. (\<And>y. y\<in>X \<Longrightarrow> \<langle>x, y\<rangle> = 0) \<Longrightarrow> x \<in> Y"
  shows "orthogonal_complement X = Y"
  unfolding orthogonal_complement_def using assms by auto *)


(* (* TODO move to ..._Matrices *)
(* TODO: Do it differently (using image (1-Proj S)) *)
lemma ortho_Span: 
  fixes S :: "'a::onb_enum list"
  shows "- Span (set S) =
    Span (onb_enum_of_vec ` set (orthogonal_complement_vec 
        (canonical_basis_length TYPE('a)) (map vec_of_onb_enum S)) :: 'a set)"
(* proof (transfer fixing: S)
  let ?onb_enum_of_vec = "onb_enum_of_vec :: _ \<Rightarrow> 'a"
  let ?vec_of_onb_enum = "vec_of_onb_enum :: 'a \<Rightarrow> _"
  define d where "d = (canonical_basis_length TYPE('a))"
  have "orthogonal_complement (closure (complex_span (set S))) =
      orthogonal_complement (complex_span (set S))"
    by (subst span_finite_dim, simp_all)

  have "complex_span
       (?onb_enum_of_vec `
        set (orthogonal_complement_vec d
              (map ?vec_of_onb_enum S))) = orthogonal_complement xxx"
    apply (rule sym)
    apply (rule orthogonal_complementI)

    

  show ?thesis
    
qed *)
   *)

(* TODO To Preliminaries *)
lemma Set_filter_unchanged: "Set.filter P X = X" if "\<And>x. x\<in>X \<Longrightarrow> P x" for P and X :: "'z set"
  by (simp add: Set_project_code subsetI subset_antisym that)


lemma adjuster_carrier': (* List adjuster_carrier but with one assm less *)
  assumes w: "(w :: 'a::conjugatable_field vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
  shows "adjuster n w us \<in> carrier_vec n"
  by (insert us, induction us, auto)

(* (* TODO: Do it differently (using image (1-Proj S)) *)
lemma orthogonal_complement_vec_carrier:
  assumes "set S \<subseteq> carrier_vec d"
  shows "set (orthogonal_complement_vec d S :: 'a::conjugatable_ordered_field vec list) \<subseteq> carrier_vec d"
proof -
  define vs_ortho where "vs_ortho = gram_schmidt0 d S"
  have vs_ortho: "set vs_ortho \<subseteq> carrier_vec d"
    unfolding vs_ortho_def
    using assms by (rule cof_vec_space.gram_schmidt0_result(1))
  have "set (map (\<lambda>w. adjuster d w vs_ortho) (unit_vecs d)) \<subseteq> carrier_vec d"
    apply auto
    apply (rule adjuster_carrier')
    using unit_vecs_carrier vs_ortho by auto
  then show ?thesis
    unfolding orthogonal_complement_vec_def vs_ortho_def by simp
qed *)


(* lemma ortho_SPAN[code]: "- (SPAN S :: 'a::onb_enum clinear_space)
        = (let d = canonical_basis_length TYPE('a) in 
            SPAN (orthogonal_complement_vec d (filter (\<lambda>v. dim_vec v = d) S)))"
proof -
  define d Sd and Sd' :: "'a list"
    where "d = canonical_basis_length TYPE('a)"
      and "Sd = filter (\<lambda>v. dim_vec v = d) S"
      and "Sd' = map onb_enum_of_vec Sd"
  have Sd_Sd': "Sd = map vec_of_onb_enum Sd'"
    unfolding Sd'_def apply auto
    apply (subst map_cong[where g=id, OF refl])
     apply (auto simp: Sd_def)
    by (simp add: d_def)
  have Sd_carrier: "set Sd \<subseteq> carrier_vec d"
    unfolding Sd_def by auto

  have "SPAN (orthogonal_complement_vec d Sd)
      = Span (onb_enum_of_vec ` set (orthogonal_complement_vec d Sd) :: 'a set)"
    unfolding SPAN_def Let_def d_def[symmetric]
    apply (subst Set_filter_unchanged)
    using orthogonal_complement_vec_carrier[OF Sd_carrier]
    by auto
  also have "\<dots> = - Span (set Sd' :: 'a set)"
    by (simp add: ortho_Span d_def Sd_Sd')
  also have "\<dots> = - SPAN S"
    by (simp add: Set.filter_def SPAN_def Sd_def d_def Sd'_def)
  finally show ?thesis
    unfolding d_def[symmetric] Sd_def
    by simp
qed *)

definition [code del,code_abbrev]: "span_code (S::'a::enum ell2 set) = (Span S)"

lemma span_Set_Monad[code]: "span_code (Set_Monad l) = (SPAN (map vec_of_ell2 l))"
  apply (simp add: span_code_def SPAN_def Let_def)
  apply (subst Set_filter_unchanged)
   apply (metis canonical_basis_length_eq dim_vec_of_onb_enum_list' imageE vec_of_ell2_def)
  by (metis (no_types, lifting) ell2_of_vec_def image_image map_idI set_map vec_of_ell2_inverse)

instantiation clinear_space :: (onb_enum) equal begin
definition [code del]: "equal_clinear_space (A::'a clinear_space) B = (A=B)"
instance apply intro_classes unfolding equal_clinear_space_def by simp
end

(* TODO: Move to ..._Matrices *)
definition "is_subspace_of n vs ws = 
  (let ws' = gram_schmidt0 n ws in
     \<forall>v\<in>set vs. adjuster n v vs = - v)"

(* TODO: Move to ..._Matrices *)
lemma Span_leq: "(Span (set A) \<le> Span (set B)) \<longleftrightarrow>
    is_subspace_of (canonical_basis_length TYPE('a::onb_enum)) 
      (map vec_of_onb_enum A) (map vec_of_onb_enum B)"
proof
  define d A' B' 
    where "d = canonical_basis_length TYPE('a)"
      and "A' = gram_schmidt0 d (map vec_of_onb_enum A)"
      and "B' = gram_schmidt0 d (map vec_of_onb_enum B)"
  interpret complex_vec_space d.

  have "Span (set A) \<le> Span (set B) \<longleftrightarrow> complex_span (set A) \<le> complex_span (set B)"
    apply (transfer fixing: A B)
    apply (subst span_finite_dim)
(* TRICKY *)

    thm span_finite_dim
    thm span_finite_dim
  thm adjuster_already_in_span

  show "is_subspace_of (canonical_basis_length (TYPE('a)::'a itself)) 
        (map vec_of_onb_enum A) (map vec_of_onb_enum B)"
    if "Span (set A) \<le> Span (set B)"
  proof -
    from that have "complex_span (set A) \<le> complex_span (set B)"
      apply transfer 
    have "adjuster d v A = - v" if "v \<in> span (set A')"
    sorry
qed
  show "Span (set A) \<le> Span (set B)"
    if "is_subspace_of (canonical_basis_length (TYPE('a)::'a itself)) 
        (map vec_of_onb_enum A) (map vec_of_onb_enum B)"
    sorry
qed

lemma SPAN_leq[code]: "SPAN A \<le> (SPAN B :: 'a::onb_enum clinear_space) 
      \<longleftrightarrow> is_subspace_of (canonical_basis_length TYPE('a)) A B"
  sorry

lemma apply_cblinfun_Span: 
  "A *\<^sub>S Span (set S) = Span (onb_enum_of_vec ` set (map ((*\<^sub>v) (mat_of_cblinfun A)) (map vec_of_onb_enum S)))"
  apply (auto simp: applyOpSpace_Span image_image)
  by (metis mat_of_cblinfun_description onb_enum_of_vec_inverse)

definition [code del, code_abbrev]: "range_cblinfun_code A = A *\<^sub>S top"

lemma Proj_ortho_compl:
  "Proj (- X) = idOp - Proj X"
  apply (transfer, auto)
  using ortho_decomp
  by (metis add_diff_cancel_left') 

lemma Proj_inj: "Proj X = Proj Y \<Longrightarrow> X = Y"
  by (metis imageOp_Proj)

lemma ortho_SPAN_code[code_unfold]: "- X = range_cblinfun_code (idOp - Proj X)"
  unfolding range_cblinfun_code_def
  by (metis Proj_ortho_compl imageOp_Proj)

lemma applyOpSpace_SPAN[code]: "applyOpSpace A (SPAN S)
      = (let d = canonical_basis_length TYPE('a) in
         SPAN (map (mult_mat_vec (mat_of_cblinfun A))
               (filter (\<lambda>v. dim_vec v = d) S)))"
  for A::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum"
proof -
  define dA dB S'
    where "dA = canonical_basis_length TYPE('a)"
      and "dB = canonical_basis_length TYPE('b)"
      and "S' = filter (\<lambda>v. dim_vec v = dA) S"

  have "applyOpSpace A (SPAN S) = A *\<^sub>S Span (set (map onb_enum_of_vec S'))"
    unfolding SPAN_def dA_def[symmetric] Let_def S'_def filter_set
    by simp
  also have "\<dots> = Span ((\<lambda>x. onb_enum_of_vec 
            (mat_of_cblinfun A *\<^sub>v vec_of_onb_enum (onb_enum_of_vec x :: 'a))) ` set S')"
    apply (subst apply_cblinfun_Span)
    by (simp add: image_image)
  also have "\<dots> = Span ((\<lambda>x. onb_enum_of_vec (mat_of_cblinfun A *\<^sub>v x)) ` set S')"
    apply (subst image_cong[OF refl])
     apply (subst vec_of_onb_enum_inverse)
    by (auto simp add: S'_def dA_def)
  also have "\<dots> = SPAN (map (mult_mat_vec (mat_of_cblinfun A)) S')"
    unfolding SPAN_def dB_def[symmetric] Let_def filter_set 
    apply (subst filter_True)
    by (simp_all add: dB_def mat_of_cblinfun_def image_image)

  finally show ?thesis
    unfolding dA_def[symmetric] S'_def[symmetric] Let_def
    by simp
qed

lemma range_cblinfun_code[code]: 
  fixes A :: "'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
  shows "range_cblinfun_code A = SPAN (cols (mat_of_cblinfun A))"
proof -
  define dA dB
    where "dA = canonical_basis_length TYPE('a)"
      and "dB = canonical_basis_length TYPE('b)"
  have carrier_A: "mat_of_cblinfun A \<in> carrier_mat dB dA"
    unfolding mat_of_cblinfun_def dA_def dB_def by simp

  have "range_cblinfun_code A = A *\<^sub>S SPAN (unit_vecs dA)"
    unfolding range_cblinfun_code_def
    by (metis dA_def top_as_span)
  also have "\<dots> = SPAN (map (\<lambda>i. mat_of_cblinfun A *\<^sub>v unit_vec dA i) [0..<dA])"
    unfolding applyOpSpace_SPAN dA_def[symmetric] Let_def
    apply (subst filter_True)
    apply (meson carrier_vecD subset_code(1) unit_vecs_carrier)
    by (simp add: unit_vecs_def o_def)
  also have "\<dots> = SPAN (map (\<lambda>x. mat_of_cblinfun A *\<^sub>v col (1\<^sub>m dA) x) [0..<dA])"
    apply (subst map_cong[OF refl])
    by auto
  also have "\<dots> = SPAN (map (col (mat_of_cblinfun A * 1\<^sub>m dA)) [0..<dA])"
    apply (subst map_cong[OF refl])
    apply (subst col_mult2[symmetric])
    apply (rule carrier_A)
    by auto
  also have "\<dots> = SPAN (cols (mat_of_cblinfun A))"
    unfolding cols_def dA_def[symmetric]
    apply (subst right_mult_one_mat[OF carrier_A])
    using carrier_A by blast
  finally show ?thesis
    by -
qed

lemma kernel_SPAN[code]: "kernel A 
    = SPAN (find_base_vectors (gauss_jordan_single (mat_of_cblinfun A)))" 
  for A::"('a::onb_enum,'b::onb_enum) cblinfun"
  sorry

lemma [code_abbrev]: "kernel (A - a *\<^sub>C idOp) = eigenspace a A" 
  unfolding eigenspace_def by simp

lemma [code]: "HOL.equal (A::_ clinear_space) B = (A\<le>B \<and> B\<le>A)"
  unfolding equal_clinear_space_def by auto

lemma [code]: "(A::'a::onb_enum clinear_space) \<sqinter> B = - (- A \<squnion> - B)"
  by (subst ortho_involution[symmetric], subst compl_inf, simp)

lemma [code]: "Inf (Set_Monad l :: 'a::onb_enum clinear_space set) = fold inf l top"
  unfolding Set_Monad_def
  by (simp add: Inf_set_fold)


subsection \<open>Miscellanea\<close>

text \<open>This is a hack to circumvent a bug in the code generation. The automatically
  generated code for the class \<^class>\<open>uniformity\<close> has a type that is different from
  what the generated code later assumes, leading to compilation errors (in ML at least)
  in any expression involving \<^typ>\<open>_ ell2\<close> (even if the constant \<^const>\<open>uniformity\<close> is
  not actually used).
  
  The fragment below circumvents this by forcing Isabelle to use the right type.
  (The logically useless fragment "\<open>let x = ((=)::'a\<Rightarrow>_\<Rightarrow>_)\<close>" achieves this.)\<close>
lemma [code]: "(uniformity :: ('a ell2 * _) filter) = Filter.abstract_filter (%_.
    Code.abort STR ''no uniformity'' (%_. 
    let x = ((=)::'a\<Rightarrow>_\<Rightarrow>_) in uniformity))"
  by simp

(* TODO explain what for *)
declare [[code drop: UNIV]]
declare enum_class.UNIV_enum[code]

(* TODO explain what for *)
derive (eq) ceq clinear_space
derive (no) ccompare clinear_space
derive (monad) set_impl clinear_space
derive (eq) ceq ell2
derive (no) ccompare ell2
derive (monad) set_impl ell2


unbundle no_jnf_notation
unbundle no_cblinfun_notation

end

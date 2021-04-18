theory Temp
  imports Jordan_Normal_Form_Missing Jordan_Normal_Form.Gram_Schmidt
begin

(* Probably more effecient in code generation than comparing with 0 *)
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
  then have "v \<bullet>c u = 0" if "u \<in> U" for u
    by (metis assms(3) U_def corthogonal_distinct distinct_Ex1 that)
  then have ortho: "u \<bullet>c v = 0" if "u \<in> U" for u
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
  then show "v = 0\<^sub>v n"
    using U_def conjugate_square_eq_0_vec span span_closed us_carrier by blast
qed


(* Following closed Gram_Schmidt.gram_schmidt_sub_result in Jordan_Normal_Form *)
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
    then have "\<not> vec_is_zero n (?v + w)"
      by (simp add: vec_is_zero)
    then have U'def: "gram_schmidt_sub0 n ((?v + w)#us) ws = us'" 
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
    then have "vec_is_zero n (?v + w)"
      by (simp add: vec_is_zero)
    then have U'_def: "us' = gram_schmidt_sub0 n us ws"
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
  then show ?thesis1 ?thesis2 ?thesis3 ?thesis4
    by auto
qed

end

section \<open>TODO: section title\<close>

theory Infinite_Set_Sum_Missing
  imports "HOL-Analysis.Infinite_Set_Sum" Ordered_Complex "HOL-Library.Rewrite" Containers.Containers_Auxiliary
begin



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
    by (metis (mono_tags, lifting) Collect_cong enn2ereal_ennreal fnn in_mono sum_nonneg)
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


end

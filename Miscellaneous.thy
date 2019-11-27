theory Miscellaneous
  imports Complex_Inner_Product 
begin

lemma finite_sum_Cauchy:
  fixes A::\<open>('a::cbanach) set\<close>
  assumes \<open>Cauchy (\<lambda> k. \<Sum>a\<in>A. r k a *\<^sub>C a)\<close> and \<open>finite A\<close> 
    and  \<open>x \<in> A\<close> and \<open>complex_independent A\<close>
  shows \<open>Cauchy (\<lambda> k. r k x)\<close>
  apply (insert assms)
  using \<open>finite A\<close>
(* In case this theorem is needed: A helpful theorem towards this might be 
   finate_span_representation_bounded which essentially shows that
   the map ("representation A") from "\<Sum>a\<in>A. r k a *\<^sub>C a" to "r k x" is bounded (and hence continous)
   on span A. (But there are still many other steps to be done to prove finite_sum_Cauchy.)
*)
  sorry


lemma closed_span_finite_set_LI:
 \<open>complex_independent A \<Longrightarrow> finite A \<Longrightarrow> closed (complex_vector.span A)\<close>
 for A::\<open>('a::cbanach) set\<close>
proof-
  assume \<open>complex_independent A\<close> and \<open>finite A\<close>
  have \<open>complex_vector.span A = {\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> A}\<close>
    using complex_vector.span_explicit[where b = "A"] by blast
  also have \<open>... = {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}\<close>
    by (metis (mono_tags, lifting)  Complex_Inner_Product.span_explicit_finite \<open>finite A\<close>)
  finally have \<open>complex_vector.span A = {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}\<close>
    by blast
  moreover have \<open>closed  {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}\<close>
  proof-
    have \<open>(\<And> n. s n \<in> {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}) \<Longrightarrow> s \<longlonglongrightarrow> l \<Longrightarrow> l \<in> {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}\<close>
      for s l
    proof-
      assume \<open>\<And> n. s n \<in> {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}\<close> and \<open>s \<longlonglongrightarrow> l\<close>
      have \<open>\<exists> r. s n = (\<Sum>a\<in>A. r a *\<^sub>C a)\<close>
        for n
        using \<open>\<And> n. s n \<in> {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}\<close>
        by simp
      hence  \<open>\<exists> r. \<forall> n. s n = (\<Sum>a\<in>A. r n a *\<^sub>C a)\<close>
        by metis
      then obtain r where \<open>\<And> n. s n = (\<Sum>a\<in>A. r n a *\<^sub>C a)\<close>
        by blast
      from  \<open>s \<longlonglongrightarrow> l\<close>
      have \<open>convergent s\<close>
        using convergentI by auto
      hence \<open>Cauchy s\<close>
        by (simp add: Cauchy_convergent_iff)
      hence \<open>Cauchy (\<lambda> k. s k)\<close>
        by auto
      hence \<open>Cauchy (\<lambda> k. (\<Sum>a\<in>A. r k a *\<^sub>C a))\<close>
        using   \<open>\<And> k. s k = (\<Sum>a\<in>A. r k a *\<^sub>C a)\<close>
        by auto
      hence \<open>a \<in> A \<Longrightarrow> Cauchy (\<lambda> n. r n a)\<close>
        for a
        using finite_sum_Cauchy[where A = "A" and r = "r" and x = "a"]
          \<open>complex_independent A\<close> \<open>finite A\<close>
        by auto
      hence \<open>a \<in> A \<Longrightarrow> convergent (\<lambda> n. r n a)\<close>
        for a
        using Cauchy_convergent_iff by auto
      hence \<open>\<forall> a \<in> A. \<exists> \<phi>. (\<lambda> n. r n a) \<longlonglongrightarrow> \<phi>\<close>
        unfolding convergent_def by blast
      hence \<open>\<exists> \<phi>. \<forall> a \<in> A. (\<lambda> n. r n a) \<longlonglongrightarrow> \<phi> a\<close>
        by metis
      then obtain \<phi> where \<open>\<forall> a \<in> A. (\<lambda> n. r n a) \<longlonglongrightarrow> \<phi> a\<close>
        by blast
      hence \<open>(\<lambda> n. (\<Sum>a\<in>A. r n a *\<^sub>C a)) \<longlonglongrightarrow>  (\<Sum>a\<in>A. \<phi> a *\<^sub>C a)\<close>
        using finite_sum_tendsto \<open>finite A\<close>
        by blast
      hence \<open>(\<lambda> n. s n) \<longlonglongrightarrow>  (\<Sum>a\<in>A. \<phi> a *\<^sub>C a)\<close>
        using \<open>\<And> n. s n = (\<Sum>a\<in>A. r n a *\<^sub>C a)\<close>
        by auto
      hence \<open>s \<longlonglongrightarrow>  (\<Sum>a\<in>A. \<phi> a *\<^sub>C a)\<close>
        by blast
      hence \<open>l = (\<Sum>a\<in>A. \<phi> a *\<^sub>C a)\<close>
        using \<open>s \<longlonglongrightarrow> l\<close> LIMSEQ_unique by blast
      moreover have \<open>(\<Sum>a\<in>A. \<phi> a *\<^sub>C a) \<in> {\<Sum>a\<in>A. r a *\<^sub>C a |r. True}\<close>
        by auto        
      ultimately show ?thesis
        by auto
    qed
    thus ?thesis
      using closed_sequential_limits by blast 
  qed
  ultimately show ?thesis by simp
qed

(* TODO move *)
lemma closed_span_finite_set:
 \<open>finite A \<Longrightarrow> closed (complex_vector.span A)\<close>
 for A::\<open>('a::cbanach) set\<close>
proof - (* sledgehammer *)
  assume a1: "finite A"
  obtain AA :: "'a set \<Rightarrow> 'a set" where
    f2: "AA A \<subseteq> A \<and> complex_independent (AA A) \<and> A \<subseteq> complex_vector.span (AA A)"
    by (meson complex_vector.maximal_independent_subset)
  then have f3: "finite (AA A)"
    using a1 by (metis finite_subset)
  have f4: "\<forall>A Aa. (complex_vector.span (A::'a set) = complex_vector.span Aa) = (A \<subseteq> complex_vector.span Aa \<and> Aa \<subseteq> complex_vector.span A)"
    using complex_vector.span_eq by blast
  then have "AA A \<subseteq> complex_vector.span A"
    using f2 by (metis subset_trans)
  then show ?thesis
    using f4 f3 f2 by (metis (full_types) closed_span_finite_set_LI)
qed

(* TODO move *)
lemma closure_span_finite_set:
 \<open>finite A \<Longrightarrow> closure (complex_vector.span A) = complex_vector.span A\<close>
 for A::\<open>('a::cbanach) set\<close>
  using closed_span_finite_set
  by (simp add: closed_span_finite_set) 


end
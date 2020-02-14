section \<open>Results of Real Analysis missing, which are needed for the proof of Banach-Steinhaus 
theorem\<close>

theory Real_Analysis_Missing
  imports 
    "HOL-Analysis.Infinite_Set_Sum"
    General_Results_Missing_Banach_Steinhaus

begin

subsection \<open>Limits of sequences\<close>

lemma lim_shift:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and l::'a and n::nat
  assumes \<open>(\<lambda> k. x (n + k)) \<longlonglongrightarrow> l\<close>
  shows \<open>x \<longlonglongrightarrow> l\<close>
proof-
  have \<open>\<forall> x::nat \<Rightarrow> 'a::real_normed_vector. \<forall> l::'a. ((\<lambda> k. x (n + k)) \<longlonglongrightarrow> l) \<longrightarrow> (x \<longlonglongrightarrow> l)\<close>
  proof(induction n)
    case 0
    thus ?case by simp
  next
    case (Suc n)
    have \<open>(\<lambda>k. x (Suc n + k)) \<longlonglongrightarrow> l \<Longrightarrow> x \<longlonglongrightarrow> l\<close>
      for x::"nat \<Rightarrow> 'a" and l::'a
    proof-
      assume \<open>(\<lambda>k. x (Suc n + k)) \<longlonglongrightarrow> l\<close>
      hence \<open>(\<lambda>k. x (n + Suc k)) \<longlonglongrightarrow> l\<close>
        by simp
      hence \<open>(\<lambda> t. (\<lambda>k. x (n + k)) (Suc t)) \<longlonglongrightarrow> l\<close>
        by simp
      hence \<open>(\<lambda> t. (\<lambda>k. x (n + k)) t) \<longlonglongrightarrow> l\<close>
        by (rule LIMSEQ_imp_Suc)
      hence \<open>(\<lambda>k. x (n + k)) \<longlonglongrightarrow> l\<close>
        by simp
      thus ?thesis 
        by (simp add: \<open>(\<lambda>k. x (n + k)) \<longlonglongrightarrow> l\<close> Suc.IH)
    qed
    thus ?case by blast
  qed
  thus ?thesis
    using assms by blast 
qed

lemma identity_telescopic:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and l::'a and n::nat
  assumes \<open>x \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<longlonglongrightarrow> l - x n\<close>
proof-
  have \<open>sum (\<lambda> k. x (Suc k) - x k) {n..n+p} = x (Suc (n+p)) - x n\<close>
    for p
  proof(induction p)
    case 0
    thus ?case by simp
  next
    case (Suc p)
    thus ?case by simp
  qed
  moreover have \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) (n + t)  = (\<lambda> p. sum (\<lambda> k. x (Suc k) - x k) {n..n+p}) t\<close>
    for t
    by blast
  moreover have \<open>(\<lambda> p. x (Suc (n + p)) - x n)\<longlonglongrightarrow> l - x n\<close>
  proof-
    from \<open>x \<longlonglongrightarrow> l\<close>
    have \<open>(\<lambda> p. x (p + Suc n)) \<longlonglongrightarrow> l\<close>
      by (rule LIMSEQ_ignore_initial_segment)
    hence \<open>(\<lambda> p. x (Suc n + p)) \<longlonglongrightarrow> l\<close>   
      by (simp add: add.commute)
    have \<open>(\<lambda> p. x (Suc (n + p))) \<longlonglongrightarrow> l\<close>
    proof-
      have \<open>Suc n + p = Suc (n + p)\<close>
        for p
        by simp
      thus ?thesis using \<open>(\<lambda> p. x (Suc n + p)) \<longlonglongrightarrow> l\<close> by simp 
    qed
    hence \<open>(\<lambda> t. (- (x n)) + (\<lambda> p.  x (Suc (n + p))) t ) \<longlonglongrightarrow> (- (x n))  + l\<close>
      using tendsto_add_const_iff 
      by metis 
    thus ?thesis by simp
  qed
  ultimately have  \<open>(\<lambda> p. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) (n + p)) \<longlonglongrightarrow> l - x n\<close>
    by simp
  hence  \<open>(\<lambda> p. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) p) \<longlonglongrightarrow> l - x n\<close>
    by (rule lim_shift)
  hence  \<open>(\<lambda> M. (\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) M) \<longlonglongrightarrow> l - x n\<close>
    by simp
  thus ?thesis by blast
qed

lemma bound_telescopic:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and l::'a and n::nat and K::real
  assumes \<open>x \<longlonglongrightarrow> l\<close> and \<open>\<And> k. (sum (\<lambda> t. norm (x (Suc t) - x t)) {n..k}) \<le> K\<close>
  shows \<open>norm (l - x n) \<le> K\<close>
proof-
  have \<open>(\<lambda> N. sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<longlonglongrightarrow> l - x n\<close>
    by (simp add: assms identity_telescopic)
  hence \<open>(\<lambda> N. norm (sum (\<lambda> k. x (Suc k) - x k) {n..N})) \<longlonglongrightarrow> norm (l - x n)\<close>
    using tendsto_norm by blast
  moreover have \<open>norm (sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<le> K\<close>
    for N
  proof-
    have \<open>norm (sum (\<lambda> k. x (Suc k) - x k) {n..N}) \<le> sum (\<lambda> n. norm (x (Suc n) - x n)) {n..N}\<close>
      by (simp add: sum_norm_le)      
    also have \<open>... \<le> K \<close>
    proof-
      have \<open>sum (\<lambda> n. norm (x (Suc n) - x n)) {n..N}
               \<in> { (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..K})|K::nat. True}\<close>
        by blast
      moreover have \<open>bdd_above { (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..K})|K::nat. True}\<close>
        using  \<open>\<And> k. (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..k}) \<le> K\<close>
        by fastforce        
      ultimately have  \<open>sum (\<lambda> n. norm (x (Suc n) - x n)) {n..N} \<le> K\<close>
        using  \<open>\<And> k. (sum (\<lambda> n. norm (x (Suc n) - x n)) {n..k}) \<le> K\<close>
        by blast
      thus ?thesis
        by (simp add: full_SetCompr_eq) 
    qed
    finally show ?thesis by blast
  qed
  ultimately show ?thesis
    using Lim_bounded by blast 
qed


lemma LIMSEQ_realpow_inf:
  fixes x :: real
  assumes \<open>x > 1\<close>
  shows  \<open>( \<lambda> n::nat. x^n) \<longlonglongrightarrow> \<infinity>\<close>
  using Limits.LIMSEQ_inverse_realpow_zero
  by (metis (mono_tags, lifting) Elementary_Topology.real_arch_pow Lim_PInfty assms le_ereal_le less_eq_ereal_def less_ereal.simps(1) power_increasing_iff) 

lemma LIMSEQ_scalarR: 
  fixes x :: \<open>nat \<Rightarrow> real\<close> and c :: real
  assumes \<open>x \<longlonglongrightarrow> \<infinity>\<close> and \<open>c > 0\<close>
  shows  \<open>(\<lambda> n::nat. c * (x n)) \<longlonglongrightarrow> \<infinity>\<close>
proof-
  have \<open>M \<ge> 0 \<Longrightarrow> \<exists> N. \<forall> n\<ge>N. c * x n \<ge> ereal M\<close>
    for M
  proof-
    assume \<open>M \<ge> 0\<close>
    hence \<open>(1/c) * M \<ge> 0\<close>
      using \<open>c > 0\<close>
      by auto
    from \<open>x \<longlonglongrightarrow> \<infinity>\<close>
    have \<open>\<exists> N. \<forall> n\<ge>N. x n \<ge> ereal ((1/c) * M)\<close>
      by (simp add: Lim_PInfty)
    hence \<open>\<exists> N. \<forall> n\<ge>N. c*(x n) \<ge> ereal M\<close>
      using \<open>c > 0\<close>
      by (simp add: mult.commute pos_divide_le_eq)
    thus ?thesis
      by blast 
  qed
  hence \<open>\<exists> N. \<forall> n\<ge>N. c * x n \<ge> ereal M\<close>
    for M
  proof(cases \<open>M \<ge> 0\<close>)
    case True
    thus ?thesis
      using \<open>\<And>M. 0 \<le> M \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. ereal M \<le> ereal (c * x n)\<close> by auto 
  next
    case False
    thus ?thesis
    proof -
      have "(0::real) \<le> 0"
        by auto
      then obtain nn :: "real \<Rightarrow> nat" where
        f1: "\<forall>n. \<not> nn 0 \<le> n \<or> ereal 0 \<le> ereal (c * x n)"
        by (meson \<open>\<And>M. 0 \<le> M \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. ereal M \<le> ereal (c * x n)\<close>)
      obtain nna :: "nat \<Rightarrow> nat" where
        "\<forall>x0. (\<exists>v1\<ge>x0. \<not> ereal M \<le> ereal (c * x v1)) = (x0 \<le> nna x0 \<and> \<not> ereal M \<le> ereal (c * x (nna x0)))"
        by moura
      moreover
      { assume "0 \<le> c * x (nna (nn 0))"
        hence "M + - 1 * (c * x (nna (nn 0))) \<le> 0"
          using False by linarith
        hence "\<exists>n. \<not> n \<le> nna n \<or> ereal M \<le> ereal (c * x (nna n))"
          by auto }
      ultimately show ?thesis
        using f1 ereal_less_eq(3) by blast
    qed 
  qed
  thus ?thesis 
    by (simp add: Lim_PInfty)
qed

subsection \<open>Cauchy sequences\<close>

lemma non_Cauchy_unbounded:
  fixes a ::\<open>nat \<Rightarrow> real\<close> and e::real
  assumes  \<open>\<And> n. a n \<ge> 0\<close> and \<open>e > 0\<close> and
    \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
  shows \<open>(\<lambda> n. (sum a  {0..n})) \<longlonglongrightarrow> \<infinity>\<close>
proof-
  have \<open>incseq (\<lambda> n. (sum a  {..<n}))\<close>
    using \<open>\<And> n. a n \<ge> 0\<close> using Extended_Real.incseq_sumI 
    by auto
  hence \<open>incseq (\<lambda> n. (sum a  {..< Suc n}))\<close>
    by (meson incseq_Suc_iff)
  hence \<open>incseq (\<lambda> n. (sum a  {0..n}))\<close>  
    by (simp add: sum_mono2 assms(1) incseq_def) 
  hence \<open>incseq (\<lambda> n. (sum a  {0..n})::ereal)\<close>
    using incseq_ereal by blast
  hence \<open>(\<lambda> n. (sum a  {0..n})::ereal) \<longlonglongrightarrow> Sup (range (\<lambda> n. (sum a  {0..n})::ereal))\<close>
    using LIMSEQ_SUP by auto
  moreover have \<open>Sup ((range (\<lambda> n. (sum a  {0..n})))::ereal set) = \<infinity>\<close>
  proof-
    define S where \<open>S = ((range (\<lambda> n. (sum a  {0..n})))::ereal set)\<close>
    have \<open>\<exists> s \<in> S.  k*e \<le> s\<close>
      for k::nat
    proof(induction k)
      case 0
      from \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
      obtain m n where \<open>m \<ge> 0\<close> and \<open>n \<ge> 0\<close> and \<open>m > n\<close>
        and \<open>sum a {Suc n..m} \<ge> e\<close>
        by blast
      from \<open>sum a {Suc n..m} \<ge> e\<close>
      have \<open>sum a {Suc n..m} > 0\<close>
        using \<open>e > 0\<close>
        by linarith
      moreover have \<open>sum a {0..n} \<ge> 0\<close>
        by (simp add: assms(1) sum_nonneg)
      moreover have \<open>sum a {0..n} + sum a {Suc n..m} = sum a {0..m}\<close>
      proof-
        have \<open>finite {0..n}\<close>
          by simp
        moreover have \<open>finite {Suc n..m}\<close>
          by simp
        moreover have \<open>{0..n} \<union> {Suc n..m} = {0..m}\<close>
        proof-
          have \<open>n < Suc n\<close>
            by simp
          thus ?thesis using Set_Interval.ivl_disj_un(7)
            using \<open>n < m\<close> by auto
        qed
        moreover have \<open>{0..n} \<inter> {Suc n..m} = {}\<close>
          by simp
        ultimately show ?thesis
          by (metis sum.union_disjoint) 
      qed
      ultimately have \<open>sum a {0..m} > 0\<close>
        by linarith
      moreover have \<open>ereal (sum a {0..m}) \<in> S\<close>
        unfolding S_def
        by blast
      ultimately have \<open>\<exists> s \<in> S. 0 \<le> s\<close>
        using ereal_less_eq(5) by fastforce    
      thus ?case
        by (simp add: zero_ereal_def)  
    next
      case (Suc k)
      assume \<open>\<exists>s\<in>S. ereal (real k * e) \<le> s\<close>
      then obtain s where \<open>s \<in> S\<close> 
        and \<open> ereal (real k * e) \<le> s\<close>
        by blast
      have \<open>\<exists> N. s = ereal (sum a {0..N})\<close>
        using \<open>s \<in> S\<close>
        unfolding S_def by blast
      then obtain N where \<open>s = ereal (sum a {0..N})\<close>
        by blast
      from \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
      obtain m n where \<open>m \<ge> Suc N\<close> and \<open>n \<ge> Suc N\<close> and \<open>m > n\<close>
        and \<open>sum a {Suc n..m} \<ge> e\<close>
        by blast
      have \<open>sum a {Suc N..m} \<ge> e\<close>
      proof-
        have \<open>sum a {Suc N..m} = sum a {Suc N..n} + sum a {Suc n..m}\<close>
        proof-
          have \<open>finite {Suc N..n}\<close>
            by simp
          moreover have \<open>finite {Suc n..m}\<close>
            by simp
          moreover have \<open>{Suc N..n} \<union> {Suc n..m} = {Suc N..m}\<close>
            using Set_Interval.ivl_disj_un
            by (smt \<open>Suc N \<le> n\<close> \<open>n < m\<close> atLeastSucAtMost_greaterThanAtMost less_imp_le_nat)
          moreover have \<open>{} = {Suc N..n} \<inter> {Suc n..m}\<close>
            by simp
          ultimately show ?thesis 
            by (metis sum.union_disjoint)
        qed
        moreover have \<open>sum a {Suc N..n} \<ge> 0\<close>
          using  \<open>\<And> n. a n \<ge> 0\<close>
          by (simp add: sum_nonneg) 
        ultimately show ?thesis
          using \<open>e \<le> sum a {Suc n..m}\<close> by linarith 
      qed
      moreover have \<open>sum a {0..N} + sum a {Suc N..m} =  sum a {0..m}\<close>
      proof-
        have \<open>finite {0..N}\<close>
          by simp
        have \<open>finite {Suc N..m}\<close>
          by simp
        moreover have \<open>{0..N} \<union> {Suc N..m} = {0..m}\<close>
        proof-
          have \<open>N < Suc N\<close>
            by simp
          thus ?thesis using Set_Interval.ivl_disj_un(7)
              \<open>Suc N \<le> m\<close> by auto            
        qed          
        moreover have \<open>{0..N} \<inter> {Suc N..m} = {}\<close>
          by simp
        ultimately show ?thesis 
          by (metis \<open>finite {0..N}\<close> sum.union_disjoint)
      qed
      ultimately have \<open>e + k * e \<le> sum a {0..m}\<close>
        using \<open>ereal (real k * e) \<le> s\<close> \<open>s = ereal (sum a {0..N})\<close> by auto
      moreover have \<open>e + k * e = (Suc k) * e\<close>
      proof-
        have \<open>e + k * e = (1 + k) * e\<close>
          by (simp add: semiring_normalization_rules(3))
        thus ?thesis by simp
      qed
      ultimately have \<open>(Suc k) * e \<le> sum a {0..m}\<close>
        by linarith
      hence \<open>ereal ((Suc k) * e) \<le> ereal (sum a {0..m})\<close>
        by auto
      moreover have \<open>ereal (sum a {0..m}) \<in> S\<close>
        unfolding S_def
        by blast
      ultimately show ?case
        by blast
    qed
    hence  \<open>\<exists> s \<in> S.  (real n) \<le> s\<close>
      for n::nat
      by (meson assms(2) ereal_le_le ex_less_of_nat_mult less_le_not_le)
    hence  \<open>Sup S = \<infinity>\<close>
      using Sup_le_iff Sup_subset_mono dual_order.strict_trans1 leD less_PInf_Ex_of_nat subsetI 
      by metis
    thus ?thesis using S_def 
      by blast
  qed
  ultimately show ?thesis 
    using PInfty_neq_ereal by auto 
qed

lemma sum_Cauchy_positive:
  fixes a ::\<open>nat \<Rightarrow> real\<close>
  assumes \<open>\<And> n. a n \<ge> 0\<close> 
    and \<open>\<exists> K. \<forall> n::nat. (sum a  {0..n}) \<le> K\<close>
  shows \<open>Cauchy (\<lambda> n. (sum a  {0..n}))\<close>
proof-
  have \<open>e>0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
    for e
  proof-
    assume \<open>e>0\<close>       
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
    proof(rule classical)
      assume \<open>\<not>(\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e)\<close>
      hence \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> \<not>(sum a {Suc n..m} < e)\<close>
        by blast
      hence \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
        by fastforce
      hence \<open>(\<lambda> n. (sum a  {0..n}) ) \<longlonglongrightarrow> \<infinity>\<close>
        using non_Cauchy_unbounded \<open>0 < e\<close> assms(1) by blast
      from  \<open>\<exists> K. \<forall> n::nat. (sum a  {0..n}) \<le> K\<close>
      obtain K where  \<open>\<forall> n::nat. (sum a  {0..n}) \<le> K\<close>
        by blast
      from  \<open>(\<lambda> n. (sum a  {0..n}) ) \<longlonglongrightarrow> \<infinity>\<close>
      have \<open>\<forall>B. \<exists>N. \<forall>n\<ge>N. (\<lambda> n. (sum a  {0..n}) ) n \<ge> ereal B\<close>
        using Lim_PInfty by simp
      hence  \<open>\<exists> n::nat. (sum a  {0..n}) \<ge> K+1\<close>
        using ereal_less_eq(3) by blast        
      thus ?thesis using  \<open>\<forall> n::nat. (sum a  {0..n}) \<le> K\<close> by smt       
    qed
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
    proof-
      have \<open>sum a {Suc n..m} = sum a {0..m} - sum a {0..n}\<close>
        if "m > n" for m n
        apply (simp add: that atLeast0AtMost)
        using that by (rule sum_interval_split)
      thus ?thesis using \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close> 
        by smt 
    qed
    have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
    proof-
      from \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
      obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
        by blast
      moreover have \<open>m > n \<Longrightarrow> sum a {0..m} \<ge> sum a {0..n}\<close>
        for m n
        using \<open>\<And> n. a n \<ge> 0\<close> 
        by (simp add: sum_mono2)
      ultimately show ?thesis 
        by auto
    qed
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m \<ge> n \<longrightarrow> \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
      by (metis \<open>0 < e\<close> abs_zero cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' less_irrefl_nat linorder_neqE_nat zero_less_diff)      
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
      by (metis abs_minus_commute nat_le_linear)
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
      by (simp add: dist_real_def)      
    thus ?thesis by blast
  qed
  thus ?thesis
    using Cauchy_altdef2 le_refl by fastforce 
qed

lemma convergent_series_Cauchy:
  fixes a::\<open>nat \<Rightarrow> real\<close> and \<phi>::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>\<exists> M. \<forall> n. (sum a {0..n}) \<le> M\<close>
    and \<open>\<And> n. dist (\<phi> (Suc n)) (\<phi> n) \<le> a n\<close>
  shows \<open>Cauchy \<phi>\<close>
proof-
  have \<open>e > 0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> dist (\<phi> m) (\<phi> n) < e\<close>
    for e
  proof-
    assume \<open>e > 0\<close>
    have \<open>dist (\<phi> (n+p+1)) (\<phi> n) \<le> sum a {n..n+p}\<close>
      for p n :: nat
    proof(induction p)
      case 0
      thus ?case
        by (simp add: assms(2))
    next
      case (Suc p)
      thus ?case
        by (smt Suc_eq_plus1 add_Suc_right assms(2) dist_self dist_triangle2 le_add1 sum.nat_ivl_Suc') 
    qed
    hence \<open>m > n \<Longrightarrow> dist (\<phi> m) (\<phi> n) \<le> sum a {n..m-1}\<close>
      for m n :: nat
      by (metis Suc_eq_plus1 Suc_le_D diff_Suc_1  gr0_implies_Suc less_eq_Suc_le less_imp_Suc_add zero_less_Suc)
    moreover have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {n..m-1} < e\<close>
    proof-
      have  \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
      proof-
        have \<open>\<And> k. a k \<ge> 0\<close>
          using \<open>\<And> n. dist (\<phi> (Suc n)) (\<phi> n) \<le> a n\<close>
            dual_order.trans zero_le_dist by blast
        hence \<open>Cauchy (\<lambda> k. sum a {0..k})\<close>
          using  \<open>\<exists> M. \<forall> n. (sum a {0..n}) \<le> M\<close>
            sum_Cauchy_positive by blast
        hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
          unfolding Cauchy_def
          using \<open>e > 0\<close>
          by blast
        hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> dist (sum a {0..m}) (sum a {0..n}) < e\<close>
          by blast
        have \<open>m > n \<Longrightarrow> dist (sum a {0..m}) (sum a {0..n}) = sum a {Suc n..m}\<close>
          for m n
        proof-
          assume \<open>m > n\<close>
          have \<open>dist (sum a {0..m}) (sum a {0..n}) 
            = \<bar>(sum a {0..m}) - (sum a {0..n})\<bar>\<close>
            using dist_real_def by blast
          moreover have \<open>(sum a {0..m}) - (sum a {0..n}) = sum a {Suc n..m}\<close>
          proof-
            have  \<open>(sum a {0..n}) + sum a {Suc n..m} = (sum a {0..m})\<close>
            proof-
              have \<open>finite {0..n}\<close>
                by simp
              moreover have \<open>finite {Suc n..m}\<close>
                by simp
              moreover have \<open>{0..n} \<union> {Suc n..m} = {0..m}\<close>
              proof-
                have \<open>n < Suc n\<close>
                  by simp
                thus ?thesis using  \<open>n < m\<close> by auto
              qed
              moreover have  \<open>{0..n} \<inter> {Suc n..m} = {}\<close>
                by simp
              ultimately show ?thesis
                by (metis sum.union_disjoint)
            qed
            thus ?thesis
              by linarith 
          qed
          ultimately show ?thesis
            by (simp add: \<open>\<And>k. 0 \<le> a k\<close> sum_nonneg) 
        qed
        thus ?thesis
          by (metis \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>) 
      qed  
      show ?thesis 
      proof-
        obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
          using \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. n < m \<longrightarrow> sum a {Suc n..m} < e\<close> by blast
        hence  \<open>\<forall>m. \<forall>n. Suc m \<ge> Suc M \<and> Suc n \<ge> Suc M \<and> Suc m > Suc n \<longrightarrow> sum a {Suc n..Suc m - 1} < e\<close>
          by simp
        hence  \<open>\<forall>m\<ge>1. \<forall>n\<ge>1. m \<ge> Suc M \<and> n \<ge> Suc M \<and> m > n \<longrightarrow> sum a {n..m - 1} < e\<close>
          by (metis Suc_le_D)
        thus ?thesis 
          by (meson add_leE)
      qed
    qed
    ultimately show ?thesis using \<open>e > 0\<close> by smt
  qed
  thus ?thesis
    using Cauchy_altdef2 by fastforce 
qed


subsection \<open>Pointwise convergence\<close>

text\<open>Pointwise convergence\<close>
definition pointwise_convergent_to :: 
  \<open>( nat \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) ) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> 
  (\<open>((_)/ \<midarrow>pointwise\<rightarrow> (_))\<close> [60, 60] 60) where
  \<open>pointwise_convergent_to x l = (\<forall> t::'a. (\<lambda> n. (x n) t) \<longlonglongrightarrow> l t)\<close>

lemma linear_limit_linear:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_vector \<Rightarrow> 'b::real_normed_vector)\<close>
    and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. linear (f n)\<close> and  \<open>f \<midarrow>pointwise\<rightarrow> F\<close>
  shows \<open>linear F\<close> 
proof
  have \<open>\<And> x. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
    using  \<open>f \<midarrow>pointwise\<rightarrow> F\<close>
    by (auto simp: pointwise_convergent_to_def)
  show "F (x + y) = F x + F y"
    for x :: 'a
      and y :: 'a
  proof-
    have \<open>(\<lambda> n. (f n) (x + y)) \<longlonglongrightarrow> F (x + y)\<close>
      by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>(\<lambda> n. (f n) y) \<longlonglongrightarrow> F y\<close>
      by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>lim (\<lambda> n. (f n) (x + y)) = lim (\<lambda> n. (f n) x) + lim (\<lambda> n. (f n) y)\<close> 
    proof-
      have \<open>(f n) (x + y) = (f n) x + (f n) y\<close>
        for n
        using \<open>\<And> n.  linear (f n)\<close>
        unfolding linear_def
        using Real_Vector_Spaces.linear_iff assms(1) by auto
      hence \<open>lim (\<lambda> n. (f n) (x + y)) = lim (\<lambda> n. (f n) x + (f n) y)\<close>
        by simp
      moreover have \<open>lim (\<lambda> n. (f n) x + (f n) y) = lim (\<lambda> n. (f n) x) + lim (\<lambda> n. (f n) y)\<close>
      proof-
        have \<open>convergent (\<lambda> n. (f n) x)\<close> 
          using \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> convergentI by auto
        moreover have \<open>convergent (\<lambda> n. (f n) y)\<close> 
          using \<open>(\<lambda> n. (f n) y) \<longlonglongrightarrow> F y\<close> convergentI by auto            
        ultimately show ?thesis
        proof -
          have f1: "\<forall>a. F a = lim (\<lambda>n. f n a)"
            by (metis (full_types)  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close> limI)
          have "\<forall>f b ba fa. (lim (\<lambda>n. fa n + f n) = (b::'b) + ba \<or> \<not> f \<longlonglongrightarrow> ba) \<or> \<not> fa \<longlonglongrightarrow> b"
            by (metis (no_types) limI tendsto_add)
          thus ?thesis
            using f1  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close> by fastforce
        qed 
      qed
      ultimately show ?thesis
        by simp  
    qed
    ultimately show ?thesis
      by (metis limI) 
  qed
  show "F (r *\<^sub>R x) = r *\<^sub>R F x"
    for r :: real
      and x :: 'a
  proof-
    have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      by (simp add:  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>(\<lambda> n.  (f n) (r *\<^sub>R x)) \<longlonglongrightarrow> F (r *\<^sub>R x)\<close>
      by (simp add:  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close>)
    moreover have \<open>lim (\<lambda> n.  (f n) (r *\<^sub>R x)) = r *\<^sub>R lim (\<lambda> n. (f n) x)\<close>
    proof-
      have \<open>(f n) (r *\<^sub>R x) = r *\<^sub>R (f n) x\<close>
        for n
        using  \<open>\<And> n.  linear (f n)\<close>
        unfolding linear_def
        unfolding Modules.additive_def
        by (simp add: Real_Vector_Spaces.linear_def real_vector.linear_scale)
      hence \<open>lim (\<lambda> n. (f n) (r *\<^sub>R x)) = lim (\<lambda> n. r *\<^sub>R (f n) x)\<close>
        by simp
      show ?thesis 
      proof-
        have \<open>convergent (\<lambda> n. (f n) x)\<close>
          using \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> convergentI by auto
        moreover have \<open>isCont (\<lambda> t::'b. r *\<^sub>R t) tt\<close>
          for tt
          by (simp add: bounded_linear_scaleR_right)
        ultimately have \<open>lim (\<lambda> n. r *\<^sub>R ((f n) x)) =  r *\<^sub>R lim (\<lambda> n. (f n) x)\<close>
          by (metis (mono_tags)  \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> F x\<close> isCont_tendsto_compose limI)
        thus ?thesis using  \<open>lim (\<lambda> n. (f n) (r *\<^sub>R x)) = lim (\<lambda> n. r *\<^sub>R (f n) x)\<close>
          by simp
      qed
    qed
    ultimately show ?thesis
      by (metis limI) 
  qed
qed

end
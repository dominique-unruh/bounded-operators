(*
  File:   Banach_Steinhaus.thy
  Author: Dominique Unruh, University of Tartu
  Author: Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Banach-Steinhaus theorem\<close>

theory Banach_Steinhaus
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL-Analysis.Infinite_Set_Sum"
    "HOL-Types_To_Sets.Types_To_Sets"
begin


text \<open>
  We formalize Banach-Steinhaus theorem as theorem @{text banach_steinhaus}.
\<close>

subsection \<open>Results missing for the proof of Banach-Steinhaus theorem\<close>
text \<open>
  The results proved here are preliminaries for the proof of Banach-Steinhaus theorem using Sokal 
  approach, but they do not explicitly appear in Sokal's paper ~\cite{sokal2011reall}.
\<close>

lemma bdd_above_plus:
  \<open>S \<noteq> {} \<Longrightarrow> bdd_above (f ` S) \<Longrightarrow> bdd_above (g ` S) \<Longrightarrow> bdd_above ((\<lambda> x. f x + g x) ` S)\<close>
  for f::\<open>'a \<Rightarrow> real\<close>
proof-
  assume \<open>S \<noteq> {}\<close> and \<open>bdd_above (f ` S)\<close> and \<open>bdd_above (g ` S)\<close>
  obtain M where \<open>\<And> x. x\<in>S \<Longrightarrow> f x \<le> M\<close>
    using \<open>bdd_above (f ` S)\<close> unfolding bdd_above_def by blast
  obtain N where \<open>\<And> x. x\<in>S \<Longrightarrow> g x \<le> N\<close>
    using \<open>bdd_above (g ` S)\<close> unfolding bdd_above_def by blast
  have \<open>\<And> x. x\<in>S \<Longrightarrow> f x + g x \<le> M + N\<close>
    using \<open>\<And>x. x \<in> S \<Longrightarrow> f x \<le> M\<close> \<open>\<And>x. x \<in> S \<Longrightarrow> g x \<le> N\<close> by fastforce
  thus ?thesis unfolding bdd_above_def by blast
qed


lemma max_Sup_absord_left:
  fixes f g :: \<open>'a \<Rightarrow> real\<close> and X::\<open>'a set\<close>
  assumes \<open>X \<noteq> {}\<close> and \<open>bdd_above (f ` X)\<close> and \<open>bdd_above (g ` X)\<close> and \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close>
  shows \<open>Sup ((\<lambda> x. max (f x) (g x)) ` X) = Sup (f ` X)\<close>
proof-
  have y_Sup: \<open>y \<in> ((\<lambda> x. max (f x) (g x)) ` X) \<Longrightarrow> y \<le> Sup (f ` X)\<close> for y
  proof-
    assume \<open>y \<in> ((\<lambda> x. max (f x) (g x)) ` X)\<close>
    then obtain x where \<open>y = max (f x) (g x)\<close> and \<open>x \<in> X\<close>
      by blast
    have \<open>f x \<le> Sup (f ` X)\<close>
      by (simp add:  \<open>x \<in> X\<close> \<open>bdd_above (f ` X)\<close> cSUP_upper) 
    moreover have  \<open>g x \<le> Sup (g ` X)\<close>
      by (simp add:  \<open>x \<in> X\<close> \<open>bdd_above (g ` X)\<close> cSUP_upper) 
    ultimately have \<open>max (f x) (g x) \<le> Sup (f ` X)\<close>
      using  \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close> by auto
    thus ?thesis by (simp add: \<open>y = max (f x) (g x)\<close>) 
  qed

  have y_f_X: \<open>y \<in> f ` X \<Longrightarrow> y \<le> Sup ((\<lambda> x. max (f x) (g x)) ` X)\<close> for y
  proof-
    assume \<open>y \<in> f ` X\<close>
    then obtain x where \<open>x \<in> X\<close> and \<open>y = f x\<close>
      by blast
    have  \<open>bdd_above ((\<lambda> \<xi>. max (f \<xi>) (g \<xi>)) ` X)\<close>
      by (metis (no_types) \<open>bdd_above (f ` X)\<close> \<open>bdd_above (g ` X)\<close> bdd_above_image_sup sup_max)
    moreover have \<open>e > 0 \<Longrightarrow> \<exists> k \<in> (\<lambda> \<xi>. max (f \<xi>) (g \<xi>)) ` X. y \<le> k + e\<close>
      for e::real
      using \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close> by (smt \<open>x \<in> X\<close> \<open>y = f x\<close> image_eqI)        
    ultimately show ?thesis
      using \<open>x \<in> X\<close> \<open>y = f x\<close> cSUP_upper by fastforce
  qed

  have \<open>Sup ((\<lambda> x. max (f x) (g x)) ` X) \<le> Sup (f ` X)\<close>
    using y_Sup by (simp add: \<open>X \<noteq> {}\<close> cSup_least) 
  moreover have \<open>Sup ((\<lambda> x. max (f x) (g x)) ` X) \<ge> Sup (f ` X)\<close>
    using y_f_X by (metis (mono_tags) cSup_least calculation empty_is_image)  
  ultimately show ?thesis by simp
qed

lemma max_Sup_absord_right:
  fixes f g :: \<open>'a \<Rightarrow> real\<close> and X::\<open>'a set\<close>
  assumes \<open>X \<noteq> {}\<close> and \<open>bdd_above (f ` X)\<close> and \<open>bdd_above (g ` X)\<close> and \<open>Sup (f ` X) \<le> Sup (g ` X)\<close>
  shows \<open>Sup ((\<lambda> x. max (f x) (g x)) ` X) = Sup (g ` X)\<close>
proof-
  have \<open>Sup ((\<lambda> x. max (g x) (f x)) ` X) = Sup (g ` X)\<close>
    using max_Sup_absord_left by (simp add: max_Sup_absord_left assms(1) assms(2) assms(3) assms(4)) 
  moreover have \<open>max (g x) (f x) = max (f x) (g x)\<close> for x
    by auto
  ultimately show ?thesis by simp
qed

lemma max_Sup:
  fixes f g :: \<open>'a \<Rightarrow> real\<close> and X::\<open>'a set\<close>
  assumes \<open>X \<noteq> {}\<close> and \<open>bdd_above (f ` X)\<close> and \<open>bdd_above (g ` X)\<close>
  shows \<open>Sup ((\<lambda> x. max (f x) (g x)) ` X) = max (Sup (f ` X)) (Sup (g ` X))\<close>
proof(cases \<open>Sup (f ` X) \<ge> Sup (g ` X)\<close>)
  case True thus ?thesis by (simp add: assms(1) assms(2) assms(3) max_Sup_absord_left)
next
  case False 
  have f1: "Sup (f ` X) + - 1 * Sup (g ` X) \<le> 0"
    using False by auto
  have f2: "\<forall>A f g. A \<noteq> {} \<and> bdd_above (f ` A) \<and> bdd_above (g ` A) \<and> Sup (f ` A) \<le> Sup (g ` A)
         \<longrightarrow> (SUP a\<in>A. if (f (a::'a)::real) \<le> g a then g a else f a) = Sup (g ` A)"
    by (smt max_Sup_absord_right)    
  have "(Sup (f ` X) \<le> Sup (g ` X)) = (Sup (f ` X) + - 1 * Sup (g ` X) \<le> 0)"
    by auto
  hence "(SUP a\<in>X. if f a \<le> g a then g a else f a) = 
         (if Sup (f ` X) \<le> Sup (g ` X) then Sup (g ` X) else Sup (f ` X))"
    using f2 f1 by (meson assms(1) assms(2) assms(3))
  thus ?thesis
    by (simp add: max_def_raw)
qed

lemma bounded_linear_ball_bdd_above:
  assumes \<open>r > 0\<close> and \<open>bounded_linear f\<close>
  shows \<open>bdd_above ((norm \<circ> f) ` (ball x r))\<close>
proof-
  define M where \<open>M = onorm f * (r + norm x)\<close>
  have \<open>norm (x - y) < r \<Longrightarrow> norm (f y) \<le> M\<close> for y
  proof-
    assume \<open>norm (x - y) < r\<close>
    moreover have \<open>norm (f \<xi>) \<le> onorm f * norm \<xi>\<close> for \<xi>
      by (simp add: \<open>bounded_linear f\<close> onorm)    
    moreover have \<open>norm y \<le> norm (x - y) + norm x\<close> for y
      by (smt norm_triangle_ineq3)
    ultimately show ?thesis
      by (smt M_def \<open>bounded_linear f\<close> combine_common_factor 
          linordered_comm_semiring_strict_class.comm_mult_strict_left_mono onorm_pos_le) 
  qed
  thus ?thesis 
    unfolding bdd_above_def ball_def by (smt comp_eq_dest_lhs imageE mem_Collect_eq dist_norm)
qed


lemma non_Cauchy_unbounded:
  fixes a ::\<open>nat \<Rightarrow> real\<close> and e::real
  assumes  \<open>\<And> n. a n \<ge> 0\<close> and \<open>e > 0\<close>
    and \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
  shows \<open>(\<lambda> n. (sum a  {0..n})) \<longlonglongrightarrow> \<infinity>\<close>
proof-
  define S where \<open>S = ((range (\<lambda> n. (sum a  {0..n})))::ereal set)\<close>
  have \<open>\<exists> s \<in> S.  k*e \<le> s\<close> for k::nat
  proof(induction k)
    case 0
    from \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
    obtain m n where \<open>m \<ge> 0\<close> and \<open>n \<ge> 0\<close> and \<open>m > n\<close> and \<open>sum a {Suc n..m} \<ge> e\<close> by blast
    have \<open>n < Suc n\<close>
      by simp
    hence \<open>{0..n} \<union> {Suc n..m} = {0..m}\<close>
      using Set_Interval.ivl_disj_un(7) \<open>n < m\<close> by auto
    moreover have \<open>finite {0..n}\<close>
      by simp
    moreover have \<open>finite {Suc n..m}\<close>
      by simp
    moreover have \<open>{0..n} \<inter> {Suc n..m} = {}\<close>
      by simp
    ultimately have \<open>sum a {0..n} + sum a {Suc n..m} = sum a {0..m}\<close>
      by (metis sum.union_disjoint) 
    moreover have \<open>sum a {Suc n..m} > 0\<close>
      using \<open>e > 0\<close> \<open>sum a {Suc n..m} \<ge> e\<close> by linarith
    moreover have \<open>sum a {0..n} \<ge> 0\<close>
      by (simp add: assms(1) sum_nonneg)
    ultimately have \<open>sum a {0..m} > 0\<close>
      by linarith      
    moreover have \<open>ereal (sum a {0..m}) \<in> S\<close>
      unfolding S_def by blast
    ultimately have \<open>\<exists> s \<in> S. 0 \<le> s\<close>
      using ereal_less_eq(5) by fastforce    
    thus ?case
      by (simp add: zero_ereal_def)  
  next
    case (Suc k)
    assume \<open>\<exists>s\<in>S. ereal (real k * e) \<le> s\<close>
    then obtain s where \<open>s \<in> S\<close> and \<open> ereal (real k * e) \<le> s\<close>
      by blast
    have \<open>\<exists> N. s = ereal (sum a {0..N})\<close>
      using \<open>s \<in> S\<close> unfolding S_def by blast
    then obtain N where \<open>s = ereal (sum a {0..N})\<close>
      by blast
    from \<open>\<forall>M. \<exists>m. \<exists>n. m \<ge> M \<and> n \<ge> M \<and> m > n \<and> sum a {Suc n..m} \<ge> e\<close>
    obtain m n where \<open>m \<ge> Suc N\<close> and \<open>n \<ge> Suc N\<close> and \<open>m > n\<close> and \<open>sum a {Suc n..m} \<ge> e\<close>
      by blast
    have \<open>finite {Suc N..n}\<close>
      by simp
    moreover have \<open>finite {Suc n..m}\<close>
      by simp
    moreover have \<open>{Suc N..n} \<union> {Suc n..m} = {Suc N..m}\<close>
      using Set_Interval.ivl_disj_un
      by (smt \<open>Suc N \<le> n\<close> \<open>n < m\<close> atLeastSucAtMost_greaterThanAtMost less_imp_le_nat)
    moreover have \<open>{} = {Suc N..n} \<inter> {Suc n..m}\<close>
      by simp
    ultimately have \<open>sum a {Suc N..m} = sum a {Suc N..n} + sum a {Suc n..m}\<close>
      by (metis sum.union_disjoint)
    moreover have \<open>sum a {Suc N..n} \<ge> 0\<close>
      using  \<open>\<And> n. a n \<ge> 0\<close> by (simp add: sum_nonneg) 
    ultimately have \<open>sum a {Suc N..m} \<ge> e\<close>
      using \<open>e \<le> sum a {Suc n..m}\<close> by linarith
    moreover have \<open>sum a {0..N} + sum a {Suc N..m} =  sum a {0..m}\<close>
    proof-
      have \<open>finite {0..N}\<close>
        by simp
      have \<open>finite {Suc N..m}\<close>
        by simp
      moreover have \<open>{0..N} \<union> {Suc N..m} = {0..m}\<close>
        using Set_Interval.ivl_disj_un(7) \<open>Suc N \<le> m\<close> by auto          
      moreover have \<open>{0..N} \<inter> {Suc N..m} = {}\<close>
        by simp
      ultimately show ?thesis 
        by (metis \<open>finite {0..N}\<close> sum.union_disjoint)
    qed
    ultimately have \<open>e + k * e \<le> sum a {0..m}\<close>
      using \<open>ereal (real k * e) \<le> s\<close> \<open>s = ereal (sum a {0..N})\<close> by auto
    moreover have \<open>e + k * e = (Suc k) * e\<close>
      by (simp add: semiring_normalization_rules(3))
    ultimately have \<open>(Suc k) * e \<le> sum a {0..m}\<close>
      by linarith
    hence \<open>ereal ((Suc k) * e) \<le> ereal (sum a {0..m})\<close>
      by auto
    moreover have \<open>ereal (sum a {0..m}) \<in> S\<close>
      unfolding S_def by blast
    ultimately show ?case
      by blast
  qed
  hence  \<open>\<exists> s \<in> S.  (real n) \<le> s\<close> for n
    by (meson assms(2) ereal_le_le ex_less_of_nat_mult less_le_not_le)
  hence  \<open>Sup S = \<infinity>\<close>
    using Sup_le_iff Sup_subset_mono dual_order.strict_trans1 leD less_PInf_Ex_of_nat subsetI 
    by metis
  hence Sup: \<open>Sup ((range (\<lambda> n. (sum a  {0..n})))::ereal set) = \<infinity>\<close> using S_def 
    by blast
  have \<open>incseq (\<lambda> n. (sum a  {..<n}))\<close>
    using \<open>\<And> n. a n \<ge> 0\<close> using Extended_Real.incseq_sumI by auto
  hence \<open>incseq (\<lambda> n. (sum a  {..< Suc n}))\<close>
    by (meson incseq_Suc_iff)
  hence \<open>incseq (\<lambda> n. (sum a  {0..n}))\<close>  
    by (simp add: sum_mono2 assms(1) incseq_def) 
  hence \<open>incseq (\<lambda> n. (sum a  {0..n})::ereal)\<close>
    using incseq_ereal by blast
  hence \<open>(\<lambda> n. (sum a  {0..n})::ereal) \<longlonglongrightarrow> Sup (range (\<lambda> n. (sum a  {0..n})::ereal))\<close>
    using LIMSEQ_SUP by auto
  thus ?thesis 
    using Sup PInfty_neq_ereal by auto 
qed


lemma sum_Cauchy_positive:
  fixes a ::\<open>_ \<Rightarrow> real\<close>
  assumes \<open>\<And> n. a n \<ge> 0\<close> and \<open>\<exists> K. \<forall> n. (sum a  {0..n}) \<le> K\<close>
  shows \<open>Cauchy (\<lambda> n. (sum a  {0..n}))\<close>
proof-
  { fix e::real
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
    have \<open>sum a {Suc n..m} = sum a {0..m} - sum a {0..n}\<close>
      if "m > n" for m n
      apply (simp add: that atLeast0AtMost)
        (*        using that by (rule sum_interval_split) *) sorry
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
      using \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close> by smt     
    from \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
    obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {0..m} - sum a {0..n} < e\<close>
      by blast
    moreover have \<open>m > n \<Longrightarrow> sum a {0..m} \<ge> sum a {0..n}\<close> for m n
      using \<open>\<And> n. a n \<ge> 0\<close> by (simp add: sum_mono2)
    ultimately have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
      by auto
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m \<ge> n \<longrightarrow> \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
      by (metis \<open>0 < e\<close> abs_zero cancel_comm_monoid_add_class.diff_cancel diff_is_0_eq' less_irrefl_nat linorder_neqE_nat zero_less_diff)      
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<bar>sum a {0..m} - sum a {0..n}\<bar> < e\<close>
      by (metis abs_minus_commute nat_le_linear)
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
      by (simp add: dist_real_def)      
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close> by blast }
  thus ?thesis
    using Cauchy_altdef2 le_refl by fastforce 
qed


lemma convergent_series_Cauchy:
  fixes a::\<open>nat \<Rightarrow> real\<close> and \<phi>::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>\<exists> M. \<forall> n. (sum a {0..n}) \<le> M\<close> and \<open>\<And> n. dist (\<phi> (Suc n)) (\<phi> n) \<le> a n\<close>
  shows \<open>Cauchy \<phi>\<close>
proof-
  { fix e::real
    assume \<open>e > 0\<close>
    have \<open>\<And> k. a k \<ge> 0\<close>
      using \<open>\<And> n. dist (\<phi> (Suc n)) (\<phi> n) \<le> a n\<close> dual_order.trans zero_le_dist by blast
    hence \<open>Cauchy (\<lambda> k. sum a {0..k})\<close>
      using  \<open>\<exists> M. \<forall> n. (sum a {0..n}) \<le> M\<close> sum_Cauchy_positive by blast
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>
      unfolding Cauchy_def using \<open>e > 0\<close> by blast
    hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> dist (sum a {0..m}) (sum a {0..n}) < e\<close>
      by blast
    { fix m n::nat
      assume \<open>n < m\<close>
      have sum_plus: \<open>(sum a {0..n}) + sum a {Suc n..m} = (sum a {0..m})\<close>
      proof-
        have \<open>n < Suc n\<close>
          by simp
        have \<open>finite {0..n}\<close>
          by simp
        moreover have \<open>finite {Suc n..m}\<close>
          by simp
        moreover have \<open>{0..n} \<union> {Suc n..m} = {0..m}\<close>
          using \<open>n < Suc n\<close> \<open>n < m\<close> by auto
        moreover have  \<open>{0..n} \<inter> {Suc n..m} = {}\<close>
          by simp
        ultimately show ?thesis
          by (metis sum.union_disjoint)
      qed
      have \<open>dist (sum a {0..m}) (sum a {0..n}) = \<bar>(sum a {0..m}) - (sum a {0..n})\<bar>\<close>
        using dist_real_def by blast
      moreover have \<open>(sum a {0..m}) - (sum a {0..n}) = sum a {Suc n..m}\<close>
        using sum_plus by linarith 
      ultimately have \<open>m > n \<Longrightarrow> dist (sum a {0..m}) (sum a {0..n}) = sum a {Suc n..m}\<close>
        by (simp add: \<open>\<And>k. 0 \<le> a k\<close> sum_nonneg) }
    hence sum_a: \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
      by (metis \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (sum a {0..m}) (sum a {0..n}) < e\<close>) 
    obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {Suc n..m} < e\<close>
      using sum_a \<open>e > 0\<close> by blast
    hence  \<open>\<forall>m. \<forall>n. Suc m \<ge> Suc M \<and> Suc n \<ge> Suc M \<and> Suc m > Suc n \<longrightarrow> sum a {Suc n..Suc m - 1} < e\<close>
      by simp
    hence  \<open>\<forall>m\<ge>1. \<forall>n\<ge>1. m \<ge> Suc M \<and> n \<ge> Suc M \<and> m > n \<longrightarrow> sum a {n..m - 1} < e\<close>
      by (metis Suc_le_D)
    hence sum_a2: \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> sum a {n..m-1} < e\<close>
      by (meson add_leE)
    have \<open>dist (\<phi> (n+p+1)) (\<phi> n) \<le> sum a {n..n+p}\<close> for p n :: nat
    proof(induction p)
      case 0 thus ?case  by (simp add: assms(2))
    next
      case (Suc p) thus ?case
        by (smt Suc_eq_plus1 add_Suc_right add_less_same_cancel1 assms(2) dist_self dist_triangle2 
            gr_implies_not0 sum.cl_ivl_Suc)  
    qed
    hence \<open>m > n \<Longrightarrow> dist (\<phi> m) (\<phi> n) \<le> sum a {n..m-1}\<close> for m n :: nat
      by (metis Suc_eq_plus1 Suc_le_D diff_Suc_1  gr0_implies_Suc less_eq_Suc_le less_imp_Suc_add 
          zero_less_Suc)
    hence \<open>e > 0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. m > n \<longrightarrow> dist (\<phi> m) (\<phi> n) < e\<close> 
      using sum_a2 \<open>e > 0\<close> by smt } 
  thus ?thesis using Cauchy_altdef2 by fastforce 
qed

lemma bound_Cauchy_to_lim:
  assumes \<open>y \<longlonglongrightarrow> x\<close> and \<open>\<And> n. norm (y (Suc n) - y n) \<le> c^n\<close> and \<open>y 0 = 0\<close> and \<open>c < 1\<close>
  shows \<open>norm (x - y (Suc n)) \<le> (c / (1 - c)) * (c ^ n)\<close>
proof-
  have \<open>c \<ge> 0\<close>
    using \<open>\<And> n. norm (y (Suc n) - y n) \<le> c^n\<close> by (smt norm_imp_pos_and_ge power_Suc0_right)
  have norm_1: \<open>norm (\<Sum>k = Suc n..N. y (Suc k) - y k) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close> for N
  proof(cases \<open>N < Suc n\<close>)
    case True
    hence \<open>norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}) = 0\<close>
      by auto
    thus ?thesis
      using  \<open>c \<ge> 0\<close> \<open>c < 1\<close> by auto       
  next
    case False
    hence \<open>N \<ge> Suc n\<close>
      by auto
    have \<open>c^(Suc N) \<ge> 0\<close>
      using \<open>c \<ge> 0\<close> by auto
    have \<open>1 - c > 0\<close>
      by (simp add: \<open>c < 1\<close>)
    hence \<open>inverse (1 - c) * (1 - c) = 1\<close>
      by auto
    have \<open>norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N})
            \<le> (sum (\<lambda>k. norm (y (Suc k) - y k)) {Suc n .. N})\<close>
      by (simp add: sum_norm_le)
    also have \<open>\<dots> \<le> (sum (power c) {Suc n .. N})\<close>
      using \<open>\<And> n. norm (y (Suc n) - y n) \<le> c^n\<close>
      by (simp add: sum_mono) 
    finally have \<open>norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}) \<le> (sum (power c) {Suc n .. N})\<close>
      by blast      
    hence \<open>(1 - c) * norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}) 
                   \<le> (1 - c) * (sum (power c) {Suc n .. N})\<close>
      using \<open>0 < 1 - c\<close> real_mult_le_cancel_iff2 by blast      
    also have \<open>\<dots> = c^(Suc n) - c^(Suc N)\<close>
      using Set_Interval.sum_gp_multiplied \<open>Suc n \<le> N\<close> by blast
    also have \<open>\<dots> \<le> c^(Suc n)\<close>
      using \<open>c^(Suc N) \<ge> 0\<close> by auto
    finally have \<open>(1 - c) * norm (\<Sum>k = Suc n..N. y (Suc k) - y k) \<le> c ^ Suc n\<close>
      by blast
    moreover have \<open>inverse (1 - c) > 0\<close>
      using \<open>0 < 1 - c\<close> by auto      
    ultimately have \<open>(inverse (1 - c)) * ((1 - c) * norm (\<Sum>k = Suc n..N. y (Suc k) - y k) )
                   \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
      by auto
    moreover have \<open>(inverse (1 - c)) * ((1 - c) * norm (\<Sum>k = Suc n..N. y (Suc k) - y k) ) 
          = norm (\<Sum>k = Suc n..N. y (Suc k) - y k)\<close>
      by (simp add: \<open>inverse (1 - c) * (1 - c) = 1\<close>)      
    ultimately show \<open>norm (\<Sum>k = Suc n..N. y (Suc k) - y k) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
      by auto
  qed
  have \<open>(\<lambda> N. (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N})) \<longlonglongrightarrow> x - y (Suc n)\<close>
    (*   by (metis (no_types) \<open>y \<longlonglongrightarrow> x\<close> identity_telescopic) *)
    sorry
  hence \<open>(\<lambda> N. norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N})) \<longlonglongrightarrow> norm (x - y (Suc n))\<close>
    using tendsto_norm by blast
  hence \<open>norm (x - y (Suc n)) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
    using norm_1 Lim_bounded by blast
  hence  \<open>norm (x - y (Suc n)) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
    by auto
  moreover have \<open>(inverse (1 - c)) * (c ^ Suc n) = (c / (1 - c)) * (c ^ n)\<close>
    by (simp add: divide_inverse_commute)    
  ultimately show \<open>norm (x - y (Suc n)) \<le> (c / (1 - c)) * (c ^ n)\<close>
    by linarith
qed


subsection \<open>Preliminaries for Sokal's proof of Banach-Steinhaus theorem\<close>

lemma linear_plus_norm:
  assumes \<open>linear f\<close>
  shows \<open>norm (f \<xi>) \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>
proof-
  have \<open>norm (f \<xi>) = norm ( (inverse (of_nat 2)) *\<^sub>R (f (x + \<xi>) - f (x - \<xi>)) )\<close>
    (*    by (metis \<open>linear f\<close> linear_plus_minus_one_half)    
*) sorry
  also have \<open>\<dots> = inverse (of_nat 2) * norm (f (x + \<xi>) - f (x - \<xi>))\<close>
    using Real_Vector_Spaces.real_normed_vector_class.norm_scaleR by simp
  also have \<open>\<dots> \<le> inverse (of_nat 2) * (norm (f (x + \<xi>)) + norm (f (x - \<xi>)))\<close>
    by (simp add: norm_triangle_ineq4)
  also have \<open>\<dots> \<le>  max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close>
    by auto
  finally show ?thesis by blast
qed


lemma onorm_r:
  assumes \<open>bounded_linear f\<close> and \<open>r > 0\<close>
  shows \<open>onorm f = (inverse r) * Sup ((norm \<circ> f) ` (ball 0 r))\<close>
proof-
  have onorm_f: \<open>onorm f = Sup ((norm \<circ> f) ` (ball 0 1))\<close>
    (*  by (simp add: \<open>bounded_linear f\<close> onorm_1)      *) sorry
  have s2: \<open>x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1 \<Longrightarrow> x \<le> r * Sup ((norm \<circ> f) ` ball 0 1)\<close> for x
  proof-
    assume \<open>x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1\<close>
    hence \<open>\<exists> t. x = r *\<^sub>R norm (f t) \<and> norm t < 1\<close>
      by auto
    then obtain t where \<open>x = r *\<^sub>R norm (f t)\<close> and \<open>norm t < 1\<close>
      by blast
    have \<open>(norm \<circ> f) ` ball 0 1 \<noteq> {}\<close>
      by simp        
    moreover have \<open>bdd_above ((norm \<circ> f) ` ball 0 1)\<close>
      using \<open>bounded_linear f\<close> Elementary_Normed_Spaces.bounded_linear_image
        [where S = "ball (0::'a) 1" and f = f] bdd_above_norm image_comp
        Elementary_Metric_Spaces.bounded_ball[where x = "0::'a" and e = 1] by metis
    moreover have \<open>\<exists> y. y \<in> (norm \<circ> f) ` ball 0 1 \<and> x \<le> r * y\<close>
    proof-
      define y where \<open>y = x /\<^sub>R r\<close>
      have \<open>x = r * (inverse r * x)\<close>
        using \<open>x = r *\<^sub>R norm (f t)\<close> by auto
      hence \<open>x + - 1 * (r * (inverse r * x)) \<le> 0\<close>
        by linarith
      hence \<open>x \<le> r * (x /\<^sub>R r)\<close>
        by auto
      have \<open>y \<in> (norm \<circ> f) ` ball 0 1\<close>
        unfolding y_def using \<open>x = r *\<^sub>R norm (f t)\<close>  \<open>norm t < 1\<close>
        by (smt \<open>0 < r\<close> \<open>x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1\<close> comp_apply image_iff 
            inverse_inverse_eq pos_le_divideR_eq positive_imp_inverse_positive)
      moreover have \<open>x \<le> r * y\<close>          
        using \<open>x \<le> r * (x /\<^sub>R r)\<close> y_def by blast
      ultimately show ?thesis 
        by blast
    qed
    ultimately show ?thesis
      by (smt \<open>0 < r\<close> cSup_upper ordered_comm_semiring_class.comm_mult_left_mono) 
  qed
  have s3: \<open>(\<And>x. x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1 \<Longrightarrow> x \<le> y) \<Longrightarrow>
         r * Sup ((norm \<circ> f) ` ball 0 1) \<le> y\<close> for y
  proof-
    assume \<open>\<And>x. x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1 \<Longrightarrow> x \<le> y\<close>    
    have \<open>(norm \<circ> f) ` ball 0 1 \<noteq> {}\<close>
      by simp        
    moreover have \<open>bdd_above ((norm \<circ> f) ` ball 0 1)\<close>
      using \<open>bounded_linear f\<close> Elementary_Normed_Spaces.bounded_linear_image
        [where S = "ball (0::'a) 1" and f = f] bdd_above_norm image_comp
        Elementary_Metric_Spaces.bounded_ball[where x = "0::'a" and e = 1] by metis
    moreover have x_leq: \<open>x \<in> ((norm \<circ> f) ` ball 0 1) \<Longrightarrow> x \<le> (inverse r) * y\<close> for x
    proof-
      assume \<open>x \<in> (norm \<circ> f) ` ball 0 1\<close>
      then obtain t where \<open>t \<in> ball (0::'a) 1\<close> and \<open>x = norm (f t)\<close>
        by auto
      define x' where \<open>x' = r *\<^sub>R x\<close>
      have \<open>x' = r *  norm (f t)\<close>
        by (simp add: \<open>x = norm (f t)\<close> x'_def)
      hence \<open>x' \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1\<close>
        using \<open>t \<in> ball (0::'a) 1\<close> by auto
      hence \<open>x' \<le> y\<close>
        using  \<open>\<And>x. x \<in> ((*\<^sub>R) r \<circ> norm \<circ> f) ` ball 0 1 \<Longrightarrow> x \<le> y\<close> by blast
      thus ?thesis
        unfolding x'_def using \<open>r > 0\<close> by (metis pos_le_divideR_eq real_scaleR_def)
    qed
    ultimately have \<open>Sup ((norm \<circ> f) ` ball 0 1) \<le> (inverse r) * y\<close>
      by (simp add: cSup_least)
    thus ?thesis 
      using \<open>r > 0\<close> by (metis pos_le_divideR_eq real_scaleR_def) 
  qed
  have norm_scaleR: \<open>norm \<circ> ((*\<^sub>R) r) = ((*\<^sub>R) \<bar>r\<bar>) \<circ> (norm::'a \<Rightarrow> real)\<close>
    by auto
  have f_x1: \<open>(f \<circ> ((*\<^sub>R) r)) x = (((*\<^sub>R) r) \<circ> f) x\<close> for x
    using \<open>bounded_linear f\<close> by (simp add: linear_simps(5))
  hence f_x2: \<open>f \<circ> ((*\<^sub>R) r) = ((*\<^sub>R) r) \<circ> f\<close>
    by auto      
  have \<open>ball (0::'a) r = ((*\<^sub>R) r) ` (ball 0 1)\<close>
    (*    using \<open>0 < r\<close> ball_scale by blast *) sorry
  hence \<open>Sup ((norm \<circ> f) ` (ball 0 r)) = Sup ((norm \<circ> f) ` (((*\<^sub>R) r) ` (ball 0 1)))\<close>
    by simp
  also have \<open>\<dots> = Sup ((norm \<circ> f \<circ> ((*\<^sub>R) r)) ` (ball 0 1))\<close>
    using Sup.SUP_image by auto
  also have \<open>\<dots> = Sup ((norm \<circ> ((*\<^sub>R) r) \<circ> f) ` (ball 0 1))\<close>
    using f_x1 f_x2 by (simp add: comp_assoc) 
  also have \<open>\<dots> = Sup ((((*\<^sub>R) \<bar>r\<bar>) \<circ> norm \<circ> f) ` (ball 0 1))\<close>
    using norm_scaleR by auto
  also have \<open>\<dots> = Sup ((((*\<^sub>R) r) \<circ> norm \<circ> f) ` (ball 0 1))\<close>
    using \<open>r > 0\<close> by auto
  also have \<open>\<dots> = r * Sup ((norm \<circ> f) ` (ball 0 1))\<close>
    apply (rule cSup_eq_non_empty) apply simp using s2 apply blast using s3 by blast
  also have \<open>\<dots> = r * onorm f\<close>
    using onorm_f by auto
  finally have \<open>Sup ((norm \<circ> f) ` ball 0 r) = r * onorm f\<close>
    by simp    
  thus ?thesis using \<open>r > 0\<close> by simp
qed

text \<open>                 
  The following lemma is due to Alain Sokal ~\cite{sokal2011reall}.
\<close>
lemma sokal_banach_steinhaus:
  "r > 0 \<Longrightarrow> norm f \<le> Sup ( norm ` blinfun_apply f ` (ball x r) ) / r"   
proof transfer
  fix r::real and f::\<open>'a \<Rightarrow> 'b\<close> and x::'a
  assume \<open>r > 0\<close> and \<open>bounded_linear f\<close>
  have bdd_above_3: \<open>bdd_above ((\<lambda> \<xi>. norm (f \<xi>)) ` (ball 0 r))\<close>
  proof -
    obtain M where \<open>\<And> \<xi>. norm (f \<xi>) \<le> M * norm \<xi>\<close> and \<open>M \<ge> 0\<close>
      using \<open>bounded_linear f\<close> 
      by (metis bounded_linear.nonneg_bounded semiring_normalization_rules(7))
    hence \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f \<xi>) \<le> M * r\<close>
      using \<open>r > 0\<close> by (smt mem_ball_0 mult_left_mono) 
    thus ?thesis
      by (meson bdd_aboveI2)     
  qed
  have bdd_above_2: \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close>
  proof-
    have \<open>ball (0::'a) r \<noteq> {}\<close>
      using \<open>0 < r\<close> by auto          
    moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f x)) ` (ball 0 r))\<close>
      by auto          
    moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f \<xi>)) ` (ball 0 r))\<close>
      using bdd_above_3 by blast
    ultimately have \<open>bdd_above ((\<lambda> \<xi>. norm (f x) + norm (f \<xi>)) ` (ball 0 r))\<close>
      using bdd_above_plus[where S = "ball (0::'a) r" and f = "\<lambda> \<xi>. norm (f x)" 
          and g = "\<lambda> \<xi>. norm (f \<xi>)"] by simp
    then obtain M where \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f x) + norm (f \<xi>) \<le> M\<close>
      unfolding bdd_above_def by (meson image_eqI)
    moreover have \<open>norm (f (x + \<xi>)) \<le> norm (f x) + norm (f \<xi>)\<close> for \<xi>
      by (simp add: \<open>bounded_linear f\<close> linear_simps(1) norm_triangle_ineq)          
    ultimately have \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> M\<close>
      by (simp add:  \<open>bounded_linear f\<close> linear_simps(1) norm_triangle_le)          
    thus ?thesis
      by (meson bdd_aboveI2)                          
  qed 
  have bdd_above_4: \<open>bdd_above ((\<lambda> \<xi>. norm (f (x - \<xi>))) ` (ball 0 r))\<close>
  proof-
    obtain K where K_def: \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> K\<close>
      using  \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close> unfolding bdd_above_def 
      by (meson image_eqI)
    have \<open>\<xi> \<in> ball (0::'a) r \<Longrightarrow> -\<xi> \<in> ball 0 r\<close> for \<xi>
      by auto
    thus ?thesis
      by (metis K_def ab_group_add_class.ab_diff_conv_add_uminus bdd_aboveI2)
  qed

  have bdd_above_1: \<open>bdd_above ((\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) ` (ball 0 r))\<close>
  proof-
    have \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close>
      using bdd_above_2 by blast
    moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f (x - \<xi>))) ` (ball 0 r))\<close>
      using bdd_above_4 by blast
    ultimately show ?thesis
      unfolding max_def apply auto apply (meson bdd_above_Int1 bdd_above_mono image_Int_subset)
      by (meson bdd_above_Int1 bdd_above_mono image_Int_subset)   
  qed 

  have bdd_above_6: \<open>bdd_above ((norm \<circ> f) ` ball x r)\<close>
  proof-
    have \<open>bounded (ball x r)\<close>
      by simp            
    hence \<open>bounded ((norm \<circ> f) ` ball x r)\<close>
      using \<open>bounded_linear f\<close> bounded_linear_image bounded_norm_comp by auto
    thus ?thesis
      by (simp add: bounded_imp_bdd_above)
  qed

  have norm_1: \<open>(\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r = (norm \<circ> f) ` ball x r\<close>
  proof-
    have "(\<lambda>a. norm (f (x + a))) ` ball 0 r = (\<lambda>a. (norm \<circ> f) (x + a)) ` ball 0 r"
      by (metis comp_apply)
    thus ?thesis
      by (metis (no_types) add.left_neutral image_add_ball image_image)
  qed 

  have bdd_above_5: \<open>bdd_above ((\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r)\<close>
  proof-
    have \<open>(\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r = (norm \<circ> f) ` ball x r\<close>
      using norm_1 by blast
    moreover have \<open>bdd_above ((norm \<circ> f) ` ball x r)\<close>
      using bdd_above_6 by blast
    ultimately show ?thesis 
      by simp
  qed 

  have norm_2: \<open>norm \<xi> < r \<Longrightarrow> norm (f (x - \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close> for \<xi>
  proof-
    assume \<open>norm \<xi> < r\<close>
    hence \<open>\<xi> \<in> ball (0::'a) r\<close>
      by auto
    hence \<open>-\<xi> \<in> ball (0::'a) r\<close>
      by auto
    thus ?thesis 
      by (metis (no_types, lifting) ab_group_add_class.ab_diff_conv_add_uminus image_iff) 
  qed
  have norm_2': \<open>norm \<xi> < r \<Longrightarrow> norm (f (x + \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r\<close> for \<xi>
  proof-
    assume \<open>norm \<xi> < r\<close>
    hence \<open>\<xi> \<in> ball (0::'a) r\<close>
      by auto
    hence \<open>-\<xi> \<in> ball (0::'a) r\<close>
      by auto
    thus ?thesis 
      by (metis (no_types, lifting) diff_minus_eq_add image_iff)          
  qed

  have bdd_above_6: \<open>bdd_above ((\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r)\<close>
  proof-
    have \<open>(\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r = (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close>
      apply auto using norm_2 apply auto using norm_2' by auto 
    thus ?thesis
      using bdd_above_4 by blast       
  qed   

  have Sup_2: \<open>(SUP \<xi>\<in>ball 0 r. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) =
                 max (SUP \<xi>\<in>ball 0 r. norm (f (x + \<xi>))) (SUP \<xi>\<in>ball 0 r. norm (f (x - \<xi>)))\<close>
  proof-
    have \<open>ball (0::'a) r \<noteq> {}\<close>
      using \<open>r > 0\<close> by auto
    moreover have \<open>bdd_above ((\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r)\<close>
      using bdd_above_5 by blast
    moreover have \<open>bdd_above ((\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r)\<close>
      using bdd_above_6 by blast
    ultimately show ?thesis
      using max_Sup[where X = "ball (0::'a) r" and f = "\<lambda> \<xi>. (norm (f (x + \<xi>)))" 
          and g = "\<lambda> \<xi>. (norm (f (x - \<xi>)))"] by blast    
  qed 

  have Sup_3': \<open>norm \<xi> < r \<Longrightarrow> norm (f (x + \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r\<close> for \<xi>::'a
  proof-
    assume \<open>norm \<xi> < r\<close>
    have \<open>norm (f (x + \<xi>)) = norm (f (x - (- \<xi>)))\<close>
      by simp
    moreover have \<open>-\<xi> \<in> ball 0 r\<close>
      by (simp add: \<open>norm \<xi> < r\<close>)            
    ultimately show ?thesis
      by blast
  qed

  have Sup_3'': \<open>norm \<xi> < r \<Longrightarrow> norm (f (x - \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close>  for \<xi>::'a
  proof-
    assume \<open>norm \<xi> < r\<close>
    have \<open>norm (f (x - \<xi>)) = norm (f (x + (- \<xi>)))\<close>
      by simp
    moreover have \<open>-\<xi> \<in> ball 0 r\<close>
      by (simp add: \<open>norm \<xi> < r\<close>)            
    ultimately show ?thesis
      by blast
  qed

  have Sup_3: \<open>max (SUP \<xi>\<in>ball 0 r. norm (f (x + \<xi>))) (SUP \<xi>\<in>ball 0 r. norm (f (x - \<xi>))) =
        (SUP \<xi>\<in>ball 0 r. norm (f (x + \<xi>)))\<close>
  proof-
    have \<open>(\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r) = (\<lambda> \<xi>. (norm (f (x - \<xi>)))) ` (ball 0 r)\<close>
      apply auto using Sup_3' apply auto using Sup_3'' by blast
    hence \<open>Sup ((\<lambda> \<xi>.(norm (f (x + \<xi>)))) ` (ball 0 r))=Sup ((\<lambda> \<xi>.(norm (f (x - \<xi>)))) ` (ball 0 r))\<close>
      by simp
    thus ?thesis 
      by auto
  qed

  have Sup_1: \<open>Sup ((norm \<circ> f) ` (ball 0 r)) \<le> Sup ( (\<lambda> \<xi>. norm (f \<xi>)) ` (ball x r) )\<close> 
  proof-
    have \<open>(norm \<circ> f) \<xi> \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close> for \<xi>
      using linear_plus_norm \<open>bounded_linear f\<close> 
      by (simp add: linear_plus_norm bounded_linear.linear)
    moreover have \<open>bdd_above ((\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) ` (ball 0 r))\<close> 
      using bdd_above_1 by blast
    moreover have \<open>ball (0::'a) r \<noteq> {}\<close>
      using \<open>r > 0\<close> by auto      
    ultimately have \<open>Sup ((norm \<circ> f) ` (ball 0 r)) \<le>
                     Sup ((\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) ` (ball 0 r))\<close>
      using cSUP_mono[where A = "ball (0::'a) r" and B = "ball (0::'a) r" and f = "norm \<circ> f" and 
          g = "\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))"] by blast
    also have \<open>\<dots> = max (Sup ((\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r)))
                        (Sup ((\<lambda> \<xi>. (norm (f (x - \<xi>)))) ` (ball 0 r)))\<close> 
      using Sup_2 by blast
    also have \<open>\<dots> = Sup ((\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r))\<close>
      using Sup_3 by blast
    also have \<open>\<dots> = Sup ((\<lambda> \<xi>. (norm (f \<xi>))) ` (ball x r))\<close>
      by (metis  add.right_neutral ball_translation image_image)      
    finally show ?thesis by blast
  qed

  have \<open>onorm f = (inverse r) * Sup ((norm \<circ> f) ` (ball 0 r))\<close>
    using \<open>0 < r\<close> \<open>bounded_linear f\<close> onorm_r by blast
  moreover have \<open>Sup ((norm \<circ> f) ` (ball 0 r)) \<le> Sup ( (\<lambda> \<xi>. norm (f \<xi>)) ` (ball x r) )\<close>
    using Sup_1 by blast
  ultimately have \<open>onorm f \<le> inverse r * Sup ((norm \<circ> f) ` ball x r)\<close>
    by (simp add: \<open>r > 0\<close>)    
  thus \<open>onorm f \<le> Sup (norm ` f ` ball x r) / r\<close>
    using \<open>r > 0\<close> by (simp add: Sup.SUP_image divide_inverse_commute)
qed

text \<open>                 
  In the proof of Banach-Steinhaus theorem, we will use the following variation of
  the lemma @{thm sokal_banach_steinhaus}.
\<close>

thm blinfun_apply

lemma sokal_banach_steinhaus':
  "\<lbrakk>r > 0; \<tau> < 1; f \<noteq> 0\<rbrakk> \<Longrightarrow> \<exists>\<xi>\<in>ball x r.  \<tau> * r * norm f \<le> norm (blinfun_apply f \<xi>)"
proof-
  assume \<open>r > 0\<close> and \<open>\<tau> < 1\<close> and \<open>f \<noteq> 0\<close>
  have  \<open>norm f > 0\<close>
    using \<open>f \<noteq> 0\<close> by auto
  have \<open>norm f \<le> (inverse r) * Sup ( (norm \<circ> ( blinfun_apply f)) ` (ball x r) )\<close>
    using \<open>r > 0\<close> sokal_banach_steinhaus by (metis Inf.INF_image divide_inverse_commute) 
  hence \<open>r * norm f \<le> r * (inverse r) * Sup ( (norm \<circ> (blinfun_apply f)) ` (ball x r) )\<close>
    using \<open>r > 0\<close> by (smt linordered_field_class.sign_simps(4) mult_left_less_imp_less) 
  hence \<open>r * norm f \<le> Sup ( (norm \<circ> (blinfun_apply f)) ` (ball x r) )\<close>
    using \<open>0 < r\<close> by auto
  moreover have \<open>\<tau> * r * norm f < r * norm f\<close>
    using  \<open>\<tau> < 1\<close> using \<open>0 < norm f\<close> \<open>0 < r\<close> by auto
  ultimately have \<open>\<tau> * r * norm f < Sup ( (norm \<circ> (blinfun_apply f)) ` (ball x r) )\<close>
    by simp
  moreover have \<open>(norm \<circ> ( blinfun_apply f)) ` (ball x r) \<noteq> {}\<close>
    using \<open>0 < r\<close> by auto    
  moreover have \<open>bdd_above ((norm \<circ> ( blinfun_apply f)) ` (ball x r))\<close>
    using \<open>0 < r\<close> apply transfer by (meson bounded_linear_ball_bdd_above)    
  ultimately have \<open>\<exists>t \<in> (norm \<circ> ( blinfun_apply f)) ` (ball x r). \<tau> * r * norm f < t\<close> 
    by (simp add: less_cSup_iff)    
  thus ?thesis by (smt comp_def image_iff) 
qed

subsection \<open>Banach-Steinhaus theorem\<close>

theorem banach_steinhaus:
  \<open>\<lbrakk>\<And>x. bounded (range (\<lambda>n. blinfun_apply (f n) x))\<rbrakk> \<Longrightarrow> bounded (range f)\<close>
  for f::\<open>'c \<Rightarrow> ('a::banach \<Rightarrow>\<^sub>L 'b::real_normed_vector)\<close>
proof-
  assume \<open>\<And>x. bounded (range (\<lambda>n. blinfun_apply (f n) x))\<close>
  show ?thesis proof(rule classical)
    assume \<open>\<not>(bounded (range f))\<close>
    have sum_1: \<open>\<exists>K. \<forall>n. sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> K\<close>
    proof-
      have \<open>summable (\<lambda>n. (inverse (real_of_nat 3))^n)\<close>
        using Series.summable_geometric_iff [where c = "inverse (real_of_nat 3)"] by auto
      moreover have \<open>(inverse (real_of_nat 3))^n = inverse (real_of_nat 3^n)\<close> for n::nat
        using power_inverse by blast        
      ultimately have \<open>summable (\<lambda>n. inverse (real_of_nat 3^n))\<close>
        by auto
      hence \<open>bounded (range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n}))\<close>
        using summable_imp_sums_bounded[where f = "(\<lambda>n. inverse (real_of_nat 3^n))"]
          lessThan_atLeast0 by auto
      hence \<open>\<exists>M. \<forall>h\<in>(range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n})). norm h \<le> M\<close>
        using bounded_iff by blast
      then obtain M where \<open>h\<in>range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n}) \<Longrightarrow> norm h \<le> M\<close> 
        for h
        by blast      
      have sum_2: \<open>sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> M\<close> for n
      proof-
        have  \<open>norm (sum (\<lambda> k. inverse (real 3 ^ k)) {0..< Suc n}) \<le> M\<close>
          using \<open>\<And>h. h\<in>(range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n})) \<Longrightarrow> norm h \<le> M\<close> 
          by blast
        hence  \<open>norm (sum (\<lambda> k. inverse (real 3 ^ k)) {0..n}) \<le> M\<close>
          by (simp add: atLeastLessThanSuc_atLeastAtMost)        
        hence  \<open>(sum (\<lambda> k. inverse (real 3 ^ k)) {0..n}) \<le> M\<close>
          by auto
        thus ?thesis  by blast
      qed
      have \<open>sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> M\<close> for n 
        using sum_2 by blast
      thus ?thesis  by blast
    qed
    have \<open>of_rat 2/3 < (1::real)\<close>
      by auto
    hence \<open>\<forall>g::'a \<Rightarrow>\<^sub>L 'b. \<forall>x. \<forall>r. \<exists>\<xi>. g \<noteq> 0 \<and> r > 0
               \<longrightarrow> (\<xi>\<in>ball x r \<and> (of_rat 2/3) * r * norm g \<le> norm (blinfun_apply g \<xi>))\<close> 
      using sokal_banach_steinhaus' by blast
    hence \<open>\<exists>\<xi>. \<forall>g::'a \<Rightarrow>\<^sub>L 'b. \<forall>x. \<forall>r. g \<noteq> 0 \<and> r > 0
           \<longrightarrow> ((\<xi> g x r)\<in>ball x r \<and> (of_rat 2/3) * r * norm g \<le> norm (blinfun_apply g (\<xi> g x r)))\<close> 
      by metis
    then obtain \<xi> where f1: \<open>\<lbrakk>g \<noteq> 0; r > 0\<rbrakk> \<Longrightarrow> 
        \<xi> g x r \<in> ball x r \<and>  (of_rat 2/3) * r * norm g \<le> norm (blinfun_apply g (\<xi> g x r))\<close>
      for g::\<open>'a \<Rightarrow>\<^sub>L 'b\<close> and x and r
      by blast
    have \<open>\<forall>n. \<exists>k. norm (f k) \<ge> 4^n\<close>
      using \<open>\<not>(bounded (range f))\<close> by (metis (mono_tags, hide_lams) boundedI image_iff linear)
    hence  \<open>\<exists>k. \<forall>n. norm (f (k n)) \<ge> 4^n\<close>
      by metis
    hence  \<open>\<exists>k. \<forall>n. norm ((f \<circ> k) n) \<ge> 4^n\<close>
      by simp
    then obtain k where \<open>norm ((f \<circ> k) n) \<ge> 4^n\<close> for n
      by blast
    define T where \<open>T = f \<circ> k\<close>
    have \<open>T n \<in> range f\<close> for n
      unfolding T_def by simp        
    have \<open>norm (T n) \<ge> of_nat (4^n)\<close> for n
      unfolding T_def using \<open>\<And> n. norm ((f \<circ> k) n) \<ge> 4^n\<close> by auto
    hence \<open>T n \<noteq> 0\<close> for n
      by (smt T_def \<open>\<And>n. 4 ^ n \<le> norm ((f \<circ> k) n)\<close> norm_zero power_not_zero zero_le_power)
    have \<open>inverse (of_nat 3^n) > (0::real)\<close> for n
      by auto
    define y::\<open>nat \<Rightarrow> 'a\<close> where \<open>y = rec_nat 0 (\<lambda>n x. \<xi> (T n) x (inverse (of_nat 3^n)))\<close>
    have \<open>y (Suc n) \<in> ball (y n) (inverse (of_nat 3^n))\<close> for n
      using f1 \<open>\<And> n. T n \<noteq> 0\<close> \<open>\<And> n. inverse (of_nat 3^n) > 0\<close> unfolding y_def by auto
    hence \<open>norm (y (Suc n) - y n) \<le> inverse (of_nat 3^n)\<close> for n
      unfolding ball_def apply auto using dist_norm by (smt norm_minus_commute) 
    moreover have \<open>\<exists>K. \<forall>n. sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> K\<close>
      using sum_1 by blast
    moreover have \<open>Cauchy y\<close>
      using convergent_series_Cauchy[where a = "\<lambda>n. inverse (of_nat 3^n)" and \<phi> = y] dist_norm
      by (metis calculation(1) calculation(2))
    hence \<open>\<exists> x. y \<longlonglongrightarrow> x\<close>
      by (simp add: convergent_eq_Cauchy)
    then obtain x where \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    have norm_2: \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close> for n
    proof-
      have \<open>inverse (real_of_nat 3) < 1\<close>
        by simp        
      moreover have \<open>y 0 = 0\<close>
        using y_def by auto
      ultimately have \<open>norm (x - y (Suc n)) 
    \<le> (inverse (of_nat 3)) * inverse (1 - (inverse (of_nat 3))) * ((inverse (of_nat 3)) ^ n)\<close>
        using bound_Cauchy_to_lim[where c = "inverse (of_nat 3)" and y = y and x = x]
          power_inverse semiring_norm(77)  \<open>y \<longlonglongrightarrow> x\<close>
          \<open>\<And> n. norm (y (Suc n) - y n) \<le> inverse (of_nat 3^n)\<close> by (metis divide_inverse)
      moreover have \<open>inverse (real_of_nat 3) * inverse (1 - (inverse (of_nat 3)))
                   = inverse (of_nat 2)\<close>
        by auto
      ultimately show ?thesis 
        by (metis power_inverse) 
    qed
    have \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close> for n
      using norm_2 by blast
    have \<open>\<exists> M. \<forall> n. norm (blinfun_apply (T n) x) \<le> M\<close>
      unfolding T_def apply auto
      by (metis \<open>\<And>x. bounded (range (\<lambda>n. blinfun_apply (f n) x))\<close> bounded_iff rangeI)
    then obtain M where \<open>norm (blinfun_apply (T n) x) \<le> M\<close> for n
      by blast
    have norm_1: \<open>norm (T n) * norm (y (Suc n) - x) + norm (blinfun_apply (T n) x)
       \<le> inverse (real 2) * inverse (real 3 ^ n) * norm (T n) + norm (blinfun_apply (T n) x)\<close> for n
    proof-   
      have \<open>norm (y (Suc n) - x) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close>
        using \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close> 
        by (simp add: norm_minus_commute)
      moreover have \<open>norm (T n) \<ge> 0\<close>
        by auto
      ultimately have \<open>norm (T n) * norm (y (Suc n) - x) 
                     \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))*norm (T n)\<close>
        by (simp add: \<open>\<And>n. T n \<noteq> 0\<close>)
      thus ?thesis by simp      
    qed 
    have inverse_2: \<open>(inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n) 
                  \<le> norm (blinfun_apply (T n) x)\<close> for n
    proof-
      have \<open>(of_rat 2/3)*(inverse (of_nat 3^n))*norm (T n) \<le> norm (blinfun_apply (T n) (y (Suc n)))\<close> 
        using f1 \<open>\<And> n. T n \<noteq> 0\<close> \<open>\<And> n. inverse (of_nat 3^n) > 0\<close> unfolding y_def by auto
      also have \<open>\<dots> = norm (blinfun_apply (T n) ((y (Suc n) - x) + x))\<close>
        by auto
      also have \<open>\<dots> = norm (blinfun_apply (T n) (y (Suc n) - x) + blinfun_apply (T n) x)\<close>
        apply transfer apply auto by (metis diff_add_cancel linear_simps(1))
      also have \<open>\<dots> \<le> norm (blinfun_apply (T n) (y (Suc n) - x)) + norm (blinfun_apply (T n) x)\<close>
        by (simp add: norm_triangle_ineq)
      also have \<open>\<dots> \<le> norm (T n) * norm (y (Suc n) - x) + norm (blinfun_apply (T n) x)\<close>
        apply transfer apply auto using onorm by auto 
      also have \<open>\<dots> \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))*norm (T n) 
                + norm (blinfun_apply (T n) x)\<close>
        using norm_1 by blast
      finally have \<open>(of_rat 2/3) * inverse (real 3 ^ n) * norm (T n)
                \<le> inverse (real 2) * inverse (real 3 ^ n) * norm (T n) 
                + norm (blinfun_apply (T n) x)\<close>
        by blast
      hence \<open>(of_rat 2/3) * inverse (real 3 ^ n) * norm (T n) 
             - inverse (real 2) * inverse (real 3 ^ n) * norm (T n) \<le> norm (blinfun_apply (T n) x)\<close>
        by linarith
      thus ?thesis
        by (simp add: linordered_field_class.sign_simps(5))
    qed
    have inverse_3: \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) 
                    \<le> (inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n)\<close> for n
    proof-
      have \<open>of_rat (4/3)^n = inverse (real 3 ^ n) * (of_nat 4^n)\<close>
        apply auto by (metis divide_inverse_commute of_rat_divide power_divide of_rat_numeral_eq) 
      also have \<open>\<dots> \<le>  inverse (real 3 ^ n) * norm (T n)\<close>
        using \<open>\<And>n. norm (T n) \<ge> of_nat (4^n)\<close> by simp
      finally have \<open>of_rat (4/3)^n \<le> inverse (real 3 ^ n) * norm (T n)\<close>
        by blast
      moreover have \<open>inverse (of_nat 6) > (0::real)\<close>
        by auto
      ultimately show ?thesis by auto
    qed
    have inverse_1: \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> M\<close> for n
    proof-
      have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) 
          \<le> (inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n)\<close> 
        using inverse_3 by blast
      also have \<open>\<dots> \<le> norm (blinfun_apply (T n) x)\<close> 
        using inverse_2 by blast
      finally have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> norm (blinfun_apply (T n) x)\<close>
        by auto
      thus ?thesis 
        using \<open>\<And> n. norm (blinfun_apply (T n) x) \<le> M\<close> by smt
    qed

    have \<open>\<exists>n. M < (inverse (of_nat 6)) * (of_rat (4/3)^n)\<close>
      by (simp add: Elementary_Topology.real_arch_pow)
    moreover have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> M\<close> for n
      using inverse_1 by blast                      
    ultimately show ?thesis
      by smt
  qed
qed

subsection \<open>A consequence of Banach-Steinhaus theorem\<close>
text\<open>
  An important consequence of Banach-Steinhaus theorem is that if a sequence of bounded operators 
  converges pointwise, then the limit is a bounded operator too.
\<close>

text\<open>Pointwise convergence\<close>
definition pointwise_convergent_to :: 
  \<open>( nat \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) ) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close> 
  (\<open>((_)/ \<midarrow>pointwise\<rightarrow> (_))\<close> [60, 60] 60) where
  \<open>pointwise_convergent_to x l = (\<forall> t::'a. (\<lambda> n. (x n) t) \<longlonglongrightarrow> l t)\<close>

lemma linear_limit_linear:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_vector \<Rightarrow> 'b::real_normed_vector)\<close> and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. linear (f n)\<close> and \<open>f \<midarrow>pointwise\<rightarrow> F\<close>
  shows \<open>linear F\<close>
proof
  show "F (x + y) = F x + F y" for x :: 'a and y :: 'a
  proof-
    have "\<forall>a. F a = lim (\<lambda>n. f n a)"
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by (metis (full_types) limI)
    moreover have "\<forall>f b ba fa. (lim (\<lambda>n. fa n + f n) = (b::'b) + ba \<or> \<not> f \<longlonglongrightarrow> ba) \<or> \<not> fa \<longlonglongrightarrow> b"
      by (metis (no_types) limI tendsto_add)
    moreover have "\<And>a. (\<lambda>n. f n a) \<longlonglongrightarrow> F a"
      using assms(2) pointwise_convergent_to_def by force
    ultimately have lim_sum: \<open>lim (\<lambda> n. (f n) x + (f n) y) = lim (\<lambda> n. (f n) x) + lim (\<lambda> n. (f n) y)\<close>
      by metis
    have \<open>(f n) (x + y) = (f n) x + (f n) y\<close> for n
      using \<open>\<And> n.  linear (f n)\<close> unfolding linear_def using Real_Vector_Spaces.linear_iff assms(1) 
      by auto
    hence \<open>lim (\<lambda> n. (f n) (x + y)) = lim (\<lambda> n. (f n) x + (f n) y)\<close>
      by simp
    hence \<open>lim (\<lambda> n. (f n) (x + y)) = lim (\<lambda> n. (f n) x) + lim (\<lambda> n. (f n) y)\<close>
      using lim_sum by simp
    moreover have \<open>(\<lambda> n. (f n) (x + y)) \<longlonglongrightarrow> F (x + y)\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by blast
    moreover have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by blast
    moreover have \<open>(\<lambda> n. (f n) y) \<longlonglongrightarrow> F y\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by blast
    ultimately show ?thesis
      by (metis limI) 
  qed
  show "F (r *\<^sub>R x) = r *\<^sub>R F x" for r :: real and x :: 'a
  proof-
    have \<open>(f n) (r *\<^sub>R x) = r *\<^sub>R (f n) x\<close> for n
      using  \<open>\<And> n.  linear (f n)\<close> 
      by (simp add: Real_Vector_Spaces.linear_def real_vector.linear_scale)
    hence \<open>lim (\<lambda> n. (f n) (r *\<^sub>R x)) = lim (\<lambda> n. r *\<^sub>R (f n) x)\<close>
      by simp
    have \<open>convergent (\<lambda> n. (f n) x)\<close>
      by (metis assms(2) convergentI pointwise_convergent_to_def)
    moreover have \<open>isCont (\<lambda> t::'b. r *\<^sub>R t) tt\<close> for tt
      by (simp add: bounded_linear_scaleR_right)
    ultimately have \<open>lim (\<lambda> n. r *\<^sub>R ((f n) x)) =  r *\<^sub>R lim (\<lambda> n. (f n) x)\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def 
      by (metis (mono_tags) isCont_tendsto_compose limI)
    hence \<open>lim (\<lambda> n.  (f n) (r *\<^sub>R x)) = r *\<^sub>R lim (\<lambda> n. (f n) x)\<close> 
      using \<open>lim (\<lambda> n. (f n) (r *\<^sub>R x)) = lim (\<lambda> n. r *\<^sub>R (f n) x)\<close> by simp
    moreover have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by blast
    moreover have \<open>(\<lambda> n.  (f n) (r *\<^sub>R x)) \<longlonglongrightarrow> F (r *\<^sub>R x)\<close>
      using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> unfolding pointwise_convergent_to_def by blast
    ultimately show ?thesis
      by (metis limI) 
  qed
qed

corollary bounded_linear_limit_bounded_linear:
  fixes f::\<open>nat \<Rightarrow> ('a::banach \<Rightarrow>\<^sub>L 'b::real_normed_vector)\<close>
  assumes \<open>\<And>x. convergent (\<lambda>n. blinfun_apply (f n) x)\<close>
  shows  \<open>\<exists>g. (\<lambda>n. blinfun_apply (f n)) \<midarrow>pointwise\<rightarrow> blinfun_apply g\<close>
proof-
  have \<open>\<exists>l. (\<lambda>n. blinfun_apply (f n) x) \<longlonglongrightarrow> l\<close> for x
    by (simp add:  \<open>\<And>x. convergent (\<lambda>n. blinfun_apply (f n) x)\<close> convergentD)
  hence \<open>\<exists>F. (\<lambda>n. blinfun_apply (f n)) \<midarrow>pointwise\<rightarrow> F\<close>
    unfolding pointwise_convergent_to_def by metis
  obtain F where \<open>(\<lambda>n. blinfun_apply (f n)) \<midarrow>pointwise\<rightarrow> F\<close>
    using \<open>\<exists>F. (\<lambda>n. blinfun_apply (f n)) \<midarrow>pointwise\<rightarrow> F\<close> by auto
  have \<open>\<And>x. (\<lambda> n. blinfun_apply (f n) x) \<longlonglongrightarrow> F x\<close>
    using \<open>(\<lambda>n. blinfun_apply (f n)) \<midarrow>pointwise\<rightarrow> F\<close> apply transfer
    by (simp add: pointwise_convergent_to_def)
  have norm_f_n: \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
  proof-
    have \<open>bounded (range f)\<close>
      using \<open>\<And>x. convergent (\<lambda>n. blinfun_apply (f n) x)\<close> banach_steinhaus
        \<open>\<And>x. \<exists>l. (\<lambda>n. blinfun_apply (f n) x) \<longlonglongrightarrow> l\<close> convergent_imp_bounded by blast
    thus ?thesis  unfolding bounded_def
      by (meson UNIV_I \<open>bounded (range f)\<close> bounded_iff image_eqI) 
  qed
  have norm_f_n_x: \<open>\<exists> M. \<forall> n. norm (blinfun_apply (f n) x) \<le> M\<close> for x
  proof-
    have \<open>isCont (\<lambda> t::'b. norm t) y\<close> for y::'b
      using Limits.isCont_norm by simp
    hence \<open>(\<lambda> n. norm (blinfun_apply (f n) x)) \<longlonglongrightarrow> (norm (F x))\<close>
      using \<open>\<And> x::'a. (\<lambda> n. blinfun_apply (f n) x) \<longlonglongrightarrow> F x\<close> by (simp add: tendsto_norm)
    thus ?thesis  
      using Elementary_Metric_Spaces.convergent_imp_bounded
      by (metis UNIV_I \<open>\<And> x::'a. (\<lambda> n. blinfun_apply (f n) x) \<longlonglongrightarrow> F x\<close> bounded_iff image_eqI)
  qed
  have norm_f: \<open>\<exists>K. \<forall>n. \<forall>x. norm (blinfun_apply (f n) x) \<le> norm x * K\<close>
  proof-
    have \<open>\<exists> M. \<forall> n. norm (blinfun_apply (f n) x) \<le> M\<close> for x
      using norm_f_n_x  \<open>\<And>x. (\<lambda>n. blinfun_apply (f n) x) \<longlonglongrightarrow> F x\<close> by blast
    hence \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
      using norm_f_n by simp 
    then obtain M::real where \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
      by blast
    have \<open>\<forall> n. \<forall>x. norm (blinfun_apply (f n) x) \<le> norm x * norm (f n)\<close>
      apply transfer apply auto by (metis mult.commute onorm) 
    thus  ?thesis using \<open>\<exists> M. \<forall> n. norm (f n) \<le> M\<close>
      by (metis (no_types, hide_lams) dual_order.trans norm_eq_zero order_refl real_mult_le_cancel_iff2 vector_space_over_itself.scale_zero_left zero_less_norm_iff)
  qed 
  have norm_F_x: \<open>\<exists>K. \<forall>x. norm (F x) \<le> norm x * K\<close>
  proof-
    have "\<exists>K. \<forall>n. \<forall>x. norm (blinfun_apply (f n) x) \<le> norm x * K"
      using norm_f \<open>\<And>x. (\<lambda>n. blinfun_apply (f n) x) \<longlonglongrightarrow> F x\<close> by auto
    thus ?thesis
      using  \<open>\<And> x::'a. (\<lambda> n. blinfun_apply (f n)  x) \<longlonglongrightarrow> F x\<close> apply transfer 
      by (metis Lim_bounded tendsto_norm)   
  qed
  have \<open>linear F\<close>
  proof(rule linear_limit_linear)
    show \<open>linear (blinfun_apply (f n))\<close> for n
      apply transfer apply auto by (simp add: bounded_linear.linear) 
    show \<open>f \<midarrow>pointwise\<rightarrow> F\<close>
      using \<open>(\<lambda>n. blinfun_apply (f n)) \<midarrow>pointwise\<rightarrow> F\<close> by auto
  qed
  moreover have \<open>bounded_linear_axioms F\<close>
    using norm_F_x by (simp add: \<open>\<And>x. (\<lambda>n. blinfun_apply (f n) x) \<longlonglongrightarrow> F x\<close> bounded_linear_axioms_def) 
  ultimately have \<open>bounded_linear F\<close> 
    unfolding bounded_linear_def by blast
  hence \<open>\<exists>g. blinfun_apply g = F\<close>
    using bounded_linear_Blinfun_apply by auto
  thus ?thesis
    using \<open>(\<lambda>n. blinfun_apply (f n)) \<midarrow>pointwise\<rightarrow> F\<close> apply transfer by auto
qed


end

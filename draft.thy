

fun partial_span::\<open>nat \<Rightarrow> ('a::complex_vector) set \<Rightarrow> ('a::complex_vector) set\<close> where
  \<open>partial_span 0 S = {0}\<close>|
  \<open>partial_span (Suc n) S = {x + a *\<^sub>C y | a x y. x \<in> partial_span n S \<and> y \<in> S}\<close>


lemma partial_span_1:
  \<open>S \<subseteq> partial_span 1 S\<close>
proof-
  have \<open>partial_span 0 S = {0}\<close>
    by auto
  moreover have \<open>partial_span (Suc 0) S = {x + a *\<^sub>C y | a x y. x \<in> partial_span 0 S \<and> y \<in> S}\<close>
    by auto
  ultimately have \<open>partial_span (Suc 0) S = {a *\<^sub>C y | a y. y \<in> S}\<close>
    by auto 
  also have \<open>{a *\<^sub>C y | a y. y \<in> S} \<supseteq> {1 *\<^sub>C y | y. y \<in> S}\<close>
    by blast
  also have \<open>{1 *\<^sub>C y | y. y \<in> S} = S\<close>
    by simp
  finally have \<open>partial_span (Suc 0) S \<supseteq> S\<close>
    by blast
  thus ?thesis
    by simp 
qed


lemma partial_span_lim_n:
  fixes S::\<open>'a::complex_vector set\<close>
  shows \<open>partial_span n S \<subseteq> complex_vector.span S\<close>
proof(induction n)
  case 0
  thus ?case
    using complex_vector.span_mono by force 
next
  case (Suc n)
  have \<open>x \<in> partial_span (Suc n) S \<Longrightarrow> x \<in> complex_vector.span S\<close>
    for x
  proof-
    assume \<open>x \<in> partial_span (Suc n) S\<close>
    hence \<open>x \<in> {t + a *\<^sub>C y | a t y. t \<in> partial_span n S \<and> y \<in> S}\<close>
      by simp
    then obtain a t y where \<open>x = t + a *\<^sub>C y\<close> and \<open>t \<in> partial_span n S\<close>
      and \<open>y \<in> S\<close>
      by blast
    have \<open>t \<in> complex_vector.span S\<close>
      using Suc.IH \<open>t \<in> partial_span n S\<close> by auto
    moreover have \<open>a *\<^sub>C y \<in> complex_vector.span S\<close>
    proof-
      have \<open>y \<in> complex_vector.span S\<close>
        using \<open>y \<in> S\<close>
        by (simp add: complex_vector.span_base) 
      thus ?thesis
        by (simp add: complex_vector.span_scale) 
    qed
    ultimately show ?thesis
      by (simp add: \<open>x = t + a *\<^sub>C y\<close> complex_vector.span_add) 
  qed
  thus ?case
    by blast 
qed


lemma sum_partial_span_eq:
  fixes S::\<open>'a::complex_vector set\<close>
  assumes  \<open>S \<noteq> {}\<close>
  shows \<open>\<forall> r s. \<exists> p::nat. r \<in> partial_span n S \<longrightarrow> s \<in> partial_span n S
 \<longrightarrow> r + s \<in> partial_span (n+p) S\<close>
proof(induction n)
  case 0
  have  \<open>r \<in> partial_span 0 S \<Longrightarrow> s \<in> partial_span 0 S \<Longrightarrow> r + s \<in> partial_span (Suc 0) S\<close>
    for r s
  proof-
    assume \<open>r \<in> partial_span 0 S\<close> and \<open>s \<in> partial_span 0 S\<close>
    from  \<open>r \<in> partial_span 0 S\<close>
    have \<open>r = 0\<close>
      by simp
    from  \<open>s \<in> partial_span 0 S\<close>
    have \<open>s = 0\<close>
      by simp
    have \<open>r + s = 0\<close>
      by (simp add: \<open>r = 0\<close> \<open>s = 0\<close>)
    have \<open>partial_span (Suc 0) S = {x + a *\<^sub>C y | a x y. x \<in> partial_span 0 S \<and> y \<in> S}\<close>
      by simp
    have \<open>\<exists> w. w \<in> S\<close>
      using \<open>S \<noteq> {}\<close>
      by blast
    then obtain w where \<open>w \<in> S\<close>
      by blast
    have \<open>r + 0 *\<^sub>C w \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span 0 S \<and> y \<in> S}\<close>
      using \<open>r \<in>  partial_span 0 S\<close> \<open>w \<in> S\<close> by blast
    hence \<open>0 \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span 0 S \<and> y \<in> S}\<close>
      by (simp add: \<open>r = 0\<close>)
    thus ?thesis using \<open>r + s = 0\<close> by simp
  qed
  thus ?case
    by (metis add.left_neutral) 
next
  case (Suc n)
  have \<open>r \<in> partial_span (Suc n) S \<Longrightarrow> s \<in> partial_span (Suc n) S \<Longrightarrow> \<exists> p. r + s \<in> partial_span (Suc n + p) S\<close>
    for r s
  proof-
    assume \<open>r \<in> partial_span (Suc n) S\<close> and \<open>s \<in> partial_span (Suc n) S\<close>
    from \<open>r \<in> partial_span (Suc n) S\<close>
    have \<open>r \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span n S \<and> y \<in> S}\<close>
      by auto
    then obtain a u uu where \<open>r = u + a *\<^sub>C uu\<close> and \<open>u \<in>  partial_span n S\<close> and \<open>uu \<in> S\<close>
      by blast
    from \<open>s \<in> partial_span (Suc n) S\<close>
    have \<open>s \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span n S \<and> y \<in> S}\<close>
      by auto
    then obtain b v vv where \<open>s = v + b *\<^sub>C vv\<close> and \<open>v \<in>  partial_span n S\<close> and \<open>vv \<in> S\<close>
      by blast
    have \<open>r + s = (u + v) + a *\<^sub>C uu +  b *\<^sub>C vv\<close>
      by (simp add: \<open>r = u + a *\<^sub>C uu\<close> \<open>s = v + b *\<^sub>C vv\<close>)
    have \<open>\<exists> p. u + v \<in>  partial_span (n+p) S\<close>
      using Suc.IH  \<open>u \<in>  partial_span n S\<close> \<open>v \<in>  partial_span n S\<close>
      by auto
    then obtain p where  \<open> u + v \<in>  partial_span (n+p) S\<close>
      by blast
    hence \<open>(u + v) + a *\<^sub>C uu \<in> partial_span (Suc (n + p)) S\<close>
      using \<open>uu \<in> S\<close>
      by auto 
    hence \<open>((u + v) + a *\<^sub>C uu) + b *\<^sub>C vv \<in> partial_span (Suc (Suc (n + p))) S\<close>
      using \<open>vv \<in> S\<close> by force
    thus ?thesis
      by (metis \<open>r + s = u + v + a *\<^sub>C uu + b *\<^sub>C vv\<close> add_Suc add_Suc_right) 
  qed
  thus ?case by blast 
qed


lemma sum_partial_span_leq_ind:
  fixes S::\<open>'a::complex_vector set\<close> and n p :: nat
  assumes \<open>r \<in> partial_span n S\<close> and \<open>S \<noteq> {}\<close>
  shows \<open>r \<in> partial_span (n + p) S\<close>
proof(induction p)
  case 0
  thus ?case
    by (simp add: assms) 
next
  case (Suc p)
  have \<open>\<exists> s. s \<in> S\<close>
    using \<open>S \<noteq> {}\<close>
    by blast
  then obtain s where \<open>s \<in> S\<close>
    by blast
  have  \<open>r \<in> partial_span (n + p) S\<close>
    by (simp add: Suc.IH)
  hence  \<open>r + 0 *\<^sub>C s \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span (n + p) S \<and> y \<in> S}\<close>
    using  \<open>s \<in> S\<close>
    by blast
  hence  \<open>r + 0 *\<^sub>C s \<in> partial_span (Suc (n + p)) S\<close>
    by simp
  moreover have \<open>r = r + 0 *\<^sub>C s\<close>
    by simp
  ultimately show ?case by simp
qed


lemma sum_partial_span_leq:
  fixes S::\<open>'a::complex_vector set\<close>
  assumes \<open>r \<in> partial_span n S\<close> and \<open>n \<le> m\<close> and \<open>S \<noteq> {}\<close>
  shows \<open>r \<in> partial_span m S\<close>
  using sum_partial_span_leq_ind assms le_Suc_ex by blast 


lemma sum_partial_span:
  fixes S::\<open>'a::complex_vector set\<close>
  assumes \<open>r \<in> partial_span n S\<close> and \<open>s \<in> partial_span m S\<close> and \<open>S \<noteq> {}\<close>
  shows \<open>\<exists> p. r + s \<in> partial_span p S\<close>
  using assms sum_partial_span_eq sum_partial_span_leq
  by (metis max.cobounded1 max.cobounded2)


lemma scaleC_partial_span:
  fixes S::\<open>'a::complex_vector set\<close>
  shows \<open>\<forall> t. t \<in> partial_span n S \<longrightarrow> c *\<^sub>C t \<in> partial_span n S\<close>
proof(induction n)
  case 0
  thus ?case
    by simp 
next
  case (Suc n)
  have \<open>t \<in> partial_span (Suc n) S \<Longrightarrow> c *\<^sub>C t \<in> partial_span (Suc n) S\<close>
    for t
  proof-
    assume \<open>t \<in> partial_span (Suc n) S\<close>
    hence \<open>t \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span n S \<and> y \<in> S}\<close>
      by simp
    hence \<open>\<exists> a x y. x \<in> partial_span n S \<and> y \<in> S \<and> t = x + a *\<^sub>C y\<close>
      by blast
    then obtain a x y where \<open>x \<in> partial_span n S\<close> and \<open>y \<in> S\<close> 
      and \<open>t = x + a *\<^sub>C y\<close> by blast
    from \<open>t = x + a *\<^sub>C y\<close>
    have \<open>c *\<^sub>C t = c *\<^sub>C (x + a *\<^sub>C y)\<close>
      by blast
    hence \<open>c *\<^sub>C t = c *\<^sub>C x +  c *\<^sub>C (a *\<^sub>C y)\<close>
      by (simp add: scaleC_add_right)
    hence \<open>c *\<^sub>C t = c *\<^sub>C x +  (c * a) *\<^sub>C y\<close>
      by simp
    moreover have \<open>c *\<^sub>C x \<in> partial_span n S\<close>
      by (simp add: Suc.IH \<open>x \<in> partial_span n S\<close>)
    ultimately have  \<open>c *\<^sub>C t \<in> partial_span(Suc n) S\<close>
      using \<open>y \<in> S\<close> by auto
    thus ?thesis by blast
  qed
  thus ?case by blast 
qed


lemma partial_linear_manifold:
  fixes S::\<open>'a::complex_vector set\<close>
  assumes \<open>S \<noteq> {}\<close>
  shows \<open>complex_vector.subspace ( \<Union>n. partial_span n S)\<close>
proof-
  have "x + y \<in> (\<Union>n. partial_span n S)"
    if "x \<in> (\<Union>n. partial_span n S)"
      and "y \<in> (\<Union>n. partial_span n S)"
    for x :: 'a
      and y :: 'a
  proof-
    have \<open>\<exists> n. x \<in> partial_span n S\<close>
      using that by auto
    then obtain n where \<open>x \<in> partial_span n S\<close>
      by blast                    
    have \<open>\<exists> n. y \<in> partial_span n S\<close>
      using that by auto
    then obtain m where \<open>y \<in> partial_span m S\<close>
      by blast                    
    have \<open>\<exists> p. x + y \<in> partial_span p S\<close>
      using \<open>x \<in> partial_span n S\<close> \<open>y \<in> partial_span m S\<close> assms sum_partial_span by blast
    thus ?thesis
      by blast 
  qed
  moreover have "c *\<^sub>C x \<in> (\<Union>n. partial_span n S)"
    if "x \<in> (\<Union>n. partial_span n S)"
    for x :: 'a
      and c :: complex
  proof-
    have \<open>\<exists> n. x \<in> partial_span n S\<close>
      using that by auto
    then obtain n where \<open>x \<in> partial_span n S\<close>
      by blast                    
    thus ?thesis using scaleC_partial_span
      by blast 
  qed
  moreover have "0 \<in> (\<Union>n. partial_span n S)"
  proof-
    have \<open>0 \<in> partial_span 0 S\<close>
      by simp
    moreover have \<open>partial_span 0 S \<subseteq> (\<Union>n. partial_span n S)\<close>
      by blast
    ultimately show ?thesis by blast
  qed
  ultimately show ?thesis
    by (metis complex_vector.subspaceI) 
qed

lemma partial_span_subspace:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes  \<open>S \<noteq> {}\<close>
  shows \<open>closed_subspace (closure ( \<Union>n. partial_span n S) )\<close>
proof-
  have \<open>complex_vector.subspace ( \<Union>n. partial_span n S)\<close>
    by (simp add:  \<open>S \<noteq> {}\<close> partial_linear_manifold)    
  thus ?thesis
    by (simp add: subspace_I) 
qed


proposition partial_span_lim:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes  \<open>S \<noteq> {}\<close>
  shows \<open>closure (complex_vector.span S) = closure (\<Union> n::nat. partial_span n S)\<close>
proof
  show "closure (complex_vector.span S) \<subseteq> closure (\<Union>n. partial_span n S)"
  proof-
    have \<open>S \<subseteq> (\<Union>n. partial_span n S)\<close>
    proof-
      have \<open>partial_span 1 S \<subseteq> (\<Union>n. partial_span n S)\<close>
        by blast
      moreover have \<open>S \<subseteq> partial_span 1 S\<close>
        using partial_span_1 by blast
      ultimately show ?thesis by blast
    qed
    hence \<open>S \<subseteq> closure (\<Union>n. partial_span n S)\<close>
      by (meson closure_subset order.trans)
    moreover have \<open>closed_subspace (closure (\<Union>n. partial_span n S))\<close>
      using  \<open>S \<noteq> {}\<close>
      by (simp add: partial_span_subspace)
    ultimately show ?thesis
      using closure_closure closure_mono
      by (metis subspace_span_A)       
  qed
  show "closure (\<Union>n. partial_span n S) \<subseteq> closure (complex_vector.span S)"
  proof-
    have \<open>(\<Union>n. partial_span n S) \<subseteq> (complex_vector.span S)\<close>
      by (simp add: UN_least partial_span_lim_n) 
    thus ?thesis
      by (simp add: closure_mono) 
  qed
qed


lemma equal_span:
  fixes f::\<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close> and S::\<open>'a set\<close>
  shows \<open>\<forall> x::'a.
x \<in> partial_span n S \<longrightarrow>
 bounded_clinear f \<longrightarrow>
(\<forall> t \<in> S. f t = 0) \<longrightarrow> 
f x = 0\<close>
proof(induction n)
  case 0
  have \<open>x \<in> partial_span 0 S \<Longrightarrow> bounded_clinear f \<Longrightarrow> \<forall> t \<in> S. f t = 0 \<Longrightarrow> f x = 0\<close>
    for x::'a
  proof-
    assume \<open>x \<in> partial_span 0 S\<close> and \<open>bounded_clinear f\<close> and \<open>\<forall> t \<in> S. f t = 0\<close>
    from \<open>x \<in> partial_span 0 S\<close>
    have \<open>x = 0\<close>
      by simp
    thus ?thesis using \<open>bounded_clinear f\<close>
      by (simp add: bounded_clinear.clinear clinear_zero) 
  qed
  thus ?case by blast
next
  case (Suc n) 
  have \<open>x \<in> partial_span (Suc n) S \<Longrightarrow> bounded_clinear f \<Longrightarrow> \<forall> t \<in> S. f t = 0 \<Longrightarrow> f x = 0\<close>
    for x
  proof-
    assume \<open>x \<in> partial_span (Suc n) S\<close> and \<open>bounded_clinear f\<close> and \<open>\<forall> t \<in> S. f t = 0\<close>
    from \<open>x \<in> partial_span (Suc n) S\<close>
    have \<open>x \<in> {t + a *\<^sub>C y | a t y. t \<in> partial_span n S \<and> y \<in> S}\<close>
      by simp
    hence \<open>\<exists> a t y. t \<in> partial_span n S \<and> y \<in> S \<and> x = t + a *\<^sub>C y\<close>
      by blast
    then obtain a t y where \<open>t \<in> partial_span n S\<close> and \<open>y \<in> S\<close> and \<open>x = t + a *\<^sub>C y\<close>
      by blast
    have \<open>f t = 0\<close>
      using  \<open>t \<in> partial_span n S\<close> \<open>bounded_clinear f\<close> \<open>\<forall> t \<in> S. f t = 0\<close> Suc.IH by blast
    moreover have \<open>f y = 0\<close>
      using \<open>y \<in> S\<close>  \<open>\<forall> t \<in> S. f t = 0\<close>  by blast
    moreover have  \<open>f x = f t + f (a *\<^sub>C y)\<close>
      using \<open>bounded_clinear f\<close>  \<open>x = t + a *\<^sub>C y\<close>
      unfolding bounded_clinear_def
      using complex_vector.linear_add by blast 
    hence  \<open>f x = f t + a *\<^sub>C f y\<close>
      using \<open>bounded_clinear f\<close>  
      unfolding bounded_clinear_def
      by (simp add: complex_vector.linear_scale) 
    ultimately show ?thesis by simp
  qed
  thus ?case by blast
qed



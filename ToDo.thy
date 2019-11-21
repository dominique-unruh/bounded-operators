section \<open>TODO: section title\<close>

theory ToDo
  imports Bounded_Operators Complex_L2 
begin

text \<open>
How to use this file:

Dominique adds lemmas and definitions here that are needed by QRHL.

José can do one of the following things:
* Move them to the right theory file (and prove them)
* If they already exist (or very similar ones from which they follow trivially), add a comment here and do not edit them
* If they should be changed (the name or the formulation of the statement), add a comment here and discuss with Dominique

This way, QRHL will not be broken by the work on these lemmas/definitions
\<close>


(* TODO: move to where vector_to_bounded is defined *)
lemma vector_to_bounded_times_vec[simp]:
  includes bounded_notation
  shows "vector_to_bounded \<phi> *\<^sub>v \<gamma> = one_dim_to_complex \<gamma> *\<^sub>C \<phi>"
  apply transfer by (rule refl)

(* TODO: move to where vector_to_bounded is defined *)
lemma vector_to_bounded_adj_times_vec[simp]:
  includes bounded_notation
  shows "vector_to_bounded \<psi>* *\<^sub>v \<phi> = of_complex (cinner \<psi> \<phi>)"
proof -
  have "one_dim_to_complex (vector_to_bounded \<psi>* *\<^sub>v \<phi> :: 'a) = cinner 1 (vector_to_bounded \<psi>* *\<^sub>v \<phi> :: 'a)"
    by (simp add: one_dim_to_complex_def)
  also have "\<dots> = cinner (vector_to_bounded \<psi> *\<^sub>v (1::'a)) \<phi>"
    by (metis adjoint_I adjoint_twice)
  also have "\<dots> = \<langle>\<psi>, \<phi>\<rangle>"
    by simp
  finally have "one_dim_to_complex (vector_to_bounded \<psi>* *\<^sub>v \<phi> :: 'a) = \<langle>\<psi>, \<phi>\<rangle>" by -
  thus ?thesis
    by (metis one_dim_to_complex_inverse)
qed

lemma bounded_ext: 
  includes bounded_notation
  assumes "\<And>x::'a::chilbert_space. A *\<^sub>v x = B *\<^sub>v x"
  shows "A = B" 
  using assms apply transfer by auto

lemma one_dim_to_complex_scaleC[simp]: "one_dim_to_complex (c *\<^sub>C \<psi>) = c *\<^sub>C one_dim_to_complex \<psi>"
  (* apply transfer by simp *) 
  by (cheat one_dim_to_complex_scaleC)

lemma one_dim_to_complex_times[simp]: "one_dim_to_complex (\<psi> * \<phi>) = one_dim_to_complex \<psi> * one_dim_to_complex \<phi>"
  (* apply transfer by simp *) 
  by (cheat one_dim_to_complex_times)


lemma cinner_ext_ell2_0: 
  assumes "\<And>\<gamma>. cinner \<gamma> \<psi> = 0"
  shows "\<psi> = 0"
  using assms cinner_eq_zero_iff by blast

text \<open>This is a useful rule for establishing the equality of vectors\<close>
lemma cinner_ext_ell2: 
  assumes \<open>\<And>\<gamma>. cinner \<gamma> \<psi> = cinner \<gamma> \<phi>\<close>
  shows \<open>\<psi> = \<phi>\<close>
proof-
  have \<open>cinner \<gamma> (\<psi> - \<phi>) = 0\<close>
    for \<gamma>
    using \<open>\<And>\<gamma>. cinner \<gamma> \<psi> = cinner \<gamma> \<phi>\<close>
    by (simp add: cinner_diff_right)    
  hence \<open>\<psi> - \<phi> = 0\<close>
    using cinner_ext_ell2_0[where \<psi> = "\<psi> - \<phi>"] by blast
  thus ?thesis by simp
qed

lemma [simp]: "ket i \<noteq> 0"
  using ell2_ket[of i] by force

lemma equal_ket:
  includes bounded_notation
  assumes "\<And>x. A *\<^sub>v ket x = B *\<^sub>v ket x"
  shows "A = B"
  by (simp add: assms equal_basis)

lemma linear_space_leI:
  assumes "\<And>x. x \<in> space_as_set A \<Longrightarrow> x \<in> space_as_set B"
  shows "A \<le> B"
  using assms apply transfer by auto


lemma linear_space_member_inf[simp]:
  "x \<in> space_as_set (A \<sqinter> B) \<longleftrightarrow> x \<in> space_as_set A \<and> x \<in> space_as_set B"
  apply transfer by simp

(* TODO: move to where eigenspace is defined *)
lemma eigenspace_memberE:
  includes bounded_notation
  assumes "x \<in> space_as_set (eigenspace e A)"
  shows "A *\<^sub>v x = e *\<^sub>C x"
  using assms unfolding eigenspace_def apply transfer by auto

(* TODO: move to where kernel is defined *)
lemma kernel_memberE:
  includes bounded_notation
  assumes "x \<in> space_as_set (kernel A)"
  shows "A *\<^sub>v x = 0"
  using assms apply transfer by auto

(* TODO: move to where eigenspace is defined *)
lemma eigenspace_memberI:
  includes bounded_notation
  assumes "A *\<^sub>v x = e *\<^sub>C x"
  shows "x \<in> space_as_set (eigenspace e A)"
  using assms unfolding eigenspace_def apply transfer by auto

(* TODO: move to where kernel is defined *)
lemma kernel_memberI:
  includes bounded_notation
  assumes "A *\<^sub>v x = 0"
  shows "x \<in> space_as_set (kernel A)"
  using assms apply transfer by auto

lemma applyOpSpace_Span: 
  includes bounded_notation
  shows "A *\<^sub>s Span G = Span ((*\<^sub>v) A ` G)"
  apply transfer
proof
  show "closure (A ` closure (complex_vector.span (G::'b set))) \<subseteq> closure (complex_vector.span (A ` G::'a set))"
    if "bounded_clinear (A::'b \<Rightarrow> 'a)"
    for A :: "'b \<Rightarrow> 'a"
      and G :: "'b set"
  proof-
    have isContA: \<open>isCont A r\<close>
      for r
      using that
      by (simp add: bounded_linear_continuous)
    have \<open>A ` closure (complex_vector.span (G::'b set)) \<subseteq> closure (complex_vector.span (A ` G::'a set))\<close>
    proof
      show "x \<in> closure (complex_vector.span (A ` G))"
        if "x \<in> A ` closure (complex_vector.span G)"
        for x :: 'a
      proof-
        have \<open>\<exists> y. x = A y \<and> y \<in> closure (complex_vector.span G)\<close>
          using that by auto
        then obtain y where \<open>x = A y\<close> and \<open>y \<in> closure (complex_vector.span G)\<close>
          by blast
        from  \<open>y \<in> closure (complex_vector.span G)\<close>
        have \<open>\<exists> t. t \<longlonglongrightarrow> y \<and> (\<forall> n. t n \<in> complex_vector.span G)\<close>
          using closure_sequential by blast
        then obtain t where \<open>t \<longlonglongrightarrow> y\<close> and \<open>\<forall> n. t n \<in> complex_vector.span G\<close>
          by blast
        from \<open>\<forall> n. t n \<in> complex_vector.span G\<close>
        have \<open>\<forall> n. A (t n) \<in> complex_vector.span (A ` G)\<close>
          using \<open>bounded_clinear A\<close>
            complex_vector.linear_span_image 
          unfolding bounded_clinear_def
          by blast          
        moreover have \<open>(\<lambda> n. A (t n)) \<longlonglongrightarrow> A y\<close>
          using isContA  \<open>t \<longlonglongrightarrow> y\<close>
          by (simp add: isCont_tendsto_compose) 
        ultimately show ?thesis 
          using \<open>x = A y\<close>
          by (meson closure_sequential)
      qed
    qed
    thus ?thesis
      by (metis closure_closure closure_mono)       
  qed
  show "closure (complex_vector.span (A ` (G::'b set)::'a set)) \<subseteq> closure (A ` closure (complex_vector.span G))"
    if "bounded_clinear (A::'b \<Rightarrow> 'a)"
    for A :: "'b \<Rightarrow> 'a"
      and G :: "'b set"
    using that
    by (simp add: bounded_clinear.is_clinear closure_mono closure_subset complex_vector.linear_span_image image_mono) 
qed

lemma span_ortho_span:
  assumes "\<And>s t. s\<in>S \<Longrightarrow> t\<in>T \<Longrightarrow> is_orthogonal s t"
  shows "Span S \<le> - (Span T)"
  using assms apply transfer
proof
  show "x \<in> orthogonal_complement (closure (complex_vector.span T))"
    if "\<And>s t. \<lbrakk>s \<in> S; t \<in> T\<rbrakk> \<Longrightarrow> is_orthogonal s t"
      and "x \<in> closure (complex_vector.span S)"
    for S :: "'a set"
      and T :: "'a set"
      and x :: 'a
  proof-
    have discrete: \<open>x \<in> complex_vector.span S \<Longrightarrow> y \<in> complex_vector.span T \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
      for x y
    proof-
      assume \<open>x \<in> complex_vector.span S\<close> and \<open>y \<in> complex_vector.span T\<close>
      have \<open>\<exists> T' r\<^sub>T. finite T' \<and>  T' \<subseteq> T \<and> y = (\<Sum>a\<in>T'. r\<^sub>T a *\<^sub>C a)\<close>
        using complex_vector.span_explicit  \<open>y \<in> complex_vector.span T\<close>
        by (smt mem_Collect_eq)
      then obtain T' r\<^sub>T where \<open>finite T'\<close> and \<open>T' \<subseteq> T\<close> and \<open>y = (\<Sum>a\<in>T'. r\<^sub>T a *\<^sub>C a)\<close>
        by blast
      have \<open>\<exists> S' r\<^sub>S. finite S' \<and>  S' \<subseteq> S \<and> x = (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a)\<close>
        using complex_vector.span_explicit  \<open>x \<in> complex_vector.span S\<close>
        by (smt mem_Collect_eq)
      then obtain S' r\<^sub>S where \<open>finite S'\<close> and \<open>S' \<subseteq> S\<close> and \<open>x = (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a)\<close>
        by blast
      have \<open>\<langle> x, y \<rangle> = \<langle> (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a), (\<Sum>b\<in>T'. r\<^sub>T b *\<^sub>C b) \<rangle>\<close>
        by (simp add: \<open>x = (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a)\<close> \<open>y = (\<Sum>a\<in>T'. r\<^sub>T a *\<^sub>C a)\<close>)
      also have \<open>\<dots> = (\<Sum>a\<in>S'. \<langle> r\<^sub>S a *\<^sub>C a, (\<Sum>b\<in>T'. r\<^sub>T b *\<^sub>C b) \<rangle>)\<close>
        using cinner_sum_left by blast
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. \<langle> r\<^sub>S a *\<^sub>C a,  r\<^sub>T b *\<^sub>C b \<rangle>))\<close>
        by (simp add: cinner_sum_right)
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. (cnj (r\<^sub>S a)) * \<langle> a,  r\<^sub>T b *\<^sub>C b \<rangle>))\<close>
      proof -
        have "(\<Sum>a\<in>S'. \<Sum>aa\<in>T'. \<langle>r\<^sub>S a *\<^sub>C a, r\<^sub>T aa *\<^sub>C aa\<rangle>) = (\<Sum>a\<in>S'. \<Sum>aa\<in>T'. cnj (r\<^sub>S a) * \<langle>a, r\<^sub>T aa *\<^sub>C aa\<rangle>) \<or> (\<forall>a. (\<Sum>aa\<in>T'. \<langle>r\<^sub>S a *\<^sub>C a, r\<^sub>T aa *\<^sub>C aa\<rangle>) = (\<Sum>aa\<in>T'. cnj (r\<^sub>S a) * \<langle>a, r\<^sub>T aa *\<^sub>C aa\<rangle>))"
          by (meson cinner_scaleC_left)
        thus ?thesis
          by presburger
      qed
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. (cnj (r\<^sub>S a)) * ((r\<^sub>T b) * \<langle> a, b \<rangle>)))\<close>
      proof-
        have \<open>\<langle> a, r\<^sub>T b *\<^sub>C b \<rangle> =  r\<^sub>T b * \<langle> a, b \<rangle>\<close>
          for a b
          by simp
        thus ?thesis by simp
      qed
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. (cnj (r\<^sub>S a)) * ((r\<^sub>T b) * 0)))\<close>
      proof-
        have \<open>a \<in> S' \<Longrightarrow> b \<in> T' \<Longrightarrow> \<langle> a, b \<rangle> = 0\<close>
          for a b
        proof-
          assume \<open>a \<in> S'\<close> and \<open>b \<in> T'\<close>
          have \<open>a \<in> S\<close>
            using \<open>S' \<subseteq> S\<close> \<open>a \<in> S'\<close> by blast            
          moreover have \<open>b \<in> T\<close>
            using \<open>T' \<subseteq> T\<close> \<open>b \<in> T'\<close> by blast
          ultimately show ?thesis
            using is_orthogonal_def that(1) by auto 
        qed
        thus ?thesis by simp
      qed
      finally show \<open>\<langle> x, y \<rangle> = 0\<close> by simp
    qed
    have \<open>y \<in> complex_vector.span T \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
      for y
    proof-
      assume \<open>y \<in> complex_vector.span T\<close>
      have \<open>\<exists> t. t \<longlonglongrightarrow> x \<and> (\<forall> n. t n \<in> complex_vector.span S)\<close>
        using closure_sequential
        by (metis that(2))  
      then obtain t where \<open>t \<longlonglongrightarrow> x\<close> and \<open>\<forall> n. t n \<in> complex_vector.span S\<close>
        by blast
      from  \<open>\<forall> n. t n \<in> complex_vector.span S\<close>
      have \<open>\<langle> t n, y \<rangle> = 0\<close>
        for n
        using discrete \<open>y \<in> complex_vector.span T\<close>
        by blast
      moreover have \<open>(\<lambda> n. \<langle> t n, y \<rangle>) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
        using  \<open>t \<longlonglongrightarrow> x\<close> cinner_continuous_left
        by (simp add: cinner_continuous_left)
      ultimately have \<open>(\<lambda> n. 0) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
        by simp
      thus ?thesis
        by (simp add: LIMSEQ_const_iff) 
    qed
    hence \<open>y \<in> closure (complex_vector.span T) \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
      for y
    proof-
      assume \<open>y \<in> closure (complex_vector.span T)\<close>
      hence \<open>\<exists> t. t \<longlonglongrightarrow> y \<and> (\<forall> n. t n \<in> complex_vector.span T)\<close>
        using closure_sequential by blast
      then obtain t where \<open>t \<longlonglongrightarrow> y\<close> and \<open>\<forall> n. t n \<in> complex_vector.span T\<close>
        by blast
      from  \<open>\<forall> n. t n \<in> complex_vector.span T\<close>
      have \<open>\<langle> x, t n \<rangle> = 0\<close>
        for n
        by (simp add: \<open>\<And>y. y \<in> complex_vector.span T \<Longrightarrow> \<langle>x, y\<rangle> = 0\<close>)
      moreover have \<open>(\<lambda> n. \<langle> x, t n \<rangle>) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
        using  \<open>t \<longlonglongrightarrow> y\<close>
        by (simp add: cinner_continuous_right)        
      ultimately have \<open>(\<lambda> n. 0) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
        by simp
      thus ?thesis
        by (simp add: LIMSEQ_const_iff) 
    qed
    thus ?thesis
      using orthogonal_complement_I2 by blast 
  qed
qed

lemma ket_is_orthogonal[simp]:
  "is_orthogonal (ket x) (ket y) \<longleftrightarrow> x \<noteq> y"
  unfolding is_orthogonal_def 
  by (auto simp: ket_Kronecker_delta_neq)

unbundle bounded_notation

(* TODO: move to Bounded_Operators *)
definition "positive_op A = (\<exists>B::('a::chilbert_space,'a) bounded. A = B* *\<^sub>o B)"

(* TODO: move to Bounded_Operators *)
lemma timesOp0[simp]: "0 *\<^sub>o A = 0"
  apply transfer by simp
(* TODO: move to Bounded_Operators *)
lemma timesOp0'[simp]: "A *\<^sub>o 0 = 0"
  apply transfer apply auto
  by (metis bounded_clinear_def mult_zero_left norm_le_zero_iff norm_zero)

(* TODO: move to Bounded_Operators *)
lemma positive_idOp[simp]: "positive_op idOp"
  unfolding positive_op_def apply (rule exI[of _ idOp]) by simp
(* TODO: move to Bounded_Operators *)
lemma positive_0[simp]: "positive_op 0"
  unfolding positive_op_def apply (rule exI[of _ 0]) by auto

(* TODO: move to Bounded_Operators *)
abbreviation "loewner_leq A B == (positive_op (B-A))"

lemma Span_range_ket[simp]: "Span (range ket) = (top::('a ell2_linear_space))"
proof-
  have \<open>closure (complex_vector.span (range ket)) = (UNIV::'a ell2 set)\<close>
    using Complex_L2.ket_ell2_span by blast
  thus ?thesis
    by (simp add: Span.abs_eq top_linear_space.abs_eq)
qed

(* TODO: move to Bounded_Operators *)
lemma norm_mult_ineq_bounded:
  fixes A B :: "(_,_) bounded"
  shows "norm (A *\<^sub>o B) \<le> norm A * norm B"
  apply transfer
  by (simp add: bounded_clinear.bounded_linear onorm_compose)


(* 
Proof sketch for closed_finite_dim (with normed_vector_space):

Let B be a basis for span A. (Exists by basis_exists, with dimension "dim span A", which is \<le> card A
by dim_le_card. Hence B is finite.)

Fix a Cauchy sequence \<psi>i in span A = span B. 

Each \<psi>i can be expressed in terms of vectors in B. 

For each b\<in>B, let \<psi>ib be the b-coefficient of \<psi>i (can be written in Isabelle as "representation B \<psi>i b")

Then \<psi>ib is Cauchy for all b.

Thus exists \<psi>b s.t. \<psi>ib \<longlonglongrightarrow> \<psi>b for all b.

Thus \<psi>ib * b \<longlonglongrightarrow> \<psi>b * b for all b.

Thus \<psi>ib = (\<Sum>b\<in>B. \<psi>ib * b) \<longlonglongrightarrow> (\<Sum>b\<in>B. \<psi>b * b) =: \<psi>. (Note \<psi> \<in> span B.)

Thus the Cauchy sequence \<psi>i converges in span B = span A. Hence span A is complete.

In particular, span A is closed. (complete \<Longrightarrow> closed is probably already proven somewhere. If not,
one simply uses the fact that if \<psi>i \<longlonglongrightarrow> \<psi>, then \<psi>i is Cauchy, thus it converges to something in span A,
thus \<psi>\<in>span A. This is implies that span A is closed.)

*)

hide_fact closed_finite_dim'

lemma span_finite_dim:
  fixes T::\<open>'a::complex_inner set\<close>
  assumes \<open>finite T\<close>
  shows \<open>closure (complex_vector.span T)  = complex_vector.span T\<close>
  using closed_finite_dim
  by (simp add: closed_finite_dim assms)

lemma Ortho_expansion_finite:
  fixes T::\<open>'a::complex_inner set\<close>
  assumes \<open>is_onb T\<close> and \<open>finite T\<close>
  shows \<open>x = (\<Sum>t\<in>T. \<langle> t, x \<rangle> *\<^sub>C t)\<close>
proof-
  have \<open>closure (complex_vector.span T) = UNIV\<close>
    using \<open>is_onb T\<close>
    unfolding is_onb_def is_basis_def
    by blast
  moreover have \<open>closure (complex_vector.span T)  = complex_vector.span T\<close>
    using \<open>finite T\<close> span_finite_dim by blast
  ultimately have \<open>complex_vector.span T = (UNIV::'a set)\<close>
    by blast
  have \<open>{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> T} =
    {\<Sum>a\<in>T. r a *\<^sub>C a |r. True}\<close>
    using span_explicit_finite[where A = "T"] \<open>finite T\<close>
    by blast
  hence \<open>\<exists> r. x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
  proof -
    have f1: "\<forall>A. {a. \<exists>Aa f. (a::'a) = (\<Sum>a\<in>Aa. f a *\<^sub>C a) \<and> finite Aa \<and> Aa \<subseteq> A} = Complex_Vector_Spaces.span A"
      by (simp add: Complex_Vector_Spaces.span_raw_def complex_vector.span_explicit)
    have f2: "\<forall>a. (\<exists>f. a = (\<Sum>a\<in>T. f a *\<^sub>C a)) \<or> (\<forall>A. (\<forall>f. a \<noteq> (\<Sum>a\<in>A. f a *\<^sub>C a)) \<or> infinite A \<or> \<not> A \<subseteq> T)"
      using \<open>{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> T} = {\<Sum>a\<in>T. r a *\<^sub>C a |r. True}\<close> by auto
    have f3: "\<forall>A a. (\<exists>Aa f. (a::'a) = (\<Sum>a\<in>Aa. f a *\<^sub>C a) \<and> finite Aa \<and> Aa \<subseteq> A) \<or> a \<notin> Complex_Vector_Spaces.span A"
      using f1 by blast
    have "Complex_Vector_Spaces.span T = UNIV"
      by (metis (full_types, lifting) Complex_Vector_Spaces.span_raw_def \<open>complex_vector.span T = UNIV\<close>)
    then show ?thesis
      using f3 f2 by blast
  qed 
  then obtain r where \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    by blast
  have \<open>a \<in> T \<Longrightarrow> r a = \<langle>a, x\<rangle>\<close>
    for a
  proof-
    assume \<open>a \<in> T\<close>
    have \<open>\<langle>a, x\<rangle> = \<langle>a, (\<Sum> t\<in>T. r t *\<^sub>C t)\<rangle>\<close>
      using \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum> t\<in>T. \<langle>a, r t *\<^sub>C t\<rangle>)\<close>
      using cinner_sum_right by blast
    also have \<open>\<dots> = (\<Sum> t\<in>T. r t * \<langle>a, t\<rangle>)\<close>
    proof-
      have \<open>\<langle>a, r t *\<^sub>C t\<rangle> = r t * \<langle>a, t\<rangle>\<close>
        for t
        by simp
      thus ?thesis by simp
    qed
    also have \<open>\<dots> = r a * \<langle>a, a\<rangle> + (\<Sum> t\<in>T-{a}. r t * \<langle>a, t\<rangle>)\<close>
      using \<open>a \<in> T\<close>
      by (meson assms(2) sum.remove)
    also have \<open>\<dots> = r a * \<langle>a, a\<rangle>\<close>
    proof-
      have \<open>(\<Sum> t\<in>T-{a}. r t * \<langle>a, t\<rangle>) = 0\<close>
      proof-
        have \<open>t\<in>T-{a} \<Longrightarrow> r t * \<langle>a, t\<rangle> = 0\<close>
          for t
        proof-
          assume \<open>t \<in> T-{a}\<close>
          hence \<open>t \<in> T\<close>
            by blast
          have \<open>a \<noteq> t\<close>
            using  \<open>t \<in> T-{a}\<close>
            by auto
          hence \<open>\<langle>a, t\<rangle> = 0\<close>
            using \<open>a \<in> T\<close> \<open>t \<in> T\<close> \<open>is_onb T\<close>
            unfolding is_onb_def is_ortho_set_def
            by blast
          thus ?thesis by simp
        qed
        show ?thesis
          by (simp add: \<open>\<And>t. t \<in> T - {a} \<Longrightarrow> r t * \<langle>a, t\<rangle> = 0\<close>) 
      qed
      thus ?thesis by simp
    qed
    also have \<open>\<dots> = r a\<close>
    proof-
      have \<open>a \<in> sphere 0 1\<close>
        using \<open>a\<in>T\<close> \<open>is_onb T\<close>
        unfolding is_onb_def
        by blast
      hence \<open>norm a = 1\<close>
        unfolding sphere_def by auto
      moreover have \<open>norm a = sqrt (norm \<langle>a, a\<rangle>)\<close>
        using norm_eq_sqrt_cinner by auto        
      ultimately have \<open>sqrt (norm \<langle>a, a\<rangle>) = 1\<close>
        by simp
      hence \<open>norm \<langle>a, a\<rangle> = 1\<close>
        using real_sqrt_eq_1_iff by blast
      moreover have \<open>\<langle>a, a\<rangle> \<in> \<real>\<close>
        by (simp add: cinner_real)        
      moreover have \<open>\<langle>a, a\<rangle> \<ge> 0\<close>
        by simp        
      ultimately have \<open>\<langle>a, a\<rangle> = 1\<close>
        by (metis \<open>0 \<le> \<langle>a, a\<rangle>\<close> \<open>cmod \<langle>a, a\<rangle> = 1\<close> complex_of_real_cmod of_real_1)
      thus ?thesis by simp
    qed
    finally show ?thesis by auto
  qed
  thus ?thesis 
    using \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    by fastforce 
qed

(* TODO: move to where basis_enum is defined *)
instance basis_enum \<subseteq> chilbert_space
proof
  show "convergent X"
    if "Cauchy X"
    for X :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>finite (set canonical_basis)\<close>
      by simp
    have \<open>is_onb (set canonical_basis)\<close>
      by (simp add: is_onb_set)
    have \<open>Cauchy (\<lambda> n. \<langle> t, X n \<rangle>)\<close>
      for t
    proof-
      define f where \<open>f x = \<langle> t, x \<rangle>\<close> for x
      have \<open>bounded_clinear f\<close>
        unfolding f_def
        by (simp add: bounded_clinear_cinner_right)
      hence \<open>Cauchy (\<lambda> n. f (X n))\<close>
        using that
        by (simp add: bounded_clinear_Cauchy) 
      thus ?thesis
        unfolding f_def by blast
    qed
    hence \<open>convergent (\<lambda> n. \<langle> t, X n \<rangle>)\<close>
      for t
      by (simp add: Cauchy_convergent_iff)      
    hence \<open>\<forall> t\<in>set canonical_basis. \<exists> L. (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L\<close>
      by (simp add: convergentD)
    hence \<open>\<exists> L. \<forall> t\<in>set canonical_basis. (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
      by metis
    then obtain L where \<open>\<And> t. t\<in>set canonical_basis \<Longrightarrow> (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
      by blast
    define l where \<open>l = (\<Sum>t\<in>set canonical_basis. L t *\<^sub>C t)\<close>
    have \<open>X n = (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t)\<close>
      for n
      using Ortho_expansion_finite[where T = "set canonical_basis" and x = "X n"]
        \<open>is_onb (set canonical_basis)\<close>  \<open>finite (set canonical_basis)\<close> 
      by auto
 (*     using Ortho_expansion_finite[where T = "set canonical_basis" and x = "X n"]
        \<open>is_onb (set canonical_basis)\<close>  \<open>finite (set canonical_basis)\<close> *)
    moreover have  \<open>(\<lambda> n. (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t)) \<longlonglongrightarrow> l\<close>
    proof-
      have \<open>t\<in>set canonical_basis \<Longrightarrow> (\<lambda> n. \<langle> t, X n \<rangle> *\<^sub>C t) \<longlonglongrightarrow> L t *\<^sub>C t\<close> 
        for t
      proof-
        assume \<open>t\<in>set canonical_basis\<close>
        hence \<open>(\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
          using  \<open>\<And> t. t\<in>set canonical_basis \<Longrightarrow> (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
          by blast
        hence \<open>(\<lambda> n. \<langle> t, X n \<rangle> *\<^sub>C t) \<longlonglongrightarrow> L t *\<^sub>C t\<close>
        proof-
          define f where \<open>f x = x *\<^sub>C t\<close> for x
          have \<open>isCont f r\<close>
            for r
            unfolding f_def
            by (simp add: bounded_clinear_scaleC_left bounded_linear_continuous)
          hence \<open>(\<lambda> n. f \<langle> t, X n \<rangle>) \<longlonglongrightarrow> f (L t)\<close>
            using \<open>(\<lambda>n. \<langle>t, X n\<rangle>) \<longlonglongrightarrow> L t\<close> isCont_tendsto_compose by blast
          thus ?thesis unfolding f_def
            by simp
        qed
        thus ?thesis by blast
      qed
      hence \<open>(\<lambda> n. (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t)) \<longlonglongrightarrow>  (\<Sum>t\<in>set canonical_basis. L t *\<^sub>C t)\<close>
        using \<open>finite (set canonical_basis)\<close>
          tendsto_finite_sum[where T = "set canonical_basis" and X = "\<lambda> t. \<lambda> n. \<langle>t, X n\<rangle> *\<^sub>C t"
            and L = "\<lambda> t. L t *\<^sub>C t"]
        by auto
      thus ?thesis
        using l_def by blast 
    qed
    ultimately have \<open>X \<longlonglongrightarrow> l\<close>
      by simp
    thus ?thesis 
      unfolding convergent_def by blast
  qed
qed

(* TODO: move to where vector_to_bounded is defined *)
lemma vector_to_bounded_adj_times_vector_to_bounded[simp]:
  includes bounded_notation
  shows "vector_to_bounded \<psi>* *\<^sub>o vector_to_bounded \<phi> = cinner \<psi> \<phi> *\<^sub>C idOp"
proof -
  have "one_dim_to_complex ((vector_to_bounded \<psi>* *\<^sub>o vector_to_bounded \<phi>) *\<^sub>v \<gamma>) = one_dim_to_complex ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>v \<gamma>)" 
    for \<gamma> :: "'c::one_dim"
    by (simp add: times_applyOp)
  hence "((vector_to_bounded \<psi>* *\<^sub>o vector_to_bounded \<phi>) *\<^sub>v \<gamma>) = ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>v \<gamma>)" 
    for \<gamma> :: "'c::one_dim"
    using one_dim_to_complex_inverse by metis
  thus ?thesis
    using  bounded_ext[where A = "vector_to_bounded \<psi>* *\<^sub>o vector_to_bounded \<phi>"
        and B = "\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp"]
    by auto
qed

unbundle no_bounded_notation

end


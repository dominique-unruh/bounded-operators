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


lemma cinner_1_C1: "cinner 1 \<psi> = C1_to_complex \<psi>"
  apply transfer by (simp add: singleton_UNIV)

lemma ell2_to_bounded_times_vec[simp]:
  includes bounded_notation
  shows "ell2_to_bounded \<phi> *\<^sub>v \<gamma> = C1_to_complex \<gamma> *\<^sub>C \<phi>"
  unfolding ell2_to_bounded.rep_eq by simp

text \<open>This is the defining property of the adjoint\<close>
  (* TODO: There is adjoint_I, but it has unnecessary allquantifiers *)
lemma cinner_adjoint:
  includes bounded_notation
  shows "cinner \<psi> (A *\<^sub>v \<phi>) = cinner (A* *\<^sub>v \<psi>) \<phi>"
  by (simp add: adjoint_I)

lemma cinner_adjoint':
  includes bounded_notation
  shows "cinner (A *\<^sub>v \<phi>) \<psi> = cinner \<phi> (A* *\<^sub>v \<psi>)"
  by (simp add: cinner_adjoint)

lemma ell2_to_bounded_adj_times_vec[simp]:
  includes bounded_notation
  shows "ell2_to_bounded \<psi>* *\<^sub>v \<phi> = complex_to_C1 (cinner \<psi> \<phi>)"
proof -
  note [[show_sorts]]
  have "C1_to_complex (ell2_to_bounded \<psi>* *\<^sub>v \<phi> :: 'a ell2) = cinner 1 (ell2_to_bounded \<psi>* *\<^sub>v \<phi> :: 'a ell2)"
    by (simp add: cinner_1_C1)
  also have "\<dots> = cinner (ell2_to_bounded \<psi> *\<^sub>v (1::'a ell2)) \<phi>"
    by (metis cinner_adjoint')
  also have "\<dots> = \<langle>\<psi>, \<phi>\<rangle>"
    by simp
  finally have "C1_to_complex (ell2_to_bounded \<psi>* *\<^sub>v \<phi> :: 'a ell2) = \<langle>\<psi>, \<phi>\<rangle>" by -
  thus ?thesis
    by (metis C1_to_complex_inverse)
qed

lemma bounded_ext: 
  includes bounded_notation
  assumes "\<And>x::'a::chilbert_space. A *\<^sub>v x = B *\<^sub>v x"
  shows "A = B" 
  using assms apply transfer by auto

lemma C1_to_complex_scaleC[simp]: "C1_to_complex (c *\<^sub>C \<psi>) = c *\<^sub>C C1_to_complex \<psi>"
  apply transfer by simp

lemma C1_to_complex_times[simp]: "C1_to_complex (\<psi> * \<phi>) = C1_to_complex \<psi> * C1_to_complex \<phi>"
  apply transfer by simp

lemma ell2_to_bounded_adj_times_ell2_to_bounded[simp]:
  includes bounded_notation
  shows "ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi> = cinner \<psi> \<phi> *\<^sub>C idOp"
proof -
  have "C1_to_complex ((ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi>) *\<^sub>v \<gamma>) = C1_to_complex ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>v \<gamma>)" 
    for \<gamma> :: "'c::the_single ell2"
    by (simp add: times_applyOp)
  hence "((ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi>) *\<^sub>v \<gamma>) = ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>v \<gamma>)" 
    for \<gamma> :: "'c::the_single ell2"
    using C1_to_complex_inverse by metis
  thus ?thesis
    using  bounded_ext[where A = "ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi>"
        and B = "\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp"]
    by auto
qed

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

(* TODO analogous lemma for kernel *)
lemma eigenspace_memberE:
  includes bounded_notation
  assumes "x \<in> space_as_set (eigenspace e A)"
  shows "A *\<^sub>v x = e *\<^sub>C x"
  using assms unfolding eigenspace_def apply transfer by auto

(* TODO analogous lemma for kernel *)
lemma eigenspace_memberI:
  includes bounded_notation
  assumes "A *\<^sub>v x = e *\<^sub>C x"
  shows "x \<in> space_as_set (eigenspace e A)"
  using assms unfolding eigenspace_def apply transfer by auto


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

lemma cinner_continuous_right:
  assumes \<open>t \<longlonglongrightarrow> y\<close>
  shows \<open>(\<lambda> n. \<langle> x, t n \<rangle>) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
proof-
  have \<open>(\<lambda> n. \<langle> x, t n - y \<rangle>) \<longlonglongrightarrow> 0\<close>
  proof-
    have \<open>\<exists> K. \<forall> a b::'a. norm \<langle>a, b\<rangle> \<le> norm a * norm b * K\<close>
      using bounded_sesquilinear.bounded bounded_sesquilinear_cinner by auto
    then obtain K where \<open>\<And> a b::'a. norm \<langle>a, b\<rangle> \<le> norm a * norm b * K\<close>
      by blast
    have \<open>(\<lambda> n. norm x * norm (t n - y)) \<longlonglongrightarrow> 0\<close>
    proof-
      have \<open>(\<lambda> n. t n - y) \<longlonglongrightarrow> 0\<close>
        using \<open>t \<longlonglongrightarrow> y\<close> LIM_zero by auto
      thus ?thesis
        by (simp add: tendsto_mult_right_zero tendsto_norm_zero) 
    qed
    moreover have \<open>norm \<langle> x, t n - y \<rangle> \<le> norm (norm x * norm (t n - y)) * K\<close>
      for n
      using \<open>\<And> a b::'a. norm \<langle>a, b\<rangle> \<le> norm a * norm b * K\<close>
      by auto
    ultimately show ?thesis using Limits.tendsto_0_le
      by (metis (no_types, lifting) eventually_sequentiallyI)
  qed
  moreover have \<open>\<langle> x, t n - y \<rangle> =  \<langle> x, t n \<rangle> - \<langle> x, y \<rangle>\<close>
    for n
    by (simp add: cinner_diff_right)    
  ultimately have \<open>(\<lambda> n. \<langle> x, t n \<rangle> - \<langle> x, y \<rangle>) \<longlonglongrightarrow> 0\<close>
    by simp
  thus ?thesis
    by (simp add: LIM_zero_iff) 
qed

lemma cinner_continuous_left:
  assumes \<open>t \<longlonglongrightarrow> x\<close>
  shows \<open>(\<lambda> n. \<langle> t n, y \<rangle>) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
proof-
  have \<open>(\<lambda> n. \<langle> y, t n \<rangle>) \<longlonglongrightarrow> \<langle> y, x \<rangle>\<close>
    by (simp add: assms cinner_continuous_right)
  hence \<open>(\<lambda> n. cnj \<langle> y, t n \<rangle>) \<longlonglongrightarrow> cnj \<langle> y, x \<rangle>\<close>
    using lim_cnj by fastforce
  moreover have \<open>cnj \<langle> y, t n \<rangle> = \<langle> t n, y \<rangle>\<close>
    for n
    by simp    
  moreover have \<open>cnj \<langle> y, x \<rangle> = \<langle> x, y \<rangle>\<close>
    by simp    
  ultimately show ?thesis 
    by simp
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

definition "positive_op A = (\<exists>B::('a::chilbert_space,'a) bounded. A = B* *\<^sub>o B)"

lemma timesOp0[simp]: "0 *\<^sub>o A = 0"
  apply transfer by simp
lemma timesOp0'[simp]: "A *\<^sub>o 0 = 0"
  apply transfer apply auto
  by (metis bounded_clinear_def mult_zero_left norm_le_zero_iff norm_zero)

lemma positive_idOp[simp]: "positive_op idOp"
  unfolding positive_op_def apply (rule exI[of _ idOp]) by simp
lemma positive_0[simp]: "positive_op 0"
  unfolding positive_op_def apply (rule exI[of _ 0]) by auto

abbreviation "loewner_leq A B == (positive_op (B-A))"

lemma Span_range_ket[simp]: "Span (range ket) = (top::('a ell2_linear_space))"
proof-
  have \<open>closure (complex_vector.span (range ket)) = (UNIV::'a ell2 set)\<close>
    using Complex_L2.ket_ell2_span by blast
  thus ?thesis
    by (simp add: Span.abs_eq top_linear_space.abs_eq)
qed

lemma norm_mult_ineq_bounded:
  fixes A B :: "(_,_) bounded"
  shows "norm (A *\<^sub>o B) \<le> norm A * norm B"
  apply transfer
  by (simp add: bounded_clinear.bounded_linear onorm_compose)

lemma equal_span':
  fixes f g :: "'a::cbanach \<Rightarrow> 'b::cbanach"
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  assumes "\<And>x. x\<in>G \<Longrightarrow> f x = g x"
  assumes "x\<in>closure (complex_vector.span G)"
  shows "f x = g x"
  using assms equal_span_applyOpSpace
  by metis 

lemma ortho_bot[simp]: "- bot = (top::'a::chilbert_space linear_space)"
  apply transfer by auto

lemma ortho_top[simp]: "- top = (bot::'a::chilbert_space linear_space)"
  apply transfer by auto

(* TODO: Claimed by https://en.wikipedia.org/wiki/Complemented_lattice *)
lemma demorgan_inf: "- ((A::_::orthocomplemented_lattice) \<sqinter> B) = - A \<squnion> - B"
  by (cheat demorgan_inf) 

(* TODO: Claimed by https://en.wikipedia.org/wiki/Complemented_lattice *)
lemma demorgan_sup: "- ((A::_::orthocomplemented_lattice) \<squnion> B) = - A \<sqinter> - B"
  by (cheat demorgan_sup) 

(* TODO: move *)
lemma span_explicit_finite:
  assumes \<open>finite T\<close> and \<open>x \<in> complex_vector.span T\<close>
  shows \<open>\<exists> r. x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
proof-
  have \<open>\<exists>r T'. T' \<subseteq> T \<and> x = (\<Sum>a\<in>T'. r a *\<^sub>C a)\<close>
  proof -
    have "{\<Sum>a\<in>A. f a *\<^sub>C a |A f. finite A \<and> A \<subseteq> T} = complex_vector.span T"
      using  complex_vector.span_explicit by blast
    hence "\<And>a. a \<in> complex_vector.span T \<Longrightarrow> \<exists>A f. a = (\<Sum>a\<in>A. f a *\<^sub>C a) \<and> finite A \<and> A \<subseteq> T"
      by blast
    thus ?thesis
      using assms(2) by blast
  qed
  show ?thesis  proof-
    obtain r' T' where \<open>T' \<subseteq> T\<close> and \<open>x = (\<Sum> a\<in>T'. r' a *\<^sub>C a)\<close>
      using \<open>\<exists>r T'. T' \<subseteq> T \<and> x = (\<Sum>a\<in>T'. r a *\<^sub>C a)\<close> by blast
    define r where \<open>r x = (if x \<in> T' then r' x else 0)\<close> for x
    have \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    proof-
      from \<open>T' \<subseteq> T\<close>
      have \<open>(\<Sum> a\<in>T. r a *\<^sub>C a) = (\<Sum> a\<in>T'. r a *\<^sub>C a) + (\<Sum> a\<in>T-T'. r a *\<^sub>C a)\<close>
        by (metis (no_types, lifting) add.commute assms(1) sum.subset_diff)
      moreover have \<open>(\<Sum> a\<in>T-T'. r a *\<^sub>C a) = 0\<close>
      proof-
        have \<open>a\<in>T-T' \<Longrightarrow> r a *\<^sub>C a = 0\<close>
          for a
        proof-
          assume \<open>a\<in>T-T'\<close>
          hence \<open>r a = 0\<close>
            unfolding r_def by simp
          thus ?thesis by simp
        qed
        show ?thesis
          by (simp add: \<open>\<And>a. a \<in> T - T' \<Longrightarrow> r a *\<^sub>C a = 0\<close>) 
      qed
      ultimately show ?thesis
        using \<open>r \<equiv> \<lambda>x. if x \<in> T' then r' x else 0\<close> \<open>x = (\<Sum>a\<in>T'. r' a *\<^sub>C a)\<close> by auto 
    qed
    thus ?thesis by blast
  qed
qed


lemma closed_line:
\<open>closed {c *\<^sub>C (k::'a::chilbert_space)| c. True}\<close>
  sorry


(* TODO move *)
lemma closed_finite_dim_induction:
  \<open>\<forall> T::'a::chilbert_space set. card T = n \<and> finite T \<longrightarrow> closed (complex_vector.span T)\<close>
proof(induction n)
  case 0
  thus ?case
    by force 
next
  case (Suc n)
  have \<open>card T = Suc n \<Longrightarrow> finite T \<Longrightarrow> closed (complex_vector.span T)\<close>
    for T::\<open>'a set\<close>
  proof-
    assume \<open>card T = Suc n\<close> and \<open>finite T\<close>
    from \<open>card T = Suc n\<close>
    have \<open>\<exists> k K. k \<notin> K \<and> T = insert k K\<close>
      by (meson card_Suc_eq)
    then obtain k K where \<open>k \<notin> K\<close> and \<open>T = insert k K\<close>
      by blast
    have \<open>card K = n\<close>
      using \<open>T = insert k K\<close> \<open>card T = Suc n\<close> \<open>finite T\<close> \<open>k \<notin> K\<close> by auto
    moreover have \<open>finite K\<close>
      using \<open>T = insert k K\<close> \<open>finite T\<close> by auto
    ultimately have \<open>closed (complex_vector.span K)\<close>
      by (simp add: Suc.IH)
    hence \<open>closed_subspace (complex_vector.span K)\<close>
      by (simp add: closed_subspace.intro)
    have \<open>K \<subseteq> T\<close>
      by (simp add: \<open>T = insert k K\<close> subset_insertI)
    hence \<open>complex_vector.span K \<subseteq> complex_vector.span T\<close>
      using complex_vector.span_mono by auto
    have \<open>(\<And> n. x n \<in> complex_vector.span T) \<Longrightarrow> x \<longlonglongrightarrow> l \<Longrightarrow> l \<in> complex_vector.span T\<close>
      for x l                                                          
    proof-
      assume \<open>\<And> n. x n \<in> complex_vector.span T\<close> and \<open>x \<longlonglongrightarrow> l\<close>
      define f where \<open>f = projection (complex_vector.span K)\<close> 
      have \<open>bounded_clinear f\<close>
        unfolding f_def using \<open>closed_subspace (complex_vector.span K)\<close>
        by (simp add: projectionPropertiesA)
      hence \<open>isCont f t\<close>
        for t
        by (simp add: bounded_linear_continuous)
      define y where \<open>y n = f (x n)\<close> for n
      define z where \<open>z n = x n - y n\<close> for n
      have \<open>y \<longlonglongrightarrow> f l\<close>
        using  \<open>isCont f l\<close> \<open>x \<longlonglongrightarrow> l\<close>
        unfolding y_def
        by (simp add: isCont_tendsto_compose)
      have \<open>f l \<in> complex_vector.span K\<close>
        unfolding f_def
        by (simp add: \<open>closed_subspace (complex_vector.span K)\<close> projection_intro2)
      hence \<open>f l \<in> complex_vector.span T\<close>
        using \<open>complex_vector.span K \<subseteq> complex_vector.span T\<close>
        by blast
      have \<open>z \<longlonglongrightarrow> l - f l\<close>
        unfolding z_def
        using \<open>x \<longlonglongrightarrow> l\<close> and \<open>y \<longlonglongrightarrow> f l\<close>
        by (simp add: tendsto_diff)
      have \<open>l - f l \<in> (complex_vector.span T)\<close>
      proof-
        have \<open>z m \<in> {c *\<^sub>C k| c. True}\<close>
          for m
        proof-
          have \<open>y m \<in> complex_vector.span K\<close>
            by (simp add: \<open>closed_subspace (complex_vector.span K)\<close> f_def projection_intro2 y_def)            
          hence \<open>y m \<in> complex_vector.span T\<close>
            using \<open>complex_vector.span K \<subseteq> complex_vector.span T\<close> by blast            
          hence \<open>z m \<in> complex_vector.span T\<close>
            unfolding z_def
            using \<open>x m \<in> complex_vector.span T\<close>
            by (simp add: complex_vector.span_diff)
          hence \<open>\<exists> r. z m = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
            using \<open>finite T\<close> span_explicit_finite[where T = "T" and x = "z m"]
            by blast
          then obtain r where \<open>z m = (\<Sum>a\<in>T. r a *\<^sub>C a)\<close>
            by blast
          have \<open>(\<Sum> a\<in>T. r a *\<^sub>C a) = r k *\<^sub>C k + (\<Sum> a\<in>K. r a *\<^sub>C a)\<close>
            by (simp add: \<open>T = insert k K\<close> \<open>finite K\<close> \<open>k \<notin> K\<close>)
          hence \<open>z m = r k *\<^sub>C k + (\<Sum>a\<in>K. r a *\<^sub>C a)\<close>
            using \<open>z m = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
            by simp
          hence \<open>f (z m) = f(r k *\<^sub>C k + (\<Sum>a\<in>K. r a *\<^sub>C a))\<close>
            by simp
          also have \<open>\<dots> = f(r k *\<^sub>C k) + f (\<Sum>a\<in>K. r a *\<^sub>C a)\<close>
            sorry
          have \<open>z m \<in> orthogonal_complement (complex_vector.span K)\<close>
            by (simp add: \<open>closed_subspace (complex_vector.span K)\<close> f_def projection_intro1 y_def z_def)
          have \<open>(\<Sum>a\<in>K. r a *\<^sub>C a) \<in> complex_vector.span K\<close>
            by (simp add: complex_vector.span_base complex_vector.span_scale complex_vector.span_sum)

          thus ?thesis sorry
        qed
        moreover have \<open>closed {c *\<^sub>C k| c. True}\<close>
          using closed_line by blast
        ultimately have \<open>l - f l \<in> {c *\<^sub>C k| c. True}\<close>
          using \<open>z \<longlonglongrightarrow> l - f l\<close> closed_sequentially by blast
        moreover have \<open>{c *\<^sub>C k| c. True} \<subseteq> complex_vector.span T\<close>
        proof - (* sledgehammer *)
          have f1: "\<forall>A Aa. (\<exists>a. (a::'a) \<in> A \<and> a \<notin> Aa) \<or> A \<subseteq> Aa"
            by (meson subsetI)
          obtain aa :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
            f2: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (aa x0 x1 \<in> x1 \<and> aa x0 x1 \<notin> x0)"
            by moura
          obtain cc :: "'a \<Rightarrow> complex" where
            f3: "\<forall>a. ((\<nexists>c. a = c *\<^sub>C k) \<or> a = cc a *\<^sub>C k) \<and> ((\<exists>c. a = c *\<^sub>C k) \<or> (\<forall>c. a \<noteq> c *\<^sub>C k))"
            by moura
          have "k \<in> complex_vector.span (insert k K)"
            by (meson complex_vector.span_superset in_mono insertI1)
          moreover
          { assume "(cc (aa (complex_vector.span T) {a. \<exists>c. a = c *\<^sub>C k}) *\<^sub>C k \<in> complex_vector.span (insert k K)) \<noteq> (aa (complex_vector.span T) {a. \<exists>c. a = c *\<^sub>C k} \<in> complex_vector.span T)"
            then have "aa (complex_vector.span T) {a. \<exists>c. a = c *\<^sub>C k} \<notin> {a. \<exists>c. a = c *\<^sub>C k} \<or> aa (complex_vector.span T) {a. \<exists>c. a = c *\<^sub>C k} \<in> complex_vector.span T"
              using f3 \<open>T = insert k K\<close> by fastforce
            then have ?thesis
              using f2 f1 by meson }
          ultimately show ?thesis
            using f2 f1 by (meson complex_vector.span_scale)
        qed
        ultimately show ?thesis by blast
      qed
      thus ?thesis using \<open>f l \<in> complex_vector.span T\<close>
      proof -
        have "l \<in> complex_vector.span (insert l T)"
          by (meson complex_vector.span_base insertI1)
        then show ?thesis
          by (metis \<open>f l \<in> complex_vector.span T\<close> \<open>l - f l \<in> complex_vector.span T\<close> complex_vector.eq_span_insert_eq complex_vector.span_redundant)
      qed        
    qed
    thus ?thesis
      using closed_sequential_limits by blast 
  qed
  thus ?case by blast
qed

(* TODO move *)
lemma closed_finite_dim:
  fixes T::\<open>'a::chilbert_space set\<close>
  assumes \<open>finite T\<close>
  shows \<open>closed (complex_vector.span T)\<close>
  using assms closed_finite_dim_induction by blast  

hide_fact closed_finite_dim_induction

(* TODO move *)
lemma span_finite_dim:
  fixes T::\<open>'a::chilbert_space set\<close>
  assumes \<open>finite T\<close>
  shows \<open>closure (complex_vector.span T)  = complex_vector.span T\<close>
  using closed_finite_dim
  by (simp add: closed_finite_dim assms)

(* TODO: move *)
lemma Ortho_expansion_finite:
  fixes T::\<open>'a::chilbert_space set\<close>
  assumes \<open>is_onb T\<close> and \<open>finite T\<close>
  shows \<open>x = (\<Sum>t\<in>T. \<langle> t, x \<rangle> *\<^sub>C t)\<close>
proof-
  have \<open>closure (complex_vector.span T) = UNIV\<close>
    using \<open>is_onb T\<close>
    unfolding is_onb_def is_basis_def
    by blast
  moreover have \<open>closure (complex_vector.span T)  = complex_vector.span T\<close>
    using \<open>finite T\<close> span_finite_dim by blast
  ultimately have \<open>complex_vector.span T = UNIV\<close>
    by blast
  have \<open>\<exists> r. x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    using span_explicit_finite \<open>finite T\<close> and \<open>complex_vector.span T = UNIV\<close>
    by blast    
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
      using that
      sorry
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
 (*     using Ortho_expansion_finite[where T = "set canonical_basis" and x = "X n"]
        \<open>is_onb (set canonical_basis)\<close>  \<open>finite (set canonical_basis)\<close> *)
      sorry
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

unbundle no_bounded_notation

end

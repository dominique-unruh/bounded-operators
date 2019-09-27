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

(* TODO replace C1_to_complex \<rightarrow> one_dim_to_complex (in several places)*)

lemma cinner_1_C1: "cinner 1 \<psi> = C1_to_complex \<psi>"
  (* apply transfer by (simp add: singleton_UNIV) *) sorry

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
  (* apply transfer by simp *) sorry

lemma C1_to_complex_times[simp]: "C1_to_complex (\<psi> * \<phi>) = C1_to_complex \<psi> * C1_to_complex \<phi>"
  (* apply transfer by simp *) sorry

lemma ell2_to_bounded_adj_times_ell2_to_bounded[simp]:
  includes bounded_notation
  shows "ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi> = cinner \<psi> \<phi> *\<^sub>C idOp"
proof -
  have "C1_to_complex ((ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi>) *\<^sub>v \<gamma>) = C1_to_complex ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>v \<gamma>)" 
    for \<gamma> :: "'c::{CARD_1,enum} ell2"
    by (simp add: times_applyOp)
  hence "((ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi>) *\<^sub>v \<gamma>) = ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>v \<gamma>)" 
    for \<gamma> :: "'c::{CARD_1,enum} ell2"
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
proof-
  have \<open>-(- A \<squnion> - B) = A \<sqinter> B\<close>
  proof-
    have \<open>-(- A \<squnion> - B) \<le> A\<close>
    proof-
      have \<open>- A \<squnion> - B \<ge> -A\<close>
        by simp        
      thus ?thesis
        by (metis ortho_antimono ortho_involution) 
    qed
    moreover have \<open>-(- A \<squnion> - B) \<le> B\<close>
    proof-
      have \<open>- A \<squnion> - B \<ge> -B\<close>
        by simp        
      thus ?thesis
        by (metis ortho_antimono ortho_involution) 
    qed
    ultimately show ?thesis
    proof - (* sledgehammer *)
      have f1: "\<forall>a aa ab. (ab::'a) \<sqinter> aa \<squnion> ab \<sqinter> a \<squnion> ab \<sqinter> (aa \<squnion> a) = ab \<sqinter> (aa \<squnion> a)"
        by (meson distrib_inf_le sup.absorb_iff2)
      have f2: "\<forall>a aa. - (a::'a) \<squnion> - aa = - aa \<or> \<not> aa \<le> a"
        by (metis ortho_antimono sup.absorb_iff2)
      have "\<forall>a aa. (aa::'a) \<sqinter> a \<le> a"
        by auto
      then have f3: "\<forall>a aa. (aa::'a) \<le> aa \<squnion> a"
        by (metis inf_sup_absorb)
      have f4: "\<forall>a aa. (aa::'a) \<sqinter> a = aa \<or> \<not> aa \<le> a"
        using f2 by (metis (no_types) inf_sup_absorb ortho_antimono ortho_involution)
      have f5: "\<forall>a aa. (aa::'a) \<squnion> a \<squnion> aa = aa \<squnion> a"
        using f1 by (metis (no_types) inf.cobounded1 inf_commute inf_sup_absorb sup.absorb_iff2)
      have f6: "\<forall>a aa. - (- (aa::'a) \<squnion> a) \<squnion> aa = aa"
        using f3 f2 by (metis (no_types) ortho_involution)
      then have "A \<sqinter> B \<squnion> - (- A \<squnion> - B) = A \<sqinter> B"
        using f5 f1 by (metis (no_types) \<open>- (- A \<squnion> - B) \<le> B\<close> inf_commute inf_sup_absorb sup.absorb_iff2)
      then have f7: "- (- A \<squnion> - B) \<squnion> A \<sqinter> B = A \<sqinter> B"
        by (metis (no_types) distrib_inf_le inf.cobounded1 inf_commute inf_sup_absorb sup.absorb_iff2)
      then have f8: "- A \<squnion> - B \<squnion> - (A \<sqinter> B) = - A \<squnion> - B"
        using f6 f5 by (metis (no_types))
      have f9: "- (A \<sqinter> B) \<sqinter> (- A \<squnion> - B) = - (A \<sqinter> B)"
        using f7 f4 by (metis (no_types) ortho_antimono ortho_involution sup.absorb_iff2)
      have "\<forall>a aa. - (aa::'a) \<sqinter> - (aa \<sqinter> a) = - aa"
        using f4 by (metis (full_types) inf.cobounded1 ortho_antimono)
      then have "- A \<squnion> - B = - (A \<sqinter> B)"
        using f9 f8 f1 by (metis (no_types) inf_commute)
      then show ?thesis
        by (simp add: ortho_involution)
    qed 
  qed
  hence \<open>A \<sqinter> B = -(- A \<squnion> - B)\<close>
    by simp
  thus ?thesis
    by (simp add: ortho_involution) 
qed

(* TODO: Claimed by https://en.wikipedia.org/wiki/Complemented_lattice *)
lemma demorgan_sup: "- ((A::_::orthocomplemented_lattice) \<squnion> B) = - A \<sqinter> - B"
  using demorgan_inf
  by (metis ortho_involution)

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

lemma isCont_scalar_right:
  fixes k :: \<open>'a::complex_normed_vector\<close>
  shows \<open>isCont (\<lambda> t. t *\<^sub>C k) a\<close>
proof(cases \<open>k = 0\<close>)
  case True
  thus ?thesis
    by simp 
next
  case False
  define f where \<open>f t = t *\<^sub>C k\<close> for t
  have \<open>c \<longlonglongrightarrow> a \<Longrightarrow> (f \<circ> c) \<longlonglongrightarrow> f a\<close>
    for c
  proof-
    assume \<open>c \<longlonglongrightarrow> a\<close>
    hence  \<open>(\<lambda> n. norm ((c n) - a) ) \<longlonglongrightarrow> 0\<close>
      by (simp add: LIM_zero_iff tendsto_norm_zero)      
    hence  \<open>(\<lambda> n. norm ((c n) - a) * norm k ) \<longlonglongrightarrow> 0\<close>
      using tendsto_mult_left_zero by auto      
    moreover have \<open>norm (((c n) - a) *\<^sub>C k) = norm ((c n) - a) * norm k\<close>
      for n
      by simp      
    ultimately have  \<open>(\<lambda> n. norm (((c n) - a) *\<^sub>C k)) \<longlonglongrightarrow> 0\<close>
      by simp
    moreover have \<open>((c n) - a) *\<^sub>C k = (c n) *\<^sub>C k - a *\<^sub>C k\<close>
      for n
      by (simp add: scaleC_left.diff)
    ultimately have  \<open>(\<lambda> n. norm ((c n) *\<^sub>C k - a *\<^sub>C k)) \<longlonglongrightarrow> 0\<close>
      by simp
    hence  \<open>(\<lambda> n. dist ((c n) *\<^sub>C k) (a *\<^sub>C k)) \<longlonglongrightarrow> 0\<close>
      by (metis (no_types) LIM_zero_cancel \<open>(\<lambda>n. norm (c n *\<^sub>C k - a *\<^sub>C k)) \<longlonglongrightarrow> 0\<close> tendsto_dist_iff tendsto_norm_zero_iff)
    hence  \<open>(\<lambda> n. dist (((\<lambda>t. t *\<^sub>C k) \<circ> c) n) (a *\<^sub>C k)) \<longlonglongrightarrow> 0\<close>
      by simp
    hence  \<open>((\<lambda>t. t *\<^sub>C k) \<circ> c) \<longlonglongrightarrow> a *\<^sub>C k\<close>
      using tendsto_dist_iff by blast      
    thus \<open>(f \<circ> c) \<longlonglongrightarrow> f a\<close> 
      unfolding f_def by blast
  qed
  hence \<open>isCont f a\<close>
    by (simp add: continuous_at_sequentially)    
  thus ?thesis 
    unfolding f_def by blast
qed

lemma closed_line:
  \<open>closed {c *\<^sub>C (k::'a::complex_inner)| c. True}\<close>
proof(cases \<open>k = 0\<close>)
  case True
  hence \<open>{c *\<^sub>C k| c. True} = {0}\<close>
    by auto
  thus ?thesis
    by simp
next
  case False
  hence \<open>norm k > 0\<close>
    by simp
  have \<open>(\<And> n. x n \<in> {c *\<^sub>C k| c. True}) \<Longrightarrow>
        x \<longlonglongrightarrow> l \<Longrightarrow> l \<in> {c *\<^sub>C k| c. True}\<close>
    for x l
  proof-
    assume \<open>\<And> n. x n \<in> {c *\<^sub>C k| c. True}\<close> and
      \<open>x \<longlonglongrightarrow> l\<close>
    from \<open>\<And> n. x n \<in> {c *\<^sub>C k| c. True}\<close>
    have \<open>\<And> n. \<exists> c. x n = c *\<^sub>C k\<close>
      by simp
    hence \<open>\<exists> c. \<forall> n. x n = (c n) *\<^sub>C k\<close>
      by metis
    then obtain c where \<open>\<And> n. x n = (c n) *\<^sub>C k\<close>
      by blast
    from \<open>x \<longlonglongrightarrow> l\<close>
    have \<open>convergent x\<close>
      using convergentI by auto
    hence \<open>Cauchy x\<close>
      using LIMSEQ_imp_Cauchy convergent_def by blast
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (x m) (x n) < e\<close>
      unfolding Cauchy_def
      by blast
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (x m - x n) < e\<close>
      using dist_norm
      by (simp add: dist_norm)
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m *\<^sub>C k - c n *\<^sub>C k) < e\<close>
      by (simp add: \<open>\<And>n. x n = c n *\<^sub>C k\<close>)
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) * norm k < e\<close>
      by (metis complex_vector.scale_left_diff_distrib norm_scaleC)
    hence f1: \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) < e/norm k\<close>
      by (simp add: False linordered_field_class.pos_less_divide_eq)
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) < (e*(norm k))/(norm k)\<close>
    proof-
      have \<open>e>0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) < (e*(norm k))/(norm k)\<close>
        for e
      proof-
        assume \<open>e > 0\<close>
        hence  \<open>e * norm k > 0\<close>
          using \<open>norm k > 0\<close>
          by simp
        thus ?thesis
          using f1 by fastforce
      qed
      thus ?thesis by blast
    qed
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (c m - c n) < e\<close>
      using \<open>norm k > 0\<close>
      by simp
    hence \<open>Cauchy c\<close>
      by (simp add: CauchyI)
    hence \<open>convergent c\<close>
      by (simp add: Cauchy_convergent_iff)
    hence \<open>\<exists> a. c \<longlonglongrightarrow> a\<close>
      by (simp add: convergentD)
    then obtain a where \<open>c \<longlonglongrightarrow> a\<close>
      by blast
    define f where \<open>f t = t *\<^sub>C k\<close> for t
    have \<open>isCont f a\<close>
      using isCont_scalar_right 
      unfolding f_def by blast
    hence \<open>(\<lambda> n. f (c n)) \<longlonglongrightarrow>  f a\<close>
      using  \<open>c \<longlonglongrightarrow> a\<close> 
        Topological_Spaces.isContD[where f = "f" and x = "a"]
        isCont_tendsto_compose by blast 
    hence \<open>(\<lambda> n. (c n) *\<^sub>C k) \<longlonglongrightarrow> a *\<^sub>C k\<close>
      unfolding f_def
      by simp
    hence \<open>(\<lambda> n. x n) \<longlonglongrightarrow> a *\<^sub>C k\<close>
      using \<open>\<And> n. x n = (c n) *\<^sub>C k\<close>
      by simp
    hence \<open>x \<longlonglongrightarrow> a *\<^sub>C k\<close>
      by simp
    hence \<open>l = a *\<^sub>C k\<close>
      using LIMSEQ_unique \<open>x \<longlonglongrightarrow> l\<close> by blast
    moreover have \<open>a *\<^sub>C k \<in> {c *\<^sub>C k |c. True}\<close>
      by auto
    ultimately show ?thesis by blast
  qed
  thus ?thesis
    using closed_sequential_limits by blast 
qed

(* TODO: remove lemma (subsumed by closed_finite_dim' below, hide_fact does not fully remove it) *)
(* TODO: Use \<And> and \<Longrightarrow> instead of \<forall>, \<longrightarrow> *)
lemma closed_finite_dim'_induction:
  \<open>\<forall> A::'a::complex_inner set. card A = n \<and> finite A \<and> 0 \<notin> A \<and> (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0) 
\<longrightarrow> closed (complex_vector.span A)\<close>
proof(induction n)
  case 0
  thus ?case
    by fastforce 
next
  case (Suc n)
  have \<open>card A = Suc n \<Longrightarrow> finite A \<Longrightarrow> 0 \<notin> A \<Longrightarrow> \<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0 
  \<Longrightarrow> closed (complex_vector.span A)\<close>
    for A::\<open>'a set\<close>
  proof-
    assume \<open>card A = Suc n\<close> and \<open>finite A\<close> and \<open>0 \<notin> A\<close> and
      \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
    from \<open>card A = Suc n\<close>
    have \<open>\<exists> b B. b \<notin> B \<and> A = insert b B\<close>
      by (meson card_Suc_eq)
    then obtain b B where \<open>b \<notin> B\<close> and \<open>A = insert b B\<close>
      by blast
    have \<open>card B = n\<close>
      using \<open>A = insert b B\<close> \<open>b \<notin> B\<close> \<open>card A = Suc n\<close> \<open>finite A\<close> 
      by auto      
    moreover have \<open>finite B\<close>
      using \<open>A = insert b B\<close> \<open>finite A\<close> 
      by auto
    moreover have \<open>0 \<notin> B\<close>
      using \<open>0 \<notin> A\<close> \<open>A = insert b B\<close> 
      by auto
    moreover have \<open>\<forall>a\<in>B. \<forall>a'\<in>B. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
      by (simp add: \<open>A = insert b B\<close> \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>)      
    ultimately have \<open>closed (complex_vector.span B)\<close>
      using Suc.IH by blast
    have \<open>(\<And> k. x k \<in> complex_vector.span A) \<Longrightarrow> x \<longlonglongrightarrow> l \<Longrightarrow> l \<in> complex_vector.span A\<close>
      for x l
    proof-
      assume \<open>\<And> k. x k \<in> complex_vector.span A\<close> and \<open>x \<longlonglongrightarrow> l\<close>
      have \<open>convergent x\<close>
        using  \<open>x \<longlonglongrightarrow> l\<close>
        unfolding convergent_def by blast
      have \<open>\<exists> c. x k - c *\<^sub>C b \<in> complex_vector.span B\<close>
        for k
        using \<open>A = insert b B\<close> \<open>\<And>k. x k \<in> complex_vector.span A\<close> complex_vector.span_breakdown_eq 
        by blast
      hence \<open>\<exists> c. \<forall> k. x k - (c k) *\<^sub>C b \<in> complex_vector.span B\<close>
        by metis
      then obtain c where \<open>\<And> k. x k - (c k) *\<^sub>C b \<in> complex_vector.span B\<close>
        by blast
      have \<open>convergent c\<close>
      proof-
        have \<open>b \<in> A\<close>
          by (simp add: \<open>A = insert b B\<close>)
        hence \<open>b \<noteq> 0\<close>
          using \<open>0 \<notin> A\<close> by auto          
        hence \<open>\<langle> b, b \<rangle> \<noteq> 0\<close>
          by simp          
        have \<open>\<langle> b, x k \<rangle> = c k * \<langle> b, b \<rangle>\<close>
          for k
        proof-
          have \<open>\<langle> b, x k \<rangle> = \<langle> b, (x k - c k *\<^sub>C b) + c k *\<^sub>C b\<rangle>\<close>
            by simp
          also have \<open>\<dots> = \<langle>b, x k - c k *\<^sub>C b\<rangle> + \<langle>b, c k *\<^sub>C b\<rangle>\<close>
            using cinner_right_distrib by blast
          also have \<open>\<dots> = \<langle>b, c k *\<^sub>C b\<rangle>\<close>
          proof-
            have \<open>b \<in> orthogonal_complement (complex_vector.span B)\<close>
            proof-
              have \<open>b' \<in> B \<Longrightarrow> \<langle>b, b'\<rangle> = 0\<close>
                for b'
                using \<open>A = insert b B\<close> \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close> \<open>b \<notin> B\<close> 
                by auto
              hence \<open>b' \<in> complex_vector.span B \<Longrightarrow> \<langle>b, b'\<rangle> = 0\<close>
                for b'
              proof-
                assume \<open>b' \<in> complex_vector.span B\<close>
                hence \<open>\<exists> T r. finite T \<and> T \<subseteq> B \<and> b' = (\<Sum>a \<in>T. r a *\<^sub>C a)\<close>
                  by (metis Complex_Vector_Spaces.span_finite span_explicit_finite)
                then obtain T r where \<open>finite T\<close> and \<open>T \<subseteq> B\<close> and \<open>b' = (\<Sum>a\<in>T. r a *\<^sub>C a)\<close>
                  by blast
                have \<open>\<langle>b, b'\<rangle> = (\<Sum>a\<in>T. \<langle>b, r a *\<^sub>C a\<rangle>)\<close>
                  using  \<open>finite T\<close> \<open>b' = (\<Sum>a\<in>T. r a *\<^sub>C a)\<close> cinner_sum_right by blast
                show \<open>\<langle>b, b'\<rangle> = 0\<close>
                proof-
                  have \<open>a \<in> T \<Longrightarrow> \<langle>b, r a *\<^sub>C a\<rangle> = 0\<close>
                    for a
                  proof-
                    assume \<open>a \<in> T\<close>
                    hence \<open>\<langle>b, a\<rangle> = 0\<close>
                      using \<open>T \<subseteq> B\<close> \<open>\<And>b'. b' \<in> B \<Longrightarrow> \<langle>b, b'\<rangle> = 0\<close>
                      by auto
                    thus ?thesis
                      by simp 
                  qed
                  thus ?thesis 
                    using \<open>\<langle>b, b'\<rangle> = (\<Sum>a\<in>T. \<langle>b, r a *\<^sub>C a\<rangle>)\<close> sum.not_neutral_contains_not_neutral 
                    by force                    
                qed
              qed
              thus ?thesis
                by (simp add: orthogonal_complement_I2) 
            qed
            hence \<open>\<langle>b, x k - c k *\<^sub>C b\<rangle> = 0\<close>
              using \<open>x k - c k *\<^sub>C b \<in> complex_vector.span B\<close>
              using orthogonal_complement_D1 by blast
            thus ?thesis by simp
          qed
          also have \<open>\<dots> = c k * \<langle>b, b\<rangle>\<close>
            by simp
          finally show ?thesis by blast
        qed
        moreover have \<open>(\<lambda> k. \<langle> b, x k \<rangle>) \<longlonglongrightarrow>  \<langle> b, l \<rangle>\<close>
          using \<open>x \<longlonglongrightarrow> l\<close>
          by (simp add: cinner_continuous_right)
        ultimately have \<open>(\<lambda> k. c k * \<langle> b, b \<rangle>) \<longlonglongrightarrow>  \<langle> b, l \<rangle>\<close>
          by simp
        hence \<open>convergent (\<lambda> k. c k * \<langle> b, b \<rangle>)\<close>
          using convergentI by auto
        hence \<open>convergent (\<lambda> k. (c k * \<langle> b, b \<rangle>)*(1/\<langle> b, b \<rangle>))\<close>
          using \<open>\<langle> b, b \<rangle> \<noteq> 0\<close>
          by (metis convergent_mult_const_right_iff divide_eq_0_iff zero_neq_one)          
        thus \<open>convergent c\<close>
          using \<open>\<langle> b, b \<rangle> \<noteq> 0\<close>
          by simp
      qed
      hence \<open>\<exists> a. c \<longlonglongrightarrow> a\<close>
        by (simp add: convergentD)
      then obtain a where \<open>c \<longlonglongrightarrow> a\<close>
        by blast
      moreover have \<open>isCont (\<lambda> t. t *\<^sub>C b) a\<close>
        using isCont_scalar_right by auto
      ultimately have \<open>(\<lambda> k. (c k) *\<^sub>C b) \<longlonglongrightarrow> a *\<^sub>C b\<close>
        using isCont_tendsto_compose[where g = "(\<lambda> t. t *\<^sub>C b)" and l = "a" and f = "c" 
            and F = "sequentially"]
        by blast
      hence \<open>(\<lambda> k. x k - (c k) *\<^sub>C b) \<longlonglongrightarrow> l - a *\<^sub>C b\<close>
        using \<open>x \<longlonglongrightarrow> l\<close> tendsto_diff by blast
      hence \<open>l - a *\<^sub>C b \<in> complex_vector.span B\<close>
        by (meson \<open>\<And>k. x k - c k *\<^sub>C b \<in> complex_vector.span B\<close> \<open>closed (complex_vector.span B)\<close> closed_sequentially)
      hence \<open>l - a *\<^sub>C b \<in> complex_vector.span A\<close>
        by (metis \<open>A = insert b B\<close> complex_vector.span_base complex_vector.span_breakdown_eq complex_vector.span_diff complex_vector.span_scale insertI1)
      moreover have \<open>a *\<^sub>C b \<in> complex_vector.span A\<close>
        by (simp add: \<open>A = insert b B\<close> complex_vector.span_base complex_vector.span_scale)
      ultimately show \<open>l \<in> complex_vector.span A\<close>
        using \<open>A = insert b B\<close> \<open>l - a *\<^sub>C b \<in> complex_vector.span B\<close> complex_vector.span_breakdown_eq 
        by blast 
    qed
    thus \<open>closed (complex_vector.span A)\<close>
      using closed_sequential_limits by blast      
  qed
  thus ?case by blast
qed

(* TODO: Use \<And> and \<Longrightarrow> instead of \<forall>, \<longrightarrow> *)
(* TODO: Remove lemma (subsumed by closed_finite_dim below) *)
lemma closed_finite_dim':
  fixes A::\<open>'a::complex_inner set\<close>
  assumes \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
    and \<open>0 \<notin> A\<close> and \<open>finite A\<close>
  shows \<open>closed (complex_vector.span A)\<close>
  using assms closed_finite_dim'_induction by blast

hide_fact closed_finite_dim'_induction

(* TODO: Holds for complex_normed_vector (with a different proof that even shows completeness). Use that proof? *)
lemma closed_finite_dim:
  fixes T::\<open>'a::complex_inner set\<close>
  assumes \<open>finite T\<close>
  shows \<open>closed (complex_vector.span T)\<close>
proof-
  have \<open>\<exists> A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> complex_vector.span A = complex_vector.span T
           \<and> 0 \<notin> A \<and> finite A\<close>
    using \<open>finite T\<close> Gram_Schmidt by blast
  then obtain A where \<open>\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
    and \<open>complex_vector.span A = complex_vector.span T\<close>
    and \<open>0 \<notin> A\<close> and \<open>finite A\<close>
    by auto
  hence \<open>closed (complex_vector.span A)\<close>
    using closed_finite_dim' by blast
  thus ?thesis 
    using \<open>complex_vector.span A = complex_vector.span T\<close>
    by auto
qed

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

unbundle no_bounded_notation

end


theory ToDo
imports Bounded_Operators Complex_L2 Tensor_Product
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
  have "C1_to_complex (ell2_to_bounded \<psi>* *\<^sub>v \<phi>) = cinner 1 (ell2_to_bounded \<psi>* *\<^sub>v \<phi>)"
    by (simp add: cinner_1_C1)
  also have "cinner 1 (ell2_to_bounded \<psi>* *\<^sub>v \<phi>) = cinner (ell2_to_bounded \<psi> *\<^sub>v 1) \<phi>"
    by (metis cinner_adjoint')
  also have "\<dots> = \<langle>\<psi>, \<phi>\<rangle>"
    by simp
  finally have "C1_to_complex (ell2_to_bounded \<psi>* *\<^sub>v \<phi>) = \<langle>\<psi>, \<phi>\<rangle>" by -
  then show ?thesis
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
  have "C1_to_complex ((ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi>) *\<^sub>v \<gamma>) = C1_to_complex ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>v \<gamma>)" for \<gamma> :: "unit ell2"
    by (simp add: times_applyOp)
  then have "((ell2_to_bounded \<psi>* *\<^sub>o ell2_to_bounded \<phi>) *\<^sub>v \<gamma>) = ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>v \<gamma>)" for \<gamma> :: "unit ell2"
    using C1_to_complex_inverse by metis
  then show ?thesis
    by (rule bounded_ext)
qed

lemma cinner_tensor: "\<langle>\<gamma> \<otimes> \<psi>, \<delta> \<otimes> \<phi>\<rangle> = \<langle>\<psi>, \<phi>\<rangle> * \<langle>\<gamma>, \<delta>\<rangle>"
  by (cheat cinner_tensor)

text \<open>This is a useful rule for establishing the equality of vectors\<close>
lemma cinner_ext_ell2: 
  assumes "\<And>\<gamma>. cinner \<gamma> \<psi> = cinner \<gamma> \<phi>"
  shows "\<gamma> = \<phi>"
  by (cheat cinner_ext_ell2)

lemma addState_adj_times_addState[simp]: 
  includes bounded_notation
  fixes \<psi> \<phi> :: "'a ell2"
  shows "addState \<psi>* *\<^sub>o addState \<phi> = \<langle>\<psi>, \<phi>\<rangle> *\<^sub>C (idOp::('b,'b) l2bounded)"
proof -
  have "\<langle>\<gamma>, (addState \<psi>* *\<^sub>o addState \<phi>) *\<^sub>v \<delta>\<rangle> = \<langle>\<gamma>, (\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp) *\<^sub>v \<delta>\<rangle>" for \<gamma> \<delta> :: "'b ell2"
    apply (simp add: times_applyOp cinner_adjoint'[symmetric])
    apply (transfer fixing: \<psi> \<phi> \<delta> \<gamma>)
    by (rule cinner_tensor)
  then have "(addState \<psi>* *\<^sub>o addState \<phi>) *\<^sub>v \<delta> = (\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp) *\<^sub>v \<delta>" for \<delta> :: "'b ell2"
    by (rule cinner_ext_ell2)
  then show ?thesis
    by (rule bounded_ext)
qed


lemma [simp]: "norm \<psi>=1 \<Longrightarrow> isometry (addState \<psi>)"
  unfolding isometry_def 
  by (simp add: cinner_norm_sq)


lemma [simp]: "ket i \<noteq> 0"
  using ell2_ket[of i] by force


lemma equal_ket:
  includes bounded_notation
  assumes "\<And>x. A *\<^sub>v ket x = B *\<^sub>v ket x"
  shows "A = B"
  by (cheat equal_ket)

lemma ket_product: "ket (a,b) = ket a \<otimes> ket b"
  by (cheat ket_product)

lemma tensorOp_applyOp_distr:
  includes bounded_notation
  shows "(A \<otimes> B) *\<^sub>v (\<psi> \<otimes> \<phi>) = (A *\<^sub>v \<psi>) \<otimes> (B *\<^sub>v \<phi>)"
  using cinner_ext_ell2 by blast

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

lemma assoc_op_apply_tensor[simp]:
  includes bounded_notation
  shows "assoc_op *\<^sub>v (\<psi>\<otimes>(\<phi>\<otimes>\<tau>)) = (\<psi>\<otimes>\<phi>)\<otimes>\<tau>"
  using cinner_ext_ell2 by blast

lemma comm_op_apply_tensor[simp]: 
  includes bounded_notation
  shows "comm_op *\<^sub>v (\<psi>\<otimes>\<phi>) = (\<phi>\<otimes>\<psi>)"
  using cinner_ext_ell2 by blast

lemma assoc_op_adj_apply_tensor[simp]:
  includes bounded_notation
  shows "assoc_op* *\<^sub>v ((\<psi>\<otimes>\<phi>)\<otimes>\<tau>) = \<psi>\<otimes>(\<phi>\<otimes>\<tau>)"
  using cinner_ext_ell2 by blast

lemma span_tensor: "Span G \<otimes> Span H = Span {g\<otimes>h|g h. g\<in>G \<and> h\<in>H}"
  by (cheat span_tensor)

lemma applyOpSpace_Span: 
  includes bounded_notation
  shows "A *\<^sub>s Span G = Span ((*\<^sub>v) A ` G)"
  by (cheat applyOpSpace_Span)

lemma span_ortho_span:
  assumes "\<And>s t. s\<in>S \<Longrightarrow> t\<in>T \<Longrightarrow> is_orthogonal s t"
  shows "Span S \<le> - (Span T)"
  by (cheat span_ortho_span)

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

lemma Span_range_ket[simp]: "Span (range ket) = top"
  by (cheat Span_range_ket)

lemma norm_mult_ineq_bounded:
  fixes A B :: "(_,_) bounded"
  shows "norm (A *\<^sub>o B) \<le> norm A * norm B"
  by (cheat norm_mult_ineq_bounded)

lemma equal_span':
  assumes "bounded_clinear f"
    and "bounded_clinear g"
  assumes "\<And>x. x\<in>G \<Longrightarrow> f x = g x"
  assumes "x\<in>closure (span G)"
  shows "f x = g x"
  by (cheat equal_span')

lemma span_tensors:
  "closure (span {C1 \<otimes> C2| (C1::(_,_) l2bounded) (C2::(_,_) l2bounded). True}) = UNIV"
  by (cheat span_tensors)

unbundle no_bounded_notation



end

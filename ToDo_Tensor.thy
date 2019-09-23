theory ToDo_Tensor
  imports Tensor_Product ToDo
begin

lemma cinner_tensor: "\<langle>\<gamma> \<otimes> \<psi>, \<delta> \<otimes> \<phi>\<rangle> = \<langle>\<psi>, \<phi>\<rangle> * \<langle>\<gamma>, \<delta>\<rangle>"
  by (cheat cinner_tensor)

lemma addState_adj_times_addState[simp]: 
  includes bounded_notation
  fixes \<psi> \<phi> :: "'a ell2"
  shows "addState \<psi>* *\<^sub>o addState \<phi> = \<langle>\<psi>, \<phi>\<rangle> *\<^sub>C (idOp::('b ell2,'b ell2) bounded)"
proof -
  have "\<langle>\<gamma>, (addState \<psi>* *\<^sub>o addState \<phi>) *\<^sub>v \<delta>\<rangle> = \<langle>\<gamma>, (\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp) *\<^sub>v \<delta>\<rangle>" for \<gamma> \<delta> :: "'b ell2"
    apply (simp add: times_applyOp cinner_adjoint'[symmetric])
    apply (transfer fixing: \<psi> \<phi> \<delta> \<gamma>)
    by (rule cinner_tensor)
  hence "(addState \<psi>* *\<^sub>o addState \<phi>) *\<^sub>v \<delta> = (\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp) *\<^sub>v \<delta>" for \<delta> :: "'b ell2"
    by (rule cinner_ext_ell2)
  thus ?thesis
    by (rule bounded_ext)
qed

lemma [simp]: "norm \<psi>=1 \<Longrightarrow> isometry (addState \<psi>)"
  unfolding isometry_def 
  by (simp add: cinner_norm_sq)

lemma ket_product: "ket (a,b) = ket a \<otimes> ket b"
  by (cheat ket_product)

lemma tensorOp_applyOp_distr:
  includes bounded_notation
  shows "(A \<otimes> B) *\<^sub>v (\<psi> \<otimes> \<phi>) = (A *\<^sub>v \<psi>) \<otimes> (B *\<^sub>v \<phi>)"
  using cinner_ext_ell2 sorry

lemma assoc_op_apply_tensor[simp]:
  includes bounded_notation
  shows "assoc_op *\<^sub>v (\<psi>\<otimes>(\<phi>\<otimes>\<tau>)) = (\<psi>\<otimes>\<phi>)\<otimes>\<tau>"
  using cinner_ext_ell2 sorry

lemma comm_op_apply_tensor[simp]: 
  includes bounded_notation
  shows "comm_op *\<^sub>v (\<psi>\<otimes>\<phi>) = (\<phi>\<otimes>\<psi>)"
  using cinner_ext_ell2 sorry

lemma assoc_op_adj_apply_tensor[simp]:
  includes bounded_notation
  shows "assoc_op* *\<^sub>v ((\<psi>\<otimes>\<phi>)\<otimes>\<tau>) = \<psi>\<otimes>(\<phi>\<otimes>\<tau>)"
  using cinner_ext_ell2 sorry

lemma span_tensor: "Span G \<otimes> Span H = Span {g\<otimes>h|g h. g\<in>G \<and> h\<in>H}"
  by (cheat span_tensor)

lemma span_tensors:
  "closure (span {C1 \<otimes> C2| (C1::(_,_) l2bounded) (C2::(_,_) l2bounded). True}) = UNIV"
  by (cheat span_tensors)



end

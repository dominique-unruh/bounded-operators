(*  Title:      Bounded-Operators/Bounded_Operators.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

References:

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}

*)


(*
We will derive the properties of bounded operators from 
the properties of Cstar_algebras
*)

theory Bounded_Operators
  imports Complex_L2 "HOL-Library.Adhoc_Overloading" Extended_Sorry
begin


subsection \<open>Bounded operators\<close>

typedef ('a,'b) bounded = "{A::'a ell2\<Rightarrow>'b ell2. bounded_clinear A}"
  morphisms applyOp Abs_bounded
  using bounded_clinear_zero by blast
setup_lifting type_definition_bounded
(* derive universe bounded *)

lift_definition idOp :: "('a,'a)bounded" is id
  by (metis bounded_clinear_ident comp_id fun.map_ident)

instantiation bounded :: (type,type) zero begin
lift_definition zero_bounded :: "('a,'b) bounded" is "\<lambda>_. 0" by simp
instance ..
end

lift_definition timesOp :: "('b,'c) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'c) bounded" is "(o)"
  unfolding o_def 
  by (rule bounded_clinear_compose, simp_all)

lift_definition applyOpSpace :: "('a,'b) bounded \<Rightarrow> 'a subspace \<Rightarrow> 'b subspace" is
  "\<lambda>A S. {A x|x. x\<in>S}"
  by (cheat applyOpSpace)

(* TODO: instantiation of scaleC instead! *)
lift_definition timesScalarOp :: "complex \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>c A x. c *\<^sub>C A x"
  by (rule bounded_clinear_const_scaleC)

(* TODO: is this even a meaningful operation? Do we use it anywhere? Remove? *)
(* TODO: instantiation of scaleC instead! *)
lift_definition timesScalarSpace :: "complex \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace" is
  "\<lambda>c S. {c *\<^sub>C x|x. x\<in>S}"
  by (smt Collect_cong applyOpSpace.rsp bounded_clinear_scaleC_right eq_onp_same_args rel_fun_eq_onp_rel)

consts
  adjoint :: "('a,'b) bounded \<Rightarrow> ('b,'a) bounded" ("_*" [99] 100)

lemma applyOp_0[simp]: "applyOpSpace U 0 = 0" 
  apply transfer
  by (simp add: additive.zero bounded_clinear_def clinear.axioms(1))

lemma times_applyOp: "applyOp (timesOp A B) \<psi> = applyOp A (applyOp B \<psi>)" 
  apply transfer by simp

lemma timesScalarSpace_0[simp]: "timesScalarSpace 0 S = 0"
  apply transfer apply (auto intro!: exI[of _ 0])
  by (simp add: is_linear_manifold.zero is_subspace.subspace) 


lemma timesScalarSpace_not0[simp]: "a \<noteq> 0 \<Longrightarrow> timesScalarSpace a S = S"
  apply transfer apply auto
  by (cheat timesScalarSpace_not0)

lemma one_times_op[simp]: "timesScalarOp (1::complex) B = B" 
  apply transfer by simp

lemma scalar_times_adj[simp]: "(timesScalarOp a A)* = timesScalarOp (cnj a) (A*)" for A::"('a,'b)bounded"
  by (cheat scalar_times_adj)

lemma timesOp_assoc: "timesOp (timesOp A B) C = timesOp A (timesOp B C)" 
  apply transfer by auto

lemma times_adjoint[simp]: "adjoint (timesOp A B) = timesOp (adjoint B) (adjoint A)" 
  by (cheat times_adjoint)

lemma timesOp_assoc_subspace: "applyOpSpace (timesOp A B) S = applyOpSpace A (applyOpSpace B S)" 
  apply transfer by auto

instantiation bounded :: (type,type) ab_group_add begin
lift_definition plus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>a b x. a x + b x"
  by (rule bounded_clinear_add)
lift_definition minus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>a b x. a x - b x"
  by (rule bounded_clinear_sub)
lift_definition uminus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>a x. - a x"
  by (rule bounded_clinear_minus)
instance 
  apply intro_classes
  by (transfer; auto)+
end

(* TODO: where are these definitions needed? Should they be in qrhl-tool instead? *)
lemmas assoc_left = timesOp_assoc[symmetric] timesOp_assoc_subspace[symmetric] add.assoc[where ?'a="('a,'b) bounded", symmetric]
lemmas assoc_right = timesOp_assoc timesOp_assoc_subspace add.assoc[where ?'a="('a,'b) bounded"]


lemma scalar_times_op_add[simp]: "timesScalarOp a (A+B) = timesScalarOp a A + timesScalarOp a B"
  apply transfer
  by (simp add: scaleC_add_right) 
lemma scalar_times_op_minus[simp]: "timesScalarOp a (A-B) = timesScalarOp a A - timesScalarOp a B"
  apply transfer
  by (simp add: complex_vector.scale_right_diff_distrib)

lemma applyOp_bot[simp]: "applyOpSpace U bot = bot"
  by (simp add: subspace_zero_bot[symmetric])

lemma equal_basis: "(\<And>x. applyOp A (ket x) = applyOp B (ket x)) \<Longrightarrow> A = B"
  by (cheat equal_basis)

lemma adjoint_twice[simp]: "(U*)* = U" for U :: "('a,'b) bounded"
  by (cheat adjoint_twice)

(* TODO: move specialized syntax into QRHL-specific file *)
consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)
adhoc_overloading
  cdot timesOp applyOp applyOpSpace timesScalarOp timesScalarSpace

lemma cdot_plus_distrib[simp]: "U \<cdot> (A + B) = U \<cdot> A + U \<cdot> B"
  for A B :: "'a subspace" and U :: "('a,'b) bounded"
  apply transfer 
  by (cheat cdot_plus_distrib)

lemma scalar_op_subspace_assoc [simp]: 
  "(\<alpha>\<cdot>A)\<cdot>S = \<alpha>\<cdot>(A\<cdot>S)" for \<alpha>::complex and A::"('a,'b)bounded" and S::"'a subspace"
  apply transfer by auto

lemma apply_idOp[simp]: "applyOp idOp \<psi> = \<psi>"
  by (simp add: idOp.rep_eq)

lemma scalar_mult_0_op[simp]: "(0::complex) \<cdot> A = 0" for A::"('a,'b)bounded"
  apply transfer by auto

lemma scalar_op_op[simp]: "(a \<cdot> A) \<cdot> B = a \<cdot> (A \<cdot> B)"
  for a :: complex and A :: "('a,'b) bounded" and B :: "('c,'a) bounded"
  apply transfer by auto

lemma op_scalar_op[simp]: "A \<cdot> (a \<cdot> B) = a \<cdot> (A \<cdot> B)" 
  for a :: complex and A :: "('a,'b) bounded" and B :: "('c,'a) bounded"
  apply transfer
  by (simp add: bounded_clinear.clinear clinear.scaleC o_def)
  
lemma scalar_scalar_op[simp]: "a \<cdot> (b \<cdot> A) = (a*b) \<cdot> A"
  for a b :: complex and A  :: "('a,'b) bounded"
  apply transfer by auto

lemma scalar_op_vec[simp]: "(a \<cdot> A) \<cdot> \<psi> = a *\<^sub>C (A \<cdot> \<psi>)" 
  for a :: complex and A :: "('a,'b) bounded" and \<psi> :: "'a ell2"
  apply transfer by auto

lemma add_scalar_mult: "a\<noteq>0 \<Longrightarrow> a \<cdot> A = a \<cdot> B \<Longrightarrow> A=B" for A B :: "('a,'b)bounded" and a::complex 
  apply transfer apply (rule ext)
  by (meson complex_vector.scale_cancel_left)

lemma apply_idOp_space[simp]: "applyOpSpace idOp S = S"
  apply transfer by simp

lemma apply_0[simp]: "applyOp U 0 = 0"
  using additive.zero applyOp bounded_clinear.clinear clinear.axioms(1) by blast

lemma times_idOp1[simp]: "U \<cdot> idOp = U"
  apply transfer by auto

lemma times_idOp2[simp]: "idOp \<cdot> V = V" for V :: "('b,'a) bounded"
  apply transfer by auto

lemma idOp_adjoint[simp]: "idOp* = idOp"
  by (cheat idOp_adjoint)

lemma mult_INF[simp]: "U \<cdot> (INF x. V x) = (INF x. U \<cdot> V x)" 
  for V :: "'a \<Rightarrow> 'b subspace" and U :: "('b,'c) bounded"
  apply transfer apply auto
  by (cheat mult_INF)

lemma mult_inf_distrib[simp]: "U \<cdot> (B \<sqinter> C) = (U \<cdot> B) \<sqinter> (U \<cdot> C)" 
  for U :: "('a,'b) bounded" and B C :: "'a subspace"
  using mult_INF[where V="\<lambda>x. if x then B else C" and U=U]
  unfolding INF_UNIV_bool_expand
  by simp

definition "inj_option \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"
definition "inv_option \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (Hilbert_Choice.inv \<pi> (Some y)) else None)"
lemma inj_option_Some_pi[simp]: "inj_option (Some o \<pi>) = inj \<pi>"
  unfolding inj_option_def inj_def by simp

lemma inj_option_Some[simp]: "inj_option Some"
  using[[show_consts,show_types,show_sorts]]
  apply (rewrite asm_rl[of "(Some::'a\<Rightarrow>_) = Some o id"]) apply simp
  unfolding inj_option_Some_pi by simp

lemma inv_option_Some: "surj \<pi> \<Longrightarrow> inv_option (Some o \<pi>) = Some o (Hilbert_Choice.inv \<pi>)"
  unfolding inv_option_def o_def inv_def apply (rule ext) by auto
lemma inj_option_map_comp[simp]: "inj_option f \<Longrightarrow> inj_option g \<Longrightarrow> inj_option (f \<circ>\<^sub>m g)"
  unfolding inj_option_def apply auto
  by (smt map_comp_Some_iff)

lemma inj_option_inv_option[simp]: "inj_option (inv_option \<pi>)"
proof (unfold inj_option_def, rule allI, rule allI, rule impI, erule conjE)
  fix x y
  assume same: "inv_option \<pi> x = inv_option \<pi> y"
    and pix_not_None: "inv_option \<pi> x \<noteq> None"
  have x_pi: "Some x \<in> range \<pi>" 
    using pix_not_None unfolding inv_option_def apply auto
    by (meson option.distinct(1))
  have y_pi: "Some y \<in> range \<pi>" 
    using pix_not_None unfolding same unfolding inv_option_def apply auto
    by (meson option.distinct(1))
  have "inv_option \<pi> x = Some (Hilbert_Choice.inv \<pi> (Some x))"
    unfolding inv_option_def using x_pi by simp
  moreover have "inv_option \<pi> y = Some (Hilbert_Choice.inv \<pi> (Some y))"
    unfolding inv_option_def using y_pi by simp
  ultimately have "Hilbert_Choice.inv \<pi> (Some x) = Hilbert_Choice.inv \<pi> (Some y)"
    using same by simp
  then show "x = y"
    by (meson inv_into_injective option.inject x_pi y_pi)
qed


consts classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> ('a,'b) bounded"
lemma classical_operator_basis: "inj_option \<pi> \<Longrightarrow>
    applyOp (classical_operator \<pi>) (ket x) = (case \<pi> x of Some y \<Rightarrow> ket y | None \<Rightarrow> 0)"
  by (cheat TODO5)
lemma classical_operator_adjoint[simp]: 
  "inj_option \<pi> \<Longrightarrow> adjoint (classical_operator \<pi>) = classical_operator (inv_option \<pi>)"
for \<pi> :: "'a \<Rightarrow> 'b option"
  by (cheat TODO1)


lemma classical_operator_mult[simp]:
  "inj_option \<pi> \<Longrightarrow> inj_option \<rho> \<Longrightarrow> classical_operator \<pi> \<cdot> classical_operator \<rho> = classical_operator (map_comp \<pi> \<rho>)"
  apply (rule equal_basis)
  unfolding times_applyOp
  apply (subst classical_operator_basis, simp)+
  apply (case_tac "\<rho> x")
   apply auto
  apply (subst classical_operator_basis, simp)
  by auto


lemma classical_operator_Some[simp]: "classical_operator Some = idOp"
  apply (rule equal_basis) apply (subst classical_operator_basis) apply simp by auto

definition "unitary U = (U \<cdot> (U*) = idOp \<and> U* \<cdot> U = idOp)"  
definition "isometry U = (U* \<cdot> U = idOp)"  

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* \<cdot> U = idOp" unfolding isometry_def by simp
lemma UadjU[simp]: "unitary U \<Longrightarrow> U \<cdot> U* = idOp" unfolding unitary_def by simp

lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"('a,'b)bounded"
  unfolding unitary_def by auto

lemma unitary_times[simp]: "unitary A \<Longrightarrow> unitary B \<Longrightarrow> unitary (A\<cdot>B)"
  unfolding unitary_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma isometry_times[simp]: "isometry A \<Longrightarrow> isometry B \<Longrightarrow> isometry (A\<cdot>B)"
  unfolding isometry_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma isometry_classical_operator[simp]:
  assumes "inj \<pi>"
  shows "isometry (classical_operator (Some o \<pi>))"
proof -
  have comp: "inv_option (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>) = Some" 
    apply (rule ext) unfolding inv_option_def o_def 
    using assms unfolding inj_def inv_def by auto

  show ?thesis
    unfolding isometry_def
    apply (subst classical_operator_adjoint) using assms apply simp
    apply (subst classical_operator_mult) using assms apply auto[2]
    apply (subst comp)
    by simp
qed

lemma unitary_classical_operator[simp]:
  assumes "bij \<pi>"
  shows "unitary (classical_operator (Some o \<pi>))"
proof (unfold unitary_def, rule conjI)
  have "isometry (classical_operator (Some o \<pi>))"
    by (simp add: assms bij_is_inj)
  then show "classical_operator (Some \<circ> \<pi>)* \<cdot> classical_operator (Some \<circ> \<pi>) = idOp"
    unfolding isometry_def by simp
next
  have "inj \<pi>"
    by (simp add: assms bij_is_inj)
  have comp: "Some \<circ> \<pi> \<circ>\<^sub>m inv_option (Some \<circ> \<pi>) = Some"
    apply (rule ext)
    unfolding inv_option_def o_def map_comp_def
    unfolding inv_def apply auto
    apply (metis \<open>inj \<pi>\<close> inv_def inv_f_f)
    by (metis assms bij_def image_iff range_eqI)

  show "classical_operator (Some \<circ> \<pi>) \<cdot> classical_operator (Some \<circ> \<pi>)* = idOp"
    by (simp add: comp \<open>inj \<pi>\<close>)
qed

lemma unitary_image[simp]: "unitary U \<Longrightarrow> applyOpSpace U top = top"
  by (cheat TODO1)

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def by simp

(* TODO: put somewhere better. Also: exists in standard library? *)
class singleton = fixes the_single :: "'a" assumes everything_the_single: "x=the_single" begin
lemma singleton_UNIV: "UNIV = {the_single}"
  using everything_the_single by auto
lemma everything_the_same: "(x::'a)=y"
  apply (subst everything_the_single, subst (2) everything_the_single) by simp
lemma singleton_ext: "x (a::'a) = y b \<Longrightarrow> x = y"
  apply (rule ext) 
  apply (subst (asm) everything_the_same[where x=a])
  apply (subst (asm) everything_the_same[where x=b])
  by simp
lemma CARD_singleton[simp]: "CARD('a) = 1"
  by (simp add: singleton_UNIV)
subclass finite apply standard unfolding singleton_UNIV by simp  
end

instantiation unit :: singleton begin
definition "singleton = ()"
instance apply standard by auto
end

lift_definition C1_to_complex :: "'a::singleton ell2 \<Rightarrow> complex" is
  "\<lambda>\<psi>. \<psi> the_single" .
lift_definition complex_to_C1 :: "complex \<Rightarrow> 'a::singleton ell2" is
  "\<lambda>c _. c" 
  by simp

lemma C1_to_complex_inverse[simp]: "complex_to_C1 (C1_to_complex \<psi>) = \<psi>"
  apply transfer apply (rule singleton_ext) by auto

lemma complex_to_C1_inverse[simp]: "C1_to_complex (complex_to_C1 \<psi>) = \<psi>"
  apply transfer by simp

lemma bounded_clinear_complex_to_C1: "bounded_clinear complex_to_C1"
  apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def)+

lemma bounded_clinear_C1_to_complex: "bounded_clinear C1_to_complex"
  apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def singleton_UNIV)+

lift_definition ell2_to_bounded :: "'a ell2 \<Rightarrow> (unit,'a) bounded" is
  "\<lambda>(\<psi>::'a ell2) (x::unit ell2). C1_to_complex x *\<^sub>C \<psi>"
  by (simp add: bounded_clinear_C1_to_complex bounded_clinear_scaleC_const)

lemma ell2_to_bounded_applyOp: "ell2_to_bounded (A\<cdot>\<psi>) = A \<cdot> ell2_to_bounded \<psi>" for A :: "(_,_)bounded"
  apply transfer
  by (simp add: bounded_clinear_def clinear.scaleC o_def)

lemma ell2_to_bounded_scalar_times: "ell2_to_bounded (a *\<^sub>C \<psi>) = a \<cdot> ell2_to_bounded \<psi>" for a::complex
  apply (rewrite at "a *\<^sub>C \<psi>" DEADID.rel_mono_strong[of _ "(a\<cdot>idOp) \<cdot> \<psi>"])
   apply simp
  apply (subst ell2_to_bounded_applyOp)
  by simp

lift_definition kernel :: "('a,'b) bounded \<Rightarrow> 'a subspace" is ker_op
  by (metis ker_op_lin)

definition eigenspace :: "complex \<Rightarrow> ('a,'a) bounded \<Rightarrow> 'a subspace" where
  "eigenspace a A = kernel (A-a\<cdot>idOp)" 

lemma kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a\<cdot>A) = kernel A" 
  for a :: complex and A :: "('a,'b) bounded"
  apply transfer
  by (smt Collect_cong complex_vector.scale_eq_0_iff ker_op_def)

lemma kernel_0[simp]: "kernel 0 = top"
  apply transfer unfolding ker_op_def by simp

lemma kernel_id[simp]: "kernel idOp = 0"
  apply transfer unfolding ker_op_def by simp

lemma [simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a\<cdot>A) = eigenspace (b/a) A"
  unfolding eigenspace_def
  apply (rewrite at "kernel \<hole>" DEADID.rel_mono_strong[where y="a \<cdot> (A - b / a \<cdot> idOp)"])
   apply auto[1]
  by (subst kernel_scalar_times, auto)



section \<open>Projectors\<close>

(* TODO: link with definition from Complex_Inner (needs definition of adjoint, first) *)
definition "isProjector P = (P=P* \<and> P=P\<cdot>P)"

consts Proj :: "'a subspace \<Rightarrow> ('a,'a) bounded"
lemma isProjector_Proj[simp]: "isProjector (Proj S)"
  by (cheat TODO5)

lemma imageOp_Proj[simp]: "applyOpSpace (Proj S) top = S"
  by (cheat TODO5)

lemma Proj_leq: "Proj S \<cdot> A \<le> S"
  by (metis imageOp_Proj inf.orderE inf.orderI mult_inf_distrib top_greatest)


lemma Proj_times: "A \<cdot> Proj S \<cdot> A* = Proj (A\<cdot>S)" for A::"('a,'b)bounded"
  by (cheat TODO2)

abbreviation proj :: "'a ell2 \<Rightarrow> ('a,'a) bounded" where "proj \<psi> \<equiv> Proj (span {\<psi>})"

lemma proj_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" for a::complex and \<psi>::"'a ell2"
  by (cheat TODO2)


lemma move_plus:
  "Proj (ortho C) \<cdot> A \<le> B \<Longrightarrow> A \<le> B + C"
for A B C::"'a subspace"
  by (cheat TODO2)


section \<open>Tensor products\<close>

consts "tensorOp" :: "('a,'b) bounded \<Rightarrow> ('c,'d) bounded \<Rightarrow> ('a*'c,'b*'d) bounded"
consts "tensorSpace" :: "'a subspace \<Rightarrow> 'c subspace \<Rightarrow> ('a*'c) subspace"
consts "tensorVec" :: "'a ell2 \<Rightarrow> 'c ell2 \<Rightarrow> ('a*'c) ell2"
consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infix "\<otimes>" 71)
adhoc_overloading tensor tensorOp tensorSpace tensorVec

lemma idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"
  by (cheat TODO2)

consts "comm_op" :: "('a*'b, 'b*'a) bounded"

lemma adj_comm_op[simp]: "adjoint comm_op = comm_op"
  by (cheat TODO2)

lemma
  comm_op_swap[simp]: "comm_op \<cdot> (A\<otimes>B) \<cdot> comm_op = B\<otimes>A"
  for A::"('a,'b) bounded" and B::"('c,'d) bounded"
  by (cheat TODO3)

lemma comm_op_times_comm_op[simp]: "comm_op \<cdot> comm_op = idOp"
proof -
  find_theorems "idOp \<otimes> idOp"
  have "comm_op \<cdot> (idOp \<otimes> idOp) \<cdot> comm_op = idOp \<otimes> idOp" by (simp del: idOp_tensor_idOp)
  then show ?thesis by simp
qed

lemma unitary_comm_op[simp]: "unitary comm_op"
  unfolding unitary_def by simp

consts "assoc_op" :: "('a*'b*'c, ('a*'b)*'c) bounded"
lemma unitary_assoc_op[simp]: "unitary assoc_op"
  by (cheat TODO5)

lemma tensor_scalar_mult1[simp]: "(a \<cdot> A) \<otimes> B = a \<cdot> (A \<otimes> B)" for a::complex and A::"('a,'b)bounded" and B::"('c,'d)bounded"
  by (cheat TODO3)
lemma tensor_scalar_mult2[simp]: "A \<otimes> (a \<cdot> B) = a \<cdot> (A \<otimes> B)" for a::complex and A::"('a,'b)bounded" and B::"('c,'d)bounded"
  by (cheat TODO3)

lemma tensor_times[simp]: "(U1 \<otimes> U2) \<cdot> (V1 \<otimes> V2) = (U1 \<cdot> V1) \<otimes> (U2 \<cdot> V2)"
  for V1 :: "('a1,'b1) bounded" and U1 :: "('b1,'c1) bounded"
   and V2 :: "('a2,'b2) bounded" and U2 :: "('b2,'c2) bounded"
  by (cheat TODO3)

consts remove_qvar_unit_op :: "('a*unit,'a) bounded"


definition addState :: "'a ell2 \<Rightarrow> ('b,'b*'a) bounded" where
  "addState \<psi> = idOp \<otimes> (ell2_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*"

lemma addState_times_scalar[simp]: "addState (a *\<^sub>C \<psi>) = a \<cdot> addState \<psi>" for a::complex and psi::"'a ell2"
  unfolding addState_def by (simp add: ell2_to_bounded_scalar_times)

lemma tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)"
  for U :: "('a,'b) bounded" and V :: "('c,'d) bounded"
  by (cheat TODO3)

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

end

(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee


*)


theory Quantum_State
  imports Bounded_Operators Complex_L2

begin

section \<open>Option\<close>

definition "inj_option \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"

definition 
"inv_option \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (Hilbert_Choice.inv \<pi> (Some y)) else None)"

lemma inj_option_Some_pi[simp]: "inj_option (Some o \<pi>) = inj \<pi>"
  unfolding inj_option_def inj_def by simp

lemma inj_option_Some[simp]: "inj_option Some"
  using[[show_consts,show_types,show_sorts]]
  by (simp add: inj_option_def)

lemma inv_option_Some: "surj \<pi> \<Longrightarrow> inv_option (Some o \<pi>) = Some o (Hilbert_Choice.inv \<pi>)"
  unfolding inv_option_def o_def inv_def apply (rule ext) by auto

lemma inj_option_map_comp[simp]: "inj_option f \<Longrightarrow> inj_option g \<Longrightarrow> inj_option (f \<circ>\<^sub>m g)"
  unfolding inj_option_def apply auto
  using map_comp_Some_iff by smt

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


section \<open>Classical operators\<close>

lift_definition classical_operator':: 
"(('a::chilbert_space \<Rightarrow> 'b::chilbert_space) option) \<Rightarrow> ('a \<Rightarrow> 'b)" 
is "\<lambda>\<pi> \<psi> b. case inv_option \<pi> b of Some a \<Rightarrow> \<psi> a | None \<Rightarrow> 0"



lift_definition classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> ('a ell2,'b ell2) bounded" is
  "classical_operator'"
  sorry

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
  unfolding timesOp_assoc_linear_space
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

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"(_,_)bounded"
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

(* TODO: Replace by existing class CARD_1 *)
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


(* TODO move to L2_Complex *)
instantiation ell2 :: (singleton) complex_algebra_1 begin
lift_definition one_ell2 :: "'a ell2" is "\<lambda>_. 1" by simp
lift_definition times_ell2 :: "'a ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'a ell2" is "\<lambda>a b _. a the_single * b the_single" by simp
instance 
proof
  show "(a::'a ell2) * b * c = a * (b * c)"
    for a :: "'a ell2"
      and b :: "'a ell2"
      and c :: "'a ell2"
    by (transfer, auto)
  show "((a::'a ell2) + b) * c = a * c + b * c"
    for a :: "'a ell2"
      and b :: "'a ell2"
      and c :: "'a ell2"
    apply (transfer, rule ext, auto)
    by (simp add: distrib_left mult.commute)
  show "(a::'a ell2) * (b + c) = a * b + a * c"
    for a :: "'a ell2"
      and b :: "'a ell2"
      and c :: "'a ell2"
    apply transfer apply (rule ext) apply auto
    using distrib_left by blast
  show "a *\<^sub>C (x::'a ell2) * y = a *\<^sub>C (x * y)"
    for a :: complex
      and x :: "'a ell2"
      and y :: "'a ell2"
    by (transfer, auto)
  show "(x::'a ell2) * a *\<^sub>C y = a *\<^sub>C (x * y)"
    for x :: "'a ell2"
      and a :: complex
      and y :: "'a ell2"
    by (transfer, auto)
  show "(1::'a ell2) * a = a"
    for a :: "'a ell2"
    apply (transfer, rule ext, auto simp: everything_the_single)
    by (metis (full_types) everything_the_single)
  show "(a::'a ell2) * 1 = a"
    for a :: "'a ell2"
    apply (transfer, rule ext, auto simp: everything_the_single)
    by (metis (full_types) everything_the_single)
  show "(0::'a ell2) \<noteq> 1"
    apply transfer
    by (meson zero_neq_one)
qed
end

(* TODO move to L2_Complex *)
lift_definition C1_to_complex :: "'a::singleton ell2 \<Rightarrow> complex" is
  "\<lambda>\<psi>. \<psi> the_single" .
(* TODO: abbreviation can be removed eventually *)
abbreviation "complex_to_C1 :: complex \<Rightarrow> 'a::singleton ell2 == of_complex"

(* lift_definition complex_to_C1 :: "complex \<Rightarrow> 'a::singleton ell2" is
  "\<lambda>c _. c" 
  by simp *)

lemma C1_to_complex_one[simp]: "C1_to_complex 1 = 1"
  apply transfer by simp

lemma C1_to_complex_inverse[simp]: "complex_to_C1 (C1_to_complex \<psi>) = \<psi>"
  unfolding of_complex_def apply transfer apply (rule singleton_ext) by auto

lemma complex_to_C1_inverse[simp]: "C1_to_complex (complex_to_C1 \<psi>) = \<psi>"
  unfolding of_complex_def apply transfer by simp

lemma bounded_clinear_complex_to_C1: "bounded_clinear complex_to_C1"
  unfolding of_complex_def apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def)+

lemma bounded_clinear_C1_to_complex: "bounded_clinear C1_to_complex"
  apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def singleton_UNIV)+

lift_definition ell2_to_bounded :: "'a::chilbert_space \<Rightarrow> (unit ell2,'a) bounded" is
  "\<lambda>(\<psi>::'a) (x::unit ell2). C1_to_complex x *\<^sub>C \<psi>"
  by (simp add: bounded_clinear_C1_to_complex bounded_clinear_scaleC_const)

lemma ell2_to_bounded_applyOp: "ell2_to_bounded (A\<cdot>\<psi>) = A \<cdot> ell2_to_bounded \<psi>" for A :: "(_,_)bounded"
  apply transfer
  by (simp add: bounded_clinear_def clinear.scaleC o_def)

lemma ell2_to_bounded_scalar_times: "ell2_to_bounded (a *\<^sub>C \<psi>) = a *\<^sub>C ell2_to_bounded \<psi>" for a::complex
  apply (rewrite at "a *\<^sub>C \<psi>" DEADID.rel_mono_strong[of _ "(a *\<^sub>C idOp) \<cdot> \<psi>"])
  apply transfer apply simp
  apply (subst ell2_to_bounded_applyOp)
  by simp

lift_definition kernel :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> 'a linear_space" is ker_op
  by (metis ker_op_lin)

definition eigenspace :: "complex \<Rightarrow> ('a::chilbert_space,'a) bounded \<Rightarrow> 'a linear_space" where
  "eigenspace a A = kernel (A - a *\<^sub>C idOp)" 

lemma kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a *\<^sub>C A) = kernel A"
  for a :: complex and A :: "(_,_) bounded"
  apply transfer
  by (smt Collect_cong complex_vector.scale_eq_0_iff ker_op_def)

lemma kernel_0[simp]: "kernel 0 = top"
  apply transfer unfolding ker_op_def by simp

lemma kernel_id[simp]: "kernel idOp = 0"
  apply transfer unfolding ker_op_def by simp

lemma [simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a *\<^sub>C A) = eigenspace (b/a) A"
  unfolding eigenspace_def
  apply (rewrite at "kernel \<hole>" DEADID.rel_mono_strong[where y="a *\<^sub>C (A - (b / a) *\<^sub>C idOp)"])
  apply auto[1]
  by (subst kernel_scalar_times, auto)

section \<open>Projectors\<close>

(* TODO: link with definition from Complex_Inner (needs definition of adjoint, first) *)
definition "isProjector P = (P=P* \<and> P=P\<cdot>P)"

consts Proj :: "'a linear_space \<Rightarrow> ('a,'a) bounded"
lemma isProjector_Proj[simp]: "isProjector (Proj S)"
  by (cheat TODO5)

lemma imageOp_Proj[simp]: "applyOpSpace (Proj S) top = S"
  by (cheat TODO5)

lemma Proj_leq: "Proj S \<cdot> A \<le> S"
  by (metis imageOp_Proj inf.orderE inf.orderI mult_inf_distrib top_greatest)


lemma Proj_times: "A \<cdot> Proj S \<cdot> A* = Proj (A\<cdot>S)" for A::"(_,_)bounded"
  by (cheat TODO2)

abbreviation proj :: "'a::chilbert_space \<Rightarrow> ('a,'a) bounded" where "proj \<psi> \<equiv> Proj (span {\<psi>})"

lemma proj_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" for a::complex and \<psi>::"'a ell2"
  by (cheat TODO2)


lemma move_plus:
  "Proj (ortho C) \<cdot> A \<le> B \<Longrightarrow> A \<le> B + C"
  for A B C::"_ linear_space"
  by (cheat TODO2)


section \<open>Tensor products\<close>

consts "tensorOp" :: "('a,'b) l2bounded \<Rightarrow> ('c,'d) l2bounded \<Rightarrow> ('a*'c,'b*'d) l2bounded"

lift_definition "tensorVec" :: "'a ell2 \<Rightarrow> 'c ell2 \<Rightarrow> ('a*'c) ell2" is
  "\<lambda>\<psi> \<phi> (x,y). \<psi> x * \<phi> y"
  by (cheat tensorVec)

definition "tensorSpace A B = span {tensorVec \<psi> \<phi>| \<psi> \<phi>. \<psi> \<in> Rep_linear_space A \<and> \<phi> \<in> Rep_linear_space B}"

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<otimes>" 71)
  adhoc_overloading tensor tensorOp tensorSpace tensorVec

lemma idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"
  by (cheat TODO2)

consts "comm_op" :: "('a*'b, 'b*'a) l2bounded"

lemma adj_comm_op[simp]: "adjoint comm_op = comm_op"
  by (cheat TODO2)

lemma
  comm_op_swap[simp]: "comm_op \<cdot> (A\<otimes>B) \<cdot> comm_op = B\<otimes>A"
  for A::"('a,'b) l2bounded" and B::"('c,'d) l2bounded"
  by (cheat TODO3)

lemma comm_op_times_comm_op[simp]: "comm_op \<cdot> comm_op = idOp"
proof -
  find_theorems "idOp \<otimes> idOp"
  have "comm_op \<cdot> (idOp \<otimes> idOp) \<cdot> comm_op = idOp \<otimes> idOp" by (simp del: idOp_tensor_idOp)
  then show ?thesis by simp
qed

lemma unitary_comm_op[simp]: "unitary comm_op"
  unfolding unitary_def by simp

consts "assoc_op" :: "('a*'b*'c, ('a*'b)*'c) l2bounded"
lemma unitary_assoc_op[simp]: "unitary assoc_op"
  by (cheat TODO5)

lemma tensor_scalar_mult1[simp]: "(a *\<^sub>C A) \<otimes> B = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)
lemma tensor_scalar_mult1_ell2[simp]: "(a *\<^sub>C A) \<otimes> B = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"_ ell2" and B::"_ ell2"
  by (cheat TODO3)
lemma tensor_scalar_mult2[simp]: "A \<otimes> (a *\<^sub>C B) = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)
lemma tensor_scalar_mult2_ell2[simp]: "A \<otimes> (a *\<^sub>C B) = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"_ ell2" and B::"_ ell2"
  by (cheat TODO3)
lemma tensor_plus: "(A+B) \<otimes> C = A \<otimes> C + B \<otimes> C" for A B C :: "(_,_)bounded"
  by (cheat tensor_plus)
lemma tensor_plus_ell2: "(A+B) \<otimes> C = A \<otimes> C + B \<otimes> C" for A B C :: "_ ell2"
  by (cheat tensor_plus)
lemma tensor_norm_ell2: "norm (\<psi> \<otimes> \<phi>) = norm \<psi> * norm \<phi>" for \<psi> \<phi> :: "_ ell2"
  by (cheat tensor_norm_ell2)

lemma tensor_times[simp]: "(U1 \<otimes> U2) \<cdot> (V1 \<otimes> V2) = (U1 \<cdot> V1) \<otimes> (U2 \<cdot> V2)"
  for V1 :: "('a1,'b1) l2bounded" and U1 :: "('b1,'c1) l2bounded"
    and V2 :: "('a2,'b2) l2bounded" and U2 :: "('b2,'c2) l2bounded"
  by (cheat TODO3)

lift_definition addState :: "'a ell2 \<Rightarrow> ('b,'b*'a) l2bounded" is
  \<open>\<lambda>\<psi> \<phi>. tensorVec \<phi> \<psi>\<close>
  apply (rule_tac K="norm ell2" in bounded_clinear_intro)
  by (auto simp: tensor_norm_ell2 tensor_plus_ell2)
  

(* TODO: this is simply the adjoint of addState (1::unit ell2), and addState y is best defined as x \<rightarrow> x \<otimes> y (lifted).
   Do we even use remove_qvar_unit_op then? *)
consts remove_qvar_unit_op :: "('a*unit,'a) l2bounded"


(* definition addState :: "'a ell2 \<Rightarrow> ('b,'b*'a) l2bounded" where
  "addState \<psi> = idOp \<otimes> (ell2_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*" *)

lemma addState_times_scalar[simp]: "addState (a *\<^sub>C \<psi>) = a *\<^sub>C addState \<psi>" for a::complex and psi::"'a ell2"
  apply transfer by auto

lemma tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)"
  for U :: "('a,'b) l2bounded" and V :: "('c,'d) l2bounded"
  by (cheat TODO3)

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

subsection \<open>Dual\<close>

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>continuous_on\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>)\<close>

class topological_real_vector = real_vector + topological_ab_group_add +
  assumes scaleR_continuous: "continuous_on UNIV (case_prod scaleR)"

class topological_complex_vector = complex_vector + topological_ab_group_add +
  assumes scaleC_continuous: "continuous_on UNIV (case_prod scaleC)"

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>continuous_on\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> ('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> bool\<close>)\<close>


instance topological_complex_vector \<subseteq> topological_real_vector
  apply standard
  apply (rewrite at "case_prod scaleR" DEADID.rel_mono_strong[of _ "\<lambda>x. (complex_of_real (fst x)) *\<^sub>C (snd x)"])
  apply (auto simp: scaleR_scaleC case_prod_beta)[1]
  unfolding continuous_on_def
  apply (auto intro!: tendsto_intros)
  using tendsto_fst tendsto_snd by fastforce+

instance real_normed_vector \<subseteq> topological_real_vector
proof standard 
  have "(\<lambda>(x, y). x *\<^sub>R y) \<midarrow>(a, b)\<rightarrow> a *\<^sub>R b" for a and b :: 'a
    unfolding case_prod_beta apply (rule Limits.tendsto_scaleR)
    using tendsto_fst tendsto_snd by fastforce+
  then show "continuous_on UNIV (\<lambda>(x, y::'a). x *\<^sub>R y)"
    unfolding continuous_on_def by simp
qed

instance complex_normed_vector \<subseteq> topological_complex_vector
proof standard 
  note tendsto_scaleC = bounded_bilinear.tendsto[OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]
  have "(\<lambda>(x, y). x *\<^sub>C y) \<midarrow>(a, b)\<rightarrow> a *\<^sub>C b" for a and b :: 'a
    unfolding case_prod_beta apply (rule tendsto_scaleC)
    using tendsto_fst tendsto_snd by fastforce+
  then show "continuous_on UNIV (\<lambda>(x, y::'a). x *\<^sub>C y)"
    unfolding continuous_on_def by simp
qed

lemma clinear_0[simp]: "clinear (\<lambda>f. 0)"
  unfolding clinear_def Modules.additive_def clinear_axioms_def by simp

typedef (overloaded) 'a dual = \<open>{f::'a::topological_complex_vector\<Rightarrow>complex. continuous_on UNIV f \<and> clinear f}\<close>
  apply (rule exI[where x="\<lambda>f. 0"]) by auto

instantiation dual :: (complex_normed_vector) chilbert_space begin
instance 
  by (cheat "dual :: (complex_normed_vector) chilbert_space")
end

subsection \<open>Dimension\<close>


lift_definition finite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> is
  \<open>\<lambda>S. \<exists>G. finite G \<and> complex_vector.span G = S\<close> .

(* lift_definition infinite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> is
\<open>\<lambda>S. (
\<exists> f::nat \<Rightarrow> 'a set.
(\<forall>n. is_subspace (f n)) \<and>
(\<forall> n. f n \<subset> f (Suc n)) \<and>
(\<forall> n. f n \<subseteq> S)
)\<close> *)


(* (* TODO: define on sets first and lift? *)
(* TODO: I would define only finite_dim and just negate it for infinite_dim (avoid too many definitions) *)
definition infinite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> where
\<open>infinite_dim S = (
\<exists> f::nat \<Rightarrow> 'a linear_space.
(\<forall> n::nat. Rep_linear_space (f n) \<subset> Rep_linear_space (f (Suc n))) \<and>
(\<forall> n::nat. Rep_linear_space (f n) \<subseteq> Rep_linear_space S)
)\<close> *)

(* definition finite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> where
\<open>finite_dim S = ( \<not> (infinite_dim S) )\<close> *)


subsection \<open>Tensor product\<close>

(* TODO: define Tensor later as "('a dual, 'b) hilbert_schmidt" *)

(* (* Tensor product *)
typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) tensor
(* TODO: is that compatible (isomorphic) with tensorVec? *)
= \<open>{ A :: ('a dual, 'b) bounded. finite_dim (Abs_linear_space ((Rep_bounded A) ` UNIV)) }\<close>
   *)

(* TODO: universal property of tensor products *)

(* Embedding of (x,y) into the tensor product as x\<otimes>y *)
(* TODO: Shouldn't this be called "tensor" or similar then? *)
(* definition HS_embedding :: \<open>('a::chilbert_space)*('b::chilbert_space) \<Rightarrow> ('a, 'b) tensor\<close> where
\<open>HS_embedding x = Abs_tensor ( Abs_bounded (\<lambda> w::'a dual. ( (Rep_bounded w) (fst x) ) *\<^sub>C (snd x) ) )\<close> *)

(* The tensor product of two Hilbert spaces is a Hilbert space *)
(* instantiation tensor :: (chilbert_space,chilbert_space) "chilbert_space" begin
instance 
end *)



end
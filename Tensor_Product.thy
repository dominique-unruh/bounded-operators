(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee


*)


theory Tensor_Product
  imports Bounded_Operators Complex_L2 "HOL-Library.Adhoc_Overloading"

begin

unbundle bounded_notation

consts "tensorOp" :: "('a ell2,'b ell2) bounded \<Rightarrow> ('c ell2,'d ell2) bounded \<Rightarrow> (('a*'c) ell2,('b*'d) ell2) bounded"

type_synonym ('a, 'b) l2bounded = "('a ell2,'b ell2) bounded"

lift_definition "tensorVec" :: "'a ell2 \<Rightarrow> 'c ell2 \<Rightarrow> ('a*'c) ell2" is
  "\<lambda>\<psi> \<phi> (x,y). \<psi> x * \<phi> y"
  by (cheat tensorVec)

definition "tensorSpace A B = span {tensorVec \<psi> \<phi>| \<psi> \<phi>. \<psi> \<in> space_as_set A \<and> \<phi> \<in> space_as_set B}"

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<otimes>" 71)
  adhoc_overloading tensor tensorOp tensorSpace tensorVec

lemma idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"
  by (cheat TODO2)

definition "comm_op" :: "(('a*'b) ell2, ('b*'a) ell2) bounded" where
  "comm_op = classical_operator (\<lambda>(a,b). Some (b,a))"

lemma adj_comm_op[simp]: "adjoint comm_op = comm_op"
  by (cheat TODO2)

lemma
  comm_op_swap[simp]: "comm_op \<cdot>\<^sub>o (A\<otimes>B) \<cdot>\<^sub>o comm_op = B\<otimes>A"
  for A::"('a ell2,'b ell2) bounded" and B::"('c ell2,'d ell2) bounded"
  by (cheat TODO3)

lemma comm_op_times_comm_op[simp]: "comm_op  \<cdot>\<^sub>o comm_op = idOp"
proof -
  have "comm_op  \<cdot>\<^sub>o (idOp \<otimes> idOp)  \<cdot>\<^sub>o comm_op = idOp \<otimes> idOp" by (simp del: idOp_tensor_idOp)
  then show ?thesis by simp
qed

lemma unitary_comm_op[simp]: "unitary comm_op"
  unfolding unitary_def by (cheat TODO)

definition "assoc_op" :: "(('a*('b*'c)) ell2, (('a*'b)*'c) ell2) bounded" where
  "assoc_op = classical_operator (\<lambda>(a,(b,c)). Some ((a,b),c))"

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

lemma tensor_times[simp]: "(U1 \<otimes> U2) \<cdot>\<^sub>o (V1 \<otimes> V2) = (U1 \<cdot>\<^sub>o V1) \<otimes> (U2 \<cdot>\<^sub>o V2)"
  for V1 :: "('a1,'b1) l2bounded" and U1 :: "('b1,'c1) l2bounded"
    and V2 :: "('a2,'b2) l2bounded" and U2 :: "('b2,'c2) l2bounded"
  by (cheat TODO3)

lift_definition addState :: "'a ell2 \<Rightarrow> ('b ell2,('b*'a) ell2) bounded" is
  \<open>\<lambda>\<psi> \<phi>. tensorVec \<phi> \<psi>\<close>
  apply (rule_tac K="norm ell2" in bounded_clinear_intro)
  by (auto simp: tensor_norm_ell2 tensor_plus_ell2)
  

(* TODO: this is simply the adjoint of addState (1::unit ell2), and addState y is best defined as x \<rightarrow> x \<otimes> y (lifted).
   Do we even use remove_qvar_unit_op then? *)
consts remove_qvar_unit_op :: "(('a*unit) ell2,'a ell2) bounded"


(* definition addState :: "'a ell2 \<Rightarrow> ('b,'b*'a) l2bounded" where
  "addState \<psi> = idOp \<otimes> (ell2_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*" *)

lemma addState_times_scalar[simp]: "addState (a *\<^sub>C \<psi>) = a *\<^sub>C addState \<psi>"
  for a::complex and \<psi>::"'a ell2"
  by (cheat TODO)

lemma tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)"
  for U :: "('a,'b) l2bounded" and V :: "('c,'d) l2bounded"
  by (cheat TODO3)

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  by (cheat TODO)


unbundle no_bounded_notation


end

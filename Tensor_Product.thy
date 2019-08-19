(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee


*)


theory Tensor_Product
  imports Bounded_Operators Complex_L2 "HOL-Library.Adhoc_Overloading" Completion

begin

section \<open>Tensor product\<close>

definition bifunctional :: \<open>'a \<Rightarrow> (('a \<Rightarrow> complex) \<Rightarrow> complex)\<close> where
  \<open>bifunctional x = (\<lambda> f. f x)\<close>

lift_definition Bifunctional' :: \<open>'a::complex_normed_vector \<Rightarrow> (('a, complex) bounded \<Rightarrow> complex)\<close> 
  is bifunctional.

lift_definition Bifunctional :: \<open>'a::complex_normed_vector \<Rightarrow> (('a, complex) bounded, complex) bounded\<close> 
  is Bifunctional'
proof
  show "clinear (Bifunctional' (a::'a))"
    for a :: 'a
    unfolding clinear_def proof
    show "Bifunctional' a (b1 + b2) = Bifunctional' a b1 + Bifunctional' a b2"
      for b1 :: "('a, complex) bounded"
        and b2 :: "('a, complex) bounded"
      by (simp add: Bifunctional'.rep_eq bifunctional_def plus_bounded.rep_eq)
    show "Bifunctional' a (r *\<^sub>C b) = r *\<^sub>C Bifunctional' a b"
      for r :: complex
        and b :: "('a, complex) bounded"
      by (simp add: Bifunctional'.rep_eq bifunctional_def)    
  qed
  show "\<exists>K. \<forall>x. cmod (Bifunctional' (a::'a) x) \<le> norm x * K"
    for a :: 'a
    apply transfer
    apply auto unfolding bifunctional_def
    using bounded_clinear.bounded_linear onorm by blast 
qed


definition
  cbilinear :: "('a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector) \<Rightarrow> bool" where
  "cbilinear f \<longleftrightarrow> (\<forall>x. clinear (\<lambda>y. f x y)) \<and> (\<forall>y. clinear (\<lambda>x. f x y))"

typedef (overloaded) ('a::complex_normed_vector, 'b::complex_vector) pre_hilbert_tensor
  = \<open>{f::('a, complex) bounded \<Rightarrow>'b\<Rightarrow>complex. cbilinear f}\<close>
  apply auto
proof
  show "cbilinear (\<lambda> _ _. 0)"
    unfolding cbilinear_def proof
    show "All ((\<lambda>x. clinear ((\<lambda>_. 0)::'d \<Rightarrow> 'e))::'c \<Rightarrow> bool)"
      by (simp add: complex_vector.module_hom_zero)
    show "All ((\<lambda>y. clinear ((\<lambda>x. 0)::'c \<Rightarrow> 'e))::'d \<Rightarrow> bool)"
      by (simp add: complex_vector.module_hom_zero)
  qed
qed


typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) hilbert_tensor 
  = \<open>(UNIV::((('a, 'b) pre_hilbert_tensor) completion) set)\<close>
  by (rule Set.UNIV_witness)

instantiation hilbert_tensor :: (chilbert_space, chilbert_space) chilbert_space
begin
instance 
  sorry
end


section \<open>Tensor product ell2\<close>

unbundle bounded_notation

consts "tensorOp" :: "('a ell2,'b ell2) bounded \<Rightarrow> ('c ell2,'d ell2) bounded \<Rightarrow> (('a*'c) ell2,('b*'d) ell2) bounded"

type_synonym ('a, 'b) l2bounded = "('a ell2,'b ell2) bounded"

lift_definition "tensorVec" :: "'a ell2 \<Rightarrow> 'c ell2 \<Rightarrow> ('a*'c) ell2" is
  "\<lambda>\<psi> \<phi> (x,y). \<psi> x * \<phi> y"
  by (cheat tensorVec)

definition tensorSpace :: "'a ell2 linear_space \<Rightarrow> 'b ell2 linear_space \<Rightarrow> ('a*'b) ell2 linear_space" where
  "tensorSpace A B = Span {tensorVec \<psi> \<phi>| \<psi> \<phi>. \<psi> \<in> space_as_set A \<and> \<phi> \<in> space_as_set B}"

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<otimes>" 71)
adhoc_overloading tensor tensorOp tensorSpace tensorVec

lemma idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"
  by (cheat TODO2)

definition "comm_op" :: "(('a*'b) ell2, ('b*'a) ell2) bounded" where
  "comm_op = classical_operator (\<lambda>(a,b). Some (b,a))"

lemma adj_comm_op[simp]: "adjoint comm_op = comm_op"
  by (cheat TODO2)

lemma
  comm_op_swap[simp]: "comm_op *\<^sub>o (A\<otimes>B) *\<^sub>o comm_op = B\<otimes>A"
  for A::"('a ell2,'b ell2) bounded" and B::"('c ell2,'d ell2) bounded"
  by (cheat TODO3)

lemma comm_op_times_comm_op[simp]: "comm_op  *\<^sub>o comm_op = idOp"
proof -
  have "comm_op  *\<^sub>o (idOp \<otimes> idOp)  *\<^sub>o comm_op = idOp \<otimes> idOp" by (simp del: idOp_tensor_idOp)
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

lemma tensor_times[simp]: "(U1 \<otimes> U2) *\<^sub>o (V1 \<otimes> V2) = (U1 *\<^sub>o V1) \<otimes> (U2 *\<^sub>o V2)"
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
  using assms unfolding unitary_def by simp

lemma tensor_isometry[simp]: 
  assumes "isometry U" and "isometry V"
  shows "isometry (U\<otimes>V)"
  using assms unfolding isometry_def by simp

unbundle no_bounded_notation


end

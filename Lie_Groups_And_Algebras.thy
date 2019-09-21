(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Lie_Groups_And_Algebras
  imports
    Tensor_Product

begin

unbundle bounded_notation

typedef (overloaded) ('a::complex_normed_vector) GL
  = \<open>{A::('a,'a) bounded. invertible_bounded A}\<close>
  morphisms Rep_GL Abs_GL
  proof
  show "(idOp::('a, 'a) bounded) \<in> {A. invertible_bounded A}"
    unfolding invertible_bounded_def by auto
qed

setup_lifting type_definition_GL

lift_definition GLtimesOp::\<open>'a::complex_normed_vector GL \<Rightarrow> 'a GL \<Rightarrow> 'a GL\<close>
is \<open>\<lambda> f g. f *\<^sub>o g\<close>
  unfolding invertible_bounded_def
  by (metis timesOp_assoc times_idOp1)

lift_definition GL_eval::\<open>'a::complex_normed_vector GL \<Rightarrow> 'a \<Rightarrow> 'a\<close>
is \<open>\<lambda> A v. A *\<^sub>v v\<close>.

bundle GL_notation begin
notation GLtimesOp (infixl "\<circ>\<^sub>G\<^sub>L" 69)
notation GL_eval (infixl "*\<^sub>G\<^sub>L" 69)
end

bundle no_GL_notation begin
no_notation GLtimesOp (infixl "\<circ>\<^sub>G\<^sub>L" 69)
no_notation GL_eval (infixl "*\<^sub>G\<^sub>L" 69)
end

unbundle GL_notation


instantiation GL :: (complex_normed_vector) group_add
begin

lift_definition zero_GL:: \<open>'a GL\<close> is idOp
  unfolding invertible_bounded_def
  by simp

lift_definition uminus_GL:: \<open>'a GL \<Rightarrow> 'a GL\<close> is 
\<open>inverse_bounded\<close>
  unfolding invertible_bounded_def
  using inverse_bounded_uniq by blast

lift_definition plus_GL:: \<open>'a GL \<Rightarrow> 'a GL \<Rightarrow> 'a GL\<close> is 
"(*\<^sub>o)"
  by (smt inverse_bounded_well_defined invertible_bounded_def timesOp_assoc times_idOp1)
(* > 1 s *)

definition minus_GL:: \<open>'a GL \<Rightarrow> 'a GL \<Rightarrow> 'a GL\<close> where
"minus_GL A B = A + (- B)"

instance
  proof
  show "(a::'a GL) + b + c = a + (b + c)"
    for a :: "'a GL"
      and b :: "'a GL"
      and c :: "'a GL"
    apply transfer
    by (simp add: timesOp_assoc)
  show "(0::'a GL) + a = a"
    for a :: "'a GL"
    apply transfer
    by simp
  show "(a::'a GL) + 0 = a"
    for a :: "'a GL"
    apply transfer
    by simp
  show "- (a::'a GL) + a = 0"
    for a :: "'a GL"
    apply transfer
    by (simp add: inverse_bounded_left)
  show "(a::'a GL) + - b = a - b"
    for a :: "'a GL"
      and b :: "'a GL"
    by (simp add: minus_GL_def)    
qed

end

typedef (overloaded) ('a::complex_inner) U
  = \<open>{A::'a GL. \<forall> x y. \<langle> A *\<^sub>G\<^sub>L x, A *\<^sub>G\<^sub>L y \<rangle> = \<langle>x, y\<rangle>}\<close>
  morphisms Rep_U Abs_U
  proof
  show "0 \<in> {A. \<forall>x y. \<langle>A *\<^sub>G\<^sub>L (x::'a), A *\<^sub>G\<^sub>L y\<rangle> = \<langle>x, y\<rangle>}"
    by (simp add: GL_eval.abs_eq zero_GL.abs_eq zero_GL.rsp)    
qed

setup_lifting type_definition_U

lift_definition UtimesOp::\<open>'a::complex_inner U \<Rightarrow> 'a U \<Rightarrow> 'a U\<close>
is \<open>\<lambda> f g. f \<circ>\<^sub>G\<^sub>L g\<close>
  by (simp add: GL_eval.rep_eq GLtimesOp.rep_eq times_applyOp)

lift_definition U_eval::\<open>'a::complex_inner U \<Rightarrow> 'a \<Rightarrow> 'a\<close>
is \<open>\<lambda> A v. A *\<^sub>G\<^sub>L v\<close>.

bundle U_notation begin
notation UtimesOp (infixl "\<circ>\<^sub>U" 69)
notation U_eval (infixl "*\<^sub>U" 69)
end

bundle no_U_notation begin
no_notation GLtimesOp (infixl "\<circ>\<^sub>U" 69)
no_notation GL_eval (infixl "*\<^sub>U" 69)
end

unbundle U_notation

instantiation U :: (complex_inner) group_add
begin

lift_definition zero_U:: \<open>'a U\<close> is 0
  apply transfer
  apply transfer
  by auto

lift_definition uminus_U:: \<open>'a U \<Rightarrow> 'a U\<close> is 
\<open>\<lambda> A. - A\<close>
  apply transfer
  by (metis (no_types, lifting) inverse_bounded_right times_applyOp times_idOp1)
  
lift_definition plus_U:: \<open>'a U \<Rightarrow> 'a U \<Rightarrow> 'a U\<close> is 
"(+)"
proof-
  fix     GL1 :: "'a GL"
    and GL2 :: "'a GL"
    and a1 :: 'a
    and a2 :: 'a
  assume \<open>\<And>x y. \<langle>GL1 *\<^sub>G\<^sub>L (x::'a), GL1 *\<^sub>G\<^sub>L y\<rangle> = \<langle>x, y\<rangle>\<close>
    and \<open>\<And>x y. \<langle>GL2 *\<^sub>G\<^sub>L (x::'a), GL2 *\<^sub>G\<^sub>L y\<rangle> = \<langle>x, y\<rangle>\<close>
  have \<open>\<langle>(GL1 + GL2) *\<^sub>G\<^sub>L a1, (GL1 + GL2) *\<^sub>G\<^sub>L a2\<rangle> = 
        \<langle>GL1 *\<^sub>G\<^sub>L (GL2 *\<^sub>G\<^sub>L a1), GL1 *\<^sub>G\<^sub>L (GL2 *\<^sub>G\<^sub>L a2)\<rangle>\<close>
  proof-
    have \<open>(GL1 + GL2) *\<^sub>G\<^sub>L a1 = GL1 *\<^sub>G\<^sub>L (GL2 *\<^sub>G\<^sub>L a1)\<close>
      apply transfer
      by (simp add: times_applyOp)
    moreover have \<open>(GL1 + GL2) *\<^sub>G\<^sub>L a2 = GL1 *\<^sub>G\<^sub>L (GL2 *\<^sub>G\<^sub>L a2)\<close>
      apply transfer
      by (simp add: times_applyOp)
    ultimately show ?thesis by simp
  qed
  also have \<open>\<langle>GL1 *\<^sub>G\<^sub>L (GL2 *\<^sub>G\<^sub>L a1), GL1 *\<^sub>G\<^sub>L (GL2 *\<^sub>G\<^sub>L a2)\<rangle> = \<langle>GL2 *\<^sub>G\<^sub>L a1, GL2 *\<^sub>G\<^sub>L a2\<rangle>\<close>
    by (simp add: \<open>\<And>y x. \<langle>GL1 *\<^sub>G\<^sub>L x, GL1 *\<^sub>G\<^sub>L y\<rangle> = \<langle>x, y\<rangle>\<close>)
  also have \<open>\<langle>GL2 *\<^sub>G\<^sub>L a1, GL2 *\<^sub>G\<^sub>L a2\<rangle> = \<langle>a1, a2\<rangle>\<close>
    by (simp add: \<open>\<And>y x. \<langle>GL2 *\<^sub>G\<^sub>L x, GL2 *\<^sub>G\<^sub>L y\<rangle> = \<langle>x, y\<rangle>\<close>)
  finally show \<open>\<langle>(GL1 + GL2) *\<^sub>G\<^sub>L a1, (GL1 + GL2) *\<^sub>G\<^sub>L a2\<rangle> = \<langle>a1, a2\<rangle>\<close>
    by simp
qed

definition minus_U:: \<open>'a U \<Rightarrow> 'a U \<Rightarrow> 'a U\<close> where
"minus_U A B = A + (- B)"

instance
  proof
  show "(a::'a U) + b + c = a + (b + c)"
    for a :: "'a U"
      and b :: "'a U"
      and c :: "'a U"
    using Rep_U_inject add.assoc plus_U.rep_eq by fastforce
    
  show "(0::'a U) + a = a"
    for a :: "'a U"
    using Rep_U_inject plus_U.rep_eq zero_U.rep_eq by fastforce
    
  show "(a::'a U) + 0 = a"
    for a :: "'a U"
    using Rep_U_inject plus_U.rep_eq zero_U.rep_eq by fastforce
    
  show "- (a::'a U) + a = 0"
    for a :: "'a U"
    by (simp add: plus_U_def uminus_U.rep_eq zero_U_def)
    
  show "(a::'a U) + - b = a - b"
    for a :: "'a U"
      and b :: "'a U"
    by (simp add: minus_U_def)
    
qed
end


unbundle no_U_notation
unbundle no_GL_notation
unbundle no_bounded_notation

end






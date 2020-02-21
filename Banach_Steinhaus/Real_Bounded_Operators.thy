(*
  File:   Real_Bounded_Operators.thy
  Author: Dominique Unruh, University of Tartu
  Author: Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Real bounded operators\<close>

theory Real_Bounded_Operators
  imports 
    "HOL-Analysis.Operator_Norm"

begin

typedef (overloaded) ('a::real_normed_vector, 'b::real_normed_vector) real_bounded
  = \<open>{f::'a \<Rightarrow> 'b. bounded_linear f}\<close>
  morphisms times_real_bounded_vec Abs_real_bounded
  using bounded_linear_zero by blast

notation times_real_bounded_vec (infixr "*\<^sub>v" 70)

setup_lifting type_definition_real_bounded

instantiation  real_bounded :: (real_normed_vector, real_normed_vector) real_normed_vector
begin
lift_definition uminus_real_bounded ::
  "('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded "  is \<open>\<lambda> f. \<lambda> x. - f x\<close>
  by (simp add: bounded_linear_minus)

lift_definition zero_real_bounded ::
  "('a, 'b) real_bounded"  is \<open>\<lambda> x. 0\<close>
  by simp

lift_definition plus_real_bounded ::
  "('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded "  
  is \<open>\<lambda> f. \<lambda> g. \<lambda> x. f x + g x\<close>
  by (simp add: bounded_linear_add)

lift_definition minus_real_bounded ::
  "('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded "  
  is \<open>\<lambda> f. \<lambda> g. \<lambda> x. f x - g x\<close>
  by (simp add: bounded_linear_sub)

lift_definition norm_real_bounded :: \<open>('a, 'b) real_bounded \<Rightarrow> real\<close>
  is \<open>onorm\<close>.

lift_definition dist_real_bounded :: \<open>('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. onorm (\<lambda> x. f x - g x )\<close>.

lift_definition scaleR_real_bounded :: \<open>real \<Rightarrow> ('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded\<close>
  is \<open>\<lambda> r. \<lambda> f. \<lambda> x. r *\<^sub>R f x\<close>
  by (simp add: bounded_linear_const_scaleR)

lift_definition sgn_real_bounded :: \<open>('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded\<close>
  is \<open>\<lambda> f. (\<lambda> x. (f x) /\<^sub>R (onorm f) )\<close>
  by (simp add: bounded_linear_const_scaleR)

definition uniformity_real_bounded :: \<open>( ('a, 'b) real_bounded \<times> ('a, 'b) real_bounded ) filter\<close>
  where  \<open>uniformity_real_bounded = (INF e:{0<..}. principal {((f::('a, 'b) real_bounded), g). 
          dist f g < e})\<close>

definition open_real_bounded :: \<open>(('a, 'b) real_bounded) set \<Rightarrow> bool\<close>
  where \<open>open_real_bounded = (\<lambda> U::(('a, 'b) real_bounded) set. 
  \<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)\<close>

instance
proof
  show "dist (x::('a, 'b) real_bounded) y = norm (x - y)"
    for x :: "('a, 'b) real_bounded"
      and y :: "('a, 'b) real_bounded"
    apply transfer by simp 
  show "a + b + c = a + (b + c)"
    for a :: "('a, 'b) real_bounded"
      and b :: "('a, 'b) real_bounded"
      and c :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "a + b = b + a"
    for a :: "('a, 'b) real_bounded"
      and b :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "(0::('a, 'b) real_bounded) + a = a"
    for a :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "- a + a = 0"
    for a :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "a - b = a + - b"
    for a :: "('a, 'b) real_bounded"
      and b :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real
      and x :: "('a, 'b) real_bounded"
      and y :: "('a, 'b) real_bounded"
    apply transfer by (simp add: scaleR_add_right) 
  show "(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "('a, 'b) real_bounded"
    apply transfer by (simp add: scaleR_left.add)
  show "a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "('a, 'b) real_bounded"
    apply transfer by simp 
  show "1 *\<^sub>R x = x"
    for x :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "sgn x = inverse (norm x) *\<^sub>R x"
    for x :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a, 'b) real_bounded) y < e})"
    by (simp add: uniformity_real_bounded_def)    
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
    for U :: "('a, 'b) real_bounded set"
    by (simp add: open_real_bounded_def)    
  show "(norm x = 0) = (x = 0)"
    for x :: "('a, 'b) real_bounded"
    apply transfer using onorm_eq_0 by blast 
  show "norm (x + y) \<le> norm x + norm y"
    for x :: "('a, 'b) real_bounded"
      and y :: "('a, 'b) real_bounded"
    apply transfer by (simp add: onorm_triangle) 
  show "norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x"
    for a :: real
      and x :: "('a, 'b) real_bounded"
    apply transfer by (simp add: onorm_scaleR) 
qed

end


end
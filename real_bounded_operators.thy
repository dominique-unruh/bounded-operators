(*  Title:      bounded-Operators/real_bounded_operators.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

Operators between real vector spaces.

References:             

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}


*)

theory real_bounded_operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    Operator_Norm_Plus
begin

section \<open>Linear operators\<close>
(* The operators may be unbounded *)

typedef (overloaded) ('a::real_vector, 'b::real_vector) real_operator
= \<open>{ f::'a\<Rightarrow>'b. linear f}\<close>
  using linear_zero by blast

setup_lifting type_definition_real_operator

lift_definition bounded_real_operator :: \<open>('a::real_normed_vector, 'b::real_normed_vector) real_operator \<Rightarrow> bool\<close> 
is \<open>\<lambda> f. bounded_linear_axioms f\<close>.

lift_definition ev_real_operator :: \<open>('a::real_vector, 'b::real_vector) real_operator \<Rightarrow> 'a \<Rightarrow> 'b\<close> 
is \<open>\<lambda> f. \<lambda> x. f x\<close>.

instantiation real_operator :: (real_vector, real_vector) \<open>real_vector\<close>
begin
lift_definition uminus_real_operator :: \<open>('a, 'b) real_operator \<Rightarrow> ('a, 'b) real_operator\<close>
is \<open>\<lambda> f. ( \<lambda> x. -f x)\<close>
  by (rule Real_Vector_Spaces.real_vector.linear_compose_neg)
lift_definition zero_real_operator :: \<open>('a, 'b) real_operator\<close> is \<open>\<lambda> _::'a. 0::'b\<close>
  by (rule Real_Vector_Spaces.real_vector.linear_zero)
lift_definition minus_real_operator :: \<open>('a, 'b) real_operator \<Rightarrow> ('a, 'b) real_operator \<Rightarrow> ('a, 'b) real_operator\<close>
is \<open>\<lambda> f. \<lambda> g. ( \<lambda> x. f x - g x)\<close>
  by (rule Real_Vector_Spaces.real_vector.module_hom_sub)
lift_definition plus_real_operator :: \<open>('a, 'b) real_operator \<Rightarrow> ('a, 'b) real_operator \<Rightarrow> ('a, 'b) real_operator\<close>
is \<open>\<lambda> f. \<lambda> g. ( \<lambda> x. f x + g x)\<close>
  by (rule Real_Vector_Spaces.real_vector.linear_compose_add)
lift_definition scaleR_real_operator :: \<open>real \<Rightarrow> ('a, 'b) real_operator \<Rightarrow> ('a, 'b) real_operator\<close>
is \<open>\<lambda> c. \<lambda> f. (\<lambda> x. c *\<^sub>R (f x))\<close>
  by (rule Real_Vector_Spaces.real_vector.linear_compose_scale_right)

instance
  apply intro_classes
  apply transfer
  apply auto
  apply transfer
  apply auto
  apply transfer
  apply auto
  apply transfer
  apply auto
  apply transfer
  apply auto
  apply transfer
  apply (simp add: scaleR_add_right)
  apply transfer
  apply (simp add: scaleR_add_left)
  apply transfer
  apply simp
  apply transfer
  apply auto
  done
end


section \<open>Bounded linear operators\<close>

typedef (overloaded) ('a::real_normed_vector, 'b::real_normed_vector) real_bounded
= \<open>{ f::('a, 'b) real_operator. bounded_real_operator f}\<close>
  apply transfer
  using bounded_linear.axioms(2) bounded_linear_zero module_hom_zero by blast

setup_lifting type_definition_real_bounded

lift_definition ev_real_bounded :: \<open>('a::real_normed_vector, 'b::real_normed_vector) real_bounded \<Rightarrow> 'a \<Rightarrow> 'b\<close> 
is \<open>\<lambda> f. \<lambda> x. ev_real_operator f x\<close>.

instantiation real_bounded :: (real_normed_vector, real_normed_vector) \<open>real_vector\<close>
begin
  
lift_definition uminus_real_bounded :: \<open>('a::real_normed_vector, 'b::real_normed_vector) real_bounded \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded\<close>
is \<open>\<lambda> f. -f\<close>
  apply transfer
  using bounded_linear_minus bounded_linear.axioms(2) bounded_linear.intro by auto

lift_definition zero_real_boudned :: \<open>('a::real_normed_vector, 'b::real_normed_vector) real_bounded\<close>
 is \<open>0\<close>
  apply transfer
  by (simp add: bounded_linear.axioms(2))

lift_definition minus_real_bounded :: \<open>('a::real_normed_vector, 'b::real_normed_vector) real_bounded \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded\<close>
is \<open>\<lambda> f. \<lambda> g. f - g\<close>
  apply transfer
  using bounded_linear_sub bounded_linear_def by blast

lift_definition plus_real_bounded :: \<open>('a::real_normed_vector, 'b::real_normed_vector) real_bounded \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded\<close>
is \<open>\<lambda> f g.  f + g\<close>
  apply transfer
  using bounded_linear_add bounded_linear_def by blast

lift_definition scaleR_real_bounded :: \<open>real \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded\<close>
is \<open>\<lambda> c. \<lambda> f. c *\<^sub>R f\<close>
  apply transfer
  using bounded_linear_const_scaleR bounded_linear_def by blast

instance
  apply intro_classes
  apply transfer
  apply auto
  apply transfer
  apply auto
  apply transfer
  sorry    

end


end
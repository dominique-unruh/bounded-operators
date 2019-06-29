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
lift_definition zero_real_operator :: \<open>('a, 'b) real_operator\<close> is \<open>\<lambda> _. 0\<close>
  by (rule Real_Vector_Spaces.real_vector.linear_zero)

instance..

end

section \<open>Bounded linear operators\<close>

typedef (overloaded) ('a::real_normed_vector, 'b::real_normed_vector) real_bounded
= \<open>{ f::('a, 'b) real_operator. bounded_real_operator f}\<close>
  apply transfer
  using bounded_linear.axioms(2) bounded_linear_zero module_hom_zero by blast

setup_lifting type_definition_real_bounded

lift_definition ev_real_bounded :: \<open>('a::real_normed_vector, 'b::real_normed_vector) real_bounded \<Rightarrow> 'a \<Rightarrow> 'b\<close> 
is \<open>\<lambda> f. \<lambda> x. ev_real_operator f x\<close>.

instantiation real_bounded :: (real_normed_vector, real_normed_vector) \<open>zero\<close>
begin
lift_definition zero_real_bounded :: \<open>('a, 'b) real_bounded\<close> is \<open>0::('a,'b) real_operator\<close>
  apply transfer
  by (simp add: bounded_linear.axioms(2))
instance..
end



end
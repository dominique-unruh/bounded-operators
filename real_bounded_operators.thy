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

typedef (overloaded) ('a::real_normed_vector, 'b::real_normed_vector) real_bounded
= \<open>{ f::'a\<Rightarrow>'b. bounded_linear f}\<close>
  using bounded_linear_zero by blast

setup_lifting type_definition_real_bounded


instantiation real_bounded :: (real_normed_vector, real_normed_vector) \<open>zero\<close>
begin
lift_definition zero_real_bounded :: \<open>('a, 'b) real_bounded\<close> is \<open>\<lambda> _::'a. 0::'b\<close>
  by (rule bounded_linear_zero)
instance..
end



end
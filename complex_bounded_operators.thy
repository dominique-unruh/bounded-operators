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

theory complex_bounded_operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    real_bounded_operators
    Complex_Vector_Spaces
begin


typedef (overloaded) ('a::complex_normed_vector, 'b::complex_normed_vector) complex_bounded
= \<open>{f :: ('a, 'b) real_bounded. \<forall> c. \<forall> x. (Rep_real_bounded f) (c *\<^sub>C x) = c *\<^sub>C ((Rep_real_bounded f) x) }\<close>
  apply transfer
  using zero_real_bounded_def 
  apply auto
  using bounded_linear_zero by fastforce

end
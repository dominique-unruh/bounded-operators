(*  Title:      bounded-Operators/finite_dimensional_case.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

Finite rank operators.

References:             

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}


*)

theory finite_rank_operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    complex_bounded_operators

begin

fun complex_gen ::\<open>nat \<Rightarrow> ('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> bool\<close> where
\<open>complex_gen 0 f = (\<forall> x. f x = 0)\<close> |
\<open>complex_gen (Suc n) f =  (\<exists> g. complex_gen n g \<and>
  ( \<exists> t. \<forall> x. \<exists> c. f x = c *\<^sub>C t + g x ) )\<close> 

definition finite_complex_rank ::\<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> bool\<close> where
 \<open>finite_complex_rank f = (\<exists> n. complex_gen n f)\<close> 

definition complex_rank ::\<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> ereal\<close> where
 \<open>complex_rank f = Inf { n |n. complex_gen n f}\<close> 


lemma finite_rank_and_linear:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes \<open>clinear f\<close> and \<open>finite_complex_rank f\<close>
  shows \<open>bounded_clinear f\<close>
  sorry



end
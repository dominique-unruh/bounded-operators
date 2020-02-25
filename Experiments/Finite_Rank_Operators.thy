section \<open>TODO: section title\<close>

(*  Title:      bounded-Operators/finite_rank_operators.thy
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

theory Finite_Rank_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    Bounded_Operators
    Complex_L2
begin

fun complex_gen ::\<open>nat \<Rightarrow> ('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> bool\<close> where
  \<open>complex_gen 0 f = (\<forall> x. f x = 0)\<close> |
  \<open>complex_gen (Suc n) f =  (\<exists> g. complex_gen n g \<and>
  ( \<exists> t. \<forall> x. \<exists> c. f x = c *\<^sub>C t + g x ) )\<close> 

definition finite_complex_rank :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> bool\<close> where
  \<open>finite_complex_rank f = (\<exists> n. complex_gen n f)\<close> 

definition complex_rank :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> ereal\<close> where
  \<open>complex_rank f = Inf { n |n. complex_gen n f}\<close> 

(* There are unbounded operators whose rank is fintie,
but we use the name "finite rank operators" just for bounded
operators. Reference:

https://math.stackexchange.com/questions/1492097/unbounded-operator-of-finite-rank
 *)

definition finite_rank_operator :: \<open>('a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector) \<Rightarrow> bool\<close> where
  \<open>finite_rank_operator f = (finite_complex_rank f \<and> bounded_clinear f)\<close> 

end

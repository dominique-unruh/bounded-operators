section \<open>TODO: section title\<close>

theory ToDo
  imports Bounded_Operators Complex_L2 
begin

text \<open>
How to use this file:

Dominique adds lemmas and definitions here that are needed by QRHL.

José can do one of the following things:
* Move them to the right theory file (and prove them)
* If they already exist (or very similar ones from which they follow trivially), add a comment here and do not edit them
* If they should be changed (the name or the formulation of the statement), add a comment here and discuss with Dominique

This way, QRHL will not be broken by the work on these lemmas/definitions
\<close>


lemma one_dim_to_complex_scaleC[simp]: "one_dim_to_complex (c *\<^sub>C \<psi>) = c *\<^sub>C one_dim_to_complex \<psi>"
  (* apply transfer by simp *) 
  by (cheat one_dim_to_complex_scaleC)

lemma one_dim_to_complex_times[simp]: "one_dim_to_complex (\<psi> * \<phi>) = one_dim_to_complex \<psi> * one_dim_to_complex \<phi>"
  (* apply transfer by simp *) 
  by (cheat one_dim_to_complex_times)







unbundle bounded_notation





unbundle no_bounded_notation

end


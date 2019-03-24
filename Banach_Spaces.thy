(*  Title:      Bounded-Operators/Banach_Spaces.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu


*)


theory Banach_Spaces
  imports Complex_Main "HOL-Library.Adhoc_Overloading" "HOL-Analysis.Infinite_Set_Sum" 
 Complex_Vector_Spaces
 "HOL-Analysis.Inner_Product" "HOL-Library.LaTeXsugar"

begin
                                             
class cbanach_space = complex_vector + complete_space +
  fixes norm :: "'a \<Rightarrow> real"  ("\<parallel>/_/\<parallel>") 
  assumes 
triangular: \<open>\<parallel> x + y \<parallel> \<le> \<parallel> x \<parallel> + \<parallel> y \<parallel>\<close> and
scalar: \<open>\<parallel> c *\<^sub>C x \<parallel> = (cmod c) * \<parallel> x \<parallel>\<close> and
dist_norm: \<open>dist x y = \<parallel> x - y \<parallel>\<close> 
begin

lemma norm_zero: \<open>\<parallel>x\<parallel> = 0 \<longleftrightarrow> x = 0\<close>
  by (metis (mono_tags, hide_lams)  local.diff_zero local.dist_eq_0_iff local.dist_norm local.eq_iff_diff_eq_0)

end



end
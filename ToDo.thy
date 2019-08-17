theory ToDo
imports Bounded_Operators Complex_L2 Tensor_Product
begin

instantiation linear_space :: (chilbert_space) comm_monoid_add begin
lemma zero_linear_space_def[simp]: "(0 :: 'a linear_space) = bot"
  by (rule linear_space_zero_bot)
(* TODO: replace the above lemma by the following definition, after removing existing instantiation of linear_space::zero *)
(* definition zero_linear_space :: "'a linear_space" where [simp]: "zero_linear_space = bot" *)
definition plus_linear_space :: "'a linear_space \<Rightarrow> _ \<Rightarrow> _" where [simp]: "plus_linear_space = sup"
instance 
  apply standard 
    apply (simp add: sup_assoc)
   apply (simp add: sup_commute)
  by simp
end

lemma ortho_bot[simp]: "- bot = (top::_ subspace)"
  apply transfer by auto
lemma ortho_top[simp]: "- top = (bot::_ subspace)"
  apply transfer by auto

lemma demorgan_inf: "- ((A::_::orthocomplemented_lattice) \<sqinter> B) = - A \<squnion> - B"
  by (cheat demorgan_inf) 

lemma demorgan_sup: "- ((A::_::orthocomplemented_lattice) \<squnion> B) = - A \<sqinter> - B"
  by (cheat demorgan_sup) 

end

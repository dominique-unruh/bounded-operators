
(* TODO (Jose): delete
text \<open>Orthogonal basis\<close>
definition is_ob :: "'a::complex_inner set \<Rightarrow> bool" 
  where "is_ob S  = (
  is_ortho_set S \<and> 
  (complex_vector.independent S) \<and> closure (complex_vector.span S) = UNIV
)"
*)

(* TODO (Jose): Delete
text \<open>Orthonormal basis\<close>
definition is_onb :: "'a::complex_inner set \<Rightarrow> bool" 
  where "is_onb S  = (
  is_ob S \<and> S \<subseteq> sphere 0 1
)"
*)

(* TODO (Jose): delete (better to work with two property independently)
definition is_basis :: "'a::complex_normed_vector set \<Rightarrow> bool" 
  where \<open>is_basis S = (
  (complex_independent S) \<and> closure (complex_vector.span S) = UNIV
)\<close>
*)

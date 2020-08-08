section \<open>\<open>Bounded_Operators_Code\<close> -- Support for code generation\<close>

theory Bounded_Operators_Code
  imports
    Bounded_Operators_Matrices 
begin


unbundle jnf_notation
unbundle cblinfun_notation

subsection \<open>Code equations for cblinfun operators\<close>

text \<open>In this subsection, we define the code for all operations involving only 
  operators (no combinations of operators/vectors/subspaces)\<close>

text \<open>This lemma defines addition. By writing \<^term>\<open>mat_of_cblinfun (M + N)\<close>
on the left hand side, we get access to the\<close>
lemma cblinfun_of_mat_plusOp[code]:
  "mat_of_cblinfun (F + G) = mat_of_cblinfun F + mat_of_cblinfun G"
  for F G::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum"
  using cblinfun_of_mat_plusOp'.

lemma cblinfun_of_mat_id[code]:
  "mat_of_cblinfun (idOp :: ('a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L'a)) = 1\<^sub>m (canonical_basis_length TYPE('a))"
  using cblinfun_of_mat_id'.

lemma mat_of_cblinfun_zero[code]:
  "mat_of_cblinfun (0 :: ('a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)) 
  = 0\<^sub>m (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))"
  using mat_of_cblinfun_zero'.

lemma cblinfun_of_mat_uminusOp[code]:
  "mat_of_cblinfun (- M) = - mat_of_cblinfun M" 
  for M::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum"
  using cblinfun_of_mat_uminusOp'.

lemma cblinfun_of_mat_minusOp[code]:
  "mat_of_cblinfun (M - N) = mat_of_cblinfun M - mat_of_cblinfun N" 
  for M::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum" and N::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b"
  using cblinfun_of_mat_minusOp'.


text \<open>This instantiation defines a code equation for equality tests for cblinfun operators.\<close>
instantiation cblinfun :: (onb_enum,onb_enum) equal begin
definition [code]: "equal_cblinfun M N \<longleftrightarrow> mat_of_cblinfun M = mat_of_cblinfun N" 
  for M N :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
instance 
  apply intro_classes
  unfolding equal_cblinfun_def 
  using mat_of_cblinfun_inj injD by fastforce
end


declare mat_of_cblinfun_classical_operator_inj_option[code]


subsection \<open>Miscellanea\<close>

text \<open>This is a hack to circumvent a bug in the code generation. The automatically
  generated code for the class \<^class>\<open>uniformity\<close> has a type that is different from
  what the generated code later assumes, leading to compilation errors (in ML at least)
  in any expression involving \<^typ>\<open>_ ell2\<close> (even if the constant \<^const>\<open>uniformity\<close> is
  not actually used).
  
  The fragment below circumvents this by forcing Isabelle to use the right type.
  (The logically useless fragment "\<open>let x = ((=)::'a\<Rightarrow>_\<Rightarrow>_)\<close>" achieves this.)\<close>
lemma [code]: "(uniformity :: ('a ell2 * _) filter) = Filter.abstract_filter (%_.
    Code.abort STR ''no uniformity'' (%_. 
    let x = ((=)::'a\<Rightarrow>_\<Rightarrow>_) in uniformity))"
  by simp

unbundle no_jnf_notation
unbundle no_cblinfun_notation

end

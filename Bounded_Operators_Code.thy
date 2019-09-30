theory Bounded_Operators_Code
  imports Bounded_Operators ToDo
    Jordan_Normal_Form_Notation
begin

unbundle jnf_notation
unbundle bounded_notation

section \<open>Setting up code generation for type bounded\<close>

text \<open>We define the canonical isomorphism between \<^typ>\<open>('a::basis_enum,'b::basis_enum) bounded\<close>
  and the complex \<^term>\<open>n*m\<close>-matrices (where n,m are the dimensions of 'a,'b, 
  respectively). This is possible if \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close> are of class \<^class>\<open>basis_enum\<close>
  since that class fixes a finite canonical basis. Matrices are represented using
  the \<^typ>\<open>_ mat\<close> type from \<^session>\<open>Jordan_Normal_Form\<close>.\<close>
(* TODO: Define (canonical isomorphism). *)


(* bad definition: No type arity Matrix.vec :: comm_monoid_add
The reason of the error is the fact that the zero in vec depends on the dimension.

definition vec_of_basis_enum :: \<open>'a::basis_enum \<Rightarrow> complex vec\<close> where
\<open>vec_of_basis_enum v = (\<Sum>i::nat|i<length canonical_basis. 
(\<langle>canonical_basis ! i, v\<rangle> \<cdot>\<^sub>v unit_vec (length canonical_basis) i)
)\<close>
*)

primrec vec_of_basis_enum_list :: \<open>'a list \<Rightarrow> 'a::basis_enum \<Rightarrow> complex vec\<close> where
\<open>vec_of_basis_enum_list [] v = 0\<^sub>v (length (canonical_basis::'a list))\<close> | 
\<open>vec_of_basis_enum_list (x#ys) v = vec_of_basis_enum_list (ys) v + 
\<langle>x, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length ys)\<close>

definition vec_of_basis_enum :: \<open>'a::basis_enum \<Rightarrow> complex vec\<close> where
\<open>vec_of_basis_enum v = vec_of_basis_enum_list canonical_basis v\<close> 

definition basis_enum_of_vec :: \<open>complex vec \<Rightarrow> 'a::basis_enum\<close> where
\<open>basis_enum_of_vec v = sum (\<lambda> i. (vec_index v i) *\<^sub>C ((canonical_basis::'a list) ! i)) {..< length (canonical_basis::'a list)}\<close>

lemma basis_enum_of_vec_COMP_vec_of_basis_enum:
\<open>basis_enum_of_vec \<circ> vec_of_basis_enum = id\<close>
  sorry

lemma vec_of_basis_enum_COMP_basis_enum_of_vec:
\<open>vec_of_basis_enum \<circ> basis_enum_of_vec = id\<close>
  sorry

definition mat_of_bounded :: \<open>('a::basis_enum,'b::basis_enum) bounded \<Rightarrow> complex mat\<close> where
\<open>mat_of_bounded = undefined\<close>

definition bounded_of_mat :: \<open>complex mat \<Rightarrow> ('a::basis_enum,'b::basis_enum) bounded\<close> where
\<open>bounded_of_mat = undefined\<close>


lemma mat_of_bounded_inj: "inj mat_of_bounded"
  by (cheat 16)

text \<open>The following lemma registers bounded as an abstract datatype with 
  constructor bounded_of_mat.
  That means that in generated code, all bounded operators will be represented
  as "Bounded_of_mat X" where X is a matrix. And code equations below
  can directly refer the matrix that represents an operator O by
  writing \<^term>\<open>bounded_of_mat_plusOp X\<close> (see, e.g.,
  [TODO reference plus-lemma] below).

  See [TODO: bibtex reference to code generation tutorial] for more information on 
  [code abstype].\<close>
lemma mat_of_bounded_inverse [code abstype]:
  "bounded_of_mat (mat_of_bounded B) = B" 
  for B::"('a::basis_enum,'b::basis_enum) bounded"
  by (cheat 15)

section \<open>Code equations for bounded operators\<close>

text \<open>In this section, we define the code for all operations involving only 
  operators (no combinations of operators/vectors/subspaces)\<close>

text \<open>This lemma defines addition. By writing \<^term>\<open>mat_of_bounded (M + N)\<close>
on the left hand side, we get access to the\<close>
lemma bounded_of_mat_plusOp[code]:
  "mat_of_bounded (M + N) =  (mat_of_bounded M + mat_of_bounded N)" 
  for M::"('a::basis_enum,'b::basis_enum) bounded" and N::"('a::basis_enum,'b) bounded"
  by (cheat 15)

lemma bounded_of_mat_id[code]:
  "mat_of_bounded (idOp :: ('a::basis_enum,'a) bounded) = one_mat (canonical_basis_length TYPE('a))"
  by (cheat 15)

lemma bounded_of_mat_timesOp[code]:
  "mat_of_bounded (M *\<^sub>o N) =  (mat_of_bounded M * mat_of_bounded N)" 
  for M::"('b::basis_enum,'c::basis_enum) bounded" and N::"('a::basis_enum,'b) bounded"
  by (cheat 15)

lemma bounded_of_mat_minusOp[code]:
  "mat_of_bounded (M - N) =  (mat_of_bounded M - mat_of_bounded N)" 
  for M::"('a::basis_enum,'b::basis_enum) bounded" and N::"('a::basis_enum,'b) bounded"
  by (cheat 15)

lemma bounded_of_mat_uminusOp[code]:
  "mat_of_bounded (- M) = - mat_of_bounded M" for M::"('a::basis_enum,'b::basis_enum) bounded"
  by (cheat 15)

lemma mat_of_bounded_scalarMult[code]:
  "mat_of_bounded ((a::complex) *\<^sub>C M) = smult_mat a (mat_of_bounded M)" for M :: "('a::basis_enum,'b::basis_enum) bounded"
  by (cheat 16)

text \<open>This instantiation defines a code equation for equality tests for bounded operators.\<close>
instantiation bounded :: (basis_enum,basis_enum) equal begin
definition [code]: "equal_bounded M N \<longleftrightarrow> mat_of_bounded M = mat_of_bounded N" 
  for M N :: "('a,'b) bounded"
instance 
  apply intro_classes
  unfolding equal_bounded_def 
  using mat_of_bounded_inj injD by fastforce
end

(* TODO: check if such a definition already exists in Jordan_Normal_Form *)
definition "adjoint_mat M = transpose_mat (map_mat cnj M)"

lemma bounded_of_mat_adjoint[code]:
  "mat_of_bounded (adjoint A) = adjoint_mat (mat_of_bounded A)"
for A :: "('a::basis_enum,'b::basis_enum) bounded"
  by (cheat 17)

lemma mat_of_bounded_zero[code]:
  "mat_of_bounded (0::('a::basis_enum,'b::basis_enum) bounded)
       = zero_mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))"
  by (cheat 17)

lemma mat_of_bounded_classical_operator[code]: 
  "mat_of_bounded (classical_operator f) = mat (CARD('b)) (CARD('a))
  (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0)" 
  for f::"'a::enum \<Rightarrow> 'b::enum option"
  by (cheat 17)

section \<open>Miscellanea\<close>

text \<open>This is a hack to circumvent a bug in the code generation. The automatically
  generated code for the class \<^class>\<open>uniformity\<close> has a type that is different from
  what the generated code later assumes, leading to compilation errors (in ML at least)
  in any expression involving \<^typ>\<open>_ ell2\<close> (even if the constant \<^const>\<open>uniformity\<close> is
  not actually used).
  
  The fragment below circumvents this by forcing Isabelle to use the right type.
  (The logically useless fragment "let x = ((=)::'a\<Rightarrow>_\<Rightarrow>_)" achieves this.)\<close>
lemma [code]: "(uniformity :: ('a ell2 * _) filter) = Filter.abstract_filter (%_.
    Code.abort STR ''no uniformity'' (%_. 
    let x = ((=)::'a\<Rightarrow>_\<Rightarrow>_) in uniformity))"
  by auto

unbundle no_jnf_notation
unbundle no_bounded_notation

end

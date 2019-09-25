theory Bounded_Operators_Code
  imports Bounded_Operators ToDo
    Jordan_Normal_Form_Notation
begin

(* TODO: Move these directly after those definitions *)
declare norm_ell2_def[code del]
declare cinner_ell2_def[code del]

unbundle jnf_notation
unbundle bounded_notation

section \<open>Setting up code generation for type bounded\<close>

text \<open>We define the canonical isomorphism between \<^typ>\<open>('a::basis_enum,'b::basis_enum) bounded\<close>
  and the complex \<^term>\<open>n*m\<close>-matrices (where n,m are the dimensions of 'a,'b, 
  respectively). This is possible if \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close> are of class \<^class>\<open>basis_enum\<close>
  since that class fixes a finite canonical basis. Matrices are represented using
  the \<^typ>\<open>_ mat\<close> type from \<^session>\<open>Jordan_Normal_Form\<close>.\<close>
(* TODO: Define (canonical isomorphism). *)
(* TODO: Rename l2bounded_of_mat \<rightarrow> bounded_of_mat *)
(* TODO: Rename mat_of_l2bounded \<rightarrow> mat_of_bounded *)
consts l2bounded_of_mat :: "complex mat \<Rightarrow> ('a::basis_enum,'b::basis_enum) bounded"
       mat_of_l2bounded :: "('a::basis_enum,'b::basis_enum) bounded \<Rightarrow> complex mat"

lemma mat_of_l2bounded_inj: "inj mat_of_l2bounded"
  by (cheat 16)

text \<open>The following lemma registers bounded as an abstract datatype with 
  constructor l2bounded_of_mat.
  That means that in generated code, all bounded operators will be represented
  as "Bounded_of_mat X" where X is a matrix. And code equations below
  can directly refer the matrix that represents an operator O by
  writing \<^term>\<open>l2bounded_of_mat_plusOp X\<close> (see, e.g.,
  [TODO reference plus-lemma] below).

  See [TODO: bibtex reference to code generation tutorial] for more information on 
  [code abstype].\<close>
lemma mat_of_l2bounded_inverse [code abstype]:
  "l2bounded_of_mat (mat_of_l2bounded B) = B" 
  for B::"('a::basis_enum,'b::basis_enum) bounded"
  by (cheat 15)

section \<open>Code equations for bounded operators\<close>

text \<open>In this section, we define the code for all operations involving only 
  operators (no combinations of operators/vectors/subspaces)\<close>

text \<open>This lemma defines addition. By writing \<^term>\<open>mat_of_l2bounded (M + N)\<close>
on the left hand side, we get access to the\<close>
lemma l2bounded_of_mat_plusOp[code]:
  "mat_of_l2bounded (M + N) =  (mat_of_l2bounded M + mat_of_l2bounded N)" 
  for M::"('a::basis_enum,'b::basis_enum) bounded" and N::"('a::basis_enum,'b) bounded"
  by (cheat 15)

lemma l2bounded_of_mat_id[code]:
  "mat_of_l2bounded (idOp :: ('a::basis_enum,'a) bounded) = one_mat (canonical_basis_length TYPE('a))"
  by (cheat 15)

lemma l2bounded_of_mat_timesOp[code]:
  "mat_of_l2bounded (M *\<^sub>o N) =  (mat_of_l2bounded M * mat_of_l2bounded N)" 
  for M::"('b::basis_enum,'c::basis_enum) bounded" and N::"('a::basis_enum,'b) bounded"
  by (cheat 15)

lemma l2bounded_of_mat_minusOp[code]:
  "mat_of_l2bounded (M - N) =  (mat_of_l2bounded M - mat_of_l2bounded N)" 
  for M::"('a::basis_enum,'b::basis_enum) bounded" and N::"('a::basis_enum,'b) bounded"
  by (cheat 15)

lemma l2bounded_of_mat_uminusOp[code]:
  "mat_of_l2bounded (- M) = - mat_of_l2bounded M" for M::"('a::basis_enum,'b::basis_enum) bounded"
  by (cheat 15)

lemma mat_of_l2bounded_scalarMult[code]:
  "mat_of_l2bounded ((a::complex) *\<^sub>C M) = smult_mat a (mat_of_l2bounded M)" for M :: "('a::basis_enum,'b::basis_enum) bounded"
  by (cheat 16)

text \<open>This instantiation defines a code equation for equality tests for bounded operators.\<close>
instantiation bounded :: (basis_enum,basis_enum) equal begin
definition [code]: "equal_bounded M N \<longleftrightarrow> mat_of_l2bounded M = mat_of_l2bounded N" 
  for M N :: "('a,'b) bounded"
instance 
  apply intro_classes
  unfolding equal_bounded_def 
  using mat_of_l2bounded_inj injD by fastforce
end

(* TODO: check if such a definition already exists in Jordan_Normal_Form *)
definition "adjoint_mat M = transpose_mat (map_mat cnj M)"

lemma l2bounded_of_mat_adjoint[code]:
  "mat_of_l2bounded (adjoint A) = adjoint_mat (mat_of_l2bounded A)"
for A :: "('a::basis_enum,'b::basis_enum) bounded"
  by (cheat 17)

lemma mat_of_l2bounded_zero[code]:
  "mat_of_l2bounded (0::('a::basis_enum,'b::basis_enum) bounded)
       = zero_mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))"
  by (cheat 17)

lemma mat_of_l2bounded_classical_operator[code]: 
  "mat_of_l2bounded (classical_operator f) = mat (CARD('b)) (CARD('a))
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

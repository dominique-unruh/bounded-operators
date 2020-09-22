section \<open>\<open>Bounded_Operators_Code\<close> -- Support for code generation\<close>

theory Bounded_Operators_Code
  imports
    Bounded_Operators_Matrices Containers.Set_Impl Jordan_Normal_Form.Matrix_Kernel
begin

no_notation "Lattice.meet" (infixl "\<sqinter>\<index>" 70)
no_notation "Lattice.join" (infixl "\<squnion>\<index>" 65)
hide_const (open) Coset.kernel
hide_const (open) Matrix_Kernel.kernel
hide_const (open) Order.bottom Order.top

unbundle jnf_notation
unbundle cblinfun_notation



subsection \<open>Code equations for cblinfun operators\<close>

text \<open>In this subsection, we define the code for all operations involving only 
  operators (no combinations of operators/vectors/subspaces)\<close>


text \<open>The following lemma registers cblinfun as an abstract datatype with 
  constructor \<^const>\<open>cblinfun_of_mat\<close>.
  That means that in generated code, all cblinfun operators will be represented
  as \<^term>\<open>cblinfun_of_mat X\<close> where X is a matrix.
  In code equations for operations involving operators (e.g., +), we
  can then write the equation directly in terms of matrices
  by writing, e.g., \<^term>\<open>mat_of_cblinfun (A+B)\<close> in the lhs,
  and in the rhs we define the matrix that corresponds to the sum of A,B.
  In the rhs, we can access the matrices corresponding to A,B by
  writing \<^term>\<open>mat_of_cblinfun B\<close>.
  (See, e.g., lemma \<open>cblinfun_of_mat_plusOp\<close> below).

  See [TODO: bibtex reference to code generation tutorial] for more information on 
  @{theory_text \<open>[code abstype]\<close>}.\<close>

declare mat_of_cblinfun_inverse [code abstype]


text \<open>This lemma defines addition. By writing \<^term>\<open>mat_of_cblinfun (M + N)\<close>
on the left hand side, we get access to the\<close>


(* TODO: rename \<rightarrow> cblinfun_of_mat_plus *)
declare cblinfun_of_mat_plusOp'[code]
  \<comment> \<open>Code equation for addition of cblinfuns\<close>

  (* TODO: rename (remove ') *)
declare cblinfun_of_mat_id'[code]
  \<comment> \<open>Code equation for computing the identity operator\<close>

  (* TODO: rename (remove ') *)
declare mat_of_cblinfun_zero'[code]
  \<comment> \<open>Code equation for computing the zero operator\<close>

(* TODO: rename (remove ') *)
declare cblinfun_of_mat_uminusOp'[code]
  \<comment> \<open>Code equation for computing the unary minus on cblinfun's\<close>

  (* TODO: rename (remove ') *)
declare cblinfun_of_mat_minusOp'[code]
  \<comment> \<open>Code equation for computing the difference of cblinfun's\<close>

  (* TODO: rename (remove inj_option) *)
declare mat_of_cblinfun_classical_operator_inj_option[code]
  \<comment> \<open>Code equation for computing the "classical operator"\<close>

declare cblinfun_of_mat_timesOp[code]
  \<comment> \<open>Code equation for computing the composition/product of cblinfun's\<close>

declare mat_of_cblinfun_scalarMult[code]
  \<comment> \<open>Code equation for multiplication with complex scalar\<close>

declare mat_of_cblinfun_scaleR[code]
  \<comment> \<open>Code equation for multiplication with real scalar\<close>

declare cblinfun_of_mat_adjoint[code]
  \<comment> \<open>Code equation for computing the adjoint\<close>

text \<open>This instantiation defines a code equation for equality tests for cblinfun.\<close>
instantiation cblinfun :: (onb_enum,onb_enum) equal begin
definition [code]: "equal_cblinfun M N \<longleftrightarrow> mat_of_cblinfun M = mat_of_cblinfun N" 
  for M N :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
instance 
  apply intro_classes
  unfolding equal_cblinfun_def 
  using mat_of_cblinfun_inj injD by fastforce
end

subsection \<open>Vectors\<close>


text \<open>In this section, we define code for operations on vectors. As with operators above,
  we do this by using an isomorphism between finite vectors
  (i.e., types T of sort \<open>complex_vector\<close>) and the type \<^typ>\<open>complex vec\<close> from
  \<^session>\<open>Jordan_Normal_Form\<close>. We have developed such an isomorphism in 
  \<^theory>\<open>Bounded_Operators.Bounded_Operators_Matrices\<close> for 
  any type T of sort \<open>onb_enum\<close> (i.e., any type with a finite canonical orthonormal basis)
  as was done above for bounded operators.
  Unfortunately, we cannot declare code equations for a type class, 
  code equations must be related to a specific type constructor.
  So we give code definition only for vectors of type \<^typ>\<open>'a ell2\<close> (where \<^typ>\<open>'a\<close>
  must be of sort \<open>enum\<close> to make make sure that \<^typ>\<open>'a ell2\<close> is finite dimensional).
  
  The isomorphism between \<^typ>\<open>'a ell2\<close> is given by the constants \<open>ell2_of_vec\<close>
  and \<open>vec_of_ell2\<close> which are copies of the more general \<^const>\<open>onb_enum_of_vec\<close>
  and \<^const>\<open>vec_of_onb_enum\<close> but with a more restricted type to be usable in our code equations.
\<close>

definition ell2_of_vec :: "complex vec \<Rightarrow> 'a::enum ell2" where "ell2_of_vec = onb_enum_of_vec"
definition vec_of_ell2 :: "'a::enum ell2 \<Rightarrow> complex vec" where "vec_of_ell2 = vec_of_onb_enum"

text \<open>The following theorem registers the isomorphism \<open>ell2_of_vec\<close>/\<open>vec_of_ell2\<close>
  for code generation. From now on,
  code for operations on \<^typ>\<open>_ ell2\<close> can be expressed by declarations such
  as \<^term>\<open>vec_of_ell2 (f a b) = g (vec_of_ell2 a) (vec_of_ell2 b)\<close>
  if the operation f on \<^typ>\<open>_ ell2\<close> corresponds to the operation g on
  \<^typ>\<open>complex vec\<close>.\<close>

lemma vec_of_ell2_inverse [code abstype]:
  "ell2_of_vec (vec_of_ell2 B) = B" 
  unfolding ell2_of_vec_def vec_of_ell2_def
  by (rule onb_enum_of_vec_inverse)

text \<open>This instantiation defines a code equation for equality tests for ell2.\<close>
instantiation ell2 :: (enum) equal begin
definition [code]: "equal_ell2 M N \<longleftrightarrow> vec_of_ell2 M = vec_of_ell2 N" 
  for M N :: "'a::enum ell2"
instance 
  apply intro_classes
  unfolding equal_ell2_def
  by (metis vec_of_ell2_inverse)
end

lemma vec_of_ell2_zero[code]:
  \<comment> \<open>Code equation for computing the zero vector\<close>
  "vec_of_ell2 (0::'a::enum ell2) = zero_vec (canonical_basis_length TYPE('a ell2))"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_zero)

lemma vec_of_ell2_ket[code]:
  \<comment> \<open>Code equation for computing a standard basis vector\<close>
  "vec_of_ell2 (ket i) = unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)" 
  for i::"'a::enum"
  using vec_of_ell2_def vec_of_onb_enum_ket by metis

lemma vec_of_ell2_timesScalarVec[code]: 
  \<comment> \<open>Code equation for multiplying a vector with a complex scalar\<close>
  "vec_of_ell2 (scaleC a \<psi>) = smult_vec a (vec_of_ell2 \<psi>)"
  for \<psi> :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_scaleC)

lemma vec_of_ell2_scaleR[code]: 
  \<comment> \<open>Code equation for multiplying a vector with a real scalar\<close>
  "vec_of_ell2 (scaleR a \<psi>) = smult_vec (complex_of_real a) (vec_of_ell2 \<psi>)"
  for \<psi> :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_scaleR)

lemma ell2_of_vec_plus[code]:
  \<comment> \<open>Code equation for adding vectors\<close>
  "vec_of_ell2 (x + y) =  (vec_of_ell2 x) + (vec_of_ell2 y)" for x y :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_add) 

lemma ell2_of_vec_minus[code]:
  \<comment> \<open>Code equation for subtracting vectors\<close>
  "vec_of_ell2 (x - y) =  (vec_of_ell2 x) - (vec_of_ell2 y)" for x y :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_minus)

lemma ell2_of_vec_uminus[code]:
  \<comment> \<open>Code equation for negating a vector\<close>
  "vec_of_ell2 (- y) =  - (vec_of_ell2 y)" for y :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_uminus)

lemma cinner_ell2_code' [code]: "cinner \<psi> \<phi> = cscalar_prod (vec_of_ell2 \<phi>) (vec_of_ell2 \<psi>)"
  \<comment> \<open>Code equation for the inner product of vectors\<close>
  by (simp add: cinner_ell2_code vec_of_ell2_def)

lemma norm_ell2_code [code]: 
  \<comment> \<open>Code equation for the norm of a vector\<close>
  "norm \<psi> = (let \<psi>' = vec_of_ell2 \<psi> in
    sqrt (\<Sum> i \<in> {0 ..< dim_vec \<psi>'}. let z = vec_index \<psi>' i in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
  by (simp add: norm_ell2_code vec_of_ell2_def)

lemma times_ell2_code'[code]: 
  \<comment> \<open>Code equation for the product in the algebra of one-dimensional vectors\<close>
  fixes \<psi> \<phi> :: "'a::{CARD_1,enum} ell2"
  shows "vec_of_ell2 (\<psi> * \<phi>)
   = vec_of_list [vec_index (vec_of_ell2 \<psi>) 0 * vec_index (vec_of_ell2 \<phi>) 0]"
  using vec_of_ell2_def times_ell2_code by metis

lemma one_ell2_code'[code]: 
  \<comment> \<open>Code equation for the unit in the algebra of one-dimensional vectors\<close>
  "vec_of_ell2 (1 :: 'a::{CARD_1,enum} ell2) = vec_of_list [1]"
  using one_ell2_code vec_of_ell2_def by metis

subsection \<open>Vector/Matrix\<close>

text \<open>We proceed to give code equations for operations involving both
  operators (cblinfun) and vectors. As explained above, we have to restrict
  the equations to vectors of type \<^typ>\<open>'a ell2\<close> even though the theory is available
  for any type of class \<^class>\<open>onb_enum\<close>. As a consequence, we run into an
  addition technicality now. For example, to define a code equation for applying
  an operator to a vector, we might try to give the following lemma:

\<^theory_text>\<open>lemma cblinfun_apply_code[code]:
  "vec_of_ell2 (M *\<^sub>V x) = (mult_mat_vec (mat_of_cblinfun M) (vec_of_ell2 x))"
  by (simp add: mat_of_cblinfun_description vec_of_ell2_def)\<close>

  Unfortunately, this does not work, Isabelle produces the warning 
  "Projection as head in equation", most likely due to the fact that
  the type of \<^term>\<open>(*\<^sub>V)\<close> in the equation is less general than the type of 
  \<^term>\<open>(*\<^sub>V)\<close> (it is restricted to @{type ell2}). We overcome this problem
  by defining a constant \<open>cblinfun_apply_code\<close> which is equal to \<^term>\<open>(*\<^sub>V)\<close>
  but has a more restricted type. We then instruct the code generation 
  to replace occurrences of \<^term>\<open>(*\<^sub>V)\<close> by \<open>cblinfun_apply_code\<close> (where possible),
  and we add code generation for \<open>cblinfun_apply_code\<close> instead of \<^term>\<open>(*\<^sub>V)\<close>.
\<close>


definition cblinfun_apply_code :: "'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2 \<Rightarrow> 'a ell2 \<Rightarrow> 'b ell2" 
  where [code del, code_abbrev]: "cblinfun_apply_code = (*\<^sub>V)"
  \<comment> \<open>@{attribute code_abbrev} instructs the code generation to replace the
     rhs \<^term>\<open>(*\<^sub>V)\<close> by the lhs \<^term>\<open>cblinfun_apply_code\<close> before starting 
     the actual code generation.\<close>

lemma cblinfun_apply_code[code]:
  \<comment> \<open>Code equation for \<^term>\<open>cblinfun_apply_code\<close>, i.e., for applying an operator
     to an \<^type>\<open>ell2\<close> vector\<close>
  "vec_of_ell2 (cblinfun_apply_code M x) = (mult_mat_vec (mat_of_cblinfun M) (vec_of_ell2 x))"
  by (simp add: cblinfun_apply_code_def mat_of_cblinfun_description vec_of_ell2_def)

text \<open>For the constant \<^term>\<open>vector_to_cblinfun\<close> (canonical isomorphism from
  vectors to operators), we have the same problem and define a constant
  \<open>vector_to_cblinfun_code\<close> with more restricted type\<close>

definition vector_to_cblinfun_code :: "'a ell2 \<Rightarrow> 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a ell2" where
  [code del,code_abbrev]: "vector_to_cblinfun_code = vector_to_cblinfun"
  \<comment> \<open>@{attribute code_abbrev} instructs the code generation to replace the
     rhs \<^term>\<open>vector_to_cblinfun\<close> by the lhs \<^term>\<open>vector_to_cblinfun_code\<close>
     before starting the actual code generation.\<close>

lemma vector_to_cblinfun_code[code]: 
  \<comment> \<open>Code equation for translating a vector into an operation (single-column matrix)\<close>
  "mat_of_cblinfun (vector_to_cblinfun_code \<psi>) = mat_of_cols (CARD('a)) [vec_of_ell2 \<psi>]"
  for \<psi>::"'a::enum ell2"
  by (simp add: mat_of_cblinfun_ell2_to_l2bounded canonical_basis_length_ell2_def vec_of_ell2_def vector_to_cblinfun_code_def)

subsection \<open>Subspaces\<close>

text \<open>In this section, we define code equations for handling subspaces, i.e.,
values of type \<^typ>\<open>'a clinear_space\<close>. We choose to computationally represent
a subspace by a list of vectors that span the subspace. That is,
if \<^term>\<open>vecs\<close> are vectors (type \<^typ>\<open>complex vec\<close>), \<open>SPAN vecs\<close> is defined to be their
span. Then the code generation can simply represent all subspaces in this form, and 
we need to define the operations on subspaces in terms of list of vectors 
(e.g., the closed union of two subspaces would be computed as the concatenation 
of the two lists, to give one of the simplest examples).

To support this, \<open>SPAN\<close> is declared as a "\<open>code_datatype\<close>".
(Not as an abstract datatype like \<^term>\<open>cblinfun_of_mat\<close>/\<^term>\<open>mat_of_cblinfun\<close>
because that would require \<open>SPAN\<close> to be injective.)

Then all code equations for different operations need to be formulated as
functions of values of the form \<open>SPAN x\<close>. (E.g., \<open>SPAN x + SPAN y = SPAN (\<dots>)\<close>.)\<close>

definition [code del]: "SPAN x = (let n = canonical_basis_length TYPE('a::onb_enum) in
    Span (onb_enum_of_vec ` Set.filter (\<lambda>v. dim_vec v = n) (set x)) :: 'a clinear_space)"
  \<comment> \<open>The SPAN of vectors x, as a \<^type>\<open>clinear_space\<close>.
      We filter out vectors of the wrong dimension because \<open>SPAN\<close> needs to have
      well-defined behavior even in cases that would not actually occur in an execution.\<close>
code_datatype SPAN

text \<open>We first declare code equations for \<^term>\<open>Proj\<close>, i.e., for
turning a subspace into a projector. This means, we would need a code equation
of the form \<open>mat_of_cblinfun (Proj (SPAN S)) = \<dots>\<close>. However, this equation is
not accepted by the code generation for reasons we do not understand. But
if we define an auxiliary constant \<open>mat_of_cblinfun_Proj_code\<close> that stands for 
\<open>mat_of_cblinfun (Proj _)\<close>, define a code equation for \<open>mat_of_cblinfun_Proj_code\<close>,
and then define a code equation for \<open>mat_of_cblinfun (Proj S)\<close> in terms of 
\<open>mat_of_cblinfun_Proj_code\<close>, Isabelle accepts the code equations.\<close>

definition "mat_of_cblinfun_Proj_code S = mat_of_cblinfun (Proj S)"
declare mat_of_cblinfun_Proj_code_def[symmetric, code]

lemma mat_of_cblinfun_Proj_code_code[code]: 
  \<comment> \<open>Code equation for computing a projector onto a set S of vectors.
     We first make the vectors S into an orthonormal basis using
     the Gram-Schmidt procedure and then compute the projector
     as the sum of the "butterflies" \<open>x * x*\<close> of the vectors \<open>x\<in>S\<close>
     (done by \<^term>\<open>mk_projector_orthog\<close>).\<close>
  "mat_of_cblinfun_Proj_code (SPAN S :: 'a::onb_enum clinear_space) = 
    (let d = canonical_basis_length TYPE('a) in mk_projector_orthog d 
              (gram_schmidt0 d (filter (\<lambda>v. dim_vec v = d) S)))"
proof -
  (* note [[show_types, show_consts]] *)
  have *: "map_option vec_of_onb_enum (if dim_vec x = canonical_basis_length TYPE('a) then Some (onb_enum_of_vec x :: 'a) else None)
      = (if dim_vec x = canonical_basis_length TYPE('a) then Some x else None)" for x
    by auto
  show ?thesis
    unfolding SPAN_def mat_of_cblinfun_Proj_code_def
    using mat_of_cblinfun_Proj_Span[where S = 
        "map onb_enum_of_vec (filter (\<lambda>v. dim_vec v = (canonical_basis_length TYPE('a))) S) :: 'a list"]
    apply (simp only: Let_def map_filter_map_filter filter_set image_set map_map_filter o_def)
    unfolding *
    by (simp add: map_filter_map_filter[symmetric])
qed

lemma top_clinear_space_code[code]: 
  \<comment> \<open>Code equation for \<^term>\<open>top\<close>, the subspace containing everything.
      Top is represented as the span of the standard basis vectors.\<close>
  "(top::'a clinear_space) =
  (let n = canonical_basis_length TYPE('a::onb_enum) in
    SPAN (unit_vecs n))"
  unfolding SPAN_def
  apply (simp only: index_unit_vec Let_def map_filter_map_filter filter_set image_set map_map_filter 
      map_filter_map o_def unit_vecs_def)
  apply (simp add: onb_enum_of_vec_unit_vec)
  apply (subst nth_image)
  by (auto simp: canonical_basis_length_eq)

lemma bot_as_span[code]: 
  \<comment> \<open>Code equation for \<^term>\<open>bot\<close>, the subspace containing everything.
      Top is represented as the span of the standard basis vectors.\<close>
  "(bot::'a::onb_enum clinear_space) = SPAN []"
  unfolding SPAN_def by (auto simp: Set.filter_def)


lemma sup_spans[code]:
  \<comment> \<open>Code equation for the join (lub) of two subspaces (union of the generating lists)\<close>
 "SPAN A \<squnion> SPAN B = SPAN (A @ B)"
  unfolding SPAN_def 
  by (auto simp: Span_union image_Un filter_Un Let_def)

text \<open>We do not need an equation for \<^term>\<open>(+)\<close> because \<^term>\<open>(+)\<close>
is defined in terms of \<^term>\<open>(\<squnion>)\<close> (for \<^type>\<open>clinear_space\<close>), thus the code generation automatically
computes \<^term>\<open>(+)\<close> in terms of the code for \<^term>\<open>(\<squnion>)\<close>\<close>

definition [code del,code_abbrev]: "Span_code (S::'a::enum ell2 set) = (Span S)"
  \<comment> \<open>A copy of \<^term>\<open>Span\<close> with restricted type. For analogous reasons as
     \<^term>\<open>cblinfun_apply_code\<close>, see there for explanations\<close>

lemma span_Set_Monad[code]: "Span_code (Set_Monad l) = (SPAN (map vec_of_ell2 l))"
  \<comment> \<open>Code equation for the span of a finite set. (\<^term>\<open>Set_Monad\<close> is a datatype
     constructor that represents sets as lists in the computation.)\<close>
  apply (simp add: Span_code_def SPAN_def Let_def)
  apply (subst Set_filter_unchanged)
   apply (metis canonical_basis_length_eq dim_vec_of_onb_enum_list' imageE vec_of_ell2_def)
  by (metis (no_types, lifting) ell2_of_vec_def image_image map_idI set_map vec_of_ell2_inverse)

text \<open>This instantiation defines a code equation for equality tests for clinear_space.
      The actual code for equality tests is given below (lemma \<open>equal_clinear_space_code\<close>).\<close>
instantiation clinear_space :: (onb_enum) equal begin
definition [code del]: "equal_clinear_space (A::'a clinear_space) B = (A=B)"
instance apply intro_classes unfolding equal_clinear_space_def by simp
end

lemma leq_clinear_space_code[code]:
  \<comment> \<open>Code equation for deciding inclusion of one space in another.
     Uses the constant \<^term>\<open>is_subspace_of\<close> which implements the actual
     computation by checking for each generator of A whether it is in the
     span of B (by orthogonal projection onto an orthonormal basis of B
     which is computed using Gram-Schmidt).\<close>
  "SPAN A \<le> (SPAN B :: 'a::onb_enum clinear_space)
      \<longleftrightarrow> (let d = canonical_basis_length TYPE('a) in
          is_subspace_of d
          (filter (\<lambda>v. dim_vec v = d) A)
          (filter (\<lambda>v. dim_vec v = d) B))"
proof -
  define d A' B' where "d = canonical_basis_length TYPE('a)"
    and "A' = filter (\<lambda>v. dim_vec v = d) A"
    and "B' = filter (\<lambda>v. dim_vec v = d) B"

  show ?thesis
    unfolding SPAN_def d_def[symmetric] filter_set Let_def
        A'_def[symmetric] B'_def[symmetric] image_set
    apply (subst Span_leq)
    unfolding d_def[symmetric] map_map o_def
    apply (subst map_cong[where xs=A', OF refl])
     apply (rule vec_of_onb_enum_inverse)
     apply (simp add: A'_def d_def)
    apply (subst map_cong[where xs=B', OF refl])
     apply (rule vec_of_onb_enum_inverse)
    by (simp_all add: B'_def d_def)
qed

lemma equal_clinear_space_code[code]:
  \<comment> \<open>Code equation for equality test. By checking mutual inclusion
      (for which we have code by the preceding code equation).\<close>
  "HOL.equal (A::_ clinear_space) B = (A\<le>B \<and> B\<le>A)"
  unfolding equal_clinear_space_def by auto

lemma apply_cblinfun_code[code]:
  \<comment> \<open>Code equation for applying an operator \<^term>\<open>A\<close> to a subspace. 
      Simply by multiplying each generator with \<^term>\<open>A\<close>\<close>
  "A *\<^sub>S SPAN S = (let d = canonical_basis_length TYPE('a) in
         SPAN (map (mult_mat_vec (mat_of_cblinfun A))
               (filter (\<lambda>v. dim_vec v = d) S)))"
  for A::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum"
proof -
  define dA dB S'
    where "dA = canonical_basis_length TYPE('a)"
      and "dB = canonical_basis_length TYPE('b)"
      and "S' = filter (\<lambda>v. dim_vec v = dA) S"

  have "applyOpSpace A (SPAN S) = A *\<^sub>S Span (set (map onb_enum_of_vec S'))"
    unfolding SPAN_def dA_def[symmetric] Let_def S'_def filter_set
    by simp
  also have "\<dots> = Span ((\<lambda>x. onb_enum_of_vec 
            (mat_of_cblinfun A *\<^sub>v vec_of_onb_enum (onb_enum_of_vec x :: 'a))) ` set S')"
    apply (subst apply_cblinfun_Span)
    by (simp add: image_image)
  also have "\<dots> = Span ((\<lambda>x. onb_enum_of_vec (mat_of_cblinfun A *\<^sub>v x)) ` set S')"
    apply (subst image_cong[OF refl])
     apply (subst vec_of_onb_enum_inverse)
    by (auto simp add: S'_def dA_def)
  also have "\<dots> = SPAN (map (mult_mat_vec (mat_of_cblinfun A)) S')"
    unfolding SPAN_def dB_def[symmetric] Let_def filter_set 
    apply (subst filter_True)
    by (simp_all add: dB_def mat_of_cblinfun_def image_image)

  finally show ?thesis
    unfolding dA_def[symmetric] S'_def[symmetric] Let_def
    by simp
qed

definition [code del, code_abbrev]: "range_cblinfun_code A = A *\<^sub>S top"
\<comment> \<open>A new constant for the special case of applying an operator to the subspace \<^term>\<open>top\<close>
  (i.e., for computing the range of the operator). We do this to be able to give
  more specialized code for this specific situation. (The generic code for
  \<^term>\<open>(*\<^sub>S)\<close> would work but is less efficient because it involves repeated matrix 
  multiplications. @{attribute code_abbrev} makes sure occurrences of \<^term>\<open>A *\<^sub>S top\<close>
  are replaced before starting the actual code generation.\<close>

lemma range_cblinfun_code[code]: 
  \<comment> \<open>Code equation for computing the range of an operator \<^term>\<open>A\<close>.
      Returns the columns of the matrix representation of \<^term>\<open>A\<close>.\<close>
  fixes A :: "'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
  shows "range_cblinfun_code A = SPAN (cols (mat_of_cblinfun A))"
proof -
  define dA dB
    where "dA = canonical_basis_length TYPE('a)"
      and "dB = canonical_basis_length TYPE('b)"
  have carrier_A: "mat_of_cblinfun A \<in> carrier_mat dB dA"
    unfolding mat_of_cblinfun_def dA_def dB_def by simp

  have "range_cblinfun_code A = A *\<^sub>S SPAN (unit_vecs dA)"
    unfolding range_cblinfun_code_def
    by (metis dA_def top_clinear_space_code)
  also have "\<dots> = SPAN (map (\<lambda>i. mat_of_cblinfun A *\<^sub>v unit_vec dA i) [0..<dA])"
    unfolding apply_cblinfun_code dA_def[symmetric] Let_def
    apply (subst filter_True)
    apply (meson carrier_vecD subset_code(1) unit_vecs_carrier)
    by (simp add: unit_vecs_def o_def)
  also have "\<dots> = SPAN (map (\<lambda>x. mat_of_cblinfun A *\<^sub>v col (1\<^sub>m dA) x) [0..<dA])"
    apply (subst map_cong[OF refl])
    by auto
  also have "\<dots> = SPAN (map (col (mat_of_cblinfun A * 1\<^sub>m dA)) [0..<dA])"
    apply (subst map_cong[OF refl])
    apply (subst col_mult2[symmetric])
    apply (rule carrier_A)
    by auto
  also have "\<dots> = SPAN (cols (mat_of_cblinfun A))"
    unfolding cols_def dA_def[symmetric]
    apply (subst right_mult_one_mat[OF carrier_A])
    using carrier_A by blast
  finally show ?thesis
    by -
qed


lemma uminus_Span_code[code]: "- X = range_cblinfun_code (idOp - Proj X)"
  \<comment> \<open>Code equation for the orthogonal complement of a subspace \<^term>\<open>X\<close>. 
      Computed as the range of one minus the projector on \<^term>\<open>X\<close>\<close>
  unfolding range_cblinfun_code_def
  by (metis Proj_ortho_compl imageOp_Proj)

lemma kernel_code[code]: 
  \<comment> \<open>Computes the kernel of an operator \<^term>\<open>A\<close>.
      This is implemented using the existing functions 
      for transforming a matrix into row echelon form (\<^term>\<open>gauss_jordan_single\<close>)
      and for computing a basis of the kernel of such a matrix
      (\<^term>\<open>find_base_vectors\<close>)\<close>
  "kernel A = SPAN (find_base_vectors (gauss_jordan_single (mat_of_cblinfun A)))" 
  for A::"('a::onb_enum,'b::onb_enum) cblinfun"
proof -
  define dA dB Am Ag base
    where "dA = canonical_basis_length TYPE('a)"
      and "dB = canonical_basis_length TYPE('b)"
      and "Am = mat_of_cblinfun A"
      and "Ag = gauss_jordan_single Am"
      and "base = find_base_vectors Ag"

  interpret complex_vec_space dA.

  have Am_carrier: "Am \<in> carrier_mat dB dA"
    unfolding Am_def mat_of_cblinfun_def dA_def dB_def by simp

  have row_echelon: "row_echelon_form Ag"
    unfolding Ag_def
    using Am_carrier refl by (rule gauss_jordan_single)

  have Ag_carrier: "Ag \<in> carrier_mat dB dA"
    unfolding Ag_def
    using Am_carrier refl by (rule gauss_jordan_single(2))

  have base_carrier: "set base \<subseteq> carrier_vec dA"
    unfolding base_def
    using find_base_vectors(1)[OF row_echelon Ag_carrier]
    using Ag_carrier mat_kernel_def by blast

  interpret k: kernel dB dA Ag
      apply standard using Ag_carrier by simp
  
  have basis_base: "kernel.basis dA Ag (set base)"
    using row_echelon Ag_carrier unfolding base_def
    by (rule find_base_vectors(3))


  have "space_as_set (SPAN base)
       = space_as_set (Span (onb_enum_of_vec ` set base :: 'a set))"
    unfolding SPAN_def dA_def[symmetric] Let_def filter_set
    apply (subst filter_True)
    using base_carrier by auto

  also have "\<dots> = complex_span (onb_enum_of_vec ` set base)"
    apply transfer apply (subst span_finite_dim)
    by simp_all

  also have "\<dots> = onb_enum_of_vec ` span (set base)"
    apply (subst module_span_complex_span')
    using base_carrier dA_def by auto

  also have "\<dots> = onb_enum_of_vec ` mat_kernel Ag"
    using basis_base k.Ker.basis_def k.span_same by auto

  also have "\<dots> = onb_enum_of_vec ` {v \<in> carrier_vec dA. Ag *\<^sub>v v = 0\<^sub>v dB}"
    apply (rule arg_cong[where f="\<lambda>x. onb_enum_of_vec ` x"])
    unfolding mat_kernel_def using Ag_carrier
    by simp

  also have "\<dots> = onb_enum_of_vec ` {v \<in> carrier_vec dA. Am *\<^sub>v v = 0\<^sub>v dB}"
    using gauss_jordan_single(1)[OF Am_carrier Ag_def[symmetric]]
    by auto

  also have "\<dots> = {w. A *\<^sub>V w = 0}"
  proof -
    have "onb_enum_of_vec ` {v \<in> carrier_vec dA. Am *\<^sub>v v = 0\<^sub>v dB}
        = onb_enum_of_vec ` {v \<in> carrier_vec dA. A *\<^sub>V onb_enum_of_vec v = 0}"
      apply (rule arg_cong[where f="\<lambda>t. onb_enum_of_vec ` t"])
      apply (rule Collect_cong)
      apply (simp add: Am_def)
      by (metis Am_carrier Am_def carrier_matD(2) carrier_vecD dB_def mat_carrier mat_of_cblinfun_def mat_of_cblinfun_description onb_enum_of_vec_inverse vec_of_onb_enum_inverse vec_of_onb_enum_zero)
    also have "\<dots> = {w \<in> onb_enum_of_vec ` carrier_vec dA. A *\<^sub>V w = 0}"
      apply (subst Compr_image_eq[symmetric])
      by simp
(*     also have "\<dots> \<longleftrightarrow> A *\<^sub>V x = 0"
      apply auto
      by (metis (no_types, lifting) Am_carrier Am_def canonical_basis_length_eq carrier_matD(2) carrier_vec_dim_vec dim_vec_of_onb_enum_list' image_iff mat_carrier mat_of_cblinfun_def onb_enum_of_vec_inverse) *)
    also have "\<dots> = {w. A *\<^sub>V w = 0}"
      apply auto
      by (metis (no_types, lifting) Am_carrier Am_def canonical_basis_length_eq carrier_matD(2) carrier_vec_dim_vec dim_vec_of_onb_enum_list' image_iff mat_carrier mat_of_cblinfun_def onb_enum_of_vec_inverse)
    finally show ?thesis
      by -
  qed

  also have "\<dots> = space_as_set (kernel A)"
    apply transfer by auto

  finally have "SPAN base = kernel A"
    by (simp add: space_as_set_inject)
  then show ?thesis
    by (simp add: base_def Ag_def Am_def)
qed

lemma inf_clinear_space_code[code]: 
  \<comment> \<open>Code equation for intersection of subspaces.
     Reduced to orthogonal complement and sum of subspaces
     for which we already have code equations.\<close>
  "(A::'a::onb_enum clinear_space) \<sqinter> B = - (- A \<squnion> - B)"
  by (subst ortho_involution[symmetric], subst compl_inf, simp)

lemma Sup_clinear_space_code[code]:
  \<comment> \<open>Supremum (sum) of a set of subspaces. Implemented
     by repeated pairwise sum.\<close>
  "Sup (Set_Monad l :: 'a::onb_enum clinear_space set) = fold sup l bot"
  unfolding Set_Monad_def
  by (simp add: Sup_set_fold)


lemma Inf_clinear_space_code[code]: 
  \<comment> \<open>Infimum (intersection) of a set of subspaces. 
      Implemented by the orthogonal complement of the supremum.\<close>
  "Inf (Set_Monad l :: 'a::onb_enum clinear_space set)
  = - Sup (Set_Monad (map uminus l))"
  unfolding Set_Monad_def
  apply (induction l)
  by auto

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

text \<open>Code equation for \<^term>\<open>UNIV\<close>. 
  It is now implemented via type class \<^class>\<open>enum\<close> 
  (which provides a list of all values).\<close>
declare [[code drop: UNIV]]
declare enum_class.UNIV_enum[code]

text \<open>Setup for code generation involving sets of ell2/clinear_spaces.
  This configures to use lists for representing sets in code.\<close>
derive (eq) ceq clinear_space
derive (no) ccompare clinear_space
derive (monad) set_impl clinear_space
derive (eq) ceq ell2
derive (no) ccompare ell2
derive (monad) set_impl ell2


unbundle no_jnf_notation
unbundle no_cblinfun_notation

end

section \<open>\<open>Bounded_Operators_Code\<close> -- Support for code generation\<close>

theory Bounded_Operators_Code
  imports
    Bounded_Operators_Matrices Containers.Set_Impl 
begin

no_notation "Lattice.meet" (infixl "\<sqinter>\<index>" 70)
no_notation "Lattice.join" (infixl "\<squnion>\<index>" 65)
hide_const (open) Coset.kernel
hide_const (open) Order.bottom Order.top

unbundle jnf_notation
unbundle cblinfun_notation

subsection \<open>Code equations for cblinfun operators\<close>

text \<open>In this subsection, we define the code for all operations involving only 
  operators (no combinations of operators/vectors/subspaces)\<close>

text \<open>This lemma defines addition. By writing \<^term>\<open>mat_of_cblinfun (M + N)\<close>
on the left hand side, we get access to the\<close>
(* TODO: rename \<rightarrow> cblinfun_of_mat_plus *)
declare cblinfun_of_mat_plusOp'[code]
(* TODO: rename (remove ') *)
declare cblinfun_of_mat_id'[code]
(* TODO: rename (remove ') *)
declare mat_of_cblinfun_zero'[code]
(* TODO: rename (remove ') *)
declare cblinfun_of_mat_uminusOp'[code]
(* TODO: rename (remove ') *)
declare cblinfun_of_mat_minusOp'[code]
(* TODO: rename (remove inj_option) *)
declare mat_of_cblinfun_classical_operator_inj_option[code]

text \<open>This instantiation defines a code equation for equality tests for cblinfun operators.\<close>
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
  must be of sort \<open>enum\<close> to make make sure that  \<^typ>\<open>'a ell2\<close> is finite dimensional).
  
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

instantiation ell2 :: (enum) equal begin
definition [code]: "equal_ell2 M N \<longleftrightarrow> vec_of_ell2 M = vec_of_ell2 N" 
  for M N :: "'a::enum ell2"
instance 
  apply intro_classes
  unfolding equal_ell2_def
  by (metis vec_of_ell2_inverse) 
end

lemma vec_of_ell2_zero[code]:
  "vec_of_ell2 (0::'a::enum ell2) = zero_vec (canonical_basis_length TYPE('a ell2))"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_zero)

(* TODO: To preliminaries *)
fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

(* TODO: To preliminaries *)
definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"

(* TODO: To Bounded_Operators_Matrices *)
lemma vec_of_ell2_ket:
  "vec_of_ell2 (ket i) = unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)" for i::"'a::enum"
  sorry

declare vec_of_ell2_ket[code]

lemma vec_of_ell2_timesScalarVec[code]: "vec_of_ell2 (scaleC a \<psi>) = smult_vec a (vec_of_ell2 \<psi>)"
  for \<psi> :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_scaleC)

lemma vec_of_ell2_scaleR[code]: "vec_of_ell2 (scaleR a \<psi>) = smult_vec (complex_of_real a) (vec_of_ell2 \<psi>)"
  for \<psi> :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_scaleR)

lemma ell2_of_vec_plus[code]:
  "vec_of_ell2 (x + y) =  (vec_of_ell2 x) + (vec_of_ell2 y)" for x y :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_add) 

lemma ell2_of_vec_minus[code]:
  "vec_of_ell2 (x - y) =  (vec_of_ell2 x) - (vec_of_ell2 y)" for x y :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_minus)

lemma ell2_of_vec_uminus[code]:
  "vec_of_ell2 (- y) =  - (vec_of_ell2 y)" for y :: "'a::enum ell2"
  by (simp add: vec_of_ell2_def vec_of_onb_enum_uminus)

lemma cinner_ell2_code [code]: "cinner \<psi> \<phi> = scalar_prod (map_vec cnj (vec_of_ell2 \<psi>)) (vec_of_ell2 \<phi>)"
  by (simp add: cinner_ell2_code vec_of_ell2_def)

lemma norm_ell2_code [code]: "norm \<psi> = 
  (let \<psi>' = vec_of_ell2 \<psi> in
    sqrt (\<Sum> i \<in> {0 ..< dim_vec \<psi>'}. let z = vec_index \<psi>' i in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
  by (simp add: norm_ell2_code vec_of_ell2_def)

(* TODO move to ..._Matrices *)
(* TODO better name *)
lemma times_ell2_code: "vec_of_ell2 (\<psi> * \<phi>) == vec_of_list [vec_index (vec_of_ell2 \<psi>) 0 * vec_index (vec_of_ell2 \<phi>) 0]"
  for \<psi> \<phi> :: "'a::{CARD_1,enum} ell2"
  sorry
declare times_ell2_code[code]

(* TODO move to ..._Matrices *)
(* TODO better name *)
lemma one_ell2_code: "vec_of_ell2 (1 :: 'a::{CARD_1,enum} ell2) == vec_of_list [1]"
  sorry
declare one_ell2_code[code]

subsection \<open>Vector/Matrix\<close>

(* TODO explain everything in this section *)

(* Wrapper class so that we can define a code datatype constructors for that type (does not work with type synonyms) *)
(* TODO: Find out if it's OK to remove the ell2 from the output (once QRHL compiles) *)
typedef ('a::enum,'b::enum) code_l2bounded = "UNIV::('a ell2, 'b ell2) cblinfun set" ..
setup_lifting type_definition_code_l2bounded

lift_definition l2bounded_of_mat' :: "complex mat \<Rightarrow> ('a::enum,'b::enum) code_l2bounded"
  is cblinfun_of_mat.
lift_definition mat_of_l2bounded' :: "('a::enum,'b::enum) code_l2bounded \<Rightarrow> complex mat"
  is mat_of_cblinfun.

lemma mat_of_cblinfun_inverse' [code abstype]:
  "l2bounded_of_mat' (mat_of_l2bounded' B) = B" 
  apply transfer
  using mat_of_cblinfun_inverse by blast

lemma [code]: "mat_of_l2bounded' (Abs_code_l2bounded X) = mat_of_cblinfun X"
  apply transfer by simp
lemma [code]: "mat_of_cblinfun (Rep_code_l2bounded X) = mat_of_l2bounded' X"
  apply transfer by simp


lift_definition applyOp_code :: "('a::enum, 'b::enum) code_l2bounded \<Rightarrow> 'a ell2 \<Rightarrow> 'b ell2" 
  is "cblinfun_apply :: ('a ell2,'b ell2) cblinfun \<Rightarrow> _ \<Rightarrow> _".

lemma [symmetric,code_abbrev]: "cblinfun_apply M = applyOp_code (Abs_code_l2bounded M)"
  apply transfer by simp

lemma ell2_of_vec_applyOp[code]:
  "vec_of_ell2 (applyOp_code M x) = (mult_mat_vec (mat_of_l2bounded' M) (vec_of_ell2 x))"
  by (simp add: applyOp_code.rep_eq mat_of_cblinfun_description mat_of_l2bounded'.rep_eq vec_of_ell2_def) 


(* TODO: move to ..._Matrices *)
lemma mat_of_cblinfun_ell2_to_l2bounded:
  "mat_of_cblinfun (vector_to_cblinfun \<psi>) = mat_of_cols (canonical_basis_length TYPE('a)) [vec_of_onb_enum \<psi>]" 
  for \<psi>::"'a::onb_enum"
  sorry

definition [code del,code_abbrev]: "vector_to_cblinfun_code (\<psi>::'a ell2) = (vector_to_cblinfun \<psi>)"

lemma mat_of_cblinfun_ell2_to_l2bounded_code[code]: 
  "mat_of_cblinfun (vector_to_cblinfun_code \<psi>) = mat_of_cols (CARD('a)) [vec_of_ell2 \<psi>]" 
  for \<psi>::"'a::enum ell2"
  by (simp add: mat_of_cblinfun_ell2_to_l2bounded canonical_basis_length_ell2_def vec_of_ell2_def vector_to_cblinfun_code_def)




subsection \<open>Subspaces\<close>

(* TODO add explanations *)

(* TODO: Problem: this is only well-defined if x contains only vectors of the right dimension.
   Otherwise all the code below might be incorrect. *)
definition [code del]: "SPAN x = (let n = canonical_basis_length TYPE('a::onb_enum) in
  Span (onb_enum_of_vec ` Set.filter (\<lambda>v. dim_vec v = n) (set x)) :: 'a clinear_space)"
code_datatype SPAN


definition "mk_projector (S::'a::onb_enum clinear_space) = mat_of_cblinfun (Proj S)" 

(* TODO: move to ..._Matrices *)
text \<open>\<^term>\<open>mk_projector_orthog d L\<close> takes a list L of d-dimensional vectors
and returns the projector onto the span of L. (Assuming that all vectors in L are orthogonal.)\<close>
fun mk_projector_orthog :: "nat \<Rightarrow> complex vec list \<Rightarrow> complex mat" where
  "mk_projector_orthog d [] = zero_mat d d"
| "mk_projector_orthog d [v] = (let norm2 = cscalar_prod v v in
                                if norm2=0 then zero_mat d d else
                                smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]))"
| "mk_projector_orthog d (v#vs) = (let norm2 = cscalar_prod v v in
                                   if norm2=0 then mk_projector_orthog d vs else
                                   smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [v]) 
                                        + mk_projector_orthog d vs)"

(* TODO move to ..._Matrices *)
lemma mat_of_cblinfun_Proj_Span: "mat_of_cblinfun (Proj (Span (set S))) =
    (let d = canonical_basis_length TYPE('a) in 
      mk_projector_orthog d (gram_schmidt d (map vec_of_onb_enum S)))"
  for S :: "'a::onb_enum list"
  using[[show_consts,show_types]]
  sorry

lemma mk_projector_SPAN[code]: 
  "mk_projector (SPAN S :: 'a::onb_enum clinear_space) = 
    (let d = canonical_basis_length TYPE('a) in mk_projector_orthog d 
              (gram_schmidt d (filter (\<lambda>v. dim_vec v = d) S)))"
proof -
  note [[show_types, show_consts]]
  have *: "map_option vec_of_onb_enum (if dim_vec x = canonical_basis_length TYPE('a) then Some (onb_enum_of_vec x :: 'a) else None)
      = (if dim_vec x = canonical_basis_length TYPE('a) then Some x else None)" for x
    by auto
  show ?thesis
    unfolding mk_projector_def SPAN_def
    using mat_of_cblinfun_Proj_Span[where S = 
        "map onb_enum_of_vec (filter (\<lambda>v. dim_vec v = (canonical_basis_length TYPE('a))) S) :: 'a list"]
    apply (simp only: Let_def map_filter_map_filter filter_set image_set map_map_filter o_def)
    unfolding *
    by (simp add: map_filter_map_filter[symmetric])
qed

lemma [code]: "mat_of_cblinfun (Proj S) = mk_projector S" for S :: "'a::onb_enum clinear_space"
  unfolding mk_projector_def by simp

(* TODO move to ..._Matrices *)
definition "orthogonal_complement_vec n vs = 
  filter ((\<noteq>) (zero_vec n)) (drop (length vs) (gram_schmidt n (vs @ map (unit_vec n) [0..<n])))"

(* TODO: move to Preliminaries *)
lemma map_filter_map: "List.map_filter f (map g l) = List.map_filter (f o g) l"
  apply (induction l)
  apply (simp add: map_filter_simps)
  apply auto by (metis map_filter_simps(1))

(* TODO: move to Preliminaries *)
lemma map_filter_Some[simp]: "List.map_filter (\<lambda>x. Some (f x)) l = map f l"
  apply (induction l)
   apply (simp add: map_filter_simps)
  by (simp add: map_filter_simps(1))

(* (* TODO: move to Preliminaries *)
lemma map_filter_Some'[simp]: "List.map_filter (\<lambda>x. if f x then Some x else None) l = filter f l"
  apply (induction l)
   apply (simp add: map_filter_simps)
  by (simp add: map_filter_simps(1)) *)

(* TODO move to ..._Matrices *)
lemma onb_enum_of_vec_unit_vec: "onb_enum_of_vec (unit_vec (canonical_basis_length TYPE('a)) i) = (canonical_basis!i :: 'a::onb_enum)"
  sorry

(* TODO: Move to Complex_Inner_Product *)
lemma Span_canonical_basis[simp]: "Span (set canonical_basis) = top"
  using Span.rep_eq is_basis_def is_basis_set space_as_set_inject top_clinear_space.rep_eq by fastforce

lemma top_as_span[code]: "(top::'a clinear_space) = 
  (let n = canonical_basis_length TYPE('a::onb_enum) in
    SPAN (map (unit_vec n) [0..<n]))"
  unfolding SPAN_def
  apply (simp only: index_unit_vec Let_def map_filter_map_filter filter_set image_set map_map_filter map_filter_map o_def)
  apply (simp add: onb_enum_of_vec_unit_vec)
  apply (subst nth_image)
  by (auto simp: canonical_basis_length_eq)

(* TODO: Move to the Complex_Vector_Spaces *)
lemma Span_empty[simp]: "Span {} = bot"
  sorry

lemma bot_as_span[code]: "(bot::'a::onb_enum clinear_space) = SPAN []"
  unfolding SPAN_def by (auto simp: Set.filter_def)

(* TODO: Move to the Complex_Vector_Spaces *)
lemma Span_union: "Span A \<squnion> Span B = Span (A \<union> B)"
  sorry

lemma filter_Un: "Set.filter f (x \<union> y) = Set.filter f x \<union> Set.filter f y"
  by (simp add: Int_Un_distrib2 Set_project_code)

lemma sup_spans[code]: "SPAN A \<squnion> SPAN B = SPAN (A @ B)"
  unfolding SPAN_def 
  by (auto simp: Span_union image_Un filter_Un Let_def)

(* TODO move to ..._Matrices *)
lemma ortho_Span: "- Span (set S) =
    Span (onb_enum_of_vec ` set (orthogonal_complement_vec 
        (canonical_basis_length TYPE('a::onb_enum)) (map vec_of_onb_enum S)))"
  sorry

lemma ortho_SPAN[code]: "- (SPAN S :: 'a::onb_enum clinear_space)
        = (let d = canonical_basis_length TYPE('a) in 
            SPAN (orthogonal_complement_vec d (filter (\<lambda>v. dim_vec v = d) S)))"
proof -
  note [[show_types, show_consts]]
  have *: "map_option vec_of_onb_enum (if dim_vec x = canonical_basis_length TYPE('a) 
          then Some (onb_enum_of_vec x :: 'a) else None)
      = (if dim_vec x = canonical_basis_length TYPE('a) then Some x else None)" for x
    by auto
  show ?thesis
    unfolding mk_projector_def SPAN_def
    using ortho_Span[where S = 
        "map onb_enum_of_vec (filter (\<lambda>v. dim_vec v = (canonical_basis_length TYPE('a))) S) :: 'a list"]
    apply (simp only: Let_def  filter_set image_set map_map_filter o_def)
    sorry
qed

definition [code del,code_abbrev]: "span_code (S::'a::enum ell2 set) = (Span S)"

lemma span_Set_Monad[code]: "span_code (Set_Monad l) = (SPAN (map vec_of_ell2 l))"
  apply (auto simp: SPAN_def vec_of_ell2_def image_image Set.filter_def)
  sorry

instantiation clinear_space :: (onb_enum) equal begin
definition [code del]: "equal_clinear_space (A::'a clinear_space) B = (A=B)"
instance apply intro_classes unfolding equal_clinear_space_def by simp
end

(* TODO: Move to ..._Matrices *)
definition "is_subspace_of n vs ws =  
  list_all ((=) (zero_vec n)) (drop (length ws) (gram_schmidt n (ws @ vs)))"

(* TODO: Move to ..._Matrices *)
lemma Span_leq: "(Span (set A) \<le> Span (set B)) =
    is_subspace_of (canonical_basis_length TYPE('a::onb_enum)) (map vec_of_onb_enum A) (map vec_of_onb_enum B)"
  sorry

lemma SPAN_leq[code]: "SPAN A \<le> (SPAN B :: 'a::onb_enum clinear_space) \<longleftrightarrow> is_subspace_of (canonical_basis_length TYPE('a)) A B"
  sorry

lemma apply_cblinfun_Span: 
  "A *\<^sub>S Span (set S) = Span (onb_enum_of_vec ` set (map ((*\<^sub>v) (mat_of_cblinfun A)) (map vec_of_onb_enum S)))"
  apply (auto simp: applyOpSpace_Span image_image)
  by (metis mat_of_cblinfun_description onb_enum_of_vec_inverse)

lemma applyOpSpace_SPAN[code]: "applyOpSpace A (SPAN S) = SPAN (map (mult_mat_vec (mat_of_cblinfun A)) S)"
  for A::"('a::onb_enum,'b::onb_enum) cblinfun"
  unfolding SPAN_def Let_def
  using apply_cblinfun_Span[where A = A and S = 
        "map onb_enum_of_vec (filter (\<lambda>v. dim_vec v = (canonical_basis_length TYPE('a))) S) :: 'a list"]
  sorry

lemma kernel_SPAN[code]: "kernel A = SPAN (find_base_vectors (gauss_jordan_single (mat_of_cblinfun A)))" 
  for A::"('a::onb_enum,'b::onb_enum) cblinfun"
  sorry

lemma [code_abbrev]: "kernel (A - a *\<^sub>C idOp) = eigenspace a A" 
  unfolding eigenspace_def by simp

lemma [code]: "HOL.equal (A::_ clinear_space) B = (A\<le>B \<and> B\<le>A)"
  unfolding equal_clinear_space_def by auto

lemma [code]: "(A::'a::onb_enum clinear_space) \<sqinter> B = - (- A \<squnion> - B)"
  by (subst ortho_involution[symmetric], subst compl_inf, simp)

lemma [code]: "Inf (Set_Monad l :: 'a::onb_enum clinear_space set) = fold inf l top"
  unfolding Set_Monad_def
  by (simp add: Inf_set_fold)


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

(* TODO explain what for *)
declare [[code drop: UNIV]]
declare enum_class.UNIV_enum[code]

(* TODO explain what for *)
derive (eq) ceq clinear_space
derive (no) ccompare clinear_space
derive (monad) set_impl clinear_space
derive (eq) ceq ell2
derive (no) ccompare ell2
derive (monad) set_impl ell2


unbundle no_jnf_notation
unbundle no_cblinfun_notation

end

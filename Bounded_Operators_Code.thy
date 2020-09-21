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
declare cblinfun_of_mat_timesOp[code]
declare mat_of_cblinfun_scalarMult[code]
declare mat_of_cblinfun_scaleR[code]
declare cblinfun_of_mat_adjoint[code]

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

lemma vec_of_ell2_ket[code]:
  "vec_of_ell2 (ket i) = unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)" 
  for i::"'a::enum"
  using vec_of_ell2_def vec_of_onb_enum_ket by metis

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

lemma cinner_ell2_code' [code]: "cinner \<psi> \<phi> = cscalar_prod (vec_of_ell2 \<phi>) (vec_of_ell2 \<psi>)"
  by (simp add: cinner_ell2_code vec_of_ell2_def)

lemma norm_ell2_code [code]: "norm \<psi> = 
  (let \<psi>' = vec_of_ell2 \<psi> in
    sqrt (\<Sum> i \<in> {0 ..< dim_vec \<psi>'}. let z = vec_index \<psi>' i in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
  by (simp add: norm_ell2_code vec_of_ell2_def)

lemma times_ell2_code'[code]: 
  fixes \<psi> \<phi> :: "'a::{CARD_1,enum} ell2"
  shows "vec_of_ell2 (\<psi> * \<phi>)
   = vec_of_list [vec_index (vec_of_ell2 \<psi>) 0 * vec_index (vec_of_ell2 \<phi>) 0]"
  using vec_of_ell2_def times_ell2_code by metis

lemma one_ell2_code'[code]: "vec_of_ell2 (1 :: 'a::{CARD_1,enum} ell2) = vec_of_list [1]"
  using one_ell2_code vec_of_ell2_def by metis

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

definition [code del,code_abbrev]: "vector_to_cblinfun_code (\<psi>::'a ell2) = (vector_to_cblinfun \<psi>)"

lemma mat_of_cblinfun_ell2_to_l2bounded_code[code]: 
  "mat_of_cblinfun (vector_to_cblinfun_code \<psi>) = mat_of_cols (CARD('a)) [vec_of_ell2 \<psi>]" 
  for \<psi>::"'a::enum ell2"
  by (simp add: mat_of_cblinfun_ell2_to_l2bounded canonical_basis_length_ell2_def vec_of_ell2_def vector_to_cblinfun_code_def)



subsection \<open>Subspaces\<close>

(* TODO add explanations *)

definition [code del]: "SPAN x = (let n = canonical_basis_length TYPE('a::onb_enum) in
    Span (onb_enum_of_vec ` Set.filter (\<lambda>v. dim_vec v = n) (set x)) :: 'a clinear_space)"
code_datatype SPAN


definition "mk_projector (S::'a::onb_enum clinear_space)
   = mat_of_cblinfun (Proj S)" 

text \<open>\<^term>\<open>mk_projector_orthog d L\<close> takes a list L of d-dimensional vectors
and returns the projector onto the span of L. (Assuming that all vectors in L are orthogonal
and nonzero.)\<close>

fun mk_projector_orthog :: "nat \<Rightarrow> complex vec list \<Rightarrow> complex mat" where
  "mk_projector_orthog d [] = zero_mat d d"
| "mk_projector_orthog d [v] = (let norm2 = cscalar_prod v v in
                                smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [conjugate v]))"
| "mk_projector_orthog d (v#vs) = (let norm2 = cscalar_prod v v in
                                   smult_mat (1/norm2) (mat_of_cols d [v] * mat_of_rows d [conjugate v]) 
                                        + mk_projector_orthog d vs)"

lemma mat_of_cblinfun_Proj_Span_aux_1:
  fixes S :: "'a::onb_enum list"
  defines "d == canonical_basis_length TYPE('a)"
  assumes ortho: "is_ortho_set (set S)" and distinct: "distinct S"
  shows "mk_projector_orthog d (map vec_of_onb_enum S) = mk_projector (Span (set S))"
proof -
  define Snorm where "Snorm = map (\<lambda>s. s /\<^sub>R norm s) S"
  
  have "distinct Snorm"
  proof (insert ortho distinct, unfold Snorm_def, induction S)
    case Nil
    show ?case by simp
  next
    case (Cons s S)
    then have "is_ortho_set (set S)" and "distinct S"
      unfolding is_ortho_set_def by auto
    note IH = Cons.IH[OF this]
    have "s /\<^sub>R norm s \<notin> (\<lambda>s. s /\<^sub>R norm s) ` set S"
    proof auto
      fix s' assume "s' \<in> set S" and same: "s /\<^sub>R norm s = s' /\<^sub>R norm s'"
      with Cons.prems have "s \<noteq> s'" by auto
      have "s \<noteq> 0"
        by (metis Cons.prems(1) is_ortho_set_def list.set_intros(1))
      then have "0 \<noteq> \<langle>s /\<^sub>R norm s, s /\<^sub>R norm s\<rangle>"
        by simp
      also have \<open>\<langle>s /\<^sub>R norm s, s /\<^sub>R norm s\<rangle> = \<langle>s /\<^sub>R norm s, s' /\<^sub>R norm s'\<rangle>\<close>
        by (simp add: same)
      also have \<open>\<langle>s /\<^sub>R norm s, s' /\<^sub>R norm s'\<rangle> = \<langle>s, s'\<rangle> / (norm s * norm s')\<close>
        by (simp add: scaleR_scaleC divide_inverse_commute)
      also from \<open>s' \<in> set S\<close> \<open>s \<noteq> s'\<close> have "\<dots> = 0"
        using Cons.prems unfolding is_ortho_set_def by simp
      finally show False
        by simp
    qed
    then show ?case
      using IH by simp
  qed

  have norm_Snorm: "norm s = 1" if "s \<in> set Snorm" for s
    using that ortho unfolding Snorm_def is_ortho_set_def by auto

  have ortho_Snorm: "is_ortho_set (set Snorm)"
    unfolding is_ortho_set_def
  proof (intro conjI ballI impI)
    fix x y
    show "x \<in> set Snorm \<Longrightarrow> x \<noteq> 0"
      using norm_Snorm[of 0] by auto
    assume "x \<in> set Snorm" and "y \<in> set Snorm" and "x \<noteq> y"
    from \<open>x \<in> set Snorm\<close>
    obtain x' where x: "x = x' /\<^sub>R norm x'" and x': "x' \<in> set S"
      unfolding Snorm_def by auto
    from \<open>y \<in> set Snorm\<close>
    obtain y' where y: "y = y' /\<^sub>R norm y'" and y': "y' \<in> set S"
      unfolding Snorm_def by auto
    from \<open>x \<noteq> y\<close> x y have \<open>x' \<noteq> y'\<close> by auto
    with x' y' ortho have "cinner x' y' = 0"
      unfolding is_ortho_set_def by auto
    then show "cinner x y = 0"
      unfolding x y scaleR_scaleC by auto
  qed

  have inj_butter: "inj_on butterfly (set Snorm)"
  proof (rule inj_onI)
    fix x y 
    assume "x \<in> set Snorm" and "y \<in> set Snorm"
    assume "butterfly x = butterfly y"
    then obtain c where xcy: "x = c *\<^sub>C y" and "cmod c = 1"
      using inj_butterfly by auto
    have "0 \<noteq> cmod (cinner x x)"
      using \<open>x \<in> set Snorm\<close> norm_Snorm
      by (simp add: cinner_norm_sq)
    also have "cmod (cinner x x) = cmod (c * \<langle>x, y\<rangle>)"
      apply (subst (2) xcy) by simp
    also have "\<dots> = cmod \<langle>x, y\<rangle>"
      using \<open>cmod c = 1\<close> by (simp add: norm_mult)
    finally have "\<langle>x, y\<rangle> \<noteq> 0"
      by simp
    then show "x = y"
      using ortho_Snorm \<open>x \<in> set Snorm\<close> \<open>y \<in> set Snorm\<close>
      unfolding is_ortho_set_def by auto
  qed

  from \<open>distinct Snorm\<close> inj_butter
  have distinct': "distinct (map butterfly Snorm)"
    unfolding distinct_map by simp

  have Span_Snorm: "Span (set Snorm) = Span (set S)"
    apply (transfer fixing: Snorm S)
    apply (simp add: scaleR_scaleC Snorm_def)
    apply (subst span_image_scale) 
    using is_ortho_set_def ortho by fastforce+

  have "mk_projector_orthog d (map vec_of_onb_enum S)
      = mat_of_cblinfun (sum_list (map butterfly Snorm))"
    unfolding Snorm_def
  proof (induction S)
    case Nil
    show ?case 
      by (simp add: d_def mat_of_cblinfun_zero')
  next
    case (Cons a S)
    define sumS where "sumS = sum_list (map butterfly (map (\<lambda>s. s /\<^sub>R norm s) S))"
    with Cons have IH: "mk_projector_orthog d (map vec_of_onb_enum S)
                  = mat_of_cblinfun sumS"
      by simp

    define factor where "factor = inverse ((complex_of_real (norm a))\<^sup>2)"
    have factor': "factor = 1 / (vec_of_onb_enum a \<bullet>c vec_of_onb_enum a)"
      unfolding factor_def cinner_ell2_code[symmetric]
      by (simp add: inverse_eq_divide power2_norm_eq_cinner'')

    have "mk_projector_orthog d (map vec_of_onb_enum (a # S))
          = factor \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a] 
                    * mat_of_rows d [conjugate (vec_of_onb_enum a)])
            + mat_of_cblinfun sumS"
      apply (cases S)
       apply (auto simp add: factor' sumS_def d_def mat_of_cblinfun_zero')[1]
      by (auto simp add: IH[symmetric] factor' d_def)

    also have "\<dots> = factor \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a] *
         adjoint_mat (mat_of_cols d [vec_of_onb_enum a])) + mat_of_cblinfun sumS"
      apply (rule arg_cong[where f="\<lambda>x. _ \<cdot>\<^sub>m (_ * x) + _"])
      apply (rule mat_eq_iff[THEN iffD2])
        apply (auto simp add: adjoint_mat_def)
      apply (subst mat_of_rows_index)
        apply auto
      apply (subst mat_of_cols_index)
        apply auto
      by (simp add: assms(1) canonical_basis_length_eq dim_vec_of_onb_enum_list')

    also have "\<dots> = mat_of_cblinfun (butterfly (a /\<^sub>R norm a)) + mat_of_cblinfun sumS"
      apply (simp add: butterfly_scaleR power_inverse mat_of_cblinfun_scaleR factor_def)
      by (simp add: butterfly_def' cblinfun_of_mat_timesOp
          cblinfun_of_mat_adjoint mat_of_cblinfun_ell2_to_l2bounded d_def)

    finally show ?case
      by (simp add: cblinfun_of_mat_plusOp' sumS_def)
  qed
  also have "\<dots> = mat_of_cblinfun (\<Sum>s\<in>set Snorm. butterfly s)"
    by (metis distinct' distinct_map sum.distinct_set_conv_list)
  also have "\<dots> = mat_of_cblinfun (\<Sum>s\<in>set Snorm. proj s)"
    apply (rule arg_cong[where f="mat_of_cblinfun"])
    apply (rule sum.cong[OF refl])
    apply (rule butterfly_proj)
    using norm_Snorm by simp
  also have "\<dots> = mat_of_cblinfun (Proj (Span (set Snorm)))"
    apply (rule arg_cong[of _ _ mat_of_cblinfun])
  proof (insert ortho_Snorm, insert \<open>distinct Snorm\<close>, induction Snorm)
    case Nil
    show ?case
      by simp
  next
    case (Cons a Snorm)
    from Cons.prems have [simp]: "a \<notin> set Snorm"
      by simp

    have "sum proj (set (a # Snorm))
        = proj a + sum proj (set Snorm)"
      by auto
    also have "\<dots> = proj a + Proj (Span (set Snorm))"
      apply (subst Cons.IH)
      using Cons.prems apply auto
      using is_onb_delete by blast
    also have "\<dots> = Proj (Span (set (a # Snorm)))"
      apply (rule Proj_Span_insert[symmetric])
      using Cons.prems by auto
    finally show ?case
      by -
  qed
  also have "\<dots> = mk_projector (Span (set S))"
    unfolding mk_projector_def Span_Snorm by simp
  finally show ?thesis
    by -
qed

lemma mat_of_cblinfun_Proj_Span: 
  fixes S :: "'a::onb_enum list"
  shows "mat_of_cblinfun (Proj (Span (set S))) =
    (let d = canonical_basis_length TYPE('a) in 
      mk_projector_orthog d (gram_schmidt0 d (map vec_of_onb_enum S)))"
proof-
  define d gs 
    where "d = canonical_basis_length TYPE('a)"
      and "gs = gram_schmidt0 d (map vec_of_onb_enum S)"
  interpret complex_vec_space d.
  have gs_dim: "x \<in> set gs \<Longrightarrow> dim_vec x = d" for x
    by (smt canonical_basis_length_eq carrier_vecD carrier_vec_dim_vec d_def dim_vec_of_onb_enum_list' ex_map_conv gram_schmidt0_result(1) gs_def subset_code(1))
  have ortho_gs: "is_ortho_set (set (map onb_enum_of_vec gs :: 'a list))"
    apply (rule corthogonal_is_ortho_set)
    by (smt canonical_basis_length_eq carrier_dim_vec cof_vec_space.gram_schmidt0_result(1) d_def dim_vec_of_onb_enum_list' gram_schmidt0_result(3) gs_def imageE map_idI map_map o_apply set_map subset_code(1) vec_of_onb_enum_inverse)
  have distinct_gs: "distinct (map onb_enum_of_vec gs :: 'a list)"
    by (metis (mono_tags, hide_lams) canonical_basis_length_eq carrier_vec_dim_vec cof_vec_space.gram_schmidt0_result(2) d_def dim_vec_of_onb_enum_list' distinct_map gs_def gs_dim image_iff inj_on_inverseI set_map subsetI vec_of_onb_enum_inverse)

  have "mk_projector_orthog d gs 
      = mk_projector_orthog d (map vec_of_onb_enum (map onb_enum_of_vec gs :: 'a list))"
    apply simp
    apply (subst map_cong[where ys=gs and g=id], simp)
    using gs_dim by (auto intro!: vec_of_onb_enum_inverse simp: d_def)
  also have "\<dots> = mk_projector (Span (set (map onb_enum_of_vec gs :: 'a list)))"
    unfolding d_def
    apply (subst mat_of_cblinfun_Proj_Span_aux_1)
    using ortho_gs distinct_gs by auto
  also have "\<dots> = mk_projector (Span (set S))"
    apply (rule arg_cong[where f=mk_projector])
    unfolding gs_def d_def
    apply (subst Span_onb_enum_gram_schmidt0)
    by (auto simp add: canonical_basis_length_eq carrier_vecI dim_vec_of_onb_enum_list')
  also have "\<dots> = mat_of_cblinfun (Proj (Span (set S)))"
    unfolding mk_projector_def by simp
  finally show ?thesis
    unfolding d_def gs_def by auto
qed





lemma mk_projector_SPAN[code]: 
  "mk_projector (SPAN S :: 'a::onb_enum clinear_space) = 
    (let d = canonical_basis_length TYPE('a) in mk_projector_orthog d 
              (gram_schmidt0 d (filter (\<lambda>v. dim_vec v = d) S)))"
proof -
  (* note [[show_types, show_consts]] *)
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




lemma top_as_span[code]: "(top::'a clinear_space) = 
  (let n = canonical_basis_length TYPE('a::onb_enum) in
    SPAN (unit_vecs n))"
  unfolding SPAN_def
  apply (simp only: index_unit_vec Let_def map_filter_map_filter filter_set image_set map_map_filter 
      map_filter_map o_def unit_vecs_def)
  apply (simp add: onb_enum_of_vec_unit_vec)
  apply (subst nth_image)
  by (auto simp: canonical_basis_length_eq)

lemma bot_as_span[code]: "(bot::'a::onb_enum clinear_space) = SPAN []"
  unfolding SPAN_def by (auto simp: Set.filter_def)


lemma sup_spans[code]: "SPAN A \<squnion> SPAN B = SPAN (A @ B)"
  unfolding SPAN_def 
  by (auto simp: Span_union image_Un filter_Un Let_def)


definition [code del,code_abbrev]: "span_code (S::'a::enum ell2 set) = (Span S)"

lemma span_Set_Monad[code]: "span_code (Set_Monad l) = (SPAN (map vec_of_ell2 l))"
  apply (simp add: span_code_def SPAN_def Let_def)
  apply (subst Set_filter_unchanged)
   apply (metis canonical_basis_length_eq dim_vec_of_onb_enum_list' imageE vec_of_ell2_def)
  by (metis (no_types, lifting) ell2_of_vec_def image_image map_idI set_map vec_of_ell2_inverse)

instantiation clinear_space :: (onb_enum) equal begin
definition [code del]: "equal_clinear_space (A::'a clinear_space) B = (A=B)"
instance apply intro_classes unfolding equal_clinear_space_def by simp
end

lemma SPAN_leq[code]: "SPAN A \<le> (SPAN B :: 'a::onb_enum clinear_space) 
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

definition [code del, code_abbrev]: "range_cblinfun_code A = A *\<^sub>S top"

lemma ortho_SPAN_code[code_unfold]: "- X = range_cblinfun_code (idOp - Proj X)"
  unfolding range_cblinfun_code_def
  by (metis Proj_ortho_compl imageOp_Proj)

lemma applyOpSpace_SPAN[code]: "applyOpSpace A (SPAN S)
      = (let d = canonical_basis_length TYPE('a) in
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

lemma range_cblinfun_code[code]: 
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
    by (metis dA_def top_as_span)
  also have "\<dots> = SPAN (map (\<lambda>i. mat_of_cblinfun A *\<^sub>v unit_vec dA i) [0..<dA])"
    unfolding applyOpSpace_SPAN dA_def[symmetric] Let_def
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

lemma kernel_SPAN[code]: "kernel A 
    = SPAN (find_base_vectors (gauss_jordan_single (mat_of_cblinfun A)))" 
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

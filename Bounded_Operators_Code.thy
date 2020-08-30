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

(* NEW *)
lemma index_of_length: "index_of x y \<le> length y"
proof(induction y)
  case Nil
  thus ?case by auto
next
  case (Cons a y)
  thus ?case by auto
qed

lemma index_of_bound: 
  assumes "y \<noteq> []" and "x \<in> set y"
  shows "index_of x y < length y"
  using assms proof(induction y arbitrary: x)
  case Nil
  thus ?case by auto
next
  case (Cons a y)
  show ?case 
  proof(cases "a = x")
    case True
    thus ?thesis by auto
  next
    case False
    thus ?thesis apply auto
      using Cons.IH Cons.prems(2) by fastforce
  qed
qed

(* TODO: To preliminaries *)
definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"

(* TODO To preliminaries *)
lemma index_of_correct:
  assumes "x \<in> set y"
  shows "y ! index_of x y = x"
  using assms 
proof(induction y arbitrary: x)
  case Nil
  thus ?case by auto
next
  case (Cons a y)
  thus ?case by auto
qed

(* TODO To preliminaries *)
lemma enum_idx_correct: 
  "Enum.enum ! enum_idx i = i"
proof-
  have "i \<in> set enum_class.enum"
    using UNIV_enum by blast 
  thus ?thesis
    unfolding enum_idx_def
    using index_of_correct by metis
qed

(* TODO: To Bounded_Operators_Matrices *)
lemma vec_of_ell2_ket:
  "vec_of_ell2 (ket i) = unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)" 
  for i::"'a::enum"
proof-
  have "dim_vec (vec_of_ell2 (ket i)) 
      = dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i))"
  proof-
    have "dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) 
      = canonical_basis_length TYPE('a ell2)"
      by simp     
    moreover have "dim_vec (vec_of_ell2 (ket i)) = canonical_basis_length TYPE('a ell2)"
      unfolding vec_of_ell2_def vec_of_onb_enum_def apply auto
      using canonical_basis_length_eq[where 'a = "'a ell2"] by auto
    ultimately show ?thesis by simp
  qed
  moreover have "vec_of_ell2 (ket i) $ j =
    (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) $ j"
    if "j < dim_vec (vec_of_ell2 (ket i))"
    for j
  proof-
    have j_bound: "j < length (canonical_basis::'a ell2 list)"
      by (metis dim_vec_of_onb_enum_list' that vec_of_ell2_def)
    have y1: "complex_independent (set (canonical_basis::'a ell2 list))"
      using canonical_basis_non_zero is_ortho_set_independent is_orthonormal by auto        
    have y2: "canonical_basis ! j \<in> set (canonical_basis::'a ell2 list)"
      using j_bound by auto
    have p1: "enum_class.enum ! enum_idx i = i"
      using enum_idx_correct by blast
    moreover have p2: "(canonical_basis::'a ell2 list) ! t  = ket ((enum_class.enum::'a list) ! t)"
      if "t < length (enum_class.enum::'a list)"
      for t
      unfolding canonical_basis_ell2_def 
      using that by auto
    moreover have p3: "enum_idx i < length (enum_class.enum::'a list)"
    proof-
      have "set (enum_class.enum::'a list) = UNIV"
        using UNIV_enum by blast
      hence "i \<in> set (enum_class.enum::'a list)"
        by blast
      thus ?thesis
        unfolding enum_idx_def
        by (metis index_of_bound length_greater_0_conv length_pos_if_in_set) 
    qed
    ultimately have p4: "(canonical_basis::'a ell2 list) ! (enum_idx i)  = ket i"
      by auto
    have "enum_idx i < length (enum_class.enum::'a list)"
      using p3
      by auto
    moreover have "length (enum_class.enum::'a list) = dim_vec (vec_of_ell2 (ket i))"
      unfolding vec_of_ell2_def canonical_basis_ell2_def
      using dim_vec_of_onb_enum_list'[where v = "ket i"]
      unfolding canonical_basis_ell2_def by simp              
    ultimately have "enum_idx i < dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) 
        (enum_idx i))"
      using \<open>dim_vec (vec_of_ell2 (ket i)) = dim_vec (unit_vec (canonical_basis_length 
        TYPE('a ell2)) (enum_idx i))\<close> by auto            
    hence r1: "(unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) $ j
        = (if enum_idx i = j then 1 else 0)"
      using \<open>dim_vec (vec_of_ell2 (ket i)) = dim_vec (unit_vec (canonical_basis_length 
        TYPE('a ell2)) (enum_idx i))\<close> that by auto
    moreover have "vec_of_ell2 (ket i) $ j = (if enum_idx i = j then 1 else 0)"
    proof(cases "enum_idx i = j")
      case True                        
      have "Complex_Vector_Spaces.representation (set (canonical_basis::'a ell2 list)) 
          ((canonical_basis::'a ell2 list) ! j) ((canonical_basis::'a ell2 list) ! j) = 1"        
        using y1 y2 Complex_Vector_Spaces.representation_basis[where 
            basis = "set (canonical_basis::'a ell2 list)" 
            and b = "(canonical_basis::'a ell2 list) ! j"]
        by (smt ) 

      hence "vec_of_onb_enum ((canonical_basis::'a ell2 list) ! j) $ j = 1"
        unfolding vec_of_onb_enum_def 
        by (metis True \<open>enum_idx i < dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) 
          (enum_idx i))\<close> canonical_basis_length_eq index_unit_vec(3) list_of_vec_index list_vec nth_map)
      hence "vec_of_onb_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) 
            $ enum_idx i = 1"
        using True by simp
      hence "vec_of_onb_enum (ket i) $ enum_idx i = 1"
        using p4
        by simp
      thus ?thesis using True unfolding vec_of_ell2_def by auto
    next
      case False
      have "Complex_Vector_Spaces.representation (set (canonical_basis::'a ell2 list)) 
          ((canonical_basis::'a ell2 list) ! (enum_idx i)) ((canonical_basis::'a ell2 list) ! j) = 0"        
        using y1 y2 Complex_Vector_Spaces.representation_basis[where 
            basis = "set (canonical_basis::'a ell2 list)" 
            and b = "(canonical_basis::'a ell2 list) ! j"]
          False \<open>enum_idx i < dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) 
          (enum_idx i))\<close> canonical_basis_length_eq 
          complex_vector.representation_basis distinct_canonical_basis index_unit_vec(3) 
          j_bound nth_eq_iff_index_eq nth_mem 
        by (metis ) 
      hence "vec_of_onb_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) $ j = 0"
        unfolding vec_of_onb_enum_def by (smt j_bound nth_map vec_of_list_index)        
      hence "vec_of_onb_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) 
            $ j = 0"
        by auto
      hence "vec_of_onb_enum (ket i) $ j = 0"
        using p4
        by simp
      thus ?thesis using False unfolding vec_of_ell2_def by simp
    qed
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis 
    using Matrix.eq_vecI
    by auto
qed

(* TODO: To preliminaries *)
lemma enum_idx_bound: "enum_idx x < length (Enum.enum :: 'a list)" for x :: "'a::enum"
proof-
  have p1: "False"
    if "(Enum.enum :: 'a list) = []"
  proof-
    have "(UNIV::'a set) = set ([]::'a list)"
      using that UNIV_enum by metis
    also have "\<dots> = {}"
      by blast
    finally have "(UNIV::'a set) = {}".
    thus ?thesis by simp
  qed    
  have p2: "x \<in> set (Enum.enum :: 'a list)"
    using UNIV_enum by auto
  show ?thesis
    unfolding enum_idx_def apply (rule Bounded_Operators_Code.index_of_bound[where x = x 
          and y = "(Enum.enum :: 'a list)"])
    using p1 apply auto using p2 by auto
qed

(* TODO: To Bounded_Operators_Matrices *)
lemma vec_of_basis_vector:
  assumes "i < canonical_basis_length TYPE('a)"
  shows "vec_of_onb_enum (canonical_basis!i :: 'a)
       = unit_vec (canonical_basis_length TYPE('a::basis_enum)) i" 
proof-
  have "dim_vec (vec_of_onb_enum (canonical_basis!i :: 'a)) 
      = dim_vec (unit_vec (canonical_basis_length TYPE('a)) i)"
  proof-
    have "dim_vec (unit_vec (canonical_basis_length TYPE('a)) i) 
      = canonical_basis_length TYPE('a)"
      by simp     
    moreover have "dim_vec (vec_of_onb_enum (canonical_basis!i :: 'a)) 
        = canonical_basis_length TYPE('a)"
      unfolding vec_of_ell2_def vec_of_onb_enum_def apply auto
      using canonical_basis_length_eq[where 'a = "'a"] by auto
    ultimately show ?thesis by simp
  qed
  moreover have "vec_of_onb_enum (canonical_basis!i :: 'a) $ j =
    (unit_vec (canonical_basis_length TYPE('a)) i) $ j"
    if "j < dim_vec (vec_of_onb_enum (canonical_basis!i::'a))"
    for j
  proof-
    have j_bound: "j < length (canonical_basis::'a list)"
      by (metis dim_vec_of_onb_enum_list' that)
    have y1: "complex_independent (set (canonical_basis::'a list))"
      by (simp add: is_complex_independent_set)              
    have y2: "canonical_basis ! j \<in> set (canonical_basis::'a list)"
      using j_bound by auto    
    have "i < dim_vec (unit_vec (canonical_basis_length TYPE('a)) i)"
      by (simp add: assms)
    hence r1: "(unit_vec (canonical_basis_length TYPE('a)) i) $ j
        = (if i = j then 1 else 0)"
      by (simp add: canonical_basis_length_eq j_bound)
    have r2: "vec_of_onb_enum ((canonical_basis::'a list) ! i) $ j = (if i = j then 1 else 0)"
    proof(cases "i = j")
      case True
      have "\<not> Complex_Vector_Spaces.dependent (set (canonical_basis::'a list))"
        using is_complex_independent_set
        by (simp add: )       
      moreover have "canonical_basis ! i \<in> set (canonical_basis::'a list)"
        by (simp add: True y2)        
      ultimately have "(Complex_Vector_Spaces.representation
            (set (canonical_basis::'a list)) ((canonical_basis::'a list) ! i)) 
          ((canonical_basis::'a list) ! i) = 1"       
        using Complex_Vector_Spaces.representation_basis[where basis = "set (canonical_basis::'a list)" 
            and b = "(canonical_basis::'a list)!i"] by simp
      hence "vec_of_onb_enum ((canonical_basis::'a list) ! i) $ j = 1"
        unfolding vec_of_onb_enum_def using True by (smt j_bound nth_map vec_of_list_index)
      thus ?thesis using True by simp
    next
      case False
      have "\<not> Complex_Vector_Spaces.dependent (set (canonical_basis::'a list))"
        using is_complex_independent_set
        by (simp add: )     
      moreover have "canonical_basis ! j \<in> set (canonical_basis::'a list)"
        by (simp add: y2)
      ultimately have "(Complex_Vector_Spaces.representation
            (set (canonical_basis::'a list)) ((canonical_basis::'a list) ! i)) 
          ((canonical_basis::'a list) ! j) = 0"       
        using Complex_Vector_Spaces.representation_basis[where basis = 
            "set (canonical_basis::'a list)" 
            and b = "(canonical_basis::'a list)!i"] False 
        by (smt assms canonical_basis_length_eq distinct_canonical_basis j_bound nth_eq_iff_index_eq 
            nth_mem) 
      hence "vec_of_onb_enum ((canonical_basis::'a list) ! i) $ j = 0"
        unfolding vec_of_onb_enum_def using False by (smt j_bound nth_map vec_of_list_index)
      thus ?thesis using False by simp
    qed
    show ?thesis using r1 r2 by auto
  qed
  ultimately show ?thesis 
    using Matrix.eq_vecI
    by auto
qed


(* TODO: To Bounded_Operators_Matrices *)
lemma ket_canonical_basis: "ket x = canonical_basis ! enum_idx x"  
proof-
  have "x = (enum_class.enum::'a list) ! enum_idx x"
    using Bounded_Operators_Code.enum_idx_correct[where i = x] by simp
  hence p1: "ket x = ket ((enum_class.enum::'a list) ! enum_idx x)"
    by simp
  have "enum_idx x < length (enum_class.enum::'a list)"
    using Bounded_Operators_Code.enum_idx_bound[where x = x].
  hence "(map ket (enum_class.enum::'a list)) ! enum_idx x 
        = ket ((enum_class.enum::'a list) ! enum_idx x)"
    by auto      
  thus ?thesis
    unfolding canonical_basis_ell2_def using p1 by auto    
qed

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

lemma cinner_ell2_code [code]: "cinner \<psi> \<phi> = cscalar_prod (vec_of_ell2 \<phi>) (vec_of_ell2 \<psi>)"
  by (simp add: cinner_ell2_code vec_of_ell2_def)

lemma norm_ell2_code [code]: "norm \<psi> = 
  (let \<psi>' = vec_of_ell2 \<psi> in
    sqrt (\<Sum> i \<in> {0 ..< dim_vec \<psi>'}. let z = vec_index \<psi>' i in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
  by (simp add: norm_ell2_code vec_of_ell2_def)

(* NEW *)
lemma complex_span_singleton:
  fixes x y::"'a::complex_vector"
  assumes a1: "x \<in> complex_span {y}"
  shows "\<exists>\<alpha>. x = \<alpha> *\<^sub>C y"
proof-
  have "\<exists>t r. x = (\<Sum>j\<in>t. r j *\<^sub>C j) \<and> finite t \<and> t \<subseteq> {y}"
    using a1 using complex_vector.span_explicit[where b = "{y}"]
    by (smt  mem_Collect_eq)
  then obtain t r where b1: "x = (\<Sum>j\<in>t. r j *\<^sub>C j)" and b2: "finite t" and b3: "t \<subseteq> {y}"
    by blast
  show ?thesis
  proof(cases "t = {}")
    case True
    hence "(\<Sum>j\<in>t. r j *\<^sub>C j) = 0"
      using b2
      by simp
    thus ?thesis using b1 by simp
  next
    case False
    hence "t = {y}"
      using b3 by auto
    moreover have "(\<Sum>j\<in>{y}. r j *\<^sub>C j) = r y *\<^sub>C y"
      by auto
    ultimately show  ?thesis using b1 by blast
  qed

qed

(* TODO move to ..._Matrices *)
(* TODO better name *)
lemma times_ell2_code: 
  fixes \<psi> \<phi> :: "'a::{CARD_1,enum} ell2"
  shows "vec_of_ell2 (\<psi> * \<phi>)
   = vec_of_list [vec_index (vec_of_ell2 \<psi>) 0 * vec_index (vec_of_ell2 \<phi>) 0]"
proof-
  have "\<exists>i. i\<in>(UNIV::'a set)"
    by blast
  then obtain i where i_def: "i\<in>(UNIV::'a set)"
    by blast
  have "set (enum_class.enum::'a list) = UNIV"
    using UNIV_enum by blast
  moreover have "card (UNIV::'a set) = 1"
    by (simp add: CARD_1)      
  moreover have "distinct (enum_class.enum::'a list)"
    using enum_distinct by auto
  ultimately have "length (enum_class.enum::'a list) = 1"
    by (metis One_nat_def UNIV_witness \<open>\<exists>i. i \<in> UNIV\<close> card_num1 class_semiring.one_closed
        length_remdups_card_conv plus_1_eq_Suc remdups_id_iff_distinct top.extremum_unique)      
  hence p0: "length (canonical_basis::'a ell2 list) = 1"
    unfolding canonical_basis_ell2_def by simp
  hence q1: "canonical_basis_length TYPE('a ell2) = 1"
    using canonical_basis_length_eq[where 'a = "'a ell2"] by simp
  have "vec_of_ell2 f = vec_of_list [vec_of_ell2 f $ 0]"
    for f::"'a ell2" 
  proof-
    have p1: "dim_vec (vec_of_ell2 f) = 1"
      using p0
      unfolding vec_of_ell2_def vec_of_onb_enum_def
      by auto
    have "(vec_of_ell2 f) $ k = vec_of_list [vec_of_ell2 f $ 0] $ k"
      if "k < dim_vec (vec_of_ell2 f)"
      for k
    proof-
      have "k = 0"
        using that p1 by auto
      moreover have "vec_of_list [vec_of_ell2 f $ 0] $ 0 = vec_of_ell2 f $ 0"
        by simp        
      ultimately show ?thesis by simp
    qed
    moreover have "dim_vec (vec_of_list [vec_of_ell2 f $ 0]) = 1"
    proof-
      have "length [vec_of_ell2 f $ 0] = 1"
        by simp
      thus ?thesis
        by simp 
    qed
    ultimately show ?thesis
      by (metis eq_vecI p1) 
  qed
  hence "vec_of_ell2 (\<psi> * \<phi>) = vec_of_list [vec_of_ell2 (\<psi> * \<phi>) $ 0]"
    by blast
  also have "\<dots> = vec_of_list [vec_of_ell2 \<psi> $ 0 * vec_of_ell2 \<phi> $ 0]"
  proof-
    have "Rep_ell2 (\<psi> * \<phi>) i = Rep_ell2 \<psi> i * Rep_ell2 \<phi> i"
      by (simp add: times_ell2.rep_eq)
    moreover have "vec_of_ell2 x $ 0 = Rep_ell2 x i"
      for x
    proof-
      have "(UNIV::'a set) = {i}"
        using CARD_1[where 'a = 'a] i_def by auto
      hence t1: "set (enum_class.enum::'a list) = {i}"
        using UNIV_enum by auto
      hence s0: "(enum_class.enum::'a list)!0 = i"
        by auto
      have "card (set (enum_class.enum::'a list)) = 1"
        using t1 by simp
      hence "length (enum_class.enum::'a list) = 1"
        using enum_distinct List.distinct_card by smt
      hence "(enum_class.enum::'a list) = [i]"
        by (metis s0 One_nat_def length_0_conv length_Suc_conv length_nth_simps(3))                    
      hence "map ket (enum_class.enum::'a list) = [ket i]"
        by (metis list.simps(8) list.simps(9))          
      hence "(map ket (enum_class.enum::'a list)) ! 0 = ket i"
        by simp
      hence ket_canonical_basis: "(canonical_basis::'a ell2 list)!0 = ket i"
        unfolding canonical_basis_ell2_def.
      have x_ket: "x = Rep_ell2 x i *\<^sub>C ket i"
      proof-
        have "x \<in> complex_span (range ket)"
          using finite_class.finite_UNIV finite_imageI ket_ell2_span span_finite_dim
          by (metis  iso_tuple_UNIV_I) 

        moreover have "range (ket::'a \<Rightarrow>_) = {ket i}"
          by (simp add: \<open>UNIV = {i}\<close>)
        ultimately have "x \<in> complex_span {ket i}"
          by simp
        hence "\<exists>\<alpha>. x = \<alpha> *\<^sub>C ket i"
          using complex_span_singleton by blast
        then obtain \<alpha> where "x = \<alpha> *\<^sub>C ket i"
          by blast
        hence "(Rep_ell2 x) i = (Rep_ell2 (\<alpha> *\<^sub>C ket i)) i"
          by simp
        moreover have "(Rep_ell2 (\<alpha> *\<^sub>C ket i)) i = \<alpha>"
          apply transfer
          by simp
        ultimately show ?thesis
          by (simp add: \<open>x = \<alpha> *\<^sub>C ket i\<close>) 
      qed
      have "x = Rep_ell2 x i *\<^sub>C (canonical_basis::'a ell2 list)!0"
        using i_def x_ket ket_canonical_basis by simp
      hence "vec_of_ell2 x = vec_of_ell2 (Rep_ell2 x i *\<^sub>C (canonical_basis::'a ell2 list)!0)"
        by simp
      also have "\<dots> = Rep_ell2 x i \<cdot>\<^sub>v vec_of_ell2 ((canonical_basis::'a ell2 list)!0)"
        by (simp add: vec_of_ell2_timesScalarVec)
      also have "\<dots> = Rep_ell2 x i \<cdot>\<^sub>v unit_vec (canonical_basis_length TYPE('a ell2)) 0"
        by (simp add: canonical_basis_length_ell2_def vec_of_basis_vector vec_of_ell2_def)
      finally have "vec_of_ell2 x
         = Rep_ell2 x i \<cdot>\<^sub>v unit_vec (canonical_basis_length TYPE('a ell2)) 0".
      hence "vec_of_ell2 x $ 0
         = (Rep_ell2 x i \<cdot>\<^sub>v unit_vec (canonical_basis_length TYPE('a ell2)) 0) $ 0"
        by simp
      also have "\<dots> = Rep_ell2 x i * ((unit_vec (canonical_basis_length TYPE('a ell2)) 0) $ 0)"
        by (simp add: canonical_basis_length_ell2_def)
      also have "\<dots> = Rep_ell2 x i"
      proof-
        have "(unit_vec (canonical_basis_length TYPE('a ell2)) 0) $ 0 = 1"
          using q1
          by auto
        thus ?thesis by auto
      qed
      finally show ?thesis.
    qed  
    ultimately have "vec_of_ell2 (\<psi> * \<phi>) $ 0 = vec_of_ell2 \<psi> $ 0 * vec_of_ell2 \<phi> $ 0"
      by auto
    thus ?thesis by simp
  qed
  finally show "vec_of_ell2 (\<psi> * \<phi>) =
        vec_of_list [vec_of_ell2 \<psi> $ 0 * vec_of_ell2 \<phi> $ 0]".
qed

declare times_ell2_code[code]

(* TODO move to ..._Matrices *)
(* TODO better name *)
lemma one_ell2_code: "vec_of_ell2 (1 :: 'a::{CARD_1,enum} ell2) = vec_of_list [1]"
proof-
  have "\<exists>i. i\<in>(UNIV::'a set)"
    by blast
  then obtain i where i_def: "i\<in>(UNIV::'a set)"
    by blast
  have "set (enum_class.enum::'a list) = UNIV"
    using UNIV_enum by blast
  moreover have "card (UNIV::'a set) = 1"
    by (simp add: CARD_1)      
  moreover have "distinct (enum_class.enum::'a list)"
    using enum_distinct by auto
  ultimately have "length (enum_class.enum::'a list) = 1"
    by (metis One_nat_def UNIV_witness \<open>\<exists>i. i \<in> UNIV\<close> card_num1 class_semiring.one_closed
        length_remdups_card_conv plus_1_eq_Suc remdups_id_iff_distinct top.extremum_unique)      
  hence p0: "length (canonical_basis::'a ell2 list) = 1"
    unfolding canonical_basis_ell2_def by simp
  have w1: "vec_of_ell2 f = vec_of_list [vec_of_ell2 f $ 0]"
    for f::"'a ell2" 
  proof-
    have p1: "dim_vec (vec_of_ell2 f) = 1"
      using p0 
      unfolding vec_of_ell2_def vec_of_onb_enum_def
      by auto
    have "(vec_of_ell2 f) $ k = vec_of_list [vec_of_ell2 f $ 0] $ k"
      if "k < dim_vec (vec_of_ell2 f)"
      for k
    proof-
      have "k = 0"
        using that p1 by auto
      moreover have "vec_of_list [vec_of_ell2 f $ 0] $ 0 = vec_of_ell2 f $ 0"
        by simp        
      ultimately show ?thesis by simp
    qed
    moreover have "dim_vec (vec_of_list [vec_of_ell2 f $ 0]) = 1"
    proof-
      have "length [vec_of_ell2 f $ 0] = 1"
        by simp
      thus ?thesis
        by simp 
    qed
    ultimately show ?thesis
      by (metis eq_vecI p1) 
  qed
  have "(Complex_Vector_Spaces.representation (set (canonical_basis::'a ell2 list)) 1) 
        ((canonical_basis::'a ell2 list)!0) = 1"
    by (simp add: complex_vector.representation_basis one_dim_canonical_basis)    
  hence "vec_of_ell2 (1 :: 'a::{CARD_1,enum} ell2) $ 0 = 1"
    unfolding vec_of_ell2_def vec_of_onb_enum_def vec_of_list_def id_def
    apply auto
    by (metis class_field.zero_not_one complex_vector.representation_ne_zero length_map 
        length_pos_if_in_set nth_map vec_of_list.abs_eq vec_of_list_index)
  thus ?thesis using w1[where f = "(1 :: 'a::{CARD_1,enum} ell2)"] by simp
qed


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
  "mat_of_cblinfun (vector_to_cblinfun \<psi>)
 = mat_of_cols (canonical_basis_length TYPE('a)) [vec_of_onb_enum \<psi>]"
  for \<psi>::"'a::onb_enum"  
proof-
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"
  have "nB = 1"
    unfolding nB_def 
    using one_dim_canonical_basis canonical_basis_length_eq
    apply auto
    by (simp add: canonical_basis_length_eq one_dim_canonical_basis)
  hence carrier_mat1: "mat_of_cols nA [vec_of_onb_enum \<psi>] \<in> carrier_mat nA nB"
    using mat_of_cols_carrier[where n = nA and vs = "[vec_of_onb_enum \<psi>]"]
    unfolding nA_def nB_def 
    by auto
  have t1: "mat_of_cols nA [vec_of_onb_enum \<psi>] \<in> carrier_mat nA nB"
    unfolding nA_def nB_def
    using carrier_mat1 nA_def nB_def by auto 
  have "one_dim_to_complex x *\<^sub>C \<psi> = (onb_enum_of_vec (mat_of_cols nA [vec_of_onb_enum \<psi>]
        *\<^sub>v vec_of_onb_enum x)::'a)"
    for x::'b
    using nA_def
  proof transfer
    fix x::'b and \<psi>::'a and nA::nat
    assume nA_def': "nA = canonical_basis_length TYPE('a)"
    have "length (canonical_basis::'b list) = 1"
      using one_dim_canonical_basis[where 'a = 'b]
      by (metis One_nat_def length_nth_simps(1) length_nth_simps(2)) 
    hence dim_vec_b: "dim_vec (vec_of_onb_enum x) = 1"
      by (simp add: dim_vec_of_onb_enum_list')            
    have "mat_of_cols nA [vec_of_onb_enum \<psi>] *\<^sub>v vec_of_onb_enum x
        = vec nA
     (\<lambda>i. scalar_prod (row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i) (vec_of_onb_enum x))"
      unfolding mult_mat_vec_def by auto
    also have "\<dots> = vec nA
     (\<lambda>i. \<Sum>j = 0..<1.
      row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i $ j * vec_of_onb_enum x $ j)"
      unfolding scalar_prod_def using dim_vec_b by auto
    also have "\<dots> = vec nA
     (\<lambda>i. \<Sum>j\<in>{0}.
      row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i $ j * vec_of_onb_enum x $ j)"
      by auto
    also have "\<dots> = vec nA
     (\<lambda>i. row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i $ 0 * vec_of_onb_enum x $ 0)"
      using VS_Connect.class_semiring.finsum_singleton_set by auto
    also have "\<dots> = vec nA
     (\<lambda>i. row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i $ 0 * one_dim_to_complex x)"
    proof-
      have "x = one_dim_to_complex x *\<^sub>C 1"
        by (simp add: one_dim_1_times_a_eq_a one_dim_to_complex_def)
      hence "vec_of_onb_enum x = vec_of_onb_enum (one_dim_to_complex x *\<^sub>C (1::'b))"
        by simp
      also have "\<dots> = one_dim_to_complex x \<cdot>\<^sub>v (vec_of_onb_enum (1::'b))"
        by (simp add: vec_of_onb_enum_scaleC)
      finally have "vec_of_onb_enum x = one_dim_to_complex x \<cdot>\<^sub>v (vec_of_onb_enum (1::'b))".
      hence "(vec_of_onb_enum x)$0 = (one_dim_to_complex x \<cdot>\<^sub>v (vec_of_onb_enum (1::'b)))$0"
        by auto
      also have "\<dots> = one_dim_to_complex x * ((vec_of_onb_enum (1::'b))$0)"
        using \<open>vec_of_onb_enum x = one_dim_to_complex x \<cdot>\<^sub>v vec_of_onb_enum 1\<close> dim_vec_b by auto
      also have "\<dots> = one_dim_to_complex x"
      proof-
        have "Complex_Vector_Spaces.representation
         (set (canonical_basis::'b list)) 1 ((canonical_basis::'b list)!0) = 1"
          by (simp add: complex_vector.representation_basis one_dim_canonical_basis)          
        hence "(vec_of_onb_enum (1::'b))$0 = 1"
          unfolding vec_of_onb_enum_def apply auto
          by (simp add: one_dim_canonical_basis) 
        thus ?thesis by simp
      qed
      finally have "vec_of_onb_enum x $ 0 = one_dim_to_complex x".
      thus ?thesis 
        unfolding one_dim_to_complex_def 
        by simp
    qed
    also have "\<dots> = vec nA
     (\<lambda>i. one_dim_to_complex x * (row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i) $ 0 )"
      by auto
    also have "\<dots> = vec nA
     (\<lambda>i. (one_dim_to_complex x \<cdot>\<^sub>v ( row (mat_of_cols nA [vec_of_onb_enum \<psi>]) i) ) $ 0 )"
      by auto
    also have "\<dots> = vec nA
     (\<lambda>i. ( row (one_dim_to_complex x \<cdot>\<^sub>m mat_of_cols nA [vec_of_onb_enum \<psi>]) i) $ 0 )"
      by auto
    also have "\<dots> = vec nA
     (\<lambda>i. ( row (mat_of_cols nA [one_dim_to_complex x \<cdot>\<^sub>v vec_of_onb_enum \<psi>]) i) $ 0 )"
    proof-
      have sss: "a \<cdot>\<^sub>m mat_of_cols nA [y] = mat_of_cols nA [a \<cdot>\<^sub>v y]"
        if "dim_vec y = nA"
        for a and y::"complex vec"
      proof-
        have "(a \<cdot>\<^sub>m mat_of_cols nA [y]) $$ (i,j) = (mat_of_cols nA [a \<cdot>\<^sub>v y]) $$ (i,j)"
          if "i < dim_row (mat_of_cols nA [y])" and "j < dim_col (mat_of_cols nA [y])"
          for i j
          using that Matrix.index_smult_mat(1)[where i = i and j = j and a = a 
              and A = "mat_of_cols nA [y]"] apply auto
          by (simp add: \<open>dim_vec y = nA\<close> mat_of_cols_Cons_index_0)          
        thus ?thesis
          by auto
      qed
      have "dim_vec (vec_of_onb_enum \<psi>) = nA"
        by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list' nA_def')
      thus ?thesis
        using sss[where a = "one_dim_to_complex x" and y = "vec_of_onb_enum \<psi>"]
        by auto
    qed
    also have "\<dots> = vec nA
     (\<lambda>i. ( row (mat_of_cols nA [vec_of_onb_enum (one_dim_to_complex x *\<^sub>C \<psi>)]) i) $ 0 )"
      by (simp add: vec_of_onb_enum_scaleC)
    also have "\<dots> = vec_of_onb_enum (one_dim_to_complex x *\<^sub>C \<psi>)"
    proof-
      have ll: "vec nA (\<lambda>i. ( row (mat_of_cols nA [y]) i) $ 0 ) = y"
        if "dim_vec y = nA"
        for y::"complex vec"
      proof-
        have "vec nA (\<lambda>i. ( row (mat_of_cols nA [y]) i) $ 0 ) $ j = y $ j"
          if "j < dim_vec y"
          for j
        proof-
          have "vec nA (\<lambda>i. ( row (mat_of_cols nA [y]) i) $ 0 ) $ j
              = (row (mat_of_cols nA [y]) j) $ 0"
            using \<open>dim_vec y = nA\<close> index_vec that by blast            
          also have "\<dots> = y $ j"
            unfolding row_def apply auto unfolding mat_of_cols_def apply auto
            using \<open>dim_vec y = nA\<close> that by auto
          finally show ?thesis.
        qed
        thus ?thesis
          using dim_vec that by blast 
      qed
      have "dim_vec (vec_of_onb_enum (one_dim_to_complex (x::'b::one_dim) *\<^sub>C (\<psi>::'a::onb_enum))) 
            = (nA::nat)"
        by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list' nA_def')
      thus ?thesis using ll[where y = "vec_of_onb_enum (one_dim_to_complex x *\<^sub>C \<psi>)"]
        by blast
    qed
    finally have "mat_of_cols nA [vec_of_onb_enum \<psi>] *\<^sub>v vec_of_onb_enum x = 
              vec_of_onb_enum (one_dim_to_complex x *\<^sub>C \<psi>)". 
    thus "one_dim_to_complex x *\<^sub>C \<psi> =
          onb_enum_of_vec (mat_of_cols nA [vec_of_onb_enum \<psi>] *\<^sub>v vec_of_onb_enum x)" 
      by simp
  qed
  hence  "((vector_to_cblinfun \<psi>)::'b\<Rightarrow>\<^sub>C\<^sub>L'a) *\<^sub>V x
       = ((cblinfun_of_mat (mat_of_cols nA [vec_of_onb_enum \<psi>]))::'b\<Rightarrow>\<^sub>C\<^sub>L'a) *\<^sub>V x"
    for x
    using t1 
    unfolding nA_def nB_def apply auto
    by (simp add: cblinfun_of_mat.rep_eq)
  hence  "((vector_to_cblinfun \<psi>)::'b\<Rightarrow>\<^sub>C\<^sub>L'a)
       = ((cblinfun_of_mat (mat_of_cols nA [vec_of_onb_enum \<psi>]))::'b\<Rightarrow>\<^sub>C\<^sub>L'a)"
    using cblinfun_ext by blast        
  hence  "mat_of_cblinfun ((vector_to_cblinfun \<psi>)::'b\<Rightarrow>\<^sub>C\<^sub>L'a)
       = mat_of_cblinfun ((cblinfun_of_mat (mat_of_cols nA [vec_of_onb_enum \<psi>]))::'b\<Rightarrow>\<^sub>C\<^sub>L'a)"
    using [[show_sorts]]    
    by simp
  also have "mat_of_cblinfun
   (cblinfun_of_mat (mat_of_cols nA [vec_of_onb_enum \<psi>]) :: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a) =
                     mat_of_cols nA [vec_of_onb_enum \<psi>]"
    apply (rule cblinfun_of_mat_inverse[where 'a = 'b and 'b = 'a
          and M = "mat_of_cols nA [vec_of_onb_enum \<psi>]" and nA = nB and nB = nA])
    using carrier_mat1 nA_def nB_def by auto
  finally show ?thesis 
    unfolding nA_def by auto
qed

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


(* NEW *)
lemma Span_insert:
  assumes "finite (S::'a'::complex_inner set)"
  shows "space_as_set (Span (insert a S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> space_as_set (Span S)}"
proof -
  have "closure (complex_span (insert a S)) = complex_span (insert a S)"
    by (metis assms finite_insert span_finite_dim)
  thus ?thesis
    by (simp add: Span.rep_eq assms complex_vector.span_insert span_finite_dim)
qed

(* NEW *)
lemma closed_subspace_complex_span_finite:
  assumes "finite (S::'a::chilbert_space set)"
  shows "closed_subspace (complex_span S)"
  unfolding closed_subspace_def apply auto
  by (simp add: assms closed_finite_dim)

(* NEW *)
lemma projection_singleton:
  assumes "(a::'a::chilbert_space) \<noteq> 0"
  shows "projection (complex_span {a}) u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
proof-
  define p where "p u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a" for u
  define M where "M = complex_span {a}"
  have "closed_subspace M"
    unfolding M_def 
    using closed_subspace_complex_span_finite
    by (simp add: closed_subspace_complex_span_finite)
  moreover have "u - p u \<in> orthogonal_complement M"
    unfolding p_def M_def orthogonal_complement_def
  proof auto
    fix y
    assume "y \<in> complex_span {a}" 
    hence "\<exists>c. y = c *\<^sub>C a"
      by (simp add: complex_span_singleton)
    then obtain c where c_def: "y = c *\<^sub>C a"
      by blast
    have "\<langle>u - (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, c *\<^sub>C a\<rangle> = 
          \<langle>u, c *\<^sub>C a\<rangle> - \<langle>(\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, c *\<^sub>C a\<rangle>"
      using cinner_diff_left by blast    
    also have "\<dots> = 0"
      by simp
    finally have "\<langle>u - (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, c *\<^sub>C a\<rangle> = 0".
    thus "\<langle>u - (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a, y\<rangle> = 0"
      using c_def by simp
  qed
  moreover have "p u \<in> M"
    unfolding p_def M_def
    by (simp add: complex_vector.span_base complex_vector.span_scale)
  ultimately have "projection M u = p u"
    using projection_uniq[where x = "p u" and h = u and M = M] by blast
  thus ?thesis unfolding M_def p_def.
qed

(* NEW *)
lemma ortho_complex_span:
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> \<langle>a, s\<rangle> = 0" and a2: "finite (S::'a::chilbert_space set)"
    and a3: "x \<in> complex_span S"
  shows "\<langle>a, x\<rangle> = 0"
proof-
  have "\<exists>t r. finite t \<and> t \<subseteq> S \<and> (\<Sum>a\<in>t. r a *\<^sub>C a) = x"
    using complex_vector.span_explicit
    by (smt a3 mem_Collect_eq)
  then obtain t r where b1: "finite t" and b2: "t \<subseteq> S" and b3: "(\<Sum>a\<in>t. r a *\<^sub>C a) = x"
    by blast
  have x1: "\<langle>a, i\<rangle> = 0"
    if "i\<in>t" for i
    using b2 a1 that by blast
  have  "\<langle>a, x\<rangle> = \<langle>a, (\<Sum>i\<in>t. r i *\<^sub>C i)\<rangle>"
    by (simp add: b3) 
  also have  "\<dots> = (\<Sum>i\<in>t. r i *\<^sub>C \<langle>a, i\<rangle>)"
    by (simp add: cinner_sum_right)
  also have  "\<dots> = 0"
    using x1 by simp
  finally show ?thesis.
qed

(* NEW *)
lemma projection_insert:
  assumes a1: "\<And>s. s \<in> S \<Longrightarrow> \<langle>a, s\<rangle> = 0" and a2: "finite (S::'a::chilbert_space set)"
  shows "projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span S} u
        = projection (complex_span {a}) u
        + projection (complex_span S) u"
proof-
  define p where "p u = projection (complex_span {a}) u
                      + projection (complex_span S) u" for u
  define M where "M = {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span S}"
  have "projection (complex_span {a}) u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
    by (metis complex_vector.scale_zero_right complex_vector.span_empty complex_vector.span_insert_0 
        projection_singleton projection_zero_subspace)
  have "closed_subspace M"
    unfolding M_def
    by (metis (no_types) a2 closed_subspace_complex_span_finite complex_vector.span_insert 
        finite_insert) 
  moreover have "p u \<in> M"
    unfolding p_def M_def 
  proof auto 
    define k where "k = \<langle>a, u\<rangle>/\<langle>a, a\<rangle>"
    have "projection (complex_span {a}) u = (\<langle>a, u\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
      by (simp add: \<open>projection (complex_span {a}) u = (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a\<close>)      
    hence "projection (complex_span {a}) u +
          projection (complex_span S) u - k *\<^sub>C a
          \<in> complex_span S"
      unfolding k_def
      by (simp add: a2 closed_subspace_complex_span_finite projection_intro2)      
    thus "\<exists>k. projection (complex_span {a}) u +
              projection (complex_span S) u - k *\<^sub>C a
              \<in> complex_span S"
      by blast
  qed
  moreover have "u - p u \<in> orthogonal_complement M"
    unfolding orthogonal_complement_def
  proof auto
    fix y
    assume b1: "y \<in> M"
    hence "\<exists>k. y - k *\<^sub>C a \<in> complex_span S"
      unfolding M_def by simp
    then obtain k where k_def: "y - k *\<^sub>C a \<in> complex_span S"
      by blast
    have "u - projection (complex_span S) u \<in> orthogonal_complement (complex_span S)"
      by (simp add: a2 closed_subspace_complex_span_finite projection_intro1)
    moreover have "projection (complex_span {a}) u \<in> orthogonal_complement (complex_span S)"
      unfolding orthogonal_complement_def
    proof auto
      fix y
      assume "y \<in> complex_span S"
      have "\<langle>a, y\<rangle> = 0"
        using ortho_complex_span
          \<open>y \<in> complex_span S\<close> a1 a2 by auto
      thus "\<langle>projection (complex_span {a}) u, y\<rangle> = 0"
        by (simp add: \<open>projection (complex_span {a}) u = (\<langle>a, u\<rangle> / \<langle>a, a\<rangle>) *\<^sub>C a\<close>)         
    qed
    ultimately have "(u - projection (complex_span S) u)
                    - projection (complex_span {a}) u \<in> orthogonal_complement (complex_span S)"
      using Complex_Vector_Spaces.complex_vector.span_diff
      by (smt cinner_diff_left diff_zero orthogonal_complement_D1 orthogonal_complement_I2)
    hence "u - projection (complex_span {a}) u 
            - projection (complex_span S) u \<in> orthogonal_complement (complex_span S)"
      by (simp add: cancel_ab_semigroup_add_class.diff_right_commute)
    have "\<langle>u - projection (complex_span {a}) u 
         - projection (complex_span S) u, y - k *\<^sub>C a\<rangle> = 0"
      using \<open>u - projection (complex_span {a}) u - projection (complex_span S) u \<in> 
        orthogonal_complement (complex_span S)\<close> k_def orthogonal_complement_D1 by auto      
    moreover have "\<langle>u - projection (complex_span {a}) u 
         - projection (complex_span S) u, k *\<^sub>C a\<rangle> = 0"
    proof-
      have "u - projection (complex_span {a}) u \<in> orthogonal_complement (complex_span {a})"
        by (simp add: closed_subspace_complex_span_finite projection_intro1)
      moreover have "projection (complex_span S) u \<in> orthogonal_complement (complex_span {a})"
        unfolding orthogonal_complement_def
      proof auto
        fix y
        assume "y \<in> complex_span {a}"
        hence "\<exists>k. y = k *\<^sub>C a"
          by (simp add: complex_span_singleton)
        then obtain k where ky:"y = k *\<^sub>C a"
          by blast
        have "projection (complex_span S) u \<in> complex_span S"
          by (simp add: a2 closed_subspace_complex_span_finite projection_intro2)          
        hence "\<langle>projection (complex_span S) u, a\<rangle> = 0"
          by (meson a1 a2 ortho_complex_span orthogonal_complement_D2 orthogonal_complement_I2)          
        thus "\<langle>projection (complex_span S) u, y\<rangle> = 0"
          using ky
          by simp
      qed
      moreover have "complex_vector.subspace ( orthogonal_complement (complex_span {a}))"
        by (simp add: closed_subspace.subspace closed_subspace_complex_span_finite)

      ultimately have "(u - projection (complex_span {a}) u) - projection (complex_span S) u
                   \<in> orthogonal_complement (complex_span {a})"
        by (smt complex_vector.subspace_diff)
      thus ?thesis
        using complex_vector.span_base orthogonal_complement_D1 by fastforce 
    qed
    ultimately have "\<langle>u - projection (complex_span {a}) u 
         - projection (complex_span S) u, y\<rangle> = 0"
      by (metis cinner_right_distrib class_semiring.add.l_one 
          class_semiring.add.one_closed diff_add_cancel)      
    moreover have "\<langle>u - p u, y\<rangle> =
      \<langle>u - projection (complex_span {a}) u 
         - projection (complex_span S) u, y\<rangle>"
      unfolding p_def
      by (simp add: diff_diff_add) 
    ultimately show "\<langle>u - p u, y\<rangle> = 0" by simp
  qed
  ultimately have "projection M u = p u"
    using projection_uniq[where x = "p u" and h = u and M = M] by blast
  thus ?thesis 
    unfolding p_def M_def by auto
qed

(* NEW *)
lemma Proj_Span_insert:
  fixes S :: "'a::{onb_enum, chilbert_space} list"
    and a::'a 
  assumes a1: "is_ortho_set (set (a#S))" and a2: "distinct (a#S)"
  shows "Proj (Span (set (a#S))) = Proj (Span {a}) + Proj (Span (set S))"
proof-
  define d where "d = canonical_basis_length TYPE('a)"
  hence IH': "is_ortho_set (set S)"
    using assms is_onb_delete by auto    
  have IH0: "distinct S"
    using a2 by auto   
  have "closure (complex_span (set S)) = complex_span (set S)"
    by (simp add: span_finite_dim)    
  have "complex_span (insert a (set S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}"
    using complex_vector.span_insert[where a = a and S = "(set S)"].
  moreover have "finite (insert a (set S))"
    by simp    
  ultimately have "closure (complex_span (insert a (set S))) = 
        complex_span {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}"
    by (metis complex_vector.span_span span_finite_dim)
  hence s2: "space_as_set (Abs_clinear_space (closure (complex_span (insert a (set S))))) 
        = complex_span {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}"
    by (metis Span.rep_eq space_as_set_inverse)
  have "closure (complex_span (set S)) = complex_span (set S)"
    by (simp add: span_finite_dim)    
  have ios: "is_ortho_set (set S)"
    by (simp add: IH')    
  have aS: "a \<notin> set S"
    using a2 by auto
  have "projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)} u
        = projection (complex_span {a}) u
        + projection (complex_span (set S)) u"
    for u   
    apply(rule projection_insert)
    using ios unfolding is_ortho_set_def apply auto
    using aS
    by (metis a1 insertCI is_ortho_set_def list.simps(15))
  have s1: "projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)} u
        = projection (complex_span {a}) u + projection (complex_span (set S)) u"
    for u
    by (simp add: \<open>\<And>u. projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)} u
     = projection (complex_span {a}) u + projection (complex_span (set S)) u\<close>)
  have "Proj (Span (set (a#S))) = cBlinfun (projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)})"
    unfolding Proj_def Span_def id_def apply auto
    by (metis \<open>complex_span (insert a (set S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}\<close> 
        complex_vector.span_span s2)
  also have "\<dots> = (cBlinfun (\<lambda>u. projection (complex_span {a}) u
                   + projection (complex_span (set S)) u))"
    using s1
    by presburger 
  also have "\<dots> = cBlinfun (\<lambda>u. projection (complex_span {a}) u)
               +  cBlinfun (\<lambda>u. projection (complex_span (set S)) u)"
    unfolding plus_cblinfun_def apply auto
    by (metis (no_types, lifting) List.finite_set List.set_insert Proj.rep_eq Span.rep_eq
        cblinfun_apply_inverse finite.emptyI finite_list span_finite_dim)
  also have "\<dots> = Proj (Abs_clinear_space (complex_span {a}))
               +  Proj (Abs_clinear_space (complex_span (set S)))"
    unfolding Proj_def apply auto
    by (metis Span.rep_eq \<open>closure (complex_span (set S)) = complex_span (set S)\<close> finite.emptyI 
        finite.insertI space_as_set_inverse span_finite_dim)
  also have "\<dots> = Proj (Span {a}) + Proj (Span (set S))"
    by (simp add: Span.abs_eq span_finite_dim)
  finally show "Proj (Span (set (a#S))) = Proj (Span {a}) + Proj (Span (set S))".
qed

(* NEW *)
lemma mat_of_cblinfun_proj:
  fixes a::"'a::{onb_enum, chilbert_space}"
  defines   "d == canonical_basis_length TYPE('a)"
    and "norm2 == (vec_of_onb_enum a) \<bullet>c (vec_of_onb_enum a)"
  shows  "mat_of_cblinfun (proj a) = 
  1 / norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [vec_of_onb_enum a])"
proof(cases "a = 0")
  case True
  have q1: \<open>mat_of_cblinfun (proj a) \<in> carrier_mat d d\<close>
    unfolding mat_of_cblinfun_def d_def
    by auto
  have"proj a = 0"
    using True
      apply transfer
      by (simp add: projection_zero_subspace)
    hence "mat_of_cblinfun (proj a) = 0\<^sub>m d d"
      by (metis q1 cancel_comm_monoid_add_class.diff_cancel 
          cblinfun_of_mat_minusOp' minus_r_inv_mat)
    moreover have "norm2 = 0"
      unfolding norm2_def
      by (metis Bounded_Operators_Matrices.cinner_ell2_code True cinner_zero_left) 
    ultimately show ?thesis by auto
next
  case False
  then show ?thesis sorry
qed


(* NEW *)
lemma mk_projector_orthog_recurrence:
  fixes S::"'a::{onb_enum, chilbert_space} list"
    and a::'a
  defines "d == canonical_basis_length TYPE('a)"
  assumes a1: "is_ortho_set (set (a#S))" and a2: "distinct (a#S)"
  shows "mk_projector_orthog d (gram_schmidt d (map vec_of_onb_enum (a # S)))
  = mat_of_cblinfun (proj a) +
    mk_projector_orthog d (gram_schmidt d (map vec_of_onb_enum S))"
  using assms proof(induction S)
  case Nil
  have "dim_vec (vec_of_onb_enum a) = d"
    by (simp add: canonical_basis_length_eq d_def dim_vec_of_onb_enum_list')
  moreover have "dim_vec (0\<^sub>v d) = d"
    by simp
  ultimately have s1: "0\<^sub>v d + vec_of_onb_enum a = vec_of_onb_enum a"
    using carrier_vec_dim_vec left_zero_vec by blast   
  define norm2 where "norm2 = (vec_of_onb_enum a) \<bullet>c (vec_of_onb_enum a)"
  have dvad: "dim_vec (vec_of_onb_enum a) = d"
    by (simp add: \<open>dim_vec (vec_of_onb_enum a) = d\<close>)    
  have norm2_0:"norm2 = (0\<^sub>v d + vec_of_onb_enum a) \<bullet>c (0\<^sub>v d + vec_of_onb_enum a)"
    unfolding norm2_def
    using s1 by auto 
  have "mat_of_cblinfun (proj a) \<in> carrier_mat d d"
    unfolding mat_of_cblinfun_def d_def by auto
  hence w1: "mat_of_cblinfun (proj a) +
    0\<^sub>m (dim_vec (vec_of_onb_enum a)) (dim_vec (vec_of_onb_enum a)) 
    = mat_of_cblinfun (proj a)"
    by (simp add: dvad)    
  have "(if norm2 = 0 then 0\<^sub>m d d
        else 1 / norm2 \<cdot>\<^sub>m
     (mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [vec_of_onb_enum a])) 
    = mat_of_cblinfun (proj a)"
  proof(cases "norm2 = 0")
    case True
    hence "a = 0"
      unfolding norm2_def
      by (metis Bounded_Operators_Matrices.cinner_ell2_code cinner_eq_zero_iff) 
    hence "proj a = 0"
      apply transfer
      by (simp add: projection_zero_subspace)
    hence "mat_of_cblinfun (proj a) = 0\<^sub>m d d"
      by (metis \<open>mat_of_cblinfun (proj a) \<in> carrier_mat d d\<close> cancel_comm_monoid_add_class.diff_cancel 
          cblinfun_of_mat_minusOp' minus_r_inv_mat)      
    thus ?thesis
      by (simp add: True) 
  next
    case False
    hence "a \<noteq> 0"
      unfolding norm2_def
      by (metis Bounded_Operators_Matrices.cinner_ell2_code cinner_zero_left)
    hence "1 / norm2 \<cdot>\<^sub>m
          (mat_of_cols d [vec_of_onb_enum a] *
           mat_of_rows d [vec_of_onb_enum a]) =
    mat_of_cblinfun (proj a)"
      using mat_of_cblinfun_proj
      by (simp add: mat_of_cblinfun_proj d_def norm2_def)
    thus ?thesis using False by auto
  qed
  thus ?case apply auto unfolding norm2_def gram_schmidt_def apply auto
    using w1 dvad norm2_0 apply auto
    using s1 by presburger
next
  case (Cons b S)

  have "dim_vec (vec_of_onb_enum a) = d"
    by (simp add: canonical_basis_length_eq d_def dim_vec_of_onb_enum_list')
  moreover have "dim_vec (0\<^sub>v d) = d"
    by simp
  ultimately have s1: "0\<^sub>v d + vec_of_onb_enum a = vec_of_onb_enum a"
    using carrier_vec_dim_vec left_zero_vec by blast   

  have "gram_schmidt_sub d [vec_of_onb_enum a] (map vec_of_onb_enum S) = X"
    sorry    

  have "mk_projector_orthog d (gram_schmidt d (map vec_of_onb_enum (a # S)))
      = mk_projector_orthog d
     (rev (gram_schmidt_sub d [vec_of_onb_enum a] (map vec_of_onb_enum S)))"
    unfolding gram_schmidt_def using s1 by auto


  show ?case sorry
qed


(* NEW *)
lemma mat_of_cblinfun_Proj_Span_EASY:
  fixes S :: "'a::{onb_enum, chilbert_space} list"
  assumes "is_ortho_set (set S)" and "distinct S"
  shows
    "mat_of_cblinfun (Proj (Span (set S))) =
    (let d = canonical_basis_length TYPE('a) in 
      mk_projector_orthog d (gram_schmidt d (map vec_of_onb_enum S)))"
  using assms proof(induction S)
  case Nil
  have "space_as_set (Abs_clinear_space {0::'a}) = {0::'a}"
    by (metis bot_clinear_space.abs_eq bot_clinear_space.rep_eq)    
  hence "projection (space_as_set (Abs_clinear_space {0::'a})) = 
        projection {0::'a}"
    by simp
  also have "\<dots> = (\<lambda>_. (0::'a))"
    by (simp add: projection_zero_subspace)    
  finally have x2: "projection (space_as_set (Abs_clinear_space {0::'a})) = (\<lambda>_. (0::'a))".
  have " \<langle>(canonical_basis::'a list)!i, cBlinfun (\<lambda>_. 0) *\<^sub>V (canonical_basis::'a list)!j\<rangle> = 0"
    for i j
    by (metis cinner_zero_right zero_cblinfun.abs_eq zero_cblinfun.rep_eq)    
  hence x1: "mat_of_cblinfun (cBlinfun (\<lambda>_::'a. (0::'a)))
     = (let d = canonical_basis_length TYPE('a) in 0\<^sub>m d d)"
    unfolding mat_of_cblinfun_def zero_mat_def
    by (metis mat_of_cblinfun_def mat_of_cblinfun_zero' zero_cblinfun.abs_eq zero_mat_def) 
  show ?case apply auto unfolding gram_schmidt_def apply auto
    unfolding Span_def Proj_def apply auto
    using x1 x2 by simp
next
  case (Cons a S)
  define d where "d = canonical_basis_length TYPE('a)"
  have "is_ortho_set (set S)"
    using Cons.prems(1) is_onb_delete by auto    
  moreover have "distinct S"
    using Cons.prems(2) by auto    
  ultimately have t1: "mat_of_cblinfun (Proj (Span (set S))) =
    (let d = canonical_basis_length TYPE('a)
     in mk_projector_orthog d
         (gram_schmidt d (map vec_of_onb_enum S)))"
    by (simp add: Cons.IH)    
  have "Proj (Span (set (a#S))) = Proj (Span {a}) + Proj (Span (set S))"
    using Cons.prems(1) Cons.prems(2) Proj_Span_insert by auto
  hence "mat_of_cblinfun (Proj (Span (set (a#S)))) = 
         mat_of_cblinfun (Proj (Span {a}))
       + mat_of_cblinfun (Proj (Span (set S)))"
    by (simp add: cblinfun_of_mat_plusOp')
  hence "mat_of_cblinfun (Proj (Span (set (a#S)))) = 
         mat_of_cblinfun (Proj (Span {a}))
       + mk_projector_orthog d
         (gram_schmidt d (map vec_of_onb_enum S))"
    unfolding d_def using t1 by metis
  thus ?case
    using mk_projector_orthog_recurrence
    by (metis Cons.prems(1) Cons.prems(2) \<open>mat_of_cblinfun (Proj (Span (set (a # S)))) 
    = mat_of_cblinfun (proj a) + mat_of_cblinfun (Proj (Span (set S)))\<close> t1)
qed

(* TODO move to ..._Matrices *)
lemma mat_of_cblinfun_Proj_Span: "mat_of_cblinfun (Proj (Span (set S))) =
    (let d = canonical_basis_length TYPE('a) in 
      mk_projector_orthog d (gram_schmidt d (map vec_of_onb_enum S)))"
  for S :: "'a::onb_enum list"
    (*  using[[show_consts,show_types]]  *)
  thm Complex_Inner_Product.inner_product_projection
  thm Complex_Inner_Product.ortho_decomp
proof(induction S)
  case Nil
  have "space_as_set (Abs_clinear_space {0::'a}) = {0::'a}"
    by (metis bot_clinear_space.abs_eq bot_clinear_space.rep_eq)    
  hence "projection (space_as_set (Abs_clinear_space {0::'a})) = 
        projection {0::'a}"
    by simp
  also have "\<dots> = (\<lambda>_. (0::'a))"
    by (simp add: projection_zero_subspace)    
  finally have x2: "projection (space_as_set (Abs_clinear_space {0::'a})) = (\<lambda>_. (0::'a))".
  have " \<langle>(canonical_basis::'a list)!i, cBlinfun (\<lambda>_. 0) *\<^sub>V (canonical_basis::'a list)!j\<rangle> = 0"
    for i j
    by (metis cinner_zero_right zero_cblinfun.abs_eq zero_cblinfun.rep_eq)    
  hence x1: "mat_of_cblinfun (cBlinfun (\<lambda>_::'a. (0::'a)))
     = (let d = canonical_basis_length TYPE('a) in 0\<^sub>m d d)"
    unfolding mat_of_cblinfun_def zero_mat_def
    by (metis mat_of_cblinfun_def mat_of_cblinfun_zero' zero_cblinfun.abs_eq zero_mat_def) 
  show ?case apply auto unfolding gram_schmidt_def apply auto
    unfolding Span_def Proj_def apply auto
    using x1 x2 by simp
next
  case (Cons a S)
  define d where "d = canonical_basis_length TYPE('a)"
  have "dim_vec (vec_of_onb_enum a) = d"
    by (simp add: canonical_basis_length_eq d_def dim_vec_of_onb_enum_list')
  moreover have "dim_vec (0\<^sub>v d) = d"
    by simp
  ultimately have s1: "0\<^sub>v d + vec_of_onb_enum a = vec_of_onb_enum a"
    using carrier_vec_dim_vec left_zero_vec by blast   
  have "complex_span (insert a (set S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}"
    using complex_vector.span_insert[where a = a and S = "(set S)"].
  moreover have "finite (insert a (set S))"
    by simp    
  ultimately have "closure (complex_span (insert a (set S))) = 
        complex_span {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}"
    by (metis complex_vector.span_span span_finite_dim)
  hence s2: "space_as_set (Abs_clinear_space (closure (complex_span (insert a (set S))))) 
        = complex_span {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}"
    by (metis Span.rep_eq space_as_set_inverse)
  have "closure (complex_span (set S)) = complex_span (set S)"
    by (simp add: span_finite_dim)    
  hence q1: "mat_of_cblinfun
    (cBlinfun (projection (complex_span (set S)))) =
    (let d = canonical_basis_length TYPE('a)
     in mk_projector_orthog d
         (rev (gram_schmidt_sub d [] (map vec_of_onb_enum S))))"
    by (metis Cons.IH Proj_def Span.rep_eq gram_schmidt_def map_fun_apply)

  have "mat_of_cblinfun
     (cBlinfun
       (projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)})) =
          mk_projector_orthog d
         (rev (gram_schmidt_sub d [vec_of_onb_enum a] (map vec_of_onb_enum S)))"
    using q1 sorry
  thus ?case apply auto unfolding d_def gram_schmidt_def apply auto
    unfolding Span_def Proj_def using d_def s2 s1 Span.abs_eq Span_def map_fun_apply
    apply simp
    using \<open>closure (complex_span (insert a (set S))) = complex_span {x. \<exists>k. x - k *\<^sub>C a 
    \<in> complex_span (set S)}\<close> \<open>complex_span (insert a (set S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span 
    (set S)}\<close> \<open>finite (insert a (set S))\<close> span_finite_dim
  proof -
    show "mat_of_cblinfun (cBlinfun (projection (complex_span {aa. \<exists>c. aa - c *\<^sub>C a \<in> complex_span (set S)}))) = (let n = canonical_basis_length (TYPE('a)::'a itself) in mk_projector_orthog n (rev (gram_schmidt_sub n [vec_of_onb_enum a] (map vec_of_onb_enum S))))"
      by (metis (no_types) \<open>complex_span (insert a (set S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)}\<close> \<open>mat_of_cblinfun (cBlinfun (projection {x. \<exists>k. x - k *\<^sub>C a \<in> complex_span (set S)})) = mk_projector_orthog d (rev (gram_schmidt_sub d [vec_of_onb_enum a] (map vec_of_onb_enum S)))\<close> complex_vector.span_span d_def)
  qed
qed



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


lemma onb_enum_of_vec_unit_vec: "onb_enum_of_vec (unit_vec (canonical_basis_length TYPE('a)) i)
   = (canonical_basis!i :: 'a::onb_enum)"
  if "i < canonical_basis_length TYPE('a)"
  by (simp add: onb_enum_of_vec_unit_vec that)

(* Ask to Dominique: Is this lemma incorrect. See the version that I proved above.

\<Longrightarrow> You are right. You can remove the incorrect version.

(* TODO move to ..._Matrices *)
lemma onb_enum_of_vec_unit_vec: "onb_enum_of_vec (unit_vec (canonical_basis_length TYPE('a)) i)
   = (canonical_basis!i :: 'a::onb_enum)"
  sorry
*)

(* TODO: Move to Complex_Inner_Product *)
lemma Span_canonical_basis[simp]: "Span (set canonical_basis) = top"
  using Span.rep_eq space_as_set_inject top_clinear_space.rep_eq
    closure_UNIV is_generator_set
  by (metis )


lemma top_as_span[code]: "(top::'a clinear_space) = 
  (let n = canonical_basis_length TYPE('a::onb_enum) in
    SPAN (map (unit_vec n) [0..<n]))"
  unfolding SPAN_def
  apply (simp only: index_unit_vec Let_def map_filter_map_filter filter_set image_set map_map_filter 
      map_filter_map o_def)
  apply (simp add: onb_enum_of_vec_unit_vec)
  apply (subst nth_image)
  by (auto simp: canonical_basis_length_eq)

(* TODO: Move to the Complex_Vector_Spaces *)
lemma Span_empty[simp]: "Span {} = bot"
  apply transfer
  by simp

lemma bot_as_span[code]: "(bot::'a::onb_enum clinear_space) = SPAN []"
  unfolding SPAN_def by (auto simp: Set.filter_def)

(* TODO: Move to the Complex_Vector_Spaces *)
lemma Span_union: "Span A \<squnion> Span B = Span (A \<union> B)"
proof (transfer, auto)
  have p0: "Complex_Vector_Spaces.span (A \<union> B) = 
      Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B"
    for A B::"'a set"
    using Complex_Vector_Spaces.complex_vector.span_Un
    by (smt Collect_cong set_plus_def)
  hence p1: "closure (Complex_Vector_Spaces.span (A \<union> B)) = 
             closure (Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B)"
    for A B::"'a set"
    by simp

  show "x \<in> closure (Complex_Vector_Spaces.span (A \<union> B))"
    if "x \<in> closure (Complex_Vector_Spaces.span A) +\<^sub>M
            closure (Complex_Vector_Spaces.span B)"
    for x::'a and A B
  proof-
    have "closure (Complex_Vector_Spaces.span A) + closure (Complex_Vector_Spaces.span B) \<subseteq>
          closure (Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B)"
      using Starlike.closure_sum by auto
    hence "closure (Complex_Vector_Spaces.span A) + closure (Complex_Vector_Spaces.span B)
        \<subseteq> closure (Complex_Vector_Spaces.span (A \<union> B))"
      by (metis \<open>closure (Complex_Vector_Spaces.span A) + closure (Complex_Vector_Spaces.span B)
           \<subseteq> closure (Complex_Vector_Spaces.span A + Complex_Vector_Spaces.span B)\<close> p1)
    thus ?thesis by (smt closed_sum_def closure_closure closure_mono subsetD that)
  qed

  show "x \<in> closure (Complex_Vector_Spaces.span A) +\<^sub>M
            closure (Complex_Vector_Spaces.span B)"
    if "x \<in> closure (Complex_Vector_Spaces.span (A \<union> B))"
    for x::'a and A B
  proof-
    have "Complex_Vector_Spaces.span (A \<union> B) \<subseteq>
           closure (Complex_Vector_Spaces.span A) +
           closure (Complex_Vector_Spaces.span B)"
      apply auto
      by (metis closure_subset p0 set_plus_mono2_b) 
    hence "closure (Complex_Vector_Spaces.span (A \<union> B)) \<subseteq>
           closure (closure (Complex_Vector_Spaces.span A) +
                    closure (Complex_Vector_Spaces.span B))"
      by (smt closure_mono)
    thus ?thesis by (smt closed_sum_def in_mono that)
  qed
qed


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
    is_subspace_of (canonical_basis_length TYPE('a::onb_enum)) 
      (map vec_of_onb_enum A) (map vec_of_onb_enum B)"
proof
  show "is_subspace_of (canonical_basis_length (TYPE('a)::'a itself)) 
        (map vec_of_onb_enum A) (map vec_of_onb_enum B)"
    if "Span (set A) \<le> Span (set B)"
    sorry
  show "Span (set A) \<le> Span (set B)"
    if "is_subspace_of (canonical_basis_length (TYPE('a)::'a itself)) 
        (map vec_of_onb_enum A) (map vec_of_onb_enum B)"
    sorry
qed

lemma SPAN_leq[code]: "SPAN A \<le> 
  (SPAN B :: 'a::onb_enum clinear_space) \<longleftrightarrow> is_subspace_of (canonical_basis_length TYPE('a)) A B"
  sorry

lemma apply_cblinfun_Span: 
  "A *\<^sub>S Span (set S) = Span (onb_enum_of_vec ` set (map ((*\<^sub>v) (mat_of_cblinfun A)) (map vec_of_onb_enum S)))"
  apply (auto simp: applyOpSpace_Span image_image)
  by (metis mat_of_cblinfun_description onb_enum_of_vec_inverse)

lemma applyOpSpace_SPAN[code]: "applyOpSpace A (SPAN S)
      = SPAN (map (mult_mat_vec (mat_of_cblinfun A)) S)"
  for A::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum"
  unfolding SPAN_def Let_def
  using apply_cblinfun_Span[where A = A and S = 
      "map onb_enum_of_vec (filter (\<lambda>v. dim_vec v = (canonical_basis_length TYPE('a))) S) :: 'a list"]
  sorry

lemma kernel_SPAN[code]: "kernel A 
    = SPAN (find_base_vectors (gauss_jordan_single (mat_of_cblinfun A)))" 
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

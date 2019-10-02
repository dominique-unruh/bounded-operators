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

(* TODO:

This transforms |0> into [0,...,1] and |n-1> into [1,...,0] (if canonical_basis = [|0>,|1>,...,|n>])
which seems unnatural (backwards). I think we should map |0> to [1,...,0] instead.
 *)
primrec vec_of_basis_enum_list :: \<open>'a list \<Rightarrow> 'a::basis_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_basis_enum_list [] v = 0\<^sub>v (length (canonical_basis::'a list))\<close> | 
  \<open>vec_of_basis_enum_list (x#ys) v = vec_of_basis_enum_list ys v + 
\<langle>x, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length ys)\<close>

definition vec_of_basis_enum :: \<open>'a::basis_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_basis_enum v = vec_of_basis_enum_list canonical_basis v\<close> 


(* TODO: I think mixing recursion over lists (the basis) and direct indexing via natural numbers
   (vec_index ...) makes inductions harder. I think it is easier to define this like:

fun basis_enum_of_vec_list :: \<open>'a list \<Rightarrow> complex list \<Rightarrow> 'a::basis_enum\<close> where 
  \<open>basis_enum_of_vec_list [] [] = 0\<close> |
  \<open>basis_enum_of_vec_list (x#ys) (v#vs) =
 v *\<^sub>C x + basis_enum_of_vec_list ys vs\<close>

and then invoke it as "basis_enum_of_vec_list canonical_basis (list_of_vec v)".

(This also has the natural order of the coefficients like requested in my TODO above.)
*)


primrec basis_enum_of_vec_list :: \<open>'a list \<Rightarrow> complex vec \<Rightarrow> 'a::basis_enum\<close> where
  \<open>basis_enum_of_vec_list [] v = 0\<close> |
  \<open>basis_enum_of_vec_list (x#ys) v =
 (vec_index v (length ys)) *\<^sub>C x + basis_enum_of_vec_list ys v\<close>

definition basis_enum_of_vec :: \<open>complex vec \<Rightarrow> 'a::basis_enum\<close> where
  \<open>basis_enum_of_vec v = basis_enum_of_vec_list (canonical_basis::'a list) v\<close>

lemma basis_enum_of_vec_list':
  \<open>basis_enum_of_vec_list L v = sum (\<lambda> i. (vec_index v (length L - 1 - i)) *\<^sub>C ((L::'a::basis_enum list) ! i)) {..< length L}\<close>
proof(induction L)
  case Nil
  thus ?case by simp
next
  case (Cons a L)
  have \<open>basis_enum_of_vec_list (a # L) v =
           (\<Sum>i<length (a # L). (vec_index v (length (a # L) - 1 - i)) *\<^sub>C (a # L) ! i)\<close>
  proof-
    have \<open>basis_enum_of_vec_list (a # L) v = (vec_index v (length L)) *\<^sub>C a + 
                                    basis_enum_of_vec_list L v\<close>
      by simp
    also have \<open>... = (vec_index v (length L)) *\<^sub>C a + 
                                    (\<Sum>i<length L. (vec_index v (length L - 1 - i)) *\<^sub>C L ! i)\<close>
      using Cons.IH by presburger
    also have \<open>... = (vec_index v (length L)) *\<^sub>C ((a # L) ! 0) + 
   (\<Sum>i<length L. (vec_index v (length (a # L) - 1 - Suc i)) *\<^sub>C (a#L) ! (Suc i))\<close>
      by auto
    also have \<open>... = (vec_index v (length L)) *\<^sub>C ((a # L) ! 0) + 
   sum (\<lambda> i. vec_index v (length (a # L) - 1 - i) *\<^sub>C (a#L) ! i) {Suc 0..length L}\<close>
      using Set_Interval.comm_monoid_add_class.sum.atLeast1_atMost_eq
      by (metis (no_types, lifting) sum.cong)
    also have \<open>... = (\<lambda> i. vec_index v (length (a # L) - 1 - i) *\<^sub>C (a#L) ! i) 0 + 
   sum (\<lambda> i. vec_index v (length (a # L) - 1 - i) *\<^sub>C (a#L) ! i) {Suc 0..length L}\<close>
      by auto    
    also have \<open>... = 
   sum (\<lambda> i. vec_index v (length (a # L) - 1 - i) *\<^sub>C (a#L) ! i) {..length L}\<close>
      by (simp add: sum.atLeast1_atMost_eq sum.atMost_shift)
    finally show ?thesis
      by (simp add: lessThan_Suc_atMost) 
  qed
  thus ?case by simp
qed

(* TODO: Why do we need basis_enum_of_vec_list? We can write the following lemma as the definition of basis_enum_of_vec
   (since 'a::basis_enum is a comm_monoid_add) *)
lemma basis_enum_of_vec':
  \<open>basis_enum_of_vec v = sum (\<lambda> i. (vec_index v (length (canonical_basis::'a::basis_enum list) - 1 - i)) *\<^sub>C ((canonical_basis::'a::basis_enum list) ! i)) {..< length (canonical_basis::'a list)}\<close>
  using basis_enum_of_vec_list' unfolding basis_enum_of_vec_def
  by blast

lemma basis_enum_of_vec_list_add':
\<open>\<forall> x y. length L \<le> dim_vec x \<and> length L \<le> dim_vec y \<longrightarrow> 
(basis_enum_of_vec_list L) (x + y) = (basis_enum_of_vec_list L) x + (basis_enum_of_vec_list L) y\<close>
proof(induction L)
case Nil
  thus ?case
    by simp 
next
  case (Cons a L)
  have \<open>length (a # L) \<le> dim_vec x \<Longrightarrow> length (a # L) \<le> dim_vec y \<Longrightarrow>
          basis_enum_of_vec_list (a # L) (x + y) =
          basis_enum_of_vec_list (a # L) x +
          basis_enum_of_vec_list (a # L) y\<close>
    for x y
  proof-
    assume \<open>length (a # L) \<le> dim_vec x\<close> and \<open>length (a # L) \<le> dim_vec y\<close>
    have \<open>basis_enum_of_vec_list (a # L) x =
      (vec_index x (length L)) *\<^sub>C a + basis_enum_of_vec_list L x\<close>
      by simp
    moreover have \<open>basis_enum_of_vec_list (a # L) y =
      (vec_index y (length L)) *\<^sub>C a + basis_enum_of_vec_list L y\<close>
      by simp
    moreover have \<open>basis_enum_of_vec_list (a # L) (x + y) =
      (vec_index (x + y) (length L)) *\<^sub>C a + basis_enum_of_vec_list L (x + y)\<close>
      by simp
    moreover have \<open>vec_index (x + y) (length L) = vec_index x (length L) + vec_index y (length L)\<close>
      using \<open>length (a # L) \<le> dim_vec y\<close> by auto
    moreover have \<open>basis_enum_of_vec_list L (x + y) = basis_enum_of_vec_list L x
         + basis_enum_of_vec_list L y\<close>
      using Cons.IH \<open>length (a # L) \<le> dim_vec x\<close> \<open>length (a # L) \<le> dim_vec y\<close> by auto      
    ultimately show ?thesis
      by (simp add: scaleC_left.add) 
  qed
  thus ?case by blast
qed

lemma basis_enum_of_vec_list_add:
\<open>length L \<le> dim_vec x \<Longrightarrow> length L \<le> dim_vec y \<Longrightarrow> 
(basis_enum_of_vec_list L) (x + y) = (basis_enum_of_vec_list L) x + (basis_enum_of_vec_list L) y\<close>
  using basis_enum_of_vec_list_add'
  by blast

hide_fact basis_enum_of_vec_list_add'

lemma basis_enum_of_vec_list_mult':
\<open>\<forall> x y. length L \<le> dim_vec x \<longrightarrow> 
(basis_enum_of_vec_list L) (c \<cdot>\<^sub>v x) = c *\<^sub>C (basis_enum_of_vec_list L) x\<close>
proof(induction L)
  case Nil
  thus ?case by auto
next
  case (Cons a L)
  have \<open>length (a # L) \<le> dim_vec x \<Longrightarrow>
                 basis_enum_of_vec_list (a # L) (c \<cdot>\<^sub>v x) =
                 c *\<^sub>C basis_enum_of_vec_list (a # L) x\<close>
    for x
  proof-
    assume \<open>length (a # L) \<le> dim_vec x\<close>
    have \<open>basis_enum_of_vec_list (a # L) (c \<cdot>\<^sub>v x) =
        basis_enum_of_vec_list L (c \<cdot>\<^sub>v x) + (vec_index (c \<cdot>\<^sub>v x) (length L)) *\<^sub>C a\<close>
      by auto
    also have \<open>\<dots> =
        basis_enum_of_vec_list L (c \<cdot>\<^sub>v x) + (c *\<^sub>C (vec_index x (length L))) *\<^sub>C a\<close>
      using \<open>length (a # L) \<le> dim_vec x\<close> by auto
    also have \<open>\<dots> =
        c *\<^sub>C (basis_enum_of_vec_list L x) + (c *\<^sub>C (vec_index x (length L))) *\<^sub>C a\<close>
      using Cons.IH \<open>length (a # L) \<le> dim_vec x\<close> by auto
    also have \<open>\<dots> =
        c *\<^sub>C ((basis_enum_of_vec_list L x) + (vec_index x (length L)) *\<^sub>C a)\<close>
      by (simp add: scaleC_add_right)
    also have \<open>\<dots> =
        c *\<^sub>C basis_enum_of_vec_list (a # L) x\<close>
      by simp
    finally show \<open>basis_enum_of_vec_list (a # L) (c \<cdot>\<^sub>v x) =
                 c *\<^sub>C basis_enum_of_vec_list (a # L) x\<close>
      by blast
  qed
  thus ?case by blast
qed

lemma basis_enum_of_vec_list_mult:
\<open>length L \<le> dim_vec x \<Longrightarrow>
(basis_enum_of_vec_list L) (c \<cdot>\<^sub>v x) = c *\<^sub>C (basis_enum_of_vec_list L) x\<close>
  using basis_enum_of_vec_list_mult' by auto

hide_fact basis_enum_of_vec_list_mult'

lemma vec_of_basis_enum_list_dim:
\<open>dim_vec (vec_of_basis_enum_list L (t::'a)) = length (canonical_basis::('a::basis_enum) list)\<close>
proof(induction L)
  case Nil
  have \<open>dim_vec (vec_of_basis_enum_list [] t) = length (canonical_basis::'a list)\<close>
    by simp
  thus ?case by blast
next
  case (Cons a L)
  have \<open>vec_of_basis_enum_list (a # L) t = vec_of_basis_enum_list L t + 
\<langle>a, t\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L)\<close>
    by simp
  hence \<open>dim_vec (vec_of_basis_enum_list (a # L) t) =
           length (canonical_basis::('a::basis_enum) list)\<close>
    by simp    
  thus ?case by blast
qed

lemma vec_of_basis_enum_list':
  \<open>\<forall> x y. (vec_of_basis_enum_list (L::('a::basis_enum) list)) (x + y) = (vec_of_basis_enum_list L) x + (vec_of_basis_enum_list L) y\<close>
proof(induction L)
  case Nil
  thus ?case by auto
next
  case (Cons a L)
  have \<open>dim_vec (vec_of_basis_enum_list L t) = length (canonical_basis::'a list)\<close>
    for t
    by (simp add: vec_of_basis_enum_list_dim)    
  have \<open>vec_of_basis_enum_list (a # L) (x + y) =
    vec_of_basis_enum_list (a # L) x + vec_of_basis_enum_list (a # L) y\<close>
    for x y
  proof-
    have \<open>vec_of_basis_enum_list (a # L) (x + y) = 
        vec_of_basis_enum_list L (x + y) +
         \<langle>a, x+y\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L)\<close>
      by simp
    also have \<open>\<dots> = 
        (vec_of_basis_enum_list L) x + (vec_of_basis_enum_list L) y +
         \<langle>a, x+y\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L)\<close>
      by (simp add: Cons.IH)
    also have \<open>\<dots> = 
        (vec_of_basis_enum_list L) x + (vec_of_basis_enum_list L) y +
         \<langle>a, x\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L)
       + \<langle>a, y\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L)\<close>
    proof-
      have \<open>\<langle>a, x+y\<rangle> = \<langle>a, x\<rangle> + \<langle>a, y\<rangle>\<close>
        by (simp add: cinner_right_distrib)        
      hence \<open>\<langle>a, x+y\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L)
          = \<langle>a, x\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L)
          + \<langle>a, y\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L)\<close>
        by (simp add: add_smult_distrib_vec)       
      thus ?thesis by auto
    qed
    also have \<open>\<dots>
  = ( (vec_of_basis_enum_list L x) + 
  (\<langle>a, x\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L)) ) +
  ( (vec_of_basis_enum_list L y) +
  (\<langle>a, y\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L)) )\<close>
      using \<open>\<And>t. dim_vec (vec_of_basis_enum_list L t) = length canonical_basis\<close> carrier_vec_dim_vec comm_add_vec index_add_vec(2) index_smult_vec(2) index_unit_vec(3) 
      by auto
    also have \<open>\<dots>
  = (vec_of_basis_enum_list (a # L) x) + (vec_of_basis_enum_list (a # L) y)\<close>
      by simp
    finally show ?thesis by blast
  qed
  thus ?case by blast
qed

lemma vec_of_basis_enum_list:
  \<open>(vec_of_basis_enum_list (L::('a::basis_enum) list)) (x + y) = (vec_of_basis_enum_list L) x + (vec_of_basis_enum_list L) y\<close>
  by (simp add: vec_of_basis_enum_list')


lemma basis_enum_of_vec_COMP_vec_of_basis_enum_list:
  \<open>(basis_enum_of_vec_list L) \<circ> (vec_of_basis_enum_list L)
 = projection (complex_vector.span (set L))\<close>
proof (induction L)
  show "basis_enum_of_vec_list [] \<circ> (\<lambda>a. vec_of_basis_enum_list [] (a::'a)) = projection (complex_vector.span (set []))"
  proof-
    have \<open>projection (complex_vector.span (set [])) = (\<lambda> _. 0::'a)\<close>
    proof-
      have \<open>complex_vector.span (set ([]::'a list)) = {0}\<close>
        by auto
      thus ?thesis using projection_zero_subspace
        by auto
    qed
    moreover have \<open>basis_enum_of_vec_list [] = (\<lambda> _. 0::'a)\<close>
      by auto      
    ultimately show ?thesis 
      by auto
  qed
  show "basis_enum_of_vec_list (a # L) \<circ> vec_of_basis_enum_list (a # L) = projection (complex_vector.span (set (a # L)))"
    if "basis_enum_of_vec_list L \<circ> (\<lambda>a. vec_of_basis_enum_list L (a::'a)) = projection (complex_vector.span (set L))"
    for a :: 'a
      and L :: "'a list"
  proof-
    have \<open>basis_enum_of_vec_list (a # L) \<circ> vec_of_basis_enum_list (a # L)
        = (\<lambda> v. (vec_index v (length L)) *\<^sub>C a + basis_enum_of_vec_list L v ) \<circ> vec_of_basis_enum_list (a # L)\<close>
      by auto
    also have \<open>\<dots> = (\<lambda> v. (vec_index v (length L)) *\<^sub>C a + basis_enum_of_vec_list L v ) \<circ> 
(\<lambda> v. vec_of_basis_enum_list L v + 
\<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L) )\<close>
      by auto
    also have \<open>\<dots> = (\<lambda> v. vec_index ( vec_of_basis_enum_list L v + 
\<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L) ) (length L) *\<^sub>C a +
 basis_enum_of_vec_list L (vec_of_basis_enum_list L v + 
\<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L) ) )\<close>
      by (meson comp_apply)
    also have \<open>\<dots> = (\<lambda> v. vec_index ( vec_of_basis_enum_list L v + 
\<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L) ) (length L) *\<^sub>C a +
 basis_enum_of_vec_list L (vec_of_basis_enum_list L v) + 
 basis_enum_of_vec_list L (\<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L) ) )\<close>
      sorry
    also have \<open>\<dots> = (\<lambda> v. vec_index ( vec_of_basis_enum_list L v + 
\<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L) ) (length L) *\<^sub>C a +
 projection (complex_vector.span (set L)) v + 
 basis_enum_of_vec_list L (\<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L) ) )\<close>
      using comp_eq_dest_lhs that by fastforce
    also have \<open>\<dots> = (\<lambda> v. vec_index ( vec_of_basis_enum_list L v + 
\<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) (length L) ) (length L) *\<^sub>C a +
 projection (complex_vector.span (set L)) v + 
 \<langle>a, v\<rangle> *\<^sub>C basis_enum_of_vec_list L (unit_vec (length (canonical_basis::'a list)) (length L) ) )\<close>
      sorry
    show ?thesis sorry
  qed
qed


(* TODO: When written as \<open>basis_enum_of_vec (vec_of_basis_enum v) = v\<close>
   such a lemma is more easily used as, e.g., a simp-rule (in my experience) *)
lemma basis_enum_of_vec_COMP_vec_of_basis_enum:
  \<open>basis_enum_of_vec \<circ> vec_of_basis_enum = id\<close>
  unfolding basis_enum_of_vec_def vec_of_basis_enum_def
  sorry

(* TODO: When written as \<open>vec_of_basis_enum (basis_enum_of_vec v) = v\<close>
   such a lemma is more easily used as, e.g., a simp-rule (in my experience) *)
(* TODO: Not true. Only holds for vectors v with "dim v = canonical_basis_length" *)
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

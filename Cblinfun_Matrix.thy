theory Cblinfun_Matrix
  imports
    Complex_L2

    "Jordan_Normal_Form.Gram_Schmidt"
    "HOL-Analysis.Starlike"
    "Bounded_Operators-Extra.Extra_Jordan_Normal_Form"
begin

hide_const (open) Order.bottom Order.top
hide_type (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.mat
hide_fact (open) Finite_Cartesian_Product.mat_def
hide_const (open) Finite_Cartesian_Product.vec
hide_fact (open) Finite_Cartesian_Product.vec_def
hide_const (open) Finite_Cartesian_Product.row
hide_fact (open) Finite_Cartesian_Product.row_def
no_notation Finite_Cartesian_Product.vec_nth (infixl "$" 90)

subsection\<open>\<open>Jordan_Normal_Form_Notation\<close> -- Cleaning up syntax from \<^session>\<open>Jordan_Normal_Form\<close>\<close>

unbundle jnf_notation
unbundle cblinfun_notation


subsection \<open>Setting up code generation for type cblinfun\<close>

text \<open>We define the canonical isomorphism between \<^typ>\<open>'a::basis_enum \<Rightarrow>\<^sub>C\<^sub>L'b::basis_enum\<close>
  and the complex \<^term>\<open>n*m\<close>-matrices (where n,m are the cdimensions of 'a,'b, 
  respectively). This is possible if \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close> are of class \<^class>\<open>basis_enum\<close>
  since that class fixes a finite canonical basis. Matrices are represented using
  the \<^typ>\<open>_ mat\<close> type from \<^session>\<open>Jordan_Normal_Form\<close>.
  (The isomorphism will be called \<^term>\<open>mat_of_cblinfun\<close> below.)\<close>

(* primrec vec_of_basis_enum_list :: \<open>'a list \<Rightarrow> 'a::{basis_enum,complex_inner} \<Rightarrow> nat \<Rightarrow> complex vec\<close> 
  where
  \<open>vec_of_basis_enum_list [] v _ = 0\<^sub>v (length (canonical_basis::'a list))\<close> |
  \<open>vec_of_basis_enum_list (x#ys) v i = vec_of_basis_enum_list ys v (Suc i) +
    \<langle>x, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i\<close> *)

definition vec_of_basis_enum :: \<open>'a::basis_enum \<Rightarrow> complex vec\<close> where
  \<comment> \<open>Maps \<^term>\<open>v\<close> to a \<^typ>\<open>'a vec\<close> represented in basis \<^const>\<open>canonical_basis\<close>\<close>
  \<open>vec_of_basis_enum v = vec_of_list (map (crepresentation (set canonical_basis) v) canonical_basis)\<close>

(* lemma dim_vec_of_basis_enum_list:
  \<open>dim_vec (vec_of_basis_enum_list (L::'a list) v i) = length (canonical_basis::'a::{basis_enum,complex_inner} list)\<close>
  by (induction L, auto) *)

(* Renamed from dim_vec_of_basis_enum_list' *)
lemma dim_vec_of_basis_enum':
  \<open>dim_vec (vec_of_basis_enum (v::'a)) = length (canonical_basis::'a::basis_enum list)\<close>
  unfolding vec_of_basis_enum_def 
  (* using dim_vec_of_basis_enum_list *)
  by simp  

lemma dim_vec_vec_of_basis_enum[simp]: "dim_vec (vec_of_basis_enum (a :: 'a::enum ell2)) = CARD('a)"
  by (metis canonical_basis_length_ell2 dim_vec_of_basis_enum')

(* lemma vec_of_basis_enum_list_add:
  \<open>vec_of_basis_enum_list (L::'a::{basis_enum,complex_inner} list) (v1 + v2) i =
   vec_of_basis_enum_list L v1 i + vec_of_basis_enum_list L v2 i\<close>
proof (induction L arbitrary : i)
  case Nil thus ?case by simp
next
  case (Cons a L)
  have "vec_of_basis_enum_list (a # L) (v1 + v2) i = 
    vec_of_basis_enum_list L (v1 + v2) (Suc i) +
    \<langle>a, v1 + v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i"
    by simp
  moreover have "vec_of_basis_enum_list L (v1 + v2) (Suc i) = 
  vec_of_basis_enum_list L v1 (Suc i) + vec_of_basis_enum_list L v2 (Suc i)"
    by (simp add: Cons.IH)
  moreover have "\<langle>a, v1 + v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i = 
                 \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i + 
                 \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i"
    by (simp add: add_smult_distrib_vec cinner_add_right)
  ultimately have "vec_of_basis_enum_list (a # L) (v1 + v2) i = 
                   vec_of_basis_enum_list L v1 (Suc i)
                 + vec_of_basis_enum_list L v2 (Suc i)
                 + \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i 
                 + \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i"
    by auto
  also have "\<dots> = (vec_of_basis_enum_list L v1 (Suc i) + \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i)
    + (vec_of_basis_enum_list L v2 (Suc i) + \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i)"
  proof-
    have w1: "\<lbrakk>dim_vec a = n; dim_vec b = n; dim_vec c = n; dim_vec d = n\<rbrakk>
        \<Longrightarrow> a + b + c + d = (a + c) + (b + d)" for a b c d::"complex vec" and n
      by auto
    thus ?thesis
      by (simp add: dim_vec_of_basis_enum_list) 
  qed
  finally have "vec_of_basis_enum_list (a # L) (v1 + v2) i = 
  (vec_of_basis_enum_list L v1 (Suc i) + \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i)
+ (vec_of_basis_enum_list L v2 (Suc i) + \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i)"
    by simp
  moreover have "vec_of_basis_enum_list L v1 (Suc i)
                + \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i 
                = vec_of_basis_enum_list (a # L) v1 i"
    by simp
  moreover have "vec_of_basis_enum_list L v2 (Suc i)
                + \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i =
                vec_of_basis_enum_list (a # L) v2 i"
    by simp
  ultimately show "vec_of_basis_enum_list (a # L) (v1 + v2) i =
       vec_of_basis_enum_list (a # L) v1 i +
       vec_of_basis_enum_list (a # L) v2 i"
    by smt
qed
 *)

(* lemma vec_of_basis_enum_list_mult:
  fixes L :: "'a::{basis_enum,complex_inner} list"
  shows \<open>vec_of_basis_enum_list L (c *\<^sub>C v) i = c \<cdot>\<^sub>v vec_of_basis_enum_list L v i\<close>
proof(induction L arbitrary: i)
  case Nil
  thus ?case by auto
next
  case (Cons a L)
  have "vec_of_basis_enum_list (a # L) (c *\<^sub>C v) i = 
    vec_of_basis_enum_list L (c *\<^sub>C v) (Suc i) +
    c * \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i"
    by simp
  also have "\<dots> = 
    c \<cdot>\<^sub>v vec_of_basis_enum_list L v (Suc i) +
    c * \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i"
    by (simp add: Cons.IH)
  also have "\<dots> = 
    c \<cdot>\<^sub>v (vec_of_basis_enum_list L v (Suc i) +
           \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i)"
  proof-
    have "\<lbrakk>dim_vec x = n; dim_vec y = n\<rbrakk> \<Longrightarrow> 
         c \<cdot>\<^sub>v x + c \<cdot>\<^sub>v y = c \<cdot>\<^sub>v (x + y)" for x y::"complex vec" and n
      by (metis carrier_vec_dim_vec smult_add_distrib_vec)      
    thus ?thesis
      by (metis dim_vec_of_basis_enum_list index_smult_vec(2) index_unit_vec(3) smult_smult_assoc) 
  qed
  finally show "vec_of_basis_enum_list (a # L) (c *\<^sub>C v) i =
        c \<cdot>\<^sub>v vec_of_basis_enum_list (a # L) v i"
    by simp
qed *)

fun basis_enum_of_vec_list :: \<open>'a list \<Rightarrow> complex list \<Rightarrow> 'a::complex_vector\<close> where 
  \<open>basis_enum_of_vec_list [] v = 0\<close> |
  \<open>basis_enum_of_vec_list y [] = 0\<close> |
  \<open>basis_enum_of_vec_list (x#ys) (v#vs) = v *\<^sub>C x + basis_enum_of_vec_list ys vs\<close>

lemma basis_enum_of_vec_list_def': "basis_enum_of_vec_list xs ys = sum_list (map2 (*\<^sub>C) ys xs)"
proof(induction xs arbitrary: ys)
  case Nil
  thus ?case by auto
next
  case (Cons a xs)
  thus ?case
  proof(induction ys)
    case Nil
    thus ?case by auto
  next
    case (Cons a ys)
    thus ?case by auto
  qed
qed

definition basis_enum_of_vec :: \<open>complex vec \<Rightarrow> 'a::basis_enum\<close> where
  \<open>basis_enum_of_vec v = 
    (if dim_vec v = canonical_basis_length TYPE('a)
     then basis_enum_of_vec_list (canonical_basis::'a list) (list_of_vec v)
     else 0)\<close>

lemma list_of_vec_plus:
  fixes v1 v2 :: \<open>complex vec\<close>
  assumes \<open>dim_vec v1 = dim_vec v2\<close>
  shows \<open>list_of_vec (v1 + v2) = map2 (+) (list_of_vec v1) (list_of_vec v2)\<close>
proof-
  have \<open>i < dim_vec v1 \<Longrightarrow> (list_of_vec (v1 + v2)) ! i = (map2 (+) (list_of_vec v1) (list_of_vec v2)) ! i\<close>
    for i
    by (simp add: assms)
  thus ?thesis
    by (metis assms index_add_vec(2) length_list_of_vec length_map map_fst_zip nth_equalityI) 
qed

lemma basis_enum_of_vec_add:
  assumes \<open>dim_vec v1 = canonical_basis_length TYPE('a::basis_enum)\<close> and
    \<open>dim_vec v2 = canonical_basis_length TYPE('a)\<close>
  shows \<open>((basis_enum_of_vec (v1 + v2)) :: 'a) = basis_enum_of_vec v1 + basis_enum_of_vec v2\<close>
proof -
  define l1 l2 where "l1 = list_of_vec v1" and "l2 = list_of_vec v2"
  define basis where "basis = (canonical_basis::'a list)"
  have length: "length l1 = length l2"
    by (simp add: assms l1_def l2_def)
  have length_basis: "length l2 = length basis"
    by (simp add: assms basis_def l2_def)
  have \<open>(basis_enum_of_vec::_\<Rightarrow>'a) (v1 + v2) = basis_enum_of_vec_list basis (list_of_vec (v1+v2))\<close>
    by (simp add: basis_def basis_enum_of_vec_def assms)
  also have \<open>\<dots> = basis_enum_of_vec_list basis (map2 (+) l1 l2)\<close>
    apply (subst list_of_vec_plus)
    using assms l1_def l2_def by auto
  also have \<open>\<dots> = basis_enum_of_vec_list basis l1
           + basis_enum_of_vec_list basis l2\<close>
    using length length_basis
  proof (induction l1 l2 basis rule: list_induct3)
    case Nil
    thus ?case
      using basis_enum_of_vec_list.elims by auto 
  next
    case (Cons x xs y ys z zs)
    assume \<open>length xs = length ys\<close> and \<open>length ys = length zs\<close> and
      \<open>basis_enum_of_vec_list zs (map2 (+) xs ys) =
       basis_enum_of_vec_list zs xs + basis_enum_of_vec_list zs ys\<close>
    have \<open>basis_enum_of_vec_list (z # zs) (map2 (+) (x # xs) (y # ys)) =
       (x + y) *\<^sub>C z + basis_enum_of_vec_list zs (map2 (+) xs ys)\<close>
      by auto
    also have \<open>\<dots> =
       (x + y) *\<^sub>C z + basis_enum_of_vec_list zs xs + basis_enum_of_vec_list zs ys\<close>
      using \<open>basis_enum_of_vec_list zs (map2 (+) xs ys) =
       basis_enum_of_vec_list zs xs + basis_enum_of_vec_list zs ys\<close>
      by auto
    also have \<open>\<dots> =
       x *\<^sub>C z + y *\<^sub>C z + basis_enum_of_vec_list zs xs + basis_enum_of_vec_list zs ys\<close>
    proof-
      have \<open>(x + y) *\<^sub>C z = x *\<^sub>C z + y *\<^sub>C z\<close>
        by (simp add: scaleC_left.add)
      thus ?thesis
        by simp 
    qed
    also have \<open>\<dots> =
       (x *\<^sub>C z + basis_enum_of_vec_list zs xs) + (y *\<^sub>C z + basis_enum_of_vec_list zs ys)\<close>
      by simp
    also have \<open>\<dots> =
       basis_enum_of_vec_list (z # zs) (x # xs) +
       basis_enum_of_vec_list (z # zs) (y # ys)\<close>
      by simp
    finally show \<open>basis_enum_of_vec_list (z # zs) (map2 (+) (x # xs) (y # ys)) =
       basis_enum_of_vec_list (z # zs) (x # xs) +
       basis_enum_of_vec_list (z # zs) (y # ys)\<close> 
      by blast
  qed
  also have \<open>\<dots> = basis_enum_of_vec v1 + basis_enum_of_vec v2\<close>
    by (simp add: basis_def basis_enum_of_vec_def l1_def l2_def assms)
  finally show ?thesis
    by auto
qed

lemma list_of_vec_mult:
  fixes v :: \<open>complex vec\<close>
  shows \<open>list_of_vec (c \<cdot>\<^sub>v v) = map ((*) c) (list_of_vec v)\<close>
proof-
  have \<open>i < dim_vec v \<Longrightarrow> (list_of_vec (c \<cdot>\<^sub>v v))!i = (map ((*) c) (list_of_vec v)) ! i\<close>
    for i
    by simp    
  thus ?thesis
    by (simp add: list_eq_iff_nth_eq) 
qed

lemma basis_enum_of_vec_mult:
  assumes \<open>dim_vec v = canonical_basis_length TYPE('a::basis_enum)\<close> 
  shows \<open>((basis_enum_of_vec (c \<cdot>\<^sub>v v)) :: 'a) =  c *\<^sub>C basis_enum_of_vec v\<close>
proof -
  define basis where "basis \<equiv> canonical_basis::'a::basis_enum list"
  define l where "l = list_of_vec v"
  have length_basis: "length l = length basis"
    by (simp add: assms basis_def l_def)
  have \<open>(basis_enum_of_vec::_\<Rightarrow>'a) (c \<cdot>\<^sub>v v) =
 basis_enum_of_vec_list basis (list_of_vec (c \<cdot>\<^sub>v v))\<close>
    by (simp add: basis_def basis_enum_of_vec_def assms)
  also have \<open>\<dots> = basis_enum_of_vec_list basis (map ((*) c) (list_of_vec v))\<close>
    apply (subst list_of_vec_mult)
    by auto
  also have \<open>\<dots> = basis_enum_of_vec_list basis (map ((*) c) l)\<close>
    using l_def by auto
  also have \<open>\<dots> = c *\<^sub>C (basis_enum_of_vec_list basis l)\<close>
    using length_basis
  proof (induction l basis rule: list_induct2)
    case Nil
    thus ?case by auto
  next
    case (Cons x xs y ys)
    assume \<open>length xs = length ys\<close> and 
      \<open>basis_enum_of_vec_list ys (map ((*) c) xs) =
       c *\<^sub>C basis_enum_of_vec_list ys xs\<close> 
    have \<open>basis_enum_of_vec_list (y # ys)
        (map ((*) c) (x # xs)) = (c * x) *\<^sub>C y +
    basis_enum_of_vec_list ys (map ((*) c) xs)\<close>
      by auto
    also have \<open>\<dots> = (c * x) *\<^sub>C y + c *\<^sub>C basis_enum_of_vec_list ys xs\<close>
      by (simp add: Cons.IH)
    also have \<open>\<dots> = c *\<^sub>C (x *\<^sub>C y) + c *\<^sub>C basis_enum_of_vec_list ys xs\<close>
      by simp
    also have \<open>\<dots> = c *\<^sub>C (x *\<^sub>C y + basis_enum_of_vec_list ys xs)\<close>
      by (simp add: scaleC_add_right)
    also have \<open>\<dots>  =
       c *\<^sub>C basis_enum_of_vec_list (y # ys) (x # xs)\<close>
      by simp
    finally show \<open>basis_enum_of_vec_list (y # ys)
        (map ((*) c) (x # xs)) =
       c *\<^sub>C basis_enum_of_vec_list (y # ys) (x # xs)\<close>
      by blast
  qed
  also have \<open>\<dots> = c *\<^sub>C basis_enum_of_vec v\<close>
    by (simp add: basis_def basis_enum_of_vec_def l_def assms)
  finally show ?thesis
    by auto
qed

lemma vector_space_zero_canonical_basis:
  assumes f1: "(canonical_basis::('a::basis_enum list)) = []"
  shows "(v::'a) = 0"
proof-
  have "complex_vector.span (set (canonical_basis::('a list))) = UNIV"
    using is_generator_set  by auto
  moreover have "complex_vector.span (set (canonical_basis::('a list))) = {0}"
  proof-
    have "set (canonical_basis::('a list)) = {}"
      using f1 by auto      
    thus ?thesis by simp 
  qed
  ultimately show ?thesis by auto
qed

lemma cinner_span_breakdown_eq:
  includes notation_norm
  assumes f1: "a \<notin> S" and f2: "is_ortho_set (insert a S)" and f3: "\<parallel>a\<parallel> = 1"
  shows
 "(x \<in> cspan (insert a S)) = (x - \<langle>a, x\<rangle> *\<^sub>C a \<in> cspan S)"
proof
  show "x - \<langle>a, x\<rangle> *\<^sub>C a \<in> cspan S"
    if "x \<in> cspan (insert a S)"
  proof-
    have "\<exists>k. x - k *\<^sub>C a \<in> cspan S"
      using that
      by (simp add: complex_vector.span_breakdown_eq)
    then obtain k where "x - k *\<^sub>C a \<in> cspan S"
      by blast
    hence "\<exists>t r. finite t \<and> t \<subseteq> S \<and> x - k *\<^sub>C a = (\<Sum>c\<in>t. r c *\<^sub>C c)"
      using complex_vector.span_explicit by (smt mem_Collect_eq)
    then obtain t r where c1: "finite t" and c2: "t \<subseteq> S" and c3: "x - k *\<^sub>C a = (\<Sum>c\<in>t. r c *\<^sub>C c)"
      by blast
    have "\<langle>a, x - k *\<^sub>C a\<rangle> = \<langle>a, (\<Sum>c\<in>t. r c *\<^sub>C c)\<rangle>"
      using c3
      by simp
    also have "\<dots> = (\<Sum>c\<in>t. r c * \<langle>a, c\<rangle>)"
      by (metis (mono_tags, lifting) cinner_scaleC_right cinner_sum_right sum.cong)
    also have "\<dots> = 0"
    proof-
      have "c\<in>S \<Longrightarrow> \<langle>a, c\<rangle> = 0" for c
      proof-
        assume "c\<in>S"
        hence "a \<noteq> c"
          using f1 by blast
        thus ?thesis
          using f2
          by (metis DiffD1 Diff_insert_absorb \<open>c \<in> S\<close> f1 insertI1 is_ortho_set_def) 
      qed
      thus ?thesis
        by (metis (mono_tags, lifting) c2 class_semiring.add.finprod_all1 mult_hom.hom_zero subset_iff)
    qed
    finally have "\<langle>a, x - k *\<^sub>C a\<rangle> = 0"
      by blast
    hence "\<langle>a, x\<rangle> - \<langle>a, k *\<^sub>C a\<rangle> = 0"
      by (simp add: cinner_diff_right)
    hence "\<langle>a, x\<rangle> = \<langle>a, k *\<^sub>C a\<rangle>"
      by simp
    hence "\<langle>a, x\<rangle> = k * \<langle>a, a\<rangle>"
      by simp
    moreover have "\<langle>a, a\<rangle> = 1"
    proof-
      have "norm \<langle>a, a\<rangle> = 1"
        using norm_eq_sqrt_cinner[where x = a]
        using f3 by auto         
      moreover have "\<langle>a, a\<rangle> \<in> \<real>"
        by (simp add: cinner_real)
      moreover have "\<langle>a, a\<rangle> \<ge> 0"
        using cinner_ge_zero by auto
      ultimately show ?thesis
        using complex_of_real_cmod by force 
    qed
    ultimately show ?thesis by (smt \<open>x - k *\<^sub>C a \<in> cspan S\<close> mult_cancel_left1)
  qed
  show "x \<in> cspan (insert a S)"
    if "x - \<langle>a, x\<rangle> *\<^sub>C a \<in> cspan S"
    using that complex_vector.span_breakdown_eq by auto 
qed

lemma span_set_inner:
  includes notation_norm
  assumes "w \<in> complex_vector.span (set L)" and "distinct L" and "is_ortho_set (set L)" 
      and "\<forall>a\<in>set L. \<parallel>a\<parallel> = 1"
  shows  "w = (\<Sum>b\<in>set L. \<langle>b, w\<rangle> *\<^sub>C b)"
using assms
proof(induction L arbitrary: w)
  case Nil
  hence "w = 0"
    by auto
  moreover have "(\<Sum>b\<in>set []. \<langle>b, w\<rangle> *\<^sub>C b) = 0"
    by simp    
  ultimately show ?case by simp
next
  case (Cons a L)
  have "(\<Sum>b\<in>set (a # L). \<langle>b, w\<rangle> *\<^sub>C b) = (\<Sum>b\<in>insert a (set L). \<langle>b, w\<rangle> *\<^sub>C b)"
    by auto
  also have "\<dots> = \<langle>a, w\<rangle> *\<^sub>C a + (\<Sum>b\<in>(set L). \<langle>b, w\<rangle> *\<^sub>C b)"
    using Cons.prems(2) by auto
  also have "\<dots> = \<langle>a, w\<rangle> *\<^sub>C a + (\<Sum>b\<in>(set L). \<langle>b, w - \<langle>a, w\<rangle> *\<^sub>C a\<rangle> *\<^sub>C b)"
  proof-
    have "b\<in>(set L) \<Longrightarrow> \<langle>b, w - \<langle>a, w\<rangle> *\<^sub>C a\<rangle> = \<langle>b, w\<rangle>" for b
    proof-
      assume "b\<in>(set L)"
      hence "b \<noteq> a"
        using Cons.prems(2) by auto        
      hence g1: "\<langle>b, a\<rangle> = 0"
        by (meson Cons.prems(3) \<open>b \<in> set L\<close> is_ortho_set_def list.set_intros(1) list.set_intros(2))        
      have "\<langle>b, w - \<langle>a, w\<rangle> *\<^sub>C a\<rangle> = \<langle>b, w\<rangle> - \<langle>b, \<langle>a, w\<rangle> *\<^sub>C a\<rangle>"
        using cinner_diff_right by blast
      also have "\<dots> = \<langle>b, w\<rangle> - \<langle>a, w\<rangle> * \<langle>b, a\<rangle>"
        by simp
      also have "\<dots> = \<langle>b, w\<rangle>"
        using g1 by simp
      finally show ?thesis by blast
    qed
    thus ?thesis by simp
  qed
  also have "\<dots> = \<langle>a, w\<rangle> *\<^sub>C a + (w - \<langle>a, w\<rangle> *\<^sub>C a)"
  proof-
    have setaL: "set (a # L) = insert a (set L)"
      by simp
    moreover have "a \<in> sphere 0 1"
      using Cons.prems(4) by auto      
    ultimately have "w - \<langle>a, w\<rangle> *\<^sub>C a \<in> complex_vector.span (set L)"
      using Cons.prems(1) cinner_span_breakdown_eq[where S = "set L" and x = w and a = a]
        Cons.prems(2) Cons.prems(3) distinct.simps(2) 
      by (smt mem_sphere_0) 
    moreover have orthoL: "is_ortho_set (set L)"
      by (metis Cons.prems(3) is_ortho_set_antimono setaL subset_insertI)
    moreover have "\<forall>a\<in>set L. \<parallel>a\<parallel> = 1"
      using Cons.prems(4) by auto      
    ultimately have "(\<Sum>b\<in>(set L). \<langle>b, w - \<langle>a, w\<rangle> *\<^sub>C a\<rangle> *\<^sub>C b) = w - \<langle>a, w\<rangle> *\<^sub>C a"
      using orthoL Cons.IH \<open>\<forall>a\<in>set L. \<parallel>a\<parallel> = 1\<close> \<open>distinct (a # L)\<close> \<open>w - \<langle>a, w\<rangle> *\<^sub>C a \<in> cspan (set L)\<close> by fastforce

    thus ?thesis by simp
  qed
  also have "\<dots> = w"
    by simp
  finally have "(\<Sum>b\<in>set (a # L). \<langle>b, w\<rangle> *\<^sub>C b) = w"
    by blast
  thus "w = (\<Sum>b\<in>set (a # L). \<langle>b, w\<rangle> *\<^sub>C b)" by simp
qed

(* lemma canonical_basis_inner:
  "w = (\<Sum>b\<in>set (canonical_basis::'a::onb_enum list). \<langle>b, w\<rangle> *\<^sub>C b)"
  apply (rule onb_expansion_finite)
  using is_generator_set by (auto simp add: is_orthonormal is_normal) *)

lemma basis_enum_of_vec_expansion:  
  fixes S::"'a::basis_enum list" and L::"complex list"
  assumes "length S = length L" and "distinct S"
  shows   "sum_list (map2 (\<lambda>l s. l *\<^sub>C s) L S)
             = (\<Sum>i\<in>{0..<length S}. L!i *\<^sub>C S!i)"
  using assms sum_list_sum_nth[where xs = "map2 (*\<^sub>C) L S"]
  by auto

(* lemma length_list_of_vec_vec_of_basis_enum_list:
  fixes w::"'a::{basis_enum,complex_inner}" and S::"'a list"
  shows "length (list_of_vec (vec_of_basis_enum_list S w i)) = length (canonical_basis::'a list)"
  by (simp add: dim_vec_of_basis_enum_list) *)

(* lemma list_of_vec_unit_vec:
  defines "basis == canonical_basis::'a::basis_enum list"
  assumes "length basis \<ge> 1"
  shows "list_of_vec (c \<cdot>\<^sub>v unit_vec (length basis) (length basis-1))!(length basis-1) = (c::complex)"
proof-
  have "c \<cdot>\<^sub>v
  unit_vec (length basis) 
  (length basis - 1)
   = Matrix.vec (length basis)
     (\<lambda>j. if j = length basis - 1 then c
          else 0)"
    unfolding smult_vec_def unit_vec_def mk_vec_def 
    by auto
  hence "list_of_vec (c \<cdot>\<^sub>v unit_vec (length (basis)) 
  (length basis -1))
   = list_of_vec (Matrix.vec (length basis)
     (\<lambda>j. if j = length basis - 1 then c else 0) )"
    by simp
  hence "list_of_vec (c \<cdot>\<^sub>v unit_vec (length basis) 
  (length basis - 1))!(length basis - 1)
   = list_of_vec (Matrix.vec (length basis)
     (\<lambda>j. if j = length basis - 1 then c
          else 0) )!(length basis - 1)"
    by simp
  also have "\<dots> = c"
  proof-
    have "[0..<length basis] !
    (length basis - Suc 0) = length basis - Suc 0"
      unfolding basis_def
      using assms by auto      
    thus ?thesis unfolding basis_def using assms by auto
  qed
  finally show ?thesis 
    unfolding basis_def
    using assms(1) by blast    
qed *)

lemma independent_length_leq:
  defines "basis == canonical_basis::'a::basis_enum list"
  assumes f1: "complex_vector.independent (set (S::'a list))"
    and f2: "distinct S"
  shows "length S \<le> length basis"
proof(rule classical)
  have h1: "finite (set S)"
    by simp
  assume "\<not>(length S \<le> length basis)"
  hence "length S > length basis"
    by simp
  hence g1: "card (set S) > card (set basis)"
    unfolding basis_def
    by (simp add: distinct_card f2)
  have "finite (set basis)"
    by simp    
  hence "complex_vector.span (set basis) = (UNIV:: 'a set)"
    using basis_def is_generator_set
    using basis_def  is_generator_set by blast
  hence g2: "card (set S) > cdim (UNIV:: 'a set)"
    by (metis \<open>length basis < length S\<close> basis_def cdim_UNIV_basis_enum distinct_card f2)

  hence "complex_vector.span (set S) \<subseteq> (UNIV:: 'a set)"
    by simp
  hence "card (set S) \<le> cdim (UNIV:: 'a set)"
    using f1 h1 cdependent_raw_def 
      complex_vector.dim_le_card complex_vector.dim_span_eq_card_independent 
      distinct_canonical_basis distinct_card f2 
    by (smt \<open>cspan (set basis) = UNIV\<close> \<open>\<not> length S \<le> length basis\<close> 
        \<open>finite (set basis)\<close> basis_def) 
  thus ?thesis using g2 by (smt leD)
qed


lemma basis_enum_of_vec_inverse[simp]:
  fixes w::"'a::basis_enum"
  shows  "basis_enum_of_vec (vec_of_basis_enum w) = w"
  unfolding vec_of_basis_enum_def basis_enum_of_vec_def basis_enum_of_vec_list_def'
  unfolding list_vec zip_map1 zip_same_conv_map map_map 
  apply (simp add: o_def)
  apply (subst sum.distinct_set_conv_list[symmetric], simp)
  apply (rule complex_vector.sum_representation_eq)
  apply (simp add: is_cindependent_set)    
  using  is_generator_set apply auto[1]
  apply simp
  by simp

lemma uniq_linear_expansion_sum_list_zero:
  fixes f::"'a::{basis_enum} \<Rightarrow> complex"
  defines  "basis == (canonical_basis::'a list)"
  assumes h0: "sum_list (map2 (*\<^sub>C) (map f basis) basis) = 0"
    and h1: "b \<in> set basis"
  shows "f b = 0"
proof-
  have a1: "distinct basis"
    by (simp add: basis_def)    
  have "sum_list (map2 (*\<^sub>C) (map f basis) basis) = (\<Sum>x\<leftarrow>basis. f x *\<^sub>C x)"
    by (metis (no_types) map2_map_map map_ident)
  also have "\<dots> = (\<Sum>x\<in>set basis. f x *\<^sub>C x)"
    using a1
    by (simp add: sum_list_distinct_conv_sum_set) 
  also have "\<dots> = f b *\<^sub>C b + (\<Sum>x\<in>(set basis)-{b}. f x *\<^sub>C x)"
    by (meson List.finite_set h1 sum.remove)
  finally have "sum_list (map2 (*\<^sub>C) (map f basis) basis)
              = f b *\<^sub>C b + (\<Sum>x\<in>(set basis)-{b}. f x *\<^sub>C x)"
    by blast
  hence "f b *\<^sub>C b + (\<Sum>x\<in>(set basis)-{b}. f x *\<^sub>C x) = 0"
    using h0 by auto
  hence "(-f b) *\<^sub>C b = (\<Sum>x\<in>(set basis)-{b}. f x *\<^sub>C x)"
    using add.inverse_unique by auto
  hence s1: "(-f b) *\<^sub>C b \<in> complex_vector.span ((set basis)-{b})"
    by (metis (no_types, lifting) complex_vector.span_base complex_vector.span_scale complex_vector.span_sum)
  have "(-f b) *\<^sub>C b = 0"
  proof(rule classical)
    assume "\<not>((-f b) *\<^sub>C b = 0)"
    hence s2: "(-f b) *\<^sub>C b \<noteq> 0"
      by simp
    hence "b \<noteq> 0"
      by simp
    have s3: "-f b \<noteq> 0"
      using s2 by simp
    have "(inverse (-f b)) *\<^sub>C ((-f b) *\<^sub>C b) \<in> complex_vector.span ((set basis)-{b})"
      using s1 by (smt complex_vector.span_scale)
    hence "b \<in> complex_vector.span ((set basis)-{b})"
      using s3 
      by (metis add_diff_cancel_right' complex_vector.scale_right_diff_distrib 
          complex_vector_eq_affinity)
    hence "complex_vector.dependent (set basis)"
      using complex_vector.dependent_def[where P = "set basis"]
        h1 by blast
    moreover have "complex_vector.independent (set basis)"
      using basis_def calculation is_cindependent_set
      by blast 
    ultimately show ?thesis 
      by (metis cdependent_raw_def)
  qed
  moreover have "b \<noteq> 0"  
    using complex_vector.dependent_zero[where A = "set basis"]
      h1 is_cindependent_set unfolding basis_def
    by blast
  ultimately have "-f b = 0"
    by simp
  thus ?thesis by simp
qed

lemma uniq_linear_expansion_sum_list:
  fixes f g::"'a::{basis_enum} \<Rightarrow> complex"
  defines  "basis == (canonical_basis::'a list)"
  assumes h0: "sum_list (map2 (*\<^sub>C) (map f basis) basis)
             = sum_list (map2 (*\<^sub>C) (map g basis) basis)"
    and h1: "b \<in> set basis"
  shows "f b = g b"
proof-
  have a1: "sum_list (map2 (*\<^sub>C) (map f basis) basis)
      = (\<Sum>x\<leftarrow>basis. f x *\<^sub>C x)"
    by (metis (no_types) map2_map_map map_ident)
  have a2: "sum_list (map2 (*\<^sub>C) (map g basis) basis)
      = (\<Sum>x\<leftarrow>basis. g x *\<^sub>C x)"
    by (metis (no_types) map2_map_map map_ident)
  have a3: "sum_list (map2 (*\<^sub>C) (map (\<lambda>x. f x - g x) basis) basis)
      = (\<Sum>x\<leftarrow>basis. (f x - g x) *\<^sub>C x)"
    by (metis (no_types) map2_map_map map_ident)
  have a4: "(\<Sum>x\<leftarrow>basis. (f x - g x) *\<^sub>C x) = (\<Sum>x\<leftarrow>basis. f x *\<^sub>C x) - (\<Sum>x\<leftarrow>basis. g x *\<^sub>C x)"
    by (simp add: scaleC_left.diff sum_list_subtractf)    
  have "0 = sum_list (map2 (*\<^sub>C) (map f basis) basis)
          - sum_list (map2 (*\<^sub>C) (map g basis) basis)"
    by (simp add: h0)
  also have "\<dots> = sum_list (map2 (*\<^sub>C) (map (\<lambda>x. f x - g x) basis) basis)"
    using a1 a2 a3 a4 by auto 
  finally have "0 = sum_list (map2 (*\<^sub>C) (map (\<lambda>x. f x - g x) basis) basis)".
  hence "sum_list (map2 (*\<^sub>C) (map (\<lambda>x. f x - g x) basis) basis) = 0"
    by simp
  hence "(\<lambda>x. f x - g x) b = 0"
    using uniq_linear_expansion_sum_list_zero[where f = "(\<lambda>x. f x - g x)"]
      basis_def h1 by blast
  thus ?thesis by simp
qed

lemma basis_enum_of_vec_inverse'[simp]:
  fixes v::"complex vec"
  defines "n == canonical_basis_length TYPE('a::basis_enum)"
  assumes f1: "dim_vec v = n"
  shows "vec_of_basis_enum ((basis_enum_of_vec v)::'a) = v"
proof- 
  define w where "w = list_of_vec v"
  define basis where "basis = (canonical_basis::'a list)"
  have length_w: "length w = dim_vec v"
    using f1 unfolding w_def
    by simp 
  hence length_basis: "length basis = length w"
    by (simp add: basis_def f1 n_def)    
  have "map (crepresentation (set basis) (basis_enum_of_vec_list basis w)) basis = w"
  proof-
    have "i < length basis \<Longrightarrow> 
        crepresentation (set basis) (basis_enum_of_vec_list basis w) (basis!i) = w!i"
      for i
    proof-
      assume h1: "i < length basis"
      have h2: "cindependent (set basis)"
        by (simp add: basis_def is_cindependent_set)
      have h3: "basis_enum_of_vec_list basis w \<in> cspan (set basis)"
        using basis_def is_generator_set
          by blast 
      define f where 
        "f x = crepresentation (set basis) (basis_enum_of_vec_list basis w) x"
      for x
      have h4: "f x \<noteq> 0 \<Longrightarrow> x \<in> set basis" for x
        by (simp add: complex_vector.representation_ne_zero f_def)
      have h5: "finite {v. f v \<noteq> 0}"
        by (metis \<open>f \<equiv> crepresentation (set basis) 
            (basis_enum_of_vec_list basis w)\<close> complex_vector.finite_representation)
      have h6: "(\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = basis_enum_of_vec_list basis w"
        by (simp add: \<open>f \<equiv> crepresentation (set basis) (basis_enum_of_vec_list basis w)\<close> basis_def complex_vector.sum_nonzero_representation_eq is_cindependent_set is_generator_set)
      have h7: "distinct basis"
        by (simp add: basis_def)
      have "(\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = (\<Sum>v\<in>set basis. f v *\<^sub>C v)"
        by (simp add: h4 subset_eq sum.mono_neutral_cong_left)
      also have "\<dots> = sum_list (map (\<lambda>x. f x *\<^sub>C x) basis)"
        using Groups_List.monoid_add_class.sum_list_distinct_conv_sum_set
        by (simp add: sum_list_distinct_conv_sum_set h7)        
      also have "\<dots> = (\<Sum>b\<leftarrow>basis. f b *\<^sub>C b)"
        by simp
      finally have "(\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = (\<Sum>b\<leftarrow>basis. f b *\<^sub>C b)"
        by (simp add: \<open>(\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = (\<Sum>v\<in>set basis. f v *\<^sub>C v)\<close> 
            \<open>(\<Sum>v\<in>set basis. f v *\<^sub>C v) = (\<Sum>x\<leftarrow>basis. f x *\<^sub>C x)\<close>)
      define g where "g b = w!(SOME i::nat. i < n \<and> basis!i = b)" for b
      have e1: "i < n \<Longrightarrow>  w!i = g (basis!i)" for i
        unfolding g_def
        by (smt basis_def distinct_Ex1 f1 h1 h7 le_neq_implies_less length_basis length_list_of_vec less_not_refl mem_Collect_eq nth_mem set_conv_nth someI_ex sup.strict_order_iff sup_ge2 w_def) 
      have "sum_list (map2 (*\<^sub>C) (map f basis) basis)
            = (\<Sum>b\<leftarrow>basis. f b *\<^sub>C b)"
        by (metis (mono_tags, lifting) basis_def distinct_canonical_basis list.map_ident 
            map2_map_map sum.cong sum_list_distinct_conv_sum_set)        
      also have "(\<Sum>b\<leftarrow>basis. f b *\<^sub>C b) 
            = basis_enum_of_vec_list basis w"
        using \<open>(\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = (\<Sum>b\<leftarrow>basis. f b *\<^sub>C b)\<close> h6 by auto
      also have "\<dots> = sum_list (map2 (*\<^sub>C) w basis)"
        by (simp add: basis_enum_of_vec_list_def')      
      also have "\<dots> = (\<Sum>i\<leftarrow>[0..<n]. w!i *\<^sub>C (basis!i))"
        by (smt basis_def f1 length_w map2_map_map map_eq_conv map_nth n_def)
      also have "\<dots> = (\<Sum>i\<leftarrow>[0..<n]. g (basis!i) *\<^sub>C (basis!i))"
      proof-
        have "i < n \<Longrightarrow>  w!i *\<^sub>C (basis!i) = g (basis!i) *\<^sub>C (basis!i)" for i
          using e1
          by simp 
        hence "(\<Sum>i=0..<n. w ! i *\<^sub>C basis ! i) =
               (\<Sum>i=0..<n. g (basis ! i) *\<^sub>C basis ! i)"
          by (meson sum.ivl_cong)
        thus ?thesis
          by (metis (no_types, lifting) atLeastLessThan_upt interv_sum_list_conv_sum_set_nat)
      qed
      also have "\<dots> = (\<Sum>b\<leftarrow>basis. g b *\<^sub>C b)"
        unfolding n_def basis_def
        by (smt length_map map_nth nth_equalityI nth_map) 
      also have "\<dots> = sum_list (map2 (*\<^sub>C) (map g basis) basis)"
        by (metis (no_types) map2_map_map map_ident)
      finally have "sum_list (map2 (*\<^sub>C) (map f basis) basis)
                  = sum_list (map2 (*\<^sub>C) (map g basis) basis)"
        by blast
      hence "f (basis!i) = g (basis!i)"
        using basis_def h1 nth_mem[where n = i and xs = "basis"] 
          uniq_linear_expansion_sum_list[where b = "basis ! i"]
        by auto        
      hence "f (basis!i) = w!i"
        using e1 f1 h1 length_basis length_w by auto        
      thus ?thesis unfolding f_def.
    qed
    thus ?thesis 
      by (smt length_basis length_map nth_equalityI nth_map)
  qed
  thus ?thesis
    unfolding basis_def
    by (simp add: basis_enum_of_vec_def vec_list vec_of_basis_enum_def w_def assms)
qed

lemma vec_of_basis_enum_add:
  "vec_of_basis_enum (b1 + b2) = vec_of_basis_enum b1 + vec_of_basis_enum b2"
proof-
  have "cspan
         (set (canonical_basis::'a list)) = UNIV"
    using closure_finite_cspan is_generator_set
    by simp
  hence "crepresentation (set (canonical_basis::'a list)) (b1+b2) i
      = crepresentation (set (canonical_basis::'a list)) b1 i + 
        crepresentation (set (canonical_basis::'a list)) b2 i" for i
  proof -
    have "cindependent (set (canonical_basis::'a list))"
      using is_cindependent_set
      by (simp add: ) 
    thus ?thesis
      by (metis UNIV_I \<open>cspan (set canonical_basis) = UNIV\<close> complex_vector.representation_add) (* failed *)
  qed 
  moreover have "vec_of_list (map (\<lambda>x. f x + g x) S) = vec_of_list (map f S) + vec_of_list (map g S)"
    for S::"'a list" and f g::"'a \<Rightarrow> complex" 
  proof (induction S)
    case Nil
    thus ?case by auto
  next
    case (Cons a S)
    have "vec_of_list (map (\<lambda>x. f x + g x) (a # S)) = 
      vCons (f a + g a)
     (map_vec (\<lambda>x. f x + g x) (vec_of_list S))"
      by auto
    also have "\<dots> = vCons (f a + g a)
     (map_vec f (vec_of_list S) + map_vec g (vec_of_list S))"
      by auto
    also have "\<dots> =  vec_of_list (map f (a#S)) + vec_of_list (map g (a#S))"
    proof auto
      have "dim_vec A = n \<Longrightarrow> dim_vec B = n \<Longrightarrow> 
            vCons (p + q) (A + B) = vCons p A + vCons q B"
        for p q::complex and A B and n
      proof-
        assume d1: "dim_vec A = n" and d2: "dim_vec B = n"
        hence d3: "dim_vec (A + B) = n"
          by simp
        have d4: "dim_vec (vCons (p + q) (A + B)) = Suc n"
          using d3 by auto
        have d5': "dim_vec  (vCons p A) = Suc n"
          by (simp add: d1)          
        moreover have d5'': "dim_vec  (vCons q B) = Suc n"
          by (simp add: d2)          
        ultimately have d5: "dim_vec  (vCons p A + vCons q B) = Suc n"
          by simp
        have "i < Suc n \<Longrightarrow> vCons (p + q) (A + B) $ i = (vCons p A + vCons q B) $ i"
          for i
          using d5'' index_add_vec(1) less_Suc_eq_0_disj by auto
        thus ?thesis
          using d4 
          by auto 
      qed
      thus "vCons (f a + g a)
     (map_vec f (vec_of_list S) + map_vec g (vec_of_list S)) =
    vCons (f a) (map_vec f (vec_of_list S)) +
    vCons (g a) (map_vec g (vec_of_list S))"
        by simp         
    qed
    finally show ?case
      by simp 
  qed
  ultimately show ?thesis 
    unfolding vec_of_basis_enum_def 
    by auto
qed

lemma vec_of_basis_enum_scaleC:
  "vec_of_basis_enum (c *\<^sub>C b) = c \<cdot>\<^sub>v (vec_of_basis_enum b)"
proof-
  have "cspan
         (set (canonical_basis::'a list)) = UNIV"    
    using closure_finite_cspan is_generator_set
    by simp
  hence "crepresentation (set (canonical_basis::'a list)) (c *\<^sub>C b) i
      = c *\<^sub>C (crepresentation (set (canonical_basis::'a list)) b i)" for i
    using complex_vector.representation_scale
      cdependent_raw_def UNIV_I complex_scaleC_def
     is_cindependent_set 
    by smt
  moreover have "vec_of_list (map (\<lambda>x. c *\<^sub>C (f x)) S) = c \<cdot>\<^sub>v vec_of_list (map f S)"
    for S::"'a list" and f g::"'a \<Rightarrow> complex" 
  proof(induction S)
    case Nil
    thus ?case by auto
  next
    case (Cons a S)
    have "vec_of_list (map (\<lambda>x. c *\<^sub>C f x) (a # S)) = 
      vCons (c *\<^sub>C f a)
     (map_vec (\<lambda>x. c *\<^sub>C f x) (vec_of_list S))"
      by auto
    also have "\<dots> = c \<cdot>\<^sub>v vCons (f a) (map_vec f (vec_of_list S))"
      by (metis Cons.IH complex_scaleC_def list.simps(9) list_of_vec_mult list_of_vec_vCons vec_list
          vec_of_list_map)      
    also have "\<dots> =  c \<cdot>\<^sub>v (vec_of_list (map f (a#S)))"
      by simp    
    finally show ?case
      by simp 
  qed
  ultimately show ?thesis 
    unfolding vec_of_basis_enum_def 
    by auto
qed

lemma vec_of_basis_enum_scaleR:
  "vec_of_basis_enum (r *\<^sub>R b) = complex_of_real r \<cdot>\<^sub>v (vec_of_basis_enum b)"
  by (simp add: scaleR_scaleC vec_of_basis_enum_scaleC)

lemma vec_of_basis_enum_uminus:
  "vec_of_basis_enum (- b2) = - vec_of_basis_enum b2"
  unfolding scaleC_minus1_left[symmetric, of b2]
  unfolding scaleC_minus1_left_vec[symmetric]
  by (rule vec_of_basis_enum_scaleC)

lemma sum_list_orthonormal:
  assumes  "length xs = length ys"
    and "length ys = length B" 
    and "is_ortho_set (set B)"
    and "distinct B"
    and "set B \<subseteq> sphere 0 1"
  shows "\<langle>sum_list (map2 (*\<^sub>C) xs B), sum_list (map2 (*\<^sub>C) ys B)\<rangle> 
       = sum_list (map2 (\<lambda>x. (*) (cnj x)) xs ys)"
proof-
  have is_ortho_setsum_list_map2_zero:
    "\<langle>b, sum_list (map2 (*\<^sub>C) ys B)\<rangle> = 0"
    if "length ys = length B"
      and "is_ortho_set (set (b#B))"
      and "distinct (b#B)"
    for b::'a and B::"'a list" and ys
    using that proof(induction ys B rule: list_induct2)
    case Nil
    show ?case by auto
  next
    case (Cons x xs b' B)
    have "b \<noteq> b'"
      using Cons.prems(2) by auto    
    hence h1: "\<langle>b, b'\<rangle> = 0"
      by (meson Cons.prems is_ortho_set_def list.set_intros(1) list.set_intros(2))
    have "\<langle>b, sum_list (map2 (*\<^sub>C) (x # xs) (b' # B))\<rangle> = \<langle>b, x *\<^sub>C b' + sum_list (map2 (*\<^sub>C) xs B)\<rangle>"
      by simp
    also have "\<dots> = \<langle>b, x *\<^sub>C b'\<rangle> + \<langle>b, sum_list (map2 (*\<^sub>C) xs B)\<rangle>"
      by (simp add: cinner_add_right)
    also have "\<dots> = x * \<langle>b, b'\<rangle> + \<langle>b, sum_list (map2 (*\<^sub>C) xs B)\<rangle>"
      by simp
    also have "\<dots> = \<langle>b, sum_list (map2 (*\<^sub>C) xs B)\<rangle>"
      using h1 by simp
    also have "\<dots> = 0"
      using Cons.IH Cons.prems(1) Cons.prems(2) distinct_length_2_or_more is_ortho_set_def list.set_intros(1) list.set_intros(2) set_ConsD
      by (simp add: is_ortho_set_def)
    finally have "\<langle>b, sum_list (map2 (*\<^sub>C) (x # xs) (b' # B))\<rangle> = 0"
      .
    thus ?case .
  qed
  show ?thesis
    using assms
  proof(induction xs ys B rule: list_induct3)
    case Nil show ?case by auto
  next
    case (Cons x xs y ys b B)
    have h1: "is_ortho_set (set B)"
      by (meson Cons.prems(1) is_ortho_set_antimono set_subset_Cons)
    have h2: "set B \<subseteq> sphere 0 1"
      using Cons.prems(3) by auto
    have h3: "distinct B"
      using Cons.prems(2) by auto
    have " \<langle>sum_list (map2 (*\<^sub>C) (x # xs)
        (b # B)), sum_list (map2 (*\<^sub>C) (y # ys) (b # B))\<rangle> =
    \<langle>x *\<^sub>C b + sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b + sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by auto
    also have "\<dots> = \<langle>x *\<^sub>C b, y *\<^sub>C b + sum_list (map2 (*\<^sub>C) ys B)\<rangle>
                + \<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b + sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by (simp add: cinner_add_left)
    also have "\<dots> = \<langle>x *\<^sub>C b, y *\<^sub>C b\<rangle>
                 +\<langle>x *\<^sub>C b, sum_list (map2 (*\<^sub>C) ys B)\<rangle>
                + \<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b + sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by (simp add: cinner_add_right)
    also have "\<dots> = \<langle>x *\<^sub>C b, y *\<^sub>C b\<rangle>
                 +\<langle>x *\<^sub>C b, sum_list (map2 (*\<^sub>C) ys B)\<rangle>
                 +\<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b\<rangle>
                 +\<langle>sum_list (map2 (*\<^sub>C) xs B), sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by (simp add: cinner_add_right)
    also have "\<dots> = cnj x * y * \<langle>b, b\<rangle>
                 +cnj x * \<langle>b, sum_list (map2 (*\<^sub>C) ys B)\<rangle>
                 + y * \<langle>sum_list (map2 (*\<^sub>C) xs B), b\<rangle>
                 +\<langle>sum_list (map2 (*\<^sub>C) xs B), sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by auto
    also have "\<dots> = cnj x * y                 
                 +\<langle>sum_list (map2 (*\<^sub>C) xs B), sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
    proof-
      have "b\<in>sphere 0 1"
        using Cons.prems(3) by auto
      hence "norm b = 1"
        by simp
      hence "(norm b)^2 = 1"
        by simp
      hence "\<langle>b, b\<rangle> = 1"
        by (simp add: cdot_square_norm)
      moreover have "\<langle>b, sum_list (map2 (*\<^sub>C) ys B)\<rangle> = 0"
        using Cons.hyps(2) Cons.prems(1) Cons.prems(2) 
          is_ortho_setsum_list_map2_zero[where B = B and b = b and ys = ys]
        by blast
      moreover have "\<langle>sum_list (map2 (*\<^sub>C) xs B), b\<rangle> = 0"
        using  is_ortho_setsum_list_map2_zero
        by (metis Cons.hyps(1) Cons.hyps(2) Cons.prems(1) Cons.prems(2) cinner_commute' complex_cnj_zero)
      ultimately show ?thesis by simp
    qed
    also have "\<dots> =  sum_list (map2 (\<lambda>x. (*) (cnj x)) (x # xs) (y # ys))"
      using h1 h3 h2 Cons.IH by auto
    finally have " \<langle>sum_list (map2 (*\<^sub>C) (x # xs)
        (b # B)), sum_list (map2 (*\<^sub>C) (y # ys) (b # B))\<rangle> =
    sum_list (map2 (\<lambda>x. (*) (cnj x)) (x # xs) (y # ys))"
      .
    thus ?case .
  qed
qed


lemma vec_of_basis_enum_minus:
  "vec_of_basis_enum (b1 - b2) = vec_of_basis_enum b1 - vec_of_basis_enum b2"
  by (metis (mono_tags, hide_lams) carrier_vec_dim_vec diff_conv_add_uminus diff_zero index_add_vec(2) minus_add_uminus_vec vec_of_basis_enum_add vec_of_basis_enum_uminus)

lemma cinner_onb_enum_of_vec:
  defines "n == canonical_basis_length TYPE('a::onb_enum)"
  assumes w1: "dim_vec x = n" and w2: "dim_vec y = n"
  shows  "\<langle>(basis_enum_of_vec::_\<Rightarrow> 'a) x, (basis_enum_of_vec::_\<Rightarrow> 'a) y\<rangle>
           = y \<bullet>c x"
proof -
  include notation_norm
  define B where "B = (canonical_basis::'a list)"
  have a0: "\<langle>basis_enum_of_vec_list B xs, basis_enum_of_vec_list B ys\<rangle> = 
    sum_list (map2 (\<lambda>x y. cnj x * y) xs ys)"
    if "length xs = length ys" and "length ys = length B"
      and "is_ortho_set (set B)" and "complex_vector.span (set B) = UNIV"
      and "distinct B" and "\<And>t. t\<in>set B \<Longrightarrow> \<parallel>t\<parallel> = 1"
    for xs ys and B :: "'a list"
    unfolding basis_enum_of_vec_list_def'
    using that
  proof (induction xs ys B rule:list_induct3)
    case Nil thus ?case by auto
  next
    case (Cons x xs y ys b B)
    have w1: "distinct B"      
      using Cons.prems(3) by auto 
    have "length xs = length B"
      by (simp add: Cons.hyps(1) Cons.hyps(2))
    moreover have "b \<notin> set B"
      using Cons.prems(3) by auto      
    moreover have "is_ortho_set (set (b#B))"
      using Cons.prems(1) 
      by simp
    ultimately have braket0: "\<langle>sum_list (map2 (*\<^sub>C) xs B), b\<rangle> = 0"
    proof (induction xs B rule:list_induct2)
      case Nil thus ?case by auto
    next
      case (Cons x xs b' B)
      have "b' \<noteq> b"
        using Cons.prems by auto
      have  "is_ortho_set (set (b'#(b#B)))"
        using Cons.prems(2)
        by (simp add: insert_commute) 
      hence b2: "is_ortho_set (set (b#B))"
        by (meson is_ortho_set_antimono set_subset_Cons)
      have b1: "\<langle>b', b\<rangle> = 0"
        by (meson Cons.prems(2) \<open>b' \<noteq> b\<close> is_ortho_set_def list.set_intros(1) list.set_intros(2))
      have "\<langle>sum_list (map2 (*\<^sub>C) (x # xs) (b' # B)), b\<rangle> = \<langle>x *\<^sub>C b' + sum_list (map2 (*\<^sub>C) xs B), b\<rangle>"
        by auto
      also have "\<dots> = \<langle>x *\<^sub>C b', b\<rangle> + \<langle>sum_list (map2 (*\<^sub>C) xs B), b\<rangle>"
        by (simp add: cinner_add_left)
      also have "\<dots> = \<langle>x *\<^sub>C b', b\<rangle>"
        using Cons.IH Cons.prems b2 by simp
      also have "\<dots> = cnj x * \<langle>b', b\<rangle>"
        by simp
      also have "\<dots> = 0"
        using b1 by simp
      finally show ?case .
    qed
    have "length ys = length B"
      by (simp add: Cons.hyps(1) Cons.hyps(2))
    moreover have "b \<notin> set B"
      using \<open>b \<notin> set B\<close> by auto      
    moreover have "is_ortho_set (set (b#B))"
      using Cons.prems(1) by auto
    ultimately have braket1: "\<langle>sum_list (map2 (*\<^sub>C) ys B), b\<rangle> = 0"
    proof (induction ys B rule:list_induct2)
      case Nil thus ?case by auto
    next
      case (Cons x xs b' B)
      have "b' \<noteq> b"
        using Cons.prems by auto
      have  "is_ortho_set (set (b'#(b#B)))"
        using Cons.prems(2)
        by (simp add: insert_commute) 
      hence b2: "is_ortho_set (set (b#B))"
        by (meson is_ortho_set_antimono set_subset_Cons)
      have b1: "\<langle>b', b\<rangle> = 0"
        by (meson Cons.prems(2) \<open>b' \<noteq> b\<close> is_ortho_set_def list.set_intros(1) list.set_intros(2))
      have "\<langle>sum_list (map2 (*\<^sub>C) (x # xs) (b' # B)), b\<rangle> = \<langle>x *\<^sub>C b' + sum_list (map2 (*\<^sub>C) xs B), b\<rangle>"
        by auto
      also have "\<dots> = \<langle>x *\<^sub>C b', b\<rangle> + \<langle>sum_list (map2 (*\<^sub>C) xs B), b\<rangle>"
        by (simp add: cinner_add_left)
      also have "\<dots> = \<langle>x *\<^sub>C b', b\<rangle>"
        using Cons.IH Cons.prems b2 by simp
      also have "\<dots> = cnj x * \<langle>b', b\<rangle>"
        by simp
      also have "\<dots> = 0"
        using b1 by simp
      finally show ?case .
    qed

    have "\<langle>sum_list (map2 (*\<^sub>C) (x # xs) (b # B)), 
           sum_list (map2 (*\<^sub>C) (y # ys) (b # B))\<rangle> =
    \<langle>x *\<^sub>C b + sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b + sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by auto
    also have "\<dots> =
    \<langle>x *\<^sub>C b, y *\<^sub>C b + sum_list (map2 (*\<^sub>C) ys B)\<rangle>
   +\<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b + sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by (simp add: cinner_add_left)
    also have "\<dots> =
    \<langle>x *\<^sub>C b, y *\<^sub>C b\<rangle>
   + \<langle>x *\<^sub>C b, sum_list (map2 (*\<^sub>C) ys B)\<rangle>
   +\<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b + sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by (simp add: cinner_add_right)
    also have "\<dots> =
    \<langle>x *\<^sub>C b, y *\<^sub>C b\<rangle>
   +\<langle>x *\<^sub>C b, sum_list (map2 (*\<^sub>C) ys B)\<rangle>
   +\<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b\<rangle>
   +\<langle>sum_list (map2 (*\<^sub>C) xs B), sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by (simp add: cinner_add_right)
    also have "\<dots> =
    \<langle>x *\<^sub>C b, y *\<^sub>C b\<rangle>
   +\<langle>x *\<^sub>C b, sum_list (map2 (*\<^sub>C) ys B)\<rangle>   
   +\<langle>sum_list (map2 (*\<^sub>C) xs B), sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
    proof-
      have "\<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b\<rangle> = 0"
        by (simp add: braket0)        
      thus ?thesis by simp
    qed
    also have "\<dots> =
    \<langle>x *\<^sub>C b, y *\<^sub>C b\<rangle>
   +\<langle>sum_list (map2 (*\<^sub>C) xs B), sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
    proof-
      have "\<langle>sum_list (map2 (*\<^sub>C) ys B), b\<rangle> = 0"
        using braket1 by simp
      hence "\<langle>sum_list (map2 (*\<^sub>C) ys B), x *\<^sub>C b\<rangle> = 0"
        by simp        
      hence "\<langle>x *\<^sub>C b, sum_list (map2 (*\<^sub>C) ys B)\<rangle> = 0"
        by (metis cinner_commute' complex_cnj_zero)        
      thus ?thesis by simp
    qed
    also have "\<dots> = sum_list (map2 (\<lambda>x. (*) (cnj x)) (x # xs) (y # ys))"
    proof auto
      have "norm b = 1"
        by (simp add: Cons.prems(4))               
      hence "(norm b)^2 = 1"
        by simp
      hence "\<langle>b, b\<rangle> = 1"
        by (simp add: cdot_square_norm)
      moreover have "\<langle>sum_list (map2 (*\<^sub>C) xs B), 
                      sum_list (map2 (*\<^sub>C) ys B)\<rangle> =
      sum_list (map2 (\<lambda>x. (*) (cnj x)) xs ys)"
        apply(rule sum_list_orthonormal)
            apply (simp add: Cons.hyps(1))
           apply (simp add: Cons.hyps(2))
        using Cons.prems(1) apply auto[1]
        apply (metis is_ortho_set_antimono list.simps(15) set_subset_Cons)
        apply (simp add: w1)
        by (simp add: Cons.prems(4) subsetI)
      ultimately show " y * (cnj x * \<langle>b, b\<rangle>) +
    \<langle>sum_list (map2 (*\<^sub>C) xs B), sum_list (map2 (*\<^sub>C) ys B)\<rangle> =
    cnj x * y + sum_list (map2 (\<lambda>x. (*) (cnj x)) xs ys)" 
        by simp
    qed
    finally have "\<langle>sum_list (map2 (*\<^sub>C) (x # xs) (b # B)),
           sum_list (map2 (*\<^sub>C) (y # ys) (b # B))\<rangle> =
    sum_list (map2 (\<lambda>x. (*) (cnj x)) (x # xs) (y # ys))"
      by simp
    thus ?case .      
  qed

  have "length (list_of_vec x) = length (list_of_vec y)"
    by (simp add: assms)    
  hence a2: "sum_list (map2 (\<lambda>x. (*) (cnj x)) (list_of_vec x) (list_of_vec y))
         = (\<Sum>i = 0..<dim_vec x. cnj (vec_index x i) * (vec_index y i))"
  proof(induction "list_of_vec x" "list_of_vec y" arbitrary: x y rule: list_induct2)
    case Nil
    have "dim_vec x = 0"
      by (metis Nil.hyps(1) length_list_of_vec list.size(3))
    thus ?case by auto
  next
    case (Cons x' xs' y' ys')
    have "sum_list (map2 (\<lambda>t. (*) (cnj t)) (list_of_vec x) (list_of_vec y)) =
          sum_list (map2 (\<lambda>t. (*) (cnj t)) (x' # xs') (y' # ys'))"
      by (simp add: Cons.hyps(3) Cons.hyps(4))
    also have "\<dots> = (cnj x')*y' + sum_list (map2 (\<lambda>t. (*) (cnj t)) xs' ys')"
      by auto     
    also have "\<dots> = (\<Sum>i = 0..<dim_vec x. cnj (vec_index x i) * (vec_index y i))"
    proof-     
      define a where "a = vec_of_list xs'"
      define b where "b = vec_of_list ys'"
      have xs'1: "xs' = list_of_vec a"
        unfolding a_def
        by (simp add: list_vec)
      moreover have ys'1: "ys' = list_of_vec b"
        unfolding b_def
        by (simp add: list_vec)
      ultimately have "sum_list (map2 (\<lambda>x. (*) (cnj x)) (list_of_vec a) (list_of_vec b)) =
            (\<Sum>i = 0..<dim_vec a. cnj (vec_index a i) * (vec_index b i))"
        using Cons.hyps(2) by blast        
      hence h1: "(\<Sum>i = 0..<length xs'. cnj (xs' ! i) * ys' ! i) =
                sum_list (map2 (\<lambda>t. (*) (cnj t)) xs' ys')"
        using xs'1 ys'1
        by (metis (no_types, lifting) a_def b_def length_list_of_vec sum.cong vec_of_list_index) 
      have "(\<Sum>i = 0..<dim_vec x. cnj (vec_index x i) * (vec_index y i))
          = (\<Sum>i = 0..<length (x'#xs'). cnj ((x'#xs')!i) * ((y'#ys')!i))"
        by (metis (no_types, lifting) Cons.hyps(3) Cons.hyps(4) length_list_of_vec list_of_vec_index
            sum.cong)
      also have "\<dots> = (\<Sum>i = 0..<Suc (length xs'). cnj ((x'#xs')!i) * ((y'#ys')!i))"
        by simp
      also have "\<dots> = cnj ((x'#xs')!0) * ((y'#ys')!0) + (\<Sum>i = Suc 0..<Suc (length xs'). cnj ((x'#xs')!i) * ((y'#ys')!i))"
        using sum.atLeast_Suc_lessThan by blast
      also have "\<dots> = cnj x' * y' + (\<Sum>i = Suc 0..<Suc (length xs'). cnj ((x'#xs')!i) * ((y'#ys')!i))"
        by simp
      also have "\<dots> = cnj x' * y' + (\<Sum>i = 0..<(length xs'). cnj ((x'#xs')!(Suc i)) * ((y'#ys')!(Suc i)))"
        by (metis (mono_tags, lifting) sum.cong sum.shift_bounds_Suc_ivl)
      also have "\<dots> = cnj x' * y' + (\<Sum>i = 0..<(length xs'). cnj (xs'!i) * (ys'!i))"
        by auto
      also have "\<dots> = cnj x' * y' + sum_list (map2 (\<lambda>t. (*) (cnj t)) xs' ys')"
        using h1 by simp
      finally show ?thesis by auto
    qed
    finally have "sum_list (map2 (\<lambda>t. (*) (cnj t)) (list_of_vec x) (list_of_vec y)) =
          (\<Sum>i = 0..<dim_vec x. cnj (vec_index x i) * (vec_index y i))"
      by blast
    thus ?case .
  qed
  have a3: "length (list_of_vec y) = length (canonical_basis::'a list)"
    by (simp add: w2 w1 n_def)    
  have a1: "\<langle>basis_enum_of_vec_list B (list_of_vec x), basis_enum_of_vec_list B (list_of_vec y)\<rangle>
          = (\<Sum>i = 0..<dim_vec x. cnj (vec_index x i) * (vec_index y i))"
    unfolding basis_enum_of_vec_def 
    apply (subst a0)
    using assms apply auto[1]
    using B_def a3 apply auto[1]
    apply (simp add: B_def is_orthonormal)
    using B_def is_generator_set apply auto[1]
       apply (simp add: B_def)
    apply (simp add: B_def)
    apply (simp add: B_def is_normal)
    using a2 by blast
   thus ?thesis
    unfolding scalar_prod_def apply auto
    by (metis (no_types, lifting) B_def mult.commute n_def basis_enum_of_vec_def sum.cong w1 w2)
qed

lemma cscalar_prod_cinner: "cinner \<psi> \<phi> = cscalar_prod (vec_of_basis_enum \<phi>) (vec_of_basis_enum \<psi>)"
  for \<psi> :: "'a::onb_enum"
  thm cinner_onb_enum_of_vec
  apply (subst cinner_onb_enum_of_vec[symmetric, where 'a='a])
  by (simp_all add: dim_vec_of_basis_enum')

lemma norm_ell2_vec: "norm \<psi> = 
  (let \<psi>' = vec_of_basis_enum \<psi> in
    sqrt (\<Sum> i \<in> {0 ..< dim_vec \<psi>'}. let z = vec_index \<psi>' i in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
  (is "_ = ?rhs") for \<psi> :: "'a::onb_enum"
proof -
  have "norm \<psi> = sqrt (cmod (\<Sum>i = 0..<dim_vec (vec_of_basis_enum \<psi>). 
            vec_of_basis_enum \<psi> $ i * conjugate (vec_of_basis_enum \<psi>) $ i))"
    unfolding norm_eq_sqrt_cinner[where 'a='a] cscalar_prod_cinner scalar_prod_def dim_vec_conjugate
    by rule
  also have "\<dots> = sqrt (cmod (\<Sum>x = 0..<dim_vec (vec_of_basis_enum \<psi>). 
                    let z = vec_of_basis_enum \<psi> $ x in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
    apply (subst sum.cong, rule refl)
     apply (subst vec_index_conjugate)
    by (auto simp: Let_def complex_mult_cnj)
  also have "\<dots> = ?rhs"
    unfolding Let_def norm_of_real
    apply (subst abs_of_nonneg)
     apply (rule sum_nonneg)
    by auto
  finally show ?thesis
    by -
qed

lemma basis_enum_of_vec_unit_vec:
  defines a1: "basis == (canonical_basis::'a::basis_enum list)"
    and a2: "n == canonical_basis_length TYPE('a)"
  assumes a3: "i < n"  
  shows "basis_enum_of_vec (unit_vec n i) = basis!i"
proof-
  define L::"complex list" where "L = list_of_vec (unit_vec n i)"
  define I::"nat list" where "I = [0..<n]"
  have "length L = n"
    by (simp add: L_def)    
  moreover have "length basis = n"
    by (simp add: a1 a2)
  ultimately have "map2 (*\<^sub>C) L basis = map (\<lambda>j. L!j *\<^sub>C basis!j) I"
    by (simp add: I_def list_eq_iff_nth_eq)  
  hence "sum_list (map2 (*\<^sub>C) L basis) = sum_list (map (\<lambda>j. L!j *\<^sub>C basis!j) I)"
    by simp
  also have "\<dots> = sum (\<lambda>j. L!j *\<^sub>C basis!j) {0..n-1}"
  proof-
    have "set I = {0..n-1}"
      using I_def a3 by auto      
    thus ?thesis 
      using Groups_List.sum_code[where xs = I and g = "(\<lambda>j. L!j *\<^sub>C basis!j)"]
      by (simp add: I_def)      
  qed
  also have "\<dots> = sum (\<lambda>j. (list_of_vec (unit_vec n i))!j *\<^sub>C basis!j) {0..n-1}"
    unfolding L_def by blast
  finally have "sum_list (map2 (*\<^sub>C) (list_of_vec (unit_vec n i)) basis)
       = sum (\<lambda>j. (list_of_vec (unit_vec n i))!j *\<^sub>C basis!j) {0..n-1}"
    using L_def by blast    
  also have "\<dots> = basis ! i"
  proof-
    have "(\<Sum>j = 0..n - 1. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j) =
          (\<Sum>j \<in> {0..n - 1}. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j)"
      by simp
    also have "\<dots> = list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i
               + (\<Sum>j \<in> {0..n - 1}-{i}. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j)"
    proof-
      define a where "a j = list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j" for j
      define S where "S = {0..n - 1}"
      have "finite S"
        by (simp add: S_def)        
      hence "(\<Sum>j \<in> insert i S. a j) = a i + (\<Sum>j\<in>S-{i}. a j)"
        using Groups_Big.comm_monoid_add_class.sum.insert_remove
        by auto
      moreover have "S-{i} = {0..n-1}-{i}"
        unfolding S_def
        by blast 
      moreover have "insert i S = {0..n-1}"
        using S_def Suc_diff_1 a3 atLeastAtMost_iff diff_is_0_eq' le_SucE le_numeral_extra(4) 
          less_imp_le not_gr_zero
        by fastforce 
      ultimately show ?thesis
        using \<open>a \<equiv> \<lambda>j. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j\<close>
        by simp 
    qed
    also have "\<dots> = list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i"
    proof-
      have "j \<in> {0..n - 1}-{i} \<Longrightarrow> list_of_vec (unit_vec n i) ! j = 0"
        for j
        using a3 atMost_atLeast0 atMost_iff diff_Suc_less index_unit_vec(1) le_less_trans 
          list_of_vec_index member_remove zero_le by fastforce         
      hence "j \<in> {0..n - 1}-{i} \<Longrightarrow> list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j = 0"
        for j
        by auto         
      hence "(\<Sum>j \<in> {0..n - 1}-{i}. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j) = 0"
        by (simp add: \<open>\<And>j. j \<in> {0..n - 1} - {i} \<Longrightarrow> list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j = 0\<close>)        
      thus ?thesis by simp
    qed
    also have "\<dots> = basis ! i"
      by (simp add: a3)      
    finally show ?thesis
      using \<open>(\<Sum>j = 0..n - 1. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j)
             = list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i + (\<Sum>j\<in>{0..n - 1} - {i}. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j)\<close>
        \<open>list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i + (\<Sum>j\<in>{0..n - 1} - {i}. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j)
           = list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i\<close>
        \<open>list_of_vec (unit_vec n i) ! i *\<^sub>C basis ! i = basis ! i\<close> 
      by auto 
  qed
  finally have "sum_list (map2 (*\<^sub>C) (list_of_vec (unit_vec n i)) basis)
      = basis ! i"
    by (simp add: a1 a2)    
  hence "basis_enum_of_vec_list (canonical_basis::'a list) (list_of_vec (unit_vec n i)) 
      = (canonical_basis::'a list) ! i"     
    by (simp add: basis_enum_of_vec_list_def' a1)
  thus ?thesis 
    unfolding basis_enum_of_vec_def
    by (simp add: a1 a2) 
qed


lift_definition cblinfun_of_mat :: \<open>complex mat \<Rightarrow> 'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L'b::{basis_enum,complex_normed_vector}\<close> is  
  \<open>\<lambda>M. \<lambda>v. (if M\<in>carrier_mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))
           then basis_enum_of_vec (M *\<^sub>v vec_of_basis_enum v)
           else 0)\<close>
proof
  fix M :: "complex mat"
  define m where "m = canonical_basis_length TYPE('b)"
  define n where "n = canonical_basis_length TYPE('a)"
  define f::"complex mat \<Rightarrow> 'a \<Rightarrow> 'b" 
    where "f M v = (if M\<in>carrier_mat m n
        then basis_enum_of_vec (M *\<^sub>v vec_of_basis_enum (v::'a)) 
        else (0::'b))" 
    for M::"complex mat" and v::'a

  show add: \<open>f M (b1 + b2) = f M b1 + f M b2\<close> for b1 b2
    apply (auto simp: f_def)
    by (metis (mono_tags, lifting) carrier_matD(1) carrier_vec_dim_vec dim_mult_mat_vec dim_vec_of_basis_enum' m_def mult_add_distrib_mat_vec n_def basis_enum_of_vec_add vec_of_basis_enum_add)

  show scale: \<open>f M (c *\<^sub>C b) = c *\<^sub>C f M b\<close> for c b
    apply (auto simp: f_def)
    by (metis carrier_matD(1) carrier_vec_dim_vec dim_mult_mat_vec dim_vec_of_basis_enum' m_def mult_mat_vec n_def basis_enum_of_vec_mult vec_of_basis_enum_scaleC)

  from add scale have \<open>clinear (f M)\<close>
    by (simp add: clinear_iff)

  show \<open>\<exists>K. \<forall>b. norm (f M b) \<le> norm b * K\<close>
  proof (cases "M\<in>carrier_mat m n")
    case True
    have f_def': "f M v = basis_enum_of_vec (M *\<^sub>v (vec_of_basis_enum v))" for v
      using True f_def 
        m_def n_def by auto      
    have M_carrier_mat: 
      "M \<in> carrier_mat m n"
      by (simp add: True)
    have "bounded_clinear (f M)"
      apply (rule bounded_clinear_finite_dim) using \<open>clinear (f M)\<close> by auto
    thus ?thesis
      by (simp add: bounded_clinear.bounded) 
  next
    case False
    thus ?thesis
      unfolding f_def m_def n_def
      by (metis (full_types) order_refl mult_eq_0_iff norm_eq_zero)
  qed
qed

definition mat_of_cblinfun :: \<open>'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L'b::{basis_enum,complex_normed_vector} \<Rightarrow> complex mat\<close> where
  \<open>mat_of_cblinfun f = 
    mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a)) (
    \<lambda> (i, j). crepresentation (set (canonical_basis::'b list)) (f *\<^sub>V ((canonical_basis::'a list)!j)) ((canonical_basis::'b list)!i))\<close>
  for f

(* definition mat_of_cblinfun :: \<open>'a::basis_enum \<Rightarrow>\<^sub>C\<^sub>L'b::basis_enum \<Rightarrow> complex mat\<close> where
  \<open>mat_of_cblinfun f = 
    mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a)) (
    \<lambda> (i, j). \<langle> (canonical_basis::'b list)!i, f *\<^sub>V ((canonical_basis::'a list)!j) \<rangle> )\<close>
  for f *)

lemma mat_of_cblinfun_ell2_carrier[simp]: \<open>mat_of_cblinfun (a::'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2) \<in> carrier_mat CARD('b) CARD('a)\<close>
  by (simp add: mat_of_cblinfun_def)

lemma dim_row_mat_of_cblinfun[simp]: \<open>dim_row (mat_of_cblinfun (a::'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2)) = CARD('b)\<close>
  by (simp add: mat_of_cblinfun_def)

lemma dim_col_mat_of_cblinfun[simp]: \<open>dim_col (mat_of_cblinfun (a::'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2)) = CARD('a)\<close>
  by (simp add: mat_of_cblinfun_def)

(* lemma cinner_mat_of_cblinfun_basis:
  fixes F::"'a::basis_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::basis_enum"
  defines "BasisA == (canonical_basis::'a list)"
    and "BasisB == (canonical_basis::'b list)"
    and "nA == canonical_basis_length TYPE('a)"
    and "nB == canonical_basis_length TYPE('b)"
  assumes "iB < nB" and "iA < nA"
  shows "vec_index (mat_of_cblinfun F *\<^sub>v unit_vec nA iA) iB
        = \<langle> BasisB!iB, F *\<^sub>V (BasisA!iA) \<rangle>"
proof-
  have  "mat_of_cblinfun F \<in> carrier_mat nB nA"
    unfolding  mat_of_cblinfun_def nB_def nA_def by simp
  hence "vec_index (mat_of_cblinfun F *\<^sub>v unit_vec nA iA) iB
      = (mat_of_cblinfun F) $$ (iB, iA)"
    using mat_entry_explicit assms(5) assms(6) by auto    
  also have "\<dots> =  \<langle> BasisB!iB, F *\<^sub>V (BasisA!iA) \<rangle>"
    using assms unfolding BasisA_def BasisB_def mat_of_cblinfun_def
    by auto
  finally show ?thesis .
qed *)

(* lemma cinner_mat_of_cblinfun:
  fixes F::"'a::basis_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::basis_enum"
  defines "BasisB == (canonical_basis::'b list)"
    and "nB == canonical_basis_length TYPE('b)"
  assumes "iB < nB"
  shows "vec_index (mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u) iB
        = \<langle> BasisB!iB, F *\<^sub>V u \<rangle>"
proof-
  define BasisA where "BasisA = (canonical_basis::'a list)"
  define basisA where "basisA = set BasisA"
  define nA where "nA == canonical_basis_length TYPE('a)"
  define P where "P x = vec_index (mat_of_cblinfun F *\<^sub>v vec_of_basis_enum x) iB" for x::'a
  define Q where "Q x = \<langle> BasisB!iB, F *\<^sub>V x \<rangle>" for x::'a
  have carrier_mat1: "mat_of_cblinfun F \<in> carrier_mat nB nA"
    unfolding nB_def nA_def mat_of_cblinfun_def by simp
  have "clinear P"
    unfolding clinear_def proof
    show "P (b1 + b2) = P b1 + P b2"
      for b1 :: 'a
        and b2 :: 'a
    proof-
      have "vec_of_basis_enum (b1 + b2) = vec_of_basis_enum b1 + vec_of_basis_enum b2"
        by (simp add: vec_of_basis_enum_add)
      hence "mat_of_cblinfun F *\<^sub>v (vec_of_basis_enum (b1 + b2)) 
            = mat_of_cblinfun F *\<^sub>v (vec_of_basis_enum b1)
            + mat_of_cblinfun F *\<^sub>v (vec_of_basis_enum b2)"
        using carrier_mat1
          add.commute carrier_vec_dim_vec dim_vec_last index_add_vec(2) mult_add_distrib_mat_vec 
          nA_def vec_of_basis_enum_add basis_enum_of_vec_inverse'
        by metis
      thus ?thesis
        unfolding P_def
        using assms(3) carrier_mat1 by auto      
    qed
    show "P (r *\<^sub>C b) = r *\<^sub>C P b"
      for r :: complex
        and b :: 'a
    proof-
      have carrier_vec1: "vec_of_basis_enum b \<in> carrier_vec nA"
        unfolding nA_def vec_of_basis_enum_def
        by (simp add: carrier_dim_vec)
      have "vec_of_basis_enum (r *\<^sub>C b) = r \<cdot>\<^sub>v (vec_of_basis_enum b)"
        by (simp add: vec_of_basis_enum_scaleC)
      hence "mat_of_cblinfun F *\<^sub>v (vec_of_basis_enum (r *\<^sub>C b)) 
            = mat_of_cblinfun F *\<^sub>v (r \<cdot>\<^sub>v (vec_of_basis_enum b))"
        by simp
      also have "\<dots> = r \<cdot>\<^sub>v (mat_of_cblinfun F *\<^sub>v (vec_of_basis_enum b))"
        apply (rule Matrix.mult_mat_vec[where nr = nB and nc = nA and k = r and A = "mat_of_cblinfun F" and v = "vec_of_basis_enum b"])
         apply (simp add: carrier_mat1)
        by (simp add: carrier_vec1)
      finally have "mat_of_cblinfun F *\<^sub>v vec_of_basis_enum (r *\<^sub>C b) =
             r \<cdot>\<^sub>v (mat_of_cblinfun F *\<^sub>v vec_of_basis_enum b)".
      thus ?thesis
        unfolding P_def
        using assms(3) carrier_mat1 by auto      
    qed
  qed
  moreover have "clinear Q"
    unfolding clinear_def proof
    show "Q (b1 + b2) = Q b1 + Q b2"
      for b1 :: 'a
        and b2 :: 'a
    proof-
      have "F *\<^sub>V (b1 + b2) = F *\<^sub>V b1 + F *\<^sub>V b2"
        by (simp add: cblinfun.add_right)        
      thus ?thesis
        unfolding Q_def
        by (simp add: cinner_add_right)        
    qed
    show "Q (r *\<^sub>C b) = r *\<^sub>C Q b"
      for r :: complex
        and b :: 'a
    proof-
      have "F *\<^sub>V (r *\<^sub>C b) = r *\<^sub>C (F *\<^sub>V b)"
        by (simp add: cblinfun.scaleC_right)        
      thus ?thesis
        unfolding Q_def
        by (simp add: cinner_add_right)        
    qed
  qed
  moreover have "P x = Q x" 
    if "x \<in> basisA"
    for x
  proof-
    have "\<exists>iA. BasisA!iA = x \<and> iA < nA"
      by (metis BasisA_def basisA_def distinct_Ex1 
          distinct_canonical_basis nA_def that)     
    then obtain iA where a1: "BasisA!iA = x" and a2: "iA < nA"
      by blast
    have "vec_of_basis_enum (BasisA ! iA) = unit_vec nA iA"
      unfolding BasisA_def nA_def
      by (metis a2 index_unit_vec(3) nA_def basis_enum_of_vec_unit_vec basis_enum_of_vec_inverse')
    hence "P (BasisA!iA) = Q (BasisA!iA)"
      using cinner_mat_of_cblinfun_basis[where iA = iA and iB = iB and F = F]
      unfolding P_def Q_def nA_def BasisA_def BasisB_def
      using a2 assms(3) nA_def nB_def by auto     
    thus ?thesis
      by (simp add: a1)      
  qed
  ultimately have "P x = Q x"
    if "x \<in> complex_vector.span basisA"
    for x
    using complex_vector.linear_eq_on that by blast
  moreover have "complex_vector.span basisA = UNIV"
  proof-
    have "closure (cspan basisA) = cspan basisA"
      by (simp add: basisA_def closure_finite_cspan)
    thus ?thesis
      using BasisA_def basisA_def is_generator_set
        by (metis BasisA_def basisA_def  is_generator_set)
  qed
  ultimately have "P = Q" 
    by (metis UNIV_I ext)    
  thus ?thesis unfolding P_def Q_def
    by meson 
qed *)


lemma mat_of_cblinfun_description:
  "vec_of_basis_enum (F *\<^sub>V u) = mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u"
  for F::"'a::{basis_enum,complex_normed_vector}  \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector}" and u::'a
proof (rule eq_vecI)
  show \<open>dim_vec (vec_of_basis_enum (F *\<^sub>V u)) = dim_vec (mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u)\<close>
    by (simp add: dim_vec_of_basis_enum' mat_of_cblinfun_def)
next
  fix i
  define BasisA where "BasisA = (canonical_basis::'a list)"
  define BasisB where "BasisB = (canonical_basis::'b list)"
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"
  assume \<open>i < dim_vec (mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u)\<close>
  then have [simp]: \<open>i < nB\<close>
    by (simp add: mat_of_cblinfun_def nB_def)
  define v where \<open>v = BasisB ! i\<close>

  have [simp]: \<open>dim_row (mat_of_cblinfun F) = nB\<close>
    by (simp add: mat_of_cblinfun_def nB_def)
  have [simp]: \<open>length BasisB = nB\<close>
    by (simp add: nB_def BasisB_def)
  have [simp]: \<open>length BasisA = nA\<close>
    using BasisA_def nA_def by auto
  have [simp]: \<open>cindependent (set BasisA)\<close>
    using BasisA_def is_cindependent_set by auto
  have [simp]: \<open>cindependent (set BasisB)\<close>
    using BasisB_def is_cindependent_set by blast
  have [simp]: \<open>cspan (set BasisB) = UNIV\<close>
    by (simp add: BasisB_def is_generator_set)
  have [simp]: \<open>cspan (set BasisA) = UNIV\<close>
    by (simp add: BasisA_def is_generator_set)

  have \<open>(mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u) $ i = 
          (\<Sum>j = 0..<nA. row (mat_of_cblinfun F) i $ j * crepresentation (set BasisA) u (vec_of_list BasisA $ j))\<close>
    by (auto simp: vec_of_basis_enum_def scalar_prod_def simp flip: BasisA_def)
  also have \<open>\<dots> = (\<Sum>j = 0..<nA. crepresentation (set BasisB) (F *\<^sub>V BasisA ! j) v
                                 * crepresentation (set BasisA) u (BasisA ! j))\<close>
    apply (rule sum.cong[OF refl])
    by (auto simp: vec_of_list_index mat_of_cblinfun_def scalar_prod_def v_def simp flip: BasisA_def BasisB_def)
  also have \<open>\<dots> = crepresentation (set BasisB) (F *\<^sub>V u) v\<close> (is \<open>(\<Sum>j=_..<_. ?lhs v j) = _\<close>)
  proof (rule complex_vector.representation_eqI[symmetric, THEN fun_cong])
    show \<open>cindependent (set BasisB)\<close> \<open>F *\<^sub>V u \<in> cspan (set BasisB)\<close>
      by simp_all
    show only_basis: \<open>(\<Sum>j = 0..<nA. ?lhs b j) \<noteq> 0 \<Longrightarrow> b \<in> set BasisB\<close> for b
      by (metis (mono_tags, lifting) complex_vector.representation_ne_zero mult_not_zero sum.not_neutral_contains_not_neutral)
    then show \<open>finite {b. (\<Sum>j = 0..<nA. ?lhs b j) \<noteq> 0}\<close>
      by (smt (z3) List.finite_set finite_subset mem_Collect_eq subsetI)
    have \<open>(\<Sum>b | (\<Sum>j = 0..<nA. ?lhs b j) \<noteq> 0. (\<Sum>j = 0..<nA. ?lhs b j) *\<^sub>C b) = 
            (\<Sum>b\<in>set BasisB. (\<Sum>j = 0..<nA. ?lhs b j) *\<^sub>C b)\<close>
      apply (rule sum.mono_neutral_left)
      using only_basis by auto
    also have \<open>\<dots> = (\<Sum>b\<in>set BasisB. (\<Sum>a\<in>set BasisA. crepresentation (set BasisB) (F *\<^sub>V a) b * crepresentation (set BasisA) u a) *\<^sub>C b)\<close>
      apply (subst sum.reindex_bij_betw[where h=\<open>nth BasisA\<close> and T=\<open>set BasisA\<close>])
       apply (metis BasisA_def \<open>length BasisA = nA\<close> atLeast0LessThan bij_betw_nth distinct_canonical_basis)
      by simp
    also have \<open>\<dots> = (\<Sum>a\<in>set BasisA. crepresentation (set BasisA) u a *\<^sub>C (\<Sum>b\<in>set BasisB. crepresentation (set BasisB) (F *\<^sub>V a) b *\<^sub>C b))\<close>
      apply (simp add: scaleC_sum_left scaleC_sum_right)
      apply (subst sum.swap)
      by (metis (no_types, lifting) mult.commute sum.cong)
    also have \<open>\<dots> = (\<Sum>a\<in>set BasisA. crepresentation (set BasisA) u a *\<^sub>C (F *\<^sub>V a))\<close>
      apply (subst complex_vector.sum_representation_eq)
      by auto
    also have \<open>\<dots> = F *\<^sub>V (\<Sum>a\<in>set BasisA. crepresentation (set BasisA) u a *\<^sub>C a)\<close>
      by (simp flip: cblinfun.scaleC_right cblinfun.sum_right)
    also have \<open>\<dots> = F *\<^sub>V u\<close>
      apply (subst complex_vector.sum_representation_eq)
      by auto
    finally show \<open>(\<Sum>b | (\<Sum>j = 0..<nA. ?lhs b j) \<noteq> 0. (\<Sum>j = 0..<nA. ?lhs b j) *\<^sub>C b) = F *\<^sub>V u\<close>
      by auto
  qed
  also have \<open>crepresentation (set BasisB) (F *\<^sub>V u) v = vec_of_basis_enum (F *\<^sub>V u) $ i\<close>
      by (auto simp: vec_of_list_index vec_of_basis_enum_def v_def simp flip: BasisB_def)
  finally show \<open>vec_of_basis_enum (F *\<^sub>V u) $ i = (mat_of_cblinfun F *\<^sub>v vec_of_basis_enum u) $ i\<close>
    by simp
qed


lemma mat_of_cblinfun_inverse:
  "cblinfun_of_mat (mat_of_cblinfun B) = B"
  for B::"'a::{basis_enum,complex_normed_vector}  \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector}"
proof (rule cblinfun_eqI)
  fix x :: 'a define y where \<open>y = vec_of_basis_enum x\<close>
  then have \<open>cblinfun_of_mat (mat_of_cblinfun B) *\<^sub>V x = ((cblinfun_of_mat (mat_of_cblinfun B) :: 'a\<Rightarrow>\<^sub>C\<^sub>L'b) *\<^sub>V basis_enum_of_vec y)\<close>
    by simp
  also have \<open>\<dots> = basis_enum_of_vec (mat_of_cblinfun B *\<^sub>v vec_of_basis_enum (basis_enum_of_vec y :: 'a))\<close>
    apply (transfer fixing: B)
    by (simp add: mat_of_cblinfun_def)
  also have \<open>\<dots> = basis_enum_of_vec (vec_of_basis_enum (B *\<^sub>V x))\<close>
    by (simp add: mat_of_cblinfun_description y_def)
  also have \<open>\<dots> = B *\<^sub>V x\<close>
    by simp
  finally show \<open>cblinfun_of_mat (mat_of_cblinfun B) *\<^sub>V x = B *\<^sub>V x\<close>
    by -
qed

lemma mat_of_cblinfun_inj: "inj mat_of_cblinfun"
  by (metis inj_on_def mat_of_cblinfun_inverse)

lemma cblinfun_of_mat_plus:
  defines "nA \<equiv> canonical_basis_length TYPE('a::{basis_enum,complex_normed_vector})" 
    and "nB \<equiv> canonical_basis_length TYPE('b::{basis_enum,complex_normed_vector})"
  assumes [simp,intro]: "M \<in> carrier_mat nB nA" and [simp,intro]: "N \<in> carrier_mat nB nA"
  shows "(cblinfun_of_mat (M + N) :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = ((cblinfun_of_mat M + cblinfun_of_mat N))"
proof -
  have [simp]: \<open>vec_of_basis_enum (v :: 'a) \<in> carrier_vec nA\<close> for v
    by (auto simp add: carrier_dim_vec dim_vec_of_basis_enum' nA_def)
  have [simp]: \<open>dim_row M = nB\<close> \<open>dim_row N = nB\<close>
    using carrier_matD(1) by auto
  show ?thesis
    apply (transfer fixing: M N)
    by (auto intro!: ext simp add: add_mult_distrib_mat_vec nA_def[symmetric] nB_def[symmetric]
        add_mult_distrib_mat_vec[where nr=nB and nc=nA] basis_enum_of_vec_add)
qed



lemma vec_of_basis_enum_zero:
  assumes a1: "nA = canonical_basis_length TYPE('a::basis_enum)" 
  shows "vec_of_basis_enum (0::'a) = 0\<^sub>v nA"
  by (metis assms carrier_vecI dim_vec_of_basis_enum' minus_cancel_vec right_minus_eq vec_of_basis_enum_minus)

(* TODO move *)
lemma eq_mat_on_vecI:
  fixes M N :: \<open>'a::field mat\<close>
  assumes eq: \<open>\<And>v. v\<in>carrier_vec nA \<Longrightarrow> M *\<^sub>v v = N *\<^sub>v v\<close>
  assumes [simp]: \<open>M \<in> carrier_mat nB nA\<close> \<open>N \<in> carrier_mat nB nA\<close>
  shows \<open>M = N\<close>
proof (rule eq_matI)
  show [simp]: \<open>dim_row M = dim_row N\<close> \<open>dim_col M = dim_col N\<close>
    using assms(2) assms(3) by blast+
  fix i j
  assume [simp]: \<open>i < dim_row N\<close> \<open>j < dim_col N\<close>
  show \<open>M $$ (i, j) = N $$ (i, j)\<close>
    thm mat_entry_explicit[where M=M]
    apply (subst mat_entry_explicit[symmetric])
    using assms apply auto[3]
    apply (subst mat_entry_explicit[symmetric])
    using assms apply auto[3]
    apply (subst eq)
    apply auto using assms(3) unit_vec_carrier by blast
qed

lemma cblinfun_of_mat_zero_converse:
  fixes M::"complex mat"
  defines "nA \<equiv> canonical_basis_length TYPE('a::{basis_enum,complex_normed_vector})" 
    and "nB \<equiv> canonical_basis_length TYPE('b::{basis_enum,complex_normed_vector})"  
  assumes [simp]: "M \<in> carrier_mat nB nA"
    and a4: "(cblinfun_of_mat M :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = 0"
  shows "M = 0\<^sub>m nB nA"
proof -
  have [simp]: \<open>dim_row M = nB\<close>
    using assms(3) by blast
  from a4 have *: \<open>cblinfun_of_mat M *\<^sub>V v = (0::'b)\<close> for v :: 'a
    by auto

  have \<open>M *\<^sub>v vec_of_basis_enum v = vec_of_basis_enum (basis_enum_of_vec (M *\<^sub>v vec_of_basis_enum v) :: 'b)\<close> for v :: 'a
    by (auto simp flip: nA_def nB_def)
  also have \<open>\<dots> v = vec_of_basis_enum (0::'b)\<close> for v :: 'a
    using *[of v]
    by (auto simp: cblinfun_of_mat.rep_eq nA_def[symmetric] nB_def[symmetric])
  also have \<open>\<dots> = 0\<^sub>v nB\<close>
    using nB_def vec_of_basis_enum_zero by force
  finally have \<open>M *\<^sub>v v = 0\<^sub>v nB\<close> if \<open>dim_vec v = nA\<close> for v
    using basis_enum_of_vec_inverse'[OF that[unfolded nA_def]]
    by metis
  also have \<open>\<dots> = 0\<^sub>m nB nA *\<^sub>v v\<close> if \<open>dim_vec v = nA\<close> for v
    using that by auto
  finally show ?thesis
    apply (rule eq_mat_on_vecI[where nA=nA and nB=nB])
    by auto
qed

lemma mat_of_cblinfun_plus:
  "mat_of_cblinfun (F + G) = mat_of_cblinfun F + mat_of_cblinfun G"
  for F G::"'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L'b::{basis_enum,complex_normed_vector}"
  by (auto simp add: mat_of_cblinfun_def cblinfun.add_left is_generator_set is_cindependent_set complex_vector.representation_add)


lemma cblinfun_of_mat_id:
  "mat_of_cblinfun (id_cblinfun :: ('a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L'a)) = 1\<^sub>m (canonical_basis_length TYPE('a))"
  apply (rule eq_matI)
  by (auto simp: mat_of_cblinfun_def complex_vector.representation_basis is_cindependent_set nth_eq_iff_index_eq)

(* TODO: declare at definition *)
declare one_dim_canonical_basis[simp]

(* TODO: move *)
lemma one_cblinfun_apply_one[simp]: \<open>1 *\<^sub>V 1 = 1\<close>
  by (simp add: one_cblinfun.rep_eq)

lemma cblinfun_of_mat_1:
  "mat_of_cblinfun (1 :: ('a::one_dim \<Rightarrow>\<^sub>C\<^sub>L'b::one_dim)) = 1\<^sub>m 1"
  apply (rule eq_matI)
  by (auto simp: mat_of_cblinfun_def complex_vector.representation_basis is_cindependent_set nth_eq_iff_index_eq)

lemma mat_of_cblinfun_zero:
  "mat_of_cblinfun (0 :: ('a::{basis_enum,complex_normed_vector}  \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector})) 
  = 0\<^sub>m (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))"
  by (metis cblinfun_of_mat_zero_converse mat_carrier mat_of_cblinfun_def mat_of_cblinfun_inverse)


lemma cblinfun_of_mat_uminusOp:
  "mat_of_cblinfun (- M) = - mat_of_cblinfun M" 
  for M::"'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L'b::{basis_enum,complex_normed_vector}"
proof-
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"
  have M1: "mat_of_cblinfun M \<in> carrier_mat nB nA"
    unfolding nB_def nA_def
    by (metis add.right_neutral add_carrier_mat mat_of_cblinfun_plus mat_of_cblinfun_zero nA_def
        nB_def zero_carrier_mat) 
  have M2: "mat_of_cblinfun (-M) \<in> carrier_mat nB nA"
    by (metis add_carrier_mat mat_of_cblinfun_plus mat_of_cblinfun_zero diff_0 nA_def nB_def 
        uminus_add_conv_diff zero_carrier_mat)
  have "mat_of_cblinfun (M - M) =  0\<^sub>m nB nA"
    unfolding nA_def nB_def
    by (simp add: mat_of_cblinfun_zero)
  moreover have "mat_of_cblinfun (M - M) = mat_of_cblinfun M + mat_of_cblinfun (- M)"
    by (metis mat_of_cblinfun_plus pth_2)
  ultimately have "mat_of_cblinfun M + mat_of_cblinfun (- M) = 0\<^sub>m nB nA"
    by simp
  thus ?thesis
    using M1 M2
    by (smt add_uminus_minus_mat assoc_add_mat comm_add_mat left_add_zero_mat minus_r_inv_mat 
        uminus_carrier_mat) 
qed


lemma cblinfun_of_mat_minusOp:
  "mat_of_cblinfun (M - N) = mat_of_cblinfun M - mat_of_cblinfun N" 
  for M::"'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector}" and N::"'a \<Rightarrow>\<^sub>C\<^sub>L'b"
  by (smt (z3) add_uminus_minus_mat cblinfun_of_mat_uminusOp mat_carrier mat_of_cblinfun_def mat_of_cblinfun_plus pth_2)

lemma cblinfun_of_mat_uminus:
  defines "nA \<equiv> canonical_basis_length TYPE('a::{basis_enum,complex_normed_vector})" 
    and "nB \<equiv> canonical_basis_length TYPE('b::{basis_enum,complex_normed_vector})"
  assumes "M \<in> carrier_mat nB nA"
  shows "(cblinfun_of_mat (-M) :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = - cblinfun_of_mat M"
  by (smt assms add.group_axioms add.right_neutral add_minus_cancel add_uminus_minus_mat 
      cblinfun_of_mat_plus group.inverse_inverse mat_of_cblinfun_inverse mat_of_cblinfun_zero 
      minus_r_inv_mat uminus_carrier_mat)

lemma cblinfun_of_mat_minus:
  fixes M::"complex mat"
  assumes a1: "M \<in> carrier_mat nB nA" and a2: "N \<in> carrier_mat nB nA"
    and a3: "nA = canonical_basis_length TYPE('a::{basis_enum,complex_normed_vector})" 
    and a4: "nB = canonical_basis_length TYPE('b::{basis_enum,complex_normed_vector})"
  shows   "(cblinfun_of_mat (M - N) :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = cblinfun_of_mat M - cblinfun_of_mat N"
  by (metis a1 a2 a3 a4 add_uminus_minus_mat cblinfun_of_mat_plus cblinfun_of_mat_uminus pth_2 uminus_carrier_mat)

lemma cblinfun_of_mat_inverse:
  fixes M::"complex mat"
  defines "nA == canonical_basis_length TYPE('a::{basis_enum,complex_normed_vector})"
    and "nB == canonical_basis_length TYPE('b::{basis_enum,complex_normed_vector})"
  assumes "M \<in> carrier_mat nB nA"
  shows "mat_of_cblinfun (cblinfun_of_mat M :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = M"
  by (smt (verit) assms(3) basis_enum_of_vec_inverse' carrier_matD(1) carrier_vecD cblinfun_of_mat.rep_eq dim_mult_mat_vec eq_mat_on_vecI mat_carrier mat_of_cblinfun_def mat_of_cblinfun_description nA_def nB_def)

lemma mat_of_cblinfun_timesOp:
  fixes M N ::"complex mat"
  defines "nA == canonical_basis_length TYPE('a::{basis_enum,complex_normed_vector})" 
    and "nB == canonical_basis_length TYPE('b::{basis_enum,complex_normed_vector})"
    and "nC == canonical_basis_length TYPE('c::{basis_enum,complex_normed_vector})"
  assumes a1: "M \<in> carrier_mat nC nB" and a2: "N \<in> carrier_mat nB nA"
  shows  "cblinfun_of_mat (M * N) = ((cblinfun_of_mat M)::'b \<Rightarrow>\<^sub>C\<^sub>L'c) o\<^sub>C\<^sub>L ((cblinfun_of_mat N)::'a \<Rightarrow>\<^sub>C\<^sub>L'b)"
proof -
  have b1: "((cblinfun_of_mat M)::'b \<Rightarrow>\<^sub>C\<^sub>L'c) v = basis_enum_of_vec (M *\<^sub>v vec_of_basis_enum v)"
    for v
    by (metis assms(4) cblinfun_of_mat.rep_eq nB_def nC_def)
  have b2: "((cblinfun_of_mat N)::'a \<Rightarrow>\<^sub>C\<^sub>L'b) v = basis_enum_of_vec (N *\<^sub>v vec_of_basis_enum v)"
    for v
    by (metis assms(5) cblinfun_of_mat.rep_eq nA_def nB_def)
  have b3: "((cblinfun_of_mat (M * N))::'a \<Rightarrow>\<^sub>C\<^sub>L'c) v
       = basis_enum_of_vec ((M * N) *\<^sub>v vec_of_basis_enum v)"
    for v
    by (metis assms(4) assms(5) cblinfun_of_mat.rep_eq mult_carrier_mat nA_def nC_def)
  have "(basis_enum_of_vec ((M * N) *\<^sub>v vec_of_basis_enum v)::'c)
      = (basis_enum_of_vec (M *\<^sub>v ( vec_of_basis_enum ( (basis_enum_of_vec (N *\<^sub>v vec_of_basis_enum v))::'b ))))"
    for v::'a
  proof-
    have c1: "vec_of_basis_enum (basis_enum_of_vec x :: 'b) = x"
      if "dim_vec x = nB"
      for x::"complex vec"
      using that unfolding nB_def
      by simp
    have c2: "vec_of_basis_enum v \<in> carrier_vec nA"
      by (metis (mono_tags, hide_lams) add.commute carrier_vec_dim_vec index_add_vec(2) 
          index_zero_vec(2) nA_def vec_of_basis_enum_add basis_enum_of_vec_inverse')      
    have "(M * N) *\<^sub>v vec_of_basis_enum v = M *\<^sub>v (N *\<^sub>v vec_of_basis_enum v)"
      using Matrix.assoc_mult_mat_vec a1 a2 c2 by blast      
    hence "(basis_enum_of_vec ((M * N) *\<^sub>v vec_of_basis_enum v)::'c)
        = (basis_enum_of_vec (M *\<^sub>v (N *\<^sub>v vec_of_basis_enum v))::'c)"
      by simp
    also have "\<dots> = 
      (basis_enum_of_vec (M *\<^sub>v ( vec_of_basis_enum ( (basis_enum_of_vec (N *\<^sub>v vec_of_basis_enum v))::'b ))))"
      using c1 a2 by auto 
    finally show ?thesis by simp
  qed
  thus ?thesis using b1 b2 b3
    by (simp add: cblinfun_eqI scaleC_cblinfun.rep_eq)    
qed



lemma cblinfun_of_mat_inj: "inj_on (cblinfun_of_mat::complex mat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) 
      (carrier_mat (canonical_basis_length TYPE('b::{basis_enum,complex_normed_vector}))
                   (canonical_basis_length TYPE('a::{basis_enum,complex_normed_vector})))"
  using cblinfun_of_mat_inverse
  by (metis inj_onI)

lemma cblinfun_of_mat_apply_cblinfun:
  fixes M :: "complex mat"
  defines "nA == canonical_basis_length TYPE('a::{basis_enum,complex_normed_vector})"
    and "nB == canonical_basis_length TYPE('b::{basis_enum,complex_normed_vector})"
  assumes a1: "M \<in> carrier_mat nB nA" and a2: "dim_vec x = nA"
  shows "basis_enum_of_vec (M *\<^sub>v x) = (cblinfun_of_mat M :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) *\<^sub>V basis_enum_of_vec x"
  by (metis a1 a2 basis_enum_of_vec_inverse' cblinfun_of_mat.rep_eq nA_def nB_def)


lemma mat_of_cblinfun_adjoint:
  defines "nA == canonical_basis_length TYPE('a::onb_enum)" 
    and "nB == canonical_basis_length TYPE('b::onb_enum)" 
  fixes M:: "complex mat"
  assumes "M \<in> carrier_mat nB nA"
  shows "((cblinfun_of_mat (mat_adjoint M)) :: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a) = (cblinfun_of_mat M)*"
proof (rule adjoint_eqI)
  show "\<langle>cblinfun_of_mat (mat_adjoint M) *\<^sub>V x, y\<rangle> =
           \<langle>x, cblinfun_of_mat M *\<^sub>V y\<rangle>"
    for x::'b and y::'a
  proof-
    define u where "u = vec_of_basis_enum x"
    define v where "v = vec_of_basis_enum y"
    have c1: "vec_of_basis_enum ((cblinfun_of_mat (mat_adjoint M) *\<^sub>V x)::'a)
          = (mat_adjoint M) *\<^sub>v u"
      unfolding u_def
      by (metis mat_adjoint_def' assms(3) cblinfun_of_mat_inverse map_carrier_mat 
          mat_of_cblinfun_description nA_def nB_def transpose_carrier_mat)
    have c2: "(vec_of_basis_enum ((cblinfun_of_mat M *\<^sub>V y)::'b))
        = M *\<^sub>v v"
      by (metis assms(3) cblinfun_of_mat_inverse mat_of_cblinfun_description nA_def nB_def v_def)
    have c3: "dim_vec v = nA"
      unfolding v_def nA_def vec_of_basis_enum_def
      by (simp add:)
    have c4: "dim_vec u = nB"
      unfolding u_def nB_def vec_of_basis_enum_def
      by (simp add:)
    have "v \<bullet>c ((mat_adjoint M) *\<^sub>v u) = (M *\<^sub>v v) \<bullet>c u"
      using c3 c4 cscalar_prod_adjoint assms(3) by blast      
    hence "v \<bullet>c (vec_of_basis_enum ((cblinfun_of_mat (mat_adjoint M) *\<^sub>V x)::'a))
        = (vec_of_basis_enum ((cblinfun_of_mat M *\<^sub>V y)::'b)) \<bullet>c u"
      using c1 c2 by simp
    thus "\<langle>cblinfun_of_mat (mat_adjoint M) *\<^sub>V x, y\<rangle> =
          \<langle>x, cblinfun_of_mat M *\<^sub>V y\<rangle>"
      unfolding u_def v_def
      by (simp add: cscalar_prod_cinner)      
  qed
qed


lemma cinner_square_canonical_basis: 
  defines "BasisA == (canonical_basis:: ('a::onb_enum list))"
    and "n == canonical_basis_length TYPE('a)"
  assumes a1: "i < n"
  shows "\<langle>BasisA!i, BasisA!i\<rangle> = 1"
  using BasisA_def a1 cnorm_eq_1 is_normal n_def nth_mem by blast

(* TODO remove? (Use CARD()) *)
lemma enum_canonical_basis_length:
  "length (enum_class.enum::'a list) = canonical_basis_length TYPE('a::enum ell2)"
proof-
  define nA where "nA = canonical_basis_length TYPE('a ell2)" 
  define BasisA where "BasisA = (canonical_basis::'a ell2 list)"
  have q1:"BasisA = map ket (enum_class.enum::'a list)"
    unfolding BasisA_def
    using canonical_basis_ell2_def by auto
  hence "length BasisA = length (map ket (enum_class.enum::'a list))"
    by simp
  also have "\<dots> = length (enum_class.enum::'a list)"
    by simp
  finally have "length BasisA = length (enum_class.enum::'a list)"
    .
  hence "length (enum_class.enum::'a list) = length BasisA"
    by simp
  also have "length BasisA = nA"
    unfolding BasisA_def nA_def
    by (simp add:)
  finally show ?thesis unfolding nA_def .
qed


lemma mat_of_cblinfun_classical_operator:
  fixes f::"'a::enum \<Rightarrow> 'b::enum option"
  shows "mat_of_cblinfun (classical_operator f) = mat (CARD('b)) (CARD('a))
           (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0)"
proof-
  define nA where "nA = canonical_basis_length TYPE('a ell2)"
  define nB where "nB = canonical_basis_length TYPE('b ell2)"
  define BasisA where "BasisA = (canonical_basis::'a ell2 list)"
  define BasisB where "BasisB = (canonical_basis::'b ell2 list)"
  have "mat_of_cblinfun (classical_operator f) \<in> carrier_mat nB nA"
    unfolding nA_def nB_def
    by (metis cblinfun_of_mat_minusOp diff_zero mat_of_cblinfun_zero minus_carrier_mat 
        zero_carrier_mat)    
  moreover have "nA = CARD ('a)"
    unfolding nA_def
    by (simp add:)    
  moreover have "nB = CARD ('b)"
    unfolding nB_def
    by (simp add:)
  ultimately have "mat_of_cblinfun (classical_operator f) \<in> carrier_mat (CARD('b)) (CARD('a))"
    unfolding nA_def nB_def
    by simp
  moreover have "(mat_of_cblinfun (classical_operator f))$$(r,c) 
  = (mat (CARD('b)) (CARD('a))
    (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0))$$(r,c)"
    if a1: "r < CARD('b)" and a2: "c < CARD('a)"
    for r c
  proof-
    have "CARD('a) = length (enum_class.enum::'a list)"
      using card_UNIV_length_enum[where 'a = 'a] .
    hence x1: "BasisA!c = ket ((Enum.enum::'a list)!c)"
      unfolding BasisA_def using a2 canonical_basis_ell2_def 
        nth_map[where n = c and xs = "Enum.enum::'a list" and f = ket] by metis
    have cardb: "CARD('b) = length (enum_class.enum::'b list)"
      using card_UNIV_length_enum[where 'a = 'b] .
    hence x2: "BasisB!r = ket ((Enum.enum::'b list)!r)"
      unfolding BasisB_def using a1 canonical_basis_ell2_def 
        nth_map[where n = r and xs = "Enum.enum::'b list" and f = ket] by metis
    have "inj (map (ket::'b \<Rightarrow>_))"
      by (meson injI ket_injective list.inj_map)      
    hence "length (Enum.enum::'b list) = length (map (ket::'b \<Rightarrow>_) (Enum.enum::'b list))"
      by simp      
    hence lengthBasisB: "CARD('b) = length BasisB"
      unfolding BasisB_def canonical_basis_ell2_def using cardb 
      by smt
    have v1: "(mat_of_cblinfun (classical_operator f))$$(r,c) = 0"
      if c1: "f (Enum.enum!c) = None"
    proof-
      have "(classical_operator f) *\<^sub>V ket (Enum.enum!c) 
          = (case f (Enum.enum!c) of None \<Rightarrow> 0 | Some i \<Rightarrow> ket i)"
        using classical_operator_ket_finite .
      also have "\<dots> = 0"
        using c1 by simp
      finally have "(classical_operator f) *\<^sub>V ket (Enum.enum!c) = 0" .
      hence *: "(classical_operator f) *\<^sub>V BasisA!c = 0"
        using x1 by simp
      hence "\<langle>BasisB!r, (classical_operator f) *\<^sub>V BasisA!c\<rangle> = 0"
        by simp
      thus ?thesis
        unfolding mat_of_cblinfun_def BasisA_def BasisB_def
        by (smt (verit, del_insts) BasisA_def * a1 a2 canonical_basis_length_ell2 complex_vector.representation_zero index_mat(1) old.prod.case)
    qed
    have v2: "(mat_of_cblinfun (classical_operator f))$$(r,c) = 0"
      if c1: "f (Enum.enum!c) = Some (Enum.enum!r')" and c2: "r\<noteq>r'" 
        and c3: "r' < CARD('b)"
      for r'
    proof-
      have x3: "BasisB!r' = ket ((Enum.enum::'b list)!r')"
        unfolding BasisB_def using cardb c3 canonical_basis_ell2_def 
          nth_map[where n = r' and xs = "Enum.enum::'b list" and f = ket] 
        by smt
      have "distinct BasisB"
        unfolding BasisB_def 
        by simp        
      moreover have "r < length BasisB"
        using a1 lengthBasisB by simp
      moreover have "r' < length BasisB"
        using c3 lengthBasisB by simp        
      ultimately have h1: "BasisB!r \<noteq> BasisB!r'"
        using nth_eq_iff_index_eq[where xs = BasisB and i = r and j = r'] c2
        by blast
      have "(classical_operator f) *\<^sub>V ket (Enum.enum!c) 
          = (case f (Enum.enum!c) of None \<Rightarrow> 0 | Some i \<Rightarrow> ket i)"
        using classical_operator_ket_finite .
      also have "\<dots> = ket (Enum.enum!r')"
        using c1 by simp
      finally have "(classical_operator f) *\<^sub>V ket (Enum.enum!c) = ket (Enum.enum!r')" .
      hence *: "(classical_operator f) *\<^sub>V BasisA!c = BasisB!r'"
        using x1 x3 by simp
      moreover have "\<langle>BasisB!r, BasisB!r'\<rangle> = 0"
        using h1
        using BasisB_def \<open>r < length BasisB\<close> \<open>r' < length BasisB\<close> is_ortho_set_def is_orthonormal nth_mem
        by metis
      ultimately have "\<langle>BasisB!r, (classical_operator f) *\<^sub>V BasisA!c\<rangle> = 0"
        by simp
      thus ?thesis
        unfolding mat_of_cblinfun_def BasisA_def BasisB_def
        by (smt (z3) BasisA_def BasisB_def * \<open>r < length BasisB\<close> \<open>r' < length BasisB\<close> a2 canonical_basis_length_ell2 case_prod_conv complex_vector.representation_basis h1 index_mat(1) is_cindependent_set nth_mem)
    qed
    have "(mat_of_cblinfun (classical_operator f))$$(r,c) = 0"
      if b1: "f (Enum.enum!c) \<noteq> Some (Enum.enum!r)"
    proof (cases "f (Enum.enum!c) = None")
      case True thus ?thesis using v1 by blast
    next
      case False
      hence "\<exists>R. f (Enum.enum!c) = Some R"
        apply (induction "f (Enum.enum!c)")
         apply simp
        by simp
      then obtain R where R0: "f (Enum.enum!c) = Some R"
        by blast
      have "R \<in> set (Enum.enum::'b list)"
        using UNIV_enum by blast
      hence "\<exists>r'. R = (Enum.enum::'b list)!r' \<and> r' < length (Enum.enum::'b list)"
        by (metis in_set_conv_nth)
      then obtain r' where u1: "R = (Enum.enum::'b list)!r'" 
        and u2: "r' < length (Enum.enum::'b list)"
        by blast
      have R1: "f (Enum.enum!c) = Some (Enum.enum!r')"
        using R0 u1 by blast
      have "Some ((Enum.enum::'b list)!r') \<noteq> Some ((Enum.enum::'b list)!r)"
      proof(rule classical)
        assume "\<not>(Some ((Enum.enum::'b list)!r') \<noteq> Some ((Enum.enum::'b list)!r))"
        hence "Some ((Enum.enum::'b list)!r') = Some ((Enum.enum::'b list)!r)"
          by blast
        hence "f (Enum.enum!c) = Some ((Enum.enum::'b list)!r)"
          using R1 by auto
        thus ?thesis
          using b1 by blast
      qed
      hence "((Enum.enum::'b list)!r') \<noteq> ((Enum.enum::'b list)!r)"
        by simp
      hence "r' \<noteq> r"
        by blast
      moreover have "r' < CARD('b)"
        using u2 cardb by simp
      ultimately show ?thesis using R1 v2[where r' = r'] by blast
    qed
    moreover have "(mat_of_cblinfun (classical_operator f))$$(r,c) = 1"
      if b1: "f (Enum.enum!c) = Some (Enum.enum!r)"
    proof-
      have "CARD('b) = length (enum_class.enum::'b list)"
        using card_UNIV_length_enum[where 'a = 'b].
      hence "length (map (ket::'b\<Rightarrow>_) enum_class.enum) = CARD('b)"
        by simp        
      hence w0: "map (ket::'b\<Rightarrow>_) enum_class.enum ! r = ket (enum_class.enum ! r)"
        by (simp add: a1)
      have "CARD('a) = length (enum_class.enum::'a list)"
        using card_UNIV_length_enum[where 'a = 'a].
      hence "length (map (ket::'a\<Rightarrow>_) enum_class.enum) = CARD('a)"
        by simp        
      hence "map (ket::'a\<Rightarrow>_) enum_class.enum ! c = ket (enum_class.enum ! c)"
        by (simp add: a2)        
      hence "(classical_operator f) *\<^sub>V (BasisA!c) = (classical_operator f) *\<^sub>V (ket (Enum.enum!c))"
        unfolding BasisA_def canonical_basis_ell2_def by simp
      also have "... = (case f (enum_class.enum ! c) of None \<Rightarrow> 0 | Some x \<Rightarrow> ket x)"
        by (rule classical_operator_ket_finite)
      also have "\<dots> = BasisB!r"
        using w0 b1 by (simp add: BasisB_def canonical_basis_ell2_def) 
      finally have w1: "(classical_operator f) *\<^sub>V (BasisA!c) = BasisB!r"
        by simp        
      have "(mat_of_cblinfun (classical_operator f))$$(r,c)
        = \<langle>BasisB!r, (classical_operator f) *\<^sub>V (BasisA!c)\<rangle>"
        unfolding BasisB_def BasisA_def mat_of_cblinfun_def
        using \<open>nA = CARD('a)\<close> \<open>nB = CARD('b)\<close> a1 a2 nA_def nB_def apply auto
        by (metis BasisA_def BasisB_def cinner_square_canonical_basis complex_vector.representation_basis is_cindependent_set nB_def nth_mem w1)
      also have "\<dots> = \<langle>BasisB!r, BasisB!r\<rangle>"
        using w1 by simp        
      also have "\<dots> = 1"
        unfolding BasisB_def
        using \<open>nB = CARD('b)\<close> a1 cinner_square_canonical_basis nB_def by metis
      finally show ?thesis by blast
    qed
    ultimately show ?thesis
      by (simp add: a1 a2)            
  qed
  ultimately show ?thesis 
    apply (rule_tac eq_matI) by auto
qed

lemma cblinfun_of_mat_timesOp:
  "mat_of_cblinfun (F o\<^sub>C\<^sub>L G) = mat_of_cblinfun F * mat_of_cblinfun G" 
  for F::"'b::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'c::{basis_enum,complex_normed_vector}"
    and G::"'a::{basis_enum,complex_normed_vector}  \<Rightarrow>\<^sub>C\<^sub>L 'b"
  by (smt (verit, del_insts) cblinfun_of_mat_inverse mat_carrier mat_of_cblinfun_def mat_of_cblinfun_inverse mat_of_cblinfun_timesOp mult_carrier_mat)

lemma mat_of_cblinfun_scalarMult:
  "mat_of_cblinfun ((a::complex) *\<^sub>C F) = a \<cdot>\<^sub>m (mat_of_cblinfun F)"
  for F :: "'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::{basis_enum,complex_normed_vector}"
  by (auto simp add: complex_vector.representation_scale mat_of_cblinfun_def is_generator_set is_cindependent_set)

lemma mat_of_cblinfun_scaleR:
  "mat_of_cblinfun ((a::real) *\<^sub>R F) = (complex_of_real a) \<cdot>\<^sub>m (mat_of_cblinfun F)"
  unfolding scaleR_scaleC by (rule mat_of_cblinfun_scalarMult)

lemma mat_of_cblinfun_adjoint':
  "mat_of_cblinfun (F*) = mat_adjoint (mat_of_cblinfun F)"
  for F :: "'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
  by (metis (no_types, lifting) cblinfun_of_mat_inverse map_carrier_mat mat_adjoint_def' mat_carrier mat_of_cblinfun_adjoint mat_of_cblinfun_def mat_of_cblinfun_inverse transpose_carrier_mat)


subsubsection\<open>Gram Schmidt sub\<close>

lemma (in complex_vec_space) module_span_cspan:
  fixes X :: "'a::basis_enum set"
  assumes "canonical_basis_length TYPE('a) = n"
  shows "span (vec_of_basis_enum ` X) = vec_of_basis_enum ` cspan X"
proof -
  have carrier: "vec_of_basis_enum ` X \<subseteq> carrier_vec n"
    by (metis assms carrier_vecI dim_vec_of_basis_enum' image_subsetI)
  have lincomb_sum: "lincomb c A = vec_of_basis_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)" 
    if B_def: "B = basis_enum_of_vec ` A" and \<open>finite A\<close>
      and AX: "A \<subseteq> vec_of_basis_enum ` X" and c'_def: "\<And>b. c' b = c (vec_of_basis_enum b)"
    for c c' A and B::"'a set"
    unfolding B_def using \<open>finite A\<close> AX
  proof induction
    case empty
    then show ?case
      by (simp add: assms vec_of_basis_enum_zero)
  next
    case (insert x F)
    then have IH: "lincomb c F = vec_of_basis_enum (\<Sum>b\<in>basis_enum_of_vec ` F. c' b *\<^sub>C b)"
      (is "_ = ?sum")
      by simp
    have xx: "vec_of_basis_enum (basis_enum_of_vec x :: 'a) = x"
      apply (rule basis_enum_of_vec_inverse')
      using assms carrier carrier_vecD insert.prems by auto
    have "lincomb c (insert x F) = c x \<cdot>\<^sub>v x + lincomb c F"
      apply (rule lincomb_insert2)
      using insert.hyps insert.prems carrier by auto
    also have "c x \<cdot>\<^sub>v x = vec_of_basis_enum (c' (basis_enum_of_vec x) *\<^sub>C (basis_enum_of_vec x :: 'a))"
      by (simp add: xx vec_of_basis_enum_scaleC c'_def)
    also note IH
    also have
      "vec_of_basis_enum (c' (basis_enum_of_vec x) *\<^sub>C (basis_enum_of_vec x :: 'a)) + ?sum
          = vec_of_basis_enum (\<Sum>b\<in>basis_enum_of_vec ` insert x F. c' b *\<^sub>C b)"
      apply simp apply (rule sym)
      apply (subst sum.insert)
      using \<open>finite F\<close> \<open>x \<notin> F\<close> dim_vec_of_basis_enum' insert.prems 
        vec_of_basis_enum_add c'_def by auto
    finally show ?case
      by -
  qed

  show ?thesis
  proof auto
    fix x assume "x \<in> local.span (vec_of_basis_enum ` X)"
    then obtain c A where xA: "x = lincomb c A" and "finite A" and AX: "A \<subseteq> vec_of_basis_enum ` X"
      unfolding span_def by auto
    define B::"'a set" and c' where "B = basis_enum_of_vec ` A"
      and "c' b = c (vec_of_basis_enum b)" for b::'a
    note xA
    also have "lincomb c A = vec_of_basis_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)"
      using B_def \<open>finite A\<close> AX c'_def by (rule lincomb_sum)
    also have "\<dots> \<in> vec_of_basis_enum ` cspan X"
      unfolding complex_vector.span_explicit
      apply (rule imageI) apply (rule CollectI)
      apply (rule exI) apply (rule exI)
      using \<open>finite A\<close> AX by (auto simp: B_def)
    finally show "x \<in> vec_of_basis_enum ` cspan X"
      by -
  next
    fix x assume "x \<in> cspan X" 
    then obtain c' B where x: "x = (\<Sum>b\<in>B. c' b *\<^sub>C b)" and "finite B" and BX: "B \<subseteq> X"
      unfolding complex_vector.span_explicit by auto
    define A and c where "A = vec_of_basis_enum ` B"
      and "c b = c' (basis_enum_of_vec b)" for b
    have "vec_of_basis_enum x = vec_of_basis_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)"
      using x by simp
    also have "\<dots> = lincomb c A"
      apply (rule lincomb_sum[symmetric])
      unfolding A_def c_def using BX \<open>finite B\<close>
      by (auto simp: image_image)
    also have "\<dots> \<in> span (vec_of_basis_enum ` X)"
      unfolding span_def apply (rule CollectI)
      apply (rule exI, rule exI)
      unfolding A_def using \<open>finite B\<close> BX by auto
    finally show "vec_of_basis_enum x \<in> local.span (vec_of_basis_enum ` X)"
      by -
  qed
qed

lemma (in complex_vec_space) module_span_cspan':
  assumes "canonical_basis_length TYPE('a) = n"
  assumes "Y \<subseteq> carrier_vec n"
  shows "cspan (basis_enum_of_vec ` Y :: 'a::basis_enum set) = basis_enum_of_vec ` local.span Y"
proof -
  define X::"'a set" where "X = basis_enum_of_vec ` Y"
  then have "cspan (basis_enum_of_vec ` Y :: 'a set) = basis_enum_of_vec ` vec_of_basis_enum ` cspan X"
    by (simp add: image_image)
  also have "\<dots> = basis_enum_of_vec ` local.span (vec_of_basis_enum ` X)"
    apply (subst module_span_cspan)
    using assms by simp_all
  also have "vec_of_basis_enum ` X = Y"
    unfolding X_def image_image
    apply (rule image_cong[where g=id and M=Y and N=Y, simplified])
    using assms(1) assms(2) by auto
  finally show ?thesis
    by simp
qed

lemma Span_basis_enum_gram_schmidt0:
  defines "basis_enum == (basis_enum_of_vec :: _ \<Rightarrow> 'a::{basis_enum,complex_normed_vector})"
  defines "n == canonical_basis_length TYPE('a)"
  assumes "set ws \<subseteq> carrier_vec n"
  shows "ccspan (set (map basis_enum (gram_schmidt0 n ws)))
     = ccspan (set (map basis_enum ws))"
proof (transfer fixing: n ws basis_enum)
  interpret complex_vec_space.
  define gs where "gs = gram_schmidt0 n ws"
  have "closure (cspan (set (map basis_enum gs)))
     = cspan (set (map basis_enum gs))"
    apply (rule closure_finite_cspan)
    by simp
  also have "\<dots> = cspan (basis_enum ` set gs)"
    by simp
  also have "\<dots> = basis_enum ` span (set gs)"
    unfolding basis_enum_def
    apply (rule module_span_cspan')
    using n_def apply simp
    by (simp add: assms(3) cof_vec_space.gram_schmidt0_result(1) gs_def)
  also have "\<dots> = basis_enum ` span (set ws)"
    unfolding gs_def
    apply (subst gram_schmidt0_result(4)[where ws=ws, symmetric])
    using assms by auto
  also have "\<dots> = cspan (basis_enum ` set ws)"
    unfolding basis_enum_def
    apply (rule module_span_cspan'[symmetric])
    using n_def apply simp
    by (simp add: assms(3))
  also have "\<dots> = cspan (set (map basis_enum ws))"
    by simp
  also have "\<dots> = closure (cspan (set (map basis_enum ws)))"
    apply (rule closure_finite_cspan[symmetric])
    by simp
  finally show "closure (cspan (set (map basis_enum gs)))
              = closure (cspan (set (map basis_enum ws)))".
qed

(* TODO move *)
lemma index_of_length: "index_of x y \<le> length y"
  apply (induction y) by auto

lemma vec_of_basis_enum_ket:
  "vec_of_basis_enum (ket i) = unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)" 
  for i::"'a::enum"
proof-
  have "dim_vec (vec_of_basis_enum (ket i)) 
      = dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i))"
  proof-
    have "dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) 
      = canonical_basis_length TYPE('a ell2)"
      by simp     
    moreover have "dim_vec (vec_of_basis_enum (ket i)) = canonical_basis_length TYPE('a ell2)"
      unfolding vec_of_basis_enum_def vec_of_basis_enum_def by auto
    ultimately show ?thesis by simp
  qed
  moreover have "vec_of_basis_enum (ket i) $ j =
    (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) $ j"
    if "j < dim_vec (vec_of_basis_enum (ket i))"
    for j
  proof-
    have j_bound: "j < length (canonical_basis::'a ell2 list)"
      by (metis dim_vec_of_basis_enum' that)
    have y1: "cindependent (set (canonical_basis::'a ell2 list))"
      using is_cindependent_set by blast
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
    moreover have "length (enum_class.enum::'a list) = dim_vec (vec_of_basis_enum (ket i))"
      unfolding vec_of_basis_enum_def canonical_basis_ell2_def
      using dim_vec_of_basis_enum'[where v = "ket i"]
      unfolding canonical_basis_ell2_def by simp              
    ultimately have "enum_idx i < dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) 
        (enum_idx i))"
      using \<open>dim_vec (vec_of_basis_enum (ket i)) = dim_vec (unit_vec (canonical_basis_length 
        TYPE('a ell2)) (enum_idx i))\<close> by auto            
    hence r1: "(unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) $ j
        = (if enum_idx i = j then 1 else 0)"
      using \<open>dim_vec (vec_of_basis_enum (ket i)) = dim_vec (unit_vec (canonical_basis_length 
        TYPE('a ell2)) (enum_idx i))\<close> that by auto
    moreover have "vec_of_basis_enum (ket i) $ j = (if enum_idx i = j then 1 else 0)"
    proof(cases "enum_idx i = j")
      case True                        
      have "crepresentation (set (canonical_basis::'a ell2 list)) 
          ((canonical_basis::'a ell2 list) ! j) ((canonical_basis::'a ell2 list) ! j) = 1"        
        using y1 y2 complex_vector.representation_basis[where 
            basis = "set (canonical_basis::'a ell2 list)" 
            and b = "(canonical_basis::'a ell2 list) ! j"]
        by smt

      hence "vec_of_basis_enum ((canonical_basis::'a ell2 list) ! j) $ j = 1"
        unfolding vec_of_basis_enum_def 
        by (metis True \<open>enum_idx i < dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) 
          (enum_idx i))\<close> index_unit_vec(3) list_of_vec_index list_vec nth_map)
      hence "vec_of_basis_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) 
            $ enum_idx i = 1"
        using True by simp
      hence "vec_of_basis_enum (ket i) $ enum_idx i = 1"
        using p4
        by simp
      thus ?thesis using True unfolding vec_of_basis_enum_def by auto
    next
      case False
      have "crepresentation (set (canonical_basis::'a ell2 list)) 
          ((canonical_basis::'a ell2 list) ! (enum_idx i)) ((canonical_basis::'a ell2 list) ! j) = 0"        
        using y1 y2 complex_vector.representation_basis[where 
            basis = "set (canonical_basis::'a ell2 list)" 
            and b = "(canonical_basis::'a ell2 list) ! j"]
          False \<open>enum_idx i < dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) 
          (enum_idx i))\<close> 
          complex_vector.representation_basis distinct_canonical_basis index_unit_vec(3) 
          j_bound nth_eq_iff_index_eq nth_mem 
        by metis
      hence "vec_of_basis_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) $ j = 0"
        unfolding vec_of_basis_enum_def by (smt j_bound nth_map vec_of_list_index)        
      hence "vec_of_basis_enum ((canonical_basis::'a ell2 list) ! (enum_idx i)) 
            $ j = 0"
        by auto
      hence "vec_of_basis_enum (ket i) $ j = 0"
        using p4
        by simp
      thus ?thesis using False unfolding vec_of_basis_enum_def by simp
    qed
    ultimately show ?thesis by auto
  qed
  ultimately show ?thesis 
    using Matrix.eq_vecI
    by auto
qed


lemma vec_of_basis_vector:
  assumes "i < canonical_basis_length TYPE('a)"
  shows "vec_of_basis_enum (canonical_basis!i :: 'a)
       = unit_vec (canonical_basis_length TYPE('a::basis_enum)) i"
  by (metis assms basis_enum_of_vec_inverse' basis_enum_of_vec_unit_vec index_unit_vec(3))

lemma ket_canonical_basis: "ket x = canonical_basis ! enum_idx x"  
proof-
  have "x = (enum_class.enum::'a list) ! enum_idx x"
    using enum_idx_correct[where i = x] by simp
  hence p1: "ket x = ket ((enum_class.enum::'a list) ! enum_idx x)"
    by simp
  have "enum_idx x < length (enum_class.enum::'a list)"
    using enum_idx_bound[where x = x].
  hence "(map ket (enum_class.enum::'a list)) ! enum_idx x 
        = ket ((enum_class.enum::'a list) ! enum_idx x)"
    by auto      
  thus ?thesis
    unfolding canonical_basis_ell2_def using p1 by auto    
qed


lemma vec_of_basis_enum_times: 
  fixes \<psi> \<phi> :: "'a::one_dim"
  shows "vec_of_basis_enum (\<psi> * \<phi>)
   = vec_of_list [vec_index (vec_of_basis_enum \<psi>) 0 * vec_index (vec_of_basis_enum \<phi>) 0]"
proof -
  have [simp]: \<open>crepresentation {1} x 1 = one_dim_iso x\<close> for x :: 'a
    apply (subst one_dim_scaleC_1[where x=x, symmetric])
    apply (subst complex_vector.representation_scale)
    by (auto simp add: complex_vector.span_base complex_vector.representation_basis)
  show ?thesis
    apply (rule eq_vecI)
    by (auto simp: vec_of_basis_enum_def)
qed


lemma vec_of_basis_enum_inverse: 
  fixes \<psi> :: "'a::one_dim"
  shows "vec_of_basis_enum (inverse \<psi>)
     = vec_of_list [inverse (vec_index (vec_of_basis_enum \<psi>) 0)]"
proof -
  have [simp]: \<open>crepresentation {1} x 1 = one_dim_iso x\<close> for x :: 'a
    apply (subst one_dim_scaleC_1[where x=x, symmetric])
    apply (subst complex_vector.representation_scale)
    by (auto simp add: complex_vector.span_base complex_vector.representation_basis)
  show ?thesis
    apply (rule eq_vecI)
    apply (auto simp: vec_of_basis_enum_def)
    by (metis complex_vector.scale_cancel_right one_dim_inverse one_dim_scaleC_1 zero_neq_one)
qed


lemma vec_of_basis_enum_divide: 
  fixes \<psi> \<phi> :: "'a::one_dim"
  shows "vec_of_basis_enum (\<psi> / \<phi>)
   = vec_of_list [vec_index (vec_of_basis_enum \<psi>) 0 / vec_index (vec_of_basis_enum \<phi>) 0]"
  by (simp add: divide_inverse vec_of_basis_enum_inverse vec_of_basis_enum_times)

lemma vec_of_basis_enum_1: "vec_of_basis_enum (1 :: 'a::one_dim) = vec_of_list [1]"
proof -
  have [simp]: \<open>crepresentation {1} x 1 = one_dim_iso x\<close> for x :: 'a
    apply (subst one_dim_scaleC_1[where x=x, symmetric])
    apply (subst complex_vector.representation_scale)
    by (auto simp add: complex_vector.span_base complex_vector.representation_basis)
  show ?thesis
    apply (rule eq_vecI)
    by (auto simp: vec_of_basis_enum_def)
qed

lemma mat_of_cblinfun_ell2_to_l2bounded:
  "mat_of_cblinfun (vector_to_cblinfun \<psi>)
       = mat_of_cols (canonical_basis_length TYPE('a)) [vec_of_basis_enum \<psi>]"
  for \<psi>::"'a::{basis_enum,complex_normed_vector}"  
  by (auto simp: mat_of_cols_Cons_index_0 mat_of_cblinfun_def vec_of_basis_enum_def vec_of_list_index)

(* TODO move *)
lemma proj_0[simp]: \<open>proj 0 = 0\<close>
  apply transfer by auto

lemma mat_of_cblinfun_proj:
  fixes a::"'a::onb_enum"
  defines   "d == canonical_basis_length TYPE('a)"
    and "norm2 == (vec_of_basis_enum a) \<bullet>c (vec_of_basis_enum a)"
  shows  "mat_of_cblinfun (proj a) = 
      1 / norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_basis_enum a]
                 * mat_of_rows d [conjugate (vec_of_basis_enum a)])" (is \<open>_ = ?rhs\<close>)
proof (cases "a = 0")
  case False 
  have norm2: \<open>norm2 = (norm a)\<^sup>2\<close>
    by (simp add: cscalar_prod_cinner norm2_def cdot_square_norm[symmetric, simplified])
  have [simp]: \<open>vec_of_basis_enum a \<in> carrier_vec d\<close>
    by (simp add: carrier_vecI d_def dim_vec_of_basis_enum')

  have \<open>mat_of_cblinfun (proj a) = mat_of_cblinfun (proj (a /\<^sub>R norm a))\<close>
    by (metis (mono_tags, hide_lams) ccspan_singleton_scaleC complex_vector.scale_eq_0_iff nonzero_imp_inverse_nonzero norm_eq_zero scaleR_scaleC scale_left_imp_eq)
  also have \<open>\<dots> = mat_of_cblinfun (selfbutter (a /\<^sub>R norm a))\<close>
    apply (subst butterfly_eq_proj)
    by (auto simp add: False)
  also have \<open>\<dots> = 1/norm2 \<cdot>\<^sub>m mat_of_cblinfun (selfbutter a)\<close>
    apply (simp add: mat_of_cblinfun_scalarMult norm2)
    by (simp add: inverse_eq_divide power2_eq_square)
  also have \<open>\<dots> = 1 / norm2 \<cdot>\<^sub>m (mat_of_cblinfun (vector_to_cblinfun a :: complex \<Rightarrow>\<^sub>C\<^sub>L 'a) * mat_adjoint (mat_of_cblinfun (vector_to_cblinfun a :: complex \<Rightarrow>\<^sub>C\<^sub>L 'a)))\<close>
    by (simp add: butterfly_def cblinfun_of_mat_timesOp mat_of_cblinfun_adjoint')
  also have \<open>\<dots> = ?rhs\<close>
    by (simp add: mat_of_cblinfun_ell2_to_l2bounded mat_adjoint_def flip: d_def)
  finally show ?thesis
    by -
next
  case True
  show ?thesis
    apply (rule eq_matI)
    by (auto simp: True mat_of_cblinfun_zero vec_of_basis_enum_zero scalar_prod_def  mat_of_rows_index
        simp flip: d_def)
qed



lemma mat_of_cblinfun_proj':
  fixes a b::"'a::onb_enum" 
  defines "u == vec_of_basis_enum a"
    and "v == vec_of_basis_enum b"
    and "norm2 == vec_of_basis_enum a \<bullet>c vec_of_basis_enum a"
  shows   "mat_of_cblinfun (proj a) *\<^sub>v v = (v \<bullet>c u) / norm2 \<cdot>\<^sub>v u"
proof-
  define d where "d = canonical_basis_length TYPE('a)"
  have ucdim: "dim_vec u = d"
    unfolding u_def d_def
    by (simp add: dim_vec_of_basis_enum') 
  have vcdim: "dim_vec v = d"
    unfolding v_def d_def
    by (simp add: dim_vec_of_basis_enum') 
  have "dim_col (mat_of_cols d [u]) = 1"
    by auto
  hence x1: "row (mat_of_cols d [u]) i $ 0 = u $ i"
    if "i < d"
    for i
    unfolding row_def mat_of_cols_def using that by auto
  have "dim_row (mat_of_rows d [conjugate u]) = 1"
    by auto  
  hence x3: "col (mat_of_rows d [conjugate u]) j $ 0 = cnj (u $ j)"
    if "j < d"
    for j
    unfolding col_def mat_of_rows_def using that
    by (simp add: ucdim)
  have "row (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k $ l = cnj (u $ l) * u $ k"
    if "k < d" and "l < d"
    for k l    
    by (simp add: that)    
  hence "row (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k $ l * v $ l =
        v $ l * cnj (u $ l) * u $ k"
    if "k < d" and "l < d"
    for k l
    by (simp add: that)
  moreover have "(\<And> k. k < d \<Longrightarrow> f k = g k) \<Longrightarrow> (\<Sum>k = 0..<d. f k) =  (\<Sum>k = 0..<d. g k)"
    for f g::"nat \<Rightarrow> complex"
    by auto    
  ultimately have "(\<Sum>l = 0..<d. row (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k $ l * v $ l) =
         (\<Sum>l = 0..<d. v $ l * cnj (u $ l) * u $ k)"
    if "k < d" 
    for k
    using that by presburger    
  hence "(\<Sum>i = 0..<d.
        row (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k $ i * v $ i) =
        (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) * u $ k"
    if "k < d"
    for k
    by (metis (mono_tags, lifting) sum.cong that vector_space_over_itself.scale_sum_left)    
  hence "scalar_prod (row (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k) v
      = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) * (u $ k)"
    if "k < d"
    for k
    unfolding scalar_prod_def vcdim 
    apply auto                 
    using \<open>\<And>k. k < d \<Longrightarrow> (\<Sum>i = 0..<d. Matrix.row (Matrix.mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k
     $ i * v $ i) = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) * u $ k\<close> that by blast
  hence "mat d d (\<lambda>(i, j). u $ i * cnj (u $ j)) *\<^sub>v v = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) \<cdot>\<^sub>v u"
    unfolding mult_mat_vec_def apply auto
    by (smt \<open>\<And>k. k < d \<Longrightarrow> scalar_prod (row (Matrix.mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k) v = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) * u $ k\<close> dim_vec eq_vecI index_smult_vec(1) index_smult_vec(2) index_vec ucdim) 
  moreover have "mat d d (\<lambda>(i, j). row (mat_of_cols d [u]) i $ 0
                                 * col (mat_of_rows d [conjugate u]) j $ 0)
      = mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))"
  proof-
    have "(mat d d (\<lambda>(i, j). row (mat_of_cols d [u]) i $ 0
        * col (mat_of_rows d [conjugate u]) j $ 0)) $$ (i, j)
        = (mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) $$ (i, j)"
      if "i < d" and "j < d"
      for i j
    proof-
      have "(mat d d (\<lambda>(i, j). row (mat_of_cols d [u]) i $ 0
        * col (mat_of_rows d [conjugate u]) j $ 0)) $$ (i, j)
       = row (mat_of_cols d [u]) i $ 0 * col (mat_of_rows d [conjugate u]) j $ 0"
        by (simp add: that)        
      moreover have "(mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) $$ (i, j) =  u $ i * cnj (u $ j)"
        by (simp add: that)        
      ultimately show ?thesis
        using x1 x3 that
        by auto
    qed
    thus ?thesis 
      by auto
  qed
  ultimately have "mat d d
     (\<lambda>(i, j). row (mat_of_cols d [u]) i $ 0 * col (mat_of_rows d [conjugate u]) j $ 0) *\<^sub>v
    v = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) \<cdot>\<^sub>v u"
    by simp
  hence "(mat_of_cols d [u] * mat_of_rows d [conjugate u]) *\<^sub>v v = (v \<bullet>c u) \<cdot>\<^sub>v u"
    unfolding times_mat_def scalar_prod_def apply auto
    using ucdim by blast
  moreover have "1 / norm2 \<cdot>\<^sub>m
      (mat_of_cols d [vec_of_basis_enum a] *
       mat_of_rows d [conjugate (vec_of_basis_enum a)]) *\<^sub>v v =
       1 / norm2 \<cdot>\<^sub>v
      ((mat_of_cols d [vec_of_basis_enum a] *
       mat_of_rows d [conjugate (vec_of_basis_enum a)]) *\<^sub>v v)"
  proof-
    have "mat_of_cols d [vec_of_basis_enum a] *
       mat_of_rows d [conjugate (vec_of_basis_enum a)] \<in> carrier_mat d d"
      unfolding d_def
      by (simp add: carrier_matI) 
    moreover have "v \<in> carrier_vec d"
      unfolding d_def v_def
      using carrier_vecI d_def v_def vcdim by blast
    ultimately show ?thesis 
      using mult_mat_vec by auto
  qed
  ultimately have "1 / norm2 \<cdot>\<^sub>m
      (mat_of_cols d [vec_of_basis_enum a] *
       mat_of_rows d [conjugate (vec_of_basis_enum a)]) *\<^sub>v v =
       1 / norm2 \<cdot>\<^sub>v (v \<bullet>c u \<cdot>\<^sub>v u)"
    by (simp add: u_def)    
  hence "1 / norm2 \<cdot>\<^sub>m
      (mat_of_cols d [vec_of_basis_enum a] *
       mat_of_rows d [conjugate (vec_of_basis_enum a)]) *\<^sub>v v =
       v \<bullet>c u / norm2 \<cdot>\<^sub>v u"
    by auto
  thus ?thesis
    unfolding d_def norm2_def mat_of_cblinfun_proj[where 'a = 'a and a = a].
qed


lemma is_ortho_set_corthogonal:
  fixes S :: "'a::onb_enum list"
  defines  "R \<equiv> map vec_of_basis_enum S"
  assumes a1: "is_ortho_set (set S)" and a2: "distinct S"
  shows    "corthogonal R"
  by (smt (verit, ccfv_threshold) R_def a1 a2 cinner_eq_zero_iff corthogonalI cscalar_prod_cinner is_ortho_set_def length_map length_map nth_eq_iff_index_eq nth_map nth_map nth_mem nth_mem)

lemma corthogonal_is_ortho_set:
  fixes vs :: "'a::onb_enum list"
  assumes "corthogonal (map vec_of_basis_enum vs)"
  shows "is_ortho_set (set vs)"
  by (smt (verit, ccfv_SIG) assms cinner_eq_zero_iff corthogonal_def cscalar_prod_cinner in_set_conv_nth is_ortho_set_def length_map nth_map)

definition "is_subspace_of n vs ws = 
  (let ws' = gram_schmidt0 n ws in
     \<forall>v\<in>set vs. adjuster n v ws' = - v)"

lemma Span_leq:
  fixes A B :: "'a::{basis_enum,complex_normed_vector} list"
  shows "(ccspan (set A) \<le> ccspan (set B)) \<longleftrightarrow>
    is_subspace_of (canonical_basis_length TYPE('a)) 
      (map vec_of_basis_enum A) (map vec_of_basis_enum B)"
proof -
  define d Av Bv Bo
    where "d = canonical_basis_length TYPE('a)"
      and "Av = map vec_of_basis_enum A"
      and "Bv = map vec_of_basis_enum B"
      (* and "Ao = gram_schmidt0 d Av" *)
      and "Bo = gram_schmidt0 d Bv" 
  interpret complex_vec_space d.

  have Av_carrier: "set Av \<subseteq> carrier_vec d"
    unfolding Av_def apply auto
    by (simp add: carrier_vecI d_def dim_vec_of_basis_enum')
  have Bv_carrier: "set Bv \<subseteq> carrier_vec d"
    unfolding Bv_def apply auto
    by (simp add: carrier_vecI d_def dim_vec_of_basis_enum')
  have Bo_carrier: "set Bo \<subseteq> carrier_vec d"
    apply (simp add: Bo_def)
    using Bv_carrier by (rule gram_schmidt0_result(1))
  have orth_Bo: "corthogonal Bo"
    apply (simp add: Bo_def)
    using Bv_carrier by (rule gram_schmidt0_result(3))
  have distinct_Bo: "distinct Bo"
    apply (simp add: Bo_def)
    using Bv_carrier by (rule gram_schmidt0_result(2))

  have "ccspan (set A) \<le> ccspan (set B) \<longleftrightarrow> cspan (set A) \<subseteq> cspan (set B)"
    apply (transfer fixing: A B)
    apply (subst closure_finite_cspan, simp)
    by (subst closure_finite_cspan, simp_all)
  also have "\<dots> \<longleftrightarrow> span (set Av) \<subseteq> span (set Bv)"
    apply (simp add: Av_def Bv_def)
    apply (subst module_span_cspan, simp add: d_def)
    apply (subst module_span_cspan, simp add: d_def)
    by (metis inj_image_subset_iff inj_on_def basis_enum_of_vec_inverse)
  also have "\<dots> \<longleftrightarrow> span (set Av) \<subseteq> span (set Bo)"
    unfolding Bo_def Av_def Bv_def
    apply (subst gram_schmidt0_result(4)[symmetric])
    by (simp_all add: carrier_dim_vec d_def dim_vec_of_basis_enum' image_subset_iff)
  also have "\<dots> \<longleftrightarrow> (\<forall>v\<in>set Av. adjuster d v Bo = - v)"
  proof (intro iffI ballI)
    fix v assume "v \<in> set Av" and "span (set Av) \<subseteq> span (set Bo)"
    then have "v \<in> span (set Bo)"
      using Av_carrier span_mem by auto
    have "adjuster d v Bo + v = 0\<^sub>v d"
      apply (rule adjuster_already_in_span)
      using Av_carrier \<open>v \<in> set Av\<close> Bo_carrier orth_Bo
        \<open>v \<in> span (set Bo)\<close> by simp_all
    then show "adjuster d v Bo = - v"
      using Av_carrier Bo_carrier \<open>v \<in> set Av\<close>
      by (metis (no_types, lifting) add.inv_equality adjuster_carrier' local.vec_neg subsetD)
  next
    fix v
    assume adj_minusv: "\<forall>v\<in>set Av. adjuster d v Bo = - v"
    have *: "adjuster d v Bo \<in> span (set Bo)" if "v \<in> set Av" for v
      apply (rule adjuster_in_span)
      using Bo_carrier that Av_carrier distinct_Bo by auto
    have "v \<in> span (set Bo)" if "v \<in> set Av" for v
      using *[OF that] adj_minusv[rule_format, OF that]
      apply auto
      by (metis (no_types, lifting) Av_carrier Bo_carrier adjust_nonzero distinct_Bo subsetD that uminus_l_inv_vec)
    then show "span (set Av) \<subseteq> span (set Bo)"
      apply auto
      by (meson Bo_carrier in_mono span_subsetI subsetI)
  qed
  also have "\<dots> = is_subspace_of d Av Bv"
    by (simp add: is_subspace_of_def d_def Bo_def)
  finally show "ccspan (set A) \<le> ccspan (set B) \<longleftrightarrow> is_subspace_of d Av Bv"
    by simp
qed

lemma apply_cblinfun_Span: 
  "A *\<^sub>S ccspan (set S) = ccspan (basis_enum_of_vec ` set (map ((*\<^sub>v) (mat_of_cblinfun A)) (map vec_of_basis_enum S)))"
  apply (auto simp: cblinfun_image_Span image_image)
  by (metis mat_of_cblinfun_description basis_enum_of_vec_inverse)


text \<open>\<^term>\<open>mk_projector_orthog d L\<close> takes a list L of d-cdimensional vectors
and returns the projector onto the span of L. (Assuming that all vectors in L are 
orthogonal and nonzero.)\<close>
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
  shows "mk_projector_orthog d (map vec_of_basis_enum S) 
       = mat_of_cblinfun (Proj (ccspan (set S)))"
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
    using that ortho unfolding Snorm_def is_ortho_set_def apply auto
    by (metis left_inverse norm_eq_zero)

  have ortho_Snorm: "is_ortho_set (set Snorm)"
    unfolding is_ortho_set_def
  proof (intro conjI ballI impI)
    fix x y
    show "0 \<notin> set Snorm"
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

  have inj_butter: "inj_on selfbutter (set Snorm)"
  proof (rule inj_onI)
    fix x y 
    assume "x \<in> set Snorm" and "y \<in> set Snorm"
    assume "selfbutter x = selfbutter y"
    then obtain c where xcy: "x = c *\<^sub>C y" and "cmod c = 1"
      using inj_selfbutter_upto_phase by auto
    have "0 \<noteq> cmod (cinner x x)"
      using \<open>x \<in> set Snorm\<close> norm_Snorm
      by force
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
  have distinct': "distinct (map selfbutter Snorm)"
    unfolding distinct_map by simp

  have Span_Snorm: "ccspan (set Snorm) = ccspan (set S)"
    apply (transfer fixing: Snorm S)
    apply (simp add: scaleR_scaleC Snorm_def)
    apply (subst complex_vector.span_image_scale) 
    using is_ortho_set_def ortho by fastforce+

  have "mk_projector_orthog d (map vec_of_basis_enum S)
      = mat_of_cblinfun (sum_list (map selfbutter Snorm))"
    unfolding Snorm_def
  proof (induction S)
    case Nil
    show ?case 
      by (simp add: d_def mat_of_cblinfun_zero)
  next
    case (Cons a S)
    define sumS where "sumS = sum_list (map selfbutter (map (\<lambda>s. s /\<^sub>R norm s) S))"
    with Cons have IH: "mk_projector_orthog d (map vec_of_basis_enum S)
                  = mat_of_cblinfun sumS"
      by simp

    define factor where "factor = inverse ((complex_of_real (norm a))\<^sup>2)"
    have factor': "factor = 1 / (vec_of_basis_enum a \<bullet>c vec_of_basis_enum a)"
      unfolding factor_def cscalar_prod_cinner[symmetric]
      by (simp add: inverse_eq_divide power2_norm_eq_cinner)

    have "mk_projector_orthog d (map vec_of_basis_enum (a # S))
          = factor \<cdot>\<^sub>m (mat_of_cols d [vec_of_basis_enum a] 
                    * mat_of_rows d [conjugate (vec_of_basis_enum a)])
            + mat_of_cblinfun sumS"
      apply (cases S)
       apply (auto simp add: factor' sumS_def d_def mat_of_cblinfun_zero)[1]
      by (auto simp add: IH[symmetric] factor' d_def)

    also have "\<dots> = factor \<cdot>\<^sub>m (mat_of_cols d [vec_of_basis_enum a] *
         mat_adjoint (mat_of_cols d [vec_of_basis_enum a])) + mat_of_cblinfun sumS"
      apply (rule arg_cong[where f="\<lambda>x. _ \<cdot>\<^sub>m (_ * x) + _"])
      apply (rule mat_eq_iff[THEN iffD2])
        apply (auto simp add: mat_adjoint_def)
      apply (subst mat_of_rows_index) apply auto
      apply (subst mat_of_rows_index) apply auto
      apply (subst mat_of_cols_index) apply auto
      by (simp add: assms(1) dim_vec_of_basis_enum')
    also have "\<dots> = mat_of_cblinfun (selfbutter (a /\<^sub>R norm a)) + mat_of_cblinfun sumS"
      apply (simp add: butterfly_scaleR_left butterfly_scaleR_right power_inverse mat_of_cblinfun_scaleR factor_def)
      apply (simp add: butterfly_def cblinfun_of_mat_timesOp
          mat_of_cblinfun_adjoint' mat_of_cblinfun_ell2_to_l2bounded d_def)
      by (simp add: cblinfun_of_mat_timesOp mat_of_cblinfun_adjoint' mat_of_cblinfun_ell2_to_l2bounded mat_of_cblinfun_scalarMult power2_eq_square)
    finally show ?case
      by (simp add: mat_of_cblinfun_plus sumS_def)
  qed
  also have "\<dots> = mat_of_cblinfun (\<Sum>s\<in>set Snorm. selfbutter s)"
    by (metis distinct' distinct_map sum.distinct_set_conv_list)
  also have "\<dots> = mat_of_cblinfun (\<Sum>s\<in>set Snorm. proj s)"
    apply (rule arg_cong[where f="mat_of_cblinfun"])
    apply (rule sum.cong[OF refl])
    apply (rule butterfly_eq_proj)
    using norm_Snorm by simp
  also have "\<dots> = mat_of_cblinfun (Proj (ccspan (set Snorm)))"
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
    also have "\<dots> = proj a + Proj (ccspan (set Snorm))"
      apply (subst Cons.IH)
      using Cons.prems apply auto
      by (meson Cons.prems(1) is_ortho_set_antimono set_subset_Cons)
    also have "\<dots> = Proj (ccspan ({a} \<union> set Snorm))"
      apply (rule Proj_orthog_ccspan_union[symmetric])
      by (metis Cons.prems(1) \<open>a \<notin> set Snorm\<close> is_ortho_set_def list.set_intros(1) list.set_intros(2) singleton_iff)
    finally show ?case
      by simp
  qed
  also have "\<dots> = mat_of_cblinfun (Proj (ccspan (set S)))"
    unfolding Span_Snorm by simp
  finally show ?thesis
    by -
qed

lemma mat_of_cblinfun_Proj_Span: 
  fixes S :: "'a::onb_enum list"
  shows "mat_of_cblinfun (Proj (ccspan (set S))) =
    (let d = canonical_basis_length TYPE('a) in 
      mk_projector_orthog d (gram_schmidt0 d (map vec_of_basis_enum S)))"
proof-
  define d gs 
    where "d = canonical_basis_length TYPE('a)"
      and "gs = gram_schmidt0 d (map vec_of_basis_enum S)"
  interpret complex_vec_space d.
  have gs_dim: "x \<in> set gs \<Longrightarrow> dim_vec x = d" for x
    by (smt carrier_vecD carrier_vec_dim_vec d_def dim_vec_of_basis_enum' ex_map_conv gram_schmidt0_result(1) gs_def subset_code(1))
  have ortho_gs: "is_ortho_set (set (map basis_enum_of_vec gs :: 'a list))"
    apply (rule corthogonal_is_ortho_set)
    by (smt carrier_dim_vec cof_vec_space.gram_schmidt0_result(1) d_def dim_vec_of_basis_enum' gram_schmidt0_result(3) gs_def imageE map_idI map_map o_apply set_map subset_code(1) basis_enum_of_vec_inverse')
  have distinct_gs: "distinct (map basis_enum_of_vec gs :: 'a list)"
    by (metis (mono_tags, hide_lams) carrier_vec_dim_vec cof_vec_space.gram_schmidt0_result(2) d_def dim_vec_of_basis_enum' distinct_map gs_def gs_dim image_iff inj_on_inverseI set_map subsetI basis_enum_of_vec_inverse')

  have "mk_projector_orthog d gs 
      = mk_projector_orthog d (map vec_of_basis_enum (map basis_enum_of_vec gs :: 'a list))"
    apply simp
    apply (subst map_cong[where ys=gs and g=id], simp)
    using gs_dim by (auto intro!: basis_enum_of_vec_inverse simp: d_def)
  also have "\<dots> = mat_of_cblinfun (Proj (ccspan (set (map basis_enum_of_vec gs :: 'a list))))"
    unfolding d_def
    apply (subst mat_of_cblinfun_Proj_Span_aux_1)
    using ortho_gs distinct_gs by auto
  also have "\<dots> = mat_of_cblinfun (Proj (ccspan (set S)))"
    apply (rule arg_cong[where f="\<lambda>x. mat_of_cblinfun (Proj x)"])
    unfolding gs_def d_def
    apply (subst Span_basis_enum_gram_schmidt0)
    by (auto simp add: carrier_vecI dim_vec_of_basis_enum')
  finally show ?thesis
    unfolding d_def gs_def by auto
qed

lemma vec_of_basis_enum_ell2_index:
  fixes \<psi> :: \<open>'a::enum ell2\<close> 
  assumes [simp]: \<open>i < CARD('a)\<close>
  shows \<open>vec_of_basis_enum \<psi> $ i = Rep_ell2 \<psi> (Enum.enum ! i)\<close>
proof -
  let ?i = \<open>Enum.enum ! i\<close>
  have \<open>Rep_ell2 \<psi> (Enum.enum ! i) = \<langle>ket ?i, \<psi>\<rangle>\<close>
    by (simp add: cinner_ket_left)
  also have \<open>\<dots> = vec_of_basis_enum \<psi> \<bullet>c vec_of_basis_enum (ket ?i :: 'a ell2)\<close>
    by (rule cscalar_prod_cinner)
  also have \<open>\<dots> = vec_of_basis_enum \<psi> \<bullet>c unit_vec (CARD('a)) i\<close>
    by (simp add: vec_of_basis_enum_ket enum_idx_enum)
  also have \<open>\<dots> = vec_of_basis_enum \<psi> \<bullet> unit_vec (CARD('a)) i\<close>
    by (smt (verit, best) assms carrier_vecI conjugate_conjugate_sprod conjugate_id conjugate_vec_sprod_comm dim_vec_conjugate eq_vecI index_unit_vec(3) scalar_prod_left_unit vec_index_conjugate)
  also have \<open>\<dots> = vec_of_basis_enum \<psi> $ i\<close>
    by simp
  finally show ?thesis
    by simp
qed


lemma mat_of_cblinfun_ell2_index:
  fixes a :: \<open>'a::enum ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::enum ell2\<close> 
  assumes [simp]: \<open>i < CARD('b)\<close> \<open>j < CARD('a)\<close>
  shows \<open>mat_of_cblinfun a $$ (i,j) = Rep_ell2 (a *\<^sub>V ket (Enum.enum ! j)) (Enum.enum ! i)\<close>
proof -
  let ?i = \<open>Enum.enum ! i\<close> and ?j = \<open>Enum.enum ! j\<close> and ?aj = \<open>a *\<^sub>V ket (Enum.enum ! j)\<close>
  have \<open>Rep_ell2 ?aj (Enum.enum ! i) = vec_of_basis_enum ?aj $ i\<close>
    by (rule vec_of_basis_enum_ell2_index[symmetric], simp)
  also have \<open>\<dots> = (mat_of_cblinfun a *\<^sub>v vec_of_basis_enum (ket (enum_class.enum ! j) :: 'a ell2)) $ i\<close>
    by (simp add: mat_of_cblinfun_description)
  also have \<open>\<dots> = (mat_of_cblinfun a *\<^sub>v unit_vec CARD('a) j) $ i\<close>
    by (simp add: vec_of_basis_enum_ket enum_idx_enum)
  also have \<open>\<dots> = mat_of_cblinfun a $$ (i, j)\<close>
    apply (subst mat_entry_explicit[where m=\<open>CARD('b)\<close>])
    by auto
  finally show ?thesis
    by auto
qed

lemma cblinfun_eq_mat_of_cblinfunI: 
  assumes "mat_of_cblinfun a = mat_of_cblinfun b"
  shows "a = b"
  by (metis assms mat_of_cblinfun_inverse)


lemma ell2_eq_vec_of_basis_enumI:
  fixes a b :: "_::basis_enum"
  assumes "vec_of_basis_enum a = vec_of_basis_enum b"
  shows "a = b"
  by (metis assms basis_enum_of_vec_inverse)


lemma mat_of_cblinfun_sandwich:
  fixes a :: "(_::onb_enum, _::onb_enum) cblinfun"
  shows \<open>mat_of_cblinfun (sandwich a *\<^sub>V b) = (let a' = mat_of_cblinfun a in a' * mat_of_cblinfun b * mat_adjoint a')\<close>
  by (simp add: cblinfun_of_mat_timesOp sandwich_apply Let_def mat_of_cblinfun_adjoint')


unbundle no_jnf_notation
unbundle no_cblinfun_notation


end

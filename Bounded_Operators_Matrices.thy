theory Bounded_Operators_Matrices
  imports Complex_L2 Jordan_Normal_Form_Missing Jordan_Normal_Form.Gram_Schmidt 
begin

hide_const (open) Order.bottom Order.top

subsection\<open>\<open>Jordan_Normal_Form_Notation\<close> -- Cleaning up syntax from \<^session>\<open>Jordan_Normal_Form\<close>\<close>

text \<open>\<^const>\<open>Finite_Cartesian_Product.vec_nth\<close> collides with the notation from \<^session>\<open>Jordan_Normal_Form\<close>\<close>
no_notation vec_nth (infixl "$" 90)

unbundle jnf_notation
unbundle cblinfun_notation


subsection \<open>Setting up code generation for type cblinfun\<close>

text \<open>We define the canonical isomorphism between \<^typ>\<open>'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum\<close>
  and the complex \<^term>\<open>n*m\<close>-matrices (where n,m are the dimensions of 'a,'b, 
  respectively). This is possible if \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close> are of class \<^class>\<open>onb_enum\<close>
  since that class fixes a finite canonical basis. Matrices are represented using
  the \<^typ>\<open>_ mat\<close> type from \<^session>\<open>Jordan_Normal_Form\<close>.\<close>
  (* TODO: Define (canonical isomorphism). *)
  (* Jose: More details please *)

primrec vec_of_onb_enum_list :: \<open>'a list \<Rightarrow> 'a::{basis_enum,complex_inner} \<Rightarrow> nat \<Rightarrow> complex vec\<close> where
  \<open>vec_of_onb_enum_list [] v _ = 0\<^sub>v (length (canonical_basis::'a list))\<close> |
  \<open>vec_of_onb_enum_list (x#ys) v i = vec_of_onb_enum_list ys v (Suc i) +
    \<langle>x, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i\<close>


definition vec_of_onb_enum :: \<open>'a::basis_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_onb_enum v = vec_of_list (map (complex_vector.representation (set canonical_basis) v) canonical_basis)\<close>

lemma dim_vec_of_onb_enum_list:
  \<open>dim_vec (vec_of_onb_enum_list (L::'a list) v i) = length (canonical_basis::'a::{basis_enum,complex_inner} list)\<close>
  by (induction L, auto)

lemma dim_vec_of_onb_enum_list':
  \<open>dim_vec (vec_of_onb_enum (v::'a)) = length (canonical_basis::'a::basis_enum list)\<close>
  unfolding vec_of_onb_enum_def 
  using dim_vec_of_onb_enum_list
  by simp  

lemma vec_of_onb_enum_list_add:
  \<open>vec_of_onb_enum_list (L::'a::{basis_enum,complex_inner} list) (v1 + v2) i =
   vec_of_onb_enum_list L v1 i + vec_of_onb_enum_list L v2 i\<close>
proof (induction L arbitrary : i)
  case Nil thus ?case by simp
next
  case (Cons a L)
  have "vec_of_onb_enum_list (a # L) (v1 + v2) i = 
    vec_of_onb_enum_list L (v1 + v2) (Suc i) +
    \<langle>a, v1 + v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i"
    by simp
  moreover have "vec_of_onb_enum_list L (v1 + v2) (Suc i) = 
  vec_of_onb_enum_list L v1 (Suc i) + vec_of_onb_enum_list L v2 (Suc i)"
    by (simp add: Cons.IH)
  moreover have "\<langle>a, v1 + v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i = 
                 \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i + 
                 \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i"
    by (simp add: add_smult_distrib_vec cinner_right_distrib)
  ultimately have "vec_of_onb_enum_list (a # L) (v1 + v2) i = 
                   vec_of_onb_enum_list L v1 (Suc i)
                 + vec_of_onb_enum_list L v2 (Suc i)
                 + \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i 
                 + \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i"
    by auto
  also have "\<dots> = (vec_of_onb_enum_list L v1 (Suc i) + \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i)
    + (vec_of_onb_enum_list L v2 (Suc i) + \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i)"
  proof-
    have w1: "\<lbrakk>dim_vec a = n; dim_vec b = n; dim_vec c = n; dim_vec d = n\<rbrakk>
        \<Longrightarrow> a + b + c + d = (a + c) + (b + d)" for a b c d::"complex vec" and n
      by auto
    thus ?thesis
      by (simp add: dim_vec_of_onb_enum_list) 
  qed
  finally have "vec_of_onb_enum_list (a # L) (v1 + v2) i = 
  (vec_of_onb_enum_list L v1 (Suc i) + \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i)
+ (vec_of_onb_enum_list L v2 (Suc i) + \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i)"
    by simp
  moreover have "vec_of_onb_enum_list L v1 (Suc i)
                + \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i 
                = vec_of_onb_enum_list (a # L) v1 i"
    by simp
  moreover have "vec_of_onb_enum_list L v2 (Suc i)
                + \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i =
                vec_of_onb_enum_list (a # L) v2 i"
    by simp
  ultimately show "vec_of_onb_enum_list (a # L) (v1 + v2) i =
       vec_of_onb_enum_list (a # L) v1 i +
       vec_of_onb_enum_list (a # L) v2 i"
    by smt
qed

lemma vec_of_onb_enum_list_mult:
  fixes L :: "'a::{basis_enum,complex_inner} list"
  shows \<open>vec_of_onb_enum_list L (c *\<^sub>C v) i = c \<cdot>\<^sub>v vec_of_onb_enum_list L v i\<close>
proof(induction L arbitrary: i)
  case Nil
  thus ?case by auto
next
  case (Cons a L)
  have "vec_of_onb_enum_list (a # L) (c *\<^sub>C v) i = 
    vec_of_onb_enum_list L (c *\<^sub>C v) (Suc i) +
    c * \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i"
    by simp
  also have "\<dots> = 
    c \<cdot>\<^sub>v vec_of_onb_enum_list L v (Suc i) +
    c * \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i"
    by (simp add: Cons.IH)
  also have "\<dots> = 
    c \<cdot>\<^sub>v (vec_of_onb_enum_list L v (Suc i) +
           \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i)"
  proof-
    have "\<lbrakk>dim_vec x = n; dim_vec y = n\<rbrakk> \<Longrightarrow> 
         c \<cdot>\<^sub>v x + c \<cdot>\<^sub>v y = c \<cdot>\<^sub>v (x + y)" for x y::"complex vec" and n
      by (metis carrier_vec_dim_vec smult_add_distrib_vec)      
    thus ?thesis
      by (metis dim_vec_of_onb_enum_list index_smult_vec(2) index_unit_vec(3) smult_smult_assoc) 
  qed
  finally show "vec_of_onb_enum_list (a # L) (c *\<^sub>C v) i =
        c \<cdot>\<^sub>v vec_of_onb_enum_list (a # L) v i"
    by simp
qed

fun onb_enum_of_vec_list :: \<open>'a list \<Rightarrow> complex list \<Rightarrow> 'a::complex_vector\<close> where 
  \<open>onb_enum_of_vec_list [] v = 0\<close> |
  \<open>onb_enum_of_vec_list y [] = 0\<close> |
  \<open>onb_enum_of_vec_list (x#ys) (v#vs) = v *\<^sub>C x + onb_enum_of_vec_list ys vs\<close>

lemma onb_enum_of_vec_list_def': "onb_enum_of_vec_list xs ys = sum_list (map2 (*\<^sub>C) ys xs)"
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

definition onb_enum_of_vec :: \<open>complex vec \<Rightarrow> 'a::basis_enum\<close> where
  \<open>onb_enum_of_vec v = 
    (if dim_vec v = canonical_basis_length TYPE('a)
     then onb_enum_of_vec_list (canonical_basis::'a list) (list_of_vec v)
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

lemma onb_enum_of_vec_add:
  assumes \<open>dim_vec v1 = canonical_basis_length TYPE('a::basis_enum)\<close> and
    \<open>dim_vec v2 = canonical_basis_length TYPE('a)\<close>
  shows \<open>((onb_enum_of_vec (v1 + v2)) :: 'a) = onb_enum_of_vec v1 + onb_enum_of_vec v2\<close>
proof -
  define l1 l2 where "l1 = list_of_vec v1" and "l2 = list_of_vec v2"
  define basis where "basis = (canonical_basis::'a list)"
  have length: "length l1 = length l2"
    by (simp add: assms l1_def l2_def)
  have length_basis: "length l2 = length basis"
    by (simp add: assms basis_def l2_def canonical_basis_length_eq)
  have \<open>(onb_enum_of_vec::_\<Rightarrow>'a) (v1 + v2) = onb_enum_of_vec_list basis (list_of_vec (v1+v2))\<close>
    by (simp add: basis_def onb_enum_of_vec_def assms)
  also have \<open>\<dots> = onb_enum_of_vec_list basis (map2 (+) l1 l2)\<close>
    apply (subst list_of_vec_plus)
    using assms l1_def l2_def by auto
  also have \<open>\<dots> = onb_enum_of_vec_list basis l1
           + onb_enum_of_vec_list basis l2\<close>
    using length length_basis
  proof (induction l1 l2 basis rule: list_induct3)
    case Nil
    thus ?case
      using onb_enum_of_vec_list.elims by auto 
  next
    case (Cons x xs y ys z zs)
    assume \<open>length xs = length ys\<close> and \<open>length ys = length zs\<close> and
      \<open>onb_enum_of_vec_list zs (map2 (+) xs ys) =
       onb_enum_of_vec_list zs xs + onb_enum_of_vec_list zs ys\<close>
    have \<open>onb_enum_of_vec_list (z # zs) (map2 (+) (x # xs) (y # ys)) =
       (x + y) *\<^sub>C z + onb_enum_of_vec_list zs (map2 (+) xs ys)\<close>
      by auto
    also have \<open>\<dots> =
       (x + y) *\<^sub>C z + onb_enum_of_vec_list zs xs + onb_enum_of_vec_list zs ys\<close>
      using \<open>onb_enum_of_vec_list zs (map2 (+) xs ys) =
       onb_enum_of_vec_list zs xs + onb_enum_of_vec_list zs ys\<close>
      by auto
    also have \<open>\<dots> =
       x *\<^sub>C z + y *\<^sub>C z + onb_enum_of_vec_list zs xs + onb_enum_of_vec_list zs ys\<close>
    proof-
      have \<open>(x + y) *\<^sub>C z = x *\<^sub>C z + y *\<^sub>C z\<close>
        by (simp add: scaleC_left.add)
      thus ?thesis
        by simp 
    qed
    also have \<open>\<dots> =
       (x *\<^sub>C z + onb_enum_of_vec_list zs xs) + (y *\<^sub>C z + onb_enum_of_vec_list zs ys)\<close>
      by simp
    also have \<open>\<dots> =
       onb_enum_of_vec_list (z # zs) (x # xs) +
       onb_enum_of_vec_list (z # zs) (y # ys)\<close>
      by simp
    finally show \<open>onb_enum_of_vec_list (z # zs) (map2 (+) (x # xs) (y # ys)) =
       onb_enum_of_vec_list (z # zs) (x # xs) +
       onb_enum_of_vec_list (z # zs) (y # ys)\<close> 
      by blast
  qed
  also have \<open>\<dots> = onb_enum_of_vec v1 + onb_enum_of_vec v2\<close>
    by (simp add: basis_def onb_enum_of_vec_def l1_def l2_def assms)
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

lemma onb_enum_of_vec_mult:
  assumes \<open>dim_vec v = canonical_basis_length TYPE('a::basis_enum)\<close> 
  shows \<open>((onb_enum_of_vec (c \<cdot>\<^sub>v v)) :: 'a) =  c *\<^sub>C onb_enum_of_vec v\<close>
proof -
  define basis where "basis \<equiv> canonical_basis::'a::basis_enum list"
  define l where "l = list_of_vec v"
  have length_basis: "length l = length basis"
    by (simp add: assms basis_def canonical_basis_length_eq l_def)
  have \<open>(onb_enum_of_vec::_\<Rightarrow>'a) (c \<cdot>\<^sub>v v) =
 onb_enum_of_vec_list basis (list_of_vec (c \<cdot>\<^sub>v v))\<close>
    by (simp add: basis_def onb_enum_of_vec_def assms)
  also have \<open>\<dots> = onb_enum_of_vec_list basis (map ((*) c) (list_of_vec v))\<close>
    apply (subst list_of_vec_mult)
    by auto
  also have \<open>\<dots> = onb_enum_of_vec_list basis (map ((*) c) l)\<close>
    using l_def by auto
  also have \<open>\<dots> = c *\<^sub>C (onb_enum_of_vec_list basis l)\<close>
    using length_basis
  proof (induction l basis rule: list_induct2)
    case Nil
    thus ?case by auto
  next
    case (Cons x xs y ys)
    assume \<open>length xs = length ys\<close> and 
      \<open>onb_enum_of_vec_list ys (map ((*) c) xs) =
       c *\<^sub>C onb_enum_of_vec_list ys xs\<close> 
    have \<open>onb_enum_of_vec_list (y # ys)
        (map ((*) c) (x # xs)) = (c * x) *\<^sub>C y +
    onb_enum_of_vec_list ys (map ((*) c) xs)\<close>
      by auto
    also have \<open>\<dots> = (c * x) *\<^sub>C y + c *\<^sub>C onb_enum_of_vec_list ys xs\<close>
      by (simp add: Cons.IH)
    also have \<open>\<dots> = c *\<^sub>C (x *\<^sub>C y) + c *\<^sub>C onb_enum_of_vec_list ys xs\<close>
      by simp
    also have \<open>\<dots> = c *\<^sub>C (x *\<^sub>C y + onb_enum_of_vec_list ys xs)\<close>
      by (simp add: scaleC_add_right)
    also have \<open>\<dots>  =
       c *\<^sub>C onb_enum_of_vec_list (y # ys) (x # xs)\<close>
      by simp
    finally show \<open>onb_enum_of_vec_list (y # ys)
        (map ((*) c) (x # xs)) =
       c *\<^sub>C onb_enum_of_vec_list (y # ys) (x # xs)\<close>
      by blast
  qed
  also have \<open>\<dots> = c *\<^sub>C onb_enum_of_vec v\<close>
    by (simp add: basis_def onb_enum_of_vec_def l_def assms)
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
 "(x \<in> Complex_Vector_Spaces.span (insert a S)) = (x - \<langle>a, x\<rangle> *\<^sub>C a \<in> Complex_Vector_Spaces.span S)"
proof
  show "x - \<langle>a, x\<rangle> *\<^sub>C a \<in> Complex_Vector_Spaces.span S"
    if "x \<in> Complex_Vector_Spaces.span (insert a S)"
  proof-
    have "\<exists>k. x - k *\<^sub>C a \<in> Complex_Vector_Spaces.span S"
      using that
      by (simp add: complex_vector.span_breakdown_eq)
    then obtain k where "x - k *\<^sub>C a \<in> Complex_Vector_Spaces.span S"
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
        by (metis (mono_tags, lifting) c2 mult_not_zero subset_eq sum_not_0)
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
    ultimately show ?thesis by (smt \<open>x - k *\<^sub>C a \<in> Complex_Vector_Spaces.span S\<close> mult_cancel_left1)
  qed
  show "x \<in> Complex_Vector_Spaces.span (insert a S)"
    if "x - \<langle>a, x\<rangle> *\<^sub>C a \<in> Complex_Vector_Spaces.span S"
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
    have "set (a # L) = insert a (set L)"
      by simp
    moreover have "a \<in> sphere 0 1"
      using Cons.prems(4) by auto      
    ultimately have "w - \<langle>a, w\<rangle> *\<^sub>C a \<in> complex_vector.span (set L)"
      using Cons.prems(1) cinner_span_breakdown_eq[where S = "set L" and x = w and a = a]
        Cons.prems(2) Cons.prems(3) distinct.simps(2) 
      by (smt mem_sphere_0) 
    moreover have "is_ortho_set (set L)"
      unfolding is_ortho_set_def 
    proof auto
      show "x \<in> set L \<Longrightarrow>
           y \<in> set L \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<langle>x, y\<rangle> = 0"
        for x y
      proof-
      assume o1: "x \<in> set L" and o2: "y \<in> set L" and o3: "x \<noteq> y" 
      have "x \<in> set (a#L)"
        by (simp add: o1)        
      moreover have "y \<in> set (a#L)"
        by (simp add: o2)
      ultimately show "\<langle>x, y\<rangle> = 0"
        using o3 Cons.prems(3) is_ortho_set_def by metis
      qed
      show "0 \<in> set L \<Longrightarrow> False"
        using Cons.prems(4) by auto        
    qed
    moreover have "\<forall>a\<in>set L. \<parallel>a\<parallel> = 1"
      using Cons.prems(4) by auto      
    ultimately have "(\<Sum>b\<in>(set L). \<langle>b, w - \<langle>a, w\<rangle> *\<^sub>C a\<rangle> *\<^sub>C b) = w - \<langle>a, w\<rangle> *\<^sub>C a"
    proof -
      have "is_ortho_set (set L)"
        using Cons.prems(3) is_onb_delete by fastforce
      thus ?thesis
        using Cons.IH \<open>\<forall>a\<in>set L. \<parallel>a\<parallel> = 1\<close> \<open>distinct (a # L)\<close> \<open>w - \<langle>a, w\<rangle> *\<^sub>C a \<in> complex_span (set L)\<close> by fastforce
    qed

    thus ?thesis by simp
  qed
  also have "\<dots> = w"
    by simp
  finally have "(\<Sum>b\<in>set (a # L). \<langle>b, w\<rangle> *\<^sub>C b) = w"
    by blast
  thus "w = (\<Sum>b\<in>set (a # L). \<langle>b, w\<rangle> *\<^sub>C b)" by simp
qed

lemma canonical_basis_inner:
  "w = (\<Sum>b\<in>set (canonical_basis::'a::onb_enum list). \<langle>b, w\<rangle> *\<^sub>C b)"
  apply (rule Ortho_expansion_finite)
  using is_generator_set apply auto[1]
  apply auto[1]
  apply (simp add: is_orthonormal)
  by (simp add: is_normal)

lemma onb_enum_of_vec_expansion:  
  fixes S::"'a::basis_enum list" and L::"complex list"
  assumes "length S = length L" and "distinct S"
  shows   "sum_list (map2 (\<lambda>l s. l *\<^sub>C s) L S)
             = (\<Sum>i\<in>{0..<length S}. L!i *\<^sub>C S!i)"
  using assms sum_list_sum_nth[where xs = "map2 (*\<^sub>C) L S"]
  by auto

lemma length_list_of_vec_vec_of_onb_enum_list:
  fixes w::"'a::{basis_enum,complex_inner}" and S::"'a list"
  shows "length (list_of_vec (vec_of_onb_enum_list S w i)) = length (canonical_basis::'a list)"
  by (simp add: dim_vec_of_onb_enum_list)

lemma list_of_vec_unit_vec:
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
qed

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
  hence g2: "card (set S) > dim (UNIV:: 'a set)"
    using g1 
    by (smt \<open>\<not> length S \<le> length basis\<close> \<open>finite (set basis)\<close> basis_def complex_vector.dim_le_card' 
        complex_vector.dim_span distinct_canonical_basis distinct_card f2 not_le_imp_less 
        order.trans)
  hence "complex_vector.span (set S) \<subseteq> (UNIV:: 'a set)"
    by simp
  hence "card (set S) \<le> dim (UNIV:: 'a set)"
    using f1 h1 Complex_Vector_Spaces.dependent_raw_def 
      complex_vector.dim_le_card complex_vector.dim_span_eq_card_independent 
      distinct_canonical_basis distinct_card f2 
    by (smt \<open>Complex_Vector_Spaces.span (set basis) = UNIV\<close> \<open>\<not> length S \<le> length basis\<close> 
        \<open>finite (set basis)\<close> basis_def) 
  thus ?thesis using g2 by (smt leD)
qed

(* TODO: should be called vec_of_onb_enum_inverse *)
lemma onb_enum_of_vec_inverse[simp]:
  fixes w::"'a::onb_enum"
  shows  "onb_enum_of_vec (vec_of_onb_enum w) = w"
  unfolding vec_of_onb_enum_def onb_enum_of_vec_def onb_enum_of_vec_list_def'
  unfolding list_vec zip_map1 zip_same_conv_map map_map 
  apply (simp add: o_def canonical_basis_length_eq)
  apply (subst sum.distinct_set_conv_list[symmetric], simp)
  apply (rule complex_vector.sum_representation_eq)
  using is_complex_independent_set apply auto[1]    
  using  is_generator_set apply auto[1]
  apply simp
  by simp

lemma uniq_linear_expansion_sum_list_zero:
  fixes f::"'a::{basis_enum,complex_inner} \<Rightarrow> complex"
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
      using basis_def calculation is_complex_independent_set
      by blast 
    ultimately show ?thesis 
      by (metis Complex_Vector_Spaces.dependent_raw_def)
  qed
  moreover have "b \<noteq> 0"  
    using Complex_Vector_Spaces.complex_vector.dependent_zero[where A = "set basis"]
      h1 is_complex_independent_set unfolding basis_def
    by blast
  ultimately have "-f b = 0"
    by simp
  thus ?thesis by simp
qed

lemma uniq_linear_expansion_sum_list:
  fixes f g::"'a::{basis_enum,complex_inner} \<Rightarrow> complex"
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

(* TODO: rename: onb_enum_of_vec_inverse *)
lemma vec_of_onb_enum_inverse[simp]:
  fixes v::"complex vec"
  defines "n == canonical_basis_length TYPE('a::{basis_enum,complex_inner})"
  assumes f1: "dim_vec v = n"
  shows "vec_of_onb_enum ((onb_enum_of_vec v)::'a) = v"
proof- 
  define w where "w = list_of_vec v"
  define basis where "basis = (canonical_basis::'a list)"
  have length_w: "length w = dim_vec v"
    using f1 unfolding w_def
    by simp 
  hence length_basis: "length basis = length w"
    by (simp add: basis_def canonical_basis_length_eq f1 n_def)    
  have "map (complex_vector.representation (set basis) (onb_enum_of_vec_list basis w)) basis = w"
  proof-
    have "i < length basis \<Longrightarrow> 
        complex_vector.representation (set basis) (onb_enum_of_vec_list basis w) (basis!i) = w!i"
      for i
    proof-
      assume h1: "i < length basis"
      have h2: "complex_independent (set basis)"
        by (simp add: basis_def is_complex_independent_set)
      have h3: "onb_enum_of_vec_list basis w \<in> Complex_Vector_Spaces.span (set basis)"
        using basis_def is_generator_set
          by blast 
      define f where 
        "f x = complex_vector.representation (set basis) (onb_enum_of_vec_list basis w) x"
      for x
      have h4: "f x \<noteq> 0 \<Longrightarrow> x \<in> set basis" for x
        by (simp add: complex_vector.representation_ne_zero f_def)
      have h5: "finite {v. f v \<noteq> 0}"
        by (metis \<open>f \<equiv> Complex_Vector_Spaces.representation (set basis) 
            (onb_enum_of_vec_list basis w)\<close> complex_vector.finite_representation)
      have h6: "(\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = onb_enum_of_vec_list basis w"
        using Collect_cong DiffD1 DiffD2 \<open>f \<equiv> Complex_Vector_Spaces.representation (set basis)
         (onb_enum_of_vec_list basis w)\<close> 
            complex_vector.sum_nonzero_representation_eq h2 h3 h5 subset_iff 
            sum.mono_neutral_cong_left
        by (smt ) (* > 1 s*)
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
        by (smt basis_def canonical_basis_length_eq distinct_Ex1 f1 h1 h7 le_neq_implies_less length_basis length_list_of_vec less_not_refl mem_Collect_eq nth_mem set_conv_nth someI_ex sup.strict_order_iff sup_ge2 w_def) 
      have "sum_list (map2 (*\<^sub>C) (map f basis) basis)
            = (\<Sum>b\<leftarrow>basis. f b *\<^sub>C b)"
        by (metis (mono_tags, lifting) basis_def distinct_canonical_basis list.map_ident 
            map2_map_map sum.cong sum_list_distinct_conv_sum_set)        
      also have "(\<Sum>b\<leftarrow>basis. f b *\<^sub>C b) 
            = onb_enum_of_vec_list basis w"
        using \<open>(\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = (\<Sum>b\<leftarrow>basis. f b *\<^sub>C b)\<close> h6 by auto
      also have "\<dots> = sum_list (map2 (*\<^sub>C) w basis)"
        by (simp add: onb_enum_of_vec_list_def')      
      also have "\<dots> = (\<Sum>i\<leftarrow>[0..<n]. w!i *\<^sub>C (basis!i))"
        by (smt basis_def canonical_basis_length_eq f1 length_w map2_map_map map_eq_conv map_nth n_def)
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
        by (smt canonical_basis_length_eq length_map map_nth nth_equalityI nth_map) 
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
    by (simp add: onb_enum_of_vec_def vec_list vec_of_onb_enum_def w_def assms)
qed

lemma vec_of_onb_enum_add:
  "vec_of_onb_enum (b1 + b2) = vec_of_onb_enum b1 + vec_of_onb_enum b2"
proof-
  have "Complex_Vector_Spaces.span
         (set (canonical_basis::'a list)) = UNIV"
    using span_finite_dim is_generator_set
    by (simp add: ) 
  hence "Complex_Vector_Spaces.representation (set (canonical_basis::'a list)) (b1+b2) i
      = Complex_Vector_Spaces.representation (set (canonical_basis::'a list)) b1 i + 
        Complex_Vector_Spaces.representation (set (canonical_basis::'a list)) b2 i" for i
  proof -
    have "\<not> Complex_Vector_Spaces.dependent (set (canonical_basis::'a list))"
      using is_complex_independent_set
      by (simp add: ) 
    thus ?thesis
      by (metis UNIV_I \<open>Complex_Vector_Spaces.span (set canonical_basis) = UNIV\<close> complex_vector.representation_add) (* failed *)
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
    unfolding vec_of_onb_enum_def 
    by auto
qed

lemma vec_of_onb_enum_scaleC:
  "vec_of_onb_enum (c *\<^sub>C b) = c \<cdot>\<^sub>v (vec_of_onb_enum b)"
proof-
  have "Complex_Vector_Spaces.span
         (set (canonical_basis::'a list)) = UNIV"    
    using span_finite_dim is_generator_set
    by (simp add: )
  hence "Complex_Vector_Spaces.representation (set (canonical_basis::'a list)) (c *\<^sub>C b) i
      = c *\<^sub>C (Complex_Vector_Spaces.representation (set (canonical_basis::'a list)) b i)" for i
    using Complex_Vector_Spaces.complex_vector.representation_scale
      Complex_Vector_Spaces.dependent_raw_def UNIV_I complex_scaleC_def
     is_complex_independent_set 
    by (smt ) 
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
    unfolding vec_of_onb_enum_def 
    by auto
qed

lemma vec_of_onb_enum_scaleR:
  "vec_of_onb_enum (r *\<^sub>R b) = complex_of_real r \<cdot>\<^sub>v (vec_of_onb_enum b)"
  by (simp add: scaleR_scaleC vec_of_onb_enum_scaleC)

(* TODO: Move to Jordan...Missing *)
lemma scaleC_minus1_left_vec: "-1 \<cdot>\<^sub>v v = - v" for v :: "_::ring_1 vec"
  unfolding smult_vec_def uminus_vec_def by auto

lemma vec_of_onb_enum_uminus:
  "vec_of_onb_enum (- b2) = - vec_of_onb_enum b2"
  unfolding scaleC_minus1_left[symmetric, of b2]
  unfolding scaleC_minus1_left_vec[symmetric]
  by (rule vec_of_onb_enum_scaleC)

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
      by (simp add: cinner_right_distrib)
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
      using Cons.prems(1) is_onb_delete by auto    
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
      by (simp add: cinner_left_distrib)
    also have "\<dots> = \<langle>x *\<^sub>C b, y *\<^sub>C b\<rangle>
                 +\<langle>x *\<^sub>C b, sum_list (map2 (*\<^sub>C) ys B)\<rangle>
                + \<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b + sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by (simp add: cinner_right_distrib)
    also have "\<dots> = \<langle>x *\<^sub>C b, y *\<^sub>C b\<rangle>
                 +\<langle>x *\<^sub>C b, sum_list (map2 (*\<^sub>C) ys B)\<rangle>
                 +\<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b\<rangle>
                 +\<langle>sum_list (map2 (*\<^sub>C) xs B), sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by (simp add: cinner_right_distrib)
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
        by (metis of_real_hom.hom_one power2_norm_eq_cinner')       
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


lemma vec_of_onb_enum_minus:
  "vec_of_onb_enum (b1 - b2) = vec_of_onb_enum b1 - vec_of_onb_enum b2"
  by (metis (mono_tags, hide_lams) carrier_vec_dim_vec diff_conv_add_uminus diff_zero index_add_vec(2) minus_add_uminus_vec vec_of_onb_enum_add vec_of_onb_enum_uminus)

lemma cinner_onb_enum_of_vec:
  defines "n == canonical_basis_length TYPE('a::onb_enum)"
  assumes w1: "dim_vec x = n" and w2: "dim_vec y = n"
  shows  "\<langle>(onb_enum_of_vec::_\<Rightarrow> 'a) x, (onb_enum_of_vec::_\<Rightarrow> 'a) y\<rangle>
           = y \<bullet>c x"
proof-
  include notation_norm
  define B where "B = (canonical_basis::'a list)"
  have a0: "\<langle>onb_enum_of_vec_list B xs, onb_enum_of_vec_list B ys\<rangle> = 
    sum_list (map2 (\<lambda>x y. cnj x * y) xs ys)"
    if "length xs = length ys" and "length ys = length B"
      and "is_ortho_set (set B)" and "complex_vector.span (set B) = UNIV"
      and "distinct B" and "\<And>t. t\<in>set B \<Longrightarrow> \<parallel>t\<parallel> = 1"
    for xs ys and B :: "'a list"
    unfolding onb_enum_of_vec_list_def'
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
        using is_onb_delete by auto        
      have b1: "\<langle>b', b\<rangle> = 0"
        by (meson Cons.prems(2) \<open>b' \<noteq> b\<close> is_ortho_set_def list.set_intros(1) list.set_intros(2))
      have "\<langle>sum_list (map2 (*\<^sub>C) (x # xs) (b' # B)), b\<rangle> = \<langle>x *\<^sub>C b' + sum_list (map2 (*\<^sub>C) xs B), b\<rangle>"
        by auto
      also have "\<dots> = \<langle>x *\<^sub>C b', b\<rangle> + \<langle>sum_list (map2 (*\<^sub>C) xs B), b\<rangle>"
        by (simp add: cinner_left_distrib)
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
        using is_onb_delete by auto        
      have b1: "\<langle>b', b\<rangle> = 0"
        by (meson Cons.prems(2) \<open>b' \<noteq> b\<close> is_ortho_set_def list.set_intros(1) list.set_intros(2))
      have "\<langle>sum_list (map2 (*\<^sub>C) (x # xs) (b' # B)), b\<rangle> = \<langle>x *\<^sub>C b' + sum_list (map2 (*\<^sub>C) xs B), b\<rangle>"
        by auto
      also have "\<dots> = \<langle>x *\<^sub>C b', b\<rangle> + \<langle>sum_list (map2 (*\<^sub>C) xs B), b\<rangle>"
        by (simp add: cinner_left_distrib)
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
      by (simp add: cinner_left_distrib)
    also have "\<dots> =
    \<langle>x *\<^sub>C b, y *\<^sub>C b\<rangle>
   + \<langle>x *\<^sub>C b, sum_list (map2 (*\<^sub>C) ys B)\<rangle>
   +\<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b + sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by (simp add: cinner_right_distrib)
    also have "\<dots> =
    \<langle>x *\<^sub>C b, y *\<^sub>C b\<rangle>
   +\<langle>x *\<^sub>C b, sum_list (map2 (*\<^sub>C) ys B)\<rangle>
   +\<langle>sum_list (map2 (*\<^sub>C) xs B), y *\<^sub>C b\<rangle>
   +\<langle>sum_list (map2 (*\<^sub>C) xs B), sum_list (map2 (*\<^sub>C) ys B)\<rangle>"
      by (simp add: cinner_right_distrib)
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
        by (metis of_real_hom.hom_one power2_norm_eq_cinner')        
      moreover have "\<langle>sum_list (map2 (*\<^sub>C) xs B), 
                      sum_list (map2 (*\<^sub>C) ys B)\<rangle> =
      sum_list (map2 (\<lambda>x. (*) (cnj x)) xs ys)"
        apply(rule sum_list_orthonormal)
            apply (simp add: Cons.hyps(1))
           apply (simp add: Cons.hyps(2))
        using Cons.prems(1)  apply auto[1]
        using is_onb_delete apply auto[1]
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
    by (simp add: canonical_basis_length_eq w2 w1 n_def)    
  have a1: "\<langle>onb_enum_of_vec_list B (list_of_vec x), onb_enum_of_vec_list B (list_of_vec y)\<rangle>
          = (\<Sum>i = 0..<dim_vec x. cnj (vec_index x i) * (vec_index y i))"
    unfolding onb_enum_of_vec_def 
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
    by (metis (no_types, lifting) B_def mult.commute n_def onb_enum_of_vec_def sum.cong w1 w2)
qed


(* TODO: give better name *)
lemma cinner_ell2_code: "cinner \<psi> \<phi> = cscalar_prod (vec_of_onb_enum \<phi>) (vec_of_onb_enum \<psi>)"
  for \<psi> :: "'a::onb_enum"
  thm cinner_onb_enum_of_vec
  apply (subst cinner_onb_enum_of_vec[symmetric, where 'a='a])
  by (simp_all add: canonical_basis_length_eq dim_vec_of_onb_enum_list')

(* TODO move to JNF_Missing *)
lemma square_nneg_complex:
  fixes x :: complex
  assumes "x \<in> \<real>" shows "x^2 \<ge> 0"
  apply (cases x) using assms unfolding Reals_def by auto


(* TODO move to Preliminaries *)
lemma abs_complex_real[simp]: "abs x \<in> \<real>" for x :: complex
  by (simp add: abs_complex_def)

(* TODO move to Preliminaries *)
lemma Im_abs[simp]: "Im (abs x) = 0"
  using abs_complex_real complex_is_Real_iff by blast


(* TODO: give better name *)
lemma norm_ell2_code: "norm \<psi> = 
  (let \<psi>' = vec_of_onb_enum \<psi> in
    sqrt (\<Sum> i \<in> {0 ..< dim_vec \<psi>'}. let z = vec_index \<psi>' i in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
  (is "_ = ?rhs") for \<psi> :: "'a::onb_enum"
proof -
  have "norm \<psi> = sqrt (cmod (\<Sum>i = 0..<dim_vec (vec_of_onb_enum \<psi>). 
            vec_of_onb_enum \<psi> $ i * conjugate (vec_of_onb_enum \<psi>) $ i))"
    unfolding norm_eq_sqrt_cinner[where 'a='a] cinner_ell2_code scalar_prod_def dim_vec_conjugate
    by rule
  also have "\<dots> = sqrt (cmod (\<Sum>x = 0..<dim_vec (vec_of_onb_enum \<psi>). 
                    let z = vec_of_onb_enum \<psi> $ x in (Re z)\<^sup>2 + (Im z)\<^sup>2))"
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

lemma onb_enum_of_vec_unit_vec:
  defines a1: "basis == (canonical_basis::'a::basis_enum list)"
    and a2: "n == canonical_basis_length TYPE('a)"
  assumes a3: "i < n"  
  shows "onb_enum_of_vec (unit_vec n i) = basis!i"
proof-
  define L::"complex list" where "L = list_of_vec (unit_vec n i)"
  define I::"nat list" where "I = [0..<n]"
  have "length L = n"
    by (simp add: L_def)    
  moreover have "length basis = n"
    by (simp add: a1 a2 canonical_basis_length_eq)
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
  hence "onb_enum_of_vec_list (canonical_basis::'a list) (list_of_vec (unit_vec n i)) 
      = (canonical_basis::'a list) ! i"     
    by (simp add: onb_enum_of_vec_list_def' a1)
  thus ?thesis 
    unfolding onb_enum_of_vec_def
    by (simp add: a1 a2) 
qed


(* TODO: Could be defined on basis_enum (like the vec_of_onb_enum).
   Most of the rules don't need an ONB *)
lift_definition cblinfun_of_mat :: \<open>complex mat \<Rightarrow> 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum\<close> is  
  \<open>\<lambda>M. \<lambda>v. (if M\<in>carrier_mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))
           then onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum v)
           else 0)\<close>
proof
  fix M :: "complex mat"
  define f::"complex mat \<Rightarrow> 'a \<Rightarrow> 'b" 
    where "f M v = (if M\<in>carrier_mat (canonical_basis_length (TYPE('b)::'b itself)) 
                                     (canonical_basis_length (TYPE('a)::'a itself)) 
        then onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum (v::'a)) 
        else (0::'b))" 
    for M::"complex mat" and v::'a
  define m where "m = canonical_basis_length TYPE('b)"
  define n where "n = canonical_basis_length TYPE('a)"

  show "clinear (f M)"
  proof(cases "M\<in>carrier_mat m n")
    case True
    have "f M v = onb_enum_of_vec (M *\<^sub>v (vec_of_onb_enum v))" for v
      using True f_def m_def n_def by auto
    have M_carrier_mat: 
      "M \<in> carrier_mat m n"
      by (simp add: True)
    show ?thesis
      unfolding clinear_def proof
      show "f M (b1 + b2) = f M b1 + f M b2"
        for b1 :: 'a
          and b2 :: 'a
      proof-
        have dim1: "dim_vec (vec_of_onb_enum b1) = n"
          by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list' n_def)

        have dim2: "dim_vec (vec_of_onb_enum b2) = n"
          by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list' n_def)

        have "vec_of_onb_enum (b1 + b2) = vec_of_onb_enum b1 + vec_of_onb_enum b2"
          by (simp add: vec_of_onb_enum_add)
        have "vec_of_onb_enum b1 \<in> carrier_vec n"
          by (simp add: carrier_vecI dim1)        
        moreover have "vec_of_onb_enum b2 \<in> carrier_vec n"
          by (simp add: carrier_dim_vec dim2)        
        ultimately have "M *\<^sub>v vec_of_onb_enum (b1 + b2) = M *\<^sub>v vec_of_onb_enum b1
                                                        + M *\<^sub>v vec_of_onb_enum b2"
          using  M_carrier_mat Matrix.mult_add_distrib_mat_vec[where A = M 
              and v\<^sub>1 = "vec_of_onb_enum b1" and v\<^sub>2 = "vec_of_onb_enum b2"]
            \<open>vec_of_onb_enum (b1 + b2) = vec_of_onb_enum b1 + vec_of_onb_enum b2\<close> by auto
        moreover have "dim_vec (M *\<^sub>v vec_of_onb_enum b1) = m" 
          using dim1
          using True dim_mult_mat_vec by blast           
        moreover have "dim_vec (M *\<^sub>v vec_of_onb_enum b2) = m" 
          using dim2
          using True by auto
        ultimately show ?thesis
          by (simp add: f_def m_def onb_enum_of_vec_add)
      qed

      show "f M (r *\<^sub>C b) = r *\<^sub>C f M b"
        for r :: complex
          and b :: 'a
      proof-
        have dim1: "dim_vec (vec_of_onb_enum b) = n"
          by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list' n_def)
        have "vec_of_onb_enum (r *\<^sub>C b) = r \<cdot>\<^sub>v vec_of_onb_enum b"
          by (simp add: vec_of_onb_enum_scaleC)
        have "vec_of_onb_enum b \<in> carrier_vec n"
          by (simp add: carrier_vecI dim1)        
        hence "M *\<^sub>v vec_of_onb_enum (r *\<^sub>C b) = r \<cdot>\<^sub>v (M *\<^sub>v vec_of_onb_enum b)"
          using True \<open>vec_of_onb_enum (r *\<^sub>C b) = r \<cdot>\<^sub>v vec_of_onb_enum b\<close> by auto
        moreover have "dim_vec (M *\<^sub>v vec_of_onb_enum b) = m" 
          using dim1
          using True by auto           
        ultimately show ?thesis 
          unfolding f_def
          by (simp add: canonical_basis_length_eq m_def onb_enum_of_vec_mult)
      qed
    qed
  next
    case False
    thus ?thesis
      unfolding m_def n_def
      by (simp add: clinearI f_def) 
  qed

  show "\<exists>K. \<forall>x. norm (f M x) \<le> norm x * K"
  proof(cases "M\<in>carrier_mat m n")
    case True
    have f_def': "f M v = onb_enum_of_vec (M *\<^sub>v (vec_of_onb_enum v))" for v
      using True \<open>f \<equiv> \<lambda>M v. if M \<in> carrier_mat (canonical_basis_length TYPE('b)) 
        (canonical_basis_length TYPE('a)) then onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum v) else 0\<close> 
        m_def n_def by auto      
    have M_carrier_mat: 
      "M \<in> carrier_mat m n"
      by (simp add: True)
    have "clinear (f M)"
      by (simp add: \<open>clinear (f M)\<close>)
    hence "cbounded_linear (f M)"
      using clinear_cbounded_linear_onb_enum by blast
    thus ?thesis
      by (simp add: cbounded_linear.bounded) 
  next
    case False
    thus ?thesis
      unfolding f_def m_def n_def
      by (metis (full_types) order_refl mult_eq_0_iff norm_eq_zero)
  qed
qed

(* TODO: Could be defined on basis_enum (like the vec_of_onb_enum).
   Most of the rules don't need an ONB *)
definition mat_of_cblinfun :: \<open>'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum \<Rightarrow> complex mat\<close> where
  \<open>mat_of_cblinfun f = 
    mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a)) (
    \<lambda> (i, j). \<langle> (canonical_basis::'b list)!i, f *\<^sub>V ((canonical_basis::'a list)!j) \<rangle> )\<close>
  for f




lemma cinner_mat_of_cblinfun_basis:
  fixes F::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
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
qed

lemma cinner_mat_of_cblinfun:
  fixes F::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
  defines "BasisB == (canonical_basis::'b list)"
    and "nB == canonical_basis_length TYPE('b)"
  assumes "iB < nB"
  shows "vec_index (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum u) iB
        = \<langle> BasisB!iB, F *\<^sub>V u \<rangle>"
proof-
  define BasisA where "BasisA = (canonical_basis::'a list)"
  define basisA where "basisA = set BasisA"
  define nA where "nA == canonical_basis_length TYPE('a)"
  define P where "P x = vec_index (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum x) iB" for x::'a
  define Q where "Q x = \<langle> BasisB!iB, F *\<^sub>V x \<rangle>" for x::'a
  have carrier_mat1: "mat_of_cblinfun F \<in> carrier_mat nB nA"
    unfolding nB_def nA_def mat_of_cblinfun_def by simp
  have "clinear P"
    unfolding clinear_def proof
    show "P (b1 + b2) = P b1 + P b2"
      for b1 :: 'a
        and b2 :: 'a
    proof-
      have "vec_of_onb_enum (b1 + b2) = vec_of_onb_enum b1 + vec_of_onb_enum b2"
        by (simp add: vec_of_onb_enum_add)
      hence "mat_of_cblinfun F *\<^sub>v (vec_of_onb_enum (b1 + b2)) 
            = mat_of_cblinfun F *\<^sub>v (vec_of_onb_enum b1)
            + mat_of_cblinfun F *\<^sub>v (vec_of_onb_enum b2)"
        using carrier_mat1
          add.commute carrier_vec_dim_vec dim_vec_last index_add_vec(2) mult_add_distrib_mat_vec 
          nA_def vec_of_onb_enum_add vec_of_onb_enum_inverse
        by metis
      thus ?thesis
        unfolding P_def
        using assms(3) carrier_mat1 by auto      
    qed
    show "P (r *\<^sub>C b) = r *\<^sub>C P b"
      for r :: complex
        and b :: 'a
    proof-
      have carrier_vec1: "vec_of_onb_enum b \<in> carrier_vec nA"
        unfolding nA_def vec_of_onb_enum_def
        by (simp add: canonical_basis_length_eq carrier_dim_vec)
      have "vec_of_onb_enum (r *\<^sub>C b) = r \<cdot>\<^sub>v (vec_of_onb_enum b)"
        by (simp add: vec_of_onb_enum_scaleC)
      hence "mat_of_cblinfun F *\<^sub>v (vec_of_onb_enum (r *\<^sub>C b)) 
            = mat_of_cblinfun F *\<^sub>v (r \<cdot>\<^sub>v (vec_of_onb_enum b))"
        by simp
      also have "\<dots> = r \<cdot>\<^sub>v (mat_of_cblinfun F *\<^sub>v (vec_of_onb_enum b))"
        apply (rule Matrix.mult_mat_vec[where nr = nB and nc = nA and k = r and A = "mat_of_cblinfun F" and v = "vec_of_onb_enum b"])
         apply (simp add: carrier_mat1)
        by (simp add: carrier_vec1)
      finally have "mat_of_cblinfun F *\<^sub>v vec_of_onb_enum (r *\<^sub>C b) =
             r \<cdot>\<^sub>v (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum b)".
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
        by (simp add: cblinfun_apply_add)        
      thus ?thesis
        unfolding Q_def
        by (simp add: cinner_right_distrib)        
    qed
    show "Q (r *\<^sub>C b) = r *\<^sub>C Q b"
      for r :: complex
        and b :: 'a
    proof-
      have "F *\<^sub>V (r *\<^sub>C b) = r *\<^sub>C (F *\<^sub>V b)"
        by (simp add: cblinfun_apply_scaleC)        
      thus ?thesis
        unfolding Q_def
        by (simp add: cinner_right_distrib)        
    qed
  qed
  moreover have "P x = Q x" 
    if "x \<in> basisA"
    for x
  proof-
    have "\<exists>iA. BasisA!iA = x \<and> iA < nA"
      by (metis BasisA_def basisA_def canonical_basis_length_eq distinct_Ex1 
          distinct_canonical_basis nA_def that)     
    then obtain iA where a1: "BasisA!iA = x" and a2: "iA < nA"
      by blast
    have "vec_of_onb_enum (BasisA ! iA) = unit_vec nA iA"
      unfolding BasisA_def nA_def
      by (metis a2 index_unit_vec(3) nA_def onb_enum_of_vec_unit_vec vec_of_onb_enum_inverse)
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
    have "closure (Complex_Vector_Spaces.span basisA) = Complex_Vector_Spaces.span basisA"
      by (simp add: basisA_def span_finite_dim)      
    thus ?thesis
      using BasisA_def basisA_def is_generator_set
        by (metis BasisA_def basisA_def  is_generator_set)
  qed
  ultimately have "P = Q" 
    by (metis UNIV_I ext)    
  thus ?thesis unfolding P_def Q_def
    by meson 
qed


lemma mat_of_cblinfun_description:
  "vec_of_onb_enum (F *\<^sub>V u) = mat_of_cblinfun F *\<^sub>v vec_of_onb_enum u"
  for F::"'a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum" and u::'a
proof-

  define BasisA where "BasisA = (canonical_basis::'a list)"
  define BasisB where "BasisB = (canonical_basis::'b list)"
  define basisA where "basisA = set BasisA"
  define basisB where "basisB = set BasisB"
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"

  have onb_enum_of_vec_mat_of_cblinfun_cinner:
    "vec_index (mat_of_cblinfun F *\<^sub>v unit_vec nA iA) iB =
        \<langle> BasisB!iB, onb_enum_of_vec (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum (BasisA!iA)) \<rangle>"
    if "iB < nB" and "iA < nA"
    for F::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum" and iA iB
  proof-
  define v where "v = mat_of_cblinfun F *\<^sub>v unit_vec nA iA"
  have r1: "vec_of_onb_enum (BasisA!iA) = unit_vec nA iA"
    by (metis BasisA_def index_unit_vec(3) nA_def onb_enum_of_vec_unit_vec that(2) 
        vec_of_onb_enum_inverse)
  have "length BasisB = nB"
    by (simp add: BasisB_def canonical_basis_length_eq nB_def)    
  moreover have length_v: "length (list_of_vec v) = nB"
  proof-
    have "mat_of_cblinfun F \<in> carrier_mat nB nA"
      unfolding nB_def nA_def mat_of_cblinfun_def by auto
    hence "dim_vec v = nB"
      unfolding v_def
      by auto       
    thus ?thesis
      by simp 
  qed
  ultimately have "sum_list (map2 (*\<^sub>C) (list_of_vec v) BasisB)
      = (\<Sum>iB=0..<nB. (list_of_vec v)!iB *\<^sub>C BasisB!iB)"
    by (metis BasisB_def distinct_canonical_basis onb_enum_of_vec_expansion)
  hence "\<langle>BasisB!iB, sum_list (map2 (*\<^sub>C) (list_of_vec v) BasisB)\<rangle> 
      =  \<langle>BasisB!iB, (\<Sum>iB=0..<nB. (list_of_vec v)!iB *\<^sub>C BasisB!iB)\<rangle>"
    by simp
  also have "\<dots> = 
     (\<Sum>jB\<in>{0..<nB}. \<langle>BasisB!iB, (list_of_vec v)!jB *\<^sub>C BasisB!jB\<rangle>)"
    using Complex_Inner_Product.complex_inner_class.cinner_sum_right[where 
        x = "BasisB!iB" and f = "\<lambda>x. (list_of_vec v)!x *\<^sub>C BasisB!x" and A = "{0..<nB}"]
    by blast
  also have "\<dots> = 
     (\<Sum>jB\<in>{0..<nB}.  (list_of_vec v)!jB * \<langle>BasisB!iB, BasisB!jB\<rangle>)"
    by simp
  also have "\<dots> = 
      (list_of_vec v)!iB * \<langle>BasisB!iB, BasisB!iB\<rangle>
       + (\<Sum>jB\<in>{0..<nB}-{iB}.  (list_of_vec v)!jB * \<langle>BasisB!iB, BasisB!jB\<rangle>)"
  proof-
    have "iB \<in> {0..<nB}"
      using that(1) by auto      
    thus ?thesis
      by (simp add: sum.remove)      
  qed
  also have "\<dots> = 
      (list_of_vec v)!iB * \<langle>BasisB!iB, BasisB!iB\<rangle>"
  proof-
    have "jB\<in>{0..<nB}-{iB} \<Longrightarrow> (list_of_vec v)!jB * \<langle>BasisB!iB, BasisB!jB\<rangle> = 0"
      for jB
    proof-
      assume a1: "jB\<in>{0..<nB}-{iB}"
      hence a2: "jB < nB"
        by simp
      have "iB \<noteq> jB"
        using a1
        by simp
      moreover have "distinct BasisB"
        unfolding BasisB_def
        by simp
      ultimately have "BasisB!iB \<noteq> BasisB!jB"
        using \<open>jB \<in> {0..<nB} - {iB}\<close> \<open>length BasisB = nB\<close> nth_eq_iff_index_eq
         a2 that(1) by blast         
      moreover have "BasisB!iB \<in> set BasisB"
        using \<open>length BasisB = nB\<close>
        by (simp add: that(1)) 
      moreover have "BasisB!jB \<in> set BasisB"
        by (simp add: \<open>length BasisB = nB\<close> a2)        
      moreover have "x\<in>set BasisB \<Longrightarrow> y\<in>set BasisB \<Longrightarrow>
            x \<noteq> y \<Longrightarrow> \<langle>x, y\<rangle> = 0"
        for x y::'b
        using BasisB_def is_ortho_set_def is_orthonormal by fastforce
      ultimately have "\<langle>BasisB!iB, BasisB!jB\<rangle> = 0"
        by blast
      thus ?thesis by simp
    qed
    hence "(\<Sum>jB\<in>{0..<nB}-{iB}.  (list_of_vec v)!jB * \<langle>BasisB!iB, BasisB!jB\<rangle>) = 0"
      by (simp add: \<open>\<And>jB. jB \<in> {0..<nB} - {iB} \<Longrightarrow> list_of_vec v ! jB * \<langle>BasisB ! iB, BasisB ! jB\<rangle> = 0\<close>)      
    thus ?thesis by simp
  qed
  also have "\<dots> = 
      (list_of_vec v)!iB"
  proof-
    have "BasisB!iB \<in> set BasisB"
      using \<open>length BasisB = nB\<close>
      by (simp add: that(1)) 
    have "norm (BasisB!iB) = 1"
      using BasisB_def \<open>BasisB ! iB \<in> set BasisB\<close> is_normal by blast      
    hence "(norm (BasisB!iB))^2 = 1"
      by simp
    hence "\<langle>BasisB!iB, BasisB!iB\<rangle> = 1"
      by (metis of_real_hom.hom_one power2_norm_eq_cinner')
    thus ?thesis by simp
  qed
  also have "\<dots> = vec_index v iB"
    by (simp add: list_of_vec_index)
  finally have "\<langle>BasisB!iB, sum_list (map2 (*\<^sub>C) (list_of_vec v) BasisB)\<rangle> 
        = vec_index v iB".
  hence "vec_index v iB = \<langle> BasisB!iB, onb_enum_of_vec v\<rangle>"
    unfolding onb_enum_of_vec_def onb_enum_of_vec_list_def'
    using BasisB_def length_v nB_def by auto
  thus ?thesis unfolding v_def using r1
    by simp 
qed

  define M where "M = mat_of_cblinfun F"
  have carrier_M: "M \<in> carrier_mat nB nA"
    unfolding nB_def nA_def M_def mat_of_cblinfun_def
    by auto
  have "vec_index (mat_of_cblinfun F *\<^sub>v unit_vec nA iA) iB =
        \<langle>BasisB!iB, F *\<^sub>V BasisA!iA\<rangle>"
    if "iA < nA" and "iB < nB"
    for iA iB
    using nA_def nB_def that(1) that(2) 
      cinner_mat_of_cblinfun_basis[where iA = iA and iB = iB and F = F]
    unfolding nA_def nB_def BasisA_def BasisB_def
    by blast 
  moreover have "vec_index (mat_of_cblinfun F *\<^sub>v unit_vec nA iA) iB = 
          \<langle> BasisB!iB, onb_enum_of_vec (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum (BasisA!iA)) \<rangle>"
    if "iA < nA" and "iB < nB"
    for iA iB
    using onb_enum_of_vec_mat_of_cblinfun_cinner
      BasisA_def BasisB_def nA_def nB_def that(1) that(2) by blast    
  ultimately have r1: "\<langle> BasisB!iB, onb_enum_of_vec (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum (BasisA!iA)) \<rangle>
         = \<langle>BasisB!iB, F *\<^sub>V BasisA!iA\<rangle>"
    if "iA < nA" and "iB < nB"
    for iA iB
    by (simp add: that(1) that(2))
  hence "\<langle> v, onb_enum_of_vec (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum u) \<rangle> = \<langle> v, F *\<^sub>V u \<rangle>"
    if "u \<in> basisA" and "v \<in> basisB"
    for u v
  proof-
    have "length BasisA = nA"
      by (simp add: BasisA_def canonical_basis_length_eq nA_def)
    moreover have "length BasisB = nB"
      by (simp add: BasisB_def canonical_basis_length_eq nB_def)
    moreover have "distinct BasisA"
      by (simp add: BasisA_def)
    moreover have "distinct BasisB"
      by (simp add: BasisB_def)
    ultimately show ?thesis 
      using that
      unfolding basisA_def basisB_def
      by (metis r1 distinct_Ex1)     
  qed
  hence "onb_enum_of_vec (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum u) = F *\<^sub>V u"
    using cinner_unique_onb_enum
    by (metis BasisA_def BasisB_def M_def basisA_def basisB_def carrier_M cblinfun_of_mat.rep_eq
        nA_def nB_def)    
  hence "vec_of_onb_enum ((onb_enum_of_vec (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum u))::'b) 
       = vec_of_onb_enum (F *\<^sub>V u)"
    by simp    
  moreover have "dim_vec (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum u) = nB"
    using M_def carrier_M dim_mult_mat_vec by blast    
  ultimately show ?thesis
    using vec_of_onb_enum_inverse nB_def by auto 
qed


lemma mat_of_cblinfun_inverse:
  "cblinfun_of_mat (mat_of_cblinfun B) = B"
  for B::"'a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
proof -
  define BasisA where "BasisA = (canonical_basis::'a list)"
  define BasisB where "BasisB = (canonical_basis::'b list)"
  define basisA where "basisA = set BasisA"
  define basisB where "basisB = set BasisB"
  define n where "n = canonical_basis_length TYPE('a)"
  define m where "m = canonical_basis_length TYPE('b)"
  define M where "M = mat_of_cblinfun B"
  have carrier_M: "M \<in> carrier_mat m n"
    unfolding M_def mat_of_cblinfun_def m_def n_def by simp
  have "\<langle>v, (cblinfun_of_mat M) *\<^sub>V u\<rangle> = \<langle>v, B *\<^sub>V u\<rangle>"
    if "u \<in> basisA" and "v \<in> basisB" for u::'a and v::'b
  proof-
    have "vec_of_onb_enum (B *\<^sub>V u) = mat_of_cblinfun B *\<^sub>v vec_of_onb_enum u"
      using mat_of_cblinfun_description by blast
    hence "(onb_enum_of_vec (mat_of_cblinfun B *\<^sub>v vec_of_onb_enum u)::'b) = B *\<^sub>V u"
      by (metis onb_enum_of_vec_inverse)      
    hence "\<langle>v, onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum u)\<rangle> = \<langle>v, B *\<^sub>V u\<rangle>"
      unfolding M_def by auto
    thus ?thesis
      using carrier_M
      unfolding cblinfun_of_mat_def id_def m_def n_def
      by (metis (mono_tags, lifting) cblinfun_of_mat.abs_eq cblinfun_of_mat.rep_eq map_fun_apply)      
  qed
  hence "(cblinfun_of_mat M) *\<^sub>V u = B *\<^sub>V u"
    if "u \<in> basisA" for u
    using BasisA_def BasisB_def basisA_def basisB_def cinner_unique_onb_enum by auto
  hence "cblinfun_apply (cblinfun_of_mat M) = cblinfun_apply B"
    using obn_enum_uniq BasisA_def basisA_def by blast    
  thus ?thesis
    using cblinfun_apply_inject unfolding M_def by blast
qed

lemma mat_of_cblinfun_inj: "inj mat_of_cblinfun"
  by (metis inj_on_def mat_of_cblinfun_inverse)


lemma cblinfun_of_mat_plus:
  assumes a1: "M \<in> carrier_mat nB nA" and a2: "N \<in> carrier_mat nB nA"
    and a3: "nA = canonical_basis_length TYPE('a)" 
    and a4: "nB = canonical_basis_length TYPE('b)"
  shows "(cblinfun_of_mat (M + N) :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) 
  = ((cblinfun_of_mat M + cblinfun_of_mat N):: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)"
proof-
  have "(cblinfun_of_mat (M + N) :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) v
  = ((cblinfun_of_mat M + cblinfun_of_mat N):: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) v"
    for v
  proof-
    have w1: "dim_vec (M *\<^sub>v vec_of_onb_enum v) = dim_vec (N *\<^sub>v vec_of_onb_enum v)"
      using a1 a2 by auto      
    have "vec_of_onb_enum v \<in> carrier_vec nA"
      by (metis a3 carrier_vec_dim_vec diff_add_cancel dim_vec index_add_vec(2) 
          vec_of_onb_enum_add vec_of_onb_enum_inverse)      
    hence w2: "M *\<^sub>v vec_of_onb_enum v + N *\<^sub>v vec_of_onb_enum v = (M + N) *\<^sub>v vec_of_onb_enum v"
      using a1 a2 Matrix.add_mult_distrib_mat_vec
      by metis
    have "((cblinfun_of_mat M)::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) v = 
        onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum v)"
      by (metis a1 a3 a4 cblinfun_of_mat.rep_eq)      
    moreover have "((cblinfun_of_mat N)::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) v = 
        onb_enum_of_vec (N *\<^sub>v vec_of_onb_enum v)"
      by (metis a2 a3 a4 cblinfun_of_mat.rep_eq)
    ultimately have "((cblinfun_of_mat M)::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) v 
                   + ((cblinfun_of_mat N)::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) v
        = onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum v)
        + onb_enum_of_vec (N *\<^sub>v vec_of_onb_enum v)"
      by simp
    also have "\<dots>
        = onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum v + N *\<^sub>v vec_of_onb_enum v)"
      using onb_enum_of_vec_add w1
      by (metis a2 a4 canonical_basis_length_eq carrier_matD(1) dim_mult_mat_vec) 
    also have "\<dots>
        = onb_enum_of_vec ((M + N) *\<^sub>v vec_of_onb_enum v)"
      by (simp add: w2)
    also have "\<dots>
        = (cblinfun_of_mat (M + N) :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) v"
      by (metis a2 a3 a4 add_carrier_mat cblinfun_of_mat.rep_eq)
    finally have "((cblinfun_of_mat M)::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) v 
                   + ((cblinfun_of_mat N)::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) v 
        = (cblinfun_of_mat (M + N) :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) v"
      .    
    thus ?thesis
      by (simp add: plus_cblinfun.rep_eq) 
  qed
  thus ?thesis
    by (simp add: cblinfun_ext) 
qed

lemma vec_of_onb_enum_zero:
  assumes a1: "nA = canonical_basis_length TYPE('a::onb_enum)" 
  shows "vec_of_onb_enum (0::'a) = 0\<^sub>v nA"
  by (smt add_cancel_right_left assms index_zero_vec(2) left_zero_vec onb_enum_of_vec_inverse
      vec_of_onb_enum_add vec_of_onb_enum_inverse zero_carrier_vec)  

lemma cblinfun_of_mat_zero_converse:
  fixes M::"complex mat"
  assumes a1: "M \<in> carrier_mat nB nA"
    and a2: "nA = canonical_basis_length TYPE('a)" 
    and a3: "nB = canonical_basis_length TYPE('b)"  
    and a4: "(cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) = 0"
  shows "M = 0\<^sub>m nB nA"
proof-
  have "M $$ (iB,iA) = 0"
    if "iB < nB" and "iA < nA" 
    for iB iA
  proof-
    have "(cblinfun_of_mat M :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) *\<^sub>V v = 0"
      for v
      by (simp add: a4)
    moreover have "((cblinfun_of_mat M) :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) *\<^sub>V v = 
          onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum v)"
      for v
      by (metis a1 a2 a3 cblinfun_of_mat.rep_eq)
    ultimately have c1: "onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum v) = (0::'b)"
      for v::'a
      by simp
    have "M *\<^sub>v vec_of_onb_enum v = 0\<^sub>v nB"
      for v::'a
    proof-
      have "vec_of_onb_enum (onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum v)::'b) = vec_of_onb_enum (0::'b)"
        by (simp add: c1)
      hence "M *\<^sub>v vec_of_onb_enum v = vec_of_onb_enum (0::'b)"
        using vec_of_onb_enum_inverse a1 a3 by auto
      also have "vec_of_onb_enum (0::'b) = 0\<^sub>v nB"
        using vec_of_onb_enum_zero
        by (simp add: vec_of_onb_enum_zero a3) 
      finally show ?thesis 
        .
    qed
    moreover have "M $$ (iB,iA) = vec_index (M *\<^sub>v unit_vec nA iA) iB"
      using a1 that(1) that(2) by auto
    ultimately show ?thesis
      by (metis a2 index_unit_vec(3) index_zero_vec(1) that(1) vec_of_onb_enum_inverse)      
  qed
  thus ?thesis 
    using Matrix.eq_matI a1 by auto
qed

lemma cblinfun_of_mat_plusOp':
  "mat_of_cblinfun (F + G) = mat_of_cblinfun F + mat_of_cblinfun G"
  for F G::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum"
proof-
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"
  define BasisA where "BasisA = (canonical_basis::'a list)"
  define BasisB where "BasisB = (canonical_basis::'b list)"

  have a1: "mat_of_cblinfun F \<in> carrier_mat nB nA"
    unfolding mat_of_cblinfun_def nA_def nB_def
    by simp
  moreover have a2: "mat_of_cblinfun G \<in> carrier_mat nB nA"
    unfolding mat_of_cblinfun_def nA_def nB_def
    by simp
  ultimately have "mat_of_cblinfun F + mat_of_cblinfun G \<in> carrier_mat nB nA"
    using  Matrix.add_carrier_mat by blast
  moreover have "mat_of_cblinfun (F + G) \<in> carrier_mat nB nA"
    unfolding mat_of_cblinfun_def nA_def nB_def
    by simp
  moreover have "(mat_of_cblinfun (F + G)) $$ (iB,iA)
           = (mat_of_cblinfun F + mat_of_cblinfun G) $$ (iB,iA)"
    if "iB < nB" and "iA < nA"
    for iB iA
  proof-
    have "(mat_of_cblinfun F) $$ (iB,iA) = 
          \<langle>BasisB ! iB, F *\<^sub>V BasisA ! iA\<rangle>"
      unfolding mat_of_cblinfun_def BasisA_def BasisB_def
      using nA_def nB_def that(1) that(2) by auto
    moreover have "(mat_of_cblinfun G) $$ (iB,iA) = 
          \<langle>BasisB ! iB, G *\<^sub>V BasisA ! iA\<rangle>"
      unfolding mat_of_cblinfun_def BasisA_def BasisB_def
      using nA_def nB_def that(1) that(2) by auto
    ultimately have "(mat_of_cblinfun F) $$ (iB,iA) + (mat_of_cblinfun G) $$ (iB,iA)
      = \<langle>BasisB ! iB, F *\<^sub>V BasisA ! iA\<rangle> + \<langle>BasisB ! iB, G *\<^sub>V BasisA ! iA\<rangle>"
      by simp
    also have "\<dots> = \<langle>BasisB ! iB, F *\<^sub>V BasisA!iA +  G *\<^sub>V BasisA!iA\<rangle>"
      by (simp add: cinner_right_distrib)
    also have "\<dots> = \<langle>BasisB ! iB, (F + G) *\<^sub>V BasisA!iA\<rangle>"
      by (simp add: plus_cblinfun.rep_eq)
    also have "\<dots> = (mat_of_cblinfun (F + G)) $$ (iB,iA)"
      unfolding mat_of_cblinfun_def BasisA_def BasisB_def
      using nA_def nB_def that(1) that(2) by auto
    finally have "(mat_of_cblinfun F) $$ (iB,iA) + (mat_of_cblinfun G) $$ (iB,iA)
                = (mat_of_cblinfun (F + G)) $$ (iB,iA)"
      by blast
    moreover have "(mat_of_cblinfun F + mat_of_cblinfun G) $$ (iB,iA)
        = (mat_of_cblinfun F) $$ (iB,iA) + (mat_of_cblinfun G) $$ (iB,iA)"
      using a2 that(1) that(2) by auto
    ultimately show ?thesis
      by simp
  qed
  ultimately show ?thesis 
    using Matrix.eq_matI
    by blast
qed


lemma cblinfun_of_mat_id':
  "mat_of_cblinfun (idOp :: ('a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L'a)) = 1\<^sub>m (canonical_basis_length TYPE('a))"
proof-
  define n where "n = canonical_basis_length TYPE('a)"
  define Basis where "Basis = (canonical_basis::'a list)"
  define I where "I = (idOp ::'a \<Rightarrow>\<^sub>C\<^sub>L 'a)"
  have b1: "dim_row (mat_of_cblinfun I) = n"
    unfolding mat_of_cblinfun_def n_def
    by simp
  have b2: "dim_col (mat_of_cblinfun I) = n"
    unfolding mat_of_cblinfun_def n_def
    by simp
  have b3: "dim_row (1\<^sub>m n) = n"
    by simp    
  have b4: "dim_col (1\<^sub>m n) = n"
    by simp
  have "(mat_of_cblinfun I)$$(i, j) = (one_mat n)$$(i, j)"
    if "i < n" and "j < n"
    for i j
  proof-
    have "(mat_of_cblinfun I)$$(i, j) = \<langle>Basis!i, Basis!j\<rangle>"
      using that 
      unfolding Basis_def mat_of_cblinfun_def one_mat_def I_def n_def
      apply transfer
      unfolding id_def apply auto
      by (simp add: mk_mat_def)
    also have "\<dots> = (if i = j then 1 else 0)"
    proof(cases "i = j")
      case True
      have "Basis!i \<in> set Basis"
        using that(1) unfolding n_def Basis_def
        by (simp add: canonical_basis_length_eq)
      hence "norm (Basis!i) = 1"
        by (simp add: Basis_def is_normal)
      hence "(norm (Basis!i))^2 = 1"
        by simp
      thus ?thesis
        by (metis True of_real_hom.hom_one power2_norm_eq_cinner') 
    next
      case False
      have c1: "distinct Basis"
        unfolding Basis_def
        by simp
      have "x\<in>set Basis \<Longrightarrow> y\<in>set Basis \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<langle>x, y\<rangle> = 0"
        for x y
        using Basis_def is_ortho_set_def is_orthonormal by fastforce
      moreover have "Basis!i \<in> set Basis"
        using that(1) unfolding n_def Basis_def
        by (simp add: canonical_basis_length_eq) 
      moreover have "Basis!j \<in> set Basis"
        using that(2) unfolding n_def Basis_def
        by (simp add: canonical_basis_length_eq) 
      moreover have  "Basis!i \<noteq> Basis!j"
        using c1 that  unfolding n_def Basis_def
        by (simp add: False canonical_basis_length_eq distinct_conv_nth) 
      ultimately show ?thesis
        by auto        
    qed
    also have "\<dots> = (one_mat n)$$(i, j)"
      unfolding one_mat_def
      by (simp add: that(1) that(2))
    finally show ?thesis .
  qed    
  thus ?thesis 
    unfolding n_def I_def
    apply (rule Matrix.eq_matI)
       apply simp
      apply simp
    using I_def b1 n_def apply auto[1]
    using I_def b2 n_def by auto
qed


lemma mat_of_cblinfun_zero':
  "mat_of_cblinfun (0 :: ('a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)) 
  = 0\<^sub>m (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))"
proof-
  define Z where "Z = (0 :: ('a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum))"
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"

  have z1: "Z + Z = Z"
    unfolding Z_def by simp
  have z2: "mat_of_cblinfun Z \<in> carrier_mat nB nA"
    unfolding nB_def nA_def mat_of_cblinfun_def by auto
  hence "mat_of_cblinfun (Z + Z) = mat_of_cblinfun Z + mat_of_cblinfun Z"
    by (simp add: cblinfun_of_mat_plusOp')
  hence "mat_of_cblinfun Z = mat_of_cblinfun Z + mat_of_cblinfun Z"
    using z1 by simp
  hence "mat_of_cblinfun Z = 0\<^sub>m nB nA"
    unfolding nB_def nA_def
    by (smt add_uminus_minus_mat assoc_add_mat minus_r_inv_mat nA_def nB_def right_add_zero_mat 
        uminus_carrier_mat z2)  
  thus ?thesis unfolding Z_def nB_def nA_def by simp
qed


lemma cblinfun_of_mat_uminusOp':
  "mat_of_cblinfun (- M) = - mat_of_cblinfun M" 
  for M::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum"
proof-
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"
  have M1: "mat_of_cblinfun M \<in> carrier_mat nB nA"
    unfolding nB_def nA_def
    by (metis add.right_neutral add_carrier_mat cblinfun_of_mat_plusOp' mat_of_cblinfun_zero' nA_def
        nB_def zero_carrier_mat) 
  have M2: "mat_of_cblinfun (-M) \<in> carrier_mat nB nA"
    by (metis add_carrier_mat cblinfun_of_mat_plusOp' mat_of_cblinfun_zero' diff_0 nA_def nB_def 
        uminus_add_conv_diff zero_carrier_mat)
  have "mat_of_cblinfun (M - M) =  0\<^sub>m nB nA"
    unfolding nA_def nB_def
    by (simp add: mat_of_cblinfun_zero')
  moreover have "mat_of_cblinfun (M - M) = mat_of_cblinfun M + mat_of_cblinfun (- M)"
    by (metis cblinfun_of_mat_plusOp' pth_2)
  ultimately have "mat_of_cblinfun M + mat_of_cblinfun (- M) = 0\<^sub>m nB nA"
    by simp
  thus ?thesis
    using M1 M2
    by (smt add_uminus_minus_mat assoc_add_mat comm_add_mat left_add_zero_mat minus_r_inv_mat 
        uminus_carrier_mat) 
qed


lemma cblinfun_of_mat_minusOp':
  "mat_of_cblinfun (M - N) = mat_of_cblinfun M - mat_of_cblinfun N" 
  for M::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum" and N::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b"
proof-
  have a1: "mat_of_cblinfun (- N) = -(mat_of_cblinfun N)"
    using cblinfun_of_mat_uminusOp' .
  have "mat_of_cblinfun (M - N) = mat_of_cblinfun (M + (- N))"
    by simp
  also have "\<dots> = mat_of_cblinfun M + mat_of_cblinfun (- N)"
    using cblinfun_of_mat_plusOp'. 
  also have "\<dots> = mat_of_cblinfun M - mat_of_cblinfun N"
    using a1 by auto
  finally show ?thesis .
qed  

lemma cblinfun_of_mat_uminus:
  assumes a1: "M \<in> carrier_mat nB nA"
    and a2: "nA = canonical_basis_length TYPE('a)" 
    and a3: "nB = canonical_basis_length TYPE('b)"
  shows
    "(cblinfun_of_mat (-M) :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) 
  = -((cblinfun_of_mat M):: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)"
  by (smt a1 a2 a3 add.group_axioms add.right_neutral add_minus_cancel add_uminus_minus_mat 
      cblinfun_of_mat_plus group.inverse_inverse mat_of_cblinfun_inverse mat_of_cblinfun_zero' 
      minus_r_inv_mat uminus_carrier_mat)

lemma cblinfun_of_mat_minus:
  fixes M::"complex mat"
  assumes a1: "M \<in> carrier_mat nB nA" and a2: "N \<in> carrier_mat nB nA"
    and a3: "nA = canonical_basis_length TYPE('a)" 
    and a4: "nB = canonical_basis_length TYPE('b)"
  shows   "(cblinfun_of_mat (M - N) :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) 
  = ((cblinfun_of_mat M - cblinfun_of_mat N):: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)"
proof-
  have b1: "-N \<in> carrier_mat nB nA"
    by (simp add: a2)
  hence b2: "((cblinfun_of_mat (-N)):: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)
       = -((cblinfun_of_mat N):: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)"
    by (simp add: a3 a4 cblinfun_of_mat_uminus)
  have "(cblinfun_of_mat (M - N) :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)
     = (cblinfun_of_mat (M + (- N)) :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) "
    by (metis a1 a2 minus_add_uminus_mat)
  also have "\<dots>
     = ((cblinfun_of_mat M + cblinfun_of_mat (-N)):: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)"
    using a1 a3 a4 b1 cblinfun_of_mat_plus by blast
  also have "\<dots>
     = ((cblinfun_of_mat M - cblinfun_of_mat N):: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)"
    using b2
    by simp
  finally show ?thesis .
qed



lemma cblinfun_of_mat_inverse:
  fixes M::"complex mat"
  assumes "M \<in> carrier_mat nB nA"
    and "nA = canonical_basis_length TYPE('a)" (* TODO: use 'defines' *)
    and "nB = canonical_basis_length TYPE('b)" (* TODO: use 'defines' *)
  shows "mat_of_cblinfun (cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum) = M"
proof-
  define F where "F = (cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)"
  have g1: "M \<in> carrier_mat nB nA"
    by (simp add: assms(1))
  have g2: "(mat_of_cblinfun (cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum))
                   \<in> carrier_mat nB nA"
    by (metis add_diff_cancel_right' assms(2) assms(3) cblinfun_of_mat_minusOp' mat_of_cblinfun_zero'
        minus_carrier_mat zero_carrier_mat)
  have  "cblinfun_of_mat (mat_of_cblinfun F) = F"
    by (simp add: mat_of_cblinfun_inverse)
  hence "cblinfun_of_mat (mat_of_cblinfun (cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)) 
      = (cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)"
    unfolding F_def .
  hence "0 = 
        cblinfun_of_mat (mat_of_cblinfun (cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)) 
      - (cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)"
    by simp
  also have "\<dots> = 
        (cblinfun_of_mat
        ( (mat_of_cblinfun (cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)) 
          - M ):: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)"
    using g1 g2
    by (simp add: assms(2) assms(3) cblinfun_of_mat_minus) 
  finally have "0 = (cblinfun_of_mat
        ( (mat_of_cblinfun (cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)) 
          - M ):: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)".
  hence "(mat_of_cblinfun (cblinfun_of_mat M :: 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)) 
          - M = 0\<^sub>m nB nA"
    by (metis assms(1) assms(2) assms(3) cblinfun_of_mat_zero_converse minus_carrier_mat)
  thus ?thesis
    by (smt add.inverse_neutral assms(1) assms(2) assms(3) cblinfun_of_mat_minusOp' 
        cblinfun_of_mat_uminusOp' diff_zero mat_of_cblinfun_zero' minus_add_minus_mat
        minus_add_uminus_mat minus_carrier_mat minus_r_inv_mat right_add_zero_mat 
        uminus_carrier_mat zero_carrier_mat) 
qed

lemma mat_of_cblinfun_timesOp:
  fixes M N ::"complex mat"
  defines "nA == canonical_basis_length TYPE('a::onb_enum)" 
    and "nB == canonical_basis_length TYPE('b::onb_enum)"
    and "nC == canonical_basis_length TYPE('c::onb_enum)"
  assumes a1: "M \<in> carrier_mat nC nB" and a2: "N \<in> carrier_mat nB nA"
  shows  "cblinfun_of_mat (M * N)
       = ((cblinfun_of_mat M)::'b \<Rightarrow>\<^sub>C\<^sub>L'c) o\<^sub>C\<^sub>L ((cblinfun_of_mat N)::'a \<Rightarrow>\<^sub>C\<^sub>L'b)"
proof -
  have b1: "((cblinfun_of_mat M)::'b \<Rightarrow>\<^sub>C\<^sub>L'c) v = onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum v)"
    for v
    by (metis assms(4) cblinfun_of_mat.rep_eq nB_def nC_def)
  have b2: "((cblinfun_of_mat N)::'a \<Rightarrow>\<^sub>C\<^sub>L'b) v = onb_enum_of_vec (N *\<^sub>v vec_of_onb_enum v)"
    for v
    by (metis assms(5) cblinfun_of_mat.rep_eq nA_def nB_def)
  have b3: "((cblinfun_of_mat (M * N))::'a \<Rightarrow>\<^sub>C\<^sub>L'c) v
       = onb_enum_of_vec ((M * N) *\<^sub>v vec_of_onb_enum v)"
    for v
    by (metis assms(4) assms(5) cblinfun_of_mat.rep_eq mult_carrier_mat nA_def nC_def)
  have "(onb_enum_of_vec ((M * N) *\<^sub>v vec_of_onb_enum v)::'c)
      = (onb_enum_of_vec (M *\<^sub>v ( vec_of_onb_enum ( (onb_enum_of_vec (N *\<^sub>v vec_of_onb_enum v))::'b ))))"
    for v::'a
  proof-
    have c1: "vec_of_onb_enum (onb_enum_of_vec x :: 'b) = x"
      if "dim_vec x = nB"
      for x::"complex vec"
      using that unfolding nB_def
      by simp
    have c2: "vec_of_onb_enum v \<in> carrier_vec nA"
      by (metis (mono_tags, hide_lams) add.commute carrier_vec_dim_vec index_add_vec(2) 
          index_zero_vec(2) nA_def vec_of_onb_enum_add vec_of_onb_enum_inverse)      
    have "(M * N) *\<^sub>v vec_of_onb_enum v = M *\<^sub>v (N *\<^sub>v vec_of_onb_enum v)"
      using Matrix.assoc_mult_mat_vec a1 a2 c2 by blast      
    hence "(onb_enum_of_vec ((M * N) *\<^sub>v vec_of_onb_enum v)::'c)
        = (onb_enum_of_vec (M *\<^sub>v (N *\<^sub>v vec_of_onb_enum v))::'c)"
      by simp
    also have "\<dots> = 
      (onb_enum_of_vec (M *\<^sub>v ( vec_of_onb_enum ( (onb_enum_of_vec (N *\<^sub>v vec_of_onb_enum v))::'b ))))"
      using c1 a2 by auto 
    finally show ?thesis by simp
  qed
  thus ?thesis using b1 b2 b3
    by (simp add: cblinfun_ext times_applyOp)    
qed


(* lemma cinner_vec_of_onb_enum:
  "\<langle>x, y\<rangle> = (vec_of_onb_enum y) \<bullet>c (vec_of_onb_enum x)"

proof-
  define u where "u = vec_of_onb_enum x"
  define v where "v = vec_of_onb_enum y"
  define n where "n = canonical_basis_length TYPE('a)"
  have b1: "dim_vec u = n"
    unfolding u_def n_def
    by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list') 
  have b2: "dim_vec v = n"
    unfolding v_def n_def
    by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list') 
  have  "\<langle>(onb_enum_of_vec::_\<Rightarrow> 'a) u, (onb_enum_of_vec::_\<Rightarrow> 'a) v\<rangle>
           = v \<bullet>c u"
    using b1 b2 cinner_onb_enum_of_vec
    by (simp add: cinner_onb_enum_of_vec n_def)
  moreover have "x = onb_enum_of_vec u"
    by (simp add: onb_enum_of_vec_inverse u_def)
  moreover have "y = onb_enum_of_vec v"
    by (simp add: onb_enum_of_vec_inverse v_def)
  ultimately show ?thesis
    using u_def v_def by presburger 
qed *)


lemma cblinfun_of_mat_inj: "inj_on (cblinfun_of_mat::complex mat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) 
      (carrier_mat (canonical_basis_length TYPE('b::onb_enum))
                   (canonical_basis_length TYPE('a::onb_enum)))"
  using cblinfun_of_mat_inverse
  by (metis inj_onI)

lemma cblinfun_of_mat_apply_cblinfun:
  fixes M :: "complex mat"
  defines "nA == canonical_basis_length TYPE('a::onb_enum)"
    and "nB == canonical_basis_length TYPE('b::onb_enum)"
  assumes a1: "M \<in> carrier_mat nB nA" and a2: "dim_vec x = nA"
  shows "((onb_enum_of_vec (M *\<^sub>v x))::'b) 
       = ((cblinfun_of_mat M)::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) *\<^sub>V ((onb_enum_of_vec x)::'a)"
proof-
  define F::"'a \<Rightarrow>\<^sub>C\<^sub>L 'b" where "F = cblinfun_of_mat M"
  have b1: "M = mat_of_cblinfun F"
    unfolding F_def
    using assms(3) cblinfun_of_mat_inverse nA_def nB_def by fastforce
  define u::'a where "u = onb_enum_of_vec x"
  have b2: "x = vec_of_onb_enum u"
    unfolding u_def 
    using vec_of_onb_enum_inverse
    by (simp add: a2 nA_def)
  have "vec_of_onb_enum (F *\<^sub>V u) = mat_of_cblinfun F *\<^sub>v vec_of_onb_enum u"
    by (simp add: mat_of_cblinfun_description)
  hence "vec_of_onb_enum (F *\<^sub>V u) = M *\<^sub>v x"
    by (simp add: b1 b2)
  hence "F *\<^sub>V u = onb_enum_of_vec (M *\<^sub>v x)"
    by (metis onb_enum_of_vec_inverse)
  hence "((cblinfun_of_mat M)::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) *\<^sub>V ((onb_enum_of_vec x)::'a)
         = ((onb_enum_of_vec (M *\<^sub>v x))::'b)"
    by (simp add: F_def u_def)
  thus ?thesis by simp
qed



lemma mat_of_cblinfun_adjoint:
  defines "nA == canonical_basis_length TYPE('a::onb_enum)" 
    and "nB == canonical_basis_length TYPE('b::onb_enum)" 
  fixes M:: "complex mat"
  assumes "M \<in> carrier_mat nB nA"
  shows "((cblinfun_of_mat (adjoint_mat M)) :: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)
       = ((cblinfun_of_mat M) :: 'a \<Rightarrow>\<^sub>C\<^sub>L'b)*"
proof (rule adjoint_D)
  show "\<langle>cblinfun_of_mat (adjoint_mat M) *\<^sub>V x, y\<rangle> =
           \<langle>x, cblinfun_of_mat M *\<^sub>V y\<rangle>"
    for x::'b and y::'a
  proof-
    define u where "u = vec_of_onb_enum x"
    define v where "v = vec_of_onb_enum y"
    have c1: "vec_of_onb_enum ((cblinfun_of_mat (adjoint_mat M) *\<^sub>V x)::'a)
          = (adjoint_mat M) *\<^sub>v u"
      unfolding u_def
      by (metis adjoint_mat_def assms(3) cblinfun_of_mat_inverse map_carrier_mat 
          mat_of_cblinfun_description nA_def nB_def transpose_carrier_mat)
    have c2: "(vec_of_onb_enum ((cblinfun_of_mat M *\<^sub>V y)::'b))
        = M *\<^sub>v v"
      by (metis assms(3) cblinfun_of_mat_inverse mat_of_cblinfun_description nA_def nB_def v_def)
    have c3: "dim_vec v = nA"
      unfolding v_def nA_def vec_of_onb_enum_def
      by (simp add: canonical_basis_length_eq)
    have c4: "dim_vec u = nB"
      unfolding u_def nB_def vec_of_onb_enum_def
      by (simp add: canonical_basis_length_eq)
    have "v \<bullet>c ((adjoint_mat M) *\<^sub>v u) = (M *\<^sub>v v) \<bullet>c u"
      using c3 c4 cscalar_prod_adjoint assms(3) by blast      
    hence "v \<bullet>c (vec_of_onb_enum ((cblinfun_of_mat (adjoint_mat M) *\<^sub>V x)::'a))
        = (vec_of_onb_enum ((cblinfun_of_mat M *\<^sub>V y)::'b)) \<bullet>c u"
      using c1 c2 by simp
    thus "\<langle>cblinfun_of_mat (adjoint_mat M) *\<^sub>V x, y\<rangle> =
          \<langle>x, cblinfun_of_mat M *\<^sub>V y\<rangle>"
      unfolding u_def v_def
      by (simp add: cinner_ell2_code)      
  qed
qed


lemma cinner_square_canonical_basis: 
  defines "BasisA == (canonical_basis:: ('a::onb_enum list))"
    and "n == canonical_basis_length TYPE('a)"
  assumes a1: "i < n"
  shows "\<langle>BasisA!i, BasisA!i\<rangle> = 1"
proof-
  have "BasisA!i \<in> set BasisA"
    using a1 unfolding n_def BasisA_def
    by (simp add: canonical_basis_length_eq) 
  hence "norm (BasisA!i) = 1"
    by (simp add: BasisA_def is_normal)    
  hence "(norm (BasisA!i))^2 = 1"
    by simp
  thus ?thesis
    by (metis of_real_hom.hom_one power2_norm_eq_cinner') 
qed

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
    by (simp add: canonical_basis_length_eq)
  finally show ?thesis unfolding nA_def .
qed


lemma mat_of_cblinfun_classical_operator_inj_option:
  fixes f::"'a::enum \<Rightarrow> 'b::enum option"
  (* assumes r1: "inj_option f"  *)
  shows "mat_of_cblinfun (classical_operator f) = mat (CARD('b)) (CARD('a))
           (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0)"
proof-
  define nA where "nA = canonical_basis_length TYPE('a ell2)"
  define nB where "nB = canonical_basis_length TYPE('b ell2)"
  define BasisA where "BasisA = (canonical_basis::'a ell2 list)"
  define BasisB where "BasisB = (canonical_basis::'b ell2 list)"
  have "mat_of_cblinfun (classical_operator f) \<in> carrier_mat nB nA"
    unfolding nA_def nB_def
    by (metis cblinfun_of_mat_minusOp' diff_zero mat_of_cblinfun_zero' minus_carrier_mat 
        zero_carrier_mat)    
  moreover have "nA = CARD ('a)"
    unfolding nA_def
    by (simp add: canonical_basis_length_ell2_def)    
  moreover have "nB = CARD ('b)"
    unfolding nB_def
    by (simp add: canonical_basis_length_ell2_def)
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
      by (meson injI ket_distinct list.inj_map)      
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
        using classical_operator_finite .
      also have "\<dots> = 0"
        using c1 by simp
      finally have "(classical_operator f) *\<^sub>V ket (Enum.enum!c) = 0" .
      hence "(classical_operator f) *\<^sub>V BasisA!c = 0"
        using x1 by simp
      hence "\<langle>BasisB!r, (classical_operator f) *\<^sub>V BasisA!c\<rangle> = 0"
        by simp
      thus ?thesis
        unfolding mat_of_cblinfun_def BasisA_def BasisB_def
        by (simp add: a1 a2 canonical_basis_length_ell2_def)        
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
        using classical_operator_finite .
      also have "\<dots> = ket (Enum.enum!r')"
        using c1 by simp
      finally have "(classical_operator f) *\<^sub>V ket (Enum.enum!c) = ket (Enum.enum!r')" .
      hence "(classical_operator f) *\<^sub>V BasisA!c = BasisB!r'"
        using x1 x3 by simp
      moreover have "\<langle>BasisB!r, BasisB!r'\<rangle> = 0"
        using h1
        using BasisB_def \<open>r < length BasisB\<close> \<open>r' < length BasisB\<close> is_ortho_set_def is_orthonormal 
          nth_mem by fastforce
      ultimately have "\<langle>BasisB!r, (classical_operator f) *\<^sub>V BasisA!c\<rangle> = 0"
        by simp
      thus ?thesis
        unfolding mat_of_cblinfun_def BasisA_def BasisB_def
        by (simp add: a1 a2 canonical_basis_length_ell2_def)        
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
        by (rule classical_operator_finite)
      also have "\<dots> = BasisB!r"
        using w0 b1 by (simp add: BasisB_def canonical_basis_ell2_def) 
      finally have w1: "(classical_operator f) *\<^sub>V (BasisA!c) = BasisB!r"
        by simp        
      have "(mat_of_cblinfun (classical_operator f))$$(r,c)
        = \<langle>BasisB!r, (classical_operator f) *\<^sub>V (BasisA!c)\<rangle>"
        unfolding BasisB_def BasisA_def mat_of_cblinfun_def
        using \<open>nA = CARD('a)\<close> \<open>nB = CARD('b)\<close> a1 a2 nA_def nB_def by auto
      also have "\<dots> = \<langle>BasisB!r, BasisB!r\<rangle>"
        using w1 by simp        
      also have "\<dots> = 1"
        unfolding BasisB_def
        using \<open>nB = CARD('b)\<close> a1 cinner_square_canonical_basis nB_def by fastforce 
      finally show ?thesis by blast
    qed
    ultimately show ?thesis
      by (simp add: a1 a2)            
  qed
  ultimately show ?thesis using eq_matI
    by auto
qed

lemma cblinfun_of_mat_timesOp:
  "mat_of_cblinfun (F o\<^sub>C\<^sub>L G) = mat_of_cblinfun F * mat_of_cblinfun G" 
  for F::"'b::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'c::onb_enum" and G::"'a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b"
proof -
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"
  define nC where "nC = canonical_basis_length TYPE('c)"
  have a3: "mat_of_cblinfun F \<in> carrier_mat nC nB"
    unfolding nC_def nB_def mat_of_cblinfun_def
    by simp
  moreover have a2: "mat_of_cblinfun G \<in> carrier_mat nB nA"
    unfolding nB_def nA_def mat_of_cblinfun_def
    by simp
  ultimately have a1: "mat_of_cblinfun F * mat_of_cblinfun G \<in> carrier_mat nC nA"
    using Matrix.mult_carrier_mat[where A = "mat_of_cblinfun F" and B = "mat_of_cblinfun G" 
        and nr = nC and n = nB and nc = nA] 
    by blast
  have "cblinfun_of_mat (mat_of_cblinfun F * mat_of_cblinfun G)
      = ((cblinfun_of_mat (mat_of_cblinfun F))::'b\<Rightarrow>\<^sub>C\<^sub>L'c) o\<^sub>C\<^sub>L 
        ((cblinfun_of_mat (mat_of_cblinfun G))::'a\<Rightarrow>\<^sub>C\<^sub>L'b)"
    using mat_of_cblinfun_timesOp a2 a3 nA_def nB_def nC_def by blast
  moreover have "((cblinfun_of_mat (mat_of_cblinfun F))::'b\<Rightarrow>\<^sub>C\<^sub>L'c) = F"
    by (simp add: mat_of_cblinfun_inverse)    
  moreover have "((cblinfun_of_mat (mat_of_cblinfun G))::'a\<Rightarrow>\<^sub>C\<^sub>L'b) = G"
    by (simp add: mat_of_cblinfun_inverse)    
  ultimately have "F o\<^sub>C\<^sub>L G = cblinfun_of_mat (mat_of_cblinfun F * mat_of_cblinfun G)"
    by simp
  hence "mat_of_cblinfun (F o\<^sub>C\<^sub>L G) 
    = mat_of_cblinfun ((cblinfun_of_mat::complex mat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'c) 
                        (mat_of_cblinfun F * mat_of_cblinfun G))"
    by simp
  moreover have "mat_of_cblinfun ((cblinfun_of_mat::complex mat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'c) 
                        (mat_of_cblinfun F * mat_of_cblinfun G))
        = mat_of_cblinfun F * mat_of_cblinfun G"
    using a1 cblinfun_of_mat_inverse
    by (simp add: cblinfun_of_mat_inverse nA_def nC_def)
  ultimately show ?thesis by simp
qed


lemma mat_of_cblinfun_scalarMult:
  "mat_of_cblinfun ((a::complex) *\<^sub>C F) = a \<cdot>\<^sub>m (mat_of_cblinfun F)"
  for F :: "'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
proof -
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"
  define BasisA where "BasisA = (canonical_basis::'a list)"
  define BasisB where "BasisB = (canonical_basis::'b list)"

  define G where "G = (a::complex) *\<^sub>C (idOp:: 'b \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  have w1: "a *\<^sub>C F = G o\<^sub>C\<^sub>L F"
    unfolding G_def
    by simp
  have "\<langle>BasisB ! i, BasisB ! j\<rangle> = (if i = j then 1 else 0)"
    if "i < nB" and "j < nB"
    for i j
  proof(cases "i = j")
    case True
    have "BasisB!i \<in> set BasisB"
      using that(1) unfolding nB_def BasisB_def
      by (simp add: canonical_basis_length_eq) 
    hence "norm (BasisB!i) = 1"
      using BasisB_def is_normal by blast
    hence "(norm (BasisB!i))^2 = 1"
      by simp
    thus ?thesis
      by (metis True of_real_hom.hom_one power2_norm_eq_cinner') 
  next
    case False
    moreover have "distinct BasisB"
      unfolding BasisB_def
      by simp
    ultimately have "BasisB!i \<noteq> BasisB!j"
      using that unfolding nB_def
      by (simp add: BasisB_def canonical_basis_length_eq nth_eq_iff_index_eq) 
    moreover have "BasisB!i \<in> set BasisB"
      using that(1) unfolding nB_def BasisB_def
      by (simp add: canonical_basis_length_eq) 
    moreover have "BasisB!j \<in> set BasisB"
      using that(2) unfolding nB_def BasisB_def
      by (simp add: canonical_basis_length_eq) 
    ultimately show ?thesis
      using BasisB_def is_ortho_set_def is_orthonormal by fastforce
  qed
  hence w2: "mat_of_cblinfun G = a \<cdot>\<^sub>m (1\<^sub>m nB)"
    unfolding BasisB_def nB_def mat_of_cblinfun_def G_def smult_mat_def one_mat_def
    by auto
  have w3: "1\<^sub>m nB \<in> carrier_mat nB nB"
    unfolding nB_def  mat_of_cblinfun_def by auto
  have w4: "mat_of_cblinfun F \<in> carrier_mat nB nA"
    unfolding nB_def nA_def mat_of_cblinfun_def by auto
  have w5: "(1\<^sub>m nB) * (mat_of_cblinfun F) = (mat_of_cblinfun F)"
    using w4 by auto    
  have "mat_of_cblinfun (a *\<^sub>C F) = mat_of_cblinfun (G o\<^sub>C\<^sub>L F)"
    using w1
    by simp
  also have "\<dots> = (mat_of_cblinfun G)* (mat_of_cblinfun F)"
    by (simp add: cblinfun_of_mat_timesOp)
  also have "\<dots> = (a \<cdot>\<^sub>m (1\<^sub>m nB)) * (mat_of_cblinfun F)"
    using w2 by simp
  also have "\<dots> = a \<cdot>\<^sub>m ((1\<^sub>m nB) * (mat_of_cblinfun F))"
    using Matrix.mult_smult_distrib w4 by auto
  also have "\<dots> = a \<cdot>\<^sub>m (mat_of_cblinfun F)"
    by (simp add: w5)
  finally show ?thesis .
qed

lemma mat_of_cblinfun_scaleR:
  "mat_of_cblinfun ((a::real) *\<^sub>R F) = (complex_of_real a) \<cdot>\<^sub>m (mat_of_cblinfun F)"
  unfolding scaleR_scaleC by (rule mat_of_cblinfun_scalarMult)

(* TODO: rename \<rightarrow> mat_of_cblinfun_adjoint *)
lemma cblinfun_of_mat_adjoint:
  "mat_of_cblinfun (F*) = adjoint_mat (mat_of_cblinfun F)"
  for F :: "'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
proof -
  define nA where "nA = canonical_basis_length TYPE('a::onb_enum)" 
  define nB where "nB = canonical_basis_length TYPE('b::onb_enum)" 
  define M  where "M = mat_of_cblinfun F"
  have b1: "M \<in> carrier_mat nB nA"
    by (metis M_def add.right_neutral add_carrier_mat cblinfun_of_mat_plusOp' mat_of_cblinfun_zero'
        nA_def nB_def zero_carrier_mat)
  hence b2: "adjoint_mat M \<in> carrier_mat nA nB"
    unfolding adjoint_mat_def
    by simp
  hence "((cblinfun_of_mat M)::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum)* 
  = ((cblinfun_of_mat (adjoint_mat M)):: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
    using b1 mat_of_cblinfun_adjoint nA_def nB_def by metis
  hence "((cblinfun_of_mat (mat_of_cblinfun F))::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum)* 
  = ((cblinfun_of_mat (adjoint_mat (mat_of_cblinfun F))):: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
    unfolding M_def by simp
  moreover have "((cblinfun_of_mat (mat_of_cblinfun F))::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum) = F"
    by (simp add: mat_of_cblinfun_inverse)    
  ultimately have "F*  = ((cblinfun_of_mat (adjoint_mat (mat_of_cblinfun F))):: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
    by simp
  hence "mat_of_cblinfun (F*) = mat_of_cblinfun ((cblinfun_of_mat (adjoint_mat (mat_of_cblinfun F))):: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
    by simp
  also have "\<dots> = adjoint_mat (mat_of_cblinfun F)"
    using b2 cblinfun_of_mat_inverse[where M = "adjoint_mat (mat_of_cblinfun F)"]
    by (metis M_def nA_def nB_def)
  finally show ?thesis .
qed


subsubsection\<open>Gram Schmidt sub\<close>

(* TODO: Move to JNF_Missing *)
definition "vec_is_zero n v = (\<forall>i<n. v $ i = 0)"

(* TODO: Move to JNF_Missing *)
lemma vec_is_zero: "dim_vec v = n \<Longrightarrow> vec_is_zero n v \<longleftrightarrow> v = 0\<^sub>v n"
  unfolding vec_is_zero_def apply auto
  by (metis index_zero_vec(1))

(* TODO: Move to JNF_Missing *)
fun gram_schmidt_sub0
  where "gram_schmidt_sub0 n us [] = us"
  | "gram_schmidt_sub0 n us (w # ws) =
     (let w' = adjuster n w us + w in
      if vec_is_zero n w' then gram_schmidt_sub0 n us ws
                          else gram_schmidt_sub0 n (w' # us) ws)"

(* TODO: Move to JNF_Missing *)
lemma (in cof_vec_space) adjuster_already_in_span:
  assumes "w \<in> carrier_vec n"
  assumes us_carrier: "set us \<subseteq> carrier_vec n"
  assumes "corthogonal us"
  assumes "w \<in> span (set us)"
  shows "adjuster n w us + w = 0\<^sub>v n"
proof -
  define v U where "v = adjuster n w us + w" and "U = set us"
  have span: "v \<in> span U"
    unfolding v_def U_def
    apply (rule adjust_preserves_span[THEN iffD1])
    using assms corthogonal_distinct by simp_all
  have v_carrier: "v \<in> carrier_vec n"
    by (simp add: v_def assms corthogonal_distinct)
  have "v \<bullet>c us!i = 0" if "i < length us" for i
    unfolding v_def
    apply (rule adjust_zero)
    using that assms by simp_all
  hence "v \<bullet>c u = 0" if "u \<in> U" for u
    by (metis assms(3) U_def corthogonal_distinct distinct_Ex1 that)
  hence ortho: "u \<bullet>c v = 0" if "u \<in> U" for u
    apply (subst conjugate_zero_iff[symmetric])
    apply (subst conjugate_vec_sprod_comm)
    using that us_carrier v_carrier apply (auto simp: U_def)[2]
    apply (subst conjugate_conjugate_sprod)
    using that us_carrier v_carrier by (auto simp: U_def)
  from span obtain a where v: "lincomb a U = v"
    apply atomize_elim apply (rule finite_in_span[simplified])
    unfolding U_def using us_carrier by auto
  have "v \<bullet>c v = (\<Sum>u\<in>U. (a u \<cdot>\<^sub>v u) \<bullet>c v)"
    apply (subst v[symmetric])
    unfolding lincomb_def
    apply (subst finsum_scalar_prod_sum)
    using U_def span us_carrier by auto
  also have "\<dots> = (\<Sum>u\<in>U. a u * (u \<bullet>c v))"
    using U_def assms(1) in_mono us_carrier v_def by fastforce
  also have "\<dots> = (\<Sum>u\<in>U. a u * conjugate 0)"
    apply (rule sum.cong, simp)
    using span span_closed U_def us_carrier ortho by auto
  also have "\<dots> = 0"
    by auto
  finally have "v \<bullet>c v = 0"
    by -
  thus "v = 0\<^sub>v n"
    using U_def conjugate_square_eq_0_vec span span_closed us_carrier by blast
qed


(* Following closely Gram_Schmidt.gram_schmidt_sub_result in Jordan_Normal_Form *)
(* TODO: Move to JNF_Missing *)
lemma (in cof_vec_space) gram_schmidt_sub0_result:
  assumes "gram_schmidt_sub0 n us ws = us'"
    and "set ws \<subseteq> carrier_vec n"
    and "set us \<subseteq> carrier_vec n"
    and "distinct us"
    and "~ lin_dep (set us)"
    and "corthogonal us"
  shows "set us' \<subseteq> carrier_vec n \<and>
         distinct us' \<and>
         corthogonal us' \<and>
         span (set (us @ ws)) = span (set us')"  
  using assms
proof (induct ws arbitrary: us us')
  case (Cons w ws)
  show ?case
  proof (cases "w \<in> span (set us)")
    case False
    let ?v = "adjuster n w us"
    have wW[simp]: "set (w#ws) \<subseteq> carrier_vec n" using Cons by simp
    hence W[simp]: "set ws \<subseteq> carrier_vec n"
      and w[simp]: "w : carrier_vec n" by auto
    have U[simp]: "set us \<subseteq> carrier_vec n" using Cons by simp
    have UW: "set (us@ws) \<subseteq> carrier_vec n" by simp
    have wU: "set (w#us) \<subseteq> carrier_vec n" by simp
        (* have dist: "distinct (us @ w # ws)" using Cons by simp *)
    have dist_U: "distinct us" using Cons by simp
        (* and dist_W: "distinct ws" *)
        (* and dist_UW: "distinct (us @ ws)" *)
    have w_U: "w \<notin> set us" using False using span_mem by auto
        (* and w_W: "w \<notin> set ws" *)
        (* and w_UW: "w \<notin> set (us @ ws)" *)
        (* have ind: "~ lin_dep (set (us @ w # ws))" using Cons by simp *)
    have ind_U: "~ lin_dep (set us)"
      using Cons by simp
        (* and ind_W: "~ lin_dep (set ws)" *)
    have ind_wU: "~ lin_dep (insert w (set us))"
      apply (subst lin_dep_iff_in_span[simplified, symmetric])
      using w_U ind_U False by auto
    thm lin_dep_iff_in_span[simplified, symmetric]
    have corth: "corthogonal us" using Cons by simp
    have "?v + w \<noteq> 0\<^sub>v n"
      by (simp add: False adjust_nonzero dist_U)
    hence "\<not> vec_is_zero n (?v + w)"
      by (simp add: vec_is_zero)
    hence U'def: "gram_schmidt_sub0 n ((?v + w)#us) ws = us'" 
      using Cons by simp
    have v: "?v : carrier_vec n" using dist_U by auto
    hence vw: "?v + w : carrier_vec n" by auto
    hence vwU: "set ((?v + w) # us) \<subseteq> carrier_vec n" by auto
    have vsU: "?v : span (set us)" 
      apply (rule adjuster_in_span[OF w])
      using Cons by simp_all
    hence vsUW: "?v : span (set (us @ ws))"
      using span_is_monotone[of "set us" "set (us@ws)"] by auto
    have wsU: "w \<notin> span (set us)"
      using lin_dep_iff_in_span[OF U ind_U w w_U] ind_wU by auto
    hence vwU: "?v + w \<notin> span (set us)" using adjust_not_in_span[OF w U dist_U] by auto

    have span: "?v + w \<notin> span (set us)" 
      apply (subst span_add[symmetric])
      by (simp_all add: False vsU)
    hence vwUS: "?v + w \<notin> set us" using span_mem by auto
        (*     hence ind2: "~ lin_dep (set (((?v + w) # us) @ ws))"
      using lin_dep_iff_in_span[OF UW ind_UW vw] span by auto *)

    have vwU: "set ((?v + w) # us) \<subseteq> carrier_vec n" 
      using U w vw by simp
    have dist2: "distinct (((?v + w) # us))" 
      using vwUS
      by (simp add: dist_U)

    have orth2: "corthogonal ((adjuster n w us + w) # us)"
      using adjust_orthogonal[OF U corth w wsU].

    have ind_vwU: "~ lin_dep (set ((adjuster n w us + w) # us))"
      apply simp
      apply (subst lin_dep_iff_in_span[simplified, symmetric])
      by (simp_all add: ind_U vw vwUS span)

    have span_UwW_U': "span (set (us @ w # ws)) = span (set us')"
      using Cons(1)[OF U'def W vwU dist2 ind_vwU orth2] 
      using span_Un[OF vwU wU gram_schmidt_sub_span[OF w U dist_U] W W refl]
      by simp

    show ?thesis
      apply (intro conjI)
      using Cons(1)[OF U'def W vwU dist2 ind_vwU orth2] span_UwW_U' by simp_all
  next
    case True

    let ?v = "adjuster n w us"
    have "?v + w = 0\<^sub>v n"
      apply (rule adjuster_already_in_span)
      using True Cons by auto
    hence "vec_is_zero n (?v + w)"
      by (simp add: vec_is_zero)
    hence U'_def: "us' = gram_schmidt_sub0 n us ws"
      using Cons by simp
    have span: "span (set (us @ w # ws)) = span (set us')"
    proof -
      have wU_U: "span (set (w # us)) = span (set us)"
        apply (subst already_in_span[OF _ True, simplified])
        using Cons by auto
      have "span (set (us @ w # ws)) = span (set (w # us) \<union> set ws)"
        by simp
      also have "\<dots> = span (set us \<union> set ws)"
        apply (rule span_Un) using wU_U Cons by auto
      also have "\<dots> = local.span (set us')"
        using Cons U'_def by auto
      finally show ?thesis
        by -
    qed
    moreover have "set us' \<subseteq> carrier_vec n \<and> distinct us' \<and> corthogonal us'"
      unfolding U'_def using Cons by simp
    ultimately show ?thesis
      by auto
  qed
qed simp

(* TODO: Move to JNF_Missing *)
definition "gram_schmidt0 n ws = gram_schmidt_sub0 n [] ws"

(* TODO: Move to JNF_Missing *)
lemma (in cof_vec_space) gram_schmidt0_result:
  fixes ws
  defines "us' \<equiv> gram_schmidt0 n ws"
  assumes ws: "set ws \<subseteq> carrier_vec n"
  shows "set us' \<subseteq> carrier_vec n"        (is ?thesis1)
    and "distinct us'"                    (is ?thesis2)
    and "corthogonal us'"                 (is ?thesis3)
    and "span (set ws) = span (set us')"  (is ?thesis4)
proof -
  have carrier_empty: "set [] \<subseteq> carrier_vec n" by auto
  have distinct_empty: "distinct []" by simp
  have indep_empty: "lin_indpt (set [])"
    using basis_def subset_li_is_li unit_vecs_basis by auto
  have ortho_empty: "corthogonal []" by auto
  note gram_schmidt_sub0_result' = gram_schmidt_sub0_result
    [OF us'_def[symmetric, THEN meta_eq_to_obj_eq, unfolded gram_schmidt0_def] ws
      carrier_empty distinct_empty indep_empty ortho_empty]
  thus ?thesis1 ?thesis2 ?thesis3 ?thesis4
    by auto
qed

(* (* TODO: More to Preliminaries *)
lemma (in module) lin_indep_empty: "\<not> lin_dep {}"
  unfolding lin_dep_def by auto
 *)

(* TODO: Move to JNF_Missing *)
locale complex_vec_space = cof_vec_space n "TYPE(complex)" for n :: nat

lemma (in complex_vec_space) module_span_complex_span:
  fixes X :: "'a::onb_enum set"
  assumes "canonical_basis_length TYPE('a) = n"
  shows "span (vec_of_onb_enum ` X) = vec_of_onb_enum ` complex_span X"
proof -
  have carrier: "vec_of_onb_enum ` X \<subseteq> carrier_vec n"
    by (metis assms canonical_basis_length_eq carrier_vecI dim_vec_of_onb_enum_list' image_subsetI)
  have lincomb_sum: "lincomb c A = vec_of_onb_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)" 
    if B_def: "B = onb_enum_of_vec ` A" and \<open>finite A\<close>
      and AX: "A \<subseteq> vec_of_onb_enum ` X" and c'_def: "\<And>b. c' b = c (vec_of_onb_enum b)"
    for c c' A and B::"'a set"
    unfolding B_def using \<open>finite A\<close> AX
  proof induction
    case empty
    then show ?case
      by (simp add: assms vec_of_onb_enum_zero)
  next
    case (insert x F)
    then have IH: "lincomb c F = vec_of_onb_enum (\<Sum>b\<in>onb_enum_of_vec ` F. c' b *\<^sub>C b)"
      (is "_ = ?sum")
      by simp
    have xx: "vec_of_onb_enum (onb_enum_of_vec x :: 'a) = x"
      apply (rule vec_of_onb_enum_inverse)
      using assms carrier carrier_vecD insert.prems by auto
    have "lincomb c (insert x F) = c x \<cdot>\<^sub>v x + lincomb c F"
      apply (rule lincomb_insert2)
      using insert.hyps insert.prems carrier by auto
    also have "c x \<cdot>\<^sub>v x = vec_of_onb_enum (c' (onb_enum_of_vec x) *\<^sub>C (onb_enum_of_vec x :: 'a))"
      by (simp add: xx vec_of_onb_enum_scaleC c'_def)
    also note IH
    also have
      "vec_of_onb_enum (c' (onb_enum_of_vec x) *\<^sub>C (onb_enum_of_vec x :: 'a)) + ?sum
          = vec_of_onb_enum (\<Sum>b\<in>onb_enum_of_vec ` insert x F. c' b *\<^sub>C b)"
      apply simp apply (rule sym)
      apply (subst sum.insert)
      using \<open>finite F\<close> \<open>x \<notin> F\<close> dim_vec_of_onb_enum_list' insert.prems 
        vec_of_onb_enum_add c'_def by auto
    finally show ?case
      by -
  qed

  show ?thesis
  proof auto
    fix x assume "x \<in> local.span (vec_of_onb_enum ` X)"
    then obtain c A where xA: "x = lincomb c A" and "finite A" and AX: "A \<subseteq> vec_of_onb_enum ` X"
      unfolding span_def by auto
    define B::"'a set" and c' where "B = onb_enum_of_vec ` A"
      and "c' b = c (vec_of_onb_enum b)" for b::'a
    note xA
    also have "lincomb c A = vec_of_onb_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)"
      using B_def \<open>finite A\<close> AX c'_def by (rule lincomb_sum)
    also have "\<dots> \<in> vec_of_onb_enum ` complex_span X"
      unfolding complex_vector.span_explicit
      apply (rule imageI) apply (rule CollectI)
      apply (rule exI) apply (rule exI)
      using \<open>finite A\<close> AX by (auto simp: B_def)
    finally show "x \<in> vec_of_onb_enum ` complex_span X"
      by -
  next
    fix x assume "x \<in> complex_span X" 
    then obtain c' B where x: "x = (\<Sum>b\<in>B. c' b *\<^sub>C b)" and "finite B" and BX: "B \<subseteq> X"
      unfolding span_explicit by auto
    define A and c where "A = vec_of_onb_enum ` B"
      and "c b = c' (onb_enum_of_vec b)" for b
    have "vec_of_onb_enum x = vec_of_onb_enum (\<Sum>b\<in>B. c' b *\<^sub>C b)"
      using x by simp
    also have "\<dots> = lincomb c A"
      apply (rule lincomb_sum[symmetric])
      unfolding A_def c_def using BX \<open>finite B\<close>
      by (auto simp: image_image)
    also have "\<dots> \<in> span (vec_of_onb_enum ` X)"
      unfolding span_def apply (rule CollectI)
      apply (rule exI, rule exI)
      unfolding A_def using \<open>finite B\<close> BX by auto
    finally show "vec_of_onb_enum x \<in> local.span (vec_of_onb_enum ` X)"
      by -
  qed
qed

lemma (in complex_vec_space) module_span_complex_span':
  assumes "canonical_basis_length TYPE('a) = n"
  assumes "Y \<subseteq> carrier_vec n"
  shows "complex_span (onb_enum_of_vec ` Y :: 'a::onb_enum set) = onb_enum_of_vec ` local.span Y"
proof -
  define X::"'a set" where "X = onb_enum_of_vec ` Y"
  then have "complex_span (onb_enum_of_vec ` Y :: 'a set) = onb_enum_of_vec ` vec_of_onb_enum ` complex_span X"
    by (simp add: image_image)
  also have "\<dots> = onb_enum_of_vec ` local.span (vec_of_onb_enum ` X)"
    apply (subst module_span_complex_span)
    using assms by simp_all
  also have "vec_of_onb_enum ` X = Y"
    unfolding X_def image_image
    apply (rule image_cong[where g=id and M=Y and N=Y, simplified])
    using assms(1) assms(2) by auto
  finally show ?thesis
    by simp
qed

lemma Span_onb_enum_gram_schmidt0:
  defines "onb_enum == (onb_enum_of_vec :: _ \<Rightarrow> 'a::onb_enum)"
  defines "n == canonical_basis_length TYPE('a)"
  assumes "set ws \<subseteq> carrier_vec n"
  shows "Span (set (map onb_enum (gram_schmidt0 n ws)))
     = Span (set (map onb_enum ws))"
proof (transfer fixing: n ws onb_enum)
  interpret complex_vec_space.
  define gs where "gs = gram_schmidt0 n ws"
  have "closure (complex_span (set (map onb_enum gs)))
     = complex_span (set (map onb_enum gs))"
    apply (rule span_finite_dim)
    by simp
  also have "\<dots> = complex_span (onb_enum ` set gs)"
    by simp
  also have "\<dots> = onb_enum ` span (set gs)"
    unfolding onb_enum_def
    apply (rule module_span_complex_span')
    using n_def apply simp
    by (simp add: assms(3) cof_vec_space.gram_schmidt0_result(1) gs_def)
  also have "\<dots> = onb_enum ` span (set ws)"
    unfolding gs_def
    apply (subst gram_schmidt0_result(4)[where ws=ws, symmetric])
    using assms by auto
  also have "\<dots> = complex_span (onb_enum ` set ws)"
    unfolding onb_enum_def
    apply (rule module_span_complex_span'[symmetric])
    using n_def apply simp
    by (simp add: assms(3))
  also have "\<dots> = complex_span (set (map onb_enum ws))"
    by simp
  also have "\<dots> = closure (complex_span (set (map onb_enum ws)))"
    apply (rule span_finite_dim[symmetric])
    by simp
  finally show "closure (complex_span (set (map onb_enum gs)))
              = closure (complex_span (set (map onb_enum ws)))".
qed

(* TODO: To preliminaries *)
fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"


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

lemma vec_of_onb_enum_ket:
  "vec_of_onb_enum (ket i) = unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)" 
  for i::"'a::enum"
proof-
  have "dim_vec (vec_of_onb_enum (ket i)) 
      = dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i))"
  proof-
    have "dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) 
      = canonical_basis_length TYPE('a ell2)"
      by simp     
    moreover have "dim_vec (vec_of_onb_enum (ket i)) = canonical_basis_length TYPE('a ell2)"
      unfolding vec_of_onb_enum_def vec_of_onb_enum_def apply auto
      using canonical_basis_length_eq[where 'a = "'a ell2"] by auto
    ultimately show ?thesis by simp
  qed
  moreover have "vec_of_onb_enum (ket i) $ j =
    (unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) $ j"
    if "j < dim_vec (vec_of_onb_enum (ket i))"
    for j
  proof-
    have j_bound: "j < length (canonical_basis::'a ell2 list)"
      by (metis dim_vec_of_onb_enum_list' that vec_of_onb_enum_def)
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
    moreover have "length (enum_class.enum::'a list) = dim_vec (vec_of_onb_enum (ket i))"
      unfolding vec_of_onb_enum_def canonical_basis_ell2_def
      using dim_vec_of_onb_enum_list'[where v = "ket i"]
      unfolding canonical_basis_ell2_def by simp              
    ultimately have "enum_idx i < dim_vec (unit_vec (canonical_basis_length TYPE('a ell2)) 
        (enum_idx i))"
      using \<open>dim_vec (vec_of_onb_enum (ket i)) = dim_vec (unit_vec (canonical_basis_length 
        TYPE('a ell2)) (enum_idx i))\<close> by auto            
    hence r1: "(unit_vec (canonical_basis_length TYPE('a ell2)) (enum_idx i)) $ j
        = (if enum_idx i = j then 1 else 0)"
      using \<open>dim_vec (vec_of_onb_enum (ket i)) = dim_vec (unit_vec (canonical_basis_length 
        TYPE('a ell2)) (enum_idx i))\<close> that by auto
    moreover have "vec_of_onb_enum (ket i) $ j = (if enum_idx i = j then 1 else 0)"
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
      thus ?thesis using True unfolding vec_of_onb_enum_def by auto
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
      thus ?thesis using False unfolding vec_of_onb_enum_def by simp
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
    unfolding enum_idx_def apply (rule index_of_bound[where x = x 
          and y = "(Enum.enum :: 'a list)"])
    using p1 apply auto using p2 by auto
qed

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
      unfolding vec_of_onb_enum_def vec_of_onb_enum_def apply auto
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

(* TODO move to Complex_Vector *)
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

(* TODO better name *)
(* TODO: Can probably be generalized to "'a::{one_dim,basis_enum}" *)
lemma times_ell2_code: 
  fixes \<psi> \<phi> :: "'a::{CARD_1,enum} ell2"
  shows "vec_of_onb_enum (\<psi> * \<phi>)
   = vec_of_list [vec_index (vec_of_onb_enum \<psi>) 0 * vec_index (vec_of_onb_enum \<phi>) 0]"
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
    using distinct_card by fastforce      
  hence p0: "length (canonical_basis::'a ell2 list) = 1"
    unfolding canonical_basis_ell2_def by simp
  hence q1: "canonical_basis_length TYPE('a ell2) = 1"
    using canonical_basis_length_eq[where 'a = "'a ell2"] by simp
  have "vec_of_onb_enum f = vec_of_list [vec_of_onb_enum f $ 0]"
    for f::"'a ell2" 
  proof-
    have p1: "dim_vec (vec_of_onb_enum f) = 1"
      using p0
      unfolding vec_of_onb_enum_def vec_of_onb_enum_def
      by auto
    have "(vec_of_onb_enum f) $ k = vec_of_list [vec_of_onb_enum f $ 0] $ k"
      if "k < dim_vec (vec_of_onb_enum f)"
      for k
    proof-
      have "k = 0"
        using that p1 by auto
      moreover have "vec_of_list [vec_of_onb_enum f $ 0] $ 0 = vec_of_onb_enum f $ 0"
        by simp        
      ultimately show ?thesis by simp
    qed
    moreover have "dim_vec (vec_of_list [vec_of_onb_enum f $ 0]) = 1"
    proof-
      have "length [vec_of_onb_enum f $ 0] = 1"
        by simp
      thus ?thesis
        by simp 
    qed
    ultimately show ?thesis
      by (metis eq_vecI p1) 
  qed
  hence "vec_of_onb_enum (\<psi> * \<phi>) = vec_of_list [vec_of_onb_enum (\<psi> * \<phi>) $ 0]"
    by blast
  also have "\<dots> = vec_of_list [vec_of_onb_enum \<psi> $ 0 * vec_of_onb_enum \<phi> $ 0]"
  proof-
    have "Rep_ell2 (\<psi> * \<phi>) i = Rep_ell2 \<psi> i * Rep_ell2 \<phi> i"
      by (simp add: times_ell2.rep_eq)
    moreover have "vec_of_onb_enum x $ 0 = Rep_ell2 x i"
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
        apply (subgoal_tac "\<And>(x::'a) xs. (x # xs) ! 0 = x")
         apply (metis s0 One_nat_def length_0_conv length_Suc_conv)                    
        by simp
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
      hence "vec_of_onb_enum x = vec_of_onb_enum (Rep_ell2 x i *\<^sub>C (canonical_basis::'a ell2 list)!0)"
        by simp
      also have "\<dots> = Rep_ell2 x i \<cdot>\<^sub>v vec_of_onb_enum ((canonical_basis::'a ell2 list)!0)"
        by (simp add: vec_of_onb_enum_scaleC)
      also have "\<dots> = Rep_ell2 x i \<cdot>\<^sub>v unit_vec (canonical_basis_length TYPE('a ell2)) 0"
        by (simp add: q1 vec_of_basis_vector)
      finally have "vec_of_onb_enum x
         = Rep_ell2 x i \<cdot>\<^sub>v unit_vec (canonical_basis_length TYPE('a ell2)) 0".
      hence "vec_of_onb_enum x $ 0
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
    ultimately have "vec_of_onb_enum (\<psi> * \<phi>) $ 0 = vec_of_onb_enum \<psi> $ 0 * vec_of_onb_enum \<phi> $ 0"
      by auto
    thus ?thesis by simp
  qed
  finally show "vec_of_onb_enum (\<psi> * \<phi>) =
        vec_of_list [vec_of_onb_enum \<psi> $ 0 * vec_of_onb_enum \<phi> $ 0]".
qed

(* TODO better name *)
(* TODO: Can probably be generalized to "'a::{one_dim,basis_enum}" *)
lemma one_ell2_code: "vec_of_onb_enum (1 :: 'a::{CARD_1,enum} ell2) = vec_of_list [1]"
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
  have w1: "vec_of_onb_enum f = vec_of_list [vec_of_onb_enum f $ 0]"
    for f::"'a ell2" 
  proof-
    have p1: "dim_vec (vec_of_onb_enum f) = 1"
      using p0 
      unfolding vec_of_onb_enum_def vec_of_onb_enum_def
      by auto
    have "(vec_of_onb_enum f) $ k = vec_of_list [vec_of_onb_enum f $ 0] $ k"
      if "k < dim_vec (vec_of_onb_enum f)"
      for k
    proof-
      have "k = 0"
        using that p1 by auto
      moreover have "vec_of_list [vec_of_onb_enum f $ 0] $ 0 = vec_of_onb_enum f $ 0"
        by simp        
      ultimately show ?thesis by simp
    qed
    moreover have "dim_vec (vec_of_list [vec_of_onb_enum f $ 0]) = 1"
    proof-
      have "length [vec_of_onb_enum f $ 0] = 1"
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
  hence "vec_of_onb_enum (1 :: 'a::{CARD_1,enum} ell2) $ 0 = 1"
    unfolding vec_of_onb_enum_def vec_of_onb_enum_def vec_of_list_def id_def
    apply auto
    by (metis class_field.zero_not_one complex_vector.representation_ne_zero length_map 
        length_pos_if_in_set nth_map vec_of_list.abs_eq vec_of_list_index)
  thus ?thesis using w1[where f = "(1 :: 'a::{CARD_1,enum} ell2)"] by simp
qed

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
      by (metis \<open>nB = 1\<close> canonical_basis_length_eq nB_def)
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

(* TODO Move to Complex_Inner *)
lemma Span_insert:
  assumes "finite (S::'a'::complex_inner set)"
  shows "space_as_set (Span (insert a S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> space_as_set (Span S)}"
proof -
  have "closure (complex_span (insert a S)) = complex_span (insert a S)"
    by (metis assms finite_insert span_finite_dim)
  thus ?thesis
    by (simp add: Span.rep_eq assms complex_vector.span_insert span_finite_dim)
qed

(* TODO Move to Complex_Inner *)
lemma closed_subspace_complex_span_finite:
  assumes "finite (S::'a::chilbert_space set)"
  shows "closed_subspace (complex_span S)"
  unfolding closed_subspace_def apply auto
  by (simp add: assms closed_finite_dim)

(* TODO Move to Complex_Inner *)
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


(* TODO Move to Complex_Inner *)
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


(* TODO Move to Complex_Inner *)
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

(* TODO: replace by a more general lemma that show Proj (A\<union>B) = Proj A + Proj B
         under orthogonality assumptions *)
(* TODO: move to Complex_Inner *)
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
    using ios unfolding is_ortho_set_def
     apply (metis Set.set_insert Un_insert_left a1 aS insertI1 insert_union is_ortho_set_def list.simps(15))
    using aS
    by simp
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


lemma mat_of_cblinfun_proj:
  fixes a::"'a::{onb_enum}"
  defines   "d == canonical_basis_length TYPE('a)"
    and "norm2 == (vec_of_onb_enum a) \<bullet>c (vec_of_onb_enum a)"
  shows  "mat_of_cblinfun (proj a) = 
      1 / norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a]
                 * mat_of_rows d [conjugate (vec_of_onb_enum a)])"
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
  define basis where "basis = (canonical_basis :: 'a list)"
  have "mat_of_cols d [vec_of_onb_enum a] \<in> carrier_mat d 1"
    by auto
  moreover have "mat_of_rows d [vec_of_onb_enum a] \<in> carrier_mat 1 d"
    by auto
  ultimately have f1: "mat_of_cols d [vec_of_onb_enum a]
           * mat_of_rows d [conjugate (vec_of_onb_enum a)] \<in> carrier_mat d d"
    by auto
  have "mat_of_cblinfun (proj a) \<in> carrier_mat d d"
    unfolding d_def mat_of_cblinfun_def
    by auto
  moreover have "(1 / norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a]
             * mat_of_rows d [conjugate (vec_of_onb_enum a)]))
         \<in> carrier_mat d d"
  proof-
    have d1: "dim_vec (vec_of_onb_enum a) = d"
      by (simp add: canonical_basis_length_eq d_def dim_vec_of_onb_enum_list')
    hence d2: "mat_of_cols d [vec_of_onb_enum a] \<in> carrier_mat d 1"
      unfolding mat_of_cols_def by auto
    have d3: "mat_of_rows d [conjugate (vec_of_onb_enum a)] \<in> carrier_mat 1 d"
      using d1 unfolding mat_of_rows_def by auto
    have "mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)]
         \<in> carrier_mat d d"
      using d2 d3
      by simp 
    thus ?thesis
      by simp      
  qed
  moreover have "(mat_of_cblinfun (proj a)) $$ (i, j) = 
  (1 / norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)])) 
    $$ (i, j)"
    if "i < d" and "j < d" for i j
  proof-
    have norm2a: "norm2 = \<langle>a, a\<rangle>"
      unfolding norm2_def
      by (simp add: Bounded_Operators_Matrices.cinner_ell2_code)

    have "\<langle>a, basis ! j\<rangle> * cnj \<langle>a, basis ! i\<rangle>
        = (unit_vec d j \<bullet>c vec_of_onb_enum a) * cnj (unit_vec d i \<bullet>c vec_of_onb_enum a)"
    proof-
      have "\<langle>a, basis ! j\<rangle> = unit_vec d j \<bullet>c vec_of_onb_enum a"
        by (metis basis_def Bounded_Operators_Matrices.cinner_ell2_code d_def that(2) vec_of_basis_vector)
      moreover have "\<langle>a, basis ! i\<rangle> = unit_vec d i \<bullet>c vec_of_onb_enum a"
        by (metis basis_def Bounded_Operators_Matrices.cinner_ell2_code d_def that(1) vec_of_basis_vector)
      ultimately show ?thesis by simp
    qed
    have "\<dots> = (vec_of_onb_enum a $ i) * cnj (vec_of_onb_enum a $ j)"
    proof-
      have t1: "vec_of_onb_enum a \<in> carrier_vec d"
        by (metis add.right_neutral carrier_vec_dim_vec d_def index_add_vec(2) index_zero_vec(2) 
            vec_of_onb_enum_add vec_of_onb_enum_zero)
      hence "unit_vec d j \<bullet>c vec_of_onb_enum a = cnj (vec_of_onb_enum a $ j)"
        using Matrix.scalar_prod_left_unit that(2)
        by auto 
      moreover have "unit_vec d i \<bullet>c vec_of_onb_enum a = cnj (vec_of_onb_enum a $ i)"
        using t1 Matrix.scalar_prod_left_unit that(1)
        by auto
      ultimately show ?thesis by simp
    qed
    also have "\<dots> = ((mat_of_cols d [vec_of_onb_enum a] 
                    * mat_of_rows d [conjugate (vec_of_onb_enum a)])) $$ (i, j)" (is "?lhs = ?rhs")
    proof-
      have "?rhs = scalar_prod (Matrix.row (mat_of_cols d [vec_of_onb_enum a]) i) 
                   (Matrix.col (mat_of_rows d [conjugate (vec_of_onb_enum a)]) j)"
        apply (subst index_mult_mat)
        using \<open>j < d\<close> \<open>i < d\<close> by auto
      also have "\<dots> = Matrix.row (mat_of_cols d [vec_of_onb_enum a]) i $ 0 *
                 Matrix.col (mat_of_rows d [conjugate (vec_of_onb_enum a)]) j $ 0"
        unfolding scalar_prod_def
        apply (subgoal_tac "dim_vec (col (mat_of_rows d [conjugate (vec_of_onb_enum a)]) j) = 1")
        by auto
      also have "\<dots> = mat_of_cols d [vec_of_onb_enum a] $$ (i, 0) *
                 mat_of_rows d [conjugate (vec_of_onb_enum a)] $$ (0, j)"
        apply (subst index_row) using \<open>i < d\<close> apply auto[2]
        apply (subst index_col) using \<open>j < d\<close> by auto
      also have "\<dots> = vec_of_onb_enum a $ i * conjugate (vec_of_onb_enum a) $ j"
        apply (subst mat_of_cols_Cons_index_0) using \<open>i < d\<close> apply simp
        apply (subst mat_of_rows_index) using \<open>j < d\<close> by auto
      also have "\<dots> = vec_of_onb_enum a $ i * cnj (vec_of_onb_enum a $ j)"
        apply (subst vec_index_conjugate) using \<open>j < d\<close> apply auto
        by (simp add: assms(1) canonical_basis_length_eq dim_vec_of_onb_enum_list')
      finally show ?thesis
        by simp
    qed     
    have "\<langle>a, (canonical_basis::'a list) ! j\<rangle> * cnj \<langle>a, (canonical_basis::'a list) ! i\<rangle>
        = ((mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)])) 
      $$ (i, j)"
      using \<open>\<langle>a, basis ! j\<rangle> * cnj \<langle>a, basis ! i\<rangle> = unit_vec d j \<bullet>c vec_of_onb_enum a * cnj 
      (unit_vec d i \<bullet>c vec_of_onb_enum a)\<close> \<open>vec_of_onb_enum a $ i * cnj (vec_of_onb_enum a $ j)
       = (mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)]) 
      $$ (i, j)\<close> basis_def calculation by auto
    have x1: "proj a *\<^sub>V (canonical_basis::'a list) ! j = 
         (\<langle>a, (canonical_basis::'a list) ! j\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a"
      using projection_singleton[where a = a and u = "(canonical_basis::'a list)!j"] False
      apply transfer
      by (simp add: span_finite_dim)
    have x2: "(mat_of_cblinfun (proj a)) $$ (i, j) =
        \<langle>(canonical_basis::'a list) ! i, 
          proj a *\<^sub>V (canonical_basis::'a list) ! j\<rangle>"
      unfolding mat_of_cblinfun_def
      using d_def that(1) that(2) by auto
    have x3: "\<langle>(canonical_basis::'a list) ! i, 
          proj a *\<^sub>V (canonical_basis::'a list) ! j\<rangle> =
        \<langle>(canonical_basis::'a list) ! i, 
          (\<langle>a, (canonical_basis::'a list) ! j\<rangle>/\<langle>a, a\<rangle>) *\<^sub>C a\<rangle>"
      using x1 x2 by simp
    have x4: "(mat_of_cblinfun (proj a)) $$ (i, j)
          = \<langle>(canonical_basis::'a list) ! i, a\<rangle>*\<langle>a, (canonical_basis::'a list) ! j\<rangle>/norm2"
      using  x2 x3
      by (simp add: norm2a)
    have y1:"(mat_of_cols d [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)]) 
          $$ (i, j) = \<langle>(canonical_basis::'a list) ! i, a\<rangle>*\<langle>a, (canonical_basis::'a list) ! j\<rangle>"
      by (metis \<open>\<langle>a, canonical_basis ! j\<rangle> * cnj \<langle>a, canonical_basis ! i\<rangle> = (mat_of_cols d 
          [vec_of_onb_enum a] * mat_of_rows d [conjugate (vec_of_onb_enum a)]) $$ (i, j)\<close> 
          cinner_commute' ordered_field_class.sign_simps(46))      
    have "(mat_of_cblinfun (proj a)) $$ (i, j)
          = ((mat_of_cols d [vec_of_onb_enum a]
           * mat_of_rows d [conjugate (vec_of_onb_enum a)])$$(i,j))/norm2"
      using y1 x4
      by simp      
    moreover have "((mat_of_cols d [vec_of_onb_enum a]
           * mat_of_rows d [conjugate (vec_of_onb_enum a)])$$(i,j))/norm2 = (1/norm2 \<cdot>\<^sub>m (mat_of_cols d [vec_of_onb_enum a]
           * mat_of_rows d [conjugate (vec_of_onb_enum a)]))$$(i,j)"
    proof-
      have "p * (M $$ (i,j)) = (p \<cdot>\<^sub>m M) $$ (i,j)"
        if "M \<in> carrier_mat d d" and "i < d" and "j < d"
        for p::complex and  M::"complex mat" and i j::nat
        using that(1) that(2) that(3) by auto        
      moreover have f1: "mat_of_cols d [vec_of_onb_enum a]
           * mat_of_rows d [conjugate (vec_of_onb_enum a)] \<in> carrier_mat d d"
        by (simp add: f1)        
      ultimately show ?thesis
        by (metis mult.left_neutral that(1) that(2) times_divide_eq_left)            
    qed
    ultimately show ?thesis
      by simp
  qed  
  ultimately show ?thesis
    by auto 
qed

lemma mat_of_cblinfun_proj':
  fixes a b::"'a::{onb_enum, chilbert_space}" 
  defines "u == vec_of_onb_enum a"
    and "v == vec_of_onb_enum b"
    and "norm2 == vec_of_onb_enum a \<bullet>c vec_of_onb_enum a"
  shows   "mat_of_cblinfun (proj a) *\<^sub>v v = (v \<bullet>c u) / norm2 \<cdot>\<^sub>v u"
proof-
  define d where "d = canonical_basis_length TYPE('a)"
  have udim: "dim_vec u = d"
    unfolding u_def d_def
    by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list') 
  have vdim: "dim_vec v = d"
    unfolding v_def d_def
    by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list') 
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
    by (simp add: udim)
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
    unfolding scalar_prod_def vdim 
    apply auto                 
    using \<open>\<And>k. k < d \<Longrightarrow> (\<Sum>i = 0..<d. Matrix.row (Matrix.mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k
     $ i * v $ i) = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) * u $ k\<close> that by blast
  hence "mat d d (\<lambda>(i, j). u $ i * cnj (u $ j)) *\<^sub>v v = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) \<cdot>\<^sub>v u"
    unfolding mult_mat_vec_def apply auto
    by (smt \<open>\<And>k. k < d \<Longrightarrow> scalar_prod (row (Matrix.mat d d (\<lambda>(i, j). u $ i * cnj (u $ j))) k) v = (\<Sum>i = 0..<d. v $ i * cnj (u $ i)) * u $ k\<close> dim_vec eq_vecI index_smult_vec(1) index_smult_vec(2) index_vec udim) 
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
    using udim by blast
  moreover have "1 / norm2 \<cdot>\<^sub>m
      (mat_of_cols d [vec_of_onb_enum a] *
       mat_of_rows d [conjugate (vec_of_onb_enum a)]) *\<^sub>v v =
       1 / norm2 \<cdot>\<^sub>v
      ((mat_of_cols d [vec_of_onb_enum a] *
       mat_of_rows d [conjugate (vec_of_onb_enum a)]) *\<^sub>v v)"
  proof-
    have "mat_of_cols d [vec_of_onb_enum a] *
       mat_of_rows d [conjugate (vec_of_onb_enum a)] \<in> carrier_mat d d"
      unfolding d_def
      by (simp add: carrier_matI) 
    moreover have "v \<in> carrier_vec d"
      unfolding d_def v_def
      using carrier_vecI d_def v_def vdim by auto
    ultimately show ?thesis 
      using mult_mat_vec by auto
  qed
  ultimately have "1 / norm2 \<cdot>\<^sub>m
      (mat_of_cols d [vec_of_onb_enum a] *
       mat_of_rows d [conjugate (vec_of_onb_enum a)]) *\<^sub>v v =
       1 / norm2 \<cdot>\<^sub>v (v \<bullet>c u \<cdot>\<^sub>v u)"
    by (simp add: u_def)    
  hence "1 / norm2 \<cdot>\<^sub>m
      (mat_of_cols d [vec_of_onb_enum a] *
       mat_of_rows d [conjugate (vec_of_onb_enum a)]) *\<^sub>v v =
       v \<bullet>c u / norm2 \<cdot>\<^sub>v u"
    by auto
  thus ?thesis
    unfolding d_def norm2_def mat_of_cblinfun_proj[where 'a = 'a and a = a].
qed


lemma is_ortho_set_corthogonal:
  fixes S :: "'a::onb_enum list"
  defines  "R == map vec_of_onb_enum S"
  assumes a1: "is_ortho_set (set S)" and a2: "distinct S"
    and a3: "0 \<notin> set S" (* TODO: redundant assumption *)
  shows    "corthogonal R"
proof-
  have x1: "R ! i \<bullet>c R ! j = \<langle>S ! j, S ! i\<rangle>"
    if b1: "i < length R"
      and b2: "j < length R"
    for i j
    by (metis Bounded_Operators_Matrices.cinner_ell2_code R_def b1 b2 length_map nth_map)     
  have "R ! i \<bullet>c R ! j = 0"
    if b1: "i < length R"
      and b2: "j < length R"
      and b3: "i \<noteq> j"
    for i j 
  proof-
    have "S ! i \<in> set S"
      using R_def b1 by auto
    moreover have "S ! j \<in> set S"
      using R_def b2 by auto      
    moreover have "S ! j \<noteq> S ! i"
      using that a2 R_def nth_eq_iff_index_eq by auto
    ultimately have "\<langle>S ! j, S ! i\<rangle> = 0"
      using a1 unfolding is_ortho_set_def by blast
    thus ?thesis
      by (simp add: b1 b2 x1) 
  qed
  moreover have "i \<noteq> j"
    if b1: "i < length R"
      and b2: "j < length R"
      and b3: "R ! i \<bullet>c R ! j = 0"
    for i j 
  proof(rule ccontr)
    assume c1: "\<not> i \<noteq> j"
    hence  "i = j" by blast
    have "S ! i \<in> set S"
      using R_def b1 by auto
    have "S ! j \<in> set S"
      using R_def b2 by auto      
    have "S ! j = S ! i"
      using c1 by auto            
    hence "\<langle>S ! j, S ! i\<rangle> \<noteq> 0"
      using \<open>S ! i \<in> set S\<close> a3 by auto
    hence "R ! i \<bullet>c R ! j \<noteq> 0"
      using b2 c1 x1 by auto
    thus False using that(3) by blast
  qed
  ultimately show ?thesis by blast
qed

lemma corthogonal_is_ortho_set:
  fixes vs :: "'a::onb_enum list"
  assumes "corthogonal (map vec_of_onb_enum vs)"
  shows "is_ortho_set (set vs)"
proof (unfold is_ortho_set_def, intro conjI ballI impI)
  fix x y :: 'a
  assume "x \<in> set vs"
  then have "vec_of_onb_enum x \<bullet>c vec_of_onb_enum x \<noteq> 0"
    using assms unfolding corthogonal_def apply auto
    by (metis in_set_conv_nth)
  then have "\<langle>x, x\<rangle> \<noteq> 0"
    apply (subst cinner_ell2_code)
    by simp
  then show "x \<noteq> 0"
    by auto

  assume "y \<in> set vs" and "x \<noteq> y"
  then have "vec_of_onb_enum x \<bullet>c vec_of_onb_enum y = 0"
    using assms \<open>x \<in> set vs\<close> unfolding corthogonal_def apply auto
    by (metis in_set_conv_nth)
  then show "\<langle>x, y\<rangle> = 0"
    apply (subst cinner_ell2_code)
    by (metis cinner_commute cinner_ell2_code conjugate_complex_def conjugate_zero)
qed

(* TODO: Move to JNF_Missing (or remove, it's unused) *)
lemma gram_schmidt0_corthogonal:
  assumes a1: "corthogonal R" 
    and a2: "\<And>x. x \<in> set R \<Longrightarrow> dim_vec x = d"
  shows "gram_schmidt0 d R = rev R"
proof -
  have "gram_schmidt_sub0 d U R = rev R @ U"
    if "corthogonal ((rev U) @ R)"
      and "\<And>x. x \<in> set U \<union> set R \<Longrightarrow> dim_vec x = d" for U
  proof (insert that, induction R arbitrary: U)
    case Nil
    show ?case 
      by auto
  next
    case (Cons a R)
    have "a \<in> set (rev U @ a # R)"
      by simp      
    moreover have uar: "corthogonal (rev U @ a # R)"
      by (simp add: Cons.prems(1))      
    ultimately have \<open>a \<noteq> 0\<^sub>v d\<close>
      unfolding corthogonal_def
      by (metis conjugate_zero_vec in_set_conv_nth scalar_prod_right_zero zero_carrier_vec)
    then have nonzero_a: "\<not> vec_is_zero d a"
      by (simp add: Cons.prems(2) vec_is_zero)
    define T where "T = rev U @ a # R"
    have "T ! length (rev U) = a"
      unfolding T_def
      by (meson nth_append_length) 
    moreover have "(T ! i \<bullet>c T ! j = 0) = (i \<noteq> j)"
      if "i<length T"
        and "j<length T"
      for i j
      using uar 
      unfolding corthogonal_def T_def
      apply auto
      using T_def that(2) apply auto[1]
      using T_def that(1) that(2) by auto     
    moreover have "length (rev U) < length T"
      by (simp add: T_def)
    ultimately have "(T ! (length (rev U)) \<bullet>c T ! j = 0) = (length (rev U) \<noteq> j)"
      if "j<length T"
      for j
      using that by blast    
    hence "T ! (length (rev U)) \<bullet>c T ! j = 0"
      if  "j<length T"
        and "j \<noteq> length (rev U)"
      for j
      using that(1) that(2) by blast
    hence "a \<bullet>c T ! j = 0"
      if   "j < length (rev U)"
      for j
      using \<open>T ! length (rev U) = a\<close> that(1)
        \<open>length (rev U) < length T\<close> dual_order.strict_trans by blast
    moreover have "T ! j = (rev U) ! j"
      if   "j < length (rev U)"
      for j
      by (smt T_def \<open>length (rev U) < length T\<close> dual_order.strict_trans list_update_append1
          list_update_id nth_list_update_eq that)
    ultimately have "a \<bullet>c u = 0"
      if "u \<in> set (rev U)"
      for u
      by (metis in_set_conv_nth that)
    hence "a \<bullet>c u = 0"
      if "u \<in> set U"
      for u
      by (simp add: that)
    moreover have "\<And>x. x \<in> set U \<Longrightarrow> dim_vec x = d"
      by (simp add: Cons.prems(2))      
    ultimately have "adjuster d a U = 0\<^sub>v d"
    proof(induction U)
      case Nil
      then show ?case by simp
    next
      case (Cons u U)
      moreover have "0 \<cdot>\<^sub>v u + 0\<^sub>v d = 0\<^sub>v d"
      proof-
        have "dim_vec u = d"
          by (simp add: calculation(3))          
        thus ?thesis
          by auto 
      qed
      ultimately show ?case by auto
    qed
    hence adjuster_a: "adjuster d a U + a = a"
      by (simp add: Cons.prems(2) carrier_vecI)      
    have "gram_schmidt_sub0 d U (a # R) = gram_schmidt_sub0 d (a # U) R"
      by (simp add: adjuster_a nonzero_a)
    also have "\<dots> = rev (a # R) @ U"
      apply (subst Cons.IH)
      using Cons.prems by simp_all
    finally show ?case
      by -
  qed
  from this[where U="[]"] show ?thesis
    unfolding gram_schmidt0_def using assms by auto
qed



(* TODO move to Complex_Inner *)
instantiation complex :: basis_enum begin
definition "canonical_basis = [1::complex]"
definition "canonical_basis_length (_::complex itself) = 1"
instance
  apply intro_classes
  unfolding canonical_basis_complex_def canonical_basis_length_complex_def
  by (auto simp add: Complex_Vector_Spaces.span_raw_def vector_space_over_itself.span_Basis)
end

(* TODO move to Complex_Inner *)
instance complex :: one_dim
  apply intro_classes
  unfolding canonical_basis_complex_def is_ortho_set_def
  by auto

(* TODO move to Bounded_Op *)
definition butterfly_def': "butterfly (s::'a::chilbert_space)
   = vector_to_cblinfun s o\<^sub>C\<^sub>L (vector_to_cblinfun s :: complex \<Rightarrow>\<^sub>C\<^sub>L _)*"

(* TODO move to Bounded_Op *)
lift_definition one_dim_isom :: "'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'b::one_dim" is
  "\<lambda>a. of_complex (one_dim_to_complex a)"
  apply (rule cbounded_linear_intro[where K=1])
  apply (auto simp: one_dim_to_complex_def cinner_add_right)
  apply (simp add: scaleC_conv_of_complex)
  by (smt cinner_scaleC_left complex_to_one_dim_inverse norm_eq_sqrt_cinner of_complex_def one_dim_1_times_a_eq_a)

(* TODO move to Bounded_Op *)
lemma one_dim_isom_inverse[simp]: "one_dim_isom o\<^sub>C\<^sub>L one_dim_isom = idOp"
  by (transfer, rule ext, simp)

(* TODO move to Bounded_Op *)
lemma one_dim_isom_adj[simp]: "one_dim_isom* = one_dim_isom"
  apply (rule adjoint_D[symmetric])
  apply transfer
  by (simp add: of_complex_def one_dim_to_complex_def)

(* TODO move to Bounded_Op *)
lemma one_dim_isom_vector_to_cblinfun: 
  "(vector_to_cblinfun s :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L _) o\<^sub>C\<^sub>L one_dim_isom = (vector_to_cblinfun s :: 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)"
  by (transfer fixing: s, auto)


(* TODO move to Bounded_Op *)
lemma butterfly_def: "butterfly s = (vector_to_cblinfun s :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)
                                 o\<^sub>C\<^sub>L (vector_to_cblinfun s :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)*"
    (is "_ = ?rhs")
proof -
  let ?isoAC = "one_dim_isom :: 'a \<Rightarrow>\<^sub>C\<^sub>L complex"
  let ?isoCA = "one_dim_isom :: complex \<Rightarrow>\<^sub>C\<^sub>L 'a"

  have "butterfly s =
    (vector_to_cblinfun s o\<^sub>C\<^sub>L ?isoCA) o\<^sub>C\<^sub>L (vector_to_cblinfun s o\<^sub>C\<^sub>L ?isoCA)*"
    unfolding butterfly_def' one_dim_isom_vector_to_cblinfun by simp
  also have "\<dots> = vector_to_cblinfun s o\<^sub>C\<^sub>L (?isoCA o\<^sub>C\<^sub>L ?isoCA*) o\<^sub>C\<^sub>L (vector_to_cblinfun s)*"
    by (simp add: timesOp_assoc del: one_dim_isom_adj)
  also have "\<dots> = ?rhs"
    by simp
  finally show ?thesis
    by simp
qed

(* TODO move to Bounded_Op *)
lemma butterfly_apply: "butterfly \<psi> *\<^sub>V \<phi> = \<langle>\<psi>, \<phi>\<rangle> *\<^sub>C \<psi>"
  apply (subst butterfly_def)
  by (simp add: times_applyOp)

(* TODO move to Bounded_Op *)
lemma vector_to_cblinfun_0[simp]: "vector_to_cblinfun 0 = 0"
  apply transfer by simp

(* TODO move to Bounded_Op *)
lemma butterfly_0[simp]: "butterfly 0 = 0"
  apply (subst butterfly_def)
  by simp

(* TODO move to Preliminaries *)
lemma onormI:
  assumes "\<And>x. norm (f x) \<le> b * norm x"
    and "x \<noteq> 0" and "norm (f x) = b * norm x"
  shows "onorm f = b"
proof (unfold onorm_def, rule cSup_eq_maximum)
  from assms(2) have "norm x \<noteq> 0"
    by auto
  with assms(3) 
  have "norm (f x) / norm x = b"
    by auto
  then show "b \<in> range (\<lambda>x. norm (f x) / norm x)"
    by auto
next
  fix y 
  assume "y \<in> range (\<lambda>x. norm (f x) / norm x)"
  then obtain x where y_def: "y = norm (f x) / norm x"
    by auto
  then show "y \<le> b"
    unfolding y_def using assms(1)[of x]
    by (metis assms(2) assms(3) divide_eq_0_iff linordered_field_class.pos_divide_le_eq norm_ge_zero norm_zero zero_less_norm_iff)
qed

(* TODO move to Bounded_Op *)
lemma norm_butterfly: "norm (butterfly \<psi>) = norm \<psi> ^ 2"
proof (cases "\<psi>=0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis 
    unfolding norm_cblinfun.rep_eq
  proof (rule onormI[OF _ False])
    fix x 
    show "norm (butterfly \<psi> *\<^sub>V x) \<le> (norm \<psi>)\<^sup>2 * norm x"
      apply (simp add: butterfly_apply power2_eq_square)
      using norm_cauchy_schwarz[of \<psi> x]
      by (simp add: linordered_field_class.sign_simps(25) mult_left_mono ordered_field_class.sign_simps(5))
    show "norm (butterfly \<psi> *\<^sub>V \<psi>) = (norm \<psi>)\<^sup>2 * norm \<psi>"
      apply (simp add: butterfly_apply power2_eq_square)
      by (simp add: power2_norm_eq_cinner semiring_normalization_rules(29))
  qed
qed

(* TODO move to Bounded_Op *)
lemma butterfly_scaleC: "butterfly (c *\<^sub>C \<psi>) = abs c ^ 2 *\<^sub>C butterfly \<psi>"
  unfolding butterfly_def' vector_to_cblinfun_scalar_times scalar_times_adj
  by (simp add: cnj_x_x)

(* TODO move to Bounded_Op *)
lemma butterfly_scaleR: "butterfly (r *\<^sub>R \<psi>) = r ^ 2 *\<^sub>R butterfly \<psi>"
  unfolding scaleR_scaleC butterfly_scaleC power2_abs cnj_x_x[symmetric]
  unfolding power2_eq_square
  by auto

(* TODO move to Bounded_Op *)
lemma inj_butterfly: 
  assumes "butterfly x = butterfly y"
  shows "\<exists>c. cmod c = 1 \<and> x = c *\<^sub>C y"
proof (cases "x = 0")
  case True
  from assms have "y = 0"
    using norm_butterfly
    by (metis True norm_eq_zero zero_less_power2)
  with True show ?thesis
    apply (rule_tac exI[of _ 1])
    by auto
next
  case False
  define c where "c = \<langle>y, x\<rangle> / \<langle>x, x\<rangle>"
  have "\<langle>x, x\<rangle> *\<^sub>C x = butterfly x *\<^sub>V x"
    by (simp add: butterfly_apply)
  also have "\<dots> = butterfly y *\<^sub>V x"
    using assms by simp
  also have "\<dots> = \<langle>y, x\<rangle> *\<^sub>C y"
    by (simp add: butterfly_apply)
  finally have xcy: "x = c *\<^sub>C y"
    by (simp add: c_def Complex_Vector_Spaces.eq_vector_fraction_iff)
  have "cmod c * norm x = cmod c * norm y"
    using assms norm_butterfly
    by (metis norm_eq_sqrt_cinner power2_norm_eq_cinner) 
  also have "cmod c * norm y = norm (c *\<^sub>C y)"
    by simp
  also have "\<dots> = norm x"
    unfolding xcy[symmetric] by simp
  finally have c: "cmod c = 1"
    by (simp add: False)
  from c xcy show ?thesis
    by auto
qed

(* TODO move to Bounded_Op *)
lemma isometry_vector_to_cblinfun:
  assumes "norm x = 1"
  shows "isometry (vector_to_cblinfun x)"
  by (simp add: isometry_def cinner_norm_sq assms)

(* TODO move to Bounded_Op *)
lemma image_vector_to_cblinfun[simp]: "vector_to_cblinfun x *\<^sub>S top = Span {x}"
  apply transfer
  apply (rule arg_cong[where f=closure])
  unfolding complex_vector.span_singleton
  apply auto
  by (smt UNIV_I complex_scaleC_def image_iff mult.right_neutral one_dim_to_complex_one one_dim_to_complex_scaleC)


(* TODO move to Bounded_Op *)
lemma butterfly_proj:
  assumes "norm x = 1"
  shows "butterfly x = proj x"
proof -
  define B and \<phi> :: "complex \<Rightarrow>\<^sub>C\<^sub>L 'a"
    where "B = butterfly x" and "\<phi> = vector_to_cblinfun x"
  then have B: "B = \<phi> o\<^sub>C\<^sub>L \<phi>*"
    unfolding butterfly_def' by simp
  have \<phi>adj\<phi>: "\<phi>* o\<^sub>C\<^sub>L \<phi> = idOp"
    by (simp add: \<phi>_def cinner_norm_sq assms)
  have "B o\<^sub>C\<^sub>L B = \<phi> o\<^sub>C\<^sub>L (\<phi>* o\<^sub>C\<^sub>L \<phi>) o\<^sub>C\<^sub>L \<phi>*"
    unfolding B timesOp_assoc by rule
  also have "\<dots> = B"
    unfolding \<phi>adj\<phi> by (simp add: B)
  finally have idem: "B o\<^sub>C\<^sub>L B = B"
    by -
  have herm: "B = B*"
    unfolding B by simp
  from idem herm have BProj: "B = Proj (B *\<^sub>S top)"
    by (rule Proj_I)

  have "B *\<^sub>S top = Span {x}"
    unfolding B timesOp_assoc_subspace 
    by (simp add: \<phi>_def isometry_vector_to_cblinfun assms range_adjoint_isometry)

  with BProj show "B = proj x"
    by simp
qed


(* TODO: Move to the Complex_Vector_Spaces *)
lemma Span_empty[simp]: "Span {} = bot"
  apply transfer
  by simp

(* TODO move to Bounded_Op *)
lemma Proj_bot[simp]: "Proj bot = 0"
  by (metis Bounded_Operators.timesScalarSpace_0 Proj_I isProjector0 isProjector_algebraic zero_clinear_space_def)

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


(* TODO: Move to Complex_Inner_Product *)
lemma Span_canonical_basis[simp]: "Span (set canonical_basis) = top"
  using Span.rep_eq space_as_set_inject top_clinear_space.rep_eq
    closure_UNIV is_generator_set
  by metis

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

(* TODO Move to Preliminaries *)
lemma filter_Un: "Set.filter f (x \<union> y) = Set.filter f x \<union> Set.filter f y"
  unfolding Set.filter_def by auto

(* TODO To Preliminaries *)
lemma Set_filter_unchanged: "Set.filter P X = X" if "\<And>x. x\<in>X \<Longrightarrow> P x" for P and X :: "'z set"
  using that unfolding Set.filter_def by auto

(* TODO To JNF_Missing *)
lemma adjuster_carrier': (* Like adjuster_carrier but with one assm less *)
  assumes w: "(w :: 'a::conjugatable_field vec) : carrier_vec n"
    and us: "set (us :: 'a vec list) \<subseteq> carrier_vec n"
  shows "adjuster n w us \<in> carrier_vec n"
  by (insert us, induction us, auto)


definition "is_subspace_of n vs ws = 
  (let ws' = gram_schmidt0 n ws in
     \<forall>v\<in>set vs. adjuster n v ws' = - v)"

lemma Span_leq:
  fixes A B :: "'a::onb_enum list"
  shows "(Span (set A) \<le> Span (set B)) \<longleftrightarrow>
    is_subspace_of (canonical_basis_length TYPE('a)) 
      (map vec_of_onb_enum A) (map vec_of_onb_enum B)"
proof -
  define d Av Bv Bo
    where "d = canonical_basis_length TYPE('a)"
      and "Av = map vec_of_onb_enum A"
      and "Bv = map vec_of_onb_enum B"
      (* and "Ao = gram_schmidt0 d Av" *)
      and "Bo = gram_schmidt0 d Bv" 
  interpret complex_vec_space d.

  have Av_carrier: "set Av \<subseteq> carrier_vec d"
    unfolding Av_def apply auto
    by (simp add: canonical_basis_length_eq carrier_vecI d_def dim_vec_of_onb_enum_list')
  have Bv_carrier: "set Bv \<subseteq> carrier_vec d"
    unfolding Bv_def apply auto
    by (simp add: canonical_basis_length_eq carrier_vecI d_def dim_vec_of_onb_enum_list')
  have Bo_carrier: "set Bo \<subseteq> carrier_vec d"
    apply (simp add: Bo_def)
    using Bv_carrier by (rule gram_schmidt0_result(1))
  have orth_Bo: "corthogonal Bo"
    apply (simp add: Bo_def)
    using Bv_carrier by (rule gram_schmidt0_result(3))
  have distinct_Bo: "distinct Bo"
    apply (simp add: Bo_def)
    using Bv_carrier by (rule gram_schmidt0_result(2))

  have "Span (set A) \<le> Span (set B) \<longleftrightarrow> complex_span (set A) \<subseteq> complex_span (set B)"
    apply (transfer fixing: A B)
    apply (subst span_finite_dim, simp)
    by (subst span_finite_dim, simp_all)
  also have "\<dots> \<longleftrightarrow> span (set Av) \<subseteq> span (set Bv)"
    apply (simp add: Av_def Bv_def)
    apply (subst module_span_complex_span, simp add: d_def)
    apply (subst module_span_complex_span, simp add: d_def)
    by (metis inj_image_subset_iff inj_on_def onb_enum_of_vec_inverse)
  also have "\<dots> \<longleftrightarrow> span (set Av) \<subseteq> span (set Bo)"
    unfolding Bo_def Av_def Bv_def
    apply (subst gram_schmidt0_result(4)[symmetric])
    by (simp_all add: canonical_basis_length_eq carrier_dim_vec d_def dim_vec_of_onb_enum_list' image_subset_iff)
    (* apply (subst gram_schmidt0_result(4)[symmetric]) *)
    (* by (simp_all add: canonical_basis_length_eq carrier_dim_vec d_def dim_vec_of_onb_enum_list' image_subset_iff) *)
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
  finally show "Span (set A) \<le> Span (set B) \<longleftrightarrow> is_subspace_of d Av Bv"
    by simp
qed

lemma apply_cblinfun_Span: 
  "A *\<^sub>S Span (set S) = Span (onb_enum_of_vec ` set (map ((*\<^sub>v) (mat_of_cblinfun A)) (map vec_of_onb_enum S)))"
  apply (auto simp: applyOpSpace_Span image_image)
  by (metis mat_of_cblinfun_description onb_enum_of_vec_inverse)

(* TODO move to Bounded_Operators *)
lemma Proj_ortho_compl:
  "Proj (- X) = idOp - Proj X"
  apply (transfer, auto)
  using ortho_decomp
  by (metis add_diff_cancel_left') 

(* TODO move to Bounded_Operators *)
lemma Proj_inj: "Proj X = Proj Y \<Longrightarrow> X = Y"
  by (metis imageOp_Proj)


unbundle no_jnf_notation
unbundle no_cblinfun_notation


end

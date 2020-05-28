section \<open>\<open>Bounded_Operators_Code\<close> -- Support for code generation\<close>

theory Bounded_Operators_Code
  imports
    Complex_L2  Jordan_Normal_Form.Matrix 
begin

subsection\<open>\<open>Jordan_Normal_Form_Notation\<close> -- Cleaning up syntax from \<^session>\<open>Jordan_Normal_Form\<close>\<close>


text \<open>This theory defines bundes to activate/deactivate the notation
  from \<^session>\<open>Jordan_Normal_Form\<close>.

Reactivate the notation locally via "@{theory_text \<open>includes jnf_notation\<close>}" in a lemma statement.
(Or sandwich a declaration using that notation between "@{theory_text \<open>unbundle jnf_notation ... unbundle no_jnf_notation\<close>}.)
\<close>

bundle jnf_notation begin
notation transpose_mat ("(_\<^sup>T)" [1000])
notation cscalar_prod (infix "\<bullet>c" 70)
notation vec_index (infixl "$" 100)
notation smult_vec (infixl "\<cdot>\<^sub>v" 70)
notation scalar_prod (infix "\<bullet>" 70)
notation index_mat (infixl "$$" 100)
notation smult_mat (infixl "\<cdot>\<^sub>m" 70)
notation mult_mat_vec (infixl "*\<^sub>v" 70)
notation pow_mat (infixr "^\<^sub>m" 75)
notation append_vec (infixr "@\<^sub>v" 65)
notation append_rows (infixr "@\<^sub>r" 65)
end


bundle no_jnf_notation begin
no_notation transpose_mat ("(_\<^sup>T)" [1000])
no_notation cscalar_prod (infix "\<bullet>c" 70)
no_notation vec_index (infixl "$" 100)
no_notation smult_vec (infixl "\<cdot>\<^sub>v" 70)
no_notation scalar_prod (infix "\<bullet>" 70)
no_notation index_mat (infixl "$$" 100)
no_notation smult_mat (infixl "\<cdot>\<^sub>m" 70)
no_notation mult_mat_vec (infixl "*\<^sub>v" 70)
no_notation pow_mat (infixr "^\<^sub>m" 75)
no_notation append_vec (infixr "@\<^sub>v" 65)
no_notation append_rows (infixr "@\<^sub>r" 65)
end

unbundle jnf_notation
unbundle bounded_notation

subsection \<open>Setting up code generation for type bounded\<close>

text \<open>We define the canonical isomorphism between \<^typ>\<open>('a::onb_enum,'b::onb_enum) bounded\<close>
  and the complex \<^term>\<open>n*m\<close>-matrices (where n,m are the dimensions of 'a,'b, 
  respectively). This is possible if \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close> are of class \<^class>\<open>onb_enum\<close>
  since that class fixes a finite canonical basis. Matrices are represented using
  the \<^typ>\<open>_ mat\<close> type from \<^session>\<open>Jordan_Normal_Form\<close>.\<close>
  (* TODO: Define (canonical isomorphism). *)

primrec vec_of_onb_enum_list :: \<open>'a list \<Rightarrow> 'a::onb_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_onb_enum_list [] v = 0\<^sub>v (length (canonical_basis::'a list))\<close> |
  \<open>vec_of_onb_enum_list (x#ys) v = vec_of_onb_enum_list ys v +
\<langle>x, v\<rangle> \<cdot>\<^sub>v 
unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length ys)\<close>

definition vec_of_onb_enum :: \<open>'a::onb_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_onb_enum v = vec_of_onb_enum_list (canonical_basis::'a list) v\<close>

lemma dim_vec_of_onb_enum_list:
  \<open>dim_vec (vec_of_onb_enum_list (L::'a list) v) = length (canonical_basis::'a::onb_enum list)\<close>
  by (induction L, auto)

lemma vec_of_onb_enum_list_add:
  \<open>vec_of_onb_enum_list (L::'a::onb_enum list) (v1 + v2) =
 vec_of_onb_enum_list L v1 + vec_of_onb_enum_list L v2\<close>
proof (induction L arbitrary : v1 v2)
  case Nil
  thus ?case by auto
next
  case (Cons a L)
  fix v1 v2
  assume \<open>(\<And>v1 v2.
           vec_of_onb_enum_list L (v1 + v2) =
           vec_of_onb_enum_list L v1 + vec_of_onb_enum_list L v2)\<close>
  have \<open>vec_of_onb_enum_list (a # L) (v1 + v2) = vec_of_onb_enum_list (a # L) v1 + vec_of_onb_enum_list (a # L) v2\<close>
  proof-
    have \<open>dim_vec (vec_of_onb_enum_list L v1) = length (canonical_basis::'a list)\<close>
      by (simp add: dim_vec_of_onb_enum_list)
    moreover have \<open>dim_vec (vec_of_onb_enum_list L v2) = length (canonical_basis::'a list)\<close>
      by (simp add: dim_vec_of_onb_enum_list)
    moreover have \<open>dim_vec (\<langle>a, v1\<rangle> \<cdot>\<^sub>v  unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L) )
          =  length (canonical_basis::'a list)\<close>
      by auto
    moreover have \<open>dim_vec (\<langle>a, v2\<rangle> \<cdot>\<^sub>v  unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L) )
          =  length (canonical_basis::'a list)\<close>
      by auto
    moreover have \<open>vec_of_onb_enum_list (a # L) (v1 + v2) = 
           vec_of_onb_enum_list L (v1 + v2) 
+ \<langle>a, v1 + v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L)\<close>
      by auto
    moreover have \<open>vec_of_onb_enum_list L (v1 + v2) =
            vec_of_onb_enum_list L v1 + vec_of_onb_enum_list L v2\<close>
      by (simp add: Cons.IH)        
    moreover have \<open>\<langle>a, v1 + v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L)
= \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L)
+ \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L)\<close>
    proof-
      have \<open>\<langle>a, v1 + v2\<rangle> = \<langle>a, v1\<rangle> + \<langle>a, v2\<rangle>\<close>
        by (simp add: cinner_right_distrib)
      thus ?thesis
        by (simp add: add_smult_distrib_vec) 
    qed
    ultimately have \<open>vec_of_onb_enum_list (a # L) (v1 + v2) =
   (vec_of_onb_enum_list L v1 + \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L))
+  (vec_of_onb_enum_list L v2 + \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L))\<close>
      by auto
    thus ?thesis by auto
  qed
  thus \<open>vec_of_onb_enum_list (a # L) (v1 + v2) =
       vec_of_onb_enum_list (a # L) v1 + vec_of_onb_enum_list (a # L) v2\<close> 
    by blast
qed

lemma vec_of_onb_enum_add:
  \<open>vec_of_onb_enum (v1 + v2) = vec_of_onb_enum v1 + vec_of_onb_enum v2\<close>
  by (simp add: vec_of_onb_enum_def vec_of_onb_enum_list_add)


lemma vec_of_onb_enum_list_mult:
  fixes L :: "'a::onb_enum list"
  shows \<open>vec_of_onb_enum_list L (c *\<^sub>C v) = c \<cdot>\<^sub>v vec_of_onb_enum_list L v\<close>
proof (induction L)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  let ?basis = "canonical_basis :: 'a list"
  let ?dim = "length ?basis"

  have dim_L: "dim_vec (vec_of_onb_enum_list L v) = ?dim"
    by (simp add: dim_vec_of_onb_enum_list)

  have "vec_of_onb_enum_list (a # L) (c *\<^sub>C v) 
      = vec_of_onb_enum_list L (c *\<^sub>C v) + c * \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length ?basis) (length ?basis - length L)"
    by simp
  also have "\<dots> = c \<cdot>\<^sub>v vec_of_onb_enum_list L v + c * \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length ?basis) (length ?basis - length L)"
    using Cons.IH by simp
  also have "\<dots> = c \<cdot>\<^sub>v vec_of_onb_enum_list L v + c \<cdot>\<^sub>v (\<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length ?basis) (length ?basis - length L))"
    by (simp add: smult_smult_assoc)
  also have "\<dots> = c \<cdot>\<^sub>v (vec_of_onb_enum_list L v + \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length ?basis) (length ?basis - length L))"
    apply (rule smult_add_distrib_vec[where n="?dim", symmetric])
    using dim_L apply auto
    by (metis carrier_vec_dim_vec)
  also have "\<dots> = c \<cdot>\<^sub>v vec_of_onb_enum_list (a # L) v"
    by auto
  finally show ?case
    by -
qed


lemma vec_of_onb_enum_mult:
  \<open>vec_of_onb_enum (c *\<^sub>C v) = c \<cdot>\<^sub>v vec_of_onb_enum v\<close>
  by (simp add: vec_of_onb_enum_def vec_of_onb_enum_list_mult)

fun onb_enum_of_vec_list :: \<open>'a list \<Rightarrow> complex list \<Rightarrow> 'a::onb_enum\<close> where 
  \<open>onb_enum_of_vec_list [] v = 0\<close> |
  \<open>onb_enum_of_vec_list y [] = 0\<close> |
  \<open>onb_enum_of_vec_list (x#ys) (v#vs) = v *\<^sub>C x + onb_enum_of_vec_list ys vs\<close>

definition onb_enum_of_vec :: \<open>complex vec \<Rightarrow> 'a::onb_enum\<close> where
  \<open>onb_enum_of_vec v = onb_enum_of_vec_list (canonical_basis::'a list) (list_of_vec v)\<close>

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
  defines "basis \<equiv> canonical_basis::'a::onb_enum list"
  assumes \<open>dim_vec v1 = length basis\<close> and
    \<open>dim_vec v2 = length basis\<close>
  shows \<open>((onb_enum_of_vec (v1 + v2)) :: 'a) = onb_enum_of_vec v1 + onb_enum_of_vec v2\<close>
proof -
  define l1 l2 where "l1 = list_of_vec v1" and "l2 = list_of_vec v2"
  have length: "length l1 = length l2"
    by (simp add: assms(2) assms(3) l1_def l2_def)
  have length_basis: "length l2 = length basis"
    by (simp add: assms(3) l2_def)
  have \<open>(onb_enum_of_vec::_\<Rightarrow>'a) (v1 + v2) = onb_enum_of_vec_list basis (list_of_vec (v1+v2))\<close>
    by (simp add: basis_def onb_enum_of_vec_def)
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
    by (simp add: basis_def onb_enum_of_vec_def l1_def l2_def)
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
  defines "basis \<equiv> canonical_basis::'a::onb_enum list"
  assumes \<open>dim_vec v = length basis\<close> 
  shows \<open>((onb_enum_of_vec (c \<cdot>\<^sub>v v)) :: 'a) =  c *\<^sub>C onb_enum_of_vec v\<close>
proof -
  define l where "l = list_of_vec v"
  have length_basis: "length l = length basis"
    by (simp add: assms(2) l_def)
  have \<open>(onb_enum_of_vec::_\<Rightarrow>'a) (c \<cdot>\<^sub>v v) =
 onb_enum_of_vec_list basis (list_of_vec (c \<cdot>\<^sub>v v))\<close>
    by (simp add: basis_def onb_enum_of_vec_def)
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
    by (simp add: basis_def onb_enum_of_vec_def l_def)
  finally show ?thesis
    by auto
qed

(* NEW *)
lemma vector_space_zero_canonical_basis:
  assumes f1: "(canonical_basis::('a::onb_enum list)) = []"
  shows "(v::'a) = 0"
proof-
  have "closure (complex_vector.span (set (canonical_basis::('a::onb_enum list)))) = UNIV"
    using is_onb_set unfolding is_onb_def is_ob_def is_basis_def by auto
  moreover have "complex_vector.span (set (canonical_basis::('a::onb_enum list))) = {0}"
  proof-
    have "set (canonical_basis::('a::onb_enum list)) = {}"
      using f1 by auto      
    thus ?thesis by simp 
  qed
  ultimately show ?thesis by auto
qed

lemma cinner_span_breakdown_eq:
  assumes f1: "a \<notin> S" and f2: "is_ortho_set (insert a S)" and f3: "a \<in> sphere 0 1"
  shows
    "(x \<in> Complex_Vector_Spaces.span (insert a S)) =
   (x - \<langle>a, x\<rangle> *\<^sub>C a \<in> Complex_Vector_Spaces.span S)"
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
      have "cmod \<langle>a, a\<rangle> = 1"
        using f3 unfolding sphere_def apply auto 
        using norm_eq_sqrt_cinner[where x = a] 
        by auto
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
  assumes "w \<in> complex_vector.span (set L)" and "distinct L" and "is_ortho_set (set L)" 
    and "\<forall>a\<in>set L. a\<in>sphere 0 1"
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
      by smt
    moreover have "is_ortho_set (set L)"
      unfolding is_ortho_set_def 
    proof auto
      fix x y::'a
      assume o1: "x \<in> set L" and o2: "y \<in> set L" and o3: "x \<noteq> y" 
      have "x \<in> set (a#L)"
        by (simp add: o1)        
      moreover have "y \<in> set (a#L)"
        by (simp add: o2)
      ultimately show "\<langle>x, y\<rangle> = 0"
        using o3 Cons.prems(3) is_ortho_set_def by blast 
    qed
    moreover have "\<forall>a\<in>set L. a\<in>sphere 0 1"
      using Cons.prems(4) by auto      
    ultimately have "(\<Sum>b\<in>(set L). \<langle>b, w - \<langle>a, w\<rangle> *\<^sub>C a\<rangle> *\<^sub>C b) = w - \<langle>a, w\<rangle> *\<^sub>C a"
      using Cons.IH Cons.prems(2) distinct.simps(2) sum.cong
      by smt
    thus ?thesis by simp
  qed
  also have "\<dots> = w"
    by simp
  finally have "(\<Sum>b\<in>set (a # L). \<langle>b, w\<rangle> *\<^sub>C b) = w"
    by blast
  thus "w = (\<Sum>b\<in>set (a # L). \<langle>b, w\<rangle> *\<^sub>C b)" by simp
qed


thm span_set_inner
lemma canonical_basis_inner:
  "w = (\<Sum>b\<in>set (canonical_basis::'a::onb_enum list). \<langle>b, w\<rangle> *\<^sub>C b)"
proof (rule Ortho_expansion_finite)
  show "is_onb (set (canonical_basis::'a list))"
    unfolding is_onb_def is_ob_def apply auto
    apply (simp add: is_orthonormal)
    apply (simp add: is_basis_set)
    by (simp add: is_normal)

  show "finite (set (canonical_basis::'a list))"
    by simp    
qed

(* NEW *)
lemma onb_enum_of_vec_list_list_of_vec:
  fixes w::"'a::onb_enum"
  assumes f1: "distinct (canonical_basis::('a list))"
  shows  "onb_enum_of_vec_list (canonical_basis::('a list))
         (list_of_vec (vec_of_onb_enum w)) = w"
proof-
  have "onb_enum_of_vec_list (canonical_basis::('a list))
         (list_of_vec (vec_of_onb_enum w)) = 
        sum (\<lambda>b. \<langle>b, w \<rangle> *\<^sub>C b) (set (canonical_basis::('a list)))"
    sorry
  also have "\<dots> = w"
    using canonical_basis_inner[where w = w] by simp
  finally show ?thesis by blast
qed

(* TODO: When written as \<open>onb_enum_of_vec (vec_of_onb_enum v) = v\<close>
   such a lemma is more easily used as, e.g., a simp-rule (in my experience) *)
lemma onb_enum_of_vec_COMP_vec_of_onb_enum:
  \<open>(onb_enum_of_vec::(complex vec \<Rightarrow> 'a::onb_enum)) \<circ> (vec_of_onb_enum::('a \<Rightarrow> complex vec))
 = (id::('a \<Rightarrow> 'a))\<close>
proof-
  have \<open>dim_vec (vec_of_onb_enum b) = length (canonical_basis::'a list)\<close>
    for b::'a
    by (simp add: dim_vec_of_onb_enum_list vec_of_onb_enum_def)    
  define f::\<open>'a \<Rightarrow> 'a\<close> where \<open>f v = onb_enum_of_vec ( vec_of_onb_enum v ) - v\<close>
    for v::'a
  have \<open>v \<in> set (canonical_basis::('a list)) \<Longrightarrow> f v = 0\<close>
    for v
  proof-
    have \<open>distinct (canonical_basis::('a list))\<close>
      by (simp add: distinct_canonical_basis)    
    thus ?thesis 
      unfolding f_def
      using Bounded_Operators_Code.onb_enum_of_vec_def[where v = "vec_of_onb_enum v"]
        onb_enum_of_vec_list_list_of_vec
      by (simp add: \<open>onb_enum_of_vec (vec_of_onb_enum v) = onb_enum_of_vec_list canonical_basis (list_of_vec (vec_of_onb_enum v))\<close>)
  qed
  moreover have \<open>clinear f\<close>
  proof-
    have \<open>clinear (\<lambda> v. (onb_enum_of_vec::(complex vec \<Rightarrow> 'a::onb_enum)) ( (vec_of_onb_enum::('a \<Rightarrow> complex vec)) v) )\<close>
      unfolding clinear_def
    proof
      show "onb_enum_of_vec (vec_of_onb_enum (b1 + b2)) = onb_enum_of_vec (vec_of_onb_enum b1) + ((onb_enum_of_vec (vec_of_onb_enum b2))::'a)"
        for b1 :: 'a
          and b2 :: 'a
      proof-
        have \<open>onb_enum_of_vec (vec_of_onb_enum (b1 + b2)) = 
              onb_enum_of_vec (vec_of_onb_enum b1 + vec_of_onb_enum b2)\<close>
          by (simp add: vec_of_onb_enum_def vec_of_onb_enum_list_add)
        also have \<open>\<dots> = 
              onb_enum_of_vec (vec_of_onb_enum b1) + ((onb_enum_of_vec (vec_of_onb_enum b2))::'a)\<close>
        proof-
          have \<open>length (canonical_basis::'a list) \<le> dim_vec (vec_of_onb_enum b1)\<close>
            by (simp add: \<open>\<And>b. dim_vec (vec_of_onb_enum b) = length canonical_basis\<close>)
          moreover have \<open>length (canonical_basis::'a list) \<le> dim_vec (vec_of_onb_enum b2)\<close>
            by (simp add: \<open>\<And>b. dim_vec (vec_of_onb_enum b) = length canonical_basis\<close>)
          ultimately show ?thesis
            unfolding onb_enum_of_vec_def
          proof -
            have ?thesis
              by (meson \<open>\<And>b. dim_vec (vec_of_onb_enum b) = length canonical_basis\<close> onb_enum_of_vec_add)
            thus "onb_enum_of_vec_list canonical_basis (list_of_vec (vec_of_onb_enum b1 + vec_of_onb_enum b2)) = (onb_enum_of_vec_list canonical_basis (list_of_vec (vec_of_onb_enum b1))::'a) + onb_enum_of_vec_list canonical_basis (list_of_vec (vec_of_onb_enum b2))"
              by (simp add: onb_enum_of_vec_def)
          qed            
        qed
        finally show ?thesis by auto
      qed
      show "onb_enum_of_vec (vec_of_onb_enum (r *\<^sub>C (b::'a))) = r *\<^sub>C (onb_enum_of_vec (vec_of_onb_enum b)::'a)"
        for r :: complex
          and b :: 'a
      proof-
        have \<open>onb_enum_of_vec (vec_of_onb_enum (r *\<^sub>C b)) = 
              onb_enum_of_vec (r \<cdot>\<^sub>v (vec_of_onb_enum b))\<close>
          by (simp add: vec_of_onb_enum_def vec_of_onb_enum_list_mult)          
        also have \<open>\<dots> = 
              r *\<^sub>C ((onb_enum_of_vec (vec_of_onb_enum b))::'a)\<close>
        proof-
          have \<open>length (canonical_basis::'a list) \<le> dim_vec (vec_of_onb_enum b)\<close>
            by (simp add: \<open>\<And>b. dim_vec (vec_of_onb_enum b) = length canonical_basis\<close>)
          thus ?thesis
            unfolding onb_enum_of_vec_def
          proof -
            have ?thesis
              by (meson \<open>\<And>b. dim_vec (vec_of_onb_enum b) = length canonical_basis\<close> onb_enum_of_vec_mult)
            then show "onb_enum_of_vec_list canonical_basis (list_of_vec (r \<cdot>\<^sub>v vec_of_onb_enum b)) = r *\<^sub>C (onb_enum_of_vec_list canonical_basis (list_of_vec (vec_of_onb_enum b))::'a)"
              by (simp add: onb_enum_of_vec_def)
          qed         
        qed
        finally show ?thesis by auto
      qed
    qed
    moreover have \<open>clinear (\<lambda>v::'a. v)\<close>
      by (simp add: clinearI)      
    ultimately show ?thesis unfolding f_def
      using complex_vector.linear_compose_sub by auto            
  qed
  ultimately have \<open>v \<in> complex_vector.span (set (canonical_basis::('a list))) \<Longrightarrow> f v = 0\<close>
    for v
    using Complex_Vector_Spaces.equal_span_0
    by blast
  moreover have \<open>complex_vector.span (set (canonical_basis::('a list))) = UNIV\<close>
  proof-
    have \<open>closure (complex_vector.span (set (canonical_basis::('a list)))) = UNIV\<close>
      using is_onb_set
      unfolding is_onb_def is_ob_def is_basis_def
      by blast
    moreover have \<open>closure (complex_vector.span (set (canonical_basis::('a list)))) = 
                   complex_vector.span (set (canonical_basis::('a list)))\<close>
    proof-
      have \<open>finite (set (canonical_basis::('a list)))\<close>
        by simp        
      thus ?thesis
        by (simp add: span_finite_dim) 
    qed
    ultimately show ?thesis by blast
  qed
  ultimately have \<open>f v = 0\<close>
    for v
    by auto
  thus ?thesis unfolding f_def by auto
qed

(* TODO: When written as \<open>vec_of_onb_enum (onb_enum_of_vec v) = v\<close>
   such a lemma is more easily used as, e.g., a simp-rule (in my experience) *)
(* TODO: Not true. Only holds for vectors v with "dim v = canonical_basis_length" *)
lemma vec_of_onb_enum_COMP_onb_enum_of_vec:
  \<open>vec_of_onb_enum \<circ> onb_enum_of_vec = id\<close>
  sorry


definition mat_of_bounded :: \<open>('a::onb_enum,'b::onb_enum) bounded \<Rightarrow> complex mat\<close> where
  \<open>mat_of_bounded = undefined\<close>

definition bounded_of_mat :: \<open>complex mat \<Rightarrow> ('a::onb_enum,'b::onb_enum) bounded\<close> where
  \<open>bounded_of_mat = undefined\<close>


lemma mat_of_bounded_inj: "inj mat_of_bounded"
  sorry

text \<open>The following lemma registers bounded as an abstract datatype with 
  constructor \<^const>\<open>bounded_of_mat\<close>.
  That means that in generated code, all bounded operators will be represented
  as \<^term>\<open>bounded_of_mat X\<close> where X is a matrix.
  In code equations for operations involving operators (e.g., +), we
  can then write the equation directly in terms of matrices
  by writing, e.g., \<^term>\<open>mat_of_bounded (A+B)\<close> in the lhs,
  and in the rhs we define the matrix that corresponds to the sum of A,B.
  In the rhs, we can access the matrices corresponding to A,B by
  writing \<^term>\<open>mat_of_bounded B\<close>.
  (See, e.g., lemma \<open>bounded_of_mat_plusOp\<close> below).

  See [TODO: bibtex reference to code generation tutorial] for more information on 
  @{theory_text \<open>[code abstype]\<close>}.\<close>
lemma mat_of_bounded_inverse [code abstype]:
  "bounded_of_mat (mat_of_bounded B) = B" 
  for B::"('a::onb_enum,'b::onb_enum) bounded"
  sorry

subsection \<open>Code equations for bounded operators\<close>

text \<open>In this subsection, we define the code for all operations involving only 
  operators (no combinations of operators/vectors/subspaces)\<close>

text \<open>This lemma defines addition. By writing \<^term>\<open>mat_of_bounded (M + N)\<close>
on the left hand side, we get access to the\<close>
lemma bounded_of_mat_plusOp[code]:
  "mat_of_bounded (M + N) =  (mat_of_bounded M + mat_of_bounded N)" 
  for M::"('a::onb_enum,'b::onb_enum) bounded" and N::"('a::onb_enum,'b) bounded"
  sorry

lemma bounded_of_mat_id[code]:
  "mat_of_bounded (idOp :: ('a::onb_enum,'a) bounded) = one_mat (canonical_basis_length TYPE('a))"
  sorry

lemma bounded_of_mat_timesOp[code]:
  "mat_of_bounded (M *\<^sub>o N) =  (mat_of_bounded M * mat_of_bounded N)" 
  for M::"('b::onb_enum,'c::onb_enum) bounded" and N::"('a::onb_enum,'b) bounded"
  sorry

lemma bounded_of_mat_minusOp[code]:
  "mat_of_bounded (M - N) =  (mat_of_bounded M - mat_of_bounded N)" 
  for M::"('a::onb_enum,'b::onb_enum) bounded" and N::"('a::onb_enum,'b) bounded"
  sorry

lemma bounded_of_mat_uminusOp[code]:
  "mat_of_bounded (- M) = - mat_of_bounded M" for M::"('a::onb_enum,'b::onb_enum) bounded"
  sorry

lemma mat_of_bounded_scalarMult[code]:
  "mat_of_bounded ((a::complex) *\<^sub>C M) = smult_mat a (mat_of_bounded M)" for M :: "('a::onb_enum,'b::onb_enum) bounded"
  sorry

text \<open>This instantiation defines a code equation for equality tests for bounded operators.\<close>
instantiation bounded :: (onb_enum,onb_enum) equal begin
definition [code]: "equal_bounded M N \<longleftrightarrow> mat_of_bounded M = mat_of_bounded N" 
  for M N :: "('a,'b) bounded"
instance 
  apply intro_classes
  unfolding equal_bounded_def 
  using mat_of_bounded_inj injD by fastforce
end

definition "adjoint_mat M = transpose_mat (map_mat cnj M)"

lemma bounded_of_mat_adjoint[code]:
  "mat_of_bounded (adjoint A) = adjoint_mat (mat_of_bounded A)"
  for A :: "('a::onb_enum,'b::onb_enum) bounded"
  sorry

lemma mat_of_bounded_zero[code]:
  "mat_of_bounded (0::('a::onb_enum,'b::onb_enum) bounded)
       = zero_mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))"
  sorry

lemma mat_of_bounded_classical_operator[code]: 
  "mat_of_bounded (classical_operator f) = mat (CARD('b)) (CARD('a))
  (\<lambda>(r,c). if f (Enum.enum!c) = Some (Enum.enum!r) then 1 else 0)" 
  for f::"'a::enum \<Rightarrow> 'b::enum option"
  sorry

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
  by auto

unbundle no_jnf_notation
unbundle no_bounded_notation

end

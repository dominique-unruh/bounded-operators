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

(* TODO: use this definition instead of vec_of_onb_enum_list (+ fix proofs) *)
primrec vec_of_onb_enum_list :: \<open>'a list \<Rightarrow> 'a::onb_enum \<Rightarrow> nat \<Rightarrow> complex vec\<close> where
  \<open>vec_of_onb_enum_list [] v _ = 0\<^sub>v (length (canonical_basis::'a list))\<close> |
  \<open>vec_of_onb_enum_list (x#ys) v i = vec_of_onb_enum_list ys v (Suc i) +
    \<langle>x, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i\<close>

definition vec_of_onb_enum :: \<open>'a::onb_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_onb_enum v = vec_of_onb_enum_list (canonical_basis::'a list) v 0\<close>

definition vec_of_onb_enum2 :: \<open>'a::onb_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_onb_enum2 v = vec_of_list (map (complex_vector.representation (set canonical_basis) v) canonical_basis)\<close>

lemma dim_vec_of_onb_enum_list:
  \<open>dim_vec (vec_of_onb_enum_list (L::'a list) v i) = length (canonical_basis::'a::onb_enum list)\<close>
  by (induction L, auto)

lemma dim_vec_of_onb_enum_list':
  \<open>dim_vec (vec_of_onb_enum (v::'a)) = length (canonical_basis::'a::onb_enum list)\<close>
  unfolding vec_of_onb_enum_def 
  using dim_vec_of_onb_enum_list[where L = "(canonical_basis::'a::onb_enum list)" 
      and v = v and i = 0] by auto  

lemma vec_of_onb_enum_list_add:
  \<open>vec_of_onb_enum_list (L::'a::onb_enum list) (v1 + v2) i =
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


lemma vec_of_onb_enum_add:
  \<open>vec_of_onb_enum (v1 + v2) = vec_of_onb_enum v1 + vec_of_onb_enum v2\<close>
  by (simp add: vec_of_onb_enum_def vec_of_onb_enum_list_add) 

lemma vec_of_onb_enum_list_mult:
  fixes L :: "'a::onb_enum list"
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

lemma vec_of_onb_enum_mult:
  \<open>vec_of_onb_enum (c *\<^sub>C v) = c \<cdot>\<^sub>v vec_of_onb_enum v\<close>
  by (simp add: vec_of_onb_enum_def vec_of_onb_enum_list_mult)

fun onb_enum_of_vec_list :: \<open>'a list \<Rightarrow> complex list \<Rightarrow> 'a::onb_enum\<close> where 
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
    (* TODO: norm a = 1 *)
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
    (* TODO: norm a = 1 *)
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

(* TODO?: Remove and use onb_enum_of_vec_list_def' instead? *)
lemma onb_enum_of_vec_expansion:  
  fixes S::"'a::onb_enum list" and L::"complex list"
  assumes f1: "distinct S" and f2: "length S = length L"
  shows "onb_enum_of_vec_list S L = (\<Sum>i\<in>{0..<length S}. L!i *\<^sub>C S!i)"
    (* TODO?: = sum_list (map2 (\<lambda>(l,s). l *\<^sub>C s) S L) *)
proof-
  have "onb_enum_of_vec_list S L 
      = (\<Sum>i\<in>{0..<length S}. (L!i) *\<^sub>C S!i)"
    if  f1: "distinct S" and f2: "length S = length L"
      and f3: "length S = n"
    for S::"'a::onb_enum list" and L::"complex list" and n::nat
    using that proof(induction n arbitrary: S L)
    case 0
    have "S = []"
      using "0.prems"(3) by auto
    moreover have "L = []"
      using "0.prems"(2) "0.prems"(3) by auto
    ultimately show ?case by simp
  next
    case (Suc n)
    have "\<exists>S' s. S = s # S' \<and> s \<notin> set S'"
      by (metis Suc.prems(1) Suc.prems(3) Suc_length_conv distinct.simps(2))
    then obtain S' s where a1: "S = s # S'" and a2: "s \<notin> set S'"
      by blast
    have distinctS: "distinct S'"
      using Suc.prems(1) a1 by auto
    have "length L = Suc n"
      using Suc.prems(2) Suc.prems(3) by auto
    hence "\<exists>L' l. L = l # L'"
      by (metis Suc_length_conv)    
    then obtain L' l where b1: "L = l # L'"
      by blast
    have "length S' = length L'"
      using Suc.prems(2) a1 b1 by auto    
    moreover have "length S' = n"
      using Suc.prems(2) Suc.prems(3) b1 calculation by auto    
    ultimately have prethesis: "onb_enum_of_vec_list S' L' =
    (\<Sum>i = 0..<length S'. L' ! i *\<^sub>C S' ! i)"
      using distinctS Suc.IH[where S = S' and L = L']
      by blast
    have "onb_enum_of_vec_list S L = onb_enum_of_vec_list (s#S') (l#L')"
      by (simp add: a1 b1)
    also have "\<dots> =  l *\<^sub>C s + onb_enum_of_vec_list S' L'"
      by simp
    also have "\<dots> =  l *\<^sub>C s + (\<Sum>i = 0..<length S'. L' ! i *\<^sub>C S' ! i)"
      by (simp add: prethesis)
    also have "\<dots> =  L ! 0 *\<^sub>C S ! 0 + (\<Sum>i = 0..<length S'. L' ! i *\<^sub>C S' ! i)"
      by (simp add: a1 b1)
    also have "\<dots> =  L ! 0 *\<^sub>C S ! 0 + (\<Sum>i = 0..<length S'. L ! (Suc i) *\<^sub>C S ! (Suc i))"
      using a1 b1 by auto
    also have "\<dots> =  L ! 0 *\<^sub>C S ! 0 + (\<Sum>i = Suc 0..< Suc (length S'). L ! i *\<^sub>C S ! i)"
      by (metis (no_types, lifting) sum.cong sum.shift_bounds_Suc_ivl)
    also have "\<dots> =  L ! 0 *\<^sub>C S ! 0 + (\<Sum>i = 1..< length S. L ! i *\<^sub>C S ! i)"
      by (simp add: Suc.prems(3) \<open>length S' = n\<close>)
    also have "\<dots> = (\<Sum>i = 0..< length S. L ! i *\<^sub>C S ! i)"
      by (simp add: Suc.prems(3) sum.atLeast_Suc_lessThan)    
    finally show ?case by blast
  qed
  thus ?thesis using assms by blast
qed

(* TODO: check if needed at all (in the end) *)
lemma list_sum_function:
  fixes f :: "'a \<Rightarrow> 'b::ab_group_add" and S :: "'a list"
  shows "(\<Sum>i = 0..<length S. f (S ! i)) = (\<Sum>b\<leftarrow>S. f b)"
proof(induction S)
  case Nil thus ?case by simp 
next
  case (Cons a S)
  thus ?case
    by (metis (mono_tags, lifting) atLeastLessThan_iff length_map nth_map sum.cong sum_list_sum_nth) 
qed


(* TODO: Maybe just use (simp add: dim_vec_of_onb_enum_list) instead of using this *)
lemma length_list_of_vec_vec_of_onb_enum_list:
  fixes w::"'a::onb_enum" and S::"'a list"
  shows "length (list_of_vec (vec_of_onb_enum_list S w i)) = length (canonical_basis::'a list)"
  by (simp add: dim_vec_of_onb_enum_list)

lemma list_of_vec_unit_vec:
  defines "basis == canonical_basis::'a::basis_enum list"
  assumes "length basis \<ge> 1"
  shows "list_of_vec (c \<cdot>\<^sub>v
  unit_vec (length basis)
  (length basis-1))!(length basis-1)
   = (c::complex)"
proof-
  (* TODO replace (canonical_basis::'a::basis_enum list) \<rightarrow> basis *)
  have "c \<cdot>\<^sub>v
  unit_vec (length (canonical_basis::'a::basis_enum list)) 
  (length (canonical_basis::'a list)-1)
   = Matrix.vec (length (canonical_basis::'a list))
     (\<lambda>j. if j = length (canonical_basis::'a list)-1 then c
          else 0)"
    unfolding smult_vec_def unit_vec_def mk_vec_def 
    by auto
  hence "list_of_vec (c \<cdot>\<^sub>v
  unit_vec (length (canonical_basis::'a::basis_enum list)) 
  (length (canonical_basis::'a list)-1))
   = list_of_vec (Matrix.vec (length (canonical_basis::'a list))
     (\<lambda>j. if j = length (canonical_basis::'a list)-1 then c
          else 0) )"
    by simp
  hence "list_of_vec (c \<cdot>\<^sub>v
  unit_vec (length (canonical_basis::'a::basis_enum list)) 
  (length (canonical_basis::'a list)-1))!(length (canonical_basis::'a list)-1)
   = list_of_vec (Matrix.vec (length (canonical_basis::'a list))
     (\<lambda>j. if j = length (canonical_basis::'a list)-1 then c
          else 0) )!(length (canonical_basis::'a list)-1)"
    by simp
  also have "\<dots> = c"
  proof-
    have "[0..<length (canonical_basis::'a list)] !
    (length (canonical_basis::'a list) - Suc 0) = 
     length (canonical_basis::'a list) - Suc 0"
      using assms by auto      
    thus ?thesis using assms by auto
  qed
  finally show ?thesis 
    unfolding basis_def
    by auto 
qed

lemma independent_length_leq:
  assumes f1: "complex_vector.independent (set (S::'a list))"
    and f2: "distinct S"
  shows "length S \<le> length (canonical_basis::'a::basis_enum list)"
proof(rule classical)
  have h1: "finite (set S)"
    by simp
  assume "\<not>(length S \<le> length (canonical_basis::'a::basis_enum list))"
  hence "length S > length (canonical_basis::'a::basis_enum list)"
    by simp
  hence g1: "card (set S) > card (set (canonical_basis::'a::basis_enum list))"
    by (simp add: distinct_card f2)
  have "finite (set (canonical_basis::'a::basis_enum list))"
    by simp    
  hence "complex_vector.span (set (canonical_basis::'a::basis_enum list)) = (UNIV:: 'a set)"
    using span_finite_dim is_basis_set unfolding is_basis_def by auto 
  hence g2: "card (set S) > dim (UNIV:: 'a set)"
    using g1 
    by (smt Complex_Vector_Spaces.dependent_raw_def complex_vector.dim_eq_card complex_vector.span_UNIV is_basis_def is_basis_set)
  hence "complex_vector.span (set S) \<subseteq> (UNIV:: 'a set)"
    by simp
  hence "card (set S) \<le> dim (UNIV:: 'a set)"
    using f1 h1 Complex_Vector_Spaces.dependent_raw_def 
      \<open>Complex_Vector_Spaces.span (set canonical_basis) = UNIV\<close>
      \<open>\<not> length S \<le> length canonical_basis\<close> \<open>finite (set canonical_basis)\<close> 
      complex_vector.dim_le_card complex_vector.dim_span_eq_card_independent 
      distinct_canonical_basis distinct_card f2 by smt
  thus ?thesis using g2 by (smt leD)
qed

lemma onb_enum_of_vec_inverse:
  fixes w::"'a::onb_enum"
  shows  "onb_enum_of_vec (vec_of_onb_enum2 w) = w"
  unfolding vec_of_onb_enum2_def onb_enum_of_vec_def onb_enum_of_vec_list_def'
  unfolding list_vec zip_map1 zip_same_conv_map map_map 
  apply (simp add: o_def)
  apply (subst sum.distinct_set_conv_list[symmetric])
   apply simp
  apply (rule complex_vector.sum_representation_eq)
  using is_ob_nonzero is_onb_set is_onb_then_is_ob is_ortho_set_independent is_orthonormal apply auto[1]
  subgoal 
  proof- 
    have "w \<in> closure (Complex_Vector_Spaces.span (set canonical_basis))"
      using is_basis_set unfolding is_basis_def by blast
    moreover have "closure (Complex_Vector_Spaces.span (set (canonical_basis::'a list)))
                 = Complex_Vector_Spaces.span (set (canonical_basis::'a list))"
      by (simp add: span_finite_dim)      
    ultimately show ?thesis by blast
  qed
   apply simp
  by simp

(* NEW *)
lemma uniq_linear_expansion_zero:
  fixes f::"nat \<Rightarrow> complex" 
  defines  "basis == canonical_basis::('a::basis_enum list)"
  assumes h1: "(\<Sum>i = 0 ..< length basis. f i *\<^sub>C (basis!i)) = 0" and 
          h2: "k < length basis"
  shows "f k = 0"
proof-
  define t where "t i = basis!i" for i::nat
  have "inj_on t {0..<length basis}"
    unfolding basis_def using distinct_canonical_basis
    by (simp add: basis_def inj_on_def nth_eq_iff_index_eq t_def) 
  define s where "s = the_inv_into {0..<length basis} t"
  have "inj_on s (set basis)"
    sorry
  define F where "F b = f (s b)" for b
  have "(\<Sum>i = 0 ..< length basis. f i *\<^sub>C (basis!i)) = (\<Sum>b \<in> set basis. F b *\<^sub>C b)"
    sorry
  hence "(\<Sum>b \<in> set basis. F b *\<^sub>C b) = 0"
    sorry
  hence "b \<in> (set basis) \<Longrightarrow> F b = 0" for b
  proof-
    have "complex_vector.independent (set basis)"
      unfolding basis_def using is_basis_set unfolding is_basis_def by blast
    thus ?thesis using complex_vector.independentD[where s = "set basis" and t = "set basis" 
          and u = F and v = b]  sorry      
  qed
  hence "F (basis!k) = 0"
    by (simp add: h2)    
  moreover have "s (basis!k) = k"
    using \<open>inj_on t {0..<length basis}\<close> \<open>t \<equiv> (!) basis\<close> atLeastLessThan_iff h2 s_def 
      the_inv_into_f_f by fastforce    
  ultimately show ?thesis unfolding F_def by simp
qed

(* NEW *)
lemma uniq_linear_expansion:
  fixes f g::"nat \<Rightarrow> complex" 
  defines  "basis == canonical_basis::('a::basis_enum list)"
  assumes h1: "(\<Sum>i = 0 ..< length basis. f i *\<^sub>C (basis!i))
             = (\<Sum>i = 0..< length basis. g i *\<^sub>C (basis!i))" and 
          h2: "k < length basis"
  shows "f k = g k"
proof-
  have "0 = (\<Sum>i = 0 ..< length basis. f i *\<^sub>C (basis!i))
      - (\<Sum>i = 0..< length basis. g i *\<^sub>C (basis!i))"
    by (simp add: h1)
  also have "\<dots> = (\<Sum>i = 0 ..< length basis. f i *\<^sub>C (basis!i) -  g i *\<^sub>C (basis!i))"
    by (metis (no_types, lifting) sum.cong sum_subtractf)
  also have "\<dots> = (\<Sum>i = 0 ..< length basis. (f i - g i) *\<^sub>C (basis!i))"
    by (simp add: complex_vector.scale_left_diff_distrib)
  finally have "0 = (\<Sum>i = 0 ..< length basis. (f i - g i) *\<^sub>C (basis!i))" .
  hence "(\<Sum>i = 0 ..< length basis. (f i - g i) *\<^sub>C (basis!i)) = 0"
    by simp
  moreover have "complex_vector.independent (set basis)"
    using is_basis_set unfolding is_basis_def basis_def by blast 
  ultimately show ?thesis 
    using uniq_linear_expansion_zero[where f = "\<lambda>i. f i - g i"]
     basis_def eq_iff_diff_eq_0 h2 by blast    
qed

lemma vec_of_onb_enum_inverse[simp]:
  fixes v::"complex vec"
  assumes f1: "dim_vec v = canonical_basis_length TYPE('a::onb_enum)"
  shows "vec_of_onb_enum2 ((onb_enum_of_vec v)::'a) = v"
proof-
  define w where "w = list_of_vec v"
  define basis where "basis = (canonical_basis::'a list)"
  have length_w: "length w = dim_vec v"
    using f1 unfolding w_def
    by simp 
  hence length_basis: "length basis = length w"
    by (simp add: basis_def canonical_basis_length_eq f1)    
  have "map (complex_vector.representation (set basis) (onb_enum_of_vec_list basis w)) basis = w"
  proof-
    have "i < length basis \<Longrightarrow> 
        complex_vector.representation (set basis) (onb_enum_of_vec_list basis w) (basis!i) = w!i"
      for i
    proof-
      assume h1: "i < length basis"
      have h2: "complex_independent (set basis)"
        using basis_def canonical_basis_non_zero is_ortho_set_independent is_orthonormal by blast        
      have h3: "onb_enum_of_vec_list basis w \<in> Complex_Vector_Spaces.span (set basis)"
      proof-
        have "Complex_Vector_Spaces.span (set basis) = 
              closure (Complex_Vector_Spaces.span (set basis))"
          by (simp add: span_finite_dim)          
        thus ?thesis 
          using  is_basis_set unfolding is_basis_def basis_def 
          by blast 
      qed
      define f where 
        "f x = complex_vector.representation (set basis) (onb_enum_of_vec_list basis w) x"
      for x
      have h4: "f x \<noteq> 0 \<Longrightarrow> x \<in> set basis" for x
        using is_basis_set complex_vector.representation_def
        unfolding f_def
        by (simp add: complex_vector.representation_ne_zero)        
      have h5: "finite {v. f v \<noteq> 0}"
        using is_basis_set complex_vector.representation_def
        unfolding f_def
        using complex_vector.finite_representation by force        
      have h6: "(\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = onb_enum_of_vec_list basis w"
        using is_basis_set complex_vector.representation_def 
        by (smt Collect_cong \<open>f \<equiv> Complex_Vector_Spaces.representation (set basis) 
        (onb_enum_of_vec_list basis w)\<close> complex_vector.sum_nonzero_representation_eq h2 h3 sum.cong) 

      have h7: "distinct basis"
        by (simp add: basis_def)
      have "(\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = (\<Sum>v\<in>set basis. f v *\<^sub>C v)"
        by (simp add: h4 subset_eq sum.mono_neutral_cong_left)
      also have "\<dots> = sum_list (map (\<lambda>x. f x *\<^sub>C x) basis)"
        using Groups_List.monoid_add_class.sum_list_distinct_conv_sum_set
        by (simp add: sum_list_distinct_conv_sum_set h7)        
      also have "\<dots> = (\<Sum>i = 0..< length basis. f (basis!i) *\<^sub>C (basis!i))"
        by (metis (mono_tags, lifting) list_sum_function sum.cong)        
      finally have "(\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = (\<Sum>i = 0..< length basis. f (basis!i) *\<^sub>C (basis!i))"
        by auto
      hence "(\<Sum>i = 0..< length basis. f (basis!i) *\<^sub>C (basis!i)) = onb_enum_of_vec_list basis w"
        by (simp add: h6) 
      also have "onb_enum_of_vec_list basis w = (\<Sum>i = 0..<length basis. (w!i) *\<^sub>C (basis!i))"
        using Bounded_Operators_Code.onb_enum_of_vec_expansion[where S = basis and L = w]
          length_basis
        using h7 by blast 
      finally have "(\<Sum>i = 0..<length basis. f (basis!i) *\<^sub>C (basis!i))
                  = (\<Sum>i = 0..<length basis. (w!i) *\<^sub>C (basis!i))"
        by blast
      hence "f (basis!i) = w!i"
        using uniq_linear_expansion[where f = "\<lambda>i. f (basis ! i)" and g = "\<lambda>i. w!i"]
          basis_def h1 by blast
      thus ?thesis unfolding f_def.
    qed
    thus ?thesis 
      by (smt basis_def canonical_basis_length_eq f1 length_map length_w nth_equalityI nth_map)
  qed
  thus ?thesis
    unfolding basis_def
    by (simp add: onb_enum_of_vec_def vec_list vec_of_onb_enum2_def w_def)    
qed

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

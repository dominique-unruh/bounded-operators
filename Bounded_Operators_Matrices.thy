theory Bounded_Operators_Matrices
  imports Complex_L2 Jordan_Normal_Form.Matrix 
begin

subsection\<open>\<open>Jordan_Normal_Form_Notation\<close> -- Cleaning up syntax from \<^session>\<open>Jordan_Normal_Form\<close>\<close>

text \<open>\<^const>\<open>Finite_Cartesian_Product.vec_nth\<close> collides with the notation from \<^session>\<open>Jordan_Normal_Form\<close>\<close>
no_notation vec_nth (infixl "$" 90)


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
unbundle cblinfun_notation


subsection \<open>Setting up code generation for type cblinfun\<close>

text \<open>We define the canonical isomorphism between \<^typ>\<open>'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum\<close>
  and the complex \<^term>\<open>n*m\<close>-matrices (where n,m are the dimensions of 'a,'b, 
  respectively). This is possible if \<^typ>\<open>'a\<close>, \<^typ>\<open>'b\<close> are of class \<^class>\<open>onb_enum\<close>
  since that class fixes a finite canonical basis. Matrices are represented using
  the \<^typ>\<open>_ mat\<close> type from \<^session>\<open>Jordan_Normal_Form\<close>.\<close>
  (* TODO: Define (canonical isomorphism). *)
  (* Jose: More details please *)

primrec vec_of_onb_enum_list :: \<open>'a list \<Rightarrow> 'a::onb_enum \<Rightarrow> nat \<Rightarrow> complex vec\<close> where
  \<open>vec_of_onb_enum_list [] v _ = 0\<^sub>v (length (canonical_basis::'a list))\<close> |
  \<open>vec_of_onb_enum_list (x#ys) v i = vec_of_onb_enum_list ys v (Suc i) +
    \<langle>x, v\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) i\<close>


definition vec_of_onb_enum :: \<open>'a::onb_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_onb_enum v = vec_of_list (map (complex_vector.representation (set canonical_basis) v) canonical_basis)\<close>

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
      fix x y::'a
      assume o1: "x \<in> set L" and o2: "y \<in> set L" and o3: "x \<noteq> y" 
      have "x \<in> set (a#L)"
        by (simp add: o1)        
      moreover have "y \<in> set (a#L)"
        by (simp add: o2)
      ultimately show "\<langle>x, y\<rangle> = 0"
        using o3 Cons.prems(3) is_ortho_set_def by blast 
    qed
    moreover have "\<forall>a\<in>set L. \<parallel>a\<parallel> = 1"
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

lemma onb_enum_of_vec_expansion:  
  fixes S::"'a::onb_enum list" and L::"complex list"
  assumes "length S = length L" and "distinct S"
  shows   "sum_list (map2 (\<lambda>l s. l *\<^sub>C s) L S)
             = (\<Sum>i\<in>{0..<length S}. L!i *\<^sub>C S!i)"
  using assms sum_list_sum_nth[where xs = "map2 (*\<^sub>C) L S"]
  by auto

lemma length_list_of_vec_vec_of_onb_enum_list:
  fixes w::"'a::onb_enum" and S::"'a list"
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
    using span_finite_dim is_basis_set unfolding is_basis_def basis_def by auto 
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

lemma onb_enum_of_vec_inverse:
  fixes w::"'a::onb_enum"
  shows  "onb_enum_of_vec (vec_of_onb_enum w) = w"
  unfolding vec_of_onb_enum_def onb_enum_of_vec_def onb_enum_of_vec_list_def'
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


lemma uniq_linear_expansion_sum_list_zero:
  fixes f::"'a::basis_enum \<Rightarrow> complex"
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
      using is_basis_set unfolding basis_def is_basis_def
      by blast       
    ultimately show ?thesis 
      by (metis Complex_Vector_Spaces.dependent_raw_def)
  qed
  moreover have "b \<noteq> 0"
    using h1 is_basis_set unfolding basis_def is_basis_def
    using assms Complex_Vector_Spaces.complex_vector.dependent_zero
    by (metis Complex_Vector_Spaces.dependent_raw_def)
  ultimately have "(-f b) = 0"
    by simp
  thus ?thesis by simp
qed


lemma uniq_linear_expansion_sum_list:
  fixes f g::"'a::basis_enum \<Rightarrow> complex"
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
  finally have "0 = sum_list (map2 (*\<^sub>C) (map (\<lambda>x. f x - g x) basis) basis)"
    .
  hence "sum_list (map2 (*\<^sub>C) (map (\<lambda>x. f x - g x) basis) basis) = 0"
    by simp
  hence "(\<lambda>x. f x - g x) b = 0"
    using uniq_linear_expansion_sum_list_zero[where f = "(\<lambda>x. f x - g x)"]
      basis_def h1 by blast
  thus ?thesis by simp
qed


lemma vec_of_onb_enum_inverse[simp]:
  fixes v::"complex vec"
  defines "n == canonical_basis_length TYPE('a::onb_enum)"
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
        using basis_def h1 nth_mem uniq_linear_expansion_sum_list by blast        
      hence "f (basis!i) = w!i"
        using e1 f1 h1 length_basis length_w by auto        
      thus ?thesis unfolding f_def.
    qed
    thus ?thesis 
      by (smt length_basis length_map nth_equalityI nth_map)
  qed
  thus ?thesis
    unfolding basis_def
    by (simp add: onb_enum_of_vec_def vec_list vec_of_onb_enum_def w_def)    
qed

lemma vec_of_onb_enum_add:
  "vec_of_onb_enum (b1 + b2) = vec_of_onb_enum b1 + vec_of_onb_enum b2"
proof-
  have "Complex_Vector_Spaces.span
         (set (canonical_basis::'a list)) = UNIV"
    using is_basis_set unfolding is_basis_def
    using span_finite_dim by auto 
  hence "Complex_Vector_Spaces.representation (set (canonical_basis::'a list)) (b1+b2) i
      = Complex_Vector_Spaces.representation (set (canonical_basis::'a list)) b1 i + 
        Complex_Vector_Spaces.representation (set (canonical_basis::'a list)) b2 i" for i
    using Complex_Vector_Spaces.complex_vector.representation_add[where basis = "set (canonical_basis::'a list)"]
    by (smt canonical_basis_non_zero is_ortho_set_independent is_orthonormal iso_tuple_UNIV_I)  
  moreover have "vec_of_list (map (\<lambda>x. f x + g x) S) = vec_of_list (map f S) + vec_of_list (map g S)"
    for S::"'a list" and f g::"'a \<Rightarrow> complex" 
  proof(induction S)
    case Nil
    then show ?case by auto
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
    using is_basis_set unfolding is_basis_def
    using span_finite_dim by auto 
  hence "Complex_Vector_Spaces.representation (set (canonical_basis::'a list)) (c *\<^sub>C b) i
      = c *\<^sub>C (Complex_Vector_Spaces.representation (set (canonical_basis::'a list)) b i)" for i
    using Complex_Vector_Spaces.complex_vector.representation_scale
    by (smt UNIV_I canonical_basis_non_zero complex_scaleC_def is_ortho_set_independent is_orthonormal)
  moreover have "vec_of_list (map (\<lambda>x. c *\<^sub>C (f x)) S) = c \<cdot>\<^sub>v vec_of_list (map f S)"
    for S::"'a list" and f g::"'a \<Rightarrow> complex" 
  proof(induction S)
    case Nil
    then show ?case by auto
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


lemma onb_enum_of_vec_unit_vec:
  defines a1: "basis == (canonical_basis::'a::onb_enum list)"
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
          less_imp_le not_gr_zero by auto                
      ultimately show ?thesis
        using \<open>a \<equiv> \<lambda>j. list_of_vec (unit_vec n i) ! j *\<^sub>C basis ! j\<close> by auto 
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
      by (metis Cons.IH Cons.prems(1) Cons.prems(2) distinct_length_2_or_more is_ortho_set_def 
          list.set_intros(1) list.set_intros(2) set_ConsD)    
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

lemma cinner_onb_enum_of_vec:
  defines "n == canonical_basis_length TYPE('a::onb_enum)"
  assumes w1: "dim_vec x = n" and w2: "dim_vec y = n"
  shows  "\<langle>(onb_enum_of_vec::_\<Rightarrow> 'a) x, (onb_enum_of_vec::_\<Rightarrow> 'a) y\<rangle>
           = y \<bullet>c x"
proof-
  define B where "B = (canonical_basis::'a list)"
  have a0: "\<langle>onb_enum_of_vec_list B xs, onb_enum_of_vec_list B ys\<rangle> = 
    sum_list (map2 (\<lambda>x y. cnj x * y) xs ys)"
    if "length xs = length ys" and "length ys = length B" 
      and "is_onb (set B)" and "distinct B"
    for xs ys and B :: "'a list"
    unfolding onb_enum_of_vec_list_def'
    using that
  proof (induction xs ys B rule:list_induct3)
    case Nil then show ?case by auto
  next
    case (Cons x xs y ys b B)
    have w1: "distinct B"
      using Cons.prems(2) by auto
    have "length xs = length B"
      by (simp add: Cons.hyps(1) Cons.hyps(2))
    moreover have "b \<notin> set B"
      using Cons.prems(2) by auto
    moreover have "is_ortho_set (set (b#B))"
      using Cons.prems(1) unfolding is_onb_def is_ob_def
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
        by (meson Cons.prems(2) \<open>b' \<noteq> b\<close> is_ob_def is_onb_then_is_ob is_ortho_set_def 
            list.set_intros(1) list.set_intros(2))        
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
      using Cons.prems(2) by auto
    moreover have "is_ortho_set (set (b#B))"
      using Cons.prems(1) unfolding is_onb_def is_ob_def
      by simp
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
        by (meson Cons.prems(2) \<open>b' \<noteq> b\<close> is_ob_def is_onb_then_is_ob is_ortho_set_def 
            list.set_intros(1) list.set_intros(2))        
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
      have "is_onb (set (b#B))"
        using Cons.prems(1) by auto
      hence "b \<in> sphere (0::'a) 1"
        unfolding is_onb_def
        by simp
      hence "norm b = 1"
        by simp        
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
        using Cons.prems(1) is_ob_def is_onb_delete is_onb_then_is_ob apply auto[1]
        using w1 apply auto[1]
        using Cons.prems(1) dual_order.trans is_onb_def by auto        
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
      apply (simp add: B_def is_onb_set)
     apply (simp add: B_def)
    by (simp add: a2)
  thus ?thesis
    unfolding scalar_prod_def apply auto
    by (metis (no_types, lifting) B_def onb_enum_of_vec_def semiring_normalization_rules(7) sum.cong)        
qed


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
          unfolding f_def 
          using onb_enum_of_vec_add[where ?v1.0 = "M *\<^sub>v vec_of_onb_enum b1" 
              and ?v2.0 = "M *\<^sub>v vec_of_onb_enum b2"]
          by (simp add: \<open>\<lbrakk>dim_vec (M *\<^sub>v vec_of_onb_enum b1) = length canonical_basis; 
            dim_vec (M *\<^sub>v vec_of_onb_enum b2) = length canonical_basis\<rbrakk>
        \<Longrightarrow> onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum b1 + M *\<^sub>v vec_of_onb_enum b2) 
          = onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum b1) + onb_enum_of_vec (M *\<^sub>v vec_of_onb_enum b2)\<close> 
              canonical_basis_length_eq m_def)          
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
        thus ?thesis 
          unfolding f_def
          by (smt True calculation m_def n_def onb_enum_of_vec_inverse 
              vec_of_onb_enum_inverse vec_of_onb_enum_scaleC)
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

definition mat_of_cblinfun :: \<open>'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum \<Rightarrow> complex mat\<close> where
  \<open>mat_of_cblinfun f = 
    mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a)) (
    \<lambda> (i, j). \<langle> (canonical_basis::'b list)!i, f *\<^sub>V ((canonical_basis::'a list)!j) \<rangle> )\<close>
for f


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

(* TODO: move to "missing" theory (for Jordan_Normal_Form) *)
lemma mat_entry_explicit:
  fixes M :: "complex mat"
  assumes "M \<in> carrier_mat m n" and "i < m" and "j < n"
  shows   "vec_index (M *\<^sub>v unit_vec n j) i = M $$ (i,j)"
proof-
  have dim_col1: "dim_col M = n"
    using assms(1) by blast
  have dim_vec1: "dim_vec (unit_vec n j) = n"
    by simp
  have "vec_index (M *\<^sub>v unit_vec n j) i = scalar_prod (row M i) (unit_vec n j)"
    using assms(1) assms(2) by auto
  also have "\<dots> = scalar_prod (vec n (\<lambda>j. M $$ (i, j))) (unit_vec n j)"
    unfolding row_def using dim_col1 by simp 
  also have "\<dots> = (\<Sum>k\<in>{0..<n}. vec_index (vec n (\<lambda>j. M $$ (i, j))) k * vec_index (unit_vec n j) k)"
    unfolding scalar_prod_def using dim_vec1 by auto
  also have "\<dots> = vec_index (vec n (\<lambda>j. M $$ (i, j))) j * vec_index (unit_vec n j) j
           + (\<Sum>k\<in>{0..<n}-{j}. vec_index (vec n (\<lambda>j. M $$ (i, j))) k * vec_index (unit_vec n j) k)"
  proof-
    have "j\<in>{0..<n}"
      by (simp add: assms(3))
    thus ?thesis 
      by (simp add: sum.remove)
  qed
  also have "\<dots> = vec_index (vec n (\<lambda>j. M $$ (i, j))) j * vec_index (unit_vec n j) j"
  proof-
    have "vec_index (vec n (\<lambda>j. M $$ (i, j))) k * vec_index (unit_vec n j) k = 0"
      if "k \<in>{0..<n}-{j}"
      for k
    proof-
      have "vec_index (unit_vec n j) k = 0"
        using that
        by (simp add: assms(3)) 
      thus ?thesis
        by (simp add: \<open>vec_index (unit_vec n j) k = 0\<close>) 
    qed
    hence "(\<Sum>k\<in>{0..<n}-{j}. vec_index (vec n (\<lambda>j. M $$ (i, j))) k * vec_index (unit_vec n j) k) = 0"
      using sum_not_0 by blast      
    thus ?thesis by simp
  qed
  also have "\<dots> = vec_index (vec n (\<lambda>j. M $$ (i, j))) j"
  proof-
    have "vec_index (unit_vec n j) j = 1"
      by (simp add: assms(3))      
    thus ?thesis
      by auto 
  qed
  also have "\<dots> = M $$ (i, j)"
    by (simp add: assms(3))
  finally show ?thesis by simp
qed

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
             r \<cdot>\<^sub>v (mat_of_cblinfun F *\<^sub>v vec_of_onb_enum b)"
        .
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
      by (smt BasisA_def basisA_def is_basis_def is_basis_set)
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
  moreover have "length (list_of_vec v) = nB"
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
        using is_onb_set 
        unfolding BasisB_def is_onb_def is_ob_def is_ortho_set_def
        by blast        
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
    hence "BasisB!iB \<in> sphere (0::'b) 1"
      using is_onb_set BasisB_def unfolding is_onb_def by blast
    hence "norm (BasisB!iB) = 1"
      by simp
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
    using BasisB_def by auto    
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

declare mat_of_cblinfun_inverse [code abstype]

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
        using is_onb_set 
        unfolding Basis_def is_onb_def
        by (simp add: is_normal) 
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
        using is_onb_set
        unfolding is_onb_def is_ob_def is_ortho_set_def Basis_def by blast
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
    and "nA = canonical_basis_length TYPE('a)" 
    and "nB = canonical_basis_length TYPE('b)"
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


lemma cinner_vec_of_onb_enum:
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
qed

(* TODO Move to JNF Missing *)
definition "adjoint_mat M = transpose_mat (map_mat cnj M)"

(* TODO: Move to JNF Missing *)
lemma adjoint_mat_swap:
  fixes M ::"complex mat"
  assumes "M \<in> carrier_mat nB nA" and "iA < dim_row M" and "iB < dim_col M"
  shows "(adjoint_mat M)$$(iB,iA) = cnj (M$$(iA,iB))"
  unfolding adjoint_mat_def transpose_mat_def map_mat_def
  by (simp add: assms(2) assms(3))

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

(* TODO: Move to JNF Missing theory *)
lemma cscalar_prod_adjoint:
  fixes M:: "complex mat"
  assumes a1: "M \<in> carrier_mat nB nA" 
    and a2: "dim_vec v = nA"
    and a3: "dim_vec u = nB"
  shows "v \<bullet>c ((adjoint_mat M) *\<^sub>v u) = (M *\<^sub>v v) \<bullet>c u"
proof-
  define N where "N = adjoint_mat M"
  have b1: "N \<in> carrier_mat nA nB"
    unfolding N_def
    using a1 unfolding adjoint_mat_def by simp
  hence b2: "dim_vec (N *\<^sub>v u) = nA"    
    using a3 dim_mult_mat_vec by blast
  hence b3: "dim_vec (conjugate (N *\<^sub>v u)) = nA"
    by simp
  have b4: " (conjugate v) $ i = cnj (vec_index v i)"
    if "i < nA"
    for i
    using a2 that by auto
  have b5: "(Matrix.row N) i = (Matrix.col (map_mat cnj M)) i"
    if "i < nA"
    for i
    unfolding N_def adjoint_mat_def
    using row_transpose a1 that by auto    
  have b6: "vec_index (N *\<^sub>v u) i = cnj (scalar_prod ( (Matrix.col M) i ) (conjugate u))"
    if "i < nA"
    for i
  proof-
    have "vec_index (N *\<^sub>v u) i = scalar_prod ((Matrix.row N) i) u"
      using Matrix.index_mult_mat_vec
      using b1 that by auto
    also have "\<dots> = scalar_prod ((Matrix.col (map_mat cnj M)) i) u"
      by (simp add: b5 that)
    also have "\<dots> = scalar_prod ( conjugate ((Matrix.col M) i) ) u"
      by (smt a1 carrier_matD(2) col_map_mat conjugate_complex_def dim_col dim_vec_conjugate eq_vecI 
          index_map_mat(2) index_map_vec(1) that vec_index_conjugate)
    also have "\<dots> = cnj (scalar_prod ( (Matrix.col M) i ) (conjugate u))"
      by (metis a1 a3 carrier_matD(1) carrier_vec_dim_vec col_dim complex_cnj_cnj 
          conjugate_complex_def conjugate_conjugate_sprod)
    finally show ?thesis .
  qed    
  have b7: "dim_vec (conjugate u) = nB"
    by (simp add: a3)
  have b8: "vec_index (conjugate u) j = cnj (vec_index u j)"
    if "j < nB"
    for j
    by (simp add: a3 that)    
  have b9: "scalar_prod ( (Matrix.col M) i ) (conjugate u) = 
      (\<Sum>j=0..< nB.  vec_index ( (Matrix.col M) i ) j * cnj (vec_index u j) )"
    if "i < nA"
    for i
    unfolding scalar_prod_def
    using b7 b8 by auto
  have b10: "vec_index (M *\<^sub>v v) j = 
      (\<Sum>i=0..<nA.  
      vec_index ( (Matrix.col M) i ) j  * (vec_index v i) )"
    if "j < nB"
    for j
  proof-
    have "vec_index ( (Matrix.col M) i ) j = vec_index ( (Matrix.row M) j ) i"
      if "i < nA"
      for i
      unfolding col_def row_def
      using \<open>j < nB\<close> a1 that by auto 
    moreover have "vec_index (M *\<^sub>v v) j = 
      (\<Sum>i=0..<nA.  
      vec_index ( (Matrix.row M) j ) i  * (vec_index v i) )"
      unfolding mult_mat_vec_def scalar_prod_def using a2 a1 index_vec that by blast
    ultimately show ?thesis by simp
  qed
  have "v \<bullet>c ((adjoint_mat M) *\<^sub>v u) = cnj ((N *\<^sub>v u) \<bullet>c v)"
    by (metis N_def a2 b2 carrier_vec_dim_vec conjugate_complex_def conjugate_conjugate_sprod 
        conjugate_vec_sprod_comm)    
  also have "\<dots> = cnj (\<Sum>i = 0..<nA.
            vec_index (N *\<^sub>v u) i * vec_index (conjugate v) i)"
    unfolding scalar_prod_def
    by (simp add: a2)    
  also have "\<dots> = cnj (\<Sum>i = 0..<nA.
            vec_index (N *\<^sub>v u) i * cnj (vec_index v i))"
    using b4 by simp
  also have "\<dots> = (\<Sum>i = 0..<nA.
            (cnj (vec_index (N *\<^sub>v u) i)) * (vec_index v i))"
    by auto
  also have "\<dots> = (\<Sum>i = 0..<nA.
            (cnj (cnj (scalar_prod ( (Matrix.col M) i ) (conjugate u)))) * (vec_index v i))"
    using b6 by auto
  also have "\<dots> = (\<Sum>i = 0..<nA.
            (scalar_prod ( (Matrix.col M) i ) (conjugate u)) * (vec_index v i))"
    by simp
  also have "\<dots> = (\<Sum>i = 0..<nA.
                  (\<Sum>j=0..< nB.  
      vec_index ( (Matrix.col M) i ) j * cnj (vec_index u j) ) * (vec_index v i))"
    using b9 by simp
  also have "\<dots> = (\<Sum>i=0..<nA.
                  (\<Sum>j=0..< nB.  
      vec_index ( (Matrix.col M) i ) j * cnj (vec_index u j) * (vec_index v i) ))"
    by (simp add: vector_space_over_itself.scale_sum_left)
  also have "\<dots> = (\<Sum>i=0..<nA.
                  (\<Sum>j=0..<nB.  
      vec_index ( (Matrix.col M) i ) j  * (vec_index v i) * cnj (vec_index u j) ))"
    by (smt conjugate_complex_def mult.commute sum.cong vector_space_over_itself.scale_scale)
  also have "\<dots> = (\<Sum>j=0..<nB.
                  (\<Sum>i=0..<nA.  
      vec_index ( (Matrix.col M) i ) j  * (vec_index v i) * cnj (vec_index u j) ))"
    using sum.swap by auto
  also have "\<dots> = (\<Sum>j=0..<nB.
                  (\<Sum>i=0..<nA.  
      vec_index ( (Matrix.col M) i ) j  * (vec_index v i) ) * cnj (vec_index u j) )"
    by (simp add: vector_space_over_itself.scale_sum_left)
  also have "\<dots> = (\<Sum>j\<in>{0..<nB}. vec_index (M *\<^sub>v v) j * cnj (vec_index u j))"
    using b10 by simp
  also have "\<dots> = (M *\<^sub>v v) \<bullet>c u"
    unfolding scalar_prod_def using a3 by auto
  finally show ?thesis .
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
      by (simp add: cinner_vec_of_onb_enum)      
  qed
qed


lemma cinner_square_canonical_basis: 
  defines "BasisA == (canonical_basis:: ('a::onb_enum list))"
    and "n == canonical_basis_length TYPE('a)"
  assumes a1: "i < n"
  shows "\<langle>BasisA!i, BasisA!i\<rangle> = 1"
proof-
  have "set BasisA \<subseteq> sphere 0 1"
    using is_onb_set unfolding BasisA_def is_onb_def by blast
  moreover have "BasisA!i \<in> set BasisA"
    using a1 unfolding n_def BasisA_def
    by (simp add: canonical_basis_length_eq) 
  ultimately have "norm (BasisA!i) = 1"
    by auto
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


unbundle no_jnf_notation
unbundle no_cblinfun_notation


end

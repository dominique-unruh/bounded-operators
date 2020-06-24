section \<open>\<open>Bounded_Operators_Code\<close> -- Support for code generation\<close>

theory Bounded_Operators_Code
  imports
    Complex_L2 Jordan_Normal_Form.Matrix 
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
unbundle cblinfun_notation

subsection \<open>Setting up code generation for type cblinfun\<close>

text \<open>We define the canonical isomorphism between \<^typ>\<open>('a::onb_enum,'b::onb_enum) cblinfun\<close>
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

(*
definition vec_of_onb_enum :: \<open>'a::onb_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_onb_enum v = vec_of_onb_enum_list (canonical_basis::'a list) v 0\<close>
*)

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

(* NEW *)
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

(* NEW *)
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
        have "i < Suc n \<Longrightarrow> vec_index (vCons (p + q) (A + B)) i = vec_index (vCons p A + vCons q B) i"
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

(* TODO: move this lemma near "is_ortho_set_def" *)
lemma is_onb_delete:
  assumes "is_ortho_set (insert x B)"
  shows "is_ortho_set B"
  using assms
  unfolding  is_ortho_set_def
  by blast

(* TODO: put inside other lemma *)
lemma is_ortho_setsum_list_map2_zero:
  assumes "length ys = length B"
    and "is_ortho_set (set (b#B))"
    and "distinct (b#B)"
  shows "\<langle>b, sum_list (map2 (*\<^sub>C) ys B)\<rangle> = 0"
  using assms proof(induction ys B rule: list_induct2)
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


lemma sum_list_orthonormal:
  assumes  "length xs = length ys"
    and "length ys = length B" 
    and "is_ortho_set (set B)"
    and "distinct B"
    and "set B \<subseteq> sphere 0 1"
  shows "\<langle>sum_list (map2 (*\<^sub>C) xs B), 
          sum_list (map2 (*\<^sub>C) ys B)\<rangle> =
      sum_list (map2 (\<lambda>x. (*) (cnj x)) xs ys)"
  using assms proof(induction xs ys B rule: list_induct3)
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
      using Cons.hyps(2) Cons.prems(1) Cons.prems(2) is_ortho_setsum_list_map2_zero by auto
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


(* NEW *)
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

(* NEW *)
(* TODO: move to ell2 *)
lemma ell2_norm_cinner:
  fixes a b :: "'a \<Rightarrow> complex" and X :: "'a set"
  assumes h1: "finite X"
  defines "x == (\<Sum>t\<in>X. a t *\<^sub>C ket t)" and "y == (\<Sum>t\<in>X. b t *\<^sub>C ket t)"
  shows "\<langle>x, y\<rangle> = (\<Sum>t\<in>X. (cnj (a t)) * b t)"
proof-
  have "\<langle>x, y\<rangle> = \<langle>(\<Sum>t\<in>X. a t *\<^sub>C ket t), (\<Sum>s\<in>X. b s *\<^sub>C ket s)\<rangle>"
    unfolding x_def y_def by blast
  also have "\<dots> = (\<Sum>t\<in>X. \<langle>a t *\<^sub>C ket t, (\<Sum>s\<in>X. b s *\<^sub>C ket s)\<rangle>)"
    using cinner_sum_left by blast
  also have "\<dots> = (\<Sum>t\<in>X. (\<Sum>s\<in>X. \<langle>a t *\<^sub>C ket t, b s *\<^sub>C ket s\<rangle>))"
    by (simp add: cinner_sum_right)
  also have "\<dots> = (\<Sum>t\<in>X. (\<Sum>s\<in>X. (cnj (a t)) * \<langle>ket t, b s *\<^sub>C ket s\<rangle>))"
    by (meson cinner_scaleC_left sum.cong)
  also have "\<dots> = (\<Sum>t\<in>X. (\<Sum>s\<in>X. (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle>))"
    by (metis (mono_tags, lifting) cinner_scaleC_right sum.cong vector_space_over_itself.scale_scale)
  also have "\<dots> = (\<Sum>t\<in>X. (cnj (a t)) * b t * \<langle>ket t, ket t\<rangle> + (\<Sum>s\<in>X-{t}. (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle>))"
  proof-
    have "t\<in>X \<Longrightarrow> (\<Sum>s\<in>X. (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle>) = (cnj (a t)) * b t * \<langle>ket t, ket t\<rangle> + (\<Sum>s\<in>X-{t}. (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle>)"
      for t
      using h1 Groups_Big.comm_monoid_add_class.sum.remove
      by (simp add: sum.remove)
    thus ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>t\<in>X. (cnj (a t)) * b t * \<langle>ket t, ket t\<rangle>)"
  proof-
    have "s\<in>X-{t} \<Longrightarrow> (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle> = 0"
      for s t
      by (metis DiffD2 ket_Kronecker_delta_neq mult_not_zero singletonI) 
    hence "(\<Sum>s\<in>X-{t}. (cnj (a t)) * b s * \<langle>ket t, ket s\<rangle>) = 0" for t
      by (simp add: \<open>\<And>t s. s \<in> X - {t} \<Longrightarrow> cnj (a t) * b s * \<langle>ket t, ket s\<rangle> = 0\<close>)      
    thus ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>t\<in>X. (cnj (a t)) * b t)"
  proof-
    have "\<langle>ket t, ket t\<rangle> = 1" for t::'a
      by (simp add: ket_Kronecker_delta_eq)      
    thus ?thesis
      by auto 
  qed
  finally show ?thesis .
qed

(* NEW *)
lemma ell2_norm_list:
  fixes a :: "'a \<Rightarrow> complex" and X :: "'a set"
  assumes h1: "finite X"
  defines "x == (\<Sum>t\<in>X. a t *\<^sub>C ket t)"
  shows "norm x = sqrt (\<Sum>t\<in>X. (norm (a t))\<^sup>2)"
proof-
  have "(norm x)^2 = \<langle>x, x\<rangle>"
    using power2_norm_eq_cinner' by auto
  also have "\<dots> = (\<Sum>t\<in>X. (cnj (a t)) * (a t))"   
    using h1 ell2_norm_cinner[where X = X and a = a and b = a]
    using x_def by blast    
  also have "\<dots> = (\<Sum>t\<in>X. (norm (a t))\<^sup>2)"   
  proof-
    have "(cnj (a t)) * (a t) = (norm (a t))\<^sup>2" for t
      using complex_norm_square by auto      
    thus ?thesis by simp
  qed
  finally have "(norm x)^2 = (\<Sum>t\<in>X. (norm (a t))\<^sup>2)"
    using of_real_eq_iff by blast    
  thus ?thesis
    by (metis abs_norm_cancel real_sqrt_abs) 
qed

(* NEW *)
lemma Cauchy_Schwarz_complex:
  fixes a b :: "'a \<Rightarrow> complex"
  assumes h1: "finite X"
  shows "norm (\<Sum>t\<in>X. (cnj (a t)) * b t) \<le> sqrt (\<Sum>t\<in>X. (norm (a t))\<^sup>2) * sqrt (\<Sum>t\<in>X. (norm (b t))\<^sup>2)"
proof-
  define x where "x = (\<Sum>t\<in>X. a t *\<^sub>C ket t)"
  define y where "y = (\<Sum>t\<in>X. b t *\<^sub>C ket t)"
  have "\<langle>x, y\<rangle> = (\<Sum>t\<in>X. (cnj (a t)) * b t)"
    using h1 ell2_norm_cinner[where X = X and a = a and b = b]
     x_def y_def by blast    
  hence "norm \<langle>x, y\<rangle> = norm (\<Sum>t\<in>X. (cnj (a t)) * b t)"
    by simp
  moreover have "norm x = sqrt (\<Sum>t\<in>X. (norm (a t))\<^sup>2)"
    using h1 ell2_norm_list[where X = X and a = a]
     x_def by blast        
  moreover have "norm y = sqrt (\<Sum>t\<in>X. (norm (b t))\<^sup>2)"
    using h1 ell2_norm_list[where X = X and a = b]
      y_def by blast        
  moreover have "norm \<langle>x, y\<rangle> \<le> norm x * norm y"
    by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)    
  ultimately show ?thesis by simp
qed


(* NEW *)
lemma Cauchy_Schwarz_real:
  fixes a b :: "'a \<Rightarrow> real"
  assumes "finite X"
  shows "norm (\<Sum>t\<in>X. a t * b t) \<le> sqrt (\<Sum>t\<in>X. (a t)\<^sup>2) * sqrt (\<Sum>t\<in>X. (b t)\<^sup>2)"
proof-
  have "norm (\<Sum>t\<in>X. cnj (complex_of_real (a t)) * complex_of_real (b t))
    \<le> sqrt (\<Sum>t\<in>X. (cmod (complex_of_real (a t)))\<^sup>2) *
      sqrt (\<Sum>t\<in>X. (cmod (complex_of_real (b t)))\<^sup>2)"
  using assms Cauchy_Schwarz_complex [where X = X and a = a and b = b]
  by simp
  moreover have "norm (\<Sum>t\<in>X. (a t) * (b t)) = norm (\<Sum>t\<in>X. cnj (complex_of_real (a t)) * complex_of_real (b t))"
  proof-
    have "(a t) * (b t) = cnj (complex_of_real (a t)) * complex_of_real (b t)"
      for t
      by simp      
    hence "(\<Sum>t\<in>X. (a t) * (b t)) = (\<Sum>t\<in>X. cnj (complex_of_real (a t)) * complex_of_real (b t))"
      by simp
    moreover have "norm (complex_of_real (\<Sum>t\<in>X. (a t) * (b t))) = norm (\<Sum>t\<in>X. (a t) * (b t))"
    proof-
      have "cmod (complex_of_real r) = norm r" for r::real
        by auto
      thus ?thesis
        by blast 
    qed
    ultimately show ?thesis by simp
  qed
  moreover have "sqrt (\<Sum>t\<in>X. (cmod (complex_of_real (a t)))\<^sup>2) = sqrt (\<Sum>t\<in>X.  (a t)\<^sup>2)"
    by simp
  moreover have "sqrt (\<Sum>t\<in>X. (cmod (complex_of_real (b t)))\<^sup>2) = sqrt (\<Sum>t\<in>X.  (b t)\<^sup>2)"
    by simp    
  ultimately show ?thesis 
    by simp    
qed

(* NEW *)
(* TODO: move to near the definition of onb_enum *)
lemma clinear_cbounded_linear_onb_enum: 
  fixes f::"'a::onb_enum \<Rightarrow> 'b::onb_enum"
  assumes "clinear f"
  shows "cbounded_linear f"
  using assms unfolding cbounded_linear_def
proof auto
  assume "clinear f"
  define basis where "basis = (canonical_basis::'a list)"
  define K::real where "K = sqrt (\<Sum>t\<in>set basis. norm (f t)^2)"

  have "norm (f x) \<le> norm x * K" for x
  proof-
    define c where "c t = complex_vector.representation (set basis) x t" for t
    have c1: "c t \<noteq> 0 \<Longrightarrow> t \<in> set basis" for t
      by (simp add: c_def complex_vector.representation_ne_zero)      
    have c2: "finite {t. c t \<noteq> 0}"
      by (metis (mono_tags, lifting) Collect_cong List.finite_set Set.filter_def c1 finite_filter)
    have basis_finite: "finite (set basis)"
      by simp
    have c3: "(\<Sum>t | c t \<noteq> 0. c t *\<^sub>C t) = x"
      unfolding c_def Complex_Vector_Spaces.representation_def
      apply auto
      subgoal
      proof-
        assume a1: "complex_independent (set basis)"
        assume a2: "x \<in> Complex_Vector_Spaces.span (set basis)"
        then have f3: "(\<Sum>a | Complex_Vector_Spaces.representation (set basis) x a \<noteq> 0. Complex_Vector_Spaces.representation (set basis) x a *\<^sub>C a) = x"
          using a1 complex_vector.sum_nonzero_representation_eq by blast
        have "Complex_Vector_Spaces.representation (set basis) x = (SOME f. (\<forall>a. f a \<noteq> 0 \<longrightarrow> a \<in> set basis) \<and> finite {a. f a \<noteq> 0} \<and> (\<Sum>a | f a \<noteq> 0. f a *\<^sub>C a) = x)"
          using a2 a1 by (simp add: complex_vector.representation_def)
        thus "(\<Sum>a | (SOME f. (\<forall>a. f a \<noteq> 0 \<longrightarrow> a \<in> set basis) \<and> finite {a. f a \<noteq> 0} \<and> (\<Sum>a | f a \<noteq> 0. f a *\<^sub>C a) = x) a \<noteq> 0. (SOME f. (\<forall>a. f a \<noteq> 0 \<longrightarrow> a \<in> set basis) \<and> finite {a. f a \<noteq> 0} \<and> (\<Sum>a | f a \<noteq> 0. f a *\<^sub>C a) = x) a *\<^sub>C a) = x"
          using f3 by presburger
      qed
      using basis_def canonical_basis_non_zero is_ortho_set_independent is_orthonormal apply auto[1]
      subgoal
      proof-
        assume "x \<notin> Complex_Vector_Spaces.span (set basis)"
        moreover have "Complex_Vector_Spaces.span (set basis) = UNIV"
        proof-
          have "Complex_Vector_Spaces.span (set basis) 
              = closure (Complex_Vector_Spaces.span (set basis))"
            by (simp add: span_finite_dim)
          thus ?thesis
          using is_basis_set
          unfolding basis_def is_basis_def
          by blast          
        qed
        ultimately show ?thesis
          by auto
      qed
      done
    hence "x = (\<Sum>t | c t \<noteq> 0. c t *\<^sub>C t)"
      by simp
    also have "\<dots> = (\<Sum>t\<in>set basis. c t *\<^sub>C t)"
      using DiffD2 List.finite_set c1 complex_vector.scale_eq_0_iff mem_Collect_eq subsetI 
        sum.mono_neutral_cong_left
      by smt (* > 1s *)
    finally have c4: "x = (\<Sum>t\<in>set basis. c t *\<^sub>C t)"
      by blast
    hence "f x = (\<Sum>t\<in>set basis. c t *\<^sub>C f t)"
      by (smt assms complex_vector.linear_scale complex_vector.linear_sum sum.cong)
    hence "norm (f x) = norm (\<Sum>t\<in>set basis. c t *\<^sub>C f t)"
      by simp
    also have "\<dots> \<le> (\<Sum>t\<in>set basis. norm (c t *\<^sub>C f t))"
      by (simp add: sum_norm_le)
    also have "\<dots> = (\<Sum>t\<in>set basis. norm (c t) * norm (f t))"
      by auto
    also have "\<dots> = norm (\<Sum>t\<in>set basis. norm (c t) * norm (f t))"
    proof-
      have "(\<Sum>t\<in>set basis. norm (c t) * norm (f t)) \<ge> 0"
        by (smt calculation norm_ge_zero)        
      thus ?thesis by simp
    qed
    also have "\<dots> \<le> sqrt (\<Sum>t\<in>set basis. (norm (c t))^2) * sqrt (\<Sum>t\<in>set basis. (norm (f t))^2)"
      using Cauchy_Schwarz_real
      by fastforce
    also have "\<dots> \<le> norm x * K"
    proof-
      have "(norm x)^2 = \<langle>x, x\<rangle>"
        using power2_norm_eq_cinner' by blast
      also have "\<dots> = \<langle>(\<Sum>t\<in>set basis. c t *\<^sub>C t), (\<Sum>s\<in>set basis. c s *\<^sub>C s)\<rangle>"
        using c4
        by simp 
      also have "\<dots> = (\<Sum>t\<in>set basis. \<langle>c t *\<^sub>C t, (\<Sum>s\<in>set basis. c s *\<^sub>C s)\<rangle>)"
        using cinner_sum_left by blast
      also have "\<dots> = (\<Sum>t\<in>set basis. (\<Sum>s\<in>set basis. \<langle>c t *\<^sub>C t, c s *\<^sub>C s\<rangle>))"
        by (metis (mono_tags, lifting) cinner_sum_right sum.cong)
      also have "\<dots> = (\<Sum>t\<in>set basis. (\<Sum>s\<in>set basis. c s * \<langle>c t *\<^sub>C t,  s\<rangle>))"
        by simp
      also have "\<dots> = (\<Sum>t\<in>set basis. (\<Sum>s\<in>set basis. c s * cnj (c t) * \<langle>t,  s\<rangle>))"
        by (metis (no_types, lifting) cinner_scaleC_left sum.cong vector_space_over_itself.scale_scale)
      also have "\<dots> = (\<Sum>t\<in>set basis. (norm (c t))^2 + (\<Sum>s\<in>(set basis)-{t}. c s * cnj (c t) * \<langle>t,  s\<rangle>))"
      proof-
        have "(\<Sum>s\<in>set basis. c s * cnj (c t) * \<langle>t,  s\<rangle>) = (norm (c t))^2 + (\<Sum>s\<in>(set basis)-{t}. c s * cnj (c t) * \<langle>t,  s\<rangle>)"
          if "t \<in> set basis" for t
        proof-         
          have "(\<Sum>s\<in>set basis. c s * cnj (c t) * \<langle>t,  s\<rangle>) =  c t * cnj (c t) * \<langle>t,  t\<rangle> + (\<Sum>s\<in>(set basis)-{t}. c s * cnj (c t) * \<langle>t,  s\<rangle>)"
            using that basis_finite
            Groups_Big.comm_monoid_add_class.sum.remove
            by (metis (no_types, lifting))
          moreover have "\<langle>t,  t\<rangle> = 1"
          proof-
            have "norm t = 1"
              using that is_normal[where x = t] unfolding basis_def is_basis_def
              by blast
            hence "(norm t)^2 = 1"
              by simp
            thus ?thesis
              by (metis of_real_hom.hom_one power2_norm_eq_cinner') 
          qed
          ultimately show ?thesis
            using complex_norm_square by auto 
        qed
        thus ?thesis by simp
      qed
      also have "\<dots> = (\<Sum>t\<in>set basis. (norm (c t))^2)"
      proof-
        have "s\<in>(set basis)-{t} \<Longrightarrow> c s * cnj (c t) * \<langle>t,  s\<rangle> = 0"
          for s t
          by (metis DiffD2 basis_def c1 complex_cnj_zero_iff is_ortho_set_def is_orthonormal mult_not_zero singleton_iff)          
        hence " (\<Sum>s\<in>(set basis)-{t}. c s * cnj (c t) * \<langle>t,  s\<rangle>) = 0"
          for t
          by (simp add: \<open>\<And>t s. s \<in> set basis - {t} \<Longrightarrow> c s * cnj (c t) * \<langle>t, s\<rangle> = 0\<close>) 
        thus ?thesis by simp
      qed
      finally have "(norm x)^2 = (\<Sum>t\<in>set basis. (norm (c t))^2)"
        using of_real_eq_iff by blast        
      hence "norm x = sqrt (\<Sum>t\<in>set basis. norm (c t)^2)"
        using real_sqrt_unique by auto        
      thus ?thesis 
        unfolding K_def by simp
    qed
    finally show ?thesis by blast
  qed
  thus "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K" 
    by blast
qed

lift_definition cblinfun_of_mat :: \<open>complex mat \<Rightarrow> 'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum\<close> is  
  \<open>\<lambda>M. \<lambda>v. (if M\<in>carrier_mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))
           then onb_enum_of_vec (M *\<^sub>v (vec_of_onb_enum v))
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
          using Bounded_Operators_Code.onb_enum_of_vec_add[where ?v1.0 = "M *\<^sub>v vec_of_onb_enum b1" 
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


(* TODO: constructive definition *)
definition mat_of_cblinfun :: \<open>'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum \<Rightarrow> complex mat\<close> where
  \<open>mat_of_cblinfun f  = mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a)) (
  \<lambda> (i, j).
  \<langle> (canonical_basis::'b list)!i,
    (map (cblinfun_apply f) (canonical_basis::'a list) )!j\<rangle>
)\<close>
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
lemma mat_of_cblinfun_inverse [code abstype]:
  "cblinfun_of_mat (mat_of_cblinfun B) = B" 
  for B::"('a::onb_enum,'b::onb_enum) cblinfun"
  sorry

lemma mat_of_cblinfun_inj: "inj mat_of_cblinfun"
  by (metis inj_on_def mat_of_cblinfun_inverse)


subsection \<open>Code equations for cblinfun operators\<close>

text \<open>In this subsection, we define the code for all operations involving only 
  operators (no combinations of operators/vectors/subspaces)\<close>

text \<open>This lemma defines addition. By writing \<^term>\<open>mat_of_cblinfun (M + N)\<close>
on the left hand side, we get access to the\<close>
lemma cblinfun_of_mat_plusOp[code]:
  "mat_of_cblinfun (M + N) = mat_of_cblinfun M + mat_of_cblinfun N" 
  for M::"('a::onb_enum,'b::onb_enum) cblinfun" and N::"('a::onb_enum,'b) cblinfun"
    (* 

Approach 1: Use definition of mat_of_cblinfun. Then do linear algebra.

Approach 2: Show
"(M + N) =  (cblinfun_of_mat M + cblinfun_of_mat N)" first.
Then use mat_of_cblinfun_inverse to get the lemma.

(Probably approach 2 is easier)

*)
  sorry

lemma cblinfun_of_mat_id[code]:
  "mat_of_cblinfun (idOp :: ('a::onb_enum,'a) cblinfun) = one_mat (canonical_basis_length TYPE('a))"
  sorry

lemma cblinfun_of_mat_timesOp[code]:
  "mat_of_cblinfun (M o\<^sub>C\<^sub>L N) =  (mat_of_cblinfun M * mat_of_cblinfun N)" 
  for M::"('b::onb_enum,'c::onb_enum) cblinfun" and N::"('a::onb_enum,'b) cblinfun"
  sorry

lemma cblinfun_of_mat_minusOp[code]:
  "mat_of_cblinfun (M - N) =  (mat_of_cblinfun M - mat_of_cblinfun N)" 
  for M::"('a::onb_enum,'b::onb_enum) cblinfun" and N::"('a::onb_enum,'b) cblinfun"
  sorry

lemma cblinfun_of_mat_uminusOp[code]:
  "mat_of_cblinfun (- M) = - mat_of_cblinfun M" for M::"('a::onb_enum,'b::onb_enum) cblinfun"
  sorry

lemma mat_of_cblinfun_scalarMult[code]:
  "mat_of_cblinfun ((a::complex) *\<^sub>C M) = smult_mat a (mat_of_cblinfun M)" for M :: "('a::onb_enum,'b::onb_enum) cblinfun"
  sorry

text \<open>This instantiation defines a code equation for equality tests for cblinfun operators.\<close>
instantiation cblinfun :: (onb_enum,onb_enum) equal begin
definition [code]: "equal_cblinfun M N \<longleftrightarrow> mat_of_cblinfun M = mat_of_cblinfun N" 
  for M N :: "('a,'b) cblinfun"
instance 
  apply intro_classes
  unfolding equal_cblinfun_def 
  using mat_of_cblinfun_inj injD by fastforce
end

definition "adjoint_mat M = transpose_mat (map_mat cnj M)"

lemma cblinfun_of_mat_adjoint[code]:
  "mat_of_cblinfun (adjoint A) = adjoint_mat (mat_of_cblinfun A)"
  for A :: "('a::onb_enum,'b::onb_enum) cblinfun"
  sorry

lemma mat_of_cblinfun_zero[code]:
  "mat_of_cblinfun (0::('a::onb_enum,'b::onb_enum) cblinfun)
       = zero_mat (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))"
  sorry

lemma mat_of_cblinfun_classical_operator[code]: 
  "mat_of_cblinfun (classical_operator f) = mat (CARD('b)) (CARD('a))
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
unbundle no_cblinfun_notation

end
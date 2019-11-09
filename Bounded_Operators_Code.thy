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

primrec vec_of_basis_enum_list :: \<open>'a list \<Rightarrow> 'a::basis_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_basis_enum_list [] v = 0\<^sub>v (length (canonical_basis::'a list))\<close> |
  \<open>vec_of_basis_enum_list (x#ys) v = vec_of_basis_enum_list ys v +
\<langle>x, v\<rangle> \<cdot>\<^sub>v 
unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length ys)\<close>

definition vec_of_basis_enum :: \<open>'a::basis_enum \<Rightarrow> complex vec\<close> where
  \<open>vec_of_basis_enum v = vec_of_basis_enum_list (canonical_basis::'a list) v\<close>

lemma dim_vec_of_basis_enum_list:
  \<open>dim_vec (vec_of_basis_enum_list (L::'a list) v) = length (canonical_basis::'a::basis_enum list)\<close>
  by (induction L, auto)

lemma vec_of_basis_enum_list_add:
  \<open>vec_of_basis_enum_list (L::'a::basis_enum list) (v1 + v2) =
 vec_of_basis_enum_list L v1 + vec_of_basis_enum_list L v2\<close>
proof (induction L arbitrary : v1 v2)
  case Nil
  thus ?case by auto
next
  case (Cons a L)
  fix v1 v2
  assume \<open>(\<And>v1 v2.
           vec_of_basis_enum_list L (v1 + v2) =
           vec_of_basis_enum_list L v1 + vec_of_basis_enum_list L v2)\<close>
  have \<open>vec_of_basis_enum_list (a # L) (v1 + v2) = vec_of_basis_enum_list (a # L) v1 + vec_of_basis_enum_list (a # L) v2\<close>
  proof-
    have \<open>dim_vec (vec_of_basis_enum_list L v1) = length (canonical_basis::'a list)\<close>
      by (simp add: dim_vec_of_basis_enum_list)
    moreover have \<open>dim_vec (vec_of_basis_enum_list L v2) = length (canonical_basis::'a list)\<close>
      by (simp add: dim_vec_of_basis_enum_list)
    moreover have \<open>dim_vec (\<langle>a, v1\<rangle> \<cdot>\<^sub>v  unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L) )
          =  length (canonical_basis::'a list)\<close>
      by auto
    moreover have \<open>dim_vec (\<langle>a, v2\<rangle> \<cdot>\<^sub>v  unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L) )
          =  length (canonical_basis::'a list)\<close>
      by auto
    moreover have \<open>vec_of_basis_enum_list (a # L) (v1 + v2) = 
           vec_of_basis_enum_list L (v1 + v2) 
+ \<langle>a, v1 + v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L)\<close>
      by auto
    moreover have \<open>vec_of_basis_enum_list L (v1 + v2) =
            vec_of_basis_enum_list L v1 + vec_of_basis_enum_list L v2\<close>
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
    ultimately have \<open>vec_of_basis_enum_list (a # L) (v1 + v2) =
   (vec_of_basis_enum_list L v1 + \<langle>a, v1\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L))
+  (vec_of_basis_enum_list L v2 + \<langle>a, v2\<rangle> \<cdot>\<^sub>v unit_vec (length (canonical_basis::'a list)) ((length (canonical_basis::'a list)) - length L))\<close>
      by auto
    thus ?thesis by auto
  qed
  thus \<open>vec_of_basis_enum_list (a # L) (v1 + v2) =
       vec_of_basis_enum_list (a # L) v1 + vec_of_basis_enum_list (a # L) v2\<close> 
    by blast
qed

lemma vec_of_basis_enum_add:
  \<open>vec_of_basis_enum (v1 + v2) = vec_of_basis_enum v1 + vec_of_basis_enum v2\<close>
  by (simp add: vec_of_basis_enum_def vec_of_basis_enum_list_add)


lemma vec_of_basis_enum_list_mult:
  fixes L :: "'a::basis_enum list"
  shows \<open>vec_of_basis_enum_list L (c *\<^sub>C v) = c \<cdot>\<^sub>v vec_of_basis_enum_list L v\<close>
proof (induction L)
  case Nil
  then show ?case by auto
next
  case (Cons a L)
  let ?basis = "canonical_basis :: 'a list"
  let ?dim = "length ?basis"

  have dim_L: "dim_vec (vec_of_basis_enum_list L v) = ?dim"
    by (simp add: dim_vec_of_basis_enum_list)

  have "vec_of_basis_enum_list (a # L) (c *\<^sub>C v) 
      = vec_of_basis_enum_list L (c *\<^sub>C v) + c * \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length ?basis) (length ?basis - length L)"
    by simp
  also have "\<dots> = c \<cdot>\<^sub>v vec_of_basis_enum_list L v + c * \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length ?basis) (length ?basis - length L)"
    using Cons.IH by simp
  also have "\<dots> = c \<cdot>\<^sub>v vec_of_basis_enum_list L v + c \<cdot>\<^sub>v (\<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length ?basis) (length ?basis - length L))"
    by (simp add: smult_smult_assoc)
  also have "\<dots> = c \<cdot>\<^sub>v (vec_of_basis_enum_list L v + \<langle>a, v\<rangle> \<cdot>\<^sub>v unit_vec (length ?basis) (length ?basis - length L))"
    apply (rule smult_add_distrib_vec[where n="?dim", symmetric])
    using dim_L apply auto
    by (metis carrier_vec_dim_vec)
  also have "\<dots> = c \<cdot>\<^sub>v vec_of_basis_enum_list (a # L) v"
    by auto
  finally show ?case
    by -
qed


lemma vec_of_basis_enum_mult:
  \<open>vec_of_basis_enum (c *\<^sub>C v) = c \<cdot>\<^sub>v vec_of_basis_enum v\<close>
  by (simp add: vec_of_basis_enum_def vec_of_basis_enum_list_mult)


fun basis_enum_of_vec_list :: \<open>'a list \<Rightarrow> complex list \<Rightarrow> 'a::basis_enum\<close> where 
  \<open>basis_enum_of_vec_list [] v = 0\<close> |
  \<open>basis_enum_of_vec_list y [] = 0\<close> |
  \<open>basis_enum_of_vec_list (x#ys) (v#vs) = v *\<^sub>C x + basis_enum_of_vec_list ys vs\<close>

definition basis_enum_of_vec :: \<open>complex vec \<Rightarrow> 'a::basis_enum\<close> where
  \<open>basis_enum_of_vec v = basis_enum_of_vec_list (canonical_basis::'a list) (list_of_vec v)\<close>

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
  defines "basis \<equiv> canonical_basis::'a::basis_enum list"
  assumes \<open>dim_vec v1 = length basis\<close> and
    \<open>dim_vec v2 = length basis\<close>
  shows \<open>((basis_enum_of_vec (v1 + v2)) :: 'a) = basis_enum_of_vec v1 + basis_enum_of_vec v2\<close>
proof -
  define l1 l2 where "l1 = list_of_vec v1" and "l2 = list_of_vec v2"
  have length: "length l1 = length l2"
    by (simp add: assms(2) assms(3) l1_def l2_def)
  have length_basis: "length l2 = length basis"
    by (simp add: assms(3) l2_def)
  have \<open>(basis_enum_of_vec::_\<Rightarrow>'a) (v1 + v2) = basis_enum_of_vec_list basis (list_of_vec (v1+v2))\<close>
    by (simp add: basis_def basis_enum_of_vec_def)
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
    by (simp add: basis_def basis_enum_of_vec_def l1_def l2_def)
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
  defines "basis \<equiv> canonical_basis::'a::basis_enum list"
  assumes \<open>dim_vec v = length basis\<close> 
  shows \<open>((basis_enum_of_vec (c \<cdot>\<^sub>v v)) :: 'a) =  c *\<^sub>C basis_enum_of_vec v\<close>
proof -
  define l where "l = list_of_vec v"
  have length_basis: "length l = length basis"
    by (simp add: assms(2) l_def)
  have \<open>(basis_enum_of_vec::_\<Rightarrow>'a) (c \<cdot>\<^sub>v v) =
 basis_enum_of_vec_list basis (list_of_vec (c \<cdot>\<^sub>v v))\<close>
    by (simp add: basis_def basis_enum_of_vec_def)
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
    by (simp add: basis_def basis_enum_of_vec_def l_def)
  finally show ?thesis
    by auto
qed


(* TODO: When written as \<open>basis_enum_of_vec (vec_of_basis_enum v) = v\<close>
   such a lemma is more easily used as, e.g., a simp-rule (in my experience) *)
lemma basis_enum_of_vec_COMP_vec_of_basis_enum:
  \<open>(basis_enum_of_vec::(complex vec \<Rightarrow> 'a::basis_enum)) \<circ> (vec_of_basis_enum::('a \<Rightarrow> complex vec))
 = (id::('a \<Rightarrow> 'a))\<close>
proof-
  have \<open>dim_vec (vec_of_basis_enum b) = length (canonical_basis::'a list)\<close>
    for b::'a
    by (simp add: dim_vec_of_basis_enum_list vec_of_basis_enum_def)    
  define f::\<open>'a \<Rightarrow> 'a\<close> where \<open>f v = basis_enum_of_vec ( vec_of_basis_enum v ) - v\<close>
    for v::'a
  have \<open>distinct (canonical_basis::('a list))\<close>
    by (simp add: distinct_canonical_basis)    
  hence \<open>v \<in> set (canonical_basis::('a list)) \<Longrightarrow> f v = 0\<close>
    for v
    unfolding f_def
    by (cheat TODO)
  moreover have \<open>clinear f\<close>
  proof-
    have \<open>clinear (\<lambda> v. (basis_enum_of_vec::(complex vec \<Rightarrow> 'a::basis_enum)) ( (vec_of_basis_enum::('a \<Rightarrow> complex vec)) v) )\<close>
      unfolding clinear_def
    proof
      show "basis_enum_of_vec (vec_of_basis_enum (b1 + b2)) = basis_enum_of_vec (vec_of_basis_enum b1) + ((basis_enum_of_vec (vec_of_basis_enum b2))::'a)"
        for b1 :: 'a
          and b2 :: 'a
      proof-
        have \<open>basis_enum_of_vec (vec_of_basis_enum (b1 + b2)) = 
              basis_enum_of_vec (vec_of_basis_enum b1 + vec_of_basis_enum b2)\<close>
          by (simp add: vec_of_basis_enum_def vec_of_basis_enum_list_add)
        also have \<open>\<dots> = 
              basis_enum_of_vec (vec_of_basis_enum b1) + ((basis_enum_of_vec (vec_of_basis_enum b2))::'a)\<close>
        proof-
          have \<open>length (canonical_basis::'a list) \<le> dim_vec (vec_of_basis_enum b1)\<close>
            by (simp add: \<open>\<And>b. dim_vec (vec_of_basis_enum b) = length canonical_basis\<close>)
          moreover have \<open>length (canonical_basis::'a list) \<le> dim_vec (vec_of_basis_enum b2)\<close>
            by (simp add: \<open>\<And>b. dim_vec (vec_of_basis_enum b) = length canonical_basis\<close>)
          ultimately show ?thesis
            unfolding basis_enum_of_vec_def
          proof -
            have ?thesis
              by (meson \<open>\<And>b. dim_vec (vec_of_basis_enum b) = length canonical_basis\<close> basis_enum_of_vec_add)
            thus "basis_enum_of_vec_list canonical_basis (list_of_vec (vec_of_basis_enum b1 + vec_of_basis_enum b2)) = (basis_enum_of_vec_list canonical_basis (list_of_vec (vec_of_basis_enum b1))::'a) + basis_enum_of_vec_list canonical_basis (list_of_vec (vec_of_basis_enum b2))"
              by (simp add: basis_enum_of_vec_def)
          qed            
        qed
        finally show ?thesis by auto
      qed
      show "basis_enum_of_vec (vec_of_basis_enum (r *\<^sub>C (b::'a))) = r *\<^sub>C (basis_enum_of_vec (vec_of_basis_enum b)::'a)"
        for r :: complex
          and b :: 'a
      proof-
        have \<open>basis_enum_of_vec (vec_of_basis_enum (r *\<^sub>C b)) = 
              basis_enum_of_vec (r \<cdot>\<^sub>v (vec_of_basis_enum b))\<close>
          by (simp add: vec_of_basis_enum_def vec_of_basis_enum_list_mult)          
        also have \<open>\<dots> = 
              r *\<^sub>C ((basis_enum_of_vec (vec_of_basis_enum b))::'a)\<close>
        proof-
          have \<open>length (canonical_basis::'a list) \<le> dim_vec (vec_of_basis_enum b)\<close>
            by (simp add: \<open>\<And>b. dim_vec (vec_of_basis_enum b) = length canonical_basis\<close>)
          thus ?thesis
            unfolding basis_enum_of_vec_def
          proof -
            have ?thesis
              by (meson \<open>\<And>b. dim_vec (vec_of_basis_enum b) = length canonical_basis\<close> basis_enum_of_vec_mult)
            then show "basis_enum_of_vec_list canonical_basis (list_of_vec (r \<cdot>\<^sub>v vec_of_basis_enum b)) = r *\<^sub>C (basis_enum_of_vec_list canonical_basis (list_of_vec (vec_of_basis_enum b))::'a)"
              by (simp add: basis_enum_of_vec_def)
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
      unfolding is_onb_def is_basis_def
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

(* TODO: When written as \<open>vec_of_basis_enum (basis_enum_of_vec v) = v\<close>
   such a lemma is more easily used as, e.g., a simp-rule (in my experience) *)
(* TODO: Not true. Only holds for vectors v with "dim v = canonical_basis_length" *)
lemma vec_of_basis_enum_COMP_basis_enum_of_vec:
  \<open>vec_of_basis_enum \<circ> basis_enum_of_vec = id\<close>
  by (cheat TODO)

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

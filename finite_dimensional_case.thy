(*  Title:      bounded-Operators/finite_dimensional_case.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

Embedding of finite dimensional structures in the infinite dimensional ones.

References:             

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}


*)

theory finite_dimensional_case
  imports 
    "HOL-ex.Sketch_and_Explore"
    finite_rank_operators
    complex_bounded_operators
    Jordan_Normal_Form.Matrix
    Complex_L2

begin

section \<open>Embedding of an n-dimensional complex vector space into the complex
vector space of square-summable sequences\<close>

subsection \<open>Definitions\<close>

text \<open>Embedding of vec into ell2.\<close>
lift_definition vec_to_ell2 :: \<open>complex vec \<Rightarrow> nat ell2\<close> is
  \<open>\<lambda> v::complex vec. (\<lambda> i::nat. 
(if i < dim_vec v
then (vec_index v) i
else 0)
)\<close>
  apply transfer
proof auto
  fix n :: nat and f :: \<open>nat \<Rightarrow> complex\<close>
  define F where \<open>F i = (if i < n then f i else 0)\<close> 
    for i::nat
  define g where \<open>g i = (cmod (F i))\<^sup>2\<close> 
    for i::nat
  define h where \<open>h i = (norm (g i))\<close> 
    for i::nat
  have \<open>finite {i::nat. i < n}\<close>
    by simp
  moreover have \<open>h i = (if i < n then h i else 0)\<close>
    for i
    unfolding h_def g_def F_def
    by simp     
  ultimately have \<open>summable h\<close>
    by (metis (no_types) \<open>\<And>i. h i = (if i < n then h i else 0)\<close> \<open>finite {i. i < n}\<close> mem_Collect_eq summable_finite)    
  hence \<open>g abs_summable_on UNIV\<close>
    unfolding h_def using abs_summable_on_nat_iff' by blast
  thus \<open>has_ell2_norm F\<close> unfolding F_def g_def
    using has_ell2_norm_infsetsum by auto
qed

text \<open>Embedding of a function (defined on an n-dimensional space) into functions defined on ell2.\<close>
definition fun_to_ell2 :: \<open>nat \<Rightarrow> (complex vec \<Rightarrow> 'a) \<Rightarrow> (nat ell2 \<Rightarrow> 'a)\<close> where
  \<open>fun_to_ell2 n f = (\<lambda> x::nat ell2. f (vec n (Rep_ell2 x)))\<close>

text \<open>Transformation of of a vector in ell2 into an n dimensional vector space (some
information may be lost)\<close>
definition ell2_to_vec :: \<open>nat \<Rightarrow> nat ell2 \<Rightarrow> complex vec\<close> where
  \<open>ell2_to_vec n x = ( fun_to_ell2 n (id::complex vec \<Rightarrow> complex vec) ) x\<close>
for x :: \<open>nat ell2\<close>

subsection \<open>Set-theoretic properties of the embedding\<close>

text\<open>The embedding for vectors is injective.\<close>
lemma vec_to_ell2_inj:
  fixes x y :: \<open>complex vec\<close>
  assumes \<open>vec_to_ell2 x = vec_to_ell2 y\<close> and \<open>dim_vec x = dim_vec y\<close>
  shows \<open>vec_index x = vec_index y\<close>
proof-
  define n::nat where \<open>n = dim_vec x\<close>
  hence \<open>n = dim_vec y\<close> using \<open>dim_vec x = dim_vec y\<close> by blast
  have \<open>(vec_index x) i = (vec_index y) i\<close>
    for i
  proof(cases \<open>i < n\<close>)
    case True
    hence \<open>i < n\<close> by blast
    have \<open>(Rep_ell2 (vec_to_ell2 x)) i = (vec_index x) i\<close>
      using True vec_to_ell2.rep_eq n_def by auto      
    moreover have \<open>(Rep_ell2 (vec_to_ell2 y)) i = (vec_index y) i\<close>
      using True \<open>n = dim_vec y\<close> vec_to_ell2.rep_eq by auto      
    moreover have \<open>(Rep_ell2 (vec_to_ell2 x)) i = (Rep_ell2 (vec_to_ell2 y)) i\<close>
      using \<open>vec_to_ell2 x = vec_to_ell2 y\<close> by simp
    ultimately show ?thesis by simp
  next
    case False
    hence \<open>\<not>(i < n)\<close> by blast
    hence \<open>(vec_index x) i = undef_vec (i - n)\<close>
      using mk_vec_def 
      by (metis (no_types, hide_lams) dim_vec.rep_eq eq_vecI fst_conv n_def snd_conv vec.rep_eq vec_index.rep_eq)       
    moreover have \<open>(vec_index y) i = undef_vec (i - n)\<close>
      using mk_vec_def  \<open>\<not>(i < n)\<close> \<open>n = dim_vec y\<close>
      by (metis (no_types, hide_lams) dim_vec.rep_eq eq_vecI fst_conv snd_conv vec.rep_eq vec_index.rep_eq)       
    ultimately show ?thesis by simp
  qed
  thus ?thesis by blast
qed

lemma ell2_to_vec_well_defined_dim:
  fixes x :: \<open>nat ell2\<close> and n :: nat
  shows \<open>dim_vec (ell2_to_vec n x) = n\<close>
  unfolding dim_vec_def 
  apply auto
  unfolding ell2_to_vec_def id_def fun_to_ell2_def
  apply transfer
  apply auto
  done

lemma ell2_to_vec_well_defined_index:
  fixes x :: \<open>nat ell2\<close> and n :: nat and i :: nat
  shows \<open>i < n \<Longrightarrow> vec_index (ell2_to_vec n x) i = (Rep_ell2 x) i\<close>
  unfolding vec_index_def 
  apply auto
  unfolding ell2_to_vec_def id_def fun_to_ell2_def
  apply transfer
  apply auto
  unfolding mk_vec_def
  apply auto
  done

text \<open>The embedding for functions is well-defined\<close>
lemma fun_to_ell2_well_defined:
  fixes f :: \<open>complex vec \<Rightarrow> 'a\<close> and x :: \<open>nat ell2\<close> and v :: \<open>complex vec\<close> and n :: nat
  assumes \<open>dim_vec v = n\<close>
  shows \<open>fun_to_ell2 n f (vec_to_ell2 v) = f v\<close>
  unfolding fun_to_ell2_def
  using assms
  by (metis dim_vec eq_vecI index_vec vec_to_ell2.rep_eq)


text \<open>The embdedding for functions is injective.\<close>
lemma fun_to_ell2_inject:
  fixes f g :: \<open>complex vec \<Rightarrow> 'a\<close> and n :: nat
  assumes \<open>dim_vec v = n\<close> and \<open>fun_to_ell2 n f = fun_to_ell2 n g\<close>
  shows \<open>f v = g v\<close>
  unfolding fun_to_ell2_def
  by (metis assms(1) assms(2) fun_to_ell2_well_defined)


subsection \<open>Linear-algebraic properties of the embedding\<close>

text \<open>The embedding for vectors is additive\<close>
lemma vec_to_ell2_add:
  fixes x y :: \<open>complex vec\<close> 
  shows \<open>dim_vec x = dim_vec y \<Longrightarrow> vec_to_ell2 (x + y) = vec_to_ell2 x + vec_to_ell2 y\<close>
  apply transfer
  by auto


text \<open>The embedding for vectors is complex-homogeneous\<close>
lemma vec_to_ell2_smult:
  fixes x :: \<open>complex vec\<close> and r :: complex 
  shows \<open>vec_to_ell2 (r \<cdot>\<^sub>v x) = r *\<^sub>C (vec_to_ell2 x)\<close>
  apply transfer
  by auto

text\<open>The embedding of a complex-linear function (defined on an n-dimensional space) 
is complex-linear\<close>

locale clinear_vec =
  fixes n :: nat and f :: \<open>complex vec \<Rightarrow> 'a::complex_vector\<close>
  assumes add:  \<open>\<And> x y. dim_vec x = n \<Longrightarrow> dim_vec y = n \<Longrightarrow> f (x + y) = f x + f y\<close>
    and mults:  \<open>\<And> c. \<And> x. dim_vec x = n \<Longrightarrow> f (c \<cdot>\<^sub>v x) = c *\<^sub>C (f x)\<close>

lemma clinear_ell2_map_left:
  fixes n :: nat and f :: \<open>complex vec \<Rightarrow> 'a::complex_vector\<close>
  assumes \<open>clinear_vec n f\<close>   
  shows \<open>clinear (fun_to_ell2 n f)\<close>
proof
  show "fun_to_ell2 n f (x + y) = fun_to_ell2 n f x + fun_to_ell2 n f y"
    for x :: "nat ell2"
      and y :: "nat ell2"
    using  \<open>clinear_vec n f\<close>   
    unfolding fun_to_ell2_def vec_def Abs_vec_inverse clinear_vec_def
    by (smt Matrix.vec_def dim_vec eq_vecI index_add_vec(1) index_add_vec(2) index_vec plus_ell2.rep_eq)

  show "fun_to_ell2 n f (r *\<^sub>C x) = r *\<^sub>C fun_to_ell2 n f x"
    for r :: complex
      and x :: "nat ell2"
    using  \<open>clinear_vec n f\<close>   
    unfolding fun_to_ell2_def vec_def Abs_vec_inverse clinear_vec_def
    by (smt Matrix.vec_def dim_vec eq_vecI index_smult_vec(1) index_smult_vec(2) index_vec scaleC_ell2.rep_eq)
qed

lemma clinear_ell2_map_left_converse:
  fixes n :: nat and f :: \<open>complex vec \<Rightarrow> 'a::complex_vector\<close>
  assumes \<open>clinear (fun_to_ell2 n f)\<close>    
  shows \<open>clinear_vec n f\<close>
proof
  show "f (x + y) = f x + f y"
    if "dim_vec (x::complex Matrix.vec) = n"
      and "dim_vec (y::complex Matrix.vec) = n"
    for x :: "complex Matrix.vec"
      and y :: "complex Matrix.vec"
  proof-
    have \<open>(fun_to_ell2 n f) (vec_to_ell2 x + vec_to_ell2 y) = 
        (fun_to_ell2 n f) (vec_to_ell2 x) +  (fun_to_ell2 n f) (vec_to_ell2 y)\<close>
      using \<open>clinear (fun_to_ell2 n f)\<close>
      unfolding clinear_def Modules.additive_def
      by blast
    moreover have \<open>vec_to_ell2 (x + y) = vec_to_ell2 x + vec_to_ell2 y\<close>
      by (simp add: that(1) that(2) vec_to_ell2_add)
    ultimately have  \<open>(fun_to_ell2 n f) (vec_to_ell2 (x + y)) = 
        (fun_to_ell2 n f) (vec_to_ell2 x) +  (fun_to_ell2 n f) (vec_to_ell2 y)\<close>
      by auto
    moreover have \<open>(fun_to_ell2 n f) (vec_to_ell2 (x + y)) = f (x + y)\<close>
      by (simp add: fun_to_ell2_well_defined that(2))
    moreover have \<open>(fun_to_ell2 n f) (vec_to_ell2 x) = f x\<close>
      by (simp add: fun_to_ell2_well_defined that(1))
    moreover have \<open>(fun_to_ell2 n f) (vec_to_ell2 y) = f y\<close>
      by (simp add: fun_to_ell2_well_defined that(2))
    ultimately show ?thesis
      by simp
  qed
  show "f (c \<cdot>\<^sub>v x) = c *\<^sub>C f x"
    if "dim_vec (x::complex Matrix.vec) = n"
    for c :: complex
      and x :: "complex Matrix.vec"
    by (metis (no_types, lifting) assms clinear.axioms(2) clinear_axioms_def fun_to_ell2_well_defined index_smult_vec(2) that vec_to_ell2_smult)   
qed



lemma ell2_to_vec_add:
  fixes x y :: \<open>nat ell2\<close> and n :: nat 
  shows \<open>ell2_to_vec n (x + y) = ell2_to_vec n x + ell2_to_vec n y\<close>
proof-
  have \<open>ell2_to_vec n x + ell2_to_vec n y = 
    vec (dim_vec (ell2_to_vec n y)) 
        (\<lambda>i. vec_index (ell2_to_vec n x) i + vec_index (ell2_to_vec n y) i)\<close>
    using plus_vec_def
    by auto
  have \<open>dim_vec (ell2_to_vec n x) = n\<close>
    by (simp add: ell2_to_vec_well_defined_dim)
  have \<open>dim_vec (ell2_to_vec n y) = n\<close>
    by (simp add: ell2_to_vec_well_defined_dim)
  have \<open>dim_vec (ell2_to_vec n (x + y)) = n\<close>
    by (simp add: ell2_to_vec_well_defined_dim)
  have \<open>i < n \<Longrightarrow> vec_index (ell2_to_vec n x) i = (Rep_ell2 x) i\<close>
    for i::nat
    using ell2_to_vec_well_defined_index by auto
  have \<open>i < n \<Longrightarrow> vec_index (ell2_to_vec n y) i = (Rep_ell2 y) i\<close>
    for i::nat
    using ell2_to_vec_well_defined_index by auto
  have \<open>i < n \<Longrightarrow> vec_index (ell2_to_vec n (x + y)) i = (Rep_ell2 (x + y)) i\<close>
    for i::nat
    using ell2_to_vec_well_defined_index by auto
  have \<open>i \<ge> n \<Longrightarrow> vec_index (ell2_to_vec n x) i = undef_vec (i - n)\<close>
    for i::nat
    using \<open>dim_vec (ell2_to_vec n x) = n\<close>
    unfolding vec_index_def
    apply auto
    unfolding ell2_to_vec_def fun_to_ell2_def
    apply auto
    unfolding vec_def
    apply auto
    unfolding mk_vec_def
  proof-
    assume \<open>n \<le> i\<close>
    hence \<open> snd  (n, \<lambda>i. if i < n then Rep_ell2 x i else undef_vec (i - n)) i =
     undef_vec (i - n) \<close>
      by auto
    moreover have \<open>(Rep_vec (Abs_vec (n, \<lambda>i. if i < n then Rep_ell2 x i else undef_vec (i - n))))
        = (n, \<lambda>i. if i < n then Rep_ell2 x i else undef_vec (i - n))\<close>
    proof-
      have \<open> (n, \<lambda>i. if i < n then Rep_ell2 x i else undef_vec (i - n)) \<in> {(n, mk_vec n f) |n f. True} \<close>
        unfolding mk_vec_def
        by auto
      thus ?thesis using Abs_vec_inverse
        by blast
    qed
    ultimately show \<open>snd (Rep_vec (Abs_vec (n, \<lambda>i. if i < n then Rep_ell2 x i else undef_vec (i - n)))) i =
    undef_vec (i - n)\<close> by simp 
  qed
  have \<open>i \<ge> n \<Longrightarrow> vec_index (ell2_to_vec n y) i = undef_vec (i - n)\<close>
    for i::nat
    using \<open>dim_vec (ell2_to_vec n y) = n\<close>
    unfolding vec_index_def
    apply auto
    unfolding ell2_to_vec_def fun_to_ell2_def
    apply auto
    unfolding vec_def
    apply auto
    unfolding mk_vec_def
  proof-
    assume \<open>n \<le> i\<close>
    hence \<open> snd  (n, \<lambda>i. if i < n then Rep_ell2 y i else undef_vec (i - n)) i =
     undef_vec (i - n) \<close>
      by auto
    moreover have \<open>(Rep_vec (Abs_vec (n, \<lambda>i. if i < n then Rep_ell2 y i else undef_vec (i - n))))
        = (n, \<lambda>i. if i < n then Rep_ell2 y i else undef_vec (i - n))\<close>
    proof-
      have \<open> (n, \<lambda>i. if i < n then Rep_ell2 y i else undef_vec (i - n)) \<in> {(n, mk_vec n f) |n f. True} \<close>
        unfolding mk_vec_def
        by auto
      thus ?thesis using Abs_vec_inverse
        by blast
    qed
    ultimately show \<open>snd (Rep_vec (Abs_vec (n, \<lambda>i. if i < n then Rep_ell2 y i else undef_vec (i - n)))) i =
    undef_vec (i - n)\<close> by simp 
  qed
  have \<open>i \<ge> n \<Longrightarrow> vec_index (ell2_to_vec n (x + y)) i = undef_vec (i - n)\<close>
    for i::nat
    using \<open>dim_vec (ell2_to_vec n (x+y)) = n\<close>
    unfolding vec_index_def
    apply auto
    unfolding ell2_to_vec_def fun_to_ell2_def
    apply auto
    unfolding vec_def
    apply auto
    unfolding mk_vec_def
  proof-
    assume \<open>n \<le> i\<close>
    hence \<open> snd  (n, \<lambda>i. if i < n then Rep_ell2 (x+y) i else undef_vec (i - n)) i =
     undef_vec (i - n) \<close>
      by auto
    moreover have \<open>(Rep_vec (Abs_vec (n, \<lambda>i. if i < n then Rep_ell2 (x+y) i else undef_vec (i - n))))
        = (n, \<lambda>i. if i < n then Rep_ell2 (x + y) i else undef_vec (i - n))\<close>
    proof-
      have \<open> (n, \<lambda>i. if i < n then Rep_ell2 (x+y) i else undef_vec (i - n)) \<in> {(n, mk_vec n f) |n f. True} \<close>
        unfolding mk_vec_def
        by auto
      thus ?thesis using Abs_vec_inverse
        by blast
    qed
    ultimately show \<open>snd (Rep_vec (Abs_vec (n, \<lambda>i. if i < n then Rep_ell2 (x+y) i else undef_vec (i - n)))) i =
    undef_vec (i - n)\<close> by simp 
  qed
  show ?thesis
    by (smt \<open>dim_vec (ell2_to_vec n (x + y)) = n\<close> \<open>dim_vec (ell2_to_vec n y) = n\<close> ell2_to_vec_well_defined_index eq_vecI index_add_vec(1) index_add_vec(2) plus_ell2.rep_eq)
qed

lemma ell2_to_vec_smult:
  fixes x :: \<open>nat ell2\<close> and c :: complex and n :: nat 
  shows \<open>ell2_to_vec n (c *\<^sub>C x) = c \<cdot>\<^sub>v (ell2_to_vec n x)\<close>
  unfolding ell2_to_vec_def fun_to_ell2_def smult_vec_def
  apply auto
  apply transfer
  apply auto
  unfolding mk_vec_def
  by auto

section \<open>Topological properties of finite dimensional subspaces of nat ell2\<close>

lemma vec_to_ell2_id:
  \<open>j < n \<Longrightarrow> (vec_to_ell2 (vec n (Rep_ell2 (ket j)))) = (ket j)\<close>
proof-
  assume \<open>j < n\<close>
  hence  \<open>Rep_ell2 ( (vec_to_ell2 (vec n (Rep_ell2 (ket j)))) ) i
     = (Rep_ell2 (ket j)) i\<close>
    for i::nat
    unfolding vec_def mk_vec_def
    apply auto
    apply transfer
  proof-
    fix j n i :: nat
    assume \<open>j < n\<close>
    have \<open>dim_vec
                (Abs_vec
                  (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                          else undef_vec (i - id n))) = n\<close>
    proof-
      have \<open>(n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                          else undef_vec (i - id n)) \<in> {(n, mk_vec n f) |n f. True}\<close>
        unfolding mk_vec_def
        apply auto
        by (metis id_apply)          
      hence \<open>Rep_vec
          (Abs_vec
                  (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                          else undef_vec (i - id n)))
    = (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                          else undef_vec (i - id n))\<close>
        using Abs_vec_inverse 
        by blast
      moreover have \<open>fst (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                          else undef_vec (i - id n)) = n\<close>
        by simp
      ultimately have \<open>fst ( Rep_vec
          (Abs_vec
                  (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                          else undef_vec (i - id n))) ) = n\<close>
        by smt
      thus ?thesis 
        by (simp add: dim_vec.rep_eq) 
    qed
    moreover have \<open>(if i < n
        then vec_index (Abs_vec
              (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                      else undef_vec (i - id n)) ) i
        else 0) =
       (if j = i then 1 else 0)\<close>
    proof(cases \<open>i < n\<close>)
      case True
      show ?thesis
      proof(cases \<open>j = i\<close>)
        case True
        have \<open>(if i < n
     then vec_index (Abs_vec
           (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                   else undef_vec (i - id n)) ) i
     else 0) = 1\<close>
        proof-
          have \<open>id (\<lambda>y. if j = y then 1 else 0) i  = 1\<close>
            using \<open>j = i\<close> by simp
          hence \<open>(\<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                   else undef_vec (i - id n)) i  = 1\<close>
            using \<open>i < n\<close>
            by simp
          hence \<open>(n , (\<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                   else undef_vec (i - id n)) i) = (n, 1)\<close>
            by simp
          have \<open>vec_index (Abs_vec (n , (\<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                   else undef_vec (i - id n)))) i = 1\<close>
            unfolding vec_index_def
            apply auto
          proof-
            have \<open>Rep_vec
          (Abs_vec
            (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n)))
            = (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n))\<close>
            proof-
              have \<open>(n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n)) \<in> {(n, mk_vec n f) |n f. True}\<close>
                unfolding mk_vec_def 
                apply auto
                by (metis id_apply)                
              thus ?thesis
                using Abs_vec_inverse by blast
            qed
            moreover have \<open>snd (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n)) = (\<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n))\<close>
              by simp
            ultimately show  \<open>snd (Rep_vec
          (Abs_vec
            (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n)))) i = 1\<close>
              using  \<open>(n , (\<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                   else undef_vec (i - id n)) i) = (n, 1)\<close>
              by (simp add: \<open>Rep_vec (Abs_vec (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i else undef_vec (i - id n))) = (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i else undef_vec (i - id n))\<close> True)
          qed
          thus ?thesis
            using True \<open>j < n\<close> by auto 
        qed
        moreover have \<open>(if j = i then 1 else 0)  = 1\<close>
          using \<open>j = i\<close>
          by simp
        ultimately show ?thesis 
          by auto    
      next
        case False
        have \<open>(if i < n
     then vec_index (Abs_vec
           (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                   else undef_vec (i - id n)) ) i
     else 0) = 0\<close>
        proof-
          have \<open>id (\<lambda>y. if j = y then 1 else 0) i  = 0\<close>
            using \<open>j \<noteq> i\<close> by simp
          hence \<open>(\<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                   else undef_vec (i - id n)) i  = 0\<close>
            using \<open>i < n\<close>
            by simp
          hence \<open>(n , (\<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                   else undef_vec (i - id n)) i) = (n, 0)\<close>
            by simp
          have \<open>vec_index (Abs_vec (n , (\<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                   else undef_vec (i - id n)))) i = 0\<close>
            unfolding vec_index_def
            apply auto
          proof-
            have \<open>Rep_vec
          (Abs_vec
            (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n)))
            = (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n))\<close>
            proof-
              have \<open>(n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n)) \<in> {(n, mk_vec n f) |n f. True}\<close>
                unfolding mk_vec_def 
                apply auto
                by (metis id_apply)                
              thus ?thesis
                using Abs_vec_inverse by blast
            qed
            moreover have \<open>snd (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n)) = (\<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n))\<close>
              by simp
            ultimately show  \<open>snd (Rep_vec
          (Abs_vec
            (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                    else undef_vec (i - id n)))) i = 0\<close>
              using  \<open>(n , (\<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                   else undef_vec (i - id n)) i) = (n, 0)\<close>
              by (simp add: \<open>Rep_vec (Abs_vec (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i else undef_vec (i - id n))) = (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i else undef_vec (i - id n))\<close> True)
          qed
          thus ?thesis
            by (simp add: \<open>vec_index (Abs_vec (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i else undef_vec (i - id n))) i = 0\<close>)            
        qed
        thus ?thesis
          by (simp add: False) 
      qed
    next
      case False
      then show ?thesis
        using \<open>j < n\<close> by auto 
    qed
    ultimately show \<open>(if i < dim_vec
                (Abs_vec
                  (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                          else undef_vec (i - id n)))
        then vec_index (Abs_vec
              (n, \<lambda>i. if i < n then id (\<lambda>y. if j = y then 1 else 0) i
                      else undef_vec (i - id n)) ) 
             i
        else 0) =
       (if j = i then 1 else 0)\<close>
      by smt
  qed
  hence \<open>Rep_ell2 ( (vec_to_ell2 (vec n (Rep_ell2 (ket j)))) )
     = (Rep_ell2 (ket j))\<close>
    by blast
  thus ?thesis using Rep_ell2_inject by blast 
qed

text \<open>final_trunc x0 x1 x2 ... x(n-1) = x0 x1 x2 ... x(n-2)\<close>
definition final_trunc :: \<open>complex vec \<Rightarrow> complex vec\<close> where
  \<open>final_trunc v = vec (dim_vec v - 1) (vec_index v)\<close>

text \<open>final_add x0 x1 x2 ... x(n-1) = x0 x1 x2 ... x(n-1) 0\<close>
definition final_add :: \<open>complex vec \<Rightarrow> complex vec\<close> where
  \<open>final_add v = vec (dim_vec v + 1) 
(\<lambda> i. if i < dim_vec v then vec_index v i else 0)\<close>

lemma final_trunc_add:
  \<open>dim_vec v \<ge> 1 \<Longrightarrow> (final_add \<circ> final_trunc) v = vec (dim_vec v) 
(\<lambda> i. if i < (dim_vec v)-1 then vec_index v i else 0)\<close>
  unfolding final_trunc_def final_add_def
  by auto

lemma final_add_dim:
  \<open>(dim_vec (final_add x)) = Suc (dim_vec x)\<close>
  unfolding final_add_def by auto  

lemma final_add_clinear_add:
  fixes x y :: \<open>complex vec\<close>
  assumes \<open>dim_vec x = dim_vec y\<close>
  shows \<open>final_add (x + y) = final_add x + final_add y\<close>
  unfolding final_add_def
  using plus_vec_def
  apply auto
  by (simp add: Matrix.vec_eq_iff assms)



lemma final_add_clinear_smult:
  fixes x :: \<open>complex vec\<close> and c :: complex
  shows \<open>final_add (c \<cdot>\<^sub>v x) = c \<cdot>\<^sub>v final_add x\<close>
  unfolding final_add_def
  using smult_vec_def
  by auto

lemma final_add_clinear:
  fixes f :: \<open>complex vec \<Rightarrow> 'a::complex_normed_vector\<close>
    and n :: nat
  assumes \<open>clinear_vec (Suc n) f\<close>
  shows  \<open>clinear_vec n (f \<circ> final_add)\<close>
proof
  show "(f \<circ> final_add) (x + y) = (f \<circ> final_add) x + (f \<circ> final_add) y"
    if "dim_vec (x::complex Matrix.vec) = n"
      and "dim_vec (y::complex Matrix.vec) = n"
    for x :: "complex Matrix.vec"
      and y :: "complex Matrix.vec"
  proof-
    have \<open>dim_vec x = dim_vec y\<close>
      by (simp add: that(1) that(2))
    hence \<open>final_add (x + y) = final_add x + final_add y\<close>
      by (simp add: final_add_clinear_add)
    hence \<open>f (final_add (x + y)) = f (final_add x + final_add y)\<close>
      by simp
    also have \<open>f (final_add x + final_add y) = f (final_add x) +  f (final_add y)\<close>
      using \<open>clinear_vec (Suc n) f\<close>
      by (simp add: clinear_vec_def final_add_dim that(1) that(2))
    finally show ?thesis by simp
  qed

  show "(f \<circ> final_add) (c \<cdot>\<^sub>v x) = c *\<^sub>C (f \<circ> final_add) x"
    if "dim_vec (x::complex Matrix.vec) = n"
    for c :: complex
      and x :: "complex Matrix.vec"
  proof-
    have \<open>dim_vec (final_add x) = Suc n\<close>
      using \<open>dim_vec x = n\<close>
      by (simp add: final_add_dim)      
    have \<open>final_add (c \<cdot>\<^sub>v x) = c \<cdot>\<^sub>v (final_add x)\<close>
      by (simp add: final_add_clinear_smult)
    hence \<open>f (final_add (c \<cdot>\<^sub>v x)) = f (c \<cdot>\<^sub>v (final_add x))\<close>
      by simp
    also have \<open>... = c *\<^sub>C f (final_add x)\<close>
      using \<open>clinear_vec (Suc n) f\<close>  \<open>dim_vec (final_add x) = Suc n\<close> clinear_vec.mults by blast
    finally show ?thesis by simp
  qed
qed

lemma trunc_clinear_vec:
  fixes f :: \<open>complex vec \<Rightarrow> 'a::complex_normed_vector\<close>
    and n :: nat
  assumes \<open>clinear_vec (Suc n) f\<close>
  shows \<open>\<exists> g. clinear_vec n g \<and> 
        (\<exists> t. \<forall> v. \<exists> c. dim_vec v = Suc n \<longrightarrow> f v =  c *\<^sub>C t + g (final_trunc v))\<close>
proof
  define g where \<open>g = f \<circ> final_add\<close>
  have \<open>clinear_vec n g\<close>
    using  \<open>clinear_vec (Suc n) f\<close> \<open>g = f \<circ> final_add\<close> final_add_clinear
    unfolding g_def
    by blast
  moreover have \<open>\<exists>t. \<forall>v. \<exists>c. dim_vec v = Suc n \<longrightarrow> f v = c *\<^sub>C t + g (final_trunc v)\<close>
  proof-
    have \<open>\<exists>c. dim_vec v = Suc n \<longrightarrow> f v = c *\<^sub>C f ( unit_vec (Suc n) n ) + g (final_trunc v)\<close>
      for v
    proof-
      have \<open>dim_vec v = Suc n \<Longrightarrow> f v = (vec_index v n) *\<^sub>C f ( unit_vec (Suc n) n ) + g (final_trunc v)\<close>
      proof-
        assume \<open>dim_vec v = Suc n\<close>
        have \<open>f v = (vec_index v n) *\<^sub>C f ( unit_vec (Suc n) n )
                   + f ( final_add (final_trunc v) )\<close>
        proof-
          have \<open>(vec_index v n) *\<^sub>C f ( unit_vec (Suc n) n )
                  = f ( vec (Suc n) ( \<lambda> i. (
                if i < n then 0 else (vec_index v n) ) ) )\<close>
          proof-
            have \<open>(vec_index v n) *\<^sub>C f ( unit_vec (Suc n) n )
              = f ( (vec_index v n) \<cdot>\<^sub>v (unit_vec (Suc n) n) )\<close>
              using \<open>clinear_vec (Suc n) f\<close>
              unfolding clinear_vec_def
              by simp
            moreover have \<open>(vec_index v n) \<cdot>\<^sub>v (unit_vec (Suc n) n)
      = vec (Suc n) ( \<lambda> i. (if i < n then 0 else (vec_index v n) ) )\<close>
            proof-
              have \<open>(unit_vec (Suc n) n)
         =  vec (Suc n) ( \<lambda> i. (if i < n then 0 else 1 ) )\<close>
                unfolding unit_vec_def
                by auto
              hence \<open>(vec_index v n) \<cdot>\<^sub>v (unit_vec (Suc n) n)
      = (vec_index v n) \<cdot>\<^sub>v vec (Suc n) ( \<lambda> i. (if i < n then 0 else 1 ) )\<close>
                by auto
              thus ?thesis unfolding smult_vec_def by auto
            qed
            ultimately show ?thesis by simp
          qed
          moreover have \<open>f ( final_add (final_trunc v) )
                = f ( vec (Suc n) ( \<lambda> i. (
                if i < n then vec_index v i else 0 ) ) )\<close>
          proof-
            have \<open>final_add (final_trunc v) 
          =  vec (Suc n) ( \<lambda> i. ( if i < n then vec_index v i else 0 ) )\<close>
              using final_trunc_add
              by (simp add: \<open>dim_vec v = Suc n\<close>) 
            thus ?thesis by simp
          qed
          ultimately have \<open>(vec_index v n) *\<^sub>C f ( unit_vec (Suc n) n )
                   + f ( final_add (final_trunc v) )
            = f ( vec (Suc n) ( \<lambda> i. (
                if i < n then 0 else (vec_index v n) ) ) )
            + f ( vec (Suc n) ( \<lambda> i. (
                if i < n then vec_index v i else 0 ) ) )\<close>
            by simp
          hence \<open>(vec_index v n) *\<^sub>C f ( unit_vec (Suc n) n )
                   + f ( final_add (final_trunc v) )
            = f ( vec (Suc n) ( \<lambda> i. (
                if i < n then 0 else (vec_index v n) ) ) 
            +  vec (Suc n) ( \<lambda> i. (
                if i < n then vec_index v i else 0 ) ) )\<close>
            using \<open>clinear_vec (Suc n) f\<close>
            unfolding clinear_vec_def
            by auto
          moreover have \<open>vec (Suc n) ( \<lambda> i. (
                if i < n then 0 else (vec_index v n) ) ) 
            +  vec (Suc n) ( \<lambda> i. (
                if i < n then vec_index v i else 0 ) )
            =  vec (Suc n) ( \<lambda> i. (
                if i < n then 0 + vec_index v i
                   else (vec_index v n) + 0 ) )\<close>
            using plus_vec_def
            by auto
          ultimately have \<open>(vec_index v n) *\<^sub>C f ( unit_vec (Suc n) n )
                   + f ( final_add (final_trunc v) )
            = f ( vec (Suc n) ( \<lambda> i. (
                if i < n then 0 + vec_index v i
                   else (vec_index v n) + 0 ) ) )\<close>
            by simp
          moreover have \<open>vec (Suc n) ( \<lambda> i. (
                if i < n then 0 + vec_index v i
                   else (vec_index v n) + 0 ) ) = v\<close>
            unfolding vec_def mk_vec_def id_def
            apply auto
          proof-
            have \<open>dim_vec (Abs_vec (Suc n,
      \<lambda>i. if i < Suc n then if i < n then  0 + vec_index v i 
          else vec_index v n + 0
          else undef_vec (i - Suc n))) = dim_vec v\<close>
              using \<open>dim_vec v = Suc n\<close>
              apply auto
              apply transfer
              unfolding dim_vec_def
              apply auto
            proof-
              show \<open>fst (Rep_vec (Abs_vec (Suc n,
                    \<lambda>i. if i < Suc n
                        then if i < n
                             then 0 +
               snd (Suc n, mk_vec (Suc n) f) i
                             else snd (Suc n, mk_vec (Suc n) f)
             n + 0 else undef_vec (i - Suc n)))) = Suc n\<close>
                for n::nat and f::\<open>nat \<Rightarrow> complex\<close>
              proof-
                have \<open>fst (Suc n,
                    \<lambda>i. if i < Suc n
                        then if i < n
                             then 0 +
               snd (Suc n, mk_vec (Suc n) f) i
                             else snd (Suc n, mk_vec (Suc n) f)
             n + 0 else undef_vec (i - Suc n)) = Suc n\<close>
                  by simp
                moreover have \<open>(Rep_vec (Abs_vec (Suc n,
                    \<lambda>i. if i < Suc n
                        then if i < n
                             then 0 +
               snd (Suc n, mk_vec (Suc n) f) i
                             else snd (Suc n, mk_vec (Suc n) f)
             n + 0 else undef_vec (i - Suc n))))
          = (Suc n, \<lambda>i. if i < Suc n
                        then if i < n
                             then 0 +
               snd (Suc n, mk_vec (Suc n) f) i
                             else snd (Suc n, mk_vec (Suc n) f)
             n + 0 else undef_vec (i - Suc n))\<close>
                proof-
                  have \<open>(Suc n, \<lambda>i. if i < Suc n
                        then if i < n
                             then 0 +
               snd (Suc n, mk_vec (Suc n) f) i
                             else snd (Suc n, mk_vec (Suc n) f)
             n + 0 else undef_vec (i - Suc n))
                    \<in> {(n, mk_vec n f) |n f. True}\<close>
                    unfolding mk_vec_def by auto
                  thus ?thesis using Abs_vec_inverse by blast
                qed
                ultimately show ?thesis 
                  by simp
              qed
            qed
            moreover have \<open>vec_index (Abs_vec (Suc n,
      \<lambda>i. if i < Suc n then if i < n then  0 + vec_index v i 
          else vec_index v n + 0
          else undef_vec (i - Suc n))) = vec_index v\<close>
              using \<open>dim_vec v = Suc n\<close>
              unfolding vec_index_def
              apply auto
              apply transfer
              unfolding dim_vec_def id_def map_fun_def mk_vec_def
              apply auto
            proof-
              show \<open>snd (Rep_vec (Abs_vec (Suc n,\<lambda>i. if i < Suc n
                        then if i < n then 0 +((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) i
                             else ((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) n + 0
                        else undef_vec (i - Suc n)))) =
           (\<lambda>i. if i < Suc n then f i else undef_vec (i - Suc n))\<close>
                for n :: nat and f :: \<open>nat \<Rightarrow> complex\<close>
              proof-
                have \<open>snd (Suc n, \<lambda>i. if i < Suc n
                        then if i < n then 0 +((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) i
                             else ((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) n + 0
                        else undef_vec (i - Suc n)) =
           (\<lambda>i. if i < Suc n then f i else undef_vec (i - Suc n))\<close>
                proof-
                  have \<open>(if i < Suc n
                        then if i < n then 0 +((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) i
                             else ((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) n + 0
                        else undef_vec (i - Suc n))
= (if i < Suc n then f i else undef_vec (i - Suc n))\<close>
                    for i :: nat
                    apply auto
                  proof-
                    assume \<open> \<not> i < n\<close> and \<open>i < Suc n\<close>
                    from \<open> \<not> i < n\<close>
                    have \<open>i \<ge> n\<close> by simp
                    hence \<open>n = i\<close>  using \<open>i < Suc n\<close>
                      by simp
                    thus \<open>f n = f i\<close> by simp
                  qed
                  thus ?thesis by simp
                qed
                moreover have \<open> (Rep_vec (Abs_vec (Suc n,\<lambda>i. if i < Suc n
                        then if i < n then 0 +((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) i
                             else ((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) n + 0
                        else undef_vec (i - Suc n))))
=  (Suc n,\<lambda>i. if i < Suc n
                        then if i < n then 0 +((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) i
                             else ((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) n + 0
                        else undef_vec (i - Suc n))\<close>
                proof-
                  have \<open>(Suc n,\<lambda>i. if i < Suc n
                        then if i < n then 0 +((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) i
                             else ((\<lambda>x. x) \<circ> snd \<circ> (\<lambda>x. x)) (Suc n, \<lambda>i.
    if i < Suc n then f i else undef_vec (i - Suc n)) n + 0
                        else undef_vec (i - Suc n))
           \<in> {(n, mk_vec n f) |n f. True}\<close>
                    unfolding mk_vec_def by auto
                  thus ?thesis using Abs_vec_inverse
                    by blast
                qed
                ultimately show ?thesis by simp
              qed
            qed
            ultimately show \<open>Abs_vec (Suc n,
      \<lambda>i. if i < Suc n then if i < n then  0 + vec_index v i 
          else vec_index v n + 0
          else undef_vec (i - Suc n)) = v\<close>
              by (simp add: eq_vecI)              
          qed
          ultimately show ?thesis by simp
        qed
        hence \<open>f v = (vec_index v n) *\<^sub>C f ( unit_vec (Suc n) n ) + g (final_trunc v)\<close>
          unfolding g_def by simp
        thus ?thesis by blast
      qed
      thus ?thesis by blast
    qed
    thus ?thesis by blast
  qed
  ultimately show "clinear_vec n g \<and> (\<exists>t. \<forall>v. \<exists>c. dim_vec v = Suc n \<longrightarrow> f v = c *\<^sub>C t + g (final_trunc v))"
    by blast
qed

lemma fun_to_ell2_ell2_to_vec:
  \<open>(fun_to_ell2 n f) x = f (ell2_to_vec n x)\<close>
  unfolding fun_to_ell2_def ell2_to_vec_def vec_def mk_vec_def
  by auto

lemma fun_to_ell2_final_trunc_suc:
  fixes f :: \<open>complex vec \<Rightarrow> 'a::complex_normed_vector\<close>
  shows \<open>fun_to_ell2 n f = (\<lambda> t. f (final_trunc (ell2_to_vec (Suc n) t)))\<close>
proof-
  have \<open>(Abs_vec (n, \<lambda>i. if i < n then Rep_ell2 x i else undef_vec (i - n)))
= Abs_vec
             (fst (Rep_vec
                    (Abs_vec
                      (Suc n,
                       \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n)))) -
              Suc 0,
              \<lambda>i. if i < fst (Rep_vec
                               (Abs_vec
                                 (Suc n,
                                  \<lambda>i. if i < Suc n then Rep_ell2 x i
                                      else undef_vec (i - Suc n)))) -
                         Suc 0
                  then snd (Rep_vec
                             (Abs_vec
                               (Suc n,
                                \<lambda>i. if i < Suc n then Rep_ell2 x i
                                    else undef_vec (i - Suc n))))
                        i
                  else undef_vec
                        (i -
                         (fst (Rep_vec
                                (Abs_vec
                                  (Suc n,
                                   \<lambda>i. if i < Suc n then Rep_ell2 x i
                                       else undef_vec (i - Suc n)))) -
                          Suc 0)))\<close>
    for x
  proof-
    have \<open>( (n, \<lambda>i. if i < n then Rep_ell2 x i else undef_vec (i - n)))
=  (fst (Rep_vec
                    (Abs_vec
                      (Suc n,
                       \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n)))) -
              Suc 0,
              \<lambda>i. if i < fst (Rep_vec
                               (Abs_vec
                                 (Suc n,
                                  \<lambda>i. if i < Suc n then Rep_ell2 x i
                                      else undef_vec (i - Suc n)))) -
                         Suc 0
                  then snd (Rep_vec
                             (Abs_vec
                               (Suc n,
                                \<lambda>i. if i < Suc n then Rep_ell2 x i
                                    else undef_vec (i - Suc n))))
                        i
                  else undef_vec
                        (i -
                         (fst (Rep_vec
                                (Abs_vec
                                  (Suc n,
                                   \<lambda>i. if i < Suc n then Rep_ell2 x i
                                       else undef_vec (i - Suc n)))) -
                          Suc 0)))\<close>
    proof-
      have \<open>n = fst (Rep_vec
                    (Abs_vec
                      (Suc n,
                       \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n)))) -
              Suc 0\<close>
      proof-
        have \<open>(Suc n, \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n)) \<in>
             {(n, mk_vec n f) |n f. True}\<close>
          unfolding mk_vec_def
          by auto
        hence \<open>Rep_vec ( Abs_vec ( (Suc n, \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n)) ))
 = (Suc n, \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n))\<close>
          using Abs_vec_inverse
          by blast
        hence \<open>fst ( Rep_vec ( Abs_vec ( (Suc n, \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n)) )) )
 = fst (Suc n, \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n))\<close>
          by simp
        also have \<open>... = Suc n\<close>
          by simp
        finally show ?thesis by simp
      qed
      moreover have \<open> (if i < n then Rep_ell2 x i else undef_vec (i - n)) 
              = ( if i < fst (Rep_vec
                               (Abs_vec
                                 (Suc n,
                                  \<lambda>i. if i < Suc n then Rep_ell2 x i
                                      else undef_vec (i - Suc n)))) -
                         Suc 0
                  then snd (Rep_vec
                             (Abs_vec
                               (Suc n,
                                \<lambda>i. if i < Suc n then Rep_ell2 x i
                                    else undef_vec (i - Suc n))))
                        i
                  else undef_vec
                        (i -
                         (fst (Rep_vec
                                (Abs_vec
                                  (Suc n,
                                   \<lambda>i. if i < Suc n then Rep_ell2 x i
                                       else undef_vec (i - Suc n)))) -
                          Suc 0)))\<close>
        for i
      proof-
        have \<open> (if i < n then Rep_ell2 x i else undef_vec (i - n)) 
            = ( if i < n then snd (Rep_vec
                             (Abs_vec
                               (Suc n,
                                \<lambda>i. if i < Suc n then Rep_ell2 x i
                                    else undef_vec (i - Suc n)))) i
                  else undef_vec
                        (i -
                         (fst (Rep_vec
                                (Abs_vec
                                  (Suc n,
                                   \<lambda>i. if i < Suc n then Rep_ell2 x i
                                       else undef_vec (i - Suc n)))) -
                          Suc 0)))\<close>
        proof-
          have \<open>i < n \<Longrightarrow> Rep_ell2 x i 
              =  snd (Rep_vec (Abs_vec
                               (Suc n,
                                \<lambda>i. if i < Suc n then Rep_ell2 x i
                                    else undef_vec (i - Suc n)))) i\<close>
            apply transfer
          proof-
            fix x::\<open>nat \<Rightarrow> complex\<close> and i n::nat
            assume \<open>i < n\<close> and \<open>has_ell2_norm x\<close>
            from \<open>i < n\<close>
            have \<open>x i = snd (Suc n, \<lambda>i. if i < Suc n then x i else undef_vec (i - Suc n)) i\<close>
              by auto
            moreover have \<open>(Suc n, \<lambda>i. if i < Suc n then x i else undef_vec (i - Suc n)) 
                \<in> {(n, mk_vec n f) |n f. True}\<close>
              unfolding mk_vec_def
              by auto
            ultimately show \<open>x i = snd (Rep_vec
             (Abs_vec (Suc n, \<lambda>i. if i < Suc n then x i else undef_vec (i - Suc n)))) i\<close>
              using Abs_vec_inverse by fastforce
          qed
          moreover have \<open>i \<ge> n \<Longrightarrow> undef_vec (i - n) = 
                undef_vec (i -
                         (fst (Rep_vec
                                (Abs_vec
                                  (Suc n,
                                   \<lambda>i. if i < Suc n then Rep_ell2 x i
                                       else undef_vec (i - Suc n)))) - Suc 0))\<close>
            using \<open>n = fst (Rep_vec
                    (Abs_vec
                      (Suc n,
                       \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n)))) -
              Suc 0\<close> by simp
          ultimately show ?thesis by auto
        qed
        thus ?thesis using \<open>n = fst (Rep_vec
                    (Abs_vec
                      (Suc n,
                       \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n)))) -
              Suc 0\<close>
          by simp
      qed
      ultimately show ?thesis 
        by auto
    qed
    hence \<open>(Abs_vec (n, \<lambda>i. if i < n then Rep_ell2 x i else undef_vec (i - n)))
= Abs_vec
             (fst (Rep_vec
                    (Abs_vec
                      (Suc n,
                       \<lambda>i. if i < Suc n then Rep_ell2 x i else undef_vec (i - Suc n)))) -
              Suc 0,
              \<lambda>i. if i < fst (Rep_vec
                               (Abs_vec
                                 (Suc n,
                                  \<lambda>i. if i < Suc n then Rep_ell2 x i
                                      else undef_vec (i - Suc n)))) -
                         Suc 0
                  then snd (Rep_vec
                             (Abs_vec
                               (Suc n,
                                \<lambda>i. if i < Suc n then Rep_ell2 x i
                                    else undef_vec (i - Suc n))))
                        i
                  else undef_vec
                        (i -
                         (fst (Rep_vec
                                (Abs_vec
                                  (Suc n,
                                   \<lambda>i. if i < Suc n then Rep_ell2 x i
                                       else undef_vec (i - Suc n)))) -
                          Suc 0)))\<close>
      by simp
    thus ?thesis by blast
  qed
  hence \<open>(\<lambda>x. f (Abs_vec (n, \<lambda>i. if i < n then Rep_ell2 x i else undef_vec (i - n)))) =
    (\<lambda>t. f (Abs_vec
             (fst (Rep_vec
                    (Abs_vec
                      (Suc n,
                       \<lambda>i. if i < Suc n then Rep_ell2 t i else undef_vec (i - Suc n)))) -
              Suc 0,
              \<lambda>i. if i < fst (Rep_vec
                               (Abs_vec
                                 (Suc n,
                                  \<lambda>i. if i < Suc n then Rep_ell2 t i
                                      else undef_vec (i - Suc n)))) -
                         Suc 0
                  then snd (Rep_vec
                             (Abs_vec
                               (Suc n,
                                \<lambda>i. if i < Suc n then Rep_ell2 t i
                                    else undef_vec (i - Suc n))))
                        i
                  else undef_vec
                        (i -
                         (fst (Rep_vec
                                (Abs_vec
                                  (Suc n,
                                   \<lambda>i. if i < Suc n then Rep_ell2 t i
                                       else undef_vec (i - Suc n)))) -
                          Suc 0)))))\<close>
    by simp    
  thus ?thesis 
    unfolding  fun_to_ell2_def final_trunc_def vec_def mk_vec_def id_def vec_index_def
      dim_vec_def ell2_to_vec_def
    by auto
qed


lemma finite_complex_rank_ell2_map_left_vec_exact:
  fixes n :: nat
  shows \<open>\<forall> f :: complex vec \<Rightarrow> 'a::complex_normed_vector.
             clinear_vec n f \<longrightarrow> complex_gen n (fun_to_ell2 n f)\<close>
proof(induction n)
  case 0
  have \<open>clinear_vec 0 f \<Longrightarrow> (complex_gen 0 (fun_to_ell2 0 f))\<close>
    for f :: \<open>complex vec \<Rightarrow> 'a\<close>
  proof-
    assume \<open>clinear_vec 0 f\<close>
    have \<open>f (Abs_vec (0, mk_vec 0 (Rep_ell2 x))) = 0\<close>
      for x
    proof-
      have \<open>Abs_vec (0, undef_vec) = vNil\<close>
        unfolding vec_def
        using Abs_vec_inject
        by (simp add: mk_vec_def)        
      hence \<open>dim_vec ( Abs_vec (0, mk_vec 0 (Rep_ell2 x)) ) = 0\<close>
        unfolding mk_vec_def
        by simp
      hence \<open>f (( Abs_vec (0, mk_vec 0 (Rep_ell2 x)) ) + ( Abs_vec (0, mk_vec 0 (Rep_ell2 x)) )) 
        = f ( Abs_vec (0, mk_vec 0 (Rep_ell2 x)) ) + f ( Abs_vec (0, mk_vec 0 (Rep_ell2 x)) )\<close>
        using \<open>clinear_vec 0 f\<close>
          clinear_vec.add by blast 
      moreover have \<open>( Abs_vec (0, mk_vec 0 (Rep_ell2 x)) ) + ( Abs_vec (0, mk_vec 0 (Rep_ell2 x))) 
                = ( Abs_vec (0, mk_vec 0 (Rep_ell2 x)) )\<close>
        using \<open>dim_vec (Abs_vec (0, mk_vec 0 (Rep_ell2 x))) = 0\<close> by auto
      ultimately have \<open>f ( Abs_vec (0, mk_vec 0 (Rep_ell2 x)) ) = 0\<close>
        by simp
      thus ?thesis
        by simp 
    qed
    hence \<open>fun_to_ell2 0 f x = 0\<close>
      for x
      unfolding fun_to_ell2_def
      unfolding vec_def
      by simp
    hence \<open>complex_gen 0 (fun_to_ell2 0 f)\<close>
      by simp
    thus ?thesis
      by blast 
  qed
  thus ?case by blast 
next
  case (Suc n)
  have \<open>clinear_vec (Suc n) f \<Longrightarrow> complex_gen (Suc n) (fun_to_ell2 (Suc n) f)\<close>
    for f :: \<open>complex vec \<Rightarrow> 'a\<close>
  proof-
    assume \<open>clinear_vec (Suc n) f\<close>
    hence \<open>\<exists> g. clinear_vec n g \<and> 
        (\<exists> t. \<forall> v. \<exists> c. dim_vec v = Suc n \<longrightarrow> f v =  c *\<^sub>C t + g (final_trunc v))\<close>
      using trunc_clinear_vec by blast
    then obtain g where \<open>clinear_vec n g\<close>
      and \<open>\<exists> t. \<forall> v. \<exists> c. dim_vec v = Suc n \<longrightarrow> f v =  c *\<^sub>C t + g (final_trunc v)\<close>
      by blast
    have \<open>complex_gen n (\<lambda> t. g (final_trunc (ell2_to_vec (Suc n) t)))\<close>
    proof-
      have \<open>complex_gen n (fun_to_ell2 n g)\<close>
        using \<open>clinear_vec n g\<close>
        by (simp add: Suc.IH)
      moreover have \<open>fun_to_ell2 n g = (\<lambda> t. g (final_trunc (ell2_to_vec (Suc n) t)))\<close>
        by (rule fun_to_ell2_final_trunc_suc)
      ultimately show ?thesis by simp
    qed
    moreover have \<open>\<exists> t. \<forall> x. \<exists> c. (fun_to_ell2 (Suc n) f) x =  c *\<^sub>C t + (\<lambda> s. g (final_trunc (ell2_to_vec (Suc n) s)) ) x\<close>
    proof-
      from \<open>\<exists> t. \<forall> v. \<exists> c. dim_vec v = Suc n \<longrightarrow> f v =  c *\<^sub>C t + g (final_trunc v)\<close>
      obtain t where \<open>\<forall> v. \<exists> c. dim_vec v = Suc n \<longrightarrow> f v =  c *\<^sub>C t + g (final_trunc v)\<close>
        by blast
      have \<open>\<exists> c. (fun_to_ell2 (Suc n) f) x =  c *\<^sub>C t + (\<lambda> s. g (final_trunc (ell2_to_vec (Suc n) s)) ) x\<close>
        for x::\<open>nat ell2\<close>
      proof-
        have \<open>(fun_to_ell2 (Suc n) f) x = f (ell2_to_vec (Suc n) x)\<close>
          using fun_to_ell2_ell2_to_vec
          by blast
        hence \<open>(fun_to_ell2 (Suc n) f) x = f (ell2_to_vec (Suc n) x)\<close>
          by simp
        hence \<open>\<exists> c. (fun_to_ell2 (Suc n) f) x =  c *\<^sub>C t + g (final_trunc (ell2_to_vec (Suc n) x))\<close>
          using  \<open>\<forall> v. \<exists> c. dim_vec v = Suc n \<longrightarrow> f v =  c *\<^sub>C t + g (final_trunc v)\<close>
          by (simp add: ell2_to_vec_well_defined_dim)
        hence \<open>\<exists> c. (fun_to_ell2 (Suc n) f) x =  c *\<^sub>C t + (\<lambda> s. g (final_trunc (ell2_to_vec (Suc n) s)) ) x\<close>
          by auto
        thus ?thesis by blast
      qed
      thus ?thesis by blast
    qed
    ultimately have \<open>complex_gen (Suc n) (fun_to_ell2 (Suc n) f)\<close>
      using complex_gen.simps(2) by blast      
    thus ?thesis by blast
  qed
  thus ?case by blast
qed


lemma clinear_vec_zero:
  fixes n :: nat and f :: \<open>complex vec \<Rightarrow> 'a::complex_normed_vector\<close>
  assumes \<open>clinear_vec n f\<close>
  shows \<open>f (0\<^sub>v n) = 0\<close>
proof-
  have \<open>f (0\<^sub>v n) = f (0\<^sub>v n + 0\<^sub>v n)\<close>
  proof-
    have \<open>dim_vec v = n \<Longrightarrow> (0\<^sub>v n) + v = v\<close>
      for v:: \<open>complex vec\<close> 
      using left_zero_vec unfolding carrier_vec_def
      by auto
    moreover have \<open>dim_vec (0\<^sub>v n) = n\<close>
      by simp
    ultimately have \<open>(0\<^sub>v n) + (0\<^sub>v n) = (0\<^sub>v n::(complex vec))\<close>
      by blast
    thus ?thesis by simp
  qed
  also have \<open>... = f (0\<^sub>v n) + f (0\<^sub>v n)\<close>
    using \<open>clinear_vec n f\<close> clinear_vec.add index_zero_vec(2) by blast 
  finally have \<open>f (0\<^sub>v n) = f (0\<^sub>v n) + f (0\<^sub>v n)\<close> 
    by blast
  thus ?thesis by simp
qed


definition fun_l2 :: \<open>nat \<Rightarrow> (complex vec \<Rightarrow> complex vec) \<Rightarrow> ((nat ell2) \<Rightarrow> (nat ell2))\<close> where
\<open>fun_l2 n f = fun_to_ell2 n ( \<lambda> v::complex vec. vec_to_ell2 (f v) )\<close>

locale clinear_v =
  fixes n :: nat and f :: \<open>complex vec \<Rightarrow> complex vec\<close>
  assumes add:  \<open>\<And> x y. dim_vec x = n \<Longrightarrow> dim_vec y = n \<Longrightarrow> f (x + y) = f x + f y\<close>
    and mults:  \<open>\<And> c. \<And> x. dim_vec x = n \<Longrightarrow> f (c \<cdot>\<^sub>v x) = c \<cdot>\<^sub>v (f x)\<close>

lemma clinear_v_clinear_vec:
  fixes n :: nat and f :: \<open>complex vec \<Rightarrow> complex vec\<close>
  assumes \<open>clinear_v n f\<close>
  shows \<open>clinear_vec n ( \<lambda> v::complex vec. vec_to_ell2 (f v) )\<close>
  proof
  show "vec_to_ell2 (f (x + y)) = vec_to_ell2 (f x) + vec_to_ell2 (f y)"
    if "dim_vec (x::complex Matrix.vec) = n"
      and "dim_vec (y::complex Matrix.vec) = n"
    for x :: "complex Matrix.vec"
      and y :: "complex Matrix.vec"
    using that
    by (metis Matrix.vec_eq_iff assms clinear_v.add index_add_vec(2) ordered_field_class.sign_simps(2) vec_to_ell2_add vec_to_ell2_inj) 

  show "vec_to_ell2 (f (c \<cdot>\<^sub>v x)) = c *\<^sub>C vec_to_ell2 (f x)"
    if "dim_vec (x::complex Matrix.vec) = n"
    for c :: complex
      and x :: "complex Matrix.vec"
    using that assms clinear_v.mults vec_to_ell2_smult by fastforce 
qed

theorem finite_rank_operator_fun_l2:
  fixes n :: nat and f :: \<open>complex vec \<Rightarrow> complex vec\<close>
  assumes \<open>clinear_v n f\<close>
  shows \<open>complex_gen n (fun_l2 n f)\<close>
proof-
  have \<open>clinear_vec n ( \<lambda> v::complex vec. vec_to_ell2 (f v) )\<close>
    using assms clinear_v_clinear_vec by blast
 thus ?thesis unfolding fun_l2_def
   by (simp add: finite_complex_rank_ell2_map_left_vec_exact)
qed

theorem fun_l2_inj:
  fixes n :: nat and f g :: \<open>complex vec \<Rightarrow> complex vec\<close>
  assumes  \<open>fun_l2 n f = fun_l2 n g\<close> and \<open>dim_vec v = n\<close> 
    and \<open>dim_vec (f v) = dim_vec (g v)\<close>
  shows \<open>f v = g v\<close>
proof-
  from \<open>fun_l2 n f = fun_l2 n g\<close>
  have \<open>(\<lambda>v. vec_to_ell2 (f v)) v = (\<lambda>v. vec_to_ell2 (g v)) v\<close>
    unfolding fun_l2_def using fun_to_ell2_inject  \<open>dim_vec v = n\<close>
    by blast
  hence \<open>vec_to_ell2 (f v) = vec_to_ell2 (g v)\<close>
    by blast
  thus ?thesis using vec_to_ell2_inj
    using \<open>dim_vec (f v) = dim_vec (g v)\<close>
    by (metis eq_vecI)    
qed


end

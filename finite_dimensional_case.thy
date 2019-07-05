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

section \<open>Topological properties of finite dimensional subspaces of nat ell2\<close>

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
  assume \<open>\<forall>f. clinear_vec n f \<longrightarrow> complex_gen n (fun_to_ell2 n f)\<close>
  have \<open>clinear_vec (Suc n) f \<Longrightarrow> complex_gen (Suc n) (fun_to_ell2 (Suc n) f)\<close>
    for f :: \<open>complex vec \<Rightarrow> 'a\<close>
  proof-
    assume \<open>clinear_vec (Suc n) f\<close>
    define g :: \<open>nat ell2 \<Rightarrow> 'a\<close> where 
      \<open>g x = (fun_to_ell2 (Suc n) f) (left_shift_ell2 x)\<close> for x
    have \<open>complex_gen n g\<close>
      using g_def
      sorry
    moreover have \<open>\<exists> t. \<forall> x. \<exists> c. (fun_to_ell2 (Suc n) f) x = c *\<^sub>C t + g x\<close>
      sorry
    ultimately have \<open>complex_gen (Suc n) (fun_to_ell2 (Suc n) f)\<close>
      by auto
    thus ?thesis by blast
  qed
  thus ?case by blast 
qed

lemma finite_complex_rank_ell2_map_left_vec:
  fixes n :: nat and f :: \<open>complex vec \<Rightarrow> 'a::complex_normed_vector\<close>
  assumes \<open>clinear_vec n f\<close>
  shows \<open>finite_complex_rank (fun_to_ell2 n f)\<close>
  unfolding finite_complex_rank_def
  using assms finite_complex_rank_ell2_map_left_vec_exact by blast

lemma clinear_ell2_map_left_vec:
  fixes n :: nat and f :: \<open>complex vec \<Rightarrow> 'a::complex_normed_vector\<close>
  assumes \<open>clinear_vec n f\<close>   
  shows \<open>bounded_clinear (fun_to_ell2 n f)\<close>
  using assms finite_complex_rank_ell2_map_left_vec finite_rank_and_linear  clinear_ell2_map_left
  by blast 
  

end

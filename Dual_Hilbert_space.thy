(*  Title:      Dual_Hilbert_space/Dual_Hilbert_space.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

References:             

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}

*)


theory Dual_Hilbert_space
  imports Complex_L2 Hilbert_space_dim "HOL-Library.Adhoc_Overloading" 
    "HOL-Analysis.Abstract_Topology" Extended_Sorry
begin

section \<open>Riesz Frechet representation\<close>

(* NEW *)
lemma bounded_clinearDiff: \<open>clinear A \<Longrightarrow> clinear B \<Longrightarrow> clinear (A - B)\<close>
  by (smt add_diff_add additive.add clinear.axioms(1) clinear.axioms(2) clinearI clinear_axioms_def complex_vector.scale_right_diff_distrib minus_apply)

(* NEW *)
(* The norm of a bouded operator *)
definition norm_bounded::\<open>('a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector) \<Rightarrow> real\<close> where
  \<open>norm_bounded \<equiv> \<lambda> f. Sup{ K | K.  \<forall>x. norm (f x) \<le> norm x * K}\<close>

(* NEW *)
definition proportion :: \<open>('a::complex_vector) set \<Rightarrow> bool\<close> where
  \<open>proportion S =  (
  \<forall> x y. x \<in> S \<and> x \<noteq> 0 \<and> y \<in> S \<and> y \<noteq> 0 \<longrightarrow> (\<exists> k. x = k *\<^sub>C y) 
)\<close>

(* NEW *)
lemma proportion_existence:
  \<open>proportion S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists> t \<in> S. (\<forall> x \<in> S. \<exists> k. x = k *\<^sub>C t)\<close>
  using complex_vector.scale_zero_left ex_in_conv proportion_def
  by metis

(* NEW *)
(* functional *)
type_synonym 'a functional = \<open>'a \<Rightarrow> complex\<close>

(* NEW *)
lemma ker_ortho_nonzero:
  fixes f :: \<open>('a::chilbert_space) functional\<close> and x :: 'a
  assumes \<open>bounded_clinear f\<close> and \<open>x \<noteq> 0\<close> and \<open>x \<in> (orthogonal_complement (ker_op f))\<close> 
  shows \<open>f x \<noteq> 0\<close>
proof(rule classical)
  have \<open>is_subspace (ker_op f)\<close> using \<open>bounded_clinear f\<close>
    by (simp add: ker_op_lin) 
  assume \<open>\<not>(f x \<noteq> 0)\<close>
  hence \<open>x \<in> ker_op f\<close>
    by (simp add: ker_op_def) 
  moreover have \<open>(ker_op f)\<inter>(orthogonal_complement (ker_op f)) = {0}\<close>
    using \<open>is_subspace (ker_op f)\<close>
    by (simp add: ortho_inter_zero) 
  ultimately have  \<open>x \<notin> orthogonal_complement (ker_op f)\<close> using \<open>x \<noteq> 0\<close>
    by (smt Int_iff empty_iff insert_iff) 
  thus ?thesis using \<open>x \<in> orthogonal_complement (ker_op f)\<close> by blast
qed

(* NEW *)
lemma ker_unidim:
  fixes f :: \<open>('a::chilbert_space) functional\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>proportion (orthogonal_complement (ker_op f))\<close>
proof-
  have \<open>x \<in> (orthogonal_complement (ker_op f)) \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<in> orthogonal_complement (ker_op f) \<Longrightarrow> y \<noteq> 0 
    \<Longrightarrow> \<exists> k. x = k *\<^sub>C y\<close>
    for x y
  proof-
    assume \<open>x \<in> (orthogonal_complement (ker_op f))\<close> and \<open>x \<noteq> 0\<close> and \<open>y \<in>(orthogonal_complement (ker_op f))\<close> and \<open>y \<noteq> 0\<close>
    from \<open>bounded_clinear f\<close> 
    have \<open>is_subspace (ker_op f)\<close>
      by (simp add: ker_op_lin)
    hence \<open>is_subspace (orthogonal_complement (ker_op f))\<close>
      by simp
    hence \<open>f x \<noteq> 0\<close>
      using ker_ortho_nonzero \<open>x \<in> (orthogonal_complement (ker_op f))\<close> \<open>x \<noteq> 0\<close> assms by auto 
    from \<open>is_subspace (orthogonal_complement (ker_op f))\<close>
    have \<open>f y \<noteq> 0\<close>
      using ker_ortho_nonzero \<open>y \<in> (orthogonal_complement (ker_op f))\<close> \<open>y \<noteq> 0\<close> assms by auto 
    from  \<open>f x \<noteq> 0\<close>  \<open>f y \<noteq> 0\<close>
    have \<open>\<exists> k. (f x) = k*(f y)\<close>
      by (metis add.inverse_inverse minus_divide_eq_eq)
    then obtain k where \<open>(f x) = k*(f y)\<close>
      by blast
    hence  \<open>(f x) = (f (k *\<^sub>C y))\<close>
      using  \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def
      by (simp add: clinear.scaleC)
    hence  \<open>(f x) - (f (k *\<^sub>C y)) = 0\<close>
      by simp
    hence  \<open>f (x - (k *\<^sub>C y)) = 0\<close>
      using  \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def
      by (simp add: additive.diff clinear.axioms(1))
    hence  \<open>(x - (k *\<^sub>C y)) \<in> ker_op f\<close>
      using ker_op_def
      by (simp add: ker_op_def)
    moreover have \<open>(ker_op f) \<inter> (orthogonal_complement (ker_op f)) = {0}\<close>
      using \<open>is_subspace (ker_op f)\<close>
      by (simp add: ortho_inter_zero)
    moreover have \<open>(x - (k *\<^sub>C y)) \<in> orthogonal_complement (ker_op f)\<close>
    proof-
      from  \<open>y \<in> (orthogonal_complement (ker_op f))\<close>
      have  \<open>k *\<^sub>C y \<in> (orthogonal_complement (ker_op f))\<close>
        using \<open>is_subspace (orthogonal_complement (ker_op f))\<close>
        unfolding is_subspace_def
        by (simp add: is_linear_manifold.smult_closed)
      thus ?thesis using  \<open>x \<in> (orthogonal_complement (ker_op f))\<close>  \<open>is_subspace (orthogonal_complement (ker_op f))\<close>
        unfolding is_subspace_def
        by (metis \<open>is_subspace (ker_op f)\<close> add_diff_cancel_left' calculation(1) diff_add_cancel diff_zero is_linear_manifold.zero is_subspace.subspace proj_uniq)
    qed
    ultimately have \<open>x - (k *\<^sub>C y) = 0\<close>
      using \<open>f (x - k *\<^sub>C y) = 0\<close> \<open>x - k *\<^sub>C y \<in> orthogonal_complement (ker_op f)\<close> 
        assms ker_ortho_nonzero by blast
    thus ?thesis by simp
  qed 
  thus ?thesis
    by (simp add: proportion_def) 
qed


(* NEW *)
(* https://en.wikipedia.org/wiki/Riesz_representation_theorem *)
lemma Riesz_Frechet_representation_existence:
  fixes f::\<open>'a::chilbert_space \<Rightarrow> complex\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>\<exists> t::'a.  \<forall> x :: 'a.  f x = \<langle>t , x\<rangle>\<close>
proof(cases \<open>\<forall> x. f x = 0\<close>)
  case True
  then show ?thesis
    by (metis cinner_zero_left) 
next
  case False
  then show ?thesis 
  proof-
    from \<open>bounded_clinear f\<close>
    have \<open>proportion (orthogonal_complement (ker_op f))\<close>
      by (simp add: ker_unidim)
    moreover have \<open>\<exists> h \<in> (orthogonal_complement (ker_op f)). h \<noteq> 0\<close>
      by (metis ExistenceUniquenessProj False assms diff_0_right ker_op_lin orthogonal_complement_twice projPropertiesA projPropertiesD proj_fixed_points proj_ker_simp)
    ultimately have \<open>\<exists> t. t \<noteq> 0 \<and> (\<forall> x \<in>(orthogonal_complement (ker_op f)). \<exists> k. x = k *\<^sub>C t)\<close>
      by (metis complex_vector.scale_zero_right equals0D proportion_existence) 
    then obtain t where \<open>t \<noteq> 0\<close> and \<open>\<forall> x \<in>(orthogonal_complement (ker_op f)). \<exists> k. x = k *\<^sub>C t\<close>
      by blast
    have  \<open>is_subspace ( orthogonal_complement (ker_op f))\<close>
      by (simp add: assms ker_op_lin)
    hence  \<open>t \<in> (orthogonal_complement (ker_op f))\<close>
    proof-
      have \<open>\<exists> s \<in> (orthogonal_complement (ker_op f)). s \<noteq> 0\<close>
        by (simp add: \<open>\<exists>h\<in>orthogonal_complement (ker_op f). h \<noteq> 0\<close>)
      then obtain s where \<open>s \<in> (orthogonal_complement (ker_op f))\<close> and \<open>s \<noteq> 0\<close>
        by blast
      have \<open>\<exists> k. s = k *\<^sub>C t\<close>
        by (simp add: \<open>\<forall>x\<in>orthogonal_complement (ker_op f). \<exists>k. x = k *\<^sub>C t\<close> \<open>s \<in> orthogonal_complement (ker_op f)\<close>)
      then obtain k where \<open>s = k *\<^sub>C t\<close>
        by blast
      have  \<open>k \<noteq> 0\<close>
        using \<open>s \<noteq> 0\<close>
        by (simp add: \<open>s = k *\<^sub>C t\<close>) 
      hence  \<open>(1/k) *\<^sub>C s = t\<close>
        using  \<open>s = k *\<^sub>C t\<close> by simp
      moreover have \<open>(1/k) *\<^sub>C s \<in>  (orthogonal_complement (ker_op f))\<close>
        using \<open>is_subspace  (orthogonal_complement (ker_op f))\<close>
        unfolding is_subspace_def
        by (simp add: \<open>s \<in> orthogonal_complement (ker_op f)\<close> is_linear_manifold.smult_closed)
      ultimately show ?thesis
        by simp 
    qed
    have \<open>proj (orthogonal_complement (ker_op f)) x = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) *\<^sub>C t\<close>
      for x
      using inner_product_proj \<open>is_subspace  (orthogonal_complement (ker_op f))\<close>
        \<open>\<forall> m \<in>  (orthogonal_complement (ker_op f)). \<exists> k. m = k *\<^sub>C t\<close>  \<open>t \<in> (orthogonal_complement (ker_op f))\<close>
      by (simp add: inner_product_proj \<open>t \<noteq> 0\<close>)
    hence \<open>f (proj (orthogonal_complement (ker_op f)) x) = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) * (f t)\<close>
      for x
      using \<open>bounded_clinear f\<close>
      unfolding bounded_clinear_def
      by (simp add: clinear.scaleC)
    hence \<open>f (proj (orthogonal_complement (ker_op f)) x) = \<langle>(((cnj (f t))/(\<langle>t , t\<rangle>)) *\<^sub>C t) , x\<rangle>\<close>
      for x
    proof-
      from \<open>f (proj (orthogonal_complement (ker_op f)) x) = ((\<langle>t , x\<rangle>)/(\<langle>t , t\<rangle>)) * (f t)\<close>
      have \<open>f (proj (orthogonal_complement (ker_op f)) x) = ((f t)/(\<langle>t , t\<rangle>)) * (\<langle>t , x\<rangle>)\<close>
        by simp
      thus ?thesis
        by auto 
    qed
    moreover have \<open>f (proj ((ker_op f)) x) = 0\<close>
      for x
      using proj_ker_simp
      by (simp add: proj_ker_simp assms) 
    ultimately have \<open>f x = \<langle>(((cnj (f t))/(\<langle>t , t\<rangle>)) *\<^sub>C t) , x\<rangle>\<close>
      for x
      using ortho_decomp_linear
      by (metis add.left_neutral assms ker_op_lin) 
    thus ?thesis
      by blast  
  qed
qed



section \<open> Adjoint \<close>

(* NEW *)
corollary Existence_of_adjoint: 
  \<open>bounded_clinear G \<Longrightarrow> \<exists> F:: 'a::chilbert_space \<Rightarrow> 'b::chilbert_space. ( 
   \<forall> x::'a. \<forall> y::'b. (\<langle>(F x) , y\<rangle>) = (\<langle>x , (G y)\<rangle>)
)\<close>
proof-
  include notation_norm
  assume \<open>bounded_clinear G\<close>
  hence \<open>clinear G\<close>
    unfolding bounded_clinear_def by blast
  have  \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
    using  \<open>bounded_clinear G\<close>
    unfolding bounded_clinear_def
    by (simp add: bounded_clinear_axioms_def) 
  define g :: \<open>'a \<Rightarrow> ('b \<Rightarrow> complex)\<close> where
    \<open>g \<equiv> \<lambda> x. ( \<lambda> y. (\<langle>x , (G y)\<rangle>) )\<close>
  have \<open>bounded_clinear (g x)\<close>
    for x
  proof-
    have \<open>clinear (g x)\<close>
    proof-
      have \<open>(g x) (a + b) = (g x) a + (g x) b\<close>
        for a b
        unfolding  \<open>g \<equiv> \<lambda> x. ( \<lambda> y. (\<langle>x , (G y)\<rangle>) )\<close>
        using  \<open>clinear G\<close>
        by (simp add: additive.add cinner_right_distrib clinear_def)
      moreover have  \<open>(g x) (k *\<^sub>C a) = k *\<^sub>C ((g x) a)\<close>
        for a k
        unfolding g_def
        using  \<open>clinear G\<close>
        by (simp add: clinear.scaleC)
      ultimately show ?thesis
        by (simp add: clinearI) 
    qed
    moreover have \<open>\<exists> M. \<forall> y. \<parallel> (g x) y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
      using \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close> g_def
      by (simp add: \<open>bounded_clinear G\<close> bounded_clinear.bounded bounded_clinear_cinner_right_comp)
    ultimately show ?thesis unfolding bounded_linear_def
      using bounded_clinear.intro bounded_clinear_axioms_def by auto 
  qed
  hence  \<open>\<forall> x. \<exists> t::'b. ( \<forall> y :: 'b.  (g x) y = (\<langle>t , y\<rangle>) )\<close>
    using  Riesz_Frechet_representation_existence by blast
  hence  \<open>\<exists> F. \<forall> x. ( \<forall> y :: 'b.  (g x) y = (\<langle>(F x) , y\<rangle>) )\<close>
    by metis
  then obtain F where \<open>\<forall> x. ( \<forall> y :: 'b.  (g x) y = (\<langle>(F x) , y\<rangle>) )\<close>
    by blast
  thus ?thesis using  \<open>g \<equiv> \<lambda> x. ( \<lambda> y. (\<langle>x , (G y)\<rangle>) )\<close>
    by auto
qed

(* NEW *)
corollary Existence_of_adjoint2: 
  \<open>\<exists> Adj. \<forall> G:: 'b::chilbert_space \<Rightarrow> 'a::chilbert_space. 
 bounded_clinear G \<longrightarrow> ( 
   \<forall> x::'a. \<forall> y::'b. \<langle>(Adj G) x , y\<rangle> = \<langle>x , (G y)\<rangle>
)\<close>
proof-
  have   \<open>\<forall> G. \<exists> F:: 'a::chilbert_space \<Rightarrow> 'b::chilbert_space.
 bounded_clinear G \<longrightarrow> ( 
   \<forall> x::'a. \<forall> y::'b. (\<langle>(F x) , y\<rangle>) = (\<langle>x , (G y)\<rangle>) )\<close>
    using Existence_of_adjoint by blast
  thus ?thesis by metis
qed

definition Adj::\<open>('b::chilbert_space \<Rightarrow> 'a::chilbert_space) 
 \<Rightarrow> ('a::chilbert_space \<Rightarrow> 'b::chilbert_space)\<close> where 
  \<open>Adj \<equiv> SOME Adj. \<forall> G:: 'b::chilbert_space \<Rightarrow> 'a::chilbert_space. 
 bounded_clinear G \<longrightarrow> ( 
   \<forall> x::'a. \<forall> y::'b. \<langle>((Adj G) x) , y\<rangle> = \<langle>x , (G y)\<rangle>
)\<close>

notation Adj ("_\<^sup>\<dagger>" [99] 100)

lemma AdjI: \<open>bounded_clinear G \<Longrightarrow> 
 \<forall> x::'a. \<forall> y::'b. \<langle>((G\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (G y)\<rangle> \<close>
  for G:: \<open>'b::chilbert_space \<Rightarrow> 'a::chilbert_space\<close>
proof-
  assume \<open>bounded_clinear G\<close> 
  moreover have \<open>\<forall> G:: 'b::chilbert_space \<Rightarrow> 'a::chilbert_space. 
 bounded_clinear G \<longrightarrow> ( 
   \<forall> x::'a. \<forall> y::'b. \<langle>((G\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (G y)\<rangle> )\<close>
    using Existence_of_adjoint2 Adj_def
    by (smt tfl_some)
  ultimately show ?thesis by blast  
qed


(* NEW *)
lemma AdjUniq:
  \<open>bounded_clinear G \<Longrightarrow>  
   \<forall> x::'a. \<forall> y::'b. \<langle>(F x) , y\<rangle> = \<langle>x , (G y)\<rangle>  \<Longrightarrow> F = G\<^sup>\<dagger>\<close>
  for G:: \<open>'b::chilbert_space \<Rightarrow> 'a::chilbert_space\<close>
    and F:: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close>
proof-
  assume  \<open>bounded_clinear G\<close>  
  assume\<open>\<forall> x::'a. \<forall> y::'b. \<langle>(F x) , y\<rangle> = \<langle>x , (G y)\<rangle>\<close>
  moreover have \<open>\<forall> x::'a. \<forall> y::'b. \<langle>((G\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (G y)\<rangle>\<close>
    using  \<open>bounded_clinear G\<close> AdjI by blast
  ultimately have  \<open>\<forall> x::'a. \<forall> y::'b. 
    (\<langle>(F x) , y\<rangle> )-(\<langle>((G\<^sup>\<dagger>) x) , y\<rangle>) = 0\<close>
    by (simp add: \<open>\<forall>x y. \<langle> (G\<^sup>\<dagger>) x | y \<rangle> = \<langle> x | G y \<rangle>\<close> \<open>\<forall>x y. \<langle> F x | y \<rangle> = \<langle> x | G y \<rangle>\<close>)
  hence  \<open>\<forall> x::'a. \<forall> y::'b. 
    (\<langle>((F x) - ((G\<^sup>\<dagger>) x)) , y\<rangle> ) = 0\<close>
    by (simp add: cinner_diff_left)
  hence \<open>\<forall> x::'a. (F x) - ((G\<^sup>\<dagger>) x) = 0\<close>
    by (metis cinner_gt_zero_iff cinner_zero_left)
  hence \<open>\<forall> x::'a. (F - (G\<^sup>\<dagger>)) x = 0\<close>
    by simp
  hence \<open>\<forall> x::'a. F x = (G\<^sup>\<dagger>) x\<close>
    by (simp add: \<open>\<forall>x. F x - (G\<^sup>\<dagger>) x = 0\<close> eq_iff_diff_eq_0)
  thus ?thesis by auto
qed


(* NEW *)
lemma Adj_bounded_clinear:
  \<open>bounded_clinear A \<Longrightarrow> bounded_clinear (A\<^sup>\<dagger>)\<close>
proof-
  include notation_norm 
  assume \<open>bounded_clinear A\<close>
  have \<open>\<langle>((A\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (A y)\<rangle>\<close>
    for x y
    by (simp add: AdjI \<open>bounded_clinear A\<close>)
  have \<open>Modules.additive (A\<^sup>\<dagger>)\<close>
  proof-
    have \<open>\<langle>((A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2)) , y\<rangle> = 0\<close>
      for x1 x2 y
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x | y \<rangle> = \<langle> x | A y \<rangle>\<close> cinner_diff_left cinner_left_distrib)        
    hence \<open>(A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2) = 0\<close>
      for x1 x2
      using cinner_eq_zero_iff by blast
    thus ?thesis
      by (simp add: \<open>\<And>x2 x1. (A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2) = 0\<close> additive.intro eq_iff_diff_eq_0) 
  qed 
  moreover have \<open>(A\<^sup>\<dagger>) (r *\<^sub>C x) = r *\<^sub>C  (A\<^sup>\<dagger>) x\<close>
    for r x
  proof-
    have \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> = \<langle>(r *\<^sub>C x) , (A y)\<rangle>\<close>
      for y
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x | y \<rangle> = \<langle> x | A y \<rangle>\<close>)
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> = (cnj r) * ( \<langle>x , (A y)\<rangle>)\<close>
      for y
      by simp
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> =  (\<langle>x , ((cnj r) *\<^sub>C A y)\<rangle>)\<close>
      for y
      by simp
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> =  (cnj r) * (\<langle>x , A y\<rangle>)\<close>
      for y
      by auto
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> =  (cnj r) * (\<langle>(A\<^sup>\<dagger>) x , y\<rangle>)\<close>
      for y
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x | y \<rangle> = \<langle> x | A y \<rangle>\<close>)
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> =  (\<langle>r *\<^sub>C (A\<^sup>\<dagger>) x , y\<rangle>)\<close>
      for y
      by simp
    hence \<open>\<langle>(((A\<^sup>\<dagger>) (r *\<^sub>C x)) - (r *\<^sub>C (A\<^sup>\<dagger>) x )) , y\<rangle> = 0\<close>
      for y
      by (simp add: \<open>\<And>y. \<langle> (A\<^sup>\<dagger>) (r *\<^sub>C x) | y \<rangle> = \<langle> r *\<^sub>C (A\<^sup>\<dagger>) x | y \<rangle>\<close> cinner_diff_left)
    hence \<open>((A\<^sup>\<dagger>) (r *\<^sub>C x)) - (r *\<^sub>C (A\<^sup>\<dagger>) x ) = 0\<close>
      using cinner_eq_zero_iff by blast
    thus ?thesis
      by (simp add: \<open>(A\<^sup>\<dagger>) (r *\<^sub>C x) - r *\<^sub>C (A\<^sup>\<dagger>) x = 0\<close> eq_iff_diff_eq_0) 
  qed
  moreover have \<open>(\<exists>K. \<forall>x. \<parallel> (A\<^sup>\<dagger>) x\<parallel> \<le> \<parallel>x\<parallel> * K)\<close>
  proof-
    have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<langle>((A\<^sup>\<dagger>) x) , ((A\<^sup>\<dagger>) x)\<rangle>\<close>
      for x
      using power2_norm_eq_cinner' by auto
    moreover have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<ge> 0\<close>
      for x
      by simp
    ultimately have  \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<bar> \<langle>((A\<^sup>\<dagger>) x) , ((A\<^sup>\<dagger>) x)\<rangle> \<bar>\<close>
      for x
      by (simp add: abs_pos)
    hence \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 = \<bar> \<langle>x , (A ((A\<^sup>\<dagger>) x))\<rangle> \<bar>\<close>
      for x
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x | y \<rangle> = \<langle> x | A y \<rangle>\<close>)
    moreover have  \<open>\<bar>\<langle>x , (A ((A\<^sup>\<dagger>) x))\<rangle>\<bar> \<le> \<parallel>x\<parallel> *  \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close>
      for x
      by (simp add: complex_inner_class.norm_cauchy_schwarz)
    ultimately have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2  \<le> \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close>
      for x
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x | y \<rangle> = \<langle> x | A y \<rangle>\<close> complex_inner_class.Cauchy_Schwarz_ineq2 power2_norm_eq_cinner)
    moreover have \<open>\<exists> M. M \<ge> 0 \<and> (\<forall> x.  \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le>  \<parallel>x\<parallel> * M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>)\<close>
    proof-
      have \<open>\<exists> M. M \<ge> 0 \<and> (\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>)\<close>
        using \<open>bounded_clinear A\<close>
        by (metis (mono_tags, hide_lams) bounded_clinear.bounded linear mult_nonneg_nonpos mult_zero_right norm_ge_zero order.trans semiring_normalization_rules(7)) 
      then obtain M where \<open>M \<ge> 0\<close> and \<open>\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
        by blast
      have \<open>\<forall> x. \<parallel>x\<parallel> \<ge> 0\<close>
        by simp
      hence \<open>\<forall> x.  \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le>  \<parallel>x\<parallel> * M * \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
        using  \<open>\<forall> x. \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel> \<le> M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
        by (smt ordered_comm_semiring_class.comm_mult_left_mono vector_space_over_itself.scale_scale) 
      thus ?thesis using \<open>M \<ge> 0\<close> by blast
    qed
    ultimately have  \<open>\<exists> M. M \<ge> 0 \<and> (\<forall> x. \<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>)\<close>
      by (meson order.trans)
    then obtain M where \<open>M \<ge> 0\<close> and \<open>\<forall> x. \<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
      by blast
    have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel> \<le> \<parallel>x\<parallel> *  M\<close>
      for x
    proof(cases \<open> \<parallel>(A\<^sup>\<dagger>) x\<parallel> = 0\<close>)
      case True
      thus ?thesis
        by (simp add: \<open>0 \<le> M\<close>) 
    next
      case False
      have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
        using \<open>\<forall> x. \<parallel> (A\<^sup>\<dagger>) x \<parallel>^2 \<le> \<parallel>x\<parallel> *  M *  \<parallel>(A\<^sup>\<dagger>) x\<parallel>\<close>
        by simp
      thus ?thesis
        by (smt False mult_right_cancel mult_right_mono norm_ge_zero semiring_normalization_rules(29)) 
    qed
    thus ?thesis by blast
  qed
  ultimately show ?thesis
    unfolding bounded_clinear_def
    unfolding clinear_def
    by (simp add: bounded_clinear_axioms_def clinear_axioms.intro)
qed

section \<open>Dual space\<close>
  (* This is an important particular case of ('a, 'b) bounded,
where 'b is the set of complex numbers. *)

(* The interpretation of Riesz representation theorem as an anti-isomorphism
between a Hilbert space and its dual of a Hilbert space is the justification of 
the brac-ket notation *)

(* NEW *)
(* TODO: define for topological_vector_space? (continuous functionals) *)
(* TODO: is there an advantage in not simply using type_synonym 'a dual = ('a,complex) bounded? *)
typedef (overloaded) ('a::chilbert_space) dual = "{f::'a functional. bounded_clinear f}"
  morphisms Rep_dual Abs_dual (* TODO These are the default names. Why mention them here? *)
  using bounded_clinear_zero by blast
setup_lifting type_definition_dual

(* TODO: all the instantiations are probably better done with lift_definition *)

(* NEW *)
instantiation dual :: (chilbert_space) "zero"
begin
definition
  "0 = Abs_dual (\<lambda> x::'a. (0::complex))"
instance ..
end

(* NEW *)
instantiation dual :: (chilbert_space) "uminus"
begin
definition
  "- x = Abs_dual (\<lambda> t::'a. - Rep_dual x t)"
instance ..
end

(* NEW *)
(* TODO exists: Rep_dual_inject[THEN iffD1] *)
lemma dual_eqI:
  \<open>Rep_dual m = Rep_dual n \<Longrightarrow> m = n\<close>
  by (simp add: Rep_dual_inject)

(* NEW *)
(* TODO exists: Rep_dual_inject[symmetric] *)
lemma dual_eq_iff:
  "m = n \<longleftrightarrow> Rep_dual m = Rep_dual n"
  by (simp add: Rep_dual_inject)

(* NEW *)
(* TODO exists: Rep_dual_inverse *)
(* TODO: why "code abstype"? *)
lemma Abs_dual_Rep_dual [code abstype]:
  \<open>Abs_dual (Rep_dual n) = n\<close>
  by (fact Rep_dual_inverse)

(* NEW *)
instantiation dual :: (chilbert_space) "semigroup_add"
begin
definition 
  \<open>x + y = Abs_dual (\<lambda> t::'a. Rep_dual x t + Rep_dual y t)\<close>

instance
proof      
  fix a b c :: \<open>('a::chilbert_space) dual\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply (simp add: dual_eq_iff)
  proof-
    have \<open>Rep_dual (a + b + c) x = Rep_dual (a + (b + c)) x\<close>
      for x
    proof -
      have "Rep_dual a x + Rep_dual b x + Rep_dual c x = Rep_dual a x + (Rep_dual b x + Rep_dual c x)"
        by auto
      then show ?thesis
        by (metis (no_types) Abs_dual_inverse Rep_dual bounded_clinear_add mem_Collect_eq plus_dual_def)
    qed     
    thus \<open>Rep_dual (a + b + c) = Rep_dual (a + (b + c))\<close>
      by blast 
  qed
qed

end

(* NEW *)
instantiation dual :: (chilbert_space) "comm_monoid_add" begin
instance
proof
  fix a b :: \<open>'a::chilbert_space dual\<close>
  show \<open>a + b = b + a\<close>
    apply (simp add: dual_eq_iff)
  proof-
    have \<open>Rep_dual (a + b) x = Rep_dual (b + a) x\<close>
      for x
    proof-
      have  \<open>Rep_dual a x + Rep_dual b x  = Rep_dual b x + Rep_dual a x\<close>
        by simp
      hence  \<open>Rep_dual (a + b) x = Rep_dual (b + a) x\<close>
      proof -
        have "\<forall>d. bounded_clinear (Rep_dual (d::'a dual))"
          by (metis Rep_dual mem_Collect_eq)
        then show ?thesis
          by (simp add: Abs_dual_inverse bounded_clinear_add plus_dual_def)
      qed 
      thus ?thesis by blast
    qed
    thus \<open>Rep_dual (a + b) = Rep_dual (b + a)\<close> by blast
  qed

  fix a :: \<open>'a::chilbert_space dual\<close>
  show \<open>0 + a = a\<close>
    apply (simp add: dual_eq_iff)
  proof-
    have \<open>(Rep_dual 0) x + Rep_dual a x = Rep_dual a x\<close>
      for x
      by (simp add: Abs_dual_inverse zero_dual_def)
    hence \<open>Rep_dual (0 + a) x = Rep_dual a x\<close>
      for x
      using  Abs_dual_inverse
      by (metis (full_types) Rep_dual bounded_clinear_add mem_Collect_eq plus_dual_def)  
    thus \<open>Rep_dual (0 + a) = Rep_dual a\<close> by blast
  qed
qed

end

(* NEW *)
instantiation dual :: (chilbert_space) "ab_group_add" begin
definition
  \<open>x - y = Abs_dual (\<lambda> t::'a. Rep_dual x t - Rep_dual y t)\<close>
instance
proof
  fix a::\<open>'a::chilbert_space dual\<close>
  show \<open>- a + a = 0\<close>
    apply (simp add: dual_eq_iff)
  proof-
    have \<open>- Rep_dual a x + Rep_dual a x = 0\<close>
      for x
      by simp
    moreover have \<open>(0::complex) = (Rep_dual (0::'a dual)) x\<close>
      for x
      using  Abs_dual_inverse
      by (simp add: Abs_dual_inverse zero_dual_def)
    ultimately have \<open>- Rep_dual a x + Rep_dual a x = Rep_dual 0 x\<close>
      for x
      by simp       
    moreover have \<open>Rep_dual (- a) x = - Rep_dual a x\<close>
      for x
      using  Abs_dual_inverse
      by (metis Rep_dual bounded_clinear_minus mem_Collect_eq uminus_dual_def)     
    ultimately have \<open>Rep_dual (- a) x + Rep_dual a x = Rep_dual 0 x\<close>
      for x
      by simp
    hence \<open>Rep_dual (- a + a) x = Rep_dual 0 x\<close>
      for x
      using  Abs_dual_inverse
      by (metis (full_types) Rep_dual bounded_clinear_add mem_Collect_eq plus_dual_def) 
    thus \<open>Rep_dual (- a + a) = Rep_dual 0\<close> by blast
  qed

  fix a b::\<open>'a::chilbert_space dual\<close>
  show \<open>a - b = a + - b\<close>
    apply (simp add: dual_eq_iff)
  proof-
    have \<open>Rep_dual (a - b) x = Rep_dual a x - Rep_dual b x\<close>
      for x
    proof -
      have "\<forall>d. bounded_clinear (Rep_dual (d::'a dual))"
        using Rep_dual by blast
      then show ?thesis
        by (simp add: Abs_dual_inverse bounded_clinear_sub minus_dual_def)
    qed
    moreover have \<open>Rep_dual (a + (- b)) x = Rep_dual a x + Rep_dual (- b) x\<close>
      for x
      by (metis (no_types) Abs_dual_inverse Rep_dual bounded_clinear_add mem_Collect_eq plus_dual_def)
    moreover have \<open> - Rep_dual b x = Rep_dual (- b) x\<close> 
      for x  
      using  Abs_dual_inverse
      by (metis Rep_dual bounded_clinear_minus mem_Collect_eq uminus_dual_def)     
    ultimately have  \<open>Rep_dual (a - b) x = Rep_dual (a + (- b)) x\<close> 
      for x  
      by simp
    thus \<open>Rep_dual (a - b) = Rep_dual (a + - b)\<close> by blast
  qed
qed
end

(* NEW *)
instantiation dual :: (chilbert_space) "complex_vector" begin
definition
  \<open>(*\<^sub>C) \<equiv> \<lambda> r. \<lambda> x. (Abs_dual ( \<lambda> t::'a. r *\<^sub>C (Rep_dual x) t ))\<close>
definition
  \<open>(*\<^sub>R) \<equiv> \<lambda> r. \<lambda> x. (Abs_dual ( \<lambda> t::'a. r *\<^sub>R (Rep_dual x) t ))\<close>

instance
  apply intro_classes
proof
  fix r and x::\<open>'a::chilbert_space dual\<close>
  show \<open>r *\<^sub>R x = complex_of_real r *\<^sub>C x\<close>
    apply (simp add: dual_eq_iff)
    by (simp add: scaleC_dual_def scaleR_dual_def scaleR_scaleC)

  fix a and x y::\<open>'a::chilbert_space dual\<close>
  show \<open>a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    apply (simp add: dual_eq_iff)
  proof-
    have \<open>Rep_dual (a *\<^sub>C (x + y)) t = Rep_dual (a *\<^sub>C x + a *\<^sub>C y) t\<close>
      for t
    proof-
      have \<open>a *\<^sub>C ( Rep_dual x t + Rep_dual y t ) = a *\<^sub>C Rep_dual x t + a *\<^sub>C Rep_dual y t\<close>
        using scaleC_add_right by blast
      hence \<open>a *\<^sub>C Rep_dual (x + y) t = a *\<^sub>C Rep_dual x t + a *\<^sub>C Rep_dual y t\<close>
        using Abs_dual_inverse
        by (metis (full_types) Rep_dual bounded_clinear_add mem_Collect_eq plus_dual_def)
      hence \<open>Rep_dual (a *\<^sub>C (x + y)) t = Rep_dual (a *\<^sub>C x) t + Rep_dual (a *\<^sub>C y) t\<close>
        by (metis (no_types) Abs_dual_inverse Rep_dual \<open>a *\<^sub>C Rep_dual (x + y) t = a *\<^sub>C Rep_dual x t + a *\<^sub>C Rep_dual y t\<close> bounded_clinear_const_scaleC mem_Collect_eq scaleC_dual_def)
      hence \<open>Rep_dual (a *\<^sub>C (x + y)) t = Rep_dual (a *\<^sub>C x + a *\<^sub>C y) t\<close>
        by (metis (no_types) Abs_dual_inverse Rep_dual \<open>Rep_dual (a *\<^sub>C (x + y)) t = Rep_dual (a *\<^sub>C x) t + Rep_dual (a *\<^sub>C y) t\<close> bounded_clinear_add mem_Collect_eq plus_dual_def)
      thus ?thesis by blast
    qed
    thus \<open>Rep_dual (a *\<^sub>C (x + y)) = Rep_dual (a *\<^sub>C x + a *\<^sub>C y)\<close>
      by auto
  qed

  fix a b and x::\<open>'a::chilbert_space dual\<close>
  show \<open>(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x\<close>
    apply (simp add: dual_eq_iff)
  proof-
    have \<open>Rep_dual ((a + b) *\<^sub>C x) t = Rep_dual (a *\<^sub>C x + b *\<^sub>C x) t\<close>
      for t
    proof-
      have \<open>Rep_dual ((a + b) *\<^sub>C x) t = Rep_dual (a *\<^sub>C x + b *\<^sub>C x) t\<close>
      proof- (* sledgehammer *)
        have f1: "\<forall>d c. Rep_dual (Abs_dual (\<lambda>a. c *\<^sub>C Rep_dual d (a::'a))) = (\<lambda>a. c *\<^sub>C Rep_dual d a)"
          by (metis (no_types) Abs_dual_inverse Rep_dual bounded_clinear_compose bounded_clinear_scaleC_right mem_Collect_eq)
        then have "\<forall>c d da. Rep_dual (Abs_dual (\<lambda>a. Rep_dual da (a::'a) + c *\<^sub>C Rep_dual d a)) = (\<lambda>a. Rep_dual da a + c *\<^sub>C Rep_dual d a)"
          by (metis (no_types) Abs_dual_inverse Rep_dual bounded_clinear_add mem_Collect_eq)
        hence "Rep_dual (Abs_dual (\<lambda>aa. a *\<^sub>C Rep_dual x aa + b *\<^sub>C Rep_dual x aa)) t = a *\<^sub>C Rep_dual x t + b *\<^sub>C Rep_dual x t"
          using f1 by (metis (no_types))
        then have "Rep_dual (Abs_dual (\<lambda>aa. a *\<^sub>C Rep_dual x aa + b *\<^sub>C Rep_dual x aa)) t = (a + b) *\<^sub>C Rep_dual x t"
          by (metis (no_types) scaleC_left.add)
        then show ?thesis
          using f1 by (simp add: plus_dual_def scaleC_dual_def)
      qed
      thus ?thesis by blast
    qed
    thus \<open>Rep_dual ((a + b) *\<^sub>C x) = Rep_dual (a *\<^sub>C x + b *\<^sub>C x)\<close> by blast
  qed

  fix a b::complex and x :: \<open>'a::chilbert_space dual\<close>
  show \<open>a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x\<close>
    apply (simp add: dual_eq_iff)
  proof-
    have \<open>Rep_dual (a *\<^sub>C b *\<^sub>C x) t = Rep_dual ((a * b) *\<^sub>C x) t\<close>
      for t
    proof-
      have \<open>Rep_dual (a *\<^sub>C b *\<^sub>C x) t = Rep_dual ((a * b) *\<^sub>C x) t\<close>
      proof- (* sledgehammer *)
        have "Rep_dual (Abs_dual (\<lambda>aa. a *\<^sub>C Rep_dual (Abs_dual (\<lambda>aa. b *\<^sub>C Rep_dual x aa)) aa)) t = Rep_dual (Abs_dual (\<lambda>aa. (a *\<^sub>C b) *\<^sub>C Rep_dual x aa)) t"
          by (metis (no_types) Abs_dual_inverse Rep_dual bounded_clinear_compose bounded_clinear_mult_right complex_scaleC_def mem_Collect_eq scaleC_scaleC)
        then show ?thesis
          by (simp add: scaleC_dual_def)
      qed

      thus ?thesis by blast
    qed
    thus \<open>Rep_dual (a *\<^sub>C b *\<^sub>C x) = Rep_dual ((a * b) *\<^sub>C x)\<close>
      by blast
  qed

  fix x::\<open>'a::chilbert_space dual\<close>
  show \<open>1 *\<^sub>C x = x\<close>
    apply (simp add: dual_eq_iff)
  proof-
    have \<open>Rep_dual (1 *\<^sub>C x) t = Rep_dual x t\<close>
      for t
      using Abs_dual_inverse
      by (metis (full_types) Rep_dual bounded_clinear_const_scaleC mem_Collect_eq scaleC_dual_def scaleC_one)
    thus \<open>Rep_dual (1 *\<^sub>C x) = Rep_dual x\<close> by blast
  qed
qed

end

(* NEW *)
instantiation dual :: (chilbert_space) "complex_normed_vector" begin
instance by (cheat "dual complex_normed_vector")
end

instantiation dual :: (chilbert_space) "chilbert_space" begin
  (* The inner product is defined using Riesz representation theorem *)
  (* TODO: is that the same as the Hilbert-Schmidt inner product? *)

  (* In order to define the Hilbert-Schmidt inner product we need
to define the tensor product of Hilbert spaces. 
https://en.wikipedia.org/wiki/Tensor_product_of_Hilbert_spaces *)

instance by (cheat "dual chilbert_space")
end

(* NEW *)
section \<open>Tensor product\<close>

typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) bounded 
= \<open>{A :: 'a \<Rightarrow> 'b. bounded_clinear A}\<close>
  using bounded_clinear_zero by blast

setup_lifting type_definition_bounded

(* Tensor product *)
typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) tensor
= \<open>{ A :: ('a dual, 'b) bounded. finite_dim (Abs_linear_space ((Rep_bounded A) ` UNIV)) }\<close>
  sorry

(* Embedding of (x,y) into the tensor product as x\<otimes>y *)
definition HS_embedding :: \<open>('a::chilbert_space)*('b::chilbert_space) \<Rightarrow> ('a, 'b) tensor\<close> where
\<open>HS_embedding x = Abs_tensor ( Abs_bounded (\<lambda> w::'a dual. ( (Rep_dual w) (fst x) ) *\<^sub>C (snd x) ) )\<close>

(* NEW *)
(* The tensor product of two Hilbert spaces is a Hilbert space *)
instantiation tensor :: (chilbert_space,chilbert_space) "chilbert_space" begin
instance sorry
end


end



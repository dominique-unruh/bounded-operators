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
  imports Complex_L2 "HOL-Library.Adhoc_Overloading" 
    "HOL-Analysis.Abstract_Topology" Extended_Sorry
begin

(* NEW *)
lemma bounded_clinearDiff: \<open>clinear A \<Longrightarrow> clinear B \<Longrightarrow> clinear (A - B)\<close>
  by (smt add_diff_add additive.add clinear.axioms(1) clinear.axioms(2) clinearI clinear_axioms_def complex_vector.scale_right_diff_distrib minus_apply)

(* NEW *)
(* The norm of a bouded operator *)
definition norm_bounded::\<open>('a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector) \<Rightarrow> real\<close> where
  \<open>norm_bounded \<equiv> \<lambda> f. Sup{ K | K.  \<forall>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K}\<close>

(* NEW *)
definition proportion :: \<open>('a::complex_vector) set \<Rightarrow> bool\<close> where
\<open>proportion S =  (
  \<forall> x y. x \<in> S \<and> x \<noteq> 0 \<and> y \<in> S \<and> y \<noteq> 0 \<longrightarrow> (\<exists> k. x = k *\<^sub>C y) 
)\<close>

(* functional *)
type_synonym 'a functional = \<open>'a \<Rightarrow> complex\<close>
                                       
lemma ker_ortho_nonzero:
  fixes f :: \<open>('a::chilbert_space) functional\<close> and x :: 'a
  assumes \<open>bounded_clinear f\<close> and \<open>x \<noteq> 0\<close> and \<open>x \<in> ((ker_op f)\<^sub>\<bottom>)\<close> 
  shows \<open>f x \<noteq> 0\<close>
proof(rule classical)
  have \<open>is_subspace (ker_op f)\<close> using \<open>bounded_clinear f\<close>
    by (simp add: ker_op_lin) 
  assume \<open>\<not>(f x \<noteq> 0)\<close>
  hence \<open>x \<in> ker_op f\<close>
    by (simp add: ker_op_def) 
  moreover have \<open>(ker_op f)\<inter>(((ker_op f))\<^sub>\<bottom>) = {0}\<close>
    using \<open>is_subspace (ker_op f)\<close> sorry
  ultimately have  \<open>x \<notin> ((ker_op f)\<^sub>\<bottom>)\<close> using \<open>x \<noteq> 0\<close>
    by (smt Int_iff empty_iff insert_iff) 
  thus ?thesis using \<open>x \<in> ((ker_op f)\<^sub>\<bottom>)\<close> by blast
qed
                                               
(* NEW *)
lemma ker_unidim:
  fixes f :: \<open>('a::chilbert_space) functional\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>proportion ((ker_op f)\<^sub>\<bottom>)\<close>
proof-
  have \<open>x \<in> ((ker_op f)\<^sub>\<bottom>) \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> y \<in>((ker_op f)\<^sub>\<bottom>) \<Longrightarrow> y \<noteq> 0 
    \<Longrightarrow> \<exists> k. x = k *\<^sub>C y\<close>
    for x y
  proof-
    assume \<open>x \<in> ((ker_op f)\<^sub>\<bottom>)\<close> and \<open>x \<noteq> 0\<close> and \<open>y \<in>((ker_op f)\<^sub>\<bottom>)\<close> and \<open>y \<noteq> 0\<close>
    from \<open>bounded_clinear f\<close> 
    have \<open>is_subspace (ker_op f)\<close>
      by (simp add: ker_op_lin)
    hence \<open>is_subspace ((ker_op f)\<^sub>\<bottom>)\<close>
      by simp
    hence \<open>f x \<noteq> 0\<close>

  qed 
  thus ?thesis
    by (simp add: proportion_def) 
qed

(* NEW *)
(* https://en.wikipedia.org/wiki/Riesz_representation_theorem *)
theorem Riesz_Frechet_representation:
  fixes f::\<open>'a::chilbert_space \<Rightarrow> complex\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>\<exists> t::'a. ( \<parallel>t\<parallel> = norm_bounded f ) \<and> ( \<forall> x :: 'a.  f x = (t \<cdot> x) )\<close>
  sorry

(* NEW *)
corollary Existence_of_adjoint: 
  \<open>bounded_clinear G \<Longrightarrow> \<exists> F:: 'a::chilbert_space \<Rightarrow> 'b::chilbert_space. ( 
   \<forall> x::'a. \<forall> y::'b. ((F x) \<cdot> y) = (x \<cdot> (G y))
)\<close>
proof-
  assume \<open>bounded_clinear G\<close>
  hence \<open>clinear G\<close>
    unfolding bounded_clinear_def by blast
  have  \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
    using  \<open>bounded_clinear G\<close>
    unfolding bounded_clinear_def
    by (simp add: bounded_clinear_axioms_def) 
  define g :: \<open>'a \<Rightarrow> ('b \<Rightarrow> complex)\<close> where
    \<open>g \<equiv> \<lambda> x. ( \<lambda> y. (x \<cdot> (G y)) )\<close>
  have \<open>bounded_clinear (g x)\<close>
    for x
  proof-
    have \<open>clinear (g x)\<close>
    proof-
      have \<open>(g x) (a + b) = (g x) a + (g x) b\<close>
        for a b
        unfolding  \<open>g \<equiv> \<lambda> x. ( \<lambda> y. (x \<cdot> (G y)) )\<close>
        using  \<open>clinear G\<close>
        by (simp add: additive.add cinner_right_distrib clinear_def)
      moreover have  \<open>(g x) (k *\<^sub>C a) = k *\<^sub>C ((g x) a)\<close>
        for a k
        unfolding  \<open>g \<equiv> \<lambda> x. ( \<lambda> y. (x \<cdot> (G y)) )\<close>
        using  \<open>clinear G\<close>
        by (simp add: clinear.scaleC)
      ultimately show ?thesis
        by (simp add: clinearI) 
    qed
    moreover have \<open>\<exists> M. \<forall> y. \<parallel> (g x) y \<parallel> \<le> \<parallel> y \<parallel> * M\<close>
      using \<open>\<exists> M. \<forall> y. \<parallel> G y \<parallel> \<le> \<parallel> y \<parallel> * M\<close> \<open>g \<equiv> \<lambda> x. ( \<lambda> y. (x \<cdot> (G y)) )\<close>
      by (simp add: \<open>bounded_clinear G\<close> bounded_clinear.bounded bounded_clinear_cinner_right_comp)
    ultimately show ?thesis unfolding bounded_linear_def
      using bounded_clinear.intro bounded_clinear_axioms_def by auto 
  qed
  hence  \<open>\<forall> x. \<exists> t::'b. ( \<parallel>t\<parallel> = norm_bounded (g x) ) \<and> ( \<forall> y :: 'b.  (g x) y = (t \<cdot> y) )\<close>
    using Riesz_Frechet_representation by blast
  hence  \<open>\<exists> F. \<forall> x. ( \<parallel>F x\<parallel> = norm_bounded (g x) ) \<and> ( \<forall> y :: 'b.  (g x) y = ((F x) \<cdot> y) )\<close>
    by metis
  then obtain F where \<open>\<forall> x. ( \<parallel>F x\<parallel> = norm_bounded (g x) ) \<and> ( \<forall> y :: 'b.  (g x) y = ((F x) \<cdot> y) )\<close>
    by blast
  thus ?thesis using  \<open>g \<equiv> \<lambda> x. ( \<lambda> y. (x \<cdot> (G y)) )\<close>
    by auto
qed

(* NEW *)
corollary Existence_of_adjoint2: 
  \<open>\<exists> Adj. \<forall> G:: 'b::chilbert_space \<Rightarrow> 'a::chilbert_space. 
 bounded_clinear G \<longrightarrow> ( 
   \<forall> x::'a. \<forall> y::'b. ((Adj G) x) \<cdot> y = x \<cdot> (G y)
)\<close>
proof-
  have   \<open>\<forall> G. \<exists> F:: 'a::chilbert_space \<Rightarrow> 'b::chilbert_space.
 bounded_clinear G \<longrightarrow> ( 
   \<forall> x::'a. \<forall> y::'b. ((F x) \<cdot> y) = (x \<cdot> (G y)) )\<close>
  using Existence_of_adjoint by blast
  thus ?thesis by metis
qed

definition Adj::\<open>('b::chilbert_space \<Rightarrow> 'a::chilbert_space) 
 \<Rightarrow> ('a::chilbert_space \<Rightarrow> 'b::chilbert_space)\<close> where 
\<open>Adj \<equiv> SOME Adj. \<forall> G:: 'b::chilbert_space \<Rightarrow> 'a::chilbert_space. 
 bounded_clinear G \<longrightarrow> ( 
   \<forall> x::'a. \<forall> y::'b. ((Adj G) x) \<cdot> y = x \<cdot> (G y)
)\<close>

notation Adj ("_\<^sup>\<dagger>" [99] 100)

lemma AdjI: \<open>\<forall> G:: 'b::chilbert_space \<Rightarrow> 'a::chilbert_space. 
 bounded_clinear G \<Longrightarrow> ( 
   \<forall> x::'a. \<forall> y::'b. ((G\<^sup>\<dagger>) x) \<cdot> y = x \<cdot> (G y) )\<close>
  using Existence_of_adjoint2 Adj_def
  by (smt tfl_some)

end
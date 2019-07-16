(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

theory Adjoint_Operator
  imports Complex_Inner_Product

begin
                                                
locale adjoint =
  fixes adj::\<open>('a::complex_inner \<Rightarrow> 'b::complex_inner) \<Rightarrow> ('b \<Rightarrow> 'a)\<close> ( "(_)\<^sup>\<dagger>" )
  assumes equation: \<open>\<And> f::'a\<Rightarrow>'b. (\<forall> x::'a. \<forall> y::'b. \<langle>f x, y\<rangle> = \<langle>x, f\<^sup>\<dagger> y\<rangle>)\<close>
    and uniq: \<open>\<And> f::'a\<Rightarrow>'b. \<And> g::'b\<Rightarrow>'a. (\<forall> x::'a. \<forall> y::'b. \<langle>f x, y\<rangle> = \<langle>x, g y\<rangle>) \<Longrightarrow> g = (f\<^sup>\<dagger>)\<close>


subsection \<open>Riesz Representation\<close>

lemma bounded_clinearDiff: \<open>clinear A \<Longrightarrow> clinear B \<Longrightarrow> clinear (A - B)\<close>
  by (smt add_diff_add additive.add clinear.axioms(1) clinear.axioms(2) clinearI clinear_axioms_def complex_vector.scale_right_diff_distrib minus_apply)

(* TODO: remove and define locally in lemma *)
definition proportion :: \<open>('a::complex_vector) set \<Rightarrow> bool\<close> where
  \<open>proportion S =  (
  \<forall> x y. x \<in> S \<and> x \<noteq> 0 \<and> y \<in> S \<and> y \<noteq> 0 \<longrightarrow> (\<exists> k. x = k *\<^sub>C y) 
)\<close>

(* TODO: locally *)
lemma proportion_existence:
  \<open>proportion S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists> t \<in> S. (\<forall> x \<in> S. \<exists> k. x = k *\<^sub>C t)\<close>
  using complex_vector.scale_zero_left ex_in_conv proportion_def
  by metis

(* functional *)
type_synonym 'a functional = \<open>'a \<Rightarrow> complex\<close>

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
    using \<open>is_subspace (ker_op f)\<close> is_linear_manifold.zero is_subspace.subspace ortho_inter_zero by auto
  ultimately have  \<open>x \<notin> orthogonal_complement (ker_op f)\<close> using \<open>x \<noteq> 0\<close>
    by (smt Int_iff empty_iff insert_iff) 
  thus ?thesis using \<open>x \<in> orthogonal_complement (ker_op f)\<close> by blast
qed

(* TODO: local in Riesz_Frechet_representation_existence *)
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
      by (simp add: \<open>is_subspace (ker_op f)\<close> is_linear_manifold.zero is_subspace.subspace ortho_inter_zero)
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

(* https://en.wikipedia.org/wiki/Riesz_representation_theorem *)
lemma Riesz_Frechet_representation_existence:
  fixes f::\<open>'a::chilbert_space functional\<close>
  assumes \<open>bounded_clinear f\<close>
  shows \<open>\<exists>t. \<forall>x.  f x = \<langle>t, x\<rangle>\<close>
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
      by (smt \<open>t \<in> orthogonal_complement (ker_op f)\<close> additive.add assms bounded_clinear_def cinner_simps(1) cinner_simps(5) cinner_simps(6) cinner_zero_left clinear.axioms(1) ker_op_lin ortho_decomp projPropertiesA projPropertiesD proj_fixed_points proj_ker_simp proj_ker_simp)
    thus ?thesis
      by blast  
  qed
qed

subsection \<open>Adjoin\<close>

definition \<open>Adj G = (SOME F. \<forall>x. \<forall>y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>)\<close>
  for G :: "'b::complex_inner \<Rightarrow> 'a::complex_inner"

lemma Adj_is_adjoint:
  fixes G :: "'b::chilbert_space \<Rightarrow> 'a::chilbert_space"
  assumes \<open>bounded_clinear G\<close>
  shows \<open>\<forall>x. \<forall>y. \<langle>Adj G x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
proof (unfold Adj_def, rule someI_ex[where P="\<lambda>F. \<forall>x. \<forall>y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>"])
  include notation_norm
  from assms have \<open>clinear G\<close>
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
  thus "\<exists>x. \<forall>xa y. \<langle>x xa, y\<rangle> = \<langle>xa, G y\<rangle>" using  g_def
    by auto
qed

notation Adj ("_\<^sup>\<dagger>" [99] 100)

lemma AdjI: \<open>bounded_clinear G \<Longrightarrow> 
 \<langle>((G\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (G y)\<rangle> \<close>
  for G:: \<open>'b::chilbert_space \<Rightarrow> 'a::chilbert_space\<close>
proof-
  assume \<open>bounded_clinear G\<close> 
  moreover have \<open>\<forall> G:: 'b::chilbert_space \<Rightarrow> 'a::chilbert_space. 
 bounded_clinear G \<longrightarrow> ( 
   \<forall> x::'a. \<forall> y::'b. \<langle>((G\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (G y)\<rangle> )\<close>
    using Adj_is_adjoint 
    by (smt tfl_some)
  ultimately show ?thesis by blast  
qed


lemma AdjUniq:
  fixes G:: \<open>'b::chilbert_space \<Rightarrow> 'a::chilbert_space\<close>
    and F:: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close>
  assumes "bounded_clinear G"
  assumes F_is_adjoint: \<open>\<And>x y. \<langle>F x, y\<rangle> = \<langle>x, G y\<rangle>\<close>
  shows \<open>F = G\<^sup>\<dagger>\<close>
proof-
  note F_is_adjoint
  moreover have \<open>\<forall> x::'a. \<forall> y::'b. \<langle>((G\<^sup>\<dagger>) x) , y\<rangle> = \<langle>x , (G y)\<rangle>\<close>
    using  \<open>bounded_clinear G\<close> AdjI by blast
  ultimately have  \<open>\<forall> x::'a. \<forall> y::'b. 
    (\<langle>(F x) , y\<rangle> )-(\<langle>((G\<^sup>\<dagger>) x) , y\<rangle>) = 0\<close>
    by (simp add: \<open>\<forall>x y. \<langle> (G\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , G y \<rangle>\<close> F_is_adjoint)
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

(* TODO: cbanach should be sufficient? *)
lemma Adj_bounded_clinear:
  fixes A :: "'a::chilbert_space \<Rightarrow> 'b::chilbert_space"
  shows \<open>bounded_clinear A \<Longrightarrow> bounded_clinear (A\<^sup>\<dagger>)\<close>
proof-
  include notation_norm 
  assume \<open>bounded_clinear A\<close>
  have \<open>\<langle>((A\<^sup>\<dagger>) x), y\<rangle> = \<langle>x , (A y)\<rangle>\<close>
    for x y
    by (auto intro: AdjI \<open>bounded_clinear A\<close>)
  have \<open>Modules.additive (A\<^sup>\<dagger>)\<close>
  proof-
    have \<open>\<langle>((A\<^sup>\<dagger>) (x1 + x2) - ((A\<^sup>\<dagger>) x1 + (A\<^sup>\<dagger>) x2)) , y\<rangle> = 0\<close>
      for x1 x2 y
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close> cinner_diff_left cinner_left_distrib)        
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
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close>)
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
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close>)
    hence \<open>\<langle>((A\<^sup>\<dagger>) (r *\<^sub>C x)) , y\<rangle> =  (\<langle>r *\<^sub>C (A\<^sup>\<dagger>) x , y\<rangle>)\<close>
      for y
      by simp
    hence \<open>\<langle>(((A\<^sup>\<dagger>) (r *\<^sub>C x)) - (r *\<^sub>C (A\<^sup>\<dagger>) x )) , y\<rangle> = 0\<close>
      for y
      by (simp add: \<open>\<And>y. \<langle> (A\<^sup>\<dagger>) (r *\<^sub>C x) , y \<rangle> = \<langle> r *\<^sub>C (A\<^sup>\<dagger>) x , y \<rangle>\<close> cinner_diff_left)
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
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close>)
    moreover have  \<open>\<bar>\<langle>x , (A ((A\<^sup>\<dagger>) x))\<rangle>\<bar> \<le> \<parallel>x\<parallel> *  \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close>
      for x
      by (simp add: complex_inner_class.norm_cauchy_schwarz2)
    ultimately have \<open>\<parallel> (A\<^sup>\<dagger>) x \<parallel>^2  \<le> \<parallel>x\<parallel> * \<parallel>A ((A\<^sup>\<dagger>) x)\<parallel>\<close>
      for x
      by (simp add: \<open>\<And>y x. \<langle> (A\<^sup>\<dagger>) x , y \<rangle> = \<langle> x , A y \<rangle>\<close> complex_inner_class.norm_cauchy_schwarz power2_norm_eq_cinner)
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



end
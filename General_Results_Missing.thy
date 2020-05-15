section \<open>\<open>General_Results_Missing\<close> -- Miscellaneous missing facts\<close>

theory General_Results_Missing
  imports Complex_Main Complex_Inner_Product "HOL-Analysis.Infinite_Set_Sum"
    "HOL-ex.Sketch_and_Explore" HOL.Groups
begin


(* TODO: Never used in Bounded Operators. Move to tensor product. *)
(* Jose: I do not know how to move information from one library to another *)
(* TODO: Should be possible now because you have both libraries in GitHub Desktop now *)
lemma big_sum_reordering_fst:
  fixes  S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. f z) = (\<Sum>u\<in>fst ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>S}. f (u, v)))\<close>
proof-
  define g where \<open>g z = (if z \<in> S then f z else 0)\<close>
    for z
  have \<open>(\<Sum>z\<in>S. f z) = (\<Sum>z\<in>S. g z)\<close>
    unfolding g_def
    by auto
  also have \<open>\<dots>  = (\<Sum>z\<in>((fst ` S) \<times> (snd ` S)). g z)\<close>
  proof-
    have \<open>S \<subseteq> ((fst ` S) \<times> (snd ` S))\<close>
      by (simp add: subset_fst_snd)
    thus ?thesis unfolding g_def
      by (smt DiffD2 assms finite_SigmaI finite_imageI sum.mono_neutral_right)
        (* > 1s *)
  qed
  also have \<open>\<dots>  = (\<Sum>u\<in>(fst ` S). (\<Sum>v\<in>(snd ` S). g (u,v)))\<close>
    by (simp add: sum.cartesian_product)
  also have \<open>\<dots>  = (\<Sum>u\<in>(fst ` S). (\<Sum>v\<in>{v|v. (u,v)\<in>S}.  f (u, v)) )\<close>
  proof-
    have \<open>u \<in> fst ` S \<Longrightarrow> (\<Sum>v\<in>(snd ` S). g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}.  f (u, v))\<close>
      for u
    proof-
      have \<open>{v|v. (u,v)\<in>S} \<subseteq> (snd ` S)\<close>
        using image_iff by fastforce
      hence \<open>(\<Sum>v\<in>(snd ` S). g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}. g (u,v))
             + (\<Sum>v\<in>(snd ` S)-{v|v. (u,v)\<in>S}. g (u,v))\<close>
        by (simp add: add.commute assms sum.subset_diff)
      moreover have \<open>(\<Sum>v\<in>(snd ` S)-{v|v. (u,v)\<in>S}. g (u,v)) = 0\<close>
        by (simp add: g_def)        
      moreover have \<open>(\<Sum>v\<in>{v|v. (u,v)\<in>S}. g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}. f (u,v))\<close>
        unfolding g_def
        by auto
      ultimately show ?thesis by auto
    qed
    thus ?thesis
      by auto 
  qed
  finally show ?thesis by blast
qed

(* TODO: Never used in Bounded Operators. Move to tensor product. *)
lemma swap_set_fst:
  \<open>fst ` (prod.swap ` S) = snd ` S\<close>
  unfolding prod.swap_def apply auto
   apply (simp add: rev_image_eqI)
  by (metis (no_types, lifting) fst_conv image_cong image_eqI pair_in_swap_image prod.swap_def)

(* TODO: Never used in Bounded Operators. Move to tensor product. *)
lemma swap_set_snd:
  \<open>snd ` (prod.swap ` S) = fst ` S\<close>
  unfolding prod.swap_def apply auto
   apply (simp add: rev_image_eqI)
  using image_iff by fastforce

(* TODO: Never used in Bounded Operators. Move to tensor product. *)
lemma big_sum_reordering_snd:
  fixes  S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. f z) = (\<Sum>v\<in>snd ` S. (\<Sum>u\<in>{u|u. (u,v)\<in>S}. f (u, v)))\<close>
proof-
  have \<open>prod.swap \<circ> (prod.swap::('a \<times> 'b \<Rightarrow> 'b \<times> 'a)) = id\<close>
    by simp    
  hence \<open>(\<Sum>z\<in>S. f z) = (\<Sum>z\<in>prod.swap ` (prod.swap ` S). f z)\<close>
    by (simp add: \<open>prod.swap \<circ> prod.swap = id\<close> image_comp)
  also have \<open>\<dots> = (\<Sum>z\<in>(prod.swap ` S). (f \<circ> prod.swap) z)\<close>
  proof-
    have \<open>inj prod.swap\<close>
      by simp      
    show ?thesis
      by (meson \<open>inj prod.swap\<close> inj_def inj_on_def sum.reindex)    
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>fst ` (prod.swap ` S). (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. (f \<circ> prod.swap) (u,v)))\<close>
  proof-
    have \<open>finite (prod.swap ` S)\<close>
      using \<open>finite S\<close> by simp
    thus ?thesis
      using big_sum_reordering_fst[where S = "prod.swap ` S" and f = "f \<circ> prod.swap"]
      by blast
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. (f \<circ> prod.swap) (u,v)))\<close>
  proof-
    have \<open>fst ` (prod.swap ` S) = snd ` S\<close>
      by (simp add: swap_set_fst) 
    thus ?thesis by simp
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. f (v,u) ))\<close>
  proof-
    have \<open>prod.swap (u, v) = (v, u)\<close>
      for u::'a and v::'b
      unfolding prod.swap_def by auto
    hence \<open>(f \<circ> prod.swap) (u, v) = f (v, u)\<close>
      for v::'a and u::'b
      by simp
    thus ?thesis by simp      
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (v,u)\<in>S}. f (v,u) ))\<close>
  proof-
    have \<open>(u,v)\<in>(prod.swap ` S) \<longleftrightarrow> (v,u)\<in>S\<close>
      for u v
      by simp
    thus ?thesis by simp
  qed
  finally show ?thesis by blast
qed

class not_singleton =
  assumes not_singleton_card: "\<exists>x y. x \<noteq> y"

lemma not_singleton_existence[simp]:
  \<open>\<exists> x::('a::not_singleton). x \<noteq> t\<close>
proof (rule classical)
  assume \<open>\<nexists>x. (x::'a) \<noteq> t\<close> 
  have \<open>\<exists> x::'a. \<exists> y::'a. x \<noteq> y\<close>
    using not_singleton_card
    by blast
  then obtain x y::'a where \<open>x \<noteq> y\<close>
    by blast
  have \<open>\<forall> x::'a. x = t\<close>
    using \<open>\<nexists>x. (x::'a) \<noteq> t\<close> by simp
  hence \<open>x = t\<close>
    by blast
  moreover have \<open>y = t\<close>
    using \<open>\<forall> x::'a. x = t\<close>
    by blast
  ultimately have \<open>x = y\<close>
    by simp
  thus ?thesis using \<open>x \<noteq> y\<close> by blast
qed

lemma UNIV_not_singleton[simp]: "(UNIV::_::not_singleton set) \<noteq> {x}"
  using not_singleton_existence[of x] by blast

(* lemma UNIV_not_singleton_converse: "(\<And> x. (UNIV::'a set) \<noteq> {x}) \<Longrightarrow> \<exists>x::'a. \<exists>y::'a. x \<noteq> y"
  by fastforce *)

(* lemma UNIV_not_singleton_converse_zero: "((UNIV::('a::real_normed_vector) set) \<noteq> {0}) \<Longrightarrow> \<exists>x::'a. \<exists>y::'a. x \<noteq> y"
  using UNIV_not_singleton_converse
  by fastforce  *)

subclass (in card2) not_singleton
  apply standard using two_le_card
  by (meson card_2_exists ex_card) 

lemma linear_space_top_not_bot[simp]: 
  "(top::'a::{complex_vector,t1_space,not_singleton} linear_space) \<noteq> bot"
  (* The type class t1_space is needed because the definition of bot in linear_space needs it *)
  by (metis General_Results_Missing.UNIV_not_singleton bot_linear_space.rep_eq top_linear_space.rep_eq)

lemma linear_space_bot_not_top[simp]:
  "(bot::'a::{complex_vector,t1_space,not_singleton} linear_space) \<noteq> top"
  using linear_space_top_not_bot by metis

typedef 'a euclidean_space = "UNIV :: ('a \<Rightarrow> real) set" ..
setup_lifting type_definition_euclidean_space

instantiation euclidean_space :: (type) real_vector begin
lift_definition plus_euclidean_space :: "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" is "\<lambda>f g x. f x + g x" .
lift_definition zero_euclidean_space :: "'a euclidean_space" is "\<lambda>_. 0" .
lift_definition uminus_euclidean_space :: "'a euclidean_space \<Rightarrow> 'a euclidean_space" is "\<lambda>f x. - f x" .
lift_definition minus_euclidean_space :: "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" is "\<lambda>f g x. f x - g x" .
lift_definition scaleR_euclidean_space :: "real \<Rightarrow> 'a euclidean_space \<Rightarrow> 'a euclidean_space" is "\<lambda>c f x. c * f x" .
instance
  apply intro_classes
  by (transfer; auto intro: distrib_left distrib_right)+
end

instantiation euclidean_space :: (finite) real_inner begin
lift_definition inner_euclidean_space :: "'a euclidean_space \<Rightarrow> 'a euclidean_space \<Rightarrow> real"
  is "\<lambda>f g. \<Sum>x\<in>UNIV. f x * g x :: real" .
definition "norm_euclidean_space (x::'a euclidean_space) = sqrt (x \<bullet> x)"
definition "dist_euclidean_space (x::'a euclidean_space) y = norm (x-y)"
definition "sgn x = x /\<^sub>R norm x" for x::"'a euclidean_space"
definition "uniformity = (INF e\<in>{0<..}. principal {(x::'a euclidean_space, y). dist x y < e})"
definition "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x'::'a euclidean_space, y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
instance
proof intro_classes
  fix x :: "'a euclidean_space"
    and y :: "'a euclidean_space"
      and z :: "'a euclidean_space"
  show "dist (x::'a euclidean_space) y = norm (x - y)"
    and "sgn (x::'a euclidean_space) = x /\<^sub>R norm x"
    and "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a euclidean_space) y < e})"
    and "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a euclidean_space) = x \<longrightarrow> y \<in> U)"
    and "norm x = sqrt (x \<bullet> x)" for U
    unfolding dist_euclidean_space_def norm_euclidean_space_def sgn_euclidean_space_def
      uniformity_euclidean_space_def open_euclidean_space_def
    by simp_all

  show "x \<bullet> y = y \<bullet> x"
    apply transfer
    by (simp add: mult.commute)
  show "(x + y) \<bullet> z = x \<bullet> z + y \<bullet> z"
    apply transfer
    apply (subst sum.distrib[symmetric])
    by (simp add: distrib_left mult.commute)
  show "r *\<^sub>R x \<bullet> y = r * (x \<bullet> y)" for r :: real
    apply transfer
    apply (subst sum_distrib_left)
    by (simp add: mult.assoc)
  show "0 \<le> x \<bullet> x"
    apply transfer
    by (simp add: sum_nonneg)
  show "(x \<bullet> x = 0) = (x = 0)"
    thm sum_nonneg_eq_0_iff
  proof (transfer, rule)
    fix f :: "'a \<Rightarrow> real"
    assume "(\<Sum>xa\<in>UNIV. f xa * f xa) = 0"
    then have "f x * f x = 0" for x
      apply (rule_tac sum_nonneg_eq_0_iff[THEN iffD1, rule_format, where A=UNIV and x=x])
      by auto
    then show "f = (\<lambda>_. 0)"
      by auto
  qed auto
qed
end

instantiation euclidean_space :: (finite) euclidean_space begin
lift_definition euclidean_space_basis_vector :: "'a \<Rightarrow> 'a euclidean_space" is
  "\<lambda>x. indicator {x}" .
definition "Basis_euclidean_space == (euclidean_space_basis_vector ` UNIV)"
instance
proof intro_classes
  fix u :: "'a euclidean_space"
    and v :: "'a euclidean_space"
  show "(Basis::'a euclidean_space set) \<noteq> {}"
    unfolding Basis_euclidean_space_def by simp
  show "finite (Basis::'a euclidean_space set)"
    unfolding Basis_euclidean_space_def by simp
  show "u \<bullet> v = (if u = v then 1 else 0)"
    if "u \<in> Basis" and "v \<in> Basis"
    using that unfolding Basis_euclidean_space_def 
    apply transfer using indicator_eq_0_iff by fastforce
  show "(\<forall>v\<in>Basis. (u::'a euclidean_space) \<bullet> v = 0) = (u = 0)"
    unfolding Basis_euclidean_space_def
    apply transfer
    by auto
qed
end

(* TODO move somewhere appropriate *)
lemma (in vector_space) span_finite_basis_exists:
  assumes "finite A"
  shows "\<exists>B. finite B \<and> independent B \<and> span B = span A \<and> card B = dim A"
proof -
  obtain B where BT1: "B \<subseteq> span A" 
    and BT2: "span A \<subseteq> span B"
    and indep: "independent B"  
    and card: "card B = dim (span A)"
    using basis_exists[where V="span A"]
    by metis
  have "finite B"
    using assms indep BT1 by (rule independent_span_bound[THEN conjunct1])
  moreover from BT1 BT2 have BT: "span B = span A"
    using span_mono span_span by blast
  moreover from card have "card B = dim (span A)"
    by auto
  moreover note indep
  ultimately show ?thesis
    by auto
qed


end


(*  Title:      bounded-Operators/bounded_Operators.thy
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


(*
We will derive the properties of bounded operators from 
the properties of Cstar_algebras
*)

theory Bounded_Operators
  imports Complex_L2 "HOL-Library.Adhoc_Overloading" 
    "HOL-Analysis.Abstract_Topology" 
Extended_Sorry

begin
subsection \<open>Preliminaries\<close>

(* The complex numbers are a Hilbert space *)
instantiation complex :: "chilbert_space" begin
instance ..
end

section \<open>The onorm and the complex scalar product\<close>




subsection \<open>bounded operators\<close>

typedef (overloaded) ('a::complex_normed_vector, 'b::complex_normed_vector) bounded
  = \<open>{A::'a \<Rightarrow> 'b. bounded_clinear A}\<close>
  using bounded_clinear_zero by blast

setup_lifting type_definition_bounded

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "zero"
begin
lift_definition zero_bounded :: "('a,'b) bounded" is "\<lambda>x::'a. (0::'b)"
  by (fact bounded_clinear_zero)
instance ..
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "uminus"
begin
lift_definition uminus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded"
  is "\<lambda> f. (\<lambda> t::'a. - (f) t)"
  by (fact bounded_clinear_minus)
instance ..
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "semigroup_add"
begin
lift_definition plus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  \<open>\<lambda> f g. (\<lambda> t. (f) t + (g) t)\<close>
  by (fact bounded_clinear_add)
instance
proof      
  fix a b c :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer by auto
qed
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "comm_monoid_add" begin
instance
proof
  fix a b :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded\<close>
  show \<open>a + b = b + a\<close>
    apply transfer
  proof transfer
    fix a b :: \<open>'a \<Rightarrow> 'b\<close>
    assume \<open>bounded_clinear a\<close> and \<open>bounded_clinear b\<close>
    thus \<open> (\<lambda>t. a t + b t) =
            (\<lambda>t. b t + a t)\<close>
      by (simp add: ordered_field_class.sign_simps(2))
  qed

  fix a :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded\<close>
  show \<open>0 + a = a\<close>
    apply transfer by simp
qed
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "ab_group_add" begin
lift_definition minus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded"
  is \<open>\<lambda> f g.  (\<lambda>t. (f) t - (g) t)\<close>
  by (fact bounded_clinear_sub)

instance
proof
  fix a::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded\<close>
  show \<open>- a + a = 0\<close>
    apply transfer
    by simp

  fix a b::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded\<close>
  show \<open>a - b = a + - b\<close>
    apply transfer by simp
qed
end

lemma PREscaleR_bounded:
  fixes c :: real
  assumes \<open>bounded_clinear f\<close>
  shows \<open>bounded_clinear (\<lambda> x. c *\<^sub>R f x )\<close>
proof-
  have  \<open>bounded_clinear (\<lambda> x. (complex_of_real c) *\<^sub>C f x )\<close>
    by (simp add: assms bounded_clinear_const_scaleC)
  thus ?thesis
    by (simp add: scaleR_scaleC) 
qed

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "complex_vector" begin
lift_definition scaleC_bounded :: "complex \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" 
  is \<open>\<lambda> r. \<lambda> f. ( \<lambda> t::'a. r *\<^sub>C f t )\<close>
  by (fact bounded_clinear_const_scaleC)

lift_definition scaleR_bounded :: "real \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" 
  is \<open>\<lambda> r. \<lambda> f. ( \<lambda> t::'a. r *\<^sub>R f t )\<close>
  by (fact PREscaleR_bounded)

instance
  apply intro_classes
proof
  fix r::real and x::\<open>('a, 'b) bounded\<close>
  show \<open>r *\<^sub>R x = complex_of_real r *\<^sub>C x\<close>
    apply transfer
    by (simp add: scaleR_scaleC) 

  fix a::complex and x y::\<open>('a, 'b) bounded\<close>
  show \<open>a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    apply transfer
    by (simp add: scaleC_add_right) 

  fix a b and x::\<open>('a, 'b) bounded\<close>
  show \<open>(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x\<close>
    apply transfer
    by (simp add: scaleC_add_left)

  fix a b::complex and x :: \<open>('a, 'b) bounded\<close>
  show \<open>a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x\<close>
    apply transfer by simp

  fix x::\<open>('a, 'b) bounded\<close>
  show \<open>1 *\<^sub>C x = x\<close>
    apply transfer by simp
qed
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "dist_norm" begin
lift_definition norm_bounded :: \<open>('a, 'b) bounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f. onorm (f)\<close>.
lift_definition dist_bounded :: \<open>('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. onorm (f - g) \<close>.

instance
  apply intro_classes
  apply transfer
proof transfer
  fix x y :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>bounded_clinear x\<close> and \<open>bounded_clinear y\<close>
  show \<open>onorm (x - y) =
           onorm ( ( (\<lambda>t. x t - y t)))\<close>
    by (meson minus_apply) 
qed
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "sgn_div_norm" begin
lift_definition sgn_bounded :: \<open>('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded\<close>
  is \<open>\<lambda> f::('a, 'b) bounded. f /\<^sub>R norm f\<close>.

instance
  apply intro_classes
  by (metis (mono_tags, lifting) Bounded_Operators.sgn_bounded.transfer)
end


instantiation bounded :: (complex_normed_vector, complex_normed_vector) "uniformity_dist" begin
lift_definition uniformity_bounded :: \<open>(('a, 'b) bounded \<times> ('a, 'b) bounded) filter\<close>
  is \<open>(INF e:{0<..}. principal {((f::('a, 'b) bounded), g). dist f g < e})\<close> .

instance
  apply intro_classes
  by (simp add: uniformity_bounded.transfer)
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "open_uniformity" begin
lift_definition open_bounded :: \<open>(('a, 'b) bounded) set \<Rightarrow> bool\<close>
  is \<open>\<lambda> U::(('a, 'b) bounded) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)\<close>.
instance
  apply intro_classes
  apply auto
   apply (metis (mono_tags, lifting) open_bounded.transfer)
  by (smt case_prod_beta eventually_mono open_bounded.transfer)
end

instantiation bounded :: (complex_normed_vector, complex_normed_vector) "complex_normed_vector" begin
instance
  apply intro_classes
     apply auto
proof transfer
  fix x :: "'a \<Rightarrow> 'b"
  assume \<open>bounded_clinear x\<close>
    and \<open>onorm x = 0\<close>
  then show \<open>x = (\<lambda>_::'a. 0::'b)\<close>
    using onorm_zero bounded_clinear.bounded_linear onorm_pos_lt by fastforce
next 
  show \<open>norm (0::('a,'b) bounded) = 0\<close>
    apply transfer
    by (simp add: onorm_zero) 
next
  fix x y :: \<open>('a, 'b) bounded\<close>
  show \<open>norm (x + y) \<le> norm x + norm y\<close>
    apply transfer using  bounded_clinear.bounded_linear
    by (simp add: bounded_clinear.bounded_linear onorm_triangle) 

next
  fix a :: real  and x :: \<open>('a, 'b) bounded\<close>
  show \<open>norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x\<close>
    apply transfer
    using bounded_clinear.bounded_linear onorm_scaleR by auto
next
  fix a :: complex  and x :: \<open>('a, 'b) bounded\<close>
  show \<open>norm (a *\<^sub>C x) = cmod a * norm x\<close>
    apply transfer
    using onorm_scalarC by blast
qed

end

lemma clinear_limit_clinear:
  fixes f :: \<open>nat \<Rightarrow> ('a::complex_vector \<Rightarrow> 'b::complex_normed_vector)\<close>
    and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. clinear (f n)\<close> 
    and  \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
  shows \<open>clinear F\<close> 
proof-
  have \<open>linear F\<close>
  proof-
    have \<open>linear (f n)\<close>
      for n
      using clinear_linear \<open>\<And> n. clinear (f n)\<close>
      by auto
    thus ?thesis using \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> by (rule linear_limit_linear) 
    qed
  moreover have "F (r *\<^sub>C x) = r *\<^sub>C F x"
    for r :: complex
      and x :: 'a
  proof-
    have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      by (simp add: assms(2))
    moreover have \<open>(\<lambda> n.  (f n) (r *\<^sub>C x)) \<longlonglongrightarrow> F (r *\<^sub>C x)\<close>
      by (simp add: assms(2))
    moreover have \<open>lim (\<lambda> n.  (f n) (r *\<^sub>C x)) = r *\<^sub>C lim (\<lambda> n. (f n) x)\<close>
    proof-
      have \<open>(f n) (r *\<^sub>C x) = r *\<^sub>C (f n) x\<close>
        for n
        using  \<open>\<And> n.  clinear (f n)\<close>
        unfolding clinear_def
        unfolding Modules.additive_def
        unfolding clinear_axioms_def
        by blast
      hence \<open>lim (\<lambda> n. (f n) (r *\<^sub>C x)) = lim (\<lambda> n. r *\<^sub>C (f n) x)\<close>
        by simp
      show ?thesis 
      proof-
        have \<open>convergent (\<lambda> n. (f n) x)\<close>
          using \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> convergentI by auto
        moreover have \<open>isCont (\<lambda> t::'b. r *\<^sub>C t) tt\<close>
          for tt
          by (simp add: bounded_clinear_scaleC_right bounded_linear_continuous)
        ultimately have \<open>lim (\<lambda> n. r *\<^sub>C ((f n) x)) =  r *\<^sub>C lim (\<lambda> n. (f n) x)\<close>
          by (metis (mono_tags) assms(2) isCont_tendsto_compose limI)
        thus ?thesis using  \<open>lim (\<lambda> n. (f n) (r *\<^sub>C x)) = lim (\<lambda> n. r *\<^sub>C (f n) x)\<close>
          by simp
      qed
    qed
    ultimately show ?thesis
      by (metis limI) 
  qed
  ultimately show ?thesis  
    by (metis clinearI linear_add)  
qed

lemma bounded_clinear_limit_bounded_clinear:
  fixes f :: \<open>nat \<Rightarrow> ('a::{cbanach, perfect_space} \<Rightarrow> 'b::complex_normed_vector)\<close>
    and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. bounded_clinear (f n)\<close> 
    and  \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
  shows \<open>bounded_clinear F\<close>
proof-
  have \<open>clinear F\<close>
    using assms(1) assms(2) bounded_clinear.clinear clinear_limit_clinear by blast
  moreover have \<open>bounded_clinear_axioms F\<close>
  proof-
    from \<open>\<And> n. bounded_clinear (f n)\<close> 
    have \<open>\<And> n. bounded_linear (f n)\<close>
      by (simp add: bounded_clinear.bounded_linear)
    hence \<open>bounded_linear F\<close>
      using \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
      by (rule bounded_linear_limit_bounded_linear)
    thus ?thesis unfolding bounded_linear_def bounded_linear_axioms_def bounded_clinear_axioms_def
      by blast
  qed
  ultimately show ?thesis unfolding bounded_clinear_def by blast
qed

(* NEW *)
lemma pointwise_convergent_onorm:
  fixes f :: \<open>nat \<Rightarrow> ('a::cbanach, 'b::cbanach) bounded\<close>
    and F :: \<open>('a,'b) bounded\<close>
  (* assumes \<open>bounded_clinear F\<close>  *)
  assumes  \<open>\<And> x::'a. (\<lambda> n. Rep_bounded (f n) x) \<longlonglongrightarrow> Rep_bounded F x\<close>
  shows \<open>f \<longlonglongrightarrow> F\<close>
  by (cheat bounded_linear_convergence)

(* TODO: fix proof, Exercise III.2.1 in Conway func analysis *)
lemma Cauchy_linear_operators:
  fixes f :: \<open>nat \<Rightarrow> ('a::complex_normed_vector, 'b::cbanach) bounded\<close>
  assumes \<open>Cauchy f\<close>
  shows \<open>convergent f\<close>
proof-
  have \<open>Cauchy (\<lambda> n. (Rep_bounded (f n)) x)\<close>
    if "x\<noteq>0" for x::'a
  proof (rule metric_CauchyI)
    fix \<epsilon>
    have geq0: "\<epsilon> / norm x > 0"
      sorry
    from \<open>Cauchy f\<close>
    obtain N where \<open>\<forall> m \<ge> N. \<forall> n \<ge> N. dist (f n) (f m) < \<epsilon> / norm x\<close>
      apply atomize_elim using geq0 metric_CauchyD by blast

    have \<open>\<forall>m\<ge>N. \<forall>n\<ge>N. dist (Rep_bounded (f m) x) (Rep_bounded (f n) x) < \<epsilon>\<close>
    proof auto
      fix m n assume "m\<ge>N" and "n\<ge>N"
      have "dist (Rep_bounded (f m) x) (Rep_bounded (f n) x) = norm (Rep_bounded (f m - f n) x)"
        sorry
      also have "\<dots> \<le> norm (f m - f n) * norm x"
        sorry
      also have "\<dots> = dist (f n) (f m) * norm x"
        sorry
      also have "\<dots> < \<epsilon>"
        sorry
      finally show "dist (Rep_bounded (f m) x) (Rep_bounded (f n) x) < \<epsilon>"
        by simp
    qed
    thus \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (Rep_bounded (f m) x) (Rep_bounded (f n) x) < \<epsilon>\<close>
      by blast 
  qed
  hence \<open>Cauchy (\<lambda> n. (Rep_bounded (f n)) x)\<close>
    for x::'a
    apply (cases "x=0") apply auto sorry
  hence \<open>convergent (\<lambda> n. (Rep_bounded (f n)) x)\<close>
    for x::'a
    by (simp add: Cauchy_convergent_iff)
  then obtain F :: \<open>('a,'b) bounded\<close> where \<open>(\<lambda> n. (Rep_bounded (f n)) x) \<longlonglongrightarrow> Rep_bounded F x\<close>
    for x::'a
  proof (atomize_elim , transfer , simp)
    fix fa :: "nat \<Rightarrow> 'a \<Rightarrow> 'b"
    assume "\<forall>x. bounded_clinear (fa (x::nat)::'a \<Rightarrow> 'b)"
      and "\<And>x. convergent (\<lambda>n. fa n (x::'a)::'b)"
      and "\<And>x. convergent (\<lambda>n. Rep_bounded (f n) x)"
    show "\<exists>F. bounded_clinear F \<and> (\<forall>x. (\<lambda>n. fa n (x::'a)) \<longlonglongrightarrow> (F x::'b))"
      sorry
  qed
  have \<open>f \<longlonglongrightarrow> F\<close>
    sorry
    (* TODO *)
(*   proof -
    have  \<open>bounded_clinear (Rep_bounded (f n))\<close>
      for n
      apply transfer apply auto done
    hence \<open>bounded_clinear F\<close>
      using bounded_clinear_limit_bounded_clinear \<open>\<And>x. (\<lambda>n. Rep_bounded (f n) x) \<longlonglongrightarrow> F x\<close>
        (* by metis *) (* does not terminate *)
      by (cheat metis_failed)
    thus ?thesis
      using pointwise_convergent_onorm
        \<open>\<And>x. (\<lambda>n. Rep_bounded (f n) x) \<longlonglongrightarrow> F x\<close> by blastx 
  qed *)
  thus ?thesis unfolding convergent_def by blast
qed

instantiation bounded :: (complex_normed_vector, cbanach) "cbanach" begin
instance
  apply intro_classes
  apply transfer
  using Cauchy_linear_operators by blast
end



lift_definition idOp :: "('a::complex_normed_vector,'a) bounded" is id
  by (metis bounded_clinear_ident comp_id fun.map_ident)

(* instantiation l2bounded :: (type,type) zero begin
lift_definition zero_l2bounded :: "('a,'b) l2bounded" is "\<lambda>_. 0" by simp
instance ..
end *)

(* TODO define for bounded *)
lift_definition timesOp :: 
  "('b::complex_normed_vector,'c::complex_normed_vector) bounded
     \<Rightarrow> ('a::complex_normed_vector,'b) bounded \<Rightarrow> ('a,'c) bounded" 
  is "(o)"
  unfolding o_def 
  by (rule bounded_clinear_compose, simp_all)

(* TODO: rename bounded_clinearE' *)
lemma bound_op_characterization: 
  \<open>bounded_clinear f \<Longrightarrow> \<exists>K. \<forall>x. K \<ge> 0 \<and> norm (f x) \<le> norm x * K\<close>
  by (metis (mono_tags) bounded_clinear.bounded mult_zero_left  norm_eq_zero  norm_le_zero_iff order.trans ordered_field_class.sign_simps(24) zero_le_mult_iff)

lemma bounded_clinear_comp:
  \<open>bounded_clinear f \<Longrightarrow> bounded_clinear g \<Longrightarrow> bounded_clinear (f \<circ> g)\<close>
proof-
  include notation_norm 
  assume \<open>bounded_clinear f\<close>
  assume \<open>bounded_clinear g\<close>
  have \<open>clinear (f \<circ> g)\<close>
  proof-
    have \<open>clinear f\<close>
      by (simp add: \<open>bounded_clinear f\<close> bounded_clinear.clinear)
    moreover have \<open>clinear g\<close>
      by (simp add: \<open>bounded_clinear g\<close> bounded_clinear.clinear)
    ultimately show ?thesis
    proof - (* automatically generated *)
      obtain cc :: "('c \<Rightarrow> 'b) \<Rightarrow> complex" and cca :: "('c \<Rightarrow> 'b) \<Rightarrow> 'c" where
        f1: "\<forall>x0. (\<exists>v1 v2. x0 (v1 *\<^sub>C v2) \<noteq> v1 *\<^sub>C x0 v2) = (x0 (cc x0 *\<^sub>C cca x0) \<noteq> cc x0 *\<^sub>C x0 (cca x0))"
        by moura
      obtain ccb :: "('c \<Rightarrow> 'b) \<Rightarrow> 'c" and ccc :: "('c \<Rightarrow> 'b) \<Rightarrow> 'c" where
        f2: "\<forall>x0. (\<exists>v1 v2. x0 (v1 + v2) \<noteq> x0 v1 + x0 v2) = (x0 (ccb x0 + ccc x0) \<noteq> x0 (ccb x0) + x0 (ccc x0))"
        by moura
      have "\<forall>c ca. g (c + ca) = g c + g ca"
        by (meson Modules.additive_def \<open>clinear g\<close> clinear.axioms(1))
      then have f3: "(f \<circ> g) (ccb (f \<circ> g) + ccc (f \<circ> g)) = (f \<circ> g) (ccb (f \<circ> g)) + (f \<circ> g) (ccc (f \<circ> g))"
        by (simp add: \<open>clinear f\<close> additive.add clinear.axioms(1))
      have "(f \<circ> g) (cc (f \<circ> g) *\<^sub>C cca (f \<circ> g)) = cc (f \<circ> g) *\<^sub>C (f \<circ> g) (cca (f \<circ> g))"
        by (simp add: \<open>clinear f\<close> \<open>clinear g\<close> clinear.scaleC)
      then show ?thesis
        using f3 f2 f1 by (meson clinearI)
    qed
  qed
  moreover have \<open>\<exists>K. \<forall>x. \<parallel>(f \<circ> g) x\<parallel> \<le> \<parallel>x\<parallel> * K\<close>
  proof-
    have \<open>\<exists> K\<^sub>f. \<forall>x. K\<^sub>f \<ge> 0 \<and> \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>f\<close>
      using \<open>bounded_clinear f\<close> bound_op_characterization 
      by blast
    then obtain K\<^sub>f where \<open> K\<^sub>f \<ge> 0\<close> and \<open>\<forall>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>f\<close>
      by metis
    have \<open>\<exists> K\<^sub>g. \<forall>x. \<parallel>g x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>g\<close>
      using \<open>bounded_clinear g\<close> bounded_clinear.bounded by blast 
    then obtain K\<^sub>g where \<open>\<forall>x. \<parallel>g x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>g\<close>
      by metis
    have \<open>\<parallel>(f \<circ> g) x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>g * K\<^sub>f\<close>
      for x
    proof-                             
      have \<open>\<parallel>(f \<circ> g) x\<parallel> \<le> \<parallel>f (g x)\<parallel>\<close>
        by simp
      also have \<open>... \<le> \<parallel>g x\<parallel> * K\<^sub>f\<close>
        by (simp add: \<open>\<forall>x. \<parallel>f x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>f\<close>)
      also have \<open>... \<le> (\<parallel>x\<parallel> * K\<^sub>g) * K\<^sub>f\<close>
        using \<open>K\<^sub>f \<ge> 0\<close>
        by (metis \<open>\<forall>x. \<parallel>g x\<parallel> \<le> \<parallel>x\<parallel> * K\<^sub>g\<close> mult.commute ordered_comm_semiring_class.comm_mult_left_mono)
      finally show ?thesis
        by simp
    qed
    thus ?thesis 
      by (metis  comp_eq_dest_lhs linordered_field_class.sign_simps(23) )
  qed
  ultimately show ?thesis 
    using bounded_clinear_def bounded_clinear_axioms_def by blast
qed

lemma is_linear_manifold_image:
  assumes "clinear f" and "is_linear_manifold S"
  shows "is_linear_manifold (f ` S)"
  apply (rule is_linear_manifold.intro)
  subgoal proof - (* sledgehammer proof *)
    fix x :: 'b and y :: 'b
    assume a1: "x \<in> f ` S"
    assume a2: "y \<in> f ` S"
    obtain aa :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 = x1 v3) = (aa x0 x1 x2 \<in> x0 \<and> x2 = x1 (aa x0 x1 x2))"
      by moura
    then have f3: "\<forall>b f A. (b \<notin> f ` A \<or> aa A f b \<in> A \<and> b = f (aa A f b)) \<and> (b \<in> f ` A \<or> (\<forall>a. a \<notin> A \<or> b \<noteq> f a))"
      by blast
    then have "aa S f x + aa S f y \<in> S"
      using a2 a1 by (metis (no_types) assms(2) is_linear_manifold_def)
    then show "x + y \<in> f ` S"
      using f3 a2 a1 by (metis (no_types) additive.add assms(1) clinear.axioms(1))
  qed
  subgoal proof -
    fix x :: 'b and c :: complex
    assume a1: "x \<in> f ` S"
    obtain aa :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a" where
      "\<forall>x0 x1 x2. (\<exists>v3. v3 \<in> x0 \<and> x2 = x1 v3) = (aa x0 x1 x2 \<in> x0 \<and> x2 = x1 (aa x0 x1 x2))"
      by moura
    then have f2: "aa S f x \<in> S \<and> x = f (aa S f x)"
      using a1 by (simp add: Bex_def_raw image_iff)
    then have "c *\<^sub>C x = f (c *\<^sub>C aa S f x)"
      by (metis (no_types) assms(1) clinear_axioms_def clinear_def)
    then show "c *\<^sub>C x \<in> f ` S"
      using f2 by (metis (no_types) assms(2) image_iff is_linear_manifold_def)
  qed
  by (metis Complex_Vector_Spaces.eq_vector_fraction_iff \<open>\<And>x c. x \<in> f ` S \<Longrightarrow> c *\<^sub>C x \<in> f ` S\<close> assms(2) imageI is_linear_manifold_def)

lemma PREapplyOpSpace:
  fixes f::\<open>('a::chilbert_space) \<Rightarrow> ('b::chilbert_space)\<close>
    and S::\<open>'a set\<close>
    (* assumes \<open>bounded_clinear f\<close> and \<open>is_subspace S\<close> *)
  assumes "clinear f" and "is_linear_manifold S"
  shows  \<open>is_subspace (closure {f x |x. x \<in> S})\<close> (* TODO: use f ` S *)
proof -
  have "is_linear_manifold {f x |x. x \<in> S}"
    using assms is_linear_manifold_image
    by (simp add: is_linear_manifold_image Setcompr_eq_image)
  then show \<open>is_subspace (closure {f x |x. x \<in> S})\<close>
    apply (rule_tac is_subspace.intro)
    using is_subspace_cl apply blast
    by blast
qed

(* 
proof-
  have \<open>bounded_clinear (proj S)\<close>
    using \<open>is_subspace S\<close> projPropertiesA by blast
  hence \<open>bounded_clinear (f \<circ> (proj S))\<close>
    using  \<open>bounded_clinear f\<close> bounded_clinear_comp by blast
  hence \<open>clinear (f \<circ> (proj S))\<close>
    unfolding bounded_clinear_def
    by blast
  hence \<open>is_linear_manifold (ran_op (f \<circ> (proj S)))\<close>
    using ran_op_lin
    by blast
  hence \<open>is_linear_manifold {x. \<exists> y. (f \<circ> (proj S)) y = x}\<close>
    unfolding ran_op_def by blast
  moreover have \<open>{f x |x. x \<in> S} = {x. \<exists> y. (f \<circ> (proj S)) y = x}\<close>
    by (metis assms(2) comp_apply proj_fixed_points proj_intro2)
  ultimately have  \<open>is_linear_manifold {f x |x. x \<in> S}\<close>
    by simp
  hence  \<open>is_linear_manifold (closure {f x |x. x \<in> S})\<close>
    by (simp add: is_subspace_cl)
  moreover have \<open>closed (closure {f x |x. x \<in> S})\<close>
    by auto
  ultimately show ?thesis
    using is_subspace_def by blast
qed
 *)

(* Note that without "closure", applyOpSpace would not in general return a subspace.
   See: https://math.stackexchange.com/questions/801806/is-the-image-of-a-closed-subspace-under-a-bounded-linear-operator-closed *)
(* TODO: use cbanach or complex_normed_vector *)
lift_definition applyOpSpace :: \<open>('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> 'a linear_space \<Rightarrow> 'b linear_space\<close> is
  "\<lambda>A S. closure {A x|x. x\<in>S}"
  using PREapplyOpSpace bounded_clinear_def is_subspace.subspace by blast

(* instantiation bounded :: (chilbert_space,chilbert_space) scaleC begin
lift_definition scaleC_l2bounded :: "complex \<Rightarrow> ('a,'b) l2bounded \<Rightarrow> ('a,'b) l2bounded" is
  "\<lambda>c A x. c *\<^sub>C A x"
  by (rule bounded_clinear_const_scaleC)
lift_definition scaleR_l2bounded :: "real \<Rightarrow> ('a,'b) l2bounded \<Rightarrow> ('a,'b) l2bounded" is
  "\<lambda>c A x. c *\<^sub>R A x"
  by (cheat scaleR_bounded)
instance
  apply standard unfolding scaleC_l2bounded_def scaleR_l2bounded_def
  by (simp add: scaleR_scaleC)
end *)

(* TODO: same for linear_space *)
instantiation linear_space :: (complex_normed_vector) scaleC begin
lift_definition scaleC_linear_space :: "complex \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is
  "\<lambda>c S. scaleC c ` S"
  apply (rule is_subspace.intro)
  using bounded_clinear_def bounded_clinear_scaleC_right is_linear_manifold_image is_subspace.subspace apply blast
  by (simp add: closed_scaleC is_subspace.closed)
lift_definition scaleR_linear_space :: "real \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is
  "\<lambda>c S. scaleR c ` S"
  apply (rule is_subspace.intro)
  apply (metis bounded_clinear_def bounded_clinear_scaleC_right is_linear_manifold_image is_subspace.subspace scaleR_scaleC)
  by (simp add: closed_scaling is_subspace.closed)
instance 
  apply standard
  by (simp add: scaleR_scaleC scaleC_linear_space_def scaleR_linear_space_def)
end

(* TODO chilbert_space \<longrightarrow> cbanach *)
lift_definition
  adjoint :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> ('b,'a) bounded" ("_*" [99] 100) is Adj
  by (fact Adj_bounded_clinear)

lemma applyOp_0[simp]: "applyOpSpace U 0 = 0" 
  apply transfer
  by (simp add: additive.zero bounded_clinear_def clinear.axioms(1))

lemma times_applyOp: "applyOp (timesOp A B) \<psi> = applyOp A (applyOp B \<psi>)" 
  apply transfer by simp

lemma timesScalarSpace_0[simp]: "0 *\<^sub>C S = 0" for S :: "_ linear_space"
  apply transfer apply (auto intro!: exI[of _ 0])
  using  is_linear_manifold.zero is_subspace.subspace  by auto
    (* apply (metis (mono_tags, lifting) Collect_cong bounded_clinear_ident closure_eq is_subspace.closed ker_op_def ker_op_lin mem_Collect_eq) *)
    (*   using  is_linear_manifold.zero is_subspace.subspace
  by (metis (mono_tags, lifting) Collect_cong bounded_clinear_ident is_subspace_cl ker_op_def ker_op_lin) *)



(* TODO rename, e.g., subspace_scale_invariant *)
lemma PREtimesScalarSpace_not0: 
  fixes a S
  assumes \<open>a \<noteq> 0\<close> and \<open>is_subspace S\<close>
    (* TODO: is_linear_manifold instead? *)
  shows \<open>(*\<^sub>C) a ` S = S\<close>
proof-
  have  \<open>x \<in> (*\<^sub>C) a ` S \<Longrightarrow> x \<in> S\<close>
    for x
    using assms(2) is_linear_manifold.smult_closed is_subspace.subspace by fastforce
  moreover have  \<open>x \<in> S \<Longrightarrow> x \<in> (*\<^sub>C) a ` S\<close>
    for x
  proof - (* automatically generated *)
    assume "x \<in> S"
    then have "\<exists>c aa. (c / a) *\<^sub>C aa \<in> S \<and> c *\<^sub>C aa = x"
      using assms(2) is_linear_manifold_def is_subspace.subspace scaleC_one by blast
    then have "\<exists>aa. aa \<in> S \<and> a *\<^sub>C aa = x"
      using assms(1) by auto
    then show ?thesis
      by (meson image_iff)
  qed 
  ultimately show ?thesis by blast
qed

lemma timesScalarSpace_not0[simp]: "a \<noteq> 0 \<Longrightarrow> a *\<^sub>C S = S" for S :: "_ linear_space"
  apply transfer using PREtimesScalarSpace_not0 by blast

lemma one_times_op[simp]: "scaleC (1::complex) B = B" for B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  using Complex_Vector_Spaces.complex_vector.scale_one by auto

lemma scalar_times_adj[simp]: "(a *\<^sub>C A)* = (cnj a) *\<^sub>C (A*)" for A::"(_::complex_normed_vector,_::complex_normed_vector)bounded"
  apply transfer by (cheat scalar_times_adj)

lemma timesOp_assoc: "timesOp (timesOp A B) C = timesOp A (timesOp B C)" 
  apply transfer by auto

lemma times_adjoint[simp]: "adjoint (timesOp A B) = timesOp (adjoint B) (adjoint A)" 
  by (cheat times_adjoint)

lemma PREtimesOp_assoc_linear_space:
  fixes A B S
  assumes \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close>
    and \<open>is_subspace S\<close>
  shows \<open>closure {(A \<circ> B) x |x. x \<in> S} =
       closure {A x |x. x \<in> closure {B x |x. x \<in> S}}\<close>
proof-
  have  \<open>closure {(A \<circ> B) x |x. x \<in> S} \<subseteq>
       closure {A x |x. x \<in> closure {B x |x. x \<in> S}}\<close>
    by (smt closure_mono closure_subset comp_apply mem_Collect_eq subset_iff)
  moreover have  \<open>closure {(A \<circ> B) x |x. x \<in> S} \<supseteq>
       closure {A x |x. x \<in> closure {B x |x. x \<in> S}}\<close>
  proof-
    have \<open>t \<in> {A x |x. x \<in> closure {B x |x. x \<in> S}}
        \<Longrightarrow> t \<in> closure {(A \<circ> B) x |x. x \<in> S}\<close>
      for t
    proof-
      assume \<open>t \<in> {A x |x. x \<in> closure {B x |x. x \<in> S}}\<close>
      then obtain u where 
        \<open>t = A u\<close> and \<open>u \<in> closure {B x |x. x \<in> S}\<close>
        by auto
      from  \<open>u \<in> closure {B x |x. x \<in> S}\<close> 
      obtain v where \<open>v \<longlonglongrightarrow> u\<close>
        and \<open>\<forall> n. v n \<in>  {B x |x. x \<in> S}\<close>
        using closure_sequential by blast
      from  \<open>\<forall> n. v n \<in>  {B x |x. x \<in> S}\<close>
      have \<open>\<forall> n. \<exists> x \<in> S.  v n = B x\<close>
        by auto
      then obtain w where \<open>w n \<in> S\<close> and \<open>v n = B (w n)\<close>
        for n
        by metis
      have \<open>(\<lambda> n. B (w n) ) \<longlonglongrightarrow> u\<close>
        using  \<open>\<And> n. v n = B (w n)\<close> \<open>v \<longlonglongrightarrow> u\<close>
        by presburger
      moreover have \<open>isCont A x\<close>
        for x
        using \<open>bounded_clinear A\<close>
        by (simp add: bounded_linear_continuous)
      ultimately have \<open>(\<lambda> n. A (B (w n)) ) \<longlonglongrightarrow> t\<close>
        using  \<open>t = A u\<close>
          isCont_tendsto_compose by blast
      hence  \<open>(\<lambda> n. (A \<circ> B) (w n) ) \<longlonglongrightarrow> t\<close>
        by simp                               
      thus ?thesis using \<open>\<And> n. w n \<in> S\<close>
        using closure_sequential by fastforce
    qed
    hence \<open> {A x |x. x \<in> closure {B x |x. x \<in> S}}
        \<subseteq> closure {(A \<circ> B) x |x. x \<in> S}\<close>
      by blast
    thus ?thesis
      by (metis (no_types, lifting) closure_closure closure_mono) 
  qed
  ultimately show ?thesis by blast
qed

lemma timesOp_assoc_linear_space: "applyOpSpace (timesOp A B) S = applyOpSpace A (applyOpSpace B S)" 
  apply transfer
  using PREtimesOp_assoc_linear_space by blast

(* instantiation bounded :: (chilbert_space,chilbert_space) ab_group_add begin
lift_definition plus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>a b x. a x + b x"
  by (rule bounded_clinear_add)
lift_definition minus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>a b x. a x - b x"
  by (rule bounded_clinear_sub)
lift_definition uminus_bounded :: "('a,'b) bounded \<Rightarrow> ('a,'b) bounded" is
  "\<lambda>a x. - a x"
  by (rule bounded_clinear_minus)
instance 
  apply intro_classes
  by (transfer; auto)+
end *)

(* TODO: where are these definitions needed? Should they be in qrhl-tool instead? *)
lemmas assoc_left = timesOp_assoc[symmetric] timesOp_assoc_linear_space[symmetric] add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded", symmetric]
lemmas assoc_right = timesOp_assoc timesOp_assoc_linear_space add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded"]

lemma scalar_times_op_add[simp]: "scaleC a (A+B) = scaleC a A + scaleC a B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  by (simp add: scaleC_add_right)

lemma scalar_times_op_minus[simp]: "scaleC a (A-B) = scaleC a A - scaleC a B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  by (simp add: complex_vector.scale_right_diff_distrib)

lemma applyOp_bot[simp]: "applyOpSpace U bot = bot"
  by (simp add: linear_space_zero_bot[symmetric])

lemma equal_basis: "(\<And>x. applyOp A (ket x) = applyOp B (ket x)) \<Longrightarrow> A = B"
  by (cheat equal_basis)

lemma adjoint_twice[simp]: "(U*)* = U" for U :: "(_,_) bounded"
  by (cheat adjoint_twice)


(* TODO: move specialized syntax into QRHL-specific file *)
consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhoc_overloading
  cdot timesOp applyOp applyOpSpace
  (* Removed scaleC here: the overloading cannot be restricted to a specific type, so all occurrences of scaleC become \<cdot> *)

lemma cdot_plus_distrib[simp]: "U \<cdot> (A + B) = U \<cdot> A + U \<cdot> B"
  for A B :: "_ linear_space" and U :: "(_,_) bounded"
  apply transfer 
  by (cheat cdot_plus_distrib)


lemma scalar_op_linear_space_assoc [simp]: 
  "(\<alpha> *\<^sub>C A) \<cdot> S = \<alpha> *\<^sub>C (A \<cdot> S)" for \<alpha>::complex and A::"(_::complex_normed_vector,_::complex_normed_vector)bounded" and S::"(_::complex_normed_vector) linear_space"
  (* using transfer_raw *)
proof transfer
  fix \<alpha> and A::"'a::chilbert_space \<Rightarrow> 'b::chilbert_space" and S
  have "(*\<^sub>C) \<alpha> ` closure {A x |x. x \<in> S} = closure {\<alpha> *\<^sub>C x |x. x \<in> {A x |x. x \<in> S}}" (is "?nested = _")
    by (simp add: closure_scaleC setcompr_eq_image)
  also have "\<dots> = closure {\<alpha> *\<^sub>C A x |x. x \<in> S}" (is "_ = ?nonnested")
    by (simp add: Setcompr_eq_image image_image)
  finally show "?nonnested = ?nested" by simp
qed

lemma apply_idOp[simp]: "applyOp idOp \<psi> = \<psi>"
  by (simp add: idOp.rep_eq)

lemma scalar_mult_0_op[simp]: "0 *\<^sub>C A = 0" for A::"(_,_) bounded"
  apply transfer by auto

lemma scalar_op_op[simp]: "(a *\<^sub>C A) \<cdot> B = a *\<^sub>C (A \<cdot> B)"
  for A :: "('b::complex_normed_vector,_) bounded" and B :: "(_,'b) bounded"
  apply transfer by auto

lemma op_scalar_op[simp]: "timesOp A (a *\<^sub>C B) = a *\<^sub>C (timesOp A B)" 
  for a :: complex and A :: "(_,_) bounded" and B :: "(_,_) bounded"
  apply transfer
  by (simp add: bounded_clinear.clinear clinear.scaleC o_def)

(* REMOVE (subsumed by scale_scale) *)
lemma scalar_scalar_op[simp]: "a *\<^sub>C (b *\<^sub>C A) = (a*b) *\<^sub>C A"
  for a b :: complex and A  :: "(_,_) bounded"
  apply transfer by auto

lemma scalar_op_vec[simp]: "(a *\<^sub>C A) \<cdot> \<psi> = a *\<^sub>C (A \<cdot> \<psi>)" 
  for a :: complex and A :: "(_,_) bounded" and \<psi> :: "'a ell2"
  apply transfer by auto

(* REMOVE (subsumed by scaleC_left_imp_eq) *)
lemma add_scalar_mult: "a\<noteq>0 \<Longrightarrow> a *\<^sub>C A = a *\<^sub>C B \<Longrightarrow> A=B" for A B :: "('a,'b)l2bounded" and a::complex 
  by (rule scaleC_left_imp_eq)

lemma apply_idOp_space[simp]: "applyOpSpace idOp S = S"
  apply transfer by (simp add: is_subspace.closed)

lemma apply_0[simp]: "applyOp U 0 = 0"
  apply transfer 
  using additive.zero bounded_clinear.clinear clinear.axioms(1) by blast

lemma times_idOp1[simp]: "U \<cdot> idOp = U"
  apply transfer by auto

lemma times_idOp2[simp]: "timesOp idOp V = V" for V :: "(_,_) bounded"
  apply transfer by auto

lemma idOp_adjoint[simp]: "idOp* = idOp"
  by (cheat idOp_adjoint)

lemma mult_INF[simp]: "U \<cdot> (INF x. V x) = (INF x. U \<cdot> V x)" 
  for V :: "'a \<Rightarrow> 'b::chilbert_space linear_space" and U :: "('b,'c::chilbert_space) bounded"
  apply transfer apply auto
  by (cheat mult_INF)

lemma mult_inf_distrib[simp]: "U \<cdot> (B \<sqinter> C) = (U \<cdot> B) \<sqinter> (U \<cdot> C)" 
  for U :: "(_,_) bounded" and B C :: "_ linear_space"
  using mult_INF[where V="\<lambda>x. if x then B else C" and U=U]
  unfolding INF_UNIV_bool_expand
  by simp

definition "inj_option \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"
definition "inv_option \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (Hilbert_Choice.inv \<pi> (Some y)) else None)"
lemma inj_option_Some_pi[simp]: "inj_option (Some o \<pi>) = inj \<pi>"
  unfolding inj_option_def inj_def by simp

lemma inj_option_Some[simp]: "inj_option Some"
  using[[show_consts,show_types,show_sorts]]
  apply (rewrite asm_rl[of "(Some::'a\<Rightarrow>_) = Some o id"]) apply simp
  unfolding inj_option_Some_pi by simp

lemma inv_option_Some: "surj \<pi> \<Longrightarrow> inv_option (Some o \<pi>) = Some o (Hilbert_Choice.inv \<pi>)"
  unfolding inv_option_def o_def inv_def apply (rule ext) by auto
lemma inj_option_map_comp[simp]: "inj_option f \<Longrightarrow> inj_option g \<Longrightarrow> inj_option (f \<circ>\<^sub>m g)"
  unfolding inj_option_def apply auto
  by (smt map_comp_Some_iff)

lemma inj_option_inv_option[simp]: "inj_option (inv_option \<pi>)"
proof (unfold inj_option_def, rule allI, rule allI, rule impI, erule conjE)
  fix x y
  assume same: "inv_option \<pi> x = inv_option \<pi> y"
    and pix_not_None: "inv_option \<pi> x \<noteq> None"
  have x_pi: "Some x \<in> range \<pi>" 
    using pix_not_None unfolding inv_option_def apply auto
    by (meson option.distinct(1))
  have y_pi: "Some y \<in> range \<pi>" 
    using pix_not_None unfolding same unfolding inv_option_def apply auto
    by (meson option.distinct(1))
  have "inv_option \<pi> x = Some (Hilbert_Choice.inv \<pi> (Some x))"
    unfolding inv_option_def using x_pi by simp
  moreover have "inv_option \<pi> y = Some (Hilbert_Choice.inv \<pi> (Some y))"
    unfolding inv_option_def using y_pi by simp
  ultimately have "Hilbert_Choice.inv \<pi> (Some x) = Hilbert_Choice.inv \<pi> (Some y)"
    using same by simp
  then show "x = y"
    by (meson inv_into_injective option.inject x_pi y_pi)
qed

lift_definition classical_operator' :: "('a\<Rightarrow>'b option) \<Rightarrow> ('a ell2 \<Rightarrow> 'b ell2)" is
  "\<lambda>\<pi> \<psi> b. case inv_option \<pi> b of Some a \<Rightarrow> \<psi> a | None \<Rightarrow> 0"
  sorry


lift_definition classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> ('a ell2,'b ell2) bounded" is
  "classical_operator'"
  sorry

lemma classical_operator_basis: "inj_option \<pi> \<Longrightarrow>
    applyOp (classical_operator \<pi>) (ket x) = (case \<pi> x of Some y \<Rightarrow> ket y | None \<Rightarrow> 0)"

  by (cheat TODO5)
lemma classical_operator_adjoint[simp]: 
  "inj_option \<pi> \<Longrightarrow> adjoint (classical_operator \<pi>) = classical_operator (inv_option \<pi>)"
  for \<pi> :: "'a \<Rightarrow> 'b option"
  by (cheat TODO1)

lemma classical_operator_mult[simp]:
  "inj_option \<pi> \<Longrightarrow> inj_option \<rho> \<Longrightarrow> classical_operator \<pi> \<cdot> classical_operator \<rho> = classical_operator (map_comp \<pi> \<rho>)"
  apply (rule equal_basis)
  unfolding times_applyOp
  apply (subst classical_operator_basis, simp)+
  apply (case_tac "\<rho> x")
  apply auto
  apply (subst classical_operator_basis, simp)
  by auto

lemma classical_operator_Some[simp]: "classical_operator Some = idOp"
  apply (rule equal_basis) apply (subst classical_operator_basis) apply simp by auto

definition "unitary U = (U \<cdot> (U*) = idOp \<and> U* \<cdot> U = idOp)"  
definition "isometry U = (U* \<cdot> U = idOp)"  

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* \<cdot> U = idOp" unfolding isometry_def by simp
lemma UadjU[simp]: "unitary U \<Longrightarrow> U \<cdot> U* = idOp" unfolding unitary_def by simp

lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"(_,_)bounded"
  unfolding unitary_def by auto

lemma unitary_times[simp]: "unitary A \<Longrightarrow> unitary B \<Longrightarrow> unitary (A\<cdot>B)"
  unfolding unitary_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma isometry_times[simp]: "isometry A \<Longrightarrow> isometry B \<Longrightarrow> isometry (A\<cdot>B)"
  unfolding isometry_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma isometry_classical_operator[simp]:
  assumes "inj \<pi>"
  shows "isometry (classical_operator (Some o \<pi>))"
proof -
  have comp: "inv_option (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>) = Some" 
    apply (rule ext) unfolding inv_option_def o_def 
    using assms unfolding inj_def inv_def by auto

  show ?thesis
    unfolding isometry_def
    apply (subst classical_operator_adjoint) using assms apply simp
    apply (subst classical_operator_mult) using assms apply auto[2]
    apply (subst comp)
    by simp
qed

lemma unitary_classical_operator[simp]:
  assumes "bij \<pi>"
  shows "unitary (classical_operator (Some o \<pi>))"
proof (unfold unitary_def, rule conjI)
  have "isometry (classical_operator (Some o \<pi>))"
    by (simp add: assms bij_is_inj)
  then show "classical_operator (Some \<circ> \<pi>)* \<cdot> classical_operator (Some \<circ> \<pi>) = idOp"
    unfolding isometry_def by simp
next
  have "inj \<pi>"
    by (simp add: assms bij_is_inj)
  have comp: "Some \<circ> \<pi> \<circ>\<^sub>m inv_option (Some \<circ> \<pi>) = Some"
    apply (rule ext)
    unfolding inv_option_def o_def map_comp_def
    unfolding inv_def apply auto
    apply (metis \<open>inj \<pi>\<close> inv_def inv_f_f)
    by (metis assms bij_def image_iff range_eqI)

  show "classical_operator (Some \<circ> \<pi>) \<cdot> classical_operator (Some \<circ> \<pi>)* = idOp"
    by (simp add: comp \<open>inj \<pi>\<close>)
qed

lemma unitary_image[simp]: "unitary U \<Longrightarrow> applyOpSpace U top = top"
  by (cheat TODO1)

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def by simp

(* TODO: Replace by existing class CARD_1 *)
class singleton = fixes the_single :: "'a" assumes everything_the_single: "x=the_single" begin
lemma singleton_UNIV: "UNIV = {the_single}"
  using everything_the_single by auto
lemma everything_the_same: "(x::'a)=y"
  apply (subst everything_the_single, subst (2) everything_the_single) by simp
lemma singleton_ext: "x (a::'a) = y b \<Longrightarrow> x = y"
  apply (rule ext) 
  apply (subst (asm) everything_the_same[where x=a])
  apply (subst (asm) everything_the_same[where x=b])
  by simp
lemma CARD_singleton[simp]: "CARD('a) = 1"
  by (simp add: singleton_UNIV)
subclass finite apply standard unfolding singleton_UNIV by simp  
end

instantiation unit :: singleton begin
definition "singleton = ()"
instance apply standard by auto
end

(* TODO move to L2_Complex *)
lift_definition C1_to_complex :: "'a::singleton ell2 \<Rightarrow> complex" is
  "\<lambda>\<psi>. \<psi> the_single" .
lift_definition complex_to_C1 :: "complex \<Rightarrow> 'a::singleton ell2" is
  "\<lambda>c _. c" 
  by simp

lemma C1_to_complex_inverse[simp]: "complex_to_C1 (C1_to_complex \<psi>) = \<psi>"
  apply transfer apply (rule singleton_ext) by auto

lemma complex_to_C1_inverse[simp]: "C1_to_complex (complex_to_C1 \<psi>) = \<psi>"
  apply transfer by simp

lemma bounded_clinear_complex_to_C1: "bounded_clinear complex_to_C1"
  apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def)+

lemma bounded_clinear_C1_to_complex: "bounded_clinear C1_to_complex"
  apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def singleton_UNIV)+

lift_definition ell2_to_bounded :: "'a::chilbert_space \<Rightarrow> (unit ell2,'a) bounded" is
  "\<lambda>(\<psi>::'a) (x::unit ell2). C1_to_complex x *\<^sub>C \<psi>"
  by (simp add: bounded_clinear_C1_to_complex bounded_clinear_scaleC_const)

lemma ell2_to_bounded_applyOp: "ell2_to_bounded (A\<cdot>\<psi>) = A \<cdot> ell2_to_bounded \<psi>" for A :: "(_,_)bounded"
  apply transfer
  by (simp add: bounded_clinear_def clinear.scaleC o_def)

lemma ell2_to_bounded_scalar_times: "ell2_to_bounded (a *\<^sub>C \<psi>) = a *\<^sub>C ell2_to_bounded \<psi>" for a::complex
  apply (rewrite at "a *\<^sub>C \<psi>" DEADID.rel_mono_strong[of _ "(a *\<^sub>C idOp) \<cdot> \<psi>"])
  apply transfer apply simp
  apply (subst ell2_to_bounded_applyOp)
  by simp

lift_definition kernel :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> 'a linear_space" is ker_op
  by (metis ker_op_lin)

definition eigenspace :: "complex \<Rightarrow> ('a::chilbert_space,'a) bounded \<Rightarrow> 'a linear_space" where
  "eigenspace a A = kernel (A - a *\<^sub>C idOp)" 

lemma kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a *\<^sub>C A) = kernel A"
  for a :: complex and A :: "(_,_) bounded"
  apply transfer
  by (smt Collect_cong complex_vector.scale_eq_0_iff ker_op_def)

lemma kernel_0[simp]: "kernel 0 = top"
  apply transfer unfolding ker_op_def by simp

lemma kernel_id[simp]: "kernel idOp = 0"
  apply transfer unfolding ker_op_def by simp

lemma [simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a *\<^sub>C A) = eigenspace (b/a) A"
  unfolding eigenspace_def
  apply (rewrite at "kernel \<hole>" DEADID.rel_mono_strong[where y="a *\<^sub>C (A - (b / a) *\<^sub>C idOp)"])
  apply auto[1]
  by (subst kernel_scalar_times, auto)

section \<open>Projectors\<close>

(* TODO: link with definition from Complex_Inner (needs definition of adjoint, first) *)
definition "isProjector P = (P=P* \<and> P=P\<cdot>P)"

consts Proj :: "'a linear_space \<Rightarrow> ('a,'a) bounded"
lemma isProjector_Proj[simp]: "isProjector (Proj S)"
  by (cheat TODO5)

lemma imageOp_Proj[simp]: "applyOpSpace (Proj S) top = S"
  by (cheat TODO5)

lemma Proj_leq: "Proj S \<cdot> A \<le> S"
  by (metis imageOp_Proj inf.orderE inf.orderI mult_inf_distrib top_greatest)


lemma Proj_times: "A \<cdot> Proj S \<cdot> A* = Proj (A\<cdot>S)" for A::"(_,_)bounded"
  by (cheat TODO2)

abbreviation proj :: "'a::chilbert_space \<Rightarrow> ('a,'a) bounded" where "proj \<psi> \<equiv> Proj (span {\<psi>})"

lemma proj_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" for a::complex and \<psi>::"'a ell2"
  by (cheat TODO2)


lemma move_plus:
  "Proj (ortho C) \<cdot> A \<le> B \<Longrightarrow> A \<le> B + C"
  for A B C::"_ linear_space"
  by (cheat TODO2)


section \<open>Tensor products\<close>

consts "tensorOp" :: "('a,'b) l2bounded \<Rightarrow> ('c,'d) l2bounded \<Rightarrow> ('a*'c,'b*'d) l2bounded"

lift_definition "tensorVec" :: "'a ell2 \<Rightarrow> 'c ell2 \<Rightarrow> ('a*'c) ell2" is
  "\<lambda>\<psi> \<phi> (x,y). \<psi> x * \<phi> y"
  by (cheat tensorVec)

definition "tensorSpace A B = span {tensorVec \<psi> \<phi>| \<psi> \<phi>. \<psi> \<in> Rep_linear_space A \<and> \<phi> \<in> Rep_linear_space B}"

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<otimes>" 71)
adhoc_overloading tensor tensorOp tensorSpace tensorVec

lemma idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"
  by (cheat TODO2)

consts "comm_op" :: "('a*'b, 'b*'a) l2bounded"

lemma adj_comm_op[simp]: "adjoint comm_op = comm_op"
  by (cheat TODO2)

lemma
  comm_op_swap[simp]: "comm_op \<cdot> (A\<otimes>B) \<cdot> comm_op = B\<otimes>A"
  for A::"('a,'b) l2bounded" and B::"('c,'d) l2bounded"
  by (cheat TODO3)

lemma comm_op_times_comm_op[simp]: "comm_op \<cdot> comm_op = idOp"
proof -
  find_theorems "idOp \<otimes> idOp"
  have "comm_op \<cdot> (idOp \<otimes> idOp) \<cdot> comm_op = idOp \<otimes> idOp" by (simp del: idOp_tensor_idOp)
  then show ?thesis by simp
qed

lemma unitary_comm_op[simp]: "unitary comm_op"
  unfolding unitary_def by simp

consts "assoc_op" :: "('a*'b*'c, ('a*'b)*'c) l2bounded"
lemma unitary_assoc_op[simp]: "unitary assoc_op"
  by (cheat TODO5)

lemma tensor_scalar_mult1[simp]: "(a *\<^sub>C A) \<otimes> B = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)
lemma tensor_scalar_mult2[simp]: "A \<otimes> (a *\<^sub>C B) = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)

lemma tensor_times[simp]: "(U1 \<otimes> U2) \<cdot> (V1 \<otimes> V2) = (U1 \<cdot> V1) \<otimes> (U2 \<cdot> V2)"
  for V1 :: "('a1,'b1) l2bounded" and U1 :: "('b1,'c1) l2bounded"
    and V2 :: "('a2,'b2) l2bounded" and U2 :: "('b2,'c2) l2bounded"
  by (cheat TODO3)

consts remove_qvar_unit_op :: "('a*unit,'a) l2bounded"


definition addState :: "'a ell2 \<Rightarrow> ('b,'b*'a) l2bounded" where
  "addState \<psi> = idOp \<otimes> (ell2_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*"

lemma addState_times_scalar[simp]: "addState (a *\<^sub>C \<psi>) = a *\<^sub>C addState \<psi>" for a::complex and psi::"'a ell2"
  unfolding addState_def by (simp add: ell2_to_bounded_scalar_times)

lemma tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)"
  for U :: "('a,'b) l2bounded" and V :: "('c,'d) l2bounded"
  by (cheat TODO3)

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

subsection \<open>Dual\<close>

(* The interpretation of Riesz representation theorem as an anti-isomorphism
between a Hilbert space and its dual of a Hilbert space is the justification of 
the brac-ket notation *)

(* TODO: the things related to topological_real_vector should be in earlier theory *)

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>continuous_on\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>)\<close>

class topological_real_vector = real_vector + topological_ab_group_add +
  assumes scaleR_continuous: "continuous_on UNIV (case_prod scaleR)"

class topological_complex_vector = complex_vector + topological_ab_group_add +
  assumes scaleC_continuous: "continuous_on UNIV (case_prod scaleC)"

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>continuous_on\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> ('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> bool\<close>)\<close>

thm tendsto_scaleR
  (* This overwrites Limits.tendsto_scaleR by a stronger fact *)
lemma tendsto_scaleR[tendsto_intros]:
  fixes b :: "'a::topological_real_vector"
  assumes "(f \<longlongrightarrow> a) F" and "(g \<longlongrightarrow> b) F"
  shows "((\<lambda>x. f x *\<^sub>R g x) \<longlongrightarrow> a *\<^sub>R b) F"
proof -
  have "(((\<lambda>x. case_prod scaleR (f x, g x))) \<longlongrightarrow> case_prod scaleR (a, b)) F"
    apply (rule tendsto_compose[where g="case_prod scaleR"])
    using continuous_on_def scaleR_continuous apply blast
    by (simp add: assms(1) assms(2) tendsto_Pair)
  then show ?thesis
    by (simp add: case_prod_beta o_def)
qed

(* This overwrites Limits.tendsto_scaleR by a stronger fact *)
lemma tendsto_scaleC[tendsto_intros]:
  fixes b :: "'a::topological_complex_vector"
  assumes "(f \<longlongrightarrow> a) F" and "(g \<longlongrightarrow> b) F"
  shows "((\<lambda>x. f x *\<^sub>C g x) \<longlongrightarrow> a *\<^sub>C b) F"
proof -
  have "(((\<lambda>x. case_prod scaleC (f x, g x))) \<longlongrightarrow> case_prod scaleC (a, b)) F"
    apply (rule tendsto_compose[where g="case_prod scaleC"])
    using continuous_on_def scaleC_continuous apply blast
    by (simp add: assms(1) assms(2) tendsto_Pair)
  then show ?thesis
    by (simp add: case_prod_beta o_def)
qed

(* lemma continuous_on_scaleC[continuous_intros]:
  fixes g :: "_\<Rightarrow>'a::topological_complex_vector"
  assumes "continuous_on s f" and "continuous_on s g"
  shows "continuous_on s (\<lambda>x. f x *\<^sub>C g x)" 
  using assms unfolding continuous_on_def by (auto intro!: tendsto_intros) *)

instance topological_complex_vector \<subseteq> topological_real_vector
  apply standard
  apply (rewrite at "case_prod scaleR" DEADID.rel_mono_strong[of _ "\<lambda>x. (complex_of_real (fst x)) *\<^sub>C (snd x)"])
  apply (auto simp: scaleR_scaleC case_prod_beta)[1]
  unfolding continuous_on_def
  apply (auto intro!: tendsto_intros)
  using tendsto_fst tendsto_snd by fastforce+

instance real_normed_vector \<subseteq> topological_real_vector
proof standard 
  have "(\<lambda>(x, y). x *\<^sub>R y) \<midarrow>(a, b)\<rightarrow> a *\<^sub>R b" for a and b :: 'a
    unfolding case_prod_beta apply (rule Limits.tendsto_scaleR)
    using tendsto_fst tendsto_snd by fastforce+
  then show "continuous_on UNIV (\<lambda>(x, y::'a). x *\<^sub>R y)"
    unfolding continuous_on_def by simp
qed

instance complex_normed_vector \<subseteq> topological_complex_vector
proof standard 
  note tendsto_scaleC = bounded_bilinear.tendsto[OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]
  have "(\<lambda>(x, y). x *\<^sub>C y) \<midarrow>(a, b)\<rightarrow> a *\<^sub>C b" for a and b :: 'a
    unfolding case_prod_beta apply (rule tendsto_scaleC)
    using tendsto_fst tendsto_snd by fastforce+
  then show "continuous_on UNIV (\<lambda>(x, y::'a). x *\<^sub>C y)"
    unfolding continuous_on_def by simp
qed

lemma clinear_0[simp]: "clinear (\<lambda>f. 0)"
  unfolding clinear_def Modules.additive_def clinear_axioms_def by simp

typedef (overloaded) 'a dual = \<open>{f::'a::topological_complex_vector\<Rightarrow>complex. continuous_on UNIV f \<and> clinear f}\<close>
  apply (rule exI[where x="\<lambda>f. 0"]) by auto

instantiation dual :: (complex_normed_vector) chilbert_space begin
instance 
  by (cheat "dual :: (complex_normed_vector) chilbert_space")
end

subsection \<open>Dimension\<close>


lift_definition finite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> is
  \<open>\<lambda>S. \<exists>G. finite G \<and> complex_vector.span G = S\<close> .

(* lift_definition infinite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> is
\<open>\<lambda>S. (
\<exists> f::nat \<Rightarrow> 'a set.
(\<forall>n. is_subspace (f n)) \<and>
(\<forall> n. f n \<subset> f (Suc n)) \<and>
(\<forall> n. f n \<subseteq> S)
)\<close> *)


(* (* TODO: define on sets first and lift? *)
(* TODO: I would define only finite_dim and just negate it for infinite_dim (avoid too many definitions) *)
definition infinite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> where
\<open>infinite_dim S = (
\<exists> f::nat \<Rightarrow> 'a linear_space.
(\<forall> n::nat. Rep_linear_space (f n) \<subset> Rep_linear_space (f (Suc n))) \<and>
(\<forall> n::nat. Rep_linear_space (f n) \<subseteq> Rep_linear_space S)
)\<close> *)

(* definition finite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> where
\<open>finite_dim S = ( \<not> (infinite_dim S) )\<close> *)


subsection \<open>Tensor product\<close>

(* TODO: define Tensor later as "('a dual, 'b) hilbert_schmidt" *)

(* (* Tensor product *)
typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) tensor
(* TODO: is that compatible (isomorphic) with tensorVec? *)
= \<open>{ A :: ('a dual, 'b) bounded. finite_dim (Abs_linear_space ((Rep_bounded A) ` UNIV)) }\<close>
   *)

(* TODO: universal property of tensor products *)

(* Embedding of (x,y) into the tensor product as x\<otimes>y *)
(* TODO: Shouldn't this be called "tensor" or similar then? *)
(* definition HS_embedding :: \<open>('a::chilbert_space)*('b::chilbert_space) \<Rightarrow> ('a, 'b) tensor\<close> where
\<open>HS_embedding x = Abs_tensor ( Abs_bounded (\<lambda> w::'a dual. ( (Rep_bounded w) (fst x) ) *\<^sub>C (snd x) ) )\<close> *)

(* The tensor product of two Hilbert spaces is a Hilbert space *)
(* instantiation tensor :: (chilbert_space,chilbert_space) "chilbert_space" begin
instance 
end *)



end

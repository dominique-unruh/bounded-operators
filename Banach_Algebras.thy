(*  Title:      Bounded-Operators/Banach_Algebras.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu
*)

theory Banach_Algebras
  imports Complex_Vector_Spaces "HOL-Library.Adhoc_Overloading" Extended_Sorry
begin

class cbanach_algebra = cbanach + monoid_mult +
(* TODO remove those fixes and remove axioms that are already in monoid_mult.
Possibly add some typeclass about ring or similar? *)
  fixes banach_mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<degree>" 70)
    and unit :: 'a ("\<one>")
  assumes
    BAlg1: \<open>norm (x \<degree> y) \<le> norm x * norm y\<close> and
    BAlg2: \<open>((x + y) \<degree> z) = (x \<degree> z) + (y \<degree> z)\<close> and
    BAlg3: \<open>((c *\<^sub>C x) \<degree> y) = c *\<^sub>C (x \<degree> y)\<close> and
    BAlg4: \<open>(z \<degree> (x + y)) = (z \<degree> x) + (z \<degree> x)\<close> and
    BAlg5: \<open>(x \<degree> (c *\<^sub>C y)) = c *\<^sub>C (x \<degree> y)\<close> and
    BAlg6: \<open>(x \<degree> (y \<degree> z)) = ((x \<degree> y) \<degree> z)\<close> and
    BAlg7: \<open>(\<one> \<degree> x) = x\<close>  and
    BAlg8: \<open>(x \<degree> \<one>) = x\<close>  and
    BAlg9: \<open>norm \<one> \<le> 1\<close> 

begin

lemma zero_left: \<open>(0\<degree>y) = 0\<close>
  by (metis local.BAlg2 local.add_cancel_right_right)

lemma zero_right: \<open>(x\<degree>0) = 0\<close>
  by (metis local.BAlg4 local.add_cancel_right_right)

lemma isCont_mult_left: \<open>isCont (\<lambda> x. (x\<degree>y)) t\<close>
proof(cases \<open>y = 0\<close>)
  case True
  moreover have \<open>isCont (\<lambda> x. 0) t\<close>
    by simp
  ultimately show ?thesis using zero_right 
    by (simp add: cbanach_algebra_class.zero_right) 
next
  include notation_norm
  case False
  hence \<open>y \<noteq> 0\<close> by auto
  have  \<open>\<parallel> y \<parallel> > 0\<close>
    (* find_theorems "norm _ = 0 \<longleftrightarrow> _ = 0" *)
    (* using cbanach_class.norm_zero *)
    (* by (sxxxmt False ab_group_add_class.ab_diff_conv_add_uminus cancel_semigroup_add_class.add_left_cancel cbanach_algebra_class.BAlg4 cbanach_algebra_class.BAlg7 group_add_class.right_minus_eq) *)
    by (cheat fixme)
  have \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> \<delta> > 0. \<forall> s. dist s t < \<delta> \<longrightarrow> dist ((\<lambda> x. (x\<degree>y)) s) ((\<lambda> x. (x\<degree>y)) t) < \<epsilon>\<close> for \<epsilon>
  proof-
    assume \<open>\<epsilon> > 0\<close>
    obtain \<delta> where \<open>\<delta> = \<epsilon> / (\<parallel>y\<parallel>)\<close> by blast
    have  \<open>\<delta> > 0\<close> 
      (* by (simp add: \<open>0 < \<epsilon>\<close> \<open>0 < \<parallel>y\<parallel>\<close> \<open>\<delta> = \<epsilon> / \<parallel>y\<parallel>\<close>) *)
      by (cheat fixme)
    have \<open>dist s t < \<delta> \<Longrightarrow> dist ((\<lambda> x. (x\<degree>y)) s) ((\<lambda> x. (x\<degree>y)) t) < \<epsilon>\<close> for s
    proof-
      assume \<open>dist s t < \<delta>\<close>
      hence \<open>\<parallel> s - t \<parallel> < \<delta>\<close> 
        (* by (simp add: cbanach_space_class.dist_norm) *)
        by (cheat fixme)
      have \<open> dist ((\<lambda> x. (x\<degree>y)) s) ((\<lambda> x. (x\<degree>y)) t) =  \<parallel> ((\<lambda> x. (x\<degree>y)) s) - ((\<lambda> x. (x\<degree>y)) t) \<parallel>\<close>
        (* by (simp add: cbanach_space_class.dist_norm) *)
        by (cheat fixme)
      hence \<open> ... =  \<parallel> (s\<degree>y) - (t\<degree>y) \<parallel>\<close>
        by simp
      hence \<open> ... =  \<parallel> (s - t) \<degree> y \<parallel>\<close>
        by (metis (mono_tags, lifting) cbanach_algebra_class.BAlg2 group_add_class.add_diff_cancel group_add_class.diff_minus_eq_add)
      hence \<open> ... \<le>  \<parallel> s - t \<parallel> * \<parallel> y \<parallel>\<close>
        using cbanach_algebra_class.BAlg1 by auto
      hence \<open> ... <  \<delta> * \<parallel> y \<parallel>\<close>
        using  \<open>\<parallel> s - t \<parallel> < \<delta>\<close> 
          by (cheat fixme)
        (* by (simp add: \<open>0 < \<parallel>y\<parallel>\<close>) *)
      also have \<open> ... <  (\<epsilon> / (\<parallel>y\<parallel>)) * \<parallel> y \<parallel>\<close>
        using  \<open>\<delta> = \<epsilon> / (\<parallel>y\<parallel>)\<close> \<open>\<delta> > 0\<close>     
        by (smt False cbanach_algebra_class.BAlg4 cbanach_algebra_class.BAlg6 cbanach_algebra_class.BAlg7 cbanach_algebra_class.BAlg8 cbanach_algebra_class.zero_right monoid_add_class.add.right_neutral monoid_add_class.add_0_left)
      also have \<open> ... <  \<epsilon> * (\<parallel> y \<parallel> / \<parallel> y \<parallel>)\<close>
        using \<open>\<delta> * \<parallel>y\<parallel> < \<epsilon> / \<parallel>y\<parallel> * \<parallel>y\<parallel>\<close> \<open>\<delta> = \<epsilon> / \<parallel>y\<parallel>\<close> by auto
      finally have \<open> ... <  \<epsilon>\<close>
        using  \<open>\<epsilon> > 0\<close>  \<open>\<parallel> y \<parallel> > 0\<close> 
        using \<open>\<delta> * \<parallel>y\<parallel> < \<epsilon> / \<parallel>y\<parallel> * \<parallel>y\<parallel>\<close> \<open>\<delta> = \<epsilon> / \<parallel>y\<parallel>\<close> by blast
      thus ?thesis 
        using \<open>\<delta> * \<parallel>y\<parallel> < \<epsilon> / \<parallel>y\<parallel> * \<parallel>y\<parallel>\<close> \<open>\<delta> = \<epsilon> / \<parallel>y\<parallel>\<close> by blast
    qed
    hence \<open>\<forall> s. dist s t < \<delta> \<longrightarrow> dist ((\<lambda> x. (x\<degree>y)) s) ((\<lambda> x. (x\<degree>y)) t) < \<epsilon>\<close>
      by simp
    show ?thesis 
      by (smt False cbanach_algebra_class.BAlg4 cbanach_algebra_class.BAlg6 cbanach_algebra_class.BAlg7 cbanach_algebra_class.BAlg8 cbanach_algebra_class.zero_right monoid_add_class.add.right_neutral monoid_add_class.add_0_left)
  qed
  hence \<open>\<forall> \<epsilon> > 0. \<exists> \<delta> > 0. \<forall> s. dist s t < \<delta> \<longrightarrow> dist ((\<lambda> x. (x\<degree>y)) s) ((\<lambda> x. (x\<degree>y)) t) < \<epsilon>\<close>
    by blast
  thus ?thesis 
    by (cheat fixme)
  (* by (simp add: continuous_at_eps_delta)   *)
qed


lemma isCont_mult_right: \<open>isCont (\<lambda> x. (y\<degree>x)) t\<close>
proof(cases \<open>y = 0\<close>)
  case True
  moreover have \<open>isCont (\<lambda> x. 0) t\<close>
    by simp
  ultimately show ?thesis using zero_right 
    by (simp add: cbanach_algebra_class.zero_left) 
next
  include notation_norm
  case False
  hence \<open>y \<noteq> 0\<close> by auto
  have  \<open>\<parallel> y \<parallel> > 0\<close>
    by (cheat fixme)
  (* using cbanach_space_class.norm_zero *)
    (* by (smxt False ab_group_add_class.ab_diff_conv_add_uminus cancel_semigroup_add_class.add_left_cancel cbanach_algebra_class.BAlg4 cbanach_algebra_class.BAlg7 group_add_class.right_minus_eq) *)
  have \<open>\<epsilon> > 0 \<Longrightarrow> \<exists> \<delta> > 0. \<forall> s. dist s t < \<delta> \<longrightarrow> dist ((\<lambda> x. (y\<degree>x)) s) ((\<lambda> x. (y\<degree>x)) t) < \<epsilon>\<close> for \<epsilon>
  proof-
    assume \<open>\<epsilon> > 0\<close>
    obtain \<delta> where \<open>\<delta> = \<epsilon> / (\<parallel>y\<parallel>)\<close> by blast
    have  \<open>\<delta> > 0\<close> 
      by (cheat fixme)
    (* by (simp add: \<open>0 < \<epsilon>\<close> \<open>0 < \<parallel>y\<parallel>\<close> \<open>\<delta> = \<epsilon> / \<parallel>y\<parallel>\<close>) *)
    have \<open>dist s t < \<delta> \<Longrightarrow> dist ((\<lambda> x. (x\<degree>y)) s) ((\<lambda> x. (x\<degree>y)) t) < \<epsilon>\<close> for s
    proof-
      assume \<open>dist s t < \<delta>\<close>
      hence \<open>\<parallel> s - t \<parallel> < \<delta>\<close> 
        by (cheat fixme)
      (* by (simp add: cbanach_space_class.dist_norm) *)
      have \<open> dist ((\<lambda> x. (y\<degree>x)) s) ((\<lambda> x. (y\<degree>x)) t) =  \<parallel> ((\<lambda> x. (y\<degree>x)) s) - ((\<lambda> x. (y\<degree>x)) t) \<parallel>\<close>
        by (cheat fixme)
      (* by (simp add: cbanach_space_class.dist_norm) *)
      hence \<open> ... =  \<parallel> (y\<degree>s) - (y\<degree>t) \<parallel>\<close>
        by simp
      hence \<open> ... =  \<parallel> y \<degree> (s - t) \<parallel>\<close>
        using  cbanach_algebra_class.BAlg4
        by (smt cancel_comm_monoid_add_class.diff_cancel cancel_comm_monoid_add_class.diff_zero group_add_class.diff_add_cancel group_add_class.diff_diff_eq2)

      hence \<open> ... \<le>   \<parallel> y \<parallel> * \<parallel> s - t \<parallel>\<close>
        using cbanach_algebra_class.BAlg1 by auto
      hence \<open> ... <  \<delta> * \<parallel> y \<parallel>\<close>
        using  \<open>\<parallel> s - t \<parallel> < \<delta>\<close> 
          by (cheat fixme)
        (* by (simp add: \<open>0 < \<parallel>y\<parallel>\<close>) *)
      also have \<open> ... <  (\<epsilon> / (\<parallel>y\<parallel>)) * \<parallel> y \<parallel>\<close>
        using  \<open>\<delta> = \<epsilon> / (\<parallel>y\<parallel>)\<close> \<open>\<delta> > 0\<close>     
        by (smt False cbanach_algebra_class.BAlg4 cbanach_algebra_class.BAlg6 cbanach_algebra_class.BAlg7 cbanach_algebra_class.BAlg8 cbanach_algebra_class.zero_right monoid_add_class.add.right_neutral monoid_add_class.add_0_left)
      also have \<open> ... <  \<epsilon> * (\<parallel> y \<parallel> / \<parallel> y \<parallel>)\<close>
        using \<open>\<delta> * \<parallel>y\<parallel> < \<epsilon> / \<parallel>y\<parallel> * \<parallel>y\<parallel>\<close> \<open>\<delta> = \<epsilon> / \<parallel>y\<parallel>\<close> by auto
      finally have \<open> ... <  \<epsilon>\<close>
        using  \<open>\<epsilon> > 0\<close>  \<open>\<parallel> y \<parallel> > 0\<close> 
        using \<open>\<delta> * \<parallel>y\<parallel> < \<epsilon> / \<parallel>y\<parallel> * \<parallel>y\<parallel>\<close> \<open>\<delta> = \<epsilon> / \<parallel>y\<parallel>\<close> by blast
      thus ?thesis 
        using \<open>\<delta> * \<parallel>y\<parallel> < \<epsilon> / \<parallel>y\<parallel> * \<parallel>y\<parallel>\<close> \<open>\<delta> = \<epsilon> / \<parallel>y\<parallel>\<close> by blast
    qed
    hence \<open>\<forall> s. dist s t < \<delta> \<longrightarrow> dist ((\<lambda> x. (x\<degree>y)) s) ((\<lambda> x. (x\<degree>y)) t) < \<epsilon>\<close>
      by simp
    show ?thesis 
      by (cheat fixme)
    (* by (sxmt False cbanach_algebra_class.BAlg4 cbanach_algebra_class.BAlg6 cbanach_algebra_class.BAlg7 cbanach_algebra_class.BAlg8 cbanach_algebra_class.zero_right monoid_add_class.add.right_neutral monoid_add_class.add_0_left) *)
  qed
  hence \<open>\<forall> \<epsilon> > 0. \<exists> \<delta> > 0. \<forall> s. dist s t < \<delta> \<longrightarrow> dist ((\<lambda> x. (y\<degree>x)) s) ((\<lambda> x. (y\<degree>x)) t) < \<epsilon>\<close>
    by blast
  thus ?thesis 
    by (cheat fixme)
  (* by (simp add: continuous_at_eps_delta)   *)
qed

end


end
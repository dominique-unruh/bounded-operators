section \<open>Uniform_limit_Missing\<close>

(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Complement to the library "HOL-Analysis.Uniform_Limit"

Main results:

- nsuniform_convergence_iff: Equivalence between  \<open>S: f \<midarrow>uniformly\<rightarrow> l\<close> and its nonstandard
 equivalent.

- nsupointwise_convergence_unique: Uniqueness of the limit of a sequence of linear operators 
(the limit may not be unique in general if we ignore linearity).

*)

theory Uniform_Limit_Missing
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL.Real_Vector_Spaces"
    "HOL-Analysis.Operator_Norm"
    "HOL-Analysis.Uniform_Limit"
    Unobtrusive_NSA
begin

unbundle nsa_notation

abbreviation uniform_convergence_abbr::
  \<open>'a set \<Rightarrow> (nat \<Rightarrow> ('a \<Rightarrow>'b::metric_space)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  (\<open>(_): ((_)/ \<midarrow>uniformly\<rightarrow> (_))\<close> [60, 60, 60] 60)
  where \<open>S: f \<midarrow>uniformly\<rightarrow> l \<equiv> (  uniform_limit S f l sequentially )\<close>

subsection \<open>Nonstandard analog of uniform convergence\<close>

lemma nsuniform_convergence_D:
  fixes l::\<open>'a \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
    and S :: \<open>'a set\<close> and N::hypnat and x::\<open>'a star\<close>
  assumes \<open>S: f \<midarrow>uniformly\<rightarrow> l\<close> and \<open>N\<in>HNatInfinite\<close> and \<open>x\<in>*s* S\<close>
  shows \<open>(*f2* f) N x \<approx> (*f* l) x\<close>
proof-
  have \<open>(*f2* f) N x - (*f* l) x \<in> Infinitesimal\<close>
  proof (rule InfinitesimalI2)
    fix r :: real
    assume \<open>0 < r\<close>
    have \<open>\<exists> no. \<forall> n \<ge> no. \<forall> x\<in>S. norm (f n x - l x) < r\<close>
      using \<open>S: f \<midarrow>uniformly\<rightarrow> l\<close> \<open>0 < r\<close>
        dist_norm uniform_limit_sequentially_iff by metis
    then obtain no where \<open>\<forall> n \<ge> no. \<forall> x\<in>S. norm (f n x - l x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> no. \<forall> x\<in>S. norm ( f n x - l x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> hypnat_of_nat no. \<forall> x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x) < hypreal_of_real r\<close>
      by StarDef.transfer
    thus \<open>hnorm ((*f2* f) N x- (*f* l) x) < hypreal_of_real r\<close>
      using star_of_le_HNatInfinite \<open>N \<in> HNatInfinite\<close>
      by (simp add: \<open>x\<in>*s* S\<close>)
  qed
  thus \<open>(*f2* f) N x \<approx> (*f* l) x\<close>
    by (simp only: approx_def)
qed

lemma nsuniform_convergence_I:
  fixes l::\<open>'a \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
    and S :: \<open>'a set\<close>
  assumes \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x\<close>
  shows \<open>S: f \<midarrow>uniformly\<rightarrow> l\<close>
proof-
  have \<open>r > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>S. norm (f n x - l x) < r\<close>
    for r::real
  proof-
    assume \<open>r > 0\<close>
    from \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x\<close>
    have \<open>\<forall>n\<in>HNatInfinite.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
      by (simp add: InfinitesimalD2 Infinitesimal_approx_minus \<open>r > 0\<close>)
    have \<open>\<exists> no. \<forall>n \<ge> no.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
    proof-
      have \<open>n \<ge> whn \<Longrightarrow>
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
        for n
        using HNatInfinite_upward_closed HNatInfinite_whn
          \<open>\<forall>n\<in>HNatInfinite. \<forall>x\<in>*s* S. hnorm ((*f2* f) n x - (*f* l) x) < hypreal_of_real r\<close> 
        by blast     
      thus ?thesis by blast
    qed
    thus \<open>\<exists> no. \<forall>n \<ge> no. \<forall>x\<in>S. norm ( f n x - l x ) < r\<close>
      by StarDef.transfer
  qed
  thus ?thesis
    using dist_norm uniform_limit_sequentially_iff by metis
qed

proposition nsuniform_convergence_iff:
  fixes l::\<open>'a\<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
    and S :: \<open>'a set\<close>
  shows \<open>(S: f \<midarrow>uniformly\<rightarrow> l)\<longleftrightarrow>(\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x)\<close>
proof
  show "\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x"
    if "S: f \<midarrow>uniformly\<rightarrow> l"
    using that
    using nsuniform_convergence_D by blast 
  show "S: f \<midarrow>uniformly\<rightarrow> l"
    if "\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x"
    using that
    by (simp add: nsuniform_convergence_I) 
qed


lemma nsuniformly_Cauchy_on_D:
  fixes f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector)\<close> and S::\<open>'a set\<close> 
    and N::hypnat and x::\<open>'a star\<close>
  assumes  \<open>uniformly_Cauchy_on S f\<close> and \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close> and \<open>x\<in>*s* S\<close>
  shows \<open>(*f2* f) N x \<approx> (*f2* f) M x\<close>
proof-
  have \<open>(*f2* f) N x - (*f2* f) M x \<in> Infinitesimal\<close>
  proof (rule InfinitesimalI2)
    fix r :: real
    assume \<open>0 < r\<close>
    have \<open>\<exists> no. \<forall> n \<ge> no. \<forall> m \<ge> no. \<forall> x\<in>S. norm (f n x - f m x) < r\<close>
      using \<open>uniformly_Cauchy_on S f\<close> \<open>0 < r\<close>
      using dist_norm
      unfolding uniformly_Cauchy_on_def
      by metis
    then obtain no where \<open>\<forall> n \<ge> no. \<forall> m \<ge> no. \<forall> x\<in>S. norm (f n x - f m x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> no. \<forall> m \<ge> no. \<forall> x\<in>S. norm (f n x - f m x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> hypnat_of_nat no. \<forall> m \<ge> hypnat_of_nat no. 
      \<forall> x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x) < hypreal_of_real r\<close>
      by StarDef.transfer
    thus \<open>hnorm ((*f2* f) N x- (*f2* f) M x) < hypreal_of_real r\<close>
      using star_of_le_HNatInfinite \<open>N \<in> HNatInfinite\<close> \<open>M \<in> HNatInfinite\<close>
      by (simp add: \<open>x\<in>*s* S\<close>)
  qed
  thus \<open>(*f2* f) N x \<approx> (*f2* f) M x\<close>
    by (simp only: approx_def)
qed

lemma nsuniformly_Cauchy_on_I:
  fixes  f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector)\<close> and S::\<open>'a set\<close>
  assumes \<open>\<forall>N\<in>HNatInfinite. \<forall> M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x\<close>
  shows \<open>uniformly_Cauchy_on S f\<close>
proof-
  have \<open>r > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<forall> m\<ge>N. \<forall>x\<in>S. norm (f n x - f m x) < r\<close>
    for r::real
  proof-
    assume \<open>r > 0\<close>
    from \<open>\<forall>N\<in>HNatInfinite. \<forall> M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x\<close>
    have \<open>\<forall>n\<in>HNatInfinite. \<forall> m\<in>HNatInfinite.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x ) < hypreal_of_real r\<close>
      by (simp add: InfinitesimalD2 Infinitesimal_approx_minus \<open>r > 0\<close>)
    have \<open>\<exists> no. \<forall>n \<ge> no. \<forall> m \<ge> no.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x ) < hypreal_of_real r\<close>
    proof-
      have \<open>n \<ge> whn \<Longrightarrow> m \<ge> whn \<Longrightarrow>
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x ) < hypreal_of_real r\<close>
        for n m
        using HNatInfinite_upward_closed HNatInfinite_whn
          \<open>\<forall>n\<in>HNatInfinite. \<forall> m\<in>HNatInfinite. \<forall>x\<in>*s* S. hnorm ((*f2* f) n x - (*f2* f) m x) < hypreal_of_real r\<close> 
        by blast     
      thus ?thesis by blast
    qed
    thus \<open>\<exists> no. \<forall>n \<ge> no. \<forall> m \<ge> no. \<forall>x\<in>S. norm ( f n x - f m x ) < r\<close>
      by StarDef.transfer
  qed
  thus ?thesis
    using  dist_norm
    unfolding uniformly_Cauchy_on_def
    by metis
qed


proposition nsuniformly_Cauchy_on_iff:
  fixes  f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector)\<close> and S::\<open>'a set\<close>
  shows \<open>(uniformly_Cauchy_on S f) \<longleftrightarrow> 
    (\<forall>N\<in>HNatInfinite. \<forall> M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x)\<close>
proof
  show "\<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x"
    if "uniformly_Cauchy_on S f"
    using that
    using nsuniformly_Cauchy_on_D by blast 
  show "uniformly_Cauchy_on S f"
    if "\<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x"
    using that
    using nsuniformly_Cauchy_on_I by metis 
qed

subsection \<open>Nonstandard analog of uniform convergence on the unit (sphere 0 1) \<close>

lemma sphere_iff:
  \<open>x\<in>*s*(sphere 0 1) \<longleftrightarrow> hnorm x = 1\<close>
proof-
  have \<open>\<forall> xx.  xx\<in>(sphere 0 1) \<longleftrightarrow> norm xx = 1\<close>
    by simp
  hence \<open>\<forall> xx.  xx\<in>*s*(sphere 0 1) \<longleftrightarrow> hnorm xx = 1\<close>
    by StarDef.transfer
  thus ?thesis by blast
qed

lemma nsupointwise_convergence_I: 
  \<open>( \<And>N. \<And> x. N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x  \<approx> (*f* l) x )
   \<Longrightarrow> (sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close> 
proof-
  assume \<open>\<And>N x. N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
  hence \<open>\<forall>N\<in>HNatInfinite. \<forall>x. hnorm x = 1 \<longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
    by blast                
  hence \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s*(sphere 0 1).  (*f2* f) N x \<approx> (*f* l) x\<close>
    using sphere_iff by auto
  hence \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close>
    by (simp add: nsuniform_convergence_I)
  thus \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close>
    by blast
qed

lemma nsupointwise_convergence_D:
  \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l \<Longrightarrow> N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 
  \<Longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
proof-
  assume \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  have \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s*(sphere 0 1). (*f2* f) N x \<approx> (*f* l) x\<close>
    using nsuniform_convergence_D \<open>sphere 0 1: f \<midarrow>uniformly\<rightarrow> l\<close> by blast                     
  thus \<open>(*f2* f) N x \<approx> (*f* l) x\<close>
    by (simp add: \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> sphere_iff)
qed

lemma bounded_linear_HFinite:
  \<open>bounded_linear a \<Longrightarrow> hnorm x = 1 \<Longrightarrow> ((*f* a) x) \<in> HFinite\<close>
proof-
  {
    assume \<open>bounded_linear a\<close> and \<open>hnorm x = 1\<close>
    have \<open>\<And> t. norm t = 1 \<Longrightarrow> norm (a t) \<le> onorm a\<close>
      using \<open>bounded_linear a\<close> by (metis mult_cancel_left2 onorm)      
    hence  \<open>\<And> t. norm t = 1 \<Longrightarrow> norm (a t) < onorm a + 1\<close>
      by fastforce      
    hence  \<open>\<And> t. hnorm t = 1 \<Longrightarrow> hnorm ((*f* a) t) < star_of (onorm a + 1)\<close>
      by StarDef.transfer
    hence  \<open>hnorm ((*f* a) x) < star_of (onorm a + 1)\<close>
      using \<open>hnorm x = 1\<close>
      by auto
    hence \<open>\<exists>xa\<in>\<real>. hnorm ((*f* a) x) < xa\<close> by auto
  } note 1 = this
  assume \<open>bounded_linear a\<close> and \<open>hnorm x = 1\<close>
  thus ?thesis
    unfolding HFinite_def
    apply auto
    apply (rule 1)
    by auto
qed

lemma nsupointwise_convergence_mult: 
  fixes a b :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
  assumes \<open>sphere 0 1: X \<midarrow>uniformly\<rightarrow> a\<close> and \<open>sphere 0 1: Y \<midarrow>uniformly\<rightarrow> b\<close>
    and \<open>bounded_linear a\<close> and \<open>bounded_linear b\<close>
  shows \<open>sphere 0 1: (\<lambda>n. (\<lambda> t. X n t * Y n t)) \<midarrow>uniformly\<rightarrow> (\<lambda> t. a t * b t)\<close>
proof(rule nsupointwise_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using  \<open>sphere 0 1: X \<midarrow>uniformly\<rightarrow> a\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsupointwise_convergence_D by blast 
  moreover have \<open>(*f2* Y) N x \<approx> (*f* b) x\<close>
    using \<open>sphere 0 1: Y \<midarrow>uniformly\<rightarrow> b\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsupointwise_convergence_D by blast 
  moreover have \<open>((*f* a) x) \<in> HFinite\<close>
    using \<open>bounded_linear a\<close> \<open>hnorm x = 1\<close>
    by (simp add: bounded_linear_HFinite) 
  moreover have \<open>((*f* b) x) \<in> HFinite\<close>
    using \<open>bounded_linear b\<close> \<open>hnorm x = 1\<close>
    by (simp add: bounded_linear_HFinite)
  ultimately have \<open>(*f2* X) N x * (*f2* Y) N x \<approx> (*f* a) x * (*f* b) x\<close>
    using approx_mult_HFinite by auto
  moreover have \<open>(*f2* X) N x * (*f2* Y) N x = (*f2* (\<lambda>n t. X n t * Y n t)) N x\<close>
  proof-
    have \<open>\<forall> NN. \<forall> xx. X NN xx * Y NN xx = (\<lambda>n t. X n t * Y n t) NN xx\<close>
      by auto
    hence \<open>\<forall> NN. \<forall> xx. (*f2* X) NN xx * (*f2* Y) NN xx = (*f2* (\<lambda>n t. X n t * Y n t)) NN xx\<close>
      apply StarDef.transfer
      by auto
    thus ?thesis
      by simp  
  qed
  moreover have \<open>(*f* a) x * (*f* b) x = (*f* (\<lambda>t. a t * b t)) x\<close>
    by simp
  ultimately show \<open>(*f2* (\<lambda>n t. X n t * Y n t)) N x \<approx> (*f* (\<lambda>t. a t * b t)) x\<close>
    by metis
qed


(* TODO: move to real_normed_vector *)
(* Ask to Dominique: where is "real_normed_vector", it is a type, not a file. *)
lemma linear_ball_zero:
  \<open>linear f \<Longrightarrow>  \<forall> x. norm x = 1 \<longrightarrow> f x = 0 \<Longrightarrow> f = (\<lambda> _. 0)\<close>
proof
  show "f u = 0"
    if "linear f"
      and "\<forall>x. norm x = 1 \<longrightarrow> f x = 0"
    for u :: 'a
  proof(cases \<open>u = 0\<close>)
    case True
    thus ?thesis
      by (simp add: linear_0 that(1))
  next
    case False
    have \<open>norm ( (inverse (norm u)) *\<^sub>R u ) = 1\<close>
      by (simp add: False)
    hence \<open>f ( (inverse (norm u)) *\<^sub>R u ) = 0\<close>
      by (simp add: that(2))
    moreover have \<open>f ( (inverse (norm u)) *\<^sub>R u ) = (inverse (norm u)) *\<^sub>R (f  u)\<close>
      using \<open>linear f\<close> unfolding linear_def
      by (simp add: Real_Vector_Spaces.linear_def linear_scale) 
    ultimately have \<open>(inverse (norm u)) *\<^sub>R (f  u) = 0\<close>
      by simp
    moreover have \<open>(inverse (norm u)) \<noteq> 0\<close>
      using \<open>norm (u /\<^sub>R norm u) = 1\<close> by auto
    ultimately show ?thesis by simp
  qed
qed

(* TODO: move to real_normed_vector? *)
lemma linear_ball_uniq:
  \<open>linear f \<Longrightarrow> linear g \<Longrightarrow> \<forall> x. norm x = 1 \<longrightarrow> f x = g x \<Longrightarrow> f = g\<close>
proof
  show "f x = g x"
    if "linear f"
      and "linear g"
      and "\<forall>x. norm x = 1 \<longrightarrow> f x = g x"
    for x :: 'a
  proof-
    have "\<forall>x. norm x = 1 \<longrightarrow> (\<lambda> t. f t - g t) x = 0"
      by (simp add: that(3))
    moreover have \<open>linear (\<lambda> t. f t - g t)\<close>
      using \<open>linear f\<close> \<open>linear g\<close>
      by (simp add: linear_compose_sub) 
    ultimately have \<open>(\<lambda> t. f t - g t) = (\<lambda> _. 0)\<close>
      using linear_ball_zero by fastforce
    thus ?thesis
      by (meson eq_iff_diff_eq_0) 
  qed
qed

lemma nsupointwise_convergence_unique: 
  fixes a b :: \<open>'a::real_normed_vector\<Rightarrow>'b::real_normed_vector\<close>
  assumes \<open>sphere 0 1:X \<midarrow>uniformly\<rightarrow> a\<close> and \<open>sphere 0 1:X \<midarrow>uniformly\<rightarrow> b\<close>
    and \<open>linear a\<close> and \<open>linear b\<close>
  shows \<open>a = b\<close>
proof-
  have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow>(*f2* X) N x \<approx> (*f* a) x\<close>
    using  \<open>sphere 0 1:X \<midarrow>uniformly\<rightarrow> a\<close>
    by (simp add: nsupointwise_convergence_D)
  moreover have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow> (*f2* X) N x \<approx> (*f* b) x\<close>
    using  \<open>sphere 0 1:X \<midarrow>uniformly\<rightarrow> b\<close>
    by (simp add: nsupointwise_convergence_D)
  ultimately have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow> (*f* a) x \<approx> (*f* b) x\<close>
    by (simp add: approx_monad_iff)
  hence \<open>\<forall> x. hnorm x = 1 \<longrightarrow> (*f* a) x \<approx> (*f* b) x\<close>
    by (meson NSLIMSEQ_def NSLIMSEQ_unique zero_neq_one)
  have \<open>norm t = 1 \<Longrightarrow> a t = b t\<close>
    for t
  proof-
    assume \<open>norm t = 1\<close>
    hence \<open>hnorm (star_of t) = 1\<close>
      by (metis star_of_norm star_one_def)
    hence \<open>(*f* a) (star_of t) \<approx> (*f* b) (star_of t)\<close>
      using \<open>\<forall>x. hnorm x = 1 \<longrightarrow> (*f* a) x \<approx> (*f* b) x\<close> by blast
    thus ?thesis
      by simp 
  qed
  thus ?thesis using linear_ball_uniq  \<open>linear a\<close>  \<open>linear b\<close>
    by blast
qed

unbundle no_nsa_notation

end

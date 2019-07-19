(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Uniform convergence.

Main results.
- ustrong_convergence: Definition of the strong convergence on the unit sphere.
- uCauchy: Definition of the Cauchy property on the unit sphere.
- nsuniform_convergence_iff: Equivalent between the standard and nonstandard
version of ustrong_convergence.
- nsuniformly_Cauchy_on_iff: Equivalent between the standard and nonstandard
version of uCauchy.

*)

theory Uniform_Convergence
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL.Real_Vector_Spaces"
    "HOL-Analysis.Operator_Norm"
    "HOL-Analysis.Uniform_Limit"
    Unobtrusive_NSA
begin

chapter \<open>General case\<close>
section \<open>Standard definitions\<close>

abbreviation uniform_convergence_abbr::
  \<open>'a set \<Rightarrow> (nat \<Rightarrow> ('a \<Rightarrow>'b::metric_space)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  (\<open>(_): ((_)/ \<midarrow>uniformly\<rightarrow> (_))\<close> [60, 60, 60] 60)
  where \<open>S: f \<midarrow>uniformly\<rightarrow> l \<equiv> (  uniform_limit S f l sequentially )\<close>

subsection \<open>Nonstandard analog of uniform convergence\<close>

text \<open>We will restrict ourselves to the case of vector spaces for the nonstandard models.\<close>

text \<open>See theorem 7.12.2 of [goldblatt2012lectures]\<close>

lemma uniform_convergence_norm_I:
  fixes l::\<open>'a \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close> and S :: \<open>'a set\<close> 
  assumes \<open>\<forall> e > 0. \<exists> N. \<forall> n \<ge> N. \<forall> x\<in>S. norm (f n x - l x) < e\<close>
  shows \<open>(S: f \<midarrow>uniformly\<rightarrow> l)\<close>
  using assms dist_norm uniform_limit_sequentially_iff by metis
  
lemma uniform_convergence_norm_D:
  fixes l::\<open>'a \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close> and S :: \<open>'a set\<close> 
  assumes  \<open>S: f \<midarrow>uniformly\<rightarrow> l\<close>
  shows \<open>\<forall> e > 0. \<exists> N. \<forall> n \<ge> N. \<forall> x\<in>S. norm (f n x - l x) < e\<close>
  using assms dist_norm uniform_limit_sequentially_iff by metis
  
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
      by (simp add: uniform_convergence_norm_D)      
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
    by (simp add: uniform_convergence_norm_I)
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

subsection \<open>Nonstandard analog of Cauchy property uniformly\<close>

lemma uniformly_Cauchy_on_norm_I:
  fixes f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector)\<close> and S :: \<open>'a set\<close> 
  assumes \<open>\<forall> e > 0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall> x\<in>S. norm (f m x - f n x) < e\<close>
  shows \<open>uniformly_Cauchy_on S f\<close>
  using assms dist_norm 
  unfolding uniformly_Cauchy_on_def
  by metis

lemma uniformly_Cauchy_on_norm_D:
  fixes f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector)\<close> and S::\<open>'a set\<close> 
  assumes \<open>uniformly_Cauchy_on S f\<close>
  shows \<open>\<forall> e > 0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall> x\<in>S. norm (f m x - f n x) < e\<close>
  using assms dist_norm
  unfolding uniformly_Cauchy_on_def
  by metis

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
      by (simp add: uniformly_Cauchy_on_norm_D)      
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
    by (simp add: uniformly_Cauchy_on_norm_I)
qed


proposition nsuniformly_Cauchy_on_iff:
  fixes  f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b::real_normed_vector)\<close> and S::\<open>'a set\<close>
  shows \<open>(uniformly_Cauchy_on S f) \<longleftrightarrow> (\<forall>N\<in>HNatInfinite. \<forall> M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x)\<close>
  proof
  show "\<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x"
    if "uniformly_Cauchy_on S f"
    using that
    using nsuniformly_Cauchy_on_D by blast 
  show "uniformly_Cauchy_on S f"
    if "\<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x"
    using that
    using nsuniformly_Cauchy_on_I by smt 
qed


chapter \<open>Linear case\<close>

section \<open>Standard definitions\<close>

definition sphere:: \<open>'a::real_normed_vector set\<close> where
\<open>sphere = {x. norm x = 1}\<close> (* TODO rename: unit_sphere (to avoid name conflict) *)
(* TODO: same as sphere 0 1 from Elementary_Metric_Spaces *)

definition hsphere :: "('a::real_normed_vector star) set"
  where [transfer_unfold]: "hsphere = *s* sphere"

(* TODO: remove (just write unit_sphere: f \<midarrow>uniformly\<rightarrow> l) *)
definition ustrong_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close> where 
  \<open>ustrong_convergence f l = (sphere: f \<midarrow>uniformly\<rightarrow> l)\<close>

(* TODO remove *)
abbreviation ustrong_convergence_abbr::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>  (\<open>((_)/ \<midarrow>ustrong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>ustrong\<rightarrow> l \<equiv> ( ustrong_convergence f l )\<close>

(* TODO remove *)
definition uCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>uCauchy f = (uniformly_Cauchy_on sphere f)\<close>

section \<open>Nonstandard analogs\<close>

subsection \<open>Nonstandard analog of uniform convergence on the unit sphere \<close>

lemma sphere_iff:
  \<open>x\<in>hsphere \<longleftrightarrow> hnorm x = 1\<close>
proof-
  have \<open>\<forall> xx.  xx\<in>sphere \<longleftrightarrow> norm xx = 1\<close>
    by (simp add: Uniform_Convergence.sphere_def)
  hence \<open>\<forall> xx.  xx\<in>hsphere \<longleftrightarrow> hnorm xx = 1\<close>
    by StarDef.transfer
  thus ?thesis by blast
qed

lemma nsustrong_convergence_I: 
  \<open>( \<And>N. \<And> x. N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x  \<approx> (*f* l) x )
   \<Longrightarrow> f \<midarrow>ustrong\<rightarrow> l\<close> 
proof-
  assume \<open>\<And>N x. N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
  hence \<open>\<forall>N\<in>HNatInfinite. \<forall>x. hnorm x = 1 \<longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
    by blast                
  hence \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>hsphere.  (*f2* f) N x \<approx> (*f* l) x\<close>
    using sphere_iff by auto
  hence \<open>sphere: f \<midarrow>uniformly\<rightarrow> l\<close>
    unfolding hsphere_def
    by (simp add: nsuniform_convergence_I)
  thus \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
    unfolding ustrong_convergence_def by blast
qed

lemma nsustrong_convergence_D:
  \<open>f \<midarrow>ustrong\<rightarrow> l \<Longrightarrow> N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 
  \<Longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
proof-
  assume \<open>f \<midarrow>ustrong\<rightarrow> l\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  from  \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
  have  \<open>sphere: f \<midarrow>uniformly\<rightarrow> l\<close>
    by (simp add: ustrong_convergence_def)
  hence \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>hsphere. (*f2* f) N x \<approx> (*f* l) x\<close>
    using hsphere_def nsuniform_convergence_D by blast                    
  thus \<open>(*f2* f) N x \<approx> (*f* l) x\<close>
    by (simp add: \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> sphere_iff)
qed

lemma nsustrong_convergence_const:
  fixes k :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  assumes \<open>\<And> n::nat. f n = k\<close>
  shows \<open>f\<midarrow>ustrong\<rightarrow> k\<close>
proof-
  have \<open>\<forall> n. \<forall> x::'a. norm x = 1 \<longrightarrow> f n x = k x\<close>
    using  \<open>\<And> n::nat. f n = k\<close> by auto
  hence \<open>\<forall> n. \<forall> x::'a star. hnorm x = 1 \<longrightarrow> (*f2* f) n x = (*f* k) x\<close>
    by StarDef.transfer
  thus ?thesis
    by (simp add: nsustrong_convergence_I)  
qed

lemma nsustrong_convergence_add: "X \<midarrow>ustrong\<rightarrow> a \<Longrightarrow> Y \<midarrow>ustrong\<rightarrow> b
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. X n t + Y n t)) \<midarrow>ustrong\<rightarrow> (\<lambda> t. a t + b t)"
  unfolding ustrong_convergence_def
  using uniform_limit_add by blast

lemma nsustrong_convergence_add_const: "f \<midarrow>ustrong\<rightarrow> a
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. f n t + b)) \<midarrow>ustrong\<rightarrow> (\<lambda> t. a t + b)"
  by (simp only: nsustrong_convergence_add nsustrong_convergence_const)

lemma bounded_linear_HFinite:
  \<open>bounded_linear a \<Longrightarrow> hnorm x = 1 \<Longrightarrow> ((*f* a) x) \<in> HFinite\<close>
  unfolding HFinite_def
  apply auto
proof-
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
  thus \<open>\<exists>xa\<in>\<real>. hnorm ((*f* a) x) < xa\<close> by auto
qed

lemma nsustrong_convergence_mult: "X \<midarrow>ustrong\<rightarrow> a \<Longrightarrow> Y \<midarrow>ustrong\<rightarrow> b
 \<Longrightarrow> bounded_linear a \<Longrightarrow> bounded_linear b 
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. X n t * Y n t)) \<midarrow>ustrong\<rightarrow> (\<lambda> t. a t * b t)"
  for a b :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow> a\<close> and \<open>Y \<midarrow>ustrong\<rightarrow> b\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
    and \<open>bounded_linear a\<close> and \<open>bounded_linear b\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow> a\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_D by blast 
  moreover have \<open>(*f2* Y) N x \<approx> (*f* b) x\<close>
    using \<open>Y \<midarrow>ustrong\<rightarrow> b\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_D by blast 
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
    by smt
qed

lemma nsustrong_convergence_minus: "X \<midarrow>ustrong\<rightarrow> a
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. - X n t)) \<midarrow>ustrong\<rightarrow> (\<lambda> t. - a t)"
  unfolding ustrong_convergence_def
  using uniform_limit_uminus by fastforce

lemma nsustrong_convergence_minus_cancel: "(\<lambda>n. (\<lambda> t. - X n t)) \<midarrow>ustrong\<rightarrow> (\<lambda> t. - a t)
 \<Longrightarrow> X \<midarrow>ustrong\<rightarrow> a"
  by (drule nsustrong_convergence_minus) simp

lemma nsustrong_convergence_diff: "X \<midarrow>ustrong\<rightarrow> a \<Longrightarrow> Y \<midarrow>ustrong\<rightarrow> b
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. X n t - Y n t)) \<midarrow>ustrong\<rightarrow> (\<lambda> t. a t - b t)"
  using nsustrong_convergence_add [of X a "- Y" "- b"]
  by (simp add: nsustrong_convergence_minus fun_Compl_def)

lemma nsustrong_convergence_diff_const: "f  \<midarrow>ustrong\<rightarrow> a
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. f n t - b)) \<midarrow>ustrong\<rightarrow> (\<lambda> t. a t - b)"
  by (simp add: nsustrong_convergence_diff nsustrong_convergence_const)

lemma nsustrong_convergence_inverse: "X  \<midarrow>ustrong\<rightarrow> a \<Longrightarrow> 
 bounded_linear a \<Longrightarrow> \<exists> e > 0. \<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. inverse (X n t) )) \<midarrow>ustrong\<rightarrow> (\<lambda> t. inverse (a t))"
  for a :: "'a::real_normed_vector \<Rightarrow>'b::real_normed_div_algebra"
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow> a\<close> and \<open>N \<in> HNatInfinite\<close>
    and \<open>hnorm x = 1\<close> and \<open>\<exists> e > 0. \<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e\<close> and \<open>bounded_linear a\<close>
  from \<open>X \<midarrow>ustrong\<rightarrow> a\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close>
    by (simp add: nsustrong_convergence_D) 
  moreover have \<open>inverse ((*f2* X) N x) \<approx> (*f2* (\<lambda>n t. inverse (X n t))) N x\<close>
  proof-                            
    have \<open>\<forall> NN. \<forall> xx. inverse ( X NN xx) = ( (\<lambda>n t. inverse (X n t))) NN xx\<close>
      by blast
    hence \<open>\<forall> NN. \<forall> xx. inverse ((*f2* X) NN xx) = (*f2* (\<lambda>n t. inverse (X n t))) NN xx\<close>
      by StarDef.transfer
    thus ?thesis
      by simp 
  qed
  moreover have \<open>inverse ((*f* a) x) \<approx> (*f* (\<lambda>t. inverse (a t))) x\<close>
  proof-
    have \<open>\<forall> xx. inverse (a xx) = (\<lambda>t. inverse (a t)) xx\<close>
      by simp
    hence \<open>\<forall> xx. inverse ((*f* a) xx) = (*f* (\<lambda>t. inverse (a t))) xx\<close>
      by StarDef.transfer
    thus ?thesis by simp
  qed
  moreover have \<open>(*f* a) x \<in> HFinite - Infinitesimal\<close>
  proof
    show "(*f* a) x \<in> HFinite"
      using \<open>bounded_linear a\<close> \<open>hnorm x = 1\<close> bounded_linear_HFinite by auto
    show "(*f* a) x \<notin> Infinitesimal"
    proof
      show False
        if "(*f* a) x \<in> Infinitesimal"
      proof-
        from \<open>\<exists> e > 0. \<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e\<close>
        obtain e::real where \<open>e > 0\<close> and \<open>\<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e\<close>
          by blast
        from \<open>\<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e\<close>
        have \<open>\<forall> t. hnorm t = 1 \<longrightarrow> hnorm ((*f* a) t) > star_of e\<close>
          by StarDef.transfer
        hence  \<open>hnorm ((*f* a) x) > star_of e\<close>
          using \<open>hnorm x = 1\<close> by blast       
        thus ?thesis using \<open>e > 0\<close>
        proof -
          have "\<not> e \<le> 0"
            using \<open>0 < e\<close> by linarith
          thus ?thesis
            by (meson Infinitesimal_hnorm_iff \<open>hypreal_of_real e < hnorm ((*f* a) x)\<close> hypreal_of_real_less_Infinitesimal_le_zero star_of_le_0 that)
        qed 
      qed
    qed
  qed
  ultimately show \<open>(*f2* (\<lambda>n t. inverse (X n t))) N x \<approx> (*f* (\<lambda>t. inverse (a t))) x\<close>
    by (meson approx_inverse approx_sym approx_trans2)    
qed

lemma nsustrong_convergence_norm: \<open>X \<midarrow>ustrong\<rightarrow>  a \<Longrightarrow>
 (\<lambda>n. (\<lambda> t. norm (X n t))) \<midarrow>ustrong\<rightarrow> (\<lambda> t. norm (a t))\<close>
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>  a\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using  \<open>X \<midarrow>ustrong\<rightarrow>  a\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
      nsustrong_convergence_D by blast
  moreover have  \<open>hnorm ((*f2* X) N x) \<approx> (*f2* (\<lambda>n t. norm (X n t))) N x\<close>
  proof-
    have \<open>\<forall> NN. \<forall> xx. norm ( X NN xx) = ( (\<lambda>n t. norm (X n t))) NN xx\<close>
      by blast
    hence \<open>\<forall> NN. \<forall> xx. hnorm ( (*f2* X) NN xx) = (*f2* (\<lambda>n t. norm (X n t))) NN xx\<close>
      by StarDef.transfer
    thus ?thesis by simp
  qed
  moreover have \<open>hnorm ((*f* a) x) \<approx> (*f* (\<lambda>t. norm (a t))) x\<close>
  proof-
    have \<open>\<forall> xx. norm (a xx) = (\<lambda>t. norm (a t)) xx\<close>
      by blast
    hence \<open>\<forall> xx. hnorm ((*f* a) xx) = (*f* (\<lambda>t. norm (a t))) xx\<close>
      by StarDef.transfer
    thus ?thesis by simp
  qed
  ultimately show \<open>(*f2* (\<lambda>n t. norm (X n t))) N x \<approx> (*f* (\<lambda>t. norm (a t))) x\<close>
    by (meson approx_hnorm approx_sym approx_trans2)    
qed

(* TODO: move to real_normed_vector? *)
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
      using linear_ball_zero by smt
    thus ?thesis
      by (meson eq_iff_diff_eq_0) 
  qed
qed

lemma nsustrong_convergence_unique: "X \<midarrow>ustrong\<rightarrow> a \<Longrightarrow> X \<midarrow>ustrong\<rightarrow> b
 \<Longrightarrow> linear a  \<Longrightarrow> linear b \<Longrightarrow> a = b"
proof-
  assume \<open>X \<midarrow>ustrong\<rightarrow> a\<close> and \<open>X \<midarrow>ustrong\<rightarrow> b\<close> and \<open>linear a\<close> and \<open>linear b\<close>
  have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow> a\<close>
    by (simp add: nsustrong_convergence_D)
  moreover have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow> (*f2* X) N x \<approx> (*f* b) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow> b\<close>
    by (simp add: nsustrong_convergence_D)
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

lemma nsustrong_convergence_iff:
  fixes l::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  shows "((\<lambda>n. f (Suc n)) \<midarrow>ustrong\<rightarrow> l) \<longleftrightarrow> (f \<midarrow>ustrong\<rightarrow> l)"
  unfolding ustrong_convergence_def
  using filterlim_sequentially_Suc by auto


end
section \<open>Miscellany of Analysis (classical and nonstandard)\<close>

(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Miscellany results on Nonstandard Analysis.

*)

theory NSA_Miscellany
  imports 
    "HOL-Analysis.Elementary_Metric_Spaces"
    "HOL-Analysis.Operator_Norm"
    Complex_Inner_Product
begin

unbundle nsa_notation

subsection \<open>Boundeness\<close>

lemma nsbounded_existencial:
  \<open>(\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite) \<longleftrightarrow> (\<exists>x. ((*f2* dist) x) ` (*s* S) \<subseteq> HFinite)\<close>
  for S::\<open>('a::metric_space) set\<close>
proof
  show "\<exists>x. (*f2* dist) x ` (*s* S) \<subseteq> HFinite"
    if "\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite"
    using that image_subset_iff  by fastforce
  show "\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite"
    if "\<exists>x. (*f2* dist) x ` (*s* S) \<subseteq> HFinite"
  proof-
    obtain z where \<open>(*f2* dist) z ` (*s* S) \<subseteq> HFinite\<close>
      using \<open>\<exists>x. (*f2* dist) x ` (*s* S) \<subseteq> HFinite\<close> by blast
    have \<open>x\<in>*s* S \<Longrightarrow> y\<in>*s* S \<Longrightarrow> (*f2* dist) x y \<in> HFinite\<close>
      for x y
    proof-
      assume \<open>x\<in>*s* S\<close> and \<open>y\<in>*s* S\<close>
      have \<open>(*f2* dist) x y \<le> (*f2* dist) x z + (*f2* dist) z y\<close>
      proof-
        have \<open>\<forall> xx yy zz. dist xx yy \<le> dist xx zz + dist zz yy\<close>
          by (simp add: dist_triangle)
        hence \<open>\<forall> xx yy zz. (*f2* dist) xx yy \<le> (*f2* dist) xx zz + (*f2* dist) zz yy\<close>
          by StarDef.transfer
        thus ?thesis by blast 
      qed
      moreover have \<open>(*f2* dist) x z + (*f2* dist) z y \<in> HFinite\<close>
      proof-
        have  \<open>(*f2* dist) x z \<in> HFinite\<close>
        proof-
          have  \<open>(*f2* dist) z x \<in> HFinite\<close>
            using \<open>(*f2* dist) z ` (*s* S) \<subseteq> HFinite\<close> \<open>x\<in>*s* S \<close> 
            by blast
          moreover have \<open>(*f2* dist) z x = (*f2* dist) x z\<close>
          proof-
            have \<open>\<forall> zz xx. dist zz xx = dist xx zz\<close>
              using dist_commute by blast
            hence \<open>\<forall> zz xx. (*f2* dist) zz xx = (*f2* dist) xx zz\<close>
              by StarDef.transfer
            thus ?thesis by blast
          qed
          ultimately show ?thesis by simp
        qed
        moreover have  \<open>(*f2* dist) z y \<in> HFinite\<close>
          using \<open>(*f2* dist) z ` (*s* S) \<subseteq> HFinite\<close> \<open>y\<in>*s* S \<close> 
          by blast
        ultimately show ?thesis
          by (simp add: HFinite_add) 
      qed
      moreover have \<open>0 \<le> (*f2* dist) x y\<close>
      proof-
        have \<open>\<forall> xx yy. 0 \<le> dist xx yy\<close>
          by simp
        hence \<open>\<forall> xx yy. 0 \<le> (*f2* dist) xx yy\<close>
          by StarDef.transfer
        show ?thesis
          by (simp add: \<open>\<forall>xx yy. 0 \<le> (*f2* dist) xx yy\<close>) 
      qed
      ultimately show ?thesis
        using HFinite_bounded by blast  
    qed
    thus ?thesis by blast
  qed
qed

lemma nsbounded_I:
  \<open>\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite \<Longrightarrow> \<exists>x. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
  by blast

lemma nsbounded_D:
  \<open>\<exists>x. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite \<Longrightarrow> \<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
  by (meson image_subsetI nsbounded_existencial)

lemma bounded_nsbounded:
  fixes S :: \<open>('a::metric_space) set\<close>
  assumes \<open>bounded S\<close>
  shows \<open>\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
proof-
  from  \<open>bounded S\<close>
  have \<open>\<exists> M. \<exists> u. \<forall> v \<in> S. dist u v < M\<close>
    by (meson bounded_def gt_ex le_less_trans)
  then obtain M where \<open>\<exists> u. \<forall> v \<in> S. dist u v < M\<close>
    by blast
  have \<open>\<exists> u. \<forall> v \<in> *s* S. (*f2* dist) u v < hypreal_of_real M\<close>
    using \<open>\<exists> u. \<forall> v \<in> S. dist u v < M\<close> by StarDef.transfer
  have \<open>\<exists> u. \<forall> v \<in> *s* S. (*f2* dist) u v \<in> HFinite\<close>
  proof-
    obtain u where \<open>\<forall> v \<in> *s* S. (*f2* dist) u v < hypreal_of_real M\<close>
      using  \<open>\<exists> u. \<forall> v \<in> *s* S. (*f2* dist) u v < hypreal_of_real M\<close>
      by blast
    have \<open>v \<in> *s* S \<Longrightarrow> (*f2* dist) u v \<in> HFinite\<close>
      for v
    proof-
      assume \<open>v \<in> *s* S\<close>
      hence \<open>(*f2* dist) u v < hypreal_of_real M\<close>
        using  \<open>\<forall> v \<in> *s* S. (*f2* dist) u v < hypreal_of_real M\<close>
        by blast
      moreover have \<open>hnorm ((*f2* dist) u v) = (*f2* dist) u v\<close>
      proof-
        have \<open>\<forall> uu vv. norm (dist uu vv) =  dist uu vv\<close>
          by simp         
        hence \<open>\<forall> uu vv. hnorm ((*f2* dist) uu vv) =  (*f2* dist) uu vv\<close>
          by StarDef.transfer
        thus ?thesis by blast
      qed
      ultimately show \<open>(*f2* dist) u v \<in> HFinite\<close>
        by (metis HInfiniteD HInfinite_HFinite_disj SReal_hypreal_of_real order.asym) 
    qed
    thus ?thesis
      by blast 
  qed    
  thus ?thesis
    by (simp add: nsbounded_D) 
qed

(* TODO: move? *)
lemma hypreal_of_hypnat_hypnat_of_nat_hypreal_of_nat:
  \<open>hypreal_of_hypnat (hypnat_of_nat n) = hypreal_of_nat n\<close>
proof-
  have \<open>(*f* of_nat) (star_of n) = (plus 1 ^^ n) (0::hypreal)\<close>
  proof(induction n)
    case 0
    thus ?case
      by (metis funpow_0 of_nat_0 star_zero_def starfun_eq) 
  next
    case (Suc n)
    thus ?case
      by (metis of_nat_def star_of_nat_def starfun_star_of) 
  qed
  thus ?thesis
    by (simp add: of_hypnat_def)  
qed

lemma nsbounded_bounded:
  fixes S :: \<open>('a::metric_space) set\<close>
  assumes \<open>\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
  shows \<open>bounded S\<close>
proof-
  have \<open>\<exists>x e. \<forall>y\<in>S. dist x y \<le> e\<close> 
  proof-
    from \<open>\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close>
    obtain x where \<open>\<forall> y \<in> *s* S. (*f2* dist) x y \<in> HFinite\<close>
      by blast
    have \<open>\<exists> M. \<forall> y \<in> *s* S. (*f2* dist) x y < M\<close>
    proof(rule classical)
      assume \<open>\<not>(\<exists> M. \<forall> y \<in> *s* S. (*f2* dist) x y < M)\<close>
      hence \<open>\<forall> M. \<exists> y \<in> *s* S. (*f2* dist) x y \<ge> M\<close>
        using leI by blast
      hence \<open>\<exists> y \<in> *s* S. (*f2* dist) x y \<ge> hypreal_of_hypnat whn\<close>
        by blast
      then obtain y where \<open>y \<in> *s* S\<close> and \<open>(*f2* dist) x y \<ge> hypreal_of_hypnat whn\<close>
        by blast
      have \<open>(*f2* dist) x y \<notin> HFinite\<close>
      proof(rule classical)
        assume \<open>\<not>((*f2* dist) x y \<notin> HFinite)\<close>
        hence \<open>(*f2* dist) x y \<in> HFinite\<close>
          by blast
        hence \<open>\<exists> r \<in> \<real>. hnorm ((*f2* dist) x y) < r\<close>
          using HFinite_def by blast
        moreover have \<open>hnorm ((*f2* dist) x y) = (*f2* dist) x y\<close>
        proof-
          have \<open>\<forall> xx. \<forall> yy. norm ( dist xx yy) = dist xx yy\<close>
            by simp
          hence \<open>\<forall> xx. \<forall> yy. hnorm ((*f2* dist) xx yy) = (*f2* dist) xx yy\<close>
            by StarDef.transfer
          thus ?thesis
            by blast 
        qed
        ultimately have \<open>\<exists> r \<in> \<real>. (*f2* dist) x y < r\<close>
          by simp
        hence \<open>\<exists> r \<in> \<real>. hypreal_of_hypnat whn < r\<close>
          using \<open>(*f2* dist) x y \<ge> hypreal_of_hypnat whn\<close>
            order.not_eq_order_implies_strict by fastforce
        then obtain r where \<open>r \<in> \<real>\<close> and \<open>hypreal_of_hypnat whn < r\<close>
          by blast
        have \<open>\<exists> n::nat. r < hypreal_of_nat n\<close>
        proof-
          from \<open>r \<in> \<real>\<close>
          have \<open>\<exists> s. r = hypreal_of_real s\<close>
            by (simp add: SReal_iff)
          then obtain s where \<open>r = hypreal_of_real s\<close>
            by blast
          have \<open>\<exists> n::nat. s < n\<close>
            by (simp add: reals_Archimedean2)
          then obtain n::nat where \<open>s < n\<close>
            by blast
          from \<open>s < n\<close>
          have \<open>hypreal_of_real s < hypreal_of_nat n\<close>
            by StarDef.transfer
          thus ?thesis using \<open>r = hypreal_of_real s\<close> by blast
        qed
        then obtain n where \<open>r < hypreal_of_nat n\<close>
          by blast
        from \<open>hypreal_of_hypnat whn < r\<close>  \<open>r < hypreal_of_nat n\<close>
        have \<open>hypreal_of_hypnat whn < hypreal_of_nat n\<close>
          by simp
        moreover have \<open>hypreal_of_nat n < hypreal_of_hypnat whn\<close>
        proof-
          have  \<open>hypnat_of_nat n < whn\<close>
            by simp
          hence  \<open>hypreal_of_hypnat (hypnat_of_nat n) < hypreal_of_hypnat whn\<close>
            by simp
          moreover have \<open>hypreal_of_hypnat (hypnat_of_nat n) = hypreal_of_nat n\<close>
            using hypreal_of_hypnat_hypnat_of_nat_hypreal_of_nat by blast
          ultimately show ?thesis by simp
        qed
        ultimately have \<open>hypreal_of_hypnat whn < hypreal_of_hypnat whn\<close>
          by simp
        thus ?thesis by blast
      qed
      thus ?thesis
        using \<open>\<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite\<close> \<open>y \<in> *s* S\<close> by auto 
    qed
    hence \<open>\<exists> x. \<exists>M. \<forall>y\<in>*s* S. (*f2* dist) x y < M\<close>
      by blast
    hence \<open>\<exists> x. \<exists>M. \<forall>y\<in>*s* S. (*f2* dist) x y \<le> M\<close>
      using le_less by blast
    thus ?thesis by StarDef.transfer 
  qed
  thus ?thesis using bounded_def by blast
qed

proposition bounded_nsbounded_iff:
  \<open>bounded S \<longleftrightarrow> (\<forall>x\<in>*s* S. \<forall>y\<in>*s* S. (*f2* dist) x y \<in> HFinite)\<close>
  using bounded_nsbounded nsbounded_bounded by blast


lemma ex_approx:
  fixes f::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
    and S::\<open>'a set\<close> and l::'b
  assumes \<open>\<forall>e>0. \<exists> x\<in>S. norm (f x - l) < e\<close>
  shows \<open>\<exists> x\<in>*s* S. (*f* f) x \<approx> star_of l\<close>
proof-
  have \<open>\<forall>e>0. \<exists> x. x\<in>S \<and> norm (f x - l) < e\<close>
    using \<open>\<forall>e>0. \<exists> x\<in>S. norm (f x - l) < e\<close>
    by blast
  hence \<open>\<exists> x. \<forall>e>0. x e \<in> S \<and> norm (f (x e) - l) < e\<close>
    by metis
  then obtain x where \<open>\<forall>e>0. x e \<in> S\<close> and \<open>\<forall>e>0. norm (f (x e) - l) < e\<close>
    by blast
  from \<open>\<forall>e>0. x e \<in> S\<close> 
  have \<open>\<forall>e>0. (*f* x) e \<in> *s* S\<close>
    by StarDef.transfer
  hence \<open>(*f* x) epsilon \<in> *s* S\<close>
    by (simp add: hypreal_epsilon_gt_zero)
  from  \<open>\<forall>e>0. norm (f (x e) - l) < e\<close>
  have  \<open>\<forall>e>0. hnorm ((*f* f) ((*f* x) e) - (star_of l)) < e\<close>
    by StarDef.transfer
  hence  \<open>hnorm ((*f* f) ((*f* x) epsilon) - (star_of l)) < epsilon\<close>
    by (simp add: hypreal_epsilon_gt_zero)
  hence  \<open>(*f* f) ((*f* x) epsilon) \<approx> (star_of l)\<close>
    by (metis Infinitesimal_epsilon add_diff_cancel_left' bex_Infinitesimal_iff2 diff_add_cancel hnorm_less_Infinitesimal)
  thus ?thesis using \<open>(*f* x) epsilon \<in> *s* S\<close> by blast
qed


lemma inv_hSuc_Infinite_Infinitesimal:
  \<open>N\<in>HNatInfinite \<Longrightarrow> inverse (hypreal_of_hypnat (hSuc N)) \<in> Infinitesimal\<close>
proof-
  assume \<open>N\<in>HNatInfinite\<close>
  have \<open>\<forall> n. n < Suc n\<close>
    by auto
  hence \<open>\<forall> n. n < hSuc n\<close>
    by StarDef.transfer
  hence \<open>N < hSuc N\<close>
    by blast
  hence \<open>hSuc N \<in> HNatInfinite\<close>
    using \<open>N\<in>HNatInfinite\<close> HNatInfinite_upward_closed dual_order.strict_implies_order by blast
  thus ?thesis
    by simp
qed

definition starfun3 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'a star \<Rightarrow> 'b star \<Rightarrow> 'c star \<Rightarrow> 'd star"  (\<open>*f3* _\<close> [80] 80)
  where "starfun3 f \<equiv> \<lambda>x y z. star_of f \<star> x \<star> y \<star> z"
declare starfun3_def [StarDef.transfer_unfold]

subsection \<open>Closure\<close>

lemma nsclosure_I:
  \<open>r \<in> closure A \<Longrightarrow> \<exists> a \<in> *s* A. star_of r \<approx> a\<close>
proof-
  assume \<open>r \<in> closure A\<close>
  hence \<open>\<exists> s::nat\<Rightarrow>_. (\<forall> n. s n \<in> A) \<and> s \<longlonglongrightarrow> r\<close>
    by (simp add: closure_sequential)
  then obtain s::\<open>nat\<Rightarrow>_\<close> where \<open>\<forall> n. s n \<in> A\<close> and \<open>s \<longlonglongrightarrow> r\<close>     
    by blast
  from  \<open>\<forall> n. s n \<in> A\<close>
  have \<open>\<forall> n. (*f* s) n \<in> *s* A\<close>
    by StarDef.transfer
  obtain N where \<open>N \<in> HNatInfinite\<close>
    using HNatInfinite_whn by blast
  have \<open>(*f* s) N \<in> *s* A\<close>    
    using \<open>\<forall> n. (*f* s) n \<in> *s* A\<close> by blast
  moreover have \<open>(*f* s) N \<approx> star_of r\<close>    
    using \<open>s \<longlonglongrightarrow> r\<close>
    by (simp add: LIMSEQ_NSLIMSEQ NSLIMSEQ_D \<open>N \<in> HNatInfinite\<close>)   
  ultimately show ?thesis
    using approx_reorient by blast 
qed

lemma nsclosure_D:
  \<open>\<exists> a \<in> *s* A. star_of r \<approx> a \<Longrightarrow> r \<in> closure A\<close>
proof-
  assume \<open>\<exists> a \<in> *s* A. star_of r \<approx> a\<close>
  hence \<open>\<exists> a \<in> *s* A. hnorm (star_of r - a) \<in> Infinitesimal\<close>
    using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by auto
  hence \<open>\<exists> a \<in> *s* A. \<forall> e\<in>Reals. e > 0 \<longrightarrow> hnorm (star_of r - a) <  e\<close>
    using Infinitesimal_less_SReal2 by blast
  hence \<open>\<forall> e\<in>Reals. e > 0 \<longrightarrow> (\<exists> a \<in> *s* A. hnorm (star_of r - a) <  e)\<close>
    by blast
  hence \<open>hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n ) > 0
   \<longrightarrow> (\<exists> a \<in> *s* A. hnorm (star_of r - a)
           < hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n ) )\<close>
    for n::nat    
    by auto
  hence \<open>\<exists> a \<in> *s* A. hnorm (star_of r - a)
           < hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
    for n::nat
    by (meson InfinitesimalD2 \<open>\<exists>a\<in>*s* A. star_of r \<approx> a\<close> bex_Infinitesimal_iff nice_ordered_field_class.inverse_positive_iff_positive of_nat_0_less_iff zero_less_Suc)    
  hence \<open>\<exists> a \<in>  A. norm (r - a)
           <  ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
    for n::nat
  proof-
    have \<open>\<exists> a \<in> *s* A. hnorm (star_of r - a)
           < hypreal_of_real ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
      using \<open>\<And>n. \<exists>a\<in>*s* A. hnorm (star_of r - a) < hypreal_of_real (inverse (real (Suc n)))\<close> by auto
    thus ?thesis
      by StarDef.transfer
  qed
  hence \<open>\<forall> n. \<exists> a \<in>  A. norm (r - a)
           <  ( (\<lambda>n. inverse (real (Suc n))) n )\<close>
    by blast
  hence \<open>\<exists> s. \<forall> n. s n \<in> A \<and> norm (r - s n)  <  (\<lambda>n. inverse (real (Suc n))) n\<close>
    by metis
  then obtain s where \<open>\<forall> n. s n \<in> A\<close> 
    and \<open>\<forall> n. norm (r - s n)  <  (\<lambda>n. inverse (real (Suc n))) n\<close> 
    by blast
  from \<open>\<forall> n. norm (r - s n)  <  (\<lambda>n. inverse (real (Suc n))) n\<close>
  have \<open>\<forall> n. hnorm (star_of r - (*f* s) n)  <  (*f* (\<lambda>n. inverse (real (Suc n)))) n\<close>
    by StarDef.transfer
  have \<open>N\<in>HNatInfinite \<Longrightarrow> (*f* s) N \<approx> star_of r\<close>
    for N
  proof-
    assume  \<open>N \<in> HNatInfinite\<close>
    have \<open>hnorm (star_of r - (*f* s) N)  <  (*f* (\<lambda>n. inverse (real (Suc n)))) N\<close>
      using \<open>\<forall> n. hnorm (star_of r - (*f* s) n)  <  (*f* (\<lambda>n. inverse (real (Suc n)))) n\<close>
        \<open>N \<in> HNatInfinite\<close>
      by blast
    moreover have \<open> (*f* (\<lambda>n. inverse (real (Suc n)))) N \<in> Infinitesimal\<close>
      using  \<open>N \<in> HNatInfinite\<close>
      by (metis (full_types) hSuc_def inv_hSuc_Infinite_Infinitesimal of_hypnat_def starfun_inverse2 starfun_o2)
    ultimately have \<open>hnorm (star_of r - (*f* s) N) \<in> Infinitesimal\<close>
      using Infinitesimal_hnorm_iff hnorm_less_Infinitesimal by blast
    thus \<open>(*f* s) N \<approx> star_of r\<close>
      by (meson Infinitesimal_hnorm_iff approx_sym bex_Infinitesimal_iff)
  qed
  hence \<open>s \<longlonglongrightarrow> r\<close>
    using NSLIMSEQ_I NSLIMSEQ_LIMSEQ by metis     
  thus ?thesis
    using \<open>\<forall> n. s n \<in> A\<close> closure_sequential by blast     
qed

text \<open>Theorem 10.1.1 (3) of [goldblatt2012lectures]\<close>
lemma nsclosure_iff:
  \<open>r \<in> closure A \<longleftrightarrow> (\<exists> a \<in> *s* A. star_of r \<approx> a)\<close>
  using nsclosure_D nsclosure_I by blast

text \<open>Hyperfinite set\<close>
definition hypfinite where \<open>hypfinite = (*p* finite)\<close> 


subsection \<open>Unsorted\<close>

lemma Cauchy_convergent_norm:
  \<open>Cauchy (x::nat \<Rightarrow> 'a::real_normed_vector) \<Longrightarrow> Cauchy (\<lambda> n. norm (x n))\<close>
proof-
  assume \<open>Cauchy x\<close>
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
    (*f* x) N \<approx> (*f* x) M\<close>
    for N M
    by (simp add: Cauchy_NSCauchy NSCauchyD)
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
    hnorm ((*f* x) N) \<approx> hnorm ((*f* x) M)\<close>
    for N M
    by (simp add: approx_hnorm)
  thus \<open>Cauchy (\<lambda> n. norm (x n))\<close>
    by (metis (full_types) NSCauchyI NSCauchy_Cauchy_iff starfun_hnorm)
qed

lemma Cauchy_add:
  fixes f g::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>Cauchy f\<close> and \<open>Cauchy g\<close>
  shows \<open>Cauchy (\<lambda> n. f n + g n)\<close>
proof-
  from \<open>Cauchy f\<close>
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (*f* f) M\<close>
    for N M::hypnat
    using NSCauchy_Cauchy_iff NSCauchy_def by blast
  from \<open>Cauchy g\<close>
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* g) N \<approx> (*f* g) M\<close>
    for N M::hypnat
    using NSCauchy_Cauchy_iff NSCauchy_def by blast
  from \<open>Cauchy f\<close>

  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
         (*f* (\<lambda> n. f n + g n)) N \<approx> (*f*  (\<lambda> n. f n + g n)) M\<close>
    for N M::hypnat
  proof-
    assume \<open>N \<in> HNatInfinite\<close> and \<open>M \<in> HNatInfinite\<close>
    have \<open>(*f* f) N + (*f* g) N \<approx> (*f* f) M + (*f* g) M\<close>
      using \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (*f* f) M\<close>
        \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* g) N \<approx> (*f* g) M\<close>
      using \<open>M \<in> HNatInfinite\<close> \<open>N \<in> HNatInfinite\<close> approx_add by auto      
    moreover have \<open>(*f* (\<lambda> n. f n + g n)) N = (*f* f) N + (*f* g) N\<close>
      by auto
    moreover have \<open>(*f* (\<lambda> n. f n + g n)) M = (*f* f) M + (*f* g) M\<close>
      by auto
    ultimately show \<open>(*f* (\<lambda> n. f n + g n)) N \<approx> (*f*  (\<lambda> n. f n + g n)) M\<close>
      by simp
  qed
  thus \<open>Cauchy (\<lambda> n. f n + g n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed

lemma lim_leq:
  fixes x y :: \<open>nat \<Rightarrow> real\<close>
  assumes \<open>\<And> n. x n \<le> y n\<close> and \<open>convergent x\<close> and \<open>convergent y\<close>
  shows \<open>lim x \<le> lim y\<close>
  by (metis NSLIMSEQ_le NSconvergent_def assms(1) assms(2) assms(3) convergent_NSconvergent_iff lim_nslim_iff nslimI)

lemma lim_ge:
  fixes x ::real and y :: \<open>nat \<Rightarrow> real\<close>
  assumes \<open>\<And> n. x \<le> y n\<close> and \<open>convergent y\<close>
  shows \<open>x \<le> lim y\<close>
  using lim_leq
  by (metis (full_types) NSLIMSEQ_le_const NSconvergent_NSLIMSEQ_iff assms(1) assms(2) convergent_NSconvergent_iff lim_nslim_iff) 

lemma lim_add:
  fixes x y :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>convergent x\<close> and \<open>convergent y\<close>
  shows \<open>lim (\<lambda> n. x n + y n) = lim x + lim y\<close>
proof-
  have \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* x) N \<approx> star_of (lim x)\<close>
    for N
    using \<open>convergent x\<close>
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  moreover have \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* y) N \<approx> star_of (lim y)\<close>
    for N
    using \<open>convergent y\<close>
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow>  (*f* x) N + (*f* y) N \<approx> star_of (lim x) + star_of (lim y)\<close>
    for N
    by (simp add: approx_add)
  moreover have \<open>(*f* (\<lambda> n. x n + y n)) N = (*f* x) N + (*f* y) N\<close>
    for N
    by auto
  moreover have \<open>star_of (lim x + lim y) = star_of (lim x) + star_of (lim y)\<close>
    by auto
  ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow>  (*f* (\<lambda> n. x n + y n)) N \<approx> star_of (lim x + lim y)\<close>
    for N
    by simp
  thus ?thesis
    by (simp add: NSLIMSEQ_I lim_nslim_iff nslimI) 
qed


lemma lim_add_const_left:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and c::'a
  assumes  \<open>convergent x\<close>
  shows \<open>lim (\<lambda> n. c + x n) = c + lim x\<close>
proof-
  have \<open>convergent (\<lambda> i. c)\<close>
    by (simp add: convergent_const)    
  hence \<open>lim (\<lambda> n. (\<lambda> i. c) n + x n) = lim (\<lambda> n. c) + lim x\<close>
    using \<open>convergent x\<close> lim_add[where x = "(\<lambda> i. c)" and y = "x"]
    by blast
  moreover have \<open>lim (\<lambda> i. c) = c\<close>
    by simp
  ultimately show ?thesis by auto
qed

lemma lim_add_const_right:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes  \<open>convergent x\<close>
  shows \<open>lim (\<lambda> n. x n + c) = lim x + c\<close>
proof-
  have \<open>lim (\<lambda> n. c + x n) = c + lim x\<close>
    using assms lim_add_const_left by blast
  moreover have \<open>(\<lambda> n. c + x n) = (\<lambda> n. x n + c)\<close>
    by auto
  moreover have \<open>c + lim x = lim x + c\<close>
    by simp
  ultimately show ?thesis by simp
qed

lemma lim_scaleR:
  fixes x :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close> and r::real
  assumes \<open>convergent x\<close> 
  shows \<open>lim (\<lambda> n. r *\<^sub>R x n ) = r *\<^sub>R lim x\<close>
proof-
  have \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* x) N \<approx> star_of (lim x)\<close>
    for N
    using \<open>convergent x\<close>
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  hence \<open>N \<in> HNatInfinite \<Longrightarrow>  r *\<^sub>R (*f* x) N \<approx> r *\<^sub>R (star_of (lim x)) \<close>
    for N
    by (simp add: approx_scaleR2)
  moreover have \<open> (*f* (\<lambda> n. r *\<^sub>R x n)) N = r *\<^sub>R (*f* x) N\<close>
    for N
    by (simp add: star_scaleR_def)    
  moreover have \<open>star_of (r *\<^sub>R lim x) = r *\<^sub>R star_of (lim x)\<close>
    by auto
  ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow>  (*f* (\<lambda> n. r *\<^sub>R x n)) N \<approx> star_of (r *\<^sub>R lim x)\<close>
    for N
    by auto
  thus ?thesis
    by (simp add: NSLIMSEQ_I lim_nslim_iff nslimI) 
qed


lemma Cauchy_minus:
  fixes f g::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  shows  \<open>Cauchy f \<Longrightarrow> Cauchy g \<Longrightarrow> Cauchy (\<lambda> n. f n - g n)\<close>
proof-
  assume \<open>Cauchy f\<close> and \<open>Cauchy g\<close>
  from \<open>Cauchy f\<close>
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (*f* f) M\<close>
    for N M::hypnat
    using NSCauchy_Cauchy_iff NSCauchy_def by blast
  from \<open>Cauchy g\<close>
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* g) N \<approx> (*f* g) M\<close>
    for N M::hypnat
    using NSCauchy_Cauchy_iff NSCauchy_def by blast
  from \<open>Cauchy f\<close>

  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
         (*f* (\<lambda> n. f n -g n)) N \<approx> (*f*  (\<lambda> n. f n -g n)) M\<close>
    for N M::hypnat
  proof-
    assume \<open>N \<in> HNatInfinite\<close> and \<open>M \<in> HNatInfinite\<close>
    have \<open>(*f* f) N - (*f* g) N \<approx> (*f* f) M - (*f* g) M\<close>
      using \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (*f* f) M\<close>
        \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* g) N \<approx> (*f* g) M\<close>
      by (simp add: \<open>M \<in> HNatInfinite\<close> \<open>N \<in> HNatInfinite\<close> approx_diff)
    moreover have \<open>(*f* (\<lambda> n. f n -g n)) N = (*f* f) N - (*f* g) N\<close>
      by auto
    moreover have \<open>(*f* (\<lambda> n. f n -g n)) M = (*f* f) M - (*f* g) M\<close>
      by auto
    ultimately show \<open>(*f* (\<lambda> n. f n -g n)) N \<approx> (*f*  (\<lambda> n. f n -g n)) M\<close>
      by simp
  qed
  thus \<open>Cauchy (\<lambda> n. f n - g n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed

lemma Cauchy_sgn:
  fixes x::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>Cauchy x\<close>
  shows \<open>Cauchy (\<lambda> n. (x n) /\<^sub>R lim (\<lambda> n. norm (x n)))\<close>
proof-
  have \<open>\<exists> L::real. lim (\<lambda>n. norm (x n)) = L\<close>
    by auto
  then obtain L where \<open>lim (\<lambda>n. norm (x n)) = L\<close>
    by blast
  show \<open>Cauchy (\<lambda>n. x n /\<^sub>R lim (\<lambda>n. norm (x n)))\<close>
  proof (cases \<open>L = 0\<close>)
    show "Cauchy (\<lambda>n. x n /\<^sub>R lim (\<lambda>n. norm (x n)))"
      if "L = 0"
    proof-
      have \<open>(x n) /\<^sub>R L = 0\<close>
        for n
        using that by simp
      hence \<open>(\<lambda>n. (x n) /\<^sub>R L) = (\<lambda> _. 0)\<close>
        by blast
      moreover have \<open>lim (\<lambda> _. 0) = 0\<close>
        by auto
      ultimately have \<open>(\<lambda>n. (x n) /\<^sub>R L) \<longlonglongrightarrow> 0\<close>
        by simp
      hence \<open>convergent (\<lambda>n. (x n) /\<^sub>R L)\<close>
        unfolding convergent_def
        by blast
      thus ?thesis
        using  \<open>lim (\<lambda>n. norm (x n)) = L\<close> LIMSEQ_imp_Cauchy \<open>(\<lambda>n. x n /\<^sub>R L) \<longlonglongrightarrow> 0\<close> by blast
    qed
    show "Cauchy (\<lambda>n. x n /\<^sub>R lim (\<lambda>n. norm (x n)))"
      if "L \<noteq> 0"
    proof-
      have \<open>(\<lambda>n. x n /\<^sub>R lim (\<lambda>n. norm (x n))) = (\<lambda>n. x n /\<^sub>R L)\<close>
        using \<open>lim (\<lambda>n. norm (x n)) = L\<close> by simp
      have \<open>Cauchy (\<lambda>n. x n /\<^sub>R L)\<close>
      proof-
        from \<open>Cauchy x\<close>
        have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
            (*f* x) N \<approx> (*f* x) M\<close>
          for N M
          by (simp add: Cauchy_NSCauchy NSCauchyD)
        hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
         (*f2* scaleR) (inverse (star_of L)) ((*f* x) N) \<approx> (*f2* scaleR) (inverse (star_of L)) ((*f* x) M)\<close>
          for N M
        proof -
          assume a1: "N \<in> HNatInfinite"
          assume "M \<in> HNatInfinite"
          hence "(*f* x) N \<approx> (*f* x) M"
            using a1 by (metis \<open>\<And>N M. \<lbrakk>N \<in> HNatInfinite; M \<in> HNatInfinite\<rbrakk> \<Longrightarrow> (*f* x) N \<approx> (*f* x) M\<close>)
          thus ?thesis
            by (metis (no_types) approx_scaleR2 star_of_inverse star_scaleR_def starfun2_star_of)
        qed
        moreover have \<open>(*f2* scaleR) (inverse (star_of L)) ((*f* x) N) =  (*f* (\<lambda>n. x n /\<^sub>R L)) N\<close>
          for N
          by (metis star_of_inverse starfun2_star_of starfun_o2)
        ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
               (*f* (\<lambda>n. x n /\<^sub>R L)) N \<approx> (*f* (\<lambda>n. x n /\<^sub>R L)) M\<close>
          for N M
          by simp
        thus ?thesis
          using NSCauchyI NSCauchy_Cauchy by blast 
      qed
      thus ?thesis
        by (simp add: \<open>lim (\<lambda>n. norm (x n)) = L\<close>)  
    qed
  qed
qed


lemma Cauchy_scaleR:
  fixes r::real and x::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  shows \<open>Cauchy x \<Longrightarrow> Cauchy (\<lambda>n. r *\<^sub>R x n)\<close>
proof-
  assume \<open>Cauchy x\<close>
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
    (*f* x) N \<approx> (*f* x) M\<close>
    for N M
    by (simp add: NSCauchyD NSCauchy_Cauchy_iff)
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
     (*f2* scaleR) (star_of r) ((*f* x) N) \<approx> (*f2* scaleR) (star_of r) ((*f* x) M)\<close>
    for N M
    by (metis approx_scaleR2 star_scaleR_def starfun2_star_of)
  moreover have \<open>(*f2* scaleR) (star_of r) ((*f* x) N) = (*f* (\<lambda>n. r *\<^sub>R x n)) N\<close>
    for N
    by auto
  ultimately have  \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
      (*f* (\<lambda>n. r *\<^sub>R x n)) N \<approx> (*f* (\<lambda>n. r *\<^sub>R x n)) M\<close>
    for N M
    by simp
  thus \<open>Cauchy (\<lambda>n. r *\<^sub>R x n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed

lemma Infinitesimal_scaleC2: 
  fixes x :: \<open>('a::complex_normed_vector) star\<close>
  assumes "x \<in> Infinitesimal" 
  shows "a *\<^sub>C x \<in> Infinitesimal"
proof-
  have \<open>hnorm x \<in> Infinitesimal\<close>
    using \<open>x \<in> Infinitesimal\<close>
    by (simp add: Infinitesimal_hnorm_iff)
  hence \<open>(star_of (cmod a)) * hnorm x \<in> Infinitesimal\<close>
    using Infinitesimal_star_of_mult2 by blast
  moreover have \<open>(star_of (cmod a)) * hnorm x = hnorm (a *\<^sub>C x)\<close>
    by (simp add: hnorm_scaleC)
  ultimately have \<open>hnorm (a *\<^sub>C x) \<in> Infinitesimal\<close>
    by simp
  thus ?thesis by (simp add: Infinitesimal_hnorm_iff)
qed

lemma approx_scaleC2: 
  fixes a b :: \<open>('a::complex_normed_vector) star\<close>
  shows "a \<approx> b \<Longrightarrow> c *\<^sub>C a \<approx> c *\<^sub>C b"
proof-
  assume \<open>a \<approx> b\<close>
  hence \<open>a - b \<in> Infinitesimal\<close>
    by (simp add: Infinitesimal_approx_minus)
  hence \<open>c *\<^sub>C (a - b) \<in> Infinitesimal\<close>
    by (simp add: Infinitesimal_scaleC2)
  moreover have \<open>c *\<^sub>C (a - b) = c *\<^sub>C a - c *\<^sub>C b\<close>
    by (simp add: complex_vector.scale_right_diff_distrib)
  ultimately have \<open>c *\<^sub>C a - c *\<^sub>C b \<in> Infinitesimal\<close> 
    by simp
  thus ?thesis by (simp add: Infinitesimal_approx_minus)
qed

lemma Cauchy_scaleC:
  fixes r::complex and x::\<open>nat \<Rightarrow> 'a::complex_normed_vector\<close>
  shows \<open>Cauchy x \<Longrightarrow> Cauchy (\<lambda>n. r *\<^sub>C x n)\<close>
proof-
  assume \<open>Cauchy x\<close>
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
    (*f* x) N \<approx> (*f* x) M\<close>
    for N M
    by (simp add: NSCauchyD NSCauchy_Cauchy_iff)
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
     (*f2* scaleC) (star_of r) ((*f* x) N) \<approx> (*f2* scaleC) (star_of r) ((*f* x) M)\<close>
    for N M
    by (metis approx_scaleC2 star_scaleC_def starfun2_star_of)
  moreover have \<open>(*f2* scaleC) (star_of r) ((*f* x) N) = (*f* (\<lambda>n. r *\<^sub>C x n)) N\<close>
    for N
  proof-
    have \<open>\<forall> n. ( scaleC) ( r) (( x) n) = ( (\<lambda>n. r *\<^sub>C x n)) n\<close>
      by auto
    hence \<open>\<forall> n. (*f2* scaleC) (star_of r) ((*f* x) n) = (*f* (\<lambda>n. r *\<^sub>C x n)) n\<close>
      by StarDef.transfer
    thus ?thesis by blast
  qed
  ultimately have  \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
      (*f* (\<lambda>n. r *\<^sub>C x n)) N \<approx> (*f* (\<lambda>n. r *\<^sub>C x n)) M\<close>
    for N M
    by simp
  thus \<open>Cauchy (\<lambda>n. r *\<^sub>C x n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed


lemma limit_point_Cauchy:
  assumes \<open>Cauchy x\<close>
  shows \<open>\<exists> L\<in>HFinite. \<forall> N \<in> HNatInfinite. (*f* x) N \<approx> L\<close>
proof-
  have \<open>\<exists> L. \<forall> N. N \<in> HNatInfinite \<longrightarrow> (*f* x) N \<approx> L\<close>
    using Cauchy_NSCauchy NSCauchyD assms by blast
  then obtain L where \<open>\<forall> N. N \<in> HNatInfinite \<longrightarrow> (*f* x) N \<approx> L\<close>
    by blast
  moreover have \<open>\<forall> N. N \<in> HNatInfinite \<longrightarrow> (*f* x) N \<in> HFinite\<close>
    by (simp add: Cauchy_NSCauchy NSBseqD2 NSCauchy_NSBseq assms)
  ultimately show ?thesis
    using HFinite_star_of approx_HFinite by blast 
qed

lemma lim_initial_segment:
  assumes \<open>convergent x\<close>
  shows \<open>lim x = lim (\<lambda> n. x (n + k))\<close>
proof-
  have \<open>\<exists> L. x \<longlonglongrightarrow> L\<close>
    using \<open>convergent x\<close>
    unfolding convergent_def
    by blast
  then obtain L where \<open>x \<longlonglongrightarrow> L\<close>
    by blast
  hence \<open>(\<lambda> n. x (n + k)) \<longlonglongrightarrow> L\<close>
    using Topological_Spaces.LIMSEQ_ignore_initial_segment
    by auto
  thus ?thesis 
    unfolding lim_def
    by (metis LIMSEQ_unique \<open>x \<longlonglongrightarrow> L\<close>) 
qed

lemma lim_initial_segment':
  assumes \<open>convergent x\<close>
  shows \<open>lim x = lim (\<lambda> n. x (k + n))\<close>
proof-
  have \<open>lim x = lim (\<lambda> n. x (n + k))\<close>
    using \<open>convergent x\<close> lim_initial_segment by blast
  moreover have \<open>n + k = k + n\<close>
    for n
    by simp
  ultimately show ?thesis by auto
qed

lemma Lim_bounded_lim:
  fixes x :: \<open>nat \<Rightarrow> 'a::linorder_topology\<close>
  assumes \<open>convergent x\<close> and \<open>\<forall>n\<ge>M. x n \<le> C\<close>
  shows \<open>lim x \<le> C\<close>
proof-
  have \<open>\<exists> l. x \<longlonglongrightarrow> l\<close>
    using \<open>convergent x\<close>
    unfolding convergent_def
    by blast
  then obtain l where \<open>x \<longlonglongrightarrow> l\<close>
    by blast
  hence \<open>l \<le> C\<close> using \<open>\<forall>n\<ge>M. x n \<le> C\<close>
    using Topological_Spaces.Lim_bounded
    by blast
  thus ?thesis unfolding lim_def using \<open>x \<longlonglongrightarrow> l\<close>
    by (metis limI t2_space_class.Lim_def) 
qed

lemma Cauchy_cinner_Cauchy:
  fixes x y :: \<open>nat \<Rightarrow> 'a::complex_inner\<close>
  assumes \<open>Cauchy x\<close> and \<open>Cauchy y\<close>
  shows \<open>Cauchy (\<lambda> n. \<langle> x n, y n \<rangle>)\<close>
proof-
  have \<open>\<exists> M. \<forall> n. norm (x n) < M \<and> norm (y n) < M\<close>
  proof-
    have \<open>\<exists> M. \<forall> n. norm (x n) < M\<close>
    proof-
      have \<open>bounded (range x)\<close>
        using \<open>Cauchy x\<close>
        by (simp add: Elementary_Metric_Spaces.cauchy_imp_bounded)
      thus ?thesis
        by (meson bounded_pos_less rangeI)  
    qed
    moreover have \<open>\<exists> M. \<forall> n. norm (y n) < M\<close>
    proof-
      have \<open>bounded (range y)\<close>
        using \<open>Cauchy y\<close>
        by (simp add: Elementary_Metric_Spaces.cauchy_imp_bounded)
      thus ?thesis
        by (meson bounded_pos_less rangeI)  
    qed
    ultimately show ?thesis
      by (metis dual_order.strict_trans linorder_neqE_linordered_idom) 
  qed
  then obtain M where \<open>\<forall> n. norm (x n) < M\<close> and \<open>\<forall> n. norm (y n) < M\<close>
    by blast
  have \<open>M > 0\<close>
    using \<open>\<forall> n. norm (x n) < M\<close>
    by (smt norm_not_less_zero) 
  have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N. \<forall> m \<ge> N. norm ( (\<lambda> i. \<langle> x i, y i \<rangle>) n -  (\<lambda> i. \<langle> x i, y i \<rangle>) m ) < e\<close>
    for e
  proof-
    assume \<open>e > 0\<close>
    hence \<open>e / (2*M) > 0\<close>
      using \<open>M > 0\<close> by auto
    hence \<open>\<exists> N. \<forall> n\<ge>N. \<forall> m\<ge>N. norm (x n - x m) < e / (2*M)\<close>
      using \<open>Cauchy x\<close>
      by (simp add: Cauchy_iff) 
    then obtain N1 where \<open>\<forall> n\<ge>N1. \<forall> m\<ge>N1. norm (x n - x m) < e / (2*M)\<close>
      by blast
    have \<open>\<exists> N. \<forall> n\<ge>N. \<forall> m\<ge>N. norm (y n - y m) < e / (2*M)\<close>
      using \<open>Cauchy y\<close> \<open>e / (2*M) > 0\<close>
      by (simp add: Cauchy_iff) 
    obtain N2 where \<open>\<forall> n\<ge>N2. \<forall> m\<ge>N2. norm (y n - y m) < e / (2*M)\<close>
      using \<open>\<exists> N. \<forall> n\<ge>N. \<forall> m\<ge>N. norm (y n - y m) < e / (2*M)\<close>
      by blast
    define N where \<open>N = N1 + N2\<close>
    hence \<open>N \<ge> N1\<close>
      by auto
    have \<open>N \<ge> N2\<close>
      using \<open>N = N1 + N2\<close>
      by auto
    have \<open>n \<ge> N \<Longrightarrow> m \<ge> N \<Longrightarrow> norm ( \<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle> ) < e\<close>
      for n m
    proof-
      assume \<open>n \<ge> N\<close> and \<open>m \<ge> N\<close>
      have \<open>\<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle> = (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) + (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>)\<close>
        by simp
      hence \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle>) \<le> norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>)
           + norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>)\<close>
        by (metis norm_triangle_ineq)
      moreover have \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) < e/2\<close>
      proof-
        have \<open>\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle> = \<langle> x n - x m, y n \<rangle>\<close>
          by (simp add: cinner_diff_left)
        hence \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) = norm \<langle> x n - x m, y n \<rangle>\<close>
          by simp
        moreover have \<open>norm \<langle> x n - x m, y n \<rangle> \<le> norm (x n - x m) * norm (y n)\<close>
          using complex_inner_class.norm_cauchy_schwarz by auto
        moreover have \<open>norm (y n) < M\<close>
          using \<open>\<forall> n. norm (y n) < M\<close> by blast
        moreover have \<open>norm (x n - x m) < e/(2*M)\<close>
          using \<open>N \<le> m\<close> \<open>N \<le> n\<close> \<open>N1 \<le> N\<close> \<open>\<forall>n\<ge>N1. \<forall>m\<ge>N1. norm (x n - x m) < e / (2 * M)\<close> by auto          
        ultimately have \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) < (e/(2*M)) * M\<close>
          by (smt linordered_semiring_strict_class.mult_strict_mono norm_ge_zero)
        moreover have \<open> (e/(2*M)) * M = e/2\<close>
          using \<open>M > 0\<close> by simp
        ultimately have  \<open>norm (\<langle> x n, y n \<rangle> - \<langle> x m, y n \<rangle>) < e/2\<close>
          by simp
        thus ?thesis by blast
      qed
      moreover have \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) < e/2\<close>
      proof-
        have \<open>\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle> = \<langle> x m, y n - y m \<rangle>\<close>
          by (simp add: cinner_diff_right)
        hence \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) = norm \<langle> x m, y n - y m \<rangle>\<close>
          by simp
        moreover have \<open>norm \<langle> x m, y n - y m \<rangle> \<le> norm (x m) * norm (y n - y m)\<close>
          using complex_inner_class.norm_cauchy_schwarz by auto
        moreover have \<open>norm (x m) < M\<close>
          using \<open>\<forall> n. norm (x n) < M\<close> by blast
        moreover have \<open>norm (y n - y m) < e/(2*M)\<close>
          using \<open>N \<le> m\<close> \<open>N \<le> n\<close> \<open>N2 \<le> N\<close> \<open>\<forall>n\<ge>N2. \<forall>m\<ge>N2. norm (y n - y m) < e / (2 * M)\<close> by auto          
        ultimately have \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) < M * (e/(2*M))\<close>
          by (smt linordered_semiring_strict_class.mult_strict_mono norm_ge_zero)
        moreover have \<open>M * (e/(2*M)) = e/2\<close>
          using \<open>M > 0\<close> by simp
        ultimately have  \<open>norm (\<langle> x m, y n \<rangle> - \<langle> x m, y m \<rangle>) < e/2\<close>
          by simp
        thus ?thesis by blast
      qed
      ultimately show \<open>norm ( \<langle> x n, y n \<rangle> - \<langle> x m, y m \<rangle> ) < e\<close> by simp
    qed
    thus ?thesis by blast
  qed
  thus ?thesis
    by (simp add: CauchyI)
qed

lemma Cauchy_cinner_convergent:
  fixes x y :: \<open>nat \<Rightarrow> 'a::complex_inner\<close>
  assumes \<open>Cauchy x\<close> and \<open>Cauchy y\<close>
  shows \<open>convergent (\<lambda> n. \<langle> x n, y n \<rangle>)\<close>
proof-
  have \<open>Cauchy (\<lambda> n. \<langle> x n, y n \<rangle>)\<close>
    using \<open>Cauchy x\<close> \<open>Cauchy y\<close> Cauchy_cinner_Cauchy
    by blast
  hence \<open>Cauchy (\<lambda> n. norm \<langle> x n, y n \<rangle>)\<close>
    by (simp add: Cauchy_convergent_norm)
  hence \<open>convergent (\<lambda> n. norm \<langle> x n, y n \<rangle>)\<close>
    using Cauchy_convergent_iff by auto
  thus ?thesis
    using Cauchy_convergent_iff \<open>Cauchy (\<lambda>n. \<langle>x n, y n\<rangle>)\<close> by auto
qed

lemma lim_minus:
  fixes x y :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>convergent x\<close> and \<open>convergent y\<close>
  shows \<open>lim (\<lambda> n. x n - y n) = lim x - lim y\<close>
proof-
  have \<open>convergent (\<lambda> i. x i - y i)\<close>
    using \<open>convergent x\<close>  \<open>convergent y\<close>
    by (simp add: convergent_diff)
  hence \<open>lim (\<lambda> n. (\<lambda> i. x i - y i) n + y n) = lim (\<lambda> i. x i - y i) + lim y\<close>
    using \<open>convergent y\<close> lim_add by blast
  moreover have \<open>(\<lambda> n. (\<lambda> i. x i - y i) n + y n) = x\<close>
    by auto
  ultimately have \<open>lim x = lim (\<lambda> i. x i - y i) + lim y\<close>
    by simp
  thus ?thesis by simp
qed

lemma lim_scaleC:
  fixes x :: \<open>nat \<Rightarrow> 'a::complex_normed_vector\<close> and r::complex
  assumes \<open>convergent x\<close> 
  shows \<open>lim (\<lambda> n. r *\<^sub>C x n ) = r *\<^sub>C lim x\<close>
proof-
  have \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* x) N \<approx> star_of (lim x)\<close>
    for N
    using \<open>convergent x\<close>
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  hence \<open>N \<in> HNatInfinite \<Longrightarrow>  r *\<^sub>C (*f* x) N \<approx> r *\<^sub>C (star_of (lim x)) \<close>
    for N
    by (simp add: approx_scaleC2)
  moreover have \<open>(*f* (\<lambda> n. r *\<^sub>C x n)) N = r *\<^sub>C (*f* x) N\<close>
    for N
    using star_scaleC_def
    by (metis starfun_o2) 
  moreover have \<open>star_of (r *\<^sub>C lim x) = r *\<^sub>C star_of (lim x)\<close>
    by auto
  ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow>  (*f* (\<lambda> n. r *\<^sub>C x n)) N \<approx> star_of (r *\<^sub>C lim x)\<close>
    for N
    by auto
  thus ?thesis
    by (simp add: NSLIMSEQ_I lim_nslim_iff nslimI) 
qed

lemma lim_Lim_bounded2:
  fixes x::\<open>nat \<Rightarrow> real\<close>
  assumes \<open>\<forall> n \<ge> N. C \<le> x n\<close> and \<open>convergent x\<close>
  shows \<open>C \<le> lim x\<close>
proof-
  have \<open>\<exists> l. x \<longlonglongrightarrow> l\<close>
    using \<open>convergent x\<close>
    unfolding convergent_def by blast
  then obtain l where \<open>x \<longlonglongrightarrow> l\<close>
    by blast
  hence \<open>C \<le> l\<close>
    using \<open>\<forall> n \<ge> N. C \<le> x n\<close> Topological_Spaces.Lim_bounded2[where f = "x" and l="l" and N = "N"]
    by blast
  thus \<open>C \<le> lim x\<close>
    using \<open>x \<longlonglongrightarrow> l\<close> limI by auto    
qed

lemma lim_complex_of_real:
  fixes x::\<open>nat \<Rightarrow> real\<close>
  assumes \<open>convergent x\<close>
  shows \<open>lim (\<lambda> n. complex_of_real (x n)) = complex_of_real (lim x)\<close>
proof-
  have \<open>\<exists> l. x \<longlonglongrightarrow> l\<close>
    using \<open>convergent x\<close> unfolding convergent_def
    by blast
  then obtain l where
   \<open>x \<longlonglongrightarrow> l\<close>
    by blast
  moreover have \<open>(\<lambda>n. (0::real)) \<longlonglongrightarrow> 0\<close>
    by auto
  ultimately have \<open>(\<lambda>n. Complex (x n) ((\<lambda>n. (0::real)) n)) \<longlonglongrightarrow> Complex l 0\<close>
    using Complex.tendsto_Complex[where f = "x" and g = "(\<lambda>n. (0::real))"]
    by auto
  hence \<open>(\<lambda>n. Complex (x n) 0) \<longlonglongrightarrow> Complex l 0\<close>
    by simp
  moreover  have \<open>lim x = l\<close>
    using \<open>x \<longlonglongrightarrow> l\<close> limI by auto 
  ultimately have \<open>(\<lambda>n. Complex (x n) 0) \<longlonglongrightarrow> Complex (lim x) 0\<close>
    by simp
  hence \<open>lim (\<lambda>n. Complex (x n) 0) = Complex (lim x) 0\<close>
    using limI by auto
  thus ?thesis
    unfolding complex_of_real_def
    by blast
qed     

lemma lim_norm:
  fixes x::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>convergent x\<close>
  shows \<open>lim (\<lambda> n. norm (x n)) = norm (lim x)\<close>
proof-
  have \<open>\<exists> l. x \<longlonglongrightarrow> l\<close>
    using \<open>convergent x\<close> unfolding convergent_def by blast
  then obtain l where \<open>x \<longlonglongrightarrow> l\<close>
    by blast
  hence \<open>(\<lambda> n. norm (x n) ) \<longlonglongrightarrow> norm l\<close>
    by (simp add: tendsto_norm)
  moreover have \<open>lim x = l\<close>
    using  \<open>x \<longlonglongrightarrow> l\<close>
    by (simp add: limI) 
  ultimately show ?thesis
    by (simp add: limI) 
qed

lemma lim_sqrt:
  fixes x::\<open>nat \<Rightarrow> real\<close>
  assumes \<open>convergent x\<close>
  shows \<open>lim (\<lambda> n. sqrt (x n)) = sqrt (lim x)\<close>
proof-
  from \<open>convergent x\<close>
  have \<open>\<exists> l. x \<longlonglongrightarrow> l\<close>
    by (simp add: convergent_def)
  then obtain l where \<open>x \<longlonglongrightarrow> l\<close>
    by blast
  hence \<open>lim x = l\<close>
    by (simp add: limI)
  from \<open>x \<longlonglongrightarrow> l\<close>
  have \<open>(\<lambda> n.  sqrt (x n)) \<longlonglongrightarrow> sqrt l\<close>
    by (simp add: tendsto_real_sqrt)
  thus ?thesis using \<open>lim x = l\<close>
    by (simp add: limI) 
qed

lemma bounded_clinear_Cauchy:
  assumes \<open>Cauchy x\<close> and \<open>bounded_clinear f\<close>
  shows \<open>Cauchy (\<lambda> n. f (x n))\<close>
proof-
  have \<open>e>0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (f (x m) - f (x n)) < e\<close>
    for e
  proof-
    assume \<open>e > 0\<close>
    have \<open>\<exists> M. \<forall> t. norm (f t) \<le> norm t * M \<and> M > 0\<close>
      using assms(2) bounded_clinear.bounded_linear bounded_linear.pos_bounded
      by blast
    then obtain M where \<open>\<And> t. norm (f t) \<le> norm t * M\<close> and \<open>M > 0\<close>
      by blast
    have \<open>norm (f (x m - x n)) \<le> norm (x m - x n) * M\<close>
      for m n
      using  \<open>\<And> t. norm (f t) \<le> norm t * M\<close> by blast
    moreover have \<open>f (x m - x n) = f (x m) - f (x n)\<close>
      for m n
      using \<open>bounded_clinear f\<close> unfolding bounded_clinear_def
      by (simp add: complex_vector.linear_diff) 
    ultimately have f1: \<open>norm (f (x m) - f (x n)) \<le> norm (x m - x n) * M\<close>
      for m n
      by simp
    have \<open>e/M > 0\<close>
      by (simp add: \<open>0 < M\<close> \<open>0 < e\<close>)
    hence \<open>\<exists>K. \<forall>m\<ge>K. \<forall>n\<ge>K. norm (x m - x n) < e/M\<close>
      using Cauchy_iff assms(1) by blast
    then obtain K where \<open>\<And> m n. m\<ge>K \<Longrightarrow> n\<ge>K \<Longrightarrow> norm (x m - x n) < e/M\<close>
      by blast
    hence \<open>m \<ge> K \<Longrightarrow> n \<ge> K \<Longrightarrow> norm (f (x m) - f (x n)) < e\<close>
      for m n
    proof-
      assume \<open>m \<ge> K\<close> and \<open>n \<ge> K\<close>
      have \<open>norm (f (x m) - f (x n)) \<le> norm (x m -x n) * M\<close>
        by (simp add: f1)
      also have \<open>\<dots> < e/M * M\<close>
        using \<open>0 < M\<close> \<open>K \<le> m\<close> \<open>K \<le> n\<close> \<open>\<And>n m. \<lbrakk>K \<le> m; K \<le> n\<rbrakk> \<Longrightarrow> norm (x m - x n) < e / M\<close> linordered_semiring_strict_class.mult_strict_right_mono by blast
      also have \<open>\<dots> = e\<close>
        using \<open>0 < M\<close> by auto        
      finally show ?thesis by blast
    qed
    thus ?thesis
      by blast 
  qed
  thus ?thesis 
    unfolding Cauchy_def
    using dist_norm
    by smt
qed


lemma tendsto_finite_sum_induction:
  fixes X :: \<open>_ \<Rightarrow> _ \<Rightarrow> _::topological_monoid_add\<close>
  shows \<open>\<forall> T. card T = n \<and> finite T \<and> (\<forall> t. t\<in>T \<longrightarrow> (X t \<longlonglongrightarrow> L t)) \<longrightarrow> 
((\<lambda> n. (\<Sum>t\<in>T. X t n)) \<longlonglongrightarrow>  (\<Sum>t\<in>T. L t))\<close>
  proof (induction n)
  show "\<forall>T. card T = 0 \<and> finite T \<and> (\<forall>t. t \<in> T \<longrightarrow> X t \<longlonglongrightarrow> L t) \<longrightarrow> (\<lambda>n. \<Sum>t\<in>T. X t n) \<longlonglongrightarrow> sum L T"
  proof-
    have \<open>card T = 0 \<Longrightarrow> finite T \<Longrightarrow> (\<And> t. t \<in> T \<Longrightarrow> X t \<longlonglongrightarrow> L t) \<Longrightarrow> (\<lambda>n. \<Sum>t\<in>T. X t n) \<longlonglongrightarrow> sum L T\<close>
      for T
    proof-
      assume \<open>card T = 0\<close> and \<open>finite T\<close> and \<open>\<And> t. t \<in> T \<Longrightarrow> X t \<longlonglongrightarrow> L t\<close>
      have \<open>T = {}\<close>
        using \<open>card T = 0\<close> \<open>finite T\<close> by auto 
      hence \<open>(\<Sum>t\<in>T. X t n) = 0\<close>
        for n
        by simp
      hence \<open>(\<lambda>n. (\<Sum>t\<in>T. X t n)) \<longlonglongrightarrow> 0\<close>
        by auto
      moreover have \<open>sum L T = 0\<close>
        using \<open>T = {}\<close> by simp
      ultimately show ?thesis by simp
    qed
    thus ?thesis by blast
  qed
  show "\<forall>T. card T = Suc n \<and> finite T \<and> (\<forall>t. t \<in> T \<longrightarrow> X t \<longlonglongrightarrow> L t) \<longrightarrow> (\<lambda>n. \<Sum>t\<in>T. X t n) \<longlonglongrightarrow> sum L T"
    if "\<forall>T. card T = n \<and> finite T \<and> (\<forall>t. t \<in> T \<longrightarrow> X t \<longlonglongrightarrow> L t) \<longrightarrow> (\<lambda>n. \<Sum>t\<in>T. X t n) \<longlonglongrightarrow> sum L T"
    for n :: nat
  proof-
    have \<open>card T = Suc n \<Longrightarrow> finite T \<Longrightarrow> (\<And> t. t \<in> T \<Longrightarrow> X t \<longlonglongrightarrow> L t) \<Longrightarrow> (\<lambda>n. \<Sum>t\<in>T. X t n) \<longlonglongrightarrow> sum L T\<close>
      for T
    proof-
      assume \<open>card T = Suc n\<close> and \<open>finite T\<close> and \<open>\<And> t. t \<in> T \<Longrightarrow> X t \<longlonglongrightarrow> L t\<close>
      have \<open>\<exists> k K. k \<notin> K \<and> T = insert k K\<close>
        by (metis \<open>card T = Suc n\<close> card_le_Suc_iff le_Suc_eq)
      then obtain k K where \<open>k \<notin> K\<close> and \<open>T = insert k K\<close>
        by blast
      have \<open>finite K\<close>
        using \<open>T = insert k K\<close> \<open>finite T\<close> by auto
      moreover have \<open>card K = n\<close>
        using \<open>T = insert k K\<close> \<open>card T = Suc n\<close> \<open>k \<notin> K\<close> calculation by auto
      moreover have  \<open>\<And> t. t \<in> K \<Longrightarrow> X t \<longlonglongrightarrow> L t\<close>
        by (simp add: \<open>T = insert k K\<close> \<open>\<And>t. t \<in> T \<Longrightarrow> X t \<longlonglongrightarrow> L t\<close>)
      ultimately have \<open>(\<lambda>n. \<Sum>t\<in>K. X t n) \<longlonglongrightarrow> sum L K\<close>
        by (simp add: that)
      moreover have \<open>X k \<longlonglongrightarrow> L k\<close>
        by (simp add: \<open>T = insert k K\<close> \<open>\<And>t. t \<in> T \<Longrightarrow> X t \<longlonglongrightarrow> L t\<close>)
      ultimately have \<open>(\<lambda> n. X k n  + (\<Sum>t\<in>K. X t n)) \<longlonglongrightarrow> L k + sum L K\<close>
        using Limits.tendsto_add by auto
      moreover have \<open>X k n + (\<Sum>t\<in>K. X t n) = (\<Sum>t\<in>T. X t n)\<close>
        for n
        using \<open>T = insert k K\<close> \<open>finite K\<close> \<open>k \<notin> K\<close> by auto
      ultimately have \<open>(\<lambda> n. (\<Sum>t\<in>T. X t n)) \<longlonglongrightarrow> L k + sum L K\<close>
        by simp
      moreover have \<open> L k + sum L K = sum L T\<close>
        by (simp add: \<open>T = insert k K\<close> \<open>finite K\<close> \<open>k \<notin> K\<close>)
      ultimately show ?thesis
        by simp        
    qed
    thus ?thesis by blast
  qed
qed

lemma tendsto_finite_sum:
  fixes X :: \<open>_ \<Rightarrow> _ \<Rightarrow> _::topological_monoid_add\<close>
  assumes  \<open>\<And> t. t\<in>T \<Longrightarrow> X t \<longlonglongrightarrow> L t\<close> \<open>finite T\<close>
  shows \<open>(\<lambda> n. (\<Sum>t\<in>T. X t n)) \<longlonglongrightarrow>  (\<Sum>t\<in>T. L t)\<close>
  using assms tendsto_finite_sum_induction 
  by blast

hide_fact tendsto_finite_sum_induction

lemma infinitesimal_square:
  fixes x::hypreal
  shows \<open>x^2 \<in> Infinitesimal \<Longrightarrow> x \<in> Infinitesimal\<close>
  by (metis (full_types) NSA.Infinitesimal_mult_disj semiring_normalization_rules(29))


proposition unbounded_nsbounded_D:
  \<open>\<not>(bounded S) \<Longrightarrow> \<exists> x\<in>*s* S. x \<in> HInfinite\<close>
  for S::\<open>'a::real_normed_vector set\<close>
proof-
  assume \<open>\<not>(bounded S)\<close>
  hence \<open>\<And> M. \<exists> x\<in>S. norm x > M\<close>
    unfolding bounded_def by (metis dist_0_norm not_le_imp_less)
  hence \<open>\<And> M. \<exists> x\<in>*s* S. hnorm x > M\<close>
    by StarDef.transfer
  hence \<open>\<exists> x\<in>*s* S. hnorm x > \<omega>\<close>
    by blast
  thus ?thesis
    using HInfiniteI SReal_less_omega less_trans by blast
qed

proposition unbounded_nsbounded_I:
  \<open>\<exists> x\<in>*s* S. x \<in> HInfinite \<Longrightarrow> \<not>(bounded S)\<close>
  for S::\<open>'a::real_normed_vector set\<close>
proof(rule classical)
  assume \<open>\<exists> x\<in>*s* S. x \<in> HInfinite\<close> and \<open>\<not>( \<not>(bounded S))\<close>
  have \<open>bounded S\<close>
    using  \<open>\<not>( \<not>(bounded S))\<close> by blast
  hence \<open>bounded (insert 0 S)\<close>
    by simp
  from  \<open>\<exists> x\<in>*s* S. x \<in> HInfinite\<close>
  obtain x where \<open>x\<in>*s* S\<close> and \<open>x \<in> HInfinite\<close>
    by blast
  have \<open>x\<in>*s* (insert 0 S)\<close>
    using \<open>x\<in>*s* S\<close> by simp 
  moreover have \<open>0\<in>*s* (insert 0 S)\<close>
    by auto
  ultimately have \<open>(*f2* dist) 0 x \<in> HFinite\<close>
    using \<open>bounded (insert 0 S)\<close> bounded_nsbounded by blast
  moreover have \<open>(*f2* dist) 0 x = hnorm x\<close>
  proof-
    have \<open>\<forall> t::'a. dist 0 t = norm t\<close>
      using dist_norm  by auto
    hence \<open>\<forall> t::'a star. (*f2* dist) 0 t = hnorm t\<close>
      by StarDef.transfer      
    thus ?thesis by blast
  qed
  ultimately have \<open>hnorm x \<in> HFinite\<close>
    by simp
  hence \<open>x \<in> HFinite\<close>
    unfolding HFinite_def by auto   
  thus ?thesis using \<open>x \<in> HInfinite\<close>
    by (simp add: HInfinite_HFinite_iff) 
qed

proposition bounded_nsbounded_norm_D:
  \<open>bounded S \<Longrightarrow> \<forall> x\<in>*s* S. x \<in> HFinite\<close>
  for S::\<open>'a::real_normed_vector set\<close>
  using not_HFinite_HInfinite unbounded_nsbounded_I by blast

proposition bounded_nsbounded_norm_I:
  \<open>\<forall> x\<in>*s* S. x \<in> HFinite \<Longrightarrow> bounded S\<close>
  for S::\<open>'a::real_normed_vector set\<close>
  using HFinite_not_HInfinite unbounded_nsbounded_D by blast

proposition bounded_nsbounded_norm:
\<open>(\<forall> x\<in>*s* S. x \<in> HFinite) \<longleftrightarrow> bounded S\<close>
  for S::\<open>'a::real_normed_vector set\<close>
  using bounded_nsbounded_norm_I[where S = S] bounded_nsbounded_norm_D[where S = S] 
  by blast

unbundle no_nsa_notation

end

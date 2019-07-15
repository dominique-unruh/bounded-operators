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
    Unobtrusive_NSA
begin

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
    then show ?case
      by (metis funpow_0 of_nat_0 star_zero_def starfun_eq) 
  next
    case (Suc n)
    then show ?case
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


end

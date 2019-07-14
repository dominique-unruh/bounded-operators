(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Several definitions of convergence of families of operators.

Important results:
- completeness_real_bounded: A sufficient condition for the completeness of a sequence of
 bounded operators.
 
*)

theory Convergence_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL.Real_Vector_Spaces"
    "HOL-Analysis.Operator_Norm"
    Operator_Norm_Plus
    "HOL-Nonstandard_Analysis.Nonstandard_Analysis"

begin

section \<open>Pointwise convergence\<close>

definition strong_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>strong_convergence f l = ( \<forall> x. ( \<lambda> n. norm (f n x - l x) ) \<longlonglongrightarrow> 0 )\<close>

abbreviation strong_convergence_abbr:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  (\<open>((_)/ \<midarrow>strong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>strong\<rightarrow> l \<equiv> ( strong_convergence f l )\<close>

definition onorm_convergence::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>onorm_convergence f l = ( ( \<lambda> n. onorm (\<lambda> x. f n x - l x) ) \<longlonglongrightarrow> 0 )\<close>

section \<open>Convergence with respect to the operator norm\<close>

abbreviation onorm_convergence_abbr::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>  (\<open>((_)/ \<midarrow>onorm\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>onorm\<rightarrow> l \<equiv> ( onorm_convergence f l )\<close>

definition oCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>oCauchy f = ( \<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e )\<close>

section \<open>Uniform convergence on the unit sphere\<close>

definition ustrong_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close> where 
  \<open>ustrong_convergence f l = ( \<forall> e > 0. \<exists> N. \<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e )\<close>

abbreviation ustrong_convergence_abbr::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>  (\<open>((_)/ \<midarrow>ustrong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>ustrong\<rightarrow> l \<equiv> ( ustrong_convergence f l )\<close>

definition uCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>uCauchy f = ( \<forall> e > 0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e )\<close>

subsection \<open>Nonstandard analogs\<close>
subsubsection \<open>Nonstandard analog of uniform convergence on the unit sphere \<close>

text \<open>See theorem 7.12.2 of [goldblatt2012lectures]\<close>
definition nsustrong_convergence :: "(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector))
   \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  ("((_)/ \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (_))" [60, 60] 60) where
  \<comment> \<open>Nonstandard definition of uniform convergence of sequence on the unit sphere\<close>
  "f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l \<longleftrightarrow> 
( \<forall>N\<in>HNatInfinite. \<forall> x::'a star. hnorm x = 1 \<longrightarrow> (*f2* f) N x \<approx> (*f* l) x )"

lemma nsustrong_convergence_I: 
  \<open>( \<And>N. \<And> x. N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x  \<approx> (*f* l) x )
   \<Longrightarrow> f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l\<close> 
  by (simp add: nsustrong_convergence_def) 

lemma nsustrong_convergence_D: 
  \<open>f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l \<Longrightarrow> N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 
  \<Longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
  by (simp add: nsustrong_convergence_def)

lemma nsustrong_convergence_const:
  fixes k :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  assumes \<open>\<And> n::nat. f n = k\<close>
  shows \<open>f\<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S k\<close>
proof-
  have \<open>\<forall> n. \<forall> x::'a. norm x = 1 \<longrightarrow> f n x = k x\<close>
    using  \<open>\<And> n::nat. f n = k\<close> by auto
  hence \<open>\<forall> n. \<forall> x::'a star. hnorm x = 1 \<longrightarrow> (*f2* f) n x = (*f* k) x\<close>
    by transfer
  thus ?thesis using nsustrong_convergence_def
    by (simp add: nsustrong_convergence_def) 
qed

lemma nsustrong_convergence_add: "X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. X n t + Y n t)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. a t + b t)"
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close> and \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_D by blast 
  moreover have \<open>(*f2* Y) N x \<approx> (*f* b) x\<close>
    using \<open>Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_D by blast 
  ultimately have \<open>(*f2* X) N x + (*f2* Y) N x \<approx> (*f* a) x + (*f* b) x\<close>
    by (simp add: approx_add)
  moreover have \<open>(*f2* X) N x + (*f2* Y) N x = (*f2* (\<lambda>n t. X n t + Y n t)) N x\<close>
  proof-
    have \<open>\<forall> NN. \<forall> xx. X NN xx + Y NN xx = (\<lambda>n t. X n t + Y n t) NN xx\<close>
      by auto
    hence \<open>\<forall> NNN. \<forall> xxx. (*f2* X) NNN xxx + (*f2* Y) NNN xxx = (*f2* (\<lambda>n t. X n t + Y n t)) NNN xxx\<close>
      apply transfer
      by auto
    thus ?thesis
      by simp  
  qed
  moreover have \<open>(*f* a) x + (*f* b) x = (*f* (\<lambda>t. a t + b t)) x\<close>
    by simp
  ultimately show \<open>(*f2* (\<lambda>n t. X n t + Y n t)) N x \<approx> (*f* (\<lambda>t. a t + b t)) x\<close>
    by smt
qed

lemma nsustrong_convergence_add_const: "f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. f n t + b)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. a t + b)"
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
    by transfer
  hence  \<open>hnorm ((*f* a) x) < star_of (onorm a + 1)\<close>
    using \<open>hnorm x = 1\<close>
    by auto
  thus \<open>\<exists>xa\<in>\<real>. hnorm ((*f* a) x) < xa\<close> by auto
qed

lemma nsustrong_convergence_mult: "X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b
 \<Longrightarrow> bounded_linear a \<Longrightarrow> bounded_linear b 
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. X n t * Y n t)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. a t * b t)"
  for a b :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_algebra"
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
    and \<open>bounded_linear a\<close> and \<open>bounded_linear b\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_D by blast 
  moreover have \<open>(*f2* Y) N x \<approx> (*f* b) x\<close>
    using \<open>Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close> \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_D by blast 
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
      apply transfer
      by auto
    thus ?thesis
      by simp  
  qed
  moreover have \<open>(*f* a) x * (*f* b) x = (*f* (\<lambda>t. a t * b t)) x\<close>
    by simp
  ultimately show \<open>(*f2* (\<lambda>n t. X n t * Y n t)) N x \<approx> (*f* (\<lambda>t. a t * b t)) x\<close>
    by smt
qed

lemma nsustrong_convergence_minus: "X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. - X n t)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. - a t)"
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  from \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>hnorm x = 1\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    by (simp add: \<open>N \<in> HNatInfinite\<close> nsustrong_convergence_D)
  hence \<open>-(*f2* X) N x \<approx> -(*f* a) x\<close>
    by simp
  moreover have \<open>-(*f2* X) N x \<approx> (*f2* (\<lambda>n t. - X n t)) N x\<close>
  proof-
    have \<open>\<forall> NN. \<forall> xx. -( X) NN xx = ( (\<lambda>n t. - X n t)) NN xx\<close>
      by blast
    hence \<open>\<forall> NN. \<forall> xx. -(*f2* X) NN xx = (*f2* (\<lambda>n t. - X n t)) NN xx\<close>
      by transfer
    thus ?thesis by simp
  qed
  moreover have \<open>-(*f* a) x \<approx> (*f* (\<lambda>t. - a t)) x\<close>
    by simp
  ultimately show \<open>(*f2* (\<lambda>n t. - X n t)) N x \<approx> (*f* (\<lambda>t. - a t)) x\<close>
    using approx_trans3 by blast 
qed

lemma nsustrong_convergence_minus_cancel: "(\<lambda>n. (\<lambda> t. - X n t)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. - a t)
 \<Longrightarrow> X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a"
  by (drule nsustrong_convergence_minus) simp

lemma nsustrong_convergence_diff: "X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> Y \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. X n t - Y n t)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. a t - b t)"
  using nsustrong_convergence_add [of X a "- Y" "- b"]
  by (simp add: nsustrong_convergence_minus fun_Compl_def)

lemma nsustrong_convergence_diff_const: "f  \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. f n t - b)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. a t - b)"
  by (simp add: nsustrong_convergence_diff nsustrong_convergence_const)

lemma nsustrong_convergence_inverse: "X  \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> 
 bounded_linear a \<Longrightarrow> \<exists> e > 0. \<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e
 \<Longrightarrow> (\<lambda>n. (\<lambda> t. inverse (X n t) )) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. inverse (a t))"
  for a :: "'a::real_normed_vector \<Rightarrow>'b::real_normed_div_algebra"
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>N \<in> HNatInfinite\<close>
    and \<open>hnorm x = 1\<close> and \<open>\<exists> e > 0. \<forall> t. norm t = 1 \<longrightarrow> norm (a t) > e\<close> and \<open>bounded_linear a\<close>
  from \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> nsustrong_convergence_def by blast
  moreover have \<open>inverse ((*f2* X) N x) \<approx> (*f2* (\<lambda>n t. inverse (X n t))) N x\<close>
  proof-                            
    have \<open>\<forall> NN. \<forall> xx. inverse ( X NN xx) = ( (\<lambda>n t. inverse (X n t))) NN xx\<close>
      by blast
    hence \<open>\<forall> NN. \<forall> xx. inverse ((*f2* X) NN xx) = (*f2* (\<lambda>n t. inverse (X n t))) NN xx\<close>
      by transfer
    thus ?thesis
      by simp 
  qed
  moreover have \<open>inverse ((*f* a) x) \<approx> (*f* (\<lambda>t. inverse (a t))) x\<close>
  proof-
    have \<open>\<forall> xx. inverse (a xx) = (\<lambda>t. inverse (a t)) xx\<close>
      by simp
    hence \<open>\<forall> xx. inverse ((*f* a) xx) = (*f* (\<lambda>t. inverse (a t))) xx\<close>
      by transfer
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
          by transfer
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

lemma nsustrong_convergence_norm: \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S  a \<Longrightarrow>
 (\<lambda>n. (\<lambda> t. norm (X n t))) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S (\<lambda> t. norm (a t))\<close>
proof(rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S  a\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  have \<open>(*f2* X) N x \<approx> (*f* a) x\<close>
    using  \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S  a\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
      nsustrong_convergence_D by blast
  moreover have  \<open>hnorm ((*f2* X) N x) \<approx> (*f2* (\<lambda>n t. norm (X n t))) N x\<close>
  proof-
    have \<open>\<forall> NN. \<forall> xx. norm ( X NN xx) = ( (\<lambda>n t. norm (X n t))) NN xx\<close>
      by blast
    hence \<open>\<forall> NN. \<forall> xx. hnorm ( (*f2* X) NN xx) = (*f2* (\<lambda>n t. norm (X n t))) NN xx\<close>
      by transfer
    thus ?thesis by simp
  qed
  moreover have \<open>hnorm ((*f* a) x) \<approx> (*f* (\<lambda>t. norm (a t))) x\<close>
  proof-
    have \<open>\<forall> xx. norm (a xx) = (\<lambda>t. norm (a t)) xx\<close>
      by blast
    hence \<open>\<forall> xx. hnorm ((*f* a) xx) = (*f* (\<lambda>t. norm (a t))) xx\<close>
      by transfer
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

lemma nsustrong_convergence_unique: "X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a \<Longrightarrow> X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b
 \<Longrightarrow> linear a  \<Longrightarrow> linear b \<Longrightarrow> a = b"
proof-
  assume \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close> and \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close> and \<open>linear a\<close> and \<open>linear b\<close>
  have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow>(*f2* X) N x \<approx> (*f* a) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S a\<close>
    by (simp add: nsustrong_convergence_D)
  moreover have \<open>\<forall> N\<in>HNatInfinite. \<forall> x. hnorm x = 1 \<longrightarrow> (*f2* X) N x \<approx> (*f* b) x\<close>
    using \<open>X \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S b\<close>
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
  shows "((\<lambda>n. f (Suc n)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l) \<longleftrightarrow> (f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l)"
proof
  assume *: "f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  show "(\<lambda>n. f (Suc n)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  proof (rule nsustrong_convergence_I)
    fix N and x::\<open>'a star\<close>
    assume "N \<in> HNatInfinite" and \<open>hnorm x = 1\<close>
    hence "(*f2* f) (N + 1) x \<approx> (*f* l) x"
      by (simp add: HNatInfinite_add nsustrong_convergence_D *)
    moreover have \<open>(*f2* (\<lambda> n. f (Suc n))) N x = (*f2* f) (N + 1) x\<close>
    proof-
      have \<open>\<forall> NN. \<forall> xx. (\<lambda> n. f (Suc n)) NN xx =  f (NN + 1) xx\<close>
        by simp
      hence \<open>\<forall> NN. \<forall> xx. (*f2* (\<lambda> n. f (Suc n))) NN xx =  (*f2* f) (NN + 1) xx\<close>
        by transfer
      thus ?thesis
        by simp 
    qed 
    ultimately show \<open>(*f2* (\<lambda>k. f (Suc k))) N x \<approx> (*f* l) x\<close> by simp
  qed
next
  assume *: "(\<lambda>n. f(Suc n)) \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  show  "f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l"
  proof (rule nsustrong_convergence_I)
    fix N and x::\<open>'a star\<close>
    assume "N \<in> HNatInfinite" and \<open>hnorm x = 1\<close>
    hence "(*f2* (\<lambda>n. f (Suc n))) (N - 1) x \<approx> (*f* l) x"
      using * HNatInfinite_diff nsustrong_convergence_D by fastforce
    moreover have \<open>(*f2* (\<lambda>n. (f (Suc n) ))) (N - 1) x = (*f2* f) N x\<close>
    proof-
      have \<open>\<forall> NN. \<forall> xx.  NN \<ge> 1 \<longrightarrow> (\<lambda>n. (f (Suc n) )) (NN - 1) xx =  f NN xx\<close>
        by simp
      hence \<open>\<forall> NN. \<forall> xx.  NN \<ge> 1 \<longrightarrow> (*f2* (\<lambda>n. (f (Suc n)))) (NN - 1) xx =  (*f2* f) NN xx\<close>
        by transfer
      thus ?thesis
        using \<open>N \<in> HNatInfinite\<close> one_le_HNatInfinite by auto 
    qed
    ultimately show "(*f2* f) N x \<approx> (*f* l) x"
      by simp
  qed
qed

lemma ustrong_convergence_nsustrong_convergence:
  fixes l::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  assumes \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
  shows \<open>f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l\<close>
proof (rule nsustrong_convergence_I)
  fix N and x::\<open>'a star\<close>
  assume \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  have \<open>(*f2* f) N x - (*f* l) x \<in> Infinitesimal\<close>
  proof (rule InfinitesimalI2)
    fix r :: real
    assume \<open>0 < r\<close>
    have \<open>\<exists> no. \<forall> n \<ge> no. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < r\<close>
      using \<open>f \<midarrow>ustrong\<rightarrow> l\<close>  \<open>0 < r\<close> ustrong_convergence_def by auto 
    then obtain no where \<open>\<forall> n \<ge> no. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> no. \<forall> x. norm x = 1 \<longrightarrow> norm ( f n x - l x) < r\<close>
      by blast
    hence \<open>\<forall> n \<ge> hypnat_of_nat no. \<forall> x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) n x - (*f* l) x) < hypreal_of_real r\<close>
      by transfer
    thus \<open>hnorm ((*f2* f) N x- (*f* l) x) < hypreal_of_real r\<close>
      using star_of_le_HNatInfinite \<open>N \<in> HNatInfinite\<close>
      by (simp add: \<open>hnorm x = 1\<close>)
  qed
  thus \<open>(*f2* f) N x \<approx>  (*f* l) x\<close>
    by (simp only: approx_def)
qed

lemma ustrong_convergence_I: \<open>(\<And>r. 0 < r \<Longrightarrow>
\<exists> no. \<forall> n \<ge> no. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < r) \<Longrightarrow> f \<midarrow>ustrong\<rightarrow> l\<close>
  for l :: "'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector"
  by (simp add: ustrong_convergence_def)

lemma nsustrong_convergence_ustrong_convergence:
  fixes l::\<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close> and f::\<open>nat \<Rightarrow> ('a \<Rightarrow> 'b)\<close>
  assumes \<open>f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l\<close>
  shows \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
proof (rule ustrong_convergence_I)
  fix r :: real
  assume \<open>r > (0::real)\<close>
  from \<open>f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S l\<close>
  have \<open>\<forall>n\<in>HNatInfinite. 
  \<forall>x. hnorm x = 1 \<longrightarrow> (*f2* f) n x \<approx> (*f* l) x\<close>
    unfolding nsustrong_convergence_def by blast
  hence \<open>\<forall>n\<in>HNatInfinite.
       \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
    by (simp add: InfinitesimalD2 Infinitesimal_approx_minus \<open>0 < r\<close>)
  have \<open>\<exists> no. \<forall>n \<ge> no.
       \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
  proof-
    have \<open>n \<ge> whn \<Longrightarrow>
       \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
      for n
      using HNatInfinite_upward_closed HNatInfinite_whn \<open>\<forall>n\<in>HNatInfinite. \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ((*f2* f) n x - (*f* l) x) < hypreal_of_real r\<close> by blast     
    thus ?thesis by blast
  qed
  thus \<open>\<exists> no. \<forall>n \<ge> no. \<forall>x. norm x = 1 \<longrightarrow> norm ( f n x - l x ) < r\<close>
    by transfer
qed

proposition ustrong_convergence_ustrong_convergence_iff:
  \<open>f \<midarrow>ustrong\<rightarrow> L \<longleftrightarrow> f \<midarrow>ustrong\<rightarrow>\<^sub>N\<^sub>S L\<close>
  using nsustrong_convergence_ustrong_convergence ustrong_convergence_nsustrong_convergence by blast

subsubsection \<open>Nonstandard analog of Cauchy property on the unit sphere \<close>

definition uNSCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>uNSCauchy f \<longleftrightarrow> ( \<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. 
    \<forall> x. hnorm x = 1 \<longrightarrow> (*f2* f) N x \<approx> (*f2* f) M x )\<close> 

lemma Cauchy_uNSCauchy:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close>
  assumes \<open>uCauchy f\<close>
  shows \<open>uNSCauchy f\<close>
proof-
  from \<open>uCauchy f\<close>
  have \<open>\<forall>e>0. \<exists>K. \<forall>m\<ge>K. \<forall>n\<ge>K.
     \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
    unfolding uCauchy_def
    by blast
  hence \<open>N\<in>HNatInfinite \<Longrightarrow> M\<in>HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x \<approx> (*f2* f) M x\<close>
    for N M x
  proof-
    assume \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close> and \<open>hnorm x = 1\<close>
    have \<open>e \<in> \<real> \<Longrightarrow>  e > 0 \<Longrightarrow> hnorm ((*f2* f) N x - (*f2* f) M x) < e\<close>
      for e
    proof-
      assume \<open>e \<in> \<real>\<close> and \<open>e > 0\<close>
      have \<open>\<exists> d. e = hypreal_of_real d\<close>
        using  \<open>e \<in> \<real>\<close>
        by (simp add: SReal_iff)
      then obtain d where \<open>e = hypreal_of_real d\<close>
        by blast
      have \<open>d > 0\<close> using \<open>e = hypreal_of_real d\<close> \<open>e > 0\<close>
        by simp
      have \<open>\<exists>K. \<forall>m\<ge>K. \<forall>n\<ge>K. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < d\<close>
        by (simp add: \<open>0 < d\<close> \<open>\<forall>e>0. \<exists>K. \<forall>m\<ge>K. \<forall>n\<ge>K. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>)
      then obtain K::nat where \<open>\<forall>m\<ge>K. \<forall>n\<ge>K. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < d\<close>
        by blast
      hence \<open>\<forall>m \<ge> hypnat_of_nat K. \<forall>n \<ge> hypnat_of_nat K. 
          \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ((*f2* f) m x - (*f2* f) n x) < hypreal_of_real d\<close>
        by transfer
      hence \<open>\<forall>m \<ge> hypnat_of_nat K. \<forall>n \<ge> hypnat_of_nat K. 
          \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ((*f2* f) m x - (*f2* f) n x) < e\<close>
        using  \<open>e = hypreal_of_real d\<close> by blast
      hence \<open>\<forall>x. hnorm x = 1 \<longrightarrow> hnorm ((*f2* f) N x - (*f2* f) M x) < e\<close>
        using \<open>N\<in>HNatInfinite\<close> \<open>M\<in>HNatInfinite\<close>
        by (simp add: star_of_le_HNatInfinite) 
      thus ?thesis using \<open>hnorm x = 1\<close> by blast
    qed
    thus ?thesis
      using InfinitesimalI bex_Infinitesimal_iff by auto 
  qed
  thus ?thesis
    by (simp add: uNSCauchy_def) 
qed

lemma uNSCauchy_Cauchy:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close>
  assumes \<open>uNSCauchy f\<close>
  shows \<open>uCauchy f\<close>
proof-
  have \<open>e>0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
    for e
  proof-
    assume \<open>e>0\<close>
    have \<open>\<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. 
      \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) N x - (*f2* f) M x ) \<in> Infinitesimal\<close>
      using Infinitesimal_approx_minus Infinitesimal_hnorm_iff assms uNSCauchy_def by blast
    hence \<open>\<forall>e\<in>\<real>. e > 0 \<longrightarrow> ( \<forall>N\<in>HNatInfinite. \<forall>M\<in>HNatInfinite. 
      \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) N x - (*f2* f) M x ) < e )\<close>
      by (simp add: Infinitesimal_less_SReal2)
    hence \<open>\<forall>e\<in>\<real>. e > 0 \<longrightarrow> ( \<forall>N \<ge> whn. \<forall> M \<ge> whn. 
      \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) N x - (*f2* f) M x ) < e )\<close>
      using HNatInfinite_upward_closed HNatInfinite_whn by blast
    hence \<open>\<forall>e\<in>\<real>. e > 0 \<longrightarrow> ( \<exists> K. \<forall>N \<ge> K. \<forall> M \<ge> K. 
      \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) N x - (*f2* f) M x ) < e )\<close>
      by blast
    hence \<open>\<exists> K. \<forall>N \<ge> K. \<forall> M \<ge> K. 
      \<forall>x. hnorm x = 1 \<longrightarrow> hnorm ( (*f2* f) N x - (*f2* f) M x ) < hypreal_of_real e\<close>
      by (simp add: \<open>0 < e\<close>)
    thus \<open>\<exists> K. \<forall>N \<ge> K. \<forall> M \<ge> K. 
      \<forall>x. norm x = 1 \<longrightarrow> norm ( f N x - f M x ) < e\<close>
      by transfer
  qed
  thus ?thesis unfolding uCauchy_def by blast
qed

proposition Cauchy_uNSCauchy_iff:
  \<open>uCauchy f \<longleftrightarrow> uNSCauchy f\<close>
  using Cauchy_uNSCauchy uNSCauchy_Cauchy by auto


section \<open>Relationships among the different kind of convergence\<close>

lemma ustrong_onorm:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close>
    and l::\<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>\<forall>n. bounded_linear (f n)\<close> and \<open>bounded_linear l\<close>
    and \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
  shows \<open>f \<midarrow>onorm\<rightarrow> l\<close> 
proof-
  have \<open>(\<lambda>n. onorm (\<lambda>x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
  proof-
    have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N.  onorm (\<lambda>x. f n x - l x) \<le> e\<close>
      for e
    proof-
      assume \<open>e > 0\<close>
      hence \<open>\<exists> N. \<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
        using \<open>f \<midarrow>ustrong\<rightarrow> l\<close> unfolding ustrong_convergence_def
        by blast
      then obtain N where \<open>\<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
        by blast
      have \<open>bounded_linear g \<Longrightarrow> \<exists> x. norm x = 1 \<and> onorm g \<le> norm (g x) + inverse (real (Suc m))\<close>
        for x::'a and g::\<open>'a \<Rightarrow> 'b\<close> and m :: nat
      proof-
        assume \<open>bounded_linear g\<close>
        hence \<open>onorm g = Sup {norm (g x) | x. norm x = 1}\<close>
          using onorm_sphere by blast
        have \<open>\<exists> t \<in> {norm (g x) | x. norm x = 1}. onorm g \<le>  t + inverse (real (Suc m))\<close>
        proof-
          have \<open>ereal (inverse (real (Suc m))) > 0\<close>
            by simp
          moreover have \<open>\<bar>Sup {ereal (norm (g x)) | x. norm x = 1}\<bar> \<noteq> \<infinity>\<close>
          proof-
            have \<open>\<exists> M::real. \<forall> x. norm x = 1 \<longrightarrow>  (norm (g x))  \<le> M\<close>
              by (metis \<open>bounded_linear g\<close>  bounded_linear.bounded)
            then obtain M::real where \<open>\<forall> x. norm x = 1 \<longrightarrow>  (norm (g x))  \<le> M\<close>
              by blast
            hence \<open>\<forall> x. norm x = 1 \<longrightarrow> ereal (norm (g x)) \<le> M\<close>
              by simp
            hence \<open>t \<in> {ereal (norm (g x)) | x. norm x = 1} \<Longrightarrow> t \<le> M\<close>
              for t
              by blast
            hence \<open>Sup {ereal (norm (g x)) | x. norm x = 1} \<le> M\<close>
              using Sup_least by blast
            moreover have \<open>Sup { ereal (norm (g x))  | x. norm x = 1} \<ge> 0\<close>
            proof-
              have \<open>t \<in> { ereal (norm (g x))  | x. norm x = 1} \<Longrightarrow> t \<ge> 0\<close>
                for t
                by auto                
              moreover have \<open>{ ereal (norm (g x))  | x. norm x = 1} \<noteq> {}\<close>
              proof-
                have \<open>\<exists> x::'a.  norm x = 1\<close>
                  using le_numeral_extra(1) vector_choose_size by blast
                thus ?thesis by blast
              qed
              ultimately show ?thesis
                by (meson less_eq_Sup) 
            qed
            ultimately have \<open>\<bar> Sup { ereal (norm (g x))  | x. norm x = 1} \<bar> \<le> M\<close>
              by simp
            thus ?thesis by auto
          qed
          moreover have \<open>{ereal(norm (g x)) | x. norm x = 1} \<noteq> {}\<close>
            by (metis Sup_empty bot.extremum_strict calculation(2) less_ereal.simps(1) lt_ex not_infty_ereal)
          ultimately have \<open>\<exists> t \<in> {ereal(norm (g x)) | x. norm x = 1}. Sup {ereal(norm (g x)) | x. norm x = 1}
               - ereal (inverse (real (Suc m))) < t\<close>
            by (rule Sup_ereal_close)
          hence \<open>\<exists> t \<in> {(norm (g x)) | x. norm x = 1}. Sup {ereal(norm (g x)) | x. norm x = 1}
               - (inverse (real (Suc m))) < t\<close>
            by auto
          then obtain t::real where \<open>t \<in> {(norm (g x)) | x. norm x = 1}\<close> 
            and \<open>Sup {ereal(norm (g x)) | x. norm x = 1}
               - (inverse (real (Suc m))) < t\<close>
            by blast
          have \<open>onorm g = Sup {ereal(norm (g x)) | x. norm x = 1}\<close>
            using \<open>onorm g = Sup {norm (g x) | x. norm x = 1}\<close>
            by simp
          also have \<open>... < t + (inverse (real (Suc m)))\<close>
            apply auto
            using \<open>Sup {ereal(norm (g x)) | x. norm x = 1} - (inverse (real (Suc m))) < t\<close>
          proof auto
            assume \<open>Sup {ereal (norm (g x)) |x. norm x = 1} - ereal (inverse (1 + real m))
                  < ereal t\<close>
            moreover have \<open>\<bar> ereal (inverse (1 + real m)) \<bar> \<noteq> \<infinity>\<close>
              by auto
            ultimately have \<open>Sup {ereal (norm (g x)) |x. norm x = 1}
                  < ereal t + ereal (inverse (1 + real m))\<close>
              using ereal_minus_less by simp               
            hence \<open>Sup {ereal (norm (g x)) |x. norm x = 1}
                  < t + (inverse (1 + real m))\<close>
              by simp
            moreover have \<open>Sup {ereal (norm (g x)) |x. norm x = 1} = 
                    Sup {(norm (g x)) |x. norm x = 1}\<close>
            proof-
              have \<open>{ereal (norm (g x)) |x. norm x = 1} = 
                    {(norm (g x)) |x. norm x = 1}\<close>
                by simp
              hence \<open>y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<in> {(norm (g x)) |x. norm x = 1}\<close>
                for y
                by simp
              moreover have \<open>{ (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (metis \<open>t \<in> {norm (g x) |x. norm x = 1}\<close> empty_iff)                
              moreover have \<open>bdd_above { (norm (g x)) |x. norm x = 1}\<close>
                by (metis (mono_tags, lifting)  \<open>bounded_linear g\<close> norm_set_bdd_above_eq1) 
              ultimately have \<open>y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {(norm (g x)) |x. norm x = 1}\<close>
                for y
                by (smt cSup_upper ereal_less_eq(3) mem_Collect_eq)
              from \<open>{ereal (norm (g x)) |x. norm x = 1} = 
                    {(norm (g x)) |x. norm x = 1}\<close>
              have \<open>y \<in> {(norm (g x)) |x. norm x = 1} \<Longrightarrow>
                   y \<in> {ereal (norm (g x)) |x. norm x = 1}\<close>
                for y
                by simp
              moreover have \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (metis \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>)                
              moreover have \<open>bdd_above {ereal (norm (g x)) |x. norm x = 1}\<close>
                by (metis (no_types, lifting) bdd_above_top) 
              ultimately have \<open>y \<in> {(norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                for y
                by (simp add: Sup_upper)
              from  \<open>\<And> y. y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {(norm (g x)) |x. norm x = 1}\<close>
              have \<open>Sup {ereal (norm (g x)) |x. norm x = 1} \<le>  Sup {(norm (g x)) |x. norm x = 1}\<close>
                using \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (meson cSup_least)
              have \<open>(Sup { (norm (g x)) |x. norm x = 1}) \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close> 
              proof-
                define X::\<open>ereal set\<close> where \<open>X = {norm (g x) |x. norm x = 1}\<close>
                define z::ereal where \<open>z = Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                have \<open>X \<noteq> {}\<close>
                  unfolding X_def
                  using \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close> by blast 
                moreover have \<open>\<And>x. x \<in> X \<Longrightarrow> x \<le> z\<close>
                  unfolding X_def z_def
                  by (simp add: Sup_upper)
                ultimately have \<open>Sup X \<le> z\<close>
                  by (rule cSup_least)
                hence \<open>Sup X \<le>  Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  unfolding z_def 
                  by auto
                hence \<open>real_of_ereal (Sup {norm (g x) |x. norm x = 1}) \<le>  Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  unfolding X_def 
                  by auto
                thus ?thesis
                  by (smt \<open>\<And>y. y \<in> {norm (g x) |x. norm x = 1} \<Longrightarrow> ereal y \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close> \<open>\<bar>Sup {ereal (norm (g x)) |x. norm x = 1}\<bar> \<noteq> \<infinity>\<close> \<open>{norm (g x) |x. norm x = 1} \<noteq> {}\<close> cSup_least ereal_le_real_iff) 
              qed
              show ?thesis 
                using \<open>(Sup {(norm (g x)) |x. norm x = 1}) \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  \<open>Sup {ereal (norm (g x)) |x. norm x = 1} \<le>  Sup {(norm (g x)) |x. norm x = 1}\<close>
                by auto
            qed
            ultimately show \<open>Sup {norm (g x) |x. norm x = 1} < t + inverse (1 + real m)\<close>
              by simp
          qed
          finally have \<open>(onorm g) < t + (inverse (real (Suc m)))\<close>
            by blast
          thus ?thesis
            using \<open>t \<in> {norm (g x) |x. norm x = 1}\<close> by auto             
        qed
        thus ?thesis by auto
      qed
      hence \<open>\<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
        for n and m::nat
        using \<open>\<forall>n. bounded_linear (f n)\<close>
        by (simp add: assms(2) bounded_linear_sub)
      hence \<open>n \<ge> N \<Longrightarrow>  onorm (\<lambda> x. f n x - l x) \<le> e\<close>
        for n
      proof-
        assume \<open>n \<ge> N\<close>
        hence  \<open>\<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          using \<open>\<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          by blast
        have  \<open>\<forall> m. \<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
          using \<open>\<And> m. \<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
          by blast
        hence  \<open>\<exists> x. \<forall> m. norm (x m) = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m))\<close>
          using choice by simp  
        then obtain x where \<open>norm (x m) = 1\<close> 
          and \<open>onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m))\<close>
        for m::nat
          by blast          
        have \<open>\<forall> m. onorm (\<lambda> x. f n x - l x) < e + inverse (real (Suc m))\<close>
          using \<open>\<And> m. norm (x m) = 1\<close>  \<open>\<And> m. onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m)) \<close>
            \<open>\<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          by smt
        have \<open>onorm (\<lambda> x. f n x - l x) \<le> e\<close>
        proof(rule classical)
          assume \<open>\<not>(onorm (\<lambda> x. f n x - l x) \<le> e)\<close>
          hence \<open>e < onorm (\<lambda> x. f n x - l x)\<close>
            by simp
          hence \<open>0 < onorm (\<lambda> x. f n x - l x) - e\<close>
            by simp
          hence \<open>\<exists> n0. inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close>
            by (rule Archimedean_Field.reals_Archimedean)
          then obtain n0 where \<open>inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close>
            by blast
          have \<open>\<forall> m. onorm (\<lambda> x. f n x - l x) - e < inverse (real (Suc m))\<close>
            by (smt \<open>\<forall>m. onorm (\<lambda>x. f n x - l x) < e + inverse (real (Suc m))\<close>)
          hence \<open>\<forall> m. inverse (real (Suc n0)) < inverse (real (Suc m))\<close>
            using  \<open>inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close> by smt
          hence \<open>inverse (real (Suc n0)) < inverse (real (Suc n0))\<close>
            by blast
          thus ?thesis by blast
        qed
        thus ?thesis by blast 
      qed
      thus ?thesis by blast
    qed
    hence \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N. norm ( onorm (\<lambda>x. f n x - l x) ) \<le> e\<close>
      for e
    proof-
      assume \<open>e > 0\<close>
      hence \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        using  \<open>\<And> e. e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N.  onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        by blast
      then obtain N where \<open>\<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        by blast
      have  \<open>\<forall> n \<ge> N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close>
      proof-
        have \<open>n \<ge> N \<Longrightarrow> norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close>
          for n
        proof-
          assume \<open>n \<ge> N\<close>
          hence \<open>onorm (\<lambda>x. f n x - l x) \<le> e\<close>
            using \<open>\<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close> by blast
          moreover have \<open>onorm (\<lambda>x. f n x - l x) \<ge> 0\<close>
            by (simp add: assms(1) assms(2) bounded_linear_sub onorm_pos_le)            
          ultimately show ?thesis by simp
        qed
        thus ?thesis by blast
      qed
      thus ?thesis by blast 
    qed
    have \<open>0 < e \<Longrightarrow>
      \<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) < e\<close>
      for e::real
    proof-
      assume \<open>0 < e\<close>
      hence \<open>e/2 < e\<close>
        by simp
      have \<open>0 < e/2\<close>
        using \<open>0 < e\<close> by simp
      hence \<open>\<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e/2\<close>
        using \<open>\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close> by blast
      thus ?thesis using \<open>e/2 < e\<close> by fastforce
    qed
    thus ?thesis by (simp add: LIMSEQ_I) 
  qed
  thus ?thesis unfolding onorm_convergence_def by blast
qed


lemma oCauchy_uCauchy:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close>
  assumes \<open>\<forall>n. bounded_linear (f n)\<close>
    and \<open>oCauchy f\<close>
  shows \<open>uCauchy f\<close>
proof-
  have  \<open>e > 0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
    for e::real
  proof-
    assume \<open>e > 0\<close>
    moreover have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
      using \<open>oCauchy f\<close> unfolding oCauchy_def by blast
    ultimately have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
      using \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
      by blast
    then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
      by blast
    have \<open>m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
      for m n::nat
    proof-
      assume \<open>m \<ge> M\<close>
      moreover assume \<open>n \<ge> M\<close>
      ultimately have \<open>onorm (\<lambda>x. f m x - f n x) < e\<close>
        by (simp add: \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>)
      moreover have \<open>norm x = 1 \<Longrightarrow>  norm (f m x - f n x) \<le> onorm (\<lambda>x. f m x - f n x)\<close>
        for x
      proof-
        assume \<open>norm x = 1\<close>
        moreover have \<open>norm (f m x - f n x) \<le> onorm (\<lambda>x. f m x - f n x) * norm x\<close>
          using assms(1) bounded_linear_sub onorm by blast          
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis by smt
    qed
    thus ?thesis by blast
  qed
  thus ?thesis
    by (simp add: uCauchy_def) 
qed

lemma uCauchy_ustrong:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>\<And> n. bounded_linear (f n)\<close> and \<open>uCauchy f\<close> 
  shows \<open>\<exists> l::'a\<Rightarrow>'b. bounded_linear l \<and> f \<midarrow>ustrong\<rightarrow> l\<close>
proof-
  have \<open>\<exists> l::'a\<Rightarrow>'b. f \<midarrow>ustrong\<rightarrow> l\<close>
  proof-
    have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
      using \<open>uCauchy f\<close> unfolding uCauchy_def by blast
    hence \<open>norm x = 1 \<Longrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (f m x - f n x) < e)\<close>
      for x
      by blast
    hence \<open>norm x = 1 \<Longrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m x) (f n x) < e)\<close>
      for x
      by (simp add: dist_norm)    
    hence \<open>norm x = 1 \<Longrightarrow> Cauchy (\<lambda> n. f n x)\<close>
      for x
      using Cauchy_def by blast
    hence \<open>norm x = 1 \<Longrightarrow> convergent (\<lambda> n. f n x)\<close>
      for x
      by (simp add: Cauchy_convergent_iff)
    hence \<open>norm x = 1 \<Longrightarrow> \<exists> l. (\<lambda> n. f n x) \<longlonglongrightarrow> l\<close>
      for x
      by (simp add: convergentD)
    hence \<open>\<forall> x. \<exists> l. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l\<close>
      by blast
    hence \<open>\<exists> l. \<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
      by metis
    then obtain l where \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close> by blast
    have \<open>e > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<forall>x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
      for e::real
    proof-
      assume \<open>e > 0\<close>
      hence \<open>e/2 > 0\<close>
        by simp
      hence \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. dist (f n x) (l x) < e/2)\<close>
        using  \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
        by (meson LIMSEQ_iff_nz)
      have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x)  (f n x) < e/2\<close>
        using  \<open>e/2 > 0\<close> \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
        by (metis dist_norm)
      then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (f n x) < e/2\<close>
        by blast
      have \<open>m \<ge> M \<Longrightarrow> \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (l x) < e\<close>
        for m
      proof-
        assume \<open>m \<ge> M\<close>
        have \<open>norm x = 1 \<Longrightarrow> dist (f m x) (l x) < e\<close>
          for x
        proof-
          assume \<open>norm x = 1\<close>
          have \<open>dist (f m x) (l x) \<le> dist (f m x) (f n x) + dist (l x) (f n x)\<close>
            for n
            by (simp add: dist_triangle2)
          moreover have \<open>n \<ge> M \<Longrightarrow> dist (f m x) (f n x) < e/2\<close>
            for n
            using \<open>M \<le> m\<close> \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (f n x) < e / 2\<close> \<open>norm x = 1\<close> by blast
          moreover have \<open>\<exists> N. \<forall> n \<ge> N. dist (l x) (f n x) < e/2\<close>
          proof-
            have \<open>\<exists> N. \<forall> n \<ge> N. dist (f n x) (l x) < e/2\<close>
              using \<open>e/2 > 0\<close> \<open>\<forall>x. norm x = 1 \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. dist (f n x) (l x) < e / 2)\<close> \<open>norm x = 1\<close> by auto 
            thus ?thesis
              by (simp add: dist_commute) 
          qed
          ultimately show ?thesis
            by (meson dist_triangle_half_l le_add1 le_add2) 
        qed
        thus ?thesis by blast
      qed
      thus ?thesis
        by (metis dist_norm) 
    qed
    thus ?thesis unfolding ustrong_convergence_def by blast
  qed
  then obtain s where \<open>f \<midarrow>ustrong\<rightarrow> s\<close> by blast
  define l::\<open>'a \<Rightarrow> 'b\<close> where \<open>l x = (norm x) *\<^sub>R s ((inverse (norm x)) *\<^sub>R x)\<close>
    for x::'a
  have \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
    using l_def \<open>f \<midarrow>ustrong\<rightarrow> s\<close> 
    unfolding l_def
    unfolding ustrong_convergence_def
    by simp
  moreover have \<open>bounded_linear l\<close>
  proof-
    have \<open>(\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
      for x
    proof(cases \<open> x = 0\<close>)
      case True
      have \<open>(\<lambda> n. f n x) \<longlonglongrightarrow> 0\<close>
      proof-
        have \<open>f n x = (0::'b)\<close>
          for n
          using \<open>\<And> n. bounded_linear (f n)\<close>
          by (simp add: True linear_simps(3))
        moreover  have \<open>(\<lambda> n. (0::'b)) \<longlonglongrightarrow> 0\<close>
          by simp            
        ultimately show ?thesis by simp
      qed
      moreover have \<open>l x = 0\<close>
      proof-
        have \<open>norm x = 0\<close>
          using \<open>x = 0\<close> by simp
        thus ?thesis using l_def by simp
      qed
      ultimately show ?thesis by simp 
    next
      case False
      hence  \<open>norm x \<noteq> 0\<close> by simp
      thus ?thesis
      proof-
        have  \<open>(\<lambda> n. f n (x  /\<^sub>R norm x)) \<longlonglongrightarrow> s (x /\<^sub>R norm x)\<close>
        proof-
          have \<open>norm (x  /\<^sub>R norm x) = 1\<close>
            by (simp add: False)
          have \<open> \<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x. norm x = 1 \<longrightarrow> norm (f n x - s x) < e\<close>
            using \<open>f \<midarrow>ustrong\<rightarrow> s\<close>
            unfolding ustrong_convergence_def by blast
          hence \<open> \<forall>e>0. \<exists>N. \<forall>n\<ge>N. norm (f n (x  /\<^sub>R norm x) - s (x  /\<^sub>R norm x)) < e\<close>
            using  \<open>norm (x  /\<^sub>R norm x) = 1\<close> by fastforce
          thus ?thesis
            by (simp add: LIMSEQ_iff) 
        qed
        hence  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow>  (norm x) *\<^sub>R  s (x /\<^sub>R norm x)\<close>
          using bounded_linear.tendsto bounded_linear_scaleR_right by blast
        hence  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
          using l_def
          by simp
        have  \<open>(\<lambda> n.  f n x) \<longlonglongrightarrow> l x\<close>
        proof-
          have \<open>(norm x) *\<^sub>R f n (x /\<^sub>R norm x) = f n x\<close>
            for n
            using \<open>norm x \<noteq> 0\<close> \<open>\<And> n. bounded_linear (f n)\<close>
            unfolding bounded_linear_def linear_def
            by (simp add: assms(1) linear_simps(5)) 
          thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close> by simp
        qed
        thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
          by auto
      qed
    qed
    have \<open>linear l\<close>
    proof
      show "l (b1 + b2) = l b1 + l b2"
        for b1 :: 'a
          and b2 :: 'a
      proof-
        have \<open>(\<lambda> n. f n (b1 + b2)) \<longlonglongrightarrow> l (b1 + b2)\<close>
          using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
          by blast
        moreover have \<open>(\<lambda> n. f n (b1 + b2)) \<longlonglongrightarrow> l b1 + l b2\<close>
        proof-
          have \<open>(\<lambda> n. f n b1) \<longlonglongrightarrow> l b1\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          moreover have \<open>(\<lambda> n. f n b2) \<longlonglongrightarrow> l b2\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          ultimately have \<open>(\<lambda> n. f n b1 + f n b2) \<longlonglongrightarrow> l b1 + l b2\<close>
            by (simp add: tendsto_add) 
          moreover have \<open>(\<lambda> n. f n (b1 + b2)) = (\<lambda> n. f n b1 + f n b2)\<close>
          proof-
            have \<open>f n (b1 + b2) = f n b1 + f n b2\<close>
              for n
              using \<open>\<And> n. bounded_linear (f n)\<close>
              unfolding bounded_linear_def
              by (simp add: linear_add)
            thus ?thesis by blast
          qed
          ultimately show ?thesis by simp 
        qed
        ultimately show ?thesis
          using LIMSEQ_unique by blast            
      qed
      show "l (r *\<^sub>R b) = r *\<^sub>R l b"
        for r :: real
          and b :: 'a
      proof-
        have \<open>(\<lambda> n. f n (r *\<^sub>R b)) \<longlonglongrightarrow> l (r *\<^sub>R b)\<close>
          using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
          by blast
        moreover have \<open>(\<lambda> n. f n (r *\<^sub>R b)) \<longlonglongrightarrow>  r *\<^sub>R (l b)\<close>
        proof-
          have \<open>(\<lambda> n. f n b) \<longlonglongrightarrow> l b\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          hence \<open>(\<lambda> n. r *\<^sub>R (f n b)) \<longlonglongrightarrow> r *\<^sub>R (l b)\<close>
            using bounded_linear.tendsto bounded_linear_scaleR_right by blast
          moreover have \<open>(\<lambda> n. (f n (r *\<^sub>R b))) = (\<lambda> n. r *\<^sub>R (f n b))\<close>
          proof-
            have \<open>f n (r *\<^sub>R b) = r *\<^sub>R (f n b)\<close>
              for n
              using \<open>\<And> n. bounded_linear (f n)\<close>
              unfolding bounded_linear_def
              by (simp add: linear_scale)
            thus ?thesis by blast
          qed
          ultimately show ?thesis by simp 
        qed
        ultimately show ?thesis
          using LIMSEQ_unique by blast            
      qed
    qed
    moreover have \<open>bounded_linear_axioms l\<close>
    proof-
      have \<open>\<exists>K. \<forall>x. norm (l x) \<le> norm x * K\<close>
      proof(rule classical)
        assume \<open>\<not> (\<exists>K. \<forall>x. norm (l x) \<le> norm x * K)\<close>
        hence \<open>\<forall> K. \<exists> x. norm (l x) > norm x * K\<close>
          by smt
        hence \<open>\<forall> K. \<exists> x \<noteq> 0. norm (l x) > norm x * K\<close>
          using calculation linear_0 by force
        have \<open>\<forall> K. \<exists> x. norm x = 1 \<and> K < norm (l x)\<close>
        proof-
          have \<open>\<exists> x. norm x = 1 \<and> K < norm (l x)\<close>
            for K
          proof-
            have \<open>\<exists> x \<noteq> 0. norm (l x) > norm x * K\<close>
              using  \<open>\<forall> K. \<exists> x \<noteq> 0. norm (l x) > norm x * K\<close> by blast
            then obtain x where \<open>x \<noteq> 0\<close> and \<open>norm (l x) > norm x * K\<close>
              by blast
            have \<open>norm x > 0\<close> using \<open>x \<noteq> 0\<close> by simp
            hence  \<open>inverse (norm x) * norm (l x) > inverse (norm x) * (norm x) * K\<close>
              using  \<open>norm (l x) > norm x * K\<close>
              by (smt linordered_field_class.sign_simps(23) mult_left_le_imp_le positive_imp_inverse_positive) 
            moreover have \<open>(inverse (norm x)) * (norm x) = 1\<close>
              using \<open>norm x > 0\<close> by simp
            ultimately have \<open>(inverse (norm x)) * norm (l x) >  K\<close>
              by simp
            moreover have \<open>(inverse (norm x)) * norm (l x) = norm ((inverse (norm x)) *\<^sub>R (l x))\<close>
            proof-
              have \<open>(inverse (norm x)) > 0\<close>
                using \<open>norm x > 0\<close> 
                by simp
              thus ?thesis using norm_scaleR
                by simp 
            qed
            hence \<open> norm ((inverse (norm x)) *\<^sub>R (l x)) >  K\<close>
              using calculation by linarith
            hence \<open> norm (l ((inverse (norm x)) *\<^sub>R  x)) >  K\<close>
            proof-
              have \<open>(inverse (norm x)) *\<^sub>R (l x) = l ((inverse (norm x)) *\<^sub>R  x)\<close>
                by (simp add: \<open>linear l\<close> linear_scale)
              thus ?thesis
                using \<open>K < norm (l x /\<^sub>R norm x)\<close> by simp                 
            qed
            have \<open>norm ( (inverse (norm x)) *\<^sub>R  x ) = 1\<close>
              using \<open>norm x > 0\<close> by simp
            show ?thesis
              using \<open>K < norm (l (x /\<^sub>R norm x))\<close> \<open>norm (x /\<^sub>R norm x) = 1\<close> by blast 
          qed
          thus ?thesis by blast
        qed
        have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < e\<close>
          using \<open>uCauchy f\<close>
          unfolding uCauchy_def
          by blast
        hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < 1\<close>
          by auto
        then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < 1\<close>
          by blast
        hence \<open>\<forall>m\<ge>M. \<forall>x. 
            norm x = 1 \<longrightarrow> norm (f m x - f M x) < 1\<close>
          by blast
        have \<open>norm (f m x) \<le> norm (f M x) + norm (f m x - f M x)\<close>
          for m and x
          by (simp add: norm_triangle_sub) 
        hence \<open>norm (f m x) \<le> onorm (f M) * norm x + norm (f m x - f M x)\<close>
          for m and x
          using onorm
          by (smt assms(1)) 
        hence \<open>norm x = 1 \<Longrightarrow> norm (f m x) \<le> onorm (f M) + norm (f m x - f M x)\<close>
          for m and x
          by (metis mult_cancel_left2)
        hence \<open>m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm (f m x) < onorm (f M) + 1\<close>
          for m and x
          using  \<open>\<forall>m\<ge>M. \<forall>x. 
            norm x = 1 \<longrightarrow> norm (f m x - f M x) < 1\<close> 
          by smt
        have \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. f m x) \<longlonglongrightarrow> l x\<close>
          for x
          by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> l x\<close>)
        hence \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
          for x
          by (simp add: tendsto_norm)
        hence \<open>norm x = 1 \<Longrightarrow> norm (l x) \<le> onorm (f M) + 1\<close>
          for x
        proof-
          assume \<open>norm x = 1\<close>
          hence \<open>(\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
            using  \<open>\<And> x. norm x = 1 \<Longrightarrow> (\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
            by blast
          moreover have \<open>\<forall>  m \<ge> M. norm (f m x) \<le> onorm (f M) + 1\<close>
            using  \<open>\<And> m. \<And> x.  m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm (f m x) < onorm (f M) + 1\<close>
              \<open>norm x = 1\<close> by smt
          ultimately show ?thesis 
            by (rule Topological_Spaces.Lim_bounded)
        qed
        moreover have  \<open>\<exists> x. norm x = 1 \<and> onorm (f M) + 1 < norm (l x)\<close>
          by (simp add: \<open>\<forall>K. \<exists>x. norm x = 1 \<and> K < norm (l x)\<close>)
        ultimately show ?thesis
          by fastforce 
      qed
      thus ?thesis unfolding bounded_linear_axioms_def by blast
    qed
    ultimately show ?thesis unfolding bounded_linear_def by blast
  qed
  ultimately show ?thesis by blast
qed

theorem completeness_real_bounded:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector, perfect_space} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>\<And>n. bounded_linear (f n)\<close> and \<open>oCauchy f\<close>
  shows \<open>\<exists> l. bounded_linear l \<and> f \<midarrow>onorm\<rightarrow> l\<close>
proof-
  have \<open>uCauchy f\<close>
    using oCauchy_uCauchy \<open>oCauchy f\<close> \<open>\<And> n. bounded_linear (f n)\<close> by blast
  hence \<open>\<exists> l. bounded_linear l \<and> f \<midarrow>ustrong\<rightarrow> l\<close>
    using \<open>\<And> n. bounded_linear (f n)\<close>
      uCauchy_ustrong
    by auto
  then obtain l where \<open>bounded_linear l\<close> and \<open>f \<midarrow>ustrong\<rightarrow> l\<close> 
    by blast
  have \<open>(\<lambda>n. onorm (\<lambda>x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
    using  \<open>f \<midarrow>ustrong\<rightarrow> l\<close> \<open>bounded_linear l\<close> assms(1) onorm_convergence_def ustrong_onorm 
    by blast
  thus ?thesis
    unfolding onorm_convergence_def using \<open>bounded_linear l\<close> by blast
qed



end
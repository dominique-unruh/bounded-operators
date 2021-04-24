theory Extra_Nonstandard_Analysis
  imports
    "HOL-Nonstandard_Analysis.Nonstandard_Analysis"
    "HOL-Analysis.Uniform_Limit"
    "HOL-Analysis.Operator_Norm"

    Extra_General
begin

subsection\<open>\<open>Unobtrusive_NSA\<close> -- Cleaning up syntax from \<open>Nonstandard_Analysis\<close>\<close>

text \<open>
Load this theory instead of \<^theory>\<open>HOL-Nonstandard_Analysis.Nonstandard_Analysis\<close>. 
This will not include the syntax from \<^theory>\<open>HOL-Nonstandard_Analysis.Nonstandard_Analysis\<close>
(which is somewhat intrusive because it overwrites, e.g., the letters \<open>\<epsilon>\<close> and \<open>\<omega>\<close>).

Reactivate the notation locally via "@{theory_text \<open>includes nsa_notation\<close>}" in a lemma statement.
(Or sandwich a declaration using that notation between "@{theory_text \<open>unbundle nsa_notation ... unbundle no_nsa_notation\<close>}.)
\<close>

bundle no_nsa_notation begin
no_notation HyperDef.epsilon ("\<epsilon>")
no_notation HyperDef.omega ("\<omega>")
no_notation NSA.approx (infixl "\<approx>" 50)
no_notation HyperDef.pow (infixr "pow" 80)
no_notation HLim.NSLIM ("((_)/ \<midarrow>(_)/\<rightarrow>\<^sub>N\<^sub>S (_))" [60, 0, 60] 60)
no_notation HLog.powhr (infixr "powhr" 80)
no_notation HSEQ.NSLIMSEQ ("((_)/ \<longlonglongrightarrow>\<^sub>N\<^sub>S (_))" [60, 60] 60)
no_notation HSeries.NSsums (infixr "NSsums" 80)
no_notation Star.starfun_n ("*fn* _" [80] 80)
no_notation StarDef.FreeUltrafilterNat (\<open>\<U>\<close>)
no_notation StarDef.Ifun (\<open>(_ \<star>/ _)\<close> [300, 301] 300)
no_notation StarDef.starfun (\<open>*f* _\<close> [80] 80)
no_notation StarDef.starfun2 (\<open>*f2* _\<close> [80] 80)
no_notation StarDef.starP (\<open>*p* _\<close> [80] 80)
no_notation StarDef.starP2 (\<open>*p2* _\<close> [80] 80)
no_notation StarDef.starset (\<open>*s* _\<close> [80] 80)
end

bundle nsa_notation begin
notation HyperDef.epsilon ("\<epsilon>")
notation HyperDef.omega ("\<omega>")
notation NSA.approx (infixl "\<approx>" 50)
notation HyperDef.pow (infixr "pow" 80)
notation HLim.NSLIM ("((_)/ \<midarrow>(_)/\<rightarrow>\<^sub>N\<^sub>S (_))" [60, 0, 60] 60)
notation HLog.powhr (infixr "powhr" 80)
notation HSEQ.NSLIMSEQ ("((_)/ \<longlonglongrightarrow>\<^sub>N\<^sub>S (_))" [60, 60] 60)
notation HSeries.NSsums (infixr "NSsums" 80)
notation Star.starfun_n ("*fn* _" [80] 80)
notation StarDef.FreeUltrafilterNat (\<open>\<U>\<close>)
notation StarDef.Ifun (\<open>(_ \<star>/ _)\<close> [300, 301] 300)
notation StarDef.starfun (\<open>*f* _\<close> [80] 80)
notation StarDef.starfun2 (\<open>*f2* _\<close> [80] 80)
notation StarDef.starP (\<open>*p* _\<close> [80] 80)
notation StarDef.starP2 (\<open>*p2* _\<close> [80] 80)
notation StarDef.starset (\<open>*s* _\<close> [80] 80)
end

unbundle no_nsa_notation

text \<open>The following restores the method transfer under the name transfer.
      Use @{method StarDef.transfer} for the transfer method for nonstandard analysis.\<close>

method_setup transfer = \<open>
  let val free = Args.context -- Args.term >> (fn (_, Free v) => v | (ctxt, t) =>
        error ("Bad free variable: " ^ Syntax.string_of_term ctxt t))
      val fixing = Scan.optional (Scan.lift (Args.$$$ "fixing" -- Args.colon)
        |-- Scan.repeat free) []
      fun transfer_method equiv : (Proof.context -> Proof.method) context_parser =
        fixing >> (fn vs => fn ctxt =>
          SIMPLE_METHOD' (Transfer.gen_frees_tac vs ctxt THEN' Transfer.transfer_tac equiv ctxt))
  in
    transfer_method true
  end\<close>

subsection \<open>Nonstandard analog of uniform convergence\<close>

unbundle nsa_notation


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
  have \<open>\<exists>N. \<forall>n\<ge>N. \<forall>x\<in>S. norm (f n x - l x) < r\<close>
    if "r > 0"
    for r::real
  proof-
    from \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f* l) x\<close>
    have \<open>\<forall>n\<in>HNatInfinite.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
      by (simp add: InfinitesimalD2 Infinitesimal_approx_minus \<open>r > 0\<close>)
    have \<open>n \<ge> whn \<Longrightarrow>
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close>
      for n
      using HNatInfinite_upward_closed HNatInfinite_whn
        \<open>\<forall>n\<in>HNatInfinite. \<forall>x\<in>*s* S. hnorm ((*f2* f) n x - (*f* l) x) < hypreal_of_real r\<close> 
      by blast     
    hence \<open>\<exists> no. \<forall>n \<ge> no.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f* l) x ) < hypreal_of_real r\<close> 
      by blast    
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
  have \<open>\<exists>N. \<forall>n\<ge>N. \<forall> m\<ge>N. \<forall>x\<in>S. norm (f n x - f m x) < r\<close>
    if "r > 0"
    for r::real
  proof-
    from \<open>\<forall>N\<in>HNatInfinite. \<forall> M\<in>HNatInfinite. \<forall>x\<in>*s* S. (*f2* f) N x \<approx> (*f2* f) M x\<close>
    have \<open>\<forall>n\<in>HNatInfinite. \<forall> m\<in>HNatInfinite.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x ) < hypreal_of_real r\<close>
      by (simp add: InfinitesimalD2 Infinitesimal_approx_minus \<open>r > 0\<close>)
    have \<open>n \<ge> whn \<Longrightarrow> m \<ge> whn \<Longrightarrow>
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x ) < hypreal_of_real r\<close>
      for n m
      using HNatInfinite_upward_closed HNatInfinite_whn
        \<open>\<forall>n\<in>HNatInfinite. \<forall> m\<in>HNatInfinite. \<forall>x\<in>*s* S. hnorm ((*f2* f) n x - (*f2* f) m x) < hypreal_of_real r\<close> 
      by blast     
    hence \<open>\<exists> no. \<forall>n \<ge> no. \<forall> m \<ge> no.
       \<forall>x\<in>*s* S. hnorm ( (*f2* f) n x - (*f2* f) m x ) < hypreal_of_real r\<close>
      by blast
    thus \<open>\<exists> no. \<forall>n \<ge> no. \<forall> m \<ge> no. \<forall>x\<in>S. norm ( f n x - f m x ) < r\<close>
      by StarDef.transfer
  qed
  thus ?thesis
    using  dist_norm
    unfolding uniformly_Cauchy_on_def
    by metis
qed

lemma nsuniformly_Cauchy_on_iff:
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
  assumes a1: "\<And>N. \<And> x. N \<in> HNatInfinite \<Longrightarrow> hnorm x = 1 \<Longrightarrow> (*f2* f) N x  \<approx> (*f* l) x"
  shows "(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l"  
proof-
  have \<open>\<forall>N\<in>HNatInfinite. \<forall>x. hnorm x = 1 \<longrightarrow> (*f2* f) N x \<approx> (*f* l) x\<close>
    using a1 by blast                
  hence \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s*(sphere 0 1).  (*f2* f) N x \<approx> (*f* l) x\<close>
    using sphere_iff by auto
  hence \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close>
    by (simp add: nsuniform_convergence_I)
  thus \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close>
    by blast
qed

lemma nsupointwise_convergence_D:
  assumes \<open>(sphere 0 1): f \<midarrow>uniformly\<rightarrow> l\<close> and \<open>N \<in> HNatInfinite\<close> and \<open>hnorm x = 1\<close>
  shows "(*f2* f) N x \<approx> (*f* l) x"
proof-
  have \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s*(sphere 0 1). (*f2* f) N x \<approx> (*f* l) x\<close>
    using nsuniform_convergence_D \<open>sphere 0 1: f \<midarrow>uniformly\<rightarrow> l\<close> by blast                     
  thus \<open>(*f2* f) N x \<approx> (*f* l) x\<close>
    by (simp add: \<open>N \<in> HNatInfinite\<close> \<open>hnorm x = 1\<close> sphere_iff)
qed

lemma bounded_linear_HFinite:
  assumes a1: "bounded_linear a" and a2: "hnorm x = 1"
  shows "(*f* a) x \<in> HFinite"
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
  show ?thesis
    unfolding HFinite_def
    using "1" a1 a2 by auto
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


lemma linear_ball_zero:
  assumes t1: "linear f" and t2: "\<forall> x. norm x = 1 \<longrightarrow> f x = 0"
  shows "f = (\<lambda> _. 0)"
proof-
  have "f u = 0"
    for u
  proof(cases "u = 0")
    case True
    thus ?thesis
      by (simp add: linear_0 t1) 
  next
    case False
    have \<open>norm ( (inverse (norm u)) *\<^sub>R u ) = 1\<close>
      by (simp add: False)
    hence \<open>f ( (inverse (norm u)) *\<^sub>R u ) = 0\<close>
      by (simp add: t2)
    moreover have \<open>f ( (inverse (norm u)) *\<^sub>R u ) = (inverse (norm u)) *\<^sub>R (f  u)\<close>
      using \<open>linear f\<close> unfolding linear_def
      by (simp add: Real_Vector_Spaces.linear_def linear_scale) 
    ultimately have \<open>(inverse (norm u)) *\<^sub>R (f  u) = 0\<close>
      by simp
    moreover have \<open>(inverse (norm u)) \<noteq> 0\<close>
      using \<open>norm (u /\<^sub>R norm u) = 1\<close> by auto
    ultimately show ?thesis by simp
  qed
  thus ?thesis by auto
qed

lemma linear_ball_uniq:
  assumes t1: "linear f" and t2: "linear g" and t3: "\<forall> x. norm x = 1 \<longrightarrow> f x = g x"
shows "f = g"
proof-
  have "f x = g x"
    for x :: 'a
  proof-
    have "\<forall>x. norm x = 1 \<longrightarrow> (\<lambda> t. f t - g t) x = 0"
      using t3 by auto  
    moreover have \<open>linear (\<lambda> t. f t - g t)\<close>
      using \<open>linear f\<close> \<open>linear g\<close>
      by (simp add: linear_compose_sub) 
    ultimately have \<open>(\<lambda> t. f t - g t) = (\<lambda> _. 0)\<close>
      using linear_ball_zero by fastforce
    thus ?thesis
      by (meson eq_iff_diff_eq_0) 
  qed
  thus ?thesis by auto
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
  have \<open>a t = b t\<close>
    if "norm t = 1"
    for t
  proof-
    have \<open>hnorm (star_of t) = 1\<close>
      by (metis star_of_norm star_one_def that)
    hence \<open>(*f* a) (star_of t) \<approx> (*f* b) (star_of t)\<close>
      using \<open>\<forall>x. hnorm x = 1 \<longrightarrow> (*f* a) x \<approx> (*f* b) x\<close> by blast
    thus ?thesis
      by simp 
  qed
  thus ?thesis using linear_ball_uniq  \<open>linear a\<close>  \<open>linear b\<close>
    by blast
qed

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

unbundle no_nsa_notation

end

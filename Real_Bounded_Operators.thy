(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Several definitions of convergence of families of operators.

Main results:
- completeness_real_bounded: A sufficient condition for the completeness of a sequence of
 bounded operators.

*)

theory Real_Bounded_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL.Real_Vector_Spaces"
    Operator_Norm_Missing
    Uniform_Limit_Missing
    NSA_Miscellany
begin

section \<open>rbounded\<close>

section \<open>Real bounded operators\<close>

typedef (overloaded) ('a::real_normed_vector, 'b::real_normed_vector) rbounded
  = \<open>{f::'a \<Rightarrow> 'b. bounded_linear f}\<close>
  using bounded_linear_zero by blast

setup_lifting type_definition_rbounded

instantiation rbounded :: (real_normed_vector, real_normed_vector) "real_vector"
begin
lift_definition uminus_rbounded :: "('a,'b) rbounded \<Rightarrow> ('a,'b) rbounded"
  is "\<lambda> f. (\<lambda> t::'a. - f t)"
  by (fact bounded_linear_minus)

lift_definition zero_rbounded :: "('a,'b) rbounded" is "\<lambda>x::'a. (0::'b)"
  by (fact bounded_linear_zero)

lift_definition plus_rbounded :: "('a,'b) rbounded \<Rightarrow> ('a,'b) rbounded \<Rightarrow> ('a,'b) rbounded" is
  \<open>\<lambda> f g. (\<lambda> t. f t + g t)\<close>
  by (fact bounded_linear_add)

lift_definition minus_rbounded :: "('a,'b) rbounded \<Rightarrow> ('a,'b) rbounded \<Rightarrow> ('a,'b) rbounded" is
  \<open>\<lambda> f g. (\<lambda> t. f t - g t)\<close>
  by (simp add: bounded_linear_sub)

lift_definition scaleR_rbounded :: \<open>real \<Rightarrow> ('a, 'b) rbounded \<Rightarrow> ('a, 'b) rbounded\<close>
  is \<open>\<lambda> c. \<lambda> f. (\<lambda> x. c *\<^sub>R (f x))\<close>
  by (rule Real_Vector_Spaces.bounded_linear_const_scaleR)

instance
proof      
  fix a b c :: \<open>('a, 'b) rbounded\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer by auto
  fix a b :: \<open>('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close>
  show \<open>a + b = b + a\<close>
    apply transfer
    by (simp add: linordered_field_class.sign_simps(2))
  fix a :: \<open>('a, 'b) rbounded\<close>
  show \<open>0 + a = a\<close>
    apply transfer by simp
  fix a :: \<open>('a, 'b) rbounded\<close>
  show \<open>-a + a = 0\<close>
    apply transfer
    by simp
  fix a b :: \<open>('a, 'b) rbounded\<close>
  show \<open>a - b = a + - b\<close>
    apply transfer
    by auto
  fix a::real and x y :: \<open>('a, 'b) rbounded\<close>
  show \<open>a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y\<close>
    apply transfer
    by (simp add: scaleR_add_right)
  fix a b :: real and x :: \<open>('a, 'b) rbounded\<close>
  show \<open>(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x\<close>
    apply transfer
    by (simp add: scaleR_add_left)
  fix a b :: real and x :: \<open>('a, 'b) rbounded\<close>
  show \<open>a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x\<close>
    apply transfer
    by simp
  fix x :: \<open>('a, 'b) rbounded\<close>
  show \<open>1 *\<^sub>R x = x\<close>
    apply transfer
    by simp
qed
end

instantiation rbounded :: (real_normed_vector, real_normed_vector) "real_normed_vector"
begin
lift_definition norm_rbounded :: \<open>('a, 'b) rbounded \<Rightarrow> real\<close>
  is \<open>onorm\<close>.

lift_definition dist_rbounded :: \<open>('a, 'b) rbounded \<Rightarrow> ('a, 'b) rbounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. onorm (\<lambda> x. f x - g x )\<close>.

lift_definition sgn_rbounded :: \<open>('a, 'b) rbounded \<Rightarrow> ('a, 'b) rbounded\<close>
  is \<open>\<lambda> f. (\<lambda> x. (f x) /\<^sub>R (onorm f) )\<close>
  by (simp add: bounded_linear_const_scaleR)

definition uniformity_rbounded :: \<open>( ('a, 'b) rbounded \<times> ('a, 'b) rbounded ) filter\<close>
  where  \<open>uniformity_rbounded = (INF e:{0<..}. principal {((f::('a, 'b) rbounded), g). dist f g < e})\<close>

definition open_rbounded :: \<open>(('a, 'b) rbounded) set \<Rightarrow> bool\<close>
  where \<open>open_rbounded = (\<lambda> U::(('a, 'b) rbounded) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity))\<close>

instance
  apply intro_classes
        apply transfer
        apply auto
         apply transfer
         apply auto
        apply (simp add: uniformity_rbounded_def)
       apply (simp add: open_rbounded_def)
      apply (simp add: open_rbounded_def)
     apply transfer
  using onorm_pos_lt apply fastforce
    apply transfer
    apply (simp add: onorm_zero)
   apply transfer
   apply (simp add: onorm_triangle)
  apply transfer
  using onorm_scaleR by blast 
end

lemma trivia_UNIV_rbounded:
  fixes f::\<open>('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close> 
  assumes \<open>(UNIV::'a set) = 0\<close>
  shows \<open>f = 0\<close>
proof-
  have \<open>x = 0\<close>
    for x::'a
    using \<open>(UNIV::'a set) = 0\<close> by auto
  moreover have \<open>bounded_linear (Rep_rbounded f)\<close>
    using Rep_rbounded by auto
  ultimately have \<open>Rep_rbounded f x = 0\<close>
    for x::'a
    by (metis (full_types) linear_simps(3))
  hence \<open>Rep_rbounded f = (\<lambda> _. 0)\<close>
    by blast
  moreover have \<open>Rep_rbounded (Abs_rbounded (\<lambda> _::'a. 0::'b)) = (\<lambda> _. 0)\<close>
    by (simp add: Abs_rbounded_inverse)
  moreover have \<open>0 \<equiv> Abs_rbounded (\<lambda> _::'a. 0::'b)\<close>
    using zero_rbounded_def by auto
  ultimately have \<open>Rep_rbounded f = Rep_rbounded 0\<close>
    by simp
  thus ?thesis using  Rep_rbounded_inject 
    by auto
qed


section \<open>Pointwise convergence\<close>

definition pointwise_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>pointwise_convergence f l = ( \<forall> x. ( \<lambda> n. f n x ) \<longlonglongrightarrow> l x )\<close>

abbreviation pointwise_convergence_abbr:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  (\<open>((_)/ \<midarrow>strong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>strong\<rightarrow> l \<equiv> ( pointwise_convergence f l )\<close>


section \<open>Relationships among the different kind of convergence\<close>


lemma hnorm_unit_sphere:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector,'b::real_normed_vector) rbounded\<close>
    and N::hypnat
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>N\<in>HNatInfinite\<close> 
  shows \<open>\<exists> x \<in> *s* (sphere 0 1). 
    hnorm ((*f* f) N) \<approx> hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x )\<close>
proof-
  have \<open>bounded_linear (Rep_rbounded (f n))\<close>
    for n
    using Rep_rbounded by blast
  hence \<open>\<forall>e>0. \<exists> x\<in>(sphere 0 1).
      norm (norm((Rep_rbounded (f n)) x) - (onorm (Rep_rbounded (f n)))) < e\<close>
    for n
    using norm_unit_sphere  \<open>(UNIV::'a set) \<noteq> 0\<close> 
    by auto
  moreover have \<open>norm (f n) = onorm (Rep_rbounded (f n))\<close> 
    for n
    apply transfer
    by blast
  ultimately have \<open>\<forall>e>0. \<exists> x\<in>(sphere 0 1).
       norm ( norm ((Rep_rbounded (f n)) x) - norm (f n) ) < e\<close>
    for n
    by simp
  hence \<open>\<forall> n. \<exists> x\<in>(sphere 0 1).
       norm ( norm ((\<lambda> m. Rep_rbounded (f m)) n x) - norm (f n) ) < inverse (real (Suc n))\<close>
    by auto
  hence \<open>\<forall> n. \<exists> x\<in>*s*(sphere 0 1).
       hnorm ( hnorm ( (*f2* (\<lambda> m. Rep_rbounded (f m))) n x) - hnorm ((*f* f) n) ) 
            < inverse (hypreal_of_hypnat (hSuc n))\<close>
    by StarDef.transfer
  hence \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( hnorm ( (*f2* (\<lambda> m. Rep_rbounded (f m))) N x) - hnorm ((*f* f) N) ) 
            < inverse (hypreal_of_hypnat (hSuc N))\<close>
    by blast
  moreover have \<open>inverse (hypreal_of_hypnat (hSuc N)) \<in> Infinitesimal\<close>
    using inv_hSuc_Infinite_Infinitesimal \<open>N\<in>HNatInfinite\<close>
    by blast
  ultimately have \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( (*f2* (\<lambda> m. Rep_rbounded (f m))) N x) - hnorm ((*f* f) N) \<in> Infinitesimal\<close>
    using hnorm_less_Infinitesimal by blast
  hence \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( (*f2* (\<lambda> m. Rep_rbounded (f m))) N x) \<approx> hnorm ((*f* f) N)\<close>
    using bex_Infinitesimal_iff by blast
  thus ?thesis
    using approx_sym by blast    
qed

lemma hnorm_unit_sphere_double:
  fixes f::\<open>nat \<Rightarrow> nat \<Rightarrow> ('a::real_normed_vector,'b::real_normed_vector) rbounded\<close>
    and N M::hypnat 
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close> 
  shows \<open>\<exists> x \<in> *s* (sphere 0 1). 
    hnorm ((*f2* f) N M) \<approx> hnorm ( (*f3* (\<lambda> n m. Rep_rbounded (f n m))) N M x )\<close>
proof-
  have \<open>bounded_linear (Rep_rbounded (f n m))\<close>
    for n m
    using Rep_rbounded by blast
  hence \<open>\<forall>e>0. \<exists> x\<in>(sphere 0 1).
      norm (norm((Rep_rbounded (f n m)) x) - (onorm (Rep_rbounded (f n m)))) < e\<close>
    for n m
    using norm_unit_sphere  \<open>(UNIV::'a set) \<noteq> 0\<close> 
    by auto
  moreover have \<open>norm (f n m) = onorm (Rep_rbounded (f n m))\<close> 
    for n m
    apply transfer
    by blast
  ultimately have \<open>\<forall>e>0. \<exists> x\<in>(sphere 0 1).
       norm ( norm ((Rep_rbounded (f n m)) x) - norm (f n m) ) < e\<close>
    for n m
    by simp
  hence \<open>\<forall> n m. \<exists> x\<in>(sphere 0 1).
       norm ( norm ((\<lambda> n m. Rep_rbounded (f n m)) n m x) - norm (f n m) ) < inverse (real (Suc n))\<close>
    by auto
  hence \<open>\<forall> n m. \<exists> x\<in>*s*(sphere 0 1).
       hnorm ( hnorm ( (*f3* (\<lambda> n m. Rep_rbounded (f n m))) n m x) - hnorm ((*f2* f) n m) ) 
            < inverse (hypreal_of_hypnat (hSuc n))\<close>
    by StarDef.transfer
  hence \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( hnorm ( (*f3* (\<lambda> n m. Rep_rbounded (f n m))) N M x) - hnorm ((*f2* f) N M) ) 
            < inverse (hypreal_of_hypnat (hSuc N))\<close>
    by blast
  moreover have \<open>inverse (hypreal_of_hypnat (hSuc N)) \<in> Infinitesimal\<close>
    using inv_hSuc_Infinite_Infinitesimal \<open>N\<in>HNatInfinite\<close>
    by blast
  ultimately have \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( (*f3* (\<lambda> n m. Rep_rbounded (f n m))) N M x) - hnorm ((*f2* f) N M) \<in> Infinitesimal\<close>
    using hnorm_less_Infinitesimal by blast
  hence \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( (*f3* (\<lambda> n m. Rep_rbounded (f n m))) N M x) \<approx> hnorm ((*f2* f) N M)\<close>
    using bex_Infinitesimal_iff by blast
  thus ?thesis
    using approx_sym by blast    
qed

lemma uCauchy_unit_sphere:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector,'b::real_normed_vector) rbounded\<close>
    and N M::hypnat
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close>
  shows  \<open>\<exists> x \<in>*s* (sphere 0 1). hnorm ( (*f* f) N - (*f* f) M )
         \<approx> hnorm( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f2* (\<lambda> n. Rep_rbounded (f n))) M x )\<close>
proof-
  define g::\<open>nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) rbounded\<close>
    where \<open>g n m = f n - f m\<close> for n and m
  have \<open>\<exists> x \<in> *s* (sphere 0 1). 
    hnorm ((*f2* g) N M) \<approx> hnorm ( (*f3* (\<lambda> n m. Rep_rbounded (g n m))) N M x )\<close>
    using assms by (rule hnorm_unit_sphere_double)
  then obtain x where \<open>x \<in> *s* (sphere 0 1)\<close> and
    \<open>hnorm ((*f2* g) N M) \<approx> hnorm ( (*f3* (\<lambda> n m. Rep_rbounded (g n m))) N M x )\<close>
    by blast
  have \<open>\<forall> N M. hnorm ((*f2* g) N M) = hnorm ( (*f* f) N - (*f* f) M )\<close>
  proof-
    have \<open>\<forall> N M. norm (( (\<lambda>n m. f n - f m)) N M) =
    norm (( f) N - ( f) M)\<close>
      by blast
    hence \<open>\<forall> N M. hnorm ((*f2* (\<lambda>n m. f n - f m)) N M) =
    hnorm ((*f* f) N - (*f* f) M)\<close>
      by StarDef.transfer
    thus ?thesis unfolding g_def by blast
  qed
  moreover have \<open>\<forall> N M x. hnorm ( (*f3* (\<lambda> n m. Rep_rbounded (g n m))) N M x )
      = hnorm( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f2* (\<lambda> n. Rep_rbounded (f n))) M x )\<close>
  proof-
    have \<open>\<forall>N M x. norm
           (( (\<lambda>n m. Rep_rbounded (f n - f m))) N M x) =
          norm
           (( (\<lambda>n. Rep_rbounded (f n))) N x -
            ( (\<lambda>n. Rep_rbounded (f n))) M x)\<close>
      by (simp add: minus_rbounded.rep_eq)      
    hence \<open>\<forall>N M x. hnorm
           ((*f3* (\<lambda>n m. Rep_rbounded (f n - f m))) N M x) =
          hnorm
           ((*f2* (\<lambda>n. Rep_rbounded (f n))) N x -
            (*f2* (\<lambda>n. Rep_rbounded (f n))) M x)\<close>
      by StarDef.transfer
    thus ?thesis unfolding g_def by blast
  qed
  ultimately show ?thesis using \<open>x \<in> *s* (sphere 0 1)\<close> 
      \<open>hnorm ((*f2* g) N M) \<approx> hnorm ( (*f3* (\<lambda> n m. Rep_rbounded (g n m))) N M x )\<close>
    by auto
qed

lemma ustrong_onorm:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close> 
    and l::\<open>('a, 'b) rbounded\<close>
  assumes \<open>sphere 0 1: (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> (Rep_rbounded l)\<close>
  shows \<open>f \<longlonglongrightarrow> l\<close> 
proof(cases \<open>(UNIV::'a set) = 0\<close>)
  case True
  hence \<open>f n = 0\<close>
    for n
    by (rule trivia_UNIV_rbounded) 
  moreover have \<open>l = 0\<close>
    using True by (rule trivia_UNIV_rbounded)
  ultimately have \<open>( \<lambda> n. norm (f n - l) ) \<longlonglongrightarrow> 0\<close>
    by auto
  thus ?thesis
    using LIM_zero_cancel tendsto_norm_zero_iff by blast 
next
  case False
  have \<open>N\<in>HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (star_of l)\<close>
    for N::hypnat
  proof-
    assume \<open>N\<in>HNatInfinite\<close>
    from \<open>sphere 0 1: (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> (Rep_rbounded l)\<close>
    have \<open>NN\<in>HNatInfinite \<Longrightarrow> x \<in> *s* (sphere 0 1) \<Longrightarrow> 
              (*f2* (\<lambda> n. Rep_rbounded (f n))) NN x \<approx> (*f* (Rep_rbounded l)) x\<close>
      for x::\<open>'a star\<close> and NN::hypnat
      by (simp add: nsupointwise_convergence_D sphere_iff)
    hence \<open>x \<in> *s* (sphere 0 1) \<Longrightarrow> 
              (*f2* (\<lambda> n. Rep_rbounded (f n))) N x \<approx> (*f* (Rep_rbounded l)) x\<close>
      for x::\<open>'a star\<close>
      by (simp add: \<open>N \<in> HNatInfinite\<close>)
    hence \<open>x \<in> *s* (sphere 0 1) \<Longrightarrow> 
              (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f* (Rep_rbounded l)) x \<in> Infinitesimal\<close>
      for x::\<open>'a star\<close>
      using Infinitesimal_approx_minus by blast
    hence \<open>x \<in> *s* (sphere 0 1) \<Longrightarrow> 
             hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f* (Rep_rbounded l)) x ) \<in> Infinitesimal\<close>
      for x::\<open>'a star\<close>
      by (simp add: Infinitesimal_hnorm_iff)
    moreover have \<open>\<exists> x\<in> *s* (sphere 0 1). hnorm ((*f* f) N - (star_of l)) \<approx>
        hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f* (Rep_rbounded l)) x )\<close>
    proof-
      define g where \<open>g n = f n - l\<close> for n
      have \<open>\<exists> x \<in> *s* (sphere 0 1). 
        hnorm ((*f* g) N) \<approx> hnorm ( (*f2* (\<lambda> n. Rep_rbounded (g n))) N x )\<close>
        using False \<open>N\<in>HNatInfinite\<close>
        by (simp add: hnorm_unit_sphere)
      moreover have \<open>(*f* g) N \<approx> (*f* f) N - (star_of l)\<close>
      proof-
        have  \<open>\<forall> NN. ( g) NN = ( f) NN - ( l)\<close>
          unfolding g_def by auto
        hence  \<open>\<forall> NN. (*f* g) NN = (*f* f) NN - (star_of l)\<close>
          by StarDef.transfer
        thus ?thesis by auto
      qed
      moreover have \<open>(*f2* (\<lambda> n. Rep_rbounded (g n))) N x
         = (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f* (Rep_rbounded l)) x\<close>
        for x
      proof-
        have  \<open>\<forall> NN xx. ( (\<lambda> n. Rep_rbounded (g n))) NN xx
         = ( (\<lambda> n. Rep_rbounded (f n))) NN xx - ( (Rep_rbounded l)) xx\<close>
          unfolding g_def
          by (simp add: minus_rbounded.rep_eq) 
        hence  \<open>\<forall> NN xx. (*f2* (\<lambda> n. Rep_rbounded (g n))) NN xx
         = (*f2* (\<lambda> n. Rep_rbounded (f n))) NN xx - (*f* (Rep_rbounded l)) xx\<close>
          by StarDef.transfer
        thus ?thesis by auto
      qed
      ultimately show \<open>\<exists> x\<in> *s* (sphere 0 1). hnorm ((*f* f) N - (star_of l)) \<approx>
        hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f* (Rep_rbounded l)) x )\<close>
        by (metis (no_types, lifting) approx_hnorm approx_trans3)
    qed
    ultimately have \<open>hnorm ((*f* f) N - (star_of l)) \<in> Infinitesimal\<close>
      using approx_trans mem_infmal_iff by blast      
    hence \<open>(*f* f) N - (star_of l) \<in> Infinitesimal\<close>
      by (simp add: Infinitesimal_hnorm_iff)      
    thus ?thesis
      using bex_Infinitesimal_iff by auto 
  qed
  hence \<open>( \<lambda> n. norm (f n - l) ) \<longlonglongrightarrow>\<^sub>N\<^sub>S 0\<close>
    by (metis (full_types) NSLIMSEQ_I NSLIMSEQ_diff_const NSLIMSEQ_norm_zero cancel_comm_monoid_add_class.diff_cancel)     
  hence \<open>( \<lambda> n. norm (f n - l) ) \<longlonglongrightarrow> 0\<close>
    by (simp add: LIMSEQ_NSLIMSEQ_iff) 
  thus ?thesis
    using LIM_zero_cancel tendsto_norm_zero_iff by blast 
qed 


lemma oCauchy_uCauchy:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close>
  assumes \<open>Cauchy f\<close>
  shows \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. Rep_rbounded (f n))\<close>
proof-
  have  \<open>N\<in>HNatInfinite \<Longrightarrow> M\<in>HNatInfinite \<Longrightarrow> x\<in>*s* (sphere 0 1) \<Longrightarrow> 
    (*f2* (\<lambda> n. Rep_rbounded (f n))) N x \<approx> (*f2* (\<lambda> n. Rep_rbounded (f n))) M x\<close>
    for N M x
  proof-
    assume \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close> and \<open>x\<in>*s* (sphere 0 1)\<close> 
    from \<open>Cauchy f\<close>
    have \<open>NSCauchy f\<close>
      by (simp add: NSCauchy_Cauchy_iff)
    hence \<open>(*f* f) N \<approx> (*f* f) M\<close>
      unfolding NSCauchy_def
      using \<open>N\<in>HNatInfinite\<close> \<open>M\<in>HNatInfinite\<close>
      by blast
    hence \<open>(*f* f) N - (*f* f) M \<in> Infinitesimal\<close>
      using bex_Infinitesimal_iff by blast
    hence \<open>hnorm ((*f* f) N - (*f* f) M) \<in> Infinitesimal\<close>
      by (simp add: Infinitesimal_hnorm_iff)
    moreover have \<open>hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x
                                 - (*f2* (\<lambda> n. Rep_rbounded (f n))) M x )
        \<le> hnorm ((*f* f) N - (*f* f) M)\<close>
    proof-
      have \<open>bounded_linear (Rep_rbounded (f n))\<close>
        for n
        using Rep_rbounded by blast
      hence \<open>bounded_linear (\<lambda> x. Rep_rbounded (f n) x - Rep_rbounded (f m) x )\<close>
        for n m
        by (simp add: bounded_linear_sub)    
      moreover have \<open>\<And>NN MM xx.
       (\<And>n m. bounded_linear (\<lambda>x. Rep_rbounded (f n) x - Rep_rbounded (f m) x)) \<Longrightarrow>
       norm xx = 1 \<Longrightarrow>
       norm (Rep_rbounded (f NN) xx - Rep_rbounded (f MM) xx) \<le> onorm (Rep_rbounded (f NN - f MM))\<close>
        using onorm
        by (metis (no_types, hide_lams) Rep_rbounded mem_Collect_eq minus_rbounded.rep_eq mult.commute mult.left_neutral)        
      ultimately have \<open>\<forall> NN MM xx. norm xx = 1 \<longrightarrow> norm ( ( (\<lambda> n. Rep_rbounded (f n))) NN xx
                                 - ( (\<lambda> n. Rep_rbounded (f n))) MM xx )
        \<le> norm (( f) NN - ( f) MM)\<close>
        unfolding norm_rbounded_def
        by auto
      hence \<open>\<forall> NN MM xx. hnorm xx = 1 \<longrightarrow> hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) NN xx
                                 - (*f2* (\<lambda> n. Rep_rbounded (f n))) MM xx )
        \<le> hnorm ((*f* f) NN - (*f* f) MM)\<close>
        by StarDef.transfer
      moreover have \<open>hnorm x = 1\<close>
      proof-
        have \<open>\<forall> xx::'a. xx \<in> (sphere 0 1) \<longrightarrow> norm xx = 1\<close>
          by auto
        hence \<open>\<forall> xx::'a star. xx \<in> *s* (sphere 0 1) \<longrightarrow> hnorm xx = 1\<close>
          by StarDef.transfer
        thus ?thesis
          using \<open>x \<in> *s* (sphere 0 1)\<close>
          by blast
      qed
      ultimately show ?thesis by blast 
    qed
    moreover have \<open>hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f2* (\<lambda> n. Rep_rbounded (f n))) M x ) \<ge> 0\<close>
    proof-
      have \<open>norm ( ( (\<lambda> n. Rep_rbounded (f n))) NN xx - ( (\<lambda> n. Rep_rbounded (f n))) MM xx ) \<ge> 0\<close>
        for NN MM xx
        by auto
      thus ?thesis by auto 
    qed
    ultimately have \<open>hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f2* (\<lambda> n. Rep_rbounded (f n))) M x ) \<in> Infinitesimal\<close>
      using Infinitesimal_interval2 by blast
    thus ?thesis
      using bex_Infinitesimal_iff hnorm_le_Infinitesimal by blast 
  qed
  thus ?thesis using nsuniformly_Cauchy_on_I by metis
qed


lemma uCauchy_oCauchy:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close>
  assumes \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. Rep_rbounded (f n))\<close> 
  shows \<open>Cauchy f\<close>
proof(cases \<open>(UNIV::('a set)) = 0\<close>)
  case True
  hence \<open>f n = 0\<close>
    for n
    by (rule trivia_UNIV_rbounded) 
  moreover have \<open>Cauchy (\<lambda> n. 0::('a,'b) rbounded)\<close>
    unfolding Cauchy_def by auto
  ultimately show ?thesis
    by presburger 
next
  case False
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (*f* f) M\<close>
    for N M
  proof-
    assume \<open>N \<in> HNatInfinite\<close> and \<open>M \<in> HNatInfinite\<close>
    have \<open>x \<in>*s* (sphere 0 1) \<Longrightarrow> 
      (*f2* (\<lambda> n. Rep_rbounded (f n))) N x \<approx> (*f2* (\<lambda> n. Rep_rbounded (f n))) M x\<close>
      for x
      using \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. Rep_rbounded (f n))\<close>
      by (simp add: \<open>M \<in> HNatInfinite\<close> \<open>N \<in> HNatInfinite\<close> nsuniformly_Cauchy_on_iff)    
    hence \<open>x \<in>*s* (sphere 0 1) \<Longrightarrow> 
      hnorm( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f2* (\<lambda> n. Rep_rbounded (f n))) M x ) \<in> Infinitesimal\<close>
      for x
      using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by blast
    moreover have \<open>\<exists> x \<in>*s* (sphere 0 1). hnorm ( (*f* f) N - (*f* f) M )
         \<approx> hnorm( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f2* (\<lambda> n. Rep_rbounded (f n))) M x )\<close>
      using  False \<open>N \<in> HNatInfinite\<close> \<open>M \<in> HNatInfinite\<close>
      by (rule uCauchy_unit_sphere)
    ultimately have \<open>hnorm ( (*f* f) N - (*f* f) M ) \<in> Infinitesimal\<close>
      using approx_sym approx_trans3 mem_infmal_iff by blast          
    thus \<open>(*f* f) N \<approx> (*f* f) M\<close>
      using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by auto      
  qed
  hence \<open>NSCauchy f\<close>
    by (simp add: NSCauchy_def)
  thus ?thesis
    by (simp add: NSCauchy_Cauchy_iff) 
qed


proposition oCauchy_uCauchy_iff:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close>
  shows \<open>Cauchy f \<longleftrightarrow> uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. Rep_rbounded (f n))\<close>
proof
  show "uniformly_Cauchy_on (sphere 0 1) (\<lambda>n. Rep_rbounded (f n))"
    if "Cauchy f"
    using that
    by (simp add: oCauchy_uCauchy) 
  show "Cauchy f"
    if "uniformly_Cauchy_on (sphere 0 1) (\<lambda>n. Rep_rbounded (f n))"
    using that
    by (simp add: uCauchy_oCauchy) 
qed


lemma uCauchy_ustrong:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::banach) rbounded\<close>
  assumes \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. Rep_rbounded (f n))\<close>
  shows  \<open>\<exists> l::('a,'b) rbounded. 
    (sphere 0 1): (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> Rep_rbounded l\<close>
proof-
  from \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. Rep_rbounded (f n))\<close>
  have \<open>\<exists> s::'a\<Rightarrow>'b.
 (sphere 0 1): (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
    using uniformly_convergent_eq_Cauchy uniformly_convergent_on_def by blast
  then obtain s::\<open>'a\<Rightarrow>'b\<close> where
    \<open>(sphere 0 1): (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
    by blast
  have \<open>\<exists> L. \<forall> x\<in>(sphere 0 1). Rep_rbounded L x = s x\<close>
  proof-
    define l::\<open>'a \<Rightarrow> 'b\<close> where \<open>l x = (norm x) *\<^sub>R s ((inverse (norm x)) *\<^sub>R x)\<close>
      for x::'a       
    have \<open>t \<in> sphere 0 1 \<Longrightarrow> (\<lambda>x. norm x *\<^sub>R s (x /\<^sub>R norm x)) t = s t\<close>
      for t
      unfolding sphere_def
      by simp
    hence \<open>sphere 0 1: (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> l\<close>
      using  \<open>sphere 0 1: (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
      unfolding l_def 
      by (metis (no_types, lifting) uniform_limit_cong') 
    hence \<open>x \<in> sphere 0 1 \<Longrightarrow> l x = s x\<close>
      for x
      using  \<open>sphere 0 1: (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
      by (meson LIMSEQ_unique tendsto_uniform_limitI)
    have \<open>bounded_linear l\<close>
    proof-
      have \<open>\<And> n. bounded_linear (Rep_rbounded (f n))\<close>
        using Rep_rbounded by blast
      have \<open>(\<lambda> n. Rep_rbounded (f n) x) \<longlonglongrightarrow> l x\<close>
        for x
      proof(cases \<open>x = 0\<close>)
        case True
        have \<open>(\<lambda> n. Rep_rbounded (f n) x) \<longlonglongrightarrow> 0\<close>
        proof-
          have \<open>Rep_rbounded (f n) x = (0::'b)\<close>
            for n
          proof-
            have \<open>\<And> n. bounded_linear (Rep_rbounded (f n))\<close>
              using Rep_rbounded by blast 
            thus ?thesis
              by (simp add: True linear_simps(3)) 
          qed
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
          have  \<open>(\<lambda> n. (Rep_rbounded (f n)) (x  /\<^sub>R norm x)) \<longlonglongrightarrow> s (x /\<^sub>R norm x)\<close>
          proof-
            have \<open>\<forall> N\<in>HNatInfinite. \<forall>x\<in>*s* (sphere 0 1).
                     (*f2* (\<lambda> n. Rep_rbounded (f n))) N x \<approx> (*f* s) x\<close>
              using \<open>sphere 0 1: (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> s\<close> nsuniform_convergence_D 
              by blast
            moreover have \<open>star_of (x /\<^sub>R norm x) \<in> *s* (sphere 0 1)\<close>
            proof-
              have \<open>norm (x  /\<^sub>R norm x) = 1\<close>
                by (simp add: False)
              hence \<open>(x  /\<^sub>R norm x) \<in> (sphere 0 1)\<close>
                unfolding sphere_def by auto
              thus ?thesis
                by (meson starset_mem)                
            qed
            ultimately have \<open>\<forall> N\<in>HNatInfinite.
               (*f2* (\<lambda> n. Rep_rbounded (f n))) N (star_of (x /\<^sub>R norm x)) \<approx> (*f* s) (star_of (x /\<^sub>R norm x))\<close>
              by blast 
            moreover have \<open>\<forall> N. (*f2* (\<lambda> n. Rep_rbounded (f n))) N (star_of (x /\<^sub>R norm x))
                        \<approx> (*f* (\<lambda> n. Rep_rbounded (f n) (x /\<^sub>R norm x) )) N\<close>
            proof-
              have  \<open>\<forall> N. ( (\<lambda> n. Rep_rbounded (f n))) N ( (x /\<^sub>R norm x))
                        = ( (\<lambda> n. Rep_rbounded (f n) (x /\<^sub>R norm x) )) N\<close>
                by blast
              hence \<open>\<forall> N. (*f2* (\<lambda> n. Rep_rbounded (f n))) N (star_of (x /\<^sub>R norm x))
                        = (*f* (\<lambda> n. Rep_rbounded (f n) (x /\<^sub>R norm x) )) N\<close>
                by StarDef.transfer
              thus ?thesis
                by simp 
            qed
            ultimately have  \<open>\<forall> N\<in>HNatInfinite.
               (*f* (\<lambda> n. Rep_rbounded (f n) (x /\<^sub>R norm x) )) N \<approx> (*f* s) (star_of (x /\<^sub>R norm x))\<close>
              using approx_trans3 by blast                 
            hence \<open> (\<lambda>n. Rep_rbounded (f n)  (x /\<^sub>R norm x)) \<longlonglongrightarrow>\<^sub>N\<^sub>S s  (x /\<^sub>R norm x)\<close>
              using NSLIMSEQ_def
              by (metis starfun_eq)              
            thus ?thesis
              by (simp add: NSLIMSEQ_LIMSEQ)              
          qed
          hence  \<open>(\<lambda> n. (norm x) *\<^sub>R (Rep_rbounded (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow>  (norm x) *\<^sub>R  s (x /\<^sub>R norm x)\<close>
            using bounded_linear.tendsto bounded_linear_scaleR_right by blast
          hence  \<open>(\<lambda> n. (norm x) *\<^sub>R (Rep_rbounded (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
            using l_def
            by simp
          have  \<open>(\<lambda> n. (Rep_rbounded(f n)) x) \<longlonglongrightarrow> l x\<close>
          proof-
            have \<open>(norm x) *\<^sub>R (Rep_rbounded (f n)) (x /\<^sub>R norm x) = (Rep_rbounded (f n)) x\<close>
              for n
              using \<open>norm x \<noteq> 0\<close> \<open>\<And> n. bounded_linear (Rep_rbounded (f n))\<close>
              unfolding bounded_linear_def linear_def
              by (simp add: \<open>\<And>n. bounded_linear (Rep_rbounded (f n))\<close> linear_simps(5))               
            thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R (Rep_rbounded (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close> 
              by simp
          qed
          thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R (Rep_rbounded (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
            by auto
        qed
      qed
      have \<open>linear l\<close>
      proof
        show "l (b1 + b2) = l b1 + l b2"
          for b1 :: 'a
            and b2 :: 'a
        proof-
          have \<open>(\<lambda> n. (Rep_rbounded (f n)) (b1 + b2)) \<longlonglongrightarrow> l (b1 + b2)\<close>
            using  \<open>\<And> x. (\<lambda> n. (Rep_rbounded (f n)) x) \<longlonglongrightarrow> l x\<close>
            by blast
          moreover have \<open>(\<lambda> n. (Rep_rbounded (f n)) (b1 + b2)) \<longlonglongrightarrow> l b1 + l b2\<close>
          proof-
            have \<open>(\<lambda> n. (Rep_rbounded (f n))  b1) \<longlonglongrightarrow> l b1\<close>
              using  \<open>\<And> x. (\<lambda> n. (Rep_rbounded (f n))  x) \<longlonglongrightarrow> l x\<close>
              by blast
            moreover have \<open>(\<lambda> n. (Rep_rbounded (f n))  b2) \<longlonglongrightarrow> l b2\<close>
              using  \<open>\<And> x. (\<lambda> n.  (Rep_rbounded (f n))  x) \<longlonglongrightarrow> l x\<close>
              by blast
            ultimately have \<open>(\<lambda> n. (Rep_rbounded (f n))  b1 +  (Rep_rbounded (f n))  b2) \<longlonglongrightarrow> l b1 + l b2\<close>
              by (simp add: tendsto_add) 
            moreover have \<open>(\<lambda> n.  (Rep_rbounded (f n))  (b1 + b2)) = (\<lambda> n.  (Rep_rbounded (f n))  b1 +  (Rep_rbounded (f n))  b2)\<close>
            proof-
              have \<open> (Rep_rbounded (f n))  (b1 + b2) =  (Rep_rbounded (f n))  b1 +  (Rep_rbounded (f n))  b2\<close>
                for n
                using \<open>\<And> n. bounded_linear  (Rep_rbounded (f n))\<close>
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
          have \<open>(\<lambda> n.  (Rep_rbounded (f n))  (r *\<^sub>R b)) \<longlonglongrightarrow> l (r *\<^sub>R b)\<close>
            using  \<open>\<And> x. (\<lambda> n.  (Rep_rbounded (f n))  x) \<longlonglongrightarrow> l x\<close>
            by blast
          moreover have \<open>(\<lambda> n.  (Rep_rbounded (f n))  (r *\<^sub>R b)) \<longlonglongrightarrow>  r *\<^sub>R (l b)\<close>
          proof-
            have \<open>(\<lambda> n.  (Rep_rbounded (f n))  b) \<longlonglongrightarrow> l b\<close>
              using  \<open>\<And> x. (\<lambda> n.  (Rep_rbounded (f n))  x) \<longlonglongrightarrow> l x\<close>
              by blast
            hence \<open>(\<lambda> n. r *\<^sub>R ( (Rep_rbounded (f n))  b)) \<longlonglongrightarrow> r *\<^sub>R (l b)\<close>
              using bounded_linear.tendsto bounded_linear_scaleR_right by blast
            moreover have \<open>(\<lambda> n. ( (Rep_rbounded (f n))  (r *\<^sub>R b))) = (\<lambda> n. r *\<^sub>R ( (Rep_rbounded (f n))  b))\<close>
            proof-
              have \<open> (Rep_rbounded (f n))  (r *\<^sub>R b) = r *\<^sub>R ( (Rep_rbounded (f n))  b)\<close>
                for n
                using \<open>\<And> n. bounded_linear ( (Rep_rbounded (f n)) )\<close>
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
          from \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. Rep_rbounded (f n))\<close>
          have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x\<in>(sphere 0 1). dist ((Rep_rbounded (f m)) x) (Rep_rbounded (f n) x) < e\<close>
            by (meson uniformly_Cauchy_on_def)
          hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x\<in>(sphere 0 1). norm (((Rep_rbounded (f m)) x) - (Rep_rbounded (f n) x)) < e\<close>
            by (simp add: dist_norm) 
          hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (((Rep_rbounded (f m)) x) - (Rep_rbounded (f n) x)) < e\<close>
            unfolding sphere_def by auto
          hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm ((Rep_rbounded (f m)) x - (Rep_rbounded (f n)) x) < 1\<close>
            by auto
          then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm ((Rep_rbounded (f m)) x - (Rep_rbounded (f n)) x) < 1\<close>
            by blast
          hence  \<open>\<forall>m\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm ((Rep_rbounded (f m)) x - (Rep_rbounded (f M)) x) < 1\<close>
            by blast
          have \<open>norm ((Rep_rbounded (f m)) x) \<le> norm ((Rep_rbounded (f M)) x) + norm ((Rep_rbounded (f m)) x - (Rep_rbounded (f M)) x)\<close>
            for m and x
            by (simp add: norm_triangle_sub) 
          hence \<open>norm ((Rep_rbounded (f m)) x) \<le> onorm (Rep_rbounded (f M)) * norm x + norm ((Rep_rbounded (f m)) x - (Rep_rbounded (f M)) x)\<close>
            for m and x
            using onorm  \<open>\<And>n. bounded_linear (Rep_rbounded (f n))\<close>
            by smt                    
          hence \<open>norm x = 1 \<Longrightarrow> norm ((Rep_rbounded (f m)) x) \<le> onorm (Rep_rbounded (f M)) + norm ((Rep_rbounded (f m)) x - (Rep_rbounded (f M)) x)\<close>
            for m and x
            by (metis mult_cancel_left2)
          hence \<open>m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm ((Rep_rbounded (f m)) x) < onorm (Rep_rbounded (f M)) + 1\<close>
            for m and x
            using  \<open>\<forall>m\<ge>M. \<forall>x. 
            norm x = 1 \<longrightarrow> norm ((Rep_rbounded (f m)) x - (Rep_rbounded (f M)) x) < 1\<close> 
            by smt
          have \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. (Rep_rbounded (f m)) x) \<longlonglongrightarrow> l x\<close>
            for x
            by (simp add: \<open>\<And>x. (\<lambda>n. (Rep_rbounded (f n)) x) \<longlonglongrightarrow> l x\<close>)
          hence \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. norm ((Rep_rbounded (f m)) x)) \<longlonglongrightarrow> norm (l x)\<close>
            for x
            by (simp add: tendsto_norm)
          hence \<open>norm x = 1 \<Longrightarrow> norm (l x) \<le> onorm (Rep_rbounded (f M)) + 1\<close>
            for x
          proof-
            assume \<open>norm x = 1\<close>
            hence \<open>(\<lambda> m. norm ((Rep_rbounded (f m)) x)) \<longlonglongrightarrow> norm (l x)\<close>
              using  \<open>\<And> x. norm x = 1 \<Longrightarrow> (\<lambda> m. norm ((Rep_rbounded (f m)) x)) \<longlonglongrightarrow> norm (l x)\<close>
              by blast
            moreover have \<open>\<forall>  m \<ge> M. norm ((Rep_rbounded (f m)) x) \<le> onorm (Rep_rbounded (f M)) + 1\<close>
              using  \<open>\<And> m. \<And> x.  m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm ((Rep_rbounded (f m)) x) < onorm (Rep_rbounded (f M)) + 1\<close>
                \<open>norm x = 1\<close> by smt
            ultimately show ?thesis 
              by (rule Topological_Spaces.Lim_bounded)
          qed
          moreover have  \<open>\<exists> x. norm x = 1 \<and> onorm (Rep_rbounded (f M)) + 1 < norm (l x)\<close>
            by (simp add: \<open>\<forall>K. \<exists>x. norm x = 1 \<and> K < norm (l x)\<close>)
          ultimately show ?thesis
            by fastforce 
        qed
        thus ?thesis unfolding bounded_linear_axioms_def by blast 
      qed
      ultimately show ?thesis unfolding bounded_linear_def by blast
    qed
    hence \<open>\<exists> L. Rep_rbounded L = l\<close>
      using Rep_rbounded_cases by auto
    thus ?thesis
      using \<open>\<And>x. x \<in> sphere 0 1 \<Longrightarrow> l x = s x\<close> 
      by blast        
  qed
  then obtain L::\<open>('a,'b) rbounded\<close> where \<open>\<forall> x\<in>(sphere 0 1). (Rep_rbounded L) x = s x\<close>
    by blast
  have "sphere 0 1: (\<lambda>n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> Rep_rbounded L"
    using  \<open>\<forall> x\<in>(sphere 0 1). (Rep_rbounded L) x = s x\<close>  \<open>(sphere 0 1): (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
    by (metis (no_types, lifting) uniform_limit_cong')
  thus ?thesis by blast
qed  

lemma onorm_ustrong:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close>
    and l::\<open>('a, 'b) rbounded\<close> 
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(sphere 0 1): (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> Rep_rbounded l\<close>
proof-
  have \<open>N\<in>HNatInfinite \<Longrightarrow> x \<in> *s* (sphere 0 1) \<Longrightarrow>
       (*f2* (\<lambda> n. Rep_rbounded (f n))) N x \<approx> (*f* (Rep_rbounded l)) x\<close>
    for N and x
  proof-
    assume \<open>N\<in>HNatInfinite\<close> and \<open>x \<in> *s* (sphere 0 1)\<close>
    have \<open>(*f* f) N \<approx> (star_of l)\<close>
      using \<open>f \<longlonglongrightarrow> l\<close> \<open>N\<in>HNatInfinite\<close>
      by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_D)
    hence \<open>hnorm ( (*f* f) N - (star_of l) ) \<in> Infinitesimal\<close>
      using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by auto
    moreover have \<open>hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f* (Rep_rbounded l)) x )
                \<le> hnorm ( (*f* f) N - (star_of l) )\<close>
    proof-
      have \<open>bounded_linear (\<lambda> t. Rep_rbounded (f N) t - Rep_rbounded l t)\<close>
        for N
        using Rep_rbounded bounded_linear_sub by auto        
      hence \<open>norm x = 1 \<Longrightarrow>
           norm (Rep_rbounded (f N) x - Rep_rbounded l x)
           \<le> onorm (\<lambda> t. Rep_rbounded (f N) t - Rep_rbounded l t)\<close>
        for N x
        by (metis (no_types) mult.commute mult.left_neutral onorm)
      moreover have \<open> (\<lambda> t. Rep_rbounded (f N) t - Rep_rbounded l t) = Rep_rbounded (f N - l)\<close>
        for N
        apply transfer
        by auto
      ultimately have \<open>norm x = 1 \<Longrightarrow>
           norm (Rep_rbounded (f N) x - Rep_rbounded l x)
           \<le> onorm (Rep_rbounded (f N - l))\<close>
        for N x
        by simp
      hence \<open>\<forall> N. \<forall> x. x \<in>  (sphere 0 1) \<longrightarrow> 
         norm ( ( (\<lambda> n. Rep_rbounded (f n))) N x - ( (Rep_rbounded l)) x )
                \<le> norm ( ( f) N - ( l) )\<close>
        unfolding norm_rbounded_def
        by auto
      hence \<open>\<forall> N. \<forall> x. x \<in> *s* (sphere 0 1) \<longrightarrow> 
         hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f* (Rep_rbounded l)) x )
                \<le> hnorm ( (*f* f) N - (star_of l) )\<close>
        by StarDef.transfer
      thus ?thesis using \<open>x\<in>*s* (sphere 0 1)\<close> by blast
    qed
    moreover have \<open>0 \<le> hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f* (Rep_rbounded l)) x )\<close>
      by simp      
    ultimately have \<open>hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f* (Rep_rbounded l)) x )
            \<in> Infinitesimal\<close>
      using Infinitesimal_interval2 by blast
    thus ?thesis
      by (simp add: Infinitesimal_approx_minus Infinitesimal_hnorm_iff) 
  qed
  hence \<open>(sphere 0 1): (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> Rep_rbounded l\<close>
    by (simp add: nsupointwise_convergence_I sphere_iff)    
  thus ?thesis by blast
qed

proposition onorm_ustrong_iff:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close>
    and l::\<open>('a, 'b) rbounded\<close> 
  shows \<open>(f \<longlonglongrightarrow> l) \<longleftrightarrow> (sphere 0 1): (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> Rep_rbounded l\<close>
proof
  show "sphere 0 1: (\<lambda>n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> Rep_rbounded l"
    if "f \<longlonglongrightarrow> l"
    using that
    using onorm_ustrong by blast 
  show "f \<longlonglongrightarrow> l"
    if "sphere 0 1: (\<lambda>n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> Rep_rbounded l"
    using that
    by (simp add: that ustrong_onorm) 
qed

theorem completeness_real_bounded:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::banach) rbounded\<close>
  assumes \<open>Cauchy f\<close>
  shows \<open>\<exists> L. f \<longlonglongrightarrow> L\<close>
proof-
  have  \<open>\<And> n. bounded_linear (Rep_rbounded (f n))\<close>
    using Rep_rbounded by auto
  hence \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. Rep_rbounded (f n))\<close>
    using oCauchy_uCauchy  \<open>Cauchy f\<close> by blast
  hence \<open>\<exists> L. sphere 0 1: (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> Rep_rbounded L\<close>
    using uCauchy_ustrong
    by blast
  then obtain L where \<open>sphere 0 1: (\<lambda> n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> Rep_rbounded L\<close>
    by blast
  thus ?thesis 
    using ustrong_onorm Lim_null tendsto_norm_zero_cancel by fastforce 
qed


instantiation rbounded :: ("{real_normed_vector, perfect_space}", banach) "banach"
begin
instance
  apply intro_classes
  using completeness_real_bounded convergentI by auto
end

lemma onorm_strong:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close>
    and l::\<open>('a, 'b) rbounded\<close> and x::'a
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda>n. (Rep_rbounded (f n)) x) \<longlonglongrightarrow> (Rep_rbounded l) x\<close>
proof-
  have \<open>N\<in>HNatInfinite \<Longrightarrow> (*f* (\<lambda>n. (Rep_rbounded (f n)) x)) N \<approx> star_of ((Rep_rbounded l) x)\<close>
    for N
  proof-
    assume \<open>N\<in>HNatInfinite\<close>
    show ?thesis 
    proof(cases \<open>x = 0\<close>)
      case True
      have \<open>(Rep_rbounded (f n)) x = 0\<close>
        for n
      proof-
        have \<open>bounded_linear (Rep_rbounded (f n))\<close>
          using Rep_rbounded by blast
        thus ?thesis
          using \<open>x = 0\<close>
          by (simp add: linear_simps(3))          
      qed
      moreover have \<open>(Rep_rbounded l) x = 0\<close>
      proof-
        have \<open>bounded_linear (Rep_rbounded l)\<close>
          using Rep_rbounded by blast
        thus ?thesis 
          using \<open>x = 0\<close>
          by (simp add: linear_simps(3))          
      qed
      ultimately have \<open>(Rep_rbounded (f n)) x = (Rep_rbounded l) x\<close>
        for n
        by simp
      hence \<open>star_of ((Rep_rbounded (f n)) x) = star_of ((Rep_rbounded l) x)\<close>
        for n
        by StarDef.transfer
      hence \<open>(*f* (\<lambda> n. (Rep_rbounded (f n)) x)) N = star_of ((Rep_rbounded l) x)\<close>
        by auto
      thus ?thesis by auto 
    next
      case False
      from \<open>f \<longlonglongrightarrow> l\<close>
      have \<open>sphere 0 1: (\<lambda>n. Rep_rbounded (f n)) \<midarrow>uniformly\<rightarrow> (Rep_rbounded l)\<close>
        using onorm_ustrong by blast
      hence \<open>t \<in> *s*(sphere 0 1) \<Longrightarrow> (*f2* (\<lambda>n. Rep_rbounded (f n))) N t \<approx> (*f* (Rep_rbounded l)) t\<close>
        for t
        using \<open>N \<in> HNatInfinite\<close> nsupointwise_convergence_D sphere_iff by blast
      moreover have \<open>star_of (x /\<^sub>R norm x) \<in> *s*(sphere 0 1)\<close>
      proof-
        have \<open>(x /\<^sub>R norm x) \<in> (sphere 0 1)\<close>
          using False unfolding sphere_def by auto
        thus ?thesis by StarDef.transfer
      qed
      ultimately have \<open>(*f2* (\<lambda>n. Rep_rbounded (f n))) N (star_of (x /\<^sub>R norm x)) 
          \<approx> (*f* (Rep_rbounded l)) (star_of (x /\<^sub>R norm x))\<close>
        by blast
      hence \<open>(*f2* scaleR) (star_of (norm x)) ( (*f2* (\<lambda>n. Rep_rbounded (f n))) N (star_of (x /\<^sub>R norm x)) ) 
          \<approx> (*f2* scaleR) (star_of (norm x)) ( (*f* (Rep_rbounded l)) (star_of (x /\<^sub>R norm x)) )\<close>
        using approx_scaleR2 star_scaleR_def starfun2_star_of
        by metis
      moreover have \<open>(*f2* scaleR) (star_of (norm x)) ( (*f2* (\<lambda>n. Rep_rbounded (f n))) N (star_of (x /\<^sub>R norm x)) )
          = (*f* (\<lambda>n. Rep_rbounded (f n) x)) N\<close>
      proof-
        have \<open>bounded_linear (Rep_rbounded (f n))\<close>
          for n
          using Rep_rbounded by auto          
        hence \<open>\<forall> N. ( scaleR) ( (norm x)) ( ( (\<lambda>n. Rep_rbounded (f n))) N ( (x /\<^sub>R norm x)) )
          = ( (\<lambda>n. Rep_rbounded (f n) x)) N\<close>
        proof -
          have f1: "Rep_rbounded (f v0_0) (x /\<^sub>R norm x) = Rep_rbounded (f v0_0) x /\<^sub>R norm x"
            using \<open>\<And>n. bounded_linear (Rep_rbounded (f n))\<close> linear_simps(5) by blast
          obtain nn :: nat where
            "(\<exists>v0. norm x *\<^sub>R Rep_rbounded (f v0) (x /\<^sub>R norm x) \<noteq> Rep_rbounded (f v0) x) = (norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) \<noteq> Rep_rbounded (f nn) x)"
            by meson
          moreover
          { assume "norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) \<noteq> Rep_rbounded (f nn) x"
            then have "norm x *\<^sub>R (x /\<^sub>R norm x) \<noteq> 0 \<or> x \<noteq> 0"
              by (metis \<open>\<And>n. bounded_linear (Rep_rbounded (f n))\<close> linear_simps(5))
            moreover
            { assume "norm x *\<^sub>R (x /\<^sub>R norm x) \<noteq> 0"
              moreover
              { assume "norm x *\<^sub>R x /\<^sub>R norm x \<noteq> norm x *\<^sub>R (x /\<^sub>R norm x)"
                moreover
                { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded (f nn) x /\<^sub>R norm x) = Rep_rbounded (f nn) x /\<^sub>R norm x \<and> norm x *\<^sub>R x /\<^sub>R norm x \<noteq> norm x *\<^sub>R (x /\<^sub>R norm x)"
                  moreover
                  { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded (f nn) x /\<^sub>R norm x) = Rep_rbounded (f nn) x /\<^sub>R norm x \<and> 0 *\<^sub>R (0::'a) \<noteq> (1 / norm x) *\<^sub>R 0"
                    moreover
                    { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded (f nn) x /\<^sub>R norm x) = Rep_rbounded (f nn) x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 \<noteq> x /\<^sub>R norm x"
                      moreover
                      { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded (f nn) x /\<^sub>R norm x) = Rep_rbounded (f nn) x /\<^sub>R norm x \<and> norm x \<noteq> inverse (norm x)"
                        moreover
                        { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded (f nn) x /\<^sub>R norm x) = Rep_rbounded (f nn) x /\<^sub>R norm x \<and> 1 / norm x \<noteq> 0"
                          { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded (f nn) x /\<^sub>R norm x) = Rep_rbounded (f nn) x /\<^sub>R norm x \<and> (if 1 / norm x = 0 then norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) = 0 else (1 / norm x) *\<^sub>R (Rep_rbounded (f nn) x /\<^sub>R norm x) = (1 / norm x) *\<^sub>R norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x))"
                            then have "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded (f nn) x /\<^sub>R norm x) = Rep_rbounded (f nn) x /\<^sub>R norm x \<and> (1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded (f nn) x /\<^sub>R norm x) = norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x)"
                              using vector_fraction_eq_iff by blast
                            then have "x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) = Rep_rbounded (f nn) x"
                              using f1
                              using \<open>(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded (f nn) x /\<^sub>R norm x) = Rep_rbounded (f nn) x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 \<noteq> (1 / norm x) *\<^sub>R 0\<close> scaleR_cong_right by blast  }
                          then have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) = Rep_rbounded (f nn) x"
                            by fastforce }
                        ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) = Rep_rbounded (f nn) x"
                          by fastforce }
                      ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> 0 *\<^sub>R 0 = norm x *\<^sub>R x \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) = Rep_rbounded (f nn) x"
                        by auto }
                    ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> (1 / norm x) *\<^sub>R 0 = x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 = norm x *\<^sub>R x \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) = Rep_rbounded (f nn) x"
                      by auto }
                  ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = 0 \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) = Rep_rbounded (f nn) x"
                    by auto }
                ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = 0 \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) = Rep_rbounded (f nn) x"
                  by fastforce }
              ultimately have "norm x = 0 \<and> x = 0 \<longrightarrow> norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) = Rep_rbounded (f nn) x"
                by (simp add: inverse_eq_divide) }
            ultimately have "norm x *\<^sub>R Rep_rbounded (f nn) (x /\<^sub>R norm x) = Rep_rbounded (f nn) x"
              using f1
              by (simp add: \<open>\<And>n. bounded_linear (Rep_rbounded (f n))\<close> linear_simps(5))  }
          ultimately show ?thesis
            by meson
        qed       
        hence  \<open>\<forall> N. (*f2* scaleR) (star_of (norm x)) ( (*f2* (\<lambda>n. Rep_rbounded (f n))) N (star_of (x /\<^sub>R norm x)) )
          = (*f* (\<lambda>n. Rep_rbounded (f n) x)) N\<close>
          by StarDef.transfer
        thus ?thesis by blast
      qed
      moreover have \<open>(*f2* scaleR) (star_of (norm x)) ( (*f* (Rep_rbounded l)) (star_of (x /\<^sub>R norm x)) )
            = star_of (Rep_rbounded l x)\<close> 
      proof-
        have \<open>bounded_linear (Rep_rbounded l)\<close>
          using Rep_rbounded by auto          
        hence \<open>( scaleR) ( (norm x)) ( ( (Rep_rbounded l)) ( (x /\<^sub>R norm x)) )
            =  (Rep_rbounded l x)\<close>
        proof -
          have f1: "Rep_rbounded l (x /\<^sub>R norm x) = Rep_rbounded l x /\<^sub>R norm x"
            by (meson \<open>bounded_linear (Rep_rbounded l)\<close> linear_simps(5))
          { assume "norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x) \<noteq> Rep_rbounded l x"
            then have "norm x *\<^sub>R (x /\<^sub>R norm x) \<noteq> 0 \<or> x \<noteq> 0"
              by (metis \<open>bounded_linear (Rep_rbounded l)\<close> linear_simps(5))
            moreover
            { assume "norm x *\<^sub>R (x /\<^sub>R norm x) \<noteq> 0"
              moreover
              { assume "norm x *\<^sub>R x /\<^sub>R norm x \<noteq> norm x *\<^sub>R (x /\<^sub>R norm x)"
                moreover
                { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded l x /\<^sub>R norm x) = Rep_rbounded l x /\<^sub>R norm x \<and> norm x *\<^sub>R x /\<^sub>R norm x \<noteq> norm x *\<^sub>R (x /\<^sub>R norm x)"
                  moreover
                  { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded l x /\<^sub>R norm x) = Rep_rbounded l x /\<^sub>R norm x \<and> 0 *\<^sub>R (0::'a) \<noteq> (1 / norm x) *\<^sub>R 0"
                    moreover
                    { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded l x /\<^sub>R norm x) = Rep_rbounded l x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 \<noteq> x /\<^sub>R norm x"
                      moreover
                      { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded l x /\<^sub>R norm x) = Rep_rbounded l x /\<^sub>R norm x \<and> norm x \<noteq> inverse (norm x)"
                        moreover
                        { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded l x /\<^sub>R norm x) = Rep_rbounded l x /\<^sub>R norm x \<and> 1 / norm x \<noteq> 0"
                          { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded l x /\<^sub>R norm x) = Rep_rbounded l x /\<^sub>R norm x \<and> (if 1 / norm x = 0 then norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x) = 0 else (1 / norm x) *\<^sub>R (Rep_rbounded l x /\<^sub>R norm x) = (1 / norm x) *\<^sub>R norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x))"
                            then have "(1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded l x /\<^sub>R norm x) = Rep_rbounded l x /\<^sub>R norm x \<and> (1 / norm x / (1 / norm x)) *\<^sub>R (Rep_rbounded l x /\<^sub>R norm x) = norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x)"
                              using vector_fraction_eq_iff by blast
                            then have "x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x) = Rep_rbounded l x"
                              using f1 by fastforce }
                          then have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x) = Rep_rbounded l x"
                            by fastforce }
                        ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x) = Rep_rbounded l x"
                          by force }
                      ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> 0 *\<^sub>R 0 = norm x *\<^sub>R x \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x) = Rep_rbounded l x"
                        by simp }
                    ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> (1 / norm x) *\<^sub>R 0 = x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 = norm x *\<^sub>R x \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x) = Rep_rbounded l x"
                      by simp }
                  ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = 0 \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x) = Rep_rbounded l x"
                    by simp }
                ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = 0 \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x) = Rep_rbounded l x"
                  by fastforce }
              ultimately have "norm x = 0 \<and> x = 0 \<longrightarrow> norm x *\<^sub>R Rep_rbounded l (x /\<^sub>R norm x) = Rep_rbounded l x"
                by auto }
            ultimately have ?thesis
              using f1 by auto }
          then show ?thesis
            by metis
        qed          
        thus ?thesis by StarDef.transfer
      qed
      ultimately show ?thesis by simp
    qed
  qed
  hence  \<open>(\<lambda>n. (Rep_rbounded (f n)) x) \<longlonglongrightarrow>\<^sub>N\<^sub>S (Rep_rbounded l) x\<close>
    by (simp add: NSLIMSEQ_I)
  thus ?thesis
    by (simp add: NSLIMSEQ_LIMSEQ)
qed



end

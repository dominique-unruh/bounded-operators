(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Bounded_Operators
  imports 
    Complex_Inner_Product 
    Banach_Steinhaus.Banach_Steinhaus
    "HOL-Types_To_Sets.Types_To_Sets"
begin

subsection \<open>Algebraic properties of real cblinfun operators\<close>

instantiation blinfun :: (real_normed_vector, complex_normed_vector) "complex_vector"
begin
lift_definition scaleC_blinfun :: \<open>complex \<Rightarrow>
 ('a::real_normed_vector, 'b::complex_normed_vector) blinfun \<Rightarrow>
 ('a, 'b) blinfun\<close>
  is \<open>\<lambda> c::complex. \<lambda> f::'a\<Rightarrow>'b. (\<lambda> x. c *\<^sub>C (f x) )\<close> 
proof
  fix c::complex and f :: \<open>'a\<Rightarrow>'b\<close> and b1::'a and b2::'a
  assume \<open>bounded_linear f\<close>
  show \<open>c *\<^sub>C f (b1 + b2) = c *\<^sub>C f b1 + c *\<^sub>C f b2\<close>
    by (simp add: \<open>bounded_linear f\<close> linear_simps scaleC_add_right)

  fix c::complex and f :: \<open>'a\<Rightarrow>'b\<close> and b::'a and r::real
  assume \<open>bounded_linear f\<close>
  show \<open>c *\<^sub>C f (r *\<^sub>R b) = r *\<^sub>R (c *\<^sub>C f b)\<close>
    by (simp add: \<open>bounded_linear f\<close> linear_simps(5) scaleR_scaleC)

  fix c::complex and f :: \<open>'a\<Rightarrow>'b\<close>
  assume \<open>bounded_linear f\<close>
  show \<open>\<exists>K. \<forall>x. norm (c *\<^sub>C f x) \<le> norm x * K \<close>
  proof-
    have \<open>\<exists> K. \<forall> x. norm (f x) \<le> norm x * K\<close>
      using \<open>bounded_linear f\<close>
      by (simp add: bounded_linear.bounded)      
    then obtain K where \<open>\<forall> x. norm (f x) \<le> norm x * K\<close>
      by blast
    have \<open>cmod c \<ge> 0\<close>
      by simp
    hence \<open>\<forall> x. (cmod c) * norm (f x) \<le> (cmod c) * norm x * K\<close>
      using  \<open>\<forall> x. norm (f x) \<le> norm x * K\<close> 
      by (metis ordered_comm_semiring_class.comm_mult_left_mono vector_space_over_itself.scale_scale)
    moreover have \<open>norm (c *\<^sub>C f x) = (cmod c) * norm (f x)\<close>
      for x
      by simp
    ultimately show ?thesis
      by (metis ab_semigroup_mult_class.mult_ac(1) mult.commute) 
  qed
qed

instance
proof
  show "((*\<^sub>R) r::('a, 'b) blinfun \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
  proof
    show "r *\<^sub>R (x::('a, 'b) blinfun) = complex_of_real r *\<^sub>C x"
      for x :: "('a, 'b) blinfun"
      apply transfer
      by (simp add: scaleR_scaleC)
  qed

  show "a *\<^sub>C ((x::('a, 'b) blinfun) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "('a, 'b) blinfun"
      and y :: "('a, 'b) blinfun"
    apply transfer
    by (simp add: scaleC_add_right)

  show "(a + b) *\<^sub>C (x::('a, 'b) blinfun) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) blinfun"
    apply transfer
    by (simp add: scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::('a, 'b) blinfun) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) blinfun"
    apply transfer
    by simp

  show "1 *\<^sub>C (x::('a, 'b) blinfun) = x"
    for x :: "('a, 'b) blinfun"
    apply transfer
  proof
    fix f :: \<open>'a\<Rightarrow>'b\<close> and x :: 'a
    show \<open>1 *\<^sub>C f x = f x\<close>
      by auto
  qed
qed  
end

instantiation blinfun :: (real_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
instance
proof intro_classes 
  {fix f::\<open>'a \<Rightarrow> 'b\<close> and a::complex
    assume \<open>bounded_linear f\<close>
    hence \<open>onorm (\<lambda>x. a *\<^sub>C f x) = (SUP x. norm (a *\<^sub>C f x) / norm x)\<close>
      by (simp add: onorm_def)
    also have \<open>... = (SUP x. ((cmod a) * norm (f x)) / norm x)\<close>
      by simp
    also have \<open>... =  (SUP x. (cmod a) * ((norm (f x)) / norm x))\<close>
      by simp
    also have \<open>... = (cmod a) *  (SUP x. ((norm (f x)) / norm x))\<close>
    proof-
      have \<open>(UNIV::('a set)) \<noteq> {}\<close>
        by simp
      moreover have \<open>\<And> i. i \<in> (UNIV::('a set)) \<Longrightarrow> (\<lambda> x. (norm (f x)) / norm x :: ereal) i \<ge> 0\<close>
        by simp
      moreover have \<open>cmod a \<ge> 0\<close>
        by simp
      ultimately have \<open>(SUP i\<in>(UNIV::('a set)). ((cmod a)::ereal) * (\<lambda> x. (norm (f x)) / norm x :: ereal) i ) 
        = ((cmod a)::ereal) * ( SUP i\<in>(UNIV::('a set)). (\<lambda> x. (norm (f x)) / norm x :: ereal) i )\<close>
        by (simp add: Sup_ereal_mult_left')
      hence \<open>(SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) ) 
        = ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) )\<close>
        by simp
      hence \<open>real_of_ereal ( (SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) ) )
        = real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )\<close>
        by simp
      moreover have \<open>real_of_ereal (SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) ) 
                  = (SUP x. cmod a * (norm (f x) / norm x))\<close>
      proof-
        have \<open>cmod a \<ge> 0\<close>
          by simp
        have \<open>\<bar> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. (cmod a) * (norm (f x)) / norm x) i)) \<bar> \<noteq> \<infinity>\<close>
        proof-
          have \<open>\<exists> K::real. \<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
            using \<open>bounded_linear f\<close> le_onorm by fastforce
          then obtain K::real where \<open>\<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
            by blast
          hence  \<open>\<forall> x. (cmod a) *(\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> (cmod a) * K\<close>
            using \<open>cmod a \<ge> 0\<close> 
            by (metis abs_ereal.simps(1) abs_ereal_pos   abs_pos ereal_mult_left_mono  times_ereal.simps(1))
          hence  \<open>\<forall> x.  (\<bar> ereal ((cmod a) * (norm (f x)) / (norm x)) \<bar>) \<le> (cmod a) * K\<close>
            by simp
          hence \<open>bdd_above {ereal (cmod a * (norm (f x)) / (norm x)) | x. True}\<close>
            by simp
          moreover have \<open>{ereal (cmod a * (norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
            by auto
          ultimately have \<open>(SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>) \<le> cmod a * K\<close>
            using \<open>\<forall> x. \<bar> ereal (cmod a * (norm (f x)) / (norm x)) \<bar> \<le> cmod a * K\<close>
              Sup_least mem_Collect_eq
            by (simp add: SUP_le_iff) 
          hence \<open>\<bar>SUP x. ereal (cmod a * (norm (f x)) / (norm x))\<bar>
              \<le> (SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>)\<close>
          proof-
            have  \<open>\<And>i. i \<in> UNIV \<Longrightarrow> 0 \<le> ereal (cmod a * norm (f i) / norm i)\<close>
              by simp              
            thus ?thesis
              using  \<open>bdd_above {ereal (cmod a * (norm (f x)) / (norm x)) | x. True}\<close>
                \<open>{ereal (cmod a * (norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
              by (metis (mono_tags, lifting) SUP_upper2 Sup.SUP_cong UNIV_I \<open>\<And>i. i \<in> UNIV \<Longrightarrow> 0 \<le> ereal (cmod a * norm (f i) / norm i)\<close> abs_ereal_ge0 ereal_le_real)
          qed
          hence \<open>\<bar>SUP x. ereal (cmod a * (norm (f x)) / (norm x))\<bar> \<le> cmod a * K\<close>
            using  \<open>(SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>) \<le> cmod a * K\<close>
            by simp
          thus ?thesis
            by auto 
        qed
        hence \<open> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. cmod a * (norm (f x)) / norm x) i))
             = ereal ( Sup ((\<lambda> x. cmod a * (norm (f x)) / norm x) ` (UNIV::'a set) ))\<close>
          by (simp add: ereal_SUP) 
        thus ?thesis
          by simp
      qed
      moreover have \<open>real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )
                = cmod a * (SUP x. norm (f x) / norm x)\<close>
      proof-
        have \<open>real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )
                =  (cmod a) * real_of_ereal ( SUP x. ( (norm (f x)) / norm x :: ereal) )\<close>
          by simp
        moreover have \<open>real_of_ereal ( SUP x. ( (norm (f x)) / norm x :: ereal) )
                  = ( SUP x. ((norm (f x)) / norm x) )\<close>
        proof-
          have \<open>\<bar> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. (norm (f x)) / norm x) i)) \<bar> \<noteq> \<infinity>\<close>
          proof-
            have \<open>\<exists> K::real. \<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
              using \<open>bounded_linear f\<close> le_onorm by fastforce
            then obtain K::real where \<open>\<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
              by blast
            hence \<open>bdd_above {ereal ((norm (f x)) / (norm x)) | x. True}\<close>
              by simp
            moreover have \<open>{ereal ((norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
              by auto
            ultimately have \<open>(SUP x. \<bar>ereal ((norm (f x)) / (norm x))\<bar>) \<le> K\<close>
              using \<open>\<forall> x. \<bar> ereal ((norm (f x)) / (norm x)) \<bar> \<le> K\<close>
                Sup_least mem_Collect_eq
              by (simp add: SUP_le_iff) 
            hence \<open>\<bar>SUP x. ereal ((norm (f x)) / (norm x))\<bar>
              \<le> (SUP x. \<bar>ereal ((norm (f x)) / (norm x))\<bar>)\<close>
              using  \<open>bdd_above {ereal ((norm (f x)) / (norm x)) | x. True}\<close>
                \<open>{ereal ((norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
              by (metis (mono_tags, lifting) SUP_upper2 Sup.SUP_cong UNIV_I \<open>\<And>i. i \<in> UNIV \<Longrightarrow> 0 \<le> ereal (norm (f i) / norm i)\<close> abs_ereal_ge0 ereal_le_real)
            hence \<open>\<bar>SUP x. ereal ((norm (f x)) / (norm x))\<bar> \<le> K\<close>
              using  \<open>(SUP x. \<bar>ereal ((norm (f x)) / (norm x))\<bar>) \<le> K\<close>
              by simp
            thus ?thesis
              by auto 
          qed
          hence \<open> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. (norm (f x)) / norm x) i))
             = ereal ( Sup ((\<lambda> x. (norm (f x)) / norm x) ` (UNIV::'a set) ))\<close>
            by (simp add: ereal_SUP) 
          thus ?thesis
            by simp         
        qed
        show ?thesis
          by (simp add: \<open>real_of_ereal (SUP x. ereal (norm (f x) / norm x)) = (SUP x. norm (f x) / norm x)\<close>)
      qed
      ultimately have \<open>(SUP x. cmod a * (norm (f x) / norm x)) =
          cmod a * (SUP x. norm (f x) / norm x)\<close>
        by simp     
      thus ?thesis
        by simp 
    qed
    hence \<open>onorm (\<lambda>x. a *\<^sub>C f x) = cmod a * onorm f\<close>
      by (simp add: onorm_def) 
  } note 1 = this 

  show \<open>norm (a *\<^sub>C x) = cmod a * norm x\<close> 
    for a::complex and x::\<open>('a, 'b) blinfun\<close>
    apply transfer
    apply (rule 1)
    by blast
qed
end

lemma trivia_UNIV_blinfun:
  fixes f::\<open>('a::real_normed_vector, 'b::real_normed_vector) blinfun\<close> 
  assumes \<open>(UNIV::'a set) = 0\<close>
  shows \<open>f = 0\<close>
proof-
  have \<open>x = 0\<close>
    for x::'a
    using \<open>(UNIV::'a set) = 0\<close> by auto
  moreover have \<open>bounded_linear (blinfun_apply f)\<close>
    using blinfun_apply by auto
  ultimately have \<open>blinfun_apply f x = 0\<close>
    for x::'a
    by (metis (full_types) linear_simps(3))
  hence \<open>blinfun_apply f = (\<lambda> _. 0)\<close>
    by blast
  moreover have \<open>blinfun_apply (Blinfun (\<lambda> _::'a. 0::'b)) = (\<lambda> _. 0)\<close>
    by (simp add: Blinfun_inverse)
  moreover have \<open>0 \<equiv> Blinfun (\<lambda> _::'a. 0::'b)\<close>
    using zero_blinfun_def by auto
  ultimately have \<open>blinfun_apply f = blinfun_apply 0\<close>
    by simp
  thus ?thesis using  blinfun_apply_inject 
    by auto
qed

subsection \<open>Topological properties of real cblinfun operators\<close>

lemma hnorm_unit_sphere:
  includes nsa_notation
  fixes f::\<open>nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
    and N::hypnat
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>N\<in>HNatInfinite\<close> 
  shows \<open>\<exists> x \<in> *s* (sphere 0 1). 
    hnorm ((*f* f) N) \<approx> hnorm ( (*f2* (\<lambda> n. (*\<^sub>v) (f n))) N x )\<close>
proof-
  have \<open>bounded_linear ((*\<^sub>v) (f n))\<close>
    for n
    using blinfun_apply by blast
  hence \<open>\<forall>e>0. \<exists> x\<in>(sphere 0 1).
      norm (norm(((*\<^sub>v) (f n)) x) - (onorm ((*\<^sub>v) (f n)))) < e\<close>
    for n
    using  \<open>(UNIV::'a set) \<noteq> 0\<close> norm_unit_sphere[where f = "Blinfun (f n)"]
    apply transfer apply auto
    by (metis bounded_linear_Blinfun_apply norm_blinfun.rep_eq)
  moreover have \<open>norm (f n) = onorm (blinfun_apply (f n))\<close> 
    for n
    apply transfer
    by blast
  ultimately have \<open>\<forall>e>0. \<exists> x\<in>(sphere 0 1).
       norm ( norm ((blinfun_apply (f n)) x) - norm (f n) ) < e\<close>
    for n
    by simp
  hence \<open>\<forall> n. \<exists> x\<in>(sphere 0 1).
       norm ( norm ((\<lambda> m. blinfun_apply (f m)) n x) - norm (f n) ) < inverse (real (Suc n))\<close>
    by auto
  hence \<open>\<forall> n. \<exists> x\<in>*s*(sphere 0 1).
       hnorm ( hnorm ( (*f2* (\<lambda> m. blinfun_apply (f m))) n x) - hnorm ((*f* f) n) ) 
            < inverse (hypreal_of_hypnat (hSuc n))\<close>
    by StarDef.transfer
  hence \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( hnorm ( (*f2* (\<lambda> m. blinfun_apply (f m))) N x) - hnorm ((*f* f) N) ) 
            < inverse (hypreal_of_hypnat (hSuc N))\<close>
    by blast
  moreover have \<open>inverse (hypreal_of_hypnat (hSuc N)) \<in> Infinitesimal\<close>
    using inv_hSuc_Infinite_Infinitesimal \<open>N\<in>HNatInfinite\<close>
    by blast
  ultimately have \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( (*f2* (\<lambda> m. blinfun_apply (f m))) N x) - hnorm ((*f* f) N) \<in> Infinitesimal\<close>
    using hnorm_less_Infinitesimal by blast
  hence \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( (*f2* (\<lambda> m. blinfun_apply (f m))) N x) \<approx> hnorm ((*f* f) N)\<close>
    using bex_Infinitesimal_iff by blast
  thus ?thesis
    using approx_sym by blast    
qed

lemma hnorm_unit_sphere_double:
  includes nsa_notation
  fixes f::\<open>nat \<Rightarrow> nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
    and N M::hypnat 
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close> 
  shows \<open>\<exists> x \<in> *s* (sphere 0 1). 
    hnorm ((*f2* f) N M) \<approx> hnorm ( (*f3* (\<lambda> n m. (*\<^sub>v) (f n m))) N M x )\<close>
proof-
  have \<open>bounded_linear (blinfun_apply (f n m))\<close>
    for n m
    using blinfun_apply by blast
  hence \<open>e>0 \<Longrightarrow> \<exists> x\<in>(sphere 0 1).
      norm (norm((blinfun_apply (f n m)) x) - (onorm (blinfun_apply (f n m)))) < e\<close>
    for n m e
    using norm_unit_sphere[where f = "f n m"] \<open>(UNIV::'a set) \<noteq> 0\<close> 
    apply transfer by auto     
  moreover have \<open>norm (f n m) = onorm (blinfun_apply (f n m))\<close> 
    for n m
    apply transfer
    by blast
  ultimately have \<open>\<forall>e>0. \<exists> x\<in>(sphere 0 1).
       norm ( norm ((blinfun_apply (f n m)) x) - norm (f n m) ) < e\<close>
    for n m
    by simp
  hence \<open>\<forall> n m. \<exists> x\<in>(sphere 0 1).
       norm ( norm ((\<lambda> n m. blinfun_apply (f n m)) n m x) - norm (f n m) ) < inverse (real (Suc n))\<close>
    by auto
  hence \<open>\<forall> n m. \<exists> x\<in>*s*(sphere 0 1).
       hnorm ( hnorm ( (*f3* (\<lambda> n m. blinfun_apply (f n m))) n m x) - hnorm ((*f2* f) n m) ) 
            < inverse (hypreal_of_hypnat (hSuc n))\<close>
    by StarDef.transfer
  hence \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( hnorm ( (*f3* (\<lambda> n m. blinfun_apply (f n m))) N M x) - hnorm ((*f2* f) N M) ) 
            < inverse (hypreal_of_hypnat (hSuc N))\<close>
    by blast
  moreover have \<open>inverse (hypreal_of_hypnat (hSuc N)) \<in> Infinitesimal\<close>
    using inv_hSuc_Infinite_Infinitesimal \<open>N\<in>HNatInfinite\<close>
    by blast
  ultimately have \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( (*f3* (\<lambda> n m. blinfun_apply (f n m))) N M x) - hnorm ((*f2* f) N M) \<in> Infinitesimal\<close>
    using hnorm_less_Infinitesimal by blast
  hence \<open>\<exists> x\<in>*s*(sphere 0 1).
       hnorm ( (*f3* (\<lambda> n m. blinfun_apply (f n m))) N M x) \<approx> hnorm ((*f2* f) N M)\<close>
    using bex_Infinitesimal_iff by blast
  thus ?thesis
    using approx_sym by blast    
qed

lemma uCauchy_unit_sphere:
  includes nsa_notation
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector,'b::real_normed_vector) blinfun\<close>
    and N M::hypnat
  assumes \<open>(UNIV::'a set) \<noteq> 0\<close> and \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close>
  shows  \<open>\<exists> x \<in>*s* (sphere 0 1). hnorm ( (*f* f) N - (*f* f) M )
         \<approx> hnorm( (*f2* (\<lambda> n. (*\<^sub>v) (f n))) N x - (*f2* (\<lambda> n. (*\<^sub>v) (f n))) M x )\<close>
proof-
  define g::\<open>nat \<Rightarrow> nat \<Rightarrow> ('a, 'b) blinfun\<close>
    where \<open>g n m = f n - f m\<close> for n and m
  have \<open>\<exists> x \<in> *s* (sphere 0 1). 
    hnorm ((*f2* g) N M) \<approx> hnorm ( (*f3* (\<lambda> n m. blinfun_apply (g n m))) N M x )\<close>
    using assms by (rule hnorm_unit_sphere_double)
  then obtain x where \<open>x \<in> *s* (sphere 0 1)\<close> and
    \<open>hnorm ((*f2* g) N M) \<approx> hnorm ( (*f3* (\<lambda> n m. blinfun_apply (g n m))) N M x )\<close>
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
  moreover have \<open>\<forall> N M x. hnorm ( (*f3* (\<lambda> n m. blinfun_apply (g n m))) N M x )
      = hnorm( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f2* (\<lambda> n. blinfun_apply (f n))) M x )\<close>
  proof-
    have \<open>\<forall>N M x. norm
           (( (\<lambda>n m. blinfun_apply (f n - f m))) N M x) =
          norm
           (( (\<lambda>n. blinfun_apply (f n))) N x -
            ( (\<lambda>n. blinfun_apply (f n))) M x)\<close>
      by (simp add: minus_blinfun.rep_eq)      
    hence \<open>\<forall>N M x. hnorm
           ((*f3* (\<lambda>n m. blinfun_apply (f n - f m))) N M x) =
          hnorm
           ((*f2* (\<lambda>n. blinfun_apply (f n))) N x -
            (*f2* (\<lambda>n. blinfun_apply (f n))) M x)\<close>
      by StarDef.transfer
    thus ?thesis unfolding g_def by blast
  qed
  ultimately show ?thesis using \<open>x \<in> *s* (sphere 0 1)\<close> 
      \<open>hnorm ((*f2* g) N M) \<approx> hnorm ( (*f3* (\<lambda> n m. blinfun_apply (g n m))) N M x )\<close>
    by auto
qed

lemma ustrong_onorm:
  fixes f::"nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector"
    and l::"'a \<Rightarrow>\<^sub>L 'b"
  assumes \<open>sphere 0 1: (\<lambda> n. (*\<^sub>v) (f n)) \<midarrow>uniformly\<rightarrow> ((*\<^sub>v) l)\<close>
  shows \<open>f \<longlonglongrightarrow> l\<close> 
proof(cases \<open>(UNIV::'a set) = 0\<close>)
  case True
  hence \<open>f n = 0\<close>
    for n
    by (rule trivia_UNIV_blinfun) 
  moreover have \<open>l = 0\<close>
    using True by (rule trivia_UNIV_blinfun)
  ultimately have \<open>( \<lambda> n. norm (f n - l) ) \<longlonglongrightarrow> 0\<close>
    by auto
  thus ?thesis
    using LIM_zero_cancel tendsto_norm_zero_iff by blast 
next
  case False
  include nsa_notation
  have \<open>N\<in>HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (star_of l)\<close>
    for N::hypnat
  proof-
    assume \<open>N\<in>HNatInfinite\<close>
    from \<open>sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> (blinfun_apply l)\<close>
    have \<open>NN\<in>HNatInfinite \<Longrightarrow> x \<in> *s* (sphere 0 1) \<Longrightarrow> 
              (*f2* (\<lambda> n. blinfun_apply (f n))) NN x \<approx> (*f* (blinfun_apply l)) x\<close>
      for x::\<open>'a star\<close> and NN::hypnat
      by (simp add: nsupointwise_convergence_D sphere_iff)
    hence \<open>x \<in> *s* (sphere 0 1) \<Longrightarrow> 
              (*f2* (\<lambda> n. blinfun_apply (f n))) N x \<approx> (*f* (blinfun_apply l)) x\<close>
      for x::\<open>'a star\<close>
      by (simp add: \<open>N \<in> HNatInfinite\<close>)
    hence \<open>x \<in> *s* (sphere 0 1) \<Longrightarrow> 
              (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x \<in> Infinitesimal\<close>
      for x::\<open>'a star\<close>
      using Infinitesimal_approx_minus by blast
    hence \<open>x \<in> *s* (sphere 0 1) \<Longrightarrow> 
             hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x ) \<in> Infinitesimal\<close>
      for x::\<open>'a star\<close>
      by (simp add: Infinitesimal_hnorm_iff)
    moreover have \<open>\<exists> x\<in> *s* (sphere 0 1). hnorm ((*f* f) N - (star_of l)) \<approx>
        hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )\<close>
    proof-
      define g where \<open>g n = f n - l\<close> for n
      have \<open>\<exists> x \<in> *s* (sphere 0 1). 
        hnorm ((*f* g) N) \<approx> hnorm ( (*f2* (\<lambda> n. blinfun_apply (g n))) N x )\<close>
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
      moreover have \<open>(*f2* (\<lambda> n. blinfun_apply (g n))) N x
         = (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x\<close>
        for x
      proof-
        have  \<open>\<forall> NN xx. ( (\<lambda> n. blinfun_apply (g n))) NN xx
         = ( (\<lambda> n. blinfun_apply (f n))) NN xx - ( (blinfun_apply l)) xx\<close>
          unfolding g_def
          by (simp add: minus_blinfun.rep_eq) 
        hence  \<open>\<forall> NN xx. (*f2* (\<lambda> n. blinfun_apply (g n))) NN xx
         = (*f2* (\<lambda> n. blinfun_apply (f n))) NN xx - (*f* (blinfun_apply l)) xx\<close>
          by StarDef.transfer
        thus ?thesis by auto
      qed
      ultimately show \<open>\<exists> x\<in> *s* (sphere 0 1). hnorm ((*f* f) N - (star_of l)) \<approx>
        hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )\<close>
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
  fixes f::\<open>nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
  assumes \<open>Cauchy f\<close>
  shows \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. (*\<^sub>v) (f n))\<close>
proof-
  include nsa_notation
  have  \<open>N\<in>HNatInfinite \<Longrightarrow> M\<in>HNatInfinite \<Longrightarrow> x\<in>*s* (sphere 0 1) \<Longrightarrow> 
    (*f2* (\<lambda> n. blinfun_apply (f n))) N x \<approx> (*f2* (\<lambda> n. blinfun_apply (f n))) M x\<close>
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
    moreover have \<open>hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x
                                 - (*f2* (\<lambda> n. blinfun_apply (f n))) M x )
        \<le> hnorm ((*f* f) N - (*f* f) M)\<close>
    proof-
      have \<open>bounded_linear (blinfun_apply (f n))\<close>
        for n
        using blinfun_apply by blast
      hence \<open>bounded_linear (\<lambda> x. blinfun_apply (f n) x - blinfun_apply (f m) x )\<close>
        for n m
        by (simp add: bounded_linear_sub)    
      moreover have \<open>\<And>NN MM xx.
       (\<And>n m. bounded_linear (\<lambda>x. blinfun_apply (f n) x - blinfun_apply (f m) x)) \<Longrightarrow>
       norm xx = 1 \<Longrightarrow>
       norm (blinfun_apply (f NN) xx - blinfun_apply (f MM) xx) \<le> onorm (blinfun_apply (f NN - f MM))\<close>
        using onorm
        by (metis (no_types, hide_lams) blinfun_apply mem_Collect_eq minus_blinfun.rep_eq mult.commute mult.left_neutral)        
      ultimately have \<open>\<forall> NN MM xx. norm xx = 1 \<longrightarrow> norm ( ( (\<lambda> n. blinfun_apply (f n))) NN xx
                                 - ( (\<lambda> n. blinfun_apply (f n))) MM xx )
        \<le> norm (( f) NN - ( f) MM)\<close>
        unfolding norm_blinfun_def
        by auto
      hence \<open>\<forall> NN MM xx. hnorm xx = 1 \<longrightarrow> hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) NN xx
                                 - (*f2* (\<lambda> n. blinfun_apply (f n))) MM xx )
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
    moreover have \<open>hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f2* (\<lambda> n. blinfun_apply (f n))) M x ) \<ge> 0\<close>
    proof-
      have \<open>norm ( ( (\<lambda> n. blinfun_apply (f n))) NN xx - ( (\<lambda> n. blinfun_apply (f n))) MM xx ) \<ge> 0\<close>
        for NN MM xx
        by auto
      thus ?thesis by auto 
    qed
    ultimately have \<open>hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f2* (\<lambda> n. blinfun_apply (f n))) M x ) \<in> Infinitesimal\<close>
      using Infinitesimal_interval2 by blast
    thus ?thesis
      using bex_Infinitesimal_iff hnorm_le_Infinitesimal by blast 
  qed
  thus ?thesis using nsuniformly_Cauchy_on_I by metis
qed


lemma uCauchy_oCauchy:
  fixes f::\<open>nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
  assumes \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. (*\<^sub>v) (f n))\<close> 
  shows \<open>Cauchy f\<close>
proof(cases \<open>(UNIV::('a set)) = 0\<close>)
  case True
  hence \<open>f n = 0\<close>
    for n
    by (rule trivia_UNIV_blinfun) 
  moreover have \<open>Cauchy (\<lambda> n. 0::('a,'b) blinfun)\<close>
    unfolding Cauchy_def by auto
  ultimately show ?thesis
    by presburger 
next
  case False
  include nsa_notation
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (*f* f) M\<close>
    for N M
  proof-
    assume \<open>N \<in> HNatInfinite\<close> and \<open>M \<in> HNatInfinite\<close>
    have \<open>x \<in>*s* (sphere 0 1) \<Longrightarrow> 
      (*f2* (\<lambda> n. blinfun_apply (f n))) N x \<approx> (*f2* (\<lambda> n. blinfun_apply (f n))) M x\<close>
      for x
      using \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. blinfun_apply (f n))\<close>
      by (simp add: \<open>M \<in> HNatInfinite\<close> \<open>N \<in> HNatInfinite\<close> nsuniformly_Cauchy_on_iff)    
    hence \<open>x \<in>*s* (sphere 0 1) \<Longrightarrow> 
      hnorm( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f2* (\<lambda> n. blinfun_apply (f n))) M x ) \<in> Infinitesimal\<close>
      for x
      using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by blast
    moreover have \<open>\<exists> x \<in>*s* (sphere 0 1). hnorm ( (*f* f) N - (*f* f) M )
         \<approx> hnorm( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f2* (\<lambda> n. blinfun_apply (f n))) M x )\<close>
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
  fixes f::\<open>nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
  shows \<open>Cauchy f \<longleftrightarrow> uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. (*\<^sub>v) (f n))\<close>
proof
  show "uniformly_Cauchy_on (sphere 0 1) (\<lambda>n. blinfun_apply (f n))"
    if "Cauchy f"
    using that
    by (simp add: oCauchy_uCauchy) 
  show "Cauchy f"
    if "uniformly_Cauchy_on (sphere 0 1) (\<lambda>n. blinfun_apply (f n))"
    using that
    by (simp add: uCauchy_oCauchy) 
qed


lemma uCauchy_ustrong:
  fixes f::\<open>nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::banach\<close>
  assumes \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. (*\<^sub>v) (f n))\<close>
  shows  \<open>\<exists> l::'a \<Rightarrow>\<^sub>L 'b. 
    (sphere 0 1): (\<lambda> n. (*\<^sub>v) (f n)) \<midarrow>uniformly\<rightarrow> (*\<^sub>v) l\<close>
proof-
  include nsa_notation
  from \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. blinfun_apply (f n))\<close>
  have \<open>\<exists> s::'a\<Rightarrow>'b.
 (sphere 0 1): (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
    using uniformly_convergent_eq_Cauchy uniformly_convergent_on_def by blast
  then obtain s::\<open>'a\<Rightarrow>'b\<close> where
    \<open>(sphere 0 1): (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
    by blast
  have \<open>\<exists> L. \<forall> x\<in>(sphere 0 1). blinfun_apply L x = s x\<close>
  proof-
    define l::\<open>'a \<Rightarrow> 'b\<close> where \<open>l x = (norm x) *\<^sub>R s ((inverse (norm x)) *\<^sub>R x)\<close>
      for x::'a       
    have \<open>t \<in> sphere 0 1 \<Longrightarrow> (\<lambda>x. norm x *\<^sub>R s (x /\<^sub>R norm x)) t = s t\<close>
      for t
      unfolding sphere_def
      by simp
    hence \<open>sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> l\<close>
      using  \<open>sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
      unfolding l_def 
      by (metis (no_types, lifting) uniform_limit_cong') 
    hence \<open>x \<in> sphere 0 1 \<Longrightarrow> l x = s x\<close>
      for x
      using  \<open>sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
      by (meson LIMSEQ_unique tendsto_uniform_limitI)
    have \<open>bounded_linear l\<close>
    proof-
      have \<open>\<And> n. bounded_linear (blinfun_apply (f n))\<close>
        using blinfun_apply by blast
      have \<open>(\<lambda> n. blinfun_apply (f n) x) \<longlonglongrightarrow> l x\<close>
        for x
      proof(cases \<open>x = 0\<close>)
        case True
        have \<open>(\<lambda> n. blinfun_apply (f n) x) \<longlonglongrightarrow> 0\<close>
        proof-
          have \<open>blinfun_apply (f n) x = (0::'b)\<close>
            for n
          proof-
            have \<open>\<And> n. bounded_linear (blinfun_apply (f n))\<close>
              using blinfun_apply by blast 
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
          have  \<open>(\<lambda> n. (blinfun_apply (f n)) (x  /\<^sub>R norm x)) \<longlonglongrightarrow> s (x /\<^sub>R norm x)\<close>
          proof-
            have \<open>\<forall> N\<in>HNatInfinite. \<forall>x\<in>*s* (sphere 0 1).
                     (*f2* (\<lambda> n. blinfun_apply (f n))) N x \<approx> (*f* s) x\<close>
              using \<open>sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close> nsuniform_convergence_D 
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
               (*f2* (\<lambda> n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x)) \<approx> (*f* s) (star_of (x /\<^sub>R norm x))\<close>
              by blast 
            moreover have \<open>\<forall> N. (*f2* (\<lambda> n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x))
                        \<approx> (*f* (\<lambda> n. blinfun_apply (f n) (x /\<^sub>R norm x) )) N\<close>
            proof-
              have  \<open>\<forall> N. ( (\<lambda> n. blinfun_apply (f n))) N ( (x /\<^sub>R norm x))
                        = ( (\<lambda> n. blinfun_apply (f n) (x /\<^sub>R norm x) )) N\<close>
                by blast
              hence \<open>\<forall> N. (*f2* (\<lambda> n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x))
                        = (*f* (\<lambda> n. blinfun_apply (f n) (x /\<^sub>R norm x) )) N\<close>
                by StarDef.transfer
              thus ?thesis
                by simp 
            qed
            ultimately have  \<open>\<forall> N\<in>HNatInfinite.
               (*f* (\<lambda> n. blinfun_apply (f n) (x /\<^sub>R norm x) )) N \<approx> (*f* s) (star_of (x /\<^sub>R norm x))\<close>
              using approx_trans3 by blast                 
            hence \<open> (\<lambda>n. blinfun_apply (f n)  (x /\<^sub>R norm x)) \<longlonglongrightarrow>\<^sub>N\<^sub>S s  (x /\<^sub>R norm x)\<close>
              using NSLIMSEQ_def
              by (metis starfun_eq)              
            thus ?thesis
              by (simp add: NSLIMSEQ_LIMSEQ)              
          qed
          hence  \<open>(\<lambda> n. (norm x) *\<^sub>R (blinfun_apply (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow>  (norm x) *\<^sub>R  s (x /\<^sub>R norm x)\<close>
            using bounded_linear.tendsto bounded_linear_scaleR_right by blast
          hence  \<open>(\<lambda> n. (norm x) *\<^sub>R (blinfun_apply (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
            using l_def
            by simp
          have  \<open>(\<lambda> n. (blinfun_apply(f n)) x) \<longlonglongrightarrow> l x\<close>
          proof-
            have \<open>(norm x) *\<^sub>R (blinfun_apply (f n)) (x /\<^sub>R norm x) = (blinfun_apply (f n)) x\<close>
              for n
              using \<open>norm x \<noteq> 0\<close> \<open>\<And> n. bounded_linear (blinfun_apply (f n))\<close>
              unfolding cbounded_linear_def linear_def
              by (simp add: \<open>\<And>n. bounded_linear (blinfun_apply (f n))\<close> linear_simps(5))               
            thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R (blinfun_apply (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close> 
              by simp
          qed
          thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R (blinfun_apply (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
            by auto
        qed
      qed
      have \<open>linear l\<close>
      proof
        show "l (b1 + b2) = l b1 + l b2"
          for b1 :: 'a
            and b2 :: 'a
        proof-
          have \<open>(\<lambda> n. (blinfun_apply (f n)) (b1 + b2)) \<longlonglongrightarrow> l (b1 + b2)\<close>
            using  \<open>\<And> x. (\<lambda> n. (blinfun_apply (f n)) x) \<longlonglongrightarrow> l x\<close>
            by blast
          moreover have \<open>(\<lambda> n. (blinfun_apply (f n)) (b1 + b2)) \<longlonglongrightarrow> l b1 + l b2\<close>
          proof-
            have \<open>(\<lambda> n. (blinfun_apply (f n))  b1) \<longlonglongrightarrow> l b1\<close>
              using  \<open>\<And> x. (\<lambda> n. (blinfun_apply (f n))  x) \<longlonglongrightarrow> l x\<close>
              by blast
            moreover have \<open>(\<lambda> n. (blinfun_apply (f n))  b2) \<longlonglongrightarrow> l b2\<close>
              using  \<open>\<And> x. (\<lambda> n.  (blinfun_apply (f n))  x) \<longlonglongrightarrow> l x\<close>
              by blast
            ultimately have \<open>(\<lambda> n. (blinfun_apply (f n))  b1 +  (blinfun_apply (f n))  b2) \<longlonglongrightarrow> l b1 + l b2\<close>
              by (simp add: tendsto_add) 
            moreover have \<open>(\<lambda> n.  (blinfun_apply (f n))  (b1 + b2)) = (\<lambda> n.  (blinfun_apply (f n))  b1 +  (blinfun_apply (f n))  b2)\<close>
            proof-
              have \<open> (blinfun_apply (f n))  (b1 + b2) =  (blinfun_apply (f n))  b1 +  (blinfun_apply (f n))  b2\<close>
                for n
                using \<open>\<And> n. bounded_linear  (blinfun_apply (f n))\<close>
                unfolding bounded_linear_def
                by (simp add: real_vector.linear_add)                
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
          have \<open>(\<lambda> n.  (blinfun_apply (f n))  (r *\<^sub>R b)) \<longlonglongrightarrow> l (r *\<^sub>R b)\<close>
            using  \<open>\<And> x. (\<lambda> n.  (blinfun_apply (f n))  x) \<longlonglongrightarrow> l x\<close>
            by blast
          moreover have \<open>(\<lambda> n.  (blinfun_apply (f n))  (r *\<^sub>R b)) \<longlonglongrightarrow>  r *\<^sub>R (l b)\<close>
          proof-
            have \<open>(\<lambda> n.  (blinfun_apply (f n))  b) \<longlonglongrightarrow> l b\<close>
              using  \<open>\<And> x. (\<lambda> n.  (blinfun_apply (f n))  x) \<longlonglongrightarrow> l x\<close>
              by blast
            hence \<open>(\<lambda> n. r *\<^sub>R ( (blinfun_apply (f n))  b)) \<longlonglongrightarrow> r *\<^sub>R (l b)\<close>
              using bounded_linear.tendsto bounded_linear_scaleR_right by blast
            moreover have \<open>(\<lambda> n. ( (blinfun_apply (f n))  (r *\<^sub>R b))) = (\<lambda> n. r *\<^sub>R ( (blinfun_apply (f n))  b))\<close>
            proof-
              have \<open> (blinfun_apply (f n))  (r *\<^sub>R b) = r *\<^sub>R ( (blinfun_apply (f n))  b)\<close>
                for n
                using \<open>\<And> n. bounded_linear (blinfun_apply (f n))\<close>
                unfolding bounded_linear_def
                by (simp add: real_vector.linear_scale)
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
            using calculation linear_0
            by (smt norm_eq_zero real_vector.linear_0 vector_space_over_itself.scale_eq_0_iff)
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
                  using \<open>linear l\<close> linear_scale
                  by (simp add: real_vector.linear_scale)
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
          from \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. blinfun_apply (f n))\<close>
          have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x\<in>(sphere 0 1). dist ((blinfun_apply (f m)) x) (blinfun_apply (f n) x) < e\<close>
            by (meson uniformly_Cauchy_on_def)
          hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x\<in>(sphere 0 1). norm (((blinfun_apply (f m)) x) - (blinfun_apply (f n) x)) < e\<close>
            by (simp add: dist_norm) 
          hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (((blinfun_apply (f m)) x) - (blinfun_apply (f n) x)) < e\<close>
            unfolding sphere_def by auto
          hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm ((blinfun_apply (f m)) x - (blinfun_apply (f n)) x) < 1\<close>
            by auto
          then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm ((blinfun_apply (f m)) x - (blinfun_apply (f n)) x) < 1\<close>
            by blast
          hence  \<open>\<forall>m\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm ((blinfun_apply (f m)) x - (blinfun_apply (f M)) x) < 1\<close>
            by blast
          have \<open>norm ((blinfun_apply (f m)) x) \<le> norm ((blinfun_apply (f M)) x) + norm ((blinfun_apply (f m)) x - (blinfun_apply (f M)) x)\<close>
            for m and x
            by (simp add: norm_triangle_sub) 
          hence \<open>norm ((blinfun_apply (f m)) x) \<le> onorm (blinfun_apply (f M)) * norm x + norm ((blinfun_apply (f m)) x - (blinfun_apply (f M)) x)\<close>
            for m and x
            using onorm  \<open>\<And>n. bounded_linear (blinfun_apply (f n))\<close>
            by smt                    
          hence \<open>norm x = 1 \<Longrightarrow> norm ((blinfun_apply (f m)) x) \<le> onorm (blinfun_apply (f M)) + norm ((blinfun_apply (f m)) x - (blinfun_apply (f M)) x)\<close>
            for m and x
            by (metis mult_cancel_left2)
          hence \<open>m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm ((blinfun_apply (f m)) x) < onorm (blinfun_apply (f M)) + 1\<close>
            for m and x
            using  \<open>\<forall>m\<ge>M. \<forall>x. 
            norm x = 1 \<longrightarrow> norm ((blinfun_apply (f m)) x - (blinfun_apply (f M)) x) < 1\<close> 
            by smt
          have \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. (blinfun_apply (f m)) x) \<longlonglongrightarrow> l x\<close>
            for x
            by (simp add: \<open>\<And>x. (\<lambda>n. (blinfun_apply (f n)) x) \<longlonglongrightarrow> l x\<close>)
          hence \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. norm ((blinfun_apply (f m)) x)) \<longlonglongrightarrow> norm (l x)\<close>
            for x
            by (simp add: tendsto_norm)
          hence \<open>norm x = 1 \<Longrightarrow> norm (l x) \<le> onorm (blinfun_apply (f M)) + 1\<close>
            for x
          proof-
            assume \<open>norm x = 1\<close>
            hence \<open>(\<lambda> m. norm ((blinfun_apply (f m)) x)) \<longlonglongrightarrow> norm (l x)\<close>
              using  \<open>\<And> x. norm x = 1 \<Longrightarrow> (\<lambda> m. norm ((blinfun_apply (f m)) x)) \<longlonglongrightarrow> norm (l x)\<close>
              by blast
            moreover have \<open>\<forall>  m \<ge> M. norm ((blinfun_apply (f m)) x) \<le> onorm (blinfun_apply (f M)) + 1\<close>
              using  \<open>\<And> m. \<And> x.  m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm ((blinfun_apply (f m)) x) < onorm (blinfun_apply (f M)) + 1\<close>
                \<open>norm x = 1\<close> by smt
            ultimately show ?thesis 
              by (rule Topological_Spaces.Lim_bounded)
          qed
          moreover have  \<open>\<exists> x. norm x = 1 \<and> onorm (blinfun_apply (f M)) + 1 < norm (l x)\<close>
            by (simp add: \<open>\<forall>K. \<exists>x. norm x = 1 \<and> K < norm (l x)\<close>)
          ultimately show ?thesis
            by fastforce 
        qed
        thus ?thesis unfolding bounded_linear_axioms_def by blast 
      qed
      ultimately show ?thesis unfolding bounded_linear_def by blast
    qed
    hence \<open>\<exists> L. blinfun_apply L = l\<close>
      using blinfun_apply_cases by auto
    thus ?thesis
      using \<open>\<And>x. x \<in> sphere 0 1 \<Longrightarrow> l x = s x\<close> 
      by blast        
  qed
  then obtain L::\<open>('a,'b) blinfun\<close> where \<open>\<forall> x\<in>(sphere 0 1). (blinfun_apply L) x = s x\<close>
    by blast
  have "sphere 0 1: (\<lambda>n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> blinfun_apply L"
    using  \<open>\<forall> x\<in>(sphere 0 1). (blinfun_apply L) x = s x\<close>  \<open>(sphere 0 1): (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
    by (metis (no_types, lifting) uniform_limit_cong')
  thus ?thesis by blast
qed  

lemma onorm_ustrong:
  fixes f::\<open>nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
    and l::\<open>'a \<Rightarrow>\<^sub>L 'b\<close> 
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(sphere 0 1): (\<lambda> n. (*\<^sub>v) (f n)) \<midarrow>uniformly\<rightarrow> (*\<^sub>v) l\<close>
proof-
  include nsa_notation
  have \<open>N\<in>HNatInfinite \<Longrightarrow> x \<in> *s* (sphere 0 1) \<Longrightarrow>
       (*f2* (\<lambda> n. blinfun_apply (f n))) N x \<approx> (*f* (blinfun_apply l)) x\<close>
    for N and x
  proof-
    assume \<open>N\<in>HNatInfinite\<close> and \<open>x \<in> *s* (sphere 0 1)\<close>
    have \<open>(*f* f) N \<approx> (star_of l)\<close>
      using \<open>f \<longlonglongrightarrow> l\<close> \<open>N\<in>HNatInfinite\<close>
      by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_D)
    hence \<open>hnorm ( (*f* f) N - (star_of l) ) \<in> Infinitesimal\<close>
      using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by auto
    moreover have \<open>hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )
                \<le> hnorm ( (*f* f) N - (star_of l) )\<close>
    proof-
      have \<open>bounded_linear (\<lambda> t. blinfun_apply (f N) t - blinfun_apply l t)\<close>
        for N
        using blinfun_apply bounded_linear_sub by auto
      hence \<open>norm x = 1 \<Longrightarrow>
           norm (blinfun_apply (f N) x - blinfun_apply l x)
           \<le> onorm (\<lambda> t. blinfun_apply (f N) t - blinfun_apply l t)\<close>
        for N x
        by (metis (no_types) mult.commute mult.left_neutral onorm)
      moreover have \<open> (\<lambda> t. blinfun_apply (f N) t - blinfun_apply l t) = blinfun_apply (f N - l)\<close>
        for N
        apply transfer
        by auto
      ultimately have \<open>norm x = 1 \<Longrightarrow>
           norm (blinfun_apply (f N) x - blinfun_apply l x)
           \<le> onorm (blinfun_apply (f N - l))\<close>
        for N x
        by simp
      hence \<open>\<forall> N. \<forall> x. x \<in>  (sphere 0 1) \<longrightarrow> 
         norm ( ( (\<lambda> n. blinfun_apply (f n))) N x - ( (blinfun_apply l)) x )
                \<le> norm ( ( f) N - ( l) )\<close>
        unfolding norm_blinfun_def
        by auto
      hence \<open>\<forall> N. \<forall> x. x \<in> *s* (sphere 0 1) \<longrightarrow> 
         hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )
                \<le> hnorm ( (*f* f) N - (star_of l) )\<close>
        by StarDef.transfer
      thus ?thesis using \<open>x\<in>*s* (sphere 0 1)\<close> by blast
    qed
    moreover have \<open>0 \<le> hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )\<close>
      by simp      
    ultimately have \<open>hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )
            \<in> Infinitesimal\<close>
      using Infinitesimal_interval2 by blast
    thus ?thesis
      by (simp add: Infinitesimal_approx_minus Infinitesimal_hnorm_iff) 
  qed
  hence \<open>(sphere 0 1): (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> blinfun_apply l\<close>
    by (simp add: nsupointwise_convergence_I sphere_iff)    
  thus ?thesis by blast
qed

proposition onorm_ustrong_iff:
  fixes f::\<open>nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
    and l::\<open>'a  \<Rightarrow>\<^sub>L 'b\<close> 
  shows \<open>(f \<longlonglongrightarrow> l) \<longleftrightarrow> (sphere 0 1): (\<lambda> n. (*\<^sub>v) (f n)) \<midarrow>uniformly\<rightarrow> (*\<^sub>v) l\<close>
proof
  show "sphere 0 1: (\<lambda>n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> blinfun_apply l"
    if "f \<longlonglongrightarrow> l"
    using that
    using onorm_ustrong by blast 
  show "f \<longlonglongrightarrow> l"
    if "sphere 0 1: (\<lambda>n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> blinfun_apply l"
    using that
    by (simp add: that ustrong_onorm) 
qed

theorem completeness_real_cblinfun:
  fixes f::\<open>nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::banach\<close>
  assumes \<open>Cauchy f\<close>
  shows \<open>\<exists> L. f \<longlonglongrightarrow> L\<close>
proof-
  have  \<open>\<And> n. bounded_linear (blinfun_apply (f n))\<close>
    using blinfun_apply by auto
  hence \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. blinfun_apply (f n))\<close>
    using oCauchy_uCauchy  \<open>Cauchy f\<close> by blast
  hence \<open>\<exists> L. sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> blinfun_apply L\<close>
    using uCauchy_ustrong
    by blast
  then obtain L where \<open>sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> blinfun_apply L\<close>
    by blast
  thus ?thesis 
    using ustrong_onorm Lim_null tendsto_norm_zero_cancel by fastforce 
qed


instantiation blinfun :: (real_normed_vector, cbanach) "cbanach"
begin
instance..
end

lemma onorm_strong:
  fixes f::\<open>nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
    and l::\<open>'a  \<Rightarrow>\<^sub>L 'b\<close> and x::'a
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda>n. (blinfun_apply (f n)) x) \<longlonglongrightarrow> (blinfun_apply l) x\<close>
proof-
  include nsa_notation
  have \<open>N\<in>HNatInfinite \<Longrightarrow> (*f* (\<lambda>n. (blinfun_apply (f n)) x)) N \<approx> star_of ((blinfun_apply l) x)\<close>
    for N
  proof-
    assume \<open>N\<in>HNatInfinite\<close>
    show ?thesis 
    proof(cases \<open>x = 0\<close>)
      case True
      have \<open>(blinfun_apply (f n)) x = 0\<close>
        for n
      proof-
        have \<open>bounded_linear (blinfun_apply (f n))\<close>
          using blinfun_apply by blast
        thus ?thesis
          using \<open>x = 0\<close>
          by (simp add: linear_simps(3))          
      qed
      moreover have \<open>(blinfun_apply l) x = 0\<close>
      proof-
        have \<open>bounded_linear (blinfun_apply l)\<close>
          using blinfun_apply by blast
        thus ?thesis 
          using \<open>x = 0\<close>
          by (simp add: linear_simps(3))          
      qed
      ultimately have \<open>(blinfun_apply (f n)) x = (blinfun_apply l) x\<close>
        for n
        by simp
      hence \<open>star_of ((blinfun_apply (f n)) x) = star_of ((blinfun_apply l) x)\<close>
        for n
        by StarDef.transfer
      hence \<open>(*f* (\<lambda> n. (blinfun_apply (f n)) x)) N = star_of ((blinfun_apply l) x)\<close>
        by auto
      thus ?thesis by auto 
    next
      case False
      from \<open>f \<longlonglongrightarrow> l\<close>
      have \<open>sphere 0 1: (\<lambda>n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> (blinfun_apply l)\<close>
        using onorm_ustrong by blast
      hence \<open>t \<in> *s*(sphere 0 1) \<Longrightarrow> (*f2* (\<lambda>n. blinfun_apply (f n))) N t \<approx> (*f* (blinfun_apply l)) t\<close>
        for t
        using \<open>N \<in> HNatInfinite\<close> nsupointwise_convergence_D sphere_iff by blast
      moreover have \<open>star_of (x /\<^sub>R norm x) \<in> *s*(sphere 0 1)\<close>
      proof-
        have \<open>(x /\<^sub>R norm x) \<in> (sphere 0 1)\<close>
          using False unfolding sphere_def by auto
        thus ?thesis by StarDef.transfer
      qed
      ultimately have \<open>(*f2* (\<lambda>n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x)) 
          \<approx> (*f* (blinfun_apply l)) (star_of (x /\<^sub>R norm x))\<close>
        by blast
      hence \<open>(*f2* scaleR) (star_of (norm x)) ( (*f2* (\<lambda>n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x)) ) 
          \<approx> (*f2* scaleR) (star_of (norm x)) ( (*f* (blinfun_apply l)) (star_of (x /\<^sub>R norm x)) )\<close>
        using approx_scaleR2 star_scaleR_def starfun2_star_of
        by metis
      moreover have \<open>(*f2* scaleR) (star_of (norm x)) ( (*f2* (\<lambda>n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x)) )
          = (*f* (\<lambda>n. blinfun_apply (f n) x)) N\<close>
      proof-
        have \<open>bounded_linear (blinfun_apply (f n))\<close>
          for n
          using blinfun_apply by auto          
        hence \<open>\<forall> N. ( scaleR) ( (norm x)) ( ( (\<lambda>n. blinfun_apply (f n))) N ( (x /\<^sub>R norm x)) )
          = ( (\<lambda>n. blinfun_apply (f n) x)) N\<close>
        proof - \<comment> \<open>Sledgehammer proof\<close>
          have f1: "blinfun_apply (f v0_0) (x /\<^sub>R norm x) = blinfun_apply (f v0_0) x /\<^sub>R norm x"
            using \<open>\<And>n. bounded_linear (blinfun_apply (f n))\<close> linear_simps(5) by blast
          obtain nn :: nat where
            "(\<exists>v0. norm x *\<^sub>R blinfun_apply (f v0) (x /\<^sub>R norm x) \<noteq> blinfun_apply (f v0) x) = (norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) \<noteq> blinfun_apply (f nn) x)"
            by meson
          moreover
          { assume "norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) \<noteq> blinfun_apply (f nn) x"
            hence "norm x *\<^sub>R (x /\<^sub>R norm x) \<noteq> 0 \<or> x \<noteq> 0"
              by (metis \<open>\<And>n. bounded_linear (blinfun_apply (f n))\<close> linear_simps(5))
            moreover
            { assume "norm x *\<^sub>R (x /\<^sub>R norm x) \<noteq> 0"
              moreover
              { assume "norm x *\<^sub>R x /\<^sub>R norm x \<noteq> norm x *\<^sub>R (x /\<^sub>R norm x)"
                moreover
                { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = blinfun_apply (f nn) x /\<^sub>R norm x \<and> norm x *\<^sub>R x /\<^sub>R norm x \<noteq> norm x *\<^sub>R (x /\<^sub>R norm x)"
                  moreover
                  { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = blinfun_apply (f nn) x /\<^sub>R norm x \<and> 0 *\<^sub>R (0::'a) \<noteq> (1 / norm x) *\<^sub>R 0"
                    moreover
                    { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = blinfun_apply (f nn) x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 \<noteq> x /\<^sub>R norm x"
                      moreover
                      { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = blinfun_apply (f nn) x /\<^sub>R norm x \<and> norm x \<noteq> inverse (norm x)"
                        moreover
                        { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = blinfun_apply (f nn) x /\<^sub>R norm x \<and> 1 / norm x \<noteq> 0"
                          { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = blinfun_apply (f nn) x /\<^sub>R norm x \<and> (if 1 / norm x = 0 then norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) = 0 else (1 / norm x) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = (1 / norm x) *\<^sub>R norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x))"
                            hence "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = blinfun_apply (f nn) x /\<^sub>R norm x \<and> (1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x)"
                              using vector_fraction_eq_iff
                              using \<open>(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = blinfun_apply (f nn) x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 \<noteq> (1 / norm x) *\<^sub>R 0\<close> by auto
                            hence "x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) = blinfun_apply (f nn) x"
                              using f1
                              using \<open>(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply (f nn) x /\<^sub>R norm x) = blinfun_apply (f nn) x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 \<noteq> (1 / norm x) *\<^sub>R 0\<close> scaleR_cong_right by blast  }
                          hence "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) = blinfun_apply (f nn) x"
                            by fastforce }
                        ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) = blinfun_apply (f nn) x"
                          by fastforce }
                      ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> 0 *\<^sub>R 0 = norm x *\<^sub>R x \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) = blinfun_apply (f nn) x"
                        by auto }
                    ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> (1 / norm x) *\<^sub>R 0 = x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 = norm x *\<^sub>R x \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) = blinfun_apply (f nn) x"
                      by auto }
                  ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = 0 \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) = blinfun_apply (f nn) x"
                    by auto }
                ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = 0 \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) = blinfun_apply (f nn) x"
                  by fastforce }
              ultimately have "norm x = 0 \<and> x = 0 \<longrightarrow> norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) = blinfun_apply (f nn) x"
                by (simp add: inverse_eq_divide) }
            ultimately have "norm x *\<^sub>R blinfun_apply (f nn) (x /\<^sub>R norm x) = blinfun_apply (f nn) x"
              using f1
              by (simp add: \<open>\<And>n. bounded_linear (blinfun_apply (f n))\<close> linear_simps(5))  }
          ultimately show ?thesis
            by meson
        qed       
        hence  \<open>\<forall> N. (*f2* scaleR) (star_of (norm x)) ( (*f2* (\<lambda>n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x)) )
          = (*f* (\<lambda>n. blinfun_apply (f n) x)) N\<close>
          by StarDef.transfer
        thus ?thesis by blast
      qed
      moreover have \<open>(*f2* scaleR) (star_of (norm x)) ( (*f* (blinfun_apply l)) (star_of (x /\<^sub>R norm x)) )
            = star_of (blinfun_apply l x)\<close> 
      proof-
        have \<open>bounded_linear (blinfun_apply l)\<close>
          using blinfun_apply by auto          
        hence \<open>( scaleR) ( (norm x)) ( ( (blinfun_apply l)) ( (x /\<^sub>R norm x)) )
            =  (blinfun_apply l x)\<close>
        proof - \<comment> \<open>Sledgehammer proof\<close>
          have f1: "blinfun_apply l (x /\<^sub>R norm x) = blinfun_apply l x /\<^sub>R norm x"
            by (meson \<open>bounded_linear (blinfun_apply l)\<close> linear_simps(5))
          { assume "norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x) \<noteq> blinfun_apply l x"
            hence "norm x *\<^sub>R (x /\<^sub>R norm x) \<noteq> 0 \<or> x \<noteq> 0"
              by (metis \<open>bounded_linear (blinfun_apply l)\<close> linear_simps(5))
            moreover
            { assume "norm x *\<^sub>R (x /\<^sub>R norm x) \<noteq> 0"
              moreover
              { assume "norm x *\<^sub>R x /\<^sub>R norm x \<noteq> norm x *\<^sub>R (x /\<^sub>R norm x)"
                moreover
                { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply l x /\<^sub>R norm x) = blinfun_apply l x /\<^sub>R norm x \<and> norm x *\<^sub>R x /\<^sub>R norm x \<noteq> norm x *\<^sub>R (x /\<^sub>R norm x)"
                  moreover
                  { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply l x /\<^sub>R norm x) = blinfun_apply l x /\<^sub>R norm x \<and> 0 *\<^sub>R (0::'a) \<noteq> (1 / norm x) *\<^sub>R 0"
                    moreover
                    { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply l x /\<^sub>R norm x) = blinfun_apply l x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 \<noteq> x /\<^sub>R norm x"
                      moreover
                      { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply l x /\<^sub>R norm x) = blinfun_apply l x /\<^sub>R norm x \<and> norm x \<noteq> inverse (norm x)"
                        moreover
                        { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply l x /\<^sub>R norm x) = blinfun_apply l x /\<^sub>R norm x \<and> 1 / norm x \<noteq> 0"
                          { assume "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply l x /\<^sub>R norm x) = blinfun_apply l x /\<^sub>R norm x \<and> (if 1 / norm x = 0 then norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x) = 0 else (1 / norm x) *\<^sub>R (blinfun_apply l x /\<^sub>R norm x) = (1 / norm x) *\<^sub>R norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x))"
                            hence "(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply l x /\<^sub>R norm x) = blinfun_apply l x /\<^sub>R norm x \<and> (1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply l x /\<^sub>R norm x) = norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x)"
                              using vector_fraction_eq_iff
                              using \<open>(1 / norm x / (1 / norm x)) *\<^sub>R (blinfun_apply l x /\<^sub>R norm x) = blinfun_apply l x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 \<noteq> (1 / norm x) *\<^sub>R 0\<close> by auto
                            hence "x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x) = blinfun_apply l x"
                              using f1 by fastforce }
                          hence "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x) = blinfun_apply l x"
                            by fastforce }
                        ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x) = blinfun_apply l x"
                          by force }
                      ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> 0 *\<^sub>R 0 = norm x *\<^sub>R x \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x) = blinfun_apply l x"
                        by simp }
                    ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> (1 / norm x) *\<^sub>R 0 = x /\<^sub>R norm x \<and> 0 *\<^sub>R 0 = norm x *\<^sub>R x \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x) = blinfun_apply l x"
                      by simp }
                  ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = 0 \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x) = blinfun_apply l x"
                    by simp }
                ultimately have "norm x = 0 \<and> 1 / 0 = inverse (norm x) \<and> x = 0 \<and> x = x /\<^sub>R norm x \<longrightarrow> norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x) = blinfun_apply l x"
                  by fastforce }
              ultimately have "norm x = 0 \<and> x = 0 \<longrightarrow> norm x *\<^sub>R blinfun_apply l (x /\<^sub>R norm x) = blinfun_apply l x"
                by auto }
            ultimately have ?thesis
              using f1 by auto }
          thus ?thesis
            by metis
        qed          
        thus ?thesis by StarDef.transfer
      qed
      ultimately show ?thesis by simp
    qed
  qed
  hence  \<open>(\<lambda>n. (blinfun_apply (f n)) x) \<longlonglongrightarrow>\<^sub>N\<^sub>S (blinfun_apply l) x\<close>
    by (simp add: NSLIMSEQ_I)
  thus ?thesis
    by (simp add: NSLIMSEQ_LIMSEQ)
qed

lemma times_blinfun_assoc: "(A o\<^sub>L B)  o\<^sub>L C = A  o\<^sub>L (B  o\<^sub>L C)" 
  apply transfer
  by (simp add: comp_assoc) 

lemma times_blinfun_dist1:
  fixes a b :: "('b::real_normed_vector, 'c::real_normed_vector) blinfun"
    and c :: "('a::real_normed_vector, 'b) blinfun"
  shows "(a + b)  o\<^sub>L c = (a  o\<^sub>L c) + (b o\<^sub>L c)"
proof -
  (* sledgehammer *)
  {  fix aa :: "'b \<Rightarrow> 'c" and ba :: "'b \<Rightarrow> 'c" and ca :: "'a \<Rightarrow> 'b"
    assume a1: "bounded_linear ca"
    assume a2: "bounded_linear ba"
    assume a3: "bounded_linear aa"
    { fix aaa :: 'a
      have ff1: "\<forall>r. blinfun_apply (r::('b, 'c) blinfun) \<circ> ca = blinfun_apply (r  o\<^sub>L Blinfun ca)"
        using a1
        by (simp add: blinfun_compose.rep_eq bounded_linear_Blinfun_apply) 
      have ff2: "blinfun_apply (Blinfun ba) = ba"
        using a2 by (meson Blinfun_inverse mem_Collect_eq)
      have "blinfun_apply (Blinfun aa) = aa"
        using a3 by (metis Blinfun_inverse mem_Collect_eq)
      hence "Blinfun ((\<lambda>b. aa b + ba b) \<circ> ca) = Blinfun (\<lambda>a. blinfun_apply (Blinfun (aa \<circ> ca)) a + blinfun_apply (Blinfun (ba \<circ> ca)) a) \<or> ((\<lambda>b. aa b + ba b) \<circ> ca) aaa = blinfun_apply (Blinfun (aa \<circ> ca)) aaa + blinfun_apply (Blinfun (ba \<circ> ca)) aaa"
        using ff2 ff1 by (metis (no_types) blinfun_apply_inverse comp_apply) }
    hence "Blinfun ((\<lambda>b. aa b + ba b) \<circ> ca) = Blinfun (\<lambda>a. blinfun_apply (Blinfun (aa \<circ> ca)) a + blinfun_apply (Blinfun (ba \<circ> ca)) a)"
      by meson
  } note 1 = this

  show ?thesis
    apply transfer
    unfolding plus_blinfun_def
    by auto  
qed

lemma times_blinfun_dist2:
  fixes a b :: "'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector"
    and c :: "'b  \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  shows "c  o\<^sub>L (a + b) = (c o\<^sub>L a) + (c o\<^sub>L b)"
proof-
  have \<open>blinfun_apply (c  o\<^sub>L (a + b)) x = blinfun_apply ( (c  o\<^sub>L a) +  (c  o\<^sub>L b) ) x\<close>
    for x
  proof-
    have \<open>bounded_linear (blinfun_apply c)\<close>
      using blinfun_apply by auto
    have \<open>blinfun_apply (c  o\<^sub>L (a + b)) x = (blinfun_apply c) ( (blinfun_apply (a + b)) x )\<close>
      by simp
    also have \<open>\<dots> = (blinfun_apply c) ( blinfun_apply a x + blinfun_apply b x )\<close>
      by (simp add: plus_blinfun.rep_eq)
    also have \<open>\<dots> = (blinfun_apply c) ( blinfun_apply a x ) + (blinfun_apply c) ( blinfun_apply b x )\<close>
      using  \<open>bounded_linear (blinfun_apply c)\<close>
      unfolding cbounded_linear_def linear_def
      by (simp add: \<open>bounded_linear (blinfun_apply c)\<close> linear_simps(1))
    also have \<open>\<dots> = ( (blinfun_apply c) \<circ> (blinfun_apply a) ) x
                  + ( (blinfun_apply c) \<circ> (blinfun_apply b) ) x\<close>
      by simp
    finally have \<open>blinfun_apply (c o\<^sub>L (a + b)) x = blinfun_apply ( (c o\<^sub>L a) +  (c o\<^sub>L b) ) x\<close>
      by (simp add: blinfun.add_left)      
    thus ?thesis
      by simp 
  qed
  hence \<open>blinfun_apply (c  o\<^sub>L (a + b)) = blinfun_apply ( (c  o\<^sub>L a) +  (c  o\<^sub>L b) )\<close>
    by blast
  thus ?thesis 
    using blinfun_apply_inject
    by blast  
qed

lemma times_blinfun_scaleC:
  fixes f::"'b::complex_normed_vector \<Rightarrow>\<^sub>L'c::complex_normed_vector" 
    and g::"'a::complex_normed_vector \<Rightarrow>\<^sub>L 'b"
  assumes \<open>\<forall> c. \<forall> x. (*\<^sub>v) f (c *\<^sub>C x) = c *\<^sub>C ((*\<^sub>v) f x)\<close>
    and \<open>\<forall> c. \<forall> x. (*\<^sub>v) g (c *\<^sub>C x) = c *\<^sub>C ((*\<^sub>v) g x)\<close>
  shows \<open>\<forall> c. \<forall> x. (*\<^sub>v) (f  o\<^sub>L g) (c *\<^sub>C x) = c *\<^sub>C ((*\<^sub>v) (f  o\<^sub>L g) x)\<close>
  by (simp add: assms(1) assms(2))

lemma rscalar_op_op: 
  fixes A::"'b::real_normed_vector \<Rightarrow>\<^sub>L 'c::complex_normed_vector" 
    and B::"'a::real_normed_vector \<Rightarrow>\<^sub>L 'b"
  shows \<open>(a *\<^sub>C A)  o\<^sub>L B = a *\<^sub>C (A  o\<^sub>L B)\<close>
proof-
  have \<open>(blinfun_apply (a *\<^sub>C A) \<circ> blinfun_apply B) x =
    blinfun_apply (a *\<^sub>C Blinfun (blinfun_apply A \<circ> blinfun_apply B)) x\<close>
    for x
  proof-
    have \<open>(blinfun_apply (a *\<^sub>C A) \<circ> blinfun_apply B) x
       = a *\<^sub>C (blinfun_apply A ((blinfun_apply B) x))\<close>
      by (simp add: scaleC_blinfun.rep_eq)
    moreover have \<open>blinfun_apply (a *\<^sub>C Blinfun (blinfun_apply A \<circ> blinfun_apply B)) x
        = a *\<^sub>C (blinfun_apply ( Blinfun (blinfun_apply A \<circ> blinfun_apply B)) x)\<close>
      by (simp add: scaleC_blinfun.rep_eq)
    moreover have \<open>(blinfun_apply A ((blinfun_apply B) x))
        = (blinfun_apply ( Blinfun (blinfun_apply A \<circ> blinfun_apply B)) x)\<close>
    proof-
      have \<open>blinfun_apply A ((blinfun_apply B) x) = ((blinfun_apply A \<circ> blinfun_apply B)) x\<close>
        by simp        
      thus ?thesis
        using Blinfun_inverse
        by (metis blinfun_apply blinfun_compose.rep_eq)        
    qed
    ultimately show ?thesis by simp
  qed
  hence \<open>(blinfun_apply (a *\<^sub>C A) \<circ> blinfun_apply B) =
    blinfun_apply (a *\<^sub>C Blinfun (blinfun_apply A \<circ> blinfun_apply B))\<close>
    by blast
  hence \<open>Blinfun (blinfun_apply (a *\<^sub>C A) \<circ> blinfun_apply B) =
    a *\<^sub>C Blinfun (blinfun_apply A \<circ> blinfun_apply B)\<close>
    by (simp add: blinfun_apply_inverse)    
  thus ?thesis
    by (metis blinfun_apply_inverse blinfun_compose.rep_eq)    
qed


lemma op_rscalar_op: 
  fixes A::"'b::complex_normed_vector  \<Rightarrow>\<^sub>L 'c::complex_normed_vector" 
    and B::"'a::real_normed_vector  \<Rightarrow>\<^sub>L  'b"
  assumes \<open>\<forall> c. \<forall> x. A *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (A *\<^sub>v x)\<close>
  shows \<open>A  o\<^sub>L (a *\<^sub>C B) = a *\<^sub>C (A  o\<^sub>L B)\<close>
proof-
  have \<open>blinfun_apply (A o\<^sub>L (a *\<^sub>C B)) x  = blinfun_apply ((a *\<^sub>C A) o\<^sub>L B) x\<close>
    for x
  proof-
    have \<open>blinfun_apply (A o\<^sub>L (a *\<^sub>C B)) x
        = ( (blinfun_apply A) \<circ> (blinfun_apply (a *\<^sub>C B)) ) x\<close>
      by simp
    also have \<open>... = 
        (blinfun_apply A) ( (blinfun_apply (a *\<^sub>C B))  x )\<close>
      by simp
    also have \<open>... = 
        (blinfun_apply A) (a *\<^sub>C ( (blinfun_apply  B) x ))\<close>
      by (simp add: scaleC_blinfun.rep_eq)
    also have \<open>... = 
       a *\<^sub>C ( (blinfun_apply A) ( (blinfun_apply  B) x ) )\<close>
      using assms by auto      
    finally show ?thesis
      by (simp add: scaleC_blinfun.rep_eq)       
  qed
  hence \<open>blinfun_apply (A o\<^sub>L (a *\<^sub>C B))  = blinfun_apply ((a *\<^sub>C A) o\<^sub>L B)\<close>
    by blast     
  hence \<open>A o\<^sub>L (a *\<^sub>C B) = (a *\<^sub>C A) o\<^sub>L B\<close>
    using blinfun_apply_inject by auto    
  thus ?thesis
    by (simp add: rscalar_op_op)  
qed

subsection \<open>On-demand syntax\<close>

subsection \<open>Complex cblinfun operators\<close>

typedef\<^marker>\<open>tag important\<close> (overloaded) ('a, 'b) cblinfun ("(_ \<Rightarrow>\<^sub>C\<^sub>L /_)" [22, 21] 21) =
  "{f::'a::complex_normed_vector\<Rightarrow>'b::complex_normed_vector. cbounded_linear f}"
  morphisms cblinfun_apply cBlinfun
  using cbounded_linear_zero by blast

setup_lifting type_definition_cblinfun


declare [[coercion
      "cblinfun_apply :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'b"]]

notation cblinfun_apply (infixr "*\<^sub>V" 70)

lift_definition blinfun_of_cblinfun::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun
\<Rightarrow> ('a,'b) blinfun\<close> is "id"
  apply transfer apply auto
  by (simp add: cbounded_linear.bounded_linear)

lemma blinfun_of_cblinfun_inj:
  \<open>blinfun_of_cblinfun f = blinfun_of_cblinfun g \<Longrightarrow> f = g\<close>
  by (metis cblinfun_apply_inject blinfun_of_cblinfun.rep_eq)

lemma blinfun_of_cblinfun_inv:
  \<open>\<forall> c. \<forall> x. blinfun_apply f (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply f x) \<Longrightarrow> \<exists> g. blinfun_of_cblinfun g = f\<close>
  apply transfer apply auto
  by (simp add: bounded_linear_cbounded_linear)

lemma blinfun_of_cblinfun_inv_uniq:
  \<open>\<forall> c. \<forall> x. blinfun_apply f (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply f x) \<Longrightarrow> \<exists>! g. blinfun_of_cblinfun g = f\<close>
  using blinfun_of_cblinfun_inv blinfun_of_cblinfun_inj
  by blast

lemma blinfun_of_cblinfun_prelim:
  \<open>\<forall> c. \<forall> x. blinfun_apply (blinfun_of_cblinfun g) (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply (blinfun_of_cblinfun g) x)\<close>
  apply transfer
  apply auto
  using cbounded_linear_def
  by (simp add: cbounded_linear_def complex_vector.linear_scale)

definition cblinfun_of_blinfun::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) blinfun \<Rightarrow>
('a, 'b) cblinfun\<close> where
  \<open>cblinfun_of_blinfun = inv blinfun_of_cblinfun\<close>

lemma cblinfun_blinfun:
  \<open>cblinfun_of_blinfun (blinfun_of_cblinfun f) = f\<close>
  by (metis (no_types, hide_lams) cblinfun_apply_inverse UNIV_I cblinfun_of_blinfun_def f_inv_into_f image_iff blinfun_of_cblinfun.rep_eq)

lemma blinfun_cblinfun:
  \<open>\<forall> c. \<forall> x. blinfun_apply f (c *\<^sub>C x)
 = c *\<^sub>C (blinfun_apply f x)
 \<Longrightarrow> blinfun_of_cblinfun (cblinfun_of_blinfun f) = f\<close>
  by (metis blinfun_of_cblinfun_inv cblinfun_blinfun) 


instantiation cblinfun :: (complex_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
lift_definition zero_cblinfun::"('a,'b) cblinfun" is "\<lambda>_. 0" by simp

lemma cblinfun_of_blinfun_zero:
  "(0::('a::complex_normed_vector,'b::complex_normed_vector) cblinfun) = cblinfun_of_blinfun (0::('a,'b) blinfun)" 
proof-
  have \<open>cblinfun_apply 0 t  = cblinfun_apply (SOME x. Blinfun (cblinfun_apply x) = 0) t\<close>
    for t
  proof-
    have \<open>cblinfun_apply (SOME x. Blinfun (cblinfun_apply x) = 0) t = 0\<close>
      by (metis (mono_tags, lifting) cBlinfun_inverse blinfun_apply_inverse cbounded_linear_zero mem_Collect_eq blinfun_of_cblinfun.rep_eq tfl_some zero_blinfun.abs_eq)
    moreover have \<open>cblinfun_apply 0 t = 0\<close>
      apply transfer by blast
    ultimately show ?thesis by simp
  qed
  hence \<open>cblinfun_apply 0  = cblinfun_apply (SOME x. Blinfun (cblinfun_apply x) = 0) \<close>
    by blast
  hence \<open>0 = (SOME x. Blinfun (cblinfun_apply x) = 0)\<close>
    using cblinfun_apply_inject
    by blast
  hence \<open>0 = inv (Blinfun \<circ> cblinfun_apply) 0\<close>
    unfolding inv_def
    by auto
  hence \<open>0 = inv (map_fun cblinfun_apply Blinfun id) 0\<close>
    unfolding map_fun_def 
    by auto
  thus ?thesis
    unfolding cblinfun_of_blinfun_def blinfun_of_cblinfun_def inv_def
    by blast
qed

lemma blinfun_of_cblinfun_zero:
  \<open>blinfun_of_cblinfun 0 = 0\<close>
  apply transfer by simp


lift_definition plus_cblinfun::"('a,'b) cblinfun \<Rightarrow> ('a,'b) cblinfun \<Rightarrow> ('a,'b) cblinfun" is
  "\<lambda>f g x. f x + g x"
  by (rule cbounded_linear_add)

(* TODO remove *)
(* Jose: If I remove it, there are errors *)
lemma blinfun_of_cblinfun_plus:
  fixes f g :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L'b\<close> 
  shows "blinfun_of_cblinfun (f + g) =  (blinfun_of_cblinfun f)+(blinfun_of_cblinfun g)"
  unfolding cblinfun_of_blinfun_def blinfun_of_cblinfun_def inv_def
  apply auto
  apply transfer
  by (simp add: cbounded_linear.bounded_linear eq_onp_same_args plus_blinfun.abs_eq)

lemma cblinfun_of_blinfun_plus:
  assumes \<open>\<And>c. \<And>x. blinfun_apply f (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply f x)\<close>
    and \<open>\<And>c. \<And>x. blinfun_apply g (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply g x)\<close>
  shows \<open>cblinfun_of_blinfun (f + g) = cblinfun_of_blinfun f + cblinfun_of_blinfun g\<close>
  using assms
  by (metis blinfun_of_cblinfun_plus blinfun_cblinfun blinfun_of_cblinfun_inj blinfun_of_cblinfun_prelim)

lift_definition uminus_cblinfun::"('a,'b) cblinfun \<Rightarrow> ('a,'b) cblinfun" is
  "\<lambda>f x. - f x"
  by (rule Complex_Vector_Spaces.cbounded_linear_minus)

lemma blinfun_of_cblinfun_uminus:
  \<open>blinfun_of_cblinfun (- f) = - (blinfun_of_cblinfun f)\<close>
  apply transfer
  by auto

lemma cblinfun_of_blinfun_uminus:
  assumes \<open>\<And>c. \<And>x. blinfun_apply f (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply f x)\<close>
  shows  \<open>cblinfun_of_blinfun (- f) = - (cblinfun_of_blinfun f)\<close>
  using assms
  by (metis (mono_tags) blinfun_cblinfun blinfun_of_cblinfun_inj blinfun_of_cblinfun_prelim blinfun_of_cblinfun_uminus)

lift_definition minus_cblinfun::"('a,'b) cblinfun \<Rightarrow> ('a,'b) cblinfun \<Rightarrow> ('a,'b) cblinfun" is
  "\<lambda>f g x. f x - g x"
  by (rule Complex_Vector_Spaces.cbounded_linear_sub)

lemma blinfun_of_cblinfun_minus:
  \<open>blinfun_of_cblinfun (f - g) = blinfun_of_cblinfun f - blinfun_of_cblinfun g\<close>
  apply transfer
  by auto

lemma cblinfun_of_blinfun_minus:
  assumes \<open>\<forall> c. \<forall> x. blinfun_apply f (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply f x)\<close>
    and \<open>\<forall> c. \<forall> x. blinfun_apply g (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply g x)\<close>
  shows \<open>cblinfun_of_blinfun (f - g) = cblinfun_of_blinfun f - cblinfun_of_blinfun g\<close>
  using assms
  unfolding cblinfun_of_blinfun_def inv_def
  by (smt cblinfun_blinfun blinfun_cblinfun blinfun_of_cblinfun_minus someI_ex)

lift_definition scaleC_cblinfun :: \<open>complex \<Rightarrow> ('a, 'b) cblinfun \<Rightarrow> ('a, 'b) cblinfun\<close>
  is  "\<lambda> c f x. c *\<^sub>C (f x)"
  by (rule Complex_Vector_Spaces.cbounded_linear_const_scaleC)


lemma blinfun_of_cblinfun_scaleC:
  \<open>blinfun_of_cblinfun ( c *\<^sub>C f ) = c *\<^sub>C (blinfun_of_cblinfun f)\<close>
  apply transfer
  by auto

lemma cblinfun_of_blinfun_scaleC:
  assumes \<open>\<forall> c. \<forall> x. blinfun_apply f (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply f x)\<close>
  shows \<open>cblinfun_of_blinfun ( c *\<^sub>C f ) = c *\<^sub>C (cblinfun_of_blinfun f)\<close>
  using assms
  by (metis (mono_tags) cblinfun_blinfun blinfun_cblinfun blinfun_of_cblinfun_scaleC)


lift_definition scaleR_cblinfun :: \<open>real \<Rightarrow> ('a, 'b) cblinfun \<Rightarrow> ('a, 'b) cblinfun\<close>
  is  "\<lambda> c f x. c *\<^sub>R (f x)"
  by (rule Complex_Vector_Spaces.scalarR_cbounded_linear)

lemma blinfun_of_cblinfun_scaleR:
  \<open>blinfun_of_cblinfun (c *\<^sub>R f) = c *\<^sub>R (blinfun_of_cblinfun f)\<close>
  apply transfer by auto

lemma cblinfun_of_blinfun_scaleR:
  assumes \<open>\<forall> c. \<forall> x. blinfun_apply f (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply f x)\<close>
  shows \<open>cblinfun_of_blinfun ( c *\<^sub>R f ) = c *\<^sub>R (cblinfun_of_blinfun f)\<close>
  using assms
  by (metis (mono_tags) cblinfun_blinfun blinfun_cblinfun blinfun_of_cblinfun_scaleR)

lemma cblinfun_of_blinfun_Blinfun:
  \<open>cblinfun_of_blinfun ( Blinfun (cblinfun_apply f) ) = f\<close>
  by (metis Quotient_cblinfun Quotient_rel_rep cblinfun_apply_inverse cblinfun_blinfun blinfun_of_cblinfun.abs_eq)

lift_definition norm_cblinfun :: \<open>('a, 'b) cblinfun \<Rightarrow> real\<close>
  is onorm.

lemma blinfun_of_cblinfun_norm:
  fixes f::\<open>('a, 'b) cblinfun\<close>
  shows \<open>norm f = norm (blinfun_of_cblinfun f)\<close>
  apply transfer
  by auto

lift_definition dist_cblinfun :: \<open>('a, 'b) cblinfun \<Rightarrow> ('a, 'b) cblinfun \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. onorm (\<lambda> x. f x - g x)\<close>.

lemma blinfun_of_cblinfun_dist:
  fixes f::\<open>('a, 'b) cblinfun\<close>
  shows \<open>dist f g = dist (blinfun_of_cblinfun f) (blinfun_of_cblinfun g)\<close>
  unfolding dist_cblinfun_def dist_blinfun_def apply auto apply transfer
  by auto

definition sgn_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  where "sgn_cblinfun x = scaleR (inverse (norm x)) x"

lemma blinfun_of_cblinfun_sgn:
  \<open>blinfun_of_cblinfun (sgn f) = (sgn (blinfun_of_cblinfun f))\<close>
  by (simp add: sgn_cblinfun_def sgn_blinfun_def
      blinfun_of_cblinfun_scaleR blinfun_of_cblinfun_norm)

definition uniformity_cblinfun :: \<open>( ('a, 'b) cblinfun \<times> ('a, 'b) cblinfun ) filter\<close>
  where \<open>uniformity_cblinfun = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a, 'b) cblinfun) y < e})\<close>

definition open_cblinfun :: \<open>(('a, 'b) cblinfun) set \<Rightarrow> bool\<close>
  where \<open>open_cblinfun U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::('a, 'b) cblinfun) = x \<longrightarrow> y \<in> U)\<close>

instance
proof
  show \<open>a + b + c = a + (b + c)\<close>
    for a :: "('a, 'b) cblinfun"
      and b :: "('a, 'b) cblinfun"
      and c :: "('a, 'b) cblinfun"
  proof -
    have f1: "\<forall>r ra. ((\<exists>c a. blinfun_apply r (c *\<^sub>C (a::'a)) \<noteq> c *\<^sub>C (blinfun_apply r a::'b)) \<or> (\<exists>c a. blinfun_apply ra (c *\<^sub>C a) \<noteq> c *\<^sub>C blinfun_apply ra a)) \<or> cblinfun_of_blinfun (r + ra) = cblinfun_of_blinfun r + cblinfun_of_blinfun ra"
      using cblinfun_of_blinfun_plus by blast
    obtain cc :: "('a, 'b) blinfun \<Rightarrow> complex" and aa :: "('a, 'b) blinfun \<Rightarrow> 'a" where
      "\<forall>x0. (\<exists>v2 v3. blinfun_apply x0 (v2 *\<^sub>C v3) \<noteq> v2 *\<^sub>C blinfun_apply x0 v3) = (blinfun_apply x0 (cc x0 *\<^sub>C aa x0) \<noteq> cc x0 *\<^sub>C blinfun_apply x0 (aa x0))"
      by moura
    then obtain cca :: "('a, 'b) blinfun \<Rightarrow> complex" and aaa :: "('a, 'b) blinfun \<Rightarrow> 'a" where
      f2: "\<forall>r ra. (blinfun_apply r (cca r *\<^sub>C aaa r) \<noteq> cca r *\<^sub>C blinfun_apply r (aaa r) \<or> blinfun_apply ra (cc ra *\<^sub>C aa ra) \<noteq> cc ra *\<^sub>C blinfun_apply ra (aa ra)) \<or> cblinfun_of_blinfun (r + ra) = cblinfun_of_blinfun r + cblinfun_of_blinfun ra"
      using f1 by simp
    hence "cblinfun_of_blinfun (blinfun_of_cblinfun a + blinfun_of_cblinfun b + blinfun_of_cblinfun c) = cblinfun_of_blinfun (blinfun_of_cblinfun a + blinfun_of_cblinfun b) + cblinfun_of_blinfun (blinfun_of_cblinfun c)"
      by (simp add: plus_blinfun.rep_eq blinfun_of_cblinfun_prelim scaleC_add_right)
    hence f3: "cblinfun_of_blinfun (blinfun_of_cblinfun a + (blinfun_of_cblinfun b + blinfun_of_cblinfun c)) = a + b + c"
      by (metis (mono_tags, lifting) ab_semigroup_add_class.add_ac(1) cblinfun_blinfun blinfun_of_cblinfun_plus)
    have "cblinfun_of_blinfun (blinfun_of_cblinfun a) + cblinfun_of_blinfun (blinfun_of_cblinfun b + blinfun_of_cblinfun c) = a + (b + c)"
      by (metis cblinfun_blinfun blinfun_of_cblinfun_plus)
    thus ?thesis
      using f3 f2 by (simp add: plus_blinfun.rep_eq blinfun_of_cblinfun_prelim scaleC_add_right)
  qed

  show \<open>(0::('a, 'b) cblinfun) + a = a\<close>
    for a :: "('a, 'b) cblinfun"
  proof -
    have "blinfun_of_cblinfun (map_fun cblinfun_apply (map_fun cblinfun_apply cBlinfun) (\<lambda>f fa a. f a + fa a) 0 a) = blinfun_of_cblinfun 0 + blinfun_of_cblinfun a"
      using Bounded_Operators.blinfun_of_cblinfun_plus plus_cblinfun_def by auto
    hence "map_fun cblinfun_apply (map_fun cblinfun_apply cBlinfun) (\<lambda>f fa a. f a + fa a) 0 a = a"
      by (simp add: Bounded_Operators.blinfun_of_cblinfun_zero blinfun_of_cblinfun_inj)
    thus ?thesis
      unfolding plus_cblinfun_def
      by blast
  qed

  show \<open>a + b = b + a\<close>
    for a :: "('a, 'b) cblinfun"
      and b :: "('a, 'b) cblinfun"
    by (simp add: add.commute plus_cblinfun_def)

  show \<open>- a + a = 0\<close>
    for a :: "('a, 'b) cblinfun"
    by (metis (mono_tags) add.left_inverse cblinfun_of_blinfun_zero cblinfun_blinfun blinfun_of_cblinfun_plus blinfun_of_cblinfun_uminus)

  show \<open>a - b = a + - b\<close>
    for a :: "('a, 'b) cblinfun"
      and b :: "('a, 'b) cblinfun"
    by (metis (mono_tags, lifting) ab_group_add_class.ab_diff_conv_add_uminus blinfun_of_cblinfun_inj blinfun_of_cblinfun_minus blinfun_of_cblinfun_plus blinfun_of_cblinfun_uminus)

  show \<open>((*\<^sub>R) r::('a, 'b) cblinfun \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
    for r :: real
  proof-
    have \<open>r *\<^sub>R cblinfun_apply f t =
          complex_of_real r *\<^sub>C cblinfun_apply f t\<close>
      for f::\<open>('a, 'b) cblinfun\<close> and t
      by (simp add: scaleR_scaleC)      
    hence \<open>(\<lambda>t. r *\<^sub>R cblinfun_apply f t) t =
          (\<lambda>t. complex_of_real r *\<^sub>C cblinfun_apply f t) t\<close>
      for f::\<open>('a, 'b) cblinfun\<close> and t
      by simp      
    hence \<open>(\<lambda>t. r *\<^sub>R cblinfun_apply f t) =
          (\<lambda>t. complex_of_real r *\<^sub>C cblinfun_apply f t)\<close>
      for f::\<open>('a, 'b) cblinfun\<close>
      by simp
    hence \<open>cBlinfun (\<lambda>t. r *\<^sub>R cblinfun_apply f t) =
    cBlinfun
          (\<lambda>t. complex_of_real r *\<^sub>C cblinfun_apply f t)\<close>
      for f::\<open>('a, 'b) cblinfun\<close>
      by simp
    hence \<open>(\<lambda>f. cBlinfun (\<lambda>t. r *\<^sub>R cblinfun_apply f t)) f =
    (\<lambda>f. cBlinfun
          (\<lambda>t. complex_of_real r *\<^sub>C cblinfun_apply f t)) f\<close>
      for f::\<open>('a, 'b) cblinfun\<close>
      by blast
    hence \<open>(\<lambda>f. cBlinfun (\<lambda>t. r *\<^sub>R cblinfun_apply f t)) =
    (\<lambda>f. cBlinfun
          (\<lambda>t. complex_of_real r *\<^sub>C cblinfun_apply f t))\<close>
      by (simp add: scaleR_scaleC)      
    thus ?thesis
      unfolding scaleR_cblinfun_def scaleC_cblinfun_def o_def blinfun_of_cblinfun_def map_fun_def
      by auto
  qed
  show \<open>a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    for a :: complex
      and x :: "('a, 'b) cblinfun"
      and y :: "('a, 'b) cblinfun"
    by (simp add: blinfun_of_cblinfun_inj blinfun_of_cblinfun_plus blinfun_of_cblinfun_scaleC scaleC_add_right)

  show \<open>(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x\<close>
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) cblinfun"
    by (simp add: blinfun_of_cblinfun_inj blinfun_of_cblinfun_plus blinfun_of_cblinfun_scaleC scaleC_left.add)

  show \<open>a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x\<close>
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) cblinfun"
    by (simp add: blinfun_of_cblinfun_inj blinfun_of_cblinfun_scaleC)

  show \<open>1 *\<^sub>C x = x\<close>
    for x :: "('a, 'b) cblinfun"
    by (simp add: blinfun_of_cblinfun_inj blinfun_of_cblinfun_scaleC)

  show \<open>dist x y = norm (x - y)\<close>
    for x :: "('a, 'b) cblinfun"
      and y :: "('a, 'b) cblinfun"
    by (simp add: dist_norm blinfun_of_cblinfun_dist blinfun_of_cblinfun_minus blinfun_of_cblinfun_norm)

  show \<open>sgn x = (inverse (norm x)) *\<^sub>R x\<close>
    for x :: "('a, 'b) cblinfun"
    by (simp add: norm_cblinfun_def scaleR_cblinfun_def sgn_cblinfun_def sgn_div_norm)

  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a, 'b) cblinfun) y < e})\<close>
    by (simp add: Bounded_Operators.uniformity_cblinfun_def)

  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::('a, 'b) cblinfun) = x \<longrightarrow> y \<in> U)\<close>
    for U :: "('a, 'b) cblinfun set"
    by (simp add: Bounded_Operators.open_cblinfun_def)

  show \<open>(norm x = 0) = (x = 0)\<close>
    for x :: "('a, 'b) cblinfun"
  proof -
    have f1: "cblinfun_of_blinfun (0::('a, 'b) blinfun) = 0"
      by (simp add: cblinfun_of_blinfun_zero)

    { assume "x \<noteq> 0"
      hence "x \<noteq> 0 \<and> cblinfun_of_blinfun 0 \<noteq> x"
        using f1 by meson
      hence ?thesis
        by (metis cblinfun_blinfun norm_eq_zero blinfun_of_cblinfun_norm)
    }
    thus ?thesis
      using blinfun_of_cblinfun_norm blinfun_of_cblinfun_zero by auto     
  qed

  show \<open>norm (x + y) \<le> norm x + norm y\<close>
    for x :: "('a, 'b) cblinfun"
      and y :: "('a, 'b) cblinfun"
    by (simp add: norm_triangle_ineq blinfun_of_cblinfun_norm blinfun_of_cblinfun_plus)

  show \<open>norm (a *\<^sub>C x) = cmod a * norm x\<close>
    for a :: complex
      and x :: "('a, 'b) cblinfun"
    using blinfun_of_cblinfun_norm blinfun_of_cblinfun_scaleC by auto


  show \<open>norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x\<close>
    for a :: real
      and x :: "('a, 'b) cblinfun"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) cblinfun \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x a. norm (a *\<^sub>C x) = cmod a * norm (x::('a, 'b) cblinfun)\<close>
      of_real_mult
    by simp

  show \<open>a *\<^sub>R (x + y) = a *\<^sub>R x +  a *\<^sub>R y\<close>
    for a :: real
      and x y :: "('a, 'b) cblinfun"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) cblinfun \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x y a. a *\<^sub>C (x + y) = a *\<^sub>C x +  a *\<^sub>C (y::('a, 'b) cblinfun)\<close>
      of_real_mult
    by simp

  show \<open>(a + b) *\<^sub>R x = a *\<^sub>R x +  b *\<^sub>R x\<close>
    for a b :: real
      and x :: "('a, 'b) cblinfun"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) cblinfun \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x b a. (a + b) *\<^sub>C (x::('a,'b) cblinfun) = a *\<^sub>C x +  b *\<^sub>C x\<close>
      of_real_mult
    by simp

  show \<open>a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x\<close>
    for a b :: real
      and x :: "('a, 'b) cblinfun"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) cblinfun \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x b a. a *\<^sub>C b *\<^sub>C (x::('a, 'b) cblinfun) = (a * b) *\<^sub>C x\<close>
      of_real_mult
    by simp

  show \<open>1 *\<^sub>R x = x\<close>
    for x :: "('a, 'b) cblinfun"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) cblinfun \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x. 1 *\<^sub>C (x::('a, 'b) cblinfun) = x\<close> of_real_1
    by simp

qed

end


lemma cblinfun_apply_add: "F *\<^sub>V (b1 + b2) = F *\<^sub>V b1 + F *\<^sub>V b2"
  apply transfer unfolding cbounded_linear_def clinear_def Vector_Spaces.linear_def
  using module_hom.add by blast


lemma cblinfun_apply_scaleC: "F *\<^sub>V (r *\<^sub>C b) = r *\<^sub>C (F *\<^sub>V b)"
  apply transfer unfolding cbounded_linear_def clinear_def Vector_Spaces.linear_def
  using module_hom.scale by blast


lemma cblinfun_apply_norm: "\<exists>K. \<forall>x. norm (F *\<^sub>V x) \<le> norm x * K "
  apply transfer unfolding cbounded_linear_def clinear_def Vector_Spaces.linear_def
  by simp

instantiation cblinfun :: (complex_normed_vector, cbanach) "cbanach"
begin
lemma blinfun_of_cblinfun_Cauchy:
  assumes \<open>Cauchy f\<close>
  shows \<open>Cauchy (\<lambda> n. blinfun_of_cblinfun (f n))\<close>
  using assms unfolding Cauchy_def
  by (simp add: blinfun_of_cblinfun_dist)  


lemma cblinfun_of_blinfun_Cauchy:
  assumes \<open>Cauchy f\<close> and
    \<open>\<And> n::nat. \<forall> c. \<forall> x. blinfun_apply (f n) (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply (f n) x)\<close>
  shows \<open>Cauchy (\<lambda> n. cblinfun_of_blinfun (f n))\<close>
  using assms  unfolding Cauchy_def 
  using blinfun_of_cblinfun_dist
  apply auto
  by (simp add: blinfun_cblinfun blinfun_of_cblinfun_dist)

lemma blinfun_of_cblinfun_lim:
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda> n. blinfun_of_cblinfun (f n)) \<longlonglongrightarrow> blinfun_of_cblinfun l\<close>
proof
  show "\<forall>\<^sub>F x in sequentially. dist (blinfun_of_cblinfun (f x)) (blinfun_of_cblinfun l) < e"
    if "(0::real) < e"
    for e :: real
  proof-
    from \<open>f \<longlonglongrightarrow> l\<close>
    have \<open>\<forall>\<^sub>F x in sequentially. dist (f x) l < e\<close>
      by (simp add: tendstoD that)
    thus ?thesis 
      unfolding blinfun_of_cblinfun_dist by blast
  qed
qed

lemma cblinfun_of_blinfun_complex_lim:
  fixes f::\<open>nat \<Rightarrow> ('a::complex_normed_vector, 'b::cbanach) blinfun\<close>
    and l::\<open>('a, 'b) blinfun\<close>
  assumes  \<open>f \<longlonglongrightarrow> l\<close> and
    \<open>\<And> n::nat. \<forall> c. \<forall> x. blinfun_apply (f n) (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply (f n) x)\<close> 
  shows \<open>\<forall> c. \<forall> x. blinfun_apply l (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply l x)\<close>
proof-
  have \<open>blinfun_apply l (c *\<^sub>C x) = c *\<^sub>C blinfun_apply l x\<close>
    for c::complex and x
  proof-
    have \<open>(\<lambda> n. blinfun_apply (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> blinfun_apply l (c *\<^sub>C x)\<close>
      by (simp add: assms(1) onorm_strong)        
    moreover have \<open>(\<lambda> n. c *\<^sub>C (blinfun_apply (f n) x) ) \<longlonglongrightarrow> c *\<^sub>C (blinfun_apply l x)\<close>
    proof-
      have \<open>isCont ((*\<^sub>C) c) y\<close>
        for y::'b
        using isCont_scaleC by auto
      hence \<open>isCont ((*\<^sub>C) c) (blinfun_apply l x)\<close>
        by simp
      thus ?thesis
        using assms(1) isCont_tendsto_compose onorm_strong by blast 
    qed
    moreover have \<open>blinfun_apply (f n) (c *\<^sub>C x) =  c *\<^sub>C (blinfun_apply (f n) x)\<close>
      for n
      by (simp add: assms(2))
    ultimately have \<open>(\<lambda> n. blinfun_apply (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> c *\<^sub>C (blinfun_apply l x)\<close>
      by simp
    thus ?thesis
      using  \<open>(\<lambda> n. blinfun_apply (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> blinfun_apply l (c *\<^sub>C x)\<close> LIMSEQ_unique 
      by blast
  qed
  thus ?thesis by blast
qed  

lemma cblinfun_of_blinfun_lim:
  fixes f::\<open>nat \<Rightarrow> ('a::complex_normed_vector, 'b::cbanach) blinfun\<close>
    and l::\<open>('a, 'b) blinfun\<close>
  assumes  \<open>f \<longlonglongrightarrow> l\<close> and
    \<open>\<And> n::nat. \<forall> c. \<forall> x. blinfun_apply (f n) (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply (f n) x)\<close>
  shows \<open>(\<lambda> n. cblinfun_of_blinfun (f n)) \<longlonglongrightarrow> cblinfun_of_blinfun l\<close>
proof
  show "\<forall>\<^sub>F x in sequentially. dist (cblinfun_of_blinfun (f x)) (cblinfun_of_blinfun l) < e"
    if "(0::real) < e"
    for e :: real
  proof-
    from \<open>f \<longlonglongrightarrow> l\<close>
    have \<open>\<forall>\<^sub>F x in sequentially. dist (f x) l < e\<close>
      by (simp add: tendstoD that)
    moreover have \<open>blinfun_of_cblinfun (cblinfun_of_blinfun (f n)) = f n\<close>
      for n
      by (simp add: assms(2) blinfun_cblinfun)
    moreover have \<open>blinfun_of_cblinfun (cblinfun_of_blinfun l) = l\<close>
    proof-
      have \<open>\<forall> c. \<forall> x. blinfun_apply l (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply l x)\<close>
        using assms(1) assms(2) cblinfun_of_blinfun_complex_lim by blast        
      thus ?thesis
        by (simp add: blinfun_cblinfun) 
    qed
    ultimately show ?thesis 
      unfolding blinfun_of_cblinfun_dist
      by simp  
  qed    
qed

instance 
proof
  show "convergent f"
    if "Cauchy f"
    for f :: "nat \<Rightarrow> ('a, 'b) cblinfun"
  proof-
    have \<open>Cauchy (\<lambda> n. blinfun_of_cblinfun (f n))\<close>
      by (simp add: blinfun_of_cblinfun_Cauchy that)
    hence \<open>convergent (\<lambda> n. blinfun_of_cblinfun (f n))\<close>
      by (simp add: Cauchy_convergent_iff)
    hence \<open>\<exists> l. (\<lambda> n. blinfun_of_cblinfun (f n)) \<longlonglongrightarrow> blinfun_of_cblinfun l\<close>
      by (metis (no_types, lifting) Bounded_Operators.cblinfun_of_blinfun_complex_lim convergent_LIMSEQ_iff blinfun_cblinfun blinfun_of_cblinfun_prelim)
    then obtain l where \<open>(\<lambda> n. blinfun_of_cblinfun (f n)) \<longlonglongrightarrow> blinfun_of_cblinfun l\<close>
      by blast
    hence \<open>(\<lambda> n. cblinfun_of_blinfun (blinfun_of_cblinfun (f n))) \<longlonglongrightarrow> cblinfun_of_blinfun (blinfun_of_cblinfun l)\<close>
      by (simp add: Bounded_Operators.cblinfun_of_blinfun_lim blinfun_of_cblinfun_prelim)
    hence \<open>f \<longlonglongrightarrow> l\<close>
      by (simp add: cblinfun_blinfun)
    thus ?thesis
      using convergent_def by blast 
  qed
qed
end


subsection \<open>Adjoint\<close>

lift_definition
  adjoint :: "('a::chilbert_space,'b::chilbert_space) cblinfun \<Rightarrow> ('b,'a) cblinfun" ("_*" [99] 100)
  is Adj by (fact Adj_cbounded_linear)

lift_definition idOp::\<open>('a::complex_normed_vector,'a) cblinfun\<close> is id
  using id_cbounded_linear by blast

lemma idOp_adjoint[simp]: "idOp* = idOp"
  apply transfer using id_dagger by blast

lemma scalar_times_adj[simp]: "(a *\<^sub>C A)* = (cnj a) *\<^sub>C (A*)" 
  for A::"('a::chilbert_space,'b::chilbert_space) cblinfun"
    and a :: complex 
proof-
  have \<open>cbounded_linear ((cblinfun_apply A))\<close>
    using cblinfun_apply by blast
  hence \<open>(\<lambda> t. a *\<^sub>C ((cblinfun_apply A) t))\<^sup>\<dagger> = (\<lambda> s. (cnj a) *\<^sub>C (((cblinfun_apply A)\<^sup>\<dagger>) s))\<close>
    using scalar_times_adjc_flatten
    unfolding cbounded_linear_def 
      scalar_times_adjc_flatten \<open>cbounded_linear (cblinfun_apply A)\<close>
    using scalar_times_adjc_flatten complex_vector.linear_scale
    by (simp add: complex_vector.linear_scale scalar_times_adjc_flatten \<open>cbounded_linear ((*\<^sub>V) A)\<close> 
        cbounded_linear.bounded_linear)
  moreover have \<open>cblinfun_apply ((a *\<^sub>C A)*) = (\<lambda> t. a *\<^sub>C ((cblinfun_apply A) t))\<^sup>\<dagger>\<close>
    unfolding Adj_def
    apply auto
    by (smt Adj_def Eps_cong adjoint.rep_eq cinner_scaleC_right scaleC_cblinfun.rep_eq)
  moreover have \<open>cblinfun_apply (cnj a *\<^sub>C (A*)) = (\<lambda> s. (cnj a) *\<^sub>C (((cblinfun_apply A)\<^sup>\<dagger>) s))\<close>
    unfolding Adj_def
    by (simp add: Adj_def adjoint.rep_eq scaleC_cblinfun.rep_eq)    
  ultimately show ?thesis
    using cblinfun_apply_inject
    by fastforce 
qed

lemma Adj_cblinfun_plus:
  fixes A B :: \<open>('a::chilbert_space, 'b::chilbert_space) cblinfun\<close>
  shows \<open>(A + B)* = (A*) + (B*)\<close>
proof transfer
  fix A B::\<open>'a \<Rightarrow> 'b\<close>
  assume \<open>cbounded_linear A\<close> and \<open>cbounded_linear B\<close>
  define F where \<open>F = (\<lambda>x. (A\<^sup>\<dagger>) x + (B\<^sup>\<dagger>) x)\<close>
  define G where \<open>G = (\<lambda>x. A x + B x)\<close>
  have \<open>cbounded_linear G\<close>
    unfolding G_def
    by (simp add: \<open>cbounded_linear A\<close> \<open>cbounded_linear B\<close> cbounded_linear_add)
  moreover have \<open>\<langle>F u,  v\<rangle> = \<langle>u, G v\<rangle>\<close>
    for u::'b and v::'a
    unfolding F_def G_def
    using Adj_I \<open>cbounded_linear A\<close> \<open>cbounded_linear B\<close> 
      cinner_left_distrib
    by (simp add: Adj_I cinner_left_distrib cinner_right_distrib) 
  ultimately have \<open>F = G\<^sup>\<dagger> \<close>
    by (rule Adj_D)
  thus \<open>(\<lambda>x. A x + B x)\<^sup>\<dagger> = (\<lambda>x. (A\<^sup>\<dagger>) x + (B\<^sup>\<dagger>) x)\<close>
    unfolding F_def G_def
    by auto
qed

lemma Adj_cblinfun_uminus[simp]:
  \<open>(- A)* = - (A*)\<close>
  by (metis (no_types, lifting) Adj_cblinfun_plus  add_cancel_left_right diff_0 ordered_field_class.sign_simps(9))

lemma Adj_cblinfun_minus[simp]:
  \<open>(A - B)* = (A*) - (B*)\<close>
  by (metis Adj_cblinfun_plus add_right_cancel diff_add_cancel)


lemma Adj_cblinfun_zero[simp]:
  \<open>0* = 0\<close>
  by (metis Adj_cblinfun_plus add_cancel_right_right)

subsection \<open>Composition\<close>

lift_definition timesOp:: 
  "('b::complex_normed_vector,'c::complex_normed_vector) cblinfun
     \<Rightarrow> ('a::complex_normed_vector,'b) cblinfun \<Rightarrow> ('a,'c) cblinfun"
  is "(o)"
  unfolding o_def 
  by (rule cbounded_linear_compose, simp_all)

(* Closure is necessary. See thunderlink://messageid=47a3bb3d-3cc3-0934-36eb-3ef0f7b70a85@ut.ee *)
lift_definition applyOpSpace::\<open>('a::complex_normed_vector,'b::complex_normed_vector) cblinfun
\<Rightarrow> 'a linear_space \<Rightarrow> 'b linear_space\<close> 
  is "\<lambda>A S. closure (A ` S)"
  using  cbounded_linear_def closed_closure  closed_subspace.intro
  by (simp add: cbounded_linear_def closed_subspace.subspace complex_vector.linear_subspace_image subspace_I) 



bundle cblinfun_notation begin
notation timesOp (infixl "o\<^sub>C\<^sub>L" 69)
notation cblinfun_apply (infixr "*\<^sub>V" 70)
notation applyOpSpace (infixr "*\<^sub>S" 70)
notation adjoint ("_*" [99] 100)
end

bundle no_cblinfun_notation begin
no_notation timesOp (infixl "o\<^sub>C\<^sub>L" 69)
no_notation cblinfun_apply (infixr "*\<^sub>V" 70)
no_notation applyOpSpace (infixr "*\<^sub>S" 70)
no_notation adjoint ("_*" [99] 100)
end

bundle blinfun_notation begin
notation blinfun_apply (infixr "*\<^sub>V" 70)
end

bundle no_blinfun_notation begin
no_notation blinfun_apply (infixr "*\<^sub>V" 70)
end


unbundle cblinfun_notation

lemma adjoint_I:
  fixes G :: "('b::chilbert_space, 'a::chilbert_space) cblinfun"
  shows \<open>\<langle>G* *\<^sub>V x, y\<rangle> = \<langle>x, G *\<^sub>V y\<rangle>\<close>
  apply transfer using Adj_I by blast

lemma adjoint_I':
  fixes G :: "('b::chilbert_space, 'a::chilbert_space) cblinfun"
  shows \<open>\<langle>x, G* *\<^sub>V y\<rangle> = \<langle>G *\<^sub>V x, y\<rangle>\<close> 
  apply transfer using Adj_I' by blast

lemma adjoint_D:
  fixes G:: \<open>('b::chilbert_space, 'a::chilbert_space) cblinfun\<close>
    and F:: \<open>('a, 'b) cblinfun\<close>
  assumes \<open>\<And>x y. \<langle>(cblinfun_apply F) x, y\<rangle> = \<langle>x, (cblinfun_apply G) y\<rangle>\<close>
  shows \<open>F = G*\<close>
  using assms apply transfer using Adj_D by auto

lemma adjoint_twice[simp]: "(U*)* = U" 
  for U :: "('a::chilbert_space,'b::chilbert_space) cblinfun"
  apply transfer
  using dagger_dagger_id by blast

lemma blinfun_of_cblinfun_timesOp:
  fixes f::\<open>('b::complex_normed_vector,'c::complex_normed_vector) cblinfun\<close>
    and g::\<open>('a::complex_normed_vector,'b) cblinfun\<close>
  shows \<open>blinfun_of_cblinfun (f  o\<^sub>C\<^sub>L g) = (blinfun_of_cblinfun f) o\<^sub>L (blinfun_of_cblinfun g)\<close>
  apply transfer by auto

lemma timesOp_assoc: 
  shows "(A  o\<^sub>C\<^sub>L B)  o\<^sub>C\<^sub>L C = A  o\<^sub>C\<^sub>L (B  o\<^sub>C\<^sub>L C)"
  by (metis (no_types, lifting) cblinfun_apply_inject fun.map_comp timesOp.rep_eq)

lemma timesOp_dist1:  
  fixes a b :: "('b::complex_normed_vector, 'c::complex_normed_vector) cblinfun"
    and c :: "('a::complex_normed_vector, 'b) cblinfun"
  shows "(a + b)  o\<^sub>C\<^sub>L c = (a  o\<^sub>C\<^sub>L c) + (b  o\<^sub>C\<^sub>L c)"
  using blinfun_of_cblinfun_inj blinfun_of_cblinfun_plus blinfun_of_cblinfun_timesOp
  by (simp add: blinfun_of_cblinfun_inj blinfun_of_cblinfun_plus blinfun_of_cblinfun_timesOp times_blinfun_dist1)

lemma timesOp_dist2:  
  fixes a b :: "('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun"
    and c :: "('b, 'c::complex_normed_vector) cblinfun"
  shows "c o\<^sub>C\<^sub>L (a + b) = (c o\<^sub>C\<^sub>L a) + (c o\<^sub>C\<^sub>L b)"
  using  blinfun_of_cblinfun_inj blinfun_of_cblinfun_plus blinfun_of_cblinfun_timesOp
  by (simp add: blinfun_of_cblinfun_inj blinfun_of_cblinfun_plus blinfun_of_cblinfun_timesOp times_blinfun_dist2)

lemma timesOp_minus:
  \<open>A o\<^sub>C\<^sub>L (B - C) = A o\<^sub>C\<^sub>L B - A o\<^sub>C\<^sub>L C\<close>
  apply transfer
  using  cbounded_linear_def
  by (metis comp_apply complex_vector.linear_diff)

lemma times_adjoint[simp]:
  fixes B::\<open>('a::chilbert_space,'b::chilbert_space) cblinfun\<close>
    and A::\<open>('b,'c::chilbert_space) cblinfun\<close> 
  shows "(A o\<^sub>C\<^sub>L B)* =  (B*) o\<^sub>C\<^sub>L (A*)"
proof transfer
  fix  A :: \<open>'b\<Rightarrow>'c\<close> and B :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>cbounded_linear A\<close> and \<open>cbounded_linear B\<close>
  hence \<open>cbounded_linear (A \<circ> B)\<close>
    by (simp add: comp_cbounded_linear)
  have \<open>\<langle> (A \<circ> B) u, v \<rangle> = \<langle> u, (B\<^sup>\<dagger> \<circ> A\<^sup>\<dagger>) v \<rangle>\<close>
    for u v
    by (metis (no_types, lifting) Adj_I \<open>cbounded_linear A\<close> \<open>cbounded_linear B\<close> cinner_commute' comp_def)    
  thus \<open>(A \<circ> B)\<^sup>\<dagger> = B\<^sup>\<dagger> \<circ> A\<^sup>\<dagger>\<close>
    using \<open>cbounded_linear (A \<circ> B)\<close>
    by (metis Adj_D cinner_commute')
qed

lemma cblinfun_apply_0[simp]:  
  fixes U::\<open>('a::complex_normed_vector,'b::complex_normed_vector) cblinfun\<close>
  shows  "U  o\<^sub>C\<^sub>L 0 = 0"
  apply transfer
  unfolding cbounded_linear_def
  by (simp add: complex_vector.linear_0)


lemma applyOp_0[simp]:  
  fixes U::\<open>('a::chilbert_space,'b::chilbert_space) cblinfun\<close>
  shows   "U *\<^sub>S (0::'a linear_space) = (0::'b linear_space)"
proof-
  {
    have \<open>cbounded_linear U \<Longrightarrow>
          (closure
            (U ` {0})) = {0}\<close>
      for U::\<open>'a\<Rightarrow>'b\<close>
    proof-
      assume \<open>cbounded_linear U\<close>
      have \<open>U ` {0} = {U 0}\<close>
        by auto
      moreover have \<open>U 0 = 0\<close>
        using \<open>cbounded_linear U\<close>
        unfolding cbounded_linear_def
        by (simp add: complex_vector.linear_0)
      ultimately have \<open>U ` {0} = {0}\<close>
        by simp
      thus ?thesis
        by simp 
    qed
    hence \<open>cbounded_linear U \<Longrightarrow>
         Abs_linear_space
          (closure
            (U ` {0})) =
         Abs_linear_space {0}\<close>
      for U::\<open>'a\<Rightarrow>'b\<close>
      using Abs_linear_space_inject
      by presburger
    hence \<open>cbounded_linear U \<Longrightarrow>
         Abs_linear_space
          (closure (U ` space_as_set (Abs_linear_space {0}))) =
         Abs_linear_space {0}\<close>
      for U::\<open>'a\<Rightarrow>'b\<close>
      by (simp add: Abs_linear_space_inverse)  } note 1 = this
  thus ?thesis
    unfolding zero_linear_space_def applyOpSpace_def
    apply auto
    using 1 bot_linear_space.abs_eq   
    by (metis (full_types) mem_Collect_eq cblinfun_apply) 
qed

lemma times_comp: \<open>\<And>A B \<psi>.
       cbounded_linear A \<Longrightarrow>
       cbounded_linear B \<Longrightarrow>
       closed_subspace \<psi> \<Longrightarrow>
       closure ( (A \<circ> B) ` \<psi>) = closure (A ` closure (B ` \<psi>))\<close>
proof
  show "closure ((A \<circ> B) ` (\<psi>::'c set)::'b set) \<subseteq> closure (A ` closure (B ` \<psi>::'a set))"
    if "cbounded_linear (A::'a \<Rightarrow> 'b)"
      and "cbounded_linear (B::'c \<Rightarrow> 'a)"
      and "closed_subspace (\<psi>::'c set)"
    for A :: "'a \<Rightarrow> 'b"
      and B :: "'c \<Rightarrow> 'a"
      and \<psi> :: "'c set"
    using that
    by (metis closure_mono closure_subset image_comp image_mono) 
  show "closure (A ` closure (B ` (\<psi>::'c set)::'a set)) \<subseteq> closure ((A \<circ> B) ` \<psi>::'b set)"
    if "cbounded_linear (A::'a \<Rightarrow> 'b)"
      and "cbounded_linear (B::'c \<Rightarrow> 'a)"
      and "closed_subspace (\<psi>::'c set)"
    for A :: "'a \<Rightarrow> 'b"
      and B :: "'c \<Rightarrow> 'a"
      and \<psi> :: "'c set"
    using that 
  proof-
    have \<open>A ` closure (B ` \<psi>) \<subseteq> closure ((A \<circ> B) ` \<psi>)\<close>
    proof
      show "x \<in> closure ((A \<circ> B) ` \<psi>)"
        if "x \<in> A ` closure (B ` \<psi>)"
        for x :: 'b
        using that
      proof-
        have \<open>\<exists> t::nat \<Rightarrow> 'b. (\<forall> n. t n \<in> (A \<circ> B) ` \<psi>) \<and> (t \<longlonglongrightarrow> x)\<close>
        proof-
          have \<open>\<exists> y\<in>closure (B ` \<psi>). x = A y\<close>
            using that by blast
          then obtain y where \<open>y\<in>closure (B ` \<psi>)\<close> and \<open>x = A y\<close>
            by blast
          from \<open>y\<in>closure (B ` \<psi>)\<close>
          have \<open>\<exists> s::nat \<Rightarrow> 'a. (\<forall>n. s n \<in> B ` \<psi>) \<and> s \<longlonglongrightarrow> y\<close>
            using closure_sequential by blast
          then obtain s::\<open>nat\<Rightarrow>'a\<close> where \<open>\<forall>n. s n \<in> B ` \<psi>\<close> and \<open>s \<longlonglongrightarrow> y\<close>
            by blast
          define t::"nat \<Rightarrow> 'b" where \<open>t n = A (s n)\<close> for n::nat
          have \<open>\<forall>n. t n \<in> (A \<circ> B) ` \<psi>\<close>
            by (metis \<open>\<forall>n. s n \<in> B ` \<psi>\<close> imageI image_comp t_def)
          moreover have \<open>t \<longlonglongrightarrow> x\<close>
          proof-
            have \<open>isCont A y\<close>
              using \<open>cbounded_linear A\<close>
              by (simp add: bounded_linear_continuous) 
            thus ?thesis unfolding t_def using \<open>s \<longlonglongrightarrow> y\<close>
              by (simp add: \<open>x = A y\<close> isCont_tendsto_compose) 
          qed
          ultimately have "(\<forall>n. t n \<in> (A \<circ> B) ` \<psi>) \<and> t \<longlonglongrightarrow> x"
            by blast
          thus ?thesis by blast
        qed
        thus ?thesis
          using closure_sequential by blast 
      qed
    qed
    thus ?thesis
      by (metis closure_closure closure_mono) 
  qed
qed

lemma timesOp_assoc_linear_space: 
  shows  \<open>(A o\<^sub>C\<^sub>L B) *\<^sub>S \<psi> =  A *\<^sub>S (B *\<^sub>S \<psi>)\<close>
proof-
  have \<open>cbounded_linear (cblinfun_apply A)\<close>
    using cblinfun_apply by auto
  moreover have \<open>cbounded_linear (cblinfun_apply B)\<close>
    using cblinfun_apply by auto
  moreover have \<open>closed_subspace (space_as_set \<psi>)\<close>
    using space_as_set by auto
  ultimately have  \<open>
     (closure
       ( (cblinfun_apply A \<circ> cblinfun_apply B) ` space_as_set \<psi>)) =
     (closure
       (cblinfun_apply A `
      closure (cblinfun_apply B ` space_as_set \<psi>)))\<close>
    using times_comp by blast
  hence  \<open>
     (closure
       ( (cblinfun_apply A \<circ> cblinfun_apply B) ` space_as_set \<psi>)) =
     (closure
       (cblinfun_apply A `
        space_as_set
         (Abs_linear_space
           (closure (cblinfun_apply B ` space_as_set \<psi>)))))\<close>
    by (metis space_as_set_inverse applyOpSpace.rep_eq)    
  hence  \<open>
     (closure
       (cblinfun_apply (timesOp A B) ` space_as_set \<psi>)) =
     (closure
       (cblinfun_apply A `
        space_as_set
         (Abs_linear_space
           (closure (cblinfun_apply B ` space_as_set \<psi>)))))\<close>
    by (simp add: timesOp.rep_eq)    
  hence \<open> Abs_linear_space
     (closure
       (cblinfun_apply (timesOp A B) ` space_as_set \<psi>)) =
    Abs_linear_space
     (closure
       (cblinfun_apply A `
        space_as_set
         (Abs_linear_space
           (closure (cblinfun_apply B ` space_as_set \<psi>)))))\<close>
    using Abs_linear_space_inject by auto
  thus ?thesis
    unfolding applyOpSpace_def
    by auto
qed


lemmas assoc_left = timesOp_assoc[symmetric] timesOp_assoc_linear_space[symmetric] add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) cblinfun", symmetric]
lemmas assoc_right = timesOp_assoc timesOp_assoc_linear_space add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) cblinfun"]

lemma scalar_times_op_add[simp]: "a *\<^sub>C (A+B) = a *\<^sub>C A + a *\<^sub>C B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) cblinfun"
  by (simp add: scaleC_add_right)

lemma scalar_times_op_minus[simp]: "a *\<^sub>C (A-B) =  a *\<^sub>C A - a *\<^sub>C B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) cblinfun"
  by (simp add: complex_vector.scale_right_diff_distrib)


lemma applyOp_bot[simp]:
  fixes U::\<open>('a::chilbert_space, 'b::chilbert_space) cblinfun\<close> 
  shows "U *\<^sub>S bot = bot"
proof-
  have \<open>closed {0::'a}\<close>
    using Topological_Spaces.t1_space_class.closed_singleton by blast
  hence \<open>closure {0::'a} = {0}\<close>
    by (simp add: closure_eq)    
  moreover have \<open>cblinfun_apply U ` {0::'a} = {0}\<close>
  proof-
    have \<open>cbounded_linear (cblinfun_apply U)\<close>
      using cblinfun_apply by auto
    hence  \<open>cblinfun_apply U 0 = 0\<close>
      by (simp add: cbounded_linear.clinear clinear_zero)
    thus ?thesis
      by simp 
  qed
  ultimately have \<open>closure (cblinfun_apply U ` {0}) = {0}\<close>
    by simp
  hence \<open>(closure (cblinfun_apply U ` space_as_set (Abs_linear_space {0}))) = {0}\<close>
    by (metis bot_linear_space.abs_eq bot_linear_space.rep_eq) 
  thus ?thesis
    unfolding applyOpSpace_def bot_linear_space_def by simp
qed

lemma cdot_plus_distrib_transfer:
  \<open>cbounded_linear U \<Longrightarrow>
       closed_subspace A \<Longrightarrow>
       closed_subspace B \<Longrightarrow>
        (closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
  for U::\<open>'a::complex_normed_vector\<Rightarrow>'b::complex_normed_vector\<close> and A B::\<open>'a set\<close>
proof-
  assume \<open>cbounded_linear U\<close> and \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close> 
  have \<open>(closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
  proof-
    have \<open>U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} \<subseteq>
          {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
    proof-
      have \<open>U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} = {U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
        by auto
      moreover have \<open> {U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}
                      = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}\<close>
      proof-
        have \<open>{U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} = {U \<psi> + U \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
          using \<open>cbounded_linear U\<close>
          unfolding cbounded_linear_def
          by (metis (no_types, lifting) complex_vector.linear_add) 

        also have \<open>{U \<psi> + U \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} 
            = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}\<close>
          by blast
        finally show ?thesis by blast
      qed
      moreover have \<open>{\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}
           \<subseteq> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
        by (smt closure_subset mem_Collect_eq subsetD subsetI)
          (* > 1s *)
      ultimately show ?thesis
        by simp 
    qed
    hence \<open>closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
      by (simp add: closure_mono)      
    moreover have \<open>(U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})
            \<subseteq> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
    proof-
      define S where \<open>S = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
      from  \<open>cbounded_linear U\<close>
      have \<open>isCont U x\<close>
        for x
        by (simp add: bounded_linear_continuous)
      hence \<open>continuous_on (closure S) U\<close>
        by (simp add: continuous_at_imp_continuous_on)
      hence \<open>U ` (closure S) \<subseteq> closure (U ` S)\<close>
        using Abstract_Topology_2.image_closure_subset
        by (simp add: image_closure_subset closure_subset)
      thus ?thesis unfolding S_def by blast
    qed
    ultimately have \<open>(U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
      by blast
    thus ?thesis
      by (metis (no_types, lifting) closure_closure closure_mono) 
  qed
  moreover have \<open>(closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})
      \<subseteq> closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
  proof-
    have \<open>x \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}
      \<Longrightarrow> x \<in> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
      for x
    proof-
      assume \<open>x \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
      then obtain \<psi> \<phi> where \<open>x =  \<psi> + \<phi>\<close>  and \<open>\<psi> \<in> closure (U ` A)\<close> and \<open>\<phi> \<in> closure (U ` B)\<close>
        by blast
      from  \<open>\<psi> \<in> closure (U ` A)\<close>
      have \<open>\<exists> psiU. (\<forall> n. psiU n \<in> (U ` A)) \<and> (\<lambda> n. psiU n) \<longlonglongrightarrow> \<psi>\<close>
        using closure_sequential by blast
      then obtain psiU where \<open>\<forall> n. psiU n \<in> (U ` A)\<close> and \<open>(\<lambda> n. psiU n) \<longlonglongrightarrow> \<psi>\<close>
        by blast
      from \<open>\<forall> n. psiU n \<in> (U ` A)\<close>
      have \<open>\<forall> n. \<exists> psi.  psiU n = U psi \<and> psi \<in> A\<close>
        by blast
      hence \<open>\<exists> psi. \<forall> n. psiU n = U (psi n) \<and> psi n \<in> A\<close>
        by metis
      then obtain psi where \<open>\<forall> n. psiU n = U (psi n)\<close> and \<open>\<forall> n. psi n \<in> A\<close>
        by blast
      have  \<open>(\<lambda> n. U (psi n)) \<longlonglongrightarrow> \<psi>\<close>
        using \<open>(\<lambda> n. psiU n) \<longlonglongrightarrow> \<psi>\<close> \<open>\<forall> n. psiU n = U (psi n)\<close>
        by simp
      from  \<open>\<phi> \<in> closure (U ` B)\<close>
      have \<open>\<exists> phiU. (\<forall> n. phiU n \<in> (U ` B)) \<and> (\<lambda> n. phiU n) \<longlonglongrightarrow> \<phi>\<close>
        using closure_sequential by blast
      then obtain phiU where \<open>\<forall> n. phiU n \<in> (U ` B)\<close> and \<open>(\<lambda> n. phiU n) \<longlonglongrightarrow> \<phi>\<close>
        by blast
      from \<open>\<forall> n. phiU n \<in> (U ` B)\<close>
      have \<open>\<forall> n. \<exists> phi.  phiU n = U phi \<and> phi \<in> B\<close>
        by blast
      hence \<open>\<exists> phi. \<forall> n. phiU n = U (phi n) \<and> phi n \<in> B\<close>
        by metis
      then obtain phi where \<open>\<forall> n. phiU n = U (phi n)\<close> and \<open>\<forall> n. phi n \<in> B\<close>
        by blast
      have  \<open>(\<lambda> n. U (phi n)) \<longlonglongrightarrow> \<phi>\<close>
        using \<open>(\<lambda> n. phiU n) \<longlonglongrightarrow> \<phi>\<close> \<open>\<forall> n. phiU n = U (phi n)\<close>
        by simp
      from  \<open>(\<lambda> n. U (psi n)) \<longlonglongrightarrow> \<psi>\<close> \<open>(\<lambda> n. U (phi n)) \<longlonglongrightarrow> \<phi>\<close>
      have \<open>(\<lambda> n. U (psi n) +  U (phi n) ) \<longlonglongrightarrow> \<psi> + \<phi>\<close>
        by (simp add: tendsto_add)
      hence \<open>(\<lambda> n. U ( (psi n) +  (phi n)) ) \<longlonglongrightarrow> \<psi> + \<phi>\<close>
      proof-
        have \<open>U (psi n) +  U (phi n) =  U ( (psi n) +  (phi n))\<close>
          for n
          using \<open>cbounded_linear U\<close>
          unfolding cbounded_linear_def clinear_def Vector_Spaces.linear_def
            module_hom_def module_hom_axioms_def
          by auto
        thus ?thesis 
          using  \<open>(\<lambda> n. U (psi n) +  U (phi n) ) \<longlonglongrightarrow> \<psi> + \<phi>\<close>
          by auto
      qed
      hence \<open>(\<lambda> n. U ( (psi n) +  (phi n)) ) \<longlonglongrightarrow> x\<close>
        by (simp add: \<open>x = \<psi> + \<phi>\<close>)
      hence \<open>x \<in> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
        by (smt \<open>\<forall>n. phi n \<in> B\<close> \<open>\<forall>n. psi n \<in> A\<close> closure_sequential mem_Collect_eq setcompr_eq_image)
      thus ?thesis by blast
    qed
    moreover have \<open>closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})
        \<subseteq> closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
      by (simp add: closure_mono closure_subset image_mono)
    ultimately show ?thesis
      using closure_mono
      by (metis (no_types, lifting) closure_closure dual_order.trans subsetI)  
  qed
  ultimately show ?thesis by blast
qed

lemma cdot_plus_distrib[simp]:   
  fixes A B :: \<open>('a::chilbert_space) linear_space\<close> and U :: "('a,'b::chilbert_space) cblinfun"
  shows \<open>U *\<^sub>S (sup A B) = sup (U *\<^sub>S A) (U *\<^sub>S B)\<close>
  apply transfer
proof-
  fix U::\<open>'a\<Rightarrow>'b\<close> and A B::\<open>'a set\<close>
  assume \<open>cbounded_linear U\<close> and \<open>closed_subspace A\<close> and \<open>closed_subspace B\<close> 
  hence \<open>(closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
        (closure {\<psi> + \<phi> |\<psi> \<phi>.
           \<psi> \<in> closure (U ` A) \<and>
           \<phi> \<in> closure (U ` B)})\<close>
    using cdot_plus_distrib_transfer by blast    
  thus \<open>closure (U ` (A +\<^sub>M B)) =
       closure (U ` A) +\<^sub>M closure (U ` B)\<close>
    unfolding closed_sum_def set_plus_def
    by (smt Collect_cong)
      (* > 1 s *)
qed


lemma scalar_op_linear_space_assoc [simp]: 
  fixes A::\<open>('a::chilbert_space,'b::chilbert_space) cblinfun\<close>
    and S::\<open>'a linear_space\<close> and \<alpha>::complex
  shows \<open>(\<alpha> *\<^sub>C A) *\<^sub>S S  = \<alpha> *\<^sub>C (A *\<^sub>S S)\<close>
proof-
  have \<open>closure ( ( ((*\<^sub>C) \<alpha>) \<circ> (cblinfun_apply A) ) ` space_as_set S) =
   ((*\<^sub>C) \<alpha>) ` (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis closure_scaleC image_comp)    
  hence \<open>(closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
   ((*\<^sub>C) \<alpha>) ` (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis (mono_tags, lifting) comp_apply image_cong scaleC_cblinfun.rep_eq)
  hence \<open>Abs_linear_space
     (closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
    \<alpha> *\<^sub>C
    Abs_linear_space (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis space_as_set_inverse applyOpSpace.rep_eq scaleC_linear_space.rep_eq)    
  show ?thesis 
    unfolding applyOpSpace_def apply auto
    using \<open>Abs_linear_space
     (closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
    \<alpha> *\<^sub>C Abs_linear_space (closure (cblinfun_apply A ` space_as_set S))\<close>
    by blast
qed

lemma applyOpSpace_id[simp]: 
  "idOp *\<^sub>S \<psi> = \<psi>"
proof-
  have \<open>closed_subspace ( space_as_set \<psi>)\<close>
    using space_as_set by blast    
  hence \<open>closed ( space_as_set \<psi>)\<close>
    unfolding closed_subspace_def by blast
  hence \<open>closure ( space_as_set \<psi>) = space_as_set \<psi>\<close>
    by simp    
  hence \<open>(closure ( id ` space_as_set \<psi>)) = space_as_set \<psi>\<close>
    by simp    
  hence \<open>(closure (cblinfun_apply (cBlinfun id) ` space_as_set \<psi>)) = space_as_set \<psi>\<close>
    by (metis idOp.abs_eq idOp.rep_eq)    
  hence \<open>Abs_linear_space
     (closure (cblinfun_apply (cBlinfun id) ` space_as_set \<psi>)) = \<psi>\<close>
    by (simp add: space_as_set_inverse)    
  show ?thesis
    unfolding applyOpSpace_def idOp_def
    apply auto
    using  \<open>Abs_linear_space
     (closure (cblinfun_apply (cBlinfun id) ` space_as_set \<psi>)) = \<psi>\<close>
    by blast
qed

lemma scalar_op_op[simp]:
  fixes A::"('b::complex_normed_vector,'c::complex_normed_vector) cblinfun"
    and B::"('a::complex_normed_vector, 'b) cblinfun"
  shows \<open>(a *\<^sub>C A) o\<^sub>C\<^sub>L B = a *\<^sub>C (A o\<^sub>C\<^sub>L B)\<close>
proof-
  have \<open>(a *\<^sub>C (blinfun_of_cblinfun A) o\<^sub>L
       (blinfun_of_cblinfun B)) =
   ( a *\<^sub>C  ( (blinfun_of_cblinfun A) o\<^sub>L (blinfun_of_cblinfun B)) )\<close>
    by (simp add: rscalar_op_op)
  hence \<open> (blinfun_of_cblinfun (a *\<^sub>C A) o\<^sub>L
       (blinfun_of_cblinfun B)) =
   ( a *\<^sub>C  ((blinfun_of_cblinfun A) o\<^sub>L (blinfun_of_cblinfun B)) )\<close>
    by (simp add: blinfun_of_cblinfun_scaleC)    
  hence \<open>cblinfun_of_blinfun
     ( (blinfun_of_cblinfun (a *\<^sub>C A))
      o\<^sub>L (blinfun_of_cblinfun B)) =
    cblinfun_of_blinfun
   ( a *\<^sub>C  ( (blinfun_of_cblinfun A) o\<^sub>L (blinfun_of_cblinfun B)) )\<close>
    by simp    
  hence \<open>cblinfun_of_blinfun
     ( (blinfun_of_cblinfun (a *\<^sub>C A))
      o\<^sub>L (blinfun_of_cblinfun B)) =
    a *\<^sub>C cblinfun_of_blinfun
     ((blinfun_of_cblinfun A) o\<^sub>L (blinfun_of_cblinfun B))\<close>
    by (simp add: cblinfun_of_blinfun_scaleC blinfun_of_cblinfun_prelim times_blinfun_scaleC)  
  thus ?thesis
    by (metis cblinfun_blinfun blinfun_of_cblinfun_timesOp)   
qed


lemma op_scalar_op[simp]:
  fixes A::"('b::complex_normed_vector,'c::complex_normed_vector) cblinfun" 
    and B::"('a::complex_normed_vector, 'b) cblinfun"
  shows \<open>A o\<^sub>C\<^sub>L (a *\<^sub>C B) = a *\<^sub>C (A o\<^sub>C\<^sub>L B)\<close>
  using op_rscalar_op
  by (simp add: op_rscalar_op blinfun_of_cblinfun_inj blinfun_of_cblinfun_prelim blinfun_of_cblinfun_scaleC blinfun_of_cblinfun_timesOp)

lemma times_idOp1[simp]: 
  shows "U o\<^sub>C\<^sub>L idOp = U"
  by (metis cblinfun_apply_inject comp_id idOp.rep_eq timesOp.rep_eq)

lemma times_idOp2[simp]: 
  shows "idOp o\<^sub>C\<^sub>L U  = U"
  by (metis cblinfun_apply_inject idOp.rep_eq id_comp timesOp.rep_eq)

lemma mult_INF1[simp]:
  fixes U :: "('b::complex_normed_vector,'c::cbanach) cblinfun"
    and V :: "'a \<Rightarrow> 'b linear_space" 
  shows \<open>U *\<^sub>S (INF i. V i) \<le> (INF i. U *\<^sub>S (V i))\<close>
proof-
  have \<open>cbounded_linear U \<Longrightarrow>
       \<forall>j. closed_subspace (V j) \<Longrightarrow> closure (U ` \<Inter> (range V)) \<subseteq> closure (U ` V i)\<close>
    for U::\<open>'b\<Rightarrow>'c\<close> and V::\<open>'a \<Rightarrow> 'b set\<close> and x::'c and i::'a
  proof-
    assume \<open>cbounded_linear U\<close> and \<open>\<forall>j. closed_subspace (V j)\<close> 
    have \<open>U ` \<Inter> (range V) \<subseteq> U ` (V i)\<close>
      by (simp add: Inter_lower image_mono)    
    thus ?thesis
      by (simp add: closure_mono) 
  qed
  thus ?thesis
    apply transfer
    by auto
qed

(* For mult_INF2:

I have a proof sketch for a slightly more restricted version of mult_INF2:

Assume that V_i is orthogonal to ker U for all i.

Let W be the pseudoinverse of U (exists according to https://en.wikipedia.org/wiki/Moore%E2%80%93Penrose_inverse#Generalizations).


Then (1) UW is the projector onto the range of U, and (2) WU the projector onto the orthogonal complement of ker U.


Then


INF (U*Vi)

= (1)

UW INF (U*Vi)

<= (INF_mult1)

U INF (WU*Vi)

= (2)

U INF Vi.


Of course, I don't know how difficult it is to show the existence of the pseudoinverse. An easy special case would be U=isometry, in which case W=U*.

 *)

lemma mult_inf_distrib':
  fixes U::\<open>('a::chilbert_space,'b::chilbert_space) cblinfun\<close> and B C::"'a linear_space"
  shows "U *\<^sub>S (inf B  C) \<le> inf (U *\<^sub>S B) (U *\<^sub>S C)"
proof-
  have \<open>cbounded_linear U \<Longrightarrow>
       closed_subspace B \<Longrightarrow>
       closed_subspace C \<Longrightarrow>
       closure (U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
    for U::\<open>'a\<Rightarrow>'b\<close> and B C::\<open>'a set\<close>
  proof-
    assume \<open>cbounded_linear U\<close> and \<open>closed_subspace B\<close> and \<open>closed_subspace C\<close>
    have \<open>(U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
      using closure_subset by force      
    moreover have \<open>closed ( closure (U ` B) \<inter> closure (U ` C) )\<close>
      by blast      
    ultimately show ?thesis
      by (simp add: closure_minimal) 
  qed
  show ?thesis 
    apply transfer
    using \<open>\<And>U B C.
       cbounded_linear U \<Longrightarrow>
       closed_subspace B \<Longrightarrow>
       closed_subspace C \<Longrightarrow>
       closure (U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
    by blast
qed



lemma equal_span:
  fixes A B :: "'a::cbanach \<Rightarrow> 'b::cbanach"
  assumes \<open>clinear A\<close> and \<open>clinear B\<close> and
    \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and \<open>t \<in> (complex_vector.span G)\<close>
  shows \<open>A t = B t\<close>
  using assms(1) assms(2) assms(3) assms(4)
  by (metis complex_vector.linear_eq_on_span) 

lemma equal_span_applyOpSpace:
  fixes A B :: "'a::cbanach \<Rightarrow> 'b::cbanach"
  assumes \<open>cbounded_linear A\<close> and \<open>cbounded_linear B\<close> and
    \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and \<open>t \<in> closure (complex_vector.span G)\<close>
  shows \<open>A t = B t\<close>
  using assms 
proof transfer
  include nsa_notation
  fix A B::\<open>'a \<Rightarrow> 'b\<close> and G::\<open>'a set\<close> and t::'a
  assume \<open>cbounded_linear A\<close> and
    \<open>cbounded_linear B\<close> and
    \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and
    \<open>t \<in> closure (complex_vector.span G)\<close>
  define F where \<open>F = (\<lambda> x. A x - B x)\<close>
  have \<open>cbounded_linear F\<close>
    unfolding F_def
    using \<open>cbounded_linear A\<close> \<open>cbounded_linear B\<close>
      cbounded_linear_sub by auto
  hence \<open>isCont F t\<close>
    using linear_continuous_at
    by (simp add: bounded_linear_continuous) 
  hence \<open>isNSCont F t\<close>
    by (simp add: isCont_isNSCont)
  from \<open>t \<in> closure (complex_vector.span G)\<close>
  have \<open>\<exists> T \<in> *s* (complex_vector.span G). T \<approx> star_of t\<close>
    using approx_sym nsclosure_I by blast
  then obtain T where \<open>T \<in> *s* (complex_vector.span G)\<close> and \<open>T \<approx> star_of t\<close>
    by blast
  have \<open>(*f* F) T \<approx> (*f* F) (star_of t)\<close>
    using \<open>T \<approx> star_of t\<close>  \<open>isNSCont F t\<close>
    by (simp add: isNSCont_def)
  moreover have \<open>(*f* F) T \<approx> 0\<close>
  proof-
    from  \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close>
    have  \<open>\<And>x. x \<in> complex_vector.span G \<Longrightarrow> A x = B x\<close>
      using \<open>cbounded_linear A\<close> \<open>cbounded_linear B\<close> cbounded_linear.is_clinear equal_span by blast
    hence \<open>\<forall>x.  x \<in> complex_vector.span G \<longrightarrow> F x = 0\<close>
      unfolding F_def
      by simp
    hence \<open>\<forall> x. x \<in> *s* (complex_vector.span G) \<longrightarrow> (*f* F) x = 0\<close>
      by StarDef.transfer
    thus ?thesis
      using \<open>T \<in> *s* complex_vector.span G\<close> by auto 
  qed
  hence \<open>F t = 0\<close>
    using approx_sym approx_trans calculation by fastforce    
  thus \<open>A t = B t\<close>
    unfolding F_def
    by auto
qed

lemma applyOpSpace_span:
  fixes A B :: "('a::cbanach,'b::cbanach) cblinfun"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and \<open>t \<in> space_as_set (Span G)\<close>
  shows "A *\<^sub>V t = B *\<^sub>V t"
  using assms
  apply transfer
  using equal_span_applyOpSpace by blast

lemma applyOpSpace_less_eq:
  fixes S :: "'a::cbanach linear_space" 
    and A B :: "('a::cbanach,'b::cbanach) cblinfun"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and "Span G \<ge> S"
  shows "A *\<^sub>S S \<le> B *\<^sub>S S"
  using assms
  apply transfer
proof - (* sledgehammer *)
  fix Ga :: "'a set" and Aa :: "'a \<Rightarrow> 'b" and Ba :: "'a \<Rightarrow> 'b" and Sa :: "'a set"
  assume a1: "cbounded_linear Aa"
  assume a2: "cbounded_linear Ba"
  assume a3: "\<And>x. x \<in> Ga \<Longrightarrow> Aa x = Ba x"
  assume a4: "Sa \<subseteq> closure (complex_vector.span Ga)"
  have f5: "\<forall>A Aa f fa. (A \<noteq> Aa \<or> (\<exists>a. (a::'a) \<in> Aa \<and> (f a::'b) \<noteq> fa a)) \<or> f ` A = fa ` Aa"
    by (meson image_cong)
  obtain aa :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a" where
    "\<forall>x0 x1 x2. (\<exists>v4. v4 \<in> x2 \<and> x1 v4 \<noteq> x0 v4) = (aa x0 x1 x2 \<in> x2 \<and> x1 (aa x0 x1 x2) \<noteq> x0 (aa x0 x1 x2))"
    by moura
  hence f6: "aa Ba Aa Sa \<in> Sa \<and> Aa (aa Ba Aa Sa) \<noteq> Ba (aa Ba Aa Sa) \<or> Aa ` Sa = Ba ` Sa"
    using f5 by presburger
  have f7: "\<forall>f fa A a. (\<not> cbounded_linear f \<or> \<not> cbounded_linear fa \<or> (\<exists>a. (a::'a) \<in> A \<and> (f a::'b) \<noteq> fa a) \<or> a \<notin> closure (complex_vector.span A)) \<or> f a = fa a"
    using equal_span_applyOpSpace by blast
  obtain aaa :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a" where
    "\<forall>x1 x2 x3. (\<exists>v4. v4 \<in> x1 \<and> x3 v4 \<noteq> x2 v4) = (aaa x1 x2 x3 \<in> x1 \<and> x3 (aaa x1 x2 x3) \<noteq> x2 (aaa x1 x2 x3))"
    by moura
  hence "\<forall>f fa A a. (\<not> cbounded_linear f \<or> \<not> cbounded_linear fa \<or> aaa A fa f \<in> A \<and> f (aaa A fa f) \<noteq> fa (aaa A fa f) \<or> a \<notin> closure (complex_vector.span A)) \<or> f a = fa a"
    using f7 by presburger
  hence "Aa ` Sa = Ba ` Sa"
    using f6 a4 a3 a2 a1 by blast
  thus "closure (Aa ` Sa) \<subseteq> closure (Ba ` Sa)"
    by (metis equalityE)
qed

lemma applyOpSpace_eq:
  fixes S :: "'a::chilbert_space linear_space"                        
    and A B :: "('a::chilbert_space,'b::chilbert_space) cblinfun"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and "Span G \<ge> S"
  shows "A *\<^sub>S S = B *\<^sub>S S"
  by (metis applyOpSpace_less_eq assms(1) assms(2) dual_order.antisym)

subsection \<open>Unitary\<close>

definition isometry::\<open>('a::chilbert_space,'b::chilbert_space) cblinfun \<Rightarrow> bool\<close> where
  \<open>isometry U \<longleftrightarrow> U* o\<^sub>C\<^sub>L  U = idOp\<close>

definition unitary::\<open>('a::chilbert_space,'b::chilbert_space) cblinfun \<Rightarrow> bool\<close> where
  \<open>unitary U \<longleftrightarrow> U* o\<^sub>C\<^sub>L  U  = idOp \<and> U o\<^sub>C\<^sub>L U* = idOp\<close>

lemma unitary_def': "unitary U \<longleftrightarrow> isometry U \<and> isometry (U*)"
  unfolding unitary_def isometry_def by simp

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* o\<^sub>C\<^sub>L U = idOp" 
  unfolding isometry_def 
  by simp

lemma UadjU[simp]: "unitary U \<Longrightarrow> U o\<^sub>C\<^sub>L U* = idOp"
  unfolding unitary_def isometry_def by simp


lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"(_,_)cblinfun"
  unfolding unitary_def by auto

lemma isometry_times[simp]: "isometry A \<Longrightarrow> isometry B \<Longrightarrow> isometry (A o\<^sub>C\<^sub>L B)"
  unfolding isometry_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma unitary_times[simp]: "unitary A \<Longrightarrow> unitary B \<Longrightarrow> unitary (A o\<^sub>C\<^sub>L B)"
  unfolding unitary_def' by simp

lemma unitary_surj: "unitary U \<Longrightarrow> surj (cblinfun_apply U)"
proof-
  assume \<open>unitary U\<close>
  have \<open>\<exists> t. (cblinfun_apply U) t = x\<close>
    for x
  proof-
    have \<open>(cblinfun_apply U) ((cblinfun_apply (U*)) x) = x\<close>
    proof-
      have \<open>(cblinfun_apply U) ((cblinfun_apply (U*)) x)
          = ((cblinfun_apply U) \<circ> (cblinfun_apply (U*))) x\<close>
        by simp        
      also have \<open>\<dots>
          = (cblinfun_apply ( U o\<^sub>C\<^sub>L (U*) )) x\<close>
        by (simp add: timesOp.rep_eq)
      also have \<open>\<dots>
          = (cblinfun_apply ( idOp )) x\<close>
        by (simp add: \<open>unitary U\<close>)
      also have \<open>\<dots> =  x\<close>
        by (simp add: idOp.rep_eq)        
      finally show ?thesis
        by simp 
    qed
    thus ?thesis
      by blast 
  qed
  thus ?thesis
    by (metis surj_def) 
qed

lemma unitary_image[simp]: "unitary U \<Longrightarrow> U *\<^sub>S top = top"
proof-
  assume \<open>unitary U\<close>
  hence \<open>surj (cblinfun_apply U)\<close>
    using unitary_surj by blast
  hence \<open>range (cblinfun_apply U)  = UNIV\<close>
    by simp
  hence \<open>closure (range (cblinfun_apply U))  = UNIV\<close>
    by simp
  thus ?thesis
    apply transfer
    by blast
qed

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def
  by (simp add: isometry_def) 


subsection \<open>Projectors\<close>

lift_definition Proj :: "('a::chilbert_space) linear_space \<Rightarrow> ('a,'a) cblinfun"
  is \<open>projection\<close>
  by (rule Complex_Inner_Product.projectionPropertiesA)


lemma imageOp_Proj[simp]: "(Proj S) *\<^sub>S top = S"
  apply transfer
proof
  show "closure (range (projection (S::'a set))) \<subseteq> S"
    if "closed_subspace (S::'a set)"
    for S :: "'a set"
    using that OrthoClosedEq orthogonal_complement_twice 
    by (metis closed_subspace.subspace pre_ortho_twice projectionPropertiesE subspace_cl)

  show "(S::'a set) \<subseteq> closure (range (projection S))"
    if "closed_subspace (S::'a set)"
    for S :: "'a set"
    using that
    by (metis (no_types, lifting) closure_subset image_subset_iff in_mono projection_fixed_points subsetI subset_UNIV) 
qed


lemma Proj_D1: \<open>(Proj M) = (Proj M)*\<close>
  apply transfer
  by (rule projection_D1)


lemma Proj_D2[simp]: \<open>(Proj M) o\<^sub>C\<^sub>L (Proj M) = (Proj M)\<close>
proof-
  have \<open>(cblinfun_apply (Proj M)) = projection (space_as_set M)\<close>
    apply transfer
    by blast
  moreover have \<open>(projection (space_as_set M))\<circ>(projection (space_as_set M))
                = (projection (space_as_set M)) \<close>
  proof-
    have \<open>closed_subspace (space_as_set M)\<close>
      using space_as_set by auto
    thus ?thesis
      by (simp add: projectionPropertiesC) 
  qed
  ultimately have \<open>(cblinfun_apply (Proj M)) \<circ> (cblinfun_apply (Proj M)) = cblinfun_apply (Proj M)\<close>
    by simp    
  hence \<open>cblinfun_apply ((Proj M) o\<^sub>C\<^sub>L (Proj M)) = cblinfun_apply (Proj M)\<close>
    by (simp add: timesOp.rep_eq)
  thus ?thesis using cblinfun_apply_inject
    by auto 
qed

lift_definition isProjector::\<open>('a::chilbert_space, 'a) cblinfun \<Rightarrow> bool\<close> is
  \<open>\<lambda> P. \<exists> M. closed_subspace M \<and> is_projection_on P M\<close>.

lemma Proj_I:
  \<open>P o\<^sub>C\<^sub>L P = P \<Longrightarrow> P = P* \<Longrightarrow> \<exists> M. P = Proj M \<and> space_as_set M = range (cblinfun_apply P)\<close>
  for P :: \<open>('a::chilbert_space,'a) cblinfun\<close>
proof-
  assume \<open>P o\<^sub>C\<^sub>L P = P\<close> and \<open>P = P*\<close>
  have \<open>closed (range (cblinfun_apply P))\<close>
  proof-
    have \<open>range (cblinfun_apply P) = (\<lambda> x. x - cblinfun_apply P x) -` {0}\<close>
    proof
      show "range (cblinfun_apply P) \<subseteq> (\<lambda>x. x - cblinfun_apply P x) -` {0}"
      proof
        show "x \<in> (\<lambda>x. x - cblinfun_apply P x) -` {0}"
          if "x \<in> range (cblinfun_apply P)"
          for x :: 'a
        proof-
          have \<open>\<exists> t. cblinfun_apply P t = x\<close>
            using that by blast
          then obtain t where \<open>cblinfun_apply P t = x\<close>
            by blast 
          hence \<open>x - cblinfun_apply P x = x - cblinfun_apply P (cblinfun_apply P t)\<close>
            by simp
          also have \<open>\<dots> = x - (cblinfun_apply P t)\<close>
          proof-
            have \<open>cblinfun_apply P \<circ> cblinfun_apply P = cblinfun_apply P\<close>
              by (metis \<open>P o\<^sub>C\<^sub>L P = P\<close> timesOp.rep_eq)
            thus ?thesis
              by (metis comp_apply) 
          qed
          also have \<open>\<dots> = 0\<close>
            by (simp add: \<open>cblinfun_apply P t = x\<close>)
          finally have \<open>x - cblinfun_apply P x = 0\<close>
            by blast
          thus ?thesis
            by simp 
        qed
      qed
      show "(\<lambda>x. x - cblinfun_apply P x) -` {0} \<subseteq> range (cblinfun_apply P)"
      proof
        show "x \<in> range (cblinfun_apply P)"
          if "x \<in> (\<lambda>x. x - cblinfun_apply P x) -` {0}"
          for x :: 'a
        proof-
          have \<open>x - cblinfun_apply P x = 0\<close>
            using that by blast
          hence \<open>x = cblinfun_apply P x\<close>
            by (simp add: \<open>x - cblinfun_apply P x = 0\<close> eq_iff_diff_eq_0)
          thus ?thesis
            by blast 
        qed
      qed
    qed
    moreover have \<open>closed ( (\<lambda> x. x - cblinfun_apply P x) -` {0} )\<close>
    proof-
      have \<open>closed {(0::'a)}\<close>
        by simp        
      moreover have \<open>continuous (at x) (\<lambda> x. x - cblinfun_apply P x)\<close>
        for x
      proof-
        have \<open>cblinfun_apply (idOp - P) = (\<lambda> x. x - cblinfun_apply P x)\<close>
          by (simp add: idOp.rep_eq minus_cblinfun.rep_eq)                 
        hence \<open>cbounded_linear (cblinfun_apply (idOp - P))\<close>
          using cblinfun_apply
          by blast 
        hence \<open>continuous (at x) (cblinfun_apply (idOp - P))\<close>
          by (simp add: bounded_linear_continuous)
        thus ?thesis
          using \<open>cblinfun_apply (idOp - P) = (\<lambda> x. x - cblinfun_apply P x)\<close>
          by simp
      qed
      ultimately show ?thesis  
        by (rule Abstract_Topology.continuous_closed_vimage)               
    qed
    ultimately show ?thesis
      by simp  
  qed
  have \<open>cbounded_linear (cblinfun_apply P)\<close>
    using cblinfun_apply by auto
  hence \<open>closed_subspace ( range (cblinfun_apply P) )\<close>
    using \<open>closed (range (cblinfun_apply P))\<close>
      cbounded_linear.clinear  closed_subspace.intro
    using complex_vector.linear_subspace_image complex_vector.subspace_UNIV by blast        
  hence \<open>\<exists> M. space_as_set M = (range (cblinfun_apply P))\<close>
    using  \<open>closed (range (cblinfun_apply P))\<close>
    by (metis applyOpSpace.rep_eq closure_eq top_linear_space.rep_eq)    
  then obtain M where \<open>space_as_set M = (range (cblinfun_apply P))\<close>
    by blast
  have \<open>cblinfun_apply P x \<in> space_as_set M\<close>
    for x
    by (simp add: \<open>space_as_set M = range (cblinfun_apply P)\<close>)
  moreover have \<open>x - cblinfun_apply P x \<in> orthogonal_complement ( space_as_set M)\<close>
    for x
  proof-
    have \<open>y \<in> space_as_set M \<Longrightarrow> \<langle> x - cblinfun_apply P x, y \<rangle> = 0\<close>
      for y
    proof-
      assume \<open>y \<in> space_as_set M\<close>
      hence \<open>\<exists> t. y = cblinfun_apply P t\<close>
        by (simp add: \<open>space_as_set M = range (cblinfun_apply P)\<close> image_iff)
      then obtain t where \<open>y = cblinfun_apply P t\<close>
        by blast
      have \<open>\<langle> x - cblinfun_apply P x, y \<rangle> = \<langle> x - cblinfun_apply P x, cblinfun_apply P t \<rangle>\<close>
        by (simp add: \<open>y = cblinfun_apply P t\<close>)
      also have \<open>\<dots> = \<langle> cblinfun_apply P (x - cblinfun_apply P x), t \<rangle>\<close>
        by (metis \<open>P = P*\<close> adjoint_I)
      also have \<open>\<dots> = \<langle> cblinfun_apply P x - cblinfun_apply P (cblinfun_apply P x), t \<rangle>\<close>
        by (metis \<open>P = P*\<close> adjoint_I cinner_diff_left)
      also have \<open>\<dots> = \<langle> cblinfun_apply P x - cblinfun_apply P x, t \<rangle>\<close>
      proof-
        have \<open>(cblinfun_apply P) \<circ> (cblinfun_apply P) = (cblinfun_apply P)\<close>
          using  \<open>P o\<^sub>C\<^sub>L P = P\<close>
          by (metis timesOp.rep_eq)
        thus ?thesis
          using comp_eq_dest_lhs by fastforce 
      qed
      also have \<open>\<dots> = \<langle> 0, t \<rangle>\<close>
        by simp
      also have \<open>\<dots> = 0\<close>
        by simp
      finally show ?thesis by blast
    qed
    thus ?thesis
      by (simp add: orthogonal_complement_I2) 
  qed
  ultimately have \<open>P = Proj M\<close>
  proof - (* sledgehammer *)
    have "closed_subspace (space_as_set M)"
      by (metis \<open>space_as_set M = range (cblinfun_apply P)\<close> \<open>closed_subspace (range (cblinfun_apply P))\<close>)
    hence f1: "\<forall>a. cblinfun_apply (Proj M) a = cblinfun_apply P a"
      by (simp add: Proj.rep_eq \<open>\<And>x. cblinfun_apply P x \<in> space_as_set M\<close> \<open>\<And>x. x - cblinfun_apply P x \<in> orthogonal_complement (space_as_set M)\<close> projection_uniq)
    have "\<forall>a. (+) ((a::'a) - a) = id"
      by force
    hence "\<forall>a. (+) (cblinfun_apply (P - Proj M) a) = id"
      using f1
      by (simp add: minus_cblinfun.rep_eq) 
    hence "\<forall>a aa. aa - aa = cblinfun_apply (P - Proj M) a"
      by (metis (no_types) add_diff_cancel_right' id_apply)
    hence "\<forall>a. cblinfun_apply (idOp - (P - Proj M)) a = a"
      by (simp add: idOp.rep_eq minus_cblinfun.rep_eq)      
    thus ?thesis
      by (metis (no_types) cblinfun_apply_inject diff_diff_eq2 diff_eq_diff_eq eq_id_iff idOp.rep_eq)
  qed
  thus ?thesis
    using \<open>space_as_set M = range (cblinfun_apply P)\<close> by blast 
qed

lemma Proj_isProjector[simp]:
  fixes M::\<open>'a::chilbert_space linear_space\<close>
  shows \<open>isProjector (Proj M)\<close>
  unfolding isProjector_def
  apply auto
proof
  show "closed_subspace (space_as_set M) \<and> is_projection_on ((*\<^sub>V) (Proj M)) (space_as_set M)"
  proof
    show "closed_subspace (space_as_set M)"
      using space_as_set by blast
    show "is_projection_on ((*\<^sub>V) (Proj M)) (space_as_set M)"
      unfolding is_projection_on_def
      apply auto
       apply (simp add: Proj.rep_eq \<open>closed_subspace (space_as_set M)\<close> projection_intro1)
      by (metis Proj.rep_eq \<open>closed_subspace (space_as_set M)\<close> projectionPropertiesE range_eqI)
  qed
qed

lemma isProjector_algebraic: 
  fixes P::\<open>('a::chilbert_space, 'a) cblinfun\<close>
  shows \<open>isProjector P \<longleftrightarrow> P o\<^sub>C\<^sub>L P = P \<and> P = P*\<close>
proof
  show "P o\<^sub>C\<^sub>L P = P \<and> P = P*"
    if "isProjector P"
  proof
    show "P o\<^sub>C\<^sub>L P = P"
      using that apply transfer
      using  projectionPropertiesC'
      by auto
    show "P = P*"
      using that apply transfer
      using projection_D1'
      by blast
  qed
  show "isProjector P"
    if "P o\<^sub>C\<^sub>L P = P \<and> P = P*"
    using that Proj_I Proj_isProjector
    by blast    
qed


lemma Proj_leq: "(Proj S) *\<^sub>S A \<le> S"
proof -
  have "top = sup top A"
    apply transfer
    using Complex_Vector_Spaces.subspace_UNIV is_closed_subspace_universal_inclusion_left 
    by blast 
  hence "sup S (Proj S *\<^sub>S A) = S"
    by (metis (full_types) cdot_plus_distrib imageOp_Proj)
  thus ?thesis
    by (meson sup.absorb_iff1)
qed


lemma Proj_times: "isometry A \<Longrightarrow> A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*) = Proj (A *\<^sub>S S)" 
  for A::"('a::chilbert_space,'b::chilbert_space) cblinfun"
proof-
  assume \<open>isometry A\<close>
  define P where \<open>P = A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*)\<close>
  have \<open>P o\<^sub>C\<^sub>L P = P\<close>
    using  \<open>isometry A\<close>
    unfolding P_def isometry_def
    by (metis (no_types, lifting) Proj_D2 timesOp_assoc times_idOp2)
  moreover have \<open>P = P*\<close>
    unfolding P_def
    by (metis Proj_D1 adjoint_twice timesOp_assoc times_adjoint)
  ultimately have 
    \<open>\<exists> M. P = Proj M \<and> space_as_set M = range (cblinfun_apply (A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*)))\<close>
    using P_def Proj_I by blast
  then obtain M where \<open>P = Proj M\<close>
    and \<open>space_as_set M = range (cblinfun_apply (A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*)))\<close>
    by blast
  have \<open>M = A *\<^sub>S S\<close>
  proof - (* sledgehammer *)
    have f1: "\<forall>l. A *\<^sub>S Proj S *\<^sub>S A* *\<^sub>S l = P *\<^sub>S l"
      by (simp add: P_def timesOp_assoc_linear_space)
    have f2: "\<forall>l b. b* *\<^sub>S (b *\<^sub>S (l::'a linear_space)::'b linear_space) = idOp *\<^sub>S l \<or> \<not> isometry b"
      by (metis (no_types) adjUU timesOp_assoc_linear_space)
    have f3: "\<forall>l b. b *\<^sub>S idOp *\<^sub>S (l::'a linear_space) = (b *\<^sub>S l::'a linear_space)"
      by (metis timesOp_assoc_linear_space times_idOp1)
    have "\<forall>l la. sup (Proj (la::'a linear_space) *\<^sub>S l) la = la"
      by (metis Proj_leq sup.absorb_iff2)
    thus ?thesis
      using f3 f2 f1 by (metis Proj_leq \<open>P = Proj M\<close> \<open>isometry A\<close> cdot_plus_distrib imageOp_Proj sup.order_iff)
  qed 
  thus ?thesis
    using \<open>P = Proj M\<close>
    unfolding P_def
    by blast
qed

abbreviation proj :: "'a::chilbert_space \<Rightarrow> ('a,'a) cblinfun" where "proj \<psi> \<equiv> Proj (Span {\<psi>})"

lemma projection_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" for a::complex and \<psi>::"'a::chilbert_space"
  by (metis Span.abs_eq span_mult)

lemma move_plus:
  "(Proj (- C)) *\<^sub>S A \<le> B \<Longrightarrow> A \<le> sup B C"
  for A B C::"'a::chilbert_space linear_space"
proof-
  assume \<open>(Proj (- C)) *\<^sub>S A \<le> B\<close>
  hence \<open>cBlinfun
     (projection
       (space_as_set
         (Abs_linear_space (orthogonal_complement (space_as_set C))))) *\<^sub>S A \<le> B\<close>
    unfolding Proj_def  less_eq_linear_space_def
    by (simp add: uminus_linear_space_def)

  hence proj_ortho_CAB: \<open>cBlinfun (projection (orthogonal_complement (space_as_set C))) *\<^sub>S A \<le> B\<close>
    using Proj_def \<open>Proj (- C) *\<^sub>S A \<le> B\<close> map_fun_apply
    by (simp add: Proj_def uminus_linear_space.rep_eq) 

  hence \<open>x \<in> space_as_set
              (Abs_linear_space
                (closure
                  (cblinfun_apply
                    (cBlinfun
                      (projection (orthogonal_complement (space_as_set C)))) `
                   space_as_set A))) \<Longrightarrow>
         x \<in> space_as_set B\<close>
    for x
    unfolding applyOpSpace_def less_eq_linear_space_def
    by auto
  hence \<open>x \<in>  closure (cblinfun_apply (cBlinfun
                      (projection (orthogonal_complement (space_as_set C)))) `
                   space_as_set A) \<Longrightarrow>
         x \<in> space_as_set B\<close>
    for x
    using proj_ortho_CAB
      applyOpSpace.rep_eq less_eq_linear_space.rep_eq by blast
  hence \<open>x \<in>  closure ( (projection (orthogonal_complement (space_as_set C))) `
                   space_as_set A) \<Longrightarrow>
         x \<in> space_as_set B\<close>
    for x
    using Proj.rep_eq Proj_def map_fun_apply
    by (metis (full_types) uminus_linear_space.rep_eq)

  hence \<open>x \<in> space_as_set A \<Longrightarrow>
    x \<in> closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set B \<and> \<phi> \<in> space_as_set C}\<close>
    for x
  proof-
    assume \<open>x \<in> space_as_set A\<close>
    have \<open>closed_subspace (space_as_set C)\<close>
      using space_as_set by auto
    hence \<open>x = (projection (space_as_set C)) x
       + (projection (orthogonal_complement (space_as_set C))) x\<close>
      by (simp add: ortho_decomp)
    hence \<open>x = (projection (orthogonal_complement (space_as_set C))) x
              + (projection (space_as_set C)) x\<close>
      by (metis ordered_field_class.sign_simps(2))
    moreover have \<open>(projection (orthogonal_complement (space_as_set C))) x \<in> space_as_set B\<close>
      using \<open>x \<in>  closure ( (projection (orthogonal_complement (space_as_set C))) `
                   space_as_set A) \<Longrightarrow> x \<in> space_as_set B\<close>
      by (meson \<open>\<And>x. x \<in> closure (projection (orthogonal_complement (space_as_set C)) ` space_as_set A) \<Longrightarrow> x \<in> space_as_set B\<close> \<open>x \<in> space_as_set A\<close> closure_subset image_subset_iff)
    moreover have \<open>(projection (space_as_set C)) x \<in> space_as_set C\<close>
      by (simp add: \<open>closed_subspace (space_as_set C)\<close> projection_intro2)
    ultimately show ?thesis
      using closure_subset by fastforce 
  qed
  hence \<open>x \<in> space_as_set A \<Longrightarrow>
        x \<in> (space_as_set B +\<^sub>M space_as_set C)\<close>
    for x
    unfolding closed_sum_def set_plus_def
    by (smt Collect_cong)
      (* > 1 s *)
  hence \<open> x \<in> space_as_set A \<Longrightarrow>
         x \<in> space_as_set
               (Abs_linear_space (space_as_set B +\<^sub>M space_as_set C))\<close>
    for x
    by (metis space_as_set_inverse sup_linear_space.rep_eq)
  thus ?thesis 
    by (simp add: \<open>\<And>x. x \<in> space_as_set A \<Longrightarrow> x \<in> space_as_set B +\<^sub>M space_as_set C\<close> less_eq_linear_space.rep_eq subset_eq sup_linear_space.rep_eq)    
qed


subsection \<open>Kernel\<close>

(* debate 1 Bounded_Operators
- Dominique: type class: complex_vector + topological_space
- Jose: it is more natural, in the setting of this library, to
  take the class "complex_normed_vector" in place of "complex_vector + topological_space".
  
Dominique: complex_vector+topological_space is strictly more general.
  Any theorem or definition that is proven wrt. complex_vector+topological_space
  can be directly used in a situation requiring complex_normed_vector as well.
  Thus restricting to complex_normed_vector reduces the generality of the results without
  good reason. In specific cases, of course, there are good reasons. For example,
  the type cblinfun only makes sense for complex_normed_vector because we need the norm.

  Why would complex_normed_vector be more natural in this setting?

  I am not sure which specific lemma/definition this debate refers to.
*)

lift_definition kernel :: "('a::complex_normed_vector,'b::complex_normed_vector) cblinfun \<Rightarrow> 'a linear_space" 
  is "\<lambda> f. f -` {0}"
  by (metis ker_op_lin)

definition eigenspace :: "complex \<Rightarrow> ('a::complex_normed_vector,'a) cblinfun \<Rightarrow> 'a linear_space" where
  "eigenspace a A = kernel (A - a *\<^sub>C idOp)" 

lemma kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a *\<^sub>C A) = kernel A"
  for a :: complex and A :: "(_,_) cblinfun"
  apply transfer
  using complex_vector.scale_eq_0_iff by blast

lemma kernel_0[simp]: "kernel 0 = top"
proof-
  have \<open>(\<lambda> _. 0) -` {0} = UNIV\<close>
    using Collect_cong UNIV_def
    by blast
  hence \<open>(cblinfun_apply (cblinfun_of_blinfun 0)) -` {0} = UNIV\<close>
    by (metis cblinfun_of_blinfun_zero cr_blinfun_def blinfun.pcr_cr_eq blinfun_of_cblinfun.rep_eq blinfun_of_cblinfun_zero zero_blinfun.transfer)
  hence \<open>Abs_linear_space ( (cblinfun_apply (cblinfun_of_blinfun 0)) -` {0} ) = Abs_linear_space UNIV\<close>
    using Abs_linear_space_inject
    by (simp add: \<open>(cblinfun_apply (cblinfun_of_blinfun 0)) -` {0} = UNIV\<close>)
  thus ?thesis
    unfolding kernel_def zero_cblinfun_def top_linear_space_def
    by (simp add: cBlinfun_inverse \<open>(\<lambda>_. 0) -` {0} = UNIV\<close>)   
qed

lemma kernel_id[simp]: "kernel idOp = 0"
  unfolding kernel_def
  apply transfer
  apply auto
  unfolding bot_linear_space_def
  by blast

lemma scaleC_eigenspace[simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a *\<^sub>C A) = eigenspace (b/a) A"
proof -
  assume a1: "a \<noteq> 0"
  hence "b *\<^sub>C (idOp::('a, _) cblinfun) = a *\<^sub>C (b / a) *\<^sub>C idOp"
    by (metis Complex_Vector_Spaces.eq_vector_fraction_iff)
  hence "kernel (a *\<^sub>C A - b *\<^sub>C idOp) = kernel (A - (b / a) *\<^sub>C idOp)"
    using a1 by (metis (no_types) complex_vector.scale_right_diff_distrib kernel_scalar_times)
  thus ?thesis 
    unfolding eigenspace_def 
    by blast
qed

subsection \<open>Option\<close>

definition "inj_option \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"

definition 
  "inv_option \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (Hilbert_Choice.inv \<pi> (Some y)) else None)"

lemma inj_option_Some_pi[simp]: "inj_option (Some o \<pi>) = inj \<pi>"
  unfolding inj_option_def inj_def by simp

lemma inj_option_Some[simp]: "inj_option Some"
  by (simp add: inj_option_def)

lemma inv_option_Some: "surj \<pi> \<Longrightarrow> inv_option (Some o \<pi>) = Some o (Hilbert_Choice.inv \<pi>)"
  unfolding inv_option_def o_def inv_def apply (rule ext) by auto

lemma inj_option_map_comp[simp]: "inj_option f \<Longrightarrow> inj_option g \<Longrightarrow> inj_option (f \<circ>\<^sub>m g)"
  unfolding inj_option_def apply auto
  using map_comp_Some_iff by smt

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
  thus "x = y"
    by (meson inv_into_injective option.inject x_pi y_pi)
qed

subsection \<open>New/restored things\<close>


lemma isProjector_D1: \<open>isProjector P \<Longrightarrow> P o\<^sub>C\<^sub>L P = P\<close>
  unfolding isProjector_def
  apply auto
  by (metis projectionPropertiesC' timesOp.rep_eq cblinfun_apply_inject)

lemma isProjector_D2: \<open>isProjector P \<Longrightarrow> P* = P\<close>
  unfolding isProjector_def
  by (metis isProjector_algebraic isProjector_def) 


lemma isProjector_I: \<open>P o\<^sub>C\<^sub>L P = P \<Longrightarrow> P* = P \<Longrightarrow> isProjector P\<close>
  unfolding isProjector_def
  by (metis (mono_tags, lifting) isProjector_algebraic isProjector_def) 

lemma isProjector0[simp]: "isProjector ( 0::('a::chilbert_space, 'a) cblinfun )"
  unfolding isProjector_def is_projection_on_def
  apply auto
proof
  define M where \<open>M = {(0::'a::chilbert_space)}\<close>
  show "closed_subspace M \<and> (\<forall>h. (h::'a) - 0 *\<^sub>V h \<in> orthogonal_complement M \<and> 0 *\<^sub>V h \<in> M)"
    unfolding M_def
  proof
    show "closed_subspace {0::'a}"
      by simp

    show "\<forall>h. (h::'a) - 0 *\<^sub>V h \<in> orthogonal_complement {0} \<and> 0 *\<^sub>V h \<in> {0::'a}"
      by (simp add: zero_cblinfun.rep_eq)    
  qed
qed

lemma isProjectoridMinus[simp]: "isProjector P \<Longrightarrow> isProjector (idOp-P)"
proof (rule isProjector_I)
  show "(idOp - P) o\<^sub>C\<^sub>L (idOp - P) = idOp - P"
    if "isProjector P"
  proof -
    have f1: "P o\<^sub>C\<^sub>L P = P \<and> P* = P"
      using isProjector_algebraic that by auto

    hence "(idOp - P) o\<^sub>C\<^sub>L (idOp - P) = ((idOp - P) o\<^sub>C\<^sub>L (idOp - P))*"
      by auto
    thus ?thesis
      using f1 by (simp add: timesOp_minus)
  qed    
  show "(idOp - P)* = idOp - P"
    if "isProjector P"
    using that
    by (simp add: isProjector_algebraic)
qed

lemma applyOp0[simp]: "0 *\<^sub>V \<psi> = 0"
  apply transfer by simp

lemma apply_idOp[simp]: "idOp *\<^sub>V \<psi> = \<psi>"
  apply transfer by simp


lemma rel_interior_sing_generalized:
  fixes a :: "'n::chilbert_space"
  shows "rel_interior {a} = {a}"
  apply (auto simp: rel_interior_ball)
  by (metis affine_sing gt_ex le_infI2 subset_hull subset_singleton_iff)


(* Move to Missing *)
lemma subspace_rel_interior:
  fixes S::\<open>'a::chilbert_space set\<close>
  assumes \<open>complex_vector.subspace S\<close>
  shows \<open>0 \<in> rel_interior S\<close>
proof-
  {  assume a1: "affine hull S \<subseteq> S"
    have f2: "\<not> (1::real) \<le> 0"
      by auto
    have "\<forall>x0. ((0::real) < x0) = (\<not> x0 \<le> 0)"
      by auto
    hence "\<exists>r>0. ball 0 r \<inter> affine hull S \<subseteq> S"
      using f2 a1 by (metis inf.coboundedI2)
  } note 1 = this

  have \<open>affine S\<close>
  proof-
    have \<open>x\<in>S \<Longrightarrow> y\<in>S \<Longrightarrow>  u + v = 1 \<Longrightarrow> u *\<^sub>R x + v *\<^sub>R y \<in> S\<close>
      for x y u v
    proof-
      assume \<open>x\<in>S\<close> and \<open>y\<in>S\<close> and \<open>u + v = 1\<close>
      have \<open>(u::complex) *\<^sub>C x \<in> S\<close>
        using \<open>complex_vector.subspace S\<close>
        unfolding complex_vector.subspace_def
        by (simp add: \<open>x \<in> S\<close>)
      hence \<open>u *\<^sub>R x \<in> S\<close>
        by (simp add: scaleR_scaleC)
      have \<open>(v::complex) *\<^sub>C y \<in> S\<close>
        using \<open>complex_vector.subspace S\<close>
        unfolding complex_vector.subspace_def
        by (simp add: \<open>y \<in> S\<close>)
      hence \<open>v *\<^sub>R y \<in> S\<close>
        by (simp add: scaleR_scaleC)
      show \<open> u *\<^sub>R x + v *\<^sub>R y \<in> S\<close> 
        using \<open>complex_vector.subspace S\<close>
        unfolding complex_vector.subspace_def
        by (simp add:  \<open>u *\<^sub>R x \<in> S\<close>  \<open>v *\<^sub>R y \<in> S\<close>)
    qed
    thus ?thesis 
      unfolding affine_def by blast
  qed
  hence \<open>affine hull S \<subseteq> S\<close>
    unfolding  hull_def by auto
  thus ?thesis 
    apply (auto simp: rel_interior_ball)
    using assms
     apply (simp add: complex_vector.subspace_0)
    apply (rule 1)
    by blast
qed


(*
lemma mult_INF_less_eq_transfer_bij:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space set" 
    and U :: "'b \<Rightarrow>'c::chilbert_space"
  assumes \<open>cbounded_linear U\<close> 
       and \<open>\<forall>i. closed_subspace (V i)\<close>  
       and \<open>bij U\<close>
  shows \<open>\<Inter> (range (\<lambda> i. closure (U ` V i))) = closure (U ` \<Inter> (range V))\<close>
proof-
  define I where \<open>I = range (\<lambda> i. U ` (V i))\<close>
  have \<open>S\<in>I \<Longrightarrow> complex_vector.subspace S\<close>
    for S
  proof-
    assume \<open>S\<in>I\<close>
    hence \<open>\<exists> i. S = U ` (V i)\<close>
      unfolding I_def by auto
    then obtain i where \<open>S = U ` (V i)\<close>
      by blast
    have \<open>closed_subspace (V i)\<close>
      by (simp add: assms(2))
    thus \<open>complex_vector.subspace S\<close>
      using  \<open>S = U ` (V i)\<close> \<open>cbounded_linear U\<close>
      by (simp add: cbounded_linear.clinear complex_vector.subspace_image closed_subspace.complex_vector.subspace)
  qed
  hence \<open>\<forall>S\<in>I. convex S\<close>
    using linear_manifold_Convex by blast
  moreover have \<open>\<Inter>{rel_interior S |S. S \<in> I} \<noteq> {}\<close>
  proof-
    have \<open>S \<in> I \<Longrightarrow> 0 \<in> rel_interior S\<close>
      for S
    proof-
      assume \<open>S \<in> I\<close>
      hence \<open>complex_vector.subspace S\<close>
        by (simp add: \<open>\<And>S. S \<in> I \<Longrightarrow> complex_vector.subspace S\<close>)
      thus ?thesis using complex_vector.subspace_rel_interior
        by (simp add: complex_vector.subspace_rel_interior) 
    qed
    thus ?thesis by blast
  qed
  ultimately have "closure (\<Inter>I) = \<Inter>{closure S |S. S \<in> I}"
    by (rule convex_closure_inter_generalized)
  moreover have \<open>closure (\<Inter>I) = closure (U ` \<Inter> (range V))\<close>
  proof-
    have \<open>U ` \<Inter> (range V) = (\<Inter>i. U ` V i)\<close>
      using \<open>bij U\<close>  Complete_Lattices.bij_image_INT
      by metis      
    hence \<open>(\<Inter>I) = (U ` \<Inter> (range V))\<close>
      unfolding I_def
      by auto
    thus ?thesis
      by simp 
  qed
  moreover have \<open>\<Inter>{closure S |S. S \<in> I} = \<Inter> (range (\<lambda> i. closure (U ` V i)))\<close>
    unfolding I_def
    by (simp add: Setcompr_eq_image)
  ultimately show ?thesis by simp
qed

lift_definition BIJ::\<open>('a::complex_normed_vector,'b::complex_normed_vector) cblinfun \<Rightarrow> bool\<close> 
is bij.
*)

lemma isCont_applyOp[simp]: "isCont ((*\<^sub>V) A) \<psi>"
  apply transfer
  by (simp add: bounded_linear_continuous) 

lemma applyOpSpace_mono:
  "S \<le> T \<Longrightarrow> A *\<^sub>S S \<le> A *\<^sub>S T"
  by (simp add: applyOpSpace.rep_eq closure_mono image_mono less_eq_linear_space.rep_eq)

lemma apply_left_neutral:
  assumes "A o\<^sub>C\<^sub>L B = B"
  assumes "\<psi> \<in> space_as_set (B *\<^sub>S top)"
  shows "A *\<^sub>V \<psi> = \<psi>" 
proof -
  define rangeB rangeB' where "rangeB = space_as_set (B *\<^sub>S top)" and "rangeB' = range (cblinfun_apply B)"
  from assms have "\<psi> \<in> closure rangeB'"
    unfolding rangeB'_def apply (transfer fixing: \<psi>) by simp
  then obtain \<psi>i where \<psi>i_lim: "\<psi>i \<longlonglongrightarrow> \<psi>" and \<psi>i_B: "\<psi>i i \<in> rangeB'" for i
    apply atomize_elim using closure_sequential by blast
  have A_invariant: "A *\<^sub>V \<psi>i i = \<psi>i i" for i
  proof -
    from \<psi>i_B obtain \<phi> where \<phi>: "\<psi>i i = B *\<^sub>V \<phi>"
      apply atomize_elim unfolding rangeB'_def apply transfer by auto
    hence "A *\<^sub>V \<psi>i i = (A o\<^sub>C\<^sub>L B) *\<^sub>V \<phi>"
      by (simp add: timesOp.rep_eq)
    also have "\<dots> = B *\<^sub>V \<phi>"
      by (simp add: assms)
    also have "\<dots> = \<psi>i i"
      by (simp add: \<phi>)
    finally show ?thesis
      by -
  qed
  from \<psi>i_lim have "(\<lambda>i. A *\<^sub>V (\<psi>i i)) \<longlonglongrightarrow> A *\<^sub>V \<psi>"
    by (rule isCont_tendsto_compose[rotated], simp)
  with A_invariant have "(\<lambda>i. \<psi>i i) \<longlonglongrightarrow> A *\<^sub>V \<psi>"
    by auto
  with \<psi>i_lim show "A *\<^sub>V \<psi> = \<psi>"
    using LIMSEQ_unique by blast
qed

lemma range_adjoint_isometry:
  assumes "isometry U"
  shows "U* *\<^sub>S top = top"
proof -
  from assms have "top = U* *\<^sub>S U *\<^sub>S top"
    by (metis adjUU applyOpSpace_id timesOp_assoc_linear_space)
  also have "\<dots> \<le> U* *\<^sub>S top"
    by (simp add: applyOpSpace_mono)
  finally show ?thesis
    using top.extremum_unique by blast
qed


lemma mult_INF_general[simp]: 
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space linear_space"
    and U :: "('b,'c::chilbert_space) cblinfun"
    and Uinv :: "('c,'b) cblinfun" 
  assumes UinvUUinv: "Uinv o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Uinv = Uinv"
    and UUinvU: "U o\<^sub>C\<^sub>L Uinv o\<^sub>C\<^sub>L U = U"
    and V: "\<And>i. V i \<le> Uinv *\<^sub>S top"
  shows "U *\<^sub>S (INF i. V i) = (INF i. U *\<^sub>S V i)"
proof (rule antisym)
  show "U *\<^sub>S (INF i. V i) \<le> (INF i. U *\<^sub>S V i)"
    by (rule mult_INF1)
next
  define rangeU rangeUinv where "rangeU = U *\<^sub>S top" and "rangeUinv = Uinv *\<^sub>S top"
  define INFUV INFV where "INFUV = (INF i. U *\<^sub>S V i)" and "INFV = (INF i. V i)"
  have "INFUV = U *\<^sub>S Uinv *\<^sub>S INFUV"
  proof -
    have "U *\<^sub>S V i \<le> rangeU" for i
      unfolding rangeU_def apply transfer apply auto
      by (meson closure_mono image_mono subsetD top_greatest)
    hence "INFUV \<le> rangeU"
      unfolding INFUV_def by (meson INF_lower UNIV_I order_trans)
    moreover have "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeU" for \<psi>
      apply (rule apply_left_neutral[where B=U])
      using assms that rangeU_def by auto
    ultimately have "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set INFUV" for \<psi>
      by (simp add: in_mono less_eq_linear_space.rep_eq that)
    hence "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>S INFUV = INFUV"
      apply transfer apply auto
       apply (metis closed_sum_def closure_closure is_closed_subspace_zero)
      using closure_subset by blast
    thus ?thesis
      by (simp add: timesOp_assoc_linear_space)
  qed
  also have "\<dots> \<le> U *\<^sub>S (INF i. Uinv *\<^sub>S U *\<^sub>S V i)"
    unfolding INFUV_def
    apply (rule applyOpSpace_mono)
    by (rule mult_INF1)
  also have "\<dots> = U *\<^sub>S INFV"
  proof -
    from assms have "V i \<le> rangeUinv" for i
      unfolding rangeUinv_def by simp
    moreover have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeUinv" for \<psi>
      apply (rule apply_left_neutral[where B=Uinv])
      using assms that rangeUinv_def by auto
    ultimately have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set (V i)" for \<psi> i
      using less_eq_linear_space.rep_eq that by blast
    hence "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>S (V i) = (V i)" for i
      apply transfer apply auto
       apply (metis closed_sum_def closure_closure is_closed_subspace_zero)
      using closure_subset by blast
    thus ?thesis
      unfolding INFV_def
      by (simp add: timesOp_assoc_linear_space)
  qed
  finally show "INFUV \<le> U *\<^sub>S INFV".
qed

lemma mult_INF[simp]: 
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space linear_space" and U :: "('b,'c::chilbert_space) cblinfun"
  assumes \<open>isometry U\<close>
  shows "U *\<^sub>S (INF i. V i) = (INF i. U *\<^sub>S V i)"
proof -
  from \<open>isometry U\<close> have "U* o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L U* = U*"
    unfolding isometry_def by simp
  moreover from \<open>isometry U\<close> have "U o\<^sub>C\<^sub>L U* o\<^sub>C\<^sub>L U = U"
    unfolding isometry_def
    by (simp add: timesOp_assoc)
  moreover have "V i \<le> U* *\<^sub>S top" for i
    by (simp add: range_adjoint_isometry assms)
  ultimately show ?thesis
    by (rule mult_INF_general)
qed

lemma leq_INF[simp]:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space linear_space"
  shows "(A \<le> (INF x. V x)) = (\<forall>x. A \<le> V x)"
  by (simp add: le_Inf_iff)

lemma times_applyOp: "(A o\<^sub>C\<^sub>L B) *\<^sub>V \<psi> = A *\<^sub>V (B *\<^sub>V \<psi>)"
  apply transfer by simp

lemma mult_inf_distrib[simp]:
  fixes U::\<open>('a::chilbert_space,'b::chilbert_space) cblinfun\<close>
    and X Y::"'a linear_space"
  assumes "isometry U"
  shows "U *\<^sub>S (inf X Y) = inf (U *\<^sub>S X) (U *\<^sub>S Y)"
  using mult_INF[where V="\<lambda>b. if b then X else Y" and U=U]
  unfolding INF_UNIV_bool_expand
  using assms by auto

lemma applyOp_scaleC1[simp]: "(c *\<^sub>C A) *\<^sub>V \<psi> = c *\<^sub>C (A *\<^sub>V \<psi>)"
  apply transfer by simp

lemma applyOp_scaleC2[simp]: "A *\<^sub>V (c *\<^sub>C \<psi>) = c *\<^sub>C (A *\<^sub>V \<psi>)"
  apply transfer 
  using cbounded_linear.clinear
  by (simp add: cbounded_linear.is_clinear complex_vector.linear_scale)


definition bifunctional :: \<open>'a \<Rightarrow> (('a \<Rightarrow> complex) \<Rightarrow> complex)\<close> where
  \<open>bifunctional x = (\<lambda> f. f x)\<close>

lift_definition Bifunctional' :: \<open>'a::complex_normed_vector \<Rightarrow> (('a, complex) cblinfun \<Rightarrow> complex)\<close> 
  is bifunctional.

lift_definition Bifunctional :: \<open>'a::complex_normed_vector \<Rightarrow> (('a, complex) cblinfun, complex) cblinfun\<close> 
  is Bifunctional'
proof
  show "clinear (Bifunctional' (a::'a))"
    for a :: 'a
    unfolding clinear_def proof
    show "Bifunctional' a (b1 + b2) = Bifunctional' a b1 + Bifunctional' a b2"
      for b1 :: "('a, complex) cblinfun"
        and b2 :: "('a, complex) cblinfun"
      by (simp add: Bifunctional'.rep_eq bifunctional_def plus_cblinfun.rep_eq)
    show "Bifunctional' a (r *\<^sub>C b) = r *\<^sub>C Bifunctional' a b"
      for r :: complex
        and b :: "('a, complex) cblinfun"
      by (simp add: Bifunctional'.rep_eq bifunctional_def)    
  qed
  show "\<exists>K. \<forall>x. cmod (Bifunctional' (a::'a) x) \<le> norm x * K"
    for a :: 'a
    apply transfer
    apply auto unfolding bifunctional_def
    using cbounded_linear.bounded_linear onorm by blast 
qed

lemma norm_of_cblinfun:
  \<open>norm (L *\<^sub>V z) \<le> norm z * norm L\<close>
  apply transfer
  by (simp add: cbounded_linear.bounded_linear linordered_field_class.sign_simps(24) onorm)

lemma norm_of_cblinfun1:
  \<open>norm z = 1 \<Longrightarrow> norm (L *\<^sub>V z) \<le> norm L\<close>
  using norm_of_cblinfun
  by (metis mult_cancel_right1) 

lemma norm_of_cblinfun2:
  \<open>norm z \<le> 1 \<Longrightarrow> norm (L *\<^sub>V z) \<le> norm L\<close>
proof (cases \<open>z = 0\<close>)
  show "norm (L *\<^sub>V z) \<le> norm L"
    if "norm z \<le> 1"
      and "z = 0"
    using that
    by (smt mult_cancel_left1 norm_ge_zero norm_of_cblinfun norm_zero)

  show "norm (L *\<^sub>V z) \<le> norm L"
    if "norm z \<le> 1"
      and "z \<noteq> 0"
    using that
    by (smt mult_left_le_one_le norm_ge_zero norm_of_cblinfun) 
qed

lemma onormless1: 
  assumes a1: "norm x < 1" and a2: "cbounded_linear f"
  shows "norm (f x) \<le> onorm f"
proof-
  have "norm (f x) \<le> onorm f * norm x"
    using a2 onorm
    by (simp add: onorm cbounded_linear.bounded_linear)    
  also have "\<dots> \<le> onorm f"
    using a1 a2 mult_right_le_one_le onorm_pos_le
    by (smt cbounded_linear.bounded_linear norm_not_less_zero) 
  finally show ?thesis by blast
qed

lemma norm1_normless1_approx:
  assumes a1: "norm t = 1" and a2: "e > 0"
  shows "\<exists>s. norm s < 1 \<and> norm (t - s) < e"
proof(cases "e > 1")
  case True
  thus ?thesis
    by (smt a1 diff_zero norm_zero) 
next
  case False
  define s where "s = (1-e/2) *\<^sub>R t"
  have a1:"1-e/2 < 1"
    by (simp add: a2)
  moreover have "norm s = abs (1-e/2) * norm t"
    unfolding s_def by auto
  ultimately have b1: "norm s < 1"
    using a1 False assms(1) by auto 

  have "t - s = (e/2) *\<^sub>R t"
    unfolding s_def
    by (smt diff_eq_eq scaleR_collapse) 
  hence "norm (t - s) = abs (e/2) * norm t"
    by simp    
  hence b2: "norm (t - s) < e"
    using a1 assms(1) by auto 
  from b1 b2 show ?thesis by blast
qed


lemma norm_of_cblinfun3:
  fixes S::"'a::{complex_normed_vector,not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector"
  shows "norm S = Sup {norm (S *\<^sub>V x)| x. norm x < 1}"
proof transfer 
  have a1: \<open>(UNIV::'a set) \<noteq> 0\<close>
    by simp
  fix S::\<open>'a \<Rightarrow> 'b\<close>
  assume a2: \<open>cbounded_linear S\<close>
  define X where X_def: "X = {norm (S x) |x. norm x < 1}"
  define a where a_def: "a = onorm S"
  have "x \<in> X \<Longrightarrow> x \<le> a" for x
    unfolding X_def a_def 
  proof-
    assume x1: "x \<in> {norm (S x) |x. norm x < 1}"
    then obtain x' where x2: "x = norm (S x')" and x3: "norm x' < 1"
      by blast
    have "norm (S x') \<le> onorm S"
      using x3 a2 onormless1 cbounded_linear.bounded_linear by auto
    thus "x \<le> onorm S"
      by (simp add: x2) 
  qed
  moreover have "(\<And>x. x \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> a \<le> y" for y
  proof-
    assume "\<And>x. x \<in> X \<Longrightarrow> x \<le> y"
    hence f1: "norm t < 1 \<Longrightarrow> norm (S t) \<le> y" for t
      unfolding X_def by blast 
    have "e>0 \<Longrightarrow> onorm S \<le> y+e" for e
    proof-
      assume e0:"e>0"
      have \<open>cbounded_linear S\<close>
        using a2
        by (simp add: cbounded_linear.bounded_linear)
      hence "onorm S = Sup { norm (S t) |t. norm t = 1 }"
        using a1 onorm_sphere[where f = S]
        by (simp add: cbounded_linear.bounded_linear)
      hence "onorm S - e/2 < Sup { norm (S t) |t. norm t = 1 }"
        by (simp add: e0)        
      moreover have "{ norm (S t) |t. norm t = 1 } \<noteq> {}"
      proof-
        have "\<exists>t::'a. norm t = 1"
          using a1 ex_norm1
          by (simp add: ex_norm1) 
        thus ?thesis
          by simp 
      qed
      ultimately have "\<exists>T\<in>{ norm (S t) |t. norm t = 1 }. onorm S - e/2 \<le> T"
        using e0 Sup_real_def
        by (meson less_cSupE less_eq_real_def)
      hence "\<exists>t. norm t = 1 \<and> onorm S - e/2 \<le> norm (S t)"
        by auto
      then obtain t where s1: "norm t = 1" and s2: "onorm S - e/2 \<le> norm (S t)"
        by blast
      have "isCont S w" for w
        using linear_continuous_at
        by (simp add: a2 bounded_linear_continuous)
      hence "isCont (\<lambda>x. norm (S x)) w" for w
        by simp
      hence "e > 0 \<Longrightarrow> \<exists>\<delta>>0. \<forall>s. norm (t - s) < \<delta> \<longrightarrow>  norm (norm (S t) - norm (S s)) < e" for e
        unfolding isCont_def LIM_def using dist_norm
        by (metis dist_commute eq_iff_diff_eq_0 norm_eq_zero) 
      hence "\<exists>\<delta>>0. \<forall>s. norm (t - s) < \<delta> \<longrightarrow> norm (norm (S t) - norm (S s)) < e/2"
        using e0 half_gt_zero by blast
      then obtain \<delta> where delta1: "\<delta>>0" and 
        delta2: "\<forall>s. norm (t - s) < \<delta> \<longrightarrow> norm (norm (S t) - norm (S s)) < e/2"
        by blast
      have "\<exists>s. norm s < 1 \<and> norm (t - s) < \<delta>"        
        by (simp add: norm1_normless1_approx delta1 s1) 
      then obtain s where b1:"norm s < 1" and b2:"norm (t - s) < \<delta>"
        by blast
      have w:"norm (norm (S t) - norm (S s)) < e/2"
        using b2 delta2 by auto
      have "norm (S t) \<le> norm (S s) + norm (norm (S t) - norm (S s))"
        by auto
      hence "norm (S t) \<le> norm (S s) + e/2"
        using w by linarith        
      moreover have "norm (S s) \<le> y"
        using f1
        by (simp add: b1)         
      ultimately show "onorm S \<le> y+e"
        using s2 by linarith        
    qed
    hence "onorm S \<le> y"
      using linordered_field_class.field_le_epsilon by blast      
    thus "a \<le> y"
      unfolding a_def by blast
  qed
  ultimately have "Sup X = a"
    using cSup_eq by blast
  thus "onorm S = Sup {norm (S x) |x. norm x < 1}"
    unfolding X_def a_def by simp
qed

subsection \<open>Inverse\<close>

lemma inverse_cblinfun_uniq':
  \<open>A o\<^sub>C\<^sub>L B = idOp \<Longrightarrow> B o\<^sub>C\<^sub>L A = idOp \<Longrightarrow> A o\<^sub>C\<^sub>L B' = idOp \<Longrightarrow> B' o\<^sub>C\<^sub>L A = idOp \<Longrightarrow> B = B'\<close>
proof-
  assume \<open>A o\<^sub>C\<^sub>L B = idOp\<close> and \<open>B o\<^sub>C\<^sub>L A = idOp\<close> and \<open>A o\<^sub>C\<^sub>L B' = idOp\<close> and \<open>B' o\<^sub>C\<^sub>L A = idOp\<close>
  have \<open>B *\<^sub>V x = B' *\<^sub>V x\<close>
    for x
  proof-
    have \<open>(A o\<^sub>C\<^sub>L B) *\<^sub>V x = x\<close>
      using \<open>A o\<^sub>C\<^sub>L B = idOp\<close>
      by simp
    hence \<open>B' *\<^sub>V ((A o\<^sub>C\<^sub>L B) *\<^sub>V x) = B' *\<^sub>V x\<close>
      by simp
    moreover have \<open>B' *\<^sub>V ((A o\<^sub>C\<^sub>L B) *\<^sub>V x) = B *\<^sub>V x\<close>
    proof-
      have \<open>B' *\<^sub>V ((A o\<^sub>C\<^sub>L B) *\<^sub>V x) = B' *\<^sub>V (A *\<^sub>V (B *\<^sub>V x))\<close>
        by (simp add: times_applyOp)
      also have \<open>\<dots> = (B' o\<^sub>C\<^sub>L A) *\<^sub>V (B *\<^sub>V x)\<close>
        by (simp add: times_applyOp)
      also have \<open>\<dots> = idOp *\<^sub>V (B *\<^sub>V x)\<close>
        by (simp add: \<open>B' o\<^sub>C\<^sub>L A = idOp\<close>)
      also have \<open>\<dots> = B *\<^sub>V x\<close>
        by simp
      finally show ?thesis by blast
    qed
    ultimately show ?thesis by auto
  qed
  thus ?thesis
    by (metis \<open>A o\<^sub>C\<^sub>L B' = idOp\<close> \<open>B o\<^sub>C\<^sub>L A = idOp\<close> timesOp_assoc times_idOp1 times_idOp2) 
qed

definition invertible_cblinfun::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun \<Rightarrow> bool\<close> where
  \<open>invertible_cblinfun A = (\<exists> B. A o\<^sub>C\<^sub>L B = idOp \<and> B o\<^sub>C\<^sub>L A = idOp)\<close>

definition inverse_cblinfun::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun \<Rightarrow> ('b,'a) cblinfun\<close> where
  \<open>inverse_cblinfun A = (THE B. A o\<^sub>C\<^sub>L B = idOp \<and> B o\<^sub>C\<^sub>L A = idOp)\<close>

lemma inverse_cblinfun_well_defined:
  \<open>invertible_cblinfun A \<Longrightarrow> \<exists>! B. A o\<^sub>C\<^sub>L B = idOp \<and> B o\<^sub>C\<^sub>L A = idOp\<close>
  by (meson inverse_cblinfun_uniq' invertible_cblinfun_def)

lemma inverse_cblinfun_left:
  \<open>invertible_cblinfun A \<Longrightarrow> (inverse_cblinfun A) o\<^sub>C\<^sub>L A = idOp\<close>
proof-
  assume \<open>invertible_cblinfun A\<close>
  hence \<open>\<exists>! B. A o\<^sub>C\<^sub>L B = idOp \<and> B o\<^sub>C\<^sub>L A = idOp\<close>
    using inverse_cblinfun_well_defined by blast
  hence \<open>A o\<^sub>C\<^sub>L (inverse_cblinfun A) = idOp \<and> (inverse_cblinfun A) o\<^sub>C\<^sub>L A = idOp\<close>
    unfolding inverse_cblinfun_def
    by (smt theI)
  thus ?thesis by blast
qed

lemma inverse_cblinfun_right:
  \<open>invertible_cblinfun A \<Longrightarrow> A o\<^sub>C\<^sub>L (inverse_cblinfun A) = idOp\<close>
proof-
  assume \<open>invertible_cblinfun A\<close>
  hence \<open>\<exists>! B. A o\<^sub>C\<^sub>L B = idOp \<and> B o\<^sub>C\<^sub>L A = idOp\<close>
    using inverse_cblinfun_well_defined by blast
  hence \<open>A o\<^sub>C\<^sub>L (inverse_cblinfun A) = idOp \<and> (inverse_cblinfun A) o\<^sub>C\<^sub>L A = idOp\<close>
    unfolding inverse_cblinfun_def
    by (smt theI)
  thus ?thesis by blast
qed

lemma inverse_cblinfun_uniq:
  \<open>A o\<^sub>C\<^sub>L B = idOp \<Longrightarrow> B o\<^sub>C\<^sub>L A = idOp \<Longrightarrow> inverse_cblinfun A = B\<close>
  using inverse_cblinfun_left inverse_cblinfun_right inverse_cblinfun_uniq' invertible_cblinfun_def 
  by blast

hide_fact inverse_cblinfun_uniq'


subsection \<open>Recovered theorems\<close>

(*
consts
  adjoint :: "('a,'b) cblinfun \<Rightarrow> ('b,'a) cblinfun" ("_*" [99] 100)
 timesOp :: "('b,'c) cblinfun \<Rightarrow> ('a,'b) cblinfun \<Rightarrow> ('a,'c) cblinfun" 
(* and applyOp :: "('a,'b) cblinfun \<Rightarrow> 'a vector \<Rightarrow> 'b vector" *)
 applyOpSpace :: "('a,'b) cblinfun \<Rightarrow> 'a subspace \<Rightarrow> 'b subspace"
 timesScalarOp :: "complex \<Rightarrow> ('a,'b) cblinfun \<Rightarrow> ('a,'b) cblinfun"
 timesScalarSpace :: "complex \<Rightarrow> 'a subspace \<Rightarrow> 'a subspace"
*)


lemma timesScalarSpace_0[simp]: "0 *\<^sub>S S = (0::_::{complex_vector,t1_space} linear_space)"
proof (auto, transfer)
  fix S :: "'b set"
  assume "closed_subspace S"
  hence "0 \<in> S"
    unfolding closed_subspace_def Complex_Vector_Spaces.subspace_def 
    by blast
  hence "(\<lambda>_. 0) ` S = {0::'a}"
    by auto
  hence "closure ((\<lambda>_. 0) ` S) = closure {0::'a}"
    by simp
  also have "closure {0} = {0::'a}"
    by simp
  finally show "closure ((\<lambda>_. 0) ` S) = {0::'a}"
    by simp
qed


lemma one_times_op[simp]: "(1::complex) *\<^sub>C B = B"
  for B::\<open>'a::complex_normed_vector linear_space\<close>
  by simp

lemma timesOp_assoc_subspace: "(A o\<^sub>C\<^sub>L B) *\<^sub>S S =  A *\<^sub>S (B *\<^sub>S S)"
  by (simp add: timesOp_assoc_linear_space) 


lift_definition vector_to_cblinfun :: \<open>'a::complex_normed_vector \<Rightarrow> ('b::one_dim,'a) cblinfun\<close> is
  \<open>\<lambda>\<psi> \<phi>. one_dim_to_complex \<phi> *\<^sub>C \<psi>\<close>
  by (simp add: cbounded_linear_one_dim_to_complex cbounded_linear_scaleC_const)

lemma vector_to_cblinfun_applyOp: 
  "vector_to_cblinfun (A *\<^sub>V \<psi>) = A  o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>)" 
  apply transfer 
  unfolding one_dim_to_complex_def comp_def cbounded_linear_def clinear_def Vector_Spaces.linear_def
    module_hom_def module_hom_axioms_def
  by simp

lemma vector_to_cblinfun_scalar_times: 
  "vector_to_cblinfun (a *\<^sub>C \<psi>) = a *\<^sub>C vector_to_cblinfun \<psi>" for a::complex
  apply (subst asm_rl[of "a *\<^sub>C \<psi> = (a *\<^sub>C idOp) *\<^sub>V \<psi>"])
   apply simp
  apply (subst vector_to_cblinfun_applyOp)
  by simp

lift_definition cblinfun_to_blinfun::\<open>('a::complex_normed_vector,'b::complex_normed_vector) cblinfun \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'b)\<close> 
  is \<open>(\<lambda>f. ((*\<^sub>V) f))\<close>
  apply transfer
  by (simp add: cbounded_linear.bounded_linear)

lemma cblinfun_to_blinfun_norm: "norm (cblinfun_to_blinfun F) = norm F"
  by (simp add: cblinfun_to_blinfun.rep_eq norm_blinfun.rep_eq norm_cblinfun.rep_eq)

theorem banach_steinhaus_cblinfun:
  fixes F :: \<open>'c \<Rightarrow> ('a::cbanach, 'b::complex_normed_vector) cblinfun\<close>
  assumes \<open>\<And> x. \<exists> M. \<forall> n.  norm ((F n) *\<^sub>V x) \<le> M\<close>
  shows  \<open>\<exists> M. \<forall> n. norm (F n) \<le> M\<close>  
proof-
  define f where f_def: "f x = cblinfun_to_blinfun (F x)" for x
  have  \<open>\<And> x. \<exists> M. \<forall> n.  norm (blinfun_apply (f n) x) \<le> M\<close>
    using  \<open>\<And> x. \<exists> M. \<forall> n.  norm ((F n) *\<^sub>V x) \<le> M\<close>
    by (simp add: cblinfun_to_blinfun.rep_eq \<open>f \<equiv> \<lambda>x. cblinfun_to_blinfun (F x)\<close>)
  hence \<open>\<And>x. bounded (range (\<lambda>n. blinfun_apply (f n) x))\<close>
    by (metis (no_types, lifting) boundedI rangeE)
  hence \<open>bounded (range f)\<close>
    by (simp add: banach_steinhaus)
  hence  \<open>\<exists>M. \<forall>n. norm (f n) \<le> M\<close>
    by (simp add: bounded_iff)
  thus ?thesis 
    unfolding f_def using cblinfun_to_blinfun_norm by metis
qed

theorem riesz_frechet_representation_cblinfun_existence_uniq:
  fixes f::\<open>('a::chilbert_space, complex) cblinfun\<close>
  shows \<open>\<exists>!t. \<forall>x.  f *\<^sub>V x = \<langle>t, x\<rangle>\<close>
  apply transfer apply auto
   apply (simp add: riesz_frechet_representation_existence)
proof-
  fix y t::'a and f:: \<open>'a \<Rightarrow> complex\<close>
  assume \<open>cbounded_linear f\<close> and \<open>\<forall>x. \<langle>y, x\<rangle> = \<langle>t, x\<rangle>\<close> 
    and \<open>\<forall>x. f x = \<langle>t, x\<rangle>\<close>
  have  \<open>\<langle>y - t, x\<rangle> = 0\<close> 
    for x
  proof-
    have \<open>\<langle>y - t, x\<rangle> = \<langle>y, x\<rangle> - \<langle>t, x\<rangle>\<close>
      by (simp add: cinner_diff_left)
    also have \<open>\<langle>y, x\<rangle> - \<langle>t, x\<rangle> = 0\<close>
      using  \<open>\<forall>x. \<langle>y, x\<rangle> = \<langle>t, x\<rangle>\<close> 
      by simp
    finally show ?thesis 
      by blast
  qed
  hence \<open>y - t = 0\<close>
    using cinner_eq_zero_iff by blast    
  thus \<open>t = y\<close>
    by auto
qed

theorem riesz_frechet_representation_cblinfun_norm:
  includes notation_norm
  fixes f::\<open>('a::chilbert_space, complex) cblinfun\<close>
  assumes \<open>\<And> x.  f *\<^sub>V x = \<langle>t, x\<rangle>\<close>
  shows \<open>\<parallel>f\<parallel> = \<parallel>t\<parallel>\<close>
  using assms apply transfer
proof-
  fix f::\<open>'a \<Rightarrow> complex\<close> and t
  assume \<open>cbounded_linear f\<close> and \<open>\<And>x. f x = \<langle>t, x\<rangle>\<close> 
  from  \<open>\<And>x. f x = \<langle>t, x\<rangle>\<close> 
  have \<open>(norm (f x)) / (norm x) \<le> norm t\<close>
    for x
  proof(cases \<open>norm x = 0\<close>)
    case True
    thus ?thesis by simp
  next
    case False
    have \<open>norm (f x) = norm (\<langle>t, x\<rangle>)\<close>
      using \<open>\<And>x. f x = \<langle>t, x\<rangle>\<close> by simp
    also have \<open>norm \<langle>t, x\<rangle> \<le> norm t * norm x\<close>
      by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)
    finally have \<open>norm (f x) \<le> norm t * norm x\<close>
      by blast
    thus ?thesis
      by (metis False linordered_field_class.divide_right_mono nonzero_mult_div_cancel_right norm_ge_zero) 
  qed
  moreover have \<open>(norm (f t)) / (norm t) = norm t\<close>
  proof(cases \<open>norm t = 0\<close>)
    case True
    thus ?thesis
      by simp 
  next
    case False
    have \<open>f t = \<langle>t, t\<rangle>\<close>
      using \<open>\<And>x. f x = \<langle>t, x\<rangle>\<close> by blast
    also have \<open>\<dots> = norm \<langle>t, t\<rangle>\<close>
      using complex_of_real_cmod by auto
    also have \<open>\<dots> = (norm t)^2\<close>
      by (simp add: power2_norm_eq_cinner)
    also have \<open>\<dots> = (norm t)*(norm t)\<close>
      by (simp add: power2_eq_square)
    finally have \<open>f t = (norm t)*(norm t)\<close>
      by blast
    thus ?thesis
      by (metis False \<open>\<langle>t, t\<rangle> = complex_of_real (cmod \<langle>t, t\<rangle>)\<close> \<open>f t = \<langle>t, t\<rangle>\<close> nonzero_eq_divide_eq of_real_eq_iff) 
  qed
  ultimately have \<open>Sup {(norm (f x)) / (norm x)| x. True} = norm t\<close>
    by (smt cSup_eq_maximum mem_Collect_eq)    
  moreover have \<open>Sup {(norm (f x)) / (norm x)| x. True} = (SUP x. (norm (f x)) / (norm x))\<close>
    by (simp add: full_SetCompr_eq)    
  ultimately show \<open>onorm f = norm t\<close>
    by (simp add: onorm_def) 
qed


lemma clinear_finite_sum:
  assumes "finite S"
  shows "F *\<^sub>V (\<Sum>a\<in>S. r a *\<^sub>C a) = (\<Sum>a\<in>S. r a *\<^sub>C (F *\<^sub>V a))"
proof-
  have "\<And>S. card S = n \<Longrightarrow> finite S \<Longrightarrow> F *\<^sub>V (\<Sum>a\<in>S. r a *\<^sub>C a) = (\<Sum>a\<in>S. r a *\<^sub>C (F *\<^sub>V a))" for n
  proof(induction n)
    case 0
    fix S::"'a set"
    assume q1:"card S = 0" and q2:"finite S"
    hence "S = {}" by auto
    thus "F *\<^sub>V (\<Sum>a\<in>S. r a *\<^sub>C a) = (\<Sum>a\<in>S. r a *\<^sub>C (F *\<^sub>V a))"
      by (metis (no_types, lifting) applyOp_scaleC2 complex_vector.scale_zero_left sum.empty)
  next
    case (Suc n)
    fix S::"'a set"
    assume q1:"card S = Suc n" and q2:"finite S"
    hence "\<exists>R s. S = insert s R \<and> s \<notin> R"
      by (metis card_le_Suc_iff le_Suc_eq)
    then obtain R s where a1:"S = insert s R" and a2:"s \<notin> R"
      by blast
    have cardR: "card R = n"
      using a1 a2 q1 q2 by auto
    hence q3:"F *\<^sub>V (\<Sum>a\<in>R. r a *\<^sub>C a) = (\<Sum>a\<in>R. r a *\<^sub>C (F *\<^sub>V a))"
      using Suc.IH a1 q2 by auto
    have "F *\<^sub>V (\<Sum>a\<in>S. r a *\<^sub>C a) = F *\<^sub>V ((r s *\<^sub>C s) + (\<Sum>a\<in>R. r a *\<^sub>C a))"
      using a1 a2 q2 by auto    
    also have "\<dots> = F *\<^sub>V (r s *\<^sub>C s) + F *\<^sub>V (\<Sum>a\<in>R. r a *\<^sub>C a)"
      apply transfer unfolding cbounded_linear_def  clinear_def Vector_Spaces.linear_def
        module_hom_def module_hom_axioms_def by auto
    also have "\<dots> = F *\<^sub>V (r s *\<^sub>C s) + (\<Sum>a\<in>R.  r a *\<^sub>C (F *\<^sub>V a))"
      using q3 by auto
    also have "\<dots> = r s *\<^sub>C (F *\<^sub>V s) + (\<Sum>a\<in>R.  r a *\<^sub>C (F *\<^sub>V a))"
      by simp
    also have "\<dots> = (\<Sum>a\<in>S.  r a *\<^sub>C (F *\<^sub>V a))"
      using a1 a2 q2 by auto
    finally show "F *\<^sub>V (\<Sum>a\<in>S. r a *\<^sub>C a) = (\<Sum>a\<in>S. r a *\<^sub>C (F *\<^sub>V a))"
      by blast
  qed
  thus ?thesis using assms by auto 
qed


lemma vector_to_cblinfun_times_vec[simp]:
  includes cblinfun_notation
  shows "vector_to_cblinfun \<phi> *\<^sub>V \<gamma> = one_dim_to_complex \<gamma> *\<^sub>C \<phi>"
  apply transfer by (rule refl)

lemma vector_to_cblinfun_adj_times_vec[simp]:
  includes cblinfun_notation
  shows "vector_to_cblinfun \<psi>* *\<^sub>V \<phi> = of_complex (cinner \<psi> \<phi>)"
proof -
  have "one_dim_to_complex (vector_to_cblinfun \<psi>* *\<^sub>V \<phi> :: 'a) = cinner 1 (vector_to_cblinfun \<psi>* *\<^sub>V \<phi> :: 'a)"
    by (simp add: one_dim_to_complex_def)
  also have "\<dots> = cinner (vector_to_cblinfun \<psi> *\<^sub>V (1::'a)) \<phi>"
    by (metis adjoint_I adjoint_twice)
  also have "\<dots> = \<langle>\<psi>, \<phi>\<rangle>"
    by simp
  finally have "one_dim_to_complex (vector_to_cblinfun \<psi>* *\<^sub>V \<phi> :: 'a) = \<langle>\<psi>, \<phi>\<rangle>" by -
  thus ?thesis
    by (metis one_dim_to_complex_inverse)
qed

lemma cblinfun_ext: 
  includes cblinfun_notation
  assumes "\<And>x::'a::chilbert_space. A *\<^sub>V x = B *\<^sub>V x"
  shows "A = B" 
  using assms apply transfer by auto

lemma eigenspace_memberE:
  includes cblinfun_notation
  assumes "x \<in> space_as_set (eigenspace e A)"
  shows "A *\<^sub>V x = e *\<^sub>C x"
  using assms unfolding eigenspace_def apply transfer by auto

lemma kernel_memberE:
  includes cblinfun_notation
  assumes "x \<in> space_as_set (kernel A)"
  shows "A *\<^sub>V x = 0"
  using assms apply transfer by auto

lemma eigenspace_memberI:
  includes cblinfun_notation
  assumes "A *\<^sub>V x = e *\<^sub>C x"
  shows "x \<in> space_as_set (eigenspace e A)"
  using assms unfolding eigenspace_def apply transfer by auto

lemma kernel_memberI:
  includes cblinfun_notation
  assumes "A *\<^sub>V x = 0"
  shows "x \<in> space_as_set (kernel A)"
  using assms apply transfer by auto

lemma applyOpSpace_Span: 
  includes cblinfun_notation
  shows "A *\<^sub>S Span G = Span ((*\<^sub>V) A ` G)"
  apply transfer
proof
  show "closure (A ` closure (complex_vector.span (G::'b set))) \<subseteq> closure (complex_vector.span (A ` G::'a set))"
    if "cbounded_linear (A::'b \<Rightarrow> 'a)"
    for A :: "'b \<Rightarrow> 'a"
      and G :: "'b set"
  proof-
    have isContA: \<open>isCont A r\<close>
      for r
      using that
      by (simp add: bounded_linear_continuous)
    have \<open>A ` closure (complex_vector.span (G::'b set)) \<subseteq> closure (complex_vector.span (A ` G::'a set))\<close>
    proof
      show "x \<in> closure (complex_vector.span (A ` G))"
        if "x \<in> A ` closure (complex_vector.span G)"
        for x :: 'a
      proof-
        have \<open>\<exists> y. x = A y \<and> y \<in> closure (complex_vector.span G)\<close>
          using that by auto
        then obtain y where \<open>x = A y\<close> and \<open>y \<in> closure (complex_vector.span G)\<close>
          by blast
        from  \<open>y \<in> closure (complex_vector.span G)\<close>
        have \<open>\<exists> t. t \<longlonglongrightarrow> y \<and> (\<forall> n. t n \<in> complex_vector.span G)\<close>
          using closure_sequential by blast
        then obtain t where \<open>t \<longlonglongrightarrow> y\<close> and \<open>\<forall> n. t n \<in> complex_vector.span G\<close>
          by blast
        from \<open>\<forall> n. t n \<in> complex_vector.span G\<close>
        have \<open>\<forall> n. A (t n) \<in> complex_vector.span (A ` G)\<close>
          using \<open>cbounded_linear A\<close>
            complex_vector.linear_span_image 
          unfolding cbounded_linear_def
          by blast          
        moreover have \<open>(\<lambda> n. A (t n)) \<longlonglongrightarrow> A y\<close>
          using isContA  \<open>t \<longlonglongrightarrow> y\<close>
          by (simp add: isCont_tendsto_compose) 
        ultimately show ?thesis 
          using \<open>x = A y\<close>
          by (meson closure_sequential)
      qed
    qed
    thus ?thesis
      by (metis closure_closure closure_mono)       
  qed
  show "closure (complex_vector.span (A ` (G::'b set)::'a set)) \<subseteq> closure (A ` closure (complex_vector.span G))"
    if "cbounded_linear (A::'b \<Rightarrow> 'a)"
    for A :: "'b \<Rightarrow> 'a"
      and G :: "'b set"
    using that
    by (simp add: cbounded_linear.is_clinear closure_mono closure_subset complex_vector.linear_span_image image_mono) 
qed

lemma span_ortho_span:
  assumes "\<And>s t. s\<in>S \<Longrightarrow> t\<in>T \<Longrightarrow> is_orthogonal s t"
  shows "Span S \<le> - (Span T)"
  using assms apply transfer
proof
  show "x \<in> orthogonal_complement (closure (complex_vector.span T))"
    if "\<And>s t. \<lbrakk>s \<in> S; t \<in> T\<rbrakk> \<Longrightarrow> is_orthogonal s t"
      and "x \<in> closure (complex_vector.span S)"
    for S :: "'a set"
      and T :: "'a set"
      and x :: 'a
  proof-
    have discrete: \<open>x \<in> complex_vector.span S \<Longrightarrow> y \<in> complex_vector.span T \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
      for x y
    proof-
      assume \<open>x \<in> complex_vector.span S\<close> and \<open>y \<in> complex_vector.span T\<close>
      have \<open>\<exists> T' r\<^sub>T. finite T' \<and>  T' \<subseteq> T \<and> y = (\<Sum>a\<in>T'. r\<^sub>T a *\<^sub>C a)\<close>
        using complex_vector.span_explicit  \<open>y \<in> complex_vector.span T\<close>
        by (smt mem_Collect_eq)
      then obtain T' r\<^sub>T where \<open>finite T'\<close> and \<open>T' \<subseteq> T\<close> and \<open>y = (\<Sum>a\<in>T'. r\<^sub>T a *\<^sub>C a)\<close>
        by blast
      have \<open>\<exists> S' r\<^sub>S. finite S' \<and>  S' \<subseteq> S \<and> x = (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a)\<close>
        using complex_vector.span_explicit  \<open>x \<in> complex_vector.span S\<close>
        by (smt mem_Collect_eq)
      then obtain S' r\<^sub>S where \<open>finite S'\<close> and \<open>S' \<subseteq> S\<close> and \<open>x = (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a)\<close>
        by blast
      have \<open>\<langle> x, y \<rangle> = \<langle> (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a), (\<Sum>b\<in>T'. r\<^sub>T b *\<^sub>C b) \<rangle>\<close>
        by (simp add: \<open>x = (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a)\<close> \<open>y = (\<Sum>a\<in>T'. r\<^sub>T a *\<^sub>C a)\<close>)
      also have \<open>\<dots> = (\<Sum>a\<in>S'. \<langle> r\<^sub>S a *\<^sub>C a, (\<Sum>b\<in>T'. r\<^sub>T b *\<^sub>C b) \<rangle>)\<close>
        using cinner_sum_left by blast
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. \<langle> r\<^sub>S a *\<^sub>C a,  r\<^sub>T b *\<^sub>C b \<rangle>))\<close>
        by (simp add: cinner_sum_right)
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. (cnj (r\<^sub>S a)) * \<langle> a,  r\<^sub>T b *\<^sub>C b \<rangle>))\<close>
      proof -
        have "(\<Sum>a\<in>S'. \<Sum>aa\<in>T'. \<langle>r\<^sub>S a *\<^sub>C a, r\<^sub>T aa *\<^sub>C aa\<rangle>) = (\<Sum>a\<in>S'. \<Sum>aa\<in>T'. cnj (r\<^sub>S a) * \<langle>a, r\<^sub>T aa *\<^sub>C aa\<rangle>) \<or> (\<forall>a. (\<Sum>aa\<in>T'. \<langle>r\<^sub>S a *\<^sub>C a, r\<^sub>T aa *\<^sub>C aa\<rangle>) = (\<Sum>aa\<in>T'. cnj (r\<^sub>S a) * \<langle>a, r\<^sub>T aa *\<^sub>C aa\<rangle>))"
          by (meson cinner_scaleC_left)
        thus ?thesis
          by presburger
      qed
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. (cnj (r\<^sub>S a)) * ((r\<^sub>T b) * \<langle> a, b \<rangle>)))\<close>
      proof-
        have \<open>\<langle> a, r\<^sub>T b *\<^sub>C b \<rangle> =  r\<^sub>T b * \<langle> a, b \<rangle>\<close>
          for a b
          by simp
        thus ?thesis by simp
      qed
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. (cnj (r\<^sub>S a)) * ((r\<^sub>T b) * 0)))\<close>
      proof-
        have \<open>a \<in> S' \<Longrightarrow> b \<in> T' \<Longrightarrow> \<langle> a, b \<rangle> = 0\<close>
          for a b
        proof-
          assume \<open>a \<in> S'\<close> and \<open>b \<in> T'\<close>
          have \<open>a \<in> S\<close>
            using \<open>S' \<subseteq> S\<close> \<open>a \<in> S'\<close> by blast            
          moreover have \<open>b \<in> T\<close>
            using \<open>T' \<subseteq> T\<close> \<open>b \<in> T'\<close> by blast
          ultimately show ?thesis
            using is_orthogonal_def that(1) by auto 
        qed
        thus ?thesis by simp
      qed
      finally show \<open>\<langle> x, y \<rangle> = 0\<close> by simp
    qed
    have \<open>y \<in> complex_vector.span T \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
      for y
    proof-
      assume \<open>y \<in> complex_vector.span T\<close>
      have \<open>\<exists> t. t \<longlonglongrightarrow> x \<and> (\<forall> n. t n \<in> complex_vector.span S)\<close>
        using closure_sequential
        by (metis that(2))  
      then obtain t where \<open>t \<longlonglongrightarrow> x\<close> and \<open>\<forall> n. t n \<in> complex_vector.span S\<close>
        by blast
      from  \<open>\<forall> n. t n \<in> complex_vector.span S\<close>
      have \<open>\<langle> t n, y \<rangle> = 0\<close>
        for n
        using discrete \<open>y \<in> complex_vector.span T\<close>
        by blast
      moreover have \<open>(\<lambda> n. \<langle> t n, y \<rangle>) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
        using  \<open>t \<longlonglongrightarrow> x\<close> cinner_continuous_left
        by (simp add: cinner_continuous_left)
      ultimately have \<open>(\<lambda> n. 0) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
        by simp
      thus ?thesis
        by (simp add: LIMSEQ_const_iff) 
    qed
    hence \<open>y \<in> closure (complex_vector.span T) \<Longrightarrow> \<langle> x, y \<rangle> = 0\<close>
      for y
    proof-
      assume \<open>y \<in> closure (complex_vector.span T)\<close>
      hence \<open>\<exists> t. t \<longlonglongrightarrow> y \<and> (\<forall> n. t n \<in> complex_vector.span T)\<close>
        using closure_sequential by blast
      then obtain t where \<open>t \<longlonglongrightarrow> y\<close> and \<open>\<forall> n. t n \<in> complex_vector.span T\<close>
        by blast
      from  \<open>\<forall> n. t n \<in> complex_vector.span T\<close>
      have \<open>\<langle> x, t n \<rangle> = 0\<close>
        for n
        by (simp add: \<open>\<And>y. y \<in> complex_vector.span T \<Longrightarrow> \<langle>x, y\<rangle> = 0\<close>)
      moreover have \<open>(\<lambda> n. \<langle> x, t n \<rangle>) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
        using  \<open>t \<longlonglongrightarrow> y\<close>
        by (simp add: cinner_continuous_right)        
      ultimately have \<open>(\<lambda> n. 0) \<longlonglongrightarrow> \<langle> x, y \<rangle>\<close>
        by simp
      thus ?thesis
        by (simp add: LIMSEQ_const_iff) 
    qed
    thus ?thesis
      using orthogonal_complement_I2 by blast 
  qed
qed

definition "positive_op A = (\<exists>B::('a::chilbert_space,'a) cblinfun. A = B* o\<^sub>C\<^sub>L B)"

lemma timesOp0[simp]: "0 o\<^sub>C\<^sub>L A = 0"
  apply transfer by simp

lemma timesOp0'[simp]: "A o\<^sub>C\<^sub>L 0 = 0"
  apply transfer apply auto
  by (metis cbounded_linear_def mult_zero_left norm_le_zero_iff norm_zero)

lemma positive_idOp[simp]: "positive_op idOp"
  unfolding positive_op_def apply (rule exI[of _ idOp]) by simp

lemma positive_0[simp]: "positive_op 0"
  unfolding positive_op_def apply (rule exI[of _ 0]) by auto

abbreviation "loewner_leq A B == (positive_op (B-A))"


lemma norm_mult_ineq_cblinfun:
  fixes A B :: "(_,_) cblinfun"
  shows "norm (A o\<^sub>C\<^sub>L B) \<le> norm A * norm B"
  apply transfer
  by (simp add: cbounded_linear.bounded_linear onorm_compose)

hide_fact closed_finite_dim'

lemma span_finite_dim:
  fixes T::\<open>'a::complex_inner set\<close>
  assumes \<open>finite T\<close>
  shows \<open>closure (complex_vector.span T)  = complex_vector.span T\<close>
  using closed_finite_dim
  by (simp add: closed_finite_dim assms)


lemma Ortho_expansion_finite:
  fixes T::\<open>'a::complex_inner set\<close>
  assumes \<open>is_onb T\<close> and \<open>finite T\<close>
  shows \<open>x = (\<Sum>t\<in>T. \<langle> t, x \<rangle> *\<^sub>C t)\<close>
proof-
  have \<open>closure (complex_vector.span T) = UNIV\<close>
    using \<open>is_onb T\<close>
    unfolding is_onb_def is_ob_def is_basis_def
    by blast
  moreover have \<open>closure (complex_vector.span T)  = complex_vector.span T\<close>
    using \<open>finite T\<close> span_finite_dim by blast
  ultimately have \<open>complex_vector.span T = (UNIV::'a set)\<close>
    by blast
  have \<open>{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> T} =
    {\<Sum>a\<in>T. r a *\<^sub>C a |r. True}\<close>
    using span_explicit_finite[where A = "T"] \<open>finite T\<close>
    by blast
  hence \<open>\<exists> r. x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
  proof -
    have f1: "\<forall>A. {a. \<exists>Aa f. (a::'a) = (\<Sum>a\<in>Aa. f a *\<^sub>C a) \<and> finite Aa \<and> Aa \<subseteq> A} = Complex_Vector_Spaces.span A"
      by (simp add: complex_vector.span_explicit)      
    have f2: "\<forall>a. (\<exists>f. a = (\<Sum>a\<in>T. f a *\<^sub>C a)) \<or> (\<forall>A. (\<forall>f. a \<noteq> (\<Sum>a\<in>A. f a *\<^sub>C a)) \<or> infinite A \<or> \<not> A \<subseteq> T)"
      using \<open>{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> T} = {\<Sum>a\<in>T. r a *\<^sub>C a |r. True}\<close> by auto
    have f3: "\<forall>A a. (\<exists>Aa f. (a::'a) = (\<Sum>a\<in>Aa. f a *\<^sub>C a) \<and> finite Aa \<and> Aa \<subseteq> A) \<or> a \<notin> Complex_Vector_Spaces.span A"
      using f1 by blast
    have "Complex_Vector_Spaces.span T = UNIV"
      by (metis (full_types, lifting) Complex_Vector_Spaces.span_raw_def \<open>complex_vector.span T = UNIV\<close>)
    then show ?thesis
      using f3 f2 by blast
  qed 
  then obtain r where \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    by blast
  have \<open>a \<in> T \<Longrightarrow> r a = \<langle>a, x\<rangle>\<close>
    for a
  proof-
    assume \<open>a \<in> T\<close>
    have \<open>\<langle>a, x\<rangle> = \<langle>a, (\<Sum> t\<in>T. r t *\<^sub>C t)\<rangle>\<close>
      using \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum> t\<in>T. \<langle>a, r t *\<^sub>C t\<rangle>)\<close>
      using cinner_sum_right by blast
    also have \<open>\<dots> = (\<Sum> t\<in>T. r t * \<langle>a, t\<rangle>)\<close>
    proof-
      have \<open>\<langle>a, r t *\<^sub>C t\<rangle> = r t * \<langle>a, t\<rangle>\<close>
        for t
        by simp
      thus ?thesis by simp
    qed
    also have \<open>\<dots> = r a * \<langle>a, a\<rangle> + (\<Sum> t\<in>T-{a}. r t * \<langle>a, t\<rangle>)\<close>
      using \<open>a \<in> T\<close>
      by (meson assms(2) sum.remove)
    also have \<open>\<dots> = r a * \<langle>a, a\<rangle>\<close>
    proof-
      have \<open>(\<Sum> t\<in>T-{a}. r t * \<langle>a, t\<rangle>) = 0\<close>
      proof-
        have \<open>t\<in>T-{a} \<Longrightarrow> r t * \<langle>a, t\<rangle> = 0\<close>
          for t
        proof-
          assume \<open>t \<in> T-{a}\<close>
          hence \<open>t \<in> T\<close>
            by blast
          have \<open>a \<noteq> t\<close>
            using  \<open>t \<in> T-{a}\<close>
            by auto
          hence \<open>\<langle>a, t\<rangle> = 0\<close>
            using \<open>a \<in> T\<close> \<open>t \<in> T\<close> \<open>is_onb T\<close>
            unfolding is_onb_def is_ob_def is_ortho_set_def
            by blast
          thus ?thesis by simp
        qed
        show ?thesis
          by (simp add: \<open>\<And>t. t \<in> T - {a} \<Longrightarrow> r t * \<langle>a, t\<rangle> = 0\<close>) 
      qed
      thus ?thesis by simp
    qed
    also have \<open>\<dots> = r a\<close>
    proof-
      have \<open>a \<in> sphere 0 1\<close>
        using \<open>a\<in>T\<close> \<open>is_onb T\<close>
        unfolding is_onb_def
        by blast
      hence \<open>norm a = 1\<close>
        unfolding sphere_def by auto
      moreover have \<open>norm a = sqrt (norm \<langle>a, a\<rangle>)\<close>
        using norm_eq_sqrt_cinner by auto        
      ultimately have \<open>sqrt (norm \<langle>a, a\<rangle>) = 1\<close>
        by simp
      hence \<open>norm \<langle>a, a\<rangle> = 1\<close>
        using real_sqrt_eq_1_iff by blast
      moreover have \<open>\<langle>a, a\<rangle> \<in> \<real>\<close>
        by (simp add: cinner_real)        
      moreover have \<open>\<langle>a, a\<rangle> \<ge> 0\<close>
        by simp        
      ultimately have \<open>\<langle>a, a\<rangle> = 1\<close>
        by (metis \<open>0 \<le> \<langle>a, a\<rangle>\<close> \<open>cmod \<langle>a, a\<rangle> = 1\<close> complex_of_real_cmod of_real_1)
      thus ?thesis by simp
    qed
    finally show ?thesis by auto
  qed
  thus ?thesis 
    using \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    by fastforce 
qed



instance onb_enum \<subseteq> chilbert_space
proof
  show "convergent X"
    if "Cauchy X"
    for X :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>finite (set canonical_basis)\<close>
      by simp
    have \<open>is_onb (set (canonical_basis::'a list))\<close>
      unfolding is_onb_def is_ob_def apply auto
        apply (simp add: is_orthonormal)
       apply (simp add: is_basis_set)
      by (simp add: is_normal)
    have \<open>Cauchy (\<lambda> n. \<langle> t, X n \<rangle>)\<close>
      for t
    proof-
      define f where \<open>f x = \<langle> t, x \<rangle>\<close> for x
      have \<open>cbounded_linear f\<close>
        unfolding f_def
        by (simp add: cbounded_linear_cinner_right)
      hence \<open>Cauchy (\<lambda> n. f (X n))\<close>
        using that
        by (simp add: cbounded_linear_Cauchy) 
      thus ?thesis
        unfolding f_def by blast
    qed
    hence \<open>convergent (\<lambda> n. \<langle> t, X n \<rangle>)\<close>
      for t
      by (simp add: Cauchy_convergent_iff)      
    hence \<open>\<forall> t\<in>set canonical_basis. \<exists> L. (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L\<close>
      by (simp add: convergentD)
    hence \<open>\<exists> L. \<forall> t\<in>set canonical_basis. (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
      by metis
    then obtain L where \<open>\<And> t. t\<in>set canonical_basis \<Longrightarrow> (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
      by blast
    define l where \<open>l = (\<Sum>t\<in>set canonical_basis. L t *\<^sub>C t)\<close>
    have \<open>X n = (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t)\<close>
      for n
      using Ortho_expansion_finite[where T = "set canonical_basis" and x = "X n"]
        \<open>is_onb (set canonical_basis)\<close>  \<open>finite (set canonical_basis)\<close> 
      by auto
        (*     using Ortho_expansion_finite[where T = "set canonical_basis" and x = "X n"]
        \<open>is_onb (set canonical_basis)\<close>  \<open>finite (set canonical_basis)\<close> *)
    moreover have  \<open>(\<lambda> n. (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t)) \<longlonglongrightarrow> l\<close>
    proof-
      have \<open>t\<in>set canonical_basis \<Longrightarrow> (\<lambda> n. \<langle> t, X n \<rangle> *\<^sub>C t) \<longlonglongrightarrow> L t *\<^sub>C t\<close> 
        for t
      proof-
        assume \<open>t\<in>set canonical_basis\<close>
        hence \<open>(\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
          using  \<open>\<And> t. t\<in>set canonical_basis \<Longrightarrow> (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
          by blast
        hence \<open>(\<lambda> n. \<langle> t, X n \<rangle> *\<^sub>C t) \<longlonglongrightarrow> L t *\<^sub>C t\<close>
        proof-
          define f where \<open>f x = x *\<^sub>C t\<close> for x
          have \<open>isCont f r\<close>
            for r
            unfolding f_def
            by (simp add: cbounded_linear_scaleC_left bounded_linear_continuous)
          hence \<open>(\<lambda> n. f \<langle> t, X n \<rangle>) \<longlonglongrightarrow> f (L t)\<close>
            using \<open>(\<lambda>n. \<langle>t, X n\<rangle>) \<longlonglongrightarrow> L t\<close> isCont_tendsto_compose by blast
          thus ?thesis unfolding f_def
            by simp
        qed
        thus ?thesis by blast
      qed
      hence \<open>(\<lambda> n. (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t)) \<longlonglongrightarrow>  (\<Sum>t\<in>set canonical_basis. L t *\<^sub>C t)\<close>
        using \<open>finite (set canonical_basis)\<close>
          tendsto_finite_sum[where T = "set canonical_basis" and X = "\<lambda> t. \<lambda> n. \<langle>t, X n\<rangle> *\<^sub>C t"
            and L = "\<lambda> t. L t *\<^sub>C t"]
        by auto
      thus ?thesis
        using l_def by blast 
    qed
    ultimately have \<open>X \<longlonglongrightarrow> l\<close>
      by simp
    thus ?thesis 
      unfolding convergent_def by blast
  qed
qed

lemma vector_to_cblinfun_adj_times_vector_to_cblinfun[simp]:
  includes cblinfun_notation
  shows "vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi> = cinner \<psi> \<phi> *\<^sub>C idOp"
proof -
  have "one_dim_to_complex ((vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>) *\<^sub>V \<gamma>) = one_dim_to_complex ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>V \<gamma>)" 
    for \<gamma> :: "'c::one_dim"
    by (simp add: times_applyOp)
  hence "((vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>) *\<^sub>V \<gamma>) = ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>V \<gamma>)" 
    for \<gamma> :: "'c::one_dim"
    using one_dim_to_complex_inverse by metis
  thus ?thesis
    using  cblinfun_ext[where A = "vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>"
        and B = "\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp"]
    by auto
qed

lemma finite_span_complete_aux:
  fixes b :: "'b::real_normed_vector" and B :: "'b set"
    and  rep :: "'basis::finite \<Rightarrow> 'b" and abs :: "'b \<Rightarrow> 'basis"
  assumes t: "type_definition rep abs B"
  assumes "finite B" and "b\<in>B" and "independent B"
  shows "\<exists>D>0. \<forall>\<psi>. norm (real_vector.representation B \<psi> b) \<le> norm \<psi> * D"
    and "complete (real_vector.span B)"

  text \<open>This auxiliary lemma shows more or less the same as \<open>finite_span_representation_cblinfun\<close>
     \<open>finite_span_complete\<close> below (see there for an intuition about the mathematical 
     content of the lemmas. However, there is one difference: We additionally assume here
     that there is a bijection rep/abs between a finite type \<^typ>\<open>'basis\<close> and the set $B$.
     This is needed to be able to use results about euclidean spaces that are formulated w.r.t.
     the type class \<^class>\<open>finite\<close>

     Since we anyway assume that $B$ is finite, this added assumption does not make the lemma
     weaker. However, we cannot derive the existence of \<^typ>\<open>'basis\<close> inside the proof
     (HOL does not support such reasoning). Therefore we have the type \<^typ>\<open>'basis\<close> as
     an explicit assumption and remove it using @{attribute internalize_sort} after the proof.\<close>

proof -
  define repr  where "repr = real_vector.representation B"
  define repr' where "repr' \<psi> = Abs_euclidean_space (repr \<psi> o rep)" for \<psi>
  define comb  where "comb l = (\<Sum>b\<in>B. l b *\<^sub>R b)" for l
  define comb' where "comb' l = comb (Rep_euclidean_space l o abs)" for l

  have comb_cong: "comb x = comb y" if "\<And>z. z\<in>B \<Longrightarrow> x z = y z" for x y
    unfolding comb_def using that by auto
  have comb_repr[simp]: "comb (repr \<psi>) = \<psi>" if "\<psi> \<in> real_vector.span B" for \<psi>
    unfolding comb_def repr_def 
    apply (rule real_vector.sum_representation_eq)
    using assms that by auto
  have repr_comb[simp]: "repr (comb x) = (\<lambda>b. if b\<in>B then x b else 0)" for x
    unfolding repr_def comb_def
    apply (rule real_vector.representation_eqI)
    using \<open>independent B\<close> \<open>finite B\<close> apply (auto simp add: real_vector.span_base real_vector.span_scale real_vector.span_sum)
     apply meson
    by (smt DiffD1 DiffD2 mem_Collect_eq real_vector.scale_eq_0_iff subset_eq sum.mono_neutral_left) 
      (* > 1s *)
  have repr_bad[simp]: "repr \<psi> = (\<lambda>_. 0)" if "\<psi> \<notin> real_vector.span B" for \<psi>
    unfolding repr_def using that
    by (simp add: real_vector.representation_def)
  have [simp]: "repr' \<psi> = 0" if "\<psi> \<notin> real_vector.span B" for \<psi>
    unfolding repr'_def repr_bad[OF that]
    by (transfer fixing: rep, simp)
  have comb'_repr'[simp]: "comb' (repr' \<psi>) = \<psi>" if "\<psi> \<in> real_vector.span B" for \<psi>
  proof -
    have "comb' (repr' \<psi>) = comb ((repr \<psi> \<circ> rep) \<circ> abs)"
      unfolding comb'_def repr'_def
      by (subst Abs_euclidean_space_inverse; simp)
    also have "\<dots> = comb (repr \<psi>)"
      apply (rule comb_cong) unfolding o_def
      by (subst type_definition.Abs_inverse[OF t]; simp)
    also have "\<dots> = \<psi>"
      using that by simp
    finally show ?thesis by -
  qed
  have repr'_comb'[simp]: "repr' (comb' x) = x" for x
    unfolding comb'_def repr'_def o_def
    apply simp
    apply (subst type_definition.Rep_inverse[OF t])
    using type_definition.Rep[OF t] apply simp
    apply (subst Rep_euclidean_space_inverse)
    by simp
  have sphere: "compact (sphere 0 d :: 'basis euclidean_space set)" for d
    using compact_sphere by blast

  have "complete (UNIV :: 'basis euclidean_space set)"
    by (simp add: complete_UNIV)

  have blin_comb': "bounded_linear comb'"
    unfolding comb_def comb'_def apply (rule bounded_linearI')
     apply (transfer fixing: abs)
     apply (simp add: scaleR_add_left sum.distrib)
    apply (transfer fixing: abs)
    by (simp add: real_vector.scale_sum_right)

  then have "continuous_on X comb'" for X
    by (simp add: linear_continuous_on)

  then have "compact (comb' ` sphere 0 d)" for d
    using sphere
    apply (rule compact_continuous_image)
    by -

  then have compact_norm_comb': "compact (norm ` comb' ` sphere 0 1)"
    apply (rule compact_continuous_image[rotated])
    apply (rule continuous_on_norm)
    by auto

  have not0: "0 \<notin> norm ` comb' ` sphere 0 1"
  proof (rule ccontr, simp)
    assume "0 \<in> norm ` comb' ` sphere 0 1"
    then obtain x where nc0: "norm (comb' x) = 0" and x: "x \<in> sphere 0 1"
      by auto
    then have "comb' x = 0"
      by simp
    then have "repr' (comb' x) = 0"
      unfolding repr'_def o_def repr_def apply simp
      by (smt repr'_comb' blin_comb' dist_0_norm linear_simps(3) mem_sphere norm_zero x)
    then have "x = 0"
      by auto
    with x show False
      by simp
  qed
  have "\<exists>d>0. \<forall>x\<in>norm ` comb' ` sphere 0 1. d \<le> dist 0 x"
    apply (rule_tac separate_point_closed)
    using not0 compact_norm_comb'
     apply auto
    using compact_imp_closed by blast

  then obtain d where d: "x\<in>norm ` comb' ` sphere 0 1 \<Longrightarrow> d \<le> dist 0 x"  
    and "d > 0" for x
    by metis
  define D where "D = 1/d"
  then have "D > 0"
    using \<open>d>0\<close> unfolding D_def by auto
  from d have "x \<ge> d"  if "x\<in>norm ` comb' ` sphere 0 1" for x
    apply auto
    using that by fastforce
  then have *: "norm (comb' x) \<ge> d" if "norm x = 1" for x
    using that by auto
  have norm_comb': "norm (comb' x) \<ge> d * norm x" for x
    apply (cases "x=0")
     apply simp
    using *[of "(1/norm x) *\<^sub>R x"]
    unfolding linear_simps(5)[OF blin_comb']
    apply auto
    by (simp add: le_divide_eq)
  have *:  "norm (repr' \<psi>) \<le> norm \<psi> * D" for \<psi>
    apply (cases "\<psi> \<in> real_vector.span B")
    unfolding D_def
    using norm_comb'[of "repr' \<psi>"] \<open>d>0\<close>
    by (simp_all add: linordered_field_class.mult_imp_le_div_pos mult.commute)
  then have "norm (Rep_euclidean_space (repr' \<psi>) (abs b)) \<le> norm \<psi> * D" for \<psi>
  proof -
    have "(Rep_euclidean_space (repr' \<psi>) (abs b)) = repr' \<psi> \<bullet> euclidean_space_basis_vector (abs b)"
      apply (transfer fixing: abs b)
      apply auto by -
    also have "\<bar>\<dots>\<bar> \<le> norm (repr' \<psi>)"
      apply (rule Basis_le_norm)
      unfolding Basis_euclidean_space_def by simp
    also have "\<dots> \<le> norm \<psi> * D"
      using * by auto
    finally show ?thesis by simp
  qed
  then have "norm (repr \<psi> b) \<le> norm \<psi> * D" for \<psi>
    unfolding repr'_def apply (subst (asm) Abs_euclidean_space_inverse)
     apply auto
    unfolding type_definition.Abs_inverse[OF t \<open>b\<in>B\<close>] by simp
  then show "\<exists>D>0. \<forall>\<psi>. norm (repr \<psi> b) \<le> norm \<psi> * D"
    using \<open>D>0\<close> by auto

  have complete_comb': "complete (comb' ` UNIV)"
    using \<open>d>0\<close> apply (rule complete_isometric_image)
    using blin_comb' norm_comb' complete_UNIV by auto

  have range_comb': "comb' ` UNIV = real_vector.span B"
  proof (auto simp: image_def)
    show "comb' x \<in> real_vector.span B" for x
      by (metis comb'_def comb_cong comb_repr local.repr_def repr_bad repr_comb real_vector.representation_zero real_vector.span_zero)
  next
    fix \<psi> assume "\<psi> \<in> real_vector.span B"
    then obtain f where f: "comb f = \<psi>"
      apply atomize_elim
      unfolding real_vector.span_finite[OF \<open>finite B\<close>] comb_def
      by auto
    define f' where "f' b = (if b\<in>B then f b else 0)" for b :: 'b
    have f': "comb f' = \<psi>"
      unfolding f[symmetric]
      apply (rule comb_cong)
      unfolding f'_def by simp
    define x :: "'basis euclidean_space" where "x = Abs_euclidean_space (f' o rep)"
    have "\<psi> = comb' x"
      unfolding comb'_def x_def o_def
      apply (subst Abs_euclidean_space_inverse, simp)
      apply (subst comb_cong[of _ f'])
       apply (subst type_definition.Abs_inverse[OF t]; simp)
      using f' by simp
    then show "\<exists>x. \<psi> = comb' x"
      by auto
  qed

  from range_comb' complete_comb'
  show "complete (real_vector.span B)"
    by simp
qed

(* TODO: move to General_Results_Missing or similar *)
lemma complete_singleton: 
  shows "complete {s::'a::uniform_space}"
  unfolding complete_uniform
  apply auto
  by (meson dual_order.trans empty_subsetI insert_subset le_nhds le_principal principal_le_iff)

(* We do not need this theorem for our development but we get it almost for
   free as a side effect of the proof of finite_span_complete. *)
lemma finite_span_representation_cblinfun:  (* TODO: cblinfun \<rightarrow> bounded *)
  fixes B :: "'a::real_normed_vector set"
  assumes "finite B" "independent B"
  shows "\<exists>D>0. \<forall>\<psi> b. abs (real_vector.representation B \<psi> b) \<le> norm \<psi> * D"

  text \<open>
  Assume $B$ is a finite linear independent set of vectors (in a real normed vector space).
  Let $\<alpha>^\<psi>_b$ be the coefficients of $\<psi>$ expressed as a linear combination over $B$.
  Then $\<alpha>$ is is uniformly cblinfun (i.e., $\lvert\alpha^\<psi>_b \leq D \lVert\psi\rVert\psi for some $D$ independent of $\<psi>,b$).

  (This also holds when $b$ is not in the span of $B$ because of the way \<open>real_vector.representation\<close>
  is defined in this corner case.) \<close>

proof (cases "B\<noteq>{}")
  case True

(* The following generalizes finite_span_complete_aux to hold without the assumption
     that 'basis has type class finite *)
  define repr  where "repr = real_vector.representation B"
  {
    (* Step 1: Create a fake type definition by introducing a new type variable 'basis
               and then assuming the existence of the morphisms Rep/Abs to B
               This is then roughly equivalent to "typedef 'basis = B" *)
    (* The type variable 'basisT must not be the same as the one used in finite_span_complete_aux
       (I.e., we cannot call it 'basis) *)
    assume "\<exists>(Rep :: 'basisT\<Rightarrow>'a) Abs. type_definition Rep Abs B"
    then obtain rep :: "'basisT \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'basisT" where t: "type_definition rep abs B"
      by auto
        (* Step 2: We show that our fake typedef 'basisT could be instantiated as type class finite *)
    have basisT_finite: "class.finite TYPE('basisT)"
      apply intro_classes
      using \<open>finite B\<close> t
      by (metis (mono_tags, hide_lams) ex_new_if_finite finite_imageI image_eqI type_definition_def)
        (* Step 3: We take the finite_span_complete_aux and remove the requirement that 'basis::finite
               (instead, a precondition "class.finite TYPE('basisT)" is introduced) *)
    note finite_span_complete_aux(1)[internalize_sort "'basis::finite"]
      (* Step 4: We instantiate the premises *)
    note this[OF basisT_finite t]
  }
    (* Now we have the desired fact, except that it still assumes that B is isomorphic to some type 'basis
     together with the assumption that there are morphisms between 'basis and B. 'basis and that premise
     are removed using cancel_type_definition
  *)
  note this[cancel_type_definition, OF True \<open>finite B\<close> _ \<open>independent B\<close>]

  then have "\<exists>D. \<forall>\<psi>. D>0 \<and> norm (repr \<psi> b) \<le> norm \<psi> * D" if \<open>b\<in>B\<close> for b
    by (simp add: repr_def that True)
  then obtain D where D: "D b > 0 \<and> norm (repr \<psi> b) \<le> norm \<psi> * D b" if "b\<in>B" for b \<psi>
    apply atomize_elim apply (rule choice) by auto
  then have Dpos: "D b > 0" and Dbound: "norm (repr \<psi> b) \<le> norm \<psi> * D b" if "b\<in>B" for b \<psi>
    using that by auto
  define Dall where "Dall = Max (D`B)"
  have "Dall > 0"
    unfolding Dall_def using \<open>finite B\<close> \<open>B\<noteq>{}\<close> Dpos
    apply auto
    by (metis (mono_tags) Max_in True empty_is_image finite_imageI imageE)

  have "Dall \<ge> D b" if "b\<in>B" for b
    unfolding Dall_def using \<open>finite B\<close> that by auto
  with Dbound
  have "norm (repr \<psi> b) \<le> norm \<psi> * Dall" if "b\<in>B" for b \<psi>
    using that apply auto
    by (meson mult_left_mono norm_ge_zero order_trans)
  moreover have "norm (repr \<psi> b) \<le> norm \<psi> * Dall" if "b\<notin>B" for b \<psi>
    unfolding repr_def using real_vector.representation_ne_zero True
    by (metis calculation empty_subsetI less_le_trans local.repr_def norm_ge_zero norm_zero not_less subsetI subset_antisym)
  ultimately show "\<exists>D>0. \<forall>\<psi> b. abs (repr \<psi> b) \<le> norm \<psi> * D"
    using \<open>Dall > 0\<close> real_norm_def by metis
next
  case False
  then show ?thesis
    unfolding repr_def using real_vector.representation_ne_zero[of B]
    using nice_ordered_field_class.linordered_field_no_ub by fastforce
qed

lemma finite_span_complete:
  fixes A :: "'a::real_normed_vector set"
  assumes "finite A"
  shows "complete (real_vector.span A)"

  text \<open>The span of a finite set is complete.\<close>

proof (cases "A \<noteq> {} \<and> A \<noteq> {0}")
  case True
  obtain B where
    BT: "real_vector.span B = real_vector.span A"
    and "independent B"  
    and "finite B"
    by (smt assms empty_subsetI real_vector.independent_empty 
        real_vector.maximal_independent_subset_extend real_vector.span_eq rev_finite_subset 
        subset_trans)
  have "B\<noteq>{}"
    apply (rule ccontr, simp)
    using BT True
    by (metis real_vector.span_superset real_vector.span_empty subset_singletonD)

(* The following generalizes finite_span_complete_aux to hold without the assumption
     that 'basis has type class finite *)
  {
    (* The type variable 'basisT must not be the same as the one used in finite_span_complete_aux,
       otherwise "internalize_sort" below fails *)
    assume "\<exists>(Rep :: 'basisT\<Rightarrow>'a) Abs. type_definition Rep Abs B"
    then obtain rep :: "'basisT \<Rightarrow> 'a" and abs :: "'a \<Rightarrow> 'basisT" where t: "type_definition rep abs B"
      by auto
    have basisT_finite: "class.finite TYPE('basisT)"
      apply intro_classes
      using \<open>finite B\<close> t
      by (metis (mono_tags, hide_lams) ex_new_if_finite finite_imageI image_eqI type_definition_def)
    note finite_span_complete_aux(2)[internalize_sort "'basis::finite"]
    note this[OF basisT_finite t]
  }
  note this[cancel_type_definition, OF \<open>B\<noteq>{}\<close> \<open>finite B\<close> _ \<open>independent B\<close>]
  then have "complete (real_vector.span B)"
    using \<open>B\<noteq>{}\<close> by auto 
  then show "complete (real_vector.span A)"
    unfolding BT by simp
next
  case False
  then show ?thesis
    using complete_singleton by auto
qed

hide_fact finite_span_complete_aux

lemma finite_span_closed: 
  fixes B :: "'a::real_normed_vector set"
  assumes "finite B"
  shows "closed (real_vector.span B)"
  by (simp add: assms complete_imp_closed finite_span_complete)

lemma complex_real_span:
  "complex_vector.span B = real_vector.span (B \<union> scaleC \<i> ` B)"
proof auto
  let ?cspan = complex_vector.span
  let ?rspan = real_vector.span
  fix \<psi>
  assume cspan: "\<psi> \<in> ?cspan B"
  obtain B' r where "finite B'" and "B' \<subseteq> B" and \<psi>_explicit: "\<psi> = (\<Sum>b\<in>B'. r b *\<^sub>C b)"
    apply atomize_elim 
    using complex_vector.span_explicit[of B] cspan
    by auto
  define R where "R = B \<union> scaleC \<i> ` B"
  have "r b *\<^sub>C b = Re (r b) *\<^sub>R b + Im (r b) *\<^sub>R \<i> *\<^sub>C b" for b
    using complex_eq scaleC_add_left scaleC_scaleC scaleR_scaleC
    by (metis (no_types, lifting) ordered_field_class.sign_simps(46))
  then have "\<psi> = (\<Sum>(b,i)\<in>(B'\<times>UNIV). if i then Im (r b) *\<^sub>R (\<i> *\<^sub>C b) else Re (r b) *\<^sub>R b)"
    apply (subst sum.cartesian_product[symmetric])
    by (simp add: UNIV_bool \<psi>_explicit)
  also have "\<dots> \<in> ?rspan R"
    unfolding R_def
    apply (rule real_vector.span_sum)
    using \<open>B' \<subseteq> B\<close> by (auto simp add: real_vector.span_base real_vector.span_scale subset_iff) 
  finally show "\<psi> \<in> ?rspan R" by -
next
  let ?cspan = complex_vector.span
  let ?rspan = real_vector.span
  define R where "R = B \<union> scaleC \<i> ` B"
  fix \<psi>
  assume rspan: "\<psi> \<in> ?rspan R"
  then show "\<psi> \<in> ?cspan B"
    apply induction
     apply (rule real_vector.subspaceI, auto simp add: complex_vector.span_zero complex_vector.span_add_eq2 complex_vector.span_scale scaleR_scaleC)
    using R_def complex_vector.span_base complex_vector.span_scale by fastforce 
qed

(* NEW *)
lemma scaleC_complex_independent:
  assumes a1: "complex_independent B" and a2: "finite B" and a3: "c \<noteq> 0"
  shows "complex_independent ((*\<^sub>C) c ` B)"
proof-
  have "u y = 0"
    if "y\<in>S" and "(\<Sum>x\<in>S. u x *\<^sub>C x) = 0" and "finite S" and "S\<subseteq>(*\<^sub>C) c ` B"
    for u y S
  proof-
    define v where "v x = u (c *\<^sub>C x)" for x
    obtain S' where "S'\<subseteq>B" and "S = (*\<^sub>C) c ` S'"
      by (meson \<open>S \<subseteq> (*\<^sub>C) c ` B\<close> subset_imageE)
    have "finite S'"
      using \<open>S' \<subseteq> B\<close> a2 finite_subset by blast
    have "t \<in> (*\<^sub>C) (inverse c) ` S"
      if "t \<in> S'" for t
    proof-
      have "c *\<^sub>C t \<in> S"
        using \<open>S = (*\<^sub>C) c ` S'\<close> that by blast
      hence "(inverse c) *\<^sub>C (c *\<^sub>C t) \<in> (*\<^sub>C) (inverse c) ` S"
        by blast
      moreover have "(inverse c) *\<^sub>C (c *\<^sub>C t) = t"
        by (simp add: a3)
      ultimately show ?thesis by simp
    qed
    moreover have "t \<in> S'"
      if "t \<in> (*\<^sub>C) (inverse c) ` S" for t
    proof-
      obtain t' where "t = (inverse c) *\<^sub>C t'" and "t' \<in> S"
        using \<open>t \<in> (*\<^sub>C) (inverse c) ` S\<close> by auto
      have "c *\<^sub>C t = c *\<^sub>C ((inverse c) *\<^sub>C t')"
        using \<open>t = (inverse c) *\<^sub>C t'\<close> by simp
      also have "\<dots> = (c * (inverse c)) *\<^sub>C t'"
        by simp
      also have "\<dots> = t'"
        by (simp add: a3)
      finally have "c *\<^sub>C t = t'".
      thus ?thesis using \<open>t' \<in> S\<close>
        using \<open>S = (*\<^sub>C) c ` S'\<close> a3 complex_vector.scale_left_imp_eq by blast 
    qed
    ultimately have "S' = (*\<^sub>C) (inverse c) ` S"
      by blast 
    hence "inverse c *\<^sub>C y \<in> S'"
      using that(1) by blast 
    have "0 = (\<Sum>x\<in>(*\<^sub>C) c ` S'. u x *\<^sub>C x)"
      using \<open>S = (*\<^sub>C) c ` S'\<close> that(2) by auto
    also have "\<dots> = (\<Sum>x\<in>S'. v x *\<^sub>C (c *\<^sub>C x))"
    proof-
      have "inj (((*\<^sub>C) c)::'a \<Rightarrow> _)"
        using a3 Complex_Vector_Spaces.complex_vector.injective_scale[where c = c]
        by blast
      thus ?thesis
        unfolding v_def
        using  Groups_Big.comm_monoid_add_class.sum.reindex[where h = "((*\<^sub>C) c)" and A = S' 
            and g = "\<lambda>x. u x *\<^sub>C x"] subset_inj_on by auto     
    qed
    also have "\<dots> = c *\<^sub>C (\<Sum>x\<in>S'. v x *\<^sub>C x)"
      by (metis (mono_tags, lifting) complex_vector.scale_left_commute scaleC_right.sum sum.cong)
    finally have "0 = c *\<^sub>C (\<Sum>x\<in>S'. v x *\<^sub>C x)".
    hence "(\<Sum>x\<in>S'. v x *\<^sub>C x) = 0"
      using a3 by auto
    hence "v (inverse c *\<^sub>C y) = 0"
      using \<open>inverse c *\<^sub>C y \<in> S'\<close> \<open>finite S'\<close> \<open>S' \<subseteq> B\<close> a1
      using complex_vector.independentD by blast
    thus "u y = 0"
      unfolding v_def
      by (simp add: a3) 
  qed
  thus ?thesis
    by (simp add: complex_vector.independent_explicit_finite_subsets)
qed



lemma complex_real_independent:
  assumes a1: "complex_vector.independent B" and a2: "finite B"
  shows "real_vector.independent (B \<union> (*\<^sub>C) \<i> ` B)"
proof- (* NEW *)
  have a1': "complex_independent B"
    using a1
    by (simp add: Complex_Vector_Spaces.dependent_raw_def)
  have "f y = 0"
    if b0: "y\<in>B \<union> (*\<^sub>C) \<i> ` B" and
      b1: "(\<Sum>x\<in>B \<union> (*\<^sub>C) \<i> ` B. f x *\<^sub>R x) = 0"  
    for y and f::"'a \<Rightarrow> real"
  proof-
    define g where "g x = f x + \<i> *\<^sub>C f (\<i> *\<^sub>C x)" for x
    define h where "h x = g (-\<i> *\<^sub>C x)" for x
    have "finite ((*\<^sub>C) \<i> ` B)"
      using a2
      by simp      
    moreover have "B \<inter> (*\<^sub>C) \<i> ` B = {}"
    proof(rule classical)
      assume "\<not>(B \<inter> (*\<^sub>C) \<i> ` B = {})"
      hence "B \<inter> (*\<^sub>C) \<i> ` B \<noteq> {}"
        by blast
      then obtain x where u1: "x\<in>B \<inter> (*\<^sub>C) \<i> ` B"
        by blast
      then obtain b where u2: "x = b" and u3: "b\<in>B"
        by blast
      then obtain b' where u2': "x = \<i> *\<^sub>C b'" and u3': "b'\<in>B"
        using u1
        by blast
      have g1: "b = \<i> *\<^sub>C b'"
        using u2 and u2' by simp
      hence "b \<in> complex_vector.span {b'}"
        using complex_vector.span_base by force
      hence "b = b'"
        by (smt a1' complex_vector.dependent_def complex_vector.span_base complex_vector.span_scale 
            insert_Diff insert_iff u2 u2' u3 u3') 
      thus ?thesis using g1
        by (metis a1' complex_i_not_one complex_vector.representation_basis 
            complex_vector.representation_zero complex_vector.scale_cancel_right scaleC_one u3' 
            zero_neq_one) 
    qed
    ultimately have "(\<Sum>x\<in>B \<union> (*\<^sub>C) \<i> ` B. f x *\<^sub>R x) = (\<Sum>x\<in>B. f x *\<^sub>R x) + (\<Sum>x\<in>(*\<^sub>C) \<i> ` B. f x *\<^sub>R x)"
      by (simp add: a2 sum.union_disjoint)
    also have "\<dots> = (\<Sum>x\<in>B. f x *\<^sub>R x) + (\<Sum>x\<in>B. f (\<i> *\<^sub>C x) *\<^sub>R (\<i> *\<^sub>C x))"
      sorry
    also have "\<dots> = (\<Sum>x\<in>B. f x *\<^sub>R x) + (\<Sum>x\<in>B. (\<i> *\<^sub>C f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      sorry
    also have "\<dots> = (\<Sum>x\<in>B. f x *\<^sub>C x + (\<i> *\<^sub>C f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      sorry
    also have "\<dots> = (\<Sum>x\<in>B. (f x + (\<i> *\<^sub>C f (\<i> *\<^sub>C x))) *\<^sub>C x)"
      sorry
    also have "\<dots> = (\<Sum>x\<in>B. (g x) *\<^sub>C x)"
      sorry
    finally have "(\<Sum>x\<in>B \<union> (*\<^sub>C) \<i> ` B. f x *\<^sub>R x) = (\<Sum>x\<in>B. (g x) *\<^sub>C x)".
    hence "(\<Sum>x\<in>B. (g x) *\<^sub>C x) = 0"
      using b1 by auto
    hence "(\<Sum>x\<in>(*\<^sub>C) \<i> ` B. (g (-\<i> *\<^sub>C x)) *\<^sub>C (-\<i> *\<^sub>C x)) = 0"
      sorry
    hence k1: "(\<Sum>x\<in>(*\<^sub>C) \<i> ` B. h x *\<^sub>C x) = 0"
      sorry
    show ?thesis 
    proof(cases "y \<in> B")
      case True
      hence "g y = 0"
        using a1' a2 independent_explicit_finite_subsets[where A = B]
          \<open>(\<Sum>x\<in>B. g x *\<^sub>C x) = 0\<close> by blast
      thus "f y = 0"
        unfolding g_def
        using complex_eq_cancel_iff2
        by simp
    next
      case False
      hence "y \<in> (*\<^sub>C) \<i> ` B"
        using b0 by blast
      moreover have "finite ((*\<^sub>C) \<i> ` B)"
        by (simp add: \<open>finite ((*\<^sub>C) \<i> ` B)\<close>)        
      moreover have "complex_independent ((*\<^sub>C) \<i> ` B)"
        by (simp add: a1' a2 scaleC_complex_independent)        
      ultimately have "h y = 0"        
        using k1 independent_explicit_finite_subsets[where A = "(*\<^sub>C) \<i> ` B"]
        by blast        
      thus "f y = 0"
        unfolding h_def
        using complex_minus g_def by auto
    qed
  qed
  thus ?thesis
    using Real_Vector_Spaces.dependent_raw_def Un_infinite finite_UnI finite_imageI 
      real_vector.dependent_explicit real_vector.dependent_finite subset_eq sum.infinite
      Un_upper1 rev_finite_subset
    by smt (* > 1s *)
qed

lemma complex_real_vector_representation:
  assumes a1: "complex_vector.independent B" and a2: "b \<in> B" and a3: "finite B"
  shows "complex_vector.representation B \<psi> b
       = complex_of_real (real_vector.representation (B \<union> scaleC \<i> ` B) \<psi> b)
  + \<i> *\<^sub>C complex_of_real (real_vector.representation (B \<union> scaleC \<i> ` B) \<psi> (scaleC \<i> b))"
proof (cases "\<psi> \<in> complex_vector.span B") (* NEW *)
  case True
  define B' where "B' = (B \<union> scaleC \<i> ` B)"
  define r  where "r b = real_vector.representation B' \<psi> b" for b
  define r' where "r' b = real_vector.representation B' \<psi> (\<i> *\<^sub>C b)" for b
  define f  where "f b = r b + \<i> *\<^sub>C r' b" for b

  have k1: "real_vector.independent B'"
    unfolding B'_def using a1 complex_real_independent
    by (simp add: complex_real_independent a3)

  moreover have k2: "finite B'"
    unfolding B'_def
    by (simp add: a3)
  ultimately have "(\<Sum>b\<in>B'. r b *\<^sub>R b) = \<psi>"
    unfolding r_def B'_def
    by (metis (no_types, lifting) Real_Vector_Spaces.dependent_raw_def True complex_real_span
        real_vector.sum_representation_eq sum.cong sup.cobounded2 sup_left_idem)
  hence "(\<Sum>b\<in>B'. r b *\<^sub>C b) = \<psi>"
    by (metis (mono_tags, lifting) scaleR_scaleC sum.cong)
  have "\<i> * (-\<i>) = 1"
    by simp
  have "(\<Sum>b\<in>(*\<^sub>C) (-\<i>) ` B'. r (\<i> *\<^sub>C b) *\<^sub>C (\<i> *\<^sub>C b)) = (\<Sum>b\<in>B'. r b *\<^sub>C b)"
    sorry
  have "(\<Sum>b\<in>(*\<^sub>C) (-\<i>) ` B'. r (\<i> *\<^sub>C b) *\<^sub>C (\<i> *\<^sub>C b)) = \<psi>"
    sorry

  have "(\<Sum>b\<in>B'. r' b *\<^sub>R b) = \<psi>"
    unfolding r_def B'_def
    using Real_Vector_Spaces.dependent_raw_def True complex_real_span
      real_vector.sum_representation_eq sum.cong sup.cobounded2 sup_left_idem
    sorry

  have "f b *\<^sub>C b = r b *\<^sub>C b + (\<i> *\<^sub>C (r' b)) *\<^sub>C b"
    for b
    unfolding f_def
    by (simp add: scaleC_left.add)    
  hence "(\<Sum>b\<in>B. f b *\<^sub>C b) = (\<Sum>b\<in>B. r b *\<^sub>C b + (\<i> *\<^sub>C (r' b)) *\<^sub>C b)"
    by simp
  also have "\<dots> = (\<Sum>b\<in>B. r b *\<^sub>C b) + (\<Sum>b\<in>B. (\<i> *\<^sub>C (r' b)) *\<^sub>C b)"
    by (simp add: sum.distrib)
  also have "\<dots> = (\<Sum>b\<in>B. r b *\<^sub>R b) + \<i> *\<^sub>C (\<Sum>b\<in>B. (r' b) *\<^sub>R b)"
  proof-
    have "\<i> *\<^sub>C (\<Sum>b\<in>B. (r' b) *\<^sub>R b) = \<i> *\<^sub>C (\<Sum>b\<in>B. (r' b) *\<^sub>C b)"
      by (simp add: scaleR_scaleC)
    also have "\<dots> = (\<Sum>b\<in>B. \<i> *\<^sub>C ((r' b) *\<^sub>C b))"
      using scaleC_right.sum by blast      
    finally have "\<i> *\<^sub>C (\<Sum>b\<in>B. (r' b) *\<^sub>R b) = (\<Sum>b\<in>B. (\<i> *\<^sub>C (r' b)) *\<^sub>C b)" by simp
    moreover have "(\<Sum>b\<in>B. r b *\<^sub>R b) = (\<Sum>b\<in>B. r b *\<^sub>C b)"
      by (metis scaleR_scaleC)      
    ultimately show ?thesis by simp
  qed
  finally have "(\<Sum>b\<in>B. f b *\<^sub>C b) = (\<Sum>b\<in>B. r b *\<^sub>R b) + \<i> *\<^sub>C (\<Sum>b\<in>B. r' b *\<^sub>R b)".
  have w1: "(\<Sum>b\<in>B. f b *\<^sub>C b) = \<psi>"
    sorry
  have "\<psi> \<in> Complex_Vector_Spaces.span B"
    by (simp add: True)     
  moreover have w2: "b \<in> B"
    if r1: "f b \<noteq> 0"
    for b
    sorry
  moreover have "finite {b. f b \<noteq> 0}"
    by (metis (mono_tags, lifting) a3 calculation(2) finite_subset mem_Collect_eq subsetI)    
  moreover have "(\<Sum>b | f b \<noteq> 0. f b *\<^sub>C b) = \<psi>"
  proof-
    have q1: "\<not>(f b \<noteq> 0 \<and> b \<notin> B)"
      using w2 by blast      
    have "(\<Sum>b | f b \<noteq> 0. f b *\<^sub>C b) = (\<Sum>b | (f b \<noteq> 0 \<and> b \<in> B)\<or>(f b \<noteq> 0 \<and> b \<notin> B). f b *\<^sub>C b)"
      by meson
    also have "\<dots> = (\<Sum>b | f b \<noteq> 0 \<and> b \<in> B. f b *\<^sub>C b)+(\<Sum>b | f b \<noteq> 0 \<and> b \<notin> B. f b *\<^sub>C b)"
      by (smt Collect_cong add.right_neutral mem_Collect_eq sum.not_neutral_contains_not_neutral w2)
    also have "\<dots> = (\<Sum>b | f b \<noteq> 0 \<and> b \<in> B. f b *\<^sub>C b)"
      using sum_not_0 w2 by auto        
    also have "\<dots> = (\<Sum>b | b \<in> B. f b *\<^sub>C b)"
    proof-
      have "(\<Sum>b | f b = 0 \<and> b \<in> B. f b *\<^sub>C b) = 0"
        by simp
      moreover have "(\<Sum>b | b \<in> B. f b *\<^sub>C b) = (\<Sum>b | f b = 0 \<and> b \<in> B. f b *\<^sub>C b)
                                             + (\<Sum>b | f b \<noteq> 0 \<and> b \<in> B. f b *\<^sub>C b)"
      proof-
        have "B = {b|b. f b = 0 \<and> b \<in> B} \<union> {b|b. f b \<noteq> 0 \<and> b \<in> B}"
          by blast
        moreover have "{b|b. f b = 0 \<and> b \<in> B} \<inter> {b|b. f b \<noteq> 0 \<and> b \<in> B} = {}"
          by blast
        moreover have "finite {b|b. f b = 0 \<and> b \<in> B}"
          using a3 by simp
        moreover have "finite {b|b. f b \<noteq> 0 \<and> b \<in> B}"
          using a3 by simp          
        ultimately show ?thesis 
          using Groups_Big.comm_monoid_add_class.sum.union_disjoint[where 
              A = "{b |b. f b = 0 \<and> b \<in> B}" and B = "{b |b. f b \<noteq> 0 \<and> b \<in> B}"
              and g = "\<lambda>b. f b *\<^sub>C b"] by simp
      qed
      ultimately show ?thesis by simp
    qed
    also have "\<dots> = \<psi>"
      by (simp add: w1)
    finally show ?thesis .
  qed
  ultimately have "complex_vector.representation B \<psi> = f"
    using Complex_Vector_Spaces.complex_vector.representation_eqI[where basis = B and v = \<psi> 
        and f = f] by (smt Complex_Vector_Spaces.dependent_raw_def a1)
  thus ?thesis unfolding f_def r_def r'_def
    by (simp add: B'_def) 
next
  case False
  have b2: "\<psi> \<notin> real_vector.span (B \<union> scaleC \<i> ` B)"
    using False complex_real_span by auto    
  have "\<psi> \<notin> complex_vector.span B"
    using False by blast
  have "complex_vector.representation B \<psi> b = 0"
    unfolding complex_vector.representation_def
    using Complex_Vector_Spaces.dependent_raw_def False a1
    by simp
  moreover have "real_vector.representation (B \<union> scaleC \<i> ` B) \<psi> b = 0"
    unfolding real_vector.representation_def
    by (simp add: b2)
  moreover have "real_vector.representation (B \<union> scaleC \<i> ` B) \<psi> (scaleC \<i> b) = 0"
    unfolding real_vector.representation_def
    by (simp add: b2)
  ultimately show ?thesis by simp
qed


lemma finite_complex_span_representation_bounded:
  fixes B :: "'a::complex_normed_vector set"
  assumes a1: "finite B" and a2: "complex_vector.independent B"
  shows "\<exists>D>0. \<forall>\<psi> b. norm (complex_vector.representation B \<psi> b) \<le> norm \<psi> * D"
proof -
  define B' where "B' = (B \<union> scaleC \<i> ` B)"
  have independent_B': "real_vector.independent B'"
    using complex_real_independent B'_def \<open>complex_vector.independent B\<close>
    by (simp add: complex_real_independent a1) 
  have "finite B'"
    unfolding B'_def using \<open>finite B\<close> by simp
  obtain D' where "D' > 0" and D': "norm (real_vector.representation B' \<psi> b) \<le> norm \<psi> * D'" for \<psi> b
    apply atomize_elim
    using independent_B' \<open>finite B'\<close>
    by (simp add: Real_Vector_Spaces.dependent_raw_def finite_span_representation_cblinfun)
  define D where "D = 2*D'" 
  from \<open>D' > 0\<close> have \<open>D > 0\<close>
    unfolding D_def by simp
  have "norm (complex_vector.representation B \<psi> b) \<le> norm \<psi> * D" for \<psi> b
  proof (cases "b\<in>B")
    case True
    have "norm (complex_vector.representation B \<psi> b)
        = norm (complex_of_real (real_vector.representation B' \<psi> b)
            + \<i> *\<^sub>C complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      apply (subst complex_real_vector_representation)
      using \<open>complex_vector.independent B\<close> True B'_def a1 by auto
    also have "\<dots> \<le> norm (complex_of_real (real_vector.representation B' \<psi> b))
             + norm (\<i> *\<^sub>C complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      using norm_triangle_ineq by blast
    also have "\<dots> = norm (complex_of_real (real_vector.representation B' \<psi> b))
             + norm (complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      sorry
    also have "\<dots> = norm (real_vector.representation B' \<psi> b)
             + norm (real_vector.representation B' \<psi> (\<i> *\<^sub>C b))"
      sorry
    also have "\<dots> \<le> norm \<psi> * D' + norm \<psi> * D'"
      by (rule add_mono; rule D')
    also have "\<dots> \<le> norm \<psi> * D"
      unfolding D_def by linarith
    finally show ?thesis
      by auto
  next
    case False
    show ?thesis
      sorry
  qed
  with \<open>D > 0\<close>
  show ?thesis
    by auto
qed

lemma finite_complex_span_complete: 
  fixes B :: "'a::complex_normed_vector set"
  assumes "finite B"
  shows "complete (complex_vector.span B)"
  apply (subst complex_real_span)
  apply (rule finite_span_complete)
  using assms by auto



lemma cblinfun_operator_S_zero_uniq_span:
  fixes S::\<open>'a::chilbert_space set\<close>
  assumes a1: "x \<in> complex_vector.span S"
    and a2: "complex_vector.independent S"
    and a4: "\<And>s. s\<in>S \<Longrightarrow> F *\<^sub>V s = 0"
  shows \<open>F *\<^sub>V x = 0\<close>
proof-
  have "F x = 0"
  proof-
    have "\<exists>t r. finite t \<and> t \<subseteq> S \<and>  x = (\<Sum>a\<in>t. r a *\<^sub>C a)"
      using complex_vector.span_explicit a1 by (smt mem_Collect_eq)
    then obtain t r where b1: "finite t" and b2: "t \<subseteq> S" and b3: "x = (\<Sum>a\<in>t. r a *\<^sub>C a)"
      by blast
    have  "F x = (\<Sum>a\<in>t. r a *\<^sub>C (F a))"
      using b3
      by (smt \<open>\<And>thesis. (\<And>t r. \<lbrakk>finite t; t \<subseteq> S; x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> a4 b2 clinear_finite_sum complex_vector.scale_eq_0_iff in_mono sum.neutral)
    thus ?thesis using a4 b2
      by (simp add: subset_eq) 
  qed
  thus ?thesis by (simp add: cblinfun_ext) 
qed

lemma cblinfun_operator_S_uniq_span:
  fixes S::\<open>'a::chilbert_space set\<close>
  assumes a1: "x \<in> complex_vector.span S"
    and a2: "complex_vector.independent S"
    and a4: "\<And>s. s\<in>S \<Longrightarrow> F *\<^sub>V s = G *\<^sub>V s"
  shows \<open>F *\<^sub>V x = G *\<^sub>V x\<close>
proof-
  define H where "H = F - G"
  have "\<And>s. s\<in>S \<Longrightarrow> H *\<^sub>V s = 0"
    unfolding H_def
    by (simp add: a4 minus_cblinfun.rep_eq)
  hence "H x = 0"
    using a1 a2 cblinfun_operator_S_zero_uniq_span by auto
  thus ?thesis unfolding H_def
    by (metis eq_iff_diff_eq_0 minus_cblinfun.rep_eq)
qed

lemma cblinfun_operator_basis_zero_uniq:
  fixes basis::\<open>'a::chilbert_space set\<close>
  assumes a1: "complex_vector.span basis = UNIV"
    and a2: "complex_vector.independent basis"
    and a4: "\<And>s. s\<in>basis \<Longrightarrow> cblinfun_apply F s = 0"
  shows \<open>F = 0\<close>
  using cblinfun_operator_S_zero_uniq_span
  by (metis UNIV_I a1 a2 a4 applyOp0 cblinfun_ext)

(*
lemma cblinfun_operator_finite_dim':
  fixes  F::"'a::chilbert_space \<Rightarrow> 'b::chilbert_space" and S basis::"'a set"
  assumes b4:"clinear F" 
    and b9: "is_ob basis"
    and b3:"finite basis"
    and b5: "S \<subseteq> basis"  
    and b6: "\<And>w. w \<in> complex_vector.span (basis - S) \<Longrightarrow> F w = 0"
    and b7: "card S = n"     
  shows "cbounded_linear F"
  using assms
proof(induction n arbitrary: S F)
  case 0
  hence S_empty: "S = {}"
    using card_eq_0_iff finite_subset
    by fastforce
  hence "complex_vector.span S = {0}"
    by simp
  have "F s = 0" for s
  proof-
    have "s \<in> complex_vector.span basis"
      using b9 unfolding is_ob_def is_basis_def
      by (simp add: b3 span_finite_dim) 
    moreover have "basis - S = basis"
      using S_empty by blast
    ultimately have "s \<in> complex_vector.span (basis-S)"
      by simp
    thus ?thesis by (smt "0.prems"(5))
  qed
  thus ?case by simp
next
  case (Suc n)
  have "\<exists> s S'. S = insert s S' \<and> s \<notin> S'"
    by (metis Suc.prems(6) card_Suc_eq) 

  then obtain s S' where s1: "S = insert s S'" and s2: "s \<notin> S'"
    by blast
  have r1: "S' \<subseteq> basis"
    using s1 Suc.prems(4) by auto 
  have r2: "card S' = n"
    using Suc.prems(5)  b3 rev_finite_subset s1 s2
     Suc.prems(6) r1 by fastforce 

  have s0: "s \<noteq> 0"
  proof-
    have "s \<in> S"
      using s1 by auto
    hence "s \<in> basis"
      using Suc.prems(4) by blast
    thus ?thesis
      using b9 is_ob_nonzero by blast      
  qed
  hence snorm0: "norm s \<noteq> 0"
    by simp
  define f where "f x = F (projection (complex_vector.span {s}) x)" for x
  have f1: "cbounded_linear f"
  proof-
    have "closed_subspace (complex_vector.span {s})"
      unfolding closed_subspace_def apply auto
      by (simp add: closed_finite_dim)
    hence "cbounded_linear ( projection (complex_vector.span {s}) )"
      by (smt projectionPropertiesA)
    hence "clinear ( projection (Complex_Vector_Spaces.span {s}) )"
      by (smt cbounded_linear.is_clinear)
    hence "clinear f"
      using Suc.prems(4)
        Complex_Vector_Spaces.linear_compose
        [where g = F and f = "\<lambda>x. projection (complex_vector.span {s}) x"]
      unfolding f_def comp_def by (smt Suc.prems(1)) 
    moreover have "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
    proof-
      define K where "K = norm (F s) / norm s"
      have xonedim: "x\<in>complex_vector.span {s} \<Longrightarrow> norm (F x) \<le> norm x * K" for x
      proof-
        assume "x\<in>complex_vector.span {s}"
        hence "\<exists>r. x = r *\<^sub>C s"
          using complex_vector.span_breakdown by fastforce
        then obtain r where "x = r *\<^sub>C s"
          by blast
        hence "norm (F x) = norm (F (r *\<^sub>C s))"
          by simp
        also have "\<dots> = norm (r *\<^sub>C (F s))"
        proof-
          have "F (r *\<^sub>C s) = r *\<^sub>C (F s)"
            using complex_vector.linear_scale
            by (simp add: complex_vector.linear_scale Suc.prems(1))
          thus ?thesis by simp
        qed
        also have "\<dots> = norm r * norm s * K"
          unfolding K_def snorm0
          using snorm0 by auto
        also have "\<dots> = norm (r *\<^sub>C s) * K"
          by simp
        also have "\<dots> = norm x * K"
          by (simp add: \<open>x = r *\<^sub>C s\<close>)
        finally show ?thesis by auto
      qed
      have "norm (f x) \<le> norm x * K" for x
      proof-
        have proj_leq: "norm (projection (complex_vector.span {s}) x) \<le> norm x"
          by (smt \<open>closed_subspace (Complex_Vector_Spaces.span {s})\<close> projectionPropertiesB) 
        have "norm (f x) = norm (F (projection (complex_vector.span {s}) x))"
          unfolding f_def by blast
        also have "\<dots> \<le> norm (projection (complex_vector.span {s}) x) * K"
          using xonedim by (smt \<open>closed_subspace (Complex_Vector_Spaces.span {s})\<close> projection_intro2)
        also have "\<dots> \<le> (norm x) * K"
          using proj_leq
          by (metis K_def linordered_field_class.divide_nonneg_nonneg mult_right_mono norm_ge_zero)
        finally show ?thesis by blast
      qed
      thus ?thesis by blast
    qed
    ultimately show ?thesis
      unfolding cbounded_linear_def by blast
  qed
  have cs1: "closed_subspace (Complex_Vector_Spaces.span {s})"
    unfolding closed_subspace_def apply auto
    by (simp add: closed_finite_dim)
  define F' where "F' w = F w - f w" for w
  have r4: "clinear F'"
    unfolding F'_def cbounded_linear_def 
    using cbounded_linear.is_clinear complex_vector.linear_compose_sub f1
    by (simp add: cbounded_linear.is_clinear complex_vector.linear_compose_sub Suc.prems(1)) 
  hence r3: "w \<in> complex_vector.span (basis - S') \<Longrightarrow> F' w = 0" for w 
  proof-
    assume "w \<in> complex_vector.span (basis - S')"
    moreover have "basis - S' = insert s (basis - S)"
      using  s1 s2 Suc.prems(4) by blast 
    ultimately have "w \<in> complex_vector.span (insert s (basis - S))"
      by simp
    hence "\<exists>k. w - k *\<^sub>C s \<in> complex_vector.span (basis - S)"
      by (smt complex_vector.span_breakdown_eq)
    then obtain k where k_def: "w - k *\<^sub>C s \<in> complex_vector.span (basis - S)"
      by blast
    hence "F (w - k *\<^sub>C s) = 0"
      by (simp add: Suc.prems(5))
    hence "F w - F (k *\<^sub>C s) = 0"
      using  complex_vector.linear_diff Suc.prems(1) by fastforce 
    moreover have "F (k *\<^sub>C s) = f w"
    proof-
      have "closed_subspace (Complex_Vector_Spaces.span (basis - S))"
        unfolding closed_subspace_def apply auto
        by (simp add: b3 closed_finite_dim)
      have "x \<in> (Complex_Vector_Spaces.span (basis - S)) \<Longrightarrow> 
            x \<in> orthogonal_complement (Complex_Vector_Spaces.span {s})" for x
      proof-
        assume "x \<in> (Complex_Vector_Spaces.span (basis - S))"
        have "\<exists>t r. finite t \<and> t \<subseteq> basis - S \<and> x = (\<Sum>a\<in>t. r a *\<^sub>C a)"
          using complex_vector.span_explicit 
          by (smt \<open>x \<in> Complex_Vector_Spaces.span (basis - S)\<close> mem_Collect_eq)
        then obtain t r where t1: "finite t" and t2: "t \<subseteq> basis - S" and t3: "x = (\<Sum>a\<in>t. r a *\<^sub>C a)"
          by blast
        have t4: "q \<in> Complex_Vector_Spaces.span {s} \<Longrightarrow> a \<in> t \<Longrightarrow> \<langle>q, a\<rangle> = 0" for a q
        proof-
          assume v1: "q \<in> Complex_Vector_Spaces.span {s}" and v2: "a \<in> t"
          from v1 have "\<exists>h. q = h *\<^sub>C s"
            using complex_vector.span_breakdown_eq by force
          then obtain h where h_def: "q = h *\<^sub>C s" 
            by blast
          have "\<langle>q, a\<rangle> = \<langle>h *\<^sub>C s, a\<rangle>"
            unfolding h_def by blast
          also have "\<dots> = (cnj h) * \<langle>s, a\<rangle>"
            by simp
          also have "\<dots> = 0"
          proof-
            have "a \<in> basis - S"
              using t2 v2 by auto
            hence "\<langle>s, a\<rangle> = 0"
              using s1 assms(2) Suc.prems(4) unfolding is_ob_def is_ortho_set_def by auto  
            thus ?thesis by simp
          qed
          finally show ?thesis by blast
        qed
        hence "q \<in> Complex_Vector_Spaces.span {s} \<Longrightarrow> \<langle>q, x\<rangle> = 0" for q
        proof-
          assume "q \<in> Complex_Vector_Spaces.span {s}"
          have "\<langle>q, (\<Sum>a\<in>t. r a *\<^sub>C a)\<rangle> = (\<Sum>a\<in>t. r a * \<langle>q, a\<rangle>)"
            by (metis (mono_tags, lifting) cinner_scaleC_right cinner_sum_right sum.cong)
          also have "\<dots> = 0"
            using t4  by (smt \<open>q \<in> Complex_Vector_Spaces.span {s}\<close> 
                mult_zero_right sum.not_neutral_contains_not_neutral) 
          finally have "\<langle>q, (\<Sum>a\<in>t. r a *\<^sub>C a)\<rangle> = 0"
            by blast
          thus ?thesis using t3 by auto
        qed
        thus ?thesis using orthogonal_complement_I1 by metis
      qed
      hence "w - k *\<^sub>C s \<in> orthogonal_complement (Complex_Vector_Spaces.span {s})"
        using k_def by auto
      hence "projection (Complex_Vector_Spaces.span {s}) (w - k *\<^sub>C s) = 0"
        by (smt cs1 projectionPropertiesD vimage_singleton_eq) 
      hence "projection (Complex_Vector_Spaces.span {s}) w =
             projection (Complex_Vector_Spaces.span {s}) (k *\<^sub>C s)"
        using Complex_Vector_Spaces.span_mult
          \<open>w - k *\<^sub>C s \<in> orthogonal_complement (Complex_Vector_Spaces.span {s})\<close> 
          complex_vector.scale_eq_0_iff complex_vector.span_base complex_vector.span_zero cs1 
          projection_fixed_points projection_uniq singletonI by metis
      moreover have "projection (Complex_Vector_Spaces.span {s}) (k *\<^sub>C s) = k *\<^sub>C s"
        by (simp add: complex_vector.span_base complex_vector.span_scale cs1 projection_fixed_points)
      ultimately have "projection (Complex_Vector_Spaces.span {s}) w = k *\<^sub>C s"
        by simp
      thus ?thesis unfolding f_def by simp
    qed
    ultimately show ?thesis 
      unfolding F'_def by auto
  qed
  from r1 r2 r3 r4 assms
  have "cbounded_linear F'"
    using Suc.IH by blast
  moreover have "F = (\<lambda>x. F' x + f x)"
    using F'_def by auto
  ultimately show "cbounded_linear F"
    using f1 Complex_Vector_Spaces.cbounded_linear_add by blast
qed
*)

lemma cblinfun_operator_finite_dim_ortho:
  fixes  F::"'a::chilbert_space \<Rightarrow> 'b::chilbert_space" and basis::"'a set"
  assumes b4:"clinear F"  and b9:"is_ob basis" and b3:"finite basis"
  shows "cbounded_linear F"
proof-
  have cblinfun_operator_finite_dim': "cbounded_linear F"
    if b4:"clinear F" 
      and b9: "is_ob basis"
      and b3:"finite basis"
      and b5: "S \<subseteq> basis"  
      and b6: "\<And>w. w \<in> complex_vector.span (basis - S) \<Longrightarrow> F w = 0"
      and b7: "card S = n"
    for  F::"'a::chilbert_space \<Rightarrow> 'b::chilbert_space" and S basis::"'a set" and n::nat
    using that
  proof(induction n arbitrary: S F)
    case 0
    hence S_empty: "S = {}"
      using card_eq_0_iff finite_subset
      by fastforce
    hence "complex_vector.span S = {0}"
      by simp
    have "F s = 0" for s
    proof-
      have "s \<in> complex_vector.span basis"
        using b9 unfolding is_ob_def is_basis_def
        by (simp add: b3 span_finite_dim) 
      moreover have "basis - S = basis"
        using S_empty by blast
      ultimately have "s \<in> complex_vector.span (basis-S)"
        by simp
      thus ?thesis by (smt "0.prems"(5))
    qed
    thus ?case by simp
  next
    case (Suc n)
    have "\<exists> s S'. S = insert s S' \<and> s \<notin> S'"
      by (metis Suc.prems(6) card_Suc_eq) 

    then obtain s S' where s1: "S = insert s S'" and s2: "s \<notin> S'"
      by blast
    have r1: "S' \<subseteq> basis"
      using s1 Suc.prems(4) by auto 
    have r2: "card S' = n"
      using Suc.prems(5)  b3 rev_finite_subset s1 s2
        Suc.prems(6) r1 by fastforce 
    have s0: "s \<noteq> 0"
    proof-
      have "s \<in> S"
        using s1 by auto
      hence "s \<in> basis"
        using Suc.prems(4) by blast
      thus ?thesis
        using b9 is_ob_nonzero by blast      
    qed
    hence snorm0: "norm s \<noteq> 0"
      by simp
    define f where "f x = F (projection (complex_vector.span {s}) x)" for x
    have f1: "cbounded_linear f"
    proof-
      have "closed_subspace (complex_vector.span {s})"
        unfolding closed_subspace_def apply auto
        by (simp add: closed_finite_dim)
      hence "cbounded_linear ( projection (complex_vector.span {s}) )"
        by (smt projectionPropertiesA)
      hence "clinear ( projection (Complex_Vector_Spaces.span {s}) )"
        by (smt cbounded_linear.is_clinear)
      hence "clinear f"
        using Suc.prems(4)
          Complex_Vector_Spaces.linear_compose
          [where g = F and f = "\<lambda>x. projection (complex_vector.span {s}) x"]
        unfolding f_def comp_def by (smt Suc.prems(1)) 
      moreover have "\<exists>K. \<forall>x. norm (f x) \<le> norm x * K"
      proof-
        define K where "K = norm (F s) / norm s"
        have xonedim: "x\<in>complex_vector.span {s} \<Longrightarrow> norm (F x) \<le> norm x * K" for x
        proof-
          assume "x\<in>complex_vector.span {s}"
          hence "\<exists>r. x = r *\<^sub>C s"
            using complex_vector.span_breakdown by fastforce
          then obtain r where "x = r *\<^sub>C s"
            by blast
          hence "norm (F x) = norm (F (r *\<^sub>C s))"
            by simp
          also have "\<dots> = norm (r *\<^sub>C (F s))"
          proof-
            have "F (r *\<^sub>C s) = r *\<^sub>C (F s)"
              using complex_vector.linear_scale
              by (simp add: complex_vector.linear_scale Suc.prems(1))
            thus ?thesis by simp
          qed
          also have "\<dots> = norm r * norm s * K"
            unfolding K_def snorm0
            using snorm0 by auto
          also have "\<dots> = norm (r *\<^sub>C s) * K"
            by simp
          also have "\<dots> = norm x * K"
            by (simp add: \<open>x = r *\<^sub>C s\<close>)
          finally show ?thesis by auto
        qed
        have "norm (f x) \<le> norm x * K" for x
        proof-
          have proj_leq: "norm (projection (complex_vector.span {s}) x) \<le> norm x"
            by (smt \<open>closed_subspace (Complex_Vector_Spaces.span {s})\<close> projectionPropertiesB) 
          have "norm (f x) = norm (F (projection (complex_vector.span {s}) x))"
            unfolding f_def by blast
          also have "\<dots> \<le> norm (projection (complex_vector.span {s}) x) * K"
            using xonedim by (smt \<open>closed_subspace (Complex_Vector_Spaces.span {s})\<close> projection_intro2)
          also have "\<dots> \<le> (norm x) * K"
            using proj_leq
            by (metis K_def linordered_field_class.divide_nonneg_nonneg mult_right_mono norm_ge_zero)
          finally show ?thesis by blast
        qed
        thus ?thesis by blast
      qed
      ultimately show ?thesis
        unfolding cbounded_linear_def by blast
    qed
    have cs1: "closed_subspace (Complex_Vector_Spaces.span {s})"
      unfolding closed_subspace_def apply auto
      by (simp add: closed_finite_dim)
    define F' where "F' w = F w - f w" for w
    have r4: "clinear F'"
      unfolding F'_def cbounded_linear_def 
      using cbounded_linear.is_clinear complex_vector.linear_compose_sub f1
      by (simp add: cbounded_linear.is_clinear complex_vector.linear_compose_sub Suc.prems(1)) 
    hence r3: "w \<in> complex_vector.span (basis - S') \<Longrightarrow> F' w = 0" for w 
    proof-
      assume "w \<in> complex_vector.span (basis - S')"
      moreover have "basis - S' = insert s (basis - S)"
        using s1 s2 Suc.prems(4) by blast 
      ultimately have "w \<in> complex_vector.span (insert s (basis - S))"
        by simp
      hence "\<exists>k. w - k *\<^sub>C s \<in> complex_vector.span (basis - S)"
        by (smt complex_vector.span_breakdown_eq)
      then obtain k where k_def: "w - k *\<^sub>C s \<in> complex_vector.span (basis - S)"
        by blast
      hence "F (w - k *\<^sub>C s) = 0"
        by (simp add: Suc.prems(5))
      hence "F w - F (k *\<^sub>C s) = 0"
        using  complex_vector.linear_diff Suc.prems(1) by fastforce 
      moreover have "F (k *\<^sub>C s) = f w"
      proof-
        have "closed_subspace (Complex_Vector_Spaces.span (basis - S))"
          unfolding closed_subspace_def apply auto
          by (simp add: b3 closed_finite_dim)
        have "x \<in> (Complex_Vector_Spaces.span (basis - S)) \<Longrightarrow> 
            x \<in> orthogonal_complement (Complex_Vector_Spaces.span {s})" for x
        proof-
          assume "x \<in> (Complex_Vector_Spaces.span (basis - S))"
          have "\<exists>t r. finite t \<and> t \<subseteq> basis - S \<and> x = (\<Sum>a\<in>t. r a *\<^sub>C a)"
            using complex_vector.span_explicit 
            by (smt \<open>x \<in> Complex_Vector_Spaces.span (basis - S)\<close> mem_Collect_eq)
          then obtain t r where t1: "finite t" and t2: "t \<subseteq> basis - S" and t3: "x = (\<Sum>a\<in>t. r a *\<^sub>C a)"
            by blast
          have t4: "q \<in> Complex_Vector_Spaces.span {s} \<Longrightarrow> a \<in> t \<Longrightarrow> \<langle>q, a\<rangle> = 0" for a q
          proof-
            assume v1: "q \<in> Complex_Vector_Spaces.span {s}" and v2: "a \<in> t"
            from v1 have "\<exists>h. q = h *\<^sub>C s"
              using complex_vector.span_breakdown_eq by force
            then obtain h where h_def: "q = h *\<^sub>C s" 
              by blast
            have "\<langle>q, a\<rangle> = \<langle>h *\<^sub>C s, a\<rangle>"
              unfolding h_def by blast
            also have "\<dots> = (cnj h) * \<langle>s, a\<rangle>"
              by simp
            also have "\<dots> = 0"
            proof-
              have "a \<in> basis - S"
                using t2 v2 by auto
              hence "\<langle>s, a\<rangle> = 0"
                using s1 assms(2) Suc.prems(4) unfolding is_ob_def is_ortho_set_def
                by (metis Diff_iff b9 insertI1 insert_subset is_ob_def is_ortho_set_def) 
              thus ?thesis by simp
            qed
            finally show ?thesis by blast
          qed
          hence "q \<in> Complex_Vector_Spaces.span {s} \<Longrightarrow> \<langle>q, x\<rangle> = 0" for q
          proof-
            assume "q \<in> Complex_Vector_Spaces.span {s}"
            have "\<langle>q, (\<Sum>a\<in>t. r a *\<^sub>C a)\<rangle> = (\<Sum>a\<in>t. r a * \<langle>q, a\<rangle>)"
              by (metis (mono_tags, lifting) cinner_scaleC_right cinner_sum_right sum.cong)
            also have "\<dots> = 0"
              using t4  by (smt \<open>q \<in> Complex_Vector_Spaces.span {s}\<close> mult_not_zero sum_not_0)
            finally have "\<langle>q, (\<Sum>a\<in>t. r a *\<^sub>C a)\<rangle> = 0"
              by blast
            thus ?thesis using t3 by auto
          qed
          thus ?thesis using orthogonal_complement_I1 by metis
        qed
        hence "w - k *\<^sub>C s \<in> orthogonal_complement (Complex_Vector_Spaces.span {s})"
          using k_def by auto
        hence "projection (Complex_Vector_Spaces.span {s}) (w - k *\<^sub>C s) = 0"
          by (smt cs1 projectionPropertiesD vimage_singleton_eq) 
        hence "projection (Complex_Vector_Spaces.span {s}) w =
             projection (Complex_Vector_Spaces.span {s}) (k *\<^sub>C s)"
          using Complex_Vector_Spaces.span_mult
            \<open>w - k *\<^sub>C s \<in> orthogonal_complement (Complex_Vector_Spaces.span {s})\<close> 
            complex_vector.scale_eq_0_iff complex_vector.span_base complex_vector.span_zero cs1 
            projection_fixed_points projection_uniq singletonI by metis
        moreover have "projection (Complex_Vector_Spaces.span {s}) (k *\<^sub>C s) = k *\<^sub>C s"
          by (simp add: complex_vector.span_base complex_vector.span_scale cs1 projection_fixed_points)
        ultimately have "projection (Complex_Vector_Spaces.span {s}) w = k *\<^sub>C s"
          by simp
        thus ?thesis unfolding f_def by simp
      qed
      ultimately show ?thesis 
        unfolding F'_def by auto
    qed
    from r1 r2 r3 r4 assms
    have "cbounded_linear F'"
      using Suc.IH b3 b9 by blast 
    moreover have "F = (\<lambda>x. F' x + f x)"
      using F'_def by auto
    ultimately show "cbounded_linear F"
      using f1 Complex_Vector_Spaces.cbounded_linear_add by blast
  qed
  show ?thesis
    using cblinfun_operator_finite_dim'[where F = F and basis = basis and S = basis 
        and n = "card basis"]  by (smt Diff_cancel b3 b4 b9 complex_vector.linear_0
        complex_vector.span_empty empty_iff insert_iff order_refl)
qed


lemma ortho_imples_independent:
  assumes a1: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<langle>x, y\<rangle> = 0"
    and a2: "0 \<notin> A" 
  shows "complex_vector.independent A"
proof-
  have "finite t \<Longrightarrow> t \<subseteq> A \<Longrightarrow> (\<Sum>v\<in>t. u v *\<^sub>C v) = 0 \<Longrightarrow> v \<in> t \<Longrightarrow> u v = 0"
    for t u v
  proof-
    assume b1: "finite t" and b2: "t \<subseteq> A" and b3: "(\<Sum>v\<in>t. u v *\<^sub>C v) = 0" and b4: "v \<in> t"
    have "v'\<in>t-{v} \<Longrightarrow> \<langle>v, v'\<rangle> = 0" for v'
    proof-
      assume "v'\<in>t-{v}"
      hence "v \<noteq> v'" by blast
      thus ?thesis using a1
        by (meson DiffD1 \<open>v' \<in> t - {v}\<close> b2 b4 subset_eq) 
    qed
    hence sum0: "(\<Sum>v'\<in>t-{v}. u v' * \<langle>v, v'\<rangle>) = 0"
      by simp
    have "\<langle>v, (\<Sum>v'\<in>t. u v' *\<^sub>C v')\<rangle> = (\<Sum>v'\<in>t. u v' * \<langle>v, v'\<rangle>)"
      using b1
      by (metis (mono_tags, lifting) cinner_scaleC_right cinner_sum_right sum.cong) 
    also have "\<dots> = u v * \<langle>v, v\<rangle> + (\<Sum>v'\<in>t-{v}. u v' * \<langle>v, v'\<rangle>)"
      by (meson b1 b4 sum.remove)
    also have "\<dots> = u v * \<langle>v, v\<rangle>"
      using sum0 by simp
    finally have "\<langle>v, (\<Sum>v'\<in>t. u v' *\<^sub>C v')\<rangle> =  u v * \<langle>v, v\<rangle>"
      by blast
    hence "u v * \<langle>v, v\<rangle> = 0" using b3 by simp
    moreover have "\<langle>v, v\<rangle> \<noteq> 0"
    proof-
      have "v \<in> A"
        using b2 b4 by blast        
      hence "v \<noteq> 0"
        using a2 by blast
      thus ?thesis by simp 
    qed
    ultimately show "u v = 0" by simp
  qed
  thus ?thesis using independent_explicit_module
    by (smt Complex_Vector_Spaces.dependent_raw_def) 
      (* > 1s *)
qed

(* TODO: Put inside complex_normed_vector_inf_norm_leq_any_norm'
  after the proof is completed *)
lemma complex_normed_vector_inf_norm_leq_any_norm':
  includes notation_norm
  fixes  F:: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" (* TODO remove *)
    and basis:: "'a set"
  assumes b1: "complex_vector.span basis = UNIV"
    and b2: "complex_vector.independent basis"
    and b3: "finite basis"
    and b4: "basis \<noteq> {}" (* TODO: remove: if basis={}, (\<exists>i\<in>basis. \<parallel>r i\<parallel> = 1) is false *)
  shows "\<exists>c>0. \<forall>r. (\<forall>i\<in>basis. \<parallel>r i\<parallel> \<le> 1) \<and> (\<exists>i\<in>basis. \<parallel>r i\<parallel> = 1)
                       \<longrightarrow> c \<le> \<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>"
proof-
  define f::"'a \<Rightarrow> real" where "f s = \<parallel>s\<parallel>" for s
  define S where "S = {(\<Sum>i\<in>basis. r i *\<^sub>C i) |r. (\<forall>i\<in>basis. \<parallel>r i\<parallel> \<le> 1) \<and> (\<exists>i\<in>basis. \<parallel>r i\<parallel> = 1)}"
  have "S \<noteq> {}"
  proof-
    obtain b where "b\<in>basis"
      using b4 by blast
    define r::"'a \<Rightarrow> complex" where "r = (\<lambda>i. if i = b then 1 else 0)"
    have "\<forall>i\<in>basis. \<parallel>r i\<parallel> \<le> 1"
      unfolding r_def by auto
    moreover have "\<exists>i\<in>basis. \<parallel>r i\<parallel> = 1"
      unfolding r_def
      by (simp add: \<open>b \<in> basis\<close>) 
    ultimately have "(\<Sum>i\<in>basis. r i *\<^sub>C i)\<in>S"
      unfolding S_def
      by blast
    thus ?thesis by blast
  qed
  moreover have "compact S"
    sorry
      (* Ask to Dominique for a fast proof *)
      (* using unions of compact sets *)
  moreover have "continuous_on S f"
    unfolding f_def
    by (simp add: continuous_on_norm)   
  ultimately have "\<exists>x\<in>S. \<forall>y\<in>S. f x \<le> f y"
    using continuous_attains_inf
    by blast
  then obtain x where u1: "x\<in>S" and u2: "y\<in>S \<Longrightarrow> f x \<le> f y" for y
    by blast
  have "f x > 0"
  proof(rule classical)
    assume "\<not>(f x > 0)"
    hence "\<parallel>x\<parallel> = 0"
      unfolding f_def by auto
    hence "x = 0"
      by auto
    hence "\<exists>r.  (\<forall>i\<in>basis. \<parallel>r i\<parallel> \<le> 1) \<and> (\<exists>i\<in>basis. \<parallel>r i\<parallel> = 1) \<and> (\<Sum>i\<in>basis. r i *\<^sub>C i) = 0"
      using u1 unfolding S_def by auto
    then obtain r where v1: "\<forall>i\<in>basis. \<parallel>r i\<parallel> \<le> 1" and v2: "\<exists>i\<in>basis. \<parallel>r i\<parallel> = 1" 
      and v3: "(\<Sum>i\<in>basis. r i *\<^sub>C i) = 0" by blast
    from v3 have "r i = 0"
      if "i\<in>basis" for i
      by (metis b2 Complex_Vector_Spaces.dependent_raw_def b3 complex_vector.dependent_finite that)
    thus ?thesis using v2 by simp
  qed
  moreover have "\<forall>i\<in>basis. \<parallel>r i\<parallel> \<le> 1 \<Longrightarrow> \<exists>i\<in>basis. \<parallel>r i\<parallel> = 1 \<Longrightarrow> f x \<le> \<parallel> (\<Sum>i\<in>basis. r i *\<^sub>C i) \<parallel>"
    for r
    using u2 unfolding S_def f_def by blast
  ultimately show ?thesis
    by blast 
qed

lemma complex_normed_vector_inf_norm_leq_any_norm:
  includes notation_norm
  fixes  F:: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" (* TODO remove *)
    and basis:: "'a set"
  assumes b1: "complex_vector.span basis = UNIV"
    and b2: "complex_vector.independent basis"
    and b3: "finite basis" 
    and b4: "basis \<noteq> {}"
  shows "\<exists>C>0. \<forall>r. Max {\<parallel>r j\<parallel> |j. j\<in>basis} \<le> C*\<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>"
proof-
  have "\<exists>c>0. \<forall>r. (\<forall>i\<in>basis. \<parallel>r i\<parallel> \<le> 1) \<and> (\<exists>i\<in>basis. \<parallel>r i\<parallel> = 1) \<longrightarrow> c \<le> \<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>"
    using assms complex_normed_vector_inf_norm_leq_any_norm'
    by blast
  then obtain c where q1: "c > 0" and
    q2: "(\<forall>i\<in>basis. \<parallel>s i\<parallel> \<le> 1) \<and> (\<exists>i\<in>basis. \<parallel>s i\<parallel> = 1) \<longrightarrow> c \<le> \<parallel>(\<Sum>i\<in>basis. s i *\<^sub>C i)\<parallel>" for s
    by blast
  define C::real where "C = 1/c"
  have "C > 0"
    unfolding C_def q1
    by (simp add: q1) 
  moreover have "Max {\<parallel>r j\<parallel> |j. j\<in>basis} \<le> C*\<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>" for r
  proof(cases "\<forall>i\<in>basis. r i = 0")
    case True
    have "i\<in>basis \<Longrightarrow> \<parallel>r i\<parallel> = 0" for i
      by (simp add: True)      
    hence "{\<parallel>r j\<parallel> |j. j\<in>basis} = {0}"
      by (smt Collect_cong b3 b4 finite.cases insertI1 singleton_conv)     
    hence "Max {\<parallel>r j\<parallel> |j. j\<in>basis} = 0"
      by simp      
    moreover have "\<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel> = 0"
      using True
      by simp 
    ultimately show ?thesis by simp
  next
    case False
    define s where "s i = (r i)/( Max {\<parallel>r j\<parallel> |j. j\<in>basis} )" for i
    have p1: "i\<in>basis \<Longrightarrow> \<parallel>s i\<parallel> \<le> 1"
      for i
    proof-
      assume i1: "i\<in>basis"
      define S where "S = {\<parallel>r j\<parallel> |j. j\<in>basis}"
      have "\<parallel>r i\<parallel> \<in> S"
        unfolding S_def
        using i1 by blast 
      moreover have "finite S"
        unfolding S_def
        by (simp add: b3) 
      ultimately have "\<parallel>r i\<parallel> \<le> ( Max S )"
        by simp
      thus ?thesis
        unfolding s_def S_def
        by (smt complex_of_real_cmod complex_of_real_nn_iff div_by_0 
            linordered_field_class.less_divide_eq_1_pos norm_divide norm_le_zero_iff of_real_eq_iff)        
    qed
    moreover have p2: "\<exists>i\<in>basis. \<parallel>s i\<parallel> = 1"
    proof-
      define S where "S = {\<parallel>r j\<parallel> |j. j\<in>basis}"
      have "finite S"
        unfolding S_def
        by (simp add: b3) 
      hence "\<exists>i\<in>basis. \<parallel>r i\<parallel> = Max S"
        unfolding S_def
        by (smt False Max_in S_def empty_iff mem_Collect_eq) 
      then obtain i where r1: "i\<in>basis" and r2: "\<parallel>r i\<parallel> = ( Max S )"
        by blast
      have "\<exists>i\<in>basis. r i \<noteq> 0"
        using False by blast
      hence "\<exists>i\<in>basis. \<parallel>r i\<parallel> > 0"
        by auto
      hence "Max S \<noteq> 0"
        unfolding S_def
        using Max_gr_iff S_def \<open>finite S\<close> by fastforce 
      hence "\<parallel>r i\<parallel> / ( Max S ) = 1"
        using r2
        by simp
      thus ?thesis
        unfolding s_def 
        using r1
        by (metis S_def \<open>\<And>thesis. (\<And>i. \<lbrakk>i \<in> basis; cmod (r i) = Max S\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
            complex_of_real_cmod complex_of_real_nn_iff norm_divide norm_ge_zero of_real_eq_iff) 
    qed
    ultimately have p3: "c \<le> \<parallel>(\<Sum>i\<in>basis. s i *\<^sub>C i)\<parallel>"
      using q2 by blast
    moreover have m0: "Max {\<parallel>r j\<parallel> |j. j\<in>basis} \<ge> 0"
    proof-
      define S where "S = {\<parallel>r j\<parallel> |j. j\<in>basis}"
      have "\<parallel>r j\<parallel> \<in> S"
        if "j\<in>basis"
        for j
        unfolding S_def
        using that by auto
      moreover have "\<parallel>r j\<parallel> \<ge> 0"
        if "j\<in>basis"
        for j
        by simp       
      moreover have "finite S"
        unfolding S_def
        by (simp add: b3) 
      ultimately show ?thesis using Lattices_Big.linorder_class.Max.coboundedI
        by (smt False S_def)
    qed
    ultimately have 
      "( Max {\<parallel>r j\<parallel> |j. j\<in>basis} ) * c \<le> ( Max {\<parallel>r j\<parallel> |j. j\<in>basis} ) * \<parallel>(\<Sum>i\<in>basis. s i *\<^sub>C i)\<parallel>"
      using mult_left_mono by blast
    also have "\<dots> = \<parallel>( Max {\<parallel>r j\<parallel> |j. j\<in>basis} ) *\<^sub>C (\<Sum>i\<in>basis. s i *\<^sub>C i)\<parallel>"
      by (simp add: m0)
    also have "\<dots> = \<parallel>(\<Sum>i\<in>basis. ( Max {\<parallel>r j\<parallel> |j. j\<in>basis} ) *\<^sub>C (s i *\<^sub>C i))\<parallel>"
      by (simp add: scaleC_right.sum)
    also have "\<dots> = \<parallel>(\<Sum>i\<in>basis. ( (Max {\<parallel>r j\<parallel> |j. j\<in>basis}) * s i) *\<^sub>C i)\<parallel>"
      by auto
    also have "\<dots> = \<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>"
    proof-
      have "(Max {\<parallel>r j\<parallel> |j. j\<in>basis}) \<noteq> 0"
        using p2 s_def by auto
      hence "(Max {\<parallel>r j\<parallel> |j. j\<in>basis}) * s i = r i"
        for i
        unfolding s_def
        by simp
      thus ?thesis
        by simp
    qed
    finally have "( Max {\<parallel>r j\<parallel> |j. j\<in>basis} ) * c \<le> \<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>".
    thus ?thesis using C_def
      by (smt divide_cancel_left divide_divide_eq_left' linordered_field_class.divide_pos_pos 
          nonzero_divide_mult_cancel_left norm_ge_zero ordered_field_class.sign_simps(67) 
          ordered_semiring_strict_class.mult_less_le_imp_less q1) 
  qed
  ultimately show ?thesis by blast
qed

lemma complex_normed_vector_norm_basis:
  includes notation_norm
  fixes  F:: "'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" (* TODO remove *)
    and basis:: "'a set"
  assumes b1: "complex_vector.span basis = UNIV"
    and b2: "complex_vector.independent basis"
    and b3: "finite basis" 
    and b4: "basis \<noteq> {}"
  shows "\<exists>C>0. \<forall>r. \<forall>j\<in>basis. \<parallel>r j\<parallel> \<le> C*\<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>"
proof-
  have "\<exists>C>0. \<forall>r. Max {\<parallel>r j\<parallel> |j. j\<in>basis} \<le> C*\<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>"  
    using assms complex_normed_vector_inf_norm_leq_any_norm
    by blast
  then obtain C where c0: "C > 0" 
    and c1: "Max {\<parallel>r j\<parallel> |j. j\<in>basis} \<le> C*\<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>" for r
    by blast
  have "\<parallel>r k\<parallel> \<le> C*\<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>"
    if a1: "k\<in>basis"
    for r k
  proof-
    define S where "S = {\<parallel>r j\<parallel> |j. j\<in>basis}"
    have "\<parallel>r k\<parallel>\<in>S"
      unfolding S_def using a1 by blast
    moreover have "finite S"
      unfolding S_def using b3 by simp
    ultimately have "\<parallel>r k\<parallel> \<le> Max S"
      using a1
      by simp 
    thus ?thesis unfolding S_def using c1[where r = r] by simp
  qed
  thus ?thesis using c0 by blast
qed


(* There is an existing locale "finite_dimensional_vector_space" *)
(* TODO: Should hold for type_class complex_normed_vector.
See chapter on Finite Dimensional Normed Spaces in Conway's Functional Analysis book *)
lemma cblinfun_operator_finite_dim:
  fixes  F::"'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" 
    and basis::"'a set"
  assumes b1: "complex_vector.span basis = UNIV"
    and b2: "complex_vector.independent basis"
    and b3:"finite basis" 
    and b4: "basis \<noteq> {}" (* TODO: remove premise (if basis={}, then span={0}, then F=0, then bounded) *)
    and b5:"clinear F"
  shows "cbounded_linear F"
proof -
  include notation_norm
  have "\<exists>C>0. \<forall>r. \<forall>j\<in>basis. \<parallel>r j\<parallel> \<le> C*\<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>"   
    using complex_normed_vector_norm_basis b1 b2 b3 b4.
  then obtain C where C_def: "j\<in>basis \<Longrightarrow> \<parallel>r j\<parallel> \<le> C*\<parallel>(\<Sum>i\<in>basis. r i *\<^sub>C i)\<parallel>" for r j
    by blast
  define M::real where "M = C * (\<Sum>a\<in>basis. \<parallel>F a\<parallel>)"
  have "\<parallel>F x\<parallel> \<le> \<parallel>x\<parallel> * M"
    for x
  proof-
    have "x \<in> complex_vector.span basis"
      by (simp add: b1)
    have "\<exists>r. x = (\<Sum>a\<in>basis. r a *\<^sub>C a)"
      by (simp add: Complex_Vector_Spaces.span_explicit_finite b1 b2 b3)
    then obtain r where r_def: "x = (\<Sum>a\<in>basis. r a *\<^sub>C a)"
      by blast     
    have "a\<in>basis \<Longrightarrow> \<parallel>F a\<parallel> \<ge> 0"
      for a
      by simp      
    hence FM: "a\<in>basis \<Longrightarrow> \<parallel>r a\<parallel> * \<parallel>F a\<parallel> \<le> C * \<parallel>x\<parallel> * \<parallel>F a\<parallel>"
      for a
      by (simp add: C_def mult_right_mono r_def)
    have "F x = F (\<Sum>a\<in>basis. r a *\<^sub>C a)"
      using r_def
      by simp
    also have "\<dots> = (\<Sum>a\<in>basis. r a *\<^sub>C F a)"
      by (smt Finite_Cartesian_Product.sum_cong_aux b5 complex_vector.linear_scale 
          complex_vector.linear_sum)
    finally have "F x = (\<Sum>a\<in>basis. r a *\<^sub>C F a)".
    hence "\<parallel>F x\<parallel> = \<parallel>(\<Sum>a\<in>basis. r a *\<^sub>C F a)\<parallel>"
      by simp
    also have "\<dots> \<le> (\<Sum>a\<in>basis. \<parallel>r a *\<^sub>C F a\<parallel>)"
      by (simp add: sum_norm_le)
    also have "\<dots> \<le> (\<Sum>a\<in>basis. \<parallel>r a\<parallel> * \<parallel>F a\<parallel>)"
      by simp
    also have "\<dots> \<le> (\<Sum>a\<in>basis. C * \<parallel>x\<parallel> * \<parallel>F a\<parallel>)"
      using FM
      by (simp add: sum_mono) 
    also have "\<dots> \<le> \<parallel>x\<parallel> * C * (\<Sum>a\<in>basis. \<parallel>F a\<parallel>)"
      using sum_distrib_left
      by (metis eq_iff vector_space_over_itself.scale_left_commute 
          vector_space_over_itself.scale_scale)
    also have "\<dots> = \<parallel>x\<parallel> * M"
      unfolding M_def
      by linarith 
    finally show ?thesis .
  qed
  thus ?thesis
    using b5 cbounded_linear_def by blast
qed

(* see above
lemma cblinfun_operator_finite_dim:
  fixes  F::"'a::chilbert_space \<Rightarrow> 'b::chilbert_space" and basis::"'a set"
  assumes b1: "complex_vector.span basis = UNIV"
    and b2: "complex_vector.independent basis"
    and b3:"finite basis" and b4:"clinear F"
  shows "cbounded_linear F"
proof-
  have \<open>\<exists> A. (\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0)
           \<and> complex_vector.span A = complex_vector.span basis
           \<and> 0 \<notin> A \<and> finite A\<close>
    by (simp add: Gram_Schmidt b3)
  then obtain A where a1: "\<forall>a\<in>A. \<forall>a'\<in>A. a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0"
    and a2: "complex_vector.span A = complex_vector.span basis"
    and a4: "0 \<notin> A" and a5: "finite A"
    by auto
  have "is_ob A"
    unfolding is_ob_def is_ortho_set_def is_basis_def
  proof auto
    show "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<langle>x, y\<rangle> = 0"
      using a1 by auto
    thus "module.dependent (*\<^sub>C) A \<Longrightarrow> False"
      using ortho_imples_independent a4 by blast
    show "\<And>x. x \<in> closure (Complex_Vector_Spaces.span A)"
      using a2 b1 by auto
  qed
  thus ?thesis using cblinfun_operator_finite_dim_ortho[where F = F and basis = A]
    by (simp add: a5 b4)
qed
*)*)



(* TODO: Remove existence (because we have Complex_Vector_Spaces.construct).
   For uniqueness: check if that already exists (probably!) *)
lemma cblinfun_operator_basis_existence_uniq:
  fixes basis::\<open>'a::chilbert_space set\<close> and \<phi>::\<open>'a \<Rightarrow> 'b::chilbert_space\<close>
  assumes \<open>complex_vector.span basis = UNIV\<close> 
    and \<open>complex_vector.independent basis\<close>
    and \<open>finite basis\<close>
    and "basis \<noteq> {}" (* TODO remove (if basis empty, all functions 0), or not used after changing lemmas above *)
  shows \<open>\<exists>!F. \<forall>s\<in>basis.  F *\<^sub>V s = \<phi> s\<close>
proof-
  have \<open>\<exists>F. \<forall>s\<in>basis.  cblinfun_apply F s = \<phi> s\<close>
  proof-
    have f1: "Complex_Vector_Spaces.representation basis w =
        (if complex_independent basis \<and> w \<in> Complex_Vector_Spaces.span basis
         then SOME f.
         (\<forall>v. f v \<noteq> 0 \<longrightarrow> v \<in> basis) \<and>
         finite {v. f v \<noteq> 0} \<and> (\<Sum>v | f v \<noteq> 0. f v *\<^sub>C v) = w
       else (\<lambda>b. 0))" for w
      by (simp add: complex_vector.representation_def)
    define f::"'a \<Rightarrow> 'a \<Rightarrow> complex" where
      "f w v = Complex_Vector_Spaces.representation basis w v" for w v
    have f2: "\<forall>v. f w v \<noteq> 0 \<longrightarrow> v \<in> basis" for w
      using complex_vector.representation_ne_zero f_def by auto
    have f3: "finite {v. f w v \<noteq> 0}" for w
      by (metis \<open>f \<equiv> Complex_Vector_Spaces.representation basis\<close> complex_vector.finite_representation)
    have f4: "(\<Sum>v | f w v \<noteq> 0. f w v *\<^sub>C v) = w" for w
      using \<open>complex_vector.independent basis\<close> \<open>complex_vector.span basis = UNIV\<close>
        f1[where w = w] unfolding f_def
      using Complex_Vector_Spaces.dependent_raw_def complex_vector.sum_nonzero_representation_eq 
        iso_tuple_UNIV_I
    proof -
      have "complex_independent basis"
        by (metis Complex_Vector_Spaces.dependent_raw_def \<open>complex_vector.independent basis\<close>)
      thus "(\<Sum>a | Complex_Vector_Spaces.representation basis w a \<noteq> 0. 
            Complex_Vector_Spaces.representation basis w a *\<^sub>C a) = w"
        using \<open>Complex_Vector_Spaces.span basis = UNIV\<close> complex_vector.sum_nonzero_representation_eq iso_tuple_UNIV_I
        by metis (* > 1s *)
    qed
    have f5: "w \<in> basis \<Longrightarrow> f w w = 1" for w
      using complex_vector.representation_basis[where basis = basis and b = w]
      by (smt Complex_Vector_Spaces.dependent_raw_def \<open>f \<equiv> Complex_Vector_Spaces.representation basis\<close> assms(2))
    have f6: "w\<in>basis \<Longrightarrow> v \<noteq> w \<Longrightarrow> f w v = 0" for v w
      using complex_vector.representation_basis f1 f_def by fastforce
    define F where "F w = (\<Sum>v | f w v \<noteq> 0. f w v *\<^sub>C \<phi> v)" for w

    have f_def': "w = (\<Sum>v\<in>basis. f w v *\<^sub>C v)" for w
    proof- 
      have "basis = {v |v. f w v \<noteq> 0 \<and> v \<in> basis} \<union> {v |v. f w v = 0 \<and> v \<in> basis}"
        by blast
      moreover have "{v |v. f w v \<noteq> 0 \<and> v \<in> basis} \<inter> {v |v. f w v = 0 \<and> v \<in> basis} = {}"
        by blast
      ultimately have "(\<Sum>v\<in>basis. f w v *\<^sub>C v) =
                     (\<Sum>v\<in>{v |v. f w v \<noteq> 0 \<and> v \<in> basis}. f w v *\<^sub>C v)
                  +  (\<Sum>v\<in>{v |v. f w v = 0 \<and> v \<in> basis}. f w v *\<^sub>C v)"
        by (metis (no_types, lifting) assms(3) finite_Un sum.union_disjoint)
      moreover have "(\<Sum>v\<in>{v |v. f w v = 0 \<and> v \<in> basis}. f w v *\<^sub>C v) = 0"
        by simp        
      ultimately 
      have "(\<Sum>v\<in>basis. f w v *\<^sub>C v) = (\<Sum>v\<in>{v |v. f w v \<noteq> 0 \<and> v \<in> basis}. f w v *\<^sub>C v)"
        by simp
      also have "\<dots> = (\<Sum>v\<in>{v |v. f w v \<noteq> 0}. f w v *\<^sub>C v)"
        using f2 by meson  
      also have "\<dots> = w"
        using f4 by auto
      finally show ?thesis by simp
    qed
    have F_def': "F w = (\<Sum>v\<in>basis. f w v *\<^sub>C \<phi> v)" for w
    proof- 
      have "basis = {v |v. f w v \<noteq> 0 \<and> v \<in> basis} \<union> {v |v. f w v = 0 \<and> v \<in> basis}"
        by blast
      moreover have "{v |v. f w v \<noteq> 0 \<and> v \<in> basis} \<inter> {v |v. f w v = 0 \<and> v \<in> basis} = {}"
        by blast
      ultimately have "(\<Sum>v\<in>basis. f w v *\<^sub>C \<phi> v) =
                     (\<Sum>v\<in>{v |v. f w v \<noteq> 0 \<and> v \<in> basis}. f w v *\<^sub>C \<phi> v)
                  +  (\<Sum>v\<in>{v |v. f w v = 0 \<and> v \<in> basis}. f w v *\<^sub>C \<phi> v)"
        by (metis (no_types, lifting) assms(3) finite_Un sum.union_disjoint)
      moreover have "(\<Sum>v\<in>{v |v. f w v = 0 \<and> v \<in> basis}. f w v *\<^sub>C \<phi> v) = 0"
        by simp        
      ultimately 
      have "(\<Sum>v\<in>basis. f w v *\<^sub>C \<phi> v) = (\<Sum>v\<in>{v |v. f w v \<noteq> 0 \<and> v \<in> basis}. f w v *\<^sub>C \<phi> v)"
        by simp
      also have "\<dots> = (\<Sum>v\<in>{v |v. f w v \<noteq> 0}. f w v *\<^sub>C \<phi> v)"
        using f2 by meson  
      also have "\<dots> = F w"
        unfolding F_def by auto
      finally show ?thesis by simp
    qed
    have f_add: "v\<in>basis \<Longrightarrow> f (w1+w2) v = f w1 v + f w2 v" for w1 w2 v
    proof-
      have "w1 = (\<Sum>v | v\<in>basis. f w1 v *\<^sub>C v)"
        using f_def' by auto
      moreover have "w2 = (\<Sum>v | v\<in>basis. f w2 v *\<^sub>C v)"
        using f_def' by auto
      ultimately have "w1 + w2 = (\<Sum>v | v\<in>basis. f w1 v *\<^sub>C v) +  (\<Sum>v | v\<in>basis. f w2 v *\<^sub>C v)"
        by simp
      also have "\<dots> = (\<Sum>v | v\<in>basis. (f w1 v *\<^sub>C v + f w2 v *\<^sub>C v))"
        by (metis (no_types, lifting) sum.cong sum.distrib)
      also have "\<dots> = (\<Sum>v | v\<in>basis. ((f w1 v + f w2 v) *\<^sub>C v))"
        by (metis scaleC_add_left)
      finally have "w1 + w2 = (\<Sum>v | v\<in>basis. ((f w1 v + f w2 v) *\<^sub>C v))"
        by blast
      moreover have "w1 + w2 = (\<Sum>v | v\<in>basis. (f (w1 + w2) v *\<^sub>C v))"
        using f_def' by auto
      ultimately have "(\<Sum>v | v\<in>basis. (f (w1 + w2) v *\<^sub>C v)) = (\<Sum>v | v\<in>basis. ((f w1 v + f w2 v) *\<^sub>C v))"
        by simp
      hence "0 = (\<Sum>v | v\<in>basis. (f (w1 + w2) v *\<^sub>C v)) -  (\<Sum>v | v\<in>basis. ((f w1 v + f w2 v) *\<^sub>C v))"
        by simp
      also have "\<dots> = (\<Sum>v | v\<in>basis. (f (w1 + w2) v *\<^sub>C v)- (f w1 v + f w2 v) *\<^sub>C v)"
        by (simp add: sum_subtractf)
      also have "\<dots> = (\<Sum>v | v\<in>basis. (f (w1 + w2) v - f w1 v - f w2 v) *\<^sub>C v)"
        by (metis (no_types, lifting) diff_diff_add scaleC_left.diff)
      finally have "0 = (\<Sum>v | v\<in>basis. (f (w1 + w2) v - f w1 v - f w2 v) *\<^sub>C v)"
        by simp
      hence "(\<Sum>v | v\<in>basis. (f (w1 + w2) v - f w1 v - f w2 v) *\<^sub>C v) = 0"
        by simp
      hence "v\<in>basis \<Longrightarrow> f (w1 + w2) v - f w1 v - f w2 v = 0" for v
      proof -
        assume "v \<in> basis"
        then have f1: "\<And>f. (\<Sum>a\<in>basis. f a *\<^sub>C a) \<noteq> 0 \<or> Complex_Vector_Spaces.dependent basis \<or> f v = 0"
          using assms(3) complex_vector.dependent_finite by auto
        have "complex_independent basis"
          by (simp add: Complex_Vector_Spaces.dependent_raw_def \<open>complex_vector.independent basis\<close>)
        thus ?thesis
          using f1 \<open>(\<Sum>v | v \<in> basis. (f (w1 + w2) v - f w1 v - f w2 v) *\<^sub>C v) = 0\<close> by fastforce
      qed
      thus ?thesis
        by (metis add.commute eq_diff_eq eq_iff_diff_eq_0 f2) 
    qed
    have f_scaleC: "v\<in>basis \<Longrightarrow> f (r *\<^sub>C w) v = r * f w v" for w v r
    proof-
      have "w = (\<Sum>v | v\<in>basis. f w v *\<^sub>C v)"
        using f_def' by auto
      hence "r *\<^sub>C w = r *\<^sub>C (\<Sum>v | v\<in>basis. f w v *\<^sub>C v)"
        by simp
      also have "\<dots> = (\<Sum>v | v\<in>basis. r *\<^sub>C (f w v *\<^sub>C v))"
        using scaleC_right.sum by blast
      also have "\<dots> = (\<Sum>v | v\<in>basis. (r * f w v) *\<^sub>C v)"
        by simp
      finally have "r *\<^sub>C w = (\<Sum>v | v\<in>basis. (r * f w v) *\<^sub>C v)"
        by blast
      moreover have "r *\<^sub>C w = (\<Sum>v | v\<in>basis. f (r *\<^sub>C w) v *\<^sub>C v)"
        by (simp add: f_def')
      ultimately have "(\<Sum>v | v\<in>basis. f (r *\<^sub>C w) v *\<^sub>C v) =  (\<Sum>v | v\<in>basis. (r * f w v) *\<^sub>C v)"
        by simp
      hence "0 = (\<Sum>v | v\<in>basis. f (r *\<^sub>C w) v *\<^sub>C v) - (\<Sum>v | v\<in>basis. (r * f w v) *\<^sub>C v)"
        by simp
      also have "\<dots> = (\<Sum>v | v\<in>basis. f (r *\<^sub>C w) v *\<^sub>C v - (r * f w v) *\<^sub>C v)"
        by (simp add: sum_subtractf)
      also have "\<dots> = (\<Sum>v | v\<in>basis. (f (r *\<^sub>C w) v - r * f w v) *\<^sub>C v)"
        by (metis (no_types, lifting) scaleC_left.diff)
      finally have "0 = (\<Sum>v | v\<in>basis. (f (r *\<^sub>C w) v - r * f w v) *\<^sub>C v)"
        by blast
      hence \<open>(\<Sum>v | v\<in>basis. (f (r *\<^sub>C w) v - r * f w v) *\<^sub>C v) = 0\<close>
        by simp
      hence "v\<in>basis \<Longrightarrow> f (r *\<^sub>C w) v - r * f w v = 0" for v
      proof -
        assume "v \<in> basis"
        then have f1: "\<And>f. (\<Sum>a\<in>basis. f a *\<^sub>C a) \<noteq> 0 \<or> Complex_Vector_Spaces.dependent basis \<or> f v = 0"
          using assms(3) complex_vector.dependent_finite by auto
        have "complex_independent basis"
          by (simp add: Complex_Vector_Spaces.dependent_raw_def \<open>complex_vector.independent basis\<close>)
        thus ?thesis
          using f1 \<open>(\<Sum>v | v\<in>basis. (f (r *\<^sub>C w) v - r * f w v) *\<^sub>C v) = 0\<close> by fastforce
      qed
      thus ?thesis
        by (metis diff_eq_diff_eq diff_numeral_special(9) f2 mult_cancel_right1) 
    qed
    have "clinear F" 
      unfolding clinear_def proof
      show "F (b1 + b2) = F b1 + F b2"
        for b1 :: 'a
          and b2 :: 'a
        using f_add 
        unfolding F_def'
        by (smt scaleC_add_left sum.cong sum.distrib)         

      show "F (r *\<^sub>C b) = r *\<^sub>C F b"
        for r :: complex
          and b :: 'a
      proof-
        have "F (r *\<^sub>C b) = (\<Sum>v\<in>basis. f (r *\<^sub>C b) v *\<^sub>C \<phi> v)"
          unfolding F_def' by blast
        also have "\<dots> = (\<Sum>v\<in>basis. (r * f b v) *\<^sub>C \<phi> v)"
          using f_scaleC by simp
        also have "\<dots> = (\<Sum>v\<in>basis. r *\<^sub>C (f b v *\<^sub>C \<phi> v))"
          by simp
        also have "\<dots> = r *\<^sub>C (\<Sum>v\<in>basis. f b v *\<^sub>C \<phi> v)"
          by (metis (full_types) scaleC_right.sum)          
        finally show ?thesis using F_def' by simp
      qed  
    qed
    hence "cbounded_linear F"
      using cblinfun_operator_finite_dim assms by smt 
    moreover have "w\<in>basis \<Longrightarrow> F w = \<phi> w" for w
    proof-
      assume b1: "w\<in>basis"
      have "F w = (\<Sum>v | f w v \<noteq> 0 \<and> v = w. f w v *\<^sub>C \<phi> v)
                 +(\<Sum>v | f w v \<noteq> 0 \<and> v \<noteq> w. f w v *\<^sub>C \<phi> v)"
        by (smt Collect_cong F_def add.commute add_cancel_right_left b1 f6 mem_Collect_eq sum.cong 
            sum.neutral_const)
      moreover have "(\<Sum>v | f w v \<noteq> 0 \<and> v = w. f w v *\<^sub>C \<phi> v) = \<phi> w"
      proof-
        have "f w w \<noteq> 0"
          by (simp add: b1 f5)
        hence "(\<Sum>v | f w v \<noteq> 0 \<and> v = w. f w v *\<^sub>C \<phi> v) = (\<Sum>v | v = w. f w v *\<^sub>C \<phi> v)"
          by metis
        also have "\<dots> = f w w *\<^sub>C \<phi> w"
          using Collect_mem_eq add_cancel_right_left complex_vector.scale_cancel_right 
            complex_vector.scale_zero_right by auto          
        finally have "(\<Sum>v | f w v \<noteq> 0 \<and> v = w. f w v *\<^sub>C \<phi> v) = f w w *\<^sub>C \<phi> w"
          by blast
        thus ?thesis
          by (simp add: b1 f5) 
      qed
      moreover have "(\<Sum>v | f w v \<noteq> 0 \<and> v \<noteq> w. f w v *\<^sub>C \<phi> v) = 0"
        by (simp add: b1 f6)        
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis apply transfer
      by blast
  qed
  moreover have \<open>(\<And>s. s\<in>basis \<Longrightarrow> cblinfun_apply F s = \<phi> s)
             \<Longrightarrow> (\<And>s. s\<in>basis \<Longrightarrow> cblinfun_apply G s = \<phi> s) \<Longrightarrow> F = G\<close> for F G
  proof-
    assume a1: "\<And>s. s\<in>basis \<Longrightarrow> F s = \<phi> s" and a2: "\<And>s. s\<in>basis \<Longrightarrow> G s = \<phi> s"
    hence "s\<in>basis \<Longrightarrow> (F-G) s = 0" for s
      by (simp add: minus_cblinfun.rep_eq)
    hence "F - G = 0"
      using cblinfun_operator_basis_zero_uniq[where F = "F - G" and basis = basis]
        assms(1) assms(2) assms(3) by auto
    thus ?thesis by simp
  qed
  ultimately show ?thesis
    by auto 
qed


(* TODO: move *)
lemma obn_enum_uniq_zero:
  fixes f ::"'a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
  defines "basis == set (canonical_basis::'a list)"
  assumes "\<And>u. u \<in> basis \<Longrightarrow> cblinfun_apply f u = 0"
  shows  "f = 0" 
proof-
  have "cblinfun_apply f x = 0" for x
  proof-
    define a where "a = ((complex_vector.representation basis x)::'a \<Rightarrow> complex)"
    have a1: "a v \<noteq> 0 \<Longrightarrow> v \<in> basis" for v
      by (simp add: a_def complex_vector.representation_ne_zero)      
    have "finite {v. a v \<noteq> 0}"
      by (simp add: a_def complex_vector.finite_representation)      
    have "complex_independent basis"
      using basis_def canonical_basis_non_zero is_ortho_set_independent is_orthonormal by auto
    moreover have "x \<in> Complex_Vector_Spaces.span basis"
    proof-
      have "closure (Complex_Vector_Spaces.span basis) = UNIV"
        using is_basis_set
        unfolding basis_def is_basis_def
        by blast        
      moreover have "closure (Complex_Vector_Spaces.span basis) = Complex_Vector_Spaces.span basis"
        by (simp add: basis_def span_finite_dim)        
      ultimately have "Complex_Vector_Spaces.span basis = UNIV"
        by blast
      thus ?thesis by blast
    qed
    ultimately have "(\<Sum>v | a v \<noteq> 0. a v *\<^sub>C v) = x"
      unfolding a_def 
      using sum.cong Collect_cong DiffD1 DiffD2 Eps_cong \<open>finite {v. a v \<noteq> 0}\<close> a_def complex_vector.representation_def complex_vector.sum_nonzero_representation_eq subset_iff sum.mono_neutral_cong_right
      by smt
    hence "cblinfun_apply f x = cblinfun_apply f (\<Sum>v | a v \<noteq> 0. a v *\<^sub>C v)"
      by simp
    also have "\<dots> = (\<Sum>v | a v \<noteq> 0. a v *\<^sub>C cblinfun_apply f v)"
      using \<open>finite {v. a v \<noteq> 0}\<close> clinear_finite_sum by blast
    also have "\<dots> = 0"
    proof-
      have "a v \<noteq> 0 \<Longrightarrow> a v *\<^sub>C (cblinfun_apply f v) = 0" for v
      proof-
        assume "a v \<noteq> 0"
        hence "v \<in> basis"
          by (simp add: a1)
        hence "cblinfun_apply f v = 0"
          using assms(2) by auto          
        thus ?thesis by simp
      qed
      thus ?thesis
        by simp 
    qed
    finally show ?thesis
      by simp 
  qed
  thus ?thesis
    by (simp add: cblinfun_ext) 
qed


lemma obn_enum_uniq:
  fixes f g::"'a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
  defines "basis == set (canonical_basis::'a list)"
  assumes "\<And>u. u \<in> basis \<Longrightarrow> f *\<^sub>V u = g *\<^sub>V u"
  shows  "f = g" 
proof-
  define h where "h = f - g"
  have "\<And>u. u \<in> basis \<Longrightarrow> cblinfun_apply h u = 0"
    using assms unfolding h_def
    by (simp add: assms(2) minus_cblinfun.rep_eq)
  hence "h = 0"
    using obn_enum_uniq_zero[where f = h]
      basis_def by blast 
  thus ?thesis 
    unfolding h_def
    using eq_iff_diff_eq_0 by blast 
qed

lemma cinner_unique_onb_enum_zero:
  defines "basisA == set (canonical_basis::'a::onb_enum list)"
    and   "basisB == set (canonical_basis::'b::onb_enum list)"
  assumes "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> \<langle>v, F *\<^sub>V u\<rangle> = 0"
  shows "F = 0"
proof-
  have "F *\<^sub>V u = 0"
    if "u\<in>basisA" for u
  proof-
    have "\<And>v. v\<in>basisB \<Longrightarrow> \<langle>v, F *\<^sub>V u\<rangle> = 0"
      by (simp add: assms(3) that)
    moreover have "(\<And>v. v\<in>basisB \<Longrightarrow> \<langle>v, x\<rangle> = 0) \<Longrightarrow> x = 0"
      for x
    proof-     
      assume r1: "\<And>v. v\<in>basisB \<Longrightarrow> \<langle>v, x\<rangle> = 0"      
      have "\<langle>v, x\<rangle> = 0" for v
      proof-
        have "closure (Complex_Vector_Spaces.span basisB) = UNIV"
          using is_basis_set
          unfolding basisB_def is_basis_def
          by auto
        hence "Complex_Vector_Spaces.span basisB = UNIV"
          by (smt List.finite_set basisB_def span_finite_dim)
        hence "v \<in> Complex_Vector_Spaces.span basisB"
          by (smt iso_tuple_UNIV_I)
        hence "\<exists>t s. v = (\<Sum>a\<in>t. s a *\<^sub>C a) \<and> finite t \<and> t \<subseteq> basisB"
          using complex_vector.span_explicit
          by (smt mem_Collect_eq)
        then obtain t s where b1: "v = (\<Sum>a\<in>t. s a *\<^sub>C a)" and b2: "finite t" and b3: "t \<subseteq> basisB"
          by blast
        have "\<langle>v, x\<rangle> = \<langle>(\<Sum>a\<in>t. s a *\<^sub>C a), x\<rangle>"
          by (simp add: b1)
        also have "\<dots> = (\<Sum>a\<in>t. \<langle>s a *\<^sub>C a, x\<rangle>)"
          using cinner_sum_left by blast
        also have "\<dots> = (\<Sum>a\<in>t. cnj (s a) * \<langle>a, x\<rangle>)"
          by auto
        also have "\<dots> = 0"
          using b3 r1 subsetD by force
        finally show ?thesis by simp
      qed
      thus ?thesis
        by (simp add: \<open>\<And>v. \<langle>v, x\<rangle> = 0\<close> cinner_ext_0) 
    qed
    ultimately show ?thesis by simp
  qed
  thus ?thesis
    using basisA_def obn_enum_uniq_zero by auto 
qed

lemma cinner_unique_onb_enum:
  defines "basisA == set (canonical_basis::'a::onb_enum list)"
    and   "basisB == set (canonical_basis::'b::onb_enum list)"
  assumes "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> \<langle>v, F *\<^sub>V u\<rangle> = \<langle>v, G *\<^sub>V u\<rangle>"
  shows "F = G"
proof-
  define H where "H = F - G"
  have "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> \<langle>v, H *\<^sub>V u\<rangle> = 0"
    unfolding H_def
    by (simp add: assms(3) cinner_diff_right minus_cblinfun.rep_eq) 
  hence "H = 0"
    by (simp add: basisA_def basisB_def cinner_unique_onb_enum_zero)    
  thus ?thesis unfolding H_def by simp
qed

lemma cinner_unique_onb_enum':
  defines "basisA == set (canonical_basis::'a::onb_enum list)"
    and   "basisB == set (canonical_basis::'b::onb_enum list)"
  assumes "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> \<langle>F *\<^sub>V u, v\<rangle> = \<langle>G *\<^sub>V u, v\<rangle>"
  shows "F = G"
  using cinner_unique_onb_enum assms
  by (metis cinner_commute')

subsection \<open>Extension of complex bounded operators\<close>

definition cblinfun_extension where 
  "cblinfun_extension S \<phi> = (SOME B. \<forall>x\<in>S. B *\<^sub>V x = \<phi> x)"

definition cblinfun_extension_exists where 
  "cblinfun_extension_exists S \<phi> = (\<exists>B. \<forall>x\<in>S. B *\<^sub>V x = \<phi> x)"

(* TODO remove *)
lemma cblinfun_extension_itself:
  fixes B::"_ \<Rightarrow>\<^sub>C\<^sub>L _"
  assumes a1: "x \<in> complex_vector.span S" and a2: "complex_independent S"
  shows "cblinfun_extension S ((*\<^sub>V) B) x = B *\<^sub>V x"
proof-
  have "cblinfun_extension S ((*\<^sub>V) B) t = B *\<^sub>V t"
    if "t \<in> S"
    for t
    unfolding cblinfun_extension_def
    by (smt someI_ex that) 
  thus ?thesis using assms
    using equal_span
    by (meson applyOp_scaleC2 cblinfun_apply_add clinearI complex_vector.linear_eq_on_span)    
qed

lemma complex_independent_finite_onb_enum:
  assumes a1: "complex_independent A"
  shows "finite (A::'a::onb_enum set)"
proof(cases "set (canonical_basis::'a list) = {}")
  case True
  have "complex_vector.span (set (canonical_basis::'a list)) = {0}"
    by (simp add: True)
  moreover have "closure (complex_vector.span (set (canonical_basis::'a list))) = UNIV"
    using is_basis_def is_basis_set by blast    
  ultimately have "(UNIV::'a set) = {0}"
    by simp
  hence "finite (UNIV::'a set)"
    by (metis finite.emptyI finite.insertI)   
  thus ?thesis
    using rev_finite_subset by auto 
next
  case False
  define AA where "AA = Complex_Vector_Spaces.extend_basis A"
  have "complex_vector.span AA = UNIV"
    using span_extend_basis a1
    by (simp add: AA_def)
  moreover have "complex_independent AA"
    using a1
    by (simp add: AA_def complex_vector.independent_extend_basis)
  ultimately have "card AA = dim (UNIV::'a set)"
    by (metis complex_vector.basis_card_eq_dim subset_UNIV)
  also have "dim (UNIV::'a set) = card (set (canonical_basis::'a list))"
    using is_basis_set unfolding is_basis_def
    by (smt Complex_Vector_Spaces.dependent_raw_def List.finite_set complex_vector.dim_eq_card 
        complex_vector.dim_span is_basis_set span_finite_dim)
  finally have r1: "card AA = card (set (canonical_basis::'a list))".
  have "finite (set (canonical_basis::'a list))"
    by simp    
  hence "card (set (canonical_basis::'a list)) \<noteq> 0"
    using False by auto    
  hence "finite AA"
    using r1 card_infinite by force
  thus ?thesis unfolding AA_def
    by (simp add: assms complex_vector.extend_basis_superset rev_finite_subset)
qed

(* TODO: prove this *)
lemma cblinfun_extension_exists_finite:
  (* TODO: generalize to 
\<phi>::"'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" 
*)
  fixes \<phi>::"'a::chilbert_space \<Rightarrow> 'b::chilbert_space" 
  assumes a1: "complex_independent S"
    and a2: "complex_vector.span S = UNIV"
    and a3: "finite S"
    and a4: "S \<noteq> {}" (* TODO: not needed (cblinfun_extension_exists holds trivially for empty S) *)
  shows "cblinfun_extension_exists S \<phi>"
proof-
  define f::"'a::chilbert_space \<Rightarrow> 'b::chilbert_space" 
    where "f = complex_vector.construct S \<phi>"
  have "clinear f"
    using linear_construct
    by (simp add: complex_vector.linear_construct a1 f_def)    
  have "cbounded_linear f"
    by (metis cblinfun_operator_finite_dim Complex_Vector_Spaces.dependent_raw_def \<open>clinear f\<close> 
        a1 a2 a3 a4)
  then obtain B::"'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space" 
    where "B *\<^sub>V x = f x" for x
    using cblinfun_apply_cases by blast
  have "B *\<^sub>V x = \<phi> x"
    if c1: "x\<in>S"
    for x
  proof-
    have "B *\<^sub>V x = f x"
      by (simp add: \<open>\<And>x. B *\<^sub>V x = f x\<close>)
    also have "\<dots> = \<phi> x"
      by (simp add: a1 complex_vector.construct_basis f_def that)
    finally show?thesis by blast
  qed
  thus ?thesis 
    unfolding cblinfun_extension_exists_def
    by blast

qed

unbundle no_cblinfun_notation

end

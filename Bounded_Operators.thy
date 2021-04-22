(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Bounded_Operators
  imports 
    Complex_Inner_Product One_Dimensional_Spaces
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
  ultimately show \<open>\<exists>K. \<forall>x. norm (c *\<^sub>C f x) \<le> norm x * K\<close>
    by (metis ab_semigroup_mult_class.mult_ac(1) mult.commute)
qed

instance
proof
  have "r *\<^sub>R (x::'a \<Rightarrow>\<^sub>L 'b) = complex_of_real r *\<^sub>C x"
    for x :: "('a, 'b) blinfun"
      and r :: real
    apply transfer
    by (simp add: scaleR_scaleC)
  thus "((*\<^sub>R) r::'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
    by auto
  show "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a \<Rightarrow>\<^sub>L 'b"
      and y :: "'a \<Rightarrow>\<^sub>L 'b"
    apply transfer
    by (simp add: scaleC_add_right)

  show "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<Rightarrow>\<^sub>L 'b"
    apply transfer
    by (simp add: scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<Rightarrow>\<^sub>L 'b"
    apply transfer
    by simp

  have \<open>1 *\<^sub>C f x = f x\<close>
    for f :: \<open>'a\<Rightarrow>'b\<close> and x :: 'a
    by auto
  thus "1 *\<^sub>C x = x"
    for x :: "'a \<Rightarrow>\<^sub>L 'b"
    by (simp add: Bounded_Operators.scaleC_blinfun.rep_eq blinfun_eqI)   
qed  
end

instantiation blinfun :: (real_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
instance
proof intro_classes 
  have \<open>onorm (\<lambda>x. a *\<^sub>C f x) = cmod a * onorm f\<close>
    if a1: \<open>bounded_linear f\<close>
    for f::\<open>'a \<Rightarrow> 'b\<close> and a::complex
  proof-
    have \<open>cmod a \<ge> 0\<close>
      by simp
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
    ultimately have p1: \<open>(SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>) \<le> cmod a * K\<close>
      using \<open>\<forall> x. \<bar> ereal (cmod a * (norm (f x)) / (norm x)) \<bar> \<le> cmod a * K\<close>
        Sup_least mem_Collect_eq
      by (simp add: SUP_le_iff) 
    have  p2: \<open>\<And>i. i \<in> UNIV \<Longrightarrow> 0 \<le> ereal (cmod a * norm (f i) / norm i)\<close>
      by simp
    hence \<open>\<bar>SUP x. ereal (cmod a * (norm (f x)) / (norm x))\<bar>
              \<le> (SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>)\<close>    
      using  \<open>bdd_above {ereal (cmod a * (norm (f x)) / (norm x)) | x. True}\<close>
        \<open>{ereal (cmod a * (norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
      by (metis (mono_tags, lifting) SUP_upper2 Sup.SUP_cong UNIV_I 
          p2 abs_ereal_ge0 ereal_le_real)
    hence \<open>\<bar>SUP x. ereal (cmod a * (norm (f x)) / (norm x))\<bar> \<le> cmod a * K\<close>
      using  \<open>(SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>) \<le> cmod a * K\<close>
      by simp
    hence \<open>\<bar> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. (cmod a) * (norm (f x)) / norm x) i)) \<bar> \<noteq> \<infinity>\<close>
      by auto
    hence w2: \<open>( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. cmod a * (norm (f x)) / norm x) i))
             = ereal ( Sup ((\<lambda> x. cmod a * (norm (f x)) / norm x) ` (UNIV::'a set) ))\<close>
      by (simp add: ereal_SUP) 
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
    hence z1: \<open>real_of_ereal ( (SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) ) )
        = real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )\<close>
      by simp
    have z2: \<open>real_of_ereal (SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) ) 
                  = (SUP x. cmod a * (norm (f x) / norm x))\<close>
      using w2
      by auto 
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
    have z3: \<open>real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )
                = cmod a * (SUP x. norm (f x) / norm x)\<close>
      by (simp add: \<open>real_of_ereal (SUP x. ereal (norm (f x) / norm x)) = (SUP x. norm (f x) / norm x)\<close>)
    hence w1: \<open>(SUP x. cmod a * (norm (f x) / norm x)) =
          cmod a * (SUP x. norm (f x) / norm x)\<close>
      using z1 z2 by linarith     
    have v1: \<open>onorm (\<lambda>x. a *\<^sub>C f x) = (SUP x. norm (a *\<^sub>C f x) / norm x)\<close>
      by (simp add: onorm_def)
    have v2: \<open>(SUP x. norm (a *\<^sub>C f x) / norm x) = (SUP x. ((cmod a) * norm (f x)) / norm x)\<close>
      by simp
    have v3: \<open>(SUP x. ((cmod a) * norm (f x)) / norm x) =  (SUP x. (cmod a) * ((norm (f x)) / norm x))\<close>
      by simp
    have v4: \<open>(SUP x. (cmod a) * ((norm (f x)) / norm x)) = (cmod a) *  (SUP x. ((norm (f x)) / norm x))\<close>
      using w1
      by blast
    show \<open>onorm (\<lambda>x. a *\<^sub>C f x) = cmod a * onorm f\<close>
      using v1 v2 v3 v4
      by (metis (mono_tags, lifting) onorm_def)
  qed
  thus \<open>norm (a *\<^sub>C x) = cmod a * norm x\<close> 
    for a::complex and x::\<open>('a, 'b) blinfun\<close>
    apply transfer
    by blast
qed
end


lemma trivia_UNIV_blinfun:
  fixes f::\<open>'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close> 
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
  fixes f::\<open>nat \<Rightarrow> 'a::{real_normed_vector,not_singleton} \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
    and N::hypnat
  assumes \<open>N\<in>HNatInfinite\<close> 
  shows \<open>\<exists> x \<in> *s* (sphere 0 1). 
    hnorm ((*f* f) N) \<approx> hnorm ( (*f2* (\<lambda> n. (*\<^sub>v) (f n))) N x )\<close>
proof-
  have \<open>bounded_linear ((*\<^sub>v) (f n))\<close>
    for n
    using blinfun_apply by blast
  hence \<open>\<forall>e>0. \<exists> x\<in>(sphere 0 1).
      norm (norm(((*\<^sub>v) (f n)) x) - (onorm ((*\<^sub>v) (f n)))) < e\<close>
    for n
    using norm_unit_sphere[where f = "Blinfun (f n)"]
    by (simp add: blinfun_apply_inverse norm_blinfun.rep_eq)
  moreover have \<open>norm (f n) = onorm (blinfun_apply (f n))\<close> 
    for n
    by (simp add: norm_blinfun.rep_eq)
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
  fixes f::\<open>nat \<Rightarrow> nat \<Rightarrow> 'a::{real_normed_vector,not_singleton} \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
    and N M::hypnat 
  assumes \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close> 
  shows \<open>\<exists> x \<in> *s* (sphere 0 1). 
    hnorm ((*f2* f) N M) \<approx> hnorm ( (*f3* (\<lambda> n m. (*\<^sub>v) (f n m))) N M x )\<close>
proof-
  have \<open>bounded_linear (blinfun_apply (f n m))\<close>
    for n m
    using blinfun_apply by blast
  hence \<open>e>0 \<Longrightarrow> \<exists> x\<in>(sphere 0 1).
      norm (norm((blinfun_apply (f n m)) x) - (onorm (blinfun_apply (f n m)))) < e\<close>
    for n m e
    using norm_unit_sphere[where f = "f n m"]
    by (simp add: norm_blinfun.rep_eq)     
  moreover have \<open>norm (f n m) = onorm (blinfun_apply (f n m))\<close> 
    for n m
    by (simp add: norm_blinfun.rep_eq)
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
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector,not_singleton},'b::real_normed_vector) blinfun\<close>
    and N M::hypnat
  assumes \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close>
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

  have \<open>\<forall> N M. norm (( (\<lambda>n m. f n - f m)) N M) =
    norm (( f) N - ( f) M)\<close>
    by blast
  hence \<open>\<forall> N M. hnorm ((*f2* (\<lambda>n m. f n - f m)) N M) =
    hnorm ((*f* f) N - (*f* f) M)\<close>
    by StarDef.transfer  
  hence u1: \<open>\<forall> N M. hnorm ((*f2* g) N M) = hnorm ( (*f* f) N - (*f* f) M )\<close>
    unfolding g_def by blast

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
  hence u2: \<open>\<forall> N M x. hnorm ( (*f3* (\<lambda> n m. blinfun_apply (g n m))) N M x )
      = hnorm( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f2* (\<lambda> n. blinfun_apply (f n))) M x )\<close>
    unfolding g_def
    by simp 
  thus ?thesis using \<open>x \<in> *s* (sphere 0 1)\<close> 
      \<open>hnorm ((*f2* g) N M) \<approx> hnorm ( (*f3* (\<lambda> n m. blinfun_apply (g n m))) N M x )\<close>
    using u1 by auto    
qed

lemma ustrong_onorm:
  fixes f::"nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector"
    and l::"'a \<Rightarrow>\<^sub>L 'b"
  assumes \<open>sphere 0 1: (\<lambda> n. (*\<^sub>v) (f n)) \<midarrow>uniformly\<rightarrow> ((*\<^sub>v) l)\<close>
  shows \<open>f \<longlonglongrightarrow> l\<close> 
proof (cases \<open>(UNIV::'a set) = 0\<close>)
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
  have s1: \<open>(*f* f) N \<approx> (star_of l)\<close>
    if "N\<in>HNatInfinite"
    for N::hypnat
  proof-
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
    hence u1: \<open>x \<in> *s* (sphere 0 1) \<Longrightarrow> 
      hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x ) \<in> Infinitesimal\<close>
      for x::\<open>'a star\<close>
      by (simp add: Infinitesimal_hnorm_iff)
    define g where \<open>g n = f n - l\<close> for n
    note hnorm_unit_sphere' = hnorm_unit_sphere[
        where 'a="'z::{not_singleton,real_normed_vector}",
          rule_format,
          internalize_sort "'z::{not_singleton,real_normed_vector}"]

    have t1: "class.not_singleton (TYPE('a)::'a itself)"
      using False unfolding set_zero by (rule class_not_singletonI_monoid_add)          
    have t2: "class.real_normed_vector (-) dist norm (+) (0::'a) uminus (*\<^sub>R) sgn uniformity open"
      by (rule real_normed_vector_class.real_normed_vector_axioms)
    have q1: \<open>\<exists>x \<in> *s* (sphere 0 1). 
        hnorm ((*f* g) N) \<approx> hnorm ( (*f2* (\<lambda> n. blinfun_apply (g n))) N x )\<close>
      (* The attributes to hnorm_unit_sphere remove the sort from variable 'a in hnorm_unit_sphere.
          This is needed because 'a has sort not_singleton there that we don't have *)
      apply  (rule hnorm_unit_sphere [where 'a = "'z::{not_singleton,real_normed_vector}", 
            rule_format, internalize_sort "'z::{not_singleton,real_normed_vector}"])
      using t1 t2 that by auto    
    have  \<open>\<forall> NN. ( g) NN = ( f) NN - ( l)\<close>
      unfolding g_def by auto
    hence  \<open>\<forall> NN. (*f* g) NN = (*f* f) NN - (star_of l)\<close>
      by StarDef.transfer
    hence q2: \<open>(*f* g) N \<approx> (*f* f) N - (star_of l)\<close>
      by auto

    have q3: \<open>(*f2* (\<lambda> n. blinfun_apply (g n))) N x
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
    have \<open>\<exists> x\<in> *s* (sphere 0 1). hnorm ((*f* f) N - (star_of l)) \<approx>
        hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )\<close>
      using q1 q2 q3
      by (metis (no_types, lifting) approx_hnorm approx_trans3)
    hence u2: \<open>\<exists> x\<in> *s* (sphere 0 1). hnorm ((*f* f) N - (star_of l)) \<approx>
        hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )\<close>
      by simp
    have \<open>hnorm ((*f* f) N - (star_of l)) \<in> Infinitesimal\<close>
      using approx_trans mem_infmal_iff u1 u2  by blast
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
  have  \<open>(*f2* (\<lambda> n. blinfun_apply (f n))) N x \<approx> (*f2* (\<lambda> n. blinfun_apply (f n))) M x\<close>
    if \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close> and \<open>x\<in>*s* (sphere 0 1)\<close>
    for N M x
  proof- 
    from \<open>Cauchy f\<close>
    have \<open>NSCauchy f\<close>
      by (simp add: NSCauchy_Cauchy_iff)
    hence \<open>(*f* f) N \<approx> (*f* f) M\<close>
      unfolding NSCauchy_def
      using \<open>N\<in>HNatInfinite\<close> \<open>M\<in>HNatInfinite\<close>
      by blast
    hence \<open>(*f* f) N - (*f* f) M \<in> Infinitesimal\<close>
      using bex_Infinitesimal_iff by blast
    hence x1: \<open>hnorm ((*f* f) N - (*f* f) M) \<in> Infinitesimal\<close>
      by (simp add: Infinitesimal_hnorm_iff)

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
    hence z1: \<open>\<forall> NN MM xx. hnorm xx = 1 \<longrightarrow> hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) NN xx
                                 - (*f2* (\<lambda> n. blinfun_apply (f n))) MM xx )
        \<le> hnorm ((*f* f) NN - (*f* f) MM)\<close>
      by StarDef.transfer

    have \<open>\<forall> xx::'a. xx \<in> (sphere 0 1) \<longrightarrow> norm xx = 1\<close>
      by auto
    hence \<open>\<forall> xx::'a star. xx \<in> *s* (sphere 0 1) \<longrightarrow> hnorm xx = 1\<close>
      by StarDef.transfer
    hence \<open>hnorm x = 1\<close>
      using \<open>x \<in> *s* (sphere 0 1)\<close>
      by blast        
    hence x2: \<open>hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x
               - (*f2* (\<lambda> n. blinfun_apply (f n))) M x )
        \<le> hnorm ((*f* f) N - (*f* f) M)\<close>
      using z1 by blast     
    have \<open>norm ( ( (\<lambda> n. blinfun_apply (f n))) NN xx - ( (\<lambda> n. blinfun_apply (f n))) MM xx ) \<ge> 0\<close>
      for NN MM xx
      by auto
    hence x3: \<open>hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f2* (\<lambda> n. blinfun_apply (f n))) M x ) \<ge> 0\<close>
      by simp    
    have \<open>hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f2* (\<lambda> n. blinfun_apply (f n))) M x ) \<in> Infinitesimal\<close>
      using Infinitesimal_interval2 x1 x2 x3 by blast
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
  have \<open>(*f* f) N \<approx> (*f* f) M\<close>
    if \<open>N \<in> HNatInfinite\<close> and \<open>M \<in> HNatInfinite\<close>
    for N M
  proof-
    have \<open>x \<in>*s* (sphere 0 1) \<Longrightarrow> 
      (*f2* (\<lambda> n. blinfun_apply (f n))) N x \<approx> (*f2* (\<lambda> n. blinfun_apply (f n))) M x\<close>
      for x
      using \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. blinfun_apply (f n))\<close>
      by (simp add: \<open>M \<in> HNatInfinite\<close> \<open>N \<in> HNatInfinite\<close> nsuniformly_Cauchy_on_iff)    
    hence n1: \<open>x \<in>*s* (sphere 0 1) \<Longrightarrow> 
      hnorm( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f2* (\<lambda> n. blinfun_apply (f n))) M x ) \<in> Infinitesimal\<close>
      for x
      using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by blast    
    have m1: "class.not_singleton (TYPE('a)::'a itself)"
      using False unfolding set_zero by (rule class_not_singletonI_monoid_add)        
    have m2: "class.real_normed_vector (-) dist norm (+) (0::'a) uminus (*\<^sub>R) sgn uniformity open"
      by (rule real_normed_vector_class.real_normed_vector_axioms)
    have n2: \<open>\<exists>x\<in>*s* (sphere 0 1). hnorm ( (*f* f) N - (*f* f) M )
         \<approx> hnorm( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f2* (\<lambda> n. blinfun_apply (f n))) M x )\<close>
      (* The attributes to hnorm_unit_sphere remove the sort from variable 'a in hnorm_unit_sphere.
           This is needed because 'a has sort not_singleton there that we don't have *)
      apply  (rule uCauchy_unit_sphere [where 'a = "'z::{not_singleton,real_normed_vector}" , rule_format , internalize_sort "'z::{not_singleton,real_normed_vector}" , where M = M and N = N and f = f])
      using m1 m2 that by auto
    have \<open>hnorm ( (*f* f) N - (*f* f) M ) \<in> Infinitesimal\<close>
      using n1 n2 approx_sym approx_trans3 mem_infmal_iff by blast
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
  shows \<open>\<exists>l::'a \<Rightarrow>\<^sub>L 'b. 
    (sphere 0 1): (\<lambda> n. (*\<^sub>v) (f n)) \<midarrow>uniformly\<rightarrow> (*\<^sub>v) l\<close>
proof-
  include nsa_notation
  from \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. blinfun_apply (f n))\<close>
  have \<open>\<exists>s::'a\<Rightarrow>'b.
 (sphere 0 1): (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
    using uniformly_convergent_eq_Cauchy uniformly_convergent_on_def by blast
  then obtain s::\<open>'a\<Rightarrow>'b\<close> where
    \<open>(sphere 0 1): (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
    by blast
  define l::\<open>'a \<Rightarrow> 'b\<close> where \<open>l x = (norm x) *\<^sub>R s ((inverse (norm x)) *\<^sub>R x)\<close>
    for x::'a       
  have \<open>(\<lambda>x. norm x *\<^sub>R s (x /\<^sub>R norm x)) t = s t\<close>
    if "t \<in> sphere 0 1"
    for t
    unfolding sphere_def using that
    by simp
  hence \<open>sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> l\<close>
    using  \<open>sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
    unfolding l_def 
    by (metis (no_types, lifting) uniform_limit_cong') 
  hence \<open>x \<in> sphere 0 1 \<Longrightarrow> l x = s x\<close>
    for x
    using  \<open>sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
    by (meson LIMSEQ_unique tendsto_uniform_limitI)
  have \<open>\<And>n. bounded_linear (blinfun_apply (f n))\<close>
    using blinfun_apply by blast
  have \<open>(\<lambda> n. blinfun_apply (f n) x) \<longlonglongrightarrow> l x\<close>
    for x
  proof(cases \<open>x = 0\<close>)
    case True
    have \<open>\<And> n. bounded_linear (blinfun_apply (f n))\<close>
      using blinfun_apply by blast 
    hence \<open>blinfun_apply (f n) x = (0::'b)\<close>
      for n
      by (simp add: True linear_simps(3)) 
    moreover  have \<open>(\<lambda> n. (0::'b)) \<longlonglongrightarrow> 0\<close>
      by simp            
    ultimately have \<open>(\<lambda> n. blinfun_apply (f n) x) \<longlonglongrightarrow> 0\<close>
      by simp
    have \<open>norm x = 0\<close>
      using \<open>x = 0\<close> by simp
    hence \<open>l x = 0\<close>
      using l_def by simp
    thus ?thesis
      by (simp add: \<open>(\<lambda>n. f n *\<^sub>v x) \<longlonglongrightarrow> 0\<close>)
  next
    case False
    hence  \<open>norm x \<noteq> 0\<close> by simp
    have p1: \<open>\<forall>N\<in>HNatInfinite. \<forall>x\<in>*s* (sphere 0 1).
                     (*f2* (\<lambda> n. blinfun_apply (f n))) N x \<approx> (*f* s) x\<close>
      using \<open>sphere 0 1: (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close> nsuniform_convergence_D 
      by blast

    have \<open>norm (x  /\<^sub>R norm x) = 1\<close>
      by (simp add: False)
    hence \<open>(x  /\<^sub>R norm x) \<in> (sphere 0 1)\<close>
      unfolding sphere_def by auto    
    hence p2: \<open>star_of (x /\<^sub>R norm x) \<in> *s* (sphere 0 1)\<close>
      by (meson starset_mem)                

    have z1: \<open>\<forall> N\<in>HNatInfinite.
     (*f2* (\<lambda> n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x)) \<approx> (*f* s) (star_of (x /\<^sub>R norm x))\<close>
      using p1 p2 by auto
    have  \<open>\<forall> N. ( (\<lambda> n. blinfun_apply (f n))) N ( (x /\<^sub>R norm x))
                        = ( (\<lambda> n. blinfun_apply (f n) (x /\<^sub>R norm x) )) N\<close>
      by blast
    hence \<open>\<forall> N. (*f2* (\<lambda> n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x))
                        = (*f* (\<lambda> n. blinfun_apply (f n) (x /\<^sub>R norm x) )) N\<close>
      by StarDef.transfer
    hence z2: \<open>\<forall> N. (*f2* (\<lambda> n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x))
                        \<approx> (*f* (\<lambda> n. blinfun_apply (f n) (x /\<^sub>R norm x) )) N\<close>
      by simp
    have  \<open>\<forall> N\<in>HNatInfinite.
               (*f* (\<lambda> n. blinfun_apply (f n) (x /\<^sub>R norm x) )) N \<approx> (*f* s) (star_of (x /\<^sub>R norm x))\<close>
      using approx_trans3 using z1 z2
      by blast 
    hence \<open> (\<lambda>n. blinfun_apply (f n)  (x /\<^sub>R norm x)) \<longlonglongrightarrow>\<^sub>N\<^sub>S s  (x /\<^sub>R norm x)\<close>
      using NSLIMSEQ_def
      by (metis starfun_eq)              
    hence  \<open>(\<lambda> n. (blinfun_apply (f n)) (x  /\<^sub>R norm x)) \<longlonglongrightarrow> s (x /\<^sub>R norm x)\<close>
      by (simp add: NSLIMSEQ_LIMSEQ)
    hence  \<open>(\<lambda> n. (norm x) *\<^sub>R (blinfun_apply (f n)) (x /\<^sub>R norm x)) 
                  \<longlonglongrightarrow>  (norm x) *\<^sub>R  s (x /\<^sub>R norm x)\<close>
      using bounded_linear.tendsto bounded_linear_scaleR_right by blast
    hence  \<open>(\<lambda> n. (norm x) *\<^sub>R (blinfun_apply (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
      using l_def
      by simp
    have \<open>(norm x) *\<^sub>R (blinfun_apply (f n)) (x /\<^sub>R norm x) = (blinfun_apply (f n)) x\<close>
      for n
      using \<open>norm x \<noteq> 0\<close> \<open>\<And> n. bounded_linear (blinfun_apply (f n))\<close>
      unfolding cbounded_linear_def linear_def
      by (simp add: \<open>\<And>n. bounded_linear (blinfun_apply (f n))\<close> linear_simps(5))
    hence  \<open>(\<lambda> n. (blinfun_apply(f n)) x) \<longlonglongrightarrow> l x\<close>
      using  \<open>(\<lambda> n. (norm x) *\<^sub>R (blinfun_apply (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close> 
      by simp
    thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R (blinfun_apply (f n)) (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
      by auto
  qed

  have plus: "l (b1 + b2) = l b1 + l b2"
    for b1 :: 'a
      and b2 :: 'a
  proof-
    have u1: \<open>(\<lambda> n. (blinfun_apply (f n)) (b1 + b2)) \<longlonglongrightarrow> l (b1 + b2)\<close>
      using  \<open>\<And> x. (\<lambda> n. (blinfun_apply (f n)) x) \<longlonglongrightarrow> l x\<close>
      by blast
    have \<open>(\<lambda> n. (blinfun_apply (f n))  b1) \<longlonglongrightarrow> l b1\<close>
      using  \<open>\<And> x. (\<lambda> n. (blinfun_apply (f n))  x) \<longlonglongrightarrow> l x\<close>
      by blast
    moreover have \<open>(\<lambda> n. (blinfun_apply (f n))  b2) \<longlonglongrightarrow> l b2\<close>
      using  \<open>\<And> x. (\<lambda> n.  (blinfun_apply (f n))  x) \<longlonglongrightarrow> l x\<close>
      by blast
    ultimately have v3:\<open>(\<lambda> n. (blinfun_apply (f n))  b1 + (blinfun_apply (f n))  b2)
                                   \<longlonglongrightarrow> l b1 + l b2\<close>
      by (simp add: tendsto_add) 
    have v2: \<open>(blinfun_apply (f n))  (b1 + b2) 
                        = (blinfun_apply (f n))  b1 + (blinfun_apply (f n))  b2\<close>
      for n
      using \<open>\<And> n. bounded_linear  (blinfun_apply (f n))\<close>
      unfolding bounded_linear_def
      by (simp add: real_vector.linear_add)
    hence v1: \<open>(\<lambda> n.  (blinfun_apply (f n))  (b1 + b2)) 
                      = (\<lambda> n.  (blinfun_apply (f n))  b1 +  (blinfun_apply (f n))  b2)\<close>
      using v3 by auto
    hence u2: \<open>(\<lambda> n. (blinfun_apply (f n)) (b1 + b2)) \<longlonglongrightarrow> l b1 + l b2\<close>
      using v1 v2 v3
      by simp
    show ?thesis
      using u1 u2 LIMSEQ_unique by blast            
  qed
  have scale: "l (r *\<^sub>R b) = r *\<^sub>R l b"
    for r :: real
      and b :: 'a
  proof-
    have s1: \<open>(\<lambda> n.  (blinfun_apply (f n))  (r *\<^sub>R b)) \<longlonglongrightarrow> l (r *\<^sub>R b)\<close>
      using  \<open>\<And> x. (\<lambda> n.  (blinfun_apply (f n))  x) \<longlonglongrightarrow> l x\<close>
      by blast
    have r1: \<open>(\<lambda> n.  (blinfun_apply (f n))  b) \<longlonglongrightarrow> l b\<close>
      using  \<open>\<And> x. (\<lambda> n.  (blinfun_apply (f n))  x) \<longlonglongrightarrow> l x\<close>
      by blast
    hence r2: \<open>(\<lambda> n. r *\<^sub>R ( (blinfun_apply (f n))  b)) \<longlonglongrightarrow> r *\<^sub>R (l b)\<close>
      using bounded_linear.tendsto bounded_linear_scaleR_right by blast
    have \<open> (blinfun_apply (f n))  (r *\<^sub>R b) = r *\<^sub>R ( (blinfun_apply (f n))  b)\<close>
      for n
      using \<open>\<And> n. bounded_linear (blinfun_apply (f n))\<close>
      unfolding bounded_linear_def
      by (simp add: real_vector.linear_scale)
    hence r3: \<open>(\<lambda> n. ( (blinfun_apply (f n))  (r *\<^sub>R b))) = (\<lambda> n. r *\<^sub>R ( (blinfun_apply (f n))  b))\<close>
      by blast
    have s2: \<open>(\<lambda> n.  (blinfun_apply (f n))  (r *\<^sub>R b)) \<longlonglongrightarrow>  r *\<^sub>R (l b)\<close>
      using r2 r3 by auto
    show ?thesis
      using s1 s2 LIMSEQ_unique by blast            
  qed
  have bound: \<open>\<exists>K. \<forall>x. norm (l x) \<le> norm x * K\<close>
  proof(rule classical)
    assume \<open>\<not> (\<exists>K. \<forall>x. norm (l x) \<le> norm x * K)\<close>
    hence \<open>\<forall>K. \<exists> x. norm (l x) > norm x * K\<close>
      by smt
    hence \<open>\<forall>K. \<exists> x \<noteq> 0. norm (l x) > norm x * K\<close>
      using plus scale dual_order.strict_iff_order mult_zero_left norm_zero           
      by (metis real_vector.scale_zero_left)
    have \<open>\<exists>x. norm x = 1 \<and> K < norm (l x)\<close>
      for K
    proof-
      have \<open>\<exists> x \<noteq> 0. norm (l x) > norm x * K\<close>
        using  \<open>\<forall> K. \<exists> x \<noteq> 0. norm (l x) > norm x * K\<close> by blast
      then obtain x where \<open>x \<noteq> 0\<close> and \<open>norm (l x) > norm x * K\<close>
        by blast
      have \<open>norm x > 0\<close> using \<open>x \<noteq> 0\<close> by simp
      hence  \<open>inverse (norm x) * norm (l x) > inverse (norm x) * (norm x) * K\<close>
        using  \<open>norm (l x) > norm x * K\<close>
        by (smt linordered_field_class.positive_imp_inverse_positive mult.assoc 
            mult_left_le_imp_le)
      moreover have \<open>(inverse (norm x)) * (norm x) = 1\<close>
        using \<open>norm x > 0\<close> by simp
      ultimately have \<open>(inverse (norm x)) * norm (l x) >  K\<close>
        by simp
      have \<open>(inverse (norm x)) > 0\<close>
        using \<open>norm x > 0\<close> 
        by simp
      hence \<open>(inverse (norm x)) * norm (l x) = norm ((inverse (norm x)) *\<^sub>R (l x))\<close>
        using norm_scaleR
        by simp 
      hence \<open>norm ((inverse (norm x)) *\<^sub>R (l x)) >  K\<close>
        using \<open>K < inverse (norm x) * norm (l x)\<close> by linarith        
      have \<open>(inverse (norm x)) *\<^sub>R (l x) = l ((inverse (norm x)) *\<^sub>R  x)\<close>
        using plus scale linear_scale
        by (simp add: real_vector.linear_scale)
      hence \<open>norm (l ((inverse (norm x)) *\<^sub>R  x)) >  K\<close>
        using \<open>K < norm (l x /\<^sub>R norm x)\<close> by simp                 
      have \<open>norm ( (inverse (norm x)) *\<^sub>R  x ) = 1\<close>
        using \<open>norm x > 0\<close> by simp
      show ?thesis
        using \<open>K < norm (l (x /\<^sub>R norm x))\<close> \<open>norm (x /\<^sub>R norm x) = 1\<close> by blast 
    qed
    hence \<open>\<forall>K. \<exists> x. norm x = 1 \<and> K < norm (l x)\<close>
      by simp
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
    hence d1: \<open>m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm ((blinfun_apply (f m)) x) < onorm (blinfun_apply (f M)) + 1\<close>
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
    hence \<open>norm (l x) \<le> onorm (blinfun_apply (f M)) + 1\<close>
      if t1: \<open>norm x = 1\<close>
      for x
    proof-
      have \<open>(\<lambda> m. norm ((blinfun_apply (f m)) x)) \<longlonglongrightarrow> norm (l x)\<close>
        using t1  \<open>\<And> x. norm x = 1 \<Longrightarrow> (\<lambda> m. norm ((blinfun_apply (f m)) x)) \<longlonglongrightarrow> norm (l x)\<close>
        by blast
      moreover have \<open>\<forall>  m \<ge> M. norm ((blinfun_apply (f m)) x) \<le> onorm (blinfun_apply (f M)) + 1\<close>
        using  d1 \<open>norm x = 1\<close> by smt
      ultimately show ?thesis 
        by (rule Topological_Spaces.Lim_bounded)
    qed
    moreover have  \<open>\<exists>x. norm x = 1 \<and> onorm (blinfun_apply (f M)) + 1 < norm (l x)\<close>
      by (simp add: \<open>\<forall>K. \<exists>x. norm x = 1 \<and> K < norm (l x)\<close>)
    ultimately show ?thesis
      by fastforce 
  qed
  hence \<open>bounded_linear_axioms l\<close> unfolding bounded_linear_axioms_def 
    by blast
  hence \<open>bounded_linear l\<close>
    unfolding bounded_linear_def
    using plus scale linearI by metis 
  hence \<open>\<exists> L. blinfun_apply L = l\<close>
    using blinfun_apply_cases by auto
  hence \<open>\<exists>L. \<forall> x\<in>(sphere 0 1). blinfun_apply L x = s x\<close>
    using \<open>\<And>x. x \<in> sphere 0 1 \<Longrightarrow> l x = s x\<close> 
    by blast
  then obtain L::\<open>'a \<Rightarrow>\<^sub>L'b\<close> where L_def: \<open>\<forall>x\<in>(sphere 0 1).  L *\<^sub>v x = s x\<close>
    by blast
  have "sphere 0 1: (\<lambda>n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> blinfun_apply L"
    using L_def \<open>(sphere 0 1): (\<lambda> n. blinfun_apply (f n)) \<midarrow>uniformly\<rightarrow> s\<close>
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
  have \<open>(*f2* (\<lambda> n. blinfun_apply (f n))) N x \<approx> (*f* (blinfun_apply l)) x\<close>
    if \<open>N\<in>HNatInfinite\<close> and \<open>x \<in> *s* (sphere 0 1)\<close>
    for N and x
  proof-
    have \<open>(*f* f) N \<approx> (star_of l)\<close>
      using \<open>f \<longlonglongrightarrow> l\<close> \<open>N\<in>HNatInfinite\<close>
      by (simp add: LIMSEQ_NSLIMSEQ_iff NSLIMSEQ_D)
    hence y0: \<open>hnorm ( (*f* f) N - (star_of l) ) \<in> Infinitesimal\<close>
      using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by auto
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
    ultimately have \<open>norm (blinfun_apply (f N) x - blinfun_apply l x)
           \<le> onorm (blinfun_apply (f N - l))\<close>
      if "norm x = 1"
      for N x
      using that
      by simp
    hence \<open>\<forall>N. \<forall>x. x \<in> (sphere 0 1) \<longrightarrow> 
         norm ( (\<lambda>n. blinfun_apply (f n)) N x - blinfun_apply l x )
                \<le> norm ( f N - l )\<close>
      unfolding norm_blinfun_def
      by auto
    hence \<open>\<forall>N. \<forall>x. x \<in> *s* (sphere 0 1) \<longrightarrow> 
         hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )
                \<le> hnorm ( (*f* f) N - (star_of l) )\<close>
      by StarDef.transfer
    hence y1: \<open>hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )
                \<le> hnorm ( (*f* f) N - (star_of l) )\<close>
      using \<open>x\<in>*s* (sphere 0 1)\<close> by blast
    have y2: \<open>0 \<le> hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )\<close>
      by simp      
    have \<open>hnorm ( (*f2* (\<lambda> n. blinfun_apply (f n))) N x - (*f* (blinfun_apply l)) x )
            \<in> Infinitesimal\<close>
      using Infinitesimal_interval2 y0 y1 y2 by blast 
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
  have  \<open>\<And>n. bounded_linear (blinfun_apply (f n))\<close>
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
  have \<open>(*f* (\<lambda>n. (blinfun_apply (f n)) x)) N \<approx> star_of ((blinfun_apply l) x)\<close>
    if \<open>N\<in>HNatInfinite\<close>
    for N
  proof(cases \<open>x = 0\<close>)
    case True
    have \<open>bounded_linear (blinfun_apply (f n))\<close>
      for n
      using blinfun_apply by blast
    hence c1: \<open>(f n) *\<^sub>v x = 0\<close>
      for n
      by (simp add: True)    
    have \<open>bounded_linear (blinfun_apply l)\<close>
      using blinfun_apply by blast
    hence c2: \<open>(blinfun_apply l) x = 0\<close>
      by (simp add: True)    
    have \<open>(blinfun_apply (f n)) x = (blinfun_apply l) x\<close>
      for n
      using c1 c2
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
    hence c1: \<open>t \<in> *s*(sphere 0 1) \<Longrightarrow> (*f2* (\<lambda>n. blinfun_apply (f n))) N t \<approx> (*f* (blinfun_apply l)) t\<close>
      for t
      using \<open>N \<in> HNatInfinite\<close> nsupointwise_convergence_D sphere_iff by blast
    have \<open>(x /\<^sub>R norm x) \<in> (sphere 0 1)\<close>
      using False unfolding sphere_def by auto    
    hence c2: \<open>star_of (x /\<^sub>R norm x) \<in> *s*(sphere 0 1)\<close>
      by StarDef.transfer
    have \<open>(*f2* (\<lambda>n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x)) 
          \<approx> (*f* (blinfun_apply l)) (star_of (x /\<^sub>R norm x))\<close>
      using c1 c2 by auto
    hence d1: \<open>(*f2* scaleR) (star_of (norm x)) 
          ( (*f2* (\<lambda>n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x)) ) 
          \<approx> (*f2* scaleR) (star_of (norm x)) ( (*f* (blinfun_apply l)) (star_of (x /\<^sub>R norm x)) )\<close>
      using approx_scaleR2 star_scaleR_def starfun2_star_of
      by metis
    have \<open>bounded_linear (blinfun_apply (f n))\<close>
      for n
      using blinfun_apply by auto          
    hence \<open>\<forall>N. ( scaleR) ( (norm x)) ( ( (\<lambda>n. blinfun_apply (f n))) N ( (x /\<^sub>R norm x)) )
          = ( (\<lambda>n. blinfun_apply (f n) x)) N\<close>
      by (simp add: False blinfun.scaleR_right)      
    hence  \<open>\<forall> N. (*f2* scaleR) (star_of (norm x)) ( (*f2* (\<lambda>n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x)) )
          = (*f* (\<lambda>n. blinfun_apply (f n) x)) N\<close>
      by StarDef.transfer    
    hence d2: \<open>(*f2* scaleR) (star_of (norm x)) ( (*f2* (\<lambda>n. blinfun_apply (f n))) N (star_of (x /\<^sub>R norm x)) )
          = (*f* (\<lambda>n. blinfun_apply (f n) x)) N\<close>
      by auto
    have \<open>bounded_linear (blinfun_apply l)\<close>
      using blinfun_apply by auto          
    hence \<open>( scaleR) ( (norm x)) ( ( (blinfun_apply l)) ( (x /\<^sub>R norm x)) )
            =  (blinfun_apply l x)\<close>
      by (metis blinfun.scaleR_right div_self divide_real_def norm_eq_zero pth_1 pth_4(1) pth_5)
    hence d3: \<open>(*f2* scaleR) (star_of (norm x)) ( (*f* (blinfun_apply l)) (star_of (x /\<^sub>R norm x)) )
            = star_of (blinfun_apply l x)\<close> 
      by StarDef.transfer
    show ?thesis
      using d1 d2 d3 by auto 
  qed
  hence  \<open>(\<lambda>n. (blinfun_apply (f n)) x) \<longlonglongrightarrow>\<^sub>N\<^sub>S (blinfun_apply l) x\<close>
    by (simp add: NSLIMSEQ_I)
  thus ?thesis
    by (simp add: NSLIMSEQ_LIMSEQ)
qed

lemma times_blinfun_assoc: "(A o\<^sub>L B)  o\<^sub>L C = A  o\<^sub>L (B  o\<^sub>L C)" 
proof transfer
  show "A \<circ> B \<circ> C = A \<circ> (B \<circ> C)"
    if "bounded_linear A"
      and "bounded_linear B"
      and "bounded_linear C"
    for A :: "'d \<Rightarrow> 'b"
      and B :: "'c \<Rightarrow> 'd"
      and C :: "'a \<Rightarrow> 'c"
    using that by (simp add: comp_assoc)
qed


lemma times_blinfun_dist1:
  fixes a b :: "'b::real_normed_vector \<Rightarrow>\<^sub>L 'c::real_normed_vector"
    and c :: "'a::real_normed_vector \<Rightarrow>\<^sub>L 'b"
  shows "(a + b) o\<^sub>L c = (a o\<^sub>L c) + (b o\<^sub>L c)"
  by (simp add: blinfun.add_left blinfun_eqI)

lemma times_blinfun_dist2:
  fixes a b :: "'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector"
    and c :: "'b  \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  shows "c o\<^sub>L (a + b) = (c o\<^sub>L a) + (c o\<^sub>L b)"
proof-
  have z1: \<open>bounded_linear (blinfun_apply c)\<close>
    using blinfun_apply by auto

  have \<open>(c  o\<^sub>L (a + b)) *\<^sub>v x = ( (c  o\<^sub>L a) +  (c  o\<^sub>L b) ) *\<^sub>v x\<close>
    for x
  proof-
    have \<open>blinfun_apply (c  o\<^sub>L (a + b)) x = (blinfun_apply c) ( (blinfun_apply (a + b)) x )\<close>
      by simp
    also have \<open>\<dots> = (blinfun_apply c) ( blinfun_apply a x + blinfun_apply b x )\<close>
      by (simp add: plus_blinfun.rep_eq)
    also have \<open>\<dots> = (blinfun_apply c) ( blinfun_apply a x ) + (blinfun_apply c) ( blinfun_apply b x )\<close>
      using  \<open>bounded_linear (blinfun_apply c)\<close>
      unfolding cbounded_linear_def linear_def
      by (simp add: z1 linear_simps(1))
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
  shows \<open>(a *\<^sub>C A) o\<^sub>L B = a *\<^sub>C (A o\<^sub>L B)\<close>
proof-
  have \<open>(blinfun_apply (a *\<^sub>C A) \<circ> blinfun_apply B) x =
    blinfun_apply (a *\<^sub>C Blinfun (blinfun_apply A \<circ> blinfun_apply B)) x\<close>
    for x
  proof-
    have y1: \<open>blinfun_apply A ((blinfun_apply B) x) = ((blinfun_apply A \<circ> blinfun_apply B)) x\<close>
      by simp
    have \<open>(blinfun_apply (a *\<^sub>C A) \<circ> blinfun_apply B) x
       = a *\<^sub>C (blinfun_apply A ((blinfun_apply B) x))\<close>
      by (simp add: scaleC_blinfun.rep_eq)
    moreover have \<open>blinfun_apply (a *\<^sub>C Blinfun (blinfun_apply A \<circ> blinfun_apply B)) x
        = a *\<^sub>C (blinfun_apply ( Blinfun (blinfun_apply A \<circ> blinfun_apply B)) x)\<close>
      by (simp add: scaleC_blinfun.rep_eq)
    moreover have \<open>(blinfun_apply A ((blinfun_apply B) x))
        = (blinfun_apply ( Blinfun (blinfun_apply A \<circ> blinfun_apply B)) x)\<close>
      using y1
      using Blinfun_inverse
      by (metis blinfun_apply blinfun_compose.rep_eq)        
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
  assumes \<open>\<And>c. \<And>x. A *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (A *\<^sub>v x)\<close>
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

(* TODO remove (confusing) *)
declare [[coercion
      "cblinfun_apply :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'b"]]

notation cblinfun_apply (infixr "*\<^sub>V" 70)

lift_definition blinfun_of_cblinfun::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector 
  \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b\<close> is "id"
proof transfer
  show "bounded_linear (id F)"
    if "cbounded_linear F"
    for F :: "'a \<Rightarrow> 'b"
    using that
    by (simp add: cbounded_linear.bounded_linear)
qed 



lemma blinfun_of_cblinfun_inj:
  \<open>blinfun_of_cblinfun f = blinfun_of_cblinfun g \<Longrightarrow> f = g\<close>
  by (metis cblinfun_apply_inject blinfun_of_cblinfun.rep_eq)

lemma blinfun_of_cblinfun_inv:
  assumes "\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)"
  shows "\<exists>g. blinfun_of_cblinfun g = f"
  using assms
proof transfer
  show "\<exists>g\<in>Collect cbounded_linear. id g = f"
    if "bounded_linear f"
      and "\<And>c x. f (c *\<^sub>C x) = c *\<^sub>C f x"
    for f :: "'a \<Rightarrow> 'b"
    using that bounded_linear_cbounded_linear by auto 
qed  

lemma blinfun_of_cblinfun_inv_uniq:
  assumes "\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)"
  shows  \<open>\<exists>! g. blinfun_of_cblinfun g = f\<close>
  using assms blinfun_of_cblinfun_inv blinfun_of_cblinfun_inj
  by blast


lemma blinfun_of_cblinfun_prelim:
  fixes c and x
  shows \<open>(blinfun_of_cblinfun g) *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C ((blinfun_of_cblinfun g) *\<^sub>v x)\<close>
proof transfer
  show "id g (c *\<^sub>C x) = c *\<^sub>C (id g x)"
    if "cbounded_linear g"
    for g :: "'b \<Rightarrow> 'a"
      and c :: complex
      and x :: 'b
    using that 
    by (simp add: cbounded_linear_def complex_vector.linear_scale)
qed

definition cblinfun_of_blinfun::
  "'a::complex_normed_vector \<Rightarrow>\<^sub>L 'b::complex_normed_vector \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" 
  where "cblinfun_of_blinfun = inv blinfun_of_cblinfun"

lemma cblinfun_blinfun:
  \<open>cblinfun_of_blinfun (blinfun_of_cblinfun f) = f\<close>
  by (metis (no_types, hide_lams) cblinfun_apply_inverse UNIV_I cblinfun_of_blinfun_def f_inv_into_f image_iff blinfun_of_cblinfun.rep_eq)

lemma blinfun_cblinfun:
  assumes "\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)"
  shows \<open>blinfun_of_cblinfun (cblinfun_of_blinfun f) = f\<close>
  using assms
  by (metis blinfun_of_cblinfun_inv cblinfun_blinfun) 


instantiation cblinfun :: (complex_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
lift_definition zero_cblinfun::"'a \<Rightarrow>\<^sub>C\<^sub>L'b" is "\<lambda>_. 0" by simp

lemma cblinfun_of_blinfun_zero:
  "(0::('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector)) 
  = cblinfun_of_blinfun (0::('a \<Rightarrow>\<^sub>L'b))" 
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


lift_definition plus_cblinfun::"'a \<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L'b" is
  "\<lambda>f g x. f x + g x"
  by (rule cbounded_linear_add)


lemma cblinfun_of_blinfun_plus:
  assumes \<open>\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)\<close>
    and \<open>\<And>c. \<And>x. g *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (g *\<^sub>v x)\<close>
  shows \<open>cblinfun_of_blinfun (f + g) = cblinfun_of_blinfun f + cblinfun_of_blinfun g\<close>
  using assms
  by (smt blinfun_cblinfun blinfun_eqI blinfun_of_cblinfun.rep_eq blinfun_of_cblinfun_inj 
      plus_blinfun.rep_eq plus_cblinfun.rep_eq scaleC_add_right) 

lift_definition uminus_cblinfun::"'a \<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L'b" is
  "\<lambda>f x. - f x"
  by (rule cbounded_linear_minus)

lemma blinfun_of_cblinfun_uminus:
  \<open>blinfun_of_cblinfun (- f) = - (blinfun_of_cblinfun f)\<close>
  apply transfer
  by auto

lemma cblinfun_of_blinfun_uminus:
  assumes \<open>\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)\<close>
  shows  \<open>cblinfun_of_blinfun (- f) = - (cblinfun_of_blinfun f)\<close>
  using assms
  by (metis (mono_tags) blinfun_cblinfun blinfun_of_cblinfun_inj blinfun_of_cblinfun_prelim blinfun_of_cblinfun_uminus)

lift_definition minus_cblinfun::"('a,'b) cblinfun \<Rightarrow> ('a,'b) cblinfun \<Rightarrow> ('a,'b) cblinfun" is
  "\<lambda>f g x. f x - g x"
  by (rule cbounded_linear_sub)

lemma blinfun_of_cblinfun_minus:
  \<open>blinfun_of_cblinfun (f - g) = blinfun_of_cblinfun f - blinfun_of_cblinfun g\<close>
  apply transfer
  by auto

lemma cblinfun_of_blinfun_minus:
  assumes \<open>\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)\<close>
    and \<open>\<And>c. \<And>x. g *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (g *\<^sub>v x)\<close>
  shows \<open>cblinfun_of_blinfun (f - g) = cblinfun_of_blinfun f - cblinfun_of_blinfun g\<close>
  using assms
  unfolding cblinfun_of_blinfun_def inv_def
  by (smt cblinfun_blinfun blinfun_cblinfun blinfun_of_cblinfun_minus someI_ex)

lift_definition scaleC_cblinfun :: \<open>complex \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  is  "\<lambda> c f x. c *\<^sub>C (f x)"
  by (rule cbounded_linear_const_scaleC)


lemma blinfun_of_cblinfun_scaleC:
  \<open>blinfun_of_cblinfun ( c *\<^sub>C f ) = c *\<^sub>C (blinfun_of_cblinfun f)\<close>
  apply transfer
  by auto

lemma cblinfun_of_blinfun_scaleC:
  assumes \<open>\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)\<close>
  shows \<open>cblinfun_of_blinfun ( c *\<^sub>C f ) = c *\<^sub>C (cblinfun_of_blinfun f)\<close>
  using assms
  by (metis (mono_tags) cblinfun_blinfun blinfun_cblinfun blinfun_of_cblinfun_scaleC)

lift_definition scaleR_cblinfun :: \<open>real \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  is  "\<lambda> c f x. c *\<^sub>R (f x)"
  by (rule Complex_Vector_Spaces.scalarR_cbounded_linear)

lemma blinfun_of_cblinfun_scaleR:
  \<open>blinfun_of_cblinfun (c *\<^sub>R f) = c *\<^sub>R (blinfun_of_cblinfun f)\<close>
  apply transfer by auto

lemma cblinfun_of_blinfun_scaleR:
  assumes \<open>\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)\<close>
  shows \<open>cblinfun_of_blinfun ( c *\<^sub>R f ) = c *\<^sub>R (cblinfun_of_blinfun f)\<close>
  using assms
  by (metis (mono_tags) cblinfun_blinfun blinfun_cblinfun blinfun_of_cblinfun_scaleR)

lemma cblinfun_of_blinfun_Blinfun:
  \<open>cblinfun_of_blinfun ( Blinfun (cblinfun_apply f) ) = f\<close>
  by (metis Quotient_cblinfun Quotient_rel_rep cblinfun_apply_inverse cblinfun_blinfun blinfun_of_cblinfun.abs_eq)

lift_definition norm_cblinfun :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> real\<close>
  is onorm.

lemma blinfun_of_cblinfun_norm:
  fixes f::\<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  shows \<open>norm f = norm (blinfun_of_cblinfun f)\<close>
  apply transfer
  by auto

lift_definition dist_cblinfun :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. onorm (\<lambda> x. f x - g x)\<close>.

lemma blinfun_of_cblinfun_dist:
  fixes f::\<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  shows \<open>dist f g = dist (blinfun_of_cblinfun f) (blinfun_of_cblinfun g)\<close>
  unfolding dist_cblinfun_def dist_blinfun_def apply auto apply transfer
  by auto

definition sgn_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  where "sgn_cblinfun x = scaleR (inverse (norm x)) x"

lemma blinfun_of_cblinfun_sgn:
  \<open>blinfun_of_cblinfun (sgn f) = (sgn (blinfun_of_cblinfun f))\<close>
  by (simp add: sgn_cblinfun_def sgn_blinfun_def
      blinfun_of_cblinfun_scaleR blinfun_of_cblinfun_norm)

definition uniformity_cblinfun :: \<open>( ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<times> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) ) filter\<close>
  where \<open>uniformity_cblinfun = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a \<Rightarrow>\<^sub>C\<^sub>L 'b)) y < e})\<close>

definition open_cblinfun :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set \<Rightarrow> bool\<close>
  where \<open>open_cblinfun U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::('a \<Rightarrow>\<^sub>C\<^sub>L 'b)) = x \<longrightarrow> y \<in> U)\<close>

instance
proof
  show \<open>a + b + c = a + (b + c)\<close>
    for a b c :: "'a \<Rightarrow>\<^sub>C\<^sub>L'b"
  proof transfer
    show "(\<lambda>x. a x + b x + c x) = (\<lambda>x. a x + (b x + c x))"
      if "cbounded_linear a"
        and "cbounded_linear b"
        and "cbounded_linear c"
      for a b c :: "'a \<Rightarrow> 'b"
      using that
      by (simp add: ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(3)) 
  qed  

  show \<open>0 + a = a\<close>
    for a :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  proof transfer
    show "(\<lambda>x. 0 + a x) = a"
      if "cbounded_linear a"
      for a :: "'a \<Rightarrow> 'b" by auto      
  qed

  show \<open>a + b = b + a\<close>
    for a b :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"      
    by (simp add: add.commute plus_cblinfun_def)

  show \<open>- a + a = 0\<close>
    for a :: "('a, 'b) cblinfun"
  proof transfer
    show "(\<lambda>x. - a x + a x) = (\<lambda>_. 0)"
      if "cbounded_linear a"
      for a :: "'a \<Rightarrow> 'b"
      using that by auto
  qed

  show \<open>a - b = a + - b\<close>
    for a b :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"      
  proof transfer
    show "(\<lambda>x. a x - b x) = (\<lambda>x. a x + - b x)"
      if "cbounded_linear a"
        and "cbounded_linear b"
      for a b :: "'a \<Rightarrow> 'b"
      using that by auto
  qed

  show \<open>((*\<^sub>R) r::('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
    for r :: real
  proof-
    have \<open>r *\<^sub>R (f *\<^sub>V t) = complex_of_real r *\<^sub>C (f *\<^sub>V t)\<close>
      for f::\<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and t
      by (simp add: scaleR_scaleC)      
    hence \<open>(\<lambda>t. r *\<^sub>R (f *\<^sub>V t)) t = (\<lambda>t. complex_of_real r *\<^sub>C (f *\<^sub>V t)) t\<close>
      for f::\<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and t
      by simp      
    hence \<open>(\<lambda>t. r *\<^sub>R (f *\<^sub>V t)) = (\<lambda>t. complex_of_real r *\<^sub>C (f *\<^sub>V t))\<close>
      for f::\<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by simp
    hence \<open>cBlinfun (\<lambda>t. r *\<^sub>R (f *\<^sub>V t)) =
           cBlinfun (\<lambda>t. complex_of_real r *\<^sub>C (f *\<^sub>V t))\<close>
      for f::\<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by simp
    hence \<open>(\<lambda>f. cBlinfun (\<lambda>t. r *\<^sub>R (f *\<^sub>V t))) f =
           (\<lambda>f. cBlinfun (\<lambda>t. complex_of_real r *\<^sub>C (f *\<^sub>V t))) f\<close>
      for f::\<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
      by blast
    hence \<open>(\<lambda>f. cBlinfun (\<lambda>t. r *\<^sub>R cblinfun_apply f t)) =
    (\<lambda>f. cBlinfun (\<lambda>t. complex_of_real r *\<^sub>C cblinfun_apply f t))\<close>
      by (simp add: scaleR_scaleC)      
    thus ?thesis
      unfolding scaleR_cblinfun_def scaleC_cblinfun_def o_def blinfun_of_cblinfun_def map_fun_def
      by auto
  qed
  show \<open>a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    for a :: complex
      and x y :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    apply transfer
    by (simp add: scaleC_add_right) 

  show \<open>(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x\<close>
    for a :: complex
      and b :: complex
      and x :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  proof transfer
    show "(\<lambda>t. (a + b) *\<^sub>C (x t)) = (\<lambda>t. a *\<^sub>C x t + b *\<^sub>C x t)"
      if "cbounded_linear x"
      for a b :: complex
        and x :: "'a \<Rightarrow> 'b"
      using that
      by (simp add: scaleC_left.add) 
  qed


  show \<open>a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x\<close>
    for a b :: complex
      and x ::  "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    by (simp add: blinfun_of_cblinfun_inj blinfun_of_cblinfun_scaleC)

  show \<open>1 *\<^sub>C x = x\<close>
    for x ::  "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    by (simp add: blinfun_of_cblinfun_inj blinfun_of_cblinfun_scaleC)

  show \<open>dist x y = norm (x - y)\<close>
    for x y ::  "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    by (simp add: dist_norm blinfun_of_cblinfun_dist blinfun_of_cblinfun_minus blinfun_of_cblinfun_norm)

  show \<open>sgn x = (inverse (norm x)) *\<^sub>R x\<close>
    for x ::  "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    by (simp add: norm_cblinfun_def scaleR_cblinfun_def sgn_cblinfun_def sgn_div_norm)

  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a \<Rightarrow>\<^sub>C\<^sub>L 'b)) y < e})\<close>
    by (simp add: Bounded_Operators.uniformity_cblinfun_def)

  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::('a \<Rightarrow>\<^sub>C\<^sub>L 'b)) = x \<longrightarrow> y \<in> U)\<close>
    for U :: "('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set"
    by (simp add: Bounded_Operators.open_cblinfun_def)

  show \<open>(norm x = 0) = (x = 0)\<close>
    for x ::"'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  proof transfer
    show "(onorm x = 0) = (x = (\<lambda>_. 0))"
      if "cbounded_linear x"
      for x :: "'a \<Rightarrow> 'b"
      using that
      using cbounded_linear.bounded_linear onorm_eq_0 by auto 
  qed

  show \<open>norm (x + y) \<le> norm x + norm y\<close>
    for x y :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  proof transfer
    show "onorm (\<lambda>t. x t + y t) \<le> onorm x + onorm y"
      if h1: "cbounded_linear x" and h2: "cbounded_linear y"
      for x y :: "'a \<Rightarrow> 'b"      
    proof (rule Operator_Norm.onorm_triangle)
      show "bounded_linear x"
        using h1
        by (simp add: cbounded_linear.bounded_linear) 
      show "bounded_linear y"
        using h2
        by (simp add: cbounded_linear.bounded_linear) 
    qed
  qed

  show \<open>norm (a *\<^sub>C x) = cmod a * norm x\<close>
    for a :: complex
      and x :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    using blinfun_of_cblinfun_norm blinfun_of_cblinfun_scaleC by auto


  show \<open>norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x\<close>
    for a :: real
      and x :: "('a, 'b) cblinfun"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x a. norm (a *\<^sub>C x) = cmod a * norm (x::('a \<Rightarrow>\<^sub>C\<^sub>L 'b))\<close>
      of_real_mult
    by simp

  show \<open>a *\<^sub>R (x + y) = a *\<^sub>R x +  a *\<^sub>R y\<close>
    for a :: real
      and x y :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    using  \<open>\<And>r. ((*\<^sub>R) r::'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x y a. a *\<^sub>C (x + y) = a *\<^sub>C x +  a *\<^sub>C (y::'a \<Rightarrow>\<^sub>C\<^sub>L 'b)\<close> 
    by simp

  show \<open>(a + b) *\<^sub>R x = a *\<^sub>R x +  b *\<^sub>R x\<close>
    for a b :: real
      and x :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    using  \<open>\<And>r. ((*\<^sub>R) r::'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x b a. (a + b) *\<^sub>C (x::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = a *\<^sub>C x +  b *\<^sub>C x\<close>
      of_real_mult
    by simp

  show \<open>a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x\<close>
    for a b :: real
      and x :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    using  \<open>\<And>r. ((*\<^sub>R) r::'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x b a. a *\<^sub>C b *\<^sub>C (x::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = (a * b) *\<^sub>C x\<close>
    by simp

  show \<open>1 *\<^sub>R x = x\<close>
    for x :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) cblinfun \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x. 1 *\<^sub>C (x::('a, 'b) cblinfun) = x\<close>
    by simp
qed

end


lemma cblinfun_apply_add: "F *\<^sub>V (b1 + b2) = F *\<^sub>V b1 + F *\<^sub>V b2"
proof transfer
  show "F (b1 + b2) = F b1 + F b2"
    if "cbounded_linear F"
    for F :: "'b \<Rightarrow> 'a"
      and b1 b2 :: 'b
    using that unfolding cbounded_linear_def clinear_def Vector_Spaces.linear_def
    using module_hom.add by blast
qed

lemma apply_cblinfun_distr_left: "(A + B) *\<^sub>V x = A *\<^sub>V x + B *\<^sub>V x"
  apply transfer by simp

lemma cblinfun_apply_scaleC: "F *\<^sub>V (r *\<^sub>C b) = r *\<^sub>C (F *\<^sub>V b)"
proof transfer
  show "F (r *\<^sub>C b) = r *\<^sub>C (F b)"
    if "cbounded_linear F"
    for F :: "'b \<Rightarrow> 'a"
      and r :: complex
      and b :: 'b
    using that  
    unfolding cbounded_linear_def clinear_def Vector_Spaces.linear_def
    using module_hom.scale by blast
qed 


lemma cblinfun_apply_norm: "\<exists>K. \<forall>x. norm (F *\<^sub>V x) \<le> norm x * K "
  apply transfer unfolding cbounded_linear_def clinear_def Vector_Spaces.linear_def
  by (simp add: cbounded_linear_axioms_def)

instantiation cblinfun :: (complex_normed_vector, cbanach) "cbanach"
begin
lemma blinfun_of_cblinfun_Cauchy:
  assumes \<open>Cauchy f\<close>
  shows \<open>Cauchy (\<lambda> n. blinfun_of_cblinfun (f n))\<close>
  using assms unfolding Cauchy_def
  by (simp add: blinfun_of_cblinfun_dist)  


lemma cblinfun_of_blinfun_Cauchy:
  assumes \<open>Cauchy f\<close> and
    \<open>\<And>n::nat. \<And>c. \<And>x. (f n) *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C ((f n) *\<^sub>v x)\<close>
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
  fixes f::\<open>nat \<Rightarrow> ('a::complex_normed_vector \<Rightarrow>\<^sub>L 'b::cbanach)\<close>
    and l::\<open>'a \<Rightarrow>\<^sub>L 'b\<close> and c x
  assumes  \<open>f \<longlonglongrightarrow> l\<close> and
    \<open>\<And> n::nat. \<And>c. \<And>x. (f n) *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C ((f n) *\<^sub>v x)\<close> 
  shows \<open>l *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (l *\<^sub>v x)\<close>
proof-
  have \<open>l *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (l *\<^sub>v x)\<close>
    for c::complex and x
  proof-
    have u1: \<open>(\<lambda> n. (f n) *\<^sub>v (c *\<^sub>C x) ) \<longlonglongrightarrow> l *\<^sub>v (c *\<^sub>C x)\<close>
      by (simp add: assms(1) onorm_strong)        
    have \<open>isCont ((*\<^sub>C) c) y\<close>
      for y::'b
      using isCont_scaleC by auto
    hence \<open>isCont ((*\<^sub>C) c) (blinfun_apply l x)\<close>
      by simp
    hence u2: \<open>(\<lambda> n. c *\<^sub>C ((f n) *\<^sub>v x) ) \<longlonglongrightarrow> c *\<^sub>C (l *\<^sub>v x)\<close>
      using assms(1) isCont_tendsto_compose onorm_strong by blast 
    have u3: \<open>(f n) *\<^sub>v (c *\<^sub>C x) =  c *\<^sub>C ((f n) *\<^sub>v x)\<close>
      for n
      by (simp add: assms(2))
    have \<open>(\<lambda> n. (f n) *\<^sub>v (c *\<^sub>C x) ) \<longlonglongrightarrow> c *\<^sub>C (l *\<^sub>v x)\<close>
      using u1 u2 u3
      by simp
    thus ?thesis
      using  \<open>(\<lambda> n. (f n) *\<^sub>v (c *\<^sub>C x) ) \<longlonglongrightarrow> l *\<^sub>v (c *\<^sub>C x)\<close> LIMSEQ_unique 
      by blast
  qed
  thus ?thesis by blast
qed  

lemma cblinfun_of_blinfun_lim:
  fixes f::\<open>nat \<Rightarrow> ('a::complex_normed_vector \<Rightarrow>\<^sub>L 'b::cbanach)\<close>
    and l::\<open>'a \<Rightarrow>\<^sub>L 'b\<close>
  assumes  \<open>f \<longlonglongrightarrow> l\<close> and \<open>\<And>n::nat. \<And>c. \<And>x. (f n) *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C ((f n) *\<^sub>v x)\<close>
  shows \<open>(\<lambda> n. cblinfun_of_blinfun (f n)) \<longlonglongrightarrow> cblinfun_of_blinfun l\<close>
proof
  show "\<forall>\<^sub>F x in sequentially. dist (cblinfun_of_blinfun (f x)) (cblinfun_of_blinfun l) < e"
    if "(0::real) < e"
    for e :: real
  proof-
    from \<open>f \<longlonglongrightarrow> l\<close>
    have u1: \<open>\<forall>\<^sub>F x in sequentially. dist (f x) l < e\<close>
      by (simp add: tendstoD that)
    have u2: \<open>blinfun_of_cblinfun (cblinfun_of_blinfun (f n)) = f n\<close>
      for n
      by (simp add: assms(2) blinfun_cblinfun)
    have \<open>\<forall> c. \<forall> x. blinfun_apply l (c *\<^sub>C x) = c *\<^sub>C (blinfun_apply l x)\<close>
      using assms(1) assms(2) cblinfun_of_blinfun_complex_lim by blast        
    hence u3: \<open>blinfun_of_cblinfun (cblinfun_of_blinfun l) = l\<close>
      by (simp add: blinfun_cblinfun) 
    show ?thesis 
      unfolding blinfun_of_cblinfun_dist
      using u1 u2 u3
      by simp  
  qed    
qed

instance 
proof
  show "convergent f"
    if "Cauchy f"
    for f :: "nat \<Rightarrow> ('a, 'b) cblinfun"
  proof-
    have \<open>Cauchy (\<lambda>n. blinfun_of_cblinfun (f n))\<close>
      by (simp add: blinfun_of_cblinfun_Cauchy that)
    hence \<open>convergent (\<lambda> n. blinfun_of_cblinfun (f n))\<close>
      by (simp add: Cauchy_convergent_iff)
    hence \<open>\<exists>l. (\<lambda>n. blinfun_of_cblinfun (f n)) \<longlonglongrightarrow> blinfun_of_cblinfun l\<close>
      by (metis (no_types, lifting) Bounded_Operators.cblinfun_of_blinfun_complex_lim convergent_LIMSEQ_iff blinfun_cblinfun blinfun_of_cblinfun_prelim)
    then obtain l where \<open>(\<lambda>n. blinfun_of_cblinfun (f n)) \<longlonglongrightarrow> blinfun_of_cblinfun l\<close>
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
  adjoint :: "'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space \<Rightarrow> ('b,'a) cblinfun" ("_*" [99] 100)
  is Adj by (fact Adj_cbounded_linear)

lift_definition idOp::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> is id
  using id_cbounded_linear by blast

lemma idOp_adjoint[simp]: "idOp* = idOp"
  apply transfer using id_dagger by blast

lemma scalar_times_adj[simp]: "(a *\<^sub>C A)* = (cnj a) *\<^sub>C (A*)" 
  for A::"'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space"
    and a :: complex 
proof-
  have \<open>cbounded_linear ((cblinfun_apply A))\<close>
    using cblinfun_apply by blast
  hence \<open>(\<lambda>t. a *\<^sub>C (A *\<^sub>V t))\<^sup>\<dagger> = (\<lambda>s. (cnj a) *\<^sub>C (((cblinfun_apply A)\<^sup>\<dagger>) s))\<close>
    using scalar_times_adjc_flatten
    unfolding cbounded_linear_def 
      scalar_times_adjc_flatten \<open>cbounded_linear (cblinfun_apply A)\<close>
    using scalar_times_adjc_flatten complex_vector.linear_scale
    by (simp add: complex_vector.linear_scale scalar_times_adjc_flatten \<open>cbounded_linear ((*\<^sub>V) A)\<close> 
        cbounded_linear.bounded_linear)
  moreover have \<open>cblinfun_apply ((a *\<^sub>C A)*) = (\<lambda> t. a *\<^sub>C (A *\<^sub>V t))\<^sup>\<dagger>\<close>
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
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  shows \<open>(A + B)* = (A*) + (B*)\<close>
proof transfer
  fix A B::\<open>'a \<Rightarrow> 'b\<close>
  assume a1: \<open>cbounded_linear A\<close> and a2: \<open>cbounded_linear B\<close>
  define F where \<open>F = (\<lambda>x. (A\<^sup>\<dagger>) x + (B\<^sup>\<dagger>) x)\<close>
  define G where \<open>G = (\<lambda>x. A x + B x)\<close>
  have \<open>cbounded_linear G\<close>
    unfolding G_def
    by (simp add: a1 a2 cbounded_linear_add)
  moreover have \<open>\<langle>F u,  v\<rangle> = \<langle>u, G v\<rangle>\<close>
    for u::'b and v::'a
    unfolding F_def G_def
    using Adj_I a1 a2 
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
  "'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'c::complex_normed_vector
     \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L'c"
  is "(o)"
  unfolding o_def 
  by (rule cbounded_linear_compose, simp_all)

(*TODO: change name from "applyOpSpace" to "cblinfun_image" *)
(* Closure is necessary. See thunderlink://messageid=47a3bb3d-3cc3-0934-36eb-3ef0f7b70a85@ut.ee *)
lift_definition applyOpSpace::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector
\<Rightarrow> 'a clinear_space \<Rightarrow> 'b clinear_space\<close> 
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
  fixes G :: "'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space"
  shows \<open>\<langle>G* *\<^sub>V x, y\<rangle> = \<langle>x, G *\<^sub>V y\<rangle>\<close>
  apply transfer using Adj_I by blast

lemma adjoint_I':
  fixes G :: "'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space"
  shows \<open>\<langle>x, G* *\<^sub>V y\<rangle> = \<langle>G *\<^sub>V x, y\<rangle>\<close> 
  apply transfer using Adj_I' by blast

lemma adjoint_D:
  fixes G:: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
    and F:: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assumes \<open>\<And>x y. \<langle>(cblinfun_apply F) x, y\<rangle> = \<langle>x, (cblinfun_apply G) y\<rangle>\<close>
  shows \<open>F = G*\<close>
  using assms apply transfer using Adj_D by auto

lemma adjoint_twice[simp]: "(U*)* = U" 
  for U :: "'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space"
  apply transfer
  using dagger_dagger_id by blast

lemma blinfun_of_cblinfun_timesOp:
  fixes f::\<open>'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector\<close>
    and g::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  shows \<open>blinfun_of_cblinfun (f  o\<^sub>C\<^sub>L g) = (blinfun_of_cblinfun f) o\<^sub>L (blinfun_of_cblinfun g)\<close>
  apply transfer by auto

lemma cblinfun_apply_assoc: 
  shows "(A  o\<^sub>C\<^sub>L B)  o\<^sub>C\<^sub>L C = A  o\<^sub>C\<^sub>L (B  o\<^sub>C\<^sub>L C)"
  by (metis (no_types, lifting) cblinfun_apply_inject fun.map_comp timesOp.rep_eq)

lemma cblinfun_apply_dist1:  
  fixes a b :: "'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
    and c :: "'a::complex_normed_vector   \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows "(a + b)  o\<^sub>C\<^sub>L c = (a  o\<^sub>C\<^sub>L c) + (b  o\<^sub>C\<^sub>L c)"
  apply transfer
  by auto

lemma cblinfun_apply_dist2:
  fixes a b :: "'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector"
    and c :: "'b \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
  shows "c o\<^sub>C\<^sub>L (a + b) = (c o\<^sub>C\<^sub>L a) + (c o\<^sub>C\<^sub>L b)"
proof-
  have u1: "c \<circ> (\<lambda>x. a x + b x) = (\<lambda>x. c (a x) + c (b x))"
    if "cbounded_linear c"
      and "cbounded_linear a"
      and "cbounded_linear b"
    for a b:: "'a \<Rightarrow> 'b" and c::"'b \<Rightarrow> 'c"
    using that  blinfun_of_cblinfun_inj  blinfun_of_cblinfun_timesOp times_blinfun_dist2
    using cbounded_linear.bounded_linear linear_simps(1) by fastforce
  show ?thesis
    apply transfer by (simp add: u1)
qed

lemma timesOp_minus:
  \<open>A o\<^sub>C\<^sub>L (B - C) = A o\<^sub>C\<^sub>L B - A o\<^sub>C\<^sub>L C\<close>
  apply transfer
  using  cbounded_linear_def
  by (metis comp_apply complex_vector.linear_diff)

lemma times_adjoint[simp]:
  fixes B::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
    and A::\<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space\<close> 
  shows "(A o\<^sub>C\<^sub>L B)* =  (B*) o\<^sub>C\<^sub>L (A*)"
proof transfer
  fix  A :: \<open>'b \<Rightarrow> 'c\<close> and B :: \<open>'a \<Rightarrow> 'b\<close>
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

lemma OCL_zero [simp]:  
  fixes U::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector\<close>
  shows  "U  o\<^sub>C\<^sub>L 0 = 0"
  apply transfer
  unfolding cbounded_linear_def
  using complex_vector.linear_0 by force


lemma applyOp_0[simp]:  
  fixes U::"'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space"
  shows "U *\<^sub>S 0 = 0"
proof-  
  have  \<open>closure (U ` {0}) = {0}\<close>
    if a1: "cbounded_linear U"
    for U::\<open>'a\<Rightarrow>'b\<close>
  proof-
    have \<open>U ` {0} = {U 0}\<close>
      by auto
    moreover have \<open>U 0 = 0\<close>
      using a1
      unfolding cbounded_linear_def
      by (simp add: complex_vector.linear_0)
    ultimately have \<open>U ` {0} = {0}\<close>
      by simp
    thus ?thesis
      by simp 
  qed
  hence \<open>Abs_clinear_space (closure (U ` {0})) = Abs_clinear_space {0}\<close>
    if "cbounded_linear U"
    for U::\<open>'a\<Rightarrow>'b\<close>
    using Abs_clinear_space_inject that
    by presburger
  hence u1: \<open>Abs_clinear_space (closure (U ` space_as_set (Abs_clinear_space {0}))) =
         Abs_clinear_space {0}\<close>
    if "cbounded_linear U"
    for U::\<open>'a\<Rightarrow>'b\<close>
    using that
    by (simp add: Abs_clinear_space_inverse)
  have u2: "(\<And>U::'a \<Rightarrow> 'b.
        cbounded_linear U \<Longrightarrow>
        Abs_clinear_space
         (closure (U ` space_as_set (Abs_clinear_space {0::'a}))) =
        Abs_clinear_space {0::'b}) \<Longrightarrow>
    Abs_clinear_space (closure ((*\<^sub>V) U ` space_as_set \<bottom>)) = \<bottom>"
    using bot_clinear_space.abs_eq   
    by (metis (full_types) mem_Collect_eq cblinfun_apply)
  show ?thesis
    unfolding zero_clinear_space_def applyOpSpace_def
    by (simp add: u1 u2)    
qed

lemma times_comp:
  fixes A B \<psi>
  assumes a1: "cbounded_linear A" and a2: "cbounded_linear B" and a3: "closed_subspace \<psi>"
  shows "closure ((A \<circ> B) ` \<psi>) = closure (A ` closure (B ` \<psi>))"
proof-
  have b1: "closure ((A \<circ> B) ` (\<psi>::'c set)::'b set) \<subseteq> closure (A ` closure (B ` \<psi>::'a set))"
    by (metis closure_mono closure_subset image_comp image_mono)      
  have "x \<in> closure ((A \<circ> B) ` \<psi>)"
    if "x \<in> A ` closure (B ` \<psi>)"
    for x :: 'b
  proof-
    have \<open>\<exists>y\<in>closure (B ` \<psi>). x = A y\<close>
      using that by blast
    then obtain y where y_def1: \<open>y\<in>closure (B ` \<psi>)\<close> and y_def2: \<open>x = A y\<close>
      by blast
    from \<open>y\<in>closure (B ` \<psi>)\<close>
    have \<open>\<exists> s::nat \<Rightarrow> 'a. (\<forall>n. s n \<in> B ` \<psi>) \<and> s \<longlonglongrightarrow> y\<close>
      using closure_sequential by blast
    then obtain s::\<open>nat\<Rightarrow>'a\<close> where \<open>\<forall>n. s n \<in> B ` \<psi>\<close> and \<open>s \<longlonglongrightarrow> y\<close>
      by blast
    define t::"nat \<Rightarrow> 'b" where \<open>t n = A (s n)\<close> for n::nat
    have v1: \<open>t n \<in> (A \<circ> B) ` \<psi>\<close>
      for n
      by (metis \<open>\<forall>n. s n \<in> B ` \<psi>\<close> imageI image_comp t_def)
    have \<open>isCont A y\<close>
      using \<open>cbounded_linear A\<close>
      by (simp add: bounded_linear_continuous)
    hence v2: \<open>t \<longlonglongrightarrow> x\<close>
      unfolding t_def using \<open>s \<longlonglongrightarrow> y\<close>
      by (simp add: \<open>x = A y\<close> isCont_tendsto_compose) 
    have "(\<forall>n. t n \<in> (A \<circ> B) ` \<psi>) \<and> t \<longlonglongrightarrow> x"
      using v1 v2 by blast
    thus ?thesis
      using closure_sequential by blast 
  qed
  hence \<open>A ` closure (B ` \<psi>) \<subseteq> closure ((A \<circ> B) ` \<psi>)\<close>
    by blast    
  hence b2: "closure (A ` closure (B ` (\<psi>::'c set)::'a set)) \<subseteq> closure ((A \<circ> B) ` \<psi>::'b set)"
    by (metis closure_closure closure_mono)
  show ?thesis
    using b1 b2 a1 a2 a3 by blast 
qed

lemma cblinfun_apply_assoc_clinear_space: 
  \<open>(A o\<^sub>C\<^sub>L B) *\<^sub>S \<psi> =  A *\<^sub>S (B *\<^sub>S \<psi>)\<close>
  apply transfer
  using times_comp by blast 

lemmas assoc_left = cblinfun_apply_assoc[symmetric] cblinfun_apply_assoc_clinear_space[symmetric] 
  add.assoc[where ?'a="'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space", symmetric]
lemmas assoc_right = cblinfun_apply_assoc cblinfun_apply_assoc_clinear_space add.assoc
  [where ?'a="'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space"]

lemma scalar_times_op_add[simp]: "a *\<^sub>C (A+B) = a *\<^sub>C A + a *\<^sub>C B" 
  for A B :: "_::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L _::complex_normed_vector"
  by (simp add: scaleC_add_right)

lemma scalar_times_op_minus[simp]: "a *\<^sub>C (A-B) =  a *\<^sub>C A - a *\<^sub>C B" 
  for A B :: "_::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L _::complex_normed_vector"
  by (simp add: complex_vector.scale_right_diff_distrib)


lemma applyOp_bot[simp]:
  fixes U::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> 
  shows "U *\<^sub>S bot = bot"
proof-
  have \<open>closed {0::'a}\<close>
    using Topological_Spaces.t1_space_class.closed_singleton by blast
  hence u1: \<open>closure {0::'a} = {0}\<close>
    by (simp add: closure_eq)    
  have \<open>cbounded_linear (cblinfun_apply U)\<close>
    using cblinfun_apply by auto
  hence  \<open>cblinfun_apply U 0 = 0\<close>
    by (simp add: cbounded_linear.clinear clinear_zero)  
  hence u2: \<open>cblinfun_apply U ` {0::'a} = {0}\<close>
    by simp
  have \<open>closure (cblinfun_apply U ` {0}) = {0}\<close>
    using u2 by auto    
  hence \<open>(closure (cblinfun_apply U ` space_as_set (Abs_clinear_space {0}))) = {0}\<close>
    by (metis bot_clinear_space.abs_eq bot_clinear_space.rep_eq) 
  thus ?thesis
    unfolding applyOpSpace_def bot_clinear_space_def by simp
qed

lemma cbounded_minkowski_sum_exchange:
  fixes U::\<open>'a::complex_normed_vector\<Rightarrow>'b::complex_normed_vector\<close> and A B::\<open>'a set\<close>
  assumes a1: \<open>cbounded_linear U\<close> and a2: \<open>closed_subspace A\<close> and a3: \<open>closed_subspace B\<close>
  shows "(closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
         (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})"
proof- 
  have v1: \<open>U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} = {U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
    by auto
  have \<open>{U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} = {U \<psi> + U \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
    using \<open>cbounded_linear U\<close>
    unfolding cbounded_linear_def
    by (metis (no_types, lifting) complex_vector.linear_add) 
  also have \<open>{U \<psi> + U \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} 
            = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}\<close>
    by blast  
  finally have v2: \<open>{U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}
                      = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}\<close>
    by blast
  have v3: \<open>{\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}
           \<subseteq> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
    by (smt Collect_mono_iff closure_subset subsetD)
      (* > 1s*)      
  have \<open>U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} \<subseteq>
          {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
    by (simp add: v1 v2 v3)  
  hence y1: \<open>closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
    by (simp add: closure_mono)      
  define S where \<open>S = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
  from a1 have \<open>isCont U x\<close>
    for x
    by (simp add: bounded_linear_continuous)
  hence \<open>continuous_on (closure S) U\<close>
    by (simp add: continuous_at_imp_continuous_on)
  hence \<open>U ` (closure S) \<subseteq> closure (U ` S)\<close>
    using Abstract_Topology_2.image_closure_subset
    by (simp add: image_closure_subset closure_subset)
  hence y2: \<open>(U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})
            \<subseteq> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
    unfolding S_def by blast
  have \<open>(U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
    using y1 y2 by blast    
  hence x1: \<open>(closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
    by (metis (no_types, lifting) closure_closure closure_mono)
  have \<open>x \<in> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
    if q1: \<open>x \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
    for x
  proof-
    from q1 obtain \<psi> \<phi> where q2: \<open>x =  \<psi> + \<phi>\<close>  and q3: \<open>\<psi> \<in> closure (U ` A)\<close> 
      and q4: \<open>\<phi> \<in> closure (U ` B)\<close>
      by blast
    from  \<open>\<psi> \<in> closure (U ` A)\<close>
    have \<open>\<exists>psiU. (\<forall> n. psiU n \<in> (U ` A)) \<and> (\<lambda> n. psiU n) \<longlonglongrightarrow> \<psi>\<close>
      using closure_sequential by blast
    then obtain psiU where o1: \<open>\<forall>n. psiU n \<in> (U ` A)\<close> and o2: \<open>(\<lambda> n. psiU n) \<longlonglongrightarrow> \<psi>\<close>
      by blast
    from \<open>\<forall> n. psiU n \<in> (U ` A)\<close>
    have \<open>\<forall> n. \<exists> psi.  psiU n = U psi \<and> psi \<in> A\<close>
      by blast
    hence \<open>\<exists>psi. \<forall> n. psiU n = U (psi n) \<and> psi n \<in> A\<close>
      by metis
    then obtain psi where o3: \<open>\<And>n. psiU n = U (psi n)\<close> and o4: \<open>\<And>n. psi n \<in> A\<close>
      by blast
    have  t1: \<open>(\<lambda> n. U (psi n)) \<longlonglongrightarrow> \<psi>\<close>
      using o2 o3
      by simp
    from  \<open>\<phi> \<in> closure (U ` B)\<close>
    have \<open>\<exists>phiU. (\<forall> n. phiU n \<in> (U ` B)) \<and> (\<lambda> n. phiU n) \<longlonglongrightarrow> \<phi>\<close>
      using closure_sequential by blast
    then obtain phiU where h1: \<open>\<And>n. phiU n \<in> (U ` B)\<close> and h2: \<open>(\<lambda> n. phiU n) \<longlonglongrightarrow> \<phi>\<close>
      by blast    
    have \<open>\<exists>phi.  phiU n = U phi \<and> phi \<in> B\<close>
      for n
      using h1 by blast
    hence \<open>\<exists>phi. \<forall> n. phiU n = U (phi n) \<and> phi n \<in> B\<close>
      by metis
    then obtain phi where h3: \<open>\<And>n. phiU n = U (phi n)\<close> and h4: \<open>\<And>n. phi n \<in> B\<close>
      by blast
    have t2:  \<open>(\<lambda> n. U (phi n)) \<longlonglongrightarrow> \<phi>\<close>
      using h2 h3
      by simp
    have t3: \<open>(\<lambda> n. U (psi n) +  U (phi n) ) \<longlonglongrightarrow> \<psi> + \<phi>\<close>
      by (simp add: tendsto_add t2 t1)
    have \<open>U (psi n) +  U (phi n) =  U ( (psi n) +  (phi n))\<close>
      for n
      using \<open>cbounded_linear U\<close>
      unfolding cbounded_linear_def clinear_def Vector_Spaces.linear_def
        module_hom_def module_hom_axioms_def
      by auto
    hence \<open>(\<lambda> n. U ( (psi n) +  (phi n)) ) \<longlonglongrightarrow> \<psi> + \<phi>\<close>
      using t3 by auto  
    hence \<open>(\<lambda> n. U ( (psi n) +  (phi n)) ) \<longlonglongrightarrow> x\<close>
      by (simp add: q2)      
    hence \<open>x \<in> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
      by (smt closure_sequential h4 mem_Collect_eq o4 v1)
    thus ?thesis by blast
  qed
  moreover have \<open>closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})
        \<subseteq> closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
    by (simp add: closure_mono closure_subset image_mono)
  ultimately have x2: \<open>(closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})
      \<subseteq> closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
    using closure_mono
    by (metis (no_types, lifting) closure_closure dual_order.trans subsetI)  
  show ?thesis
    using x1 x2 by blast 
qed

lemma cblinfun_image_sup_exchange[simp]:   
  fixes A B :: \<open>'a::chilbert_space clinear_space\<close> and U :: "'a \<Rightarrow>\<^sub>C\<^sub>L'b::chilbert_space"
  shows \<open>U *\<^sub>S (sup A B) = sup (U *\<^sub>S A) (U *\<^sub>S B)\<close>  
proof transfer
  fix U::\<open>'a\<Rightarrow>'b\<close> and A B::\<open>'a set\<close>
  assume a1: \<open>cbounded_linear U\<close> and a2: \<open>closed_subspace A\<close> and a3: \<open>closed_subspace B\<close> 
  hence \<open>(closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
        (closure {\<psi> + \<phi> |\<psi> \<phi>.
           \<psi> \<in> closure (U ` A) \<and>
           \<phi> \<in> closure (U ` B)})\<close>
    using cbounded_minkowski_sum_exchange by blast    
  thus \<open>closure (U ` (A +\<^sub>M B)) =
       closure (U ` A) +\<^sub>M closure (U ` B)\<close>
    unfolding closed_sum_def set_plus_def
    by (smt Collect_cong)    
qed


lemma scalar_op_clinear_space_assoc [simp]: 
  fixes A::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
    and S::\<open>'a clinear_space\<close> and \<alpha>::complex
  shows \<open>(\<alpha> *\<^sub>C A) *\<^sub>S S  = \<alpha> *\<^sub>C (A *\<^sub>S S)\<close>
proof-
  have \<open>closure ( ( ((*\<^sub>C) \<alpha>) \<circ> (cblinfun_apply A) ) ` space_as_set S) =
   ((*\<^sub>C) \<alpha>) ` (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis closure_scaleC image_comp)    
  hence \<open>(closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
   ((*\<^sub>C) \<alpha>) ` (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis (mono_tags, lifting) comp_apply image_cong scaleC_cblinfun.rep_eq)
  hence \<open>Abs_clinear_space
     (closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
    \<alpha> *\<^sub>C
    Abs_clinear_space (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis space_as_set_inverse applyOpSpace.rep_eq scaleC_clinear_space.rep_eq)    
  have x1: "Abs_clinear_space (closure ((*\<^sub>V) (\<alpha> *\<^sub>C A) ` space_as_set S)) =
    \<alpha> *\<^sub>C Abs_clinear_space (closure ((*\<^sub>V) A ` space_as_set S))"
    using \<open>Abs_clinear_space
     (closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
    \<alpha> *\<^sub>C Abs_clinear_space (closure (cblinfun_apply A ` space_as_set S))\<close>
    by blast
  show ?thesis
    unfolding applyOpSpace_def apply auto using x1 by blast
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
  hence \<open>Abs_clinear_space
     (closure (cblinfun_apply (cBlinfun id) ` space_as_set \<psi>)) = \<psi>\<close>
    by (simp add: space_as_set_inverse)    
  have x1: "Abs_clinear_space
     (closure ((*\<^sub>V) (cBlinfun id) ` space_as_set \<psi>)) = \<psi>"
    using  \<open>Abs_clinear_space
     (closure (cblinfun_apply (cBlinfun id) ` space_as_set \<psi>)) = \<psi>\<close>
    by blast
  show ?thesis
    unfolding applyOpSpace_def idOp_def
    by (simp add: x1)    
qed

(* TODO: Same for scaleR *)
lemma scalar_op_op[simp]:
  fixes A::"'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
    and B::"'a::complex_normed_vector  \<Rightarrow>\<^sub>C\<^sub>L 'b"
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

(* TODO: Same for scaleR *)
lemma op_scalar_op[simp]:
  fixes A::"'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector" 
    and B::"'a::complex_normed_vector  \<Rightarrow>\<^sub>C\<^sub>L 'b"
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
  fixes U :: "'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::cbanach"
    and V :: "'a \<Rightarrow> 'b clinear_space" 
  shows \<open>U *\<^sub>S (INF i. V i) \<le> (INF i. U *\<^sub>S (V i))\<close>
  apply transfer
  by (simp add: INT_greatest Inter_lower closure_mono image_mono) 

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
  fixes U::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> and B C::"'a clinear_space"
  shows "U *\<^sub>S (inf B  C) \<le> inf (U *\<^sub>S B) (U *\<^sub>S C)"
proof-
  have \<open>closure (U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
    if \<open>cbounded_linear U\<close> and \<open>closed_subspace B\<close> and \<open>closed_subspace C\<close>
    for U::\<open>'a\<Rightarrow>'b\<close> and B C::\<open>'a set\<close>
  proof-
    have \<open>(U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
      using closure_subset by force      
    moreover have \<open>closed ( closure (U ` B) \<inter> closure (U ` C) )\<close>
      by blast      
    ultimately show ?thesis
      by (simp add: closure_minimal) 
  qed
  thus ?thesis
    by (metis (no_types, lifting) cblinfun_image_sup_exchange inf.cobounded2 inf.idem inf_commute le_inf_iff 
        sup.bounded_iff sup_inf_absorb)
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
  have \<open>\<exists>T \<in> *s* (complex_vector.span G). T \<approx> star_of t\<close>
    using approx_sym nsclosure_I by blast
  then obtain T where \<open>T \<in> *s* (complex_vector.span G)\<close> and \<open>T \<approx> star_of t\<close>
    by blast
  have \<open>(*f* F) T \<approx> (*f* F) (star_of t)\<close>
    using \<open>T \<approx> star_of t\<close>  \<open>isNSCont F t\<close>
    by (simp add: isNSCont_def)

  from  \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close>
  have  \<open>\<And>x. x \<in> complex_vector.span G \<Longrightarrow> A x = B x\<close>
    by (simp add: \<open>cbounded_linear (A::'a \<Rightarrow> 'b)\<close> \<open>cbounded_linear (B::'a \<Rightarrow> 'b)\<close> cbounded_linear.clinear complex_vector.linear_eq_on)
  hence \<open>\<forall>x.  x \<in> complex_vector.span G \<longrightarrow> F x = 0\<close>
    unfolding F_def
    by simp
  hence \<open>\<forall>x. x \<in> *s* (complex_vector.span G) \<longrightarrow> (*f* F) x = 0\<close>
    by StarDef.transfer
  hence \<open>(*f* F) T \<approx> 0\<close>
    using \<open>T \<in> *s* complex_vector.span G\<close> by auto  
  hence \<open>F t = 0\<close>
    using approx_sym approx_trans \<open>(*f* F) T \<approx> (*f* F) (star_of t)\<close> by fastforce
  thus \<open>A t = B t\<close>
    unfolding F_def by auto
qed

lemma applyOpSpace_span:
  fixes A B :: "'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L'b::cbanach"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and \<open>t \<in> space_as_set (Span G)\<close>
  shows "A *\<^sub>V t = B *\<^sub>V t"
  using assms
  apply transfer
  using equal_span_applyOpSpace by blast

lemma applyOpSpace_less_eq:
  fixes S :: "'a::cbanach clinear_space" 
    and A B :: "'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L'b::cbanach"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and "Span G \<ge> S"
  shows "A *\<^sub>S S \<le> B *\<^sub>S S"
  using assms proof transfer
  fix G :: "'a set" and A :: "'a \<Rightarrow> 'b" and B :: "'a \<Rightarrow> 'b" and S :: "'a set"
  assume a1: "cbounded_linear A"
  assume a2: "cbounded_linear B"
  assume a3: "\<And>x. x \<in> G \<Longrightarrow> A x = B x"
  assume a4: "S \<subseteq> closure (cspan G)"
  have f5: "(A \<noteq> B \<or> (\<exists>a::'a. a \<in> B \<and> (f a::'b) \<noteq> g a)) \<or> f ` A = g ` B"
    for A B f g
    by (meson image_cong)
  obtain t :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a" where
    "\<forall>x0 x1 x2. (\<exists>v. v \<in> x2 \<and> x1 v \<noteq> x0 v)
       = (t x0 x1 x2 \<in> x2 \<and> x1 (t x0 x1 x2) \<noteq> x0 (t x0 x1 x2))"
    by moura
  then have f6: "t B A S \<in> S \<and> A (t B A S) \<noteq> B (t B A S) \<or> A ` S = B ` S"
    using f5 by presburger
  have f7: "\<forall>f g A a. (\<not> cbounded_linear f \<or> \<not> cbounded_linear g
      \<or> (\<exists>a. (a::'a) \<in> A \<and> (f a::'b) \<noteq> g a) 
      \<or> a \<notin> closure (cspan A)) \<or> f a = g a"
    using equal_span_applyOpSpace by blast
  obtain s :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a" where
    "\<forall>x1 x2 x3. (\<exists>v. v \<in> x1 \<and> x3 v \<noteq> x2 v) 
    = (s x1 x2 x3 \<in> x1 \<and> x3 (s x1 x2 x3) \<noteq> x2 (s x1 x2 x3))"
    by moura
  hence f8: "(\<not> cbounded_linear f \<or> \<not> cbounded_linear g 
      \<or> s A g f \<in> A \<and> f (s A g f) \<noteq> g (s A g f) \<or> a \<notin> closure (cspan A)) 
      \<or> f a = g a"
    for f g A a
    using f7 by presburger
  have f9: "a \<notin> G \<or> A a = B a"
    for a
    using a3 by metis
  have "(\<not> A \<subseteq> B \<or> (a::'a) \<notin> A) \<or> a \<in> B"
    for A B a
    by (metis in_mono)
  hence "A ` S = B ` S"
    using f9 f8 f6 a4 a2 a1 by meson
  thus "closure (A ` S) \<subseteq> closure (B ` S)"
    by (metis equalityE)
qed


lemma applyOpSpace_eq:
  fixes S :: "'a::chilbert_space clinear_space"
    and A B :: "'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and "Span G \<ge> S"
  shows "A *\<^sub>S S = B *\<^sub>S S"
  by (metis applyOpSpace_less_eq assms(1) assms(2) dual_order.antisym)

subsection \<open>Unitary\<close>

definition isometry::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space \<Rightarrow> bool\<close> where
  \<open>isometry U \<longleftrightarrow> U* o\<^sub>C\<^sub>L  U = idOp\<close>

definition unitary::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space \<Rightarrow> bool\<close> where
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

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" 
  for U::"_ \<Rightarrow>\<^sub>C\<^sub>L  _"
  unfolding unitary_def by auto

lemma isometry_times[simp]: 
  assumes "isometry A" and "isometry B"  
  shows "isometry (A o\<^sub>C\<^sub>L B)"
proof-
  have "B* o\<^sub>C\<^sub>L A* o\<^sub>C\<^sub>L (A o\<^sub>C\<^sub>L B) = idOp"
    if "A* o\<^sub>C\<^sub>L A = idOp" and "B* o\<^sub>C\<^sub>L B = idOp"
    using that
    by (metis cblinfun_apply_assoc times_idOp1)
  thus ?thesis 
    using assms unfolding isometry_def by simp
qed


lemma unitary_times[simp]: "unitary (A o\<^sub>C\<^sub>L B)"
  if "unitary A" and "unitary B"
  using that unfolding unitary_def' by simp

lemma unitary_surj: 
  assumes "unitary U"
  shows "surj (cblinfun_apply U)"
proof-
  have \<open>\<exists>t. (cblinfun_apply U) t = x\<close>
    for x
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
    finally have \<open>(cblinfun_apply U) ((cblinfun_apply (U*)) x) = x\<close>
      by simp    
    thus ?thesis
      by blast 
  qed
  thus ?thesis
    by (metis surj_def) 
qed

lemma unitary_image[simp]: 
  assumes a1: "unitary U"
  shows "U *\<^sub>S top = top"
proof-
  have \<open>surj (cblinfun_apply U)\<close>
    using a1 unitary_surj by blast
  hence \<open>range (cblinfun_apply U) = UNIV\<close>
    by simp
  hence \<open>closure (range (cblinfun_apply U)) = UNIV\<close>
    by simp
  thus ?thesis
    apply transfer
    by blast
qed

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def
  by (simp add: isometry_def) 

subsection \<open>Projectors\<close>

lift_definition Proj :: "('a::chilbert_space) clinear_space \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L'a"
  is \<open>projection\<close>
  by (rule Complex_Inner_Product.projectionPropertiesA)


lemma imageOp_Proj[simp]: "(Proj S) *\<^sub>S top = S"  
proof-
  have "closure (range (projection S)) \<subseteq> S"
    if "closed_subspace S"
    for S :: "'a set"
    using that OrthoClosedEq orthogonal_complement_twice 
    by (metis closed_subspace.subspace pre_ortho_twice projectionPropertiesE subspace_cl)
  moreover have "S \<subseteq> closure (range (projection S))"
    if "closed_subspace S"
    for S :: "'a set"
    using that
    by (metis (no_types, lifting) closure_subset image_subset_iff in_mono projection_fixed_points 
        subsetI subset_UNIV) 
  ultimately show ?thesis 
    apply transfer by (simp add: set_eq_subset)
qed


lemma Proj_D1: \<open>(Proj M) = (Proj M)*\<close>
  apply transfer
  by (rule projection_D1)


lemma Proj_D2[simp]: \<open>(Proj M) o\<^sub>C\<^sub>L (Proj M) = (Proj M)\<close>
proof-
  have u1: \<open>(cblinfun_apply (Proj M)) = projection (space_as_set M)\<close>
    apply transfer
    by blast
  have \<open>closed_subspace (space_as_set M)\<close>
    using space_as_set by auto
  hence u2: \<open>(projection (space_as_set M))\<circ>(projection (space_as_set M))
                = (projection (space_as_set M)) \<close>
    by (simp add: projectionPropertiesC)
  have \<open>(cblinfun_apply (Proj M)) \<circ> (cblinfun_apply (Proj M)) = cblinfun_apply (Proj M)\<close>
    using u1 u2
    by simp    
  hence \<open>cblinfun_apply ((Proj M) o\<^sub>C\<^sub>L (Proj M)) = cblinfun_apply (Proj M)\<close>
    by (simp add: timesOp.rep_eq)
  thus ?thesis using cblinfun_apply_inject
    by auto 
qed

lift_definition isProjector::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> bool\<close> is
  \<open>\<lambda>P. \<exists> M. closed_subspace M \<and> is_projection_on P M\<close>.

lemma Proj_I:
  fixes P :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'a\<close>
  assumes \<open>P o\<^sub>C\<^sub>L P = P\<close> and \<open>P = P*\<close>
  shows \<open>P = Proj (P *\<^sub>S top)\<close>
proof-
  define M where "M = P *\<^sub>S top"
  have v3: "x \<in> (\<lambda>x. x - P *\<^sub>V x) -` {0}"
    if "x \<in> range (cblinfun_apply P)"
    for x :: 'a
  proof-
    have v3_1: \<open>cblinfun_apply P \<circ> cblinfun_apply P = cblinfun_apply P\<close>
      by (metis \<open>P o\<^sub>C\<^sub>L P = P\<close> timesOp.rep_eq)
    have \<open>\<exists>t. P *\<^sub>V t = x\<close>
      using that by blast
    then obtain t where t_def: \<open>P *\<^sub>V t = x\<close>
      by blast 
    hence \<open>x - P *\<^sub>V x = x - P *\<^sub>V (P *\<^sub>V t)\<close>
      by simp
    also have \<open>\<dots> = x - (P *\<^sub>V t)\<close>
      using v3_1      
      by (metis comp_apply) 
    also have \<open>\<dots> = 0\<close>
      by (simp add: t_def)
    finally have \<open>x - P *\<^sub>V x = 0\<close>
      by blast
    thus ?thesis
      by simp 
  qed

  have v1: "range (cblinfun_apply P) \<subseteq> (\<lambda>x. x - cblinfun_apply P x) -` {0}"
    using v3
    by blast

  have "x \<in> range (cblinfun_apply P)"
    if "x \<in> (\<lambda>x. x - P *\<^sub>V x) -` {0}"
    for x :: 'a
  proof-
    have x1:\<open>x - P *\<^sub>V x = 0\<close>
      using that by blast
    have \<open>x = P *\<^sub>V x\<close>
      by (simp add: x1 eq_iff_diff_eq_0)
    thus ?thesis
      by blast 
  qed
  hence v2: "(\<lambda>x. x - cblinfun_apply P x) -` {0} \<subseteq> range (cblinfun_apply P)"
    by blast
  have i1: \<open>range (cblinfun_apply P) = (\<lambda> x. x - cblinfun_apply P x) -` {0}\<close>
    using v1 v2
    by (simp add: v1 dual_order.antisym) 
  have p1: \<open>closed {(0::'a)}\<close>
    by simp        
  have p2: \<open>continuous (at x) (\<lambda> x. x - P *\<^sub>V x)\<close>
    for x
  proof-
    have \<open>cblinfun_apply (idOp - P) = (\<lambda> x. x - P *\<^sub>V x)\<close>
      by (simp add: idOp.rep_eq minus_cblinfun.rep_eq)                 
    hence \<open>cbounded_linear (cblinfun_apply (idOp - P))\<close>
      using cblinfun_apply
      by blast 
    hence \<open>continuous (at x) (cblinfun_apply (idOp - P))\<close>
      by (simp add: bounded_linear_continuous)
    thus ?thesis
      using \<open>cblinfun_apply (idOp - P) = (\<lambda> x. x - P *\<^sub>V x)\<close>
      by simp
  qed

  have i2: \<open>closed ( (\<lambda> x. x - P *\<^sub>V x) -` {0} )\<close>
    using p1 p2
    by (rule Abstract_Topology.continuous_closed_vimage)

  have \<open>closed (range (cblinfun_apply P))\<close>
    using i1 i2
    by simp
  have u2: \<open>cblinfun_apply P x \<in> space_as_set M\<close>
    for x
    by (simp add: M_def \<open>closed (range ((*\<^sub>V) P))\<close> applyOpSpace.rep_eq top_clinear_space.rep_eq)

  have xy: \<open>\<langle> x - P *\<^sub>V x, y \<rangle> = 0\<close>
    if y1: \<open>y \<in> space_as_set M\<close>
    for x y
  proof-
    have \<open>\<exists>t. y = P *\<^sub>V t\<close>
      using y1
      by (simp add:  M_def \<open>closed (range ((*\<^sub>V) P))\<close> applyOpSpace.rep_eq image_iff 
          top_clinear_space.rep_eq)
    then obtain t where t_def: \<open>y = P *\<^sub>V t\<close>
      by blast
    have \<open>\<langle> x - P *\<^sub>V x, y \<rangle> = \<langle> x - P *\<^sub>V x, P *\<^sub>V t \<rangle>\<close>
      by (simp add: t_def)
    also have \<open>\<dots> = \<langle> P *\<^sub>V (x - P *\<^sub>V x), t \<rangle>\<close>
      by (metis \<open>P = P*\<close> adjoint_I)
    also have \<open>\<dots> = \<langle> P *\<^sub>V x - P *\<^sub>V (P *\<^sub>V x), t \<rangle>\<close>
      by (metis \<open>P = P*\<close> adjoint_I cinner_diff_left)
    also have \<open>\<dots> = \<langle> P *\<^sub>V x - P *\<^sub>V x, t \<rangle>\<close>
      by (metis assms(1) comp_apply timesOp.rep_eq)    
    also have \<open>\<dots> = \<langle> 0, t \<rangle>\<close>
      by simp
    also have \<open>\<dots> = 0\<close>
      by simp
    finally show ?thesis by blast
  qed
  hence u1: \<open>x - P *\<^sub>V x \<in> orthogonal_complement (space_as_set M)\<close> 
    for x
    by (simp add: orthogonal_complement_I2) 
  have "closed_subspace (space_as_set M)"
    using space_as_set by auto
  hence f1: "(Proj M) *\<^sub>V a = P *\<^sub>V a"
    for a
    by (simp add: Proj.rep_eq projection_uniq u1 u2)
  have "(+) (a - a) = id"
    for a::'a
    by auto
  hence "(+) ((P - Proj M) *\<^sub>V a) = id"
    for a
    using f1
    by (simp add: minus_cblinfun.rep_eq) 
  hence "b - b = cblinfun_apply (P - Proj M) a"
    for a b
    by (metis (no_types) add_diff_cancel_right' id_apply)
  hence "cblinfun_apply (idOp - (P - Proj M)) a = a"
    for a
    by (simp add: idOp.rep_eq minus_cblinfun.rep_eq)      
  thus ?thesis
    using u1 u2 cblinfun_apply_inject diff_diff_eq2 diff_eq_diff_eq eq_id_iff idOp.rep_eq
    by (metis (no_types, hide_lams) M_def)
qed

lemma Proj_range_closed:
  assumes "isProjector P"
  shows "closed (range (cblinfun_apply P))"
  using assms apply transfer
  using closed_subspace.closed projectionPropertiesE' by blast

lemma Proj_isProjector[simp]:
  fixes M::\<open>'a::chilbert_space clinear_space\<close>
  shows \<open>isProjector (Proj M)\<close>
proof-
  have u1: "closed_subspace (space_as_set M)"
    using space_as_set by blast
  have v1: "h - Proj M *\<^sub>V h
         \<in> orthogonal_complement (space_as_set M)"
    for h
    by (simp add: Proj.rep_eq projection_intro1 u1)    
  have v2: "Proj M *\<^sub>V h \<in> space_as_set M"
    for h
    by (metis Proj.rep_eq projectionPropertiesE rangeI u1)
  have u2: "is_projection_on ((*\<^sub>V) (Proj M)) (space_as_set M)"
    unfolding is_projection_on_def
    by (simp add: v1 v2)
  show ?thesis
    using u1 u2 isProjector.rep_eq by blast 
qed

lemma isProjector_algebraic: 
  fixes P::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  shows \<open>isProjector P \<longleftrightarrow> P o\<^sub>C\<^sub>L P = P \<and> P = P*\<close>
proof
  have "P o\<^sub>C\<^sub>L P = P"
    if "isProjector P"
    using that apply transfer
    using  projectionPropertiesC'
    by auto
  moreover have "P = P*"
    if "isProjector P"
    using that apply transfer
    using projection_D1'
    by blast
  ultimately show "P o\<^sub>C\<^sub>L P = P \<and> P = P*"
    if "isProjector P"
    using that
    by blast
  show "isProjector P"
    if "P o\<^sub>C\<^sub>L P = P \<and> P = P*"
    using that Proj_I Proj_isProjector by metis
qed


lemma Proj_leq: "(Proj S) *\<^sub>S A \<le> S"
proof -
  have "top = sup top A"
    apply transfer
    using Complex_Vector_Spaces.subspace_UNIV is_closed_subspace_universal_inclusion_left 
    by blast 
  hence "sup S (Proj S *\<^sub>S A) = S"
    by (metis (full_types) cblinfun_image_sup_exchange imageOp_Proj)
  thus ?thesis
    by (meson sup.absorb_iff1)
qed


lemma Proj_times: 
  fixes A::"'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space"
  assumes a1: "isometry A" 
  shows "A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*) = Proj (A *\<^sub>S S)" 
proof-
  define P where \<open>P = A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*)\<close>
  have \<open>P o\<^sub>C\<^sub>L P = P\<close>
    using a1
    unfolding P_def isometry_def
    by (metis (no_types, lifting) Proj_D2 cblinfun_apply_assoc times_idOp2)
  moreover have \<open>P = P*\<close>
    unfolding P_def
    by (metis Proj_D1 adjoint_twice cblinfun_apply_assoc times_adjoint)
  ultimately have 
    \<open>\<exists>M. P = Proj M \<and> space_as_set M = range (cblinfun_apply (A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*)))\<close>
    using P_def Proj_I
    by (metis Proj.rep_eq mem_Collect_eq projectionPropertiesE space_as_set)
  then obtain M where \<open>P = Proj M\<close>
    and \<open>space_as_set M = range (cblinfun_apply (A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*)))\<close>
    by blast

  have f1: "A o\<^sub>C\<^sub>L Proj S = P o\<^sub>C\<^sub>L A"
    by (simp add: P_def assms cblinfun_apply_assoc)
  hence "P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L A* = P"
    using P_def by presburger
  hence "(P o\<^sub>C\<^sub>L A) *\<^sub>S (c \<squnion> A* *\<^sub>S d) = P *\<^sub>S (A *\<^sub>S c \<squnion> d)"
    for c d
    by (metis (no_types) cblinfun_apply_assoc_clinear_space cblinfun_image_sup_exchange)
  hence "P *\<^sub>S (A *\<^sub>S \<top> \<squnion> c) = (P o\<^sub>C\<^sub>L A) *\<^sub>S \<top>"
    for c
    by (metis sup_top_left)
  hence \<open>M = A *\<^sub>S S\<close>
    using f1 by (metis (no_types) \<open>P = Proj M\<close> cblinfun_apply_assoc_clinear_space imageOp_Proj 
        sup_commute sup_top_left)   
  thus ?thesis
    using \<open>P = Proj M\<close>
    unfolding P_def
    by blast
qed

abbreviation proj :: "'a::chilbert_space \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a" where "proj \<psi> \<equiv> Proj (Span {\<psi>})"

lemma projection_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" 
  for a::complex and \<psi>::"'a::chilbert_space"
  by (metis Span.abs_eq span_mult)

lemma move_plus:
  fixes A B C::"'a::chilbert_space clinear_space"
  assumes a1: \<open>(Proj (- C)) *\<^sub>S A \<le> B\<close>
  shows  "A \<le> sup B C"
proof-
  have x2: \<open>x \<in> space_as_set B\<close>
    if "x \<in>  closure ( (projection (orthogonal_complement (space_as_set C))) `
                   space_as_set A)"
    for x
    using that
    by (metis Proj.rep_eq applyOpSpace.rep_eq assms less_eq_clinear_space.rep_eq subsetD 
        uminus_clinear_space.rep_eq)
  have q1: \<open>x \<in> closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set B \<and> \<phi> \<in> space_as_set C}\<close>
    if \<open>x \<in> space_as_set A\<close>
    for x
  proof-
    have p1: \<open>closed_subspace (space_as_set C)\<close>
      using space_as_set by auto
    hence \<open>x = (projection (space_as_set C)) x
       + (projection (orthogonal_complement (space_as_set C))) x\<close>
      by (simp add: ortho_decomp)
    hence \<open>x = (projection (orthogonal_complement (space_as_set C))) x
              + (projection (space_as_set C)) x\<close>
      by (metis ordered_field_class.sign_simps(2))
    moreover have \<open>(projection (orthogonal_complement (space_as_set C))) x \<in> space_as_set B\<close>
      using x2
      by (meson closure_subset image_subset_iff that)
    moreover have \<open>(projection (space_as_set C)) x \<in> space_as_set C\<close>
      by (simp add: p1 projection_intro2)
    ultimately show ?thesis
      using closure_subset by fastforce 
  qed
  have x1: \<open>x \<in> (space_as_set B +\<^sub>M space_as_set C)\<close>
    if "x \<in> space_as_set A"
    for x
  proof -
    have f1: "x \<in> closure {a + b |a b. a \<in> space_as_set B \<and> b \<in> space_as_set C}"
      by (simp add: q1 that)
    have "{a + b |a b. a \<in> space_as_set B \<and> b \<in> space_as_set C} = {a. \<exists>p. p \<in> space_as_set B 
      \<and> (\<exists>q. q \<in> space_as_set C \<and> a = p + q)}"
      by blast
    hence "x \<in> closure {a. \<exists>b\<in>space_as_set B. \<exists>c\<in>space_as_set C. a = b + c}"
      using f1 by (simp add: Bex_def_raw)
    thus ?thesis
      using that
      unfolding closed_sum_def set_plus_def
      by blast
  qed

  hence \<open>x \<in> space_as_set
               (Abs_clinear_space (space_as_set B +\<^sub>M space_as_set C))\<close>
    if "x \<in> space_as_set A"
    for x
    using that
    by (metis space_as_set_inverse sup_clinear_space.rep_eq)
  thus ?thesis 
    by (simp add: x1 less_eq_clinear_space.rep_eq subset_eq sup_clinear_space.rep_eq)
qed


subsection \<open>Kernel\<close>

lift_definition kernel :: "'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector
   \<Rightarrow> 'a clinear_space" 
  is "\<lambda> f. f -` {0}"
  by (metis ker_op_lin)

definition eigenspace :: "complex \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'a \<Rightarrow> 'a clinear_space" where
  "eigenspace a A = kernel (A - a *\<^sub>C idOp)" 

lemma kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a *\<^sub>C A) = kernel A"
  for a :: complex and A :: "(_,_) cblinfun"
  apply transfer
  using complex_vector.scale_eq_0_iff by blast

lemma kernel_0[simp]: "kernel 0 = top"
proof-
  have x1: \<open>(\<lambda> _. 0) -` {0} = UNIV\<close>
    using Collect_cong UNIV_def
    by blast
  hence \<open>(cblinfun_apply (cblinfun_of_blinfun 0)) -` {0} = UNIV\<close>
    by (metis cblinfun_of_blinfun_zero cr_blinfun_def blinfun.pcr_cr_eq blinfun_of_cblinfun.rep_eq 
        blinfun_of_cblinfun_zero zero_blinfun.transfer)
  hence \<open>Abs_clinear_space ( (cblinfun_apply (cblinfun_of_blinfun 0)) -` {0} )
       = Abs_clinear_space UNIV\<close>
    using Abs_clinear_space_inject
    by (simp add: \<open>(cblinfun_apply (cblinfun_of_blinfun 0)) -` {0} = UNIV\<close>)
  thus ?thesis
    unfolding kernel_def zero_cblinfun_def top_clinear_space_def
    by (simp add: cBlinfun_inverse x1)   
qed

lemma kernel_id[simp]: "kernel idOp = 0"
  unfolding kernel_def
  apply transfer
  by (simp add: bot_clinear_space.abs_eq)


lemma scaleC_eigenspace[simp]: 
  assumes a1: "a \<noteq> 0"
  shows "eigenspace b (a *\<^sub>C A) = eigenspace (b/a) A"
proof -
  have "b *\<^sub>C (idOp::('a, _) cblinfun) = a *\<^sub>C (b / a) *\<^sub>C idOp"
    using a1
    by (metis ceq_vector_fraction_iff)
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

lemma inv_option_Some: 
  assumes "surj \<pi>"
  shows "inv_option (Some o \<pi>) = Some o (Hilbert_Choice.inv \<pi>)"
proof-
  have "(if Some y \<in> range (\<lambda>x. Some (\<pi> x))
          then Some (SOME x. Some (\<pi> x) = Some y)
          else None) =
         Some (SOME b. \<pi> b = y)"
    if "surj \<pi>"
    for y
    using that by auto
  hence  "surj \<pi> \<Longrightarrow>
    (\<lambda>y. if Some y \<in> range (\<lambda>x. Some (\<pi> x))
         then Some (SOME x. Some (\<pi> x) = Some y) else None) =
    (\<lambda>x. Some (SOME xa. \<pi> xa = x))"
    by (rule ext) 
  thus ?thesis 
    unfolding inv_option_def o_def inv_def
    using assms by linarith
qed


lemma inj_option_map_comp[simp]: 
  assumes a1: "inj_option f" and a2: "inj_option g" 
  shows "inj_option (f \<circ>\<^sub>m g)"
  using a1 a2
  unfolding inj_option_def
  by (metis (mono_tags, lifting) map_comp_def option.case_eq_if option.expand)

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


lemma isProjector_D1: 
  assumes "isProjector P"
  shows "P o\<^sub>C\<^sub>L P = P"
  using assms
  unfolding isProjector_def
  using assms isProjector_algebraic by auto


lemma isProjector_D2:
  assumes "isProjector P"
  shows "P* = P"
  using assms
  unfolding isProjector_def
  by (metis isProjector_algebraic isProjector_def) 


lemma isProjector_I: 
  assumes "P o\<^sub>C\<^sub>L P = P" and "P* = P"
  shows "isProjector P"
  using assms
  unfolding isProjector_def
  by (metis (mono_tags, lifting) isProjector_algebraic isProjector_def) 

lemma isProjector0[simp]: "isProjector ( 0::('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a) )"
  by (simp add: isProjector_I)

lemma isProjectoridMinus[simp]: 
  assumes a1: "isProjector P"
  shows "isProjector (idOp-P)"
proof-
  have f1: "P o\<^sub>C\<^sub>L P = P \<and> P* = P"
    using isProjector_algebraic a1 by auto
  hence "(idOp - P) o\<^sub>C\<^sub>L (idOp - P) = ((idOp - P) o\<^sub>C\<^sub>L (idOp - P))*"
    by auto
  hence x1: "(idOp - P) o\<^sub>C\<^sub>L (idOp - P) = idOp - P"
    using f1 by (simp add: timesOp_minus)
  have x2: "(idOp - P)* = idOp - P"
    using a1
    by (simp add: isProjector_algebraic)
  show ?thesis 
    using x1 x2 isProjector_I by blast
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


lemma isCont_applyOp[simp]: "isCont ((*\<^sub>V) A) \<psi>"
  apply transfer
  by (simp add: bounded_linear_continuous) 

lemma applyOpSpace_mono:
  assumes a1: "S \<le> T"
  shows "A *\<^sub>S S \<le> A *\<^sub>S T"
  using a1
  by (simp add: applyOpSpace.rep_eq closure_mono image_mono less_eq_clinear_space.rep_eq)

lemma apply_left_neutral:
  assumes "A o\<^sub>C\<^sub>L B = B" and "\<psi> \<in> space_as_set (B *\<^sub>S top)"
  shows "A *\<^sub>V \<psi> = \<psi>" 
proof-
  define rangeB rangeB' where "rangeB = space_as_set (B *\<^sub>S top)" 
    and "rangeB' = range (cblinfun_apply B)"
  from assms have "\<psi> \<in> closure rangeB'"
    by (simp add: applyOpSpace.rep_eq rangeB'_def top_clinear_space.rep_eq)

  then obtain \<psi>i where \<psi>i_lim: "\<psi>i \<longlonglongrightarrow> \<psi>" and \<psi>i_B: "\<psi>i i \<in> rangeB'" for i
    using closure_sequential by blast
  have A_invariant: "A *\<^sub>V \<psi>i i = \<psi>i i" 
    for i
  proof-
    from \<psi>i_B obtain \<phi> where \<phi>: "\<psi>i i = B *\<^sub>V \<phi>"
      using rangeB'_def by blast      
    hence "A *\<^sub>V \<psi>i i = (A o\<^sub>C\<^sub>L B) *\<^sub>V \<phi>"
      by (simp add: timesOp.rep_eq)
    also have "\<dots> = B *\<^sub>V \<phi>"
      by (simp add: assms)
    also have "\<dots> = \<psi>i i"
      by (simp add: \<phi>)
    finally show ?thesis.
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
proof-
  from assms have "top = U* *\<^sub>S U *\<^sub>S top"
    by (metis adjUU applyOpSpace_id cblinfun_apply_assoc_clinear_space)
  also have "\<dots> \<le> U* *\<^sub>S top"
    by (simp add: applyOpSpace_mono)
  finally show ?thesis
    using top.extremum_unique by blast
qed


lemma mult_INF_general[simp]: 
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space clinear_space"
    and U :: "'b \<Rightarrow>\<^sub>C\<^sub>L'c::chilbert_space"
    and Uinv :: "'c \<Rightarrow>\<^sub>C\<^sub>L'b" 
  assumes UinvUUinv: "Uinv o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Uinv = Uinv"
    and UUinvU: "U o\<^sub>C\<^sub>L Uinv o\<^sub>C\<^sub>L U = U"
    and V: "\<And>i. V i \<le> Uinv *\<^sub>S top"
  shows "U *\<^sub>S (INF i. V i) = (INF i. U *\<^sub>S V i)"
proof (rule antisym)
  show "U *\<^sub>S (INF i. V i) \<le> (INF i. U *\<^sub>S V i)"
    by (rule mult_INF1)
next
  define rangeU rangeUinv where "rangeU = U *\<^sub>S top" and "rangeUinv = Uinv *\<^sub>S top"
  define INFUV INFV where INFUV_def: "INFUV = (INF i. U *\<^sub>S V i)" and INFV_def: "INFV = (INF i. V i)"
  from assms have "V i \<le> rangeUinv" 
    for i
    unfolding rangeUinv_def by simp
  moreover have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeUinv" 
    for \<psi>
    using UinvUUinv apply_left_neutral rangeUinv_def that by auto
  ultimately have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set (V i)" 
    for \<psi> i
    using less_eq_clinear_space.rep_eq that by blast
  hence d1: "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>S (V i) = (V i)" for i
  proof transfer
    show "closure ((Uinv \<circ> U) ` V i) = V i"
      if "pred_fun \<top> closed_subspace V"
        and "cbounded_linear Uinv"
        and "cbounded_linear U"
        and "\<And>\<psi> i. \<psi> \<in> V i \<Longrightarrow> (Uinv \<circ> U) \<psi> = \<psi>"
      for V :: "'a \<Rightarrow> 'b set"
        and Uinv :: "'c \<Rightarrow> 'b"
        and U :: "'b \<Rightarrow> 'c"
        and i :: 'a
      using that proof auto
      show "x \<in> V i"
        if "\<forall>x. closed_subspace (V x)"
          and "cbounded_linear Uinv"
          and "cbounded_linear U"
          and "\<And>\<psi> i. \<psi> \<in> V i \<Longrightarrow> Uinv (U \<psi>) = \<psi>"
          and "x \<in> closure (V i)"
        for x :: 'b
        using that
        by (metis OrthoClosedEq closed_subspace.subspace orthogonal_complement_twice subspace_I) 
      show "x \<in> closure (V i)"
        if "\<forall>x. closed_subspace (V x)"
          and "cbounded_linear Uinv"
          and "cbounded_linear U"
          and "\<And>\<psi> i. \<psi> \<in> V i \<Longrightarrow> Uinv (U \<psi>) = \<psi>"
          and "x \<in> V i"
        for x :: 'b
        using that
        using setdist_eq_0_sing_1 setdist_sing_in_set
        by blast  
    qed
  qed     
  have "U *\<^sub>S V i \<le> rangeU" for i
    by (simp add: applyOpSpace_mono rangeU_def)
  hence "INFUV \<le> rangeU"
    unfolding INFUV_def by (meson INF_lower UNIV_I order_trans)
  moreover have "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeU" for \<psi>
    using UUinvU apply_left_neutral rangeU_def that by auto
  ultimately have x: "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set INFUV" for \<psi>
    by (simp add: in_mono less_eq_clinear_space.rep_eq that)

  have "closure ((U \<circ> Uinv) ` INFUV) = INFUV"
    if "closed_subspace INFUV"
      and "cbounded_linear U"
      and "cbounded_linear Uinv"
      and "\<And>\<psi>. \<psi> \<in> INFUV \<Longrightarrow> (U \<circ> Uinv) \<psi> = \<psi>"
    for INFUV :: "'c set"
      and U :: "'b \<Rightarrow> 'c"
      and Uinv :: "'c \<Rightarrow> 'b"
    using that proof auto
    show "x \<in> INFUV"
      if "closed_subspace INFUV"
        and "cbounded_linear U"
        and "cbounded_linear Uinv"
        and "\<And>\<psi>. \<psi> \<in> INFUV \<Longrightarrow> U (Uinv \<psi>) = \<psi>"
        and "x \<in> closure INFUV"
      for x :: 'c
      using that
      by (metis OrthoClosedEq closed_subspace.subspace orthogonal_complement_twice subspace_I) 
    show "x \<in> closure INFUV"
      if "closed_subspace INFUV"
        and "cbounded_linear U"
        and "cbounded_linear Uinv"
        and "\<And>\<psi>. \<psi> \<in> INFUV \<Longrightarrow> U (Uinv \<psi>) = \<psi>"
        and "x \<in> INFUV"
      for x :: 'c
      using that
      using setdist_eq_0_sing_1 setdist_sing_in_set
      by (simp add: closed_subspace.closed)  
  qed
  hence "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>S INFUV = INFUV"
    by (metis (mono_tags, hide_lams) x applyOpSpace.rep_eq applyOpSpace_id apply_idOp image_cong 
        space_as_set_inject)
  hence "INFUV = U *\<^sub>S Uinv *\<^sub>S INFUV"
    by (simp add: cblinfun_apply_assoc_clinear_space)
  also have "\<dots> \<le> U *\<^sub>S (INF i. Uinv *\<^sub>S U *\<^sub>S V i)"
    unfolding INFUV_def
    by (metis applyOpSpace_mono mult_INF1)    
  also have "\<dots> = U *\<^sub>S INFV"
    using d1
    by (metis (no_types, lifting) Sup.SUP_cong \<open>INFV \<equiv> \<Sqinter> (range V)\<close> 
        cblinfun_apply_assoc_clinear_space)
  finally show "INFUV \<le> U *\<^sub>S INFV".
qed

lemma mult_INF[simp]: 
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space clinear_space" 
    and U :: "'b \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space"
  assumes \<open>isometry U\<close>
  shows "U *\<^sub>S (INF i. V i) = (INF i. U *\<^sub>S V i)"
proof -
  from \<open>isometry U\<close> have "U* o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L U* = U*"
    unfolding isometry_def by simp
  moreover from \<open>isometry U\<close> have "U o\<^sub>C\<^sub>L U* o\<^sub>C\<^sub>L U = U"
    unfolding isometry_def
    by (simp add: cblinfun_apply_assoc)
  moreover have "V i \<le> U* *\<^sub>S top" for i
    by (simp add: range_adjoint_isometry assms)
  ultimately show ?thesis
    by (rule mult_INF_general)
qed

lemma leq_INF[simp]:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space clinear_space"
  shows "(A \<le> (INF x. V x)) = (\<forall>x. A \<le> V x)"
  by (simp add: le_Inf_iff)

lemma times_applyOp: "(A o\<^sub>C\<^sub>L B) *\<^sub>V \<psi> = A *\<^sub>V (B *\<^sub>V \<psi>)"
  apply transfer by simp

lemma mult_inf_distrib[simp]:
  fixes U::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
    and X Y::"'a clinear_space"
  assumes "isometry U"
  shows "U *\<^sub>S (inf X Y) = inf (U *\<^sub>S X) (U *\<^sub>S Y)"
  using mult_INF[where V="\<lambda>b. if b then X else Y" and U=U]
  unfolding INF_UNIV_bool_expand
  using assms by auto

lemma applyOp_scaleC1[simp]: "(c *\<^sub>C A) *\<^sub>V \<psi> = c *\<^sub>C (A *\<^sub>V \<psi>)"
  apply transfer by simp

lemma applyOp_scaleC2[simp]: "A *\<^sub>V (c *\<^sub>C \<psi>) = c *\<^sub>C (A *\<^sub>V \<psi>)"
  by (simp add: cblinfun_apply_scaleC)

definition bifunctional :: \<open>'a \<Rightarrow> (('a \<Rightarrow> complex) \<Rightarrow> complex)\<close> where
  \<open>bifunctional x = (\<lambda>f. f x)\<close>

lift_definition Bifunctional' :: \<open>'a::complex_normed_vector \<Rightarrow> (('a, complex) cblinfun \<Rightarrow> complex)\<close>
  is bifunctional.

lift_definition Bifunctional :: \<open>'a::complex_normed_vector \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L complex) \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  is Bifunctional'
proof
  fix a :: 'a and b b1 b2 and r :: complex
  show "Bifunctional' a (b1 + b2) = Bifunctional' a b1 + Bifunctional' a b2"
    by (simp add: Bifunctional'.rep_eq bifunctional_def plus_cblinfun.rep_eq)
  show "Bifunctional' a (r *\<^sub>C b) = r *\<^sub>C Bifunctional' a b"
    by (simp add: Bifunctional'.rep_eq bifunctional_def)    

  have "\<exists>K. \<forall>x. cbounded_linear x \<longrightarrow>
            cmod (bifunctional a x) \<le> onorm x * K"
    for a::'a
    unfolding bifunctional_def
    using cbounded_linear.bounded_linear onorm by blast
  hence x1: "\<exists>K. \<forall>x\<in>Collect cbounded_linear. cmod (bifunctional (a::'a) x) \<le> onorm x * K"
    for a :: 'a
    by auto 
  show "\<exists>K. \<forall>x. cmod (Bifunctional' (a::'a) x) \<le> norm x * K"
    for a :: 'a
    apply transfer
    using x1.     
qed

lemma norm_of_cblinfun:
  \<open>norm (L *\<^sub>V z) \<le> norm z * norm L\<close>
  apply transfer
  using cbounded_linear.bounded_linear onorm
  by (simp add: cbounded_linear.bounded_linear onorm algebra_simps)

lemma norm_of_cblinfun1:
  assumes a1: "norm z = 1"
  shows  "norm (L *\<^sub>V z) \<le> norm L"
  using a1 norm_of_cblinfun
  by (metis mult_cancel_right1) 

lemma norm_of_cblinfun2:
  assumes a1: "norm z \<le> 1"
  shows "norm (L *\<^sub>V z) \<le> norm L"
  using a1 proof (cases \<open>z = 0\<close>)
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
  have "x \<le> a"
    if "x \<in> X"
    for x
  proof-
    obtain x' where x2: "x = norm (S x')" and x3: "norm x' < 1"
      using that X_def \<open>x \<in> X\<close> by auto 
    have "norm (S x') \<le> onorm S"
      using x3 a2 onormless1 cbounded_linear.bounded_linear by auto
    hence "x \<le> onorm S"
      by (simp add: x2) 
    thus ?thesis
      unfolding X_def a_def
      by simp 
  qed
  moreover have "a \<le> y" 
    if b1: "\<And>x. x \<in> X \<Longrightarrow> x \<le> y"
    for y
  proof-
    have f1: "norm t < 1 \<Longrightarrow> norm (S t) \<le> y" for t
      using b1
      unfolding X_def by blast 
    have "onorm S \<le> y+e" 
      if e0:"e>0"      
      for e
    proof-
      have \<open>cbounded_linear S\<close>
        using a2
        by (simp add: cbounded_linear.bounded_linear)
      hence "onorm S = Sup { norm (S t) |t. norm t = 1 }"
        using a1 onorm_sphere[where f = S]
        by (simp add: cbounded_linear.bounded_linear)
      hence u1: "onorm S - e/2 < Sup { norm (S t) |t. norm t = 1 }"
        by (simp add: e0)        
      moreover have u2: "{ norm (S t) |t. norm t = 1 } \<noteq> {}"
      proof-
        have "\<exists>t::'a. norm t = 1"
          using a1 ex_norm1
          by (simp add: ex_norm1) 
        thus ?thesis
          by simp 
      qed
      ultimately have u3: "\<exists>T\<in>{ norm (S t) |t. norm t = 1 }. onorm S - e/2 \<le> T"
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

definition invertible_cblinfun::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun \<Rightarrow> bool\<close> where
  \<open>invertible_cblinfun A = (\<exists> B. A o\<^sub>C\<^sub>L B = idOp \<and> B o\<^sub>C\<^sub>L A = idOp)\<close>

definition invert_cblinfun::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun \<Rightarrow> ('b,'a) cblinfun\<close> where
  \<open>invert_cblinfun A = (THE B. A o\<^sub>C\<^sub>L B = idOp \<and> B o\<^sub>C\<^sub>L A = idOp)\<close>

(*


lemma invert_cblinfun_uniq':
  \<open>A o\<^sub>C\<^sub>L B = idOp \<Longrightarrow> B o\<^sub>C\<^sub>L A = idOp \<Longrightarrow> A o\<^sub>C\<^sub>L B' = idOp \<Longrightarrow> B' o\<^sub>C\<^sub>L A = idOp \<Longrightarrow> B = B'\<close>
proof-
  assume \<open>A o\<^sub>C\<^sub>L B = idOp\<close> and \<open>B o\<^sub>C\<^sub>L A = idOp\<close> and \<open>A o\<^sub>C\<^sub>L B' = idOp\<close> and \<open>B' o\<^sub>C\<^sub>L A = idOp\<close>
  
  thus ?thesis
    by (metis \<open>A o\<^sub>C\<^sub>L B' = idOp\<close> \<open>B o\<^sub>C\<^sub>L A = idOp\<close> cblinfun_apply_assoc times_idOp1 times_idOp2) 
qed


*)

lemma invert_cblinfun_well_defined:
  assumes a1: "invertible_cblinfun A"
  shows "\<exists>!B. A o\<^sub>C\<^sub>L B = idOp \<and> B o\<^sub>C\<^sub>L A = idOp"
proof-
  have \<open>B *\<^sub>V x = B' *\<^sub>V x\<close>
    if \<open>A o\<^sub>C\<^sub>L B = idOp\<close> and \<open>B o\<^sub>C\<^sub>L A = idOp\<close> and \<open>A o\<^sub>C\<^sub>L B' = idOp\<close> and \<open>B' o\<^sub>C\<^sub>L A = idOp\<close>
    for A::"'a \<Rightarrow>\<^sub>C\<^sub>L 'b" and B B' and x
  proof-
    have \<open>(A o\<^sub>C\<^sub>L B) *\<^sub>V x = x\<close>
      using \<open>A o\<^sub>C\<^sub>L B = idOp\<close>
      by simp
    hence u1: \<open>B' *\<^sub>V ((A o\<^sub>C\<^sub>L B) *\<^sub>V x) = B' *\<^sub>V x\<close>
      by simp
    have \<open>B' *\<^sub>V ((A o\<^sub>C\<^sub>L B) *\<^sub>V x) = B' *\<^sub>V (A *\<^sub>V (B *\<^sub>V x))\<close>
      by (simp add: times_applyOp)
    also have \<open>\<dots> = (B' o\<^sub>C\<^sub>L A) *\<^sub>V (B *\<^sub>V x)\<close>
      by (simp add: times_applyOp)
    also have \<open>\<dots> = idOp *\<^sub>V (B *\<^sub>V x)\<close>
      by (simp add: \<open>B' o\<^sub>C\<^sub>L A = idOp\<close>)
    also have \<open>\<dots> = B *\<^sub>V x\<close>
      by simp
    finally have u2: \<open>B' *\<^sub>V ((A o\<^sub>C\<^sub>L B) *\<^sub>V x) = B *\<^sub>V x\<close>
      by blast
    show ?thesis
      using u1 u2
      by auto
  qed
  thus ?thesis
    by (metis (no_types, lifting) assms cblinfun_apply_assoc invertible_cblinfun_def times_idOp1 
        times_idOp2) 
qed

lemma invert_cblinfun_left:
  assumes a1: "invertible_cblinfun A"
  shows "(invert_cblinfun A) o\<^sub>C\<^sub>L A = idOp"
proof-
  have \<open>\<exists>! B. A o\<^sub>C\<^sub>L B = idOp \<and> B o\<^sub>C\<^sub>L A = idOp\<close>
    using a1 invert_cblinfun_well_defined by blast
  hence \<open>A o\<^sub>C\<^sub>L (invert_cblinfun A) = idOp \<and> (invert_cblinfun A) o\<^sub>C\<^sub>L A = idOp\<close>
    unfolding invert_cblinfun_def
    by (smt theI)
  thus ?thesis by blast
qed

lemma invert_cblinfun_right:
  assumes a1: \<open>invertible_cblinfun A\<close>
  shows \<open>A o\<^sub>C\<^sub>L (invert_cblinfun A) = idOp\<close>
proof-
  have \<open>\<exists>!B. A o\<^sub>C\<^sub>L B = idOp \<and> B o\<^sub>C\<^sub>L A = idOp\<close>
    using a1 invert_cblinfun_well_defined by blast
  hence \<open>A o\<^sub>C\<^sub>L (invert_cblinfun A) = idOp \<and> (invert_cblinfun A) o\<^sub>C\<^sub>L A = idOp\<close>
    unfolding invert_cblinfun_def
    by (smt theI)
  thus ?thesis by blast
qed

lemma invert_cblinfun_uniq:
  assumes a1: "A o\<^sub>C\<^sub>L B = idOp" and a2: "B o\<^sub>C\<^sub>L A = idOp"
  shows "invert_cblinfun A = B"
  using a1 a2 invert_cblinfun_left invert_cblinfun_right  invertible_cblinfun_def 
    invert_cblinfun_well_defined by fastforce 

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


lemma timesScalarSpace_0[simp]: "0 *\<^sub>S S = (0::_::{complex_vector,t1_space} clinear_space)"
proof (auto, transfer)
  fix S :: "'b set"
  assume "closed_subspace S"
  hence "0 \<in> S"
    unfolding closed_subspace_def complex_vector.subspace_def 
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
  for B::\<open>'a::complex_normed_vector clinear_space\<close>
  by simp

(* TODO: identical to cblinfun_apply_assoc_subspace *)
lemma cblinfun_apply_assoc_subspace: "(A o\<^sub>C\<^sub>L B) *\<^sub>S S =  A *\<^sub>S (B *\<^sub>S S)"
  by (simp add: cblinfun_apply_assoc_clinear_space) 


lift_definition vector_to_cblinfun :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L'a\<close> is
  \<open>\<lambda>\<psi> \<phi>. one_dim_isom \<phi> *\<^sub>C \<psi>\<close>
  by (simp add: cbounded_linear_scaleC_const)

lemma vector_to_cblinfun_applyOp: 
  "vector_to_cblinfun (A *\<^sub>V \<psi>) = A  o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>)" 
  apply transfer 
  unfolding comp_def cbounded_linear_def clinear_def Vector_Spaces.linear_def
    module_hom_def module_hom_axioms_def
  by simp

lemma vector_to_cblinfun_scalar_times: 
  "vector_to_cblinfun (a *\<^sub>C \<psi>) = a *\<^sub>C vector_to_cblinfun \<psi>" for a::complex
proof (subst asm_rl [of "a *\<^sub>C \<psi> = (a *\<^sub>C idOp) *\<^sub>V \<psi>"])
  show "a *\<^sub>C \<psi> = a *\<^sub>C idOp *\<^sub>V \<psi>"
    by simp    
  show "vector_to_cblinfun (a *\<^sub>C idOp *\<^sub>V \<psi>) = a *\<^sub>C (vector_to_cblinfun \<psi>::'a \<Rightarrow>\<^sub>C\<^sub>L 'b)"
    by (metis apply_idOp scalar_op_op vector_to_cblinfun_applyOp)    
qed


lift_definition cblinfun_to_blinfun::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector 
  \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'b)\<close> 
  is \<open>(\<lambda>f. ((*\<^sub>V) f))\<close>
  apply transfer
  by (simp add: cbounded_linear.bounded_linear)

lemma cblinfun_to_blinfun_norm: "norm (cblinfun_to_blinfun F) = norm F"
  by (simp add: cblinfun_to_blinfun.rep_eq norm_blinfun.rep_eq norm_cblinfun.rep_eq)

theorem banach_steinhaus_cblinfun:
  fixes F :: \<open>'c \<Rightarrow> 'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<And>x. \<exists>M. \<forall> n.  norm ((F n) *\<^sub>V x) \<le> M\<close>
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
  fixes f::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  shows \<open>\<exists>!t. \<forall>x.  f *\<^sub>V x = \<langle>t, x\<rangle>\<close>
proof transfer
  show "\<exists>!t. \<forall>x. f x = \<langle>t, x\<rangle>"
    if "cbounded_linear f"
    for f :: "'a \<Rightarrow> complex"
    using that proof auto
    show "\<exists>t. \<forall>x. f x = \<langle>t, x\<rangle>"
      if "cbounded_linear f"
      using that
      by (simp add: riesz_frechet_representation_existence) 
    show "t = y"
      if "cbounded_linear f"
        and "\<forall>x. \<langle>y, x\<rangle> = \<langle>t, x\<rangle>"
        and "\<forall>x. f x = \<langle>t, x\<rangle>"
      for t :: 'a
        and y :: 'a
      using that    
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
  qed
qed

theorem riesz_frechet_representation_cblinfun_norm:
  includes notation_norm
  fixes f::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  assumes \<open>\<And>x.  f *\<^sub>V x = \<langle>t, x\<rangle>\<close>
  shows \<open>\<parallel>f\<parallel> = \<parallel>t\<parallel>\<close>
  using assms 
proof transfer
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
      using complex_of_real_cmod
      by (metis cinner_ge_zero)
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
  have "\<And>S. card S = n \<Longrightarrow> finite S \<Longrightarrow> F *\<^sub>V (\<Sum>a\<in>S. r a *\<^sub>C a) = (\<Sum>a\<in>S. r a *\<^sub>C (F *\<^sub>V a))"
    for n
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
  shows "vector_to_cblinfun \<phi> *\<^sub>V \<gamma> = one_dim_isom \<gamma> *\<^sub>C \<phi>"
  apply transfer by (rule refl)

lemma vector_to_cblinfun_adj_times_vec[simp]:
  includes cblinfun_notation
  shows "vector_to_cblinfun \<psi>* *\<^sub>V \<phi> = of_complex (cinner \<psi> \<phi>)"
proof -
  have "one_dim_isom (vector_to_cblinfun \<psi>* *\<^sub>V \<phi> :: 'a) 
        = cinner 1 (vector_to_cblinfun \<psi>* *\<^sub>V \<phi> :: 'a)"
    by (simp add: one_dim_isom_def)
  also have *: "\<dots> = cinner (vector_to_cblinfun \<psi> *\<^sub>V (1::'a)) \<phi>"
    by (metis adjoint_I adjoint_twice)
  also have "\<dots> = \<langle>\<psi>, \<phi>\<rangle>"
    by simp
  finally have "one_dim_isom (vector_to_cblinfun \<psi>* *\<^sub>V \<phi> :: 'a) = \<langle>\<psi>, \<phi>\<rangle>"
    using "*" by auto
  thus ?thesis
    by (metis one_dim_isom_eq_of_complex one_dim_isom_inverse)
qed

instantiation cblinfun :: (one_dim, one_dim) complex_inner begin
text \<open>Once we have a theory for the trace, we could instead define the Hilbert-Schmidt inner product
  and make cblinfun and relax the \<^class>\<open>one_dim\<close>-sort constraint\<close>
definition "cinner_cblinfun (A::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) (B::'a \<Rightarrow>\<^sub>C\<^sub>L 'b)
             = cnj (one_dim_isom (A *\<^sub>V 1)) * one_dim_isom (B *\<^sub>V 1)"
instance
proof intro_classes
  fix A B C :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    and c c' :: complex
  show "\<langle>A, B\<rangle> = cnj \<langle>B, A\<rangle>"
    unfolding cinner_cblinfun_def by auto
  show "\<langle>A + B, C\<rangle> = \<langle>A, C\<rangle> + \<langle>B, C\<rangle>"
    by (simp add: cinner_cblinfun_def algebra_simps plus_cblinfun.rep_eq) 
  show "\<langle>c *\<^sub>C A, B\<rangle> = cnj c * \<langle>A, B\<rangle>"
    unfolding cinner_cblinfun_def by auto
  show "0 \<le> \<langle>A, A\<rangle>"
    unfolding cinner_cblinfun_def by auto
  have "cbounded_linear A \<Longrightarrow> A 1 = 0 \<Longrightarrow> A = (\<lambda>_. 0)"
    for A::"'a \<Rightarrow> 'b"
  proof (rule one_dim_linear_eq [where x = 1] , auto)
    show "clinear A"
      if "cbounded_linear A"
        and "A 1 = 0"
      for A :: "'a \<Rightarrow> 'b"
      using that
      by (simp add: cbounded_linear.clinear)
    show "clinear ((\<lambda>_. 0)::'a \<Rightarrow> 'b)"
      if "cbounded_linear A"
        and "A 1 = 0"
      for A :: "'a \<Rightarrow> 'b"
      using that
      by (simp add: complex_vector.module_hom_zero) 
  qed
  hence "A *\<^sub>V 1 = 0 \<Longrightarrow> A = 0"
    by transfer
  hence "one_dim_isom (A *\<^sub>V 1) = 0 \<Longrightarrow> A = 0"
    by (metis one_dim_isom_0 one_dim_isom_inj)    
  thus "(\<langle>A, A\<rangle> = 0) = (A = 0)"
    by (auto simp: cinner_cblinfun_def)

  show "norm A = sqrt (cmod \<langle>A, A\<rangle>)"
    unfolding cinner_cblinfun_def 
    apply transfer 
    by (simp add: norm_mult abs_complex_def one_dim_onorm' cnj_x_x power2_eq_square cbounded_linear.clinear)
qed
end

instantiation cblinfun :: (one_dim, one_dim) one_dim begin
lift_definition one_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b" is "one_dim_isom"
  by (rule cbounded_linear_one_dim_isom)
lift_definition times_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  is "\<lambda>f g. f o one_dim_isom o g"
  by (simp add: comp_cbounded_linear)
lift_definition inverse_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" is
  "\<lambda>f. ((*) (one_dim_isom (inverse (f 1)))) o one_dim_isom"
  by (auto intro!: comp_cbounded_linear cbounded_linear_mult_right)
definition divide_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" where
  "divide_cblinfun A B = A * inverse B"
definition "canonical_basis_cblinfun = [1 :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b]"
definition "canonical_basis_length_cblinfun (_::('a \<Rightarrow>\<^sub>C\<^sub>L 'b) itself) = (1::nat)"
instance
proof intro_classes
  let ?basis = "canonical_basis :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) list"
  fix A B C :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    and c c' :: complex
  show "distinct ?basis"
    unfolding canonical_basis_cblinfun_def by simp
  have "(1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<noteq> (0::'a \<Rightarrow>\<^sub>C\<^sub>L 'b)"
    by (metis applyOp0 one_cblinfun.rep_eq one_dim_isom_one zero_neq_one)
  thus "cindependent (set ?basis)"
    unfolding canonical_basis_cblinfun_def by simp



  have "A \<in> cspan (set ?basis)" for A
  proof -
    define c :: complex where "c = one_dim_isom (A *\<^sub>V 1)"
    have "A x = one_dim_isom (A 1) *\<^sub>C one_dim_isom x" for x
      by (metis (mono_tags, hide_lams) applyOp_scaleC2 complex_vector.scale_left_commute mult.right_neutral of_complex_inner_1 of_complex_one_dim_isom one_dim_isom_def scaleC_conv_of_complex)
    hence "A = one_dim_isom (A *\<^sub>V 1) *\<^sub>C 1"
      apply transfer by metis
    thus "A \<in> cspan (set ?basis)"
      unfolding canonical_basis_cblinfun_def
      by (smt complex_vector.span_base complex_vector.span_scale list.set_intros(1))
  qed
  thus "cspan (set ?basis) = UNIV" by auto

  show "canonical_basis_length TYPE('a \<Rightarrow>\<^sub>C\<^sub>L 'b) = length ?basis"
    unfolding canonical_basis_length_cblinfun_def canonical_basis_cblinfun_def by simp


  have "A = (1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Longrightarrow>
    norm (1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = (1::real)"
    apply transfer by simp
  thus "A \<in> set ?basis \<Longrightarrow> norm A = 1"
    unfolding canonical_basis_cblinfun_def 
    by simp

  show "?basis = [1]"
    unfolding canonical_basis_cblinfun_def by simp
  show "c *\<^sub>C 1 * c' *\<^sub>C 1 = (c * c') *\<^sub>C (1::'a\<Rightarrow>\<^sub>C\<^sub>L'b)"
    apply transfer by auto
  have "(1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = (0::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Longrightarrow> False"
    by (metis applyOp0 one_cblinfun.rep_eq one_dim_isom_0' zero_neq_neg_one)
  thus "is_ortho_set (set ?basis)"
    unfolding is_ortho_set_def canonical_basis_cblinfun_def by auto
  show "A div B = A * inverse B"
    by (simp add: divide_cblinfun_def)
  show "inverse (c *\<^sub>C 1) = (1::'a\<Rightarrow>\<^sub>C\<^sub>L'b) /\<^sub>C c"
    apply transfer by (simp add: o_def one_dim_inverse)
qed
end

lemma one_dim_idOp: "1 = idOp"
  apply transfer by simp

lemma one_dim_times: 
  fixes A :: "'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a" and B :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'a"
  shows "A * B = A o\<^sub>C\<^sub>L B"
  apply transfer by simp

lemma one_comp_one_cblinfun[simp]: "1 o\<^sub>C\<^sub>L 1 = 1"
  apply transfer unfolding o_def by simp

lemma one_cblinfun_adj[simp]: "1* = 1"
proof (rule adjoint_D [symmetric])
  show "\<langle>1 *\<^sub>V x, y\<rangle> = \<langle>x, 1 *\<^sub>V y\<rangle>"
    for x :: 'a
      and y :: 'b
    apply transfer by (rule one_dim_isom_adjoint)
qed


lemma one_vector_to_cblinfun[simp]: 
  "(vector_to_cblinfun s :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L _) o\<^sub>C\<^sub>L 1 
     = (vector_to_cblinfun s :: 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)"
proof (transfer fixing: s)
  show "(\<lambda>\<phi>. one_dim_isom \<phi> *\<^sub>C s) \<circ> one_dim_isom = (\<lambda>\<phi>. one_dim_isom \<phi> *\<^sub>C s)"
    by (metis (full_types) comp_apply of_complex_inner_1 one_dim_isom_def)
qed

lemma norm_vector_to_cblinfun[simp]: "norm (vector_to_cblinfun x) = norm x"
proof transfer
  have "cbounded_linear (one_dim_isom::'a \<Rightarrow> complex)"
    by simp    
  moreover have "onorm (one_dim_isom::'a \<Rightarrow> complex) * norm x = norm x"
    for x :: 'b
    by simp
  ultimately show "onorm (\<lambda>\<phi>. one_dim_isom (\<phi>::'a) *\<^sub>C x) = norm x"
    for x :: 'b
    by (subst onorm_scaleC_left)
qed

lemma norm_cblinfun_times:
  "norm (A o\<^sub>C\<^sub>L B) \<le> norm A * norm B"
  apply transfer
  by (simp add: cbounded_linear.bounded_linear onorm_compose)

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
proof-
  have u1: "closure (A ` closure (complex_vector.span G))
         \<subseteq> closure (complex_vector.span (A ` G))"
    if "cbounded_linear A"
    for A :: "'b \<Rightarrow> 'a"
      and G :: "'b set"
  proof-
    have isContA: \<open>isCont A r\<close>
      for r
      using that
      by (simp add: bounded_linear_continuous)

    have "x \<in> closure (complex_vector.span (A ` G))"
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
    hence \<open>A ` closure (complex_vector.span G)
           \<subseteq> closure (complex_vector.span (A ` G))\<close>
      by blast
    thus ?thesis
      by (metis closure_closure closure_mono)       
  qed
  have u2: "closure (complex_vector.span (A ` G))
         \<subseteq> closure (A ` closure (complex_vector.span G))"
    if "cbounded_linear A"
    for A :: "'b \<Rightarrow> 'a"
      and G :: "'b set"
    using that
    by (simp add: cbounded_linear.clinear closure_mono closure_subset complex_vector.linear_span_image image_mono) 
  show ?thesis
    apply transfer
    using u1 u2
    by blast 
qed

lemma span_ortho_span:
  assumes "\<And>s t. s\<in>S \<Longrightarrow> t\<in>T \<Longrightarrow> is_orthogonal s t"
  shows "Span S \<le> - (Span T)"
proof-
  have u1: "x \<in> orthogonal_complement (closure (complex_vector.span T))"
    if "\<And>s t. \<lbrakk>s \<in> S; t \<in> T\<rbrakk> \<Longrightarrow> is_orthogonal s t"
      and "x \<in> closure (complex_vector.span S)"
    for S :: "'a set"
      and T :: "'a set"
      and x :: 'a
  proof-
    have discrete: \<open>\<langle> x, y \<rangle> = 0\<close>
      if t1: \<open>x \<in> complex_vector.span S\<close> and t2: \<open>y \<in> complex_vector.span T\<close>
      for x y
    proof-
      have \<open>\<exists>T' r\<^sub>T. finite T' \<and>  T' \<subseteq> T \<and> y = (\<Sum>a\<in>T'. r\<^sub>T a *\<^sub>C a)\<close>
        using complex_vector.span_explicit  \<open>y \<in> complex_vector.span T\<close>
        by (smt mem_Collect_eq)
      then obtain T' r\<^sub>T where \<open>finite T'\<close> and \<open>T' \<subseteq> T\<close> and \<open>y = (\<Sum>a\<in>T'. r\<^sub>T a *\<^sub>C a)\<close>
        by blast
      have \<open>\<exists>S' r\<^sub>S. finite S' \<and>  S' \<subseteq> S \<and> x = (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a)\<close>
        using complex_vector.span_explicit  \<open>x \<in> complex_vector.span S\<close>
        by (smt mem_Collect_eq)
      then obtain S' r\<^sub>S where \<open>finite S'\<close> and \<open>S' \<subseteq> S\<close> and \<open>x = (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a)\<close>
        by blast
      have x1: \<open>\<langle> a, r\<^sub>T b *\<^sub>C b \<rangle> =  r\<^sub>T b * \<langle> a, b \<rangle>\<close>
        for a b
        by simp

      have x2: \<open>a \<in> S' \<Longrightarrow> b \<in> T' \<Longrightarrow> \<langle> a, b \<rangle> = 0\<close>
        for a b
      proof-
        assume \<open>a \<in> S'\<close> and \<open>b \<in> T'\<close>
        have \<open>a \<in> S\<close>
          using \<open>S' \<subseteq> S\<close> \<open>a \<in> S'\<close> by blast            
        moreover have \<open>b \<in> T\<close>
          using \<open>T' \<subseteq> T\<close> \<open>b \<in> T'\<close> by blast
        ultimately show ?thesis
          using is_orthogonal_def \<open>\<And>t s. \<lbrakk>s \<in> S; t \<in> T\<rbrakk> \<Longrightarrow> is_orthogonal s t\<close> by blast
      qed

      have \<open>\<langle> x, y \<rangle> = \<langle> (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a), (\<Sum>b\<in>T'. r\<^sub>T b *\<^sub>C b) \<rangle>\<close>
        by (simp add: \<open>x = (\<Sum>a\<in>S'. r\<^sub>S a *\<^sub>C a)\<close> \<open>y = (\<Sum>a\<in>T'. r\<^sub>T a *\<^sub>C a)\<close>)
      also have \<open>\<dots> = (\<Sum>a\<in>S'. \<langle> r\<^sub>S a *\<^sub>C a, (\<Sum>b\<in>T'. r\<^sub>T b *\<^sub>C b) \<rangle>)\<close>
        using cinner_sum_left by blast
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. \<langle> r\<^sub>S a *\<^sub>C a,  r\<^sub>T b *\<^sub>C b \<rangle>))\<close>
        by (simp add: cinner_sum_right)
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. (cnj (r\<^sub>S a)) * \<langle> a,  r\<^sub>T b *\<^sub>C b \<rangle>))\<close>
        by (meson cinner_scaleC_left sum.cong)
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. (cnj (r\<^sub>S a)) * ((r\<^sub>T b) * \<langle> a, b \<rangle>)))\<close>
        apply transfer
        using x1
        by auto 
      also have \<open>\<dots> = (\<Sum>a\<in>S'. (\<Sum>b\<in>T'. (cnj (r\<^sub>S a)) * ((r\<^sub>T b) * 0)))\<close>
        by (simp add: x2)        
      finally show \<open>\<langle> x, y \<rangle> = 0\<close> by simp
    qed
    have \<open>\<langle> x, y \<rangle> = 0\<close>
      if \<open>y \<in> complex_vector.span T\<close>
      for y
    proof-
      have \<open>\<exists>t. t \<longlonglongrightarrow> x \<and> (\<forall> n. t n \<in> complex_vector.span S)\<close>
        using closure_sequential \<open>x \<in> closure (cspan S)\<close>
        by metis        
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
    hence \<open>\<langle> x, y \<rangle> = 0\<close>
      if \<open>y \<in> closure (complex_vector.span T)\<close>
      for y
    proof-
      have \<open>\<exists> t. t \<longlonglongrightarrow> y \<and> (\<forall> n. t n \<in> complex_vector.span T)\<close>
        using that closure_sequential by blast
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
  thus ?thesis
    by (metis Span.rep_eq assms clinear_space_leI uminus_clinear_space.rep_eq) 
qed

definition "positive_op A = (\<exists>B::'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'a. A = B* o\<^sub>C\<^sub>L B)"

lemma timesOp0[simp]: "0 o\<^sub>C\<^sub>L A = 0"
  apply transfer
  by (simp add: K_record_comp) 

lemma timesOp0'[simp]: "A o\<^sub>C\<^sub>L 0 = 0"
  using Bounded_Operators.OCL_zero by auto

lemma positive_idOp[simp]: "positive_op idOp"
  unfolding positive_op_def apply (rule exI[of _ idOp]) by simp

lemma positive_0[simp]: "positive_op 0"
  unfolding positive_op_def apply (rule exI[of _ 0]) by auto

abbreviation "loewner_leq A B == (positive_op (B-A))"


lemma norm_mult_ineq_cblinfun:
  fixes A B
  shows "norm (A o\<^sub>C\<^sub>L B) \<le> norm A * norm B"
  apply transfer
  by (simp add: cbounded_linear.bounded_linear onorm_compose)


lemma Ortho_expansion_finite:
  includes notation_norm
  fixes T::\<open>'a::complex_inner set\<close>
  assumes a1: \<open>complex_vector.span T = UNIV\<close> and a2: \<open>finite T\<close> and a3: \<open>is_ortho_set T\<close>
    and a4: \<open>\<And>t. t\<in>T \<Longrightarrow> \<parallel>t\<parallel> = 1\<close>
  shows \<open>x = (\<Sum>t\<in>T. \<langle> t, x \<rangle> *\<^sub>C t)\<close>
proof-
  have \<open>closure (complex_vector.span T)  = complex_vector.span T\<close>
    using \<open>finite T\<close> span_finite_dim by blast
  have \<open>{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> T} = {\<Sum>a\<in>T. r a *\<^sub>C a |r. True}\<close>
    by (metis (mono_tags) UNIV_I a1 a2 a3 cdependent_raw_def is_ortho_set_independent 
        span_explicit_finite subset_refl)

  have f1: "\<forall>A. {a. \<exists>Aa f. (a::'a) = (\<Sum>a\<in>Aa. f a *\<^sub>C a) \<and> finite Aa \<and> Aa \<subseteq> A} = cspan A"
    by (simp add: complex_vector.span_explicit)      
  have f2: "\<forall>a. (\<exists>f. a = (\<Sum>a\<in>T. f a *\<^sub>C a)) \<or> (\<forall>A. (\<forall>f. a \<noteq> (\<Sum>a\<in>A. f a *\<^sub>C a)) \<or> infinite A \<or> \<not> A \<subseteq> T)"
    using \<open>{\<Sum>a\<in>t. r a *\<^sub>C a |t r. finite t \<and> t \<subseteq> T} = {\<Sum>a\<in>T. r a *\<^sub>C a |r. True}\<close> by auto
  have f3: "\<forall>A a. (\<exists>Aa f. (a::'a) = (\<Sum>a\<in>Aa. f a *\<^sub>C a) \<and> finite Aa \<and> Aa \<subseteq> A) \<or> a \<notin> cspan A"
    using f1 by blast
  have "cspan T = UNIV"
    by (metis (full_types, lifting)  \<open>complex_vector.span T = UNIV\<close>)
  hence \<open>\<exists> r. x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    using f3 f2 by blast
  then obtain r where \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
    by blast

  have \<open>r a = \<langle>a, x\<rangle>\<close>
    if \<open>a \<in> T\<close>
    for a
  proof-
    have \<open>norm a = 1\<close>
      using a4
      by (simp add: \<open>a \<in> T\<close>)
    moreover have \<open>norm a = sqrt (norm \<langle>a, a\<rangle>)\<close>
      using norm_eq_sqrt_cinner by auto        
    ultimately have \<open>sqrt (norm \<langle>a, a\<rangle>) = 1\<close>
      by simp
    hence \<open>norm \<langle>a, a\<rangle> = 1\<close>
      using real_sqrt_eq_1_iff by blast
    moreover have \<open>\<langle>a, a\<rangle> \<in> \<real>\<close>
      by (simp add: cinner_real)        
    moreover have \<open>\<langle>a, a\<rangle> \<ge> 0\<close>
      using cinner_ge_zero by blast
    ultimately have w1: \<open>\<langle>a, a\<rangle> = 1\<close>
      by (metis \<open>0 \<le> \<langle>a, a\<rangle>\<close> \<open>cmod \<langle>a, a\<rangle> = 1\<close> complex_of_real_cmod of_real_1)

    have \<open>r t * \<langle>a, t\<rangle> = 0\<close> if \<open>t \<in> T-{a}\<close> for t
      by (metis DiffD1 DiffD2 \<open>a \<in> T\<close> a3 is_ortho_set_def mult_eq_0_iff singletonI that)
    hence s1: \<open>(\<Sum> t\<in>T-{a}. r t * \<langle>a, t\<rangle>) = 0\<close>
      by (simp add: \<open>\<And>t. t \<in> T - {a} \<Longrightarrow> r t * \<langle>a, t\<rangle> = 0\<close>) 
    have \<open>\<langle>a, x\<rangle> = \<langle>a, (\<Sum> t\<in>T. r t *\<^sub>C t)\<rangle>\<close>
      using \<open>x = (\<Sum> a\<in>T. r a *\<^sub>C a)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum> t\<in>T. \<langle>a, r t *\<^sub>C t\<rangle>)\<close>
      using cinner_sum_right by blast
    also have \<open>\<dots> = (\<Sum> t\<in>T. r t * \<langle>a, t\<rangle>)\<close>
      by simp    
    also have \<open>\<dots> = r a * \<langle>a, a\<rangle> + (\<Sum> t\<in>T-{a}. r t * \<langle>a, t\<rangle>)\<close>
      using \<open>a \<in> T\<close>
      by (meson assms(2) sum.remove)
    also have \<open>\<dots> = r a * \<langle>a, a\<rangle>\<close>
      using s1
      by simp
    also have \<open>\<dots> = r a\<close>
      by (simp add: w1)
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
    have x1: \<open>X n = (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t)\<close>
      for n
      using Ortho_expansion_finite[where T = "set canonical_basis" and x = "X n"]
        \<open>finite (set canonical_basis)\<close> 
      by (smt  is_generator_set is_normal is_orthonormal)

    have \<open>(\<lambda> n. \<langle> t, X n \<rangle> *\<^sub>C t) \<longlonglongrightarrow> L t *\<^sub>C t\<close> 
      if r1: \<open>t\<in>set canonical_basis\<close>
      for t
    proof-
      have \<open>(\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
        using r1  \<open>\<And> t. t\<in>set canonical_basis \<Longrightarrow> (\<lambda> n. \<langle> t, X n \<rangle>) \<longlonglongrightarrow> L t\<close>
        by blast
      define f where \<open>f x = x *\<^sub>C t\<close> for x
      have \<open>isCont f r\<close>
        for r
        unfolding f_def
        by (simp add: cbounded_linear_scaleC_left bounded_linear_continuous)
      hence \<open>(\<lambda> n. f \<langle> t, X n \<rangle>) \<longlonglongrightarrow> f (L t)\<close>
        using \<open>(\<lambda>n. \<langle>t, X n\<rangle>) \<longlonglongrightarrow> L t\<close> isCont_tendsto_compose by blast
      hence \<open>(\<lambda> n. \<langle> t, X n \<rangle> *\<^sub>C t) \<longlonglongrightarrow> L t *\<^sub>C t\<close>
        unfolding f_def
        by simp
      thus ?thesis by blast
    qed
    hence \<open>(\<lambda> n. (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t))
    \<longlonglongrightarrow>  (\<Sum>t\<in>set canonical_basis. L t *\<^sub>C t)\<close>
      using \<open>finite (set canonical_basis)\<close>
        tendsto_finite_sum[where T = "set canonical_basis" and X = "\<lambda> t. \<lambda> n. \<langle>t, X n\<rangle> *\<^sub>C t"
          and L = "\<lambda> t. L t *\<^sub>C t"]
      by auto      
    hence x2: \<open>(\<lambda> n. (\<Sum>t\<in>set canonical_basis. \<langle> t, X n \<rangle> *\<^sub>C t)) \<longlonglongrightarrow> l\<close>
      using l_def by blast 
    have \<open>X \<longlonglongrightarrow> l\<close>
      using x1 x2 by simp
    thus ?thesis 
      unfolding convergent_def by blast
  qed
qed

lemma vector_to_cblinfun_adj_times_vector_to_cblinfun[simp]:
  includes cblinfun_notation
  shows "vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi> = cinner \<psi> \<phi> *\<^sub>C idOp"
proof -
  have "one_dim_isom \<gamma> *\<^sub>C one_dim_isom (of_complex \<langle>\<psi>, \<phi>\<rangle>) =
    \<langle>\<psi>, \<phi>\<rangle> *\<^sub>C one_dim_isom \<gamma>"
    for \<gamma> :: "'c::one_dim"
    by (metis (mono_tags, hide_lams) complex_vector.scale_left_commute id_apply of_complex_def 
        of_complex_eq_id of_complex_inner_1 one_dim_isom_def)
  hence "one_dim_isom ((vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>) *\<^sub>V \<gamma>)
      = one_dim_isom ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>V \<gamma>)" 
    for \<gamma> :: "'c::one_dim"
    by (simp add: times_applyOp)
  hence "((vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>) *\<^sub>V \<gamma>) = ((cinner \<psi> \<phi> *\<^sub>C idOp) *\<^sub>V \<gamma>)" 
    for \<gamma> :: "'c::one_dim"
    by (rule one_dim_isom_inj)
  thus ?thesis
    using  cblinfun_ext[where A = "vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>"
        and B = "\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C idOp"]
    by auto
qed


lemma scaleC_cindependent:
  assumes a1: "cindependent (B::'a::complex_vector set)" and a3: "c \<noteq> 0"
  shows "cindependent ((*\<^sub>C) c ` B)"
proof-
  have "u y = 0"
    if g1: "y\<in>S" and g2: "(\<Sum>x\<in>S. u x *\<^sub>C x) = 0" and g3: "finite S" and g4: "S\<subseteq>(*\<^sub>C) c ` B"
    for u y S
  proof-
    define v where "v x = u (c *\<^sub>C x)" for x
    obtain S' where "S'\<subseteq>B" and S_S': "S = (*\<^sub>C) c ` S'"
      by (meson g4 subset_imageE)      
    have "inj ((*\<^sub>C) c::'a\<Rightarrow>_)"
      unfolding inj_def
      using a3 by auto 
    hence "finite S'"
      using S_S' finite_imageD g3 subset_inj_on by blast            
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
    have t: "inj (((*\<^sub>C) c)::'a \<Rightarrow> _)"
      using a3 complex_vector.injective_scale[where c = c]
      by blast
    have "0 = (\<Sum>x\<in>(*\<^sub>C) c ` S'. u x *\<^sub>C x)"
      using \<open>S = (*\<^sub>C) c ` S'\<close> that(2) by auto
    also have "\<dots> = (\<Sum>x\<in>S'. v x *\<^sub>C (c *\<^sub>C x))"
      unfolding v_def
      using t Groups_Big.comm_monoid_add_class.sum.reindex[where h = "((*\<^sub>C) c)" and A = S' 
          and g = "\<lambda>x. u x *\<^sub>C x"] subset_inj_on by auto     
    also have "\<dots> = c *\<^sub>C (\<Sum>x\<in>S'. v x *\<^sub>C x)"
      by (metis (mono_tags, lifting) complex_vector.scale_left_commute scaleC_right.sum sum.cong)
    finally have "0 = c *\<^sub>C (\<Sum>x\<in>S'. v x *\<^sub>C x)".
    hence "(\<Sum>x\<in>S'. v x *\<^sub>C x) = 0"
      using a3 by auto
    hence "v (inverse c *\<^sub>C y) = 0"
      using \<open>inverse c *\<^sub>C y \<in> S'\<close> \<open>finite S'\<close> \<open>S' \<subseteq> B\<close> a1
        complex_vector.independentD
      by blast 
    thus "u y = 0"
      unfolding v_def
      by (simp add: a3) 
  qed
  thus ?thesis
    using complex_vector.dependent_explicit
    by (simp add: complex_vector.dependent_explicit ) 
qed

lemma inter_cindependent:
  assumes a1: "cindependent (B::'a::complex_vector set)" and a2: "c \<noteq> 0" and a3: "c \<noteq> 1"
  shows "B \<inter> (*\<^sub>C) c ` B = {}"
proof(rule classical)
  assume "\<not>(B \<inter> (*\<^sub>C) c ` B = {})"
  hence "B \<inter> (*\<^sub>C) c ` B \<noteq> {}"
    by blast
  then obtain x where u1: "x \<in> B \<inter> (*\<^sub>C) c ` B"
    by blast
  then obtain b where u2: "x = b" and u3: "b\<in>B"
    by blast
  then  obtain b' where u2': "x = c *\<^sub>C b'" and u3': "b'\<in>B"
    using u1
    by blast
  have g1: "b = c *\<^sub>C b'"
    using u2 and u2' by simp
  hence "b \<in> complex_vector.span {b'}"
    using complex_vector.span_base a2 by force 
  hence "b = b'"
    by (metis  u3' a1 complex_vector.dependent_def complex_vector.span_base 
        complex_vector.span_scale insertE insert_Diff u2 u2' u3) 
  hence "b' = c *\<^sub>C b'"
    using g1 by blast
  thus ?thesis
    by (metis a1 a3 complex_vector.dependent_zero complex_vector.scale_right_imp_eq
        mult_cancel_right2 scaleC_scaleC u3')
qed


lemma complex_span_eq_scaleC:
  "complex_vector.span (B \<union> (*\<^sub>C) c ` B) = complex_vector.span B"
proof-
  have "B \<subseteq> complex_vector.span B"
    using complex_vector.span_eq by auto    
  moreover have "(*\<^sub>C) c ` B \<subseteq> complex_vector.span B"
    using calculation complex_vector.span_scale by auto    
  ultimately have "B \<union> (*\<^sub>C) c ` B \<subseteq> complex_vector.span B"
    by blast
  hence c2: "complex_vector.span (B \<union> (*\<^sub>C) c ` B) \<subseteq> complex_vector.span B"
    by (smt complex_vector.span_minimal complex_vector.subspace_span)
  have "B \<subseteq> B \<union> (*\<^sub>C) c ` B"
    by simp
  hence c1: "complex_vector.span B \<subseteq> complex_vector.span (B \<union> (*\<^sub>C) c ` B)"
    by (simp add: complex_vector.span_mono)     
  show ?thesis 
    using c1 c2
    by blast
qed

lemma sum_3_sets:
  assumes "finite A" and "finite B" and "finite C"
    and "A \<inter> B = {}" and "A \<inter> C = {}" and "B \<inter> C = {}"
  shows "sum f (A \<union> B \<union> C) = sum f A + sum f B + sum f C"
  by (simp add: Int_Un_distrib2 assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) sum.union_disjoint)

lemma complex_real_independent:
  assumes a1: "cindependent (B::'a::complex_vector set)"
  defines "B' == ((*\<^sub>C) \<i> ` B)"
  shows "independent (B \<union> B')"
proof-
  have inj_scaleC: "inj (((*\<^sub>C) \<i>) ::'a \<Rightarrow> 'a)"
    unfolding inj_def
    by simp
  have inj_scaleC': "inj (((*\<^sub>C) (-\<i>)) ::'a \<Rightarrow> 'a)"
    unfolding inj_def
    by simp
  have "f y = 0"
    if b1:  "finite {x. f x \<noteq> 0}" and
      b2:  "{x. f x \<noteq> 0} \<subseteq> B \<union> B'" and 
      b3:  "(\<Sum>x| f x \<noteq> 0. f x *\<^sub>R x) = 0" 
    for f and y
  proof-
    have z0: "B \<inter> B' = {}"
      unfolding B'_def
      by (simp add: a1 inter_cindependent) 
    have "finite {x\<in>B. f x \<noteq> 0}"
      using b1 by auto
    have "finite {x\<in>B'. f x \<noteq> 0}"
      using b1 by auto
    moreover have "(*\<^sub>C) \<i> ` {x\<in>B. f (\<i> *\<^sub>C x) \<noteq> 0} \<subseteq> {x\<in>B'. f x \<noteq> 0}"
      unfolding B'_def by auto
    ultimately have "finite ((*\<^sub>C) \<i> ` {x\<in>B. f (\<i> *\<^sub>C x) \<noteq> 0})"
      using finite_subset by blast
    hence "finite {x\<in>B. f (\<i> *\<^sub>C x) \<noteq> 0}"
      using inj_scaleC
      by (metis (mono_tags, lifting) \<open>(*\<^sub>C) \<i> ` {x \<in> B. f (\<i> *\<^sub>C x) \<noteq> 0} \<subseteq> {x \<in> B'. f x \<noteq> 0}\<close> 
          \<open>finite {x \<in> B'. f x \<noteq> 0}\<close> inj_def inj_on_def inj_on_finite) 
    define g where "g x = (if x \<in> B then f x + \<i> *\<^sub>C f (\<i> *\<^sub>C x) else 0)" for x
    have g0_inter: "{x\<in>B. f x \<noteq> 0} \<inter> {x\<in>B. f (\<i> *\<^sub>C x) \<noteq> 0} = {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0}"
      by blast
    have g0_union: "{x. g x \<noteq> 0} = {x\<in>B. f x \<noteq> 0} \<union> {x\<in>B. f (\<i> *\<^sub>C x) \<noteq> 0}" 
      unfolding g_def by auto
    hence g1: "finite {x. g x \<noteq> 0}"
      by (simp add: \<open>finite {x \<in> B. f (\<i> *\<^sub>C x) \<noteq> 0}\<close> \<open>finite {x \<in> B. f x \<noteq> 0}\<close>)        
    have g2: "{x. g x \<noteq> 0} \<subseteq> B"
      unfolding g_def by auto
    have "f x + \<i> * f (\<i> *\<^sub>C x) \<noteq> 0 \<longleftrightarrow> (f x \<noteq> 0 \<or> f (\<i> *\<^sub>C x) \<noteq> 0)"
      for x
      by auto
    hence x1: "{x\<in>B. f x + \<i> * f (\<i> *\<^sub>C x) \<noteq> 0} = {x\<in>B. f x \<noteq> 0 \<or> f (\<i> *\<^sub>C x) \<noteq> 0}"
      by auto
    have "{x\<in>B. f x \<noteq> 0} \<union> {x\<in>B'. f x \<noteq> 0} 
                = {x. (x\<in>B \<and> f x \<noteq> 0) \<or> (x\<in>B' \<and> f x \<noteq> 0)}"
      by blast
    also have "\<dots> = {x. (x\<in>B \<or> x\<in>B') \<and> f x \<noteq> 0}"
      by blast
    also have "\<dots> = {x\<in>B\<union>B'. f x \<noteq> 0}"
      by blast
    finally have p2: " {x \<in> B. f x \<noteq> 0} \<union> {x \<in> B'. f x \<noteq> 0} =
    {x \<in> B \<union> B'. f x \<noteq> 0}" by blast
    have "finite {x\<in>B. f x \<noteq> 0}"
      by (simp add: \<open>finite {x \<in> B. f x \<noteq> 0}\<close>)            
    moreover have "finite {x\<in>B'. f x \<noteq> 0}"
      unfolding B'_def
      by (simp add: b1)
    moreover have "{x\<in>B. f x \<noteq> 0} \<inter> {x\<in>B'. f x \<noteq> 0} = {}"
      using z0 by auto
    moreover have "{x\<in>B. f x \<noteq> 0} \<union> {x\<in>B'. f x \<noteq> 0} = {x\<in>B\<union>B'. f x \<noteq> 0}"
      using p2
      by simp 
    ultimately have r1: "(\<Sum>x | x \<in> B \<union> B' \<and> f x \<noteq> 0. f x *\<^sub>R x) =
    (\<Sum>x | x \<in> B \<and> f x \<noteq> 0. f x *\<^sub>R x) +
    (\<Sum>x | x \<in> B' \<and> f x \<noteq> 0. f x *\<^sub>R x)"
      by (metis (mono_tags, lifting) sum.union_disjoint)
    have "(\<Sum>x\<in>(*\<^sub>C) \<i> ` {x|x. x\<in>B \<and> f (\<i> *\<^sub>C x) \<noteq> 0}. f x *\<^sub>R x)
        = (\<Sum>x|x\<in>B \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f (\<i> *\<^sub>C x) *\<^sub>R (\<i> *\<^sub>C x))"
      using inj_scaleC Groups_Big.comm_monoid_add_class.sum.reindex
        [where A = "{x|x. x\<in>B \<and> f (\<i> *\<^sub>C x) \<noteq> 0}" and h = "(*\<^sub>C) \<i>" and g = "\<lambda>x. f x *\<^sub>R x"]
      unfolding comp_def inj_def inj_on_def by auto            
    moreover have "{x|x. x\<in>B' \<and> f x \<noteq> 0} = (*\<^sub>C) \<i> ` {x|x. x\<in>B \<and> f (\<i> *\<^sub>C x) \<noteq> 0}"
      unfolding B'_def by auto
    ultimately have r2: "(\<Sum>x | x \<in> B \<and> f x \<noteq> 0. f x *\<^sub>R x) +
    (\<Sum>x | x \<in> B' \<and> f x \<noteq> 0. f x *\<^sub>R x) =
    (\<Sum>x | x \<in> B \<and> f x \<noteq> 0. f x *\<^sub>R x) +
    (\<Sum>x | x \<in> B \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f (\<i> *\<^sub>C x) *\<^sub>R \<i> *\<^sub>C x)" by simp
    have "(\<Sum>x|x\<in>B \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f (\<i> *\<^sub>C x) *\<^sub>R (\<i> *\<^sub>C x))
              =  (\<Sum>x|x\<in>B \<and> f (\<i> *\<^sub>C x) \<noteq> 0. (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      by (metis (no_types, lifting) complex_vector.scale_left_commute scaleC_scaleC 
          scaleR_scaleC)
    moreover have "(\<Sum>x|x\<in>B \<and> f x \<noteq> 0. f x *\<^sub>R x) = (\<Sum>x|x\<in>B \<and> f x \<noteq> 0. f x *\<^sub>C x)"
      by (simp add: scaleR_scaleC)            
    ultimately have r3: "(\<Sum>x | x \<in> B \<and> f x \<noteq> 0. f x *\<^sub>R x) +
    (\<Sum>x | x \<in> B \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f (\<i> *\<^sub>C x) *\<^sub>R \<i> *\<^sub>C x) =
    (\<Sum>x | x \<in> B \<and> f x \<noteq> 0. complex_of_real (f x) *\<^sub>C x) +
    (\<Sum>x | x \<in> B \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x)"
      by simp
    have "{x\<in>B. (f x = 0 \<or> f x \<noteq> 0) \<and> f (\<i> *\<^sub>C x) \<noteq> 0}
                = {x\<in>B. f x = 0  \<and> f (\<i> *\<^sub>C x) \<noteq> 0} \<union> {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0}"
      by blast
    moreover have "{x\<in>B. f x = 0  \<and> f (\<i> *\<^sub>C x) \<noteq> 0} \<inter> {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0} = {}"
      by blast
    ultimately have p1: "(\<Sum>x | x \<in> B \<and> (f x = 0 \<or> f x \<noteq> 0) \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x) =
    (\<Sum>x | x \<in> B \<and> f x = 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x) +
    (\<Sum>x | x \<in> B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x)"
      by (metis (no_types, lifting) \<open>finite {x \<in> B. f (\<i> *\<^sub>C x) \<noteq> 0}\<close>
          finite_Un sum.union_disjoint)
    have "{x\<in>B. f x \<noteq> 0 \<and> (f (\<i> *\<^sub>C x) = 0 \<or> f (\<i> *\<^sub>C x) \<noteq> 0)}
              = {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0} \<union> {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0}"
      by blast
    moreover have "{x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0} \<inter> {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0} = {}"
      by blast
    moreover have "finite {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0}"
      by (simp add: b1)                        
    moreover have "finite {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0}"
      using \<open>finite {x \<in> B. f x \<noteq> 0}\<close> calculation(1) by auto              
    ultimately have "(\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> (f (\<i> *\<^sub>C x) = 0 \<or> f (\<i> *\<^sub>C x) \<noteq> 0). f x *\<^sub>C x)
              = (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0. f x *\<^sub>C x)
              + (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f x *\<^sub>C x)"
      by (simp add: sum.union_disjoint)
    moreover have "(\<Sum>x|x\<in>B \<and> (f x = 0 \<or> f x \<noteq> 0) \<and> f (\<i> *\<^sub>C x) \<noteq> 0. (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)
              = (\<Sum>x|x\<in>B \<and> f x = 0  \<and> f (\<i> *\<^sub>C x) \<noteq> 0. (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)
              + (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0. (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      using p1 by simp        
    ultimately have r4:"(\<Sum>x | x \<in> B \<and>
           f x \<noteq> 0 \<and> (f (\<i> *\<^sub>C x) = 0 \<or> f (\<i> *\<^sub>C x) \<noteq> 0).
       complex_of_real (f x) *\<^sub>C x) +
    (\<Sum>x | x \<in> B \<and> (f x = 0 \<or> f x \<noteq> 0) \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x) =
    (\<Sum>x | x \<in> B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0.
       complex_of_real (f x) *\<^sub>C x) +
    (\<Sum>x | x \<in> B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       complex_of_real (f x) *\<^sub>C x) +
    (\<Sum>x | x \<in> B \<and> f x = 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x) +
    (\<Sum>x | x \<in> B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x)" 
      by simp
    have r5: "(\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f x *\<^sub>C x)
              + (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0. (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)
            = (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f x *\<^sub>C x + (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      by (metis (mono_tags, lifting) sum.cong sum.distrib)
    have "{x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0} \<inter> {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0} = {}"
      by blast
    moreover have "{x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0} \<inter> {x\<in>B. f x = 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0} = {}"
      by blast
    moreover have "{x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0} \<inter> {x\<in>B. f x = 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0} = {}"
      by blast
    moreover have "finite {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0}"
      by (metis (no_types, lifting) Collect_mono \<open>finite {x \<in> B. f x \<noteq> 0}\<close> rev_finite_subset)
    moreover have "finite {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0}"
      by (metis (no_types, lifting) Collect_mono \<open>finite {x \<in> B. f (\<i> *\<^sub>C x) \<noteq> 0}\<close> rev_finite_subset)
    moreover have "finite {x\<in>B. f x = 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0}"
      by (metis (no_types, lifting) Collect_mono \<open>finite {x \<in> B. f (\<i> *\<^sub>C x) \<noteq> 0}\<close> rev_finite_subset)            
    ultimately have " (\<Sum>x\<in>{x \<in> B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0} 
                               \<union> {x \<in> B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0} \<union>
                                 {x \<in> B. f x = 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0}.
       complex_of_real (f x) *\<^sub>C x + (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x) =
    (\<Sum>x | x \<in> B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0.
       complex_of_real (f x) *\<^sub>C x + (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x) +
    (\<Sum>x | x \<in> B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       complex_of_real (f x) *\<^sub>C x + (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x) +
    (\<Sum>x | x \<in> B \<and> f x = 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       complex_of_real (f x) *\<^sub>C x + (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x)"
      using sum_3_sets[where A = "{x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0}"
          and B = "{x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0}" and C = "{x\<in>B. f x = 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0}"
          and f = "\<lambda>x. f x *\<^sub>C x+(\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x"] by auto
    moreover have "{x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0} \<union>
                {x\<in>B. f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0} \<union>
                {x\<in>B. f x = 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0} = 
                {x\<in>B. (f x \<noteq> 0 \<or> f (\<i> *\<^sub>C x) \<noteq> 0)}"
      by auto
    ultimately have r6: "(\<Sum>x | x \<in> B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0.
       complex_of_real (f x) *\<^sub>C x +
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x) +
    (\<Sum>x | x \<in> B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       complex_of_real (f x) *\<^sub>C x +
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x) +
    (\<Sum>x | x \<in> B \<and> f x = 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0.
       complex_of_real (f x) *\<^sub>C x +
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x) =
    (\<Sum>x | x \<in> B \<and> (f x \<noteq> 0 \<or> f (\<i> *\<^sub>C x) \<noteq> 0).
       complex_of_real (f x) *\<^sub>C x +
       (\<i> * complex_of_real (f (\<i> *\<^sub>C x))) *\<^sub>C x)" by auto

    have "(\<Sum>x| f x \<noteq> 0. f x *\<^sub>R x) = (\<Sum>x|x\<in>B\<union>B' \<and> f x \<noteq> 0. f x *\<^sub>R x)"
      by (metis (mono_tags, lifting) UnI1 b2 mem_Collect_eq sup.absorb_iff2)
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> f x \<noteq> 0. f x *\<^sub>R x) + (\<Sum>x|x\<in>B' \<and> f x \<noteq> 0. f x *\<^sub>R x)"
      using r1 by auto
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> f x \<noteq> 0. f x *\<^sub>R x)
                      + (\<Sum>x|x\<in>B \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f (\<i> *\<^sub>C x) *\<^sub>R (\<i> *\<^sub>C x))"
      using r1 r2 by simp
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> f x \<noteq> 0. f x *\<^sub>C x)
                      + (\<Sum>x|x\<in>B \<and> f (\<i> *\<^sub>C x) \<noteq> 0. (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      using r3 by simp
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> (f (\<i> *\<^sub>C x) = 0 \<or> f (\<i> *\<^sub>C x) \<noteq> 0). f x *\<^sub>C x)
                      + (\<Sum>x|x\<in>B \<and> (f x = 0 \<or> f x \<noteq> 0) \<and> f (\<i> *\<^sub>C x) \<noteq> 0. (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      by auto
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0. f x *\<^sub>C x)
                      + (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f x *\<^sub>C x)
                      + (\<Sum>x|x\<in>B \<and> f x = 0  \<and> f (\<i> *\<^sub>C x) \<noteq> 0. (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)
                      + (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0. (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      using r4 by simp
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0. f x *\<^sub>C x+(\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)
                      + (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f x *\<^sub>C x)
                      + (\<Sum>x|x\<in>B \<and> f x = 0  \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f x *\<^sub>C x+(\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)
                      + (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0. (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      by auto
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) = 0. f x *\<^sub>C x+(\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)
                      + (\<Sum>x|x\<in>B \<and> f x \<noteq> 0 \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f x *\<^sub>C x + (\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)
                      + (\<Sum>x|x\<in>B \<and> f x = 0  \<and> f (\<i> *\<^sub>C x) \<noteq> 0. f x *\<^sub>C x+(\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      using r5
      by simp
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> (f x \<noteq> 0 \<or> f (\<i> *\<^sub>C x) \<noteq> 0). f x *\<^sub>C x+(\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      using r6 by simp
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> f x + \<i> * f (\<i> *\<^sub>C x) \<noteq> 0. f x *\<^sub>C x+(\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      by simp
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> g x \<noteq> 0. f x *\<^sub>C x+(\<i> * f (\<i> *\<^sub>C x)) *\<^sub>C x)"
      by (metis complex_scaleC_def g_def)          
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> g x \<noteq> 0. (f x +(\<i> * f (\<i> *\<^sub>C x))) *\<^sub>C x)"
      by (metis (no_types, lifting) scaleC_add_left)          
    also have "\<dots> = (\<Sum>x|x\<in>B \<and> g x \<noteq> 0. g x *\<^sub>C x)"
      using g_def by auto
    also have "\<dots> = (\<Sum>x|g x \<noteq> 0. g x *\<^sub>C x)"
      by (metis (mono_tags, lifting) \<open>{x. g x \<noteq> 0} \<subseteq> B\<close> mem_Collect_eq subsetD)
    finally have "(\<Sum>x | f x \<noteq> 0. f x *\<^sub>R x) = (\<Sum>x|g x \<noteq> 0. g x *\<^sub>C x)".
    hence g3: "(\<Sum>x| g x \<noteq> 0. g x *\<^sub>C x) = 0"
      using b3 by auto
    show ?thesis
    proof(cases "y \<in> B")
      case True     
      have "g y = 0"
        using g1 g2 g3 True a1 complex_vector.independent_alt[where B = B]
        by (smt Collect_cong  sum.cong)
      thus ?thesis unfolding g_def
        using True by auto 
    next
      case False
      hence y_notB: "y \<notin> B".
      show ?thesis 
      proof(rule classical)
        assume "f y \<noteq> 0"
        hence "y \<in> B \<union> B'"
          using b2 by auto
        hence "y \<in> B'"
          using y_notB by auto
        hence "y \<in> (*\<^sub>C) \<i> ` B"
          unfolding B'_def by blast
        hence v1: "(*\<^sub>C) (-\<i>) y \<in> (*\<^sub>C) (-\<i>) ` (*\<^sub>C) \<i> ` B"
          by simp

        have "(*\<^sub>C) (-\<i>) ` (*\<^sub>C) \<i> ` B = ((*\<^sub>C) (-\<i>) \<circ> (*\<^sub>C) \<i>) ` B"
          by (simp add: image_comp)
        also have "\<dots> = ((*\<^sub>C) ((-\<i>)*\<i>)) ` B"
          by auto
        also have "\<dots> = (*\<^sub>C) 1 ` B"
          by simp
        also have "\<dots> = B" by simp
        finally have v2: "(*\<^sub>C) (-\<i>) ` (*\<^sub>C) \<i> ` B = B"
          by blast
        have yB: "(-\<i>) *\<^sub>C y \<in> B"
          using v1 v2 by blast 
        define h::"'a \<Rightarrow> complex" where "h x = (-\<i>) * g ((-\<i>) *\<^sub>C x)" for x
        have z1: "cindependent B'"
          using a1 unfolding B'_def
          by (simp add: scaleC_cindependent)
        have f1: "\<And>y. g y \<noteq> 0 \<Longrightarrow> \<exists>x. g (- (\<i> *\<^sub>C x)) \<noteq> 0 \<and> y = - (\<i> *\<^sub>C x)"
        proof-
          fix y
          assume hyp1: "g y \<noteq> 0"
          define x where "x = \<i> *\<^sub>C y"
          have "y = - (\<i> *\<^sub>C x)"
            unfolding x_def by simp
          moreover have "g (- (\<i> *\<^sub>C x)) \<noteq> 0"
            unfolding x_def
            using hyp1 by auto 
          ultimately show " \<exists>x. g (- (\<i> *\<^sub>C x)) \<noteq> 0 \<and> y = - (\<i> *\<^sub>C x)" by blast
        qed
        have "{x. h x \<noteq> 0} = {x. g (- \<i> *\<^sub>C x) \<noteq> 0}"
          unfolding h_def by auto
        moreover have "bij_betw ((*\<^sub>C) (- \<i>)) {x. g (- \<i> *\<^sub>C x) \<noteq> 0} {x. g x \<noteq> 0}"
        proof (rule bij_betwI')
          show "(- \<i> *\<^sub>C x = - \<i> *\<^sub>C y) = (x = y)"
            if "x \<in> {x. g (- \<i> *\<^sub>C x) \<noteq> 0}"
              and "y \<in> {x. g (- \<i> *\<^sub>C x) \<noteq> 0}"
            for x :: 'a
              and y :: 'a
            using that
            by auto 
          show "- \<i> *\<^sub>C x \<in> {x. g x \<noteq> 0}"
            if "x \<in> {x. g (- \<i> *\<^sub>C x) \<noteq> 0}"
            for x :: 'a
            using that
            by simp 
          show "\<exists>x\<in>{x. g (- \<i> *\<^sub>C x) \<noteq> 0}. y = - \<i> *\<^sub>C x"
            if "y \<in> {x. g x \<noteq> 0}"
            for y :: 'a
            using that
            by (simp add: f1) 
        qed           
        ultimately have z2: "finite {x. h x \<noteq> 0}"
          by (simp add: bij_betw_finite g1) 

        have z3: "{x. h x \<noteq> 0} \<subseteq> B'"
        proof auto
          fix x
          assume "h x \<noteq> 0"
          hence "g ((- \<i>) *\<^sub>C x) \<noteq> 0"
            by (simp add: h_def)
          hence "(- \<i>) *\<^sub>C x \<in> B"
            using g2 by blast
          thus "x \<in> B'"
            unfolding B'_def
            using image_iff by fastforce 
        qed

        have g1: "g ((-\<i>) *\<^sub>C (\<i> *\<^sub>C x)) = 0 \<longleftrightarrow> h (\<i> *\<^sub>C x) = 0"
          for x
          unfolding h_def by auto

        have h1: "bij_betw ((*\<^sub>C) \<i>) {x. h (\<i> *\<^sub>C x) \<noteq> 0} {x. h x \<noteq> 0}"
        proof (rule bij_betwI')
          show "(\<i> *\<^sub>C x = \<i> *\<^sub>C y) = (x = y)"
            if "x \<in> {x. h (\<i> *\<^sub>C x) \<noteq> 0}"
              and "y \<in> {x. h (\<i> *\<^sub>C x) \<noteq> 0}"
            for x :: 'a
              and y :: 'a
            using that
            by auto 
          show "\<i> *\<^sub>C x \<in> {x. h x \<noteq> 0}"
            if "x \<in> {x. h (\<i> *\<^sub>C x) \<noteq> 0}"
            for x :: 'a
            using that
            by simp 
          show "\<exists>x\<in>{x. h (\<i> *\<^sub>C x) \<noteq> 0}. y = \<i> *\<^sub>C x"
            if "y \<in> {x. h x \<noteq> 0}"
            for y :: 'a
            using that
          proof transfer
            fix yb :: 'a and ha :: "'a \<Rightarrow> complex"
            assume "yb \<in> {x. ha x \<noteq> 0}"
            hence "ha yb \<noteq> 0"
              by blast
            hence "\<exists>a. \<i> *\<^sub>C a = yb \<and> ha (\<i> *\<^sub>C a) \<noteq> 0"
              by (metis (full_types) ceq_vector_fraction_iff complex_i_not_zero)
            thus "\<exists>a\<in>{a. ha (\<i> *\<^sub>C a) \<noteq> 0}. yb = \<i> *\<^sub>C a"
              by blast
          qed
        qed

        have "(\<Sum>x| g x \<noteq> 0. g x *\<^sub>C x) 
              = (\<Sum>x| g ((-\<i>) *\<^sub>C (\<i> *\<^sub>C x)) \<noteq> 0. g ((-\<i>) *\<^sub>C (\<i> *\<^sub>C x)) *\<^sub>C ((-\<i>) *\<^sub>C (\<i> *\<^sub>C x)))"
          by simp
        also have "\<dots> = (\<Sum>x| g ((-\<i>) *\<^sub>C (\<i> *\<^sub>C x)) \<noteq> 0. ((-\<i>) * g ((-\<i>) *\<^sub>C (\<i> *\<^sub>C x))) *\<^sub>C (\<i> *\<^sub>C x))"
          by (metis (no_types, lifting) complex_vector.scale_left_commute scaleC_scaleC)
        also have "\<dots> = (\<Sum>x| g ((-\<i>) *\<^sub>C (\<i> *\<^sub>C x)) \<noteq> 0.  h (\<i> *\<^sub>C x) *\<^sub>C (\<i> *\<^sub>C x))"
          unfolding h_def by auto
        also have "\<dots> = (\<Sum>x| h (\<i> *\<^sub>C x) \<noteq> 0.  h (\<i> *\<^sub>C x) *\<^sub>C (\<i> *\<^sub>C x))"
          using g1 by simp
        also have "\<dots> = (\<Sum>t| h t \<noteq> 0.  h t *\<^sub>C t)"
          using h1 Groups_Big.comm_monoid_add_class.sum.reindex_bij_betw[where g = h and h = "(*\<^sub>C) \<i>" 
              and S = "{x. h (\<i> *\<^sub>C x) \<noteq> 0}" and T = "{x. h x \<noteq> 0}"]
          by (metis (mono_tags, lifting) sum.cong sum.reindex_bij_betw)
        finally have "(\<Sum>x | g x \<noteq> 0. g x *\<^sub>C x) = (\<Sum>t | h t \<noteq> 0. h t *\<^sub>C t)".
        hence z4: "(\<Sum>x| h x \<noteq> 0. h x *\<^sub>C x) = 0"
          using g3 by auto

        have "h y = 0"
          using z1 z2 z3 z4 complex_vector.independentD
          by blast 
        thus ?thesis
          unfolding h_def g_def using yB by simp
      qed
    qed 
  qed
  thus ?thesis
    using Real_Vector_Spaces.real_vector.independent_alt[where B = "B \<union> B'"]
    by meson
qed        


lemma finite_complex_span_representation_bounded:
  fixes B :: "'a::complex_normed_vector set"
  assumes a1: "finite B" and a2: "cindependent B"
  shows "\<exists>D>0. \<forall>\<psi> b. norm (complex_vector.representation B \<psi> b) \<le> norm \<psi> * D"
proof -
  have complex_real_vector_representation: 
    "complex_vector.representation B \<psi> b
       = (real_vector.representation (B \<union> (*\<^sub>C) \<i> ` B) \<psi> b)
   + \<i> *\<^sub>C (real_vector.representation (B \<union> (*\<^sub>C) \<i> ` B) \<psi> (\<i> *\<^sub>C b))"
    if a1: "cindependent B" and a2: "b \<in> B" and a3: "finite B"
    for b \<psi>
  proof (cases "\<psi> \<in> complex_vector.span B")
    define B' where "B' = B \<union> (*\<^sub>C) \<i> ` B"
    case True
    define r  where "r v = real_vector.representation B' \<psi> v" for v
    define r' where "r' v = real_vector.representation B' \<psi> (\<i> *\<^sub>C v)" for v
    define f  where "f v = r v + \<i> *\<^sub>C r' v" for v
    define g  where "g v = complex_vector.representation B \<psi> v" for v
    have "(\<Sum>v | g v \<noteq> 0. g v *\<^sub>C v) = \<psi>"
      unfolding g_def
      using Collect_cong Collect_mono_iff DiffD1 DiffD2 True a1 
        complex_vector.finite_representation
        complex_vector.sum_nonzero_representation_eq sum.mono_neutral_cong_left
      by fastforce
    moreover have "finite {v. g v \<noteq> 0}"
      unfolding g_def
      by (simp add: complex_vector.finite_representation)
    moreover have "v \<in> B"
      if "g v \<noteq> 0" for v
      using that unfolding g_def
      by (simp add: complex_vector.representation_ne_zero)        
    ultimately have rep1: "(\<Sum>v\<in>B. g v *\<^sub>C v) = \<psi>"    
      unfolding g_def
      using a3
      by (smt DiffD2 complex_vector.scale_eq_0_iff mem_Collect_eq subset_eq 
          sum.mono_neutral_cong_left) (* > 1s *)
    have l0': "inj ((*\<^sub>C) \<i>::'a \<Rightarrow>'a)"
      unfolding inj_def 
      by simp 
    have l0: "inj ((*\<^sub>C) (- \<i>)::'a \<Rightarrow>'a)"
      unfolding inj_def 
      by simp 
    have l1: "(*\<^sub>C) (- \<i>) ` B \<inter> B = {}"
      using inter_cindependent[where B=B and c = "- \<i>"]
      by (metis Int_commute a1 add.inverse_inverse complex_i_not_one i_squared mult_cancel_left1 
          neg_equal_0_iff_equal)
    have l2: "B \<inter> (*\<^sub>C) \<i> ` B = {}"
      by (simp add: a1 inter_cindependent)
    have rr1: "r (\<i> *\<^sub>C v) = r' v" for v
      unfolding r_def r'_def
      by simp 
    have k1: "independent B'"
      unfolding B'_def using a1 complex_real_independent
      by (simp add: complex_real_independent)    
    have "\<psi> \<in> Real_Vector_Spaces.span B'"
      using B'_def True complex_real_span by blast    
    have "v \<in> B'"
      if "r v \<noteq> 0"
      for v
      unfolding r_def
      using r_def real_vector.representation_ne_zero that by auto
    have "finite B'"
      unfolding B'_def using a3
      by simp 
    have "(\<Sum>v\<in>B'. r v *\<^sub>R v) = \<psi>"
      unfolding r_def 
      using True  Real_Vector_Spaces.real_vector.sum_representation_eq[where B = B' and basis = B' 
          and v = \<psi>]  
      by (smt Real_Vector_Spaces.dependent_raw_def \<open>\<psi> \<in> Real_Vector_Spaces.span B'\<close> \<open>finite B'\<close> 
          equalityD2 k1)
    have d1: "(\<Sum>v\<in>B. r (\<i> *\<^sub>C v) *\<^sub>R (\<i> *\<^sub>C v)) = (\<Sum>v\<in>(*\<^sub>C) \<i> ` B. r v *\<^sub>R v)"
      using l0'
      by (metis (mono_tags, lifting) inj_eq inj_on_def sum.reindex_cong)
    have "(\<Sum>v\<in>B. (r v + \<i> * (r' v)) *\<^sub>C v) = (\<Sum>v\<in>B. r v *\<^sub>C v + (\<i> * r' v) *\<^sub>C v)"
      by (meson scaleC_left.add)
    also have "\<dots> = (\<Sum>v\<in>B. r v *\<^sub>C v) + (\<Sum>v\<in>B. (\<i> * r' v) *\<^sub>C v)"
      using sum.distrib by fastforce
    also have "\<dots> = (\<Sum>v\<in>B. r v *\<^sub>C v) + (\<Sum>v\<in>B. \<i> *\<^sub>C (r' v *\<^sub>C v))"
      by auto
    also have "\<dots> = (\<Sum>v\<in>B. r v *\<^sub>R v) + (\<Sum>v\<in>B. \<i> *\<^sub>C (r (\<i> *\<^sub>C v) *\<^sub>R v))"
      unfolding r'_def r_def
      by (metis (mono_tags, lifting) scaleR_scaleC sum.cong) 
    also have "\<dots> = (\<Sum>v\<in>B. r v *\<^sub>R v) + (\<Sum>v\<in>B. r (\<i> *\<^sub>C v) *\<^sub>R (\<i> *\<^sub>C v))"
      by (metis (no_types, lifting) complex_vector.scale_left_commute scaleR_scaleC)      
    also have "\<dots> = (\<Sum>v\<in>B. r v *\<^sub>R v) + (\<Sum>v\<in>(*\<^sub>C) \<i> ` B. r v *\<^sub>R v)"
      using d1
      by simp
    also have "\<dots> = \<psi>"
      using l2 \<open>(\<Sum>v\<in>B'. r v *\<^sub>R v) = \<psi>\<close>
      unfolding B'_def
      by (simp add: a3 sum.union_disjoint) 
    finally have "(\<Sum>v\<in>B. f v *\<^sub>C v) = \<psi>" unfolding r'_def r_def f_def by simp
    hence "0 = (\<Sum>v\<in>B. f v *\<^sub>C v) - (\<Sum>v\<in>B. complex_vector.representation B \<psi> v *\<^sub>C v)"
      using rep1
      unfolding g_def
      by simp
    also have "\<dots> = (\<Sum>v\<in>B. f v *\<^sub>C v - complex_vector.representation B \<psi> v *\<^sub>C v)"
      by (simp add: sum_subtractf)
    also have "\<dots> = (\<Sum>v\<in>B. (f v - complex_vector.representation B \<psi> v) *\<^sub>C v)"
      by (metis scaleC_left.diff)
    finally have "0 = (\<Sum>v\<in>B. (f v - complex_vector.representation B \<psi> v) *\<^sub>C v)".
    hence "(\<Sum>v\<in>B. (f v - complex_vector.representation B \<psi> v) *\<^sub>C v) = 0"
      by simp
    hence "f b - complex_vector.representation B \<psi> b = 0"
      using a1 a2 a3 complex_vector.independentD[where s = B and t = B 
          and u = "\<lambda>v. f v - complex_vector.representation B \<psi> v" and v = b]
        order_refl  by smt
    hence "complex_vector.representation B \<psi> b = f b"
      by simp
    thus ?thesis unfolding f_def r_def r'_def B'_def by auto
  next
    define B' where "B' = B \<union> (*\<^sub>C) \<i> ` B"
    case False
    have b2: "\<psi> \<notin> real_vector.span B'"
      unfolding B'_def
      using False complex_real_span by auto    
    have "\<psi> \<notin> complex_vector.span B"
      using False by blast
    have "complex_vector.representation B \<psi> b = 0"
      unfolding complex_vector.representation_def
      by (simp add: False)
    moreover have "real_vector.representation B' \<psi> b = 0"
      unfolding real_vector.representation_def
      by (simp add: b2)
    moreover have "real_vector.representation B' \<psi> ((*\<^sub>C) \<i> b) = 0"
      unfolding real_vector.representation_def
      by (simp add: b2)
    ultimately show ?thesis unfolding B'_def by simp
  qed
  define B' where "B' = (B \<union> scaleC \<i> ` B)"
  have independent_B': "independent B'"
    using complex_real_independent B'_def \<open>cindependent B\<close>
    by (simp add: complex_real_independent a1) 
  have "finite B'"
    unfolding B'_def using \<open>finite B\<close> by simp
  obtain D' where "D' > 0" and D': "norm (real_vector.representation B' \<psi> b) \<le> norm \<psi> * D'" 
    for \<psi> b
    apply atomize_elim
    using independent_B' \<open>finite B'\<close>
    by (simp add: finite_span_representation_bounded)

  define D where "D = 2*D'" 
  from \<open>D' > 0\<close> have \<open>D > 0\<close>
    unfolding D_def by simp
  have "norm (complex_vector.representation B \<psi> b) \<le> norm \<psi> * D" for \<psi> b
  proof (cases "b\<in>B")
    case True
    have d3: "norm \<i> = 1"
      by simp          

    have "norm (\<i> *\<^sub>C complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))
          = norm \<i> * norm (complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      using norm_scaleC by blast
    also have "\<dots> = norm (complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      using d3 by simp
    finally have d2:"norm (\<i> *\<^sub>C complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))
          = norm (complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))".
    have "norm (complex_vector.representation B \<psi> b)
        = norm (complex_of_real (real_vector.representation B' \<psi> b)
            + \<i> *\<^sub>C complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      by (simp add: B'_def True a1 a2 complex_real_vector_representation)      
    also have "\<dots> \<le> norm (complex_of_real (real_vector.representation B' \<psi> b))
             + norm (\<i> *\<^sub>C complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      using norm_triangle_ineq by blast
    also have "\<dots> = norm (complex_of_real (real_vector.representation B' \<psi> b))
                  + norm (complex_of_real (real_vector.representation B' \<psi> (\<i> *\<^sub>C b)))"
      using d2 by simp
    also have "\<dots> = norm (real_vector.representation B' \<psi> b)
                  + norm (real_vector.representation B' \<psi> (\<i> *\<^sub>C b))"
      by simp
    also have "\<dots> \<le> norm \<psi> * D' + norm \<psi> * D'"
      by (rule add_mono; rule D')
    also have "\<dots> \<le> norm \<psi> * D"
      unfolding D_def by linarith
    finally show ?thesis
      by auto
  next
    case False
    hence "crepresentation B \<psi> b = 0"
      using complex_vector.representation_ne_zero by blast      
    thus ?thesis
      by (smt \<open>0 < D\<close> norm_ge_zero norm_zero split_mult_pos_le)
  qed
  with \<open>D > 0\<close>
  show ?thesis
    by auto
qed

lemma finite_complex_span_complete: 
  fixes B :: "'a::complex_normed_vector set"
  assumes "finite B"
  shows "complete (complex_vector.span B)"
  by (simp add: assms finite_cspan_complete)


lemma cblinfun_operator_S_zero_uniq_span:
  fixes S::\<open>'a::chilbert_space set\<close>
  assumes a1: "x \<in> complex_vector.span S"
    and a2: "cindependent S"
    and a4: "\<And>s. s\<in>S \<Longrightarrow> F *\<^sub>V s = 0"
  shows \<open>F *\<^sub>V x = 0\<close>
proof-
  have "\<exists>t r. finite t \<and> t \<subseteq> S \<and>  x = (\<Sum>a\<in>t. r a *\<^sub>C a)"
    using complex_vector.span_explicit a1 by (smt mem_Collect_eq)
  then obtain t r where b1: "finite t" and b2: "t \<subseteq> S" and b3: "x = (\<Sum>a\<in>t. r a *\<^sub>C a)"
    by blast
  have  "F x = (\<Sum>a\<in>t. r a *\<^sub>C (F a))"
    by (simp add: b1 b3 clinear_finite_sum)    
  hence "F x = 0"
    using a4 b2
    by (simp add: subset_eq) 
  thus ?thesis by (simp add: cblinfun_ext) 
qed

lemma cblinfun_operator_S_uniq_span:
  fixes S::\<open>'a::chilbert_space set\<close>
  assumes a1: "x \<in> complex_vector.span S"
    and a2: "cindependent S"
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
    and a2: "cindependent basis"
    and a4: "\<And>s. s\<in>basis \<Longrightarrow> F *\<^sub>V s = 0"
  shows \<open>F = 0\<close>
  using cblinfun_operator_S_zero_uniq_span
  by (metis UNIV_I a1 a2 a4 applyOp0 cblinfun_ext)


lemma ortho_imples_independent:
  assumes a1: "is_ortho_set A"
  shows "cindependent A"
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
        by (meson DiffD1 \<open>v' \<in> t - {v}\<close> b2 b4 is_ortho_set_def subsetD)         
    qed
    hence sum0: "(\<Sum>v'\<in>t-{v}. u v' * \<langle>v, v'\<rangle>) = 0"
      by simp

    have v1: "v \<in> A"
      using b2 b4 by blast        
    hence "v \<noteq> 0"
      using a1 unfolding is_ortho_set_def
      by blast

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
      using v1
      by (simp add: \<open>v \<noteq> 0\<close>)  
    ultimately show "u v = 0" by simp
  qed
  thus ?thesis using complex_vector.independent_explicit_module
    by smt    
qed

(* TODO move Complex_Normed *)
lemma cblinfun_operator_finite_dim:
  fixes  F::"'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" 
    and basis::"'a set"
  assumes b1: "complex_vector.span basis = UNIV"
    and b2: "cindependent basis"
    and b3:"finite basis" 
    and b5:"clinear F"
  shows "cbounded_linear F"
proof-
  include notation_norm
  have "\<exists>C>0. \<forall>\<psi> b. cmod (crepresentation basis \<psi> b) \<le> \<parallel>\<psi>\<parallel> * C"
    using finite_complex_span_representation_bounded[where B = basis] b2 b3 by blast
  then obtain C where s1: "cmod (crepresentation basis \<psi> b) \<le> \<parallel>\<psi>\<parallel> * C" 
    and s2: "C > 0"
  for \<psi> b by blast
  define M where "M = C * (\<Sum>a\<in>basis. \<parallel>F a\<parallel>)"
  have "\<parallel>F x\<parallel> \<le> \<parallel>x\<parallel> * M"
    for x
  proof-
    define r where "r b = crepresentation basis x b" for b
    have x_span: "x \<in> complex_vector.span basis"
      by (simp add: b1)
    have f0: "v \<in> basis"
      if "r v \<noteq> 0" for v
      using complex_vector.representation_ne_zero r_def that by auto       
    have w:"{a|a. r a \<noteq> 0} \<subseteq> basis"
      using f0 by blast
    hence f1: "finite {a|a. r a \<noteq> 0}"
      using b3 rev_finite_subset by auto 
    have f2: "(\<Sum>a| r a \<noteq> 0. r a *\<^sub>C a) = x"
      unfolding r_def
      using b2 complex_vector.sum_nonzero_representation_eq x_span
        Collect_cong  by fastforce
    have g1: "(\<Sum>a\<in>basis. crepresentation basis x a *\<^sub>C a) = x"
      by (simp add: b2 b3 complex_vector.sum_representation_eq x_span)
    have f3: "(\<Sum>a\<in>basis. r a *\<^sub>C a) = x"
      unfolding r_def
      by (simp add: g1) 
    hence "F x = F (\<Sum>a\<in>basis. r a *\<^sub>C a)"
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
    also have "\<dots> \<le> (\<Sum>a\<in>basis. \<parallel>x\<parallel> * C * \<parallel>F a\<parallel>)"      
      using sum_mono s1 unfolding r_def
      by (simp add: sum_mono mult_right_mono)
    also have "\<dots> \<le> \<parallel>x\<parallel> * C * (\<Sum>a\<in>basis. \<parallel>F a\<parallel>)"
      using sum_distrib_left
      by (smt sum.cong)
    also have "\<dots> = \<parallel>x\<parallel> * M"
      unfolding M_def
      by linarith 
    finally show ?thesis .
  qed
  thus ?thesis
    using b5 cbounded_linear_def
    using cbounded_linear_axioms_def by blast
qed

(* TODO move Complex_Normed *)
lemma cbounded_linear_finite_dim[simp, intro!]:
  fixes f :: \<open>'a::{cfinite_dim,complex_normed_vector} \<Rightarrow> 'b::complex_normed_vector\<close>
  shows \<open>cbounded_linear f = clinear f\<close>
proof (rule iffI)
  assume \<open>clinear f\<close>
  from finite_basis obtain basis :: \<open>'a set\<close> where basis: \<open>finite basis\<close> \<open>cindependent basis\<close> \<open>cspan basis = UNIV\<close>
    by auto
  with \<open>clinear f\<close> show \<open>cbounded_linear f\<close>
    apply (rule_tac cblinfun_operator_finite_dim[where basis=\<open>basis\<close>])
    by auto
next
  assume \<open>cbounded_linear f\<close>
  then show \<open>clinear f\<close>
    using cbounded_linear.clinear by blast
qed


lemma cblinfun_operator_basis_existence_uniq:
  fixes basis::"'a::chilbert_space set" and \<phi>::"'a \<Rightarrow> 'b::chilbert_space"
  assumes "complex_vector.span basis = UNIV"
    and "cindependent basis" (* TODO: does this really need independence? *)
    and "finite basis" 
    and "\<And>s. s\<in>basis \<Longrightarrow> F *\<^sub>V s = \<phi> s" (* TODO: why is this split into two? *)
    and "\<And>s. s\<in>basis \<Longrightarrow> G *\<^sub>V s = \<phi> s"
  shows \<open>F = G\<close>
proof-
  have "s\<in>basis \<Longrightarrow> (F-G) s = 0" for s
    using minus_cblinfun.rep_eq
    by (simp add: minus_cblinfun.rep_eq assms(4) assms(5))
  hence "F - G = 0"
    using cblinfun_operator_basis_zero_uniq[where F = "F - G" and basis = basis]
      assms(1) assms(2) assms(3) by auto
  thus ?thesis by simp
qed


lemma obn_enum_uniq:
  fixes f g::"'a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
  defines "basis == set (canonical_basis::'a list)"
  assumes "\<And>u. u \<in> basis \<Longrightarrow> f *\<^sub>V u = g *\<^sub>V u"
  shows  "f = g" 
proof-
  define h where "h = f - g"
  have "\<And>u. u \<in> basis \<Longrightarrow> h *\<^sub>V u = 0"
    using assms unfolding h_def
    by (simp add: assms(2) minus_cblinfun.rep_eq)
  hence "h = 0"
    using basis_def cblinfun_operator_basis_zero_uniq
      is_cindependent_set is_generator_set by auto
  thus ?thesis 
    unfolding h_def
    using eq_iff_diff_eq_0 by blast 
qed


lemma obn_enum_uniq_zero:
  fixes f ::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
  defines "basis == set (canonical_basis::'a list)"
  assumes "\<And>u. u \<in> basis \<Longrightarrow> f *\<^sub>V u = 0"
  shows  "f = 0" 
proof-
  have "cblinfun_apply f x = 0" for x
  proof-
    define a where "a = ((complex_vector.representation basis x)::'a \<Rightarrow> complex)"
    have a1: "a v \<noteq> 0 \<Longrightarrow> v \<in> basis" for v
      by (simp add: a_def complex_vector.representation_ne_zero)      
    have "finite {v. a v \<noteq> 0}"
      by (simp add: a_def complex_vector.finite_representation)      
    have f1: "cindependent basis"
      using basis_def canonical_basis_non_zero is_ortho_set_independent is_orthonormal by auto
    have "closure (cspan basis) = UNIV"
      using basis_def closure_UNIV is_generator_set
      by (metis )
    moreover have "closure (cspan basis) = cspan basis"
      by (simp add: basis_def span_finite_dim)        
    ultimately have "cspan basis = UNIV"
      by blast
    hence f2: "x \<in> cspan basis"
      by simp
    have x1: "a v *\<^sub>C (cblinfun_apply f v) = 0" 
      if "a v \<noteq> 0"
      for v
    proof-
      have "v \<in> basis"
        using that by (simp add: a1)
      hence "cblinfun_apply f v = 0"
        using assms(2) by auto          
      thus ?thesis by simp
    qed
    have "(\<Sum>v | a v \<noteq> 0. a v *\<^sub>C v) = x"
      unfolding a_def 
      using f1 f2 sum.cong Collect_cong DiffD1 DiffD2 Eps_cong \<open>finite {v. a v \<noteq> 0}\<close> a_def complex_vector.representation_def complex_vector.sum_nonzero_representation_eq subset_iff sum.mono_neutral_cong_right
      by fastforce      
    hence "cblinfun_apply f x = cblinfun_apply f (\<Sum>v | a v \<noteq> 0. a v *\<^sub>C v)"
      by simp
    also have "\<dots> = (\<Sum>v | a v \<noteq> 0. a v *\<^sub>C cblinfun_apply f v)"
      using \<open>finite {v. a v \<noteq> 0}\<close> clinear_finite_sum by blast
    also have "\<dots> = 0"
      using x1
      by simp 
    finally show ?thesis
      by simp 
  qed
  thus ?thesis
    by (simp add: cblinfun_ext) 
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
        have "cspan basisB = UNIV"
          using basisB_def is_generator_set  by auto 
        hence "v \<in> cspan basisB"
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

lemma cblinfun_extension_existsI:
  assumes "\<And>x. x\<in>S \<Longrightarrow> B *\<^sub>V x = \<phi> x"
  shows "cblinfun_extension_exists S \<phi>"
  using assms cblinfun_extension_exists_def by blast

lemma cindependent_finite_onb_enum:
  assumes a1: "cindependent A"
  shows "finite (A::'a::onb_enum set)"
proof(cases "set (canonical_basis::'a list) = {}")
  case True
  have "complex_vector.span (set (canonical_basis::'a list)) = {0}"
    by (simp add: True)
  moreover have "complex_vector.span (set (canonical_basis::'a list)) = UNIV"
    using is_generator_set
    by (simp add: ) 
  ultimately have "(UNIV::'a set) = {0}"
    by simp
  hence "finite (UNIV::'a set)"
    by (metis finite.emptyI finite.insertI)   
  thus ?thesis
    using rev_finite_subset by auto 
next
  case False
  define AA where "AA = cextend_basis A"
  have "complex_vector.span AA = UNIV"
    using complex_vector.span_extend_basis a1
    using AA_def by blast    
  moreover have "cindependent AA"
    using a1
    by (simp add: AA_def  complex_vector.independent_extend_basis)
  ultimately have "card AA = cdim (UNIV::'a set)"
    by (metis complex_vector.dim_eq_card_independent complex_vector.dim_span)
  also have "cdim (UNIV::'a set) = card (set (canonical_basis::'a list))"
    using complex_vector.dim_eq_card complex_vector.dim_span
    by (simp add: complex_vector.dim_eq_card is_cindependent_set is_generator_set)
  finally have r1: "card AA = card (set (canonical_basis::'a list))".
  have "finite (set (canonical_basis::'a list))"
    by simp    
  hence "card (set (canonical_basis::'a list)) \<noteq> 0"
    using False by auto    
  hence "finite AA"
    by (metis card.infinite r1)
  thus ?thesis unfolding AA_def
    using assms complex_vector.extend_basis_superset rev_finite_subset
    by (simp add: complex_vector.extend_basis_superset rev_finite_subset)
qed

lemma cblinfun_extension_exists_finite:
  fixes \<phi>::"'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector" 
  assumes a1: "cindependent S"
    and a2: "complex_vector.span S = UNIV"
    and a3: "finite S"
  shows "cblinfun_extension_exists S \<phi>"
proof-
  define f::"'a \<Rightarrow> 'b" 
    where "f = complex_vector.construct S \<phi>"
  have "clinear f"
    using linear_construct a1 f_def
    by (simp add: complex_vector.linear_construct ) 
  have "cbounded_linear f"
    using \<open>clinear f\<close> a1 a2 a3  cblinfun_operator_finite_dim by auto    
  then obtain B::"'a \<Rightarrow>\<^sub>C\<^sub>L 'b" 
    where "B *\<^sub>V x = f x" for x
    using cblinfun_apply_cases by blast
  have "B *\<^sub>V x = \<phi> x"
    if c1: "x\<in>S"
    for x
  proof-
    have "B *\<^sub>V x = f x"
      by (simp add: \<open>\<And>x. B *\<^sub>V x = f x\<close>)
    also have "\<dots> = \<phi> x"
      using a1 complex_vector.construct_basis f_def that
      by (simp add: complex_vector.construct_basis ) 
    finally show?thesis by blast
  qed
  thus ?thesis 
    unfolding cblinfun_extension_exists_def
    by blast
qed

lemma cblinfun_extension_exists:
  assumes "cblinfun_extension_exists S f"
    and "v \<in> S"
  shows "(cblinfun_extension S f) *\<^sub>V v = f v"
  by (smt assms(1) assms(2) cblinfun_extension_def cblinfun_extension_exists_def tfl_some)

subsection \<open>Unsorted\<close>

lemma cblinfun_apply_to_zero[simp]: "A *\<^sub>V 0 = 0"
  by (metis add_cancel_left_left cblinfun_apply_add)

(* TODO: replace by a more general lemma that shows Proj (A\<union>B) = Proj A + Proj B
         under orthogonality assumptions (using projection_union (other TODO)) *)
(* It follows from projection_union *)
lemma Proj_Span_insert:
  fixes S :: "'a::{onb_enum, chilbert_space} list"
    and a::'a 
  assumes a1: "is_ortho_set (set (a#S))" and a2: "distinct (a#S)"
  shows "Proj (Span (set (a#S))) = Proj (Span {a}) + Proj (Span (set S))"
proof-
  define d where "d = canonical_basis_length TYPE('a)"
  hence IH': "is_ortho_set (set S)"
    using assms is_onb_delete by auto    
  have IH0: "distinct S"
    using a2 by auto   
  have "closure (cspan (set S)) = cspan (set S)"
    by (simp add: span_finite_dim)    
  have d: "cspan (insert a (set S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> cspan (set S)}"
    using complex_vector.span_insert[where a = a and S = "(set S)"].
  moreover have "finite (insert a (set S))"
    by simp    
  ultimately have "closure (cspan (insert a (set S))) = 
        cspan {x. \<exists>k. x - k *\<^sub>C a \<in> cspan (set S)}"
    by (metis complex_vector.span_span span_finite_dim)
  hence s2: "space_as_set (Abs_clinear_space (closure (cspan (insert a (set S))))) 
        = cspan {x. \<exists>k. x - k *\<^sub>C a \<in> cspan (set S)}"
    by (metis Span.rep_eq space_as_set_inverse)
  have "closure (cspan (set S)) = cspan (set S)"
    by (simp add: span_finite_dim)    
  have ios: "is_ortho_set (set S)"
    by (simp add: IH')    
  have aS: "a \<notin> set S"
    using a2 by auto
  have p: "projection {x. \<exists>k. x - k *\<^sub>C a \<in> cspan (set S)} u
        = projection (cspan {a}) u
        + projection (cspan (set S)) u"
    for u   
  proof (rule projection_insert)
    show "\<langle>a, s\<rangle> = 0"
      if "s \<in> set S"
      for s :: 'a
      using that
      by (metis (no_types, lifting) Un_insert_right a1 aS insertI1 insert_is_Un is_ortho_set_def 
          list.simps(15) mk_disjoint_insert) 
    show "finite (set S)"
      by simp    
  qed
  have s1: "projection {x. \<exists>k. x - k *\<^sub>C a \<in> cspan (set S)} u
        = projection (cspan {a}) u + projection (cspan (set S)) u"
    for u
    by (simp add: p)    
  have "Proj (Span (set (a#S))) = cBlinfun (projection {x. \<exists>k. x - k *\<^sub>C a \<in> cspan (set S)})"
    unfolding Proj_def Span_def id_def
    by (metis \<open>cspan (insert a (set S)) = {x. \<exists>k. x - k *\<^sub>C a \<in> cspan (set S)}\<close> 
        complex_vector.span_span list.simps(15) map_fun_apply s2) 

  also have "\<dots> = (cBlinfun (\<lambda>u. projection (cspan {a}) u
                   + projection (cspan (set S)) u))"
    using s1
    by presburger 
  also have "\<dots> = cBlinfun (\<lambda>u. projection (cspan {a}) u)
               +  cBlinfun (\<lambda>u. projection (cspan (set S)) u)"
    unfolding plus_cblinfun_def apply auto
    by (metis (no_types, lifting) List.finite_set List.set_insert Proj.rep_eq Span.rep_eq
        cblinfun_apply_inverse finite.emptyI finite_list span_finite_dim)
  also have "\<dots> = Proj (Abs_clinear_space (cspan {a}))
               +  Proj (Abs_clinear_space (cspan (set S)))"
    unfolding Proj_def apply auto
    by (metis Span.rep_eq \<open>closure (cspan (set S)) = cspan (set S)\<close> finite.emptyI 
        finite.insertI space_as_set_inverse span_finite_dim)
  also have "\<dots> = Proj (Span {a}) + Proj (Span (set S))"
    by (simp add: Span.abs_eq span_finite_dim)
  finally show "Proj (Span (set (a#S))) = Proj (Span {a}) + Proj (Span (set S))".
qed

(* TODO: rename to butterfly_def *)
definition butterfly_def': "butterfly (s::'a::complex_normed_vector) (t::'b::chilbert_space)
   = vector_to_cblinfun s o\<^sub>C\<^sub>L (vector_to_cblinfun t :: complex \<Rightarrow>\<^sub>C\<^sub>L _)*"

abbreviation "selfbutter s \<equiv> butterfly s s"

lemma butterfly_def: "butterfly s t = (vector_to_cblinfun s :: 'c::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)
                                   o\<^sub>C\<^sub>L (vector_to_cblinfun t :: 'c \<Rightarrow>\<^sub>C\<^sub>L _)*"
  (is "_ = ?rhs") for s :: "'a::complex_normed_vector" and t :: "'b::chilbert_space"
proof -
  let ?isoAC = "1 :: 'c \<Rightarrow>\<^sub>C\<^sub>L complex"
  let ?isoCA = "1 :: complex \<Rightarrow>\<^sub>C\<^sub>L 'c"
  let ?vector = "vector_to_cblinfun :: _ \<Rightarrow> ('c \<Rightarrow>\<^sub>C\<^sub>L _)"

  have "butterfly s t =
    (?vector s o\<^sub>C\<^sub>L ?isoCA) o\<^sub>C\<^sub>L (?vector t o\<^sub>C\<^sub>L ?isoCA)*"
    unfolding butterfly_def' one_vector_to_cblinfun by simp
  also have "\<dots> = ?vector s o\<^sub>C\<^sub>L (?isoCA o\<^sub>C\<^sub>L ?isoCA*) o\<^sub>C\<^sub>L (?vector t)*"
    by (metis (no_types, lifting) cblinfun_apply_assoc times_adjoint)
  also have "\<dots> = ?rhs"
    by simp
  finally show ?thesis
    by simp
qed

lemma butterfly_times_right: "butterfly \<psi> \<phi> o\<^sub>C\<^sub>L a = butterfly \<psi> (a* *\<^sub>V \<phi>)"
  unfolding butterfly_def'
  by (simp add: cblinfun_apply_assoc vector_to_cblinfun_applyOp)  

lemma butterfly_apply: "butterfly \<psi> \<psi>' *\<^sub>V \<phi> = \<langle>\<psi>', \<phi>\<rangle> *\<^sub>C \<psi>"
  by (simp add: butterfly_def' times_applyOp)


lemma vector_to_cblinfun_0[simp]: "vector_to_cblinfun 0 = 0"
  by (metis cblinfun_apply_to_zero timesOp0 vector_to_cblinfun_applyOp)

lemma butterfly_0[simp]: "butterfly 0 a = 0"
  by (simp add: butterfly_def')

lemma butterfly_0'[simp]: "butterfly a 0 = 0"
  by (simp add: butterfly_def')

lemma norm_butterfly: "norm (butterfly \<psi> \<phi>) = norm \<psi> * norm \<phi>"
proof (cases "\<phi>=0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis 
    unfolding norm_cblinfun.rep_eq
    thm onormI[OF _ False]
  proof (rule onormI[OF _ False])
    fix x 

    have "cmod \<langle>\<phi>, x\<rangle> * norm \<psi> \<le> norm \<psi> * norm \<phi> * norm x"
      using norm_cauchy_schwarz[of \<phi> x]
      by (metis mult.assoc mult.commute norm_imp_pos_and_ge ordered_comm_semiring_class.comm_mult_left_mono)
    thus "norm (butterfly \<psi> \<phi> *\<^sub>V x) \<le> norm \<psi> * norm \<phi> * norm x"
      by (simp add: butterfly_apply power2_eq_square)

    show "norm (butterfly \<psi> \<phi> *\<^sub>V \<phi>) = norm \<psi> * norm \<phi> * norm \<phi>"
      by (simp add: butterfly_apply power2_eq_square power2_norm_eq_cinner[symmetric])
      thm power2_norm_eq_cinner
  qed
qed

lemma butterfly_scaleC1: "butterfly (c *\<^sub>C \<psi>) \<phi> = c *\<^sub>C butterfly \<psi> \<phi>"
  unfolding butterfly_def' vector_to_cblinfun_scalar_times scalar_times_adj
  by (simp add: cnj_x_x)

lemma butterfly_scaleC2: "butterfly \<psi> (c *\<^sub>C \<phi>) = cnj c *\<^sub>C butterfly \<psi> \<phi>"
  unfolding butterfly_def' vector_to_cblinfun_scalar_times scalar_times_adj
  by (simp add: cnj_x_x)

lemma butterfly_scaleR1: "butterfly (r *\<^sub>R \<psi>) \<phi> = r *\<^sub>C butterfly \<psi> \<phi>"
  by (simp add: butterfly_scaleC1 scaleR_scaleC)

lemma butterfly_scaleR2: "butterfly \<psi> (r *\<^sub>R \<phi>) = r *\<^sub>C butterfly \<psi> \<phi>"
  by (simp add: butterfly_scaleC2 scaleR_scaleC)

lemma inj_selfbutter: 
  assumes "selfbutter x = selfbutter y"
  shows "\<exists>c. cmod c = 1 \<and> x = c *\<^sub>C y"
proof (cases "x = 0")
  case True
  from assms have "y = 0"
    using norm_butterfly
    by (metis True butterfly_0 divisors_zero norm_eq_zero)
  with True show ?thesis
    using norm_one by fastforce
next
  case False
  define c where "c = \<langle>y, x\<rangle> / \<langle>x, x\<rangle>"
  have "\<langle>x, x\<rangle> *\<^sub>C x = selfbutter x *\<^sub>V x"
    by (simp add: butterfly_apply)
  also have "\<dots> = selfbutter y *\<^sub>V x"
    using assms by simp
  also have "\<dots> = \<langle>y, x\<rangle> *\<^sub>C y"
    by (simp add: butterfly_apply)
  finally have xcy: "x = c *\<^sub>C y"
    by (simp add: c_def ceq_vector_fraction_iff)
  have "cmod c * norm x = cmod c * norm y"
    using assms norm_butterfly
    by (smt (verit, ccfv_SIG) \<open>\<langle>x, x\<rangle> *\<^sub>C x = selfbutter x *\<^sub>V x\<close> \<open>selfbutter y *\<^sub>V x = \<langle>y, x\<rangle> *\<^sub>C y\<close> cinner_scaleC_right complex_vector.scale_left_commute complex_vector.scale_right_imp_eq mult_cancel_left norm_eq_sqrt_cinner norm_eq_zero scaleC_scaleC xcy)
  also have "cmod c * norm y = norm (c *\<^sub>C y)"
    by simp
  also have "\<dots> = norm x"
    unfolding xcy[symmetric] by simp
  finally have c: "cmod c = 1"
    by (simp add: False)
  from c xcy show ?thesis
    by auto
qed

lemma isometry_vector_to_cblinfun:
  assumes "norm x = 1"
  shows "isometry (vector_to_cblinfun x)"
  by (simp add: isometry_def cinner_norm_sq assms)


lemma image_vector_to_cblinfun[simp]: "vector_to_cblinfun x *\<^sub>S top = Span {x}"
proof transfer
  show "closure (range (\<lambda>\<phi>::'b. one_dim_isom \<phi> *\<^sub>C x)) = closure (cspan {x})"
    for x :: 'a
  proof (rule arg_cong [where f = closure])
    have "k *\<^sub>C x \<in> range (\<lambda>\<phi>. one_dim_isom \<phi> *\<^sub>C x)"
      for k
      by (smt one_dim_isom_inverse range_eqI)
    thus "range (\<lambda>\<phi>. one_dim_isom (\<phi>::'b) *\<^sub>C x) = cspan {x}"
      unfolding complex_vector.span_singleton
      by auto
  qed
qed



lemma butterfly_proj:
  assumes "norm x = 1"
  shows "selfbutter x = proj x"
proof -
  define B and \<phi> :: "complex \<Rightarrow>\<^sub>C\<^sub>L 'a"
    where "B = selfbutter x" and "\<phi> = vector_to_cblinfun x"
  then have B: "B = \<phi> o\<^sub>C\<^sub>L \<phi>*"
    unfolding butterfly_def' by simp
  have \<phi>adj\<phi>: "\<phi>* o\<^sub>C\<^sub>L \<phi> = idOp"
    by (simp add: \<phi>_def cinner_norm_sq assms)
  have "B o\<^sub>C\<^sub>L B = \<phi> o\<^sub>C\<^sub>L (\<phi>* o\<^sub>C\<^sub>L \<phi>) o\<^sub>C\<^sub>L \<phi>*"
    by (simp add: B cblinfun_apply_assoc)
  also have "\<dots> = B"
    unfolding \<phi>adj\<phi> by (simp add: B)
  finally have idem: "B o\<^sub>C\<^sub>L B = B".
  have herm: "B = B*"
    unfolding B by simp
  from idem herm have BProj: "B = Proj (B *\<^sub>S top)"
    by (rule Proj_I)
  have "B *\<^sub>S top = Span {x}"
    by (metis \<open>\<phi> o\<^sub>C\<^sub>L (\<phi>* o\<^sub>C\<^sub>L \<phi>) o\<^sub>C\<^sub>L \<phi>* = B\<close> \<phi>_def \<phi>adj\<phi> assms cblinfun_apply_assoc_subspace 
        image_vector_to_cblinfun isometry_vector_to_cblinfun range_adjoint_isometry times_idOp1) 
  with BProj show "B = proj x"
    by simp
qed

lemma butterfly_isProjector:
  \<open>norm x = 1 \<Longrightarrow> isProjector (selfbutter x)\<close>
  by (subst butterfly_proj, simp_all)

lemma Proj_bot[simp]: "Proj bot = 0"
  by (metis Bounded_Operators.timesScalarSpace_0 Proj_I isProjector0 isProjector_algebraic 
      zero_clinear_space_def)

lemma Proj_ortho_compl:
  "Proj (- X) = idOp - Proj X"
proof (transfer , auto)
  show "projection (orthogonal_complement X) = (\<lambda>x. (x::'a) - projection X x)"
    if "closed_subspace (X::'a set)"
    for X :: "'a set"
    using that ortho_decomp
    by (metis add_diff_cancel_left') 
qed


lemma Proj_inj: 
  assumes a1: "Proj X = Proj Y"
  shows "X = Y"
  by (metis a1 imageOp_Proj)

lemma cblinfun_apply_in_image[simp]: "A *\<^sub>V \<psi> \<in> space_as_set (A *\<^sub>S \<top>)"
  by (metis applyOpSpace.rep_eq closure_subset in_mono range_eqI top_clinear_space.rep_eq)

lemma cbilinear_timesOp[simp]: "cbilinear timesOp"
  by (auto intro!: clinearI simp add: cbilinear_def cblinfun_apply_dist1 cblinfun_apply_dist2)


lemma one_dim_isom_idOp[simp]: \<open>one_dim_isom idOp = (1::complex)\<close>
  by (metis one_dim_idOp one_dim_isom_one)

lemma one_dim_isom_cblinfun_apply[simp]: \<open>one_dim_isom (a o\<^sub>C\<^sub>L b) = one_dim_isom b o\<^sub>C\<^sub>L one_dim_isom a\<close>
  by (smt (z3) of_complex_def one_comp_one_cblinfun one_dim_1_times_a_eq_a one_dim_isom_def one_dim_isom_scaleC op_scalar_op scalar_op_op)

lemma one_dim_isom_cblinfun_apply_complex[simp]: \<open>one_dim_isom (a o\<^sub>C\<^sub>L b) = one_dim_isom b * one_dim_isom a\<close>
  by (smt (z3) complex_scaleC_def one_comp_one_cblinfun one_dim_1_times_a_eq_a one_dim_isom_def one_dim_isom_of_complex one_dim_isom_one one_dim_isom_scaleC one_dim_prod op_scalar_op scalar_op_op)

lemma one_dim_isom_adjoint[simp]: \<open>one_dim_isom (A*) = (one_dim_isom A)*\<close>
  by (smt (z3) one_cblinfun_adj one_dim_1_times_a_eq_a one_dim_isom_one one_dim_isom_scaleC scalar_times_adj)

lemma one_dim_isom_adjoint_complex[simp]: \<open>one_dim_isom (A*) = cnj (one_dim_isom A)\<close>
  by (metis (mono_tags, lifting) one_cblinfun_adj one_dim_isom_idem one_dim_scaleC_1 scalar_times_adj)


unbundle no_cblinfun_notation

end

(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Main results:
- bounded: Definition of complex bounded operators. Instantiation as a complex Banach space.

*)


theory Bounded_Operators
  imports Complex_Inner_Product Real_Bounded_Operators

begin

section \<open>Real bounded operators with complex scalar product\<close>

instantiation rbounded :: (real_normed_vector, complex_normed_vector) "complex_vector"
begin
lift_definition scaleC_rbounded :: \<open>complex \<Rightarrow>
 ('a::real_normed_vector, 'b::complex_normed_vector) rbounded \<Rightarrow>
 ('a, 'b) rbounded\<close>
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
  show "((*\<^sub>R) r::('a, 'b) rbounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
  proof
    show "r *\<^sub>R (x::('a, 'b) rbounded) = complex_of_real r *\<^sub>C x"
      for x :: "('a, 'b) rbounded"
      apply transfer
      by (simp add: scaleR_scaleC)
  qed

  show "a *\<^sub>C ((x::('a, 'b) rbounded) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "('a, 'b) rbounded"
      and y :: "('a, 'b) rbounded"
    apply transfer
    by (simp add: scaleC_add_right)

  show "(a + b) *\<^sub>C (x::('a, 'b) rbounded) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) rbounded"
    apply transfer
    by (simp add: scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::('a, 'b) rbounded) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) rbounded"
    apply transfer
    by simp

  show "1 *\<^sub>C (x::('a, 'b) rbounded) = x"
    for x :: "('a, 'b) rbounded"
    apply transfer
  proof
    fix f :: \<open>'a\<Rightarrow>'b\<close> and x :: 'a
    show \<open>1 *\<^sub>C f x = f x\<close>
      by auto
  qed
qed  
end

instantiation rbounded :: (real_normed_vector, complex_normed_vector) "complex_normed_vector"
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
    for a::complex and x::\<open>('a, 'b) rbounded\<close>
    apply transfer
    apply (rule 1)
    by blast
qed
end

instantiation rbounded :: (real_normed_vector, cbanach) "cbanach"
begin
instance..
end


section \<open>Complex bounded operators\<close>

typedef (overloaded) ('a::complex_normed_vector, 'b::complex_normed_vector) bounded
  = \<open>{A::'a \<Rightarrow> 'b. bounded_clinear A}\<close>
  using bounded_clinear_zero by blast

setup_lifting type_definition_bounded

lift_definition rbounded_of_bounded::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) bounded
\<Rightarrow> ('a,'b) rbounded\<close> is "id"
  apply transfer apply auto
  by (simp add: bounded_clinear.bounded_linear)

lemma rbounded_of_bounded_inj:
  \<open>rbounded_of_bounded f = rbounded_of_bounded g \<Longrightarrow> f = g\<close>
  by (metis Rep_bounded_inject rbounded_of_bounded.rep_eq)

lemma rbounded_of_bounded_inv:
  \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x) \<Longrightarrow> \<exists> g. rbounded_of_bounded g = f\<close>
  apply transfer apply auto
  by (simp add: bounded_linear_bounded_clinear)

lemma rbounded_of_bounded_inv_uniq:
  \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x) \<Longrightarrow> \<exists>! g. rbounded_of_bounded g = f\<close>
  using rbounded_of_bounded_inv rbounded_of_bounded_inj
  by blast

lemma rbounded_of_bounded_prelim:
  \<open>\<forall> c. \<forall> x. Rep_rbounded (rbounded_of_bounded g) (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded (rbounded_of_bounded g) x)\<close>
  apply transfer
  apply auto
  by (simp add: bounded_clinear_def clinear.scaleC)


definition bounded_of_rbounded::\<open>('a::complex_normed_vector, 'b::complex_normed_vector) rbounded \<Rightarrow>
('a, 'b) bounded\<close> where
  \<open>bounded_of_rbounded f = (THE g. rbounded_of_bounded g = f)\<close>

lemma bounded_rbounded:
  \<open>bounded_of_rbounded (rbounded_of_bounded f) = f\<close>
  by (simp add: bounded_of_rbounded_def rbounded_of_bounded_inj the_equality)

lemma rbounded_bounded:
  \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x)
 = c *\<^sub>C (Rep_rbounded f x)
 \<Longrightarrow> rbounded_of_bounded (bounded_of_rbounded f) = f\<close> 
  by (metis Abs_bounded_inverse Rep_rbounded Rep_rbounded_inject bounded_linear_bounded_clinear bounded_rbounded mem_Collect_eq rbounded_of_bounded.rep_eq)


instantiation bounded :: (complex_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
definition zero_bounded::"('a,'b) bounded" 
  where "zero_bounded = bounded_of_rbounded (0::('a,'b) rbounded)"

lemma rbounded_of_bounded_zero:
  \<open>rbounded_of_bounded 0 = 0\<close>
  by (simp add: Bounded_Operators.zero_bounded_def rbounded_bounded zero_rbounded.rep_eq)

lemma bounded_of_rbounded_zero:
  \<open>bounded_of_rbounded 0 = 0\<close>
  by (simp add: zero_bounded_def)

definition plus_bounded::"('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" 
  where "plus_bounded f g =  bounded_of_rbounded ( (rbounded_of_bounded f)+(rbounded_of_bounded g) )"

lemma bounded_of_rbounded_plus:
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
    and \<open>\<forall> c. \<forall> x. Rep_rbounded g (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded g x)\<close>
  shows \<open>bounded_of_rbounded (f + g) = bounded_of_rbounded f + bounded_of_rbounded g\<close>
  using assms
  by (simp add: plus_bounded_def rbounded_bounded) 

lemma rbounded_of_bounded_plus:
  \<open>rbounded_of_bounded (f + g) = rbounded_of_bounded f + rbounded_of_bounded g\<close>
  by (simp add: plus_bounded_def plus_rbounded.rep_eq rbounded_bounded rbounded_of_bounded_prelim scaleC_add_right)

definition uminus_bounded::"('a,'b) bounded \<Rightarrow> ('a,'b) bounded" 
  where "uminus_bounded f =  bounded_of_rbounded (- (rbounded_of_bounded f))"

lemma rbounded_of_bounded_uminus:
  \<open>rbounded_of_bounded (- f) = - (rbounded_of_bounded f) \<close>
  by (simp add: rbounded_bounded rbounded_of_bounded_prelim uminus_bounded_def uminus_rbounded.rep_eq)

lemma bounded_of_rbounded_uminus:
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
  shows  \<open>bounded_of_rbounded (- f) = - (bounded_of_rbounded f)\<close>
  using assms
  by (simp add: rbounded_bounded uminus_bounded_def)

definition minus_bounded::"('a,'b) bounded \<Rightarrow> ('a,'b) bounded \<Rightarrow> ('a,'b) bounded" 
  where "minus_bounded f g =  bounded_of_rbounded ( (rbounded_of_bounded f)-(rbounded_of_bounded g) )"

lemma bounded_of_rbounded_minus:
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
    and \<open>\<forall> c. \<forall> x. Rep_rbounded g (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded g x)\<close>
  shows \<open>bounded_of_rbounded (f - g) = bounded_of_rbounded f - bounded_of_rbounded g\<close>
  using assms
  by (simp add: minus_bounded_def rbounded_bounded) 

lemma rbounded_of_bounded_minus:
  \<open>rbounded_of_bounded (f - g) = rbounded_of_bounded f - rbounded_of_bounded g\<close>
  by (metis (mono_tags, lifting) bounded_rbounded minus_bounded_def pth_2 rbounded_of_bounded_plus rbounded_of_bounded_uminus)

definition scaleC_bounded :: \<open>complex \<Rightarrow> ('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded\<close>
  where "scaleC_bounded c f =  bounded_of_rbounded ( c *\<^sub>C (rbounded_of_bounded f) )"

lemma bounded_of_rbounded_scaleC:
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
  shows \<open>bounded_of_rbounded ( c *\<^sub>C f ) = c *\<^sub>C (bounded_of_rbounded f)\<close>
  using assms
  by (simp add: rbounded_bounded scaleC_bounded_def)

lemma rbounded_of_bounded_scaleC:
  \<open>rbounded_of_bounded ( c *\<^sub>C f ) = c *\<^sub>C (rbounded_of_bounded f)\<close>
proof -
  obtain cc :: "('a, 'b) rbounded \<Rightarrow> complex" and aa :: "('a, 'b) rbounded \<Rightarrow> 'a" where
    "\<forall>r. Rep_rbounded r (cc r *\<^sub>C aa r) \<noteq> cc r *\<^sub>C Rep_rbounded r (aa r) \<or> rbounded_of_bounded (bounded_of_rbounded r) = r"
    using rbounded_bounded by moura
  then show ?thesis
    by (simp add: rbounded_of_bounded_prelim scaleC_bounded_def scaleC_rbounded.rep_eq)
qed

definition scaleR_bounded :: \<open>real \<Rightarrow> ('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded\<close>
  where "scaleR_bounded c f =  bounded_of_rbounded ( c *\<^sub>R (rbounded_of_bounded f) )"

lemma bounded_of_rbounded_scaleR:
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
  shows \<open>bounded_of_rbounded ( c *\<^sub>R f ) = c *\<^sub>R (bounded_of_rbounded f)\<close>
  using assms
  by (simp add: rbounded_bounded scaleR_bounded_def)

lemma rbounded_of_bounded_scaleR:
  \<open>rbounded_of_bounded ( c *\<^sub>R f ) = c *\<^sub>R (rbounded_of_bounded f)\<close>
  using Rep_rbounded Rep_rbounded_inverse linear_simps(5) mem_Collect_eq rbounded_bounded rbounded_of_bounded.rep_eq rbounded_of_bounded_prelim scaleC_rbounded.rep_eq scaleR_bounded_def scaleR_rbounded.rep_eq
  by smt 

lemma bounded_of_rbounded_Abs_rbounded:
  \<open>bounded_of_rbounded ( Abs_rbounded (Rep_bounded f) ) = f\<close>
  by (metis Quotient_bounded Quotient_rel_rep Rep_bounded_inverse bounded_rbounded rbounded_of_bounded.abs_eq)

definition norm_bounded :: \<open>('a, 'b) bounded \<Rightarrow> real\<close>
  where \<open>norm_bounded f = norm (rbounded_of_bounded f)\<close>

definition dist_bounded :: \<open>('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded \<Rightarrow> real\<close>
  where \<open>dist_bounded f g = dist (rbounded_of_bounded f) (rbounded_of_bounded g)\<close>

definition sgn_bounded :: \<open>('a, 'b) bounded \<Rightarrow> ('a, 'b) bounded\<close>
  where \<open>sgn_bounded f =  bounded_of_rbounded ( sgn (rbounded_of_bounded f))\<close>

definition uniformity_bounded :: \<open>( ('a, 'b) bounded \<times> ('a, 'b) bounded ) filter\<close>
  where \<open>uniformity_bounded = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a, 'b) bounded) y < e})\<close>

definition open_bounded :: \<open>(('a, 'b) bounded) set \<Rightarrow> bool\<close>
  where \<open>open_bounded U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::('a, 'b) bounded) = x \<longrightarrow> y \<in> U)\<close>

instance
proof
  show \<open>a + b + c = a + (b + c)\<close>
    for a :: "('a, 'b) bounded"
      and b :: "('a, 'b) bounded"
      and c :: "('a, 'b) bounded"
  proof -
    have f1: "\<forall>r ra. ((\<exists>c a. Rep_rbounded r (c *\<^sub>C (a::'a)) \<noteq> c *\<^sub>C (Rep_rbounded r a::'b)) \<or> (\<exists>c a. Rep_rbounded ra (c *\<^sub>C a) \<noteq> c *\<^sub>C Rep_rbounded ra a)) \<or> bounded_of_rbounded (r + ra) = bounded_of_rbounded r + bounded_of_rbounded ra"
      using bounded_of_rbounded_plus by blast
    obtain cc :: "('a, 'b) rbounded \<Rightarrow> complex" and aa :: "('a, 'b) rbounded \<Rightarrow> 'a" where
      "\<forall>x0. (\<exists>v2 v3. Rep_rbounded x0 (v2 *\<^sub>C v3) \<noteq> v2 *\<^sub>C Rep_rbounded x0 v3) = (Rep_rbounded x0 (cc x0 *\<^sub>C aa x0) \<noteq> cc x0 *\<^sub>C Rep_rbounded x0 (aa x0))"
      by moura
    then obtain cca :: "('a, 'b) rbounded \<Rightarrow> complex" and aaa :: "('a, 'b) rbounded \<Rightarrow> 'a" where
      f2: "\<forall>r ra. (Rep_rbounded r (cca r *\<^sub>C aaa r) \<noteq> cca r *\<^sub>C Rep_rbounded r (aaa r) \<or> Rep_rbounded ra (cc ra *\<^sub>C aa ra) \<noteq> cc ra *\<^sub>C Rep_rbounded ra (aa ra)) \<or> bounded_of_rbounded (r + ra) = bounded_of_rbounded r + bounded_of_rbounded ra"
      using f1 by simp
    then have "bounded_of_rbounded (rbounded_of_bounded a + rbounded_of_bounded b + rbounded_of_bounded c) = bounded_of_rbounded (rbounded_of_bounded a + rbounded_of_bounded b) + bounded_of_rbounded (rbounded_of_bounded c)"
      by (simp add: plus_rbounded.rep_eq rbounded_of_bounded_prelim scaleC_add_right)
    then have f3: "bounded_of_rbounded (rbounded_of_bounded a + (rbounded_of_bounded b + rbounded_of_bounded c)) = a + b + c"
      by (simp add: Bounded_Operators.plus_bounded_def bounded_rbounded ordered_field_class.sign_simps(1))
    have "bounded_of_rbounded (rbounded_of_bounded a) + bounded_of_rbounded (rbounded_of_bounded b + rbounded_of_bounded c) = a + (b + c)"
      by (simp add: Bounded_Operators.plus_bounded_def bounded_rbounded)
    then show ?thesis
      using f3 f2 by (simp add: plus_rbounded.rep_eq rbounded_of_bounded_prelim scaleC_add_right)
  qed

  show \<open>(0::('a, 'b) bounded) + a = a\<close>
    for a :: "('a, 'b) bounded"
    unfolding plus_bounded_def
    by (simp add: bounded_rbounded rbounded_of_bounded_zero) 

  show \<open>a + b = b + a\<close>
    for a :: "('a, 'b) bounded"
      and b :: "('a, 'b) bounded"
    by (simp add: add.commute plus_bounded_def)

  show \<open>- a + a = 0\<close>
    for a :: "('a, 'b) bounded"
    by (simp add: Bounded_Operators.plus_bounded_def Bounded_Operators.rbounded_of_bounded_uminus zero_bounded_def)

  show \<open>a - b = a + - b\<close>
    for a :: "('a, 'b) bounded"
      and b :: "('a, 'b) bounded"
    using minus_bounded_def plus_bounded_def rbounded_of_bounded_uminus by auto

  show \<open>((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
    for r :: real
    apply transfer
    unfolding scaleR_bounded_def  rbounded_of_bounded_def
    apply auto
  proof
    show "bounded_of_rbounded (r *\<^sub>R Abs_rbounded (Rep_bounded (f::('a, 'b) bounded))) = complex_of_real r *\<^sub>C f"
      for r :: real
        and f :: "('a, 'b) bounded"
    proof-
      have \<open>bounded_of_rbounded (r *\<^sub>R Abs_rbounded (Rep_bounded f))
        = r *\<^sub>R bounded_of_rbounded (Abs_rbounded (Rep_bounded f))\<close>
        by (metis Bounded_Operators.scaleR_bounded_def Rep_rbounded_inverse bounded_of_rbounded_Abs_rbounded rbounded_of_bounded.rep_eq)
      moreover have \<open>bounded_of_rbounded (Abs_rbounded (Rep_bounded f)) = f\<close>
        by (simp add: bounded_of_rbounded_Abs_rbounded)
      ultimately show ?thesis
        by (simp add: Bounded_Operators.scaleC_bounded_def Bounded_Operators.scaleR_bounded_def scaleR_scaleC)
    qed
  qed

  show \<open>a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    for a :: complex
      and x :: "('a, 'b) bounded"
      and y :: "('a, 'b) bounded"
    by (metis (mono_tags) plus_bounded_def rbounded_of_bounded_plus rbounded_of_bounded_scaleC scaleC_add_right scaleC_bounded_def)

  show \<open>(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x\<close>
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) bounded"
    by (metis (mono_tags) plus_bounded_def rbounded_of_bounded_scaleC scaleC_bounded_def scaleC_left.add)

  show \<open>a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x\<close>
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) bounded"
    using rbounded_of_bounded_scaleC scaleC_bounded_def by auto

  show \<open>1 *\<^sub>C x = x\<close>
    for x :: "('a, 'b) bounded"
    by (simp add: Bounded_Operators.scaleC_bounded_def bounded_rbounded)

  show \<open>dist x y = norm (x - y)\<close>
    for x :: "('a, 'b) bounded"
      and y :: "('a, 'b) bounded"
    by (simp add: dist_bounded_def dist_norm norm_bounded_def rbounded_of_bounded_minus)

  show \<open>sgn x = (inverse (norm x)) *\<^sub>R x\<close>
    for x :: "('a, 'b) bounded"
    by (simp add: norm_bounded_def scaleR_bounded_def sgn_bounded_def sgn_div_norm)

  show \<open>uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a, 'b) bounded) y < e})\<close>
    by (simp add: Bounded_Operators.uniformity_bounded_def)

  show \<open>open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::('a, 'b) bounded) = x \<longrightarrow> y \<in> U)\<close>
    for U :: "('a, 'b) bounded set"
    by (simp add: Bounded_Operators.open_bounded_def)

  show \<open>(norm x = 0) = (x = 0)\<close>
    for x :: "('a, 'b) bounded"
  proof -
    have f1: "bounded_of_rbounded (0::('a, 'b) rbounded) = 0"
      by (simp add: zero_bounded_def)
    { assume "x \<noteq> 0"
      then have "x \<noteq> 0 \<and> bounded_of_rbounded 0 \<noteq> x"
        using f1 by meson
      then have ?thesis
        by (metis bounded_rbounded norm_bounded_def norm_zero zero_less_norm_iff) }
    then show ?thesis
      using Bounded_Operators.rbounded_of_bounded_zero norm_bounded_def by auto
  qed

  show \<open>norm (x + y) \<le> norm x + norm y\<close>
    for x :: "('a, 'b) bounded"
      and y :: "('a, 'b) bounded"
    by (simp add: norm_bounded_def norm_triangle_ineq rbounded_of_bounded_plus)

  show \<open>norm (a *\<^sub>C x) = cmod a * norm x\<close>
    for a :: complex
      and x :: "('a, 'b) bounded"
    using norm_bounded_def rbounded_of_bounded_scaleC by auto    

  show \<open>norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x\<close>
    for a :: real
      and x :: "('a, 'b) bounded"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x a. norm (a *\<^sub>C x) = cmod a * norm (x::('a, 'b) bounded)\<close>
      of_real_mult
    by simp

  show \<open>a *\<^sub>R (x + y) = a *\<^sub>R x +  a *\<^sub>R y\<close>
    for a :: real
      and x y :: "('a, 'b) bounded"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x y a. a *\<^sub>C (x + y) = a *\<^sub>C x +  a *\<^sub>C (y::('a, 'b) bounded)\<close>
      of_real_mult
    by simp

  show \<open>(a + b) *\<^sub>R x = a *\<^sub>R x +  b *\<^sub>R x\<close>
    for a b :: real
      and x :: "('a, 'b) bounded"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x b a. (a + b) *\<^sub>C (x::('a,'b) bounded) = a *\<^sub>C x +  b *\<^sub>C x\<close>
      of_real_mult
    by simp

  show \<open>a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x\<close>
    for a b :: real
      and x :: "('a, 'b) bounded"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x b a. a *\<^sub>C b *\<^sub>C (x::('a, 'b) bounded) = (a * b) *\<^sub>C x\<close>
      of_real_mult
    by simp

  show \<open>1 *\<^sub>R x = x\<close>
    for x :: "('a, 'b) bounded"
    using  \<open>\<And>r. ((*\<^sub>R) r::('a, 'b) bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close> 
      \<open>\<And>x. 1 *\<^sub>C (x::('a, 'b) bounded) = x\<close> of_real_1
    by simp

qed

end


instantiation bounded :: (complex_normed_vector, cbanach) "cbanach"
begin
lemma rbounded_of_bounded_Cauchy:
  assumes \<open>Cauchy f\<close>
  shows \<open>Cauchy (\<lambda> n. rbounded_of_bounded (f n))\<close>
  using assms unfolding Cauchy_def dist_bounded_def by auto

lemma bounded_of_rbounded_Cauchy:
  assumes \<open>Cauchy f\<close> and
      \<open>\<And> n::nat. \<forall> c. \<forall> x. Rep_rbounded (f n) (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded (f n) x)\<close>
  shows \<open>Cauchy (\<lambda> n. bounded_of_rbounded (f n))\<close>
  using assms  unfolding Cauchy_def dist_bounded_def
  by (simp add: rbounded_bounded)

lemma rbounded_of_bounded_lim:
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda> n. rbounded_of_bounded (f n)) \<longlonglongrightarrow> rbounded_of_bounded l\<close>
  proof
  show "\<forall>\<^sub>F x in sequentially. dist (rbounded_of_bounded (f x)) (rbounded_of_bounded l) < e"
    if "(0::real) < e"
    for e :: real
  proof-
    from \<open>f \<longlonglongrightarrow> l\<close>
    have \<open>\<forall>\<^sub>F x in sequentially. dist (f x) l < e\<close>
      by (simp add: tendstoD that)
    thus ?thesis 
      unfolding dist_bounded_def by blast
  qed
qed

lemma bounded_of_rbounded_complex_lim:
  fixes f::\<open>nat \<Rightarrow> ('a::complex_normed_vector, 'b::cbanach) rbounded\<close>
    and l::\<open>('a, 'b) rbounded\<close>
  assumes  \<open>f \<longlonglongrightarrow> l\<close> and
    \<open>\<And> n::nat. \<forall> c. \<forall> x. Rep_rbounded (f n) (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded (f n) x)\<close> 
  shows \<open>\<forall> c. \<forall> x. Rep_rbounded l (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded l x)\<close>
  proof-
    have \<open>Rep_rbounded l (c *\<^sub>C x) = c *\<^sub>C Rep_rbounded l x\<close>
    for c::complex and x
    proof-
      have \<open>(\<lambda> n. Rep_rbounded (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> Rep_rbounded l (c *\<^sub>C x)\<close>
        by (simp add: assms(1) onorm_strong)        
      moreover have \<open>(\<lambda> n. c *\<^sub>C (Rep_rbounded (f n) x) ) \<longlonglongrightarrow> c *\<^sub>C (Rep_rbounded l x)\<close>
      proof-
        have \<open>isCont ((*\<^sub>C) c) y\<close>
          for y::'b
          using isCont_scaleC by auto
        hence \<open>isCont ((*\<^sub>C) c) (Rep_rbounded l x)\<close>
          by simp
        thus ?thesis
          using assms(1) isCont_tendsto_compose onorm_strong by blast 
      qed
      moreover have \<open>Rep_rbounded (f n) (c *\<^sub>C x) =  c *\<^sub>C (Rep_rbounded (f n) x)\<close>
        for n
        by (simp add: assms(2))
      ultimately have \<open>(\<lambda> n. Rep_rbounded (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> c *\<^sub>C (Rep_rbounded l x)\<close>
        by simp
      thus ?thesis
        using  \<open>(\<lambda> n. Rep_rbounded (f n) (c *\<^sub>C x) ) \<longlonglongrightarrow> Rep_rbounded l (c *\<^sub>C x)\<close> LIMSEQ_unique 
        by blast
    qed
    thus ?thesis by blast
qed  

lemma bounded_of_rbounded_lim:
  fixes f::\<open>nat \<Rightarrow> ('a::complex_normed_vector, 'b::cbanach) rbounded\<close>
    and l::\<open>('a, 'b) rbounded\<close>
  assumes  \<open>f \<longlonglongrightarrow> l\<close> and
      \<open>\<And> n::nat. \<forall> c. \<forall> x. Rep_rbounded (f n) (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded (f n) x)\<close>
  shows \<open>(\<lambda> n. bounded_of_rbounded (f n)) \<longlonglongrightarrow> bounded_of_rbounded l\<close>
proof
  show "\<forall>\<^sub>F x in sequentially. dist (bounded_of_rbounded (f x)) (bounded_of_rbounded l) < e"
    if "(0::real) < e"
    for e :: real
  proof-
    from \<open>f \<longlonglongrightarrow> l\<close>
    have \<open>\<forall>\<^sub>F x in sequentially. dist (f x) l < e\<close>
      by (simp add: tendstoD that)
    moreover have \<open>rbounded_of_bounded (bounded_of_rbounded (f n)) = f n\<close>
      for n
      by (simp add: assms(2) rbounded_bounded)
    moreover have \<open>rbounded_of_bounded (bounded_of_rbounded l) = l\<close>
    proof-
      have \<open>\<forall> c. \<forall> x. Rep_rbounded l (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded l x)\<close>
        using assms(1) assms(2) bounded_of_rbounded_complex_lim by blast        
      thus ?thesis
        by (simp add: rbounded_bounded) 
    qed
    ultimately show ?thesis 
      unfolding dist_bounded_def
      by simp  
  qed    
qed

instance 
proof
  show "convergent f"
    if "Cauchy f"
    for f :: "nat \<Rightarrow> ('a, 'b) bounded"
  proof-
    have \<open>Cauchy (\<lambda> n. rbounded_of_bounded (f n))\<close>
      by (simp add: rbounded_of_bounded_Cauchy that)
    hence \<open>convergent (\<lambda> n. rbounded_of_bounded (f n))\<close>
      by (simp add: Cauchy_convergent_iff)
    hence \<open>\<exists> l. (\<lambda> n. rbounded_of_bounded (f n)) \<longlonglongrightarrow> rbounded_of_bounded l\<close>
      by (metis (no_types, lifting) Bounded_Operators.bounded_of_rbounded_complex_lim convergent_LIMSEQ_iff rbounded_bounded rbounded_of_bounded_prelim)
    then obtain l where \<open>(\<lambda> n. rbounded_of_bounded (f n)) \<longlonglongrightarrow> rbounded_of_bounded l\<close>
      by blast
    hence \<open>(\<lambda> n. bounded_of_rbounded (rbounded_of_bounded (f n))) \<longlonglongrightarrow> bounded_of_rbounded (rbounded_of_bounded l)\<close>
      by (simp add: Bounded_Operators.bounded_of_rbounded_lim rbounded_of_bounded_prelim)
    hence \<open>f \<longlonglongrightarrow> l\<close>
      by (simp add: bounded_rbounded)
    thus ?thesis
      using convergent_def by blast 
  qed
qed
end

lemma zero_bounded_lift:
  \<open>Rep_bounded (0::('a, 'b) bounded) = (\<lambda> _::('a::complex_normed_vector). 0::('b::complex_normed_vector))\<close>
  by (metis rbounded_of_bounded.rep_eq rbounded_of_bounded_zero zero_rbounded.rep_eq)

lemma uminus_bounded_lift:
  \<open>Rep_bounded (- f) = (\<lambda> x. - (Rep_bounded f) x)\<close>
  by (metis (no_types, hide_lams) rbounded_of_bounded.rep_eq rbounded_of_bounded_uminus scaleC_minus1_left scaleC_rbounded.rep_eq)

lemma plus_bounded_lift:
  \<open>Rep_bounded (f + g) = (\<lambda> x. (Rep_bounded f) x + (Rep_bounded g) x)\<close>
  unfolding plus_bounded_def
  by (metis (no_types, hide_lams) plus_bounded_def plus_rbounded.rep_eq rbounded_of_bounded.rep_eq rbounded_of_bounded_plus) 

lemma minus_bounded_lift:
  \<open>Rep_bounded (f - g) = (\<lambda> x. (Rep_bounded f) x - (Rep_bounded g) x)\<close>
  unfolding minus_bounded_def
  by (metis (no_types, hide_lams) minus_bounded_def minus_rbounded.rep_eq rbounded_of_bounded.rep_eq rbounded_of_bounded_minus)

lemma scaleC_bounded_lift:
  \<open>Rep_bounded (c *\<^sub>C f) = (\<lambda> x. c *\<^sub>C (Rep_bounded f) x)\<close>
  unfolding scaleC_bounded_def
  by (metis rbounded_of_bounded.rep_eq rbounded_of_bounded_scaleC scaleC_bounded_def scaleC_rbounded.rep_eq)

lemma scaleR_bounded_lift:
  \<open>Rep_bounded (c *\<^sub>R f) = (\<lambda> x. c *\<^sub>R (Rep_bounded f) x)\<close>
  unfolding scaleR_bounded_def
  by (metis rbounded_of_bounded.rep_eq rbounded_of_bounded_scaleR scaleR_bounded_def scaleR_rbounded.rep_eq)

lift_definition
  adjoint :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> ('b,'a) bounded" ("_*" [99] 100) 
  is Adj by (fact Adj_bounded_clinear)

lemma adjoint_I:
  fixes G :: "('b::chilbert_space, 'a::chilbert_space) bounded"
  shows \<open>\<forall>x. \<forall>y. \<langle>Rep_bounded (adjoint G) x, y\<rangle> = \<langle>x, (Rep_bounded G) y\<rangle>\<close>
  apply transfer using Adj_I by blast

lemma adjoint_D:
  fixes G:: \<open>('b::chilbert_space, 'a::chilbert_space) bounded\<close>
    and F:: \<open>('a, 'b) bounded\<close>
  assumes \<open>\<And>x y. \<langle>(Rep_bounded F) x, y\<rangle> = \<langle>x, (Rep_bounded G) y\<rangle>\<close>
  shows \<open>F = G*\<close>
  using assms apply transfer using Adj_D by auto

lemma adjoint_twice[simp]: "(U*)* = U" 
  for U :: "('a::chilbert_space,'b::chilbert_space) bounded"
  apply transfer
  using dagger_dagger_id by blast

lift_definition idOp::\<open>('a::complex_normed_vector,'a) bounded\<close> is id
  using id_bounded_clinear by blast

lemma idOp_adjoint[simp]: "idOp* = idOp"
  apply transfer using id_dagger by blast

lemma scalar_times_adj[simp]: "(a *\<^sub>C A)* = (cnj a) *\<^sub>C (A*)" 
  for A::"('a::chilbert_space,'b::chilbert_space) bounded"
    and a :: complex 
proof-
  have \<open>bounded_clinear ((Rep_bounded A))\<close>
    using Rep_bounded by blast
  hence \<open>(\<lambda> t. a *\<^sub>C ((Rep_bounded A) t))\<^sup>\<dagger> = (\<lambda> s. (cnj a) *\<^sub>C (((Rep_bounded A)\<^sup>\<dagger>) s))\<close>
    using scalar_times_adjc_flatten
    unfolding bounded_clinear_def clinear_def clinear_axioms_def Modules.additive_def
    by (simp add: scalar_times_adjc_flatten \<open>bounded_clinear (Rep_bounded A)\<close> bounded_clinear.bounded_linear)
  moreover have \<open>Rep_bounded ((a *\<^sub>C A)*) = (\<lambda> t. a *\<^sub>C ((Rep_bounded A) t))\<^sup>\<dagger>\<close>
    unfolding Adj_def
    apply auto
    by (smt Adj_def Eps_cong adjoint.rep_eq cinner_scaleC_right scaleC_bounded_lift)
  moreover have \<open>Rep_bounded (cnj a *\<^sub>C (A*)) = (\<lambda> s. (cnj a) *\<^sub>C (((Rep_bounded A)\<^sup>\<dagger>) s))\<close>
    unfolding Adj_def
    by (simp add: Adj_def adjoint.rep_eq scaleC_bounded_lift)
  ultimately show ?thesis
    using Rep_bounded_inject
    by fastforce 
qed
  

chapter \<open>Chaos\<close>


section \<open>Composition\<close>

lift_definition rtimesOp:: 
  "('b::real_normed_vector,'c::real_normed_vector) rbounded
     \<Rightarrow> ('a::real_normed_vector,'b) rbounded \<Rightarrow> ('a,'c) rbounded"
  is "(o)"
  unfolding o_def 
  by (rule bounded_linear_compose, simp_all)

lift_definition ctimesOp:: 
  "('b::complex_normed_vector,'c::complex_normed_vector) cbounded
     \<Rightarrow> ('a::complex_normed_vector,'b) cbounded \<Rightarrow> ('a,'c) cbounded"
  is "rtimesOp"
  by transfer auto

definition timesOp:: 
  "('b::complex_normed_vector,'c::complex_normed_vector) bounded
     \<Rightarrow> ('a::complex_normed_vector,'b) bounded \<Rightarrow> ('a,'c) bounded" where
  \<open>timesOp f g = flatten (ctimesOp (unflatten f) (unflatten g))\<close>

(* This lemma plays the role of lift_definition *)
lemma timesOp_Rep_bounded:
  \<open>Rep_bounded (timesOp f g) = (Rep_bounded f)\<circ>(Rep_bounded g)\<close>
  unfolding timesOp_def ctimesOp_def rtimesOp_def unflatten_def flatten_def
  apply auto
  by (metis (no_types, lifting) Rep_cbounded_inverse ctimesOp.rep_eq flatten.abs_eq flatten.rep_eq rtimesOp.rep_eq unflatten.rep_eq unflatten_inv) 

lemma rtimesOp_assoc: "rtimesOp (rtimesOp A B) C = rtimesOp A (rtimesOp B C)" 
  apply transfer
  by (simp add: comp_assoc) 

lemma ctimesOp_assoc: "ctimesOp (ctimesOp A B) C = ctimesOp A (ctimesOp B C)" 
  apply transfer
  using rtimesOp_assoc by smt

lift_definition timesOpX:: 
  "('b::complex_normed_vector,'c::complex_normed_vector) bounded
     \<Rightarrow> ('a::complex_normed_vector,'b) bounded \<Rightarrow> ('a,'c) bounded"
  is "(o)"
  unfolding o_def 
  by (rule bounded_clinear_compose, simp_all)

lemma rtimesOp_assoc_plain: "bounded_linear Aa \<Longrightarrow>
  bounded_linear Ba \<Longrightarrow> bounded_linear Ca \<Longrightarrow> Aa \<circ> Ba \<circ> Ca = Aa \<circ> (Ba \<circ> Ca)"
  sorry (* from rtimesOp_assoc by automation *)

lemma tmp: "timesOpX (timesOpX A B) C = timesOpX A (timesOpX B C)"
  apply transfer
    (* using rtimesOp_assoc_plain *)
  by auto


lemma timesOp_assoc: "timesOp (timesOp A B) C = timesOp A (timesOp B C)" 
  unfolding timesOp_def using ctimesOp_assoc
  by (simp add: ctimesOp_assoc flatten_inv) 

lemma times_adjoint[simp]: "adjoint (timesOp A B) = timesOp (adjoint B) (adjoint A)"
  using timesOp_Rep_bounded 
  by (smt adjoint_D adjoint_I comp_apply)

lemma ctimes_adjoint[simp]: "cadjoint (ctimesOp A B) = ctimesOp (cadjoint B) (cadjoint A)"
  unfolding cadjoint_def using times_adjoint
  by (metis flatten_inv timesOp_def) 

section \<open>Image of a subspace by an operator\<close>

lift_definition applyOpSpace::\<open>('a::chilbert_space,'b::chilbert_space) bounded
\<Rightarrow> 'a linear_space \<Rightarrow> 'b linear_space\<close> 
  is "\<lambda>A S. closure (A ` S)"
  using  bounded_clinear_def is_subspace.subspace
  by (metis closed_closure is_linear_manifold_image is_subspace.intro is_subspace_cl) 

instantiation linear_space :: (complex_normed_vector) scaleC begin
lift_definition scaleC_linear_space :: "complex \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is
  "\<lambda>c S. scaleC c ` S"
  apply (rule is_subspace.intro)
  using bounded_clinear_def bounded_clinear_scaleC_right is_linear_manifold_image is_subspace.subspace apply blast
  by (simp add: closed_scaleC is_subspace.closed)
lift_definition scaleR_linear_space :: "real \<Rightarrow> 'a linear_space \<Rightarrow> 'a linear_space" is
  "\<lambda>c S. scaleR c ` S"
  apply (rule is_subspace.intro)
  apply (metis bounded_clinear_def bounded_clinear_scaleC_right is_linear_manifold_image is_subspace.subspace scaleR_scaleC)
  by (simp add: closed_scaling is_subspace.closed)
instance 
  apply standard
  by (simp add: scaleR_scaleC scaleC_linear_space_def scaleR_linear_space_def)
end

instantiation linear_space :: (complex_normed_vector) zero begin
lift_definition zero_linear_space :: \<open>'a linear_space\<close> is \<open>0\<close>
  by simp
instance..
end

lemma applyOp_0[simp]: "applyOpSpace U 0 = 0" 
  apply transfer
  by (simp add: additive.zero bounded_clinear_def clinear.axioms(1))

lemma times_comp: \<open>\<And>A B \<psi>.
       bounded_clinear A \<Longrightarrow>
       bounded_clinear B \<Longrightarrow>
       is_subspace \<psi> \<Longrightarrow>
       closure ( (A \<circ> B) ` \<psi>) = closure (A ` closure (B ` \<psi>))\<close>
proof
  show "closure ((A \<circ> B) ` (\<psi>::'c set)::'b set) \<subseteq> closure (A ` closure (B ` \<psi>::'a set))"
    if "bounded_clinear (A::'a \<Rightarrow> 'b)"
      and "bounded_clinear (B::'c \<Rightarrow> 'a)"
      and "is_subspace (\<psi>::'c set)"
    for A :: "'a \<Rightarrow> 'b"
      and B :: "'c \<Rightarrow> 'a"
      and \<psi> :: "'c set"
    using that
    by (metis closure_mono closure_subset image_comp image_mono) 
  show "closure (A ` closure (B ` (\<psi>::'c set)::'a set)) \<subseteq> closure ((A \<circ> B) ` \<psi>::'b set)"
    if "bounded_clinear (A::'a \<Rightarrow> 'b)"
      and "bounded_clinear (B::'c \<Rightarrow> 'a)"
      and "is_subspace (\<psi>::'c set)"
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
              using \<open>bounded_clinear A\<close>
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
  \<open>applyOpSpace (timesOp A B) \<psi> = applyOpSpace A (applyOpSpace B \<psi>)\<close>
proof-
  have \<open>bounded_clinear (Rep_bounded A)\<close>
    using Rep_bounded by auto
  moreover have \<open>bounded_clinear (Rep_bounded B)\<close>
    using Rep_bounded by auto
  moreover have \<open>is_subspace (Rep_linear_space \<psi>)\<close>
    using Rep_linear_space by auto
  ultimately have  \<open>
     (closure
       ( (Rep_bounded A \<circ> Rep_bounded B) ` Rep_linear_space \<psi>)) =
     (closure
       (Rep_bounded A `
      closure (Rep_bounded B ` Rep_linear_space \<psi>)))\<close>
    using times_comp by blast
  hence  \<open>
     (closure
       ( (Rep_bounded A \<circ> Rep_bounded B) ` Rep_linear_space \<psi>)) =
     (closure
       (Rep_bounded A `
        Rep_linear_space
         (Abs_linear_space
           (closure (Rep_bounded B ` Rep_linear_space \<psi>)))))\<close>
    by (metis Rep_linear_space_inverse applyOpSpace.rep_eq)    
  hence  \<open>
     (closure
       (Rep_bounded (timesOp A B) ` Rep_linear_space \<psi>)) =
     (closure
       (Rep_bounded A `
        Rep_linear_space
         (Abs_linear_space
           (closure (Rep_bounded B ` Rep_linear_space \<psi>)))))\<close>
    using timesOp_Rep_bounded by metis
  hence \<open> Abs_linear_space
     (closure
       (Rep_bounded (timesOp A B) ` Rep_linear_space \<psi>)) =
    Abs_linear_space
     (closure
       (Rep_bounded A `
        Rep_linear_space
         (Abs_linear_space
           (closure (Rep_bounded B ` Rep_linear_space \<psi>)))))\<close>
    using Abs_linear_space_inject by auto
  thus ?thesis
    unfolding applyOpSpace_def
    by auto
qed

lemma timesScalarSpace_0[simp]: "0 *\<^sub>C S = 0" for S :: "_ linear_space"
  apply transfer apply (auto intro!: exI[of _ 0])
  using  is_linear_manifold.zero is_subspace.subspace  by auto

lemma subspace_scale_invariant: 
  fixes a S
  assumes \<open>a \<noteq> 0\<close> and \<open>is_subspace S\<close>
  shows \<open>(*\<^sub>C) a ` S = S\<close>
proof-
  have  \<open>x \<in> (*\<^sub>C) a ` S \<Longrightarrow> x \<in> S\<close>
    for x
    using assms(2) is_linear_manifold.smult_closed is_subspace.subspace by fastforce
  moreover have  \<open>x \<in> S \<Longrightarrow> x \<in> (*\<^sub>C) a ` S\<close>
    for x
  proof - (* automatically generated *)
    assume "x \<in> S"
    then have "\<exists>c aa. (c / a) *\<^sub>C aa \<in> S \<and> c *\<^sub>C aa = x"
      using assms(2) is_linear_manifold_def is_subspace.subspace scaleC_one by blast
    then have "\<exists>aa. aa \<in> S \<and> a *\<^sub>C aa = x"
      using assms(1) by auto
    then show ?thesis
      by (meson image_iff)
  qed 
  ultimately show ?thesis by blast
qed

lemma timesScalarSpace_not0[simp]: "a \<noteq> 0 \<Longrightarrow> a *\<^sub>C S = S" for S :: "_ linear_space"
  apply transfer using subspace_scale_invariant by blast

lemmas assoc_left = timesOp_assoc[symmetric] timesOp_assoc_linear_space[symmetric] add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded", symmetric]
lemmas assoc_right = timesOp_assoc timesOp_assoc_linear_space add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded"]

lemma scalar_times_op_add[simp]: "scaleC a (A+B) = scaleC a A + scaleC a B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  by (simp add: scaleC_add_right)

lemma scalar_times_op_minus[simp]: "scaleC a (A-B) = scaleC a A - scaleC a B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  by (simp add: complex_vector.scale_right_diff_distrib)

instantiation linear_space :: (cbanach) "bot"
begin
lift_definition bot_linear_space :: \<open>'a linear_space\<close> is \<open>{0}\<close>
  by (rule Complex_Inner_Product.is_subspace_0)
instance ..
end

instantiation linear_space :: (cbanach) "top"
begin
lift_definition top_linear_space :: \<open>'a linear_space\<close> is \<open>UNIV\<close>
  by (rule Complex_Inner_Product.is_subspace_UNIV)
instance ..
end

lemma applyOp_bot[simp]: "applyOpSpace U bot = bot"
  for U::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> 
proof-
  have \<open>closed {0::'a}\<close>
    using Topological_Spaces.t1_space_class.closed_singleton by blast
  hence \<open>closure {0::'a} = {0}\<close>
    by (simp add: closure_eq)    
  moreover have \<open>Rep_bounded U ` {0::'a} = {0}\<close>
  proof-
    have \<open>bounded_clinear (Rep_bounded U)\<close>
      using Rep_bounded by auto
    hence  \<open>Rep_bounded U 0 = 0\<close>
      by (simp add: bounded_clinear.clinear clinear_zero)
    thus ?thesis
      by simp 
  qed
  ultimately have \<open>closure (Rep_bounded U ` {0}) = {0}\<close>
    by simp
  hence \<open>(closure (Rep_bounded U ` Rep_linear_space (Abs_linear_space {0}))) = {0}\<close>
    by (metis bot_linear_space.abs_eq bot_linear_space.rep_eq) 
  thus ?thesis
    unfolding applyOpSpace_def bot_linear_space_def by simp
qed

section \<open>Complex Span\<close>

(* TODO Complex_Vector_Spaces *)
lift_definition span :: "'a::cbanach set \<Rightarrow> 'a linear_space"
  is "\<lambda>G. closure (complex_vector.span G)"
  apply (rule is_subspace.intro)
  apply (rule is_subspace_cl)
  by (simp_all add: complex_vector.span_add complex_vector.span_scale complex_vector.span_zero is_linear_manifold.intro)

instantiation linear_space :: (cbanach) "Inf"
begin
lift_definition Inf_linear_space::\<open>'a linear_space set \<Rightarrow> 'a linear_space\<close>
  is \<open>\<lambda> S. \<Inter> S\<close>
proof
  show "(x::'a) + y \<in> \<Inter> set"
    if "\<And>x. (x::'a set) \<in> set \<Longrightarrow> is_subspace x"
      and "(x::'a) \<in> \<Inter> set"
      and "(y::'a) \<in> \<Inter> set"
    for set :: "'a set set"
      and x :: 'a
      and y :: 'a
    using that
    by (simp add: is_linear_manifold.additive_closed is_subspace.subspace) 
  show "c *\<^sub>C (x::'a) \<in> \<Inter> set"
    if "\<And>x. (x::'a set) \<in> set \<Longrightarrow> is_subspace x"
      and "(x::'a) \<in> \<Inter> set"
    for set :: "'a set set"
      and x :: 'a
      and c :: complex
    using that
    by (simp add: is_linear_manifold.smult_closed is_subspace.subspace) 
  show "(0::'a) \<in> \<Inter> set"
    if "\<And>x. (x::'a set) \<in> set \<Longrightarrow> is_subspace x"
    for set :: "'a set set"
    using that
    by (simp add: is_linear_manifold.zero is_subspace.subspace) 
  show "closed (\<Inter> set::'a set)"
    if "\<And>x. (x::'a set) \<in> set \<Longrightarrow> is_subspace x"
    for set :: "'a set set"
    using that
    by (simp add: is_subspace.closed) 
qed

instance ..
end

instantiation linear_space :: (cbanach) "order"
begin
lift_definition less_eq_linear_space :: \<open>'a linear_space \<Rightarrow> 'a linear_space \<Rightarrow> bool\<close>
  is \<open>(\<subseteq>)\<close>.
lift_definition less_linear_space :: \<open>'a linear_space \<Rightarrow> 'a linear_space \<Rightarrow> bool\<close>
  is \<open>(\<subset>)\<close>.
instance
proof
  show "((x::'a linear_space) < y) = (x \<le> y \<and> \<not> y \<le> x)"
    for x :: "'a linear_space"
      and y :: "'a linear_space"
    by (simp add: less_eq_linear_space.rep_eq less_le_not_le less_linear_space.rep_eq)    
  show "(x::'a linear_space) \<le> x"
    for x :: "'a linear_space"
    by (simp add: Bounded_Operators.less_eq_linear_space.rep_eq)    
  show "(x::'a linear_space) \<le> z"
    if "(x::'a linear_space) \<le> y"
      and "(y::'a linear_space) \<le> z"
    for x :: "'a linear_space"
      and y :: "'a linear_space"
      and z :: "'a linear_space"
    using that
    using less_eq_linear_space.rep_eq by auto 
  show "(x::'a linear_space) = y"
    if "(x::'a linear_space) \<le> y"
      and "(y::'a linear_space) \<le> x"
    for x :: "'a linear_space"
      and y :: "'a linear_space"
    using that
    by (simp add: Rep_linear_space_inject less_eq_linear_space.rep_eq) 
qed
end

lemma is_subspace_span_A:
  assumes \<open>is_subspace S\<close> and \<open>A \<subseteq> S\<close>
  shows \<open>complex_vector.span A \<subseteq> S\<close>
  using assms
  unfolding complex_vector.span_def complex_vector.subspace_def
    hull_def is_subspace_def is_linear_manifold_def
  by auto

lemma is_subspace_span_B:
  assumes \<open>is_subspace S\<close> and \<open>complex_vector.span A \<subseteq> S\<close>
  shows \<open>A \<subseteq> S\<close>
  using assms(2) complex_vector.span_superset by blast

lemma span_def': \<open>span A = Inf {S. A \<subseteq> Rep_linear_space S}\<close>
  for A::\<open>('a::cbanach) set\<close>
proof-
  have \<open>x \<in> Rep_linear_space (span A) 
    \<Longrightarrow> x \<in> Rep_linear_space (Inf {S. A \<subseteq> Rep_linear_space S})\<close>
    for x::'a
  proof-
    assume \<open>x \<in> Rep_linear_space (span A)\<close>
    hence \<open>x \<in> closure (complex_vector.span A)\<close>
      unfolding span_def
      apply auto
      using Abs_linear_space_inverse \<open>x \<in> Rep_linear_space (Bounded_Operators.span A)\<close> span.rep_eq 
      by blast
    hence \<open>\<exists> y::nat \<Rightarrow> 'a. (\<forall> n. y n \<in> (complex_vector.span A)) \<and> y \<longlonglongrightarrow> x\<close>
      by (simp add: closure_sequential)
    then obtain y where \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close> and \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>y n \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> is_subspace S}\<close>
      for n
      using  \<open>\<forall> n. y n \<in> (complex_vector.span A)\<close>
      by auto
    have \<open>x \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> is_subspace S}\<close> 
    proof-
      have \<open>is_subspace S \<Longrightarrow> closed S\<close>
        for S::\<open>'a set\<close>
        by (simp add: is_subspace.closed)
      hence \<open>closed ( \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> is_subspace S})\<close>
        by simp
      thus ?thesis using \<open>y \<longlonglongrightarrow> x\<close>
        using \<open>\<And>n. y n \<in> \<Inter> {S. complex_vector.span A \<subseteq> S \<and> is_subspace S}\<close> closed_sequentially 
        by blast  
    qed
    moreover have \<open>{S. A \<subseteq> S \<and> is_subspace S} \<subseteq> {S. (complex_vector.span A) \<subseteq> S \<and> is_subspace S}\<close>
      by (simp add: Collect_mono_iff is_subspace_span_A)    
    ultimately have \<open>x \<in> \<Inter> {S. A \<subseteq> S \<and> is_subspace S}\<close>
      by blast     
    thus \<open>x \<in> Rep_linear_space (Inf {S. A \<subseteq> Rep_linear_space S})\<close> 
      apply transfer
      by blast
  qed
  moreover have \<open>x \<in> Rep_linear_space (Inf {S. A \<subseteq> Rep_linear_space S})
             \<Longrightarrow> x \<in> Rep_linear_space (span A)\<close>
    for x::'a
  proof-
    assume \<open>x \<in> Rep_linear_space (Inf {S. A \<subseteq> Rep_linear_space S})\<close>
    hence \<open>x \<in> \<Inter> {S. A \<subseteq> S \<and> is_subspace S}\<close>
      apply transfer
      by blast
    moreover have \<open>{S. (complex_vector.span A) \<subseteq> S \<and> is_subspace S} \<subseteq> {S. A \<subseteq> S \<and> is_subspace S}\<close>
      by (simp add: Collect_mono_iff is_subspace_span_B)    
    ultimately have \<open>x \<in> \<Inter> {S. (complex_vector.span A) \<subseteq> S \<and> is_subspace S}\<close>
      by blast 
    thus \<open>x \<in> Rep_linear_space (span A)\<close>
      by (metis (no_types, lifting) Inter_iff Rep_linear_space closure_subset mem_Collect_eq span.rep_eq)      
  qed
  ultimately have \<open>Rep_linear_space (span A) = Rep_linear_space (Inf {S. A \<subseteq> Rep_linear_space S})\<close>
    by blast
  thus ?thesis
    using Rep_linear_space_inject by auto 
qed

lemma span_mult[simp]: "(a::complex)\<noteq>0 \<Longrightarrow> span { a *\<^sub>C \<psi> } = span {\<psi>}"
  for \<psi>::"'a::chilbert_space"
proof-
  assume \<open>a \<noteq> 0\<close>
  have \<open>span {\<psi>} = Inf {S | S::'a linear_space. {\<psi>} \<subseteq> Rep_linear_space S }\<close>
    by (metis span_def')
  also have \<open>... = Inf {S | S::'a linear_space. \<psi> \<in> Rep_linear_space S }\<close>
    by simp
  also have \<open>... = Inf {S | S::'a linear_space. a *\<^sub>C \<psi> \<in> Rep_linear_space S }\<close>
  proof-
    have \<open>\<psi> \<in> Rep_linear_space S \<longleftrightarrow>  a *\<^sub>C \<psi> \<in> Rep_linear_space S\<close> for S
    proof-
      have \<open>is_subspace (Rep_linear_space S)  \<close>
        using Rep_linear_space by auto
      hence \<open>\<psi> \<in> Rep_linear_space S \<Longrightarrow>  a *\<^sub>C \<psi> \<in> Rep_linear_space S\<close> for S
        by (metis Abs_linear_space_cases Abs_linear_space_inverse is_linear_manifold.smult_closed is_subspace.subspace mem_Collect_eq)
      moreover have  \<open>a *\<^sub>C \<psi> \<in> Rep_linear_space S \<Longrightarrow> \<psi> \<in> Rep_linear_space S\<close> for S
      proof-
        assume \<open>a *\<^sub>C \<psi> \<in> Rep_linear_space S\<close>
        obtain b where \<open>b * a = 1\<close> using \<open>a \<noteq> 0\<close> 
          by (metis divide_complex_def divide_self_if mult.commute)
        have \<open>b *\<^sub>C (a *\<^sub>C \<psi>) \<in> Rep_linear_space S\<close> 
          using  \<open>a *\<^sub>C \<psi> \<in> Rep_linear_space S\<close> is_linear_manifold.smult_closed
            is_subspace.subspace Rep_linear_space
          by fastforce
        hence  \<open>(b *\<^sub>C a) *\<^sub>C \<psi> \<in> Rep_linear_space S\<close> 
          by simp
        thus ?thesis using  \<open>b * a = 1\<close> by simp
      qed                       
      ultimately show ?thesis by blast
    qed
    thus ?thesis by simp
  qed
  also have \<open>... = Inf {S | S::'a linear_space. {a *\<^sub>C \<psi>} \<subseteq> Rep_linear_space S }\<close>
    by auto
  also have \<open>... = span {a *\<^sub>C \<psi>}\<close> 
    by (metis span_def')
  finally have  \<open>span {\<psi>} = span {a *\<^sub>C \<psi>}\<close>
    by blast
  thus ?thesis by auto
qed

(* NEW *)
definition cgenerator :: \<open>'a::cbanach set \<Rightarrow> bool\<close> where
  \<open>cgenerator S = (span S = top)\<close>

fun partial_span::\<open>nat \<Rightarrow> ('a::complex_vector) set \<Rightarrow> ('a::complex_vector) set\<close> where
  \<open>partial_span 0 S = {0}\<close>|
  \<open>partial_span (Suc n) S = {x + a *\<^sub>C y | a x y. x \<in> partial_span n S \<and> y \<in> S}\<close>

definition finite_dimensional::\<open>('a::{complex_vector,topological_space}) linear_space \<Rightarrow> bool\<close> where
  \<open>finite_dimensional S = (\<exists> n. Rep_linear_space S = partial_span n (Rep_linear_space S))\<close>

definition dim::\<open>('a::{complex_vector,topological_space}) linear_space \<Rightarrow> nat\<close> where
  \<open>dim S = Inf {n | n. Rep_linear_space S = partial_span n (Rep_linear_space S)}\<close>

term \<open>dim S = (if S=0 then 0 else 1)\<close>

lemma partial_span_1:
  \<open>S \<subseteq> partial_span 1 S\<close>
proof-
  have \<open>partial_span 0 S = {0}\<close>
    by auto
  moreover have \<open>partial_span (Suc 0) S = {x + a *\<^sub>C y | a x y. x \<in> partial_span 0 S \<and> y \<in> S}\<close>
    by auto
  ultimately have \<open>partial_span (Suc 0) S = {a *\<^sub>C y | a y. y \<in> S}\<close>
    by auto 
  also have \<open>{a *\<^sub>C y | a y. y \<in> S} \<supseteq> {1 *\<^sub>C y | y. y \<in> S}\<close>
    by blast
  also have \<open>{1 *\<^sub>C y | y. y \<in> S} = S\<close>
    by simp
  finally have \<open>partial_span (Suc 0) S \<supseteq> S\<close>
    by blast
  thus ?thesis
    by simp 
qed

lemma partial_span_lim_n:
  fixes S::\<open>'a::complex_vector set\<close>
  shows \<open>partial_span n S \<subseteq> complex_vector.span S\<close>
proof(induction n)
  case 0
  thus ?case
    using complex_vector.span_mono by force 
next
  case (Suc n)
  have \<open>x \<in> partial_span (Suc n) S \<Longrightarrow> x \<in> complex_vector.span S\<close>
    for x
  proof-
    assume \<open>x \<in> partial_span (Suc n) S\<close>
    hence \<open>x \<in> {t + a *\<^sub>C y | a t y. t \<in> partial_span n S \<and> y \<in> S}\<close>
      by simp
    then obtain a t y where \<open>x = t + a *\<^sub>C y\<close> and \<open>t \<in> partial_span n S\<close>
      and \<open>y \<in> S\<close>
      by blast
    have \<open>t \<in> complex_vector.span S\<close>
      using Suc.IH \<open>t \<in> partial_span n S\<close> by auto
    moreover have \<open>a *\<^sub>C y \<in> complex_vector.span S\<close>
    proof-
      have \<open>y \<in> complex_vector.span S\<close>
        using \<open>y \<in> S\<close>
        by (simp add: complex_vector.span_base) 
      thus ?thesis
        by (simp add: complex_vector.span_scale) 
    qed
    ultimately show ?thesis
      by (simp add: \<open>x = t + a *\<^sub>C y\<close> complex_vector.span_add) 
  qed
  thus ?case
    by blast 
qed

lemma sum_partial_span_eq:
  fixes S::\<open>'a::complex_vector set\<close>
  assumes  \<open>S \<noteq> {}\<close>
  shows \<open>\<forall> r s. \<exists> p::nat. r \<in> partial_span n S \<longrightarrow> s \<in> partial_span n S
 \<longrightarrow> r + s \<in> partial_span (n+p) S\<close>
proof(induction n)
  case 0
  have  \<open>r \<in> partial_span 0 S \<Longrightarrow> s \<in> partial_span 0 S \<Longrightarrow> r + s \<in> partial_span (Suc 0) S\<close>
    for r s
  proof-
    assume \<open>r \<in> partial_span 0 S\<close> and \<open>s \<in> partial_span 0 S\<close>
    from  \<open>r \<in> partial_span 0 S\<close>
    have \<open>r = 0\<close>
      by simp
    from  \<open>s \<in> partial_span 0 S\<close>
    have \<open>s = 0\<close>
      by simp
    have \<open>r + s = 0\<close>
      by (simp add: \<open>r = 0\<close> \<open>s = 0\<close>)
    have \<open>partial_span (Suc 0) S = {x + a *\<^sub>C y | a x y. x \<in> partial_span 0 S \<and> y \<in> S}\<close>
      by simp
    have \<open>\<exists> w. w \<in> S\<close>
      using \<open>S \<noteq> {}\<close>
      by blast
    then obtain w where \<open>w \<in> S\<close>
      by blast
    have \<open>r + 0 *\<^sub>C w \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span 0 S \<and> y \<in> S}\<close>
      using \<open>r \<in>  partial_span 0 S\<close> \<open>w \<in> S\<close> by blast
    hence \<open>0 \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span 0 S \<and> y \<in> S}\<close>
      by (simp add: \<open>r = 0\<close>)
    thus ?thesis using \<open>r + s = 0\<close> by simp
  qed
  thus ?case
    by (metis add.left_neutral) 
next
  case (Suc n)
  have \<open>r \<in> partial_span (Suc n) S \<Longrightarrow> s \<in> partial_span (Suc n) S \<Longrightarrow> \<exists> p. r + s \<in> partial_span (Suc n + p) S\<close>
    for r s
  proof-
    assume \<open>r \<in> partial_span (Suc n) S\<close> and \<open>s \<in> partial_span (Suc n) S\<close>
    from \<open>r \<in> partial_span (Suc n) S\<close>
    have \<open>r \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span n S \<and> y \<in> S}\<close>
      by auto
    then obtain a u uu where \<open>r = u + a *\<^sub>C uu\<close> and \<open>u \<in>  partial_span n S\<close> and \<open>uu \<in> S\<close>
      by blast
    from \<open>s \<in> partial_span (Suc n) S\<close>
    have \<open>s \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span n S \<and> y \<in> S}\<close>
      by auto
    then obtain b v vv where \<open>s = v + b *\<^sub>C vv\<close> and \<open>v \<in>  partial_span n S\<close> and \<open>vv \<in> S\<close>
      by blast
    have \<open>r + s = (u + v) + a *\<^sub>C uu +  b *\<^sub>C vv\<close>
      by (simp add: \<open>r = u + a *\<^sub>C uu\<close> \<open>s = v + b *\<^sub>C vv\<close>)
    have \<open>\<exists> p. u + v \<in>  partial_span (n+p) S\<close>
      using Suc.IH  \<open>u \<in>  partial_span n S\<close> \<open>v \<in>  partial_span n S\<close>
      by auto
    then obtain p where  \<open> u + v \<in>  partial_span (n+p) S\<close>
      by blast
    hence \<open>(u + v) + a *\<^sub>C uu \<in> partial_span (Suc (n + p)) S\<close>
      using \<open>uu \<in> S\<close>
      by auto 
    hence \<open>((u + v) + a *\<^sub>C uu) + b *\<^sub>C vv \<in> partial_span (Suc (Suc (n + p))) S\<close>
      using \<open>vv \<in> S\<close> by force
    thus ?thesis
      by (metis \<open>r + s = u + v + a *\<^sub>C uu + b *\<^sub>C vv\<close> add_Suc add_Suc_right) 
  qed
  thus ?case by blast 
qed

lemma sum_partial_span_leq_ind:
  fixes S::\<open>'a::complex_vector set\<close> and n p :: nat
  assumes \<open>r \<in> partial_span n S\<close> and \<open>S \<noteq> {}\<close>
  shows \<open>r \<in> partial_span (n + p) S\<close>
proof(induction p)
  case 0
  thus ?case
    by (simp add: assms) 
next
  case (Suc p)
  have \<open>\<exists> s. s \<in> S\<close>
    using \<open>S \<noteq> {}\<close>
    by blast
  then obtain s where \<open>s \<in> S\<close>
    by blast
  have  \<open>r \<in> partial_span (n + p) S\<close>
    by (simp add: Suc.IH)
  hence  \<open>r + 0 *\<^sub>C s \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span (n + p) S \<and> y \<in> S}\<close>
    using  \<open>s \<in> S\<close>
    by blast
  hence  \<open>r + 0 *\<^sub>C s \<in> partial_span (Suc (n + p)) S\<close>
    by simp
  moreover have \<open>r = r + 0 *\<^sub>C s\<close>
    by simp
  ultimately show ?case by simp
qed

lemma sum_partial_span_leq:
  fixes S::\<open>'a::complex_vector set\<close>
  assumes \<open>r \<in> partial_span n S\<close> and \<open>n \<le> m\<close> and \<open>S \<noteq> {}\<close>
  shows \<open>r \<in> partial_span m S\<close>
  using sum_partial_span_leq_ind assms le_Suc_ex by blast 

lemma sum_partial_span:
  fixes S::\<open>'a::complex_vector set\<close>
  assumes \<open>r \<in> partial_span n S\<close> and \<open>s \<in> partial_span m S\<close> and \<open>S \<noteq> {}\<close>
  shows \<open>\<exists> p. r + s \<in> partial_span p S\<close>
  using assms sum_partial_span_eq sum_partial_span_leq
  by (metis max.cobounded1 max.cobounded2)

lemma scaleC_partial_span:
  fixes S::\<open>'a::complex_vector set\<close>
  shows \<open>\<forall> t. t \<in> partial_span n S \<longrightarrow> c *\<^sub>C t \<in> partial_span n S\<close>
proof(induction n)
  case 0
  thus ?case
    by simp 
next
  case (Suc n)
  have \<open>t \<in> partial_span (Suc n) S \<Longrightarrow> c *\<^sub>C t \<in> partial_span (Suc n) S\<close>
    for t
  proof-
    assume \<open>t \<in> partial_span (Suc n) S\<close>
    hence \<open>t \<in> {x + a *\<^sub>C y | a x y. x \<in> partial_span n S \<and> y \<in> S}\<close>
      by simp
    hence \<open>\<exists> a x y. x \<in> partial_span n S \<and> y \<in> S \<and> t = x + a *\<^sub>C y\<close>
      by blast
    then obtain a x y where \<open>x \<in> partial_span n S\<close> and \<open>y \<in> S\<close> 
      and \<open>t = x + a *\<^sub>C y\<close> by blast
    from \<open>t = x + a *\<^sub>C y\<close>
    have \<open>c *\<^sub>C t = c *\<^sub>C (x + a *\<^sub>C y)\<close>
      by blast
    hence \<open>c *\<^sub>C t = c *\<^sub>C x +  c *\<^sub>C (a *\<^sub>C y)\<close>
      by (simp add: scaleC_add_right)
    hence \<open>c *\<^sub>C t = c *\<^sub>C x +  (c * a) *\<^sub>C y\<close>
      by simp
    moreover have \<open>c *\<^sub>C x \<in> partial_span n S\<close>
      by (simp add: Suc.IH \<open>x \<in> partial_span n S\<close>)
    ultimately have  \<open>c *\<^sub>C t \<in> partial_span(Suc n) S\<close>
      using \<open>y \<in> S\<close> by auto
    thus ?thesis by blast
  qed
  thus ?case by blast 
qed

lemma partial_linear_manifold:
  fixes S::\<open>'a::complex_vector set\<close>
  assumes \<open>S \<noteq> {}\<close>
  shows \<open>is_linear_manifold ( \<Union>n. partial_span n S)\<close>
proof
  show "x + y \<in> (\<Union>n. partial_span n S)"
    if "x \<in> (\<Union>n. partial_span n S)"
      and "y \<in> (\<Union>n. partial_span n S)"
    for x :: 'a
      and y :: 'a
  proof-
    have \<open>\<exists> n. x \<in> partial_span n S\<close>
      using that by auto
    then obtain n where \<open>x \<in> partial_span n S\<close>
      by blast                    
    have \<open>\<exists> n. y \<in> partial_span n S\<close>
      using that by auto
    then obtain m where \<open>y \<in> partial_span m S\<close>
      by blast                    
    have \<open>\<exists> p. x + y \<in> partial_span p S\<close>
      using \<open>x \<in> partial_span n S\<close> \<open>y \<in> partial_span m S\<close> assms sum_partial_span by blast
    thus ?thesis
      by blast 
  qed
  show "c *\<^sub>C x \<in> (\<Union>n. partial_span n S)"
    if "x \<in> (\<Union>n. partial_span n S)"
    for x :: 'a
      and c :: complex
  proof-
    have \<open>\<exists> n. x \<in> partial_span n S\<close>
      using that by auto
    then obtain n where \<open>x \<in> partial_span n S\<close>
      by blast                    
    thus ?thesis using scaleC_partial_span
      by blast 
  qed
  show "0 \<in> (\<Union>n. partial_span n S)"
  proof-
    have \<open>0 \<in> partial_span 0 S\<close>
      by simp
    moreover have \<open>partial_span 0 S \<subseteq> (\<Union>n. partial_span n S)\<close>
      by blast
    ultimately show ?thesis by blast
  qed
qed

lemma is_subspace_I:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes \<open>is_linear_manifold S\<close>
  shows \<open>is_subspace (closure S )\<close>
proof
  show "x + y \<in> closure S"
    if "x \<in> closure S"
      and "y \<in> closure S"
    for x :: 'a
      and y :: 'a
  proof-
    have \<open>\<exists> r. (\<forall> n::nat. r n \<in> S) \<and> r \<longlonglongrightarrow> x\<close>
      using closure_sequential that(1) by auto
    then obtain r where \<open>\<forall> n::nat. r n \<in> S\<close> and \<open>r \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>\<exists> s. (\<forall> n::nat. s n \<in> S) \<and> s \<longlonglongrightarrow> y\<close>
      using closure_sequential that(2) by auto
    then obtain s where \<open>\<forall> n::nat. s n \<in> S\<close> and \<open>s \<longlonglongrightarrow> y\<close>
      by blast
    have \<open>\<forall> n::nat. r n + s n \<in> S\<close>
      by (simp add: \<open>\<forall>n. r n \<in> S\<close> \<open>\<forall>n. s n \<in> S\<close> assms is_linear_manifold.additive_closed)
    moreover have \<open>(\<lambda> n. r n + s n) \<longlonglongrightarrow> x + y\<close>
      by (simp add: \<open>r \<longlonglongrightarrow> x\<close> \<open>s \<longlonglongrightarrow> y\<close> tendsto_add)
    ultimately show ?thesis
      using assms is_linear_manifold.additive_closed is_subspace_cl that(1) that(2) by blast 
  qed
  show "c *\<^sub>C x \<in> closure S"
    if "x \<in> closure S"
    for x :: 'a
      and c :: complex
  proof-
    have \<open>\<exists> y. (\<forall> n::nat. y n \<in> S) \<and> y \<longlonglongrightarrow> x\<close>
      using Elementary_Topology.closure_sequential that by auto
    then obtain y where \<open>\<forall> n::nat. y n \<in> S\<close> and \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    have \<open>isCont (scaleC c) x\<close>
      using continuous_at continuous_on_def scaleC_continuous by blast
    hence \<open>(\<lambda> n. scaleC c (y n)) \<longlonglongrightarrow> scaleC c x\<close>
      by (simp add: \<open>y \<longlonglongrightarrow> x\<close> tendsto_scaleC)
    from  \<open>\<forall> n::nat. y n \<in> S\<close>
    have  \<open>\<forall> n::nat. scaleC c (y n) \<in> S\<close>
      by (simp add: assms is_linear_manifold.smult_closed)
    thus ?thesis
      by (simp add: assms is_linear_manifold.smult_closed is_subspace_cl that) 
  qed
  show "0 \<in> closure S"
    by (metis \<open>\<And>x c. x \<in> closure S \<Longrightarrow> c *\<^sub>C x \<in> closure S\<close> all_not_in_conv assms closure_eq_empty complex_vector.scale_zero_left is_linear_manifold_def)    
  show "closed (closure S)"
    by auto
qed

lemma partial_span_subspace:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes  \<open>S \<noteq> {}\<close>
  shows \<open>is_subspace (closure ( \<Union>n. partial_span n S) )\<close>
proof-
  have \<open>is_linear_manifold ( \<Union>n. partial_span n S)\<close>
    by (simp add:  \<open>S \<noteq> {}\<close> partial_linear_manifold)    
  thus ?thesis using is_subspace_I by blast
qed

proposition partial_span_lim:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes  \<open>S \<noteq> {}\<close>
  shows \<open>closure (complex_vector.span S) = closure (\<Union> n::nat. partial_span n S)\<close>
proof
  show "closure (complex_vector.span S) \<subseteq> closure (\<Union>n. partial_span n S)"
  proof-
    have \<open>S \<subseteq> (\<Union>n. partial_span n S)\<close>
    proof-
      have \<open>partial_span 1 S \<subseteq> (\<Union>n. partial_span n S)\<close>
        by blast
      moreover have \<open>S \<subseteq> partial_span 1 S\<close>
        using partial_span_1 by blast
      ultimately show ?thesis by blast
    qed
    hence \<open>S \<subseteq> closure (\<Union>n. partial_span n S)\<close>
      by (meson closure_subset order.trans)
    moreover have \<open>is_subspace (closure (\<Union>n. partial_span n S))\<close>
      using  \<open>S \<noteq> {}\<close> partial_span_subspace by auto      
    ultimately show ?thesis
      using closure_closure closure_mono is_subspace_span_A by blast      
  qed
  show "closure (\<Union>n. partial_span n S) \<subseteq> closure (complex_vector.span S)"
  proof-
    have \<open>(\<Union>n. partial_span n S) \<subseteq> (complex_vector.span S)\<close>
      by (simp add: UN_least partial_span_lim_n) 
    thus ?thesis
      by (simp add: closure_mono) 
  qed
qed

lemma equal_span_0_n:
  fixes  f::\<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close> and S::\<open>'a set\<close>
  shows \<open>\<forall> x::'a.
x \<in> partial_span n S \<longrightarrow>
 bounded_clinear f \<longrightarrow>
(\<forall> t \<in> S. f t = 0) \<longrightarrow> 
f x = 0\<close>
proof(induction n)
  case 0
  have \<open>x \<in> partial_span 0 S \<Longrightarrow> bounded_clinear f \<Longrightarrow> \<forall> t \<in> S. f t = 0 \<Longrightarrow> f x = 0\<close>
    for x::'a
  proof-
    assume \<open>x \<in> partial_span 0 S\<close> and \<open>bounded_clinear f\<close> and \<open>\<forall> t \<in> S. f t = 0\<close>
    from \<open>x \<in> partial_span 0 S\<close>
    have \<open>x = 0\<close>
      by simp
    thus ?thesis using \<open>bounded_clinear f\<close>
      by (simp add: bounded_clinear.clinear clinear_zero) 
  qed
  thus ?case by blast
next
  case (Suc n) 
  have \<open>x \<in> partial_span (Suc n) S \<Longrightarrow> bounded_clinear f \<Longrightarrow> \<forall> t \<in> S. f t = 0 \<Longrightarrow> f x = 0\<close>
    for x
  proof-
    assume \<open>x \<in> partial_span (Suc n) S\<close> and \<open>bounded_clinear f\<close> and \<open>\<forall> t \<in> S. f t = 0\<close>
    from \<open>x \<in> partial_span (Suc n) S\<close>
    have \<open>x \<in> {t + a *\<^sub>C y | a t y. t \<in> partial_span n S \<and> y \<in> S}\<close>
      by simp
    hence \<open>\<exists> a t y. t \<in> partial_span n S \<and> y \<in> S \<and> x = t + a *\<^sub>C y\<close>
      by blast
    then obtain a t y where \<open>t \<in> partial_span n S\<close> and \<open>y \<in> S\<close> and \<open>x = t + a *\<^sub>C y\<close>
      by blast
    have \<open>f t = 0\<close>
      using  \<open>t \<in> partial_span n S\<close> \<open>bounded_clinear f\<close> \<open>\<forall> t \<in> S. f t = 0\<close> Suc.IH by blast
    moreover have \<open>f y = 0\<close>
      using \<open>y \<in> S\<close>  \<open>\<forall> t \<in> S. f t = 0\<close>  by blast
    moreover have  \<open>f x = f t + f (a *\<^sub>C y)\<close>
      using \<open>bounded_clinear f\<close>  \<open>x = t + a *\<^sub>C y\<close>
      unfolding bounded_clinear_def clinear_def Modules.additive_def by simp    
    hence  \<open>f x = f t + a *\<^sub>C f y\<close>
      using \<open>bounded_clinear f\<close>  
      unfolding bounded_clinear_def clinear_def clinear_axioms_def by simp
    ultimately show ?thesis by simp
  qed
  thus ?case by blast
qed

lemma equal_span_0:
  fixes f::\<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close> 
    and S::\<open>'a set\<close> and x::'a
  assumes \<open>bounded_clinear f\<close> and \<open>\<forall> t \<in> S. f t = 0\<close> and \<open>x \<in> complex_vector.span S\<close> and  \<open>S \<noteq> {}\<close>
  shows \<open>f x = 0\<close>
    (* 
Proof in general case: Modules.thy \<rightarrow> eq_0_on_span
*)
  thm complex_vector.span_induct
proof -
  have \<open>x \<in> closure (complex_vector.span S)\<close>
    using  \<open>x \<in> complex_vector.span S\<close> closure_subset by auto
  hence \<open>x \<in> closure (\<Union> n::nat. partial_span n S)\<close>
    using  \<open>S \<noteq> {}\<close> partial_span_lim by blast
  hence \<open>\<exists> y::nat \<Rightarrow> _. (\<forall> k. y k \<in> (\<Union> n::nat. partial_span n S)) \<and> y \<longlonglongrightarrow> x\<close>
    using closure_sequential by blast
  then obtain y 
    where \<open>\<forall> k. y k \<in> (\<Union> n::nat. partial_span n S)\<close> and \<open>y \<longlonglongrightarrow> x\<close>
    by blast
  hence \<open>\<forall> k. \<exists> n. y k \<in> partial_span n S\<close>
    by blast
  then obtain n where \<open>\<forall> k. y k \<in> partial_span (n k) S\<close>
    by metis
  hence \<open>\<forall> k. f (y k) = 0\<close>
    using assms(1) assms(2) equal_span_0_n by blast
  have \<open>isCont f x\<close>
    using \<open>bounded_clinear f\<close>
    by (simp add: bounded_linear_continuous)
  hence  \<open>(\<lambda> k. f (y k)) \<longlonglongrightarrow> f x\<close>
    using \<open>y \<longlonglongrightarrow> x\<close> isCont_tendsto_compose by auto 
  hence \<open>(\<lambda> k. 0) \<longlonglongrightarrow> f x\<close>
    using  \<open>\<forall> k. f (y k) = 0\<close> 
    by simp
  moreover have  \<open>(\<lambda> k. 0) \<longlonglongrightarrow> (0::'b)\<close>
    by simp
  ultimately show ?thesis
    using LIMSEQ_unique by blast
qed

lemma equal_generator_0:
  fixes A::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and S::\<open>'a set\<close>
  assumes \<open>cgenerator S\<close> and \<open>\<And>x. x \<in> S \<Longrightarrow> Rep_bounded A x = 0\<close> and  \<open>S \<noteq> {}\<close>
  shows  \<open>A = 0\<close>
proof-
  have \<open>Rep_bounded A = Rep_bounded (0::('a,'b) bounded)\<close>
  proof
    show "Rep_bounded A x = Rep_bounded 0 x"
      for x :: 'a
    proof-
      have \<open>Rep_bounded (0::('a, 'b) bounded) x = 0\<close>
        by (simp add: zero_bounded_lift) 
      moreover have \<open>Rep_bounded A x = 0\<close>
      proof-
        have \<open>bounded_clinear (Rep_bounded A)\<close>
          using Rep_bounded by auto          
        have \<open>Abs_linear_space (closure (complex_vector.span S)) =
                Abs_linear_space UNIV\<close>
          using  \<open>cgenerator S\<close>  
          unfolding cgenerator_def top_linear_space_def Bounded_Operators.span_def
          by auto          
        hence \<open>closure (complex_vector.span S) = UNIV\<close>
          by (metis assms(1) cgenerator_def span.rep_eq top_linear_space.rep_eq)          
        hence  \<open>x \<in> closure (complex_vector.span S)\<close>
          by blast
        hence \<open>\<exists> y. (\<forall> n::nat. y n \<in> complex_vector.span S) \<and> y \<longlonglongrightarrow> x\<close>
          using closure_sequential by auto
        then obtain y where \<open>\<forall> n::nat. y n \<in> complex_vector.span S\<close> and \<open>y \<longlonglongrightarrow> x\<close>
          by blast
        have \<open>isCont (Rep_bounded A) x\<close>
          using \<open>bounded_clinear (Rep_bounded A)\<close>
          by (simp add: bounded_linear_continuous) 
        hence \<open>(\<lambda> n.  Rep_bounded A (y n)) \<longlonglongrightarrow> Rep_bounded A x\<close>
          using \<open>y \<longlonglongrightarrow> x\<close>
          by (simp add: isCont_tendsto_compose)
        moreover have \<open>Rep_bounded A (y n) = 0\<close>
          for n
        proof-
          from \<open>\<forall> n::nat. y n \<in> complex_vector.span S\<close>
          have \<open>y n \<in> complex_vector.span S\<close>
            by blast
          thus ?thesis using equal_span_0
            using assms(2)
            using \<open>bounded_clinear (Rep_bounded A)\<close>  \<open>S \<noteq> {}\<close> by auto  
        qed
        ultimately have \<open>(\<lambda> n.  0) \<longlonglongrightarrow> Rep_bounded A x\<close>
          by simp
        thus \<open>Rep_bounded A x = 0\<close>
          by (simp add: LIMSEQ_const_iff)
      qed
      ultimately show ?thesis by simp
    qed
  qed
  thus ?thesis using Rep_bounded_inject by blast 
qed

(* 
TODO: show this and then equal_generator as corollary?
lemma equal_span:
  fixes A B::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and S::\<open>'a set\<close>
  assumes \<open>\<And>x. x \<in> S \<Longrightarrow> Rep_bounded A x = Rep_bounded B x\<close> 
  shows \<open>\<And>x. x \<in> closure (complex_vector.span S) \<Longrightarrow> Rep_bounded A x = Rep_bounded B x\<close>
*)

lemma equal_generator:
  fixes A B::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and S::\<open>'a set\<close>
  assumes \<open>cgenerator S\<close> and \<open>\<And>x. x \<in> S \<Longrightarrow> Rep_bounded A x = Rep_bounded B x\<close> and  \<open>S \<noteq> {}\<close>
  shows \<open>A = B\<close>
proof-
  have \<open>A - B = 0\<close>
  proof-
    have \<open>x \<in> S \<Longrightarrow> Rep_bounded (A - B) x = 0\<close>
      for x
    proof-
      assume \<open>x \<in> S\<close>
      hence \<open>Rep_bounded A x = Rep_bounded B x\<close>
        using \<open>x \<in> S \<Longrightarrow> Rep_bounded A x = Rep_bounded B x\<close>
        by blast
      hence \<open>Rep_bounded A x - Rep_bounded B x = 0\<close>
        by simp
      hence \<open>(Rep_bounded A - Rep_bounded B) x = 0\<close>
        by simp
      moreover have \<open>Rep_bounded (A - B) = (\<lambda> t. Rep_bounded A t - Rep_bounded B t)\<close>
        using minus_bounded_lift by blast
      ultimately have \<open>Rep_bounded (A - B) x = 0\<close>
        by simp
      thus ?thesis by simp 
    qed
    thus ?thesis
      using assms(1) equal_generator_0  \<open>S \<noteq> {}\<close> by blast 
  qed
  thus ?thesis by simp
qed





chapter \<open>Chaos\<close>
  (* These are the results that I have not assimilated yet *)



(*
(* TODO: move specialized syntax into QRHL-specific file *)
consts cdot :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixl "\<cdot>" 70)

adhocoverloading
cdot timesOp applyOp applyOpSpace
(* Removed scaleC here: the overloading cannot be restricted to a specific type, so all occurrences of scaleC become \<cdot> *)
*)

(*
lemma cdot_plus_distrib[simp]: "U \<cdot> (A + B) = U \<cdot> A + U \<cdot> B"
  for A B :: "_ linear_space" and U :: "(_,_) bounded"
  apply transfer 
  by (cheat cdot_plus_distrib)
*)


(*
lemma scalar_op_linear_space_assoc [simp]: 
  "(\<alpha> *\<^sub>C A) \<cdot> S = \<alpha> *\<^sub>C (A \<cdot> S)" for \<alpha>::complex and A::"(_::complex_normed_vector,_::complex_normed_vector)bounded" and S::"(_::complex_normed_vector) linear_space"
proof transfer
  fix \<alpha> and A::"'a::chilbert_space \<Rightarrow> 'b::chilbert_space" and S
  have "(*\<^sub>C) \<alpha> ` closure {A x |x. x \<in> S} = closure {\<alpha> *\<^sub>C x |x. x \<in> {A x |x. x \<in> S}}" (is "?nested = _")
    by (simp add: closure_scaleC setcompr_eq_image)
  also have "\<dots> = closure {\<alpha> *\<^sub>C A x |x. x \<in> S}" (is "_ = ?nonnested")
    by (simp add: Setcompr_eq_image image_image)
  finally show "?nonnested = ?nested" by simp
qed
*) *)

(*
lemma apply_idOp[simp]: "applyOp idOp \<psi> = \<psi>"
  by (simp add: idOp.rep_eq)
*)

lemma scalar_mult_0_op[simp]: "0 *\<^sub>C A = 0" for A::"(_,_) bounded"
  apply transfer by auto

lemma scalar_op_op[simp]: "(a *\<^sub>C A) \<cdot> B = a *\<^sub>C (A \<cdot> B)"
  for A :: "('b::complex_normed_vector,_) bounded" and B :: "(_,'b) bounded"
  apply transfer by auto

lemma op_scalar_op[simp]: "timesOp A (a *\<^sub>C B) = a *\<^sub>C (timesOp A B)" 
  for a :: complex and A :: "(_,_) bounded" and B :: "(_,_) bounded"
  apply transfer
  by (simp add: bounded_clinear.clinear clinear.scaleC o_def)

(* REMOVE (subsumed by scale_scale) *)
lemma scalar_scalar_op[simp]: "a *\<^sub>C (b *\<^sub>C A) = (a*b) *\<^sub>C A"
  for a b :: complex and A  :: "(_,_) bounded"
  apply transfer by auto

lemma scalar_op_vec[simp]: "(a *\<^sub>C A) \<cdot> \<psi> = a *\<^sub>C (A \<cdot> \<psi>)" 
  for a :: complex and A :: "(_,_) bounded" and \<psi> :: "'a ell2"
  apply transfer by auto

(* REMOVE (subsumed by scaleC_left_imp_eq) *)
lemma add_scalar_mult: "a\<noteq>0 \<Longrightarrow> a *\<^sub>C A = a *\<^sub>C B \<Longrightarrow> A=B" for A B :: "('a,'b)l2bounded" and a::complex 
  by (rule scaleC_left_imp_eq)

lemma apply_idOp_space[simp]: "applyOpSpace idOp S = S"
  apply transfer by (simp add: is_subspace.closed)

lemma apply_0[simp]: "applyOp U 0 = 0"
  apply transfer 
  using additive.zero bounded_clinear.clinear clinear.axioms(1) by blast

lemma times_idOp1[simp]: "U \<cdot> idOp = U"
  apply transfer by auto

lemma times_idOp2[simp]: "timesOp idOp V = V" for V :: "(_,_) bounded"
  apply transfer by auto



lemma mult_INF[simp]: "U \<cdot> (INF x. V x) = (INF x. U \<cdot> V x)" 
  for V :: "'a \<Rightarrow> 'b::chilbert_space linear_space" and U :: "('b,'c::chilbert_space) bounded"
  apply transfer apply auto
  by (cheat mult_INF)

lemma mult_inf_distrib[simp]: "U \<cdot> (B \<sqinter> C) = (U \<cdot> B) \<sqinter> (U \<cdot> C)" 
  for U :: "(_,_) bounded" and B C :: "_ linear_space"
  using mult_INF[where V="\<lambda>x. if x then B else C" and U=U]
  unfolding INF_UNIV_bool_expand
  by simp

definition "inj_option \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"
definition "inv_option \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (Hilbert_Choice.inv \<pi> (Some y)) else None)"
lemma inj_option_Some_pi[simp]: "inj_option (Some o \<pi>) = inj \<pi>"
  unfolding inj_option_def inj_def by simp

lemma inj_option_Some[simp]: "inj_option Some"
  using[[show_consts,show_types,show_sorts]]
  apply (rewrite asm_rl[of "(Some::'a\<Rightarrow>_) = Some o id"]) apply simp
  unfolding inj_option_Some_pi by simp

lemma inv_option_Some: "surj \<pi> \<Longrightarrow> inv_option (Some o \<pi>) = Some o (Hilbert_Choice.inv \<pi>)"
  unfolding inv_option_def o_def inv_def apply (rule ext) by auto
lemma inj_option_map_comp[simp]: "inj_option f \<Longrightarrow> inj_option g \<Longrightarrow> inj_option (f \<circ>\<^sub>m g)"
  unfolding inj_option_def apply auto
  by (smt map_comp_Some_iff)

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
  then show "x = y"
    by (meson inv_into_injective option.inject x_pi y_pi)
qed

lift_definition classical_operator' :: "('a\<Rightarrow>'b option) \<Rightarrow> ('a ell2 \<Rightarrow> 'b ell2)" is
  "\<lambda>\<pi> \<psi> b. case inv_option \<pi> b of Some a \<Rightarrow> \<psi> a | None \<Rightarrow> 0"
  sorry


lift_definition classical_operator :: "('a\<Rightarrow>'b option) \<Rightarrow> ('a ell2,'b ell2) bounded" is
  "classical_operator'"
  sorry

lemma classical_operator_basis: "inj_option \<pi> \<Longrightarrow>
    applyOp (classical_operator \<pi>) (ket x) = (case \<pi> x of Some y \<Rightarrow> ket y | None \<Rightarrow> 0)"

  by (cheat TODO5)
lemma classical_operator_adjoint[simp]: 
  "inj_option \<pi> \<Longrightarrow> adjoint (classical_operator \<pi>) = classical_operator (inv_option \<pi>)"
  for \<pi> :: "'a \<Rightarrow> 'b option"
  by (cheat TODO1)

lemma classical_operator_mult[simp]:
  "inj_option \<pi> \<Longrightarrow> inj_option \<rho> \<Longrightarrow> classical_operator \<pi> \<cdot> classical_operator \<rho> = classical_operator (map_comp \<pi> \<rho>)"
  apply (rule equal_basis)
  unfolding timesOp_assoc_linear_space
  apply (subst classical_operator_basis, simp)+
  apply (case_tac "\<rho> x")
  apply auto
  apply (subst classical_operator_basis, simp)
  by auto

lemma classical_operator_Some[simp]: "classical_operator Some = idOp"
  apply (rule equal_basis) apply (subst classical_operator_basis) apply simp by auto

definition "unitary U = (U \<cdot> (U*) = idOp \<and> U* \<cdot> U = idOp)"  
definition "isometry U = (U* \<cdot> U = idOp)"  

lemma adjUU[simp]: "isometry U \<Longrightarrow> U* \<cdot> U = idOp" unfolding isometry_def by simp
lemma UadjU[simp]: "unitary U \<Longrightarrow> U \<cdot> U* = idOp" unfolding unitary_def by simp

lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"(_,_)bounded"
  unfolding unitary_def by auto

lemma unitary_times[simp]: "unitary A \<Longrightarrow> unitary B \<Longrightarrow> unitary (A\<cdot>B)"
  unfolding unitary_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma isometry_times[simp]: "isometry A \<Longrightarrow> isometry B \<Longrightarrow> isometry (A\<cdot>B)"
  unfolding isometry_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma isometry_classical_operator[simp]:
  assumes "inj \<pi>"
  shows "isometry (classical_operator (Some o \<pi>))"
proof -
  have comp: "inv_option (Some \<circ> \<pi>) \<circ>\<^sub>m (Some \<circ> \<pi>) = Some" 
    apply (rule ext) unfolding inv_option_def o_def 
    using assms unfolding inj_def inv_def by auto

  show ?thesis
    unfolding isometry_def
    apply (subst classical_operator_adjoint) using assms apply simp
    apply (subst classical_operator_mult) using assms apply auto[2]
    apply (subst comp)
    by simp
qed

lemma unitary_classical_operator[simp]:
  assumes "bij \<pi>"
  shows "unitary (classical_operator (Some o \<pi>))"
proof (unfold unitary_def, rule conjI)
  have "isometry (classical_operator (Some o \<pi>))"
    by (simp add: assms bij_is_inj)
  then show "classical_operator (Some \<circ> \<pi>)* \<cdot> classical_operator (Some \<circ> \<pi>) = idOp"
    unfolding isometry_def by simp
next
  have "inj \<pi>"
    by (simp add: assms bij_is_inj)
  have comp: "Some \<circ> \<pi> \<circ>\<^sub>m inv_option (Some \<circ> \<pi>) = Some"
    apply (rule ext)
    unfolding inv_option_def o_def map_comp_def
    unfolding inv_def apply auto
    apply (metis \<open>inj \<pi>\<close> inv_def inv_f_f)
    by (metis assms bij_def image_iff range_eqI)

  show "classical_operator (Some \<circ> \<pi>) \<cdot> classical_operator (Some \<circ> \<pi>)* = idOp"
    by (simp add: comp \<open>inj \<pi>\<close>)
qed

lemma unitary_image[simp]: "unitary U \<Longrightarrow> applyOpSpace U top = top"
  by (cheat TODO1)

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def by simp

(* TODO: Replace by existing class CARD_1 *)
class singleton = fixes the_single :: "'a" assumes everything_the_single: "x=the_single" begin
lemma singleton_UNIV: "UNIV = {the_single}"
  using everything_the_single by auto
lemma everything_the_same: "(x::'a)=y"
  apply (subst everything_the_single, subst (2) everything_the_single) by simp
lemma singleton_ext: "x (a::'a) = y b \<Longrightarrow> x = y"
  apply (rule ext) 
  apply (subst (asm) everything_the_same[where x=a])
  apply (subst (asm) everything_the_same[where x=b])
  by simp
lemma CARD_singleton[simp]: "CARD('a) = 1"
  by (simp add: singleton_UNIV)
subclass finite apply standard unfolding singleton_UNIV by simp  
end

instantiation unit :: singleton begin
definition "singleton = ()"
instance apply standard by auto
end

(* TODO move to L2_Complex *)
lift_definition C1_to_complex :: "'a::singleton ell2 \<Rightarrow> complex" is
  "\<lambda>\<psi>. \<psi> the_single" .
lift_definition complex_to_C1 :: "complex \<Rightarrow> 'a::singleton ell2" is
  "\<lambda>c _. c" 
  by simp

lemma C1_to_complex_inverse[simp]: "complex_to_C1 (C1_to_complex \<psi>) = \<psi>"
  apply transfer apply (rule singleton_ext) by auto

lemma complex_to_C1_inverse[simp]: "C1_to_complex (complex_to_C1 \<psi>) = \<psi>"
  apply transfer by simp

lemma bounded_clinear_complex_to_C1: "bounded_clinear complex_to_C1"
  apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def)+

lemma bounded_clinear_C1_to_complex: "bounded_clinear C1_to_complex"
  apply (rule bounded_clinear_intro[where K=1])
  by (transfer; auto simp: ell2_norm_finite_def singleton_UNIV)+

lift_definition ell2_to_bounded :: "'a::chilbert_space \<Rightarrow> (unit ell2,'a) bounded" is
  "\<lambda>(\<psi>::'a) (x::unit ell2). C1_to_complex x *\<^sub>C \<psi>"
  by (simp add: bounded_clinear_C1_to_complex bounded_clinear_scaleC_const)

lemma ell2_to_bounded_applyOp: "ell2_to_bounded (A\<cdot>\<psi>) = A \<cdot> ell2_to_bounded \<psi>" for A :: "(_,_)bounded"
  apply transfer
  by (simp add: bounded_clinear_def clinear.scaleC o_def)

lemma ell2_to_bounded_scalar_times: "ell2_to_bounded (a *\<^sub>C \<psi>) = a *\<^sub>C ell2_to_bounded \<psi>" for a::complex
  apply (rewrite at "a *\<^sub>C \<psi>" DEADID.rel_mono_strong[of _ "(a *\<^sub>C idOp) \<cdot> \<psi>"])
  apply transfer apply simp
  apply (subst ell2_to_bounded_applyOp)
  by simp

lift_definition kernel :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> 'a linear_space" is ker_op
  by (metis ker_op_lin)

definition eigenspace :: "complex \<Rightarrow> ('a::chilbert_space,'a) bounded \<Rightarrow> 'a linear_space" where
  "eigenspace a A = kernel (A - a *\<^sub>C idOp)" 

lemma kernel_scalar_times[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a *\<^sub>C A) = kernel A"
  for a :: complex and A :: "(_,_) bounded"
  apply transfer
  by (smt Collect_cong complex_vector.scale_eq_0_iff ker_op_def)

lemma kernel_0[simp]: "kernel 0 = top"
  apply transfer unfolding ker_op_def by simp

lemma kernel_id[simp]: "kernel idOp = 0"
  apply transfer unfolding ker_op_def by simp

lemma [simp]: "a\<noteq>0 \<Longrightarrow> eigenspace b (a *\<^sub>C A) = eigenspace (b/a) A"
  unfolding eigenspace_def
  apply (rewrite at "kernel \<hole>" DEADID.rel_mono_strong[where y="a *\<^sub>C (A - (b / a) *\<^sub>C idOp)"])
  apply auto[1]
  by (subst kernel_scalar_times, auto)

section \<open>Projectors\<close>

(* TODO: link with definition from Complex_Inner (needs definition of adjoint, first) *)
definition "isProjector P = (P=P* \<and> P=P\<cdot>P)"

consts Proj :: "'a linear_space \<Rightarrow> ('a,'a) bounded"
lemma isProjector_Proj[simp]: "isProjector (Proj S)"
  by (cheat TODO5)

lemma imageOp_Proj[simp]: "applyOpSpace (Proj S) top = S"
  by (cheat TODO5)

lemma Proj_leq: "Proj S \<cdot> A \<le> S"
  by (metis imageOp_Proj inf.orderE inf.orderI mult_inf_distrib top_greatest)


lemma Proj_times: "A \<cdot> Proj S \<cdot> A* = Proj (A\<cdot>S)" for A::"(_,_)bounded"
  by (cheat TODO2)

abbreviation proj :: "'a::chilbert_space \<Rightarrow> ('a,'a) bounded" where "proj \<psi> \<equiv> Proj (span {\<psi>})"

lemma proj_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" for a::complex and \<psi>::"'a ell2"
  by (cheat TODO2)


lemma move_plus:
  "Proj (ortho C) \<cdot> A \<le> B \<Longrightarrow> A \<le> B + C"
  for A B C::"_ linear_space"
  by (cheat TODO2)


section \<open>Tensor products\<close>

consts "tensorOp" :: "('a,'b) l2bounded \<Rightarrow> ('c,'d) l2bounded \<Rightarrow> ('a*'c,'b*'d) l2bounded"

lift_definition "tensorVec" :: "'a ell2 \<Rightarrow> 'c ell2 \<Rightarrow> ('a*'c) ell2" is
  "\<lambda>\<psi> \<phi> (x,y). \<psi> x * \<phi> y"
  by (cheat tensorVec)

definition "tensorSpace A B = span {tensorVec \<psi> \<phi>| \<psi> \<phi>. \<psi> \<in> Rep_linear_space A \<and> \<phi> \<in> Rep_linear_space B}"

consts tensor :: "'a \<Rightarrow> 'b \<Rightarrow> 'c" (infixr "\<otimes>" 71)
  adhoc_overloading tensor tensorOp tensorSpace tensorVec

lemma idOp_tensor_idOp[simp]: "idOp\<otimes>idOp = idOp"
  by (cheat TODO2)

consts "comm_op" :: "('a*'b, 'b*'a) l2bounded"

lemma adj_comm_op[simp]: "adjoint comm_op = comm_op"
  by (cheat TODO2)

lemma
  comm_op_swap[simp]: "comm_op \<cdot> (A\<otimes>B) \<cdot> comm_op = B\<otimes>A"
  for A::"('a,'b) l2bounded" and B::"('c,'d) l2bounded"
  by (cheat TODO3)

lemma comm_op_times_comm_op[simp]: "comm_op \<cdot> comm_op = idOp"
proof -
  find_theorems "idOp \<otimes> idOp"
  have "comm_op \<cdot> (idOp \<otimes> idOp) \<cdot> comm_op = idOp \<otimes> idOp" by (simp del: idOp_tensor_idOp)
  then show ?thesis by simp
qed

lemma unitary_comm_op[simp]: "unitary comm_op"
  unfolding unitary_def by simp

consts "assoc_op" :: "('a*'b*'c, ('a*'b)*'c) l2bounded"
lemma unitary_assoc_op[simp]: "unitary assoc_op"
  by (cheat TODO5)

lemma tensor_scalar_mult1[simp]: "(a *\<^sub>C A) \<otimes> B = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)
lemma tensor_scalar_mult2[simp]: "A \<otimes> (a *\<^sub>C B) = a *\<^sub>C (A \<otimes> B)" for a::complex and A::"('a,'b)l2bounded" and B::"('c,'d)l2bounded"
  by (cheat TODO3)

lemma tensor_times[simp]: "(U1 \<otimes> U2) \<cdot> (V1 \<otimes> V2) = (U1 \<cdot> V1) \<otimes> (U2 \<cdot> V2)"
  for V1 :: "('a1,'b1) l2bounded" and U1 :: "('b1,'c1) l2bounded"
    and V2 :: "('a2,'b2) l2bounded" and U2 :: "('b2,'c2) l2bounded"
  by (cheat TODO3)

consts remove_qvar_unit_op :: "('a*unit,'a) l2bounded"


definition addState :: "'a ell2 \<Rightarrow> ('b,'b*'a) l2bounded" where
  "addState \<psi> = idOp \<otimes> (ell2_to_bounded \<psi>) \<cdot> remove_qvar_unit_op*"

lemma addState_times_scalar[simp]: "addState (a *\<^sub>C \<psi>) = a *\<^sub>C addState \<psi>" for a::complex and psi::"'a ell2"
  unfolding addState_def by (simp add: ell2_to_bounded_scalar_times)

lemma tensor_adjoint[simp]: "adjoint (U\<otimes>V) = (adjoint U) \<otimes> (adjoint V)"
  for U :: "('a,'b) l2bounded" and V :: "('c,'d) l2bounded"
  by (cheat TODO3)

lemma tensor_unitary[simp]: 
  assumes "unitary U" and "unitary V"
  shows "unitary (U\<otimes>V)"
  using assms unfolding unitary_def by simp

subsection \<open>Dual\<close>

(* The interpretation of Riesz representation theorem as an anti-isomorphism
between a Hilbert space and its dual of a Hilbert space is the justification of 
the brac-ket notation *)

(* TODO: the things related to topological_real_vector should be in earlier theory *)

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>continuous_on\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool\<close>)\<close>

class topological_real_vector = real_vector + topological_ab_group_add +
  assumes scaleR_continuous: "continuous_on UNIV (case_prod scaleR)"

class topological_complex_vector = complex_vector + topological_ab_group_add +
  assumes scaleC_continuous: "continuous_on UNIV (case_prod scaleC)"

setup \<open>Sign.add_const_constraint
(\<^const_name>\<open>continuous_on\<close>, SOME \<^typ>\<open>'a set \<Rightarrow> ('a::topological_space \<Rightarrow> 'b::topological_space) \<Rightarrow> bool\<close>)\<close>

thm tendsto_scaleR
  (* This overwrites Limits.tendsto_scaleR by a stronger fact *)
lemma tendsto_scaleR[tendsto_intros]:
  fixes b :: "'a::topological_real_vector"
  assumes "(f \<longlongrightarrow> a) F" and "(g \<longlongrightarrow> b) F"
  shows "((\<lambda>x. f x *\<^sub>R g x) \<longlongrightarrow> a *\<^sub>R b) F"
proof -
  have "(((\<lambda>x. case_prod scaleR (f x, g x))) \<longlongrightarrow> case_prod scaleR (a, b)) F"
    apply (rule tendsto_compose[where g="case_prod scaleR"])
    using continuous_on_def scaleR_continuous apply blast
    by (simp add: assms(1) assms(2) tendsto_Pair)
  then show ?thesis
    by (simp add: case_prod_beta o_def)
qed

(* This overwrites Limits.tendsto_scaleR by a stronger fact *)
lemma tendsto_scaleC[tendsto_intros]:
  fixes b :: "'a::topological_complex_vector"
  assumes "(f \<longlongrightarrow> a) F" and "(g \<longlongrightarrow> b) F"
  shows "((\<lambda>x. f x *\<^sub>C g x) \<longlongrightarrow> a *\<^sub>C b) F"
proof -
  have "(((\<lambda>x. case_prod scaleC (f x, g x))) \<longlongrightarrow> case_prod scaleC (a, b)) F"
    apply (rule tendsto_compose[where g="case_prod scaleC"])
    using continuous_on_def scaleC_continuous apply blast
    by (simp add: assms(1) assms(2) tendsto_Pair)
  then show ?thesis
    by (simp add: case_prod_beta o_def)
qed

(* lemma continuous_on_scaleC[continuous_intros]:
  fixes g :: "_\<Rightarrow>'a::topological_complex_vector"
  assumes "continuous_on s f" and "continuous_on s g"
  shows "continuous_on s (\<lambda>x. f x *\<^sub>C g x)" 
  using assms unfolding continuous_on_def by (auto intro!: tendsto_intros) *)

instance topological_complex_vector \<subseteq> topological_real_vector
  apply standard
  apply (rewrite at "case_prod scaleR" DEADID.rel_mono_strong[of _ "\<lambda>x. (complex_of_real (fst x)) *\<^sub>C (snd x)"])
  apply (auto simp: scaleR_scaleC case_prod_beta)[1]
  unfolding continuous_on_def
  apply (auto intro!: tendsto_intros)
  using tendsto_fst tendsto_snd by fastforce+

instance real_normed_vector \<subseteq> topological_real_vector
proof standard 
  have "(\<lambda>(x, y). x *\<^sub>R y) \<midarrow>(a, b)\<rightarrow> a *\<^sub>R b" for a and b :: 'a
    unfolding case_prod_beta apply (rule Limits.tendsto_scaleR)
    using tendsto_fst tendsto_snd by fastforce+
  then show "continuous_on UNIV (\<lambda>(x, y::'a). x *\<^sub>R y)"
    unfolding continuous_on_def by simp
qed

instance complex_normed_vector \<subseteq> topological_complex_vector
proof standard 
  note tendsto_scaleC = bounded_bilinear.tendsto[OF bounded_cbilinear_scaleC[THEN bounded_cbilinear.bounded_bilinear]]
  have "(\<lambda>(x, y). x *\<^sub>C y) \<midarrow>(a, b)\<rightarrow> a *\<^sub>C b" for a and b :: 'a
    unfolding case_prod_beta apply (rule tendsto_scaleC)
    using tendsto_fst tendsto_snd by fastforce+
  then show "continuous_on UNIV (\<lambda>(x, y::'a). x *\<^sub>C y)"
    unfolding continuous_on_def by simp
qed

lemma clinear_0[simp]: "clinear (\<lambda>f. 0)"
  unfolding clinear_def Modules.additive_def clinear_axioms_def by simp

typedef (overloaded) 'a dual = \<open>{f::'a::topological_complex_vector\<Rightarrow>complex. continuous_on UNIV f \<and> clinear f}\<close>
  apply (rule exI[where x="\<lambda>f. 0"]) by auto

instantiation dual :: (complex_normed_vector) chilbert_space begin
instance 
  by (cheat "dual :: (complex_normed_vector) chilbert_space")
end

subsection \<open>Dimension\<close>


lift_definition finite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> is
  \<open>\<lambda>S. \<exists>G. finite G \<and> complex_vector.span G = S\<close> .

(* lift_definition infinite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> is
\<open>\<lambda>S. (
\<exists> f::nat \<Rightarrow> 'a set.
(\<forall>n. is_subspace (f n)) \<and>
(\<forall> n. f n \<subset> f (Suc n)) \<and>
(\<forall> n. f n \<subseteq> S)
)\<close> *)


(* (* TODO: define on sets first and lift? *)
(* TODO: I would define only finite_dim and just negate it for infinite_dim (avoid too many definitions) *)
definition infinite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> where
\<open>infinite_dim S = (
\<exists> f::nat \<Rightarrow> 'a linear_space.
(\<forall> n::nat. Rep_linear_space (f n) \<subset> Rep_linear_space (f (Suc n))) \<and>
(\<forall> n::nat. Rep_linear_space (f n) \<subseteq> Rep_linear_space S)
)\<close> *)

(* definition finite_dim :: \<open>(('a::chilbert_space) linear_space) \<Rightarrow> bool\<close> where
\<open>finite_dim S = ( \<not> (infinite_dim S) )\<close> *)


subsection \<open>Tensor product\<close>

(* TODO: define Tensor later as "('a dual, 'b) hilbert_schmidt" *)

(* (* Tensor product *)
typedef (overloaded) ('a::chilbert_space, 'b::chilbert_space) tensor
(* TODO: is that compatible (isomorphic) with tensorVec? *)
= \<open>{ A :: ('a dual, 'b) bounded. finite_dim (Abs_linear_space ((Rep_bounded A) ` UNIV)) }\<close>
   *)

(* TODO: universal property of tensor products *)

(* Embedding of (x,y) into the tensor product as x\<otimes>y *)
(* TODO: Shouldn't this be called "tensor" or similar then? *)
(* definition HS_embedding :: \<open>('a::chilbert_space)*('b::chilbert_space) \<Rightarrow> ('a, 'b) tensor\<close> where
\<open>HS_embedding x = Abs_tensor ( Abs_bounded (\<lambda> w::'a dual. ( (Rep_bounded w) (fst x) ) *\<^sub>C (snd x) ) )\<close> *)

(* The tensor product of two Hilbert spaces is a Hilbert space *)
(* instantiation tensor :: (chilbert_space,chilbert_space) "chilbert_space" begin
instance 
end *)



end





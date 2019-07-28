(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Main results:
- bounded: Definition of complex bounded operators. Instantiation as a complex Banach space.

*)


theory Bounded_Operators
  imports Complex_Inner_Product Real_Bounded_Operators Extended_Sorry

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


section \<open>Adjoint\<close>

lift_definition
  adjoint :: "('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> ('b,'a) bounded" ("_*" [99] 100) 
  is Adj by (fact Adj_bounded_clinear)

lemma adjoint_I:
  fixes G :: "('b::chilbert_space, 'a::chilbert_space) bounded"
  shows \<open>\<forall>x. \<forall>y. \<langle>Rep_bounded (G*) x, y\<rangle> = \<langle>x, (Rep_bounded G) y\<rangle>\<close>
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


lemma Adj_bounded_plus:
\<open>(A + B)* = (A*) + (B*)\<close>
proof -
  { have f1: "\<forall>b ba. (\<exists>a bb. \<langle>Rep_bounded b (a::'a), bb::'b\<rangle> \<noteq> \<langle>a, Rep_bounded ba bb\<rangle>) \<or> b = ba*"
  using adjoint_D by blast
  obtain aa :: "('b, 'a) bounded \<Rightarrow> ('a, 'b) bounded \<Rightarrow> 'a" and bb :: "('b, 'a) bounded \<Rightarrow> ('a, 'b) bounded \<Rightarrow> 'b" where
    f2: "\<forall>x0 x1. (\<exists>v2 v3. \<langle>Rep_bounded x1 v2, v3\<rangle> \<noteq> \<langle>v2, Rep_bounded x0 v3\<rangle>) = (\<langle>Rep_bounded x1 (aa x0 x1), bb x0 x1\<rangle> \<noteq> \<langle>aa x0 x1, Rep_bounded x0 (bb x0 x1)\<rangle>)"
by moura
have f3: "bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)* = Abs_bounded (Rep_bounded (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B))\<^sup>\<dagger>)"
  by (metis (no_types) Rep_bounded_inverse adjoint.rep_eq)
have "A* = Abs_bounded (Rep_bounded A\<^sup>\<dagger>)"
by (metis Rep_bounded_inverse adjoint.rep_eq)
then have f4: "\<langle>aa (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>)), Rep_bounded A (bb (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>)))\<rangle> = \<langle>Rep_bounded (Abs_bounded (Rep_bounded A\<^sup>\<dagger>)) (aa (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>))), bb (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>))\<rangle>"
  by (metis adjoint_I)
  have f5: "\<langle>aa (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>)), Rep_bounded B (bb (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>)))\<rangle> = \<langle>Rep_bounded (Abs_bounded (Rep_bounded B\<^sup>\<dagger>)) (aa (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>))), bb (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>))\<rangle>"
    by (metis (no_types) Rep_bounded_inverse adjoint.rep_eq adjoint_I)
have "Rep_bounded (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (bb (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>))) = Rep_bounded A (bb (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>))) + Rep_bounded B (bb (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)) (Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>)))"
  by (metis plus_bounded_def plus_bounded_lift)
  then have "Abs_bounded (Rep_bounded A\<^sup>\<dagger>) + Abs_bounded (Rep_bounded B\<^sup>\<dagger>) = bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B)*"
using f5 f4 f2 f1 by (simp add: cinner_left_distrib cinner_right_distrib plus_bounded_lift)
  hence "Abs_bounded (Rep_bounded (bounded_of_rbounded (rbounded_of_bounded A + rbounded_of_bounded B))\<^sup>\<dagger>) = bounded_of_rbounded (rbounded_of_bounded (Abs_bounded (Rep_bounded A\<^sup>\<dagger>)) + rbounded_of_bounded (Abs_bounded (Rep_bounded B\<^sup>\<dagger>)))"
    using f3 by (simp add: plus_bounded_def) } note 1 = this

  show ?thesis 
  unfolding plus_bounded_def adjoint_def 
  apply auto
  by (rule 1)
qed

lemma Adj_bounded_uminus[simp]:
\<open>(- A)* = - (A*)\<close>
  by (metis (no_types, lifting) Adj_bounded_plus  add_cancel_left_right diff_0 ordered_field_class.sign_simps(9))

lemma Adj_bounded_minus[simp]:
\<open>(A - B)* = (A*) - (B*)\<close>
  by (metis Adj_bounded_plus add_right_cancel diff_add_cancel)


lemma Adj_bounded_zero[simp]:
\<open>0* = 0\<close>
  by (metis Adj_bounded_plus add_cancel_right_right)

section \<open>Composition\<close>

lift_definition rtimesOp:: 
  "('b::real_normed_vector,'c::real_normed_vector) rbounded
     \<Rightarrow> ('a::real_normed_vector,'b) rbounded \<Rightarrow> ('a,'c) rbounded"
 (infixl "\<circ>\<^sub>R" 55) is "(o)"
  unfolding o_def 
  by (rule bounded_linear_compose, simp_all)

definition timesOp:: 
  "('b::complex_normed_vector,'c::complex_normed_vector) bounded
     \<Rightarrow> ('a::complex_normed_vector,'b) bounded \<Rightarrow> ('a,'c) bounded"   
 (infixl "\<circ>\<^sub>C" 55)
where \<open>timesOp f g = bounded_of_rbounded (rtimesOp (rbounded_of_bounded f) (rbounded_of_bounded g))\<close>

lemma timesOp_Rep_bounded:
  \<open>Rep_bounded (f \<circ>\<^sub>C g) = (Rep_bounded f)\<circ>(Rep_bounded g)\<close>
  unfolding timesOp_def
  by (metis (no_types, lifting) comp_apply rbounded_bounded rbounded_of_bounded.rep_eq rbounded_of_bounded_prelim rtimesOp.rep_eq)

lemma rtimesOp_assoc: "(A \<circ>\<^sub>R B) \<circ>\<^sub>R C = A \<circ>\<^sub>R (B \<circ>\<^sub>R C)" 
  apply transfer
  by (simp add: comp_assoc) 

lemma timesOp_assoc: "(A \<circ>\<^sub>C B)  \<circ>\<^sub>C C = A  \<circ>\<^sub>C (B  \<circ>\<^sub>C C)" 
  by (metis (no_types, lifting) Rep_bounded_inverse fun.map_comp timesOp_Rep_bounded) 


lemma rtimesOp_dist1:
  fixes a b :: "('b::real_normed_vector, 'c::real_normed_vector) rbounded"
    and c :: "('a::real_normed_vector, 'b) rbounded"
  shows "(a + b) \<circ>\<^sub>R c = (a \<circ>\<^sub>R c) + (b \<circ>\<^sub>R c)"
proof -
 (* sledgehammer *)
  {  fix aa :: "'b \<Rightarrow> 'c" and ba :: "'b \<Rightarrow> 'c" and ca :: "'a \<Rightarrow> 'b"
  assume a1: "bounded_linear ca"
  assume a2: "bounded_linear ba"
  assume a3: "bounded_linear aa"
  { fix aaa :: 'a
    have ff1: "\<forall>r. Rep_rbounded (r::('b, 'c) rbounded) \<circ> ca = Rep_rbounded (r \<circ>\<^sub>R Abs_rbounded ca)"
      using a1 by (simp add: Abs_rbounded_inverse rtimesOp.rep_eq)
    have ff2: "Rep_rbounded (Abs_rbounded ba) = ba"
      using a2 by (meson Abs_rbounded_inverse mem_Collect_eq)
    have "Rep_rbounded (Abs_rbounded aa) = aa"
      using a3 by (metis Abs_rbounded_inverse mem_Collect_eq)
    then have "Abs_rbounded ((\<lambda>b. aa b + ba b) \<circ> ca) = Abs_rbounded (\<lambda>a. Rep_rbounded (Abs_rbounded (aa \<circ> ca)) a + Rep_rbounded (Abs_rbounded (ba \<circ> ca)) a) \<or> ((\<lambda>b. aa b + ba b) \<circ> ca) aaa = Rep_rbounded (Abs_rbounded (aa \<circ> ca)) aaa + Rep_rbounded (Abs_rbounded (ba \<circ> ca)) aaa"
      using ff2 ff1 by (metis (no_types) Rep_rbounded_inverse comp_apply) }
  then have "Abs_rbounded ((\<lambda>b. aa b + ba b) \<circ> ca) = Abs_rbounded (\<lambda>a. Rep_rbounded (Abs_rbounded (aa \<circ> ca)) a + Rep_rbounded (Abs_rbounded (ba \<circ> ca)) a)"
    by meson
} note 1 = this

  show ?thesis
  unfolding rtimesOp_def 
  apply auto
  apply transfer
  unfolding plus_rbounded_def
  apply auto
  apply (rule 1)
  by blast
qed


lemma rtimesOp_dist2:
  fixes a b :: "('a::real_normed_vector, 'b::real_normed_vector) rbounded"
    and c :: "('b, 'c::real_normed_vector) rbounded"
  shows "c \<circ>\<^sub>R (a + b) = (c \<circ>\<^sub>R a) + (c \<circ>\<^sub>R b)"
proof-
  have \<open>Rep_rbounded (c \<circ>\<^sub>R (a + b)) x = Rep_rbounded ( (c \<circ>\<^sub>R a) +  (c \<circ>\<^sub>R b) ) x\<close>
    for x
  proof-
    have \<open>bounded_linear (Rep_rbounded c)\<close>
      using Rep_rbounded by auto
    have \<open>Rep_rbounded (c \<circ>\<^sub>R (a + b)) x = (Rep_rbounded c) ( (Rep_rbounded (a + b)) x )\<close>
      by (simp add: rtimesOp.rep_eq)
    also have \<open>\<dots> = (Rep_rbounded c) ( Rep_rbounded a x + Rep_rbounded b x )\<close>
      by (simp add: plus_rbounded.rep_eq)
    also have \<open>\<dots> = (Rep_rbounded c) ( Rep_rbounded a x ) + (Rep_rbounded c) ( Rep_rbounded b x )\<close>
      using  \<open>bounded_linear (Rep_rbounded c)\<close>
      unfolding bounded_linear_def linear_def
      by (simp add: \<open>bounded_linear (Rep_rbounded c)\<close> linear_simps(1))
    also have \<open>\<dots> = ( (Rep_rbounded c) \<circ> (Rep_rbounded a) ) x
                  + ( (Rep_rbounded c) \<circ> (Rep_rbounded b) ) x\<close>
      by simp
    finally have \<open>Rep_rbounded (c \<circ>\<^sub>R (a + b)) x = Rep_rbounded ( (c \<circ>\<^sub>R a) +  (c \<circ>\<^sub>R b) ) x\<close>
      by (simp add: plus_rbounded.rep_eq rtimesOp.rep_eq)
    thus ?thesis
      by simp 
  qed
  hence \<open>Rep_rbounded (c \<circ>\<^sub>R (a + b)) = Rep_rbounded ( (c \<circ>\<^sub>R a) +  (c \<circ>\<^sub>R b) )\<close>
    by blast
  thus ?thesis 
    using Rep_rbounded_inject
    by blast  
qed


lemma timesOp_dist1:
  fixes a b :: "('b::complex_normed_vector, 'c::complex_normed_vector) bounded"
      and c :: "('a::complex_normed_vector, 'b) bounded"
shows "(a + b) \<circ>\<^sub>C c = (a \<circ>\<^sub>C c) + (b \<circ>\<^sub>C c)"
  using rtimesOp_dist1
  by (metis (no_types, lifting) bounded_of_rbounded_plus rbounded_of_bounded.rep_eq rbounded_of_bounded_plus rbounded_of_bounded_prelim rtimesOp.rep_eq timesOp_Rep_bounded timesOp_def) 

lemma timesOp_dist2:
  fixes a b :: "('a::complex_normed_vector, 'b::complex_normed_vector) bounded"
    and c :: "('b, 'c::complex_normed_vector) bounded"
  shows "c \<circ>\<^sub>C (a + b) = (c \<circ>\<^sub>C a) + (c \<circ>\<^sub>C b)"
  using rtimesOp_dist2
  by (metis (no_types, lifting) bounded_of_rbounded_plus rbounded_of_bounded.rep_eq rbounded_of_bounded_plus rbounded_of_bounded_prelim rtimesOp.rep_eq timesOp_Rep_bounded timesOp_def) 

lemma times_adjoint[simp]: "(A \<circ>\<^sub>C B)* =  (B*) \<circ>\<^sub>C (A*)"
  using timesOp_Rep_bounded 
  by (smt adjoint_D adjoint_I comp_apply)

lift_definition applyOpSpace::\<open>('a::chilbert_space,'b::chilbert_space) bounded
\<Rightarrow> 'a linear_space \<Rightarrow> 'b linear_space\<close> 
 (infixl "\<down>" 55)
  is "\<lambda>A S. closure (A ` S)"
  using  bounded_clinear_def is_subspace.subspace
  by (metis closed_closure is_linear_manifold_image is_subspace.intro is_subspace_cl) 

lemma applyOp_0[simp]: "U \<down> 0 = 0" 
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
  \<open>(A \<circ>\<^sub>C B) \<down> \<psi> =  A  \<down>  (B  \<down>  \<psi>)\<close>
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


lemmas assoc_left = timesOp_assoc[symmetric] timesOp_assoc_linear_space[symmetric] add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded", symmetric]
lemmas assoc_right = timesOp_assoc timesOp_assoc_linear_space add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded"]

lemma scalar_times_op_add[simp]: "a *\<^sub>C (A+B) = a *\<^sub>C A + a *\<^sub>C B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  by (simp add: scaleC_add_right)

lemma scalar_times_op_minus[simp]: "a *\<^sub>C (A-B) =  a *\<^sub>C A - a *\<^sub>C B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  by (simp add: complex_vector.scale_right_diff_distrib)


lemma applyOp_bot[simp]: "U \<down> bot = bot"
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


lemma equal_span_0_n:
  fixes f::\<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close> and S::\<open>'a set\<close>
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
          unfolding cgenerator_def top_linear_space_def Complex_Inner_Product.span_def
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

lemma cdot_plus_distrib_transfer:
  \<open>bounded_clinear U \<Longrightarrow>
       is_subspace A \<Longrightarrow>
       is_subspace B \<Longrightarrow>
        (closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
  for U::\<open>'a::complex_normed_vector\<Rightarrow>'b::complex_normed_vector\<close> and A B::\<open>'a set\<close>
proof-
  assume \<open>bounded_clinear U\<close> and \<open>is_subspace A\<close> and \<open>is_subspace B\<close> 
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
          using \<open>bounded_clinear U\<close>
          unfolding bounded_clinear_def clinear_def Modules.additive_def
          by auto
        also have \<open>{U \<psi> + U \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} 
            = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}\<close>
          by blast
        finally show ?thesis by blast
      qed
      moreover have \<open>{\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}
           \<subseteq> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
        by (smt Collect_mono_iff closure_subset subsetD)
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
      from  \<open>bounded_clinear U\<close>
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
        using \<open>bounded_clinear U\<close>
        unfolding bounded_clinear_def clinear_def Modules.additive_def
        by auto
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
  fixes A B :: \<open>('a::chilbert_space) linear_space\<close> and U :: "('a,'b::chilbert_space) bounded"
  shows \<open> U \<down> (A + B) = (U \<down> A) + (U \<down> B)\<close>
proof-
  {  have   \<open>
       bounded_clinear U \<Longrightarrow>
       is_subspace A \<Longrightarrow>
       is_subspace B \<Longrightarrow>
       Abs_linear_space
        (closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
       Abs_linear_space
        (closure
          {\<psi> + \<phi> |\<psi> \<phi>.
           \<psi> \<in> Rep_linear_space (Abs_linear_space (closure (U ` A))) \<and>
           \<phi> \<in> Rep_linear_space (Abs_linear_space (closure (U ` B)))})\<close>
      for U::\<open>'a\<Rightarrow>'b\<close> and A B::\<open>'a set\<close>
    proof-
      assume \<open>bounded_clinear U\<close> and \<open>is_subspace A\<close> and \<open>is_subspace B\<close> 
      hence \<open>(closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
        (closure {\<psi> + \<phi> |\<psi> \<phi>.
           \<psi> \<in> closure (U ` A) \<and>
           \<phi> \<in> closure (U ` B)})\<close>
        using cdot_plus_distrib_transfer by blast
      hence \<open>Abs_linear_space (closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
        Abs_linear_space (closure {\<psi> + \<phi> |\<psi> \<phi>.
           \<psi> \<in> closure (U ` A) \<and>
           \<phi> \<in> closure (U ` B)})\<close>
        by simp
      thus ?thesis using Abs_linear_space_inverse
        by (smt Collect_cong Rep_bounded_cases Rep_linear_space \<open>bounded_clinear U\<close> \<open>is_subspace A\<close> \<open>is_subspace B\<close> applyOpSpace.rep_eq mem_Collect_eq)
    qed    
  } note 1 = this

  show ?thesis 
    unfolding plus_bounded_def applyOpSpace_def apply auto apply transfer 
    unfolding closed_sum_def Minkoswki_sum_def
    apply auto
    unfolding plus_linear_space_def closed_sum_def Minkoswki_sum_def
    apply auto
    apply (rule 1) 
    by blast
qed

lemma scalar_op_linear_space_assoc [simp]: 
  fixes A::\<open>('a::chilbert_space,'b::chilbert_space) bounded\<close>
    and S::\<open>'a linear_space\<close> and \<alpha>::complex
  shows \<open>(\<alpha> *\<^sub>C A) \<down> S  = \<alpha> *\<^sub>C (A \<down> S)\<close>
proof-
  have \<open>closure ( ( ((*\<^sub>C) \<alpha>) \<circ> (Rep_bounded A) ) ` Rep_linear_space S) =
   ((*\<^sub>C) \<alpha>) ` (closure (Rep_bounded A ` Rep_linear_space S))\<close>
    by (metis closure_scaleC image_comp)    
  hence \<open>(closure (Rep_bounded (\<alpha> *\<^sub>C A) ` Rep_linear_space S)) =
   ((*\<^sub>C) \<alpha>) ` (closure (Rep_bounded A ` Rep_linear_space S))\<close>
    by (metis (no_types, lifting) comp_apply image_cong scaleC_bounded_lift)    
  hence \<open>Abs_linear_space
     (closure (Rep_bounded (\<alpha> *\<^sub>C A) ` Rep_linear_space S)) =
    \<alpha> *\<^sub>C
    Abs_linear_space (closure (Rep_bounded A ` Rep_linear_space S))\<close>
    by (metis Rep_linear_space_inverse applyOpSpace.rep_eq scaleC_linear_space.rep_eq)    
  show ?thesis 
    unfolding applyOpSpace_def apply auto
    using \<open>Abs_linear_space
     (closure (Rep_bounded (\<alpha> *\<^sub>C A) ` Rep_linear_space S)) =
    \<alpha> *\<^sub>C Abs_linear_space (closure (Rep_bounded A ` Rep_linear_space S))\<close>
    by blast
qed

lemma applyOpSpace_id[simp]: "idOp \<down> \<psi> = \<psi>"
proof-
  have \<open>is_subspace ( Rep_linear_space \<psi>)\<close>
    using Rep_linear_space by blast    
  hence \<open>closed ( Rep_linear_space \<psi>)\<close>
    unfolding is_subspace_def by blast
  hence \<open>closure ( Rep_linear_space \<psi>) = Rep_linear_space \<psi>\<close>
    by simp    
  hence \<open>(closure ( id ` Rep_linear_space \<psi>)) = Rep_linear_space \<psi>\<close>
    by simp    
  hence \<open>(closure (Rep_bounded (Abs_bounded id) ` Rep_linear_space \<psi>)) = Rep_linear_space \<psi>\<close>
    by (metis idOp.abs_eq idOp.rep_eq)    
  hence \<open>Abs_linear_space
     (closure (Rep_bounded (Abs_bounded id) ` Rep_linear_space \<psi>)) = \<psi>\<close>
    by (simp add: Rep_linear_space_inverse)    
  show ?thesis
    unfolding applyOpSpace_def idOp_def
    apply auto
    using  \<open>Abs_linear_space
     (closure (Rep_bounded (Abs_bounded id) ` Rep_linear_space \<psi>)) = \<psi>\<close>
    by blast
qed

lemma rtimesOp_scaleC:
  fixes f::"('b::chilbert_space,'c::chilbert_space) rbounded" 
    and g::"('a::chilbert_space, 'b::chilbert_space) rbounded"
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded f (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded f x)\<close>
    and \<open>\<forall> c. \<forall> x. Rep_rbounded g (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded g x)\<close>
  shows \<open>\<forall> c. \<forall> x. Rep_rbounded (f \<circ>\<^sub>R g) (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded (f  \<circ>\<^sub>R g) x)\<close>
  by (simp add: assms(1) assms(2) rtimesOp.rep_eq)

lemma rscalar_op_op: 
  fixes A::"('b::chilbert_space,'c::chilbert_space) rbounded" 
    and B::"('a::chilbert_space, 'b::chilbert_space) rbounded"
  shows \<open>(a *\<^sub>C A) \<circ>\<^sub>R B = a *\<^sub>C (A \<circ>\<^sub>R B)\<close>
proof-
  have \<open>(Rep_rbounded (a *\<^sub>C A) \<circ> Rep_rbounded B) x =
    Rep_rbounded (a *\<^sub>C Abs_rbounded (Rep_rbounded A \<circ> Rep_rbounded B)) x\<close>
    for x
  proof-
    have \<open>(Rep_rbounded (a *\<^sub>C A) \<circ> Rep_rbounded B) x
       = a *\<^sub>C (Rep_rbounded A ((Rep_rbounded B) x))\<close>
      by (simp add: scaleC_rbounded.rep_eq)
    moreover have \<open>Rep_rbounded (a *\<^sub>C Abs_rbounded (Rep_rbounded A \<circ> Rep_rbounded B)) x
        = a *\<^sub>C (Rep_rbounded ( Abs_rbounded (Rep_rbounded A \<circ> Rep_rbounded B)) x)\<close>
      by (simp add: scaleC_rbounded.rep_eq)
    moreover have \<open>(Rep_rbounded A ((Rep_rbounded B) x))
        = (Rep_rbounded ( Abs_rbounded (Rep_rbounded A \<circ> Rep_rbounded B)) x)\<close>
    proof-
      have \<open>Rep_rbounded A ((Rep_rbounded B) x) = ((Rep_rbounded A \<circ> Rep_rbounded B)) x\<close>
        by simp        
      thus ?thesis
        using Abs_rbounded_inverse
        by (metis Rep_rbounded rtimesOp.rep_eq)
    qed
    ultimately show ?thesis by simp
  qed
  hence \<open>(Rep_rbounded (a *\<^sub>C A) \<circ> Rep_rbounded B) =
    Rep_rbounded (a *\<^sub>C Abs_rbounded (Rep_rbounded A \<circ> Rep_rbounded B))\<close>
    by blast
  hence \<open>Abs_rbounded (Rep_rbounded (a *\<^sub>C A) \<circ> Rep_rbounded B) =
    a *\<^sub>C Abs_rbounded (Rep_rbounded A \<circ> Rep_rbounded B)\<close>
    by (simp add: Rep_rbounded_inverse)    
  thus ?thesis
    unfolding  rtimesOp_def
    by auto
qed

lemma scalar_op_op[simp]:
  fixes A::"('b::chilbert_space,'c::chilbert_space) bounded" 
    and B::"('a::chilbert_space, 'b::chilbert_space) bounded"
  shows \<open>(a *\<^sub>C A) \<circ>\<^sub>C B = a *\<^sub>C (A \<circ>\<^sub>C B)\<close>
proof-
  have \<open>(rtimesOp (a *\<^sub>C (rbounded_of_bounded A))
       (rbounded_of_bounded B)) =
   ( a *\<^sub>C  (rtimesOp (rbounded_of_bounded A) (rbounded_of_bounded B)) )\<close>
    by (simp add: rscalar_op_op)
  hence \<open>(rtimesOp (rbounded_of_bounded (a *\<^sub>C A))
       (rbounded_of_bounded B)) =
   ( a *\<^sub>C  (rtimesOp (rbounded_of_bounded A) (rbounded_of_bounded B)) )\<close>
    by (simp add: rbounded_of_bounded_scaleC)    
  hence \<open>bounded_of_rbounded
     (rtimesOp (rbounded_of_bounded (a *\<^sub>C A))
       (rbounded_of_bounded B)) =
    bounded_of_rbounded
   ( a *\<^sub>C  (rtimesOp (rbounded_of_bounded A) (rbounded_of_bounded B)) )\<close>
    by simp    
  hence \<open>bounded_of_rbounded
     (rtimesOp (rbounded_of_bounded (a *\<^sub>C A))
       (rbounded_of_bounded B)) =
    a *\<^sub>C bounded_of_rbounded
     (rtimesOp (rbounded_of_bounded A) (rbounded_of_bounded B))\<close>
    by (simp add: bounded_of_rbounded_scaleC rbounded_of_bounded_prelim rtimesOp_scaleC)  
  thus ?thesis
    unfolding timesOp_def 
    by blast
qed

lemma op_rscalar_op: 
  fixes A::"('b::chilbert_space,'c::chilbert_space) rbounded" 
    and B::"('a::chilbert_space, 'b::chilbert_space) rbounded"
  assumes \<open>\<forall> c. \<forall> x. Rep_rbounded A (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded A x)\<close>
  shows \<open>A \<circ>\<^sub>R (a *\<^sub>C B) = a *\<^sub>C (A \<circ>\<^sub>R B)\<close>
proof-
  have \<open>Rep_rbounded (rtimesOp A (a *\<^sub>C B)) x  = Rep_rbounded (rtimesOp (a *\<^sub>C A) B) x\<close>
    for x
  proof-
    have \<open>Rep_rbounded (rtimesOp A (a *\<^sub>C B)) x
        = ( (Rep_rbounded A) \<circ> (Rep_rbounded (a *\<^sub>C B)) ) x\<close>
      by (simp add: rtimesOp.rep_eq)
    also have \<open>... = 
        (Rep_rbounded A) ( (Rep_rbounded (a *\<^sub>C B))  x )\<close>
      by simp
    also have \<open>... = 
        (Rep_rbounded A) (a *\<^sub>C ( (Rep_rbounded  B) x ))\<close>
      by (simp add: scaleC_rbounded.rep_eq)
    also have \<open>... = 
       a *\<^sub>C ( (Rep_rbounded A) ( (Rep_rbounded  B) x ) )\<close>
      using assms by auto      
    finally show ?thesis
      by (simp add: rtimesOp.rep_eq scaleC_rbounded.rep_eq) 
  qed
  hence \<open>Rep_rbounded (rtimesOp A (a *\<^sub>C B))  = Rep_rbounded (rtimesOp (a *\<^sub>C A) B)\<close>
    by blast     
  hence \<open>rtimesOp A (a *\<^sub>C B) = rtimesOp (a *\<^sub>C A) B\<close>
    using Rep_rbounded_inject by auto    
  thus ?thesis
    by (simp add: rscalar_op_op)  
qed

lemma op_scalar_op[simp]:
  fixes A::"('b::chilbert_space,'c::chilbert_space) bounded" 
    and B::"('a::chilbert_space, 'b::chilbert_space) bounded"
  shows \<open>A \<circ>\<^sub>C (a *\<^sub>C B) = a *\<^sub>C (A \<circ>\<^sub>C B)\<close>
  using op_rscalar_op
  by (metis (no_types, lifting) rbounded_of_bounded_prelim rbounded_of_bounded_scaleC rscalar_op_op scalar_op_op timesOp_def)

lemma times_idOp1[simp]: "U  \<circ>\<^sub>C idOp = U"
  by (metis Rep_bounded_inverse comp_id idOp.rep_eq timesOp_Rep_bounded)

lemma times_idOp2[simp]: "idOp \<circ>\<^sub>C U  = U"
  by (metis Rep_bounded_inject idOp.rep_eq id_comp timesOp_Rep_bounded)

lemma mult_INF1[simp]:
  fixes U :: "('b::chilbert_space,'c::chilbert_space) bounded"
    and V :: "'a \<Rightarrow> 'b linear_space" 
  shows \<open>U \<down> (INF i. V i) \<le> (INF i. U \<down> (V i))\<close>
proof-
  have \<open>bounded_clinear U \<Longrightarrow>
       \<forall>j. is_subspace (V j) \<Longrightarrow> closure (U ` \<Inter> (range V)) \<subseteq> closure (U ` V i)\<close>
    for U::\<open>'b\<Rightarrow>'c\<close> and V::\<open>'a \<Rightarrow> 'b set\<close> and x::'c and i::'a
  proof-
    assume \<open>bounded_clinear U\<close> and \<open>\<forall>j. is_subspace (V j)\<close> 
    have \<open>U ` \<Inter> (range V) \<subseteq> U ` (V i)\<close>
      by (simp add: Inter_lower image_mono)    
    thus ?thesis
      by (simp add: closure_mono) 
  qed
  thus ?thesis
    apply transfer
    by auto
qed

lemma mult_inf_distrib[simp]: 
  fixes U::\<open>('a::chilbert_space,'b::chilbert_space) bounded\<close> and B C::"'a linear_space"
  shows "(applyOpSpace U) (B * C) \<le> ((applyOpSpace U) B) *  ((applyOpSpace U) C)"
proof-
  have \<open>bounded_clinear U \<Longrightarrow>
       is_subspace B \<Longrightarrow>
       is_subspace C \<Longrightarrow>
       closure (U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
    for U::\<open>'a\<Rightarrow>'b\<close> and B C::\<open>'a set\<close>
  proof-
    assume \<open>bounded_clinear U\<close> and \<open>is_subspace B\<close> and \<open>is_subspace C\<close>
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
       bounded_clinear U \<Longrightarrow>
       is_subspace B \<Longrightarrow>
       is_subspace C \<Longrightarrow>
       closure (U ` (B \<inter> C))
       \<subseteq> closure (U ` B) \<inter> closure (U ` C)\<close>
    by blast
qed

(*
lemma applyOpSpace_eq:
  fixes S :: "'a::chilbert_space linear_space" 
    and A B :: "('a::chilbert_space,'b::chilbert_space) bounded"
  assumes "\<And>x. x \<in> G \<Longrightarrow> Rep_bounded A x = Rep_bounded B x"
  assumes "span G \<ge> S"
  shows "A \<down> S = B \<down> S"
  using assms
  sorry
*)

(* NEW *)
section \<open>Endomorphism algebra\<close>

(* https://en.wikipedia.org/wiki/Endomorphism_ring  *)
typedef (overloaded) ('a::complex_normed_vector) endo 
= \<open>{f :: 'a\<Rightarrow>'a. bounded_clinear f}\<close>
  using bounded_clinear_ident by blast

definition bounded_of_endo:: \<open>'a::chilbert_space endo \<Rightarrow> ('a, 'a) bounded\<close>  where 
\<open>bounded_of_endo f = Abs_bounded (Rep_endo f)\<close>

definition endo_of_bounded:: \<open>('a::chilbert_space, 'a) bounded \<Rightarrow> 'a endo\<close>  where 
\<open>endo_of_bounded f = Abs_endo (Rep_bounded f)\<close>

lemma endo_of_bounded_inj:
\<open>endo_of_bounded f = endo_of_bounded g \<Longrightarrow> f = g\<close>
  by (metis Abs_endo_inject endo_of_bounded_def Rep_bounded Rep_bounded_inject)

lemma bounded_of_endo_inj:
\<open>bounded_of_endo f = bounded_of_endo g \<Longrightarrow> f = g\<close>
  by (metis Abs_bounded_inject Rep_endo Rep_endo_inject bounded_of_endo_def)

lemma endo_of_bounded_inv:
\<open>bounded_of_endo (endo_of_bounded f) = f\<close>
  by (metis Abs_endo_inverse endo_of_bounded_def Rep_bounded Rep_bounded_inverse bounded_of_endo_def)

lemma bounded_of_endo_inv:
\<open>endo_of_bounded (bounded_of_endo f) = f\<close>
  using endo_of_bounded_inv bounded_of_endo_inj by auto

instantiation endo :: (chilbert_space) \<open>complex_normed_vector\<close>
begin

definition zero_endo::"'a endo" 
  where "zero_endo = endo_of_bounded (0::('a,'a) bounded)"

definition plus_endo::"'a endo \<Rightarrow> 'a endo \<Rightarrow> 'a endo" 
  where "plus_endo f g =  endo_of_bounded ( (bounded_of_endo f)+(bounded_of_endo g) )"

definition uminus_endo::"'a endo \<Rightarrow> 'a endo" 
  where "uminus_endo f =  endo_of_bounded (- (bounded_of_endo f))"

definition minus_endo::"'a endo \<Rightarrow> 'a endo \<Rightarrow> 'a endo" 
  where "minus_endo f g =  endo_of_bounded ( (bounded_of_endo f)-(bounded_of_endo g) )"

definition scaleC_endo :: \<open>complex \<Rightarrow> 'a endo \<Rightarrow> 'a endo\<close>
  where "scaleC_endo c f =  endo_of_bounded ( c *\<^sub>C (bounded_of_endo f) )"

definition scaleR_endo :: \<open>real \<Rightarrow> 'a endo \<Rightarrow> 'a endo\<close>
  where "scaleR_endo c f =  endo_of_bounded ( c *\<^sub>R (bounded_of_endo f) )"

definition norm_endo :: \<open>'a endo \<Rightarrow> real\<close>
  where \<open>norm_endo f = norm (bounded_of_endo f)\<close>

definition dist_endo :: \<open>'a endo \<Rightarrow> 'a endo \<Rightarrow> real\<close>
  where \<open>dist_endo f g = dist (bounded_of_endo f) (bounded_of_endo g)\<close>

definition sgn_endo :: \<open>'a endo \<Rightarrow> 'a endo\<close>
  where \<open>sgn_endo f =  endo_of_bounded ( sgn (bounded_of_endo f))\<close>

definition uniformity_endo :: \<open>( 'a  endo \<times> 'a endo ) filter\<close>
  where \<open>uniformity_endo = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a endo) y < e})\<close>

definition open_endo :: \<open>('a endo) set \<Rightarrow> bool\<close>
  where \<open>open_endo U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a endo) = x \<longrightarrow> y \<in> U)\<close>

instance
  proof
  show \<open>((*\<^sub>R) r::'a endo \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
    for r :: real
    unfolding scaleR_endo_def scaleC_endo_def
    by (simp add: scaleR_scaleC)
    
  show "(a::'a endo) + b + c = a + (b + c)"
    for a :: "'a endo"
      and b :: "'a endo"
      and c :: "'a endo"
    by (simp add: endo_of_bounded_inv ab_semigroup_add_class.add_ac(1) plus_endo_def)


  show "(a::'a endo) + b = b + a"
    for a :: "'a endo"
      and b :: "'a endo"
    by (simp add: add.commute plus_endo_def)
    
  show "(0::'a endo) + a = a"
    for a :: "'a endo"
    by (simp add: endo_of_bounded_inv Bounded_Operators.plus_endo_def Bounded_Operators.zero_endo_def bounded_of_endo_inv)
    
  show "- (a::'a endo) + a = 0"
    for a :: "'a endo"
    by (simp add: endo_of_bounded_inv plus_endo_def uminus_endo_def zero_endo_def)

  show "(a::'a endo) - b = a + - b"
    for a :: "'a endo"
      and b :: "'a endo"
    by (metis (full_types) endo_of_bounded_inv ab_group_add_class.ab_diff_conv_add_uminus minus_endo_def plus_endo_def uminus_endo_def)
    
  show \<open>a *\<^sub>C ((x::'a endo) + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    for a :: complex
      and x :: "'a endo"
      and y :: "'a endo"
    by (simp add: endo_of_bounded_inv plus_endo_def scaleC_endo_def scaleC_add_right)

  show "(a + b) *\<^sub>C (x::'a endo) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a endo"
    by (simp add: endo_of_bounded_inv Bounded_Operators.plus_endo_def Bounded_Operators.scaleC_endo_def scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::'a endo) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a endo"
    by (simp add: endo_of_bounded_inv scaleC_endo_def)

  show "1 *\<^sub>C (x::'a endo) = x"
    for x :: "'a endo"
    by (simp add: bounded_of_endo_inv scaleC_endo_def)    

  show "dist (x::'a endo) y = norm (x - y)"
    for x :: "'a endo"
      and y :: "'a endo"
    by (simp add: endo_of_bounded_inv Bounded_Operators.minus_endo_def Bounded_Operators.norm_endo_def dist_endo_def dist_norm)

  show "a *\<^sub>R ((x::'a endo) + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real
      and x :: "'a endo"
      and y :: "'a endo"
    using \<open>\<And>r. ((*\<^sub>R) r::'a endo \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
      \<open>\<And> y x a. a *\<^sub>C ((x::'a endo) + y) = a *\<^sub>C x + a *\<^sub>C y\<close>
    by fastforce

  show "(a + b) *\<^sub>R (x::'a endo) = a *\<^sub>R x + b *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a endo"
    using  \<open>\<And>r. ((*\<^sub>R) r::'a endo \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
      \<open>\<And> a b x. (a + b) *\<^sub>C (x::'a endo) = a *\<^sub>C x + b *\<^sub>C x\<close>
    by fastforce

  show "a *\<^sub>R b *\<^sub>R (x::'a endo) = (a * b) *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a endo"
    using  \<open>\<And>r. ((*\<^sub>R) r::'a endo \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
      \<open>\<And> a b x. a *\<^sub>C b *\<^sub>C (x::'a endo) = (a * b) *\<^sub>C x\<close>
    by fastforce

  show "1 *\<^sub>R (x::'a endo) = x"
    for x :: "'a endo"
    using  \<open>\<And>r. ((*\<^sub>R) r::'a endo \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)\<close>
        \<open>1 *\<^sub>C (x::'a endo) = x\<close>
    by fastforce

  show "sgn (x::'a endo) = inverse (norm x) *\<^sub>R x"
    for x :: "'a endo"
    by (simp add: Bounded_Operators.norm_endo_def Bounded_Operators.scaleR_endo_def Bounded_Operators.sgn_endo_def sgn_div_norm)
    
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a endo) y < e})"
    using Bounded_Operators.uniformity_endo_def by auto    

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a endo) = x \<longrightarrow> y \<in> U)"
    for U :: "'a endo set"
    using Bounded_Operators.open_endo_def by auto    

  show "(norm (x::'a endo) = 0) = (x = 0)"
    for x :: "'a endo"
  proof -
    have f1: "\<not> (0::real) < 0"
      by (metis norm_zero zero_less_norm_iff)
    have "bounded_of_endo x = 0 \<longrightarrow> norm (bounded_of_endo x) = 0"
      by auto
    then show ?thesis
      using f1 by (metis (mono_tags) endo_of_bounded_inv Bounded_Operators.zero_endo_def bounded_of_endo_inv norm_endo_def zero_less_norm_iff)
  qed

  show "norm ((x::'a endo) + y) \<le> norm x + norm y"
    for x :: "'a endo"
      and y :: "'a endo"
    by (simp add: endo_of_bounded_inv norm_endo_def norm_triangle_ineq plus_endo_def)
    
  show "norm (a *\<^sub>R (x::'a endo)) = \<bar>a\<bar> * norm x"
    for a :: real
      and x :: "'a endo"
    by (simp add: endo_of_bounded_inv norm_endo_def scaleR_endo_def)
    
  show "norm (a *\<^sub>C (x::'a endo)) = cmod a * norm x"
    for a :: complex
      and x :: "'a endo"
    by (simp add: endo_of_bounded_inv norm_endo_def scaleC_endo_def)
    
qed

end

instantiation endo :: (chilbert_space) \<open>cbanach\<close>
begin

lemma bounded_of_endo_Cauchy:
  \<open>Cauchy f \<Longrightarrow> Cauchy (\<lambda> n. bounded_of_endo (f n))\<close>
  unfolding Cauchy_def dist_endo_def by blast

lemma endo_of_bounded_tendsto:
  \<open>f \<longlonglongrightarrow> l \<Longrightarrow> (\<lambda> n. endo_of_bounded (f n)) \<longlonglongrightarrow> endo_of_bounded l\<close>
proof-
  assume \<open>f \<longlonglongrightarrow> l\<close>
  hence \<open>N\<in>HNatInfinite \<Longrightarrow> (*f* f) N \<approx> star_of l\<close>
    for N
    by (simp add: LIMSEQ_NSLIMSEQ NSLIMSEQ_D)
  hence \<open>N\<in>HNatInfinite \<Longrightarrow> hnorm ((*f* f) N - star_of l) \<in> Infinitesimal\<close>
    for N
    using Infinitesimal_hnorm_iff bex_Infinitesimal_iff by auto
  moreover have \<open>hnorm ((*f* f) N - star_of l) =
     hnorm ( (*f* (\<lambda> n. endo_of_bounded (f n))) N - star_of (endo_of_bounded l) ) \<close>
    for N
  proof-
    have \<open>\<forall> N. norm (f N -  l) =
     norm (  (\<lambda> n. endo_of_bounded (f n)) N -  (endo_of_bounded l) )\<close>
      unfolding norm_endo_def
      by (simp add: endo_of_bounded_inv minus_endo_def)
    hence \<open>\<forall> N. hnorm ((*f* f) N - star_of l) =
     hnorm ( (*f* (\<lambda> n. endo_of_bounded (f n))) N - star_of (endo_of_bounded l) )\<close>
      by StarDef.transfer
    thus ?thesis by blast
  qed
  ultimately have  \<open>N\<in>HNatInfinite \<Longrightarrow>
   hnorm ( (*f* (\<lambda> n. endo_of_bounded (f n))) N - star_of (endo_of_bounded l) ) \<in> Infinitesimal\<close>
    for N
    by simp    
  hence \<open>N\<in>HNatInfinite \<Longrightarrow> (*f* (\<lambda> n. endo_of_bounded (f n))) N \<approx> star_of  (endo_of_bounded l)\<close>
    for N
    by (simp add: Infinitesimal_approx_minus Infinitesimal_hnorm_iff)    
  hence \<open>(\<lambda> n. endo_of_bounded (f n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S endo_of_bounded l\<close>
    by (simp add: NSLIMSEQ_I)    
  thus ?thesis
    by (simp add: NSLIMSEQ_LIMSEQ)
qed

instance
  proof
  show "convergent (X::nat \<Rightarrow> 'a endo)"
    if "Cauchy (X::nat \<Rightarrow> 'a endo)"
    for X :: "nat \<Rightarrow> 'a endo"
  proof-
    have \<open>Cauchy (\<lambda> n. bounded_of_endo (X n))\<close>
      using that
      by (simp add: bounded_of_endo_Cauchy) 
    hence \<open>convergent (\<lambda> n. bounded_of_endo (X n))\<close>
      by (simp add: Cauchy_convergent)
    then obtain l where \<open>(\<lambda> n. bounded_of_endo (X n)) \<longlonglongrightarrow> l\<close>
      unfolding convergent_def by blast
    hence \<open>(\<lambda> n. endo_of_bounded ( (\<lambda> m. bounded_of_endo (X m)) n) )
             \<longlonglongrightarrow> endo_of_bounded l\<close>
      using endo_of_bounded_tendsto
      by (simp add: endo_of_bounded_tendsto)
    moreover have \<open>endo_of_bounded ( (\<lambda> m. bounded_of_endo (X m)) n) = X n\<close>
      for n
      by (simp add: bounded_of_endo_inv)      
    ultimately show ?thesis
      by (simp add: convergentI) 
  qed
qed
end

instantiation endo::(chilbert_space) \<open>ring\<close>
begin
definition times_endo::\<open>'a endo \<Rightarrow> 'a endo \<Rightarrow> 'a endo\<close> where
\<open>times_endo A B = endo_of_bounded ((bounded_of_endo A) \<circ>\<^sub>C (bounded_of_endo B))\<close>
instance
  proof
  show "(a::'a endo) * b * c = a * (b * c)"
    for a :: "'a endo"
      and b :: "'a endo"
      and c :: "'a endo"
    by (simp add: endo_of_bounded_inv Bounded_Operators.times_endo_def timesOp_assoc)
    
  show "((a::'a endo) + b) * c = a * c + b * c"
    for a :: "'a endo"
      and b :: "'a endo"
      and c :: "'a endo"
    by (simp add: endo_of_bounded_inv plus_endo_def timesOp_dist1 times_endo_def)
    
  show "(a::'a endo) * (b + c) = a * b + a * c"
    for a :: "'a endo"
      and b :: "'a endo"
      and c :: "'a endo"
        by (simp add: endo_of_bounded_inv plus_endo_def timesOp_dist2 times_endo_def)
qed
end


instantiation endo::("{chilbert_space, perfect_space}") \<open>ring_1\<close>
begin
definition one_endo::\<open>'a endo\<close> where
  \<open>one_endo = endo_of_bounded idOp\<close>

instance
  proof
  show "(1::'a endo) * a = a"
    for a :: "'a endo"
    unfolding one_endo_def times_endo_def
    by (simp add: endo_of_bounded_inv bounded_of_endo_inj)
    
  show "(a::'a endo) * 1 = a"
    for a :: "'a endo"
    unfolding one_endo_def times_endo_def
    by (simp add: endo_of_bounded_inv bounded_of_endo_inj)

  show "(0::'a::{chilbert_space, perfect_space} endo) \<noteq> 1"
  proof-
    have \<open>(0::('a,'a) bounded) \<noteq> idOp\<close>
    proof-
      have \<open>\<exists> x::'a. x \<noteq> 0\<close>
        using UNIV_not_singleton
        by auto
      then obtain x::'a where \<open>x \<noteq> 0\<close>
        by blast
      moreover have \<open>Rep_bounded ((0::('a,'a) bounded)) x = 0\<close>
        by (simp add: zero_bounded_lift)        
      moreover have \<open>Rep_bounded (idOp) x = x\<close>
        by (simp add: idOp.rep_eq)       
      ultimately have \<open>Rep_bounded ((0::('a,'a) bounded)) \<noteq> Rep_bounded (idOp)\<close>
        by auto        
      thus ?thesis using Rep_bounded_inject
        by (simp add: Rep_bounded_inject)
    qed
    thus ?thesis
      unfolding one_endo_def zero_endo_def
      using endo_of_bounded_inj by blast
  qed
qed

end

definition Adj_endo :: "'a::chilbert_space endo \<Rightarrow> 'a endo"  ("_\<^sup>a\<^sup>d\<^sup>j" [99] 100)  where
\<open>Adj_endo A = endo_of_bounded ( (bounded_of_endo A)* )\<close>

lemma Adj_endo_times[simp]:
\<open>(A * B)\<^sup>a\<^sup>d\<^sup>j = (B\<^sup>a\<^sup>d\<^sup>j) * (A\<^sup>a\<^sup>d\<^sup>j)\<close>
  unfolding Adj_endo_def times_endo_def
  by (simp add: endo_of_bounded_inv)

lemma Adj_endo_twices[simp]:
\<open>(A\<^sup>a\<^sup>d\<^sup>j)\<^sup>a\<^sup>d\<^sup>j = A\<close>
  unfolding Adj_endo_def
  by (simp add: bounded_of_endo_inj endo_of_bounded_inv)

lemma Adj_endo_scaleC[simp]:
\<open>(c *\<^sub>C A)\<^sup>a\<^sup>d\<^sup>j = (cnj c) *\<^sub>C (A\<^sup>a\<^sup>d\<^sup>j)\<close>
  by (simp add: Adj_endo_def endo_of_bounded_inv scaleC_endo_def)

lemma Adj_endo_plus[simp]:
\<open>(A + B)\<^sup>a\<^sup>d\<^sup>j = (A\<^sup>a\<^sup>d\<^sup>j) + (B\<^sup>a\<^sup>d\<^sup>j)\<close>
  unfolding Adj_endo_def plus_endo_def
  using Adj_bounded_plus
  by (simp add: Adj_bounded_plus endo_of_bounded_inv)

lemma Adj_endo_uminus[simp]:
\<open>(- A)\<^sup>a\<^sup>d\<^sup>j = - (A\<^sup>a\<^sup>d\<^sup>j)\<close>
  by (metis Adj_endo_plus add.group_axioms add.left_inverse add_cancel_right_left group.right_cancel)

lemma Adj_endo_minus[simp]:
\<open>(A - B)\<^sup>a\<^sup>d\<^sup>j = (A\<^sup>a\<^sup>d\<^sup>j) - (B\<^sup>a\<^sup>d\<^sup>j)\<close>
  by (simp add: additive.diff additive.intro)

lemma Adj_endo_zero[simp]:
\<open>0\<^sup>a\<^sup>d\<^sup>j = 0\<close>
  by (metis Adj_endo_plus Adj_endo_uminus add.right_inverse)

lemma Adj_endo_unit[simp]:
\<open>1\<^sup>a\<^sup>d\<^sup>j = 1\<close>
  by (metis (no_types, lifting) Adj_endo_times Adj_endo_twices Adj_endo_uminus add.inverse_inverse mult_minus1_right)

section \<open>Unitary\<close>

definition isometry::\<open>('a::chilbert_space,'b::chilbert_space) bounded \<Rightarrow> bool\<close> where
\<open>isometry U = ( (U*) \<circ>\<^sub>C  U  = idOp )\<close>

definition unitary::\<open>('a::chilbert_space,'a) bounded \<Rightarrow> bool\<close> where
\<open>unitary U = ( isometry U \<and> isometry (U*))\<close>


lemma adjUU[simp]: "isometry U \<Longrightarrow> U* \<circ>\<^sub>C U = idOp" 
  unfolding isometry_def 
  by simp

lemma UadjU[simp]: "unitary U \<Longrightarrow> U \<circ>\<^sub>C U* = idOp"
  unfolding unitary_def isometry_def by simp


lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

lemma unitary_adjoint[simp]: "unitary (U*) = unitary U" for U::"(_,_)bounded"
  unfolding unitary_def by auto

lemma isometry_times[simp]: "isometry A \<Longrightarrow> isometry B \<Longrightarrow> isometry (A \<circ>\<^sub>C B)"
  unfolding isometry_def apply simp
  apply (subst timesOp_assoc[symmetric])  
  apply (subst timesOp_assoc)  
  by simp

lemma unitary_times[simp]: "unitary A \<Longrightarrow> unitary B \<Longrightarrow> unitary (A \<circ>\<^sub>C B)"
  unfolding unitary_def by simp

lemma unitary_surj: "unitary U \<Longrightarrow> surj (Rep_bounded U)"
proof-
  assume \<open>unitary U\<close>
  have \<open>\<exists> t. (Rep_bounded U) t = x\<close>
    for x
  proof-
    have \<open>(Rep_bounded U) ((Rep_bounded (U*)) x) = x\<close>
    proof-
      have \<open>(Rep_bounded U) ((Rep_bounded (U*)) x)
          = ((Rep_bounded U) \<circ> (Rep_bounded (U*))) x\<close>
        by simp        
      also have \<open>\<dots>
          = (Rep_bounded ( U \<circ>\<^sub>C (U*) )) x\<close>
        by (simp add: timesOp_Rep_bounded)
      also have \<open>\<dots>
          = (Rep_bounded ( idOp )) x\<close>
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

lemma unitary_image[simp]: "unitary U \<Longrightarrow> U \<down> top = top"
proof-
  assume \<open>unitary U\<close>
  hence \<open>surj (Rep_bounded U)\<close>
    using unitary_surj by blast
  hence \<open>range (Rep_bounded U)  = UNIV\<close>
    by simp
  hence \<open>closure (range (Rep_bounded U))  = UNIV\<close>
    by simp
  thus ?thesis
    apply transfer
    by blast
qed

lemma unitary_id[simp]: "unitary idOp"
  unfolding unitary_def
  by (simp add: isometry_def) 


section \<open>Projectors\<close>

lift_definition Proj :: "('a::chilbert_space) linear_space \<Rightarrow> ('a,'a) bounded"
is \<open>projection\<close>
  by (rule Complex_Inner_Product.projectionPropertiesA)

definition Proj_endo :: "('a::chilbert_space) linear_space \<Rightarrow> 'a endo" 
 ("\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o_" [99] 100)  where
\<open>Proj_endo S = endo_of_bounded (Proj S)\<close>

lemma imageOp_Proj[simp]: "(Proj S) \<down> top = S"
  apply transfer
  proof
  show "closure (range (projection (S::'a set))) \<subseteq> S"
    if "is_subspace (S::'a set)"
    for S :: "'a set"
    using that
    by (metis (full_types) OrthoClosedEq closure_mono image_subsetI is_subspace.subspace is_subspace_I orthogonal_complement_twice projection_intro2) 
  show "(S::'a set) \<subseteq> closure (range (projection S))"
    if "is_subspace (S::'a set)"
    for S :: "'a set"
    using that
    by (metis (no_types, lifting) closure_subset image_subset_iff in_mono projection_fixed_points subsetI subset_UNIV) 
qed

lemma projection_D1:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_subspace M\<close>
  shows \<open>projection M = (projection M)\<^sup>\<dagger>\<close>
proof-
  have \<open>(projection M) x = ((projection M)\<^sup>\<dagger>) x\<close>
    for x
  proof (rule projection_uniq)
    show \<open>is_subspace M\<close>
      by (simp add: assms)
    show \<open>((projection M)\<^sup>\<dagger>) x \<in> M\<close>
    proof-
      have "y \<in> orthogonal_complement M \<Longrightarrow> \<langle> ((projection M)\<^sup>\<dagger>) x, y \<rangle> = 0"
        for y
      proof-
        assume \<open>y \<in> orthogonal_complement M\<close>
        hence \<open>(projection M) y = 0\<close>
          by (metis add_cancel_right_right assms is_subspace_orthog ortho_decomp orthogonal_complement_twice projection_fixed_points)          
        hence \<open>\<langle> x, (projection M) y \<rangle> = 0\<close>
          by simp          
        thus ?thesis
          by (simp add: Adj_I assms projectionPropertiesA) 
      qed
      hence "((projection M)\<^sup>\<dagger>) x \<in> orthogonal_complement (orthogonal_complement M)"
        unfolding orthogonal_complement_def is_orthogonal_def
        by blast
      thus ?thesis
        by (simp add: assms orthogonal_complement_twice) 
    qed
    show \<open>x - ((projection M)\<^sup>\<dagger>) x \<in> orthogonal_complement M\<close>
    proof (rule orthogonal_complement_I2)
      show "\<langle>x - (projection M\<^sup>\<dagger>) x, y\<rangle> = 0"
        if "y \<in> M"
        for y :: 'a
      proof-
        have \<open>y = projection M y\<close>
          using that(1)
          by (simp add: assms projection_fixed_points)
        hence \<open>y - projection M y = 0\<close>
          by simp
        have \<open>\<langle>x - (projection M\<^sup>\<dagger>) x, y\<rangle> = \<langle>x, y\<rangle> - \<langle>(projection M\<^sup>\<dagger>) x, y\<rangle>\<close>
          by (simp add: cinner_diff_left)
        also have \<open>... = \<langle>x, y\<rangle> - \<langle>x, (projection M) y\<rangle>\<close>
          by (simp add: Adj_I assms projectionPropertiesA)
        also have \<open>... = \<langle>x, y - (projection M) y\<rangle>\<close>
          by (simp add: cinner_diff_right)
        also have \<open>... = \<langle>x, 0\<rangle>\<close>
          using  \<open>y - projection M y = 0\<close>
          by simp
        also have \<open>... = 0\<close>
          by simp          
        finally show ?thesis
          by simp 
      qed
    qed
  qed
  thus ?thesis by blast 
qed

lemma Proj_D1:
\<open>(Proj M) = (Proj M)*\<close>
  apply transfer
  by (rule projection_D1)

lemma Proj_endo_D1[simp]:
\<open>(\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M) = (\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M)\<^sup>a\<^sup>d\<^sup>j\<close>
  by (metis Adj_endo_def Proj_D1 Proj_endo_def endo_of_bounded_inv)

lemma Proj_D2[simp]:
\<open>(Proj M) \<circ>\<^sub>C (Proj M) = (Proj M)\<close>
proof-
  have \<open>(Rep_bounded (Proj M)) = projection (Rep_linear_space M)\<close>
    apply transfer
    by blast
  moreover have \<open>(projection (Rep_linear_space M))\<circ>(projection (Rep_linear_space M))
                = (projection (Rep_linear_space M)) \<close>
  proof-
    have \<open>is_subspace (Rep_linear_space M)\<close>
      using Rep_linear_space by auto
    thus ?thesis
      by (simp add: projectionPropertiesC) 
  qed
  ultimately have \<open>(Rep_bounded (Proj M)) \<circ> (Rep_bounded (Proj M)) = Rep_bounded (Proj M)\<close>
    by simp    
  hence \<open>Rep_bounded ((Proj M) \<circ>\<^sub>C (Proj M)) = Rep_bounded (Proj M)\<close>
    by (simp add: timesOp_Rep_bounded)    
  thus ?thesis using Rep_bounded_inject
    by auto 
qed

lemma Proj_endo_D2[simp]:
\<open>(\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M) * (\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M) = (\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M)\<close>
  unfolding Proj_endo_def times_endo_def
  by (simp add: endo_of_bounded_inv)


lemma Proj_I:
\<open>P \<circ>\<^sub>C P = P \<Longrightarrow> P = P* \<Longrightarrow> \<exists> M. P = Proj M \<and> Rep_linear_space M = range (Rep_bounded P)\<close>
  for P :: \<open>('a::chilbert_space,'a) bounded\<close>
proof-
  assume \<open>P \<circ>\<^sub>C P = P\<close> and \<open>P = P*\<close>
  have \<open>closed (range (Rep_bounded P))\<close>
  proof-
    have \<open>range (Rep_bounded P) = (\<lambda> x. x - Rep_bounded P x) -` {0}\<close>
    proof
      show "range (Rep_bounded P) \<subseteq> (\<lambda>x. x - Rep_bounded P x) -` {0}"
      proof
        show "x \<in> (\<lambda>x. x - Rep_bounded P x) -` {0}"
          if "x \<in> range (Rep_bounded P)"
          for x :: 'a
        proof-
          have \<open>\<exists> t. Rep_bounded P t = x\<close>
            using that by blast
          then obtain t where \<open>Rep_bounded P t = x\<close>
            by blast 
          hence \<open>x - Rep_bounded P x = x - Rep_bounded P (Rep_bounded P t)\<close>
            by simp
          also have \<open>\<dots> = x - (Rep_bounded P t)\<close>
          proof-
            have \<open>Rep_bounded P \<circ> Rep_bounded P = Rep_bounded P\<close>
              by (metis \<open>P \<circ>\<^sub>C P = P\<close> timesOp_Rep_bounded)
            thus ?thesis
              by (metis comp_apply) 
          qed
          also have \<open>\<dots> = 0\<close>
            by (simp add: \<open>Rep_bounded P t = x\<close>)
          finally have \<open>x - Rep_bounded P x = 0\<close>
            by blast
          thus ?thesis
            by simp 
        qed
      qed
      show "(\<lambda>x. x - Rep_bounded P x) -` {0} \<subseteq> range (Rep_bounded P)"
      proof
        show "x \<in> range (Rep_bounded P)"
          if "x \<in> (\<lambda>x. x - Rep_bounded P x) -` {0}"
          for x :: 'a
        proof-
          have \<open>x - Rep_bounded P x = 0\<close>
            using that by blast
          hence \<open>x = Rep_bounded P x\<close>
            by (simp add: \<open>x - Rep_bounded P x = 0\<close> eq_iff_diff_eq_0)
          thus ?thesis
            by blast 
        qed
      qed
    qed
    moreover have \<open>closed ( (\<lambda> x. x - Rep_bounded P x) -` {0} )\<close>
    proof-
      have \<open>closed {(0::'a)}\<close>
        by simp        
      moreover have \<open>continuous (at x) (\<lambda> x. x - Rep_bounded P x)\<close>
        for x
      proof-
        have \<open>Rep_bounded (idOp - P) = (\<lambda> x. x - Rep_bounded P x)\<close>
          by (simp add: idOp.rep_eq minus_bounded_lift)          
        hence \<open>bounded_clinear (Rep_bounded (idOp - P))\<close>
          using Rep_bounded
          by blast 
        hence \<open>continuous (at x) (Rep_bounded (idOp - P))\<close>
          by (simp add: bounded_linear_continuous)          
        thus ?thesis
          using \<open>Rep_bounded (idOp - P) = (\<lambda> x. x - Rep_bounded P x)\<close>
          by simp
      qed
      ultimately show ?thesis  
        by (rule Abstract_Topology.continuous_closed_vimage)               
    qed
    ultimately show ?thesis
      by simp  
  qed
  have \<open>bounded_clinear (Rep_bounded P)\<close>
    using Rep_bounded by auto
  hence \<open>is_subspace ( range (Rep_bounded P) )\<close>
    using \<open>closed (range (Rep_bounded P))\<close>
     bounded_clinear.clinear is_linear_manifold_image is_subspace.intro 
      is_subspace.subspace is_subspace_UNIV by blast
  hence \<open>\<exists> M. Rep_linear_space M = (range (Rep_bounded P))\<close>
    using  \<open>closed (range (Rep_bounded P))\<close>
    by (metis applyOpSpace.rep_eq closure_eq top_linear_space.rep_eq)    
  then obtain M where \<open>Rep_linear_space M = (range (Rep_bounded P))\<close>
    by blast
  have \<open>Rep_bounded P x \<in> Rep_linear_space M\<close>
    for x
    by (simp add: \<open>Rep_linear_space M = range (Rep_bounded P)\<close>)
  moreover have \<open>x - Rep_bounded P x \<in> orthogonal_complement ( Rep_linear_space M)\<close>
    for x
  proof-
    have \<open>y \<in> Rep_linear_space M \<Longrightarrow> \<langle> x - Rep_bounded P x, y \<rangle> = 0\<close>
      for y
    proof-
      assume \<open>y \<in> Rep_linear_space M\<close>
      hence \<open>\<exists> t. y = Rep_bounded P t\<close>
        by (simp add: \<open>Rep_linear_space M = range (Rep_bounded P)\<close> image_iff)
      then obtain t where \<open>y = Rep_bounded P t\<close>
        by blast
      have \<open>\<langle> x - Rep_bounded P x, y \<rangle> = \<langle> x - Rep_bounded P x, Rep_bounded P t \<rangle>\<close>
        by (simp add: \<open>y = Rep_bounded P t\<close>)
      also have \<open>\<dots> = \<langle> Rep_bounded P (x - Rep_bounded P x), t \<rangle>\<close>
        by (metis \<open>P = P*\<close> adjoint_I)
      also have \<open>\<dots> = \<langle> Rep_bounded P x - Rep_bounded P (Rep_bounded P x), t \<rangle>\<close>
        by (metis \<open>P = P*\<close> adjoint_I cinner_diff_left)
      also have \<open>\<dots> = \<langle> Rep_bounded P x - Rep_bounded P x, t \<rangle>\<close>
      proof-
        have \<open>(Rep_bounded P) \<circ> (Rep_bounded P) = (Rep_bounded P)\<close>
          using  \<open>P \<circ>\<^sub>C P = P\<close>
          by (metis timesOp_Rep_bounded)          
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
    have "is_subspace (Rep_linear_space M)"
      by (metis \<open>Rep_linear_space M = range (Rep_bounded P)\<close> \<open>is_subspace (range (Rep_bounded P))\<close>)
    then have f1: "\<forall>a. Rep_bounded (Proj M) a = Rep_bounded P a"
      by (simp add: Proj.rep_eq \<open>\<And>x. Rep_bounded P x \<in> Rep_linear_space M\<close> \<open>\<And>x. x - Rep_bounded P x \<in> orthogonal_complement (Rep_linear_space M)\<close> projection_uniq)
    have "\<forall>a. (+) ((a::'a) - a) = id"
      by force
    then have "\<forall>a. (+) (Rep_bounded (P - Proj M) a) = id"
      using f1 by (simp add: minus_bounded_lift)
    then have "\<forall>a aa. aa - aa = Rep_bounded (P - Proj M) a"
      by (metis (no_types) add_diff_cancel_right' id_apply)
    then have "\<forall>a. Rep_bounded (idOp - (P - Proj M)) a = a"
      by (simp add: idOp.rep_eq minus_bounded_lift)
    then show ?thesis
      by (metis (no_types) Rep_bounded_inject diff_diff_eq2 diff_eq_diff_eq eq_id_iff idOp.rep_eq)
  qed
  thus ?thesis
    using \<open>Rep_linear_space M = range (Rep_bounded P)\<close> by blast 
qed

lemma Proj_endo_I:
\<open>P * P = P \<Longrightarrow> P = P\<^sup>a\<^sup>d\<^sup>j \<Longrightarrow> \<exists> M. P = (\<Pi>\<^sub>e\<^sub>n\<^sub>d\<^sub>o M)\<close>
  using Proj_I
  unfolding Adj_endo_def times_endo_def
  by (metis Proj_endo_def endo_of_bounded_inv)

lemma Proj_leq: "(Proj S) \<down> A \<le> S"
  by (metis cdot_plus_distrib imageOp_Proj le_iff_add top_greatest xsupxy_linear_space)

lemma Proj_times: "isometry A \<Longrightarrow> A \<circ>\<^sub>C (Proj S) \<circ>\<^sub>C (A*) = Proj (A \<down> S)" 
  for A::"('a::chilbert_space,'b::chilbert_space) bounded"
proof-
  assume \<open>isometry A\<close>
  define P where \<open>P = A \<circ>\<^sub>C (Proj S) \<circ>\<^sub>C (A*)\<close>
  have \<open>P \<circ>\<^sub>C P = P\<close>
    using  \<open>isometry A\<close>
    unfolding P_def isometry_def
    by (metis (no_types, lifting) Proj_D2 timesOp_assoc times_idOp2)
  moreover have \<open>P = P*\<close>
    unfolding P_def
    by (metis Proj_D1 adjoint_twice timesOp_assoc times_adjoint)
  ultimately have 
    \<open>\<exists> M. P = Proj M \<and> Rep_linear_space M = range (Rep_bounded (A \<circ>\<^sub>C (Proj S) \<circ>\<^sub>C (A*)))\<close>
    using P_def Proj_I by blast
  then obtain M where \<open>P = Proj M\<close>
    and \<open>Rep_linear_space M = range (Rep_bounded (A \<circ>\<^sub>C (Proj S) \<circ>\<^sub>C (A*)))\<close>
    by blast
  have \<open>M = A \<down> S\<close>
  proof - (* sledgehammer *)
    have f1: "\<forall>l. A \<down> (Proj S \<down> (A* \<down> l)) = P \<down> l"
      by (simp add: P_def timesOp_assoc_linear_space)
    have f2: "\<forall>l b. b* \<down> (b \<down> (l::'a linear_space)::'b linear_space) = idOp \<down> l \<or> \<not> isometry b"
      by (metis (no_types) isometry_def timesOp_assoc_linear_space)
    have f3: "\<forall>l b. b \<down> (idOp \<down> (l::'a linear_space)) = (b \<down> l::'a linear_space)"
      by auto
    have f4: "\<forall>l. (0::'b linear_space) \<le> l"
      by (metis add.left_neutral le_iff_add)
    have "\<forall>l. (top::'a linear_space) + l = top"
      by (simp add: top_add)
    then show ?thesis
      using f4 f3 f2 f1 by (metis \<open>P = Proj M\<close> \<open>isometry A\<close> add.commute cdot_plus_distrib imageOp_Proj top_add)
  qed  
  thus ?thesis
    using \<open>P = Proj M\<close>
    unfolding P_def
    by blast
qed

abbreviation proj :: "'a::chilbert_space \<Rightarrow> ('a,'a) bounded" where "proj \<psi> \<equiv> Proj (span {\<psi>})"

lift_definition ortho :: \<open>'a::chilbert_space linear_space \<Rightarrow> 'a linear_space\<close>
is \<open>orthogonal_complement\<close>
  by (rule Complex_Inner_Product.is_subspace_orthog)

lemma projection_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" for a::complex and \<psi>::"'a::chilbert_space"
  by simp  

lemma move_plus:
  "(Proj (ortho C)) \<down> A \<le> B \<Longrightarrow> A \<le> B + C"
  for A B C::"'a::chilbert_space linear_space"
proof-
  assume \<open>(Proj (ortho C)) \<down> A \<le> B\<close>
  hence \<open>Abs_bounded
     (projection
       (Rep_linear_space
         (Abs_linear_space (orthogonal_complement (Rep_linear_space C))))) \<down> A \<le> B\<close>
    unfolding Proj_def ortho_def less_eq_linear_space_def
    by auto
  hence \<open>Abs_bounded (projection (orthogonal_complement (Rep_linear_space C))) \<down> A \<le> B\<close>
    by (metis Proj_def \<open>Proj (ortho C) \<down> A \<le> B\<close> map_fun_apply ortho.rep_eq)
  hence \<open>x \<in> Rep_linear_space
              (Abs_linear_space
                (closure
                  (Rep_bounded
                    (Abs_bounded
                      (projection (orthogonal_complement (Rep_linear_space C)))) `
                   Rep_linear_space A))) \<Longrightarrow>
         x \<in> Rep_linear_space B\<close>
    for x
    unfolding applyOpSpace_def less_eq_linear_space_def
    by auto
  hence \<open>x \<in>  closure (Rep_bounded (Abs_bounded
                      (projection (orthogonal_complement (Rep_linear_space C)))) `
                   Rep_linear_space A) \<Longrightarrow>
         x \<in> Rep_linear_space B\<close>
  for x
    using \<open>Abs_bounded (projection (orthogonal_complement (Rep_linear_space C))) \<down> A \<le> B\<close>
          applyOpSpace.rep_eq less_eq_linear_space.rep_eq by blast
  hence \<open>x \<in>  closure ( (projection (orthogonal_complement (Rep_linear_space C))) `
                   Rep_linear_space A) \<Longrightarrow>
         x \<in> Rep_linear_space B\<close>
  for x
    by (metis (full_types) Proj.rep_eq Proj_def map_fun_apply ortho.rep_eq)

  hence \<open>x \<in> Rep_linear_space A \<Longrightarrow>
    x \<in> closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> Rep_linear_space B \<and> \<phi> \<in> Rep_linear_space C}\<close>
    for x
  proof-
    assume \<open>x \<in> Rep_linear_space A\<close>
    have \<open>is_subspace (Rep_linear_space C)\<close>
      using Rep_linear_space by auto
    hence \<open>x = (projection (Rep_linear_space C)) x
       + (projection (orthogonal_complement (Rep_linear_space C))) x\<close>
      by (simp add: ortho_decomp)
    hence \<open>x = (projection (orthogonal_complement (Rep_linear_space C))) x
              + (projection (Rep_linear_space C)) x\<close>
      by (metis ordered_field_class.sign_simps(2))
    moreover have \<open>(projection (orthogonal_complement (Rep_linear_space C))) x \<in> Rep_linear_space B\<close>
      using \<open>x \<in>  closure ( (projection (orthogonal_complement (Rep_linear_space C))) `
                   Rep_linear_space A) \<Longrightarrow> x \<in> Rep_linear_space B\<close>
      by (meson \<open>\<And>x. x \<in> closure (projection (orthogonal_complement (Rep_linear_space C)) ` Rep_linear_space A) \<Longrightarrow> x \<in> Rep_linear_space B\<close> \<open>x \<in> Rep_linear_space A\<close> closure_subset image_subset_iff)
    moreover have \<open>(projection (Rep_linear_space C)) x \<in> Rep_linear_space C\<close>
      by (simp add: \<open>is_subspace (Rep_linear_space C)\<close> projection_intro2)
    ultimately show ?thesis
      using closure_subset by fastforce 
  qed
  hence \<open>x \<in> Rep_linear_space A \<Longrightarrow>
        x \<in> (Rep_linear_space B +\<^sub>M Rep_linear_space C)\<close>
    for x
    unfolding closed_sum_def Minkoswki_sum_def
    by blast
  hence \<open> x \<in> Rep_linear_space A \<Longrightarrow>
         x \<in> Rep_linear_space
               (Abs_linear_space (Rep_linear_space B +\<^sub>M Rep_linear_space C))\<close>
    for x
    by (metis Rep_linear_space_inverse plus_linear_space.rep_eq)    
  thus ?thesis 
  unfolding Proj_def ortho_def less_eq_linear_space_def plus_linear_space_def
  by auto
qed


end

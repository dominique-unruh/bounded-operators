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


lift_definition rtimesOp:: 
  "('b::real_normed_vector,'c::real_normed_vector) rbounded
     \<Rightarrow> ('a::real_normed_vector,'b) rbounded \<Rightarrow> ('a,'c) rbounded"
  is "(o)"
  unfolding o_def 
  by (rule bounded_linear_compose, simp_all)

definition timesOp:: 
  "('b::complex_normed_vector,'c::complex_normed_vector) bounded
     \<Rightarrow> ('a::complex_normed_vector,'b) bounded \<Rightarrow> ('a,'c) bounded" where
  \<open>timesOp f g = bounded_of_rbounded (rtimesOp (rbounded_of_bounded f) (rbounded_of_bounded g))\<close>

lemma timesOp_Rep_bounded:
  \<open>Rep_bounded (timesOp f g) = (Rep_bounded f)\<circ>(Rep_bounded g)\<close>
  unfolding timesOp_def
  by (metis (no_types, lifting) comp_apply rbounded_bounded rbounded_of_bounded.rep_eq rbounded_of_bounded_prelim rtimesOp.rep_eq)

lemma rtimesOp_assoc: "rtimesOp (rtimesOp A B) C = rtimesOp A (rtimesOp B C)" 
  apply transfer
  by (simp add: comp_assoc) 

lemma timesOp_assoc: "timesOp (timesOp A B) C = timesOp A (timesOp B C)" 
  by (metis (no_types, lifting) Rep_bounded_inverse fun.map_comp timesOp_Rep_bounded) 

lemma times_adjoint[simp]: "adjoint (timesOp A B) = timesOp (adjoint B) (adjoint A)"
  using timesOp_Rep_bounded 
  by (smt adjoint_D adjoint_I comp_apply)

lift_definition applyOpSpace::\<open>('a::chilbert_space,'b::chilbert_space) bounded
\<Rightarrow> 'a linear_space \<Rightarrow> 'b linear_space\<close> 
  is "\<lambda>A S. closure (A ` S)"
  using  bounded_clinear_def is_subspace.subspace
  by (metis closed_closure is_linear_manifold_image is_subspace.intro is_subspace_cl) 

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


lemmas assoc_left = timesOp_assoc[symmetric] timesOp_assoc_linear_space[symmetric] add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded", symmetric]
lemmas assoc_right = timesOp_assoc timesOp_assoc_linear_space add.assoc[where ?'a="('a::chilbert_space,'b::chilbert_space) bounded"]

lemma scalar_times_op_add[simp]: "scaleC a (A+B) = scaleC a A + scaleC a B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  by (simp add: scaleC_add_right)

lemma scalar_times_op_minus[simp]: "scaleC a (A-B) = scaleC a A - scaleC a B" for A B :: "(_::complex_normed_vector,_::complex_normed_vector) bounded"
  by (simp add: complex_vector.scale_right_diff_distrib)


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
  shows \<open>(applyOpSpace U) (A + B) = (applyOpSpace U) A + (applyOpSpace U) B\<close>
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
  shows \<open>(applyOpSpace (\<alpha> *\<^sub>C A)) S  = \<alpha> *\<^sub>C ((applyOpSpace A) S)\<close>
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

lemma applyOpSpace_id[simp]: "(applyOpSpace idOp) \<psi> = \<psi>"
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
  shows \<open>\<forall> c. \<forall> x. Rep_rbounded (rtimesOp f g) (c *\<^sub>C x) = c *\<^sub>C (Rep_rbounded (rtimesOp f g) x)\<close>
  by (simp add: assms(1) assms(2) rtimesOp.rep_eq)

lemma rscalar_op_op: 
  fixes A::"('b::chilbert_space,'c::chilbert_space) rbounded" 
    and B::"('a::chilbert_space, 'b::chilbert_space) rbounded"
  shows \<open>rtimesOp (a *\<^sub>C A) B = a *\<^sub>C (rtimesOp A B)\<close>
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
  shows \<open>timesOp (a *\<^sub>C A) B = a *\<^sub>C (timesOp A B)\<close>
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
  shows \<open>rtimesOp A (a *\<^sub>C B) = a *\<^sub>C (rtimesOp A B)\<close>
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
  shows \<open>timesOp A (a *\<^sub>C B) = a *\<^sub>C (timesOp A B)\<close>
  using op_rscalar_op
  by (metis (no_types, lifting) rbounded_of_bounded_prelim rbounded_of_bounded_scaleC rscalar_op_op scalar_op_op timesOp_def)

lemma times_idOp1[simp]: "timesOp U idOp = U"
  by (metis Rep_bounded_inverse comp_id idOp.rep_eq timesOp_Rep_bounded)

lemma times_idOp2[simp]: "timesOp idOp U  = U"
  by (metis Rep_bounded_inject idOp.rep_eq id_comp timesOp_Rep_bounded)



lemma mult_INF1[simp]:
  fixes U :: "('b::chilbert_space,'c::chilbert_space) bounded"
    and V :: "'a \<Rightarrow> 'b linear_space" 
  shows \<open>(applyOpSpace U) (INF i. V i) \<le> (INF i. (applyOpSpace U) (V i))\<close>
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

lemma applyOpSpace_eq:
  fixes S :: "_ linear_space" and A B :: "(_,_) bounded"
  assumes "\<And>x. x \<in> G \<Longrightarrow> Rep_bounded A x = Rep_bounded B x"
  assumes "span G \<ge> S"
  shows "applyOpSpace A S = applyOpSpace B S"
  using assms
  by (cheat applyOpSpace_eq)


section \<open>Projectors\<close>

lift_definition Proj :: "('a::chilbert_space) linear_space \<Rightarrow> ('a,'a) bounded"
is \<open>proj\<close>
  by (rule Complex_Inner_Product.projPropertiesA)

lemma imageOp_Proj[simp]: "applyOpSpace (Proj S) top = S"
  apply transfer
  proof
  show "closure (range (proj (S::'a set))) \<subseteq> S"
    if "is_subspace (S::'a set)"
    for S :: "'a set"
    using that
    by (metis (full_types) OrthoClosedEq closure_mono image_subsetI is_subspace.subspace is_subspace_I orthogonal_complement_twice proj_intro2) 
  show "(S::'a set) \<subseteq> closure (range (proj S))"
    if "is_subspace (S::'a set)"
    for S :: "'a set"
    using that
    by (metis (no_types, lifting) closure_subset image_subset_iff in_mono proj_fixed_points subsetI subset_UNIV) 
qed

lemma proj_D1:
  fixes M :: \<open>'a::chilbert_space set\<close>
  assumes \<open>is_subspace M\<close>
  shows \<open>proj M = (proj M)\<^sup>\<dagger>\<close>
proof-
  have \<open>(proj M) x = ((proj M)\<^sup>\<dagger>) x\<close>
    for x
  proof (rule proj_uniq)
    show \<open>is_subspace M\<close>
      by (simp add: assms)
    show \<open>((proj M)\<^sup>\<dagger>) x \<in> M\<close>
    proof-
      have "y \<in> orthogonal_complement M \<Longrightarrow> \<langle> ((proj M)\<^sup>\<dagger>) x, y \<rangle> = 0"
        for y
      proof-
        assume \<open>y \<in> orthogonal_complement M\<close>
        hence \<open>(proj M) y = 0\<close>
          by (metis add_cancel_right_right assms is_subspace_orthog ortho_decomp orthogonal_complement_twice proj_fixed_points)          
        hence \<open>\<langle> x, (proj M) y \<rangle> = 0\<close>
          by simp          
        thus ?thesis
          by (simp add: Adj_I assms projPropertiesA) 
      qed
      hence "((proj M)\<^sup>\<dagger>) x \<in> orthogonal_complement (orthogonal_complement M)"
        unfolding orthogonal_complement_def is_orthogonal_def
        by blast
      thus ?thesis
        by (simp add: assms orthogonal_complement_twice) 
    qed
    show \<open>x - ((proj M)\<^sup>\<dagger>) x \<in> orthogonal_complement M\<close>
    proof (rule orthogonal_complement_I2)
      show "\<langle>x - (proj M\<^sup>\<dagger>) x, y\<rangle> = 0"
        if "y \<in> M"
        for y :: 'a
      proof-
        have \<open>y = proj M y\<close>
          using that(1)
          by (simp add: assms proj_fixed_points)
        hence \<open>y - proj M y = 0\<close>
          by simp
        have \<open>\<langle>x - (proj M\<^sup>\<dagger>) x, y\<rangle> = \<langle>x, y\<rangle> - \<langle>(proj M\<^sup>\<dagger>) x, y\<rangle>\<close>
          by (simp add: cinner_diff_left)
        also have \<open>... = \<langle>x, y\<rangle> - \<langle>x, (proj M) y\<rangle>\<close>
          by (simp add: Adj_I assms projPropertiesA)
        also have \<open>... = \<langle>x, y - (proj M) y\<rangle>\<close>
          by (simp add: cinner_diff_right)
        also have \<open>... = \<langle>x, 0\<rangle>\<close>
          using  \<open>y - proj M y = 0\<close>
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
  by (rule proj_D1)

lemma Proj_D2:
\<open>timesOp (Proj M) (Proj M) = idOp\<close>
  sorry

lemma Proj_I:
\<open>timesOp P P = idOp \<Longrightarrow> P = P* \<Longrightarrow> \<exists> M. P = Proj M\<close>
  sorry


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



end




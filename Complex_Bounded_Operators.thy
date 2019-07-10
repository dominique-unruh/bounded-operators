(*  Title:      bounded-Operators/complex_bounded_operators.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

Operators between complex vector spaces.

References:             

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}


*)

theory complex_bounded_operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    real_bounded_operators
    Complex_Vector_Spaces
begin

section \<open>Real bounded operators with complex scalar product\<close>

instantiation real_bounded :: (real_normed_vector, complex_normed_vector) "complex_vector"
begin
lift_definition scaleC_real_bounded :: \<open>complex \<Rightarrow>
 ('a::real_normed_vector, 'b::complex_normed_vector) real_bounded \<Rightarrow>
 ('a, 'b) real_bounded\<close>
  is \<open>\<lambda> c::complex. \<lambda> f::'a\<Rightarrow>'b. (\<lambda> x. c *\<^sub>C (f x) )\<close> 
proof
  fix c::complex and f :: \<open>'a\<Rightarrow>'b\<close> and b1::'a and b2::'a
  assume \<open>bounded_linear f\<close>
  show \<open>c *\<^sub>C f (b1 + b2) = c *\<^sub>C f b1 + c *\<^sub>C f b2\<close>
    by (simp add: \<open>bounded_linear f\<close> linear_simps(1) scaleC_add_right)

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
  show "((*\<^sub>R) r::('a, 'b) real_bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
  proof
    show "r *\<^sub>R (x::('a, 'b) real_bounded) = complex_of_real r *\<^sub>C x"
      for x :: "('a, 'b) real_bounded"
      apply transfer
      by (simp add: scaleR_scaleC)
  qed

  show "a *\<^sub>C ((x::('a, 'b) real_bounded) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "('a, 'b) real_bounded"
      and y :: "('a, 'b) real_bounded"
    apply transfer
    by (simp add: scaleC_add_right)

  show "(a + b) *\<^sub>C (x::('a, 'b) real_bounded) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) real_bounded"
    apply transfer
    by (simp add: scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::('a, 'b) real_bounded) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) real_bounded"
    apply transfer
    by simp

  show "1 *\<^sub>C (x::('a, 'b) real_bounded) = x"
    for x :: "('a, 'b) real_bounded"
    apply transfer
  proof
    fix f :: \<open>'a\<Rightarrow>'b\<close> and x :: 'a
    show \<open>1 *\<^sub>C f x = f x\<close>
      by auto
  qed
qed  
end

instantiation real_bounded :: (real_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
instance
  apply intro_classes
  apply transfer
proof-
  fix f::\<open>'a \<Rightarrow> 'b\<close> and a::complex
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
  thus \<open>onorm (\<lambda>x. a *\<^sub>C f x) = cmod a * onorm f\<close>
    by (simp add: onorm_def) 
qed
end


instantiation real_bounded :: ("{real_normed_vector, perfect_space}", cbanach) "cbanach"
begin
instance..
end


section \<open>Complex bounded operators\<close>

typedef (overloaded) ('a::complex_normed_vector, 'b::complex_normed_vector) complex_bounded
  = \<open>{f :: ('a, 'b) real_bounded. \<forall> c. \<forall> x. ev_real_bounded f (c *\<^sub>C x) = c *\<^sub>C (ev_real_bounded f x) }\<close>
  apply transfer
  apply auto
proof
  have "bounded_linear (\<lambda> _::'a. 0::'b)"
    by simp    
  moreover have "(\<forall>c x.  (\<lambda> _::'a. 0::'b) (c *\<^sub>C (x::'a)) = c *\<^sub>C ( (\<lambda> _::'a. 0::'b) x::'b))"
    by simp   
  ultimately show "bounded_linear (\<lambda> _::'a. 0::'b) \<and> (\<forall>c x.  (\<lambda> _::'a. 0::'b) (c *\<^sub>C (x::'a)) = c *\<^sub>C ( (\<lambda> _::'a. 0::'b) x::'b))"
    by blast
qed

setup_lifting type_definition_complex_bounded

type_synonym 'a bounded = "('a, 'a ) complex_bounded"


lift_definition ev_complex_bounded :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) complex_bounded \<Rightarrow> 'a \<Rightarrow> 'b\<close> 
  is \<open>\<lambda> f. \<lambda> x. ev_real_bounded f x\<close>.


instantiation complex_bounded :: (complex_normed_vector, complex_normed_vector) "real_vector"
begin
lift_definition uminus_complex_bounded :: "('a,'b) complex_bounded \<Rightarrow> ('a,'b) complex_bounded"
  is "\<lambda> f. - f"
  by (simp add: ev_real_bounded.rep_eq uminus_real_bounded.rep_eq)

lift_definition zero_complex_bounded :: "('a,'b) complex_bounded" is "0"
  by (simp add: ev_real_bounded.rep_eq zero_real_bounded.rep_eq)

lift_definition plus_complex_bounded :: "('a,'b) complex_bounded \<Rightarrow> ('a,'b) complex_bounded \<Rightarrow> ('a,'b) complex_bounded" is
  \<open>\<lambda> f g. f + g\<close>
  by (simp add: ev_real_bounded.rep_eq plus_real_bounded.rep_eq scaleC_add_right)

lift_definition minus_complex_bounded :: "('a,'b) complex_bounded \<Rightarrow> ('a,'b) complex_bounded \<Rightarrow> ('a,'b) complex_bounded" is
  \<open>\<lambda> f g. f - g\<close>
  by (simp add: complex_vector.scale_right_diff_distrib ev_real_bounded.rep_eq minus_real_bounded.rep_eq)

lift_definition scaleR_complex_bounded :: \<open>real \<Rightarrow> ('a, 'b) complex_bounded \<Rightarrow> ('a, 'b) complex_bounded\<close>
  is \<open>\<lambda> c. \<lambda> f. c *\<^sub>R f\<close>
  by (simp add: ev_real_bounded.rep_eq scaleC_real_bounded.rep_eq scaleR_scaleC)


instance
proof      
  fix a b c :: \<open>('a, 'b) complex_bounded\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer by simp
  fix a b :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) complex_bounded\<close>
  show \<open>a + b = b + a\<close>
    apply transfer by simp
  fix a :: \<open>('a, 'b) complex_bounded\<close>
  show \<open>0 + a = a\<close>
    apply transfer by simp
  fix a :: \<open>('a, 'b) complex_bounded\<close>
  show \<open>-a + a = 0\<close>
    apply transfer
    by simp
  fix a b :: \<open>('a, 'b) complex_bounded\<close>
  show \<open>a - b = a + - b\<close>
    apply transfer by simp
  fix a::real and x y :: \<open>('a, 'b) complex_bounded\<close>
  show \<open>a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y\<close>
    apply transfer
    by (simp add: scaleR_add_right)

  fix a b :: real and x :: \<open>('a, 'b) complex_bounded\<close>
  show \<open>(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x\<close>
    apply transfer
    by (simp add: scaleR_add_left)

  fix a b :: real and x :: \<open>('a, 'b) complex_bounded\<close>
  show \<open>a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x\<close>
    apply transfer
    by simp

  fix x :: \<open>('a, 'b) complex_bounded\<close>
  show \<open>1 *\<^sub>R x = x\<close>
    apply transfer
    by simp
qed
end

instantiation complex_bounded :: (complex_normed_vector, complex_normed_vector) "real_normed_vector"
begin
lift_definition norm_complex_bounded :: \<open>('a, 'b) complex_bounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f. norm f\<close>.

lift_definition dist_complex_bounded :: \<open>('a, 'b) complex_bounded \<Rightarrow> ('a, 'b) complex_bounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. dist f g\<close>.

lift_definition sgn_complex_bounded :: \<open>('a, 'b) complex_bounded \<Rightarrow> ('a, 'b) complex_bounded\<close>
  is \<open>\<lambda> f. sgn f\<close>
  apply transfer
  by (simp add: scaleR_scaleC)

lift_definition uniformity_complex_bounded :: \<open>( ('a, 'b) complex_bounded \<times> ('a, 'b) complex_bounded ) filter\<close>
  is \<open>(INF e:{0<..}. principal {((f::('a, 'b) complex_bounded), g). dist f g < e})\<close>.

lift_definition open_complex_bounded :: \<open>(('a, 'b) complex_bounded) set \<Rightarrow> bool\<close>
  is \<open>\<lambda> U::(('a, 'b) complex_bounded) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)\<close>.

instance
  apply intro_classes
        apply transfer 
        apply auto
          apply transfer 
          apply auto
         apply transfer 
         apply (simp add: sgn_div_norm)
        apply (simp add: uniformity_complex_bounded.transfer)
       apply (metis (mono_tags, lifting)  open_complex_bounded.transfer)
      apply (smt eventually_mono open_complex_bounded.transfer split_cong)
     apply transfer
     apply simp
    apply transfer
    apply simp
   apply (smt add_diff_cancel_left' minus_complex_bounded.rep_eq norm_complex_bounded.rep_eq norm_triangle_ineq2)
  apply transfer
  by simp
end


instantiation complex_bounded :: (complex_normed_vector, complex_normed_vector) "complex_vector"
begin 
lift_definition scaleC_complex_bounded :: \<open>complex \<Rightarrow> ('a, 'b) complex_bounded \<Rightarrow> ('a, 'b) complex_bounded\<close>
  is \<open>\<lambda> c::complex. \<lambda> f::('a, 'b) real_bounded. c *\<^sub>C f\<close> 
  by (simp add: ev_real_bounded.rep_eq scaleC_real_bounded.rep_eq)

instance
proof
  show "((*\<^sub>R) r::('a, 'b) complex_bounded \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
  proof
    fix x::\<open>('a, 'b) complex_bounded\<close>
    show \<open>r *\<^sub>R x = complex_of_real r *\<^sub>C x\<close>
      apply transfer
      by (simp add: scaleR_scaleC)
  qed
  show "a *\<^sub>C ((x::('a, 'b) complex_bounded) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "('a, 'b) complex_bounded"
      and y :: "('a, 'b) complex_bounded"
    apply transfer
    by (simp add: scaleC_add_right)

  show "(a + b) *\<^sub>C (x::('a, 'b) complex_bounded) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) complex_bounded"
    apply transfer
    by (simp add: scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::('a, 'b) complex_bounded) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "('a, 'b) complex_bounded"
    apply transfer
    by simp

  show "1 *\<^sub>C (x::('a, 'b) complex_bounded) = x"
    for x :: "('a, 'b) complex_bounded"
    apply transfer
    using scaleC_one by blast
qed  
end

instantiation complex_bounded :: (complex_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
instance
  apply intro_classes
  apply transfer
  by simp
end


lemma scaleC_continuous:
  fixes c :: complex
  shows \<open>continuous_on UNIV (((*\<^sub>C) c)::('a::complex_normed_vector \<Rightarrow> 'a))\<close>
proof-
  have \<open>0 < r \<Longrightarrow>
           \<exists>s>0. \<forall>xa. xa \<noteq> x \<and> dist xa x < s \<longrightarrow> dist (c *\<^sub>C xa) (c *\<^sub>C x) < r\<close>
    for x::'a and r::real
  proof-
    assume \<open>0 < r\<close>
    show ?thesis 
    proof(cases \<open>c = 0\<close>)
      case True
      thus ?thesis
        using \<open>0 < r\<close> by auto 
    next
      case False
      hence \<open>c \<noteq> 0\<close>
        by blast
      hence \<open>cmod c > 0\<close>
        by simp
      hence  \<open>inverse (cmod c) > 0\<close>
        by simp
      hence \<open>\<exists>s>0. \<forall>y. y \<noteq> x \<and> norm (y - x) < s \<longrightarrow> norm (y - x) < r/(cmod c)\<close>
      proof-
        have \<open> r/(cmod c) > 0\<close>
          using \<open>r > 0\<close> and \<open>cmod c > 0\<close>
          by simp
        moreover have \<open>y \<noteq> x \<Longrightarrow> norm (y - x) < r/(cmod c) \<Longrightarrow> norm (y - x) < r/(cmod c)\<close>
          for y
          by blast
        ultimately show ?thesis
          by blast 
      qed
      hence \<open>\<exists>s>0. \<forall>y. y \<noteq> x \<and> norm (y - x) < s \<longrightarrow> (cmod c) * norm (y - x) < r\<close>
        using  \<open>cmod c > 0\<close>
        by (simp add: linordered_field_class.pos_less_divide_eq ordered_field_class.sign_simps(24))        
      hence \<open>\<exists>s>0. \<forall>y. y \<noteq> x \<and> norm (y - x) < s \<longrightarrow> norm (c *\<^sub>C (y - x)) < r\<close>
        by simp       
      hence \<open>\<exists>s>0. \<forall>y. y \<noteq> x \<and> norm (y - x) < s \<longrightarrow> norm ((c *\<^sub>C y) - (c *\<^sub>C x)) < r\<close>
        by (simp add: complex_vector.scale_right_diff_distrib)        
      hence \<open>\<exists>s>0. \<forall>y. y \<noteq> x \<and> dist y x < s \<longrightarrow> dist (c *\<^sub>C y) (c *\<^sub>C x) < r\<close>
        by (simp add: dist_norm)        
      thus ?thesis by blast
    qed
  qed
  thus ?thesis unfolding continuous_on LIM_def by blast
qed
lemma tendsto_scaleC:
  fixes f :: \<open>nat \<Rightarrow> 'a::complex_normed_vector\<close> 
    and l :: 'a and c :: complex
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda> n. c *\<^sub>C (f n)) \<longlonglongrightarrow>  c *\<^sub>C l\<close>
proof-
  have \<open>continuous_on UNIV (((*\<^sub>C) c)::('a\<Rightarrow>'a))\<close>
    using scaleC_continuous by blast
  thus ?thesis using  \<open>f \<longlonglongrightarrow> l\<close>
    by (metis (full_types) UNIV_I continuous_on_def filterlim_compose tendsto_at_iff_tendsto_nhds) 
qed

lemma real_bounded_SEQ_scaleC:
  fixes f :: \<open>nat \<Rightarrow> ('a::{complex_normed_vector, perfect_space}, 'b::cbanach) real_bounded\<close> 
    and l :: \<open>('a, 'b) real_bounded\<close>
  assumes \<open>\<And> n. \<forall> c. \<forall> x. ev_real_bounded (f n) (c *\<^sub>C x) = c *\<^sub>C ev_real_bounded (f n) x\<close>
    and \<open>f \<longlonglongrightarrow> l\<close> 
  shows \<open>\<forall> c. \<forall> x. ev_real_bounded l (c *\<^sub>C x) = c *\<^sub>C ev_real_bounded l x\<close>
proof-
  have \<open>ev_real_bounded l (c *\<^sub>C x) = c *\<^sub>C ev_real_bounded l x\<close>
    for c::complex and x::'a
  proof-
    have  \<open>(\<lambda> n. ev_real_bounded (f n) p)  \<longlonglongrightarrow> ev_real_bounded l p\<close>
      for p
    proof-
      from  \<open>f \<longlonglongrightarrow> l\<close>
      have \<open>f\<midarrow>STRONG\<rightarrow>l\<close>
        by (simp add: ONORM_STRONG tendsto_ONORM_real_bounded)
      thus ?thesis 
        apply transfer
        unfolding strong_convergence_def
        apply auto
        by (simp add: LIM_zero_cancel tendsto_norm_zero_iff)
    qed
    hence \<open>(\<lambda> n. ev_real_bounded (f n) (c *\<^sub>C x)) \<longlonglongrightarrow> ev_real_bounded l (c *\<^sub>C x)\<close>
      by blast
    moreover have \<open>(\<lambda> n. ev_real_bounded (f n) (c *\<^sub>C x)) \<longlonglongrightarrow>  c *\<^sub>C ev_real_bounded l x\<close>
    proof-
      have \<open>(\<lambda> n. ev_real_bounded (f n) (c *\<^sub>C x))
        = (\<lambda> n. c *\<^sub>C ev_real_bounded (f n) x)\<close>
        using  \<open>\<And> n. \<forall> c. \<forall> x. ev_real_bounded (f n) (c *\<^sub>C x) = c *\<^sub>C ev_real_bounded (f n) x\<close>
        by auto
      moreover have \<open>(\<lambda> n. c *\<^sub>C ev_real_bounded (f n) x)  \<longlonglongrightarrow>  c *\<^sub>C ev_real_bounded l x\<close>
        using  \<open>\<And> p. (\<lambda> n. ev_real_bounded (f n) p)  \<longlonglongrightarrow> ev_real_bounded l p\<close>
        by (simp add: tendsto_scaleC)
      ultimately show ?thesis using LIMSEQ_unique by simp
    qed
    ultimately show ?thesis
      using LIMSEQ_unique by blast 
  qed
  thus ?thesis by blast
qed

instantiation complex_bounded :: ("{complex_normed_vector, perfect_space}", cbanach) "cbanach"
begin
instance
  apply intro_classes
proof-
  fix f :: \<open>nat \<Rightarrow> ('a, 'b) complex_bounded\<close>
  assume \<open>Cauchy f\<close>
  hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m) (f n) < e\<close>
    unfolding Cauchy_def
    by blast
  hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. 
    dist (Rep_complex_bounded (f m)) (Rep_complex_bounded (f n)) < e\<close>
    apply transfer
    by blast
  hence \<open>Cauchy (\<lambda> n. (Rep_complex_bounded (f n)))\<close>
    using Cauchy_altdef by force
  hence \<open>convergent (\<lambda> n. (Rep_complex_bounded (f n)))\<close>
    by (simp add: Cauchy_convergent_iff)
  hence \<open>\<exists> l::('a, 'b) real_bounded. 
         (\<lambda> n. (Rep_complex_bounded (f n))) \<longlonglongrightarrow> l\<close>
    using convergentD by blast
  then obtain l::\<open>('a, 'b) real_bounded\<close>
    where \<open>(\<lambda> n. (Rep_complex_bounded (f n))) \<longlonglongrightarrow> l\<close>
    by blast
  have \<open>\<forall> c. \<forall> x. ev_real_bounded l (c *\<^sub>C x) =
                c *\<^sub>C ev_real_bounded l x \<close>
  proof-
    have \<open>\<And> n. \<forall> c. \<forall> x. ev_real_bounded (Rep_complex_bounded (f n)) (c *\<^sub>C x)
         = c *\<^sub>C ev_real_bounded (Rep_complex_bounded (f n)) x\<close>
      apply transfer
      by simp
    thus ?thesis
      using \<open>(\<lambda> n. (Rep_complex_bounded (f n))) \<longlonglongrightarrow> l\<close>
      by (rule real_bounded_SEQ_scaleC)
  qed
  hence \<open>\<exists> L. Rep_complex_bounded L = l\<close>
    apply transfer by blast
  then obtain L::\<open>('a, 'b) complex_bounded\<close>
    where \<open>Rep_complex_bounded L = l\<close> by blast
  have \<open>(\<lambda> n. (Rep_complex_bounded (f n))) \<longlonglongrightarrow> (Rep_complex_bounded L)\<close>
    using \<open>Rep_complex_bounded L = l\<close>
      \<open>(\<lambda> n. (Rep_complex_bounded (f n))) \<longlonglongrightarrow> l\<close>
    by blast
  hence \<open>\<forall>e>0. \<exists>N. \<forall>n\<ge>N. 
    dist (Rep_complex_bounded (f n)) (Rep_complex_bounded L) < e\<close>
    by (simp add: metric_LIMSEQ_D)
  hence \<open>\<forall>e>0. \<exists>N. \<forall>n\<ge>N. dist (f n) L < e\<close>
    apply transfer by blast
  hence \<open>f \<longlonglongrightarrow> L\<close>
    by (simp add: metric_LIMSEQ_I)
  thus \<open>convergent f\<close> 
    unfolding convergent_def by blast
qed

end




end


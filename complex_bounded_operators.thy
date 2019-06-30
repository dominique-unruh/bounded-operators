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
  by (simp add: ev_real_bounded.rep_eq scaleR_real_bounded.rep_eq scaleR_scaleC)

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


end
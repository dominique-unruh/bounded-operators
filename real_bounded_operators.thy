(*  Title:      bounded-Operators/real_bounded_operators.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

Operators between real vector spaces.

References:             

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}

*)

theory real_bounded_operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    Operator_Norm_Plus
begin


section "Bounded operators"

typedef (overloaded) ('a::real_normed_vector, 'b::real_normed_vector) real_bounded
  = \<open>{f::'a \<Rightarrow> 'b. bounded_linear f}\<close>
  using bounded_linear_zero by blast

setup_lifting type_definition_real_bounded

lift_definition ev_real_bounded :: \<open>('a::real_normed_vector, 'b::real_normed_vector) real_bounded \<Rightarrow> 'a \<Rightarrow> 'b\<close> 
  is \<open>\<lambda> f. \<lambda> x. f x\<close>.

instantiation real_bounded :: (real_normed_vector, real_normed_vector) "real_vector"
begin
lift_definition uminus_real_bounded :: "('a,'b) real_bounded \<Rightarrow> ('a,'b) real_bounded"
  is "\<lambda> f. (\<lambda> t::'a. - f t)"
  by (fact bounded_linear_minus)

lift_definition zero_real_bounded :: "('a,'b) real_bounded" is "\<lambda>x::'a. (0::'b)"
  by (fact bounded_linear_zero)

lift_definition plus_real_bounded :: "('a,'b) real_bounded \<Rightarrow> ('a,'b) real_bounded \<Rightarrow> ('a,'b) real_bounded" is
  \<open>\<lambda> f g. (\<lambda> t. f t + g t)\<close>
  by (fact bounded_linear_add)

lift_definition minus_real_bounded :: "('a,'b) real_bounded \<Rightarrow> ('a,'b) real_bounded \<Rightarrow> ('a,'b) real_bounded" is
  \<open>\<lambda> f g. (\<lambda> t. f t - g t)\<close>
  by (simp add: bounded_linear_sub)

lift_definition scaleR_real_bounded :: \<open>real \<Rightarrow> ('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded\<close>
  is \<open>\<lambda> c. \<lambda> f. (\<lambda> x. c *\<^sub>R (f x))\<close>
  by (rule Bounded_Linear_Function.bounded_linear_intros(6))

instance
proof      
  fix a b c :: \<open>('a, 'b) real_bounded\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply transfer by auto
  fix a b :: \<open>('a::real_normed_vector, 'b::real_normed_vector) real_bounded\<close>
  show \<open>a + b = b + a\<close>
    apply transfer
    by (simp add: linordered_field_class.sign_simps(2))

  fix a :: \<open>('a, 'b) real_bounded\<close>
  show \<open>0 + a = a\<close>
    apply transfer by simp

  fix a :: \<open>('a, 'b) real_bounded\<close>
  show \<open>-a + a = 0\<close>
    apply transfer
    by simp

  fix a b :: \<open>('a, 'b) real_bounded\<close>
  show \<open>a - b = a + - b\<close>
    apply transfer
    by auto
  fix a::real and x y :: \<open>('a, 'b) real_bounded\<close>
  show \<open>a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y\<close>
    apply transfer
    by (simp add: pth_6)

  fix a b :: real and x :: \<open>('a, 'b) real_bounded\<close>
  show \<open>(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x\<close>
    apply transfer
    by (simp add: scaleR_add_left)

  fix a b :: real and x :: \<open>('a, 'b) real_bounded\<close>
  show \<open>a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x\<close>
    apply transfer
    by simp

  fix x :: \<open>('a, 'b) real_bounded\<close>
  show \<open>1 *\<^sub>R x = x\<close>
    apply transfer
    by simp
qed
end

instantiation real_bounded :: (real_normed_vector, real_normed_vector) "real_normed_vector"
begin
lift_definition norm_real_bounded :: \<open>('a, 'b) real_bounded \<Rightarrow> real\<close>
  is \<open>onorm\<close>.

lift_definition dist_real_bounded :: \<open>('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. onorm (\<lambda> x. f x - g x )\<close>.

lift_definition sgn_real_bounded :: \<open>('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded\<close>
  is \<open>\<lambda> f. (\<lambda> x. (f x) /\<^sub>R (onorm f) )\<close>
  by (rule Bounded_Linear_Function.bounded_linear_intros(6))

lift_definition uniformity_real_bounded :: \<open>( ('a, 'b) real_bounded \<times> ('a, 'b) real_bounded ) filter\<close>
  is \<open>(INF e:{0<..}. principal {((f::('a, 'b) real_bounded), g). dist f g < e})\<close>.

lift_definition open_real_bounded :: \<open>(('a, 'b) real_bounded) set \<Rightarrow> bool\<close>
  is \<open>\<lambda> U::(('a, 'b) real_bounded) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)\<close>.

instance
  apply intro_classes
        apply transfer
        apply auto
         apply transfer
         apply auto
        apply (simp add: uniformity_real_bounded.transfer)
       apply (metis (mono_tags, lifting) open_real_bounded.transfer)
      apply (smt eventually_mono open_real_bounded.transfer split_cong)
     apply transfer
  using onorm_pos_lt apply fastforce
    apply transfer
    apply (simp add: onorm_zero)
   apply transfer
   apply (simp add: onorm_triangle)
  apply transfer
  using onorm_scaleR by blast
end




end
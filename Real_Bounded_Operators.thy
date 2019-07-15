(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Definition of the type rbounded
Main results:
- Definition of the type rbounded for bounded operators between real normed spaces.
- Instantiation of rbounded as real_normed_vector.

*)

theory Real_Bounded_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    HOL.Real_Vector_Spaces
    "HOL-Analysis.Operator_Norm"
begin


section "Real bounded operators"

typedef (overloaded) ('a::real_normed_vector, 'b::real_normed_vector) rbounded
  = \<open>{f::'a \<Rightarrow> 'b. bounded_linear f}\<close>
  using bounded_linear_zero by blast

setup_lifting type_definition_rbounded

lift_definition ev_rbounded :: \<open>('a::real_normed_vector, 'b::real_normed_vector) rbounded
 \<Rightarrow> 'a \<Rightarrow> 'b\<close> is \<open>\<lambda> f. \<lambda> x. f x\<close>.

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
        apply (simp add: Real_Bounded_Operators.uniformity_rbounded_def)
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



end

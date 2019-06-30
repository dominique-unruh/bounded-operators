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


end
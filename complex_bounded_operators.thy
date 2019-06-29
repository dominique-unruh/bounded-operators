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
proof -
  obtain rr :: "('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_operator" where
    f1: "\<forall>r. rr r \<in> Collect bounded_real_operator \<and> Abs_real_bounded (rr r) = r"
by (metis (no_types) Abs_real_bounded_cases)
obtain cc :: "('a, 'b) real_operator \<Rightarrow> complex" and aa :: "('a, 'b) real_operator \<Rightarrow> 'a" where
  f2: "\<forall>r. ((\<forall>c a. ev_real_operator r (c *\<^sub>C a) = c *\<^sub>C ev_real_operator r a) \<and> bounded_real_operator r \<or> \<not> bounded_real_operator r \<or> ev_real_operator r (cc r *\<^sub>C aa r) \<noteq> cc r *\<^sub>C ev_real_operator r (aa r)) \<and> (bounded_real_operator r \<and> (\<forall>c a. ev_real_operator r (c *\<^sub>C a) = c *\<^sub>C ev_real_operator r a) \<or> (\<exists>c a. ev_real_operator r (c *\<^sub>C a) \<noteq> c *\<^sub>C ev_real_operator r a) \<or> \<not> bounded_real_operator r)"
  by moura
  obtain bb :: "('a, 'b) real_operator \<Rightarrow> 'a \<Rightarrow> 'b" where
    f3: "\<forall>r. ev_real_operator r = bb r"
    by metis
  have "0 = rr 0"
    using f1 by (metis (no_types) Abs_real_bounded_inverse cr_real_bounded_def zero_real_bounded.transfer)
  then have "\<exists>r. bb r (cc r *\<^sub>C aa r) = cc r *\<^sub>C bb r (aa r) \<and> bounded_real_operator r"
    using f3 f1 by (metis complex_vector.scale_eq_0_iff ev_real_operator.rep_eq mem_Collect_eq zero_real_operator.rep_eq)
  then show "\<exists>r\<in>{r. bounded_real_operator r}. r \<in> {r. (\<forall>c a. ev_real_operator r (c *\<^sub>C (a::'a)) = c *\<^sub>C (ev_real_operator r a::'b)) \<and> bounded_real_operator r}"
    using f3 f2 by auto
qed

lift_definition ev_complex_bounded :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) real_bounded \<Rightarrow> 'a \<Rightarrow> 'b\<close> 
is \<open>\<lambda> f. \<lambda> x. ev_real_bounded f x\<close>.


end
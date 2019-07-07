(*  Title:      bounded-Operators/finite_rank_operators.thy
    Author:     Dominique Unruh, University of Tartu
    Author:     Jose Manuel Rodriguez Caballero, University of Tartu

Finite rank operators.

References:             

 @book{conway2013course,
  title={A course in functional analysis},
  author={Conway, John B},
  volume={96},
  year={2013},
  publisher={Springer Science \& Business Media}
}


*)

theory finite_rank_operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    complex_bounded_operators
    Complex_Inner_Product
begin

fun complex_gen ::\<open>nat \<Rightarrow> ('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> bool\<close> where
  \<open>complex_gen 0 f = (\<forall> x. f x = 0)\<close> |
  \<open>complex_gen (Suc n) f =  (\<exists> g. complex_gen n g \<and>
  ( \<exists> t. \<forall> x. \<exists> c. f x = c *\<^sub>C t + g x ) )\<close> 

definition finite_complex_rank :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> bool\<close> where
  \<open>finite_complex_rank f = (\<exists> n. complex_gen n f)\<close> 

definition complex_rank :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> ereal\<close> where
  \<open>complex_rank f = Inf { n |n. complex_gen n f}\<close> 

lemma finite_rank_and_linear:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes \<open>clinear f\<close> and \<open>finite_complex_rank f\<close>
  shows \<open>bounded_clinear f\<close>
  sorry

lift_definition finite_complex_rank_real_bouded :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) real_bounded \<Rightarrow> bool\<close>
  is finite_complex_rank.

lift_definition finite_complex_rank_complex_bouded :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) complex_bounded \<Rightarrow> bool\<close>
  is finite_complex_rank_real_bouded.

text \<open>Definition of compact operators on a Hilbert space (this definition does not generalize to
Banach spaces)\<close>

typedef (overloaded) ('a::chilbert_space) finite_rank
  = \<open>{f :: 'a bounded. finite_complex_rank_complex_bouded f}\<close>
  apply auto
  apply transfer
  apply auto
  apply transfer
  apply auto
proof
  show "bounded_linear (\<lambda> _. 0) \<and> (\<forall>c x. (\<lambda> _. 0) (c *\<^sub>C (x::'a)) = c *\<^sub>C ((\<lambda> _. 0) x::'a)) \<and> finite_complex_rank (\<lambda> _. 0)"
    apply auto
    unfolding finite_complex_rank_def
  proof
    show "complex_gen 0 ((\<lambda>_. 0)::'d \<Rightarrow> 'e)"
      by simp
  qed
qed

typedef (overloaded) ('a::chilbert_space) compact
  = \<open>{f :: 'a bounded. \<exists> g::nat \<Rightarrow> 'a bounded.
 (\<forall> n. finite_complex_rank_complex_bouded (g n)) \<and> (g \<longlonglongrightarrow> f)}\<close>
  apply auto
proof
  define x where \<open>x = (0::'a bounded)\<close>
  show "\<exists>g. (\<forall>n. finite_complex_rank_complex_bouded (g n)) \<and> g \<longlonglongrightarrow> x"
  proof
    define g where \<open>g = (\<lambda> _::nat. (0::'a bounded))\<close>
    show "(\<forall>n. finite_complex_rank_complex_bouded (g n)) \<and> g \<longlonglongrightarrow> x"
      apply auto
      unfolding g_def
       apply auto
       apply transfer
       apply transfer
      unfolding finite_complex_rank_def
    proof-
      show \<open>\<exists>n. complex_gen n (\<lambda>x. 0)\<close>
      proof
        show "complex_gen 0 (\<lambda>x. 0)"
          by simp
      qed
      show \<open>(\<lambda>_. 0) \<longlonglongrightarrow> x\<close>
        unfolding x_def
        by simp
    qed
  qed
qed



end
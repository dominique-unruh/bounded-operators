section \<open>TODO: section title\<close>

(* Title:      Bounded-Operators/linear_complex_structure.thy
   Author:     Dominique Unruh, University of Tartu
   Author:     Jose Manuel Rodriguez Caballero, University of Tartu

References:

@book{conway2013course,
title={A course in functional analysis},
author={Conway, John B},
volume={96},
year={2013},
publisher={Springer Science \& Business Media}
}

*)

theory Linear_Complex_Structure
  imports Complex_Vector_Spaces

begin


(* NEW *)
subsection \<open>A complex vector space from a real vector space\<close>
(*
Linear complex structure

https://en.wikipedia.org/wiki/Linear_complex_structure

Complexification

https://en.wikipedia.org/wiki/Complexification
*)

typedef (overloaded) ('a::real_vector) complexification
  = \<open>{z::'a*'a. True}\<close>
  by blast

setup_lifting type_definition_complexification

instantiation complexification :: (real_vector) real_vector begin
lift_definition zero_complexification :: "'a complexification" is "(0::'a,0::'a)::'a*'a" 
  by blast    
lift_definition uminus_complexification :: "'a complexification \<Rightarrow> 'a complexification" is "(\<lambda> x. (- fst x, - snd x))"
  by blast
lift_definition plus_complexification :: "'a complexification \<Rightarrow> 'a complexification \<Rightarrow> 'a complexification" 
  is "\<lambda>f g. (fst f + fst g, snd f + snd g)"
  by blast
lift_definition minus_complexification :: "'a complexification \<Rightarrow> 'a complexification \<Rightarrow> 'a complexification" 
  is "\<lambda>f g. (fst f - fst g, snd f - snd g)" by blast
lift_definition scaleR_complexification :: "real \<Rightarrow> 'a complexification \<Rightarrow> 'a complexification" 
  is "\<lambda>r f. (r *\<^sub>R fst f, r  *\<^sub>R  snd f)"
  by blast

instance apply intro_classes
          apply transfer 
          apply simp
         apply transfer 
         apply simp
        apply transfer 
        apply simp
       apply transfer 
       apply simp
      apply transfer 
      apply simp
     apply transfer 
     apply simp
     apply transfer 
     apply (simp add: scaleR_add_right)
    apply transfer 
    apply simp
    apply transfer 
    apply (simp add: scaleR_add_left)
   apply transfer 
   apply simp
  apply transfer
  apply simp
  done
end

lift_definition prodC::\<open>complex \<Rightarrow> ('a::real_vector) complexification \<Rightarrow> 'a complexification\<close>  (infixr "\<cdot>\<^sub>C" 75) is
\<open>\<lambda> c::complex. \<lambda> z::'a*'a. (Re c *\<^sub>R fst z - Im c *\<^sub>R snd z, Im c *\<^sub>R fst z + Re c *\<^sub>R snd z )\<close> 
  by blast

lemma prodC_one:
\<open>(1::complex) \<cdot>\<^sub>C z = z\<close>
  apply transfer
  by simp

lemma prodC_add_right:
\<open>a \<cdot>\<^sub>C (x + y) = a \<cdot>\<^sub>C x + a \<cdot>\<^sub>C y\<close>
  apply transfer
  by (simp add: scaleR_add_right)

lemma prodC_add_left:
\<open>(a + b) \<cdot>\<^sub>C x = a \<cdot>\<^sub>C x + b \<cdot>\<^sub>C x\<close>
  apply transfer
  by (simp add: add.commute add.left_commute add_diff_eq scaleR_add_left)

lemma prodC_prodC:
\<open>a \<cdot>\<^sub>C b \<cdot>\<^sub>C x = (a * b) \<cdot>\<^sub>C x\<close>
  apply transfer
  apply auto
proof-
  fix a b :: complex and  aa ba :: 'a 
  show \<open>Re a *\<^sub>R (Re b *\<^sub>R aa - Im b *\<^sub>R ba) -
       Im a *\<^sub>R (Im b *\<^sub>R aa + Re b *\<^sub>R ba) =
       (Re a * Re b - Im a * Im b) *\<^sub>R aa -
       (Re a * Im b + Im a * Re b) *\<^sub>R ba\<close>
    using scaleR_add_right scaleR_add_left scaleR_scaleR
    by (smt add.commute add.left_commute add_diff_cancel_right diff_add_cancel diff_diff_add scale_right_diff_distrib)

  fix a b :: complex and  aa ba :: 'a
    show \<open> Im a *\<^sub>R (Re b *\<^sub>R aa - Im b *\<^sub>R ba) +
       Re a *\<^sub>R (Im b *\<^sub>R aa + Re b *\<^sub>R ba) =
       (Re a * Im b + Im a * Re b) *\<^sub>R aa +
       (Re a * Re b - Im a * Im b) *\<^sub>R ba\<close>
    using scaleR_add_right scaleR_add_left scaleR_scaleR
    by (smt add.commute add.left_commute add_diff_cancel_right diff_add_cancel diff_diff_add scale_right_diff_distrib)
qed

lemma complex_of_real_prod:
  fixes a::real 
  shows \<open> a *\<^sub>R x = (complex_of_real a) \<cdot>\<^sub>C x\<close>
  apply transfer
  by simp

(* NEW *)
instantiation complexification :: (real_vector) complex_vector
begin
lift_definition scaleC_complexification :: \<open>complex \<Rightarrow> 'a complexification \<Rightarrow> 'a complexification\<close> 
  is \<open>prodC\<close> .
instance
  apply intro_classes
  proof
  show "r *\<^sub>R (x::'a complexification) = complex_of_real r *\<^sub>C x"
    for r :: real
      and x :: "'a complexification"
    apply transfer
    by (rule complex_of_real_prod)

  show "a *\<^sub>C ((x::'a complexification) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a complexification"
      and y :: "'a complexification"
    apply transfer
    by (rule prodC_add_right)

  show "(a + b) *\<^sub>C (x::'a complexification) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a complexification"
    apply transfer
    by (rule prodC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::'a complexification) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a complexification"
    apply transfer
    by (rule prodC_prodC)

  show "1 *\<^sub>C (x::'a complexification) = x"
    for x :: "'a complexification"
    apply transfer
    by (rule prodC_one)
qed
end


end

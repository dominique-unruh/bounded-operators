section \<open>Hamming weight and quantum superposition\<close>

(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

theory Hamming_Weight
  imports Complex_L2

begin

text\<open>Hamming weight of a string\<close>
fun Hamming_w :: \<open>'a::zero list \<Rightarrow> nat\<close> where
  \<open>Hamming_w [] = 0\<close> |
  \<open>Hamming_w (a # L) = Hamming_w L + (if a = 0 then 0 else 1)\<close>

text \<open>Example of calculation\<close>
value \<open>Hamming_w ([0, 1, 0, 0, 1, 0, 0, 1]::int list)\<close>

text \<open>Explicit formula for Hamming_w\<close>
lemma Hamming_w_explicit: 
  \<open>Hamming_w L = (\<Sum> i<length L. (if L!i = 0 then 0 else 1))\<close>
proof(induction \<open>length L\<close> arbitrary: L)
  case 0
  hence \<open>L = ([]::'a list)\<close>
    by auto
  moreover have \<open>Hamming_w ([]::'a list) = 0\<close>
    by simp
  moreover have \<open>(\<Sum> i<length ([]::'a list). (if L!i = 0 then 0 else 1)) = 0\<close>
    by simp
  ultimately show ?case by auto
next
  case (Suc n)
  hence \<open>\<exists> L' a. L = a # L'\<close>
    by (meson Suc_length_conv)
  then obtain L' a where \<open>L = a # L'\<close>
    by blast
  hence \<open>i<length L' \<Longrightarrow> L'!i = L!(Suc i)\<close>
    for i
    by simp
  have \<open>Hamming_w L = Hamming_w L' + (if a = 0 then 0 else 1)\<close>
    using \<open>L = a # L'\<close>
    by simp
  moreover have \<open>(\<Sum> i<length L. (if L!i = 0 then 0 else 1)) 
    = (\<Sum> i<length L'. (if L'!i = 0 then 0 else 1)) + (if a = 0 then 0 else 1)\<close>
  proof-
    have \<open>(\<Sum> i<length L. (if L!i = 0 then 0 else 1)) 
        = (\<Sum> i<length (a # L'). (if L!i = 0 then 0 else 1))\<close>
      using \<open>L = a # L'\<close> by blast
    also have \<open>... 
        = (if a = 0 then 0 else 1)
          + (\<Sum> i\<in>{1..length (a # L')-1}. (if L!i = 0 then 0 else 1))\<close>
      by (metis (no_types, lifting) Suc.hyps(2) \<open>L = a # L'\<close> add_diff_cancel_left' nth_Cons_0 plus_1_eq_Suc sum.lessThan_Suc_shift sum_bounds_lt_plus1)
    also have \<open>... 
        = (if a = 0 then 0 else 1)
          + (\<Sum> i\<in>{1..length L'}. (if L!i = 0 then 0 else 1))\<close>
      by simp
    also have \<open>... 
        = (if a = 0 then 0 else 1)
          + (\<Sum> i<length L'. (if L!(Suc i) = 0 then 0 else 1))\<close>
      using Binomial.sum_bounds_lt_plus1[where mm = "length L'" 
          and f = "\<lambda> i. (if L!i = 0 then 0 else 1)"]
      by (simp add: \<open>(\<Sum>k<length L'. if L ! Suc k = 0 then 0 else 1) = (\<Sum>k = 1..length L'. if L ! k = 0 then 0 else 1)\<close>)
    also have \<open>... 
        = (if a = 0 then 0 else 1)
          + (\<Sum> i<length L'. (if L'!i = 0 then 0 else 1))\<close>
      using \<open>\<And>i. i < length L' \<Longrightarrow> L' ! i = L ! Suc i\<close> by auto
    finally show ?thesis
      by (simp add: ordered_field_class.sign_simps(2)) 
  qed
  moreover have \<open>Hamming_w L' = (\<Sum> i<length L'. (if L'!i = 0 then 0 else 1))\<close>
  proof-
    have \<open>n = length L'\<close>
      using  \<open>L = a # L'\<close> Suc.hyps(2) by auto
    hence \<open>Hamming_w L' = (\<Sum> i<length L'. (if L'!i = 0 then 0 else 1))\<close>
      using Suc.hyps(1)[where L = \<open>L'\<close>]
      by blast      
    thus ?thesis
      by auto 
  qed
  ultimately show ?case
    by (simp add: \<open>(\<Sum>i<length L. if L ! i = 0 then 0 else 1) = (\<Sum>i<length L'. if L' ! i = 0 then 0 else 1) + (if a = 0 then 0 else 1)\<close>)    
qed


text\<open>Hamming relative weight of a string\<close>
definition Hamming_rel_w :: \<open>'a::zero list \<Rightarrow> real\<close> where
  \<open>Hamming_rel_w L = (Hamming_w L) / (length L)\<close>

text \<open>Example of calculation\<close>
value \<open>Hamming_rel_w ([0, 1, 0, 0, 1, 0, 0, 1]::int list)\<close>

text\<open>Hamming relative weight of a ket\<close>
definition Hamming_rel_w_ket :: \<open>('a::zero list) ell2 \<Rightarrow> real\<close> where
  \<open>Hamming_rel_w_ket b = (if (\<exists> s. b = ket s)  
  then Hamming_rel_w (SOME s. b = ket s)
  else 0)\<close>

text\<open>Identification of "False" with "zero"\<close>
instantiation bool::zero
begin
definition zero_bool::bool where \<open>zero_bool = False\<close>
instance..
end

text\<open>Superposition of states delta-close to \<beta>\<close>

fun boolean_cube :: \<open>nat \<Rightarrow> (bool list) set\<close> where
\<open>boolean_cube 0 = {[]}\<close> |
\<open>boolean_cube (Suc n) = (\<lambda> x. False # x) ` (boolean_cube n)
                      \<union>  (\<lambda> x. True # x) ` (boolean_cube n)\<close>

text \<open>Example of calculation:boolean cube\<close>
value \<open>boolean_cube 5\<close>

definition Hamming_ball :: \<open>nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (bool list) set\<close> where
\<open>Hamming_ball n \<beta> \<delta> = ((\<lambda> x. (if \<bar>Hamming_rel_w x - \<beta>\<bar> \<le> \<delta>  then x else []) ) ` (boolean_cube n))-{[]}\<close>

text \<open>Example of calculation: strings 0.1-close to 0.3 Hamming weight\<close>
value \<open>Hamming_ball 5 0.3 0.1\<close>

text \<open>Example of calculation: the Hamming weights\<close>
value \<open>Hamming_rel_w ` (Hamming_ball 5 0.3 0.1)\<close>

definition Hamming_superposition :: \<open>nat \<Rightarrow> real \<Rightarrow> real \<Rightarrow> (bool list) ell2\<close> where
  \<open>Hamming_superposition n \<beta> \<delta> = (\<Sum> b\<in>Hamming_ball n \<beta> \<delta>. ket b)\<close>

text \<open>Example of calculation: coefficient 1\<close>
value \<open>Rep_ell2 (Hamming_superposition 5 0.3 0.1) [False, True, True, False, False]\<close>

text \<open>Example of calculation: coefficient 0\<close>
value \<open>Rep_ell2 (Hamming_superposition 5 0.3 0.1) [False, False, False, False, False]\<close>

end

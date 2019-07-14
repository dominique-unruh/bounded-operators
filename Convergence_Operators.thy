(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Several definitions of convergence of families of operators.

*)

theory Convergence_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL.Real_Vector_Spaces"
    "HOL-Analysis.Operator_Norm"
begin

section \<open>Pointwise convergence\<close>

definition strong_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>strong_convergence f l = ( \<forall> x. ( \<lambda> n. norm (f n x - l x) ) \<longlonglongrightarrow> 0 )\<close>

abbreviation strong_convergence_abbr:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  (\<open>((_)/ \<midarrow>strong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>strong\<rightarrow> l \<equiv> ( strong_convergence f l )\<close>

definition onorm_convergence::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>onorm_convergence f l = ( ( \<lambda> n. onorm (\<lambda> x. f n x - l x) ) \<longlonglongrightarrow> 0 )\<close>

section \<open>Convergence with respect to the operator norm\<close>

abbreviation onorm_convergence_abbr::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>  (\<open>((_)/ \<midarrow>onorm\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>onorm\<rightarrow> l \<equiv> ( onorm_convergence f l )\<close>

definition oCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>oCauchy f = ( \<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e )\<close>

section \<open>Uniform convergence on the unit sphere\<close>

definition ustrong_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close> where 
  \<open>ustrong_convergence f l = ( \<forall> e > 0. \<exists> N. \<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e )\<close>

abbreviation ustrong_convergence_abbr::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>  (\<open>((_)/ \<midarrow>ustrong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>ustrong\<rightarrow> l \<equiv> ( ustrong_convergence f l )\<close>

definition uCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>uCauchy f = ( \<forall> e > 0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall> x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e )\<close>


end
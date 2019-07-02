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
    SEQ_bounded_operators
begin


section "Real bounded operators"

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

definition uniformity_real_bounded :: \<open>( ('a, 'b) real_bounded \<times> ('a, 'b) real_bounded ) filter\<close>
  where  \<open>uniformity_real_bounded = (INF e:{0<..}. principal {((f::('a, 'b) real_bounded), g). dist f g < e})\<close>

definition open_real_bounded :: \<open>(('a, 'b) real_bounded) set \<Rightarrow> bool\<close>
  where \<open>open_real_bounded = (\<lambda> U::(('a, 'b) real_bounded) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity))\<close>

instance
  apply intro_classes
        apply transfer
        apply auto
         apply transfer
         apply auto
        apply (simp add: real_bounded_operators.uniformity_real_bounded_def)
       apply (simp add: open_real_bounded_def)
      apply (simp add: open_real_bounded_def)
     apply transfer
  using onorm_pos_lt apply fastforce
    apply transfer
    apply (simp add: onorm_zero)
   apply transfer
   apply (simp add: onorm_triangle)
  apply transfer
  using onorm_scaleR by blast 
end

subsection \<open>Sequence of operators, bounded in norm\<close>

(* This subsection was just an exercise in order to practive typedef and lift_definition *)

typedef (overloaded) ('a::real_normed_vector, 'b::real_normed_vector) real_bounded_SEQ_bounded_pointwise
  = \<open>{f :: nat \<Rightarrow> ('a, 'b) real_bounded. \<forall> x::'a. bdd_above { norm ( ev_real_bounded (f n) x ) | n. True } }\<close>
  apply transfer
proof
  show \<open>(\<lambda> n::nat. (\<lambda> _::'a. 0::'b)) \<in> {f. (\<forall>x. bdd_above {norm (f n x) |n. True}) \<and> pred_fun top bounded_linear f}\<close>
    apply auto.
  show \<open>(\<lambda> n::nat. (\<lambda> _::'a. 0::'b)) \<in> Collect (pred_fun top bounded_linear)\<close>
    apply auto.
qed

setup_lifting type_definition_real_bounded_SEQ_bounded_pointwise

lift_definition index_real_bounded :: 
  \<open>('a::real_normed_vector, 'b::real_normed_vector) real_bounded_SEQ_bounded_pointwise \<Rightarrow> nat 
\<Rightarrow> ('a, 'b) real_bounded\<close> is \<open>\<lambda> f::nat \<Rightarrow> ('a, 'b) real_bounded. \<lambda> n::nat. f n\<close>.

lift_definition norm_SEQ_real_bounded :: 
  \<open>('a::real_normed_vector, 'b::real_normed_vector) real_bounded_SEQ_bounded_pointwise \<Rightarrow> (nat 
\<Rightarrow> real)\<close> is \<open>\<lambda> f::nat \<Rightarrow> ('a, 'b) real_bounded. \<lambda> n::nat. norm (f n)\<close>.

typedef (overloaded) ('a::metric_space) bounded_SEQ
  = \<open>{f :: nat \<Rightarrow> 'a.  bounded { f n | n. True } }\<close>
proof-
  have \<open>\<exists> x. x \<in> (UNIV :: 'a set)\<close>
    by simp
  then obtain x where \<open>x \<in> (UNIV :: 'a set)\<close>
    by blast
  hence \<open>bounded {x}\<close>
    by simp    
  hence \<open>bounded {(\<lambda> _::nat. x) n |n. True}\<close>
    by simp
  hence \<open>(\<lambda> _::nat. x) \<in> {f. bounded {f n |n. True}}\<close>
    by simp
  thus ?thesis 
    by meson 
qed

setup_lifting type_definition_bounded_SEQ

corollary Banach_Steinhaus_coro:
  fixes f :: \<open>nat \<Rightarrow> ('a::{banach,perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close>
  shows \<open>\<forall>n. bounded_linear (f n)
\<Longrightarrow> \<forall> x. bdd_above {norm ((f n) x) | n. True}
\<Longrightarrow> bounded {onorm (f n) | n. True}\<close>
proof-
  assume \<open>\<forall>n. bounded_linear (f n)\<close>
  hence  \<open>\<And> n. bounded_linear (f n)\<close>
    by blast
  assume \<open>\<forall> x. bdd_above {norm ((f n) x) | n. True}\<close>
  hence \<open>\<And> x. \<exists> M. \<forall> n.  norm ((f n) x) \<le> M\<close>
    using bdd_above_def
    by (metis (mono_tags) mem_Collect_eq)
  have  \<open>\<exists> M. \<forall> n. onorm (f n) \<le> M\<close>
    using  \<open>\<And> n. bounded_linear (f n)\<close> \<open>\<And> x. \<exists> M. \<forall> n.  norm ((f n) x) \<le> M\<close>  
    by (rule Banach_Steinhaus)
  then obtain M where \<open>\<forall> n. onorm (f n) \<le> M\<close> by blast
  have \<open>y\<in>{onorm (f n) |n. True} \<Longrightarrow> \<bar>y\<bar> \<le> M\<close>
    for y
  proof-
    assume \<open>y\<in>{onorm (f n) |n. True}\<close>
    hence \<open>\<exists> n. y = onorm (f n)\<close>
      by blast
    then obtain n where \<open>y = onorm (f n)\<close> by blast
    hence \<open>y \<ge> 0\<close>
      by (simp add: \<open>\<forall>n. bounded_linear (f n)\<close> onorm_pos_le)  
    thus ?thesis using \<open>\<forall> n. onorm (f n) \<le> M\<close>
      by (simp add: \<open>y = onorm (f n)\<close>)      
  qed
  hence \<open>\<forall>y\<in>{onorm (f n) |n. True}. dist 0 y \<le> M\<close>
    by simp
  thus ?thesis unfolding bounded_def 
    by blast
qed

lift_definition Banach_Steinhaus_real_bounded::
  \<open>('a::{banach,perfect_space}, 'b::real_normed_vector) real_bounded_SEQ_bounded_pointwise \<Rightarrow>
real bounded_SEQ\<close> 
  is \<open>\<lambda> f. (\<lambda> n::nat. norm (f n))\<close>
  apply transfer   
  apply auto
  using Banach_Steinhaus_coro
  by auto

subsection \<open>Convergence\<close>

lift_definition strong_convergence_real_bounded:: "(nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded) \<Rightarrow> (('a, 'b) real_bounded) \<Rightarrow> bool"
  is \<open>\<lambda> f. \<lambda> l. f \<midarrow>strong\<rightarrow> l\<close>.

abbreviation
  strong_convergence_real_bounded_abbr :: "(nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded) \<Rightarrow> (('a, 'b) real_bounded ) \<Rightarrow> bool"  ("((_)/ \<midarrow>STRONG\<rightarrow> (_))" [60, 60] 60)
  where "f \<midarrow>STRONG\<rightarrow> l \<equiv> (strong_convergence_real_bounded f l ) "

lift_definition onorm_convergence_real_bounded:: "(nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded) \<Rightarrow> (('a, 'b) real_bounded) \<Rightarrow> bool"
  is \<open>\<lambda> f. \<lambda> l. f \<midarrow>onorm\<rightarrow> l\<close>.

abbreviation
  onorm_convergence_real_bounded_abbr :: "(nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded) \<Rightarrow> (('a, 'b) real_bounded ) \<Rightarrow> bool"  ("((_)/ \<midarrow>ONORM\<rightarrow> (_))" [60, 60] 60)
  where "f \<midarrow>ONORM\<rightarrow> l \<equiv> (onorm_convergence_real_bounded f l ) "

lemma ONORM_tendsto_real_bounded:
  \<open>f \<midarrow>ONORM\<rightarrow> l \<Longrightarrow> f \<longlonglongrightarrow> l\<close>
  apply transfer
proof
  show "f \<midarrow>ONORM\<rightarrow> (l::('a, 'b) real_bounded) \<Longrightarrow> e > 0 \<Longrightarrow> \<forall>\<^sub>F x in sequentially. dist (f x) (l::('a, 'b) real_bounded) < e"   
    for f :: "nat \<Rightarrow> ('a, 'b) real_bounded"
      and l :: "('a, 'b) real_bounded"
      and e :: real
    apply transfer
    apply auto
    by (rule onorm_tendsto)    
qed

lemma tendsto_ONORM_real_bounded:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) real_bounded\<close>
    and l :: \<open>('a, 'b) real_bounded\<close>
  shows \<open>f \<longlonglongrightarrow> l \<Longrightarrow> f \<midarrow>ONORM\<rightarrow> l\<close>
proof-
  assume \<open>f \<longlonglongrightarrow> l\<close>
  hence \<open>(\<lambda> n. dist (f n) l) \<longlonglongrightarrow> 0\<close>
    using  Real_Vector_Spaces.tendsto_dist_iff
    by blast
  hence \<open>f \<midarrow>ONORM\<rightarrow> l\<close>
    apply transfer
    apply auto
    unfolding onorm_convergence_def
    by simp
  thus ?thesis by blast
qed

instantiation real_bounded :: (real_normed_vector, banach) "banach"
begin
instance
proof
  show "Cauchy f \<Longrightarrow> convergent f"
    for f :: "nat \<Rightarrow> ('a, 'b) real_bounded"
    unfolding Cauchy_def convergent_def 
  proof-
    show \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m) (f n) < e \<Longrightarrow> \<exists>L. f \<longlonglongrightarrow> L\<close>
    proof-
      assume \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m) (f n) < e\<close>
      hence \<open>\<exists>l. bounded_linear l \<and> (\<lambda>n. onorm (\<lambda>x. (Rep_real_bounded (f n)) x - l x)) \<longlonglongrightarrow> 0\<close>
        apply transfer
        apply auto
        using completeness_real_bounded 
        apply smt.
      then obtain l
        where \<open> bounded_linear l \<and> (\<lambda>n. onorm (\<lambda>x. (Rep_real_bounded (f n)) x - l x)) \<longlonglongrightarrow> 0\<close>
        by blast
      have \<open>bounded_linear l\<close>
        using \<open> bounded_linear l \<and> (\<lambda>n. onorm (\<lambda>x. (Rep_real_bounded (f n)) x - l x)) \<longlonglongrightarrow> 0\<close> 
        by blast
      hence \<open>\<exists> L. Rep_real_bounded L = l\<close>
        apply transfer
        by auto
      then obtain L::\<open>('a, 'b) real_bounded\<close> where \<open>Rep_real_bounded L = l\<close> by blast
      have \<open>(\<lambda>n. onorm (\<lambda>x. (Rep_real_bounded (f n)) x - l x)) \<longlonglongrightarrow> 0\<close>
        using \<open> bounded_linear l \<and> (\<lambda>n. onorm (\<lambda>x. (Rep_real_bounded (f n)) x - l x)) \<longlonglongrightarrow> 0\<close> 
        by blast
      hence \<open>(\<lambda>n. onorm (\<lambda>x. (Rep_real_bounded (f n)) x - (Rep_real_bounded L) x)) \<longlonglongrightarrow> 0\<close>
        using  \<open>Rep_real_bounded L = l\<close> by blast
      hence \<open>(\<lambda>n. Rep_real_bounded (f n)) \<midarrow>onorm\<rightarrow> (Rep_real_bounded L)\<close>
        using onorm_convergence_def
        by blast
      hence \<open>f \<midarrow>ONORM\<rightarrow> L\<close>
        unfolding onorm_convergence_real_bounded_def
        apply auto
        unfolding map_fun_def
        apply simp
        unfolding comp_def
        by auto
      hence \<open>f \<longlonglongrightarrow> L\<close>
        using ONORM_tendsto_real_bounded
        by auto
      thus ?thesis by blast
    qed
  qed
qed  
end



end
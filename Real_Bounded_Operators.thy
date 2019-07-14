(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Definition of the type rbounded

*)

theory Real_Bounded_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    SEQ_bounded_operators
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
  by (rule Bounded_Linear_Function.bounded_linear_intros(6))

instance
proof      
  fix a b c :: \<open>('a, 'b) rbounded\<close>
  show \<open>a + b + c = a + (b + c)\<close>
    apply Transfer.transfer by auto
  fix a b :: \<open>('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close>
  show \<open>a + b = b + a\<close>
    apply Transfer.transfer
    by (simp add: linordered_field_class.sign_simps(2))

  fix a :: \<open>('a, 'b) rbounded\<close>
  show \<open>0 + a = a\<close>
    apply Transfer.transfer by simp

  fix a :: \<open>('a, 'b) rbounded\<close>
  show \<open>-a + a = 0\<close>
    apply Transfer.transfer
    by simp

  fix a b :: \<open>('a, 'b) rbounded\<close>
  show \<open>a - b = a + - b\<close>
    apply Transfer.transfer
    by auto
  fix a::real and x y :: \<open>('a, 'b) rbounded\<close>
  show \<open>a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y\<close>
    apply Transfer.transfer
    by (simp add: pth_6)

  fix a b :: real and x :: \<open>('a, 'b) rbounded\<close>
  show \<open>(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x\<close>
    apply Transfer.transfer
    by (simp add: scaleR_add_left)

  fix a b :: real and x :: \<open>('a, 'b) rbounded\<close>
  show \<open>a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x\<close>
    apply Transfer.transfer
    by simp

  fix x :: \<open>('a, 'b) rbounded\<close>
  show \<open>1 *\<^sub>R x = x\<close>
    apply Transfer.transfer
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
  by (rule Bounded_Linear_Function.bounded_linear_intros(6))

definition uniformity_rbounded :: \<open>( ('a, 'b) rbounded \<times> ('a, 'b) rbounded ) filter\<close>
  where  \<open>uniformity_rbounded = (INF e:{0<..}. principal {((f::('a, 'b) rbounded), g). dist f g < e})\<close>

definition open_rbounded :: \<open>(('a, 'b) rbounded) set \<Rightarrow> bool\<close>
  where \<open>open_rbounded = (\<lambda> U::(('a, 'b) rbounded) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity))\<close>

instance
  apply intro_classes
        apply Transfer.transfer
        apply auto
         apply Transfer.transfer
         apply auto
        apply (simp add: Real_Bounded_Operators.uniformity_rbounded_def)
       apply (simp add: open_rbounded_def)
      apply (simp add: open_rbounded_def)
     apply Transfer.transfer
  using onorm_pos_lt apply fastforce
    apply Transfer.transfer
    apply (simp add: onorm_zero)
   apply Transfer.transfer
   apply (simp add: onorm_triangle)
  apply Transfer.transfer
  using onorm_scaleR by blast 
end

subsection \<open>Convergence\<close>

lift_definition strong_convergence_rbounded:: "(nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded) \<Rightarrow> (('a, 'b) rbounded) \<Rightarrow> bool"
  is \<open>\<lambda> f. \<lambda> l. f \<midarrow>strong\<rightarrow> l\<close>.

abbreviation
  strong_convergence_rbounded_abbr :: "(nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded) \<Rightarrow> (('a, 'b) rbounded ) \<Rightarrow> bool"  ("((_)/ \<midarrow>STRONG\<rightarrow> (_))" [60, 60] 60)
  where "f \<midarrow>STRONG\<rightarrow> l \<equiv> (strong_convergence_rbounded f l ) "

lift_definition onorm_convergence_rbounded:: "(nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded) \<Rightarrow> (('a, 'b) rbounded) \<Rightarrow> bool"
  is \<open>\<lambda> f. \<lambda> l. f \<midarrow>onorm\<rightarrow> l\<close>.

abbreviation
  onorm_convergence_rbounded_abbr :: "(nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded) \<Rightarrow> (('a, 'b) rbounded ) \<Rightarrow> bool"  ("((_)/ \<midarrow>ONORM\<rightarrow> (_))" [60, 60] 60)
  where "f \<midarrow>ONORM\<rightarrow> l \<equiv> (onorm_convergence_rbounded f l ) "

lemma ONORM_tendsto_rbounded:
  \<open>f \<midarrow>ONORM\<rightarrow> l \<Longrightarrow> f \<longlonglongrightarrow> l\<close>
  apply Transfer.transfer
proof
  show "f \<midarrow>ONORM\<rightarrow> (l::('a, 'b) rbounded) \<Longrightarrow> e > 0 \<Longrightarrow>
 \<forall>\<^sub>F x in sequentially. dist (f x) (l::('a, 'b) rbounded) < e"   
    for f :: "nat \<Rightarrow> ('a, 'b) rbounded"
      and l :: "('a, 'b) rbounded"
      and e :: real
    apply Transfer.transfer
    apply auto
    by (rule onorm_tendsto)    
qed

lemma tendsto_ONORM_rbounded:
  fixes f :: \<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close>
    and l :: \<open>('a, 'b) rbounded\<close>
  shows \<open>f \<longlonglongrightarrow> l \<Longrightarrow> f \<midarrow>ONORM\<rightarrow> l\<close>
proof-
  assume \<open>f \<longlonglongrightarrow> l\<close>
  hence \<open>(\<lambda> n. dist (f n) l) \<longlonglongrightarrow> 0\<close>
    using  Real_Vector_Spaces.tendsto_dist_iff
    by blast
  hence \<open>f \<midarrow>ONORM\<rightarrow> l\<close>
    apply Transfer.transfer
    apply auto
    unfolding onorm_convergence_def
    by simp
  thus ?thesis by blast
qed

lemma ONORM_STRONG:
  \<open>f \<midarrow>ONORM\<rightarrow> l \<Longrightarrow> f \<midarrow>STRONG\<rightarrow> l\<close>
  apply Transfer.transfer
  apply auto
  by (rule onorm_strong)

instantiation rbounded :: ("{real_normed_vector, perfect_space}", banach) "banach"
begin
instance
proof
  show "Cauchy f \<Longrightarrow> convergent f"
    for f :: "nat \<Rightarrow> ('a, 'b) rbounded"
    unfolding Cauchy_def convergent_def 
  proof-
    show \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m) (f n) < e \<Longrightarrow> \<exists>L. f \<longlonglongrightarrow> L\<close>
    proof-
      assume \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m) (f n) < e\<close>
      hence \<open>\<exists>l. bounded_linear l \<and> (\<lambda> n. Rep_rbounded (f n)) \<midarrow>onorm\<rightarrow> l\<close>
        apply Transfer.transfer
        apply auto
        using completeness_real_bounded oCauchy_def onorm_convergence_def
        by blast 
      then obtain l
        where \<open>bounded_linear l \<and> (\<lambda> n. Rep_rbounded (f n)) \<midarrow>onorm\<rightarrow> l\<close>
        by blast
      have \<open>bounded_linear l\<close>
        using \<open>bounded_linear l \<and> (\<lambda> n. Rep_rbounded (f n)) \<midarrow>onorm\<rightarrow> l\<close> 
        by blast
      hence \<open>\<exists> L. Rep_rbounded L = l\<close>
        apply Transfer.transfer
        by auto
      then obtain L::\<open>('a, 'b) rbounded\<close> where \<open>Rep_rbounded L = l\<close> by blast
      have \<open>(\<lambda> n. Rep_rbounded (f n)) \<midarrow>onorm\<rightarrow> l\<close>
        using  \<open>bounded_linear l \<and> (\<lambda> n. Rep_rbounded (f n)) \<midarrow>onorm\<rightarrow> l\<close>  
        by blast
      hence \<open>(\<lambda> n. Rep_rbounded (f n)) \<midarrow>onorm\<rightarrow> l\<close>
        using  \<open>Rep_rbounded L = l\<close> by blast
      hence \<open>(\<lambda>n. Rep_rbounded (f n)) \<midarrow>onorm\<rightarrow> (Rep_rbounded L)\<close>
        using  \<open>Rep_rbounded L = l\<close> by blast
      hence \<open>f \<midarrow>ONORM\<rightarrow> L\<close>
        unfolding onorm_convergence_rbounded_def
        apply auto
        unfolding map_fun_def
        apply simp
        unfolding comp_def
        by auto
      hence \<open>f \<longlonglongrightarrow> L\<close>
        using ONORM_tendsto_rbounded
        by auto
      thus ?thesis by blast
    qed
  qed
qed  

end



end

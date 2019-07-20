(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Several definitions of convergence of families of operators.

Main results:
- completeness_real_bounded: A sufficient condition for the completeness of a sequence of
 bounded operators.

*)

theory Convergence_Operators
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL.Real_Vector_Spaces"
    Operator_Norm_Missing
    Uniform_Limit_Missing

begin

section \<open>rbounded\<close>

section \<open>Real bounded operators\<close>

typedef (overloaded) ('a::real_normed_vector, 'b::real_normed_vector) rbounded
  = \<open>{f::'a \<Rightarrow> 'b. bounded_linear f}\<close>
  using bounded_linear_zero by blast

setup_lifting type_definition_rbounded

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
        apply (simp add: uniformity_rbounded_def)
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



section \<open>Pointwise convergence\<close>

definition pointwise_convergence:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>pointwise_convergence f l = ( \<forall> x. ( \<lambda> n. f n x ) \<longlonglongrightarrow> l x )\<close>

abbreviation pointwise_convergence_abbr:: 
  \<open>(nat \<Rightarrow> ('a::real_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  (\<open>((_)/ \<midarrow>strong\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>strong\<rightarrow> l \<equiv> ( pointwise_convergence f l )\<close>

section \<open>Convergence with respect to the operator norm\<close>

(*
definition onorm_convergence::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>
  where \<open>onorm_convergence f l = ( ( \<lambda> n. onorm (\<lambda> x. f n x - l x) ) \<longlonglongrightarrow> 0 )\<close>

abbreviation onorm_convergence_abbr::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow>'b::real_normed_vector)) \<Rightarrow> ('a\<Rightarrow>'b) \<Rightarrow> bool\<close>  (\<open>((_)/ \<midarrow>onorm\<rightarrow> (_))\<close> [60, 60] 60)
  where \<open>f \<midarrow>onorm\<rightarrow> l \<equiv> ( onorm_convergence f l )\<close>

definition oCauchy::
  \<open>(nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)) \<Rightarrow> bool\<close>
  where \<open>oCauchy f = ( \<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e )\<close>

*)

section \<open>Relationships among the different kind of convergence\<close>

lemma ustrong_onorm:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> and l::\<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>\<And> n. bounded_linear (f n)\<close> and \<open>bounded_linear l\<close> and \<open>sphere 0 1: f \<midarrow>uniformly\<rightarrow> l\<close>
  shows \<open>( \<lambda> n. onorm (\<lambda> x. f n x - l x) ) \<longlonglongrightarrow> 0\<close> 
proof(cases \<open>(UNIV::'a set) = 0\<close>)
  case True
  hence \<open>x = 0\<close>
    for x::'a
    by auto
  hence \<open>f n x = 0\<close>
    for n::nat and x::'a
    using \<open>bounded_linear (f n)\<close>
    by (metis (full_types) linear_simps(3))
  moreover have \<open>l x = 0\<close>
    for x::'a
    by (metis (full_types) \<open>\<And>x. x = 0\<close> assms(2) linear_simps(3))
  ultimately have \<open>(\<lambda> x. f n x - l x) = (\<lambda> _. 0)\<close>
    for n
    by simp
  moreover have \<open>onorm (\<lambda> _. 0::'a) = 0\<close>
    using onorm_zero by auto
  ultimately have \<open>onorm (\<lambda> x. f n x - l x) = 0\<close>
    for n
    by (simp add: onorm_eq_0)   
  thus ?thesis
    by simp     
next
  case False
  have \<open>(\<lambda>n. onorm (\<lambda>x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
  proof-
    have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N.  onorm (\<lambda>x. f n x - l x) \<le> e\<close>
      for e
    proof-
      assume \<open>e > 0\<close>
      hence \<open>\<exists> N. \<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
        using  \<open>sphere 0 1: f \<midarrow>uniformly\<rightarrow> l\<close> 
        unfolding sphere_def
        by (simp add: dist_norm uniform_limit_sequentially_iff)               
      then obtain N where \<open>\<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
        by blast
      have \<open>bounded_linear g \<Longrightarrow> \<exists> x. norm x = 1 \<and> onorm g \<le> norm (g x) + inverse (real (Suc m))\<close>
        for x::'a and g::\<open>'a \<Rightarrow> 'b\<close> and m :: nat
      proof-
        assume \<open>bounded_linear g\<close>
        hence \<open>onorm g = Sup {norm (g x) | x. norm x = 1}\<close>
          using False onorm_sphere \<open>bounded_linear g\<close>
          by auto
        have \<open>\<exists> t \<in> {norm (g x) | x. norm x = 1}. onorm g \<le>  t + inverse (real (Suc m))\<close>
        proof-
          have \<open>ereal (inverse (real (Suc m))) > 0\<close>
            by simp
          moreover have \<open>\<bar>Sup {ereal (norm (g x)) | x. norm x = 1}\<bar> \<noteq> \<infinity>\<close>
          proof-
            have \<open>\<exists> M::real. \<forall> x. norm x = 1 \<longrightarrow>  (norm (g x))  \<le> M\<close>
              by (metis \<open>bounded_linear g\<close>  bounded_linear.bounded)
            then obtain M::real where \<open>\<forall> x. norm x = 1 \<longrightarrow>  (norm (g x))  \<le> M\<close>
              by blast
            hence \<open>\<forall> x. norm x = 1 \<longrightarrow> ereal (norm (g x)) \<le> M\<close>
              by simp
            hence \<open>t \<in> {ereal (norm (g x)) | x. norm x = 1} \<Longrightarrow> t \<le> M\<close>
              for t
              by blast
            hence \<open>Sup {ereal (norm (g x)) | x. norm x = 1} \<le> M\<close>
              using Sup_least by blast
            moreover have \<open>Sup { ereal (norm (g x))  | x. norm x = 1} \<ge> 0\<close>
            proof-
              have \<open>t \<in> { ereal (norm (g x))  | x. norm x = 1} \<Longrightarrow> t \<ge> 0\<close>
                for t
                by auto                
              moreover have \<open>{ ereal (norm (g x))  | x. norm x = 1} \<noteq> {}\<close>
              proof-
                have \<open>\<exists> x::'a.  norm x = 1\<close>
                  using \<open>(UNIV::'a set) \<noteq> 0\<close> ex_norm_1
                  by blast
                thus ?thesis by blast
              qed
              ultimately show ?thesis
                by (meson less_eq_Sup) 
            qed
            ultimately have \<open>\<bar> Sup { ereal (norm (g x))  | x. norm x = 1} \<bar> \<le> M\<close>
              by simp
            thus ?thesis by auto
          qed
          moreover have \<open>{ereal(norm (g x)) | x. norm x = 1} \<noteq> {}\<close>
            by (metis Sup_empty bot.extremum_strict calculation(2) less_ereal.simps(1) lt_ex not_infty_ereal)
          ultimately have \<open>\<exists> t \<in> {ereal(norm (g x)) | x. norm x = 1}. Sup {ereal(norm (g x)) | x. norm x = 1}
               - ereal (inverse (real (Suc m))) < t\<close>
            by (rule Sup_ereal_close)
          hence \<open>\<exists> t \<in> {(norm (g x)) | x. norm x = 1}. Sup {ereal(norm (g x)) | x. norm x = 1}
               - (inverse (real (Suc m))) < t\<close>
            by auto
          then obtain t::real where \<open>t \<in> {(norm (g x)) | x. norm x = 1}\<close> 
            and \<open>Sup {ereal(norm (g x)) | x. norm x = 1}
               - (inverse (real (Suc m))) < t\<close>
            by blast
          have \<open>onorm g = Sup {ereal(norm (g x)) | x. norm x = 1}\<close>
            using \<open>onorm g = Sup {norm (g x) | x. norm x = 1}\<close>
            by simp
          also have \<open>... < t + (inverse (real (Suc m)))\<close>
            apply auto
            using \<open>Sup {ereal(norm (g x)) | x. norm x = 1} - (inverse (real (Suc m))) < t\<close>
          proof auto
            assume \<open>Sup {ereal (norm (g x)) |x. norm x = 1} - ereal (inverse (1 + real m))
                  < ereal t\<close>
            moreover have \<open>\<bar> ereal (inverse (1 + real m)) \<bar> \<noteq> \<infinity>\<close>
              by auto
            ultimately have \<open>Sup {ereal (norm (g x)) |x. norm x = 1}
                  < ereal t + ereal (inverse (1 + real m))\<close>
              using ereal_minus_less by simp               
            hence \<open>Sup {ereal (norm (g x)) |x. norm x = 1}
                  < t + (inverse (1 + real m))\<close>
              by simp
            moreover have \<open>Sup {ereal (norm (g x)) |x. norm x = 1} = 
                    Sup {(norm (g x)) |x. norm x = 1}\<close>
            proof-
              have \<open>{ereal (norm (g x)) |x. norm x = 1} = 
                    {(norm (g x)) |x. norm x = 1}\<close>
                by simp
              hence \<open>y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<in> {(norm (g x)) |x. norm x = 1}\<close>
                for y
                by simp
              moreover have \<open>{ (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (metis \<open>t \<in> {norm (g x) |x. norm x = 1}\<close> empty_iff)                
              moreover have \<open>bdd_above { (norm (g x)) |x. norm x = 1}\<close>
                by (metis (mono_tags, lifting)  \<open>bounded_linear g\<close> norm_set_bdd_above_eq1) 
              ultimately have \<open>y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {(norm (g x)) |x. norm x = 1}\<close>
                for y
                by (smt cSup_upper ereal_less_eq(3) mem_Collect_eq)
              from \<open>{ereal (norm (g x)) |x. norm x = 1} = 
                    {(norm (g x)) |x. norm x = 1}\<close>
              have \<open>y \<in> {(norm (g x)) |x. norm x = 1} \<Longrightarrow>
                   y \<in> {ereal (norm (g x)) |x. norm x = 1}\<close>
                for y
                by simp
              moreover have \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (metis \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>)                
              moreover have \<open>bdd_above {ereal (norm (g x)) |x. norm x = 1}\<close>
                by (metis (no_types, lifting) bdd_above_top) 
              ultimately have \<open>y \<in> {(norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                for y
                by (simp add: Sup_upper)
              from  \<open>\<And> y. y \<in> {ereal (norm (g x)) |x. norm x = 1}  
                  \<Longrightarrow> y \<le> Sup {(norm (g x)) |x. norm x = 1}\<close>
              have \<open>Sup {ereal (norm (g x)) |x. norm x = 1} \<le>  Sup {(norm (g x)) |x. norm x = 1}\<close>
                using \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close>
                by (meson cSup_least)
              have \<open>(Sup { (norm (g x)) |x. norm x = 1}) \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close> 
              proof-
                define X::\<open>ereal set\<close> where \<open>X = {norm (g x) |x. norm x = 1}\<close>
                define z::ereal where \<open>z = Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                have \<open>X \<noteq> {}\<close>
                  unfolding X_def
                  using \<open>{ereal (norm (g x)) |x. norm x = 1} \<noteq> {}\<close> by blast 
                moreover have \<open>\<And>x. x \<in> X \<Longrightarrow> x \<le> z\<close>
                  unfolding X_def z_def
                  by (simp add: Sup_upper)
                ultimately have \<open>Sup X \<le> z\<close>
                  by (rule cSup_least)
                hence \<open>Sup X \<le>  Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  unfolding z_def 
                  by auto
                hence \<open>real_of_ereal (Sup {norm (g x) |x. norm x = 1}) \<le>  Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  unfolding X_def 
                  by auto
                thus ?thesis
                  by (smt \<open>\<And>y. y \<in> {norm (g x) |x. norm x = 1} \<Longrightarrow> ereal y \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close> \<open>\<bar>Sup {ereal (norm (g x)) |x. norm x = 1}\<bar> \<noteq> \<infinity>\<close> \<open>{norm (g x) |x. norm x = 1} \<noteq> {}\<close> cSup_least ereal_le_real_iff) 
              qed
              show ?thesis 
                using \<open>(Sup {(norm (g x)) |x. norm x = 1}) \<le> Sup {ereal (norm (g x)) |x. norm x = 1}\<close>
                  \<open>Sup {ereal (norm (g x)) |x. norm x = 1} \<le>  Sup {(norm (g x)) |x. norm x = 1}\<close>
                by auto
            qed
            ultimately show \<open>Sup {norm (g x) |x. norm x = 1} < t + inverse (1 + real m)\<close>
              by simp
          qed
          finally have \<open>(onorm g) < t + (inverse (real (Suc m)))\<close>
            by blast
          thus ?thesis
            using \<open>t \<in> {norm (g x) |x. norm x = 1}\<close> by auto             
        qed
        thus ?thesis by auto
      qed
      hence \<open>\<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
        for n and m::nat
        using \<open>bounded_linear (f n)\<close>
        by (simp add: assms(2) bounded_linear_sub)
      hence \<open>n \<ge> N \<Longrightarrow>  onorm (\<lambda> x. f n x - l x) \<le> e\<close>
        for n
      proof-
        assume \<open>n \<ge> N\<close>
        hence  \<open>\<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          using \<open>\<forall> n \<ge> N. \<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          by blast
        have  \<open>\<forall> m. \<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
          using \<open>\<And> m. \<exists> x. norm x = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) x) + inverse (real (Suc m))\<close>
          by blast
        hence  \<open>\<exists> x. \<forall> m. norm (x m) = 1 \<and> onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m))\<close>
          using choice by simp  
        then obtain x where \<open>norm (x m) = 1\<close> 
          and \<open>onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m))\<close>
        for m::nat
          by blast          
        have \<open>\<forall> m. onorm (\<lambda> x. f n x - l x) < e + inverse (real (Suc m))\<close>
          using \<open>\<And> m. norm (x m) = 1\<close>  \<open>\<And> m. onorm (\<lambda> x. f n x - l x) \<le> norm ((\<lambda> x. f n x - l x) (x m)) + inverse (real (Suc m)) \<close>
            \<open>\<forall> x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
          by smt
        have \<open>onorm (\<lambda> x. f n x - l x) \<le> e\<close>
        proof(rule classical)
          assume \<open>\<not>(onorm (\<lambda> x. f n x - l x) \<le> e)\<close>
          hence \<open>e < onorm (\<lambda> x. f n x - l x)\<close>
            by simp
          hence \<open>0 < onorm (\<lambda> x. f n x - l x) - e\<close>
            by simp
          hence \<open>\<exists> n0. inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close>
            by (rule Archimedean_Field.reals_Archimedean)
          then obtain n0 where \<open>inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close>
            by blast
          have \<open>\<forall> m. onorm (\<lambda> x. f n x - l x) - e < inverse (real (Suc m))\<close>
            by (smt \<open>\<forall>m. onorm (\<lambda>x. f n x - l x) < e + inverse (real (Suc m))\<close>)
          hence \<open>\<forall> m. inverse (real (Suc n0)) < inverse (real (Suc m))\<close>
            using  \<open>inverse (real (Suc n0)) < onorm (\<lambda> x. f n x - l x) - e\<close> by smt
          hence \<open>inverse (real (Suc n0)) < inverse (real (Suc n0))\<close>
            by blast
          thus ?thesis by blast
        qed
        thus ?thesis by blast 
      qed
      thus ?thesis by blast
    qed
    hence \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N. norm ( onorm (\<lambda>x. f n x - l x) ) \<le> e\<close>
      for e
    proof-
      assume \<open>e > 0\<close>
      hence \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        using  \<open>\<And> e. e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N.  onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        by blast
      then obtain N where \<open>\<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close>
        by blast
      have  \<open>\<forall> n \<ge> N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close>
      proof-
        have \<open>n \<ge> N \<Longrightarrow> norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close>
          for n
        proof-
          assume \<open>n \<ge> N\<close>
          hence \<open>onorm (\<lambda>x. f n x - l x) \<le> e\<close>
            using \<open>\<forall> n \<ge> N. onorm (\<lambda>x. f n x - l x) \<le> e\<close> by blast
          moreover have \<open>onorm (\<lambda>x. f n x - l x) \<ge> 0\<close>
            by (simp add: assms(1) assms(2) bounded_linear_sub onorm_pos_le)            
          ultimately show ?thesis by simp
        qed
        thus ?thesis by blast
      qed
      thus ?thesis by blast 
    qed
    have \<open>0 < e \<Longrightarrow>
      \<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) < e\<close>
      for e::real
    proof-
      assume \<open>0 < e\<close>
      hence \<open>e/2 < e\<close>
        by simp
      have \<open>0 < e/2\<close>
        using \<open>0 < e\<close> by simp
      hence \<open>\<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e/2\<close>
        using \<open>\<And>e. 0 < e \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. norm (onorm (\<lambda>x. f n x - l x)) \<le> e\<close> by blast
      thus ?thesis using \<open>e/2 < e\<close> by fastforce
    qed
    thus ?thesis by (simp add: LIMSEQ_I) 
  qed
  thus ?thesis  by blast
qed

lemma oCauchy_uCauchy:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector, 'b::real_normed_vector) rbounded\<close>
  assumes \<open>Cauchy f\<close>
  shows \<open>uniformly_Cauchy_on (sphere 0 1) (\<lambda> n. Rep_rbounded (f n))\<close>
proof-
  have  \<open>N\<in>HNatInfinite \<Longrightarrow> M\<in>HNatInfinite \<Longrightarrow> x\<in>*s* (sphere 0 1) \<Longrightarrow> 
    (*f2* (\<lambda> n. Rep_rbounded (f n))) N x \<approx> (*f2* (\<lambda> n. Rep_rbounded (f n))) M x\<close>
    for N M x
  proof-
    assume \<open>N\<in>HNatInfinite\<close> and \<open>M\<in>HNatInfinite\<close> and \<open>x\<in>*s* (sphere 0 1)\<close> 
    from \<open>Cauchy f\<close>
    have \<open>NSCauchy f\<close>
      by (simp add: NSCauchy_Cauchy_iff)
    hence \<open>(*f* f) N \<approx> (*f* f) M\<close>
      unfolding NSCauchy_def
      using \<open>N\<in>HNatInfinite\<close> \<open>M\<in>HNatInfinite\<close>
      by blast
    hence \<open>(*f* f) N - (*f* f) M \<in> Infinitesimal\<close>
      using bex_Infinitesimal_iff by blast
    hence \<open>hnorm ((*f* f) N - (*f* f) M) \<in> Infinitesimal\<close>
      by (simp add: Infinitesimal_hnorm_iff)
    moreover have \<open>hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x
                                 - (*f2* (\<lambda> n. Rep_rbounded (f n))) M x )
        \<le> hnorm ((*f* f) N - (*f* f) M)\<close>
    proof-
      have \<open>bounded_linear (Rep_rbounded (f n))\<close>
        for n
        using Rep_rbounded by blast
      hence \<open>bounded_linear (\<lambda> x. Rep_rbounded (f n) x - Rep_rbounded (f m) x )\<close>
        for n m
        by (simp add: bounded_linear_sub)    
      moreover have \<open>\<And>NN MM xx.
       (\<And>n m. bounded_linear (\<lambda>x. Rep_rbounded (f n) x - Rep_rbounded (f m) x)) \<Longrightarrow>
       norm xx = 1 \<Longrightarrow>
       norm (Rep_rbounded (f NN) xx - Rep_rbounded (f MM) xx) \<le> onorm (Rep_rbounded (f NN - f MM))\<close>
        using onorm
        by (metis (no_types, hide_lams) Rep_rbounded mem_Collect_eq minus_rbounded.rep_eq mult.commute mult.left_neutral)        
      ultimately have \<open>\<forall> NN MM xx. norm xx = 1 \<longrightarrow> norm ( ( (\<lambda> n. Rep_rbounded (f n))) NN xx
                                 - ( (\<lambda> n. Rep_rbounded (f n))) MM xx )
        \<le> norm (( f) NN - ( f) MM)\<close>
        unfolding norm_rbounded_def
        by auto
      hence \<open>\<forall> NN MM xx. hnorm xx = 1 \<longrightarrow> hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) NN xx
                                 - (*f2* (\<lambda> n. Rep_rbounded (f n))) MM xx )
        \<le> hnorm ((*f* f) NN - (*f* f) MM)\<close>
        by StarDef.transfer
      moreover have \<open>hnorm x = 1\<close>
      proof-
        have \<open>\<forall> xx::'a. xx \<in> (sphere 0 1) \<longrightarrow> norm xx = 1\<close>
          by auto
        hence \<open>\<forall> xx::'a star. xx \<in> *s* (sphere 0 1) \<longrightarrow> hnorm xx = 1\<close>
          by StarDef.transfer
        thus ?thesis
          using \<open>x \<in> *s* (sphere 0 1)\<close>
          by blast
      qed
      ultimately show ?thesis by blast 
    qed
    moreover have \<open>hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f2* (\<lambda> n. Rep_rbounded (f n))) M x ) \<ge> 0\<close>
    proof-
      have  \<open>norm ( ( (\<lambda> n. Rep_rbounded (f n))) NN xx - ( (\<lambda> n. Rep_rbounded (f n))) MM xx ) \<ge> 0\<close>
        for NN MM xx
        by auto
      thus ?thesis by auto 
    qed
    ultimately have \<open>hnorm ( (*f2* (\<lambda> n. Rep_rbounded (f n))) N x - (*f2* (\<lambda> n. Rep_rbounded (f n))) M x ) \<in> Infinitesimal\<close>
      using Infinitesimal_interval2 by blast
    thus ?thesis
      using bex_Infinitesimal_iff hnorm_le_Infinitesimal by blast 
  qed
  thus ?thesis using nsuniformly_Cauchy_on_I by metis
qed













chapter \<open>Chaos\<close>

lemma uCauchy_ustrong:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>\<And> n. bounded_linear (f n)\<close> and \<open>uCauchy f\<close> 
  shows \<open>\<exists> l::'a\<Rightarrow>'b. bounded_linear l \<and> f \<midarrow>ustrong\<rightarrow> l\<close>
proof-
  have \<open>\<exists> l::'a\<Rightarrow>'b. f \<midarrow>ustrong\<rightarrow> l\<close>
  proof-
    have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
      using \<open>uCauchy f\<close> unfolding uCauchy_def sphere_def uniformly_Cauchy_on_def dist_norm
      by blast
    hence \<open>norm x = 1 \<Longrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (f m x - f n x) < e)\<close>
      for x
      by blast
    hence \<open>norm x = 1 \<Longrightarrow> (\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. dist (f m x) (f n x) < e)\<close>
      for x
      by (simp add: dist_norm)    
    hence \<open>norm x = 1 \<Longrightarrow> Cauchy (\<lambda> n. f n x)\<close>
      for x
      using Cauchy_def by blast
    hence \<open>norm x = 1 \<Longrightarrow> convergent (\<lambda> n. f n x)\<close>
      for x
      by (simp add: Cauchy_convergent_iff)
    hence \<open>norm x = 1 \<Longrightarrow> \<exists> l. (\<lambda> n. f n x) \<longlonglongrightarrow> l\<close>
      for x
      by (simp add: convergentD)
    hence \<open>\<forall> x. \<exists> l. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l\<close>
      by blast
    hence \<open>\<exists> l. \<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
      by metis
    then obtain l where \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close> by blast
    have \<open>e > 0 \<Longrightarrow> \<exists>N. \<forall>n\<ge>N. \<forall>x. norm x = 1 \<longrightarrow> norm (f n x - l x) < e\<close>
      for e::real
    proof-
      assume \<open>e > 0\<close>
      hence \<open>e/2 > 0\<close>
        by simp
      hence \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. dist (f n x) (l x) < e/2)\<close>
        using  \<open>\<forall> x. norm x = 1 \<longrightarrow> (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
        by (meson LIMSEQ_iff_nz)
      have \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x)  (f n x) < e/2\<close>
        using  \<open>e/2 > 0\<close> \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
        by (metis dist_norm)
      then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (f n x) < e/2\<close>
        by blast
      have \<open>m \<ge> M \<Longrightarrow> \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (l x) < e\<close>
        for m
      proof-
        assume \<open>m \<ge> M\<close>
        have \<open>norm x = 1 \<Longrightarrow> dist (f m x) (l x) < e\<close>
          for x
        proof-
          assume \<open>norm x = 1\<close>
          have \<open>dist (f m x) (l x) \<le> dist (f m x) (f n x) + dist (l x) (f n x)\<close>
            for n
            by (simp add: dist_triangle2)
          moreover have \<open>n \<ge> M \<Longrightarrow> dist (f m x) (f n x) < e/2\<close>
            for n
            using \<open>M \<le> m\<close> \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> dist (f m x) (f n x) < e / 2\<close> \<open>norm x = 1\<close> by blast
          moreover have \<open>\<exists> N. \<forall> n \<ge> N. dist (l x) (f n x) < e/2\<close>
          proof-
            have \<open>\<exists> N. \<forall> n \<ge> N. dist (f n x) (l x) < e/2\<close>
              using \<open>e/2 > 0\<close> \<open>\<forall>x. norm x = 1 \<longrightarrow> (\<exists>N. \<forall>n\<ge>N. dist (f n x) (l x) < e / 2)\<close> \<open>norm x = 1\<close> by auto 
            thus ?thesis
              by (simp add: dist_commute) 
          qed
          ultimately show ?thesis
            by (meson dist_triangle_half_l le_add1 le_add2) 
        qed
        thus ?thesis by blast
      qed
      thus ?thesis
        by (metis dist_norm) 
    qed
    hence \<open>\<forall> e > 0. \<exists>N. \<forall>n\<ge>N. \<forall>x\<in>sphere. norm (f n x - l x) < e\<close>
      unfolding sphere_def mem_Collect_eq by blast
    thus ?thesis unfolding upointwise_convergence_def using uniform_convergence_norm_I
      by metis
  qed
  then obtain s where \<open>f \<midarrow>ustrong\<rightarrow> s\<close> by blast
  define l::\<open>'a \<Rightarrow> 'b\<close> where \<open>l x = (norm x) *\<^sub>R s ((inverse (norm x)) *\<^sub>R x)\<close>
    for x::'a       
  have \<open>t \<in> sphere \<Longrightarrow> (\<lambda>x. norm x *\<^sub>R s (x /\<^sub>R norm x)) t = s t\<close>
    for t
    unfolding sphere_def
    by simp
  hence \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
    using \<open>f \<midarrow>ustrong\<rightarrow> s\<close> 
    unfolding l_def upointwise_convergence_def
    by (metis (no_types, lifting) uniform_limit_cong') 
  moreover have \<open>bounded_linear l\<close>
  proof-
    have \<open>(\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
      for x
    proof(cases \<open> x = 0\<close>)
      case True
      have \<open>(\<lambda> n. f n x) \<longlonglongrightarrow> 0\<close>
      proof-
        have \<open>f n x = (0::'b)\<close>
          for n
          using \<open>\<And> n. bounded_linear (f n)\<close>
          by (simp add: True linear_simps(3))
        moreover  have \<open>(\<lambda> n. (0::'b)) \<longlonglongrightarrow> 0\<close>
          by simp            
        ultimately show ?thesis by simp
      qed
      moreover have \<open>l x = 0\<close>
      proof-
        have \<open>norm x = 0\<close>
          using \<open>x = 0\<close> by simp
        thus ?thesis using l_def by simp
      qed
      ultimately show ?thesis by simp 
    next
      case False
      hence  \<open>norm x \<noteq> 0\<close> by simp
      thus ?thesis
      proof-
        have  \<open>(\<lambda> n. f n (x  /\<^sub>R norm x)) \<longlonglongrightarrow> s (x /\<^sub>R norm x)\<close>
        proof-
          have \<open>norm (x  /\<^sub>R norm x) = 1\<close>
            by (simp add: False)
          have \<open> \<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<forall>x. norm x = 1 \<longrightarrow> norm (f n x - s x) < e\<close>
            using \<open>f \<midarrow>ustrong\<rightarrow> s\<close>
            unfolding upointwise_convergence_def sphere_def
            using uniform_convergence_norm_D by fastforce

          hence \<open> \<forall>e>0. \<exists>N. \<forall>n\<ge>N. norm (f n (x  /\<^sub>R norm x) - s (x  /\<^sub>R norm x)) < e\<close>
            using  \<open>norm (x  /\<^sub>R norm x) = 1\<close> by fastforce
          thus ?thesis
            by (simp add: LIMSEQ_iff) 
        qed
        hence  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow>  (norm x) *\<^sub>R  s (x /\<^sub>R norm x)\<close>
          using bounded_linear.tendsto bounded_linear_scaleR_right by blast
        hence  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
          using l_def
          by simp
        have  \<open>(\<lambda> n.  f n x) \<longlonglongrightarrow> l x\<close>
        proof-
          have \<open>(norm x) *\<^sub>R f n (x /\<^sub>R norm x) = f n x\<close>
            for n
            using \<open>norm x \<noteq> 0\<close> \<open>\<And> n. bounded_linear (f n)\<close>
            unfolding bounded_linear_def linear_def
            by (simp add: assms(1) linear_simps(5)) 
          thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close> by simp
        qed
        thus ?thesis using  \<open>(\<lambda> n. (norm x) *\<^sub>R f n (x /\<^sub>R norm x)) \<longlonglongrightarrow> l x\<close>
          by auto
      qed
    qed
    have \<open>linear l\<close>
    proof
      show "l (b1 + b2) = l b1 + l b2"
        for b1 :: 'a
          and b2 :: 'a
      proof-
        have \<open>(\<lambda> n. f n (b1 + b2)) \<longlonglongrightarrow> l (b1 + b2)\<close>
          using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
          by blast
        moreover have \<open>(\<lambda> n. f n (b1 + b2)) \<longlonglongrightarrow> l b1 + l b2\<close>
        proof-
          have \<open>(\<lambda> n. f n b1) \<longlonglongrightarrow> l b1\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          moreover have \<open>(\<lambda> n. f n b2) \<longlonglongrightarrow> l b2\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          ultimately have \<open>(\<lambda> n. f n b1 + f n b2) \<longlonglongrightarrow> l b1 + l b2\<close>
            by (simp add: tendsto_add) 
          moreover have \<open>(\<lambda> n. f n (b1 + b2)) = (\<lambda> n. f n b1 + f n b2)\<close>
          proof-
            have \<open>f n (b1 + b2) = f n b1 + f n b2\<close>
              for n
              using \<open>\<And> n. bounded_linear (f n)\<close>
              unfolding bounded_linear_def
              by (simp add: linear_add)
            thus ?thesis by blast
          qed
          ultimately show ?thesis by simp 
        qed
        ultimately show ?thesis
          using LIMSEQ_unique by blast            
      qed
      show "l (r *\<^sub>R b) = r *\<^sub>R l b"
        for r :: real
          and b :: 'a
      proof-
        have \<open>(\<lambda> n. f n (r *\<^sub>R b)) \<longlonglongrightarrow> l (r *\<^sub>R b)\<close>
          using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
          by blast
        moreover have \<open>(\<lambda> n. f n (r *\<^sub>R b)) \<longlonglongrightarrow>  r *\<^sub>R (l b)\<close>
        proof-
          have \<open>(\<lambda> n. f n b) \<longlonglongrightarrow> l b\<close>
            using  \<open>\<And> x. (\<lambda> n. f n x) \<longlonglongrightarrow> l x\<close>
            by blast
          hence \<open>(\<lambda> n. r *\<^sub>R (f n b)) \<longlonglongrightarrow> r *\<^sub>R (l b)\<close>
            using bounded_linear.tendsto bounded_linear_scaleR_right by blast
          moreover have \<open>(\<lambda> n. (f n (r *\<^sub>R b))) = (\<lambda> n. r *\<^sub>R (f n b))\<close>
          proof-
            have \<open>f n (r *\<^sub>R b) = r *\<^sub>R (f n b)\<close>
              for n
              using \<open>\<And> n. bounded_linear (f n)\<close>
              unfolding bounded_linear_def
              by (simp add: linear_scale)
            thus ?thesis by blast
          qed
          ultimately show ?thesis by simp 
        qed
        ultimately show ?thesis
          using LIMSEQ_unique by blast            
      qed
    qed
    moreover have \<open>bounded_linear_axioms l\<close>
    proof-
      have \<open>\<exists>K. \<forall>x. norm (l x) \<le> norm x * K\<close>
      proof(rule classical)
        assume \<open>\<not> (\<exists>K. \<forall>x. norm (l x) \<le> norm x * K)\<close>
        hence \<open>\<forall> K. \<exists> x. norm (l x) > norm x * K\<close>
          by smt
        hence \<open>\<forall> K. \<exists> x \<noteq> 0. norm (l x) > norm x * K\<close>
          using calculation linear_0 by force
        have \<open>\<forall> K. \<exists> x. norm x = 1 \<and> K < norm (l x)\<close>
        proof-
          have \<open>\<exists> x. norm x = 1 \<and> K < norm (l x)\<close>
            for K
          proof-
            have \<open>\<exists> x \<noteq> 0. norm (l x) > norm x * K\<close>
              using  \<open>\<forall> K. \<exists> x \<noteq> 0. norm (l x) > norm x * K\<close> by blast
            then obtain x where \<open>x \<noteq> 0\<close> and \<open>norm (l x) > norm x * K\<close>
              by blast
            have \<open>norm x > 0\<close> using \<open>x \<noteq> 0\<close> by simp
            hence  \<open>inverse (norm x) * norm (l x) > inverse (norm x) * (norm x) * K\<close>
              using  \<open>norm (l x) > norm x * K\<close>
              by (smt linordered_field_class.sign_simps(23) mult_left_le_imp_le positive_imp_inverse_positive) 
            moreover have \<open>(inverse (norm x)) * (norm x) = 1\<close>
              using \<open>norm x > 0\<close> by simp
            ultimately have \<open>(inverse (norm x)) * norm (l x) >  K\<close>
              by simp
            moreover have \<open>(inverse (norm x)) * norm (l x) = norm ((inverse (norm x)) *\<^sub>R (l x))\<close>
            proof-
              have \<open>(inverse (norm x)) > 0\<close>
                using \<open>norm x > 0\<close> 
                by simp
              thus ?thesis using norm_scaleR
                by simp 
            qed
            hence \<open> norm ((inverse (norm x)) *\<^sub>R (l x)) >  K\<close>
              using calculation by linarith
            hence \<open> norm (l ((inverse (norm x)) *\<^sub>R  x)) >  K\<close>
            proof-
              have \<open>(inverse (norm x)) *\<^sub>R (l x) = l ((inverse (norm x)) *\<^sub>R  x)\<close>
                by (simp add: \<open>linear l\<close> linear_scale)
              thus ?thesis
                using \<open>K < norm (l x /\<^sub>R norm x)\<close> by simp                 
            qed
            have \<open>norm ( (inverse (norm x)) *\<^sub>R  x ) = 1\<close>
              using \<open>norm x > 0\<close> by simp
            show ?thesis
              using \<open>K < norm (l (x /\<^sub>R norm x))\<close> \<open>norm (x /\<^sub>R norm x) = 1\<close> by blast 
          qed
          thus ?thesis by blast
        qed
        have \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f m x - f n x) < e\<close>
          using \<open>uCauchy f\<close> dist_norm
          unfolding uCauchy_def uniformly_Cauchy_on_def sphere_def
          using  mem_Collect_eq
          by (metis (mono_tags))
        hence \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < 1\<close>
          by auto
        then obtain M where \<open>\<forall>m\<ge>M. \<forall>n\<ge>M. \<forall>x. norm x = 1 \<longrightarrow>
                             norm (f m x - f n x) < 1\<close>
          by blast
        hence \<open>\<forall>m\<ge>M. \<forall>x. 
            norm x = 1 \<longrightarrow> norm (f m x - f M x) < 1\<close>
          by blast
        have \<open>norm (f m x) \<le> norm (f M x) + norm (f m x - f M x)\<close>
          for m and x
          by (simp add: norm_triangle_sub) 
        hence \<open>norm (f m x) \<le> onorm (f M) * norm x + norm (f m x - f M x)\<close>
          for m and x
          using onorm
          by (smt assms(1)) 
        hence \<open>norm x = 1 \<Longrightarrow> norm (f m x) \<le> onorm (f M) + norm (f m x - f M x)\<close>
          for m and x
          by (metis mult_cancel_left2)
        hence \<open>m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm (f m x) < onorm (f M) + 1\<close>
          for m and x
          using  \<open>\<forall>m\<ge>M. \<forall>x. 
            norm x = 1 \<longrightarrow> norm (f m x - f M x) < 1\<close> 
          by smt
        have \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. f m x) \<longlonglongrightarrow> l x\<close>
          for x
          by (simp add: \<open>\<And>x. (\<lambda>n. f n x) \<longlonglongrightarrow> l x\<close>)
        hence \<open>norm x = 1 \<Longrightarrow> (\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
          for x
          by (simp add: tendsto_norm)
        hence \<open>norm x = 1 \<Longrightarrow> norm (l x) \<le> onorm (f M) + 1\<close>
          for x
        proof-
          assume \<open>norm x = 1\<close>
          hence \<open>(\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
            using  \<open>\<And> x. norm x = 1 \<Longrightarrow> (\<lambda> m. norm (f m x)) \<longlonglongrightarrow> norm (l x)\<close>
            by blast
          moreover have \<open>\<forall>  m \<ge> M. norm (f m x) \<le> onorm (f M) + 1\<close>
            using  \<open>\<And> m. \<And> x.  m \<ge> M \<Longrightarrow> norm x = 1 \<Longrightarrow> norm (f m x) < onorm (f M) + 1\<close>
              \<open>norm x = 1\<close> by smt
          ultimately show ?thesis 
            by (rule Topological_Spaces.Lim_bounded)
        qed
        moreover have  \<open>\<exists> x. norm x = 1 \<and> onorm (f M) + 1 < norm (l x)\<close>
          by (simp add: \<open>\<forall>K. \<exists>x. norm x = 1 \<and> K < norm (l x)\<close>)
        ultimately show ?thesis
          by fastforce 
      qed
      thus ?thesis unfolding bounded_linear_axioms_def by blast
    qed
    ultimately show ?thesis unfolding bounded_linear_def by blast
  qed
  ultimately show ?thesis by blast
qed

theorem completeness_real_bounded:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>\<And>n. bounded_linear (f n)\<close> and \<open>oCauchy f\<close>
  shows \<open>\<exists> l. bounded_linear l \<and> f \<midarrow>onorm\<rightarrow> l\<close>
proof-
  have \<open>uCauchy f\<close>
    using oCauchy_uCauchy \<open>oCauchy f\<close> \<open>\<And> n. bounded_linear (f n)\<close> by blast
  hence \<open>\<exists> l. bounded_linear l \<and> f \<midarrow>ustrong\<rightarrow> l\<close>
    using \<open>\<And> n. bounded_linear (f n)\<close>
      uCauchy_ustrong
    by auto
  then obtain l where \<open>bounded_linear l\<close> and \<open>f \<midarrow>ustrong\<rightarrow> l\<close> 
    by blast
  have \<open>(\<lambda>n. onorm (\<lambda>x. f n x - l x)) \<longlonglongrightarrow> 0\<close>
    using  \<open>f \<midarrow>ustrong\<rightarrow> l\<close> \<open>bounded_linear l\<close> assms(1) onorm_convergence_def ustrong_onorm 
    by blast
  thus ?thesis
    unfolding onorm_convergence_def using \<open>bounded_linear l\<close> by blast
qed

lemma onorm_oCauchy:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> and l::\<open>'a\<Rightarrow>'b\<close>
  assumes \<open>\<And> n. bounded_linear (f n)\<close> and \<open>f \<midarrow>onorm\<rightarrow> l\<close> and \<open>bounded_linear l\<close>
  shows \<open>oCauchy f\<close>
proof-
  have \<open>e>0 \<Longrightarrow> \<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. onorm (\<lambda>x. f m x - f n x) < e\<close>
    for e
  proof-
    assume \<open>e > 0\<close>
    from \<open>f \<midarrow>onorm\<rightarrow> l\<close> 
    have  \<open>(\<lambda>n. onorm (\<lambda>x. f n x - l x)) \<longlonglongrightarrow> 0\<close> 
      unfolding onorm_convergence_def by blast
    hence  \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. norm ((\<lambda>n. onorm (\<lambda>x. f n x - l x)) m) < e\<close>
      using LIMSEQ_D by fastforce
    moreover have \<open>bounded_linear F \<Longrightarrow> onorm F \<ge> 0\<close>
      for F::\<open>'a\<Rightarrow>'b\<close>
      by (simp add: onorm_pos_le)
    moreover have \<open>bounded_linear (\<lambda>x. f n x - l x)\<close>
      for n
      by (simp add: assms(1) assms(3) bounded_linear_sub)    
    ultimately have  \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. ((\<lambda>n. onorm (\<lambda>x. f n x - l x)) m) < e\<close>
      by simp
    hence \<open>\<forall>e>0. \<exists>M. \<forall>m\<ge>M. onorm (\<lambda>x. f m x - l x)  < e\<close>
      by blast
    moreover have \<open>e/2 > 0\<close>
      using \<open>e > 0\<close> by simp
    ultimately obtain M where \<open>\<forall>m\<ge>M. onorm (\<lambda>x. f m x - l x)  < e/2\<close>
      by blast
    have \<open>onorm (\<lambda>x. (f m x - l x) + (l x - f n x)) \<le> onorm (\<lambda>x. f m x - l x) + onorm (\<lambda>x. l x - f n x)\<close>
      for m n
      by (metis (full_types) assms(1) assms(3) bounded_linear_sub onorm_triangle_le order_refl)    
    hence \<open>m \<ge> M \<Longrightarrow> n \<ge> M \<Longrightarrow> onorm (\<lambda>x. f m x - f n x) < e\<close>
      for m n
    proof-
      assume \<open>m \<ge> M\<close> and \<open>n \<ge> M\<close>
      have \<open>onorm (\<lambda>x. f m x - l x)  < e/2\<close>
        using  \<open>m \<ge> M\<close>  \<open>\<forall>m\<ge>M. onorm (\<lambda>x. f m x - l x)  < e/2\<close> 
        by blast
      moreover have \<open>onorm (\<lambda>x. l x - f n x)  < e/2\<close>
      proof-
        have \<open>onorm (\<lambda>x. f n x - l x)  < e/2\<close>
          using  \<open>n \<ge> M\<close>  \<open>\<forall>m\<ge>M. onorm (\<lambda>x. f m x - l x)  < e/2\<close> 
          by blast
        moreover have \<open>onorm (\<lambda>x. f n x - l x)  = onorm (\<lambda>x.  l x - f n x)\<close>
        proof-
          have \<open>(\<lambda>x.  l x - f n x) = (\<lambda> y. - (\<lambda>x. f n x - l x) y)\<close>
            by auto
          thus ?thesis using onorm_neg by metis
        qed
        ultimately show ?thesis
          by simp 
      qed
      ultimately have \<open>onorm (\<lambda>x. f m x - l x) + onorm (\<lambda>x. l x - f n x) < e/2 + e/2\<close>
        by simp
      hence \<open>onorm (\<lambda>x. f m x - l x) + onorm (\<lambda>x. l x - f n x) < e\<close>
        by simp
      thus ?thesis using \<open>onorm (\<lambda>x. (f m x - l x) + (l x - f n x)) \<le> onorm (\<lambda>x. f m x - l x) + onorm (\<lambda>x. l x - f n x)\<close>
        by simp
    qed
    thus ?thesis by blast
  qed
  thus ?thesis unfolding oCauchy_def by blast
qed

proposition oCauchy_uCauchy_iff:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>\<And> n. bounded_linear (f n)\<close> 
  shows \<open>oCauchy f \<longleftrightarrow> uCauchy f\<close>
proof
  show "uCauchy f"
    if "oCauchy f"
    using that
    by (simp add: assms oCauchy_uCauchy) 
  show "oCauchy f"
    if "uCauchy f"
    by (meson assms onorm_oCauchy that uCauchy_ustrong ustrong_onorm)
qed

lemma onorm_strong:
  fixes f::\<open>nat \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector)\<close> and l::\<open>'a \<Rightarrow> 'b\<close>
  assumes \<open>\<forall>n. bounded_linear (f n)\<close> and \<open>bounded_linear l\<close> and \<open>f \<midarrow>onorm\<rightarrow> l\<close>
  shows \<open>f \<midarrow>strong\<rightarrow> l\<close>
proof-
  have \<open>(\<lambda>n. norm (f n x - l x)) \<longlonglongrightarrow> 0\<close>
    for x
  proof-
    have \<open>e > 0 \<Longrightarrow> \<exists> N. \<forall> n \<ge> N. dist (norm (f n x - l x)) 0 < e\<close>
      for e::real
    proof-
      assume \<open>e > 0\<close>
      have \<open>\<exists> N. \<forall> n \<ge> N. norm (f n x - l x) < e\<close>
      proof-
        have \<open>norm (f n x - l x) \<le> onorm (\<lambda> t. f n t - l t) * norm x\<close>
          for n::nat
          using assms(1) assms(2) bounded_linear_sub onorm by blast                          
        moreover have \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda> t. f n t - l t) * norm x < e\<close>
        proof(cases \<open>norm x = 0\<close>)
          case True
          thus ?thesis
            by (simp add: \<open>0 < e\<close>) 
        next
          case False
          hence \<open>norm x > 0\<close>
            by simp
          have \<open>\<exists> N. \<forall> n \<ge> N. onorm (\<lambda> t. f n t - l t) < e/norm x\<close>
          proof-
            from \<open>f \<midarrow>onorm\<rightarrow> l\<close>
            have \<open>(\<lambda> n. onorm (\<lambda> t. f n t - l t)) \<longlonglongrightarrow> 0\<close>
              unfolding onorm_convergence_def
              by blast
            moreover have \<open>e / norm x > 0\<close>
              using \<open>e > 0\<close> \<open>norm x > 0\<close> by simp
            ultimately have \<open>\<exists> N. \<forall> n\<ge>N. norm ((\<lambda> n. onorm (\<lambda> t. f n t - l t)) n ) < e / norm x\<close>
              by (simp add: LIMSEQ_iff) 
            then obtain N where \<open>\<forall> n\<ge>N. norm ((\<lambda> n. onorm (\<lambda> t. f n t - l t)) n ) < e / norm x\<close>
              by blast
            hence \<open>\<forall> n\<ge>N. norm ( onorm (\<lambda> t. f n t - l t ) ) < e / norm x\<close>
              by blast
            have \<open>\<forall> n\<ge>N.  onorm (\<lambda> t. f n t - l t ) < e / norm x\<close>
            proof-
              have \<open>onorm (\<lambda> t. f n t - l t ) \<ge> 0\<close>
                for n
                by (simp add: assms(1) assms(2) bounded_linear_sub onorm_pos_le)                
              thus ?thesis using  \<open>\<forall> n\<ge>N. norm ( onorm (\<lambda> t. f n t - l t ) ) < e / norm x\<close>
                by simp
            qed
            thus ?thesis by blast
          qed
          thus ?thesis using \<open>norm x > 0\<close>
          proof -
            { fix nn :: "nat \<Rightarrow> nat"
              have ff1: "\<forall>r ra. (ra::real) * r = r * ra \<or> ra = 0"
                by auto
              have "\<forall>r ra rb. (((rb::real) = 0 \<or> rb * ra < r) \<or> \<not> ra < r / rb) \<or> \<not> 0 < rb"
                by (metis (no_types) linordered_comm_semiring_strict_class.comm_mult_strict_left_mono nonzero_mult_div_cancel_left times_divide_eq_right)
              hence "\<exists>n. \<not> n \<le> nn n \<or> onorm (\<lambda>a. f (nn n) a - l a) * norm x < e"
                using ff1 by (metis (no_types) False \<open>0 < norm x\<close> \<open>\<exists>N. \<forall>n\<ge>N. onorm (\<lambda>t. f n t - l t) < e / norm x\<close>) }
            thus ?thesis
              by (metis (no_types))
          qed  
        qed
        ultimately show ?thesis by smt
      qed
      thus ?thesis
        by auto 
    qed
    thus ?thesis
      by (simp add: LIMSEQ_I) 
  qed
  thus ?thesis unfolding pointwise_convergence_def by blast
qed

lemma pointwise_convergence_pointwise: 
  \<open>f \<midarrow>strong\<rightarrow> F \<Longrightarrow> (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
  for x
proof-
  assume  \<open>f \<midarrow>strong\<rightarrow> F\<close>
  hence  \<open>( \<lambda> n. norm ((f n) x - F x))  \<longlonglongrightarrow> 0\<close>
    unfolding pointwise_convergence_def
    by blast
  have \<open>( \<lambda> n. (F x) )  \<longlonglongrightarrow> F x\<close>
    by simp
  moreover have  \<open>( \<lambda> n. ( (f n) x - F x))  \<longlonglongrightarrow> 0\<close>
    using  \<open>( \<lambda> n. norm ((f n) x - F x) )  \<longlonglongrightarrow> 0\<close>
    by (simp add:  tendsto_norm_zero_iff)
  ultimately have  \<open>( \<lambda> n. (f n) x)  \<longlonglongrightarrow> F x\<close>
    by (rule Limits.Lim_transform)
  thus ?thesis by blast
qed


lemma onorm_uniq:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>\<And> n. bounded_linear (f n)\<close> and \<open>bounded_linear l\<close> and \<open>bounded_linear s\<close> 
    and \<open>f \<midarrow>onorm\<rightarrow>l\<close> and \<open>f \<midarrow>onorm\<rightarrow>s\<close>
  shows \<open>l = s\<close>
proof-
  have \<open>l x = s x\<close>
    for x
  proof-
    have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> l x\<close>
    proof-
      have \<open>f \<midarrow>strong\<rightarrow>l\<close>
        by (simp add: assms(1) assms(2) assms(4) onorm_strong)
      thus ?thesis  by (simp add: pointwise_convergence_pointwise)
    qed
    moreover have \<open>(\<lambda> n. (f n) x) \<longlonglongrightarrow> s x\<close>
    proof-
      have \<open>f \<midarrow>strong\<rightarrow>s\<close>
        by (simp add: assms(1) assms(3) assms(5) onorm_strong)
      thus ?thesis by (simp add: pointwise_convergence_pointwise)
    qed
    ultimately show ?thesis
      using LIMSEQ_unique by blast 
  qed
  thus ?thesis by blast
qed

proposition onorm_ustrong_iff:
  fixes f::\<open>nat \<Rightarrow> ('a::{real_normed_vector} \<Rightarrow> 'b::banach)\<close>
  assumes \<open>\<And> n. bounded_linear (f n)\<close> and \<open>bounded_linear l\<close> 
  shows \<open>(f \<midarrow>onorm\<rightarrow>l) \<longleftrightarrow> (f \<midarrow>ustrong\<rightarrow>l)\<close>
(* TODO: use simpler proof from whiteboard, gets rid of banach *)
proof
  show "f \<midarrow>ustrong\<rightarrow> l"
    if "f \<midarrow>onorm\<rightarrow> l"
  proof-
    have \<open>oCauchy f\<close>
      using assms(1) assms(2) onorm_oCauchy that by auto      
    hence \<open>uCauchy f\<close>
      by (simp add: assms(1) oCauchy_uCauchy)
    hence \<open>\<exists> s. bounded_linear s \<and> f \<midarrow>ustrong\<rightarrow> s\<close>
      by (simp add: assms(1) uCauchy_ustrong)
    then obtain s where  \<open>bounded_linear s\<close> and \<open>f \<midarrow>ustrong\<rightarrow> s\<close>
      by blast
    have \<open>f \<midarrow>onorm\<rightarrow> s\<close>
      using  \<open>bounded_linear s\<close>  \<open>\<And> n. bounded_linear (f n)\<close>
      by (simp add: ustrong_onorm \<open>f \<midarrow>ustrong\<rightarrow> s\<close>)
    hence \<open>l = s\<close> 
      using onorm_uniq  \<open>f \<midarrow>onorm\<rightarrow> l\<close> \<open>bounded_linear s\<close> assms(1) assms(2) by blast 
    thus ?thesis using \<open>f \<midarrow>ustrong\<rightarrow> s\<close> by blast
  qed
  show "f \<midarrow>onorm\<rightarrow> l"
    if "f \<midarrow>ustrong\<rightarrow> l"
    using ustrong_onorm \<open>\<And> n. bounded_linear (f n)\<close> \<open>bounded_linear l\<close> that by auto
qed



end

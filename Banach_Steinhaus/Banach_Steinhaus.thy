(*
  File:   Banach_Steinhaus.thy
  Author: Dominique Unruh, University of Tartu
  Author: Jose Manuel Rodriguez Caballero, University of Tartu
*)
section \<open>Banach-Steinhaus theorem\<close>

theory Banach_Steinhaus
  imports 
    Banach_Steinhaus_Missing    
    "HOL-ex.Sketch_and_Explore"
begin

text \<open>
  We formalize Banach-Steinhaus theorem as theorem @{text banach_steinhaus}.
\<close>

subsection \<open>Preliminaries for Sokal's proof of Banach-Steinhaus theorem\<close>

typedef (overloaded) ('a::real_normed_vector, 'b::real_normed_vector) real_bounded
  = \<open>{f::'a \<Rightarrow> 'b. bounded_linear f}\<close>
  morphisms times_real_bounded_vec Abs_real_bounded
  using bounded_linear_zero by blast


notation times_real_bounded_vec (infixr "*\<^sub>v" 70)

setup_lifting type_definition_real_bounded

instantiation  real_bounded :: (real_normed_vector, real_normed_vector) real_normed_vector
begin
lift_definition uminus_real_bounded ::
  "('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded "  is \<open>\<lambda> f. \<lambda> x. - f x\<close>
  by (simp add: bounded_linear_minus)

lift_definition zero_real_bounded ::
  "('a, 'b) real_bounded"  is \<open>\<lambda> x. 0\<close>
  by simp

lift_definition plus_real_bounded ::
  "('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded "  
  is \<open>\<lambda> f. \<lambda> g. \<lambda> x. f x + g x\<close>
  by (simp add: bounded_linear_add)

lift_definition minus_real_bounded ::
  "('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded "  
  is \<open>\<lambda> f. \<lambda> g. \<lambda> x. f x - g x\<close>
  by (simp add: bounded_linear_sub)

lift_definition norm_real_bounded :: \<open>('a, 'b) real_bounded \<Rightarrow> real\<close>
  is \<open>onorm\<close>.

lift_definition dist_real_bounded :: \<open>('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. onorm (\<lambda> x. f x - g x )\<close>.

lift_definition scaleR_real_bounded :: \<open>real \<Rightarrow> ('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded\<close>
  is \<open>\<lambda> r. \<lambda> f. \<lambda> x. r *\<^sub>R f x\<close>
  by (simp add: bounded_linear_const_scaleR)

lift_definition sgn_real_bounded :: \<open>('a, 'b) real_bounded \<Rightarrow> ('a, 'b) real_bounded\<close>
  is \<open>\<lambda> f. (\<lambda> x. (f x) /\<^sub>R (onorm f) )\<close>
  by (simp add: bounded_linear_const_scaleR)

definition uniformity_real_bounded :: \<open>( ('a, 'b) real_bounded \<times> ('a, 'b) real_bounded ) filter\<close>
  where  \<open>uniformity_real_bounded = (INF e:{0<..}. principal {((f::('a, 'b) real_bounded), g). 
          dist f g < e})\<close>

definition open_real_bounded :: \<open>(('a, 'b) real_bounded) set \<Rightarrow> bool\<close>
  where \<open>open_real_bounded = (\<lambda> U::(('a, 'b) real_bounded) set. 
  \<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)\<close>

instance
proof
  show "dist (x::('a, 'b) real_bounded) y = norm (x - y)"
    for x :: "('a, 'b) real_bounded"
      and y :: "('a, 'b) real_bounded"
    apply transfer by simp 
  show "a + b + c = a + (b + c)"
    for a :: "('a, 'b) real_bounded"
      and b :: "('a, 'b) real_bounded"
      and c :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "a + b = b + a"
    for a :: "('a, 'b) real_bounded"
      and b :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "(0::('a, 'b) real_bounded) + a = a"
    for a :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "- a + a = 0"
    for a :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "a - b = a + - b"
    for a :: "('a, 'b) real_bounded"
      and b :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "a *\<^sub>R (x + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real
      and x :: "('a, 'b) real_bounded"
      and y :: "('a, 'b) real_bounded"
    apply transfer by (simp add: scaleR_add_right) 
  show "(a + b) *\<^sub>R x = a *\<^sub>R x + b *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "('a, 'b) real_bounded"
    apply transfer by (simp add: scaleR_left.add)
  show "a *\<^sub>R b *\<^sub>R x = (a * b) *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "('a, 'b) real_bounded"
    apply transfer by simp 
  show "1 *\<^sub>R x = x"
    for x :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "sgn x = inverse (norm x) *\<^sub>R x"
    for x :: "('a, 'b) real_bounded"
    apply transfer by auto
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::('a, 'b) real_bounded) y < e})"
    by (simp add: Banach_Steinhaus.uniformity_real_bounded_def)    
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. x' = x \<longrightarrow> y \<in> U)"
    for U :: "('a, 'b) real_bounded set"
    by (simp add: Banach_Steinhaus.open_real_bounded_def)    
  show "(norm x = 0) = (x = 0)"
    for x :: "('a, 'b) real_bounded"
    apply transfer using onorm_eq_0 by blast 
  show "norm (x + y) \<le> norm x + norm y"
    for x :: "('a, 'b) real_bounded"
      and y :: "('a, 'b) real_bounded"
    apply transfer by (simp add: onorm_triangle) 
  show "norm (a *\<^sub>R x) = \<bar>a\<bar> * norm x"
    for a :: real
      and x :: "('a, 'b) real_bounded"
    apply transfer by (simp add: onorm_scaleR) 
qed

end


text \<open>                 
  The following lemma is due to Alain Sokal ~\cite{sokal2011reall}.
\<close>

lemma sokal_banach_steinhaus:
  "r > 0 \<Longrightarrow> norm f \<le> (inverse r) * Sup ( (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) )"
proof transfer
  fix r::real and f::\<open>'a \<Rightarrow> 'b\<close> and x::'a
  assume \<open>r > 0\<close> and \<open>bounded_linear f\<close>
  have \<open>onorm f = (inverse r) * Sup ((norm \<circ> f) ` (ball 0 r))\<close>
    using \<open>0 < r\<close> \<open>bounded_linear f\<close> onorm_r by auto    
  moreover have \<open>Sup ((norm \<circ> f) ` (ball 0 r)) \<le> Sup ( (\<lambda> \<xi>. norm (f \<xi>)) ` (ball x r) )\<close>
  proof-
    have \<open>(norm \<circ> f) \<xi> \<le> max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))\<close> for \<xi>
      using linear_plus_norm \<open>bounded_linear f\<close>
      by (simp add: linear_plus_norm bounded_linear.linear)
    moreover have \<open>bdd_above ((\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) ` (ball 0 r))\<close> 
    proof-
      have \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close>
      proof-
        have \<open>ball (0::'a) r \<noteq> {}\<close>
          using \<open>0 < r\<close> by auto          
        moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f x)) ` (ball 0 r))\<close>
          by auto          
        moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f \<xi>)) ` (ball 0 r))\<close>
        proof-
          obtain M where \<open>\<And> \<xi>. norm (f \<xi>) \<le> M * norm \<xi>\<close> and \<open>M \<ge> 0\<close>
            using \<open>bounded_linear f\<close> 
            by (metis bounded_linear.nonneg_bounded semiring_normalization_rules(7))            
          hence \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f \<xi>) \<le> M * r\<close>
            using \<open>r > 0\<close> by (smt mem_ball_0 mult_left_mono) 
          thus ?thesis
            by (meson bdd_aboveI2) 
        qed
        ultimately have \<open>bdd_above ((\<lambda> \<xi>. norm (f x) + norm (f \<xi>)) ` (ball 0 r))\<close>
          using bdd_above_plus[where S = "ball (0::'a) r" and f = "\<lambda> \<xi>. norm (f x)" 
              and g = "\<lambda> \<xi>. norm (f \<xi>)"] by simp
        then obtain M where \<open>\<And> \<xi>. \<xi> \<in> ball (0::'a) r \<Longrightarrow> norm (f x) + norm (f \<xi>) \<le> M\<close>
          unfolding bdd_above_def by (meson image_eqI)
        moreover have \<open>norm (f (x + \<xi>)) \<le> norm (f x) + norm (f \<xi>)\<close> for \<xi>
          by (simp add: \<open>bounded_linear f\<close> linear_simps(1) norm_triangle_ineq)          
        ultimately have \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> M\<close>
          by (simp add:  \<open>bounded_linear f\<close> linear_simps(1) norm_triangle_le)          
        thus ?thesis
          by (meson bdd_aboveI2)                    
      qed
      moreover have \<open>bdd_above ((\<lambda> \<xi>. norm (f (x - \<xi>))) ` (ball 0 r))\<close>
      proof-
        obtain M where \<open>\<And> \<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> M\<close>
          using  \<open>bdd_above ((\<lambda> \<xi>. norm (f (x + \<xi>))) ` (ball 0 r))\<close>
          unfolding bdd_above_def
          by (meson image_eqI)
        moreover have \<open>\<xi> \<in> ball (0::'a) r \<Longrightarrow> -\<xi> \<in> ball 0 r\<close> for \<xi>
          using sphere_antipodal by auto
        ultimately show ?thesis
        proof -
          assume a1: "\<And>\<xi>. (\<xi>::'a) \<in> ball 0 r \<Longrightarrow> - \<xi> \<in> ball 0 r"
          assume "\<And>\<xi>. \<xi> \<in> ball 0 r \<Longrightarrow> norm (f (x + \<xi>)) \<le> M"
          hence f2: "\<And>a. a \<notin> ball 0 r \<or> norm (f (a + x)) \<le> M"
            by (metis add.commute)
          have "\<forall>A f r. \<exists>a. (bdd_above (f ` A) \<or> (a::'a) \<in> A) \<and> (\<not> f a \<le> (r::real) \<or> bdd_above (f ` A))"
            by (metis bdd_aboveI2)
          thus ?thesis
            using f2 a1 by (metis uminus_add_conv_diff)
        qed       
      qed
      ultimately show ?thesis 
        unfolding  max_def apply auto apply (meson bdd_above_Int1 bdd_above_mono image_Int_subset)
        by (meson bdd_above_Int1 bdd_above_mono image_Int_subset)
    qed
    moreover have \<open>ball (0::'a) r \<noteq> {}\<close>
      using \<open>r > 0\<close> by auto      
    ultimately have \<open>Sup ((norm \<circ> f) ` (ball 0 r)) \<le>
     Sup ((\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))) ` (ball 0 r))\<close>
      using cSUP_mono[where A = "ball (0::'a) r" and B = "ball (0::'a) r"
          and f = "norm \<circ> f" and g = "\<lambda> \<xi>. max (norm (f (x + \<xi>))) (norm (f (x - \<xi>)))"] by blast
    also have \<open>\<dots> = max (Sup ((\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r)))  
                        (Sup ((\<lambda> \<xi>. (norm (f (x - \<xi>)))) ` (ball 0 r)))\<close> 
    proof-
      have \<open>ball (0::'a) r \<noteq> {}\<close>
        using \<open>r > 0\<close> by auto
      moreover have \<open>bdd_above ((\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r)\<close>
      proof-
        have \<open>(\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r = (norm \<circ> f) ` ball x r\<close>
        proof -
          have "(\<lambda>a. norm (f (x + a))) ` ball 0 r = (\<lambda>a. (norm \<circ> f) (x + a)) ` ball 0 r"
            by (metis comp_apply)
          thus ?thesis
            by (metis (no_types) add.left_neutral image_add_ball image_image)
        qed
        moreover have \<open>bdd_above ((norm \<circ> f) ` ball x r)\<close>
        proof-
          have \<open>bounded (ball x r)\<close>
            by simp            
          hence \<open>bounded ((norm \<circ> f) ` ball x r)\<close>
            using \<open>bounded_linear f\<close> bounded_linear_image bounded_norm_comp by auto
          thus ?thesis
            by (simp add: bounded_imp_bdd_above)          
        qed
        ultimately show ?thesis 
          by simp
      qed
      moreover have \<open>bdd_above ((\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r)\<close>
      proof-
        have \<open>(\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r = (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close>
        proof auto
          show \<open>norm \<xi> < r \<Longrightarrow>
         norm (f (x - \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close> for \<xi>
          proof-
            assume \<open>norm \<xi> < r\<close>
            hence \<open>\<xi> \<in> ball (0::'a) r\<close>
              by auto
            hence \<open>-\<xi> \<in> ball (0::'a) r\<close>
              by auto
            thus ?thesis
              by (metis (no_types, lifting) ab_group_add_class.ab_diff_conv_add_uminus image_iff) 
          qed
          show \<open>norm \<xi> < r \<Longrightarrow>
         norm (f (x + \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r\<close> for \<xi>
          proof-
            assume \<open>norm \<xi> < r\<close>
            hence \<open>\<xi> \<in> ball (0::'a) r\<close>
              by auto
            hence \<open>-\<xi> \<in> ball (0::'a) r\<close>
              by auto
            thus ?thesis
              by (metis (no_types, lifting) diff_minus_eq_add image_iff)
          qed
        qed
        thus ?thesis
          by (simp add: calculation(2)) 
      qed
      ultimately show ?thesis
        using max_Sup[where X = "ball (0::'a) r" and f = "\<lambda> \<xi>. (norm (f (x + \<xi>)))" 
            and g = "\<lambda> \<xi>. (norm (f (x - \<xi>)))"] by blast
    qed
    also have \<open>\<dots> = Sup ((\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r))\<close>
    proof-
      have \<open>(\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r) = (\<lambda> \<xi>. (norm (f (x - \<xi>)))) ` (ball 0 r)\<close>
      proof auto
        show \<open>norm \<xi> < r \<Longrightarrow>
         norm (f (x + \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x - \<xi>))) ` ball 0 r\<close> for \<xi>
        proof-
          assume \<open>norm \<xi> < r\<close>
          have \<open>norm (f (x + \<xi>)) = norm (f (x - (- \<xi>)))\<close>
            by simp
          moreover have \<open>-\<xi> \<in> ball 0 r\<close>
            by (simp add: \<open>norm \<xi> < r\<close>)            
          ultimately show ?thesis
            by blast             
        qed
        show  \<open>norm \<xi> < r \<Longrightarrow>
         norm (f (x - \<xi>)) \<in> (\<lambda>\<xi>. norm (f (x + \<xi>))) ` ball 0 r\<close> for \<xi>
        proof-
          assume \<open>norm \<xi> < r\<close>
          have \<open>norm (f (x - \<xi>)) = norm (f (x + (- \<xi>)))\<close>
            by simp
          moreover have \<open>-\<xi> \<in> ball 0 r\<close>
            by (simp add: \<open>norm \<xi> < r\<close>)            
          ultimately show ?thesis
            by blast             
        qed
      qed
      hence \<open>Sup ((\<lambda> \<xi>. (norm (f (x + \<xi>)))) ` (ball 0 r)) 
           = Sup ((\<lambda> \<xi>. (norm (f (x - \<xi>)))) ` (ball 0 r))\<close>
        by simp
      thus ?thesis 
        by auto
    qed
    also have \<open>\<dots> = Sup ((\<lambda> \<xi>. (norm (f \<xi>))) ` (ball x r))\<close>
      by (metis  add.right_neutral ball_translation image_image)      
    finally show ?thesis
      by blast
  qed
  ultimately show \<open>onorm f \<le> inverse r * Sup ((norm \<circ> f) ` ball x r)\<close>
    by (simp add: \<open>r > 0\<close>)    
qed


lemma sokal_banach_steinhaus':
  "r > 0 \<Longrightarrow> \<tau> < 1 \<Longrightarrow> f \<noteq> 0 \<Longrightarrow> \<exists>\<xi>\<in>ball x r.  \<tau> * r * norm f \<le> norm (f *\<^sub>v \<xi>)"
proof-
  assume \<open>r > 0\<close> and \<open>\<tau> < 1\<close> and \<open>f \<noteq> 0\<close>
  have  \<open>norm f > 0\<close>
    using \<open>f \<noteq> 0\<close> by auto
  have \<open>norm f \<le> (inverse r) * Sup ( (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) )\<close>
    using \<open>r > 0\<close> sokal_banach_steinhaus by blast
  hence \<open>r * norm f \<le> r * (inverse r) * Sup ( (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) )\<close>
    using \<open>r > 0\<close> by (smt linordered_field_class.sign_simps(4) mult_left_less_imp_less) 
  hence \<open>r * norm f \<le> Sup ( (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) )\<close>
    using \<open>0 < r\<close> by auto
  moreover have \<open>\<tau> * r * norm f < r * norm f\<close>
    using  \<open>\<tau> < 1\<close> using \<open>0 < norm f\<close> \<open>0 < r\<close> by auto
  ultimately have \<open>\<tau> * r * norm f < Sup ( (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) )\<close>
    by simp
  moreover have \<open>(norm \<circ> ( (*\<^sub>v) f)) ` (ball x r) \<noteq> {}\<close>
    using \<open>0 < r\<close> by auto    
  moreover have \<open>bdd_above ((norm \<circ> ( (*\<^sub>v) f)) ` (ball x r))\<close>
    using   \<open>0 < r\<close> apply transfer
    by (meson bounded_linear_ball_bdd_above)    
  ultimately have \<open>\<exists>t \<in> (norm \<circ> ( (*\<^sub>v) f)) ` (ball x r). \<tau> * r * norm f < t\<close> 
    by (simp add: less_cSup_iff)    
  thus ?thesis
    by (smt comp_def image_iff) 
qed

lemma bound_Cauchy_to_lim:
  assumes \<open>y \<longlonglongrightarrow> x\<close>  and \<open>\<And> n. norm (y (Suc n) - y n) \<le> c^n\<close> and \<open>y 0 = 0\<close> and \<open>c < 1\<close>
  shows \<open>norm (x - y (Suc n)) \<le> (c * inverse (1 - c)) * (c ^ n)\<close>
proof-
  have \<open>c \<ge> 0\<close>
    using  \<open>\<And> n. norm (y (Suc n) - y n) \<le> c^n\<close> by (smt norm_imp_pos_and_ge power_Suc0_right)
  have \<open>(\<lambda> N. (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N})) \<longlonglongrightarrow> x - y (Suc n)\<close>
    by (metis (no_types) assms(1) identity_telescopic)
  hence \<open>(\<lambda> N. norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N})) \<longlonglongrightarrow> norm (x - y (Suc n))\<close>
    using tendsto_norm by blast
  moreover have \<open>norm (\<Sum>k = Suc n..N. y (Suc k) - y k) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close> for N
  proof(cases \<open>N < Suc n\<close>)
    case True
    hence \<open>norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}) = 0\<close>
      by auto
    thus ?thesis
      using  \<open>c \<ge> 0\<close> assms(4) by auto      
  next
    case False
    hence \<open>N \<ge> Suc n\<close>
      by auto
    have \<open>norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N})
            \<le> (sum (\<lambda>k. norm (y (Suc k) - y k)) {Suc n .. N})\<close>
      by (simp add: sum_norm_le)
    also have \<open>\<dots> \<le> (sum (power c) {Suc n .. N})\<close>
      using \<open>\<And> n. norm (y (Suc n) - y n) \<le> c^n\<close>
      by (simp add: sum_mono) 
    finally have \<open>norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}) \<le> (sum (power c) {Suc n .. N})\<close>
      by blast
    moreover have \<open>1 - c > 0\<close>
      by (simp add: assms(4))
    ultimately have \<open>(1 - c) * norm (sum (\<lambda>k. y (Suc k) - y k) {Suc n .. N}) 
                   \<le> (1 - c) * (sum (power c) {Suc n .. N})\<close>
      by simp
    also have \<open>\<dots> = c^(Suc n) - c^(Suc N)\<close>
      using Set_Interval.sum_gp_multiplied \<open>Suc n \<le> N\<close> by blast
    also have \<open>\<dots> \<le> c^(Suc n)\<close>
    proof-
      have \<open>c^(Suc N) \<ge> 0\<close>
        using \<open>c \<ge> 0\<close> by auto
      thus ?thesis by auto
    qed
    finally have \<open>(1 - c) * norm (\<Sum>k = Suc n..N. y (Suc k) - y k) \<le> c ^ Suc n\<close>
      by blast
    moreover have \<open>inverse (1 - c) > 0\<close>
      using \<open>0 < 1 - c\<close> by auto      
    ultimately have \<open>(inverse (1 - c)) * ((1 - c) * norm (\<Sum>k = Suc n..N. y (Suc k) - y k) )
                   \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
      by auto
    moreover have \<open>(inverse (1 - c)) * ((1 - c) * norm (\<Sum>k = Suc n..N. y (Suc k) - y k) ) 
          = norm (\<Sum>k = Suc n..N. y (Suc k) - y k)\<close>
    proof-
      have \<open>inverse (1 - c) * (1 - c) = 1\<close>
        using \<open>0 < 1 - c\<close> by auto
      thus ?thesis by auto
    qed
    ultimately show \<open>norm (\<Sum>k = Suc n..N. y (Suc k) - y k) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
      by auto
  qed
  ultimately have \<open>norm (x - y (Suc n)) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
    using Lim_bounded by blast
  hence  \<open>norm (x - y (Suc n)) \<le> (inverse (1 - c)) * (c ^ Suc n)\<close>
    by auto
  moreover have \<open> (inverse (1 - c)) * (c ^ Suc n) = (c * inverse (1 - c)) * (c ^ n)\<close>
    by auto
  ultimately show \<open>norm (x - y (Suc n)) \<le> (c * inverse (1 - c)) * (c ^ n)\<close>
    by linarith 
qed


subsection \<open>Banach-Steinhaus theorem\<close>

theorem banach_steinhaus:
  \<open>(\<And>x. bounded (range (\<lambda>n. (f n) *\<^sub>v x))) \<Longrightarrow> bounded (range f)\<close>
  for f::\<open>'c \<Rightarrow> ('a::banach, 'b::real_normed_vector) real_bounded\<close>
proof-
  assume \<open>\<And>x. bounded (range (\<lambda> n. (f n) *\<^sub>v x))\<close> show ?thesis
  proof(rule classical)
    assume \<open>\<not>(bounded (range f))\<close>
    have \<open>of_rat 2/3 < (1::real)\<close>
      by auto
    hence \<open>\<forall>g::('a, 'b) real_bounded. \<forall>x. \<forall>r. \<exists>\<xi>. g \<noteq> 0 \<and> r > 0
               \<longrightarrow> (\<xi>\<in>ball x r \<and> (of_rat 2/3) * r * norm g \<le> norm (g *\<^sub>v \<xi>))\<close> 
      using sokal_banach_steinhaus'[where \<tau> = "of_rat 2/3"] by blast
    hence \<open>\<exists>\<xi>. \<forall>g::('a, 'b) real_bounded. \<forall>x. \<forall>r. g \<noteq> 0 \<and> r > 0
               \<longrightarrow> ((\<xi> g x r)\<in>ball x r \<and>  (of_rat 2/3) * r * norm g \<le> norm (g *\<^sub>v (\<xi> g x r)))\<close> 
      by metis
    then obtain \<xi> where \<open>\<And>g::('a, 'b) real_bounded. \<And>x. \<And>r. g \<noteq> 0 \<Longrightarrow> r > 0 \<Longrightarrow> 
        \<xi> g x r \<in> ball x r \<and>  (of_rat 2/3) * r * norm g \<le> norm (g *\<^sub>v (\<xi> g x r))\<close>
      by blast
    have \<open>\<forall>n. \<exists>k. norm (f k) \<ge> 4^n\<close>
      using \<open>\<not>(bounded (range f))\<close> by (metis (mono_tags, hide_lams) boundedI image_iff linear)
    hence  \<open>\<exists>k. \<forall>n. norm (f (k n)) \<ge> 4^n\<close>
      by metis
    hence  \<open>\<exists>k. \<forall>n. norm ((f \<circ> k) n) \<ge> 4^n\<close>
      by simp
    then obtain k where \<open>\<And> n. norm ((f \<circ> k) n) \<ge> 4^n\<close> by blast
    define T where \<open>T = f \<circ> k\<close>
    have \<open>T n \<in> range f\<close> for n
      unfolding T_def by simp        
    have \<open>norm (T n) \<ge> of_nat (4^n)\<close> for n
      unfolding T_def using \<open>\<And> n. norm ((f \<circ> k) n) \<ge> 4^n\<close> by auto
    hence \<open>T n \<noteq> 0\<close> for n
      by (smt T_def \<open>\<And>n. 4 ^ n \<le> norm ((f \<circ> k) n)\<close> norm_zero power_not_zero zero_le_power)        
    have \<open>inverse (of_nat 3^n) > (0::real)\<close> for n
      by auto
    define y::\<open>nat \<Rightarrow> 'a\<close> where
      \<open>y = rec_nat 0 (\<lambda>n x. \<xi> (T n) x (inverse (of_nat 3^n)))\<close>
    have \<open>y (Suc n) \<in> ball (y n) (inverse (of_nat 3^n))\<close> for n
      using \<open>\<And>g::('a, 'b) real_bounded. \<And>x. \<And>r. 
        g \<noteq> 0 \<Longrightarrow> r > 0 \<Longrightarrow> 
        \<xi> g x r \<in> ball x r \<and>  (of_rat 2/3) * r * norm g \<le> norm (g *\<^sub>v (\<xi> g x r))\<close>
        \<open>\<And> n. T n \<noteq> 0\<close> \<open>\<And> n. inverse (of_nat 3^n) > 0\<close> unfolding y_def
      by auto       
    hence \<open>norm (y (Suc n) - y n) \<le> inverse (of_nat 3^n)\<close> for n
      unfolding ball_def apply auto using dist_norm
      by (smt norm_minus_commute) 
    moreover have \<open>\<exists>K::real. \<forall>n::nat. sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> K\<close>
    proof-
      have \<open>summable (\<lambda>n. (inverse (real_of_nat 3))^n)\<close>
        using Series.summable_geometric_iff [where c = "inverse (real_of_nat 3)"] by auto
      moreover have \<open>(inverse (real_of_nat 3))^n = inverse (real_of_nat 3^n)\<close> for n::nat
        using power_inverse by blast        
      ultimately have \<open>summable (\<lambda>n. inverse (real_of_nat 3^n))\<close>
        by auto
      hence \<open>bounded (range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n}))\<close>
        using Elementary_Normed_Spaces.summable_imp_sums_bounded[where f = "(\<lambda>n. inverse (real_of_nat 3^n))"]
          lessThan_atLeast0 by auto
      hence \<open>\<exists>M. \<forall>h\<in>(range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n})). norm h \<le> M\<close>
        using bounded_iff by blast
      then obtain M where \<open>\<And>h. h\<in>(range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n})) \<Longrightarrow> norm h \<le> M\<close>
        by blast      
      have \<open>sum (\<lambda>k. inverse (real_of_nat 3^k)) {0..n} \<le> M\<close> for n 
      proof-
        have  \<open>norm (sum (\<lambda> k. inverse (real 3 ^ k)) {0..< Suc n}) \<le> M\<close>
          using \<open>\<And>h. h\<in>(range (\<lambda>n. sum (\<lambda> k. inverse (real 3 ^ k)) {0..<n})) \<Longrightarrow> norm h \<le> M\<close> 
          by blast
        hence  \<open>norm (sum (\<lambda> k. inverse (real 3 ^ k)) {0..n}) \<le> M\<close>
          by (simp add: atLeastLessThanSuc_atLeastAtMost)        
        hence  \<open>(sum (\<lambda> k. inverse (real 3 ^ k)) {0..n}) \<le> M\<close>
          by auto
        thus ?thesis by blast
      qed
      thus ?thesis by blast
    qed
    moreover have \<open>Cauchy y\<close>
      using Banach_Steinhaus_Missing.convergent_series_Cauchy[where a = "\<lambda>n. inverse (of_nat 3^n)" 
          and \<phi> = y] dist_norm
      by (metis calculation(1) calculation(2))         
    hence \<open>\<exists> x. y \<longlonglongrightarrow> x\<close>
      by (simp add: convergent_eq_Cauchy)
    then obtain x where \<open>y \<longlonglongrightarrow> x\<close>
      by blast
    hence \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close> for n
    proof-
      have  \<open>inverse (real_of_nat 3) < 1\<close>
        by simp        
      moreover have \<open>y 0 = 0\<close>
        using y_def by auto
      ultimately have \<open>norm (x - y (Suc n)) 
    \<le> ((inverse (of_nat 3)) * inverse (1 - (inverse (of_nat 3)))) * ((inverse (of_nat 3)) ^ n)\<close>
        using bound_Cauchy_to_lim[where c = "inverse (of_nat 3)" and y = y and x = x]
          power_inverse semiring_norm(77)  \<open>y \<longlonglongrightarrow> x\<close>
          \<open>\<And> n. norm (y (Suc n) - y n) \<le> inverse (of_nat 3^n)\<close>
        by metis        
      moreover have \<open>(inverse (real_of_nat 3)) * inverse (1 - (inverse (of_nat 3))) = inverse (of_nat 2)\<close>
        by auto
      ultimately show ?thesis
        by (metis power_inverse) 
    qed      
    have \<open>\<exists> M. \<forall> n. norm (T n *\<^sub>v x) \<le> M\<close>
    proof-
      have \<open>\<exists> M. \<forall> n. norm ((f n) *\<^sub>v x) \<le> M\<close>
        by (metis \<open>\<And>x. bounded (range (\<lambda>n. f n *\<^sub>v x))\<close> bounded_iff rangeI)
      thus ?thesis unfolding T_def by auto
    qed
    then obtain M where \<open>\<And> n. norm (T n *\<^sub>v x) \<le> M\<close>
      by blast
    have \<open>\<exists>n. M < (inverse (of_nat 6)) * (of_rat (4/3)^n)\<close>
      by (simp add: Elementary_Topology.real_arch_pow)
    moreover have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> M\<close> for n
    proof-
      have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> (inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n)\<close>
      proof-
        have \<open>of_rat (4/3)^n = inverse (real 3 ^ n) * (of_nat 4^n)\<close>
        proof -
          have "real_of_rat (inverse (rat_of_nat 3) * rat_of_nat 4) ^ n = inverse (real_of_rat (rat_of_nat 3) ^ n) * real_of_rat (rat_of_nat 4) ^ n"
            by (metis (no_types) divide_inverse_commute of_rat_divide power_divide)
          thus ?thesis
            by auto
        qed            
        also have \<open>\<dots> \<le>  inverse (real 3 ^ n) * norm (T n)\<close>
          using \<open>\<And>n. norm (T n) \<ge> of_nat (4^n)\<close>
          by simp
        finally have \<open>of_rat (4/3)^n \<le> inverse (real 3 ^ n) * norm (T n)\<close>
          by blast
        moreover have \<open>inverse (of_nat 6) > (0::real)\<close>
          by auto
        ultimately show ?thesis by auto
      qed
      also have \<open>\<dots> \<le> norm (T n *\<^sub>v x)\<close> 
      proof-
        have \<open>(of_rat 2/3)*(inverse (of_nat 3^n))*norm (T n) \<le> norm ((T n) *\<^sub>v (y (Suc n)))\<close> 
          using \<open>\<And>g::('a, 'b) real_bounded. \<And>x. \<And>r. 
                  g \<noteq> 0 \<Longrightarrow> r > 0 \<Longrightarrow> 
                  \<xi> g x r \<in> ball x r \<and>  (of_rat 2/3) * r * norm g \<le> norm (g *\<^sub>v (\<xi> g x r))\<close>
            \<open>\<And> n. T n \<noteq> 0\<close> \<open>\<And> n. inverse (of_nat 3^n) > 0\<close> unfolding y_def
          by auto
        also have \<open>\<dots> = norm ((T n) *\<^sub>v ((y (Suc n) - x) + x))\<close>
          by auto
        also have \<open>\<dots> = norm ((T n) *\<^sub>v (y (Suc n) - x) + (T n) *\<^sub>v x)\<close>
          apply transfer apply auto by (metis diff_add_cancel linear_simps(1))
        also have \<open>\<dots> \<le> norm ((T n) *\<^sub>v (y (Suc n) - x)) + norm ((T n) *\<^sub>v x)\<close>
          by (simp add: norm_triangle_ineq)
        also have \<open>\<dots> \<le> norm (T n) * norm (y (Suc n) - x) + norm ((T n) *\<^sub>v x)\<close>
        proof-
          have \<open>norm ((T n) *\<^sub>v (y (Suc n) - x)) \<le> norm (T n) * norm (y (Suc n) - x)\<close>
            apply transfer apply auto using onorm by auto 
          thus ?thesis by simp
        qed
        also have \<open>\<dots> \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))*norm (T n) + norm ((T n) *\<^sub>v x)\<close>
        proof-
          have \<open>norm (y (Suc n) - x) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close>
            using \<open>norm (x - y (Suc n)) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))\<close>
            by (simp add: norm_minus_commute)
          moreover have \<open>norm (T n) \<ge> 0\<close>
            by auto
          ultimately have \<open>norm (T n) * norm (y (Suc n) - x) \<le> (inverse (of_nat 2))*(inverse (of_nat 3^n))*norm (T n)\<close>
            by (simp add: \<open>\<And>n. T n \<noteq> 0\<close>)
          thus ?thesis by simp
        qed
        finally have \<open>(of_rat 2/3) * inverse (real 3 ^ n) * norm (T n)
              \<le> inverse (real 2) * inverse (real 3 ^ n) * norm (T n) + norm (T n *\<^sub>v x)\<close>
          by blast
        hence \<open>(of_rat 2/3) * inverse (real 3 ^ n) * norm (T n) 
             - inverse (real 2) * inverse (real 3 ^ n) * norm (T n) \<le> norm (T n *\<^sub>v x)\<close>
          by linarith
        thus \<open>(inverse (of_nat 6)) * inverse (real 3 ^ n) * norm (T n) \<le> norm (T n *\<^sub>v x)\<close>
          by (simp add: linordered_field_class.sign_simps(5))          
      qed
      finally have \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> norm (T n *\<^sub>v x)\<close>
        by auto
      thus \<open>(inverse (of_nat 6)) * (of_rat (4/3)^n) \<le> M\<close>
        using \<open>\<And> n. norm (T n *\<^sub>v x) \<le> M\<close> by smt
    qed                      
    ultimately show ?thesis
      by smt   
  qed
qed

subsection \<open>A consequence of Banach-Steinhaus theorem\<close>

corollary bounded_linear_limit_bounded_linear:
  fixes f :: \<open>nat \<Rightarrow> ('a::{banach, perfect_space} \<Rightarrow> 'b::real_normed_vector)\<close> and F :: \<open>'a\<Rightarrow>'b\<close>
  assumes  \<open>\<And> n. bounded_linear (f n)\<close> and \<open>f \<midarrow>pointwise\<rightarrow> F\<close> 
  shows \<open>bounded_linear F\<close> 
proof-
  have \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close>
    using \<open>f \<midarrow>pointwise\<rightarrow> F\<close> by (simp add: pointwise_convergent_to_def)
  have \<open>linear F\<close>
    using assms(1) assms(2) bounded_linear.linear linear_limit_linear by blast
  moreover have \<open>bounded_linear_axioms F\<close>
  proof
    have "\<exists>K. \<forall> n. \<forall>x. norm ((f n) x) \<le> norm x * K"
    proof-
      have \<open>\<exists> M. \<forall> n. norm ((f n) x) \<le> M\<close> for x
      proof-
        have \<open>isCont (\<lambda> t::'b. norm t) y\<close> for y::'b
          using Limits.isCont_norm by simp
        hence \<open>(\<lambda> n. norm ((f n) x)) \<longlonglongrightarrow> (norm (F x))\<close>
          using \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> by (simp add: tendsto_norm)
        thus ?thesis using Elementary_Metric_Spaces.convergent_imp_bounded
          by (metis UNIV_I \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> bounded_iff image_eqI)
      qed
      hence \<open>\<exists> M. \<forall> n. onorm (f n) \<le> M\<close>
      proof-
        have \<open>\<And> n. bounded_linear (f n)\<close>
          by (simp add: assms(1) bounded_linear.bounded_linear)           
        moreover have  \<open>\<And>x. \<exists>M. \<forall>n. norm (f n x) \<le> M\<close>
          by (simp add: \<open>\<And>x. \<exists>M. \<forall>n. norm (f n x) \<le> M\<close>)          
        ultimately show ?thesis 
          using banach_steinhaus sorry          
      qed
      then obtain M where \<open>\<forall> n. \<forall> x. onorm (f n) \<le> M\<close>
        by blast
      have \<open>\<forall> n. \<forall>x. norm ((f n) x) \<le> norm x * onorm (f n)\<close>
        using \<open>\<And> n. bounded_linear (f n)\<close> by (metis assms(1) mult.commute onorm)
      thus ?thesis using  \<open>\<forall> n. \<forall> x. onorm (f n) \<le> M\<close>
        by (metis (no_types, hide_lams) dual_order.trans norm_eq_zero order_refl real_mult_le_cancel_iff2 vector_space_over_itself.scale_zero_left zero_less_norm_iff)    
    qed
    thus "\<exists>K. \<forall>x. norm (F x) \<le> norm x * K"
      using  \<open>\<And> x::'a. (\<lambda> n. (f n) x) \<longlonglongrightarrow> F x\<close> by (metis Lim_bounded tendsto_norm) 
  qed
  ultimately show ?thesis unfolding bounded_linear_def by blast
qed


end

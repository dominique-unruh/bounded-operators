lemma bounded_operator_basis_existence_uniq:
  fixes S::\<open>'a::chilbert_space set\<close> and \<phi>::\<open>'a \<Rightarrow> 'b::chilbert_space\<close>
  assumes \<open>complex_vector.span S = UNIV\<close> 
    and \<open>complex_vector.independent S\<close>
    and \<open>finite S\<close>
  shows \<open>\<exists>!F. \<forall>s\<in>S. times_bounded_vec F s = \<phi> s\<close>
proof-
  have \<open>complex_independent S\<close>
    using \<open>complex_vector.independent S\<close>
    by (simp add: Complex_Vector_Spaces.dependent_raw_def)
  have \<open>\<exists>t. x = (\<Sum>s\<in>S. t s *\<^sub>C s)\<close>
    for x
    by (simp add: Complex_Vector_Spaces.span_explicit_finite assms)
  hence \<open>\<exists> t. \<forall>x. x = (\<Sum>s\<in>S. t x s *\<^sub>C s)\<close>
    by metis
  then obtain t where t_def: "\<And>x. x = (\<Sum>s\<in>S. t x s *\<^sub>C s)"
    by blast
  define f where \<open>f x = (\<Sum>s\<in>S. t x s *\<^sub>C \<phi> s)\<close> for x
  have \<open>s\<in>S \<Longrightarrow> bounded_clinear (\<lambda> x. t x s)\<close>
    for s
  proof
    show "clinear (\<lambda>x. t x s)"
      if "s \<in> S"
      unfolding clinear_def proof
      show "t (b1 + b2) s = t b1 s + t b2 s"
        for b1 :: 'a
          and b2 :: 'a
      proof-
        have \<open>b1 = (\<Sum>s\<in>S. t b1 s *\<^sub>C s)\<close>
          using \<open>\<And> x. x = (\<Sum>s\<in>S. t x s *\<^sub>C s)\<close>
          by blast
        moreover have \<open>b2 = (\<Sum>s\<in>S. t b2 s *\<^sub>C s)\<close>
          using \<open>\<And> x. x = (\<Sum>s\<in>S. t x s *\<^sub>C s)\<close>
          by blast
        ultimately have \<open>b1 + b2 = (\<Sum>s\<in>S. (t b1 s *\<^sub>C s + t b2 s *\<^sub>C s))\<close>
          by (metis (mono_tags, lifting) sum.cong sum.distrib)
        also have \<open>\<dots> = (\<Sum>s\<in>S. (t b1 s + t b2 s) *\<^sub>C s)\<close>
          by (metis scaleC_add_left)
        finally have \<open>b1 + b2 = (\<Sum>s\<in>S. (t b1 s + t b2 s) *\<^sub>C s)\<close>
          by blast
        moreover have \<open>b1 + b2 = (\<Sum>s\<in>S. t (b1 + b2) s *\<^sub>C s)\<close>
          by (simp add: \<open>\<And>x. x = (\<Sum>s\<in>S. t x s *\<^sub>C s)\<close>)          
        ultimately have \<open>(\<Sum>s\<in>S. t (b1 + b2) s *\<^sub>C s) = (\<Sum>s\<in>S. (t b1 s + t b2 s) *\<^sub>C s)\<close>
          by simp
        hence \<open>0 = (\<Sum>s\<in>S. t (b1 + b2) s *\<^sub>C s) - (\<Sum>s\<in>S. (t b1 s + t b2 s) *\<^sub>C s)\<close>
          by simp
        also have \<open>\<dots> = (\<Sum>s\<in>S. ( t (b1 + b2) s ) *\<^sub>C s - (t b1 s + t b2 s) *\<^sub>C s) \<close>
          by (simp add: sum_subtractf)
        also have \<open>\<dots> = (\<Sum>s\<in>S. ( t (b1 + b2) s - (t b1 s + t b2 s)) *\<^sub>C s)\<close>
          by (metis (no_types, lifting) scaleC_left.diff)
        finally have \<open>0 = (\<Sum>s\<in>S. ( t (b1 + b2) s - (t b1 s + t b2 s)) *\<^sub>C s)\<close>
          by blast
        hence \<open>(\<Sum>s\<in>S. ( t (b1 + b2) s - (t b1 s + t b2 s)) *\<^sub>C s) = 0\<close>
          by auto
        hence \<open>t (b1 + b2) s - (t b1 s + t b2 s) = 0\<close>
          using \<open>complex_independent S\<close> \<open>s\<in>S\<close>
          using independentD[where s = S and t = S 
              and u = "\<lambda>s. t (b1 + b2) s - (t b1 s + t b2 s)"] 
          apply auto
          using assms(3) by auto
        hence \<open>t (b1 + b2) s = t b1 s + t b2 s\<close>
          by simp
        thus ?thesis
          by simp
      qed
      show "t (r *\<^sub>C b) s = r *\<^sub>C t b s"
        for r :: complex
          and b :: 'a
      proof-
        have \<open>b = (\<Sum>s\<in>S. t b s *\<^sub>C s)\<close>
          using \<open>\<And> x. x = (\<Sum>s\<in>S. t x s *\<^sub>C s)\<close>
          by blast
        hence \<open>r *\<^sub>C b =  r *\<^sub>C (\<Sum>s\<in>S. (t b s *\<^sub>C s))\<close>
          by auto
        also have \<open>\<dots> =  (\<Sum>s\<in>S.  r *\<^sub>C (t b s *\<^sub>C s))\<close>
          by (metis (mono_tags, lifting) Finite_Cartesian_Product.sum_cong_aux scaleC_right.sum)
        also have \<open>\<dots> =  (\<Sum>s\<in>S.  (r * t b s) *\<^sub>C s)\<close>
          by auto
        finally have \<open>r *\<^sub>C b = (\<Sum>s\<in>S. (r * t b s) *\<^sub>C s)\<close>
          by blast
        moreover have \<open>r *\<^sub>C b = (\<Sum>s\<in>S. t (r *\<^sub>C b) s *\<^sub>C s)\<close>
          by (simp add: \<open>\<And>x. x = (\<Sum>s\<in>S. t x s *\<^sub>C s)\<close>)          
        ultimately have \<open>(\<Sum>s\<in>S. t (r *\<^sub>C b) s *\<^sub>C s) = (\<Sum>s\<in>S. (r * t b s) *\<^sub>C s)\<close>
          by simp
        hence \<open>0 = (\<Sum>s\<in>S. t (r *\<^sub>C b) s *\<^sub>C s) - (\<Sum>s\<in>S. (r * t b s) *\<^sub>C s)\<close>
          by simp
        also have \<open>\<dots> = (\<Sum>s\<in>S. t (r *\<^sub>C b) s *\<^sub>C s - (r * t b s) *\<^sub>C s)\<close>
          by (simp add: sum_subtractf)
        also have \<open>\<dots> = (\<Sum>s\<in>S. (t (r *\<^sub>C b) s  - (r * t b s)) *\<^sub>C s)\<close>
          by (metis (no_types, lifting) scaleC_left.diff)
        finally have \<open>0 = (\<Sum>s\<in>S. (t (r *\<^sub>C b) s  - (r * t b s)) *\<^sub>C s)\<close>
          by blast
        hence \<open>(\<Sum>s\<in>S. (t (r *\<^sub>C b) s  - (r * t b s)) *\<^sub>C s) = 0\<close>
          by auto
        hence \<open>t (r *\<^sub>C b) s  - (r * t b s) = 0\<close>
        proof -
          have "\<And>f. (\<Sum>a\<in>S. f a *\<^sub>C a) \<noteq> 0 \<or> f s = 0"
            using  assms(3) complex_vector.dependent_finite 
              that
            by (metis Complex_Vector_Spaces.dependent_raw_def assms(2)) 
          thus ?thesis
            using \<open>(\<Sum>s\<in>S. (t (r *\<^sub>C b) s - r * t b s) *\<^sub>C s) = 0\<close> 
            by fastforce
        qed
        hence \<open>t (r *\<^sub>C b) s  = r * t b s\<close>
          by auto
        thus ?thesis
          by auto 
      qed
    qed

    thus "\<exists>K. \<forall>x. norm (t x s) \<le> norm x * K"
      if "s \<in> S"
      sorry
        (*   using assms(3) that
    proof (induction S arbitrary: t)
      case (empty t)
      thus ?case by simp 
    next
      case (insert x S t)
      have "x = (\<Sum>s\<in>S. t x s *\<^sub>C s)"

      thus "\<exists>K. \<forall>x. cmod (t x s) \<le> norm x * K" sorry
    qed *)
  qed
  hence \<open>s \<in> S \<Longrightarrow> bounded_clinear (\<lambda> x. (t x s) *\<^sub>C \<phi> s )\<close>
    for s
    by (simp add: bounded_clinear_scaleC_const)    
  hence \<open>bounded_clinear f\<close>
    unfolding f_def
    using Complex_Vector_Spaces.bounded_clinear_sum[where I = S and f = "\<lambda> s. \<lambda>x. t x s *\<^sub>C \<phi> s"]
    by auto
  hence \<open>\<exists> F. (*\<^sub>v) F = f\<close>
    using times_bounded_vec_cases by auto
  then obtain F where \<open>(*\<^sub>v) F = f\<close>
    by blast
  have "s\<in>S \<Longrightarrow> f s = \<phi> s" for s
  proof-
    assume "s\<in>S"
    have "\<exists>R. S = insert s R \<and> s \<notin> R"
      by (meson Set.set_insert \<open>s \<in> S\<close>)        
    then obtain R where g1: "S = insert s R" and g2: "s \<notin> R"
      by blast
    have b1: "s = (\<Sum>a\<in>S. t s a *\<^sub>C a)"
      using t_def by blast
    have f2: "t s s = 1"
    proof(rule classical)
      assume "\<not>(t s s = 1)"
      hence c1: "1 - t s s \<noteq> 0"
        by simp
      have "s = t s s *\<^sub>C s + (\<Sum>a\<in>R. t s a *\<^sub>C a)"
        using assms(3) b1 g1 g2 by auto
      hence "(\<Sum>a\<in>R. t s a *\<^sub>C a) = s - t s s *\<^sub>C s"
        by (metis add_diff_cancel_left')
      also have "\<dots> = (1 - t s s) *\<^sub>C s"
        by (simp add: complex_vector.scale_left_diff_distrib)
      finally have "(\<Sum>a\<in>R. t s a *\<^sub>C a) =  (1 - t s s) *\<^sub>C s"
        by blast
      hence "(1 - t s s) *\<^sub>C s \<in> complex_vector.span R"
        by (metis (no_types, lifting) complex_vector.span_base complex_vector.span_scale 
            complex_vector.span_sum)
      hence "(1/(1 - t s s)) *\<^sub>C ((1 - t s s) *\<^sub>C s) \<in> complex_vector.span R"
        using c1 by (smt complex_vector.span_scale)
      hence "s \<in> complex_vector.span R"
        by (smt Complex_Vector_Spaces.vector_fraction_eq_iff c1 scaleC_one) 
      hence "complex_vector.dependent S"
        using g1 g2  by (smt complex_vector.independent_insert) 
      thus ?thesis
        by (metis \<open>Complex_Vector_Spaces.dependent S\<close> \<open>complex_independent S\<close>)
    qed
    have f3: "b\<in>S \<Longrightarrow> b \<noteq> s \<Longrightarrow> t s b = 0" for b
    proof-
      assume c1: "b\<in>S" and c2: "b \<noteq> s"
      have "s = s + (\<Sum>a\<in>R. t s a *\<^sub>C a)"
        using assms(3) b1 f2 g1 g2 by auto
      hence "(\<Sum>a\<in>R. t s a *\<^sub>C a) = 0"
        by simp
      thus "t s b = 0"
        using \<open>complex_independent S\<close> assms(3) c1 c2 complex_vector.independentD g1 by auto        
    qed
    have "(\<Sum>a\<in>S. t s a *\<^sub>C \<phi> a) = \<phi> s"
    proof-
      have "(\<Sum>a\<in>S. t s a *\<^sub>C \<phi> a) = t s s *\<^sub>C \<phi> s + (\<Sum>a\<in>R. t s a *\<^sub>C \<phi> a)"
        using g1 g2 assms(3) by auto 
      moreover have "(\<Sum>a\<in>R. t s a *\<^sub>C \<phi> a) = 0"
      proof-
        have "a\<in>R \<Longrightarrow> t s a = 0" for a
          using f3 g2 g1 by auto
        thus ?thesis by simp 
      qed
      ultimately show ?thesis
        by (simp add: f2) 
    qed
    thus "f s = \<phi> s" unfolding f_def by blast
  qed
  hence "s\<in>S \<Longrightarrow> F *\<^sub>v s = \<phi> s"
    for s
    using \<open>(*\<^sub>v) F = f\<close>
    by simp 
  moreover have "G = F"
    if "\<forall>s\<in>S. G *\<^sub>v s = \<phi> s"
    for G :: "('a, 'b) bounded"
  proof-
    have "\<forall>s\<in>S. G *\<^sub>v s =  F *\<^sub>v s"
      using that
      by (simp add: calculation)
    hence "\<forall>s\<in>S. F *\<^sub>v s - G *\<^sub>v s = 0"
      by simp
    moreover have "\<forall>s\<in>S. F *\<^sub>v s - G *\<^sub>v s = (F - G) *\<^sub>v s"
      by (simp add: minus_bounded.rep_eq)
    ultimately have fg0: "\<forall>s\<in>S. (F - G) *\<^sub>v s = 0"
      by simp
    hence "(F - G) *\<^sub>v s = 0" for s
    proof-
      have "s \<in> complex_vector.span S"
        using \<open>complex_vector.span S = UNIV\<close>
        by blast
      hence "\<exists>r S'. finite S' \<and> S' \<subseteq> S \<and> s = (\<Sum>a\<in>S'. r a *\<^sub>C a)"
        using complex_vector.span_explicit[where b=S] by blast
      then obtain r S' where fg1: "finite S'" and fg2: "S' \<subseteq> S" and fg3: "s = (\<Sum>a\<in>S'. r a *\<^sub>C a)"
        by blast
      have "(F - G) *\<^sub>v s = (F - G) *\<^sub>v (\<Sum>a\<in>S'. r a *\<^sub>C a)"
        using fg3 by blast
      also have "\<dots> = (\<Sum>a\<in>S'. r a *\<^sub>C ((F - G) *\<^sub>v a))"
        using clinear_finite_sum fg1 by auto 
      also have "\<dots> = 0"
        by (metis (mono_tags, lifting) Diff_iff assms(3) complex_vector.scale_eq_0_iff fg0 fg2 
            sum.mono_neutral_left sum.not_neutral_contains_not_neutral)
      finally show ?thesis
        by blast
    qed
    hence "F - G = 0"
      apply transfer by metis
    thus ?thesis by simp
  qed
  ultimately show ?thesis
    by blast 
qed

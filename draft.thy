theory draft
  imports Tensor_Product

begin

unbundle bounded_notation

lemma atensorOp_bounded_clinear:
  fixes f::\<open>'a::complex_inner \<Rightarrow> 'c::complex_inner\<close> and g::\<open>'b::complex_inner \<Rightarrow> 'c\<close>
  assumes \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close>
  shows  \<open>bounded_clinear (f \<otimes>\<^sub>A g)\<close>
proof-
  have \<open>clinear (f \<otimes>\<^sub>A g)\<close>
    using atensorOp_clinear \<open>bounded_clinear f\<close> and \<open>bounded_clinear g\<close> 
    unfolding bounded_clinear_def
    by blast 
  moreover have \<open>\<exists> K. \<forall> z. norm ((f \<otimes>\<^sub>A g) z) \<le> norm z * K\<close>
  proof-
    have \<open>\<exists>Kf. \<forall>z. norm (f z) \<le> norm z * Kf \<and> Kf > 0\<close>
      using \<open>bounded_clinear f\<close>
      using bounded_clinear.bounded_linear bounded_linear.pos_bounded 
      by blast
    then obtain Kf where \<open>\<And>z. norm (f z) \<le> norm z * Kf\<close> and \<open>Kf > 0\<close>
      by blast
    have \<open>\<exists>Kg. \<forall>z. norm (g z) \<le> norm z * Kg \<and> Kg > 0\<close>
      using \<open>bounded_clinear g\<close>
      using bounded_clinear.bounded_linear bounded_linear.pos_bounded 
      by blast
    then obtain Kg where \<open>\<And>z. norm (g z) \<le> norm z * Kg\<close> and \<open>Kg > 0\<close>
      by blast
    define K where \<open>K = Kf * Kg\<close>
    have separation: \<open>norm ((f \<otimes>\<^sub>A g) (x \<otimes>\<^sub>a y)) \<le> norm (x \<otimes>\<^sub>a y) * K\<close>
      for x y
    proof-
      have \<open>(f \<otimes>\<^sub>A g) (x \<otimes>\<^sub>a y) = (f x) \<otimes>\<^sub>a (g y)\<close>
        by (simp add: \<open>bounded_clinear f\<close> \<open>bounded_clinear g\<close> atensorOp_separation bounded_clinear.is_clinear)
      hence \<open>norm ((f \<otimes>\<^sub>A g) (x \<otimes>\<^sub>a y)) = norm ((f x) \<otimes>\<^sub>a (g y))\<close>
        by simp
      also have \<open>\<dots> = norm (f x) * norm (g y)\<close>
        by (simp add: atensor_norm_mult)
      also have \<open>\<dots> \<le> (norm x * Kf) * (norm y * Kg)\<close>
        by (simp add: \<open>\<And>z. norm (f z) \<le> norm z * Kf\<close> \<open>\<And>z. norm (g z) \<le> norm z * Kg\<close> mult_mono')
      also have \<open>\<dots> = norm x * norm y * K\<close>
        unfolding K_def
        by simp
      also have \<open>\<dots> = norm (x \<otimes>\<^sub>a y) * K\<close>
      proof-
        have \<open>norm (x \<otimes>\<^sub>a y) = norm x * norm y\<close>
          by (simp add: atensor_norm_mult)
        thus ?thesis by simp
      qed
      finally show ?thesis by simp
    qed
    hence \<open>norm ((f \<otimes>\<^sub>A g) z) \<le> norm z * K\<close>
      for z
    proof-
      have \<open>K > 0\<close>
        by (simp add: K_def \<open>0 < Kf\<close> \<open>0 < Kg\<close>)
      have \<open>norm ((f \<otimes>\<^sub>A g) z) \<le> (norm z) * K\<close>
      proof-
        have \<open>\<exists> A::'a set. complex_vector.span A = UNIV \<and> complex_vector.independent A\<close>
          using complex_vector.independent_empty complex_vector.independent_extend_basis complex_vector.span_extend_basis 
          by auto
        then obtain A::\<open>'a set\<close> where \<open>complex_vector.span A = UNIV\<close> and \<open>complex_vector.independent A\<close>
          by blast
        have \<open>\<exists> B::'b set. complex_vector.span B = UNIV \<and> complex_vector.independent B\<close>
          using complex_vector.independent_empty complex_vector.independent_extend_basis complex_vector.span_extend_basis 
          by auto
        then obtain B::\<open>'b set\<close> where \<open>complex_vector.span B = UNIV\<close> and \<open>complex_vector.independent B\<close>
          by blast
        have \<open>z \<in> complex_vector.span ((case_prod (\<otimes>\<^sub>a) ` (A \<times> B)))\<close>
          by (metis UNIV_I \<open>complex_vector.span A = UNIV\<close> \<open>complex_vector.span B = UNIV\<close> basis_atensor_complex_generator)          
        hence \<open>\<exists> r t. finite t \<and> t \<subseteq> (case_prod (\<otimes>\<^sub>a) ` (A \<times> B)) \<and> z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
          by (smt complex_vector.span_alt mem_Collect_eq)
        then obtain r t where \<open>finite t\<close> and \<open>t \<subseteq> (case_prod (\<otimes>\<^sub>a) ` (A \<times> B))\<close> 
            and \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> by blast
        have \<open>(f \<otimes>\<^sub>A g) z = (\<Sum>a\<in>t. (f \<otimes>\<^sub>A g) (r a *\<^sub>C a))\<close>
          using \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> calculation complex_vector.linear_sum by fastforce
        also have \<open>\<dots> = (\<Sum>a\<in>t. r a *\<^sub>C ((f \<otimes>\<^sub>A g) a))\<close>
          by (meson \<open>clinear (f \<otimes>\<^sub>A g)\<close> complex_vector.linear_scale)
        finally have \<open>(f \<otimes>\<^sub>A g) z = (\<Sum>a\<in>t. r a *\<^sub>C ((f \<otimes>\<^sub>A g) a))\<close>
          by blast
        hence \<open>norm ((f \<otimes>\<^sub>A g) z) = norm (\<Sum>a\<in>t. r a *\<^sub>C ((f \<otimes>\<^sub>A g) a))\<close>
          by simp
        also have \<open>\<dots> = norm (\<Sum>a\<in>t. ((r a)*(norm a)) *\<^sub>C (((f \<otimes>\<^sub>A g) a)/\<^sub>C (norm a)))\<close>
        proof-
          have \<open>a \<in> t \<Longrightarrow> norm a \<noteq> 0\<close>
            for a
          proof-
            assume \<open>a \<in> t\<close>
            moreover have \<open>complex_vector.independent (case_prod (\<otimes>\<^sub>a) ` (A \<times> B))\<close>
              using \<open>complex_vector.independent A\<close> \<open>complex_vector.independent B\<close>
                atensor_complex_independent_case_prod[where A = "A" and B = "B"] 
              by blast
            ultimately have \<open>a \<noteq> 0\<close>
              using \<open>t \<subseteq> case_prod (\<otimes>\<^sub>a) ` (A \<times> B)\<close>
              by (meson complex_vector.dependent_zero in_mono)
            thus ?thesis by simp
          qed
          hence \<open>a \<in> t \<Longrightarrow> r a *\<^sub>C ((f \<otimes>\<^sub>A g) a) = ((r a)*(norm a)) *\<^sub>C (((f \<otimes>\<^sub>A g) a)/\<^sub>C (norm a))\<close>
            for a
          proof-
            assume \<open>a \<in> t\<close>
            hence \<open>norm a \<noteq> 0\<close>
              using \<open>\<And>a. a \<in> t \<Longrightarrow> norm a \<noteq> 0\<close> by blast
            hence \<open>(norm a)*(inverse (norm a)) = 1\<close>
              by simp
            hence \<open>r a *\<^sub>C ((f \<otimes>\<^sub>A g) a) = ((r a)*(norm a)*(inverse (norm a))) *\<^sub>C ((f \<otimes>\<^sub>A g) a)\<close>
              by (metis (no_types, lifting) mult.right_neutral of_real_1 of_real_mult scaleC_scaleC)
            also have \<open>\<dots> = ((r a)*(norm a)) *\<^sub>C (((inverse (norm a)) *\<^sub>C ((f \<otimes>\<^sub>A g) a)))\<close>
              by simp
            finally show ?thesis by auto
          qed
          thus ?thesis
            by (metis (no_types, lifting) sum.cong) 
        qed
        also have \<open>\<dots> \<le> (sqrt (\<Sum>a\<in>t. (norm (r a))^2 * (norm a)^2  )) * (sqrt (\<Sum>a\<in>t. (norm ((f \<otimes>\<^sub>A g) a))^2 / (norm a)^2 ))\<close>
          sorry (* Cauchy–Bunyakovsky–Schwarz inequality *)
        also have \<open>\<dots> \<le> (norm z) * (sqrt (\<Sum>a\<in>t. (norm ((f \<otimes>\<^sub>A g) a))^2 / (norm a)^2 ))\<close>
          sorry
        also have \<open>\<dots> \<le> (norm z) * K\<close>
        proof-
          have \<open>(sqrt (\<Sum>a\<in>t. (norm ((f \<otimes>\<^sub>A g) a))^2 / (norm a)^2 )) \<le> K\<close>
            sorry (* I think that it is false *)
          thus ?thesis sorry
        qed

        show ?thesis sorry
      qed
(*
      have \<open>(norm ((f \<otimes>\<^sub>A g) z))^2 \<le> (norm z)^2 * (K^2)\<close>
      proof-
        have \<open>\<exists> A::'a set. complex_vector.span A = UNIV \<and> complex_vector.independent A\<close>
          using complex_vector.independent_empty complex_vector.independent_extend_basis complex_vector.span_extend_basis 
          by auto
        then obtain A::\<open>'a set\<close> where \<open>complex_vector.span A = UNIV\<close> and \<open>complex_vector.independent A\<close>
          by blast
        have \<open>\<exists> B::'b set. complex_vector.span B = UNIV \<and> complex_vector.independent B\<close>
          using complex_vector.independent_empty complex_vector.independent_extend_basis complex_vector.span_extend_basis 
          by auto
        then obtain B::\<open>'b set\<close> where \<open>complex_vector.span B = UNIV\<close> and \<open>complex_vector.independent B\<close>
          by blast
        have \<open>z \<in> complex_vector.span ((case_prod (\<otimes>\<^sub>a) ` (A \<times> B)))\<close>
          by (metis UNIV_I \<open>complex_vector.span A = UNIV\<close> \<open>complex_vector.span B = UNIV\<close> basis_atensor_complex_generator)          
        hence \<open>\<exists> r t. finite t \<and> t \<subseteq> (case_prod (\<otimes>\<^sub>a) ` (A \<times> B)) \<and> z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
          by (smt complex_vector.span_alt mem_Collect_eq)
        then obtain r t where \<open>finite t\<close> and \<open>t \<subseteq> (case_prod (\<otimes>\<^sub>a) ` (A \<times> B))\<close> 
            and \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> by blast
        (* I need to express z as an expansion in an orthogonal basis *) 
        have \<open>\<forall> a a'. a \<in> t \<and> a' \<in> t \<and> a \<noteq> a' \<longrightarrow> \<langle>a, a'\<rangle> = 0\<close>
          sorry
        hence \<open>(norm z)^2 = (\<Sum>a\<in>t. norm (r a)^2 * (norm a)^2)\<close>
          using \<open>finite t\<close> \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
              Pythagorean_generalized[where t = "t"]
          by auto
        have \<open>(f \<otimes>\<^sub>A g) z = (\<Sum>a\<in>t. r a *\<^sub>C ((f \<otimes>\<^sub>A g) a))\<close>
          using \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
          by (smt Finite_Cartesian_Product.sum_cong_aux calculation complex_vector.linear_scale complex_vector.linear_sum)
        hence \<open>(norm ((f \<otimes>\<^sub>A g) z))^2 = (norm (\<Sum>a\<in>t. r a *\<^sub>C ((f \<otimes>\<^sub>A g) a)))^2\<close>
          by simp
        also have \<open>\<dots> \<le> ( \<Sum>a\<in>t. ( norm (r a *\<^sub>C ((f \<otimes>\<^sub>A g) a)))^2 )\<close>
        proof-
          have \<open>norm (\<Sum>a\<in>t. r a *\<^sub>C ((f \<otimes>\<^sub>A g) a)) \<le> (\<Sum>a\<in>t. norm (r a *\<^sub>C ((f \<otimes>\<^sub>A g) a)) )\<close>
            sorry
          show ?thesis sorry
        qed
        also have \<open>\<dots> = ( \<Sum>a\<in>t. (norm (r a))^2 * (norm ((f \<otimes>\<^sub>A g) a))^2 )\<close>
          by (metis (no_types, lifting) norm_scaleC power_mult_distrib)          
        also have \<open>\<dots> \<le> (\<Sum>a\<in>t. (norm (r a))^2 * (norm a)^2 * K^2)\<close>
        proof-
          have \<open>a \<in> t \<Longrightarrow> (norm (r a))^2 * (norm ((f \<otimes>\<^sub>A g) a))^2 \<le> (norm (r a))^2 * (norm a)^2 * K^2\<close>
            for a
          proof-
            assume \<open>a \<in> t\<close>
            hence \<open>a \<in> range (case_prod (\<otimes>\<^sub>a))\<close>
              using \<open>t \<subseteq> (case_prod (\<otimes>\<^sub>a) ` (A \<times> B))\<close>
              by blast
            hence \<open>norm ((f \<otimes>\<^sub>A g) a) \<le> norm a * K\<close>
              using separation by auto
            hence \<open>(norm ((f \<otimes>\<^sub>A g) a))^2 \<le> (norm a)^2 * K^2\<close>
              by (metis norm_ge_zero power_mono power_mult_distrib)
            thus ?thesis
              by (smt mult_cancel_left power2_less_eq_zero_iff real_mult_le_cancel_iff2 semiring_normalization_rules(17) zero_eq_power2) 
          qed
          thus ?thesis
            by (simp add: sum_mono) 
        qed
        also have \<open>\<dots> = (\<Sum>a\<in>t. (norm (r a))^2 * (norm a)^2) * K^2\<close>
          by (metis (mono_tags, lifting) sum.cong sum_distrib_right)
        also have \<open>\<dots> = (norm z)^2 * K^2\<close>
          using \<open>(norm z)\<^sup>2 = (\<Sum>a\<in>t. (cmod (r a))\<^sup>2 * (norm a)\<^sup>2)\<close> 
          by presburger
        finally show \<open>(norm ((f \<otimes>\<^sub>A g) z))^2 \<le> (norm z)^2 * K^2\<close>
          by blast
      qed
*)
      thus ?thesis 
        using \<open>K > 0\<close>
        sorry 
    qed
    thus ?thesis by blast
  qed
  ultimately show ?thesis unfolding bounded_clinear_def 
    by blast
qed


lemma hilbert_tensor_existence'_left':
  fixes S :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close>
  assumes \<open>bounded_clinear S\<close> 
  shows \<open>\<exists> H :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h ('c::chilbert_space).
  bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy) \<and> onorm H \<le> onorm S\<close>
proof-
  define k::\<open>'a \<Rightarrow> 'c \<Rightarrow> 'b\<otimes>\<^sub>h'c\<close> where \<open>k x y = (S x) \<otimes>\<^sub>h y\<close> for x y
  have \<open>cbilinear k\<close>
    unfolding k_def cbilinear_def
  proof
    show "\<forall>y. clinear (\<lambda>x. S x \<otimes>\<^sub>h (y::'c))"
    proof
      show "clinear (\<lambda>x. S x \<otimes>\<^sub>h (y::'c))"
        for y :: 'c
        unfolding clinear_def proof
        show "S (b1 + b2) \<otimes>\<^sub>h y = S b1 \<otimes>\<^sub>h y + S b2 \<otimes>\<^sub>h y"
          for b1 :: 'a
            and b2 :: 'a
        proof-
          have \<open>S (b1 + b2) = S b1 + S b2\<close>
            using \<open>bounded_clinear S\<close>
            unfolding bounded_clinear_def clinear_def Vector_Spaces.linear_def module_hom_def 
               module_hom_axioms_def by auto
          thus ?thesis
            by (simp add: htensor_distr_left)             
        qed

        show "S (r *\<^sub>C b) \<otimes>\<^sub>h y = r *\<^sub>C (S b \<otimes>\<^sub>h y)"
          for r :: complex
            and b :: 'a
        proof-
          have \<open>S (r *\<^sub>C b) = r *\<^sub>C (S b)\<close>
            using \<open>bounded_clinear S\<close>
            unfolding bounded_clinear_def clinear_def
            by (simp add: assms bounded_clinear.is_clinear complex_vector.linear_scale)
          thus ?thesis
            by (simp add: htensor_mult_left) 
        qed
      qed
    qed
    show "\<forall>x. clinear ((\<otimes>\<^sub>h) (S x)::'c \<Rightarrow> 'b \<otimes>\<^sub>h _)"
      unfolding clinear_def proof
      show "Vector_Spaces.linear ((*\<^sub>C)::complex \<Rightarrow> 'c \<Rightarrow> _) (*\<^sub>C) ((\<otimes>\<^sub>h) (S x))"
        for x :: 'a
      proof
        show "S x \<otimes>\<^sub>h ((b1::'c) + b2) = S x \<otimes>\<^sub>h b1 + S x \<otimes>\<^sub>h b2"
          for b1 :: 'c
            and b2 :: 'c
          by (simp add: htensor_distr_right)

        show "S x \<otimes>\<^sub>h r *\<^sub>C (b::'c) = r *\<^sub>C (S x \<otimes>\<^sub>h b)"
          for r :: complex
            and b :: 'c
          by (simp add: htensor_mult_right)
      qed
    qed
  qed

  hence \<open>\<exists>! K :: 'a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'c. clinear K \<and> (\<forall> x y. k x y = K (x \<otimes>\<^sub>a y))\<close>
    by (simp add: atensor_universal_property)
  then obtain K::\<open>'a \<otimes>\<^sub>a 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'c\<close> where \<open>clinear K\<close> and \<open>\<forall> x y. k x y = K (x \<otimes>\<^sub>a y)\<close>
    by blast
  have \<open>\<exists> H. bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = K (x \<otimes>\<^sub>a y))\<close> 
    sorry
  then obtain H where \<open>bounded_clinear H\<close> and \<open>\<forall> x y. H (x \<otimes>\<^sub>h y) = K (x \<otimes>\<^sub>a y)\<close>
    by blast
  have \<open>bounded_clinear H\<close>
    sorry
  moreover have \<open>\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy\<close> 
    sorry
  moreover have \<open>onorm H \<le> onorm S\<close>
    sorry
  ultimately show ?thesis by blast
qed

lemma hilbert_tensor_existence'_right':
  fixes T :: \<open>'c::chilbert_space \<Rightarrow> 'd::chilbert_space\<close>
  assumes \<open>bounded_clinear T\<close> 
  shows \<open>\<exists> H :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> ('a::chilbert_space) \<otimes>\<^sub>h 'd. 
  bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)) \<and> onorm H \<le> onorm T\<close>
  sorry



lemma hilbert_tensor_existence'':
  fixes S :: \<open>'a::chilbert_space \<Rightarrow> 'b::chilbert_space\<close> and 
        T :: \<open>'c::chilbert_space \<Rightarrow> 'd::chilbert_space\<close>
  assumes \<open>bounded_clinear S\<close> and  \<open>bounded_clinear T\<close>
  shows \<open>\<exists> H :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd. 
  bounded_clinear H \<and> (\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>h(T y)) \<and> onorm H \<le> onorm S * onorm T\<close>
proof-
  have \<open>\<exists> HS :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h ('c::chilbert_space). 
  bounded_clinear HS \<and> (\<forall> x y. HS (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy) \<and> onorm HS \<le> onorm S\<close>
    by (simp add: hilbert_tensor_existence'_left' assms(1))
  then obtain HS::\<open>'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'c\<close> where \<open>bounded_clinear HS\<close> and 
  \<open>\<forall> x y. HS (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy\<close> and \<open>onorm HS \<le> onorm S\<close> by blast
  have \<open>\<exists> HT :: 'b \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd. 
  bounded_clinear HT \<and> (\<forall> x y. HT (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)) \<and> onorm HT \<le> onorm T\<close>
    by (simp add: hilbert_tensor_existence'_right' assms(2))
  then obtain HT::\<open>'b \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd\<close> where \<open>bounded_clinear HT\<close> and 
  \<open>\<forall> x y. HT (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)\<close> and \<open>onorm HT \<le> onorm T\<close> by blast
  define H where \<open>H = HT \<circ> HS\<close>
  have \<open>bounded_clinear H\<close>
    unfolding H_def
    using \<open>bounded_clinear HT\<close> \<open>bounded_clinear HS\<close>
      Complex_Vector_Spaces.comp_bounded_clinear[where A = "HT" and B = "HS"]
    by blast
  moreover have \<open>\<forall> x y. H (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>h(T y)\<close>
    using \<open>\<forall> x y. HS (x \<otimes>\<^sub>h y) = (S x)\<otimes>\<^sub>hy\<close> \<open>\<forall> x y. HT (x \<otimes>\<^sub>h y) = x\<otimes>\<^sub>h(T y)\<close> H_def 
    by auto
  moreover have \<open>onorm H \<le> onorm S * onorm T\<close>
    using \<open>onorm HS \<le> onorm S\<close> \<open>onorm HT \<le> onorm T\<close>
    by (smt H_def \<open>bounded_clinear HS\<close> \<open>bounded_clinear HT\<close> bounded_clinear.bounded_linear mult_mono' onorm_compose onorm_pos_le ordered_field_class.sign_simps(5))
  ultimately show ?thesis by blast
qed


lemma hilbert_tensor_existence':
  fixes S :: \<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and 
    T :: \<open>('c::chilbert_space, 'd::chilbert_space) bounded\<close>
  shows \<open>\<exists> H :: ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded.  (\<forall> x y. H *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> 
          norm H \<le> norm S * norm T\<close>
proof-
  have \<open>bounded_clinear (times_bounded_vec S)\<close>
    using times_bounded_vec by blast
  moreover have \<open>bounded_clinear (times_bounded_vec T)\<close>
    using times_bounded_vec by blast
  ultimately have \<open>\<exists> h :: 'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd. 
  bounded_clinear h \<and> (\<forall> x y. h (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and>
      onorm h \<le> onorm (times_bounded_vec S) * onorm (times_bounded_vec T)\<close>
    using hilbert_tensor_existence'' by blast
  then obtain h :: \<open>'a \<otimes>\<^sub>h 'c \<Rightarrow> 'b \<otimes>\<^sub>h 'd\<close> where
    \<open>bounded_clinear h\<close> and \<open>\<forall> x y. h (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)\<close>
     and \<open>onorm h \<le> onorm (times_bounded_vec S) * onorm (times_bounded_vec T)\<close>
    by blast
  from \<open>bounded_clinear h\<close>
  have \<open>\<exists> H. times_bounded_vec H = h\<close>
    using times_bounded_vec_cases by auto
  then obtain H where \<open>times_bounded_vec H = h\<close>
    by blast
  have \<open>\<forall>x y. H *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y)\<close>
    using \<open>times_bounded_vec H = h\<close> \<open>\<forall> x y. h (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)\<close>
    by auto
  moreover have \<open>norm H \<le> norm S * norm T\<close>
    using \<open>times_bounded_vec H = h\<close> \<open>onorm h \<le> onorm (times_bounded_vec S) * onorm (times_bounded_vec T)\<close>
    by (simp add: norm_bounded.rep_eq)
  ultimately show ?thesis by blast
qed

lemma htensorOp_existence:
  \<open>\<exists> H :: ('a::chilbert_space, 'b::chilbert_space) bounded \<Rightarrow>
  ('c::chilbert_space, 'd::chilbert_space) bounded \<Rightarrow>
  ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded. \<forall> S T.
   (\<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> norm (H S T) \<le> norm S * norm T\<close>
  using hilbert_tensor_existence' by metis

definition htensorOp :: \<open>('a::chilbert_space, 'b::chilbert_space) bounded
 \<Rightarrow> ('c::chilbert_space, 'd::chilbert_space ) bounded
 \<Rightarrow> (('a \<otimes>\<^sub>h 'c),  ('b \<otimes>\<^sub>h 'd)) bounded\<close> (infixl "\<otimes>\<^sub>H" 70)
  where \<open>htensorOp = (SOME H :: ('a, 'b) bounded \<Rightarrow> ('c, 'd) bounded \<Rightarrow> 
    ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded. (
    \<forall> S T. \<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y) \<and> 
    norm (H S T) \<le> norm S * norm T
))\<close> 

lemma htensorOp_I1:
  fixes S::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and
        T::\<open>('c::chilbert_space, 'd::chilbert_space) bounded\<close>
  shows \<open>(S \<otimes>\<^sub>H T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y)\<close>
proof-
  define P::\<open>(('a, 'b) bounded \<Rightarrow> ('c, 'd) bounded \<Rightarrow> ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded) \<Rightarrow> bool\<close> where 
 \<open>P H = (\<forall> S T. (\<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> 
        norm (H S T) \<le> norm S * norm T)\<close> for H
  have  \<open>\<exists> H. P H\<close>
    unfolding P_def
    by (simp add: htensorOp_existence)
  hence  \<open>P (\<lambda> S T. S \<otimes>\<^sub>H T)\<close>
    by (smt someI_ex htensorOp_def P_def) 
      (* > 1 s *)
  thus ?thesis
    by (simp add: P_def) 
qed

lemma htensorOp_I2:
  fixes S::\<open>('a::chilbert_space, 'b::chilbert_space) bounded\<close> and
        T::\<open>('c::chilbert_space, 'd::chilbert_space) bounded\<close>
  shows \<open>norm (S \<otimes>\<^sub>H T) \<le> norm S * norm T\<close>
proof-
  define P::\<open>(('a, 'b) bounded \<Rightarrow> ('c, 'd) bounded \<Rightarrow> ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded) \<Rightarrow> bool\<close> where 
 \<open>P H = (\<forall> S T. (\<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x)\<otimes>\<^sub>h(T *\<^sub>v y)) \<and> 
        norm (H S T) \<le> norm S * norm T)\<close> for H
  have  \<open>\<exists> H. P H\<close>
    unfolding P_def
    by (simp add: htensorOp_existence)
  hence  \<open>P (\<lambda> S T. S \<otimes>\<^sub>H T)\<close>
    by (smt someI_ex htensorOp_def P_def) 
      (* > 1 s *)
  thus ?thesis
    by (simp add: P_def) 
qed




unbundle no_bounded_notation


end

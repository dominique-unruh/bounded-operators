theory draft
  imports Tensor_Product

begin

unbundle bounded_notation


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

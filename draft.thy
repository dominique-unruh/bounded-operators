theory draft
  imports Tensor_Product

begin

unbundle bounded_notation


lemma htensorOp_existence:
  \<open>\<exists> H :: ('a::chilbert_space, 'b::chilbert_space) bounded \<Rightarrow> ('c::chilbert_space, 'd::chilbert_space) bounded \<Rightarrow> 
    ('a \<otimes>\<^sub>h 'c,  'b \<otimes>\<^sub>h 'd) bounded. (
    \<forall> S T. \<forall> x y. (H S T) *\<^sub>v (x \<otimes>\<^sub>h y) = (S *\<^sub>v x) \<otimes>\<^sub>h (T *\<^sub>v y) \<and> 
    norm (H S T) \<le> norm S * norm T)\<close>
  sorry

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
    using htensorOp_existence
    by auto
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
    using htensorOp_existence
    by auto
  hence  \<open>P (\<lambda> S T. S \<otimes>\<^sub>H T)\<close>
    by (smt someI_ex htensorOp_def P_def) 
      (* > 1 s *)
  thus ?thesis
    by (simp add: P_def) 
qed




unbundle no_bounded_notation


end

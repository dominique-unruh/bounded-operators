section \<open>Missing results about Jordan_Normal_Form)\<close>
(*
Authors: 
  Dominique Unruh, University of Tartu, unruh@ut.ee      
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)                 

theory Jordan_Normal_Form_Missing
  imports
    Complex_L2 Jordan_Normal_Form.Matrix
begin
text \<open>This theory defines bundes to activate/deactivate the notation
  from \<^session>\<open>Jordan_Normal_Form\<close>.
                                                                         
Reactivate the notation locally via "@{theory_text \<open>includes jnf_notation\<close>}" in a lemma statement.
(Or sandwich a declaration using that notation between "@{theory_text \<open>unbundle jnf_notation ... unbundle no_jnf_notation\<close>}.)
\<close>

bundle jnf_notation begin
notation transpose_mat ("(_\<^sup>T)" [1000])
notation cscalar_prod (infix "\<bullet>c" 70)
notation vec_index (infixl "$" 100)
notation smult_vec (infixl "\<cdot>\<^sub>v" 70)
notation scalar_prod (infix "\<bullet>" 70)
notation index_mat (infixl "$$" 100)
notation smult_mat (infixl "\<cdot>\<^sub>m" 70)
notation mult_mat_vec (infixl "*\<^sub>v" 70)
notation pow_mat (infixr "^\<^sub>m" 75)
notation append_vec (infixr "@\<^sub>v" 65)
notation append_rows (infixr "@\<^sub>r" 65)
end


bundle no_jnf_notation begin
no_notation transpose_mat ("(_\<^sup>T)" [1000])
no_notation cscalar_prod (infix "\<bullet>c" 70)
no_notation vec_index (infixl "$" 100)
no_notation smult_vec (infixl "\<cdot>\<^sub>v" 70)
no_notation scalar_prod (infix "\<bullet>" 70)
no_notation index_mat (infixl "$$" 100)
no_notation smult_mat (infixl "\<cdot>\<^sub>m" 70)
no_notation mult_mat_vec (infixl "*\<^sub>v" 70)
no_notation pow_mat (infixr "^\<^sub>m" 75)
no_notation append_vec (infixr "@\<^sub>v" 65)
no_notation append_rows (infixr "@\<^sub>r" 65)
end

unbundle jnf_notation


lemma mat_entry_explicit:
  fixes M :: "complex mat"
  assumes "M \<in> carrier_mat m n" and "i < m" and "j < n"
  shows   "vec_index (M *\<^sub>v unit_vec n j) i = M $$ (i,j)"
proof-
  have dim_col1: "dim_col M = n"
    using assms(1) by blast
  have dim_vec1: "dim_vec (unit_vec n j) = n"
    by simp
  have "vec_index (M *\<^sub>v unit_vec n j) i = scalar_prod (row M i) (unit_vec n j)"
    using assms(1) assms(2) by auto
  also have "\<dots> = scalar_prod (vec n (\<lambda>j. M $$ (i, j))) (unit_vec n j)"
    unfolding row_def using dim_col1 by simp 
  also have "\<dots> = (\<Sum>k\<in>{0..<n}. vec_index (vec n (\<lambda>j. M $$ (i, j))) k * vec_index (unit_vec n j) k)"
    unfolding scalar_prod_def using dim_vec1 by auto
  also have "\<dots> = vec_index (vec n (\<lambda>j. M $$ (i, j))) j * vec_index (unit_vec n j) j
           + (\<Sum>k\<in>{0..<n}-{j}. vec_index (vec n (\<lambda>j. M $$ (i, j))) k * vec_index (unit_vec n j) k)"
  proof-
    have "j\<in>{0..<n}"
      by (simp add: assms(3))
    thus ?thesis 
      by (simp add: sum.remove)
  qed
  also have "\<dots> = vec_index (vec n (\<lambda>j. M $$ (i, j))) j * vec_index (unit_vec n j) j"
  proof-
    have "vec_index (vec n (\<lambda>j. M $$ (i, j))) k * vec_index (unit_vec n j) k = 0"
      if "k \<in>{0..<n}-{j}"
      for k
    proof-
      have "vec_index (unit_vec n j) k = 0"
        using that
        by (simp add: assms(3)) 
      thus ?thesis
        by (simp add: \<open>vec_index (unit_vec n j) k = 0\<close>) 
    qed
    hence "(\<Sum>k\<in>{0..<n}-{j}. vec_index (vec n (\<lambda>j. M $$ (i, j))) k * vec_index (unit_vec n j) k) = 0"
      using sum_not_0 by blast      
    thus ?thesis by simp
  qed
  also have "\<dots> = vec_index (vec n (\<lambda>j. M $$ (i, j))) j"
  proof-
    have "vec_index (unit_vec n j) j = 1"
      by (simp add: assms(3))      
    thus ?thesis
      by auto 
  qed
  also have "\<dots> = M $$ (i, j)"
    by (simp add: assms(3))
  finally show ?thesis by simp
qed

unbundle no_jnf_notation


end

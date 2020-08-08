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

definition "adjoint_mat M = transpose_mat (map_mat cnj M)"


lemma adjoint_mat_swap:
  fixes M ::"complex mat"
  assumes "M \<in> carrier_mat nB nA" and "iA < dim_row M" and "iB < dim_col M"
  shows "(adjoint_mat M)$$(iB,iA) = cnj (M$$(iA,iB))"
  unfolding adjoint_mat_def transpose_mat_def map_mat_def
  by (simp add: assms(2) assms(3))


lemma cscalar_prod_adjoint:
  fixes M:: "complex mat"
  assumes a1: "M \<in> carrier_mat nB nA" 
    and a2: "dim_vec v = nA"
    and a3: "dim_vec u = nB"
  shows "v \<bullet>c ((adjoint_mat M) *\<^sub>v u) = (M *\<^sub>v v) \<bullet>c u"
proof-
  define N where "N = adjoint_mat M"
  have b1: "N \<in> carrier_mat nA nB"
    unfolding N_def
    using a1 unfolding adjoint_mat_def by simp
  hence b2: "dim_vec (N *\<^sub>v u) = nA"    
    using a3 dim_mult_mat_vec by blast
  hence b3: "dim_vec (conjugate (N *\<^sub>v u)) = nA"
    by simp
  have b4: " (conjugate v) $ i = cnj (vec_index v i)"
    if "i < nA"
    for i
    using a2 that by auto
  have b5: "(Matrix.row N) i = (Matrix.col (map_mat cnj M)) i"
    if "i < nA"
    for i
    unfolding N_def adjoint_mat_def
    using row_transpose a1 that by auto    
  have b6: "vec_index (N *\<^sub>v u) i = cnj (scalar_prod ( (Matrix.col M) i ) (conjugate u))"
    if "i < nA"
    for i
  proof-
    have "vec_index (N *\<^sub>v u) i = scalar_prod ((Matrix.row N) i) u"
      using Matrix.index_mult_mat_vec
      using b1 that by auto
    also have "\<dots> = scalar_prod ((Matrix.col (map_mat cnj M)) i) u"
      by (simp add: b5 that)
    also have "\<dots> = scalar_prod ( conjugate ((Matrix.col M) i) ) u"
      by (smt a1 carrier_matD(2) col_map_mat conjugate_complex_def dim_col dim_vec_conjugate eq_vecI 
          index_map_mat(2) index_map_vec(1) that vec_index_conjugate)
    also have "\<dots> = cnj (scalar_prod ( (Matrix.col M) i ) (conjugate u))"
      by (metis a1 a3 carrier_matD(1) carrier_vec_dim_vec col_dim complex_cnj_cnj 
          conjugate_complex_def conjugate_conjugate_sprod)
    finally show ?thesis .
  qed    
  have b7: "dim_vec (conjugate u) = nB"
    by (simp add: a3)
  have b8: "vec_index (conjugate u) j = cnj (vec_index u j)"
    if "j < nB"
    for j
    by (simp add: a3 that)    
  have b9: "scalar_prod ( (Matrix.col M) i ) (conjugate u) = 
      (\<Sum>j=0..< nB.  vec_index ( (Matrix.col M) i ) j * cnj (vec_index u j) )"
    if "i < nA"
    for i
    unfolding scalar_prod_def
    using b7 b8 by auto
  have b10: "vec_index (M *\<^sub>v v) j = 
      (\<Sum>i=0..<nA.  
      vec_index ( (Matrix.col M) i ) j  * (vec_index v i) )"
    if "j < nB"
    for j
  proof-
    have "vec_index ( (Matrix.col M) i ) j = vec_index ( (Matrix.row M) j ) i"
      if "i < nA"
      for i
      unfolding col_def row_def
      using \<open>j < nB\<close> a1 that by auto 
    moreover have "vec_index (M *\<^sub>v v) j = 
      (\<Sum>i=0..<nA.  
      vec_index ( (Matrix.row M) j ) i  * (vec_index v i) )"
      unfolding mult_mat_vec_def scalar_prod_def using a2 a1 index_vec that by blast
    ultimately show ?thesis by simp
  qed
  have "v \<bullet>c ((adjoint_mat M) *\<^sub>v u) = cnj ((N *\<^sub>v u) \<bullet>c v)"
    by (metis N_def a2 b2 carrier_vec_dim_vec conjugate_complex_def conjugate_conjugate_sprod 
        conjugate_vec_sprod_comm)    
  also have "\<dots> = cnj (\<Sum>i = 0..<nA.
            vec_index (N *\<^sub>v u) i * vec_index (conjugate v) i)"
    unfolding scalar_prod_def
    by (simp add: a2)    
  also have "\<dots> = cnj (\<Sum>i = 0..<nA.
            vec_index (N *\<^sub>v u) i * cnj (vec_index v i))"
    using b4 by simp
  also have "\<dots> = (\<Sum>i = 0..<nA.
            (cnj (vec_index (N *\<^sub>v u) i)) * (vec_index v i))"
    by auto
  also have "\<dots> = (\<Sum>i = 0..<nA.
            (cnj (cnj (scalar_prod ( (Matrix.col M) i ) (conjugate u)))) * (vec_index v i))"
    using b6 by auto
  also have "\<dots> = (\<Sum>i = 0..<nA.
            (scalar_prod ( (Matrix.col M) i ) (conjugate u)) * (vec_index v i))"
    by simp
  also have "\<dots> = (\<Sum>i = 0..<nA.
                  (\<Sum>j=0..< nB.  
      vec_index ( (Matrix.col M) i ) j * cnj (vec_index u j) ) * (vec_index v i))"
    using b9 by simp
  also have "\<dots> = (\<Sum>i=0..<nA.
                  (\<Sum>j=0..< nB.  
      vec_index ( (Matrix.col M) i ) j * cnj (vec_index u j) * (vec_index v i) ))"
    by (simp add: vector_space_over_itself.scale_sum_left)
  also have "\<dots> = (\<Sum>i=0..<nA.
                  (\<Sum>j=0..<nB.  
      vec_index ( (Matrix.col M) i ) j  * (vec_index v i) * cnj (vec_index u j) ))"
    by (smt conjugate_complex_def mult.commute sum.cong vector_space_over_itself.scale_scale)
  also have "\<dots> = (\<Sum>j=0..<nB.
                  (\<Sum>i=0..<nA.  
      vec_index ( (Matrix.col M) i ) j  * (vec_index v i) * cnj (vec_index u j) ))"
    using sum.swap by auto
  also have "\<dots> = (\<Sum>j=0..<nB.
                  (\<Sum>i=0..<nA.  
      vec_index ( (Matrix.col M) i ) j  * (vec_index v i) ) * cnj (vec_index u j) )"
    by (simp add: vector_space_over_itself.scale_sum_left)
  also have "\<dots> = (\<Sum>j\<in>{0..<nB}. vec_index (M *\<^sub>v v) j * cnj (vec_index u j))"
    using b10 by simp
  also have "\<dots> = (M *\<^sub>v v) \<bullet>c u"
    unfolding scalar_prod_def using a3 by auto
  finally show ?thesis .
qed

unbundle no_jnf_notation


end

theory General_Results_Missing
imports Complex_Main "HOL-Analysis.Infinite_Set_Sum"

begin

lemma bij_inj:
  assumes \<open>f \<circ> f = id\<close>
  shows \<open>inj f\<close>
proof(rule injI)
  fix x y
  assume \<open>f x = f y\<close>
  hence \<open>f (f x) = f (f y)\<close>
    by simp
  hence \<open>(f \<circ> f) x = (f \<circ> f) y\<close>
    by simp
  thus \<open>x = y\<close>
    by (simp add: assms)
qed


lemma big_sum_reordering_fst:
  fixes  S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. f z) = (\<Sum>u\<in>fst ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>S}. f (u, v)))\<close>
proof-
  define g where \<open>g z = (if z \<in> S then f z else 0)\<close>
    for z
  have \<open>(\<Sum>z\<in>S. f z) = (\<Sum>z\<in>S. g z)\<close>
    unfolding g_def
    by auto
  also have \<open>\<dots>  = (\<Sum>z\<in>((fst ` S) \<times> (snd ` S)). g z)\<close>
  proof-
    have \<open>S \<subseteq> ((fst ` S) \<times> (snd ` S))\<close>
      by (simp add: subset_fst_snd)
    thus ?thesis unfolding g_def
      by (smt DiffD2 assms finite_SigmaI finite_imageI sum.mono_neutral_right)
        (* > 1s *)
  qed
  also have \<open>\<dots>  = (\<Sum>u\<in>(fst ` S). (\<Sum>v\<in>(snd ` S). g (u,v)))\<close>
    by (simp add: sum.cartesian_product)
  also have \<open>\<dots>  = (\<Sum>u\<in>(fst ` S). (\<Sum>v\<in>{v|v. (u,v)\<in>S}.  f (u, v)) )\<close>
  proof-
    have \<open>u \<in> fst ` S \<Longrightarrow> (\<Sum>v\<in>(snd ` S). g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}.  f (u, v))\<close>
      for u
    proof-
      have \<open>{v|v. (u,v)\<in>S} \<subseteq> (snd ` S)\<close>
        using image_iff by fastforce
      hence \<open>(\<Sum>v\<in>(snd ` S). g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}. g (u,v))
             + (\<Sum>v\<in>(snd ` S)-{v|v. (u,v)\<in>S}. g (u,v))\<close>
        by (simp add: add.commute assms sum.subset_diff)
      moreover have \<open>(\<Sum>v\<in>(snd ` S)-{v|v. (u,v)\<in>S}. g (u,v)) = 0\<close>
        by (simp add: g_def)        
      moreover have \<open>(\<Sum>v\<in>{v|v. (u,v)\<in>S}. g (u,v)) = (\<Sum>v\<in>{v|v. (u,v)\<in>S}. f (u,v))\<close>
        unfolding g_def
        by auto
      ultimately show ?thesis by auto
    qed
    thus ?thesis
      by auto 
  qed
  finally show ?thesis by blast
qed

definition swap::\<open>'a \<times> 'b \<Rightarrow> 'b \<times> 'a\<close> where
\<open>swap z =  (snd z, fst z)\<close> for z

lemma swap_involution:
\<open>swap \<circ> swap = id\<close>
  unfolding swap_def by auto

lemma swap_inj:
\<open>inj swap\<close>
proof(rule injI)
  fix x y::\<open>'a \<times> 'b\<close>
  assume \<open>swap x = swap y\<close> 
  hence \<open>swap (swap x) = swap (swap y)\<close> 
    by simp
  moreover have \<open>swap (swap x) = x\<close>
    by (simp add: pointfree_idE swap_involution) 
  moreover have \<open>swap (swap y) = y\<close>
    by (simp add: pointfree_idE swap_involution) 
  ultimately show \<open>x = y\<close>
    by simp
qed

lemma swap_set_fst:
\<open>fst ` (swap ` S) = snd ` S\<close>
  unfolding swap_def apply auto
  apply (simp add: rev_image_eqI)
  by (metis (no_types, lifting) fst_conv image_cong image_eqI pair_in_swap_image prod.swap_def)

lemma swap_set_snd:
\<open>snd ` (swap ` S) = fst ` S\<close>
  unfolding swap_def apply auto
  apply (simp add: rev_image_eqI)
  by (metis (no_types, lifting) fst_conv image_eqI snd_conv)


lemma big_sum_reordering_snd:
  fixes  S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. f z) = (\<Sum>v\<in>snd ` S. (\<Sum>u\<in>{u|u. (u,v)\<in>S}. f (u, v)))\<close>
proof-
  have \<open>swap \<circ> (swap::('a \<times> 'b \<Rightarrow> 'b \<times> 'a)) = id\<close>
    by (simp add: swap_involution)    
  hence \<open>(\<Sum>z\<in>S. f z) = (\<Sum>z\<in>swap ` (swap ` S). f z)\<close>
    by (simp add: \<open>swap \<circ> swap = id\<close> image_comp)
  also have \<open>\<dots> = (\<Sum>z\<in>(swap ` S). (f \<circ> swap) z)\<close>
  proof-
    have \<open>inj swap\<close>
      by (simp add: swap_inj)      
    show ?thesis
      by (meson \<open>inj swap\<close> inj_def inj_on_def sum.reindex)    
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>fst ` (swap ` S). (\<Sum>v\<in>{v|v. (u,v)\<in>(swap ` S)}. (f \<circ> swap) (u,v)))\<close>
  proof-
    have \<open>finite (swap ` S)\<close>
      using \<open>finite S\<close> by simp
    thus ?thesis
    using big_sum_reordering_fst[where S = "swap ` S" and f = "f \<circ> swap"]
    by blast
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>(swap ` S)}. (f \<circ> swap) (u,v)))\<close>
  proof-
    have \<open>fst ` (swap ` S) = snd ` S\<close>
      by (simp add: swap_set_fst) 
    thus ?thesis by simp
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>(swap ` S)}. f (v,u) ))\<close>
  proof-
    have \<open>swap (u, v) = (v, u)\<close>
      for u::'a and v::'b
      unfolding swap_def by auto
    hence \<open>(f \<circ> swap) (u, v) = f (v, u)\<close>
      for v::'a and u::'b
      by (metis \<open>swap \<circ> swap = id\<close> comp_apply swap_comp_swap swap_simp)
    thus ?thesis by simp      
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (v,u)\<in>S}. f (v,u) ))\<close>
  proof-
    have \<open>(u,v)\<in>(swap ` S) \<longleftrightarrow> (v,u)\<in>S\<close>
      for u v
      by (metis General_Results_Missing.swap_def image_cong pair_in_swap_image prod.swap_def)
    thus ?thesis by simp
  qed
  finally show ?thesis by blast
qed



end

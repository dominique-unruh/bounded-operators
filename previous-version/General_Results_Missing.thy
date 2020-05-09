section \<open>\<open>General_Results_Missing\<close> -- Miscellaneous missing facts\<close>

theory General_Results_Missing
  imports Complex_Main Complex_Inner_Product "HOL-Analysis.Infinite_Set_Sum"
    "HOL-ex.Sketch_and_Explore" HOL.Groups General_Results_Missing_Banach_Steinhaus
begin


(* TODO: Never used in Bounded Operators. Move to tensor product. *)
(* Jose: I do not know how to move information from one library to another *)
(* TODO: Should be possible now because you have both libraries in GitHub Desktop now *)
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

(* TODO: Never used in Bounded Operators. Move to tensor product. *)
lemma swap_set_fst:
  \<open>fst ` (prod.swap ` S) = snd ` S\<close>
  unfolding prod.swap_def apply auto
   apply (simp add: rev_image_eqI)
  by (metis (no_types, lifting) fst_conv image_cong image_eqI pair_in_swap_image prod.swap_def)

(* TODO: Never used in Bounded Operators. Move to tensor product. *)
lemma swap_set_snd:
  \<open>snd ` (prod.swap ` S) = fst ` S\<close>
  unfolding prod.swap_def apply auto
   apply (simp add: rev_image_eqI)
  using image_iff by fastforce

(* TODO: Never used in Bounded Operators. Move to tensor product. *)
lemma big_sum_reordering_snd:
  fixes  S :: \<open>('a \<times> 'b) set\<close>
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. f z) = (\<Sum>v\<in>snd ` S. (\<Sum>u\<in>{u|u. (u,v)\<in>S}. f (u, v)))\<close>
proof-
  have \<open>prod.swap \<circ> (prod.swap::('a \<times> 'b \<Rightarrow> 'b \<times> 'a)) = id\<close>
    by simp    
  hence \<open>(\<Sum>z\<in>S. f z) = (\<Sum>z\<in>prod.swap ` (prod.swap ` S). f z)\<close>
    by (simp add: \<open>prod.swap \<circ> prod.swap = id\<close> image_comp)
  also have \<open>\<dots> = (\<Sum>z\<in>(prod.swap ` S). (f \<circ> prod.swap) z)\<close>
  proof-
    have \<open>inj prod.swap\<close>
      by simp      
    show ?thesis
      by (meson \<open>inj prod.swap\<close> inj_def inj_on_def sum.reindex)    
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>fst ` (prod.swap ` S). (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. (f \<circ> prod.swap) (u,v)))\<close>
  proof-
    have \<open>finite (prod.swap ` S)\<close>
      using \<open>finite S\<close> by simp
    thus ?thesis
      using big_sum_reordering_fst[where S = "prod.swap ` S" and f = "f \<circ> prod.swap"]
      by blast
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. (f \<circ> prod.swap) (u,v)))\<close>
  proof-
    have \<open>fst ` (prod.swap ` S) = snd ` S\<close>
      by (simp add: swap_set_fst) 
    thus ?thesis by simp
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (u,v)\<in>(prod.swap ` S)}. f (v,u) ))\<close>
  proof-
    have \<open>prod.swap (u, v) = (v, u)\<close>
      for u::'a and v::'b
      unfolding prod.swap_def by auto
    hence \<open>(f \<circ> prod.swap) (u, v) = f (v, u)\<close>
      for v::'a and u::'b
      by simp
    thus ?thesis by simp      
  qed
  also have \<open>\<dots> = (\<Sum>u\<in>snd ` S. (\<Sum>v\<in>{v|v. (v,u)\<in>S}. f (v,u) ))\<close>
  proof-
    have \<open>(u,v)\<in>(prod.swap ` S) \<longleftrightarrow> (v,u)\<in>S\<close>
      for u v
      by simp
    thus ?thesis by simp
  qed
  finally show ?thesis by blast
qed

subclass (in card2) not_singleton
  apply standard using two_le_card
  by (meson card_2_exists ex_card) 


lemma linear_space_top_not_bot[simp]: "(top::'a::{complex_vector,t1_space,not_singleton} linear_space) \<noteq> bot"
  by (metis General_Results_Missing.UNIV_not_singleton bot_linear_space.rep_eq top_linear_space.rep_eq)
 
lemma linear_space_bot_not_top[simp]: "(bot::'a::{complex_vector,t1_space,not_singleton} linear_space) \<noteq> top"
proof-
  have \<open>\<exists> x::'a. x \<noteq> 0\<close>
    using not_singleton_existence
    by auto
  thus ?thesis 
    apply transfer
    unfolding UNIV_def
    by blast
qed


end


theory General_Results_Missing
  imports Complex_Main "HOL-Analysis.Infinite_Set_Sum"
    "HOL-ex.Sketch_and_Explore" HOL.Groups

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

lemma swap_set_fst:
  \<open>fst ` (prod.swap ` S) = snd ` S\<close>
  unfolding prod.swap_def apply auto
   apply (simp add: rev_image_eqI)
  by (metis (no_types, lifting) fst_conv image_cong image_eqI pair_in_swap_image prod.swap_def)

lemma swap_set_snd:
  \<open>snd ` (prod.swap ` S) = fst ` S\<close>
  unfolding prod.swap_def apply auto
   apply (simp add: rev_image_eqI)
  using image_iff by fastforce


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

fun iteration::\<open>nat \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a\<close> where
  \<open>iteration 0 c f = c\<close> |
  \<open>iteration (Suc n) c  f = f (iteration n c f)\<close>

lemma decreasing_sequence_nat:
  fixes f :: \<open>nat \<Rightarrow> nat\<close>
  assumes \<open>\<And> n. f (Suc n) < f n\<close>
  shows False
proof-
  have \<open>f n \<le> f 0 - n\<close>
    for n
  proof(induction n)
    case 0
    thus ?case
      by simp 
  next
    case (Suc n)
    thus ?case
      by (metis (no_types, lifting) Suc_diff_le assms diff_Suc_Suc diff_is_0_eq leD le_less_trans nat_le_linear not_less_eq_eq) 
  qed
  hence \<open>f (f 0) \<le> 0\<close>
    by (metis diff_self_eq_0)
  moreover have \<open>f (Suc (f 0)) < f (f 0)\<close>
    by (simp add: assms)
  ultimately have \<open>f (Suc (f 0)) < 0\<close>
    by simp
  thus ?thesis by blast
qed

lemma pigeonhole_pair:
  assumes \<open>card (fst ` S) < card (snd ` S)\<close> and \<open>finite S\<close>
  shows \<open>\<exists> u v w. (u, v) \<in> S \<and> (u, w) \<in> S \<and> v \<noteq> w\<close>
proof-
  have \<open>\<forall>v. \<exists>u.  v\<in>snd ` S \<longrightarrow> u\<in>fst ` S \<and> (u,v) \<in> S\<close>
    using image_iff by fastforce
  hence \<open>\<exists>f. \<forall>v.  v\<in>snd ` S \<longrightarrow> f v\<in>fst ` S \<and> (f v,v) \<in> S\<close>
    by metis
  then obtain f where \<open>\<forall>v.  v\<in>snd ` S \<longrightarrow> f v\<in>fst ` S \<and> (f v,v) \<in> S\<close>
    by blast
  hence \<open>\<forall>v.  v\<in>snd ` S \<longrightarrow> f v\<in>fst ` S\<close>
    by blast
  hence \<open>(f ` (snd ` S)) \<subseteq> (fst ` S)\<close>
    by blast
  hence \<open>card (f ` (snd ` S)) \<le> card (fst ` S)\<close>
    by (simp add: assms(2) card_mono)
  hence \<open>card (f ` (snd ` S)) < card (snd ` S)\<close>
    using assms(1) dual_order.strict_trans2 by blast
  hence \<open>\<not>(inj_on f (snd ` S))\<close>
    using pigeonhole
    by blast
  hence \<open>\<exists> v \<in> (snd ` S). \<exists> w \<in> (snd ` S). f v = f w \<and> v \<noteq> w\<close>
    unfolding inj_on_def by blast
  then obtain v w where \<open>v \<in> (snd ` S)\<close> and \<open>w \<in> (snd ` S)\<close>
    and \<open>f v = f w\<close> and \<open>v \<noteq> w\<close>
    by blast
  have \<open>f v\<in>fst ` S\<close> and \<open>(f v,v) \<in> S\<close>
     apply (simp add: \<open>\<forall>v. v \<in> snd ` S \<longrightarrow> f v \<in> fst ` S\<close> \<open>v \<in> snd ` S\<close>)
    by (simp add: \<open>\<forall>v. v \<in> snd ` S \<longrightarrow> f v \<in> fst ` S \<and> (f v, v) \<in> S\<close> \<open>v \<in> snd ` S\<close>)
  have \<open>f w\<in>fst ` S\<close> and \<open>(f w,w) \<in> S\<close>
    using \<open>f v = f w\<close> \<open>f v \<in> fst ` S\<close> apply auto[1]
    using \<open>\<forall>v. v \<in> snd ` S \<longrightarrow> f v \<in> fst ` S \<and> (f v, v) \<in> S\<close> \<open>w \<in> snd ` S\<close> by blast
  show ?thesis 
    using \<open>(f v,v) \<in> S\<close>  \<open>(f w,w) \<in> S\<close>  \<open>f v = f w\<close> \<open>v \<noteq> w\<close>
    by auto    
qed

lemma additive_imples_zero:
\<open>(\<And> p q. f (p + q) = f p + f q) \<Longrightarrow> f  (0::'a::ab_group_add) = (0::'b::ab_group_add)\<close>
proof-
  assume \<open>\<And> p q. f (p + q) = f p + f q\<close>
  hence \<open>f (0 + 0) = f 0 + f 0\<close>
    by blast
  moreover have \<open>f 0 = f (0 + 0)\<close>
  proof-
    have \<open>(0::'a::ab_group_add) = 0 + 0\<close>
      by simp
    thus ?thesis by simp
  qed
  ultimately show ?thesis
    by (metis add_cancel_left_left) 
qed

lemma general_sum_from_addition_induction:
  fixes f :: \<open>'a::ab_group_add \<Rightarrow> 'b::ab_group_add\<close>
  assumes \<open>\<And> p q. f (p + q) = f p + f q\<close>
  shows \<open>\<forall> S. card S = n \<and> finite S \<longrightarrow> f (\<Sum>a\<in>S.  a) = (\<Sum>a\<in>S. f a)\<close>
proof (induction n)
  show "\<forall>S. card S = 0 \<and> finite S \<longrightarrow> f (\<Sum> S) = sum f S"
  proof-
    have \<open>card S = 0 \<Longrightarrow> finite S \<Longrightarrow> f (\<Sum> S) = sum f S\<close>
      for S
    proof-
      assume \<open>card S = 0\<close> and \<open>finite S\<close>
      have \<open>S = {}\<close>
        using \<open>card S = 0\<close> \<open>finite S\<close> by auto 
      have \<open>sum f S = 0\<close>
        by (simp add: \<open>S = {}\<close>)
      moreover have \<open>f (\<Sum> S) = 0\<close>
      proof-
        have \<open>\<Sum> S = 0\<close>
          by (simp add: \<open>S = {}\<close>)
        moreover have \<open>f 0 = 0\<close>
          using  \<open>\<And> p q. f (p + q) = f p + f q\<close> additive_imples_zero
          by blast
        ultimately show ?thesis by auto
      qed
      ultimately show \<open>f (\<Sum> S) = sum f S\<close>
        by auto
    qed
    thus ?thesis by blast
  qed
  show "\<forall>S. card S = Suc n \<and> finite S \<longrightarrow> f (\<Sum> S) = sum f S"
    if "\<forall>S. card S = n \<and> finite S \<longrightarrow> f (\<Sum> S) = sum f S"
    for n :: nat
    using that
    by (smt assms card_eq_SucD finite_insert sum.insert) 
qed

lemma general_sum_from_addition:
  fixes f :: \<open>'a::ab_group_add \<Rightarrow> 'b::ab_group_add\<close>
  assumes \<open>\<And> p q. f (p + q) = f p + f q\<close>
    and \<open>finite S\<close>
  shows \<open>f (\<Sum>a\<in>S.  a) = (\<Sum>a\<in>S. f a)\<close>
  using general_sum_from_addition_induction
   assms(1) assms(2) by blast

end

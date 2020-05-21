
(*  
Even if these theorems were never used, they may be useful contributions for 
Isabelle in general.
 *)

theory Never_Used
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
          using  \<open>\<And> p q. f (p + q) = f p + f q\<close>
          by (metis eq_add_iff) 

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



end
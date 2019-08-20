(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)

theory Completion
  imports 
    Complex_Inner_Product NSA_Miscellany

begin


definition Vanishes:: \<open>(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> bool\<close> where
  \<open>Vanishes x = (x \<longlonglongrightarrow> 0)\<close>

definition normed_space_rel :: "(nat \<Rightarrow> 'a::real_normed_vector) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> bool"
  where "normed_space_rel = (\<lambda>X Y. Cauchy X \<and> Cauchy Y \<and> Vanishes (\<lambda>n. X n - Y n))"

quotient_type  (overloaded) 'a completion = "nat \<Rightarrow> 'a::real_normed_vector" / partial: normed_space_rel
  unfolding part_equivp_def
proof
  show "\<exists>x. normed_space_rel (x::nat \<Rightarrow> 'a) x"
    unfolding normed_space_rel_def proof
    show "Cauchy (\<lambda> _. 0::'a) \<and> Cauchy (\<lambda> _. 0::'a) \<and> Vanishes (\<lambda>n. (\<lambda> _. 0::'a) n - (\<lambda> _. 0::'a) n)"
      apply auto
      unfolding Cauchy_def
       apply auto
      unfolding Vanishes_def
      by auto
  qed
  show "\<forall>x y. normed_space_rel (x::nat \<Rightarrow> 'a) y = (normed_space_rel x x \<and> normed_space_rel y y \<and> normed_space_rel x = normed_space_rel y)"
    apply auto
    unfolding normed_space_rel_def
  proof auto
    show \<open>Cauchy x \<Longrightarrow> Cauchy y \<Longrightarrow> Vanishes (\<lambda>n. x n - y n) \<Longrightarrow> Vanishes (\<lambda>n. 0)\<close>
      for x y :: \<open>nat \<Rightarrow> 'a\<close>
    proof-
      assume \<open>Cauchy x\<close> and \<open>Cauchy y\<close> and \<open>Vanishes (\<lambda>n. x n - y n)\<close>
      show \<open>Vanishes (\<lambda>n. 0)\<close>
        unfolding Vanishes_def
        by simp
    qed
    show \<open>Cauchy x \<Longrightarrow> Cauchy y \<Longrightarrow> Vanishes (\<lambda>n. x n - y n) \<Longrightarrow> Vanishes (\<lambda>n. 0)\<close>
      for x y :: \<open>nat \<Rightarrow> 'a\<close>
    proof-
      assume \<open>Cauchy x\<close> and \<open>Cauchy y\<close> and \<open>Vanishes (\<lambda>n. x n - y n)\<close>
      show \<open>Vanishes (\<lambda>n. 0)\<close>
        unfolding Vanishes_def
        by simp
    qed
    show \<open> Cauchy x \<Longrightarrow>
           Cauchy y \<Longrightarrow>
           Vanishes (\<lambda>n. x n - y n) \<Longrightarrow>
           (\<lambda>Y. Cauchy Y \<and> Vanishes (\<lambda>n. x n - Y n)) =
           (\<lambda>Y. Cauchy Y \<and> Vanishes (\<lambda>n. y n - Y n))\<close>
      for x y :: \<open>nat \<Rightarrow> 'a\<close>
    proof
      show "(Cauchy z \<and> Vanishes (\<lambda>n. x n - z n)) = (Cauchy z \<and> Vanishes (\<lambda>n. y n - z n))"
        if "Cauchy x"
          and "Cauchy y"
          and "Vanishes (\<lambda>n. x n - y n)"
        for z :: "nat \<Rightarrow> 'a"
        using that proof auto
        show "Vanishes (\<lambda>n. y n - z n)"
          if "Cauchy x"
            and "Cauchy y"
            and "Vanishes (\<lambda>n. x n - y n)"
            and "Cauchy z"
            and "Vanishes (\<lambda>n. x n - z n)"
        proof-
          have \<open>(\<lambda>n. x n - y n) \<longlonglongrightarrow> 0\<close>
            using Vanishes_def that(3) by auto
          moreover have \<open>(\<lambda>n. x n - z n) \<longlonglongrightarrow> 0\<close>
            using Vanishes_def that(5) by auto
          ultimately have \<open>(\<lambda> m. (\<lambda>n. x n - z n) m - (\<lambda>n. x n - y n) m ) \<longlonglongrightarrow> 0\<close>
            using tendsto_diff by force
          hence \<open>(\<lambda>n. y n - z n) \<longlonglongrightarrow> 0\<close>
            by simp
          thus ?thesis unfolding Vanishes_def by blast
        qed
        show "Vanishes (\<lambda>n. x n - z n)"
          if "Cauchy x"
            and "Cauchy y"
            and "Vanishes (\<lambda>n. x n - y n)"
            and "Cauchy z"
            and "Vanishes (\<lambda>n. y n - z n)"
        proof-
          have \<open>(\<lambda>n. x n - y n) \<longlonglongrightarrow> 0\<close>
            using Vanishes_def that(3) by auto
          moreover have \<open>(\<lambda>n. y n - z n) \<longlonglongrightarrow> 0\<close>
            using Vanishes_def that(5) by auto
          ultimately have \<open>(\<lambda> m. (\<lambda>n. x n - y n) m + (\<lambda>n. y n - z n) m ) \<longlonglongrightarrow> 0\<close>
            using tendsto_add by force
          hence \<open>(\<lambda>n. x n - z n) \<longlonglongrightarrow> 0\<close>
            by simp
          thus ?thesis unfolding Vanishes_def by blast
        qed
      qed
    qed
  qed
qed

instantiation completion :: (real_normed_vector) real_normed_vector
begin
lift_definition uminus_completion :: \<open>'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> x. (\<lambda> n. - (x n))\<close>
  unfolding normed_space_rel_def proof
  show "Cauchy (\<lambda>n. - (f n::'a))"
    if "Cauchy f \<and> Cauchy g \<and> Vanishes (\<lambda>n. (f n::'a) - g n)"
    for f :: "nat \<Rightarrow> 'a"
      and g :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f\<close>
      using that
      by blast
    thus ?thesis unfolding Cauchy_def
      by (simp add: dist_minus)
  qed
  show "Cauchy (\<lambda>n. - (g n::'a)) \<and> Vanishes (\<lambda>n. - f n - - g n)"
    if "Cauchy f \<and> Cauchy g \<and> Vanishes (\<lambda>n. (f n::'a) - g n)"
    for f :: "nat \<Rightarrow> 'a"
      and g :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. - (g n))\<close>
    proof-
      have \<open>Cauchy g\<close>
        using that by blast
      thus ?thesis unfolding Cauchy_def by (simp add: dist_minus)
    qed
    moreover have \<open>Vanishes (\<lambda>n. - f n - - g n)\<close>
    proof-
      have \<open>Vanishes (\<lambda>n. (f n) - (g n))\<close>
        using that by blast
      hence \<open>Vanishes (\<lambda>n. - ((f n) - (g n)))\<close>
        unfolding Vanishes_def
        using tendsto_minus_cancel_left by fastforce
      thus ?thesis by simp
    qed
    ultimately show ?thesis by blast
  qed
qed

lift_definition zero_completion :: \<open>'a completion\<close>
  is \<open>\<lambda> n. 0\<close>
  unfolding normed_space_rel_def
  apply auto
   apply (simp add: convergent_Cauchy convergent_const)
  unfolding Vanishes_def by simp

lift_definition minus_completion :: \<open>'a completion \<Rightarrow> 'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> x y. (\<lambda> n. x n - y n)\<close>
  unfolding normed_space_rel_def
proof
  show "Cauchy (\<lambda>n. (f1 n::'a) - f3 n)"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
      and "Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. (f3 n::'a) - f4 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
      and f3 :: "nat \<Rightarrow> 'a"
      and f4 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f1\<close>
      by (simp add: that(1))
    moreover have \<open>Cauchy f3\<close>
      by (simp add: that(2))
    ultimately show ?thesis 
      using Cauchy_minus by blast
  qed
  show "Cauchy (\<lambda>n. (f2 n::'a) - f4 n) \<and> Vanishes (\<lambda>n. f1 n - f3 n - (f2 n - f4 n))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
      and "Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. (f3 n::'a) - f4 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
      and f3 :: "nat \<Rightarrow> 'a"
      and f4 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. (f2 n) - (f4 n))\<close>
    proof-
      have \<open>Cauchy f2\<close>
        by (simp add: that(1))
      moreover have \<open>Cauchy f4\<close>
        by (simp add: that(2))
      ultimately show ?thesis using Cauchy_minus by blast
    qed
    moreover have \<open>Vanishes (\<lambda>n. f1 n - f3 n - (f2 n - f4 n))\<close>
    proof-
      have \<open>Vanishes (\<lambda>n. (f1 n) - (f2 n))\<close>
        by (simp add: that(1))        
      moreover have \<open>Vanishes (\<lambda>n. (f3 n) - (f4 n))\<close>
        by (simp add: that(2))        
      ultimately have \<open>Vanishes (\<lambda>n. ((f1 n) - (f2 n)) -  ((f3 n) - (f4 n)) )\<close>
        unfolding Vanishes_def
        using tendsto_diff by fastforce
      moreover have \<open>((f1 n) - (f2 n)) -  ((f3 n) - (f4 n)) = f1 n - f3 n - (f2 n - f4 n)\<close>
        for n
        by simp
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by blast
  qed
qed

lift_definition plus_completion :: \<open>'a completion \<Rightarrow> 'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> x y. (\<lambda> n. x n + y n)\<close>
  unfolding normed_space_rel_def
proof
  show "Cauchy (\<lambda>n. (f1 n::'a) + f3 n)"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
      and "Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. (f3 n::'a) - f4 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
      and f3 :: "nat \<Rightarrow> 'a"
      and f4 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f1\<close>
      by (simp add: that(1))      
    moreover have \<open>Cauchy f3\<close>
      by (simp add: that(2))      
    ultimately show ?thesis using Cauchy_add by blast
  qed
  show "Cauchy (\<lambda>n. (f2 n::'a) + f4 n) \<and> Vanishes (\<lambda>n. f1 n + f3 n - (f2 n + f4 n))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
      and "Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. (f3 n::'a) - f4 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
      and f3 :: "nat \<Rightarrow> 'a"
      and f4 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. (f2 n) + (f4 n))\<close>
    proof-
      have \<open>Cauchy f2\<close>
        by (simp add: that(1))        
      moreover have \<open>Cauchy f4\<close>
        by (simp add: that(2))        
      ultimately show ?thesis using Cauchy_add by blast
    qed
    moreover have \<open>Vanishes (\<lambda>n. f1 n + f3 n - (f2 n + f4 n))\<close>
    proof-
      have \<open>Vanishes (\<lambda>n. (f1 n) - (f2 n))\<close>
        by (simp add: that(1))        
      moreover have \<open>Vanishes (\<lambda>n. (f3 n) - (f4 n))\<close>
        by (simp add: that(2))        
      ultimately have \<open>Vanishes (\<lambda>n. ((f1 n) - (f2 n)) + ((f3 n) - (f4 n)))\<close>
        unfolding Vanishes_def
        by (simp add: tendsto_add_zero)
      moreover have \<open>((f1 n) - (f2 n)) + ((f3 n) - (f4 n)) =  f1 n + f3 n - (f2 n + f4 n)\<close>
        for n
        by simp
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by blast
  qed
qed

lift_definition  norm_completion :: \<open>'a completion \<Rightarrow> real\<close>
  is \<open>\<lambda> x. lim (\<lambda> n. norm (x n))\<close>
  unfolding normed_space_rel_def
proof-
  fix f1 f2 :: \<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assume \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close>
  have \<open>Cauchy f1\<close> and \<open>Cauchy f2\<close> and \<open>Vanishes (\<lambda>n. f1 n - f2 n)\<close>
      apply (simp add: \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close>)
     apply (simp add: \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close>)
    by (simp add: \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close>)
  have \<open>Cauchy (\<lambda>n. norm (f1 n))\<close>
    using \<open>Cauchy f1\<close>
    by (simp add: Cauchy_convergent_norm)
  hence \<open>convergent (\<lambda>n. norm (f1 n))\<close>
    by (simp add: real_Cauchy_convergent)
  have \<open>Cauchy (\<lambda>n. norm (f2 n))\<close>
    using \<open>Cauchy f2\<close>
    by (simp add: Cauchy_convergent_norm)
  hence \<open>convergent (\<lambda>n. norm (f2 n))\<close>
    by (simp add: real_Cauchy_convergent)

  have \<open>(\<lambda>n. f1 n - f2 n) \<longlonglongrightarrow> 0\<close>
    using \<open>Vanishes (\<lambda>n. f1 n - f2 n)\<close>
    unfolding Vanishes_def by blast
  hence \<open>(\<lambda>n. f1 n - f2 n) \<longlonglongrightarrow>\<^sub>N\<^sub>S 0\<close>
    by (simp add: LIMSEQ_NSLIMSEQ)
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* f1) N - (*f* f2) N \<approx> 0\<close>
    for N
    using NSLIMSEQ_D by fastforce
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* f1) N \<approx> (*f* f2) N\<close>
    for N
    using approx_minus_iff by auto
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> hnorm ((*f* f1) N) \<approx> hnorm ((*f* f2) N)\<close>
    for N
    by (simp add: approx_hnorm)
  moreover have \<open>N \<in> HNatInfinite \<Longrightarrow> hnorm ((*f* f1) N) \<approx> star_of (lim (\<lambda>n. norm (f1 n)))\<close>
    for N
  proof-
    assume \<open>N \<in> HNatInfinite\<close>
    have \<open>(\<lambda>n. norm (f1 n)) \<longlonglongrightarrow> (lim (\<lambda>n. norm (f1 n)))\<close>
      using \<open>convergent (\<lambda>n. norm (f1 n))\<close> convergent_LIMSEQ_iff by auto
    hence \<open>(\<lambda>n. norm (f1 n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S (lim (\<lambda>n. norm (f1 n)))\<close>
      by (simp add: LIMSEQ_NSLIMSEQ)
    hence \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* (\<lambda>n. norm (f1 n))) N \<approx> star_of (lim (\<lambda>n. norm (f1 n)))\<close>
      for N
      by (simp add: NSLIMSEQ_D)
    moreover have \<open>hnorm ((*f* f1) N) = (*f* (\<lambda>n. norm (f1 n))) N\<close>
      for N
      by (simp add: starfun_hnorm)
    ultimately show  ?thesis
      by (simp add: \<open>N \<in> HNatInfinite\<close>) 
  qed
  moreover have \<open>N \<in> HNatInfinite \<Longrightarrow> hnorm ((*f* f2) N) \<approx> star_of (lim (\<lambda>n. norm (f2 n)))\<close>
    for N
  proof-
    assume \<open>N \<in> HNatInfinite\<close>
    have \<open>(\<lambda>n. norm (f2 n)) \<longlonglongrightarrow> (lim (\<lambda>n. norm (f2 n)))\<close>
      using \<open>convergent (\<lambda>n. norm (f2 n))\<close> convergent_LIMSEQ_iff by auto
    hence \<open>(\<lambda>n. norm (f2 n)) \<longlonglongrightarrow>\<^sub>N\<^sub>S (lim (\<lambda>n. norm (f2 n)))\<close>
      by (simp add: LIMSEQ_NSLIMSEQ)
    hence \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* (\<lambda>n. norm (f2 n))) N \<approx> star_of (lim (\<lambda>n. norm (f2 n)))\<close>
      for N
      by (simp add: NSLIMSEQ_D)
    moreover have \<open>hnorm ((*f* f2) N) = (*f* (\<lambda>n. norm (f2 n))) N\<close>
      for N
      by (simp add: starfun_hnorm)
    ultimately show  ?thesis
      by (simp add: \<open>N \<in> HNatInfinite\<close>) 
  qed    
  ultimately have \<open>star_of (lim (\<lambda>n. norm (f1 n))) \<approx> star_of (lim (\<lambda>n. norm (f2 n)))\<close>
  proof-
    assume a1: "\<And>N. N \<in> HNatInfinite \<Longrightarrow> hnorm ((*f* f1) N) \<approx> hnorm ((*f* f2) N)"
    assume a2: "\<And>N. N \<in> HNatInfinite \<Longrightarrow> hnorm ((*f* f1) N) \<approx> hypreal_of_real (lim (\<lambda>n. norm (f1 n)))"
    assume a3: "\<And>N. N \<in> HNatInfinite \<Longrightarrow> hnorm ((*f* f2) N) \<approx> hypreal_of_real (lim (\<lambda>n. norm (f2 n)))"
    have "(\<exists>f r. lim f \<noteq> (r::real)) \<or> hypreal_of_real (lim (\<lambda>n. norm (f1 n))) \<approx> hypreal_of_real (lim (\<lambda>n. norm (f2 n)))"
      by fastforce
    then show ?thesis
      using a3 a2 a1 by (meson NSLIMSEQ_LIMSEQ NSLIMSEQ_def approx_trans3 limI)
  qed 
  thus \<open>lim (\<lambda>n. norm (f1 n)) = lim (\<lambda>n. norm (f2 n))\<close>
    by simp
qed

lift_definition sgn_completion :: \<open>'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> x. (\<lambda> n. (x n) /\<^sub>R lim (\<lambda> n. norm (x n)) )\<close>
  unfolding normed_space_rel_def proof
  show "Cauchy (\<lambda>n. (f1 n::'a) /\<^sub>R lim (\<lambda>n. norm (f1 n)))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f1\<close>
      by (simp add: that)
    thus ?thesis
      using Cauchy_sgn by blast
  qed
  show "Cauchy (\<lambda>n. (f2 n::'a) /\<^sub>R lim (\<lambda>n. norm (f2 n))) \<and> 
      Vanishes (\<lambda>n. f1 n /\<^sub>R lim (\<lambda>n. norm (f1 n)) - f2 n /\<^sub>R lim (\<lambda>n. norm (f2 n)))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
    for f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. (f2 n) /\<^sub>R lim (\<lambda>n. norm (f2 n)))\<close>
    proof-
      have \<open>Cauchy f2\<close>
        by (simp add: that)
      thus ?thesis using Cauchy_sgn by blast
    qed
    moreover have \<open>Vanishes (\<lambda>n. f1 n /\<^sub>R lim (\<lambda>n. norm (f1 n)) - f2 n /\<^sub>R lim (\<lambda>n. norm (f2 n)))\<close>
    proof-
      have \<open>Cauchy f1\<close>
        by (simp add: that)
      have \<open>Cauchy f2\<close>
        by (simp add: that)

      have \<open>Vanishes (\<lambda>n. (f1 n) - (f2 n))\<close>
        by (simp add: that)
      hence \<open>lim (\<lambda>n. norm (f1 n)) = lim (\<lambda>n. norm (f2 n))\<close>
        using \<open>Cauchy f1\<close> \<open>Cauchy f2\<close> norm_completion_def
        by (metis (full_types) Quotient3_completion Quotient3_def norm_completion.abs_eq normed_space_rel_def)
      define L where \<open>L = lim (\<lambda>n. norm (f1 n))\<close>
      have \<open>Vanishes (\<lambda>n. (f1 n - f2 n) /\<^sub>R L)\<close>
      proof-
        have \<open>(\<lambda>n. (f1 n - f2 n)) \<longlonglongrightarrow> 0\<close>
          using \<open>Vanishes (\<lambda>n. (f1 n - f2 n))\<close>
          unfolding Vanishes_def by blast
        moreover have \<open>(\<lambda>n. (inverse L)) \<longlonglongrightarrow> (inverse L)\<close>
          by simp            
        ultimately have \<open>(\<lambda>n. (inverse L) *\<^sub>R (f1 n - f2 n)) \<longlonglongrightarrow> (inverse L) *\<^sub>R 0\<close>
          using Limits.tendsto_scaleR by blast
        thus ?thesis
          unfolding Vanishes_def by simp
      qed
      moreover have \<open>(f1 n - f2 n) /\<^sub>R L =  f1 n /\<^sub>R L - f2 n /\<^sub>R L\<close>
        for n
        by (simp add: scale_right_diff_distrib)        
      ultimately have \<open>Vanishes (\<lambda>n. f1 n /\<^sub>R L - f2 n /\<^sub>R L)\<close>
        by simp
      thus ?thesis unfolding L_def using \<open>lim (\<lambda>n. norm (f1 n)) = lim (\<lambda>n. norm (f2 n))\<close>
        by simp
    qed
    ultimately show ?thesis by blast
  qed
qed

lift_definition scaleR_completion :: \<open>real \<Rightarrow> 'a completion \<Rightarrow> 'a completion\<close>
  is \<open>\<lambda> r x. (\<lambda> n. r *\<^sub>R (x n))\<close>
  unfolding normed_space_rel_def proof
  show "Cauchy (\<lambda>n. r *\<^sub>R (f1 n::'a))"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
    for r :: real
      and f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy f1\<close>
      using that by blast
    thus ?thesis using Cauchy_scaleR by blast
  qed
  show "Cauchy (\<lambda>n. r *\<^sub>R (f2 n::'a)) \<and> Vanishes (\<lambda>n. r *\<^sub>R f1 n - r *\<^sub>R f2 n)"
    if "Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. (f1 n::'a) - f2 n)"
    for r :: real
      and f1 :: "nat \<Rightarrow> 'a"
      and f2 :: "nat \<Rightarrow> 'a"
  proof-
    have \<open>Cauchy (\<lambda>n. r *\<^sub>R (f2 n))\<close>
    proof-
      have \<open>Cauchy f2\<close>
        using that by blast
      thus ?thesis using Cauchy_scaleR by blast
    qed
    moreover have \<open>Vanishes (\<lambda>n. r *\<^sub>R f1 n - r *\<^sub>R f2 n)\<close>
    proof-
      have \<open>Vanishes (\<lambda>n. (f1 n) - (f2 n))\<close>
        using that by blast
      hence \<open>(\<lambda>n. (f1 n) - (f2 n)) \<longlonglongrightarrow> 0\<close>
        unfolding Vanishes_def by blast
      moreover have \<open>(\<lambda>n. r) \<longlonglongrightarrow> r\<close>
        by simp
      ultimately have \<open>(\<lambda>n. r *\<^sub>R (f1 n - f2 n)) \<longlonglongrightarrow> r *\<^sub>R 0\<close>
        using Limits.tendsto_scaleR by blast
      moreover have \<open>r *\<^sub>R (f1 n - f2 n) = r *\<^sub>R f1 n - r *\<^sub>R f2 n\<close>
        for n
        by (simp add: scale_right_diff_distrib)        
      ultimately show ?thesis unfolding Vanishes_def
        by auto 
    qed
    ultimately show ?thesis by blast
  qed
qed     

lift_definition dist_completion :: \<open>'a completion \<Rightarrow> 'a completion \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. lim (\<lambda> n. norm (f n - g n))\<close>
  unfolding normed_space_rel_def
proof-
  fix f1 f2 f3 f4 :: \<open>nat \<Rightarrow> 'a\<close>
  assume \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close> and
    \<open>Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. f3 n - f4 n)\<close> 
  have \<open>Cauchy f1\<close> and \<open>Cauchy f2\<close> and \<open>Vanishes (\<lambda>n. f1 n - f2 n)\<close>
    using \<open>Cauchy f1 \<and> Cauchy f2 \<and> Vanishes (\<lambda>n. f1 n - f2 n)\<close>
    by auto 
  have \<open>Cauchy f3\<close> and \<open>Cauchy f4\<close> and \<open>Vanishes (\<lambda>n. f3 n - f4 n)\<close>
    using \<open>Cauchy f3 \<and> Cauchy f4 \<and> Vanishes (\<lambda>n. f3 n - f4 n)\<close>
    by auto
  have \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* (\<lambda>n. norm (f1 n - f3 n))) N \<approx> star_of (lim (\<lambda>n. norm (f1 n - f3 n)))\<close>
    for N
  proof-
    assume \<open>N \<in> HNatInfinite\<close>
    have \<open>Cauchy (\<lambda>n. (f1 n - f3 n))\<close>
      using \<open>Cauchy f1\<close> \<open>Cauchy f3\<close>
      by (simp add: Cauchy_minus)
    hence \<open>Cauchy (\<lambda>n. norm (f1 n - f3 n))\<close>
      using Cauchy_convergent_norm by auto
    hence \<open>convergent (\<lambda>n. norm (f1 n - f3 n))\<close>
      by (simp add: real_Cauchy_convergent)
    hence \<open>NSconvergent (\<lambda>n. norm (f1 n - f3 n))\<close>
      using convergent_NSconvergent_iff by auto
    thus ?thesis
      using \<open>N \<in> HNatInfinite\<close>
      by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff lim_nslim_iff)
  qed
  moreover have \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* (\<lambda>n. norm (f2 n - f4 n))) N \<approx> star_of (lim (\<lambda>n. norm (f2 n - f4 n)))\<close>
    for N
  proof-
    assume \<open>N \<in> HNatInfinite\<close>
    have \<open>Cauchy (\<lambda>n. (f2 n - f4 n))\<close>
      using \<open>Cauchy f2\<close> \<open>Cauchy f4\<close>
      by (simp add: Cauchy_minus)
    hence \<open>Cauchy (\<lambda>n. norm (f2 n - f4 n))\<close>
      using Cauchy_convergent_norm by auto
    hence \<open>convergent (\<lambda>n. norm (f2 n - f4 n))\<close>
      by (simp add: real_Cauchy_convergent)
    hence \<open>NSconvergent (\<lambda>n. norm (f2 n - f4 n))\<close>
      using convergent_NSconvergent_iff by auto
    thus ?thesis
      using \<open>N \<in> HNatInfinite\<close>
      by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff lim_nslim_iff)
  qed
  moreover have \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* (\<lambda>n. norm (f1 n - f3 n))) N \<approx> (*f* (\<lambda>n. norm (f2 n - f4 n))) N\<close>
    for N
  proof-
    assume \<open>N \<in> HNatInfinite\<close>
    from  \<open>Vanishes (\<lambda>n. f1 n - f2 n)\<close> \<open>Vanishes (\<lambda>n. f3 n - f4 n)\<close>
    have  \<open>Vanishes (\<lambda>n. (f1 n - f2 n) - (f3 n - f4 n))\<close>
      unfolding Vanishes_def
      using tendsto_diff by fastforce
    hence  \<open>(\<lambda>n. (f1 n - f2 n) - (f3 n - f4 n))\<longlonglongrightarrow>\<^sub>N\<^sub>S 0\<close>
      unfolding Vanishes_def
      by (simp add: LIMSEQ_NSLIMSEQ_iff)
    moreover have \<open>(f1 n - f2 n) - (f3 n - f4 n) = (f1 n - f3 n) - (f2 n - f4 n)\<close>
      for n
      by simp
    ultimately have \<open>(\<lambda>n. (f1 n - f3 n) - (f2 n - f4 n))\<longlonglongrightarrow>\<^sub>N\<^sub>S 0\<close>
      by simp
    hence \<open>(*f* (\<lambda>n. (f1 n - f3 n) - (f2 n - f4 n))) N \<approx> 0\<close>
      using NSLIMSEQ_D \<open>N \<in> HNatInfinite\<close> by fastforce
    hence \<open>(*f* (\<lambda>n. (f1 n - f3 n))) N - (*f* (\<lambda> n. (f2 n - f4 n))) N \<approx> 0\<close>
      by auto
    hence \<open>(*f* (\<lambda>n. (f1 n - f3 n))) N \<approx> (*f* (\<lambda> n. (f2 n - f4 n))) N\<close>
      using approx_minus_iff by auto
    hence \<open>hnorm ((*f* (\<lambda>n. (f1 n - f3 n))) N) \<approx> hnorm ((*f* (\<lambda> n. (f2 n - f4 n))) N)\<close>
      by (simp add: approx_hnorm)      
    thus \<open>(*f* (\<lambda>n. norm (f1 n - f3 n))) N \<approx> (*f* (\<lambda>n. norm (f2 n - f4 n))) N\<close>
      by (simp add: starfun_norm)      
  qed
  ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow> star_of (lim (\<lambda>n. norm (f1 n - f3 n))) \<approx> star_of (lim (\<lambda>n. norm (f2 n - f4 n)))\<close>
    for N
    by (meson approx_trans3)
  hence \<open>star_of (lim (\<lambda>n. norm (f1 n - f3 n))) \<approx> star_of (lim (\<lambda>n. norm (f2 n - f4 n)))\<close>
    using HNatInfinite_whn by blast  
  thus \<open>lim (\<lambda>n. norm (f1 n - f3 n)) = lim (\<lambda>n. norm (f2 n - f4 n))\<close>
    by simp
qed

definition uniformity_completion :: \<open>('a completion \<times> 'a completion) filter\<close>
  where  \<open>uniformity_completion = (INF e:{0<..}. principal {((f::'a completion), (g::'a completion)). dist f g < e})\<close>

definition open_completion :: \<open>('a completion) set \<Rightarrow> bool\<close>
  where \<open>open_completion = (\<lambda> U::('a completion) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity))\<close>

instance 
proof
  show "dist (x::'a completion) y = norm (x - y)"
    for x :: "'a completion"
      and y :: "'a completion"
    apply transfer
    by simp
  show "(a::'a completion) + b + c = a + (b + c)"
    for a :: "'a completion"
      and b :: "'a completion"
      and c :: "'a completion"
    apply transfer
    unfolding normed_space_rel_def proof
    show "Cauchy (\<lambda>n. (a n::'a) + b n + c n)"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
        and "Cauchy b \<and> Cauchy b \<and> Vanishes (\<lambda>n. (b n::'a) - b n)"
        and "Cauchy c \<and> Cauchy c \<and> Vanishes (\<lambda>n. (c n::'a) - c n)"
      for a :: "nat \<Rightarrow> 'a"
        and b :: "nat \<Rightarrow> 'a"
        and c :: "nat \<Rightarrow> 'a"
      using that Cauchy_add by auto 
    show "Cauchy (\<lambda>n. (a n::'a) + (b n + c n)) \<and> Vanishes (\<lambda>n. a n + b n + c n - (a n + (b n + c n)))"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
        and "Cauchy b \<and> Cauchy b \<and> Vanishes (\<lambda>n. (b n::'a) - b n)"
        and "Cauchy c \<and> Cauchy c \<and> Vanishes (\<lambda>n. (c n::'a) - c n)"
      for a :: "nat \<Rightarrow> 'a"
        and b :: "nat \<Rightarrow> 'a"
        and c :: "nat \<Rightarrow> 'a"
      using that apply auto
      using Cauchy_add by auto
  qed
  show "(a::'a completion) + b = b + a"
    for a :: "'a completion"
      and b :: "'a completion"
    apply transfer unfolding normed_space_rel_def proof
    show "Cauchy (\<lambda>n. (a n::'a) + b n)"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
        and "Cauchy b \<and> Cauchy b \<and> Vanishes (\<lambda>n. (b n::'a) - b n)"
      for a :: "nat \<Rightarrow> 'a"
        and b :: "nat \<Rightarrow> 'a"
      using that
      by (simp add: Cauchy_add) 
    show "Cauchy (\<lambda>n. (b n::'a) + a n) \<and> Vanishes (\<lambda>n. a n + b n - (b n + a n))"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
        and "Cauchy b \<and> Cauchy b \<and> Vanishes (\<lambda>n. (b n::'a) - b n)"
      for a :: "nat \<Rightarrow> 'a"
        and b :: "nat \<Rightarrow> 'a"
      using that apply auto
      by (simp add: Cauchy_add)
  qed
  show "(0::'a completion) + a = a"
    for a :: "'a completion"
    apply transfer unfolding normed_space_rel_def proof
    show "Cauchy (\<lambda>n. (0::'a) + a n)"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
      for a :: "nat \<Rightarrow> 'a"
      using that by auto
    show "Cauchy a \<and> Vanishes (\<lambda>n. (0::'a) + a n - a n)"
      if "Cauchy a \<and> Cauchy a \<and> Vanishes (\<lambda>n. (a n::'a) - a n)"
      for a :: "nat \<Rightarrow> 'a"
      using that by auto
  qed
  show "- (a::'a completion) + a = 0"
    for a :: "'a completion"
    apply transfer apply auto
    by (simp add: Completion.zero_completion.rsp) 
  show "(a::'a completion) - b = a + - b"
    for a :: "'a completion"
      and b :: "'a completion"
    apply transfer apply auto unfolding normed_space_rel_def apply auto
    by (simp add: Cauchy_minus)

  show "a *\<^sub>R ((x::'a completion) + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real
      and x :: "'a completion"
      and y :: "'a completion"
    apply transfer unfolding normed_space_rel_def apply auto
      apply (simp add: Cauchy_add Cauchy_scaleR)
     apply (simp add: Cauchy_add Cauchy_scaleR)
    unfolding Vanishes_def apply auto proof
    show "\<forall>\<^sub>F n in sequentially. dist (a *\<^sub>R (x n + y n) - (a *\<^sub>R x n + a *\<^sub>R y n)) (0::'a) < e"
      if "Cauchy (y::nat \<Rightarrow> 'a)"
        and "Cauchy (x::nat \<Rightarrow> 'a)"
        and "(0::real) < e"
      for a :: real
        and x :: "nat \<Rightarrow> 'a"
        and y :: "nat \<Rightarrow> 'a"
        and e :: real
    proof-
      have \<open>a *\<^sub>R (x n + y n) = (a *\<^sub>R x n + a *\<^sub>R y n)\<close>
        for n
        by (simp add: pth_6)
      have \<open>a *\<^sub>R (x n + y n) - (a *\<^sub>R x n + a *\<^sub>R y n) = 0\<close>
        for n
        by (simp add: \<open>\<And>n. a *\<^sub>R (x n + y n) = a *\<^sub>R x n + a *\<^sub>R y n\<close>)
      hence \<open>dist (a *\<^sub>R (x n + y n) - (a *\<^sub>R x n + a *\<^sub>R y n)) (0::'a) = 0\<close>
        for n
        by simp
      thus ?thesis
        by (simp add: that(3)) 
    qed
  qed

  show "(a + b) *\<^sub>R (x::'a completion) = a *\<^sub>R x + b *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a completion"
    apply transfer unfolding normed_space_rel_def apply auto
      apply (simp add: Cauchy_scaleR)
     apply (simp add: Cauchy_add Cauchy_scaleR)
    unfolding Vanishes_def proof
    show "\<forall>\<^sub>F n in sequentially. dist ((a + b) *\<^sub>R x n - (a *\<^sub>R x n + b *\<^sub>R x n)) (0::'a) < e"
      if "Cauchy (x::nat \<Rightarrow> 'a)"
        and "(\<lambda>n. 0::'a) \<longlonglongrightarrow> 0"
        and "(0::real) < e"
      for a :: real
        and b :: real
        and x :: "nat \<Rightarrow> 'a"
        and e :: real
    proof-
      have \<open>(a + b) *\<^sub>R x n = (a *\<^sub>R x n + b *\<^sub>R x n)\<close>
        for n
        by (simp add: scaleR_add_left)
      hence \<open>(a + b) *\<^sub>R x n - (a *\<^sub>R x n + b *\<^sub>R x n) = 0\<close>
        for n
        by simp
      hence \<open>dist ((a + b) *\<^sub>R x n - (a *\<^sub>R x n + b *\<^sub>R x n)) (0::'a) = 0\<close>
        for n
        by simp
      thus ?thesis
        by (simp add: that(3)) 
    qed
  qed

  show "a *\<^sub>R b *\<^sub>R (x::'a completion) = (a * b) *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a completion"
    apply transfer apply auto unfolding normed_space_rel_def apply auto
    by (simp add: Cauchy_scaleR)

  show "1 *\<^sub>R (x::'a completion) = x"
    for x :: "'a completion"
    apply transfer by auto

  show "sgn (x::'a completion) = inverse (norm x) *\<^sub>R x"
    for x :: "'a completion"
    apply transfer unfolding normed_space_rel_def apply auto
    by (simp add: Cauchy_scaleR)

  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a completion) y < e})"
    by (simp add: Completion.uniformity_completion_def)    

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a completion) = x \<longrightarrow> y \<in> U)"
    for U :: "'a completion set"
    by (simp add: Completion.open_completion_def)

  show "(norm (x::'a completion) = 0) = (x = 0)"
    for x :: "'a completion"
    apply transfer apply auto unfolding normed_space_rel_def Vanishes_def apply auto
      apply (metis normed_space_rel_def zero_completion.rsp)
     apply (metis Cauchy_convergent_norm convergent_eq_Cauchy limI tendsto_norm_zero_iff)
    by (simp add: limI tendsto_norm_zero)

  show "norm ((x::'a completion) + y) \<le> norm x + norm y"
    for x :: "'a completion"
      and y :: "'a completion"
    apply transfer unfolding normed_space_rel_def apply auto
  proof-
    fix x y :: \<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy x\<close> and \<open>Cauchy y\<close> and \<open>Vanishes (\<lambda>n. 0)\<close>
    from \<open>Cauchy x\<close>
    have \<open>Cauchy (\<lambda> n. norm (x n))\<close>
      by (simp add: Cauchy_convergent_norm)
    hence \<open>convergent (\<lambda> n. norm (x n))\<close>
      by (simp add: real_Cauchy_convergent)
    from \<open>Cauchy y\<close>
    have \<open>Cauchy (\<lambda> n. norm (y n))\<close>
      by (simp add: Cauchy_convergent_norm)
    hence \<open>convergent (\<lambda> n. norm (y n))\<close>
      by (simp add: real_Cauchy_convergent)
    have \<open>convergent (\<lambda> n. norm (x n) + norm (y n))\<close>
      by (simp add: \<open>convergent (\<lambda>n. norm (x n))\<close> \<open>convergent (\<lambda>n. norm (y n))\<close> convergent_add)
    have \<open>Cauchy (\<lambda> n. (x n + y n))\<close>
      using \<open>Cauchy x\<close> \<open>Cauchy y\<close>  
      by (simp add: Cauchy_add)
    hence \<open>Cauchy (\<lambda> n. norm (x n + y n))\<close>
      by (simp add: Cauchy_convergent_norm)
    hence \<open>convergent (\<lambda> n. norm (x n + y n))\<close>
      by (simp add: Cauchy_convergent)
    have \<open>norm (x n + y n) \<le> norm (x n) + norm (y n)\<close>
      for n
      by (simp add: norm_triangle_ineq)
    hence \<open>lim (\<lambda> n. norm (x n + y n)) \<le> lim (\<lambda> n. norm (x n) + norm (y n))\<close>
      using \<open>convergent (\<lambda> n. norm (x n + y n))\<close> \<open>convergent (\<lambda> n. norm (x n) + norm (y n))\<close> lim_leq
      by auto
    moreover have \<open>lim (\<lambda> n. norm (x n) + norm (y n)) = lim (\<lambda> n. norm (x n)) + lim (\<lambda> n. norm (y n))\<close>
      using \<open>convergent (\<lambda> n. norm (x n))\<close>  \<open>convergent (\<lambda> n. norm (y n))\<close> lim_add
      by blast
    ultimately show  \<open>lim (\<lambda>n. norm (x n + y n))
           \<le> lim (\<lambda>n. norm (x n)) + lim (\<lambda>n. norm (y n))\<close>
      by simp
  qed

  show "norm (a *\<^sub>R (x::'a completion)) = \<bar>a\<bar> * norm x"
    for a :: real
      and x :: "'a completion"
    apply transfer unfolding normed_space_rel_def apply auto
  proof-
    fix a::real and x::\<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy x\<close> and \<open>Vanishes (\<lambda>n. 0)\<close>
    hence \<open>convergent (\<lambda> n. norm (x n))\<close>
      using Cauchy_convergent_iff Cauchy_convergent_norm by blast
    moreover have \<open>norm (a *\<^sub>R x n) = \<bar>a\<bar> * norm (x n)\<close>
      for n
      by simp
    ultimately have \<open>lim (\<lambda>n. norm (a *\<^sub>R x n)) =  lim (\<lambda>n. \<bar>a\<bar> * norm (x n))\<close>
      by simp
    also have \<open>lim (\<lambda>n. \<bar>a\<bar> * norm (x n)) = \<bar>a\<bar> * lim (\<lambda>n. norm (x n))\<close>
      using  \<open>convergent (\<lambda> n. norm (x n))\<close>
      by (simp add: lim_scaleR)       
    finally have  \<open>lim (\<lambda>n. norm (a *\<^sub>R x n)) = \<bar>a\<bar> * lim (\<lambda>n. norm (x n))\<close>
      by blast
    thus \<open>lim (\<lambda>n. \<bar>a\<bar> * norm (x n)) = \<bar>a\<bar> * lim (\<lambda>n. norm (x n))\<close>
      by simp
  qed
qed
end

instantiation completion :: (real_normed_vector) banach
begin
instance
proof
  show "convergent (X::nat \<Rightarrow> 'a completion)"
    if "Cauchy (X::nat \<Rightarrow> 'a completion)"
    for X :: "nat \<Rightarrow> 'a completion"
    using that sorry
qed
end

instantiation completion :: (complex_normed_vector) cbanach
begin
instance 
  sorry
end

instantiation completion :: (complex_inner) chilbert_space
begin
instance 
  sorry
end


end
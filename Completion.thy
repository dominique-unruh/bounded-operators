(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)

theory Completion
  imports 
    Complex_Inner_Product

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




end
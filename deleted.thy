(* NEW *)
lemma uniq_linear_expansion_zero:
  fixes f::"nat \<Rightarrow> complex" 
  defines  "basis == canonical_basis::('a::basis_enum list)"
  assumes h1: "(\<Sum>i = 0 ..< length basis. f i *\<^sub>C (basis!i)) = 0" and 
    h2: "k < length basis"
  shows "f k = 0"
proof-
  define t where "t i = basis!i" for i::nat
  have inj_on_t: "inj_on t {0..<length basis}"
    unfolding basis_def using distinct_canonical_basis
    by (simp add: basis_def inj_on_def nth_eq_iff_index_eq t_def) 
  define s where "s = the_inv_into {0..<length basis} t"
  have inj_on_s: "inj_on s (set basis)"
    by (metis \<open>inj_on t {0..<length basis}\<close> \<open>t \<equiv> (!) basis\<close> atLeastLessThan_iff basis_def 
        distinct_Ex1 distinct_canonical_basis inj_on_inverseI le0 s_def the_inv_into_f_f)
  have "i < length basis \<Longrightarrow> i \<in> the_inv_into {0..<length basis} t ` (set basis)" for i::nat
  proof-
    assume "i < length basis"
    hence w1: "i \<in> {0..<length basis}"
      by auto
    moreover have "t i \<in> set basis"
      unfolding t_def using w1 by simp
    ultimately show "i \<in> the_inv_into {0..<length basis} t ` (set basis)"
      using image_iff inj_on_t the_inv_into_f_eq by fastforce      
  qed
  hence range_s: "s ` (set basis) = {0..<length basis}"
    unfolding s_def apply auto
    by (smt \<open>t \<equiv> (!) basis\<close> atLeastLessThan_iff gr_implies_not_zero in_set_conv_nth inj_on_t 
        nat_int of_nat_le_iff the_inv_into_f_eq zless_nat_eq_int_zless)    
  define F where "F b = f (s b)" for b
  have "(\<Sum>i\<in>{0..<length basis}. f i *\<^sub>C basis ! i) = (\<Sum>b\<in>set basis. F b *\<^sub>C b)"
    unfolding F_def basis_def
    using inj_on_s range_s
      \<open>t \<equiv> (!) basis\<close> atLeastLessThan_iff basis_def image_eqI inj_on_t nth_mem s_def sum.reindex_cong
      the_inv_into_f_eq
  proof -
    obtain aa :: "('a \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> 'a" where
      "\<forall>x0 x1 x3 x4. (\<exists>v5. v5 \<in> x3 \<and> x1 (x4 v5) \<noteq> x0 v5) = (aa x0 x1 x3 x4 \<in> x3 \<and> x1 (x4 (aa x0 x1 x3 x4)) \<noteq> x0 (aa x0 x1 x3 x4))"
      by moura
    then have f1: "\<forall>f A N fa fb. (\<not> inj_on f A \<or> N \<noteq> f ` A \<or> aa fb fa A f \<in> A \<and> fa (f (aa fb fa A f)) \<noteq> fb (aa fb fa A f)) \<or> sum fa N = sum fb A"
      by (meson sum.reindex_cong)
    have f2: "the_inv_into {0..<length basis} t ` set canonical_basis = s ` set basis"
      by (metis basis_def s_def)
    then have f3: "{0..<length basis} = the_inv_into {0..<length basis} t ` set canonical_basis"
      using range_s by presburger
    have f4: "inj_on (the_inv_into {0..<length basis} t) (set canonical_basis)"
      by (metis basis_def inj_on_s s_def)
    have "\<forall>f N n a. (\<not> inj_on f N \<or> f (n::nat) \<noteq> (a::'a) \<or> n \<notin> N) \<or> the_inv_into N f a = n"
      by (meson the_inv_into_f_eq)
    then have f5: "basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<noteq> canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<or> the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<notin> {0..<length basis} \<or> the_inv_into {0..<length basis} ((!) basis) (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) = the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))"
      using \<open>t \<equiv> (!) basis\<close> inj_on_t by blast
    have f6: "\<forall>f A a n. \<not> inj_on f A \<or> f (a::'a) \<noteq> (n::nat) \<or> a \<notin> A \<or> the_inv_into A f n = a"
      by (simp add: the_inv_into_f_eq)
    then have f7: "the_inv_into {0..<length basis} t (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) \<noteq> the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<or> (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))::'a) \<notin> set canonical_basis \<or> the_inv_into (set canonical_basis) (the_inv_into {0..<length basis} t) (the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) = canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))"
      using f4 by meson
    { assume "f (the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) *\<^sub>C canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<noteq> f (s (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) *\<^sub>C aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)"
      then have "aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t) \<noteq> canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<or> f (the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) *\<^sub>C (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))::'a) \<noteq> f (s (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)))) *\<^sub>C canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))"
        by fastforce
      moreover
      { assume "f (the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) *\<^sub>C (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))::'a) \<noteq> f (s (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)))) *\<^sub>C canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))"
        then have "s (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) \<noteq> the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))"
          by fastforce
        then have "the_inv_into {0..<length basis} ((!) basis) (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) \<noteq> the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))"
          using \<open>t \<equiv> (!) basis\<close> s_def by blast }
      moreover
      { assume "aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t) \<noteq> canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))"
        then have "the_inv_into (set canonical_basis) (the_inv_into {0..<length basis} t) (the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) \<noteq> canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<or> the_inv_into (set canonical_basis) (the_inv_into {0..<length basis} t) (the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) \<noteq> aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)"
          by auto
        moreover
        { assume "the_inv_into (set canonical_basis) (the_inv_into {0..<length basis} t) (the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) \<noteq> canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))"
          moreover
          { assume "(canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))::'a) \<notin> set canonical_basis"
            then have "the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<notin> the_inv_into {0..<length basis} t ` set canonical_basis"
              using f2 basis_def range_s by auto }
          ultimately have "the_inv_into {0..<length basis} ((!) basis) (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) \<noteq> the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<or> the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<notin> the_inv_into {0..<length basis} t ` set canonical_basis"
            using f7 \<open>t \<equiv> (!) basis\<close> by blast }
        ultimately have "the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<in> the_inv_into {0..<length basis} t ` set canonical_basis \<and> the_inv_into {0..<length basis} ((!) basis) (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) = the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<longrightarrow> aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t) \<notin> set canonical_basis \<or> f (the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) *\<^sub>C canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) = f (s (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) *\<^sub>C aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)"
          using f6 f4 by blast }
      ultimately have "the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<in> the_inv_into {0..<length basis} t ` set canonical_basis \<and> the_inv_into {0..<length basis} ((!) basis) (canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) = the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) \<longrightarrow> aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t) \<notin> set canonical_basis \<or> f (the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) *\<^sub>C canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) = f (s (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) *\<^sub>C aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)"
        by blast
      then have "aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t) \<notin> set canonical_basis \<or> f (the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) *\<^sub>C canonical_basis ! the_inv_into {0..<length basis} t (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)) = f (s (aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t))) *\<^sub>C aa (\<lambda>a. f (s a) *\<^sub>C a) (\<lambda>n. f n *\<^sub>C canonical_basis ! n) (set canonical_basis) (the_inv_into {0..<length basis} t)"
        using f5 f2 basis_def range_s by blast }
    then have "(\<Sum>n = 0..<length basis. f n *\<^sub>C canonical_basis ! n) = (\<Sum>a\<in>set canonical_basis. f (s a) *\<^sub>C a)"
      using f4 f3 f1 by meson
    then show "(\<Sum>n = 0..<length (canonical_basis::'a list). f n *\<^sub>C canonical_basis ! n) = (\<Sum>a\<in>set canonical_basis. f (s a) *\<^sub>C a)"
      using basis_def by blast
  qed 

  hence "(\<Sum>i = 0 ..< length basis. f i *\<^sub>C (basis!i)) = (\<Sum>b \<in> set basis. F b *\<^sub>C b)"
    by blast    
  hence b2: "(\<Sum>b \<in> set basis. F b *\<^sub>C b) = 0"
    using h1 by auto    
  hence "b \<in> (set basis) \<Longrightarrow> F b = 0" for b
  proof-
    assume b1: "b \<in> (set basis)"
    have "complex_vector.independent (set basis)"
      unfolding basis_def using is_basis_set unfolding is_basis_def by blast
    thus ?thesis using b1 b2 complex_vector.independentD[where s = "set basis" and t = "set basis" 
          and u = F and v = b]
      by (simp add: Complex_Vector_Spaces.dependent_raw_def)
  qed
  hence "F (basis!k) = 0"
    by (simp add: h2)    
  moreover have "s (basis!k) = k"
    using \<open>inj_on t {0..<length basis}\<close> \<open>t \<equiv> (!) basis\<close> atLeastLessThan_iff h2 s_def 
      the_inv_into_f_f by fastforce    
  ultimately show ?thesis unfolding F_def by simp
qed


(* NEW *)
lemma uniq_linear_expansion:
  fixes f g::"nat \<Rightarrow> complex" 
  defines  "basis == canonical_basis::('a::basis_enum list)"
  assumes h1: "(\<Sum>i = 0 ..< length basis. f i *\<^sub>C (basis!i))
             = (\<Sum>i = 0..< length basis. g i *\<^sub>C (basis!i))" and 
    h2: "k < length basis"
  shows "f k = g k"
proof-
  have "0 = (\<Sum>i = 0 ..< length basis. f i *\<^sub>C (basis!i))
      - (\<Sum>i = 0..< length basis. g i *\<^sub>C (basis!i))"
    by (simp add: h1)
  also have "\<dots> = (\<Sum>i = 0 ..< length basis. f i *\<^sub>C (basis!i) -  g i *\<^sub>C (basis!i))"
    by (metis (no_types, lifting) sum.cong sum_subtractf)
  also have "\<dots> = (\<Sum>i = 0 ..< length basis. (f i - g i) *\<^sub>C (basis!i))"
    by (simp add: complex_vector.scale_left_diff_distrib)
  finally have "0 = (\<Sum>i = 0 ..< length basis. (f i - g i) *\<^sub>C (basis!i))" .
  hence "(\<Sum>i = 0 ..< length basis. (f i - g i) *\<^sub>C (basis!i)) = 0"
    by simp
  moreover have "complex_vector.independent (set basis)"
    using is_basis_set unfolding is_basis_def basis_def by blast 
  ultimately show ?thesis 
    using uniq_linear_expansion_zero[where f = "\<lambda>i. f i - g i"]
      basis_def eq_iff_diff_eq_0 h2 by blast    
qed



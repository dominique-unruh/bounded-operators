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

definition norm_vec :: "complex vec \<Rightarrow> complex" where
  "norm_vec x = sqrt (norm (x \<bullet>c x) )"

(* NEW *)
lemma norm_vec_onb_enum_of_vec:
  fixes x::"complex vec"
  assumes a1: "dim_vec x = canonical_basis_length TYPE('a::onb_enum)"
  shows "norm ((onb_enum_of_vec::_\<Rightarrow>'a) x) = norm_vec x"
proof-
  have "(norm_vec x)^2 = norm (x \<bullet>c x)"
    by (metis Bounded_Operators_Code.norm_vec_def norm_eq_sqrt_cinner of_real_power power2_norm_eq_cinner real_sqrt_power)
  also have "\<dots> = x \<bullet>c x"
    using complex_of_real_cmod by blast
  finally have a1: "(norm_vec x)^2 =  x \<bullet>c x"
    by blast
  have "\<langle>(onb_enum_of_vec::_\<Rightarrow>'a) x, (onb_enum_of_vec::_\<Rightarrow>'a) x\<rangle> =  x \<bullet>c x"
    using cinner_onb_enum_of_vec cinner_onb_enum_of_vec assms by blast    
  hence a2: "(norm ((onb_enum_of_vec::_\<Rightarrow>'a) x))^2 = x \<bullet>c x"
    by (smt power2_norm_eq_cinner')   
  have "(norm ((onb_enum_of_vec::_\<Rightarrow>'a) x))^2 = (norm_vec x)^2"
    using a1 a2
    by simp
  moreover have "norm (onb_enum_of_vec x) \<ge> 0"
    by simp    
  moreover have "norm_vec x \<ge> 0"
    unfolding norm_vec_def by simp
  ultimately show ?thesis
    by (smt complex_of_real_cmod norm_ge_zero of_real_hom.injectivity of_real_power power2_eq_imp_eq) 
qed


(* NEW *)
(* TODO remove *)
lemma norm_vec_vec_of_onb_enum:
  fixes x::"'a::onb_enum"
  shows "norm_vec (vec_of_onb_enum x) = norm x"
proof-
  define y where "y = vec_of_onb_enum x"
  have a1: "dim_vec y = canonical_basis_length TYPE('a)"
    unfolding y_def
    by (simp add: canonical_basis_length_eq dim_vec_of_onb_enum_list')    
  have "x = onb_enum_of_vec y"
    unfolding y_def
    by (simp add: onb_enum_of_vec_inverse)
  moreover have "norm ((onb_enum_of_vec::_\<Rightarrow>'a) y) = norm_vec y"
    apply (rule norm_vec_onb_enum_of_vec[where x = y])
    using a1.
  ultimately show ?thesis unfolding y_def
    by simp 
qed

(* NEW *)
(* TODO remove *)
lemma norm_vec_0:
  "norm_vec (0\<^sub>v n) = 0"
  unfolding norm_vec_def by auto

(* NEW *)
(* TODO remove *)
lemma norm_vec_0':
  assumes "norm_vec x = 0"
  shows "x = 0\<^sub>v (dim_vec x)"
proof-
  have "(norm_vec x)^2 = 0"
    using assms by simp
  moreover have "(norm_vec x)^2 = x \<bullet>c x"
    unfolding norm_vec_def
    using Bounded_Operators_Code.norm_vec_def calculation by auto
  ultimately have "x \<bullet>c x = 0"
    by simp
  thus ?thesis
    using carrier_vec_dim_vec conjugate_square_eq_0_vec by blast 
qed

(* NEW *)
(* TODO remove *)
lemma norm_vec_scalar:
  "norm_vec (c \<cdot>\<^sub>v x) = norm c * norm_vec x"
proof-
  have "(c \<cdot>\<^sub>v x)\<bullet>c(c \<cdot>\<^sub>v x) = c * (x \<bullet>c (c \<cdot>\<^sub>v x))"
    by simp
  also have "\<dots> = c * (cnj c) * (x \<bullet>c x)"
    by (simp add: conjugate_smult_vec)
  also have "\<dots> =  (norm c)^2 *(x \<bullet>c x)"
    using complex_norm_square by auto    
  finally have "(c \<cdot>\<^sub>v x)\<bullet>c(c \<cdot>\<^sub>v x) = (norm c)^2 *(x \<bullet>c x)"
    .
  thus ?thesis 
    unfolding norm_vec_def
    by (smt norm_ge_zero norm_mult norm_of_real of_real_mult real_sqrt_abs real_sqrt_mult sum_power2_ge_zero)    
qed

(* NEW *)
(* TODO remove *)
lemma norm_vec_geq0:
  "norm_vec x \<ge> 0"
  unfolding norm_vec_def by auto

(* NEW *)
(* TODO remove *)
lemma norm_vec_Real:
  "norm_vec x \<in> \<real>"
  using norm_vec_geq0 reals_zero_comparable_iff by auto

(* NEW *)
(* TODO remove *)
lemma arithmeticgeometric_vec:
  assumes "dim_vec x = dim_vec y"
  shows"2 * Re (x \<bullet>c y) \<le> x \<bullet>c x + y \<bullet>c y"
proof-
  have "0 \<le> (x - y) \<bullet>c (x - y)"
    by blast
  also have "\<dots> = (x - y) \<bullet>c x + (x - y) \<bullet>c (-y)"
    by (smt assms carrier_vecD carrier_vec_conjugate carrier_vec_dim_vec conjugate_add_vec 
        index_minus_vec(2) index_uminus_vec(2) minus_add_uminus_vec scalar_prod_add_distrib)
  also have "\<dots> = x \<bullet>c x + (-y) \<bullet>c x + x \<bullet>c (-y) + (-y) \<bullet>c (-y)"
  proof-
    have "(x - y) \<bullet>c x = x \<bullet>c x + (-y) \<bullet>c x"
      by (metis (mono_tags, lifting) assms carrier_vec_dim_vec diff_minus_eq_add dim_vec_conjugate 
          index_uminus_vec(2) minus_scalar_prod_distrib scalar_prod_uminus_left uminus_uminus_vec)      
    moreover have "(x - y) \<bullet>c (-y) = x \<bullet>c (-y) + (-y) \<bullet>c (-y)"
    proof -
      have "x \<in> carrier_vec (dim_vec y)"
        by (metis assms carrier_vec_dim_vec)
      hence "(x - y) \<bullet>c - y = x \<bullet>c - y - y \<bullet>c - y"
        by (simp add: minus_scalar_prod_distrib)
      thus ?thesis
        by simp
    qed     
    ultimately show ?thesis by simp
  qed
  also have "\<dots> = x \<bullet>c x - x \<bullet>c y - y \<bullet>c x + y \<bullet>c y"
    by (smt ab_group_add_class.ab_diff_conv_add_uminus assms diff_minus_eq_add dim_vec_conjugate 
        index_uminus_vec(2) scalar_prod_uminus_left scalar_prod_uminus_right 
        semiring_normalization_rules(23) uminus_conjugate_vec)    
  also have "\<dots> = x \<bullet>c x - 2 * Re (x \<bullet>c y) + y \<bullet>c y"
  proof-
    have "y \<bullet>c x = cnj (x \<bullet>c y)"
      using assms carrier_vec_dim_vec conjugate_complex_def  
        conjugate_vec_sprod_comm
      by (metis complex_cnj_complex_of_real vec_conjugate_real)
    hence "x \<bullet>c y + y \<bullet>c x = x \<bullet>c y + cnj (x \<bullet>c y)"
      by simp
    hence "x \<bullet>c y + y \<bullet>c x = 2 * Re (x \<bullet>c y)"
      by (simp add: complex_add_cnj)     
    thus ?thesis
      by (simp add: diff_diff_add) 
  qed
  finally have "0 \<le> x \<bullet>c x - 2 * Re (x \<bullet>c y) + y \<bullet>c y"
    by simp
  thus ?thesis
    by (simp add: diff_add_eq)
qed

(* TODO remove *)
lemma Lagrange_identity_squares':
  fixes x y :: "complex list"
  assumes a1: "length x = n" and a2: "length y = n"
  shows "2*((\<Sum>i = 0..<n. x!i * cnj (x!i))*(\<Sum>j = 0..<n. y!j * cnj (y!j))
       - (cmod (\<Sum>k = 0..<n. x!k * cnj (y!k)))^2) = 
 (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  (cmod( x!i * (cnj (y!j)) - x!j * (cnj (y!i)) ))^2 )"
proof-
  have "(\<Sum>i = 0..<n. x!i * cnj (x!i))*(\<Sum>j = 0..<n. y!j * cnj (y!j))
      = (\<Sum>i = 0..<n. x!i * (cnj (x!i))*(\<Sum>j = 0..<n. y!j * cnj (y!j)))"
    using vector_space_over_itself.scale_sum_left by blast
  also have "\<dots>
      = (\<Sum>i = 0..<n. (\<Sum>j = 0..<n. x!i * (cnj (x!i)) * y!j * cnj (y!j)))"
    using vector_space_over_itself.scale_sum_right
    by (smt sum.cong vector_space_over_itself.scale_scale) 
  also have "\<dots>
      = (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. x!i * (cnj (x!i)) * y!j * (cnj (y!j)))"
    by (simp add: sum.cartesian_product)
  finally have c1: "(\<Sum>i = 0..<n. x!i * cnj (x!i))*(\<Sum>j = 0..<n. y!j * cnj (y!j))
              = (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. x!i * (cnj (x!i)) * y!j * (cnj (y!j)))"
    .

  have "(cmod (\<Sum>k = 0..<n. x!k * cnj (y!k)))^2
      = (\<Sum>k = 0..<n. x!k * cnj (y!k)) * cnj (\<Sum>k = 0..<n. x!k * cnj (y!k))"
    using complex_norm_square by blast
  also have "\<dots> = (\<Sum>i = 0..<n. x!i * cnj (y!i)) * (\<Sum>j = 0..<n. (cnj (x!j)) * y!j)"
  proof-
    have "cnj (\<Sum>k = 0..<n. x!k * cnj (y!k)) = (\<Sum>k = 0..<n. (cnj (x!k)) * y!k)"
      by auto      
    thus ?thesis
      by simp 
  qed
  also have "\<dots> = (\<Sum>i = 0..<n. x!i * cnj (y!i) * (\<Sum>j = 0..<n. (cnj (x!j)) * y!j))"
    using vector_space_over_itself.scale_sum_left by blast
  also have "\<dots> = (\<Sum>i = 0..<n. (\<Sum>j = 0..<n. x!i * cnj (y!i) * (cnj (x!j)) * y!j))"
  proof-
    have "x!i * cnj (y!i) * (\<Sum>j = 0..<n. (cnj (x!j)) * y!j)
       = (\<Sum>j = 0..<n. x!i * cnj (y!i) * (cnj (x!j)) * y!j)"
      for i
      using vector_space_over_itself.scale_sum_right
      by (smt sum.cong vector_space_over_itself.scale_scale)      
    thus ?thesis
      by auto 
  qed
  also have "\<dots> = (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. x!i * cnj (y!i) * (cnj (x!j)) * y!j)"
    by (simp add: sum.cartesian_product)
  finally have c2: "(cmod (\<Sum>k = 0..<n. x!k * cnj (y!k)))^2 
              = (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. x!i * cnj (y!i) * (cnj (x!j)) * y!j)"
    .
  have "(\<Sum>i = 0..<n. x!i * cnj (x!i))*(\<Sum>j = 0..<n. y!j * cnj (y!j))
       - (cmod (\<Sum>k = 0..<n. x!k * cnj (y!k)))^2
      = (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. x!i * (cnj (x!i)) * y!j * (cnj (y!j)))
      - (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. x!i * (cnj (y!i)) * (cnj (x!j)) * y!j)"
    using c1 c2 by simp
  also have "\<dots> = (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. 
                x!i * (cnj (x!i)) * y!j * (cnj (y!j))
              - x!i * (cnj (y!i)) * (cnj (x!j)) * y!j  )"
  proof-
    define f where "f = (\<lambda>(i,j). x!i * (cnj (x!i)) * y!j * (cnj (y!j)))"
    define g where "g = (\<lambda>(i,j). x!i * (cnj (y!i)) * (cnj (x!j)) * y!j)"
    have "(\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. f (i,j) - g (i,j)  )
      = (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. f (i,j))
      - (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. g (i,j))"
      using Groups_Big.sum_subtractf[where A = "{0..<n}\<times>{0..<n}"]
      by auto               
    thus ?thesis
      unfolding f_def g_def
      by simp
  qed
  finally have c3: "(\<Sum>i = 0..<n. x!i * cnj (x!i))*(\<Sum>j = 0..<n. y!j * cnj (y!j))
       - (cmod (\<Sum>k = 0..<n. x!k * cnj (y!k)))^2
 = (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. 
   x!i * (cnj (x!i)) * y!j * (cnj (y!j))
 - x!i * (cnj (y!i)) * (cnj (x!j)) * y!j  )"
    .
  have "(cmod (x ! i * cnj (y ! j) - x ! j * cnj (y ! i)))\<^sup>2
    = x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
    - x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
    - x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
    + x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i)"
    for i j
  proof-
    have "(cmod (x ! i * cnj (y ! j) - x ! j * cnj (y ! i)))\<^sup>2
    = (x ! i * cnj (y ! j) - x ! j * cnj (y ! i)) * cnj (x ! i * cnj (y ! j) - x ! j * cnj (y ! i))"
      using complex_norm_square by auto
    also have "\<dots>
    = (x ! i * cnj (y ! j) - x ! j * cnj (y ! i)) * (cnj (x ! i) * (y ! j) - cnj (x ! j) * (y ! i))"
      by simp
    also have "\<dots>
    = x ! i * cnj (y ! j)  * (cnj (x ! i) * (y ! j) - cnj (x ! j) * (y ! i))
    - x ! j * cnj (y ! i)  * (cnj (x ! i) * (y ! j) - cnj (x ! j) * (y ! i))"
      by (simp add: linordered_field_class.sign_simps(20))
    also have "\<dots>
    = x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j) - x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
    - x ! j * cnj (y ! i)  * (cnj (x ! i) * (y ! j) - cnj (x ! j) * (y ! i))"
      by (simp add: linordered_field_class.sign_simps(19) linordered_field_class.sign_simps(4))
    also have "\<dots>
    = x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
    - x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
    - x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
    + x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i)"
      by (simp add: right_diff_distrib')
    finally show ?thesis .
  qed
  hence "(\<lambda>(i,j). (cmod (x ! i * cnj (y ! j) - x ! j * cnj (y ! i)))\<^sup>2 )
    =(\<lambda>(i,j). x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
    - x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
    - x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
    + x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i) )"
    by auto
  hence c4: "(\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  (cmod( x!i * (cnj (y!j)) - x!j * (cnj (y!i)) ))^2 )
         = (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  
      x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
    - x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
    - x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
    + x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i) )"
    by (smt of_real_hom.hom_sum sum.cong)

  have "2*((\<Sum>i = 0..<n. x!i * cnj (x!i))*(\<Sum>j = 0..<n. y!j * cnj (y!j))
       - (cmod (\<Sum>k = 0..<n. x!k * cnj (y!k)))^2) -
         (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  (cmod( x!i * (cnj (y!j)) - x!j * (cnj (y!i)) ))^2 ) = 
   2 * (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. 
   x!i * (cnj (x!i)) * y!j * (cnj (y!j))
 - x!i * (cnj (y!i)) * (cnj (x!j)) * y!j  )
 - (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  
      x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
    - x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
    - x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
    + x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i) )"
    using c3 c4 
    by simp
  also have "\<dots> = 
   (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. 
    x!i * (cnj (x!i)) * y!j * (cnj (y!j))
 -  x!i * (cnj (y!i)) * (cnj (x!j)) * y!j 
 +  x!j * (cnj (x!j)) * y!i * (cnj (y!i))
 -  x!j * (cnj (y!j)) * (cnj (x!i)) * y!i 
 )
 - (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  
      x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
    - x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
    - x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
    + x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i) )"
  proof-
    define f where "f = (\<lambda> (i,j). x!i * (cnj (x!i)) * y!j * (cnj (y!j))
                       - x!i * (cnj (y!i)) * (cnj (x!j)) * y!j)"
    have "2 * (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. f (i,j)) = 
        (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  2*f (i,j))"
      using Cartesian_Space.vector_space_over_itself.scale_sum_right
        [where A = "{0..<n}\<times>{0..<n}" and a = 2 and f = f]
      by auto
    moreover have "2 * (x!i * (cnj (x!i)) * y!j * (cnj (y!j))
                 - x!i * (cnj (y!i)) * (cnj (x!j)) * y!j )
=  2 * x!i * (cnj (x!i)) * y!j * (cnj (y!j))
 - 2 * x!i * (cnj (y!i)) * (cnj (x!j)) * y!j"
      for i j
      by auto
    ultimately have "2 * (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. 
   x!i * (cnj (x!i)) * y!j * (cnj (y!j))
 - x!i * (cnj (y!i)) * (cnj (x!j)) * y!j  ) = 
  (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. 
   2 * x!i * (cnj (x!i)) * y!j * (cnj (y!j))
 - 2 * x!i * (cnj (y!i)) * (cnj (x!j)) * y!j  )"
      unfolding f_def apply auto
      by (simp add: mult.commute mult.left_commute)
    thus ?thesis sorry  (* Ask to Dominique *)
  qed
  also have "\<dots> = 
   (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. 
      ( x!i * (cnj (x!i)) * y!j * (cnj (y!j))
     -  x!i * (cnj (y!i)) * (cnj (x!j)) * y!j 
     +  x!j * (cnj (x!j)) * y!i * (cnj (y!i))
     -  x!j * (cnj (y!j)) * (cnj (x!i)) * y!i  ) 
   - ( x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
     - x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
     - x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
     + x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i) ) )"
  proof-
    define f where "f = (\<lambda>(i,j). x!i * (cnj (x!i)) * y!j * (cnj (y!j))
 -  x!i * (cnj (y!i)) * (cnj (x!j)) * y!j 
 +  x!j * (cnj (x!j)) * y!i * (cnj (y!i))
 -  x!j * (cnj (y!j)) * (cnj (x!i)) * y!i )"
    define g where "g = (\<lambda>(i,j). x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
     - x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
     - x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
     + x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i) )"
    have "(\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. f (i,j) - g (i,j)) = 
          (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. f (i,j))
        - (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. g (i,j))"
      using Groups_Big.sum_subtractf[where A = "{0..<n}\<times>{0..<n}" and f = f and g = g]
      by simp
    thus ?thesis unfolding f_def g_def by auto
  qed
  also have "\<dots> = 
   (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. 
        x!i * (cnj (x!i)) * y!j * (cnj (y!j))
     -  x!i * (cnj (y!i)) * (cnj (x!j)) * y!j 
     +  x!j * (cnj (x!j)) * y!i * (cnj (y!i))
     -  x!j * (cnj (y!j)) * (cnj (x!i)) * y!i   
     - x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
     + x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
     + x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
     - x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i) )"
  proof-
    have " 
      ( x!i * (cnj (x!i)) * y!j * (cnj (y!j))
     -  x!i * (cnj (y!i)) * (cnj (x!j)) * y!j 
     +  x!j * (cnj (x!j)) * y!i * (cnj (y!i))
     -  x!j * (cnj (y!j)) * (cnj (x!i)) * y!i  ) 
   - ( x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
     - x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
     - x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
     + x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i) ) = 
     x!i * (cnj (x!i)) * y!j * (cnj (y!j))
     -  x!i * (cnj (y!i)) * (cnj (x!j)) * y!j 
     +  x!j * (cnj (x!j)) * y!i * (cnj (y!i))
     -  x!j * (cnj (y!j)) * (cnj (x!i)) * y!i   
     - x ! i * cnj (y ! j) * cnj (x ! i) * (y ! j)
     + x ! i * cnj (y ! j) * cnj (x ! j) * (y ! i)
     + x ! j * cnj (y ! i) * cnj (x ! i) * (y ! j)
     - x ! j * cnj (y ! i) * cnj (x ! j) * (y ! i)"
      for i j
      by auto
    thus ?thesis
      by meson 
  qed
  also have "\<dots> = 
   (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}. 
      (x!i * cnj (x!j) - x!j * cnj (x!i))
    * (y!i * cnj (y!j) - y!j * cnj (y!i)))"
  proof-
    have "x!i * (cnj (x!i)) * y!j         * (cnj (y!j))
       -  x!i * (cnj (y!i)) * (cnj (x!j)) * y!j 
       +  x!j * (cnj (x!j)) * y!i         * (cnj (y!i))
       -  x!j * (cnj (y!j)) * (cnj (x!i)) * y!i   
       -  x!i * (cnj (y!j)) * (cnj (x!i)) * y!j
       +  x!i * (cnj (y!j)) * (cnj (x!j)) * y!i
       +  x!j * (cnj (y!i)) * (cnj (x!i)) * y!j
       -  x!j * (cnj (y!i)) * (cnj (x!j)) * y!i = 
      (x!i * cnj (x!j) - x!j * cnj (x!i))
    * (y!i * cnj (y!j) - y!j * cnj (y!i))"
      for i j
    proof-
      have "x!i * (cnj (x!i)) * y!j         * (cnj (y!j))
       -  x!i * (cnj (y!i)) * (cnj (x!j)) * y!j 
       +  x!j * (cnj (x!j)) * y!i         * (cnj (y!i))
       -  x!j * (cnj (y!j)) * (cnj (x!i)) * y!i   
       -  x!i * (cnj (y!j)) * (cnj (x!i)) * y!j
       +  x!i * (cnj (y!j)) * (cnj (x!j)) * y!i
       +  x!j * (cnj (y!i)) * (cnj (x!i)) * y!j
       -  x!j * (cnj (y!i)) * (cnj (x!j)) * y!i 
      = 
          x!i * (cnj (x!i)) * (cnj (y!j))  * y!j              
       -  x!i * (cnj (x!j)) * (cnj (y!i))  * y!j 
       +  x!j * (cnj (x!j)) * (cnj (y!i))  * y!i          
       -  x!j * (cnj (y!j)) * (cnj (x!i))  * y!i   
       -  x!i * (cnj (x!i)) * (cnj (y!j))  * y!j
       +  x!i * (cnj (x!j)) * (cnj (y!j))  * y!i
       +  x!j * (cnj (x!i)) * (cnj (y!i))  * y!j
       -  x!j * (cnj (x!j)) * (cnj (y!i))  * y!i"
        by auto
      also have "\<dots> = 
    x ! i * cnj (x ! j) * cnj (y ! j) * y ! i 
  + x ! j * cnj (x ! i) * cnj (y ! i) * y ! j 
  - x ! i * cnj (x ! j) * cnj (y ! i) * y ! j 
  - x ! j * cnj (x ! i) * cnj (y ! j) * y ! i"
        by simp
      also have "\<dots> = 
    (  x ! i * cnj (x ! j) * cnj (y ! j) * y ! i 
     - x ! i * cnj (x ! j) * cnj (y ! i) * y ! j) 
  - (  x ! j * cnj (x ! i) * cnj (y ! j) * y ! i
     - x ! j * cnj (x ! i) * cnj (y ! i) * y ! j )"
        by simp
      also have "\<dots> =  x ! i * cnj (x ! j) * (cnj (y ! j) * y ! i -  cnj (y ! i) * y ! j) 
    - x ! j * cnj (x ! i) * (cnj (y ! j) * y ! i -  cnj (y ! i) * y ! j )"
        by (simp add: ab_semigroup_mult_class.mult_ac(1) right_diff_distrib)
      also have "\<dots> = (x!i * cnj (x!j) - x!j * cnj (x!i)) * (cnj (y!j) * y!i -  cnj (y!i) * y!j)"
        by (simp add: left_diff_distrib)        
      also have "\<dots> = (x!i * cnj (x!j) - x!j * cnj (x!i))
    * (y!i * cnj (y!j) - y!j * cnj (y!i))"
        by auto
      finally show 
        ?thesis by auto
    qed
    thus ?thesis by meson 
  qed
  also have "\<dots> = 0"
     (* Ask to Dominique *)
    sorry
  finally have "2*((\<Sum>i = 0..<n. x!i * cnj (x!i))*(\<Sum>j = 0..<n. y!j * cnj (y!j))
       - (cmod (\<Sum>k = 0..<n. x!k * cnj (y!k)))^2) -
 (\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  (cmod( x!i * (cnj (y!j)) - x!j * (cnj (y!i)) ))^2 ) = 0"
    .
  thus ?thesis by simp  
qed


(* NEW *)
(* TODO: move *)
(* TODO remove *)
lemma Lagrange_identity_squares:
  fixes x y :: "complex list"
  assumes a1: "length x = n" and a2: "length y = n"
  shows "(\<Sum>i = 0..<n. x!i * cnj (x!i))*(\<Sum>j = 0..<n. y!j * cnj (y!j))
       - (cmod (\<Sum>k = 0..<n. x!k * cnj (y!k)))^2 = 
 (inverse 2::complex)*(\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  (cmod( x!i * (cnj (y!j)) - x!j * (cnj (y!i)) ))^2 )"
  sorry

(* NEW *)
(* TODO: move *)
(* TODO remove *)
lemma Cauchy_Schwarz_sum_abs:
  fixes x y :: "complex list"
  assumes a1: "length x = n" and a2: "length y = n"
  shows "cmod (\<Sum>i = 0..<n. x!i * cnj (y!i)) \<le> 
   sqrt (cmod (\<Sum>i = 0..<n. x!i * cnj (x!i)))
 * sqrt (cmod (\<Sum>i = 0..<n. y!i * cnj (y!i)))"
proof-
  have "(i,j)\<in>{0..<n}\<times>{0..<n} \<Longrightarrow>
    (cmod( x!i * (cnj (y!j)) - x!j * (cnj (y!i)) ))^2 \<ge> 0"
    for i j
    by simp    
  hence "(\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  
    (cmod( x!i * (cnj (y!j)) - x!j * (cnj (y!i)) ))^2 ) \<ge> 0"
    by (smt SigmaE case_prod_conv sum_nonneg)    
  hence "(inverse 2::complex)*(\<Sum>(i,j)\<in>{0..<n}\<times>{0..<n}.  
    (cmod( x!i * (cnj (y!j)) - x!j * (cnj (y!i)) ))^2 ) \<ge> 0"
    by simp
  hence "(\<Sum>i = 0..<n. x!i * cnj (x!i))*(\<Sum>j = 0..<n. y!j * cnj (y!j))
       - (cmod (\<Sum>k = 0..<n. x!k * cnj (y!k)))^2 \<ge> 0"
    using  assms Lagrange_identity_squares[where x = x and y = y and n = n]
    by presburger    
  hence "(cmod (\<Sum>i = 0..<n. x!i * cnj (y!i)))^2 \<le> 
   (\<Sum>i = 0..<n. x!i * cnj (x!i)) * (\<Sum>i = 0..<n. y!i * cnj (y!i))"
    by simp
  moreover have "(\<Sum>i = 0..<n. x!i * cnj (x!i)) \<ge> 0"
    by (simp add: sum_nonneg)    
  moreover have "(\<Sum>i = 0..<n. y!i * cnj (y!i)) \<ge> 0"
    by (simp add: sum_nonneg)
  ultimately have b1: "(cmod (\<Sum>i = 0..<n. x!i * cnj (y!i)))^2 \<le> 
   cmod (\<Sum>i = 0..<n. x!i * cnj (x!i)) * cmod (\<Sum>i = 0..<n. y!i * cnj (y!i))"
    by (metis (no_types, lifting) complex_of_real_cmod complex_of_real_mono_iff of_real_mult)    
  thus ?thesis
    by (metis (lifting) b1 real_le_rsqrt real_sqrt_mult)
qed

(* NEW *)
(* TODO remove *)
lemma Cauchy_Schwarz_vec:
  assumes a1: "dim_vec x = dim_vec y"
  shows "cmod (x \<bullet>c y) \<le> sqrt (cmod (x \<bullet>c x) ) * sqrt (cmod (y \<bullet>c y))"
proof-
  define n where "n = dim_vec y"
  have n_def': "n = dim_vec x"
    unfolding n_def using a1 by simp

  have "x \<bullet>c y = (\<Sum>i = 0..<n. (vec_index x i) * cnj (vec_index y i))"
    unfolding n_def
    using scalar_prod_def[where v = x and w = "conjugate y"] 
    by simp
  moreover have "x \<bullet>c x = (\<Sum>i = 0..<n. (vec_index x i) * cnj (vec_index x i))"
    unfolding n_def'
    using scalar_prod_def[where v = x and w = "conjugate x"] 
    by simp
  moreover have "y \<bullet>c y = (\<Sum>i = 0..<n. (vec_index y i) * cnj (vec_index y i))"
    unfolding n_def
    using scalar_prod_def[where v = y and w = "conjugate y"] 
    by simp
  moreover have "cmod (\<Sum>i = 0..<n. (vec_index x i) * cnj (vec_index y i)) \<le> 
    sqrt (cmod (\<Sum>i = 0..<n. (vec_index x i) * cnj (vec_index x i)))
  * sqrt (cmod (\<Sum>i = 0..<n. (vec_index y i) * cnj (vec_index y i)))"
  proof-
    define u where "u = list_of_vec x"
    define v where "v = list_of_vec y"
    have "length u = n"
      by (simp add: n_def' u_def)      
    moreover have "length v = n"
      using n_def v_def by auto      
    ultimately show ?thesis
      using Cauchy_Schwarz_sum_abs[where x = u and y = v]
      unfolding u_def v_def by simp      
  qed
  ultimately show ?thesis by simp
qed

(* NEW *)
(* TODO remove *)

lemma norm_vec_triangular:
  assumes "dim_vec x = dim_vec y"
  shows "norm_vec (x + y) \<le> norm_vec x + norm_vec y"
proof-
  have "(complex_of_real (sqrt (cmod ((x + y) \<bullet>c (x + y)))))\<^sup>2 = (x + y) \<bullet>c (x + y)"
    by (metis complex_of_real_cmod conjugate_square_ge_0_vec norm_ge_zero of_real_sqrt power2_csqrt)
  also have "\<dots> = (x + y) \<bullet>c x +  (x + y) \<bullet>c y"
    by (smt add_scalar_prod_distrib assms carrier_vec_dim_vec conjugate_add_vec 
        conjugate_vec_sprod_comm dim_vec_conjugate index_add_vec(2))    
  also have "\<dots> = x \<bullet>c x + y \<bullet>c x + x \<bullet>c y + y \<bullet>c y"
    by (smt add_scalar_prod_distrib assms carrier_vec_dim_vec dim_vec_conjugate 
        semiring_normalization_rules(25))
  also have "\<dots> = x \<bullet>c x + cnj (x \<bullet>c y) + x \<bullet>c y + y \<bullet>c y"
    by (metis assms carrier_vec_dim_vec conjugate_complex_def conjugate_conjugate_sprod 
        conjugate_vec_sprod_comm)
  also have "\<dots> = x \<bullet>c x + 2 * Re (x \<bullet>c y) + y \<bullet>c y"
    by (simp add: complex_add_cnj linordered_field_class.sign_simps(2))
  also have "\<dots> \<le> x \<bullet>c x + 2 * sqrt (norm (x \<bullet>c x) ) * sqrt (norm (y \<bullet>c y)) + y \<bullet>c y"
  proof-
    have "norm (x \<bullet>c y) \<le> sqrt (norm (x \<bullet>c x) ) * sqrt (norm (y \<bullet>c y))"
      using Cauchy_Schwarz_vec assms by blast
    hence "Re (x \<bullet>c y) \<le> sqrt (norm (x \<bullet>c x) ) * sqrt (norm (y \<bullet>c y))"
      using complex_Re_le_cmod dual_order.trans by blast 
    thus ?thesis by simp
  qed
  also have "\<dots> \<le> (sqrt (norm (x \<bullet>c x)))^2 + 2 * sqrt (norm (x \<bullet>c x) ) * sqrt (norm (y \<bullet>c y)) + (sqrt (norm (y \<bullet>c y)))^2"
  proof-
    have "(sqrt (norm (x \<bullet>c x)))^2 = x \<bullet>c x"
      by (metis abs_norm_cancel complex_of_real_cmod conjugate_square_ge_0_vec real_sqrt_abs 
          real_sqrt_power)      
    moreover have "(sqrt (norm (y \<bullet>c y)))^2 = y \<bullet>c y"
      by (metis abs_norm_cancel complex_of_real_cmod conjugate_square_ge_0_vec real_sqrt_abs 
          real_sqrt_power)
    ultimately show ?thesis by simp
  qed
  also have "\<dots> = (complex_of_real (sqrt (cmod (x \<bullet>c x))) + complex_of_real (sqrt (cmod (y \<bullet>c y))))\<^sup>2"
  proof -
    have f1: "\<And>r s. (r::real)\<^sup>2 + (s\<^sup>2 + 2 * r * s) = (r + s)\<^sup>2"
      by (metis (no_types) power2_sum semiring_normalization_rules(25))
    have "\<And>r s t. (r::real) + s + t = s + (r + t)"
      by linarith
    thus ?thesis
      using f1 by (metis (no_types) of_real_add of_real_power semiring_normalization_rules(24) 
          semiring_normalization_rules(25))
  qed       
  finally have "(complex_of_real (sqrt (cmod ((x + y) \<bullet>c (x + y)))))\<^sup>2
    \<le> (complex_of_real (sqrt (cmod (x \<bullet>c x))) + complex_of_real (sqrt (cmod (y \<bullet>c y))))\<^sup>2"
    by simp
  hence "(norm_vec (x + y))^2 \<le> (norm_vec x + norm_vec y)^2"
    unfolding norm_vec_def.
  moreover have "norm_vec (x + y) \<ge> 0"
    using norm_vec_geq0 by blast     
  moreover have "norm_vec x + norm_vec y \<ge> 0"
    using norm_vec_geq0 by auto    
  ultimately show ?thesis     
    using power2_le_imp_le
    by auto
qed

(* NEW *)
(* TODO remove *)
lemma norm_vec_mat:
  shows "\<exists>K. \<forall>x. dim_col M = dim_vec x \<longrightarrow> norm_vec (M *\<^sub>v x) \<le> norm_vec x * K"
  sorry



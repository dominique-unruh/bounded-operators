(*  Title:      Complex_Euclidean_Space.thy
    Author:     Dominique Unruh (University of Tartu)
    Author:     Jose Manuel Rodriguez Caballero (University of Tartu)
*)
section \<open>Finite-Dimensional Complex Inner Product Spaces\<close>

theory Complex_Euclidean_Space
imports
  Complex_Inner_Product
  "HOL-Analysis.Product_Vector"  
begin

unbundle notation_norm

text\<open>
  We extend the file @text{HOL/Analysis/Euclidean_Space.thy (Johannes Hölzl, Brian Huffman)} to the
  complex numbers.
\<close>

subsection \<open>Type class of complex Euclidean spaces\<close>

class complex_euclidean_space = complex_inner +
  fixes cBasis :: "'a set"
  assumes complex_nonempty_cBasis [simp]: "cBasis \<noteq> {}"
  assumes complex_finite_cBasis [simp]: "finite cBasis"
  assumes complex_inner_cBasis:
    "\<lbrakk>u \<in> cBasis; v \<in> cBasis\<rbrakk> \<Longrightarrow> \<langle>u, v\<rangle> = (if u = v then 1 else 0)"
  assumes complex_euclidean_all_zero_iff:
    "(\<forall>u\<in>cBasis. \<langle>x, u\<rangle> = 0) \<longleftrightarrow> (x = 0)"


syntax "_type_dimension" :: "type \<Rightarrow> nat"  ("(1cDIM/(1'(_')))")
translations "cDIM('a)" \<rightharpoonup> "CONST card (CONST cBasis :: 'a set)"
typed_print_translation \<open>
  [(\<^const_syntax>\<open>card\<close>,
    fn ctxt => fn _ => fn [Const (\<^const_syntax>\<open>cBasis\<close>, Type (\<^type_name>\<open>set\<close>, [T]))] =>
      Syntax.const \<^syntax_const>\<open>_type_dimension\<close> $ Syntax_Phases.term_of_typ ctxt T)]
\<close>

lemma (in complex_euclidean_space) cnorm_cBasis[simp]: "u \<in> cBasis \<Longrightarrow> norm u = 1"
  by (simp add: local.complex_inner_cBasis local.norm_eq_sqrt_cinner)
  

lemma (in complex_euclidean_space) cinner_same_cBasis[simp]: "u \<in> cBasis \<Longrightarrow> \<langle>u, u\<rangle> = 1"
  by (simp add: local.complex_inner_cBasis)


lemma (in complex_euclidean_space) cinner_not_same_cBasis: "u \<in> cBasis \<Longrightarrow> v \<in> cBasis \<Longrightarrow> u \<noteq> v \<Longrightarrow> 
  \<langle>u, v\<rangle> = 0"
  by (simp add: local.complex_inner_cBasis)
  

lemma (in complex_euclidean_space) csgn_cBasis: "u \<in> cBasis \<Longrightarrow> sgn u = u"
  using local.scaleR_one local.sgn_div_norm by auto


lemma (in complex_euclidean_space) ccBasis_zero [simp]: "0 \<notin> cBasis"
  using local.cinner_same_cBasis by fastforce


lemma (in complex_euclidean_space) cnonzero_cBasis: "u \<in> cBasis \<Longrightarrow> u \<noteq> 0"
  by clarsimp

lemma (in complex_euclidean_space) cSOME_cBasis: "(SOME i. i \<in> cBasis) \<in> cBasis"
  by (meson ex_in_conv local.complex_nonempty_cBasis someI)

lemma cnorm_some_cBasis [simp]: "norm (SOME i. i \<in> cBasis) = 1"
  using cSOME_cBasis cnorm_cBasis by auto
  

lemma (in complex_euclidean_space) cinner_sum_left_cBasis[simp]:
    "b \<in> cBasis \<Longrightarrow> \<langle>(\<Sum>i\<in>cBasis. (cnj (f i)) *\<^sub>C i), b\<rangle> = f b"
proof-
  assume a1: "b \<in> cBasis"
  hence "\<exists>cBasis'. cBasis = insert b cBasis' \<and> b \<notin> cBasis'"
    by (meson Set.set_insert)
  then obtain cBasis' where b1: "cBasis = insert b cBasis'" and b2: "b \<notin> cBasis'"
    by blast
  have "i\<in>cBasis' \<Longrightarrow> (f i) * \<langle>i, b\<rangle> = 0" for i
    by (metis (mono_tags, lifting) b1 b2 insertCI local.cinner_not_same_cBasis mult_not_zero)    
  hence c1: "(\<Sum>i\<in>cBasis'. (f i) * \<langle>i, b\<rangle>) = 0"
    by (simp add: \<open>\<And>i. i \<in> cBasis' \<Longrightarrow> f i * \<langle>i, b\<rangle> = 0\<close>)
  have "\<langle>(\<Sum>i\<in>cBasis. (cnj (f i)) *\<^sub>C i), b\<rangle> = (\<Sum>i\<in>cBasis. \<langle>(cnj (f i)) *\<^sub>C i, b\<rangle>)"
    by (metis local.cinner_sum_left)
  also have "\<dots> = (\<Sum>i\<in>cBasis. (f i) * \<langle>i, b\<rangle>)"
    by auto
  also have "\<dots> = (f b) * \<langle>b, b\<rangle> + (\<Sum>i\<in>cBasis'. (f i) * \<langle>i, b\<rangle>)"
    using b1 b2 local.complex_finite_cBasis by auto 
  also have "\<dots> = f b"
    using c1
    by (simp add: a1)
  finally show ?thesis by blast
qed

lemma (in complex_euclidean_space) cinner_sum_left_cBasis'[simp]:
    "b \<in> cBasis \<Longrightarrow> \<langle>(\<Sum>i\<in>cBasis. (f i) *\<^sub>C i), b\<rangle> = cnj (f b)"
  using cinner_sum_left_cBasis[where f = "\<lambda>x. cnj (f x)"]
  by auto

lemma (in complex_euclidean_space) euclidean_eqI:
  assumes b: "\<And>b. b \<in> cBasis \<Longrightarrow> \<langle>x, b\<rangle> = \<langle>y, b\<rangle>" shows "x = y"
proof -
  from b have "\<forall>b\<in>cBasis. \<langle>x - y, b\<rangle> = 0"
    by (simp add: local.cinner_diff_left)    
  thus "x = y"
    using local.complex_euclidean_all_zero_iff by auto    
qed


lemma (in complex_euclidean_space) complex_euclidean_eq_iff:
  "x = y \<longleftrightarrow> (\<forall>b\<in>cBasis. \<langle>x, b\<rangle> = \<langle>y, b\<rangle>)"
  using local.euclidean_eqI by auto
  
lemma (in complex_euclidean_space) complex_euclidean_representation_sum:
  "(\<Sum>i\<in>cBasis. f i *\<^sub>C i) = b \<longleftrightarrow> (\<forall>i\<in>cBasis. f i = cnj \<langle>b, i\<rangle>)"
  proof
  show "\<forall>i\<in>cBasis. f i = cnj \<langle>b, i\<rangle>"
    if "(\<Sum>i\<in>cBasis. f i *\<^sub>C i) = b"
  proof
    fix i
    assume a1: "i \<in> cBasis"
    have "\<langle>b, i\<rangle> = \<langle>(\<Sum>j\<in>cBasis. f j *\<^sub>C j), i\<rangle>"
      by (simp add: that)
    also have "\<dots> = cnj (f i)"
      using cinner_sum_left_cBasis' a1 by blast 
    finally show "f i = cnj \<langle>b, i\<rangle>" by simp 
  qed
  show "(\<Sum>i\<in>cBasis. f i *\<^sub>C i) = b"
    if "\<forall>i\<in>cBasis. f i = cnj \<langle>b, i\<rangle>"
  proof-
    have "(\<Sum>i\<in>cBasis. cnj \<langle>b, i\<rangle> *\<^sub>C i) = b"
      using local.euclidean_eqI by auto      
    thus ?thesis using that by (simp add: \<open>(\<Sum>i\<in>cBasis. cnj \<langle>b, i\<rangle> *\<^sub>C i) = b\<close>)
  qed
qed

lemma (in complex_euclidean_space) complex_euclidean_representation_sum':
  "b = (\<Sum>i\<in>cBasis. f i *\<^sub>C i) \<longleftrightarrow> (\<forall>i\<in>cBasis. f i = cnj \<langle>b, i\<rangle>)"
  using complex_euclidean_representation_sum[where f = f and b = b] by blast

lemma (in complex_euclidean_space) complex_euclidean_representation: 
  "(\<Sum>b\<in>cBasis. cnj \<langle>x, b\<rangle> *\<^sub>C b) = x"
  using complex_euclidean_representation_sum by simp

lemma (in complex_euclidean_space) complex_euclidean_cinner:
  "\<langle>x, y\<rangle> = (\<Sum>b\<in>cBasis. \<langle>x, b\<rangle> * cnj \<langle>y, b\<rangle>)"
proof-
  have "\<langle>x, y\<rangle> = \<langle>(\<Sum>b\<in>cBasis. cnj \<langle>x, b\<rangle> *\<^sub>C b), y\<rangle>"
    using complex_euclidean_representation by simp
  also have "\<dots> = (\<Sum>b\<in>cBasis. \<langle>cnj \<langle>x, b\<rangle> *\<^sub>C b, y\<rangle>)"
    using local.cinner_sum_left by blast
  also have "\<dots> = (\<Sum>b\<in>cBasis. \<langle>x, b\<rangle> * \<langle>b, y\<rangle>)"
    by (metis local.cinner_cnj_commute local.cinner_scaleC_left)
  also have "\<dots> = (\<Sum>b\<in>cBasis. \<langle>x, b\<rangle> * cnj \<langle>y, b\<rangle>)"
    by (metis local.cinner_cnj_commute)
  finally show ?thesis by blast
qed

lemma (in complex_euclidean_space) choice_cBasis_iff:
  fixes P :: "'a \<Rightarrow> complex \<Rightarrow> bool"
  shows "(\<forall>i\<in>cBasis. \<exists>x. P i x) \<longleftrightarrow> (\<exists>x. \<forall>i\<in>cBasis. P i \<langle>x, i\<rangle>)"
  proof
  show "\<exists>x. \<forall>i\<in>cBasis. P i \<langle>x, i\<rangle>"
    if "\<forall>i\<in>cBasis. \<exists>x. P i x"
  proof-
    have "\<exists>f. \<forall>i\<in>cBasis. P i (f i)"
      using that by metis
    then obtain f where a1: "i\<in>cBasis \<Longrightarrow> P i (f i)" for i
      by blast
    define x where "x = (\<Sum>i\<in>cBasis. cnj (f i) *\<^sub>C i)"
    have "i\<in>cBasis \<Longrightarrow> \<langle>x, i\<rangle> = f i" for i
      unfolding x_def using local.cinner_sum_left_cBasis by blast 
    hence "i\<in>cBasis \<Longrightarrow> P i \<langle>x, i\<rangle>" for i
      using a1 by simp
    thus ?thesis by blast
  qed
  show "\<forall>i\<in>cBasis. \<exists>x. P i x"
    if "\<exists>x. \<forall>i\<in>cBasis. P i \<langle>x, i\<rangle>"
    using that by auto
qed

lemma (in complex_euclidean_space) bchoice_cBasis_iff:
  fixes P :: "'a \<Rightarrow> complex \<Rightarrow> bool"
  shows "(\<forall>i\<in>cBasis. \<exists>x\<in>A. P i x) \<longleftrightarrow> (\<exists>x. \<forall>i\<in>cBasis. \<langle>x, i\<rangle> \<in> A \<and> P i \<langle>x, i\<rangle>)"
by (simp add: choice_cBasis_iff Bex_def)

lemma (in complex_euclidean_space) complex_euclidean_representation_sum_fun:
    "(\<lambda>x. \<Sum>b\<in>cBasis. cnj \<langle>f x, b\<rangle> *\<^sub>C b) = f"
  by (rule ext) (simp add: complex_euclidean_representation_sum)

lemma complex_euclidean_isCont:
  assumes "\<And>b. b \<in> cBasis \<Longrightarrow> isCont (\<lambda>x. cnj \<langle>f x, b\<rangle> *\<^sub>C b) x"
    shows "isCont f x"
  apply (subst complex_euclidean_representation_sum_fun [symmetric])
  apply (rule isCont_sum)
  by (simp add: assms)

lemma cDIM_positive [simp]: "0 < cDIM('a::complex_euclidean_space)"
  by (simp add: card_gt_0_iff)

lemma cDIM_ge_Suc0 [simp]: "Suc 0 \<le> card cBasis"
  by (meson cDIM_positive Suc_leI)

lemma sum_inner_cBasis_scaleC [simp]:
  fixes f :: "'a::complex_euclidean_space \<Rightarrow> 'b::complex_vector"
  assumes b1: "b \<in> cBasis" 
  shows "(\<Sum>i\<in>cBasis. \<langle>i, b\<rangle> *\<^sub>C f i) = f b"
proof-
  have "\<exists>cBasis'. cBasis = insert b cBasis' \<and> b \<notin> cBasis'"
    by (simp add: b1 mk_disjoint_insert)
  then obtain cBasis' where c1: "cBasis = insert b cBasis'" and c2: "b \<notin> cBasis'"
    by blast
  have "i\<in>cBasis' \<Longrightarrow> \<langle>i, b\<rangle> *\<^sub>C f i = 0" for i
    by (metis c1 c2 cinner_not_same_cBasis complex_vector.scale_eq_0_iff insertCI)    
  hence d1: "(\<Sum>i\<in>cBasis'. \<langle>i, b\<rangle> *\<^sub>C f i) = 0"
    by (simp add: \<open>\<And>i. i \<in> cBasis' \<Longrightarrow> \<langle>i, b\<rangle> *\<^sub>C f i = 0\<close>)   
  have "(\<Sum>i\<in>cBasis. \<langle>i, b\<rangle> *\<^sub>C f i) =  \<langle>b, b\<rangle> *\<^sub>C f b + (\<Sum>i\<in>cBasis'. \<langle>i, b\<rangle> *\<^sub>C f i)"
    by (metis (no_types, lifting) c1 c2 complex_finite_cBasis finite_insert sum.insert)
  also have "\<dots> = f b + (\<Sum>i\<in>cBasis'. \<langle>i, b\<rangle> *\<^sub>C f i)"
    by (simp add: b1)
  finally show ?thesis using d1 by simp
qed


lemma sum_cinner_Basis_eq [simp]:
  assumes "b \<in> cBasis" shows "(\<Sum>i\<in>cBasis. \<langle>i, b\<rangle> * f i) = f b"
  by (metis (no_types, lifting) assms complex_scaleC_def sum.cong sum_inner_cBasis_scaleC)

lemma sum_if_cinner [simp]:
  assumes "i \<in> cBasis" "j \<in> cBasis"
  shows "\<langle>(\<Sum>k\<in>cBasis. if k = i then cnj (f i) *\<^sub>C i else cnj (g k) *\<^sub>C k), j\<rangle>
   = (if j=i then f j else g j)"
proof (cases "i=j")
  case True
  with assms show ?thesis
    by (auto simp: cinner_sum_left if_distrib [of "\<lambda>x. \<langle>x, j\<rangle>"] complex_inner_cBasis cong: if_cong)
next
  case False
  have "(\<Sum>k\<in>cBasis. \<langle>(if k = i then cnj (f i) *\<^sub>C i else cnj (g k) *\<^sub>C k), j\<rangle>) =
        (\<Sum>k\<in>cBasis. if k = j then g k else 0)"
    apply (rule sum.cong)
    using False assms by (auto simp: complex_inner_cBasis)
  also have "... = g j"
    using assms by auto
  finally show ?thesis
    using False by (auto simp: cinner_sum_left)
qed

lemma cinner_Pythagoras: "\<parallel>x\<parallel>^2 = (\<Sum>b\<in>cBasis. \<parallel>\<langle>x, b\<rangle>\<parallel>^2)"
proof-
  have a1: "\<langle>x, b\<rangle> *\<^sub>C cnj \<langle>x, b\<rangle> = \<parallel>\<langle>x, b\<rangle>\<parallel>^2" for b
    using complex_norm_square by auto    
  have "\<parallel>x\<parallel>^2 = \<langle>x, x\<rangle>"
    using cpower2_norm_eq_inner by blast
  also have "\<dots> = (\<Sum>b\<in>cBasis. \<langle>x, b\<rangle> *\<^sub>C cnj \<langle>x, b\<rangle>)"
    using complex_euclidean_cinner by auto
  also have "\<dots> = (\<Sum>b\<in>cBasis. \<parallel>\<langle>x, b\<rangle>\<parallel>^2)"
    using a1 by simp
  finally show ?thesis using of_real_eq_iff by blast 
qed

lemma cnorm_le_componentwise:
   "(\<And>b. b \<in> cBasis \<Longrightarrow> \<parallel>\<langle>x, b\<rangle>\<parallel> \<le> \<parallel>\<langle>y, b\<rangle>\<parallel>) \<Longrightarrow> \<parallel>x\<parallel> \<le> \<parallel>y\<parallel>"
proof-
  assume a1: "\<And>b. b \<in> cBasis \<Longrightarrow> \<parallel>\<langle>x, b\<rangle>\<parallel> \<le> \<parallel>\<langle>y, b\<rangle>\<parallel>"
  have "\<parallel>x\<parallel>^2 = (\<Sum>b\<in>cBasis. \<parallel>\<langle>x, b\<rangle>\<parallel>^2)"
    using cinner_Pythagoras by blast    
  moreover have "\<parallel>y\<parallel>^2 = (\<Sum>b\<in>cBasis. \<parallel>\<langle>y, b\<rangle>\<parallel>^2)"
    using cinner_Pythagoras by blast    
  ultimately show ?thesis using a1
    by (metis (no_types, lifting) complex_dot_square_norm complex_norm_le sum_mono) 
qed
  
lemma cBasis_le_norm: "b \<in> cBasis \<Longrightarrow> \<parallel>\<langle>x, b\<rangle>\<parallel> \<le> \<parallel>x\<parallel>"
  by (metis cnorm_cBasis complex_inner_class.Cauchy_Schwarz_ineq mult_cancel_left1)
  
lemma norm_bound_cBasis_le: "b \<in> cBasis \<Longrightarrow> \<parallel>x\<parallel> \<le> e \<Longrightarrow> \<parallel>\<langle>x, b\<rangle>\<parallel> \<le> e"
  by (metis cBasis_le_norm order_trans)

lemma norm_bound_cBasis_lt: "b \<in> cBasis \<Longrightarrow> \<parallel>x\<parallel> < e \<Longrightarrow> \<parallel>\<langle>x, b\<rangle>\<parallel> < e"
  by (metis cBasis_le_norm le_less_trans)

lemma cnorm_le_l1: "\<parallel>x\<parallel> \<le> (\<Sum>b\<in>cBasis. \<parallel>\<langle>x, b\<rangle>\<parallel>)"
  apply (subst complex_euclidean_representation[of x, symmetric])
  apply (rule order_trans[OF norm_sum])
  apply (auto intro!: sum_mono)
  done

(* Ask to Dominique about the generalization to complex number in case such a generalization is
   needed.

lemma sum_norm_allsubsets_bound:
  fixes f :: "'a \<Rightarrow> 'n::euclidean_space"
  assumes fP: "finite P"
    and fPs: "\<And>Q. Q \<subseteq> P \<Longrightarrow> norm (sum f Q) \<le> e"
  shows "(\<Sum>x\<in>P. norm (f x)) \<le> 2 * real DIM('n) * e"

*)

subsection\<^marker>\<open>tag unimportant\<close> \<open>Subclass relationships\<close>

instance complex_euclidean_space \<subseteq> perfect_space
proof
  fix x :: 'a show "\<not> open {x}"
  proof
    assume "open {x}"
    then obtain e where "0 < e" and e: "\<forall>y. dist y x < e \<longrightarrow> y = x"
      unfolding open_dist by fast
    define y where "y = x + scaleC (e/2) (SOME b. b \<in> cBasis)"
    have [simp]: "(SOME b. b \<in> cBasis) \<in> cBasis"
      by (rule someI_ex) (auto simp: ex_in_conv)
    from \<open>0 < e\<close> have "y \<noteq> x"
      unfolding y_def by (auto intro!: cnonzero_cBasis)
    from \<open>0 < e\<close> have "dist y x < e"
      unfolding y_def by (simp add: dist_norm)
    from \<open>y \<noteq> x\<close> and \<open>dist y x < e\<close> show "False"
      using e by simp
  qed
qed

subsection \<open>Class instances\<close>

subsubsection\<^marker>\<open>tag unimportant\<close> \<open>Type \<^typ>\<open>complex\<close>\<close>

instantiation complex :: complex_euclidean_space
begin

definition
  [simp]: "cBasis = {1::complex}"

instance
  by standard auto

end

lemma DIM_real[simp]: "cDIM(complex) = 1"
  by simp

lemma complex_cBasis_1 [iff]: "(1::complex) \<in> cBasis"
  by (simp add: Basis_complex_def)

subsection \<open>Locale instances\<close>

lemma finite_dimensional_vector_space_euclidean:
  "finite_dimensional_vector_space (*\<^sub>C) cBasis"
proof unfold_locales
  show "finite (cBasis::'a set)" by (metis complex_finite_cBasis)
  show "complex_vector.independent (cBasis::'a set)"
  proof-
    have a1: "a \<in> cBasis \<Longrightarrow> u \<in> UNIV \<Longrightarrow>
          \<langle>a, a\<rangle> = \<langle>a, \<Sum>v\<in>cBasis - {a}. u v *\<^sub>C v\<rangle> \<Longrightarrow> False"
      for a::'a and u
    proof-
      assume b1: "a \<in> cBasis" and b2: "u \<in> UNIV" and b3: "\<langle>a, a\<rangle> = \<langle>a, \<Sum>v\<in>cBasis - {a}. u v *\<^sub>C v\<rangle>"
      have c1: "v\<in>cBasis - {a} \<Longrightarrow> \<langle>a, u v *\<^sub>C v\<rangle> = 0" for v
        by (metis DiffD1 DiffD2 b1 cinner_cnj_commute cinner_not_same_cBasis cinner_scaleC_left 
            mult_not_zero singleton_iff)        
      have "\<langle>a, a\<rangle> = (\<Sum>v\<in>cBasis - {a}. \<langle>a, u v *\<^sub>C v\<rangle>)"
        using b3 cinner_sum_right by auto 
      also have "\<dots> = (\<Sum>v\<in>cBasis - {a}. 0)"
        using c1 by auto
      also have "\<dots> = 0"
        by simp
      finally have "\<langle>a, a\<rangle> = 0"
        by blast
      hence "a = 0"
        by auto        
      thus ?thesis using b1 by simp
    qed
    show ?thesis
      unfolding complex_vector.dependent_def dependent_raw_def[symmetric]
      apply (subst complex_vector.span_finite)
       apply simp
      apply clarify
      apply (drule_tac f="cinner a" in arg_cong)
      using a1 by blast
  qed
  show "module.span (*\<^sub>C) cBasis = UNIV"
    unfolding complex_vector.span_finite [OF complex_finite_cBasis] span_raw_def[symmetric]
    by (auto intro!: complex_euclidean_representation[symmetric])
qed

interpretation complex_eucl?: finite_dimensional_vector_space 
  "scaleC :: complex => 'a => 'a::complex_euclidean_space" "cBasis"
  rewrites "module.dependent (*\<^sub>C) = complex_vector.dependent"
    and "module.representation (*\<^sub>C) = complex_vector.representation"
    and "module.subspace (*\<^sub>C) = complex_vector.subspace"
    and "module.span (*\<^sub>C) = complex_vector.span"
    and "vector_space.extend_basis (*\<^sub>C) = complex_vector.extend_basis"
    and "vector_space.dim (*\<^sub>C) = complex_vector.dim"
    and "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) = clinear"
    and "Vector_Spaces.linear (*) (*\<^sub>C) = clinear"
    and "finite_dimensional_vector_space.dimension cBasis = cDIM('a)"
    and "dimension = cDIM('a)"
  apply transfer
  apply (simp add: Complex_Euclidean_Space.finite_dimensional_vector_space_euclidean)
  apply (simp add: Complex_Vector_Spaces.dependent_raw_def)
  apply (simp add: Complex_Vector_Spaces.representation_raw_def)
  apply (simp add: Complex_Vector_Spaces.subspace_raw_def)
  apply (simp add: Complex_Vector_Spaces.span_raw_def)
  apply (simp add: Complex_Vector_Spaces.extend_basis_raw_def)
  apply (simp add: Complex_Vector_Spaces.dim_raw_def)
  proof
  show "Vector_Spaces.linear (*\<^sub>C) (*\<^sub>C) x = clinear x"
    for x :: "'a \<Rightarrow> 'a"
    by (simp add: clinear_def)    
  show "Vector_Spaces.linear (*) ((*\<^sub>C)::complex \<Rightarrow> 'a \<Rightarrow> _) = clinear"
    unfolding clinear_def complex_scaleC_def by blast
  show a1: "finite_dimensional_vector_space.dimension (cBasis::'a set) = card (cBasis::'a set)"
    using finite_dimensional_vector_space.dimension_def[where Basis = cBasis and scale = scaleC]
    by (metis Complex_Euclidean_Space.finite_dimensional_vector_space_euclidean)
  show "finite_dimensional_vector_space.dimension (cBasis::'a set) = card (cBasis::'a set)"
    using a1 by blast
qed

interpretation complex_eucl?: finite_dimensional_vector_space_pair_1
  "scaleC::complex\<Rightarrow>'a::complex_euclidean_space\<Rightarrow>'a" cBasis
  "scaleC::complex \<Rightarrow>'b::complex_vector \<Rightarrow> 'b"
  by unfold_locales

(* Ask to Dominique how to generalize from real to complex 
interpretation eucl?: finite_dimensional_vector_space_prod scaleR scaleR Basis Basis
  rewrites "Basis_pair = Basis"
    and "module_prod.scale *\<^sub>R *\<^sub>R = (scaleR::_\<Rightarrow>_\<Rightarrow>('a \<times> 'b))"
*)


unbundle no_notation_norm

end
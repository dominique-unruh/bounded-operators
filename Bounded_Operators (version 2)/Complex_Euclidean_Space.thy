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

(* Next theorem to translate from real to complex *)

thm sum_if_inner

end
(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)

theory Completion
  imports 
    "HOL-ex.Sketch_and_Explore"
    "HOL.Real_Vector_Spaces"
    NSA_Miscellany

begin


section \<open>Hilbert space pre_completion\<close>

lemma Cauchy_convergent_norm:
  \<open>Cauchy (x::nat \<Rightarrow> 'a::real_normed_vector) \<Longrightarrow> Cauchy (\<lambda> n. norm (x n))\<close>
proof-
  assume \<open>Cauchy x\<close>
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
    (*f* x) N \<approx> (*f* x) M\<close>
    for N M
    by (simp add: Cauchy_NSCauchy NSCauchyD)
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
    hnorm ((*f* x) N) \<approx> hnorm ((*f* x) M)\<close>
    for N M
    by (simp add: approx_hnorm)
  thus \<open>Cauchy (\<lambda> n. norm (x n))\<close>
    by (metis (full_types) NSCauchyI NSCauchy_Cauchy_iff starfun_hnorm)
qed

lemma CauchySEQ_add:
  fixes f g::\<open>nat \<Rightarrow> 'a::real_normed_vector\<close>
  assumes \<open>Cauchy f\<close> and \<open>Cauchy g\<close>
  shows \<open>Cauchy (\<lambda> n. f n + g n)\<close>
proof-
  from \<open>Cauchy f\<close>
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (*f* f) M\<close>
    for N M::hypnat
    using NSCauchy_Cauchy_iff NSCauchy_def by blast
  from \<open>Cauchy g\<close>
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* g) N \<approx> (*f* g) M\<close>
    for N M::hypnat
    using NSCauchy_Cauchy_iff NSCauchy_def by blast
  from \<open>Cauchy f\<close>

  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
         (*f* (\<lambda> n. f n + g n)) N \<approx> (*f*  (\<lambda> n. f n + g n)) M\<close>
    for N M::hypnat
  proof-
    assume \<open>N \<in> HNatInfinite\<close> and \<open>M \<in> HNatInfinite\<close>
    have \<open>(*f* f) N + (*f* g) N \<approx> (*f* f) M + (*f* g) M\<close>
      using \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (*f* f) M\<close>
        \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* g) N \<approx> (*f* g) M\<close>
      using \<open>M \<in> HNatInfinite\<close> \<open>N \<in> HNatInfinite\<close> approx_add by auto      
    moreover have \<open>(*f* (\<lambda> n. f n + g n)) N = (*f* f) N + (*f* g) N\<close>
      by auto
    moreover have \<open>(*f* (\<lambda> n. f n + g n)) M = (*f* f) M + (*f* g) M\<close>
      by auto
    ultimately show \<open>(*f* (\<lambda> n. f n + g n)) N \<approx> (*f*  (\<lambda> n. f n + g n)) M\<close>
      by simp
  qed
  thus \<open>Cauchy (\<lambda> n. f n + g n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed

(* TODO: move *)
lemma lim_leq:
  fixes x y :: \<open>nat \<Rightarrow> real\<close>
  assumes \<open>\<And> n. x n \<le> y n\<close> and \<open>convergent x\<close> and \<open>convergent y\<close>
  shows \<open>lim x \<le> lim y\<close>
  by (metis NSLIMSEQ_le NSconvergent_def assms(1) assms(2) assms(3) convergent_NSconvergent_iff lim_nslim_iff nslimI)

(* TODO: move *)
lemma lim_add:
  fixes x y :: \<open>nat \<Rightarrow> real\<close>
  assumes \<open>convergent x\<close> and \<open>convergent y\<close>
  shows \<open>lim (\<lambda> n. x n + y n) = lim x + lim y\<close>
proof-
  have \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* x) N \<approx> star_of (lim x)\<close>
    for N
    using \<open>convergent x\<close>
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  moreover have \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* y) N \<approx> star_of (lim y)\<close>
    for N
    using \<open>convergent y\<close>
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow>  (*f* x) N + (*f* y) N \<approx> star_of (lim x) + star_of (lim y)\<close>
    for N
    by (simp add: approx_add)
  moreover have \<open>(*f* (\<lambda> n. x n + y n)) N = (*f* x) N + (*f* y) N\<close>
    for N
    by auto
  moreover have \<open>star_of (lim x + lim y) = star_of (lim x) + star_of (lim y)\<close>
    by auto
  ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow>  (*f* (\<lambda> n. x n + y n)) N \<approx> star_of (lim x + lim y)\<close>
    for N
    by simp
  thus ?thesis
    by (simp add: NSLIMSEQ_I lim_nslim_iff nslimI) 
qed

(* TODO: move *)
lemma lim_scaleR:
  fixes x :: \<open>nat \<Rightarrow> real\<close> and r::real
  assumes \<open>convergent x\<close> 
  shows \<open>lim (\<lambda> n. r * x n ) = r * lim x\<close>
proof-
  have \<open>N \<in> HNatInfinite \<Longrightarrow> (*f* x) N \<approx> star_of (lim x)\<close>
    for N
    using \<open>convergent x\<close>
    by (simp add: NSLIMSEQ_D NSconvergent_NSLIMSEQ_iff convergent_NSconvergent_iff lim_nslim_iff)
  hence \<open>N \<in> HNatInfinite \<Longrightarrow>  star_of r * (*f* x) N \<approx> (star_of r) * star_of (lim x) \<close>
    for N
    by (simp add: approx_mult2)
  moreover have \<open> (*f* (\<lambda> n. r * x n)) N = (star_of r) * (*f* x) N\<close>
    for N
    by auto
  moreover have \<open>star_of (r * lim x) = star_of r * star_of (lim x)\<close>
    by auto
  ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow>  (*f* (\<lambda> n. r * x n)) N \<approx> star_of (r * lim x)\<close>
    for N
    by auto
  thus ?thesis
    by (simp add: NSLIMSEQ_I lim_nslim_iff nslimI) 
qed


typedef (overloaded) 'a::real_normed_vector pre_completion
= \<open>{x::nat\<Rightarrow>'a. Cauchy x}\<close>
  proof
  show "(\<lambda>_. 0) \<in> {x. Cauchy x}"
    apply auto
    by (simp add: convergent_Cauchy convergent_const)
qed

setup_lifting type_definition_pre_completion

class pre_dist =
  fixes pre_dist :: "'a \<Rightarrow> 'a \<Rightarrow> real"

class pre_norm =
  fixes pre_norm :: "'a \<Rightarrow> real"


class pre_metric_space = pre_dist +
  assumes pre_dist_eq_0_iff[simp]: "x = y \<longrightarrow> pre_dist x y = 0"
    and pre_dist_triangle2: "pre_dist x y \<le> pre_dist x z + pre_dist y z"
begin

lemma pre_dist_self [simp]: "pre_dist x x = 0"
  by simp

lemma zero_le_pre_dist [simp]: "0 \<le> pre_dist x y"
  using pre_dist_triangle2 [of x x y] by simp

lemma pre_dist_not_less_zero [simp]: "\<not> pre_dist x y < 0"
  by (simp add: not_less)

lemma pre_dist_commute: "pre_dist x y = pre_dist y x"
proof (rule order_antisym)
  show "pre_dist x y \<le> pre_dist y x"
    using pre_dist_triangle2 [of x y x] by simp
  show "pre_dist y x \<le> pre_dist x y"
    using pre_dist_triangle2 [of y x y] by simp
qed

lemma pre_dist_commute_lessI: "pre_dist y x < e \<Longrightarrow> pre_dist x y < e"
  by (simp add: pre_dist_commute)

lemma pre_dist_triangle: "pre_dist x z \<le> pre_dist x y + pre_dist y z"
  using pre_dist_triangle2 [of x z y] by (simp add: pre_dist_commute)

lemma pre_dist_triangle3: "pre_dist x y \<le> pre_dist a x + pre_dist a y"
  using pre_dist_triangle2 [of x y a] by (simp add: pre_dist_commute)

lemma abs_pre_dist_diff_le: "\<bar>pre_dist a b - pre_dist b c\<bar> \<le> pre_dist a c"
  using pre_dist_triangle3[of b c a] pre_dist_triangle2[of a b c] by simp

lemma pre_dist_triangle_le: "pre_dist x z + pre_dist y z \<le> e \<Longrightarrow> pre_dist x y \<le> e"
  by (rule order_trans [OF pre_dist_triangle2])

lemma pre_dist_triangle_lt: "pre_dist x z + pre_dist y z < e \<Longrightarrow> pre_dist x y < e"
  by (rule le_less_trans [OF pre_dist_triangle2])

lemma pre_dist_triangle_less_add: "pre_dist x1 y < e1 \<Longrightarrow> pre_dist x2 y < e2 \<Longrightarrow> pre_dist x1 x2 < e1 + e2"
  by (rule pre_dist_triangle_lt [where z=y]) simp

lemma pre_dist_triangle_half_l: "pre_dist x1 y < e / 2 \<Longrightarrow> pre_dist x2 y < e / 2 \<Longrightarrow> pre_dist x1 x2 < e"
  by (rule pre_dist_triangle_lt [where z=y]) simp

lemma pre_dist_triangle_half_r: "pre_dist y x1 < e / 2 \<Longrightarrow> pre_dist y x2 < e / 2 \<Longrightarrow> pre_dist x1 x2 < e"
  by (rule pre_dist_triangle_half_l) (simp_all add: pre_dist_commute)

lemma pre_dist_triangle_third:
  assumes "pre_dist x1 x2 < e/3" "pre_dist x2 x3 < e/3" "pre_dist x3 x4 < e/3"
  shows "pre_dist x1 x4 < e"
proof -
  have "pre_dist x1 x3 < e/3 + e/3"
    by (metis assms(1) assms(2) pre_dist_commute pre_dist_triangle_less_add)
  then have "pre_dist x1 x4 < (e/3 + e/3) + e/3"
    by (metis assms(3) pre_dist_commute pre_dist_triangle_less_add)
  then show ?thesis
    by simp
qed


end

class pre_real_normed_vector = real_vector + pre_norm +
  assumes pre_norm_eq_zero [simp]: "x = 0 \<longrightarrow> pre_norm x = 0"
    and pre_norm_triangle_ineq: "pre_norm (x + y) \<le> pre_norm x + pre_norm y"
    and pre_norm_scaleR [simp]: "pre_norm (scaleR a x) = \<bar>a\<bar> * pre_norm x"
begin 

end


instantiation pre_completion :: (real_normed_vector) pre_real_normed_vector
begin

lift_definition uminus_pre_completion :: \<open>'a pre_completion \<Rightarrow> 'a pre_completion\<close>
is \<open>\<lambda> x. (\<lambda> n. - (x n))\<close>
  unfolding Cauchy_def
  by (simp add: dist_minus) 

lift_definition zero_pre_completion :: \<open>'a pre_completion\<close>
is \<open>\<lambda> _::nat. 0::'a\<close>
  unfolding Cauchy_def
  by auto

lift_definition  minus_pre_completion ::
  \<open>'a pre_completion \<Rightarrow> 'a pre_completion \<Rightarrow> 'a pre_completion\<close>
  is \<open>\<lambda> x y. (\<lambda> n. x n - y n)\<close>
proof-
  fix f g::\<open>nat \<Rightarrow> 'a\<close>
  assume \<open>Cauchy f\<close> and \<open>Cauchy g\<close>
  from \<open>Cauchy f\<close>
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (*f* f) M\<close>
    for N M::hypnat
    using NSCauchy_Cauchy_iff NSCauchy_def by blast
  from \<open>Cauchy g\<close>
  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* g) N \<approx> (*f* g) M\<close>
    for N M::hypnat
    using NSCauchy_Cauchy_iff NSCauchy_def by blast
  from \<open>Cauchy f\<close>

  have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
         (*f* (\<lambda> n. f n -g n)) N \<approx> (*f*  (\<lambda> n. f n -g n)) M\<close>
    for N M::hypnat
  proof-
    assume \<open>N \<in> HNatInfinite\<close> and \<open>M \<in> HNatInfinite\<close>
    have \<open>(*f* f) N - (*f* g) N \<approx> (*f* f) M - (*f* g) M\<close>
      using \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* f) N \<approx> (*f* f) M\<close>
        \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow> (*f* g) N \<approx> (*f* g) M\<close>
      by (simp add: \<open>M \<in> HNatInfinite\<close> \<open>N \<in> HNatInfinite\<close> approx_diff)
    moreover have \<open>(*f* (\<lambda> n. f n -g n)) N = (*f* f) N - (*f* g) N\<close>
      by auto
    moreover have \<open>(*f* (\<lambda> n. f n -g n)) M = (*f* f) M - (*f* g) M\<close>
      by auto
    ultimately show \<open>(*f* (\<lambda> n. f n -g n)) N \<approx> (*f*  (\<lambda> n. f n -g n)) M\<close>
      by simp
  qed
  thus \<open>Cauchy (\<lambda> n. f n - g n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed

lift_definition  plus_pre_completion ::
  \<open>'a pre_completion \<Rightarrow> 'a pre_completion \<Rightarrow> 'a pre_completion\<close>
  is \<open>\<lambda> x y. (\<lambda> n. x n + y n)\<close>
  by (rule Complex_Inner_Product.CauchySEQ_add)

lift_definition norm_pre_completion :: \<open>'a pre_completion \<Rightarrow> real\<close>
  is \<open>\<lambda> x. lim (\<lambda> n. norm (x n))\<close>.

lift_definition sgn_pre_completion :: \<open>'a pre_completion \<Rightarrow> 'a pre_completion\<close>
  is \<open>\<lambda> x. (\<lambda> n. (x n) /\<^sub>R lim (\<lambda> n. norm (x n)) )\<close>
proof-
  fix x::\<open>nat \<Rightarrow> 'a\<close>
  assume \<open>Cauchy x\<close>
  hence \<open>\<exists> L::real. lim (\<lambda>n. norm (x n)) = L\<close>
    by auto
  then obtain L where \<open>lim (\<lambda>n. norm (x n)) = L\<close>
    by blast
  show \<open>Cauchy (\<lambda>n. x n /\<^sub>R lim (\<lambda>n. norm (x n)))\<close>
  proof (cases \<open>L = 0\<close>)
    show "Cauchy (\<lambda>n. x n /\<^sub>R lim (\<lambda>n. norm (x n)))"
      if "L = 0"
    proof-
      have \<open>(x n) /\<^sub>R L = 0\<close>
        for n
        using that by simp
      hence \<open>(\<lambda>n. (x n) /\<^sub>R L) = (\<lambda> _. 0)\<close>
        by blast
      moreover have \<open>lim (\<lambda> _. 0) = 0\<close>
        by auto
      ultimately have \<open>(\<lambda>n. (x n) /\<^sub>R L) \<longlonglongrightarrow> 0\<close>
        by simp
      hence \<open>convergent (\<lambda>n. (x n) /\<^sub>R L)\<close>
        unfolding convergent_def
        by blast
      thus ?thesis
        using  \<open>lim (\<lambda>n. norm (x n)) = L\<close> LIMSEQ_imp_Cauchy \<open>(\<lambda>n. x n /\<^sub>R L) \<longlonglongrightarrow> 0\<close> by blast
    qed
    show "Cauchy (\<lambda>n. x n /\<^sub>R lim (\<lambda>n. norm (x n)))"
      if "L \<noteq> 0"
    proof-
      have \<open>(\<lambda>n. x n /\<^sub>R lim (\<lambda>n. norm (x n))) = (\<lambda>n. x n /\<^sub>R L)\<close>
        using \<open>lim (\<lambda>n. norm (x n)) = L\<close> by simp
      have \<open>Cauchy (\<lambda>n. x n /\<^sub>R L)\<close>
      proof-
        from \<open>Cauchy x\<close>
        have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
            (*f* x) N \<approx> (*f* x) M\<close>
          for N M
          by (simp add: Cauchy_NSCauchy NSCauchyD)
        hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
         (*f2* scaleR) (inverse (star_of L)) ((*f* x) N) \<approx> (*f2* scaleR) (inverse (star_of L)) ((*f* x) M)\<close>
          for N M
        proof -
          assume a1: "N \<in> HNatInfinite"
          assume "M \<in> HNatInfinite"
          then have "(*f* x) N \<approx> (*f* x) M"
            using a1 by (metis \<open>\<And>N M. \<lbrakk>N \<in> HNatInfinite; M \<in> HNatInfinite\<rbrakk> \<Longrightarrow> (*f* x) N \<approx> (*f* x) M\<close>)
          then show ?thesis
            by (metis (no_types) approx_scaleR2 star_of_inverse star_scaleR_def starfun2_star_of)
        qed
        moreover have \<open>(*f2* scaleR) (inverse (star_of L)) ((*f* x) N) =  (*f* (\<lambda>n. x n /\<^sub>R L)) N\<close>
          for N
          by (metis star_of_inverse starfun2_star_of starfun_o2)
        ultimately have \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
               (*f* (\<lambda>n. x n /\<^sub>R L)) N \<approx> (*f* (\<lambda>n. x n /\<^sub>R L)) M\<close>
          for N M
          by simp
        thus ?thesis
          using NSCauchyI NSCauchy_Cauchy by blast 
      qed
      thus ?thesis
        by (simp add: \<open>lim (\<lambda>n. norm (x n)) = L\<close>)  
    qed
  qed
qed

lift_definition dist_pre_completion :: \<open>'a pre_completion \<Rightarrow> 'a pre_completion \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. lim (\<lambda> n. norm (f n - g n))\<close>.

definition uniformity_pre_completion :: \<open>( 'a pre_completion \<times> 'a pre_completion ) filter\<close>
  where  \<open>uniformity_pre_completion = (INF e:{0<..}. principal {((f:: 'a pre_completion), g). dist f g < e})\<close>

definition open_pre_completion :: \<open>('a pre_completion) set \<Rightarrow> bool\<close>
  where \<open>open_pre_completion 
  = (\<lambda> U::('a pre_completion) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity))\<close>

lift_definition scaleR_pre_completion :: \<open>real \<Rightarrow> 'a pre_completion \<Rightarrow> 'a pre_completion\<close>
is \<open>\<lambda> r x. (\<lambda> n. r *\<^sub>R (x n))\<close>
proof-
  fix r::real and x::\<open>nat \<Rightarrow> 'a\<close>
  assume \<open>Cauchy x\<close>
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
    (*f* x) N \<approx>  (*f* x) M\<close>
    for N M
    by (simp add: NSCauchyD NSCauchy_Cauchy_iff)
  hence \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
     (*f2* scaleR) (star_of r) ((*f* x) N) \<approx> (*f2* scaleR) (star_of r) ((*f* x) M)\<close>
    for N M
    by (metis approx_scaleR2 star_scaleR_def starfun2_star_of)
  moreover have \<open>(*f2* scaleR) (star_of r) ((*f* x) N) = (*f* (\<lambda>n. r *\<^sub>R x n)) N\<close>
    for N
    by auto
  ultimately have  \<open>N \<in> HNatInfinite \<Longrightarrow> M \<in> HNatInfinite \<Longrightarrow>
      (*f* (\<lambda>n. r *\<^sub>R x n)) N \<approx>  (*f* (\<lambda>n. r *\<^sub>R x n)) M\<close>
    for N M
    by simp
  thus \<open>Cauchy (\<lambda>n. r *\<^sub>R x n)\<close>
    by (simp add: NSCauchyI NSCauchy_Cauchy)
qed

instance
  proof
  show "dist (x::'a pre_completion) y = norm (x - y)"
    for x :: "'a pre_completion"
      and y :: "'a pre_completion"
    apply transfer by blast

  show "(a::'a pre_completion) + b + c = a + (b + c)"
    for a :: "'a pre_completion"
      and b :: "'a pre_completion"
      and c :: "'a pre_completion"
    apply transfer by auto

  show "(a::'a pre_completion) + b = b + a"
    for a :: "'a pre_completion"
      and b :: "'a pre_completion"
    apply transfer by auto

  show "(0::'a pre_completion) + a = a"
    for a :: "'a pre_completion"
    apply transfer by auto
  
  show "- (a::'a pre_completion) + a = 0"
    for a :: "'a pre_completion"
    apply transfer by auto

  show "(a::'a pre_completion) - b = a + - b"
    for a :: "'a pre_completion"
      and b :: "'a pre_completion"
    apply transfer by auto

  show "a *\<^sub>R ((x::'a pre_completion) + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real
      and x :: "'a pre_completion"
      and y :: "'a pre_completion"
    apply transfer
    by (simp add: pth_6) 

  show "(a + b) *\<^sub>R (x::'a pre_completion) = a *\<^sub>R x + b *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a pre_completion"
    apply transfer
    by (simp add: ordered_field_class.sign_simps(24)) 

  show "a *\<^sub>R b *\<^sub>R (x::'a pre_completion) = (a * b) *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a pre_completion"
    apply transfer by simp

  show "1 *\<^sub>R (x::'a pre_completion) = x"
    for x :: "'a pre_completion"
    apply transfer by simp

  show "sgn (x::'a pre_completion) = inverse (norm x) *\<^sub>R x"
    for x :: "'a pre_completion"
    apply transfer by auto

  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a pre_completion) y < e})"
    by (simp add: uniformity_pre_completion_def)    

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a pre_completion) = x \<longrightarrow> y \<in> U)"
    for U :: "'a pre_completion set"
    by (simp add: Complex_Inner_Product.open_pre_completion_def)
    
  show "(norm (x::'a pre_completion) = 0) = (x = 0)"
    for x :: "'a pre_completion"
    apply transfer proof
  show "(x::nat \<Rightarrow> 'a) = (\<lambda>_. 0)"
    if "Cauchy (x::nat \<Rightarrow> 'a)"
      and "lim (\<lambda>n. norm (x n::'a)) = 0"
    for x :: "nat \<Rightarrow> 'a"
    using that sorry
      (* false *)

  show "lim (\<lambda>n. norm (x n::'a)) = 0"
    if "Cauchy (x::nat \<Rightarrow> 'a)"
      and "(x::nat \<Rightarrow> 'a) = (\<lambda>_. 0)"
    for x :: "nat \<Rightarrow> 'a"
    using that by auto
qed

  show "norm ((x::'a pre_completion) + y) \<le> norm x + norm y"
    for x :: "'a pre_completion"
      and y :: "'a pre_completion"
  proof transfer
    fix x y :: \<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy x\<close> and \<open>Cauchy y\<close>
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
      using \<open>Cauchy x\<close> \<open>Cauchy y\<close>  Complex_Inner_Product.CauchySEQ_add
      by (simp add: CauchySEQ_add)
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

  show "norm (a *\<^sub>R (x::'a pre_completion)) = \<bar>a\<bar> * norm x"
    for a :: real
      and x :: "'a pre_completion"
    apply transfer
  proof-
    fix a::real and x::\<open>nat \<Rightarrow> 'a\<close>
    assume \<open>Cauchy x\<close>
    hence \<open>convergent (\<lambda> n. norm (x n))\<close>
      using Cauchy_convergent_iff Cauchy_convergent_norm by blast
    moreover have \<open>norm (a *\<^sub>R x n) = \<bar>a\<bar> * norm (x n)\<close>
      for n
      by simp
    ultimately have \<open>lim (\<lambda>n. norm (a *\<^sub>R x n)) =  lim (\<lambda>n. \<bar>a\<bar> * norm (x n))\<close>
      by simp
    also have \<open>lim (\<lambda>n. \<bar>a\<bar> * norm (x n)) = \<bar>a\<bar> * lim (\<lambda>n. norm (x n))\<close>
      using  \<open>convergent (\<lambda> n. norm (x n))\<close> 
      sorry
    finally show  \<open>lim (\<lambda>n. norm (a *\<^sub>R x n)) = \<bar>a\<bar> * lim (\<lambda>n. norm (x n))\<close>
      by blast
  qed
qed

end

section \<open>Commutative monoid of subspaces\<close>

instantiation linear_space :: (chilbert_space) comm_monoid_add begin
definition zero_linear_space :: "'a linear_space" where [simp]: "zero_linear_space = bot"
definition plus_linear_space :: "'a linear_space \<Rightarrow> _ \<Rightarrow> _" where [simp]: "plus_linear_space = sup"
instance 
  apply standard 
    apply (simp add: sup_assoc)
   apply (simp add: sup_commute)
  by simp
end


end
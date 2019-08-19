(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee
*)

theory Completion
  imports 
    Complex_Inner_Product

begin

section \<open>Pseudometric space\<close>

class pseudo_dist =
  fixes pseudo_dist :: "'a \<Rightarrow> 'a \<Rightarrow> real"

class pseudo_norm =
  fixes pseudo_norm :: "'a \<Rightarrow> real"


class pseudo_metric_space = pseudo_dist +
  assumes pseudo_dist_eq_0_iff[simp]: "x = y \<longrightarrow> pseudo_dist x y = 0"
    and pseudo_dist_triangle2: "pseudo_dist x y \<le> pseudo_dist x z + pseudo_dist y z"
begin

lemma pseudo_dist_self [simp]: "pseudo_dist x x = 0"
  by simp

lemma zero_le_pseudo_dist [simp]: "0 \<le> pseudo_dist x y"
  using pseudo_dist_triangle2 [of x x y] by simp

lemma pseudo_dist_not_less_zero [simp]: "\<not> pseudo_dist x y < 0"
  by (simp add: not_less)

lemma pseudo_dist_commute: "pseudo_dist x y = pseudo_dist y x"
proof (rule order_antisym)
  show "pseudo_dist x y \<le> pseudo_dist y x"
    using pseudo_dist_triangle2 [of x y x] by simp
  show "pseudo_dist y x \<le> pseudo_dist x y"
    using pseudo_dist_triangle2 [of y x y] by simp
qed

lemma pseudo_dist_commute_lessI: "pseudo_dist y x < e \<Longrightarrow> pseudo_dist x y < e"
  by (simp add: pseudo_dist_commute)

lemma pseudo_dist_triangle: "pseudo_dist x z \<le> pseudo_dist x y + pseudo_dist y z"
  using pseudo_dist_triangle2 [of x z y] by (simp add: pseudo_dist_commute)

lemma pseudo_dist_triangle3: "pseudo_dist x y \<le> pseudo_dist a x + pseudo_dist a y"
  using pseudo_dist_triangle2 [of x y a] by (simp add: pseudo_dist_commute)

lemma abs_pseudo_dist_diff_le: "\<bar>pseudo_dist a b - pseudo_dist b c\<bar> \<le> pseudo_dist a c"
  using pseudo_dist_triangle3[of b c a] pseudo_dist_triangle2[of a b c] by simp

lemma pseudo_dist_triangle_le: "pseudo_dist x z + pseudo_dist y z \<le> e \<Longrightarrow> pseudo_dist x y \<le> e"
  by (rule order_trans [OF pseudo_dist_triangle2])

lemma pseudo_dist_triangle_lt: "pseudo_dist x z + pseudo_dist y z < e \<Longrightarrow> pseudo_dist x y < e"
  by (rule le_less_trans [OF pseudo_dist_triangle2])

lemma pseudo_dist_triangle_less_add: "pseudo_dist x1 y < e1 \<Longrightarrow> pseudo_dist x2 y < e2 \<Longrightarrow> pseudo_dist x1 x2 < e1 + e2"
  by (rule pseudo_dist_triangle_lt [where z=y]) simp

lemma pseudo_dist_triangle_half_l: "pseudo_dist x1 y < e / 2 \<Longrightarrow> pseudo_dist x2 y < e / 2 \<Longrightarrow> pseudo_dist x1 x2 < e"
  by (rule pseudo_dist_triangle_lt [where z=y]) simp

lemma pseudo_dist_triangle_half_r: "pseudo_dist y x1 < e / 2 \<Longrightarrow> pseudo_dist y x2 < e / 2 \<Longrightarrow> pseudo_dist x1 x2 < e"
  by (rule pseudo_dist_triangle_half_l) (simp_all add: pseudo_dist_commute)

lemma pseudo_dist_triangle_third:
  assumes "pseudo_dist x1 x2 < e/3" "pseudo_dist x2 x3 < e/3" "pseudo_dist x3 x4 < e/3"
  shows "pseudo_dist x1 x4 < e"
proof -
  have "pseudo_dist x1 x3 < e/3 + e/3"
    by (metis assms(1) assms(2) pseudo_dist_commute pseudo_dist_triangle_less_add)
  then have "pseudo_dist x1 x4 < (e/3 + e/3) + e/3"
    by (metis assms(3) pseudo_dist_commute pseudo_dist_triangle_less_add)
  then show ?thesis
    by simp
qed


end

class pseudo_real_normed_vector = real_vector + pseudo_norm +
  assumes pseudo_norm_eq_zero [simp]: "x = 0 \<longrightarrow> pseudo_norm x = 0"
    and pseudo_norm_triangle_ineq: "pseudo_norm (x + y) \<le> pseudo_norm x + pseudo_norm y"
    and pseudo_norm_scaleR [simp]: "pseudo_norm (scaleR a x) = \<bar>a\<bar> * pseudo_norm x"
begin 

end



section \<open>Hilbert space pseudo_completion\<close>

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


typedef (overloaded) 'a::real_normed_vector pseudo_completion
= \<open>{x::nat\<Rightarrow>'a. Cauchy x}\<close>
  proof
  show "(\<lambda>_. 0) \<in> {x. Cauchy x}"
    apply auto
    by (simp add: convergent_Cauchy convergent_const)
qed

setup_lifting type_definition_pseudo_completion


instantiation pseudo_completion :: (real_normed_vector) pseudo_real_normed_vector
begin

lift_definition uminus_pseudo_completion :: \<open>'a pseudo_completion \<Rightarrow> 'a pseudo_completion\<close>
is \<open>\<lambda> x. (\<lambda> n. - (x n))\<close>
  unfolding Cauchy_def
  by (simp add: dist_minus) 

lift_definition zero_pseudo_completion :: \<open>'a pseudo_completion\<close>
is \<open>\<lambda> _::nat. 0::'a\<close>
  unfolding Cauchy_def
  by auto

lift_definition  minus_pseudo_completion ::
  \<open>'a pseudo_completion \<Rightarrow> 'a pseudo_completion \<Rightarrow> 'a pseudo_completion\<close>
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

lift_definition  plus_pseudo_completion ::
  \<open>'a pseudo_completion \<Rightarrow> 'a pseudo_completion \<Rightarrow> 'a pseudo_completion\<close>
  is \<open>\<lambda> x y. (\<lambda> n. x n + y n)\<close>
  by (rule Complex_Inner_Product.CauchySEQ_add)

lift_definition norm_pseudo_completion :: \<open>'a pseudo_completion \<Rightarrow> real\<close>
  is \<open>\<lambda> x. lim (\<lambda> n. norm (x n))\<close>.

lift_definition sgn_pseudo_completion :: \<open>'a pseudo_completion \<Rightarrow> 'a pseudo_completion\<close>
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

lift_definition dist_pseudo_completion :: \<open>'a pseudo_completion \<Rightarrow> 'a pseudo_completion \<Rightarrow> real\<close>
  is \<open>\<lambda> f g. lim (\<lambda> n. norm (f n - g n))\<close>.

definition uniformity_pseudo_completion :: \<open>( 'a pseudo_completion \<times> 'a pseudo_completion ) filter\<close>
  where  \<open>uniformity_pseudo_completion = (INF e:{0<..}. principal {((f:: 'a pseudo_completion), g). dist f g < e})\<close>

definition open_pseudo_completion :: \<open>('a pseudo_completion) set \<Rightarrow> bool\<close>
  where \<open>open_pseudo_completion 
  = (\<lambda> U::('a pseudo_completion) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity))\<close>

lift_definition scaleR_pseudo_completion :: \<open>real \<Rightarrow> 'a pseudo_completion \<Rightarrow> 'a pseudo_completion\<close>
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
  show "dist (x::'a pseudo_completion) y = norm (x - y)"
    for x :: "'a pseudo_completion"
      and y :: "'a pseudo_completion"
    apply transfer by blast

  show "(a::'a pseudo_completion) + b + c = a + (b + c)"
    for a :: "'a pseudo_completion"
      and b :: "'a pseudo_completion"
      and c :: "'a pseudo_completion"
    apply transfer by auto

  show "(a::'a pseudo_completion) + b = b + a"
    for a :: "'a pseudo_completion"
      and b :: "'a pseudo_completion"
    apply transfer by auto

  show "(0::'a pseudo_completion) + a = a"
    for a :: "'a pseudo_completion"
    apply transfer by auto
  
  show "- (a::'a pseudo_completion) + a = 0"
    for a :: "'a pseudo_completion"
    apply transfer by auto

  show "(a::'a pseudo_completion) - b = a + - b"
    for a :: "'a pseudo_completion"
      and b :: "'a pseudo_completion"
    apply transfer by auto

  show "a *\<^sub>R ((x::'a pseudo_completion) + y) = a *\<^sub>R x + a *\<^sub>R y"
    for a :: real
      and x :: "'a pseudo_completion"
      and y :: "'a pseudo_completion"
    apply transfer
    by (simp add: pth_6) 

  show "(a + b) *\<^sub>R (x::'a pseudo_completion) = a *\<^sub>R x + b *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a pseudo_completion"
    apply transfer
    by (simp add: ordered_field_class.sign_simps(24)) 

  show "a *\<^sub>R b *\<^sub>R (x::'a pseudo_completion) = (a * b) *\<^sub>R x"
    for a :: real
      and b :: real
      and x :: "'a pseudo_completion"
    apply transfer by simp

  show "1 *\<^sub>R (x::'a pseudo_completion) = x"
    for x :: "'a pseudo_completion"
    apply transfer by simp

  show "sgn (x::'a pseudo_completion) = inverse (norm x) *\<^sub>R x"
    for x :: "'a pseudo_completion"
    apply transfer by auto

  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a pseudo_completion) y < e})"
    by (simp add: uniformity_pseudo_completion_def)    

  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a pseudo_completion) = x \<longrightarrow> y \<in> U)"
    for U :: "'a pseudo_completion set"
    by (simp add: Complex_Inner_Product.open_pseudo_completion_def)
    
  show "(norm (x::'a pseudo_completion) = 0) = (x = 0)"
    for x :: "'a pseudo_completion"
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

  show "norm ((x::'a pseudo_completion) + y) \<le> norm x + norm y"
    for x :: "'a pseudo_completion"
      and y :: "'a pseudo_completion"
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

  show "norm (a *\<^sub>R (x::'a pseudo_completion)) = \<bar>a\<bar> * norm x"
    for a :: real
      and x :: "'a pseudo_completion"
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
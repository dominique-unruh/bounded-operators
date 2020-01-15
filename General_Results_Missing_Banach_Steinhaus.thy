section \<open>General results missing, which are needed for the proof of Banach-Steinhaus theorem\<close>

theory General_Results_Missing_Banach_Steinhaus
  imports Complex_Main 

begin

lemma sum_interval_split: 
  fixes f :: "nat \<Rightarrow> 'a::ab_group_add" and a b :: nat
  assumes "b>a" 
  shows "sum f {Suc a..b} = sum f {..b} - sum f {..a}" 
proof -
  obtain c where c: "b = a+c"
    using \<open>a < b\<close> less_imp_add_positive by blast
  show ?thesis
    unfolding c sum_up_index_split
    by auto 
qed

class not_singleton =
  assumes not_singleton_card: "\<exists>x. \<exists>y. x \<noteq> y"

lemma not_singleton_existence[simp]:
  \<open>\<exists> x::('a::not_singleton). x \<noteq> t\<close>
proof (rule classical)
  assume \<open>\<nexists>x. (x::'a) \<noteq> t\<close> 
  have \<open>\<exists> x::'a. \<exists> y::'a. x \<noteq> y\<close>
    using not_singleton_card
    by blast
  then obtain x y::'a where \<open>x \<noteq> y\<close>
    by blast
  have \<open>\<forall> x::'a. x = t\<close>
    using \<open>\<nexists>x. (x::'a) \<noteq> t\<close> by simp
  hence \<open>x = t\<close>
    by blast
  moreover have \<open>y = t\<close>
    using \<open>\<forall> x::'a. x = t\<close>
    by blast
  ultimately have \<open>x = y\<close>
    by simp
  thus ?thesis using \<open>x \<noteq> y\<close> by blast
qed

lemma UNIV_not_singleton[simp]: "(UNIV::_::not_singleton set) \<noteq> {x}"
  using not_singleton_existence[of x] by blast

lemma UNIV_not_singleton_converse: "(\<And> x. (UNIV::'a set) \<noteq> {x}) \<Longrightarrow> \<exists>x::'a. \<exists>y::'a. x \<noteq> y"
  by fastforce

lemma UNIV_not_singleton_converse_zero: "((UNIV::('a::real_normed_vector) set) \<noteq> {0}) \<Longrightarrow> \<exists>x::'a. \<exists>y::'a. x \<noteq> y"
  using UNIV_not_singleton_converse
  by fastforce 


end
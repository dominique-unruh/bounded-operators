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

end
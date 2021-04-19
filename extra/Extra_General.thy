section \<open>General missing things\<close>

theory Extra_General
  imports "HOL-Library.Cardinality"
begin

subsection \<open>Not singleton\<close>

class not_singleton =
  assumes not_singleton_card: "\<exists>x y. x \<noteq> y"

lemma not_singleton_existence[simp]:
  \<open>\<exists> x::('a::not_singleton). x \<noteq> t\<close>
proof (rule ccontr)
  assume \<open>\<nexists>x::'a. x \<noteq> t\<close> 
  have \<open>\<exists>x::'a. \<exists>y. x \<noteq> y\<close>
    using not_singleton_card
    by blast
  then obtain x y::'a where \<open>x \<noteq> y\<close>
    by blast
  have \<open>\<forall>x::'a. x = t\<close>
    using \<open>\<nexists>x::'a. x \<noteq> t\<close> by simp
  hence \<open>x = t\<close>
    by blast
  moreover have \<open>y = t\<close>
    using \<open>\<forall>x::'a. x = t\<close>
    by blast
  ultimately have \<open>x = y\<close>
    by simp
  thus False
    using \<open>x \<noteq> y\<close> by auto 
qed

lemma UNIV_not_singleton[simp]: "(UNIV::_::not_singleton set) \<noteq> {x}"
  using not_singleton_existence[of x] by blast

lemma UNIV_not_singleton_converse: 
  assumes"\<And>x::'a. UNIV \<noteq> {x}"
  shows "\<exists>x::'a. \<exists>y. x \<noteq> y"
  using assms
  by fastforce 

(* lemma UNIV_not_singleton_converse_zero: 
  assumes "UNIV \<noteq> {0::'a::real_normed_vector}"
  shows "\<exists>x::'a. \<exists>y. x \<noteq> y"
  using UNIV_not_singleton_converse assms
  by fastforce  *)

subclass (in card2) not_singleton
  apply standard using two_le_card
  by (meson card_2_iff' obtain_subset_with_card_n)


subsection \<open>CARD_1\<close>

context CARD_1 begin

lemma everything_the_same[simp]: "(x::'a)=y"
  by (metis (full_types) UNIV_I card_1_singletonE empty_iff insert_iff local.CARD_1)

lemma CARD_1_UNIV: "UNIV = {x::'a}"
  by (metis (full_types) UNIV_I card_1_singletonE local.CARD_1 singletonD)

lemma CARD_1_ext: "x (a::'a) = y b \<Longrightarrow> x = y"
proof (rule ext)
  show "x t = y t"
    if "x a = y b"
    for t :: 'a
    using that  apply (subst (asm) everything_the_same[where x=a])
    apply (subst (asm) everything_the_same[where x=b])
    by simp
qed 

end

end

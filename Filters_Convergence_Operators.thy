(*
Authors: 

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

Generalization of Convergence_Operators.thy via filters.

*)

theory Filters_Convergence_Operators
  imports 
    Convergence_Operators

begin

definition nhds_ustrong:: \<open>('a::real_normed_vector\<Rightarrow>'b::real_normed_vector) \<Rightarrow> ('a\<Rightarrow>'b) filter\<close>
  where \<open>nhds_ustrong l =
 (INF e \<in> {(0::real)<..}. principal {f. \<forall> x. norm x = 1 \<longrightarrow> norm (f x - l x) < e })\<close>

lemma ustrong_convergence_topo:
  assumes \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
  shows \<open>filterlim f (nhds_ustrong l) sequentially\<close>
proof-
  have \<open>Abs_filter (\<lambda>P. \<forall>\<^sub>F x in sequentially. P (f x))
    \<le> (INF e\<in>{0<..}. 
  principal {f. \<forall>x. norm x = 1 \<longrightarrow> norm (f x - l x) < e})\<close>
    sorry    
  thus ?thesis unfolding filterlim_def filtermap_def nhds_ustrong_def
    by blast
qed

lemma convergence_topo_ustrong:
  assumes \<open>filterlim f (nhds_ustrong l) sequentially\<close> 
  shows \<open>f \<midarrow>ustrong\<rightarrow> l\<close>
  sorry

proposition ustrong_convergence_topo_iff:
  \<open>( f \<midarrow>ustrong\<rightarrow> l ) \<longleftrightarrow> ( filterlim f (nhds_ustrong l) sequentially )\<close>
  using convergence_topo_ustrong ustrong_convergence_topo by auto  



end

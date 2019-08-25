(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Free_Vector_Spaces
  imports Complex_Inner_Product "HOL-Library.Adhoc_Overloading"

begin

typedef 'a free = \<open>{f::'a \<Rightarrow> complex. finite {x | x. f x \<noteq> 0}}\<close>
  apply auto
  using not_finite_existsD by fastforce

setup_lifting type_definition_free

instantiation free :: (type) complex_vector
begin

lift_definition zero_free :: "'a free"
  is \<open>\<lambda> _. 0\<close>
  by auto

lift_definition scaleC_free :: "complex \<Rightarrow> 'a free \<Rightarrow> 'a free"
  is \<open>\<lambda> c::complex. \<lambda> f::'a\<Rightarrow>complex. (\<lambda> x. c *\<^sub>C (f x))\<close>
  by auto

lift_definition scaleR_free :: "real \<Rightarrow> 'a free \<Rightarrow> 'a free"
  is \<open>\<lambda> c::real. \<lambda> f::'a\<Rightarrow>complex. (\<lambda> x. c *\<^sub>C (f x))\<close>
  by auto

lift_definition uminus_free :: "'a free \<Rightarrow> 'a free"
  is \<open>\<lambda> f::'a\<Rightarrow>complex. (\<lambda> x. - (f x))\<close>
  by auto

lift_definition plus_free :: "'a free \<Rightarrow> 'a free \<Rightarrow> 'a free"
  is \<open>\<lambda> f g ::'a\<Rightarrow>complex. (\<lambda> x. f x + g x)\<close>
proof-
  fix f1 f2 :: \<open>'a \<Rightarrow> complex\<close>
  assume \<open>finite {x |x. f1 x \<noteq> 0}\<close> and \<open>finite {x |x. f2 x \<noteq> 0}\<close> 
  moreover have \<open>{x |x. f1 x + f2 x \<noteq> 0} \<subseteq> {x |x. f1 x \<noteq> 0} \<union> {x |x. f2 x \<noteq> 0}\<close>
  proof-
    have \<open>{x |x. f1 x = 0} \<inter> {x |x. f2 x = 0} \<subseteq> {x |x. f1 x + f2 x = 0}\<close>
      by (simp add: Collect_mono_iff Int_def)
    thus ?thesis
      by auto 
  qed
  ultimately show \<open>finite {x |x. f1 x + f2 x \<noteq> 0}\<close>
    by (simp add: finite_subset)
qed

lift_definition minus_free :: "'a free \<Rightarrow> 'a free \<Rightarrow> 'a free"
  is \<open>\<lambda> f g ::'a\<Rightarrow>complex. (\<lambda> x. f x - g x)\<close>
proof-
  fix f1 f2 :: \<open>'a \<Rightarrow> complex\<close>
  assume \<open>finite {x |x. f1 x \<noteq> 0}\<close> and \<open>finite {x |x. f2 x \<noteq> 0}\<close> 
  moreover have \<open>{x |x. f1 x - f2 x \<noteq> 0} \<subseteq> {x |x. f1 x \<noteq> 0} \<union> {x |x. f2 x \<noteq> 0}\<close>
  proof-
    have \<open>{x |x. f1 x = 0} \<inter> {x |x. f2 x = 0} \<subseteq> {x |x. f1 x - f2 x = 0}\<close>
      by (simp add: Collect_mono_iff Int_def)
    thus ?thesis
      by auto 
  qed
  ultimately show \<open>finite {x |x. f1 x - f2 x \<noteq> 0}\<close>
    by (simp add: finite_subset)
qed


instance
proof
  show "((*\<^sub>R) r::'a free \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
    unfolding scaleR_free_def scaleC_free_def by auto
  show "(a::'a free) + b + c = a + (b + c)"
    for a :: "'a free"
      and b :: "'a free"
      and c :: "'a free"
    apply transfer
    by (simp add: add.commute add.left_commute)
  show "(a::'a free) + b = b + a"
    for a :: "'a free"
      and b :: "'a free"
    apply transfer
    by (simp add: add.commute) 
  show "(0::'a free) + a = a"
    for a :: "'a free"
    apply transfer by auto
  show "- (a::'a free) + a = 0"
    for a :: "'a free"
    apply transfer by auto
  show "(a::'a free) - b = a + - b"
    for a :: "'a free"
      and b :: "'a free"
    apply transfer by auto
  show "a *\<^sub>C ((x::'a free) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a free"
      and y :: "'a free"
    apply transfer
    using scaleC_add_right by blast 
  show "(a + b) *\<^sub>C (x::'a free) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a free"
    apply transfer
    using scaleC_add_left by blast 
  show "a *\<^sub>C b *\<^sub>C (x::'a free) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a free"
    apply transfer by auto
  show "1 *\<^sub>C (x::'a free) = x"
    for x :: "'a free"
    apply transfer by auto
qed
end

lift_definition inclusion_free:: \<open>'a \<Rightarrow> 'a free\<close>
  is \<open>\<lambda> a::'a. (\<lambda> x. if x = a then 1 else 0)\<close>
  by simp

definition clinear_iso::\<open>('a::complex_vector \<Rightarrow> 'b::complex_vector) \<Rightarrow> bool\<close> where
  \<open>clinear_iso f = ( clinear f \<and> (\<exists> g::'b\<Rightarrow>'a. clinear g \<and> f \<circ> g = id \<and> g \<circ> f = id )  ) \<close>

lemma clinear_iso_bij_I:
 \<open>clinear f \<Longrightarrow> bij f \<Longrightarrow> clinear_iso f\<close>
  unfolding clinear_iso_def
  by (meson bij_clinear_imp_inv_clinear bij_is_inj bij_is_surj inv_o_cancel surj_iff)

lemma clinear_iso_bij_D1:
 \<open>clinear_iso f \<Longrightarrow> bij f\<close>
  unfolding clinear_iso_def
  using o_bij by auto  

lemma clinear_iso_bij_D2:
 \<open>clinear_iso f \<Longrightarrow> clinear f\<close>
  unfolding clinear_iso_def by blast

lemma clinear_iso_bij_iff:
 \<open>clinear_iso f \<longleftrightarrow> clinear f \<and> bij f\<close>
  proof
  show "clinear f \<and> bij f"
    if "clinear_iso f"
    using that
    by (simp add: clinear_iso_bij_D1 clinear_iso_bij_D2) 
  show "clinear_iso f"
    if "clinear f \<and> bij f"
    using that
    by (simp add: clinear_iso_bij_I) 
qed

text\<open>A type TYPE('a) is a free vector space over the type TYPE('b) if and only if ...\<close>
definition is_free_over::\<open>('a::complex_vector) itself \<Rightarrow> 'b itself \<Rightarrow> bool\<close> where
  \<open>is_free_over (TYPE('a)) (TYPE('b)) = (\<exists> f :: 'a \<Rightarrow> 'b free. clinear_iso f)\<close>

lemma free_regular_for_sum:
  fixes x y :: \<open>'a free\<close>
  shows \<open>Rep_free (x + y) t = Rep_free x t + Rep_free y t\<close>
  apply transfer
  by auto


lemma free_regular_for_sum_general_induction:
  fixes x :: \<open>'a free\<close>
  shows \<open>\<forall> S. finite S \<and> card S = n \<longrightarrow> Rep_free ( \<Sum> u \<in> S. ((Rep_free x) u) *\<^sub>C (inclusion_free u) ) t
  = (\<Sum> u \<in> S. Rep_free ( ((Rep_free x) u) *\<^sub>C (inclusion_free u) ) t )\<close>
proof (induction n)
  show "\<forall>S. finite S \<and> card S = 0 \<longrightarrow> Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C inclusion_free u) t = (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C inclusion_free u) t)"
    by (metis (no_types, lifting) card_0_eq sum_clauses(1) zero_free.rep_eq)
  show "\<forall>S. finite S \<and> card S = Suc n \<longrightarrow> Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C inclusion_free u) t = (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C inclusion_free u) t)"
    if "\<forall>S. finite S \<and> card S = n \<longrightarrow> Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C inclusion_free u) t = (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C inclusion_free u) t)"
    for n :: nat
  proof-
    have \<open>finite S \<Longrightarrow> card S = Suc n \<Longrightarrow> Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C inclusion_free u) t = (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C inclusion_free u) t)\<close>
      for S
    proof-
      fix S::\<open>'a set\<close>
      assume \<open>finite S\<close> and \<open>card S = Suc n\<close>
      hence \<open>\<exists> R r. S = insert r R \<and> r \<notin> R\<close>
        by (meson card_Suc_eq)
      then obtain R r where \<open>S = insert r R\<close> and \<open>r \<notin> R\<close>
        by blast
      have \<open>finite R\<close>
        using \<open>finite S\<close> \<open>S = insert r R\<close>
        by simp
      moreover have \<open>card R = n\<close>
        using \<open>card S = Suc n\<close> \<open>S = insert r R\<close>  \<open>r \<notin> R\<close> \<open>finite R\<close> by auto
      ultimately have \<open>Rep_free (\<Sum>u\<in>R. Rep_free x u *\<^sub>C inclusion_free u) t = (\<Sum>u\<in>R. Rep_free (Rep_free x u *\<^sub>C inclusion_free u) t)\<close>
        by (simp add: that)
      hence \<open>Rep_free (\<Sum>u\<in>R. Rep_free x u *\<^sub>C inclusion_free u) t + Rep_free (Rep_free x r *\<^sub>C inclusion_free r) t
         = (\<Sum>u\<in>R. Rep_free (Rep_free x u *\<^sub>C inclusion_free u) t) + Rep_free (Rep_free x r *\<^sub>C inclusion_free r) t\<close>
        by simp
      moreover have \<open>Rep_free (\<Sum>u\<in>R. Rep_free x u *\<^sub>C inclusion_free u) t + Rep_free (Rep_free x r *\<^sub>C inclusion_free r) t
          = Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C inclusion_free u) t\<close>
        by (simp add: \<open>S = insert r R\<close> \<open>finite R\<close> \<open>r \<notin> R\<close> plus_free.rep_eq)        
      moreover have \<open>(\<Sum>u\<in>R. Rep_free (Rep_free x u *\<^sub>C inclusion_free u) t) + Rep_free (Rep_free x r *\<^sub>C inclusion_free r) t
          =  (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C inclusion_free u) t)\<close>
        by (simp add: \<open>S = insert r R\<close> \<open>finite R\<close> \<open>r \<notin> R\<close>)        
      ultimately show \<open>Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C inclusion_free u) t = (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C inclusion_free u) t)\<close>
        by simp
    qed
    thus ?thesis by blast
  qed
qed


lemma free_regular_for_sum_general:
  fixes x :: \<open>'a free\<close>
  assumes \<open>finite S\<close>
  shows \<open>Rep_free ( \<Sum> u \<in> S. ((Rep_free x) u) *\<^sub>C (inclusion_free u) ) t
  = (\<Sum> u \<in> S. Rep_free ( ((Rep_free x) u) *\<^sub>C (inclusion_free u) ) t )\<close>
  using free_regular_for_sum_general_induction assms
  by (simp add: free_regular_for_sum_general_induction) 

lemma free_pair_explicit:
  fixes X :: \<open>'a free\<close>
  shows \<open>X = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (inclusion_free z))\<close>
proof-
  have \<open>(Rep_free X) t = (Rep_free (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (inclusion_free z))) t\<close>
    for t
  proof (cases \<open>t \<in> {u | u. (Rep_free X) u \<noteq> 0}\<close>)
    show "Rep_free X t = Rep_free (\<Sum>z\<in>{u |u. Rep_free X u \<noteq> 0}. Rep_free X z *\<^sub>C inclusion_free z) t"
      if "t \<in> {u |u. Rep_free X u \<noteq> 0}"
    proof-
      have \<open>finite {u | u. (Rep_free X) u \<noteq> 0}\<close>
        using Rep_free by force
      hence \<open>(Rep_free (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (inclusion_free z))) t
        = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t ) \<close>
        using free_regular_for_sum_general[where S = "{u | u. (Rep_free X) u \<noteq> 0}" and x = "X" and t = "t"]
        by blast
      moreover have \<open>(\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t ) = Rep_free X t\<close>
      proof-
        have \<open>(\<Sum>z\<in>{t}. Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t ) = Rep_free X t\<close>
        proof-
          have \<open>(\<Sum>z\<in>{t}. Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t )
            = Rep_free ( ((Rep_free X) t) *\<^sub>C (inclusion_free t) ) t \<close>
            by simp
          also have \<open>\<dots> = (Rep_free X) t\<close>
            apply transfer
            by auto
          finally show ?thesis by blast
        qed
        moreover have \<open>(\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0} - {t}. Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t ) = 0\<close>
        proof-
          have \<open>z\<in>{u | u. (Rep_free X) u \<noteq> 0} - {t} \<Longrightarrow> 
                Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t  = 0\<close>
            for z
          proof-
            assume \<open>z\<in>{u | u. (Rep_free X) u \<noteq> 0} - {t}\<close>
            hence \<open>z \<noteq> t\<close>
              by simp
            hence \<open>Rep_free (inclusion_free z) t = 0\<close>
              apply transfer by auto
            thus \<open>Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t  = 0\<close>
              by (simp add: scaleC_free.rep_eq)
          qed
          thus ?thesis by simp
        qed
        moreover have \<open>(\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t )
      = (\<Sum>z\<in>{t}. Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t )
      + (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0} - {t}. Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t )\<close>
          using \<open>finite {u |u. Rep_free X u \<noteq> 0}\<close> empty_iff sum.remove that by fastforce        
        ultimately show ?thesis by simp
      qed
      ultimately show \<open>(Rep_free X) t = (Rep_free (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (inclusion_free z))) t\<close>
        by simp      
    qed
    show "Rep_free X t = Rep_free (\<Sum>z\<in>{u |u. Rep_free X u \<noteq> 0}. Rep_free X z *\<^sub>C inclusion_free z) t"
      if "t \<notin> {u |u. Rep_free X u \<noteq> 0}"
    proof-
      have \<open>Rep_free X t = 0\<close>
        using that by simp
      moreover have \<open>Rep_free (\<Sum>z\<in>{u |u. Rep_free X u \<noteq> 0}. Rep_free X z *\<^sub>C inclusion_free z) t = 0\<close>
      proof-
        have \<open>(Rep_free (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (inclusion_free z))) t
        = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t ) \<close>
          using free_regular_for_sum_general[where S = "{u | u. (Rep_free X) u \<noteq> 0}" and x = "X" and t = "t"]
          by (metis (no_types, lifting) sum.infinite zero_free.rep_eq)
        also have \<open>\<dots> = 0\<close>
        proof-
          have \<open>z\<in>{u | u. (Rep_free X) u \<noteq> 0} \<Longrightarrow> Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t = 0\<close>
            for z
          proof-
            assume \<open>z\<in>{u | u. (Rep_free X) u \<noteq> 0}\<close>
            hence \<open>Rep_free (inclusion_free z) t = 0\<close>
              by (metis inclusion_free.rep_eq that)          
            thus \<open>Rep_free ( ((Rep_free X) z) *\<^sub>C (inclusion_free z) ) t = 0\<close>
              by (simp add: scaleC_free.rep_eq) 
          qed
          thus ?thesis by simp
        qed
        finally show ?thesis by blast
      qed
      ultimately show ?thesis by simp
    qed
  qed
  thus \<open>X = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (inclusion_free z))\<close>
    using Rep_free_inject by blast
qed

lemma free_span:
\<open>complex_vector.span (range inclusion_free) = UNIV\<close>
  proof
  show "complex_vector.span (range inclusion_free) \<subseteq> (UNIV::'a free set)"
    by simp    
  show "(UNIV::'a free set) \<subseteq> complex_vector.span (range inclusion_free)"
    proof
  show "(x::'a free) \<in> complex_vector.span (range inclusion_free)"
    if "(x::'a free) \<in> UNIV"
    for x :: "'a free"
  proof-
    have \<open>x = (\<Sum>z\<in>{u | u. (Rep_free x) u \<noteq> 0}. ((Rep_free x) z) *\<^sub>C (inclusion_free z))\<close>
      using free_pair_explicit by blast
    thus ?thesis
      by (metis (no_types, lifting) complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset rangeI subset_iff) 
  qed
qed
qed

theorem free_universal_property:
  fixes f:: \<open>'a \<Rightarrow> 'b::complex_vector\<close>
  shows \<open>\<exists>!F::'a free \<Rightarrow> 'b. clinear_iso F \<and> f = F \<circ> inclusion_free\<close>
  proof
  show "clinear_iso F \<and> f = F \<circ> inclusion_free"
    sorry
  show "(G::'a free \<Rightarrow> 'b) = F"
    if "clinear_iso G \<and> f = G \<circ> inclusion_free"
    for G :: "'a free \<Rightarrow> 'b"
    using that sorry
qed

end
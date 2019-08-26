(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Free_Vector_Spaces
  imports
    Complex_Inner_Product
    "HOL-Library.Adhoc_Overloading"

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

lemma free_explicit:
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
        using free_explicit by blast
      thus ?thesis
        by (metis (no_types, lifting) complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset rangeI subset_iff) 
    qed
  qed
qed

lemma support_superset:
  fixes f :: \<open>'a \<Rightarrow> 'b::complex_vector\<close>
  assumes \<open>{u |u. Rep_free x u \<noteq> 0} \<subseteq> S\<close> and \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. Rep_free x z *\<^sub>C f z) =
     (\<Sum>z\<in>{u |u. Rep_free x u \<noteq> 0}. Rep_free x z *\<^sub>C f z)\<close>
proof-
  have \<open>{u |u. Rep_free x u \<noteq> 0} \<union> (S-{u |u. Rep_free x u \<noteq> 0}) = S\<close>
    using assms(1) by auto    
  moreover have \<open>{u |u. Rep_free x u \<noteq> 0} \<inter> (S-{u |u. Rep_free x u \<noteq> 0}) = {}\<close>
    by simp    
  ultimately have \<open>(\<Sum>z\<in>S. Rep_free x z *\<^sub>C f z) = 
   (\<Sum>z\<in>{u |u. Rep_free x u \<noteq> 0}. Rep_free x z *\<^sub>C f z)
 + (\<Sum>z\<in>S-{u |u. Rep_free x u \<noteq> 0}. Rep_free x z *\<^sub>C f z)\<close>
    using  \<open>finite S\<close>
    by (metis (no_types, lifting) add.commute assms(1) sum.subset_diff)
  moreover have \<open>(\<Sum>z\<in>S-{u |u. Rep_free x u \<noteq> 0}. Rep_free x z *\<^sub>C f z) = 0\<close>
  proof-
    have \<open>z\<in>S-{u |u. Rep_free x u \<noteq> 0} \<Longrightarrow> Rep_free x z *\<^sub>C f z = 0\<close>
      for z
    proof-
      assume \<open>z\<in>S-{u |u. Rep_free x u \<noteq> 0}\<close>
      hence \<open>Rep_free x z = 0\<close>
        by auto
      hence \<open>Rep_free x z *\<^sub>C f z = 0 *\<^sub>C f z\<close>
        by simp
      also have \<open>0 *\<^sub>C (f z) = 0\<close>
        by simp
      finally show ?thesis by simp
    qed
    thus ?thesis
      by simp 
  qed
  ultimately show \<open>(\<Sum>z\<in>S. Rep_free x z *\<^sub>C f z) =
     (\<Sum>z\<in>{u |u. Rep_free x u \<noteq> 0}. Rep_free x z *\<^sub>C f z)\<close>
    by simp
qed

text\<open>Universal property of the free vector space\<close>
theorem free_universal_property:
  fixes f:: \<open>'a \<Rightarrow> 'b::complex_vector\<close>
  shows \<open>\<exists>!F::'a free \<Rightarrow> 'b. clinear F \<and> f = F \<circ> inclusion_free\<close>
proof
  have \<open>\<forall> x. x = (\<Sum>z\<in>{u | u. (Rep_free x) u \<noteq> 0}. ((Rep_free x) z) *\<^sub>C (inclusion_free z))\<close>
    using free_explicit by auto
  define F::\<open>'a free \<Rightarrow> 'b\<close> where \<open>F x = (\<Sum>z\<in>{u | u. (Rep_free x) u \<noteq> 0}. ((Rep_free x) z) *\<^sub>C ( f z ) )\<close>
    for x
  show "clinear F \<and> f = F \<circ> inclusion_free"
  proof
    show \<open>f = F \<circ> inclusion_free\<close>
    proof-
      have \<open>f t = (F \<circ> inclusion_free) t\<close>
        for t
      proof-
        have \<open>(F \<circ> inclusion_free) t = F (inclusion_free t)\<close>
          by simp
        also have \<open>\<dots> = (\<Sum>z\<in>{u | u. (Rep_free (inclusion_free t)) u \<noteq> 0}. ((Rep_free (inclusion_free t)) z) *\<^sub>C ( f z ) )\<close>
          using \<open>F \<equiv> \<lambda>x. \<Sum>z\<in>{u |u. Rep_free x u \<noteq> 0}. Rep_free x z *\<^sub>C f z\<close> by blast
        also have  \<open>\<dots> = (\<Sum>z\<in>{t}. ((Rep_free (inclusion_free t)) z) *\<^sub>C ( f z ) )\<close>
        proof-
          have \<open>{u | u. (Rep_free (inclusion_free t)) u \<noteq> 0} = {t}\<close>
            by (smt Collect_cong inclusion_free.rep_eq singleton_conv zero_neq_one)          
          thus ?thesis by simp
        qed
        also have  \<open>\<dots> = ((Rep_free (inclusion_free t)) t) *\<^sub>C ( f t )\<close>
          by simp
        also have  \<open>\<dots> =  f t \<close>
        proof-
          have \<open>(Rep_free (inclusion_free t)) t = 1\<close>
            by (simp add: inclusion_free.rep_eq)
          thus ?thesis by simp
        qed
        finally have \<open>(F \<circ> inclusion_free) t = f t\<close>
          by blast
        thus ?thesis by simp
      qed
      thus ?thesis by blast
    qed
    show "clinear F"
    proof-
      have \<open>clinear (\<lambda> x. (Rep_free x) z)\<close>
        for z::'a
        unfolding clinear_def
        by (meson clinearI clinear_def free_regular_for_sum scaleC_free.rep_eq)
      have \<open>clinear (\<lambda> x. ((Rep_free x) z) *\<^sub>C ( f z ))\<close>
        for z
        unfolding clinear_def
      proof
        show "Rep_free (b1 + b2) z *\<^sub>C f z = Rep_free b1 z *\<^sub>C f z + Rep_free b2 z *\<^sub>C f z"
          for b1 :: "'a free"
            and b2 :: "'a free"
          unfolding clinear_def
          by (simp add: free_regular_for_sum scaleC_left.add)            
        show "Rep_free (r *\<^sub>C b) z *\<^sub>C f z = r *\<^sub>C Rep_free b z *\<^sub>C f z"
          for r :: complex
            and b :: "'a free"
          using \<open>clinear (\<lambda> x. ((Rep_free x) z))\<close>
          unfolding clinear_def
          by (simp add: scaleC_free.rep_eq) 
      qed
      show ?thesis unfolding F_def clinear_def
      proof
        show "(\<Sum>z\<in>{u |u. Rep_free (b1 + b2) u \<noteq> 0}. Rep_free (b1 + b2) z *\<^sub>C f z) = (\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0}. Rep_free b1 z *\<^sub>C f z) + (\<Sum>z\<in>{u |u. Rep_free b2 u \<noteq> 0}. Rep_free b2 z *\<^sub>C f z)"
          for b1 :: "'a free"
            and b2 :: "'a free"
        proof-
          have \<open>{u |u. Rep_free (b1 + b2) u \<noteq> 0} \<subseteq>
              {u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}\<close>
            by (smt Collect_mono_iff Un_def add.left_neutral free_regular_for_sum sup.cobounded2)
          moreover have \<open>finite ({u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0})\<close>
          proof-
            have \<open>finite {u |u. Rep_free b1 u \<noteq> 0}\<close>
              using Rep_free by blast
            moreover have \<open>finite {u |u. Rep_free b2 u \<noteq> 0}\<close>
              using Rep_free by blast
            ultimately show ?thesis by blast
          qed
          ultimately have \<open>(\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}. Rep_free (b1 + b2) z *\<^sub>C f z)
                    = (\<Sum>z\<in>{u |u. Rep_free (b1 + b2) u \<noteq> 0}. Rep_free (b1 + b2) z *\<^sub>C f z)\<close>
            using support_superset[where S = "{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}"
                and x = "(b1 + b2)" and f = "f" ] 
            by blast
          hence \<open>(\<Sum>z\<in>{u |u. Rep_free (b1 + b2) u \<noteq> 0}. Rep_free (b1 + b2) z *\<^sub>C f z)
                = (\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}. 
                      Rep_free (b1 + b2) z *\<^sub>C f z)\<close>
            by auto
          also have \<open>\<dots> = (\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}.
               (Rep_free b1 z + Rep_free b2 z ) *\<^sub>C f z)\<close>
            by (metis free_regular_for_sum)
          also have \<open>\<dots> = (\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}.
               (Rep_free b1 z) *\<^sub>C f z + (Rep_free b2 z) *\<^sub>C f z)\<close>
            by (meson scaleC_add_left)
          also have \<open>\<dots> = (\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}.
               (Rep_free b1 z) *\<^sub>C f z)
          +  (\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}.
               (Rep_free b2 z) *\<^sub>C f z)\<close>
            using sum.distrib by force
          finally have \<open>(\<Sum>z\<in>{u |u. Rep_free (b1 + b2) u \<noteq> 0}. Rep_free (b1 + b2) z *\<^sub>C f z) 
            = (\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}.
               (Rep_free b1 z) *\<^sub>C f z)
          +  (\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}.
               (Rep_free b2 z) *\<^sub>C f z)\<close>
            by blast
          moreover have \<open>(\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}.
               (Rep_free b1 z) *\<^sub>C f z)
                = (\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0}.
               (Rep_free b1 z) *\<^sub>C f z)\<close>
          proof-
            have \<open>{u |u. Rep_free b1 u \<noteq> 0} \<subseteq> {u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}\<close>
              by blast
            thus ?thesis
              by (metis (mono_tags) \<open>finite ({u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0})\<close> support_superset) 
          qed
          moreover have \<open>(\<Sum>z\<in>{u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}.
               (Rep_free b2 z) *\<^sub>C f z)
                = (\<Sum>z\<in>{u |u. Rep_free b2 u \<noteq> 0}.
               (Rep_free b2 z) *\<^sub>C f z)\<close>
          proof-
            have \<open>{u |u. Rep_free b2 u \<noteq> 0} \<subseteq> {u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0}\<close>
              by blast
            thus ?thesis
              by (metis (mono_tags) \<open>finite ({u |u. Rep_free b1 u \<noteq> 0} \<union> {u |u. Rep_free b2 u \<noteq> 0})\<close> support_superset) 
          qed
          ultimately show ?thesis by simp
        qed
        show "(\<Sum>z\<in>{u |u. Rep_free (r *\<^sub>C b) u \<noteq> 0}. Rep_free (r *\<^sub>C b) z *\<^sub>C f z) = r *\<^sub>C (\<Sum>z\<in>{u |u. Rep_free b u \<noteq> 0}. Rep_free b z *\<^sub>C f z)"
          for r :: complex
            and b :: "'a free"
        proof (cases \<open>r = 0\<close>)
          show "(\<Sum>z\<in>{u |u. Rep_free (r *\<^sub>C b) u \<noteq> 0}. Rep_free (r *\<^sub>C b) z *\<^sub>C f z) = r *\<^sub>C (\<Sum>z\<in>{u |u. Rep_free b u \<noteq> 0}. Rep_free b z *\<^sub>C f z)"
            if "r = 0"
            using that
            by (metis (no_types, lifting) add.left_neutral add_cancel_left_right complex_vector.scale_eq_0_iff free_regular_for_sum sum.not_neutral_contains_not_neutral) 
          show "(\<Sum>z\<in>{u |u. Rep_free (r *\<^sub>C b) u \<noteq> 0}. Rep_free (r *\<^sub>C b) z *\<^sub>C f z) = r *\<^sub>C (\<Sum>z\<in>{u |u. Rep_free b u \<noteq> 0}. Rep_free b z *\<^sub>C f z)"
            if "r \<noteq> 0"
            using that 
          proof-
            have \<open>{u |u. Rep_free (r *\<^sub>C b) u \<noteq> 0} = {u |u. Rep_free b u \<noteq> 0}\<close>
              by (metis complex_vector.scale_eq_0_iff scaleC_free.rep_eq that)
            hence \<open>(\<Sum>z\<in>{u |u. Rep_free (r *\<^sub>C b) u \<noteq> 0}. Rep_free (r *\<^sub>C b) z *\<^sub>C f z) 
                   = (\<Sum>z\<in>{u |u. Rep_free b u \<noteq> 0}. Rep_free (r *\<^sub>C b) z *\<^sub>C f z)\<close>
              by simp
            moreover have \<open>Rep_free (r *\<^sub>C b) u = r *\<^sub>C (Rep_free b) u\<close>
              for u
              by (simp add: scaleC_free.rep_eq)
            ultimately have \<open>(\<Sum>z\<in>{u |u. Rep_free (r *\<^sub>C b) u \<noteq> 0}. Rep_free (r *\<^sub>C b) z *\<^sub>C f z) 
                   = (\<Sum>z\<in>{u |u. Rep_free b u \<noteq> 0}. r *\<^sub>C Rep_free b z *\<^sub>C f z)\<close>
              by simp
            thus ?thesis
              by (metis (mono_tags, lifting) scaleC_right.sum sum.cong) 
          qed
        qed
      qed
    qed
  qed
  show \<open>G = F\<close>
    if "clinear G \<and> f = G \<circ> inclusion_free"
    for G :: "'a free \<Rightarrow> 'b"
  proof-
    have \<open>clinear G\<close> and \<open>f = G \<circ> inclusion_free\<close>
      using that by auto
    have \<open>x \<in> (range inclusion_free) \<Longrightarrow> G x = F x\<close>
      for x
      using \<open>clinear F \<and> f = F \<circ> inclusion_free\<close> \<open>f = G \<circ> inclusion_free\<close>
      by (metis comp_eq_elim f_inv_into_f)
    hence \<open>x \<in> complex_vector.span (range inclusion_free) \<Longrightarrow> G x = F x\<close>
      for x
      by (simp add: \<open>clinear F \<and> f = F \<circ> inclusion_free\<close> \<open>clinear G\<close> complex_vector.linear_eq_on)
    hence \<open>G x = F x\<close>
      for x
      by (simp add: free_span)      
    thus ?thesis by blast
  qed
qed

lemma inclusion_free_inj:
  assumes \<open>inclusion_free x = inclusion_free y\<close>
  shows \<open>x = y\<close>
  by (metis assms inclusion_free.rep_eq zero_neq_one)


end
(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Free_Vector_Spaces
  imports
    Complex_Inner_Product
    "HOL-Library.Adhoc_Overloading"
    General_Results_Missing

begin

typedef 'a free = \<open>{f::'a \<Rightarrow> complex. finite {x | x. f x \<noteq> 0}}\<close>
  morphisms times_free_vec Abs_free
  apply auto
  using not_finite_existsD by fastforce

setup_lifting type_definition_free

bundle free_notation begin
notation times_free_vec (infixr "\<down>" 70)
end

bundle no_free_notation begin
no_notation times_free_vec (infixr "\<down>" 70)
end

unbundle free_notation

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
  shows \<open>(x + y) \<down> t = x \<down> t + y \<down> t\<close>
  apply transfer
  by auto


lemma free_regular_for_sum_general_induction:
  fixes x :: \<open>'a free\<close>
  shows \<open>\<forall> S. finite S \<and> card S = n \<longrightarrow> ( \<Sum> u \<in> S. (x \<down> u) *\<^sub>C (inclusion_free u) ) \<down> t
  = (\<Sum> u \<in> S. ( (x \<down> u) *\<^sub>C (inclusion_free u) ) \<down> t )\<close>
proof (induction n)
  show "\<forall>S. finite S \<and> card S = 0 \<longrightarrow> (\<Sum>u\<in>S. (x \<down> u) *\<^sub>C inclusion_free u) \<down> t = (\<Sum>u\<in>S. ((x \<down> u) *\<^sub>C inclusion_free u) \<down> t)"
    by (metis (no_types, lifting) card_0_eq sum_clauses(1) zero_free.rep_eq)
  show "\<forall>S. finite S \<and> card S = Suc n \<longrightarrow> (\<Sum>u\<in>S. (x \<down> u) *\<^sub>C inclusion_free u) \<down> t = (\<Sum>u\<in>S. ((x \<down> u) *\<^sub>C inclusion_free u) \<down> t)"
    if "\<forall>S. finite S \<and> card S = n \<longrightarrow>  (\<Sum>u\<in>S. (x \<down> u) *\<^sub>C inclusion_free u) \<down> t = (\<Sum>u\<in>S. ( (x \<down> u) *\<^sub>C inclusion_free u) \<down> t)"
    for n :: nat
  proof-
    have \<open>finite S \<Longrightarrow> card S = Suc n \<Longrightarrow> (\<Sum>u\<in>S. (x \<down> u) *\<^sub>C inclusion_free u) \<down> t = (\<Sum>u\<in>S. ( (x \<down> u) *\<^sub>C inclusion_free u) \<down> t)\<close>
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
      ultimately have \<open>(\<Sum>u\<in>R. (x \<down> u) *\<^sub>C inclusion_free u) \<down> t = (\<Sum>u\<in>R. ((x \<down> u) *\<^sub>C inclusion_free u) \<down> t)\<close>
        by (simp add: that)
      hence \<open>(\<Sum>u\<in>R. (x \<down> u) *\<^sub>C inclusion_free u) \<down> t + ((x \<down> r) *\<^sub>C inclusion_free r) \<down> t
         = (\<Sum>u\<in>R. ((x \<down> u) *\<^sub>C inclusion_free u) \<down> t) + ((x \<down> r) *\<^sub>C inclusion_free r) \<down> t\<close>
        by simp
      moreover have \<open>(\<Sum>u\<in>R. (x \<down> u) *\<^sub>C inclusion_free u) \<down> t + ((x \<down> r) *\<^sub>C inclusion_free r) \<down> t
          = (\<Sum>u\<in>S. (x \<down> u) *\<^sub>C inclusion_free u) \<down> t\<close>
        by (simp add: \<open>S = insert r R\<close> \<open>finite R\<close> \<open>r \<notin> R\<close> plus_free.rep_eq)        
      moreover have \<open>(\<Sum>u\<in>R.  ( (x \<down> u) *\<^sub>C inclusion_free u) \<down> t) +  ( (x \<down> r) *\<^sub>C inclusion_free r) \<down> t
          =  (\<Sum>u\<in>S. ((x \<down> u) *\<^sub>C inclusion_free u) \<down> t)\<close>
        by (simp add: \<open>S = insert r R\<close> \<open>finite R\<close> \<open>r \<notin> R\<close>)        
      ultimately show \<open>(\<Sum>u\<in>S. (x \<down> u) *\<^sub>C inclusion_free u) \<down> t = (\<Sum>u\<in>S. ((x \<down> u) *\<^sub>C inclusion_free u) \<down> t)\<close>
        by simp
    qed
    thus ?thesis by blast
  qed
qed


lemma free_regular_for_sum_general:
  fixes x :: \<open>'a free\<close>
  assumes \<open>finite S\<close>
  shows \<open>( \<Sum> u \<in> S. (x \<down> u) *\<^sub>C (inclusion_free u) ) \<down> t
  = (\<Sum> u \<in> S. ((x \<down> u) *\<^sub>C (inclusion_free u) ) \<down> t )\<close>
  using free_regular_for_sum_general_induction assms
  by (simp add: free_regular_for_sum_general_induction) 

lemma free_explicit:
  fixes X :: \<open>'a free\<close>
  shows \<open>X = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}. (X \<down> z) *\<^sub>C (inclusion_free z))\<close>
proof-
  have \<open>X \<down> t = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}. (X \<down> z) *\<^sub>C (inclusion_free z)) \<down> t\<close>
    for t
  proof (cases \<open>t \<in> {u | u. X \<down> u \<noteq> 0}\<close>)
    show "X \<down> t = (\<Sum>z\<in>{u |u. (X \<down> u) \<noteq> 0}. (X \<down> z) *\<^sub>C inclusion_free z) \<down> t"
      if "t \<in> {u |u. X \<down> u \<noteq> 0}"
    proof-
      have \<open>finite {u | u. X \<down> u \<noteq> 0}\<close>
        using times_free_vec by force
      hence \<open>(\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}. ((X \<down> z) *\<^sub>C (inclusion_free z))) \<down> t
        = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}. ( (X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t ) \<close>
        using free_regular_for_sum_general[where S = "{u | u. X \<down> u \<noteq> 0}" and x = "X" and t = "t"]
        by blast
      moreover have \<open>(\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}.  ( ((X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t )) =  X \<down> t\<close>
      proof-
        have \<open>(\<Sum>z\<in>{t}. ( ( X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t ) = X \<down> t\<close>
        proof-
          have \<open>(\<Sum>z\<in>{t}. ( (X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t )
            = ( ( X \<down> t) *\<^sub>C (inclusion_free t) ) \<down> t \<close>
            by simp
          also have \<open>\<dots> = X \<down> t\<close>
            apply transfer
            by auto
          finally show ?thesis by blast
        qed
        moreover have \<open>(\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0} - {t}. ( (X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t ) = 0\<close>
        proof-
          have \<open>z\<in>{u | u.  X \<down> u \<noteq> 0} - {t} \<Longrightarrow> 
                ( (X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t  = 0\<close>
            for z
          proof-
            assume \<open>z\<in>{u | u. X \<down> u \<noteq> 0} - {t}\<close>
            hence \<open>z \<noteq> t\<close>
              by simp
            hence \<open>(inclusion_free z) \<down> t = 0\<close>
              apply transfer by auto
            thus \<open>( (X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t  = 0\<close>
              by (simp add: scaleC_free.rep_eq)
          qed
          thus ?thesis by simp
        qed
        moreover have \<open>(\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}.  ( ( X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t )
      = (\<Sum>z\<in>{t}. ( ( X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t )
      + (\<Sum>z\<in>{u | u.  X \<down> u \<noteq> 0} - {t}. ( (X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t )\<close>
          using \<open>finite {u |u. X \<down> u \<noteq> 0}\<close> empty_iff sum.remove that by fastforce
        ultimately show ?thesis by simp
      qed
      ultimately show \<open>X \<down> t = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}. (X \<down> z) *\<^sub>C (inclusion_free z)) \<down> t\<close>
        by simp      
    qed
    show "X \<down> t =  (\<Sum>z\<in>{u |u. X \<down> u \<noteq> 0}. (X \<down> z) *\<^sub>C inclusion_free z) \<down> t"
      if "t \<notin> {u |u. X \<down> u \<noteq> 0}"
    proof-
      have \<open>X \<down> t = 0\<close>
        using that by simp
      moreover have \<open>(\<Sum>z\<in>{u |u. X \<down> u \<noteq> 0}. (X \<down> z) *\<^sub>C inclusion_free z) \<down> t = 0\<close>
      proof-
        have \<open>(\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}. (X \<down> z) *\<^sub>C (inclusion_free z)) \<down> t
        = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}.  ( (X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t ) \<close>
          using free_regular_for_sum_general[where S = "{u | u. X \<down> u \<noteq> 0}" and x = "X" and t = "t"]
          by (metis (no_types, lifting) sum.infinite zero_free.rep_eq)
        also have \<open>\<dots> = 0\<close>
        proof-
          have \<open>z\<in>{u | u. X \<down> u \<noteq> 0} \<Longrightarrow> ( (X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t = 0\<close>
            for z
          proof-
            assume \<open>z\<in>{u | u. X \<down> u \<noteq> 0}\<close>
            hence \<open>(inclusion_free z) \<down> t = 0\<close>
              by (metis inclusion_free.rep_eq that)          
            thus \<open>( ( X \<down> z) *\<^sub>C (inclusion_free z) ) \<down> t = 0\<close>
              by (simp add: scaleC_free.rep_eq) 
          qed
          thus ?thesis by simp
        qed
        finally show ?thesis by blast
      qed
      ultimately show ?thesis by simp
    qed
  qed
  thus \<open>X = (\<Sum>z\<in>{u | u. X \<down> u \<noteq> 0}. (X \<down> z) *\<^sub>C (inclusion_free z))\<close>
    using times_free_vec_inject by blast
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
      have \<open>x = (\<Sum>z\<in>{u | u. x \<down> u \<noteq> 0}. ( x \<down> z) *\<^sub>C (inclusion_free z))\<close>
        using free_explicit by blast
      thus ?thesis
        by (metis (no_types, lifting) complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset rangeI subset_iff) 
    qed
  qed
qed

lemma support_superset:
  fixes f :: \<open>'a \<Rightarrow> 'b::complex_vector\<close>
  assumes \<open>{u |u. x \<down> u \<noteq> 0} \<subseteq> S\<close> and \<open>finite S\<close>
  shows \<open>(\<Sum>z\<in>S. (x \<down> z) *\<^sub>C f z) =
     (\<Sum>z\<in>{u |u. x \<down> u \<noteq> 0}. (x \<down> z) *\<^sub>C f z)\<close>
proof-
  have \<open>{u |u. x \<down> u \<noteq> 0} \<union> (S-{u |u. x \<down> u \<noteq> 0}) = S\<close>
    using assms(1) by auto    
  moreover have \<open>{u |u. x \<down> u \<noteq> 0} \<inter> (S-{u |u. x \<down> u \<noteq> 0}) = {}\<close>
    by simp    
  ultimately have \<open>(\<Sum>z\<in>S. (x \<down> z) *\<^sub>C f z) = 
   (\<Sum>z\<in>{u |u. x \<down> u \<noteq> 0}. (x \<down> z) *\<^sub>C f z)
 + (\<Sum>z\<in>S-{u |u. x \<down> u \<noteq> 0}. (x \<down> z) *\<^sub>C f z)\<close>
    using  \<open>finite S\<close>
    by (metis (no_types, lifting) add.commute assms(1) sum.subset_diff)
  moreover have \<open>(\<Sum>z\<in>S-{u |u. x \<down> u \<noteq> 0}. (x \<down> z) *\<^sub>C f z) = 0\<close>
  proof-
    have \<open>z\<in>S-{u |u. x \<down> u \<noteq> 0} \<Longrightarrow> (x \<down> z) *\<^sub>C f z = 0\<close>
      for z
    proof-
      assume \<open>z\<in>S-{u |u. x \<down> u \<noteq> 0}\<close>
      hence \<open>x \<down> z = 0\<close>
        by auto
      hence \<open>(x \<down> z) *\<^sub>C f z = 0 *\<^sub>C f z\<close>
        by simp
      also have \<open>0 *\<^sub>C (f z) = 0\<close>
        by simp
      finally show ?thesis by simp
    qed
    thus ?thesis
      by simp 
  qed
  ultimately show \<open>(\<Sum>z\<in>S. (x \<down> z) *\<^sub>C f z) =
     (\<Sum>z\<in>{u |u. x \<down> u \<noteq> 0}. (x \<down> z) *\<^sub>C f z)\<close>
    by simp
qed

text\<open>Universal property of the free vector space\<close>

definition universal_free::\<open>('a \<Rightarrow> 'b::complex_vector) \<Rightarrow> ('a free \<Rightarrow> 'b)\<close>
  where \<open>universal_free f x = (\<Sum>z\<in>{u | u. x \<down> u \<noteq> 0}. (x \<down> z) *\<^sub>C ( f z ) )\<close>

lemma inclusion_free_comp:
  \<open>f = (universal_free f) \<circ> inclusion_free\<close>
proof-
  have \<open>f t = ((universal_free f) \<circ> inclusion_free) t\<close>
    for t
  proof-
    have \<open>((universal_free f) \<circ> inclusion_free) t = (universal_free f) (inclusion_free t)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum>z\<in>{u | u. (inclusion_free t) \<down> u \<noteq> 0}. ((inclusion_free t) \<down> z) *\<^sub>C ( f z ) )\<close>
      using universal_free_def by blast
    also have  \<open>\<dots> = (\<Sum>z\<in>{t}. ((inclusion_free t) \<down> z) *\<^sub>C ( f z ) )\<close>
    proof-
      have \<open>{u | u. (inclusion_free t) \<down> u \<noteq> 0} = {t}\<close>
        by (smt Collect_cong inclusion_free.rep_eq singleton_conv zero_neq_one)          
      thus ?thesis by simp
    qed
    also have  \<open>\<dots> = ((inclusion_free t) \<down> t) *\<^sub>C ( f t )\<close>
      by simp
    also have  \<open>\<dots> =  f t \<close>
    proof-
      have \<open>(inclusion_free t) \<down> t = 1\<close>
        by (simp add: inclusion_free.rep_eq)
      thus ?thesis by simp
    qed
    finally have \<open>((universal_free f) \<circ> inclusion_free) t = f t\<close>
      by blast
    thus ?thesis by simp
  qed
  thus ?thesis by blast
qed


lemma universal_free_clinear:
  "clinear (universal_free f)"
proof-
  have \<open>clinear (\<lambda> x. x \<down> z)\<close>
    for z::'a
    unfolding clinear_def
    by (meson clinearI clinear_def free_regular_for_sum scaleC_free.rep_eq)
  have \<open>clinear (\<lambda> x. (x \<down> z) *\<^sub>C ( f z ))\<close>
    for z
    unfolding clinear_def
  proof
    show "((b1 + b2) \<down> z) *\<^sub>C f z = (b1 \<down> z) *\<^sub>C f z + (b2 \<down> z) *\<^sub>C f z"
      for b1 :: "'a free"
        and b2 :: "'a free"
      unfolding clinear_def
      by (simp add: free_regular_for_sum scaleC_left.add)            
    show "((r *\<^sub>C b) \<down> z) *\<^sub>C f z = r *\<^sub>C (b \<down> z) *\<^sub>C f z"
      for r :: complex
        and b :: "'a free"
      using \<open>clinear (\<lambda> x. (x \<down> z))\<close>
      unfolding clinear_def
      by (simp add: scaleC_free.rep_eq) 
  qed
  show ?thesis unfolding universal_free_def clinear_def
  proof
    show "(\<Sum>z\<in>{u |u. (b1 + b2) \<down> u \<noteq> 0}. ( (b1 + b2) \<down> z ) *\<^sub>C f z) = (\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0}. (b1 \<down> z) *\<^sub>C f z) + (\<Sum>z\<in>{u |u. b2 \<down> u \<noteq> 0}. (b2 \<down> z) *\<^sub>C f z)"
      for b1 :: "'a free"
        and b2 :: "'a free"
    proof-
      have \<open>{u |u. (b1 + b2) \<down> u \<noteq> 0} \<subseteq>
              {u |u. b1 \<down> u \<noteq> 0} \<union> {u |u. b2 \<down> u \<noteq> 0}\<close>
        by (smt Collect_mono_iff Un_def add.left_neutral free_regular_for_sum sup.cobounded2)
      moreover have \<open>finite ({u |u. b1 \<down> u \<noteq> 0} \<union> {u |u.  b2 \<down> u \<noteq> 0})\<close>
      proof-
        have \<open>finite {u |u. b1 \<down> u \<noteq> 0}\<close>
          using times_free_vec by blast
        moreover have \<open>finite {u |u. b2 \<down> u \<noteq> 0}\<close>
          using times_free_vec by blast
        ultimately show ?thesis by blast
      qed
      ultimately have \<open>(\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u. b2 \<down> u \<noteq> 0}. ((b1 + b2) \<down> z) *\<^sub>C f z)
                    = (\<Sum>z\<in>{u |u. (b1 + b2) \<down> u \<noteq> 0}.  ((b1 + b2) \<down> z) *\<^sub>C f z)\<close>
        using support_superset[where S = "{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u. b2 \<down> u \<noteq> 0}"
            and x = "(b1 + b2)" and f = "f" ] 
        by blast
      hence \<open>(\<Sum>z\<in>{u |u. (b1 + b2) \<down> u \<noteq> 0}. ((b1 + b2) \<down> z) *\<^sub>C f z)
                = (\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u. b2 \<down> u \<noteq> 0}. 
                      ((b1 + b2) \<down> z) *\<^sub>C f z)\<close>
        by auto
      also have \<open>\<dots> = (\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u.  b2 \<down> u \<noteq> 0}.
               (b1 \<down> z + b2 \<down> z ) *\<^sub>C f z)\<close>
        by (metis free_regular_for_sum)
      also have \<open>\<dots> = (\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u.  b2 \<down> u \<noteq> 0}.
               (b1 \<down> z) *\<^sub>C f z + (b2 \<down> z) *\<^sub>C f z)\<close>
        by (meson scaleC_add_left)
      also have \<open>\<dots> = (\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u.  b2 \<down> u \<noteq> 0}.
               (b1 \<down> z) *\<^sub>C f z)
          +  (\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u. b2 \<down> u \<noteq> 0}.
               (b2 \<down> z) *\<^sub>C f z)\<close>
        using sum.distrib by force
      finally have \<open>(\<Sum>z\<in>{u |u. (b1 + b2) \<down> u \<noteq> 0}. ((b1 + b2) \<down> z) *\<^sub>C f z) 
            = (\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u. b2 \<down> u \<noteq> 0}.
               (b1 \<down> z) *\<^sub>C f z)
          +  (\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u. b2 \<down> u \<noteq> 0}.
               (b2 \<down> z) *\<^sub>C f z)\<close>
        by blast
      moreover have \<open>(\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u.  b2 \<down> u \<noteq> 0}.
               (b1 \<down> z) *\<^sub>C f z)
                = (\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0}. (b1 \<down> z) *\<^sub>C f z)\<close>
      proof-
        have \<open>{u |u. b1 \<down> u \<noteq> 0} \<subseteq> {u |u. b1 \<down> u \<noteq> 0} \<union> {u |u. b2 \<down> u \<noteq> 0}\<close>
          by blast
        thus ?thesis
          by (metis (mono_tags) \<open>finite ({u |u. b1 \<down> u \<noteq> 0} \<union> {u |u. b2 \<down> u \<noteq> 0})\<close> support_superset) 
      qed
      moreover have \<open>(\<Sum>z\<in>{u |u. b1 \<down> u \<noteq> 0} \<union> {u |u.  b2 \<down> u \<noteq> 0}. (b2 \<down> z) *\<^sub>C f z)
                = (\<Sum>z\<in>{u |u. b2 \<down> u \<noteq> 0}. (b2 \<down> z) *\<^sub>C f z)\<close>
      proof-
        have \<open>{u |u. b2 \<down> u \<noteq> 0} \<subseteq> {u |u. b1 \<down> u \<noteq> 0} \<union> {u |u.  b2 \<down> u \<noteq> 0}\<close>
          by blast
        thus ?thesis
          by (metis (mono_tags) \<open>finite ({u |u. b1 \<down> u \<noteq> 0} \<union> {u |u. b2 \<down> u \<noteq> 0})\<close> support_superset) 
      qed
      ultimately show ?thesis by simp
    qed
    show "(\<Sum>z\<in>{u |u.  (r *\<^sub>C b) \<down> u \<noteq> 0}.  ((r *\<^sub>C b) \<down> z) *\<^sub>C f z) = r *\<^sub>C (\<Sum>z\<in>{u |u. b \<down> u \<noteq> 0}. (b \<down> z) *\<^sub>C f z)"
      for r :: complex
        and b :: "'a free"
    proof (cases \<open>r = 0\<close>)
      show "(\<Sum>z\<in>{u |u. (r *\<^sub>C b) \<down> u \<noteq> 0}. ( (r *\<^sub>C b) \<down> z ) *\<^sub>C f z) = r *\<^sub>C (\<Sum>z\<in>{u |u. b \<down> u \<noteq> 0}. (b \<down> z) *\<^sub>C f z)"
        if "r = 0"
        using that
        by (metis (no_types, lifting) add.left_neutral add_cancel_left_right complex_vector.scale_eq_0_iff free_regular_for_sum sum.not_neutral_contains_not_neutral) 
      show "(\<Sum>z\<in>{u |u. (r *\<^sub>C b) \<down> u \<noteq> 0}. ( (r *\<^sub>C b) \<down> z ) *\<^sub>C f z) = r *\<^sub>C (\<Sum>z\<in>{u |u. b \<down> u \<noteq> 0}. (b \<down> z) *\<^sub>C f z)"
        if "r \<noteq> 0"
        using that 
      proof-
        have \<open>{u |u.  (r *\<^sub>C b) \<down> u \<noteq> 0} = {u |u.  b \<down> u \<noteq> 0}\<close>
          by (metis complex_vector.scale_eq_0_iff scaleC_free.rep_eq that)
        hence \<open>(\<Sum>z\<in>{u |u. (r *\<^sub>C b) \<down> u \<noteq> 0}.  ((r *\<^sub>C b) \<down> z) *\<^sub>C f z) 
                   = (\<Sum>z\<in>{u |u. b \<down> u \<noteq> 0}. ((r *\<^sub>C b) \<down> z) *\<^sub>C f z)\<close>
          by simp
        moreover have \<open>(r *\<^sub>C b) \<down> u = r *\<^sub>C (b \<down> u)\<close>
          for u
          by (simp add: scaleC_free.rep_eq)
        ultimately have \<open>(\<Sum>z\<in>{u |u. (r *\<^sub>C b) \<down> u \<noteq> 0}.  ((r *\<^sub>C b) \<down> z) *\<^sub>C f z) 
                   = (\<Sum>z\<in>{u |u. b \<down> u \<noteq> 0}. r *\<^sub>C (b \<down> z) *\<^sub>C f z)\<close>
          by simp
        thus ?thesis
          by (metis (mono_tags, lifting) scaleC_right.sum sum.cong) 
      qed
    qed
  qed
qed


lemma universal_free_uniq:
  assumes \<open>clinear G\<close> and \<open>f = G \<circ> inclusion_free\<close>
  shows \<open>G = universal_free f\<close>
proof-
  have \<open>clinear (universal_free f)\<close>
    by (simp add: universal_free_clinear)
  moreover have \<open>f = (universal_free f) \<circ> inclusion_free\<close>
    by (simp add: inclusion_free_comp)    
  ultimately have \<open>x \<in> (range inclusion_free) \<Longrightarrow> G x = (universal_free f) x\<close>
    for x
    using \<open>f = G \<circ> inclusion_free\<close>
    by (metis comp_eq_elim f_inv_into_f)
  hence \<open>x \<in> complex_vector.span (range inclusion_free) \<Longrightarrow> G x = (universal_free f) x\<close>
    for x
    by (meson \<open>clinear (universal_free f)\<close> assms(1) complex_vector.module_hom_eq_on_span)
  hence \<open>G x = (universal_free f) x\<close>
    for x
    by (simp add: free_span)      
  thus ?thesis by blast
qed


theorem free_universal_property:
  fixes f:: \<open>'a \<Rightarrow> 'b::complex_vector\<close>
  shows \<open>\<exists>!F::'a free \<Rightarrow> 'b. clinear F \<and> f = F \<circ> inclusion_free\<close>
proof
  show "clinear (universal_free f) \<and> f = (universal_free f) \<circ> inclusion_free"
    by (simp add: inclusion_free_comp universal_free_clinear)

  show "F = (universal_free f)"
    if "clinear F \<and> f = F \<circ> inclusion_free"
    for F :: "'a free \<Rightarrow> 'b"
    using that
    by (simp add: universal_free_uniq) 
qed

lemma inclusion_free_inj:
  assumes \<open>inclusion_free x = inclusion_free y\<close>
  shows \<open>x = y\<close>
  by (metis assms inclusion_free.rep_eq zero_neq_one)

(* TODO: I wonder if it is easier to use when defining it as
  lift_definition ... is
      "\<lambda>f x b. \<Sum>a\<in>{a|a. x a \<noteq> 0 \<and> f a = b}. x a" 
  (It should be the same in the end.)
*)
definition free_map :: \<open>('a\<Rightarrow>'b) \<Rightarrow> ('a free\<Rightarrow>'b free)\<close> 
  where \<open>free_map f x = (\<Sum>a\<in>{a|a. x\<down>a \<noteq> 0}. (x\<down>a) *\<^sub>C inclusion_free (f a))\<close>

lemma free_map_clinear:
  \<open>clinear (free_map f)\<close>
  unfolding clinear_def
proof
  show "free_map f (b1 + b2) = free_map f b1 + free_map f b2"
    for b1 :: "'a free"
      and b2 :: "'a free"
  proof-
    have \<open>free_map f (b1 + b2) =
          (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}.
       ((b1 + b2) \<down> a) *\<^sub>C inclusion_free (f a))\<close>
      unfolding free_map_def
      by blast
    also have \<open>\<dots> =
          (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}.
       (b1 \<down> a) *\<^sub>C inclusion_free (f a) + (b2 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
      by (metis (no_types, lifting) plus_free.rep_eq scaleC_left.add)
    also have \<open>\<dots> =
          (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))
        + (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
      using sum.distrib by force      
    also have \<open>\<dots> = 
    (\<Sum>a\<in>{a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a)) +
    (\<Sum>a\<in>{a |a. b2 \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
    proof-
      have  \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a)) =
            (\<Sum>a\<in>{a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a)) -
            (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b1 \<down> a \<noteq> 0}.
           (b1 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
      proof-
        have \<open>finite {a |a. (b1 + b2) \<down> a \<noteq> 0}\<close>
          using times_free_vec by fastforce          
        hence \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))
             = (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}\<inter>{a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))
             + (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}-{a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
          using sum.Int_Diff by blast
        moreover have \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}-{a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a)) = 0\<close>
        proof-
          have \<open>i\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}-{a |a. b1 \<down> a \<noteq> 0} \<Longrightarrow> (b1 \<down> i) *\<^sub>C inclusion_free (f i) = 0\<close>
            for i
          proof-
            assume \<open>i\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}-{a |a. b1 \<down> a \<noteq> 0}\<close>
            hence  \<open>(b1 \<down> i) = 0\<close>
              by simp
            thus ?thesis
              by simp 
          qed
          thus ?thesis
            by simp 
        qed
        ultimately have \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))
             = (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}\<inter>{a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
          by simp
        also have \<open>\<dots> = (\<Sum>a\<in>{a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))
                      - (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a = 0}\<inter>{a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
        proof-
          have \<open>{a |a. (b1 + b2) \<down> a \<noteq> 0}\<inter>{a |a. b1 \<down> a \<noteq> 0}
              = {a |a. b1 \<down> a \<noteq> 0}-({a |a. (b1 + b2) \<down> a = 0}\<inter>{a |a. b1 \<down> a \<noteq> 0})\<close>
            by auto
          moreover have \<open>{a |a. (b1 + b2) \<down> a = 0}\<inter>{a |a. b1 \<down> a \<noteq> 0} \<subseteq> {a |a. b1 \<down> a \<noteq> 0}\<close>
            by auto
          moreover have \<open>finite  {a |a. b1 \<down> a \<noteq> 0}\<close>
            using times_free_vec by auto
          ultimately show ?thesis
            by (simp add: sum_diff) 
        qed
        finally show \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a)) =
  (\<Sum>a\<in>{a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a)) -
  (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b1 \<down> a \<noteq> 0}.
     (b1 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
          by blast
      qed
      moreover have \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a)) =
            (\<Sum>a\<in>{a |a. b2 \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a)) -
            (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b2 \<down> a \<noteq> 0}.
           (b2 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
      proof-
        have \<open>finite {a |a. (b1 + b2) \<down> a \<noteq> 0}\<close>
          using times_free_vec by fastforce          
        hence \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a))
             = (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}\<inter>{a |a. b2 \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a))
             + (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}-{a |a. b2 \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
          using sum.Int_Diff by blast
        moreover have \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}-{a |a. b2 \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a)) = 0\<close>
        proof-
          have \<open>i\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}-{a |a. b2 \<down> a \<noteq> 0} \<Longrightarrow> (b2 \<down> i) *\<^sub>C inclusion_free (f i) = 0\<close>
            for i
          proof-
            assume \<open>i\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}-{a |a. b2 \<down> a \<noteq> 0}\<close>
            hence  \<open>(b2 \<down> i) = 0\<close>
              by simp
            thus ?thesis
              by simp 
          qed
          thus ?thesis
            by simp 
        qed
        ultimately have \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a))
             = (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}\<inter>{a |a. b2 \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
          by simp
        also have \<open>\<dots> = (\<Sum>a\<in>{a |a. b2 \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a))
                      - (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a = 0}\<inter>{a |a. b2 \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
        proof-
          have \<open>{a |a. (b1 + b2) \<down> a \<noteq> 0}\<inter>{a |a. b2 \<down> a \<noteq> 0}
              = {a |a. b2 \<down> a \<noteq> 0}-({a |a. (b1 + b2) \<down> a = 0}\<inter>{a |a. b2 \<down> a \<noteq> 0})\<close>
            by auto
          moreover have \<open>{a |a. (b1 + b2) \<down> a = 0}\<inter>{a |a. b2 \<down> a \<noteq> 0} \<subseteq> {a |a. b2 \<down> a \<noteq> 0}\<close>
            by auto
          moreover have \<open>finite  {a |a. b2 \<down> a \<noteq> 0}\<close>
            using times_free_vec by auto
          ultimately show ?thesis
            by (simp add: sum_diff) 
        qed
        finally show \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a)) =
  (\<Sum>a\<in>{a |a. b2 \<down> a \<noteq> 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a)) -
  (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b2 \<down> a \<noteq> 0}.
     (b2 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
          by blast
      qed
      moreover have \<open>(\<Sum>a\<in>{a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b1 \<down> a \<noteq> 0}.
           (b1 \<down> a) *\<^sub>C inclusion_free (f a)) + (\<Sum>a\<in>{a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b2 \<down> a \<noteq> 0}.
           (b2 \<down> a) *\<^sub>C inclusion_free (f a)) = 0\<close>
      proof-
        have \<open>finite S \<Longrightarrow> (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b1 \<down> a \<noteq> 0}.
           (b1 \<down> a) *\<^sub>C inclusion_free (f a)) = 
              (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
          for S
        proof-
          assume \<open>finite S\<close>
          have \<open>(\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))
              = (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))
              + (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0} - {a |a. b1 \<down> a \<noteq> 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
            using \<open>finite S\<close> finite_Int sum.Int_Diff by blast            
          moreover have \<open>(\<Sum>a\<in>S\<inter>{a |a. (b1 + b2) \<down> a = 0}-{a |a. b1 \<down> a \<noteq> 0}.
                        (b1 \<down> a) *\<^sub>C inclusion_free (f a)) = 0\<close>
          proof-
            have \<open>i\<in>S\<inter>{a |a. (b1 + b2) \<down> a = 0}-{a |a. b1 \<down> a \<noteq> 0} \<Longrightarrow> (b1 \<down> i) = 0\<close>
              for i
              by auto              
            thus ?thesis
              by (metis (mono_tags, lifting) complex_vector.scale_eq_0_iff sum.not_neutral_contains_not_neutral) 
          qed
          ultimately have \<open>(\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b1 \<down> a \<noteq> 0}.
           (b1 \<down> a) *\<^sub>C inclusion_free (f a)) = 
              (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
            by auto
          thus ?thesis
            by blast 
        qed
        moreover have \<open>finite S \<Longrightarrow> (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b2 \<down> a \<noteq> 0}.
           (b2 \<down> a) *\<^sub>C inclusion_free (f a)) = 
              (\<Sum>a\<in>S \<inter>{a |a. (b1 + b2) \<down> a = 0}.
           (b2 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
          for S
          by (smt complex_vector.scale_eq_0_iff finite_Int mem_Collect_eq sum.cong sum.inter_restrict)
            (* > 1 s *)
        moreover have \<open>finite S \<Longrightarrow> (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))
           + (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a)) = 0\<close>
          for S
        proof-
          assume \<open>finite S\<close>
          have \<open>(\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a))
          + (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. (b2 \<down> a) *\<^sub>C inclusion_free (f a)) = 
            (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. (b1 \<down> a) *\<^sub>C inclusion_free (f a) 
          + (b2 \<down> a) *\<^sub>C inclusion_free (f a))\<close>
            by (simp add: sum.distrib)
          also have \<open>\<dots> = (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. 
              ( (b1 \<down> a) + (b2 \<down> a) ) *\<^sub>C inclusion_free (f a))\<close>
            by (metis (no_types, lifting) scaleC_add_left)
          also have \<open>\<dots> = (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. 0 *\<^sub>C inclusion_free (f a))\<close>
            by (simp add: free_regular_for_sum)
          also have \<open>\<dots> = (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0}. 0)\<close>
            by simp
          also have \<open>\<dots> = 0\<close>
            by simp
          finally show ?thesis by blast
        qed
        ultimately have finite_thesis: \<open>finite S \<Longrightarrow> (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b1 \<down> a \<noteq> 0}.
       (b1 \<down> a) *\<^sub>C inclusion_free (f a)) +
    (\<Sum>a\<in>S \<inter> {a |a. (b1 + b2) \<down> a = 0} \<inter> {a |a. b2 \<down> a \<noteq> 0}.
       (b2 \<down> a) *\<^sub>C inclusion_free (f a)) = 0\<close>
          for S
          by simp
        have \<open>finite ({a |a. b1 \<down> a \<noteq> 0} \<union> {a |a. b2 \<down> a \<noteq> 0})\<close>
          using times_free_vec by force
        thus ?thesis
          using finite_thesis[where S = "{a |a. b1 \<down> a \<noteq> 0} \<union> {a |a. b2 \<down> a \<noteq> 0}"]
          by (smt inf_sup_absorb inf_sup_aci(1) inf_sup_aci(3) inf_sup_aci(5))          
      qed
      ultimately show ?thesis
        by (metis (no_types, lifting) add_diff_add diff_zero) 
    qed
    also have \<open>\<dots> = free_map f b1 + free_map f b2\<close>
      unfolding free_map_def
      by blast
    finally show ?thesis by simp
  qed

  show "free_map f (r *\<^sub>C b) = r *\<^sub>C free_map f b"
    for r :: complex
      and b :: "'a free"
  proof (cases \<open>r = 0\<close>)
    show "free_map f (r *\<^sub>C b) = r *\<^sub>C free_map f b"
      if "r = 0"
      using that unfolding free_map_def
      by (metis (no_types, lifting) complex_vector.scale_eq_0_iff scaleC_free.rep_eq sum.not_neutral_contains_not_neutral)

    show "free_map f (r *\<^sub>C b) = r *\<^sub>C free_map f b"
      if "r \<noteq> 0"
    proof-
      have \<open>{a |a. r *\<^sub>C b \<down> a \<noteq> 0} = {a |a. b \<down> a \<noteq> 0}\<close>
        by (metis  complex_vector.scale_eq_0_iff scaleC_free.rep_eq that)
      moreover have \<open>(r *\<^sub>C b) \<down> a = r *\<^sub>C (b \<down> a)\<close>
        for a
        by (simp add: scaleC_free.rep_eq)      
      moreover have \<open> (\<Sum>a\<in>{a |a. b \<down> a \<noteq> 0}. r *\<^sub>C (b \<down> a) *\<^sub>C inclusion_free (f a)) =
        r *\<^sub>C (\<Sum>a\<in>{a |a. b \<down> a \<noteq> 0}. (b \<down> a) *\<^sub>C inclusion_free (f a))\<close>
        by (metis (mono_tags, lifting) scaleC_right.sum sum.cong)      
      ultimately show ?thesis 
        using that unfolding free_map_def
        by auto
    qed
  qed
qed

functor free_map
proof
  show "(free_map (f::'b \<Rightarrow> 'c) \<circ> free_map g) (x::'a free) = free_map (f \<circ> g) x"
    for f :: "'b \<Rightarrow> 'c"
      and g :: "'a \<Rightarrow> 'b"
      and x :: "'a free"
  proof-
    have \<open>clinear (free_map f)\<close>
      by (simp add: free_map_clinear)
    have \<open>(free_map f \<circ> free_map g) x = free_map f (free_map g x)\<close>
      by simp
    also have \<open>\<dots> = free_map f (\<Sum>a\<in>{a|a. x\<down>a \<noteq> 0}. (x\<down>a) *\<^sub>C inclusion_free (g a))\<close>
      using free_map_def
      by metis 
    also have \<open>\<dots> = (\<Sum>a\<in>{a|a. x\<down>a \<noteq> 0}. (x\<down>a) *\<^sub>C ((free_map f) (inclusion_free (g a))))\<close>
      using  \<open>clinear (free_map f)\<close>
      by (smt complex_vector.linear_scale complex_vector.linear_sum sum.cong)
    also have \<open>\<dots> = (\<Sum>a\<in>{a|a. x\<down>a \<noteq> 0}. (x\<down>a) *\<^sub>C inclusion_free ((f \<circ> g) a))\<close>
    proof-
      have \<open>(free_map f) (inclusion_free (g i)) = inclusion_free ((f \<circ> g) i)\<close>
        for i
      proof-
        have \<open>(free_map f) (inclusion_free (g i)) =
         (\<Sum>a\<in>{a |a. inclusion_free (g i) \<down> a \<noteq> 0}.
                (inclusion_free (g i) \<down> a) *\<^sub>C inclusion_free (f a))\<close>
          unfolding free_map_def
          by blast
        also have \<open>\<dots> = (\<Sum>a\<in>{a |a. inclusion_free ((f \<circ> g) i) \<down> a \<noteq> 0}.
                (inclusion_free ((f \<circ> g) i) \<down> a) *\<^sub>C (inclusion_free a))\<close>
        proof-
          have \<open>(\<Sum>a\<in>{a |a. inclusion_free (g i) \<down> a \<noteq> 0}.
       (inclusion_free (g i) \<down> a) *\<^sub>C inclusion_free (f a))
          = inclusion_free (f (g i))\<close>
          proof-
            have \<open>finite {a |a. inclusion_free (g i) \<down> a \<noteq> 0}\<close>
              using times_free_vec
              by blast
            moreover have \<open>g i \<in> {a |a. inclusion_free (g i) \<down> a \<noteq> 0}\<close>
              apply transfer
              by simp
            ultimately have \<open>(\<Sum>a\<in>{a |a. inclusion_free (g i) \<down> a \<noteq> 0}.
       (inclusion_free (g i) \<down> a) *\<^sub>C inclusion_free (f a))
          = ((inclusion_free (g i) \<down> (g i)) *\<^sub>C inclusion_free (f (g i)))
          + (\<Sum>a\<in>{a |a. inclusion_free (g i) \<down> a \<noteq> 0}-{g i}.
       (inclusion_free (g i) \<down> a) *\<^sub>C inclusion_free (f a))\<close>
              by (simp add: sum.remove)              
            also have \<open>\<dots> = ((inclusion_free (g i) \<down> (g i)) *\<^sub>C inclusion_free (f (g i)))\<close>
            proof-
              have \<open>j\<in>{a |a. inclusion_free (g i) \<down> a \<noteq> 0}-{g i} \<Longrightarrow>
                     (inclusion_free (g i) \<down> j) *\<^sub>C inclusion_free (f j) = 0\<close>
                for j
              proof-
                assume \<open>j\<in>{a |a. inclusion_free (g i) \<down> a \<noteq> 0}-{g i}\<close>
                hence \<open>j \<noteq> g i\<close>
                  by simp
                hence \<open>inclusion_free (g i) \<down> j = 0\<close>
                  by (simp add: inclusion_free.rep_eq)
                thus ?thesis by simp
              qed
              hence \<open>(\<Sum>a\<in>{a |a. inclusion_free (g i) \<down> a \<noteq> 0}-{g i}.
              (inclusion_free (g i) \<down> a) *\<^sub>C inclusion_free (f a)) = 0\<close>
                by simp
              thus ?thesis by simp
            qed
            also have \<open>\<dots> = inclusion_free (f (g i))\<close>
            proof-
              have \<open>inclusion_free (g i) \<down> (g i) = 1\<close>
                by (simp add: inclusion_free.rep_eq)
              thus ?thesis by simp
            qed
            finally show ?thesis by blast
          qed
          moreover have \<open>(\<Sum>a\<in>{a |a. inclusion_free ((f \<circ> g) i) \<down> a \<noteq> 0}.
                     (inclusion_free ((f \<circ> g) i) \<down> a) *\<^sub>C inclusion_free a)
          = inclusion_free (f (g i))\<close>
          proof-
            have \<open>finite {a |a. inclusion_free ((f \<circ> g) i) \<down> a \<noteq> 0}\<close>
              using times_free_vec by simp
            moreover have \<open>(f \<circ> g) i \<in> {a |a. inclusion_free ((f \<circ> g) i) \<down> a \<noteq> 0}\<close>
              by (simp add: inclusion_free.rep_eq)              
            ultimately have \<open>(\<Sum>a\<in>{a |a. inclusion_free ((f \<circ> g) i) \<down> a \<noteq> 0}.
                     (inclusion_free ((f \<circ> g) i) \<down> a) *\<^sub>C inclusion_free a)
              = (inclusion_free ((f \<circ> g) i) \<down> ((f \<circ> g) i)) *\<^sub>C inclusion_free ((f \<circ> g) i)
                  + (\<Sum>a\<in>{a |a. inclusion_free ((f \<circ> g) i) \<down> a \<noteq> 0}-{(f \<circ> g) i}.
                     (inclusion_free ((f \<circ> g) i) \<down> a) *\<^sub>C inclusion_free a)\<close>
              by (simp add: sum.remove)
            also have \<open>\<dots> = (inclusion_free ((f \<circ> g) i) \<down> ((f \<circ> g) i)) *\<^sub>C inclusion_free ((f \<circ> g) i)\<close>
            proof-
              have \<open>j\<in>{a |a. inclusion_free ((f \<circ> g) i) \<down> a \<noteq> 0}-{(f \<circ> g) i} \<Longrightarrow> 
                  (inclusion_free ((f \<circ> g) i) \<down> j) *\<^sub>C inclusion_free j = 0\<close>
                for j
              proof-
                assume \<open>j\<in>{a |a. inclusion_free ((f \<circ> g) i) \<down> a \<noteq> 0}-{(f \<circ> g) i}\<close>
                hence \<open>j \<noteq> (f \<circ> g) i\<close>
                  by simp
                hence \<open>inclusion_free ((f \<circ> g) i) \<down> j = 0\<close>
                  by (simp add: inclusion_free.rep_eq)
                thus ?thesis by simp
              qed
              hence \<open>(\<Sum>a\<in>{a |a. inclusion_free ((f \<circ> g) i) \<down> a \<noteq> 0}-{(f \<circ> g) i}.
                     (inclusion_free ((f \<circ> g) i) \<down> a) *\<^sub>C inclusion_free a) = 0\<close>
                by simp
              thus ?thesis by simp
            qed
            also have  \<open>\<dots> = inclusion_free ((f \<circ> g) i)\<close>
            proof-
              have \<open>(inclusion_free ((f \<circ> g) i) \<down> ((f \<circ> g) i)) = 1\<close>
                by (simp add: inclusion_free.rep_eq)                
              thus ?thesis by simp
            qed
            finally show ?thesis by simp
          qed
          ultimately show \<open>(\<Sum>a\<in>{a |a. inclusion_free (g i) \<down> a \<noteq> 0}.
       (inclusion_free (g i) \<down> a) *\<^sub>C inclusion_free (f a)) =
                (\<Sum>a\<in>{a |a. inclusion_free ((f \<circ> g) i) \<down> a \<noteq> 0}.
       (inclusion_free ((f \<circ> g) i) \<down> a) *\<^sub>C inclusion_free a)\<close>
            by simp
        qed
        also have \<open>\<dots> =  inclusion_free ((f \<circ> g) i)\<close>
          by (metis (no_types) free_explicit)          
        finally show ?thesis by blast
      qed
      thus ?thesis by simp
    qed
    also have \<open>\<dots> = free_map (f \<circ> g) x\<close>
      by (metis free_map_def)      
    finally have \<open>(free_map f \<circ> free_map g) x = free_map (f \<circ> g) x\<close>
      by blast
    thus ?thesis by blast
  qed
  show "free_map (id::'a \<Rightarrow> _) = id"
  proof
    show "free_map id (x::'a free) = id x"
      for x :: "'a free"
    proof-
      have \<open>(\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free (id a)) \<down> i = x \<down> i\<close>
        for i
      proof-
        have \<open>(\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free (id a)) \<down> i = 
            (\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free a) \<down> i \<close>
          by simp
        also have \<open>\<dots> = (\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. ((x \<down> a) *\<^sub>C inclusion_free a) \<down> i)\<close>
        proof-
          define f::\<open>'a free \<Rightarrow> complex\<close> where \<open>f t = t \<down> i\<close> for t
          define \<gamma> where \<open>\<gamma> a = ((x \<down> a) *\<^sub>C inclusion_free a)\<close> for a
          define S where \<open>S = \<gamma> ` {a |a. x \<down> a \<noteq> 0}\<close>
          have \<open>f (p + q) = f p + f q\<close>
            for p q
            by (simp add: \<open>f \<equiv> \<lambda>t. t \<down> i\<close> free_regular_for_sum)          
          moreover have \<open>finite {a |a. x \<down> a \<noteq> 0}\<close>
            using times_free_vec by force
          ultimately have \<open>f (\<Sum>a\<in>S. a) = (\<Sum>a\<in>S. f a)\<close>
            using general_sum_from_addition
            by (simp add: general_sum_from_addition S_def)
          thus ?thesis unfolding S_def f_def \<gamma>_def
            using \<open>finite {a |a. x \<down> a \<noteq> 0}\<close> free_regular_for_sum_general 
            by fastforce
        qed
        also have \<open>\<dots> = ((x \<down> i) *\<^sub>C inclusion_free i) \<down> i\<close>
        proof (cases \<open>i \<in> {a |a. x \<down> a \<noteq> 0}\<close>)
          show "(\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free a \<down> i) = (x \<down> i) *\<^sub>C inclusion_free i \<down> i"
            if "i \<in> {a |a. x \<down> a \<noteq> 0}"
          proof-
            have \<open>finite {a |a. x \<down> a \<noteq> 0}\<close>
              using times_free_vec by fastforce                        
            hence \<open>(\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free a \<down> i) = (x \<down> i) *\<^sub>C inclusion_free i \<down> i
              + (\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}-{i}. (x \<down> a) *\<^sub>C inclusion_free a \<down> i)\<close>
              using sum.remove that by fastforce 
            moreover have \<open>(\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}-{i}. (x \<down> a) *\<^sub>C inclusion_free a \<down> i) = 0\<close>
            proof-
              have \<open>j\<in>{a |a. x \<down> a \<noteq> 0}-{i} \<Longrightarrow> (x \<down> j) *\<^sub>C inclusion_free j \<down> i = 0\<close>
                for j 
              proof-
                assume \<open>j\<in>{a |a. x \<down> a \<noteq> 0}-{i}\<close>
                hence \<open>j \<noteq> i\<close>
                  by auto
                thus ?thesis
                  by (metis complex_vector.scale_eq_0_iff inclusion_free.rep_eq scaleC_free.rep_eq)
              qed
              thus ?thesis
                by simp 
            qed
            ultimately show ?thesis by simp
          qed
          show "(\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free a \<down> i) = (x \<down> i) *\<^sub>C inclusion_free i \<down> i"
            if "i \<notin> {a |a. x \<down> a \<noteq> 0}"
          proof-
            have \<open>(\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free a \<down> i) = 0\<close>
            proof-
              have \<open>j\<in>{a |a. x \<down> a \<noteq> 0} \<Longrightarrow> (x \<down> j) *\<^sub>C inclusion_free j \<down> i = 0\<close>
                for j 
              proof-
                assume \<open>j\<in>{a |a. x \<down> a \<noteq> 0}\<close>
                hence \<open>j \<noteq> i\<close>
                  using that by auto
                thus ?thesis
                  by (metis complex_vector.scale_eq_0_iff inclusion_free.rep_eq scaleC_free.rep_eq) 
              qed
              thus ?thesis
                by simp 
            qed
            moreover have \<open>(x \<down> i) *\<^sub>C inclusion_free i \<down> i = 0\<close>
              by (metis (mono_tags, lifting) complex_vector.scale_eq_0_iff mem_Collect_eq scaleC_free.rep_eq that)            
            ultimately show ?thesis by simp
          qed
        qed
        also have \<open>\<dots> = (x \<down> i)\<close>
          by (metis \<open>(\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free a \<down> i) = (x \<down> i) *\<^sub>C inclusion_free i \<down> i\<close> \<open>(\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free a) \<down> i = (\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free a \<down> i)\<close> free_explicit)        
        finally show ?thesis by blast
      qed
      hence \<open>times_free_vec (\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free (id a)) 
        = times_free_vec x\<close>
        by blast
      hence \<open>(\<Sum>a\<in>{a |a. x \<down> a \<noteq> 0}. (x \<down> a) *\<^sub>C inclusion_free (id a)) = x\<close>
        using times_free_vec_inject by auto
      thus ?thesis 
        unfolding free_map_def
        by auto
    qed
  qed
qed


unbundle no_free_notation

end
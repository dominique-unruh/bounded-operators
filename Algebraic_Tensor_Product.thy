(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Algebraic_Tensor_Product
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

lift_definition embed_free:: \<open>'a \<Rightarrow> 'a free\<close>
  is \<open>\<lambda> a::'a. (\<lambda> x. if x = a then 1 else 0)\<close>
  by simp


definition atensor_kernel::\<open>( (('a::complex_vector) \<times> ('b::complex_vector)) free ) set\<close> where
  \<open>atensor_kernel = complex_vector.span ( 
  {embed_free (x, (y+z)) - embed_free (x, y) - embed_free (x, z) |  x y z. True}
\<union> { embed_free ((y+z), x) - embed_free (y, x) - embed_free (z, x) |  x y z. True}
\<union> { embed_free (x, (c *\<^sub>C y)) -  c *\<^sub>C embed_free (x, y) |  x y c. True} 
\<union> { embed_free ((c *\<^sub>C x), y) -  c *\<^sub>C embed_free (x, y) |  x y c. True} )\<close>

lemma subspace_atensor_kernel:
  \<open>complex_vector.subspace atensor_kernel\<close>
  unfolding atensor_kernel_def
  using Complex_Vector_Spaces.complex_vector.subspace_span
  by blast

definition atensor_rel :: "(('a::complex_vector) \<times> ('b::complex_vector)) free \<Rightarrow> ('a \<times> 'b) free \<Rightarrow> bool"
  where "atensor_rel = (\<lambda>x y. x - y \<in> atensor_kernel)"

text\<open>Tensor product as defined in @{cite Helemskii} chapter 2, section 8\<close>
quotient_type (overloaded) ('a, 'b) atensor 
  = "(('a::complex_vector) \<times> ('b::complex_vector)) free" /  atensor_rel
  (* TODO proof (rule equivpI) would leads to a clearer proof, I think *)
  unfolding equivp_def proof
  show "\<forall>y. atensor_rel (x::('a \<times> 'b) free) y = (atensor_rel x = atensor_rel y)"
    for x :: "('a \<times> 'b) free"
  proof
    show "atensor_rel x y = (atensor_rel x = atensor_rel y)"
      for y :: "('a \<times> 'b) free"
    proof
      show "atensor_rel x = atensor_rel y"
        if "atensor_rel x y"
        using that unfolding atensor_rel_def
      proof-
        assume \<open>x - y \<in> atensor_kernel\<close>
        hence \<open>x - z \<in> atensor_kernel \<longleftrightarrow> y - z \<in> atensor_kernel\<close> 
          for z
        proof (cases \<open>x - z \<in> atensor_kernel\<close>)
          show "(x - z \<in> atensor_kernel) = (y - z \<in> atensor_kernel)"
            if "x - y \<in> atensor_kernel"
              and "x - z \<in> atensor_kernel"
          proof-
            have \<open>complex_vector.subspace atensor_kernel\<close>
              using subspace_atensor_kernel
              by blast
            hence \<open>(x - z) - (y - z) \<in> atensor_kernel\<close>
              using that 
              by auto 
            thus ?thesis
              by (metis (no_types, lifting) atensor_kernel_def complex_vector.span_add_eq diff_add_cancel)
          qed
          show "(x - z \<in> atensor_kernel) = (y - z \<in> atensor_kernel)"
            if "x - y \<in> atensor_kernel"
              and "x - z \<notin> atensor_kernel"
          proof-
            have \<open>y - z \<notin> atensor_kernel\<close>
            proof(rule classical)
              assume \<open>\<not>(y - z \<notin> atensor_kernel)\<close>
              hence  \<open>y - z \<in> atensor_kernel\<close>
                by blast
              moreover have \<open>x - z = (x - y) + (y - z)\<close>
                by simp
              moreover have \<open>complex_vector.subspace atensor_kernel\<close>
                using subspace_atensor_kernel
                by blast
              ultimately have \<open>x - z \<in> atensor_kernel\<close>
                by (smt complex_vector.subspace_add that(1))                
              thus ?thesis
                using that(2) by blast 
            qed
            thus ?thesis
              using that(2) by auto 
          qed
        qed
        thus \<open>(\<lambda>p. x - p \<in> atensor_kernel) = (\<lambda>q. y - q \<in> atensor_kernel)\<close>
          by simp          
      qed
      show "atensor_rel x y"
        if "atensor_rel x = atensor_rel y"
        using that unfolding atensor_rel_def 
      proof-
        assume \<open>(\<lambda>p. x - p \<in> atensor_kernel) = (\<lambda>q. y - q \<in> atensor_kernel)\<close>
        hence \<open>x - z \<in> atensor_kernel \<longleftrightarrow> y - z \<in> atensor_kernel\<close> 
          for z
          by meson
        hence \<open>x - y \<in> atensor_kernel \<longleftrightarrow> y - y \<in> atensor_kernel\<close> 
          by blast
        moreover have \<open>y - y \<in> atensor_kernel\<close>
        proof-
          have \<open>0 \<in> atensor_kernel\<close>
            unfolding atensor_kernel_def
            by (simp add: complex_vector.span_zero)
          moreover have \<open>y - y = 0\<close>
            by simp
          ultimately show ?thesis by simp
        qed
        ultimately show \<open>x - y \<in> atensor_kernel\<close>
          by blast
      qed
    qed
  qed
qed



type_notation
  atensor  ("(_ \<otimes>\<^sub>a/ _)" [21, 20] 20)

lift_definition atensor_op:: \<open>'a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>  (infixl "\<otimes>\<^sub>a" 70)
  is \<open>\<lambda> x::'a. \<lambda> y::'b. embed_free (x, y)\<close>.

instantiation atensor :: (complex_vector,complex_vector) complex_vector
begin

lift_definition plus_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> x y. x + y\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2 p3 p4 :: \<open>('a \<times> 'b) free\<close>
  assume \<open>p1 - p2 \<in> atensor_kernel\<close> and \<open>p3 - p4 \<in> atensor_kernel\<close>
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel by blast
  ultimately have \<open>(p1 - p2) + (p3 - p4) \<in> atensor_kernel\<close>
    using complex_vector.subspace_add by blast
  moreover have \<open>(p1 - p2) + (p3 - p4) = (p1 + p3) - (p2 + p4)\<close>
    by simp
  ultimately show \<open>(p1 + p3) - (p2 + p4) \<in> atensor_kernel\<close>
    by simp
qed

lift_definition minus_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> x y. x - y\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2 p3 p4 :: \<open>('a \<times> 'b) free\<close>
  assume \<open>p1 - p2 \<in> atensor_kernel\<close> and \<open>p3 - p4 \<in> atensor_kernel\<close>
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel by blast
  ultimately have \<open>(p1 - p2) - (p3 - p4) \<in> atensor_kernel\<close>
    using complex_vector.subspace_diff by blast
  moreover have \<open>(p1 - p2) - (p3 - p4) = (p1 - p3) - (p2 - p4)\<close>
    by simp
  ultimately show \<open>(p1 - p3) - (p2 - p4) \<in> atensor_kernel\<close>
    by simp
qed

lift_definition zero_atensor :: \<open>'a \<otimes>\<^sub>a 'b\<close>
  is \<open>0\<close>.

lift_definition scaleR_atensor :: \<open>real \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> c x. c *\<^sub>R x\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2::\<open>('a \<times> 'b) free\<close> and c::real
  assume \<open>p1 - p2 \<in> atensor_kernel\<close> 
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel
    by blast
  ultimately have \<open>c *\<^sub>R (p1 - p2) \<in> atensor_kernel\<close>
    by (simp add: \<open>complex_vector.subspace atensor_kernel\<close> complex_vector.subspace_scale scaleR_scaleC)
  show \<open>c *\<^sub>R p1 - c *\<^sub>R p2 \<in> atensor_kernel\<close>
    by (metis \<open>c *\<^sub>R (p1 - p2) \<in> atensor_kernel\<close> ordered_field_class.sign_simps(26))
qed

lift_definition scaleC_atensor :: \<open>complex \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> c x. c *\<^sub>C x\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2::\<open>('a \<times> 'b) free\<close> and c::complex
  assume \<open>p1 - p2 \<in> atensor_kernel\<close> 
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel
    by blast
  ultimately have \<open>c *\<^sub>C (p1 - p2) \<in> atensor_kernel\<close>
    by (simp add: \<open>complex_vector.subspace atensor_kernel\<close> complex_vector.subspace_scale)
  show \<open>c *\<^sub>C p1 - c *\<^sub>C p2 \<in> atensor_kernel\<close>
    by (metis (no_types) \<open>c *\<^sub>C (p1 - p2) \<in> atensor_kernel\<close> complex_vector.scale_right_diff_distrib)
qed

lift_definition uminus_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close>
  is \<open>\<lambda> x. -x\<close>
  unfolding atensor_rel_def
proof-
  fix p1 p2 :: \<open>('a \<times> 'b) free\<close>
  assume \<open>p1 - p2 \<in> atensor_kernel\<close>
  moreover have \<open>complex_vector.subspace atensor_kernel\<close>
    using subspace_atensor_kernel
    by blast
  ultimately have \<open>-(p1 - p2) \<in> atensor_kernel\<close>
    using complex_vector.subspace_neg by blast    
  thus \<open>- p1 - - p2 \<in> atensor_kernel\<close>
    by simp
qed

instance
proof
  show "((*\<^sub>R) r::'a \<otimes>\<^sub>a 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)"
    for r :: real
    unfolding scaleC_atensor_def scaleR_atensor_def 
    apply auto
  proof-
    have \<open>((*\<^sub>R) r) = ((*\<^sub>C) (complex_of_real r))\<close>
      by (simp add: scaleR_scaleC)      
    show \<open>map_fun rep_atensor abs_atensor ((*\<^sub>R) r) =
    map_fun rep_atensor abs_atensor
     ((*\<^sub>C) (complex_of_real r))\<close>
      by (simp add: \<open>(*\<^sub>R) r = (*\<^sub>C) (complex_of_real r)\<close>)
  qed

  show "(a::'a \<otimes>\<^sub>a 'b) + b + c = a + (b + c)"
    for a :: "'a \<otimes>\<^sub>a 'b"
      and b :: "'a \<otimes>\<^sub>a 'b"
      and c :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    apply auto 
    using subspace_atensor_kernel 
    unfolding complex_vector.subspace_def
    by blast

  show "(a::'a \<otimes>\<^sub>a 'b) + b = b + a"
    for a :: "'a \<otimes>\<^sub>a 'b"
      and b :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    apply auto 
    using subspace_atensor_kernel 
    unfolding complex_vector.subspace_def
    by blast

  show "(0::'a \<otimes>\<^sub>a 'b) + a = a"
    for a :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    apply auto 
    using subspace_atensor_kernel 
    unfolding complex_vector.subspace_def
    by blast

  show "- (a::'a \<otimes>\<^sub>a 'b) + a = 0"
    for a :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    apply auto 
    using subspace_atensor_kernel 
    unfolding complex_vector.subspace_def
    by blast

  show "(a::'a \<otimes>\<^sub>a 'b) - b = a + - b"
    for a :: "'a \<otimes>\<^sub>a 'b"
      and b :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    apply auto 
    using subspace_atensor_kernel 
    unfolding complex_vector.subspace_def
    by blast

  show "a *\<^sub>C ((x::'a \<otimes>\<^sub>a 'b) + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex
      and x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    using subspace_atensor_kernel
    by (simp add: subspace_atensor_kernel complex_vector.subspace_0 scaleC_add_right) 

  show "(a + b) *\<^sub>C (x::'a \<otimes>\<^sub>a 'b) = a *\<^sub>C x + b *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    using subspace_atensor_kernel
    by (simp add: subspace_atensor_kernel complex_vector.subspace_0 scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C (x::'a \<otimes>\<^sub>a 'b) = (a * b) *\<^sub>C x"
    for a :: complex
      and b :: complex
      and x :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    using subspace_atensor_kernel
    by (simp add: subspace_atensor_kernel complex_vector.subspace_0)

  show "1 *\<^sub>C (x::'a \<otimes>\<^sub>a 'b) = x"
    for x :: "'a \<otimes>\<^sub>a 'b"
    apply transfer unfolding atensor_rel_def
    using subspace_atensor_kernel
    by (simp add: subspace_atensor_kernel complex_vector.subspace_0)

qed
end


lemma atensor_distr_right:
  fixes x y z :: "'a::complex_vector"
  shows  \<open>x \<otimes>\<^sub>a (y+z) =  x \<otimes>\<^sub>a y  +  x \<otimes>\<^sub>a z\<close>
(* TODO: without unfolding atensor_kernel_def, the proof will be more readable (because atensor_kernel
can be used instead of writing out its definition twice in the proof *)
(* TODO: you can write "proof (transfer, unfold ...)" *)
  apply transfer unfolding atensor_rel_def atensor_kernel_def
proof-
  fix x y z::'a
  have \<open>embed_free (x, y + z) - (embed_free (x, y) + embed_free (x, z))
  \<in> {embed_free (x, y + z) - embed_free (x, y) - embed_free (x, z) |x y z. True}\<close>
    by (metis (mono_tags, lifting) diff_diff_add mem_Collect_eq)    
  hence \<open>embed_free (x, y + z) - (embed_free (x, y) + embed_free (x, z))
  \<in> ({embed_free (x, y + z) - embed_free (x, y) - embed_free (x, z) |x y z. True} \<union>
            {embed_free (y + z, x) - embed_free (y, x) - embed_free (z, x) |x y z. True} \<union>
            {embed_free (x, c *\<^sub>C y) - c *\<^sub>C embed_free (x, y) |x y c. True} \<union>
            {embed_free (c *\<^sub>C x, y) - c *\<^sub>C embed_free (x, y) |x y c. True})\<close>
    by simp
  thus \<open>embed_free (x, y + z) - (embed_free (x, y) + embed_free (x, z))
       \<in> complex_vector.span
           ({embed_free (x, y + z) - embed_free (x, y) - embed_free (x, z) |x y z. True} \<union>
            {embed_free (y + z, x) - embed_free (y, x) - embed_free (z, x) |x y z. True} \<union>
            {embed_free (x, c *\<^sub>C y) - c *\<^sub>C embed_free (x, y) |x y c. True} \<union>
            {embed_free (c *\<^sub>C x, y) - c *\<^sub>C embed_free (x, y) |x y c. True})\<close>
    by (simp add: complex_vector.span_base)
qed

lemma atensor_distr_left:
  fixes x y z :: "'a::complex_vector"
  shows  \<open>(y+z) \<otimes>\<^sub>a x =  y \<otimes>\<^sub>a x  +  z \<otimes>\<^sub>a x\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def
proof-
  fix x y z::'a
  have \<open>embed_free (y + z, x) - (embed_free (y, x) + embed_free (z, x))
       \<in> {embed_free (y + z, x) - embed_free (y, x) - embed_free (z, x) |x y z. True}\<close>
    by (metis (mono_tags, lifting) diff_diff_add mem_Collect_eq)
  hence \<open>embed_free (y + z, x) - (embed_free (y, x) + embed_free (z, x))
       \<in> ({embed_free (x, y + z) - embed_free (x, y) - embed_free (x, z) |x y z. True} \<union>
            {embed_free (y + z, x) - embed_free (y, x) - embed_free (z, x) |x y z. True} \<union>
            {embed_free (x, c *\<^sub>C y) - c *\<^sub>C embed_free (x, y) |x y c. True} \<union>
            {embed_free (c *\<^sub>C x, y) - c *\<^sub>C embed_free (x, y) |x y c. True})\<close>
    by simp
  thus \<open> embed_free (y + z, x) - (embed_free (y, x) + embed_free (z, x))
       \<in> complex_vector.span
           ({embed_free (x, y + z) - embed_free (x, y) - embed_free (x, z) |x y z. True} \<union>
            {embed_free (y + z, x) - embed_free (y, x) - embed_free (z, x) |x y z. True} \<union>
            {embed_free (x, c *\<^sub>C y) - c *\<^sub>C embed_free (x, y) |x y c. True} \<union>
            {embed_free (c *\<^sub>C x, y) - c *\<^sub>C embed_free (x, y) |x y c. True})\<close>
    by (simp add: complex_vector.span_base)
qed

lemma atensor_mult_right:
  fixes x y :: "'a::complex_vector" and c :: complex
  shows \<open>x \<otimes>\<^sub>a (c *\<^sub>C y) = c *\<^sub>C (x \<otimes>\<^sub>a y)\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def
proof-
  fix x y :: 'a and c :: complex
  have \<open>embed_free (x, c *\<^sub>C y) - c *\<^sub>C embed_free (x, y)
       \<in> {embed_free (x, c *\<^sub>C y) - c *\<^sub>C embed_free (x, y) |x y c. True}\<close>
    by (metis (mono_tags, lifting) mem_Collect_eq)
  hence \<open>embed_free (x, c *\<^sub>C y) - c *\<^sub>C embed_free (x, y)
       \<in> ({embed_free (x, y + z) - embed_free (x, y) - embed_free (x, z) |x y z. True} \<union>
            {embed_free (y + z, x) - embed_free (y, x) - embed_free (z, x) |x y z. True} \<union>
            {embed_free (x, c *\<^sub>C y) - c *\<^sub>C embed_free (x, y) |x y c. True} \<union>
            {embed_free (c *\<^sub>C x, y) - c *\<^sub>C embed_free (x, y) |x y c. True})\<close>
    by simp
  thus \<open>embed_free (x, c *\<^sub>C y) - c *\<^sub>C embed_free (x, y)
       \<in> complex_vector.span
           ({embed_free (x, y + z) - embed_free (x, y) - embed_free (x, z) |x y z. True} \<union>
            {embed_free (y + z, x) - embed_free (y, x) - embed_free (z, x) |x y z. True} \<union>
            {embed_free (x, c *\<^sub>C y) - c *\<^sub>C embed_free (x, y) |x y c. True} \<union>
            {embed_free (c *\<^sub>C x, y) - c *\<^sub>C embed_free (x, y) |x y c. True})\<close>
    by (simp add: complex_vector.span_base)
qed


lemma atensor_mult_left:
  fixes x y :: "'a::complex_vector" and c :: complex
  shows \<open>(c *\<^sub>C x) \<otimes>\<^sub>a y  = c *\<^sub>C (x \<otimes>\<^sub>a y)\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def
  apply auto
  by (metis (mono_tags, lifting) Un_iff complex_vector.span_base mem_Collect_eq)

lemma free_regular_for_sum:
  fixes x y :: \<open>'a free\<close>
  shows \<open>Rep_free (x + y) t = Rep_free x t + Rep_free y t\<close>
  apply transfer
  by auto


lemma free_regular_for_sum_general_induction:
  fixes x :: \<open>'a free\<close>
  shows \<open>\<forall> S. finite S \<and> card S = n \<longrightarrow> Rep_free ( \<Sum> u \<in> S. ((Rep_free x) u) *\<^sub>C (embed_free u) ) t
  = (\<Sum> u \<in> S. Rep_free ( ((Rep_free x) u) *\<^sub>C (embed_free u) ) t )\<close>
proof (induction n)
  show "\<forall>S. finite S \<and> card S = 0 \<longrightarrow> Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C embed_free u) t = (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C embed_free u) t)"
    by (metis (no_types, lifting) card_0_eq sum_clauses(1) zero_free.rep_eq)
  show "\<forall>S. finite S \<and> card S = Suc n \<longrightarrow> Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C embed_free u) t = (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C embed_free u) t)"
    if "\<forall>S. finite S \<and> card S = n \<longrightarrow> Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C embed_free u) t = (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C embed_free u) t)"
    for n :: nat
  proof-
    have \<open>finite S \<Longrightarrow> card S = Suc n \<Longrightarrow> Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C embed_free u) t = (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C embed_free u) t)\<close>
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
      ultimately have \<open>Rep_free (\<Sum>u\<in>R. Rep_free x u *\<^sub>C embed_free u) t = (\<Sum>u\<in>R. Rep_free (Rep_free x u *\<^sub>C embed_free u) t)\<close>
        by (simp add: that)
      hence \<open>Rep_free (\<Sum>u\<in>R. Rep_free x u *\<^sub>C embed_free u) t + Rep_free (Rep_free x r *\<^sub>C embed_free r) t
         = (\<Sum>u\<in>R. Rep_free (Rep_free x u *\<^sub>C embed_free u) t) + Rep_free (Rep_free x r *\<^sub>C embed_free r) t\<close>
        by simp
      moreover have \<open>Rep_free (\<Sum>u\<in>R. Rep_free x u *\<^sub>C embed_free u) t + Rep_free (Rep_free x r *\<^sub>C embed_free r) t
          = Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C embed_free u) t\<close>
        by (simp add: \<open>S = insert r R\<close> \<open>finite R\<close> \<open>r \<notin> R\<close> plus_free.rep_eq)        
      moreover have \<open>(\<Sum>u\<in>R. Rep_free (Rep_free x u *\<^sub>C embed_free u) t) + Rep_free (Rep_free x r *\<^sub>C embed_free r) t
          =  (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C embed_free u) t)\<close>
        by (simp add: \<open>S = insert r R\<close> \<open>finite R\<close> \<open>r \<notin> R\<close>)        
      ultimately show \<open>Rep_free (\<Sum>u\<in>S. Rep_free x u *\<^sub>C embed_free u) t = (\<Sum>u\<in>S. Rep_free (Rep_free x u *\<^sub>C embed_free u) t)\<close>
        by simp
    qed
    thus ?thesis by blast
  qed
qed


lemma free_regular_for_sum_general:
  fixes x :: \<open>'a free\<close>
  assumes \<open>finite S\<close>
  shows \<open>Rep_free ( \<Sum> u \<in> S. ((Rep_free x) u) *\<^sub>C (embed_free u) ) t
  = (\<Sum> u \<in> S. Rep_free ( ((Rep_free x) u) *\<^sub>C (embed_free u) ) t )\<close>
  using free_regular_for_sum_general_induction assms
  by (simp add: free_regular_for_sum_general_induction) 

lemma free_pair_explicit:
  fixes X :: \<open>('a::complex_vector \<times> 'b::complex_vector) free\<close>
  shows \<open>X = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (embed_free z))\<close>
proof-
  have \<open>(Rep_free X) t = (Rep_free (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (embed_free z))) t\<close>
    for t
  proof (cases \<open>t \<in> {u | u. (Rep_free X) u \<noteq> 0}\<close>)
    show "Rep_free X t = Rep_free (\<Sum>z\<in>{u |u. Rep_free X u \<noteq> 0}. Rep_free X z *\<^sub>C embed_free z) t"
      if "t \<in> {u |u. Rep_free X u \<noteq> 0}"
    proof-
      have \<open>finite {u | u. (Rep_free X) u \<noteq> 0}\<close>
        using Rep_free by force
      hence \<open>(Rep_free (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (embed_free z))) t
        = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t ) \<close>
        using free_regular_for_sum_general[where S = "{u | u. (Rep_free X) u \<noteq> 0}" and x = "X" and t = "t"]
        by blast
      moreover have \<open>(\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t ) = Rep_free X t\<close>
      proof-
        have \<open>(\<Sum>z\<in>{t}. Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t ) = Rep_free X t\<close>
        proof-
          have \<open>(\<Sum>z\<in>{t}. Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t )
            = Rep_free ( ((Rep_free X) t) *\<^sub>C (embed_free t) ) t \<close>
            by simp
          also have \<open>\<dots> = (Rep_free X) t\<close>
            apply transfer
            by auto
          finally show ?thesis by blast
        qed
        moreover have \<open>(\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0} - {t}. Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t ) = 0\<close>
        proof-
          have \<open>z\<in>{u | u. (Rep_free X) u \<noteq> 0} - {t} \<Longrightarrow> 
                Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t  = 0\<close>
            for z
          proof-
            assume \<open>z\<in>{u | u. (Rep_free X) u \<noteq> 0} - {t}\<close>
            hence \<open>z \<noteq> t\<close>
              by simp
            hence \<open>Rep_free (embed_free z) t = 0\<close>
              apply transfer by auto
            thus \<open>Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t  = 0\<close>
              by (simp add: scaleC_free.rep_eq)
          qed
          thus ?thesis by simp
        qed
        moreover have \<open>(\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t )
      = (\<Sum>z\<in>{t}. Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t )
      + (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0} - {t}. Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t )\<close>
          using \<open>finite {u |u. Rep_free X u \<noteq> 0}\<close> empty_iff sum.remove that by fastforce        
        ultimately show ?thesis by simp
      qed
      ultimately show \<open>(Rep_free X) t = (Rep_free (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (embed_free z))) t\<close>
        by simp      
    qed
    show "Rep_free X t = Rep_free (\<Sum>z\<in>{u |u. Rep_free X u \<noteq> 0}. Rep_free X z *\<^sub>C embed_free z) t"
      if "t \<notin> {u |u. Rep_free X u \<noteq> 0}"
    proof-
      have \<open>Rep_free X t = 0\<close>
        using that by simp
      moreover have \<open>Rep_free (\<Sum>z\<in>{u |u. Rep_free X u \<noteq> 0}. Rep_free X z *\<^sub>C embed_free z) t = 0\<close>
      proof-
        have \<open>(Rep_free (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (embed_free z))) t
        = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t ) \<close>
          using free_regular_for_sum_general[where S = "{u | u. (Rep_free X) u \<noteq> 0}" and x = "X" and t = "t"]
          by (metis (no_types, lifting) sum.infinite zero_free.rep_eq)
        also have \<open>\<dots> = 0\<close>
        proof-
          have \<open>z\<in>{u | u. (Rep_free X) u \<noteq> 0} \<Longrightarrow> Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t = 0\<close>
            for z
          proof-
            assume \<open>z\<in>{u | u. (Rep_free X) u \<noteq> 0}\<close>
            hence \<open>Rep_free (embed_free z) t = 0\<close>
              by (metis embed_free.rep_eq that)          
            thus \<open>Rep_free ( ((Rep_free X) z) *\<^sub>C (embed_free z) ) t = 0\<close>
              by (simp add: scaleC_free.rep_eq) 
          qed
          thus ?thesis by simp
        qed
        finally show ?thesis by blast
      qed
      ultimately show ?thesis by simp
    qed
  qed
  thus \<open>X = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (embed_free z))\<close>
    using Rep_free_inject by blast
qed


lemma abs_atensor_embed_free:
  \<open>abs_atensor (embed_free u) = (fst u) \<otimes>\<^sub>a (snd u)\<close>
proof-
  have \<open>complex_vector.subspace atensor_kernel\<close>
    by (simp add: subspace_atensor_kernel)
  hence \<open>atensor_rel (Abs_free (\<lambda>x. if x = u then 1 else 0))
          (embed_free (fst u, snd u))\<close>
    unfolding atensor_rel_def embed_free_def apply auto
    by (simp add: \<open>complex_vector.subspace atensor_kernel\<close> complex_vector.subspace_0) 
  thus ?thesis
    by (simp add: atensor_op.abs_eq) 
qed

lemma abs_atensor_sum:
  \<open>abs_atensor (x + y) = abs_atensor x + abs_atensor y\<close>
  by (simp add: plus_atensor.abs_eq)

lemma abs_atensor_sum_general:
  assumes \<open>finite S\<close>
  shows \<open>(\<Sum> x\<in>S. abs_atensor (f x)) = abs_atensor (\<Sum> x\<in>S. f x)\<close>
  using abs_atensor_sum
  by (smt Finite_Cartesian_Product.sum_cong_aux Modules.additive_def additive.sum assms)

lemma free_explicit:
  fixes  X :: \<open>('a::complex_vector \<times> 'b::complex_vector) free\<close>
  shows \<open>abs_atensor X = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}.  ((Rep_free X) z) *\<^sub>C ( (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
proof-                                        
  have \<open>X = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (embed_free z))\<close>
    using free_pair_explicit by auto
  hence  \<open>abs_atensor X = abs_atensor (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (embed_free z))\<close>
    by simp
  also have \<open>\<dots> = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. abs_atensor (((Rep_free X) z) *\<^sub>C (embed_free z)))\<close>
    by (metis (mono_tags, lifting) abs_atensor_sum_general sum.cong sum.infinite zero_atensor.abs_eq)
  also have \<open>\<dots> = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}.  ((Rep_free X) z) *\<^sub>C (abs_atensor (embed_free z)))\<close>
    by (metis scaleC_atensor.abs_eq)
  also have \<open>\<dots> = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}.  ((Rep_free X) z) *\<^sub>C ( (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
    by (simp add: abs_atensor_embed_free)
  finally show ?thesis by blast
qed

lemma atensor_onto_explicit:
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
  shows \<open>\<exists> S f. finite S \<and> x = (\<Sum>z\<in>S. (f z) *\<^sub>C ( (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
proof-
  have \<open>\<exists> X. x = abs_atensor X\<close>
    apply transfer using Rep_atensor apply auto
    using atensor.abs_eq_iff by blast
  then obtain X where \<open>x = abs_atensor X\<close> by blast
  moreover have \<open>abs_atensor X = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}.  ((Rep_free X) z) *\<^sub>C ( (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
    using free_explicit by blast
  moreover have \<open>finite {u | u. (Rep_free X) u \<noteq> 0}\<close>
    using Rep_free by blast
  ultimately show ?thesis
    by blast    
qed

lemma atensor_onto:
  \<open>complex_vector.span ( range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) )
 = ( UNIV::(('a::complex_vector \<otimes>\<^sub>a 'b::complex_vector) set) )\<close>
proof
  show "complex_vector.span (range (\<lambda>z. (fst z::'a) \<otimes>\<^sub>a (snd z::'b))) \<subseteq> UNIV"
    by simp    
  show "UNIV \<subseteq> complex_vector.span (range (\<lambda>z. (fst z::'a) \<otimes>\<^sub>a (snd z::'b)))"
  proof
    show "x \<in> complex_vector.span (range (\<lambda>z. (fst z::'a) \<otimes>\<^sub>a (snd z::'b)))"
      for x :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>\<exists> R g. finite R \<and> x = (\<Sum>z\<in>R.  (g z) *\<^sub>C ( (fst z) \<otimes>\<^sub>a (snd z) ))\<close>
        using atensor_onto_explicit by blast
      then obtain R g where \<open>finite R\<close> and \<open>x = (\<Sum>z\<in>R.  (g z) *\<^sub>C ( (fst z) \<otimes>\<^sub>a (snd z) ))\<close>
        by blast
      thus ?thesis
        by (metis (no_types, lifting) complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset image_subset_iff iso_tuple_UNIV_I)        
    qed
  qed
qed

lemma basis_subspace_atensor:
  \<open>\<exists> R. R \<subseteq> range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) \<and> 
  complex_independent R \<and> span R = UNIV\<close>
proof-
  have \<open>\<exists> R. R \<subseteq> ( range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) ) 
   \<and> complex_independent R \<and> span R = span ( range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
    by (metis (no_types, lifting) Complex_Vector_Spaces.span_raw_def complex_vector.independent_empty complex_vector.maximal_independent_subset_extend complex_vector.span_mono complex_vector.span_subspace complex_vector.subspace_span empty_subsetI)
  moreover have \<open>complex_vector.span ( range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) )
 = ( UNIV::(('a::complex_vector \<otimes>\<^sub>a 'b::complex_vector) set) )\<close>
    using atensor_onto by blast
  ultimately show ?thesis
    by (smt Complex_Vector_Spaces.span_raw_def) 
qed

definition cbilinear :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector) \<Rightarrow> bool\<close>
  where \<open>cbilinear \<equiv> (\<lambda> f. (\<forall> y. clinear (\<lambda> x. f x y)) \<and> (\<forall> x. clinear (\<lambda> y. f x y)) )\<close>

theorem atensor_universal_property:
  fixes h :: \<open>'v::complex_vector \<Rightarrow> 'w::complex_vector \<Rightarrow> 'z::complex_vector\<close>
  assumes \<open>cbilinear h\<close>
  shows \<open>\<exists>! H :: 'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z. clinear H \<and> (\<forall> x y. h x y = H (x \<otimes>\<^sub>a y))\<close>
proof-
  define H :: \<open>'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z\<close> where \<open>H = undefined\<close>
  have \<open>\<exists> R. R \<subseteq> range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) \<and> 
  complex_independent R \<and> span R = UNIV\<close>
    by (simp add: basis_subspace_atensor)
  then obtain R::\<open>('v \<otimes>\<^sub>a 'w) set\<close> where \<open>R \<subseteq> range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) )\<close>
    and \<open>complex_independent R\<close> and \<open>span R = UNIV\<close>
    by blast
  define \<psi>::\<open>'v \<otimes>\<^sub>a 'w \<Rightarrow> 'v \<times> 'w\<close>
    where \<open>\<psi> x = ( SOME z. x = (fst z) \<otimes>\<^sub>a (snd z) )\<close> for x
  have \<open>\<exists>H. clinear H \<and> ( \<forall>x\<in>R. H x = h (fst (\<psi> x)) (snd (\<psi> x)) )\<close>
    using \<open>complex_independent R\<close> 
      Complex_Vector_Spaces.complex_vector.linear_independent_extend[where B = "R" and f = "(\<lambda> x. h (fst (\<psi> x)) (snd (\<psi> x)) )"]
    by simp
  then obtain H where \<open>clinear H\<close> and \<open>\<forall>x\<in>R. H x = h (fst (\<psi> x)) (snd (\<psi> x))\<close>
    by blast
  have \<open>clinear H \<and> (\<forall>x y. h x y = H (x \<otimes>\<^sub>a y))\<close>
  proof-
    have \<open>h x y = H (x \<otimes>\<^sub>a y)\<close>
      for x y
    proof-
      have \<open>\<exists> t r. finite t \<and> t \<subseteq> R \<and> x \<otimes>\<^sub>a y = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        using complex_vector.span_explicit[where b = "R"]
        sorry
      show ?thesis sorry
    qed
    thus ?thesis using \<open>clinear H\<close> by blast
  qed
  moreover have \<open>HH = H\<close>
    if "clinear HH" and "\<forall>x y. h x y = HH (x \<otimes>\<^sub>a y)"
    for HH :: "'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z"
    using that sorry
  ultimately show ?thesis by blast
qed

text \<open>Proposition 1 on page 186 in @{cite Helemskii}\<close>
instantiation atensor :: (complex_inner,complex_inner) complex_inner
begin
lift_definition cinner_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> complex\<close>
  is \<open>undefined\<close>
proof-
  fix f1 f2 f3 f4::\<open>('a \<times> 'b) free\<close>
  assume \<open>atensor_rel f1 f2\<close> and \<open>atensor_rel f3 f4\<close>
  show \<open>undefined f1 f3 = undefined f2 f4\<close>
    sorry
qed

definition norm_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> real\<close> where
  \<open>norm_atensor z = sqrt (norm \<langle>z, z\<rangle> )\<close> for z

definition sgn_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close> where
  \<open>sgn_atensor x = x /\<^sub>R norm x\<close> for x

definition dist_atensor :: \<open>'a \<otimes>\<^sub>a 'b \<Rightarrow> 'a \<otimes>\<^sub>a 'b \<Rightarrow> real\<close> where
  \<open>dist_atensor x y = norm (x - y)\<close> for x y

definition uniformity_atensor :: \<open>(('a \<otimes>\<^sub>a 'b) \<times> ('a \<otimes>\<^sub>a 'b)) filter\<close>
  where  \<open>uniformity_atensor = (INF e:{0<..}. principal {((f::'a \<otimes>\<^sub>a 'b), (g::'a \<otimes>\<^sub>a 'b)). dist f g < e})\<close>

definition open_atensor :: \<open>('a \<otimes>\<^sub>a 'b) set \<Rightarrow> bool\<close>
  where \<open>open_atensor = (\<lambda> U::('a \<otimes>\<^sub>a 'b) set. (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity))\<close>

instance
proof
  show "dist (x::'a \<otimes>\<^sub>a 'b) y = norm (x - y)"
    for x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
    unfolding dist_atensor_def by blast
  show "sgn (x::'a \<otimes>\<^sub>a 'b) = x /\<^sub>R norm x"
    for x :: "'a \<otimes>\<^sub>a 'b"
    unfolding sgn_atensor_def by blast
  show "uniformity = (INF e\<in>{0<..}. principal {(x, y). dist (x::'a \<otimes>\<^sub>a 'b) y < e})"
    unfolding uniformity_atensor_def by blast
  show "open U = (\<forall>x\<in>U. \<forall>\<^sub>F (x', y) in uniformity. (x'::'a \<otimes>\<^sub>a 'b) = x \<longrightarrow> y \<in> U)"
    for U :: "('a \<otimes>\<^sub>a 'b) set"
    unfolding open_atensor_def by blast
  show "\<langle>x::'a \<otimes>\<^sub>a 'b, y\<rangle> = cnj \<langle>y, x\<rangle>"
    for x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
    sorry
  show "\<langle>(x::'a \<otimes>\<^sub>a 'b) + y, z\<rangle> = \<langle>x, z\<rangle> + \<langle>y, z\<rangle>"
    for x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
      and z :: "'a \<otimes>\<^sub>a 'b"
    sorry
  show "\<langle>r *\<^sub>C (x::'a \<otimes>\<^sub>a 'b), y\<rangle> = cnj r * \<langle>x, y\<rangle>"
    for r :: complex
      and x :: "'a \<otimes>\<^sub>a 'b"
      and y :: "'a \<otimes>\<^sub>a 'b"
    sorry
  show "0 \<le> \<langle>x::'a \<otimes>\<^sub>a 'b, x\<rangle>"
    for x :: "'a \<otimes>\<^sub>a 'b"
    sorry
  show "(\<langle>x::'a \<otimes>\<^sub>a 'b, x\<rangle> = 0) = (x = 0)"
    for x :: "'a \<otimes>\<^sub>a 'b"
    sorry
  show "norm (x::'a \<otimes>\<^sub>a 'b) = sqrt (cmod \<langle>x, x\<rangle>)"
    for x :: "'a \<otimes>\<^sub>a 'b"
    unfolding norm_atensor_def by blast
qed

end

end
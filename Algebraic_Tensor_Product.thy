(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)


theory Algebraic_Tensor_Product
  imports
    Complex_Inner_Product 
    "HOL-Library.Adhoc_Overloading"
    Free_Vector_Spaces
begin

definition atensor_kernel::\<open>( (('a::complex_vector) \<times> ('b::complex_vector)) free ) set\<close> where
  \<open>atensor_kernel = complex_vector.span ( 
  {inclusion_free (x, (y+z)) - inclusion_free (x, y) - inclusion_free (x, z) |  x y z. True}
\<union> { inclusion_free ((y+z), x) - inclusion_free (y, x) - inclusion_free (z, x) |  x y z. True}
\<union> { inclusion_free (x, (c *\<^sub>C y)) -  c *\<^sub>C inclusion_free (x, y) |  x y c. True} 
\<union> { inclusion_free ((c *\<^sub>C x), y) -  c *\<^sub>C inclusion_free (x, y) |  x y c. True} )\<close>

lemma subspace_atensor_kernel:
  \<open>complex_vector.subspace atensor_kernel\<close>
  unfolding atensor_kernel_def
  using Complex_Vector_Spaces.complex_vector.subspace_span
  by blast

definition atensor_rel :: "(('a::complex_vector) \<times> ('b::complex_vector)) free \<Rightarrow> ('a \<times> 'b) free \<Rightarrow> bool"
  where "atensor_rel = (\<lambda>x y. x - y \<in> atensor_kernel)"

text\<open>Tensor product as defined in @{cite Helemskii} chapter 2, section 8\<close>
  (* TODO: define a map function to get rid of the following warning, if such a function
   is possible (using commands definition free_map :: "('a\<Rightarrow>'b) \<Rightarrow> ('a free\<Rightarrow>'b free)", functor free_map) *)
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
  is \<open>\<lambda> x::'a. \<lambda> y::'b. inclusion_free (x, y)\<close>.

definition atensor_of_pair:: \<open>'a::complex_vector \<times> 'b::complex_vector \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close> where
\<open>atensor_of_pair z = (fst z) \<otimes>\<^sub>a (snd z)\<close>

lemma tensor_of_sets:
  \<open>( atensor_of_pair ` (A \<times> B) ) = {a\<otimes>\<^sub>ab| a b. a\<in>A \<and> b\<in>B}\<close>
proof-
  have "(\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (A \<times> B) \<subseteq> {a \<otimes>\<^sub>a b |a b. a \<in> A \<and> b \<in> B}"
  proof
    show "x \<in> {a \<otimes>\<^sub>a b |a b. a \<in> A \<and> b \<in> B}"
      if "x \<in> (\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (A \<times> B)"
      for x :: "'a \<otimes>\<^sub>a 'b"
      using that by fastforce
  qed
  moreover have "{a \<otimes>\<^sub>a b |a b. a \<in> A \<and> b \<in> B} \<subseteq> (\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (A \<times> B)"
  proof
    show "x \<in> (\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (A \<times> B)"
      if "x \<in> {a \<otimes>\<^sub>a b |a b. a \<in> A \<and> b \<in> B}"
      for x :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>\<exists>a\<in>A. \<exists>b\<in>B. x = a \<otimes>\<^sub>a b\<close>
        using that by blast
      then obtain a b where \<open>a \<in> A\<close> and \<open>b \<in> B\<close> and \<open>x = a \<otimes>\<^sub>a b\<close>
        by blast
      from \<open>x = a \<otimes>\<^sub>a b\<close>
      have  \<open>x = (\<lambda>z. fst z \<otimes>\<^sub>a snd z) (a, b)\<close>
        by simp
      moreover have \<open>(a, b) \<in> A \<times> B\<close>
        using  \<open>a \<in> A\<close>  \<open>b \<in> B\<close> by blast
      ultimately show ?thesis by blast
    qed
  qed
  ultimately show ?thesis unfolding atensor_of_pair_def by blast
qed


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
  fixes x :: "'a::complex_vector" and y z :: "'b::complex_vector"
  shows  \<open>x \<otimes>\<^sub>a (y+z) =  x \<otimes>\<^sub>a y  +  x \<otimes>\<^sub>a z\<close>
    (* TODO: without unfolding atensor_kernel_def, the proof will be more readable (because atensor_kernel
can be used instead of writing out its definition twice in the proof *)
    (* TODO: you can write "proof (transfer, unfold ...)" *)
  apply transfer unfolding atensor_rel_def atensor_kernel_def
proof-
  fix x::'a and y z::'b
  have \<open>inclusion_free (x, y + z) - (inclusion_free (x, y) + inclusion_free (x, z))
  \<in> {inclusion_free (x, y + z) - inclusion_free (x, y) - inclusion_free (x, z) |x y z. True}\<close>
    by (metis (mono_tags, lifting) diff_diff_add mem_Collect_eq)    
  hence \<open>inclusion_free (x, y + z) - (inclusion_free (x, y) + inclusion_free (x, z))
  \<in> ({inclusion_free (x, y + z) - inclusion_free (x, y) - inclusion_free (x, z) |x y z. True} \<union>
            {inclusion_free (y + z, x) - inclusion_free (y, x) - inclusion_free (z, x) |x y z. True} \<union>
            {inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y) |x y c. True} \<union>
            {inclusion_free (c *\<^sub>C x, y) - c *\<^sub>C inclusion_free (x, y) |x y c. True})\<close>
    by simp
  thus \<open>inclusion_free (x, y + z) - (inclusion_free (x, y) + inclusion_free (x, z))
       \<in> complex_vector.span
           ({inclusion_free (x, y + z) - inclusion_free (x, y) - inclusion_free (x, z) |x y z. True} \<union>
            {inclusion_free (y + z, x) - inclusion_free (y, x) - inclusion_free (z, x) |x y z. True} \<union>
            {inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y) |x y c. True} \<union>
            {inclusion_free (c *\<^sub>C x, y) - c *\<^sub>C inclusion_free (x, y) |x y c. True})\<close>
    by (simp add: complex_vector.span_base)
qed

lemma atensor_distr_right_sum:
  fixes x :: "'a::complex_vector" and y :: "'c \<Rightarrow> 'b::complex_vector"
    and I :: \<open>'c set\<close>
  shows  \<open>x \<otimes>\<^sub>a (\<Sum> i \<in> I. y i) =  (\<Sum> i \<in> I. x \<otimes>\<^sub>a (y i))\<close>
  using atensor_distr_right
  by (metis Modules.additive_def additive.sum) 

lemma atensor_distr_left:
  fixes y z :: "'a::complex_vector" and x :: "'b::complex_vector"
  shows  \<open>(y+z) \<otimes>\<^sub>a x =  y \<otimes>\<^sub>a x  +  z \<otimes>\<^sub>a x\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def
proof-
  fix y z::'a and x::'b
  have \<open>inclusion_free (y + z, x) - (inclusion_free (y, x) + inclusion_free (z, x))
       \<in> {inclusion_free (y + z, x) - inclusion_free (y, x) - inclusion_free (z, x) |x y z. True}\<close>
    by (metis (mono_tags, lifting) diff_diff_add mem_Collect_eq)
  hence \<open>inclusion_free (y + z, x) - (inclusion_free (y, x) + inclusion_free (z, x))
       \<in> ({inclusion_free (x, y + z) - inclusion_free (x, y) - inclusion_free (x, z) |x y z. True} \<union>
            {inclusion_free (y + z, x) - inclusion_free (y, x) - inclusion_free (z, x) |x y z. True} \<union>
            {inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y) |x y c. True} \<union>
            {inclusion_free (c *\<^sub>C x, y) - c *\<^sub>C inclusion_free (x, y) |x y c. True})\<close>
    by simp
  thus \<open> inclusion_free (y + z, x) - (inclusion_free (y, x) + inclusion_free (z, x))
       \<in> complex_vector.span
           ({inclusion_free (x, y + z) - inclusion_free (x, y) - inclusion_free (x, z) |x y z. True} \<union>
            {inclusion_free (y + z, x) - inclusion_free (y, x) - inclusion_free (z, x) |x y z. True} \<union>
            {inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y) |x y c. True} \<union>
            {inclusion_free (c *\<^sub>C x, y) - c *\<^sub>C inclusion_free (x, y) |x y c. True})\<close>
    by (simp add: complex_vector.span_base)
qed

lemma atensor_distr_left_sum:
  fixes  x :: "'c \<Rightarrow> 'a::complex_vector" and y :: "'b::complex_vector"
    and I :: \<open>'c set\<close>
  shows  \<open>(\<Sum> i \<in> I. x i) \<otimes>\<^sub>a y =  (\<Sum> i \<in> I. (x i) \<otimes>\<^sub>a y)\<close>
proof-
  define f::\<open>'a \<Rightarrow> 'a \<otimes>\<^sub>a 'b\<close> where \<open>f t = t \<otimes>\<^sub>a y\<close> for t
  have \<open>Modules.additive f\<close>
    unfolding f_def
    using atensor_distr_left
    by (simp add: atensor_distr_left Modules.additive_def)    
  show ?thesis 
    using additive.sum \<open>Modules.additive f\<close> \<open>f \<equiv> \<lambda>t. t \<otimes>\<^sub>a y\<close> by auto
qed

lemma atensor_mult_right:
  fixes x :: "'a::complex_vector" and y :: "'b::complex_vector" and c :: complex
  shows \<open>x \<otimes>\<^sub>a (c *\<^sub>C y) = c *\<^sub>C (x \<otimes>\<^sub>a y)\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def
proof-
  fix x::'a and y::'b and c::complex
  have \<open>inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y)
       \<in> {inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y) |x y c. True}\<close>
    by (metis (mono_tags, lifting) mem_Collect_eq)
  hence \<open>inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y)
       \<in> ({inclusion_free (x, y + z) - inclusion_free (x, y) - inclusion_free (x, z) |x y z. True} \<union>
            {inclusion_free (y + z, x) - inclusion_free (y, x) - inclusion_free (z, x) |x y z. True} \<union>
            {inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y) |x y c. True} \<union>
            {inclusion_free (c *\<^sub>C x, y) - c *\<^sub>C inclusion_free (x, y) |x y c. True})\<close>
    by simp
  thus \<open>inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y)
       \<in> complex_vector.span
           ({inclusion_free (x, y + z) - inclusion_free (x, y) - inclusion_free (x, z) |x y z. True} \<union>
            {inclusion_free (y + z, x) - inclusion_free (y, x) - inclusion_free (z, x) |x y z. True} \<union>
            {inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y) |x y c. True} \<union>
            {inclusion_free (c *\<^sub>C x, y) - c *\<^sub>C inclusion_free (x, y) |x y c. True})\<close>
    by (simp add: complex_vector.span_base)
qed


lemma atensor_mult_left:
  fixes x :: "'a::complex_vector" and y :: "'b::complex_vector" and c :: complex
  shows \<open>(c *\<^sub>C x) \<otimes>\<^sub>a y  = c *\<^sub>C (x \<otimes>\<^sub>a y)\<close>
  apply transfer unfolding atensor_rel_def atensor_kernel_def
  apply auto
  by (metis (mono_tags, lifting) Un_iff complex_vector.span_base mem_Collect_eq)


lemma abs_atensor_inclusion_free:
  \<open>abs_atensor (inclusion_free u) = atensor_of_pair u\<close>
proof-
  have \<open>complex_vector.subspace atensor_kernel\<close>
    by (simp add: subspace_atensor_kernel)
  hence \<open>atensor_rel (Abs_free (\<lambda>x. if x = u then 1 else 0))
          (inclusion_free (fst u, snd u))\<close>
    unfolding atensor_rel_def inclusion_free_def apply auto
    by (simp add: \<open>complex_vector.subspace atensor_kernel\<close> complex_vector.subspace_0) 
  thus ?thesis
    by (simp add: atensor_of_pair_def atensor_op.abs_eq)    
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
  shows \<open>abs_atensor X = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}.  ((Rep_free X) z) *\<^sub>C (atensor_of_pair z) )\<close>
proof-                                        
  have \<open>X = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (inclusion_free z))\<close>
    using free_explicit by auto
  hence  \<open>abs_atensor X = abs_atensor (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. ((Rep_free X) z) *\<^sub>C (inclusion_free z))\<close>
    by simp
  also have \<open>\<dots> = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}. abs_atensor (((Rep_free X) z) *\<^sub>C (inclusion_free z)))\<close>
    by (metis (mono_tags, lifting) abs_atensor_sum_general sum.cong sum.infinite zero_atensor.abs_eq)
  also have \<open>\<dots> = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}.  ((Rep_free X) z) *\<^sub>C (abs_atensor (inclusion_free z)))\<close>
    by (metis scaleC_atensor.abs_eq)
  also have \<open>\<dots> = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}.  ((Rep_free X) z) *\<^sub>C ( (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
    by (metis (mono_tags, lifting) abs_atensor_inclusion_free atensor_of_pair_def)
  finally have \<open> abs_atensor X = (\<Sum>z\<in>{u |u. Rep_free X u \<noteq> 0}. Rep_free X z *\<^sub>C (fst z \<otimes>\<^sub>a snd z))\<close>
    by blast
  thus ?thesis
    by (metis (no_types, lifting) atensor_of_pair_def sum.cong) 
qed

lemma atensor_onto_explicit:
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
  shows \<open>\<exists> S f. finite S \<and> (\<forall> z\<in>S. f z \<noteq> 0) \<and> x = (\<Sum>z\<in>S. (f z) *\<^sub>C ( atensor_of_pair z ) )\<close>
proof-
  have \<open>\<exists> X. x = abs_atensor X\<close>
    apply transfer
    using atensor.abs_eq_iff by blast
  then obtain X where \<open>x = abs_atensor X\<close> by blast
  moreover have \<open>abs_atensor X = (\<Sum>z\<in>{u | u. (Rep_free X) u \<noteq> 0}.  ((Rep_free X) z) *\<^sub>C ( (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
    using free_explicit
    by (metis (mono_tags, lifting) atensor_of_pair_def sum.cong) 
  moreover have \<open>finite {u | u. (Rep_free X) u \<noteq> 0}\<close>
    using Rep_free by blast
  ultimately show ?thesis
    using Algebraic_Tensor_Product.free_explicit by blast
qed

lemma tensor_product_cartesian_product:
  assumes \<open>finite t\<close> and \<open>finite t'\<close>
  shows \<open>(\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>a (\<Sum>j\<in>t'. r' j *\<^sub>C j)
 = (\<Sum>(a, b)\<in>t\<times>t'. (r a * r' b) *\<^sub>C (a \<otimes>\<^sub>a b))\<close>
proof-
  have \<open>(\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>a (\<Sum>j\<in>t'. r' j *\<^sub>C j) = (\<Sum>i\<in>t. (r i *\<^sub>C i) \<otimes>\<^sub>a (\<Sum>j\<in>t'. r' j *\<^sub>C j) )\<close>
    using atensor_distr_left_sum by force    
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. (r i *\<^sub>C i) \<otimes>\<^sub>a (r' j *\<^sub>C j)) )\<close>
    by (metis (mono_tags, lifting) Finite_Cartesian_Product.sum_cong_aux atensor_distr_right_sum)    
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. r i *\<^sub>C ( i \<otimes>\<^sub>a (r' j *\<^sub>C j) ) ) )\<close>
    by (meson atensor_mult_left sum.cong)
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. r i *\<^sub>C ( r' j *\<^sub>C (i \<otimes>\<^sub>a j) ) ) )\<close>
    by (metis (no_types, lifting) atensor_mult_right sum.cong)
  also have \<open>\<dots> = (\<Sum>i\<in>t. (\<Sum>j\<in>t'. (r i * r' j) *\<^sub>C (i \<otimes>\<^sub>a j) ) )\<close>
    by auto
  also have \<open>\<dots> = (\<Sum>z\<in>t\<times>t'. (r (fst z) * r' (snd z)) *\<^sub>C ((fst z) \<otimes>\<^sub>a (snd z)))\<close>
    using Groups_Big.comm_monoid_add_class.sum.cartesian_product [where A = "t" 
        and B = "t'" and g = "\<lambda> i j. (r i * r' j) *\<^sub>C (i \<otimes>\<^sub>a j)"]
    by (metis (no_types, lifting) case_prod_beta' sum.cong)
  finally have \<open>(\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>a (\<Sum>j\<in>t'. r' j *\<^sub>C j) =
  (\<Sum>z\<in>t \<times> t'. (r (fst z) * r' (snd z)) *\<^sub>C (fst z \<otimes>\<^sub>a snd z))\<close>
    by blast
  thus ?thesis
    by (metis (mono_tags, lifting) case_prod_beta' sum.cong) 
qed


lemma atensor_onto_explicit_normalized:
  fixes  x :: \<open>('a::complex_vector) \<otimes>\<^sub>a ('b::complex_vector)\<close>
  shows \<open>\<exists> S. finite S \<and> x = (\<Sum>z\<in>S. ( atensor_of_pair z ) )\<close>
proof-
  have \<open>\<exists> S f. finite S \<and> (\<forall> z\<in>S. f z \<noteq> 0) \<and> x = (\<Sum>z\<in>S. (f z) *\<^sub>C ( atensor_of_pair z ))\<close>
    using atensor_onto_explicit by blast
  then obtain S f where \<open>finite S\<close> and \<open>\<forall> z\<in>S. f z \<noteq> 0\<close> and
    \<open>x = (\<Sum>z\<in>S. (f z) *\<^sub>C ( atensor_of_pair z ))\<close>
    by blast
  have \<open>(\<Sum>z\<in>S. (f z) *\<^sub>C ( atensor_of_pair z )) 
    = (\<Sum>a\<in>fst ` S. (\<Sum>b\<in>{b | b. (a,b) \<in> S}. (f (a,b)) *\<^sub>C ( atensor_of_pair (a,b) ) ) )\<close>
    sorry

  show ?thesis sorry
qed

lemma atensor_onto:
  \<open>complex_vector.span ( range atensor_of_pair )
 = ( UNIV::(('a::complex_vector \<otimes>\<^sub>a 'b::complex_vector) set) )\<close>
proof
  show "complex_vector.span (range atensor_of_pair) \<subseteq> UNIV"
    by simp    
  show "(UNIV::('a \<otimes>\<^sub>a 'b) set) \<subseteq> complex_vector.span (range atensor_of_pair)"
  proof
    show "x \<in> complex_vector.span (range atensor_of_pair)"
      for x :: "'a \<otimes>\<^sub>a 'b"
    proof-
      have \<open>\<exists> R g. finite R \<and> (\<forall> z\<in>R. g z \<noteq> 0) \<and> x = (\<Sum>z\<in>R.  (g z) *\<^sub>C atensor_of_pair z)\<close>
        using atensor_onto_explicit by blast
      then obtain R g where \<open>finite R\<close> and \<open>x = (\<Sum>z\<in>R.  (g z) *\<^sub>C atensor_of_pair z)\<close>
        by blast
      thus ?thesis
        by (metis (no_types, lifting) complex_vector.span_scale complex_vector.span_sum complex_vector.span_superset image_subset_iff iso_tuple_UNIV_I)        
    qed
  qed
qed


lemma span_tensor_span:
  fixes A::\<open>'a::complex_vector set\<close> and  B::\<open>'b::complex_vector set\<close>
  assumes \<open>u \<in> complex_vector.span A\<close> and \<open>v \<in> complex_vector.span B\<close>
  shows \<open>u \<otimes>\<^sub>a v \<in> complex_vector.span ((\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (A \<times> B))\<close>
proof-
  have \<open>\<exists> t r. finite t \<and> t \<subseteq> A \<and> (\<Sum>a\<in>t. r a *\<^sub>C a) = u\<close>
  proof -
    have "\<forall>A. {a. \<exists>C f. (a::'a) = (\<Sum>a\<in>C. f a *\<^sub>C a) \<and> finite C \<and> C \<subseteq> A} = Complex_Vector_Spaces.span A"
      by (simp add: Complex_Vector_Spaces.span_raw_def complex_vector.span_explicit)
    then have "\<forall>A a. (\<exists>C f. (a::'a) = (\<Sum>a\<in>C. f a *\<^sub>C a) \<and> finite C \<and> C \<subseteq> A) \<or> a \<notin> Complex_Vector_Spaces.span A"
      by blast
    then show ?thesis
      by (metis (no_types) Complex_Vector_Spaces.span_raw_def assms(1))
  qed
  then obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> A\<close> and \<open>(\<Sum>a\<in>t. r a *\<^sub>C a) = u\<close>
    by blast
  have \<open>\<exists> t' r'. finite t' \<and> t' \<subseteq> B \<and> (\<Sum>a\<in>t'. r' a *\<^sub>C a) = v\<close>
    using  \<open>v \<in> complex_vector.span B\<close> complex_vector.span_explicit
  proof -
    have "\<exists>C f. v = (\<Sum>b\<in>C. f b *\<^sub>C b) \<and> finite C \<and> C \<subseteq> B"
      using assms(2) complex_vector.span_explicit by blast
    then show ?thesis
      by (metis (full_types, lifting))
  qed
  then obtain t' r' where \<open>finite t'\<close> and \<open>t' \<subseteq> B\<close> and \<open>(\<Sum>a\<in>t'. r' a *\<^sub>C a) = v\<close>
    by blast
  have \<open>u \<otimes>\<^sub>a v = (\<Sum>i\<in>t. r i *\<^sub>C i) \<otimes>\<^sub>a (\<Sum>j\<in>t'. r' j *\<^sub>C j)\<close>
    by (simp add: \<open>(\<Sum>a\<in>t'. r' a *\<^sub>C a) = v\<close> \<open>(\<Sum>a\<in>t. r a *\<^sub>C a) = u\<close>)
  also have \<open>\<dots> = (\<Sum>z\<in>t\<times>t'. (r (fst z) * r' (snd z)) *\<^sub>C ((fst z) \<otimes>\<^sub>a (snd z)))\<close>
    using tensor_product_cartesian_product \<open>finite t\<close> \<open>finite t'\<close> by blast
  finally have \<open>u \<otimes>\<^sub>a v = (\<Sum>k\<in>t\<times>t'. (\<lambda> z. r (fst z) * r' (snd z)) k *\<^sub>C ((\<lambda>z. fst z \<otimes>\<^sub>a snd z) k) )\<close>
    by blast
  moreover have \<open>k \<in> t \<times> t' \<Longrightarrow> ((\<lambda>z. fst z \<otimes>\<^sub>a snd z) k) \<in> complex_vector.span ( (\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (A \<times> B) )\<close>
    for k
  proof-
    assume \<open>k \<in> t \<times> t'\<close>
    hence \<open>((\<lambda>z. fst z \<otimes>\<^sub>a snd z) k) \<in> (\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (t \<times> t')\<close>
      by simp
    moreover have \<open>t \<times> t' \<subseteq> A \<times> B\<close>
      using \<open>t \<subseteq> A\<close> \<open>t' \<subseteq> B\<close>
      by auto
    ultimately have \<open>((\<lambda>z. fst z \<otimes>\<^sub>a snd z) k) \<in> (\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (A \<times> B)\<close>
      by auto
    thus \<open>((\<lambda>z. fst z \<otimes>\<^sub>a snd z) k) \<in> complex_vector.span ( (\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (A \<times> B) )\<close>
      by (simp add: complex_vector.span_base)      
  qed
  ultimately show ?thesis 
    by (metis (no_types, lifting) complex_vector.span_scale complex_vector.span_sum  image_subset_iff)
qed

lemma basis_atensor_complex_generator:
  fixes A::\<open>'a::complex_vector set\<close> and  B::\<open>'b::complex_vector set\<close>
  assumes \<open>complex_vector.span A = UNIV\<close> and  \<open>complex_vector.span B = UNIV\<close>
  shows \<open>complex_vector.span ( (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) ` (A \<times> B) ) = UNIV\<close>
proof-
  have \<open>x \<in> complex_vector.span ( (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) ` (A \<times> B) )\<close>
    for x
  proof-
    have \<open>x \<in> complex_vector.span (range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
      by (simp add: atensor_onto)
    hence \<open>\<exists> t r. finite t \<and> t \<subseteq> (range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) ) \<and>
         x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
    proof -
      have "\<forall>A a. (\<exists>B f. (a::'a \<otimes>\<^sub>a 'b) = (\<Sum>a\<in>B. f a *\<^sub>C a) \<and> finite B \<and> B \<subseteq> A) \<or> a \<notin> complex_vector.span A"
        using complex_vector.span_explicit by blast
      thus ?thesis
        by (metis (no_types) atensor_onto iso_tuple_UNIV_I)
    qed 
    then obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> (range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) )\<close> and
      \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      by blast
    have \<open>t \<subseteq> complex_vector.span ( (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) ` (A \<times> B) )\<close>
    proof
      show "x \<in> complex_vector.span ((\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (A \<times> B))"
        if "x \<in> t"
        for x :: "'a \<otimes>\<^sub>a 'b"
      proof-
        from \<open>t \<subseteq> (range (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) )\<close>
        have \<open>\<exists> u v. x = u \<otimes>\<^sub>a v\<close>
          using that by blast
        then obtain u v where \<open>x = u \<otimes>\<^sub>a v\<close> by blast
        have \<open>u \<in> complex_vector.span A\<close>
          by (simp add: assms(1))
        moreover have \<open>v \<in> complex_vector.span B\<close>
          by (simp add: assms(2))
        ultimately have \<open>u \<otimes>\<^sub>a v \<in> complex_vector.span ((\<lambda>z. fst z \<otimes>\<^sub>a snd z) ` (A \<times> B))\<close>
          using span_tensor_span by blast
        thus ?thesis
          using \<open>x = u \<otimes>\<^sub>a v\<close>
          by simp
      qed
    qed
    thus ?thesis
      by (simp add: \<open>x = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> complex_vector.span_scale complex_vector.span_sum subset_iff) 
  qed
  thus ?thesis
    by blast 
qed

lemma quot_atensor:
  fixes G ::\<open>('v::complex_vector \<times> 'w::complex_vector) free \<Rightarrow> 'z\<close>
  assumes \<open>\<And> x y. atensor_rel x y \<Longrightarrow> G x = G y\<close>
  shows \<open>\<exists>! H :: 'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z. \<forall> S. \<forall> s \<in> Rep_atensor S. H S = G s\<close>
proof-
  define H where \<open>H S = G (SOME s. s \<in> Rep_atensor S)\<close>
    for S
  have \<open>\<forall>S. \<forall>s\<in>Rep_atensor S. H S = G s\<close>
  proof-
    have \<open>s\<in>Rep_atensor S \<Longrightarrow> H S = G s\<close>
      for s S
    proof-
      assume \<open>s\<in>Rep_atensor S\<close>
      hence \<open>atensor_rel s (SOME s. s \<in> Rep_atensor S)\<close>
        by (smt Rep_atensor atensor_equivp equivp_symp equivp_transp mem_Collect_eq some_eq_ex)
      hence \<open>G s = G (SOME s. s \<in> Rep_atensor S)\<close>
        using \<open>\<And> x y. atensor_rel x y \<Longrightarrow> G x = G y\<close>
        by auto
      thus \<open>H S = G s\<close> 
        using \<open>H S = G (SOME s. s \<in> Rep_atensor S)\<close>
        by simp
    qed
    thus ?thesis by blast
  qed
  moreover have \<open>K = H\<close>
    if "\<forall>S. \<forall>s\<in>Rep_atensor S. K S = G s"
    for K :: "'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z"
  proof-
    have \<open>K S = H S\<close>
      for S
    proof-
      have \<open>K S = G (SOME s. s \<in> Rep_atensor S)\<close>
        using that Rep_atensor some_in_eq by force 
      thus ?thesis 
        using \<open>H S = G (SOME s. s \<in> Rep_atensor S)\<close>
        by auto
    qed
    thus ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed

lemma quot_atensor2:
  fixes G ::\<open>('v::complex_vector \<times> 'w::complex_vector) free \<Rightarrow> 'z\<close>
  assumes \<open>\<And> x y. atensor_rel x y \<Longrightarrow> G x = G y\<close>
  shows \<open>\<exists>! H :: 'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z. \<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
proof-
  define H where \<open>H S = G (rep_atensor S)\<close> for S
  have "atensor_rel s (rep_atensor S) \<Longrightarrow> H S = G s"
    for S s
  proof-
    assume \<open>atensor_rel s (rep_atensor S)\<close>
    hence \<open>G (rep_atensor S) = G s\<close>
      using \<open>\<And> x y. atensor_rel x y \<Longrightarrow> G x = G y\<close>
      by auto
    thus \<open>H S = G s\<close>
      unfolding H_def by blast
  qed
  hence "\<forall>S s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s"
    by blast 
  moreover have "K = H"
    if "\<forall>S s. atensor_rel s (rep_atensor S) \<longrightarrow> K S = G s"
    for K :: "'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z"
  proof-
    have \<open>K S = H S\<close>
      for S
    proof-
      have \<open>K S = G (rep_atensor S)\<close>
        using Quotient3_atensor Quotient3_rel_rep that by fastforce
      moreover have \<open>H S = G (rep_atensor S)\<close>
        by (simp add: H_def)
      ultimately show \<open>K S = H S\<close> by simp
    qed
    thus \<open>K = H\<close>
      by blast
  qed
  ultimately show ?thesis by blast
qed

definition cbilinear :: \<open>('a::complex_vector \<Rightarrow> 'b::complex_vector \<Rightarrow> 'c::complex_vector) \<Rightarrow> bool\<close>
  where \<open>cbilinear \<equiv> (\<lambda> f. (\<forall> y. clinear (\<lambda> x. f x y)) \<and> (\<forall> x. clinear (\<lambda> y. f x y)) )\<close>

text\<open>Universal property of the tensor product. See chapter XVI in @{cite lang2004algebra}\<close>
lemma atensor_universal_property:
  fixes h :: \<open>'v::complex_vector \<Rightarrow> 'w::complex_vector \<Rightarrow> 'z::complex_vector\<close>
  assumes \<open>cbilinear h\<close>
  shows \<open>\<exists>! H :: 'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z. clinear H \<and> (\<forall> x y. h x y = H (x \<otimes>\<^sub>a y))\<close>
proof-
  have "\<exists>! G ::('v \<times> 'w) free \<Rightarrow> 'z. clinear G \<and> ( (\<lambda> z. h (fst z) (snd z)) = G \<circ> inclusion_free )"
    using free_universal_property by blast
  then obtain G::\<open>('v \<times> 'w) free \<Rightarrow> 'z\<close> where \<open>clinear G\<close>
    and \<open>(\<lambda> z. h (fst z) (snd z)) = G \<circ> inclusion_free\<close>
    by blast
  have \<open>atensor_rel x y \<Longrightarrow> G x = G y\<close>
    for x y
  proof-
    assume \<open>atensor_rel x y\<close>
    hence \<open>x - y \<in> atensor_kernel\<close>
      unfolding atensor_rel_def
      by blast
    moreover have \<open>\<forall> z \<in> atensor_kernel. G z = 0\<close>
    proof-
      (* TODO: Avoid copy and pasting long definitions. This could just be written as atensor_kernel *)
      have \<open>\<forall> z \<in> ({inclusion_free (x, y + z) - inclusion_free (x, y) -
           inclusion_free (x, z) |
           x y z. True} \<union>
          {inclusion_free (y + z, x) - inclusion_free (y, x) -
           inclusion_free (z, x) |
           x y z. True} \<union>
          {inclusion_free (x, c *\<^sub>C y) -
           c *\<^sub>C inclusion_free (x, y) |
           x y c. True} \<union>
          {inclusion_free (c *\<^sub>C x, y) -
           c *\<^sub>C inclusion_free (x, y) |
           x y c. True}). G z = 0\<close>
      proof-
        have \<open>w \<in> {inclusion_free (x, y + z) - inclusion_free (x, y) -
           inclusion_free (x, z) | x y z. True} \<Longrightarrow> G w = 0\<close>
          for w
        proof-
          assume \<open>w \<in> {inclusion_free (x, y + z) - inclusion_free (x, y) -
           inclusion_free (x, z) | x y z. True}\<close>
          hence \<open>\<exists> x y z. w = inclusion_free (x, y + z) - inclusion_free (x, y) -
           inclusion_free (x, z)\<close>
            by blast
          then obtain x y z where \<open>w = inclusion_free (x, y + z) - inclusion_free (x, y) -
           inclusion_free (x, z)\<close>
            by blast
          hence \<open>G w = G (inclusion_free (x, y + z)) - G (inclusion_free (x, y)) -
           G (inclusion_free (x, z))\<close>
            using \<open>clinear G\<close>
            by (simp add: complex_vector.linear_diff)
          hence \<open>G w = h x (y + z) - h x y - h x z\<close>
            using \<open>(\<lambda> z. h (fst z) (snd z)) = G \<circ> inclusion_free\<close>
            by (metis comp_apply fst_conv snd_conv)
          hence \<open>G w = h x y + h x z - h x y - h x z\<close>
            using \<open>cbilinear h\<close> unfolding cbilinear_def
            by (simp add: complex_vector.linear_add)
          thus \<open>G w = 0\<close>
            by simp
        qed
        moreover have \<open>w \<in> {inclusion_free (y + z, x) - inclusion_free (y, x) -
           inclusion_free (z, x) | x y z. True} \<Longrightarrow> G w = 0\<close>
          for w
        proof-
          assume \<open>w \<in> {inclusion_free (y + z, x) - inclusion_free (y, x) -
           inclusion_free (z, x) | x y z. True}\<close>
          hence \<open>\<exists> x y z. w = inclusion_free (y + z, x) - inclusion_free (y, x) -
           inclusion_free (z, x)\<close>
            by blast
          then obtain x y z where \<open>w = inclusion_free (y + z, x) - inclusion_free (y, x) -
           inclusion_free (z, x)\<close>
            by blast
          hence \<open>G w = G (inclusion_free (y + z, x)) - G (inclusion_free (y, x)) -
           G (inclusion_free (z, x))\<close>
            using \<open>clinear G\<close>
            by (simp add: complex_vector.linear_diff)
          hence \<open>G w = h (y + z) x - h y x - h z x\<close>
            using \<open>(\<lambda> z. h (fst z) (snd z)) = G \<circ> inclusion_free\<close>
            by (metis comp_apply fst_conv snd_conv)
          hence \<open>G w = h y x + h z x - h y x - h z x\<close>
            using \<open>cbilinear h\<close> unfolding cbilinear_def
          proof -
            assume "(\<forall>y. clinear (\<lambda>x. h x y)) \<and> (\<forall>x. clinear (h x))"
            then show ?thesis
              (* TODO use a fact name instead of \<open>G w = h (y + z) x - h y x - h z x\<close> *)
              by (metis (no_types) \<open>G w = h (y + z) x - h y x - h z x\<close> add_diff_cancel_left' complex_vector.linear_diff)
          qed
          thus \<open>G w = 0\<close> by simp
        qed
        moreover have \<open>w \<in> {inclusion_free (x, c *\<^sub>C y) -
           c *\<^sub>C inclusion_free (x, y) | x y c. True} \<Longrightarrow> G w = 0\<close>
          for w
        proof-
          assume \<open>w \<in> {inclusion_free (x, c *\<^sub>C y) -
           c *\<^sub>C inclusion_free (x, y) | x y c. True}\<close>
          have \<open>\<exists> x y c. w = inclusion_free (x, c *\<^sub>C y) -
           c *\<^sub>C inclusion_free (x, y)\<close>
            using \<open>w \<in> {inclusion_free (x, c *\<^sub>C y) - c *\<^sub>C inclusion_free (x, y) | x y c. True}\<close> by auto
          then obtain x y c where \<open>w = inclusion_free (x, c *\<^sub>C y) -
           c *\<^sub>C inclusion_free (x, y)\<close>         
            by blast
          hence \<open>G w = G (inclusion_free (x, c *\<^sub>C y)) -
           G(c *\<^sub>C inclusion_free (x, y))\<close>
            by (simp add: \<open>clinear G\<close> complex_vector.linear_diff)
          hence \<open>G w = G (inclusion_free (x, c *\<^sub>C y)) -
           c *\<^sub>C G(inclusion_free (x, y))\<close>
            using \<open>clinear G\<close> complex_vector.linear_scale by auto
          hence \<open>G w = (h x (c *\<^sub>C y)) - c *\<^sub>C (h x y)\<close>
            by (metis \<open>(\<lambda>z. h (fst z) (snd z)) = G \<circ> inclusion_free\<close> comp_apply fst_eqD snd_eqD)
          moreover have \<open>(h x (c *\<^sub>C y)) = c *\<^sub>C (h x y)\<close>
            using \<open>cbilinear h\<close>
            unfolding cbilinear_def
            by (simp add: complex_vector.linear_scale) 
          ultimately have \<open>G w = c *\<^sub>C (h x y) - c *\<^sub>C (h x y)\<close>
            by simp
          thus \<open>G w = 0\<close>
            by simp
        qed
        moreover have \<open>w \<in> {inclusion_free (c *\<^sub>C x, y) -
           c *\<^sub>C inclusion_free (x, y) | x y c. True} \<Longrightarrow> G w = 0\<close>
          for w
        proof-
          assume \<open>w \<in> {inclusion_free (c *\<^sub>C x, y) -
           c *\<^sub>C inclusion_free (x, y) | x y c. True}\<close>
          hence \<open>\<exists> x y c. w = inclusion_free (c *\<^sub>C x, y) -
           c *\<^sub>C inclusion_free (x, y)\<close>
            by blast
          then obtain x y c where \<open>w = inclusion_free (c *\<^sub>C x, y) -
           c *\<^sub>C inclusion_free (x, y)\<close>
            by blast
          hence \<open>G w = G (inclusion_free (c *\<^sub>C x, y)) -
           G (c *\<^sub>C inclusion_free (x, y))\<close>
            using \<open>clinear G\<close> complex_vector.linear_diff by blast 
          also have \<open>\<dots> = G (inclusion_free (c *\<^sub>C x, y)) -
           c *\<^sub>C G (inclusion_free (x, y))\<close>
            using \<open>clinear G\<close>
            by (simp add: complex_vector.linear_scale)
          also have \<open>\<dots> = h (c *\<^sub>C x) y - c *\<^sub>C (h x y)\<close>
            by (metis (no_types, lifting) \<open>(\<lambda>z. h (fst z) (snd z)) = G \<circ> inclusion_free\<close> comp_apply fst_eqD snd_eqD)
          also have \<open>\<dots> = c *\<^sub>C (h x y) - c *\<^sub>C (h x y)\<close>
            using \<open>cbilinear h\<close> unfolding cbilinear_def
            using complex_vector.linear_scale by auto 
          also have \<open>\<dots> = 0\<close>
            by simp
          finally show \<open>G w = 0\<close>
            by blast
        qed
        ultimately show ?thesis by blast
      qed
      thus ?thesis unfolding atensor_kernel_def
        using \<open>clinear G\<close> complex_vector.linear_eq_0_on_span by blast        
    qed
    ultimately have \<open>G (x - y) = 0\<close>
      by blast
    thus \<open>G x = G y\<close>
      using \<open>clinear G\<close> complex_vector.linear_diff by fastforce
  qed
  hence \<open>\<exists>! H :: 'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z. \<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
    using quot_atensor2[where G = "G"] by blast
  then obtain H where \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
    by blast
  have "clinear H \<and> (\<forall>x y. h x y = H (x \<otimes>\<^sub>a y))"
  proof-
    have "clinear H"
      unfolding clinear_def
    proof
      show "H (b1 + b2) = H b1 + H b2"
        for b1 :: "'v \<otimes>\<^sub>a 'w"
          and b2 :: "'v \<otimes>\<^sub>a 'w"
      proof-
        have \<open>\<forall> \<beta>1. atensor_rel \<beta>1 (rep_atensor b1) \<longrightarrow> (H b1) = (G \<beta>1)\<close>
          using \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
          by auto
        moreover have \<open>\<forall> \<beta>2. atensor_rel \<beta>2 (rep_atensor b2) \<longrightarrow> (H b2) = (G \<beta>2)\<close>
          using \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
          by auto
        ultimately have  \<open>\<forall> \<beta>1 \<beta>2. atensor_rel \<beta>1 (rep_atensor b1) \<and> atensor_rel \<beta>2 (rep_atensor b2) 
            \<longrightarrow> (H b1) + (H b2) = (G \<beta>1) + (G \<beta>2)\<close>
          by auto
        hence  \<open>\<forall> \<beta>1 \<beta>2. atensor_rel \<beta>1 (rep_atensor b1) \<and> atensor_rel \<beta>2 (rep_atensor b2) 
            \<longrightarrow> (H b1) + (H b2) = G (\<beta>1 + \<beta>2)\<close>
          using \<open>clinear G\<close> unfolding clinear_def
          by (simp add: \<open>clinear G\<close> complex_vector.linear_add)
        moreover have \<open>\<forall> \<beta>. atensor_rel \<beta> (rep_atensor (b1 + b2)) \<longrightarrow> (H (b1 + b2)) = G \<beta>\<close>
          using \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
          by auto
        moreover have \<open>atensor_rel \<beta>1 (rep_atensor b1) \<Longrightarrow> atensor_rel \<beta>2 (rep_atensor b2)
            \<Longrightarrow> atensor_rel (\<beta>1 + \<beta>2) (rep_atensor (b1 + b2))\<close>
          for \<beta>1 \<beta>2
          by (metis Quotient3_abs_rep Quotient3_atensor atensor.abs_eq_iff plus_atensor.abs_eq)          
        ultimately show \<open>H (b1 + b2) = H b1 + H b2\<close>
          by (metis Quotient3_atensor Quotient3_rep_reflp)               
      qed
      show "H (r *\<^sub>C b) = r *\<^sub>C H b"
        for r :: complex
          and b :: "'v \<otimes>\<^sub>a 'w"
      proof-
        have \<open>\<forall> \<beta>. atensor_rel \<beta> (rep_atensor b) \<longrightarrow> r *\<^sub>C (H b) = r *\<^sub>C (G \<beta>)\<close>
          using \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
          by auto
        hence \<open>\<forall> \<beta>. atensor_rel \<beta> (rep_atensor b) \<longrightarrow> r *\<^sub>C (H b) = G (r *\<^sub>C \<beta>)\<close>
          using \<open>clinear G\<close> unfolding clinear_def
          by (simp add: \<open>clinear G\<close> complex_vector.linear_scale)
        moreover have \<open>atensor_rel \<beta> (rep_atensor b) \<Longrightarrow> atensor_rel \<gamma> (rep_atensor (r *\<^sub>C b))
           \<Longrightarrow> atensor_rel (r *\<^sub>C \<beta>)  \<gamma>\<close>                                
          for \<beta> \<gamma>
          by (metis Quotient3_abs_rep Quotient3_atensor atensor.abs_eq_iff scaleC_atensor.abs_eq)        
        moreover have \<open>\<forall> \<gamma>.  atensor_rel \<gamma> (rep_atensor (r *\<^sub>C b)) \<longrightarrow> H (r *\<^sub>C b) = G \<gamma>\<close>
          by (simp add: \<open>\<forall>S s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>)
        ultimately show ?thesis
          by (metis (full_types) \<open>\<And>\<gamma> \<beta>. \<lbrakk>atensor_rel \<beta> (rep_atensor b); atensor_rel \<gamma> (rep_atensor (r *\<^sub>C b))\<rbrakk> \<Longrightarrow> atensor_rel (r *\<^sub>C \<beta>) \<gamma>\<close> \<open>\<forall>\<beta>. atensor_rel \<beta> (rep_atensor b) \<longrightarrow> r *\<^sub>C H b = G (r *\<^sub>C \<beta>)\<close> \<open>\<forall>\<gamma>. atensor_rel \<gamma> (rep_atensor (r *\<^sub>C b)) \<longrightarrow> H (r *\<^sub>C b) = G \<gamma>\<close> atensor.abs_eq_iff)          
      qed
    qed
    moreover have "h x y = H (x \<otimes>\<^sub>a y)"
      for x y
    proof-
      from \<open>(\<lambda> z. h (fst z) (snd z)) = G \<circ> inclusion_free\<close>
      have \<open>h x y = G (inclusion_free (x, y))\<close>
        by (metis comp_apply fst_conv snd_conv)
      moreover have \<open>atensor_rel (inclusion_free (x, y)) (rep_atensor (x \<otimes>\<^sub>a y))\<close>
        by (metis (no_types) Quotient3_abs_rep Quotient3_atensor atensor.abs_eq_iff atensor_op.abs_eq)        
      ultimately show ?thesis
        using \<open>\<forall> S. \<forall>s. atensor_rel s (rep_atensor S) \<longrightarrow> H S = G s\<close>
        by auto        
    qed
    ultimately show ?thesis by blast
  qed
  moreover have "K = H"
    if "clinear K \<and> (\<forall>x y. h x y = K (x \<otimes>\<^sub>a y))"
    for K :: "'v \<otimes>\<^sub>a 'w \<Rightarrow> 'z"
  proof-
    have \<open>(\<forall>x y. h x y = K (x \<otimes>\<^sub>a y))\<close>
      using that by blast
    moreover have \<open>\<forall>x y. h x y = H (x \<otimes>\<^sub>a y)\<close>
      by (simp add: \<open>clinear H \<and> (\<forall>x y. h x y = H (x \<otimes>\<^sub>a y))\<close>)
    ultimately have \<open>K (x \<otimes>\<^sub>a y) = H (x \<otimes>\<^sub>a y)\<close>
      for x y
      by simp
    have \<open>clinear K\<close>
      by (simp add: that)
    have \<open>clinear H\<close>
      by (simp add: \<open>clinear H \<and> (\<forall>x y. h x y = H (x \<otimes>\<^sub>a y))\<close>)
    have \<open>K z = H z\<close>
      for z
    proof-
      have \<open>complex_vector.span (range (\<lambda> u. (fst u) \<otimes>\<^sub>a (snd u))) = UNIV\<close>
        by (simp add: atensor_onto)
      hence \<open>\<exists> t r. finite t \<and> t \<subseteq> (range (\<lambda> u. (fst u) \<otimes>\<^sub>a (snd u))) \<and> z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      proof -
        have "\<forall>a. \<exists>A f. a = (\<Sum>a\<in>A. f a *\<^sub>C a) \<and> finite A \<and> A \<subseteq> range (\<lambda>p. (fst p::'v) \<otimes>\<^sub>a (snd p::'w))"
          using \<open>complex_vector.span (range (\<lambda>u. fst u \<otimes>\<^sub>a snd u)) = UNIV\<close> complex_vector.span_explicit by blast
        then show ?thesis
          by meson
      qed 
      then obtain t r where \<open>finite t\<close> and \<open>t \<subseteq> (range (\<lambda> u. (fst u) \<otimes>\<^sub>a (snd u)))\<close>
        and \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        by blast
      from \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      have \<open>K z = (\<Sum>a\<in>t. r a *\<^sub>C (K a))\<close>
        using \<open>clinear K\<close> unfolding clinear_def
        by (smt \<open>clinear K\<close> complex_vector.linear_scale complex_vector.linear_sum sum.cong)
      also have \<open>\<dots> = (\<Sum>a\<in>t. r a *\<^sub>C (H a))\<close>
      proof-
        have  \<open>a \<in> t \<Longrightarrow> K a = H a\<close>
          for a
          using \<open>\<And> x y. K (x \<otimes>\<^sub>a y) = H (x \<otimes>\<^sub>a y)\<close>
            \<open>t \<subseteq> (range (\<lambda> u. (fst u) \<otimes>\<^sub>a (snd u)))\<close>
          by blast
        thus ?thesis
          by auto 
      qed
      also have \<open>\<dots> = H (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
        by (smt \<open>clinear H\<close> complex_vector.linear_scale complex_vector.linear_sum sum.cong)
      also have \<open>\<dots> = H z\<close>
        using \<open>z = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close> by auto
      finally show ?thesis by blast
    qed
    thus ?thesis
      by blast 
  qed
  ultimately show ?thesis by blast
qed                                                     


(* proposition 1. https://themath.net/linear-independence-properties-of-tensor-products-of-normed-linear-spaces *)
(* TODO: It is probably more natural to formulate this as

exists A :: ('a*'b) set,
complex_independent (fst`A)
complex_independent (snd`A)
u=sum (fst a \<otimes> snd a)

And similar for the other propositions from that webpage?

 *)
(* TODO: I believe this is called a Schmidt decomposition *)
lemma atensor_normal_explicit:
  fixes u :: \<open>'a::complex_vector \<otimes>\<^sub>a 'b::complex_vector\<close>
  shows \<open>\<exists> A::'a set. \<exists> \<phi>::'a \<Rightarrow> 'b. finite A  \<and> 
  complex_independent A \<and> complex_independent (\<phi> ` A) \<and>
  u = (\<Sum>a\<in>A. a \<otimes>\<^sub>a (\<phi> a))\<close>
proof-
  have \<open>complex_vector.span (range ( \<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) )) = (UNIV:: ('a \<otimes>\<^sub>a 'b) set)\<close>
    by (simp add: atensor_onto)
  hence \<open>u \<in> complex_vector.span (range ( \<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ))\<close>
    by simp
  hence \<open>\<exists> t r. finite t \<and> t \<subseteq> range ( \<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) \<and> u = (\<Sum>z\<in>t. r z *\<^sub>C z)\<close>
  proof -
    have "\<exists>A f. u = (\<Sum>a\<in>A. f a *\<^sub>C a) \<and> finite A \<and> A \<subseteq> range (\<lambda>p. fst p \<otimes>\<^sub>a snd p)"
      using \<open>u \<in> complex_vector.span (range (\<lambda>z. fst z \<otimes>\<^sub>a snd z))\<close> complex_vector.span_explicit by blast
    then show ?thesis
      by blast
  qed 
  then obtain t r where  \<open>finite t\<close> and \<open>t \<subseteq> range ( \<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) )\<close> 
    and \<open>u = (\<Sum>z\<in>t. r z *\<^sub>C z)\<close>
    by blast
  show ?thesis sorry
qed


(* proposition 2. https://themath.net/linear-independence-properties-of-tensor-products-of-normed-linear-spaces *)
lemma atensor_normal_independent:
  fixes \<phi>::\<open>'a::complex_vector \<Rightarrow> 'b::complex_vector\<close> and A::\<open>'a set\<close>
  assumes \<open>finite A\<close> and \<open>complex_independent A\<close> and \<open>(\<Sum>a\<in>A. a \<otimes>\<^sub>a (\<phi> a)) = 0\<close> 
  shows \<open>\<forall> a\<in>A. \<phi> a = 0\<close>
  sorry

(* proposition 3. https://themath.net/linear-independence-properties-of-tensor-products-of-normed-linear-spaces *)
lemma atensor_complex_independent:
  fixes A::\<open>'a::complex_vector set\<close> and B::\<open>'b::complex_vector set\<close>
  assumes \<open>complex_independent A\<close> and \<open>complex_independent B\<close>
  shows \<open>complex_independent {a\<otimes>\<^sub>ab| a b. a\<in>A \<and> b\<in>B}\<close>
proof-
  have \<open>S \<subseteq> (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) ` (A \<times> B) \<Longrightarrow> finite S \<Longrightarrow>
   (\<Sum>s\<in>S. (f s) *\<^sub>C s) = 0 \<Longrightarrow> \<forall>s\<in>S. f s = 0\<close>
    for S f
  proof-
    assume \<open>S \<subseteq> (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z) ) ` (A \<times> B)\<close> and
      \<open>finite S\<close> and \<open>(\<Sum>s\<in>S. (f s) *\<^sub>C s) = 0\<close>
    thus \<open>\<forall>s\<in>S. f s = 0\<close>
      sorry
  qed
  hence \<open>complex_independent ( (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z)) ` (A \<times> B) )\<close>
    using complex_vector.independent_explicit_finite_subsets by force
  moreover have \<open>( (\<lambda> z. (fst z) \<otimes>\<^sub>a (snd z)) ` (A \<times> B) ) = {a\<otimes>\<^sub>ab| a b. a\<in>A \<and> b\<in>B}\<close>
    using tensor_of_sets[where A = "A" and B = "B"] by blast
  ultimately show ?thesis 
    by simp
qed

definition separable :: \<open>('a::complex_vector \<otimes>\<^sub>a 'b::complex_vector) \<Rightarrow> bool\<close> where
  \<open>separable \<psi> = (\<exists> x y. \<psi> = x \<otimes>\<^sub>a y)\<close>

(* TODO: I don't think one needs a definition for this, it's just \<not> separable (or, if it's *really* needed,
it could be an abbreviation *)
definition entangled :: \<open>('a::complex_vector \<otimes>\<^sub>a 'b::complex_vector) \<Rightarrow> bool\<close> where
  \<open>entangled \<psi> = ( \<not>(separable \<psi>) )\<close>


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
  show "norm (x::'a \<otimes>\<^sub>a 'b) = sqrt (norm \<langle>x, x\<rangle>)"
    for x :: "'a \<otimes>\<^sub>a 'b"
    unfolding norm_atensor_def by blast
qed

end

end
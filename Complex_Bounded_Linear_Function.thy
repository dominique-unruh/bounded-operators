(*
Authors:

  Dominique Unruh, University of Tartu, unruh@ut.ee
  Jose Manuel Rodriguez Caballero, University of Tartu, jose.manuel.rodriguez.caballero@ut.ee

*)

theory Complex_Bounded_Linear_Function
  imports 
    Complex_Inner_Product One_Dimensional_Spaces
    Banach_Steinhaus.Banach_Steinhaus
    "HOL-Types_To_Sets.Types_To_Sets"
    Complex_Bounded_Linear_Function0
begin

subsection \<open>Misc basic facts and declarations\<close>

notation cblinfun_apply (infixr "*\<^sub>V" 70)

(* Renamed from apply_id_cblinfun *)
lemma id_cblinfun_apply[simp]: "id_cblinfun *\<^sub>V \<psi> = \<psi>"
  apply transfer by simp

(* Renamed from isCont_applyOp *)
lemma isCont_cblinfun_apply[simp]: "isCont ((*\<^sub>V) A) \<psi>"
  apply transfer
  by (simp add: clinear_continuous_at) 

(* Use cblinfun.zero_left instead *)
(* lemma applyOp0[simp]: "0 *\<^sub>V \<psi> = 0" *)

declare cblinfun.scaleC_left[simp]

lemma cblinfun_apply_clinear[simp]: \<open>clinear (cblinfun_apply A)\<close>
  using bounded_clinear.axioms(1) cblinfun_apply by blast

lemma cblinfun_cinner_eqI:
  fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assumes \<open>\<And>\<psi>. cinner \<psi> (A *\<^sub>V \<psi>) = cinner \<psi> (B *\<^sub>V \<psi>)\<close>
  shows \<open>A = B\<close>
proof -
  define C where \<open>C = A - B\<close>
  have C0[simp]: \<open>cinner \<psi> (C \<psi>) = 0\<close> for \<psi>
    by (simp add: C_def assms cblinfun.diff_left cinner_diff_right)
  { fix f g \<alpha>
    have \<open>0 = cinner (f + \<alpha> *\<^sub>C g) (C *\<^sub>V (f + \<alpha> *\<^sub>C g))\<close>
      by (simp add: cinner_diff_right minus_cblinfun.rep_eq)
    also have \<open>\<dots> = \<alpha> *\<^sub>C cinner f (C g) + cnj \<alpha> *\<^sub>C cinner g (C f)\<close>
      by (smt (z3) C0 add.commute add.right_neutral cblinfun.add_right cblinfun.scaleC_right cblinfun_cinner_right.rep_eq cinner_add_left cinner_scaleC_left complex_scaleC_def)
    finally have \<open>\<alpha> *\<^sub>C cinner f (C g) = - cnj \<alpha> *\<^sub>C cinner g (C f)\<close>
      by (simp add: eq_neg_iff_add_eq_0)
  }
  then have \<open>cinner f (C g) = 0\<close> for f g
    by (metis complex_cnj_i complex_cnj_one complex_vector.scale_cancel_right complex_vector.scale_left_imp_eq equation_minus_iff i_squared mult_eq_0_iff one_neq_neg_one)
  then have \<open>C g = 0\<close> for g
    using cinner_eq_zero_iff by blast
  then have \<open>C = 0\<close>
    by (simp add: cblinfun_eqI)
  then show \<open>A = B\<close>
    using C_def by auto
qed

lemma id_cblinfun_not_0[simp]: \<open>(id_cblinfun :: 'a::{complex_normed_vector, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L _) \<noteq> 0\<close>
  by (metis (full_types) Extra_General.UNIV_not_singleton cblinfun.zero_left cblinfun_id_cblinfun_apply ex_norm1 norm_zero one_neq_zero)

subsection \<open>Algebraic properties of real cblinfun operators\<close>
(* TODO rename section *)

instantiation blinfun :: (real_normed_vector, complex_normed_vector) "complex_normed_vector"
begin
lift_definition scaleC_blinfun :: \<open>complex \<Rightarrow>
 ('a::real_normed_vector, 'b::complex_normed_vector) blinfun \<Rightarrow>
 ('a, 'b) blinfun\<close>
  is \<open>\<lambda> c::complex. \<lambda> f::'a\<Rightarrow>'b. (\<lambda> x. c *\<^sub>C (f x) )\<close> 
proof
  fix c::complex and f :: \<open>'a\<Rightarrow>'b\<close> and b1::'a and b2::'a
  assume \<open>bounded_linear f\<close>
  show \<open>c *\<^sub>C f (b1 + b2) = c *\<^sub>C f b1 + c *\<^sub>C f b2\<close>
    by (simp add: \<open>bounded_linear f\<close> linear_simps scaleC_add_right)

  fix c::complex and f :: \<open>'a\<Rightarrow>'b\<close> and b::'a and r::real
  assume \<open>bounded_linear f\<close>
  show \<open>c *\<^sub>C f (r *\<^sub>R b) = r *\<^sub>R (c *\<^sub>C f b)\<close>
    by (simp add: \<open>bounded_linear f\<close> linear_simps(5) scaleR_scaleC)

  fix c::complex and f :: \<open>'a\<Rightarrow>'b\<close>
  assume \<open>bounded_linear f\<close>

  have \<open>\<exists> K. \<forall> x. norm (f x) \<le> norm x * K\<close>
    using \<open>bounded_linear f\<close>
    by (simp add: bounded_linear.bounded)      
  then obtain K where \<open>\<forall> x. norm (f x) \<le> norm x * K\<close>
    by blast
  have \<open>cmod c \<ge> 0\<close>
    by simp
  hence \<open>\<forall> x. (cmod c) * norm (f x) \<le> (cmod c) * norm x * K\<close>
    using  \<open>\<forall> x. norm (f x) \<le> norm x * K\<close> 
    by (metis ordered_comm_semiring_class.comm_mult_left_mono vector_space_over_itself.scale_scale)
  moreover have \<open>norm (c *\<^sub>C f x) = (cmod c) * norm (f x)\<close>
    for x
    by simp
  ultimately show \<open>\<exists>K. \<forall>x. norm (c *\<^sub>C f x) \<le> norm x * K\<close>
    by (metis ab_semigroup_mult_class.mult_ac(1) mult.commute)
qed

instance
proof
  have "r *\<^sub>R x = complex_of_real r *\<^sub>C x"
    for x :: "('a, 'b) blinfun" and r
    apply transfer
    by (simp add: scaleR_scaleC)
  thus "((*\<^sub>R) r::'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> _) = (*\<^sub>C) (complex_of_real r)" for r
    by auto
  show "a *\<^sub>C (x + y) = a *\<^sub>C x + a *\<^sub>C y"
    for a :: complex and x y :: "'a \<Rightarrow>\<^sub>L 'b"
    apply transfer
    by (simp add: scaleC_add_right)

  show "(a + b) *\<^sub>C x = a *\<^sub>C x + b *\<^sub>C x"
    for a b :: complex and x :: "'a \<Rightarrow>\<^sub>L 'b"
    apply transfer
    by (simp add: scaleC_add_left)

  show "a *\<^sub>C b *\<^sub>C x = (a * b) *\<^sub>C x"
    for a b :: complex and x :: "'a \<Rightarrow>\<^sub>L 'b"
    apply transfer
    by simp

  have \<open>1 *\<^sub>C f x = f x\<close>
    for f :: \<open>'a\<Rightarrow>'b\<close> and x
    by auto
  thus "1 *\<^sub>C x = x"
    for x :: "'a \<Rightarrow>\<^sub>L 'b"
    by (simp add: scaleC_blinfun.rep_eq blinfun_eqI)   

  have \<open>onorm (\<lambda>x. a *\<^sub>C f x) = cmod a * onorm f\<close>
    if \<open>bounded_linear f\<close>
    for f :: \<open>'a \<Rightarrow> 'b\<close> and a :: complex
  proof-
    have \<open>cmod a \<ge> 0\<close>
      by simp
    have \<open>\<exists> K::real. \<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
      using \<open>bounded_linear f\<close> le_onorm by fastforce
    then obtain K::real where \<open>\<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
      by blast
    hence  \<open>\<forall> x. (cmod a) *(\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> (cmod a) * K\<close>
      using \<open>cmod a \<ge> 0\<close> 
      by (metis abs_ereal.simps(1) abs_ereal_pos   abs_pos ereal_mult_left_mono  times_ereal.simps(1))
    hence  \<open>\<forall> x.  (\<bar> ereal ((cmod a) * (norm (f x)) / (norm x)) \<bar>) \<le> (cmod a) * K\<close>
      by simp
    hence \<open>bdd_above {ereal (cmod a * (norm (f x)) / (norm x)) | x. True}\<close>
      by simp
    moreover have \<open>{ereal (cmod a * (norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
      by auto
    ultimately have p1: \<open>(SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>) \<le> cmod a * K\<close>
      using \<open>\<forall> x. \<bar> ereal (cmod a * (norm (f x)) / (norm x)) \<bar> \<le> cmod a * K\<close>
        Sup_least mem_Collect_eq
      by (simp add: SUP_le_iff) 
    have  p2: \<open>\<And>i. i \<in> UNIV \<Longrightarrow> 0 \<le> ereal (cmod a * norm (f i) / norm i)\<close>
      by simp
    hence \<open>\<bar>SUP x. ereal (cmod a * (norm (f x)) / (norm x))\<bar>
              \<le> (SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>)\<close>    
      using  \<open>bdd_above {ereal (cmod a * (norm (f x)) / (norm x)) | x. True}\<close>
        \<open>{ereal (cmod a * (norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
      by (metis (mono_tags, lifting) SUP_upper2 Sup.SUP_cong UNIV_I 
          p2 abs_ereal_ge0 ereal_le_real)
    hence \<open>\<bar>SUP x. ereal (cmod a * (norm (f x)) / (norm x))\<bar> \<le> cmod a * K\<close>
      using  \<open>(SUP x. \<bar>ereal (cmod a * (norm (f x)) / (norm x))\<bar>) \<le> cmod a * K\<close>
      by simp
    hence \<open>\<bar> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. (cmod a) * (norm (f x)) / norm x) i)) \<bar> \<noteq> \<infinity>\<close>
      by auto
    hence w2: \<open>( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. cmod a * (norm (f x)) / norm x) i))
             = ereal ( Sup ((\<lambda> x. cmod a * (norm (f x)) / norm x) ` (UNIV::'a set) ))\<close>
      by (simp add: ereal_SUP) 
    have \<open>(UNIV::('a set)) \<noteq> {}\<close>
      by simp
    moreover have \<open>\<And> i. i \<in> (UNIV::('a set)) \<Longrightarrow> (\<lambda> x. (norm (f x)) / norm x :: ereal) i \<ge> 0\<close>
      by simp
    moreover have \<open>cmod a \<ge> 0\<close>
      by simp
    ultimately have \<open>(SUP i\<in>(UNIV::('a set)). ((cmod a)::ereal) * (\<lambda> x. (norm (f x)) / norm x :: ereal) i ) 
        = ((cmod a)::ereal) * ( SUP i\<in>(UNIV::('a set)). (\<lambda> x. (norm (f x)) / norm x :: ereal) i )\<close>
      by (simp add: Sup_ereal_mult_left')
    hence \<open>(SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) ) 
        = ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) )\<close>
      by simp
    hence z1: \<open>real_of_ereal ( (SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) ) )
        = real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )\<close>
      by simp
    have z2: \<open>real_of_ereal (SUP x. ((cmod a)::ereal) * ( (norm (f x)) / norm x :: ereal) ) 
                  = (SUP x. cmod a * (norm (f x) / norm x))\<close>
      using w2
      by auto 
    have \<open>real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )
                =  (cmod a) * real_of_ereal ( SUP x. ( (norm (f x)) / norm x :: ereal) )\<close>
      by simp
    moreover have \<open>real_of_ereal ( SUP x. ( (norm (f x)) / norm x :: ereal) )
                  = ( SUP x. ((norm (f x)) / norm x) )\<close>
    proof-
      have \<open>\<bar> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. (norm (f x)) / norm x) i)) \<bar> \<noteq> \<infinity>\<close>
      proof-
        have \<open>\<exists> K::real. \<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
          using \<open>bounded_linear f\<close> le_onorm by fastforce
        then obtain K::real where \<open>\<forall> x. (\<bar> ereal ((norm (f x)) / (norm x)) \<bar>) \<le> K\<close>
          by blast
        hence \<open>bdd_above {ereal ((norm (f x)) / (norm x)) | x. True}\<close>
          by simp
        moreover have \<open>{ereal ((norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
          by auto
        ultimately have \<open>(SUP x. \<bar>ereal ((norm (f x)) / (norm x))\<bar>) \<le> K\<close>
          using \<open>\<forall> x. \<bar> ereal ((norm (f x)) / (norm x)) \<bar> \<le> K\<close>
            Sup_least mem_Collect_eq
          by (simp add: SUP_le_iff) 
        hence \<open>\<bar>SUP x. ereal ((norm (f x)) / (norm x))\<bar>
              \<le> (SUP x. \<bar>ereal ((norm (f x)) / (norm x))\<bar>)\<close>
          using  \<open>bdd_above {ereal ((norm (f x)) / (norm x)) | x. True}\<close>
            \<open>{ereal ((norm (f x)) / (norm x)) | x. True} \<noteq> {}\<close>
          by (metis (mono_tags, lifting) SUP_upper2 Sup.SUP_cong UNIV_I \<open>\<And>i. i \<in> UNIV \<Longrightarrow> 0 \<le> ereal (norm (f i) / norm i)\<close> abs_ereal_ge0 ereal_le_real)
        hence \<open>\<bar>SUP x. ereal ((norm (f x)) / (norm x))\<bar> \<le> K\<close>
          using  \<open>(SUP x. \<bar>ereal ((norm (f x)) / (norm x))\<bar>) \<le> K\<close>
          by simp
        thus ?thesis
          by auto 
      qed
      hence \<open> ( SUP i\<in>UNIV::'a set. ereal ((\<lambda> x. (norm (f x)) / norm x) i))
             = ereal ( Sup ((\<lambda> x. (norm (f x)) / norm x) ` (UNIV::'a set) ))\<close>
        by (simp add: ereal_SUP) 
      thus ?thesis
        by simp         
    qed
    have z3: \<open>real_of_ereal ( ((cmod a)::ereal) * ( SUP x. ( (norm (f x)) / norm x :: ereal) ) )
                = cmod a * (SUP x. norm (f x) / norm x)\<close>
      by (simp add: \<open>real_of_ereal (SUP x. ereal (norm (f x) / norm x)) = (SUP x. norm (f x) / norm x)\<close>)
    hence w1: \<open>(SUP x. cmod a * (norm (f x) / norm x)) =
          cmod a * (SUP x. norm (f x) / norm x)\<close>
      using z1 z2 by linarith     
    have v1: \<open>onorm (\<lambda>x. a *\<^sub>C f x) = (SUP x. norm (a *\<^sub>C f x) / norm x)\<close>
      by (simp add: onorm_def)
    have v2: \<open>(SUP x. norm (a *\<^sub>C f x) / norm x) = (SUP x. ((cmod a) * norm (f x)) / norm x)\<close>
      by simp
    have v3: \<open>(SUP x. ((cmod a) * norm (f x)) / norm x) =  (SUP x. (cmod a) * ((norm (f x)) / norm x))\<close>
      by simp
    have v4: \<open>(SUP x. (cmod a) * ((norm (f x)) / norm x)) = (cmod a) *  (SUP x. ((norm (f x)) / norm x))\<close>
      using w1
      by blast
    show \<open>onorm (\<lambda>x. a *\<^sub>C f x) = cmod a * onorm f\<close>
      using v1 v2 v3 v4
      by (metis (mono_tags, lifting) onorm_def)
  qed
  thus \<open>norm (a *\<^sub>C x) = cmod a * norm x\<close> 
    for a::complex and x::\<open>('a, 'b) blinfun\<close>
    apply transfer
    by blast
qed
end

(* We do not have clinear_blinfun_compose_right *)
lemma clinear_blinfun_compose_left: \<open>clinear (\<lambda>x. blinfun_compose x y)\<close>
  by (auto intro!: clinearI simp: blinfun_eqI scaleC_blinfun.rep_eq bounded_bilinear.add_left
                                  bounded_bilinear_blinfun_compose)

(* lemma trivial_UNIV_blinfun:
  fixes f::\<open>'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close> 
  assumes \<open>(UNIV::'a set) = 0\<close>
  shows \<open>f = 0\<close>
proof (rule blinfun_eqI)
  fix x :: 'a
  have \<open>x = 0\<close>
    using assms by auto
  then show \<open>f *\<^sub>v x = 0 *\<^sub>v x\<close>
    by auto
qed *)

subsection \<open>Topological properties of real cblinfun operators\<close>

instantiation blinfun :: (real_normed_vector, cbanach) "cbanach"
begin
instance..
end

(* lemma onorm_strong:
  fixes f::\<open>nat \<Rightarrow> 'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
    and l::\<open>'a  \<Rightarrow>\<^sub>L 'b\<close> and x::'a
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda>n. (blinfun_apply (f n)) x) \<longlonglongrightarrow> (blinfun_apply l) x\<close>
    using _ assms apply (rule tendsto_compose)
    using continuous_within linear_continuous_at by blast *)

lemma blinfun_compose_assoc: "(A o\<^sub>L B) o\<^sub>L C = A o\<^sub>L (B  o\<^sub>L C)"
  by (simp add: blinfun_eqI)

(* lemma times_blinfun_dist1:
  fixes a b :: "'b::real_normed_vector \<Rightarrow>\<^sub>L 'c::real_normed_vector"
    and c :: "'a::real_normed_vector \<Rightarrow>\<^sub>L 'b"
  shows "(a + b) o\<^sub>L c = (a o\<^sub>L c) + (b o\<^sub>L c)"
  by (meson bounded_bilinear.add_left bounded_bilinear_blinfun_compose) *)

(* lemma times_blinfun_dist2:
  fixes a b :: "'a::real_normed_vector \<Rightarrow>\<^sub>L 'b::real_normed_vector"
    and c :: "'b  \<Rightarrow>\<^sub>L 'c::real_normed_vector"
  shows "c o\<^sub>L (a + b) = (c o\<^sub>L a) + (c o\<^sub>L b)"
proof-
  have z1: \<open>bounded_linear (blinfun_apply c)\<close>
    using blinfun_apply by auto

  have \<open>(c  o\<^sub>L (a + b)) *\<^sub>v x = ( (c  o\<^sub>L a) +  (c  o\<^sub>L b) ) *\<^sub>v x\<close>
    for x
  proof-
    have \<open>blinfun_apply (c  o\<^sub>L (a + b)) x = (blinfun_apply c) ( (blinfun_apply (a + b)) x )\<close>
      by simp
    also have \<open>\<dots> = (blinfun_apply c) ( blinfun_apply a x + blinfun_apply b x )\<close>
      by (simp add: plus_blinfun.rep_eq)
    also have \<open>\<dots> = (blinfun_apply c) ( blinfun_apply a x ) + (blinfun_apply c) ( blinfun_apply b x )\<close>
      using  \<open>bounded_linear (blinfun_apply c)\<close>
      unfolding bounded_clinear_def linear_def
      by (simp add: z1 linear_simps(1))
    also have \<open>\<dots> = ( (blinfun_apply c) \<circ> (blinfun_apply a) ) x
                  + ( (blinfun_apply c) \<circ> (blinfun_apply b) ) x\<close>
      by simp
    finally have \<open>blinfun_apply (c o\<^sub>L (a + b)) x = blinfun_apply ( (c o\<^sub>L a) +  (c o\<^sub>L b) ) x\<close>
      by (simp add: blinfun.add_left)      
    thus ?thesis
      by simp 
  qed
  hence \<open>blinfun_apply (c  o\<^sub>L (a + b)) = blinfun_apply ( (c  o\<^sub>L a) +  (c  o\<^sub>L b) )\<close>
    by blast
  thus ?thesis 
    using blinfun_apply_inject
    by blast  
qed *)

(* lemma times_blinfun_scaleC:
  fixes f::"'b::complex_normed_vector \<Rightarrow>\<^sub>L'c::complex_normed_vector" 
    and g::"'a::complex_normed_vector \<Rightarrow>\<^sub>L 'b"
  assumes \<open>\<forall> c. \<forall> x. ( *\<^sub>v) f (c *\<^sub>C x) = c *\<^sub>C (( *\<^sub>v) f x)\<close>
    and \<open>\<forall> c. \<forall> x. ( *\<^sub>v) g (c *\<^sub>C x) = c *\<^sub>C (( *\<^sub>v) g x)\<close>
  shows \<open>\<forall> c. \<forall> x. ( *\<^sub>v) (f  o\<^sub>L g) (c *\<^sub>C x) = c *\<^sub>C (( *\<^sub>v) (f  o\<^sub>L g) x)\<close>
  by (simp add: assms(1) assms(2)) *)


(* Use clinear_blinfun_compose_left instead *)
(* lemma rscalar_op_op:
  fixes A::"'b::real_normed_vector \<Rightarrow>\<^sub>L 'c::complex_normed_vector" 
    and B::"'a::real_normed_vector \<Rightarrow>\<^sub>L 'b"
  shows \<open>(a *\<^sub>C A) o\<^sub>L B = a *\<^sub>C (A o\<^sub>L B)\<close>
  by (simp add: blinfun_eqI scaleC_blinfun.rep_eq) *)

(* lemma op_rscalar_op: 
  fixes A::"'b::complex_normed_vector  \<Rightarrow>\<^sub>L 'c::complex_normed_vector" 
    and B::"'a::real_normed_vector  \<Rightarrow>\<^sub>L  'b"
  assumes \<open>\<And>c. \<And>x. A *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (A *\<^sub>v x)\<close>
  shows \<open>A  o\<^sub>L (a *\<^sub>C B) = a *\<^sub>C (A  o\<^sub>L B)\<close>
proof-
  have \<open>blinfun_apply (A o\<^sub>L (a *\<^sub>C B)) x  = blinfun_apply ((a *\<^sub>C A) o\<^sub>L B) x\<close>
    for x
  proof-
    have \<open>blinfun_apply (A o\<^sub>L (a *\<^sub>C B)) x
        = ( (blinfun_apply A) \<circ> (blinfun_apply (a *\<^sub>C B)) ) x\<close>
      by simp
    also have \<open>... = 
        (blinfun_apply A) ( (blinfun_apply (a *\<^sub>C B))  x )\<close>
      by simp
    also have \<open>... = 
        (blinfun_apply A) (a *\<^sub>C ( (blinfun_apply  B) x ))\<close>
      by (simp add: scaleC_blinfun.rep_eq)
    also have \<open>... = 
       a *\<^sub>C ( (blinfun_apply A) ( (blinfun_apply  B) x ) )\<close>
      using assms by auto      
    finally show ?thesis
      by (simp add: scaleC_blinfun.rep_eq)       
  qed
  hence \<open>blinfun_apply (A o\<^sub>L (a *\<^sub>C B))  = blinfun_apply ((a *\<^sub>C A) o\<^sub>L B)\<close>
    by blast     
  hence \<open>A o\<^sub>L (a *\<^sub>C B) = (a *\<^sub>C A) o\<^sub>L B\<close>
    using blinfun_apply_inject by auto    
  thus ?thesis
    by (simp add: rscalar_op_op)  
qed *)

subsection \<open>Complex cblinfun operators\<close>

(* typedef\<^marker>\<open>tag important\<close> (overloaded) ('a, 'b) cblinfun ("(_ \<Rightarrow>\<^sub>C\<^sub>L /_)" [22, 21] 21) =
  "{f::'a::complex_normed_vector\<Rightarrow>'b::complex_normed_vector. bounded_clinear f}"
  morphisms cblinfun_apply cBlinfun
  using bounded_clinear_zero by blast
 *)

(* setup_lifting type_definition_cblinfun *)

(* declare [[coercion
      "cblinfun_apply :: ('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector) \<Rightarrow> 'a \<Rightarrow> 'b"]]
 *)

lift_definition blinfun_of_cblinfun::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector 
  \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b\<close> is "id"
  apply transfer by (simp add: bounded_clinear.bounded_linear)

lift_definition blinfun_cblinfun_eq :: 
  \<open>'a \<Rightarrow>\<^sub>L 'b \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector \<Rightarrow> bool\<close> is "(=)" .

lemma blinfun_cblinfun_eq_bi_unique[transfer_rule]: \<open>bi_unique blinfun_cblinfun_eq\<close>
  unfolding bi_unique_def apply transfer by auto

lemma blinfun_cblinfun_eq_right_total[transfer_rule]: \<open>right_total blinfun_cblinfun_eq\<close>
  unfolding right_total_def apply transfer
  by (simp add: bounded_clinear.bounded_linear)

named_theorems cblinfun_blinfun_transfer

lemma cblinfun_blinfun_transfer_0[cblinfun_blinfun_transfer]:
  "blinfun_cblinfun_eq (0::(_,_) blinfun) (0::(_,_) cblinfun)"
  apply transfer by simp

lemma cblinfun_blinfun_transfer_plus[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) (+) (+)"
  unfolding rel_fun_def apply transfer by auto

lemma cblinfun_blinfun_transfer_minus[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) (-) (-)"
  unfolding rel_fun_def apply transfer by auto

lemma cblinfun_blinfun_transfer_uminus[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) (uminus) (uminus)"
  unfolding rel_fun_def apply transfer by auto

definition "real_complex_eq r c \<longleftrightarrow> complex_of_real r = c"

lemma bi_unique_real_complex_eq[transfer_rule]: \<open>bi_unique real_complex_eq\<close>
  unfolding real_complex_eq_def bi_unique_def by auto

lemma left_total_real_complex_eq[transfer_rule]: \<open>left_total real_complex_eq\<close>
  unfolding real_complex_eq_def left_total_def by auto

lemma cblinfun_blinfun_transfer_scaleC[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(real_complex_eq ===> blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) (scaleR) (scaleC)"
  unfolding rel_fun_def apply transfer
  by (simp add: real_complex_eq_def scaleR_scaleC)

lemma cblinfun_blinfun_transfer_cBlinfun[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(eq_onp bounded_clinear ===> blinfun_cblinfun_eq) Blinfun cBlinfun"
  unfolding rel_fun_def blinfun_cblinfun_eq.rep_eq eq_onp_def
  by (auto simp: cBlinfun_inverse Blinfun_inverse bounded_clinear.bounded_linear)

lemma cblinfun_blinfun_transfer_norm[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> (=)) norm norm"
  unfolding rel_fun_def apply transfer by auto

lemma cblinfun_blinfun_transfer_dist[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq ===> (=)) dist dist"
  unfolding rel_fun_def dist_norm apply transfer by auto

lemma cblinfun_blinfun_transfer_sgn[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) sgn sgn"
  unfolding rel_fun_def sgn_blinfun_def sgn_cblinfun_def apply transfer 
  by (auto simp: scaleR_scaleC)

lemma cblinfun_blinfun_transfer_Cauchy[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(((=) ===> blinfun_cblinfun_eq) ===> (=)) Cauchy Cauchy"
proof -
  note cblinfun_blinfun_transfer[transfer_rule]
  show ?thesis
    unfolding Cauchy_def
    by transfer_prover
qed

lemma cblinfun_blinfun_transfer_tendsto[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(((=) ===> blinfun_cblinfun_eq) ===> blinfun_cblinfun_eq ===> (=) ===> (=)) tendsto tendsto"
proof -
  note cblinfun_blinfun_transfer[transfer_rule]
  show ?thesis
    unfolding tendsto_iff
    by transfer_prover
qed

lemma cblinfun_blinfun_transfer_compose[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> blinfun_cblinfun_eq ===> blinfun_cblinfun_eq) (o\<^sub>L) (o\<^sub>C\<^sub>L)"
  unfolding rel_fun_def apply transfer by auto

lemma cblinfun_blinfun_transfer_apply[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> (=) ===> (=)) blinfun_apply cblinfun_apply"
  unfolding rel_fun_def apply transfer by auto

lemma blinfun_of_cblinfun_inj:
  \<open>blinfun_of_cblinfun f = blinfun_of_cblinfun g \<Longrightarrow> f = g\<close>
  by (metis cblinfun_apply_inject blinfun_of_cblinfun.rep_eq)

lemma blinfun_of_cblinfun_inv:
  assumes "\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)"
  shows "\<exists>g. blinfun_of_cblinfun g = f"
  using assms
proof transfer
  show "\<exists>g\<in>Collect bounded_clinear. id g = f"
    if "bounded_linear f"
      and "\<And>c x. f (c *\<^sub>C x) = c *\<^sub>C f x"
    for f :: "'a \<Rightarrow> 'b"
    using that bounded_linear_bounded_clinear by auto 
qed  

(* lemma blinfun_of_cblinfun_inv_uniq:
  assumes "\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)"
  shows  \<open>\<exists>! g. blinfun_of_cblinfun g = f\<close> *)

(* lemma blinfun_of_cblinfun_prelim:
  fixes c and x
  shows \<open>(blinfun_of_cblinfun g) *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C ((blinfun_of_cblinfun g) *\<^sub>v x)\<close> *)

(* definition cblinfun_of_blinfun::
  "'a::complex_normed_vector \<Rightarrow>\<^sub>L 'b::complex_normed_vector \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" 
  where "cblinfun_of_blinfun = inv blinfun_of_cblinfun" *)

(* lemma cblinfun_blinfun:
  \<open>cblinfun_of_blinfun (blinfun_of_cblinfun f) = f\<close>
  by (metis (no_types, hide_lams) cblinfun_apply_inverse UNIV_I cblinfun_of_blinfun_def f_inv_into_f image_iff blinfun_of_cblinfun.rep_eq) *)

(* lemma blinfun_cblinfun:
  assumes "\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)"
  shows \<open>blinfun_of_cblinfun (cblinfun_of_blinfun f) = f\<close>
  using assms
  by (metis blinfun_of_cblinfun_inv cblinfun_blinfun)  *)


(* lemma cblinfun_of_blinfun_zero:
  "(0::('a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector)) 
  = cblinfun_of_blinfun (0::('a \<Rightarrow>\<^sub>L'b))" 
proof-
  have \<open>cblinfun_apply 0 t  = cblinfun_apply (SOME x. Blinfun (cblinfun_apply x) = 0) t\<close>
    for t
  proof-
    have \<open>cblinfun_apply (SOME x. Blinfun (cblinfun_apply x) = 0) t = 0\<close>
      by (metis (mono_tags, lifting) cBlinfun_inverse blinfun_apply_inverse bounded_clinear_zero mem_Collect_eq blinfun_of_cblinfun.rep_eq tfl_some zero_blinfun.abs_eq)
    moreover have \<open>cblinfun_apply 0 t = 0\<close>
      apply transfer by blast
    ultimately show ?thesis by simp
  qed
  hence \<open>cblinfun_apply 0  = cblinfun_apply (SOME x. Blinfun (cblinfun_apply x) = 0) \<close>
    by blast
  hence \<open>0 = (SOME x. Blinfun (cblinfun_apply x) = 0)\<close>
    using cblinfun_apply_inject
    by blast
  hence \<open>0 = inv (Blinfun \<circ> cblinfun_apply) 0\<close>
    unfolding inv_def
    by auto
  hence \<open>0 = inv (map_fun cblinfun_apply Blinfun id) 0\<close>
    unfolding map_fun_def 
    by auto
  thus ?thesis
    unfolding cblinfun_of_blinfun_def blinfun_of_cblinfun_def inv_def
    by blast
qed *)

lemma blinfun_of_cblinfun_zero:
  \<open>blinfun_of_cblinfun 0 = 0\<close>
  apply transfer by simp


(* lemma cblinfun_of_blinfun_plus:
  assumes \<open>\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)\<close>
    and \<open>\<And>c. \<And>x. g *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (g *\<^sub>v x)\<close>
  shows \<open>cblinfun_of_blinfun (f + g) = cblinfun_of_blinfun f + cblinfun_of_blinfun g\<close>
  using assms
  by (smt blinfun_cblinfun blinfun_eqI blinfun_of_cblinfun.rep_eq blinfun_of_cblinfun_inj 
      plus_blinfun.rep_eq plus_cblinfun.rep_eq scaleC_add_right)  *)

lemma blinfun_of_cblinfun_uminus:
  \<open>blinfun_of_cblinfun (- f) = - (blinfun_of_cblinfun f)\<close>
  apply transfer
  by auto

(* lemma cblinfun_of_blinfun_uminus:
  assumes \<open>\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)\<close>
  shows  \<open>cblinfun_of_blinfun (- f) = - (cblinfun_of_blinfun f)\<close>
  using assms
  by (metis (mono_tags) blinfun_cblinfun blinfun_of_cblinfun_inj blinfun_of_cblinfun_prelim blinfun_of_cblinfun_uminus) *)

lemma blinfun_of_cblinfun_minus:
  \<open>blinfun_of_cblinfun (f - g) = blinfun_of_cblinfun f - blinfun_of_cblinfun g\<close>
  apply transfer
  by auto

(* lemma cblinfun_of_blinfun_minus:
  assumes \<open>\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)\<close>
    and \<open>\<And>c. \<And>x. g *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (g *\<^sub>v x)\<close>
  shows \<open>cblinfun_of_blinfun (f - g) = cblinfun_of_blinfun f - cblinfun_of_blinfun g\<close>
  using assms
  unfolding cblinfun_of_blinfun_def inv_def
  by (smt cblinfun_blinfun blinfun_cblinfun blinfun_of_cblinfun_minus someI_ex) *)


lemma blinfun_of_cblinfun_scaleC:
  \<open>blinfun_of_cblinfun (c *\<^sub>C f) = c *\<^sub>C (blinfun_of_cblinfun f)\<close>
  apply transfer
  by auto

(* lemma cblinfun_of_blinfun_scaleC:
  assumes \<open>\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)\<close>
  shows \<open>cblinfun_of_blinfun ( c *\<^sub>C f ) = c *\<^sub>C (cblinfun_of_blinfun f)\<close>
  using assms
  by (metis (mono_tags) cblinfun_blinfun blinfun_cblinfun blinfun_of_cblinfun_scaleC) *)

lemma blinfun_of_cblinfun_scaleR:
  \<open>blinfun_of_cblinfun (c *\<^sub>R f) = c *\<^sub>R (blinfun_of_cblinfun f)\<close>
  apply transfer by auto

(* lemma cblinfun_of_blinfun_scaleR:
  assumes \<open>\<And>c. \<And>x. f *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C (f *\<^sub>v x)\<close>
  shows \<open>cblinfun_of_blinfun ( c *\<^sub>R f ) = c *\<^sub>R (cblinfun_of_blinfun f)\<close>
  using assms
  by (metis (mono_tags) cblinfun_blinfun blinfun_cblinfun blinfun_of_cblinfun_scaleR) *)

(* lemma cblinfun_of_blinfun_Blinfun:
  \<open>cblinfun_of_blinfun (Blinfun (cblinfun_apply f)) = f\<close>
  by (metis Quotient_cblinfun Quotient_rel_rep cblinfun_apply_inverse cblinfun_blinfun blinfun_of_cblinfun.abs_eq) *)

lemma blinfun_of_cblinfun_norm:
  fixes f::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  shows \<open>norm f = norm (blinfun_of_cblinfun f)\<close>
  apply transfer by auto

(* lemma blinfun_of_cblinfun_dist:
  fixes f::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  shows \<open>dist f g = dist (blinfun_of_cblinfun f) (blinfun_of_cblinfun g)\<close> *)

(* lemma blinfun_of_cblinfun_sgn:
  \<open>blinfun_of_cblinfun (sgn f) = (sgn (blinfun_of_cblinfun f))\<close> *)

(* Use cblinfun.add_right instead *)
(* lemma cblinfun_apply_add: "F *\<^sub>V (b1 + b2) = F *\<^sub>V b1 + F *\<^sub>V b2" *)

(* Use cblinfun.add_left instead *)
(* lemma apply_cblinfun_distr_left: "(A + B) *\<^sub>V x = A *\<^sub>V x + B *\<^sub>V x" *)

(* Use cblinfun.scaleC_right instead *)
(* lemma cblinfun_apply_scaleC: "F *\<^sub>V (r *\<^sub>C b) = r *\<^sub>C (F *\<^sub>V b)" *)

(* lemma cblinfun_apply_norm: "\<exists>K. \<forall>x. norm (F *\<^sub>V x) \<le> norm x * K " *)

(* lemma blinfun_of_cblinfun_Cauchy:
  assumes \<open>Cauchy f\<close> shows \<open>Cauchy (\<lambda> n. blinfun_of_cblinfun (f n))\<close>
  using assms unfolding Cauchy_def by (simp add: blinfun_of_cblinfun_dist)   *)

(* lemma cblinfun_of_blinfun_Cauchy:
  assumes \<open>Cauchy f\<close> and
    \<open>\<And>n::nat. \<And>c. \<And>x. (f n) *\<^sub>v (c *\<^sub>C x) = c *\<^sub>C ((f n) *\<^sub>v x)\<close>
  shows \<open>Cauchy (\<lambda> n. cblinfun_of_blinfun (f n))\<close> *)

(* lemma blinfun_of_cblinfun_lim:
  assumes \<open>f \<longlonglongrightarrow> l\<close>
  shows \<open>(\<lambda> n. blinfun_of_cblinfun (f n)) \<longlonglongrightarrow> blinfun_of_cblinfun l\<close> *)



subsection \<open>Composition\<close>

abbreviation (input) "timesOp == cblinfun_compose"

(* Closure is necessary. See email 47a3bb3d-3cc3-0934-36eb-3ef0f7b70a85@ut.ee *)
lift_definition cblinfun_image :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector
\<Rightarrow> 'a ccsubspace \<Rightarrow> 'b ccsubspace\<close>  (infixr "*\<^sub>S" 70)
  is "\<lambda>A S. closure (A ` S)"
  using  bounded_clinear_def closed_closure  closed_csubspace.intro
  by (simp add: bounded_clinear_def complex_vector.linear_subspace_image closure_is_closed_csubspace) 

lemma cblinfun_image_mono:
  assumes a1: "S \<le> T"
  shows "A *\<^sub>S S \<le> A *\<^sub>S T"
  using a1
  by (simp add: cblinfun_image.rep_eq closure_mono image_mono less_eq_ccsubspace.rep_eq)

lemma blinfun_of_cblinfun_cblinfun_compose:
  fixes f::\<open>'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector\<close>
    and g::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  shows \<open>blinfun_of_cblinfun (f  o\<^sub>C\<^sub>L g) = (blinfun_of_cblinfun f) o\<^sub>L (blinfun_of_cblinfun g)\<close>
  apply transfer by auto

(* Renamed from cblinfun_apply_assoc *)
lemma cblinfun_compose_assoc: 
  shows "(A o\<^sub>C\<^sub>L B) o\<^sub>C\<^sub>L C = A o\<^sub>C\<^sub>L (B o\<^sub>C\<^sub>L C)"
  by (metis (no_types, lifting) cblinfun_apply_inject fun.map_comp cblinfun_compose.rep_eq)

(* Use bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose instead *)
(* lemma cblinfun_apply_dist1:  
  fixes a b :: "'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
    and c :: "'a::complex_normed_vector   \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows "(a + b) o\<^sub>C\<^sub>L c = (a o\<^sub>C\<^sub>L c) + (b o\<^sub>C\<^sub>L c)"
 *)

(* Use bounded_cbilinear.add_right bounded_cbilinear_cblinfun_compose instead *)
(* lemma cblinfun_apply_dist2:
  fixes a b :: "'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector"
    and c :: "'b \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
  shows "c o\<^sub>C\<^sub>L (a + b) = (c o\<^sub>C\<^sub>L a) + (c o\<^sub>C\<^sub>L b)" *)

(* Use bounded_cbilinear.diff_right bounded_cbilinear_cblinfun_compose instead *)
(* lemma cblinfun_compose_minus:
  \<open>A o\<^sub>C\<^sub>L (B - C) = (A o\<^sub>C\<^sub>L B) - (A o\<^sub>C\<^sub>L C)\<close> *)


(* Renamed from OCL_zero *)
lemma cblinfun_compose_zero_right[simp]: "U o\<^sub>C\<^sub>L 0 = 0"
  using bounded_cbilinear.zero_right bounded_cbilinear_cblinfun_compose by blast

lemma cblinfun_compose_zero_left[simp]: "0 o\<^sub>C\<^sub>L U = 0"
  using bounded_cbilinear.zero_left bounded_cbilinear_cblinfun_compose by blast

(* Renamed from applyOp_0 *)
lemma cblinfun_image_0[simp]:  
  shows "U *\<^sub>S 0 = 0"
  thm zero_ccsubspace_def
  apply transfer
  by (simp add: bounded_clinear_def complex_vector.linear_0)

(* lemma times_comp:
  fixes A B \<psi>
  assumes a1: "bounded_clinear A" and a2: "bounded_clinear B" and a3: "closed_csubspace \<psi>"
  shows "closure ((A \<circ> B) ` \<psi>) = closure (A ` closure (B ` \<psi>))"
proof rule
  show \<open>closure ((A \<circ> B) ` \<psi>) \<subseteq> closure (A ` closure (B ` \<psi>))\<close>
    by (metis closure_mono closure_subset image_comp subset_image_iff)
  have \<open>A ` closure (B ` \<psi>) \<subseteq> closure (A ` B ` \<psi>)\<close>
    apply (rule closure_bounded_linear_image_subset)
    by (simp add: Complex_Vector_Spaces0.bounded_clinear.bounded_linear a1)
  then show \<open>closure (A ` closure (B ` \<psi>)) \<subseteq> closure ((A \<circ> B) ` \<psi>)\<close>
    by (simp add: closure_minimal image_comp)
qed *)


(* Renamed from cblinfun_apply_assoc_clinear_space *)
lemma cblinfun_compose_image: 
  \<open>(A o\<^sub>C\<^sub>L B) *\<^sub>S S =  A *\<^sub>S (B *\<^sub>S S)\<close>
  apply transfer unfolding image_comp[symmetric]
  apply (rule closure_bounded_linear_image_subset_eq[symmetric])
  by (simp add: bounded_clinear.bounded_linear)

(* Renamed from assoc_left, assoc_right *)
lemmas cblinfun_assoc_left = cblinfun_compose_assoc[symmetric] cblinfun_compose_image[symmetric] 
  add.assoc[where ?'a="'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space", symmetric]
lemmas cblinfun_assoc_right = cblinfun_compose_assoc cblinfun_compose_image
  add.assoc[where ?'a="'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space"]

(* Use complex_vector.scale_right_distrib instead *)
(* lemma scalar_times_op_add[simp]: "a *\<^sub>C (A + B) = a *\<^sub>C A + a *\<^sub>C B" 
  for A B :: "_::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L _::complex_normed_vector" *)

(* Use complex_vector.scale_right_diff_distrib instead *)
(* lemma scalar_times_op_minus[simp]: "a *\<^sub>C (A-B) =  a *\<^sub>C A - a *\<^sub>C B" 
  for A B :: "_::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L _::complex_normed_vector" *)

(* Renamed from applyOp_bot *)
lemma cblinfun_image_bot[simp]: "U *\<^sub>S bot = bot"
  using cblinfun_image_0 by auto

(* Use closure_image_closed_sum instead *)
(* lemma cbounded_minkowski_sum_exchange:
  fixes U::\<open>'a::complex_normed_vector\<Rightarrow>'b::complex_normed_vector\<close> and A B::\<open>'a set\<close>
  assumes a1: \<open>bounded_clinear U\<close> and a2: \<open>closed_csubspace A\<close> and a3: \<open>closed_csubspace B\<close>
  shows "(closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) =
         (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})"
proof- 
  have v1: \<open>U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} = {U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
    by auto
  have \<open>{U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} = {U \<psi> + U \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
    using \<open>bounded_clinear U\<close>
    unfolding bounded_clinear_def
    by (metis (no_types, lifting) complex_vector.linear_add) 
  also have \<open>{U \<psi> + U \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} 
            = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}\<close>
    by blast  
  finally have v2: \<open>{U (\<psi> + \<phi>) |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}
                      = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}\<close>
    by blast
  have v3: \<open>{\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> U ` A \<and> \<phi> \<in> U ` B}
           \<subseteq> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
    by (smt Collect_mono_iff closure_subset subsetD)
      (* > 1s*)      
  have \<open>U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B} \<subseteq>
          {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
    by (simp add: v1 v2 v3)  
  hence y1: \<open>closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
    by (simp add: closure_mono)      
  define S where \<open>S = {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}\<close>
  from a1 have \<open>isCont U x\<close>
    for x
    by (simp add: clinear_continuous_at)
  hence \<open>continuous_on (closure S) U\<close>
    by (simp add: continuous_at_imp_continuous_on)
  hence \<open>U ` (closure S) \<subseteq> closure (U ` S)\<close>
    using Abstract_Topology_2.image_closure_subset
    by (simp add: image_closure_subset closure_subset)
  hence y2: \<open>(U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})
            \<subseteq> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
    unfolding S_def by blast
  have \<open>(U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B}) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
    using y1 y2 by blast    
  hence x1: \<open>(closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})) \<subseteq>
        (closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})\<close>
    by (metis (no_types, lifting) closure_closure closure_mono)
  have \<open>x \<in> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
    if q1: \<open>x \<in> {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)}\<close>
    for x
  proof-
    from q1 obtain \<psi> \<phi> where q2: \<open>x =  \<psi> + \<phi>\<close>  and q3: \<open>\<psi> \<in> closure (U ` A)\<close> 
      and q4: \<open>\<phi> \<in> closure (U ` B)\<close>
      by blast
    from  \<open>\<psi> \<in> closure (U ` A)\<close>
    have \<open>\<exists>psiU. (\<forall> n. psiU n \<in> (U ` A)) \<and> (\<lambda> n. psiU n) \<longlonglongrightarrow> \<psi>\<close>
      using closure_sequential by blast
    then obtain psiU where o1: \<open>\<forall>n. psiU n \<in> (U ` A)\<close> and o2: \<open>(\<lambda> n. psiU n) \<longlonglongrightarrow> \<psi>\<close>
      by blast
    from \<open>\<forall> n. psiU n \<in> (U ` A)\<close>
    have \<open>\<forall> n. \<exists> psi.  psiU n = U psi \<and> psi \<in> A\<close>
      by blast
    hence \<open>\<exists>psi. \<forall> n. psiU n = U (psi n) \<and> psi n \<in> A\<close>
      by metis
    then obtain psi where o3: \<open>\<And>n. psiU n = U (psi n)\<close> and o4: \<open>\<And>n. psi n \<in> A\<close>
      by blast
    have  t1: \<open>(\<lambda> n. U (psi n)) \<longlonglongrightarrow> \<psi>\<close>
      using o2 o3
      by simp
    from  \<open>\<phi> \<in> closure (U ` B)\<close>
    have \<open>\<exists>phiU. (\<forall> n. phiU n \<in> (U ` B)) \<and> (\<lambda> n. phiU n) \<longlonglongrightarrow> \<phi>\<close>
      using closure_sequential by blast
    then obtain phiU where h1: \<open>\<And>n. phiU n \<in> (U ` B)\<close> and h2: \<open>(\<lambda> n. phiU n) \<longlonglongrightarrow> \<phi>\<close>
      by blast    
    have \<open>\<exists>phi.  phiU n = U phi \<and> phi \<in> B\<close>
      for n
      using h1 by blast
    hence \<open>\<exists>phi. \<forall> n. phiU n = U (phi n) \<and> phi n \<in> B\<close>
      by metis
    then obtain phi where h3: \<open>\<And>n. phiU n = U (phi n)\<close> and h4: \<open>\<And>n. phi n \<in> B\<close>
      by blast
    have t2:  \<open>(\<lambda> n. U (phi n)) \<longlonglongrightarrow> \<phi>\<close>
      using h2 h3
      by simp
    have t3: \<open>(\<lambda> n. U (psi n) +  U (phi n) ) \<longlonglongrightarrow> \<psi> + \<phi>\<close>
      by (simp add: tendsto_add t2 t1)
    have \<open>U (psi n) +  U (phi n) =  U ( (psi n) +  (phi n))\<close>
      for n
      using \<open>bounded_clinear U\<close>
      unfolding bounded_clinear_def clinear_def Vector_Spaces.linear_def
        module_hom_def module_hom_axioms_def
      by auto
    hence \<open>(\<lambda> n. U ( (psi n) +  (phi n)) ) \<longlonglongrightarrow> \<psi> + \<phi>\<close>
      using t3 by auto  
    hence \<open>(\<lambda> n. U ( (psi n) +  (phi n)) ) \<longlonglongrightarrow> x\<close>
      by (simp add: q2)      
    hence \<open>x \<in> closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
      by (smt closure_sequential h4 mem_Collect_eq o4 v1)
    thus ?thesis by blast
  qed
  moreover have \<open>closure (U ` {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})
        \<subseteq> closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
    by (simp add: closure_mono closure_subset image_mono)
  ultimately have x2: \<open>(closure  {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> closure (U ` A) \<and> \<phi> \<in> closure (U ` B)})
      \<subseteq> closure (U ` closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> A \<and> \<phi> \<in> B})\<close>
    using closure_mono
    by (metis (no_types, lifting) closure_closure dual_order.trans subsetI)  
  show ?thesis
    using x1 x2 by blast 
qed *)


(* Renamed from cblinfun_image_sup_exchange *)
lemma cblinfun_image_sup[simp]:   
  fixes A B :: \<open>'a::chilbert_space ccsubspace\<close> and U :: "'a \<Rightarrow>\<^sub>C\<^sub>L'b::chilbert_space"
  shows \<open>U *\<^sub>S (sup A B) = sup (U *\<^sub>S A) (U *\<^sub>S B)\<close>  
  apply transfer using bounded_clinear.bounded_linear closure_image_closed_sum by blast 



(* Renamed from scalar_op_clinear_space_assoc *)
lemma scaleC_cblinfun_image[simp]:
  fixes A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b :: chilbert_space\<close>
    and S :: \<open>'a ccsubspace\<close> and \<alpha> :: complex
  shows \<open>(\<alpha> *\<^sub>C A) *\<^sub>S S  = \<alpha> *\<^sub>C (A *\<^sub>S S)\<close>
proof-
  have \<open>closure ( ( ((*\<^sub>C) \<alpha>) \<circ> (cblinfun_apply A) ) ` space_as_set S) =
   ((*\<^sub>C) \<alpha>) ` (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis closure_scaleC image_comp)    
  hence \<open>(closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
   ((*\<^sub>C) \<alpha>) ` (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis (mono_tags, lifting) comp_apply image_cong scaleC_cblinfun.rep_eq)
  hence \<open>Abs_clinear_space (closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
            \<alpha> *\<^sub>C Abs_clinear_space (closure (cblinfun_apply A ` space_as_set S))\<close>
    by (metis space_as_set_inverse cblinfun_image.rep_eq scaleC_ccsubspace.rep_eq)    
  have x1: "Abs_clinear_space (closure ((*\<^sub>V) (\<alpha> *\<^sub>C A) ` space_as_set S)) =
            \<alpha> *\<^sub>C Abs_clinear_space (closure ((*\<^sub>V) A ` space_as_set S))"
    using \<open>Abs_clinear_space (closure (cblinfun_apply (\<alpha> *\<^sub>C A) ` space_as_set S)) =
            \<alpha> *\<^sub>C Abs_clinear_space (closure (cblinfun_apply A ` space_as_set S))\<close>
    by blast
  show ?thesis
    unfolding cblinfun_image_def using x1 by force
qed

lemma cblinfun_image_id[simp]: 
  "id_cblinfun *\<^sub>S \<psi> = \<psi>"
  apply transfer
  by (simp add: closed_csubspace.closed) 

(* Renamed from scalar_op_op *)
lemma cblinfun_compose_scaleC_left[simp]:
  fixes A::"'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
    and B::"'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows \<open>(a *\<^sub>C A) o\<^sub>C\<^sub>L B = a *\<^sub>C (A o\<^sub>C\<^sub>L B)\<close>
  by (simp add: bounded_cbilinear.scaleC_left bounded_cbilinear_cblinfun_compose)

lemma cblinfun_compose_scaleR_left[simp]:
  fixes A::"'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector"
    and B::"'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows \<open>(a *\<^sub>R A) o\<^sub>C\<^sub>L B = a *\<^sub>R (A o\<^sub>C\<^sub>L B)\<close>
  by (simp add: scaleR_scaleC)
  
(* Renamed from op_scalar_op *)
lemma cblinfun_compose_scaleC_right[simp]:
  fixes A::"'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector" 
    and B::"'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows \<open>A o\<^sub>C\<^sub>L (a *\<^sub>C B) = a *\<^sub>C (A o\<^sub>C\<^sub>L B)\<close>
  apply transfer by (auto intro!: ext bounded_clinear.clinear complex_vector.linear_scale)

lemma cblinfun_compose_scaleR_right[simp]:
  fixes A::"'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_normed_vector" 
    and B::"'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b"
  shows \<open>A o\<^sub>C\<^sub>L (a *\<^sub>R B) = a *\<^sub>R (A o\<^sub>C\<^sub>L B)\<close>
  by (simp add: scaleR_scaleC)

(* Renamed from times_id_cblinfun1 *)
lemma cblinfun_compose_id_right[simp]: 
  shows "U o\<^sub>C\<^sub>L id_cblinfun = U"
  apply transfer by auto

(* Renamed from times_id_cblinfun2 *)
lemma cblinfun_compose_id_left[simp]: 
  shows "id_cblinfun o\<^sub>C\<^sub>L U  = U"
  apply transfer by auto

(* Renamed from mult_INF1 *)
lemma cblinfun_image_INF_leq[simp]:
  fixes U :: "'b::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'c::cbanach"
    and V :: "'a \<Rightarrow> 'b ccsubspace" 
  shows \<open>U *\<^sub>S (INF i. V i) \<le> (INF i. U *\<^sub>S (V i))\<close>
  apply transfer
  by (simp add: INT_greatest Inter_lower closure_mono image_mono) 

(* Renamed from mult_inf_distrib' *)
lemma mult_inf_distrib':
  fixes U::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::cbanach\<close> and B C::"'a ccsubspace"
  shows "U *\<^sub>S (inf B C) \<le> inf (U *\<^sub>S B) (U *\<^sub>S C)"
proof -
  define V where \<open>V b = (if b then B else C)\<close> for b
  have \<open>U *\<^sub>S (INF i. V i) \<le> (INF i. U *\<^sub>S (V i))\<close>
    by auto
  then show ?thesis
    unfolding V_def
    by (metis (mono_tags, lifting) INF_UNIV_bool_expand)
qed

(* Use complex_vector.linear_eq_on instead *)
(* lemma equal_span:
  fixes A B :: "'a::cbanach \<Rightarrow> 'b::cbanach"
  assumes \<open>clinear A\<close> and \<open>clinear B\<close> and
    \<open>\<And>x. x \<in> G \<Longrightarrow> A x = B x\<close> and \<open>t \<in> cspan G\<close>
  shows \<open>A t = B t\<close> *)

(* Renamed from cblinfun_image_span *)
lemma cblinfun_eq_on:
  fixes A B :: "'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and \<open>t \<in> closure (cspan G)\<close>
  shows "A *\<^sub>V t = B *\<^sub>V t"
  using assms
  apply transfer
  using bounded_clinear_eq_on by blast

lemma cblinfun_eq_gen_eqI:
  fixes A B :: "'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and \<open>ccspan G = \<top>\<close>
  shows "A = B"
  apply (rule cblinfun_eqI)
  apply (rule cblinfun_eq_on[where G=G])
  using assms apply auto
  by (metis ccspan.rep_eq iso_tuple_UNIV_I top_ccsubspace.rep_eq)


lemma cblinfun_image_eq:
  fixes S :: "'a::cbanach ccsubspace" 
    and A B :: "'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L'b::cbanach"
  assumes "\<And>x. x \<in> G \<Longrightarrow> A *\<^sub>V x = B *\<^sub>V x" and "ccspan G \<ge> S"
  shows "A *\<^sub>S S = B *\<^sub>S S"
proof (use assms in transfer)
  fix G :: "'a set" and A :: "'a \<Rightarrow> 'b" and B :: "'a \<Rightarrow> 'b" and S :: "'a set"
  assume a1: "bounded_clinear A"
  assume a2: "bounded_clinear B"
  assume a3: "\<And>x. x \<in> G \<Longrightarrow> A x = B x"
  assume a4: "S \<subseteq> closure (cspan G)"

  have "A ` closure S = B ` closure S"
    by (smt (verit, best) UnCI a1 a2 a3 a4 bounded_clinear_eq_on closure_Un closure_closure image_cong sup.absorb_iff1)
  then show "closure (A ` S) = closure (B ` S)"
    by (metis Complex_Vector_Spaces0.bounded_clinear.bounded_linear a1 a2 closure_bounded_linear_image_subset_eq)
qed

(* Renamed from apply_left_neutral *)
lemma cblinfun_fixes_range:
  assumes "A o\<^sub>C\<^sub>L B = B" and "\<psi> \<in> space_as_set (B *\<^sub>S top)"
  shows "A *\<^sub>V \<psi> = \<psi>" 
proof-
  define rangeB rangeB' where "rangeB = space_as_set (B *\<^sub>S top)" 
    and "rangeB' = range (cblinfun_apply B)"
  from assms have "\<psi> \<in> closure rangeB'"
    by (simp add: cblinfun_image.rep_eq rangeB'_def top_ccsubspace.rep_eq)

  then obtain \<psi>i where \<psi>i_lim: "\<psi>i \<longlonglongrightarrow> \<psi>" and \<psi>i_B: "\<psi>i i \<in> rangeB'" for i
    using closure_sequential by blast
  have A_invariant: "A *\<^sub>V \<psi>i i = \<psi>i i" 
    for i
  proof-
    from \<psi>i_B obtain \<phi> where \<phi>: "\<psi>i i = B *\<^sub>V \<phi>"
      using rangeB'_def by blast      
    hence "A *\<^sub>V \<psi>i i = (A o\<^sub>C\<^sub>L B) *\<^sub>V \<phi>"
      by (simp add: cblinfun_compose.rep_eq)
    also have "\<dots> = B *\<^sub>V \<phi>"
      by (simp add: assms)
    also have "\<dots> = \<psi>i i"
      by (simp add: \<phi>)
    finally show ?thesis.
  qed
  from \<psi>i_lim have "(\<lambda>i. A *\<^sub>V (\<psi>i i)) \<longlonglongrightarrow> A *\<^sub>V \<psi>"
    by (rule isCont_tendsto_compose[rotated], simp)
  with A_invariant have "(\<lambda>i. \<psi>i i) \<longlonglongrightarrow> A *\<^sub>V \<psi>"
    by auto
  with \<psi>i_lim show "A *\<^sub>V \<psi> = \<psi>"
    using LIMSEQ_unique by blast
qed

lemma cblinfun_compose_add_left: \<open>(a + b) o\<^sub>C\<^sub>L c = (a o\<^sub>C\<^sub>L c) + (b o\<^sub>C\<^sub>L c)\<close>
  by (simp add: bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose)

lemma cblinfun_compose_add_right: \<open>a o\<^sub>C\<^sub>L (b + c) = (a o\<^sub>C\<^sub>L b) + (a o\<^sub>C\<^sub>L c)\<close>
  by (simp add: bounded_cbilinear.add_right bounded_cbilinear_cblinfun_compose)

subsection \<open>Adjoint\<close>

lift_definition
  adj :: "'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner \<Rightarrow> 'b \<Rightarrow>\<^sub>C\<^sub>L 'a" ("_*" [99] 100)
  is cadjoint by (fact cadjoint_bounded_clinear)

(* Use id_cblinfun instead *)
(* abbreviation (input) "idOp == id_cblinfun" *)

lemma id_cblinfun_adjoint[simp]: "id_cblinfun* = id_cblinfun"
  apply transfer using cadjoint_id
  by (metis eq_id_iff)

(* Renamed from adjoint_twice *)
lemma double_adj[simp]: "(A*)* = A" 
  (* for U :: "'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space" *)
  apply transfer using double_cadjoint by blast

(* Renamed from times_adjoint *)
lemma adj_cblinfun_compose[simp]:
  fixes B::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
    and A::\<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner\<close> 
  shows "(A o\<^sub>C\<^sub>L B)* =  (B*) o\<^sub>C\<^sub>L (A*)"
proof transfer
  fix  A :: \<open>'b \<Rightarrow> 'c\<close> and B :: \<open>'a \<Rightarrow> 'b\<close>
  assume \<open>bounded_clinear A\<close> and \<open>bounded_clinear B\<close>
  hence \<open>bounded_clinear (A \<circ> B)\<close>
    by (simp add: comp_bounded_clinear)
  have \<open>\<langle> (A \<circ> B) u, v \<rangle> = \<langle> u, (B\<^sup>\<dagger> \<circ> A\<^sup>\<dagger>) v \<rangle>\<close>
    for u v
    by (metis (no_types, lifting) cadjoint_univ_prop \<open>bounded_clinear A\<close> \<open>bounded_clinear B\<close> cinner_commute' comp_def)    
  thus \<open>(A \<circ> B)\<^sup>\<dagger> = B\<^sup>\<dagger> \<circ> A\<^sup>\<dagger>\<close>
    using \<open>bounded_clinear (A \<circ> B)\<close>
    by (metis cadjoint_eqI cinner_commute')
qed


lemma scaleC_adj[simp]: "(a *\<^sub>C A)* = (cnj a) *\<^sub>C (A*)" 
  apply transfer
  by (simp add: Complex_Vector_Spaces0.bounded_clinear.bounded_linear bounded_clinear_def complex_vector.linear_scale scaleC_cadjoint)

lemma scaleR_adj[simp]: "(a *\<^sub>R A)* = a *\<^sub>R (A*)" 
  by (simp add: scaleR_scaleC)

lemma adj_plus:
  (* fixes A B :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close> *)
  shows \<open>(A + B)* = (A*) + (B*)\<close>
proof transfer
  fix A B::\<open>'b \<Rightarrow> 'a\<close>
  assume a1: \<open>bounded_clinear A\<close> and a2: \<open>bounded_clinear B\<close>
  define F where \<open>F = (\<lambda>x. (A\<^sup>\<dagger>) x + (B\<^sup>\<dagger>) x)\<close>
  define G where \<open>G = (\<lambda>x. A x + B x)\<close>
  have \<open>bounded_clinear G\<close>
    unfolding G_def
    by (simp add: a1 a2 bounded_clinear_add)
  moreover have \<open>\<langle>F u,  v\<rangle> = \<langle>u, G v\<rangle>\<close> for u v
    unfolding F_def G_def
    using cadjoint_univ_prop a1 a2 cinner_add_left
    by (simp add: cadjoint_univ_prop cinner_add_left cinner_add_right) 
  ultimately have \<open>F = G\<^sup>\<dagger> \<close>
    using cadjoint_eqI by blast
  thus \<open>(\<lambda>x. A x + B x)\<^sup>\<dagger> = (\<lambda>x. (A\<^sup>\<dagger>) x + (B\<^sup>\<dagger>) x)\<close>
    unfolding F_def G_def
    by auto
qed

(* lemma Adj_cblinfun_uminus[simp]:
  \<open>(- A)* = - (A* )\<close>
  by (metis (no_types, lifting) Adj_cblinfun_plus  add_cancel_left_right diff_0 ordered_field_class.sign_simps(9))

lemma Adj_cblinfun_minus[simp]:
  \<open>(A - B)* = (A* ) - (B* )\<close>
  by (metis Adj_cblinfun_plus add_right_cancel diff_add_cancel)

lemma Adj_cblinfun_zero[simp]:
  \<open>0* = 0\<close>
  by (metis Adj_cblinfun_plus add_cancel_right_right) *)


lemma cinner_sup_norm_cblinfun: 
  fixes A :: \<open>'a::{complex_normed_vector,not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner\<close>
  shows \<open>norm A = (SUP (\<psi>,\<phi>). cmod (cinner \<psi> (A *\<^sub>V \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
  apply transfer
  apply (rule cinner_sup_onorm)
  by (simp add: bounded_clinear.bounded_linear)


(* Renamed from adjoint_I *)
lemma cinner_adj_left:
  fixes G :: "'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::complex_inner"
  shows \<open>\<langle>G* *\<^sub>V x, y\<rangle> = \<langle>x, G *\<^sub>V y\<rangle>\<close>
  apply transfer using cadjoint_univ_prop by blast

(* Renamed from adjoint_I' *)
lemma cinner_adj_right:
  fixes G :: "'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::complex_inner"
  shows \<open>\<langle>x, G* *\<^sub>V y\<rangle> = \<langle>G *\<^sub>V x, y\<rangle>\<close> 
  apply transfer using cadjoint_univ_prop' by blast

lemma adj_0[simp]: \<open>0* = 0\<close>
  by (metis add_cancel_right_left adj_plus)

lemma norm_adj[simp]: \<open>norm (A*) = norm A\<close> 
  for A :: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'c::complex_inner\<close>
proof (cases \<open>(\<exists>x y :: 'b. x \<noteq> y) \<and> (\<exists>x y :: 'c. x \<noteq> y)\<close>)
  case True
  then have c1: \<open>class.not_singleton TYPE('b)\<close>
    apply intro_classes by simp
  from True have c2: \<open>class.not_singleton TYPE('c)\<close>
    apply intro_classes by simp
  have normA: \<open>norm A = (SUP (\<psi>, \<phi>). cmod (\<psi> \<bullet>\<^sub>C (A *\<^sub>V \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
    apply (rule cinner_sup_norm_cblinfun[internalize_sort \<open>'a::{complex_normed_vector,not_singleton}\<close>])
     apply (rule complex_normed_vector_axioms)
    by (rule c1)
  have normAadj: \<open>norm (A*) = (SUP (\<psi>, \<phi>). cmod (\<psi> \<bullet>\<^sub>C (A* *\<^sub>V \<phi>)) / (norm \<psi> * norm \<phi>))\<close>
    apply (rule cinner_sup_norm_cblinfun[internalize_sort \<open>'a::{complex_normed_vector,not_singleton}\<close>])
     apply (rule complex_normed_vector_axioms)
    by (rule c2)

  have \<open>norm (A*) = (SUP (\<psi>, \<phi>). cmod (\<phi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) / (norm \<psi> * norm \<phi>))\<close>
    unfolding normAadj
    apply (subst cinner_adj_right)
    apply (subst cinner_commute)
    apply (subst complex_mod_cnj)
    by rule
  also have \<open>\<dots> = Sup ((\<lambda>(\<psi>, \<phi>). cmod (\<phi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) / (norm \<psi> * norm \<phi>)) ` prod.swap ` UNIV)\<close>
    by auto
  also have \<open>\<dots> = (SUP (\<phi>, \<psi>). cmod (\<phi> \<bullet>\<^sub>C (A *\<^sub>V \<psi>)) / (norm \<psi> * norm \<phi>))\<close>
    apply (subst image_image)
    by auto
  also have \<open>\<dots> = norm A\<close>
    unfolding normA
    by (simp add: mult.commute)
  finally show ?thesis
    by -
next
  case False
  then consider (b) \<open>\<And>x::'b. x = 0\<close> | (c) \<open>\<And>x::'c. x = 0\<close>
    by auto
  then have \<open>A = 0\<close>
    apply (cases; transfer)
     apply (metis (full_types) bounded_clinear_def complex_vector.linear_0) 
    by auto
  then show \<open>norm (A*) = norm A\<close>
    by simp
qed


lemma antilinear_adj[simp]: \<open>antilinear adj\<close>
  apply (rule antilinearI) by (auto simp add: adj_plus)

lemma bounded_antilinear_adj[bounded_antilinear, simp]: \<open>bounded_antilinear adj\<close>
  by (auto intro!: antilinearI exI[of _ 1] simp: bounded_antilinear_def bounded_antilinear_axioms_def adj_plus)

(* Renamed from adjoint_D *)
lemma adjoint_eqI:
  fixes G:: \<open>'b::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a::chilbert_space\<close>
    and F:: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  assumes \<open>\<And>x y. \<langle>(cblinfun_apply F) x, y\<rangle> = \<langle>x, (cblinfun_apply G) y\<rangle>\<close>
  shows \<open>F = G*\<close>
  using assms apply transfer using cadjoint_eqI by auto


lemma cinner_real_hermiteanI: 
  \<comment> \<open>Prop. II.2.12 in @{cite conway2013course}\<close>
  assumes \<open>\<And>\<psi>. cinner \<psi> (A *\<^sub>V \<psi>) \<in> \<real>\<close>
  shows \<open>A = A*\<close>
proof -
  { fix g h :: 'a
    {
      fix \<alpha> :: complex
      have \<open>cinner h (A h) + cnj \<alpha> *\<^sub>C cinner g (A h) + \<alpha> *\<^sub>C cinner h (A g) + (abs \<alpha>)\<^sup>2 * cinner g (A g)
        = cinner (h + \<alpha> *\<^sub>C g) (A *\<^sub>V (h + \<alpha> *\<^sub>C g))\<close> (is \<open>?sum4 = _\<close>)
        apply (auto simp: cinner_add_right cinner_add_left cblinfun.add_right cblinfun.scaleC_right ring_class.ring_distribs)
        by (metis cnj_x_x mult.commute)
      also have \<open>\<dots> \<in> \<real>\<close>
        using assms by auto
      finally have \<open>?sum4 = cnj ?sum4\<close>
        using Reals_cnj_iff by fastforce
      then have \<open>cnj \<alpha> *\<^sub>C cinner g (A h) + \<alpha> *\<^sub>C cinner h (A g)
            = \<alpha> *\<^sub>C cinner (A h) g + cnj \<alpha> *\<^sub>C cinner (A g) h\<close>
        using Reals_cnj_iff abs_complex_real assms by force
      also have \<open>\<dots> = \<alpha> *\<^sub>C cinner h (A* *\<^sub>V g) + cnj \<alpha> *\<^sub>C cinner g (A* *\<^sub>V h)\<close>
        by (simp add: cinner_adj_right)
      finally have \<open>cnj \<alpha> *\<^sub>C cinner g (A h) + \<alpha> *\<^sub>C cinner h (A g) = \<alpha> *\<^sub>C cinner h (A* *\<^sub>V g) + cnj \<alpha> *\<^sub>C cinner g (A* *\<^sub>V h)\<close>
        by -
    }
    from this[where \<alpha>2=1] this[where \<alpha>2=\<i>]
    have 1: \<open>cinner g (A h) + cinner h (A g) = cinner h (A* *\<^sub>V g) + cinner g (A* *\<^sub>V h)\<close>
      and i: \<open>- \<i> * cinner g (A h) + \<i> *\<^sub>C cinner h (A g) =  \<i> *\<^sub>C cinner h (A* *\<^sub>V g) - \<i> *\<^sub>C cinner g (A* *\<^sub>V h)\<close>
      by auto
    from arg_cong2[OF 1 arg_cong[OF i, where f=\<open>(*) (-\<i>)\<close>], where f=plus]
    have \<open>cinner h (A g) = cinner h (A* *\<^sub>V g)\<close>
      by (auto simp: ring_class.ring_distribs)
  }
  then show "A = A*"
    by (simp add: adjoint_eqI cinner_adj_right)
qed

subsection \<open>Unitary\<close>


definition isometry::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner \<Rightarrow> bool\<close> where
  \<open>isometry U \<longleftrightarrow> U* o\<^sub>C\<^sub>L U = id_cblinfun\<close>

definition unitary::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner \<Rightarrow> bool\<close> where
  \<open>unitary U \<longleftrightarrow> (U* o\<^sub>C\<^sub>L U  = id_cblinfun) \<and> (U o\<^sub>C\<^sub>L U* = id_cblinfun)\<close>

(* Renamed from unitary_def' *)
lemma unitary_twosided_isometry: "unitary U \<longleftrightarrow> isometry U \<and> isometry (U*)"
  unfolding unitary_def isometry_def by simp

(* Renamed from adjUU *)
lemma isometryD[simp]: "isometry U \<Longrightarrow> U* o\<^sub>C\<^sub>L U = id_cblinfun" 
  unfolding isometry_def by simp

(* Not [simp] because isometryD + unitary_isometry already have the same effect *)
lemma unitaryD1: "unitary U \<Longrightarrow> U* o\<^sub>C\<^sub>L U = id_cblinfun" 
  unfolding unitary_def by simp

(* Renamed from UadjU *)
lemma unitaryD2[simp]: "unitary U \<Longrightarrow> U o\<^sub>C\<^sub>L U* = id_cblinfun"
  unfolding unitary_def by simp

lemma unitary_isometry[simp]: "unitary U \<Longrightarrow> isometry U"
  unfolding unitary_def isometry_def by simp

(* Renamed from unitary_adjoint *)
lemma unitary_adj[simp]: "unitary (U*) = unitary U" 
  unfolding unitary_def by auto

(* Renamed from isometry_times *)
lemma isometry_cblinfun_compose[simp]: 
  assumes "isometry A" and "isometry B"  
  shows "isometry (A o\<^sub>C\<^sub>L B)"
proof-
  have "B* o\<^sub>C\<^sub>L A* o\<^sub>C\<^sub>L (A o\<^sub>C\<^sub>L B) = id_cblinfun" if "A* o\<^sub>C\<^sub>L A = id_cblinfun" and "B* o\<^sub>C\<^sub>L B = id_cblinfun"
    using that
    by (smt (verit, del_insts) adjoint_eqI cblinfun_apply_cblinfun_compose cblinfun_id_cblinfun_apply)
  thus ?thesis 
    using assms unfolding isometry_def by simp
qed

(* Renamed from unitary_times *)
lemma unitary_cblinfun_compose[simp]: "unitary (A o\<^sub>C\<^sub>L B)"
  if "unitary A" and "unitary B"
  using that
  by (smt (z3) adj_cblinfun_compose cblinfun_compose_assoc cblinfun_compose_id_right double_adj isometryD isometry_cblinfun_compose unitary_def unitary_isometry) 

lemma unitary_surj: 
  assumes "unitary U"
  shows "surj (cblinfun_apply U)"
  apply (rule surjI[where f=\<open>cblinfun_apply (U*)\<close>])
  using assms unfolding unitary_def apply transfer
  using comp_eq_dest_lhs by force

(* Renamed from unitary_image *)
lemma unitary_range[simp]: 
  assumes "unitary U"
  shows "U *\<^sub>S top = top"
  using assms unfolding unitary_def apply transfer
  by (metis closure_UNIV comp_apply surj_def) 

lemma unitary_id[simp]: "unitary id_cblinfun"
  by (simp add: unitary_def) 

lemma orthogonal_on_basis_is_isometry:
  assumes spanB: \<open>ccspan B = \<top>\<close>
  assumes orthoU: \<open>\<And>b c. b\<in>B \<Longrightarrow> c\<in>B \<Longrightarrow> cinner (U *\<^sub>V b) (U *\<^sub>V c) = cinner b c\<close>
  shows \<open>isometry U\<close>
proof -
  have [simp]: \<open>b \<in> closure (cspan B)\<close> for b
    using spanB apply transfer by simp
  have *: \<open>cinner (U* *\<^sub>V U *\<^sub>V \<psi>) \<phi> = cinner \<psi> \<phi>\<close> if \<open>\<psi>\<in>B\<close> and \<open>\<phi>\<in>B\<close> for \<psi> \<phi>
    by (simp add: cinner_adj_left orthoU that(1) that(2))
  have *: \<open>cinner (U* *\<^sub>V U *\<^sub>V \<psi>) \<phi> = cinner \<psi> \<phi>\<close> if \<open>\<psi>\<in>B\<close> for \<psi> \<phi>
    apply (rule bounded_clinear_eq_on[where t=\<phi> and G=B])
    using bounded_clinear_cinner_right *[OF that]
    by auto
  have \<open>U* *\<^sub>V U *\<^sub>V \<phi> = \<phi>\<close> if \<open>\<phi>\<in>B\<close> for \<phi>
    apply (rule cinner_extensionality)
    apply (subst cinner_eq_flip)
    by (simp add: * that)
  then have \<open>U* o\<^sub>C\<^sub>L U = id_cblinfun\<close>
    by (metis cblinfun_apply_cblinfun_compose cblinfun_eq_gen_eqI cblinfun_id_cblinfun_apply spanB)
  then show \<open>isometry U\<close>
    using isometry_def by blast
qed

subsection \<open>Projectors\<close>

lift_definition Proj :: "('a::chilbert_space) ccsubspace \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L'a"
  is \<open>projection\<close>
  by (rule projection_bounded_clinear)

(* Renamed from imageOp_Proj *)
lemma Proj_range[simp]: "Proj S *\<^sub>S top = S"  
proof transfer
  fix S :: \<open>'a set\<close> assume \<open>closed_csubspace S\<close>
  then have "closure (range (projection S)) \<subseteq> S"
    by (metis closed_csubspace.closed closed_csubspace.subspace closure_closed complex_vector.subspace_0 csubspace_is_convex dual_order.eq_iff insert_absorb insert_not_empty projection_image)
  moreover have "S \<subseteq> closure (range (projection S))"
    using \<open>closed_csubspace S\<close>
    by (metis closed_csubspace_def closure_subset csubspace_is_convex equals0D projection_image subset_iff)
  ultimately show \<open>closure (range (projection S)) = S\<close> 
    by auto
qed

(* Renamed from adj_Proj[symmetric] *)
lemma adj_Proj: \<open>(Proj M)* = Proj M\<close>
  apply transfer by (simp add: projection_cadjoint)

(* Renamed from Proj_D2 *)
lemma Proj_idempotent[simp]: \<open>Proj M o\<^sub>C\<^sub>L Proj M = Proj M\<close>
proof -
  have u1: \<open>(cblinfun_apply (Proj M)) = projection (space_as_set M)\<close>
    apply transfer
    by blast
  have \<open>closed_csubspace (space_as_set M)\<close>
    using space_as_set by auto
  hence u2: \<open>(projection (space_as_set M))\<circ>(projection (space_as_set M))
                = (projection (space_as_set M))\<close>    
    using projection_idem by fastforce
  have \<open>(cblinfun_apply (Proj M)) \<circ> (cblinfun_apply (Proj M)) = cblinfun_apply (Proj M)\<close>
    using u1 u2
    by simp    
  hence \<open>cblinfun_apply ((Proj M) o\<^sub>C\<^sub>L (Proj M)) = cblinfun_apply (Proj M)\<close>
    by (simp add: cblinfun_compose.rep_eq)
  thus ?thesis using cblinfun_apply_inject
    by auto 
qed

(* Renamed from isProjector *)
lift_definition is_Proj::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> bool\<close> is
  \<open>\<lambda>P. \<exists>M. closed_csubspace M \<and> is_projection_on P M\<close> .

(* Renamed from Proj_I[symmetric] *)
lemma Proj_on_own_range':
  fixes P :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'a\<close>
  assumes \<open>P o\<^sub>C\<^sub>L P = P\<close> and \<open>P = P*\<close>
  shows \<open>Proj (P *\<^sub>S top) = P\<close>
proof-
  define M where "M = P *\<^sub>S top"
  have v3: "x \<in> (\<lambda>x. x - P *\<^sub>V x) -` {0}"
    if "x \<in> range (cblinfun_apply P)"
    for x :: 'a
  proof-
    have v3_1: \<open>cblinfun_apply P \<circ> cblinfun_apply P = cblinfun_apply P\<close>
      by (metis \<open>P o\<^sub>C\<^sub>L P = P\<close> cblinfun_compose.rep_eq)
    have \<open>\<exists>t. P *\<^sub>V t = x\<close>
      using that by blast
    then obtain t where t_def: \<open>P *\<^sub>V t = x\<close>
      by blast 
    hence \<open>x - P *\<^sub>V x = x - P *\<^sub>V (P *\<^sub>V t)\<close>
      by simp
    also have \<open>\<dots> = x - (P *\<^sub>V t)\<close>
      using v3_1      
      by (metis comp_apply) 
    also have \<open>\<dots> = 0\<close>
      by (simp add: t_def)
    finally have \<open>x - P *\<^sub>V x = 0\<close>
      by blast
    thus ?thesis
      by simp 
  qed

  have v1: "range (cblinfun_apply P) \<subseteq> (\<lambda>x. x - cblinfun_apply P x) -` {0}"
    using v3
    by blast

  have "x \<in> range (cblinfun_apply P)"
    if "x \<in> (\<lambda>x. x - P *\<^sub>V x) -` {0}"
    for x :: 'a
  proof-
    have x1:\<open>x - P *\<^sub>V x = 0\<close>
      using that by blast
    have \<open>x = P *\<^sub>V x\<close>
      by (simp add: x1 eq_iff_diff_eq_0)
    thus ?thesis
      by blast 
  qed
  hence v2: "(\<lambda>x. x - cblinfun_apply P x) -` {0} \<subseteq> range (cblinfun_apply P)"
    by blast
  have i1: \<open>range (cblinfun_apply P) = (\<lambda> x. x - cblinfun_apply P x) -` {0}\<close>
    using v1 v2
    by (simp add: v1 dual_order.antisym) 
  have p1: \<open>closed {(0::'a)}\<close>
    by simp        
  have p2: \<open>continuous (at x) (\<lambda> x. x - P *\<^sub>V x)\<close>
    for x
  proof-
    have \<open>cblinfun_apply (id_cblinfun - P) = (\<lambda> x. x - P *\<^sub>V x)\<close>
      by (simp add: id_cblinfun.rep_eq minus_cblinfun.rep_eq)                 
    hence \<open>bounded_clinear (cblinfun_apply (id_cblinfun - P))\<close>
      using cblinfun_apply
      by blast 
    hence \<open>continuous (at x) (cblinfun_apply (id_cblinfun - P))\<close>
      by (simp add: clinear_continuous_at)
    thus ?thesis
      using \<open>cblinfun_apply (id_cblinfun - P) = (\<lambda> x. x - P *\<^sub>V x)\<close>
      by simp
  qed

  have i2: \<open>closed ( (\<lambda> x. x - P *\<^sub>V x) -` {0} )\<close>
    using p1 p2
    by (rule Abstract_Topology.continuous_closed_vimage)

  have \<open>closed (range (cblinfun_apply P))\<close>
    using i1 i2
    by simp
  have u2: \<open>cblinfun_apply P x \<in> space_as_set M\<close>
    for x
    by (simp add: M_def \<open>closed (range ((*\<^sub>V) P))\<close> cblinfun_image.rep_eq top_ccsubspace.rep_eq)

  have xy: \<open>\<langle> x - P *\<^sub>V x, y \<rangle> = 0\<close>
    if y1: \<open>y \<in> space_as_set M\<close>
    for x y
  proof-
    have \<open>\<exists>t. y = P *\<^sub>V t\<close>
      using y1
      by (simp add:  M_def \<open>closed (range ((*\<^sub>V) P))\<close> cblinfun_image.rep_eq image_iff 
          top_ccsubspace.rep_eq)
    then obtain t where t_def: \<open>y = P *\<^sub>V t\<close>
      by blast
    have \<open>\<langle> x - P *\<^sub>V x, y \<rangle> = \<langle> x - P *\<^sub>V x, P *\<^sub>V t \<rangle>\<close>
      by (simp add: t_def)
    also have \<open>\<dots> = \<langle> P *\<^sub>V (x - P *\<^sub>V x), t \<rangle>\<close>
      by (metis \<open>P = P*\<close> cinner_adj_left)
    also have \<open>\<dots> = \<langle> P *\<^sub>V x - P *\<^sub>V (P *\<^sub>V x), t \<rangle>\<close>
      by (simp add: cblinfun.diff_right)
    also have \<open>\<dots> = \<langle> P *\<^sub>V x - P *\<^sub>V x, t \<rangle>\<close>
      by (metis assms(1) comp_apply cblinfun_compose.rep_eq)    
    also have \<open>\<dots> = \<langle> 0, t \<rangle>\<close>
      by simp
    also have \<open>\<dots> = 0\<close>
      by simp
    finally show ?thesis by blast
  qed
  hence u1: \<open>x - P *\<^sub>V x \<in> orthogonal_complement (space_as_set M)\<close> 
    for x
    by (simp add: orthogonal_complementI) 
  have "closed_csubspace (space_as_set M)"
    using space_as_set by auto
  hence f1: "(Proj M) *\<^sub>V a = P *\<^sub>V a" for a
    by (simp add: Proj.rep_eq projection_eqI u1 u2)
  have "(+) ((P - Proj M) *\<^sub>V a) = id" for a
    using f1
    by (auto intro!: ext simp add: minus_cblinfun.rep_eq) 
  hence "b - b = cblinfun_apply (P - Proj M) a"
    for a b
    by (metis (no_types) add_diff_cancel_right' id_apply)
  hence "cblinfun_apply (id_cblinfun - (P - Proj M)) a = a"
    for a
    by (simp add: id_cblinfun.rep_eq minus_cblinfun.rep_eq)      
  thus ?thesis
    using u1 u2 cblinfun_apply_inject diff_diff_eq2 diff_eq_diff_eq eq_id_iff id_cblinfun.rep_eq
    by (metis (no_types, hide_lams) M_def)
qed

lemma Proj_range_closed:
  assumes "is_Proj P"
  shows "closed (range (cblinfun_apply P))"
  using assms apply transfer      
  using closed_csubspace.closed is_projection_on_image by blast

lemma Proj_is_Proj[simp]:
  fixes M::\<open>'a::chilbert_space ccsubspace\<close>
  shows \<open>is_Proj (Proj M)\<close>
proof-
  have u1: "closed_csubspace (space_as_set M)"
    using space_as_set by blast
  have v1: "h - Proj M *\<^sub>V h
         \<in> orthogonal_complement (space_as_set M)" for h
    by (simp add: Proj.rep_eq orthogonal_complementI projection_orthogonal u1)
  have v2: "Proj M *\<^sub>V h \<in> space_as_set M" for h
    by (metis Proj.rep_eq mem_Collect_eq orthog_proj_exists projection_eqI space_as_set)
  have u2: "is_projection_on ((*\<^sub>V) (Proj M)) (space_as_set M)"
    unfolding is_projection_on_def
    by (simp add: smallest_dist_is_ortho u1 v1 v2)
  show ?thesis
    using u1 u2 is_Proj.rep_eq by blast 
qed

lemma is_Proj_algebraic: 
  fixes P::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  shows \<open>is_Proj P \<longleftrightarrow> P o\<^sub>C\<^sub>L P = P \<and> P = P*\<close>
proof
  have "P o\<^sub>C\<^sub>L P = P"
    if "is_Proj P"
    using that apply transfer
    using is_projection_on_idem
    by fastforce
  moreover have "P = P*"
    if "is_Proj P"
    using that apply transfer
    by (metis is_projection_on_cadjoint)
  ultimately show "P o\<^sub>C\<^sub>L P = P \<and> P = P*"
    if "is_Proj P"
    using that
    by blast
  show "is_Proj P"
    if "P o\<^sub>C\<^sub>L P = P \<and> P = P*"
    using that Proj_on_own_range' Proj_is_Proj by metis
qed

lemma Proj_on_own_range:
  fixes P :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'a\<close>
  assumes \<open>is_Proj P\<close>
  shows \<open>Proj (P *\<^sub>S top) = P\<close>
  using Proj_on_own_range' assms is_Proj_algebraic by blast

(* Renamed from Proj_leq *)
lemma Proj_image_leq: "(Proj S) *\<^sub>S A \<le> S"
  by (metis Proj_range inf_top_left le_inf_iff mult_inf_distrib')

(* Renamed from Proj_times *)
(* TODO use sandwich, rename *)
lemma Proj_congruence:
  fixes A::"'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space"
  assumes "isometry A"
  shows "A o\<^sub>C\<^sub>L Proj S o\<^sub>C\<^sub>L (A*) = Proj (A *\<^sub>S S)" 
proof-
  define P where \<open>P = A o\<^sub>C\<^sub>L Proj S o\<^sub>C\<^sub>L (A*)\<close>
  have \<open>P o\<^sub>C\<^sub>L P = P\<close>
    using assms
    unfolding P_def isometry_def
    by (metis (no_types, lifting) Proj_idempotent cblinfun_assoc_left(1) cblinfun_compose_id_left)
  moreover have \<open>P = P*\<close>
    unfolding P_def  
    by (metis adj_Proj adj_cblinfun_compose cblinfun_assoc_left(1) double_adj)
  ultimately have 
    \<open>\<exists>M. P = Proj M \<and> space_as_set M = range (cblinfun_apply (A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*)))\<close>
    using P_def Proj_on_own_range'
    by (metis Proj_is_Proj Proj_range_closed cblinfun_image.rep_eq closure_closed top_ccsubspace.rep_eq)
  then obtain M where \<open>P = Proj M\<close>
    and \<open>space_as_set M = range (cblinfun_apply (A o\<^sub>C\<^sub>L (Proj S) o\<^sub>C\<^sub>L (A*)))\<close>
    by blast

  have f1: "A o\<^sub>C\<^sub>L Proj S = P o\<^sub>C\<^sub>L A"  
    by (simp add: P_def assms cblinfun_compose_assoc)
  hence "P o\<^sub>C\<^sub>L A o\<^sub>C\<^sub>L A* = P"
    using P_def by presburger
  hence "(P o\<^sub>C\<^sub>L A) *\<^sub>S (c \<squnion> A* *\<^sub>S d) = P *\<^sub>S (A *\<^sub>S c \<squnion> d)"
    for c d
  
    by (simp add: cblinfun_assoc_left(2))
  hence "P *\<^sub>S (A *\<^sub>S \<top> \<squnion> c) = (P o\<^sub>C\<^sub>L A) *\<^sub>S \<top>"
    for c
    by (metis sup_top_left)
  hence \<open>M = A *\<^sub>S S\<close>
    using f1
    by (metis \<open>P = Proj M\<close> cblinfun_assoc_left(2) Proj_range sup_top_right)
  thus ?thesis
    using \<open>P = Proj M\<close>
    unfolding P_def
    by blast
qed

lemma Proj_orthog_ccspan_union:
  assumes "\<And>x y. x \<in> X \<Longrightarrow> y \<in> Y \<Longrightarrow> is_orthogonal x y"
  shows \<open>Proj (ccspan (X \<union> Y)) = Proj (ccspan X) + Proj (ccspan Y)\<close>
proof -
  have \<open>x \<in> cspan X \<Longrightarrow> y \<in> cspan Y \<Longrightarrow> is_orthogonal x y\<close> for x y
    apply (rule is_orthogonal_closure_cspan[where X=X and Y=Y])
    using closure_subset assms by auto
  then have \<open>x \<in> closure (cspan X) \<Longrightarrow> y \<in> closure (cspan Y) \<Longrightarrow> is_orthogonal x y\<close> for x y
    by (metis orthogonal_complementI orthogonal_complement_of_closure orthogonal_complement_orthoI')
  then show ?thesis
    apply (transfer fixing: X Y)
    apply (subst projection_plus[symmetric])
    by auto
qed

abbreviation proj :: "'a::chilbert_space \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'a" where "proj \<psi> \<equiv> Proj (ccspan {\<psi>})"

lemma proj_0[simp]: \<open>proj 0 = 0\<close>
  apply transfer by auto

lemma surj_isometry_is_unitary:
  fixes U :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
  assumes \<open>isometry U\<close>
  assumes \<open>U *\<^sub>S \<top> = \<top>\<close>
  shows \<open>unitary U\<close>
  by (metis Proj_congruence Proj_on_own_range' assms(1) assms(2) cblinfun_compose_id_right isometry_def unitary_def unitary_id unitary_range)

(* Use ccspan_singleton_scaleC instead *)
(* lemma projection_scalar_mult[simp]: 
  "a \<noteq> 0 \<Longrightarrow> proj (a *\<^sub>C \<psi>) = proj \<psi>" 
  for a::complex and \<psi>::"'a::chilbert_space" *)

(* Renamed from move_plus *)
lemma ccsubspace_supI_via_Proj:
  fixes A B C::"'a::chilbert_space ccsubspace"
  assumes a1: \<open>Proj (- C) *\<^sub>S A \<le> B\<close>
  shows  "A \<le> sup B C"
proof-
  have x2: \<open>x \<in> space_as_set B\<close>
    if "x \<in>  closure ( (projection (orthogonal_complement (space_as_set C))) ` space_as_set A)" for x
    using that
    by (metis Proj.rep_eq cblinfun_image.rep_eq assms less_eq_ccsubspace.rep_eq subsetD 
        uminus_ccsubspace.rep_eq)
  have q1: \<open>x \<in> closure {\<psi> + \<phi> |\<psi> \<phi>. \<psi> \<in> space_as_set B \<and> \<phi> \<in> space_as_set C}\<close>
    if \<open>x \<in> space_as_set A\<close>
    for x
  proof-
    have p1: \<open>closed_csubspace (space_as_set C)\<close>
      using space_as_set by auto
    hence \<open>x = (projection (space_as_set C)) x
       + (projection (orthogonal_complement (space_as_set C))) x\<close>
      by simp
    hence \<open>x = (projection (orthogonal_complement (space_as_set C))) x
              + (projection (space_as_set C)) x\<close>
      by (metis ordered_field_class.sign_simps(2))
    moreover have \<open>(projection (orthogonal_complement (space_as_set C))) x \<in> space_as_set B\<close>
      using x2
      by (meson closure_subset image_subset_iff that)
    moreover have \<open>(projection (space_as_set C)) x \<in> space_as_set C\<close>
      by (metis mem_Collect_eq orthog_proj_exists projection_eqI space_as_set)
    ultimately show ?thesis
      using closure_subset by fastforce 
  qed
  have x1: \<open>x \<in> (space_as_set B +\<^sub>M space_as_set C)\<close>
    if "x \<in> space_as_set A" for x
  proof -
    have f1: "x \<in> closure {a + b |a b. a \<in> space_as_set B \<and> b \<in> space_as_set C}"
      by (simp add: q1 that)
    have "{a + b |a b. a \<in> space_as_set B \<and> b \<in> space_as_set C} = {a. \<exists>p. p \<in> space_as_set B 
      \<and> (\<exists>q. q \<in> space_as_set C \<and> a = p + q)}"
      by blast
    hence "x \<in> closure {a. \<exists>b\<in>space_as_set B. \<exists>c\<in>space_as_set C. a = b + c}"
      using f1 by (simp add: Bex_def_raw)
    thus ?thesis
      using that
      unfolding closed_sum_def set_plus_def
      by blast
  qed

  hence \<open>x \<in> space_as_set (Abs_clinear_space (space_as_set B +\<^sub>M space_as_set C))\<close>
    if "x \<in> space_as_set A" for x
    using that
    by (metis space_as_set_inverse sup_ccsubspace.rep_eq)
  thus ?thesis 
    by (simp add: x1 less_eq_ccsubspace.rep_eq subset_eq sup_ccsubspace.rep_eq)
qed

(* Renamed from is_Proj_D1 *)
lemma is_Proj_idempotent:
  assumes "is_Proj P"
  shows "P o\<^sub>C\<^sub>L P = P"
  using assms
  unfolding is_Proj_def
  using assms is_Proj_algebraic by auto

(* Renamed from is_Proj_D2 *)
lemma is_proj_selfadj:
  assumes "is_Proj P"
  shows "P* = P"
  using assms
  unfolding is_Proj_def
  by (metis is_Proj_algebraic is_Proj_def) 

(* Renamed from is_Proj_on_own_range' ? *)
lemma is_Proj_I: 
  assumes "P o\<^sub>C\<^sub>L P = P" and "P* = P"
  shows "is_Proj P"
  using assms is_Proj_algebraic by metis

(* Renamed from is_Proj0 *)
lemma is_Proj_0[simp]: "is_Proj 0"
  by (metis add_left_cancel adj_plus bounded_cbilinear.zero_left bounded_cbilinear_cblinfun_compose group_cancel.rule0 is_Proj_I)

(* Renamed from is_ProjidMinus *)
lemma is_Proj_complement[simp]: 
  assumes a1: "is_Proj P"
  shows "is_Proj (id_cblinfun-P)"
  by (smt (z3) add_diff_cancel_left add_diff_cancel_left' adj_cblinfun_compose adj_plus assms bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose diff_add_cancel id_cblinfun_adjoint is_Proj_algebraic cblinfun_compose_id_left)


subsection \<open>Kernel\<close>

lift_definition kernel :: "'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector
   \<Rightarrow> 'a ccsubspace" 
  is "\<lambda> f. f -` {0}"
  by (metis kernel_is_closed_csubspace)

definition eigenspace :: "complex \<Rightarrow> 'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'a \<Rightarrow> 'a ccsubspace" where
  "eigenspace a A = kernel (A - a *\<^sub>C id_cblinfun)" 

(* Renamed from kernel_scalar_times *)
lemma kernel_scaleC[simp]: "a\<noteq>0 \<Longrightarrow> kernel (a *\<^sub>C A) = kernel A"
  for a :: complex and A :: "(_,_) cblinfun"
  apply transfer
  using complex_vector.scale_eq_0_iff by blast

lemma kernel_0[simp]: "kernel 0 = top"
  apply transfer by auto

lemma kernel_id[simp]: "kernel id_cblinfun = 0"
  apply transfer by simp

(* Renamed from scaleC_eigenspace *)
lemma eigenspace_scaleC[simp]: 
  assumes a1: "a \<noteq> 0"
  shows "eigenspace b (a *\<^sub>C A) = eigenspace (b/a) A"
proof -
  have "b *\<^sub>C (id_cblinfun::('a, _) cblinfun) = a *\<^sub>C (b / a) *\<^sub>C id_cblinfun"
    using a1
    by (metis ceq_vector_fraction_iff)
  hence "kernel (a *\<^sub>C A - b *\<^sub>C id_cblinfun) = kernel (A - (b / a) *\<^sub>C id_cblinfun)"
    using a1 by (metis (no_types) complex_vector.scale_right_diff_distrib kernel_scaleC)
  thus ?thesis 
    unfolding eigenspace_def 
    by blast
qed

subsection \<open>Option\<close>

(* Renamed from inj_option *)
definition "inj_map \<pi> = (\<forall>x y. \<pi> x = \<pi> y \<and> \<pi> x \<noteq> None \<longrightarrow> x = y)"

(* Renamed from inv_option *)
definition "inv_map \<pi> = (\<lambda>y. if Some y \<in> range \<pi> then Some (inv \<pi> (Some y)) else None)"


(* Renamed from inj_map_Some_pi *)
lemma inj_map_total[simp]: "inj_map (Some o \<pi>) = inj \<pi>"
  unfolding inj_map_def inj_def by simp

lemma inj_map_Some[simp]: "inj_map Some"
  by (simp add: inj_map_def)

(* Renamed from inv_map_Some *)
lemma inv_map_total: 
  assumes "surj \<pi>"
  shows "inv_map (Some o \<pi>) = Some o inv \<pi>"
proof-
  have "(if Some y \<in> range (\<lambda>x. Some (\<pi> x))
          then Some (SOME x. Some (\<pi> x) = Some y)
          else None) =
         Some (SOME b. \<pi> b = y)"
    if "surj \<pi>"
    for y
    using that by auto
  hence  "surj \<pi> \<Longrightarrow>
    (\<lambda>y. if Some y \<in> range (\<lambda>x. Some (\<pi> x))
         then Some (SOME x. Some (\<pi> x) = Some y) else None) =
    (\<lambda>x. Some (SOME xa. \<pi> xa = x))"
    by (rule ext) 
  thus ?thesis 
    unfolding inv_map_def o_def inv_def
    using assms by linarith
qed

lemma inj_map_map_comp[simp]: 
  assumes a1: "inj_map f" and a2: "inj_map g" 
  shows "inj_map (f \<circ>\<^sub>m g)"
  using a1 a2
  unfolding inj_map_def
  by (metis (mono_tags, lifting) map_comp_def option.case_eq_if option.expand)

lemma inj_map_inv_map[simp]: "inj_map (inv_map \<pi>)"
proof (unfold inj_map_def, rule allI, rule allI, rule impI, erule conjE)
  fix x y
  assume same: "inv_map \<pi> x = inv_map \<pi> y"
    and pix_not_None: "inv_map \<pi> x \<noteq> None"
  have x_pi: "Some x \<in> range \<pi>" 
    using pix_not_None unfolding inv_map_def apply auto
    by (meson option.distinct(1))
  have y_pi: "Some y \<in> range \<pi>" 
    using pix_not_None unfolding same unfolding inv_map_def apply auto
    by (meson option.distinct(1))
  have "inv_map \<pi> x = Some (Hilbert_Choice.inv \<pi> (Some x))"
    unfolding inv_map_def using x_pi by simp
  moreover have "inv_map \<pi> y = Some (Hilbert_Choice.inv \<pi> (Some y))"
    unfolding inv_map_def using y_pi by simp
  ultimately have "Hilbert_Choice.inv \<pi> (Some x) = Hilbert_Choice.inv \<pi> (Some y)"
    using same by simp
  thus "x = y"
    by (meson inv_into_injective option.inject x_pi y_pi)
qed

subsection \<open>New/restored things\<close>



(* lemma rel_interior_sing_generalized:
  fixes a :: "'n::chilbert_space"
  shows "rel_interior {a} = {a}"
  apply (auto simp: rel_interior_ball)
  by (metis affine_sing gt_ex le_infI2 subset_hull subset_singleton_iff) *)





lemma range_adjoint_isometry:
  assumes "isometry U"
  shows "U* *\<^sub>S top = top"
proof-
  from assms have "top = U* *\<^sub>S U *\<^sub>S top"
    by (simp add: cblinfun_assoc_left(2))
  also have "\<dots> \<le> U* *\<^sub>S top"
    by (simp add: cblinfun_image_mono)
  finally show ?thesis
    using top.extremum_unique by blast
qed

(* Renamed from mult_INF_general *)
lemma cblinfun_image_INF_eq_general:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space ccsubspace"
    and U :: "'b \<Rightarrow>\<^sub>C\<^sub>L'c::chilbert_space"
    and Uinv :: "'c \<Rightarrow>\<^sub>C\<^sub>L'b" 
  assumes UinvUUinv: "Uinv o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L Uinv = Uinv" and UUinvU: "U o\<^sub>C\<^sub>L Uinv o\<^sub>C\<^sub>L U = U"
      \<comment> \<open>Meaning: \<^term>\<open>Uinv\<close> is a Pseudoinverse of \<^term>\<open>U\<close>\<close>
    and V: "\<And>i. V i \<le> Uinv *\<^sub>S top"
  shows "U *\<^sub>S (INF i. V i) = (INF i. U *\<^sub>S V i)"
proof (rule antisym)
  show "U *\<^sub>S (INF i. V i) \<le> (INF i. U *\<^sub>S V i)"
    by (rule cblinfun_image_INF_leq)
next
  define rangeU rangeUinv where "rangeU = U *\<^sub>S top" and "rangeUinv = Uinv *\<^sub>S top"
  define INFUV INFV where INFUV_def: "INFUV = (INF i. U *\<^sub>S V i)" and INFV_def: "INFV = (INF i. V i)"
  from assms have "V i \<le> rangeUinv" 
    for i
    unfolding rangeUinv_def by simp
  moreover have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeUinv" 
    for \<psi>
    using UinvUUinv cblinfun_fixes_range rangeUinv_def that by fastforce
  ultimately have "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set (V i)" 
    for \<psi> i
    using less_eq_ccsubspace.rep_eq that by blast
  hence d1: "(Uinv o\<^sub>C\<^sub>L U) *\<^sub>S (V i) = (V i)" for i
  proof transfer
    show "closure ((Uinv \<circ> U) ` V i) = V i"
      if "pred_fun \<top> closed_csubspace V"
        and "bounded_clinear Uinv"
        and "bounded_clinear U"
        and "\<And>\<psi> i. \<psi> \<in> V i \<Longrightarrow> (Uinv \<circ> U) \<psi> = \<psi>"
      for V :: "'a \<Rightarrow> 'b set"
        and Uinv :: "'c \<Rightarrow> 'b"
        and U :: "'b \<Rightarrow> 'c"
        and i :: 'a
      using that proof auto
      show "x \<in> V i"
        if "\<forall>x. closed_csubspace (V x)"
          and "bounded_clinear Uinv"
          and "bounded_clinear U"
          and "\<And>\<psi> i. \<psi> \<in> V i \<Longrightarrow> Uinv (U \<psi>) = \<psi>"
          and "x \<in> closure (V i)"
        for x :: 'b
        using that
        by (metis orthogonal_complement_of_closure closed_csubspace.subspace double_orthogonal_complement_id closure_is_closed_csubspace) 
      show "x \<in> closure (V i)"
        if "\<forall>x. closed_csubspace (V x)"
          and "bounded_clinear Uinv"
          and "bounded_clinear U"
          and "\<And>\<psi> i. \<psi> \<in> V i \<Longrightarrow> Uinv (U \<psi>) = \<psi>"
          and "x \<in> V i"
        for x :: 'b
        using that
        using setdist_eq_0_sing_1 setdist_sing_in_set
        by blast  
    qed
  qed     
  have "U *\<^sub>S V i \<le> rangeU" for i
    by (simp add: cblinfun_image_mono rangeU_def)
  hence "INFUV \<le> rangeU"
    unfolding INFUV_def by (meson INF_lower UNIV_I order_trans)
  moreover have "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set rangeU" for \<psi>
    using UUinvU cblinfun_fixes_range rangeU_def that by fastforce
  ultimately have x: "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>V \<psi> = \<psi>" if "\<psi> \<in> space_as_set INFUV" for \<psi>
    by (simp add: in_mono less_eq_ccsubspace.rep_eq that)

  have "closure ((U \<circ> Uinv) ` INFUV) = INFUV"
    if "closed_csubspace INFUV"
      and "bounded_clinear U"
      and "bounded_clinear Uinv"
      and "\<And>\<psi>. \<psi> \<in> INFUV \<Longrightarrow> (U \<circ> Uinv) \<psi> = \<psi>"
    for INFUV :: "'c set"
      and U :: "'b \<Rightarrow> 'c"
      and Uinv :: "'c \<Rightarrow> 'b"
    using that proof auto
    show "x \<in> INFUV"
      if "closed_csubspace INFUV"
        and "bounded_clinear U"
        and "bounded_clinear Uinv"
        and "\<And>\<psi>. \<psi> \<in> INFUV \<Longrightarrow> U (Uinv \<psi>) = \<psi>"
        and "x \<in> closure INFUV"
      for x :: 'c
      using that
      by (metis orthogonal_complement_of_closure closed_csubspace.subspace double_orthogonal_complement_id closure_is_closed_csubspace) 
    show "x \<in> closure INFUV"
      if "closed_csubspace INFUV"
        and "bounded_clinear U"
        and "bounded_clinear Uinv"
        and "\<And>\<psi>. \<psi> \<in> INFUV \<Longrightarrow> U (Uinv \<psi>) = \<psi>"
        and "x \<in> INFUV"
      for x :: 'c
      using that
      using setdist_eq_0_sing_1 setdist_sing_in_set
      by (simp add: closed_csubspace.closed)  
  qed
  hence "(U o\<^sub>C\<^sub>L Uinv) *\<^sub>S INFUV = INFUV"
    by (metis (mono_tags, hide_lams) x cblinfun_image.rep_eq cblinfun_image_id id_cblinfun_apply image_cong 
        space_as_set_inject)
  hence "INFUV = U *\<^sub>S Uinv *\<^sub>S INFUV"
    by (simp add: cblinfun_compose_image)
  also have "\<dots> \<le> U *\<^sub>S (INF i. Uinv *\<^sub>S U *\<^sub>S V i)"
    unfolding INFUV_def
    by (metis cblinfun_image_mono cblinfun_image_INF_leq)    
  also have "\<dots> = U *\<^sub>S INFV"
    using d1
    by (metis (no_types, lifting) INFV_def cblinfun_assoc_left(2) image_cong)
  finally show "INFUV \<le> U *\<^sub>S INFV".
qed

(* Renamed from mult_INF *)
lemma cblinfun_image_INF_eq[simp]: 
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space ccsubspace" 
    and U :: "'b \<Rightarrow>\<^sub>C\<^sub>L 'c::chilbert_space"
  assumes \<open>isometry U\<close>
  shows "U *\<^sub>S (INF i. V i) = (INF i. U *\<^sub>S V i)"
proof -
  from \<open>isometry U\<close> have "U* o\<^sub>C\<^sub>L U o\<^sub>C\<^sub>L U* = U*"
    unfolding isometry_def by simp
  moreover from \<open>isometry U\<close> have "U o\<^sub>C\<^sub>L U* o\<^sub>C\<^sub>L U = U"
    unfolding isometry_def
    by (simp add: cblinfun_compose_assoc)
  moreover have "V i \<le> U* *\<^sub>S top" for i
    by (simp add: range_adjoint_isometry assms)
  ultimately show ?thesis
    by (rule cblinfun_image_INF_eq_general)
qed


(* Use le_Inf_iff instead *)
(* lemma leq_INF[simp]:
  fixes V :: "'a \<Rightarrow> 'b::chilbert_space ccsubspace"
  shows "(A \<le> (INF x. V x)) = (\<forall>x. A \<le> V x)" *)

(* Use cblinfun_apply_cblinfun_compose instead *)
(* lemma times_applyOp: "(A o\<^sub>C\<^sub>L B) *\<^sub>V \<psi> = A *\<^sub>V (B *\<^sub>V \<psi>)" *)

lemma mult_inf_distrib[simp]:
  fixes U::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::chilbert_space\<close>
    and X Y::"'a ccsubspace"
  assumes "isometry U"
  shows "U *\<^sub>S (inf X Y) = inf (U *\<^sub>S X) (U *\<^sub>S Y)"
  using cblinfun_image_INF_eq[where V="\<lambda>b. if b then X else Y" and U=U]
  unfolding INF_UNIV_bool_expand
  using assms by auto

(* Use cblinfun.scaleC_left instead *)
(* lemma applyOp_scaleC1[simp]: "(c *\<^sub>C A) *\<^sub>V \<psi> = c *\<^sub>C (A *\<^sub>V \<psi>)" *)

(* Use cblinfun.scaleC_right instead *)
(* lemma applyOp_scaleC2[simp]: "A *\<^sub>V (c *\<^sub>C \<psi>) = c *\<^sub>C (A *\<^sub>V \<psi>)" *)

(* definition bifunctional :: \<open>'a \<Rightarrow> (('a \<Rightarrow> complex) \<Rightarrow> complex)\<close> where
  \<open>bifunctional x = (\<lambda>f. f x)\<close> *)

(* lift_definition Bifunctional' :: \<open>'a::complex_normed_vector \<Rightarrow> (('a, complex) cblinfun \<Rightarrow> complex)\<close>
  is bifunctional. *)

lift_definition bifunctional :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L (('a \<Rightarrow>\<^sub>C\<^sub>L complex) \<Rightarrow>\<^sub>C\<^sub>L complex)\<close>
  is \<open>\<lambda>x f. f *\<^sub>V x\<close>
  by (simp add: cblinfun.flip)

lemma bifunctional_apply[simp]: \<open>(bifunctional *\<^sub>V x) *\<^sub>V f = f *\<^sub>V x\<close>
  by (transfer fixing: x f, simp)

lemma cblinfun_norm_geqI:
  assumes \<open>norm (f *\<^sub>V x) / norm x \<ge> K\<close>
  shows \<open>norm f \<ge> K\<close>
  using assms apply transfer
  by (smt (z3) bounded_clinear.bounded_linear le_onorm)

lemma bifunctional_isometric[simp]: \<open>norm (bifunctional *\<^sub>V x) = norm x\<close> for x :: \<open>'a::complex_inner\<close>
proof -
  define f :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L complex\<close> where \<open>f = cBlinfun (\<lambda>y. cinner x y)\<close>
  then have [simp]: \<open>f *\<^sub>V y = cinner x y\<close> for y
    by (simp add: bounded_clinear_cBlinfun_apply bounded_clinear_cinner_right)
  then have [simp]: \<open>norm f = norm x\<close>
    apply (auto intro!: norm_cblinfun_eqI[where x=x] simp: power2_norm_eq_cinner[symmetric])
    apply (smt (verit, best) norm_eq_sqrt_cinner norm_ge_zero power2_norm_eq_cinner real_div_sqrt)
    using Cauchy_Schwarz_ineq2 by blast
  show ?thesis
    apply (auto intro!: norm_cblinfun_eqI[where x=f])
    apply (metis norm_eq_sqrt_cinner norm_imp_pos_and_ge real_div_sqrt)
    by (metis norm_cblinfun ordered_field_class.sign_simps(33))
qed

lemma norm_bifunctional[simp]: \<open>norm (bifunctional :: 'a::{complex_inner, not_singleton} \<Rightarrow>\<^sub>C\<^sub>L _) = 1\<close>
proof -
  obtain x :: 'a where [simp]: \<open>norm x = 1\<close>
    by (meson UNIV_not_singleton ex_norm1)
  show ?thesis
    by (auto intro!: norm_cblinfun_eqI[where x=x])
qed

(* Use norm_cblinfun instead *)
(* lemma norm_of_cblinfun:
  \<open>norm (L *\<^sub>V z) \<le> norm z * norm L\<close> *)

(* Use norm_cblinfun instead *)
(* lemma norm_of_cblinfun1:
  assumes a1: "norm z = 1"
  shows  "norm (L *\<^sub>V z) \<le> norm L" *)

(* Use norm_cblinfun instead *)
(* lemma norm_of_cblinfun2:
  assumes a1: "norm z \<le> 1"
  shows "norm (L *\<^sub>V z) \<le> norm L" *)

(* lemma onormless1: 
  assumes a1: "norm x < 1" and a2: "bounded_clinear f"
  shows "norm (f x) \<le> onorm f"
proof-
  have "norm (f x) \<le> onorm f * norm x"
    using a2 onorm
    by (simp add: onorm bounded_clinear.bounded_linear)    
  also have "\<dots> \<le> onorm f"
    using a1 a2 mult_right_le_one_le onorm_pos_le
    by (smt bounded_clinear.bounded_linear norm_not_less_zero) 
  finally show ?thesis by blast
qed *)

(* lemma norm1_normless1_approx:
  assumes a1: "norm t = 1" and a2: "e > 0"
  shows "\<exists>s. norm s < 1 \<and> norm (t - s) < e"
proof(cases "e > 1")
  case True
  thus ?thesis
    by (smt a1 diff_zero norm_zero)     
next
  case False
  define s where "s = (1-e/2) *\<^sub>R t"
  have a1:"1-e/2 < 1"
    by (simp add: a2)
  moreover have "norm s = abs (1-e/2) * norm t"
    unfolding s_def by auto
  ultimately have b1: "norm s < 1"
    using a1 False assms(1) by auto 

  have "t - s = (e/2) *\<^sub>R t"
    unfolding s_def
    by (smt diff_eq_eq scaleR_collapse) 
  hence "norm (t - s) = abs (e/2) * norm t"
    by simp    
  hence b2: "norm (t - s) < e"
    using a1 assms(1) by auto 
  from b1 b2 show ?thesis by blast
qed *)

(* lemma norm_of_cblinfun3:
  fixes S::"'a::{complex_normed_vector,not_singleton} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector"
  shows "norm S = Sup {norm (S *\<^sub>V x)| x. norm x < 1}"
proof transfer 
  have a1: \<open>(UNIV::'a set) \<noteq> 0\<close>
    by simp
  fix S::\<open>'a \<Rightarrow> 'b\<close>
  assume a2: \<open>bounded_clinear S\<close>
  define X where X_def: "X = {norm (S x) |x. norm x < 1}"
  define a where a_def: "a = onorm S"
  have "x \<le> a"
    if "x \<in> X"
    for x
  proof-
    obtain x' where x2: "x = norm (S x')" and x3: "norm x' < 1"
      using that X_def \<open>x \<in> X\<close> by auto 
    have "norm (S x') \<le> onorm S"
      using x3 a2 onormless1 bounded_clinear.bounded_linear by auto
    hence "x \<le> onorm S"
      by (simp add: x2) 
    thus ?thesis
      unfolding X_def a_def
      by simp 
  qed
  moreover have "a \<le> y" 
    if b1: "\<And>x. x \<in> X \<Longrightarrow> x \<le> y"
    for y
  proof-
    have f1: "norm t < 1 \<Longrightarrow> norm (S t) \<le> y" for t
      using b1
      unfolding X_def by blast 
    have "onorm S \<le> y+e" 
      if e0:"e>0"      
      for e
    proof-
      have \<open>bounded_clinear S\<close>
        using a2
        by (simp add: bounded_clinear.bounded_linear)
      hence "onorm S = Sup { norm (S t) |t. norm t = 1 }"
        using a1 onorm_sphere[where f = S]
        by (simp add: bounded_clinear.bounded_linear)
      hence u1: "onorm S - e/2 < Sup { norm (S t) |t. norm t = 1 }"
        by (simp add: e0)        
      moreover have u2: "{ norm (S t) |t. norm t = 1 } \<noteq> {}"
      proof-
        have "\<exists>t::'a. norm t = 1"
          using a1 ex_norm1
          by (simp add: ex_norm1) 
        thus ?thesis
          by simp 
      qed
      ultimately have u3: "\<exists>T\<in>{ norm (S t) |t. norm t = 1 }. onorm S - e/2 \<le> T"
        using e0 Sup_real_def
        by (meson less_cSupE less_eq_real_def)
      hence "\<exists>t. norm t = 1 \<and> onorm S - e/2 \<le> norm (S t)"
        by auto
      then obtain t where s1: "norm t = 1" and s2: "onorm S - e/2 \<le> norm (S t)"
        by blast
      have "isCont S w" for w
        using linear_continuous_at
        by (simp add: a2 clinear_continuous_at)
      hence "isCont (\<lambda>x. norm (S x)) w" for w
        by simp
      hence "e > 0 \<Longrightarrow> \<exists>\<delta>>0. \<forall>s. norm (t - s) < \<delta> \<longrightarrow>  norm (norm (S t) - norm (S s)) < e" for e
        unfolding isCont_def LIM_def using dist_norm
        by (metis dist_commute eq_iff_diff_eq_0 norm_eq_zero) 
      hence "\<exists>\<delta>>0. \<forall>s. norm (t - s) < \<delta> \<longrightarrow> norm (norm (S t) - norm (S s)) < e/2"
        using e0 half_gt_zero by blast
      then obtain \<delta> where delta1: "\<delta>>0" and 
        delta2: "\<forall>s. norm (t - s) < \<delta> \<longrightarrow> norm (norm (S t) - norm (S s)) < e/2"
        by blast
      have "\<exists>s. norm s < 1 \<and> norm (t - s) < \<delta>"        
        by (simp add: norm1_normless1_approx delta1 s1) 
      then obtain s where b1:"norm s < 1" and b2:"norm (t - s) < \<delta>"
        by blast
      have w:"norm (norm (S t) - norm (S s)) < e/2"
        using b2 delta2 by auto
      have "norm (S t) \<le> norm (S s) + norm (norm (S t) - norm (S s))"
        by auto
      hence "norm (S t) \<le> norm (S s) + e/2"
        using w by linarith        
      moreover have "norm (S s) \<le> y"
        using f1
        by (simp add: b1)         
      ultimately show "onorm S \<le> y+e"
        using s2 by linarith        
    qed
    hence "onorm S \<le> y"
      using linordered_field_class.field_le_epsilon by blast      
    thus "a \<le> y"
      unfolding a_def by blast
  qed
  ultimately have "Sup X = a"
    using cSup_eq by blast
  thus "onorm S = Sup {norm (S x) |x. norm x < 1}"
    unfolding X_def a_def by simp
qed *)

subsection \<open>Isomorphisms and inverses\<close>

(* Renamed from invertible_cblinfun *)
definition iso_cblinfun :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun \<Rightarrow> bool\<close> where
  \<open>iso_cblinfun A = (\<exists> B. A o\<^sub>C\<^sub>L B = id_cblinfun \<and> B o\<^sub>C\<^sub>L A = id_cblinfun)\<close>

definition cblinfun_inv :: \<open>('a::complex_normed_vector, 'b::complex_normed_vector) cblinfun \<Rightarrow> ('b,'a) cblinfun\<close> where
  \<open>cblinfun_inv A = (SOME B. B o\<^sub>C\<^sub>L A = id_cblinfun)\<close>
  (* \<open>cblinfun_inv A = (THE B. A o\<^sub>C\<^sub>L B = id_cblinfun \<and> B o\<^sub>C\<^sub>L A = id_cblinfun)\<close> *)

lemma 
  assumes \<open>iso_cblinfun A\<close>
  shows cblinfun_inv_left: \<open>cblinfun_inv A o\<^sub>C\<^sub>L A = id_cblinfun\<close>
    and cblinfun_inv_right: \<open>A o\<^sub>C\<^sub>L cblinfun_inv A = id_cblinfun\<close>
proof -
  from assms
  obtain B where AB: \<open>A o\<^sub>C\<^sub>L B = id_cblinfun\<close> and BA: \<open>B o\<^sub>C\<^sub>L A = id_cblinfun\<close>
    using iso_cblinfun_def by blast
  from BA have \<open>cblinfun_inv A o\<^sub>C\<^sub>L A = id_cblinfun\<close>
    by (metis (mono_tags, lifting) cblinfun_inv_def someI_ex)
  with AB BA have \<open>cblinfun_inv A = B\<close>
    by (metis cblinfun_assoc_left(1) cblinfun_compose_id_right)
  with AB BA show \<open>cblinfun_inv A o\<^sub>C\<^sub>L A = id_cblinfun\<close>
    and \<open>A o\<^sub>C\<^sub>L cblinfun_inv A = id_cblinfun\<close>
    by auto
qed

(* lemma cblinfun_inv_well_defined:
  assumes a1: "iso_cblinfun A"
  shows "\<exists>!B. A o\<^sub>C\<^sub>L B = id_cblinfun \<and> B o\<^sub>C\<^sub>L A = id_cblinfun"
proof-
  have \<open>B *\<^sub>V x = B' *\<^sub>V x\<close>
    if \<open>A o\<^sub>C\<^sub>L B = id_cblinfun\<close> and \<open>B o\<^sub>C\<^sub>L A = id_cblinfun\<close> and \<open>A o\<^sub>C\<^sub>L B' = id_cblinfun\<close> and \<open>B' o\<^sub>C\<^sub>L A = id_cblinfun\<close>
    for A::"'a \<Rightarrow>\<^sub>C\<^sub>L 'b" and B B' and x
  proof-
    have \<open>(A o\<^sub>C\<^sub>L B) *\<^sub>V x = x\<close>
      using \<open>A o\<^sub>C\<^sub>L B = id_cblinfun\<close>
      by simp
    hence u1: \<open>B' *\<^sub>V ((A o\<^sub>C\<^sub>L B) *\<^sub>V x) = B' *\<^sub>V x\<close>
      by simp
    have \<open>B' *\<^sub>V ((A o\<^sub>C\<^sub>L B) *\<^sub>V x) = B' *\<^sub>V (A *\<^sub>V (B *\<^sub>V x))\<close>
      by simp
    also have \<open>\<dots> = (B' o\<^sub>C\<^sub>L A) *\<^sub>V (B *\<^sub>V x)\<close>
      by simp
    also have \<open>\<dots> = id_cblinfun *\<^sub>V (B *\<^sub>V x)\<close>
      by (simp add: \<open>B' o\<^sub>C\<^sub>L A = id_cblinfun\<close>)
    also have \<open>\<dots> = B *\<^sub>V x\<close>
      by simp
    finally have u2: \<open>B' *\<^sub>V ((A o\<^sub>C\<^sub>L B) *\<^sub>V x) = B *\<^sub>V x\<close>
      by blast
    show ?thesis
      using u1 u2
      by auto
  qed
  thus ?thesis
    by (meson assms cblinfun_eqI iso_cblinfun_def)
qed *)

lemma cblinfun_inv_uniq:
  assumes "A o\<^sub>C\<^sub>L B = id_cblinfun" and "B o\<^sub>C\<^sub>L A = id_cblinfun"
  shows "cblinfun_inv A = B"
  using assms by (metis cblinfun_compose_assoc cblinfun_compose_id_right cblinfun_inv_left iso_cblinfun_def)

subsection \<open>Loewner order\<close>

lift_definition heterogenous_cblinfun_id :: \<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  is \<open>if bounded_clinear (heterogenous_identity :: 'a::complex_normed_vector \<Rightarrow> 'b::complex_normed_vector) then heterogenous_identity else (\<lambda>_. 0)\<close>
  by auto

lemma heterogenous_cblinfun_id_def'[simp]: "heterogenous_cblinfun_id = id_cblinfun"
  apply transfer by auto

definition "heterogenous_same_type_cblinfun (x::'a::chilbert_space itself) (y::'b::chilbert_space itself) \<longleftrightarrow>
  unitary (heterogenous_cblinfun_id :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<and> unitary (heterogenous_cblinfun_id :: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)"

lemma heterogenous_same_type_cblinfun[simp]: \<open>heterogenous_same_type_cblinfun (x::'a::chilbert_space itself) (y::'a::chilbert_space itself)\<close>
  unfolding heterogenous_same_type_cblinfun_def by auto

instantiation cblinfun :: (chilbert_space, chilbert_space) ord begin
definition less_eq_cblinfun :: \<open>('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Rightarrow> bool\<close>
  where less_eq_cblinfun_def_heterogenous: \<open>less_eq_cblinfun A B = 
  (if heterogenous_same_type_cblinfun TYPE('a) TYPE('b) then
    \<forall>\<psi>::'b. cinner \<psi> ((B-A) *\<^sub>V heterogenous_cblinfun_id *\<^sub>V \<psi>) \<ge> 0 else (A=B))\<close>
definition \<open>less_cblinfun (A :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b) B \<longleftrightarrow> A \<le> B \<and> \<not> B \<le> A\<close>
instance..
end

lemma less_eq_cblinfun_def: \<open>A \<le> B \<longleftrightarrow>
    (\<forall>\<psi>. cinner \<psi> (A *\<^sub>V \<psi>) \<le> cinner \<psi> (B *\<^sub>V \<psi>))\<close>
  unfolding less_eq_cblinfun_def_heterogenous 
  by (auto simp del: less_eq_complex_def simp: cblinfun.diff_left cinner_diff_right)

instantiation cblinfun :: (chilbert_space, chilbert_space) ordered_complex_vector begin
instance
proof intro_classes
  note less_eq_complex_def[simp del]

  fix x y z :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  fix a b :: complex

  define pos where \<open>pos X \<longleftrightarrow> (\<forall>\<psi>. cinner \<psi> (X *\<^sub>V \<psi>) \<ge> 0)\<close> for X :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'b\<close>
  consider (unitary) \<open>heterogenous_same_type_cblinfun TYPE('a) TYPE('b)\<close>
      \<open>\<And>A B :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b. A \<le> B = pos ((B-A) o\<^sub>C\<^sub>L (heterogenous_cblinfun_id :: 'b\<Rightarrow>\<^sub>C\<^sub>L'a))\<close>
    | (trivial) \<open>\<And>A B :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b. A \<le> B \<longleftrightarrow> A = B\<close>
    apply atomize_elim by (auto simp: pos_def less_eq_cblinfun_def_heterogenous)
  note cases = this
  
  have [simp]: \<open>pos 0\<close>
    unfolding pos_def by auto

  have pos_nondeg: \<open>X = 0\<close> if \<open>pos X\<close> and \<open>pos (-X)\<close> for X
    apply (rule cblinfun_cinner_eqI, simp)
    using that by (metis (no_types, lifting) cblinfun.minus_left cinner_minus_right dual_order.antisym equation_minus_iff neg_le_0_iff_le pos_def)

  have pos_add: \<open>pos (X+Y)\<close> if \<open>pos X\<close> and \<open>pos Y\<close> for X Y
    by (smt (z3) pos_def cblinfun.diff_left cinner_minus_right cinner_simps(3) diff_ge_0_iff_ge diff_minus_eq_add neg_le_0_iff_le order_trans that(1) that(2) uminus_cblinfun.rep_eq)

  have pos_scaleC: \<open>pos (a *\<^sub>C X)\<close> if \<open>a\<ge>0\<close> and \<open>pos X\<close> for X a
    using that unfolding pos_def by (auto simp: cblinfun.scaleC_left)

  let ?id = \<open>heterogenous_cblinfun_id :: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>

  show \<open>x \<le> x\<close>
    apply (cases rule:cases) by auto
  show \<open>(x < y) \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)\<close>
    unfolding less_cblinfun_def by simp
  show \<open>x \<le> z\<close> if \<open>x \<le> y\<close> and \<open>y \<le> z\<close>
  proof (cases rule:cases)
    case unitary
    define a b :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>a = (y-x) o\<^sub>C\<^sub>L heterogenous_cblinfun_id\<close>
      and \<open>b = (z-y) o\<^sub>C\<^sub>L heterogenous_cblinfun_id\<close>
    with unitary that have \<open>pos a\<close> and \<open>pos b\<close>
      by auto
    then have \<open>pos (a + b)\<close>
      by (rule pos_add)
    moreover have \<open>a + b = (z - x) o\<^sub>C\<^sub>L heterogenous_cblinfun_id\<close>
      unfolding a_def b_def
      by (metis (no_types, lifting) bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose diff_add_cancel ordered_field_class.sign_simps(2) ordered_field_class.sign_simps(8))
    ultimately show ?thesis 
      using unitary by auto
  next
    case trivial
    with that show ?thesis by auto
  qed
  show \<open>x = y\<close> if \<open>x \<le> y\<close> and \<open>y \<le> x\<close>
  proof (cases rule:cases)
    case unitary
    then have \<open>unitary ?id\<close>
      by (auto simp: heterogenous_same_type_cblinfun_def)
    define a b :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> where \<open>a = (y-x) o\<^sub>C\<^sub>L ?id\<close>
      and \<open>b = (x-y) o\<^sub>C\<^sub>L ?id\<close>
    with unitary that have \<open>pos a\<close> and \<open>pos b\<close>
      by auto
    then have \<open>a = 0\<close>
      apply (rule_tac pos_nondeg)
      apply (auto simp: a_def b_def)
      by (smt (verit, best) add.commute bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose cblinfun_compose_zero_left diff_0 diff_add_cancel group_cancel.rule0 group_cancel.sub1)
    then show ?thesis
      unfolding a_def using \<open>unitary ?id\<close>
      by (metis cblinfun_compose_assoc cblinfun_compose_id_right cblinfun_compose_zero_left eq_iff_diff_eq_0 unitaryD2)
  next
    case trivial
    with that show ?thesis by simp
  qed
  show \<open>x + y \<le> x + z\<close> if \<open>y \<le> z\<close>
  proof (cases rule:cases)
    case unitary
    with that show ?thesis 
      by auto
  next
    case trivial
    with that show ?thesis 
      by auto
  qed

  show \<open>a *\<^sub>C x \<le> a *\<^sub>C y\<close> if \<open>x \<le> y\<close> and \<open>0 \<le> a\<close>
  proof (cases rule:cases)
    case unitary
    with that pos_scaleC show ?thesis
      by (metis cblinfun_compose_scaleC_left complex_vector.scale_right_diff_distrib) 
  next
    case trivial
    with that show ?thesis 
      by auto
  qed

  show \<open>a *\<^sub>C x \<le> b *\<^sub>C x\<close> if \<open>a \<le> b\<close> and \<open>0 \<le> x\<close>
  proof (cases rule:cases)
    case unitary
    with that show ?thesis
      by (auto intro!: pos_scaleC simp flip: scaleC_diff_left)
  next
    case trivial
    with that show ?thesis 
      by auto
  qed
qed
end

lemma positive_id_cblinfun[simp]: "id_cblinfun \<ge> 0"
  unfolding less_eq_cblinfun_def using cinner_ge_zero by auto

lemma positive_hermitianI: \<open>A = A*\<close> if \<open>A \<ge> 0\<close>
  apply (rule cinner_real_hermiteanI)
  using that by (auto simp del: less_eq_complex_def simp: reals_zero_comparable_iff less_eq_cblinfun_def)

lemma positive_cblinfunI: \<open>A \<ge> 0\<close> if \<open>\<And>x. cinner x (A *\<^sub>V x) \<ge> 0\<close>
  unfolding less_eq_cblinfun_def using that by auto

(* Note: this does not require B to be a square operator *)
lemma positive_cblinfun_squareI: \<open>A = B* o\<^sub>C\<^sub>L B \<Longrightarrow> A \<ge> 0\<close>
  apply (rule positive_cblinfunI)
  by (metis cblinfun_apply_cblinfun_compose cinner_adj_right cinner_ge_zero)



subsection \<open>Recovered theorems\<close>


lemma zero_scaleC_ccsubspace[simp]: "0 *\<^sub>S S = (0::_ ccsubspace)"
  apply transfer by (simp add: complex_vector.subspace_0 image_constant[where x=0])

(* Use ccsubspace_scaleC_invariant instead *)
(* lemma one_times_op[simp]: "(1::complex) *\<^sub>C B = B"
  for B::\<open>'a::complex_normed_vector ccsubspace\<close> *)

(* Use cblinfun_compose_image instead *)
(* lemma cblinfun_apply_assoc_subspace: "(A o\<^sub>C\<^sub>L B) *\<^sub>S S =  A *\<^sub>S (B *\<^sub>S S)" *)

lift_definition vector_to_cblinfun :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> is
  \<open>\<lambda>\<psi> \<phi>. one_dim_iso \<phi> *\<^sub>C \<psi>\<close>
  by (simp add: bounded_clinear_scaleC_const)

(* TODO: rename *)
lemma vector_to_cblinfun_applyOp: 
  "vector_to_cblinfun (A *\<^sub>V \<psi>) = A  o\<^sub>C\<^sub>L (vector_to_cblinfun \<psi>)" 
  apply transfer 
  unfolding comp_def bounded_clinear_def clinear_def Vector_Spaces.linear_def
    module_hom_def module_hom_axioms_def
  by simp

lemma vector_to_cblinfun_add: \<open>vector_to_cblinfun (x + y) = vector_to_cblinfun x + vector_to_cblinfun y\<close>
  apply transfer
  by (simp add: scaleC_add_right)

lemma norm_vector_to_cblinfun[simp]: "norm (vector_to_cblinfun x) = norm x"
proof transfer
  have "bounded_clinear (one_dim_iso::'a \<Rightarrow> complex)"
    by simp    
  moreover have "onorm (one_dim_iso::'a \<Rightarrow> complex) * norm x = norm x"
    for x :: 'b
    by simp
  ultimately show "onorm (\<lambda>\<phi>. one_dim_iso (\<phi>::'a) *\<^sub>C x) = norm x"
    for x :: 'b
    by (subst onorm_scaleC_left)
qed

lemma bounded_clinear_vector_to_cblinfun[bounded_clinear]: "bounded_clinear vector_to_cblinfun"
  apply (rule bounded_clinearI[where K=1])
    apply (transfer, simp add: scaleC_add_right)
   apply (transfer, simp add: mult.commute)
  by simp

(* Renamed from vector_to_cblinfun_scalar_times *)
lemma vector_to_cblinfun_scaleC[simp]:
  "vector_to_cblinfun (a *\<^sub>C \<psi>) = a *\<^sub>C vector_to_cblinfun \<psi>" for a::complex
proof (subst asm_rl [of "a *\<^sub>C \<psi> = (a *\<^sub>C id_cblinfun) *\<^sub>V \<psi>"])
  show "a *\<^sub>C \<psi> = a *\<^sub>C id_cblinfun *\<^sub>V \<psi>"
    by (simp add: scaleC_cblinfun.rep_eq)
  show "vector_to_cblinfun (a *\<^sub>C id_cblinfun *\<^sub>V \<psi>) = a *\<^sub>C (vector_to_cblinfun \<psi>::'a \<Rightarrow>\<^sub>C\<^sub>L 'b)"
    by (metis cblinfun_id_cblinfun_apply cblinfun_compose_scaleC_left vector_to_cblinfun_applyOp)
qed


(* Use blinfun_of_cblinfun instead *)
(* lift_definition cblinfun_to_blinfun::\<open>'a::complex_normed_vector \<Rightarrow>\<^sub>C\<^sub>L'b::complex_normed_vector \<Rightarrow> ('a \<Rightarrow>\<^sub>L 'b)\<close> 
  is \<open>(\<lambda>f. (( *\<^sub>V ) f))\<close>
  apply transfer
  by (simp add: bounded_clinear.bounded_linear)

lemma cblinfun_to_blinfun_transfer[cblinfun_blinfun_transfer]:
  includes lifting_syntax
  shows "(blinfun_cblinfun_eq ===> (=)) (\<lambda>x. x) cblinfun_to_blinfun"
  unfolding rel_fun_def blinfun_cblinfun_eq.rep_eq
  apply transfer by auto

lemma cblinfun_to_blinfun_norm: "norm (cblinfun_to_blinfun F) = norm F"
  using cblinfun_blinfun_transfer[transfer_rule] apply (rule TrueI)? (* Deletes current facts *)
  apply transfer by simp *)


(* Renamed from banach_steinhaus_cblinfun *)
theorem cbanach_steinhaus:
  fixes F :: \<open>'c \<Rightarrow> 'a::cbanach \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<And>x. \<exists>M. \<forall>n.  norm ((F n) *\<^sub>V x) \<le> M\<close>
  shows  \<open>\<exists>M. \<forall> n. norm (F n) \<le> M\<close>  
  using cblinfun_blinfun_transfer[transfer_rule] apply (rule TrueI)? (* Deletes current facts *)
proof (use assms in transfer)
  fix F :: \<open>'c \<Rightarrow> 'a \<Rightarrow>\<^sub>L 'b\<close> assume \<open>(\<And>x. \<exists>M. \<forall>n. norm (F n *\<^sub>v x) \<le> M)\<close>
  hence \<open>\<And>x. bounded (range (\<lambda>n. blinfun_apply (F n) x))\<close>
    by (metis (no_types, lifting) boundedI rangeE)
  hence \<open>bounded (range F)\<close>
    by (simp add: banach_steinhaus)
  thus  \<open>\<exists>M. \<forall>n. norm (F n) \<le> M\<close>
    by (simp add: bounded_iff)
qed

theorem riesz_frechet_representation_cblinfun_existence:
  \<comment> \<open>Theorem 3.4 in @{cite conway2013course}\<close>
  fixes f::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  shows \<open>\<exists>t. \<forall>x.  f *\<^sub>V x = \<langle>t, x\<rangle>\<close>
  apply transfer by (rule riesz_frechet_representation_existence)

lemma riesz_frechet_representation_cblinfun_unique:
  \<comment> \<open>Theorem 3.4 in @{cite conway2013course}\<close>
  fixes f::\<open>'a::complex_inner \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  assumes \<open>\<And>x. f *\<^sub>V x = \<langle>t, x\<rangle>\<close>
  assumes \<open>\<And>x. f *\<^sub>V x = \<langle>u, x\<rangle>\<close>
  shows \<open>t = u\<close>
  using assms by (rule riesz_frechet_representation_unique)

theorem riesz_frechet_representation_cblinfun_norm:
  includes notation_norm
  fixes f::\<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L complex\<close>
  assumes \<open>\<And>x.  f *\<^sub>V x = \<langle>t, x\<rangle>\<close>
  shows \<open>\<parallel>f\<parallel> = \<parallel>t\<parallel>\<close>
  using assms 
proof transfer
  fix f::\<open>'a \<Rightarrow> complex\<close> and t
  assume \<open>bounded_clinear f\<close> and \<open>\<And>x. f x = \<langle>t, x\<rangle>\<close> 
  from  \<open>\<And>x. f x = \<langle>t, x\<rangle>\<close> 
  have \<open>(norm (f x)) / (norm x) \<le> norm t\<close>
    for x
  proof(cases \<open>norm x = 0\<close>)
    case True
    thus ?thesis by simp
  next
    case False
    have \<open>norm (f x) = norm (\<langle>t, x\<rangle>)\<close>
      using \<open>\<And>x. f x = \<langle>t, x\<rangle>\<close> by simp
    also have \<open>norm \<langle>t, x\<rangle> \<le> norm t * norm x\<close>
      by (simp add: complex_inner_class.Cauchy_Schwarz_ineq2)
    finally have \<open>norm (f x) \<le> norm t * norm x\<close>
      by blast
    thus ?thesis
      by (metis False linordered_field_class.divide_right_mono nonzero_mult_div_cancel_right norm_ge_zero) 
  qed
  moreover have \<open>(norm (f t)) / (norm t) = norm t\<close>
  proof(cases \<open>norm t = 0\<close>)
    case True
    thus ?thesis
      by simp 
  next
    case False
    have \<open>f t = \<langle>t, t\<rangle>\<close>
      using \<open>\<And>x. f x = \<langle>t, x\<rangle>\<close> by blast
    also have \<open>\<dots> = (norm t)^2\<close>
      by (meson cnorm_eq_square)
    also have \<open>\<dots> = (norm t)*(norm t)\<close>
      by (simp add: power2_eq_square)
    finally have \<open>f t = (norm t)*(norm t)\<close>
      by blast
    thus ?thesis
      by (metis False Re_complex_of_real \<open>\<And>x. f x = cinner t x\<close> cinner_ge_zero complex_of_real_cmod nonzero_divide_eq_eq)
  qed
  ultimately have \<open>Sup {(norm (f x)) / (norm x)| x. True} = norm t\<close>
    by (smt cSup_eq_maximum mem_Collect_eq)    
  moreover have \<open>Sup {(norm (f x)) / (norm x)| x. True} = (SUP x. (norm (f x)) / (norm x))\<close>
    by (simp add: full_SetCompr_eq)    
  ultimately show \<open>onorm f = norm t\<close>
    by (simp add: onorm_def) 
qed

(* Use cblinfun.sum_right instead *)
(* lemma clinear_finite_sum:
  shows "F *\<^sub>V (\<Sum>a\<in>S. r a *\<^sub>C a) = (\<Sum>a\<in>S. r a *\<^sub>C (F *\<^sub>V a))" *)

(* Renamed from vector_to_cblinfun_times_vec *)
lemma vector_to_cblinfun_apply_one_dim[simp]:
  shows "vector_to_cblinfun \<phi> *\<^sub>V \<gamma> = one_dim_iso \<gamma> *\<^sub>C \<phi>"
  apply transfer by (rule refl)

(* Renamed from vector_to_cblinfun_adj_times_vec *)
lemma vector_to_cblinfun_adj_apply[simp]:
  shows "vector_to_cblinfun \<psi>* *\<^sub>V \<phi> = of_complex (cinner \<psi> \<phi>)"
  by (simp add: cinner_adj_right one_dim_iso_def one_dim_iso_inj) 

instantiation cblinfun :: (one_dim, one_dim) complex_inner begin
text \<open>Once we have a theory for the trace, we could instead define the Hilbert-Schmidt inner product
  and relax the \<^class>\<open>one_dim\<close>-sort constraint to (\<^class>\<open>cfinite_dim\<close>,\<^class>\<open>complex_normed_vector\<close>) or similar\<close>
definition "cinner_cblinfun (A::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) (B::'a \<Rightarrow>\<^sub>C\<^sub>L 'b)
             = cnj (one_dim_iso (A *\<^sub>V 1)) * one_dim_iso (B *\<^sub>V 1)"
instance
proof intro_classes
  fix A B C :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    and c c' :: complex
  show "\<langle>A, B\<rangle> = cnj \<langle>B, A\<rangle>"
    unfolding cinner_cblinfun_def by auto
  show "\<langle>A + B, C\<rangle> = \<langle>A, C\<rangle> + \<langle>B, C\<rangle>"
    by (simp add: cinner_cblinfun_def algebra_simps plus_cblinfun.rep_eq) 
  show "\<langle>c *\<^sub>C A, B\<rangle> = cnj c * \<langle>A, B\<rangle>"
    by (simp add: cblinfun.scaleC_left cinner_cblinfun_def)
  show "0 \<le> \<langle>A, A\<rangle>"
    unfolding cinner_cblinfun_def by auto
  have "bounded_clinear A \<Longrightarrow> A 1 = 0 \<Longrightarrow> A = (\<lambda>_. 0)"
    for A::"'a \<Rightarrow> 'b"
  proof (rule one_dim_clinear_eqI [where x = 1] , auto)
    show "clinear A"
      if "bounded_clinear A"
        and "A 1 = 0"
      for A :: "'a \<Rightarrow> 'b"
      using that
      by (simp add: bounded_clinear.clinear)
    show "clinear ((\<lambda>_. 0)::'a \<Rightarrow> 'b)"
      if "bounded_clinear A"
        and "A 1 = 0"
      for A :: "'a \<Rightarrow> 'b"
      using that
      by (simp add: complex_vector.module_hom_zero) 
  qed
  hence "A *\<^sub>V 1 = 0 \<Longrightarrow> A = 0"
    by transfer
  hence "one_dim_iso (A *\<^sub>V 1) = 0 \<Longrightarrow> A = 0"
    by (metis one_dim_iso_of_zero one_dim_iso_inj)    
  thus "(\<langle>A, A\<rangle> = 0) = (A = 0)"
    by (auto simp: cinner_cblinfun_def)

  show "norm A = sqrt (cmod \<langle>A, A\<rangle>)"
    unfolding cinner_cblinfun_def 
    apply transfer 
    by (simp add: norm_mult abs_complex_def one_dim_onorm' cnj_x_x power2_eq_square bounded_clinear.clinear)
qed
end

instantiation cblinfun :: (one_dim, one_dim) one_dim begin
lift_definition one_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b" is "one_dim_iso"
  by (rule bounded_clinear_one_dim_iso)
lift_definition times_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
  is "\<lambda>f g. f o one_dim_iso o g"
  by (simp add: comp_bounded_clinear)
lift_definition inverse_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" is
  "\<lambda>f. ((*) (one_dim_iso (inverse (f 1)))) o one_dim_iso"
  by (auto intro!: comp_bounded_clinear bounded_clinear_mult_right)
definition divide_cblinfun :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'b" where
  "divide_cblinfun A B = A * inverse B"
definition "canonical_basis_cblinfun = [1 :: 'a \<Rightarrow>\<^sub>C\<^sub>L 'b]"
instance
proof intro_classes
  let ?basis = "canonical_basis :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) list"
  fix A B C :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
    and c c' :: complex
  show "distinct ?basis"
    unfolding canonical_basis_cblinfun_def by simp
  have "(1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<noteq> (0::'a \<Rightarrow>\<^sub>C\<^sub>L 'b)"
    by (metis cblinfun.zero_left one_cblinfun.rep_eq one_dim_iso_of_one zero_neq_one)
  thus "cindependent (set ?basis)"
    unfolding canonical_basis_cblinfun_def by simp

  have "A \<in> cspan (set ?basis)" for A
  proof -
    define c :: complex where "c = one_dim_iso (A *\<^sub>V 1)"
    have "A x = one_dim_iso (A 1) *\<^sub>C one_dim_iso x" for x
      by (smt (z3) cblinfun.scaleC_right complex_vector.scale_left_commute one_dim_iso_idem one_dim_scaleC_1)
    hence "A = one_dim_iso (A *\<^sub>V 1) *\<^sub>C 1"
      apply transfer by metis
    thus "A \<in> cspan (set ?basis)"
      unfolding canonical_basis_cblinfun_def
      by (smt complex_vector.span_base complex_vector.span_scale list.set_intros(1))
  qed
  thus "cspan (set ?basis) = UNIV" by auto

  have "A = (1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Longrightarrow>
    norm (1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = (1::real)"
    apply transfer by simp
  thus "A \<in> set ?basis \<Longrightarrow> norm A = 1"
    unfolding canonical_basis_cblinfun_def 
    by simp

  show "?basis = [1]"
    unfolding canonical_basis_cblinfun_def by simp
  show "c *\<^sub>C 1 * c' *\<^sub>C 1 = (c * c') *\<^sub>C (1::'a\<Rightarrow>\<^sub>C\<^sub>L'b)"
    apply transfer by auto
  have "(1::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) = (0::'a \<Rightarrow>\<^sub>C\<^sub>L 'b) \<Longrightarrow> False"
    by (metis cblinfun.zero_left one_cblinfun.rep_eq one_dim_iso_of_zero' zero_neq_neg_one)
  thus "is_ortho_set (set ?basis)"
    unfolding is_ortho_set_def canonical_basis_cblinfun_def by auto
  show "A div B = A * inverse B"
    by (simp add: divide_cblinfun_def)
  show "inverse (c *\<^sub>C 1) = (1::'a\<Rightarrow>\<^sub>C\<^sub>L'b) /\<^sub>C c"
    apply transfer by (simp add: o_def one_dim_inverse)
qed
end

lemma id_cblinfun_eq_1[simp]: \<open>id_cblinfun = 1\<close>
  apply transfer by auto

(* Use id_cblinfun_eq_1 instead *)
(* lemma one_dim_id_cblinfun: "1 = id_cblinfun" *)

(* Renamed from one_dim_times[symmetric] *)
lemma one_dim_apply_is_times[simp]: 
  fixes A :: "'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L 'a" and B :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'a"
  shows "A o\<^sub>C\<^sub>L B = A * B"
  apply transfer by simp

(* lemmas one_dim_apply_is_times_complex[simp] = one_dim_apply_is_times[where 'a=complex] *)

lemma one_comp_one_cblinfun[simp]: "1 o\<^sub>C\<^sub>L 1 = 1"
  apply transfer unfolding o_def by simp

lemma one_cblinfun_adj[simp]: "1* = 1"
  apply transfer by simp 

(* Renamed from one_vector_to_cblinfun *)
lemma vector_to_cblinfun_comp_one[simp]: 
  "(vector_to_cblinfun s :: 'a::one_dim \<Rightarrow>\<^sub>C\<^sub>L _) o\<^sub>C\<^sub>L 1 
     = (vector_to_cblinfun s :: 'b::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)"
  apply (transfer fixing: s)
  by fastforce

(* Use norm_cblinfun_compose instead *)
(* lemma norm_cblinfun_times: "norm (A o\<^sub>C\<^sub>L B) \<le> norm A * norm B" *)

(* Use cblinfun_eqI instead *)
(* lemma cblinfun_ext: 
  includes cblinfun_notation
  assumes "\<And>x::'a::chilbert_space. A *\<^sub>V x = B *\<^sub>V x"
  shows "A = B"  *)

(* Renamed from eigenspace_memberE *)
lemma eigenspace_memberD:
  assumes "x \<in> space_as_set (eigenspace e A)"
  shows "A *\<^sub>V x = e *\<^sub>C x"
  using assms unfolding eigenspace_def apply transfer by auto

(* Renamed from kernel_memberE *)
lemma kernel_memberD:
  assumes "x \<in> space_as_set (kernel A)"
  shows "A *\<^sub>V x = 0"
  using assms apply transfer by auto

lemma eigenspace_memberI:
  assumes "A *\<^sub>V x = e *\<^sub>C x"
  shows "x \<in> space_as_set (eigenspace e A)"
  using assms unfolding eigenspace_def apply transfer by auto

lemma kernel_memberI:
  assumes "A *\<^sub>V x = 0"
  shows "x \<in> space_as_set (kernel A)"
  using assms apply transfer by auto

(* TODO rename *)
lemma cblinfun_image_Span: 
  shows "A *\<^sub>S ccspan G = ccspan ((*\<^sub>V) A ` G)"
  apply transfer
  by (simp add: bounded_clinear.bounded_linear bounded_clinear_def closure_bounded_linear_image_subset_eq complex_vector.linear_span_image)

(* Renamed from span_ortho_span *)
lemma ccspan_leq_ortho_ccspan:
  assumes "\<And>s t. s\<in>S \<Longrightarrow> t\<in>T \<Longrightarrow> is_orthogonal s t"
  shows "ccspan S \<le> - (ccspan T)"
  using assms apply transfer
  by (smt (verit, ccfv_threshold) is_orthogonal_closure is_orthogonal_cspan is_orthogonal_sym orthogonal_complementI subsetI) 

(* definition "positive_op A = (\<exists>B::'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L'a. A = B* o\<^sub>C\<^sub>L B)" *)

(* Use cblinfun_compose_zero_left instead *)
(* lemma cblinfun_compose0[simp]: "0 o\<^sub>C\<^sub>L A = 0" *)

(* Use cblinfun_compose_zero_right instead *)
(* lemma cblinfun_compose0'[simp]: "A o\<^sub>C\<^sub>L 0 = 0" *)

(* lemma positive_id_cblinfun[simp]: "positive_op id_cblinfun"
  unfolding positive_op_def apply (rule exI[of _ id_cblinfun]) by simp *)

(* lemma positive_0[simp]: "positive_op 0"
  unfolding positive_op_def apply (rule exI[of _ 0]) by auto *)






(* Use norm_cblinfun_compose instead *)
(* lemma norm_mult_ineq_cblinfun:
  fixes A B
  shows "norm (A o\<^sub>C\<^sub>L B) \<le> norm A * norm B" *)

(* TODO name those *)
lemma scaleC_1_right[simp]: \<open>scaleC x (1::'a::one_dim) = of_complex x\<close>
  unfolding of_complex_def by simp

lemma scaleC_1_left[simp]: \<open>scaleC x (of_complex y) = of_complex (x * y)\<close>
  unfolding of_complex_def using scaleC_scaleC by blast

lemma scaleC_1_apply[simp]: \<open>x *\<^sub>C 1 *\<^sub>V y = x *\<^sub>C y\<close>
  by (metis cblinfun.scaleC_left cblinfun_id_cblinfun_apply id_cblinfun_eq_1)

lemma cblinfun_apply_1_left[simp]: \<open>1 *\<^sub>V y = y\<close>
  by (metis cblinfun_id_cblinfun_apply id_cblinfun_eq_1)

lemma of_complex_cblinfun_apply[simp]: \<open>of_complex x *\<^sub>V y = x *\<^sub>C y\<close>
  unfolding of_complex_def
  by (metis cblinfun.scaleC_left cblinfun_id_cblinfun_apply id_cblinfun_eq_1)

declare scaleC_conv_of_complex[simp]

(* Renamed from vector_to_cblinfun_adj_applytor_to_cblinfun *)
lemma vector_to_cblinfun_adj_comp_vector_to_cblinfun[simp]:
  shows "vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi> = cinner \<psi> \<phi> *\<^sub>C id_cblinfun"
proof -
  have "one_dim_iso \<gamma> *\<^sub>C one_dim_iso (of_complex \<langle>\<psi>, \<phi>\<rangle>) =
    \<langle>\<psi>, \<phi>\<rangle> *\<^sub>C one_dim_iso \<gamma>"
    for \<gamma> :: "'c::one_dim"      
    by (metis complex_vector.scale_left_commute of_complex_def one_dim_iso_of_one one_dim_iso_scaleC one_dim_scaleC_1)
  hence "one_dim_iso ((vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>) *\<^sub>V \<gamma>)
      = one_dim_iso ((cinner \<psi> \<phi> *\<^sub>C id_cblinfun) *\<^sub>V \<gamma>)" 
    for \<gamma> :: "'c::one_dim"
    by simp
  hence "((vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>) *\<^sub>V \<gamma>) = ((cinner \<psi> \<phi> *\<^sub>C id_cblinfun) *\<^sub>V \<gamma>)" 
    for \<gamma> :: "'c::one_dim"
    by (rule one_dim_iso_inj)
  thus ?thesis
    using cblinfun_eqI[where x = "vector_to_cblinfun \<psi>* o\<^sub>C\<^sub>L vector_to_cblinfun \<phi>"
        and y = "\<langle>\<psi>, \<phi>\<rangle> *\<^sub>C id_cblinfun"]
    by auto
qed


lemma scaleC_cindependent:
  assumes a1: "cindependent (B::'a::complex_vector set)" and a3: "c \<noteq> 0"
  shows "cindependent ((*\<^sub>C) c ` B)"
proof-
  have "u y = 0"
    if g1: "y\<in>S" and g2: "(\<Sum>x\<in>S. u x *\<^sub>C x) = 0" and g3: "finite S" and g4: "S\<subseteq>(*\<^sub>C) c ` B"
    for u y S
  proof-
    define v where "v x = u (c *\<^sub>C x)" for x
    obtain S' where "S'\<subseteq>B" and S_S': "S = (*\<^sub>C) c ` S'"
      by (meson g4 subset_imageE)      
    have "inj ((*\<^sub>C) c::'a\<Rightarrow>_)"
      unfolding inj_def
      using a3 by auto 
    hence "finite S'"
      using S_S' finite_imageD g3 subset_inj_on by blast            
    have "t \<in> (*\<^sub>C) (inverse c) ` S"
      if "t \<in> S'" for t
    proof-
      have "c *\<^sub>C t \<in> S"
        using \<open>S = (*\<^sub>C) c ` S'\<close> that by blast
      hence "(inverse c) *\<^sub>C (c *\<^sub>C t) \<in> (*\<^sub>C) (inverse c) ` S"
        by blast
      moreover have "(inverse c) *\<^sub>C (c *\<^sub>C t) = t"
        by (simp add: a3)
      ultimately show ?thesis by simp
    qed
    moreover have "t \<in> S'"
      if "t \<in> (*\<^sub>C) (inverse c) ` S" for t
    proof-
      obtain t' where "t = (inverse c) *\<^sub>C t'" and "t' \<in> S"
        using \<open>t \<in> (*\<^sub>C) (inverse c) ` S\<close> by auto
      have "c *\<^sub>C t = c *\<^sub>C ((inverse c) *\<^sub>C t')"
        using \<open>t = (inverse c) *\<^sub>C t'\<close> by simp
      also have "\<dots> = (c * (inverse c)) *\<^sub>C t'"
        by simp
      also have "\<dots> = t'"
        by (simp add: a3)
      finally have "c *\<^sub>C t = t'".
      thus ?thesis using \<open>t' \<in> S\<close>
        using \<open>S = (*\<^sub>C) c ` S'\<close> a3 complex_vector.scale_left_imp_eq by blast 
    qed
    ultimately have "S' = (*\<^sub>C) (inverse c) ` S"
      by blast 
    hence "inverse c *\<^sub>C y \<in> S'"
      using that(1) by blast 
    have t: "inj (((*\<^sub>C) c)::'a \<Rightarrow> _)"
      using a3 complex_vector.injective_scale[where c = c]
      by blast
    have "0 = (\<Sum>x\<in>(*\<^sub>C) c ` S'. u x *\<^sub>C x)"
      using \<open>S = (*\<^sub>C) c ` S'\<close> that(2) by auto
    also have "\<dots> = (\<Sum>x\<in>S'. v x *\<^sub>C (c *\<^sub>C x))"
      unfolding v_def
      using t Groups_Big.comm_monoid_add_class.sum.reindex[where h = "((*\<^sub>C) c)" and A = S' 
          and g = "\<lambda>x. u x *\<^sub>C x"] subset_inj_on by auto     
    also have "\<dots> = c *\<^sub>C (\<Sum>x\<in>S'. v x *\<^sub>C x)"
      by (metis (mono_tags, lifting) complex_vector.scale_left_commute scaleC_right.sum sum.cong)
    finally have "0 = c *\<^sub>C (\<Sum>x\<in>S'. v x *\<^sub>C x)".
    hence "(\<Sum>x\<in>S'. v x *\<^sub>C x) = 0"
      using a3 by auto
    hence "v (inverse c *\<^sub>C y) = 0"
      using \<open>inverse c *\<^sub>C y \<in> S'\<close> \<open>finite S'\<close> \<open>S' \<subseteq> B\<close> a1
        complex_vector.independentD
      by blast 
    thus "u y = 0"
      unfolding v_def
      by (simp add: a3) 
  qed
  thus ?thesis
    using complex_vector.dependent_explicit
    by (simp add: complex_vector.dependent_explicit ) 
qed



(* lemma complex_span_eq_scaleC:
  "complex_vector.span (B \<union> ( *\<^sub>C) c ` B) = complex_vector.span B"
  by (metis (no_types, hide_lams) complex_vector.span_base complex_vector.span_minimal complex_vector.span_superset complex_vector.subspace_def complex_vector.subspace_span dual_order.antisym image_subset_iff sup.bounded_iff) *)

(* lemma sum_3_sets:
  assumes "finite A" and "finite B" and "finite C"
    and "A \<inter> B = {}" and "A \<inter> C = {}" and "B \<inter> C = {}"
  shows "sum f (A \<union> B \<union> C) = sum f A + sum f B + sum f C" *)


(* Renamed from cblinfun_operator_S_zero_uniq_span *)
lemma cblinfun_eq_0_on_span:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes "x \<in> cspan S"
    and "\<And>s. s\<in>S \<Longrightarrow> F *\<^sub>V s = 0"
  shows \<open>F *\<^sub>V x = 0\<close>
  apply (rule complex_vector.linear_eq_0_on_span[where f=F])
  using bounded_clinear.axioms(1) cblinfun_apply assms by auto

(* Renamed from cblinfun_operator_S_uniq_span *)
lemma cblinfun_eq_on_span:
  fixes S::\<open>'a::complex_normed_vector set\<close>
  assumes "x \<in> cspan S"
    and "\<And>s. s\<in>S \<Longrightarrow> F *\<^sub>V s = G *\<^sub>V s"
  shows \<open>F *\<^sub>V x = G *\<^sub>V x\<close>
  apply (rule complex_vector.linear_eq_on_span[where f=F])
  using bounded_clinear.axioms(1) cblinfun_apply assms by auto


(* Renamed from cblinfun_operator_basis_zero_uniq *)
lemma cblinfun_eq_0_on_UNIV_span:
  fixes basis::\<open>'a::complex_normed_vector set\<close>
  assumes "cspan basis = UNIV"
    and "\<And>s. s\<in>basis \<Longrightarrow> F *\<^sub>V s = 0"
  shows \<open>F = 0\<close>
  by (metis cblinfun_eq_0_on_span UNIV_I assms cblinfun.zero_left cblinfun_eqI)

(* (* Is duplicate *)
lemma is_ortho_set_cindependent:
  assumes a1: "is_ortho_set A"
  shows "cindependent A"
proof-
  have "finite t \<Longrightarrow> t \<subseteq> A \<Longrightarrow> (\<Sum>v\<in>t. u v *\<^sub>C v) = 0 \<Longrightarrow> v \<in> t \<Longrightarrow> u v = 0"
    for t u v
  proof-
    assume b1: "finite t" and b2: "t \<subseteq> A" and b3: "(\<Sum>v\<in>t. u v *\<^sub>C v) = 0" and b4: "v \<in> t"
    have "v'\<in>t-{v} \<Longrightarrow> \<langle>v, v'\<rangle> = 0" for v'
    proof-
      assume "v'\<in>t-{v}"
      hence "v \<noteq> v'" by blast
      thus ?thesis using a1
        by (meson DiffD1 \<open>v' \<in> t - {v}\<close> b2 b4 is_ortho_set_def subsetD)         
    qed
    hence sum0: "(\<Sum>v'\<in>t-{v}. u v' * \<langle>v, v'\<rangle>) = 0"
      by simp

    have v1: "v \<in> A"
      using b2 b4 by blast        
    hence "v \<noteq> 0"
      using a1 unfolding is_ortho_set_def
      by blast

    have "\<langle>v, (\<Sum>v'\<in>t. u v' *\<^sub>C v')\<rangle> = (\<Sum>v'\<in>t. u v' * \<langle>v, v'\<rangle>)"
      using b1
      by (metis (mono_tags, lifting) cinner_scaleC_right cinner_sum_right sum.cong) 
    also have "\<dots> = u v * \<langle>v, v\<rangle> + (\<Sum>v'\<in>t-{v}. u v' * \<langle>v, v'\<rangle>)"
      by (meson b1 b4 sum.remove)
    also have "\<dots> = u v * \<langle>v, v\<rangle>"
      using sum0 by simp
    finally have "\<langle>v, (\<Sum>v'\<in>t. u v' *\<^sub>C v')\<rangle> =  u v * \<langle>v, v\<rangle>"
      by blast
    hence "u v * \<langle>v, v\<rangle> = 0" using b3 by simp
    moreover have "\<langle>v, v\<rangle> \<noteq> 0"
      using v1
      by (simp add: \<open>v \<noteq> 0\<close>)  
    ultimately show "u v = 0" by simp
  qed
  thus ?thesis using complex_vector.independent_explicit_module
    by smt    
qed *)


(* Use bounded_clinear_finite_dim instead *)
(* lemma cblinfun_operator_finite_dim:
  fixes  F::"'a::{complex_normed_vector,cfinite_dim} \<Rightarrow> 'b::complex_normed_vector" 
    and basis::"'a set"
  assumes b1: "complex_vector.span basis = UNIV"
    and b2: "cindependent basis"
    and b3:"finite basis" 
    and b5:"clinear F"
  shows "bounded_clinear F" *)


(* Renamed from cblinfun_operator_basis_existence_uniq *)
lemma cblinfun_eq_on_UNIV_span:
  fixes basis::"'a::complex_normed_vector set" and \<phi>::"'a \<Rightarrow> 'b::complex_normed_vector" (* complex_normed_vector *)
  assumes "cspan basis = UNIV"
    and "\<And>s. s\<in>basis \<Longrightarrow> F *\<^sub>V s = G *\<^sub>V s"
  shows \<open>F = G\<close>
proof-
  have "F - G = 0"
    apply (rule cblinfun_eq_0_on_UNIV_span[where basis=basis])
    using assms by (auto simp add: cblinfun.diff_left)
  thus ?thesis by simp
qed


(* Renamed from obn_enum_uniq *)
lemma cblinfun_eq_on_canonical_basis:
  fixes f g::"'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector"
  defines "basis == set (canonical_basis::'a list)"
  assumes "\<And>u. u \<in> basis \<Longrightarrow> f *\<^sub>V u = g *\<^sub>V u"
  shows  "f = g" 
  apply (rule cblinfun_eq_on_UNIV_span[where basis=basis])
  using assms is_generator_set is_cindependent_set by auto

lemma cblinfun_eq_0_on_canonical_basis:
  fixes f ::"'a::{basis_enum,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector"
  defines "basis == set (canonical_basis::'a list)"
  assumes "\<And>u. u \<in> basis \<Longrightarrow> f *\<^sub>V u = 0"
  shows  "f = 0"
  by (simp add: assms cblinfun_eq_on_canonical_basis)

(* Renamed from cinner_canonical_basis_eq_zero *)
lemma cinner_canonical_basis_eq_0:
  defines "basisA == set (canonical_basis::'a::onb_enum list)"
    and   "basisB == set (canonical_basis::'b::onb_enum list)"
  assumes "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> \<langle>v, F *\<^sub>V u\<rangle> = 0"
  shows "F = 0"
proof-
  have "F *\<^sub>V u = 0"
    if "u\<in>basisA" for u
  proof-
    have "\<And>v. v\<in>basisB \<Longrightarrow> \<langle>v, F *\<^sub>V u\<rangle> = 0"
      by (simp add: assms(3) that)
    moreover have "(\<And>v. v\<in>basisB \<Longrightarrow> \<langle>v, x\<rangle> = 0) \<Longrightarrow> x = 0"
      for x
    proof-     
      assume r1: "\<And>v. v\<in>basisB \<Longrightarrow> \<langle>v, x\<rangle> = 0"      
      have "\<langle>v, x\<rangle> = 0" for v
      proof-
        have "cspan basisB = UNIV"
          using basisB_def is_generator_set  by auto 
        hence "v \<in> cspan basisB"
          by (smt iso_tuple_UNIV_I)
        hence "\<exists>t s. v = (\<Sum>a\<in>t. s a *\<^sub>C a) \<and> finite t \<and> t \<subseteq> basisB"
          using complex_vector.span_explicit
          by (smt mem_Collect_eq)
        then obtain t s where b1: "v = (\<Sum>a\<in>t. s a *\<^sub>C a)" and b2: "finite t" and b3: "t \<subseteq> basisB"
          by blast
        have "\<langle>v, x\<rangle> = \<langle>(\<Sum>a\<in>t. s a *\<^sub>C a), x\<rangle>"
          by (simp add: b1)
        also have "\<dots> = (\<Sum>a\<in>t. \<langle>s a *\<^sub>C a, x\<rangle>)"
          using cinner_sum_left by blast
        also have "\<dots> = (\<Sum>a\<in>t. cnj (s a) * \<langle>a, x\<rangle>)"
          by auto
        also have "\<dots> = 0"
          using b3 r1 subsetD by force
        finally show ?thesis by simp
      qed
      thus ?thesis
        by (simp add: \<open>\<And>v. \<langle>v, x\<rangle> = 0\<close> cinner_extensionality) 
    qed
    ultimately show ?thesis by simp
  qed
  thus ?thesis
    using basisA_def cblinfun_eq_0_on_canonical_basis by auto 
qed


(* Renamed from cinner_unique_onb_enum *)
lemma cinner_canonical_basis_eq:
  defines "basisA == set (canonical_basis::'a::onb_enum list)"
    and   "basisB == set (canonical_basis::'b::onb_enum list)"
  assumes "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> \<langle>v, F *\<^sub>V u\<rangle> = \<langle>v, G *\<^sub>V u\<rangle>"
  shows "F = G"
proof-
  define H where "H = F - G"
  have "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> \<langle>v, H *\<^sub>V u\<rangle> = 0"
    unfolding H_def
    by (simp add: assms(3) cinner_diff_right minus_cblinfun.rep_eq) 
  hence "H = 0"
    by (simp add: basisA_def basisB_def cinner_canonical_basis_eq_0)    
  thus ?thesis unfolding H_def by simp
qed

lemma cinner_canonical_basis_eq':
  defines "basisA == set (canonical_basis::'a::onb_enum list)"
    and   "basisB == set (canonical_basis::'b::onb_enum list)"
  assumes "\<And>u v. u\<in>basisA \<Longrightarrow> v\<in>basisB \<Longrightarrow> \<langle>F *\<^sub>V u, v\<rangle> = \<langle>G *\<^sub>V u, v\<rangle>"
  shows "F = G"
  using cinner_canonical_basis_eq assms
  by (metis cinner_commute')

subsection \<open>Extension of complex bounded operators\<close>

definition cblinfun_extension where 
  "cblinfun_extension S \<phi> = (SOME B. \<forall>x\<in>S. B *\<^sub>V x = \<phi> x)"

definition cblinfun_extension_exists where 
  "cblinfun_extension_exists S \<phi> = (\<exists>B. \<forall>x\<in>S. B *\<^sub>V x = \<phi> x)"

lemma cblinfun_extension_existsI:
  assumes "\<And>x. x\<in>S \<Longrightarrow> B *\<^sub>V x = \<phi> x"
  shows "cblinfun_extension_exists S \<phi>"
  using assms cblinfun_extension_exists_def by blast

(* Use cindependent_cfinite_dim_finite instead *)
(* lemma cindependent_finite_onb_enum:
  assumes a1: "cindependent A"
  shows "finite (A::'a::onb_enum set)" *)

(* Renamed from cblinfun_extension_exists_finite *)
lemma cblinfun_extension_exists_finite_dim:
  fixes \<phi>::"'a::{complex_normed_vector,cfinite_dim} \<Rightarrow> 'b::complex_normed_vector" 
  assumes "cindependent S"
    and "cspan S = UNIV"
  shows "cblinfun_extension_exists S \<phi>"
proof-
  define f::"'a \<Rightarrow> 'b"
    where "f = complex_vector.construct S \<phi>"
  have "clinear f"
    by (simp add: complex_vector.linear_construct assms linear_construct f_def) 
  have "bounded_clinear f"
    using \<open>clinear f\<close> assms by auto    
  then obtain B::"'a \<Rightarrow>\<^sub>C\<^sub>L 'b" 
    where "B *\<^sub>V x = f x" for x
    using cblinfun_apply_cases by blast
  have "B *\<^sub>V x = \<phi> x"
    if c1: "x\<in>S"
    for x
  proof-
    have "B *\<^sub>V x = f x"
      by (simp add: \<open>\<And>x. B *\<^sub>V x = f x\<close>)
    also have "\<dots> = \<phi> x"
      using assms complex_vector.construct_basis f_def that
      by (simp add: complex_vector.construct_basis) 
    finally show?thesis by blast
  qed
  thus ?thesis 
    unfolding cblinfun_extension_exists_def
    by blast
qed

lemma cblinfun_extension_exists_bounded_dense:
  fixes f :: \<open>'a::complex_normed_vector \<Rightarrow> 'b::cbanach\<close>
  assumes \<open>csubspace S\<close>
  assumes \<open>closure S = UNIV\<close>
  assumes f_add: \<open>\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> f (x + y) = f x + f y\<close>
  assumes f_scale: \<open>\<And>c x y. x \<in> S \<Longrightarrow> f (c *\<^sub>C x) = c *\<^sub>C f x\<close>
  assumes bounded: \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> B * norm x\<close>
  shows \<open>cblinfun_extension_exists S f\<close>
proof -
  obtain B where bounded: \<open>\<And>x. x \<in> S \<Longrightarrow> norm (f x) \<le> B * norm x\<close> and \<open>B > 0\<close>
    using bounded by (smt (z3) mult_mono norm_ge_zero)  
  have \<open>\<exists>xi. (xi \<longlonglongrightarrow> x) \<and> (\<forall>i. xi i \<in> S)\<close> for x
    using assms(2) closure_sequential by blast
  then obtain seq :: \<open>'a \<Rightarrow> nat \<Rightarrow> 'a\<close> where seq_lim: \<open>seq x \<longlonglongrightarrow> x\<close> and seq_S: \<open>seq x i \<in> S\<close> for x i
    apply (atomize_elim, subst all_conj_distrib[symmetric])
    apply (rule choice)
    by auto
  define g where \<open>g x = lim (\<lambda>i. f (seq x i))\<close> for x
  have \<open>Cauchy (\<lambda>i. f (seq x i))\<close> for x
  proof (rule CauchyI)
    fix e :: real assume \<open>e > 0\<close>
    have \<open>Cauchy (seq x)\<close>
      using LIMSEQ_imp_Cauchy seq_lim by blast
    then obtain M where less_eB: \<open>norm (seq x m - seq x n) < e/B\<close> if \<open>n \<ge> M\<close> and \<open>m \<ge> M\<close> for n m
      apply atomize_elim by (meson CauchyD \<open>0 < B\<close> \<open>0 < e\<close> linordered_field_class.divide_pos_pos)
    have \<open>norm (f (seq x m) - f (seq x n)) < e\<close> if \<open>n \<ge> M\<close> and \<open>m \<ge> M\<close> for n m
    proof -
      have \<open>norm (f (seq x m) - f (seq x n)) = norm (f (seq x m - seq x n))\<close>
        using f_add f_scale seq_S
        by (metis add_diff_cancel assms(1) complex_vector.subspace_diff diff_add_cancel) 
      also have \<open>\<dots> \<le> B * norm (seq x m - seq x n)\<close>
        apply (rule bounded)
        by (simp add: assms(1) complex_vector.subspace_diff seq_S)
      also from less_eB have \<open>\<dots> < B * (e/B)\<close>
        by (meson \<open>0 < B\<close> linordered_semiring_strict_class.mult_strict_left_mono that)
      also have \<open>\<dots> \<le> e\<close>
        using \<open>0 < B\<close> by auto
      finally show ?thesis
        by -
    qed
    then show \<open>\<exists>M. \<forall>m\<ge>M. \<forall>n\<ge>M. norm (f (seq x m) - f (seq x n)) < e\<close>
      by auto
  qed
  then have f_seq_lim: \<open>(\<lambda>i. f (seq x i)) \<longlonglongrightarrow> g x\<close> for x
    by (simp add: Cauchy_convergent_iff convergent_LIMSEQ_iff g_def)
  have f_xi_lim: \<open>(\<lambda>i. f (xi i)) \<longlonglongrightarrow> g x\<close> if \<open>xi \<longlonglongrightarrow> x\<close> and \<open>\<And>i. xi i \<in> S\<close> for xi x
  proof -
    from seq_lim that
    have \<open>(\<lambda>i. B * norm (xi i - seq x i)) \<longlonglongrightarrow> 0\<close>
      by (metis (no_types) \<open>0 < B\<close> cancel_comm_monoid_add_class.diff_cancel norm_not_less_zero norm_zero tendsto_diff tendsto_norm_zero_iff tendsto_zero_mult_left_iff)
    then have \<open>(\<lambda>i. f (xi i + (-1) *\<^sub>C seq x i)) \<longlonglongrightarrow> 0\<close>
      apply (rule Lim_null_comparison[rotated])
      using bounded by (simp add: assms(1) complex_vector.subspace_diff seq_S that(2))
    then have \<open>(\<lambda>i. f (xi i) - f (seq x i)) \<longlonglongrightarrow> 0\<close>
      apply (subst (asm) f_add)
        apply (auto simp: that \<open>csubspace S\<close> complex_vector.subspace_neg seq_S)[2]
      apply (subst (asm) f_scale)
      by (auto simp: that \<open>csubspace S\<close> complex_vector.subspace_neg seq_S)
    then show \<open>(\<lambda>i. f (xi i)) \<longlonglongrightarrow> g x\<close>
      using Lim_transform f_seq_lim by fastforce
  qed
  have g_add: \<open>g (x + y) = g x + g y\<close> for x y
  proof -
    obtain xi :: \<open>nat \<Rightarrow> 'a\<close> where \<open>xi \<longlonglongrightarrow> x\<close> and \<open>xi i \<in> S\<close> for i
      using seq_S seq_lim by auto
    obtain yi :: \<open>nat \<Rightarrow> 'a\<close> where \<open>yi \<longlonglongrightarrow> y\<close> and \<open>yi i \<in> S\<close> for i
      using seq_S seq_lim by auto
    have \<open>(\<lambda>i. xi i + yi i) \<longlonglongrightarrow> x + y\<close>
      using \<open>xi \<longlonglongrightarrow> x\<close> \<open>yi \<longlonglongrightarrow> y\<close> tendsto_add by blast
    then have lim1: \<open>(\<lambda>i. f (xi i + yi i)) \<longlonglongrightarrow> g (x + y)\<close>
      by (simp add: \<open>\<And>i. xi i \<in> S\<close> \<open>\<And>i. yi i \<in> S\<close> assms(1) complex_vector.subspace_add f_xi_lim)
    have \<open>(\<lambda>i. f (xi i + yi i)) = (\<lambda>i. f (xi i) + f (yi i))\<close>
      by (simp add: \<open>\<And>i. xi i \<in> S\<close> \<open>\<And>i. yi i \<in> S\<close> f_add)
    also have \<open>\<dots> \<longlonglongrightarrow> g x + g y\<close>
      by (simp add: \<open>\<And>i. xi i \<in> S\<close> \<open>\<And>i. yi i \<in> S\<close> \<open>xi \<longlonglongrightarrow> x\<close> \<open>yi \<longlonglongrightarrow> y\<close> f_xi_lim tendsto_add)
    finally show ?thesis
      using lim1 LIMSEQ_unique by blast
  qed
  have g_scale: \<open>g (c *\<^sub>C x) = c *\<^sub>C g x\<close> for c x
  proof -
    obtain xi :: \<open>nat \<Rightarrow> 'a\<close> where \<open>xi \<longlonglongrightarrow> x\<close> and \<open>xi i \<in> S\<close> for i
      using seq_S seq_lim by auto
    have \<open>(\<lambda>i. c *\<^sub>C xi i) \<longlonglongrightarrow> c *\<^sub>C x\<close>
      using \<open>xi \<longlonglongrightarrow> x\<close> bounded_clinear_scaleC_right clinear_continuous_at isCont_tendsto_compose by blast
    then have lim1: \<open>(\<lambda>i. f (c *\<^sub>C xi i)) \<longlonglongrightarrow> g (c *\<^sub>C x)\<close>
      by (simp add: \<open>\<And>i. xi i \<in> S\<close> assms(1) complex_vector.subspace_scale f_xi_lim)
    have \<open>(\<lambda>i. f (c *\<^sub>C xi i)) = (\<lambda>i. c *\<^sub>C f (xi i))\<close>
      by (simp add: \<open>\<And>i. xi i \<in> S\<close> f_scale)
    also have \<open>\<dots> \<longlonglongrightarrow> c *\<^sub>C g x\<close>
      using \<open>\<And>i. xi i \<in> S\<close> \<open>xi \<longlonglongrightarrow> x\<close> bounded_clinear_scaleC_right clinear_continuous_at f_xi_lim isCont_tendsto_compose by blast
    finally show ?thesis
      using lim1 LIMSEQ_unique by blast
  qed

  have [simp]: \<open>f x = g x\<close> if \<open>x \<in> S\<close> for x
  proof -
    have \<open>(\<lambda>_. x) \<longlonglongrightarrow> x\<close>
      by auto
    then have \<open>(\<lambda>_. f x) \<longlonglongrightarrow> g x\<close>
      using that by (rule f_xi_lim)
    then show \<open>f x = g x\<close>
      by (simp add: LIMSEQ_const_iff)
  qed

  have g_bounded: \<open>norm (g x) \<le> B * norm x\<close> for x
  proof -
    obtain xi :: \<open>nat \<Rightarrow> 'a\<close> where \<open>xi \<longlonglongrightarrow> x\<close> and \<open>xi i \<in> S\<close> for i
      using seq_S seq_lim by auto
    then have \<open>(\<lambda>i. f (xi i)) \<longlonglongrightarrow> g x\<close>
      using f_xi_lim by presburger
    then have \<open>(\<lambda>i. norm (f (xi i))) \<longlonglongrightarrow> norm (g x)\<close>
      by (metis tendsto_norm)
    moreover have \<open>(\<lambda>i. B * norm (xi i)) \<longlonglongrightarrow> B * norm x\<close>
      by (simp add: \<open>xi \<longlonglongrightarrow> x\<close> tendsto_mult_left tendsto_norm)
    ultimately show \<open>norm (g x) \<le> B * norm x\<close>
      apply (rule lim_mono[rotated])
      using bounded using \<open>xi _ \<in> S\<close> by blast 
  qed

  have \<open>bounded_clinear g\<close>
    using g_add g_scale apply (rule bounded_clinearI[where K=B])
    using g_bounded by (simp add: ordered_field_class.sign_simps(5))
  then have [simp]: \<open>cBlinfun g *\<^sub>V x = g x\<close> for x
    by (subst cBlinfun_inverse, auto)

  show \<open>cblinfun_extension_exists S f\<close>
    apply (rule cblinfun_extension_existsI[where B=\<open>cBlinfun g\<close>])
    by auto
qed

(* Renamed from cblinfun_extension_exists *)
lemma cblinfun_extension_apply:
  assumes "cblinfun_extension_exists S f"
    and "v \<in> S"
  shows "(cblinfun_extension S f) *\<^sub>V v = f v"
  by (smt assms cblinfun_extension_def cblinfun_extension_exists_def tfl_some)

subsection \<open>Unsorted\<close>

(* TODO sort this into the right sections *)

(* Use cblinfun.zero_right instead *)
(* lemma cblinfun_apply_to_zero[simp]: "A *\<^sub>V 0 = 0" *)

(* Use Proj_orthog_ccspan_union instead *)
(* lemma Proj_Span_insert:
  fixes S :: "'a::{onb_enum, chilbert_space} list"
    and a::'a 
  assumes a1: "is_ortho_set (set (a#S))" and a2: "distinct (a#S)"
  shows "Proj (ccspan (set (a#S))) = Proj (ccspan {a}) + Proj (ccspan (set S))" *)

(* Renamed from butterfly_def' *)
definition butterfly_def: "butterfly (s::'a::complex_normed_vector) (t::'b::chilbert_space)
   = vector_to_cblinfun s o\<^sub>C\<^sub>L (vector_to_cblinfun t :: complex \<Rightarrow>\<^sub>C\<^sub>L _)*"

abbreviation "selfbutter s \<equiv> butterfly s s"

lemma butterfly_add_left: \<open>butterfly (a + a') b = butterfly a b + butterfly a' b\<close>
  by (simp add: butterfly_def vector_to_cblinfun_add cbilinear_add_left bounded_cbilinear.add_left bounded_cbilinear_cblinfun_compose)

lemma butterfly_add_right: \<open>butterfly a (b + b') = butterfly a b + butterfly a b'\<close>
  by (simp add: butterfly_def adj_plus vector_to_cblinfun_add cblinfun_compose_add_right)

(* Renamed from butterfly_def *)
lemma butterfly_def_one_dim: "butterfly s t = (vector_to_cblinfun s :: 'c::one_dim \<Rightarrow>\<^sub>C\<^sub>L _)
                                          o\<^sub>C\<^sub>L (vector_to_cblinfun t :: 'c \<Rightarrow>\<^sub>C\<^sub>L _)*"
  (is "_ = ?rhs") for s :: "'a::complex_normed_vector" and t :: "'b::chilbert_space"
proof -
  let ?isoAC = "1 :: 'c \<Rightarrow>\<^sub>C\<^sub>L complex"
  let ?isoCA = "1 :: complex \<Rightarrow>\<^sub>C\<^sub>L 'c"
  let ?vector = "vector_to_cblinfun :: _ \<Rightarrow> ('c \<Rightarrow>\<^sub>C\<^sub>L _)"

  have "butterfly s t =
    (?vector s o\<^sub>C\<^sub>L ?isoCA) o\<^sub>C\<^sub>L (?vector t o\<^sub>C\<^sub>L ?isoCA)*"
    unfolding butterfly_def vector_to_cblinfun_comp_one by simp
  also have "\<dots> = ?vector s o\<^sub>C\<^sub>L (?isoCA o\<^sub>C\<^sub>L ?isoCA*) o\<^sub>C\<^sub>L (?vector t)*"
    by (metis (no_types, lifting) cblinfun_compose_assoc adj_cblinfun_compose)
  also have "\<dots> = ?rhs"
    by simp
  finally show ?thesis
    by simp
qed


(* Renamed from butterfly_comp_butterfly_right *)
lemma butterfly_comp_cblinfun: "butterfly \<psi> \<phi> o\<^sub>C\<^sub>L a = butterfly \<psi> (a* *\<^sub>V \<phi>)"
  unfolding butterfly_def
  by (simp add: cblinfun_compose_assoc vector_to_cblinfun_applyOp)  

lemma cblinfun_comp_butterfly: "a o\<^sub>C\<^sub>L butterfly \<psi> \<phi> = butterfly (a *\<^sub>V \<psi>) \<phi>"
  unfolding butterfly_def
  by (simp add: cblinfun_compose_assoc vector_to_cblinfun_applyOp)  

lemma butterfly_apply[simp]: "butterfly \<psi> \<psi>' *\<^sub>V \<phi> = \<langle>\<psi>', \<phi>\<rangle> *\<^sub>C \<psi>"
  by (simp add: butterfly_def scaleC_cblinfun.rep_eq)

(* Renamed from butterfly_scaleC1 *)
lemma butterfly_scaleC_left[simp]: "butterfly (c *\<^sub>C \<psi>) \<phi> = c *\<^sub>C butterfly \<psi> \<phi>"
  unfolding butterfly_def vector_to_cblinfun_scaleC scaleC_adj
  by (simp add: cnj_x_x)

(* Renamed from butterfly_scaleC2 *)
lemma butterfly_scaleC_right[simp]: "butterfly \<psi> (c *\<^sub>C \<phi>) = cnj c *\<^sub>C butterfly \<psi> \<phi>"
  unfolding butterfly_def vector_to_cblinfun_scaleC scaleC_adj
  by (simp add: cnj_x_x)

(* Renamed from butterfly_scaleR1 *)
lemma butterfly_scaleR_left[simp]: "butterfly (r *\<^sub>R \<psi>) \<phi> = r *\<^sub>C butterfly \<psi> \<phi>"
  by (simp add: scaleR_scaleC)

(* Renamed from butterfly_scaleR2 *)
lemma butterfly_scaleR_right[simp]: "butterfly \<psi> (r *\<^sub>R \<phi>) = r *\<^sub>C butterfly \<psi> \<phi>"
  by (simp add: butterfly_scaleC_right scaleR_scaleC)

lemma butterfly_adjoint[simp]: "(butterfly \<psi> \<phi>)* = butterfly \<phi> \<psi>"
  unfolding butterfly_def by auto

(* Renamed from butterfly_times *)
lemma butterfly_comp_butterfly[simp]: "butterfly \<psi>1 \<psi>2 o\<^sub>C\<^sub>L butterfly \<psi>3 \<psi>4 = \<langle>\<psi>2, \<psi>3\<rangle> *\<^sub>C butterfly \<psi>1 \<psi>4"
  by (simp add: butterfly_comp_cblinfun)

lemma vector_to_cblinfun_0[simp]: "vector_to_cblinfun 0 = 0"
  by (metis cblinfun.zero_left cblinfun_compose_zero_left vector_to_cblinfun_applyOp)

(* Renamed from butterfly_0 *)
lemma butterfly_0_left[simp]: "butterfly 0 a = 0"
  by (simp add: butterfly_def)

(* Renamed from butterfly_0' *)
lemma butterfly_0_right[simp]: "butterfly a 0 = 0"
  by (simp add: butterfly_def)

lemma norm_butterfly: "norm (butterfly \<psi> \<phi>) = norm \<psi> * norm \<phi>"
proof (cases "\<phi>=0")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis 
    unfolding norm_cblinfun.rep_eq
    thm onormI[OF _ False]
  proof (rule onormI[OF _ False])
    fix x 

    have "cmod \<langle>\<phi>, x\<rangle> * norm \<psi> \<le> norm \<psi> * norm \<phi> * norm x"
      by (metis ab_semigroup_mult_class.mult_ac(1) complex_inner_class.Cauchy_Schwarz_ineq2 mult.commute mult_left_mono norm_ge_zero)
    thus "norm (butterfly \<psi> \<phi> *\<^sub>V x) \<le> norm \<psi> * norm \<phi> * norm x"
      by (simp add: power2_eq_square)

    show "norm (butterfly \<psi> \<phi> *\<^sub>V \<phi>) = norm \<psi> * norm \<phi> * norm \<phi>"
      by (smt (z3) ab_semigroup_mult_class.mult_ac(1) butterfly_apply mult.commute norm_eq_sqrt_cinner norm_ge_zero norm_scaleC power2_eq_square real_sqrt_abs real_sqrt_eq_iff)
  qed
qed

lemma bounded_sesquilinear_butterfly[bounded_sesquilinear]: \<open>bounded_sesquilinear (\<lambda>(b::'b::chilbert_space) (a::'a::chilbert_space). butterfly a b)\<close>
proof standard
  fix a a' :: 'a and b b' :: 'b and r :: complex
  show \<open>butterfly (a + a') b = butterfly a b + butterfly a' b\<close>
    by (rule butterfly_add_left)
  show \<open>butterfly a (b + b') = butterfly a b + butterfly a b'\<close>  
    by (rule butterfly_add_right)
  show \<open>butterfly (r *\<^sub>C a) b = r *\<^sub>C butterfly a b\<close>
    by simp
  show \<open>butterfly a (r *\<^sub>C b) = cnj r *\<^sub>C butterfly a b\<close>
    by simp
  show \<open>\<exists>K. \<forall>b a. norm (butterfly a b) \<le> norm b * norm a * K \<close>
    apply (rule exI[of _ 1])
    by (simp add: norm_butterfly)
qed

(* Renamed from inj_selfbutter *)
lemma inj_selfbutter_upto_phase: 
  assumes "selfbutter x = selfbutter y"
  shows "\<exists>c. cmod c = 1 \<and> x = c *\<^sub>C y"
proof (cases "x = 0")
  case True
  from assms have "y = 0"
    using norm_butterfly
    by (metis True butterfly_0_left divisors_zero norm_eq_zero)
  with True show ?thesis
    using norm_one by fastforce
next
  case False
  define c where "c = \<langle>y, x\<rangle> / \<langle>x, x\<rangle>"
  have "\<langle>x, x\<rangle> *\<^sub>C x = selfbutter x *\<^sub>V x"
    by (simp add: butterfly_apply)
  also have "\<dots> = selfbutter y *\<^sub>V x"
    using assms by simp
  also have "\<dots> = \<langle>y, x\<rangle> *\<^sub>C y"
    by (simp add: butterfly_apply)
  finally have xcy: "x = c *\<^sub>C y"
    by (simp add: c_def ceq_vector_fraction_iff)
  have "cmod c * norm x = cmod c * norm y"
    using assms norm_butterfly
    by (smt (verit, ccfv_SIG) \<open>\<langle>x, x\<rangle> *\<^sub>C x = selfbutter x *\<^sub>V x\<close> \<open>selfbutter y *\<^sub>V x = \<langle>y, x\<rangle> *\<^sub>C y\<close> cinner_scaleC_right complex_vector.scale_left_commute complex_vector.scale_right_imp_eq mult_cancel_left norm_eq_sqrt_cinner norm_eq_zero scaleC_scaleC xcy)
  also have "cmod c * norm y = norm (c *\<^sub>C y)"
    by simp
  also have "\<dots> = norm x"
    unfolding xcy[symmetric] by simp
  finally have c: "cmod c = 1"
    by (simp add: False)
  from c xcy show ?thesis
    by auto
qed

lemma isometry_vector_to_cblinfun[simp]:
  assumes "norm x = 1"
  shows "isometry (vector_to_cblinfun x)"
  using assms cnorm_eq_1 isometry_def by force

lemma image_vector_to_cblinfun[simp]: "vector_to_cblinfun x *\<^sub>S top = ccspan {x}"
proof transfer
  show "closure (range (\<lambda>\<phi>::'b. one_dim_iso \<phi> *\<^sub>C x)) = closure (cspan {x})"
    for x :: 'a
  proof (rule arg_cong [where f = closure])
    have "k *\<^sub>C x \<in> range (\<lambda>\<phi>. one_dim_iso \<phi> *\<^sub>C x)" for k
      by (smt (z3) id_apply one_dim_iso_id one_dim_iso_idem range_eqI)
    thus "range (\<lambda>\<phi>. one_dim_iso (\<phi>::'b) *\<^sub>C x) = cspan {x}"
      unfolding complex_vector.span_singleton
      by auto
  qed
qed

lemma cblinfun_compose_1_left[simp]: \<open>1 o\<^sub>C\<^sub>L x = x\<close>
  apply transfer by auto

lemma cblinfun_compose_1_right[simp]: \<open>x o\<^sub>C\<^sub>L 1 = x\<close>
  apply transfer by auto

(* Renamed from butterfly_proj *)
lemma butterfly_eq_proj:
  assumes "norm x = 1"
  shows "selfbutter x = proj x"
proof -
  define B and \<phi> :: "complex \<Rightarrow>\<^sub>C\<^sub>L 'a"
    where "B = selfbutter x" and "\<phi> = vector_to_cblinfun x"
  then have B: "B = \<phi> o\<^sub>C\<^sub>L \<phi>*"
    unfolding butterfly_def by simp
  have \<phi>adj\<phi>: "\<phi>* o\<^sub>C\<^sub>L \<phi> = id_cblinfun"    
    using \<phi>_def assms isometry_def isometry_vector_to_cblinfun by blast
  have "B o\<^sub>C\<^sub>L B = \<phi> o\<^sub>C\<^sub>L (\<phi>* o\<^sub>C\<^sub>L \<phi>) o\<^sub>C\<^sub>L \<phi>*"
    by (simp add: B cblinfun_assoc_left(1))
  also have "\<dots> = B"
    unfolding \<phi>adj\<phi> by (simp add: B)
  finally have idem: "B o\<^sub>C\<^sub>L B = B".
  have herm: "B = B*"
    unfolding B by simp
  from idem herm have BProj: "B = Proj (B *\<^sub>S top)"
    by (rule Proj_on_own_range'[symmetric])
  have "B *\<^sub>S top = ccspan {x}"
    by (simp add: B \<phi>_def assms cblinfun_compose_image range_adjoint_isometry)
  with BProj show "B = proj x"
    by simp
qed

lemma butterfly_is_Proj:
  \<open>norm x = 1 \<Longrightarrow> is_Proj (selfbutter x)\<close>
  by (subst butterfly_eq_proj, simp_all)

lemma Proj_bot[simp]: "Proj bot = 0"
  by (metis zero_scaleC_ccsubspace Proj_on_own_range' is_Proj_0 is_Proj_algebraic 
      zero_ccsubspace_def)

lemma Proj_ortho_compl:
  "Proj (- X) = id_cblinfun - Proj X"
  by (transfer , auto)

lemma Proj_inj: 
  assumes "Proj X = Proj Y"
  shows "X = Y"
  by (metis assms Proj_range)

lemma cblinfun_apply_in_image[simp]: "A *\<^sub>V \<psi> \<in> space_as_set (A *\<^sub>S \<top>)"
  by (metis cblinfun_image.rep_eq closure_subset in_mono range_eqI top_ccsubspace.rep_eq)

lemma cbilinear_cblinfun_compose[simp]: "cbilinear cblinfun_compose"
  by (auto intro!: clinearI simp add: cbilinear_def bounded_cbilinear.add_left bounded_cbilinear.add_right bounded_cbilinear_cblinfun_compose)

lemma one_dim_iso_id_cblinfun: \<open>one_dim_iso id_cblinfun = id_cblinfun\<close>
  by simp

(* Renamed from one_dim_iso_id_cblinfun *)
lemma one_dim_iso_id_cblinfun_eq_1: \<open>one_dim_iso id_cblinfun = 1\<close>
  by simp

(* Renamed from one_dim_iso_cblinfun_apply *)
lemma one_dim_iso_comp_distr[simp]: \<open>one_dim_iso (a o\<^sub>C\<^sub>L b) = one_dim_iso a o\<^sub>C\<^sub>L one_dim_iso b\<close>
  by (smt (z3) cblinfun_compose_scaleC_left cblinfun_compose_scaleC_right one_cinner_a_scaleC_one one_comp_one_cblinfun one_dim_iso_of_one one_dim_iso_scaleC)

(* Renamed from one_dim_iso_comp_distr_complex *)
lemma one_dim_iso_comp_distr_times[simp]: \<open>one_dim_iso (a o\<^sub>C\<^sub>L b) = one_dim_iso a * one_dim_iso b\<close>
  by (smt (verit, del_insts) mult.left_neutral mult_scaleC_left one_cinner_a_scaleC_one one_comp_one_cblinfun one_dim_iso_of_one one_dim_iso_scaleC cblinfun_compose_scaleC_right cblinfun_compose_scaleC_left)

lemma one_dim_iso_adjoint[simp]: \<open>one_dim_iso (A*) = (one_dim_iso A)*\<close>
  by (smt (z3) one_cblinfun_adj one_cinner_a_scaleC_one one_dim_iso_of_one one_dim_iso_scaleC scaleC_adj)

lemma one_dim_iso_adjoint_complex[simp]: \<open>one_dim_iso (A*) = cnj (one_dim_iso A)\<close>
  by (metis (mono_tags, lifting) one_cblinfun_adj one_dim_iso_idem one_dim_scaleC_1 scaleC_adj)

lemma one_dim_cblinfun_compose_commute: \<open>a o\<^sub>C\<^sub>L b = b o\<^sub>C\<^sub>L a\<close> for a b :: \<open>('a::one_dim,'a) cblinfun\<close>
  by (simp add: one_dim_iso_inj)

lemma one_dim_loewner_order: \<open>A \<ge> B \<longleftrightarrow> one_dim_iso A \<ge> (one_dim_iso B :: complex)\<close> for A B :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::{chilbert_space, one_dim}\<close>
proof -
  note less_eq_complex_def[simp del]
  have A: \<open>A = one_dim_iso A *\<^sub>C id_cblinfun\<close>
    by simp
  have B: \<open>B = one_dim_iso B *\<^sub>C id_cblinfun\<close>
    by simp
  have \<open>A \<ge> B \<longleftrightarrow> (\<forall>\<psi>. cinner \<psi> (A \<psi>) \<ge> cinner \<psi> (B \<psi>))\<close>
    by (simp add: less_eq_cblinfun_def)
  also have \<open>\<dots> \<longleftrightarrow> (\<forall>\<psi>::'a. one_dim_iso B * (\<psi> \<bullet>\<^sub>C \<psi>) \<le> one_dim_iso A * (\<psi> \<bullet>\<^sub>C \<psi>))\<close>
    apply (subst A, subst B)
    by (metis (no_types, hide_lams) cinner_scaleC_right id_cblinfun_apply scaleC_cblinfun.rep_eq)
  also have \<open>\<dots> \<longleftrightarrow> one_dim_iso A \<ge> (one_dim_iso B :: complex)\<close>
    by (auto intro!: mult_right_mono elim!: allE[where x=1])
  finally show ?thesis
    by -
qed

lemma one_dim_positive: \<open>A \<ge> 0 \<longleftrightarrow> one_dim_iso A \<ge> (0::complex)\<close> for A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a::{chilbert_space, one_dim}\<close>
  using one_dim_loewner_order[where B=0] by auto


lift_definition sandwich :: \<open>('a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner) \<Rightarrow> (('a \<Rightarrow>\<^sub>C\<^sub>L 'a) \<Rightarrow>\<^sub>C\<^sub>L ('b \<Rightarrow>\<^sub>C\<^sub>L 'b))\<close> is
  \<open>\<lambda>(A::'a\<Rightarrow>\<^sub>C\<^sub>L'b) B. A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*\<close>
proof 
  fix A :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'b\<close> and B B1 B2 :: \<open>'a \<Rightarrow>\<^sub>C\<^sub>L 'a\<close> and c :: complex
  show \<open>A o\<^sub>C\<^sub>L (B1 + B2) o\<^sub>C\<^sub>L A* = (A o\<^sub>C\<^sub>L B1 o\<^sub>C\<^sub>L A*) + (A o\<^sub>C\<^sub>L B2 o\<^sub>C\<^sub>L A*)\<close>
    by (auto simp: cbilinear_add_left cbilinear_add_right)
  show \<open>A o\<^sub>C\<^sub>L (c *\<^sub>C B) o\<^sub>C\<^sub>L A* = c *\<^sub>C (A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*)\<close>
    by auto
  show \<open>\<exists>K. \<forall>B. norm (A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*) \<le> norm B * K\<close>
  proof (rule exI[of _ \<open>norm A * norm (A*)\<close>], rule allI)
    fix B
    have \<open>norm (A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*) \<le> norm (A o\<^sub>C\<^sub>L B) * norm (A*)\<close>
      using norm_cblinfun_compose by blast
    also have \<open>\<dots> \<le> (norm A * norm B) * norm (A*)\<close>
      by (simp add: mult_right_mono norm_cblinfun_compose)
    finally show \<open>norm (A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*) \<le> norm B * (norm A * norm (A*))\<close>
      by (simp add: mult.assoc vector_space_over_itself.scale_left_commute)
  qed
qed

lemma sandwich_apply: \<open>sandwich A *\<^sub>V B = A o\<^sub>C\<^sub>L B o\<^sub>C\<^sub>L A*\<close>
  apply (transfer fixing: A B) by auto

(* TODO move *)
lemma Sup_real_close:
  fixes e :: real
  assumes "0 < e"
    and S: "bdd_above S" "S \<noteq> {}"
  shows "\<exists>x\<in>S. Sup S - e < x"
proof -
  have \<open>\<Squnion> (ereal ` S) \<noteq> \<infinity>\<close>
    by (metis assms(2) bdd_above_def ereal_less_eq(3) less_SUP_iff less_ereal.simps(4) not_le)
  moreover have \<open>\<Squnion> (ereal ` S) \<noteq> -\<infinity>\<close>
    by (simp add: SUP_eq_iff assms(3))
  ultimately have Sup_bdd: \<open>\<bar>\<Squnion> (ereal ` S)\<bar> \<noteq> \<infinity>\<close>
    by auto
  then have \<open>\<exists>x'\<in>ereal ` S. Sup (ereal ` S) - ereal e < x'\<close>
    apply (rule_tac Sup_ereal_close)
    using assms by auto
  then obtain x where \<open>x \<in> S\<close> and Sup_x: \<open>Sup (ereal ` S) - ereal e < ereal x\<close>
    by auto
  have \<open>Sup (ereal ` S) = ereal (Sup S)\<close>
    using Sup_bdd by (rule ereal_Sup[symmetric])
  with Sup_x have \<open>ereal (Sup S - e) < ereal x\<close>
    by auto
  then have \<open>Sup S - e < x\<close>
    by auto
  with \<open>x \<in> S\<close> show ?thesis
    by auto
qed

lemma cblinfun_norm_approx_witness:
  fixes A :: \<open>'a::{not_singleton,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<epsilon> > 0\<close>
  shows \<open>\<exists>\<psi>. norm (A *\<^sub>V \<psi>) \<ge> norm A - \<epsilon> \<and> norm \<psi> = 1\<close>
proof (transfer fixing: \<epsilon>)
  fix A :: \<open>'a \<Rightarrow> 'b\<close> assume [simp]: \<open>bounded_clinear A\<close>
  have \<open>\<exists>y\<in>{norm (A x) |x. norm x = 1}. y > \<Squnion> {norm (A x) |x. norm x = 1} - \<epsilon>\<close>
    apply (rule Sup_real_close)
    using assms by (auto simp: ex_norm1 bounded_clinear.bounded_linear bdd_above_norm_f)
  also have \<open>\<Squnion> {norm (A x) |x. norm x = 1} = onorm A\<close>
    by (simp add: Complex_Vector_Spaces0.bounded_clinear.bounded_linear onorm_sphere)
  finally 
  show \<open>\<exists>\<psi>. onorm A - \<epsilon> \<le> norm (A \<psi>) \<and> norm \<psi> = 1\<close>
    by force
qed

lemma cblinfun_norm_approx_witness_mult:
  fixes A :: \<open>'a::{not_singleton,complex_normed_vector} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector\<close>
  assumes \<open>\<epsilon> < 1\<close>
  shows \<open>\<exists>\<psi>. norm (A *\<^sub>V \<psi>) \<ge> norm A * \<epsilon> \<and> norm \<psi> = 1\<close>
proof (cases \<open>norm A = 0\<close>)
  case True
  then show ?thesis
    apply auto
    by (simp add: ex_norm1)
next
  case False
  then have \<open>(1 - \<epsilon>) * norm A > 0\<close>
    using assms by fastforce
  then obtain \<psi> where geq: \<open>norm (A *\<^sub>V \<psi>) \<ge> norm A - ((1 - \<epsilon>) * norm A)\<close> and \<open>norm \<psi> = 1\<close>
    using cblinfun_norm_approx_witness by blast
  have \<open>norm A * \<epsilon> = norm A - (1 - \<epsilon>) * norm A\<close>
    by (simp add: mult.commute right_diff_distrib')
  also have \<open>\<dots> \<le> norm (A *\<^sub>V \<psi>)\<close>
    by (rule geq)
  finally show ?thesis
    using \<open>norm \<psi> = 1\<close> by auto
qed

(* TODO move *)
attribute_setup internalize_sort = \<open>let
fun find_tvar thm v = let
  val tvars = Term.add_tvars (Thm.prop_of thm) []
  val tv = case find_first (fn (n,sort) => n=v) tvars of
              SOME tv => tv | NONE => raise THM ("Type variable " ^ string_of_indexname v ^ " not found", 0, [thm])
in 
TVar tv
end

fun internalize_sort_attr (tvar:indexname) =
  Thm.rule_attribute [] (fn context => fn thm =>
    (snd (Internalize_Sort.internalize_sort (Thm.ctyp_of (Context.proof_of context) (find_tvar thm tvar)) thm)));
in
  Scan.lift Args.var >> internalize_sort_attr
end\<close>
  "internalize a sort"

(* TODO move *)
lemma CARD_1_vec_0[simp]: \<open>(\<psi> :: _ ::{complex_vector,CARD_1}) = 0\<close>
  by auto

lemma cblinfun_to_CARD_1_0[simp]: \<open>(A :: _ \<Rightarrow>\<^sub>C\<^sub>L _::CARD_1) = 0\<close>
  apply (rule cblinfun_eqI)
  by auto

lemma cblinfun_from_CARD_1_0[simp]: \<open>(A :: _::CARD_1 \<Rightarrow>\<^sub>C\<^sub>L _) = 0\<close>
  apply (rule cblinfun_eqI)
  apply (subst CARD_1_vec_0)
  by auto

(* TODO move *)
lemma not_singleton_vs_CARD_1:
  assumes \<open>\<not> class.not_singleton TYPE('a)\<close>
  shows \<open>class.CARD_1 TYPE('a)\<close>
  using assms unfolding class.not_singleton_def class.CARD_1_def
  by (metis (full_types) One_nat_def UNIV_I card.empty card.insert empty_iff equalityI finite.intros(1) insert_iff subsetI)

lemma norm_AAadj[simp]: \<open>norm (A o\<^sub>C\<^sub>L A*) = (norm A)\<^sup>2\<close> for A :: \<open>'a::chilbert_space \<Rightarrow>\<^sub>C\<^sub>L 'b::{complex_inner}\<close>
proof (cases \<open>class.not_singleton TYPE('b)\<close>)
  case True
  then have [simp]: \<open>class.not_singleton TYPE('b)\<close>
    by -
  have 1: \<open>(norm A)\<^sup>2 * \<epsilon> \<le> norm (A o\<^sub>C\<^sub>L A*)\<close> if \<open>\<epsilon> < 1\<close> and \<open>\<epsilon> \<ge> 0\<close> for \<epsilon>
  proof -
    obtain \<psi> where \<psi>: \<open>norm ((A*) *\<^sub>V \<psi>) \<ge> norm (A*) * sqrt \<epsilon>\<close> and [simp]: \<open>norm \<psi> = 1\<close>
      apply atomize_elim
      apply (rule cblinfun_norm_approx_witness_mult[internalize_sort 'a])
      using \<open>\<epsilon> < 1\<close> by (auto intro: complex_normed_vector_class.complex_normed_vector_axioms)
    have \<open>complex_of_real ((norm A)\<^sup>2 * \<epsilon>) = (norm (A*) * sqrt \<epsilon>)\<^sup>2\<close>
      by (simp add: ordered_field_class.sign_simps(23) that(2))
    also have \<open>\<dots> \<le> (norm ((A* *\<^sub>V \<psi>)))\<^sup>2\<close>
      apply (rule complex_of_real_mono)
      using \<psi> apply (rule power_mono)
      using \<open>\<epsilon> \<ge> 0\<close> by auto
    also have \<open>\<dots> \<le> cinner (A* *\<^sub>V \<psi>) (A* *\<^sub>V \<psi>)\<close>
      by (auto simp flip: power2_norm_eq_cinner)
    also have \<open>\<dots> = cinner \<psi> (A *\<^sub>V A* *\<^sub>V \<psi>)\<close>
      by (simp add: cinner_adj_left)
    also have \<open>\<dots> = cinner \<psi> ((A o\<^sub>C\<^sub>L A*) *\<^sub>V \<psi>)\<close>
      by auto
    also have \<open>\<dots> \<le> norm (A o\<^sub>C\<^sub>L A*)\<close>
      using \<open>norm \<psi> = 1\<close>
      by (smt (verit, best) Im_complex_of_real Re_complex_of_real \<open>(A* *\<^sub>V \<psi>) \<bullet>\<^sub>C (A* *\<^sub>V \<psi>) = \<psi> \<bullet>\<^sub>C (A *\<^sub>V A* *\<^sub>V \<psi>)\<close> \<open>\<psi> \<bullet>\<^sub>C (A *\<^sub>V A* *\<^sub>V \<psi>) = \<psi> \<bullet>\<^sub>C ((A o\<^sub>C\<^sub>L A*) *\<^sub>V \<psi>)\<close> cdot_square_norm cinner_ge_zero cmod_Re complex_inner_class.Cauchy_Schwarz_ineq2 less_eq_complex_def mult_cancel_left1 mult_cancel_right1 norm_cblinfun) 
    finally show ?thesis
      by auto
  qed
  then have 1: \<open>(norm A)\<^sup>2 \<le> norm (A o\<^sub>C\<^sub>L A*)\<close>
    by (metis field_le_mult_one_interval less_eq_real_def ordered_field_class.sign_simps(5))

  have 2: \<open>norm (A o\<^sub>C\<^sub>L A*) \<le> (norm A)\<^sup>2\<close>
  proof (rule norm_cblinfun_bound)
    show \<open>0 \<le> (norm A)\<^sup>2\<close> by simp
    fix \<psi>
    have \<open>norm ((A o\<^sub>C\<^sub>L A*) *\<^sub>V \<psi>) = norm (A *\<^sub>V A* *\<^sub>V \<psi>)\<close>
      by auto
    also have \<open>\<dots> \<le> norm A * norm (A* *\<^sub>V \<psi>)\<close>
      by (simp add: norm_cblinfun)
    also have \<open>\<dots> \<le> norm A * norm (A*) * norm \<psi>\<close>
      by (metis mult.assoc norm_cblinfun norm_imp_pos_and_ge ordered_comm_semiring_class.comm_mult_left_mono)
    also have \<open>\<dots> = (norm A)\<^sup>2 * norm \<psi>\<close>
      by (simp add: power2_eq_square)
    finally show \<open>norm ((A o\<^sub>C\<^sub>L A*) *\<^sub>V \<psi>) \<le> (norm A)\<^sup>2 * norm \<psi>\<close>
      by -
  qed

  from 1 2 show ?thesis by simp
next
  case False
  then have [simp]: \<open>class.CARD_1 TYPE('b)\<close>
    by (rule not_singleton_vs_CARD_1)
  have \<open>A = 0\<close>
    apply (rule cblinfun_to_CARD_1_0[internalize_sort 'b])
    by (auto intro: complex_normed_vector_class.complex_normed_vector_axioms)
  then show ?thesis
    by auto
qed

lemma norm_sandwich: \<open>norm (sandwich A) = (norm A)\<^sup>2\<close> for A :: \<open>'a::{chilbert_space,perfect_space} \<Rightarrow>\<^sub>C\<^sub>L 'b::{complex_inner,perfect_space}\<close>
    (* TODO remove perfect_space *)
proof (rule norm_cblinfun_eqI)
  show \<open>(norm A)\<^sup>2 \<le> norm (sandwich A *\<^sub>V id_cblinfun) / norm (id_cblinfun :: 'a \<Rightarrow>\<^sub>C\<^sub>L _)\<close>
    apply (auto simp: sandwich_apply)
    by -
  fix B
  have \<open>norm (sandwich A *\<^sub>V B) \<le> norm (A o\<^sub>C\<^sub>L B) * norm (A*)\<close>
    using norm_cblinfun_compose by (auto simp: sandwich_apply simp del: norm_adj)
  also have \<open>\<dots> \<le> (norm A * norm B) * norm (A*)\<close>
    by (simp add: mult_right_mono norm_cblinfun_compose)
  also have \<open>\<dots> \<le> (norm A)\<^sup>2 * norm B\<close>
    by (simp add: power2_eq_square mult.assoc vector_space_over_itself.scale_left_commute)
  finally show \<open>norm (sandwich A *\<^sub>V B) \<le> (norm A)\<^sup>2 * norm B\<close>
    by -
  show \<open>0 \<le> (norm A)\<^sup>2\<close>
    by auto
qed

lemma sandwich_apply_adj: \<open>sandwich A (B*) = (sandwich A B)*\<close>
  by (simp add: cblinfun_assoc_left(1) sandwich_apply)

lemma sandwich_id[simp]: "sandwich id_cblinfun = id_cblinfun"
  apply (rule cblinfun_eqI)
  by (auto simp: sandwich_apply)


lemma cblinfun_plus_image_distr:
  \<open>(A + B) *\<^sub>S S \<le> A *\<^sub>S S \<squnion> B *\<^sub>S S\<close>
  apply transfer
  by (smt (verit, ccfv_threshold) closed_closure closed_sum_def closure_minimal closure_subset image_subset_iff set_plus_intro subset_eq)

lemma cblinfun_sum_image_distr:
  \<open>(\<Sum>i\<in>I. A i) *\<^sub>S S \<le> (SUP i\<in>I. A i *\<^sub>S S)\<close>
proof (cases \<open>finite I\<close>)
  case True
  then show ?thesis
  proof induction
    case empty
    then show ?case
      by auto
  next
    case (insert x F)
    then show ?case
      apply auto by (smt (z3) cblinfun_plus_image_distr inf_sup_aci(6) le_iff_sup)
  qed
next
  case False
  then show ?thesis 
    by auto
qed


lemma cblinfun_cspan_UNIV:
  fixes basis :: \<open>('a::{complex_normed_vector,cfinite_dim} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_normed_vector) set\<close>
    and basisA :: \<open>'a set\<close> and basisB :: \<open>'b set\<close>
  assumes \<open>cspan basisA = UNIV\<close> and \<open>cspan basisB = UNIV\<close>
  assumes basis: \<open>\<And>a b. a\<in>basisA \<Longrightarrow> b\<in>basisB \<Longrightarrow> \<exists>F\<in>basis. \<forall>a'\<in>basisA. F *\<^sub>V a' = (if a'=a then b else 0)\<close>
  shows \<open>cspan basis = UNIV\<close>
proof -
  obtain basisA' where \<open>basisA' \<subseteq> basisA\<close> and \<open>cindependent basisA'\<close> and \<open>cspan basisA' = UNIV\<close>
    by (metis assms(1) complex_vector.maximal_independent_subset complex_vector.span_eq top_greatest)
  then have [simp]: \<open>finite basisA'\<close>
    by (simp add: cindependent_cfinite_dim_finite)
  have basis': \<open>\<And>a b. a\<in>basisA' \<Longrightarrow> b\<in>basisB \<Longrightarrow> \<exists>F\<in>basis. \<forall>a'\<in>basisA'. F *\<^sub>V a' = (if a'=a then b else 0)\<close>
    using basis \<open>basisA' \<subseteq> basisA\<close> by fastforce

  obtain F where F: \<open>F a b \<in> basis \<and> F a b *\<^sub>V a' = (if a'=a then b else 0)\<close> 
    if \<open>a\<in>basisA'\<close> \<open>b\<in>basisB\<close> \<open>a'\<in>basisA'\<close> for a b a'
    apply atomize_elim apply (intro choice allI)
    using basis' by metis
  then have F_apply: \<open>F a b *\<^sub>V a' = (if a'=a then b else 0)\<close>
    if \<open>a\<in>basisA'\<close> \<open>b\<in>basisB\<close> \<open>a'\<in>basisA'\<close> for a b a'
    using that by auto
  have F_basis: \<open>F a b \<in> basis\<close> 
    if \<open>a\<in>basisA'\<close> \<open>b\<in>basisB\<close> for a b
    using that F by auto
  have b_span: \<open>\<exists>G\<in>cspan {F a b|b. b\<in>basisB}. \<forall>a'\<in>basisA'. G *\<^sub>V a' = (if a'=a then b else 0)\<close> if \<open>a\<in>basisA'\<close> for a b
  proof -
    from \<open>cspan basisB = UNIV\<close>
    obtain r t where \<open>finite t\<close> and \<open>t \<subseteq> basisB\<close> and b_lincom: \<open>b = (\<Sum>a\<in>t. r a *\<^sub>C a)\<close>
      unfolding complex_vector.span_alt apply atomize_elim by blast
    define G where \<open>G = (\<Sum>i\<in>t. r i *\<^sub>C F a i)\<close>
    have \<open>G \<in> cspan {F a b|b. b\<in>basisB}\<close>
      using \<open>finite t\<close> \<open>t \<subseteq> basisB\<close> unfolding G_def
      by (smt (verit, ccfv_threshold) complex_vector.span_base complex_vector.span_scale complex_vector.span_sum mem_Collect_eq subset_eq)
    moreover have \<open>G *\<^sub>V a' = (if a'=a then b else 0)\<close> if \<open>a'\<in>basisA'\<close> for a'
      apply (cases \<open>a'=a\<close>)
      using \<open>t \<subseteq> basisB\<close> \<open>a\<in>basisA'\<close> \<open>a'\<in>basisA'\<close>
      by (auto simp: b_lincom G_def cblinfun.sum_left F_apply intro!: sum.neutral sum.cong) 
    ultimately show ?thesis
      by blast
  qed

  have a_span: \<open>cspan (\<Union>a\<in>basisA'. cspan {F a b|b. b\<in>basisB}) = UNIV\<close>
  proof (intro equalityI subset_UNIV subsetI, rename_tac H)
    fix H
    obtain G where G: \<open>G a b \<in> cspan {F a b|b. b\<in>basisB} \<and> G a b *\<^sub>V a' = (if a'=a then b else 0)\<close> if \<open>a\<in>basisA'\<close> and \<open>a'\<in>basisA'\<close> for a b a'
      apply atomize_elim apply (intro choice allI)
      using b_span by blast
    then have G_cspan: \<open>G a b \<in> cspan {F a b|b. b\<in>basisB}\<close> if \<open>a\<in>basisA'\<close> for a b
      using that by auto
    from G have G: \<open>G a b *\<^sub>V a' = (if a'=a then b else 0)\<close> if \<open>a\<in>basisA'\<close> and \<open>a'\<in>basisA'\<close> for a b a'
      using that by auto
    define H' where \<open>H' = (\<Sum>a\<in>basisA'. G a (H *\<^sub>V a))\<close>
    have \<open>H' \<in> cspan (\<Union>a\<in>basisA'. cspan {F a b|b. b\<in>basisB})\<close>
      unfolding H'_def using G_cspan
      by (smt (verit, del_insts) UN_iff complex_vector.span_clauses(1) complex_vector.span_sum) 
    moreover have \<open>H' = H\<close>
      using \<open>cspan basisA' = UNIV\<close> apply (rule cblinfun_eq_on_UNIV_span)
      apply (auto simp: H'_def cblinfun.sum_left)
      apply (subst sum_single)
      by (auto simp: G)
    ultimately show \<open>H \<in> cspan (\<Union>a\<in>basisA'. cspan {F a b |b. b \<in> basisB})\<close>
      by simp
  qed

  moreover have \<open>cspan basis \<supseteq> cspan (\<Union>a\<in>basisA'. cspan {F a b|b. b\<in>basisB})\<close>
    using F_basis
    by (smt (z3) UN_subset_iff complex_vector.span_alt complex_vector.span_minimal complex_vector.subspace_span mem_Collect_eq subset_iff)

  ultimately show \<open>cspan basis = UNIV\<close>
    by auto
qed

lemma cspan_butterfly_UNIV:
  assumes \<open>cspan basisA = UNIV\<close>
  assumes \<open>cspan basisB = UNIV\<close>
  assumes \<open>is_ortho_set basisB\<close>
  assumes \<open>\<And>b. b \<in> basisB \<Longrightarrow> norm b = 1\<close>
  shows \<open>cspan {butterfly a b| (a::'a::{complex_normed_vector}) (b::'b::{chilbert_space,cfinite_dim}). a \<in> basisA \<and> b \<in> basisB} = UNIV\<close>
proof -
  have F: \<open>\<exists>F\<in>{butterfly a b |a b. a \<in> basisA \<and> b \<in> basisB}. \<forall>b'\<in>basisB. F *\<^sub>V b' = (if b' = b then a else 0)\<close>
    if \<open>a \<in> basisA\<close> and \<open>b \<in> basisB\<close> for a b
    apply (rule bexI[where x=\<open>butterfly a b\<close>])
    using assms that by (auto simp: is_ortho_set_def cnorm_eq_1)
  show ?thesis
    apply (rule cblinfun_cspan_UNIV[where basisA=basisB and basisB=basisA])
    using assms apply auto[2]
    using F by (smt (verit, ccfv_SIG) image_iff)
qed

lemma cindependent_butterfly: 
  fixes basisA :: \<open>'a::chilbert_space set\<close> and basisB :: \<open>'b::chilbert_space set\<close>
  assumes \<open>is_ortho_set basisA\<close> \<open>is_ortho_set basisB\<close>
  assumes normA: \<open>\<And>a. a\<in>basisA \<Longrightarrow> norm a = 1\<close> and normB: \<open>\<And>b. b\<in>basisB \<Longrightarrow> norm b = 1\<close>
  shows \<open>cindependent {butterfly a b| a b. a\<in>basisA \<and> b\<in>basisB}\<close>
proof (unfold complex_vector.independent_explicit_module, intro allI impI, rename_tac T f g)
  fix T :: \<open>('b \<Rightarrow>\<^sub>C\<^sub>L 'a) set\<close> and f :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a \<Rightarrow> complex\<close> and g :: \<open>'b \<Rightarrow>\<^sub>C\<^sub>L 'a\<close>
  assume \<open>finite T\<close>
  assume T_subset: \<open>T \<subseteq> {butterfly a b |a b. a \<in> basisA \<and> b \<in> basisB}\<close>
  define lin where \<open>lin = (\<Sum>g\<in>T. f g *\<^sub>C g)\<close>
  assume \<open>lin = 0\<close>
  assume \<open>g \<in> T\<close>
  (* To show: f g = 0 *)
  then obtain a b where g: \<open>g = butterfly a b\<close> and [simp]: \<open>a \<in> basisA\<close> \<open>b \<in> basisB\<close>
    using T_subset by auto

  have *: "(vector_to_cblinfun a)* *\<^sub>V f g *\<^sub>C g *\<^sub>V b = 0"
    if \<open>g \<in> T - {butterfly a b}\<close> for g 
  proof -
    from that
    obtain a' b' where g: \<open>g = butterfly a' b'\<close> and [simp]: \<open>a' \<in> basisA\<close> \<open>b' \<in> basisB\<close>
      using T_subset by auto
    from that have \<open>g \<noteq> butterfly a b\<close> by auto
    with g consider (a) \<open>a\<noteq>a'\<close> | (b) \<open>b\<noteq>b'\<close>
      by auto
    then show \<open>(vector_to_cblinfun a)* *\<^sub>V f g *\<^sub>C g *\<^sub>V b = 0\<close>
    proof cases
      case a
      then show ?thesis 
        using  \<open>is_ortho_set basisA\<close> unfolding g 
        by (auto simp: is_ortho_set_def butterfly_def scaleC_cblinfun.rep_eq)
    next
      case b
      then show ?thesis
        using  \<open>is_ortho_set basisB\<close> unfolding g 
        by (auto simp: is_ortho_set_def butterfly_def scaleC_cblinfun.rep_eq)
    qed
  qed

  have \<open>0 = (vector_to_cblinfun a)* *\<^sub>V lin *\<^sub>V b\<close>
    using \<open>lin = 0\<close> by auto
  also have \<open>\<dots> = (\<Sum>g\<in>T. (vector_to_cblinfun a)* *\<^sub>V (f g *\<^sub>C g) *\<^sub>V b)\<close>
    unfolding lin_def
    apply (rule complex_vector.linear_sum)
    by (smt (z3) cblinfun.scaleC_left cblinfun.scaleC_right cblinfun.add_right clinearI plus_cblinfun.rep_eq)
  also have \<open>\<dots> = (\<Sum>g\<in>{butterfly a b}. (vector_to_cblinfun a)* *\<^sub>V (f g *\<^sub>C g) *\<^sub>V b)\<close>
    apply (rule sum.mono_neutral_right)
    using \<open>finite T\<close> * \<open>g \<in> T\<close> g by auto
  also have \<open>\<dots> = (vector_to_cblinfun a)* *\<^sub>V (f g *\<^sub>C g) *\<^sub>V b\<close>
    by (simp add: g)
  also have \<open>\<dots> = f g\<close>
    unfolding g 
    using normA normB by (auto simp: butterfly_def scaleC_cblinfun.rep_eq cnorm_eq_1)
  finally show \<open>f g = 0\<close>
    by simp
qed

lemma clinear_eq_butterflyI:
  fixes F G :: \<open>('a::{chilbert_space,cfinite_dim} \<Rightarrow>\<^sub>C\<^sub>L 'b::complex_inner) \<Rightarrow> 'c::complex_vector\<close>
  assumes "clinear F" and "clinear G"
  assumes \<open>cspan basisA = UNIV\<close> \<open>cspan basisB = UNIV\<close>
  assumes \<open>is_ortho_set basisA\<close> \<open>is_ortho_set basisB\<close>
  assumes "\<And>a b. a\<in>basisA \<Longrightarrow> b\<in>basisB \<Longrightarrow> F (butterfly a b) = G (butterfly a b)"
  assumes \<open>\<And>b. b\<in>basisB \<Longrightarrow> norm b = 1\<close>
  shows "F = G"
  apply (rule complex_vector.linear_eq_on_span[where f=F, THEN ext, rotated 3])
     apply (subst cspan_butterfly_UNIV)
  using assms by auto

instance cblinfun :: (\<open>{cfinite_dim,complex_normed_vector}\<close>, \<open>{cfinite_dim,complex_normed_vector}\<close>) cfinite_dim
proof intro_classes
  obtain basisA :: \<open>'a set\<close> where [simp]: \<open>cspan basisA = UNIV\<close> \<open>cindependent basisA\<close> \<open>finite basisA\<close>
    using finite_basis by blast
  obtain basisB :: \<open>'b set\<close> where [simp]: \<open>cspan basisB = UNIV\<close> \<open>cindependent basisB\<close> \<open>finite basisB\<close>
    using finite_basis by blast
  define f where \<open>f a b = cconstruct basisA (\<lambda>x. if x=a then b else 0)\<close> for a :: 'a and b :: 'b
  have f_a: \<open>f a b a = b\<close> if \<open>a : basisA\<close> for a b
    by (simp add: complex_vector.construct_basis f_def that)
  have f_not_a: \<open>f a b c = 0\<close> if \<open>a : basisA\<close> and \<open>c : basisA\<close> and \<open>a \<noteq> c\<close>for a b c
    using that by (simp add: complex_vector.construct_basis f_def)
  define F where \<open>F a b = cBlinfun (f a b)\<close> for a b
  have \<open>clinear (f a b)\<close> for a b
    by (auto intro: complex_vector.linear_construct simp: f_def)
  then have \<open>bounded_clinear (f a b)\<close> for a b
    by auto
  then have F_apply: \<open>cblinfun_apply (F a b) = f a b\<close> for a b
    by (simp add: F_def bounded_clinear_cBlinfun_apply)
  define basis where \<open>basis = {F a b| a b. a\<in>basisA \<and> b\<in>basisB}\<close>
  have \<open>cspan basis = UNIV\<close>
    apply (rule cblinfun_cspan_UNIV[where basisA=basisA and basisB=basisB])
    apply (auto simp: basis_def)
    by (metis F_apply f_a f_not_a)

  moreover have \<open>finite basis\<close>
    unfolding basis_def apply (rule finite_image_set2) by auto

  ultimately show \<open>\<exists>S :: ('a \<Rightarrow>\<^sub>C\<^sub>L 'b) set. finite S \<and> cspan S = UNIV\<close>
    by auto
qed  

lemma one_cblinfun_apply_one[simp]: \<open>1 *\<^sub>V 1 = 1\<close>
  by (simp add: one_cblinfun.rep_eq)

section \<open>Notation\<close>


bundle cblinfun_notation begin
notation cblinfun_compose (infixl "o\<^sub>C\<^sub>L" 55)
notation cblinfun_apply (infixr "*\<^sub>V" 70)
notation cblinfun_image (infixr "*\<^sub>S" 70)
notation adj ("_*" [99] 100)
end

bundle no_cblinfun_notation begin
no_notation cblinfun_compose (infixl "o\<^sub>C\<^sub>L" 55)
no_notation cblinfun_apply (infixr "*\<^sub>V" 70)
no_notation cblinfun_image (infixr "*\<^sub>S" 70)
no_notation adj ("_*" [99] 100)
end

bundle blinfun_notation begin
notation blinfun_apply (infixr "*\<^sub>V" 70)
end

bundle no_blinfun_notation begin
no_notation blinfun_apply (infixr "*\<^sub>V" 70)
end

unbundle no_cblinfun_notation

end

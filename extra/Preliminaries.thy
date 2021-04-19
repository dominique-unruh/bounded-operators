section\<open>Preliminaries\<close>

theory Preliminaries
  imports
    Complex_Main            
    (* "HOL-Analysis.Infinite_Set_Sum" *)
    HOL.Groups
    "HOL-Library.Rewrite" 
    Containers.Containers_Auxiliary
    "HOL.Complex" 
    "Jordan_Normal_Form.Conjugate" 
    HOL.Complete_Lattices
    Complex_Main
    Banach_Steinhaus.Banach_Steinhaus
    "HOL-Analysis.Operator_Norm"
    "HOL.Real_Vector_Spaces"
    "HOL-Analysis.Uniform_Limit"

  Extra_General

begin

(* TODO: Split this into separate files *)


subsection\<open>\<open>Lattice_Missing\<close> -- Miscellaneous missing facts about lattices\<close>

text \<open>Two bundles to activate and deactivate lattice specific notation (e.g., \<open>\<sqinter>\<close> etc.).
  Activate the notation locally via "@{theory_text \<open>includes lattice_notation\<close>}" in a lemma statement.
  (Or sandwich a declaration using that notation between "@{theory_text \<open>unbundle lattice_notation ... unbundle no_lattice_notation\<close>}.)\<close>

bundle lattice_notation begin
notation inf (infixl "\<sqinter>" 70)
notation sup (infixl "\<squnion>" 65)
notation Inf ("\<Sqinter>")
notation Sup ("\<Squnion>")
notation bot ("\<bottom>")
notation top ("\<top>")
end

bundle no_lattice_notation begin
notation inf (infixl "\<sqinter>" 70)
notation sup (infixl "\<squnion>" 65)
notation Inf ("\<Sqinter>")
notation Sup ("\<Squnion>")
notation bot ("\<bottom>")
notation top ("\<top>")
end

unbundle lattice_notation

text \<open>The following class \<open>complemented_lattice\<close> describes complemented lattices (with
  \<^const>\<open>uminus\<close> for the complement). The definition follows 
  \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Definition_and_basic_properties\<close>.
  Additionally, it adopts the convention from \<^class>\<open>boolean_algebra\<close> of defining 
  \<^const>\<open>minus\<close> in terms of the complement.\<close>

class complemented_lattice = bounded_lattice + uminus + minus + 
  assumes inf_compl_bot[simp]: "inf x (-x) = bot"
    and sup_compl_top[simp]: "sup x (-x) = top"
    and diff_eq:  "x - y = inf x (- y)" begin

lemma dual_complemented_lattice:
  "class.complemented_lattice (\<lambda>x y. x \<squnion> (- y)) uminus sup greater_eq greater inf \<top> \<bottom>"
  proof (rule class.complemented_lattice.intro)
  show "class.bounded_lattice (\<squnion>) (\<lambda>x y. (y::'a) \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_bounded_lattice)
  show "class.complemented_lattice_axioms (\<lambda>x y. (x::'a) \<squnion> - y) uminus (\<squnion>) (\<sqinter>) \<top> \<bottom>"
    by (unfold_locales, auto simp add: diff_eq)
qed


lemma compl_inf_bot [simp]: "inf (- x) x = bot"
  by (simp add: inf_commute)

lemma compl_sup_top [simp]: "sup (- x) x = top"
  by (simp add: sup_commute)

end

class complete_complemented_lattice = complemented_lattice + complete_lattice 

text \<open>The following class \<open>complemented_lattice\<close> describes orthocomplemented lattices,
  following   \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Orthocomplementation\<close>.\<close>
class orthocomplemented_lattice = complemented_lattice +
  assumes ortho_involution[simp]: "- (- x) = x"
    and ortho_antimono: "x \<le> y \<Longrightarrow> -x \<ge> -y" begin

lemma dual_orthocomplemented_lattice:
  "class.orthocomplemented_lattice (\<lambda>x y. x \<squnion> - y) uminus sup greater_eq greater inf \<top> \<bottom>"
  proof (rule class.orthocomplemented_lattice.intro)
  show "class.complemented_lattice (\<lambda>x y. (x::'a) \<squnion> - y) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_complemented_lattice)
  show "class.orthocomplemented_lattice_axioms uminus (\<lambda>x y. (y::'a) \<le> x)"
      by (unfold_locales, auto simp add: diff_eq intro: ortho_antimono)
qed



lemma compl_eq_compl_iff [simp]: "- x = - y \<longleftrightarrow> x = y"
  by (metis ortho_involution)

lemma compl_bot_eq [simp]: "- bot = top"
  by (metis inf_compl_bot inf_top_left ortho_involution)

lemma compl_top_eq [simp]: "- top = bot"
  using compl_bot_eq ortho_involution by blast

text \<open>De Morgan's law\<close>
  (* Proof from: https://planetmath.org/orthocomplementedlattice *)
lemma compl_sup [simp]: "- (x \<squnion> y) = - x \<sqinter> - y"
proof -
  have "- (x \<squnion> y) \<le> - x"
    by (simp add: ortho_antimono)
  moreover have "- (x \<squnion> y) \<le> - y"
    by (simp add: ortho_antimono)
  ultimately have 1: "- (x \<squnion> y) \<le> - x \<sqinter> - y"
    by (simp add: sup.coboundedI1)
  have \<open>x \<le> - (-x \<sqinter> -y)\<close>
    by (metis inf.cobounded1 ortho_antimono ortho_involution)
  moreover have \<open>y \<le> - (-x \<sqinter> -y)\<close>
    by (metis inf.cobounded2 ortho_antimono ortho_involution)
  ultimately have \<open>x \<squnion> y \<le> - (-x \<sqinter> -y)\<close>
    by auto
  hence 2: \<open>-x \<sqinter> -y \<le> - (x \<squnion> y)\<close>
    using ortho_antimono by fastforce
  from 1 2 show ?thesis
    by (simp add: eq_iff)
qed

text \<open>De Morgan's law\<close>
lemma compl_inf [simp]: "- (x \<sqinter> y) = - x \<squnion> - y"
  using compl_sup
  by (metis ortho_involution)

lemma compl_mono:
  assumes "x \<le> y"
  shows "- y \<le> - x"
  by (simp add: assms local.ortho_antimono)

lemma compl_le_compl_iff [simp]: "- x \<le> - y \<longleftrightarrow> y \<le> x"
  by (auto dest: compl_mono)

lemma compl_le_swap1:
  assumes "y \<le> - x"
  shows "x \<le> -y"
  using assms ortho_antimono by fastforce

lemma compl_le_swap2:
  assumes "- y \<le> x"
  shows "- x \<le> y"
  using assms local.ortho_antimono by fastforce

lemma compl_less_compl_iff[simp]: "- x < - y \<longleftrightarrow> y < x"
  by (auto simp add: less_le)

lemma compl_less_swap1:
  assumes "y < - x"
  shows "x < - y"
  using assms compl_less_compl_iff by fastforce

lemma compl_less_swap2:
  assumes "- y < x"
  shows "- x < y"
  using assms compl_le_swap1 compl_le_swap2 less_le_not_le by auto

lemma sup_cancel_left1: "sup (sup x a) (sup (- x) b) = top"
  by (simp add: sup_commute sup_left_commute)

lemma sup_cancel_left2: "sup (sup (- x) a) (sup x b) = top"
  by (simp add: sup.commute sup_left_commute)

lemma inf_cancel_left1: "inf (inf x a) (inf (- x) b) = bot"
  by (simp add: inf.left_commute inf_commute)

lemma inf_cancel_left2: "inf (inf (- x) a) (inf x b) = bot"
  using inf.left_commute inf_commute by auto

lemma sup_compl_top_left1 [simp]: "sup (- x) (sup x y) = top"
  by (simp add: sup_assoc[symmetric])

lemma sup_compl_top_left2 [simp]: "sup x (sup (- x) y) = top"
  using sup_compl_top_left1[of "- x" y] by simp

lemma inf_compl_bot_left1 [simp]: "inf (- x) (inf x y) = bot"
  by (simp add: inf_assoc[symmetric])

lemma inf_compl_bot_left2 [simp]: "inf x (inf (- x) y) = bot"
  using inf_compl_bot_left1[of "- x" y] by simp

lemma inf_compl_bot_right [simp]: "inf x (inf y (- x)) = bot"
  by (subst inf_left_commute) simp

end

class complete_orthocomplemented_lattice = orthocomplemented_lattice + complete_lattice

instance complete_orthocomplemented_lattice \<subseteq> complete_complemented_lattice
  by intro_classes

text \<open>The following class \<open>orthomodular_lattice\<close> describes orthomodular lattices,
following   \<^url>\<open>https://en.wikipedia.org/wiki/Complemented_lattice#Orthomodular_lattices\<close>.\<close>
class orthomodular_lattice = orthocomplemented_lattice +
  assumes orthomodular: "x \<le> y \<Longrightarrow> sup x (inf (-x) y) = y" begin

lemma dual_orthomodular_lattice:
  "class.orthomodular_lattice (\<lambda>x y. x \<squnion> - y) uminus sup greater_eq greater inf \<top> \<bottom>"
proof (rule class.orthomodular_lattice.intro)
  show "class.orthocomplemented_lattice (\<lambda>x y. (x::'a) \<squnion> - y) uminus (\<squnion>) (\<lambda>x y. y \<le> x) (\<lambda>x y. y < x) (\<sqinter>) \<top> \<bottom>"
    by (rule dual_orthocomplemented_lattice)
  show "class.orthomodular_lattice_axioms uminus (\<squnion>) (\<lambda>x y. (y::'a) \<le> x) (\<sqinter>)"
  proof (unfold_locales)
    show "(x::'a) \<sqinter> (- x \<squnion> y) = y"
      if "(y::'a) \<le> x"
      for x :: 'a
        and y :: 'a
      using that local.compl_eq_compl_iff local.ortho_antimono local.orthomodular by fastforce
  qed
    
qed


end

class complete_orthomodular_lattice = orthomodular_lattice + complete_lattice begin

end

instance complete_orthomodular_lattice \<subseteq> complete_orthocomplemented_lattice
  by intro_classes


instance boolean_algebra \<subseteq> orthomodular_lattice
proof
  fix x y :: 'a  
  show "sup (x::'a) (inf (- x) y) = y"
    if "(x::'a) \<le> y"
    using that
    by (simp add: sup.absorb_iff2 sup_inf_distrib1) 
  show "x - y = inf x (- y)"
    by (simp add: boolean_algebra_class.diff_eq)
qed auto

instance complete_boolean_algebra \<subseteq> complete_orthomodular_lattice
  by intro_classes

unbundle no_lattice_notation

subsection \<open>\<open>Operator_Norm_Missing\<close> -- Miscellaneous results about the operator norm\<close>

text \<open>This theorem complements \<^theory>\<open>HOL-Analysis.Operator_Norm\<close>
      additional useful facts about operator norms.\<close>

subsection \<open>Characterization of the operator norm\<close>

lemma ex_norm1: 
  assumes \<open>(UNIV::'a::real_normed_vector set) \<noteq> {0}\<close>
  shows \<open>\<exists>x::'a. norm x = 1\<close>
proof-
  have \<open>\<exists>x::'a. x \<noteq> 0\<close>
    using assms by fastforce
  then obtain x::'a where \<open>x \<noteq> 0\<close>
    by blast
  hence \<open>norm x \<noteq> 0\<close>
    by simp
  hence \<open>(norm x) / (norm x) = 1\<close>
    by simp
  moreover have \<open>(norm x) / (norm x) = norm (x /\<^sub>R (norm x))\<close>
    by simp
  ultimately have \<open>norm (x /\<^sub>R (norm x)) = 1\<close>
    by simp
  thus ?thesis
    by blast 
qed

lemma bdd_above_norm_f:
  assumes "bounded_linear f"
  shows \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
proof-
  have \<open>\<exists>M. \<forall>x. norm x = 1 \<longrightarrow> norm (f x) \<le> M\<close>
    using assms
    by (metis bounded_linear.axioms(2) bounded_linear_axioms_def)
  thus ?thesis by auto
qed

lemma onorm_sphere:
  fixes f :: "'a::{real_normed_vector, not_singleton} \<Rightarrow> 'b::real_normed_vector"
  assumes a1: "bounded_linear f"
  shows \<open>onorm f = Sup {norm (f x) | x. norm x = 1}\<close>
proof(cases \<open>f = (\<lambda> _. 0)\<close>)
  case True
  have \<open>(UNIV::'a set) \<noteq> {0}\<close>
    by simp
  hence \<open>\<exists>x::'a. norm x = 1\<close>
    using  ex_norm1
    by blast
  have \<open>norm (f x) = 0\<close>
    for x
    by (simp add: True)      
  hence \<open>{norm (f x) | x. norm x = 1} = {0}\<close>
    using \<open>\<exists>x. norm x = 1\<close> by auto
  hence v1: \<open>Sup {norm (f x) | x. norm x = 1} = 0\<close>
    by simp 
  have \<open>onorm f = 0\<close>
    by (simp add: True onorm_eq_0)  
  thus ?thesis using v1 by simp
next
  case False
  have \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
    if "y \<in> {norm (f x) / norm x |x. True}"
    for y
  proof(cases \<open>y = 0\<close>)
    case True
    thus ?thesis
      by simp 
  next
    case False
    have \<open>\<exists> x. y = norm (f x) / norm x\<close>
      using \<open>y \<in> {norm (f x) / norm x |x. True}\<close> by auto
    then obtain x where \<open>y = norm (f x) / norm x\<close>
      by blast
    hence \<open>y = \<bar>(1/norm x)\<bar> * norm ( f x )\<close>
      by simp
    hence \<open>y = norm ( (1/norm x) *\<^sub>R f x )\<close>
      by simp
    hence \<open>y = norm ( f ((1/norm x) *\<^sub>R x) )\<close>
      by (simp add: assms linear_simps(5))
    moreover have \<open>norm ((1/norm x) *\<^sub>R x) = 1\<close>
      using False \<open>y = norm (f x) / norm x\<close> by auto              
    ultimately have \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
      by blast
    thus ?thesis by blast
  qed
  moreover have "y \<in> {norm (f x) / norm x |x. True}"
    if \<open>y \<in> {norm (f x) |x. norm x = 1} \<union> {0}\<close>
    for y
  proof(cases \<open>y = 0\<close>)
    case True
    thus ?thesis
      by auto 
  next
    case False
    hence \<open>y \<notin> {0}\<close>
      by simp
    hence \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
      using that by auto      
    hence \<open>\<exists> x. norm x = 1 \<and> y = norm (f x)\<close>
      by auto
    then obtain x where \<open>norm x = 1\<close> and \<open>y = norm (f x)\<close>
      by auto
    have \<open>y = norm (f x) / norm x\<close> using  \<open>norm x = 1\<close>  \<open>y = norm (f x)\<close>
      by simp 
    thus ?thesis
      by auto 
  qed
  ultimately have \<open>{norm (f x) / norm x |x. True} = {norm (f x) |x. norm x = 1} \<union> {0}\<close> 
    by blast
  hence \<open>Sup {norm (f x) / norm x |x. True} = Sup ({norm (f x) |x. norm x = 1} \<union> {0})\<close>
    by simp
  moreover have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
  proof-
    have \<open>\<exists> x::'a. norm x = 1\<close>
      by (metis (full_types) False a1 linear_simps(3) norm_sgn)              
    then obtain x::'a where \<open>norm x = 1\<close>
      by blast
    have \<open>norm (f x) \<ge> 0\<close>
      by simp
    hence \<open>\<exists> x::'a. norm x = 1 \<and> norm (f x) \<ge> 0\<close>
      using \<open>norm x = 1\<close> by blast
    hence \<open>\<exists> y \<in> {norm (f x) |x. norm x = 1}. y \<ge> 0\<close>
      by blast
    then obtain y::real where \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> 
      and \<open>y \<ge> 0\<close>
      by auto
    have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
      using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close> by blast         
    moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
      using bdd_above_norm_f
      by (metis (mono_tags, lifting) a1) 
    ultimately have \<open>y \<le> Sup {norm (f x) |x. norm x = 1}\<close>
      using \<open>y \<in> {norm (f x) |x. norm x = 1}\<close>
      by (simp add: cSup_upper) 
    thus ?thesis using \<open>y \<ge> 0\<close> by simp
  qed
  moreover have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {0}) = Sup {norm (f x) |x. norm x = 1}\<close>
  proof-
    have \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close>
      by (simp add: assms(1) ex_norm1)
    moreover have \<open>bdd_above {norm (f x) |x. norm x = 1}\<close>
      using a1 bdd_above_norm_f by force
    have \<open>{0::real} \<noteq> {}\<close>
      by simp
    moreover have \<open>bdd_above {0::real}\<close>
      by simp
    ultimately have \<open>Sup ({norm (f x) |x. norm x = 1} \<union> {(0::real)})
             = max (Sup {norm (f x) |x. norm x = 1}) (Sup {0::real})\<close>
      by (metis (lifting) \<open>0 \<le> Sup {norm (f x) |x. norm x = 1}\<close> \<open>bdd_above {0}\<close> \<open>bdd_above {norm (f x) |x. norm x = 1}\<close> \<open>{0} \<noteq> {}\<close> \<open>{norm (f x) |x. norm x = 1} \<noteq> {}\<close> cSup_singleton cSup_union_distrib max.absorb_iff1 sup.absorb_iff1)
    moreover have \<open>Sup {(0::real)} = (0::real)\<close>
      by simp          
    moreover have \<open>Sup {norm (f x) |x. norm x = 1} \<ge> 0\<close>
      by (simp add: \<open>0 \<le> Sup {norm (f x) |x. norm x = 1}\<close>)
    ultimately show ?thesis
      by simp
  qed
  moreover have \<open>Sup ( {norm (f x) |x. norm x = 1} \<union> {0})
           = max (Sup {norm (f x) |x. norm x = 1}) (Sup {0}) \<close>
    using calculation(2) calculation(3) by auto
  ultimately have w1: "Sup {norm (f x) / norm x | x. True} = Sup {norm (f x) | x. norm x = 1}"
    by simp 

  have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) / norm x | x. True}\<close>
    by (simp add: full_SetCompr_eq)
  also have \<open>... = Sup {norm (f x) | x. norm x = 1}\<close>
    using w1 by auto
  ultimately  have \<open>(SUP x. norm (f x) / (norm x)) = Sup {norm (f x) | x. norm x = 1}\<close>
    by linarith
  thus ?thesis unfolding onorm_def by blast
qed


lemma onorm_Inf_bound:
  fixes f :: \<open>'a::{real_normed_vector,not_singleton} \<Rightarrow> 'b::real_normed_vector\<close>
  assumes a1: "bounded_linear f"
  shows "onorm f = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}"
proof-
  have a2: \<open>(UNIV::'a set) \<noteq> {0}\<close>
    by simp

  define A where \<open>A = {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
  have \<open>A \<noteq> {}\<close>
  proof-
    have \<open>\<exists> x::'a. x \<noteq> 0\<close>
      using a2 by auto
    thus ?thesis using A_def
      by simp 
  qed
  moreover have \<open>bdd_above A\<close>
  proof-
    have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
      using \<open>bounded_linear f\<close> le_onorm by auto
    thus ?thesis using A_def
      by auto 
  qed
  ultimately have \<open>Sup A = Inf {b. \<forall>a\<in>A. a \<le> b}\<close>      
    by (simp add: cSup_cInf)  
  moreover have \<open>{b. \<forall>a\<in>A. a \<le> b} = {K. (\<forall>x\<noteq>0. norm (f x)/ norm x \<le>  K)}\<close>
  proof-
    have \<open>{b. \<forall>a\<in>A. a \<le> b} = {b. \<forall>a\<in>{norm (f x) / (norm x) | x. x \<noteq> 0}. a \<le> b}\<close>
      using A_def by blast
    also have \<open>... = {b. \<forall>x\<in>{x | x. x \<noteq> 0}. norm (f x) / (norm x) \<le> b}\<close>
      by auto
    also have \<open>... = {b. \<forall>x\<noteq>0. norm (f x) / (norm x) \<le> b}\<close>
      by auto
    finally show ?thesis by blast
  qed
  ultimately have \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} 
                    = Inf {K. (\<forall>x\<noteq>0. norm (f x)/ norm x \<le>  K)}\<close>
    using A_def
    by simp 
  moreover have \<open>(\<forall>x\<noteq>0. norm (f x) \<le> norm x * K) \<longleftrightarrow> (\<forall>x\<noteq>0. norm (f x)/ norm x \<le> K)\<close>
    for K
  proof
    show "\<forall>x\<noteq>0. norm (f x) / norm x \<le> K"
      if "\<forall>x\<noteq>0. norm (f x) \<le> norm x * K"
      using divide_le_eq nonzero_mult_div_cancel_left norm_le_zero_iff that
      by (simp add: divide_le_eq mult.commute)

    show "\<forall>x\<noteq>0. norm (f x) \<le> norm x * K"
      if "\<forall>x\<noteq>0. norm (f x) / norm x \<le> K"
      using divide_le_eq nonzero_mult_div_cancel_left norm_le_zero_iff that
      by (simp add: divide_le_eq mult.commute)
  qed
  ultimately have f1: \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
    by simp
  moreover 
  have t1: \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0}  = {norm (f x) / (norm x) | x. True}\<close>
    using Collect_cong by blast

  have \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<noteq> {}\<close>
  proof-
    have \<open>\<exists> x::'a. x \<noteq> 0\<close>
      using \<open>UNIV\<noteq>{0}\<close> by auto
    thus ?thesis
      by simp 
  qed
  moreover have \<open>bdd_above {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
  proof-
    have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
      using \<open>bounded_linear f\<close> bounded_linear.nonneg_bounded 
        mult_divide_mult_cancel_left_if norm_zero real_divide_square_eq
      using le_onorm by blast
    thus ?thesis
      by auto 
  qed
  moreover have \<open>{norm (f x) / (norm x) | x. x = 0} \<noteq> {}\<close>
    by simp
  moreover have \<open>bdd_above {norm (f x) / (norm x) | x. x = 0}\<close>
    by simp
  ultimately 
  have d1: \<open>Sup ({norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0})
        = max (Sup {norm (f x) / (norm x) | x. x \<noteq> 0}) (Sup {norm (f x) / (norm x) | x. x = 0})\<close>
    by (metis (no_types, lifting) cSup_union_distrib sup_max)
  have g1: \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} \<ge> 0\<close>
  proof-
    have t2: \<open>{norm (f x) / (norm x) | x. x \<noteq> 0} \<noteq> {}\<close>
    proof-
      have \<open>\<exists> x::'a. x \<noteq> 0\<close>
        using \<open>UNIV\<noteq>{0}\<close> by auto
      thus ?thesis 
        by auto
    qed
    have \<open>\<exists> M. \<forall> x.  norm (f x) / (norm x) \<le> M\<close>
      using \<open>bounded_linear f\<close>
      by (metis \<open>\<And>K. (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) \<le> norm x * K) = (\<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) / norm x \<le> K)\<close> bounded_linear.nonneg_bounded mult_divide_mult_cancel_left_if norm_zero real_divide_square_eq)
    hence t3: \<open>bdd_above {norm (f x) / (norm x) | x. x \<noteq> 0}\<close>
      by auto
    have \<open>norm (f x) / (norm x) \<ge> 0\<close>
      for x
      by simp
    hence \<open>\<forall> y\<in>{norm (f x) / (norm x) | x. x \<noteq> 0}. y \<ge> 0\<close>
      by blast
    show ?thesis
      by (metis (lifting) \<open>\<forall>y\<in>{norm (f x) / norm x |x. x \<noteq> 0}. 0 \<le> y\<close> \<open>bdd_above {norm (f x) / norm x |x. x \<noteq> 0}\<close> \<open>{norm (f x) / norm x |x. x \<noteq> 0} \<noteq> {}\<close> bot.extremum_uniqueI cSup_upper2 subset_emptyI)
  qed
  hence r: \<open>Sup ({norm (f x) / (norm x) | x. x \<noteq> 0} \<union> {norm (f x) / (norm x) | x. x = 0}) 
         = Sup {norm (f x) / (norm x) | x. True}\<close>
    using t1 by auto
  have \<open>{norm (f x) / (norm x) | x. x = 0} = {norm (f 0) / (norm 0)}\<close>
    by simp
  hence \<open>Sup {norm (f x) / (norm x) | x. x = 0} = 0\<close>
    by simp
  have h1: \<open>Sup {norm (f x) / (norm x) | x. x \<noteq> 0} = Sup {norm (f x) / (norm x) | x. True}\<close>
    using d1 r g1 by auto 
  have \<open>(SUP x. norm (f x) / (norm x)) = Inf {K. (\<forall>x\<noteq>0. norm (f x) \<le> norm x * K)}\<close>
    using full_SetCompr_eq
    by (metis \<open>\<Squnion> {norm (f x) / norm x |x. x \<noteq> 0} = \<Sqinter> {K. \<forall>x. x \<noteq> 0 \<longrightarrow> norm (f x) \<le> norm x * K}\<close> h1) 
  thus ?thesis
    by (simp add: onorm_def)
qed

subsection \<open>Banach-Steinhaus theorem\<close>

lemma bounded_linear_ball:
  fixes f :: \<open>'a::real_normed_vector \<Rightarrow> 'b::real_normed_vector\<close>
    and K :: real
  assumes \<open>linear f\<close> and \<open>\<And> x. norm x = 1 \<Longrightarrow> norm (f x) \<le> K\<close>
  shows \<open>bounded_linear f\<close>
proof-
  have \<open>norm (f x) \<le> norm x * K\<close>
    for x
  proof(cases \<open>x = 0\<close>)
    case True
    thus ?thesis
      by (simp add: assms(1) linear_0) 
  next
    case False
    hence \<open>norm x > 0\<close>
      by simp
    hence \<open>norm (inverse (norm x) *\<^sub>R x) = 1\<close>
      by auto
    hence \<open>norm (f (inverse (norm x) *\<^sub>R x)) \<le> K\<close>
      using \<open>\<And> x. norm x = 1 \<Longrightarrow> norm (f x) \<le> K\<close>
      by blast
    hence \<open>norm (inverse (norm x) *\<^sub>R  (f x)) \<le> K\<close>
      by (simp add: assms(1) linear_scale)
    hence \<open>\<bar>inverse (norm x)\<bar> * norm (f x) \<le> K\<close>
      by simp
    hence \<open>inverse (norm x) * norm (f x) \<le> K\<close>
      using \<open>norm x > 0\<close>
      by simp
    have t1: \<open>inverse (norm x) \<ge> 0\<close>
      using \<open>norm x > 0\<close>
      by simp
    have t2: \<open>norm (f x) \<ge> 0\<close>
      by simp
    have t3: \<open>K \<ge> 0\<close>
      using \<open>inverse (norm x) * norm (f x) \<le> K\<close> \<open>inverse (norm x) \<ge> 0\<close> \<open>norm x > 0\<close> t2
      by (metis \<open>norm (f (x /\<^sub>R norm x)) \<le> K\<close> dual_order.trans norm_ge_zero)
    have t4: "\<forall>r. norm x * (inverse (norm x) * r) = r"
      by (metis \<open>norm (x /\<^sub>R norm x) = 1\<close> ab_semigroup_mult_class.mult_ac(1) abs_inverse abs_norm_cancel mult.commute mult.left_neutral norm_scaleR)
    hence t5: "norm (f x) \<le> K * norm x"
      by (metis (no_types) \<open>inverse (norm x) * norm (f x) \<le> K\<close> mult.commute norm_ge_zero real_scaleR_def scaleR_left_mono)
    show ?thesis
      using mult.commute
      by (simp add: mult.commute t5)
  qed
  thus ?thesis using \<open>linear f\<close> unfolding bounded_linear_def bounded_linear_axioms_def by blast
qed

lemma norm_unit_sphere:
  includes notation_norm
  fixes f::\<open>'a::{real_normed_vector,not_singleton} \<Rightarrow>\<^sub>L 'b::real_normed_vector\<close>
  assumes a1: "bounded_linear f" and a2: "e > 0"     
  shows \<open>\<exists>x\<in>(sphere 0 1). \<parallel> \<parallel>f *\<^sub>v x\<parallel> - \<parallel>f\<parallel> \<parallel> < e\<close>
proof-
  define S::"real set" where \<open>S = { norm (f x)| x. x \<in> sphere 0 1 }\<close>
  have "\<exists>x::'a. \<parallel>x\<parallel> = 1"
    by (simp add: ex_norm1)    
  hence \<open>\<exists>x::'a. x \<in> sphere 0 1\<close>
    by simp                
  hence \<open>S\<noteq>{}\<close>unfolding S_def 
    by auto 
  hence t1: \<open>e > 0 \<Longrightarrow> \<exists> y \<in> S. Sup S - e < y\<close>
    for e
    by (simp add: less_cSupD)
  have \<open>onorm f = Sup { norm (f x)| x. norm x = 1 }\<close>
    using \<open>bounded_linear f\<close> onorm_sphere
    by auto      
  hence \<open>onorm f = Sup { norm (f x)| x. x \<in> sphere 0 1 }\<close>
    unfolding sphere_def
    by simp
  hence t2: \<open>Sup S = onorm f\<close> unfolding S_def 
    by auto
  have s1: \<open>\<exists>y\<in>{norm (f x) |x. x \<in> sphere 0 1}. norm (onorm f - y) < e\<close>
    if "0 < e"
    for e
  proof-
    have \<open>\<exists> y \<in> S. (onorm f) - e < y\<close>
      using t1 t2 that by auto
    hence \<open>\<exists> y \<in> S. (onorm f) - y  < e\<close>
      using that
      by force
    have \<open>\<exists> y \<in> S. (onorm f) - y  < e\<close>
      using \<open>0 < e\<close> \<open>\<exists>y\<in>S. onorm f - y < e\<close> by auto
    then obtain y where \<open>y \<in> S\<close> and \<open>(onorm f) - y  < e\<close>
      by blast
    have \<open>y \<in> {norm (f x) |x. x \<in> sphere 0 1} \<Longrightarrow> y \<le> onorm f\<close>
    proof-
      assume \<open>y \<in> {norm (f x) |x. x \<in> sphere 0 1}\<close>
      hence \<open>\<exists> x \<in> sphere 0 1. y = norm (f x)\<close>
        by blast
      then obtain x where \<open>x \<in> sphere 0 1\<close> and \<open>y = norm (f x)\<close>
        by blast
      from \<open>y = norm (f x)\<close>
      have \<open>y \<le> onorm f * norm x\<close>
        using a1 onorm by auto
      moreover have \<open>norm x = 1\<close>
        using  \<open>x \<in> sphere 0 1\<close> unfolding sphere_def by auto
      ultimately show ?thesis by simp
    qed
    hence \<open>bdd_above {norm (f x) |x. x \<in> sphere 0 1}\<close>
      using a1 bdd_above_norm_f by force
    hence \<open>bdd_above S\<close> unfolding S_def 
      by blast
    hence \<open>y \<le> Sup S\<close>
      using \<open>y \<in> S\<close> \<open>S \<noteq> {}\<close> cSup_upper
      by blast
    hence \<open>0 \<le> Sup S - y\<close>
      by simp
    hence \<open>0 \<le> onorm f - y\<close>
      using \<open>Sup S = onorm f\<close>
      by simp
    hence \<open>\<bar> (onorm f - y) \<bar> = onorm f - y\<close>
      by simp
    hence \<open>norm (onorm f - y)  = onorm f - y\<close>
      by auto
    hence \<open>\<exists> y \<in> S. norm ((onorm f) - y)  < e\<close>
      using \<open>onorm f - y < e\<close> \<open>y \<in> S\<close> by force    
    show ?thesis
      unfolding S_def
      using S_def \<open>\<exists>y\<in>S. \<parallel>onorm ((*\<^sub>v) f) - y\<parallel> < e\<close> by blast      
  qed
  have f2: "onorm ((*\<^sub>v) f) = \<Squnion> S"
    using S_def \<open>onorm ((*\<^sub>v) f) = \<Squnion> {\<parallel>f *\<^sub>v x\<parallel> |x. x \<in> sphere 0 1}\<close> by blast
  hence "\<exists>a. \<parallel>\<parallel>f *\<^sub>v a\<parallel> - \<Squnion> S\<parallel> < e \<and> a \<in> sphere 0 1"
    using a1 a2 s1 a2 t2 
    by force 
  thus ?thesis
    using f2 by (metis (full_types) norm_blinfun.rep_eq)  
qed


lemma sphere_nonzero:
  assumes \<open>S \<subseteq> sphere 0 r\<close> and \<open>r > 0\<close> and \<open>x \<in> S\<close>
  shows \<open>x \<noteq> 0\<close>
proof-
  from \<open>S \<subseteq> sphere 0 r\<close> and  \<open>x \<in> S\<close>
  have  \<open>x \<in> sphere 0 r\<close>
    by blast
  hence \<open>dist x 0 = r\<close>
    by (simp add: dist_commute)     
  thus ?thesis using \<open>r > 0\<close>
    by auto
qed

subsection\<open>Unclassified\<close>

lemma complete_singleton: 
  "complete {s::'a::uniform_space}"
proof-
  have "\<And>F. F \<le> principal {s} \<Longrightarrow>
         F \<noteq> \<bottom> \<Longrightarrow> cauchy_filter F \<Longrightarrow> F \<le> nhds s"
    by (meson dual_order.trans empty_subsetI insert_subset le_nhds le_principal principal_le_iff)
  thus ?thesis
    unfolding complete_uniform
    by simp
qed

lemma onormI:
  assumes "\<And>x. norm (f x) \<le> b * norm x"
    and "x \<noteq> 0" and "norm (f x) = b * norm x"
  shows "onorm f = b"
proof (unfold onorm_def, rule cSup_eq_maximum)
  from assms(2) have "norm x \<noteq> 0"
    by auto
  with assms(3) 
  have "norm (f x) / norm x = b"
    by auto
  thus "b \<in> range (\<lambda>x. norm (f x) / norm x)"
    by auto
next
  fix y 
  assume "y \<in> range (\<lambda>x. norm (f x) / norm x)"
  then obtain x where y_def: "y = norm (f x) / norm x"
    by auto
  thus "y \<le> b"
    unfolding y_def using assms(1)[of x]
    by (metis assms(2) assms(3) divide_eq_0_iff linordered_field_class.pos_divide_le_eq norm_ge_zero norm_zero zero_less_norm_iff)
qed

lemmas has_derivative_of_real [derivative_intros] = bounded_linear.has_derivative[OF bounded_linear_of_real]

lemma cmod_Re:
  assumes "x \<ge> 0"
  shows "cmod x = Re x"
  using assms unfolding less_eq_complex_def cmod_def
  by auto


lemma class_not_singletonI_monoid_add:
  assumes "(UNIV::'a set) \<noteq> 0"
  shows "class.not_singleton TYPE('a::monoid_add)"
proof intro_classes
  let ?univ = "UNIV :: 'a set"
  from assms obtain x::'a where "x \<noteq> 0"
    by auto
  thus "\<exists>x y :: 'a. x \<noteq> y"
    by auto
qed

instantiation unit :: CARD_1
begin
instance 
  proof standard
  show "card (UNIV::unit set) = 1"
    by auto
qed 

end

lemma abs_complex_real[simp]: "abs x \<in> \<real>" for x :: complex
  by (simp add: abs_complex_def)

lemma Im_abs[simp]: "Im (abs x) = 0"
  using abs_complex_real complex_is_Real_iff by blast

fun index_of where
  "index_of x [] = (0::nat)"
| "index_of x (y#ys) = (if x=y then 0 else (index_of x ys + 1))"

definition "enum_idx (x::'a::enum) = index_of x (enum_class.enum :: 'a list)"

lemma index_of_correct:
  assumes "x \<in> set y"
  shows "y ! index_of x y = x"
  using assms 
proof(induction y arbitrary: x)
  case Nil
  thus ?case by auto
next
  case (Cons a y)
  thus ?case by auto
qed

lemma enum_idx_correct: 
  "Enum.enum ! enum_idx i = i"
proof-
  have "i \<in> set enum_class.enum"
    using UNIV_enum by blast 
  thus ?thesis
    unfolding enum_idx_def
    using index_of_correct by metis
qed

lemma index_of_bound: 
  assumes "y \<noteq> []" and "x \<in> set y"
  shows "index_of x y < length y"
  using assms proof(induction y arbitrary: x)
  case Nil
  thus ?case by auto
next
  case (Cons a y)
  show ?case 
  proof(cases "a = x")
    case True
    thus ?thesis by auto
  next
    case False
    moreover have "a \<noteq> x \<Longrightarrow> index_of x y < length y"
      using Cons.IH Cons.prems(2) by fastforce      
    ultimately show ?thesis by auto
  qed
qed

lemma enum_idx_bound: "enum_idx x < length (Enum.enum :: 'a list)" for x :: "'a::enum"
proof-
  have p1: "False"
    if "(Enum.enum :: 'a list) = []"
  proof-
    have "(UNIV::'a set) = set ([]::'a list)"
      using that UNIV_enum by metis
    also have "\<dots> = {}"
      by blast
    finally have "(UNIV::'a set) = {}".
    thus ?thesis by simp
  qed    
  have p2: "x \<in> set (Enum.enum :: 'a list)"
    using UNIV_enum by auto
  moreover have "(enum_class.enum::'a list) \<noteq> []"
    using p2 by auto
  ultimately show ?thesis
    unfolding enum_idx_def     
    using index_of_bound [where x = x and y = "(Enum.enum :: 'a list)"]
    by auto   
qed

lemma index_of_nth:
  assumes "distinct xs"
  assumes "i < length xs"
  shows "index_of (xs ! i) xs = i"
  using assms
  by (metis gr_implies_not_zero index_of_bound index_of_correct length_0_conv nth_eq_iff_index_eq nth_mem)

lemma enum_idx_enum: 
  assumes \<open>i < CARD('a::enum)\<close>
  shows \<open>enum_idx (enum_class.enum ! i :: 'a) = i\<close>
  unfolding enum_idx_def apply (rule index_of_nth)
  using assms by (simp_all add: card_UNIV_length_enum enum_distinct)

lemma cnj_x_x: "cnj x * x = (abs x)\<^sup>2"
  proof (cases x)
  show "cnj x * x = \<bar>x\<bar>\<^sup>2"
    if "x = Complex x1 x2"
    for x1 :: real
      and x2 :: real
    using that   by (auto simp: complex_cnj complex_mult abs_complex_def 
        complex_norm power2_eq_square complex_of_real_def)
qed

lemma cnj_x_x_geq0[simp]: "cnj x * x \<ge> 0"
  proof (cases x)
  show "0 \<le> cnj x * x"
    if "x = Complex x1 x2"
    for x1 :: real
      and x2 :: real
    using that by (auto simp: complex_cnj complex_mult complex_of_real_def less_eq_complex_def)
qed


lemma map_filter_map: "List.map_filter f (map g l) = List.map_filter (f o g) l"
proof (induction l)
  show "List.map_filter f (map g []) = List.map_filter (f \<circ> g) []"
    by (simp add: map_filter_simps)
  show "List.map_filter f (map g (a # l)) = List.map_filter (f \<circ> g) (a # l)"
    if "List.map_filter f (map g l) = List.map_filter (f \<circ> g) l"
    for a :: 'c
      and l :: "'c list"
    using that  map_filter_simps(1)
    by (metis comp_eq_dest_lhs list.simps(9))
qed


lemma map_filter_Some[simp]: "List.map_filter (\<lambda>x. Some (f x)) l = map f l"
  proof (induction l)
  show "List.map_filter (\<lambda>x. Some (f x)) [] = map f []"
    by (simp add: map_filter_simps)
  show "List.map_filter (\<lambda>x. Some (f x)) (a # l) = map f (a # l)"
    if "List.map_filter (\<lambda>x. Some (f x)) l = map f l"
    for a :: 'b
      and l :: "'b list"
    using that by (simp add: map_filter_simps(1))
qed

lemma filter_Un: "Set.filter f (x \<union> y) = Set.filter f x \<union> Set.filter f y"
  unfolding Set.filter_def by auto

lemma Set_filter_unchanged: "Set.filter P X = X" if "\<And>x. x\<in>X \<Longrightarrow> P x" for P and X :: "'z set"
  using that unfolding Set.filter_def by auto

end

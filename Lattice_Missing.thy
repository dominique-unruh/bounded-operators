section \<open>TODO: section title\<close>

theory Lattice_Missing
  imports Complex_Main  HOL.Lattices HOL.Complete_Lattices
begin

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
  "class.complemented_lattice (\<lambda>x y. x \<squnion> - y) uminus sup greater_eq greater inf \<top> \<bottom>"
  apply (rule class.complemented_lattice.intro)
  apply (rule dual_bounded_lattice)
  by (unfold_locales, auto simp add: diff_eq)

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
  apply (rule class.orthocomplemented_lattice.intro)
  apply (rule dual_complemented_lattice)
  by (unfold_locales, auto simp add: diff_eq intro: ortho_antimono)

lemma compl_eq_compl_iff [simp]: "- x = - y \<longleftrightarrow> x = y"
proof
  assume "- x = - y"
  hence "- (- x) = - (- y)" by (rule arg_cong)
  thus "x = y" by simp
next
  assume "x = y"
  thus "- x = - y" by simp
qed

lemma compl_bot_eq [simp]: "- bot = top"
proof -
  from sup_compl_top 
  have "sup bot (- bot) = top"
    by simp
  thus ?thesis
    by (metis local.sup_bot.left_neutral) 
qed

lemma compl_top_eq [simp]: "- top = bot"
proof -
  from inf_compl_bot 
  have "inf top (- top) = bot"
    by simp
  thus ?thesis
    by (metis local.inf_top_left)    
qed

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
  then have 2: \<open>-x \<sqinter> -y \<le> - (x \<squnion> y)\<close>
    using ortho_antimono by fastforce
  from 1 2 show ?thesis
    by (simp add: eq_iff)
qed

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
proof -
  from assms 
  have "- (- x) \<le> - y" 
    by (simp only: compl_le_compl_iff)
  thus ?thesis 
    by simp
qed

lemma compl_le_swap2:
  assumes "- y \<le> x"
  shows "- x \<le> y"
proof -
  from assms 
  have "- x \<le> - (- y)" 
    by (simp only: compl_le_compl_iff)
  thus ?thesis by simp
qed

lemma compl_less_compl_iff[simp]: "- x < - y \<longleftrightarrow> y < x"
  by (auto simp add: less_le)

lemma compl_less_swap1:
  assumes "y < - x"
  shows "x < - y"
proof -
  from assms have "- (- x) < - y" by (simp only: compl_less_compl_iff)
  then show ?thesis by simp
qed

lemma compl_less_swap2:
  assumes "- y < x"
  shows "- x < y"
proof -
  from assms have "- x < - (- y)"
    by (simp only: compl_less_compl_iff)
  then show ?thesis by simp
qed

lemma sup_cancel_left1: "sup (sup x a) (sup (- x) b) = top"
  by (simp add: inf_sup_aci sup_compl_top)

lemma sup_cancel_left2: "sup (sup (- x) a) (sup x b) = top"
  by (simp add: inf_sup_aci sup_compl_top)

lemma inf_cancel_left1: "inf (inf x a) (inf (- x) b) = bot"
  by (simp add: inf_sup_aci inf_compl_bot)

lemma inf_cancel_left2: "inf (inf (- x) a) (inf x b) = bot"
  by (simp add: inf_sup_aci inf_compl_bot)

declare inf_compl_bot [simp]
  and sup_compl_top [simp]

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
  apply (rule class.orthomodular_lattice.intro)
  apply (rule dual_orthocomplemented_lattice)
  apply (unfold_locales)
  using local.compl_eq_compl_iff local.ortho_antimono local.orthomodular by fastforce
end

class complete_orthomodular_lattice = orthomodular_lattice + complete_lattice begin

end

instance complete_orthomodular_lattice \<subseteq> complete_orthocomplemented_lattice
  by intro_classes


instance boolean_algebra \<subseteq> orthomodular_lattice
proof
(* TODO: "fix x y :: 'a" and then remove "for x :: 'a" everywhere *)
  show "inf (x::'a) (- x) = bot"
    for x :: 'a
    by simp    
  show "sup (x::'a) (- x) = top"
    for x :: 'a
    by simp
  show "- (- (x::'a)) = x"
    for x :: 'a
    by simp
  show "- (y::'a) \<le> - x"
    if "(x::'a) \<le> y"
    for x :: 'a
      and y :: 'a
    using that
    by simp 
  show "sup (x::'a) (inf (- x) y) = y"
    if "(x::'a) \<le> y"
    for x :: 'a
      and y :: 'a
    using that
    by (simp add: sup.absorb_iff2 sup_inf_distrib1) 

  show "x - y = inf x (- y)"
    for x :: 'a
      and y :: 'a
    by (simp add: boolean_algebra_class.diff_eq)
qed

instance complete_boolean_algebra \<subseteq> complete_orthomodular_lattice
  by intro_classes

unbundle no_lattice_notation

end
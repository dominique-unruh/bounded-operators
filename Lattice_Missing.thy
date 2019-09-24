theory Lattice_Missing
  imports Complex_Main  HOL.Lattices HOL.Complete_Lattices

begin

(* Following https://en.wikipedia.org/wiki/Complemented_lattice#Definition_and_basic_properties 
   and using the conventions from the definition of @{class boolean_algebra} *)
(* TODO: inf_compl_bot, sup_compl_bot should be [simp] *)
class complemented_lattice = bounded_lattice + uminus + minus + 
  assumes inf_compl_bot: "inf x (-x) = bot"
    and sup_compl_top: "sup x  (-x) = top"
    and diff_eq:  "x - y = inf x (- y)"

class complete_complemented_lattice = complemented_lattice + complete_lattice 

(* Following https://en.wikipedia.org/wiki/Complemented_lattice#Orthocomplementation *)
(* TODO: ortho_involution should be [simp] *)
class orthocomplemented_lattice = complemented_lattice +
  assumes ortho_involution: "- (- x) = x" (* TODO: add [simp] *)
    and ortho_antimono: "x \<le> y \<Longrightarrow> -x \<ge> -y" begin

(*

TODO Prove all the lemmas in the comment below unless they don't hold for orthocomplemented_lattice.
     If they don't hold for orthocomplemented_lattice, prove them in orthomodular_lattice.
     If they don't hold there, comment them out with "TODO: Dominique should check"

In some cases, the existing proofs might work (copied from boolean_lattice) 
but in some cases new proofs will be needed

*)

(*

lemma compl_inf_bot [simp]: "- x \<sqinter> x = \<bottom>"
  by (simp add: inf_commute inf_compl_bot)

lemma compl_sup_top [simp]: "- x \<squnion> x = \<top>"
  by (simp add: sup_commute sup_compl_top)

lemma compl_unique:
  assumes "x \<sqinter> y = \<bottom>"
    and "x \<squnion> y = \<top>"
  shows "- x = y"
proof -
  have "(x \<sqinter> - x) \<squnion> (- x \<sqinter> y) = (x \<sqinter> y) \<squnion> (- x \<sqinter> y)"
    using inf_compl_bot assms(1) by simp
  then have "(- x \<sqinter> x) \<squnion> (- x \<sqinter> y) = (y \<sqinter> x) \<squnion> (y \<sqinter> - x)"
    by (simp add: inf_commute)
  then have "- x \<sqinter> (x \<squnion> y) = y \<sqinter> (x \<squnion> - x)"
    by (simp add: inf_sup_distrib1)
  then have "- x \<sqinter> \<top> = y \<sqinter> \<top>"
    using sup_compl_top assms(2) by simp
  then show "- x = y" by simp
qed

lemma double_compl [simp]: "- (- x) = x"
  using compl_inf_bot compl_sup_top by (rule compl_unique)

lemma compl_eq_compl_iff [simp]: "- x = - y \<longleftrightarrow> x = y"
proof
  assume "- x = - y"
  then have "- (- x) = - (- y)" by (rule arg_cong)
  then show "x = y" by simp
next
  assume "x = y"
  then show "- x = - y" by simp
qed

lemma compl_bot_eq [simp]: "- \<bottom> = \<top>"
proof -
  from sup_compl_top have "\<bottom> \<squnion> - \<bottom> = \<top>" .
  then show ?thesis by simp
qed

lemma compl_top_eq [simp]: "- \<top> = \<bottom>"
proof -
  from inf_compl_bot have "\<top> \<sqinter> - \<top> = \<bottom>" .
  then show ?thesis by simp
qed

lemma compl_inf [simp]: "- (x \<sqinter> y) = - x \<squnion> - y"
proof (rule compl_unique)
  have "(x \<sqinter> y) \<sqinter> (- x \<squnion> - y) = (y \<sqinter> (x \<sqinter> - x)) \<squnion> (x \<sqinter> (y \<sqinter> - y))"
    by (simp only: inf_sup_distrib inf_aci)
  then show "(x \<sqinter> y) \<sqinter> (- x \<squnion> - y) = \<bottom>"
    by (simp add: inf_compl_bot)
next
  have "(x \<sqinter> y) \<squnion> (- x \<squnion> - y) = (- y \<squnion> (x \<squnion> - x)) \<sqinter> (- x \<squnion> (y \<squnion> - y))"
    by (simp only: sup_inf_distrib sup_aci)
  then show "(x \<sqinter> y) \<squnion> (- x \<squnion> - y) = \<top>"
    by (simp add: sup_compl_top)
qed

lemma compl_sup [simp]: "- (x \<squnion> y) = - x \<sqinter> - y"
  using dual_boolean_algebra
  by (rule boolean_algebra.compl_inf)

lemma compl_mono:
  assumes "x \<le> y"
  shows "- y \<le> - x"
proof -
  from assms have "x \<squnion> y = y" by (simp only: le_iff_sup)
  then have "- (x \<squnion> y) = - y" by simp
  then have "- x \<sqinter> - y = - y" by simp
  then have "- y \<sqinter> - x = - y" by (simp only: inf_commute)
  then show ?thesis by (simp only: le_iff_inf)
qed

lemma compl_le_compl_iff [simp]: "- x \<le> - y \<longleftrightarrow> y \<le> x"
  by (auto dest: compl_mono)

lemma compl_le_swap1:
  assumes "y \<le> - x"
  shows "x \<le> -y"
proof -
  from assms have "- (- x) \<le> - y" by (simp only: compl_le_compl_iff)
  then show ?thesis by simp
qed

lemma compl_le_swap2:
  assumes "- y \<le> x"
  shows "- x \<le> y"
proof -
  from assms have "- x \<le> - (- y)" by (simp only: compl_le_compl_iff)
  then show ?thesis by simp
qed

lemma compl_less_compl_iff: "- x < - y \<longleftrightarrow> y < x"  (* TODO: declare [simp] ? *)
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

*)

end

class complete_orthocomplemented_lattice = orthocomplemented_lattice + complete_lattice

instance complete_orthocomplemented_lattice \<subseteq> complete_complemented_lattice
  by intro_classes

(* Following https://en.wikipedia.org/wiki/Complemented_lattice#Orthomodular_lattices *)
class orthomodular_lattice = orthocomplemented_lattice +
  assumes orthomodular: "x \<le> y \<Longrightarrow> sup x (inf (-x) y) = y"

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

(* TODO: verify whether or not it is true
lemma demorgan_inf: "- (inf (A::_::orthocomplemented_lattice) B) = sup (- A) (- B)"
*)

(* TODO: verify whether or not it is true
lemma demorgan_sup: "- (sup (A::_::orthocomplemented_lattice)  B) = inf (- A)  (- B)"
*)

end
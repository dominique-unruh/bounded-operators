theory Lattice_Missing
  imports HOL.Lattices HOL.Complete_Lattices

begin

(* Following https://en.wikipedia.org/wiki/Complemented_lattice#Definition_and_basic_properties 
   and using the conventions from the definition of @{class boolean_algebra} *)
class complemented_lattice = bounded_lattice + uminus + minus + 
  assumes inf_compl_bot: "inf x (-x) = bot"
    and sup_compl_top: "sup x (-x) = top"

class complete_complemented_lattice = complemented_lattice + complete_lattice 

(* Following https://en.wikipedia.org/wiki/Complemented_lattice#Orthocomplementation *)
class orthocomplemented_lattice = complemented_lattice +
  assumes ortho_involution: "- (- x) = x"
    and ortho_antimono: "x \<le> y \<Longrightarrow> -x \<ge> -y"

class complete_orthocomplemented_lattice = orthocomplemented_lattice + complete_lattice

instance complete_orthocomplemented_lattice \<subseteq> complete_complemented_lattice
  by intro_classes

(* Following https://en.wikipedia.org/wiki/Complemented_lattice#Orthomodular_lattices *)
class orthomodular_lattice = orthocomplemented_lattice +
  assumes orthomodular: "x \<le> y \<Longrightarrow> sup x (inf (-x) y) = y"

class complete_orthomodular_lattice = orthomodular_lattice + complete_lattice

instance complete_orthomodular_lattice \<subseteq> complete_orthocomplemented_lattice
  by intro_classes

instance boolean_algebra \<subseteq> orthomodular_lattice
proof
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
qed


instance complete_boolean_algebra \<subseteq> complete_orthomodular_lattice
  by intro_classes


end
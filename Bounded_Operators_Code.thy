section \<open>\<open>Bounded_Operators_Code\<close> -- Support for code generation\<close>

theory Bounded_Operators_Code
  imports
    Bounded_Operators_Matrices 
begin


unbundle jnf_notation
unbundle cblinfun_notation

subsection \<open>Code equations for cblinfun operators\<close>

text \<open>In this subsection, we define the code for all operations involving only 
  operators (no combinations of operators/vectors/subspaces)\<close>

text \<open>This lemma defines addition. By writing \<^term>\<open>mat_of_cblinfun (M + N)\<close>
on the left hand side, we get access to the\<close>
lemma cblinfun_of_mat_plusOp[code]:
  "mat_of_cblinfun (F + G) = mat_of_cblinfun F + mat_of_cblinfun G"
  for F G::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum"
  using cblinfun_of_mat_plusOp'.

lemma cblinfun_of_mat_id[code]:
  "mat_of_cblinfun (idOp :: ('a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L'a)) = 1\<^sub>m (canonical_basis_length TYPE('a))"
  using cblinfun_of_mat_id'.

lemma mat_of_cblinfun_zero[code]:
  "mat_of_cblinfun (0 :: ('a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum)) 
  = 0\<^sub>m (canonical_basis_length TYPE('b)) (canonical_basis_length TYPE('a))"
  using mat_of_cblinfun_zero'.

lemma cblinfun_of_mat_uminusOp[code]:
  "mat_of_cblinfun (- M) = - mat_of_cblinfun M" 
  for M::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum"
  using cblinfun_of_mat_uminusOp'.

lemma cblinfun_of_mat_minusOp[code]:
  "mat_of_cblinfun (M - N) = mat_of_cblinfun M - mat_of_cblinfun N" 
  for M::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum" and N::"'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b"
  using cblinfun_of_mat_minusOp'.

lemma cblinfun_of_mat_timesOp[code]:
  "mat_of_cblinfun (F o\<^sub>C\<^sub>L G) = mat_of_cblinfun F * mat_of_cblinfun G" 
  for F::"'b::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'c::onb_enum" and G::"'a::onb_enum  \<Rightarrow>\<^sub>C\<^sub>L 'b"
(* TODO: move proof to Bounded_Operators_Matrices *)
proof -
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"
  define nC where "nC = canonical_basis_length TYPE('c)"
  have a3: "mat_of_cblinfun F \<in> carrier_mat nC nB"
    unfolding nC_def nB_def mat_of_cblinfun_def
    by simp
  moreover have a2: "mat_of_cblinfun G \<in> carrier_mat nB nA"
    unfolding nB_def nA_def mat_of_cblinfun_def
    by simp
  ultimately have a1: "mat_of_cblinfun F * mat_of_cblinfun G \<in> carrier_mat nC nA"
    using Matrix.mult_carrier_mat[where A = "mat_of_cblinfun F" and B = "mat_of_cblinfun G" 
        and nr = nC and n = nB and nc = nA] 
    by blast
  have "cblinfun_of_mat (mat_of_cblinfun F * mat_of_cblinfun G)
      = ((cblinfun_of_mat (mat_of_cblinfun F))::'b\<Rightarrow>\<^sub>C\<^sub>L'c) o\<^sub>C\<^sub>L 
        ((cblinfun_of_mat (mat_of_cblinfun G))::'a\<Rightarrow>\<^sub>C\<^sub>L'b)"
    using mat_of_cblinfun_timesOp a2 a3 nA_def nB_def nC_def by blast
  moreover have "((cblinfun_of_mat (mat_of_cblinfun F))::'b\<Rightarrow>\<^sub>C\<^sub>L'c) = F"
    by (simp add: mat_of_cblinfun_inverse)    
  moreover have "((cblinfun_of_mat (mat_of_cblinfun G))::'a\<Rightarrow>\<^sub>C\<^sub>L'b) = G"
    by (simp add: mat_of_cblinfun_inverse)    
  ultimately have "F o\<^sub>C\<^sub>L G = cblinfun_of_mat (mat_of_cblinfun F * mat_of_cblinfun G)"
    by simp
  hence "mat_of_cblinfun (F o\<^sub>C\<^sub>L G) 
    = mat_of_cblinfun ((cblinfun_of_mat::complex mat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'c) 
                        (mat_of_cblinfun F * mat_of_cblinfun G))"
    by simp
  moreover have "mat_of_cblinfun ((cblinfun_of_mat::complex mat \<Rightarrow> 'a \<Rightarrow>\<^sub>C\<^sub>L 'c) 
                        (mat_of_cblinfun F * mat_of_cblinfun G))
        = mat_of_cblinfun F * mat_of_cblinfun G"
    using a1 cblinfun_of_mat_inverse
    by (simp add: cblinfun_of_mat_inverse nA_def nC_def)
  ultimately show ?thesis by simp
qed


lemma mat_of_cblinfun_scalarMult[code]:
  "mat_of_cblinfun ((a::complex) *\<^sub>C F) = a \<cdot>\<^sub>m (mat_of_cblinfun F)"
  for F :: "'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
(* TODO: move proof to Bounded_Operators_Matrices *)
proof -
  define nA where "nA = canonical_basis_length TYPE('a)"
  define nB where "nB = canonical_basis_length TYPE('b)"
  define BasisA where "BasisA = (canonical_basis::'a list)"
  define BasisB where "BasisB = (canonical_basis::'b list)"

  define G where "G = (a::complex) *\<^sub>C (idOp:: 'b \<Rightarrow>\<^sub>C\<^sub>L 'b)"
  have w1: "a *\<^sub>C F = G o\<^sub>C\<^sub>L F"
    unfolding G_def
    by simp
  have "\<langle>BasisB ! i, BasisB ! j\<rangle> = (if i = j then 1 else 0)"
    if "i < nB" and "j < nB"
    for i j
  proof(cases "i = j")
    case True
    have "BasisB!i \<in> set BasisB"
      using that(1) unfolding nB_def BasisB_def
      by (simp add: canonical_basis_length_eq) 
    hence "norm (BasisB!i) = 1"
      using is_onb_set that(1)
      unfolding BasisB_def is_onb_def
      by auto
    hence "(norm (BasisB!i))^2 = 1"
      by simp
    thus ?thesis
      by (metis True of_real_hom.hom_one power2_norm_eq_cinner') 
  next
    case False
    moreover have "distinct BasisB"
      unfolding BasisB_def
      by simp
    ultimately have "BasisB!i \<noteq> BasisB!j"
      using that unfolding nB_def
      by (simp add: BasisB_def canonical_basis_length_eq nth_eq_iff_index_eq) 
    moreover have "BasisB!i \<in> set BasisB"
      using that(1) unfolding nB_def BasisB_def
      by (simp add: canonical_basis_length_eq) 
    moreover have "BasisB!j \<in> set BasisB"
      using that(2) unfolding nB_def BasisB_def
      by (simp add: canonical_basis_length_eq) 
    ultimately show ?thesis 
      using is_onb_set
      unfolding BasisB_def nB_def is_onb_def is_ob_def is_ortho_set_def      
      by auto
  qed

  hence w2: "mat_of_cblinfun G = a \<cdot>\<^sub>m (1\<^sub>m nB)"
    unfolding BasisB_def nB_def mat_of_cblinfun_def G_def smult_mat_def one_mat_def
    by auto
  have w3: "1\<^sub>m nB \<in> carrier_mat nB nB"
    unfolding nB_def  mat_of_cblinfun_def by auto
  have w4: "mat_of_cblinfun F \<in> carrier_mat nB nA"
    unfolding nB_def nA_def mat_of_cblinfun_def by auto
  have w5: "(1\<^sub>m nB) * (mat_of_cblinfun F) = (mat_of_cblinfun F)"
    using w4 by auto    
  have "mat_of_cblinfun (a *\<^sub>C F) = mat_of_cblinfun (G o\<^sub>C\<^sub>L F)"
    using w1
    by simp
  also have "\<dots> = (mat_of_cblinfun G)* (mat_of_cblinfun F)"
    by (simp add: cblinfun_of_mat_timesOp)
  also have "\<dots> = (a \<cdot>\<^sub>m (1\<^sub>m nB)) * (mat_of_cblinfun F)"
    using w2 by simp
  also have "\<dots> = a \<cdot>\<^sub>m ((1\<^sub>m nB) * (mat_of_cblinfun F))"
    using Matrix.mult_smult_distrib w4 by auto
  also have "\<dots> = a \<cdot>\<^sub>m (mat_of_cblinfun F)"
    by (simp add: w5)
  finally show ?thesis .
qed

text \<open>This instantiation defines a code equation for equality tests for cblinfun operators.\<close>
instantiation cblinfun :: (onb_enum,onb_enum) equal begin
definition [code]: "equal_cblinfun M N \<longleftrightarrow> mat_of_cblinfun M = mat_of_cblinfun N" 
  for M N :: "'a \<Rightarrow>\<^sub>C\<^sub>L 'b"
instance 
  apply intro_classes
  unfolding equal_cblinfun_def 
  using mat_of_cblinfun_inj injD by fastforce
end

lemma cblinfun_of_mat_adjoint[code]:
  "mat_of_cblinfun (F*) = adjoint_mat (mat_of_cblinfun F)"
  for F :: "'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L 'b::onb_enum"
(* TODO: move proof to Bounded_Operators_Matrices *)
proof -
  define nA where "nA = canonical_basis_length TYPE('a::onb_enum)" 
  define nB where "nB = canonical_basis_length TYPE('b::onb_enum)" 
  define M  where "M = mat_of_cblinfun F"
  have b1: "M \<in> carrier_mat nB nA"
    by (metis M_def add.right_neutral add_carrier_mat cblinfun_of_mat_plusOp mat_of_cblinfun_zero
        nA_def nB_def zero_carrier_mat)
  hence b2: "adjoint_mat M \<in> carrier_mat nA nB"
    unfolding adjoint_mat_def
    by simp
  hence "((cblinfun_of_mat M)::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum)* 
  = ((cblinfun_of_mat (adjoint_mat M)):: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
    using b1 mat_of_cblinfun_adjoint nA_def nB_def by metis
  hence "((cblinfun_of_mat (mat_of_cblinfun F))::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum)* 
  = ((cblinfun_of_mat (adjoint_mat (mat_of_cblinfun F))):: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
    unfolding M_def by simp
  moreover have "((cblinfun_of_mat (mat_of_cblinfun F))::'a::onb_enum \<Rightarrow>\<^sub>C\<^sub>L'b::onb_enum) = F"
    by (simp add: mat_of_cblinfun_inverse)    
  ultimately have "F*  = ((cblinfun_of_mat (adjoint_mat (mat_of_cblinfun F))):: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
    by simp
  hence "mat_of_cblinfun (F*) = mat_of_cblinfun ((cblinfun_of_mat (adjoint_mat (mat_of_cblinfun F))):: 'b \<Rightarrow>\<^sub>C\<^sub>L 'a)"
    by simp
  also have "\<dots> = adjoint_mat (mat_of_cblinfun F)"
    using b2 cblinfun_of_mat_inverse[where M = "adjoint_mat (mat_of_cblinfun F)"]
    by (metis M_def nA_def nB_def)
  finally show ?thesis .
qed

declare mat_of_cblinfun_classical_operator_inj_option[code]


subsection \<open>Miscellanea\<close>

text \<open>This is a hack to circumvent a bug in the code generation. The automatically
  generated code for the class \<^class>\<open>uniformity\<close> has a type that is different from
  what the generated code later assumes, leading to compilation errors (in ML at least)
  in any expression involving \<^typ>\<open>_ ell2\<close> (even if the constant \<^const>\<open>uniformity\<close> is
  not actually used).
  
  The fragment below circumvents this by forcing Isabelle to use the right type.
  (The logically useless fragment "\<open>let x = ((=)::'a\<Rightarrow>_\<Rightarrow>_)\<close>" achieves this.)\<close>
lemma [code]: "(uniformity :: ('a ell2 * _) filter) = Filter.abstract_filter (%_.
    Code.abort STR ''no uniformity'' (%_. 
    let x = ((=)::'a\<Rightarrow>_\<Rightarrow>_) in uniformity))"
  by simp


unbundle no_jnf_notation
unbundle no_cblinfun_notation

end

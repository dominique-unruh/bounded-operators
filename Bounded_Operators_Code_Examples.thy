theory Bounded_Operators_Code_Examples
  imports
    Real_Impl.Real_Impl "HOL-Library.Code_Target_Numeral" Jordan_Normal_Form.Matrix_Impl
  "HOL-ex.Sqrt"
    Bounded_Operators_Code 
begin

hide_const (open) Order.bottom Order.top
no_notation Lattice.join (infixl "\<squnion>\<index>" 65)
no_notation Lattice.meet (infixl "\<sqinter>\<index>" 70)

section \<open>Making output of value more readable\<close>

unbundle cblinfun_notation

lemma two_sqrt_irrat[simp]: "2 \<in> sqrt_irrat"
  using sqrt_prime_irrational[OF two_is_prime_nat]
  unfolding Rats_def sqrt_irrat_def image_def apply auto
proof - (* Sledgehammer proof *)
  fix p :: rat
  assume "p * p = 2"
  hence f1: "(Ratreal p)\<^sup>2 = real 2"
    by (metis Ratreal_def of_nat_numeral of_rat_numeral_eq power2_eq_square real_times_code)
  have "\<forall>r. if 0 \<le> r then sqrt (r\<^sup>2) = r else r + sqrt (r\<^sup>2) = 0"
    by simp
  hence f2: "Ratreal p + sqrt ((Ratreal p)\<^sup>2) = 0"
    using f1 by (metis Ratreal_def Rats_def \<open>sqrt (real 2) \<notin> \<rat>\<close> range_eqI)
  have f3: "sqrt (real 2) + - 1 * sqrt ((Ratreal p)\<^sup>2) \<le> 0"
    using f1 by fastforce
  have f4: "0 \<le> sqrt (real 2) + - 1 * sqrt ((Ratreal p)\<^sup>2)"
    using f1 by force
  have f5: "(- 1 * sqrt (real 2) = real_of_rat p) = (sqrt (real 2) + real_of_rat p = 0)"
    by linarith
  have "\<forall>x0. - (x0::real) = - 1 * x0"
    by auto
  hence "sqrt (real 2) + real_of_rat p \<noteq> 0"
    using f5 by (metis (no_types) Rats_def Rats_minus_iff \<open>sqrt (real 2) \<notin> \<rat>\<close> range_eqI)
  thus False
    using f4 f3 f2 by simp
qed

(* Ensure that complex numbers with zero-imaginary part are rendered as reals *)
lemma [code_post]: 
  shows "Complex a 0 = complex_of_real a"
  and "complex_of_real 0 = 0"
  and "complex_of_real 1 = 1"
  and "complex_of_real (a/b) = complex_of_real a / complex_of_real b"
  and "complex_of_real (numeral n) = numeral n"
  and "complex_of_real (-r) = - complex_of_real r"
  using complex_eq_cancel_iff2 by auto

(* Make real number implementation more readable *)
lemma [code_post]:
  shows "real_of (Abs_mini_alg (p, 0, b)) = real_of_rat p"
  and "real_of (Abs_mini_alg (p, q, 2)) = real_of_rat p + real_of_rat q * sqrt 2"
  and "sqrt 0 = 0"
  and "sqrt (real 0) = 0"
  and "x * (0::real) = 0"
  and "(0::real) * x = 0"
  and "(0::real) + x = x"
  and "x + (0::real) = x"
  and "(1::real) * x = x"
  and "x * (1::real) = x"
  by (auto simp add: eq_onp_same_args real_of.abs_eq)

(* Hide IArray in output *)
translations "x" \<leftharpoondown> "CONST IArray x"

section \<open>Examples\<close>

subsection \<open>Operators\<close>

value "id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "1 :: unit ell2 \<Rightarrow>\<^sub>C\<^sub>L unit ell2"

value "id_cblinfun + id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "0 :: (bool ell2 \<Rightarrow>\<^sub>C\<^sub>L Enum.finite_3 ell2)"

value "- id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "id_cblinfun - id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "classical_operator (\<lambda>b. Some (\<not> b))"

value "id_cblinfun = (0 :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2)"

value "2 *\<^sub>R id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "imaginary_unit *\<^sub>C id_cblinfun :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "id_cblinfun o\<^sub>C\<^sub>L 0 :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "id_cblinfun* :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

subsection \<open>Vectors\<close>

value "0 :: bool ell2"

value "1 :: unit ell2"

value "ket False"

value "2 *\<^sub>C ket False"

value "2 *\<^sub>R ket False"

value "ket True + ket False"

value "ket True - ket True"

value "ket True = ket True"

value "- ket True"

value "cinner (ket True) (ket True)"

value "norm (ket True)"

value "ket () * ket ()"

value "1 :: unit ell2"

value "(1::unit ell2) * (1::unit ell2)"

subsection \<open>Vector/Matrix\<close>

value "id_cblinfun *\<^sub>V ket True"

value \<open>vector_to_cblinfun (ket True) :: unit ell2 \<Rightarrow>\<^sub>C\<^sub>L _\<close>

subsection \<open>Subspaces\<close>

value "ccspan {ket False}"

value "Proj (ccspan {ket False})"

value "top :: bool ell2 ccsubspace"

value "bot :: bool ell2 ccsubspace"

value "0 :: bool ell2 ccsubspace"

value "ccspan {ket False} \<squnion> ccspan {ket True}"

value "ccspan {ket False} + ccspan {ket True}"

value "ccspan {ket False} \<sqinter> ccspan {ket True}"

value "id_cblinfun *\<^sub>S ccspan {ket False}"

value "id_cblinfun *\<^sub>S (top :: bool ell2 ccsubspace)" (* Special case, using range_cblinfun_code for efficiency *)

value "- ccspan {ket False}"

value "ccspan {ket False, ket True} = top"

value "ccspan {ket False} \<le> ccspan {ket True}"

value "cblinfun_image id_cblinfun (ccspan {ket True})"

value "kernel id_cblinfun :: bool ell2 ccsubspace"

value "eigenspace 1 id_cblinfun :: bool ell2 ccsubspace"

value "Inf {ccspan {ket False}, top}"

value "Sup {ccspan {ket False}, top}"

end

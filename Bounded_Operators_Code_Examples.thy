theory Bounded_Operators_Code_Examples
  imports
    Real_Impl.Real_Impl "HOL-Library.Code_Target_Numeral" Jordan_Normal_Form.Matrix_Impl
  "HOL-ex.Sqrt"
    Bounded_Operators.Bounded_Operators_Code 
begin

section \<open>Making output of value more readable\<close>

lemma two_sqrt_irrat[simp]: "2 \<in> sqrt_irrat"
  using sqrt_prime_irrational[OF two_is_prime_nat]
  unfolding Rats_def sqrt_irrat_def image_def apply auto
proof - (* Sledgehammer proof *)
  fix p :: rat
  assume "p * p = 2"
  then have f1: "(Ratreal p)\<^sup>2 = real 2"
    by (metis Ratreal_def of_nat_numeral of_rat_numeral_eq power2_eq_square real_times_code)
  have "\<forall>r. if 0 \<le> r then sqrt (r\<^sup>2) = r else r + sqrt (r\<^sup>2) = 0"
    by simp
  then have f2: "Ratreal p + sqrt ((Ratreal p)\<^sup>2) = 0"
    using f1 by (metis Ratreal_def Rats_def \<open>sqrt (real 2) \<notin> \<rat>\<close> range_eqI)
  have f3: "sqrt (real 2) + - 1 * sqrt ((Ratreal p)\<^sup>2) \<le> 0"
    using f1 by fastforce
  have f4: "0 \<le> sqrt (real 2) + - 1 * sqrt ((Ratreal p)\<^sup>2)"
    using f1 by force
  have f5: "(- 1 * sqrt (real 2) = real_of_rat p) = (sqrt (real 2) + real_of_rat p = 0)"
    by linarith
  have "\<forall>x0. - (x0::real) = - 1 * x0"
    by auto
  then have "sqrt (real 2) + real_of_rat p \<noteq> 0"
    using f5 by (metis (no_types) Rats_def Rats_minus_iff \<open>sqrt (real 2) \<notin> \<rat>\<close> range_eqI)
  then show False
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

(* TODO: add an example for every operation that is supported by Bounded_Operators_Code *)

value "idOp :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "idOp + idOp :: bool ell2 \<Rightarrow>\<^sub>C\<^sub>L bool ell2"

value "0 :: (bool ell2 \<Rightarrow>\<^sub>C\<^sub>L Enum.finite_3 ell2)"

end

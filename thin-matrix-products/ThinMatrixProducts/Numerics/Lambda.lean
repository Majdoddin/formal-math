import Statements
import ThinMatrixProducts.Util.Logs

/-!
# `ln Λ_c(γ)`, `R'_c(γ)` and the exponents of Corollary 9.1

The general identities of equation (2), and the constants `γ`, `q`, `Λ` of Corollary 9.1 written
as linear combinations of `ln 2, ln 3, ln 5, ln 7, ln 17, ln 19, ln 23, ln 29`, which the tight
enclosures of `ThinMatrixProducts.Util.Logs` then bound.
-/

namespace ThinMatrixProducts

open Real

/-- `ln (x^y) = y ln x` for `x > 0`, in the form used below. -/
lemma log_rpow' {x : ℝ} (hx : 0 < x) (y : ℝ) : Real.log (x ^ y) = y * Real.log x :=
  Real.log_rpow hx y

lemma LambdaC_pos (c γ : ℝ) : 0 < LambdaC c γ := by
  unfold LambdaC; positivity

/-- Equation (2), the logarithm of `Λ_c(γ)`. -/
lemma log_LambdaC (c γ : ℝ) :
    Real.log (LambdaC c γ) = 2 * c * Real.log 5 - c * H (1 / c) - (c - 1) * Real.log 4
      + γ * Real.log 4 := by
  unfold LambdaC
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    log_rpow' (by norm_num), Real.log_exp, log_rpow' (by norm_num),
    show (25 / 4 : ℝ) = 5 ^ 2 / 4 by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_pow]
  push_cast
  ring

theorem eq_2_forms : Eq_2_forms := by
  intro c γ _
  refine ⟨log_LambdaC c γ, ?_⟩
  rw [RPrime, log_LambdaC, log_four_eq]
  rw [show 2 * c * Real.log 5 - c * H (1 / c) - (c - 1) * (2 * Real.log 2) + γ * (2 * Real.log 2)
      = 2 * (c * Real.log 5 - c / 2 * H (1 / c) - (c - 1) * Real.log 2 + γ * Real.log 2) by ring]
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-! ## Corollary 9.1(a) -/

lemma log_27_8 : Real.log (27 / 8) = 3 * Real.log 3 - 3 * Real.log 2 := by
  rw [show (27 / 8 : ℝ) = 3 ^ 3 / 2 ^ 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow]
  push_cast; ring

lemma gammaA_eq : gammaA = (3 * Real.log 3 - 3 * Real.log 2) / (19 * Real.log 2) := by
  rw [gammaA, Real.logb, log_27_8, div_div, mul_comm (Real.log 2)]

lemma qA_eq : qA = (Real.log 19 - 16 / 19 * Real.log 2 - 36 / 19 * Real.log 3) / Real.log 2 := by
  rw [qA, Real.logb, Real.log_mul (by positivity) (by norm_num), log_rpow' (by norm_num),
    Real.log_div (by norm_num) (by norm_num),
    show (72 : ℝ) = 2 ^ 3 * 3 ^ 2 by norm_num, show (18 : ℝ) = 2 * 3 ^ 2 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow]
  push_cast
  congr 1
  ring

lemma H_one_div_19 : H (1 / 19) = Real.log 19 - 18 / 19 * Real.log 2 - 36 / 19 * Real.log 3 := by
  unfold H
  rw [show (1 : ℝ) - 1 / 19 = 2 * 3 ^ 2 / 19 by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_one]
  push_cast; ring

lemma H_one_div_14_5 :
    H (1 / 14.5) = Real.log 29 - 2 / 29 * Real.log 2 - 81 / 29 * Real.log 3 := by
  unfold H
  rw [show (1 / 14.5 : ℝ) = 2 / 29 by norm_num, show (1 : ℝ) - 2 / 29 = 3 ^ 3 / 29 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_pow]
  push_cast; ring

lemma log_LambdaA : Real.log LambdaA
    = 29 * Real.log 5 - 26 * Real.log 2 - 29 / 2 * Real.log 29 + 81 / 2 * Real.log 3
      + (6 / 19) * (Real.log 3 - Real.log 2) := by
  have h2 := log_two_gt'
  rw [LambdaA, log_LambdaC, H_one_div_14_5, gammaA_eq, log_four_eq]
  field_simp
  ring

theorem corollary_9_1_a_exponents : Corollary_9_1_a_exponents := by
  have h2 := log_two_gt'; have h2' := log_two_lt'
  have h3 := log_three_gt'; have h3' := log_three_lt'
  have h19 := log_nineteen_gt'; have h19' := log_nineteen_lt'
  have p2 : 0 < Real.log 2 := by linarith
  refine ⟨?_, ?_, ?_, ?_, by norm_num, ?_, ?_⟩
  · rw [gammaA_eq, lt_div_iff₀ (by positivity)]; linarith
  · rw [gammaA_eq, div_lt_iff₀ (by positivity)]; linarith
  · rw [qA_eq, lt_div_iff₀ p2]; linarith
  · rw [qA_eq, div_lt_iff₀ p2]; linarith
  · rw [gammaA, gammaOf, show ((14.5 : ℝ) - 1) / 4 = 27 / 8 by norm_num]; ring
  · rw [qA_eq, qOf, H_one_div_19, log_four_eq]; congr 1; ring

/-- `4^γ` for `γ = log₂(27/8)/19` is `(27/8)^{2/19}`. -/
lemma four_rpow_gammaA : (4 : ℝ) ^ gammaA = (27 / 8 : ℝ) ^ (2 / 19 : ℝ) := by
  have p2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num), gammaA, Real.logb,
    log_four_eq]
  congr 1
  field_simp

/-- `ln a = ln (a / 2^k) + k ln 2`, to bound the logarithm of a large number. -/
lemma log_eq_log_div_pow (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Real.log a = Real.log (a / 2 ^ k) + k * Real.log 2 := by
  rw [Real.log_div ha.ne' (by positivity), Real.log_pow]; ring

theorem corollary_9_1_a_Lambda : Corollary_9_1_a_Lambda := by
  have h2 := log_two_gt'; have h2' := log_two_lt'
  have h3 := log_three_gt'; have h3' := log_three_lt'
  have h5 := log_five_gt'; have h5' := log_five_lt'
  have h29 := log_twentynine_gt'; have h29' := log_twentynine_lt'
  have hL := log_LambdaA
  have hpos : 0 < LambdaA := LambdaC_pos 14.5 gammaA
  refine ⟨?_, ?_, ?_, by norm_num, by norm_num, ?_⟩
  · rw [LambdaA, LambdaC, Real.rpow_add (by norm_num), Real.rpow_one, four_rpow_gammaA]; ring
  · rw [← Real.log_lt_log_iff (by norm_num) hpos, log_eq_log_div_pow _ (by norm_num) 35]
    have := (log_mem 0 12 (by norm_num : (0 : ℝ) < 4.1456e10 / 2 ^ 35)).2
    have hb : logApprox 0 12 (4.1456e10 / 2 ^ 35) + logErr 0 12 (4.1456e10 / 2 ^ 35)
        < 0.18774714116808 := by numerics
    push_cast at *
    linarith
  · rw [← Real.log_lt_log_iff hpos (by norm_num), log_eq_log_div_pow (4.1457e10) (by norm_num) 35]
    have := (log_mem 0 12 (by norm_num : (0 : ℝ) < 4.1457e10 / 2 ^ 35)).1
    have hb : 0.18777126283778 < logApprox 0 12 (4.1457e10 / 2 ^ 35) - logErr 0 12 (4.1457e10 / 2 ^ 35) := by
      numerics
    push_cast at *
    linarith
  · have := (log_mem 0 20 (by norm_num : (0 : ℝ) < 1.657)).2
    have hb : logApprox 0 20 1.657 + logErr 0 20 1.657 < 0.50500873844443 := by numerics
    rw [← Real.log_lt_log_iff (by positivity) (by norm_num), Real.log_mul (by norm_num) hpos.ne',
      Real.log_pow, log_four_eq]
    push_cast at *
    linarith

/-! ## Corollary 9.1(b) -/

lemma log_21_8 : Real.log (21 / 8) = Real.log 3 + Real.log 7 - 3 * Real.log 2 := by
  rw [show (21 / 8 : ℝ) = 3 * 7 / 2 ^ 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
  push_cast; ring

lemma gammaB_eq : gammaB = (Real.log 3 + Real.log 7 - 3 * Real.log 2) / (18 * Real.log 2) := by
  rw [gammaB, Real.logb, log_21_8, div_div, mul_comm (Real.log 2)]

lemma qB_eq : qB = (10 / 9 * Real.log 2 + 2 * Real.log 3 - 17 / 18 * Real.log 17) / Real.log 2 := by
  rw [qB, Real.logb, Real.log_mul (by positivity) (by norm_num), log_rpow' (by norm_num),
    Real.log_div (by norm_num) (by norm_num),
    show (68 : ℝ) = 2 ^ 2 * 17 by norm_num, show (18 : ℝ) = 2 * 3 ^ 2 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow]
  push_cast
  congr 1
  ring

lemma H_one_div_18 : H (1 / 18) = Real.log 2 + 2 * Real.log 3 - 17 / 18 * Real.log 17 := by
  unfold H
  rw [show (1 : ℝ) - 1 / 18 = 17 / (2 * 3 ^ 2) by norm_num, show (1 / 18 : ℝ) = 1 / (2 * 3 ^ 2) by
      norm_num, Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_one]
  push_cast; ring

lemma H_one_div_11_5 :
    H (1 / 11.5) = Real.log 23 - 2 / 23 * Real.log 2 - 21 / 23 * (Real.log 3 + Real.log 7) := by
  unfold H
  rw [show (1 / 11.5 : ℝ) = 2 / 23 by norm_num, show (1 : ℝ) - 2 / 23 = 3 * 7 / 23 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    Real.log_mul (by norm_num) (by norm_num)]
  ring

lemma log_LambdaB : Real.log LambdaB
    = 23 * Real.log 5 - 20 * Real.log 2 - 23 / 2 * Real.log 23 + 21 / 2 * (Real.log 3 + Real.log 7)
      + 2 / 18 * (Real.log 3 + Real.log 7 - 3 * Real.log 2) := by
  have h2 := log_two_gt'
  rw [LambdaB, log_LambdaC, H_one_div_11_5, gammaB_eq, log_four_eq]
  field_simp
  ring

theorem corollary_9_1_b_exponents : Corollary_9_1_b_exponents := by
  have h2 := log_two_gt'; have h2' := log_two_lt'
  have h3 := log_three_gt'; have h3' := log_three_lt'
  have h7 := log_seven_gt'; have h7' := log_seven_lt'
  have h17 := log_seventeen_gt'; have h17' := log_seventeen_lt'
  have p2 : 0 < Real.log 2 := by linarith
  refine ⟨?_, ?_, ?_, ?_, by norm_num, ?_, ?_⟩
  · rw [gammaB_eq, lt_div_iff₀ (by positivity)]; linarith
  · rw [gammaB_eq, div_lt_iff₀ (by positivity)]; linarith
  · rw [qB_eq, lt_div_iff₀ p2]; linarith
  · rw [qB_eq, div_lt_iff₀ p2]; linarith
  · rw [gammaB, gammaOf, show ((11.5 : ℝ) - 1) / 4 = 21 / 8 by norm_num]; ring
  · rw [qB_eq, qOf, H_one_div_18, log_four_eq]; congr 1; ring

theorem corollary_9_1_b_Lambda : Corollary_9_1_b_Lambda := by
  have h2 := log_two_gt'; have h2' := log_two_lt'
  have h3 := log_three_gt'; have h3' := log_three_lt'
  have h5 := log_five_gt'; have h5' := log_five_lt'
  have h7 := log_seven_gt'; have h7' := log_seven_lt'
  have h23 := log_twentythree_gt'; have h23' := log_twentythree_lt'
  have hL := log_LambdaB
  have hpos : 0 < LambdaB := LambdaC_pos 11.5 gammaB
  refine ⟨?_, ?_, by norm_num, by norm_num, ?_⟩
  · rw [← Real.log_lt_log_iff (by norm_num) hpos, log_eq_log_div_pow _ (by norm_num) 28]
    have := (log_mem 0 14 (by norm_num : (0 : ℝ) < 2.1169e8 / 2 ^ 28)).2
    have hb : logApprox 0 14 (2.1169e8 / 2 ^ 28) + logErr 0 14 (2.1169e8 / 2 ^ 28)
        < -0.23748755734470 := by numerics
    push_cast at *
    linarith
  · rw [← Real.log_lt_log_iff hpos (by norm_num), log_eq_log_div_pow (2.1170e8) (by norm_num) 28]
    have := (log_mem 0 14 (by norm_num : (0 : ℝ) < 2.1170e8 / 2 ^ 28)).1
    have hb : -0.23744031957338 < logApprox 0 14 (2.1170e8 / 2 ^ 28)
        - logErr 0 14 (2.1170e8 / 2 ^ 28) := by numerics
    push_cast at *
    linarith
  · have := (log_mem 0 14 (by norm_num : (0 : ℝ) < 1.268)).2
    have hb : logApprox 0 14 1.268 + logErr 0 14 1.268 < 0.23744085601504 := by numerics
    rw [← Real.log_lt_log_iff (by positivity) (by norm_num), Real.log_mul (by norm_num) hpos.ne',
      Real.log_pow, log_four_eq]
    push_cast at *
    linarith

end ThinMatrixProducts

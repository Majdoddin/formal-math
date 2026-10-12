import Statements

/-!
# Appendix A.1: the consequences of the private-leaf condition
-/

namespace ThinMatrixProducts

theorem sec_A_1_private_consequences : Sec_A_1_private_consequences := by
  intro R₀ R₁ q₀ c hc hR₀ h
  have hc1 : 0 ≤ c - 1 := by linarith
  constructor
  · intro h1 h2 hq
    have hR₁ : (4 : ℝ) ^ (c - 1) ≤ R₁ ^ (2 * (c - 1)) := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      exact Real.rpow_le_rpow (by positivity) h2 (by positivity)
    have hR0 : 1 ≤ R₀ ^ 2 := by nlinarith
    have hpos : 0 ≤ R₁ ^ (2 * (c - 1)) := Real.rpow_nonneg (by linarith) _
    nlinarith
  · intro h1
    have hR1 : 1 ≤ R₁ ^ (2 * (c - 1)) := Real.one_le_rpow h1 (by positivity)
    have hsq : R₀ ^ 2 < q₀ := by nlinarith [sq_nonneg R₀]
    rw [← Real.sqrt_sq hR₀]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) hsq

end ThinMatrixProducts

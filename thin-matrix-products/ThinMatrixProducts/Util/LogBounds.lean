/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Adapted from `3sum-apsp/ThreeSumApsp/Sec4/Table2/LogBounds.lean` (the formalization of
arXiv:2610.06783 in anthropics/formal-math): the enclosure `log_mem` and the tactic `numerics`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Enclosures of logarithms of rational numbers

`log_mem k n θ` encloses `log θ` between two numbers that are rational when `θ` is: write
`θ = 2^k (1 + x)/(1 - x)` and sum `n` terms of `log ((1 + x)/(1 - x)) = 2 (x + x³/3 + ⋯)`, with
Mathlib's enclosure of `log 2`. The tactic `numerics` proves the resulting inequalities between
explicit rational numbers by `norm_num`.
-/

namespace ThinMatrixProducts

/-- Mathlib's lower bound on `ln 2`. -/
noncomputable def logTwoLo : ℝ := 0.6931471803

/-- Mathlib's upper bound on `ln 2`. -/
noncomputable def logTwoHi : ℝ := 0.6931471808

/-- The `x` with `θ = 2^k (1 + x)/(1 - x)`. -/
noncomputable def seriesArg (k : ℤ) (θ : ℝ) : ℝ := (θ - 2 ^ k) / (θ + 2 ^ k)

/-- `k ln 2 + 2 (x + x³/3 + ⋯)`, `n` terms, with the midpoint of the bounds on `ln 2`. -/
noncomputable def logApprox (k : ℤ) (n : ℕ) (θ : ℝ) : ℝ :=
  k * ((logTwoLo + logTwoHi) / 2)
    + 2 * ∑ i ∈ Finset.range n, seriesArg k θ ^ (2 * i + 1) / (2 * i + 1)

/-- The error bound of `logApprox`. -/
noncomputable def logErr (k : ℤ) (n : ℕ) (θ : ℝ) : ℝ :=
  |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) + 2 * (seriesArg k θ ^ (2 * n) / (1 - seriesArg k θ ^ 2))

/-- Evaluates both sides of an inequality between explicit rationals. -/
macro "numerics" : tactic =>
  `(tactic| norm_num [logApprox, logErr, seriesArg, logTwoLo, logTwoHi, Finset.sum_range_succ])

lemma log_two_mem : Real.log 2 ∈ Set.Icc logTwoLo logTwoHi :=
  ⟨Real.log_two_gt_d9.le, Real.log_two_lt_d9.le⟩

/-- The enclosure of `log θ`. It holds for every `k` and `n`; they decide only how tight it is. -/
theorem log_mem (k : ℤ) (n : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    Real.log θ ∈ Set.Icc (logApprox k n θ - logErr k n θ) (logApprox k n θ + logErr k n θ) := by
  have hpow : (0 : ℝ) < 2 ^ k := by positivity
  have hx : |seriesArg k θ| < 1 := by
    rw [seriesArg, abs_div, abs_of_pos (add_pos hθ hpow), div_lt_one (add_pos hθ hpow), abs_lt]
    constructor <;> linarith
  have hsq : 0 < 1 - seriesArg k θ ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one _).2 hx)
  have hlog : Real.log θ
      = k * Real.log 2 + Real.log ((1 + seriesArg k θ) / (1 - seriesArg k θ)) := by
    have hdiv : (1 + seriesArg k θ) / (1 - seriesArg k θ) = θ / 2 ^ k := by
      rw [seriesArg]
      field_simp
      ring
    rw [hdiv, Real.log_div hθ.ne' hpow.ne', Real.log_zpow]
    ring
  have htwo : |k * Real.log 2 - k * ((logTwoLo + logTwoHi) / 2)|
      ≤ |(k : ℝ)| * ((logTwoHi - logTwoLo) / 2) := by
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left (abs_le.2 ⟨?_, ?_⟩) (abs_nonneg _) <;>
      linarith [log_two_mem.1, log_two_mem.2]
  have hseries := (Real.sum_range_sub_log_div_le hx n).trans
    (div_le_div_of_nonneg_right (pow_le_pow_of_le_one (abs_nonneg _) hx.le (Nat.le_succ _)) hsq.le)
  rw [(even_two_mul n).pow_abs] at hseries
  rw [abs_le] at htwo hseries
  rw [hlog, logApprox, logErr]
  constructor <;> linarith [htwo.1, htwo.2, hseries.1, hseries.2]

/-- Lower bound form of `log_mem`. -/
theorem le_log (k : ℤ) (n : ℕ) {θ a : ℝ} (hθ : 0 < θ) (h : a ≤ logApprox k n θ - logErr k n θ) :
    a ≤ Real.log θ := h.trans (log_mem k n hθ).1

/-- Upper bound form of `log_mem`. -/
theorem log_le (k : ℤ) (n : ℕ) {θ a : ℝ} (hθ : 0 < θ) (h : logApprox k n θ + logErr k n θ ≤ a) :
    Real.log θ ≤ a := (log_mem k n hθ).2.trans h

end ThinMatrixProducts

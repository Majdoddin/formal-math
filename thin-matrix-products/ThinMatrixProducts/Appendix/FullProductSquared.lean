import Statements

/-!
# Full products: the squared run changes nothing (Section 5 of the paper)
-/

namespace ThinMatrixProducts

open Finset

theorem fp_squared : FP_squared := by
  intro R n b S t ht
  have hsum : ∑ l, ∑ l', (((S l * S l' : ℕ) : ℝ)) ^ t = (∑ l, ((S l : ℕ) : ℝ) ^ t) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
    push_cast
    exact Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨hsum, fun h => ?_⟩
  rw [hsum]
  have hl : ((n * n : ℕ) : ℝ) * ((b * b : ℕ) : ℝ) ^ (t / 2) = ((n : ℝ) * (b : ℝ) ^ (t / 2)) ^ 2 := by
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  rw [hl]
  exact pow_le_pow_left₀ (by positivity) h 2

end ThinMatrixProducts

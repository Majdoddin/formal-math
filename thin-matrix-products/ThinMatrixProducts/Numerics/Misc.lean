import Statements
import ThinMatrixProducts.Util.Choose

/-!
# The arithmetic of Corollary 10.1 and of Section 8 of the paper, paragraph "The limit is Coppersmith's exponent" (Remark 17.1 before 12 October 2026)
-/

namespace ThinMatrixProducts

open Real

theorem corollary_10_1_arith : Corollary_10_1_arith := by
  intro n τ τ₁ τ₂ γ q c hn hc
  have hn0 : 0 < n := by linarith
  have e : ∀ a b : ℝ, (n ^ a) ^ b = n ^ (a * b) := fun a b => (Real.rpow_mul hn0.le a b).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, ← Real.rpow_add hn0]; ring_nf
  · rw [e, show (1 + q * τ) = 1 + τ * q by ring, Real.rpow_add hn0, Real.rpow_one]
  · intro hτ hτ0
    rw [e]
    calc n ^ (τ * c) ≤ n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by
          rw [le_div_iff₀ hc] at hτ; linarith)
      _ = n := Real.rpow_one n
  · intro hτ hτ0
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hn (by rw [le_div_iff₀ hc] at hτ; linarith)
  · rw [e, e, ← Real.rpow_add hn0, ← Real.rpow_add hn0]; ring_nf
  · rw [e, ← Real.rpow_add hn0]; ring_nf

theorem remark_17_1_arith : Remark_17_1_arith := by
  intro m N' α L
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (2 * (L : ℝ) / 5) = ((2 * m : ℕ) : ℝ) by simp only [L]; push_cast; ring,
      Real.rpow_natCast, pow_mul]
    norm_num
  · rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num)]
    congr 1
    simp only [α]
    field_simp
  · have := NatChoose.choose_mul_pow_le 4 L m
    exact_mod_cast this
  · intro h0 hN
    have hα0 : 0 ≤ α := by simp only [α]; positivity
    calc N' ^ α ≤ ((5 : ℝ) ^ L) ^ α := Real.rpow_le_rpow h0 hN hα0
      _ = (5 : ℝ) ^ (α * L) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm]
      _ = (2 : ℝ) ^ (2 * (L : ℝ) / 5) := by
          rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos (by norm_num)]
          congr 1
          simp only [α]
          field_simp

end ThinMatrixProducts

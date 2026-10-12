import Statements
import ThinMatrixProducts.Numerics.Threshold

/-!
# Proposition 10.3: the arithmetic of the two regions, the general thresholds and the regions
-/

namespace ThinMatrixProducts

open Real

theorem remark_10_3_general : Remark_10_3_general := by
  intro n τ₁ τ₂ γ q c hn hc hγ hq
  have hn0 : 0 < n := by linarith
  have e : ∀ a b : ℝ, (n ^ a) ^ b = n ^ (a * b) := fun a b => (Real.rpow_mul hn0.le a b).symm
  have lt : ∀ a b : ℝ, 1 < n → a < b → n ^ a < n ^ b := fun a b h hab =>
    Real.rpow_lt_rpow_of_exponent_lt h hab
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro hτ0 hτ
    rw [e]
    calc n ^ (τ₁ * c) ≤ n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (by
          rw [le_div_iff₀ hc] at hτ; linarith)
      _ = n := Real.rpow_one n
  · rw [e, ← Real.rpow_add hn0]; ring_nf
  · intro h0 h1; exact lt _ _ h1 (by nlinarith)
  · rw [e, ← Real.rpow_add hn0]; ring_nf
  · intro h0 h1; exact lt _ _ h1 (by nlinarith)
  · intro hτ0 hτ
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hn (by rw [le_div_iff₀ hc] at hτ; linarith)
  · rw [show n / n ^ τ₁ = n ^ (1 - τ₁) by rw [Real.rpow_sub hn0, Real.rpow_one], e, e,
      ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    ring_nf
  · intro h0 h1; exact lt _ _ h1 (by nlinarith)
  · rw [e, ← Real.rpow_add hn0]; ring_nf
  · intro h0 h1; exact lt _ _ h1 (by nlinarith)

theorem remark_10_3_arith : Remark_10_3_arith := by
  intro n τ₁ τ₂ hn
  obtain ⟨⟨a1, a2, -, a4, -⟩, ⟨b1, b2, -, b4, -⟩⟩ :=
    remark_10_3_general n τ₁ τ₂ 0.092 0.403 18 hn (by norm_num) (by norm_num) (by norm_num)
  refine ⟨⟨fun h0 h => a1 h0.le (by linarith), a2, fun h0 => by linarith, a4,
    fun h0 => by linarith⟩, ⟨fun h0 h => b1 h0.le h.le, b2, fun h0 => by linarith, b4,
    fun h0 => by linarith⟩⟩

theorem remark_10_3_eps : Remark_10_3_eps := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro τ₁ h0 h
    exact ⟨τ₁, h0, h, fun n _ => le_rfl⟩
  · intro τ₁ τ₂ h1 h2 h
    refine ⟨τ₂ / τ₁, div_pos h2 h1, by rwa [div_lt_iff₀ h1], fun n hn => ?_⟩
    rw [← Real.rpow_mul (by linarith), mul_div_cancel₀ _ h1.ne']
  · intro τ n hτ h
    have h2 : (0 : ℝ) ≤ 2 ^ (1 / τ) := by positivity
    calc (2 : ℝ) = ((2 : ℝ) ^ (1 / τ)) ^ τ := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hτ.ne', Real.rpow_one]
      _ ≤ n ^ τ := Real.rpow_le_rpow h2 h hτ.le
  · intro n τ₁ τ₂ γ hn hγ h1 h2
    have lt : ∀ a b : ℝ, a < b → n ^ a < n ^ b := fun a b hab =>
      Real.rpow_lt_rpow_of_exponent_lt hn hab
    exact ⟨lt _ _ (by nlinarith), lt _ _ (by linarith), lt _ _ (by nlinarith),
      lt _ _ (by linarith)⟩

theorem remark_10_3_regions : Remark_10_3_regions := by
  obtain ⟨e1, e2⟩ := sec1_epsStar5_value
  have e1' : (0.17227 : ℝ) < epsStar5 := e1
  have e2' : epsStar5 < (0.17228 : ℝ) := e2
  have key : ∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → 1.4 ≤ τ₁ + τ₂ →
      (τ₁ < epsStar5 → 1 < τ₂) ∧ (τ₂ < epsStar5 * τ₁ → 1 < τ₁) := by
    intro τ₁ τ₂ h0 hs
    refine ⟨fun h => by norm_num at hs; linarith, fun h => ?_⟩
    by_contra hc
    replace hc := not_lt.mp hc
    have : epsStar5 * τ₁ ≤ epsStar5 := by nlinarith
    norm_num at hs
    linarith
  refine ⟨?_, ?_, ?_, ?_, key, ?_⟩
  · intro τ₁ τ₂ h h'
    nlinarith
  · intro τ₁ τ₂ h h'
    linarith
  · intro τ₁ h
    norm_num at h ⊢
    linarith
  · intro τ₁ τ₂ h h'
    nlinarith
  · intro τ₁ τ₂ h0 h1 h2 hs
    obtain ⟨k1, k2⟩ := key τ₁ τ₂ h0.le hs
    exact ⟨fun h => by linarith [k1 h], fun h => by linarith [k2 h]⟩

end ThinMatrixProducts

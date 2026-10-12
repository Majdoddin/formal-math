import Statements
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities
/-! # Full products: Theorem 2's inequality and the shapes of the 145 -/
namespace ThinMatrixProducts

open Finset

/-- The chord bound: for `k > 1`, `t ∈ [0,1]`, `c = (k^t - 1)/(k - 1)` and `s ≥ 1`,
`s^t ≥ (1 - c) + c min(s, k)`. -/
private lemma fp_chord {k s t : ℝ} (hk : 1 < k) (hs : 1 ≤ s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - (k ^ t - 1) / (k - 1)) + (k ^ t - 1) / (k - 1) * min s k ≤ s ^ t := by
  have hk1 : 0 < k - 1 := by linarith
  rcases le_total s k with hsk | hks
  · rw [min_eq_left hsk]
    have hconc := (Real.concaveOn_rpow ht0 ht1).2 (show (1 : ℝ) ∈ Set.Ici 0 by simp)
      (show k ∈ Set.Ici 0 by simp only [Set.mem_Ici]; linarith)
      (div_nonneg (by linarith : (0 : ℝ) ≤ k - s) hk1.le)
      (div_nonneg (by linarith : (0 : ℝ) ≤ s - 1) hk1.le) (by field_simp; ring)
    have hpt : (k - s) / (k - 1) * 1 + (s - 1) / (k - 1) * k = s := by
      field_simp; ring
    simp only [smul_eq_mul] at hconc
    rw [hpt, Real.one_rpow] at hconc
    calc (1 - (k ^ t - 1) / (k - 1)) + (k ^ t - 1) / (k - 1) * s
        = (k - s) / (k - 1) * 1 + (s - 1) / (k - 1) * k ^ t := by field_simp; ring
      _ ≤ s ^ t := hconc
  · rw [min_eq_right hks]
    calc (1 - (k ^ t - 1) / (k - 1)) + (k ^ t - 1) / (k - 1) * k = k ^ t := by
          field_simp; ring
      _ ≤ s ^ t := Real.rpow_le_rpow (by linarith) hks ht0

theorem fp_Theorem_2_ineq : FP_Theorem_2_ineq := by
  intro b k n R S hb hk hcond hS hnR hsum t ht0 ht1
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsumR : (b : ℝ) * n ≤ ∑ l, ((min (S l) k : ℕ) : ℝ) := by exact_mod_cast hsum
  have hSR : ∀ l, (1 : ℝ) ≤ (S l : ℝ) := fun l => by exact_mod_cast hS l
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  by_cases hkb : k ≤ b
  · -- case `k ≤ b`
    have hkbR : (k : ℝ) ≤ b := by exact_mod_cast hkb
    have hper : ∀ l, (k : ℝ) ^ (t - 1) * ((min (S l) k : ℕ) : ℝ) ≤ ((S l : ℕ) : ℝ) ^ t := by
      intro l
      set m : ℝ := ((min (S l) k : ℕ) : ℝ) with hm
      have hm1 : 1 ≤ m := by rw [hm]; exact_mod_cast le_min (hS l) hk
      have hmk : m ≤ k := by rw [hm]; exact_mod_cast min_le_right _ _
      have hmS : m ≤ S l := by rw [hm]; exact_mod_cast min_le_left _ _
      calc (k : ℝ) ^ (t - 1) * m ≤ m ^ (t - 1) * m :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_nonpos (by linarith) hmk (by linarith)) (by linarith)
        _ = m ^ t := by
            rw [← Real.rpow_add_one (by linarith)]; ring_nf
        _ ≤ ((S l : ℕ) : ℝ) ^ t := Real.rpow_le_rpow (by linarith) hmS ht0
    have hb_le : (b : ℝ) ^ (t / 2) ≤ b * (k : ℝ) ^ (t - 1) := by
      calc (b : ℝ) ^ (t / 2) ≤ (b : ℝ) ^ t :=
            Real.rpow_le_rpow_of_exponent_le hbR (by linarith)
        _ = b * (b : ℝ) ^ (t - 1) := by
            rw [mul_comm, ← Real.rpow_add_one (by linarith)]; ring_nf
        _ ≤ b * (k : ℝ) ^ (t - 1) :=
            mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos (by linarith) hkbR (by linarith)) (by linarith)
    calc (n : ℝ) * (b : ℝ) ^ (t / 2) ≤ n * (b * (k : ℝ) ^ (t - 1)) :=
          mul_le_mul_of_nonneg_left hb_le hn0
      _ = (k : ℝ) ^ (t - 1) * (b * n) := by ring
      _ ≤ (k : ℝ) ^ (t - 1) * ∑ l, ((min (S l) k : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_left hsumR (Real.rpow_nonneg (by linarith) _)
      _ = ∑ l, (k : ℝ) ^ (t - 1) * ((min (S l) k : ℕ) : ℝ) := by rw [mul_sum]
      _ ≤ ∑ l, ((S l : ℕ) : ℝ) ^ t := sum_le_sum fun l _ => hper l
  · -- case `b < k`
    have hcond' : b ^ (k - 1) ≤ k ^ (2 * (b - 1)) := hcond.resolve_left hkb
    have hbk : (b : ℝ) < k := by exact_mod_cast Nat.lt_of_not_le hkb
    have hk1 : (1 : ℝ) < k := by linarith
    have hk1' : (0 : ℝ) < k - 1 := by linarith
    set c : ℝ := ((k : ℝ) ^ t - 1) / (k - 1) with hc
    have hkt1 : (1 : ℝ) ≤ (k : ℝ) ^ t := Real.one_le_rpow hkR ht0
    have hktk : (k : ℝ) ^ t ≤ k := by
      simpa using Real.rpow_le_rpow_of_exponent_le hkR ht1
    have hc0 : 0 ≤ c := div_nonneg (by linarith) hk1'.le
    have hc1 : c ≤ 1 := (div_le_one hk1').2 (by linarith)
    have hper : ∀ l, (1 - c) + c * ((min (S l) k : ℕ) : ℝ) ≤ ((S l : ℕ) : ℝ) ^ t := by
      intro l
      have := fp_chord (s := (S l : ℝ)) hk1 (hSR l) ht0 ht1
      push_cast
      exact this
    have hlow : (n : ℝ) * (1 + (b - 1) * c) ≤ ∑ l, ((S l : ℕ) : ℝ) ^ t := by
      have hnR' : (n : ℝ) ≤ R := by exact_mod_cast hnR
      calc (n : ℝ) * (1 + (b - 1) * c) = n * (1 - c) + c * (b * n) := by ring
        _ ≤ R * (1 - c) + c * ∑ l, ((min (S l) k : ℕ) : ℝ) :=
            add_le_add (mul_le_mul_of_nonneg_right hnR' (by linarith))
              (mul_le_mul_of_nonneg_left hsumR hc0)
        _ = ∑ l, ((1 - c) + c * ((min (S l) k : ℕ) : ℝ)) := by
            rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sum]
        _ ≤ ∑ l, ((S l : ℕ) : ℝ) ^ t := sum_le_sum fun l _ => hper l
    -- weighted AM-GM
    set lam : ℝ := ((b : ℝ) - 1) / (k - 1) with hlam
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hk1'.le
    have hlam1 : lam ≤ 1 := (div_le_one hk1').2 (by linarith)
    have hamgm : (k : ℝ) ^ (t * lam) ≤ 1 + (b - 1) * c := by
      have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - lam) (w₂ := lam)
        (p₁ := 1) (p₂ := (k : ℝ) ^ t) (by linarith) hlam0 zero_le_one (by linarith) (by ring)
      rw [Real.one_rpow, one_mul, ← Real.rpow_mul (by linarith)] at h
      calc (k : ℝ) ^ (t * lam) ≤ (1 - lam) * 1 + lam * (k : ℝ) ^ t := h
        _ = 1 + (b - 1) * c := by rw [hlam, hc]; field_simp; ring
    -- the logarithmic condition
    have hlog : ((k : ℝ) - 1) * Real.log b ≤ 2 * ((b : ℝ) - 1) * Real.log k := by
      have h : ((b : ℝ)) ^ (k - 1) ≤ (k : ℝ) ^ (2 * (b - 1)) := by exact_mod_cast hcond'
      have h2 := Real.log_le_log (pow_pos (by linarith) _) h
      rw [Real.log_pow, Real.log_pow] at h2
      push_cast [Nat.cast_sub hk, Nat.cast_sub hb] at h2
      linarith
    have hbk' : (b : ℝ) ^ (t / 2) ≤ (k : ℝ) ^ (t * lam) := by
      rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.2
      have hlk : 0 ≤ Real.log k := Real.log_nonneg hkR
      have e : Real.log k * (t * lam) = t * (2 * ((b : ℝ) - 1) * Real.log k) / (2 * (k - 1)) := by
        rw [hlam]; field_simp
      rw [e, le_div_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hlog ht0]
    calc (n : ℝ) * (b : ℝ) ^ (t / 2) ≤ n * (1 + (b - 1) * c) :=
          mul_le_mul_of_nonneg_left (hbk'.trans hamgm) hn0
      _ ≤ _ := hlow

theorem fp_shapes_145 : FP_shapes_145 := by
  unfold FP_shapes_145
  decide

end ThinMatrixProducts

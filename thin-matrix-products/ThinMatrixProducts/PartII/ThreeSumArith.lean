import ThinMatrixProducts.PartII.ThreeSum
import ThinMatrixProducts.Util.Logs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Section 13: the arithmetic of the parameters, of Lemma 13.8, of the cost and of Corollary 13.3
-/

namespace ThinMatrixProducts

open Real

/-- `⌈x⌉ ≤ 2x` for `x ≥ 1`. -/
lemma ceil_le_two_mul {x : ℝ} (hx : 1 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ x); linarith

/-- `⌊x⌋ ≥ x/2` for `x ≥ 1`. -/
lemma half_le_floor {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by intro h; rw [Nat.floor_eq_zero] at h; linarith)
  linarith

theorem eq_13_5 : Eq_13_5 := by
  intro n U ε c₁ r hn hU hr hc₁ Λ σ g P hσ2 hcn h2
  have hU2 : (2 : ℝ) ≤ 2 * U := by linarith
  have hl : 0 < Real.log (2 * U) := Real.log_pos (by linarith)
  have hl2 : Real.log 2 ≤ Real.log (2 * U) := Real.log_le_log (by norm_num) (by linarith)
  have hΛ : 0 < Λ := by simp only [Λ]; positivity
  have hσ : (2 : ℝ) ≤ σ := by exact_mod_cast hσ2
  have hsq : (σ : ℝ) ≤ Real.sqrt (n ^ ε / Λ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (n ^ ε / Λ) := by linarith
  -- `y := ln(2U) (2σ²)^{1/r} ≥ 1`
  set y := Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) with hy
  have hy1 : 1 ≤ y := by
    have := log_two_gt
    nlinarith
  have hP5 : (P : ℝ) ≤ 5 * y := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 4 * y)
    simp only [P, ← hy, mul_assoc] at this ⊢
    nlinarith
  refine ⟨by have := half_le_floor hsq1; simpa [σ] using this, ?_, ?_,
    by simpa [hy, one_div, mul_assoc] using hP5, ?_⟩
  · have : (σ : ℝ) ^ 2 ≤ n ^ ε / Λ := by
      calc (σ : ℝ) ^ 2 ≤ (Real.sqrt (n ^ ε / Λ)) ^ 2 := pow_le_pow_left₀ (by positivity) hsq 2
        _ = n ^ ε / Λ := Real.sq_sqrt (by positivity)
    rw [le_div_iff₀ hΛ] at this
    linarith
  · have := ceil_le_two_mul hcn
    simpa [g, mul_div_assoc, mul_assoc] using this
  · have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    calc (2 * (P : ℝ)) ^ r ≤ (10 * y) ^ r := pow_le_pow_left₀ (by positivity) (by linarith) r
      _ = (10 * Real.log (2 * U)) ^ r * ((2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ))) ^ r := by
          rw [hy, ← mul_assoc, mul_pow]
      _ = Λ * (σ : ℝ) ^ 2 := by
          rw [← Real.rpow_natCast ((2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ))), ← Real.rpow_mul (by positivity),
            show 1 / (r : ℝ) * r = 1 by field_simp, Real.rpow_one]
          simp only [Λ]; ring

theorem sec13_log_bounds : Sec13_log_bounds := by
  intro n U ν hn hU hν hUn
  have hn0 : 0 < n := by linarith
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have hlU : Real.log U ≤ ν * Real.log n := by
    rw [← Real.log_rpow hn0]; exact Real.log_le_log (by linarith) hUn
  have h3 : Real.log 3 ≤ 2 * Real.log 2 := by
    have : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    rwa [log_four_eq] at this
  constructor
  · rw [Real.log_mul (by norm_num) (by linarith)]; nlinarith
  · rw [Real.log_mul (by norm_num) (by linarith)]; nlinarith

/-- `D^a ≤ (Λσ²)^a` and the split of the exponent. -/
lemma rpow_le_of_le_mul {D Λ σ a : ℝ} (hD : 1 ≤ D) (hΛ : 1 ≤ Λ) (hσ : 1 ≤ σ) (ha : 0 ≤ a)
    (h : D ≤ Λ * σ ^ 2) : D ^ a ≤ Λ ^ a * σ ^ (2 * a) := by
  calc D ^ a ≤ (Λ * σ ^ 2) ^ a := Real.rpow_le_rpow (by linarith) h ha
    _ = Λ ^ a * σ ^ (2 * a) := by
        rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_natCast σ 2,
          ← Real.rpow_mul (by linarith)]; norm_num

theorem lemma_13_8_arith : Lemma_13_8_arith := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m g T hm hg hT1 hT2
    have hs : 1 ≤ Real.sqrt m := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hm
    constructor <;> nlinarith
  · intro n σ g Λ D N ε hσ hΛ hD hε hε2 hDΛ hg hΛn hN hn
    have hg0 : 0 < g := lt_of_lt_of_le (div_pos hn hσ) hg
    -- `D^{1-ε/2} ≤ g^ε`
    have h1 : D ^ (1 - ε / 2) ≤ g ^ ε := by
      have hσ1 : (Λ * σ ^ 2) ^ (1 - ε / 2) = Λ ^ (1 - ε / 2) * σ ^ (2 - ε) := by
        rw [Real.mul_rpow (by linarith) (by positivity), ← Real.rpow_natCast σ 2,
          ← Real.rpow_mul hσ.le]
        congr 2; push_cast; ring
      calc D ^ (1 - ε / 2) ≤ (Λ * σ ^ 2) ^ (1 - ε / 2) := Real.rpow_le_rpow (by linarith) hDΛ (by linarith)
        _ = Λ ^ (1 - ε / 2) * σ ^ (2 - ε) := hσ1
        _ ≤ Λ * σ ^ (2 - ε) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc Λ ^ (1 - ε / 2) ≤ Λ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
              _ = Λ := Real.rpow_one Λ
        _ = Λ * σ ^ 2 * σ ^ (-ε) := by
            rw [mul_assoc, ← Real.rpow_natCast σ 2, ← Real.rpow_add hσ]
            congr 2
        _ ≤ n ^ ε * σ ^ (-ε) := mul_le_mul_of_nonneg_right hΛn (by positivity)
        _ = (n / σ) ^ ε := by
            rw [Real.div_rpow hn.le hσ.le, Real.rpow_neg hσ.le, div_eq_mul_inv]
        _ ≤ g ^ ε := Real.rpow_le_rpow (by positivity) hg hε.le
    calc D = D ^ (1 - ε / 2) * D ^ (ε / 2) := by
          rw [← Real.rpow_add (by linarith)]; norm_num
      _ ≤ g ^ ε * D ^ (ε / 2) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (g * Real.sqrt D) ^ ε := by
          rw [Real.mul_rpow hg0.le (Real.sqrt_nonneg _), Real.sqrt_eq_rpow, ← Real.rpow_mul (by linarith)]
          ring_nf
      _ ≤ N ^ ε := Real.rpow_le_rpow (by positivity) hN hε.le
  · intro σ g Λ D γ c₂ C W N hσ hΛ hD hγ hγ2 hDΛ hc₂ hC hg hN1 hN2 hW hWle hX
    have hsD : 1 ≤ Real.sqrt D := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hD
    have hsD0 : 0 < Real.sqrt D := by linarith
    have hD0 : 0 < D := by linarith
    have hDγ : 0 < D ^ γ := Real.rpow_pos_of_pos hD0 γ
    constructor
    · -- the number of parts
      set X := N ^ 2 / Real.sqrt D with hXdef
      have hb := half_le_floor hX
      have hb0 : (0 : ℝ) < ⌊X⌋₊ := by linarith
      have hparts : (⌈W / ⌊X⌋₊⌉₊ : ℝ) ≤ 1 + 2 * c₂ * σ / Real.sqrt D := by
        have h1 : (⌈W / ⌊X⌋₊⌉₊ : ℝ) < W / ⌊X⌋₊ + 1 := Nat.ceil_lt_add_one (by positivity)
        have h2 : W / ⌊X⌋₊ ≤ 2 * W / X := by
          rw [div_le_div_iff₀ hb0 (by linarith)]; nlinarith
        have h3 : 2 * W / X ≤ 2 * c₂ * σ / Real.sqrt D := by
          rcases eq_or_lt_of_le hg with hg0 | hg0
          · rw [← hg0] at hWle
            have : W = 0 := le_antisymm (by simpa using hWle) hW
            rw [this]; simp only [mul_zero, zero_div]; positivity
          · have hNg : g ^ 2 * D ≤ N ^ 2 := by
              have := pow_le_pow_left₀ (by positivity) hN1 2
              rwa [mul_pow, Real.sq_sqrt hD0.le] at this
            rw [hXdef, div_div_eq_mul_div, div_le_div_iff₀ (by nlinarith) hsD0]
            have hss : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt hD0.le
            calc 2 * W * Real.sqrt D * Real.sqrt D = 2 * W * D := by rw [mul_assoc, hss]
              _ ≤ 2 * (c₂ * g ^ 2 * σ) * D := by nlinarith
              _ = 2 * c₂ * σ * (g ^ 2 * D) := by ring
              _ ≤ 2 * c₂ * σ * N ^ 2 := mul_le_mul_of_nonneg_left hNg (by positivity)
        linarith
      have hcost : C * N ^ 2 / D ^ γ ≤ 9 * C * g ^ 2 * D ^ (1 - γ) := by
        have hN2' : N ^ 2 ≤ 9 * g ^ 2 * D := by
          have := pow_le_pow_left₀ (by linarith) hN2 2
          rwa [mul_pow, mul_pow, Real.sq_sqrt hD0.le, show (3 : ℝ) ^ 2 = 9 by norm_num] at this
        rw [div_le_iff₀ hDγ, Real.rpow_sub hD0, Real.rpow_one]
        rw [show 9 * C * g ^ 2 * (D / D ^ γ) * D ^ γ = 9 * C * g ^ 2 * D by field_simp]
        nlinarith
      exact mul_le_mul hparts hcost (by positivity) (by positivity)
    · -- the case analysis
      have e1 : D ^ (1 - γ) ≤ Λ ^ (1 - γ) * σ ^ (2 * (1 - γ)) :=
        rpow_le_of_le_mul hD hΛ hσ (by linarith) hDΛ
      have e2 : D ^ (1 / 2 - γ) ≤ Λ ^ (1 / 2 - γ) * σ ^ (2 * (1 / 2 - γ)) :=
        rpow_le_of_le_mul hD hΛ hσ (by linarith) hDΛ
      have e3 : Λ ^ (1 / 2 - γ) ≤ Λ ^ (1 - γ) := Real.rpow_le_rpow_of_exponent_le hΛ (by linarith)
      have e4 : σ * D ^ (1 - γ) / Real.sqrt D = σ * D ^ (1 / 2 - γ) := by
        rw [Real.sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_sub hD0]; ring_nf
      have e5 : σ * σ ^ (2 * (1 / 2 - γ)) = σ ^ (2 - 2 * γ) := by
        rw [← Real.rpow_one_add' (by linarith) (by linarith)]; ring_nf
      have e6 : σ ^ (2 * (1 - γ)) = σ ^ (2 - 2 * γ) := by ring_nf
      have hσD : σ * D ^ (1 / 2 - γ) ≤ Λ ^ (1 - γ) * σ ^ (2 - 2 * γ) := by
        calc σ * D ^ (1 / 2 - γ) ≤ σ * (Λ ^ (1 / 2 - γ) * σ ^ (2 * (1 / 2 - γ))) :=
              mul_le_mul_of_nonneg_left e2 (by linarith)
          _ = Λ ^ (1 / 2 - γ) * (σ * σ ^ (2 * (1 / 2 - γ))) := by ring
          _ = Λ ^ (1 / 2 - γ) * σ ^ (2 - 2 * γ) := by rw [e5]
          _ ≤ Λ ^ (1 - γ) * σ ^ (2 - 2 * γ) := mul_le_mul_of_nonneg_right e3 (by positivity)
      rw [e6] at e1
      calc (1 + 2 * c₂ * σ / Real.sqrt D) * (9 * C * g ^ 2 * D ^ (1 - γ))
          = 9 * C * g ^ 2 * D ^ (1 - γ) + 18 * C * c₂ * g ^ 2 * (σ * D ^ (1 - γ) / Real.sqrt D) := by
            ring
        _ = 9 * C * g ^ 2 * D ^ (1 - γ) + 18 * C * c₂ * g ^ 2 * (σ * D ^ (1 / 2 - γ)) := by rw [e4]
        _ ≤ 9 * C * g ^ 2 * (Λ ^ (1 - γ) * σ ^ (2 - 2 * γ))
            + 18 * C * c₂ * g ^ 2 * (Λ ^ (1 - γ) * σ ^ (2 - 2 * γ)) := by
            gcongr
        _ = 9 * C * (1 + 2 * c₂) * Λ ^ (1 - γ) * g ^ 2 * σ ^ (2 - 2 * γ) := by ring
  · intro N D ε γ hN hD hε hγ hγ2 hεγ hDN
    have hD0 : 0 < D := by linarith
    have hN0 : 0 < N := by linarith
    have h1 : D ^ (1 + γ) ≤ N := by
      calc D ^ (1 + γ) ≤ (N ^ ε) ^ (1 + γ) := Real.rpow_le_rpow hD0.le hDN (by linarith)
        _ = N ^ (ε * (1 + γ)) := by rw [← Real.rpow_mul hN0.le]
        _ ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN hεγ
        _ = N := Real.rpow_one N
    refine ⟨h1, ?_, ?_⟩
    · rw [le_div_iff₀ (Real.rpow_pos_of_pos hD0 γ)]
      calc N * D * D ^ γ = N * D ^ (1 + γ) := by
            rw [Real.rpow_add hD0, Real.rpow_one]; ring
        _ ≤ N * N := mul_le_mul_of_nonneg_left h1 hN0.le
        _ = N ^ 2 := by ring
    · apply div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hD0 γ)
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hD hγ2

/-- `log₂ n + 1 ≤ 3 ln n` for `n ≥ 2`. -/
lemma logb_two_add_one_le {n : ℝ} (hn : 2 ≤ n) : Real.logb 2 n + 1 ≤ 3 * Real.log n := by
  have h2 := log_two_gt; have h2' := log_two_lt
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have hl0 : 0 < Real.log 2 := by linarith
  rw [Real.logb, div_add_one hl0.ne', div_le_iff₀ hl0]
  nlinarith

theorem eq_13_6 : Eq_13_6 := by
  intro n U ν ε γ c₁ σ g P L B r hn hU hν hUn hε hγ hγ2 hc₁ hr hσ Λ hσlow hΛσ hg0 hg hP0 hP hL0 hL hB0 hB
  have hn0 : 0 < n := by linarith
  have hlnn : 0 < Real.log n := Real.log_pos (by linarith)
  have hlU := (sec13_log_bounds n U ν hn hU hν hUn).1
  have hl : 0 < Real.log (2 * U) := Real.log_pos (by linarith)
  have hΛ1 : 1 ≤ Λ := by
    simp only [Λ]
    have : (1 : ℝ) ≤ 10 * Real.log (2 * U) := by
      have := log_two_gt
      have : Real.log 2 ≤ Real.log (2 * U) := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have := one_le_pow₀ this (n := r)
    linarith
  have hΛ0 : 0 < Λ := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  -- `(2σ²)^{1/r} ≤ 2 n^{ε/r}`
  have hσ2 : σ ^ 2 ≤ n ^ ε := by
    have : σ ^ 2 ≤ Λ * σ ^ 2 := le_mul_of_one_le_left (by positivity) hΛ1
    linarith
  have hroot : (2 * σ ^ 2) ^ (1 / (r : ℝ)) ≤ 2 * n ^ (ε / r) := by
    calc (2 * σ ^ 2) ^ (1 / (r : ℝ)) ≤ (2 * n ^ ε) ^ (1 / (r : ℝ)) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ = 2 ^ (1 / (r : ℝ)) * n ^ (ε / r) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn0.le]
          congr 2; ring
      _ ≤ 2 ^ (1 : ℝ) * n ^ (ε / r) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by rw [div_le_one (by linarith)]; exact hr')
      _ = 2 * n ^ (ε / r) := by rw [Real.rpow_one]
  have hP' : P ≤ 10 * Real.log (2 * U) * n ^ (ε / r) := by
    calc P ≤ 5 * Real.log (2 * U) * (2 * σ ^ 2) ^ (1 / (r : ℝ)) := hP
      _ ≤ 5 * Real.log (2 * U) * (2 * n ^ (ε / r)) := mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = 10 * Real.log (2 * U) * n ^ (ε / r) := by ring
  -- `g² σ^{2-2γ} ≤ 4^{1+γ} c₁² Λ^γ n^{2-εγ}`
  have hσ0 : 0 < σ := by linarith
  have hg2 : g ^ 2 * σ ^ (2 - 2 * γ) ≤ 4 ^ (1 + γ) * c₁ ^ 2 * Λ ^ γ * n ^ (2 - ε * γ) := by
    have hgσ : g * σ ≤ 2 * c₁ * n := by rwa [le_div_iff₀ hσ0] at hg
    have hs : σ ^ (-(2 * γ)) ≤ 4 ^ γ * Λ ^ γ * n ^ (-(ε * γ)) := by
      have hq : 0 < Real.sqrt (n ^ ε / Λ) / 2 := by
        have : 0 < n ^ ε / Λ := by positivity
        positivity
      calc σ ^ (-(2 * γ)) ≤ (Real.sqrt (n ^ ε / Λ) / 2) ^ (-(2 * γ)) :=
            Real.rpow_le_rpow_of_nonpos hq hσlow (by linarith)
        _ = 4 ^ γ * Λ ^ γ * n ^ (-(ε * γ)) := by
            rw [Real.div_rpow (Real.sqrt_nonneg _) (by norm_num), Real.sqrt_eq_rpow,
              ← Real.rpow_mul (by positivity), Real.div_rpow (by positivity) hΛ0.le,
              ← Real.rpow_mul hn0.le]
            rw [show (1 / 2 : ℝ) * -(2 * γ) = -γ by ring, show ε * -γ = -(ε * γ) by ring,
              Real.rpow_neg hΛ0.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            rw [show (4 : ℝ) ^ γ = (2 : ℝ) ^ (2 * γ) by
              rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]]
            field_simp
    calc g ^ 2 * σ ^ (2 - 2 * γ) = (g * σ) ^ 2 * σ ^ (-(2 * γ)) := by
          rw [mul_pow, mul_assoc, ← Real.rpow_natCast σ 2, ← Real.rpow_add hσ0]
          congr 2
      _ ≤ (2 * c₁ * n) ^ 2 * (4 ^ γ * Λ ^ γ * n ^ (-(ε * γ))) := by
          apply mul_le_mul (pow_le_pow_left₀ (by positivity) hgσ 2) hs (by positivity)
            (by positivity)
      _ = 4 ^ (1 + γ) * c₁ ^ 2 * Λ ^ γ * n ^ (2 - ε * γ) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one, Real.rpow_sub hn0, Real.rpow_neg hn0.le]
          rw [show (n : ℝ) ^ (2 : ℝ) = n ^ 2 by norm_num]
          ring
  -- the logarithmic factors
  have hLB : L * B ^ 2 ≤ 27 * Real.log n ^ 3 := by
    have h3 := logb_two_add_one_le hn
    have hL' : L ≤ 3 * Real.log n := le_trans hL h3
    have hB' : B ≤ 3 * Real.log n := le_trans hB h3
    calc L * B ^ 2 ≤ (3 * Real.log n) * (3 * Real.log n) ^ 2 :=
          mul_le_mul hL' (pow_le_pow_left₀ hB0 hB' 2) (by positivity) (by positivity)
      _ = 27 * Real.log n ^ 3 := by ring
  have hΛsplit : Λ ^ (1 - γ) * Λ ^ γ = Λ := by
    rw [← Real.rpow_add hΛ0]; simp
  have h4 : (4 : ℝ) ^ (1 + γ) ≤ 8 := by
    calc (4 : ℝ) ^ (1 + γ) ≤ 4 ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 8 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have hlog : 10 * Real.log (2 * U) ≤ 10 * (ν + 1) * Real.log n := by nlinarith
  have hpowlog : (10 * Real.log (2 * U)) ^ (r + 1) ≤ (10 * (ν + 1)) ^ (r + 1) * Real.log n ^ (r + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hlog _
  have hnexp : n ^ (ε / r) * n ^ (2 - ε * γ) = n ^ (2 - ε * γ + ε / r) := by
    rw [← Real.rpow_add hn0]; ring_nf
  calc L * r * P * B ^ 2 * Λ ^ (1 - γ) * g ^ 2 * σ ^ (2 - 2 * γ)
      = (L * B ^ 2) * r * P * Λ ^ (1 - γ) * (g ^ 2 * σ ^ (2 - 2 * γ)) := by ring
    _ ≤ (27 * Real.log n ^ 3) * r * (10 * Real.log (2 * U) * n ^ (ε / r)) * Λ ^ (1 - γ)
          * (4 ^ (1 + γ) * c₁ ^ 2 * Λ ^ γ * n ^ (2 - ε * γ)) := by
        gcongr
    _ = 27 * 4 ^ (1 + γ) * c₁ ^ 2 * r * Real.log n ^ 3 * (10 * Real.log (2 * U))
          * (Λ ^ (1 - γ) * Λ ^ γ) * (n ^ (ε / r) * n ^ (2 - ε * γ)) := by ring
    _ = 54 * 4 ^ (1 + γ) * c₁ ^ 2 * r * Real.log n ^ 3 * (10 * Real.log (2 * U)) ^ (r + 1)
          * n ^ (2 - ε * γ + ε / r) := by
        rw [hΛsplit, hnexp]; simp only [Λ]; ring
    _ ≤ 54 * 8 * c₁ ^ 2 * r * Real.log n ^ 3
          * ((10 * (ν + 1)) ^ (r + 1) * Real.log n ^ (r + 1)) * n ^ (2 - ε * γ + ε / r) := by
        gcongr
    _ = 432 * c₁ ^ 2 * r * n ^ (2 - ε * γ + ε / r) * (10 * (ν + 1)) ^ (r + 1)
          * (Real.log n) ^ (r + 4) := by ring

theorem corollary_13_4_arith : Corollary_13_4_arith := by
  intro n U ν hn hν hU hUn
  have hn0 : 0 < n := by linarith
  constructor
  · calc 41 * U ≤ n * n ^ ν := mul_le_mul hn hUn hU hn0.le
      _ = n ^ (ν + 1) := by rw [Real.rpow_add hn0, Real.rpow_one]; ring
  · exact Real.rpow_le_rpow hn0.le (by linarith) (by linarith)

theorem corollary_13_3_arith : Corollary_13_3_arith := by
  intro ν ε hν hε
  set c := Real.log (10 * (ν + 1)) with hc
  have hc0 : 0 < c := Real.log_pos (by linarith)
  refine ⟨8 + 3 * c + ε, fun n hn => ?_⟩
  intro r
  have he : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hn0 : 0 < n := lt_of_lt_of_le (Real.exp_pos _) hn
  set Lg := Real.log n with hLg
  have hLe : Real.exp 1 ≤ Lg := by
    rw [hLg, ← Real.log_exp (Real.exp 1)]; exact Real.log_le_log (Real.exp_pos _) hn
  have hL0 : 0 < Lg := by linarith
  set l := Real.log Lg with hl
  have hl1 : 1 ≤ l := by
    rw [hl, ← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hLe
  have hlL : l ≤ Lg := by
    have := Real.log_le_sub_one_of_pos hL0; rw [← hl] at this; linarith
  set x := Lg / l with hx
  have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ (by linarith)]; linarith
  set s := Real.sqrt (Lg * l) with hs
  have hs1 : 1 ≤ s := by
    rw [hs, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hsx : Real.sqrt x ≤ s := by
    rw [hs, hx]; apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by linarith)]
    have h11 : 1 ≤ l * l := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h11 hL0.le]
  have hsx1 : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hx1
  have hls : l ≤ s := by
    have : Real.sqrt (l ^ 2) ≤ Real.sqrt (Lg * l) := Real.sqrt_le_sqrt (by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at this
  have hxl : Real.sqrt x * l = s := by
    rw [hs, ← Real.sqrt_sq (by positivity : 0 ≤ Real.sqrt x * l)]
    congr 1
    rw [mul_pow, Real.sq_sqrt (by positivity), hx]
    field_simp
  have hLx : Lg / Real.sqrt x = s := by
    rw [hs, ← Real.sqrt_sq (by positivity : 0 ≤ Lg / Real.sqrt x)]
    congr 1
    rw [div_pow, Real.sq_sqrt (by positivity), hx]
    field_simp
  -- `r ∈ [√x, 2√x]`
  have hr1 : Real.sqrt x ≤ r := Nat.le_ceil _
  have hr2 : (r : ℝ) ≤ 2 * Real.sqrt x := by
    have := Nat.ceil_lt_add_one (Real.sqrt_nonneg x); linarith
  have hr0 : (0 : ℝ) < r := by linarith
  -- the logarithm of the factor
  have hf : (r : ℝ) * (10 * (ν + 1)) ^ (r + 1) * Lg ^ (r + 4) * n ^ (ε / r)
      = Real.exp (Real.log r + (r + 1) * c + (r + 4) * l + ε * Lg / r) := by
    have e1 : (10 * (ν + 1)) ^ (r + 1) = Real.exp ((r + 1) * c) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith), ← hc]; push_cast; ring_nf
    have e2 : Lg ^ (r + 4) = Real.exp ((r + 4) * l) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hL0, ← hl]; push_cast; ring_nf
    have e3 : n ^ (ε / r) = Real.exp (ε * Lg / r) := by
      rw [Real.rpow_def_of_pos hn0, ← hLg]; ring_nf
    rw [e1, e2, e3, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hr0]
  rw [hf, Real.exp_le_exp]
  have h1 : Real.log r ≤ 2 * s := by
    have := Real.log_le_sub_one_of_pos hr0; linarith
  have h2 : ((r : ℝ) + 1) * c ≤ 3 * c * s := by nlinarith
  have h3 : ((r : ℝ) + 4) * l ≤ 6 * s := by nlinarith
  have h4 : ε * Lg / r ≤ ε * s := by
    rw [← hLx, mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hε.le
    exact div_le_div_of_nonneg_left hL0.le (by linarith) hr1
  nlinarith

end ThinMatrixProducts

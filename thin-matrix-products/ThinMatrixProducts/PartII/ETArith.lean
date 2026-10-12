import ThinMatrixProducts.PartII.ThreeSumArith

/-!
# Section 15: the arithmetic of the parameters, of the cost and of Corollary 15.3; Link 3; APSP
-/

namespace ThinMatrixProducts

open Real

theorem eq_15_7 : Eq_15_7 := by
  intro n U ε ξ Cc r hn hU hε hξ hr hC hCn ζ Λ σ P hh hσ2 h2 hσn
  have hζ : 1 < ζ := by
    have : Real.log 3 ≤ ζ := Real.log_le_log (by norm_num) (by linarith)
    have := log_three_gt'; linarith
  have hΛ1 : 1 ≤ Λ := by
    have : (1 : ℝ) ≤ (10 * ζ) ^ r := one_le_pow₀ (by linarith)
    simp only [Λ]; nlinarith
  have hΛ0 : 0 < Λ := by linarith
  have hσ : (2 : ℝ) ≤ σ := by exact_mod_cast hσ2
  have hsq : (σ : ℝ) ≤ Real.sqrt (n ^ ε / Λ) := Nat.floor_le (Real.sqrt_nonneg _)
  have hsq1 : (1 : ℝ) ≤ Real.sqrt (n ^ ε / Λ) := by linarith
  have hn0 : 0 < n := by linarith
  set y := ζ * (ξ * σ) ^ (1 / (r : ℝ)) with hy
  have hy1 : 1 ≤ y := by nlinarith
  have hP5 : (P : ℝ) ≤ 5 * y := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 4 * y)
    simp only [P, ← hy, mul_assoc] at this ⊢
    nlinarith
  have hσ2' : (σ : ℝ) ^ 2 ≤ n ^ ε / Λ := by
    calc (σ : ℝ) ^ 2 ≤ (Real.sqrt (n ^ ε / Λ)) ^ 2 := pow_le_pow_left₀ (by positivity) hsq 2
      _ = n ^ ε / Λ := Real.sq_sqrt (by positivity)
  refine ⟨by have := half_le_floor hsq1; simpa [σ] using this, ?_, ?_, ?_, ?_, ?_⟩
  · calc (σ : ℝ) ≤ Real.sqrt (n ^ ε / Λ) := hsq
      _ ≤ Real.sqrt (n ^ ε) := Real.sqrt_le_sqrt (div_le_self (by positivity) hΛ1)
      _ = n ^ (ε / 2) := by rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn0.le]; ring_nf
  · rw [le_div_iff₀ hΛ0] at hσ2'; linarith
  · have hσ0 : (0 : ℝ) < σ := by linarith
    have : (hh : ℝ) < Cc / σ + 1 := Nat.ceil_lt_add_one (by positivity)
    have h1 : Cc / σ ≤ n / σ := div_le_div_of_nonneg_right hCn hσ0.le
    have h2 : (1 : ℝ) ≤ n / σ := by rw [le_div_iff₀ hσ0]; linarith
    have e : 2 * n / σ = n / σ + n / σ := by ring
    linarith
  · have hP0 : (0 : ℝ) ≤ P := Nat.cast_nonneg _
    calc (2 * (P : ℝ)) ^ r ≤ (10 * y) ^ r := pow_le_pow_left₀ (by positivity) (by linarith) r
      _ = (10 * ζ) ^ r * ((ξ * σ) ^ (1 / (r : ℝ))) ^ r := by rw [hy, ← mul_assoc, mul_pow]
      _ = Λ * σ := by
          rw [← Real.rpow_natCast ((ξ * σ) ^ (1 / (r : ℝ))), ← Real.rpow_mul (by positivity),
            show 1 / (r : ℝ) * r = 1 by field_simp, Real.rpow_one]
          simp only [Λ]; ring
  · have := Nat.le_ceil (4 * ζ * (ξ * σ) ^ (1 / (r : ℝ)))
    have h4 : 8 * ζ ≤ 4 * ζ * (ξ * σ) ^ (1 / (r : ℝ)) := by nlinarith
    simp only [P]
    linarith

theorem eq_15_8 : Eq_15_8 := by
  intro n U ν ε γ ξ σ P L r hn hU hν hUn hε hγ hγ2 hξ hξ4 hr hσ ζ Λ hσlow hσup hP0 hP hL0 hL
  have hn0 : 0 < n := by linarith
  have hlnn : 0 < Real.log n := Real.log_pos (by linarith)
  have hlζ := (sec13_log_bounds n U ν hn hU hν hUn).2
  have hζ1 : 1 < ζ := by
    have : Real.log 3 ≤ ζ := Real.log_le_log (by norm_num) (by linarith)
    have := log_three_gt'; linarith
  have hΛ1 : 1 ≤ Λ := by
    have : (1 : ℝ) ≤ (10 * ζ) ^ r := one_le_pow₀ (by linarith)
    simp only [Λ]; nlinarith
  have hΛ0 : 0 < Λ := by linarith
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hσ0 : 0 < σ := by linarith
  -- `(ξσ)^{1/r} ≤ 4 n^{ε/(2r)}`
  have hroot : (ξ * σ) ^ (1 / (r : ℝ)) ≤ 4 * n ^ (ε / (2 * r)) := by
    calc (ξ * σ) ^ (1 / (r : ℝ)) ≤ (4 * n ^ (ε / 2)) ^ (1 / (r : ℝ)) :=
          Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
      _ = 4 ^ (1 / (r : ℝ)) * n ^ (ε / (2 * r)) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn0.le]
          congr 2; field_simp
      _ ≤ 4 ^ (1 : ℝ) * n ^ (ε / (2 * r)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by rw [div_le_one (by linarith)]; exact hr')
      _ = 4 * n ^ (ε / (2 * r)) := by rw [Real.rpow_one]
  have hP' : P ≤ 20 * ζ * n ^ (ε / (2 * r)) := by
    calc P ≤ 5 * ζ * (ξ * σ) ^ (1 / (r : ℝ)) := hP
      _ ≤ 5 * ζ * (4 * n ^ (ε / (2 * r))) := mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = 20 * ζ * n ^ (ε / (2 * r)) := by ring
  -- `σ^{-2γ} ≤ 4^γ Λ^γ n^{-εγ}`
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
  have hL3 : L ≤ 3 * Real.log n := le_trans hL (logb_two_add_one_le hn)
  have hΛsplit : Λ ^ (1 - γ) * Λ ^ γ = Λ := by rw [← Real.rpow_add hΛ0]; simp
  have h4 : (4 : ℝ) ^ γ ≤ 2 := by
    calc (4 : ℝ) ^ γ ≤ 4 ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ2
      _ = 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  have hΛ4 : Λ ≤ 4 * (10 * ζ) ^ r := by
    simp only [Λ]; exact mul_le_mul_of_nonneg_right hξ4 (by positivity)
  have hlog : 10 * ζ ≤ 10 * (ν + 2) * Real.log n := by nlinarith
  have hpowlog : (10 * ζ) ^ (r + 1) ≤ (10 * (ν + 2)) ^ (r + 1) * Real.log n ^ (r + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hlog _
  have hnexp : n ^ (ε / (2 * r)) * n ^ 3 * n ^ (-(ε * γ)) = n ^ (3 - ε * γ + ε / (2 * r)) := by
    rw [show (n : ℝ) ^ 3 = n ^ (3 : ℝ) by norm_num, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
    ring_nf
  calc L * r * P * n ^ 3 * Λ ^ (1 - γ) * σ ^ (-(2 * γ))
      ≤ (3 * Real.log n) * r * (20 * ζ * n ^ (ε / (2 * r))) * n ^ 3 * Λ ^ (1 - γ)
          * (4 ^ γ * Λ ^ γ * n ^ (-(ε * γ))) := by
        gcongr
    _ = 60 * 4 ^ γ * r * Real.log n * ζ * (Λ ^ (1 - γ) * Λ ^ γ)
          * (n ^ (ε / (2 * r)) * n ^ 3 * n ^ (-(ε * γ))) := by ring
    _ = 60 * 4 ^ γ * r * Real.log n * ζ * Λ * n ^ (3 - ε * γ + ε / (2 * r)) := by
        rw [hΛsplit, hnexp]
    _ ≤ 60 * 2 * r * Real.log n * ζ * (4 * (10 * ζ) ^ r) * n ^ (3 - ε * γ + ε / (2 * r)) := by
        gcongr
    _ = 48 * r * Real.log n * (10 * ζ) ^ (r + 1) * n ^ (3 - ε * γ + ε / (2 * r)) := by ring
    _ ≤ 48 * r * Real.log n * ((10 * (ν + 2)) ^ (r + 1) * Real.log n ^ (r + 1))
          * n ^ (3 - ε * γ + ε / (2 * r)) := by gcongr
    _ = 48 * r * n ^ (3 - ε * γ + ε / (2 * r)) * (10 * (ν + 2)) ^ (r + 1)
          * (Real.log n) ^ (r + 2) := by ring

theorem corollary_15_3_arith : Corollary_15_3_arith := by
  intro ν ε hν hε
  obtain ⟨C, hC⟩ := corollary_13_3_arith (ν + 1) ε (by linarith) hε
  refine ⟨C, fun n hn => ?_⟩
  intro r
  have h := hC n hn
  have he : (1 : ℝ) < Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hn0 : 0 < n := lt_of_lt_of_le (Real.exp_pos _) hn
  have hlog1 : 1 ≤ Real.log n := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (le_trans (Real.exp_le_exp.2 he.le) hn)
  have hn1 : 1 ≤ n := by
    have := Real.add_one_le_exp (Real.exp 1); linarith [Real.exp_pos 1]
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  refine le_trans ?_ h
  rw [show ν + 1 + 1 = ν + 2 by ring]
  have e1 : Real.log n ^ (r + 2) ≤ Real.log n ^ (r + 4) := pow_le_pow_right₀ hlog1 (by omega)
  have e2 : n ^ (ε / (2 * r)) ≤ n ^ (ε / r) := by
    apply Real.rpow_le_rpow_of_exponent_le hn1
    rcases eq_or_lt_of_le hr0 with h0 | h0
    · rw [← h0]; simp
    · rw [div_le_div_iff₀ (by positivity) h0]; nlinarith
  gcongr

theorem sec15_link3 : Sec15_link3 := by
  intro U' present _ w hU hw w'
  have hb : ∀ e, present e → -U' ≤ w e ∧ w e ≤ U' := fun e he => abs_le.1 (hw e he)
  by_cases h0 : present 0 <;> by_cases h1 : present 1 <;> by_cases h2 : present 2 <;>
    simp only [w', h0, h1, h2, if_true, if_false]
  all_goals first
    | (constructor
       · intro h; exact ⟨fun e => by fin_cases e <;> assumption, h⟩
       · rintro ⟨-, h⟩; exact h)
    | (constructor
       · intro h; exfalso
         first
          | (have := hb 0 h0; have := hb 1 h1; omega)
          | (have := hb 0 h0; have := hb 2 h2; omega)
          | (have := hb 1 h1; have := hb 2 h2; omega)
          | (have := hb 0 h0; omega)
          | (have := hb 1 h1; omega)
          | (have := hb 2 h2; omega)
          | omega
       · rintro ⟨hall, -⟩
         exfalso
         first | exact h0 (hall 0) | exact h1 (hall 1) | exact h2 (hall 2))

theorem sec15_apsp_encoding : Sec15_apsp_encoding := by
  refine ⟨fun B x y hB hx hy => ?_, fun n ν hn => ?_⟩
  · have := abs_le.1 hx; have := abs_le.1 hy
    refine ⟨by linarith, by linarith, by linarith⟩
  · have h1 : 1 ≤ n ^ (ν + 1) := Nat.one_le_pow _ _ (by omega)
    calc 3 * n ^ (ν + 1) + 1 ≤ 4 * n ^ (ν + 1) := by omega
      _ ≤ n * n ^ (ν + 1) := Nat.mul_le_mul_right _ hn
      _ = n ^ (ν + 2) := by ring

theorem lemma_15_6_arith : Lemma_15_6_arith := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ m Λ n ε hσ hm hΛ
    calc σ * m ≤ σ * (Λ * σ) := mul_le_mul_of_nonneg_left hm hσ
      _ = Λ * σ ^ 2 := by ring
      _ ≤ n ^ ε := hΛ
  · intro m w n D hw hsum hD hX
    set X := n ^ 2 / Real.sqrt D with hXdef
    have hb := half_le_floor hX
    have hb0 : (0 : ℝ) < ⌊X⌋₊ := by linarith
    have hsD : 0 < Real.sqrt D := Real.sqrt_pos.2 hD
    have hn2 : 0 < n ^ 2 := by
      have : 0 < X := by linarith
      rw [hXdef] at this
      exact (div_pos_iff_of_pos_right hsD).1 this
    calc (∑ ϱ, (⌈w ϱ / ⌊X⌋₊⌉₊ : ℝ)) ≤ ∑ ϱ, (w ϱ / ⌊X⌋₊ + 1) :=
          Finset.sum_le_sum fun ϱ _ => (Nat.ceil_lt_add_one (by have := hw ϱ; positivity)).le
      _ = (∑ ϱ, w ϱ) / ⌊X⌋₊ + m := by
          rw [Finset.sum_add_distrib, Finset.sum_div]; simp
      _ ≤ n ^ 2 / (X / 2) + m := by
          gcongr
      _ = m + 2 * Real.sqrt D := by
          have hn0 : n ≠ 0 := by rintro rfl; simp at hn2
          rw [hXdef]; field_simp; ring
  · intro σ m Λ n γ C hσ hm hmΛ hΛ hγ hγ2 hC
    have hσ0 : 0 < σ := by linarith
    have hm0 : 0 < m := by linarith
    have hsm : 0 < σ * m := by positivity
    have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
    rcases le_or_gt m σ with hle | hgt
    · -- `m ≤ σ`: `m ≤ √(σm)`
      have hroot : m ≤ Real.sqrt (σ * m) := by
        have : Real.sqrt (m ^ 2) ≤ Real.sqrt (σ * m) := Real.sqrt_le_sqrt (by nlinarith)
        rwa [Real.sqrt_sq hm0.le] at this
      have h1 : (m + 2 * Real.sqrt (σ * m)) * (σ * m) ^ (-γ) ≤ 3 * (σ * m) ^ (1 / 2 - γ) := by
        rw [show (σ * m) ^ (1 / 2 - γ) = Real.sqrt (σ * m) * (σ * m) ^ (-γ) by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hsm]; ring_nf]
        have : 0 < (σ * m) ^ (-γ) := Real.rpow_pos_of_pos hsm _
        nlinarith
      have h2 : (σ * m) ^ (1 / 2 - γ) ≤ σ ^ (1 - 2 * γ) := by
        calc (σ * m) ^ (1 / 2 - γ) ≤ (σ ^ 2) ^ (1 / 2 - γ) :=
              Real.rpow_le_rpow hsm.le (by nlinarith) (by linarith)
          _ = σ ^ (1 - 2 * γ) := by
              rw [← Real.rpow_natCast σ 2, ← Real.rpow_mul hσ0.le]; congr 1; push_cast; ring
      have h3 : σ ^ (1 - 2 * γ) ≤ Λ ^ (1 - γ) * σ ^ (1 - 2 * γ) :=
        le_mul_of_one_le_left (by positivity) (Real.one_le_rpow hΛ (by linarith))
      calc (m + 2 * Real.sqrt (σ * m)) * (C * n ^ 2 * (σ * m) ^ (-γ))
          = C * n ^ 2 * ((m + 2 * Real.sqrt (σ * m)) * (σ * m) ^ (-γ)) := by ring
        _ ≤ C * n ^ 2 * (3 * Λ ^ (1 - γ) * σ ^ (1 - 2 * γ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            nlinarith
        _ = 3 * C * n ^ 2 * Λ ^ (1 - γ) * σ ^ (1 - 2 * γ) := by ring
    · -- `m > σ`: `√(σm) < m`
      have hroot : Real.sqrt (σ * m) ≤ m := by
        have : Real.sqrt (σ * m) ≤ Real.sqrt (m ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        rwa [Real.sqrt_sq hm0.le] at this
      have h1 : (m + 2 * Real.sqrt (σ * m)) * (σ * m) ^ (-γ) ≤ 3 * (m ^ (1 - γ) * σ ^ (-γ)) := by
        rw [Real.mul_rpow hσ0.le hm0.le]
        have e : m * (σ ^ (-γ) * m ^ (-γ)) = m ^ (1 - γ) * σ ^ (-γ) := by
          rw [Real.rpow_sub hm0, Real.rpow_one, Real.rpow_neg hm0.le]; field_simp
        have : 0 < σ ^ (-γ) * m ^ (-γ) := by positivity
        nlinarith
      have h2 : m ^ (1 - γ) * σ ^ (-γ) ≤ Λ ^ (1 - γ) * σ ^ (1 - 2 * γ) := by
        calc m ^ (1 - γ) * σ ^ (-γ) ≤ (Λ * σ) ^ (1 - γ) * σ ^ (-γ) :=
              mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hm0.le hmΛ (by linarith)) (by positivity)
          _ = Λ ^ (1 - γ) * σ ^ (1 - 2 * γ) := by
              rw [Real.mul_rpow (by linarith) hσ0.le, mul_assoc, ← Real.rpow_add hσ0]; ring_nf
      calc (m + 2 * Real.sqrt (σ * m)) * (C * n ^ 2 * (σ * m) ^ (-γ))
          = C * n ^ 2 * ((m + 2 * Real.sqrt (σ * m)) * (σ * m) ^ (-γ)) := by ring
        _ ≤ C * n ^ 2 * (3 * (Λ ^ (1 - γ) * σ ^ (1 - 2 * γ))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
        _ = 3 * C * n ^ 2 * Λ ^ (1 - γ) * σ ^ (1 - 2 * γ) := by ring
  · intro σ n γ hσ hσn hγ hγ2
    have hσ0 : 0 < σ := by linarith
    have hn0 : 0 < n := by linarith
    have hn1 : 1 ≤ n := by linarith
    constructor
    · rw [div_eq_mul_inv, ← Real.rpow_neg_one]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
    · have h1 : n ^ (-(1 : ℝ)) ≤ σ ^ (-(2 * γ)) := by
        calc n ^ (-(1 : ℝ)) ≤ n ^ (-(2 * γ)) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
          _ ≤ σ ^ (-(2 * γ)) := Real.rpow_le_rpow_of_nonpos hσ0 hσn (by linarith)
      calc n ^ 2 = n ^ 3 * n ^ (-(1 : ℝ)) := by
            rw [Real.rpow_neg_one, show (n : ℝ) ^ 3 = n ^ 2 * n by ring]; field_simp
        _ ≤ n ^ 3 * σ ^ (-(2 * γ)) := mul_le_mul_of_nonneg_left h1 (by positivity)

end ThinMatrixProducts

import ThinMatrixProducts.PartII.ThreeSumArith

/-!
# Section 14 (Theorem 14.1): the arithmetic of the parameters and of the consequence; Link 2

The parameter bounds follow the proof of Theorem 14.1 line by line; the consequence rescales the
instances to `n' := Λ^{1/(2-2α)} n`.
-/

namespace ThinMatrixProducts

open Real

theorem theorem_14_1_params : Theorem_14_1_params := by
  intro n U ν α c₁ c₂ P m r hn hU hν hUn hα hα1 hc₁ hc₂ hr σ g Λ ΛS hcn hbig
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have hl2 := log_two_gt
  have hlogs := sec13_log_bounds n U ν hn hU hν hUn
  have hlU : Real.log 2 ≤ Real.log (2 * U) := Real.log_le_log (by norm_num) (by linarith)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  -- `σ`
  set x := n ^ (1 - α) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow hn1 (by linarith)
  have hσx : (σ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hσhalf : x / 2 ≤ σ := half_le_floor hx1
  have hσ1 : (1 : ℝ) ≤ σ := by
    have : 1 ≤ σ := Nat.le_floor (by exact_mod_cast hx1)
    exact_mod_cast this
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hx2 : x ^ 2 = n ^ (2 - 2 * α) := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    norm_num
    ring_nf
  have hσ2 : (σ : ℝ) ^ 2 ≤ n ^ (2 - 2 * α) := by
    rw [← hx2]; exact pow_le_pow_left₀ (by positivity) hσx 2
  have hg : (g : ℝ) ≤ 2 * (c₁ * n / σ) := ceil_le_two_mul hcn
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  -- `Λ_S ≤ Λ`, `Λ ≥ 1`
  have hb : 10 * Real.log (2 * U) ≤ 10 * (ν + 1) * Real.log n := by
    have := hlogs.1; nlinarith
  have hΛS : ΛS ≤ Λ := by
    simp only [ΛS, Λ]
    have : (10 * Real.log (2 * U)) ^ r ≤ (10 * (ν + 1) * Real.log n) ^ r :=
      pow_le_pow_left₀ (by nlinarith) hb r
    linarith
  have hΛ1 : 1 ≤ Λ := by
    simp only [Λ]
    have h1 : 1 ≤ 10 * (ν + 1) * Real.log n := by nlinarith
    have := one_le_pow₀ (n := r) h1
    linarith
  refine ⟨hΛS, ?_, ?_, ?_, hσx, ?_, ?_⟩
  · -- `P ≤ 10(ν+1) n^{(2-2α)/r} ln n`
    intro hP0 hP
    have h1 : (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) ≤ 2 * n ^ ((2 - 2 * α) / r) := by
      calc (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) ≤ (2 * n ^ (2 - 2 * α)) ^ (1 / (r : ℝ)) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
        _ = 2 ^ (1 / (r : ℝ)) * n ^ ((2 - 2 * α) / r) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn0.le]
            congr 2
            ring
        _ ≤ 2 * n ^ ((2 - 2 * α) / r) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc (2 : ℝ) ^ (1 / (r : ℝ)) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num)
                    (by rw [div_le_one hr0]; exact_mod_cast hr)
              _ = 2 := Real.rpow_one 2
    have hl0 : 0 ≤ Real.log (2 * U) := by linarith
    calc P ≤ 5 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) := hP
      _ ≤ 5 * ((ν + 1) * Real.log n) * (2 * n ^ ((2 - 2 * α) / r)) := by
          apply mul_le_mul _ h1 (by positivity) (by nlinarith)
          linarith [hlogs.1]
      _ = 10 * (ν + 1) * n ^ ((2 - 2 * α) / r) * Real.log n := by ring
  · -- `Λ_S σ² ≤ Λ n^{2-2α}`
    have hΛS0 : 0 ≤ ΛS := by
      have := pow_nonneg (by linarith : (0 : ℝ) ≤ 10 * Real.log (2 * U)) r
      simp only [ΛS]
      linarith
    exact mul_le_mul hΛS hσ2 (by positivity) (by linarith)
  · -- `N = g(2T+1) ≤ 10 c₁ √Λ n`
    intro hm0 hm
    have hT := Nat.ceil_lt_add_one (Real.sqrt_nonneg m)
    have hsq : Real.sqrt m ≤ Real.sqrt Λ * σ := by
      rw [← Real.sqrt_sq hσ0.le, ← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt hm.le
    have hsΛ : 1 ≤ Real.sqrt Λ := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hΛ1
    have h5 : 2 * (⌈Real.sqrt m⌉₊ : ℝ) + 1 ≤ 5 * (Real.sqrt Λ * σ) := by nlinarith
    calc (g : ℝ) * (2 * ⌈Real.sqrt m⌉₊ + 1) ≤ (2 * (c₁ * n / σ)) * (5 * (Real.sqrt Λ * σ)) :=
          mul_le_mul hg h5 (by positivity) (by positivity)
      _ = 10 * c₁ * Real.sqrt Λ * n := by field_simp; ring
  · -- `c₂ g² σ ≤ 8 c₁² c₂ n^{1+α}`
    have hn2 : n ^ (2 : ℕ) = x * n ^ (1 + α) := by
      rw [hx, ← Real.rpow_add hn0, ← Real.rpow_natCast]
      norm_num
    calc c₂ * (g : ℝ) ^ 2 * σ ≤ c₂ * (2 * (c₁ * n / σ)) ^ 2 * σ := by
          apply mul_le_mul_of_nonneg_right _ hσ0.le
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hg 2) hc₂.le
      _ = 4 * c₁ ^ 2 * c₂ * n ^ 2 / σ := by field_simp; ring
      _ ≤ 4 * c₁ ^ 2 * c₂ * n ^ 2 / (x / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hσhalf
      _ = 8 * c₁ ^ 2 * c₂ * n ^ (1 + α) := by
          rw [hn2]; field_simp; ring
  · -- `L ≤ 3 log₂ n` and `|𝒫₀| ≤ 2^L`
    intro hy1
    set y := c₂ * (g : ℝ) ^ 2 * σ with hy
    have hy8 : y ≤ 8 * c₁ ^ 2 * c₂ * n ^ (1 + α) := by
      -- the previous bullet, repeated
      have hn2 : n ^ (2 : ℕ) = x * n ^ (1 + α) := by
        rw [hx, ← Real.rpow_add hn0, ← Real.rpow_natCast]
        norm_num
      calc y ≤ c₂ * (2 * (c₁ * n / σ)) ^ 2 * σ := by
            apply mul_le_mul_of_nonneg_right _ hσ0.le
            exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg0 hg 2) hc₂.le
        _ = 4 * c₁ ^ 2 * c₂ * n ^ 2 / σ := by field_simp; ring
        _ ≤ 4 * c₁ ^ 2 * c₂ * n ^ 2 / (x / 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hσhalf
        _ = 8 * c₁ ^ 2 * c₂ * n ^ (1 + α) := by
            rw [hn2]; field_simp; ring
    have hly : 0 ≤ Real.logb 2 y := Real.logb_nonneg (by norm_num) hy1
    have hceil := Nat.ceil_lt_add_one hly
    have h2y : Real.logb 2 y + 1 ≤ 3 * Real.logb 2 n := by
      have : Real.logb 2 (2 * y) ≤ Real.logb 2 (n ^ 3) :=
        Real.logb_le_logb_of_le (by norm_num) (by linarith) (by linarith)
      rw [Real.logb_mul (by norm_num) (by linarith), Real.logb_self_eq_one (by norm_num),
        Real.logb_pow] at this
      push_cast at this
      linarith
    refine ⟨by linarith, ?_⟩
    calc y = 2 ^ Real.logb 2 y := (Real.rpow_logb (by norm_num) (by norm_num) (by linarith)).symm
      _ ≤ 2 ^ (⌈Real.logb 2 y⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = 2 ^ ⌈Real.logb 2 y⌉₊ := Real.rpow_natCast 2 _

theorem theorem_14_1_consequence : Theorem_14_1_consequence := by
  intro n ν α η r hn hν hα hα1 hη hηα hr Λ n'
  have hn0 : 0 < n := by linarith
  have hn1 : 1 ≤ n := by linarith
  have hln : 1 ≤ Real.log n := by
    have := Real.add_one_le_exp 1
    rw [Real.le_log_iff_exp_le hn0]
    have h3 : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; linarith
    linarith
  have hb : 1 ≤ 10 * (ν + 1) * Real.log n := by nlinarith
  have hΛ1 : 1 ≤ Λ := by
    simp only [Λ]
    have := one_le_pow₀ (n := r) hb
    linarith
  have hΛ0 : 0 < Λ := by linarith
  have hηa : η ≤ α := le_trans hηα (min_le_left _ _)
  have hηb : η ≤ 1 - α := le_trans hηα (min_le_right _ _)
  have h2a : 0 < 2 - 2 * α := by linarith
  set a := 1 / (2 - 2 * α) with ha
  have ha0 : 0 < a := by positivity
  have ha2 : 1 / 2 ≤ a := by rw [ha]; exact one_div_le_one_div_of_le h2a (by linarith)
  have hΛa : 1 ≤ Λ ^ a := Real.one_le_rpow hΛ1 ha0.le
  have hnn' : n ≤ n' := by simp only [n']; nlinarith
  have hn'0 : 0 < n' := by linarith
  have hb1 : 1 / 2 ≤ 1 / (1 - α) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have hsqrt : Real.sqrt Λ = Λ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow Λ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [n']
    rw [Real.mul_rpow (by positivity) hn0.le, ← Real.rpow_mul hΛ0.le,
      show a * (2 - 2 * α) = 1 by rw [ha, one_div, inv_mul_cancel₀ h2a.ne'], Real.rpow_one]
  · simp only [n']
    rw [hsqrt]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hΛ1 ha2) hn0.le
  · exact Real.rpow_le_rpow hn0.le hnn' (by linarith)
  · exact Real.rpow_le_rpow hn0.le hnn' (by linarith)
  · simp only [n']
    rw [Real.mul_rpow (by positivity) hn0.le, ← Real.rpow_mul hΛ0.le]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hΛ1
    rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ h2a (by linarith)]
    nlinarith
  · exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  · rw [hsqrt]; exact Real.rpow_le_rpow_of_exponent_le hΛ1 hb1
  · simp only [Λ]
    have h10 : 0 ≤ 10 * (ν + 1) := by linarith
    have hl0 : 0 ≤ Real.log n := by linarith
    rw [mul_pow, Real.mul_rpow (by norm_num) (by positivity),
      Real.mul_rpow (by positivity) (by positivity), mul_assoc]
    congr 2
    · rw [← Real.rpow_natCast, ← Real.rpow_mul h10]
      congr 1; ring
    · rw [← Real.rpow_natCast, ← Real.rpow_mul hl0]
      congr 1; ring

theorem sec15_link2 : Sec15_link2 := by
  intro ι s c cneg h
  rw [h]
  exact Finset.sum_pos_iff

end ThinMatrixProducts

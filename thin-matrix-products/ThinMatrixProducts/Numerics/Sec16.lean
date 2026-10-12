import ThinMatrixProducts.Numerics.Lambda
import ThinMatrixProducts.Numerics.Threshold

/-!
# The exponents of the problems: Corollary 16.1, the introduction, Sections 13.7, 15.7 and 10
-/

namespace ThinMatrixProducts

open Real

theorem corollary_16_1_a_constant : Corollary_16_1_a_constant := by
  unfold Corollary_16_1_a_constant; norm_num

/-- `⌊x⌋ ≥ x/2` for `x ≥ 1`. -/
lemma floor_ge_half {x : ℝ} (hx : 1 ≤ x) : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [Nat.floor_eq_zero] at h; linarith)
  linarith

theorem corollary_16_1_a_steps : Corollary_16_1_a_steps := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D hD
    have hD' : (4 : ℝ) ≤ D := by exact_mod_cast hD
    have hD0 : (0 : ℝ) < D := by linarith
    have hsq : Real.sqrt D = (D : ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow D
    rcases eq_or_lt_of_le hD with h4 | h5
    · subst h4
      have : ((4 : ℕ) : ℝ) ^ (0.0385 : ℝ) ≤ 2 := by
        rw [show ((4 : ℕ) : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
        calc (2 : ℝ) ^ ((2 : ℝ) * 0.0385) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      have hc : ⌈((4 : ℕ) : ℝ) ^ (0.0385 : ℝ)⌉₊ ≤ 2 := Nat.ceil_le.2 (by exact_mod_cast this)
      have : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
        rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [this]; exact_mod_cast hc
    · have hD5 : (5 : ℝ) ≤ D := by exact_mod_cast h5
      -- `D^{0.0385} ≤ √D - 1 < ⌊√D⌋ + …`, so `⌈D^{0.0385}⌉ ≤ ⌊√D⌋ ≤ √D`
      have hs2 : 2 ≤ Real.sqrt D := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt (by linarith)
      have hratio : (2 : ℝ) ≤ (D : ℝ) ^ (0.4615 : ℝ) := by
        have : (5 : ℝ) ^ (0.4615 : ℝ) ≤ (D : ℝ) ^ (0.4615 : ℝ) :=
          Real.rpow_le_rpow (by norm_num) hD5 (by norm_num)
        refine le_trans ?_ this
        rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm,
          Real.rpow_def_of_pos (by norm_num), Real.exp_le_exp]
        have h2 := log_two_lt'; have h5 := log_five_gt'
        nlinarith
      have hy : (D : ℝ) ^ (0.0385 : ℝ) ≤ Real.sqrt D - 1 := by
        have e : Real.sqrt D = (D : ℝ) ^ (0.0385 : ℝ) * (D : ℝ) ^ (0.4615 : ℝ) := by
          rw [hsq, ← Real.rpow_add hD0]; norm_num
        have hpos : 0 < (D : ℝ) ^ (0.0385 : ℝ) := Real.rpow_pos_of_pos hD0 _
        nlinarith
      have hfl : Real.sqrt D - 1 < (⌊Real.sqrt D⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one (Real.sqrt D); linarith
      have hc : ⌈(D : ℝ) ^ (0.0385 : ℝ)⌉₊ ≤ ⌊Real.sqrt D⌋₊ := Nat.ceil_le.2 (by linarith)
      calc (⌈(D : ℝ) ^ (0.0385 : ℝ)⌉₊ : ℝ) ≤ ⌊Real.sqrt D⌋₊ := by exact_mod_cast hc
        _ ≤ Real.sqrt D := Nat.floor_le (Real.sqrt_nonneg _)
  · intro n D hn hD
    rw [show (-0.0385 : ℝ) = 0.0385 - 0.077 by norm_num, Real.rpow_sub hD]
    field_simp
  · intro n D hn hD hDn
    have hn0 : 0 < n := by linarith
    have h1 : D ^ (3 / 2 : ℝ) ≤ n ^ ((3 : ℝ) / 28) := by
      calc D ^ (3 / 2 : ℝ) ≤ (n ^ ((1 : ℝ) / 14)) ^ (3 / 2 : ℝ) :=
            Real.rpow_le_rpow hD.le hDn (by norm_num)
        _ = n ^ ((3 : ℝ) / 28) := by rw [← Real.rpow_mul hn0.le]; norm_num
    have h7 : Real.logb 2 7 + 3 / 28 ≤ 2.92 := by
      rw [Real.logb, div_add' _ _ _ (Real.log_pos (by norm_num)).ne',
        div_le_iff₀ (Real.log_pos (by norm_num))]
      have := log_seven_lt'; have := log_two_gt'
      nlinarith
    calc n ^ Real.logb 2 7 * D ^ (3 / 2 : ℝ) ≤ n ^ Real.logb 2 7 * n ^ ((3 : ℝ) / 28) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hn0.le _)
      _ = n ^ (Real.logb 2 7 + 3 / 28) := (Real.rpow_add hn0 _ _).symm
      _ ≤ n ^ (2.92 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn h7
  · intro n hn
    have hx : (1 : ℝ) ≤ n ^ ((1 : ℝ) / 14) := Real.one_le_rpow hn (by norm_num)
    have hD := floor_ge_half hx
    refine ⟨hD, ?_⟩
    have hn0 : 0 < n := by linarith
    have hpos : 0 < n ^ ((1 : ℝ) / 14) / 2 := by positivity
    calc ((⌊n ^ ((1 : ℝ) / 14)⌋₊ : ℕ) : ℝ) ^ (-0.0385 : ℝ)
        ≤ (n ^ ((1 : ℝ) / 14) / 2) ^ (-0.0385 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hpos hD (by norm_num)
      _ = 2 ^ (0.0385 : ℝ) * n ^ (-0.00275 : ℝ) := by
          rw [Real.div_rpow (by positivity) (by norm_num), ← Real.rpow_mul hn0.le,
            Real.rpow_neg (by norm_num) (0.0385 : ℝ)]
          norm_num
          ring
      _ ≤ 2 * n ^ (-0.00275 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn0.le _)
          calc (2 : ℝ) ^ (0.0385 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2

theorem corollary_16_1_b_exponents : Corollary_16_1_b_exponents := by
  refine ⟨fun e he0 he1 => ⟨?_, by ring⟩, by norm_num, by norm_num, by norm_num, by norm_num⟩
  rw [max_eq_right (by linarith)]; ring

theorem corollary_16_1_cd_exponents : Corollary_16_1_cd_exponents := by
  unfold Corollary_16_1_cd_exponents; norm_num

theorem sec1_preprint_exponents : Sec1_preprint_exponents := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    fun e => ⟨by ring, rfl, by ring⟩⟩

theorem sec13_7_table : Sec13_7_table := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · intro ε γ r hε hγ hr
    rw [div_lt_iff₀ (by positivity)]
    constructor
    · intro h
      have : ε / r < 3 / 4 * (ε * γ) := by linarith
      rw [div_lt_iff₀ hr] at this
      nlinarith
    · intro h
      have : ε < 3 / 4 * (ε * γ) * r := by nlinarith
      have h' : ε / r < 3 / 4 * (ε * γ) := by rw [div_lt_iff₀ hr]; linarith
      linarith
  · intro r
    constructor
    · intro h
      by_contra h'
      have : (r : ℝ) ≤ 21 := by exact_mod_cast (show r ≤ 21 by omega)
      norm_num at h
      linarith
    · intro h
      have : (22 : ℝ) ≤ r := by exact_mod_cast h
      norm_num
      linarith

theorem sec15_7_table : Sec15_7_table := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    fun ε γ r hε hγ hr => ⟨?_, ?_⟩, fun r => ?_, fun r => ?_⟩
  · rw [div_lt_iff₀ hγ]
    constructor
    · intro h
      have : ε / (2 * r) < ε * γ / 2 := by linarith
      rw [div_lt_iff₀ (by positivity)] at this
      nlinarith
    · intro h
      have h' : ε / (2 * r) < ε * γ / 2 := by
        rw [div_lt_iff₀ (by positivity)]; nlinarith
      linarith
  · rw [div_lt_iff₀ (by positivity)]
    constructor
    · intro h
      have : ε / (2 * r) < 5 / 6 * (ε * γ) := by linarith
      rw [div_lt_iff₀ (by positivity)] at this
      nlinarith
    · intro h
      have h' : ε / (2 * r) < 5 / 6 * (ε * γ) := by
        rw [div_lt_iff₀ (by positivity)]; nlinarith
      linarith
  · constructor
    · intro h
      by_contra h'
      have : (r : ℝ) ≤ 15 := by exact_mod_cast (show r ≤ 15 by omega)
      norm_num at h
      linarith
    · intro h
      have : (16 : ℝ) ≤ r := by exact_mod_cast h
      norm_num
      linarith
  · constructor
    · intro h
      by_contra h'
      have : (r : ℝ) ≤ 9 := by exact_mod_cast (show r ≤ 9 by omega)
      norm_num at h
      linarith
    · intro h
      have : (10 : ℝ) ≤ r := by exact_mod_cast h
      norm_num
      linarith

theorem sec13_7_crossing : Sec13_7_crossing := by
  have h2 := log_two_gt'; have h2' := log_two_lt'
  have l46 := log_mem 0 8 (by norm_num : (0 : ℝ) < 4.6e5 / 2 ^ 19)
  have l47 := log_mem 0 8 (by norm_num : (0 : ℝ) < 4.7e5 / 2 ^ 19)
  have l50 := log_mem 0 8 (by norm_num : (0 : ℝ) < 5.0e5 / 2 ^ 19)
  have l52 := log_mem 0 8 (by norm_num : (0 : ℝ) < 5.2e5 / 2 ^ 19)
  have b46 : -0.1309 < logApprox 0 8 (4.6e5 / 2 ^ 19) - logErr 0 8 (4.6e5 / 2 ^ 19) := by numerics
  have b47 : logApprox 0 8 (4.7e5 / 2 ^ 19) + logErr 0 8 (4.7e5 / 2 ^ 19) < -0.1092 := by numerics
  have b50 : -0.0475 < logApprox 0 8 (5.0e5 / 2 ^ 19) - logErr 0 8 (5.0e5 / 2 ^ 19) := by numerics
  have b52 : logApprox 0 8 (5.2e5 / 2 ^ 19) + logErr 0 8 (5.2e5 / 2 ^ 19) < -0.0081 := by numerics
  unfold Sec13_7_crossing
  rw [log_eq_log_div_pow (4.6e5) (by norm_num) 19, log_eq_log_div_pow (4.7e5) (by norm_num) 19,
    log_eq_log_div_pow (5.0e5) (by norm_num) 19, log_eq_log_div_pow (5.2e5) (by norm_num) 19]
  push_cast
  refine ⟨by norm_num, by linarith [l46.1], by linarith [l47.2], by norm_num, by linarith [l50.1],
    by linarith [l52.2]⟩

theorem sec10_numbers : Sec10_numbers := by
  obtain ⟨h1, h2⟩ := sec1_epsStar5_value
  refine ⟨by linarith, by linarith, by norm_num⟩

end ThinMatrixProducts

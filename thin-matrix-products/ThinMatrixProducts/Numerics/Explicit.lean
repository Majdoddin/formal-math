import ThinMatrixProducts.Numerics.Corollary73
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Corollary 9.1: the explicit instances

Each step of the proof of Corollary 9.1 from the general steps of Corollary 7.3 and the numerical
facts of `ThinMatrixProducts.Numerics.Lambda`.
-/

namespace ThinMatrixProducts

open Real Finset Filter Topology

theorem corollary_9_1_setting_up : Corollary_9_1_setting_up := by
  intro D₀ hD
  have hD' : (2 : ℝ) ≤ D₀ := by exact_mod_cast hD
  set m := ⌈Real.logb 4 D₀⌉₊ with hm
  have hlog : 0 < Real.logb 4 D₀ := Real.logb_pos (by norm_num) (by linarith)
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by
    intro h; rw [hm, Nat.ceil_eq_zero] at h; linarith)
  have hle : Real.logb 4 D₀ ≤ m := Nat.le_ceil _
  have hlt : (m : ℝ) < Real.logb 4 D₀ + 1 := Nat.ceil_lt_add_one hlog.le
  have hD0 : (0 : ℝ) < D₀ := by linarith
  have h1 : (D₀ : ℝ) ≤ 4 ^ m := by
    rw [← Real.rpow_natCast, ← Real.logb_le_iff_le_rpow (by norm_num) hD0]; exact hle
  have h2 : (4 : ℝ) ^ m < 4 * D₀ := by
    rw [← Real.rpow_natCast]
    calc (4 : ℝ) ^ (m : ℝ) < 4 ^ (Real.logb 4 D₀ + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hlt
      _ = 4 * D₀ := by
          rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hD0,
            Real.rpow_one]; ring
  refine ⟨hm1, h1, h2, fun a N hN => ?_⟩
  have h3 : (4 : ℝ) ^ (m - 1) ≤ D₀ := by
    have : (4 : ℝ) ^ m = 4 * 4 ^ (m - 1) := by
      rw [← pow_succ']; congr 1; omega
    linarith
  calc (4 : ℝ) ^ (a * (m - 1)) = ((4 : ℝ) ^ (m - 1)) ^ a := by rw [← pow_mul, mul_comm]
    _ ≤ (D₀ : ℝ) ^ a := pow_le_pow_left₀ (by positivity) h3 a
    _ ≤ N := hN

/-- `A ≤ r^m` for all `m ≥ m₀`, from the base case and a ratio condition. -/
lemma threshold_induction {A B r : ℝ} (m₀ : ℕ) (hr : 1 ≤ r)
    (hbase : A * (B * m₀ + 2) ≤ r ^ m₀)
    (hstep : ∀ m : ℕ, m₀ ≤ m → A * (B * (m + 1) + 2) ≤ r * (A * (B * m + 2))) :
    ∀ m : ℕ, m₀ ≤ m → A * (B * m + 2) ≤ r ^ m := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => exact hbase
  | succ m hm ih =>
    push_cast
    calc A * (B * (m + 1) + 2) ≤ r * (A * (B * m + 2)) := hstep m hm
      _ ≤ r * r ^ m := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = r ^ (m + 1) := by ring

theorem corollary_9_1_a_threshold : Corollary_9_1_a_threshold := by
  have := threshold_induction (A := (4 : ℝ) ^ 18 * 75) (B := 14.5) (r := 1.657) 72 (by norm_num)
    (by norm_num) (fun m hm => by
      have : (72 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith)
  intro m hm
  have h := this m hm
  linarith

theorem corollary_9_1_b_threshold : Corollary_9_1_b_threshold := by
  have := threshold_induction (A := (4 : ℝ) ^ 14 * 75) (B := 11.5) (r := 1.268) 131 (by norm_num)
    (by norm_num) (fun m hm => by
      have : (131 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith)
  intro m hm
  have h := this m hm
  linarith

/-- The encodings step of Corollary 9.1, from (4), `(25/4)/μ_∞² < 75`, `r Λ < 4^a` and the
threshold `4^a 75 (cm+2) ≤ r^m`. -/
lemma encodings_of {c Λ r γ : ℝ} {a : ℕ} (hc : 5 < c) (hγ : 0 ≤ γ) (hΛ : Λ = LambdaC c γ)
    (hr : 0 < r) (hrΛ : r * Λ < 4 ^ a) (m : ℕ) (hm : 1 ≤ m) (hm' : (4 : ℝ) ^ a * 75 * (c * m + 2) ≤ r ^ m) (N Kg : ℝ)
    (hN : (4 : ℝ) ^ (a * (m - 1)) ≤ N) (hKg : muInf ^ 2 * K (levelsOf c m) m ≤ Kg)
    (hKgK : Kg ≤ K (levelsOf c m) m) :
    Dr m ^ γ * (25 : ℝ) ^ levelsOf c m / (Kg * N0 (levelsOf c m) m) ≤ N ∧
      (K (levelsOf c m) m : ℝ) * N0 (levelsOf c m) m ≤ N := by
  have h4 := eq_4 c γ hc hγ m hm Kg hKg
  have h75 := eq_4_constant
  have hΛ0 : 0 < Λ := hΛ ▸ LambdaC_pos c γ
  have hm0 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcm : 0 < c * m + 2 := by positivity
  -- `75 (cm+2) Λ^m ≤ 4^{a(m-1)}`
  have hpow : Λ ^ m * r ^ m ≤ ((4 : ℝ) ^ a) ^ m := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) m
  have hkey : 75 * (c * m + 2) * Λ ^ m ≤ (4 : ℝ) ^ (a * (m - 1)) := by
    have h4a : (0 : ℝ) < 4 ^ a := by positivity
    have e : ((4 : ℝ) ^ a) ^ m = 4 ^ a * 4 ^ (a * (m - 1)) := by
      rw [← pow_mul, ← pow_add]; congr 1
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp; ring
    have : 4 ^ a * (75 * (c * m + 2) * Λ ^ m) ≤ 4 ^ a * (4 : ℝ) ^ (a * (m - 1)) := by
      calc 4 ^ a * (75 * (c * m + 2) * Λ ^ m) = (4 ^ a * 75 * (c * m + 2)) * Λ ^ m := by ring
        _ ≤ r ^ m * Λ ^ m := mul_le_mul_of_nonneg_right hm' (by positivity)
        _ ≤ ((4 : ℝ) ^ a) ^ m := by linarith
        _ = 4 ^ a * (4 : ℝ) ^ (a * (m - 1)) := e
    exact le_of_mul_le_mul_left this h4a
  have hfirst : Dr m ^ γ * (25 : ℝ) ^ levelsOf c m / (Kg * N0 (levelsOf c m) m) ≤ N := by
    calc _ ≤ (25 / 4) / muInf ^ 2 * (c * m + 2) * LambdaC c γ ^ m := h4
      _ ≤ 75 * (c * m + 2) * Λ ^ m := by
          rw [← hΛ]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right h75.le hcm.le
      _ ≤ (4 : ℝ) ^ (a * (m - 1)) := hkey
      _ ≤ N := hN
  refine ⟨hfirst, ?_⟩
  have hmL : m ≤ levelsOf c m := by
    have : (m : ℝ) ≤ levelsOf c m := le_trans (by nlinarith) (Nat.le_ceil (c * m))
    exact_mod_cast this
  have hKpos : (0 : ℝ) < K (levelsOf c m) m := by
    have : 0 < K (levelsOf c m) m := Nat.choose_pos hmL
    exact_mod_cast this
  have hmu : 0 < muInf := by linarith [muInf_bounds.1]
  exact corollary_7_3_tile_fit.2 _ _ γ Kg N hmL hγ (lt_of_lt_of_le (by positivity) hKg) hKgK hfirst

theorem corollary_9_1_a_encodings : Corollary_9_1_a_encodings := by
  intro m hm N Kg hN hKg hKgK
  have hγ : 0 ≤ gammaA := by linarith [corollary_9_1_a_exponents.1]
  exact encodings_of (c := 14.5) (Λ := LambdaA) (r := 1.657) (a := 18) (by norm_num) hγ rfl
    (by norm_num) corollary_9_1_a_Lambda.2.2.2.2.2 m (by omega)
    (corollary_9_1_a_threshold m hm) N Kg hN hKg hKgK

theorem corollary_9_1_b_encodings : Corollary_9_1_b_encodings := by
  intro m hm N Kg hN hKg hKgK
  have hγ : 0 ≤ gammaB := by linarith [corollary_9_1_b_exponents.1]
  exact encodings_of (c := 11.5) (Λ := LambdaB) (r := 1.268) (a := 14) (by norm_num) hγ rfl
    (by norm_num) corollary_9_1_b_Lambda.2.2.2.2 m (by omega)
    (corollary_9_1_b_threshold m hm) N Kg hN hKg hKgK

theorem corollary_9_1_a_boxes : Corollary_9_1_a_boxes := by
  intro m hm
  obtain ⟨h1, h2, h3, h4, h5⟩ := corollary_7_3_boxes 14.5 (1 / 19) (by norm_num) (by norm_num) m hm
  have hc : rhoC 14.5 = 8 / 27 := by rw [rhoC]; norm_num
  rw [hc] at h1 h3
  have hg : gammaOf 14.5 (1 / 19) = gammaA := corollary_9_1_a_exponents.2.2.2.2.2.1.symm
  rw [hg] at h5
  refine ⟨h1, by norm_num at h3 ⊢; linarith, le_trans h4 h5.le⟩

theorem corollary_9_1_b_boxes : Corollary_9_1_b_boxes := by
  intro m hm
  obtain ⟨h1, h2, h3, h4, h5⟩ := corollary_7_3_boxes 11.5 (1 / 18) (by norm_num) (by norm_num) m hm
  have hc : rhoC 11.5 = 8 / 21 := by rw [rhoC]; norm_num
  rw [hc] at h1
  have hg : gammaOf 11.5 (1 / 18) = gammaB := corollary_9_1_b_exponents.2.2.2.2.2.1.symm
  rw [hg] at h5
  exact ⟨h1, le_trans h4 h5.le⟩

/-- The strict form of the query bound, `∑ ≤ (4x)^t (1+1/x)^{2m} < 4x D^q`. -/
lemma queries_strict {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 0.8) (m : ℕ) :
    (∑ d ∈ range (switchOf θ m + 1), ((2 * m).choose d : ℝ) * 4 ^ d)
      < 4 * ((1 - θ) / θ) * Dr m ^ qOf θ := by
  set x := (1 - θ) / θ with hx
  have hx0 : 0 < x := div_pos (by linarith) hθ
  have h4x : 1 < 4 * x := (corollary_7_3_queries θ hθ hθ1 m).1
  set t := switchOf θ m
  have ht : (t : ℝ) < 2 * θ * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have ht2 : t ≤ 2 * m := by
    apply Nat.ceil_le.2
    push_cast
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hsum : (∑ d ∈ range (t + 1), ((2 * m).choose d : ℝ) * 4 ^ d)
      ≤ (4 * x) ^ t * (1 + 1 / x) ^ (2 * m) := by
    rw [add_comm (1 : ℝ) (1 / x), add_pow, mul_sum]
    calc (∑ d ∈ range (t + 1), ((2 * m).choose d : ℝ) * 4 ^ d)
        ≤ ∑ d ∈ range (t + 1), (4 * x) ^ t * ((1 / x) ^ d * 1 ^ (2 * m - d) * ((2 * m).choose d)) := by
          refine sum_le_sum fun d hd => ?_
          have := four_pow_le hx0 h4x.le (Nat.lt_succ_iff.1 (mem_range.1 hd))
          rw [one_pow, mul_one]
          nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ((2 * m).choose d : ℝ))]
      _ ≤ ∑ d ∈ range (2 * m + 1), (4 * x) ^ t * ((1 / x) ^ d * 1 ^ (2 * m - d) * ((2 * m).choose d)) := by
          apply sum_le_sum_of_subset_of_nonneg
          · exact range_subset_range.2 (by omega)
          · intro i _ _; positivity
  have hpow : (4 * x) ^ t < 4 * x * (4 * x) ^ (2 * θ * m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_one_add' (by linarith) (by positivity)]
    exact Real.rpow_lt_rpow_of_exponent_lt h4x (by linarith)
  have hid := (corollary_7_3_queries θ hθ hθ1 m).2.1
  have h1x : 1 + 1 / x = 1 / (1 - θ) := by
    have : (1 - θ) ≠ 0 := by linarith
    rw [hx]; field_simp; ring
  have hDq : Dr m ^ qOf θ = ((4 : ℝ) ^ θ * Real.exp (H θ)) ^ (2 * m) := by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Dr_rpow, show (4 : ℝ) ^ θ * Real.exp (H θ) = Real.exp (θ * Real.log 4 + H θ) by
      rw [Real.rpow_def_of_pos (by norm_num), Real.exp_add]; ring_nf, ← Real.exp_nat_mul]
    congr 1
    unfold qOf
    rw [log_four_eq]
    field_simp
    push_cast
    ring
  have hsplit : (4 * x) ^ (2 * θ * m) * (1 + 1 / x) ^ (2 * m) = Dr m ^ qOf θ := by
    rw [hDq, ← hid, h1x, show 2 * θ * (m : ℝ) = θ * ((2 * m : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul (by positivity), Real.rpow_natCast, ← mul_pow]
    ring
  calc (∑ d ∈ range (t + 1), ((2 * m).choose d : ℝ) * 4 ^ d)
      ≤ (4 * x) ^ t * (1 + 1 / x) ^ (2 * m) := hsum
    _ < 4 * x * (4 * x) ^ (2 * θ * m) * (1 + 1 / x) ^ (2 * m) :=
        mul_lt_mul_of_pos_right hpow (by positivity)
    _ = 4 * x * Dr m ^ qOf θ := by rw [mul_assoc, hsplit]

theorem corollary_9_1_a_queries : Corollary_9_1_a_queries := by
  intro m _
  have h := queries_strict (θ := 1 / 19) (by norm_num) (by norm_num) m
  rw [← corollary_9_1_a_exponents.2.2.2.2.2.2] at h
  norm_num at h ⊢
  exact h

theorem corollary_9_1_b_queries : Corollary_9_1_b_queries := by
  intro m _
  have h := queries_strict (θ := 1 / 18) (by norm_num) (by norm_num) m
  rw [← corollary_9_1_b_exponents.2.2.2.2.2.2] at h
  norm_num at h ⊢
  exact h

/-- `m^k D^{-a} ≤ C` for `a > 0`. -/
lemma poly_mul_Dr_neg_bdd (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ m : ℕ, (m : ℝ) ^ k * Dr m ^ (-a) ≤ C := by
  have hr : (1 : ℝ) < 4 ^ a := Real.one_lt_rpow (by norm_num) ha
  have h := tendsto_pow_const_div_const_pow_of_one_lt k hr
  obtain ⟨C, hC⟩ := h.bddAbove_range
  refine ⟨C, fun m => le_trans (le_of_eq ?_) (hC ⟨m, rfl⟩)⟩
  rw [Dr, ← Real.rpow_natCast (4 : ℝ) m, ← Real.rpow_mul (by norm_num)]
  show (m : ℝ) ^ k * (4 : ℝ) ^ ((m : ℝ) * -a) = (m : ℝ) ^ k / ((4 : ℝ) ^ a) ^ m
  rw [div_eq_mul_inv, ← Real.rpow_natCast ((4 : ℝ) ^ a), ← Real.rpow_mul (by norm_num),
    ← Real.rpow_neg (by norm_num)]
  ring_nf

theorem corollary_9_1_conclusion : Corollary_9_1_conclusion := by
  have ea := corollary_9_1_a_exponents
  have eb := corollary_9_1_b_exponents
  obtain ⟨C1, h1⟩ := poly_mul_Dr_neg_bdd 3 (a := gammaA - 0.092) (by linarith [ea.1])
  obtain ⟨C2, h2⟩ := poly_mul_Dr_neg_bdd 1 (a := 0.403 - qA) (by linarith [ea.2.2.2.1])
  obtain ⟨C3, h3⟩ := poly_mul_Dr_neg_bdd 2 (a := 0.403) (by norm_num)
  obtain ⟨C4, h4⟩ := poly_mul_Dr_neg_bdd 3 (a := gammaB - 0.077) (by linarith [eb.1])
  obtain ⟨C5, h5⟩ := poly_mul_Dr_neg_bdd 1 (a := 0.421 - qB) (by linarith [eb.2.2.2.1])
  obtain ⟨C6, h6⟩ := poly_mul_Dr_neg_bdd 2 (a := 0.421) (by norm_num)
  refine ⟨max C1 (max (C2 + C3) (max C4 (C5 + C6))), fun m => ?_⟩
  have hD : 0 < Dr m := by unfold Dr; positivity
  have split : ∀ (x y : ℝ), Dr m ^ (x - y) = Dr m ^ x * Dr m ^ (-y) := fun x y => by
    rw [sub_eq_add_neg, Real.rpow_add hD]
  have pos : ∀ x : ℝ, 0 < Dr m ^ x := fun x => Real.rpow_pos_of_pos hD x
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := h1 m
    rw [show -(gammaA - 0.092) = -gammaA + 0.092 by ring, Real.rpow_add hD] at this
    have hp := pos (-0.092)
    have : (m : ℝ) ^ 3 * Dr m ^ (-gammaA) ≤ C1 * Dr m ^ (-0.092 : ℝ) := by
      have e : Dr m ^ (0.092 : ℝ) * Dr m ^ (-0.092 : ℝ) = 1 := by
        rw [← Real.rpow_add hD]; norm_num
      calc (m : ℝ) ^ 3 * Dr m ^ (-gammaA)
          = ((m : ℝ) ^ 3 * (Dr m ^ (-gammaA) * Dr m ^ (0.092 : ℝ))) * Dr m ^ (-0.092 : ℝ) := by
            rw [mul_assoc, mul_assoc, e, mul_one]
        _ ≤ C1 * Dr m ^ (-0.092 : ℝ) := mul_le_mul_of_nonneg_right this hp.le
    exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left _ _) (pos _).le)
  · have a2 := h2 m; have a3 := h3 m
    rw [pow_one, show -(0.403 - qA) = qA - 0.403 by ring, split] at a2
    have hp := pos 0.403
    have e : Dr m ^ (0.403 : ℝ) * Dr m ^ (-0.403 : ℝ) = 1 := by
      rw [← Real.rpow_add hD]; norm_num
    have b2 : (m : ℝ) * Dr m ^ qA ≤ C2 * Dr m ^ (0.403 : ℝ) := by
      calc (m : ℝ) * Dr m ^ qA = ((m : ℝ) * (Dr m ^ qA * Dr m ^ (-0.403 : ℝ))) * Dr m ^ (0.403 : ℝ) := by
            rw [mul_assoc, mul_assoc, mul_comm (Dr m ^ (-0.403 : ℝ)), e, mul_one]
        _ ≤ C2 * Dr m ^ (0.403 : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hp.le
    have b3 : (m : ℝ) ^ 2 ≤ C3 * Dr m ^ (0.403 : ℝ) := by
      calc (m : ℝ) ^ 2 = ((m : ℝ) ^ 2 * Dr m ^ (-0.403 : ℝ)) * Dr m ^ (0.403 : ℝ) := by
            rw [mul_assoc, mul_comm (Dr m ^ (-0.403 : ℝ)), e, mul_one]
        _ ≤ C3 * Dr m ^ (0.403 : ℝ) := mul_le_mul_of_nonneg_right a3 hp.le
    calc (m : ℝ) * Dr m ^ qA + (m : ℝ) ^ 2 ≤ (C2 + C3) * Dr m ^ (0.403 : ℝ) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (le_trans (le_max_left _ _) (le_max_right _ _)) hp.le
  · have := h4 m
    rw [show -(gammaB - 0.077) = -gammaB + 0.077 by ring, Real.rpow_add hD] at this
    have hp := pos (-0.077)
    have : (m : ℝ) ^ 3 * Dr m ^ (-gammaB) ≤ C4 * Dr m ^ (-0.077 : ℝ) := by
      have e : Dr m ^ (0.077 : ℝ) * Dr m ^ (-0.077 : ℝ) = 1 := by
        rw [← Real.rpow_add hD]; norm_num
      calc (m : ℝ) ^ 3 * Dr m ^ (-gammaB)
          = ((m : ℝ) ^ 3 * (Dr m ^ (-gammaB) * Dr m ^ (0.077 : ℝ))) * Dr m ^ (-0.077 : ℝ) := by
            rw [mul_assoc, mul_assoc, e, mul_one]
        _ ≤ C4 * Dr m ^ (-0.077 : ℝ) := mul_le_mul_of_nonneg_right this hp.le
    exact le_trans this (mul_le_mul_of_nonneg_right
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) (pos _).le)
  · have a5 := h5 m; have a6 := h6 m
    rw [pow_one, show -(0.421 - qB) = qB - 0.421 by ring, split] at a5
    have hp := pos 0.421
    have e : Dr m ^ (0.421 : ℝ) * Dr m ^ (-0.421 : ℝ) = 1 := by
      rw [← Real.rpow_add hD]; norm_num
    have b5 : (m : ℝ) * Dr m ^ qB ≤ C5 * Dr m ^ (0.421 : ℝ) := by
      calc (m : ℝ) * Dr m ^ qB = ((m : ℝ) * (Dr m ^ qB * Dr m ^ (-0.421 : ℝ))) * Dr m ^ (0.421 : ℝ) := by
            rw [mul_assoc, mul_assoc, mul_comm (Dr m ^ (-0.421 : ℝ)), e, mul_one]
        _ ≤ C5 * Dr m ^ (0.421 : ℝ) := mul_le_mul_of_nonneg_right (by linarith) hp.le
    have b6 : (m : ℝ) ^ 2 ≤ C6 * Dr m ^ (0.421 : ℝ) := by
      calc (m : ℝ) ^ 2 = ((m : ℝ) ^ 2 * Dr m ^ (-0.421 : ℝ)) * Dr m ^ (0.421 : ℝ) := by
            rw [mul_assoc, mul_comm (Dr m ^ (-0.421 : ℝ)), e, mul_one]
        _ ≤ C6 * Dr m ^ (0.421 : ℝ) := mul_le_mul_of_nonneg_right a6 hp.le
    calc (m : ℝ) * Dr m ^ qB + (m : ℝ) ^ 2 ≤ (C5 + C6) * Dr m ^ (0.421 : ℝ) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hp.le

end ThinMatrixProducts

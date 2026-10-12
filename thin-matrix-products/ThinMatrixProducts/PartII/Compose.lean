import ThinMatrixProducts.PartII.ETArith
import ThinMatrixProducts.PartII.ExactTriangle
import ThinMatrixProducts.PartII.Primes

/-!
# Sections 13 and 15: the parameters for large `n`, and the composition with the correctness lemmas

The side conditions of Sections 13.3 and 15.1 ("`n ≥ n₀` large enough"), proved uniformly for
`1 ≤ r ≤ r(n) = ⌈√(ln n/ln ln n)⌉`, and Theorems 13.2, 15.1, 15.2 (correctness) with those
parameters.

The analytic core (`asymp_core`): with `t = ln n` and `l = ln t`, for large `t`,
`K + 2√(t/l)(c + l) ≤ εt/4` and `2 ln 16 + 10 + l ≤ (ε/8)√(tl)`. Then `Λ ≤ 4 e^{εt/4-8}` because
`r ≤ 2√(t/l)`, so `n^ε/Λ ≥ 4e^{εt/2}` and `σ ≥ e^{εt/4}`; the root `σ^{1/r} ≥ e^y` with
`y = (ε/8)√(tl)`; and `P ≥ 2e^y` gives `P ≥ 1024` (as `y ≥ 10`) and `4r ln P ≤ P` (as
`e^{ln P/2} ≥ 16√t ≥ 8r`).
-/

namespace ThinMatrixProducts

open Real Finset

/-- `ln t ≤ 2√t`. -/
lemma log_le_two_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 ht)
  rw [Real.log_sqrt ht.le] at h
  linarith

/-- The analytic core: for large `t`, with `l = ln t`, `K + 2√(t/l)(c + l) ≤ εt/4` and
`2 ln 16 + 10 + l ≤ (ε/8)√(tl)`. -/
lemma asymp_core (ε c K : ℝ) (hε : 0 < ε) (_hc : 0 ≤ c) (_hK : 0 ≤ K) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      14 ≤ Real.log t ∧ Real.log t ≤ t ∧
      K + 2 * Real.sqrt (t / Real.log t) * (c + Real.log t) ≤ ε * t / 4 ∧
      2 * Real.log 16 + 10 + Real.log t ≤ ε / 8 * Real.sqrt (t * Real.log t) := by
  set δ := ε / 32 with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨max (Real.exp (max c 14)) (max (8 * K / ε) (4 / δ ^ 4)),
    le_max_of_le_left (Real.one_le_exp (by positivity)), fun t ht => ?_⟩
  have ht1 : Real.exp (max c 14) ≤ t := le_of_max_le_left ht
  have ht2 : 8 * K / ε ≤ t := le_trans (le_max_left _ _) (le_of_max_le_right ht)
  have ht3 : 4 / δ ^ 4 ≤ t := le_trans (le_max_right _ _) (le_of_max_le_right ht)
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht1
  have hlm : max c 14 ≤ Real.log t := by
    have := Real.log_le_log (Real.exp_pos _) ht1
    rwa [Real.log_exp] at this
  set l := Real.log t with hl
  have hl14 : 14 ≤ l := le_trans (le_max_right _ _) hlm
  have hcl : c ≤ l := le_trans (le_max_left _ _) hlm
  have hl0 : 0 < l := by linarith
  have hlt : l ≤ t := by have := Real.log_le_sub_one_of_pos ht0; linarith
  -- `l ≤ δ² t`
  set s := Real.sqrt t with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg t
  have hss : s * s = t := Real.mul_self_sqrt ht0.le
  have hδs : 2 ≤ δ ^ 2 * s := by
    have h4 : 4 ≤ δ ^ 4 * t := by
      rw [div_le_iff₀ (by positivity)] at ht3; linarith
    by_contra hcon
    push Not at hcon
    have : (δ ^ 2 * s) * (δ ^ 2 * s) < 2 * 2 := mul_self_lt_mul_self (by positivity) hcon
    nlinarith
  have hl2 : l ≤ 2 * s := log_le_two_sqrt ht0
  have hlδ : l ≤ δ ^ 2 * t := by
    rw [← hss]; nlinarith [mul_nonneg (sub_nonneg.2 hδs) hs0]
  -- `√(tl) = √(t/l) · l`
  have hkey : Real.sqrt (t * l) = Real.sqrt (t / l) * l := by
    have : Real.sqrt (t / l) * Real.sqrt (l ^ 2) = Real.sqrt (t * l) := by
      rw [← Real.sqrt_mul (div_nonneg ht0.le hl0.le)]; congr 1; field_simp
    rw [← this, Real.sqrt_sq hl0.le]
  refine ⟨hl14, hlt, ?_, ?_⟩
  · have h1 : Real.sqrt (t * l) ≤ δ * t := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ δ * t)]
      apply Real.sqrt_le_sqrt
      nlinarith
    have h2 : 2 * Real.sqrt (t / l) * (c + l) ≤ 4 * Real.sqrt (t * l) := by
      rw [hkey]; nlinarith [Real.sqrt_nonneg (t / l)]
    have h3 : 8 * K ≤ ε * t := by
      rw [div_le_iff₀ hε] at ht2; linarith
    have : 4 * (δ * t) = ε * t / 8 := by rw [hδ]; ring
    nlinarith
  · have h1 : l / δ ≤ Real.sqrt (t * l) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ l / δ)]
      apply Real.sqrt_le_sqrt
      rw [div_pow, div_le_iff₀ (by positivity)]
      nlinarith
    have h16 : Real.log 16 ≤ 15 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 16); linarith
    have : ε / 8 * (l / δ) = 4 * l := by rw [hδ]; field_simp; ring
    have h2 : ε / 8 * (l / δ) ≤ ε / 8 * Real.sqrt (t * l) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith

/-- `1024 ≤ e^{10}`. -/
lemma exp_ten_ge : (1024 : ℝ) ≤ Real.exp 10 := by
  calc (1024 : ℝ) = Real.exp (Real.log 2) ^ 10 := by rw [Real.exp_log (by norm_num)]; norm_num
    _ = Real.exp (10 * Real.log 2) := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ Real.exp 10 := Real.exp_le_exp.2 (by have := Real.log_two_lt_d9; linarith)

set_option maxHeartbeats 2000000 in
/-- The side conditions common to Sections 13.3 and 15.1. With `Λ := ξ (10Z)^r`, `0 < Z ≤ A ln n`,
`10 Z ≥ 1`, `1 ≤ ξ ≤ 4` and `σ := ⌊√(n^ε/Λ)⌋`, for `n ≥ n₀` and `1 ≤ r ≤ r(n)`: `σ ≥ 2`,
`σ ≤ n`, `2nΛ ≤ n²`, `σ^{1/r} ≥ 2`, and every `P ≥ 2σ^{1/r}` has `P ≥ 1024` and
`r ≤ P/(4 ln P)`. -/
lemma side_core (A ε : ℝ) (hA : 1 ≤ A) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ n₀ : ℝ, 1 ≤ n₀ ∧ ∀ n : ℝ, n₀ ≤ n → ∀ r : ℕ, 1 ≤ r → r ≤ rOf n →
      ∀ Z ξ : ℝ, 0 < Z → Z ≤ A * Real.log n → 1 ≤ ξ → ξ ≤ 4 → 1 ≤ 10 * Z →
      2 ≤ ⌊Real.sqrt (n ^ ε / (ξ * (10 * Z) ^ r))⌋₊ ∧
      (⌊Real.sqrt (n ^ ε / (ξ * (10 * Z) ^ r))⌋₊ : ℝ) ≤ n ∧
      2 * n * (ξ * (10 * Z) ^ r) ≤ n ^ 2 ∧
      2 ≤ (⌊Real.sqrt (n ^ ε / (ξ * (10 * Z) ^ r))⌋₊ : ℝ) ^ (1 / (r : ℝ)) ∧
      ∀ P : ℝ, 2 * (⌊Real.sqrt (n ^ ε / (ξ * (10 * Z) ^ r))⌋₊ : ℝ) ^ (1 / (r : ℝ)) ≤ P →
        1024 ≤ P ∧ (r : ℝ) ≤ P / (4 * Real.log P) := by
  obtain ⟨T, hT1, hT⟩ := asymp_core ε (Real.log (10 * A)) 8 hε
    (Real.log_nonneg (by linarith)) (by norm_num)
  refine ⟨Real.exp T, Real.one_le_exp (by linarith),
    fun n hn r hr1 hrR Z ξ hZ0 hZ hξ1 hξ4 hZ1 => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (Real.exp_pos _) hn
  have hn1 : 1 ≤ n := le_trans (Real.one_le_exp (by linarith)) hn
  have htT : T ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos _) hn; rwa [Real.log_exp] at this
  have hnt : Real.exp (Real.log n) = n := Real.exp_log hn0
  have hR : (rOf n : ℝ) < Real.sqrt (Real.log n / Real.log (Real.log n)) + 1 :=
    Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hne : n ^ ε = Real.exp (ε * Real.log n) := by rw [Real.rpow_def_of_pos hn0, mul_comm]
  obtain ⟨hl14, hlt, hB, hy⟩ := hT (Real.log n) htT
  set t := Real.log n with ht
  set l := Real.log t with hl
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < l := by linarith
  -- `r ≤ 2√(t/l)` and `r ≤ 2√t`
  have hq1 : 1 ≤ t / l := by rw [le_div_iff₀ hl0]; linarith
  set rr := Real.sqrt (t / l) with hrr
  have hrr1 : 1 ≤ rr := by rw [hrr, ← Real.sqrt_one]; exact Real.sqrt_le_sqrt hq1
  have hr2 : (r : ℝ) ≤ 2 * rr := by
    have h1 : (r : ℝ) ≤ rOf n := by exact_mod_cast hrR
    linarith
  have hrrt : rr ≤ Real.sqrt t := Real.sqrt_le_sqrt (div_le_self ht0.le (by linarith))
  have hrt : (r : ℝ) ≤ 2 * Real.sqrt t := by linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  -- the bound on `Λ`
  set c := Real.log (10 * A) with hc
  have hc0 : 0 ≤ c := Real.log_nonneg (by linarith)
  have hZA : 10 * Z ≤ Real.exp (c + l) := by
    rw [Real.exp_add, hc, Real.exp_log (by linarith), hl, Real.exp_log ht0]; nlinarith
  set Λ := ξ * (10 * Z) ^ r with hΛ
  have hεt : 8 ≤ ε * t / 4 := by
    have : 0 ≤ 2 * rr * (c + l) := by positivity
    linarith
  have hΛup : Λ ≤ 4 * Real.exp (ε * t / 4 - 8) := by
    have h1 : (10 * Z) ^ r ≤ Real.exp (c + l) ^ r := pow_le_pow_left₀ (by linarith) hZA r
    rw [← Real.exp_nat_mul] at h1
    have h2 : (r : ℝ) * (c + l) ≤ ε * t / 4 - 8 := by
      have : (r : ℝ) * (c + l) ≤ 2 * rr * (c + l) := mul_le_mul_of_nonneg_right hr2 (by positivity)
      linarith
    have h3 := Real.exp_le_exp.2 h2
    exact mul_le_mul hξ4 (h1.trans h3) (by positivity) (by norm_num)
  have hΛ1 : 1 ≤ Λ := by
    have : 1 ≤ (10 * Z) ^ r := one_le_pow₀ hZ1
    rw [hΛ]; nlinarith
  have hΛ0 : 0 < Λ := by linarith
  set x := n ^ ε / Λ with hx
  have hx4 : 4 * Real.exp (ε * t / 2) ≤ x := by
    rw [hx, le_div_iff₀ hΛ0, hne]
    have e1 : Real.exp (ε * t) =
        Real.exp (ε * t / 4 + 8) * (Real.exp (ε * t / 2) * Real.exp (ε * t / 4 - 8)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have e2 : 16 ≤ Real.exp (ε * t / 4 + 8) := by
      have := Real.add_one_le_exp (ε * t / 4 + 8); linarith
    calc 4 * Real.exp (ε * t / 2) * Λ
        ≤ 4 * Real.exp (ε * t / 2) * (4 * Real.exp (ε * t / 4 - 8)) :=
          mul_le_mul_of_nonneg_left hΛup (by positivity)
      _ = 16 * (Real.exp (ε * t / 2) * Real.exp (ε * t / 4 - 8)) := by ring
      _ ≤ Real.exp (ε * t / 4 + 8) * (Real.exp (ε * t / 2) * Real.exp (ε * t / 4 - 8)) :=
          mul_le_mul_of_nonneg_right e2 (by positivity)
      _ = Real.exp (ε * t) := e1.symm
  have hx1 : 1 ≤ x := le_trans (by have := Real.one_le_exp (by positivity : 0 ≤ ε * t / 2); linarith) hx4
  set σ := ⌊Real.sqrt x⌋₊ with hσ
  have hsx : Real.sqrt x / 2 ≤ σ := by
    have : 1 ≤ Real.sqrt x := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hx1
    exact half_le_floor this
  have hσe : Real.exp (ε * t / 4) ≤ σ := by
    have e : Real.exp (ε * t / 4) * Real.exp (ε * t / 4) = Real.exp (ε * t / 2) := by
      rw [← Real.exp_add]; ring_nf
    have h1 : 2 * Real.exp (ε * t / 4) ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.exp (ε * t / 4))]
      apply Real.sqrt_le_sqrt
      nlinarith
    linarith
  have hσ2 : (2 : ℝ) ≤ σ := by
    have := Real.add_one_le_exp (ε * t / 4); linarith
  have hσ0 : (0 : ℝ) < σ := by linarith
  -- `σ ≤ n`
  have hσn : (σ : ℝ) ≤ n := by
    have h1 : (σ : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg _)
    have h2 : x ≤ n ^ ε := div_le_self (by positivity) hΛ1
    have h3 : n ^ ε ≤ n := by
      calc n ^ ε ≤ n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        _ = n := Real.rpow_one n
    have h4 : (σ : ℝ) * σ ≤ x := by
      calc (σ : ℝ) * σ ≤ Real.sqrt x * Real.sqrt x := mul_self_le_mul_self hσ0.le h1
        _ = x := Real.mul_self_sqrt (by linarith)
    have hnn : n ≤ n * n := by nlinarith
    exact (mul_self_le_mul_self_iff hσ0.le (by linarith)).2 (by linarith)
  -- `2nΛ ≤ n²`
  have h2nΛ : 2 * n * Λ ≤ n ^ 2 := by
    have e8 : 8 ≤ Real.exp 8 := by have := Real.add_one_le_exp (8 : ℝ); linarith
    have h1 : 8 * Real.exp (ε * t / 4 - 8) ≤ Real.exp (ε * t / 4) := by
      have : Real.exp (ε * t / 4) = Real.exp (ε * t / 4 - 8) * Real.exp 8 := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; nlinarith [Real.exp_pos (ε * t / 4 - 8)]
    have h2 : Real.exp (ε * t / 4) ≤ n := by
      rw [← hnt]; exact Real.exp_le_exp.2 (by nlinarith)
    have h3 : 2 * Λ ≤ n := by linarith
    nlinarith
  -- the root `σ^{1/r} ≥ e^y`
  set y := ε / 8 * Real.sqrt (t * l) with hyy
  have hy10 : 10 ≤ y := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 16); linarith
  have hsr : Real.exp y ≤ (σ : ℝ) ^ (1 / (r : ℝ)) := by
    have h1 : Real.exp (ε * t / 4) ^ (1 / (r : ℝ)) ≤ (σ : ℝ) ^ (1 / (r : ℝ)) :=
      Real.rpow_le_rpow (by positivity) hσe (by positivity)
    rw [← Real.exp_mul] at h1
    refine le_trans (Real.exp_le_exp.2 ?_) h1
    have hkey : Real.sqrt (t * l) * rr = t := by
      rw [hrr, ← Real.sqrt_mul (by positivity), show t * l * (t / l) = t ^ 2 by field_simp,
        Real.sqrt_sq ht0.le]
    rw [mul_one_div, le_div_iff₀ hr0]
    calc ε / 8 * Real.sqrt (t * l) * r ≤ ε / 8 * Real.sqrt (t * l) * (2 * rr) :=
          mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = ε / 4 * (Real.sqrt (t * l) * rr) := by ring
      _ = ε * t / 4 := by rw [hkey]; ring
  refine ⟨by exact_mod_cast hσ2, hσn, h2nΛ, ?_, ?_⟩
  · have := Real.add_one_le_exp y; linarith
  · intro P hP
    have hPy : 2 * Real.exp y ≤ P := by linarith
    have hey : Real.exp 10 ≤ Real.exp y := Real.exp_le_exp.2 hy10
    have hP1024 : 1024 ≤ P := by linarith [exp_ten_ge]
    refine ⟨hP1024, ?_⟩
    have hP0 : 0 < P := by linarith
    set u := Real.log P with hu
    have hPu : Real.exp u = P := Real.exp_log hP0
    have huy : y ≤ u := by
      rw [← Real.log_exp y]; exact Real.log_le_log (Real.exp_pos _) (by linarith [Real.exp_pos y])
    have hu0 : 0 < u := by linarith
    have h8r : 8 * (r : ℝ) ≤ Real.exp (u / 2) := by
      have e1 : Real.exp (Real.log 16 + l / 2) = 16 * Real.sqrt t := by
        rw [Real.exp_add, Real.exp_log (by norm_num), Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht0,
          hl]
        ring_nf
      have e2 : Real.log 16 + l / 2 ≤ u / 2 := by linarith
      calc 8 * (r : ℝ) ≤ 16 * Real.sqrt t := by linarith
        _ = Real.exp (Real.log 16 + l / 2) := e1.symm
        _ ≤ Real.exp (u / 2) := Real.exp_le_exp.2 e2
    have hP4 : 4 * r * u ≤ P := by
      have e1 : Real.exp (u / 2) * Real.exp (u / 2) = P := by rw [← Real.exp_add, add_halves, hPu]
      have e2 : u / 2 ≤ Real.exp (u / 2) := by linarith [Real.add_one_le_exp (u / 2)]
      have := mul_le_mul h8r e2 (by linarith) (Real.exp_pos _).le
      linarith
    rw [le_div_iff₀ (by positivity)]; linarith

/-! ## The side conditions -/

theorem sec13_rOf_unbounded : Sec13_rOf_unbounded := by
  intro r
  refine ⟨Real.exp (max (Real.exp 1) (4 * (r : ℝ) ^ 4)), fun n hn => ?_⟩
  have hn0 : 0 < n := lt_of_lt_of_le (Real.exp_pos _) hn
  have hT : max (Real.exp 1) (4 * (r : ℝ) ^ 4) ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos _) hn; rwa [Real.log_exp] at this
  set t := Real.log n
  have ht1 : Real.exp 1 ≤ t := le_of_max_le_left hT
  have ht4 : 4 * (r : ℝ) ^ 4 ≤ t := le_of_max_le_right hT
  have ht0 : 0 < t := lt_of_lt_of_le (Real.exp_pos _) ht1
  have hl1 : 1 ≤ Real.log t := by
    have := Real.log_le_log (Real.exp_pos _) ht1; rwa [Real.log_exp] at this
  have hs : 2 * (r : ℝ) ^ 2 ≤ Real.sqrt t := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2 * (r : ℝ) ^ 2)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hss : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0.le
  have hl2 := log_le_two_sqrt ht0
  have hrl : (r : ℝ) ^ 2 ≤ t / Real.log t := by
    rw [le_div_iff₀ (by linarith)]
    have : (r : ℝ) ^ 2 * Real.log t ≤ (r : ℝ) ^ 2 * (2 * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left hl2 (by positivity)
    nlinarith [Real.sqrt_nonneg t]
  have : (r : ℝ) ≤ Real.sqrt (t / Real.log t) := by
    rw [← Real.sqrt_sq (Nat.cast_nonneg r)]; exact Real.sqrt_le_sqrt hrl
  have := this.trans (Nat.le_ceil _)
  exact_mod_cast this

theorem sec13_side_conditions : Sec13_side_conditions := by
  intro ν ε c₁ hν hε hε1 hc₁
  obtain ⟨n₀, hn₀1, h⟩ := side_core (ν + 1) ε (by linarith) hε hε1
  refine ⟨max n₀ 2, fun n U r hn hU hUn hr1 hrR => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hlog := (sec13_log_bounds n U ν hn2 hU hν hUn).1
  have hl2 : Real.log 2 ≤ Real.log (2 * U) := Real.log_le_log (by norm_num) (by linarith)
  have hlt := Real.log_two_gt_d9
  have hZ0 : 0 < Real.log (2 * U) := by linarith
  obtain ⟨hσ2, hσn, -, hσr, hPc⟩ := h n (le_trans (le_max_left _ _) hn) r hr1 hrR
    (Real.log (2 * U)) 2 hZ0 hlog (by norm_num) (by norm_num) (by linarith)
  dsimp only
  set σ := ⌊Real.sqrt (n ^ ε / (2 * (10 * Real.log (2 * U)) ^ r))⌋₊ with hσ
  have hσ' : (2 : ℝ) ≤ σ := by exact_mod_cast hσ2
  have hroot : (σ : ℝ) ^ (1 / (r : ℝ)) ≤ (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
  have hP : 2 * (σ : ℝ) ^ (1 / (r : ℝ))
      ≤ (⌈4 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ))⌉₊ : ℝ) := by
    have h1 := Nat.le_ceil (4 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)))
    have h2 : 2 ≤ 4 * Real.log (2 * U) := by linarith
    have h3 : 0 ≤ (σ : ℝ) ^ (1 / (r : ℝ)) := by positivity
    nlinarith
  obtain ⟨hP1024, hrP⟩ := hPc _ hP
  refine ⟨hσ2, ?_, by exact_mod_cast hP1024, hrP, le_trans hσr hroot⟩
  rw [le_div_iff₀ (by positivity)]; nlinarith

theorem sec15_side_conditions : Sec15_side_conditions := by
  intro ν ε ξ hν hε hε1 hξ1 hξ4
  obtain ⟨n₀, hn₀1, h⟩ := side_core (ν + 2) ε (by linarith) hε hε1
  refine ⟨max n₀ 2, fun n U r hn hU hUn hr1 hrR => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hlog := (sec13_log_bounds n U ν hn2 hU hν hUn).2
  have hl3 : Real.log 3 ≤ Real.log (3 * U) := Real.log_le_log (by norm_num) (by linarith)
  have hlt := Real.log_three_gt_d9
  have hZ0 : 0 < Real.log (3 * U) := by linarith
  obtain ⟨hσ2, hσn, h2n, hσr, hPc⟩ := h n (le_trans (le_max_left _ _) hn) r hr1 hrR
    (Real.log (3 * U)) ξ hZ0 hlog hξ1 hξ4 (by linarith)
  dsimp only
  set σ := ⌊Real.sqrt (n ^ ε / (ξ * (10 * Real.log (3 * U)) ^ r))⌋₊ with hσ
  have hσ' : (2 : ℝ) ≤ σ := by exact_mod_cast hσ2
  have hroot : (σ : ℝ) ^ (1 / (r : ℝ)) ≤ (ξ * (σ : ℝ)) ^ (1 / (r : ℝ)) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
  have hP : 2 * (σ : ℝ) ^ (1 / (r : ℝ))
      ≤ (⌈4 * Real.log (3 * U) * (ξ * (σ : ℝ)) ^ (1 / (r : ℝ))⌉₊ : ℝ) := by
    have h1 := Nat.le_ceil (4 * Real.log (3 * U) * (ξ * (σ : ℝ)) ^ (1 / (r : ℝ)))
    have h2 : 2 ≤ 4 * Real.log (3 * U) := by linarith
    have h3 : 0 ≤ (σ : ℝ) ^ (1 / (r : ℝ)) := by positivity
    nlinarith
  obtain ⟨hP1024, hrP⟩ := hPc _ hP
  exact ⟨hσ2, by exact_mod_cast hP1024, hrP, le_trans hσr hroot, h2n, hσn⟩

theorem sec15_pieces : Sec15_pieces := by
  intro nC σ hσ
  have hlt : ∀ c : Fin nC, (c : ℕ) / σ < (nC + σ - 1) / σ := by
    intro c
    have hc := c.isLt
    have : (c : ℕ) / σ + 1 ≤ (nC + σ - 1) / σ := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      have := Nat.div_mul_le_self (c : ℕ) σ
      rw [add_mul, one_mul]; omega
    omega
  refine ⟨fun c => ⟨(c : ℕ) / σ, hlt c⟩, fun k => ?_⟩
  calc (univ.filter fun c : Fin nC => (⟨(c : ℕ) / σ, hlt c⟩ : Fin _) = k).card
      ≤ (range σ).card := by
        apply card_le_card_of_injOn (fun c : Fin nC => (c : ℕ) % σ)
        · intro c _; simp only [coe_range, Set.mem_Iio]; exact Nat.mod_lt _ (by omega)
        · intro c hc c' hc' he
          simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hc hc'
          have h1 : (c : ℕ) / σ = (c' : ℕ) / σ := by
            have := congrArg Fin.val (hc.trans hc'.symm); simpa using this
          have h2 : (c : ℕ) % σ = (c' : ℕ) % σ := he
          apply Fin.ext
          rw [← Nat.div_add_mod (c : ℕ) σ, ← Nat.div_add_mod (c' : ℕ) σ, h1, h2]
    _ = σ := card_range σ

/-! ## Greedy lists and candidate moduli -/

variable {ι : Type}

/-- A pool has a prime outside a list of fewer distinct elements. -/
lemma filter_not_mem_nonempty (Pl : Finset ℕ) (ps : List ℕ) (hnd : ps.Nodup)
    (hlt : ps.length < Pl.card) : (Pl.filter fun p => p ∉ ps).Nonempty := by
  by_contra hcon
  rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hcon
  have hsub : Pl ⊆ ps.toFinset := fun p hp => List.mem_toFinset.2 (by simpa using hcon hp)
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd] at this
  omega

/-- Step 2(b) can be carried out: a greedy list of `k ≤ |Π|` primes exists. -/
lemma exists_greedy (val : ι → Multiset ℤ) (S : Finset ι) (Pl : Finset ℕ) :
    ∀ k, k ≤ Pl.card → ∃ ps : List ℕ, ps.length = k ∧ IsGreedy val S Pl ps := by
  intro k
  induction k with
  | zero => intro _; exact ⟨[], rfl, List.nodup_nil, by simp, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨ps, hlen, hnd, hmem, hgr⟩ := ih (by omega)
    obtain ⟨p₀, hp₀, hmin⟩ := Finset.exists_min_image _ (fun p => Csum val S (ps.prod * p))
      (filter_not_mem_nonempty Pl ps hnd (by omega))
    have hp₀Pl := (mem_filter.1 hp₀).1
    have hp₀ps := (mem_filter.1 hp₀).2
    refine ⟨ps ++ [p₀], by simp [hlen], ?_, ?_, ?_⟩
    · rw [List.nodup_append_comm]; exact List.nodup_cons.2 ⟨hp₀ps, hnd⟩
    · intro p hp
      rcases List.mem_append.1 hp with h | h
      · exact hmem p h
      · rw [List.mem_singleton.1 h]; exact hp₀Pl
    · intro l hl p hp hpt
      simp only [List.length_append, List.length_singleton] at hl
      rcases Nat.lt_succ_iff_lt_or_eq.1 hl with hl' | hl'
      · have e1 : (ps ++ [p₀]).take l = ps.take l := List.take_append_of_le_length hl'.le
        rw [e1] at hpt ⊢
        rw [List.getElem_append_left hl']
        exact hgr l hl' p hp hpt
      · subst hl'
        have e1 : (ps ++ [p₀]).take ps.length = ps := by simp
        rw [e1] at hpt ⊢
        simp only [List.getElem_append_right (le_refl ps.length), Nat.sub_self,
          List.getElem_singleton]
        exact hmin p (mem_filter.2 ⟨hp, hpt⟩)

lemma mem_primesIn {P p : ℕ} (hp : p ∈ primesIn P) : p.Prime ∧ P ≤ p ∧ p < 2 * P := by
  simp only [primesIn, mem_filter, mem_Ico] at hp
  exact ⟨hp.2, hp.1.1, hp.1.2⟩

/-- "Every candidate modulus `mp` is a product of at most `r` distinct primes from `[P, 2P)`, so
`2 ≤ mp < (2P)^r`." -/
lemma cand_bound (P r : ℕ) (hP : 2 ≤ P) (ps : List ℕ) (hps : ∀ p ∈ ps, p ∈ primesIn P) (l : ℕ)
    (hl : l < r) (p : ℕ) (hp : p ∈ primesIn P) :
    2 ≤ (ps.take l).prod * p ∧ (((ps.take l).prod * p : ℕ) : ℝ) < (2 * P) ^ r := by
  have hmem : ∀ q ∈ ps.take l, q ∈ primesIn P := fun q hq => hps q (List.mem_of_mem_take hq)
  have h1 : 1 ≤ (ps.take l).prod :=
    one_le_prod_primes _ (fun q hq => (mem_primesIn (hmem q hq)).1)
  have h2 : (ps.take l).prod ≤ (2 * P) ^ l := by
    calc (ps.take l).prod ≤ (2 * P) ^ (ps.take l).length :=
          List.prod_le_pow_card _ _ (fun q hq => (mem_primesIn (hmem q hq)).2.2.le)
      _ ≤ (2 * P) ^ l :=
          Nat.pow_le_pow_right (by omega) (by rw [List.length_take]; exact min_le_left _ _)
  obtain ⟨-, hpP, hp2⟩ := mem_primesIn hp
  have hnat : (ps.take l).prod * p < (2 * P) ^ r := by
    calc (ps.take l).prod * p < (2 * P) ^ l * (2 * P) :=
          Nat.mul_lt_mul_of_le_of_lt h2 hp2 (by positivity)
      _ = (2 * P) ^ (l + 1) := (pow_succ _ _).symm
      _ ≤ (2 * P) ^ r := Nat.pow_le_pow_right (by omega) hl
  refine ⟨by nlinarith, ?_⟩
  have : (((ps.take l).prod * p : ℕ) : ℝ) < (((2 * P) ^ r : ℕ) : ℝ) := by exact_mod_cast hnat
  simpa using this

/-- Lemma 13.10 with the halving hypothesis only on the subsets of the starting set (the sets
that the algorithm meets). -/
lemma detect_iff_subset (val : ι → Multiset ℤ) (M : Finset ι → ℕ) (S₀ : Finset ι)
    (hM : ∀ S ⊆ S₀, (Fsum val S (M S) : ℝ) ≤ S.card / 2) :
    ∀ (k : ℕ) (S : Finset ι), S ⊆ S₀ → (detect val M k S = true ↔ ∃ x ∈ S, 0 < zcnt val x) := by
  intro k
  induction k with
  | zero => intro S _; simp [detect]
  | succ k ih =>
    intro S hS
    have hst := lemma_13_9_stage val S (M S) (hM S hS)
    have hkeep : (∃ x ∈ S, 0 < zcnt val x) ↔
        ∃ x ∈ S.filter (fun x => 0 < cnt val (M S) x), 0 < zcnt val x := by
      constructor
      · rintro ⟨x, hx, hz⟩
        refine ⟨x, mem_filter.2 ⟨hx, ?_⟩, hz⟩
        rw [cnt_eq]; omega
      · rintro ⟨x, hx, hz⟩; exact ⟨x, (mem_filter.1 hx).1, hz⟩
    simp only [detect]
    by_cases h0 : S.card = 0
    · rw [if_pos h0]
      rw [card_eq_zero] at h0
      simp [h0]
    · rw [if_neg h0]
      by_cases hC : (S.card : ℝ) / 2 < Csum val S (M S)
      · rw [if_pos hC]; simpa using hst.1 hC
      · rw [if_neg hC, ih _ ((filter_subset _ _).trans hS), ← hkeep]

/-! ## Theorem 13.2 -/

theorem theorem_13_2_correct : Theorem_13_2_correct := by
  intro hRS ν ε c₁ hν hε hε1 hc₁
  obtain ⟨n₀, hn₀⟩ := sec13_side_conditions ν ε c₁ hν hε hε1 hc₁
  refine ⟨⌈n₀⌉₊, fun n U r A hn hU hUn hr1 hrR hA hAn => ?_⟩
  have hn' : n₀ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  obtain ⟨hσ2, hcn, hP1024, hrP, hroot⟩ := hn₀ n U r hn' hU' hUn hr1 hrR
  dsimp only
  set Λ : ℝ := 2 * (10 * Real.log (2 * U)) ^ r with hΛ
  set σ := ⌊Real.sqrt ((n : ℝ) ^ ε / Λ)⌋₊ with hσ
  set P := ⌈4 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ))⌉₊ with hPdef
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast (by omega : 0 < σ)
  have hn0 : (0 : ℝ) < n := by
    by_contra hcon
    have : (n : ℝ) = 0 := le_antisymm (not_lt.1 hcon) (Nat.cast_nonneg n)
    rw [this, mul_zero, zero_div] at hcn; linarith
  have h135 := eq_13_5 n U ε c₁ r hn0 hU' hr1 (by linarith) hσ2 hcn hroot
  try dsimp only at h135
  set g := ⌈c₁ * n / σ⌉₊ with hg
  have hgc : c₁ * n / σ ≤ g := Nat.le_ceil _
  have hg0 : (0 : ℝ) < g := by linarith
  refine ⟨by exact_mod_cast hg0, fun grp R hgrp hcov => ?_⟩
  have hP2 : 2 ≤ P := by omega
  have hPr : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  have hlogP : 0 < Real.log P := Real.log_pos hPr
  have hcard := lemma_12_1 hRS P hP1024
  have hr_card : r ≤ (primesIn P).card := by
    have h1 : (P : ℝ) / (4 * Real.log P) ≤ P / (2 * Real.log P) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have : (r : ℝ) ≤ (primesIn P).card := le_trans hrP (le_trans h1 hcard)
    exact_mod_cast this
  have hPl : ∀ p ∈ primesIn P, p.Prime ∧ P ≤ p :=
    fun p hp => ⟨(mem_primesIn hp).1, (mem_primesIn hp).2.1⟩
  have hσ1 : 1 ≤ σ := by omega
  have hgσ : ∀ i, (grpSet A grp i).card ≤ σ := by
    intro i
    have hAn' : (A.card : ℝ) ≤ n := by exact_mod_cast hAn
    have h1 : ((grpSet A grp i).card : ℝ) ≤ c₁ * n / g :=
      le_trans (hgrp i) (div_le_div_of_nonneg_right (by nlinarith) hg0.le)
    have h2 : c₁ * n / g ≤ σ := by
      rw [div_le_iff₀ hg0]; rw [div_le_iff₀ hσ0] at hgc; nlinarith
    exact_mod_cast h1.trans h2
  have hhalf : ∀ M : Finset (ℕ × Fin g × Fin g) → ℕ,
      (∀ S, ∃ ps : List ℕ, ps.length = r ∧ IsGreedy (val3 A grp) S (primesIn P) ps ∧
        M S = ps.prod) →
      ∀ S ⊆ probes A grp R, (Fsum (val3 A grp) S (M S) : ℝ) ≤ S.card / 2 := by
    intro M hM S hS
    obtain ⟨ps, hlen, hgr, hMS⟩ := hM S
    rw [hMS]
    exact lemma_13_9_threeSum A grp U σ P r (primesIn P) S ps hU hA hσ1 hgσ
      (fun q hq => (mem_product.1 (mem_filter.1 (hS hq)).1).1) hP2 hPl hcard hrP
      (Nat.le_ceil _) hr1 hlen hgr
  refine ⟨hgσ, fun S => exists_greedy _ S _ r hr_card, fun ps hps l hl p hp =>
    ⟨(cand_bound P r hP2 ps hps l hl p hp).1, by exact_mod_cast (cand_bound P r hP2 ps hps l hl p hp).2,
      by push_cast; exact h135.2.2.2.2⟩, fun M hM => ⟨hhalf M hM, fun L => ?_⟩⟩
  rw [detect_iff_subset _ M (probes A grp R) (hhalf M hM) L _ subset_rfl]
  constructor
  · rintro ⟨q, hq, hz⟩
    obtain ⟨b, hb, c, hc, h⟩ := (zcnt_val3_pos_iff A grp q).1 hz
    have hqA : q.1 ∈ A := (mem_product.1 (mem_filter.1 hq).1).1
    exact ⟨q.1, hqA, b, (mem_filter.1 hb).1, c, (mem_filter.1 hc).1, h⟩
  · rintro ⟨a, ha, b, hb, c, hc, h⟩
    refine ⟨(a, grp b, grp c), ?_, ?_⟩
    · exact mem_filter.2 ⟨mem_product.2 ⟨ha, mem_univ _⟩, hcov a ha b hb c hc h⟩
    · exact (zcnt_val3_pos_iff A grp _).2
        ⟨b, mem_filter.2 ⟨hb, rfl⟩, c, mem_filter.2 ⟨hc, rfl⟩, h⟩

theorem theorem_13_2_FKP : Theorem_13_2_FKP := by
  intro hFKP hRS ν ε hν hε hε1
  obtain ⟨c₁, c₂, hc₁, -, hF⟩ := hFKP
  obtain ⟨n₀, hn₀⟩ := theorem_13_2_correct hRS ν ε c₁ hν hε hε1 (by exact_mod_cast hc₁)
  refine ⟨c₁, hc₁, n₀, fun n U r A hn hU hUn hr1 hrR hA hAn => ?_⟩
  have H := hn₀ n U r A hn hU hUn hr1 hrR hA hAn
  dsimp only at H ⊢
  have hg1 := H.1
  have h := H.2
  obtain ⟨grp, R, hsz, -, hcov⟩ := hF U A hA _ hg1
  obtain ⟨hgσ, hex, -, hcor⟩ := h grp R hsz hcov
  choose f hf using hex
  refine ⟨grp, R, hgσ, ⟨fun S => (f S).prod, fun S => ⟨f S, (hf S).1, (hf S).2, rfl⟩⟩,
    fun M hM L => (hcor M hM).2 L⟩

/-! ## Theorems 15.1 and 15.2 -/

theorem theorem_15_1_correct : Theorem_15_1_correct := by
  intro hRS ν ε hν hε hε1
  obtain ⟨n₀, hn₀⟩ := sec15_side_conditions ν ε 2 hν hε hε1 (by norm_num) (by norm_num)
  refine ⟨⌈n₀⌉₊, fun n U r nA nB nC h T piece hn hU hUn hr1 hrR hnC hab hbc hac => ?_⟩
  have hn' : n₀ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  obtain ⟨hσ2, hP1024, hrP, hroot, -, hσn⟩ := hn₀ n U r hn' hU' hUn hr1 hrR
  dsimp only
  have hσ' : (2 : ℝ) ≤ ⌊Real.sqrt ((n : ℝ) ^ ε / (2 * (10 * Real.log (3 * U)) ^ r))⌋₊ := by
    exact_mod_cast hσ2
  have h157 := eq_15_7 n U ε 2 nC r (by linarith) hU' hε (by norm_num) hr1 (Nat.cast_nonneg _)
    (by exact_mod_cast hnC) hσ2 hroot hσn
  try dsimp only at h157
  set ζ := Real.log (3 * U) with hζ
  set Λ : ℝ := 2 * (10 * ζ) ^ r with hΛ
  set σ := ⌊Real.sqrt ((n : ℝ) ^ ε / Λ)⌋₊ with hσ
  set P := ⌈4 * ζ * (2 * (σ : ℝ)) ^ (1 / (r : ℝ))⌉₊ with hPdef
  intro hpiece
  have hP2 : 2 ≤ P := by omega
  have hPr : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  have hlogP : 0 < Real.log P := Real.log_pos hPr
  have hcard := lemma_12_1 hRS P hP1024
  have hr_card : r ≤ (primesIn P).card := by
    have h1 : (P : ℝ) / (4 * Real.log P) ≤ P / (2 * Real.log P) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have : (r : ℝ) ≤ (primesIn P).card := le_trans hrP (le_trans h1 hcard)
    exact_mod_cast this
  have hPl : ∀ p ∈ primesIn P, p.Prime ∧ P ≤ p :=
    fun p hp => ⟨(mem_primesIn hp).1, (mem_primesIn hp).2.1⟩
  have hσ1 : 1 ≤ σ := by omega
  have hhalf : ∀ M : Finset (Fin nA × Fin nB × Fin h) → ℕ,
      (∀ S, ∃ ps : List ℕ, ps.length = r ∧ IsGreedy (valE T piece) S (primesIn P) ps ∧
        M S = ps.prod) →
      ∀ S, (Fsum (valE T piece) S (M S) : ℝ) ≤ S.card / 2 := by
    intro M hM S
    obtain ⟨ps, hlen, hgr, hMS⟩ := hM S
    rw [hMS]
    exact lemma_15_8 T piece U σ P r (primesIn P) S ps hU hab hbc hac hσ1 hpiece hP2 hPl hcard
      hrP hr1 (Nat.le_ceil _) hlen hgr
  refine ⟨fun S => exists_greedy _ S _ r hr_card, fun ps hps l hl p hp =>
    ⟨(cand_bound P r hP2 ps hps l hl p hp).1, by exact_mod_cast (cand_bound P r hP2 ps hps l hl p hp).2,
      by push_cast; exact h157.2.2.2.2.1⟩,
    fun M hM => ⟨hhalf M hM, fun L => lemma_15_9 T piece M (hhalf M hM) L⟩⟩

theorem theorem_15_2_correct : Theorem_15_2_correct := by
  intro hRS ν ε hν hε hε1
  obtain ⟨n₀, hn₀⟩ := sec15_side_conditions ν ε 4 hν hε hε1 (by norm_num) (by norm_num)
  refine ⟨⌈n₀⌉₊, fun n U r nA nB nC h T piece hn hU hUn hr1 hrR hnC hab hbc hac => ?_⟩
  have hn' : n₀ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  obtain ⟨hσ2, hP1024, hrP, hroot, -, hσn⟩ := hn₀ n U r hn' hU' hUn hr1 hrR
  dsimp only
  have hσ' : (2 : ℝ) ≤ ⌊Real.sqrt ((n : ℝ) ^ ε / (4 * (10 * Real.log (3 * U)) ^ r))⌋₊ := by
    exact_mod_cast hσ2
  have h157 := eq_15_7 n U ε 4 nC r (by linarith) hU' hε (by norm_num) hr1 (Nat.cast_nonneg _)
    (by exact_mod_cast hnC) hσ2 hroot hσn
  try dsimp only at h157
  set ζ := Real.log (3 * U) with hζ
  set Λ : ℝ := 4 * (10 * ζ) ^ r with hΛ
  set σ := ⌊Real.sqrt ((n : ℝ) ^ ε / Λ)⌋₊ with hσ
  set P := ⌈4 * ζ * (4 * (σ : ℝ)) ^ (1 / (r : ℝ))⌉₊ with hPdef
  intro hpiece
  have hP2 : 2 ≤ P := by omega
  have hPr : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  have hlogP : 0 < Real.log P := Real.log_pos hPr
  have hcard := lemma_12_1 hRS P hP1024
  have hr_card : r ≤ (primesIn P).card := by
    have h1 : (P : ℝ) / (4 * Real.log P) ≤ P / (2 * Real.log P) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have : (r : ℝ) ≤ (primesIn P).card := le_trans hrP (le_trans h1 hcard)
    exact_mod_cast this
  have hPl : ∀ p ∈ primesIn P, p.Prime ∧ P ≤ p :=
    fun p hp => ⟨(mem_primesIn hp).1, (mem_primesIn hp).2.1⟩
  have hσ1 : 1 ≤ σ := by omega
  refine ⟨fun S => exists_greedy _ S _ (r - 1) (by omega), fun ps hps l hl p hp =>
    ⟨(cand_bound P r hP2 ps hps l hl p hp).1, by exact_mod_cast (cand_bound P r hP2 ps hps l hl p hp).2,
      by push_cast; exact h157.2.2.2.2.1⟩, fun M Pool hMP => ?_⟩
  have hne : ∀ S, (Pool S).Nonempty := by
    intro S
    obtain ⟨ps, hlen, hgr, -, hPS⟩ := hMP S
    rw [hPS]; exact filter_not_mem_nonempty _ ps hgr.1 (by omega)
  refine ⟨hne, fun S => ?_, fun L a b => ?_⟩
  · obtain ⟨ps, hlen, hgr, hMS, hPS⟩ := hMP S
    rw [hMS, hPS]
    exact lemma_15_11_ET T piece U σ P r _ (primesIn P) S ps hU hab hbc hac hσ1 hpiece hP2 hPl
      hcard hrP hr1 rfl h157.2.2.2.2.2 (Nat.le_ceil _) hlen hgr
  · refine lemma_15_12 T piece U P _ M Pool hU hab hbc hac hP2 le_rfl (fun S => ?_) L a b
    obtain ⟨ps, hlen, hgr, hMS, hPS⟩ := hMP S
    have hpr : ∀ q ∈ ps, q.Prime := fun q hq => (mem_primesIn (hgr.2.1 q hq)).1
    refine ⟨hMS ▸ one_le_prod_primes ps hpr, hne S, fun p hp => ?_⟩
    rw [hPS] at hp
    obtain ⟨hpP, hpps⟩ := mem_filter.1 hp
    exact ⟨(mem_primesIn hpP).1, (mem_primesIn hpP).2.1,
      hMS ▸ not_dvd_prod_of_not_mem (mem_primesIn hpP).1 ps hpr hpps⟩

end ThinMatrixProducts

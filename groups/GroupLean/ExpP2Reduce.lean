import Mathlib

/-!
# Theorem 19.17 (exponent `p²`): the reduction to `ℤ_{p²}^d` and the parameters

The paper's Section 19.6 ("Groups of exponent p²"), paragraphs "Reduction to Z_{p^2}^d" and
"Parameters", and Case H "Rows and the hash" (the choice of `k'`).

* Reduction: for an injective additive homomorphism, a zero-sum triple exists in the lists iff
  one exists in their images (`exists_triple_iff_image`), and images keep their size. The
  homomorphism `embed : ∏ ZMod (m i) →+ (Fin r → ZMod N)` for `m i ∣ N`, `N ≠ 0`, is
  coordinatewise `y ↦ (N / m i) · val y` (`embed_val`); it is injective (`embed_injective`).
  For `N = p²`: `m i ∈ {p, p²}` when `2 ≤ m i` (`eq_p_or_eq_p_sq`), the map is `y ↦ p·y` for
  `m i = p` and keeps `val` for `m i = p²` (`embedP2_val_of_eq_p`, `embedP2_val_of_eq_p_sq`).
* Parameters: `exists_pow_between` and its uniqueness and `⌈log_p x⌉` form; `κ`, `k'`,
  `κ ≥ q`, `r₀`, `β₀`.
-/

namespace GroupLean.ExpP2Reduce

open Finset

/-! ## Injective homomorphisms preserve and reflect zero-sum triples -/

section General

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

theorem map_sum3_eq_zero_iff {f : G →+ H} (hf : Function.Injective f) (x₁ x₂ x₃ : G) :
    f x₁ + f x₂ + f x₃ = 0 ↔ x₁ + x₂ + x₃ = 0 := by
  rw [← map_add f, ← map_add f, ← map_zero f]
  exact hf.eq_iff

/-- An injective homomorphism preserves and reflects `x₁ + x₂ + x₃ = 0`: the lists have a
zero-sum triple iff their images do. -/
theorem exists_triple_iff_image [DecidableEq H] {f : G →+ H} (hf : Function.Injective f)
    (S₁ S₂ S₃ : Finset G) :
    (∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) ↔
      (∃ y₁ ∈ S₁.image f, ∃ y₂ ∈ S₂.image f, ∃ y₃ ∈ S₃.image f, y₁ + y₂ + y₃ = 0) := by
  constructor
  · rintro ⟨x₁, h₁, x₂, h₂, x₃, h₃, h⟩
    exact ⟨f x₁, mem_image.mpr ⟨x₁, h₁, rfl⟩, f x₂, mem_image.mpr ⟨x₂, h₂, rfl⟩, f x₃,
      mem_image.mpr ⟨x₃, h₃, rfl⟩, (map_sum3_eq_zero_iff hf x₁ x₂ x₃).mpr h⟩
  · rintro ⟨y₁, h₁, y₂, h₂, y₃, h₃, h⟩
    obtain ⟨x₁, hx₁, rfl⟩ := mem_image.mp h₁
    obtain ⟨x₂, hx₂, rfl⟩ := mem_image.mp h₂
    obtain ⟨x₃, hx₃, rfl⟩ := mem_image.mp h₃
    exact ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, (map_sum3_eq_zero_iff hf x₁ x₂ x₃).mp h⟩

theorem card_image_eq [DecidableEq H] {f : G →+ H} (hf : Function.Injective f) (S : Finset G) :
    (S.image f).card = S.card :=
  card_image_of_injective S hf

end General

/-! ## The coordinate map `ZMod m → ZMod N`, `y ↦ (N / m) · y` -/

section Coord

/-- For `m ∣ N`: the homomorphism `ZMod m →+ ZMod N`, `y ↦ (N / m) · y`. -/
def coordEmbed (m N : ℕ) (h : m ∣ N) : ZMod m →+ ZMod N :=
  ZMod.lift m ⟨(AddMonoidHom.mulLeft ((N / m : ℕ) : ZMod N)).comp (Int.castAddHom (ZMod N)), by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      Int.coe_castAddHom, Int.cast_natCast]
    rw [← Nat.cast_mul, Nat.div_mul_cancel h, ZMod.natCast_self]⟩

theorem coordEmbed_apply (m N : ℕ) [NeZero m] (h : m ∣ N) (y : ZMod m) :
    coordEmbed m N h y = (((N / m) * y.val : ℕ) : ZMod N) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val y, ← Int.cast_natCast]
  rw [coordEmbed, ZMod.lift_coe]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
    Int.coe_castAddHom, Int.cast_natCast, Nat.cast_mul]

theorem ne_zero_of_dvd {m N : ℕ} (hN : N ≠ 0) (h : m ∣ N) : m ≠ 0 := by
  rintro rfl
  exact hN (Nat.eq_zero_of_zero_dvd h)

theorem coordEmbed_injective (m N : ℕ) (hN : N ≠ 0) (h : m ∣ N) :
    Function.Injective (coordEmbed m N h) := by
  have hm : m ≠ 0 := ne_zero_of_dvd hN h
  have : NeZero m := ⟨hm⟩
  rw [injective_iff_map_eq_zero]
  intro y hy
  rw [coordEmbed_apply, ZMod.natCast_eq_zero_iff] at hy
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hN (by simpa using hc)
  have hdiv : N / m = c := by
    rw [hc, Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hm)]
  rw [hdiv, hc, mul_comm m c] at hy
  have hmy : m ∣ y.val := (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hc0)).mp hy
  exact (ZMod.val_eq_zero y).mp (Nat.eq_zero_of_dvd_of_lt hmy (ZMod.val_lt y))

/-- The value of `(N / m) · y` is `(N / m) * val y` (no wrap-around). -/
theorem coordEmbed_val (m N : ℕ) (hN : N ≠ 0) (h : m ∣ N) (y : ZMod m) :
    (coordEmbed m N h y).val = (N / m) * y.val := by
  have hm : m ≠ 0 := ne_zero_of_dvd hN h
  have : NeZero m := ⟨hm⟩
  rw [coordEmbed_apply, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hk : N / m * m = N := Nat.div_mul_cancel h
  have hpos : 0 < N / m :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) h) (Nat.pos_of_ne_zero hm)
  have hv : y.val < m := ZMod.val_lt y
  nlinarith

end Coord

/-! ## The embedding of `∏ ZMod (m i)` into `(ZMod N)^r` -/

section Embed

variable {r : ℕ} {m : Fin r → ℕ}

/-- Coordinatewise `y ↦ (N / m i) · y`. -/
def embed (N : ℕ) (h : ∀ i, m i ∣ N) : ((i : Fin r) → ZMod (m i)) →+ (Fin r → ZMod N) where
  toFun y i := coordEmbed (m i) N (h i) (y i)
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp

theorem embed_apply (N : ℕ) (h : ∀ i, m i ∣ N) (y : (i : Fin r) → ZMod (m i)) (i : Fin r) :
    embed N h y i = coordEmbed (m i) N (h i) (y i) := rfl

theorem embed_injective (N : ℕ) (hN : N ≠ 0) (h : ∀ i, m i ∣ N) :
    Function.Injective (embed N h) := by
  intro x y hxy
  funext i
  exact coordEmbed_injective (m i) N hN (h i) (congrFun hxy i)

theorem embed_val (N : ℕ) (hN : N ≠ 0) (h : ∀ i, m i ∣ N) (y : (i : Fin r) → ZMod (m i))
    (i : Fin r) :
    (embed N h y i).val = (N / m i) * (y i).val :=
  coordEmbed_val (m i) N hN (h i) (y i)

/-! ### `N = p²` -/

/-- A divisor `m ≥ 2` of `p²` is `p` or `p²`. -/
theorem eq_p_or_eq_p_sq {p m : ℕ} (hp : p.Prime) (hdvd : m ∣ p ^ 2) (h2 : 2 ≤ m) :
    m = p ∨ m = p ^ 2 := by
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases k
  · simp at h2
  · left; simp
  · right; rfl

theorem p_sq_ne_zero {p : ℕ} (hp : p.Prime) : p ^ 2 ≠ 0 := pow_ne_zero 2 hp.ne_zero

theorem embedP2_injective {p : ℕ} (hp : p.Prime) (h : ∀ i, m i ∣ p ^ 2) :
    Function.Injective (embed (p ^ 2) h) :=
  embed_injective (p ^ 2) (p_sq_ne_zero hp) h

/-- A coordinate with `m i = p` is mapped by `y ↦ p · y`. -/
theorem embedP2_val_of_eq_p {p : ℕ} (hp : p.Prime) (h : ∀ i, m i ∣ p ^ 2)
    (y : (i : Fin r) → ZMod (m i)) (i : Fin r) (hi : m i = p) :
    (embed (p ^ 2) h y i).val = p * (y i).val := by
  have hq : p ^ 2 / m i = p := by
    rw [hi, pow_two, Nat.mul_div_cancel p hp.pos]
  rw [embed_val (p ^ 2) (p_sq_ne_zero hp) h y i, hq]

/-- A coordinate with `m i = p²` is mapped identically (the value is kept). -/
theorem embedP2_val_of_eq_p_sq {p : ℕ} (hp : p.Prime) (h : ∀ i, m i ∣ p ^ 2)
    (y : (i : Fin r) → ZMod (m i)) (i : Fin r) (hi : m i = p ^ 2) :
    (embed (p ^ 2) h y i).val = (y i).val := by
  have hq : p ^ 2 / m i = 1 := by
    rw [hi, Nat.div_self (Nat.pos_of_ne_zero (p_sq_ne_zero hp))]
  rw [embed_val (p ^ 2) (p_sq_ne_zero hp) h y i, hq, one_mul]

/-- **Reduction to `ℤ_{p²}^r`.** The lists have a zero-sum triple iff their images under the
injective homomorphism `embed (p²)` do. -/
theorem exists_triple_iff_embedP2 {p : ℕ} (hp : p.Prime) (h : ∀ i, m i ∣ p ^ 2)
    (S₁ S₂ S₃ : Finset ((i : Fin r) → ZMod (m i))) :
    (∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) ↔
      (∃ y₁ ∈ S₁.image (embed (p ^ 2) h), ∃ y₂ ∈ S₂.image (embed (p ^ 2) h),
        ∃ y₃ ∈ S₃.image (embed (p ^ 2) h), y₁ + y₂ + y₃ = 0) :=
  exists_triple_iff_image (embedP2_injective hp h) S₁ S₂ S₃

theorem card_image_embedP2 {p : ℕ} (hp : p.Prime) (h : ∀ i, m i ∣ p ^ 2)
    (S : Finset ((i : Fin r) → ZMod (m i))) :
    (S.image (embed (p ^ 2) h)).card = S.card :=
  card_image_of_injective S (embedP2_injective hp h)

end Embed

/-! ## Parameters -/

section Params

/-- For `p ≥ 2` and `1 < p x` there is `k : ℕ` with `x ≤ p^k < p x` (the least `k` with
`x ≤ p^k`). -/
theorem exists_pow_between {p : ℕ} (hp : 2 ≤ p) {x : ℝ} (hx : 1 < p * x) :
    ∃ k : ℕ, x ≤ (p : ℝ) ^ k ∧ (p : ℝ) ^ k < p * x := by
  classical
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < p := by linarith
  have hex : ∃ k : ℕ, x ≤ (p : ℝ) ^ k := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x hp1
    exact ⟨n, hn.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · rw [h0, pow_zero]
    exact hx
  · obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : ¬ x ≤ (p : ℝ) ^ k := Nat.find_min hex (by omega)
    rw [not_le] at hlt
    rw [hk, pow_succ, mul_comm]
    exact mul_lt_mul_of_pos_left hlt hp0

/-- The `k` of `exists_pow_between` is unique. -/
theorem pow_between_unique {p : ℕ} (hp : 2 ≤ p) {x : ℝ} {j k : ℕ}
    (hj : x ≤ (p : ℝ) ^ j ∧ (p : ℝ) ^ j < p * x) (hk : x ≤ (p : ℝ) ^ k ∧ (p : ℝ) ^ k < p * x) :
    j = k := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < p := by linarith
  have h1 : (p : ℝ) ^ j < (p : ℝ) ^ (k + 1) := by
    rw [pow_succ, mul_comm]
    exact lt_of_lt_of_le hj.2 (mul_le_mul_of_nonneg_left hk.1 hp0.le)
  have h2 : (p : ℝ) ^ k < (p : ℝ) ^ (j + 1) := by
    rw [pow_succ, mul_comm]
    exact lt_of_lt_of_le hk.2 (mul_le_mul_of_nonneg_left hj.1 hp0.le)
  rw [pow_lt_pow_iff_right₀ hp1] at h1 h2
  omega

/-- The `k` with `x ≤ p^k < p x` is `⌈log_p x⌉`. -/
theorem ceil_logb_eq {p : ℕ} (hp : 2 ≤ p) {x : ℝ} {k : ℕ}
    (hk : x ≤ (p : ℝ) ^ k ∧ (p : ℝ) ^ k < p * x) : ⌈Real.logb p x⌉ = k := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < p := by linarith
  have hx0 : 0 < x := by
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith [pow_pos hp0 k, hk.2]
  rw [Int.ceil_eq_iff]
  push_cast
  constructor
  · rw [Real.lt_logb_iff_rpow_lt hp1 hx0, Real.rpow_sub_one hp0.ne', Real.rpow_natCast,
      div_lt_iff₀ hp0, mul_comm]
    exact hk.2
  · rw [Real.logb_le_iff_le_rpow hp1 hx0, Real.rpow_natCast]
    exact hk.1

/-- The paper's form: `⌈log_p x⌉` is a natural number `k` (in particular `≥ 0`) with
`x ≤ p^k < p x`, whenever `1 < p x`. -/
theorem ceil_logb_spec {p : ℕ} (hp : 2 ≤ p) {x : ℝ} (hx : 1 < p * x) :
    ∃ k : ℕ, ⌈Real.logb p x⌉ = k ∧ x ≤ (p : ℝ) ^ k ∧ (p : ℝ) ^ k < p * x := by
  obtain ⟨k, hk⟩ := exists_pow_between hp hx
  exact ⟨k, ceil_logb_eq hp hk, hk⟩

/-- (a) `κ := ⌈log_p(n/σ)⌉` is a natural number with `n/σ ≤ p^κ < p n/σ`, for `1 ≤ σ ≤ n`. -/
theorem exists_kappa {p : ℕ} (hp : 2 ≤ p) {n σ : ℕ} (hσ : 1 ≤ σ) (hσn : σ ≤ n) :
    ∃ κ : ℕ, ⌈Real.logb p ((n : ℝ) / σ)⌉ = κ ∧
      (n : ℝ) / σ ≤ (p : ℝ) ^ κ ∧ (p : ℝ) ^ κ < p * n / σ := by
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast hσ
  have h1 : (1 : ℝ) ≤ n / σ := by
    rw [le_div_iff₀ hσ0, one_mul]
    exact_mod_cast hσn
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  obtain ⟨k, hk0, hk1, hk2⟩ := ceil_logb_spec hp (x := (n : ℝ) / σ) (by nlinarith)
  exact ⟨k, hk0, hk1, by rwa [mul_div_assoc]⟩

/-- (b) For `σ ≥ 1` and `s > σ/2` (i.e. `σ < 2 s`), `k' := ⌈log_p(s/σ)⌉` is a natural number
(so `k' ≥ 0`) with `s/σ ≤ p^{k'} < p s/σ`. -/
theorem exists_kprime {p : ℕ} (hp : 2 ≤ p) {s σ : ℕ} (hσ : 1 ≤ σ) (hs : σ < 2 * s) :
    ∃ k' : ℕ, ⌈Real.logb p ((s : ℝ) / σ)⌉ = k' ∧
      (s : ℝ) / σ ≤ (p : ℝ) ^ k' ∧ (p : ℝ) ^ k' < p * s / σ := by
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast hσ
  have h : (1 : ℝ) < p * ((s : ℝ) / σ) := by
    rw [← mul_div_assoc, lt_div_iff₀ hσ0, one_mul]
    have h1 : (σ : ℝ) < 2 * s := by exact_mod_cast hs
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have h3 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    nlinarith
  obtain ⟨k, hk0, hk1, hk2⟩ := ceil_logb_spec hp h
  exact ⟨k, hk0, hk1, by rwa [mul_div_assoc]⟩

/-- If `p^k < p s/σ` with `σ ≥ 1` and `s ≤ n`, then `k ≤ ⌈log_p n⌉` (`Nat.clog p n`).
Applies to `κ` (`s = n`) and to `k'` (`s = s_min ≤ n`). -/
theorem le_clog_of_pow_lt {p : ℕ} (hp : 2 ≤ p) {n s σ k : ℕ} (hσ : 1 ≤ σ) (hsn : s ≤ n)
    (hk : (p : ℝ) ^ k < p * s / σ) : k ≤ Nat.clog p n := by
  have hσ0 : (0 : ℝ) < σ := by exact_mod_cast hσ
  have h1 : (p : ℝ) * s / σ ≤ p * n := by
    rw [div_le_iff₀ hσ0]
    have hσ1 : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
    have hs' : (s : ℝ) ≤ n := by exact_mod_cast hsn
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    calc (p : ℝ) * s ≤ p * n := mul_le_mul_of_nonneg_left hs' hp0
      _ = p * n * 1 := (mul_one _).symm
      _ ≤ p * n * σ := mul_le_mul_of_nonneg_left hσ1 (by positivity)
  have h2 : p ^ k < p * n := by exact_mod_cast (lt_of_lt_of_le hk h1)
  have h3 : n ≤ p ^ Nat.clog p n := Nat.le_pow_clog (by omega) n
  have h4 : p ^ k < p ^ (Nat.clog p n + 1) := by
    rw [pow_succ]
    calc p ^ k < p * n := h2
      _ ≤ p * p ^ Nat.clog p n := Nat.mul_le_mul le_rfl h3
      _ = p ^ Nat.clog p n * p := mul_comm _ _
  have := (pow_lt_pow_iff_right₀ (by omega : 1 < p)).mp h4
  omega

/-- (c) `κ ≥ q`: if `D = p^q ≤ n^ε`, `σ² ≤ D`, `ε ≤ 1/4`, `n, σ ≥ 1` and `n/σ ≤ p^κ`, then
`q ≤ κ` (paper: `n/σ ≥ n^{1-ε/2} ≥ n^ε ≥ D`; here via `σ D ≤ n`). -/
theorem q_le_kappa {p : ℕ} (hp : 2 ≤ p) {n σ q κ : ℕ} {ε : ℝ} (hε : ε ≤ 1 / 4) (hn : 1 ≤ n)
    (hσ : 1 ≤ σ) (hD : (p : ℝ) ^ q ≤ (n : ℝ) ^ ε) (hσD : (σ : ℝ) ^ 2 ≤ (p : ℝ) ^ q)
    (hκ : (n : ℝ) / σ ≤ (p : ℝ) ^ κ) : q ≤ κ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hσ1 : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  have hσ0 : (0 : ℝ) < σ := by linarith
  set a : ℝ := (n : ℝ) ^ ε with ha_def
  set D : ℝ := (p : ℝ) ^ q with hD_def
  have hσa : (σ : ℝ) ^ 2 ≤ a := hσD.trans hD
  have ha1 : 1 ≤ a := by nlinarith
  have ha0 : 0 ≤ a := by linarith
  have hD0 : 0 ≤ D := by positivity
  have ha4 : a ^ 4 ≤ n := by
    have he : a ^ (4 : ℕ) = (n : ℝ) ^ (ε * 4) := by
      rw [ha_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [he]
    calc (n : ℝ) ^ (ε * 4) ≤ (n : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = n := Real.rpow_one _
  have hsq : ((σ : ℝ) * D) ^ 2 ≤ a ^ 4 := by
    have hD2 : D ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hD0 hD 2
    calc ((σ : ℝ) * D) ^ 2 = (σ : ℝ) ^ 2 * D ^ 2 := by ring
      _ ≤ a * a ^ 2 := mul_le_mul hσa hD2 (by positivity) ha0
      _ ≤ a ^ 4 := by nlinarith [mul_le_mul_of_nonneg_left ha1 (pow_nonneg ha0 3)]
  have hσDn : (σ : ℝ) * D ≤ n := by
    by_contra hcon
    rw [not_le] at hcon
    nlinarith [mul_self_lt_mul_self (by positivity : (0 : ℝ) ≤ n) hcon]
  have hDκ : D ≤ (p : ℝ) ^ κ := by
    refine le_trans ?_ hκ
    rw [le_div_iff₀ hσ0, mul_comm]
    exact hσDn
  exact (pow_le_pow_iff_right₀ hp1).mp hDκ

/-- `r₀ := ⌈log_p n⌉ + q + 1`. -/
def r0 (p n q : ℕ) : ℕ := Nat.clog p n + q + 1

/-- `β₀ := 1 / (2 r₀)`. -/
noncomputable def beta0 (p n q : ℕ) : ℝ := 1 / (2 * (r0 p n q : ℝ))

theorem r0_pos (p n q : ℕ) : (0 : ℝ) < r0 p n q :=
  Nat.cast_pos.mpr (by unfold r0; omega)

theorem beta0_nonneg (p n q : ℕ) : 0 ≤ beta0 p n q := by
  have := r0_pos p n q
  unfold beta0
  positivity

/-- `β₀ ℓ ≤ 1/2` for every length `ℓ ≤ r₀`. -/
theorem beta0_mul_le {p n q ℓ : ℕ} (h : ℓ ≤ r0 p n q) : beta0 p n q * ℓ ≤ 1 / 2 := by
  have hr := r0_pos p n q
  have hℓ : (ℓ : ℝ) ≤ r0 p n q := by exact_mod_cast h
  unfold beta0
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

/-- `β₀ ≤ 1/ℓ` for every `1 ≤ ℓ ≤ r₀`. -/
theorem beta0_le_inv {p n q ℓ : ℕ} (h1 : 1 ≤ ℓ) (h : ℓ ≤ r0 p n q) :
    beta0 p n q ≤ 1 / (ℓ : ℝ) := by
  have hℓ : (0 : ℝ) < ℓ := by exact_mod_cast h1
  rw [le_div_iff₀ hℓ]
  linarith [beta0_mul_le h]

/-- `2 q β₀ ≤ 1`. -/
theorem two_q_beta0_le_one (p n q : ℕ) : 2 * (q : ℝ) * beta0 p n q ≤ 1 := by
  have h : q ≤ r0 p n q := by unfold r0; omega
  have := beta0_mul_le h
  linarith

/-- `(1 + β₀)^ℓ ≤ e^{β₀ ℓ}`. -/
theorem one_add_beta0_pow_le_exp (p n q ℓ : ℕ) :
    (1 + beta0 p n q) ^ ℓ ≤ Real.exp (beta0 p n q * ℓ) := by
  have hb := beta0_nonneg p n q
  calc (1 + beta0 p n q) ^ ℓ ≤ (Real.exp (beta0 p n q)) ^ ℓ :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (beta0 p n q)]) ℓ
    _ = Real.exp (ℓ * beta0 p n q) := (Real.exp_nat_mul _ ℓ).symm
    _ = Real.exp (beta0 p n q * ℓ) := by rw [mul_comm]

/-- Every sequence of at most `r₀` rows: `(1 + β₀)^ℓ ≤ e^{1/2}`. -/
theorem one_add_beta0_pow_le_sqrt_e {p n q ℓ : ℕ} (h : ℓ ≤ r0 p n q) :
    (1 + beta0 p n q) ^ ℓ ≤ Real.exp (1 / 2) :=
  (one_add_beta0_pow_le_exp p n q ℓ).trans (Real.exp_le_exp.mpr (beta0_mul_le h))

/-- Case L: `(1 + β₀)^{2q} ≤ e^{q/r₀} ≤ e`. -/
theorem one_add_beta0_pow_two_q_le_e (p n q : ℕ) :
    (1 + beta0 p n q) ^ (2 * q) ≤ Real.exp 1 := by
  refine (one_add_beta0_pow_le_exp p n q (2 * q)).trans (Real.exp_le_exp.mpr ?_)
  have := two_q_beta0_le_one p n q
  push_cast
  linarith

/-- (d) for `κ`: if `p^κ < p n/σ`, `σ ≥ 1`, then `κ ≤ ⌈log_p n⌉ ≤ r₀`, and, when `κ ≥ 1`,
`β₀ ≤ 1/κ`. -/
theorem kappa_le_r0 {p : ℕ} (hp : 2 ≤ p) {n σ q κ : ℕ} (hσ : 1 ≤ σ)
    (hκ : (p : ℝ) ^ κ < p * n / σ) : κ ≤ Nat.clog p n ∧ κ ≤ r0 p n q := by
  have := le_clog_of_pow_lt hp hσ le_rfl hκ
  exact ⟨this, by unfold r0; omega⟩

theorem beta0_le_inv_kappa {p : ℕ} (hp : 2 ≤ p) {n σ q κ : ℕ} (hσ : 1 ≤ σ)
    (hκ : (p : ℝ) ^ κ < p * n / σ) (hκ1 : 1 ≤ κ) : beta0 p n q ≤ 1 / (κ : ℝ) :=
  beta0_le_inv hκ1 (kappa_le_r0 (q := q) hp hσ hκ).2

/-- (d) for `k'`: if `p^{k'} < p s/σ`, `σ ≥ 1`, `s ≤ n`, then `k' + q ≤ r₀`, and, when `q ≥ 1`,
`β₀ ≤ 1/(k' + q)`. -/
theorem kprime_add_q_le_r0 {p : ℕ} (hp : 2 ≤ p) {n s σ q k' : ℕ} (hσ : 1 ≤ σ) (hsn : s ≤ n)
    (hk : (p : ℝ) ^ k' < p * s / σ) : k' + q ≤ r0 p n q := by
  have := le_clog_of_pow_lt hp hσ hsn hk
  unfold r0
  omega

theorem beta0_le_inv_kprime_add_q {p : ℕ} (hp : 2 ≤ p) {n s σ q k' : ℕ} (hσ : 1 ≤ σ)
    (hsn : s ≤ n) (hk : (p : ℝ) ^ k' < p * s / σ) (hq : 1 ≤ q) :
    beta0 p n q ≤ 1 / ((k' + q : ℕ) : ℝ) :=
  beta0_le_inv (by omega) (kprime_add_q_le_r0 hp hσ hsn hk)

end Params

end GroupLean.ExpP2Reduce

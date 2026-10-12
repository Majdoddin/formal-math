import Mathlib

/-!
# Improved 3XOR: parameter blocks, cost inequalities and exponents

The arithmetic of the improved write-up, as pure inequalities (no running time is formalized):
the parameter block of Theorem I (§3.1), the parameters and the call of Theorem I′ (§3.2),
the parameters of §4.2 and the inequalities of Lemma II.3 and §4.7 (Theorem II), the
parameters of §5 and the inequality of Lemma III.1 (Theorem III), the exponents of §1, and the
absorption of the polylogarithmic factors into the rounded exponents (as `IsBigO`).
-/

namespace Xor.Improved
open Real

/-! ### General helpers -/

/-- `k := ⌈log₂ x⌉` has `x ≤ 2^k < 2x` for `x ≥ 1`. -/
theorem ceil_logb_spec (x : ℝ) (hx : 1 ≤ x) :
    x ≤ (2 : ℝ) ^ ⌈logb 2 x⌉₊ ∧ (2 : ℝ) ^ ⌈logb 2 x⌉₊ < 2 * x := by
  have hl : 0 ≤ logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hx0 : 0 < x := by linarith
  set k := ⌈logb 2 x⌉₊ with hk
  have h1 : logb 2 x ≤ k := Nat.le_ceil _
  have h2 : (k : ℝ) < logb 2 x + 1 := Nat.ceil_lt_add_one hl
  have e1 : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast 2 k).symm
  constructor
  · rw [e1]
    exact (Real.logb_le_iff_le_rpow (by norm_num) hx0).1 h1
  · rw [e1]
    calc (2 : ℝ) ^ (k : ℝ) < (2 : ℝ) ^ (logb 2 x + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h2
      _ = 2 * x := by
          rw [Real.rpow_add (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx0,
            Real.rpow_one]; ring

/-- `2^{⌈l/2⌉} ≥ √(2^l)` and `(2^{⌈l/2⌉})² ≤ 2·2^l` (the side `N = g' 2^{⌈l/2⌉}`). -/
theorem two_pow_half (l : ℕ) :
    Real.sqrt ((2 : ℝ) ^ l) ≤ (2 : ℝ) ^ ((l + 1) / 2) ∧
    ((2 : ℝ) ^ ((l + 1) / 2)) ^ 2 ≤ 2 * 2 ^ l := by
  set m := (l + 1) / 2
  have hm1 : l ≤ 2 * m := by omega
  have hm2 : 2 * m ≤ l + 1 := by omega
  have hsq : ((2 : ℝ) ^ m) ^ 2 = 2 ^ (2 * m) := by rw [← pow_mul, mul_comm]
  constructor
  · rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [hsq]
    exact pow_le_pow_right₀ (by norm_num) hm1
  · rw [hsq]
    calc (2 : ℝ) ^ (2 * m) ≤ 2 ^ (l + 1) := pow_le_pow_right₀ (by norm_num) hm2
      _ = 2 * 2 ^ l := by rw [pow_succ]; ring

/-- Cutting classes of sizes `c a` into chunks of `P`: `Σ ⌈c a / P⌉ ≤ #classes + (Σ c)/P`. -/
theorem sum_ceil_div_le {α : Type*} (s : Finset α) (c : α → ℕ) (P : ℕ) (hP : 0 < P) :
    ((∑ a ∈ s, (c a + P - 1) / P : ℕ) : ℝ) ≤ s.card + (∑ a ∈ s, (c a : ℝ)) / P := by
  have hPR : (0 : ℝ) < P := by exact_mod_cast hP
  have hterm : ∀ a, (((c a + P - 1) / P : ℕ) : ℝ) ≤ c a / P + 1 := by
    intro a
    refine Nat.cast_div_le.trans ?_
    have : ((c a + P - 1 : ℕ) : ℝ) ≤ c a + P := by
      have : c a + P - 1 ≤ c a + P := by omega
      exact_mod_cast this
    calc ((c a + P - 1 : ℕ) : ℝ) / P ≤ (c a + P) / P := div_le_div_of_nonneg_right this hPR.le
      _ = c a / P + 1 := by rw [add_div, div_self hPR.ne']
  push_cast
  calc ∑ a ∈ s, (((c a + P - 1) / P : ℕ) : ℝ) ≤ ∑ a ∈ s, ((c a : ℝ) / P + 1) :=
        Finset.sum_le_sum fun a _ => hterm a
    _ = s.card + (∑ a ∈ s, (c a : ℝ)) / P := by
        rw [Finset.sum_add_distrib, Finset.sum_div]; simp; ring

/-- A chunk size `⌊M⌋ ≥ M/2` for `M ≥ 1`. -/
theorem floor_ge_half (M : ℝ) (hM : 1 ≤ M) : M / 2 ≤ (⌊M⌋₊ : ℝ) := by
  have h1 : M < ⌊M⌋₊ + 1 := Nat.lt_floor_add_one M
  have h2 : (1 : ℝ) ≤ ⌊M⌋₊ := by exact_mod_cast Nat.le_floor (by exact_mod_cast hM)
  rcases le_total M 2 with h | h <;> linarith

/-- `(1 + 1/q)^{q-1} ≤ e` (Lemma III.3) and `(1+1/q)^q ≤ e` (§4.8). -/
theorem one_add_inv_pow_pred_le (q : ℕ) (hq : 0 < q) :
    (1 + 1 / (q : ℝ)) ^ (q - 1) ≤ exp 1 ∧ (1 + 1 / (q : ℝ)) ^ q ≤ exp 1 := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have h1 : 1 + 1 / (q : ℝ) ≤ exp (1 / q) := by
    have := Real.add_one_le_exp (1 / (q : ℝ)); linarith
  have h0 : 0 ≤ 1 + 1 / (q : ℝ) := by positivity
  have hfull : (1 + 1 / (q : ℝ)) ^ q ≤ exp 1 := by
    calc (1 + 1 / (q : ℝ)) ^ q ≤ exp (1 / q) ^ q := pow_le_pow_left₀ h0 h1 q
      _ = exp (q * (1 / q)) := (Real.exp_nat_mul _ _).symm
      _ = exp 1 := by rw [mul_one_div_cancel hq']
  refine ⟨le_trans (pow_le_pow_right₀ ?_ (Nat.sub_le q 1)) hfull, hfull⟩
  have : 0 ≤ 1 / (q : ℝ) := by positivity
  linarith

/-- The probe constant of Lemma II.1 (ii): `4 + e + 1/σ ≤ 8` for `σ ≥ 1`. -/
theorem probe_const_le (σ : ℝ) (hσ : 1 ≤ σ) : 4 + exp 1 + 1 / σ ≤ 8 := by
  have he := Real.exp_one_lt_d9
  have : 1 / σ ≤ 1 := by rw [div_le_one (by linarith)]; exact hσ
  linarith

/-- A polylogarithmic factor is absorbed by any increase of the exponent:
`x^a (log x)^c = O(x^b)` for `a < b`. -/
theorem isBigO_rpow_mul_log (a b c : ℝ) (hab : a < b) :
    (fun x : ℝ => x ^ a * Real.log x ^ c) =O[Filter.atTop] fun x => x ^ b := by
  have h1 := (isLittleO_log_rpow_rpow_atTop c (sub_pos.2 hab)).isBigO
  have h2 := (Asymptotics.isBigO_refl (fun x : ℝ => x ^ a) Filter.atTop).mul h1
  refine h2.congr' (Filter.Eventually.of_forall fun _ => rfl) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with x hx
  rw [← Real.rpow_add hx]; ring_nf

/-- `y ↦ y^{-z}` is antitone on positive reals for `z ≥ 0`. -/
private theorem rpow_neg_anti {x y z : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    y ^ (-z) ≤ x ^ (-z) := by
  rw [Real.rpow_neg (hx.le.trans hxy), Real.rpow_neg hx.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hx z) (Real.rpow_le_rpow hx.le hxy hz)

/-- `y/2 ≤ D` gives `D^{-z} ≤ 2^z y^{-z}`. -/
private theorem half_rpow_neg (y D z : ℝ) (hy : 0 < y) (hD : y / 2 ≤ D) (hz : 0 ≤ z) :
    D ^ (-z) ≤ 2 ^ z * y ^ (-z) := by
  have h1 := rpow_neg_anti (by positivity : 0 < y / 2) hD hz
  have h2 : (y / 2) ^ (-z) = 2 ^ z * y ^ (-z) := by
    rw [Real.div_rpow hy.le (by norm_num), Real.rpow_neg hy.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
  linarith

private theorem le_of_log_le' {u v : ℝ} (hu : 0 < u) (hv : 0 < v)
    (h : Real.log u ≤ Real.log v) : u ≤ v :=
  (Real.log_le_log_iff hu hv).1 h

/-! ### Theorem I (§3.1): the parameter block of part (a) -/

/-- **Theorem I (a), parameters**: `D := ⌊N^ε⌋`, `g := ⌈D^{γ/2}⌉`. For `N ≥ 16^{1/ε}`:
`16 ≤ D ≤ N^ε ≤ N`, `1 ≤ g ≤ 2D^{γ/2} ≤ √D` (so the note's Theorem 8 applies), the instances
cost `4Ng · N²/D^γ ≤ 8N³D^{-γ/2}`, writing them `N²Dg ≤ 2N^{2+ε(1+γ/2)}`, and
`D^{-γ/2} ≤ 2^{γ/2} N^{-εγ/2}`. -/
theorem partI_params (ε γ : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (N : ℕ) (hN : (16 : ℝ) ^ (1 / ε) ≤ N) :
    let D := ⌊(N : ℝ) ^ ε⌋₊
    let g := ⌈(D : ℝ) ^ (γ / 2)⌉₊
    16 ≤ D ∧ D ≤ N ∧ (D : ℝ) ≤ (N : ℝ) ^ ε ∧ 1 ≤ g ∧ (g : ℝ) ≤ 2 * (D : ℝ) ^ (γ / 2) ∧
    (g : ℝ) ≤ Real.sqrt D ∧ (N : ℝ) ^ ε / 2 ≤ D ∧
    4 * N * g * ((N : ℝ) ^ 2 / (D : ℝ) ^ γ) ≤ 8 * (N : ℝ) ^ 3 * (D : ℝ) ^ (-(γ / 2)) ∧
    (N : ℝ) ^ 2 * D * g ≤ 2 * (N : ℝ) ^ (2 + ε * (1 + γ / 2)) ∧
    (D : ℝ) ^ (-(γ / 2)) ≤ 2 ^ (γ / 2) * (N : ℝ) ^ (-(ε * γ / 2)) := by
  dsimp only
  have hN16 : (16 : ℝ) ≤ (N : ℝ) ^ ε := by
    have : ((16 : ℝ) ^ (1 / ε)) ^ ε ≤ (N : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) hN hε.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one] at this
  have hN1 : (1 : ℝ) ≤ N := by
    by_contra h
    push Not at h
    have : (N : ℝ) ^ ε ≤ 1 := Real.rpow_le_one (Nat.cast_nonneg _) h.le hε.le
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hNε_le : (N : ℝ) ^ ε ≤ N := by
    calc (N : ℝ) ^ ε ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one _
  set D := ⌊(N : ℝ) ^ ε⌋₊ with hDdef
  have hD16 : 16 ≤ D := Nat.le_floor (by exact_mod_cast hN16)
  have hDle : (D : ℝ) ≤ (N : ℝ) ^ ε := Nat.floor_le (by positivity)
  have hDN : D ≤ N := by exact_mod_cast hDle.trans hNε_le
  have hDR : (16 : ℝ) ≤ D := by exact_mod_cast hD16
  have hD0 : (0 : ℝ) < D := by linarith
  set x := (D : ℝ) ^ (γ / 2) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow (by linarith) (by positivity)
  have hxpos : 0 < x := by linarith
  have hg1 : 1 ≤ ⌈x⌉₊ := Nat.ceil_pos.2 hxpos
  have hg2 : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ x); linarith
  have hx4 : x ≤ (D : ℝ) ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have h4 : (2 : ℝ) ≤ (D : ℝ) ^ ((1 : ℝ) / 4) := by
    have h0 : (16 : ℝ) ^ ((1 : ℝ) / 4) ≤ (D : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by norm_num) hDR (by norm_num)
    have h16 : (16 : ℝ) ^ ((1 : ℝ) / 4) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    linarith
  have hsq : Real.sqrt D = (D : ℝ) ^ ((1 : ℝ) / 4) * (D : ℝ) ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hD0, Real.sqrt_eq_rpow]; norm_num
  have hgsqrt : (⌈x⌉₊ : ℝ) ≤ Real.sqrt D := by
    rw [hsq]; nlinarith
  have hhalf : (N : ℝ) ^ ε / 2 ≤ D := floor_ge_half _ (by linarith)
  have hDγ : (D : ℝ) ^ γ = x * x := by
    rw [hx, ← Real.rpow_add hD0]; congr 1; ring
  have hneg : (D : ℝ) ^ (-(γ / 2)) = x⁻¹ := by rw [hx, Real.rpow_neg hD0.le]
  refine ⟨hD16, hDN, hDle, hg1, hg2, hgsqrt, hhalf, ?_, ?_, ?_⟩
  · rw [hDγ, hneg]
    calc 4 * (N : ℝ) * ⌈x⌉₊ * ((N : ℝ) ^ 2 / (x * x))
        ≤ 4 * N * (2 * x) * ((N : ℝ) ^ 2 / (x * x)) := by gcongr
      _ = 8 * (N : ℝ) ^ 3 * x⁻¹ := by field_simp; ring
  · have hx' : x ≤ (N : ℝ) ^ (ε * (γ / 2)) := by
      rw [hx, Real.rpow_mul hNpos.le]; exact Real.rpow_le_rpow hD0.le hDle (by linarith)
    have hsplit : (N : ℝ) ^ (2 + ε * (1 + γ / 2)) =
        (N : ℝ) ^ 2 * ((N : ℝ) ^ ε * (N : ℝ) ^ (ε * (γ / 2))) := by
      rw [← Real.rpow_add hNpos, ← Real.rpow_natCast, ← Real.rpow_add hNpos]
      congr 1; push_cast; ring
    rw [hsplit]
    have hg2' : (⌈x⌉₊ : ℝ) ≤ 2 * (N : ℝ) ^ (ε * (γ / 2)) := by linarith
    calc (N : ℝ) ^ 2 * D * ⌈x⌉₊ ≤ (N : ℝ) ^ 2 * (N : ℝ) ^ ε * (2 * (N : ℝ) ^ (ε * (γ / 2))) := by
          gcongr
      _ = 2 * ((N : ℝ) ^ 2 * ((N : ℝ) ^ ε * (N : ℝ) ^ (ε * (γ / 2)))) := by ring
  · have := half_rpow_neg ((N : ℝ) ^ ε) D (γ / 2) (by positivity) hhalf (by linarith)
    rwa [← Real.rpow_mul hNpos.le, show ε * (-(γ / 2)) = -(ε * γ / 2) by ring] at this

/-- **Theorem I, the side terms against `N^{3-εγ/2}`** (for `0 < ε, γ ≤ 1/2`): writing,
`2 + ε(1+γ/2) + εγ/2 = 2 + ε(1+γ) ≤ 2.75`; the hash with `ω < 2.372`,
`2.372 + ε/2 + εγ/2 ≤ 2.747`; and (b): `3/2 ≤ 2 − εγ/4`. -/
theorem partI_side_exponents (ε γ : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hγ : 0 < γ)
    (hγ2 : γ ≤ 1 / 2) :
    2 + ε * (1 + γ / 2) + ε * γ / 2 = 2 + ε * (1 + γ) ∧ 2 + ε * (1 + γ) ≤ 2.75 ∧
    2.372 + ε / 2 + ε * γ / 2 ≤ 2.747 ∧ (3 : ℝ) / 2 ≤ 2 - ε * γ / 4 := by
  have hεγ : ε * γ ≤ 1 / 4 := by nlinarith
  refine ⟨by ring, ?_, ?_, ?_⟩ <;> nlinarith

set_option exponentiation.threshold 10000 in
/-- **Theorem I, Strassen**: the hash term `N^{log₂7 + ε/2}` is below `N^{3-εγ/2}` iff
`ε(1+γ) < 2(3 − log₂7)`; `2(3 − log₂ 7) = 0.38529…` (the text writes `0.3853…`); it holds for
`(1/14, 0.077)` and `(1/18, 0.063)`; for `(1/14, 0.077)` the exponent sum is
`log₂7 + 1/28 + 0.00275 < 2.846 < 2.9`. -/
theorem partI_strassen (ε γ : ℝ) :
    (logb 2 7 + ε / 2 < 3 - ε * γ / 2 ↔ ε * (1 + γ) < 2 * (3 - logb 2 7)) ∧
    0.38529 < 2 * (3 - logb 2 7) ∧ 2 * (3 - logb 2 7) < 0.3853 ∧
    (1 / 14 : ℝ) * (1 + 0.077) < 2 * (3 - logb 2 7) ∧
    (1 / 18 : ℝ) * (1 + 0.063) < 2 * (3 - logb 2 7) ∧
    logb 2 7 + 1 / 28 + 0.00275 < 2.846 := by
  have hlo : (1909 / 680 : ℝ) < logb 2 7 := by
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]
    by_contra h
    push Not at h
    have h2 : (7 : ℝ) ^ 680 ≤ ((2 : ℝ) ^ ((1909 : ℝ) / 680)) ^ 680 :=
      pow_le_pow_left₀ (by norm_num) h 680
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1909 : ℝ) / 680)), ← Real.rpow_mul (by norm_num)] at h2
    have h3 : (1909 : ℝ) / 680 * ((680 : ℕ) : ℝ) = ((1909 : ℕ) : ℝ) := by norm_num
    rw [h3, Real.rpow_natCast] at h2
    have h4 : (7 : ℕ) ^ 680 ≤ 2 ^ 1909 := by exact_mod_cast h2
    exact absurd h4 (by norm_num)
  have hup : logb 2 7 < (8321 / 2964 : ℝ) := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]
    by_contra h
    push Not at h
    have h2 : ((2 : ℝ) ^ ((8321 : ℝ) / 2964)) ^ 2964 ≤ (7 : ℝ) ^ 2964 :=
      pow_le_pow_left₀ (by positivity) h 2964
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((8321 : ℝ) / 2964)), ← Real.rpow_mul (by norm_num)] at h2
    have h3 : (8321 : ℝ) / 2964 * ((2964 : ℕ) : ℝ) = ((8321 : ℕ) : ℝ) := by norm_num
    rw [h3, Real.rpow_natCast] at h2
    have h4 : (2 : ℕ) ^ 8321 ≤ 7 ^ 2964 := by exact_mod_cast h2
    exact absurd h4 (by norm_num)
  have hεγ : ε * (1 + γ) = ε + ε * γ := by ring
  refine ⟨⟨fun h => by linarith, fun h => by linarith⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num at hlo hup ⊢ <;> linarith

/-- **Theorem I, the exponents** (§1, §3.1): `εγ = 0.0055` for `(1/14, 0.077)` and `0.0035` for
`(1/18, 0.063)`; `εγ/2 = 0.00175` (the note's `ε'`); (a) `3 − εγ/2 = 2.99725`; (b), (c)
`2 − εγ/4 = 1.998625 < 1.99863`; with `(1/18, 0.092)` (Corollary 9.1(a)) the exponent
`2 − 0.092/72 = 1.99872…` is worse. -/
theorem partI_exponents :
    (1 / 14 : ℝ) * 0.077 = 0.0055 ∧ (1 / 18 : ℝ) * 0.063 = 0.0035 ∧
    (0.0035 : ℝ) / 2 = 0.00175 ∧ (0.063 : ℝ) / 36 = 0.00175 ∧
    (3 : ℝ) - 0.0055 / 2 = 2.99725 ∧ (2 : ℝ) - 0.0055 / 4 = 1.998625 ∧
    (1.998625 : ℝ) < 1.99863 ∧ (3 : ℝ) - 0.0035 / 2 = 2.99825 ∧ (2 : ℝ) - 0.0035 / 4 = 1.999125 ∧
    (1.99872 : ℝ) < 2 - (1 / 18) * 0.092 / 4 ∧ 2 - (1 / 18 : ℝ) * 0.092 / 4 < 1.99873 ∧
    (1.998625 : ℝ) < 2 - (1 / 18) * 0.092 / 4 := by
  norm_num

/-- **Theorem I (c)**: `n^{1.998625} (log n)^{log₂ 27} = O(n^{1.99863})`. -/
theorem partI_absorb :
    (fun x : ℝ => x ^ (1.998625 : ℝ) * Real.log x ^ logb 2 27) =O[Filter.atTop]
      fun x => x ^ (1.99863 : ℝ) :=
  isBigO_rpow_mul_log _ _ _ (by norm_num)

/-! ### Theorem I′ (§3.2): parameters, the call, the cost terms -/

/-- **Theorem I′, parameters and the call.** `q := ⌊ε log₂ n⌋`, `D := 2^q`, `g := ⌈D^{γ/2}⌉`,
`σ := ⌊√(D/g)⌋`, `g' := ⌈3n/σ⌉`, `N := g' 2^{⌈q/2⌉}`. For `n ≥ 2^{1/ε}`: `q ≥ 1`;
`n^ε/2 < D ≤ n^ε`; `1 ≤ g ≤ D`; `1 ≤ σ ≤ √D`, `σ ≥ √(D/g)/2`, `σ² ≤ D/g`; `1 ≤ n/σ`;
`N ≥ n` and `D ≤ N^ε` (the hypothesis applies); `N²/√D ≥ 9n²/σ > 8n²/σ ≥ |W|` (one call);
the call `N²/D^γ ≤ 256 n² D^{-γ/2}`; writing `D^{1+γ} ≤ N`; probes `1/σ ≤ 2√2 D^{-γ/2}`;
scans `1/g ≤ D^{-γ/2}`; and `D^{-γ/2} ≤ 2^{γ/2} n^{-εγ/2}`. -/
theorem oneHash_params (ε γ : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (n : ℕ) (hn : (2 : ℝ) ^ (1 / ε) ≤ n) :
    let q := ⌊ε * logb 2 n⌋₊
    let D : ℕ := 2 ^ q
    let g := ⌈(D : ℝ) ^ (γ / 2)⌉₊
    let σ := ⌊Real.sqrt ((D : ℝ) / g)⌋₊
    let g' := ⌈3 * (n : ℝ) / σ⌉₊
    let N : ℕ := g' * 2 ^ ((q + 1) / 2)
    1 ≤ q ∧ (n : ℝ) ^ ε / 2 < D ∧ (D : ℝ) ≤ (n : ℝ) ^ ε ∧ 1 ≤ g ∧ g ≤ D ∧
    1 ≤ σ ∧ (σ : ℝ) ≤ Real.sqrt D ∧ Real.sqrt ((D : ℝ) / g) / 2 ≤ σ ∧
    (σ : ℝ) ^ 2 ≤ (D : ℝ) / g ∧ 1 ≤ (n : ℝ) / σ ∧
    (n : ℝ) ≤ N ∧ (D : ℝ) ≤ (N : ℝ) ^ ε ∧
    9 * (n : ℝ) ^ 2 / σ ≤ (N : ℝ) ^ 2 / Real.sqrt D ∧
    (N : ℝ) ^ 2 / (D : ℝ) ^ γ ≤ 256 * (n : ℝ) ^ 2 * (D : ℝ) ^ (-(γ / 2)) ∧
    (D : ℝ) ^ (1 + γ) ≤ N ∧
    1 / (σ : ℝ) ≤ 2 * Real.sqrt 2 * (D : ℝ) ^ (-(γ / 2)) ∧
    1 / (g : ℝ) ≤ (D : ℝ) ^ (-(γ / 2)) ∧
    (D : ℝ) ^ (-(γ / 2)) ≤ 2 ^ (γ / 2) * (n : ℝ) ^ (-(ε * γ / 2)) := by
  intro q D g σ g' N
  have hn1 : (1 : ℝ) ≤ n := le_trans (Real.one_le_rpow (by norm_num) (by positivity)) hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 1 / ε ≤ logb 2 n := (Real.le_logb_iff_rpow_le (by norm_num) hn0).2 hn
  have hεL : 1 ≤ ε * logb 2 n := by
    have := mul_le_mul_of_nonneg_left hL hε.le
    rwa [mul_one_div_cancel hε.ne'] at this
  have hq1 : 1 ≤ q := Nat.le_floor (by exact_mod_cast hεL)
  have hqle : (q : ℝ) ≤ ε * logb 2 n := Nat.floor_le (by linarith)
  have hqlt : ε * logb 2 n < q + 1 := Nat.lt_floor_add_one _
  have hnε : (n : ℝ) ^ ε = (2 : ℝ) ^ (ε * logb 2 n) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn0]
  have hDR : (D : ℝ) = (2 : ℝ) ^ (q : ℝ) := by rw [Real.rpow_natCast]; simp [D]
  have hD2 : (2 : ℝ) ≤ D := by
    rw [hDR]
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := by norm_num
      _ ≤ 2 ^ (q : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast hq1)
  have hD0 : (0 : ℝ) < D := by linarith
  have hDn : (D : ℝ) ≤ (n : ℝ) ^ ε := by
    rw [hDR, hnε]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hqle
  have hnD : (n : ℝ) ^ ε / 2 < D := by
    rw [hDR, hnε, div_lt_iff₀ (by norm_num)]
    calc (2 : ℝ) ^ (ε * logb 2 n) < 2 ^ ((q : ℝ) + 1) :=
          Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hqlt
      _ = 2 ^ (q : ℝ) * 2 := by rw [Real.rpow_add (by norm_num), Real.rpow_one]
  set x := (D : ℝ) ^ (γ / 2) with hx
  have hx1 : 1 ≤ x := Real.one_le_rpow (by linarith) (by positivity)
  have hx0 : 0 < x := by linarith
  have hgx : x ≤ g := Nat.le_ceil _
  have hgx2 : (g : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have hg1 : 1 ≤ g := Nat.ceil_pos.2 hx0
  have hxD : x ≤ D := by
    calc x ≤ (D : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = D := Real.rpow_one _
  have hgD : g ≤ D := by
    have h : (g : ℝ) < D + 1 := by linarith
    have h' : g < D + 1 := by exact_mod_cast h
    omega
  have hgR1 : (1 : ℝ) ≤ g := by exact_mod_cast hg1
  have hgRD : (g : ℝ) ≤ D := by exact_mod_cast hgD
  have hg0 : (0 : ℝ) < g := by linarith
  have hg2x : (g : ℝ) ≤ 2 * x := by linarith
  set r := (D : ℝ) / g with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hg0]; linarith
  have hrD : r ≤ D := div_le_self hD0.le hgR1
  have hsr1 : 1 ≤ Real.sqrt r := by simpa using Real.sqrt_le_sqrt hr1
  have hσle : (σ : ℝ) ≤ Real.sqrt r := Nat.floor_le (Real.sqrt_nonneg _)
  have hσ1 : 1 ≤ σ := Nat.le_floor (by exact_mod_cast hsr1)
  have hσR : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hσge : Real.sqrt r / 2 ≤ σ := floor_ge_half _ hsr1
  have hσsq : (σ : ℝ) ^ 2 ≤ r := by
    have := pow_le_pow_left₀ (by positivity) hσle 2
    rwa [Real.sq_sqrt (by linarith)] at this
  have hsD : Real.sqrt r ≤ Real.sqrt D := Real.sqrt_le_sqrt hrD
  have hσD : (σ : ℝ) ≤ Real.sqrt D := hσle.trans hsD
  have hsqD_le : Real.sqrt (D : ℝ) ≤ D := Real.sqrt_le_iff.2 ⟨hD0.le, by
    have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ D) hD0.le
    linarith⟩
  have hnε_le : (n : ℝ) ^ ε ≤ n := by
    calc (n : ℝ) ^ ε ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = n := Real.rpow_one _
  have hσn : (σ : ℝ) ≤ n := by linarith
  have hnσ : 1 ≤ (n : ℝ) / σ := by rw [le_div_iff₀ hσ0]; linarith
  have hD4 : (D : ℝ) ≤ 4 * g * σ ^ 2 := by
    have h2 : Real.sqrt r ≤ 2 * σ := by linarith
    have h1 : r ≤ 4 * σ ^ 2 := by
      calc r = (Real.sqrt r) ^ 2 := (Real.sq_sqrt (by linarith)).symm
        _ ≤ (2 * σ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
        _ = 4 * σ ^ 2 := by ring
    have e : (D : ℝ) = r * g := by rw [hr]; field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_right h1 hg0.le
    linarith
  have hg'lo : 3 * (n : ℝ) / σ ≤ g' := Nat.le_ceil _
  have hg'hi : (g' : ℝ) < 3 * n / σ + 1 := Nat.ceil_lt_add_one (by positivity)
  have hg'hi4 : (g' : ℝ) ≤ 4 * n / σ := by
    have : 4 * (n : ℝ) / σ = 3 * n / σ + n / σ := by ring
    linarith
  have hg'0 : (0 : ℝ) < g' := by
    have : 0 < 3 * (n : ℝ) / σ := by positivity
    linarith
  obtain ⟨hpw1, hpw2⟩ := two_pow_half q
  have hDq : (2 : ℝ) ^ q = D := by rw [hDR, Real.rpow_natCast]
  rw [hDq] at hpw1 hpw2
  have hNR : (N : ℝ) = g' * (2 : ℝ) ^ ((q + 1) / 2) := by simp [N]
  have hsD0 : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.2 hD0
  have hNlo : g' * Real.sqrt (D : ℝ) ≤ N := by
    rw [hNR]; exact mul_le_mul_of_nonneg_left hpw1 hg'0.le
  have hNhi : (N : ℝ) ^ 2 ≤ 2 * g' ^ 2 * D := by
    rw [hNR, mul_pow]
    have := mul_le_mul_of_nonneg_left hpw2 (sq_nonneg (g' : ℝ))
    linarith
  have hnN : (n : ℝ) ≤ N := by
    have h1 : 3 * (n : ℝ) / σ * Real.sqrt D ≤ g' * Real.sqrt D :=
      mul_le_mul_of_nonneg_right hg'lo hsD0.le
    have h2 : 3 * (n : ℝ) ≤ 3 * n / σ * Real.sqrt D := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hσ0]
      exact mul_le_mul_of_nonneg_left hσD (by positivity)
    linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hDNε : (D : ℝ) ≤ (N : ℝ) ^ ε := hDn.trans (Real.rpow_le_rpow (by positivity) hnN hε.le)
  have hg'sq : 9 * (n : ℝ) ^ 2 / σ ^ 2 ≤ g' ^ 2 := by
    calc 9 * (n : ℝ) ^ 2 / σ ^ 2 = (3 * n / σ) ^ 2 := by ring
      _ ≤ (g' : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hg'lo 2
  have hNsq : (g' : ℝ) ^ 2 * D ≤ N ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hNlo 2
    rwa [mul_pow, Real.sq_sqrt hD0.le] at this
  have hsq2 : Real.sqrt (D : ℝ) * Real.sqrt D = D := Real.mul_self_sqrt hD0.le
  have h9 : 9 * (n : ℝ) ^ 2 / σ ≤ N ^ 2 / Real.sqrt D := by
    rw [le_div_iff₀ hsD0]
    have key : 9 * (n : ℝ) ^ 2 / σ * Real.sqrt D ≤ 9 * (n : ℝ) ^ 2 / σ ^ 2 * D := by
      have e : 9 * (n : ℝ) ^ 2 / σ ^ 2 * D = (9 * n ^ 2 / σ ^ 2 * Real.sqrt D) * Real.sqrt D := by
        rw [mul_assoc, hsq2]
      have e2 : 9 * (n : ℝ) ^ 2 / σ * Real.sqrt D = (9 * n ^ 2 / σ ^ 2 * Real.sqrt D) * σ := by
        field_simp
      rw [e, e2]; exact mul_le_mul_of_nonneg_left hσD (by positivity)
    calc 9 * (n : ℝ) ^ 2 / σ * Real.sqrt D ≤ 9 * (n : ℝ) ^ 2 / σ ^ 2 * D := key
      _ ≤ g' ^ 2 * D := mul_le_mul_of_nonneg_right hg'sq hD0.le
      _ ≤ N ^ 2 := hNsq
  have hN2 : (N : ℝ) ^ 2 ≤ 256 * n ^ 2 * x := by
    have h1 : (N : ℝ) ^ 2 ≤ 2 * (4 * n / σ) ^ 2 * D := le_trans hNhi (by gcongr)
    have h2 : 2 * (4 * (n : ℝ) / σ) ^ 2 * D ≤ 2 * (4 * n / σ) ^ 2 * (4 * g * σ ^ 2) := by gcongr
    have h3 : 2 * (4 * (n : ℝ) / σ) ^ 2 * (4 * g * σ ^ 2) = 128 * n ^ 2 * g := by
      field_simp; ring
    have h4 := mul_le_mul_of_nonneg_left hg2x (by positivity : (0 : ℝ) ≤ 128 * n ^ 2)
    linarith
  have hDγ : (D : ℝ) ^ γ = x * x := by
    rw [hx, ← Real.rpow_add hD0]; congr 1; ring
  have hxneg : (D : ℝ) ^ (-(γ / 2)) = x⁻¹ := by rw [hx, Real.rpow_neg hD0.le]
  have hcall : (N : ℝ) ^ 2 / (D : ℝ) ^ γ ≤ 256 * n ^ 2 * (D : ℝ) ^ (-(γ / 2)) := by
    rw [hDγ, hxneg, div_le_iff₀ (by positivity)]
    calc (N : ℝ) ^ 2 ≤ 256 * n ^ 2 * x := hN2
      _ = 256 * n ^ 2 * x⁻¹ * (x * x) := by field_simp
  have hDpow : (D : ℝ) ^ (1 + γ) ≤ N := by
    apply le_of_log_le' (Real.rpow_pos_of_pos hD0 _) hN0
    rw [Real.log_rpow hD0]
    have h1 : Real.log D ≤ ε * Real.log N := by
      have := Real.log_le_log hD0 hDNε; rwa [Real.log_rpow hN0] at this
    have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
    have h2 : (1 + γ) * ε ≤ 1 := by
      have : (1 + γ) * ε ≤ (3 / 2) * (1 / 2) := mul_le_mul (by linarith) hε2 hε.le (by norm_num)
      linarith
    have h3 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 + γ)
    have h4 := mul_le_mul_of_nonneg_right h2 hlN
    linarith
  have hx3 : x ^ 3 ≤ D := by
    have e : x ^ 3 = (D : ℝ) ^ (3 * (γ / 2)) := by
      rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; congr 1; push_cast; ring
    rw [e]
    calc (D : ℝ) ^ (3 * (γ / 2)) ≤ (D : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = D := Real.rpow_one _
  have hx2 : x ^ 2 ≤ 8 * (σ : ℝ) ^ 2 := by
    have h3 : x ^ 3 ≤ 8 * x * σ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hg2x (sq_nonneg (σ : ℝ))
      linarith
    by_contra h
    push Not at h
    have := mul_lt_mul_of_pos_left h hx0
    linarith
  have hσinv : 1 / (σ : ℝ) ≤ 2 * Real.sqrt 2 * (D : ℝ) ^ (-(γ / 2)) := by
    rw [hxneg]
    have h8 : Real.sqrt (8 * (σ : ℝ) ^ 2) = 2 * Real.sqrt 2 * σ := by
      rw [show (8 : ℝ) * σ ^ 2 = (2 * σ) ^ 2 * 2 by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)]; ring
    have hx8 : x ≤ 2 * Real.sqrt 2 * σ := by
      rw [← h8]; exact (le_abs_self x).trans (Real.abs_le_sqrt hx2)
    rw [div_le_iff₀ hσ0]
    calc (1 : ℝ) = x⁻¹ * x := by field_simp
      _ ≤ x⁻¹ * (2 * Real.sqrt 2 * σ) := mul_le_mul_of_nonneg_left hx8 (by positivity)
      _ = 2 * Real.sqrt 2 * x⁻¹ * σ := by ring
  have hginv : 1 / (g : ℝ) ≤ (D : ℝ) ^ (-(γ / 2)) := by
    rw [hxneg, ← one_div]; exact one_div_le_one_div_of_le hx0 hgx
  have hlast : (D : ℝ) ^ (-(γ / 2)) ≤ 2 ^ (γ / 2) * (n : ℝ) ^ (-(ε * γ / 2)) := by
    have := half_rpow_neg ((n : ℝ) ^ ε) D (γ / 2) (by positivity) hnD.le (by linarith)
    rwa [← Real.rpow_mul hn0.le, show ε * (-(γ / 2)) = -(ε * γ / 2) by ring] at this
  exact ⟨hq1, hnD, hDn, hg1, hgD, hσ1, hσD, hσge, hσsq, hnσ, hnN, hDNε, h9, hcall, hDpow,
    hσinv, hginv, hlast⟩

/-- **Theorem I′, scans**: `F ≤ eσn²/D` gives `Fσ ≤ e n²/g` when `σ² ≤ D/g`. -/
theorem oneHash_scans (F σ n D g : ℝ) (hσ : 0 ≤ σ) (hD : 0 < D) (hg : 0 < g)
    (hF : F ≤ exp 1 * σ * n ^ 2 / D) (hσ2 : σ ^ 2 ≤ D / g) :
    F * σ ≤ exp 1 * n ^ 2 / g := by
  have h1 : F * σ ≤ exp 1 * σ * n ^ 2 / D * σ := mul_le_mul_of_nonneg_right hF hσ
  have h2 : exp 1 * σ * n ^ 2 / D * σ = exp 1 * n ^ 2 * σ ^ 2 / D := by ring
  have h3 : exp 1 * n ^ 2 * σ ^ 2 / D ≤ exp 1 * n ^ 2 * (D / g) / D :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσ2 (by positivity)) hD.le
  have h4 : exp 1 * n ^ 2 * (D / g) / D = exp 1 * n ^ 2 / g := by field_simp
  linarith

/-- **Theorem I′, the exponents**: `2 − 0.0055/2 = 1.99725`, `2 − 0.0035/2 = 1.99825`, and the
factor `log n` is absorbed: `O(n^{1.99725} log n) ≤ O(n^{1.99726})`,
`O(n^{1.99825} log n) ≤ O(n^{1.99826})`. -/
theorem oneHash_exponents :
    (2 : ℝ) - 0.0055 / 2 = 1.99725 ∧ (2 : ℝ) - 0.0035 / 2 = 1.99825 ∧
    ((fun x : ℝ => x ^ (1.99725 : ℝ) * Real.log x ^ (1 : ℝ)) =O[Filter.atTop]
      fun x => x ^ (1.99726 : ℝ)) ∧
    ((fun x : ℝ => x ^ (1.99825 : ℝ) * Real.log x ^ (1 : ℝ)) =O[Filter.atTop]
      fun x => x ^ (1.99826 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, isBigO_rpow_mul_log _ _ _ (by norm_num),
    isBigO_rpow_mul_log _ _ _ (by norm_num)⟩

/-! ### Theorem II (§4.2, Lemma II.3, §4.7) -/

/-- **§4.2, consequences of the parameters**: `Λ := 4e`, `σ := ⌊√(n^ε/Λ)⌋`,
`q := ⌈log₂(2eσ²)⌉`. For `σ ≥ 1`: `2^q < Λσ² ≤ n^ε`, `e 2^{-q} σ² ≤ 1/2`,
`σ ≥ √(n^ε/Λ)/2`, `q ≥ 1`, and `q ≤ ε log₂ n + 4`. -/
theorem staged_params (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    let Λ := 4 * exp 1
    let σ := ⌊Real.sqrt ((n : ℝ) ^ ε / Λ)⌋₊
    let q := ⌈logb 2 (2 * exp 1 * (σ : ℝ) ^ 2)⌉₊
    1 ≤ σ →
    (2 : ℝ) ^ q < Λ * (σ : ℝ) ^ 2 ∧ Λ * (σ : ℝ) ^ 2 ≤ (n : ℝ) ^ ε ∧
    exp 1 * (2 : ℝ)⁻¹ ^ q * (σ : ℝ) ^ 2 ≤ 1 / 2 ∧
    Real.sqrt ((n : ℝ) ^ ε / Λ) / 2 ≤ σ ∧ 1 ≤ q ∧ (q : ℝ) ≤ ε * logb 2 n + 4 := by
  dsimp only
  intro hσ1
  set a := (n : ℝ) ^ ε / (4 * exp 1) with ha
  set σ := ⌊Real.sqrt a⌋₊ with hσdef
  have he := Real.exp_one_gt_d9
  have hσR : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  have hσa : (σ : ℝ) ≤ Real.sqrt a := Nat.floor_le (Real.sqrt_nonneg _)
  have ha0 : 0 ≤ a := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  have hσ2 : (σ : ℝ) ^ 2 ≤ a := by
    have := pow_le_pow_left₀ (by positivity) hσa 2
    rwa [Real.sq_sqrt ha0] at this
  have hΛ : 4 * exp 1 * (σ : ℝ) ^ 2 ≤ (n : ℝ) ^ ε := by
    rw [ha, le_div_iff₀ (by positivity)] at hσ2; linarith
  have hx1 : 1 ≤ 2 * exp 1 * (σ : ℝ) ^ 2 := by nlinarith
  obtain ⟨h1, h2⟩ := ceil_logb_spec _ hx1
  set q := ⌈logb 2 (2 * exp 1 * (σ : ℝ) ^ 2)⌉₊ with hq
  have hpq : (0 : ℝ) < 2 ^ q := by positivity
  have hlt : (2 : ℝ) ^ q < 4 * exp 1 * σ ^ 2 := by linarith
  refine ⟨hlt, hΛ, ?_, ?_, ?_, ?_⟩
  · rw [inv_pow]
    have : exp 1 * (2 ^ q)⁻¹ * (σ : ℝ) ^ 2 = exp 1 * σ ^ 2 / 2 ^ q := by ring
    rw [this, div_le_iff₀ hpq]; linarith
  · exact floor_ge_half _ (hσR.trans hσa)
  · exact Nat.ceil_pos.2 (Real.logb_pos (by norm_num) (by nlinarith))
  · have hn0 : (0 : ℝ) < n := by
      rcases (Nat.cast_nonneg n : (0 : ℝ) ≤ n).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, Real.zero_rpow hε.ne'] at hΛ
        nlinarith
    have hlog : (q : ℝ) < logb 2 ((n : ℝ) ^ ε) := by
      have e : (2 : ℝ) ^ q = (2 : ℝ) ^ (q : ℝ) := (Real.rpow_natCast 2 q).symm
      have := Real.logb_lt_logb (b := 2) (by norm_num) hpq (lt_of_lt_of_le hlt hΛ)
      rwa [e, Real.logb_rpow (by norm_num) (by norm_num)] at this
    rw [Real.logb_rpow_eq_mul_logb_of_pos hn0] at hlog
    linarith

/-- **§4.2, the other parameters**: `k := ⌈log₂(n/σ)⌉` has `n/σ ≤ 2^k < 2n/σ` and `k ≥ 1`
when `n/σ ≥ 2`; `g' := ⌈3n/σ⌉` has `3n/σ ≤ g' ≤ 4n/σ` when `n/σ ≥ 1`; `|𝔅_i| ≤ 2^k + n/σ <
3n/σ`; `B := ⌈log₂(σ+1)⌉` has `σ < 2^B`; `L := ⌈log₂ n⌉` has `n ≤ 2^L`. -/
theorem staged_params' (n σ : ℕ) (hσ : 1 ≤ σ) (hnσ : 2 ≤ (n : ℝ) / σ) :
    let k := ⌈logb 2 ((n : ℝ) / σ)⌉₊
    let g' := ⌈3 * (n : ℝ) / σ⌉₊
    (n : ℝ) / σ ≤ 2 ^ k ∧ (2 : ℝ) ^ k < 2 * n / σ ∧ 1 ≤ k ∧
    3 * (n : ℝ) / σ ≤ g' ∧ (g' : ℝ) ≤ 4 * n / σ ∧ (2 : ℝ) ^ k + n / σ < 3 * n / σ ∧
    σ < 2 ^ Nat.clog 2 (σ + 1) ∧ n ≤ 2 ^ Nat.clog 2 n := by
  dsimp only
  have hx : (1 : ℝ) ≤ n / σ := by linarith
  have hσR : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  obtain ⟨h1, h2⟩ := ceil_logb_spec _ hx
  have e2 : (2 : ℝ) * n / σ = 2 * (n / σ) := by ring
  have e3 : (3 : ℝ) * n / σ = 3 * (n / σ) := by ring
  have e4 : (4 : ℝ) * n / σ = 4 * (n / σ) := by ring
  have hk1 : 1 ≤ ⌈logb 2 ((n : ℝ) / σ)⌉₊ :=
    Nat.ceil_pos.2 (Real.logb_pos (by norm_num) (by linarith))
  have hg1 : 3 * (n : ℝ) / σ ≤ ⌈3 * (n : ℝ) / σ⌉₊ := Nat.le_ceil _
  have hg2 : (⌈3 * (n : ℝ) / σ⌉₊ : ℝ) < 3 * n / σ + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hc1 := Nat.le_pow_clog (by norm_num : 1 < 2) (σ + 1)
  have hc2 := Nat.le_pow_clog (by norm_num : 1 < 2) n
  refine ⟨h1, by rw [e2]; exact h2, hk1, hg1, ?_, ?_, by omega, hc2⟩
  · linarith
  · rw [e3]; linarith

/-- **Lemma II.3, the conditions and the cost of the calls.** With `1 ≤ D < Λσ² ≤ n^ε`
(`D = 2^l`, `l ≤ q`), `3n/σ ≤ g' ≤ 4n/σ`, `g'√D ≤ N`, `N² ≤ 2g'²D`, `1 ≤ σ ≤ n`, `Λ ≥ 1`,
`0 < ε, γ ≤ 1/2`: `D ≤ N^ε`; `N²/√D ≥ 9n²√D/σ²`; the parts of `W` times the cost of a call,
`(1 + 2σ/√D) N²/D^γ ≤ 96Λ n² σ^{-2γ}`; `D^{1+γ} ≤ N`; `8n²/σ ≤ 8n²σ^{-2γ}`. -/
theorem eval_cost (ε γ Λ : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (hΛ : 1 ≤ Λ) (n σ g' N D : ℝ) (hσ : 1 ≤ σ) (hσn : σ ≤ n) (hD1 : 1 ≤ D) (hDΛ : D < Λ * σ ^ 2)
    (hΛn : Λ * σ ^ 2 ≤ n ^ ε) (hg'lo : 3 * n / σ ≤ g') (hg'hi : g' ≤ 4 * n / σ)
    (hNlo : g' * Real.sqrt D ≤ N) (hNhi : N ^ 2 ≤ 2 * g' ^ 2 * D) :
    D ≤ N ^ ε ∧ 9 * n ^ 2 * Real.sqrt D / σ ^ 2 ≤ N ^ 2 / Real.sqrt D ∧
    (1 + 2 * σ / Real.sqrt D) * (N ^ 2 / D ^ γ) ≤ 96 * Λ * n ^ 2 * σ ^ (-(2 * γ)) ∧
    D ^ (1 + γ) ≤ N ∧ 8 * n ^ 2 / σ ≤ 8 * n ^ 2 * σ ^ (-(2 * γ)) := by
  have hσ0 : 0 < σ := by linarith
  have hn0 : 0 < n := by linarith
  have hD0 : 0 < D := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.2 hD0
  have hsD1 : 1 ≤ Real.sqrt D := by simpa using Real.sqrt_le_sqrt hD1
  have hsD2 : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD0.le
  have hnσ : 1 ≤ n / σ := by rw [le_div_iff₀ hσ0]; linarith
  have e3 : 3 * n / σ = 3 * (n / σ) := by ring
  have hg'0 : 0 < g' := by have : 0 < 3 * n / σ := by positivity
                           linarith
  have hN1 : 1 ≤ N := by
    have := mul_le_mul_of_nonneg_left hsD1 hg'0.le
    linarith
  have hN0 : 0 < N := by linarith
  have hb : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hs : 0 ≤ Real.log σ := Real.log_nonneg hσ
  have hlN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have ha : Real.log D ≤ Real.log Λ + 2 * Real.log σ := by
    have := Real.log_le_log hD0 hDΛ.le
    rwa [Real.log_mul hΛ0.ne' (by positivity), Real.log_pow] at this
  have hbs : Real.log Λ + 2 * Real.log σ ≤ ε * Real.log n := by
    have := Real.log_le_log (by positivity) hΛn
    rwa [Real.log_mul hΛ0.ne' (by positivity), Real.log_pow, Real.log_rpow hn0] at this
  have hlN : Real.log n - Real.log σ + Real.log D / 2 ≤ Real.log N := by
    have h1 : n / σ * Real.sqrt D ≤ N := by
      have : n / σ * Real.sqrt D ≤ g' * Real.sqrt D :=
        mul_le_mul_of_nonneg_right (by linarith) hsD.le
      linarith
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_mul (by positivity) hsD.ne', Real.log_div hn0.ne' hσ0.ne',
      Real.log_sqrt hD0.le] at this
  have hkey : Real.log D ≤ ε * Real.log N := by
    have h1 : (1 - ε / 2) * Real.log D ≤ (1 - ε / 2) * (Real.log Λ + 2 * Real.log σ) :=
      mul_le_mul_of_nonneg_left ha (by linarith)
    have h2 : ε * (Real.log n - Real.log σ + Real.log D / 2) ≤ ε * Real.log N :=
      mul_le_mul_of_nonneg_left hlN hε.le
    nlinarith [mul_nonneg hε.le hb, mul_nonneg hε.le hs]
  have hDN : D ≤ N ^ ε := by
    apply le_of_log_le' hD0 (Real.rpow_pos_of_pos hN0 _)
    rw [Real.log_rpow hN0]; exact hkey
  have hDpow : D ^ (1 + γ) ≤ N := by
    apply le_of_log_le' (Real.rpow_pos_of_pos hD0 _) hN0
    rw [Real.log_rpow hD0]
    have h2 : (1 + γ) * ε ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hkey (by linarith : (0 : ℝ) ≤ 1 + γ),
      mul_le_mul_of_nonneg_right h2 hlN0]
  have hg'sq : 9 * n ^ 2 / σ ^ 2 ≤ g' ^ 2 := by
    calc 9 * n ^ 2 / σ ^ 2 = (3 * n / σ) ^ 2 := by ring
      _ ≤ g' ^ 2 := pow_le_pow_left₀ (by positivity) hg'lo 2
  have hNsq : g' ^ 2 * D ≤ N ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hNlo 2
    rwa [mul_pow, hsD2] at this
  have hb' : 9 * n ^ 2 * Real.sqrt D / σ ^ 2 ≤ N ^ 2 / Real.sqrt D := by
    rw [le_div_iff₀ hsD]
    calc 9 * n ^ 2 * Real.sqrt D / σ ^ 2 * Real.sqrt D = 9 * n ^ 2 / σ ^ 2 * D := by
          rw [show 9 * n ^ 2 / σ ^ 2 * D = 9 * n ^ 2 / σ ^ 2 * Real.sqrt D ^ 2 by rw [hsD2]]
          ring
      _ ≤ g' ^ 2 * D := mul_le_mul_of_nonneg_right hg'sq hD0.le
      _ ≤ N ^ 2 := hNsq
  have hN2 : N ^ 2 ≤ 32 * (n ^ 2 / σ ^ 2) * D := by
    calc N ^ 2 ≤ 2 * g' ^ 2 * D := hNhi
      _ ≤ 2 * (4 * n / σ) ^ 2 * D := by gcongr
      _ = 32 * (n ^ 2 / σ ^ 2) * D := by ring
  have hDm : 0 < D ^ (-γ) := Real.rpow_pos_of_pos hD0 _
  have hσm : 0 < σ ^ (-(2 * γ)) := Real.rpow_pos_of_pos hσ0 _
  have hT1 : D * D ^ (-γ) ≤ Λ * σ ^ 2 * σ ^ (-(2 * γ)) := by
    apply le_of_log_le' (by positivity) (by positivity)
    rw [Real.log_mul hD0.ne' hDm.ne', Real.log_rpow hD0,
      Real.log_mul (by positivity) hσm.ne', Real.log_mul hΛ0.ne' (by positivity), Real.log_pow,
      Real.log_rpow hσ0]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ 1 - γ), mul_nonneg hγ.le hb]
  have hT2 : 2 * σ * Real.sqrt D * D ^ (-γ) ≤ 2 * (Λ * σ ^ 2 * σ ^ (-(2 * γ))) := by
    have : σ * Real.sqrt D * D ^ (-γ) ≤ Λ * σ ^ 2 * σ ^ (-(2 * γ)) := by
      apply le_of_log_le' (by positivity) (by positivity)
      rw [Real.log_mul (by positivity) hDm.ne', Real.log_mul hσ0.ne' hsD.ne', Real.log_rpow hD0,
        Real.log_sqrt hD0.le, Real.log_mul (by positivity) hσm.ne',
        Real.log_mul hΛ0.ne' (by positivity), Real.log_pow, Real.log_rpow hσ0]
      push_cast
      have h1 := mul_le_mul_of_nonneg_left ha (by linarith : (0 : ℝ) ≤ 1 / 2 - γ)
      have h2 := mul_nonneg hγ.le hb
      linarith
    linarith
  have hq : 2 * σ / Real.sqrt D * D = 2 * σ * Real.sqrt D := by
    rw [show 2 * σ / Real.sqrt D * D = 2 * σ / Real.sqrt D * Real.sqrt D ^ 2 by rw [hsD2]]
    field_simp
  have hc : (1 + 2 * σ / Real.sqrt D) * (N ^ 2 / D ^ γ) ≤ 96 * Λ * n ^ 2 * σ ^ (-(2 * γ)) := by
    have hDg : N ^ 2 / D ^ γ = N ^ 2 * D ^ (-γ) := by rw [Real.rpow_neg hD0.le, div_eq_mul_inv]
    rw [hDg]
    have hpos : 0 ≤ 1 + 2 * σ / Real.sqrt D := by positivity
    calc (1 + 2 * σ / Real.sqrt D) * (N ^ 2 * D ^ (-γ))
        ≤ (1 + 2 * σ / Real.sqrt D) * (32 * (n ^ 2 / σ ^ 2) * D * D ^ (-γ)) := by gcongr
      _ = 32 * (n ^ 2 / σ ^ 2) * (D * D ^ (-γ) + 2 * σ * Real.sqrt D * D ^ (-γ)) := by
          linear_combination (32 * (n ^ 2 / σ ^ 2) * D ^ (-γ)) * hq
      _ ≤ 32 * (n ^ 2 / σ ^ 2) * (Λ * σ ^ 2 * σ ^ (-(2 * γ)) +
            2 * (Λ * σ ^ 2 * σ ^ (-(2 * γ)))) :=
          mul_le_mul_of_nonneg_left (add_le_add hT1 hT2) (by positivity)
      _ = 96 * Λ * n ^ 2 * σ ^ (-(2 * γ)) := by field_simp; ring
  have he : 8 * n ^ 2 / σ ≤ 8 * n ^ 2 * σ ^ (-(2 * γ)) := by
    have h1 : σ ^ (-(1 : ℝ)) ≤ σ ^ (-(2 * γ)) :=
      Real.rpow_le_rpow_of_exponent_le hσ (by linarith)
    rw [Real.rpow_neg_one] at h1
    rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
  exact ⟨hDN, hb', hc, hDpow, he⟩

/-- **Lemma II.3, splitting `W`**: `|W| ≤ 8n²/σ` positions in parts of `⌊N²/√D⌋` make at most
`1 + 2σ/√D` parts, when `N²/√D ≥ 9n²√D/σ²` and `σ ≤ n`, `1 ≤ D`. -/
theorem parts_le (n σ N D : ℝ) (hσ : 1 ≤ σ) (hσn : σ ≤ n) (hD1 : 1 ≤ D)
    (hN : 9 * n ^ 2 * Real.sqrt D / σ ^ 2 ≤ N ^ 2 / Real.sqrt D) (W : ℕ)
    (hW : (W : ℝ) ≤ 8 * n ^ 2 / σ) :
    let P := ⌊N ^ 2 / Real.sqrt D⌋₊
    0 < P ∧ (((W + P - 1) / P : ℕ) : ℝ) ≤ 1 + 2 * σ / Real.sqrt D := by
  dsimp only
  have hσ0 : 0 < σ := by linarith
  have hn0 : 0 < n := by linarith
  have hD0 : 0 < D := by linarith
  have hsD : 0 < Real.sqrt D := Real.sqrt_pos.2 hD0
  have hsD1 : 1 ≤ Real.sqrt D := by simpa using Real.sqrt_le_sqrt hD1
  have h9 : 9 ≤ 9 * n ^ 2 * Real.sqrt D / σ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have : σ ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hσ0.le hσn 2
    nlinarith
  have hM1 : 1 ≤ N ^ 2 / Real.sqrt D := by linarith
  have hP := floor_ge_half _ hM1
  have hPpos : (0 : ℝ) < ⌊N ^ 2 / Real.sqrt D⌋₊ := by linarith
  have hPnat : 0 < ⌊N ^ 2 / Real.sqrt D⌋₊ := by exact_mod_cast hPpos
  refine ⟨hPnat, ?_⟩
  set P := ⌊N ^ 2 / Real.sqrt D⌋₊ with hPdef
  have hterm : (((W + P - 1) / P : ℕ) : ℝ) ≤ W / P + 1 := by
    refine Nat.cast_div_le.trans ?_
    have : ((W + P - 1 : ℕ) : ℝ) ≤ W + P := by
      have : W + P - 1 ≤ W + P := by omega
      exact_mod_cast this
    calc ((W + P - 1 : ℕ) : ℝ) / P ≤ (W + P) / P := div_le_div_of_nonneg_right this hPpos.le
      _ = W / P + 1 := by rw [add_div, div_self hPpos.ne']
  have hW' : (W : ℝ) / P ≤ 2 * σ / Real.sqrt D := by
    rw [div_le_iff₀ hPpos]
    calc (W : ℝ) ≤ 8 * n ^ 2 / σ := hW
      _ ≤ 9 * n ^ 2 / σ := by gcongr; norm_num
      _ = 2 * σ / Real.sqrt D * (9 * n ^ 2 * Real.sqrt D / σ ^ 2 / 2) := by field_simp
      _ ≤ 2 * σ / Real.sqrt D * P :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- **Lemma II.3, last line**: `σ ≥ √(n^ε/Λ)/2` gives `σ^{-2γ} ≤ (4Λ)^γ n^{-εγ}`. -/
theorem sigma_rpow_le (ε γ Λ n σ : ℝ) (hγ : 0 ≤ γ) (hΛ : 0 < Λ) (hn : 0 < n)
    (hσ : Real.sqrt (n ^ ε / Λ) / 2 ≤ σ) (hσ0 : 0 < σ) :
    σ ^ (-(2 * γ)) ≤ (4 * Λ) ^ γ * n ^ (-(ε * γ)) := by
  have ha0 : 0 < n ^ ε / Λ := div_pos (Real.rpow_pos_of_pos hn ε) hΛ
  have h2 : Real.sqrt (n ^ ε / Λ) ≤ 2 * σ := by linarith
  have h3 : n ^ ε / Λ ≤ (2 * σ) ^ 2 := (Real.sqrt_le_iff.1 h2).2
  have h4 : n ^ ε / (4 * Λ) ≤ σ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hΛ] at h3
    nlinarith
  have h5 : 0 < n ^ ε / (4 * Λ) := by positivity
  have e1 : σ ^ (-(2 * γ)) = ((σ ^ 2) ^ γ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hσ0.le, Real.rpow_neg hσ0.le]
    norm_num
  have e2 : (4 * Λ) ^ γ * n ^ (-(ε * γ)) = ((n ^ ε / (4 * Λ)) ^ γ)⁻¹ := by
    rw [Real.div_rpow (Real.rpow_nonneg hn.le ε) (by positivity), ← Real.rpow_mul hn.le,
      Real.rpow_neg hn.le]
    field_simp
  rw [e1, e2]
  exact inv_anti₀ (Real.rpow_pos_of_pos h5 γ) (Real.rpow_le_rpow h5.le h4 hγ)

/-- **§4.7 (ii), the count of evaluations**: with `ℓ = log₂ n ≥ 1`, `L ≤ ℓ + 1`,
`q ≤ εℓ + 4`, `ε ≤ 1/2`, `d ≤ cℓ`, `|E| ≤ 4(dq)²`, `B ≤ ℓ`: `L q |E| B² ≤ 1000 c² ℓ⁸`. -/
theorem stage_evals_le (ε c ℓ L q d E B : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hℓ : 1 ≤ ℓ)
    (hL0 : 0 ≤ L) (hL : L ≤ ℓ + 1) (hq0 : 0 ≤ q) (hq : q ≤ ε * ℓ + 4) (hd0 : 0 ≤ d)
    (hd : d ≤ c * ℓ) (hE0 : 0 ≤ E) (hE : E ≤ 4 * (d * q) ^ 2) (hB0 : 0 ≤ B) (hB : B ≤ ℓ) :
    L * q * E * B ^ 2 ≤ 1000 * c ^ 2 * ℓ ^ 8 := by
  have hq5 : q ≤ 5 * ℓ := by nlinarith
  have hL2 : L ≤ 2 * ℓ := by linarith
  have hdq : d * q ≤ c * ℓ * (5 * ℓ) := mul_le_mul hd hq5 hq0 (by nlinarith)
  have hdq0 : 0 ≤ d * q := mul_nonneg hd0 hq0
  have hE' : E ≤ 100 * c ^ 2 * ℓ ^ 4 := by
    have : (d * q) ^ 2 ≤ (c * ℓ * (5 * ℓ)) ^ 2 := pow_le_pow_left₀ hdq0 hdq 2
    nlinarith
  have hB2 : B ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hB0 hB 2
  calc L * q * E * B ^ 2 ≤ (2 * ℓ) * (5 * ℓ) * (100 * c ^ 2 * ℓ ^ 4) * ℓ ^ 2 := by
        apply mul_le_mul _ hB2 (by positivity) (by positivity)
        apply mul_le_mul _ hE' hE0 (by positivity)
        exact mul_le_mul hL2 hq5 hq0 (by linarith)
    _ = 1000 * c ^ 2 * ℓ ^ 8 := by ring

/-- **§4.7 (iii), (iv)**: `2^L ≥ n` and `|𝒫₀| ≤ 8n²/σ` give `|𝒫_L| ≤ |𝒫₀|/2^L ≤ 8n/σ`;
counts at most `σ²` per probe sum to at most `8σn² ≤ 8n³`. -/
theorem final_scans_le (n σ P0 PL twoPowL : ℝ) (hσ : 0 < σ) (hσn : σ ≤ n) (hL : n ≤ twoPowL)
    (hP0 : P0 ≤ 8 * n ^ 2 / σ) (hPL : twoPowL * PL ≤ P0) (hPL0 : 0 ≤ PL) :
    PL ≤ 8 * n / σ ∧ σ ^ 2 * (8 * n ^ 2 / σ) ≤ 8 * n ^ 3 := by
  have hn : 0 < n := lt_of_lt_of_le hσ hσn
  have hL0 : 0 < twoPowL := lt_of_lt_of_le hn hL
  constructor
  · have h1 : PL ≤ P0 / twoPowL := by rw [le_div_iff₀ hL0]; linarith
    have h2 : P0 / twoPowL ≤ 8 * n ^ 2 / σ / twoPowL := div_le_div_of_nonneg_right hP0 hL0.le
    have h3 : 8 * n ^ 2 / σ / twoPowL ≤ 8 * n ^ 2 / σ / n :=
      div_le_div_of_nonneg_left (by positivity) hn hL
    have h4 : 8 * n ^ 2 / σ / n = 8 * n / σ := by field_simp
    linarith
  · have : σ ^ 2 * (8 * n ^ 2 / σ) = 8 * σ * n ^ 2 := by field_simp
    rw [this]
    have : σ * n ^ 2 ≤ n * n ^ 2 := mul_le_mul_of_nonneg_right hσn (by positivity)
    nlinarith

/-- **Theorem II, the exponents**: `2 − 0.0055 = 1.9945`, `2 − 0.0035 = 1.9965`;
`n^{1.9945}(log n)^8 = O(n^{1.99451})`, `n^{1.9965}(log n)^8 = O(n^{1.99651})`, and the search
version's `(log n)^9` is absorbed in the same way. -/
theorem staged_exponents :
    (2 : ℝ) - 0.0055 = 1.9945 ∧ (2 : ℝ) - 0.0035 = 1.9965 ∧
    ((fun x : ℝ => x ^ (1.9945 : ℝ) * Real.log x ^ (8 : ℝ)) =O[Filter.atTop]
      fun x => x ^ (1.99451 : ℝ)) ∧
    ((fun x : ℝ => x ^ (1.9965 : ℝ) * Real.log x ^ (8 : ℝ)) =O[Filter.atTop]
      fun x => x ^ (1.99651 : ℝ)) ∧
    ((fun x : ℝ => x ^ (1.9945 : ℝ) * Real.log x ^ (9 : ℝ)) =O[Filter.atTop]
      fun x => x ^ (1.99451 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, isBigO_rpow_mul_log _ _ _ (by norm_num),
    isBigO_rpow_mul_log _ _ _ (by norm_num), isBigO_rpow_mul_log _ _ _ (by norm_num)⟩

/-! ### Theorem III (§5) -/

/-- **§5, parameters**: `Λ := 8e`, `σ := ⌊√(n^ε/Λ)⌋`, `q := ⌈log₂(2eσ)⌉ + 1`. For `σ ≥ 1`:
`2^{q-1} ≥ 2eσ`, `2^q < Λσ`, `q ≥ 3`, `Λσ² ≤ n^ε`; hence `e 2^{-q} σ ≤ 1/4` (the halving of
(a)) and `e 2^{-(q-1)} σ ≤ 1/2` (Lemma III.3). -/
theorem triangle_params (ε : ℝ) (hε : 0 < ε) (n : ℕ) :
    let Λ := 8 * exp 1
    let σ := ⌊Real.sqrt ((n : ℝ) ^ ε / Λ)⌋₊
    let q := ⌈logb 2 (2 * exp 1 * σ)⌉₊ + 1
    1 ≤ σ →
    2 * exp 1 * σ ≤ (2 : ℝ) ^ (q - 1) ∧ (2 : ℝ) ^ q < Λ * σ ∧ 3 ≤ q ∧
    Λ * (σ : ℝ) ^ 2 ≤ (n : ℝ) ^ ε ∧
    exp 1 * (2 : ℝ)⁻¹ ^ q * σ ≤ 1 / 4 ∧ exp 1 * (2 : ℝ)⁻¹ ^ (q - 1) * σ ≤ 1 / 2 := by
  dsimp only
  intro hσ1
  set a := (n : ℝ) ^ ε / (8 * exp 1) with ha
  set σ := ⌊Real.sqrt a⌋₊ with hσdef
  have he := Real.exp_one_gt_d9
  have hσR : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  have hσa : (σ : ℝ) ≤ Real.sqrt a := Nat.floor_le (Real.sqrt_nonneg _)
  have ha0 : 0 ≤ a := div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity)
  have hσ2 : (σ : ℝ) ^ 2 ≤ a := by
    have := pow_le_pow_left₀ (by positivity) hσa 2
    rwa [Real.sq_sqrt ha0] at this
  have hΛ : 8 * exp 1 * (σ : ℝ) ^ 2 ≤ (n : ℝ) ^ ε := by
    rw [ha, le_div_iff₀ (by positivity)] at hσ2; linarith
  have hx1 : 1 ≤ 2 * exp 1 * (σ : ℝ) := by nlinarith
  obtain ⟨h1, h2⟩ := ceil_logb_spec _ hx1
  set m := ⌈logb 2 (2 * exp 1 * (σ : ℝ))⌉₊ with hm
  have hsub : m + 1 - 1 = m := by omega
  have hpm : (0 : ℝ) < 2 ^ m := by positivity
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    have : (2 : ℝ) ^ m ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  rw [hsub]
  refine ⟨h1, ?_, by omega, hΛ, ?_, ?_⟩
  · rw [pow_succ]; linarith
  · rw [inv_pow, pow_succ]
    have : exp 1 * (2 ^ m * 2)⁻¹ * (σ : ℝ) = exp 1 * σ / (2 ^ m * 2) := by ring
    rw [this, div_le_iff₀ (by positivity)]; linarith
  · rw [inv_pow]
    have : exp 1 * (2 ^ m)⁻¹ * (σ : ℝ) = exp 1 * σ / 2 ^ m := by ring
    rw [this, div_le_iff₀ hpm]; linarith

/-- **Lemma III.1, the cost of the calls of one piece**: with `t = 2^l`, `D = σt`,
`1 ≤ t < Λσ`, `1 ≤ σ`, `1 ≤ Λ`, `0 ≤ γ ≤ 1/2`: `(t + 2√(σt)) (σt)^{-γ} ≤ 3Λσ^{1-2γ}` (both
cases `t ≤ σ` and `σ < t`). -/
theorem triangle_call_cost (γ Λ σ t : ℝ) (hγ : 0 ≤ γ) (hγ2 : γ ≤ 1 / 2) (hΛ : 1 ≤ Λ)
    (hσ : 1 ≤ σ) (ht : 1 ≤ t) (htΛ : t < Λ * σ) :
    (t + 2 * Real.sqrt (σ * t)) * (σ * t) ^ (-γ) ≤ 3 * Λ * σ ^ (1 - 2 * γ) := by
  have hσ0 : 0 < σ := by linarith
  have ht0 : 0 < t := by linarith
  have hΛ0 : 0 < Λ := by linarith
  have hD0 : 0 < σ * t := by positivity
  have hb : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  have hs : 0 ≤ Real.log σ := Real.log_nonneg hσ
  have hlt : Real.log t ≤ Real.log Λ + Real.log σ := by
    have := Real.log_le_log ht0 htΛ.le
    rwa [Real.log_mul hΛ0.ne' hσ0.ne'] at this
  have hDm : 0 < (σ * t) ^ (-γ) := Real.rpow_pos_of_pos hD0 _
  have hσm : 0 < σ ^ (1 - 2 * γ) := Real.rpow_pos_of_pos hσ0 _
  have hT1 : t * (σ * t) ^ (-γ) ≤ Λ * σ ^ (1 - 2 * γ) := by
    apply le_of_log_le' (by positivity) (by positivity)
    rw [Real.log_mul ht0.ne' hDm.ne', Real.log_rpow hD0, Real.log_mul hσ0.ne' ht0.ne',
      Real.log_mul hΛ0.ne' hσm.ne', Real.log_rpow hσ0]
    nlinarith [mul_le_mul_of_nonneg_left hlt (by linarith : (0 : ℝ) ≤ 1 - γ), mul_nonneg hγ hb]
  have hT2 : Real.sqrt (σ * t) * (σ * t) ^ (-γ) ≤ Λ * σ ^ (1 - 2 * γ) := by
    have hsq : 0 < Real.sqrt (σ * t) := Real.sqrt_pos.2 hD0
    apply le_of_log_le' (by positivity) (by positivity)
    rw [Real.log_mul hsq.ne' hDm.ne', Real.log_rpow hD0, Real.log_sqrt hD0.le,
      Real.log_mul hσ0.ne' ht0.ne', Real.log_mul hΛ0.ne' hσm.ne', Real.log_rpow hσ0]
    nlinarith [mul_le_mul_of_nonneg_left hlt (by linarith : (0 : ℝ) ≤ 1 / 2 - γ),
      mul_nonneg hγ hb, mul_nonneg hγ hs]
  have e : (t + 2 * Real.sqrt (σ * t)) * (σ * t) ^ (-γ) =
      t * (σ * t) ^ (-γ) + 2 * (Real.sqrt (σ * t) * (σ * t) ^ (-γ)) := by ring
  rw [e]; linarith

/-- **Lemma III.1, the pieces**: `h := ⌈n/σ⌉ ≤ 2n/σ` for `1 ≤ σ ≤ n`, and
`h · 3Λσ^{1−2γ} n² ≤ 6Λ n³ σ^{-2γ}`. -/
theorem triangle_pieces (n σ Λ γ : ℝ) (hσ : 1 ≤ σ) (hσn : σ ≤ n) (hΛ : 0 ≤ Λ) :
    (⌈n / σ⌉₊ : ℝ) ≤ 2 * n / σ ∧
    (2 * n / σ) * (3 * Λ * σ ^ (1 - 2 * γ) * n ^ 2) = 6 * Λ * n ^ 3 * σ ^ (-(2 * γ)) := by
  have hσ0 : 0 < σ := by linarith
  constructor
  · have h0 : 0 ≤ n / σ := div_nonneg (by linarith) hσ0.le
    have h1 := Nat.ceil_lt_add_one h0
    have h2 : 1 ≤ n / σ := by rw [le_div_iff₀ hσ0]; linarith
    have h3 : 2 * n / σ = 2 * (n / σ) := by ring
    linarith
  · have : σ ^ (1 - 2 * γ) = σ * σ ^ (-(2 * γ)) := by
      rw [sub_eq_add_neg, Real.rpow_add hσ0, Real.rpow_one]
    rw [this]; field_simp; ring

/-- **Theorem III (a), the count of evaluations**: `L ≤ 2ℓ`, `q ≤ 4ℓ`, `d' ≤ c'ℓ`,
`|E| ≤ 4(d'q)²` give `L q |E| ≤ 512 c'² ℓ⁶`. -/
theorem triangle_evals_le (c ℓ L q d E : ℝ) (hℓ : 0 ≤ ℓ) (hL0 : 0 ≤ L) (hL : L ≤ 2 * ℓ)
    (hq0 : 0 ≤ q) (hq : q ≤ 4 * ℓ) (hd0 : 0 ≤ d) (hd : d ≤ c * ℓ) (hE0 : 0 ≤ E)
    (hE : E ≤ 4 * (d * q) ^ 2) :
    L * q * E ≤ 512 * c ^ 2 * ℓ ^ 6 := by
  have hdq : d * q ≤ c * ℓ * (4 * ℓ) := mul_le_mul hd hq hq0 (by nlinarith)
  have hdq0 : 0 ≤ d * q := mul_nonneg hd0 hq0
  have hE' : E ≤ 64 * c ^ 2 * ℓ ^ 4 := by
    have : (d * q) ^ 2 ≤ (c * ℓ * (4 * ℓ)) ^ 2 := pow_le_pow_left₀ hdq0 hdq 2
    nlinarith
  calc L * q * E ≤ (2 * ℓ) * (4 * ℓ) * (64 * c ^ 2 * ℓ ^ 4) := by
        apply mul_le_mul _ hE' hE0 (by positivity)
        exact mul_le_mul hL hq hq0 (by linarith)
    _ = 512 * c ^ 2 * ℓ ^ 6 := by ring

/-- **Theorem III, the exponents**: `3 − 0.0055 = 2.9945`, `3 − 0.0035 = 2.9965`,
`n^{2.9945}(log n)^6 = O(n^{2.99451})`. -/
theorem triangle_exponents :
    (3 : ℝ) - 0.0055 = 2.9945 ∧ (3 : ℝ) - 0.0035 = 2.9965 ∧
    ((fun x : ℝ => x ^ (2.9945 : ℝ) * Real.log x ^ (6 : ℝ)) =O[Filter.atTop]
      fun x => x ^ (2.99451 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, isBigO_rpow_mul_log _ _ _ (by norm_num)⟩

/-! ### The exponents as functions of `(ε, γ)`, and the two explicit hypotheses

Every algorithmic statement of the Improved files is generic: correctness does not depend on
`(ε, γ)` (the hypothesis `Hyp(ε, γ)` is a running-time statement and enters only the time), and
the parameter lemmas above hold for all `0 < ε, γ ≤ 1/2`. The exponents that the improved write-up
claims for the times (no time is formalized) are the functions below; their values at the paper's Corollary 9.1(b), `Hyp(1/14, 0.077)`,
`εγ = 0.0055`, and at the preprint's Corollary 16, `Hyp(1/18, 0.063)`, `εγ = 0.0035`
(Remark 23 at the preprint's own numbers), are the one-line instances. -/

/-- Exact-XOR-Triangle via the note's reduction (Theorem I (a)): `3 − εγ/2`. -/
noncomputable def expTriangleHalf (ε γ : ℝ) : ℝ := 3 - ε * γ / 2
/-- 3XOR via Convolution-3XOR (Theorem I (c), the note's route): `2 − εγ/4`. -/
noncomputable def expXorNoteRoute (ε γ : ℝ) : ℝ := 2 - ε * γ / 4
/-- 3XOR, direct detection reduction (Theorem I′): `2 − εγ/2`. -/
noncomputable def expXorDirectDetection (ε γ : ℝ) : ℝ := 2 - ε * γ / 2
/-- 3XOR, direct counting reduction (Theorem II): `2 − εγ`. -/
noncomputable def expXorDirectCount (ε γ : ℝ) : ℝ := 2 - ε * γ
/-- Exact-XOR-Triangle, staged (Theorem III): `3 − εγ`. -/
noncomputable def expTriangleFull (ε γ : ℝ) : ℝ := 3 - ε * γ

/-- **Instances at Corollary 9.1(b)**, `(ε, γ) = (1/14, 0.077)`, `εγ = 0.0055`. -/
theorem exponents_cor91b :
    (1 / 14 : ℝ) * 0.077 = 0.0055 ∧
    expTriangleHalf (1 / 14) 0.077 = 2.99725 ∧ expXorNoteRoute (1 / 14) 0.077 = 1.998625 ∧
    expXorDirectDetection (1 / 14) 0.077 = 1.99725 ∧ expXorDirectCount (1 / 14) 0.077 = 1.9945 ∧
    expTriangleFull (1 / 14) 0.077 = 2.9945 := by
  unfold expTriangleHalf expXorNoteRoute expXorDirectDetection expXorDirectCount expTriangleFull
  norm_num

/-- **Instances at the preprint's Corollary 16**, `(ε, γ) = (1/18, 0.063)`, `εγ = 0.0035`:
Remark 23 of arXiv:2610.06783 at the preprint's own numbers (the note's `1.999125`, and the
improvements `1.99825` and `1.9965`). -/
theorem exponents_cor16 :
    (1 / 18 : ℝ) * 0.063 = 0.0035 ∧
    expTriangleHalf (1 / 18) 0.063 = 2.99825 ∧ expXorNoteRoute (1 / 18) 0.063 = 1.999125 ∧
    expXorDirectDetection (1 / 18) 0.063 = 1.99825 ∧ expXorDirectCount (1 / 18) 0.063 = 1.9965 ∧
    expTriangleFull (1 / 18) 0.063 = 2.9965 := by
  unfold expTriangleHalf expXorNoteRoute expXorDirectDetection expXorDirectCount expTriangleFull
  norm_num

/-- The polylogarithmic factors at both instances are absorbed into the rounded exponents of
§1: `n^{e}(log n)^c = O(n^{e'})` for each theorem's `(e, c, e')`. -/
theorem exponents_absorbed :
    ((fun x : ℝ => x ^ expXorDirectDetection (1 / 14) 0.077 * Real.log x ^ (1 : ℝ))
      =O[Filter.atTop] fun x => x ^ (1.99726 : ℝ)) ∧
    ((fun x : ℝ => x ^ expXorDirectDetection (1 / 18) 0.063 * Real.log x ^ (1 : ℝ))
      =O[Filter.atTop] fun x => x ^ (1.99826 : ℝ)) ∧
    ((fun x : ℝ => x ^ expXorDirectCount (1 / 14) 0.077 * Real.log x ^ (8 : ℝ))
      =O[Filter.atTop] fun x => x ^ (1.99451 : ℝ)) ∧
    ((fun x : ℝ => x ^ expXorDirectCount (1 / 18) 0.063 * Real.log x ^ (8 : ℝ))
      =O[Filter.atTop] fun x => x ^ (1.99651 : ℝ)) ∧
    ((fun x : ℝ => x ^ expTriangleFull (1 / 14) 0.077 * Real.log x ^ (6 : ℝ))
      =O[Filter.atTop] fun x => x ^ (2.99451 : ℝ)) ∧
    ((fun x : ℝ => x ^ expXorNoteRoute (1 / 14) 0.077 * Real.log x ^ logb 2 27)
      =O[Filter.atTop] fun x => x ^ (1.99863 : ℝ)) := by
  unfold expXorDirectDetection expXorDirectCount expTriangleFull expXorNoteRoute
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact isBigO_rpow_mul_log _ _ _ (by norm_num)

end Xor.Improved

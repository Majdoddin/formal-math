/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.TimeClaims.Remark23.Definitions
public import ThreeSumApsp.TimeClaims.Sec3.Theorem19

/-!
# Theorem 9 of the note from its Theorem 8 and Corollary 16

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

The note's Theorem 9: "Exact-XOR-Triangle on N vertices per part with weights in F₂^{d'},
d' ≤ c' log N, is solved by a deterministic algorithm in O(N^{3−ε'}) time using [AVW26,
Corollary 26] (via its Corollary 16)".  Its proof is that of Theorem 19 of the paper, with the
parameters `D = ⌊N^{1/18}⌋` and `g = ⌈D^{0.0315}⌉`, and with the selection of the rows of the hash in
place of the choice of the prime: "the selection of h costs O((d' log D)² √D N^{log₂ 7}) =
O(N^{log₂ 7 + 1/36} log⁴ N) = O(N^{2.9}) with Strassen's algorithm".

The deduction reuses the arithmetic of Theorem 19 for the instances, the scans and the building
(`Theorem19.total_corollary_26`, where the term of the prime is non-negative and can be dropped), and
bounds the selection term on its own (`XorClaim.termSelect_le`): `(κ log n)^p √D n^{log₂ 7} ≤
C_p κ^p n^{3−ε'} log n`, because `(log n)^p ≤ C_p n^{0.1}` and `log₂ 7 + 1/36 + 0.1 < 3 − ε'`.
The result keeps `κ^p` (`XorClaim.Theorem_9_explicit`), and the bound for all sizes and all weights
(`XorClaim.exactTriangleUniform_of_explicit`) has the factor `(1 + log u)^p` in place of
`(1 + log u)²`, as `κ ≤ 1 + log u` for `κ = max 1 (log u / log s)`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace XorClaim

/-- `(log n)^p ≤ (10 (p + 1))^p n^{1/10}` for `n ≥ 1`: a power of the logarithm is absorbed by a
small power of `n`. -/
theorem log_pow_le_rpow (p : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    Real.log n ^ p ≤ (10 * ((p : ℝ) + 1)) ^ p * (n : ℝ) ^ (0.1 : ℝ) := by
  set ε : ℝ := 1 / (10 * ((p : ℝ) + 1)) with hε
  have hp0 : (0 : ℝ) < 10 * ((p : ℝ) + 1) := by positivity
  have hε0 : 0 < ε := by positivity
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn
  have hlog := Real.log_le_rpow_div n.cast_nonneg hε0
  have hlog0 := Real.log_natCast_nonneg n
  have hεp : ε * p ≤ 0.1 := by
    rw [hε, div_mul_eq_mul_div, one_mul, div_le_iff₀ hp0]
    nlinarith
  calc Real.log n ^ p ≤ ((n : ℝ) ^ ε / ε) ^ p := pow_le_pow_left₀ hlog0 hlog p
    _ = (10 * ((p : ℝ) + 1)) ^ p * (n : ℝ) ^ (ε * p) := by
        rw [div_pow, Real.rpow_mul n.cast_nonneg, Real.rpow_natCast, hε, one_div_pow,
          div_div_eq_mul_div, div_one, mul_comm]
    _ ≤ (10 * ((p : ℝ) + 1)) ^ p * (n : ℝ) ^ (0.1 : ℝ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hεp) (by positivity)

/-- **Theorem 9 of the note, the selection term**: "the selection of h costs O((d' log D)² √D
N^{log₂ 7}) = O(N^{log₂ 7 + 1/36} log⁴ N) = O(N^{2.9}) with Strassen's algorithm", with the
generous term `(κ log n)^p √D n^{log₂ 7}` of `XorClaim.Theorem_8` at `D = paramD₂₆ n`: it is at most
`C κ^p n^{3−ε'} log n`. -/
theorem termSelect_le (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 16 ^ 18 ≤ n → ∀ {κ : ℝ}, 1 ≤ κ →
      termSelect strassen n (paramD₂₆ n) κ p
        ≤ C * (κ ^ p * ((n : ℝ) ^ (3 - 0.00175 : ℝ) * Real.log n)) := by
  refine ⟨(10 * ((p : ℝ) + 1)) ^ p, by positivity, fun {n} hn {κ} hκ => ?_⟩
  have P := Theorem19.choice_corollary_26 hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  have hn1' : (1 : ℝ) ≤ n := Nat.one_le_cast.2 hn1
  have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1'
  have hlog1 := P.one_le_log
  -- `√D ≤ n^{1/36}`, because `D ≤ n^{1/18}`
  have hsqrt : Real.sqrt (paramD₂₆ n) ≤ (n : ℝ) ^ (1 / 36 : ℝ) := by
    calc Real.sqrt (paramD₂₆ n) ≤ Real.sqrt ((n : ℝ) ^ (1 / 18 : ℝ)) := Real.sqrt_le_sqrt P.le_root
      _ = (n : ℝ) ^ (1 / 36 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul n.cast_nonneg]
          norm_num
  have hexp : (0.1 : ℝ) + (1 / 36 + Real.logb 2 7) ≤ 3 - 0.00175 := by
    linarith [Real.logb_two_seven_lt]
  have hpow : (n : ℝ) ^ (0.1 : ℝ) * ((n : ℝ) ^ (1 / 36 : ℝ) * (n : ℝ) ^ Real.logb 2 7)
      ≤ (n : ℝ) ^ (3 - 0.00175 : ℝ) * Real.log n := by
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    exact (Real.rpow_le_rpow_of_exponent_le hn1' hexp).trans
      (le_mul_of_one_le_right (by positivity) hlog1)
  have hlogp := log_pow_le_rpow p hn1
  have hκp : 0 ≤ κ ^ p := by positivity
  unfold termSelect strassen
  calc (κ * Real.log n) ^ p * Real.sqrt (paramD₂₆ n) * (n : ℝ) ^ Real.logb 2 7
      = κ ^ p * (Real.log n ^ p * (Real.sqrt (paramD₂₆ n) * (n : ℝ) ^ Real.logb 2 7)) := by ring
    _ ≤ κ ^ p * ((10 * ((p : ℝ) + 1)) ^ p * (n : ℝ) ^ (0.1 : ℝ)
          * ((n : ℝ) ^ (1 / 36 : ℝ) * (n : ℝ) ^ Real.logb 2 7)) := by gcongr
    _ = (10 * ((p : ℝ) + 1)) ^ p * (κ ^ p * ((n : ℝ) ^ (0.1 : ℝ)
          * ((n : ℝ) ^ (1 / 36 : ℝ) * (n : ℝ) ^ Real.logb 2 7))) := by ring
    _ ≤ (10 * ((p : ℝ) + 1)) ^ p * (κ ^ p * ((n : ℝ) ^ (3 - 0.00175 : ℝ) * Real.log n)) := by
        gcongr

end XorClaim

/-- **Theorem 9 of the note**, the deduction "By Corollary 16": from `XorClaim.Theorem_8` (with
Strassen's algorithm and `D = ⌊n^{1/18}⌋`, `g = ⌈D^{0.0315}⌉`) and Corollary 16, Exact-XOR-Triangle
in time `O(κ^p n^{3−ε'} log n)` on weights at most `n^κ`.  The instances, the scans and the building
are added up as in Theorem 19 (`Theorem19.total_corollary_26`); the selection term is
`XorClaim.termSelect_le`. -/
theorem Theorem9.xor_explicit_of_theorem_8_corollary_16 (M : DetTimeModel) {p : ℕ} (hp : 1 ≤ p)
    (h8 : XorClaim.Theorem_8 M strassen paramD₂₆ paramG₂₆ p)
    (h16 : Claim.Corollary_16 M) : XorClaim.Theorem_9_explicit M 0.00175 1 p := by
  obtain ⟨C, hC, h8⟩ := h8
  obtain ⟨C₁₆, _, Td, hC₁₆, -, hTd, h16⟩ := h16
  obtain ⟨T, hT, h8⟩ := h8 Td hTd
  obtain ⟨C₀, hC₀, htotal⟩ := Theorem19.total_corollary_26
  obtain ⟨C₁, -, hsel⟩ := XorClaim.termSelect_le p
  refine ⟨C₀ * (2 * C₁₆ + C + C) + C * C₁, T, hT, fun n κ u hn hκ hu => ?_⟩
  -- Step 1: the parameters.
  have P := Theorem19.choice_corollary_26 hn
  have hD16 := P.sixteen_le
  have h8 := h8 n κ u hD16 P.le_n P.one_le_ceil P.ceil_le_sqrt hκ hu
  -- Step 2: one call.
  have hcall := call_cost_corollary_16 (by omega) hC hC₁₆
    (h16 n _ (queryCap n (paramD₂₆ n)) (by omega) P.pow_eighteen_le).2
  -- Step 3: the instances, the scans and the building as in Theorem 19; the prime's term is `≥ 0`.
  have hsum := htotal hn (a := 2 * C₁₆ + C) (b := C) (by positivity) hC hκ
  have hprime : 0 ≤ C * termPrime strassen n (paramD₂₆ n) :=
    mul_nonneg hC (mul_nonneg (strassen_nonneg n) (by positivity))
  -- Step 4: the selection.
  have hs := mul_le_mul_of_nonneg_left (hsel hn hκ) hC
  -- `κ ≤ κ^p`, so everything is `O(κ^p n^{3−ε'} log n)`.
  have hX : 0 ≤ (n : ℝ) ^ (3 - 0.00175 : ℝ) * Real.log n :=
    mul_nonneg (by positivity) (Real.log_natCast_nonneg n)
  have hκp : κ * ((n : ℝ) ^ (3 - 0.00175 : ℝ) * Real.log n)
      ≤ κ ^ p * ((n : ℝ) ^ (3 - 0.00175 : ℝ) * Real.log n) :=
    mul_le_mul_of_nonneg_right (le_self_pow₀ hκ (by omega)) hX
  have hκp' := mul_le_mul_of_nonneg_left hκp
    (mul_nonneg hC₀ (by positivity : (0 : ℝ) ≤ 2 * C₁₆ + C + C))
  have hcall' := mul_le_mul_of_nonneg_left hcall
    (by positivity : (0 : ℝ) ≤ 4 * (n : ℝ) * (paramG₂₆ n : ℝ))
  rw [pow_one]
  linear_combination h8 + hcall' + hsum + hprime + hs + hκp'

/-! ## A bound for all sizes and all bounds on the weights

The same steps as `exactTriangleUniform_of_explicit`, with `κ^p` in place of `κ` and so
`(1 + log u)^p` in place of `(1 + log u)²`. -/

namespace XorClaim

/-- The time `XorClaim.uniformTime` without its constant. -/
private noncomputable abbrev uniformShape (δ : ℝ) (e p : ℕ) (q : SizeBound) : ℝ :=
  (q.s : ℝ) ^ (3 - δ) * (Real.log q.s + 1) ^ e * (1 + logU q.u) ^ p

/-- Each of the three factors of `uniformShape` is at least 1. -/
private theorem one_le_uniformShape {δ : ℝ} (e p : ℕ) (hδ1 : δ ≤ 1) {q : SizeBound}
    (hs : 1 ≤ q.s) : 1 ≤ uniformShape δ e p q :=
  one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (Nat.one_le_cast.2 hs) (by linarith)) (one_le_log_add_one_pow q.s e))
    (one_le_pow₀ (one_le_one_add_logU q.u))

/-- "Smaller instances are solved by brute force": below a fixed size `n₀`, the time
`s³ (1 + log u)` is `O(s^{3−δ} (log s + 1)^e (1 + log u)^p)` for `p ≥ 1`. -/
private theorem dominated_bruteForce {δ : ℝ} (e p n₀ : ℕ) (hp : 1 ≤ p) (hδ0 : 0 ≤ δ) :
    Dominated (fun q : SizeBound => (1 ≤ q.s ∧ 1 ≤ q.u) ∧ q.s < n₀)
      (fun q => (q.s : ℝ) ^ 3 * (1 + logU q.u)) (uniformShape δ e p) := by
  refine .of_le_const_mul (C := (n₀ : ℝ) ^ δ) (by positivity) fun q hq => ?_
  have hlog := one_le_log_add_one_pow q.s e
  have hwords := one_le_one_add_logU q.u
  have hs0 : (0 : ℝ) < q.s := Nat.cast_pos.2 hq.1.1
  have hsplit : (q.s : ℝ) ^ 3 = (q.s : ℝ) ^ δ * (q.s : ℝ) ^ (3 - δ) := by
    rw [← Real.rpow_add hs0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hsmall : (q.s : ℝ) ^ δ ≤ (n₀ : ℝ) ^ δ :=
    Real.rpow_le_rpow hs0.le (Nat.cast_le.2 hq.2.le) hδ0
  have hpow : (1 + logU q.u) ^ 1 ≤ (1 + logU q.u) ^ p := pow_le_pow_right₀ hwords hp
  calc (q.s : ℝ) ^ 3 * (1 + logU q.u)
      = (q.s : ℝ) ^ δ * ((q.s : ℝ) ^ (3 - δ) * 1 * (1 + logU q.u) ^ 1) := by rw [hsplit]; ring
    _ ≤ (n₀ : ℝ) ^ δ * ((q.s : ℝ) ^ (3 - δ) * (Real.log q.s + 1) ^ e * (1 + logU q.u) ^ p) := by
        gcongr

/-- Weights up to `u` are weights up to `s^κ` for `κ = max 1 (log u / log s)`. -/
private theorem le_rpow_max_log_div {s : ℕ} {u : ℝ} (hs : 3 ≤ s) (hu : 1 ≤ u) :
    u ≤ (s : ℝ) ^ max 1 (Real.log u / Real.log s) := by
  have hs0 : (0 : ℝ) < s := Nat.cast_pos.2 (by omega)
  have hlogs : 1 ≤ Real.log s := Real.one_le_log_natCast_of_three_le hs
  calc u = (s : ℝ) ^ (Real.log u / Real.log s) := by
        rw [Real.rpow_def_of_pos hs0, mul_div_cancel₀ _ (by linarith),
          Real.exp_log (zero_lt_one.trans_le hu)]
    _ ≤ (s : ℝ) ^ max 1 (Real.log u / Real.log s) :=
        Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.2 (by omega)) (le_max_right _ _)

/-- The exponent `max 1 (log u / log s)` is at most `1 + log u`. -/
private theorem max_log_div_le {s : ℕ} {u : ℝ} (hs : 3 ≤ s) (hu : 1 ≤ u) :
    max 1 (Real.log u / Real.log s) ≤ 1 + logU u := by
  refine max_le (one_le_one_add_logU u) ?_
  linarith [div_le_self (Real.log_nonneg hu) (Real.one_le_log_natCast_of_three_le hs),
    log_le_logU (zero_lt_one.trans_le hu)]

/-- From the size `16^18` on: the explicit bound with `κ = max 1 (log u / log s)`, so
`κ^p ≤ (1 + log u)^p`. -/
private theorem dominated_explicit {T : ℕ → ℝ → ℝ} {K δ : ℝ} {e p : ℕ}
    (hb : ∀ (n : ℕ) (κ u : ℝ), 16 ^ 18 ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ ^ p * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))) :
    Dominated (fun q : SizeBound => (1 ≤ q.s ∧ 1 ≤ q.u) ∧ ¬ q.s < 16 ^ 18) (fun q => T q.s q.u)
      (uniformShape δ e p) := by
  have h3 : ∀ q : SizeBound, ¬ q.s < 16 ^ 18 → 3 ≤ q.s := fun q hq =>
    (by norm_num : 3 ≤ 16 ^ 18).trans (not_lt.1 hq)
  refine (Dominated.of_exists_const (g := fun q => max 1 (Real.log q.u / Real.log q.s) ^ p *
    ((q.s : ℝ) ^ (3 - δ) * Real.log q.s ^ e)) ⟨K, fun q hq => ?_⟩ fun q _ => ?_).trans
    (.of_le fun q hq => ?_)
  · exact hb q.s _ q.u (not_lt.1 hq.2) (le_max_left _ _) (le_rpow_max_log_div (h3 q hq.2) hq.1.2)
  · have : (0 : ℝ) ≤ max 1 (Real.log q.u / Real.log q.s) := zero_le_one.trans (le_max_left _ _)
    positivity
  · have hκ := max_log_div_le (h3 q hq.2) hq.1.2
    have hlog := Real.log_natCast_nonneg q.s
    have hκ0 : (0 : ℝ) ≤ max 1 (Real.log q.u / Real.log q.s) := zero_le_one.trans (le_max_left _ _)
    calc max 1 (Real.log q.u / Real.log q.s) ^ p * ((q.s : ℝ) ^ (3 - δ) * Real.log q.s ^ e)
        ≤ (1 + logU q.u) ^ p * ((q.s : ℝ) ^ (3 - δ) * (Real.log q.s + 1) ^ e) := by
          gcongr
          · exact pow_nonneg (zero_le_one.trans (one_le_one_add_logU q.u)) p
          · linarith
      _ = uniformShape δ e p q := by ring

/-- From the explicit form of Theorem 9, brute force for small instances and the two closure
properties: Exact-XOR-Triangle in time `K s^{3−δ} (log s + 1)^e (1 + log u)^p` for all `s` and
`u`.  This is `exactTriangleUniform_of_explicit` with `κ^p` in place of `κ`. -/
theorem exactTriangleUniform_of_explicit (M : DetTimeModel) {δ : ℝ} (e : ℕ) {p : ℕ} (hp : 1 ≤ p)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hex : XorClaim.Theorem_9_explicit M δ e p)
    (hbf : Claim.BruteForce M) (hch : Closure.ChooseBySize M)
    (hmono : Closure.MonoExactTriangle M) : XorClaim.ExactTriangleUniform M δ e p := by
  obtain ⟨K, T, hT, hb⟩ := hex
  obtain ⟨C, hbf⟩ := hbf
  obtain ⟨C₀, hch⟩ := hch (16 ^ 18)
  have hshape : ∀ q : SizeBound, 1 ≤ q.s ∧ 1 ≤ q.u → 1 ≤ uniformShape δ e p q := fun q hq =>
    one_le_uniformShape e p hδ1 hq.1
  have hsmall := (dominated_bruteForce e p (16 ^ 18) hp hδ0).const_mul_of_nonneg C fun q _ =>
    mul_nonneg (by positivity) (zero_le_one.trans (one_le_one_add_logU q.u))
  obtain ⟨K', hK'0, hK'⟩ := (Dominated.ite hsmall (dominated_explicit hb) fun q hq =>
    zero_le_one.trans (hshape q hq)).add (.const C₀ hshape)
  refine ⟨1 + K', le_add_of_nonneg_right hK'0,
    hmono _ _ (fun s u hs hu => ?_) (hch _ T hbf hT)⟩
  exact (hK' ⟨s, u⟩ ⟨hs, hu⟩).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
    (zero_le_one.trans (hshape ⟨s, u⟩ ⟨hs, hu⟩)))

/-- Theorem 9 of the note for all sizes and all weights, from Theorem 8 (with Strassen's algorithm
and the parameters of the route through Corollary 26), Corollary 16, brute force and the two closure
properties. -/
theorem exactTriangleUniform_of_theorem_8 (M : DetTimeModel) {p : ℕ} (hp : 1 ≤ p)
    (h8 : XorClaim.Theorem_8 M strassen paramD₂₆ paramG₂₆ p) (h16 : Claim.Corollary_16 M)
    (hbf : Claim.BruteForce M) (hch : Closure.ChooseBySize M)
    (hmono : Closure.MonoExactTriangle M) : XorClaim.ExactTriangleUniform M 0.00175 1 p :=
  exactTriangleUniform_of_explicit M 1 hp (by norm_num) (by norm_num)
    (Theorem9.xor_explicit_of_theorem_8_corollary_16 M hp h8 h16) hbf hch hmono

end XorClaim

end ThreeSumApsp

/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Remark23.Bridge
public import ThreeSumApsp.Util.BinaryPrefixes

/-!
# Remark 23 (3XOR): XOR and inner product of two numbers

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

The machine has no bit operations.  Two routines read the binary digits of two numbers `x, y < 2^Λ`
from the top down, as `bitsRow` of the Chan–He reduction does: the rest of each number is kept at
the top of `Λ` bits, it is doubled, and the digit is 1 if the result reaches `2^Λ`
(`ThreeSumApsp.testBit_iff_shift`).  Neither routine uses the memory.

* xorNat(Λ, 2^Λ, x, y) returns `x ^^^ y`, the number of the vector `x ⊕ y` (`xorNat_meets`).  The
  result is built from the top down: it is doubled in each round, and 1 is added if the two digits
  differ.
* ipNat(Λ, 2^Λ, u, x) returns the inner product `⟨u, x⟩` of the two vectors, 0 or 1
  (`ipNat_meets`): the parity of the number of positions where both digits are 1.

Both take `O(Λ)` steps (`xorNatTime`, `ipNatTime`).
-/

@[expose] public section

namespace Light.Remark23

open ThreeSumApsp ThreeSumApsp.Remark23

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## Facts about digits -/

/-- One more digit of a quotient by a power of two. -/
theorem div_two_pow_step (z ℓ : ℕ) :
    z / 2 ^ ℓ = 2 * (z / 2 ^ (ℓ + 1)) + (if z.testBit ℓ then 1 else 0) := by
  rw [pow_succ, ← Nat.div_div_eq_div_mul, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (z / 2 ^ ℓ) with h | h <;> simp [h] <;> omega

/-- The digit of `x` that a round of the top-down reading finds, in terms of the doubled rest. -/
theorem testBit_eq_of_lt {Λ ℓ : ℕ} (h : ℓ + 1 ≤ Λ) {x : ℕ} (hc : 2 * prefR Λ (ℓ + 1) x < 2 ^ Λ) :
    x.testBit ℓ = false := by
  by_contra hb
  exact (testBit_iff_shift h x).1 (Bool.not_eq_false _ ▸ hb) hc

/-- The digit is 1 if the doubled rest reaches `2^Λ`. -/
theorem testBit_eq_of_not_lt {Λ ℓ : ℕ} (h : ℓ + 1 ≤ Λ) {x : ℕ}
    (hc : ¬ 2 * prefR Λ (ℓ + 1) x < 2 ^ Λ) : x.testBit ℓ = true :=
  (testBit_iff_shift h x).2 hc

/-- The doubled rest, if it stays below `2^Λ`, is the next rest. -/
theorem prefR_of_lt {Λ ℓ : ℕ} (h : ℓ + 1 ≤ Λ) {x : ℕ} (hc : 2 * prefR Λ (ℓ + 1) x < 2 ^ Λ) :
    prefR Λ ℓ x = 2 * prefR Λ (ℓ + 1) x := by
  rw [(pref_step h (x : ℤ)).2, shiftR, if_pos hc]

/-- The doubled rest, less `2^Λ` if it reaches `2^Λ`, is the next rest. -/
theorem prefR_of_not_lt {Λ ℓ : ℕ} (h : ℓ + 1 ≤ Λ) {x : ℕ} (hc : ¬ 2 * prefR Λ (ℓ + 1) x < 2 ^ Λ) :
    prefR Λ ℓ x = 2 * prefR Λ (ℓ + 1) x - 2 ^ Λ := by
  rw [(pref_step h (x : ℤ)).2, shiftR, if_neg hc]

/-- The rest at level 0 is 0. -/
theorem prefR_zero (Λ : ℕ) (z : ℤ) : prefR Λ 0 z = 0 := by
  simp [prefR]

/-! ## xorNat -/

namespace XorNat

/-- The locals of xorNat: the arguments Λ, 2^Λ, x and y (whose locals keep the rests), the result
and the counter. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Pow : ℕ := 1
@[inherit_doc Len] abbrev X : ℕ := 2
@[inherit_doc Len] abbrev Y : ℕ := 3
@[inherit_doc Len] abbrev Z : ℕ := 4
@[inherit_doc Len] abbrev Cnt : ℕ := 5

end XorNat

open XorNat in
/-- One round of xorNat: the rests and the result are doubled; a digit that reaches `2^Λ` is taken
off its rest, and 1 is added to the result if the two digits differ. -/
def xorNatRound : Stmt :=
  .set X (k 2 *' v X) ;;
  .set Y (k 2 *' v Y) ;;
  .set Z (k 2 *' v Z) ;;
  .ite (v X <' v Pow)
    (.ite (v Y <' v Pow) .skip (.set Y (v Y -' v Pow) ;; .set Z (v Z +' k 1)))
    (.set X (v X -' v Pow) ;;
      .ite (v Y <' v Pow) (.set Z (v Z +' k 1)) (.set Y (v Y -' v Pow)))

open XorNat in
/-- xorNat(Λ, 2^Λ, x, y): the XOR `x ^^^ y` of two numbers below `2^Λ`, digit by digit from the
top. -/
def xorNatBody : Stmt :=
  .set Z (k 0) ;;
  .for Cnt (v Len) xorNatRound ;;
  .set Len (v Z)

/-- The time of xorNat. -/
def xorNatTime (Λ : ℕ) : ℕ := 40 * Λ + 12

/-- The state of xorNat before round `t`, with `ℓ + t = Λ`: the rests of x and y at level `ℓ`, and
the digits of `x ^^^ y` from position `ℓ` on. -/
def XorNatInv (μ : ℕ → ℤ) (Λ x y : ℕ) (t : ℕ) (σ : State) : Prop :=
  ∃ ℓ, ℓ + t = Λ ∧ σ = ⟨frame [Λ, 2 ^ Λ, prefR Λ ℓ x, prefR Λ ℓ y, ((x ^^^ y) / 2 ^ ℓ : ℕ), t], μ⟩

/-- The next digit of `x ^^^ y`: 0 if the two digits agree. -/
theorem xor_div_step (x y ℓ : ℕ) :
    (((x ^^^ y) / 2 ^ ℓ : ℕ) : ℤ) =
      2 * (((x ^^^ y) / 2 ^ (ℓ + 1) : ℕ) : ℤ) + (if x.testBit ℓ = y.testBit ℓ then 0 else 1) := by
  rw [div_two_pow_step, Nat.testBit_xor]
  cases x.testBit ℓ <;> cases y.testBit ℓ <;> simp

/-- One round of xorNat reads one more digit of each number. -/
theorem xorNatRound_ends {μ : ℕ → ℤ} {Λ x y t : ℕ} (hx : x < 2 ^ Λ) (hy : y < 2 ^ Λ) (ht : t < Λ)
    (hw : (2 * 2 ^ Λ : ℤ) ≤ lim.word) {σ : State} (hI : XorNatInv μ Λ x y t σ) :
    Ends lim P d xorNatRound σ xorNatRound.blockCost fun σ' =>
      σ'.loc XorNat.Cnt = t ∧
        XorNatInv μ Λ x y (t + 1) { σ' with loc := Function.update σ'.loc XorNat.Cnt ((t : ℤ) + 1) }
    := by
  obtain ⟨ℓ', hℓ, rfl⟩ := hI
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, ℓ' = ℓ + 1 := ⟨ℓ' - 1, by omega⟩
  have hle : ℓ + 1 ≤ Λ := by omega
  have hx0 := prefR_nonneg Λ (ℓ + 1) (x : ℤ)
  have hx1 := prefR_lt hle (x : ℤ)
  have hy0 := prefR_nonneg Λ (ℓ + 1) (y : ℤ)
  have hy1 := prefR_lt hle (y : ℤ)
  have hz : (((x ^^^ y) / 2 ^ (ℓ + 1) : ℕ) : ℤ) < 2 ^ Λ := by
    have h1 : (x ^^^ y) / 2 ^ (ℓ + 1) < 2 ^ Λ :=
      lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.xor_lt_two_pow hx hy)
    exact_mod_cast h1
  have hz0 : (0 : ℤ) ≤ (((x ^^^ y) / 2 ^ (ℓ + 1) : ℕ) : ℤ) := Int.natCast_nonneg _
  have hstep := xor_div_step x y ℓ
  generalize (x ^^^ y) / 2 ^ (ℓ + 1) = z at hz hz0 hstep ⊢
  unfold xorNatRound
  -- X := 2 X ; Y := 2 Y ; Z := 2 Z
  light_set (2 * prefR Λ (ℓ + 1) (x : ℤ))
  light_set (2 * prefR Λ (ℓ + 1) (y : ℤ))
  light_set (2 * ((z : ℕ) : ℤ))
  light_if hcx hcx' : 2 * prefR Λ (ℓ + 1) (x : ℤ) < 2 ^ Λ
  · have hbx := testBit_eq_of_lt hle hcx
    light_if hcy hcy' : 2 * prefR Λ (ℓ + 1) (y : ℤ) < 2 ^ Λ
    · -- both digits 0
      have hby := testBit_eq_of_lt hle hcy
      rw [hbx, hby, if_pos rfl] at hstep
      light_skip
      exact ⟨by simp, ℓ, by omega,
        by simp [update_frame_setLocal, prefR_of_lt hle hcx, prefR_of_lt hle hcy, hstep]⟩
    · -- the digit of y is 1: Y := Y - 2^Λ ; Z := Z + 1
      have hby := testBit_eq_of_not_lt hle hcy'
      rw [hbx, hby, if_neg (by decide)] at hstep
      light_set (2 * prefR Λ (ℓ + 1) (y : ℤ) - 2 ^ Λ)
      light_set (2 * ((z : ℕ) : ℤ) + 1)
      exact ⟨by simp, ℓ, by omega,
        by simp [update_frame_setLocal, prefR_of_lt hle hcx, prefR_of_not_lt hle hcy', hstep]⟩
  · -- the digit of x is 1: X := X - 2^Λ
    have hbx := testBit_eq_of_not_lt hle hcx'
    light_set (2 * prefR Λ (ℓ + 1) (x : ℤ) - 2 ^ Λ)
    light_if hcy hcy' : 2 * prefR Λ (ℓ + 1) (y : ℤ) < 2 ^ Λ
    · -- the digit of y is 0: Z := Z + 1
      have hby := testBit_eq_of_lt hle hcy
      rw [hbx, hby, if_neg (by decide)] at hstep
      light_set (2 * ((z : ℕ) : ℤ) + 1)
      exact ⟨by simp, ℓ, by omega,
        by simp [update_frame_setLocal, prefR_of_not_lt hle hcx', prefR_of_lt hle hcy, hstep]⟩
    · -- both digits 1: Y := Y - 2^Λ
      have hby := testBit_eq_of_not_lt hle hcy'
      rw [hbx, hby, if_pos rfl] at hstep
      light_set (2 * prefR Λ (ℓ + 1) (y : ℤ) - 2 ^ Λ)
      exact ⟨by simp, ℓ, by omega,
        by simp [update_frame_setLocal, prefR_of_not_lt hle hcx', prefR_of_not_lt hle hcy', hstep]⟩

/-- The body of xorNat computes `x ^^^ y` and writes no cell. -/
theorem xorNat_ends {μ : ℕ → ℤ} {Λ x y : ℕ} (hx : x < 2 ^ Λ) (hy : y < 2 ^ Λ)
    (hw : (2 * 2 ^ Λ : ℤ) ≤ lim.word) :
    Ends lim P d xorNatBody ⟨frame [(Λ : ℤ), 2 ^ Λ, x, y], μ⟩ (xorNatTime Λ) fun σ' =>
      σ'.loc 0 = ((x ^^^ y : ℕ) : ℤ) ∧ σ'.mem = μ := by
  have hΛ : (Λ : ℤ) < 2 ^ Λ := by exact_mod_cast Nat.lt_two_pow_self
  have hxy := Nat.xor_lt_two_pow hx hy
  have hx' : (x : ℤ) < 2 ^ Λ := by exact_mod_cast hx
  have hy' : (y : ℤ) < 2 ^ Λ := by exact_mod_cast hy
  unfold xorNatBody xorNatTime
  -- Z := 0
  light_set (0 : ℕ)
  -- for Cnt < Λ
  refine Ends.next _ (Ends.for (XorNatInv μ Λ x y) Λ xorNatRound.blockCost ?start ?round ?done
    ?bound (hT := le_rfl)) (by light_time [xorNatRound])
  case start =>
    exact ⟨Λ, by omega, by simp [update_frame_setLocal, prefR_start (Int.natCast_nonneg x) hx',
      prefR_start (Int.natCast_nonneg y) hy', Nat.div_eq_of_lt hxy]⟩
  case round => exact fun t σ ht _ hI => xorNatRound_ends hx hy ht hw hI
  case bound =>
    rintro t σ - - ⟨ℓ, -, rfl⟩
    light_side
  case done =>
    rintro σ - ⟨ℓ, hℓ, rfl⟩
    obtain rfl : ℓ = 0 := by omega
    -- result := Z
    light_set ((x ^^^ y : ℕ) : ℤ) using xorNatRound
    exact ⟨by simp, rfl⟩

/-- **xorNat(Λ, 2^Λ, x, y)** returns `x ^^^ y`, the number of the vector `x ⊕ y`
(`toVec_xor`), for `x, y < 2^Λ`, and writes no cell. -/
theorem xorNat_meets {p : ℕ} (hp : P[p]? = some xorNatBody) {μ : ℕ → ℤ} {Λ x y : ℕ}
    (hx : x < 2 ^ Λ) (hy : y < 2 ^ Λ) (hw : (2 * 2 ^ Λ : ℤ) ≤ lim.word) :
    Meets lim P p d [(Λ : ℤ), 2 ^ Λ, x, y] μ (xorNatTime Λ) fun r μ' =>
      r = ((x ^^^ y : ℕ) : ℤ) ∧ μ' = μ :=
  .of_body hp (xorNat_ends hx hy hw)

/-! ## ipNat -/

/-- The inner product of the coordinates `ℓ, …, Λ − 1`. -/
def dotFrom (u x ℓ Λ : ℕ) : ZMod 2 := ∑ β ∈ Finset.Ico ℓ Λ, bitF u β * bitF x β

/-- One more coordinate. -/
theorem dotFrom_step {u x ℓ Λ : ℕ} (h : ℓ < Λ) :
    dotFrom u x ℓ Λ = bitF u ℓ * bitF x ℓ + dotFrom u x (ℓ + 1) Λ :=
  Finset.sum_eq_sum_Ico_succ_bot h _

/-- All coordinates: the inner product of the two vectors. -/
theorem dotFrom_zero (u x Λ : ℕ) : dotFrom u x 0 Λ = toVec Λ u ⬝ᵥ toVec Λ x := by
  rw [dotFrom, ← Finset.range_eq_Ico, toVec_dotProduct]

/-- No coordinate. -/
theorem dotFrom_self (u x Λ : ℕ) : dotFrom u x Λ Λ = 0 := by
  simp [dotFrom]

namespace IpNat

/-- The locals of ipNat: the arguments Λ, 2^Λ, u and x (whose locals keep the rests), the result
and the counter. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Pow : ℕ := 1
@[inherit_doc Len] abbrev X : ℕ := 2
@[inherit_doc Len] abbrev Y : ℕ := 3
@[inherit_doc Len] abbrev Z : ℕ := 4
@[inherit_doc Len] abbrev Cnt : ℕ := 5

end IpNat

open IpNat in
/-- One round of ipNat: the rests are doubled; a digit that reaches `2^Λ` is taken off its rest,
and the result changes from `v` to `1 − v` if both digits are 1. -/
def ipNatRound : Stmt :=
  .set X (k 2 *' v X) ;;
  .set Y (k 2 *' v Y) ;;
  .ite (v X <' v Pow)
    (.ite (v Y <' v Pow) .skip (.set Y (v Y -' v Pow)))
    (.set X (v X -' v Pow) ;;
      .ite (v Y <' v Pow) .skip (.set Y (v Y -' v Pow) ;; .set Z (k 1 -' v Z)))

open IpNat in
/-- ipNat(Λ, 2^Λ, u, x): the inner product `⟨u, x⟩` of two vectors given as numbers below `2^Λ`,
digit by digit from the top. -/
def ipNatBody : Stmt :=
  .set Z (k 0) ;;
  .for Cnt (v Len) ipNatRound ;;
  .set Len (v Z)

/-- The time of ipNat. -/
def ipNatTime (Λ : ℕ) : ℕ := 40 * Λ + 12

/-- The state of ipNat before round `t`, with `ℓ + t = Λ`: the rests of u and x at level `ℓ`, and
the inner product of the coordinates from `ℓ` on. -/
def IpNatInv (μ : ℕ → ℤ) (Λ u x : ℕ) (t : ℕ) (σ : State) : Prop :=
  ∃ ℓ, ℓ + t = Λ ∧
    σ = ⟨frame [Λ, 2 ^ Λ, prefR Λ ℓ u, prefR Λ ℓ x, ((dotFrom u x ℓ Λ).val : ℤ), t], μ⟩

/-- One round of ipNat reads one more digit of each number. -/
theorem ipNatRound_ends {μ : ℕ → ℤ} {Λ u x t : ℕ} (ht : t < Λ)
    (hw : (2 * 2 ^ Λ : ℤ) ≤ lim.word) {σ : State} (hI : IpNatInv μ Λ u x t σ) :
    Ends lim P d ipNatRound σ ipNatRound.blockCost fun σ' =>
      σ'.loc IpNat.Cnt = t ∧
        IpNatInv μ Λ u x (t + 1) { σ' with loc := Function.update σ'.loc IpNat.Cnt ((t : ℤ) + 1) }
    := by
  obtain ⟨ℓ', hℓ, rfl⟩ := hI
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, ℓ' = ℓ + 1 := ⟨ℓ' - 1, by omega⟩
  have hle : ℓ + 1 ≤ Λ := by omega
  have hx0 := prefR_nonneg Λ (ℓ + 1) (u : ℤ)
  have hx1 := prefR_lt hle (u : ℤ)
  have hy0 := prefR_nonneg Λ (ℓ + 1) (x : ℤ)
  have hy1 := prefR_lt hle (x : ℤ)
  have hstep := dotFrom_step (u := u) (x := x) (show ℓ < Λ by omega)
  have hv := ZMod.val_lt (dotFrom u x (ℓ + 1) Λ)
  generalize dotFrom u x (ℓ + 1) Λ = s at hstep hv ⊢
  have hv' : ((s.val : ℕ) : ℤ) < 2 := by exact_mod_cast hv
  generalize hws : ((s.val : ℕ) : ℤ) = w at hv' ⊢
  have hw0 : 0 ≤ w := hws ▸ Int.natCast_nonneg _
  unfold ipNatRound
  -- X := 2 X ; Y := 2 Y
  light_set (2 * prefR Λ (ℓ + 1) (u : ℤ))
  light_set (2 * prefR Λ (ℓ + 1) (x : ℤ))
  light_if hcx hcx' : 2 * prefR Λ (ℓ + 1) (u : ℤ) < 2 ^ Λ
  · have hbx := testBit_eq_of_lt hle hcx
    have hkey : (((dotFrom u x ℓ Λ).val : ℕ) : ℤ) = w := by
      rw [← hws]
      simp [hstep, bitF, hbx]
    light_if hcy hcy' : 2 * prefR Λ (ℓ + 1) (x : ℤ) < 2 ^ Λ
    · light_skip
      exact ⟨by simp, ℓ, by omega, by
        rw [hkey]
        simp [update_frame_setLocal, prefR_of_lt hle hcx, prefR_of_lt hle hcy]⟩
    · -- Y := Y - 2^Λ
      light_set (2 * prefR Λ (ℓ + 1) (x : ℤ) - 2 ^ Λ)
      exact ⟨by simp, ℓ, by omega, by
        rw [hkey]
        simp [update_frame_setLocal, prefR_of_lt hle hcx, prefR_of_not_lt hle hcy']⟩
  · -- X := X - 2^Λ
    have hbx := testBit_eq_of_not_lt hle hcx'
    light_set (2 * prefR Λ (ℓ + 1) (u : ℤ) - 2 ^ Λ)
    light_if hcy hcy' : 2 * prefR Λ (ℓ + 1) (x : ℤ) < 2 ^ Λ
    · have hby := testBit_eq_of_lt hle hcy
      have hkey : (((dotFrom u x ℓ Λ).val : ℕ) : ℤ) = w := by
        rw [← hws]
        simp [hstep, bitF, hby]
      light_skip
      exact ⟨by simp, ℓ, by omega, by
        rw [hkey]
        simp [update_frame_setLocal, prefR_of_not_lt hle hcx', prefR_of_lt hle hcy]⟩
    · -- both digits 1: Y := Y - 2^Λ ; Z := 1 - Z
      have hby := testBit_eq_of_not_lt hle hcy'
      have hkey : (((dotFrom u x ℓ Λ).val : ℕ) : ℤ) = 1 - w := by
        rw [← hws, ← val_one_add]
        simp [hstep, bitF, hbx, hby]
      light_set (2 * prefR Λ (ℓ + 1) (x : ℤ) - 2 ^ Λ)
      light_set (1 - w)
      exact ⟨by simp, ℓ, by omega, by
        rw [hkey]
        simp [update_frame_setLocal, prefR_of_not_lt hle hcx', prefR_of_not_lt hle hcy']⟩

/-- The body of ipNat computes the inner product and writes no cell. -/
theorem ipNat_ends {μ : ℕ → ℤ} {Λ u x : ℕ} (hu : u < 2 ^ Λ) (hx : x < 2 ^ Λ)
    (hw : (2 * 2 ^ Λ : ℤ) ≤ lim.word) :
    Ends lim P d ipNatBody ⟨frame [(Λ : ℤ), 2 ^ Λ, u, x], μ⟩ (ipNatTime Λ) fun σ' =>
      σ'.loc 0 = (((toVec Λ u ⬝ᵥ toVec Λ x).val : ℕ) : ℤ) ∧ σ'.mem = μ := by
  have hΛ : (Λ : ℤ) < 2 ^ Λ := by exact_mod_cast Nat.lt_two_pow_self
  have hu' : (u : ℤ) < 2 ^ Λ := by exact_mod_cast hu
  have hx' : (x : ℤ) < 2 ^ Λ := by exact_mod_cast hx
  have hv := ZMod.val_lt (toVec Λ u ⬝ᵥ toVec Λ x)
  have hv' : (((toVec Λ u ⬝ᵥ toVec Λ x).val : ℕ) : ℤ) < 2 := by exact_mod_cast hv
  unfold ipNatBody ipNatTime
  -- Z := 0
  light_set (0 : ℕ)
  -- for Cnt < Λ
  refine Ends.next _ (Ends.for (IpNatInv μ Λ u x) Λ ipNatRound.blockCost ?start ?round ?done
    ?bound (hT := le_rfl)) (by light_time [ipNatRound])
  case start =>
    exact ⟨Λ, by omega, by simp [update_frame_setLocal, prefR_start (Int.natCast_nonneg u) hu',
      prefR_start (Int.natCast_nonneg x) hx', dotFrom_self]⟩
  case round => exact fun t σ ht _ hI => ipNatRound_ends ht hw hI
  case bound =>
    rintro t σ - - ⟨ℓ, -, rfl⟩
    light_side
  case done =>
    rintro σ - ⟨ℓ, hℓ, rfl⟩
    obtain rfl : ℓ = 0 := by omega
    -- result := Z
    light_set (((toVec Λ u ⬝ᵥ toVec Λ x).val : ℕ) : ℤ) using ipNatRound, dotFrom_zero
    exact ⟨by simp, rfl⟩

/-- **ipNat(Λ, 2^Λ, u, x)** returns the inner product `⟨u, x⟩ ∈ F₂` of the vectors of two numbers
below `2^Λ`, as 0 or 1, and writes no cell. -/
theorem ipNat_meets {p : ℕ} (hp : P[p]? = some ipNatBody) {μ : ℕ → ℤ} {Λ u x : ℕ}
    (hu : u < 2 ^ Λ) (hx : x < 2 ^ Λ) (hw : (2 * 2 ^ Λ : ℤ) ≤ lim.word) :
    Meets lim P p d [(Λ : ℤ), 2 ^ Λ, u, x] μ (ipNatTime Λ) fun r μ' =>
      r = (((toVec Λ u ⬝ᵥ toVec Λ x).val : ℕ) : ℤ) ∧ μ' = μ :=
  .of_body hp (ipNat_ends hu hx hw)

end Light.Remark23

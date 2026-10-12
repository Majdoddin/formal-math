/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Remark23.Bridge
public import ThreeSumApsp.Util.Flag

/-!
# Remark 23 (3XOR): operations on rows of digits

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

A vector of `F^Λ` may also be held as a row of `Λ` cells, digit `β` in cell `β`
(`digitRow Λ z`, written by vbits).  Four routines work on such rows, each in `O(Λ)` steps.

* vxor(Λ, a, b, out) writes the row of `x ^^^ y` to `out` (`vxor_meets`): a cell is 0 if the two
  digits agree and 1 if not.  This is the note's `x ⊕ y` (`toVec_xor`).
* xor3Zero(Λ, a, b, c) returns 1 if `x ⊕ y ⊕ z = 0` and 0 if not (`xor3Zero_meets`): the three
  digits at each position must have an even sum, 0 or 2.
* ipBit(Λ, a, b) returns the inner product `⟨u, x⟩` as 0 or 1 (`ipBit_meets`): the parity of the
  number of positions at which both cells hold 1.
* ofBits(Λ, a) returns the value of a row of zeros and ones, the lowest digit first, by Horner's
  rule from the top (`ofBits_meets`); for the row of `z` this is `z mod 2^Λ` (`rowVal_digitRow`).
-/

@[expose] public section

namespace Light.Remark23

open ThreeSumApsp ThreeSumApsp.Remark23

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The cell of digit `β` of the row of `z`. -/
theorem digit_of_seg {μ : ℕ → ℤ} {a Λ z β : ℕ} (h : Seg μ a (digitRow Λ z)) (hβ : β < Λ) :
    μ (a + β) = if z.testBit β then 1 else 0 := by
  rw [h.get (by simpa using hβ), getElem_digitRow]

/-! ## vxor -/

namespace VXor

/-- The locals of vxor: the arguments Λ, a, b, out, and the counter. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev A : ℕ := 1
@[inherit_doc Len] abbrev B : ℕ := 2
@[inherit_doc Len] abbrev Out : ℕ := 3
@[inherit_doc Len] abbrev Idx : ℕ := 4

end VXor

open VXor in
/-- One round of vxor: the digit of the XOR is 0 if the two digits agree. -/
def vxorRound : Stmt :=
  .ite (M (v A +' v Idx) =' M (v B +' v Idx))
    (.store (v Out +' v Idx) (k 0)) (.store (v Out +' v Idx) (k 1))

open VXor in
/-- vxor(Λ, a, b, out): the row of the XOR of the rows at a and b, to out. -/
def vxorBody : Stmt :=
  .for Idx (v Len) vxorRound

/-- The time of vxor. -/
def vxorTime (Λ : ℕ) : ℕ := 30 * Λ + 10

/-- Two equal digits give the digit 0 of the XOR. -/
theorem testBit_xor_of_eq {x y β : ℕ}
    (h : ((if x.testBit β then 1 else 0 : ℤ) = if y.testBit β then 1 else 0)) :
    (x ^^^ y).testBit β = false := by
  rw [Nat.testBit_xor]
  cases hx : x.testBit β <;> cases hy : y.testBit β <;> simp_all

/-- Two different digits give the digit 1 of the XOR. -/
theorem testBit_xor_of_ne {x y β : ℕ}
    (h : ¬ ((if x.testBit β then 1 else 0 : ℤ) = if y.testBit β then 1 else 0)) :
    (x ^^^ y).testBit β = true := by
  rw [Nat.testBit_xor]
  cases hx : x.testBit β <;> cases hy : y.testBit β <;> simp_all

/-- What vxor writes after `j` rounds. -/
def VXorInv (μ : ℕ → ℤ) (out Λ x y : ℕ) (j : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ β < j, μ' (out + β) = if (x ^^^ y).testBit β then 1 else 0) ∧ SameOutside μ μ' out Λ

/-- **vxor(Λ, a, b, out)** writes the row of `x ^^^ y` to the `Λ` cells from `out` and changes no
other cell, if the rows of `x` and `y` stand at `a` and `b`. -/
theorem vxor_meets {p : ℕ} (hp : P[p]? = some vxorBody) {μ : ℕ → ℤ} {Λ a b out x y : ℕ}
    (ha : Seg μ a (digitRow Λ x)) (hb : Seg μ b (digitRow Λ y))
    (hapa : Apart a Λ out Λ) (hapb : Apart b Λ out Λ)
    (hsa : a + Λ ≤ lim.space) (hsb : b + Λ ≤ lim.space) (hso : out + Λ ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hc : (2 : ℤ) ≤ lim.word) :
    Meets lim P p d [(Λ : ℤ), a, b, out] μ (vxorTime Λ) fun _ μ' =>
      Seg μ' out (digitRow Λ (x ^^^ y)) ∧ SameOutside μ μ' out Λ := by
  refine Meets.of_body hp ?_
  unfold vxorBody vxorTime
  refine Ends.forFrame (VXorInv μ out Λ x y) Λ ⟨fun β hβ => absurd hβ (by omega), .refl⟩ ?round
    ?done (hT := by light_time [vxorRound])
  case done =>
    rintro μ' ⟨hdig, hsame⟩
    exact ⟨fun β hβ => by rw [getElem_digitRow]; exact hdig β (by simpa using hβ), hsame⟩
  case round =>
    rintro j μ' hj ⟨hdig, hsame⟩
    have hra : μ' (a + j) = if x.testBit j then 1 else 0 := by
      rw [hsame _ (by omega)]
      exact digit_of_seg ha hj
    have hrb : μ' (b + j) = if y.testBit j then 1 else 0 := by
      rw [hsame _ (by omega)]
      exact digit_of_seg hb hj
    unfold vxorRound
    light_if h₁ h₂ : μ' (a + j) = μ' (b + j)
    · rw [hra, hrb] at h₁
      have h₁ := testBit_xor_of_eq h₁
      light_store (out + j) (0 : ℕ)
      refine ⟨rfl, fun β hβ => ?_, hsame.write (by omega) _⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hβ with hβ | rfl
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hdig β hβ
      · simp [h₁]
    · rw [hra, hrb] at h₂
      have h₂ := testBit_xor_of_ne h₂
      light_store (out + j) (1 : ℕ)
      refine ⟨rfl, fun β hβ => ?_, hsame.write (by omega) _⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hβ with hβ | rfl
      · dsimp only
        rw [Function.update_of_ne (by omega)]
        exact hdig β hβ
      · simp [h₂]

/-! ## xor3Zero -/

/-- A number below `2^Λ` is 0 exactly if its `Λ` lowest digits are. -/
theorem forall_testBit_iff {Λ w : ℕ} (hw : w < 2 ^ Λ) :
    (∀ β < Λ, w.testBit β = false) ↔ w = 0 := by
  constructor
  · intro h
    refine Nat.eq_of_testBit_eq fun β => ?_
    rw [Nat.zero_testBit]
    by_cases hβ : β < Λ
    · exact h β hβ
    · exact Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by norm_num) (by omega)))
  · rintro rfl β _
    exact Nat.zero_testBit β

/-- The digit of the XOR of three numbers is 1 exactly if the sum of the three digits is odd. -/
theorem testBit_xor3_iff (x y z β : ℕ) :
    (x ^^^ y ^^^ z).testBit β = true ↔
      ((if x.testBit β then 1 else 0) + (if y.testBit β then 1 else 0) +
        (if z.testBit β then 1 else 0) : ℤ) = 1 ∨
      ((if x.testBit β then 1 else 0) + (if y.testBit β then 1 else 0) +
        (if z.testBit β then 1 else 0) : ℤ) = 3 := by
  rw [Nat.testBit_xor, Nat.testBit_xor]
  cases x.testBit β <;> cases y.testBit β <;> cases z.testBit β <;> decide

/-- One more position at which the test holds. -/
theorem flag_forall_succ {Q : ℕ → Prop} {j : ℕ} (h : Q j) :
    flag (∀ β < j + 1, Q β) = flag (∀ β < j, Q β) := by
  refine flag_congr ⟨fun h' β hβ => h' β (by omega), fun h' β hβ => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hβ with hβ | rfl
  · exact h' β hβ
  · exact h

/-- One more position at which the test fails. -/
theorem flag_forall_succ_not {Q : ℕ → Prop} {j : ℕ} (h : ¬ Q j) :
    flag (∀ β < j + 1, Q β) = 0 :=
  flag_of_not fun h' => h (h' j (by omega))

namespace Xor3Zero

/-- The locals of xor3Zero: the arguments Λ, a, b, c, the result, the counter and the sum of the
three digits. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev A : ℕ := 1
@[inherit_doc Len] abbrev B : ℕ := 2
@[inherit_doc Len] abbrev C : ℕ := 3
@[inherit_doc Len] abbrev R : ℕ := 4
@[inherit_doc Len] abbrev Idx : ℕ := 5
@[inherit_doc Len] abbrev S : ℕ := 6

end Xor3Zero

open Xor3Zero in
/-- One round of xor3Zero: the answer becomes 0 if the three digits have the sum 1 or 3. -/
def xor3ZeroRound : Stmt :=
  .set S (M (v A +' v Idx) +' M (v B +' v Idx) +' M (v C +' v Idx)) ;;
  .ite (v S =' k 1) (.set R (k 0)) (.ite (v S =' k 3) (.set R (k 0)) .skip)

open Xor3Zero in
/-- xor3Zero(Λ, a, b, c): 1 if the XOR of the three rows at a, b, c is 0, and 0 if not. -/
def xor3ZeroBody : Stmt :=
  .set R (k 1) ;;
  .set S (k 0) ;;
  .for Idx (v Len) xor3ZeroRound ;;
  .set Len (v R)

/-- The time of xor3Zero. -/
def xor3ZeroTime (Λ : ℕ) : ℕ := 40 * Λ + 20

/-- The state of xor3Zero before round `j`: the answer for the first `j` positions. -/
def Xor3ZeroInv (μ : ℕ → ℤ) (Λ a b c x y z : ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ sv : ℤ, σ = ⟨frame [Λ, a, b, c, flag (∀ β < j, (x ^^^ y ^^^ z).testBit β = false), j, sv], μ⟩

/-- **xor3Zero(Λ, a, b, c)** returns 1 if `x ^^^ y ^^^ z = 0` and 0 if not, for `x, y, z < 2^Λ`
whose rows stand at `a`, `b`, `c`; that is, whether `x ⊕ y ⊕ z = 0` in `F^Λ`
(`toVec_add3_eq_zero_iff`).  It writes no cell. -/
theorem xor3Zero_meets {p : ℕ} (hp : P[p]? = some xor3ZeroBody) {μ : ℕ → ℤ} {Λ a b c x y z : ℕ}
    (hx : x < 2 ^ Λ) (hy : y < 2 ^ Λ) (hz : z < 2 ^ Λ)
    (ha : Seg μ a (digitRow Λ x)) (hb : Seg μ b (digitRow Λ y)) (hc : Seg μ c (digitRow Λ z))
    (hsa : a + Λ ≤ lim.space) (hsb : b + Λ ≤ lim.space) (hsc : c + Λ ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hc3 : (3 : ℤ) ≤ lim.word) :
    Meets lim P p d [(Λ : ℤ), a, b, c] μ (xor3ZeroTime Λ) fun r μ' =>
      r = flag (x ^^^ y ^^^ z = 0) ∧ μ' = μ := by
  have hxyz : x ^^^ y ^^^ z < 2 ^ Λ := Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hx hy) hz
  refine Meets.of_body hp ?_
  unfold xor3ZeroBody xor3ZeroTime
  -- R := 1 ; S := 0
  light_set (1 : ℕ)
  light_set (0 : ℕ)
  -- for Idx < Λ
  refine Ends.next _ (Ends.for (Xor3ZeroInv μ Λ a b c x y z) Λ xor3ZeroRound.blockCost ?start
    ?round ?done ?bound (hT := le_rfl)) (by light_time [xor3ZeroRound])
  case start =>
    refine ⟨0, ?_⟩
    rw [flag_of (fun β h => absurd h (Nat.not_lt_zero β))]
    simp [update_frame_setLocal]
  case bound =>
    rintro j σ - - ⟨sv, rfl⟩
    light_side
  case done =>
    rintro σ - ⟨sv, rfl⟩
    -- result := R
    rw [flag_congr (forall_testBit_iff hxyz)]
    have hf := flag_mem (x ^^^ y ^^^ z = 0)
    generalize flag (x ^^^ y ^^^ z = 0) = F at hf ⊢
    light_set F using xor3ZeroRound
    exact ⟨by simp, rfl⟩
  case round =>
    rintro j σ hj - ⟨sv, rfl⟩
    have hra := digit_of_seg ha hj
    have hrb := digit_of_seg hb hj
    have hrc := digit_of_seg hc hj
    have hbit := testBit_xor3_iff x y z j
    have hf := flag_mem (∀ β < j, (x ^^^ y ^^^ z).testBit β = false)
    generalize (if x.testBit j then 1 else 0 : ℤ) = dx at hra hbit
    generalize (if y.testBit j then 1 else 0 : ℤ) = dy at hrb hbit
    generalize (if z.testBit j then 1 else 0 : ℤ) = dz at hrc hbit
    have hdx : dx = 0 ∨ dx = 1 := by
      rw [← hra]; rw [digit_of_seg ha hj]; split_ifs <;> simp
    have hdy : dy = 0 ∨ dy = 1 := by
      rw [← hrb]; rw [digit_of_seg hb hj]; split_ifs <;> simp
    have hdz : dz = 0 ∨ dz = 1 := by
      rw [← hrc]; rw [digit_of_seg hc hj]; split_ifs <;> simp
    unfold xor3ZeroRound
    -- S := the sum of the three digits
    light_set (dx + dy + dz) using hra, hrb, hrc
    light_if h₁ h₂ : dx + dy + dz = 1
    · -- the sum is 1: R := 0
      light_set (0 : ℕ)
      refine ⟨by simp, dx + dy + dz, ?_⟩
      rw [flag_forall_succ_not (by rw [hbit.2 (Or.inl h₁)]; decide)]
      simp [update_frame_setLocal]
    · light_if h₃ h₄ : dx + dy + dz = 3
      · -- the sum is 3: R := 0
        light_set (0 : ℕ)
        refine ⟨by simp, dx + dy + dz, ?_⟩
        rw [flag_forall_succ_not (by rw [hbit.2 (Or.inr h₃)]; decide)]
        simp [update_frame_setLocal]
      · -- the sum is even: nothing changes
        light_skip
        refine ⟨by simp, dx + dy + dz, ?_⟩
        have hfalse : (x ^^^ y ^^^ z).testBit j = false := by
          rcases h : (x ^^^ y ^^^ z).testBit j
          · rfl
          · rcases hbit.1 h with h' | h' <;> contradiction
        rw [flag_forall_succ hfalse]
        simp [update_frame_setLocal]

/-! ## ipBit -/

namespace IpBit

/-- The locals of ipBit: the arguments Λ, a, b, the result and the counter. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev A : ℕ := 1
@[inherit_doc Len] abbrev B : ℕ := 2
@[inherit_doc Len] abbrev R : ℕ := 3
@[inherit_doc Len] abbrev Idx : ℕ := 4

end IpBit

open IpBit in
/-- One round of ipBit: the answer changes from `v` to `1 − v` if both digits are 1. -/
def ipBitRound : Stmt :=
  .ite (M (v A +' v Idx) *' M (v B +' v Idx) =' k 1) (.set R (k 1 -' v R)) .skip

open IpBit in
/-- ipBit(Λ, a, b): the inner product of the two rows at a and b, 0 or 1. -/
def ipBitBody : Stmt :=
  .set R (k 0) ;;
  .for Idx (v Len) ipBitRound ;;
  .set Len (v R)

/-- The time of ipBit. -/
def ipBitTime (Λ : ℕ) : ℕ := 30 * Λ + 20

/-- The state of ipBit before round `j`: the inner product of the first `j` coordinates. -/
def IpBitInv (μ : ℕ → ℤ) (Λ a b u x : ℕ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [Λ, a, b, (((dotUpTo u x j).val : ℕ) : ℤ), j], μ⟩

/-- **ipBit(Λ, a, b)** returns the inner product `⟨u, x⟩ ∈ F₂`, as 0 or 1, of the vectors whose
rows stand at `a` and `b`.  It writes no cell. -/
theorem ipBit_meets {p : ℕ} (hp : P[p]? = some ipBitBody) {μ : ℕ → ℤ} {Λ a b u x : ℕ}
    (ha : Seg μ a (digitRow Λ u)) (hb : Seg μ b (digitRow Λ x))
    (hsa : a + Λ ≤ lim.space) (hsb : b + Λ ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hc : (2 : ℤ) ≤ lim.word) :
    Meets lim P p d [(Λ : ℤ), a, b] μ (ipBitTime Λ) fun r μ' =>
      r = (((toVec Λ u ⬝ᵥ toVec Λ x).val : ℕ) : ℤ) ∧ μ' = μ := by
  refine Meets.of_body hp ?_
  unfold ipBitBody ipBitTime
  -- R := 0
  light_set (0 : ℕ)
  -- for Idx < Λ
  refine Ends.next _ (Ends.for (IpBitInv μ Λ a b u x) Λ ipBitRound.blockCost ?start
    ?round ?done ?bound (hT := le_rfl)) (by light_time [ipBitRound])
  case start => simp [IpBitInv, update_frame_setLocal, dotUpTo]
  case bound =>
    rintro j σ - - rfl
    light_side
  case done =>
    rintro σ - rfl
    have hv := ZMod.val_lt (toVec Λ u ⬝ᵥ toVec Λ x)
    have hv' : (((toVec Λ u ⬝ᵥ toVec Λ x).val : ℕ) : ℤ) < 2 := by exact_mod_cast hv
    generalize hws : (((toVec Λ u ⬝ᵥ toVec Λ x).val : ℕ) : ℤ) = w at hv' ⊢
    rw [dotUpTo_toVec, hws]
    -- result := R
    light_set w using ipBitRound
    exact ⟨by simp, rfl⟩
  case round =>
    rintro j σ hj - rfl
    have hra := digit_of_seg ha hj
    have hrb := digit_of_seg hb hj
    have hstep := dotUpTo_succ u x j
    have hv := ZMod.val_lt (dotUpTo u x j)
    have hv' : (((dotUpTo u x j).val : ℕ) : ℤ) < 2 := by exact_mod_cast hv
    generalize dotUpTo u x j = s at hstep hv hv' ⊢
    generalize hws : (((s.val : ℕ) : ℤ)) = w at hv' ⊢
    have hw0 : 0 ≤ w := hws ▸ Int.natCast_nonneg _
    have hprod : 0 ≤ μ (a + j) * μ (b + j) ∧ μ (a + j) * μ (b + j) ≤ 1 := by
      rw [hra, hrb]
      split_ifs <;> simp
    unfold ipBitRound
    light_if h₁ h₂ : μ (a + j) * μ (b + j) = 1
    · -- both digits are 1: R := 1 - R
      have hu : u.testBit j = true := by
        rw [hra, hrb] at h₁
        cases hu : u.testBit j <;> cases hx : x.testBit j <;> simp_all
      have hx : x.testBit j = true := by
        rw [hra, hrb] at h₁
        cases hu : u.testBit j <;> cases hx : x.testBit j <;> simp_all
      have hkey : (((dotUpTo u x (j + 1)).val : ℕ) : ℤ) = 1 - w := by
        rw [hstep, ← hws, ← val_one_add, add_comm]
        simp [bitF, hu, hx]
      light_set (1 - w)
      refine ⟨by simp, ?_⟩
      simp only [IpBitInv, hkey]
      simp [update_frame_setLocal]
    · -- otherwise nothing changes
      have hzero : bitF u j * bitF x j = 0 := by
        rw [hra, hrb] at h₂
        unfold bitF
        cases hu : u.testBit j <;> cases hx : x.testBit j <;> simp_all
      have hkey : (((dotUpTo u x (j + 1)).val : ℕ) : ℤ) = w := by
        rw [hstep, hzero, add_zero, hws]
      light_skip
      refine ⟨by simp, ?_⟩
      simp only [IpBitInv, hkey]
      simp [update_frame_setLocal]

/-! ## ofBits -/

/-- A row of zeros and ones. -/
def Bits01 (l : List ℤ) : Prop := ∀ b ∈ l, b = 0 ∨ b = 1

/-- The row of digits of a number is a row of zeros and ones. -/
theorem bits01_digitRow (Λ z : ℕ) : Bits01 (digitRow Λ z) := by
  intro b hb
  simp only [digitRow, List.mem_map, List.mem_range] at hb
  obtain ⟨β, -, rfl⟩ := hb
  split_ifs <;> simp

/-- The value of a row of zeros and ones has as many binary digits as the row has cells. -/
theorem rowVal_bounds : ∀ {l : List ℤ}, Bits01 l → 0 ≤ rowVal l ∧ rowVal l < 2 ^ l.length
  | [], _ => by simp [rowVal]
  | b :: l, h => by
    have hb := h b (List.mem_cons_self ..)
    have ih := rowVal_bounds (l := l) fun c hc => h c (List.mem_cons_of_mem _ hc)
    rw [rowVal, List.length_cons, pow_succ]
    omega

namespace OfBits

/-- The locals of ofBits: the arguments Λ and a, the value read so far, and the address of the
current cell. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev A : ℕ := 1
@[inherit_doc Len] abbrev R : ℕ := 2
@[inherit_doc Len] abbrev Cur : ℕ := 3

end OfBits

open OfBits in
/-- ofBits(Λ, a): the value of the row of Λ digits at a, the lowest digit first, by Horner's rule
from the top. -/
def ofBitsBody : Stmt :=
  .set R (k 0) ;;
  .set Cur (v A +' v Len) ;;
  .while (v A <' v Cur) (
    .set Cur (v Cur -' k 1) ;;
    .set R (k 2 *' v R +' M (v Cur))) ;;
  .set Len (v R)

/-- The time of ofBits. -/
def ofBitsTime (Λ : ℕ) : ℕ := 20 * Λ + 20

/-- The state of ofBits before round `t`: the value of the row from the cell `m = Λ − t` on. -/
def OfBitsInv (μ : ℕ → ℤ) (Λ a : ℕ) (row : List ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ m cur, m + t = Λ ∧ cur = a + m ∧ σ = ⟨frame [Λ, a, rowVal (row.drop m), cur], μ⟩

/-- **ofBits(Λ, a)** returns the value of the row of `Λ` zeros and ones at `a`, the lowest digit
first; for the row of `z` this is `z mod 2^Λ` (`rowVal_digitRow`).  It writes no cell. -/
theorem ofBits_meets {p : ℕ} (hp : P[p]? = some ofBitsBody) {μ : ℕ → ℤ} {Λ a : ℕ} {row : List ℤ}
    (hrow : Seg μ a row) (hlen : row.length = Λ) (h01 : Bits01 row) (hsa : a + Λ ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : (2 * 2 ^ Λ : ℤ) ≤ lim.word) :
    Meets lim P p d [(Λ : ℤ), a] μ (ofBitsTime Λ) fun r μ' => r = rowVal row ∧ μ' = μ := by
  have hpow1 : (1 : ℤ) ≤ 2 ^ Λ := one_le_pow₀ (by norm_num)
  refine Meets.of_body hp ?_
  unfold ofBitsBody ofBitsTime
  -- R := 0 ; Cur := A + Len
  light_set (0 : ℕ)
  light_set (a + Λ : ℕ)
  -- while A < Cur
  refine Ends.next _ (Ends.whileBlock (OfBitsInv μ Λ a row) Λ ?start ?round ?done (hT := le_rfl))
    (by light_time)
  case start =>
    refine ⟨Λ, a + Λ, by omega, rfl, ?_⟩
    rw [← hlen, List.drop_length]
    simp [rowVal]
  case round =>
    rintro t _ ht ⟨m', cur, hm, hcur, rfl⟩
    obtain ⟨m, rfl⟩ : ∃ m, m' = m + 1 := ⟨m' - 1, by omega⟩
    have hm' : m < row.length := by omega
    have hdrop : row.drop m = row[m] :: row.drop (m + 1) := List.drop_eq_getElem_cons hm'
    have hval : rowVal (row.drop m) = row[m] + 2 * rowVal (row.drop (m + 1)) := by
      rw [hdrop, rowVal]
    have hb := h01 _ (List.getElem_mem hm')
    have hbound := rowVal_bounds (l := row.drop (m + 1))
      fun c hc => h01 c (List.mem_of_mem_drop hc)
    have hle : (2 : ℤ) ^ (row.drop (m + 1)).length ≤ 2 ^ Λ :=
      pow_le_pow_right₀ (by norm_num) (by simp; omega)
    have hread : μ (a + m) = row[m] := hrow.get hm'
    have hpred : ((cur - 1 : ℕ) : ℤ) = (cur : ℤ) - 1 := by omega
    have haddr : ((cur : ℤ) - 1).toNat = a + m := by omega
    refine ⟨by light_side, by light_side, ?_⟩
    exact ⟨by light_side [haddr, hread], m, cur - 1, by omega, by omega,
      by simp [update_frame_setLocal, haddr, hread, hval, hpred]; ring_nf⟩
  case done =>
    rintro _ ⟨m, cur, hm, hcur, rfl⟩
    obtain rfl : m = 0 := by omega
    refine ⟨by light_side, by light_side, ?_⟩
    -- result := R
    have hbound := rowVal_bounds h01
    rw [hlen] at hbound
    light_set (rowVal row)
    exact ⟨by simp, rfl⟩

end Light.Remark23

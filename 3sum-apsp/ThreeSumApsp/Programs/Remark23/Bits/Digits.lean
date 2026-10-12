/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Remark23.Tasks
public import ThreeSumApsp.Util.BinaryPrefixes

/-!
# Remark 23 (3XOR): the table of binary digits of a list of vectors

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

vbits(len, s, Λ, bt) writes the `Λ` lowest binary digits of each of the `len` natural numbers
`z < 2^Λ` at `s`, one cell per digit, to the table at `bt`: digit `β` of the number at position `i`
in cell `bt + i Λ + β` (`vbits_meets`; the table is `digitTable Λ L`).  The row of a number stands
for its vector of `F^Λ` (`rowVec_digitRow`).

The routine is `bits` of the Chan–He reduction (`Light.Sec3.ChanHe.bitsBody`) without the offset
`V`: it first computes `2^Λ` by doubling (`vbitsPow_ends`); the digits of one number are found from
the top down, the rest of the number is doubled, and the digit is 1 if the result reaches `2^Λ`
(`vbitsRow_ends`).  It takes `O(len · Λ + Λ)` steps (`vbitsTime`).
-/

@[expose] public section

namespace Light.Remark23

open ThreeSumApsp ThreeSumApsp.Remark23

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The digits of z from position ℓ on stand in their cells of the row of Λ cells from row, and no
cell outside the row has changed. -/
structure VDigitsFrom (μ μ' : ℕ → ℤ) (row Λ z ℓ : ℕ) : Prop where
  /-- The digits from position ℓ on are written. -/
  digits : ∀ β, ℓ ≤ β → β < Λ → μ' (row + β) = if z.testBit β then 1 else 0
  /-- No cell outside the row has changed. -/
  same : SameOutside μ μ' row Λ

/-- One more digit is written. -/
theorem VDigitsFrom.write {μ μ' : ℕ → ℤ} {row Λ z ℓ : ℕ} (h : VDigitsFrom μ μ' row Λ z (ℓ + 1))
    (hℓ : ℓ < Λ) {b : ℤ} (hb : b = if z.testBit ℓ then 1 else 0) :
    VDigitsFrom μ (Function.update μ' (row + ℓ) b) row Λ z ℓ := by
  refine ⟨fun β h₁ h₂ => ?_, h.same.write (by omega) _⟩
  by_cases hβ : β = ℓ
  · rw [hβ, Function.update_self, hb]
  · rw [Function.update_of_ne (by omega)]
    exact h.digits β (by omega) h₂

/-- When all digits are written, the row holds them. -/
theorem VDigitsFrom.seg {μ μ' : ℕ → ℤ} {row Λ z : ℕ} (h : VDigitsFrom μ μ' row Λ z 0) :
    Seg μ' row (digitRow Λ z) := fun β hβ => by
  rw [getElem_digitRow]
  exact h.digits β (Nat.zero_le β) (by simpa using hβ)

namespace VBits

/-- The locals of vbits.  The arguments: len, s, Λ, bt.  Then the counter, the power 2^Λ, the
address of the digits of the current element, the address of the current digit, the rest of the
number, and the counter of the loop that computes the power. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Width : ℕ := 2
@[inherit_doc Len] abbrev Table : ℕ := 3
@[inherit_doc Len] abbrev Idx : ℕ := 4
@[inherit_doc Len] abbrev Pow : ℕ := 5
@[inherit_doc Len] abbrev Row : ℕ := 6
@[inherit_doc Len] abbrev Cur : ℕ := 7
@[inherit_doc Len] abbrev Rest : ℕ := 8
@[inherit_doc Len] abbrev Cnt : ℕ := 9

end VBits

open VBits in
/-- The power 2^Λ, by doubling. -/
def vbitsPow : Stmt :=
  .set Pow (k 1) ;;
  .set Cnt (k 0) ;;
  .while (v Cnt <' v Width) (
    .set Pow (k 2 *' v Pow) ;;
    .set Cnt (v Cnt +' k 1))

open VBits in
/-- The digits of one number, from the top down: the rest of the number is kept at the top of Λ
bits; it is doubled, and the digit is 1 if the result reaches 2^Λ. -/
def vbitsRow : Stmt :=
  .while (v Row <' v Cur) (
    .set Cur (v Cur -' k 1) ;;
    .set Rest (k 2 *' v Rest) ;;
    .ite (v Rest <' v Pow) (.store (v Cur) (k 0))
      (.store (v Cur) (k 1) ;; .set Rest (v Rest -' v Pow)))

open VBits in
/-- The digits of the current number. -/
def vbitsElem : Stmt :=
  .set Rest (M (v Src +' v Idx)) ;;
  .set Cur (v Row +' v Width) ;;
  vbitsRow ;;
  .set Row (v Row +' v Width)

open VBits in
/-- vbits(len, s, Λ, bt): len natural numbers below 2^Λ stand at s.  Writes the Λ lowest binary
digits of each number to the table at bt. -/
def vbitsBody : Stmt :=
  vbitsPow ;;
  .set Row (v Table) ;;
  .for Idx (v Len) vbitsElem

/-- The time of vbits. -/
def vbitsTime (len Λ : ℕ) : ℕ := len * (60 * Λ + 40) + 40 * Λ + 60

/-- The invariant of the loop of vbitsPow before round number j: Pow holds 2^j. -/
def VBitsPowInv (μ : ℕ → ℤ) (len s Λ bt : ℤ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [len, s, Λ, bt, 0, 2 ^ j, 0, 0, 0, j], μ⟩

/-- vbitsPow puts 2^Λ into Pow. -/
theorem vbitsPow_ends {μ : ℕ → ℤ} {len s bt : ℤ} {Λ : ℕ}
    (hword : (2 ^ Λ : ℤ) ≤ lim.word) :
    Ends lim P d vbitsPow ⟨frame [len, s, Λ, bt], μ⟩ (12 * Λ + 8)
      (· = ⟨frame [len, s, Λ, bt, 0, 2 ^ Λ, 0, 0, 0, Λ], μ⟩) := by
  have hB1 : (1 : ℤ) ≤ 2 ^ Λ := one_le_pow₀ (by norm_num)
  unfold vbitsPow
  -- Pow := 1 ; Cnt := 0
  light_set 1
  light_set (0 : ℕ)
  -- while Cnt < Width
  refine Ends.whileBlock (VBitsPowInv μ len s Λ bt) Λ ?start ?round ?done
  case start => simp [VBitsPowInv]
  case round =>
    -- Pow := 2 * Pow ; Cnt := Cnt + 1
    rintro j _ hj rfl
    have hpow : (2 : ℤ) ^ j * 2 ≤ 2 ^ Λ := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ (by norm_num) hj
    have hj' : ((j + 1 : ℕ) : ℤ) ≤ 2 ^ Λ := by
      have : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
      have h2 : (2 : ℤ) ^ (j + 1) ≤ 2 ^ Λ := pow_le_pow_right₀ (by norm_num) hj
      have : ((j + 1 : ℕ) : ℤ) < 2 ^ (j + 1) := by exact_mod_cast this
      omega
    have : (0 : ℤ) < 2 ^ j := by positivity
    push_cast at hj'
    exact ⟨by light_side, by light_side, by light_side,
      by simp [VBitsPowInv, update_frame_setLocal, pow_succ, mul_comm]⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_side, by light_side, rfl⟩

/-- The invariant of the loop of vbitsRow before round number t: the digits from position
ℓ = Λ - t on are written, Cur points to the cell of digit ℓ, and Rest holds the lower digits, moved
up to the top of Λ bits: the number `prefR Λ ℓ z`. -/
def VBitsRowInv (μ : ℕ → ℤ) (len s bt idx : ℤ) (row Λ z : ℕ) (t : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (ℓ cur : ℕ), ℓ + t = Λ ∧ cur = row + ℓ ∧
    σ = ⟨frame [len, s, Λ, bt, idx, 2 ^ Λ, row, cur, prefR Λ ℓ z, Λ], μ'⟩ ∧
    VDigitsFrom μ μ' row Λ z ℓ

/-- vbitsRow writes the digits of z into the row. -/
theorem vbitsRow_ends {μ : ℕ → ℤ} {len s bt idx : ℤ} {row Λ z : ℕ} (hz : z < 2 ^ Λ)
    (hword : (2 * 2 ^ Λ + 2 : ℤ) ≤ lim.word) (hw : (lim.space : ℤ) ≤ lim.word)
    (hrow : row + Λ ≤ lim.space) :
    Ends lim P d vbitsRow
      ⟨frame [len, s, Λ, bt, idx, 2 ^ Λ, row, ((row + Λ : ℕ) : ℤ), z, Λ], μ⟩ (23 * Λ + 4)
      fun σ' => ∃ μ',
        σ' = ⟨frame [len, s, Λ, bt, idx, 2 ^ Λ, row, row, prefR Λ 0 z, Λ], μ'⟩ ∧
        Seg μ' row (digitRow Λ z) ∧ SameOutside μ μ' row Λ := by
  unfold vbitsRow
  -- while Row < Cur
  refine Ends.whileBlock (VBitsRowInv μ len s bt idx row Λ z) Λ ?start ?round ?done
    (by simp; omega)
  case start =>
    exact ⟨μ, Λ, row + Λ, rfl, rfl, by rw [prefR_start (by positivity) (by exact_mod_cast hz)],
      fun β h₁ h₂ => absurd h₂ (by omega), .refl⟩
  case round =>
    -- Cur := Cur - 1 ; Rest := 2 * Rest
    rintro t _ ht ⟨μ', ℓ', cur, hℓ, hcur, rfl, hdig⟩
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ, ℓ' = ℓ + 1 := ⟨ℓ' - 1, by omega⟩
    have hfits := prefR_nonneg Λ (ℓ + 1) (z : ℤ)
    have hfits' := prefR_lt (show ℓ + 1 ≤ Λ by omega) (z : ℤ)
    have hstep := (pref_step (show ℓ + 1 ≤ Λ by omega) (z : ℤ)).2
    have hbit := testBit_iff_shift (show ℓ + 1 ≤ Λ by omega) z
    generalize prefR Λ (ℓ + 1) (z : ℤ) = r at hfits hfits' hstep hbit
    have hpred : ((cur - 1 : ℕ) : ℤ) = (cur : ℤ) - 1 := by omega
    have haddr : ((cur : ℤ) - 1).toNat = row + ℓ := by omega
    refine ⟨by light_side, by light_side, ?_⟩
    by_cases hc : 2 * r < 2 ^ Λ
    · -- the digit is 0: mem[Cur] := 0
      exact ⟨by light_side [hc], _, ℓ, cur - 1, by omega, by omega,
        by simp [update_frame_setLocal, hc, hpred, haddr, hstep, shiftR],
        hdig.write (b := 0) (by omega) (by rw [if_neg fun h => hbit.1 h hc])⟩
    · -- the digit is 1: mem[Cur] := 1 ; Rest := Rest - Pow
      exact ⟨by light_side [hc], _, ℓ, cur - 1, by omega, by omega,
        by simp [update_frame_setLocal, hc, hpred, haddr, hstep, shiftR],
        hdig.write (b := 1) (by omega) (by rw [if_pos (hbit.2 hc)])⟩
  case done =>
    rintro _ ⟨μ', ℓ, cur, hℓ, hcur, rfl, hdig⟩
    obtain rfl : ℓ = 0 := by omega
    obtain rfl : cur = row := by omega
    exact ⟨by light_side, by light_side, μ', rfl, hdig.seg, hdig.same⟩

/-- What vbits assumes: the list of natural numbers below `2^Λ` stands at `s`; the list and the
table lie in the memory and do not meet; addresses and doubled numbers fit in a word. -/
structure VBits.Ctx (lim : Limits) (μ : ℕ → ℤ) (s Λ bt : ℕ) (L : List ℤ) : Prop where
  nat : NatList L
  lt_pow : ∀ z ∈ L, z < 2 ^ Λ
  seg : Seg μ s L
  apart : Apart s L.length bt (L.length * Λ)
  spaceSrc : s + L.length ≤ lim.space
  spaceTable : bt + L.length * Λ ≤ lim.space
  space_le : (lim.space : ℤ) ≤ lim.word
  word : (2 * 2 ^ Λ + 2 : ℤ) ≤ lim.word

/-- The invariant of the main loop of vbits before round number i: the digits of the first i
numbers stand at bt, no cell outside the table has changed, and Row holds the address bt + iΛ of
the next row. -/
def VBitsInv (μ : ℕ → ℤ) (s Λ bt : ℕ) (L : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (row : ℕ) (cur rest : ℤ), row = bt + i * Λ ∧
    σ = ⟨frame [L.length, s, Λ, bt, i, 2 ^ Λ, row, cur, rest, Λ], μ'⟩ ∧
    Seg μ' bt (digitTable Λ (L.take i)) ∧ SameOutside μ μ' bt (L.length * Λ)

/-- One round of the main loop of vbits keeps the invariant. -/
theorem vbitsElem_ends {μ : ℕ → ℤ} {s Λ bt i : ℕ} {L : List ℤ}
    (C : VBits.Ctx lim μ s Λ bt L) (hi : i < L.length) {σ : State}
    (hI : VBitsInv μ s Λ bt L i σ) :
    Ends lim P d vbitsElem σ (23 * Λ + 19) fun σ' => σ'.loc VBits.Idx = i ∧
      VBitsInv μ s Λ bt L (i + 1)
        { σ' with loc := Function.update σ'.loc VBits.Idx ((i : ℤ) + 1) } := by
  obtain ⟨μ', row, cur, rest, hrow, rfl, hseg, hsame⟩ := hI
  -- where the regions lie
  have hw := C.space_le
  light_facts C
  have hrows : i * Λ + Λ ≤ L.length * Λ := Nat.mul_add_le_mul hi le_rfl
  have hnext : row + Λ = bt + (i + 1) * Λ := by rw [hrow, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have hread : μ' (s + i) = L.getD i 0 := (hsame _ (by omega)).trans (C.seg.getD hi 0)
  have hmem : L.getD i 0 ∈ L := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hnat := C.nat _ hmem
  have hlt := C.lt_pow _ hmem
  obtain ⟨z, hz⟩ : ∃ z, z = (L.getD i 0).toNat := ⟨_, rfl⟩
  have hlab : (z : ℤ) = μ' (s + i) := by
    rw [hz, hread]
    exact Int.toNat_of_nonneg hnat
  have hzlt : z < 2 ^ Λ := by
    have : (z : ℤ) < 2 ^ Λ := by rw [hlab, hread]; exact hlt
    exact_mod_cast this
  unfold vbitsElem
  -- Rest := mem[Src + Idx]
  light_set z
  -- Cur := Row + Width
  light_set (row + Λ : ℕ)
  -- the digits of the number
  light_piece (vbitsRow_ends (lim := lim) (z := z) hzlt C.word hw (by omega))
    with _ ⟨μ'', rfl, hrowSeg, hrowSame⟩
  -- Row := Row + Width
  light_set (row + Λ : ℕ)
  refine ⟨by simp, μ'', row + Λ, row, prefR Λ 0 z, hnext,
    by simp [update_frame_setLocal], ?_, hsame.trans (hrowSame.mono (by omega) (by omega))⟩
  have hlen : (digitTable Λ (L.take i)).length = i * Λ := by
    rw [length_digitTable, List.length_take, min_eq_left hi.le]
  rw [List.take_succ_getD L hi 0, digitTable_append, seg_append, hlen, ← hrow, ← hz]
  exact ⟨hseg.keep, hrowSeg⟩

/-- **vbits(len, s, Λ, bt)** writes the table of the binary digits of the `len` natural numbers
below `2^Λ` at `s` to `bt` (`len Λ` cells), and changes no other cell. -/
theorem vbits_meets {p : ℕ} (hP : P[p]? = some vbitsBody) {μ : ℕ → ℤ} {s Λ bt : ℕ}
    {L : List ℤ} (C : VBits.Ctx lim μ s Λ bt L) :
    Meets lim P p d [L.length, s, Λ, bt] μ (vbitsTime L.length Λ) fun _ μ' =>
      Seg μ' bt (digitTable Λ L) ∧ SameOutside μ μ' bt (L.length * Λ) := by
  light_facts C
  have hpow1 : (1 : ℤ) ≤ 2 ^ Λ := one_le_pow₀ (by norm_num)
  refine Meets.of_body hP ?_
  unfold vbitsTime vbitsBody
  -- Pow := 2 ^ Width
  light_piece (vbitsPow_ends (lim := lim) (μ := μ) (len := L.length) (s := s) (bt := bt)
    (Λ := Λ) (by omega)) with _ rfl
  -- Row := Table
  light_set bt
  -- for Idx < Len
  have htime := Nat.mul_le_mul_left L.length (show 1 + (23 * Λ + 19) + 7 ≤ 60 * Λ + 40 by omega)
  have hlen : (L.length : ℤ) ≤ lim.word := by
    have : ((s + L.length : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast C.spaceSrc
    push_cast at this
    omega
  refine Ends.for (VBitsInv μ s Λ bt L) L.length (23 * Λ + 19) ?start ?round ?done ?bound
    (hT := by simp only [Expr.cost]; omega)
  case start =>
    exact ⟨μ, bt, 0, 0, by simp, by simp [update_frame_setLocal], by simp [digitTable], .refl⟩
  case round => exact fun i σ hi _ hI => vbitsElem_ends C hi hI
  case bound =>
    rintro i _ - - ⟨μ', row, cur, rest, -, rfl, -⟩
    light_side
  case done =>
    rintro _ - ⟨μ', row, cur, rest, -, rfl, hseg, hsame⟩
    rw [List.take_length] at hseg
    exact ⟨hseg, hsame⟩

end Light.Remark23

/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Programs.Remark23.Bits.Numbers

/-!
# Remark 23 (3XOR): the table of the XORs of all pairs of `Λ`-digit numbers

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

xorTable(Λ, out) writes, for all `i, j < 2^Λ`, the number `i ^^^ j` into the cell
`out + i 2^Λ + j` (`xorTable_meets`; the list of the `4^Λ` cells is `xorTableList Λ`, and
`xorTableList_getD` reads it).  It computes `2^Λ` by doubling and calls xorNat for every pair, in
`O(4^Λ Λ)` steps (`xorTableTime`).  The table serves where many XORs of short numbers are needed:
the labels `h(w) ⊕ ϱ` of the note's Theorem 8 (`Λ = r`, `4^r ≤ D` cells) and the indices `i ⊕ j`
of its Lemma 10 (`Λ = k/2`, `2^k` cells).
-/

@[expose] public section

namespace Light.Remark23

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The table: the cell `q = i 2^Λ + j` holds `i ^^^ j`. -/
def xorTableList (Λ : ℕ) : List ℤ :=
  (List.range (2 ^ Λ * 2 ^ Λ)).map fun q => ((q / 2 ^ Λ ^^^ q % 2 ^ Λ : ℕ) : ℤ)

@[simp] theorem length_xorTableList (Λ : ℕ) : (xorTableList Λ).length = 2 ^ Λ * 2 ^ Λ := by
  simp [xorTableList]

/-- The position `i 2^Λ + j` of the table. -/
theorem xorCell_eq {Λ i j : ℕ} (hj : j < 2 ^ Λ) :
    (i * 2 ^ Λ + j) / 2 ^ Λ ^^^ (i * 2 ^ Λ + j) % 2 ^ Λ = i ^^^ j := by
  have hP : 0 < 2 ^ Λ := Nat.two_pow_pos Λ
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hj, Nat.zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

/-- **Reading the table**: the cell `i 2^Λ + j` holds `i ^^^ j`. -/
theorem xorTableList_getD {Λ i j : ℕ} (hi : i < 2 ^ Λ) (hj : j < 2 ^ Λ) :
    (xorTableList Λ).getD (i * 2 ^ Λ + j) 0 = ((i ^^^ j : ℕ) : ℤ) := by
  have hq : i * 2 ^ Λ + j < 2 ^ Λ * 2 ^ Λ := by nlinarith
  rw [List.getD_eq_getElem _ _ (by simpa using hq)]
  simp only [xorTableList, List.getElem_map, List.getElem_range]
  rw [xorCell_eq hj]

namespace XorTable

/-- The locals of xorTable: the arguments Λ and out, the power 2^Λ, the row i, the column j, the
result of xorNat, and the counter of the loop that computes the power. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Out : ℕ := 1
@[inherit_doc Len] abbrev Pow : ℕ := 2
@[inherit_doc Len] abbrev I : ℕ := 3
@[inherit_doc Len] abbrev J : ℕ := 4
@[inherit_doc Len] abbrev T : ℕ := 5
@[inherit_doc Len] abbrev Cnt : ℕ := 6

end XorTable

open XorTable in
/-- The power 2^Λ, by doubling. -/
def xorTablePow : Stmt :=
  .set Pow (k 1) ;;
  .set Cnt (k 0) ;;
  .while (v Cnt <' v Len) (
    .set Pow (k 2 *' v Pow) ;;
    .set Cnt (v Cnt +' k 1))

open XorTable in
/-- One cell: `out[i 2^Λ + j] := i ^^^ j`, by a call of xorNat, procedure number pX. -/
def xorTableCell (pX : ℕ) : Stmt :=
  .call pX [v Len, v Pow, v I, v J] T ;;
  .store (v Out +' v I *' v Pow +' v J) (v T)

open XorTable in
/-- xorTable(Λ, out): for i, j < 2^Λ, the cell out + i 2^Λ + j receives i ^^^ j.  pX is the
procedure number of xorNat. -/
def xorTableBody (pX : ℕ) : Stmt :=
  xorTablePow ;;
  .for I (v Pow) (.for J (v Pow) (xorTableCell pX))

/-- The time of xorTable. -/
def xorTableTime (Λ : ℕ) : ℕ := 2 ^ Λ * (2 ^ Λ * (40 * Λ + 35) + 14) + 12 * Λ + 14

/-- The invariant of the loop of xorTablePow before round number j: Pow holds 2^j. -/
def XorTablePowInv (μ : ℕ → ℤ) (Λ out : ℕ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [Λ, out, 2 ^ j, 0, 0, 0, j], μ⟩

/-- xorTablePow puts 2^Λ into Pow. -/
theorem xorTablePow_ends {μ : ℕ → ℤ} {Λ out : ℕ} (hword : (2 ^ Λ : ℤ) ≤ lim.word) :
    Ends lim P d xorTablePow ⟨frame [Λ, out], μ⟩ (12 * Λ + 8)
      (· = ⟨frame [Λ, out, 2 ^ Λ, 0, 0, 0, Λ], μ⟩) := by
  have hB1 : (1 : ℤ) ≤ 2 ^ Λ := one_le_pow₀ (by norm_num)
  unfold xorTablePow
  -- Pow := 1 ; Cnt := 0
  light_set 1
  light_set (0 : ℕ)
  -- while Cnt < Len
  refine Ends.whileBlock (XorTablePowInv μ Λ out) Λ ?start ?round ?done
  case start => simp [XorTablePowInv]
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
      by simp [XorTablePowInv, update_frame_setLocal, pow_succ, mul_comm]⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_side, by light_side, rfl⟩

/-- The first `m` cells of the table are written, and no cell outside the table has changed. -/
def XorWritten (μ : ℕ → ℤ) (out Λ m : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ q < m, μ' (out + q) = ((q / 2 ^ Λ ^^^ q % 2 ^ Λ : ℕ) : ℤ)) ∧
    SameOutside μ μ' out (2 ^ Λ * 2 ^ Λ)

/-- **xorTable(Λ, out)** writes the table of `i ^^^ j`, `i, j < 2^Λ`, to the `4^Λ` cells from
`out` and changes no other cell.  It calls xorNat, procedure number `pX`, one level below. -/
theorem xorTable_meets {p pX : ℕ} (hp : P[p]? = some (xorTableBody pX))
    (hpX : P[pX]? = some xorNatBody) {μ : ℕ → ℤ} {Λ out : ℕ}
    (hspace : out + 2 ^ Λ * 2 ^ Λ ≤ lim.space) (hw : (lim.space : ℤ) ≤ lim.word)
    (hword : (2 * 2 ^ Λ : ℤ) ≤ lim.word) (hd : d + 1 ≤ lim.depth) :
    Meets lim P p d [(Λ : ℤ), out] μ (xorTableTime Λ) fun _ μ' =>
      Seg μ' out (xorTableList Λ) ∧ SameOutside μ μ' out (2 ^ Λ * 2 ^ Λ) := by
  have hpow1 : (1 : ℤ) ≤ 2 ^ Λ := one_le_pow₀ (by norm_num)
  have hP : 1 ≤ 2 ^ Λ := Nat.one_le_two_pow
  have hPP : ((2 ^ Λ * 2 ^ Λ : ℕ) : ℤ) = 2 ^ Λ * 2 ^ Λ := by push_cast; ring
  have hsp : ((out + 2 ^ Λ * 2 ^ Λ : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast hspace
  push_cast at hsp
  have hPle : (2 : ℤ) ^ Λ ≤ 2 ^ Λ * 2 ^ Λ := le_mul_of_one_le_left (by positivity) hpow1
  refine Meets.of_body hp ?_
  unfold xorTableBody xorTableTime
  -- Pow := 2 ^ Λ
  light_piece (xorTablePow_ends (lim := lim) (μ := μ) (Λ := Λ) (out := out) (by omega)) with _ rfl
  -- for i < 2^Λ
  refine Ends.forScratch [XorTable.J, XorTable.T] (fun i μ' => XorWritten μ out Λ (i * 2 ^ Λ) μ')
    (2 ^ Λ) (2 ^ Λ * (40 * Λ + 35) + 6) ⟨fun q hq => absurd hq (by omega), .refl⟩ ?round ?done
    (hxs := by simp [xorTableCell]) (hn := by push_cast; omega) (hT := by light_time)
  case done =>
    intro _ μ' ⟨hdig, hsame⟩
    refine ⟨fun q hq => ?_, hsame⟩
    simp only [xorTableList, List.getElem_map, List.getElem_range]
    exact hdig q (by simpa using hq)
  case round =>
    intro i _ μ' hi hI
    -- for j < 2^Λ
    refine Ends.forScratch [XorTable.T] (fun j μ'' => XorWritten μ out Λ (i * 2 ^ Λ + j) μ'')
      (2 ^ Λ) (40 * Λ + 27) (by simpa using hI) ?cell ?rowDone (hxs := by simp [xorTableCell])
      (hn := by push_cast; omega) (hT := by light_time)
    case rowDone =>
      intro _ μ'' h
      rwa [show i * 2 ^ Λ + 2 ^ Λ = (i + 1) * 2 ^ Λ by ring] at h
    case cell =>
      intro j _ μ'' hj ⟨hdig, hsame⟩
      have hq : i * 2 ^ Λ + j < 2 ^ Λ * 2 ^ Λ := by nlinarith
      have hqZ : ((i : ℤ) * 2 ^ Λ + j) < 2 ^ Λ * 2 ^ Λ := by exact_mod_cast hq
      have hiZ : (0 : ℤ) ≤ (i : ℤ) * 2 ^ Λ := by positivity
      have hi' : i < 2 ^ Λ := hi
      have hj' : j < 2 ^ Λ := hj
      unfold xorTableCell
      -- T := xorNat(Λ, 2^Λ, i, j)
      light_call (xorNat_meets (lim := lim) (μ := μ'') hpX hi' hj' hword) using xorNatTime
        with r μ''' ⟨rfl, rfl⟩
      -- out[i 2^Λ + j] := T
      light_store (out + (i * 2 ^ Λ + j)) (i ^^^ j : ℕ) using Nat.cast_pow, Nat.cast_ofNat, xorNatTime
      refine ⟨fun q hq' => ?_, hsame.write (by omega) _⟩
      dsimp only
      by_cases hqe : q = i * 2 ^ Λ + j
      · rw [hqe, Function.update_self, xorCell_eq hj']
      · rw [Function.update_of_ne (by omega)]
        exact hdig q (by omega)

end Light.Remark23

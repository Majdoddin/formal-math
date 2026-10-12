/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.ZMod.Basic

/-!
# Remark 23 (3XOR): vectors over F₂ as natural numbers

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

The programs hold a vector of the note's `F^Λ` as the natural number whose binary digits are its
coordinates: coordinate `β` is digit `β` (`toVec`, and back `ofVec`).  The note's `⊕` is the
bitwise XOR `^^^` of the numbers (`toVec_xor`), a vector is zero exactly if the number is
(`toVec_eq_zero_iff`), and the inner product `⟨u, x⟩` is the parity of the number of positions
where both digits are 1 (`toVec_dotProduct`).  The numbers below `2^Λ` and the vectors of `F^Λ`
correspond one to one (`vecEquiv`).

A table of digits, one cell per digit, is a list of integers 0 and 1 (`digitRow`); its value as a
binary number, the lowest digit first, is `rowVal`.
-/

@[expose] public section

namespace Light.Remark23

open ThreeSumApsp ThreeSumApsp.Remark23

/-! ## Digits and vectors -/

/-- Digit `β` of `z`, as an element of `F₂`. -/
def bitF (z β : ℕ) : ZMod 2 := if z.testBit β then 1 else 0

/-- The vector of `F^Λ` whose coordinates are the `Λ` lowest binary digits of `z`. -/
def toVec (Λ z : ℕ) : Vec Λ := fun β => bitF z β

/-- The natural number whose binary digits are the coordinates of a vector, the coordinate `0` the
lowest digit. -/
def ofVec : {Λ : ℕ} → Vec Λ → ℕ
  | 0, _ => 0
  | _ + 1, v => (v 0).val + 2 * ofVec (Fin.tail v)

theorem bitF_xor (x y β : ℕ) : bitF (x ^^^ y) β = bitF x β + bitF y β := by
  unfold bitF
  rw [Nat.testBit_xor]
  cases x.testBit β <;> cases y.testBit β <;> decide

/-- **XOR is the addition of vectors.** -/
theorem toVec_xor (Λ x y : ℕ) : toVec Λ (x ^^^ y) = toVec Λ x + toVec Λ y := by
  funext β
  exact bitF_xor x y β

@[simp] theorem toVec_zero (Λ : ℕ) : toVec Λ 0 = 0 := by
  funext β
  simp [toVec, bitF]

/-- A number below `2^Λ` is 0 if its `Λ` lowest digits are. -/
theorem eq_zero_of_toVec {Λ z : ℕ} (hz : z < 2 ^ Λ) (h : toVec Λ z = 0) : z = 0 := by
  refine Nat.eq_of_testBit_eq fun β => ?_
  rw [Nat.zero_testBit]
  by_cases hβ : β < Λ
  · have := congrFun h ⟨β, hβ⟩
    simp only [toVec, bitF, Pi.zero_apply] at this
    by_contra hb
    rw [if_pos (Bool.not_eq_false _ ▸ hb)] at this
    exact one_ne_zero this
  · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- **A vector is zero exactly if its number is**, for a number below `2^Λ`. -/
theorem toVec_eq_zero_iff {Λ z : ℕ} (hz : z < 2 ^ Λ) : toVec Λ z = 0 ↔ z = 0 :=
  ⟨eq_zero_of_toVec hz, fun h => h ▸ toVec_zero Λ⟩

/-- Three vectors sum to zero exactly if the XOR of their numbers is 0. -/
theorem toVec_add3_eq_zero_iff {Λ x y z : ℕ} (hx : x < 2 ^ Λ) (hy : y < 2 ^ Λ) (hz : z < 2 ^ Λ) :
    toVec Λ x + toVec Λ y + toVec Λ z = 0 ↔ x ^^^ y ^^^ z = 0 := by
  rw [← toVec_xor, ← toVec_xor]
  exact toVec_eq_zero_iff (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow hx hy) hz)

/-- Two numbers below `2^Λ` are equal exactly if their vectors are. -/
theorem toVec_inj {Λ x y : ℕ} (hx : x < 2 ^ Λ) (hy : y < 2 ^ Λ) : toVec Λ x = toVec Λ y ↔ x = y := by
  constructor
  · intro h
    have h0 : toVec Λ (x ^^^ y) = 0 := by
      rw [toVec_xor, h]
      funext β
      exact CharTwo.add_self_eq_zero _
    have h1 := congrArg (· ^^^ y) (eq_zero_of_toVec (Nat.xor_lt_two_pow hx hy) h0)
    simpa [Nat.xor_assoc] using h1
  · rintro rfl
    rfl

/-- The vector of `z` with one more coordinate: the lowest digit, then the vector of `⌊z/2⌋`. -/
theorem toVec_succ (Λ z : ℕ) : toVec (Λ + 1) z = Fin.cons (bitF z 0) (toVec Λ (z / 2)) := by
  funext β
  refine Fin.cases rfl (fun β => ?_) β
  simp only [toVec, Fin.cons_succ, Fin.val_succ, bitF, Nat.testBit_succ]

theorem bitF_val (z β : ℕ) : (bitF z β).val = z / 2 ^ β % 2 := by
  unfold bitF
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (z / 2 ^ β) with h | h
  · simp [h]
  · simp only [h]
    rfl

/-- The number of the vector of `z` is `z mod 2^Λ`. -/
theorem ofVec_toVec (Λ z : ℕ) : ofVec (toVec Λ z) = z % 2 ^ Λ := by
  induction Λ generalizing z with
  | zero => simp [ofVec, Nat.mod_one]
  | succ Λ ih =>
    rw [toVec_succ, ofVec, Fin.cons_zero, Fin.tail_cons, ih, bitF_val, pow_succ, mul_comm (2 ^ Λ) 2,
      Nat.mod_mul]
    simp

/-- The number of a vector of `F^Λ` is below `2^Λ`. -/
theorem ofVec_lt : ∀ {Λ : ℕ} (v : Vec Λ), ofVec v < 2 ^ Λ
  | 0, _ => by simp [ofVec]
  | Λ + 1, v => by
    have h1 := ofVec_lt (Fin.tail v)
    have h2 : (v 0).val < 2 := ZMod.val_lt _
    rw [ofVec, pow_succ]
    omega

/-- The vector of the number of a vector is the vector itself. -/
theorem toVec_ofVec : ∀ {Λ : ℕ} (v : Vec Λ), toVec Λ (ofVec v) = v
  | 0, v => funext fun β => β.elim0
  | Λ + 1, v => by
    have h2 : (v 0).val < 2 := ZMod.val_lt _
    rw [toVec_succ, ofVec, show ((v 0).val + 2 * ofVec (Fin.tail v)) / 2 = ofVec (Fin.tail v) by
      omega, toVec_ofVec (Fin.tail v)]
    funext β
    refine Fin.cases ?_ (fun β => rfl) β
    rw [Fin.cons_zero, bitF, Nat.testBit_zero]
    have : (v 0).val = 0 ∨ (v 0).val = 1 := by omega
    rcases this with h | h
    · have hv : v 0 = 0 := (ZMod.val_eq_zero _).1 h
      simp [hv]
    · have hv : v 0 = 1 := by
        rw [← ZMod.natCast_zmod_val (v 0), h]
        rfl
      rw [if_pos (by rw [decide_eq_true_eq, h]; omega)]
      exact hv.symm

/-- The numbers below `2^Λ` and the vectors of `F^Λ` correspond one to one. -/
def vecEquiv (Λ : ℕ) : Fin (2 ^ Λ) ≃ Vec Λ where
  toFun i := toVec Λ i
  invFun v := ⟨ofVec v, ofVec_lt v⟩
  left_inv i := Fin.ext (by simp [ofVec_toVec, Nat.mod_eq_of_lt i.isLt])
  right_inv v := toVec_ofVec v

/-- The index `i ⊕ j` of two indices below `2^k` is the number `i ^^^ j`. -/
theorem ofVec_add_toVec {k i j : ℕ} (hi : i < 2 ^ k) (hj : j < 2 ^ k) :
    ofVec (toVec k i + toVec k j) = i ^^^ j := by
  rw [← toVec_xor, ofVec_toVec, Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hi hj)]

/-! ## The inner product -/

/-- The inner product of two vectors of digits, as a sum over the positions. -/
theorem toVec_dotProduct (Λ u x : ℕ) :
    toVec Λ u ⬝ᵥ toVec Λ x = ∑ β ∈ Finset.range Λ, bitF u β * bitF x β := by
  rw [dotProduct, ← Fin.sum_univ_eq_sum_range (fun β => bitF u β * bitF x β)]
  rfl

/-- The inner product of the first `j` coordinates. -/
def dotUpTo (u x j : ℕ) : ZMod 2 := ∑ β ∈ Finset.range j, bitF u β * bitF x β

theorem dotUpTo_succ (u x j : ℕ) :
    dotUpTo u x (j + 1) = dotUpTo u x j + bitF u j * bitF x j := by
  simp [dotUpTo, Finset.sum_range_succ]

/-- Adding 1 in `F₂` turns the value `v` into `1 - v`. -/
theorem val_one_add (s : ZMod 2) : (((1 + s).val : ℕ) : ℤ) = 1 - (s.val : ℤ) := by
  fin_cases s <;> rfl

theorem dotUpTo_toVec (Λ u x : ℕ) : dotUpTo u x Λ = toVec Λ u ⬝ᵥ toVec Λ x :=
  (toVec_dotProduct Λ u x).symm

/-! ## Rows of digits -/

/-- The digits `0, …, Λ − 1` of `z`, one integer 0 or 1 each, the lowest first. -/
def digitRow (Λ z : ℕ) : List ℤ := (List.range Λ).map fun β => if z.testBit β then 1 else 0

@[simp] theorem length_digitRow (Λ z : ℕ) : (digitRow Λ z).length = Λ := by simp [digitRow]

theorem getElem_digitRow {Λ z β : ℕ} (h : β < (digitRow Λ z).length) :
    (digitRow Λ z)[β] = if z.testBit β then 1 else 0 := by
  simp [digitRow]

/-- The rows of digits of a list of numbers, one after the other: digit `β` of the number at
position `i` in cell `i Λ + β`. -/
def digitTable (Λ : ℕ) (L : List ℤ) : List ℤ := L.flatMap fun z => digitRow Λ z.toNat

@[simp] theorem length_digitTable (Λ : ℕ) (L : List ℤ) :
    (digitTable Λ L).length = L.length * Λ := by
  induction L with
  | nil => simp [digitTable]
  | cons z L ih =>
    simp only [digitTable, List.flatMap_cons, List.length_append, length_digitRow,
      List.length_cons] at ih ⊢
    rw [ih, Nat.succ_mul, Nat.add_comm]

theorem digitTable_append (Λ : ℕ) (L : List ℤ) (z : ℤ) :
    digitTable Λ (L ++ [z]) = digitTable Λ L ++ digitRow Λ z.toNat := by
  simp [digitTable, List.flatMap_append]

/-- The value of a row of digits, the lowest digit first. -/
def rowVal : List ℤ → ℤ
  | [] => 0
  | b :: l => b + 2 * rowVal l

/-- The value of the row of digits of `z` is `z mod 2^Λ`. -/
theorem rowVal_digitRow (Λ z : ℕ) : rowVal (digitRow Λ z) = ((z % 2 ^ Λ : ℕ) : ℤ) := by
  induction Λ generalizing z with
  | zero => simp [digitRow, rowVal, Nat.mod_one]
  | succ Λ ih =>
    have hrow : digitRow (Λ + 1) z = (if z.testBit 0 then 1 else 0) :: digitRow Λ (z / 2) := by
      simp only [digitRow, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      refine List.map_congr_left fun β _ => ?_
      simp [Nat.testBit_succ]
    rw [hrow, rowVal, ih, pow_succ, mul_comm (2 ^ Λ) 2, Nat.mod_mul, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one z with h | h <;> simp [h]

/-- The vector of a row of digits. -/
def rowVec (Λ : ℕ) (row : List ℤ) : Vec Λ := fun β => (row.getD β 0 : ZMod 2)

/-- The row of digits of `z` stands for the vector of `z`. -/
theorem rowVec_digitRow (Λ z : ℕ) : rowVec Λ (digitRow Λ z) = toVec Λ z := by
  funext β
  simp only [rowVec, toVec, bitF, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some, getElem_digitRow]
  split_ifs <;> simp

end Light.Remark23

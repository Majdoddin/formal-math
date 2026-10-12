/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.TopProcedure
public import ThreeSumApsp.Programs.Remark23.Tasks

/-!
# 3XOR: from a solver of the task to a program for the layout of the end statement

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

Remark 23.  `realized_threeXor`: if the task `x3Task` is solved in time T, then
`EndStatement.ThreeXor` is solved on the word RAM within a constant times T.

The input is n in cell 0 and the 3n numbers of the three lists in the cells 1, …, 3n; the free
pointer is 3n + 1 (`threeXorInst`).  The cells hold the natural numbers of the lists
(`getD_threeXor_input₁` to `₃`), so the input meets the task's precondition (`pre_threeXor`), and
the result of a solver is the right verdict (`post_threeXor`).
-/

@[expose] public section

namespace Light.Remark23

open ThreeSumApsp ThreeSumApsp.WordRam

/-- The input of an instance of 3XOR. -/
theorem threeXor_input {n : ℕ} (S : EndStatement.ThreeXor.Instance n) :
    EndStatement.ThreeXor.input S =
      (List.ofFn S.1 ++ List.ofFn S.2.1 ++ List.ofFn S.2.2).map Int.ofNat := rfl

/-- The cells of the first list. -/
theorem getD_threeXor_input₁ {n : ℕ} (S : EndStatement.ThreeXor.Instance n) (i : Fin n) :
    (EndStatement.ThreeXor.input S).getD i 0 = S.1 i := by
  rw [threeXor_input, List.getD_eq_getElem?_getD, List.getElem?_map, List.append_assoc,
    List.getElem?_append_left (by simp), List.getElem?_ofFn]
  simp

/-- The cells of the second list. -/
theorem getD_threeXor_input₂ {n : ℕ} (S : EndStatement.ThreeXor.Instance n) (j : Fin n) :
    (EndStatement.ThreeXor.input S).getD (n + j) 0 = S.2.1 j := by
  rw [threeXor_input, List.getD_eq_getElem?_getD, List.getElem?_map, List.append_assoc,
    List.getElem?_append_right (by simp), List.getElem?_append_left (by simp),
    List.getElem?_ofFn]
  simp

/-- The cells of the third list. -/
theorem getD_threeXor_input₃ {n : ℕ} (S : EndStatement.ThreeXor.Instance n) (l : Fin n) :
    (EndStatement.ThreeXor.input S).getD (2 * n + l) 0 = S.2.2 l := by
  rw [threeXor_input, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_append_right (by simp; omega), List.getElem?_ofFn]
  simp only [List.length_append, List.length_ofFn]
  simp [show 2 * n + (l : ℕ) - (n + n) = l by omega]

/-- The numbers of the input are natural numbers. -/
theorem natList_threeXor_input {n : ℕ} (S : EndStatement.ThreeXor.Instance n) :
    NatList (EndStatement.ThreeXor.input S) := by
  intro z hz
  rw [threeXor_input, List.mem_map] at hz
  obtain ⟨a, -, rfl⟩ := hz
  exact Int.natCast_nonneg a

/-- The task's answer for the input is the answer of the end statement. -/
theorem x3Yes_threeXor {n : ℕ} (S : EndStatement.ThreeXor.Instance n) :
    x3Yes n (EndStatement.ThreeXor.input S) ↔ EndStatement.ThreeXor.yes S := by
  change _ ↔ ∃ i j k, S.1 i ^^^ S.2.1 j ^^^ S.2.2 k = 0
  constructor
  · rintro ⟨i, j, l, hi, hj, hl, h⟩
    refine ⟨⟨i, hi⟩, ⟨j, hj⟩, ⟨l, hl⟩, ?_⟩
    have h₁ := getD_threeXor_input₁ S ⟨i, hi⟩
    have h₂ := getD_threeXor_input₂ S ⟨j, hj⟩
    have h₃ := getD_threeXor_input₃ S ⟨l, hl⟩
    simp only at h₁ h₂ h₃
    rwa [h₁, h₂, h₃, Int.toNat_natCast, Int.toNat_natCast, Int.toNat_natCast] at h
  · rintro ⟨i, j, l, h⟩
    refine ⟨i, j, l, i.isLt, j.isLt, l.isLt, ?_⟩
    rw [getD_threeXor_input₁, getD_threeXor_input₂, getD_threeXor_input₃, Int.toNat_natCast,
      Int.toNat_natCast, Int.toNat_natCast]
    exact h

/-- The instance of the task: the numbers stand from cell 1 on. -/
def threeXorInst (x : Bounded EndStatement.ThreeXor) : x3Task.Inst :=
  ⟨x.n, x.U, 1, EndStatement.ThreeXor.input x.x⟩

/-- The input of the end statement meets the precondition of the task. -/
theorem pre_threeXor (x : Bounded EndStatement.ThreeXor) (hn : 1 ≤ x.n) (hU : 1 ≤ x.U) :
    x3Task.Pre (threeXorInst x) (memOf ((ofEnd EndStatement.ThreeXor).input x)) (3 * x.n + 1) where
  n_pos := hn
  U_pos := hU
  len := by simp [threeXorInst, threeXor_input]; ring
  seg := by simpa [threeXorInst] using seg_memOf [(x.n : ℤ)] (EndStatement.ThreeXor.input x.x) []
  le := fun _ ha => Bounded.abs_le ha
  nat := natList_threeXor_input x.x
  below := by simp [threeXorInst]; omega

/-- The result of a solver of the task is the right verdict of the end statement's 3XOR. -/
theorem post_threeXor (x : Bounded EndStatement.ThreeXor) (r : ℤ) (μ' : ℕ → ℤ)
    (h : x3Task.Post (threeXorInst x) (memOf ((ofEnd EndStatement.ThreeXor).input x))
      (3 * x.n + 1) r μ') :
    (ofEnd EndStatement.ThreeXor).IsAnswer x (verdictOf true r) fun i =>
      μ' (((ofEnd EndStatement.ThreeXor).input x).length + i) := by
  obtain ⟨rfl, -⟩ := h
  exact ⟨(verdictOf_flag _).trans (x3Yes_threeXor x.x), trivial⟩

/-- What connects 3XOR in the layout of the end statement with the task. -/
noncomputable def wrapThreeXor : Wrap EndStatement.ThreeXor x3Task true where
  args := [v 1, v 2, k 1, v 1 +' v 1 +' v 1 +' k 1]
  inst := threeXorInst
  fr x := 3 * x.n + 1
  size_eq _ := rfl
  bound_eq _ := rfl
  fr_pos x := by omega
  fr_le x := by
    have := Nat.le_mul_self x.n
    omega
  vals x σ hn hU _ := by
    simp [x3Task, threeXorInst, hn, hU]
    ring
  safe x lim σ hn _ _ hw := by
    have hnn : (x.n : ℤ) ≤ (x.n : ℤ) * x.n := by exact_mod_cast Nat.le_mul_self x.n
    push_cast at hw
    simp [hn, abs_le]
    omega
  zero x hn _ := by
    obtain ⟨n, U, S, hS⟩ := x
    simp only at hn
    subst hn
    exact ⟨⟨fun h => absurd h (by simp), fun ⟨i, _⟩ => i.elim0⟩, trivial⟩
  pre := pre_threeXor
  post x r μ' _ h := post_threeXor x r μ' h

/-- **3XOR**: if the task is solved in time T, then 3XOR is solved on the word RAM within a constant
times T. -/
theorem realized_threeXor (T : ℕ → ℝ → ℝ) (h : SolvedIn x3Task T) :
    Realized EndStatement.ThreeXor T :=
  wrapThreeXor.realized h

end Light.Remark23

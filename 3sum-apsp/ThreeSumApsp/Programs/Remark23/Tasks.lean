/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Programs.Tasks
public import ThreeSumApsp.Programs.Remark23.Bridge

/-!
# Remark 23 (3XOR): the problems of the note as tasks

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

The three problems of the note that its algorithm solves or calls, with the calling convention of
`Programs/Tasks.lean` (sizes, the bound, the addresses, and the free pointer last).  A vector of
`F^Λ` is a natural number below `2^Λ` (`Bridge.lean`); the number of digits that a task speaks of
is the bit length of the bound, `xlen U` (`lt_two_pow_xlen`, `two_pow_xlen_le`).

* `xetTask`, **Exact-XOR-Triangle**: three `n × n` matrices of natural numbers at most `U`; the
  answer is whether the instance of `F^Λ`-weights that they stand for (`xtriOf`) has a zero
  triangle.  In numbers: three weights with XOR 0 (`xtriOf_hasZeroTriangle_iff`).
* `cxTask`, **Convolution-3XOR** (the note's Definition 1): three arrays of length `N = 2^k`,
  indexed by `F^k` through the binary digits of the index; an entry is a natural number at most `U`
  or `-1`, which is the note's `⊥` (`cxArr`).  In numbers: `i`, `j` with nonempty `A[i]`, `B[j]`,
  `C[i ^^^ j]` whose XOR is 0 (`convHasSol_cxArr_iff`).
* `x3Task`, **3XOR**: three lists of `n` natural numbers at most `U`, one after the other, as in
  `EndStatement.ThreeXor`; the answer is whether one number from each list has XOR 0 (`x3Yes`).
  As three sets of vectors this is the note's `HasSol3` (`x3Yes_iff_hasSol3`).
-/

@[expose] public section

namespace Light.Remark23

open ThreeSumApsp ThreeSumApsp.Spec ThreeSumApsp.Remark23

/-! ## The number of digits -/

/-- The number of binary digits of the numbers up to `U`: the bit length of `U`. -/
abbrev xlen (U : ℕ) : ℕ := Nat.size U

/-- Every number up to `U` has at most `xlen U` digits. -/
theorem lt_two_pow_xlen (U : ℕ) : U < 2 ^ xlen U := Nat.lt_size_self U

/-- `2^(xlen U)` is at most `2 U`. -/
theorem two_pow_xlen_le {U : ℕ} (hU : 1 ≤ U) : 2 ^ xlen U ≤ 2 * U := by
  have hpos : 0 < xlen U := Nat.size_pos.2 hU
  have h : 2 ^ (xlen U - 1) ≤ U := Nat.lt_size.1 (by unfold xlen at hpos ⊢; omega)
  calc 2 ^ xlen U = 2 * 2 ^ (xlen U - 1) := by
        rw [← pow_succ']
        congr 1
        omega
    _ ≤ 2 * U := by omega

/-- The vector of `F^Λ` that a cell holding the natural number `z` stands for. -/
def xvec (Λ : ℕ) (z : ℤ) : Vec Λ := toVec Λ z.toNat

/-- The entries of a list are natural numbers. -/
def NatList (l : List ℤ) : Prop := ∀ z ∈ l, 0 ≤ z

/-- An entry of a list of natural numbers at most `U`, or the default 0, has at most `Λ` digits if
`U < 2^Λ`. -/
theorem toNat_getD_lt {l : List ℤ} {U Λ : ℕ} (hle : AbsLe l U) (hU : U < 2 ^ Λ) (i : ℕ) :
    (l.getD i 0).toNat < 2 ^ Λ := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[i]? with _ | z
  · simp
  · have hz := abs_le.1 (hle z (List.mem_of_getElem? h))
    simp only [Option.getD_some]
    omega

/-! ## Exact-XOR-Triangle -/

/-- The weights of the three matrices are natural numbers. -/
structure _root_.Light.TriInst.NatW (x : TriInst) : Prop where
  natAB : NatList x.AB
  natBC : NatList x.BC
  natAC : NatList x.AC

/-- The instance of Exact-XOR-Triangle with weights in `F^Λ` that three lists stand for, row by
row as in `triOf`. -/
def xtriOf (Λ n : ℕ) (AB BC AC : List ℤ) : TriangleInstance (Vec Λ) n where
  wAB a b := xvec Λ (AB.getD (a * n + b) 0)
  wBC b c := xvec Λ (BC.getD (b * n + c) 0)
  wAC a c := xvec Λ (AC.getD (a * n + c) 0)

/-- Three numbers with XOR 0: the weights of a zero triangle, read as natural numbers. -/
def XorZeroTriangle (n : ℕ) (AB BC AC : List ℤ) : Prop :=
  ∃ a b c : Fin n, (AB.getD (a * n + b) 0).toNat ^^^ (BC.getD (b * n + c) 0).toNat ^^^
    (AC.getD (a * n + c) 0).toNat = 0

/-- **A zero triangle is a triangle of weights with XOR 0**, at every number `Λ` of digits that
leaves room for the weights. -/
theorem xtriOf_hasZeroTriangle_iff {Λ n U : ℕ} {AB BC AC : List ℤ} (hU : U < 2 ^ Λ)
    (hAB : AbsLe AB U) (hBC : AbsLe BC U) (hAC : AbsLe AC U) :
    (xtriOf Λ n AB BC AC).HasZeroTriangle ↔ XorZeroTriangle n AB BC AC := by
  unfold TriangleInstance.HasZeroTriangle TriangleInstance.IsZeroTriangle TriangleInstance.S
    XorZeroTriangle
  refine exists_congr fun a => exists_congr fun b => exists_congr fun c => ?_
  exact toVec_add3_eq_zero_iff (toNat_getD_lt hAB hU _) (toNat_getD_lt hBC hU _)
    (toNat_getD_lt hAC hU _)

/-- **Exact-XOR-Triangle**: xet(n, U, ab, bc, ac, fr) returns 1 if the instance of `F^Λ`-weights,
`Λ = xlen U`, has a zero triangle, and 0 if not.  The weights are natural numbers at most `U`. -/
noncomputable def xetTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre x μ fr := x.Pre μ fr ∧ x.NatW
  Post x μ fr r μ' :=
    r = flag (xtriOf (xlen x.U) x.n x.AB x.BC x.AC).HasZeroTriangle ∧ Kept μ μ' fr

/-- The answer of Exact-XOR-Triangle, in numbers. -/
theorem xetTask_post_iff {x : TriInst} {μ : ℕ → ℤ} {fr : ℕ} (h : xetTask.Pre x μ fr) :
    (xtriOf (xlen x.U) x.n x.AB x.BC x.AC).HasZeroTriangle ↔ XorZeroTriangle x.n x.AB x.BC x.AC :=
  xtriOf_hasZeroTriangle_iff (lt_two_pow_xlen x.U) h.1.leAB h.1.leBC h.1.leAC

/-! ## Convolution-3XOR -/

/-- The entry at position `i` of an array of Convolution-3XOR: `⊥` (`none`) for a negative cell,
and otherwise the vector of the natural number in the cell. -/
def cxEntry (Λ : ℕ) (X : List ℤ) (i : ℕ) : Option (Vec Λ) :=
  if X.getD i (-1) < 0 then none else some (xvec Λ (X.getD i (-1)))

/-- The array indexed by `F^k` that a list of length `2^k` stands for: the index `i` is at the
position whose binary digits are the coordinates of `i`. -/
def cxArr (k Λ : ℕ) (X : List ℤ) : Vec k → Option (Vec Λ) := fun i => cxEntry Λ X (ofVec i)

/-- Three arrays of length `N = 2^k` in the memory. -/
structure CxInst : Type where
  N : ℕ
  k : ℕ
  U : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  A : List ℤ
  B : List ℤ
  C : List ℤ

/-- An entry is a natural number at most `U`, or `-1` (`⊥`). -/
def CxEntries (l : List ℤ) (U : ℕ) : Prop := ∀ z ∈ l, -1 ≤ z ∧ z ≤ U

/-- The three arrays lie below the free pointer, their length is `2^k`, and their entries are
natural numbers at most `U` or `-1`. -/
structure CxInst.Pre (x : CxInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_eq : x.N = 2 ^ x.k
  U_pos : 1 ≤ x.U
  lenA : x.A.length = x.N
  lenB : x.B.length = x.N
  lenC : x.C.length = x.N
  segA : Seg μ x.a x.A
  segB : Seg μ x.b x.B
  segC : Seg μ x.c x.C
  leA : CxEntries x.A x.U
  leB : CxEntries x.B x.U
  leC : CxEntries x.C x.U
  belowA : x.a + x.N ≤ fr
  belowB : x.b + x.N ≤ fr
  belowC : x.c + x.N ≤ fr

/-- The length is at least 1. -/
theorem CxInst.Pre.N_pos {x : CxInst} {μ : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr) : 1 ≤ x.N :=
  h.N_eq ▸ Nat.one_le_two_pow

/-- Entries at most `U` in absolute value. -/
theorem CxEntries.absLe {l : List ℤ} {U : ℕ} (h : CxEntries l U) (hU : 1 ≤ U) : AbsLe l U :=
  fun z hz => abs_le.2 ⟨by have := (h z hz).1; omega, (h z hz).2⟩

/-- An instance stays where it is if no cell below the free pointer changes. -/
theorem CxInst.Pre.keep {x : CxInst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr)
    (hs : Kept μ μ' fr := by light_keep) : x.Pre μ' fr := by
  light_facts h
  exact { h with segA := h.segA.keep, segB := h.segB.keep, segC := h.segC.keep }

/-- The free pointer may grow. -/
theorem CxInst.Pre.mono {x : CxInst} {μ : ℕ → ℤ} {fr fr' : ℕ} (h : x.Pre μ fr) (hfr : fr ≤ fr') :
    x.Pre μ fr' :=
  { h with
    belowA := h.belowA.trans hfr
    belowB := h.belowB.trans hfr
    belowC := h.belowC.trans hfr }

/-- **Convolution-3XOR** (the note's Definition 1): cx(N, k, U, a, b, c, fr) returns 1 if there are
`i, j ∈ F^k` with `A[i]`, `B[j]`, `C[i ⊕ j]` nonempty and of sum 0 in `F^Λ`, `Λ = xlen U`, and 0 if
not. -/
noncomputable def cxTask : Task where
  Inst := CxInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.k, x.U, x.a, x.b, x.c]
  Pre := CxInst.Pre
  Post x μ fr r μ' :=
    r = flag (ConvHasSol (cxArr x.k (xlen x.U) x.A) (cxArr x.k (xlen x.U) x.B)
      (cxArr x.k (xlen x.U) x.C)) ∧ Kept μ μ' fr

/-- The solutions of Convolution-3XOR, in numbers: positions `i`, `j` below `2^k` whose cells
`A[i]`, `B[j]`, `C[i ^^^ j]` are natural numbers with XOR 0. -/
def CxSol (k : ℕ) (A B C : List ℤ) : Prop :=
  ∃ i j : ℕ, i < 2 ^ k ∧ j < 2 ^ k ∧ 0 ≤ A.getD i (-1) ∧ 0 ≤ B.getD j (-1) ∧
    0 ≤ C.getD (i ^^^ j) (-1) ∧
    (A.getD i (-1)).toNat ^^^ (B.getD j (-1)).toNat ^^^ (C.getD (i ^^^ j) (-1)).toNat = 0

/-- An entry of a list of natural numbers at most `U` and `-1`, or the default `-1`, read as a
natural number, has at most `Λ` digits if `U < 2^Λ`. -/
theorem toNat_getD_neg_lt {l : List ℤ} {U Λ : ℕ} (hle : CxEntries l U) (hU : U < 2 ^ Λ) (i : ℕ) :
    (l.getD i (-1)).toNat < 2 ^ Λ := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[i]? with _ | z
  · simp
  · have hz := hle z (List.mem_of_getElem? h)
    simp only [Option.getD_some]
    omega

/-- The entry of a position, if it is not `⊥`. -/
theorem cxEntry_eq_some {Λ : ℕ} {X : List ℤ} {i : ℕ} {w : Vec Λ} :
    cxEntry Λ X i = some w ↔ 0 ≤ X.getD i (-1) ∧ xvec Λ (X.getD i (-1)) = w := by
  unfold cxEntry
  split_ifs with h
  · simp only [false_iff, not_and]
    intro h'
    omega
  · simp only [Option.some.injEq]
    exact ⟨fun h' => ⟨by omega, h'⟩, fun h' => h'.2⟩

/-- **Convolution-3XOR in numbers**: the instance of the arrays has a solution exactly if there are
positions `i`, `j` whose cells `A[i]`, `B[j]`, `C[i ^^^ j]` are natural numbers with XOR 0. -/
theorem convHasSol_cxArr_iff {k Λ U : ℕ} {A B C : List ℤ} (hU : U < 2 ^ Λ) (hA : CxEntries A U)
    (hB : CxEntries B U) (hC : CxEntries C U) :
    ConvHasSol (cxArr k Λ A) (cxArr k Λ B) (cxArr k Λ C) ↔ CxSol k A B C := by
  constructor
  · rintro ⟨i, j, a, b, c, hia, hjb, hijc, habc⟩
    rw [cxArr, cxEntry_eq_some] at hia hjb hijc
    have hij : ofVec (i + j) = ofVec i ^^^ ofVec j := by
      rw [← toVec_ofVec i, ← toVec_ofVec j, ofVec_add_toVec (ofVec_lt i) (ofVec_lt j),
        toVec_ofVec, toVec_ofVec]
    rw [hij] at hijc
    refine ⟨ofVec i, ofVec j, ofVec_lt i, ofVec_lt j, hia.1, hjb.1, hijc.1, ?_⟩
    rw [← toVec_add3_eq_zero_iff (toNat_getD_neg_lt hA hU _) (toNat_getD_neg_lt hB hU _)
      (toNat_getD_neg_lt hC hU _)]
    rw [← hia.2, ← hjb.2, ← hijc.2] at habc
    exact habc
  · rintro ⟨i, j, hi, hj, hA0, hB0, hC0, hx⟩
    refine ⟨toVec k i, toVec k j, xvec Λ (A.getD i (-1)), xvec Λ (B.getD j (-1)),
      xvec Λ (C.getD (i ^^^ j) (-1)), ?_, ?_, ?_, ?_⟩
    · rw [cxArr, cxEntry_eq_some, ofVec_toVec, Nat.mod_eq_of_lt hi]
      exact ⟨hA0, rfl⟩
    · rw [cxArr, cxEntry_eq_some, ofVec_toVec, Nat.mod_eq_of_lt hj]
      exact ⟨hB0, rfl⟩
    · rw [cxArr, cxEntry_eq_some, ofVec_add_toVec hi hj]
      exact ⟨hC0, rfl⟩
    · exact (toVec_add3_eq_zero_iff (toNat_getD_neg_lt hA hU _) (toNat_getD_neg_lt hB hU _)
        (toNat_getD_neg_lt hC hU _)).2 hx

/-- The answer of Convolution-3XOR, in numbers. -/
theorem cxTask_post_iff {x : CxInst} {μ : ℕ → ℤ} {fr : ℕ} (h : cxTask.Pre x μ fr) :
    ConvHasSol (cxArr x.k (xlen x.U) x.A) (cxArr x.k (xlen x.U) x.B) (cxArr x.k (xlen x.U) x.C) ↔
      CxSol x.k x.A x.B x.C :=
  convHasSol_cxArr_iff (lt_two_pow_xlen x.U) h.leA h.leB h.leC

/-! ## 3XOR -/

/-- Three lists of `n` numbers, one after the other, in the memory. -/
structure X3Inst : Type where
  n : ℕ
  U : ℕ
  a : ℕ
  X : List ℤ

/-- The `3 n` numbers lie below the free pointer, and they are natural numbers at most `U`. -/
structure X3Inst.Pre (x : X3Inst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  len : x.X.length = 3 * x.n
  seg : Seg μ x.a x.X
  le : AbsLe x.X x.U
  nat : NatList x.X
  below : x.a + 3 * x.n ≤ fr

/-- An instance stays where it is if no cell below the free pointer changes. -/
theorem X3Inst.Pre.keep {x : X3Inst} {μ μ' : ℕ → ℤ} {fr : ℕ} (h : x.Pre μ fr)
    (hs : Kept μ μ' fr := by light_keep) : x.Pre μ' fr := by
  light_facts h
  exact { h with seg := h.seg.keep }

/-- One number from each of the three lists, with XOR 0: the first list is at the positions
`0, …, n − 1`, the second at `n, …, 2n − 1`, the third at `2n, …, 3n − 1`. -/
def x3Yes (n : ℕ) (X : List ℤ) : Prop :=
  ∃ i j l : ℕ, i < n ∧ j < n ∧ l < n ∧
    (X.getD i 0).toNat ^^^ (X.getD (n + j) 0).toNat ^^^ (X.getD (2 * n + l) 0).toNat = 0

/-- **3XOR**: x3(n, U, a, fr) returns 1 if one number from each of the three lists of `n` numbers
at `a` has XOR 0, and 0 if not. -/
noncomputable def x3Task : Task where
  Inst := X3Inst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.a]
  Pre := X3Inst.Pre
  Post x μ fr r μ' := r = flag (x3Yes x.n x.X) ∧ Kept μ μ' fr

/-- The three lists of an instance of 3XOR as three sets of vectors of `F^Λ` (the note's `S_1`,
`S_2`, `S_3`, "from now on each S_i is a set"). -/
def x3Lists (Λ n : ℕ) (X : List ℤ) : Lists Λ :=
  fun t => (Finset.range n).image fun i => xvec Λ (X.getD (t.val * n + i) 0)

/-- **3XOR as the note's `HasSol3`**, at every number `Λ` of digits that leaves room for the
numbers. -/
theorem x3Yes_iff_hasSol3 {Λ n U : ℕ} {X : List ℤ} (hU : U < 2 ^ Λ) (hle : AbsLe X U) :
    x3Yes n X ↔ HasSol3 (x3Lists Λ n X) := by
  have hlt := toNat_getD_lt hle hU
  unfold x3Yes HasSol3 x3Lists
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, j, l, hi, hj, hl, h⟩
    refine ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, _, ⟨l, hl, rfl⟩, ?_⟩
    simp only [Fin.isValue, Fin.val_zero, zero_mul, zero_add, Fin.val_one, one_mul, Fin.val_two]
    exact (toVec_add3_eq_zero_iff (hlt _) (hlt _) (hlt _)).2 h
  · rintro ⟨_, ⟨i, hi, rfl⟩, _, ⟨j, hj, rfl⟩, _, ⟨l, hl, rfl⟩, h⟩
    simp only [Fin.isValue, Fin.val_zero, zero_mul, zero_add, Fin.val_one, one_mul,
      Fin.val_two] at h
    exact ⟨i, j, l, hi, hj, hl, (toVec_add3_eq_zero_iff (hlt _) (hlt _) (hlt _)).1 h⟩

end Light.Remark23

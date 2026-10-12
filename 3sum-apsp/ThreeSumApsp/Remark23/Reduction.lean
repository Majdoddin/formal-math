/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Remark23.Count
public import ThreeSumApsp.Util.Ceil
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Remark 23 (3XOR): Exact-XOR-Triangle reduces to Lop-AE-SparseTri

The note's Theorem 8 without its running time, the analogue of Theorem 17.  The general proof, in
the namespace `Remark23.General`, is about an instance `TriInst A B C d` with parts of arbitrary
finite types and about instances of Lop given by a middle part `mid : Finset V` (`LopInst`):

* the instances are instances of Lop(N, D) with at most `⌊N²/√D⌋` query pairs (`redInst_isLop`,
  `redInst_W_card`), and a query pair is accepted exactly if its piece holds a `c` with
  `h(S(a,b,c)) = 0` (`redInst_accepts_iff`);
* the cuttings into chunks and pieces exist, and there are at most `4Ng` instances
  (`exists_cutting`, `chunks_le`, `instances_le`); `reduction_spec` puts these together;
* minimizing `Z` is minimizing the false positives (`isGreedy_Z_iff`), whose number is less than
  `2eN³/√D` for the rows chosen by Lemma 5 (`false_positives_le`); the failed scans are at most
  `F(h)` (`failedScans_card_le`).

The bridge lemmas then pass to the vocabulary of the statements: `TriangleInstance (Vec d) n`
with parts `Fin n`, and the `LopInstance n` of Definition 13 (`redInstance_inTriangle_iff`,
`redInstance_middleAtMost_iff`); `pieceSize_eq` says that the paper's `pieceSize D g` is the
`⌈⌊√D⌋/g⌉` of the note.  The file ends with the statements `remark_23_theorem_8` to
`remark_23_theorem_8_failed_scans`.
-/

@[expose] public section

namespace ThreeSumApsp.Remark23.General

set_option linter.unusedSectionVars false

/-- An instance of `Lop` (Definition 13 of arXiv:2610.06783): outer parts `A`, `B`, a middle
part `mid` of vertices of `V`, edges `adjA ⊆ A × V`, `adjB ⊆ V × B`, query pairs `W`. -/
structure LopInst (A B V : Type*) where
  mid : Finset V
  adjA : A → V → Prop
  adjB : V → B → Prop
  W : Finset (A × B)

namespace LopInst
/-- `Lop(N, D)`: parts of `N` vertices, middle part of at most `D` vertices. -/
def IsLop {A B V : Type*} [Fintype A] [Fintype B] (I : LopInst A B V) (N D : ℕ) : Prop :=
  Fintype.card A = N ∧ Fintype.card B = N ∧ I.mid.card ≤ D

/-- The answer for a query pair: a common neighbour in the middle part. -/
def Accepts {A B V : Type*} (I : LopInst A B V) (a : A) (b : B) : Prop :=
  ∃ m ∈ I.mid, I.adjA a m ∧ I.adjB m b
end LopInst

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] {d r : ℕ}

/-- The instance of a chunk `Q` of the class `ϱ` and a piece `P` of `C`. -/
def redInst (I : TriInst A B C d) (h : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r)
    (Q : Finset (A × B)) (P : Finset C) : LopInst A B (C × Vec r) where
  mid := P ×ˢ Finset.univ
  adjA a m := m.2 = h (I.wac a m.1) + ϱ
  adjB m b := m.2 = h (I.wbc b m.1)
  W := Q

/-- The class `W_ϱ`. -/
def classOf (I : TriInst A B C d) (h : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r) : Finset (A × B) :=
  Finset.univ.filter fun p => h (I.wab p.1 p.2) = ϱ

/-! ### Helpers -/

private lemma vec_neg_eq_self {n : ℕ} (x : Vec n) : -x = x :=
  funext fun i => ZMod.neg_eq_self_mod_two (x i)

private lemma vec_add_self' {n : ℕ} (x : Vec n) : x + x = 0 :=
  funext fun i => by
    have : ∀ a : ZMod 2, a + a = 0 := by decide
    exact this (x i)

/-- `⌈s/g⌉ ≤ s` for `g ≥ 1`. -/
private lemma ceil_div_le_self (s g : ℕ) (hg : 1 ≤ g) : (s + g - 1) / g ≤ s := by
  have h1 : (s + g - 1) / g < s + 1 := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    have : s ≤ s * g := Nat.le_mul_of_pos_right s (by omega)
    rw [Nat.add_mul, one_mul]
    omega
  omega

/-- `s ≤ ⌈s/g⌉ g` for `g ≥ 1`. -/
private lemma le_ceil_div_mul (s g : ℕ) (hg : 1 ≤ g) : s ≤ (s + g - 1) / g * g := by
  have h1 := Nat.div_add_mod (s + g - 1) g
  have h2 := Nat.mod_lt (s + g - 1) (show 0 < g by omega)
  rw [mul_comm] at h1
  generalize (s + g - 1) / g * g = k at h1 ⊢
  omega

private lemma four_le_sqrt (D : ℕ) (hD : 16 ≤ D) : (4 : ℝ) ≤ Real.sqrt D := by
  rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg _)]
  have : (16 : ℝ) ≤ D := by exact_mod_cast hD
  linarith

/-- `√D + 1 ≤ N²/√D` for `16 ≤ D ≤ N`. -/
private lemma sqrt_add_one_le (N D : ℕ) (hD : 16 ≤ D) (hDN : D ≤ N) :
    Real.sqrt D + 1 ≤ (N : ℝ) ^ 2 / Real.sqrt D := by
  have ht := four_le_sqrt D hD
  have htt : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hD' : (16 : ℝ) ≤ D := by exact_mod_cast hD
  have hDN' : (D : ℝ) ≤ N := by exact_mod_cast hDN
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-! ### (a) Lop instances -/

theorem redInst_isLop (I : TriInst A B C d) (h : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r)
    (Q : Finset (A × B)) (P : Finset C) (N D g : ℕ)
    (hA : Fintype.card A = N) (hB : Fintype.card B = N) (hg : 1 ≤ g)
    (hP : P.card ≤ (Nat.sqrt D + g - 1) / g)          -- ⌈s/g⌉, s = ⌊√D⌋
    (hr : (2 : ℝ) ^ r ≤ Real.sqrt D) :
    (redInst I h ϱ Q P).IsLop N D := by
  refine ⟨hA, hB, ?_⟩
  have hc : (redInst I h ϱ Q P).mid.card = P.card * 2 ^ r := by
    simp [redInst, Finset.card_univ, ZMod.card]
  rw [hc]
  have hPs : (P.card : ℝ) ≤ Nat.sqrt D := by
    exact_mod_cast hP.trans (ceil_div_le_self _ _ hg)
  have hs : (Nat.sqrt D : ℝ) ≤ Real.sqrt D := Real.nat_sqrt_le_real_sqrt
  have htt : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have key : (P.card : ℝ) * 2 ^ r ≤ D := by
    calc (P.card : ℝ) * 2 ^ r ≤ Real.sqrt D * Real.sqrt D :=
          mul_le_mul (hPs.trans hs) hr (by positivity) (Real.sqrt_nonneg _)
      _ = D := htt
  exact_mod_cast key

theorem redInst_W_card (I : TriInst A B C d) (h : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r)
    (Q : Finset (A × B)) (P : Finset C) (N D : ℕ)
    (hQ : Q.card ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt D⌋₊) :
    ((redInst I h ϱ Q P).W.card : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt D :=
  le_trans (Nat.cast_le.mpr hQ) (Nat.floor_le (by positivity))

/-! ### (b) the correspondence -/

theorem redInst_accepts_iff (I : TriInst A B C d) (h : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r)
    (Q : Finset (A × B)) (P : Finset C) (a : A) (b : B) (hab : h (I.wab a b) = ϱ) :
    (redInst I h ϱ Q P).Accepts a b ↔ ∃ c ∈ P, h (I.S a b c) = 0 := by
  unfold LopInst.Accepts redInst
  simp only [Finset.mem_product, Finset.mem_univ, and_true, TriInst.S, map_add, hab]
  constructor
  · rintro ⟨⟨c, σ⟩, hc, h1, h2⟩
    refine ⟨c, hc, ?_⟩
    simp only at h1 h2
    rw [← h2, h1]
    calc ϱ + (h (I.wac a c) + ϱ) + h (I.wac a c)
        = (ϱ + ϱ) + (h (I.wac a c) + h (I.wac a c)) := by abel
      _ = 0 := by rw [vec_add_self', vec_add_self', add_zero]
  · rintro ⟨c, hc, h0⟩
    refine ⟨(c, h (I.wbc b c)), hc, ?_, rfl⟩
    simp only
    have : h (I.wbc b c) + (h (I.wac a c) + ϱ) = 0 := by rw [← h0]; abel
    rw [eq_neg_of_add_eq_zero_left this, vec_neg_eq_self]

theorem zero_triangle_caught (I : TriInst A B C d) (h : Vec d →ₗ[ZMod 2] Vec r)
    (Q : Finset (A × B)) (P : Finset C) (a : A) (b : B) (c : C)
    (_hQ : (a, b) ∈ Q) (hc : c ∈ P) (h0 : I.S a b c = 0) :
    (redInst I h (h (I.wab a b)) Q P).Accepts a b :=
  (redInst_accepts_iff I h _ Q P a b rfl).2 ⟨c, hc, by rw [h0, map_zero]⟩

/-! ### (c) the counts -/

/-- `r := ⌊log √D⌋` satisfies `√D/2 < 2^r ≤ √D` and `r ≥ 2`. -/
theorem rank_spec (D : ℕ) (hD : 16 ≤ D) :
    let r := Nat.log 2 (Nat.sqrt D)
    (2 : ℝ) ^ r ≤ Real.sqrt D ∧ Real.sqrt D / 2 < 2 ^ r ∧ 2 ≤ r := by
  intro r
  have hs : 4 ≤ Nat.sqrt D := Nat.le_sqrt'.2 (by omega)
  have h1 : 2 ^ r ≤ Nat.sqrt D := Nat.pow_log_le_self 2 (by omega)
  have h2 : Nat.sqrt D < 2 ^ (r + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  refine ⟨?_, ?_, ?_⟩
  · calc (2 : ℝ) ^ r = ((2 ^ r : ℕ) : ℝ) := by push_cast; ring
      _ ≤ Nat.sqrt D := by exact_mod_cast h1
      _ ≤ Real.sqrt D := Real.nat_sqrt_le_real_sqrt
  · have h3 : (Nat.sqrt D : ℝ) + 1 ≤ 2 ^ (r + 1) := by exact_mod_cast h2
    have := Real.real_sqrt_lt_nat_sqrt_succ (a := D)
    rw [pow_succ] at h3
    linarith
  · exact Nat.le_log_of_pow_le (by norm_num) (by omega)

/-- A finset is cut into at most `⌈|X|/L⌉` pairwise disjoint parts of at most `L` elements. -/
theorem exists_cutting {α : Type*} [DecidableEq α] (X : Finset α) (L : ℕ) (hL : 0 < L) :
    ∃ parts : Finset (Finset α), (∀ Y ∈ parts, Y ⊆ X ∧ Y.card ≤ L) ∧
      (∀ x ∈ X, ∃! Y, Y ∈ parts ∧ x ∈ Y) ∧ parts.card ≤ (X.card + L - 1) / L := by
  induction X using Finset.strongInduction with
  | H X ih =>
  rcases X.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨Y, hYX, hYc⟩ := Finset.exists_subset_card_eq (min_le_right L X.card)
  have hYne : Y.Nonempty := Finset.card_pos.1 (by rw [hYc]; exact lt_min hL hne.card_pos)
  obtain ⟨parts, h1, h2, h3⟩ := ih _ (Finset.sdiff_ssubset hYX hYne)
  refine ⟨insert Y parts, ?_, ?_, ?_⟩
  · intro Z hZ
    rcases Finset.mem_insert.1 hZ with rfl | hZ
    · exact ⟨hYX, hYc ▸ min_le_left _ _⟩
    · exact ⟨(h1 Z hZ).1.trans Finset.sdiff_subset, (h1 Z hZ).2⟩
  · intro x hx
    by_cases hxY : x ∈ Y
    · refine ⟨Y, ⟨Finset.mem_insert_self _ _, hxY⟩, ?_⟩
      rintro Z ⟨hZ, hxZ⟩
      rcases Finset.mem_insert.1 hZ with rfl | hZ
      · rfl
      · exact absurd hxY (Finset.mem_sdiff.1 ((h1 Z hZ).1 hxZ)).2
    · obtain ⟨Z, ⟨hZ, hxZ⟩, huniq⟩ := h2 x (Finset.mem_sdiff.2 ⟨hx, hxY⟩)
      refine ⟨Z, ⟨Finset.mem_insert_of_mem hZ, hxZ⟩, ?_⟩
      rintro W ⟨hW, hxW⟩
      rcases Finset.mem_insert.1 hW with rfl | hW
      · exact absurd hxW hxY
      · exact huniq W ⟨hW, hxW⟩
  · rw [Finset.card_sdiff_of_subset hYX, hYc] at h3
    have hn := hne.card_pos
    refine (Finset.card_insert_le _ _).trans ?_
    rcases le_total L X.card with hLX | hXL
    · rw [min_eq_left hLX] at h3
      have : X.card + L - 1 = (X.card - L + L - 1) + L := by omega
      rw [this, Nat.add_div_right _ hL]
      omega
    · rw [min_eq_right hXL] at h3
      have h0 : (X.card - X.card + L - 1) / L = 0 := Nat.div_eq_of_lt (by omega)
      rw [h0] at h3
      have : 1 ≤ (X.card + L - 1) / L := (Nat.le_div_iff_mul_le hL).2 (by omega)
      omega

theorem chunks_le (N D r : ℕ) (cnt : Vec r → ℕ) (hsum : ∑ ϱ, cnt ϱ = N ^ 2)
    (hD : 16 ≤ D) (hDN : D ≤ N) (hr : (2 : ℝ) ^ r ≤ Real.sqrt D) :
    let L := ⌊(N : ℝ) ^ 2 / Real.sqrt D⌋₊
    ((∑ ϱ, (cnt ϱ + L - 1) / L : ℕ) : ℝ) ≤ 2 * Real.sqrt D + 1 := by
  intro L
  have hx := sqrt_add_one_le N D hD hDN
  have ht := four_le_sqrt D hD
  have hL1 : ((N : ℝ) ^ 2 / Real.sqrt D) < L + 1 := Nat.lt_floor_add_one _
  have hLpos : (0 : ℝ) < L := by linarith
  have hLnat : 0 < L := by exact_mod_cast hLpos
  -- each term
  have hterm : ∀ ϱ, (((cnt ϱ + L - 1) / L : ℕ) : ℝ) ≤ cnt ϱ / L + 1 := by
    intro ϱ
    refine Nat.cast_div_le.trans ?_
    have : ((cnt ϱ + L - 1 : ℕ) : ℝ) ≤ cnt ϱ + L := by
      have : cnt ϱ + L - 1 ≤ cnt ϱ + L := by omega
      exact_mod_cast this
    calc ((cnt ϱ + L - 1 : ℕ) : ℝ) / L ≤ (cnt ϱ + L) / L :=
          div_le_div_of_nonneg_right this hLpos.le
      _ = cnt ϱ / L + 1 := by rw [add_div, div_self hLpos.ne']
  have hsum' : (∑ ϱ, (cnt ϱ : ℝ)) = (N : ℝ) ^ 2 := by exact_mod_cast hsum
  have hcard : (∑ _ϱ : Vec r, (1 : ℝ)) = 2 ^ r := by
    simp [Finset.card_univ, ZMod.card]
  -- N²/L ≤ √D + 1
  have hNL : (N : ℝ) ^ 2 / L ≤ Real.sqrt D + 1 := by
    rw [div_le_iff₀ hLpos]
    have htpos : 0 < Real.sqrt D := by linarith
    have hN2 : (N : ℝ) ^ 2 = (N : ℝ) ^ 2 / Real.sqrt D * Real.sqrt D := by
      field_simp
    set x := (N : ℝ) ^ 2 / Real.sqrt D
    nlinarith
  push_cast
  calc ∑ ϱ, (((cnt ϱ + L - 1) / L : ℕ) : ℝ) ≤ ∑ ϱ, ((cnt ϱ : ℝ) / L + 1) :=
        Finset.sum_le_sum fun ϱ _ => hterm ϱ
    _ = (∑ ϱ, (cnt ϱ : ℝ)) / L + ∑ _ϱ : Vec r, (1 : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_div]
    _ = (N : ℝ) ^ 2 / L + 2 ^ r := by rw [hsum', hcard]
    _ ≤ 2 * Real.sqrt D + 1 := by linarith

theorem instances_le (N D g chunks : ℕ) (hD : 16 ≤ D) (hDN : D ≤ N)
    (hg1 : 1 ≤ g) (hg : (g : ℝ) ≤ Real.sqrt D) (hch : (chunks : ℝ) ≤ 2 * Real.sqrt D + 1) :
    let p := (Nat.sqrt D + g - 1) / g                    -- piece size ⌈s/g⌉
    chunks * ((N + p - 1) / p) ≤ 4 * N * g := by
  intro p
  set s := Nat.sqrt D with hs_def
  have hs4 : 4 ≤ s := Nat.le_sqrt'.2 (by omega)
  have ht := four_le_sqrt D hD
  have htt : Real.sqrt D * Real.sqrt D = D := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hts : Real.sqrt D < s + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hpg : s ≤ p * g := le_ceil_div_mul s g hg1
  have hp1 : 1 ≤ p := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · rw [h0, zero_mul] at hpg; omega
    · exact h0
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp1
  have hsR : (4 : ℝ) ≤ s := by exact_mod_cast hs4
  have hgR : (1 : ℝ) ≤ g := by exact_mod_cast hg1
  have hpgR : (s : ℝ) ≤ p * g := by exact_mod_cast hpg
  have hD' : (16 : ℝ) ≤ D := by exact_mod_cast hD
  have hDN' : (D : ℝ) ≤ N := by exact_mod_cast hDN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  -- ⌈N/p⌉ ≤ N g / s + 1
  have hm : (((N + p - 1) / p : ℕ) : ℝ) ≤ N * g / s + 1 := by
    refine Nat.cast_div_le.trans ?_
    have h1 : ((N + p - 1 : ℕ) : ℝ) ≤ N + p := by
      have : N + p - 1 ≤ N + p := by omega
      exact_mod_cast this
    have h2 : (N : ℝ) / p ≤ N * g / s := by
      rw [div_le_div_iff₀ hpR (by linarith)]
      nlinarith
    calc ((N + p - 1 : ℕ) : ℝ) / p ≤ (N + p) / p := div_le_div_of_nonneg_right h1 hpR.le
      _ = N / p + 1 := by rw [add_div, div_self hpR.ne']
      _ ≤ N * g / s + 1 := by linarith
  have hch0 : (0 : ℝ) ≤ chunks := Nat.cast_nonneg _
  -- (2√D + 1) (N g / s) ≤ 3 N g
  have hA : (2 * Real.sqrt D + 1) * (N * g / s) ≤ 3 * N * g := by
    have : 2 * Real.sqrt D + 1 ≤ 3 * s := by linarith
    calc (2 * Real.sqrt D + 1) * (N * g / s) ≤ (3 * s) * (N * g / s) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 3 * N * g := by field_simp
  -- 2√D + 1 ≤ N g
  have hB : 2 * Real.sqrt D + 1 ≤ N * g := by
    have : 4 * Real.sqrt D ≤ D := by nlinarith
    nlinarith
  have key : (chunks : ℝ) * (((N + p - 1) / p : ℕ) : ℝ) ≤ 4 * N * g := by
    calc (chunks : ℝ) * (((N + p - 1) / p : ℕ) : ℝ)
        ≤ (2 * Real.sqrt D + 1) * (N * g / s + 1) :=
          mul_le_mul hch hm (Nat.cast_nonneg _) (by linarith)
      _ = (2 * Real.sqrt D + 1) * (N * g / s) + (2 * Real.sqrt D + 1) := by ring
      _ ≤ 4 * N * g := by linarith
  exact_mod_cast key

/-! ### (d) the hash -/

noncomputable def _root_.ThreeSumApsp.Remark23.TriInst.F {q : ℕ} (I : TriInst A B C d) (G : Vec d →ₗ[ZMod 2] Vec q) : ℕ :=
  (Finset.univ.filter fun t : A × B × C =>
    I.S t.1 t.2.1 t.2.2 ≠ 0 ∧ G (I.S t.1 t.2.1 t.2.2) = 0).card

/-- The family of Lemma 5 for this theorem: the triples with `S ≠ 0`, weight 1. -/
noncomputable def fpFamily (I : TriInst A B C d) : Finset (A × B × C) :=
  Finset.univ.filter fun t => I.S t.1 t.2.1 t.2.2 ≠ 0

theorem surv_eq_F (I : TriInst A B C d) (rows : List (Vec d)) :
    surv (fpFamily I) (fun t => I.S t.1 t.2.1 t.2.2) (fun _ => 1) rows = I.F (rowsMap rows) := by
  unfold surv TriInst.F fpFamily
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter]
  norm_cast
  congr 1
  apply Finset.filter_congr
  intro t _
  rw [rowsMap_eq_zero_iff]

theorem Z_eq_F_add (I : TriInst A B C d) {q : ℕ} (G : Vec d →ₗ[ZMod 2] Vec q) :
    I.Z G = I.F G + (Finset.univ.filter fun t : A × B × C => I.S t.1 t.2.1 t.2.2 = 0).card := by
  unfold TriInst.Z TriInst.F
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h : I.S t.1 t.2.1 t.2.2 = 0 <;> simp [h]

/-- Greedy on `Z` (what the algorithm computes) is greedy on `Φ` (what Lemma 5 bounds). -/
theorem isGreedy_Z_iff (I : TriInst A B C d) (E : Multiset (Vec d)) (rows : List (Vec d)) :
    IsGreedy E (fun l => (I.Z (rowsMap l) : ℝ)) rows ↔
      IsGreedy E (surv (fpFamily I) (fun t => I.S t.1 t.2.1 t.2.2) (fun _ => 1)) rows := by
  have : (fun l => (I.Z (rowsMap l) : ℝ)) = fun l =>
      surv (fpFamily I) (fun t => I.S t.1 t.2.1 t.2.2) (fun _ => 1) l +
        ((Finset.univ.filter fun t : A × B × C => I.S t.1 t.2.1 t.2.2 = 0).card : ℝ) := by
    funext l
    rw [Z_eq_F_add, surv_eq_F]
    push_cast
    ring
  rw [this, isGreedy_add_const]

theorem false_positives_le (I : TriInst A B C d) (N D : ℕ)
    (hA : Fintype.card A = N) (hB : Fintype.card B = N) (hC : Fintype.card C = N)
    (hD : 16 ≤ D) (hDN : D ≤ N) (E : Multiset (Vec d)) (rows : List (Vec d))
    (hlen : rows.length = Nat.log 2 (Nat.sqrt D))
    (hE : IsBiased (1 / rows.length) E)
    (hg : IsGreedy E (fun l => (I.Z (rowsMap l) : ℝ)) rows) :
    (I.F (rowsMap rows) : ℝ) ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * N ^ 3 ∧
    (I.F (rowsMap rows) : ℝ) < 2 * Real.exp 1 * N ^ 3 / Real.sqrt D := by
  obtain ⟨hr1, hr2, hr3⟩ := rank_spec D hD
  rw [← hlen] at hr1 hr2 hr3
  have hpos : 0 < rows.length := by omega
  have hg' := (isGreedy_Z_iff I E rows).1 hg
  have hb := greedy_bound_exp hE (by positivity) (fpFamily I) (fun t => I.S t.1 t.2.1 t.2.2)
    (fun _ => 1) (fun j hj => (Finset.mem_filter.1 hj).2) (fun _ _ => zero_le_one) rows hg'
    hpos le_rfl
  rw [surv_eq_F, Finset.sum_const, nsmul_eq_mul, mul_one] at hb
  have hcard : ((fpFamily I).card : ℝ) ≤ (N : ℝ) ^ 3 := by
    have : (fpFamily I).card ≤ N ^ 3 := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod, hA, hB, hC]
      ring_nf
      exact le_rfl
    exact_mod_cast this
  have h1 : (I.F (rowsMap rows) : ℝ) ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * N ^ 3 :=
    hb.trans (mul_le_mul_of_nonneg_left hcard (by positivity))
  refine ⟨h1, h1.trans_lt ?_⟩
  have ht := four_le_sqrt D hD
  have hN : (16 : ℝ) ≤ N := by exact_mod_cast hD.trans hDN
  have hkey : ((2 : ℝ) ^ rows.length)⁻¹ < 2 / Real.sqrt D := by
    rw [inv_eq_one_div, div_lt_div_iff₀ (by positivity) (by linarith)]
    linarith
  have hpos' : 0 < Real.exp 1 * (N : ℝ) ^ 3 := by positivity
  calc Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * N ^ 3
      = Real.exp 1 * (N : ℝ) ^ 3 * ((2 : ℝ) ^ rows.length)⁻¹ := by rw [inv_pow]; ring
    _ < Real.exp 1 * (N : ℝ) ^ 3 * (2 / Real.sqrt D) := mul_lt_mul_of_pos_left hkey hpos'
    _ = 2 * Real.exp 1 * N ^ 3 / Real.sqrt D := by ring

/-! ### The capstone -/

/-- One instance of the reduction: a class `ϱ`, a chunk `Q` of it and a piece `P` of `C`. -/
structure RedIndex (A B C : Type*) (r : ℕ) where
  ϱ : Vec r
  Q : Finset (A × B)
  P : Finset C
deriving DecidableEq

theorem reduction_spec (I : TriInst A B C d) (N D g : ℕ)
    (hA : Fintype.card A = N) (hB : Fintype.card B = N) (hC : Fintype.card C = N)
    (hD : 16 ≤ D) (hDN : D ≤ N) (hg1 : 1 ≤ g) (hg : (g : ℝ) ≤ Real.sqrt D)
    (rows : List (Vec d)) (hlen : rows.length = Nat.log 2 (Nat.sqrt D)) :
    let h := rowsMap rows
    ∃ inst : Finset (RedIndex A B C rows.length),
      (∀ J ∈ inst, J.Q ⊆ classOf I h J.ϱ ∧
        (redInst I h J.ϱ J.Q J.P).IsLop N D ∧ J.Q.card ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt D⌋₊) ∧
      inst.card ≤ 4 * N * g ∧
      (∀ J ∈ inst, ∀ J' ∈ inst, J.P ≠ J'.P → Disjoint J.P J'.P) ∧
      (∀ J ∈ inst, ∀ p : A × B, ∃! J' ∈ inst, J'.P = J.P ∧ p ∈ J'.Q) ∧
      (I.HasZeroTriangle ↔
        ∃ J ∈ inst, ∃ p ∈ J.Q, (redInst I h J.ϱ J.Q J.P).Accepts p.1 p.2 ∧
          ∃ c ∈ J.P, I.S p.1 p.2 c = 0) := by
  intro h
  obtain ⟨hr1, -, -⟩ := rank_spec D hD
  rw [← hlen] at hr1
  set L := ⌊(N : ℝ) ^ 2 / Real.sqrt D⌋₊ with hL_def
  have hL : 0 < L := by
    have hx := sqrt_add_one_le N D hD hDN
    have ht := four_le_sqrt D hD
    exact Nat.le_floor (by push_cast; linarith)
  set p := (Nat.sqrt D + g - 1) / g with hp_def
  have hp : 0 < p := by
    have hs4 : 4 ≤ Nat.sqrt D := Nat.le_sqrt'.2 (by omega)
    have := le_ceil_div_mul (Nat.sqrt D) g hg1
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · rw [← hp_def, h0, zero_mul] at this; omega
    · exact h0
  choose chunks hch1 hch2 hch3 using fun ϱ : Vec rows.length => exists_cutting (classOf I h ϱ) L hL
  obtain ⟨pieces, hp1, hp2, hp3⟩ := exists_cutting (Finset.univ : Finset C) p hp
  let inst : Finset (RedIndex A B C rows.length) :=
    ((Finset.univ.sigma chunks) ×ˢ pieces).image fun x => ⟨x.1.1, x.1.2, x.2⟩
  have hmem : ∀ J ∈ inst, J.Q ∈ chunks J.ϱ ∧ J.P ∈ pieces := by
    intro J hJ
    obtain ⟨⟨⟨ϱ, Q⟩, P⟩, hx, rfl⟩ := Finset.mem_image.1 hJ
    simp only [Finset.mem_product, Finset.mem_sigma, Finset.mem_univ, true_and] at hx
    exact hx
  refine ⟨inst, ?_, ?_, ?_, ?_, ?_⟩
  · intro J hJ
    obtain ⟨hQ, hP⟩ := hmem J hJ
    exact ⟨(hch1 J.ϱ J.Q hQ).1,
      redInst_isLop I h J.ϱ J.Q J.P N D g hA hB hg1 (hp1 J.P hP).2 hr1, (hch1 J.ϱ J.Q hQ).2⟩
  · -- the count of instances
    have hsum : ∑ ϱ, (classOf I h ϱ).card = N ^ 2 := by
      have := Finset.card_eq_sum_card_fiberwise (f := fun q : A × B => h (I.wab q.1 q.2))
        (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
      rw [Finset.card_univ, Fintype.card_prod, hA, hB] at this
      rw [sq, this]
      rfl
    have hK : ∑ ϱ, (chunks ϱ).card ≤ ∑ ϱ, ((classOf I h ϱ).card + L - 1) / L :=
      Finset.sum_le_sum fun ϱ _ => hch3 ϱ
    have hKR : ((∑ ϱ, (chunks ϱ).card : ℕ) : ℝ) ≤ 2 * Real.sqrt D + 1 :=
      (Nat.cast_le.2 hK).trans (chunks_le N D rows.length _ hsum hD hDN hr1)
    have hinst := instances_le N D g (∑ ϱ, (chunks ϱ).card) hD hDN hg1 hg hKR
    have hpc : pieces.card ≤ (N + p - 1) / p := by
      rw [Finset.card_univ, hC] at hp3; exact hp3
    calc inst.card ≤ ((Finset.univ.sigma chunks) ×ˢ pieces).card := Finset.card_image_le
      _ = (∑ ϱ, (chunks ϱ).card) * pieces.card := by
          rw [Finset.card_product, Finset.card_sigma]
      _ ≤ (∑ ϱ, (chunks ϱ).card) * ((N + p - 1) / p) := Nat.mul_le_mul_left _ hpc
      _ ≤ 4 * N * g := hinst
  · intro J hJ J' hJ' hne
    rw [Finset.disjoint_left]
    intro c hc hc'
    exact hne ((hp2 c (Finset.mem_univ c)).unique ⟨(hmem J hJ).2, hc⟩ ⟨(hmem J' hJ').2, hc'⟩)
  · -- every query pair is scanned exactly once per piece
    intro J hJ q
    have hq : q ∈ classOf I h (h (I.wab q.1 q.2)) := by simp [classOf]
    obtain ⟨Q, ⟨hQ, hqQ⟩, huniq⟩ := hch2 _ q hq
    refine ⟨⟨h (I.wab q.1 q.2), Q, J.P⟩, ⟨Finset.mem_image.2 ⟨⟨⟨h (I.wab q.1 q.2), Q⟩, J.P⟩, ?_, rfl⟩,
      rfl, hqQ⟩, ?_⟩
    · simp [hQ, (hmem J hJ).2]
    · rintro ⟨ϱ', Q', P'⟩ ⟨hJ'', hP', hqQ'⟩
      obtain ⟨hQ', -⟩ := hmem _ hJ''
      simp only at hP' hqQ' hQ'
      have hϱ : ϱ' = h (I.wab q.1 q.2) := by
        have := (hch1 ϱ' Q' hQ').1 hqQ'
        simp only [classOf, Finset.mem_filter, Finset.mem_univ, true_and] at this
        exact this.symm
      subst hϱ hP'
      rw [huniq Q' ⟨hQ', hqQ'⟩]
  · constructor
    · rintro ⟨a, b, c, h0⟩
      have hab : (a, b) ∈ classOf I h (h (I.wab a b)) := by simp [classOf]
      obtain ⟨Q, ⟨hQ, habQ⟩, -⟩ := hch2 _ (a, b) hab
      obtain ⟨P, ⟨hP, hcP⟩, -⟩ := hp2 c (Finset.mem_univ c)
      refine ⟨⟨h (I.wab a b), Q, P⟩, Finset.mem_image.2 ⟨⟨⟨h (I.wab a b), Q⟩, P⟩, ?_, rfl⟩,
        (a, b), habQ, zero_triangle_caught I h Q P a b c habQ hcP h0, c, hcP, h0⟩
      simp [hQ, hP]
    · rintro ⟨J, -, q, -, -, c, -, h0⟩
      exact ⟨q.1, q.2, c, h0⟩

/-! ### (e) failed witness scans -/

/-- The failed scans for a family of pieces: `(a, b, k)` accepted (some `c ∈ P k` with
`h S = 0`) but with no zero triangle in `P k`. -/
noncomputable def failedScans {κ : Type*} [Fintype κ] (I : TriInst A B C d)
    (h : Vec d →ₗ[ZMod 2] Vec r) (P : κ → Finset C) : Finset (A × B × κ) :=
  Finset.univ.filter fun t =>
    (∃ c ∈ P t.2.2, h (I.S t.1 t.2.1 c) = 0) ∧ ∀ c ∈ P t.2.2, I.S t.1 t.2.1 c ≠ 0

theorem failedScans_card_le {κ : Type*} [Fintype κ] (I : TriInst A B C d)
    (h : Vec d →ₗ[ZMod 2] Vec r) (P : κ → Finset C)
    (hdisj : Pairwise fun k k' => Disjoint (P k) (P k')) :
    (failedScans I h P).card ≤ I.F h := by
  unfold TriInst.F
  apply Finset.card_le_card_of_forall_subsingleton
    (fun (t : A × B × κ) (u : A × B × C) => u.1 = t.1 ∧ u.2.1 = t.2.1 ∧ u.2.2 ∈ P t.2.2)
  · intro t ht
    obtain ⟨⟨c, hc, hhc⟩, hall⟩ := (Finset.mem_filter.1 ht).2
    exact ⟨(t.1, t.2.1, c), Finset.mem_filter.2 ⟨Finset.mem_univ _, hall c hc, hhc⟩,
      rfl, rfl, hc⟩
  · intro u _ t ht t' ht'
    obtain ⟨-, h1, h2, h3⟩ := ht
    obtain ⟨-, h1', h2', h3'⟩ := ht'
    have hk : t.2.2 = t'.2.2 := by
      by_contra hne
      exact Finset.disjoint_left.1 (hdisj hne) h3 h3'
    exact Prod.ext (h1.symm.trans h1') (Prod.ext (h2.symm.trans h2') hk)

end ThreeSumApsp.Remark23.General

/-! ### Bridges to the vocabulary of the statements -/

namespace ThreeSumApsp.Remark23

open TriInst (ofTriangleInstance)

variable {n d : ℕ} (T : TriangleInstance (Vec d) n)

theorem F_ofTriangleInstance {q : ℕ} (G : Vec d →ₗ[ZMod 2] Vec q) :
    (ofTriangleInstance T).F G = F T G :=
  rfl

theorem fpFamily_ofTriangleInstance : General.fpFamily (ofTriangleInstance T) = fpFamily T :=
  rfl

theorem classOf_ofTriangleInstance {r : ℕ} (h : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r) :
    General.classOf (ofTriangleInstance T) h ϱ = classOf T h ϱ :=
  rfl

theorem failedScans_ofTriangleInstance {r : ℕ} {κ : Type*} [Fintype κ]
    (h : Vec d →ₗ[ZMod 2] Vec r) (P : κ → Finset (Fin n)) :
    General.failedScans (ofTriangleInstance T) h P = failedScans T h P := by
  unfold General.failedScans Remark23.failedScans
  congr 1

/-- The instance of Theorem 8 as a `LopInstance`: a query pair lies in a triangle exactly if the
general instance accepts it. -/
theorem redInstance_inTriangle_iff {r : ℕ} (h : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r)
    (Q : Finset (Fin n × Fin n)) (P : Finset (Fin n)) (a b : Fin n) :
    (redInstance T h ϱ Q P).InTriangle a b ↔
      (General.redInst (ofTriangleInstance T) h ϱ Q P).Accepts a b := by
  constructor
  · rintro ⟨⟨⟨c, hc⟩, σ⟩, h1, h2⟩
    exact ⟨(c, σ), Finset.mem_product.2 ⟨hc, Finset.mem_univ _⟩, h1, h2⟩
  · rintro ⟨⟨c, σ⟩, hm, h1, h2⟩
    exact ⟨(⟨c, (Finset.mem_product.1 hm).1⟩, σ), h1, h2⟩

theorem card_M_redInstance {r : ℕ} (h : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r)
    (Q : Finset (Fin n × Fin n)) (P : Finset (Fin n)) :
    Fintype.card (redInstance T h ϱ Q P).M =
      (General.redInst (ofTriangleInstance T) h ϱ Q P).mid.card := by
  change Fintype.card ({c : Fin n // c ∈ P} × Vec r) = (P ×ˢ (Finset.univ : Finset (Vec r))).card
  rw [Fintype.card_prod, Fintype.card_coe, Finset.card_product, Finset.card_univ]

/-- The instance of Theorem 8 as a `LopInstance`: an instance of Lop(n, D) exactly if the general
instance is one. -/
theorem redInstance_middleAtMost_iff {r : ℕ} (h : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r)
    (Q : Finset (Fin n × Fin n)) (P : Finset (Fin n)) (D : ℕ) :
    (redInstance T h ϱ Q P).MiddleAtMost D ↔
      (General.redInst (ofTriangleInstance T) h ϱ Q P).IsLop n D := by
  unfold LopInstance.MiddleAtMost General.LopInst.IsLop
  rw [card_M_redInstance]
  simp

/-- The paper's `pieceSize D g = ⌈⌊√D⌋/g⌉` is the note's `⌈s/g⌉`, `s = ⌊√D⌋`. -/
theorem pieceSize_eq (D g : ℕ) : pieceSize D g = (Nat.sqrt D + g - 1) / g := by
  unfold pieceSize sOf
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp
  · rw [Nat.ceil_div_eq_ceilDiv _ hg, Nat.ceilDiv_eq_add_pred_div]

/-- Proof of Theorem 8: an instance whose piece has at most `pieceSize D g` vertices is an instance
of Lop(n, D), for `2^r ≤ √D`. -/
theorem redInstance_middleAtMost {r : ℕ} (h : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r)
    (Q : Finset (Fin n × Fin n)) (P : Finset (Fin n)) (D g : ℕ) (hg : 1 ≤ g)
    (hP : P.card ≤ pieceSize D g) (hr : (2 : ℝ) ^ r ≤ Real.sqrt D) :
    (redInstance T h ϱ Q P).MiddleAtMost D :=
  (redInstance_middleAtMost_iff T h ϱ Q P D).2 <|
    General.redInst_isLop _ h ϱ Q P n D g (by simp) (by simp) hg (pieceSize_eq D g ▸ hP) hr

/-- An index of the general proof as an index of the statement. -/
def General.RedIndex.toRedIndex {r : ℕ} (J : General.RedIndex (Fin n) (Fin n) (Fin n) r) :
    Remark23.RedIndex n r :=
  ⟨J.ϱ, J.Q, J.P⟩

theorem General.RedIndex.toRedIndex_injective {r : ℕ} :
    Function.Injective (General.RedIndex.toRedIndex (n := n) (r := r)) := by
  rintro ⟨ϱ, Q, P⟩ ⟨ϱ', Q', P'⟩ h
  simp only [General.RedIndex.toRedIndex, Remark23.RedIndex.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

end ThreeSumApsp.Remark23

namespace ThreeSumApsp

open Remark23 Remark23.TriInst

/-- The note's Theorem 8 (`PaperStatements.Remark_23_theorem_8`). -/
theorem remark_23_theorem_8 {n d D g : ℕ} (T : TriangleInstance (Vec d) n) (hD : 16 ≤ D)
    (hDN : D ≤ n) (hg1 : 1 ≤ g) (hg : (g : ℝ) ≤ Real.sqrt D)
    (rows : List (Vec d)) (hlen : rows.length = Nat.log 2 (Nat.sqrt D)) :
    ∃ inst : Finset (RedIndex n rows.length),
      (∀ J ∈ inst, J.Q ⊆ classOf T (rowsMap rows) J.ϱ ∧
        (redInstance T (rowsMap rows) J.ϱ J.Q J.P).MiddleAtMost D ∧ J.Q.card ≤ queryCap n D) ∧
      inst.card ≤ 4 * n * g ∧
      (∀ J ∈ inst, ∀ J' ∈ inst, J.P ≠ J'.P → Disjoint J.P J'.P) ∧
      (∀ J ∈ inst, ∀ p : Fin n × Fin n, ∃! J' ∈ inst, J'.P = J.P ∧ p ∈ J'.Q) ∧
      (T.HasZeroTriangle ↔
        ∃ J ∈ inst, ∃ p ∈ J.Q, (redInstance T (rowsMap rows) J.ϱ J.Q J.P).InTriangle p.1 p.2 ∧
          ∃ c ∈ J.P, T.S p.1 p.2 c = 0) := by
  obtain ⟨inst, h1, h2, h3, h4, h5⟩ := General.reduction_spec (ofTriangleInstance T) n D g
    (by simp) (by simp) (by simp) hD hDN hg1 hg rows hlen
  let f : General.RedIndex (Fin n) (Fin n) (Fin n) rows.length ↪ RedIndex n rows.length :=
    ⟨General.RedIndex.toRedIndex, General.RedIndex.toRedIndex_injective⟩
  refine ⟨inst.map f, ?_, ?_, ?_, ?_, ?_⟩
  · intro J' hJ'
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.1 hJ'
    obtain ⟨ha, hb, hc⟩ := h1 J hJ
    exact ⟨ha, (redInstance_middleAtMost_iff T _ _ _ _ D).2 hb, hc⟩
  · rw [Finset.card_map]
    exact h2
  · intro J₁ hJ₁ J₂ hJ₂ hne
    obtain ⟨K₁, hK₁, rfl⟩ := Finset.mem_map.1 hJ₁
    obtain ⟨K₂, hK₂, rfl⟩ := Finset.mem_map.1 hJ₂
    exact h3 K₁ hK₁ K₂ hK₂ hne
  · intro J' hJ' p
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.1 hJ'
    obtain ⟨K, ⟨hK, hKP, hpK⟩, huniq⟩ := h4 J hJ p
    refine ⟨f K, ⟨Finset.mem_map_of_mem f hK, hKP, hpK⟩, ?_⟩
    rintro K' ⟨hK', hK'P, hpK'⟩
    obtain ⟨K'', hK'', rfl⟩ := Finset.mem_map.1 hK'
    rw [huniq K'' ⟨hK'', hK'P, hpK'⟩]
  · rw [← hasZeroTriangle_ofTriangleInstance, h5]
    constructor
    · rintro ⟨J, hJ, p, hp, hacc, c, hc, h0⟩
      exact ⟨f J, Finset.mem_map_of_mem f hJ, p, hp,
        (redInstance_inTriangle_iff T _ _ _ _ _ _).2 hacc, c, hc, h0⟩
    · rintro ⟨J', hJ', p, hp, hacc, c, hc, h0⟩
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_map.1 hJ'
      exact ⟨J, hJ, p, hp, (redInstance_inTriangle_iff T _ _ _ _ _ _).1 hacc, c, hc, h0⟩

/-- Proof of the note's Theorem 8: minimizing `Z` (`PaperStatements.Remark_23_theorem_8_greedy_Z`). -/
theorem remark_23_theorem_8_greedy_Z {n d : ℕ} (T : TriangleInstance (Vec d) n)
    (E : Multiset (Vec d)) (rows : List (Vec d)) :
    IsGreedy E (fun l => (Z T (rowsMap l) : ℝ)) rows ↔
      IsGreedy E (surv (fpFamily T) (fun t => T.S t.1 t.2.1 t.2.2) (fun _ => 1)) rows := by
  have := General.isGreedy_Z_iff (ofTriangleInstance T) E rows
  simp only [Z_ofTriangleInstance] at this
  exact this

/-- Proof of the note's Theorem 8: the false positives
(`PaperStatements.Remark_23_theorem_8_false_positives`). -/
theorem remark_23_theorem_8_false_positives {n d D : ℕ} (T : TriangleInstance (Vec d) n)
    (hD : 16 ≤ D) (hDN : D ≤ n) (E : Multiset (Vec d)) (rows : List (Vec d))
    (hlen : rows.length = Nat.log 2 (Nat.sqrt D)) (hE : IsBiased (1 / rows.length) E)
    (hg : IsGreedy E (fun l => (Z T (rowsMap l) : ℝ)) rows) :
    (F T (rowsMap rows) : ℝ) ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * n ^ 3 ∧
    (F T (rowsMap rows) : ℝ) < 2 * Real.exp 1 * n ^ 3 / Real.sqrt D := by
  have hg' : IsGreedy E (fun l => ((ofTriangleInstance T).Z (rowsMap l) : ℝ)) rows := by
    simpa only [Z_ofTriangleInstance] using hg
  exact General.false_positives_le (ofTriangleInstance T) n D (by simp) (by simp) (by simp)
    hD hDN E rows hlen hE hg'

/-- Proof of the note's Theorem 8: the failed scans
(`PaperStatements.Remark_23_theorem_8_failed_scans`). -/
theorem remark_23_theorem_8_failed_scans {n d r : ℕ} {κ : Type*} [Fintype κ]
    (T : TriangleInstance (Vec d) n) (h : Vec d →ₗ[ZMod 2] Vec r) (P : κ → Finset (Fin n))
    (hdisj : Pairwise fun k k' => Disjoint (P k) (P k')) :
    (failedScans T h P).card ≤ F T h := by
  rw [← failedScans_ofTriangleInstance, ← F_ofTriangleInstance]
  exact General.failedScans_card_le (ofTriangleInstance T) h P hdisj

end ThreeSumApsp

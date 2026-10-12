/-
Parts of this file are adapted from `3sum-apsp/ThreeSumApsp/Sec4/{Boxes,Lemma27_28,Lemma29}.lean`:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ThinMatrixProducts.PartI.Leaves
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Lemma 7.1: balanced boxes

[ZT, Lemmas 27-29] on the `2L` levels of the squared construction, with the five terms of
Lemma 3.1 (four terms `P_ij` instead of nine). The proofs of `3sum-apsp` are ported to strings on
`Fin N`; for `N = L + L` the levels of the first half come first (`Fin.append`). Condition (iii)
("at most `m` symbols `P₀` or stars in each half") is added: the boxes of an output string satisfy
it because their stars and `P₀`'s lie in `Q`, which has `m` levels in each half; the dynamic program
keeps it because replacing a star by a term does not add a level with a star or `P₀`; and the count
uses the leaves with at most `m` symbols `P₀` in each half, `β'_{2m-f}` of them (Lemma 6.1(b)).
-/

namespace ThinMatrixProducts

namespace Sq

open Finset

variable {N : ℕ}

/-! ### Cubes and their leaves -/

@[simp]
theorem Cube.mem_leaves {π : Cube N} {τ : FLeaf N} :
    τ ∈ Cube.leaves π ↔ ∀ ℓ, π ℓ = .star ∨ π ℓ = .term (τ ℓ) := by
  rw [Cube.leaves, Finset.mem_filter]
  simp [Cube.HasLeaf]

theorem Cube.eq_of_mem_leaves {π : Cube N} {τ : FLeaf N} (hτ : τ ∈ Cube.leaves π) {ℓ : Fin N}
    {lam : Tm} (h : π ℓ = .term lam) : τ ℓ = lam := by
  have := Cube.mem_leaves.1 hτ ℓ
  rw [h] at this
  rcases this with h1 | h1
  · cases h1
  · exact (CSym.term.inj h1).symm

@[simp]
theorem Cube.mem_starLevels {π : Cube N} {ℓ : Fin N} :
    ℓ ∈ Cube.starLevels π ↔ π ℓ = .star := by simp [Cube.starLevels]

@[simp]
theorem Cube.mem_P0Levels {π : Cube N} {ℓ : Fin N} :
    ℓ ∈ Cube.P0Levels π ↔ π ℓ = .term .P0 := by simp [Cube.P0Levels]

@[simp]
theorem mem_P0Levels {τ : FLeaf N} {ℓ : Fin N} : ℓ ∈ P0Levels τ ↔ τ ℓ = .P0 := by
  simp [P0Levels]

theorem Cube.disjoint_starLevels_P0Levels (π : Cube N) :
    Disjoint (Cube.starLevels π) (Cube.P0Levels π) := by
  rw [disjoint_left]
  intro ℓ h1 h2
  rw [Cube.mem_starLevels] at h1
  rw [Cube.mem_P0Levels, h1] at h2
  cases h2

/-- The cube that agrees with `τ` except for stars at the levels of `F`. -/
def Cube.starAt (F : Finset (Fin N)) (τ : FLeaf N) : Cube N :=
  fun ℓ => if ℓ ∈ F then .star else .term (τ ℓ)

/-- The leaf obtained by replacing the stars of a cube with `P₀`. -/
def Cube.starsToP0 (π : Cube N) : FLeaf N := fun ℓ =>
  match π ℓ with
  | .term t => t
  | .star => .P0

theorem Cube.mem_leaves_starAt (F : Finset (Fin N)) (τ : FLeaf N) :
    τ ∈ Cube.leaves (Cube.starAt F τ) :=
  Cube.mem_leaves.2 fun ℓ => (em (ℓ ∈ F)).imp (if_pos ·) (if_neg ·)

@[simp]
theorem Cube.starLevels_starAt (F : Finset (Fin N)) (τ : FLeaf N) :
    Cube.starLevels (Cube.starAt F τ) = F := by
  ext ℓ
  by_cases h : ℓ ∈ F <;> simp [Cube.starAt, h]

@[simp]
theorem Cube.P0Levels_starAt (F : Finset (Fin N)) (τ : FLeaf N) :
    Cube.P0Levels (Cube.starAt F τ) = Sq.P0Levels τ \ F := by
  ext ℓ
  by_cases h : ℓ ∈ F <;> simp [Cube.starAt, h]

theorem Cube.starsToP0_starAt {F : Finset (Fin N)} {τ : FLeaf N} (h : F ⊆ Sq.P0Levels τ) :
    Cube.starsToP0 (Cube.starAt F τ) = τ := by
  funext ℓ
  unfold Cube.starsToP0 Cube.starAt
  by_cases hℓ : ℓ ∈ F
  · simp only [if_pos hℓ]
    exact (Sq.mem_P0Levels.1 (h hℓ)).symm
  · simp only [if_neg hℓ]

theorem Cube.starAt_starLevels_starsToP0 (π : Cube N) :
    Cube.starAt (Cube.starLevels π) (Cube.starsToP0 π) = π := by
  funext ℓ
  unfold Cube.starAt Cube.starsToP0
  cases h : π ℓ <;> simp [h]

theorem P0Levels_starsToP0 (π : Cube N) :
    P0Levels (Cube.starsToP0 π) = Cube.starLevels π ∪ Cube.P0Levels π := by
  ext ℓ
  rw [mem_P0Levels, mem_union, Cube.mem_starLevels, Cube.mem_P0Levels]
  unfold Cube.starsToP0
  cases h : π ℓ <;> simp

theorem card_P0Levels_starsToP0 (π : Cube N) :
    (P0Levels (Cube.starsToP0 π)).card = (Cube.starLevels π).card + (Cube.P0Levels π).card := by
  rw [P0Levels_starsToP0, card_union_of_disjoint (Cube.disjoint_starLevels_P0Levels π)]

theorem P0Levels_subset_of_mem_leaves {π : Cube N} {τ : FLeaf N} (hτ : τ ∈ Cube.leaves π) :
    P0Levels τ ⊆ Cube.P0Levels π ∪ Cube.starLevels π := by
  intro ℓ hℓ
  rw [mem_P0Levels] at hℓ
  rw [mem_union, Cube.mem_P0Levels, Cube.mem_starLevels, ← hℓ]
  exact (Cube.mem_leaves.1 hτ ℓ).symm

/-- Conditions (i) and (ii) of a box, for `M` inner levels. -/
def IsBox0 (M t : ℕ) (π : Cube N) : Prop :=
  (Cube.starLevels π).card + (Cube.P0Levels π).card ≤ M - t ∧
  ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ'

theorem le_order_of_mem_leaves {M t : ℕ} (ht : t ≤ M) {π : Cube N} (hπ : IsBox0 M t π)
    {τ : FLeaf N} (hτ : τ ∈ Cube.leaves π) : (t : ℤ) ≤ order M τ := by
  have h1 : (P0Levels τ).card ≤ M - t :=
    calc (P0Levels τ).card ≤ (Cube.P0Levels π ∪ Cube.starLevels π).card :=
          card_le_card (P0Levels_subset_of_mem_leaves hτ)
      _ ≤ (Cube.P0Levels π).card + (Cube.starLevels π).card := card_union_le _ _
      _ ≤ M - t := (add_comm _ _).trans_le hπ.1
  unfold order
  omega

/-! ### The `k` lowest levels of a set -/

theorem lowest_subset (k : ℕ) (S : Finset (Fin N)) : lowest k S ⊆ S := filter_subset _ _

lemma mem_lowest {k : ℕ} {S : Finset (Fin N)} {ℓ : Fin N} :
    ℓ ∈ lowest k S ↔ ℓ ∈ S ∧ (S.filter fun ℓ' => ℓ' < ℓ).card < k := by
  simp [lowest]

lemma card_below_strictMonoOn (S : Finset (Fin N)) :
    StrictMonoOn (fun ℓ => (S.filter fun x => x < ℓ).card) S := by
  intro ℓ hℓ ℓ' _ hlt
  refine card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩
  · exact mem_filter.2 ⟨(mem_filter.1 hx).1, (mem_filter.1 hx).2.trans hlt⟩
  · exact lt_irrefl ℓ (mem_filter.1 (hsub (mem_filter.2 ⟨hℓ, hlt⟩))).2

theorem lowest_lt {k : ℕ} {S : Finset (Fin N)} {ℓ ℓ' : Fin N} (hℓ : ℓ ∈ lowest k S)
    (hℓ' : ℓ' ∈ S \ lowest k S) : ℓ < ℓ' := by
  obtain ⟨hS, hbelow⟩ := mem_lowest.1 hℓ
  obtain ⟨hS', hnot⟩ := mem_sdiff.1 hℓ'
  by_contra hlt
  exact hnot (mem_lowest.2
    ⟨hS', ((card_below_strictMonoOn S).monotoneOn hS' hS (not_lt.1 hlt)).trans_lt hbelow⟩)

theorem eq_lowest_of_lt {S T : Finset (Fin N)} (hT : T ⊆ S)
    (h : ∀ ℓ ∈ T, ∀ ℓ' ∈ S \ T, ℓ < ℓ') : T = lowest T.card S := by
  ext ℓ
  rw [mem_lowest]
  constructor
  · refine fun hℓ => ⟨hT hℓ, card_lt_card ⟨fun x hx => ?_, fun hsub => ?_⟩⟩
    · by_contra hxT
      exact lt_asymm (mem_filter.1 hx).2 (h ℓ hℓ x (mem_sdiff.2 ⟨(mem_filter.1 hx).1, hxT⟩))
    · exact lt_irrefl ℓ (mem_filter.1 (hsub hℓ)).2
  · rintro ⟨hℓS, hcard⟩
    by_contra hℓT
    refine absurd (card_le_card fun x hx => ?_) (not_le.2 hcard)
    exact mem_filter.2 ⟨hT hx, h x hx ℓ (mem_sdiff.2 ⟨hℓS, hℓT⟩)⟩

lemma image_card_below (S : Finset (Fin N)) :
    (S.image fun ℓ => (S.filter fun x => x < ℓ).card) = range S.card := by
  refine eq_of_subset_of_card_le (fun n hn => ?_) ?_
  · obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.1 hn
    exact mem_range.2
      (card_lt_card ⟨filter_subset _ _, fun hsub => lt_irrefl ℓ (mem_filter.1 (hsub hℓ)).2⟩)
  · rw [card_image_of_injOn (card_below_strictMonoOn S).injOn, card_range]

theorem card_lowest (k : ℕ) (S : Finset (Fin N)) : (lowest k S).card = min k S.card := by
  have hinj := (card_below_strictMonoOn S).injOn.mono (coe_subset.2 (lowest_subset k S))
  have hrange : ((range S.card).filter fun n => n < k) = range (min k S.card) := by
    ext n
    simp only [mem_filter, mem_range, lt_min_iff, and_comm]
  rw [← card_image_of_injOn hinj, ← card_range (min k S.card), ← hrange, ← image_card_below,
    filter_image]
  rfl

/-! ### Replacing the lowest symbols `P₀` of a leaf by stars -/

def starLowest (e : ℕ) (τ : FLeaf N) : Cube N := Cube.starAt (lowest e (P0Levels τ)) τ

theorem starLevels_starLowest (e : ℕ) (τ : FLeaf N) :
    Cube.starLevels (starLowest e τ) = lowest e (P0Levels τ) :=
  Cube.starLevels_starAt _ τ

theorem P0Levels_starLowest (e : ℕ) (τ : FLeaf N) :
    Cube.P0Levels (starLowest e τ) = P0Levels τ \ lowest e (P0Levels τ) :=
  Cube.P0Levels_starAt _ τ

theorem starsToP0_starLowest (e : ℕ) (τ : FLeaf N) : Cube.starsToP0 (starLowest e τ) = τ :=
  Cube.starsToP0_starAt (lowest_subset _ _)

theorem eq_starLowest_starsToP0 (π : Cube N)
    (h : ∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ') :
    π = starLowest (Cube.starLevels π).card (Cube.starsToP0 π) := by
  have hlow : Cube.starLevels π =
      lowest (Cube.starLevels π).card (P0Levels (Cube.starsToP0 π)) := by
    refine eq_lowest_of_lt ?_ fun ℓ hℓ ℓ' hℓ' => h ℓ hℓ ℓ' ?_
    · rw [P0Levels_starsToP0]
      exact subset_union_left
    · rw [P0Levels_starsToP0, mem_sdiff, mem_union] at hℓ'
      tauto
  rw [starLowest, ← hlow, Cube.starAt_starLevels_starsToP0]

/-! ### Contributing leaves -/

lemma chi_ne_zero_iff' : ∀ (lam : Tm) (z : ZL), chi lam z ≠ 0 ↔ (z ≠ .z0 → lam = privTerm z) := by
  decide

lemma privTerm_ne_P0 : ∀ z : ZL, z ≠ .z0 → privTerm z ≠ .P0 := by decide

theorem mem_innerSet {w : FOut N} {ℓ : Fin N} : ℓ ∈ innerSet w ↔ w ℓ = .z0 := by
  simp [innerSet]

lemma contrib_iff (w : FOut N) (τ : FLeaf N) :
    Contrib τ w ↔ ∀ ℓ, ℓ ∉ innerSet w → τ ℓ = privTerm (w ℓ) := by
  refine forall_congr' fun ℓ => ?_
  rw [chi_ne_zero_iff', mem_innerSet]

/-- `Z`: the levels of `Q` at which `τ` has `P₀`. -/
def Zof (Q : Finset (Fin N)) (τ : FLeaf N) : Finset (Fin N) := Q.filter fun ℓ => τ ℓ = .P0

lemma Zof_subset (Q : Finset (Fin N)) (τ : FLeaf N) : Zof Q τ ⊆ Q := filter_subset _ _

lemma P0Levels_subset_innerSet {w : FOut N} {τ : FLeaf N} (hτ : Contrib τ w) :
    P0Levels τ ⊆ innerSet w := by
  intro ℓ hℓ
  by_contra hQ
  have := (contrib_iff w τ).1 hτ ℓ hQ
  rw [mem_P0Levels] at hℓ
  exact privTerm_ne_P0 _ (fun h => hQ (mem_innerSet.2 h)) (this ▸ hℓ)

lemma P0Levels_eq_Zof (w : FOut N) (τ : FLeaf N) (hτ : Contrib τ w) :
    P0Levels τ = Zof (innerSet w) τ := by
  ext ℓ
  rw [Zof, mem_filter, mem_P0Levels]
  exact ⟨fun h => ⟨P0Levels_subset_innerSet hτ (mem_P0Levels.2 h), h⟩, fun h => h.2⟩

theorem order_eq_sub_card_Zof (M : ℕ) (w : FOut N) (τ : FLeaf N) (hτ : Contrib τ w) :
    order M τ = (M : ℤ) - ((Zof (innerSet w) τ).card : ℤ) := by
  rw [order, P0Levels_eq_Zof w τ hτ]

lemma card_Zof_le {M t : ℕ} {w : FOut N} {τ : FLeaf N} (hτ : Contrib τ w)
    (hord : (t : ℤ) ≤ order M τ) : (Zof (innerSet w) τ).card ≤ M - t := by
  have := order_eq_sub_card_Zof M w τ hτ
  omega

lemma order_nonneg {M : ℕ} {w : FOut N} (hw : (innerSet w).card = M) {τ : FLeaf N}
    (hτ : Contrib τ w) : 0 ≤ order M τ := by
  have := card_le_card (P0Levels_subset_innerSet hτ)
  unfold order
  omega

/-! ### The sets `V` and `F_V` -/

theorem Vof_subset (M t : ℕ) {Q Z : Finset (Fin N)} (hZ : Z ⊆ Q) : Vof M t Q Z ⊆ Q :=
  union_subset hZ ((lowest_subset _ _).trans sdiff_subset)

theorem card_Vof {M t : ℕ} (ht : t ≤ M) {Q Z : Finset (Fin N)} (hQ : Q.card = M) (hZ : Z ⊆ Q)
    (hZc : Z.card ≤ M - t) : (Vof M t Q Z).card = M - t := by
  have hdisj : Disjoint Z (lowest (M - t - Z.card) (Q \ Z)) :=
    disjoint_of_subset_right (lowest_subset _ _) disjoint_sdiff
  rw [Vof, card_union_of_disjoint hdisj, card_lowest, card_sdiff_of_subset hZ, hQ]
  omega

lemma Vof_sdiff_lt (M t : ℕ) (Q Z : Finset (Fin N)) :
    ∀ ℓ ∈ Vof M t Q Z \ Z, ∀ ℓ' ∈ Q \ Vof M t Q Z, ℓ < ℓ' := by
  intro ℓ hℓ ℓ' hℓ'
  obtain ⟨hV, hZ⟩ := mem_sdiff.1 hℓ
  obtain ⟨hQ', hV'⟩ := mem_sdiff.1 hℓ'
  obtain ⟨hZ', hlow'⟩ := not_or.1 (mt mem_union.2 hV')
  exact lowest_lt ((mem_union.1 hV).resolve_left hZ)
    (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hQ', hZ'⟩, hlow'⟩)

theorem FV_subset (Q V : Finset (Fin N)) : FV Q V ⊆ V := by
  intro ℓ hℓ
  by_contra hV
  exact lt_irrefl ℓ ((mem_filter.1 hℓ).2 ℓ (mem_sdiff.2 ⟨(mem_filter.1 hℓ).1, hV⟩))

lemma mem_FV_of_le {Q V : Finset (Fin N)} {ℓ ℓ' : Fin N} (hℓ : ℓ ∈ FV Q V)
    (hℓ' : ℓ' ∈ Q) (hle : ℓ' ≤ ℓ) : ℓ' ∈ FV Q V :=
  mem_filter.2 ⟨hℓ', fun x hx => hle.trans_lt ((mem_filter.1 hℓ).2 x hx)⟩

lemma sdiff_FV_subset_iff {Q V Z : Finset (Fin N)} (hV : V ⊆ Q) :
    V \ FV Q V ⊆ Z ↔ ∀ ℓ ∈ V \ Z, ∀ ℓ' ∈ Q \ V, ℓ < ℓ' := by
  constructor
  · intro h ℓ hℓ ℓ' hℓ'
    obtain ⟨hℓV, hℓZ⟩ := mem_sdiff.1 hℓ
    have hℓF : ℓ ∈ FV Q V := by
      by_contra hF
      exact hℓZ (h (mem_sdiff.2 ⟨hℓV, hF⟩))
    exact (mem_filter.1 hℓF).2 ℓ' hℓ'
  · intro h ℓ hℓ
    obtain ⟨hℓV, hℓF⟩ := mem_sdiff.1 hℓ
    by_contra hZ
    exact hℓF (mem_filter.2 ⟨hV hℓV, h ℓ (mem_sdiff.2 ⟨hℓV, hZ⟩)⟩)

/-! ### The sets `𝓑_V` -/

section BVsec

variable {w : FOut N} {V : Finset (Fin N)} {π : Cube N} {ℓ : Fin N}

lemma BV_star (hπ : π ∈ BV w V) (hℓ : ℓ ∈ FV (innerSet w) V) : π ℓ = .star :=
  ((mem_filter.1 hπ).2 ℓ).1 hℓ

lemma BV_P0 (hπ : π ∈ BV w V) (hℓ : ℓ ∈ V \ FV (innerSet w) V) : π ℓ = .term .P0 :=
  ((mem_filter.1 hπ).2 ℓ).2.1 hℓ

lemma BV_four (hπ : π ∈ BV w V) (hℓ : ℓ ∈ innerSet w \ V) : ∃ i j, π ℓ = .term (.P i j) :=
  ((mem_filter.1 hπ).2 ℓ).2.2.1 hℓ

lemma BV_outside (hπ : π ∈ BV w V) (hℓ : ℓ ∉ innerSet w) : π ℓ = .term (privTerm (w ℓ)) :=
  ((mem_filter.1 hπ).2 ℓ).2.2.2 hℓ

lemma level_cases (Q V : Finset (Fin N)) (ℓ : Fin N) :
    ℓ ∈ FV Q V ∨ ℓ ∈ V \ FV Q V ∨ ℓ ∈ Q \ V ∨ ℓ ∉ Q := by
  simp only [mem_sdiff]
  tauto

theorem BV_starLevels (hπ : π ∈ BV w V) : Cube.starLevels π = FV (innerSet w) V := by
  ext ℓ
  rw [Cube.mem_starLevels]
  refine ⟨fun h => ?_, BV_star hπ⟩
  rcases level_cases (innerSet w) V ℓ with hℓ | hℓ | hℓ | hℓ
  · exact hℓ
  · simp [BV_P0 hπ hℓ] at h
  · obtain ⟨i, j, hij⟩ := BV_four hπ hℓ
    simp [hij] at h
  · simp [BV_outside hπ hℓ] at h

theorem BV_P0Levels (hπ : π ∈ BV w V) : Cube.P0Levels π = V \ FV (innerSet w) V := by
  ext ℓ
  rw [Cube.mem_P0Levels]
  refine ⟨fun h => ?_, BV_P0 hπ⟩
  rcases level_cases (innerSet w) V ℓ with hℓ | hℓ | hℓ | hℓ
  · simp [BV_star hπ hℓ] at h
  · exact hℓ
  · obtain ⟨i, j, hij⟩ := BV_four hπ hℓ
    simp [hij] at h
  · rw [BV_outside hπ hℓ] at h
    exact absurd (CSym.term.inj h) (privTerm_ne_P0 _ fun h' => hℓ (mem_innerSet.2 h'))

theorem BV_starLevels_union_P0Levels (hπ : π ∈ BV w V) (hV : V ⊆ innerSet w) :
    Cube.starLevels π ∪ Cube.P0Levels π = V := by
  rw [BV_starLevels hπ, BV_P0Levels hπ, union_sdiff_of_subset (FV_subset _ _)]

lemma BV_ext {π' : Cube N} (hπ : π ∈ BV w V) (hπ' : π' ∈ BV w V)
    (h : ∀ ℓ ∈ innerSet w \ V, π ℓ = π' ℓ) : π = π' := by
  funext ℓ
  rcases level_cases (innerSet w) V ℓ with hℓ | hℓ | hℓ | hℓ
  · rw [BV_star hπ hℓ, BV_star hπ' hℓ]
  · rw [BV_P0 hπ hℓ, BV_P0 hπ' hℓ]
  · exact h ℓ hℓ
  · rw [BV_outside hπ hℓ, BV_outside hπ' hℓ]

lemma BV_eq_term_of_leaf (hπ : π ∈ BV w V) {τ : FLeaf N} (hτ : τ ∈ Cube.leaves π)
    (hℓ : ℓ ∈ innerSet w \ V) : π ℓ = .term (τ ℓ) := by
  obtain ⟨i, j, hij⟩ := BV_four hπ hℓ
  rw [hij, Cube.eq_of_mem_leaves hτ hij]

end BVsec

def allowed (w : FOut N) (V : Finset (Fin N)) (ℓ : Fin N) : Finset CSym :=
  univ.filter fun s =>
    (ℓ ∈ FV (innerSet w) V → s = .star) ∧
    (ℓ ∈ V \ FV (innerSet w) V → s = .term .P0) ∧
    (ℓ ∈ innerSet w \ V → ∃ i j, s = .term (.P i j)) ∧
    (ℓ ∉ innerSet w → s = .term (privTerm (w ℓ)))

lemma BV_eq_piFinset (w : FOut N) (V : Finset (Fin N)) :
    BV w V = Fintype.piFinset (allowed w V) := by
  ext π
  simp [BV, allowed, Fintype.mem_piFinset]

lemma card_allowed (w : FOut N) (V : Finset (Fin N)) (hV : V ⊆ innerSet w) (ℓ : Fin N) :
    (allowed w V ℓ).card = if ℓ ∈ innerSet w \ V then 4 else 1 := by
  have hfour :
      (univ.filter fun s : CSym => ∃ i j, s = .term (.P i j)).card = 4 := by decide
  have hFV := @FV_subset N (innerSet w) V ℓ
  have hVQ := @hV ℓ
  unfold allowed
  by_cases hF : ℓ ∈ FV (innerSet w) V
  · simp [hF, hFV hF, hVQ (hFV hF), filter_eq']
  by_cases hℓV : ℓ ∈ V
  · simp [hF, hℓV, hVQ hℓV, filter_eq']
  by_cases hℓQ : ℓ ∈ innerSet w
  · simp only [hF, hℓV, hℓQ, mem_sdiff, not_false_eq_true, and_self, if_true, IsEmpty.forall_iff,
      true_and, not_true_eq_false, forall_const, and_true]
    exact hfour
  · simp [hF, hℓV, hℓQ, filter_eq']

theorem card_BV (M t : ℕ) (ht : t ≤ M) (w : FOut N) (hw : (innerSet w).card = M)
    (V : Finset (Fin N)) (hV : V ∈ Vsets M t w) : (BV w V).card = 4 ^ t := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  rw [BV_eq_piFinset w V, Fintype.card_piFinset]
  simp only [card_allowed w V hVQ]
  rw [prod_ite_mem, univ_inter, prod_const, card_sdiff_of_subset hVQ, hw, hVc,
    Nat.sub_sub_self ht]

theorem BV_isBox0 {M t : ℕ} {w : FOut N} {V : Finset (Fin N)} (hV : V ∈ Vsets M t w)
    {π : Cube N} (hπ : π ∈ BV w V) : IsBox0 M t π := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  rw [IsBox0, BV_starLevels hπ, BV_P0Levels hπ, add_comm,
    card_sdiff_add_card_eq_card (FV_subset _ _)]
  refine ⟨hVc.le, fun ℓ hℓ ℓ' hℓ' => ?_⟩
  obtain ⟨hℓ'V, hℓ'F⟩ := mem_sdiff.1 hℓ'
  by_contra hlt
  exact hℓ'F (mem_FV_of_le hℓ (hVQ hℓ'V) (not_lt.1 hlt))

theorem BV_pairwiseDisjoint (M t : ℕ) (w : FOut N) :
    ((Vsets M t w : Finset (Finset (Fin N))) : Set (Finset (Fin N))).PairwiseDisjoint (BV w) :=
  fun V hV V' hV' hne => disjoint_left.2 fun _ hπ hπ' =>
    hne ((BV_starLevels_union_P0Levels hπ (mem_powersetCard.1 hV).1).symm.trans
      (BV_starLevels_union_P0Levels hπ' (mem_powersetCard.1 hV').1))

lemma starAt_mem_BV {w : FOut N} {V : Finset (Fin N)} {τ : FLeaf N}
    (hτ : Contrib τ w) (hVZ : V \ FV (innerSet w) V ⊆ Zof (innerSet w) τ)
    (hZV : Zof (innerSet w) τ ⊆ V) : Cube.starAt (FV (innerSet w) V) τ ∈ BV w V := by
  refine mem_filter.2
    ⟨mem_univ _, fun ℓ => ⟨fun hF => if_pos hF, fun hVF => ?_, fun hQV => ?_, fun hQ => ?_⟩⟩
  · rw [Cube.starAt, if_neg (mem_sdiff.1 hVF).2, (mem_filter.1 (hVZ hVF)).2]
  · obtain ⟨hQ, hV⟩ := mem_sdiff.1 hQV
    rw [Cube.starAt, if_neg fun hF => hV (FV_subset _ _ hF)]
    cases hterm : τ ℓ with
    | P i j => exact ⟨i, j, rfl⟩
    | P0 => exact absurd (hZV (mem_filter.2 ⟨hQ, hterm⟩)) hV
  · rw [Cube.starAt, if_neg fun hF : ℓ ∈ FV (innerSet w) V => hQ (mem_filter.1 hF).1,
      (contrib_iff w τ).1 hτ ℓ hQ]

def boxOfLeaf (M t : ℕ) (w : FOut N) (τ : FLeaf N) : Cube N :=
  Cube.starAt (FV (innerSet w) (Vof M t (innerSet w) (Zof (innerSet w) τ))) τ

theorem mem_leaves_boxOfLeaf (M t : ℕ) (w : FOut N) (τ : FLeaf N) :
    τ ∈ Cube.leaves (boxOfLeaf M t w τ) :=
  Cube.mem_leaves_starAt _ τ

theorem boxOfLeaf_mem_BV (M t : ℕ) {w : FOut N} {τ : FLeaf N} (hτ : Contrib τ w) :
    boxOfLeaf M t w τ ∈ BV w (Vof M t (innerSet w) (Zof (innerSet w) τ)) :=
  starAt_mem_BV hτ
    ((sdiff_FV_subset_iff (Vof_subset M t (Zof_subset _ τ))).2 (Vof_sdiff_lt M t _ _))
    subset_union_left

theorem exists_mem_BV_leaf_iff {w : FOut N} {V : Finset (Fin N)} (hV : V ⊆ innerSet w)
    {τ : FLeaf N} (hτ : Contrib τ w) :
    (∃ π ∈ BV w V, τ ∈ Cube.leaves π) ↔
      V \ FV (innerSet w) V ⊆ Zof (innerSet w) τ ∧ Zof (innerSet w) τ ⊆ V := by
  constructor
  · rintro ⟨π, hπ, hτπ⟩
    refine ⟨fun ℓ hℓ => mem_filter.2 ⟨hV (mem_sdiff.1 hℓ).1, ?_⟩, fun ℓ hℓ => ?_⟩
    · exact Cube.eq_of_mem_leaves hτπ (BV_P0 hπ hℓ)
    · by_contra hℓV
      obtain ⟨hℓQ, hterm⟩ := mem_filter.1 hℓ
      obtain ⟨i, j, hij⟩ := BV_four hπ (mem_sdiff.2 ⟨hℓQ, hℓV⟩)
      simp [Cube.eq_of_mem_leaves hτπ hij] at hterm
  · exact fun ⟨hVZ, hZV⟩ => ⟨_, starAt_mem_BV hτ hVZ hZV, Cube.mem_leaves_starAt _ τ⟩

theorem BV_leaf_unique {w : FOut N} {V : Finset (Fin N)} {τ : FLeaf N} {π π' : Cube N}
    (hπ : π ∈ BV w V) (hτπ : τ ∈ Cube.leaves π) (hπ' : π' ∈ BV w V)
    (hτπ' : τ ∈ Cube.leaves π') : π = π' :=
  BV_ext hπ hπ' fun _ hℓ =>
    (BV_eq_term_of_leaf hπ hτπ hℓ).trans (BV_eq_term_of_leaf hπ' hτπ' hℓ).symm

/-! ### [ZT, Lemma 27] -/

theorem lemma_27 (M t : ℕ) (ht : t ≤ M) (Q Z : Finset (Fin N)) (hQ : Q.card = M)
    (hZ : Z ⊆ Q) (hZc : Z.card ≤ M - t) (V : Finset (Fin N)) :
    (V ⊆ Q ∧ V.card = M - t ∧ V \ FV Q V ⊆ Z ∧ Z ⊆ V) ↔ V = Vof M t Q Z := by
  constructor
  · rintro ⟨hVQ, hVc, hVZ, hZV⟩
    have hrest : (Q \ Z) \ (V \ Z) = Q \ V := sdiff_sdiff_sdiff_cancel_right hZV
    have hlow := eq_lowest_of_lt (sdiff_subset_sdiff hVQ (le_refl Z))
      (hrest ▸ (sdiff_FV_subset_iff hVQ).1 hVZ)
    rw [card_sdiff_of_subset hZV, hVc] at hlow
    rw [Vof, ← hlow, union_sdiff_of_subset hZV]
  · rintro rfl
    have hVQ := Vof_subset M t hZ
    exact ⟨hVQ, card_Vof ht hQ hZ hZc, (sdiff_FV_subset_iff hVQ).2 (Vof_sdiff_lt M t Q Z),
      subset_union_left⟩

/-! ### [ZT, Lemma 28] -/

theorem lemma_28_leaves (M t : ℕ) (ht : t ≤ M) (w : FOut N) (hw : (innerSet w).card = M)
    (τ : FLeaf N) :
    (Contrib τ w ∧ (t : ℤ) ≤ order M τ) ↔
      ∃ π ∈ (Vsets M t w).biUnion (BV w), τ ∈ Cube.leaves π := by
  constructor
  · rintro ⟨hτ, hord⟩
    refine ⟨boxOfLeaf M t w τ, mem_biUnion.2 ⟨_, mem_powersetCard.2 ?_, boxOfLeaf_mem_BV M t hτ⟩,
      mem_leaves_boxOfLeaf M t w τ⟩
    exact ⟨Vof_subset M t (Zof_subset _ τ),
      card_Vof ht hw (Zof_subset _ τ) (card_Zof_le hτ hord)⟩
  · rintro ⟨π, hπ, hτπ⟩
    obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
    exact ⟨(contrib_iff w τ).2 fun ℓ hℓ => Cube.eq_of_mem_leaves hτπ (BV_outside hπV hℓ),
      le_order_of_mem_leaves ht (BV_isBox0 hV hπV) hτπ⟩

lemma eq_Vof_of_mem_leaves {M t : ℕ} (ht : t ≤ M) {w : FOut N}
    (hw : (innerSet w).card = M) {τ : FLeaf N} (hτ : Contrib τ w)
    (hord : (t : ℤ) ≤ order M τ) {V : Finset (Fin N)} (hV : V ∈ Vsets M t w) {π : Cube N}
    (hπ : π ∈ BV w V) (hτπ : τ ∈ Cube.leaves π) :
    V = Vof M t (innerSet w) (Zof (innerSet w) τ) := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  obtain ⟨hVZ, hZV⟩ := (exists_mem_BV_leaf_iff hVQ hτ).1 ⟨π, hπ, hτπ⟩
  exact (lemma_27 M t ht _ _ hw (Zof_subset _ τ) (card_Zof_le hτ hord) V).1 ⟨hVQ, hVc, hVZ, hZV⟩

theorem lemma_28_unique (M t : ℕ) (ht : t ≤ M) (w : FOut N) (hw : (innerSet w).card = M)
    (τ : FLeaf N) (hτ : Contrib τ w) (hord : (t : ℤ) ≤ order M τ) :
    ∃! π : Cube N, π ∈ (Vsets M t w).biUnion (BV w) ∧ τ ∈ Cube.leaves π := by
  obtain ⟨π, hπ, hτπ⟩ := (lemma_28_leaves M t ht w hw τ).1 ⟨hτ, hord⟩
  refine ⟨π, ⟨hπ, hτπ⟩, ?_⟩
  rintro π' ⟨hπ', hτπ'⟩
  obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
  obtain ⟨V', hV', hπV'⟩ := mem_biUnion.1 hπ'
  obtain rfl : V' = V := (eq_Vof_of_mem_leaves ht hw hτ hord hV' hπV' hτπ').trans
    (eq_Vof_of_mem_leaves ht hw hτ hord hV hπV hτπ).symm
  exact BV_leaf_unique hπV' hτπ' hπV hτπ

theorem sum_contributing (M t : ℕ) (ht : t ≤ M) (w : FOut N) (hw : (innerSet w).card = M)
    (g : FLeaf N → ℤ) :
    ∑ τ : FLeaf N with Contrib τ w, g τ =
      ∑ τ ∈ lowLeaves M t w, g τ + ∑ V ∈ Vsets M t w, ∑ π ∈ BV w V, Cube.val g π := by
  have hdisjoint :
      (((Vsets M t w).biUnion (BV w) : Finset (Cube N)) : Set (Cube N)).PairwiseDisjoint
        Cube.leaves := by
    intro π hπ π' hπ' hne
    rw [Function.onFun, disjoint_left]
    intro τ hτ hτ'
    obtain ⟨hc, hord⟩ := (lemma_28_leaves M t ht w hw τ).2 ⟨π, hπ, hτ⟩
    exact hne ((lemma_28_unique M t ht w hw τ hc hord).unique ⟨hπ, hτ⟩ ⟨hπ', hτ'⟩)
  have hhigh : ((Vsets M t w).biUnion (BV w)).biUnion Cube.leaves =
      univ.filter fun τ : FLeaf N => Contrib τ w ∧ ¬ order M τ < (t : ℤ) := by
    ext τ
    rw [mem_biUnion, mem_filter, not_lt, ← lemma_28_leaves M t ht w hw τ]
    simp
  simp only [Cube.val]
  rw [← sum_biUnion (BV_pairwiseDisjoint M t w), ← sum_biUnion hdisjoint, hhigh, lowLeaves,
    ← filter_filter, ← filter_filter, sum_filter_add_sum_filter_not]

lemma lowLeaves_eq_biUnion (M t : ℕ) (w : FOut N) (hw : (innerSet w).card = M) :
    lowLeaves M t w = (range t).biUnion fun d =>
      univ.filter fun τ : FLeaf N => Contrib τ w ∧ order M τ = d := by
  ext τ
  simp only [lowLeaves, mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
  constructor
  · rintro ⟨hτ, hlt⟩
    have hnonneg := order_nonneg hw hτ
    exact ⟨(order M τ).toNat, by omega, hτ, (Int.toNat_of_nonneg hnonneg).symm⟩
  · rintro ⟨d, hd, hτ, heq⟩
    exact ⟨hτ, by omega⟩

/-! ### The two halves -/

variable {L : ℕ}

lemma card_inter_half1 (S : Finset (Fin (L + L))) :
    (S ∩ half1 L).card = (univ.filter fun i : Fin L => Fin.castAdd L i ∈ S).card := by
  have : S ∩ half1 L = univ.filter fun ℓ : Fin (L + L) => ℓ ∈ S ∧ (ℓ : ℕ) < L := by
    ext; simp [half1]
  rw [this, card_filter, Fin.sum_univ_add, card_filter]
  simp

lemma card_sdiff_half1 (S : Finset (Fin (L + L))) :
    (S \ half1 L).card = (univ.filter fun i : Fin L => Fin.natAdd L i ∈ S).card := by
  have : S \ half1 L = univ.filter fun ℓ : Fin (L + L) => ℓ ∈ S ∧ ¬ (ℓ : ℕ) < L := by
    ext; simp [half1]
  rw [this, card_filter, Fin.sum_univ_add, card_filter]
  simp

lemma card_split (S : Finset (Fin (L + L))) :
    S.card = (S ∩ half1 L).card + (S \ half1 L).card := by
  have := card_sdiff_add_card_inter S (half1 L)
  omega

lemma innerSet_inter (w : OutStr L) : (innerSet (flatOut w) ∩ half1 L).card = (QZ w.1).card := by
  rw [card_inter_half1]; unfold innerSet flatOut QZ; simp [Fin.append_left]

lemma innerSet_sdiff (w : OutStr L) : (innerSet (flatOut w) \ half1 L).card = (QZ w.2).card := by
  rw [card_sdiff_half1]; unfold innerSet flatOut QZ; simp only [Finset.mem_filter, mem_univ, true_and, Fin.append_right]

lemma card_innerSet (w : OutStr L) :
    (innerSet (flatOut w)).card = (QZ w.1).card + (QZ w.2).card := by
  rw [card_split, innerSet_inter, innerSet_sdiff]

lemma P0_inter (τ : Leaf L) : (P0Levels (flatLeaf τ) ∩ half1 L).card = numP0 τ.1 := by
  rw [card_inter_half1]; unfold P0Levels flatLeaf numP0; simp [Fin.append_left]

lemma P0_sdiff (τ : Leaf L) : (P0Levels (flatLeaf τ) \ half1 L).card = numP0 τ.2 := by
  rw [card_sdiff_half1]; unfold P0Levels flatLeaf numP0; simp only [Finset.mem_filter, mem_univ, true_and, Fin.append_right]

lemma card_P0Levels_flat (τ : Leaf L) :
    (P0Levels (flatLeaf τ)).card = numP0 τ.1 + numP0 τ.2 := by
  rw [card_split, P0_inter, P0_sdiff]

lemma contrib_flat (τ : Leaf L) (w : OutStr L) :
    Contributes τ w ↔ Contrib (flatLeaf τ) (flatOut w) := by
  rw [Contrib, Fin.forall_fin_add, Contributes, forall_and]
  simp only [flatLeaf, flatOut, Fin.append_left, Fin.append_right]

lemma order_flat (m : ℕ) (τ : Leaf L) : ThinMatrixProducts.order m τ = order (2 * m) (flatLeaf τ) := by
  rw [ThinMatrixProducts.order, order, card_P0Levels_flat]
  push_cast
  ring

/-- The equivalence of leaves with flattened leaves. -/
def flatEquiv (L : ℕ) : Leaf L ≃ FLeaf (L + L) := Fin.appendEquiv L L

lemma flatEquiv_apply (τ : Leaf L) : flatEquiv L τ = flatLeaf τ := rfl

lemma card_contrib_order (w : OutStr L) {m : ℕ} (hw1 : (QZ w.1).card = m)
    (hw2 : (QZ w.2).card = m) (d : ℕ) :
    (univ.filter fun τ : FLeaf (L + L) => Contrib τ (flatOut w) ∧ order (2 * m) τ = d).card
      = alpha' m d := by
  rw [← lemma_6_1_a w hw1 hw2 d]
  symm
  refine card_equiv (flatEquiv L) fun τ => ?_
  simp only [mem_filter, mem_univ, true_and, flatEquiv_apply, contrib_flat, order_flat]

end Sq

open Finset Sq

theorem lemma_7_1_a : Lemma_7_1_a := by
  intro L m t ht w hw1 hw2
  have hW : (innerSet (flatOut w)).card = 2 * m := by rw [card_innerSet, hw1, hw2]; ring
  refine ⟨lemma_28_leaves (2 * m) t ht _ hW, lemma_28_unique (2 * m) t ht _ hW,
    sum_contributing (2 * m) t ht _ hW, ?_, ?_, ?_⟩
  · rw [lowLeaves_eq_biUnion (2 * m) t _ hW, card_biUnion]
    · exact sum_congr rfl fun d _ => card_contrib_order w hw1 hw2 d
    · intro d _ d' _ hne
      rw [Function.onFun, disjoint_left]
      intro τ hd hd'
      exact hne (by exact_mod_cast (mem_filter.1 hd).2.2.symm.trans (mem_filter.1 hd').2.2)
  · rw [card_biUnion (BV_pairwiseDisjoint (2 * m) t _),
      sum_congr rfl fun V hV => card_BV (2 * m) t ht _ hW V hV, sum_const, Vsets,
      card_powersetCard, hW, Nat.choose_symm ht, smul_eq_mul, alpha']
  · intro V hV π hπ
    obtain ⟨hVQ, -⟩ := mem_powersetCard.1 hV
    obtain ⟨h1, h2⟩ := BV_isBox0 hV hπ
    refine ⟨h1, h2, ?_, ?_⟩
    · rw [BV_starLevels_union_P0Levels hπ hVQ, ← hw1, ← innerSet_inter]
      exact card_le_card (inter_subset_inter_right hVQ)
    · rw [BV_starLevels_union_P0Levels hπ hVQ, ← hw2, ← innerSet_sdiff]
      exact card_le_card (sdiff_subset_sdiff hVQ le_rfl)

theorem lemma_7_1_a_link : Lemma_7_1_a_link := by
  intro L m a b w
  refine ⟨?_, fun τ => contrib_flat τ w, fun τ => order_flat m τ⟩
  simp only [Mult]
  exact sum_comm

/-! ### Lemma 7.1(b) -/

namespace Sq

open Finset

variable {L : ℕ}

@[simp]
theorem mem_boxes {m t : ℕ} {π : Cube (L + L)} : π ∈ boxes L m t ↔ IsBox L m t π := by
  simp [boxes]

/-- The leaves with `f` symbols `P₀`, at most `m` in each half. -/
def balLeaves (L m f : ℕ) : Finset (FLeaf (L + L)) :=
  univ.filter fun τ => (P0Levels τ).card = f ∧ (P0Levels τ ∩ half1 L).card ≤ m ∧
    (P0Levels τ \ half1 L).card ≤ m

lemma card_balLeaves {m f : ℕ} (hmL : m ≤ L) (hf : f ≤ 2 * m) :
    (balLeaves L m f).card = beta' L m (2 * m - f) := by
  rw [← lemma_6_1_b_count hmL (2 * m - f)]
  symm
  refine card_equiv (flatEquiv L) fun τ => ?_
  simp only [balLeaves, mem_filter, mem_univ, true_and]
  rw [flatEquiv_apply, P0_inter, P0_sdiff, card_P0Levels_flat]
  unfold ThinMatrixProducts.order
  constructor
  · rintro ⟨h1, h2, h3⟩; refine ⟨by omega, h1, h2⟩
  · rintro ⟨h1, h2, h3⟩; refine ⟨h2, h3, by omega⟩

theorem card_boxes_filter (m t f : ℕ) (hmL : m ≤ L) (hf : f ≤ 2 * m - t) :
    ((boxes L m t).filter fun π => (Cube.starLevels π).card + (Cube.P0Levels π).card = f).card
      = (f + 1) * beta' L m (2 * m - f) := by
  have hpairs : (balLeaves L m f ×ˢ range (f + 1)).card = (f + 1) * beta' L m (2 * m - f) := by
    rw [card_product, card_balLeaves hmL (by omega), card_range, mul_comm]
  have hpair : ∀ p ∈ balLeaves L m f ×ˢ range (f + 1),
      (P0Levels p.1).card = f ∧ (P0Levels p.1 ∩ half1 L).card ≤ m ∧
        (P0Levels p.1 \ half1 L).card ≤ m ∧ p.2 < f + 1 := fun p hp => by
    have h1 := (mem_filter.1 (mem_product.1 hp).1).2
    exact ⟨h1.1, h1.2.1, h1.2.2, mem_range.1 (mem_product.1 hp).2⟩
  rw [← hpairs]
  refine card_bij' (fun π _ => (Cube.starsToP0 π, (Cube.starLevels π).card))
    (fun p _ => starLowest p.2 p.1) (fun π hπ => ?_) (fun p hp => ?_) (fun π hπ => ?_)
    fun p hp => ?_
  · obtain ⟨hbox, hf⟩ := mem_filter.1 hπ
    obtain ⟨h1, -, h3, h4⟩ := mem_boxes.1 hbox
    simp only [balLeaves, mem_product, mem_filter, mem_univ, true_and, mem_range]
    refine ⟨⟨by rw [card_P0Levels_starsToP0]; exact hf, by rw [P0Levels_starsToP0]; exact h3,
      by rw [P0Levels_starsToP0]; exact h4⟩, by omega⟩
  · obtain ⟨hτ, hτ1, hτ2, he⟩ := hpair p hp
    have hu : Cube.starLevels (starLowest p.2 p.1) ∪ Cube.P0Levels (starLowest p.2 p.1)
        = P0Levels p.1 := by
      rw [← P0Levels_starsToP0, starsToP0_starLowest]
    rw [mem_filter, mem_boxes, ← card_P0Levels_starsToP0, starsToP0_starLowest]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hτ⟩
    · rw [← card_P0Levels_starsToP0, starsToP0_starLowest]; omega
    · rw [starLevels_starLowest, P0Levels_starLowest]
      exact fun ℓ hℓ ℓ' hℓ' => lowest_lt hℓ hℓ'
    · rw [hu]; exact hτ1
    · rw [hu]; exact hτ2
  · exact (eq_starLowest_starsToP0 π (mem_boxes.1 (mem_filter.1 hπ).1).2.1).symm
  · obtain ⟨hτ, -, -, he⟩ := hpair p hp
    rw [starsToP0_starLowest, starLevels_starLowest, card_lowest, hτ, min_eq_left (by omega)]

end Sq

open Sq in
theorem lemma_7_1_b_count : Lemma_7_1_b_count := by
  intro L m t hmL ht
  have hsort : (boxes L m t).card = ∑ f ∈ range (2 * m - t + 1),
      ((boxes L m t).filter
        fun π => (Cube.starLevels π).card + (Cube.P0Levels π).card = f).card := by
    refine card_eq_sum_card_fiberwise fun π hπ => ?_
    have hi := (mem_boxes.1 (mem_coe.1 hπ)).1
    simp only [coe_range, Set.mem_Iio]
    omega
  have hreflect : ∑ f ∈ range (2 * m - t + 1), beta' L m (2 * m - f)
      = ∑ d ∈ Icc t (2 * m), beta' L m d := by
    rw [range_eq_Ico, sum_Ico_reflect _ _ (by omega)]
    congr 1
    ext d
    simp only [mem_Ico, mem_Icc]
    omega
  rw [hsort, ← hreflect, mul_sum]
  refine sum_le_sum fun f hf => ?_
  have hfm : f < 2 * m - t + 1 := mem_range.1 hf
  rw [card_boxes_filter m t f hmL (by omega)]
  exact Nat.mul_le_mul_right _ (by omega)

namespace Sq

open Finset

variable {N : ℕ}

theorem Cube.mem_leaves_replace {π : Cube N} {ℓ : Fin N} (hℓ : π ℓ = .star)
    (lam : Tm) (τ : FLeaf N) :
    τ ∈ Cube.leaves (Cube.replace π ℓ lam) ↔ τ ∈ Cube.leaves π ∧ τ ℓ = lam := by
  rw [Cube.mem_leaves, Cube.mem_leaves, Cube.replace,
    Function.forall_update_iff π fun k s => s = CSym.star ∨ s = CSym.term (τ k)]
  constructor
  · rintro ⟨hlam, h⟩
    refine ⟨fun k => ?_, ?_⟩
    · by_cases hk : k = ℓ
      · exact Or.inl (hk ▸ hℓ)
      · exact h k hk
    · rcases hlam with h1 | h1
      · cases h1
      · exact (CSym.term.inj h1).symm
  · rintro ⟨h, rfl⟩
    exact ⟨Or.inr rfl, fun k _ => h k⟩

theorem Cube.starLevels_replace (π : Cube N) (ℓ : Fin N) (lam : Tm) :
    Cube.starLevels (Cube.replace π ℓ lam) = (Cube.starLevels π).erase ℓ := by
  ext k
  by_cases hk : k = ℓ <;> simp [Cube.replace, hk]

theorem Cube.P0Levels_replace_subset (π : Cube N) (ℓ : Fin N) (lam : Tm) :
    Cube.P0Levels (Cube.replace π ℓ lam) ⊆ insert ℓ (Cube.P0Levels π) := by
  intro k hk
  by_cases hkl : k = ℓ
  · exact mem_insert.2 (Or.inl hkl)
  · simpa [Cube.replace, hkl] using hk

theorem recurrence (g : FLeaf N → ℤ) (π : Cube N) (ℓ : Fin N) (hℓ : π ℓ = .star) :
    Cube.val g π = ∑ lam : Tm, Cube.val g (Cube.replace π ℓ lam) := by
  unfold Cube.val
  rw [← sum_fiberwise (Cube.leaves π) (fun τ => τ ℓ)]
  refine sum_congr rfl fun lam _ => sum_congr ?_ fun _ _ => rfl
  ext τ
  rw [mem_filter, Cube.mem_leaves_replace hℓ]

end Sq

open Sq in
theorem lemma_7_1_b_dp : Lemma_7_1_b_dp := by
  intro L m t π hne hπ
  set ℓ := (Cube.starLevels π).max' hne
  have hℓ : ℓ ∈ Cube.starLevels π := max'_mem _ hne
  refine ⟨fun lam => ?_, fun g => recurrence g π ℓ (Cube.mem_starLevels.1 hℓ)⟩
  obtain ⟨hcount, hbelow, h3, h4⟩ := hπ
  have hstar : (Cube.starLevels (Cube.replace π ℓ lam)).card + 1 = (Cube.starLevels π).card := by
    rw [Cube.starLevels_replace, card_erase_of_mem hℓ]
    have := card_pos.2 hne
    omega
  have hP0 := Cube.P0Levels_replace_subset π ℓ lam
  have hunion : Cube.starLevels (Cube.replace π ℓ lam) ∪ Cube.P0Levels (Cube.replace π ℓ lam)
      ⊆ Cube.starLevels π ∪ Cube.P0Levels π := by
    rw [Cube.starLevels_replace]
    intro k hk
    rcases mem_union.1 hk with hk | hk
    · exact mem_union_left _ (mem_of_mem_erase hk)
    · rcases mem_insert.1 (hP0 hk) with rfl | hk
      · exact mem_union_left _ hℓ
      · exact mem_union_right _ hk
  refine ⟨⟨?_, fun k hk k' hk' => ?_, ?_, ?_⟩, hstar⟩
  · have hmore := (card_le_card hP0).trans (card_insert_le _ _)
    omega
  · rw [Cube.starLevels_replace, mem_erase] at hk
    rcases mem_insert.1 (hP0 hk') with hnew | hold
    · exact hnew ▸ lt_of_le_of_ne (le_max' _ k hk.2) hk.1
    · exact hbelow k hk.2 k' hold
  · exact (card_le_card (inter_subset_inter_right hunion)).trans h3
  · exact (card_le_card (sdiff_subset_sdiff hunion le_rfl)).trans h4

end ThinMatrixProducts

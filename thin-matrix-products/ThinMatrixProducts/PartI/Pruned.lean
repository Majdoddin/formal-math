/-
Parts of this file are adapted from `3sum-apsp/ThreeSumApsp/Sec2/Lemma10.lean`:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import ThinMatrixProducts.PartI.Query

/-!
# [ZT, Lemma 10]: the pruned recursion, for any identity and on the `2L` levels

The proof of `3sum-apsp` (`ThreeSumApsp/Sec2/Lemma10.lean`) is ported with Schönhage's identity
replaced by any contribution relation `R` between terms and output letters, and with any numbers
`g τ` at the leaves in place of `Φ_τ(a) Ψ_τ(b)`.

* Values (`Pr.Pruned_eq_sum`): one induction on the number of levels; at a string of `S`, `Pruned`
  returns the sum of `g` over the leaves contributing to the string.
* Leaves visited (`Pr.called_iff_root_or`): a vertex below the root is called exactly if it
  contributes to a string of `U`; the step of the induction is `Pr.called_succ`.
* Total size (`Pr.sum_card_passed_le`): a set of strings is no larger than its set of leaves, by the
  private leaf `w ↦ p ∘ w` (`Pr.card_le_card_Leaves`), and the leaves of `Leaves(S)` that begin with
  `λ` are those of `Leaves(S_λ)` with `λ` put in front (`Pr.card_Leaves_succ`); so the sets passed
  at one depth have total size at most `|Leaves(U)|`, and there are `L + 1` depths.

Then `lemma_10_squared` applies this to the identity of Lemma 3.1 on the flattened `2L` levels
(`Π(τ)` at the leaf, the values are `∑_s Mult(a_s, b_s)` by Lemma 7 on the `2L` levels and the
leaf-sum link of Lemma 7.1(a)), and `fp_Lemma_10` to one run of the tiled product of Theorem A.14.
-/

set_option linter.unusedSectionVars false

namespace ThinMatrixProducts

namespace Pr

open Finset

section Generic

variable {T Z : Type} [Fintype T] [Fintype Z] [DecidableEq Z] {R : T → Z → Prop} [DecidableRel R]

/-! ### Step (2): the sets `S_λ` -/

@[simp]
theorem mem_sliceSet {n : ℕ} (S : Finset (Fin (n + 1) → Z)) (z : Z) (w' : Fin n → Z) :
    w' ∈ sliceSet S z ↔ (Fin.cons z w' : Fin (n + 1) → Z) ∈ S := by
  simp [sliceSet]

/-- In the proof of Lemma 10: "S_λ consists of the last L-k-1 variables of each string in S such
that λ contributes to the first variable of that string." -/
theorem mem_childSet {n : ℕ} {S : Finset (Fin (n + 1) → Z)} {lam : T} {w' : Fin n → Z} :
    w' ∈ childSet R S lam ↔ ∃ w ∈ S, R lam (w 0) ∧ Fin.tail w = w' := by
  simp only [childSet, mem_biUnion, mem_filter, mem_univ, true_and, mem_sliceSet]
  constructor
  · rintro ⟨z, hz, hw⟩
    exact ⟨_, hw, by simpa using hz, by simp⟩
  · rintro ⟨w, hw, hz, rfl⟩
    exact ⟨w 0, hz, by rwa [Fin.cons_self_tail]⟩

/-- The leaf `λ τ'` contributes to `w` iff `λ` contributes to `w₀` and `τ'` to the rest of `w`. -/
theorem contrib_cons {n : ℕ} {lam : T} {τ' : Fin n → T} {w : Fin (n + 1) → Z} :
    Contrib R (Fin.cons lam τ' : Fin (n + 1) → T) w ↔ R lam (w 0) ∧ Contrib R τ' (Fin.tail w) := by
  simp only [Contrib, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

/-- A sum over the leaves contributing to `w`, split at the first level. -/
theorem sum_contrib_succ {n : ℕ} (f : (Fin (n + 1) → T) → ℤ) (w : Fin (n + 1) → Z) :
    ∑ τ ∈ univ.filter (fun τ => Contrib R τ w), f τ
      = ∑ lam ∈ univ.filter (fun lam => R lam (w 0)),
          ∑ τ' ∈ univ.filter (fun τ' : Fin n → T => Contrib R τ' (Fin.tail w)),
            f (Fin.cons lam τ') := by
  rw [sum_filter, ← (Fin.consEquiv fun _ : Fin (n + 1) => T).sum_comp, Fintype.sum_prod_type,
    sum_filter]
  refine sum_congr rfl fun lam _ => ?_
  change (∑ y, if Contrib R (Fin.cons lam y : Fin (n + 1) → T) w then f (Fin.cons lam y) else 0) = _
  simp only [contrib_cons]
  by_cases h : R lam (w 0)
  · simp [h, sum_filter]
  · simp [h]

/-! ### Lemma 10, first claim: the values -/

/-- The array `C_λ` of step (3); the zero array if `S_λ = ∅`. -/
def childResult (R : T → Z → Prop) [DecidableRel R] {n : ℕ} (g : (Fin (n + 1) → T) → ℤ)
    (S : Finset (Fin (n + 1) → Z)) (lam : T) : (Fin n → Z) → ℤ :=
  if (childSet R S lam).Nonempty then
    Pruned R n (fun τ' => g (Fin.cons lam τ')) (childSet R S lam)
  else 0

/-- Step (4) of `Pruned` at one string. -/
theorem Pruned_succ_apply {n : ℕ} (g : (Fin (n + 1) → T) → ℤ) (S : Finset (Fin (n + 1) → Z))
    (w : Fin (n + 1) → Z) :
    Pruned R (n + 1) g S w = if w ∈ S then
      ∑ lam ∈ univ.filter (fun lam => R lam (w 0)), childResult R g S lam (Fin.tail w)
    else 0 := by
  simp only [Pruned, run, childResult, restrictTo, apply_ite Prod.fst]

/-- What `Pruned` returns, for any numbers `g` at the leaves: at each string of `S`, the sum of `g`
over the leaves contributing to it. -/
theorem Pruned_eq_sum {n : ℕ} (g : (Fin n → T) → ℤ) (S : Finset (Fin n → Z)) :
    Pruned R n g S = restrictTo S fun w => ∑ τ ∈ univ.filter (fun τ => Contrib R τ w), g τ := by
  induction n with
  | zero =>
    funext w
    have hleaf : univ.filter (fun τ : Fin 0 → T => Contrib R τ w) = {Fin.elim0} :=
      eq_singleton_iff_unique_mem.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, fun ℓ => ℓ.elim0⟩, fun _ _ => Subsingleton.elim _ _⟩
    simp only [Pruned, run, restrictTo, hleaf, sum_singleton]
  | succ n ih =>
    have hC (lam : T) : childResult R g S lam
        = restrictTo (childSet R S lam) fun w' =>
          ∑ τ' ∈ univ.filter (fun τ' => Contrib R τ' w'), g (Fin.cons lam τ') := by
      unfold childResult
      split_ifs with hne
      · exact ih _ _
      · rw [not_nonempty_iff_eq_empty.mp hne]
        funext w'
        simp [restrictTo]
    funext w
    rw [Pruned_succ_apply, restrictTo, sum_contrib_succ]
    split_ifs with hw
    · refine sum_congr rfl fun lam hlam => ?_
      have hmem : Fin.tail w ∈ childSet R S lam :=
        mem_childSet.mpr ⟨w, hw, (mem_filter.mp hlam).2, rfl⟩
      rw [hC, restrictTo, if_pos hmem]
    · rfl

/-! ### Lemma 10, second claim: the calls that are made -/

/-- The calls made by the child `λ`: none if `S_λ = ∅`. -/
def childCalls (R : T → Z → Prop) [DecidableRel R] {n : ℕ} (g : (Fin (n + 1) → T) → ℤ)
    (S : Finset (Fin (n + 1) → Z)) (lam : T) : Multiset (Call T Z) :=
  if (childSet R S lam).Nonempty then
    calls R n (fun τ' => g (Fin.cons lam τ')) (childSet R S lam)
  else 0

theorem calls_succ {n : ℕ} (g : (Fin (n + 1) → T) → ℤ) (S : Finset (Fin (n + 1) → Z)) :
    calls R (n + 1) g S = ⟨⟨0, Fin.elim0⟩, ⟨n + 1, S⟩⟩ ::ₘ
      univ.val.bind fun lam => (childCalls R g S lam).map (Call.under lam) := by
  simp only [calls, run, childCalls, apply_ite Prod.snd]

theorem mem_calls_succ {n : ℕ} {g : (Fin (n + 1) → T) → ℤ} {S : Finset (Fin (n + 1) → Z)}
    {c : Call T Z} :
    c ∈ calls R (n + 1) g S ↔
      c = ⟨⟨0, Fin.elim0⟩, ⟨n + 1, S⟩⟩
        ∨ ∃ lam : T, (childSet R S lam).Nonempty
            ∧ ∃ c' ∈ calls R n (fun τ' => g (Fin.cons lam τ')) (childSet R S lam),
                c = c'.under lam := by
  rw [calls_succ, Multiset.mem_cons, Multiset.mem_bind]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨lam, -, h⟩
    obtain ⟨c', hc', rfl⟩ := Multiset.mem_map.mp h
    unfold childCalls at hc'
    split_ifs at hc' with hne
    · exact ⟨lam, hne, c', hc', rfl⟩
    · simp at hc'
  · rintro ⟨lam, hne, c', hc', rfl⟩
    refine ⟨lam, mem_univ lam, Multiset.mem_map.mpr ⟨c', ?_, rfl⟩⟩
    rwa [childCalls, if_pos hne]

private theorem Call.vertex_under_eq_iff {lam : T} {c : Call T Z} {k : ℕ}
    {τ : Fin (k + 1) → T} :
    (c.under lam).vertex = ⟨k + 1, τ⟩ ↔ lam = τ 0 ∧ c.vertex = ⟨k, Fin.tail τ⟩ := by
  obtain ⟨⟨k', τ'⟩, U⟩ := c
  constructor
  · intro h
    simp only [Call.under, Sigma.mk.injEq, Nat.add_right_cancel_iff] at h
    obtain ⟨rfl, h⟩ := h
    obtain rfl := eq_of_heq h
    simp
  · rintro ⟨rfl, h⟩
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain rfl := eq_of_heq h
    simp [Call.under]

/-- `Pruned(U)`, called at the root, calls the vertex `τ`. -/
def Called (R : T → Z → Prop) [DecidableRel R] {L k : ℕ} (g : (Fin L → T) → ℤ)
    (U : Finset (Fin L → Z)) (τ : Fin k → T) : Prop :=
  ∃ c ∈ calls R L g U, c.vertex = ⟨k, τ⟩

theorem called_root {L : ℕ} (g : (Fin L → T) → ℤ) (U : Finset (Fin L → Z)) (τ : Fin 0 → T) :
    Called R g U τ := by
  obtain rfl : τ = Fin.elim0 := Subsingleton.elim _ _
  cases L with
  | zero => exact ⟨_, Multiset.mem_singleton_self _, rfl⟩
  | succ n => exact ⟨_, mem_calls_succ.mpr (.inl rfl), rfl⟩

/-- Step (3): the vertex `λ τ'` is called exactly if `S_λ ≠ ∅` and the child `λ` calls `τ'`. -/
theorem called_succ {n k : ℕ} (g : (Fin (n + 1) → T) → ℤ) (S : Finset (Fin (n + 1) → Z))
    (τ : Fin (k + 1) → T) :
    Called R g S τ ↔ (childSet R S (τ 0)).Nonempty ∧
      Called R (fun τ' => g (Fin.cons (τ 0) τ')) (childSet R S (τ 0)) (Fin.tail τ) := by
  constructor
  · rintro ⟨c, hc, hcτ⟩
    rcases mem_calls_succ.mp hc with rfl | ⟨lam, hne, c', hc', rfl⟩
    · exact absurd (congrArg Sigma.fst hcτ) (by simp)
    · obtain ⟨rfl, hc'τ⟩ := Call.vertex_under_eq_iff.mp hcτ
      exact ⟨hne, c', hc', hc'τ⟩
  · rintro ⟨hne, c', hc', hc'τ⟩
    exact ⟨c'.under (τ 0), mem_calls_succ.mpr (.inr ⟨τ 0, hne, c', hc', rfl⟩),
      Call.vertex_under_eq_iff.mpr ⟨rfl, hc'τ⟩⟩

/-- [ZT, Section 2.3.2]: "a vertex τ₁ ⋯ τ_k contributes to an output string w if τ_ℓ contributes
to w_ℓ at every level ℓ ≤ k." -/
def VContrib (R : T → Z → Prop) {k L : ℕ} (τ : Fin k → T) (w : Fin L → Z) : Prop :=
  ∀ (ℓ : Fin k) (h : (ℓ : ℕ) < L), R (τ ℓ) (w ⟨ℓ, h⟩)

theorem vcontrib_cons {k L : ℕ} {lam : T} {τ : Fin k → T} {w : Fin (L + 1) → Z} :
    VContrib R (Fin.cons lam τ : Fin (k + 1) → T) w
      ↔ R lam (w 0) ∧ VContrib R τ (Fin.tail w) := by
  constructor
  · intro h
    exact ⟨h 0 (Nat.succ_pos L), fun ℓ hℓ => h ℓ.succ (Nat.succ_lt_succ hℓ)⟩
  · rintro ⟨h0, h1⟩ ℓ h
    induction ℓ using Fin.cases with
    | zero => exact h0
    | succ i => exact h1 i (Nat.lt_of_succ_lt_succ h)

private theorem exists_vcontrib_childSet {n k : ℕ} (S : Finset (Fin (n + 1) → Z))
    (τ : Fin (k + 1) → T) :
    (∃ w' ∈ childSet R S (τ 0), VContrib R (Fin.tail τ) w') ↔ ∃ w ∈ S, VContrib R τ w := by
  have hcons (w : Fin (n + 1) → Z) : VContrib R τ w
      ↔ R (τ 0) (w 0) ∧ VContrib R (Fin.tail τ) (Fin.tail w) := by
    rw [← vcontrib_cons, Fin.cons_self_tail]
  constructor
  · rintro ⟨w', hw', hτ'⟩
    obtain ⟨w, hw, hz, rfl⟩ := mem_childSet.mp hw'
    exact ⟨w, hw, (hcons w).mpr ⟨hz, hτ'⟩⟩
  · rintro ⟨w, hw, hτ⟩
    exact ⟨_, mem_childSet.mpr ⟨w, hw, ((hcons w).mp hτ).1, rfl⟩, ((hcons w).mp hτ).2⟩

/-- A vertex at depth `k ≤ L` is called by `Pruned(U)` iff it is the root or it contributes to some
string of `U` (proof of Lemma 10). -/
theorem called_iff_root_or {L k : ℕ} (g : (Fin L → T) → ℤ) (U : Finset (Fin L → Z))
    (hkL : k ≤ L) (τ : Fin k → T) :
    Called R g U τ ↔ k = 0 ∨ ∃ w ∈ U, VContrib R τ w := by
  induction L generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact iff_of_true (called_root g U τ) (.inl rfl)
  | succ n ih =>
    cases k with
    | zero => exact iff_of_true (called_root g U τ) (.inl rfl)
    | succ k =>
      have ihτ := ih (fun τ' => g (Fin.cons (τ 0) τ')) (childSet R U (τ 0))
        (Nat.le_of_succ_le_succ hkL) (Fin.tail τ)
      rw [called_succ, ← exists_vcontrib_childSet]
      constructor
      · rintro ⟨⟨w', hw'⟩, hcalled⟩
        rcases ihτ.mp hcalled with rfl | hτ'
        · exact .inr ⟨w', hw', fun ℓ => ℓ.elim0⟩
        · exact .inr hτ'
      · rintro (hk | ⟨w', hw', hτ'⟩)
        · exact absurd hk (Nat.succ_ne_zero k)
        · exact ⟨⟨w', hw'⟩, ihτ.mpr (.inr ⟨w', hw', hτ'⟩)⟩

/-- Lemma 10, second claim: the leaves visited are exactly those of `Leaves(U)`. -/
theorem leaves_visited {L : ℕ} (g : (Fin L → T) → ℤ) (U : Finset (Fin L → Z))
    (h : 0 < L ∨ U.Nonempty) (τ : Fin L → T) : Visits R L g U τ ↔ τ ∈ Leaves R U := by
  change Called R g U τ ↔ _
  rw [called_iff_root_or g U le_rfl τ]
  simp only [Leaves, mem_filter, mem_univ, true_and]
  have hv (w : Fin L → Z) : VContrib R τ w ↔ Contrib R τ w :=
    ⟨fun h ℓ => h ℓ ℓ.2, fun h ℓ _ => h ℓ⟩
  simp only [hv]
  constructor
  · rintro (rfl | h')
    · obtain ⟨w, hw⟩ := h.resolve_left (lt_irrefl 0)
      exact ⟨w, hw, fun ℓ => ℓ.elim0⟩
    · exact h'
  · exact Or.inr

/-- A call at depth `k` is passed strings of length `L - k`. -/
theorem depth_add_length {L : ℕ} {g : (Fin L → T) → ℤ} {U : Finset (Fin L → Z)} {c : Call T Z}
    (hc : c ∈ calls R L g U) : c.vertex.1 + c.passed.1 = L := by
  induction L generalizing c with
  | zero =>
    obtain rfl := Multiset.mem_singleton.mp hc
    rfl
  | succ n ih =>
    rcases mem_calls_succ.mp hc with rfl | ⟨lam, -, c', hc', rfl⟩
    · exact Nat.zero_add _
    · have hlen := ih hc'
      change c'.vertex.1 + 1 + c'.passed.1 = n + 1
      omega

/-! ### Lemma 10, third claim: the total size of the sets passed -/

theorem mem_Leaves_succ {n : ℕ} {S : Finset (Fin (n + 1) → Z)} {τ : Fin (n + 1) → T} :
    τ ∈ Leaves R S ↔ Fin.tail τ ∈ Leaves R (childSet R S (τ 0)) := by
  have hc (w : Fin (n + 1) → Z) : Contrib R τ w ↔ R (τ 0) (w 0) ∧ Contrib R (Fin.tail τ) (Fin.tail w) := by
    rw [← contrib_cons, Fin.cons_self_tail]
  simp only [Leaves, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨w, hw, hcon⟩
    exact ⟨Fin.tail w, mem_childSet.mpr ⟨w, hw, ((hc w).mp hcon).1, rfl⟩, ((hc w).mp hcon).2⟩
  · rintro ⟨w', hw', h1⟩
    obtain ⟨w, hw, h0, rfl⟩ := mem_childSet.mp hw'
    exact ⟨w, hw, (hc w).mpr ⟨h0, h1⟩⟩

/-- `Leaves(S)` is the disjoint union over `λ` of the leaves `λ τ'` with `τ' ∈ Leaves(S_λ)`. -/
theorem card_Leaves_succ {n : ℕ} (S : Finset (Fin (n + 1) → Z)) :
    (Leaves R S).card = ∑ lam, (Leaves R (childSet R S lam)).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun τ : Fin (n + 1) → T => τ 0) (t := univ)
    (fun _ _ => mem_coe.mpr (mem_univ _))]
  refine sum_congr rfl fun lam _ => ?_
  rw [← card_image_of_injective (Leaves R (childSet R S lam))
    (Fin.cons_right_injective (α := fun _ : Fin (n + 1) => T) lam)]
  congr 1
  ext τ
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hτ, rfl⟩
    exact ⟨Fin.tail τ, mem_Leaves_succ.mp hτ, Fin.cons_self_tail τ⟩
  · rintro ⟨τ', hτ', rfl⟩
    refine ⟨mem_Leaves_succ.mpr ?_, Fin.cons_zero _ _⟩
    simpa using hτ'

/-- With an injective choice `p` of a contributing term for each output letter, a set of output
strings is no larger than its set of leaves (the private leaf `p ∘ w` determines `w`). -/
theorem card_le_card_Leaves {p : Z → T} (hp : Function.Injective p) (hpR : ∀ z, R (p z) z)
    {n : ℕ} (S : Finset (Fin n → Z)) : S.card ≤ (Leaves R S).card := by
  refine card_le_card_of_injOn (fun w => p ∘ w) (fun w hw => ?_) ?_
  · simp only [coe_filter, Leaves, mem_univ, true_and, Set.mem_ofPred_eq]
    exact ⟨w, hw, fun ℓ => hpR (w ℓ)⟩
  · intro w _ w' _ h
    exact funext fun ℓ => hp (congrFun h ℓ)

private def sizeAt (s : Multiset (Call T Z)) (k : ℕ) : ℕ :=
  ((s.filter fun c => c.vertex.1 = k).map fun c => c.passed.2.card).sum

private theorem sizeAt_cons (c : Call T Z) (s : Multiset (Call T Z)) (k : ℕ) :
    sizeAt (c ::ₘ s) k = (if c.vertex.1 = k then c.passed.2.card else 0) + sizeAt s k := by
  unfold sizeAt
  rw [Multiset.filter_cons]
  split_ifs <;> simp

private theorem sizeAt_bind (f : T → Multiset (Call T Z)) (k : ℕ) :
    sizeAt (univ.val.bind f) k = ∑ lam, sizeAt (f lam) k := by
  unfold sizeAt
  rw [Multiset.filter_bind, Multiset.map_bind, Multiset.sum_bind]
  rfl

private theorem sizeAt_under_succ (lam : T) (s : Multiset (Call T Z)) (k : ℕ) :
    sizeAt (s.map (Call.under lam)) (k + 1) = sizeAt s k := by
  unfold sizeAt
  rw [Multiset.filter_map, Multiset.map_map]
  rw [Multiset.filter_congr (q := fun c => c.vertex.1 = k) (by simp [Call.under])]
  rfl

private theorem sizeAt_under_zero (lam : T) (s : Multiset (Call T Z)) :
    sizeAt (s.map (Call.under lam)) 0 = 0 := by
  unfold sizeAt
  rw [Multiset.filter_map, Multiset.filter_eq_nil.mpr (by simp [Call.under])]
  rfl

private theorem sum_sizeAt (s : Multiset (Call T Z)) (N : ℕ) (h : ∀ c ∈ s, c.vertex.1 < N) :
    (s.map fun c => c.passed.2.card).sum = ∑ k ∈ range N, sizeAt s k := by
  induction s using Multiset.induction_on with
  | empty => simp [sizeAt]
  | cons c s ih =>
    simp only [sizeAt_cons, Multiset.map_cons, Multiset.sum_cons, sum_add_distrib]
    rw [ih fun c' hc' => h c' (Multiset.mem_cons_of_mem hc'), sum_ite_eq,
      if_pos (mem_range.mpr (h c (Multiset.mem_cons_self c s)))]

/-- End of the proof of Lemma 10: the sets passed at one depth have total size at most
`|Leaves(U)|`. -/
theorem sum_card_passed_le {p : Z → T} (hp : Function.Injective p) (hpR : ∀ z, R (p z) z)
    {L : ℕ} (g : (Fin L → T) → ℤ) (U : Finset (Fin L → Z)) (k : ℕ) :
    sizeAt (calls R L g U) k ≤ (Leaves R U).card := by
  induction L generalizing k with
  | zero =>
    have hcalls : calls R 0 g U = ⟨⟨0, Fin.elim0⟩, ⟨0, U⟩⟩ ::ₘ 0 := rfl
    rw [hcalls, sizeAt_cons]
    split_ifs
    · simpa [sizeAt] using card_le_card_Leaves hp hpR U
    · simp [sizeAt]
  | succ n ih =>
    rw [calls_succ, sizeAt_cons, sizeAt_bind]
    cases k with
    | zero =>
      simp only [sizeAt_under_zero, sum_const_zero, if_true, add_zero]
      exact card_le_card_Leaves hp hpR U
    | succ k =>
      simp only [sizeAt_under_succ]
      rw [if_neg (by simp), zero_add, card_Leaves_succ]
      refine sum_le_sum fun lam _ => ?_
      unfold childCalls
      split_ifs
      · exact ih _ _ _
      · simp [sizeAt]

/-- Lemma 10, third claim. -/
theorem total_size {p : Z → T} (hp : Function.Injective p) (hpR : ∀ z, R (p z) z) {L : ℕ}
    (g : (Fin L → T) → ℤ) (U : Finset (Fin L → Z)) :
    totalSize R L g U ≤ (L + 1) * (Leaves R U).card := by
  have hdepth : ∀ c ∈ calls R L g U, c.vertex.1 < L + 1 :=
    fun c hc => by have := depth_add_length hc; omega
  rw [totalSize, sum_sizeAt _ (L + 1) hdepth]
  calc ∑ k ∈ range (L + 1), sizeAt (calls R L g U) k
      ≤ ∑ _k ∈ range (L + 1), (Leaves R U).card :=
        sum_le_sum fun k _ => sum_card_passed_le hp hpR g U k
    _ = (L + 1) * (Leaves R U).card := by simp

end Generic

end Pr

open Finset

theorem lemma_10_generic : Lemma_10_generic := by
  intro T Z _ _ _ R _ L g U
  exact ⟨Pr.Pruned_eq_sum g U, fun h τ => Pr.leaves_visited g U h τ,
    fun _ hp hpR => Pr.total_size hp hpR g U⟩

/-! ### On the `2L` levels -/

/-- A leaf on the two halves is in `Leaves(U)` iff its flattening is in `Leaves` of the flattened
strings. -/
private lemma flat_mem_Leaves {L : ℕ} (U : Finset (OutStr L)) (τ : Leaf L) :
    Sq.flatLeaf τ ∈ Pr.Leaves Pr.chiRel (U.image Sq.flatOut) ↔ τ ∈ Leaves U := by
  simp only [Pr.Leaves, Leaves, mem_filter, mem_univ, true_and, mem_image]
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, h⟩
    exact ⟨w, hw, (Sq.contrib_flat τ w).mpr h⟩
  · rintro ⟨w, hw, h⟩
    exact ⟨_, ⟨w, hw, rfl⟩, (Sq.contrib_flat τ w).mp h⟩

private lemma flatOut_injective {L : ℕ} : Function.Injective (Sq.flatOut (L := L)) :=
  (Fin.appendEquiv L L).injective

private lemma privTerm_injective : Function.Injective Sq.privTerm := by decide

private lemma chiRel_privTerm (z : ZL) : Pr.chiRel (Sq.privTerm z) z := by
  cases z <;> simp [Pr.chiRel, Sq.privTerm, chi]

theorem lemma_10_squared : Lemma_10_squared := by
  intro L m a b U
  dsimp only
  refine ⟨fun w => ?_, fun h τ => ?_, ?_⟩
  · rw [Pr.Pruned_eq_sum, Pr.restrictTo]
    by_cases hw : w ∈ U
    · rw [if_pos (mem_image.mpr ⟨w, hw, rfl⟩), if_pos hw]
      rw [((lemma_7_1_a_link (m := m) a b w).1)]
      rw [sum_filter, sum_filter]
      symm
      refine Fintype.sum_equiv (Sq.flatEquiv L) _ _ fun τ => ?_
      rw [Sq.flatEquiv_apply, unflat_flat]
      have hc : Contributes τ w ↔ Pr.Contrib Pr.chiRel (Sq.flatLeaf τ) (Sq.flatOut w) :=
        Sq.contrib_flat τ w
      by_cases hτ : Contributes τ w
      · rw [if_pos hτ, if_pos (hc.mp hτ)]
        refine sum_congr rfl fun s _ => ?_
        rw [((lemma_7_squared (a s) (b s)).2.2 τ).1, ((lemma_7_squared (a s) (b s)).2.2 τ).2]
      · rw [if_neg hτ, if_neg (fun h' => hτ (hc.mpr h'))]
    · rw [if_neg hw, if_neg]
      rintro h'
      obtain ⟨w', hw', he⟩ := mem_image.mp h'
      exact hw (flatOut_injective he ▸ hw')
  · have h' : 0 < L + L ∨ (U.image Sq.flatOut).Nonempty := by
      rcases h with h | h
      · exact .inl (by omega)
      · exact .inr (h.image _)
    rw [Pr.leaves_visited _ _ h', flat_mem_Leaves]
  · have hcard : (Pr.Leaves Pr.chiRel (U.image Sq.flatOut)).card = (Leaves U).card :=
      (card_equiv (Sq.flatEquiv L) fun τ => by
        rw [Sq.flatEquiv_apply, flat_mem_Leaves]).symm
    calc Pr.totalSize Pr.chiRel (L + L) _ (U.image Sq.flatOut)
        ≤ (L + L + 1) * (Pr.Leaves Pr.chiRel (U.image Sq.flatOut)).card :=
          Pr.total_size privTerm_injective chiRel_privTerm _ _
      _ = (2 * L + 1) * (Leaves U).card := by rw [hcard, two_mul]

/-! ### One run of the tiled product of Theorem A.14 -/

theorem fp_Lemma_10 : FP_Lemma_10 := by
  intro P o₁ o₂ R L Zs W p g
  dsimp only
  refine ⟨fun ω => ?_, fun h τ => ?_⟩
  · rw [Pr.Pruned_eq_sum, Pr.restrictTo]
    simp only [mem_filter, mem_univ, true_and]
    split_ifs
    · rfl
    · rfl
  · rw [Pr.leaves_visited _ _ h]
    simp only [Pr.Leaves, mem_filter, mem_univ, true_and]
    unfold fpLeaves
    simp only [mem_filter, mem_univ, true_and]
    simp only [fpRunA, mem_filter, mem_univ, true_and, Pr.Contrib, Pr.suppRel]
    constructor
    · rintro ⟨ω, hω, hc⟩
      exact ⟨(p, ω), hω, rfl, hc⟩
    · rintro ⟨⟨p', ω⟩, hω, rfl, hc⟩
      exact ⟨ω, hω, hc⟩

end ThinMatrixProducts

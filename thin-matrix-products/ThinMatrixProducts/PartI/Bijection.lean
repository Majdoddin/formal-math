import ThinMatrixProducts.PartI.Squared
import Mathlib.Data.Fintype.Pi

/-!
# Theorem 5.1, the bijection; the example after it

An output string `w'` with inner set `Q'` is determined by `ι(w')` and by `S(w') ⊆ [L] ∖ Q'`, and
`S ↦ Δ[S]` is a bijection from the subsets of `[L] ∖ Q'` onto `F₂^{L-m}` when `Q'` is good; so the
map from output strings to positions is a bijection. The example is checked by evaluation.
-/

namespace ThinMatrixProducts

open Finset

/-- A `z`-string is determined by its inner set, its `ι` and its `S`. -/
lemma zstr_eq {L : ℕ} (ζ : ZStr L) (ℓ : Fin L) :
    ζ ℓ = if ℓ ∈ QZ ζ then .z0 else .z (iotaZ ζ ℓ) (if ℓ ∈ SZ ζ then 1 else 0) := by
  simp only [QZ, SZ, mem_filter, mem_univ, true_and, iotaZ_apply]
  rcases ζ ℓ with ⟨i, j⟩ | _
  · fin_cases j <;> simp [zIdx]
  · simp

lemma SZ_subset_compl {L : ℕ} (ζ : ZStr L) : SZ ζ ⊆ (QZ ζ)ᶜ := by
  intro ℓ h
  simp only [SZ, QZ, mem_filter, mem_univ, true_and, mem_compl] at h ⊢
  obtain ⟨i, hi⟩ := h
  rw [hi]; simp

lemma iotaZ_zero_of_mem {L : ℕ} (ζ : ZStr L) (ℓ : Fin L) (h : ℓ ∈ QZ ζ) : iotaZ ζ ℓ = 0 := by
  simp only [QZ, mem_filter, mem_univ, true_and] at h
  rw [iotaZ_apply, h]; rfl

/-- The `z`-string with inner set `Q`, indices `ι` and set `S`. -/
def mkZ {L : ℕ} (Q S : Finset (Fin L)) (ι : Fin L → Fin 2) : ZStr L := fun ℓ =>
  if ℓ ∈ Q then .z0 else .z (ι ℓ) (if ℓ ∈ S then 1 else 0)

lemma QZ_mkZ {L : ℕ} (Q S : Finset (Fin L)) (ι : Fin L → Fin 2) : QZ (mkZ Q S ι) = Q := by
  ext ℓ; simp only [QZ, mkZ, mem_filter, mem_univ, true_and]
  by_cases h : ℓ ∈ Q <;> simp [h]

lemma iotaZ_mkZ {L : ℕ} (Q S : Finset (Fin L)) (ι : Fin L → Fin 2) (hι : ∀ ℓ ∈ Q, ι ℓ = 0) :
    iotaZ (mkZ Q S ι) = ι := by
  funext ℓ; rw [iotaZ_apply]; simp only [mkZ]
  by_cases h : ℓ ∈ Q
  · simp [h, zIdx, hι ℓ h]
  · simp [h, zIdx]

lemma SZ_mkZ {L : ℕ} (Q S : Finset (Fin L)) (ι : Fin L → Fin 2) (hS : S ⊆ Qᶜ) :
    SZ (mkZ Q S ι) = S := by
  ext ℓ
  rw [SZ, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, mkZ]
  by_cases h : ℓ ∈ Q
  · have : ℓ ∉ S := fun hS' => (mem_compl.1 (hS hS')) h
    simp [h, this]
  · by_cases h' : ℓ ∈ S
    · rw [if_neg h, if_pos h']; exact ⟨fun _ => h', fun _ => ⟨ι ℓ, rfl⟩⟩
    · rw [if_neg h, if_neg h']; simp [h']

/-- The functions `Fin L → Fin 2` that vanish on `Q` number `2^{L-|Q|}`. -/
lemma card_masked {L : ℕ} (Q : Finset (Fin L)) :
    (univ.filter fun ι : Fin L → Fin 2 => ∀ ℓ ∈ Q, ι ℓ = 0).card = 2 ^ (L - Q.card) := by
  have : (univ.filter fun ι : Fin L → Fin 2 => ∀ ℓ ∈ Q, ι ℓ = 0)
      = Fintype.piFinset (fun ℓ => if ℓ ∈ Q then ({0} : Finset (Fin 2)) else univ) := by
    ext ι
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h ℓ; by_cases hℓ : ℓ ∈ Q <;> simp [hℓ, h]
    · intro h ℓ hℓ; have := h ℓ; simpa [hℓ] using this
  rw [this, Fintype.card_piFinset]
  have h2 : ∀ ℓ, (if ℓ ∈ Q then ({0} : Finset (Fin 2)) else univ).card = if ℓ ∈ Q then 1 else 2 := by
    intro ℓ; by_cases h : ℓ ∈ Q <;> simp [h]
  simp_rw [h2]
  rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  congr 1
  rw [filter_not, card_sdiff_of_subset (filter_subset _ _), card_univ, Fintype.card_fin]
  congr 1
  rw [filter_mem_eq_inter, univ_inter]

theorem theorem_5_1_bijection : Theorem_5_1_bijection := by
  intro L m Γ Δ Q' Q'' h1 h2
  have bΔ1 := (sec4_bijections Γ Δ Q' h1).2
  have bΔ2 := (sec4_bijections Γ Δ Q'' h2).2
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- maps to
    rintro w ⟨hw1, hw2⟩
    refine ⟨fun ℓ hℓ => ?_, fun ℓ hℓ => ?_⟩
    · exact iotaZ_zero_of_mem _ _ (hw1 ▸ hℓ)
    · exact iotaZ_zero_of_mem _ _ (hw2 ▸ hℓ)
  · -- injective
    rintro w ⟨hw1, hw2⟩ w' ⟨hw1', hw2'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨⟨hi1, hd2⟩, hd1, hi2⟩ := h
    have hs1 : SZ w.1 = SZ w'.1 := bΔ1.injOn
      (mem_coe.2 (mem_powerset.2 (hw1 ▸ SZ_subset_compl w.1)))
      (mem_coe.2 (mem_powerset.2 (hw1' ▸ SZ_subset_compl w'.1))) hd1
    have hs2 : SZ w.2 = SZ w'.2 := bΔ2.injOn
      (mem_coe.2 (mem_powerset.2 (hw2 ▸ SZ_subset_compl w.2)))
      (mem_coe.2 (mem_powerset.2 (hw2' ▸ SZ_subset_compl w'.2))) hd2
    refine Prod.ext (funext fun ℓ => ?_) (funext fun ℓ => ?_)
    · rw [zstr_eq w.1 ℓ, zstr_eq w'.1 ℓ, hw1, hw1', hi1, hs1]
    · rw [zstr_eq w.2 ℓ, zstr_eq w'.2 ℓ, hw2, hw2', hi2, hs2]
  · -- onto
    rintro ⟨⟨ι1, d2⟩, ⟨d1, ι2⟩⟩ ⟨hι1, hι2⟩
    obtain ⟨S1, hS1, rfl⟩ := bΔ1.surjOn (Set.mem_univ d1)
    obtain ⟨S2, hS2, rfl⟩ := bΔ2.surjOn (Set.mem_univ d2)
    have hS1' : S1 ⊆ Q'ᶜ := mem_powerset.1 (mem_coe.1 hS1)
    have hS2' : S2 ⊆ Q''ᶜ := mem_powerset.1 (mem_coe.1 hS2)
    refine ⟨(mkZ Q' S1 ι1, mkZ Q'' S2 ι2), ⟨QZ_mkZ _ _ _, QZ_mkZ _ _ _⟩, ?_⟩
    simp only [iotaZ_mkZ _ _ _ hι1, iotaZ_mkZ _ _ _ hι2, SZ_mkZ _ _ _ hS1', SZ_mkZ _ _ _ hS2']
  · -- the number of entries
    have e : (univ.filter fun p : RowIdx L m × ColIdx L m =>
          (∀ ℓ ∈ Q', p.1.1 ℓ = 0) ∧ (∀ ℓ ∈ Q'', p.2.2 ℓ = 0))
        = ((univ.filter fun ι : Fin L → Fin 2 => ∀ ℓ ∈ Q', ι ℓ = 0) ×ˢ univ) ×ˢ
          (univ ×ˢ (univ.filter fun ι : Fin L → Fin 2 => ∀ ℓ ∈ Q'', ι ℓ = 0)) := by
      ext p; simp
    rw [e, card_product, card_product, card_product, card_masked, card_masked, h1.1, h2.1,
      card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, N0]
    have h4 : (4 : ℕ) = 2 ^ 2 := rfl
    rw [h4, ← pow_mul, ← pow_mul]
    ring_nf

/-- `{0}`, `{1}`, `{2}` are good for the maps of the example. -/
lemma example_good :
    Good (!![1, 1, 1] : Matrix (Fin 1) (Fin 3) (ZMod 2))
        (!![0, 1, 1; 1, 0, 1] : Matrix (Fin (3 - 1)) (Fin 3) (ZMod 2)) {0} ∧
    Good (!![1, 1, 1] : Matrix (Fin 1) (Fin 3) (ZMod 2))
        (!![0, 1, 1; 1, 0, 1] : Matrix (Fin (3 - 1)) (Fin 3) (ZMod 2)) {1} ∧
    Good (!![1, 1, 1] : Matrix (Fin 1) (Fin 3) (ZMod 2))
        (!![0, 1, 1; 1, 0, 1] : Matrix (Fin (3 - 1)) (Fin 3) (ZMod 2)) {2} := by
  refine ⟨⟨rfl, ?_, ?_⟩, ⟨rfl, ?_, ?_⟩, ⟨rfl, ?_, ?_⟩⟩ <;>
    rw [Fintype.linearIndependent_iff] <;> decide

theorem sec5_example : Sec5_example := by
  refine ⟨example_good, ?_⟩
  decide

end ThinMatrixProducts

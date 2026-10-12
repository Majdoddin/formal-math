import Statements

/-!
# Remark 5.2: the weights of the strings in run `s`
-/

namespace ThinMatrixProducts

open Finset

lemma wX_add : ∀ c : XL, wX c + (if c = .p 1 then 1 else 0) =
    2 * (if ∃ k, c = .p k then 1 else 0) := by decide

lemma wY_eq : ∀ c : YL, wY c = if c = .q then 1 else 0 := by decide

lemma wZ_add : ∀ c : ZL, wZ c + 2 * (if c = .z0 then 1 else 0) = 2 := by decide

theorem remark_5_2_strings : Remark_5_2_strings := by
  have h1 : ∀ {L : ℕ} (ξ : XStr L), ∑ ℓ, wX (ξ ℓ) + (TX ξ).card = 2 * (QX ξ).card := by
    intro L ξ
    rw [TX, QX, card_filter, card_filter, ← sum_add_distrib, mul_sum]
    exact sum_congr rfl fun ℓ _ => wX_add (ξ ℓ)
  have h2 : ∀ {L : ℕ} (η : YStr L), ∑ ℓ, wY (η ℓ) = (TY η).card := by
    intro L η
    rw [TY, card_filter]
    exact sum_congr rfl fun ℓ _ => wY_eq (η ℓ)
  have h3 : ∀ {L : ℕ} (ζ : ZStr L), ∑ ℓ, wZ (ζ ℓ) + 2 * (QZ ζ).card = 2 * L := by
    intro L ζ
    rw [QZ, card_filter, mul_sum, ← sum_add_distrib]
    rw [sum_congr rfl fun ℓ _ => wZ_add (ζ ℓ)]
    simp [mul_comm]
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro L m s u v w hu hv hw1 hw2 hsu hsv
    have a1 := h1 u.1
    have a2 := h2 u.2
    have a3 := h2 v.1
    have a4 := h1 v.2
    have a5 := h3 w.1
    have a6 := h3 w.2
    have hmL : m ≤ L := by
      rw [← hw1]
      exact (card_le_univ _).trans (by simp)
    refine ⟨?_, ?_, ?_⟩
    · omega
    · omega
    · omega
  · intro N f hf hsum ℓ
    have hle : ∀ i ∈ (univ : Finset (Fin N)), (fun _ => (2 : ℕ)) i ≤ f i := fun i _ => hf i
    have heq : ∑ i : Fin N, (fun _ => (2 : ℕ)) i = ∑ i, f i := by simp [hsum, mul_comm]
    exact ((Finset.sum_eq_sum_iff_of_le hle).1 heq ℓ (mem_univ ℓ)).symm

end ThinMatrixProducts

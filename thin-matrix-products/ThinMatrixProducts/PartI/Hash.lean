import Statements
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Data.Fintype.Powerset

/-!
# Section 4: the re-indexing maps are bijective on good sets

If the columns of a matrix `M` over `F₂` at a set `S` of `r` levels are linearly independent and
`M` has `r` rows, then `T ↦ M[T]` (the sum of the columns at `T`) is a bijection from the subsets
of `S` onto `F₂^r`: injective because `M[T]` is the linear combination of the columns at `S` with
the indicator of `T` as coefficients, onto because both sides have `2^r` elements.
-/

namespace ThinMatrixProducts

open Finset

/-- `M[T]` for `T ⊆ S` is the linear combination of the columns at `S` with the indicator of `T`. -/
lemma colSum_eq_linearCombination {r L : ℕ} (M : Matrix (Fin r) (Fin L) (ZMod 2))
    (S T : Finset (Fin L)) (hT : T ⊆ S) :
    colSum M T = Fintype.linearCombination (ZMod 2) (fun ℓ : S => fun i => M i ℓ)
      (fun ℓ => if (ℓ : Fin L) ∈ T then 1 else 0) := by
  rw [Fintype.linearCombination_apply, colSum]
  simp only [ite_smul, one_smul, zero_smul]
  rw [Finset.sum_coe_sort S (fun ℓ => if ℓ ∈ T then (fun i => M i ℓ) else 0), ← Finset.sum_filter]
  congr 1
  ext ℓ
  simp only [mem_filter]
  exact ⟨fun h => ⟨hT h, h⟩, fun h => h.2⟩

/-- The bijection of Section 4. -/
theorem colSum_bijOn {r L : ℕ} (M : Matrix (Fin r) (Fin L) (ZMod 2)) (S : Finset (Fin L))
    (hS : S.card = r) (hli : LinearIndependent (ZMod 2) (fun ℓ : S => fun i => M i ℓ)) :
    Set.BijOn (colSum M) (S.powerset : Set (Finset (Fin L))) Set.univ := by
  have hinj : Set.InjOn (colSum M) (S.powerset : Set (Finset (Fin L))) := by
    intro T₁ h₁ T₂ h₂ h
    simp only [coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, coe_subset] at h₁ h₂
    rw [colSum_eq_linearCombination M S T₁ h₁, colSum_eq_linearCombination M S T₂ h₂] at h
    have h' := hli.fintypeLinearCombination_injective h
    ext ℓ
    constructor
    · intro hℓ
      have := congrFun h' ⟨ℓ, h₁ hℓ⟩
      simp only [hℓ, if_true] at this
      by_contra hn
      simp [hn] at this
    · intro hℓ
      have := congrFun h' ⟨ℓ, h₂ hℓ⟩
      simp only [hℓ, if_true] at this
      by_contra hn
      simp [hn] at this
  refine ⟨fun _ _ => Set.mem_univ _, hinj, ?_⟩
  -- onto: the image has `2^r` elements
  have hcard : (S.powerset.image (colSum M)).card = Fintype.card (Fin r → ZMod 2) := by
    rw [card_image_of_injOn (by simpa using hinj), card_powerset, hS]
    simp [ZMod.card]
  have himg : S.powerset.image (colSum M) = univ := eq_univ_of_card _ hcard
  intro c _
  have : c ∈ S.powerset.image (colSum M) := by rw [himg]; exact mem_univ c
  obtain ⟨T, hT, rfl⟩ := mem_image.1 this
  exact ⟨T, by simpa using hT, rfl⟩

theorem sec4_bijections : Sec4_bijections := by
  intro L m Γ Δ Q ⟨hQ, hΓ, hΔ⟩
  refine ⟨colSum_bijOn Γ Q hQ hΓ, colSum_bijOn Δ Qᶜ ?_ hΔ⟩
  rw [card_compl, Fintype.card_fin, hQ]

end ThinMatrixProducts

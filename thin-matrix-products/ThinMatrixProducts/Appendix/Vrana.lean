import Statements
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Proposition A.11: Vrana's partial product gives no saving

The identity and the cyclic symmetry are checked by `ring`. For the bound, every read output `w`
has the set `𝒯(w)` of leaves with `τ₁` or `τ₂` at a level with `x₁₂`, `τ₂` or `τ₃` at a level with
`x₂₁`, `τ₅` at `x₁₁` and `τ₄` at `x₂₂`. A leaf of `𝒯(w)` with `j` symbols `τ₂` lies in `𝒯(w')` for
at most `2^j` outputs `w'`, so `|⋃ 𝒯(w)| ≥ ∑_w ∑_{τ ∈ 𝒯(w)} 2^{-j(τ)} = |W| (3/2)^m`.
-/

namespace ThinMatrixProducts

open Finset

theorem prop_A_11_identity : Prop_A_11_identity := by
  intro R _ e x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22
  simp only [Fin.sum_univ_five, vranaTerms, vranaM]
  ring

theorem prop_A_11_symmetry : Prop_A_11_symmetry := by
  intro R _ e x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22
  refine ⟨by simp only [vranaM]; ring, ?_⟩
  simp only [vranaTerms]
  refine ⟨by ring, by ring, by ring, by ring, by ring⟩

/-- The terms allowed at a level with output `o` in `𝒯(w)`. -/
def vranaAllowed : Fin 4 → Finset (Fin 5)
  | 0 => {4}
  | 1 => {0, 1}
  | 2 => {1, 2}
  | 3 => {3}

/-- The outputs for which a term is allowed. -/
def vranaPre : Fin 5 → Finset (Fin 4)
  | 0 => {1}
  | 1 => {1, 2}
  | 2 => {2}
  | 3 => {3}
  | 4 => {0}

/-- The weight `2^{-[t = τ₂]}`. -/
noncomputable def vranaWeight (t : Fin 5) : ℝ := if t = 1 then 1 / 2 else 1

lemma vranaAllowed_contains : ∀ o t, t ∈ vranaAllowed o → vranaContains t o = true := by decide

lemma mem_vranaPre : ∀ o t, t ∈ vranaAllowed o ↔ o ∈ vranaPre t := by decide

lemma sum_vranaWeight (o : Fin 4) :
    ∑ t ∈ vranaAllowed o, vranaWeight t = if o = 1 ∨ o = 2 then 3 / 2 else 1 := by
  fin_cases o <;> simp [vranaAllowed, vranaWeight] <;> norm_num

lemma weight_mul_card_pre (t : Fin 5) : vranaWeight t * (vranaPre t).card = 1 := by
  fin_cases t <;> simp [vranaWeight, vranaPre] <;> norm_num

theorem prop_A_11 : Prop_A_11 := by
  intro L m W hW leaves
  set T : (Fin L → Fin 4) → Finset (Fin L → Fin 5) :=
    fun w => Fintype.piFinset fun ℓ => vranaAllowed (w ℓ) with hT
  set c : (Fin L → Fin 5) → ℝ := fun τ => ∏ ℓ, vranaWeight (τ ℓ) with hc
  -- the sum over one `𝒯(w)` is `(3/2)^m`
  have hsumT : ∀ w ∈ W, ∑ τ ∈ T w, c τ = (3 / 2) ^ m := by
    intro w hw
    rw [hT, hc, ← Finset.prod_univ_sum]
    simp_rw [sum_vranaWeight]
    rw [Finset.prod_ite, prod_const, prod_const_one, mul_one, ← hW w hw]
  -- a leaf lies in `𝒯(w)` for at most `1/c(τ)` outputs
  have hmult : ∀ τ : Fin L → Fin 5, ((W.filter fun w => τ ∈ T w).card : ℝ) * c τ ≤ 1 := by
    intro τ
    have hsub : (W.filter fun w => τ ∈ T w) ⊆ Fintype.piFinset fun ℓ => vranaPre (τ ℓ) := by
      intro w hw
      rw [mem_filter, hT, Fintype.mem_piFinset] at hw
      rw [Fintype.mem_piFinset]
      exact fun ℓ => (mem_vranaPre _ _).1 (hw.2 ℓ)
    have hcard := card_le_card hsub
    rw [Fintype.card_piFinset] at hcard
    have hw0 : ∀ t, 0 ≤ vranaWeight t := fun t => by unfold vranaWeight; split_ifs <;> norm_num
    have hc0 : 0 ≤ c τ := by
      rw [hc]
      exact prod_nonneg fun ℓ _ => hw0 _
    calc ((W.filter fun w => τ ∈ T w).card : ℝ) * c τ
        ≤ ((∏ ℓ, (vranaPre (τ ℓ)).card : ℕ) : ℝ) * c τ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc0
      _ = ∏ ℓ, (vranaWeight (τ ℓ) * (vranaPre (τ ℓ)).card) := by
          rw [hc, Nat.cast_prod, ← prod_mul_distrib]
          refine prod_congr rfl fun ℓ _ => by ring
      _ = 1 := by simp_rw [weight_mul_card_pre]; simp
  -- double counting
  set U := W.biUnion T
  have hU : U ⊆ leaves := by
    intro τ hτ
    obtain ⟨w, hw, hτw⟩ := mem_biUnion.1 hτ
    rw [hT, Fintype.mem_piFinset] at hτw
    exact mem_filter.2 ⟨mem_univ _, w, hw, fun ℓ => vranaAllowed_contains _ _ (hτw ℓ)⟩
  have hdouble : ∑ w ∈ W, ∑ τ ∈ T w, c τ = ∑ τ ∈ U, ∑ _w ∈ W.filter (fun w => τ ∈ T w), c τ := by
    apply Finset.sum_comm'
    intro w τ
    simp only [U, mem_biUnion, mem_filter]
    constructor
    · rintro ⟨hw, hτ⟩; exact ⟨⟨hw, hτ⟩, w, hw, hτ⟩
    · rintro ⟨⟨hw, hτ⟩, -⟩; exact ⟨hw, hτ⟩
  have hmain : (W.card : ℝ) * (3 / 2) ^ m ≤ leaves.card := by
    calc (W.card : ℝ) * (3 / 2) ^ m = ∑ w ∈ W, ∑ τ ∈ T w, c τ := by
          rw [sum_congr rfl hsumT, sum_const, nsmul_eq_mul]
      _ = ∑ τ ∈ U, ((W.filter fun w => τ ∈ T w).card : ℝ) * c τ := by
          rw [hdouble]; refine sum_congr rfl fun τ _ => ?_; rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ _τ ∈ U, (1 : ℝ) := sum_le_sum fun τ _ => hmult τ
      _ = U.card := by simp
      _ ≤ leaves.card := by exact_mod_cast card_le_card hU
  -- `2^{m/2 - 1} ≤ (3/2)^m`
  have hroot : (2 : ℝ) ^ ((m : ℝ) / 2 - 1) ≤ (3 / 2) ^ m := by
    have h1 : (2 : ℝ) ^ ((m : ℝ) / 2 - 1) ≤ 2 ^ ((m : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2 : ℝ) ^ ((m : ℝ) / 2) = ((2 : ℝ) ^ (1 / 2 : ℝ)) ^ m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
    have h3 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 3 / 2 := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_left (by norm_num)]; norm_num
    rw [h2] at h1
    exact h1.trans (pow_le_pow_left₀ (by positivity) h3 m)
  refine ⟨hmain, le_trans (mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg _)) hmain, ?_⟩
  intro N hN
  calc N ^ 2 / 2 = (W.card : ℝ) * 2 ^ ((m : ℝ) / 2 - 1) := by
        rw [hN, mul_assoc, ← Real.rpow_add (by norm_num)]
        rw [show -(m : ℝ) / 2 + ((m : ℝ) / 2 - 1) = -1 by ring, Real.rpow_neg_one]; ring
    _ ≤ (W.card : ℝ) * (3 / 2) ^ m := mul_le_mul_of_nonneg_left hroot (Nat.cast_nonneg _)
    _ ≤ leaves.card := hmain

end ThinMatrixProducts

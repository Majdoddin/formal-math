import Mathlib

/-!
# Lemma 19.5 of the paper (the identity over `ℂ`): the global count is a Fourier transform

For a finite additive commutative group `R`, maps `fᵢ : Xᵢ → R` and finsets `Sᵢ`,
`|R| · #{(x₁,x₂,x₃) ∈ S₁×S₂×S₃ : f₁ x₁ + f₂ x₂ + f₃ x₃ = 0} = Σ_ψ ĉ₁(ψ) ĉ₂(ψ) ĉ₃(ψ)`, with
`ĉᵢ(ψ) = Σ_{x ∈ Sᵢ} ψ(fᵢ x)`. In the application `fᵢ = K` restricted to the list `Sᵢ`, and the
left side is `|R| · Z(K)`.
-/

namespace GroupLean

open Finset

theorem fourier_count {R : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]
    {X₁ X₂ X₃ : Type*} (f₁ : X₁ → R) (f₂ : X₂ → R) (f₃ : X₃ → R)
    (S₁ : Finset X₁) (S₂ : Finset X₂) (S₃ : Finset X₃) :
    (Fintype.card R : ℂ)
        * ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => f₁ t.1 + f₂ t.2.1 + f₃ t.2.2 = 0).card
      = ∑ ψ : AddChar R ℂ,
          (∑ x ∈ S₁, ψ (f₁ x)) * (∑ x ∈ S₂, ψ (f₂ x)) * (∑ x ∈ S₃, ψ (f₃ x)) := by
  have h : ∀ ψ : AddChar R ℂ,
      (∑ x ∈ S₁, ψ (f₁ x)) * (∑ x ∈ S₂, ψ (f₂ x)) * (∑ x ∈ S₃, ψ (f₃ x))
        = ∑ t ∈ S₁ ×ˢ S₂ ×ˢ S₃, ψ (f₁ t.1 + f₂ t.2.1 + f₃ t.2.2) := by
    intro ψ
    rw [sum_mul_sum, sum_mul, sum_product]
    refine sum_congr rfl fun x _ => ?_
    rw [sum_mul, sum_product]
    refine sum_congr rfl fun y _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
  simp_rw [h]
  rw [sum_comm]
  simp_rw [AddChar.sum_apply_eq_ite]
  rw [sum_ite, sum_const, sum_const_zero, add_zero, nsmul_eq_mul, mul_comm]

end GroupLean

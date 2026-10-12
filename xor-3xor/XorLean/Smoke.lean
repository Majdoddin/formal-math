import Mathlib

/-! Smoke test of the set-up: vectors of `F_2^ℓ` as `Fin ℓ → ZMod 2`, sums over all of them,
a multiset of them, the inner product `⬝ᵥ`, the character `(-1)^⟨u,v⟩`, and `Real.rpow`. -/

open Finset

abbrev Vec (ℓ : ℕ) := Fin ℓ → ZMod 2

example (ℓ : ℕ) : Fintype.card (Vec ℓ) = 2 ^ ℓ := by simp

/-- The character `(-1)^⟨u,v⟩` as an integer. -/
def chi {ℓ : ℕ} (u v : Vec ℓ) : ℤ := (-1) ^ (u ⬝ᵥ v).val

example (ℓ : ℕ) (u : Vec ℓ) : ∑ v : Vec ℓ, chi u v = ∑ v : Vec ℓ, chi v u := by
  simp [chi, dotProduct_comm]

example (ℓ : ℕ) (E : Multiset (Vec ℓ)) (v : Vec ℓ) :
    (E.map fun u => chi u v).sum = (E.map fun u => chi u v).sum := rfl

example (u v : Vec 3) : (u + v) + v = u := by
  have h : ∀ a b : ZMod 2, a + b + b = a := by decide
  ext i
  exact h _ _

example (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by norm_cast

example : Real.exp 1 = Real.exp 1 := rfl

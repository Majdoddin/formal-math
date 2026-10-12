import Mathlib

/-! Smoke test of the set-up. -/

example (p d : ℕ) [Fact p.Prime] : Fintype.card (Fin d → ZMod p) = p ^ d := by simp

example {R : Type*} [AddCommGroup R] [Fintype R] (ψ : AddChar R ℂ) (x y : R) :
    ψ (x + y) = ψ x * ψ y := AddChar.map_add_eq_mul ψ x y

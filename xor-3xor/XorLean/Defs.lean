import Mathlib

/-!
# Shared definitions of the 3-XOR note's formalization

Definitions only, shared by the other files. No theorem lives here.
-/

namespace Xor

/-- `F_2^ℓ`. -/
abbrev Vec (ℓ : ℕ) := Fin ℓ → ZMod 2

/-- The character `(-1)^⟨u,v⟩`. -/
def chi {ℓ : ℕ} (u v : Vec ℓ) : ℤ := if u ⬝ᵥ v = 0 then 1 else -1

/-- The map with rows `rows`: `x ↦ (⟨rows[i], x⟩)_i`. -/
def rowsMap {ℓ : ℕ} (rows : List (Vec ℓ)) : Vec ℓ →ₗ[ZMod 2] Vec rows.length :=
  Matrix.mulVecLin (Matrix.of fun i => rows.get i)

/-- Definition 2: an ε-biased multiset, the average multiplied out. -/
def IsBiased {ℓ : ℕ} (ε : ℝ) (E : Multiset (Vec ℓ)) : Prop :=
  E ≠ 0 ∧ ∀ v : Vec ℓ, v ≠ 0 → |((E.map fun u => (chi u v : ℝ)).sum)| ≤ ε * E.card

/-- The note's `Φ`: the weight of the `v_j` that every row sends to `0`. -/
noncomputable def surv {ℓ : ℕ} {ι : Type*} (s : Finset ι) (v : ι → Vec ℓ) (ω : ι → ℝ)
    (rows : List (Vec ℓ)) : ℝ :=
  ∑ j ∈ s with ∀ u ∈ rows, u ⬝ᵥ v j = 0, ω j

/-- `rows` (newest first) was chosen greedily from `E` for the cost `f`. -/
def IsGreedy {ℓ : ℕ} (E : Multiset (Vec ℓ)) (f : List (Vec ℓ) → ℝ) : List (Vec ℓ) → Prop
  | [] => True
  | u :: rows => IsGreedy E f rows ∧ u ∈ E ∧ ∀ u' ∈ E, f (u :: rows) ≤ f (u' :: rows)

/-- An instance of Exact-XOR-Triangle. -/
structure TriInst (A B C : Type*) (d : ℕ) where
  wab : A → B → Vec d
  wbc : B → C → Vec d
  wac : A → C → Vec d

namespace TriInst
variable {A B C : Type*} {d : ℕ}

def S (I : TriInst A B C d) (a : A) (b : B) (c : C) : Vec d := I.wab a b + I.wbc b c + I.wac a c

def HasZeroTriangle (I : TriInst A B C d) : Prop := ∃ a b c, I.S a b c = 0

/-- `Z(G)`: the triples that the linear map `G` sends to zero. -/
noncomputable def Z [Fintype A] [Fintype B] [Fintype C] {q : ℕ} (I : TriInst A B C d)
    (G : Vec d →ₗ[ZMod 2] Vec q) : ℕ :=
  open Classical in
  (Finset.univ.filter fun t : A × B × C => G (I.S t.1 t.2.1 t.2.2) = 0).card

end TriInst

/-- Convolution-3XOR over an index group `ι`; `none` is the empty entry. -/
def ConvHasSol {ι : Type*} [Add ι] {d : ℕ} (A B C : ι → Option (Vec d)) : Prop :=
  ∃ i j : ι, ∃ a b c : Vec d, A i = some a ∧ B j = some b ∧ C (i + j) = some c ∧ a + b + c = 0

end Xor

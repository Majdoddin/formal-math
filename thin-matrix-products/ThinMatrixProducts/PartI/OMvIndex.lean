import Statements

/-!
# Proposition 10.3: the index identities

The Boolean entry `(U N_{I,J} V)_{i,j}` through the two products that the two regions preprocess:
`X := U`, `Y := N_{I,[n]}` (first region) and `X := N_{I,J}`, `Y := V` (second region), with
repeated indices allowed in `I` and `J`.
-/

namespace ThinMatrixProducts

open Matrix

/-- Over `ℕ`, an entry of a product is positive iff one of its terms is. -/
lemma natMul_pos_iff {m k p : Type} [Fintype k] (A : Matrix m k ℕ) (B : Matrix k p ℕ) (i : m)
    (j : p) : 0 < (A * B) i j ↔ ∃ b, 0 < A i b ∧ 0 < B b j := by
  rw [Matrix.mul_apply, Finset.sum_pos_iff]
  simp [Nat.pos_iff_ne_zero]

lemma natOf_pos_iff {m k : Type} (A : Matrix m k Bool) (i : m) (a : k) :
    0 < natOf A i a ↔ A i a = true := by
  cases h : A i a <;> simp [natOf, h]

/-- The Boolean product is the positivity pattern of the `0/1` product over `ℕ`. -/
lemma boolMatMul_eq_true_iff {m k p : Type} [Fintype k] (A : Matrix m k Bool)
    (B : Matrix k p Bool) (i : m) (j : p) :
    boolMatMul A B i j = true ↔ 0 < (natOf A * natOf B) i j := by
  rw [natMul_pos_iff]
  simp [boolMatMul, natOf_pos_iff]

lemma natOf_boolMatMul_pos_iff {m k p : Type} [Fintype k] (A : Matrix m k Bool)
    (B : Matrix k p Bool) (i : m) (j : p) :
    0 < natOf (boolMatMul A B) i j ↔ 0 < (natOf A * natOf B) i j := by
  rw [natOf_pos_iff, boolMatMul_eq_true_iff]

lemma boolMatMul_assoc {m k l p : Type} [Fintype k] [Fintype l] (A : Matrix m k Bool)
    (B : Matrix k l Bool) (C : Matrix l p Bool) :
    boolMatMul (boolMatMul A B) C = boolMatMul A (boolMatMul B C) := by
  have key : ∀ x y : Matrix m p Bool, (∀ i j, x i j = true ↔ y i j = true) → x = y := by
    intro x y h; ext i j; exact Bool.eq_iff_iff.mpr (h i j)
  refine key _ _ fun i j => ?_
  unfold boolMatMul
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨b, ⟨a, h1, h2⟩, h3⟩; exact ⟨a, h1, b, h2, h3⟩
  · rintro ⟨a, h1, b, h2, h3⟩; exact ⟨b, ⟨a, h1, h2⟩, h3⟩

theorem remark_10_3_index_nat : Remark_10_3_index_nat := by
  intro n t₁ t₂ U N V I J
  have hcol : U * N.submatrix I J = (U * N.submatrix I id).submatrix id J := by
    ext i b; simp [Matrix.mul_apply]
  refine ⟨hcol, ?_, ?_⟩
  · intro i j
    rw [natMul_pos_iff, hcol]
    simp
  · intro i j
    rw [Matrix.mul_assoc, natMul_pos_iff]

theorem remark_10_3_index : Remark_10_3_index := by
  intro n t₁ t₂ U N V I J
  have hsub : ∀ (r s : Type) (f : r → Fin n) (g : s → Fin n),
      natOf (N.submatrix f g) = (natOf N).submatrix f g := fun _ _ _ _ => rfl
  obtain ⟨hcol, h1, h2⟩ := remark_10_3_index_nat n t₁ t₂ (natOf U) (natOf N) (natOf V) I J
  refine ⟨boolMatMul_assoc _ _ _, hcol, ?_, ?_, ?_⟩
  · intro i j
    have hb : ∀ b, boolMatMul U (N.submatrix I J) i b = true ↔
        0 < (natOf U * (natOf N).submatrix I id) i (J b) := by
      intro b
      rw [boolMatMul_eq_true_iff, hsub, hcol]
      rfl
    unfold boolMatMul at hb ⊢
    simp only [decide_eq_true_eq] at hb ⊢
    simp_rw [hb]
  · intro i j
    have ha : ∀ a, boolMatMul (N.submatrix I J) V a j = true ↔
        0 < ((natOf N).submatrix I J * natOf V) a j := by
      intro a
      rw [boolMatMul_eq_true_iff, hsub]
    rw [boolMatMul_assoc]
    unfold boolMatMul at ha ⊢
    simp only [decide_eq_true_eq] at ha ⊢
    simp_rw [ha]
  · intro β σ
    ext a b; simp [Matrix.mul_apply]

end ThinMatrixProducts

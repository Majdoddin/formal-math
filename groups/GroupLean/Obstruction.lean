import Mathlib

/-!
# Proposition 19.13 of the paper (no universal homomorphic hashing beyond elementary groups)

For a homomorphism `K : G → R` and subgroups `A, B ≤ G` with `|K(A)| · |K(B)| ≤ |K(G)|`:
`|A| · |B| ≤ |A ∩ ker K| · |B ∩ ker K| · |K(G)|` (`obstruction`). The hypothesis holds in the two
instances of Proposition 19.13 (`hyp_of_nsmul`, `hyp_of_coprime`), and for `G = Z₄^d`, `A = B = 2G` the
conclusion holds for every `K` (`z4_obstruction`).
-/

namespace GroupLean

/-- `|H| = |H ∩ ker φ| · |φ(H)|` (first isomorphism theorem for `φ` restricted to `H`). -/
theorem card_eq_card_inf_ker_mul_card_map {G R : Type*} [AddGroup G] [AddGroup R]
    (φ : G →+ R) (H : AddSubgroup G) :
    Nat.card H = Nat.card (H ⊓ φ.ker : AddSubgroup G) * Nat.card (H.map φ) := by
  set f : H →+ R := φ.comp H.subtype with hf
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker, mul_comm,
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv]
  congr 1
  · apply Nat.card_congr
    exact
      { toFun := fun x => ⟨x.1.1, AddSubgroup.mem_inf.mpr
            ⟨x.1.2, AddMonoidHom.mem_ker.mpr (AddMonoidHom.mem_ker.mp x.2)⟩⟩
        invFun := fun y => ⟨⟨y.1, (AddSubgroup.mem_inf.mp y.2).1⟩,
            AddMonoidHom.mem_ker.mpr (AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp y.2).2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  · rw [hf, AddMonoidHom.range_comp, AddSubgroup.range_subtype]

/-- **Proposition C.** -/
theorem obstruction {G R : Type*} [AddCommGroup G] [AddCommGroup R]
    (K : G →+ R) (A B : AddSubgroup G)
    (h : Nat.card (A.map K) * Nat.card (B.map K) ≤ Nat.card K.range) :
    Nat.card A * Nat.card B
      ≤ Nat.card (A ⊓ K.ker : AddSubgroup G) * Nat.card (B ⊓ K.ker : AddSubgroup G)
          * Nat.card K.range := by
  rw [card_eq_card_inf_ker_mul_card_map K A, card_eq_card_inf_ker_mul_card_map K B]
  calc Nat.card (A ⊓ K.ker : AddSubgroup G) * Nat.card (A.map K)
        * (Nat.card (B ⊓ K.ker : AddSubgroup G) * Nat.card (B.map K))
      = Nat.card (A ⊓ K.ker : AddSubgroup G) * Nat.card (B ⊓ K.ker : AddSubgroup G)
          * (Nat.card (A.map K) * Nat.card (B.map K)) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ h

lemma finite_of_le {R : Type*} [AddGroup R] {S T : AddSubgroup R} [Finite T] (h : S ≤ T) :
    Finite S :=
  Finite.of_injective (AddSubgroup.inclusion h) (AddSubgroup.inclusion_injective h)

lemma finite_range {G R : Type*} [AddGroup G] [AddGroup R] [Finite G] (K : G →+ R) :
    Finite K.range :=
  Finite.of_surjective _ K.rangeRestrict_surjective

/-- Instance (i): `A ⊆ p·G` and `p·B = 0`. Then `K(A) ⊆ p·K(G)`, `K(B) ⊆ K(G)[p]`, and
`|p·H| · |H[p]| = |H|` for `H = K(G)`. -/
theorem hyp_of_nsmul {G R : Type*} [AddCommGroup G] [AddCommGroup R] [Finite G]
    (K : G →+ R) (A B : AddSubgroup G) (p : ℕ)
    (hA : ∀ a ∈ A, ∃ x : G, p • x = a) (hB : ∀ b ∈ B, p • b = 0) :
    Nat.card (A.map K) * Nat.card (B.map K) ≤ Nat.card K.range := by
  have := finite_range K
  set φ : R →+ R := nsmulAddMonoidHom p
  set H := K.range
  have hT1 : H.map φ ≤ H := by
    rw [AddSubgroup.map_le_iff_le_comap]
    intro y hy
    exact AddSubgroup.nsmul_mem H hy p
  have hT2 : H ⊓ φ.ker ≤ H := inf_le_left
  have := finite_of_le hT1
  have := finite_of_le hT2
  have h1 : A.map K ≤ H.map φ := by
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨x, rfl⟩ := hA a ha
    exact ⟨K x, (AddMonoidHom.mem_range.mpr ⟨x, rfl⟩), by simp [φ]⟩
  have h2 : B.map K ≤ H ⊓ φ.ker := by
    rintro y ⟨b, hb, rfl⟩
    refine AddSubgroup.mem_inf.mpr ⟨(AddMonoidHom.mem_range.mpr ⟨b, rfl⟩), ?_⟩
    rw [AddMonoidHom.mem_ker]
    simp [φ, ← map_nsmul, hB b hb]
  rw [card_eq_card_inf_ker_mul_card_map φ H, mul_comm]
  exact Nat.mul_le_mul (AddSubgroup.card_le_of_le h2) (AddSubgroup.card_le_of_le h1)

/-- Instance (ii): `p·A = 0`, `q·B = 0` with `p, q` coprime. Then `K(A) ∩ K(B) = 0`, so
`(x, y) ↦ x + y` embeds `K(A) × K(B)` into `K(G)`. -/
theorem hyp_of_coprime {G R : Type*} [AddCommGroup G] [AddCommGroup R] [Finite G]
    (K : G →+ R) (A B : AddSubgroup G) (p q : ℕ) (hpq : Nat.Coprime p q)
    (hA : ∀ a ∈ A, p • a = 0) (hB : ∀ b ∈ B, q • b = 0) :
    Nat.card (A.map K) * Nat.card (B.map K) ≤ Nat.card K.range := by
  have := finite_range K
  have hA' : ∀ y ∈ A.map K, p • y = 0 := by
    rintro y ⟨a, ha, rfl⟩
    rw [← map_nsmul, hA a ha, map_zero]
  have hB' : ∀ y ∈ B.map K, q • y = 0 := by
    rintro y ⟨b, hb, rfl⟩
    rw [← map_nsmul, hB b hb, map_zero]
  have hAr : A.map K ≤ K.range := by
    rintro y ⟨a, -, rfl⟩; exact (AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)
  have hBr : B.map K ≤ K.range := by
    rintro y ⟨b, -, rfl⟩; exact (AddMonoidHom.mem_range.mpr ⟨b, rfl⟩)
  let Φ : (A.map K) × (B.map K) → K.range := fun xy =>
    ⟨xy.1.1 + xy.2.1, add_mem (hAr xy.1.2) (hBr xy.2.2)⟩
  have hΦ : Function.Injective Φ := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ he
    have he' : x + y = x' + y' := congrArg Subtype.val he
    set z := x - x' with hz
    have hz1 : p • z = 0 := by
      rw [hz, nsmul_sub, hA' x hx, hA' x' hx', sub_zero]
    have hz2 : q • z = 0 := by
      have : z = y' - y := by rw [hz]; linear_combination (norm := abel_nf) he'
      rw [this, nsmul_sub, hB' y hy, hB' y' hy', sub_zero]
    have hord : addOrderOf z = 1 := Nat.dvd_one.mp
      (Nat.Coprime.gcd_eq_one hpq ▸
        Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hz1) (addOrderOf_dvd_of_nsmul_eq_zero hz2))
    have hz0 : z = 0 := AddMonoid.addOrderOf_eq_one_iff.mp hord
    have hxx : x = x' := sub_eq_zero.mp hz0
    have hyy : y = y' := by rw [hxx] at he'; exact add_left_cancel he'
    subst hxx hyy
    rfl
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective Φ hΦ

/-- The subgroup `2G` of `G = Z₄^d`. -/
def twoG (d : ℕ) : AddSubgroup (Fin d → ZMod 4) := (nsmulAddMonoidHom 2).range

/-- For `G = Z₄^d` and `A = B = 2G`: every homomorphism `K` kills at least
`|A|² / |K(G)|` pairs, `|A ∩ ker K|² · |K(G)| ≥ |A|²`. -/
theorem z4_obstruction (d : ℕ) {R : Type*} [AddCommGroup R] (K : (Fin d → ZMod 4) →+ R) :
    Nat.card (twoG d) ^ 2
      ≤ Nat.card (twoG d ⊓ K.ker : AddSubgroup (Fin d → ZMod 4)) ^ 2 * Nat.card K.range := by
  have hA : ∀ a ∈ twoG d, ∃ x, 2 • x = a := by
    rintro a ⟨x, rfl⟩; exact ⟨x, rfl⟩
  have hB : ∀ b ∈ twoG d, 2 • b = 0 := by
    rintro b ⟨x, rfl⟩
    funext i
    change 2 • (2 • x i) = 0
    rw [← mul_nsmul, nsmul_eq_mul]
    have : ((2 * 2 : ℕ) : ZMod 4) = 0 := by decide
    rw [this, zero_mul]
  have h := obstruction K (twoG d) (twoG d) (hyp_of_nsmul K _ _ 2 hA hB)
  rw [sq, sq]
  exact h

end GroupLean

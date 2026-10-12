import GroupLean.Coord

/-!
# Proposition F: where the dichotomy stops

(a) The `Z₄` Latin square `c = a + b` in `ZMod 4` is representable over `ZMod 4`; any
representation over `A` produces `x ∈ A` with `2 • x ≠ 0` and `4 • x = 0`, so it is not
representable over a group of exponent 2, a torsion-free group, or a `ZMod p`-module (`p` an odd
prime). By exclusivity it has no one-coordinate OV gadget.

(b) The loop `L5` (rows `01234, 10342, 24013, 32401, 43120`) is not representable over any
abelian group: the equation at `(0,0,1)` is an integer combination of the 25 defining equations
(coefficients `l5_combination`, found by a script that is not part of this repository), and
`g 0 0 = 0 ≠ 1`. It has no one-coordinate OV gadget (exhaustive search, `decide +kernel`).
-/

namespace GroupLean

/-! ### (a) The `Z₄` Latin square -/

/-- `c = a + b` in `ZMod 4`. -/
abbrev z4Rel (a b c : ZMod 4) : Prop := c = a + b

theorem z4Rel_rep : RepresentableOver (ZMod 4) z4Rel :=
  ⟨id, id, fun c => -c, 0, fun a b c => by
    show c = a + b ↔ a + b + -c = 0
    constructor <;> intro h <;> linear_combination -h⟩

/-- Any representation of the `Z₄` square yields an element of order exactly 4. -/
theorem z4Rel_order4 {A : Type*} [AddCommGroup A] (hr : RepresentableOver A z4Rel) :
    ∃ x : A, 2 • x ≠ 0 ∧ 4 • x = 0 := by
  obtain ⟨φ₁, φ₂, φ₃, t, h⟩ := hr
  have E : ∀ a b c : ZMod 4, c = a + b → φ₁ a + φ₂ b + φ₃ c = t := fun a b c hc => (h a b c).1 hc
  have E000 := E 0 0 0 (by decide)
  have E101 := E 1 0 1 (by decide)
  have E011 := E 0 1 1 (by decide)
  have E022 := E 0 2 2 (by decide)
  have E033 := E 0 3 3 (by decide)
  have E112 := E 1 1 2 (by decide)
  have E123 := E 1 2 3 (by decide)
  have E130 := E 1 3 0 (by decide)
  have p1 : φ₁ 1 - φ₁ 0 = -(φ₃ 1 - φ₃ 0) := by linear_combination (norm := module) E101 - E000
  have q1 : φ₂ 1 - φ₂ 0 = -(φ₃ 1 - φ₃ 0) := by linear_combination (norm := module) E011 - E000
  have q2 : φ₂ 2 - φ₂ 0 = -(φ₃ 2 - φ₃ 0) := by linear_combination (norm := module) E022 - E000
  have q3 : φ₂ 3 - φ₂ 0 = -(φ₃ 3 - φ₃ 0) := by linear_combination (norm := module) E033 - E000
  have d2 : φ₃ 2 - φ₃ 0 = 2 • (φ₃ 1 - φ₃ 0) := by
    linear_combination (norm := module) E112 - E000 - p1 - q1
  have d3 : φ₃ 3 - φ₃ 0 = 3 • (φ₃ 1 - φ₃ 0) := by
    linear_combination (norm := module) E123 - E000 - p1 - q2 + d2
  refine ⟨φ₃ 1 - φ₃ 0, fun h2 => ?_, ?_⟩
  · have h020 : z4Rel 0 2 0 := (h 0 2 0).2 (by
      linear_combination (norm := module) E000 + q2 - d2 - h2)
    exact absurd h020 (by decide)
  · linear_combination (norm := module) -E130 + E000 + p1 + q3 - d3

/-- Not representable over `A` if `4 • x = 0 → 2 • x = 0` in `A`. -/
theorem z4Rel_not_rep_of {A : Type*} [AddCommGroup A] (hA : ∀ x : A, 4 • x = 0 → 2 • x = 0) :
    ¬ RepresentableOver A z4Rel := fun hr => by
  obtain ⟨x, h2, h4⟩ := z4Rel_order4 hr
  exact h2 (hA x h4)

theorem z4Rel_not_rep_exp2 {A : Type*} [AddCommGroup A] (hA : ∀ x : A, 2 • x = 0) :
    ¬ RepresentableOver A z4Rel :=
  z4Rel_not_rep_of fun x _ => hA x

theorem z4Rel_not_rep_torsionFree {A : Type*} [AddCommGroup A]
    (hA : ∀ (n : ℕ) (x : A), n ≠ 0 → n • x = 0 → x = 0) : ¬ RepresentableOver A z4Rel :=
  z4Rel_not_rep_of fun x h4 => by rw [hA 4 x (by norm_num) h4, smul_zero]

theorem z4Rel_not_rep_zmod {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {A : Type*} [AddCommGroup A]
    [Module (ZMod p) A] : ¬ RepresentableOver A z4Rel := by
  refine z4Rel_not_rep_of fun x h4 => ?_
  have hpx : p • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]
  have hcop : IsCoprime (4 : ℤ) (p : ℤ) := by
    rw [show (4 : ℤ) = ((2 ^ 2 : ℕ) : ℤ) by norm_num, Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_left 2
      ((Nat.coprime_primes Nat.prime_two (Fact.out)).2 (Ne.symm hp))
  obtain ⟨u, v, huv⟩ := hcop
  have hx : x = 0 := by
    calc x = (u * 4 + v * p) • x := by rw [huv, one_smul]
      _ = u • ((4 : ℤ) • x) + v • ((p : ℤ) • x) := by rw [add_smul, mul_smul, mul_smul]
      _ = 0 := by rw [natCast_zsmul, hpx, smul_zero, add_zero,
          show (4 : ℤ) • x = ((4 : ℕ) : ℤ) • x by norm_num, natCast_zsmul, h4, smul_zero]
  rw [hx, smul_zero]

/-- The `Z₄` square has no one-coordinate OV gadget (it is representable). -/
theorem z4Rel_not_hasGadget : ¬ HasGadget z4Rel := not_hasGadget_of_rep z4Rel_rep

/-! ### (b) The loop `L5` -/

/-- The loop `L5`: row `a`, column `b`, entry `l5 a b`. -/
def l5 : Fin 5 → Fin 5 → Fin 5 :=
  ![![0, 1, 2, 3, 4], ![1, 0, 3, 4, 2], ![2, 4, 0, 1, 3], ![3, 2, 4, 0, 1], ![4, 3, 1, 2, 0]]

/-- The relation `c = l5 a b`. -/
abbrev l5Rel (a b c : Fin 5) : Prop := l5 a b = c

/-- `L5` is not representable over any additive commutative group:
`φ(0,0,1) = -φ(0,1,1) + φ(0,2,2) + φ(0,3,3) + 2φ(1,0,1) - φ(1,2,3) - φ(1,3,4) - φ(2,0,2)
+ φ(2,1,4)` as formal combinations, and the coefficients sum to 1. -/
theorem l5Rel_not_rep {A : Type*} [AddCommGroup A] : ¬ RepresentableOver A l5Rel := by
  rintro ⟨φ₁, φ₂, φ₃, t, h⟩
  have E : ∀ a b c : Fin 5, l5 a b = c → φ₁ a + φ₂ b + φ₃ c = t := fun a b c hc => (h a b c).1 hc
  have E011 := E 0 1 1 (by decide)
  have E022 := E 0 2 2 (by decide)
  have E033 := E 0 3 3 (by decide)
  have E101 := E 1 0 1 (by decide)
  have E123 := E 1 2 3 (by decide)
  have E134 := E 1 3 4 (by decide)
  have E202 := E 2 0 2 (by decide)
  have E214 := E 2 1 4 (by decide)
  have h001 : l5Rel 0 0 1 := (h 0 0 1).2 (by
    linear_combination (norm := module)
      -E011 + E022 + E033 + 2 • E101 - E123 - E134 - E202 + E214)
  exact absurd h001 (by decide)

/-- `L5` as a Boolean function on `ℕ` (for the exhaustive gadget search). -/
def relL5 (a b c : ℕ) : Bool :=
  [0, 1, 2, 3, 4, 1, 0, 3, 4, 2, 2, 4, 0, 1, 3, 3, 2, 4, 0, 1, 4, 3, 1, 2, 0].getD (5 * a + b) 0 == c

theorem relL5_iff : ∀ a b c : Fin 5, relL5 a b c = true ↔ l5Rel a b c := by
  unfold l5Rel; decide +kernel

theorem l5_noGadgetB : noGadgetB 5 relL5 = true := by decide +kernel

/-- `L5` has no one-coordinate OV gadget (exhaustive search over all side assignments and all
maps `Bool → Fin 5`). -/
theorem l5Rel_not_hasGadget : ¬ HasGadget l5Rel := fun hg =>
  not_hasGadget_of_noGadgetB l5_noGadgetB (hg.of_iff fun a b c => (relL5_iff a b c).symm)

end GroupLean

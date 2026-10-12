import GroupLean.ExpP2L

/-!
# Case L: the rows are chosen by computable counts (§19, "Residue rows", "Choosing the pair rows")

The algorithm of Case L chooses each residue row by minimising `Z` of `x ↦ (⟨r_i, x̄⟩)_i`, and
each pair row by minimising `p^{t+1}Z₁ + Dp^{t+1}Z₂ + p^{2t+2}(Z₃ − Z₂)`, with `Z₁, Z₂, Z₃` the
counts `Z` of three homomorphisms. This file proves that these choices are the greedy choices
for the type-II count and for `Ψ` used in `ExpP2L.lean`:

* `Zc_resMap`: `Z(x ↦ (⟨r_i, x̄⟩)_i) = T_I + #{type II : all ⟨r_i, v̄⟩ = 0}`; `isGreedy_resMap_iff`.
* `Z1_eq`, `Z2_eq`, `Z3_eq`: `Z₁ = T_I + 𝖸_t`, `Z₂ = Z₀ + 𝖲_t`, `Z₃ = Z₀ + 𝖲_t + 𝖠_t`.
* `cost_eq`: `p^t Z₁ + Dp^t Z₂ + p^{2t}(Z₃ − Z₂) = Ψ_t + p^t(T_I + D Z₀)`;
  `isGreedyL_cost_iff`: minimising the computable cost is minimising `Ψ`.
-/

set_option linter.unusedSectionVars false

namespace GroupLean
namespace CaseL

open Finset ExpP2 OneHash

variable {p : ℕ} [Fact p.Prime] {d : ℕ}

/-- The map of a list of residue rows: `x ↦ (⟨r_i, x̄⟩)_i`. -/
def resMap (rr : List (VecP p d)) : Vp p d →+ (Fin rr.length → ZMod p) where
  toFun x i := rr.get i ⬝ᵥ residue x
  map_zero' := by funext i; simp [residue_zero]
  map_add' x y := by funext i; simp [residue_add, dotProduct_add]

theorem resMap_eq_zero_iff (rr : List (VecP p d)) (x : Vp p d) :
    resMap rr x = 0 ↔ ∀ r ∈ rr, r ⬝ᵥ residue x = 0 := by
  change (fun i : Fin rr.length => rr.get i ⬝ᵥ residue x) = 0 ↔ _
  rw [funext_iff]
  exact forall_get_iff rr (fun r => r ⬝ᵥ residue x = 0)

variable (S₁ S₂ S₃ : Finset (Vp p d))

/-- **Residue rows**: `Z(x ↦ (⟨r_i, x̄⟩)_i) = T_I + #{type II : ⟨r_i, v̄⟩ = 0 for all i}`. -/
theorem Zc_resMap (rr : List (VecP p d)) :
    (Zc S₁ S₂ S₃ (resMap rr) : ℝ) = (TIset S₁ S₂ S₃).card + survII S₁ S₂ S₃ rr := by
  rw [survII_eq]
  have h := Finset.card_filter_add_card_filter_not
    (s := (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => resMap rr (t.1 + t.2.1 + t.2.2) = 0)
    (fun t => residue (t.1 + t.2.1 + t.2.2) = 0)
  have e1 : (((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => resMap rr (t.1 + t.2.1 + t.2.2) = 0).filter
      fun t => residue (t.1 + t.2.1 + t.2.2) = 0) = TIset S₁ S₂ S₃ := by
    ext t
    simp only [TIset, Finset.mem_filter, resMap_eq_zero_iff]
    constructor
    · rintro ⟨⟨hm, -⟩, h0⟩; exact ⟨hm, h0⟩
    · rintro ⟨hm, h0⟩
      exact ⟨⟨hm, fun r _ => by rw [h0, dotProduct_zero]⟩, h0⟩
  have e2 : (((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => resMap rr (t.1 + t.2.1 + t.2.2) = 0).filter
      fun t => ¬ residue (t.1 + t.2.1 + t.2.2) = 0) = (typeII S₁ S₂ S₃).filter fun t =>
        ∀ r ∈ rr, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0 := by
    ext t
    simp only [typeII, Finset.mem_filter, resMap_eq_zero_iff]
    tauto
  rw [e1, e2] at h
  unfold Zc
  rw [← h]
  push_cast
  ring

/-- Minimising `Z` of the residue map is the greedy choice for the type-II count. -/
theorem isGreedy_resMap_iff (E : Multiset (VecP p d)) (rs : List (VecP p d)) :
    IsGreedy E (fun l => (Zc S₁ S₂ S₃ (resMap l) : ℝ)) rs ↔ IsGreedy E (survII S₁ S₂ S₃) rs := by
  have : (fun l => (Zc S₁ S₂ S₃ (resMap l) : ℝ)) =
      fun l => survII S₁ S₂ S₃ l + ((TIset S₁ S₂ S₃).card : ℝ) := by
    funext l; rw [Zc_resMap]; ring
  rw [this, isGreedy_add_const]

variable (rs : List (VecP p d)) (q : ℕ)

/-- `Z₁ = Z(x ↦ (ρ(x̄), (⟨a_i, x̄⟩)_{i≤t})) = T_I + 𝖸_t`. -/
theorem Z1_eq (l : List (VecP p d × VecP p d)) :
    Zc S₁ S₂ S₃ (piLL (rs.drop q) l) = (TIset S₁ S₂ S₃).card + cntL (JY S₁ S₂ S₃ rs q) PY l := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => piLL (rs.drop q) l (t.1 + t.2.1 + t.2.2) = 0)
    (fun t => residue (t.1 + t.2.1 + t.2.2) = 0)
  have e1 : (((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => piLL (rs.drop q) l (t.1 + t.2.1 + t.2.2) = 0).filter
      fun t => residue (t.1 + t.2.1 + t.2.2) = 0) = TIset S₁ S₂ S₃ := by
    ext t
    simp only [TIset, Finset.mem_filter, piLL_eq_zero_iff]
    constructor
    · rintro ⟨⟨hm, -⟩, h0⟩; exact ⟨hm, h0⟩
    · rintro ⟨hm, h0⟩
      exact ⟨⟨hm, fun r _ => by rw [h0, dotProduct_zero], fun c _ => by rw [h0, dotProduct_zero]⟩,
        h0⟩
  have e2 : (((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => piLL (rs.drop q) l (t.1 + t.2.1 + t.2.2) = 0).filter
      fun t => ¬ residue (t.1 + t.2.1 + t.2.2) = 0) =
      (JY S₁ S₂ S₃ rs q).filter fun t => ∀ c ∈ l, PY t c := by
    ext t
    simp only [JY, typeII, Finset.mem_filter, piLL_eq_zero_iff, PY]
    tauto
  rw [e1, e2] at h
  unfold Zc cntL
  rw [← h]
  congr!

/-- `Z₂ = Z(x ↦ (ρ(x̄), ρ''(x̄), (⟨u_i, x⟩)_{i≤t})) = Z₀ + 𝖲_t`. -/
theorem Z2_eq (l : List (VecP p d × VecP p d)) :
    Zc S₁ S₂ S₃ (KLL rs l) = Zsol S₁ S₂ S₃ + cntL (JS S₁ S₂ S₃ rs) PK l := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => KLL rs l (t.1 + t.2.1 + t.2.2) = 0)
    (fun t => t.1 + t.2.1 + t.2.2 = 0)
  have e1 : (((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => KLL rs l (t.1 + t.2.1 + t.2.2) = 0).filter
      fun t => t.1 + t.2.1 + t.2.2 = 0) =
      (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => t.1 + t.2.1 + t.2.2 = 0 := by
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hm, -⟩, h0⟩; exact ⟨hm, h0⟩
    · rintro ⟨hm, h0⟩; exact ⟨⟨hm, by rw [h0, map_zero]⟩, h0⟩
  have e2 : (((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => KLL rs l (t.1 + t.2.1 + t.2.2) = 0).filter
      fun t => ¬ t.1 + t.2.1 + t.2.2 = 0) = (JS S₁ S₂ S₃ rs).filter fun t => ∀ c ∈ l, PK t c := by
    ext t
    simp only [JS, Finset.mem_filter, KLL_eq_zero_iff, PK]
    tauto
  rw [e1, e2] at h
  unfold Zc Zsol cntL
  rw [← h]
  congr!

/-- `Z₃ = Z(K_t) = Z₀ + 𝖲_t + 𝖠_t`. -/
theorem Z3_eq (l : List (VecP p d × VecP p d)) :
    Zc S₁ S₂ S₃ (KLL (rs.drop q) l) =
      Zsol S₁ S₂ S₃ + cntL (JS S₁ S₂ S₃ rs) PK l + cntL (JA S₁ S₂ S₃ rs q) PK l := by
  set T := (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => KLL (rs.drop q) l (t.1 + t.2.1 + t.2.2) = 0
  have h := Finset.card_filter_add_card_filter_not (s := T) (fun t => t.1 + t.2.1 + t.2.2 = 0)
  have h' := Finset.card_filter_add_card_filter_not
    (s := T.filter fun t => ¬ t.1 + t.2.1 + t.2.2 = 0)
    (fun t => ∀ r ∈ rs.take q, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0)
  have e1 : (T.filter fun t => t.1 + t.2.1 + t.2.2 = 0) =
      (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => t.1 + t.2.1 + t.2.2 = 0 := by
    ext t
    simp only [T, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hm, -⟩, h0⟩; exact ⟨hm, h0⟩
    · rintro ⟨hm, h0⟩; exact ⟨⟨hm, by rw [h0, map_zero]⟩, h0⟩
  have hsplit : ∀ x : Vp p d, (∀ r ∈ rs, r ⬝ᵥ residue x = 0) ↔
      (∀ r ∈ rs.take q, r ⬝ᵥ residue x = 0) ∧ ∀ r ∈ rs.drop q, r ⬝ᵥ residue x = 0 := by
    intro x
    conv_lhs => rw [← List.take_append_drop q rs]
    simp only [List.mem_append]
    constructor
    · intro h; exact ⟨fun r hr => h r (Or.inl hr), fun r hr => h r (Or.inr hr)⟩
    · rintro ⟨h1, h2⟩ r (hr | hr)
      · exact h1 r hr
      · exact h2 r hr
  have e2 : ((T.filter fun t => ¬ t.1 + t.2.1 + t.2.2 = 0).filter
      fun t => ∀ r ∈ rs.take q, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0) =
      (JS S₁ S₂ S₃ rs).filter fun t => ∀ c ∈ l, PK t c := by
    ext t
    simp only [T, JS, Finset.mem_filter, KLL_eq_zero_iff, PK, hsplit]
    tauto
  have e3 : ((T.filter fun t => ¬ t.1 + t.2.1 + t.2.2 = 0).filter
      fun t => ¬ ∀ r ∈ rs.take q, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0) =
      (JA S₁ S₂ S₃ rs q).filter fun t => ∀ c ∈ l, PK t c := by
    ext t
    simp only [T, JA, typeII, Finset.mem_filter, KLL_eq_zero_iff, PK]
    constructor
    · rintro ⟨⟨⟨hm, hr, hu⟩, hv⟩, htake⟩
      refine ⟨⟨⟨hm, fun h0 => htake fun r _ => by rw [h0, dotProduct_zero]⟩, hr, htake⟩, hu⟩
    · rintro ⟨⟨⟨hm, hres⟩, hr, htake⟩, hu⟩
      refine ⟨⟨⟨hm, hr, hu⟩, fun h0 => hres (by rw [h0, residue_zero])⟩, htake⟩
  rw [e2, e3] at h'
  rw [e1, ← h'] at h
  have hZ : Zc S₁ S₂ S₃ (KLL (rs.drop q) l) = T.card := rfl
  rw [hZ, ← h, ← add_assoc]
  unfold Zsol cntL
  congr!

/-- The computable cost of a list of pair rows:
`p^t Z₁ + D p^t Z₂ + p^{2t}(Z₃ − Z₂)`, `t = |l|`, `D = p^q`. -/
noncomputable def costL (l : List (VecP p d × VecP p d)) : ℝ :=
  (p : ℝ) ^ l.length * Zc S₁ S₂ S₃ (piLL (rs.drop q) l) +
    (p : ℝ) ^ q * (p : ℝ) ^ l.length * Zc S₁ S₂ S₃ (KLL rs l) +
    (p : ℝ) ^ (2 * l.length) *
      ((Zc S₁ S₂ S₃ (KLL (rs.drop q) l) : ℝ) - Zc S₁ S₂ S₃ (KLL rs l))

/-- **"Choosing the pair rows"**: the computable cost is `Ψ_t + p^t(T_I + D Z₀)`. -/
theorem costL_eq (l : List (VecP p d × VecP p d)) :
    costL S₁ S₂ S₃ rs q l = Psi S₁ S₂ S₃ rs q l +
      (p : ℝ) ^ l.length * ((TIset S₁ S₂ S₃).card + (p : ℝ) ^ q * Zsol S₁ S₂ S₃) := by
  unfold costL Psi
  rw [Z1_eq, Z2_eq, Z3_eq]
  push_cast
  ring

theorem isGreedyL_add_len {α : Type*} (C : Multiset α) (f : List α → ℝ) (g : ℕ → ℝ)
    (l : List α) : IsGreedyL C (fun l => f l + g l.length) l ↔ IsGreedyL C f l := by
  induction l with
  | nil => exact Iff.rfl
  | cons c l ih =>
    simp only [IsGreedyL, List.length_cons, add_le_add_iff_right]
    rw [ih]

/-- Minimising the computable cost is the greedy choice for `Ψ`. -/
theorem isGreedyL_costL_iff (E : Multiset (VecP p d)) (prs : List (VecP p d × VecP p d)) :
    IsGreedyL (E ×ˢ E) (costL S₁ S₂ S₃ rs q) prs ↔ IsGreedyL (E ×ˢ E) (Psi S₁ S₂ S₃ rs q) prs := by
  have : costL S₁ S₂ S₃ rs q = fun l => Psi S₁ S₂ S₃ rs q l +
      (fun t : ℕ => (p : ℝ) ^ t * ((TIset S₁ S₂ S₃).card + (p : ℝ) ^ q * Zsol S₁ S₂ S₃))
        l.length := by
    funext l; rw [costL_eq]
  rw [this]
  exact isGreedyL_add_len (E ×ˢ E) (Psi S₁ S₂ S₃ rs q)
    (fun t : ℕ => (p : ℝ) ^ t * ((TIset S₁ S₂ S₃).card + (p : ℝ) ^ q * Zsol S₁ S₂ S₃)) prs

end CaseL
end GroupLean

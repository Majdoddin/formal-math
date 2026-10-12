import ThinMatrixProducts.PartI.Identity
import ThinMatrixProducts.PartI.Hash
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Theorem 5.1: the squared run

The proof is the weight argument of Remark 5.2. By [ZT, Lemma 8] on the `2L` levels
(`lemma_8_squared`), the runs compute `∑_s ∑_{u,v} ∏_ℓ γ_ℓ a_s[u] b_s[v]`. A summand with
`∏ γ_ℓ ≠ 0`, `a_s[u] ≠ 0` and `b_s[v] ≠ 0` has total weight `(2m+s) + (2m-s) + 4(L-m) = 4L` over
the `2L` levels, while every level carries weight at least `2`; so every level carries exactly `2`,
which happens only for the monomials of `G`, with coefficient `1` (`remark_5_2_weights`). The
summands that remain are indexed by the pairs `T' ⊆ Q(w')`, `T'' ⊆ Q(w'')`, each in exactly one
run, and the sum over them is the matrix entry by the bijections of Section 4.
-/

namespace ThinMatrixProducts

open Finset

/-! ## Lemma 8 on the `2L` levels -/

/-- `γ` written with an indicator. -/
lemma gamma_eq_sum_ite (s : XL) (t : YL) (z : ZL) :
    gamma s t z = ∑ lam, if chi lam z ≠ 0 then phi lam s * psi lam t else 0 := by
  rw [gamma, sum_filter]

/-- `∏_ℓ γ(…)` over the levels as a sum over strings of terms. -/
lemma prod_gamma_eq {L : ℕ} (f : Fin L → Tm → ℤ) (P : Fin L → Tm → Prop)
    [∀ ℓ lam, Decidable (P ℓ lam)] :
    (∏ ℓ, ∑ lam, if P ℓ lam then f ℓ lam else 0)
      = ∑ τ : Fin L → Tm, if ∀ ℓ, P ℓ (τ ℓ) then ∏ ℓ, f ℓ (τ ℓ) else 0 := by
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr (by simp) fun τ _ => ?_
  rw [Finset.prod_ite_zero]
  simp

theorem lemma_8_squared : Lemma_8_squared := by
  intro L a b w
  -- the inner identity, for fixed `u` and `v`
  have key : ∀ (u : LeftStr L) (v : RightStr L),
      (∑ τ : Leaf L, if Contributes τ w then
          ((∏ ℓ, phi (τ.1 ℓ) (u.1 ℓ)) * ∏ ℓ, psi (τ.2 ℓ) (u.2 ℓ))
            * ((∏ ℓ, psi (τ.1 ℓ) (v.1 ℓ)) * ∏ ℓ, phi (τ.2 ℓ) (v.2 ℓ)) else 0)
        = (∏ ℓ, gamma (u.1 ℓ) (v.1 ℓ) (w.1 ℓ)) * ∏ ℓ, gamma (v.2 ℓ) (u.2 ℓ) (w.2 ℓ) := by
    intro u v
    simp_rw [gamma_eq_sum_ite]
    rw [prod_gamma_eq (fun ℓ lam => phi lam (u.1 ℓ) * psi lam (v.1 ℓ))
        (fun ℓ lam => chi lam (w.1 ℓ) ≠ 0),
      prod_gamma_eq (fun ℓ lam => phi lam (v.2 ℓ) * psi lam (u.2 ℓ))
        (fun ℓ lam => chi lam (w.2 ℓ) ≠ 0), Finset.sum_mul_sum, ← Fintype.sum_prod_type']
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [Contributes, forall_and]
    split_ifs <;> simp_all [Finset.prod_mul_distrib] <;> ring
  -- unfold `Mult`, expand the products of sums, and exchange the sums
  have expand : ∀ τ : Leaf L, PhiL τ a * PsiR τ b
      = ∑ u, ∑ v, a u * b v * (((∏ ℓ, phi (τ.1 ℓ) (u.1 ℓ)) * ∏ ℓ, psi (τ.2 ℓ) (u.2 ℓ))
            * ((∏ ℓ, psi (τ.1 ℓ) (v.1 ℓ)) * ∏ ℓ, phi (τ.2 ℓ) (v.2 ℓ))) := by
    intro τ
    rw [PhiL, PsiR, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [Mult, sum_filter]
  simp_rw [expand]
  calc (∑ τ : Leaf L, if Contributes τ w then ∑ u, ∑ v, a u * b v *
          (((∏ ℓ, phi (τ.1 ℓ) (u.1 ℓ)) * ∏ ℓ, psi (τ.2 ℓ) (u.2 ℓ))
            * ((∏ ℓ, psi (τ.1 ℓ) (v.1 ℓ)) * ∏ ℓ, phi (τ.2 ℓ) (v.2 ℓ))) else 0)
      = ∑ τ : Leaf L, ∑ u, ∑ v, a u * b v * (if Contributes τ w then
          (((∏ ℓ, phi (τ.1 ℓ) (u.1 ℓ)) * ∏ ℓ, psi (τ.2 ℓ) (u.2 ℓ))
            * ((∏ ℓ, psi (τ.1 ℓ) (v.1 ℓ)) * ∏ ℓ, phi (τ.2 ℓ) (v.2 ℓ))) else 0) := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        split_ifs <;> simp
    _ = ∑ u, ∑ v, ∑ τ : Leaf L, a u * b v * (if Contributes τ w then
          (((∏ ℓ, phi (τ.1 ℓ) (u.1 ℓ)) * ∏ ℓ, psi (τ.2 ℓ) (u.2 ℓ))
            * ((∏ ℓ, psi (τ.1 ℓ) (v.1 ℓ)) * ∏ ℓ, phi (τ.2 ℓ) (v.2 ℓ))) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
        rw [← Finset.mul_sum, key]
        ring

/-! ## The level facts -/

/-- The index read off a left letter at an outer level (`ι`). -/
def xIdx : XL → Fin 2 | .x i => i | .p _ => 0
/-- The first index of an output letter (`ι`). -/
def zIdx : ZL → Fin 2 | .z i _ => i | .z0 => 0

lemma iotaX_apply {L : ℕ} (ξ : XStr L) (ℓ : Fin L) : iotaX ξ ℓ = xIdx (ξ ℓ) := by
  unfold iotaX xIdx; cases ξ ℓ <;> rfl

lemma iotaZ_apply {L : ℕ} (ζ : ZStr L) (ℓ : Fin L) : iotaZ ζ ℓ = zIdx (ζ ℓ) := by
  unfold iotaZ zIdx; cases ζ ℓ <;> rfl

/-- What a monomial of `G` says about its three letters. -/
lemma isG_facts : ∀ (s : XL) (t : YL) (z : ZL), IsGMonomial s t z →
    ((∃ k, s = .p k) ↔ z = .z0) ∧ (s = .p 1 ↔ t = .q) ∧ (t = .y 1 ↔ ∃ i, z = .z i 1) ∧
      xIdx s = zIdx z ∧ gamma s t z = 1 := by
  decide

/-- Every level carries weight at least 2, and exactly 2 only at a monomial of `G`. -/
lemma weight_facts : ∀ (s : XL) (t : YL) (z : ZL), gamma s t z ≠ 0 →
    2 ≤ wX s + wY t + wZ z ∧ (wX s + wY t + wZ z = 2 → IsGMonomial s t z) := by
  decide

lemma sum_wX {L : ℕ} (ξ : XStr L) :
    (∑ ℓ, (wX (ξ ℓ) : ℤ)) = 2 * (QX ξ).card - (TX ξ).card := by
  have h : ∀ ℓ, (wX (ξ ℓ) : ℤ) = 2 * (if ∃ k, ξ ℓ = .p k then 1 else 0)
      - (if ξ ℓ = .p 1 then 1 else 0) := by
    intro ℓ
    rcases ξ ℓ with i | k
    · simp [wX]
    · fin_cases k <;> simp [wX]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_boole, QX, TX]

lemma sum_wY {L : ℕ} (η : YStr L) : (∑ ℓ, (wY (η ℓ) : ℤ)) = (TY η).card := by
  have h : ∀ ℓ, (wY (η ℓ) : ℤ) = if η ℓ = .q then 1 else 0 := by
    intro ℓ; rcases η ℓ with j | _ <;> simp [wY]
  simp_rw [h]
  rw [Finset.sum_boole, TY]

lemma sum_wZ {L : ℕ} (ζ : ZStr L) : (∑ ℓ, (wZ (ζ ℓ) : ℤ)) = 2 * (L - (QZ ζ).card) := by
  have h : ∀ ℓ, (wZ (ζ ℓ) : ℤ) = 2 - 2 * (if ζ ℓ = .z0 then 1 else 0) := by
    intro ℓ; rcases ζ ℓ with ⟨i, j⟩ | _ <;> simp [wZ]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, QZ]
  simp
  ring

lemma TX_subset_QX {L : ℕ} (ξ : XStr L) : TX ξ ⊆ QX ξ := by
  intro ℓ h
  simp only [TX, QX, mem_filter, mem_univ, true_and] at h ⊢
  exact ⟨1, h⟩

/-! ## The structure of the surviving summands -/

/-- The summands that survive: a monomial of `G` at every level of both halves (the second half
read with left and right exchanged). -/
def GS {L : ℕ} (w : OutStr L) (u : LeftStr L) (v : RightStr L) : Prop :=
  ∀ ℓ, IsGMonomial (u.1 ℓ) (v.1 ℓ) (w.1 ℓ) ∧ IsGMonomial (v.2 ℓ) (u.2 ℓ) (w.2 ℓ)

instance {L : ℕ} (w : OutStr L) (u : LeftStr L) (v : RightStr L) : Decidable (GS w u v) := by
  unfold GS; infer_instance

/-- The facts about a surviving summand that the theorem uses. -/
lemma GS.facts {L : ℕ} {w : OutStr L} {u : LeftStr L} {v : RightStr L} (h : GS w u v) :
    QX u.1 = QZ w.1 ∧ TY v.1 = TX u.1 ∧ SY v.1 = SZ w.1 ∧ iotaX u.1 = iotaZ w.1 ∧
    QX v.2 = QZ w.2 ∧ TY u.2 = TX v.2 ∧ SY u.2 = SZ w.2 ∧ iotaX v.2 = iotaZ w.2 ∧
    (∏ ℓ, gamma (u.1 ℓ) (v.1 ℓ) (w.1 ℓ)) * (∏ ℓ, gamma (v.2 ℓ) (u.2 ℓ) (w.2 ℓ)) = 1 := by
  have f1 := fun ℓ => isG_facts _ _ _ (h ℓ).1
  have f2 := fun ℓ => isG_facts _ _ _ (h ℓ).2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext ℓ; simp only [QX, QZ, mem_filter, mem_univ, true_and]; exact (f1 ℓ).1
  · ext ℓ; simp only [TY, TX, mem_filter, mem_univ, true_and]; exact (f1 ℓ).2.1.symm
  · ext ℓ; simp only [SY, SZ, mem_filter, mem_univ, true_and]; exact (f1 ℓ).2.2.1
  · funext ℓ; rw [iotaX_apply, iotaZ_apply]; exact (f1 ℓ).2.2.2.1
  · ext ℓ; simp only [QX, QZ, mem_filter, mem_univ, true_and]; exact (f2 ℓ).1
  · ext ℓ; simp only [TY, TX, mem_filter, mem_univ, true_and]; exact (f2 ℓ).2.1.symm
  · ext ℓ; simp only [SY, SZ, mem_filter, mem_univ, true_and]; exact (f2 ℓ).2.2.1
  · funext ℓ; rw [iotaX_apply, iotaZ_apply]; exact (f2 ℓ).2.2.2.1
  · rw [Finset.prod_eq_one fun ℓ _ => (f1 ℓ).2.2.2.2, Finset.prod_eq_one fun ℓ _ => (f2 ℓ).2.2.2.2,
      one_mul]

/-- The weight argument: a summand with nonzero coefficient, with `Q(u'), Q(v'')` of size `m`, with
`Q(w'), Q(w'')` of size `m` and with equal runs on both sides is a surviving summand. -/
lemma GS_of_weight {L m : ℕ} {w : OutStr L} {u : LeftStr L} {v : RightStr L}
    (hw1 : (QZ w.1).card = m) (hw2 : (QZ w.2).card = m) (hu : (QX u.1).card = m)
    (hv : (QX v.2).card = m)
    (hs : ((TY u.2).card : ℤ) - (TX u.1).card = ((TX v.2).card : ℤ) - (TY v.1).card)
    (hc : (∏ ℓ, gamma (u.1 ℓ) (v.1 ℓ) (w.1 ℓ)) * (∏ ℓ, gamma (v.2 ℓ) (u.2 ℓ) (w.2 ℓ)) ≠ 0) :
    GS w u v := by
  have hc1 : ∀ ℓ, gamma (u.1 ℓ) (v.1 ℓ) (w.1 ℓ) ≠ 0 := fun ℓ h =>
    hc (by rw [Finset.prod_eq_zero (f := fun i => gamma (u.1 i) (v.1 i) (w.1 i)) (mem_univ ℓ) h,
      zero_mul])
  have hc2 : ∀ ℓ, gamma (v.2 ℓ) (u.2 ℓ) (w.2 ℓ) ≠ 0 := fun ℓ h =>
    hc (by rw [Finset.prod_eq_zero (f := fun i => gamma (v.2 i) (u.2 i) (w.2 i)) (mem_univ ℓ) h,
      mul_zero])
  set W1 : Fin L → ℕ := fun ℓ => wX (u.1 ℓ) + wY (v.1 ℓ) + wZ (w.1 ℓ)
  set W2 : Fin L → ℕ := fun ℓ => wX (v.2 ℓ) + wY (u.2 ℓ) + wZ (w.2 ℓ)
  have hL1 : m ≤ L := by rw [← hw1]; exact (card_le_univ _).trans (by simp)
  -- the total weight is `4L`
  have htot : (∑ ℓ, ((W1 ℓ : ℤ) + W2 ℓ)) = 4 * L := by
    simp only [W1, W2, Nat.cast_add, Finset.sum_add_distrib, sum_wX, sum_wY, sum_wZ, hw1, hw2,
      hu, hv]
    push_cast [Nat.cast_sub hL1]
    linarith
  -- every level carries at least `2 + 2`
  have hge : ∀ ℓ, (4 : ℤ) ≤ (W1 ℓ : ℤ) + W2 ℓ := fun ℓ => by
    have := (weight_facts _ _ _ (hc1 ℓ)).1
    have := (weight_facts _ _ _ (hc2 ℓ)).1
    simp only [W1, W2]; push_cast; omega
  have heq : ∀ ℓ, (W1 ℓ : ℤ) + W2 ℓ = 4 := by
    have hsum : ∑ ℓ, ((W1 ℓ : ℤ) + W2 ℓ - 4) = 0 := by
      rw [Finset.sum_sub_distrib, htot]; simp; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun ℓ _ => sub_nonneg.2 (hge ℓ))).1 hsum
    intro ℓ; linarith [this ℓ (mem_univ ℓ)]
  intro ℓ
  have a1 := weight_facts _ _ _ (hc1 ℓ)
  have a2 := weight_facts _ _ _ (hc2 ℓ)
  have e := heq ℓ
  simp only [W1, W2] at e
  push_cast at e
  exact ⟨a1.2 (by omega), a2.2 (by omega)⟩

/-! ## The surviving summands are indexed by `T' ⊆ Q(w')`, `T'' ⊆ Q(w'')` -/

/-- The left string of the first half for `T' ⊆ Q(w')`. -/
def buildX {L : ℕ} (ζ : ZStr L) (T : Finset (Fin L)) : XStr L := fun ℓ =>
  match ζ ℓ with
  | .z i _ => .x i
  | .z0 => if ℓ ∈ T then .p 1 else .p 0

/-- The right string of the first half for `T' ⊆ Q(w')`. -/
def buildY {L : ℕ} (ζ : ZStr L) (T : Finset (Fin L)) : YStr L := fun ℓ =>
  match ζ ℓ with
  | .z _ j => .y j
  | .z0 => if ℓ ∈ T then .q else .y 0

lemma isG_build {L : ℕ} (ζ : ZStr L) (T : Finset (Fin L)) (ℓ : Fin L) :
    IsGMonomial (buildX ζ T ℓ) (buildY ζ T ℓ) (ζ ℓ) := by
  unfold buildX buildY IsGMonomial
  rcases ζ ℓ with ⟨i, j⟩ | _
  · exact Or.inl ⟨i, j, rfl, rfl, rfl⟩
  · by_cases h : ℓ ∈ T <;> simp [h]

lemma buildX_eq_p1 {L : ℕ} (ζ : ZStr L) (T : Finset (Fin L)) (ℓ : Fin L) :
    buildX ζ T ℓ = .p 1 ↔ ζ ℓ = .z0 ∧ ℓ ∈ T := by
  unfold buildX
  rcases ζ ℓ with ⟨i, j⟩ | _
  · simp
  · by_cases h : ℓ ∈ T <;> simp [h]

lemma buildY_eq_q {L : ℕ} (ζ : ZStr L) (T : Finset (Fin L)) (ℓ : Fin L) :
    buildY ζ T ℓ = .q ↔ ζ ℓ = .z0 ∧ ℓ ∈ T := by
  unfold buildY
  rcases ζ ℓ with ⟨i, j⟩ | _
  · simp
  · by_cases h : ℓ ∈ T <;> simp [h]

lemma TX_buildX {L : ℕ} (ζ : ZStr L) (T : Finset (Fin L)) (hT : T ⊆ QZ ζ) :
    TX (buildX ζ T) = T := by
  ext ℓ
  simp only [TX, mem_filter, mem_univ, true_and, buildX_eq_p1]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by simpa [QZ] using hT h, h⟩

lemma TY_buildY {L : ℕ} (ζ : ZStr L) (T : Finset (Fin L)) (hT : T ⊆ QZ ζ) :
    TY (buildY ζ T) = T := by
  ext ℓ
  simp only [TY, mem_filter, mem_univ, true_and, buildY_eq_q]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨by simpa [QZ] using hT h, h⟩

/-- A surviving summand is the one built from its sets `T(u')` and `T(u'')`. -/
lemma GS.eq_build {L : ℕ} {w : OutStr L} {u : LeftStr L} {v : RightStr L} (h : GS w u v) :
    u = (buildX w.1 (TX u.1), buildY w.2 (TY u.2)) ∧
      v = (buildY w.1 (TX u.1), buildX w.2 (TY u.2)) := by
  have f1 := fun ℓ => isG_facts _ _ _ (h ℓ).1
  have f2 := fun ℓ => isG_facts _ _ _ (h ℓ).2
  have hTY : TY u.2 = TX v.2 := h.facts.2.2.2.2.2.1
  refine ⟨Prod.ext (funext fun ℓ => ?_) (funext fun ℓ => ?_),
    Prod.ext (funext fun ℓ => ?_) (funext fun ℓ => ?_)⟩
  all_goals simp only [buildX, buildY, TX, TY, hTY, mem_filter, mem_univ, true_and]
  · have := (h ℓ).1; revert this
    rcases w.1 ℓ with ⟨i, j⟩ | _ <;> rcases u.1 ℓ with i' | k <;> rcases v.1 ℓ with j' | _ <;>
      simp [IsGMonomial] <;> (try fin_cases k) <;> simp_all
  · have := (h ℓ).2; revert this
    rcases w.2 ℓ with ⟨i, j⟩ | _ <;> rcases u.2 ℓ with j' | _ <;> rcases v.2 ℓ with i' | k <;>
      simp [IsGMonomial] <;> (try fin_cases k) <;> simp_all
  · have := (h ℓ).1; revert this
    rcases w.1 ℓ with ⟨i, j⟩ | _ <;> rcases u.1 ℓ with i' | k <;> rcases v.1 ℓ with j' | _ <;>
      simp [IsGMonomial] <;> (try fin_cases k) <;> simp_all
  · have := (h ℓ).2; revert this
    rcases w.2 ℓ with ⟨i, j⟩ | _ <;> rcases u.2 ℓ with j' | _ <;> rcases v.2 ℓ with i' | k <;>
      simp [IsGMonomial] <;> (try fin_cases k) <;> simp_all

/-! ## Theorem 5.1 -/

lemma Good.card {L m : ℕ} {Γ : Matrix (Fin m) (Fin L) (ZMod 2)}
    {Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2)} {Q : Finset (Fin L)} (h : Good Γ Δ Q) :
    Q.card = m := h.1

/-- Lemma 8 on the `2L` levels, as an equation. -/
lemma Mult_eq_sum {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (w : OutStr L) :
    Mult a b w = ∑ u, ∑ v, (∏ ℓ, gamma (u.1 ℓ) (v.1 ℓ) (w.1 ℓ))
      * (∏ ℓ, gamma (v.2 ℓ) (u.2 ℓ) (w.2 ℓ)) * a u * b v :=
  lemma_8_squared a b w

/-- The product of the two arrays of run `s` at `u` and `v`. -/
lemma arrayA_mul_arrayB {L m : ℕ} (Γ : Matrix (Fin m) (Fin L) (ZMod 2))
    (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2)) (𝒢 : Finset (Finset (Fin L)))
    (X : Finset (Fin L) → Matrix (RowIdx L m) (InIdx m) ℤ)
    (Y : Finset (Fin L) → Matrix (InIdx m) (ColIdx L m) ℤ) (u : LeftStr L) (v : RightStr L)
    (s : ℤ) :
    arrayA Γ Δ 𝒢 X s u * arrayB Γ Δ 𝒢 Y s v
      = if s = ((TY u.2).card : ℤ) - (TX u.1).card then
          (if QX u.1 ∈ 𝒢 ∧ QX v.2 ∈ 𝒢 ∧
              ((TX v.2).card : ℤ) - (TY v.1).card = ((TY u.2).card : ℤ) - (TX u.1).card then
            X (QX u.1) (iotaX u.1, colSum Δ (SY u.2)) (colSum Γ (TX u.1), colSum Γ (TY u.2))
              * Y (QX v.2) (colSum Γ (TY v.1), colSum Γ (TX v.2)) (colSum Δ (SY v.1), iotaX v.2)
          else 0) else 0 := by
  unfold arrayA arrayB
  split_ifs <;> simp_all <;> omega

theorem theorem_5_1 : Theorem_5_1 := by
  intro L m Γ Δ 𝒢 hG X Y w hw1 hw2
  have hc1 : (QZ w.1).card = m := (hG _ hw1).card
  have hc2 : (QZ w.2).card = m := (hG _ hw2).card
  -- Step A: Lemma 8, and the sum over the runs moved inside
  have stepA : ∑ s ∈ Icc (-(m : ℤ)) m, Mult (arrayA Γ Δ 𝒢 X s) (arrayB Γ Δ 𝒢 Y s) w
      = ∑ u, ∑ v, ((∏ ℓ, gamma (u.1 ℓ) (v.1 ℓ) (w.1 ℓ)) * ∏ ℓ, gamma (v.2 ℓ) (u.2 ℓ) (w.2 ℓ))
          * ∑ s ∈ Icc (-(m : ℤ)) m, arrayA Γ Δ 𝒢 X s u * arrayB Γ Δ 𝒢 Y s v := by
    simp_rw [Mult_eq_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun s _ => ?_
    ring
  -- Step B: each summand
  have stepB : ∀ u v,
      ((∏ ℓ, gamma (u.1 ℓ) (v.1 ℓ) (w.1 ℓ)) * ∏ ℓ, gamma (v.2 ℓ) (u.2 ℓ) (w.2 ℓ))
          * ∑ s ∈ Icc (-(m : ℤ)) m, arrayA Γ Δ 𝒢 X s u * arrayB Γ Δ 𝒢 Y s v
        = if GS w u v then
            X (QZ w.1) (iotaZ w.1, colSum Δ (SZ w.2)) (colSum Γ (TX u.1), colSum Γ (TY u.2))
              * Y (QZ w.2) (colSum Γ (TX u.1), colSum Γ (TY u.2)) (colSum Δ (SZ w.1), iotaZ w.2)
          else 0 := by
    intro u v
    simp_rw [arrayA_mul_arrayB]
    rw [Finset.sum_ite_eq']
    by_cases hgs : GS w u v
    · obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := hgs.facts
      have hu : QX u.1 ∈ 𝒢 := by rw [f1]; exact hw1
      have hv : QX v.2 ∈ 𝒢 := by rw [f5]; exact hw2
      have hs : ((TX v.2).card : ℤ) - (TY v.1).card = ((TY u.2).card : ℤ) - (TX u.1).card := by
        rw [f2, f6]
      have hrange : ((TY u.2).card : ℤ) - (TX u.1).card ∈ Icc (-(m : ℤ)) m := by
        have a1 : (TX u.1).card ≤ m := by
          rw [← hc1, ← f1]; exact card_le_card (TX_subset_QX _)
        have a2 : (TY u.2).card ≤ m := by
          rw [f6, ← hc2, ← f5]; exact card_le_card (TX_subset_QX _)
        simp only [mem_Icc]; constructor <;> omega
      rw [if_pos hrange, if_pos ⟨hu, hv, hs⟩, if_pos hgs, f9, one_mul, f1, f2, f3, f4, f5, f7, f8,
        ← f6]
    · rw [if_neg hgs]
      by_cases hcond : ((TY u.2).card : ℤ) - (TX u.1).card ∈ Icc (-(m : ℤ)) m ∧
          (QX u.1 ∈ 𝒢 ∧ QX v.2 ∈ 𝒢 ∧
            ((TX v.2).card : ℤ) - (TY v.1).card = ((TY u.2).card : ℤ) - (TX u.1).card)
      · rw [if_pos hcond.1, if_pos hcond.2]
        by_contra hne
        apply hgs
        have hc' : (∏ ℓ, gamma (u.1 ℓ) (v.1 ℓ) (w.1 ℓ)) * (∏ ℓ, gamma (v.2 ℓ) (u.2 ℓ) (w.2 ℓ))
            ≠ 0 := fun h0 => hne (by rw [h0, zero_mul])
        exact GS_of_weight hc1 hc2 (hG _ hcond.2.1).card (hG _ hcond.2.2.1).card
          hcond.2.2.2.symm hc'
      · rw [not_and] at hcond
        by_cases h1 : ((TY u.2).card : ℤ) - (TX u.1).card ∈ Icc (-(m : ℤ)) m
        · rw [if_pos h1, if_neg (hcond h1), mul_zero]
        · rw [if_neg h1, mul_zero]
  -- Step C: the surviving summands are indexed by `T' ⊆ Q'`, `T'' ⊆ Q''`
  have stepC : ∑ u, ∑ v, (if GS w u v then
            X (QZ w.1) (iotaZ w.1, colSum Δ (SZ w.2)) (colSum Γ (TX u.1), colSum Γ (TY u.2))
              * Y (QZ w.2) (colSum Γ (TX u.1), colSum Γ (TY u.2)) (colSum Δ (SZ w.1), iotaZ w.2)
          else 0)
      = ∑ p ∈ (QZ w.1).powerset ×ˢ (QZ w.2).powerset,
          X (QZ w.1) (iotaZ w.1, colSum Δ (SZ w.2)) (colSum Γ p.1, colSum Γ p.2)
            * Y (QZ w.2) (colSum Γ p.1, colSum Γ p.2) (colSum Δ (SZ w.1), iotaZ w.2) := by
    rw [← Fintype.sum_prod_type' (f := fun u v => if GS w u v then
            X (QZ w.1) (iotaZ w.1, colSum Δ (SZ w.2)) (colSum Γ (TX u.1), colSum Γ (TY u.2))
              * Y (QZ w.2) (colSum Γ (TX u.1), colSum Γ (TY u.2)) (colSum Δ (SZ w.1), iotaZ w.2)
          else 0), ← Finset.sum_filter]
    refine Finset.sum_nbij' (fun x => (TX x.1.1, TY x.1.2))
      (fun p => ((buildX w.1 p.1, buildY w.2 p.2), (buildY w.1 p.1, buildX w.2 p.2))) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      have hx' : GS w x.1 x.2 := (mem_filter.1 hx).2
      obtain ⟨f1, -, -, -, f5, f6, -⟩ := hx'.facts
      rw [mem_product, mem_powerset, mem_powerset]
      exact ⟨f1 ▸ TX_subset_QX _, f6 ▸ f5 ▸ TX_subset_QX _⟩
    · intro p _
      rw [mem_filter]
      exact ⟨mem_univ _, fun ℓ => ⟨isG_build _ _ ℓ, isG_build _ _ ℓ⟩⟩
    · intro x hx
      have hx' : GS w x.1 x.2 := (mem_filter.1 hx).2
      obtain ⟨hu, hv⟩ := hx'.eq_build
      rw [← hu, ← hv]
    · intro p hp
      rw [mem_product, mem_powerset, mem_powerset] at hp
      simp only [TX_buildX _ _ hp.1, TY_buildY _ _ hp.2]
    · intro x _; rfl
  -- Step D: the sum over the pairs of sets is the matrix entry
  have stepD : ∑ p ∈ (QZ w.1).powerset ×ˢ (QZ w.2).powerset,
          X (QZ w.1) (iotaZ w.1, colSum Δ (SZ w.2)) (colSum Γ p.1, colSum Γ p.2)
            * Y (QZ w.2) (colSum Γ p.1, colSum Γ p.2) (colSum Δ (SZ w.1), iotaZ w.2)
      = (X (QZ w.1) * Y (QZ w.2)) (iotaZ w.1, colSum Δ (SZ w.2)) (colSum Δ (SZ w.1), iotaZ w.2) := by
    rw [Finset.sum_product, Matrix.mul_apply, Fintype.sum_prod_type]
    have b1 := (sec4_bijections Γ Δ (QZ w.1) (hG _ hw1)).1
    have b2 := (sec4_bijections Γ Δ (QZ w.2) (hG _ hw2)).1
    refine Finset.sum_nbij (colSum Γ) (fun _ _ => mem_univ _) b1.injOn ?_ ?_
    · simpa using b1.surjOn
    · intro T' _
      refine Finset.sum_nbij (colSum Γ) (fun _ _ => mem_univ _) b2.injOn ?_ (fun _ _ => rfl)
      simpa using b2.surjOn
  rw [stepA]
  simp_rw [stepB]
  rw [stepC, stepD]

end ThinMatrixProducts

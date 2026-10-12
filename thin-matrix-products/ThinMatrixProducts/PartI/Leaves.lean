import ThinMatrixProducts.PartI.Squared
import ThinMatrixProducts.Numerics.Mu
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Lemma 6.1: the leaf counts

The leaves that contribute to a `z`-string are free at its inner levels and forced elsewhere; a
basic count (`count_nonP0`) gives `binom(k, e) 4^e` strings with `e` terms other than `P₀` on a set
of `k` levels, and the two halves combine by Vandermonde's identity, as in the paper.
-/

namespace ThinMatrixProducts

open Finset

/-- The term `P_ij` forced at an outer level with output `z_ij`. -/
def forcedTerm : ZL → Tm | .z i j => .P i j | .z0 => .P0

lemma chi_ne_zero_iff : ∀ (lam : Tm) (z : ZL), chi lam z ≠ 0 ↔ (z = .z0 ∨ lam = forcedTerm z) := by
  decide

/-- The basic count: functions with prescribed values off `Q` and exactly `e` values other than
`P₀` on `Q` number `binom(|Q|, e) 4^e`. -/
lemma count_nonP0 {ι : Type} [Fintype ι] [DecidableEq ι] (Q : Finset ι) (c : ι → Tm) (e : ℕ) :
    ((Fintype.piFinset fun ℓ => if ℓ ∈ Q then (univ : Finset Tm) else {c ℓ}).filter
        (fun f => (Q.filter fun ℓ => f ℓ ≠ .P0).card = e)).card = Q.card.choose e * 4 ^ e := by
  set s := (Fintype.piFinset fun ℓ => if ℓ ∈ Q then (univ : Finset Tm) else {c ℓ}).filter
        (fun f => (Q.filter fun ℓ => f ℓ ≠ .P0).card = e)
  have hmaps : ∀ f ∈ s, (Q.filter fun ℓ => f ℓ ≠ .P0) ∈ Q.powersetCard e := by
    intro f hf
    rw [mem_powersetCard]
    exact ⟨filter_subset _ _, (mem_filter.1 hf).2⟩
  rw [card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ S ∈ Q.powersetCard e,
      (s.filter fun f => (Q.filter fun ℓ => f ℓ ≠ .P0) = S).card = 4 ^ e := by
    intro S hS
    obtain ⟨hSQ, hSc⟩ := mem_powersetCard.1 hS
    have : (s.filter fun f => (Q.filter fun ℓ => f ℓ ≠ .P0) = S)
        = Fintype.piFinset fun ℓ => if ℓ ∈ S then (univ.erase Tm.P0)
            else if ℓ ∈ Q then ({Tm.P0} : Finset Tm) else {c ℓ} := by
      ext f
      simp only [s, mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨⟨hA, -⟩, hS'⟩ ℓ
        by_cases h1 : ℓ ∈ S
        · have : ℓ ∈ Q.filter fun ℓ => f ℓ ≠ .P0 := hS' ▸ h1
          simp only [mem_filter] at this
          simp [h1, this.2]
        · by_cases h2 : ℓ ∈ Q
          · have : ℓ ∉ Q.filter fun ℓ => f ℓ ≠ .P0 := hS' ▸ h1
            simp only [mem_filter, not_and, not_not] at this
            simp [h1, h2, this h2]
          · have := hA ℓ
            simp only [h2, if_false] at this
            simp [h1, h2, this]
      · intro hB
        have hfS : (Q.filter fun ℓ => f ℓ ≠ .P0) = S := by
          ext ℓ
          simp only [mem_filter]
          constructor
          · rintro ⟨h2, h3⟩
            by_contra h1
            have := hB ℓ
            simp only [h1, h2, if_false, if_true, mem_singleton] at this
            exact h3 this
          · intro h1
            have := hB ℓ
            simp only [h1, if_true, mem_erase] at this
            exact ⟨hSQ h1, this.1⟩
        refine ⟨⟨fun ℓ => ?_, by rw [hfS, hSc]⟩, hfS⟩
        by_cases h2 : ℓ ∈ Q
        · simp [h2]
        · have h1 : ℓ ∉ S := fun h => h2 (hSQ h)
          have := hB ℓ
          simp only [h1, h2, if_false] at this
          simpa [h2] using this
    rw [this, Fintype.card_piFinset]
    have hc : ∀ ℓ, (if ℓ ∈ S then (univ.erase Tm.P0)
        else if ℓ ∈ Q then ({Tm.P0} : Finset Tm) else {c ℓ}).card = if ℓ ∈ S then 4 else 1 := by
      intro ℓ
      by_cases h1 : ℓ ∈ S
      · simp only [h1, if_true]
        rw [card_erase_of_mem (mem_univ _), card_univ]
        rfl
      · by_cases h2 : ℓ ∈ Q <;> simp [h1, h2]
    simp_rw [hc]
    rw [prod_ite, prod_const, prod_const_one, mul_one, filter_mem_eq_inter, univ_inter, hSc]
  rw [sum_congr rfl hfib, sum_const, card_powersetCard, smul_eq_mul]

/-- The strings of terms that contribute to a `z`-string. -/
lemma contributes_half_iff {L : ℕ} (ζ : ZStr L) (τ : Fin L → Tm) :
    (∀ ℓ, chi (τ ℓ) (ζ ℓ) ≠ 0) ↔
      τ ∈ Fintype.piFinset fun ℓ => if ℓ ∈ QZ ζ then (univ : Finset Tm) else {forcedTerm (ζ ℓ)} := by
  rw [Fintype.mem_piFinset]
  refine forall_congr' fun ℓ => ?_
  rw [chi_ne_zero_iff]
  by_cases h : ζ ℓ = .z0
  · simp [h, QZ]
  · have : ℓ ∉ QZ ζ := by simp [QZ, h]
    simp [this, h]

/-- For a contributing string, the symbols `P₀` lie in the inner set. -/
lemma numP0_of_contrib {L : ℕ} (ζ : ZStr L) (τ : Fin L → Tm) (h : ∀ ℓ, chi (τ ℓ) (ζ ℓ) ≠ 0) :
    numP0 τ + ((QZ ζ).filter fun ℓ => τ ℓ ≠ .P0).card = (QZ ζ).card := by
  have hsub : (univ.filter fun ℓ => τ ℓ = .P0) = (QZ ζ).filter fun ℓ => τ ℓ = .P0 := by
    ext ℓ
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hP
      refine ⟨?_, hP⟩
      have := (chi_ne_zero_iff _ _).1 (h ℓ)
      rcases this with hz | hz
      · simpa [QZ] using hz
      · rcases hζ : ζ ℓ with ⟨i, j⟩ | _
        · rw [hζ] at hz; rw [hP] at hz; simp [forcedTerm] at hz
        · simp [QZ, hζ]
    · exact fun h' => h'.2
  rw [numP0, hsub, card_filter_add_card_filter_not]

/-- The pairs of strings combine by their sums: a fiberwise count. -/
lemma card_filter_add {α β : Type} [DecidableEq α] [DecidableEq β] (s₁ : Finset α)
    (s₂ : Finset β) (f₁ : α → ℕ) (f₂ : β → ℕ) (d : ℕ) :
    ((s₁ ×ˢ s₂).filter fun p => f₁ p.1 + f₂ p.2 = d).card
      = ∑ q ∈ antidiagonal d, (s₁.filter fun a => f₁ a = q.1).card
          * (s₂.filter fun b => f₂ b = q.2).card := by
  have hmaps : ∀ p ∈ (s₁ ×ˢ s₂).filter (fun p => f₁ p.1 + f₂ p.2 = d),
      (f₁ p.1, f₂ p.2) ∈ antidiagonal d := by
    intro p hp; rw [mem_antidiagonal]; exact (mem_filter.1 hp).2
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_congr rfl fun q hq => ?_
  rw [← card_product]
  congr 1
  ext p
  simp only [mem_filter, mem_product, Prod.ext_iff]
  rw [mem_antidiagonal] at hq
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, -⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩; exact ⟨⟨⟨h1, h2⟩, by rw [h3, h4, hq]⟩, h3, h4⟩

/-- The count of one half for Lemma 6.1(a). -/
lemma half_count {L : ℕ} (ζ : ZStr L) (e : ℕ) :
    ((univ.filter fun τ : Fin L → Tm => ∀ ℓ, chi (τ ℓ) (ζ ℓ) ≠ 0).filter
        (fun τ => ((QZ ζ).filter fun ℓ => τ ℓ ≠ .P0).card = e)).card
      = (QZ ζ).card.choose e * 4 ^ e := by
  rw [← count_nonP0 (QZ ζ) (fun ℓ => forcedTerm (ζ ℓ)) e]
  congr 1
  ext τ
  simp only [mem_filter, mem_univ, true_and, contributes_half_iff]

theorem lemma_6_1_a : Lemma_6_1_a := by
  intro L m w hw1 hw2 d
  set C₁ := univ.filter fun τ : Fin L → Tm => ∀ ℓ, chi (τ ℓ) (w.1 ℓ) ≠ 0
  set C₂ := univ.filter fun τ : Fin L → Tm => ∀ ℓ, chi (τ ℓ) (w.2 ℓ) ≠ 0
  set n₁ : (Fin L → Tm) → ℕ := fun τ => ((QZ w.1).filter fun ℓ => τ ℓ ≠ .P0).card
  set n₂ : (Fin L → Tm) → ℕ := fun τ => ((QZ w.2).filter fun ℓ => τ ℓ ≠ .P0).card
  have e : (univ.filter fun τ : Leaf L => Contributes τ w ∧ order m τ = d)
      = (C₁ ×ˢ C₂).filter fun p => n₁ p.1 + n₂ p.2 = d := by
    ext τ
    simp only [mem_filter, mem_univ, true_and, mem_product, C₁, C₂, Contributes, forall_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, ho⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      have a1 := numP0_of_contrib w.1 τ.1 h1
      have a2 := numP0_of_contrib w.2 τ.2 h2
      simp only [order] at ho
      simp only [n₁, n₂]
      omega
    · rintro ⟨⟨h1, h2⟩, hn⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      have a1 := numP0_of_contrib w.1 τ.1 h1
      have a2 := numP0_of_contrib w.2 τ.2 h2
      simp only [n₁, n₂] at hn
      simp only [order]
      omega
  rw [e, card_filter_add]
  have h1 : ∀ e, (C₁.filter fun a => n₁ a = e).card = m.choose e * 4 ^ e := fun e => by
    rw [← hw1]; exact half_count w.1 e
  have h2 : ∀ e, (C₂.filter fun a => n₂ a = e).card = m.choose e * 4 ^ e := fun e => by
    rw [← hw2]; exact half_count w.2 e
  simp_rw [h1, h2]
  rw [alpha', two_mul, Nat.add_choose_eq, sum_mul]
  refine sum_congr rfl fun q hq => ?_
  rw [mem_antidiagonal] at hq
  rw [← hq, pow_add]
  ring

/-- Strings of `L` terms with exactly `j` symbols `P₀` number `binom(L, j) 4^{L-j}`. -/
lemma count_P0 (L j : ℕ) (hj : j ≤ L) :
    (univ.filter fun τ : Fin L → Tm => numP0 τ = j).card = L.choose j * 4 ^ (L - j) := by
  have h := count_nonP0 (univ : Finset (Fin L)) (fun _ => Tm.P0) (L - j)
  simp only [mem_univ, if_true, card_univ, Fintype.card_fin, Fintype.piFinset_univ] at h
  rw [Nat.choose_symm hj] at h
  rw [← h]
  congr 1
  apply filter_congr
  intro τ _
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin L))) (fun ℓ => τ ℓ = Tm.P0)
  rw [card_univ, Fintype.card_fin] at this
  simp only [numP0, ne_eq]
  omega

theorem lemma_6_1_b_count : Lemma_6_1_b_count := by
  intro L m hmL d
  set e₁ : (Fin L → Tm) → ℕ := fun τ => m - numP0 τ
  set C := univ.filter fun τ : Fin L → Tm => numP0 τ ≤ m
  have e : (univ.filter fun τ : Leaf L => numP0 τ.1 ≤ m ∧ numP0 τ.2 ≤ m ∧ order m τ = d)
      = (C ×ˢ C).filter fun p => e₁ p.1 + e₁ p.2 = d := by
    ext τ
    simp only [mem_filter, mem_univ, true_and, mem_product, C, e₁]
    constructor
    · rintro ⟨h1, h2, h3⟩
      simp only [order] at h3
      exact ⟨⟨h1, h2⟩, by omega⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, ?_⟩
      simp only [order]
      omega
  rw [e, card_filter_add]
  have hfib : ∀ k, (C.filter fun a => e₁ a = k).card = if k ≤ m then beta L m k else 0 := by
    intro k
    by_cases hk : k ≤ m
    · rw [if_pos hk, beta, show L - m + k = L - (m - k) by omega, ← count_P0 L (m - k) (by omega)]
      congr 1
      ext τ
      simp only [C, e₁, mem_filter, mem_univ, true_and]
      omega
    · rw [if_neg hk, card_eq_zero, filter_eq_empty_iff]
      intro τ _ h
      simp only [e₁] at h
      omega
  simp_rw [hfib]
  rw [beta', sum_filter]
  refine sum_congr rfl fun q _ => ?_
  by_cases h1 : q.1 ≤ m <;> by_cases h2 : q.2 ≤ m <;> simp [h1, h2]

/-! ## Lemma 6.1(b), the bound -/

/-- `β_e (L-m+e) = 4 (m-e+1) β_{e-1}`, the ratio of [ZT, eq. (7)] in this setting. -/
lemma beta_succ_mul {L m e : ℕ} (hmL : m ≤ L) (he : e < m) :
    beta L m (e + 1) * (L - m + (e + 1)) = 4 * (m - e) * beta L m e := by
  unfold beta
  have h1 : m - e = (m - (e + 1)) + 1 := by omega
  have h2 : L - m + (e + 1) = L - (m - (e + 1)) := by omega
  have key := Nat.choose_succ_right_eq L (m - (e + 1))
  rw [← h1] at key
  rw [show L - m + (e + 1) = (L - m + e) + 1 by omega, pow_succ]
  calc L.choose (m - (e + 1)) * (4 ^ (L - m + e) * 4) * (L - m + e + 1)
      = 4 * 4 ^ (L - m + e) * (L.choose (m - (e + 1)) * (L - (m - (e + 1)))) := by
        rw [show L - (m - (e + 1)) = L - m + e + 1 by omega]; ring
    _ = 4 * 4 ^ (L - m + e) * (L.choose (m - e) * (m - e)) := by rw [← key]
    _ = 4 * (m - e) * (L.choose (m - e) * 4 ^ (L - m + e)) := by ring

theorem lemma_6_1_b_bound : Lemma_6_1_b_bound := by
  intro L m hm hmL
  have hρ0 : 0 ≤ rho L m := by
    unfold rho
    apply div_nonneg (by positivity)
    have : (m : ℝ) ≤ L := by exact_mod_cast hmL
    linarith
  -- `β_e ≤ ρ^e β₀`
  have hstep : ∀ e : ℕ, e < m → (beta L m (e + 1) : ℝ) ≤ rho L m * beta L m e := by
    intro e he
    have h := beta_succ_mul hmL he
    have hden : (0 : ℝ) < (L : ℝ) - m + (e + 1) := by
      have : (m : ℝ) ≤ L := by exact_mod_cast hmL
      linarith
    have hcast : ((L - m + (e + 1) : ℕ) : ℝ) = (L : ℝ) - m + (e + 1) := by
      push_cast [Nat.cast_sub hmL]; ring
    have h' : (beta L m (e + 1) : ℝ) * ((L : ℝ) - m + (e + 1))
        = 4 * ((m : ℝ) - e) * beta L m e := by
      have := congrArg (fun n : ℕ => (n : ℝ)) h
      simp only [Nat.cast_mul, Nat.cast_ofNat] at this
      rw [hcast, Nat.cast_sub he.le] at this
      exact this
    have hb : (0 : ℝ) ≤ beta L m e := Nat.cast_nonneg _
    rw [rho]
    have hden' : (0 : ℝ) < (L : ℝ) - m + 1 := by
      have : (m : ℝ) ≤ L := by exact_mod_cast hmL
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hden']
    have hr : (beta L m (e + 1) : ℝ) = 4 * ((m : ℝ) - e) * beta L m e / ((L : ℝ) - m + (e + 1)) := by
      rw [← h', mul_div_assoc, div_self hden.ne', mul_one]
    rw [hr, div_mul_eq_mul_div, div_le_iff₀ hden]
    have he' : (e : ℝ) + 1 ≤ m := by exact_mod_cast he
    have hm0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
    nlinarith [mul_nonneg hb hm0]
  have hβ : ∀ e : ℕ, e ≤ m → (beta L m e : ℝ) ≤ rho L m ^ e * beta L m 0 := by
    intro e he
    induction e with
    | zero => simp
    | succ e ih =>
      calc (beta L m (e + 1) : ℝ) ≤ rho L m * beta L m e := hstep e (by omega)
        _ ≤ rho L m * (rho L m ^ e * beta L m 0) :=
            mul_le_mul_of_nonneg_left (ih (by omega)) hρ0
        _ = rho L m ^ (e + 1) * beta L m 0 := by ring
  refine ⟨by simp [beta, K, N0], hβ, ?_, ?_⟩
  · intro d
    rw [beta']
    push_cast
    calc (∑ p ∈ (antidiagonal d).filter (fun p : ℕ × ℕ => p.1 ≤ m ∧ p.2 ≤ m),
          (beta L m p.1 : ℝ) * beta L m p.2)
        ≤ ∑ p ∈ (antidiagonal d).filter (fun p : ℕ × ℕ => p.1 ≤ m ∧ p.2 ≤ m),
            rho L m ^ d * (beta L m 0 : ℝ) ^ 2 := by
          refine sum_le_sum fun p hp => ?_
          obtain ⟨hp1, hp2, hp3⟩ : p.1 + p.2 = d ∧ p.1 ≤ m ∧ p.2 ≤ m := by
            simpa [mem_filter, mem_antidiagonal] using hp
          calc (beta L m p.1 : ℝ) * beta L m p.2
              ≤ (rho L m ^ p.1 * beta L m 0) * (rho L m ^ p.2 * beta L m 0) :=
                mul_le_mul (hβ _ hp2) (hβ _ hp3) (Nat.cast_nonneg _)
                  (mul_nonneg (pow_nonneg hρ0 _) (Nat.cast_nonneg _))
            _ = rho L m ^ d * (beta L m 0 : ℝ) ^ 2 := by rw [← hp1, pow_add]; ring
      _ ≤ ∑ p ∈ antidiagonal d, rho L m ^ d * (beta L m 0 : ℝ) ^ 2 :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      _ = (d + 1) * rho L m ^ d * (beta L m 0 : ℝ) ^ 2 := by
          rw [sum_const, Nat.card_antidiagonal, nsmul_eq_mul]; push_cast; ring
  · intro Kg hKg
    have hmu := (muInf_bounds).1
    have hmu0 : 0 < muInf := by linarith
    have hb0 : (beta L m 0 : ℝ) = (K L m : ℝ) * N0 L m := by simp [beta, K, N0]
    rw [hb0, le_div_iff₀ (by positivity)]
    have hK0 : (0 : ℝ) ≤ K L m := Nat.cast_nonneg _
    have h2 : (muInf ^ 2 * K L m) ^ 2 ≤ Kg ^ 2 := pow_le_pow_left₀ (by positivity) hKg 2
    have hN : (0 : ℝ) ≤ (N0 L m : ℝ) ^ 2 := by positivity
    calc ((K L m : ℝ) * N0 L m) ^ 2 * muInf ^ 4 = (muInf ^ 2 * K L m) ^ 2 * (N0 L m : ℝ) ^ 2 := by
          ring
      _ ≤ Kg ^ 2 * (N0 L m : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h2 hN

/-! ## Lemma 6.1(c) -/

theorem lemma_6_1_c : Lemma_6_1_c := by
  intro L m hmL U hU
  -- every leaf of `Leaves(U)` has an order in `[0, 2m]`
  have hord : ∀ τ ∈ Leaves U, ∃ d ∈ range (2 * m + 1), order m τ = d ∧
      numP0 τ.1 ≤ m ∧ numP0 τ.2 ≤ m := by
    intro τ hτ
    obtain ⟨-, w, hw, hc⟩ := mem_filter.1 hτ
    have h1 := numP0_of_contrib w.1 τ.1 fun ℓ => (hc ℓ).1
    have h2 := numP0_of_contrib w.2 τ.2 fun ℓ => (hc ℓ).2
    rw [(hU w hw).1] at h1
    rw [(hU w hw).2] at h2
    refine ⟨2 * m - (numP0 τ.1 + numP0 τ.2), by rw [mem_range]; omega, ?_, by omega, by omega⟩
    simp only [order]
    omega
  have hmaps : ∀ τ ∈ Leaves U, (order m τ).toNat ∈ range (2 * m + 1) := by
    intro τ hτ
    obtain ⟨d, hd, hod, -⟩ := hord τ hτ
    rw [hod]; simpa using hd
  rw [card_eq_sum_card_fiberwise hmaps]
  refine sum_le_sum fun d hd => le_min ?_ ?_
  · -- at most `|U| α'_d`
    calc ((Leaves U).filter fun τ => (order m τ).toNat = d).card
        ≤ (U.biUnion fun w => univ.filter fun τ : Leaf L => Contributes τ w ∧ order m τ = d).card := by
          apply card_le_card
          intro τ hτ
          rw [mem_filter] at hτ
          obtain ⟨d', -, hod, -⟩ := hord τ hτ.1
          obtain ⟨-, w, hw, hc⟩ := mem_filter.1 hτ.1
          rw [mem_biUnion]
          refine ⟨w, hw, ?_⟩
          rw [mem_filter]
          refine ⟨mem_univ _, hc, ?_⟩
          rw [hod] at hτ ⊢
          simp only [Int.toNat_natCast] at hτ
          rw [hτ.2]
      _ ≤ ∑ w ∈ U, (univ.filter fun τ : Leaf L => Contributes τ w ∧ order m τ = d).card :=
          card_biUnion_le
      _ = ∑ w ∈ U, alpha' m d := sum_congr rfl fun w hw => lemma_6_1_a w (hU w hw).1 (hU w hw).2 d
      _ = U.card * alpha' m d := by rw [sum_const, smul_eq_mul]
  · -- at most `β'_d`
    rw [← lemma_6_1_b_count hmL d]
    apply card_le_card
    intro τ hτ
    rw [mem_filter] at hτ
    obtain ⟨d', -, hod, h1, h2⟩ := hord τ hτ.1
    rw [mem_filter]
    refine ⟨mem_univ _, h1, h2, ?_⟩
    rw [hod] at hτ ⊢
    simp only [Int.toNat_natCast] at hτ
    rw [hτ.2]

end ThinMatrixProducts

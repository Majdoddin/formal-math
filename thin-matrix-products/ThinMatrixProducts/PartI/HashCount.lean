import ThinMatrixProducts.PartI.Hash
import ThinMatrixProducts.Numerics.Mu
import Mathlib.Logic.Equiv.Prod

/-!
# Lemma 4.1, the existence of the re-indexing maps

The proof is the averaging behind the method of conditional expectations of the paper: over all
pairs `(Γ, Δ)`, a fixed set `Q` of `m` levels is good for `c_m 2^{m(L-m)} · c_{L-m} 2^{(L-m)m}`
of the pairs, where `c_k = 2^{k²} μ_k` is the number of linearly independent `k`-tuples in `F₂^k`
(`sec4_mu_probability`); so the average number of good sets is `μ_m μ_{L-m} binom(L, m)`, and some
pair reaches it.
-/

namespace ThinMatrixProducts

open Finset

/-- The matrices whose columns at `S` are linearly independent, as pairs: the independent columns
at `S` and arbitrary columns elsewhere. -/
def indepEquiv {r L : ℕ} (S : Finset (Fin L)) :
    {M : Matrix (Fin r) (Fin L) (ZMod 2) //
        LinearIndependent (ZMod 2) (fun ℓ : S => fun i => M i ℓ)}
      ≃ {f : S → (Fin r → ZMod 2) // LinearIndependent (ZMod 2) f}
          × ({ℓ : Fin L // ℓ ∉ S} → (Fin r → ZMod 2)) where
  toFun M := (⟨fun ℓ i => M.1 i ℓ, M.2⟩, fun ℓ i => M.1 i ℓ)
  invFun p := ⟨fun i ℓ => if h : ℓ ∈ S then p.1.1 ⟨ℓ, h⟩ i else p.2 ⟨ℓ, h⟩ i, by
    have : (fun ℓ : S => fun i => (if h : (ℓ : Fin L) ∈ S then p.1.1 ⟨ℓ, h⟩ i else p.2 ⟨ℓ, h⟩ i))
        = p.1.1 := by
      funext ℓ i; simp [ℓ.2]
    rw [this]; exact p.1.2⟩
  left_inv M := by
    apply Subtype.ext
    funext i ℓ
    by_cases h : ℓ ∈ S <;> simp [h]
  right_inv p := by
    rcases p with ⟨⟨f, hf⟩, g⟩
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    constructor
    · funext ℓ i; simp [ℓ.2]
    · funext ℓ i; simp [ℓ.2]

lemma card_matrix (a b : ℕ) : Fintype.card (Matrix (Fin a) (Fin b) (ZMod 2)) = 2 ^ (a * b) := by
  rw [show Fintype.card (Matrix (Fin a) (Fin b) (ZMod 2)) = Fintype.card (Fin a → Fin b → ZMod 2)
    from Fintype.card_congr (Equiv.refl _)]
  simp [ZMod.card, ← pow_mul, mul_comm]

open scoped Classical in
/-- The number of `r × L` matrices whose columns at a set `S` of `r` levels are linearly
independent: `2^{r²} μ_r · 2^{r(L-r)}`. -/
lemma card_indep_at {r L : ℕ} (S : Finset (Fin L)) (hS : S.card = r) :
    ((univ.filter fun M : Matrix (Fin r) (Fin L) (ZMod 2) =>
        LinearIndependent (ZMod 2) (fun ℓ : S => fun i => M i ℓ)).card : ℝ)
      = 2 ^ (r ^ 2) * mu r * 2 ^ (r * (L - r)) := by
  rw [← Fintype.card_subtype, Fintype.card_congr (indepEquiv S), Fintype.card_prod]
  have e₃ : Fin r ≃ S := (Fintype.equivFinOfCardEq (by simp [hS])).symm
  have hind : Fintype.card {f : S → (Fin r → ZMod 2) // LinearIndependent (ZMod 2) f}
      = Nat.card {s : Fin r → (Fin r → ZMod 2) // LinearIndependent (ZMod 2) s} := by
    rw [Nat.card_eq_fintype_card]
    refine Fintype.card_congr
      { toFun := fun f => ⟨f.1 ∘ e₃, (linearIndependent_equiv e₃).2 f.2⟩
        invFun := fun s => ⟨s.1 ∘ e₃.symm, (linearIndependent_equiv e₃.symm).2 s.2⟩
        left_inv := fun f => by apply Subtype.ext; funext x; simp
        right_inv := fun s => by apply Subtype.ext; funext x; simp }
  have hcompl : Fintype.card {ℓ : Fin L // ℓ ∉ S} = L - r := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hS, Fintype.card_fin]
  rw [hind, Fintype.card_fun, hcompl, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  push_cast
  rw [sec4_mu_probability r, ← pow_mul]

open scoped Classical in
theorem lemma_4_1 : Lemma_4_1 := by
  intro L m hm hmL
  set n := L - m with hn
  set Pairs := (univ : Finset (Matrix (Fin m) (Fin L) (ZMod 2) × Matrix (Fin n) (Fin L) (ZMod 2)))
  set A : ℝ := (2 ^ (m ^ 2) * mu m * 2 ^ (m * (L - m))) * (2 ^ (n ^ 2) * mu n * 2 ^ (n * (L - n)))
  -- the number of pairs `(Γ, Δ)` for which a fixed `Q` of `m` levels is good
  have hpair : ∀ Q ∈ univ.powersetCard m,
      ((Pairs.filter fun p => Good p.1 p.2 Q).card : ℝ) = A := by
    intro Q hQ
    have hQc : Q.card = m := (mem_powersetCard.1 hQ).2
    have hQc' : Qᶜ.card = n := by rw [card_compl, Fintype.card_fin, hQc]
    have e : (Pairs.filter fun p => Good p.1 p.2 Q)
        = (univ.filter fun Γ : Matrix (Fin m) (Fin L) (ZMod 2) =>
            LinearIndependent (ZMod 2) (fun ℓ : Q => fun i => Γ i ℓ)) ×ˢ
          (univ.filter fun Δ : Matrix (Fin n) (Fin L) (ZMod 2) =>
            LinearIndependent (ZMod 2) (fun ℓ : (Qᶜ : Finset (Fin L)) => fun i => Δ i ℓ)) := by
      ext p
      simp only [Pairs, mem_filter, mem_univ, true_and, mem_product, Good, hQc]
      exact Iff.rfl
    rw [e, card_product]
    push_cast
    rw [card_indep_at Q hQc, card_indep_at Qᶜ hQc']
  -- the sum over all pairs of the number of good sets
  have hsum : (∑ p ∈ Pairs, (((univ.powersetCard m).filter (Good p.1 p.2)).card : ℝ))
      = (L.choose m : ℝ) * A := by
    have : (∑ p ∈ Pairs, (((univ.powersetCard m).filter (Good p.1 p.2)).card : ℝ))
        = ∑ Q ∈ univ.powersetCard m, ((Pairs.filter fun p => Good p.1 p.2 Q).card : ℝ) := by
      simp only [card_filter]
      push_cast
      rw [Finset.sum_comm]
    rw [this, Finset.sum_congr rfl hpair, sum_const, card_powersetCard, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hPairs : (Pairs.card : ℝ) = 2 ^ (m * L) * 2 ^ (n * L) := by
    rw [card_univ, Fintype.card_prod, card_matrix, card_matrix]
    push_cast; ring
  -- the average is `μ_m μ_{L-m} binom(L, m)`
  have havg : (∑ _p ∈ Pairs, mu m * mu n * (L.choose m : ℝ))
      = ∑ p ∈ Pairs, (((univ.powersetCard m).filter (Good p.1 p.2)).card : ℝ) := by
    rw [hsum, sum_const, nsmul_eq_mul, hPairs]
    have hL : L = m + n := by omega
    simp only [A]
    rw [show L - n = m by omega, hL, Nat.add_sub_cancel_left]
    ring_nf
  obtain ⟨p, -, hp⟩ := Finset.exists_le_of_sum_le univ_nonempty havg.le
  refine ⟨p.1, p.2, hp, ?_⟩
  have h1 := muInf_le m
  have h2 := muInf_le n
  have h0 : 0 ≤ muInf := le_trans (by norm_num) (muInf_bounds).1.le
  have hc : (0 : ℝ) ≤ L.choose m := Nat.cast_nonneg _
  have : muInf ^ 2 ≤ mu m * mu n := by
    rw [sq]; exact mul_le_mul h1 h2 h0 (le_trans h0 h1)
  exact mul_le_mul_of_nonneg_right this hc

end ThinMatrixProducts

import ThinMatrixProducts.Appendix.FullProductLemma1
import ThinMatrixProducts.Appendix.FullProductTheorem2
/-! # Full products: Theorem 2 composed with Lemma 1, and the thin rotations of the 145

`fp_Theorem_2` applies the inequality `fp_Theorem_2_ineq` to the output-support sizes of the terms
with `w_l ≠ 0`: there are at least `n` of them (`fp_rank_ge_n`), each has `|S_l| ≥ 1`, and the
capped covering of Lemma 1 (`fp_Lemma_1`) loses nothing when the terms with `w_l = 0` (empty
support) are dropped. `fp_145_thin` reads Theorem 2's condition off the list `fpShapes145`. -/
namespace ThinMatrixProducts

open Finset

section FullProductCompose

theorem fp_Theorem_2 : FP_Theorem_2 := by
  classical
  intro K _ o₁ b o₂ R u v w hd hb hcond t ht0 ht1
  set G : Finset (Fin R) := univ.filter (fun l => w l ≠ 0) with hG
  -- the sizes `|S_l|` of the terms of `G`, reindexed by `Fin |G|`
  set e : G ≃ Fin G.card := G.equivFin
  set S' : Fin G.card → ℕ := fun i => (outSupp (w (e.symm i))).card
  have hreindex : ∀ f : Fin R → ℝ, ∑ i, f (e.symm i : Fin R) = ∑ l ∈ G, f l := by
    intro f
    rw [← Finset.sum_coe_sort G f]
    exact Equiv.sum_comp e.symm (fun l : G => f l)
  by_cases hk : min o₁ o₂ = 0
  · have hn : o₁ * o₂ = 0 := by
      rcases Nat.min_eq_zero_iff.1 hk with h | h <;> simp [h]
    rw [hn, Nat.cast_zero, zero_mul]
    exact Finset.sum_nonneg fun l _ => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hS : ∀ i, 1 ≤ S' i := by
    intro i
    have hi := (e.symm i).2
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨z, hz⟩ := Function.ne_iff.1 hi
    exact Finset.card_pos.2 ⟨z, by simpa [outSupp] using hz⟩
  have hn : o₁ * o₂ ≤ G.card := fp_rank_ge_n K o₁ b o₂ R u v w hd hb
  have hsum : b * (o₁ * o₂) ≤ ∑ i, min (S' i) (min o₁ o₂) := by
    refine (fp_Lemma_1 K o₁ b o₂ R u v w hd).trans (le_of_eq ?_)
    have h1 : ∑ l, min (outSupp (w l)).card (min o₁ o₂)
        = ∑ l ∈ G, min (outSupp (w l)).card (min o₁ o₂) := by
      refine (Finset.sum_subset (Finset.subset_univ G) fun l _ hl => ?_).symm
      simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hl
      simp [outSupp, hl]
    have h2 : ∑ i, min (S' i) (min o₁ o₂)
        = ∑ l ∈ G, min (outSupp (w l)).card (min o₁ o₂) := by
      rw [← Finset.sum_coe_sort G]
      exact Equiv.sum_comp e.symm (fun l : G => min (outSupp (w l)).card (min o₁ o₂))
    rw [h1, h2]
  have := fp_Theorem_2_ineq b (min o₁ o₂) (o₁ * o₂) G.card S' hb (Nat.one_le_iff_ne_zero.2 hk)
    hcond hS hn hsum t ht0 ht1
  calc ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2) ≤ ∑ i, ((S' i : ℕ) : ℝ) ^ t := this
    _ = _ := hreindex (fun l => ((outSupp (w l)).card : ℝ) ^ t)

theorem fp_145_thin : FP_145_thin := by
  intro K _ o₁ b o₂ R hmem u v w hd t ht0 ht1
  obtain ⟨-, -, hall⟩ := fp_shapes_145
  refine fp_Theorem_2 K o₁ b o₂ R u v w hd ?_ ?_ t ht0 ht1
  · rcases hmem with h | h
    · exact le_trans (by norm_num) (hall _ h).2.1
    · exact le_trans (by norm_num) (hall _ h).2.1
  · right
    rcases hmem with h | h
    · obtain ⟨h1, -, -, h4⟩ := hall _ h
      rw [min_eq_left h1]
      exact h4
    · obtain ⟨h1, -, -, h4⟩ := hall _ h
      rw [min_eq_right h1]
      exact h4

end FullProductCompose

end ThinMatrixProducts

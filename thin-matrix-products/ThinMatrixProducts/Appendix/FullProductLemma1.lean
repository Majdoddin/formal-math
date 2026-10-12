import Statements
/-! # Full products: Lemma 1 (capped covering)

The rank steps are two generic facts about matrices: a matrix that is a sum of `|G|` rank-one
matrices has rank at most `|G|` (`rank_le_of_sum`), and a matrix containing an identity
submatrix on all its rows has full row rank (`card_le_rank_of_select`). Lemma 1 uses the rows
`W_r = {(r, c) : c}` of the output array as the transversals: each meets every column once, and an
output support `S_l` meets at most `|S_l|` of them (at most the number of first coordinates of
`S_l`) and at most `o₁`. The case `o₂ < o₁` follows by transposing the decomposition. -/
namespace ThinMatrixProducts

open Finset

section FullProductLemma1

variable {K : Type} [Field K]

/-- A matrix that is a sum of `|G|` rank-one matrices `f l ⊗ g l` has rank at most `|G|`. -/
lemma rank_le_of_sum {m n ι : Type} [Fintype m] [Fintype n] (M : Matrix m n K) (G : Finset ι)
    (f : ι → m → K) (g : ι → n → K) (h : ∀ i j, M i j = ∑ l ∈ G, f l i * g l j) :
    M.rank ≤ G.card := by
  have hM : M = (Matrix.of fun i (l : G) => f l i) * (Matrix.of fun (l : G) j => g l j) := by
    ext i j
    rw [h, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    exact (Finset.sum_coe_sort G (fun l => f l i * g l j)).symm
  rw [hM]
  calc _ ≤ (Matrix.of fun i (l : G) => f l i).rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card G := Matrix.rank_le_card_width _
    _ = G.card := Fintype.card_coe G

/-- A matrix with an identity submatrix on all its rows (columns selected by `s`) has rank at
least the number of rows. -/
lemma card_le_rank_of_select {m n : Type} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (M : Matrix m n K) (s : m → n)
    (hs : ∀ i i', M i (s i') = if i = i' then 1 else 0) : Fintype.card m ≤ M.rank := by
  have h1 : M * (Matrix.of fun j i' => if j = s i' then (1 : K) else 0) = 1 := by
    ext i i'
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, hs, Matrix.one_apply]
  calc Fintype.card m = (1 : Matrix m m K).rank := (Matrix.rank_one).symm
    _ = _ := by rw [← h1]
    _ ≤ M.rank := Matrix.rank_mul_le_left _ _

open scoped Classical in
theorem fp_restrict_rank : FP_restrict_rank := by
  intro K _ o₁ b o₂ R u v w hd P
  apply rank_le_of_sum _ _ (fun l y => v l y) (fun l q => u l q.1 * w l q.2)
  intro y q
  simp only [yFlat]
  rw [← hd, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs with hl
  · ring
  · have h0 : w l q.2 = 0 := by
      by_contra h0
      exact hl ⟨q.2, q.2.2, h0⟩
    rw [h0]
    ring

theorem fp_transversal_rank : FP_transversal_rank := by
  classical
  intro K _ o₁ b o₂ P hP
  choose i hi _ using hP
  refine le_antisymm ?_ ?_
  · calc _ ≤ Fintype.card (Fin b × Fin o₂) := Matrix.rank_le_card_height _
      _ = b * o₂ := by simp
  · have := card_le_rank_of_select (yFlat K o₁ b o₂ P)
      (fun y => ((i y.2, y.1), ⟨(i y.2, y.2), hi y.2⟩)) ?_
    · simpa using this
    · rintro ⟨j, c⟩ ⟨j', c'⟩
      simp only [yFlat, mmTensor, Prod.mk.injEq, true_and]
      by_cases hc : c' = c
      · subst hc
        by_cases hj : j' = j
        · simp [hj]
        · simp [hj, Ne.symm hj]
      · simp [Ne.symm hc]

open scoped Classical in
/-- Lemma 1 with the cap `o₁` in place of `min o₁ o₂`, for every shape. -/
lemma lemma1_cap_o₁ (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K)
    (hd : IsMMDecomp u v w) : b * (o₁ * o₂) ≤ ∑ l, min (outSupp (w l)).card o₁ := by
  -- the row `W r = {(r, c) : c}` is a transversal
  set W : Fin o₁ → Finset (Fin o₁ × Fin o₂) := fun r => univ.filter fun z => z.1 = r
  have hrow : ∀ r, b * o₂ ≤ (univ.filter fun l => ∃ z ∈ W r, w l z ≠ 0).card := by
    intro r
    rw [← fp_transversal_rank K o₁ b o₂ (W r) ?_]
    · exact fp_restrict_rank K o₁ b o₂ R u v w hd (W r)
    · intro c
      exact ⟨r, by simp [W], fun i hi => by simpa [W] using hi⟩
  calc b * (o₁ * o₂) = ∑ _r : Fin o₁, b * o₂ := by simp; ring
    _ ≤ ∑ r, (univ.filter fun l => ∃ z ∈ W r, w l z ≠ 0).card := Finset.sum_le_sum fun r _ => hrow r
    _ = ∑ l, (univ.filter fun r => ∃ z ∈ W r, w l z ≠ 0).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ l, min (outSupp (w l)).card o₁ := by
        refine Finset.sum_le_sum fun l _ => le_min ?_ ?_
        · refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := Prod.fst))
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, W] at hr
          obtain ⟨z, hz, hw⟩ := hr
          exact Finset.mem_image.2 ⟨z, by simp [outSupp, hw], hz⟩
        · exact le_trans (Finset.card_le_univ _) (by simp)

theorem fp_Lemma_1 : FP_Lemma_1 := by
  intro K _ o₁ b o₂ R u v w hd
  rcases le_total o₁ o₂ with h | h
  · rw [min_eq_left h]
    exact lemma1_cap_o₁ o₁ b o₂ R u v w hd
  · -- transpose: a decomposition of `⟨o₂, b, o₁⟩`
    have hd' : IsMMDecomp (fun l (a : Fin o₂ × Fin b) => v l (a.2, a.1))
        (fun l (y : Fin b × Fin o₁) => u l (y.2, y.1))
        (fun l (z : Fin o₂ × Fin o₁) => w l (z.2, z.1)) := by
      intro a y z
      have := hd (y.2, y.1) (a.2, a.1) (z.2, z.1)
      simp only [mmTensor] at this ⊢
      rw [show (∑ l, v l (a.2, a.1) * u l (y.2, y.1) * w l (z.2, z.1))
          = ∑ l, u l (y.2, y.1) * v l (a.2, a.1) * w l (z.2, z.1) from
          Finset.sum_congr rfl fun l _ => by ring, this]
      split_ifs with hA hB hB
      · rfl
      · exact absurd ⟨hA.2.2, hA.2.1.symm, hA.1⟩ hB
      · exact absurd ⟨hB.2.2, hB.2.1.symm, hB.1⟩ hA
      · rfl
    have key := lemma1_cap_o₁ o₂ b o₁ R _ _ _ hd'
    rw [min_eq_right h, mul_comm o₁ o₂]
    convert key using 3 with l
    classical
    refine Finset.card_bij (fun z _ => (z.2, z.1)) ?_ ?_ ?_
    · intro z hz; simpa [outSupp] using hz
    · intro z _ z' _ hzz; simp only [Prod.mk.injEq] at hzz; exact Prod.ext hzz.2 hzz.1
    · intro z hz; exact ⟨(z.2, z.1), by simpa [outSupp] using hz, rfl⟩

open scoped Classical in
theorem fp_rank_ge_n : FP_rank_ge_n := by
  intro K _ o₁ b o₂ R u v w hd hb
  -- the `z`-flattening
  set M : Matrix (Fin o₁ × Fin o₂) ((Fin o₁ × Fin b) × (Fin b × Fin o₂)) K :=
    fun z q => mmTensor K o₁ b o₂ q.1 q.2 z
  have hup : M.rank ≤ (univ.filter fun l => w l ≠ 0).card := by
    apply rank_le_of_sum M _ (fun l z => w l z) (fun l q => u l q.1 * v l q.2)
    intro z q
    simp only [M]
    rw [← hd, Finset.sum_filter]
    refine Finset.sum_congr rfl fun l _ => ?_
    split_ifs with hl
    · ring
    · rw [not_not.1 hl]; simp
  have hlow := card_le_rank_of_select M
    (fun z => ((z.1, ⟨0, hb⟩), ((⟨0, hb⟩ : Fin b), z.2))) (by
      rintro ⟨i, c⟩ ⟨i', c'⟩
      simp only [M, mmTensor, Prod.mk.injEq, true_and]
      by_cases h1 : i' = i
      · by_cases h2 : c' = c
        · simp [h1, h2]
        · simp [h1, h2, Ne.symm h2]
      · simp [h1, Ne.symm h1])
  simp only [Fintype.card_prod, Fintype.card_fin] at hlow
  exact hlow.trans hup

end FullProductLemma1

end ThinMatrixProducts

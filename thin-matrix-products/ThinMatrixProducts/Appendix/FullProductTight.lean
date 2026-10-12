import Statements
/-! # Thin full products: Lemma 3 (tight outputs)

For an output `e = (i, c)` with exactly `b` coverers `C`, the `(i, ·) × (·, c)` block of the slice
`B_e = ∑_{l ∈ C} w_l(e) u_l v_lᵀ` is the identity: `P Q = 1` for the `b × C` matrix
`P j l = u_l(i, j) w_l(e)` and the `C × b` matrix `Q l j = v_l(j, c)`. Since `|C| = b`, also
`Q P = 1`. A row `a` of `B_e` outside row `i` is zero, so the vector `(u_l(a) w_l(e))_l` is killed
by `Q`, hence zero; likewise for a column `y` outside column `c` and `P`. The diagonal of `Q P = 1`
shows `u_l ≠ 0` and `v_l ≠ 0`. -/
namespace ThinMatrixProducts

open Finset

section FullProductTight

variable {K : Type} [Field K]

/-- A decomposition summed over the coverers of `e` only. -/
lemma fp_sum_cov {o₁ b o₂ R : ℕ} {u : Fin R → Fin o₁ × Fin b → K}
    {v : Fin R → Fin b × Fin o₂ → K} {w : Fin R → Fin o₁ × Fin o₂ → K}
    (hd : IsMMDecomp u v w) (e : Fin o₁ × Fin o₂) (a : Fin o₁ × Fin b) (y : Fin b × Fin o₂) :
    ∑ l : fpCov w e, u l a * v l y * w l e = mmTensor K o₁ b o₂ a y e := by
  classical
  rw [← hd a y e, Finset.sum_coe_sort (fpCov w e) (fun l => u l a * v l y * w l e)]
  unfold fpCov
  refine Finset.sum_filter_of_ne fun l _ h => ?_
  intro hw
  exact h (by rw [hw, mul_zero])

theorem fp_Lemma_3 : FP_Lemma_3 := by
  classical
  intro K _ o₁ b o₂ R u v w hd e hcard
  set C := fpCov w e
  let P : Matrix (Fin b) C K := fun j l => u l (e.1, j) * w l e
  let Q : Matrix C (Fin b) K := fun l j => v l (j, e.2)
  have hPQ : P * Q = 1 := by
    ext j j'
    rw [Matrix.mul_apply, Matrix.one_apply]
    have := fp_sum_cov hd e (e.1, j) (j', e.2)
    simp only [mmTensor, true_and] at this
    rw [show (if j = j' ∧ True then (1 : K) else 0) = if j = j' then 1 else 0 by simp] at this
    rw [← this]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [P, Q]; ring
  have hC : Fintype.card C = b := by rw [Fintype.card_coe]; exact hcard
  have hQP : Q * P = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivFinOfCardEq hC).symm).1 hPQ
  intro l hl
  set l' : C := ⟨l, hl⟩
  have hwl : w l e ≠ 0 := by simpa [C, fpCov] using hl
  have hdiag : ∑ j, Q l' j * P j l' = 1 := by
    have := congrFun (congrFun hQP l') l'
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hu
    rw [Finset.sum_eq_zero fun j _ => by simp [P, l', hu]] at hdiag
    exact zero_ne_one hdiag
  · intro hv
    rw [Finset.sum_eq_zero fun j _ => by simp [Q, l', hv]] at hdiag
    exact zero_ne_one hdiag
  · intro a ha
    let x : C → K := fun m => u m a * w m e
    have hxQ : Matrix.vecMul x Q = 0 := by
      ext j'
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, x, Q]
      rw [← show ∑ m : C, u m a * v m (j', e.2) * w m e = 0 by
        rw [fp_sum_cov hd e a (j', e.2)]; simp [mmTensor, ha]]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hx : x = 0 := by
      rw [← Matrix.vecMul_one x, ← hQP, ← Matrix.vecMul_vecMul, hxQ, Matrix.zero_vecMul]
    have := congrFun hx l'
    simp only [x, Pi.zero_apply, l'] at this
    exact (mul_eq_zero.1 this).resolve_right hwl
  · intro y hy
    let x : C → K := fun m => v m y
    have hPx : Matrix.mulVec P x = 0 := by
      ext j
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, x, P]
      rw [← show ∑ m : C, u m (e.1, j) * v m y * w m e = 0 by
        rw [fp_sum_cov hd e (e.1, j) y]; simp [mmTensor, hy]]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hx : x = 0 := by
      rw [← Matrix.one_mulVec x, ← hQP, ← Matrix.mulVec_mulVec, hPx, Matrix.mulVec_zero]
    exact congrFun hx l'

theorem fp_local_unique : FP_local_unique := by
  intro K _ o₁ b o₂ u v e e' h h'
  obtain ⟨hu, hv, hA, hY⟩ := h
  obtain ⟨-, -, hA', hY'⟩ := h'
  obtain ⟨a, ha⟩ := Function.ne_iff.1 hu
  obtain ⟨y, hy⟩ := Function.ne_iff.1 hv
  have h1 : a.1 = e.1 := by by_contra hc; exact ha (hA a hc)
  have h1' : a.1 = e'.1 := by by_contra hc; exact ha (hA' a hc)
  have h2 : y.2 = e.2 := by by_contra hc; exact hy (hY y hc)
  have h2' : y.2 = e'.2 := by by_contra hc; exact hy (hY' y hc)
  exact Prod.ext (h1.symm.trans h1') (h2.symm.trans h2')

theorem fp_Lemma_3_count : FP_Lemma_3_count := by
  classical
  intro K _ o₁ b o₂ R u v w hd
  set T := univ.filter fun e : Fin o₁ × Fin o₂ => (fpCov w e).card = b
  have hdisj : (T : Set (Fin o₁ × Fin o₂)).PairwiseDisjoint (fun e => fpCov w e) := by
    intro e he e' he' hne
    refine Finset.disjoint_left.2 fun l hl hl' => hne ?_
    have he1 : (fpCov w e).card = b := by simpa [T] using he
    have he1' : (fpCov w e').card = b := by simpa [T] using he'
    exact fp_local_unique K o₁ b o₂ (u l) (v l) e e' (fp_Lemma_3 K o₁ b o₂ R u v w hd e he1 l hl)
      (fp_Lemma_3 K o₁ b o₂ R u v w hd e' he1' l hl')
  calc b * T.card = ∑ e ∈ T, (fpCov w e).card := by
        rw [Finset.sum_congr rfl fun e he => (by simpa [T] using he : (fpCov w e).card = b)]
        simp [mul_comm]
    _ = (T.biUnion fun e => fpCov w e).card := (Finset.card_biUnion hdisj).symm
    _ ≤ _ := by
        refine Finset.card_le_card fun l hl => ?_
        obtain ⟨e, -, hl⟩ := Finset.mem_biUnion.1 hl
        simp only [fpCov, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
        exact fun h => hl (by rw [h]; rfl)

theorem fp_Lemma_3_all_tight : FP_Lemma_3_all_tight := by
  classical
  intro K _ o₁ b o₂ R u v w hd hall l
  refine Finset.card_le_one.2 fun z hz z' hz' => ?_
  have hz1 : l ∈ fpCov w z := by simpa [fpCov, outSupp] using hz
  have hz2 : l ∈ fpCov w z' := by simpa [fpCov, outSupp] using hz'
  exact fp_local_unique K o₁ b o₂ (u l) (v l) z z'
    (fp_Lemma_3 K o₁ b o₂ R u v w hd z (hall z) l hz1)
    (fp_Lemma_3 K o₁ b o₂ R u v w hd z' (hall z') l hz2)

end FullProductTight

end ThinMatrixProducts

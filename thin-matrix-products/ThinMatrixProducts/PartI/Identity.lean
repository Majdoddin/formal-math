import Statements
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring

/-!
# Lemma 3.1: the identity in the preprint's notation; Coppersmith's construction; Remark 5.2

The sums over the alphabets are written out through equivalences with `Fin 2 ⊕ Fin 2` and the like,
the coefficients of the forms are evaluated, and `ring` checks the polynomial identities. The
coefficient table `γ` and the weights of Remark 5.2 are finite checks (`decide`).
-/

namespace ThinMatrixProducts

open Finset MvPolynomial

/-- `XL ≃ Fin 2 ⊕ Fin 2`: `x i ↦ inl i`, `p k ↦ inr k`. -/
def XL.equiv : XL ≃ Fin 2 ⊕ Fin 2 where
  toFun | .x i => .inl i | .p k => .inr k
  invFun | .inl i => .x i | .inr k => .p k
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with _ | _ <;> rfl

/-- `YL ≃ Fin 2 ⊕ Unit`. -/
def YL.equiv : YL ≃ Fin 2 ⊕ Unit where
  toFun | .y j => .inl j | .q => .inr ()
  invFun | .inl j => .y j | .inr _ => .q
  left_inv t := by cases t <;> rfl
  right_inv t := by rcases t with _ | _ <;> rfl

/-- `ZL ≃ Fin 2 × Fin 2 ⊕ Unit`. -/
def ZL.equiv : ZL ≃ (Fin 2 × Fin 2) ⊕ Unit where
  toFun | .z i j => .inl (i, j) | .z0 => .inr ()
  invFun | .inl (i, j) => .z i j | .inr _ => .z0
  left_inv z := by cases z <;> rfl
  right_inv z := by rcases z with ⟨_, _⟩ | _ <;> rfl

/-- `Tm ≃ Fin 2 × Fin 2 ⊕ Unit`. -/
def Tm.equiv : Tm ≃ (Fin 2 × Fin 2) ⊕ Unit where
  toFun | .P i j => .inl (i, j) | .P0 => .inr ()
  invFun | .inl (i, j) => .P i j | .inr _ => .P0
  left_inv z := by cases z <;> rfl
  right_inv z := by rcases z with ⟨_, _⟩ | _ <;> rfl

lemma sum_XL {M : Type*} [AddCommMonoid M] (f : XL → M) :
    ∑ s, f s = f (.x 0) + f (.x 1) + (f (.p 0) + f (.p 1)) := by
  rw [← XL.equiv.symm.sum_comp, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]; rfl

lemma sum_YL {M : Type*} [AddCommMonoid M] (f : YL → M) :
    ∑ t, f t = f (.y 0) + f (.y 1) + f .q := by
  rw [← YL.equiv.symm.sum_comp, Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_unique]; rfl

lemma sum_ZL {M : Type*} [AddCommMonoid M] (f : ZL → M) :
    ∑ z, f z = f (.z 0 0) + f (.z 0 1) + (f (.z 1 0) + f (.z 1 1)) + f .z0 := by
  rw [← ZL.equiv.symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two, Fintype.sum_unique]; rfl

lemma sum_Tm {M : Type*} [AddCommMonoid M] (f : Tm → M) :
    ∑ lam, f lam = f (.P 0 0) + f (.P 0 1) + (f (.P 1 0) + f (.P 1 1)) + f .P0 := by
  rw [← Tm.equiv.symm.sum_comp, Fintype.sum_sum_type, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_two, Fin.sum_univ_two, Fintype.sum_unique]; rfl

theorem lemma_3_1 : Lemma_3_1 := by
  constructor
  · simp only [sum_Tm, formX, formY, formZ, sum_XL, sum_YL, sum_ZL, G, E, Fin.sum_univ_two,
      phi, psi, chi, pHat, qHat]
    simp
    ring
  · simp only [E, Eexplicit, formX, formY, sum_XL, sum_YL, Fin.sum_univ_two, pHat, qHat]
    simp
    ring

theorem sec3_gamma_coeff : Sec3_gamma_coeff := by
  constructor
  · simp only [G, E, formX, formY, sum_XL, sum_YL, sum_ZL, Fin.sum_univ_two, pHat, qHat, gEcoef]
    simp
    ring
  · decide

theorem sec3_coppersmith : Sec3_coppersmith := by
  intro R _ a11 a12 a13 a22 a23 b11 b12 b21 b31 c11 c12 c21 x
  ring

theorem remark_5_2_weights : Remark_5_2_weights := by
  unfold Remark_5_2_weights; decide

theorem sec3_coppersmith_terms : Sec3_coppersmith_terms := by
  intro R _ a11 a12 a13 a22 a23 b11 b12 b21 b31 c11 c12 c21
  simp only [sum_XL, sum_YL, sum_ZL]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [phi, psi, chi, pHat, qHat] <;> ring

end ThinMatrixProducts

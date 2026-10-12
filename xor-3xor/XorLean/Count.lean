import XorLean.Basic

/-!
# T4 of the 3-XOR note: Lemma 7 (`lem:count`)
-/

namespace Xor

private lemma zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem sum_chi_eq {q : ℕ} (z : Vec q) :
    ∑ y : Vec q, chi y z = if z = 0 then 2 ^ q else 0 := by
  split_ifs with hz
  · subst hz
    simp [chi, ZMod.card]
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    have hzi : z i = 1 := (zmod2_cases _).resolve_left hi
    refine Finset.sum_involution (fun u _ => u + Pi.single i 1) ?_ ?_ (by simp) ?_
    · intro u _
      have hd : (u + Pi.single i 1) ⬝ᵥ z = u ⬝ᵥ z + 1 := by
        rw [add_dotProduct, single_dotProduct, hzi, one_mul]
      unfold chi
      rw [hd]
      generalize u ⬝ᵥ z = a
      rcases zmod2_cases a with rfl | rfl
      · simp
      · rw [(by decide : (1 : ZMod 2) + 1 = 0)]; norm_num
    · intro u _ _ h
      have : (Pi.single i (1 : ZMod 2) : Vec q) = 0 := by
        simpa using congrArg (· - u) h
      have := congrFun this i
      simp at this
    · intro u _
      rw [add_assoc]
      have : (Pi.single i (1 : ZMod 2) : Vec q) + Pi.single i 1 = 0 := by
        rw [← Pi.single_add]
        simp [(by decide : (1 : ZMod 2) + 1 = 0)]
      rw [this, add_zero]

theorem chi_add {q : ℕ} (y z z' : Vec q) : chi y (z + z') = chi y z * chi y z' := by
  unfold chi
  rw [dotProduct_add]
  generalize y ⬝ᵥ z = a
  generalize y ⬝ᵥ z' = b
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;> decide

theorem count_formula {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] {d q : ℕ}
    (I : TriInst A B C d) (G : Vec d →ₗ[ZMod 2] Vec q) :
    (2 : ℤ) ^ q * I.Z G =
      ∑ y : Vec q, ∑ a : A, ∑ b : B, chi y (G (I.wab a b)) *
        ((Matrix.of fun a c => chi y (G (I.wac a c))) *
         (Matrix.of fun c b => chi y (G (I.wbc b c)))) a b := by
  have h1 : (2 : ℤ) ^ q * I.Z G = ∑ t : A × B × C, ∑ y : Vec q, chi y (G (I.S t.1 t.2.1 t.2.2)) := by
    unfold TriInst.Z
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [sum_chi_eq]
    split_ifs <;> simp
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [TriInst.S, map_add, chi_add, Matrix.of_apply]
  ring

end Xor

import ThinMatrixProducts.Appendix.Border
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Appendix A.5: the fixed lines and the quotients of Propositions A.4 and A.5

* The group fixes the tensor (`prop_A_4_fixes`, part of `prop_A_5_linalg`): the tensor is a weighted
  sum of basis terms (`tAct_terms`), and each family of terms is invariant because
  `∑_i U[i', i] U⁻¹[i, i''] = δ`.
* The fixed lines (`prop_A_4_lines`): a torus element with distinct diagonal entries forces a fixed
  line to be a coordinate line (`coord_of_torus`); the unipotent element `I + E_{0i}` moves the
  coordinate lines `⟨x_i⟩`, `i ≥ 2` (and `⟨p_s⟩`, `s ≥ 2`).
* The quotients: `quot0` by a coordinate vector zeroes that slice, and the result is the smaller
  tensor padded by zero slices (`tExtend_apply`, `tExtend_zero`).
* The composition: Lemma A.3 gives a fixed line `⟨a⟩` with `R(T/a) + 1 ≤ R(T)`, the line is one of
  the coordinate lines, and the quotient has the border rank of the smaller tensor; so the
  substitution step of `Prop_A_4` and `Prop_A_5` holds, and the propositions follow.
-/

namespace ThinMatrixProducts

open Finset Matrix

variable {K : Type} [Field K]

/-! ## The action on the two tensors -/

/-- `g · G = ∑_{i,j} (g_A x_i)(g_B y_j)(g_C z_ij) + ∑_s (g_A p_s)(g_B q_s)(g_C z₀)`. -/
lemma tAct_gTensor {k n q : ℕ} (gA : Matrix (Fin k ⊕ Fin q) (Fin k ⊕ Fin q) K)
    (gB : Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) K)
    (gC : Matrix (Option (Fin k × Fin n)) (Option (Fin k × Fin n)) K) a' b' c' :
    tAct gA gB gC (gTensor k n q) a' b' c'
      = (∑ i, ∑ j, gA a' (.inl i) * gB b' (.inl j) * gC c' (some (i, j)))
        + ∑ s, gA a' (.inr s) * gB b' (.inr s) * gC c' none := by
  simp only [tAct, Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, gTensor,
    mul_zero, Finset.sum_const_zero, add_zero, zero_add, Prod.mk.injEq, mul_ite, mul_one]
  congr 1
  · refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [hj]
    · simp
    · intro i' _ hi; exact sum_eq_zero fun j' _ => by simp [hi]
    · simp
  · refine sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ ht; simp [Ne.symm ht]
    · simp

/-- `g · S = ∑_{i,j} (g_A x_i)(g_B y_j)(g_C z_ij) + ∑_s (g_A p_s)(g_B q_s)(g_C z₀)
+ (g_A c)(g_B y₁)(g_C z₀)`. -/
lemma tAct_sTensor {k n q : ℕ} (gA : Matrix (Fin k ⊕ (Fin q ⊕ Unit)) (Fin k ⊕ (Fin q ⊕ Unit)) K)
    (gB : Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) K)
    (gC : Matrix (Option (Fin k × Fin n)) (Option (Fin k × Fin n)) K) a' b' c' :
    tAct gA gB gC (sTensor k n q) a' b' c'
      = (∑ i, ∑ j, gA a' (.inl i) * gB b' (.inl j) * gC c' (some (i, j)))
        + ∑ s, gA a' (.inr (.inl s)) * gB b' (.inr s) * gC c' none
        + ∑ j : Fin n, if (j : ℕ) = 0 then gA a' (.inr (.inr ())) * gB b' (.inl j) * gC c' none
          else 0 := by
  simp only [tAct, Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_prod_type, sTensor,
    Fintype.sum_unique, mul_zero, Finset.sum_const_zero, add_zero, zero_add, Prod.mk.injEq,
    mul_ite, mul_one]
  rw [add_assoc]
  congr 1
  · refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [hj]
    · simp
    · intro i' _ hi; exact sum_eq_zero fun j' _ => by simp [hi]
    · simp
  · congr 1
    refine sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ ht; simp [Ne.symm ht]
    · simp

/-- `∑_i U[i', i] U⁻¹[i, i''] = δ_{i'i''}`. -/
lemma sum_mul_inv {m : ℕ} (U : Matrix (Fin m) (Fin m) K) (hU : IsUnit U.det) (i' i'' : Fin m) :
    ∑ i, U i' i * U⁻¹ i i'' = if i' = i'' then 1 else 0 := by
  rw [← Matrix.mul_apply, Matrix.mul_nonsing_inv U hU, Matrix.one_apply]

/-! ## The groups fix the tensors -/

/-- The `x y z` part: `∑_{i,j} U[i', i] δ_{j'j} (v-scaled) U⁻¹[i, i''] δ_{j''j} … = δ δ`. -/
lemma xyz_part {k n : ℕ} (U : Matrix (Fin k) (Fin k) K) (hU : IsUnit U.det) (D : Fin n → K)
    (v : K) (hD : ∀ j : Fin n, D j * (if (j : ℕ) = 0 then v else 1) = 1)
    (i' i'' : Fin k) (j' j'' : Fin n) :
    (∑ i, ∑ j, U i' i * Matrix.diagonal D j' j * outAct U v (some (i'', j'')) (some (i, j)))
      = if (i'', j'') = (i', j') then 1 else 0 := by
  simp only [outAct, Matrix.diagonal_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single j']
  · by_cases hj : j'' = j'
    · subst hj
      simp only [if_true]
      have : ∀ i, U i' i * D j'' * (U⁻¹ i i'' * if (j'' : ℕ) = 0 then v else 1)
          = U i' i * U⁻¹ i i'' := by
        intro i
        have := hD j''
        calc U i' i * D j'' * (U⁻¹ i i'' * if (j'' : ℕ) = 0 then v else 1)
            = U i' i * U⁻¹ i i'' * (D j'' * if (j'' : ℕ) = 0 then v else 1) := by ring
          _ = U i' i * U⁻¹ i i'' := by rw [this, mul_one]
      rw [sum_congr rfl fun i _ => this i, sum_mul_inv U hU]
      by_cases hi : i' = i'' <;> simp [hi, eq_comm]
    · simp [hj, Ne.symm hj]
  · intro j _ hj; simp [Ne.symm hj]
  · simp

/-- The `p q z₀` part. -/
lemma pqz_part {q : ℕ} (W : Matrix (Fin q) (Fin q) K) (hW : IsUnit W.det) (s' t' : Fin q) :
    (∑ s, W s' s * (W⁻¹).transpose t' s) = if s' = t' then 1 else 0 := by
  simp only [Matrix.transpose_apply]
  exact sum_mul_inv W hW s' t'

theorem prop_A_4_fixes : Prop_A_4_fixes := by
  intro K _ k n q g hg
  obtain ⟨U, W, -, -, hU, hW, rfl⟩ := hg
  funext a' b' c'
  rw [tAct_gTensor]
  have hD := xyz_part U hU (fun _ : Fin n => (1 : K)) 1 (fun j => by simp)
  rcases a' with i' | s' <;> rcases b' with j' | t' <;> rcases c' with _ | ⟨i'', j''⟩ <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero,
      add_zero, zero_add, gTensor]
  all_goals first
    | (rw [← Matrix.diagonal_one]; exact hD _ _ _ _)
    | (simp [outAct]; done)
    | (simp [outAct]; exact sum_mul_inv W hW _ _)

lemma sTensor_fixes (k n q : ℕ) : ∀ g ∈ B_S K k n q,
    tAct g.1 g.2.1 g.2.2 (sTensor k n q) = sTensor k n q := by
  intro g hg
  obtain ⟨U, W, v, -, -, hU, hW, hv, rfl⟩ := hg
  funext a' b' c'
  rw [tAct_sTensor]
  have hD := xyz_part U hU (fun j : Fin n => if (j : ℕ) = 0 then v⁻¹ else 1) v
    (fun j => by by_cases h : (j : ℕ) = 0 <;> simp [h, hv])
  rcases a' with i' | s' | u <;> rcases b' with j' | t' <;> rcases c' with _ | ⟨i'', j''⟩ <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, mul_zero, Finset.sum_const_zero,
      add_zero, zero_add, sTensor, ite_self]
  all_goals first
    | (exact hD _ _ _ _)
    | (simp [outAct]; done)
    | (simp [outAct]; exact sum_mul_inv W hW _ _)
    | (simp only [outAct, mul_one, Matrix.diagonal_apply]
       rw [Finset.sum_eq_single j']
       · by_cases h : (j' : ℕ) = 0 <;> simp [h, hv]
       · intro j _ hj; simp [Ne.symm hj]
       · simp)

/-! ## The fixed lines -/

/-- A vector on which an injective diagonal acts by a scalar is a multiple of a coordinate
vector. -/
lemma coord_of_torus {A : Type} [Fintype A] [DecidableEq A] (d : A → K)
    (hd : Function.Injective d) (a : A → K) (ha : a ≠ 0) (l : K) (hl : ∀ x, d x * a x = l * a x) :
    ∃ x₀, a x₀ ≠ 0 ∧ a = a x₀ • Pi.single x₀ 1 := by
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.1 ha
  refine ⟨x₀, hx₀, funext fun x => ?_⟩
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hx : x = x₀
  · subst hx; simp
  · rw [if_neg hx, mul_zero]
    by_contra hax
    have e1 : d x = l := mul_right_cancel₀ hax (hl x)
    have e2 : d x₀ = l := mul_right_cancel₀ hx₀ (hl x₀)
    exact hx (hd (e1.trans e2.symm))

lemma upperTri_diagonal {m : ℕ} (d : Fin m → K) : UpperTri (Matrix.diagonal d) := by
  intro i j hij
  exact Matrix.diagonal_apply_ne _ (ne_of_lt hij).symm

lemma isUnit_det_diagonal_cast {m : ℕ} [CharZero K] (c : ℕ) :
    IsUnit (Matrix.diagonal fun i : Fin m => ((c + i + 1 : ℕ) : K)).det := by
  rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
  exact prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)

/-- The unipotent `I + E_{i₀j₀}`. -/
noncomputable def unip {m : ℕ} (i₀ j₀ : Fin m) : Matrix (Fin m) (Fin m) K :=
  1 + Matrix.single i₀ j₀ 1

lemma upperTri_unip {m : ℕ} (i₀ j₀ : Fin m) (h : i₀ < j₀) : UpperTri (unip (K := K) i₀ j₀) := by
  intro i j hij
  simp only [unip, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  rw [if_neg (ne_of_lt hij).symm, if_neg]
  · simp
  · rintro ⟨rfl, rfl⟩; exact absurd (lt_trans hij h) (lt_irrefl _)

lemma isUnit_det_unip {m : ℕ} (i₀ j₀ : Fin m) (h : i₀ < j₀) :
    IsUnit (unip (K := K) i₀ j₀).det := by
  have hb : (unip (K := K) i₀ j₀).BlockTriangular id := fun i j hij => upperTri_unip i₀ j₀ h i j hij
  rw [Matrix.det_of_upperTriangular hb, isUnit_iff_ne_zero]
  refine prod_ne_zero_iff.2 fun i _ => ?_
  simp only [unip, Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply]
  rw [if_neg (fun h' => by rw [h'.1, ← h'.2] at h; exact lt_irrefl _ h)]
  simp

lemma isUnit_det_one {m : ℕ} : IsUnit (1 : Matrix (Fin m) (Fin m) K).det := by simp

lemma upperTri_one {m : ℕ} : UpperTri (1 : Matrix (Fin m) (Fin m) K) := by
  rw [← Matrix.diagonal_one]; exact upperTri_diagonal _

lemma mulVec_smul_single {A : Type} [Fintype A] [DecidableEq A] (M : Matrix A A K) (α : K)
    (x y : A) : (M *ᵥ (α • Pi.single x (1 : K))) y = α * M y x := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]

lemma unip_apply_ne {m : ℕ} (i₀ j₀ : Fin m) (h : i₀ ≠ j₀) : unip (K := K) i₀ j₀ i₀ j₀ = 1 := by
  simp [unip, Matrix.one_apply, h]

/-- Upper-triangular `U`: `U e_0 = U_{00} e_0`. -/
lemma upperTri_col0 {m : ℕ} (U : Matrix (Fin m) (Fin m) K) (hU : UpperTri U) (i i₀ : Fin m)
    (h0 : (i₀ : ℕ) = 0) (hi : i ≠ i₀) : U i i₀ = 0 :=
  hU i i₀ (by rw [Fin.lt_def, h0]; exact Nat.pos_of_ne_zero (fun h => hi (Fin.ext (by omega))))

theorem prop_A_4_lines : Prop_A_4_lines := by
  intro K _ _ k n q hk hq a
  constructor
  · rintro ⟨ha, hfix⟩
    set dU : Fin k → K := fun i => ((0 + i + 1 : ℕ) : K)
    set dW : Fin q → K := fun s => ((k + s + 1 : ℕ) : K)
    have hmem : (Matrix.fromBlocks (Matrix.diagonal dU) 0 0 (Matrix.diagonal dW),
        Matrix.fromBlocks 1 0 0 ((Matrix.diagonal dW)⁻¹).transpose,
        outAct (n := n) (Matrix.diagonal dU) 1) ∈ B_G K k n q :=
      ⟨_, _, upperTri_diagonal _, upperTri_diagonal _, isUnit_det_diagonal_cast 0,
        isUnit_det_diagonal_cast k, rfl⟩
    obtain ⟨l, hl⟩ := hfix _ hmem
    rw [Matrix.fromBlocks_diagonal] at hl
    have hd : Function.Injective (Sum.elim dU dW) := by
      intro x y hxy
      rcases x with i | s <;> rcases y with j | t <;>
        simp only [Sum.elim_inl, Sum.elim_inr, dU, dW, Nat.cast_inj] at hxy
      · exact congrArg Sum.inl (Fin.ext (by omega))
      · have := t.2; omega
      · have := s.2; omega
      · exact congrArg Sum.inr (Fin.ext (by omega))
    obtain ⟨x₀, hx₀, hax⟩ := coord_of_torus (Sum.elim dU dW) hd a ha l (fun x => by
      have := congrFun hl x
      simpa [Matrix.mulVec_diagonal] using this)
    refine ⟨a x₀, hx₀, ?_⟩
    rcases x₀ with i | s
    · by_cases hi : (i : ℕ) = 0
      · left; obtain rfl : i = ⟨0, hk⟩ := Fin.ext hi; exact hax
      · exfalso
        have hlt : (⟨0, hk⟩ : Fin k) < i := by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero hi
        have hmem' : (Matrix.fromBlocks (unip ⟨0, hk⟩ i) 0 0 1,
            Matrix.fromBlocks 1 0 0 ((1 : Matrix (Fin q) (Fin q) K)⁻¹).transpose,
            outAct (n := n) (unip (K := K) ⟨0, hk⟩ i) 1) ∈ B_G K k n q :=
          ⟨_, _, upperTri_unip _ _ hlt, upperTri_one, isUnit_det_unip _ _ hlt, isUnit_det_one, rfl⟩
        obtain ⟨l', hl'⟩ := hfix _ hmem'
        have := congrFun hl' (Sum.inl ⟨0, hk⟩)
        rw [hax, mulVec_smul_single] at this
        simp only [Matrix.fromBlocks_apply₁₁, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
          unip_apply_ne _ _ (ne_of_lt hlt)] at this
        rw [if_neg (fun h => ne_of_lt hlt (Sum.inl_injective h))] at this
        simp at this
        exact hx₀ this
    · by_cases hs : (s : ℕ) = 0
      · right; obtain rfl : s = ⟨0, hq⟩ := Fin.ext hs; exact hax
      · exfalso
        have hlt : (⟨0, hq⟩ : Fin q) < s := by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero hs
        have hmem' : (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) K) 0 0 (unip ⟨0, hq⟩ s),
            Matrix.fromBlocks 1 0 0 ((unip (K := K) ⟨0, hq⟩ s)⁻¹).transpose,
            outAct (n := n) (1 : Matrix (Fin k) (Fin k) K) 1) ∈ B_G K k n q :=
          ⟨_, _, upperTri_one, upperTri_unip _ _ hlt, isUnit_det_one, isUnit_det_unip _ _ hlt, rfl⟩
        obtain ⟨l', hl'⟩ := hfix _ hmem'
        have := congrFun hl' (Sum.inr ⟨0, hq⟩)
        rw [hax, mulVec_smul_single] at this
        simp only [Matrix.fromBlocks_apply₂₂, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
          unip_apply_ne _ _ (ne_of_lt hlt)] at this
        rw [if_neg (fun h => ne_of_lt hlt (Sum.inr_injective h))] at this
        simp at this
        exact hx₀ this
  · rintro ⟨α, hα, h⟩
    refine ⟨?_, fun g hg => ?_⟩
    · rintro h0
      rcases h with h | h <;> rw [h] at h0
      · have := congrFun h0 (Sum.inl ⟨0, hk⟩); simp at this; exact hα this
      · have := congrFun h0 (Sum.inr ⟨0, hq⟩); simp at this; exact hα this
    obtain ⟨U, W, hUt, hWt, -, -, rfl⟩ := hg
    rcases h with rfl | rfl
    · refine ⟨U ⟨0, hk⟩ ⟨0, hk⟩, funext fun y => ?_⟩
      rw [mulVec_smul_single]
      rcases y with i | s
      · simp only [Matrix.fromBlocks_apply₁₁, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        by_cases hi : i = ⟨0, hk⟩
        · subst hi; simp; ring
        · rw [upperTri_col0 U hUt i ⟨0, hk⟩ rfl hi]
          simp [hi]
      · simp
    · refine ⟨W ⟨0, hq⟩ ⟨0, hq⟩, funext fun y => ?_⟩
      rw [mulVec_smul_single]
      rcases y with i | s
      · simp
      · simp only [Matrix.fromBlocks_apply₂₂, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        by_cases hs : s = ⟨0, hq⟩
        · subst hs; simp; ring
        · rw [upperTri_col0 W hWt s ⟨0, hq⟩ rfl hs]
          simp [hs]

lemma sTensor_lines [CharZero K] (k n q : ℕ) (hk : 0 < k) (hq : 0 < q)
    (a : Fin k ⊕ (Fin q ⊕ Unit) → K) :
    FixedLine (B_S K k n q) a ↔
      ∃ α : K, α ≠ 0 ∧ (a = α • (Pi.single (Sum.inl ⟨0, hk⟩) 1 : Fin k ⊕ (Fin q ⊕ Unit) → K) ∨
        a = α • (Pi.single (Sum.inr (Sum.inl ⟨0, hq⟩)) 1 : Fin k ⊕ (Fin q ⊕ Unit) → K) ∨
        a = α • (Pi.single (Sum.inr (Sum.inr ())) 1 : Fin k ⊕ (Fin q ⊕ Unit) → K)) := by
  constructor
  · rintro ⟨ha, hfix⟩
    set dU : Fin k → K := fun i => ((0 + i + 1 : ℕ) : K)
    set dW : Fin q → K := fun s => ((k + s + 1 : ℕ) : K)
    set v₀ : K := ((k + q + 1 : ℕ) : K)
    have hv₀ : v₀ ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)
    have hmem : (Matrix.fromBlocks (Matrix.diagonal dU) 0 0
          (Matrix.fromBlocks (Matrix.diagonal dW) 0 0 (Matrix.diagonal fun _ : Unit => v₀)),
        Matrix.fromBlocks (Matrix.diagonal fun j : Fin n => if (j : ℕ) = 0 then v₀⁻¹ else 1) 0 0
          ((Matrix.diagonal dW)⁻¹).transpose,
        outAct (n := n) (Matrix.diagonal dU) v₀) ∈ B_S K k n q :=
      ⟨_, _, _, upperTri_diagonal _, upperTri_diagonal _, isUnit_det_diagonal_cast 0,
        isUnit_det_diagonal_cast k, hv₀, rfl⟩
    obtain ⟨l, hl⟩ := hfix _ hmem
    rw [Matrix.fromBlocks_diagonal, Matrix.fromBlocks_diagonal] at hl
    have hd : Function.Injective (Sum.elim dU (Sum.elim dW fun _ : Unit => v₀)) := by
      intro x y hxy
      rcases x with i | s | u <;> rcases y with j | t | u' <;>
        simp only [Sum.elim_inl, Sum.elim_inr, dU, dW, v₀, Nat.cast_inj] at hxy
      · exact congrArg Sum.inl (Fin.ext (by omega))
      · have := t.2; omega
      · omega
      · have := s.2; omega
      · exact congrArg (Sum.inr ∘ Sum.inl) (Fin.ext (by omega))
      · have := s.2; omega
      · omega
      · have := t.2; omega
      · rfl
    obtain ⟨x₀, hx₀, hax⟩ := coord_of_torus _ hd a ha l (fun x => by
      have := congrFun hl x
      simpa [Matrix.mulVec_diagonal] using this)
    refine ⟨a x₀, hx₀, ?_⟩
    rcases x₀ with i | s | u
    · by_cases hi : (i : ℕ) = 0
      · left; obtain rfl : i = ⟨0, hk⟩ := Fin.ext hi; exact hax
      · exfalso
        have hlt : (⟨0, hk⟩ : Fin k) < i := by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero hi
        have hmem' : (Matrix.fromBlocks (unip ⟨0, hk⟩ i) 0 0
              (Matrix.fromBlocks (1 : Matrix (Fin q) (Fin q) K) 0 0 (Matrix.diagonal fun _ : Unit => (1 : K))),
            Matrix.fromBlocks (Matrix.diagonal fun j : Fin n => if (j : ℕ) = 0 then (1 : K)⁻¹ else 1)
              0 0 ((1 : Matrix (Fin q) (Fin q) K)⁻¹).transpose,
            outAct (n := n) (unip (K := K) ⟨0, hk⟩ i) 1) ∈ B_S K k n q :=
          ⟨_, _, _, upperTri_unip _ _ hlt, upperTri_one, isUnit_det_unip _ _ hlt, isUnit_det_one,
            one_ne_zero, rfl⟩
        obtain ⟨l', hl'⟩ := hfix _ hmem'
        have := congrFun hl' (Sum.inl ⟨0, hk⟩)
        rw [hax, mulVec_smul_single] at this
        simp only [Matrix.fromBlocks_apply₁₁, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
          unip_apply_ne _ _ (ne_of_lt hlt)] at this
        rw [if_neg (fun h => ne_of_lt hlt (Sum.inl_injective h))] at this
        simp at this
        exact hx₀ this
    · by_cases hs : (s : ℕ) = 0
      · right; left; obtain rfl : s = ⟨0, hq⟩ := Fin.ext hs; exact hax
      · exfalso
        have hlt : (⟨0, hq⟩ : Fin q) < s := by rw [Fin.lt_def]; exact Nat.pos_of_ne_zero hs
        have hmem' : (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) K) 0 0
              (Matrix.fromBlocks (unip ⟨0, hq⟩ s) 0 0 (Matrix.diagonal fun _ : Unit => (1 : K))),
            Matrix.fromBlocks (Matrix.diagonal fun j : Fin n => if (j : ℕ) = 0 then (1 : K)⁻¹ else 1)
              0 0 ((unip (K := K) ⟨0, hq⟩ s)⁻¹).transpose,
            outAct (n := n) (1 : Matrix (Fin k) (Fin k) K) 1) ∈ B_S K k n q :=
          ⟨_, _, _, upperTri_one, upperTri_unip _ _ hlt, isUnit_det_one, isUnit_det_unip _ _ hlt,
            one_ne_zero, rfl⟩
        obtain ⟨l', hl'⟩ := hfix _ hmem'
        have := congrFun hl' (Sum.inr (Sum.inl ⟨0, hq⟩))
        rw [hax, mulVec_smul_single] at this
        simp only [Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁, Pi.smul_apply,
          Pi.single_apply, smul_eq_mul, unip_apply_ne _ _ (ne_of_lt hlt)] at this
        rw [if_neg (fun h => ne_of_lt hlt (Sum.inl_injective (Sum.inr_injective h)))] at this
        simp at this
        exact hx₀ this
    · right; right; exact hax
  · rintro ⟨α, hα, h⟩
    refine ⟨?_, fun g hg => ?_⟩
    · rintro h0
      rcases h with h | h | h <;> rw [h] at h0
      · have := congrFun h0 (Sum.inl ⟨0, hk⟩); simp at this; exact hα this
      · have := congrFun h0 (Sum.inr (Sum.inl ⟨0, hq⟩)); simp at this; exact hα this
      · have := congrFun h0 (Sum.inr (Sum.inr ())); simp at this; exact hα this
    obtain ⟨U, W, v, hUt, hWt, -, -, -, rfl⟩ := hg
    rcases h with rfl | rfl | rfl
    · refine ⟨U ⟨0, hk⟩ ⟨0, hk⟩, funext fun y => ?_⟩
      rw [mulVec_smul_single]
      rcases y with i | s | u
      · simp only [Matrix.fromBlocks_apply₁₁, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
        by_cases hi : i = ⟨0, hk⟩
        · subst hi; simp; ring
        · rw [upperTri_col0 U hUt i ⟨0, hk⟩ rfl hi]
          simp [hi]
      · simp
      · simp
    · refine ⟨W ⟨0, hq⟩ ⟨0, hq⟩, funext fun y => ?_⟩
      rw [mulVec_smul_single]
      rcases y with i | s | u
      · simp
      · simp only [Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁, Pi.smul_apply,
          Pi.single_apply, smul_eq_mul]
        by_cases hs : s = ⟨0, hq⟩
        · subst hs; simp; ring
        · rw [upperTri_col0 W hWt s ⟨0, hq⟩ rfl hs]
          simp [hs]
      · simp
    · refine ⟨v, funext fun y => ?_⟩
      rw [mulVec_smul_single]
      rcases y with i | s | u
      · simp
      · simp
      · simp; ring

/-! ## The quotients -/

/-- `quot0` by a vector supported at one coordinate zeroes that slice. -/
lemma quot0_coord {A B C : Type} [DecidableEq A] (T : A → B → C → K) (a : A → K) (c : A)
    (hc : a c ≠ 0) (h0 : ∀ x, x ≠ c → a x = 0) :
    quot0 T a = fun x b o => if x = c then 0 else T x b o := by
  classical
  unfold quot0
  have h : ∃ c', a c' ≠ 0 := ⟨c, hc⟩
  rw [dif_pos h]
  have hch : h.choose = c := by
    by_contra hne; exact h.choose_spec (h0 _ hne)
  funext x b o
  simp only [hch]
  by_cases hx : x = c
  · simp [hx]
  · simp [hx, h0 x hx]

lemma quot0_single {A B C : Type} [DecidableEq A] (T : A → B → C → K) (c : A) (α : K)
    (hα : α ≠ 0) : quot0 T (α • (Pi.single c 1 : A → K)) = fun x b o => if x = c then 0 else T x b o :=
  quot0_coord T _ c (by simp [hα]) (fun x hx => by simp [Pi.single_apply, hx])

lemma tExtend_mem {A' B' C' A B C : Type} (eA : A' → A) (eB : B' → B) (eC : C' → C)
    (hA : Function.Injective eA) (hB : Function.Injective eB) (hC : Function.Injective eC)
    (T' : A' → B' → C' → K) (a' : A') (b' : B') (c' : C') :
    tExtend eA eB eC T' (eA a') (eB b') (eC c') = T' a' b' c' := by
  classical
  unfold tExtend
  have h : (∃ x, eA x = eA a') ∧ (∃ y, eB y = eB b') ∧ (∃ z, eC z = eC c') :=
    ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩
  rw [dif_pos h, hA h.1.choose_spec, hB h.2.1.choose_spec, hC h.2.2.choose_spec]

/-- A tensor equal to `T'` on the images and zero off them is `T'` padded by zero slices. -/
lemma eq_tExtend {A' B' C' A B C : Type} (eA : A' → A) (eB : B' → B) (eC : C' → C)
    (hA : Function.Injective eA) (hB : Function.Injective eB) (hC : Function.Injective eC)
    (T' : A' → B' → C' → K) (T : A → B → C → K)
    (h1 : ∀ a' b' c', T (eA a') (eB b') (eC c') = T' a' b' c')
    (h2 : ∀ a b c, T a b c ≠ 0 → (∃ a', eA a' = a) ∧ (∃ b', eB b' = b) ∧ (∃ c', eC c' = c)) :
    T = tExtend eA eB eC T' := by
  classical
  funext a b c
  by_cases hr : (∃ a', eA a' = a) ∧ (∃ b', eB b' = b) ∧ (∃ c', eC c' = c)
  · obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩⟩ := hr
    rw [tExtend_mem eA eB eC hA hB hC, h1]
  · unfold tExtend
    rw [dif_neg hr]
    by_contra hne
    exact hr (h2 a b c hne)

lemma inj_succ_l {k q : ℕ} : Function.Injective (Sum.map Fin.succ id : Fin k ⊕ Fin q → _) :=
  Sum.map_injective.2 ⟨Fin.succ_injective _, Function.injective_id⟩

lemma inj_succ_r {k q : ℕ} : Function.Injective (Sum.map id Fin.succ : Fin k ⊕ Fin q → _) :=
  Sum.map_injective.2 ⟨Function.injective_id, Fin.succ_injective _⟩

lemma inj_out {k n : ℕ} :
    Function.Injective (Option.map (Prod.map Fin.succ id) : Option (Fin k × Fin n) → _) :=
  Option.map_injective ((Fin.succ_injective _).prodMap Function.injective_id)

theorem prop_A_4_quotients : Prop_A_4_quotients := by
  intro K _ k n q
  refine ⟨?_, ?_, fun T c α hα => ?_⟩
  · rw [quot0_coord _ _ (Sum.inl 0) (by simp) (fun x hx => by simp [Pi.single_apply, hx])]
    refine eq_tExtend _ _ _ inj_succ_l Function.injective_id inj_out _ _ ?_ ?_
    · intro a' b' c'
      rcases a' with i | s <;> rcases b' with j | t <;> rcases c' with _ | ⟨i', j'⟩ <;>
        simp [gTensor, Prod.ext_iff, Fin.succ_ne_zero]
    · intro a b c h
      rcases a with i | s <;> rcases b with j | t <;> rcases c with _ | ⟨i', j'⟩ <;>
        simp [gTensor] at h
      · obtain ⟨hi0, rfl, rfl⟩ := h
        obtain ⟨i0, rfl⟩ := Fin.exists_succ_eq.2 hi0
        exact ⟨⟨.inl i0, rfl⟩, ⟨_, rfl⟩, ⟨some (i0, _), rfl⟩⟩
      · subst h; exact ⟨⟨.inr s, rfl⟩, ⟨_, rfl⟩, ⟨none, rfl⟩⟩
  · rw [quot0_coord _ _ (Sum.inr 0) (by simp) (fun x hx => by simp [Pi.single_apply, hx])]
    refine eq_tExtend _ _ _ inj_succ_r inj_succ_r Function.injective_id _ _ ?_ ?_
    · intro a' b' c'
      rcases a' with i | s <;> rcases b' with j | t <;> rcases c' with _ | ⟨i', j'⟩ <;>
        simp [gTensor, Prod.ext_iff, Fin.succ_ne_zero]
    · intro a b c h
      rcases a with i | s <;> rcases b with j | t <;> rcases c with _ | ⟨i', j'⟩ <;>
        simp [gTensor] at h
      · obtain ⟨rfl, rfl⟩ := h
        exact ⟨⟨.inl i', rfl⟩, ⟨.inl j', rfl⟩, ⟨some (i', j'), rfl⟩⟩
      · obtain ⟨hs0, rfl⟩ := h
        obtain ⟨s0, rfl⟩ := Fin.exists_succ_eq.2 hs0
        exact ⟨⟨.inr s0, rfl⟩, ⟨.inr s0, rfl⟩, ⟨none, rfl⟩⟩
  · rw [quot0_single T c α hα, quot0_coord T _ c (by simp) (fun x hx => by simp [Pi.single_apply, hx])]

lemma range_succ_l {k : ℕ} {X : Type} (a : Fin (k + 1) ⊕ X) :
    (∃ a', Sum.map Fin.succ id a' = a) ↔ a ≠ Sum.inl 0 := by
  constructor
  · rintro ⟨a', rfl⟩; rcases a' with i | x <;> simp [Fin.succ_ne_zero]
  · intro h
    rcases a with i | x
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i0, rfl⟩
      · exact absurd rfl h
      · exact ⟨Sum.inl i0, rfl⟩
    · exact ⟨Sum.inr x, rfl⟩

lemma range_succ_r {q : ℕ} {X : Type} (b : X ⊕ Fin (q + 1)) :
    (∃ b', Sum.map id Fin.succ b' = b) ↔ b ≠ Sum.inr 0 := by
  constructor
  · rintro ⟨b', rfl⟩; rcases b' with x | s <;> simp [Fin.succ_ne_zero]
  · intro h
    rcases b with x | s
    · exact ⟨Sum.inl x, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s0, rfl⟩
      · exact absurd rfl h
      · exact ⟨Sum.inr s0, rfl⟩

lemma range_out {k n : ℕ} (c : Option (Fin (k + 1) × Fin n)) :
    (∃ c', Option.map (Prod.map Fin.succ id) c' = c) ↔ ∀ j, c ≠ some (0, j) := by
  constructor
  · rintro ⟨c', rfl⟩ j; rcases c' with _ | ⟨i, j'⟩ <;> simp [Fin.succ_ne_zero]
  · intro h
    rcases c with _ | ⟨i, j⟩
    · exact ⟨none, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i0, rfl⟩
      · exact absurd rfl (h j)
      · exact ⟨some (i0, j), rfl⟩

lemma range_inner {k q : ℕ} (a : Fin k ⊕ (Fin (q + 1) ⊕ Unit)) :
    (∃ a', Sum.map id (Sum.map Fin.succ id) a' = a) ↔ a ≠ Sum.inr (Sum.inl 0) := by
  constructor
  · rintro ⟨a', rfl⟩; rcases a' with i | s | u <;> simp [Fin.succ_ne_zero]
  · intro h
    rcases a with i | s | u
    · exact ⟨Sum.inl i, rfl⟩
    · rcases Fin.eq_zero_or_eq_succ s with rfl | ⟨s0, rfl⟩
      · exact absurd rfl h
      · exact ⟨Sum.inr (Sum.inl s0), rfl⟩
    · exact ⟨Sum.inr (Sum.inr u), rfl⟩

lemma range_inl {k q : ℕ} (a : Fin k ⊕ (Fin q ⊕ Unit)) :
    (∃ a', Sum.map id Sum.inl a' = a) ↔ a ≠ Sum.inr (Sum.inr ()) := by
  constructor
  · rintro ⟨a', rfl⟩; rcases a' with i | s <;> simp
  · intro h
    rcases a with i | s | u
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr s, rfl⟩
    · exact absurd rfl h

lemma range_id' {X : Type} (x : X) : ∃ x', id x' = x := ⟨x, rfl⟩

lemma inj_succ_l' {k : ℕ} {X : Type} : Function.Injective (Sum.map Fin.succ id : Fin k ⊕ X → _) :=
  Sum.map_injective.2 ⟨Fin.succ_injective _, Function.injective_id⟩

theorem prop_A_5_linalg : Prop_A_5_linalg := by
  intro K _
  refine ⟨fun k n q => sTensor_fixes k n q, fun _ k n q hk hq a => sTensor_lines k n q hk hq a,
    fun k n q => ⟨?_, ?_, ?_⟩⟩
  · rw [quot0_coord _ _ (Sum.inl 0) (by simp) (fun x hx => by simp [Pi.single_apply, hx])]
    refine eq_tExtend _ _ _ inj_succ_l' Function.injective_id inj_out _ _ ?_ ?_
    · intro a' b' c'
      rcases a' with i | s | u <;> rcases b' with j | t <;> rcases c' with _ | ⟨i', j'⟩ <;>
        simp [sTensor, Prod.ext_iff, Fin.succ_ne_zero]
    · intro a b c h
      refine ⟨(range_succ_l a).2 ?_, range_id' b, (range_out c).2 ?_⟩
      · rintro rfl; exact h (by simp)
      · rintro j rfl
        apply h
        rcases a with i | s | u <;> rcases b with j' | t <;> simp [sTensor]
        all_goals (intros; simp_all [eq_comm])
  · rw [quot0_coord _ _ (Sum.inr (Sum.inl 0)) (by simp)
      (fun x hx => by simp [Pi.single_apply, hx])]
    refine eq_tExtend _ _ _ (Sum.map_injective.2 ⟨Function.injective_id, inj_succ_l'⟩)
      inj_succ_r Function.injective_id _ _ ?_ ?_
    · intro a' b' c'
      rcases a' with i | s | u <;> rcases b' with j | t <;> rcases c' with _ | ⟨i', j'⟩ <;>
        simp [sTensor, Prod.ext_iff, Fin.succ_ne_zero]
    · intro a b c h
      refine ⟨(range_inner a).2 ?_, (range_succ_r b).2 ?_, range_id' c⟩
      · rintro rfl; exact h (by simp)
      · rintro rfl
        apply h
        rcases a with i | s | u <;> rcases c with _ | ⟨i', j'⟩ <;> simp [sTensor]
        all_goals (intros; simp_all [eq_comm])
  · rw [quot0_coord _ _ (Sum.inr (Sum.inr ())) (by simp)
      (fun x hx => by simp [Pi.single_apply, hx])]
    refine eq_tExtend _ _ _ (Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩)
      Function.injective_id Function.injective_id _ _ ?_ ?_
    · intro a' b' c'
      rcases a' with i | s <;> rcases b' with j | t <;> rcases c' with _ | ⟨i', j'⟩ <;>
        simp [sTensor, gTensor]
    · intro a b c h
      refine ⟨(range_inl a).2 ?_, range_id' b, range_id' c⟩
      rintro rfl; exact h (by simp)

/-! ## The composition with Lemma A.3 -/

theorem prop_A_4_composed : Prop_A_4_composed := by
  intro K _ _ br Solv hA3 hpad hSolv h1 h2 h3
  refine prop_A_4 (fun k n q => br (gTensor (K := K) k n q)) h1 h2 h3 ?_
  intro k n q hk hq
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hne : gTensor (K := K) (k' + 1) n (q' + 1) ≠ 0 := by
    intro h
    have := congrFun (congrFun (congrFun h (Sum.inr 0)) (Sum.inr 0)) none
    simp [gTensor] at this
  obtain ⟨a, hfix, hbr⟩ := hA3 (gTensor (k' + 1) n (q' + 1)) (B_G K (k' + 1) n (q' + 1))
    (hSolv _ _ _) (prop_A_4_fixes K _ _ _) hne
  obtain ⟨α, hα, ha | ha⟩ := (prop_A_4_lines K (k' + 1) n (q' + 1) (by omega) (by omega) a).1 hfix
  · have hq0 := (prop_A_4_quotients K k' n (q' + 1)).1
    rw [ha, (prop_A_4_quotients K k' n (q' + 1)).2.2 _ _ α hα] at hbr
    rw [show (⟨0, by omega⟩ : Fin (k' + 1)) = 0 from rfl, hq0,
      hpad _ _ _ inj_succ_l Function.injective_id inj_out] at hbr
    show 1 + min (br (gTensor (K := K) k' n (q' + 1))) (br (gTensor (K := K) (k' + 1) n q'))
      ≤ br (gTensor (K := K) (k' + 1) n (q' + 1))
    have := min_le_left (br (gTensor (K := K) k' n (q' + 1))) (br (gTensor (K := K) (k' + 1) n q'))
    beta_reduce at hbr ⊢
    omega
  · have hq0 := (prop_A_4_quotients K (k' + 1) n q').2.1
    rw [ha, (prop_A_4_quotients K (k' + 1) n q').2.2 _ _ α hα] at hbr
    rw [show (⟨0, by omega⟩ : Fin (q' + 1)) = 0 from rfl, hq0,
      hpad _ _ _ inj_succ_r inj_succ_r Function.injective_id] at hbr
    show 1 + min (br (gTensor (K := K) k' n (q' + 1))) (br (gTensor (K := K) (k' + 1) n q'))
      ≤ br (gTensor (K := K) (k' + 1) n (q' + 1))
    have := min_le_right (br (gTensor (K := K) k' n (q' + 1))) (br (gTensor (K := K) (k' + 1) n q'))
    beta_reduce at hbr ⊢
    omega

theorem prop_A_5_composed : Prop_A_5_composed := by
  intro K _ _ br Solv hA3 hpad hSolvG hSolvS hG1 hG2 hG3 hS1 hS2
  have hG := (prop_A_4_composed K br Solv hA3 hpad hSolvG hG1 hG2 hG3).1
  refine prop_A_5 (fun k n q => br (gTensor (K := K) k n q))
    (fun k n q => br (sTensor (K := K) k n q)) hG hS1 hS2 ?_
  intro k n q hk hq
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hne : sTensor (K := K) (k' + 1) n (q' + 1) ≠ 0 := by
    intro h
    have := congrFun (congrFun (congrFun h (Sum.inr (Sum.inl 0))) (Sum.inr 0)) none
    simp [sTensor] at this
  obtain ⟨a, hfix, hbr⟩ := hA3 (sTensor (k' + 1) n (q' + 1)) (B_S K (k' + 1) n (q' + 1))
    (hSolvS _ _ _) ((prop_A_5_linalg K).1 _ _ _) hne
  obtain ⟨α, hα, ha | ha | ha⟩ :=
    ((prop_A_5_linalg K).2.1 inferInstance (k' + 1) n (q' + 1) (by omega) (by omega) a).1 hfix
  all_goals rw [ha, (prop_A_4_quotients K 0 0 0).2.2 _ _ α hα] at hbr
  · rw [show (⟨0, by omega⟩ : Fin (k' + 1)) = 0 from rfl, ((prop_A_5_linalg K).2.2 k' n (q' + 1)).1,
      hpad _ _ _ inj_succ_l' Function.injective_id inj_out] at hbr
    show 1 + min (min (br (sTensor (K := K) k' n (q' + 1))) (br (sTensor (K := K) (k' + 1) n q')))
      (br (gTensor (K := K) (k' + 1) n (q' + 1))) ≤ br (sTensor (K := K) (k' + 1) n (q' + 1))
    have := min_le_left (min (br (sTensor (K := K) k' n (q' + 1))) (br (sTensor (K := K) (k' + 1) n q')))
      (br (gTensor (K := K) (k' + 1) n (q' + 1)))
    have := min_le_left (br (sTensor (K := K) k' n (q' + 1))) (br (sTensor (K := K) (k' + 1) n q'))
    beta_reduce at hbr ⊢
    omega
  · rw [show (⟨0, by omega⟩ : Fin (q' + 1)) = 0 from rfl, ((prop_A_5_linalg K).2.2 (k' + 1) n q').2.1,
      hpad _ _ _ (Sum.map_injective.2 ⟨Function.injective_id, inj_succ_l'⟩) inj_succ_r
        Function.injective_id] at hbr
    show 1 + min (min (br (sTensor (K := K) k' n (q' + 1))) (br (sTensor (K := K) (k' + 1) n q')))
      (br (gTensor (K := K) (k' + 1) n (q' + 1))) ≤ br (sTensor (K := K) (k' + 1) n (q' + 1))
    have := min_le_left (min (br (sTensor (K := K) k' n (q' + 1))) (br (sTensor (K := K) (k' + 1) n q')))
      (br (gTensor (K := K) (k' + 1) n (q' + 1)))
    have := min_le_right (br (sTensor (K := K) k' n (q' + 1))) (br (sTensor (K := K) (k' + 1) n q'))
    beta_reduce at hbr ⊢
    omega
  · rw [((prop_A_5_linalg K).2.2 (k' + 1) n (q' + 1)).2.2,
      hpad _ _ _ (Sum.map_injective.2 ⟨Function.injective_id, Sum.inl_injective⟩)
        Function.injective_id Function.injective_id] at hbr
    show 1 + min (min (br (sTensor (K := K) k' n (q' + 1))) (br (sTensor (K := K) (k' + 1) n q')))
      (br (gTensor (K := K) (k' + 1) n (q' + 1))) ≤ br (sTensor (K := K) (k' + 1) n (q' + 1))
    have := min_le_right (min (br (sTensor (K := K) k' n (q' + 1))) (br (sTensor (K := K) (k' + 1) n q')))
      (br (gTensor (K := K) (k' + 1) n (q' + 1)))
    beta_reduce at hbr ⊢
    omega

end ThinMatrixProducts

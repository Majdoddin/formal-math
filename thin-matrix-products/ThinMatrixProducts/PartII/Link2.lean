import ThinMatrixProducts.PartII.KPP

/-!
# Link 2 with [CVX23, Lemma 9.2]: the detection version suffices

The negative-triangle count of an edge is the sum of its exact-triangle counts over the instances
of the cited lemma; a sum of nonnegative integers is positive iff one of them is.
-/

namespace ThinMatrixProducts

open Finset

lemma card_filter_pos_iff {β : Type} (s : Finset β) (P : β → Prop) [DecidablePred P] :
    (0 : ℤ) < ((s.filter P).card : ℤ) ↔ ∃ b ∈ s, P b := by
  rw [Nat.cast_pos, Finset.card_pos]
  constructor
  · rintro ⟨b, hb⟩; exact ⟨b, (mem_filter.1 hb).1, (mem_filter.1 hb).2⟩
  · rintro ⟨b, hb, hx⟩; exact ⟨b, mem_filter.2 ⟨hb, hx⟩⟩

theorem sec15_link2_detection : Sec15_link2_detection := by
  classical
  intro hCVX
  obtain ⟨c, hc⟩ := hCVX
  refine ⟨c, fun n A B C w => ?_⟩
  obtain ⟨I, wI, t, hI, ht, hcount⟩ := hc n A B C w
  refine ⟨I, wI, t, hI, ht, fun a ha c' hc' => ?_⟩
  rw [← card_filter_pos_iff, hcount a ha c' hc']
  set f : Fin I → ℤ := fun i => ((B.filter fun b => ∃ x y z, wI i a b = some x ∧
    wI i b c' = some y ∧ wI i a c' = some z ∧ x + y + z = t i).card : ℤ) with hf
  have hpos : (0 : ℤ) < ∑ i, f i ↔ ∃ i, 0 < f i := by
    constructor
    · intro hs
      by_contra hno
      push Not at hno
      have : (∑ i, f i) ≤ 0 := Finset.sum_nonpos fun i _ => hno i
      linarith
    · rintro ⟨i, hi⟩
      exact lt_of_lt_of_le hi
        (Finset.single_le_sum (f := f) (fun j _ => Nat.cast_nonneg _) (mem_univ i))
  rw [hpos]
  exact exists_congr fun i => card_filter_pos_iff _ _

end ThinMatrixProducts

namespace ThinMatrixProducts

open Finset

/-- The encoding of a sum of two entries: exact for finite sums, at least `2B + 1` otherwise. -/
lemma enc_sum (B : ℤ) (hB : 0 ≤ B) (x y : WithTop ℤ) (hx : ∀ v : ℤ, x = v → |v| ≤ B)
    (hy : ∀ v : ℤ, y = v → |v| ≤ B) :
    (x + y = ⊤ → 2 * B + 1 ≤ x.untopD (3 * B + 1) + y.untopD (3 * B + 1)) ∧
    ∀ s : ℤ, x + y = s → x.untopD (3 * B + 1) + y.untopD (3 * B + 1) = s := by
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe
  · simp; linarith
  · rename_i b
    have := abs_le.1 (hy b rfl)
    simp; linarith
  · rename_i a
    have := abs_le.1 (hx a rfl)
    simp; linarith
  · rename_i a b
    refine ⟨fun h => by simp at h, fun s hs => ?_⟩
    simp only [WithTop.untopD_coe]
    exact_mod_cast hs

theorem sec15_apsp_step : Sec15_apsp_step := by
  intro n B X Y hB hX hY hC i j P
  have hP : ∀ k, (X i k + Y k j = ⊤ → 2 * B + 1 ≤
        (X i k).untopD (3 * B + 1) + (Y k j).untopD (3 * B + 1)) ∧
      ∀ s : ℤ, X i k + Y k j = s →
        (X i k).untopD (3 * B + 1) + (Y k j).untopD (3 * B + 1) = s := fun k =>
    enc_sum B hB _ _ (hX i k) (hY k j)
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨i, mem_univ i⟩
  rcases hm : minPlus X Y i j with _ | v
  · -- the product is `∞`: every term has an `∞`, so `P ≥ 2B + 1 > B`
    have hall : ∀ k, X i k + Y k j = ⊤ := by
      intro k
      have : (univ.inf fun k => X i k + Y k j) = ⊤ := hm
      exact (Finset.inf_eq_top_iff _ _).1 this k (mem_univ k)
    have hPge : 2 * B + 1 ≤ P := Finset.le_inf' hne _ fun k _ => (hP k).1 (hall k)
    rw [if_pos (by linarith)]
    rfl
  · -- the product is `v`: `P = v`
    have hv := abs_le.1 (hC i j v hm)
    have hinf : (univ.inf fun k => X i k + Y k j) = (v : WithTop ℤ) := hm
    obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_inf univ hne fun k => X i k + Y k j
    rw [hinf] at hk₀
    have hPv : P = v := by
      apply le_antisymm
      · exact (Finset.inf'_le _ (mem_univ k₀)).trans (le_of_eq ((hP k₀).2 v hk₀.symm))
      · refine Finset.le_inf' hne _ fun k _ => ?_
        rcases hk : X i k + Y k j with _ | s
        · linarith [(hP k).1 hk]
        · have hk' : X i k + Y k j = (s : WithTop ℤ) := hk
          rw [(hP k).2 s hk']
          have : (v : WithTop ℤ) ≤ (s : WithTop ℤ) := by
            rw [← hinf, ← hk']; exact Finset.inf_le (mem_univ k)
          exact_mod_cast this
    rw [hPv, if_neg (by linarith)]
    rfl

end ThinMatrixProducts

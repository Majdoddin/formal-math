import Statements
import Mathlib.Data.Fintype.Pi
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Appendix A: Lemma A.1 (private leaves); the inductions of Propositions A.4, A.5 and Remarks A.6,
A.7
-/

namespace ThinMatrixProducts

open Finset

theorem lemma_A_1 : Lemma_A_1 := by
  intro T O _ _ _ _ contains _ R₀ R₁ L m hR₀ hR₁ w hw
  set Pure := univ.filter fun t => contains t none ∧ ∀ o, ¬ contains t (some o)
  set Priv : O → Finset T := fun o => univ.filter fun t =>
    contains t (some o) ∧ ∀ o', o' ≠ o → ¬ contains t (some o')
  set choice : Fin L → Finset T := fun ℓ => match w ℓ with
    | none => Pure
    | some o => Priv o
  set S := Fintype.piFinset choice
  -- every leaf of `S` contributes to `w` and to no other selected output string
  have hsub : S ⊆ univ.filter fun τ : Fin L → T => (∀ ℓ, contains (τ ℓ) (w ℓ)) ∧
      ∀ w' : Fin L → Option O, (univ.filter fun ℓ => w' ℓ = none).card = m →
        (∀ ℓ, contains (τ ℓ) (w' ℓ)) → w' = w := by
    intro τ hτ
    rw [Fintype.mem_piFinset] at hτ
    rw [mem_filter]
    refine ⟨mem_univ _, fun ℓ => ?_, fun w' hw' hc => ?_⟩
    · have := hτ ℓ
      simp only [choice] at this
      rcases hwl : w ℓ with _ | o
      · rw [hwl] at this; exact (mem_filter.1 this).2.1
      · rw [hwl] at this; exact (mem_filter.1 this).2.1
    · -- the inner set of `w'` contains that of `w`, and both have `m` levels
      have hQ : (univ.filter fun ℓ => w ℓ = none) ⊆ univ.filter fun ℓ => w' ℓ = none := by
        intro ℓ hℓ
        rw [mem_filter] at hℓ ⊢
        refine ⟨mem_univ _, ?_⟩
        have := hτ ℓ
        simp only [choice, hℓ.2] at this
        obtain ⟨-, -, hpure⟩ := mem_filter.1 this
        rcases hw'l : w' ℓ with _ | o
        · rfl
        · exact absurd (hw'l ▸ hc ℓ) (hpure o)
      have hQeq := eq_of_subset_of_card_le hQ (by rw [hw, hw'])
      funext ℓ
      rcases hwl : w ℓ with _ | o
      · have : ℓ ∈ univ.filter fun ℓ => w ℓ = none := mem_filter.2 ⟨mem_univ _, hwl⟩
        rw [hQeq] at this
        exact (mem_filter.1 this).2
      · have hne : w' ℓ ≠ none := by
          intro h
          have : ℓ ∈ univ.filter fun ℓ => w' ℓ = none := mem_filter.2 ⟨mem_univ _, h⟩
          rw [← hQeq] at this
          rw [(mem_filter.1 this).2] at hwl
          cases hwl
        obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.1 hne
        have := hτ ℓ
        simp only [choice, hwl] at this
        obtain ⟨-, -, hpriv⟩ := mem_filter.1 this
        by_contra hoo
        have : o' ≠ o := fun h => hoo (by rw [ho', h])
        exact hpriv o' this (ho' ▸ hc ℓ)
  refine le_trans ?_ (card_le_card hsub)
  rw [Fintype.card_piFinset]
  calc R₀ ^ m * R₁ ^ (L - m)
      = ∏ ℓ : Fin L, (if w ℓ = none then R₀ else R₁) := by
        rw [prod_ite, prod_const, prod_const, hw, filter_not, card_sdiff_of_subset (filter_subset _ _),
          card_univ, Fintype.card_fin, hw]
    _ ≤ ∏ ℓ, (choice ℓ).card := by
        apply prod_le_prod' fun ℓ _ => ?_
        simp only [choice]
        rcases hwl : w ℓ with _ | o
        · simp only [if_true]; exact hR₀
        · simp only [reduceCtorEq, if_false]; exact hR₁ o

theorem lemma_A_1_consequence : Lemma_A_1_consequence := by
  intro N q₀ R₀ R₁ m L hN hq hR₀ hR₁ hm hmL h
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set X := R₀ ^ m * R₁ ^ (L - m) with hX
  have hX0 : 0 ≤ X := by positivity
  have hq0 : 0 < q₀ := by linarith
  have hsq : Real.sqrt (q₀ ^ m) = q₀ ^ ((m : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le]; ring_nf
  have hXlt : X < q₀ ^ ((m : ℝ) / 2) := by
    have hpos : 0 < Real.sqrt (q₀ ^ m) := Real.sqrt_pos.2 (by positivity)
    rw [div_mul_eq_mul_div, div_lt_iff₀ hpos] at h
    rw [← hsq]
    nlinarith [sq_nonneg N]
  have hexp : (0 : ℝ) < 2 / m := by positivity
  have h1 : X ^ ((2 : ℝ) / m) < (q₀ ^ ((m : ℝ) / 2)) ^ ((2 : ℝ) / m) :=
    Real.rpow_lt_rpow hX0 hXlt hexp
  have h2 : (q₀ ^ ((m : ℝ) / 2)) ^ ((2 : ℝ) / m) = q₀ := by
    rw [← Real.rpow_mul hq0.le, show (m : ℝ) / 2 * (2 / m) = 1 by field_simp, Real.rpow_one]
  have h3 : X ^ ((2 : ℝ) / m) = R₀ ^ 2 * R₁ ^ (2 * ((L : ℝ) - m) / m) := by
    rw [hX, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast R₀,
      ← Real.rpow_natCast R₁, ← Real.rpow_mul hR₀, ← Real.rpow_mul hR₁, Nat.cast_sub hmL]
    congr 1
    · rw [show (m : ℝ) * (2 / m) = 2 by field_simp]; norm_num
    · congr 1; ring
  rw [← h3, ← h2]
  exact h1

/-! ## The inductions -/

theorem prop_A_4 : Prop_A_4 := by
  intro brG h1 hout hout1 hsub
  have main : ∀ s k n q, k + q = s → 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q →
      q + k + n - 1 ≤ brG k n q := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro k n q hs hk hn hq
      rcases eq_or_lt_of_le hk with rfl | hk2
      · have := h1 n q; omega
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hq ⊢
        have e1 : (k' + 2 - 1) * n' = k' * n' + n' := by
          rw [show k' + 2 - 1 = k' + 1 by omega]; ring
        rw [e1] at hq
        have hq1 : 1 ≤ q := by omega
        have hstep := hsub (k' + 2) (n' + 1) q (by omega) hq1
        -- the first branch, by induction
        have b1 : q + (k' + 1) + (n' + 1) - 1 ≤ brG (k' + 2 - 1) (n' + 1) q := by
          have := ih (k' + 1 + q) (by omega) (k' + 1) (n' + 1) q rfl (by omega) (by omega)
            (by rw [show k' + 1 - 1 = k' by omega, Nat.add_sub_cancel]; nlinarith)
          simpa [show k' + 2 - 1 = k' + 1 by omega] using this
        -- the second branch
        have b2 : q + (k' + 2) + (n' + 1) - 2 ≤ brG (k' + 2) (n' + 1) (q - 1) := by
          by_cases hq2 : k' * n' + n' + 1 ≤ q - 1
          · have := ih (k' + 2 + (q - 1)) (by omega) (k' + 2) (n' + 1) (q - 1) rfl (by omega)
              (by omega) (by rw [Nat.add_sub_cancel, e1]; exact hq2)
            omega
          · have hqe : q - 1 = k' * n' + n' := by omega
            by_cases hq3 : 1 ≤ q - 1
            · have := hout1 (k' + 2) (n' + 1) (q - 1) hq3
              have e2 : (k' + 2) * (n' + 1) = k' * n' + n' + 1 + (k' + 2) + (n' + 1) - 2 := by
                ring_nf; omega
              omega
            · have := hout (k' + 2) (n' + 1) (q - 1)
              have hn0 : n' = 0 := by
                rcases Nat.eq_zero_or_pos n' with h | h
                · exact h
                · exfalso; nlinarith
              subst hn0
              omega
        omega
  refine ⟨fun k n q hk hn hq => main (k + q) k n q rfl hk hn hq, ?_⟩
  intro k n q R hk hn hR
  by_cases hq : (k - 1) * (n - 1) + 1 ≤ q
  · have := main (k + q) k n q rfl hk hn hq; omega
  · have := hout k n q
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hq
    have e : (k' + 1) * (n' + 1) = k' * n' + k' + n' + 1 := by ring
    omega

theorem prop_A_5 : Prop_A_5 := by
  intro brG brS hG h1 hout hsub
  have main : ∀ s k n q, k + q = s → 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q →
      q + k + n - 1 ≤ brS k n q := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro k n q hs hk hn hq
      rcases eq_or_lt_of_le hk with rfl | hk2
      · have := h1 n q; omega
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hq ⊢
        have e1 : (k' + 2 - 1) * n' = k' * n' + n' := by
          rw [show k' + 2 - 1 = k' + 1 by omega]; ring
        rw [e1] at hq
        have hq1 : 1 ≤ q := by omega
        have hstep := hsub (k' + 2) (n' + 1) q (by omega) hq1
        have b0 : q + (k' + 2) + (n' + 1) - 1 ≤ brG (k' + 2) (n' + 1) q :=
          hG (k' + 2) (n' + 1) q (by omega) (by omega) (by rw [Nat.add_sub_cancel, e1]; exact hq)
        have b1 : q + (k' + 1) + (n' + 1) - 1 ≤ brS (k' + 2 - 1) (n' + 1) q := by
          have := ih (k' + 1 + q) (by omega) (k' + 1) (n' + 1) q rfl (by omega) (by omega)
            (by rw [show k' + 1 - 1 = k' by omega, Nat.add_sub_cancel]; nlinarith)
          simpa [show k' + 2 - 1 = k' + 1 by omega] using this
        have b2 : q + (k' + 2) + (n' + 1) - 2 ≤ brS (k' + 2) (n' + 1) (q - 1) := by
          by_cases hq2 : k' * n' + n' + 1 ≤ q - 1
          · have := ih (k' + 2 + (q - 1)) (by omega) (k' + 2) (n' + 1) (q - 1) rfl (by omega)
              (by omega) (by rw [Nat.add_sub_cancel, e1]; exact hq2)
            omega
          · have hqe : q - 1 = k' * n' + n' := by omega
            have := hout (k' + 2) (n' + 1) (q - 1)
            have e2 : (k' + 2) * (n' + 1) = k' * n' + n' + 1 + (k' + 2) + (n' + 1) - 2 := by
              ring_nf; omega
            omega
        omega
  refine ⟨fun k n q hk hn hq => main (k + q) k n q rfl hk hn hq, ?_⟩
  intro k n q R hk hn hR
  by_cases hq : (k - 1) * (n - 1) + 1 ≤ q
  · have := main (k + q) k n q rfl hk hn hq; omega
  · have := hout k n q
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hq
    have e : (k' + 1) * (n' + 1) = k' * n' + k' + n' + 1 := by ring
    omega

theorem remark_A_6 : Remark_A_6 := by
  intro brG brS hG h1 hout hsub
  have main : ∀ s k n q, k + q = s → 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q →
      q + k + n ≤ brS k n q := by
    intro s
    induction s using Nat.strong_induction_on with
    | _ s ih =>
      intro k n q hs hk hn hq
      rcases eq_or_lt_of_le hk with rfl | hk2
      · have := h1 n q hn (by omega); omega
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
        obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel] at hq ⊢
        have e1 : (k' + 2 - 1) * n' = k' * n' + n' := by
          rw [show k' + 2 - 1 = k' + 1 by omega]; ring
        rw [e1] at hq
        have hq1 : 1 ≤ q := by omega
        have hstep := hsub (k' + 2) (n' + 1) q (by omega) hq1
        have b0 : q + (k' + 2) + (n' + 1) - 1 ≤ brG (k' + 2) (n' + 1) q :=
          hG (k' + 2) (n' + 1) q (by omega) (by omega) (by rw [Nat.add_sub_cancel, e1]; exact hq)
        have b1 : q + (k' + 1) + (n' + 1) ≤ brS (k' + 2 - 1) (n' + 1) q := by
          have := ih (k' + 1 + q) (by omega) (k' + 1) (n' + 1) q rfl (by omega) (by omega)
            (by rw [show k' + 1 - 1 = k' by omega, Nat.add_sub_cancel]; nlinarith)
          simpa [show k' + 2 - 1 = k' + 1 by omega] using this
        have b2 : q + (k' + 2) + (n' + 1) - 1 ≤ brS (k' + 2) (n' + 1) (q - 1) := by
          by_cases hq2 : k' * n' + n' + 1 ≤ q - 1
          · have := ih (k' + 2 + (q - 1)) (by omega) (k' + 2) (n' + 1) (q - 1) rfl (by omega)
              (by omega) (by rw [Nat.add_sub_cancel, e1]; exact hq2)
            omega
          · have hqe : q - 1 = k' * n' + n' := by omega
            have := hout (k' + 2) (n' + 1) (q - 1)
            have e2 : (k' + 2) * (n' + 1) = k' * n' + n' + (k' + 2) + (n' + 1) - 1 := by
              ring_nf; omega
            omega
        omega
  refine ⟨fun k n q hk hn hq => main (k + q) k n q rfl hk hn hq, ?_⟩
  intro k n q R hk hn hq hR
  have := main (k + q) k n q rfl hk hn hq
  omega

theorem remark_A_7 : Remark_A_7 := by
  intro brG brS hG hout hsub hmono h222 h233 h235 h223
  have hmono' : ∀ k n a b, a ≤ b → brS k n a ≤ brS k n b := by
    intro k n a b hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b _ ih => exact ih.trans (hmono k n b)
  have h335 : 11 ≤ brS 3 3 5 := by
    have hs := hsub 3 3 5 (by norm_num) (by norm_num)
    have g := hG 3 3 5 (by norm_num) (by norm_num) (by norm_num)
    have o := hout 3 3 4
    simp only [show (3 : ℕ) - 1 = 2 by rfl, show (5 : ℕ) - 1 = 4 by rfl] at hs
    omega
  have h323 : 8 ≤ brS 3 2 3 := by
    have hs := hsub 3 2 3 (by norm_num) (by norm_num)
    have g := hG 3 2 3 (by norm_num) (by norm_num) (by norm_num)
    have o := hout 3 2 2
    simp only [show (3 : ℕ) - 1 = 2 by rfl] at hs
    omega
  refine ⟨h335, h323, fun q hq => ?_, fun q hq => ⟨?_, ?_⟩, fun q hq => ?_⟩
  · have := hmono' 2 2 2 q hq; omega
  · have := hmono' 2 3 3 q hq; omega
  · have := hmono' 3 2 3 q hq; omega
  · have := hmono' 3 3 5 q hq; omega

end ThinMatrixProducts

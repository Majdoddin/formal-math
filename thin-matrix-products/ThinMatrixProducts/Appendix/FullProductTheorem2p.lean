import ThinMatrixProducts.Appendix.FullProductForest
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities
/-! # Thin full products: Theorem 2', its clean condition, the shapes asked about, the crude bound

`fp_Theorem_2p_ineq`: the two-point inequality `s^t ≥ (1 - c) + c min(s, m)` (concavity of `x^t`
on `[1, m]`, monotonicity beyond `m`), summed, with `R ≥ ρ n` and `∑ min(S, m) ≥ b n`.
`fp_Theorem_2p` composes it with Lemma 6 (`R ≥ n + (b-1) o₂ = ρ n`) and Lemma 4
(`∑ min(S, m*) ≥ b n`). `fp_Theorem_2p_clean`: if `m ≤ b`, the chord slope from `1` is decreasing,
so `c ≥ (b^t - 1)/(b - 1)` and `1 + (b - 1) c ≥ b^t`; otherwise weighted AM-GM as in Theorem 2.
`fpCleanNat` is the clean condition for `m* = n/d` raised to the power `d`. -/
namespace ThinMatrixProducts

open Finset

section FullProductTheorem2p

/-- The chord bound for real `m > 1`: `s^t ≥ (1 - c) + c min(s, m)` for `s ≥ 1`, `t ∈ [0,1]`. -/
lemma fp_chord' {m s t : ℝ} (hm : 1 < m) (hs : 1 ≤ s) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - fpC m t) + fpC m t * min s m ≤ s ^ t := by
  unfold fpC
  have hk1 : 0 < m - 1 := by linarith
  rcases le_total s m with hsk | hks
  · rw [min_eq_left hsk]
    have hconc := (Real.concaveOn_rpow ht0 ht1).2 (show (1 : ℝ) ∈ Set.Ici 0 by simp)
      (show m ∈ Set.Ici 0 by simp only [Set.mem_Ici]; linarith)
      (div_nonneg (by linarith : (0 : ℝ) ≤ m - s) hk1.le)
      (div_nonneg (by linarith : (0 : ℝ) ≤ s - 1) hk1.le) (by field_simp; ring)
    have hpt : (m - s) / (m - 1) * 1 + (s - 1) / (m - 1) * m = s := by
      field_simp; ring
    simp only [smul_eq_mul] at hconc
    rw [hpt, Real.one_rpow] at hconc
    calc (1 - (m ^ t - 1) / (m - 1)) + (m ^ t - 1) / (m - 1) * s
        = (m - s) / (m - 1) * 1 + (s - 1) / (m - 1) * m ^ t := by field_simp; ring
      _ ≤ s ^ t := hconc
  · rw [min_eq_right hks]
    calc (1 - (m ^ t - 1) / (m - 1)) + (m ^ t - 1) / (m - 1) * m = m ^ t := by
          field_simp; ring
      _ ≤ s ^ t := Real.rpow_le_rpow (by linarith) hks ht0

lemma fpC_nonneg {m t : ℝ} (hm : 1 < m) (ht0 : 0 ≤ t) : 0 ≤ fpC m t :=
  div_nonneg (by linarith [Real.one_le_rpow hm.le ht0]) (by linarith)

lemma fpC_le_one {m t : ℝ} (hm : 1 < m) (ht1 : t ≤ 1) : fpC m t ≤ 1 := by
  unfold fpC
  rw [div_le_one (by linarith)]
  have : m ^ t ≤ m := by simpa using Real.rpow_le_rpow_of_exponent_le hm.le ht1
  linarith

theorem fp_Theorem_2p_ineq : FP_Theorem_2p_ineq := by
  intro n R S b m ρ hm hS hR hsum t ht0 ht1 hcond
  have hc0 := fpC_nonneg hm ht0
  have hc1 := fpC_le_one hm ht1
  set c := fpC m t
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n : ℝ) * b ^ (t / 2) ≤ n * ((1 - c) * ρ + c * b) := mul_le_mul_of_nonneg_left hcond hn0
    _ = (1 - c) * (ρ * n) + c * (b * n) := by ring
    _ ≤ (1 - c) * R + c * ∑ l, min ((S l : ℕ) : ℝ) m :=
        add_le_add (mul_le_mul_of_nonneg_left hR (by linarith))
          (mul_le_mul_of_nonneg_left hsum hc0)
    _ = ∑ l, ((1 - c) + c * min ((S l : ℕ) : ℝ) m) := by
        rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sum]
        ring
    _ ≤ ∑ l, ((S l : ℕ) : ℝ) ^ t :=
        sum_le_sum fun l _ => fp_chord' hm (by exact_mod_cast hS l) ht0 ht1

lemma fpMstar_gt_one {o₁ o₂ : ℕ} (h₁ : 2 ≤ o₁) (h₂ : 2 ≤ o₂) : 1 < fpMstar o₁ o₂ := by
  unfold fpMstar
  have h₁' : (2 : ℝ) ≤ o₁ := by exact_mod_cast h₁
  have h₂' : (2 : ℝ) ≤ o₂ := by exact_mod_cast h₂
  rw [one_lt_div (by linarith)]
  nlinarith

open scoped Classical in
theorem fp_Theorem_2p : FP_Theorem_2p := by
  intro K _ o₁ b o₂ R u v w hd hb hbo hoo t ht0 ht1 hcond
  set G : Finset (Fin R) := univ.filter (fun l => w l ≠ 0) with hG
  set e : G ≃ Fin G.card := G.equivFin
  set S' : Fin G.card → ℕ := fun i => (outSupp (w (e.symm i))).card
  have hreindex : ∀ f : Fin R → ℝ, ∑ i, f (e.symm i : Fin R) = ∑ l ∈ G, f l := by
    intro f
    rw [← Finset.sum_coe_sort G f]
    exact Equiv.sum_comp e.symm (fun l : G => f l)
  have h₁ : 2 ≤ o₁ := by omega
  have h₂ : 2 ≤ o₂ := by omega
  have hm := fpMstar_gt_one h₁ h₂
  have hS : ∀ i, 1 ≤ S' i := by
    intro i
    have hi := (e.symm i).2
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨z, hz⟩ := Function.ne_iff.1 hi
    exact Finset.card_pos.2 ⟨z, by simpa [outSupp] using hz⟩
  -- Lemma 6: `|G| ≥ n + (b - 1) o₂ = ρ n`
  have h6 := fp_Lemma_6 K o₁ b o₂ R u v w hd (by omega) hb (by omega)
  rw [max_eq_right hoo] at h6
  have hR : (1 + ((b : ℝ) - 1) / o₁) * ((o₁ * o₂ : ℕ) : ℝ) ≤ (G.card : ℕ) := by
    have h6' : ((o₁ * o₂ + (b - 1) * o₂ : ℕ) : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast h6
    have ho₁ : (0 : ℝ) < o₁ := by exact_mod_cast (by omega : 0 < o₁)
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hb, Nat.cast_one] at h6'
    rw [Nat.cast_mul]
    calc (1 + ((b : ℝ) - 1) / o₁) * ((o₁ : ℝ) * o₂) = o₁ * o₂ + (b - 1) * o₂ := by
          field_simp
      _ ≤ _ := h6'
  -- Lemma 4 averaged, over the terms of `G`
  have hsum : (b : ℝ) * ((o₁ * o₂ : ℕ) : ℝ) ≤ ∑ i, min ((S' i : ℕ) : ℝ) (fpMstar o₁ o₂) := by
    have h4 := fp_Lemma_4_avg K o₁ b o₂ R u v w hd
    have h1 : ∑ l, min ((outSupp (w l)).card : ℝ) (fpMstar o₁ o₂)
        = ∑ l ∈ G, min ((outSupp (w l)).card : ℝ) (fpMstar o₁ o₂) := by
      refine (Finset.sum_subset (Finset.subset_univ G) fun l _ hl => ?_).symm
      simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hl
      have h0 : outSupp (w l) = ∅ := by ext z; simp [outSupp, hl]
      rw [h0, Finset.card_empty, Nat.cast_zero]
      exact min_eq_left (by linarith)
    rw [Nat.cast_mul]
    calc _ ≤ _ := h4
      _ = _ := h1
      _ = _ := (hreindex (fun l => min ((outSupp (w l)).card : ℝ) (fpMstar o₁ o₂))).symm
  have := fp_Theorem_2p_ineq (o₁ * o₂) G.card S' b (fpMstar o₁ o₂) (1 + ((b : ℝ) - 1) / o₁) hm hS
    hR hsum t ht0 ht1 hcond
  calc ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2) ≤ ∑ i, ((S' i : ℕ) : ℝ) ^ t := this
    _ = _ := hreindex (fun l => ((outSupp (w l)).card : ℝ) ^ t)

theorem fp_Theorem_2p_clean : FP_Theorem_2p_clean := by
  intro b m ρ hb hm hρ hcond t ht0 ht1
  have hc0 := fpC_nonneg hm ht0
  have hc1 := fpC_le_one hm ht1
  -- it suffices to show `1 + (b - 1) c ≥ b^{t/2}`
  suffices h : b ^ (t / 2) ≤ 1 + (b - 1) * fpC m t by
    calc b ^ (t / 2) ≤ 1 + (b - 1) * fpC m t := h
      _ ≤ (1 - fpC m t) * ρ + fpC m t * b := by nlinarith
  have hbt : b ^ (t / 2) ≤ b ^ t := Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  rcases eq_or_lt_of_le hb with hb1 | hb1
  · subst hb1; simp
  by_cases hmb : m ≤ b
  · -- `c ≥ (b^t - 1)/(b - 1)`, from the chord bound for `b` at `s = m`
    have hch := fp_chord' hb1 hm.le ht0 ht1
    rw [min_eq_left hmb] at hch
    have hcb : fpC b t ≤ fpC m t := by
      unfold fpC at hch ⊢
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    have : b ^ t = 1 + (b - 1) * fpC b t := by
      unfold fpC; field_simp; ring
    nlinarith
  · push Not at hmb
    have hcond' := hcond.resolve_left (not_le.2 hmb)
    have hm1 : 0 < m - 1 := by linarith
    set lam : ℝ := (b - 1) / (m - 1) with hlam
    have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hm1.le
    have hlam1 : lam ≤ 1 := (div_le_one hm1).2 (by linarith)
    have hamgm : m ^ (t * lam) ≤ 1 + (b - 1) * fpC m t := by
      have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := 1 - lam) (w₂ := lam)
        (p₁ := 1) (p₂ := m ^ t) (by linarith) hlam0 zero_le_one
        (Real.rpow_nonneg (by linarith) _) (by ring)
      rw [Real.one_rpow, one_mul, ← Real.rpow_mul (by linarith)] at h
      calc m ^ (t * lam) ≤ (1 - lam) * 1 + lam * m ^ t := h
        _ = 1 + (b - 1) * fpC m t := by rw [hlam]; unfold fpC; field_simp; ring
    have hlog : (m - 1) * Real.log b ≤ 2 * (b - 1) * Real.log m := by
      have h2 := Real.log_le_log (Real.rpow_pos_of_pos (by linarith) _) hcond'
      rw [Real.log_rpow (by linarith), Real.log_rpow (by linarith)] at h2
      linarith
    have hbm : b ^ (t / 2) ≤ m ^ (t * lam) := by
      rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith)]
      apply Real.exp_le_exp.2
      have e : Real.log m * (t * lam) = t * (2 * (b - 1) * Real.log m) / (2 * (m - 1)) := by
        rw [hlam]; field_simp
      rw [e, le_div_iff₀ (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left hlog ht0]
    linarith

/-- The integer form of the clean condition implies the real one for `m* = n/d`. -/
lemma fp_cleanNat_real {o₁ b o₂ : ℕ} (hb : 1 ≤ b) (h₁ : 2 ≤ o₁) (h₂ : 2 ≤ o₂)
    (h : fpCleanNat o₁ b o₂) :
    fpMstar o₁ o₂ ≤ b ∨ (b : ℝ) ^ (fpMstar o₁ o₂ - 1) ≤ fpMstar o₁ o₂ ^ (2 * ((b : ℝ) - 1)) := by
  set d := o₁ + o₂ - 1 with hd
  have hdpos : 0 < d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hdR' : ((o₁ : ℝ) + o₂ - 1) = d := by
    rw [hd, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hm : fpMstar o₁ o₂ = ((o₁ * o₂ : ℕ) : ℝ) / d := by
    unfold fpMstar; rw [hdR', Nat.cast_mul]
  have hdn : d ≤ o₁ * o₂ := by
    rw [hd, Nat.sub_le_iff_le_add]; nlinarith
  rcases h with h | h
  · left
    rw [hm, div_le_iff₀ hdR]
    exact_mod_cast h
  · right
    have hmpos : 0 < fpMstar o₁ o₂ := lt_trans one_pos (fpMstar_gt_one h₁ h₂)
    have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
    have hX : ((b : ℝ) ^ (fpMstar o₁ o₂ - 1)) ^ d = (b : ℝ) ^ (o₁ * o₂ - d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hbpos.le, ← Real.rpow_natCast]
      congr 1
      rw [hm, Nat.cast_sub hdn]
      field_simp
    have hY : (fpMstar o₁ o₂ ^ (2 * ((b : ℝ) - 1))) ^ d
        = ((o₁ * o₂ : ℕ) : ℝ) ^ (2 * (b - 1) * d) / (d : ℝ) ^ (2 * (b - 1) * d) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le,
        show 2 * ((b : ℝ) - 1) * d = ((2 * (b - 1) * d : ℕ) : ℝ) by
          rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hb]; push_cast; ring,
        Real.rpow_natCast, hm, div_pow]
    have hXY : ((b : ℝ) ^ (fpMstar o₁ o₂ - 1)) ^ d
        ≤ (fpMstar o₁ o₂ ^ (2 * ((b : ℝ) - 1))) ^ d := by
      rw [hX, hY, le_div_iff₀ (pow_pos hdR _)]
      exact_mod_cast h
    exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg hbpos.le _) (Real.rpow_nonneg hmpos.le _)
      hdpos.ne').1 hXY

theorem fp_Theorem_2p_nat : FP_Theorem_2p_nat := by
  intro K _ o₁ b o₂ R u v w hd hb hbo hoo hclean t ht0 ht1
  have h₁ : 2 ≤ o₁ := by omega
  have h₂ : 2 ≤ o₂ := by omega
  refine fp_Theorem_2p K o₁ b o₂ R u v w hd hb hbo hoo t ht0 ht1 ?_
  refine fp_Theorem_2p_clean b (fpMstar o₁ o₂) _ (by exact_mod_cast hb) (fpMstar_gt_one h₁ h₂)
    ?_ (fp_cleanNat_real hb h₁ h₂ hclean) t ht0 ht1
  have : (0 : ℝ) ≤ ((b : ℝ) - 1) / o₁ :=
    div_nonneg (by have : (1 : ℝ) ≤ b := by exact_mod_cast hb
                   linarith) (Nat.cast_nonneg _)
  linarith

theorem fp_clean_squares : FP_clean_squares := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · refine ⟨fun k h1 h2 => ?_, by unfold fpCleanNat; decide +kernel⟩
    simp only at h1 h2
    interval_cases k <;> unfold fpCleanNat <;> decide +kernel

theorem fp_open_shapes : FP_open_shapes := by
  intro K _ o₁ b o₂ R hmem u v w hd t ht0 ht1
  simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
  exact fp_Theorem_2p_nat K _ _ _ R u v w hd (by norm_num) (by norm_num) le_rfl
    (by unfold fpCleanNat; decide +kernel) t ht0 ht1

open scoped Classical in
theorem fp_value_crude : FP_value_crude := by
  intro K _ o₁ b o₂ R u v w hd hb t ht0 ht1
  set G : Finset (Fin R) := univ.filter (fun l => w l ≠ 0) with hG
  set sumS := ∑ l ∈ G, ((outSupp (w l)).card : ℝ) ^ t
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hbR
  have hterm : ∀ l ∈ G, (1 : ℝ) ≤ ((outSupp (w l)).card : ℝ) ^ t := by
    intro l hl
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hl
    obtain ⟨z, hz⟩ := Function.ne_iff.1 hl
    have : (1 : ℝ) ≤ (outSupp (w l)).card := by
      exact_mod_cast Finset.card_pos.2 ⟨z, by simpa [outSupp] using hz⟩
    exact Real.one_le_rpow this ht0
  have hsumS : (G.card : ℝ) ≤ sumS := by
    calc (G.card : ℝ) = ∑ l ∈ G, (1 : ℝ) := by simp
      _ ≤ sumS := Finset.sum_le_sum hterm
  have hn : o₁ * o₂ ≤ G.card := fp_rank_ge_n K o₁ b o₂ R u v w hd hb
  have hlogS : Real.log ((o₁ : ℝ) * o₂) ≤ Real.log sumS := by
    rcases Nat.eq_zero_or_pos (o₁ * o₂) with h0 | hpos
    · have : ((o₁ : ℝ) * o₂) = 0 := by exact_mod_cast h0
      rw [this, Real.log_zero]
      rcases G.eq_empty_or_nonempty with hGe | hGne
      · simp [sumS, hGe]
      · exact Real.log_nonneg (le_trans (by exact_mod_cast Finset.card_pos.2 hGne) hsumS)
    · have hposR : (0 : ℝ) < (o₁ : ℝ) * o₂ := by exact_mod_cast hpos
      refine Real.log_le_log hposR (le_trans ?_ hsumS)
      exact_mod_cast hn
  nlinarith

end FullProductTheorem2p

end ThinMatrixProducts

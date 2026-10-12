import ThinMatrixProducts.Appendix.FullProductTheorem2p
import ThinMatrixProducts.Appendix.FullProductLeaves
import ThinMatrixProducts.Appendix.FullProductTypes
import ThinMatrixProducts.Appendix.FullProductCompose
/-! # Thin full products in the paper (Appendix A.9 of `main.tex` at 67e1090)

Proposition A.17 in the paper's form (any `o₁, o₂ ≥ 2`, `r = 1 + (b-1)/κ`), its last sentence, and
the mathematical part of Theorem A.14 (the tiling, `ρ ≥ b^{-L/2}`, `V ≥ (N²/n^L) V_L`, and the
assembly with Lemma A.12 and Lemma A.13). Lemma A.13 is in `FullProductTypes.lean`. -/
namespace ThinMatrixProducts

open Finset Filter Topology

section FullProductPaper

open scoped Classical in
/-- Proposition A.17 with the per-`t` condition (iii). -/
lemma fp_A17_core {K : Type} [Field K] {o₁ b o₂ R : ℕ} {u : Fin R → Fin o₁ × Fin b → K}
    {v : Fin R → Fin b × Fin o₂ → K} {w : Fin R → Fin o₁ × Fin o₂ → K} (hd : IsMMDecomp u v w)
    (h₁ : 2 ≤ o₁) (h₂ : 2 ≤ o₂) (hb : 1 ≤ b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hcond : (b : ℝ) ^ (t / 2) ≤ (1 - fpC (fpMstar o₁ o₂) t) * (1 + ((b : ℝ) - 1) / (min o₁ o₂ : ℕ))
          + fpC (fpMstar o₁ o₂) t * b) :
    ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2)
      ≤ ∑ l ∈ univ.filter (fun l => w l ≠ 0), ((outSupp (w l)).card : ℝ) ^ t := by
  classical
  set G : Finset (Fin R) := univ.filter (fun l => w l ≠ 0) with hG
  set e : G ≃ Fin G.card := G.equivFin
  set S' : Fin G.card → ℕ := fun i => (outSupp (w (e.symm i))).card
  have hreindex : ∀ f : Fin R → ℝ, ∑ i, f (e.symm i : Fin R) = ∑ l ∈ G, f l := by
    intro f
    rw [← Finset.sum_coe_sort G f]
    exact Equiv.sum_comp e.symm (fun l : G => f l)
  have hm := fpMstar_gt_one h₁ h₂
  have hS : ∀ i, 1 ≤ S' i := by
    intro i
    have hi := (e.symm i).2
    simp only [hG, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨z, hz⟩ := Function.ne_iff.1 hi
    exact Finset.card_pos.2 ⟨z, by simpa [outSupp] using hz⟩
  have h6 := fp_Lemma_6 K o₁ b o₂ R u v w hd (by omega) hb (by omega)
  have hR : (1 + ((b : ℝ) - 1) / (min o₁ o₂ : ℕ)) * ((o₁ * o₂ : ℕ) : ℝ) ≤ (G.card : ℕ) := by
    have h6' : ((o₁ * o₂ + (b - 1) * max o₁ o₂ : ℕ) : ℝ) ≤ (G.card : ℝ) := by exact_mod_cast h6
    push_cast [Nat.cast_sub hb] at h6' ⊢
    have hκ : (0 : ℝ) < min (o₁ : ℝ) o₂ := lt_min (by positivity) (by positivity)
    have hmm : (o₁ : ℝ) * o₂ = min (o₁ : ℝ) o₂ * max (o₁ : ℝ) o₂ := (min_mul_max _ _).symm
    rw [hmm] at h6' ⊢
    calc (1 + ((b : ℝ) - 1) / min (o₁ : ℝ) o₂) * (min (o₁ : ℝ) o₂ * max (o₁ : ℝ) o₂)
        = min (o₁ : ℝ) o₂ * max (o₁ : ℝ) o₂ + (b - 1) * max (o₁ : ℝ) o₂ := by
          field_simp
      _ ≤ _ := h6'
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
  have := fp_Theorem_2p_ineq (o₁ * o₂) G.card S' b (fpMstar o₁ o₂)
    (1 + ((b : ℝ) - 1) / (min o₁ o₂ : ℕ)) hm hS hR hsum t ht0 ht1 hcond
  calc ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2) ≤ ∑ i, ((S' i : ℕ) : ℝ) ^ t := this
    _ = _ := hreindex (fun l => ((outSupp (w l)).card : ℝ) ^ t)

theorem fp_Prop_A_17 : FP_Prop_A_17 := by
  intro K _ o₁ b o₂ R u v w hd h₁ h₂ hb hcase t ht0 ht1
  refine fp_A17_core hd h₁ h₂ hb ht0 ht1 ?_
  have hr : (1 : ℝ) ≤ 1 + ((b : ℝ) - 1) / (min o₁ o₂ : ℕ) := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    have : (0 : ℝ) ≤ ((b : ℝ) - 1) / (min o₁ o₂ : ℕ) := div_nonneg (by linarith) (Nat.cast_nonneg _)
    linarith
  rcases hcase with h | h | h
  · exact fp_Theorem_2p_clean b _ _ (by exact_mod_cast hb) (fpMstar_gt_one h₁ h₂) hr (Or.inl h)
      t ht0 ht1
  · exact fp_Theorem_2p_clean b _ _ (by exact_mod_cast hb) (fpMstar_gt_one h₁ h₂) hr (Or.inr h)
      t ht0 ht1
  · exact h t ht0 ht1

/-- `f ≤ κ`. -/
lemma fpMstar_le_min {o₁ o₂ : ℕ} (h₁ : 1 ≤ o₁) (h₂ : 1 ≤ o₂) :
    fpMstar o₁ o₂ ≤ ((min o₁ o₂ : ℕ) : ℝ) := by
  unfold fpMstar
  have h₁' : (1 : ℝ) ≤ o₁ := by exact_mod_cast h₁
  have h₂' : (1 : ℝ) ≤ o₂ := by exact_mod_cast h₂
  rw [div_le_iff₀ (by linarith)]
  rcases le_total o₁ o₂ with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; nlinarith

theorem fp_Prop_A_17_kappa : FP_Prop_A_17_kappa := by
  intro o₁ b o₂ h₁ h₂ hb
  have hfκ := fpMstar_le_min (o₁ := o₁) (o₂ := o₂) (by omega) (by omega)
  have hf1 := fpMstar_gt_one h₁ h₂
  refine ⟨fun h => hfκ.trans (by exact_mod_cast h), fun h => ?_⟩
  set κ := min o₁ o₂
  set f := fpMstar o₁ o₂
  have hκ2 : 2 ≤ κ := by omega
  have hκR : (2 : ℝ) ≤ κ := by exact_mod_cast hκ2
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  -- the integer condition in logarithms: `(κ-1) ln b ≤ 2(b-1) ln κ`
  have hlogκ : ((κ : ℝ) - 1) * Real.log b ≤ 2 * ((b : ℝ) - 1) * Real.log κ := by
    have h' : ((b : ℝ)) ^ (κ - 1) ≤ (κ : ℝ) ^ (2 * (b - 1)) := by exact_mod_cast h
    have h2 := Real.log_le_log (pow_pos (by linarith) _) h'
    rw [Real.log_pow, Real.log_pow] at h2
    push_cast [Nat.cast_sub (by omega : 1 ≤ κ), Nat.cast_sub hb] at h2
    linarith
  -- concavity of `log`: `ln f ≥ θ ln κ` with `f = (1-θ)·1 + θ κ`
  have hk1 : (κ : ℝ) - 1 ≠ 0 := by linarith
  set θ := (f - 1) / ((κ : ℝ) - 1)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by linarith)
  have hθ1 : θ ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have hfθ : f = (1 - θ) * 1 + θ * κ := by
    simp only [θ]; field_simp; ring
  have hlogf : θ * Real.log κ ≤ Real.log f := by
    have := (strictConcaveOn_log_Ioi.concaveOn).2 (show (1 : ℝ) ∈ Set.Ioi 0 by simp)
      (show (κ : ℝ) ∈ Set.Ioi 0 by simp only [Set.mem_Ioi]; linarith) (by linarith : 0 ≤ 1 - θ)
      hθ0 (by ring)
    simp only [smul_eq_mul, Real.log_one, mul_zero, zero_add] at this
    rw [hfθ]; exact this
  have hlog : (f - 1) * Real.log b ≤ 2 * ((b : ℝ) - 1) * Real.log f := by
    have hb0 : 0 ≤ (b : ℝ) - 1 := by linarith
    have e1 : f - 1 = θ * ((κ : ℝ) - 1) := by simp only [θ]; field_simp
    calc (f - 1) * Real.log b = θ * (((κ : ℝ) - 1) * Real.log b) := by rw [e1]; ring
      _ ≤ θ * (2 * ((b : ℝ) - 1) * Real.log κ) := mul_le_mul_of_nonneg_left hlogκ hθ0
      _ = 2 * ((b : ℝ) - 1) * (θ * Real.log κ) := by ring
      _ ≤ 2 * ((b : ℝ) - 1) * Real.log f := mul_le_mul_of_nonneg_left hlogf (by linarith)
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith)]
  exact Real.exp_le_exp.2 (by linarith)

theorem fp_Thm_A_14_tiling : FP_Thm_A_14_tiling := by
  intro o₁ o₂ L N h₁ h₂
  have hN : N / o₁ ^ L * (N / o₂ ^ L) * (o₁ * o₂) ^ L = N * N := by
    rw [mul_pow]
    calc N / o₁ ^ L * (N / o₂ ^ L) * (o₁ ^ L * o₂ ^ L)
        = (N / o₁ ^ L * o₁ ^ L) * (N / o₂ ^ L * o₂ ^ L) := by ring
      _ = N * N := by rw [Nat.div_mul_cancel h₁, Nat.div_mul_cancel h₂]
  refine ⟨hN, ⟨Fintype.equivOfCardEq ?_⟩⟩
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
  rw [← hN, mul_pow]

theorem fp_Thm_A_14_rho : FP_Thm_A_14_rho := by
  intro b L N hb hN
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hD : (1 : ℝ) ≤ Real.sqrt ((b : ℝ) ^ L) := by
    rw [Real.one_le_sqrt]; exact one_le_pow₀ hbR
  have hNN : (0 : ℝ) < ((N * N : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hN hN
  refine ⟨Nat.ceil_le.2 ?_, ?_⟩
  · rw [div_le_iff₀ (by linarith)]
    nlinarith
  · calc (b : ℝ) ^ (-(L : ℝ) / 2) = ((N * N : ℕ) : ℝ) / Real.sqrt ((b : ℝ) ^ L) / (N * N : ℕ) := by
          rw [div_right_comm, div_self hNN.ne', one_div, Real.sqrt_eq_rpow,
            ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_neg (by linarith)]
          ring_nf
      _ ≤ _ := div_le_div_of_nonneg_right (Nat.le_ceil _) hNN.le

open scoped Classical in
lemma fpRunA_card {P o₁ o₂ R L : ℕ} (Z : Fin R → Finset (Fin o₁ × Fin o₂))
    (x : Fin P × (Fin L → Fin R)) : (fpRunA Z x).card = ∏ ℓ, (Z (x.2 ℓ)).card := by
  have : fpRunA Z x = (Fintype.piFinset fun ℓ => Z (x.2 ℓ)).map
      ⟨fun ω => (x.1, ω), fun ω ω' h => by simpa using h⟩ := by
    ext ⟨p, ω⟩
    simp only [fpRunA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Fintype.mem_piFinset]
    constructor
    · rintro ⟨rfl, h⟩; exact ⟨ω, h, rfl⟩
    · rintro ⟨a, h, he⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact ⟨rfl, h⟩
  rw [this, Finset.card_map, Fintype.card_piFinset]

theorem fp_Thm_A_14_V : FP_Thm_A_14_V := by
  intro P o₁ o₂ R L Z ρ β hβ hρ
  refine ⟨fpRunA_card Z, ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [fpRunA_card]
  rw [show (P : ℝ) * fpVL (fun l => (Z l).card) β L
      = ∑ _p : Fin P, fpVL (fun l => (Z l).card) β L by simp]
  refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun τ _ => ?_
  refine min_le_min le_rfl ?_
  push_cast
  rw [div_eq_mul_inv, mul_comm, ← inv_pow]
  exact mul_le_mul_of_nonneg_right hρ (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

theorem fp_Thm_A_14 : FP_Thm_A_14 := by
  classical
  intro o₁ o₂ b R Z hb hR hZ hΓ
  set S : Fin R → ℕ := fun l => (Z l).card
  have hS : ∀ l, 1 ≤ S l := fun l => Finset.card_pos.2 (hZ l)
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hβ : 0 < Real.sqrt b := Real.sqrt_pos.2 (by linarith)
  obtain ⟨-, t₀, ht0, ht1, C, hC⟩ := fp_Lemma_A_13_bounds R S (Real.sqrt b) hR hS hβ
  -- `n ≥ 1`
  obtain ⟨z₀, -⟩ := hZ ⟨0, hR⟩
  have hn : 1 ≤ o₁ * o₂ := Nat.mul_pos (Fin.pos z₀.1) (Fin.pos z₀.2)
  have hnR : (1 : ℝ) ≤ ((o₁ * o₂ : ℕ) : ℝ) := by exact_mod_cast hn
  -- `F(t₀) ≥ ln n` (this is `Γ ≥ 0`)
  have hF : Real.log ((o₁ * o₂ : ℕ) : ℝ) ≤ fpF S (Real.sqrt b) t₀ := by
    have h := hΓ t₀ ht0 ht1
    have hpos : (0 : ℝ) < ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t₀ / 2) :=
      mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
    have h2 := Real.log_le_log hpos h
    rw [Real.log_mul (by linarith) (Real.rpow_pos_of_pos (by linarith) _).ne',
      Real.log_rpow (by linarith)] at h2
    unfold fpF
    rw [Real.log_sqrt (by linarith)]
    simp only [S]
    linarith
  set δ : ℕ → ℝ := fun L => (|C| + Real.log 2) * (L : ℝ) ^ (-(1 / 2 : ℝ))
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℕ => (L : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
    have := h1.const_mul (|C| + Real.log 2)
    rw [mul_zero] at this
    exact this
  -- `V_L ≥ n^L e^{-δ_L L}`
  have hVL : ∀ L : ℕ, ((o₁ * o₂ : ℕ) : ℝ) ^ L * Real.exp (-(δ L * L)) ≤ fpVL S (Real.sqrt b) L := by
    intro L
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp [fpVL]
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hsq : Real.sqrt L = (L : ℝ) * (L : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by linarith) (by norm_num)]
      norm_num
    have hsq1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.2 hLR
    have h := hC L hL
    have hV := fp_VL_pos S hS hβ hR L
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hδL : C * Real.sqrt L + Real.log 2 ≤ δ L * L := by
      simp only [δ]
      rw [mul_assoc, mul_comm ((L : ℝ) ^ _), ← hsq]
      nlinarith [le_abs_self C, abs_nonneg C]
    rw [← Real.exp_log hV, ← Real.exp_log (pow_pos (by linarith : (0 : ℝ) < _) L),
      ← Real.exp_add, Real.log_pow]
    apply Real.exp_le_exp.2
    have : (L : ℝ) * Real.log ((o₁ * o₂ : ℕ) : ℝ) ≤ L * fpF S (Real.sqrt b) t₀ :=
      mul_le_mul_of_nonneg_left hF (by linarith)
    linarith
  refine ⟨δ, hδ, fun L N h₁ h₂ hN => ?_⟩
  obtain ⟨htile, -⟩ := fp_Thm_A_14_tiling o₁ o₂ L N h₁ h₂
  obtain ⟨hwle, hρ⟩ := fp_Thm_A_14_rho b L N hb hN
  set P := N / o₁ ^ L * (N / o₂ ^ L)
  set w := ⌈((N * N : ℕ) : ℝ) / Real.sqrt ((b : ℝ) ^ L)⌉₊
  have hcardE : Fintype.card (Fin P × (Fin L → Fin o₁ × Fin o₂)) = N * N := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
    rw [← htile]
  obtain ⟨W, hW, hlow⟩ := fp_L_exists (fpRunA (P := P) (L := L) Z) w (by rw [hcardE]; exact hwle)
  refine ⟨W, hW, le_trans ?_ hlow⟩
  rw [hcardE]
  -- `ρ ≥ (√b)^{-L}`
  have hρ' : (Real.sqrt b)⁻¹ ^ L ≤ (w : ℝ) / ((N * N : ℕ) : ℝ) := by
    refine le_trans (le_of_eq ?_) hρ
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, ← Real.rpow_mul (by linarith),
      ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    ring_nf
  have hV := (fp_Thm_A_14_V P o₁ o₂ R L Z _ _ hβ hρ').2
  have hNN : ((N * N : ℕ) : ℝ) = P * ((o₁ * o₂ : ℕ) : ℝ) ^ L := by
    rw [← htile]; push_cast; ring
  have he : 0 ≤ 1 - Real.exp (-1) := by
    have := Real.exp_le_one_iff.2 (by norm_num : (-1 : ℝ) ≤ 0); linarith
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ he
  calc ((N * N : ℕ) : ℝ) * Real.exp (-(δ L * L))
      = P * (((o₁ * o₂ : ℕ) : ℝ) ^ L * Real.exp (-(δ L * L))) := by rw [hNN]; ring
    _ ≤ P * fpVL (fun l => (Z l).card) (Real.sqrt b) L :=
        mul_le_mul_of_nonneg_left (hVL L) (Nat.cast_nonneg _)
    _ ≤ _ := hV

theorem fp_Thm_A_14_no_saving : FP_Thm_A_14_no_saving := by
  intro o₁ o₂ b R Z hb hR hZ hΓ γ hγ
  obtain ⟨δ, hδ, hW⟩ := fp_Thm_A_14 o₁ o₂ b R Z (by omega) hR hZ hΓ
  obtain ⟨z₀, -⟩ := hZ ⟨0, hR⟩
  have ho₁ : 0 < o₁ := Fin.pos z₀.1
  have ho₂ : 0 < o₂ := Fin.pos z₀.2
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hlogb : 0 < Real.log b := Real.log_pos (by linarith)
  set c := γ * Real.log b with hc
  have hcpos : 0 < c := mul_pos hγ hlogb
  have he1 : 0 < 1 - Real.exp (-1) := by
    have := Real.exp_lt_one_iff.2 (by norm_num : (-1 : ℝ) < 0); linarith
  set c₀ := -Real.log (1 - Real.exp (-1))
  -- choose `L` with `δ_L < c/2` and `L c/2 > c₀`
  have h1 : ∀ᶠ L : ℕ in atTop, δ L < c / 2 :=
    (tendsto_order.1 hδ).2 _ (by linarith)
  have h2 : ∀ᶠ L : ℕ in atTop, 2 * |c₀| / c < (L : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_gt_atTop _
  obtain ⟨L, hL1, hL2⟩ := (h1.and h2).exists
  set N := o₁ ^ L * o₂ ^ L
  have hN : 1 ≤ N := Nat.mul_pos (pow_pos ho₁ _) (pow_pos ho₂ _)
  obtain ⟨W, hWc, hWl⟩ := hW L N (dvd_mul_right _ _) (dvd_mul_left _ _) hN
  refine ⟨L, N, dvd_mul_right _ _, dvd_mul_left _ _, hN, W, hWc, lt_of_lt_of_le ?_ hWl⟩
  have hNN : (0 : ℝ) < ((N * N : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hN hN
  have hD : ((b : ℝ) ^ L) ^ γ = Real.exp (L * c) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.rpow_def_of_pos (by linarith)]
    congr 1; rw [hc]; ring
  rw [hD, div_eq_mul_inv, ← Real.exp_neg]
  have key : Real.exp (-(L * c)) < (1 - Real.exp (-1)) * Real.exp (-(δ L * L)) := by
    rw [← Real.exp_log he1, ← Real.exp_add]
    apply Real.exp_lt_exp.2
    have hLpos : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have : |c₀| * 2 < L * c := by
      have := (div_lt_iff₀ hcpos).1 hL2; linarith
    have hc0 : -Real.log (1 - Real.exp (-1)) ≤ |c₀| := le_abs_self _
    nlinarith [abs_nonneg c₀]
  calc ((N * N : ℕ) : ℝ) * Real.exp (-(L * c))
      < ((N * N : ℕ) : ℝ) * ((1 - Real.exp (-1)) * Real.exp (-(δ L * L))) :=
        mul_lt_mul_of_pos_left key hNN
    _ = _ := by ring

theorem fp_Cor_A_18 : FP_Cor_A_18 := by
  classical
  intro K _ o₁ b o₂ R hmem u v w hd hw γ hγ
  obtain ⟨-, -, hall⟩ := fp_shapes_145
  have hshape : 2 ≤ b ∧ 1 ≤ o₁ ∧ 1 ≤ o₂ := by
    rcases hmem with h | h
    · obtain ⟨h1, h2, h3, -⟩ := hall _ h; simp only at h1 h2 h3; omega
    · obtain ⟨h1, h2, h3, -⟩ := hall _ h; simp only at h1 h2 h3; omega
  obtain ⟨hb, ho₁, ho₂⟩ := hshape
  have hfilter : (univ.filter fun l => w l ≠ 0) = univ := Finset.filter_true_of_mem fun l _ => hw l
  have hR : 1 ≤ R := by
    have := fp_rank_ge_n K o₁ b o₂ R u v w hd (by omega)
    rw [hfilter, Finset.card_univ, Fintype.card_fin] at this
    exact le_trans (Nat.mul_pos ho₁ ho₂) this
  refine fp_Thm_A_14_no_saving o₁ o₂ b R (fun l => outSupp (w l)) hb hR (fun l => ?_) ?_ γ hγ
  · obtain ⟨z, hz⟩ := Function.ne_iff.1 (hw l)
    exact ⟨z, by simpa [outSupp] using hz⟩
  · intro t ht0 ht1
    have := fp_145_thin K o₁ b o₂ R hmem u v w hd t ht0 ht1
    rwa [hfilter] at this

end FullProductPaper

end ThinMatrixProducts

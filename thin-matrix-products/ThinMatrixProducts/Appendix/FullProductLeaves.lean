import Statements
/-! # Full products: the general leaf-count lemma (U), (L) -/
namespace ThinMatrixProducts

open Finset

open scoped Classical in
theorem fp_U : FP_U := by
  intro T E X _ _ A cls W α hα
  rw [card_eq_sum_card_fiberwise (f := cls) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_le_sum fun x _ => le_min ?_ ?_
  · calc #{τ ∈ fpLeaves A W | cls τ = x}
        ≤ #(W.biUnion fun e => univ.filter fun τ => cls τ = x ∧ e ∈ A τ) := by
          refine card_le_card fun τ hτ => ?_
          simp only [fpLeaves, mem_filter, mem_univ, true_and] at hτ
          obtain ⟨⟨e, he, heA⟩, hx⟩ := hτ
          exact mem_biUnion.2 ⟨e, he, by simp [hx, heA]⟩
      _ ≤ ∑ e ∈ W, #(univ.filter fun τ => cls τ = x ∧ e ∈ A τ) := card_biUnion_le
      _ ≤ ∑ _e ∈ W, α x := sum_le_sum fun e he => hα x e he
      _ = #W * α x := by simp
  · exact card_le_card fun τ hτ => by simp_all

open scoped Classical in
/-- `|Leaves(W)|` as a sum of indicators. -/
private lemma card_fpLeaves {T E : Type} [Fintype T] (A : T → Finset E) (W : Finset E) :
    (fpLeaves A W).card = ∑ τ, if Disjoint W (A τ) then 0 else 1 := by
  rw [fpLeaves, card_filter]
  refine sum_congr rfl fun τ _ => ?_
  by_cases h : Disjoint W (A τ)
  · rw [if_pos h, if_neg]; exact not_disjoint_iff.2.mt (not_not.2 h)
  · rw [if_neg h, if_pos (not_disjoint_iff.1 h)]

open scoped Classical in
private lemma filter_disjoint_eq {E : Type} [Fintype E] (B : Finset E) :
    (univ.filter fun W : Finset E => Disjoint W B) = Bᶜ.powerset := by
  ext W; simp [subset_compl_iff_disjoint_right]

theorem fp_L_bernoulli : FP_L_bernoulli := by
  classical
  intro T E _ _ A p
  have key : ∀ B : Finset E,
      ∑ W : Finset E, p ^ W.card * (1 - p) ^ (Fintype.card E - W.card) *
        (if Disjoint W B then (0 : ℝ) else 1) = 1 - (1 - p) ^ B.card := by
    intro B
    have h1 : ∑ W : Finset E, p ^ W.card * (1 - p) ^ (Fintype.card E - W.card) = 1 := by
      rw [Fintype.sum_pow_mul_eq_add_pow]; simp
    have h2 : ∑ W ∈ Bᶜ.powerset, p ^ W.card * (1 - p) ^ (Fintype.card E - W.card)
        = (1 - p) ^ B.card := by
      have hB := card_le_univ B
      calc ∑ W ∈ Bᶜ.powerset, p ^ W.card * (1 - p) ^ (Fintype.card E - W.card)
          = ∑ W ∈ Bᶜ.powerset, (1 - p) ^ B.card * (p ^ W.card * (1 - p) ^ (#Bᶜ - W.card)) := by
            refine sum_congr rfl fun W hW => ?_
            have hW' : #W ≤ #Bᶜ := card_le_card (mem_powerset.1 hW)
            rw [card_compl] at hW' ⊢
            rw [show Fintype.card E - #W = #B + (Fintype.card E - #B - #W) by omega, pow_add]
            ring
        _ = (1 - p) ^ B.card := by rw [← mul_sum, sum_pow_mul_eq_add_pow]; simp
    have h3 : ∑ W : Finset E, p ^ W.card * (1 - p) ^ (Fintype.card E - W.card) *
        (if Disjoint W B then (0 : ℝ) else 1)
        = ∑ W : Finset E, p ^ W.card * (1 - p) ^ (Fintype.card E - W.card)
          - ∑ W ∈ univ.filter (fun W : Finset E => Disjoint W B),
              p ^ W.card * (1 - p) ^ (Fintype.card E - W.card) := by
      rw [sum_filter, ← sum_sub_distrib]
      refine sum_congr rfl fun W _ => ?_
      split_ifs <;> ring
    rw [h3, h1, filter_disjoint_eq, h2]
  simp_rw [card_fpLeaves, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun τ _ => key (A τ)

theorem fp_L_uniform : FP_L_uniform := by
  classical
  intro T E _ _ A w
  simp_rw [card_fpLeaves]
  rw [sum_comm]
  refine sum_congr rfl fun τ _ => ?_
  have hD : (powersetCard w univ).filter (fun W => Disjoint W (A τ))
      = powersetCard w (A τ)ᶜ := by
    ext W; simp [mem_powersetCard, subset_compl_iff_disjoint_right, and_comm]
  have hsplit := card_filter_add_card_filter_not (s := powersetCard w (univ : Finset E))
    (fun W => Disjoint W (A τ))
  rw [hD, card_powersetCard, card_powersetCard, card_compl, card_univ] at hsplit
  rw [← hsplit, add_tsub_cancel_left, card_filter]
  exact sum_congr rfl fun W _ => by split_ifs <;> simp_all

theorem fp_choose_ratio : FP_choose_ratio := by
  intro n s w hs
  by_cases hw : w ≤ n
  · have hq : 0 ≤ 1 - (w : ℝ) / n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [sub_nonneg, div_le_one (by exact_mod_cast hn)]; exact_mod_cast hw
    induction s with
    | zero => simp
    | succ s ih =>
      have ih := ih (by omega)
      have step : (((n - (s + 1)).choose w : ℕ) : ℝ) ≤ (n - s).choose w * (1 - (w : ℝ) / n) := by
        obtain ⟨k, hk, hk'⟩ : ∃ k, n - (s + 1) = k ∧ n - s = k + 1 := ⟨_, rfl, by omega⟩
        rw [hk, hk']
        by_cases hwk : w ≤ k + 1
        · have e : ((k.choose w : ℕ) : ℝ) * (k + 1) = (k + 1).choose w * ((k + 1 : ℝ) - w) := by
            have h := congrArg (Nat.cast (R := ℝ)) (Nat.choose_mul_succ_eq k w)
            push_cast [Nat.cast_sub hwk] at h
            exact h
          have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
          have hkn : (k + 1 : ℝ) ≤ n := by exact_mod_cast (show k + 1 ≤ n by omega)
          have h1 : (k + 1 : ℝ) - w ≤ (k + 1) * (1 - w / n) := by
            have : (k + 1 : ℝ) * (w / n) ≤ w := by
              rw [mul_div_assoc', div_le_iff₀ hn]
              exact mul_le_mul_of_nonneg_right hkn (Nat.cast_nonneg w) |>.trans_eq (mul_comm _ _)
            nlinarith
          have hc : (0 : ℝ) ≤ (k + 1).choose w := Nat.cast_nonneg _
          refine le_of_mul_le_mul_right (a := (k + 1 : ℝ)) ?_ (by positivity)
          rw [e]
          nlinarith [mul_le_mul_of_nonneg_left h1 hc]
        · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero]
          exact mul_nonneg (Nat.cast_nonneg _) hq
      calc (((n - (s + 1)).choose w : ℕ) : ℝ) ≤ (n - s).choose w * (1 - (w : ℝ) / n) := step
        _ ≤ n.choose w * (1 - (w : ℝ) / n) ^ s * (1 - (w : ℝ) / n) :=
          mul_le_mul_of_nonneg_right ih hq
        _ = n.choose w * (1 - (w : ℝ) / n) ^ (s + 1) := by ring
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- `1 - e^{-x} ≥ (1 - 1/e) x` on `[0, 1]`, by convexity of `exp`. -/
private lemma one_sub_exp_neg_ge (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    (1 - Real.exp (-1)) * x ≤ 1 - Real.exp (-x) := by
  have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-1)) (sub_nonneg.2 h1) h0
    (sub_add_cancel 1 x)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, mul_neg] at this
  linarith

theorem fp_one_sub_pow : FP_one_sub_pow := by
  intro p s hp0 hp1
  have hb : 0 ≤ (1 - p) ^ s := pow_nonneg (by linarith) s
  refine ⟨?_, le_min (by linarith) ?_⟩
  · have he : (1 - p) ^ s ≤ Real.exp (-(p * s)) := by
      rw [show -(p * s) = s * (-p) by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg p) s
    have hps : 0 ≤ p * s := by positivity
    rcases le_total (p * s) 1 with h | h
    · rw [min_eq_right h]
      linarith [one_sub_exp_neg_ge _ hps h]
    · rw [min_eq_left h, mul_one]
      linarith [Real.exp_le_exp.2 (show -(p * s) ≤ -1 by linarith)]
  · have := one_add_mul_le_pow (a := -p) (by linarith) s
    rw [← sub_eq_add_neg] at this
    linarith

/-- The union bound in numbers: the `(w+1)`-subsets of an `n`-set meeting a given `s`-subset number
at most `s binom(n-1, w)`. -/
private lemma choose_sub_le (n w s : ℕ) (hs : s ≤ n) :
    n.choose (w + 1) ≤ (n - s).choose (w + 1) + s * (n - 1).choose w := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ih := ih (by omega)
    have e : (n - s).choose (w + 1) = (n - (s + 1)).choose (w + 1) + (n - (s + 1)).choose w := by
      rw [show n - s = n - (s + 1) + 1 by omega, Nat.choose_succ_succ', add_comm]
    have hle : (n - (s + 1)).choose w ≤ (n - 1).choose w := Nat.choose_le_choose _ (by omega)
    rw [e] at ih
    nlinarith

theorem fp_L_average : FP_L_average := by
  classical
  intro T E _ _ A w hw
  set n := Fintype.card E
  have hC : (0 : ℝ) < n.choose w := by exact_mod_cast Nat.choose_pos hw
  have havg : (∑ W ∈ (univ : Finset E).powersetCard w, ((fpLeaves A W).card : ℝ)) / n.choose w
      = ∑ τ, (1 - ((n - (A τ).card).choose w : ℝ) / n.choose w) := by
    rw [← Nat.cast_sum, fp_L_uniform, Nat.cast_sum, sum_div]
    refine sum_congr rfl fun τ _ => ?_
    rw [Nat.cast_sub (Nat.choose_le_choose _ (Nat.sub_le _ _)), sub_div, div_self hC.ne']
  have hp0 : (0 : ℝ) ≤ w / n := by positivity
  have hp1 : (w : ℝ) / n ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast hw) (Nat.cast_nonneg _)
  rw [havg, mul_sum]
  constructor
  · refine sum_le_sum fun τ _ => ?_
    have hs : (A τ).card ≤ n := card_le_univ _
    have hr := fp_choose_ratio n (A τ).card w hs
    have hr' : ((n - (A τ).card).choose w : ℝ) / n.choose w ≤ (1 - (w : ℝ) / n) ^ (A τ).card := by
      rw [div_le_iff₀ hC]; linarith
    linarith [(fp_one_sub_pow _ (A τ).card hp0 hp1).1]
  · refine sum_le_sum fun τ _ => ?_
    have hs : (A τ).card ≤ n := card_le_univ _
    refine le_min (by linarith [div_nonneg (Nat.cast_nonneg (α := ℝ)
      ((n - (A τ).card).choose w)) hC.le]) ?_
    rcases w with _ | w
    · simp
    · have hn : 0 < n := by omega
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 : (n.choose (w + 1) : ℝ)
          ≤ (n - (A τ).card).choose (w + 1) + (A τ).card * (n - 1).choose w := by
        exact_mod_cast choose_sub_le n w _ hs
      have h2 : (n : ℝ) * (n - 1).choose w = n.choose (w + 1) * (w + 1) := by
        have := Nat.add_one_mul_choose_eq (n - 1) w
        rw [Nat.sub_add_cancel hn] at this
        exact_mod_cast this
      rw [one_sub_div hC.ne', div_le_iff₀ hC, show ((w + 1 : ℕ) : ℝ) / n * (A τ).card *
        n.choose (w + 1) = ((w + 1 : ℕ) * (A τ).card * n.choose (w + 1) : ℝ) / n by ring,
        le_div_iff₀ hnR]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right h1 hnR.le]

theorem fp_L_exists : FP_L_exists := by
  classical
  intro T E _ _ A w hw
  by_contra h
  push Not at h
  have hne : ((univ : Finset E).powersetCard w).Nonempty := powersetCard_nonempty.2 (by simpa)
  have hC : (0 : ℝ) < (Fintype.card E).choose w := by exact_mod_cast Nat.choose_pos hw
  have hlt := sum_lt_sum_of_nonempty hne fun W hW => h W (mem_powersetCard.1 hW).2
  rw [sum_const, card_powersetCard, card_univ, nsmul_eq_mul, ← div_lt_iff₀' hC] at hlt
  linarith [(fp_L_average A w hw).1]

theorem fp_power_lower : FP_power_lower := by
  classical
  intro R n L S
  have hA : ∀ τ : Fin L → Fin R, fpPowA S τ = Fintype.piFinset fun ℓ => S (τ ℓ) := by
    intro τ; ext; simp [fpPowA, Fintype.mem_piFinset]
  refine ⟨fun τ => by rw [hA, Fintype.card_piFinset], fun w hw => ?_⟩
  have hE : Fintype.card (Fin L → Fin n) = n ^ L := by simp
  obtain ⟨W, hW, h⟩ := fp_L_exists (fpPowA S) w (hE ▸ hw)
  refine ⟨W, hW, ?_⟩
  simpa [hE, hA, Nat.cast_prod] using h

end ThinMatrixProducts

import Statements
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
/-! # Lemma A.13 (`(1/L) ln V_L → F*`)

Write `s_l = ln S_l`, `λ = ln β`, so that `β^{-L} ∏_ℓ S_{τ_ℓ} = e^{W(τ)}` with
`W(τ) = ∑_ℓ (s_{τ_ℓ} - λ)`.

Upper bound: `min{1, e^W} ≤ e^{tW}` for `t ∈ [0,1]`, and `∑_τ e^{tW(τ)} = e^{L F(t)}`.

Lower bound (instead of the method of types). For `t ∈ [0,1]` let `q_l = S_l^t / ∑ S^t` (the tilted
distribution of the paper's `p_t`), `μ = ∑_l q_l (s_l - λ)` (so `F'(t) = μ`), `e_l = s_l - λ - μ`,
`σ² = ∑_l q_l e_l²`, and under the product measure `P(τ) = ∏_ℓ q_{τ_ℓ}` let `Y(τ) = ∑_ℓ e_{τ_ℓ}`,
so `W = Lμ + Y`. Then `P(τ) e^{L F(t)} = e^{tW(τ)}`, `∑_τ P(τ) Y(τ)² = L σ²`, and by Chebyshev the
strings with `|Y| ≤ a`, `a = √(2(σ²+1)L)`, have probability at least `1/2`. If `μ = 0`, or `t = 0`
and `μ ≥ 0`, or `t = 1` and `μ ≤ 0` (the three cases of the paper's proof), each such string has
`min{1, e^W} ≥ e^{tW - a} = P(τ) e^{L F(t)} e^{-a}`, so `V_L ≥ e^{L F(t)} e^{-a}/2`. Such a `t` exists
by the intermediate value theorem applied to the continuous `μ(t)` on `[0,1]`. With the upper
bound, this `t` minimises `F` and `(1/L) ln V_L → F(t)`, with an explicit rate `O(1/√L)`. -/
namespace ThinMatrixProducts

open Finset Filter Topology

section FullProductTypes

/-- A sum over `Fin (L+1) → α` split into the first letter and the tail. -/
lemma fp_sum_cons {α M : Type} [Fintype α] [AddCommMonoid M] (L : ℕ)
    (g : (Fin (L + 1) → α) → M) : ∑ τ, g τ = ∑ j, ∑ τ' : Fin L → α, g (Fin.cons j τ') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => α) _ _ (fun _ => rfl)).symm

/-- The product measure has total mass one and the sum `Y` has mean zero and variance `L σ²`. -/
lemma fp_moments {R : ℕ} (q e : Fin R → ℝ) (hq : ∑ l, q l = 1) (he : ∑ l, q l * e l = 0) :
    ∀ L : ℕ, ∑ τ : Fin L → Fin R, ∏ ℓ, q (τ ℓ) = 1 ∧
      ∑ τ : Fin L → Fin R, (∏ ℓ, q (τ ℓ)) * ∑ ℓ, e (τ ℓ) = 0 ∧
      ∑ τ : Fin L → Fin R, (∏ ℓ, q (τ ℓ)) * (∑ ℓ, e (τ ℓ)) ^ 2 = L * ∑ l, q l * e l ^ 2 := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · rw [fp_sum_cons L]
      simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
      simp_rw [← Finset.mul_sum, h0, mul_one, hq]
    · rw [fp_sum_cons L]
      simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have : ∀ j, ∑ τ' : Fin L → Fin R, q j * (∏ ℓ, q (τ' ℓ)) * (e j + ∑ ℓ, e (τ' ℓ))
          = q j * e j * ∑ τ' : Fin L → Fin R, ∏ ℓ, q (τ' ℓ)
            + q j * ∑ τ' : Fin L → Fin R, (∏ ℓ, q (τ' ℓ)) * ∑ ℓ, e (τ' ℓ) := by
        intro j
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [Finset.sum_congr rfl fun j _ => this j, h0, h1]
      simp [he]
    · rw [fp_sum_cons L]
      simp only [Fin.prod_univ_succ, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have : ∀ j, ∑ τ' : Fin L → Fin R, q j * (∏ ℓ, q (τ' ℓ)) * (e j + ∑ ℓ, e (τ' ℓ)) ^ 2
          = q j * e j ^ 2 * ∑ τ' : Fin L → Fin R, ∏ ℓ, q (τ' ℓ)
            + 2 * (q j * e j) * ∑ τ' : Fin L → Fin R, (∏ ℓ, q (τ' ℓ)) * ∑ ℓ, e (τ' ℓ)
            + q j * ∑ τ' : Fin L → Fin R, (∏ ℓ, q (τ' ℓ)) * (∑ ℓ, e (τ' ℓ)) ^ 2 := by
        intro j
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
      rw [Finset.sum_congr rfl fun j _ => this j, h0, h1, h2]
      simp only [mul_one, mul_zero, add_zero, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hq]
      push_cast; ring

/-- `β^{-L} ∏_ℓ S_{τ_ℓ} = e^{∑_ℓ (s_{τ_ℓ} - λ)}`. -/
lemma fp_ratio_exp {R L : ℕ} (S : Fin R → ℕ) (hS : ∀ l, 1 ≤ S l) {β : ℝ} (hβ : 0 < β)
    (τ : Fin L → Fin R) :
    (∏ ℓ, (S (τ ℓ) : ℝ)) / β ^ L = Real.exp (∑ ℓ, (Real.log (S (τ ℓ)) - Real.log β)) := by
  have hpos : ∀ l, (0 : ℝ) < S l := fun l => by exact_mod_cast (hS l)
  rw [Finset.sum_sub_distrib, Real.exp_sub, Real.exp_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Real.exp_nat_mul, Real.exp_log hβ]
  congr 1
  exact Finset.prod_congr rfl fun ℓ _ => (Real.exp_log (hpos _)).symm

/-- `∑_l S_l^t = ∑_l e^{t s_l}`. -/
lemma fp_rpow_exp {R : ℕ} (S : Fin R → ℕ) (hS : ∀ l, 1 ≤ S l) (t : ℝ) (l : Fin R) :
    (S l : ℝ) ^ t = Real.exp (t * Real.log (S l)) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast (hS l)), mul_comm]

/-- `∑_τ e^{t W(τ)} = e^{L F(t)}`. -/
lemma fp_sum_exp_tW {R : ℕ} (S : Fin R → ℕ) (hS : ∀ l, 1 ≤ S l) (β t : ℝ) (L : ℕ)
    (hZ : 0 < ∑ l, (S l : ℝ) ^ t) :
    ∑ τ : Fin L → Fin R, Real.exp (t * ∑ ℓ, (Real.log (S (τ ℓ)) - Real.log β))
      = Real.exp (L * fpF S β t) := by
  unfold fpF
  have : ∀ τ : Fin L → Fin R, Real.exp (t * ∑ ℓ, (Real.log (S (τ ℓ)) - Real.log β))
      = Real.exp (-(L * t * Real.log β)) * ∏ ℓ, (S (τ ℓ) : ℝ) ^ t := by
    intro τ
    rw [Finset.prod_congr rfl fun ℓ _ => fp_rpow_exp S hS t (τ ℓ), ← Real.exp_sum, ← Real.exp_add]
    congr 1
    rw [Finset.mul_sum]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl fun τ _ => this τ, ← Finset.mul_sum,
    show (∑ τ : Fin L → Fin R, ∏ ℓ, (S (τ ℓ) : ℝ) ^ t) = (∑ l, (S l : ℝ) ^ t) ^ L from
      (Fintype.sum_pow (fun l => (S l : ℝ) ^ t) L).symm, mul_sub, Real.exp_sub, Real.exp_nat_mul, Real.exp_log hZ]
  rw [show -((L : ℝ) * t * Real.log β) = -(L * (t * Real.log β)) by ring, Real.exp_neg]
  field_simp

lemma fp_VL_pos {R : ℕ} (S : Fin R → ℕ) (hS : ∀ l, 1 ≤ S l) {β : ℝ} (hβ : 0 < β) (hR : 1 ≤ R)
    (L : ℕ) : 0 < fpVL S β L := by
  unfold fpVL
  refine Finset.sum_pos (fun τ _ => lt_min one_pos ?_) ⟨fun _ => ⟨0, hR⟩, Finset.mem_univ _⟩
  exact div_pos (Finset.prod_pos fun ℓ _ => by exact_mod_cast (hS _)) (pow_pos hβ _)

/-- The upper half: `V_L ≤ e^{L F(t)}` for `t ∈ [0,1]`. -/
lemma fp_VL_upper {R : ℕ} (S : Fin R → ℕ) (hS : ∀ l, 1 ≤ S l) {β : ℝ} (hβ : 0 < β) (hR : 1 ≤ R)
    (L : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : fpVL S β L ≤ Real.exp (L * fpF S β t) := by
  have hZ : 0 < ∑ l, (S l : ℝ) ^ t :=
    Finset.sum_pos (fun l _ => Real.rpow_pos_of_pos (by exact_mod_cast (hS l)) _)
      ⟨⟨0, hR⟩, Finset.mem_univ _⟩
  rw [← fp_sum_exp_tW S hS β t L hZ]
  unfold fpVL
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [fp_ratio_exp S hS hβ τ]
  set W := ∑ ℓ, (Real.log (S (τ ℓ)) - Real.log β)
  rcases le_total W 0 with hW | hW
  · exact (min_le_right _ _).trans (Real.exp_le_exp.2 (by nlinarith))
  · exact (min_le_left _ _).trans (Real.one_le_exp (by positivity))

/-- The lower half for a tilt `t` with the case condition on `μ = F'(t)`. -/
lemma fp_VL_lower {R : ℕ} (S : Fin R → ℕ) (hS : ∀ l, 1 ≤ S l) {β : ℝ} (hβ : 0 < β) (hR : 1 ≤ R)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hμ : let Z := ∑ l, (S l : ℝ) ^ t
          let μ := ∑ l, (S l : ℝ) ^ t / Z * (Real.log (S l) - Real.log β)
          μ = 0 ∨ (t = 0 ∧ 0 ≤ μ) ∨ (t = 1 ∧ μ ≤ 0)) :
    ∃ C : ℝ, ∀ L : ℕ, 1 ≤ L →
      (L : ℝ) * fpF S β t - C * Real.sqrt L - Real.log 2 ≤ Real.log (fpVL S β L) := by
  set Z := ∑ l, (S l : ℝ) ^ t with hZdef
  have hZ : 0 < Z :=
    Finset.sum_pos (fun l _ => Real.rpow_pos_of_pos (by exact_mod_cast (hS l)) _)
      ⟨⟨0, hR⟩, Finset.mem_univ _⟩
  set d : Fin R → ℝ := fun l => Real.log (S l) - Real.log β
  set q : Fin R → ℝ := fun l => (S l : ℝ) ^ t / Z
  set μ := ∑ l, q l * d l with hμdef
  set e : Fin R → ℝ := fun l => d l - μ
  set σ2 := ∑ l, q l * e l ^ 2
  have hq : ∑ l, q l = 1 := by
    simp only [q]; rw [← Finset.sum_div, div_self hZ.ne']
  have hqpos : ∀ l, 0 < q l := fun l =>
    div_pos (Real.rpow_pos_of_pos (by exact_mod_cast (hS l)) _) hZ
  have he : ∑ l, q l * e l = 0 := by
    simp only [e, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hq, one_mul]
    simp [μ]
  have hσ : 0 ≤ σ2 := Finset.sum_nonneg fun l _ => mul_nonneg (hqpos l).le (sq_nonneg _)
  refine ⟨Real.sqrt (2 * (σ2 + 1)), fun L hL => ?_⟩
  obtain ⟨hP1, -, hP2⟩ := fp_moments q e hq he L
  set P : (Fin L → Fin R) → ℝ := fun τ => ∏ ℓ, q (τ ℓ)
  set Y : (Fin L → Fin R) → ℝ := fun τ => ∑ ℓ, e (τ ℓ)
  have hPpos : ∀ τ, 0 < P τ := fun τ => Finset.prod_pos fun ℓ _ => hqpos _
  have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
  set a := Real.sqrt (2 * (σ2 + 1)) * Real.sqrt L with ha
  have ha2 : a ^ 2 = 2 * (σ2 + 1) * L := by
    rw [ha, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  have hapos : 0 < a := by positivity
  -- Chebyshev: the good strings have probability at least 1/2
  set good := univ.filter fun τ : Fin L → Fin R => |Y τ| ≤ a
  have hbad : ∑ τ ∈ univ.filter (fun τ : Fin L → Fin R => ¬ |Y τ| ≤ a), P τ ≤ 1 / 2 := by
    calc ∑ τ ∈ univ.filter (fun τ : Fin L → Fin R => ¬ |Y τ| ≤ a), P τ
        ≤ ∑ τ ∈ univ.filter (fun τ : Fin L → Fin R => ¬ |Y τ| ≤ a), P τ * Y τ ^ 2 / a ^ 2 := by
          refine Finset.sum_le_sum fun τ hτ => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hτ
          rw [le_div_iff₀ (by positivity)]
          have : a ^ 2 ≤ Y τ ^ 2 := by
            rw [← sq_abs (Y τ)]; exact pow_le_pow_left₀ hapos.le hτ.le 2
          nlinarith [hPpos τ]
      _ ≤ ∑ τ, P τ * Y τ ^ 2 / a ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            fun τ _ _ => div_nonneg (mul_nonneg (hPpos τ).le (sq_nonneg _)) (sq_nonneg _)
      _ = L * σ2 / a ^ 2 := by rw [← Finset.sum_div]; congr 1
      _ ≤ 1 / 2 := by
          rw [ha2, div_le_iff₀ (by positivity)]
          nlinarith
  have hgood : 1 / 2 ≤ ∑ τ ∈ good, P τ := by
    have := Finset.sum_filter_add_sum_filter_not univ (fun τ : Fin L → Fin R => |Y τ| ≤ a) P
    rw [hP1] at this
    linarith
  -- the pointwise bound on good strings
  have hW : ∀ τ, ∑ ℓ, (Real.log (S (τ ℓ)) - Real.log β) = L * μ + Y τ := by
    intro τ
    simp only [Y, e, d, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hPF : ∀ τ, P τ * Real.exp (L * fpF S β t) = Real.exp (t * (L * μ + Y τ)) := by
    intro τ
    rw [← hW τ]
    have h1 := fp_sum_exp_tW S hS β t L hZ
    have hP : P τ = Real.exp (t * ∑ ℓ, Real.log (S (τ ℓ))) / Z ^ L := by
      simp only [P, q, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rw [Finset.mul_sum, Real.exp_sum]
      congr 1
      exact Finset.prod_congr rfl fun ℓ _ => fp_rpow_exp S hS t _
    rw [hP]
    unfold fpF
    rw [mul_sub, Real.exp_sub, Real.exp_nat_mul, Real.exp_log hZ]
    rw [show (L : ℝ) * (t * Real.log β) = t * (L * Real.log β) by ring]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_sub, Real.exp_sub]
    field_simp
  have hpt : ∀ τ ∈ good, P τ * Real.exp (L * fpF S β t) * Real.exp (-a)
      ≤ min 1 ((∏ ℓ, (S (τ ℓ) : ℝ)) / β ^ L) := by
    intro τ hτ
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and, abs_le] at hτ
    rw [hPF τ, fp_ratio_exp S hS hβ τ, hW τ, ← Real.exp_add]
    set W := (L : ℝ) * μ + Y τ
    have hc1 : t * W ≤ a ∧ -a ≤ (1 - t) * W := by
      simp only at hμ
      rcases hμ with h | ⟨rfl, h⟩ | ⟨rfl, h⟩
      · have hm : μ = 0 := h
        simp only [W, hm, mul_zero, zero_add]
        constructor <;> nlinarith
      · have : 0 ≤ (L : ℝ) * μ := by positivity
        simp only [W]; constructor <;> nlinarith
      · have : (L : ℝ) * μ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h
        simp only [W]; constructor <;> nlinarith
    refine le_min ?_ ?_
    · exact Real.exp_le_one_iff.2 (by linarith)
    · exact Real.exp_le_exp.2 (by linarith)
  have hV : Real.exp (L * fpF S β t) * Real.exp (-a) / 2 ≤ fpVL S β L := by
    calc Real.exp (L * fpF S β t) * Real.exp (-a) / 2
        ≤ Real.exp (L * fpF S β t) * Real.exp (-a) * ∑ τ ∈ good, P τ := by
          have := mul_le_mul_of_nonneg_left hgood
            (by positivity : 0 ≤ Real.exp (L * fpF S β t) * Real.exp (-a))
          linarith
      _ = ∑ τ ∈ good, P τ * Real.exp (L * fpF S β t) * Real.exp (-a) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ τ ∈ good, min 1 ((∏ ℓ, (S (τ ℓ) : ℝ)) / β ^ L) := Finset.sum_le_sum hpt
      _ ≤ fpVL S β L := by
          unfold fpVL
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun τ _ _ => ?_
          exact le_min zero_le_one (div_nonneg (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)
            (pow_nonneg hβ.le _))
  have := Real.log_le_log (by positivity) hV
  rw [Real.log_div (by positivity) two_ne_zero, Real.log_mul (by positivity) (by positivity),
    Real.log_exp, Real.log_exp] at this
  linarith

/-- A tilt with the case condition exists (intermediate value theorem). -/
lemma fp_tilt_exists {R : ℕ} (S : Fin R → ℕ) (hS : ∀ l, 1 ≤ S l) (β : ℝ) (hR : 1 ≤ R) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      (let Z := ∑ l, (S l : ℝ) ^ t
       let μ := ∑ l, (S l : ℝ) ^ t / Z * (Real.log (S l) - Real.log β)
       μ = 0 ∨ (t = 0 ∧ 0 ≤ μ) ∨ (t = 1 ∧ μ ≤ 0)) := by
  set μ : ℝ → ℝ := fun t => ∑ l, (S l : ℝ) ^ t / (∑ l', (S l' : ℝ) ^ t) *
    (Real.log (S l) - Real.log β)
  have hcont : Continuous μ := by
    have hc : ∀ l, Continuous fun t : ℝ => (S l : ℝ) ^ t := fun l =>
      continuous_const.rpow continuous_id fun _ => Or.inl (by
        have : (1 : ℝ) ≤ S l := by exact_mod_cast hS l
        linarith)
    refine continuous_finsetSum _ fun l _ => ?_
    refine ((hc l).div (continuous_finsetSum _ fun l' _ => hc l') fun t => ?_).mul continuous_const
    exact (Finset.sum_pos (fun l' _ => Real.rpow_pos_of_pos (by exact_mod_cast (hS l')) _)
      ⟨⟨0, hR⟩, Finset.mem_univ _⟩).ne'
  by_cases h0 : 0 ≤ μ 0
  · exact ⟨0, le_rfl, zero_le_one, Or.inr (Or.inl ⟨rfl, h0⟩)⟩
  by_cases h1 : μ 1 ≤ 0
  · exact ⟨1, zero_le_one, le_rfl, Or.inr (Or.inr ⟨rfl, h1⟩)⟩
  push Not at h0 h1
  obtain ⟨t, ⟨ht0, ht1⟩, ht⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn
    ⟨h0.le, h1.le⟩
  exact ⟨t, ht0, ht1, Or.inl ht⟩

theorem fp_Lemma_A_13_bounds : FP_Lemma_A_13_bounds := by
  intro R S β hR hS hβ
  refine ⟨fun L t ht0 ht1 => fp_VL_upper S hS hβ hR L ht0 ht1, ?_⟩
  obtain ⟨t, ht0, ht1, hμ⟩ := fp_tilt_exists S hS β hR
  obtain ⟨C, hC⟩ := fp_VL_lower S hS hβ hR ht0 ht1 hμ
  exact ⟨t, ht0, ht1, C, hC⟩

theorem fp_Lemma_A_13 : FP_Lemma_A_13 := by
  intro R S β hR hS hβ
  obtain ⟨hup, t₀, ht0, ht1, C, hC⟩ := fp_Lemma_A_13_bounds R S β hR hS hβ
  -- the error term `(|C| + ln 2) L^{-1/2} → 0`
  set g : ℕ → ℝ := fun L => (|C| + Real.log 2) * (L : ℝ) ^ (-(1 / 2 : ℝ))
  have hg : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun L : ℕ => (L : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
    have := h1.const_mul (|C| + Real.log 2)
    rw [mul_zero] at this
    exact this
  have hlow : ∀ L : ℕ, 1 ≤ L → fpF S β t₀ - g L ≤ Real.log (fpVL S β L) / L := by
    intro L hL
    have hLR : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hsq : Real.sqrt L = (L : ℝ) * (L : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' (by linarith) (by norm_num)]
      norm_num
    have hinv : (1 : ℝ) ≤ (L : ℝ) * (L : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [← hsq]; exact Real.one_le_sqrt.2 hLR
    have hpos : 0 < (L : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    rw [le_div_iff₀ (by linarith)]
    have h := hC L hL
    rw [hsq] at h
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    simp only [g]
    nlinarith [le_abs_self C, abs_nonneg C, mul_le_mul_of_nonneg_left hinv hlog2]
  have hupper : ∀ L : ℕ, 1 ≤ L → ∀ t : ℝ, 0 ≤ t → t ≤ 1 → Real.log (fpVL S β L) / L ≤ fpF S β t := by
    intro L hL t h0 h1
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    rw [div_le_iff₀ hLR]
    have := Real.log_le_log (fp_VL_pos S hS hβ hR L) (hup L t h0 h1)
    rw [Real.log_exp] at this
    linarith
  refine ⟨t₀, ht0, ht1, fun t h0 h1 => ?_, ?_⟩
  · have : Tendsto (fun L => fpF S β t₀ - g L) atTop (𝓝 (fpF S β t₀)) := by
      simpa using (tendsto_const_nhds (x := fpF S β t₀)).sub hg
    refine le_of_tendsto this (eventually_atTop.2 ⟨1, fun L hL => ?_⟩)
    exact (hlow L hL).trans (hupper L hL t h0 h1)
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun L => fpF S β t₀ - g L)
      (h := fun _ => fpF S β t₀) ?_ tendsto_const_nhds ?_ ?_
    · simpa using (tendsto_const_nhds (x := fpF S β t₀)).sub hg
    · exact eventually_atTop.2 ⟨1, fun L hL => hlow L hL⟩
    · exact eventually_atTop.2 ⟨1, fun L hL => hupper L hL t₀ ht0 ht1⟩

end FullProductTypes

end ThinMatrixProducts

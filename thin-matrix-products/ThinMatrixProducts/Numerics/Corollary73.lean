import ThinMatrixProducts.Numerics.Lambda
import ThinMatrixProducts.Numerics.Mu
import ThinMatrixProducts.Util.Choose
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Corollary 7.3 and its proof: the arithmetic

The clauses of Corollary 7.3 that are not about running time, and the steps of its proof that are
arithmetic: the boxes (`ρ^t ≤ D^{-γ}`), the queries (`∑ binom(2m,d) 4^d ≤ 4x D^q`), the encoding
bound (3)/(4), the condition `N ≥ K N₀`, the reading of `ε < R'_c(γ)`, and the monotonicity and the
limit of `R'_c(0)`. Also Theorem 7.4's choice of parameters and Proposition 8.1.
-/

namespace ThinMatrixProducts

open Real Finset Filter Topology

/-! ## The entropy function -/

lemma H_zero : H 0 = 0 := by simp [H]

lemma H_eq_binEntropy : H = Real.binEntropy := by
  funext x
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, H, Real.negMulLog, Real.negMulLog]
  ring

lemma H_continuous : Continuous H := by rw [H_eq_binEntropy]; exact Real.binEntropy_continuous

/-- `x H(m/x) = x ln x - m ln m - (x-m) ln(x-m)` for `0 < m < x`. -/
lemma mul_H_div {m x : ℝ} (hm : 0 < m) (hx : m < x) :
    x * H (m / x) = x * Real.log x - m * Real.log m - (x - m) * Real.log (x - m) := by
  have hx0 : 0 < x := by linarith
  have h1 : 1 - m / x = (x - m) / x := by field_simp
  unfold H
  rw [h1, Real.log_div hm.ne' hx0.ne', Real.log_div (by linarith) hx0.ne']
  field_simp
  ring

/-- `c H(1/c) = c ln c - (c-1) ln(c-1)` for `c > 1`. -/
lemma mul_H_inv {c : ℝ} (hc : 1 < c) :
    c * H (1 / c) = c * Real.log c - (c - 1) * Real.log (c - 1) := by
  have := mul_H_div (m := 1) (x := c) one_pos hc
  rw [this, Real.log_one]; ring

/-- `x ↦ x ln x - (x-m) ln(x-m)` is monotone on `x > m`. -/
lemma monotoneOn_aux {m : ℝ} (hm : 0 < m) :
    MonotoneOn (fun x => x * Real.log x - (x - m) * Real.log (x - m)) (Set.Ioi m) := by
  have hd : ∀ x ∈ Set.Ioi m, HasDerivAt (fun x => x * Real.log x - (x - m) * Real.log (x - m))
      (Real.log x + 1 - (Real.log (x - m) + 1)) x := by
    intro x hx
    have hx' : (m : ℝ) < x := hx
    have h1 := Real.hasDerivAt_mul_log (x := x) (by linarith)
    have h2 := (Real.hasDerivAt_mul_log (x := x - m) (by linarith)).comp x
      ((hasDerivAt_id x).sub_const m)
    exact (h1.sub h2).congr_deriv (by ring)
  refine monotoneOn_of_deriv_nonneg (convex_Ioi m) ?_ ?_ ?_
  · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro x hx
    have hx' : (m : ℝ) < x := hx
    rw [(hd x hx).deriv]
    have : Real.log (x - m) ≤ Real.log x := Real.log_le_log (by linarith) (by linarith)
    linarith

/-- `x H(m/x)` is monotone in `x > m`. -/
lemma mul_H_div_mono {m x y : ℝ} (hm : 0 < m) (hx : m < x) (hxy : x ≤ y) :
    x * H (m / x) ≤ y * H (m / y) := by
  rw [mul_H_div hm hx, mul_H_div hm (by linarith)]
  have := monotoneOn_aux hm (show x ∈ Set.Ioi m from hx) (show y ∈ Set.Ioi m by
    simp only [Set.mem_Ioi]; linarith) hxy
  simp only at this
  linarith

/-! ## The binomial lower bound by the entropy function -/

/-- `binom(n, k) ≥ e^{n H(k/n)}/(n+1)` (as in the proof of Corollary 7.3). Adapted from
`3sum-apsp/ThreeSumApsp/Sec4/ChoosingParameters.lean`. -/
theorem exp_H_div_le_choose (k n : ℕ) (hkn : k ≤ n) :
    Real.exp ((n : ℝ) * H ((k : ℝ) / (n : ℝ))) / ((n : ℝ) + 1) ≤ (Nat.choose n k : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain rfl : k = 0 := by omega
    simp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_div, H_zero, mul_zero, Real.exp_zero, Nat.choose_zero_right,
      Nat.cast_one]
    rw [div_le_one (by positivity)]; linarith
  rcases eq_or_lt_of_le hkn with rfl | hkn'
  · have h1 : ((k : ℝ) / k) = 1 := div_self (by positivity)
    simp only [h1, Nat.choose_self, Nat.cast_one]
    rw [show H 1 = 0 by simp [H]]
    simp only [mul_zero, Real.exp_zero]
    rw [div_le_one (by positivity)]; linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hkn0 : (k : ℝ) < n := by exact_mod_cast hkn'
  have hn0 : (0 : ℝ) < n := by linarith
  -- `e^{n H(k/n)} = n^n/(k^k (n-k)^{n-k})`
  have hexp : Real.exp ((n : ℝ) * H ((k : ℝ) / (n : ℝ)))
      = (n : ℝ) ^ n / ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
    have hnk' : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
    rw [mul_H_div hk0 hkn0, show (n : ℝ) - k = ((n - k : ℕ) : ℝ) by push_cast [Nat.cast_sub hkn]; ring,
      Real.exp_sub, Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log hn0, Real.exp_log hk0, Real.exp_log hnk', div_div]
  have hstd : (n : ℝ) ^ n
      ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
    exact_mod_cast NatChoose.pow_self_le_mul_choose_mul_pow_mul_pow hkn
  have hpos : (0 : ℝ) < (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) := by
    have : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
    positivity
  rw [hexp, div_div, div_le_iff₀ (by positivity)]
  nlinarith

/-! ## `ln Λ_c(0)` as a function of `c` -/

/-- `F(c) := 2c ln 5 - c H(1/c) - (c-1) ln 4`, which is `ln Λ_c(0)`. -/
noncomputable def lnL0 (c : ℝ) : ℝ := 2 * c * Real.log 5 - c * H (1 / c) - (c - 1) * Real.log 4

lemma log_LambdaC_eq_lnL0 (c γ : ℝ) : Real.log (LambdaC c γ) = lnL0 c + γ * Real.log 4 := by
  rw [log_LambdaC, lnL0]

/-- The closed form of `F` without the entropy function, valid for `c > 1`. -/
noncomputable def lnL0' (c : ℝ) : ℝ :=
  2 * c * Real.log 5 - (c * Real.log c - (c - 1) * Real.log (c - 1)) - (c - 1) * Real.log 4

lemma lnL0_eq {c : ℝ} (hc : 1 < c) : lnL0 c = lnL0' c := by
  rw [lnL0, lnL0', mul_H_inv hc]

lemma hasDerivAt_lnL0' {c : ℝ} (hc : 1 < c) :
    HasDerivAt lnL0' (2 * Real.log 5 - Real.log c + Real.log (c - 1) - Real.log 4) c := by
  have h1 := Real.hasDerivAt_mul_log (x := c) (by linarith)
  have h2 := (Real.hasDerivAt_mul_log (x := c - 1) (by linarith)).comp c
    ((hasDerivAt_id c).sub_const 1)
  have h3 := ((hasDerivAt_id c).const_mul (2 * Real.log 5))
  have h4 := ((hasDerivAt_id c).sub_const 1).mul_const (Real.log 4)
  have := (h3.sub (h1.sub h2)).sub h4
  refine this.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · simp; ring
  · exact Filter.Eventually.of_forall fun x => by simp [lnL0']; ring

lemma hasDerivAt_lnL0 {c : ℝ} (hc : 1 < c) :
    HasDerivAt lnL0 (Real.log (25 * (c - 1) / (4 * c))) c := by
  have hev : lnL0 =ᶠ[𝓝 c] lnL0' := by
    filter_upwards [lt_mem_nhds hc] with x hx using lnL0_eq hx
  have h := (hasDerivAt_lnL0' hc).congr_of_eventuallyEq hev
  refine h.congr_deriv ?_
  rw [Real.log_div (by nlinarith) (by positivity), Real.log_mul (by norm_num) (by linarith),
    Real.log_mul (by norm_num) (by linarith), show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]
  push_cast; ring

lemma log_deriv_pos {c : ℝ} (hc : 5 < c) : 0 < Real.log (25 * (c - 1) / (4 * c)) := by
  apply Real.log_pos
  rw [one_lt_div (by positivity)]; linarith

lemma H_one_fifth : H (1 / 5) + 4 / 5 * Real.log 4 = Real.log 5 := by
  unfold H
  rw [show (1 : ℝ) - 1 / 5 = 4 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
    Real.log_div (by norm_num) (by norm_num), Real.log_one]
  ring

lemma lnL0_five : lnL0 5 = 5 * Real.log 5 := by
  have := H_one_fifth
  rw [lnL0]; linarith

theorem corollary_7_3_derivative : Corollary_7_3_derivative := by
  refine ⟨fun c hc => ?_, fun c hc => log_deriv_pos hc, H_one_fifth, ?_⟩
  · exact hasDerivAt_lnL0 hc
  · have := H_one_fifth; linarith

lemma lnL0_strictMonoOn : StrictMonoOn lnL0 (Set.Ici 5) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 5) ?_ ?_
  · intro x hx
    exact (hasDerivAt_lnL0 (by simp at hx; linarith)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx' : (5 : ℝ) < x := hx
    rw [(hasDerivAt_lnL0 (by linarith)).deriv]
    exact log_deriv_pos hx'

lemma lnL0_ge {c : ℝ} (hc : 5 ≤ c) : 5 * Real.log 5 ≤ lnL0 c := by
  rw [← lnL0_five]
  exact lnL0_strictMonoOn.monotoneOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hc) hc

lemma lnL0_gt {c : ℝ} (hc : 5 < c) : 5 * Real.log 5 < lnL0 c := by
  rw [← lnL0_five]
  exact lnL0_strictMonoOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hc.le) hc

lemma log_LambdaC_pos {c γ : ℝ} (hc : 5 ≤ c) (hγ : 0 ≤ γ) : 0 < Real.log (LambdaC c γ) := by
  rw [log_LambdaC_eq_lnL0]
  have := lnL0_ge hc
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  nlinarith

theorem corollary_7_3_limit : Corollary_7_3_limit := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [RPrime, log_LambdaC_eq_lnL0, zero_mul, add_zero]
    have hxp : 0 < lnL0 x := by have := lnL0_ge hx; nlinarith
    exact div_lt_div_of_pos_left h4 hxp (lnL0_strictMonoOn hx hy hxy)
  · simp only [RPrime, log_LambdaC_eq_lnL0, zero_mul, add_zero, lnL0_five, epsStar5]
  · have hcont : ContinuousAt lnL0 5 := (hasDerivAt_lnL0 (by norm_num)).continuousAt
    have : Tendsto (fun c => Real.log 4 / lnL0 c) (𝓝 5) (𝓝 (Real.log 4 / lnL0 5)) :=
      tendsto_const_nhds.div hcont (by rw [lnL0_five]; positivity)
    have h' := this.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (5 : ℝ)))
    simp only [RPrime, log_LambdaC_eq_lnL0, zero_mul, add_zero]
    rwa [lnL0_five, ← epsStar5] at h'

/-! ## The clauses of Corollary 7.3 -/

theorem corollary_7_3_gamma_pos : Corollary_7_3_gamma_pos := by
  intro c θ hc hθ
  unfold gammaOf
  exact mul_pos hθ (Real.logb_pos (by norm_num) (by linarith))

lemma ceil_bounds (x : ℝ) (hx : 0 ≤ x) : x ≤ (⌈x⌉₊ : ℝ) ∧ (⌈x⌉₊ : ℝ) < x + 1 :=
  ⟨Nat.le_ceil x, Nat.ceil_lt_add_one hx⟩

lemma Dr_rpow_pos (m : ℕ) (x : ℝ) : 0 < Dr m ^ x := Real.rpow_pos_of_pos (by unfold Dr; positivity) x

/-- `D^x = e^{x m ln 4}`. -/
lemma Dr_rpow (m : ℕ) (x : ℝ) : Dr m ^ x = Real.exp (x * (m * Real.log 4)) := by
  rw [Dr, Real.rpow_def_of_pos (by positivity), Real.log_pow]; ring_nf

lemma rhoC_rpow (c θ : ℝ) (hc : 5 < c) (m : ℕ) :
    rhoC c ^ (2 * θ * m) = Dr m ^ (-gammaOf c θ) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Dr_rpow, rhoC, Real.rpow_def_of_pos (by apply div_pos <;> linarith), gammaOf, Real.logb,
    log_four_eq, Real.log_div (by norm_num) (by linarith),
    Real.log_div (by linarith) (by norm_num), log_four_eq]
  congr 1
  field_simp
  ring

theorem corollary_7_3_boxes : Corollary_7_3_boxes := by
  intro c θ hc hθ m hm
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨hL1, _⟩ := ceil_bounds (c * m) (by positivity)
  set L := levelsOf c m with hLdef
  have hL : c * m ≤ (L : ℝ) := hL1
  have hden : (c - 1) * m < (L : ℝ) - m + 1 := by nlinarith
  have hden0 : 0 < (L : ℝ) - m + 1 := by nlinarith
  have hrho : rho L m < rhoC c := by
    rw [rho, rhoC, div_lt_div_iff₀ hden0 (by linarith)]
    nlinarith
  have hrho0 : 0 ≤ rho L m := by rw [rho]; positivity
  have hc1 : rhoC c < 1 := by rw [rhoC, div_lt_one (by linarith)]; linarith
  have hc0 : 0 < rhoC c := by rw [rhoC]; apply div_pos <;> linarith
  refine ⟨hrho, hc1, ?_, ?_, rhoC_rpow c θ hc m⟩
  · exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  · calc rho L m ^ switchOf θ m ≤ rhoC c ^ switchOf θ m :=
          pow_le_pow_left₀ hrho0 hrho.le _
      _ = rhoC c ^ ((switchOf θ m : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ rhoC c ^ (2 * θ * m) := by
          apply Real.rpow_le_rpow_of_exponent_ge hc0 hc1.le
          exact Nat.le_ceil _

/-- `4^d ≤ (4x)^t x^{-d}` for `d ≤ t` and `4x ≥ 1`. -/
lemma four_pow_le {x : ℝ} (hx : 0 < x) (h4x : 1 ≤ 4 * x) {d t : ℕ} (hdt : d ≤ t) :
    (4 : ℝ) ^ d ≤ (4 * x) ^ t * (1 / x) ^ d := by
  have : (4 * x) ^ d ≤ (4 * x) ^ t := pow_le_pow_right₀ h4x hdt
  rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), ← mul_pow]
  exact this

theorem corollary_7_3_queries : Corollary_7_3_queries := by
  intro θ hθ hθ1 m
  set x := (1 - θ) / θ with hx
  have hx0 : 0 < x := div_pos (by linarith) hθ
  have h4x : 1 < 4 * x := by
    rw [hx, ← mul_div_assoc, one_lt_div hθ]; linarith
  have hid : (4 * x) ^ θ / (1 - θ) = (4 : ℝ) ^ θ * Real.exp (H θ) := by
    have h1θ : 0 < 1 - θ := by linarith
    have hL : 0 < (4 * x) ^ θ / (1 - θ) := by positivity
    have hR : 0 < (4 : ℝ) ^ θ * Real.exp (H θ) := by positivity
    rw [← Real.exp_log hL, ← Real.exp_log hR]
    congr 1
    rw [Real.log_div (by positivity) h1θ.ne', Real.log_rpow (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_rpow (by norm_num), Real.log_exp, hx, Real.log_div h1θ.ne' hθ.ne']
    unfold H
    ring
  refine ⟨h4x, hid, ?_⟩
  set t := switchOf θ m
  have ht : (t : ℝ) < 2 * θ * m + 1 := Nat.ceil_lt_add_one (by positivity)
  have ht2 : t ≤ 2 * m := by
    apply Nat.ceil_le.2
    push_cast
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  -- the sum is at most `(4x)^t (1 + 1/x)^{2m}`
  have hsum : (∑ d ∈ range (t + 1), ((2 * m).choose d : ℝ) * 4 ^ d)
      ≤ (4 * x) ^ t * (1 + 1 / x) ^ (2 * m) := by
    rw [add_comm (1 : ℝ) (1 / x), add_pow, mul_sum]
    calc (∑ d ∈ range (t + 1), ((2 * m).choose d : ℝ) * 4 ^ d)
        ≤ ∑ d ∈ range (t + 1), (4 * x) ^ t * ((1 / x) ^ d * 1 ^ (2 * m - d) * ((2 * m).choose d)) := by
          refine sum_le_sum fun d hd => ?_
          have := four_pow_le hx0 h4x.le (Nat.lt_succ_iff.1 (mem_range.1 hd))
          rw [one_pow, mul_one]
          nlinarith [(Nat.cast_nonneg _ : (0 : ℝ) ≤ ((2 * m).choose d : ℝ))]
      _ ≤ ∑ d ∈ range (2 * m + 1), (4 * x) ^ t * ((1 / x) ^ d * 1 ^ (2 * m - d) * ((2 * m).choose d)) := by
          apply sum_le_sum_of_subset_of_nonneg
          · exact range_subset_range.2 (by omega)
          · intro i _ _; positivity
  -- `(4x)^t < 4x (4x)^{2θm}`
  have hpow : (4 * x) ^ t ≤ 4 * x * (4 * x) ^ (2 * θ * m) := by
    rw [← Real.rpow_natCast, ← Real.rpow_one_add' (by linarith) (by positivity)]
    · exact Real.rpow_le_rpow_of_exponent_le h4x.le (by linarith)
  have h1x : 1 + 1 / x = 1 / (1 - θ) := by
    have : (1 - θ) ≠ 0 := by linarith
    rw [hx]; field_simp; ring
  have hDq : Dr m ^ qOf θ = ((4 : ℝ) ^ θ * Real.exp (H θ)) ^ (2 * m) := by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    rw [Dr_rpow, show (4 : ℝ) ^ θ * Real.exp (H θ) = Real.exp (θ * Real.log 4 + H θ) by
      rw [Real.rpow_def_of_pos (by norm_num), Real.exp_add]; ring_nf, ← Real.exp_nat_mul]
    congr 1
    unfold qOf
    rw [log_four_eq]
    field_simp
    push_cast
    ring
  have hsplit : (4 * x) ^ (2 * θ * m) * (1 + 1 / x) ^ (2 * m) = Dr m ^ qOf θ := by
    rw [hDq, ← hid, h1x, show 2 * θ * (m : ℝ) = θ * ((2 * m : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_mul (by positivity), Real.rpow_natCast, ← mul_pow]
    ring
  calc (∑ d ∈ range (t + 1), ((2 * m).choose d : ℝ) * 4 ^ d)
      ≤ (4 * x) ^ t * (1 + 1 / x) ^ (2 * m) := hsum
    _ ≤ 4 * x * (4 * x) ^ (2 * θ * m) * (1 + 1 / x) ^ (2 * m) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = 4 * x * Dr m ^ qOf θ := by rw [mul_assoc, hsplit]

/-! ## Equations (3) and (4) -/

theorem eq_4 : Eq_4 := by
  intro c γ hc hγ m hm Kg hKg
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set L := levelsOf c m with hLdef
  obtain ⟨hL1, hL2⟩ := ceil_bounds (c * m) (by positivity)
  have hL : c * m ≤ (L : ℝ) := hL1
  have hL' : (L : ℝ) < c * m + 1 := hL2
  have hmL : m ≤ L := by
    have : (m : ℝ) ≤ L := by nlinarith
    exact_mod_cast this
  have hmu := (muInf_bounds).1
  have hmu0 : 0 < muInf := by linarith
  have hK := exp_H_div_le_choose m L hmL
  have hL0 : (0 : ℝ) < L := by nlinarith
  set E := Real.exp ((L : ℝ) * H ((m : ℝ) / (L : ℝ))) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hKpos : 0 < (K L m : ℝ) := by
    have : 0 < K L m := Nat.choose_pos hmL
    exact_mod_cast this
  have hKg0 : 0 < Kg := lt_of_lt_of_le (by positivity) hKg
  have hN0 : (0 : ℝ) < N0 L m := by unfold N0; positivity
  -- step 1: replace `K_g` by `μ_∞² e^{L H(m/L)}/(L+1)`
  have step1 : Dr m ^ γ * (25 : ℝ) ^ L / (Kg * N0 L m)
      ≤ ((L : ℝ) + 1) / muInf ^ 2 * (Dr m ^ γ * (25 : ℝ) ^ L / (E * N0 L m)) := by
    have hlow : muInf ^ 2 * (E / ((L : ℝ) + 1)) ≤ Kg :=
      le_trans (mul_le_mul_of_nonneg_left hK (by positivity)) hKg
    rw [div_le_iff₀ (by positivity)]
    calc Dr m ^ γ * (25 : ℝ) ^ L
        = ((L : ℝ) + 1) / muInf ^ 2 * (Dr m ^ γ * (25 : ℝ) ^ L / (E * N0 L m))
            * (muInf ^ 2 * (E / ((L : ℝ) + 1)) * N0 L m) := by
          field_simp
      _ ≤ ((L : ℝ) + 1) / muInf ^ 2 * (Dr m ^ γ * (25 : ℝ) ^ L / (E * N0 L m)) * (Kg * N0 L m) := by
          apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlow hN0.le)
          have := Dr_rpow_pos m γ
          positivity
  -- step 2: the exponential form
  have hHmono : (c * m) * H (m / (c * m)) ≤ (L : ℝ) * H ((m : ℝ) / (L : ℝ)) :=
    mul_H_div_mono (by positivity) (by nlinarith) hL
  have hcm : (m : ℝ) / (c * m) = 1 / c := by field_simp
  rw [hcm] at hHmono
  have step2 : Dr m ^ γ * (25 : ℝ) ^ L / (E * N0 L m) ≤ 25 / 4 * LambdaC c γ ^ m := by
    have hl25 : Real.log 25 = 2 * Real.log 5 := by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have hLHS : Dr m ^ γ * (25 : ℝ) ^ L / (E * N0 L m)
        = Real.exp (γ * (m * Real.log 4) + L * Real.log 25 - L * H (m / L)
            - ((L : ℝ) - m) * Real.log 4) := by
      rw [Dr_rpow, hE, N0, Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (25 : ℝ),
        ← Real.rpow_natCast (4 : ℝ), Real.rpow_def_of_pos (by norm_num),
        Real.rpow_def_of_pos (by norm_num), Nat.cast_sub hmL, ← Real.exp_add, ← Real.exp_add,
        ← Real.exp_sub]
      ring_nf
    have hRHS : 25 / 4 * LambdaC c γ ^ m
        = Real.exp (Real.log (25 / 4) + m * Real.log (LambdaC c γ)) := by
      rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_nat_mul,
        Real.exp_log (LambdaC_pos c γ)]
    rw [hLHS, hRHS, Real.exp_le_exp, log_LambdaC, Real.log_div (by norm_num) (by norm_num), hl25]
    have h45 : 0 ≤ 2 * Real.log 5 - Real.log 4 := by
      rw [← hl25, ← Real.log_div (by norm_num) (by norm_num)]
      exact Real.log_nonneg (by norm_num)
    nlinarith
  calc Dr m ^ γ * (25 : ℝ) ^ L / (Kg * N0 L m)
      ≤ ((L : ℝ) + 1) / muInf ^ 2 * (Dr m ^ γ * (25 : ℝ) ^ L / (E * N0 L m)) := step1
    _ ≤ ((L : ℝ) + 1) / muInf ^ 2 * (25 / 4 * LambdaC c γ ^ m) :=
        mul_le_mul_of_nonneg_left step2 (by positivity)
    _ ≤ (c * m + 2) / muInf ^ 2 * (25 / 4 * LambdaC c γ ^ m) := by
        apply mul_le_mul_of_nonneg_right _ (by have := LambdaC_pos c γ; positivity)
        exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = (25 / 4) / muInf ^ 2 * (c * m + 2) * LambdaC c γ ^ m := by ring

theorem corollary_7_3_tile_fit : Corollary_7_3_tile_fit := by
  have hsq : ∀ L m : ℕ, m ≤ L → ((K L m : ℝ) * N0 L m) ^ 2 ≤ (25 : ℝ) ^ L := by
    intro L m hmL
    have hvan : (L.choose m) * (L.choose m) ≤ (L + L).choose (m + m) := by
      rw [Nat.add_choose_eq]
      exact Finset.single_le_sum (f := fun ij : ℕ × ℕ => L.choose ij.1 * L.choose ij.2)
        (a := (m, m)) (fun _ _ => Nat.zero_le _) (Finset.mem_antidiagonal.2 rfl)
    have hbin := NatChoose.choose_mul_pow_mul_pow_le 1 4 (L + L) (m + m)
    have hnat : (L.choose m * 4 ^ (L - m)) ^ 2 ≤ 25 ^ L := by
      calc (L.choose m * 4 ^ (L - m)) ^ 2 = L.choose m * L.choose m * 4 ^ ((L + L) - (m + m)) := by
            rw [mul_pow, sq, ← pow_mul]; congr 2; omega
        _ ≤ (L + L).choose (m + m) * 1 ^ (m + m) * 4 ^ ((L + L) - (m + m)) := by
            rw [one_pow, mul_one]; exact Nat.mul_le_mul_right _ hvan
        _ ≤ (1 + 4) ^ (L + L) := hbin
        _ = 25 ^ L := by rw [show L + L = 2 * L by ring, pow_mul]; norm_num
    have : ((L.choose m * 4 ^ (L - m) : ℕ) : ℝ) ^ 2 ≤ ((25 ^ L : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa [K, N0] using this
  refine ⟨hsq, ?_⟩
  intro L m γ Kg N hmL hγ hKg0 hKgK h
  have hKpos : 0 < (K L m : ℝ) := by
    have : 0 < K L m := Nat.choose_pos hmL
    exact_mod_cast this
  have hN0 : (0 : ℝ) < N0 L m := by unfold N0; positivity
  have hD : 1 ≤ Dr m ^ γ := Real.one_le_rpow (by unfold Dr; exact one_le_pow₀ (by norm_num)) hγ
  have h1 := hsq L m hmL
  calc (K L m : ℝ) * N0 L m ≤ (25 : ℝ) ^ L / (K L m * N0 L m) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith
    _ ≤ Dr m ^ γ * (25 : ℝ) ^ L / (Kg * N0 L m) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have h25 : (0 : ℝ) ≤ 25 ^ L := by positivity
        have : Kg * N0 L m ≤ K L m * N0 L m := mul_le_mul_of_nonneg_right hKgK hN0.le
        calc (25 : ℝ) ^ L * (Kg * N0 L m) ≤ 25 ^ L * (K L m * N0 L m) :=
              mul_le_mul_of_nonneg_left this h25
          _ = 1 * ((25 : ℝ) ^ L * (K L m * N0 L m)) := by ring
          _ ≤ Dr m ^ γ * ((25 : ℝ) ^ L * (K L m * N0 L m)) :=
              mul_le_mul_of_nonneg_right hD (by positivity)
          _ = Dr m ^ γ * 25 ^ L * (K L m * N0 L m) := by ring
    _ ≤ N := h

/-! ## The reading of `ε < R'_c(γ)` and the range of `m` -/

theorem corollary_7_3_eps_iff : Corollary_7_3_eps_iff := by
  intro c γ ε hc hγ hε
  have hl := log_LambdaC_pos hc hγ
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  rw [RPrime, lt_div_iff₀ hl, ← Real.log_lt_log_iff (LambdaC_pos c γ) (by positivity),
    Real.log_rpow (by norm_num), one_div, inv_mul_eq_div, lt_div_iff₀ hε, mul_comm]

theorem corollary_7_3_range : Corollary_7_3_range := by
  intro c γ ε hc hγ hε hlt
  have hΛ := (corollary_7_3_eps_iff c γ ε hc hγ hε).1 hlt
  set Λ := LambdaC c γ
  set B := (4 : ℝ) ^ (1 / ε)
  have hΛ0 : 0 < Λ := LambdaC_pos c γ
  have hr : 1 < B / Λ := by rw [one_lt_div hΛ0]; exact hΛ
  -- `(B/Λ)^m` eventually exceeds `75 (cm+2) B`
  have hlim : Tendsto (fun m : ℕ => (75 * (c * m + 2) * B) / (B / Λ) ^ m) atTop (𝓝 0) := by
    have h1 := tendsto_pow_const_div_const_pow_of_one_lt 1 hr
    have h0 := tendsto_pow_const_div_const_pow_of_one_lt 0 hr
    have := (h1.const_mul (75 * c * B)).add (h0.const_mul (150 * B))
    simp only [mul_zero, add_zero] at this
    refine this.congr fun m => ?_
    simp only [pow_one, pow_zero]
    field_simp
    ring
  obtain ⟨m₀, hm₀⟩ := (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))).exists_forall_of_atTop
  refine ⟨m₀, fun m hm N hN => ?_⟩
  have hB : 0 < B := by positivity
  have h := hm₀ m hm
  have hpow : 0 < (B / Λ) ^ m := by positivity
  rw [div_lt_one hpow] at h
  have hBm : (4 : ℝ) ^ (((m : ℝ) - 1) / ε) = B ^ m / B := by
    rw [show ((m : ℝ) - 1) / ε = (1 / ε) * m - 1 / ε by ring, Real.rpow_sub (by norm_num),
      Real.rpow_mul (by norm_num), Real.rpow_natCast]
  rw [hBm] at hN
  refine le_trans ?_ hN
  rw [le_div_iff₀ hB, div_pow] at *
  rw [lt_div_iff₀ (by positivity)] at h
  have : 75 * (c * m + 2) * Λ ^ m * B = 75 * (c * m + 2) * B * Λ ^ m := by ring
  nlinarith [pow_pos hΛ0 m]

/-! ## Theorem 7.4: the choice of parameters; Proposition 8.1 -/

lemma RPrime_eq (c γ : ℝ) : RPrime c γ = Real.log 4 / (lnL0 c + γ * Real.log 4) := by
  rw [RPrime, log_LambdaC_eq_lnL0]

theorem proposition_8_1_range : Proposition_8_1_range := by
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro c γ hc hγ
    rw [RPrime_eq, epsStar5]
    have := lnL0_gt hc
    exact div_lt_div_of_pos_left h4 (by positivity) (by nlinarith)
  · intro ε hε
    have hev := (corollary_7_3_limit.2.2).eventually (lt_mem_nhds hε)
    obtain ⟨c, hc, hc5⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨c, hc5, hc⟩
  · intro c hc
    rw [rhoC, div_lt_one (by linarith)]
    constructor <;> intro h <;> linarith

lemma tendsto_qOf_zero : Tendsto qOf (𝓝[>] 0) (𝓝 0) := by
  have : Continuous qOf := by
    unfold qOf
    exact (H_continuous.add (continuous_id.mul continuous_const)).div_const _
  have h := this.tendsto 0
  simp only [qOf, H_zero, zero_mul, add_zero, zero_div] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem theorem_7_4_parameters : Theorem_7_4_parameters := by
  intro ε q hε hq
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  obtain ⟨c, hc5, hc⟩ := proposition_8_1_range.2.1 ε hε
  have hL : 0 < lnL0 c := by
    have := lnL0_gt hc5
    have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    nlinarith
  -- `R'_c(γ(θ)) → R'_c(0)` as `θ → 0`
  have hcontR : Tendsto (fun θ => RPrime c (gammaOf c θ)) (𝓝 0) (𝓝 (RPrime c 0)) := by
    simp only [RPrime_eq, gammaOf]
    have : Tendsto (fun θ : ℝ => lnL0 c + θ * Real.logb 2 ((c - 1) / 4) * Real.log 4) (𝓝 0)
        (𝓝 (lnL0 c + 0 * Real.log 4)) := by
      have hc : Continuous (fun θ : ℝ => lnL0 c + θ * Real.logb 2 ((c - 1) / 4) * Real.log 4) := by
        fun_prop
      simpa using hc.tendsto 0
    exact tendsto_const_nhds.div this (by simp; exact hL.ne')
  have e1 := (hcontR.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))).eventually (lt_mem_nhds hc)
  have e2 := tendsto_qOf_zero.eventually (gt_mem_nhds (show (0 : ℝ) < q / 2 by linarith))
  have e3 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < 0.8 :=
    eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (by norm_num))
  obtain ⟨θ, ⟨⟨h1, h2⟩, h3⟩, hθ⟩ := ((e1.and e2).and e3 |>.and self_mem_nhdsWithin).exists
  exact ⟨c, θ, hc5, hθ, h3, h2, h1, corollary_7_3_gamma_pos c θ hc5 hθ⟩

theorem proposition_8_1_terms : Proposition_8_1_terms := by
  have key : ∀ (a b m : ℕ), 1 ≤ b → ((a + 1) ^ ((b + 1) * m) : ℝ) / ((b + 1) * m + 1)
      ≤ ((((b + 1) * m).choose m : ℕ) : ℝ) * a ^ (a * m) → True := fun _ _ _ _ _ => trivial
  clear key
  have lower : ∀ (r m : ℕ), ((r + 1 : ℕ) : ℝ) ^ ((r + 1) * m) / (((r + 1) * m : ℕ) + 1)
      ≤ (((r + 1) * m).choose m : ℝ) * (r : ℝ) ^ (r * m) := by
    intro r m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    have h := NatChoose.pow_self_le_mul_choose_mul_pow_mul_pow
      (n := (r + 1) * m) (k := m) (by nlinarith)
    have hsub : (r + 1) * m - m = r * m := by rw [add_mul, one_mul]; omega
    rw [hsub] at h
    -- divide by `m^{(r+1)m}`
    have hfac : ((r + 1) * m) ^ ((r + 1) * m) = (r + 1) ^ ((r + 1) * m) * m ^ ((r + 1) * m) :=
      mul_pow _ _ _
    have hfac2 : m ^ m * (r * m) ^ (r * m) = r ^ (r * m) * m ^ ((r + 1) * m) := by
      rw [mul_pow, show (r + 1) * m = m + r * m by ring, pow_add]; ring
    have hm' : 0 < m ^ ((r + 1) * m) := pow_pos hm _
    have h' : (r + 1) ^ ((r + 1) * m) * m ^ ((r + 1) * m)
        ≤ ((r + 1) * m + 1) * ((r + 1) * m).choose m * r ^ (r * m) * m ^ ((r + 1) * m) := by
      calc (r + 1) ^ ((r + 1) * m) * m ^ ((r + 1) * m) = ((r + 1) * m) ^ ((r + 1) * m) := hfac.symm
        _ ≤ ((r + 1) * m + 1) * (((r + 1) * m).choose m * m ^ m * (r * m) ^ (r * m)) := h
        _ = ((r + 1) * m + 1) * ((r + 1) * m).choose m * r ^ (r * m) * m ^ ((r + 1) * m) := by
            rw [mul_assoc (((r + 1) * m).choose m), hfac2]; ring
    have h'' := Nat.le_of_mul_le_mul_right h' hm'
    rw [div_le_iff₀ (by positivity)]
    have : (((r + 1) ^ ((r + 1) * m) : ℕ) : ℝ)
        ≤ ((((r + 1) * m + 1) * ((r + 1) * m).choose m * r ^ (r * m) : ℕ) : ℝ) := by
      exact_mod_cast h''
    push_cast at this ⊢
    linarith
  have upper : ∀ (r m : ℕ), (((r + 1) * m).choose m : ℝ) * (r : ℝ) ^ (r * m)
      ≤ ((r + 1 : ℕ) : ℝ) ^ ((r + 1) * m) := by
    intro r m
    have h := NatChoose.choose_mul_pow_le r ((r + 1) * m) m
    have hsub : (r + 1) * m - m = r * m := by rw [add_mul, one_mul]; omega
    rw [hsub] at h
    exact_mod_cast h
  refine ⟨fun m => ?_, fun m => ?_, fun m => ?_⟩
  · have l := lower 4 m; have u := upper 4 m
    norm_num at l u ⊢
    exact ⟨l, u⟩
  · have l := lower 9 m; have u := upper 9 m
    norm_num at l u ⊢
    exact ⟨l, u⟩
  · have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
    rw [Dr_rpow, epsStar5, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    field_simp
    push_cast
    ring

end ThinMatrixProducts

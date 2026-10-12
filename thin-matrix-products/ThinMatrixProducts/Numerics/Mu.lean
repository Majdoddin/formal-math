import Statements
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Field.ZMod

/-!
# The constants `μ_k` and `μ_∞` (Section 4) and `(25/4)/μ_∞² < 75` (equation (4))
-/

namespace ThinMatrixProducts

open Finset

lemma mu_zero : mu 0 = 1 := by simp [mu]

lemma mu_succ (k : ℕ) : mu (k + 1) = mu k * (1 - (2 : ℝ)⁻¹ ^ (k + 1)) := by
  rw [mu, prod_range_succ]; rfl

lemma one_sub_half_pow_pos (k : ℕ) : 0 < 1 - (2 : ℝ)⁻¹ ^ (k + 1) := by
  have : (2 : ℝ)⁻¹ ^ (k + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  linarith

lemma one_sub_half_pow_lt_one (k : ℕ) : 1 - (2 : ℝ)⁻¹ ^ (k + 1) < 1 := by
  have : (0 : ℝ) < (2 : ℝ)⁻¹ ^ (k + 1) := by positivity
  linarith

lemma mu_pos (k : ℕ) : 0 < mu k := by
  induction k with
  | zero => rw [mu_zero]; norm_num
  | succ k ih => rw [mu_succ]; exact mul_pos ih (one_sub_half_pow_pos k)

lemma mu_succ_lt (k : ℕ) : mu (k + 1) < mu k := by
  rw [mu_succ]
  exact mul_lt_of_lt_one_right (mu_pos k) (one_sub_half_pow_lt_one k)

lemma mu_antitone : Antitone mu := antitone_nat_of_succ_le fun k => (mu_succ_lt k).le

lemma mu_bddBelow : BddBelow (Set.range mu) := ⟨0, by rintro _ ⟨k, rfl⟩; exact (mu_pos k).le⟩

lemma muInf_le (k : ℕ) : muInf ≤ mu k := ciInf_le mu_bddBelow k

/-- `μ_{20+j} ≥ μ_20 (1 - 2^{-20} + 2^{-20-j})`: the tail of the product loses less than `2^{-20}`. -/
lemma mu_tail (j : ℕ) :
    mu 20 * (1 - (2 : ℝ)⁻¹ ^ 20 + (2 : ℝ)⁻¹ ^ (20 + j)) ≤ mu (20 + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 20 + (j + 1) = (20 + j) + 1 by omega, mu_succ (20 + j)]
    have hb : (2 : ℝ)⁻¹ ^ (20 + j + 1) = (2 : ℝ)⁻¹ ^ (20 + j) / 2 := by
      rw [pow_succ]; ring
    have h0 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (20 + j) := by positivity
    have h1 : (2 : ℝ)⁻¹ ^ (20 + j) ≤ (2 : ℝ)⁻¹ ^ 20 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hmu := mu_pos 20
    have hfac := one_sub_half_pow_pos (20 + j)
    calc mu 20 * (1 - (2 : ℝ)⁻¹ ^ 20 + (2 : ℝ)⁻¹ ^ (20 + j + 1))
        ≤ mu 20 * (1 - (2 : ℝ)⁻¹ ^ 20 + (2 : ℝ)⁻¹ ^ (20 + j)) * (1 - (2 : ℝ)⁻¹ ^ (20 + j + 1)) := by
          rw [hb]
          have : (1 - (2 : ℝ)⁻¹ ^ 20 + (2 : ℝ)⁻¹ ^ (20 + j) / 2)
              ≤ (1 - (2 : ℝ)⁻¹ ^ 20 + (2 : ℝ)⁻¹ ^ (20 + j)) * (1 - (2 : ℝ)⁻¹ ^ (20 + j) / 2) := by
            nlinarith
          nlinarith
      _ ≤ mu (20 + j) * (1 - (2 : ℝ)⁻¹ ^ (20 + j + 1)) :=
          mul_le_mul_of_nonneg_right ih hfac.le

/-- The lower bound `μ_k ≥ μ_20 (1 - 2^{-20})` for every `k`. -/
lemma mu_ge (k : ℕ) : mu 20 * (1 - (2 : ℝ)⁻¹ ^ 20) ≤ mu k := by
  rcases le_or_gt k 20 with hk | hk
  · calc mu 20 * (1 - (2 : ℝ)⁻¹ ^ 20) ≤ mu 20 :=
          mul_le_of_le_one_right (mu_pos 20).le (by norm_num)
      _ ≤ mu k := mu_antitone hk
  · obtain ⟨j, rfl⟩ : ∃ j, k = 20 + j := ⟨k - 20, by omega⟩
    refine le_trans ?_ (mu_tail j)
    have := mu_pos 20
    nlinarith [show (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ (20 + j) by positivity]

lemma le_muInf : mu 20 * (1 - (2 : ℝ)⁻¹ ^ 20) ≤ muInf := le_ciInf mu_ge

lemma mu_twenty_eq : mu 20 = ∏ i ∈ range 20, (1 - (2 : ℝ)⁻¹ ^ (i + 1)) := rfl

lemma mu_twenty_bounds : 0.28878836 < mu 20 ∧ mu 20 < 0.28878838 := by
  rw [mu_twenty_eq]; norm_num [prod_range_succ]

lemma muInf_bounds : 0.288787 < muInf ∧ muInf < 0.28878838 := by
  obtain ⟨h1, h2⟩ := mu_twenty_bounds
  constructor
  · refine lt_of_lt_of_le ?_ le_muInf
    have : (0.288787 : ℝ) < 0.28878836 * (1 - (2 : ℝ)⁻¹ ^ 20) := by norm_num
    nlinarith [show (0 : ℝ) < 1 - (2 : ℝ)⁻¹ ^ 20 by norm_num]
  · exact lt_of_le_of_lt (muInf_le 20) h2

theorem sec4_mu_values : Sec4_mu_values := by
  obtain ⟨h1, h2⟩ := muInf_bounds
  have hpos : 0 < muInf := by linarith
  refine ⟨?_, fun k => lt_of_le_of_lt (muInf_le (k + 1)) (mu_succ_lt k), by linarith,
    by linarith, by nlinarith, by nlinarith, ?_⟩
  · exact tendsto_atTop_ciInf mu_antitone mu_bddBelow
  · rw [div_lt_iff₀ (by positivity)]
    have : (0.288787 : ℝ) ^ 4 ≤ muInf ^ 4 := pow_le_pow_left₀ (by norm_num) h1.le 4
    nlinarith

theorem eq_4_constant : Eq_4_constant := by
  obtain ⟨h1, _⟩ := muInf_bounds
  unfold Eq_4_constant
  rw [div_lt_iff₀ (by positivity)]
  nlinarith

/-- `∏_{i<k} (2^k - 2^i) = 2^{k²} μ_k`. -/
lemma prod_two_pow_sub (k : ℕ) :
    (∏ i : Fin k, ((2 : ℝ) ^ k - 2 ^ (i : ℕ))) = 2 ^ (k ^ 2) * mu k := by
  rw [Fin.prod_univ_eq_prod_range (fun i => (2 : ℝ) ^ k - 2 ^ i) k, mu,
    ← prod_range_reflect (fun i => (1 - (2 : ℝ)⁻¹ ^ (i + 1))) k,
    show (2 : ℝ) ^ (k ^ 2) = ∏ _i ∈ range k, (2 : ℝ) ^ k by
      rw [prod_const, card_range, ← pow_mul, sq], ← prod_mul_distrib]
  refine prod_congr rfl fun i hi => ?_
  have hi : i < k := mem_range.1 hi
  rw [show k - 1 - i + 1 = k - i by omega]
  have : (2 : ℝ) ^ k = 2 ^ i * 2 ^ (k - i) := by rw [← pow_add]; congr 1; omega
  rw [this, inv_pow]
  field_simp

theorem sec4_mu_probability : Sec4_mu_probability := by
  intro k
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := card_linearIndependent (K := ZMod 2) (V := Fin k → ZMod 2) (k := k)
    (by simp)
  simp only [h, Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ZMod.card]
  rw [← prod_two_pow_sub k, Nat.cast_prod]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) i.2.le)]
  push_cast; rfl

end ThinMatrixProducts

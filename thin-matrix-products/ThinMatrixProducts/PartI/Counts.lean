import ThinMatrixProducts.PartI.Leaves
import ThinMatrixProducts.Util.Logs
import Mathlib.Algebra.Ring.GeomSum

/-!
# The counts of Theorem 7.2 and of the encodings (Section 5)
-/

namespace ThinMatrixProducts

open Finset

theorem theorem_7_2_boxes : Theorem_7_2_boxes := by
  intro L m t hm hL Kg hKg
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hL' : (5 : ℝ) * m ≤ L := by exact_mod_cast hL
  have hmL : m ≤ L := by omega
  have hden : (0 : ℝ) < (L : ℝ) - m + 1 := by linarith
  have hρ0 : 0 ≤ rho L m := by unfold rho; positivity
  have hρ1 : rho L m < 1 := by
    rw [rho, div_lt_one hden]; linarith
  refine ⟨hρ1, ?_⟩
  obtain ⟨-, -, hb, hM⟩ := lemma_6_1_b_bound hm hmL
  have hM' := hM Kg hKg
  set B := (Kg ^ 2 * (N0 L m : ℝ) ^ 2) / muInf ^ 4
  have hB0 : 0 ≤ B := by
    have := (muInf_bounds).1
    positivity
  -- each term: `β'_d ≤ (2m+1) ρ^d B`
  have hterm : ∀ d ∈ Icc t (2 * m), (beta' L m d : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) * (rho L m ^ d * B) := by
    intro d hd
    have hd2 : d ≤ 2 * m := (mem_Icc.1 hd).2
    have hd' : (d : ℝ) + 1 ≤ ((2 * m + 1 : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : d + 1 ≤ 2 * m + 1)
    calc (beta' L m d : ℝ) ≤ (d + 1) * rho L m ^ d * (beta L m 0 : ℝ) ^ 2 := hb d
      _ ≤ (d + 1) * rho L m ^ d * B := by
          apply mul_le_mul_of_nonneg_left (by simpa [B, mul_div_assoc] using hM')
          positivity
      _ ≤ ((2 * m + 1 : ℕ) : ℝ) * (rho L m ^ d * B) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right hd' (by positivity)
  -- the geometric tail
  have hgeom : (∑ d ∈ Icc t (2 * m), rho L m ^ d) ≤ rho L m ^ t / (1 - rho L m) := by
    rw [le_div_iff₀ (by linarith)]
    have : (∑ d ∈ Icc t (2 * m), rho L m ^ d) ≤ ∑ d ∈ range (2 * m + 1 - t), rho L m ^ (t + d) := by
      rcases le_or_gt t (2 * m) with ht | ht
      · apply le_of_eq
        rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
      · rw [Icc_eq_empty (by omega), sum_empty]
        exact sum_nonneg fun _ _ => pow_nonneg hρ0 _
    calc (∑ d ∈ Icc t (2 * m), rho L m ^ d) * (1 - rho L m)
        ≤ (∑ d ∈ range (2 * m + 1 - t), rho L m ^ (t + d)) * (1 - rho L m) :=
          mul_le_mul_of_nonneg_right this (by linarith)
      _ = rho L m ^ t * (1 - rho L m ^ (2 * m + 1 - t)) := by
          simp_rw [pow_add]
          rw [← mul_sum, mul_assoc, geom_sum_mul_neg]
      _ ≤ rho L m ^ t := by
          have : 0 ≤ rho L m ^ (2 * m + 1 - t) := pow_nonneg hρ0 _
          nlinarith [pow_nonneg hρ0 t]
  calc ((2 * m + 1 : ℕ) : ℝ) * (∑ d ∈ Icc t (2 * m), (beta' L m d : ℝ))
      ≤ ((2 * m + 1 : ℕ) : ℝ) * (∑ d ∈ Icc t (2 * m), ((2 * m + 1 : ℕ) : ℝ) * (rho L m ^ d * B)) :=
        mul_le_mul_of_nonneg_left (sum_le_sum hterm) (by positivity)
    _ = ((2 * m + 1 : ℕ) : ℝ) ^ 2 * (∑ d ∈ Icc t (2 * m), rho L m ^ d) * B := by
        rw [← mul_sum, ← sum_mul]; ring
    _ ≤ ((2 * m + 1 : ℕ) : ℝ) ^ 2 * (rho L m ^ t / (1 - rho L m)) * B := by
        apply mul_le_mul_of_nonneg_right _ hB0
        exact mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = _ := by simp only [B]; ring

theorem theorem_7_2_tiles : Theorem_7_2_tiles := by
  intro N B hB hBN
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hBN' : (B : ℝ) ≤ N := by exact_mod_cast hBN
  have hc : (⌈(N : ℝ) / B⌉₊ : ℝ) < N / B + 1 := Nat.ceil_lt_add_one (by positivity)
  have h1 : (⌈(N : ℝ) / B⌉₊ : ℝ) ≤ 2 * N / B := by
    have : (1 : ℝ) ≤ N / B := by rw [le_div_iff₀ hB']; linarith
    have e : 2 * (N : ℝ) / B = N / B + N / B := by ring
    linarith
  have h0 : (0 : ℝ) ≤ ⌈(N : ℝ) / B⌉₊ := Nat.cast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · calc (⌈(N : ℝ) / B⌉₊ * B : ℝ) ≤ 2 * N / B * B := mul_le_mul_of_nonneg_right h1 hB'.le
      _ = 2 * N := by field_simp
  · calc ((⌈(N : ℝ) / B⌉₊ : ℝ)) ^ 2 ≤ (2 * N / B) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * (N : ℝ) ^ 2 / (B : ℝ) ^ 2 := by ring
  · calc 2 * (⌈(N : ℝ) / B⌉₊ : ℝ) ≤ 2 * (2 * N / B) := by linarith
      _ = 4 * N / B := by ring

theorem theorem_7_2_hash_cost : Theorem_7_2_hash_cost := by
  intro L m N h2m hN
  have h1 : 2 ^ m ≤ 2 ^ (L - m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (L - m) ≤ N0 L m := by
    unfold N0; exact Nat.pow_le_pow_left (by norm_num) _
  have h3 : 2 ^ L ≤ N0 L m := by
    unfold N0
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨?_, h3, fun h => h3.trans h⟩
  calc K L m * (2 ^ m + 2 ^ (L - m)) ≤ K L m * (N0 L m + N0 L m) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add (h1.trans h2) h2)
    _ = 2 * (K L m * N0 L m) := by ring
    _ ≤ 2 * N := Nat.mul_le_mul_left _ hN

theorem sec7_word_size : Sec7_word_size := by
  refine ⟨fun L m hL N hN => ?_, fun L m => ?_⟩
  · have hN1 : (1 : ℝ) ≤ N := le_trans (one_le_pow₀ (by norm_num)) hN
    have hN0 : (0 : ℝ) < N := by linarith
    -- `25 ≤ 4^{2.328}` and `L - m ≥ 4L/5`
    have h25 : Real.log 25 ≤ 2.328 * Real.log 4 := by
      rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow, log_four_eq]
      have := log_five_lt'; have := log_two_gt'
      push_cast; nlinarith
    have hLm : (4 : ℝ) / 5 * L ≤ ((L - m : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      have : (5 : ℝ) * m ≤ L := by exact_mod_cast hL
      linarith
    have hlogN : ((L - m : ℕ) : ℝ) * Real.log 4 ≤ Real.log N := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hN
    rw [← Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hN0 _), Real.log_rpow hN0,
      Real.log_pow]
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith
  · calc L.choose m * 2 ^ L * 3 ^ L ≤ 2 ^ L * 2 ^ L * 3 ^ L := by
          apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right
          exact Nat.choose_le_two_pow L m
      _ = 12 ^ L := by rw [← mul_pow, ← mul_pow]; norm_num

theorem sec5_encodings : Sec5_encodings := by
  intro L
  have geom : ∀ x y : ℝ, (∑ k ∈ range (L + 1), x ^ k * y ^ (L - k)) * (x - y)
      = x ^ (L + 1) - y ^ (L + 1) := by
    intro x y
    rw [← geom_sum₂_mul, Nat.add_sub_cancel]
  constructor
  · have h := geom 5 4
    have hs : (∑ k ∈ range (L + 1), (5 : ℝ) ^ k * 4 ^ (L - k)) ≤ 5 ^ (L + 1) := by
      have : (5 : ℝ) - 4 = 1 := by norm_num
      rw [this, mul_one] at h
      rw [h]; linarith [pow_pos (show (0 : ℝ) < 4 by norm_num) (L + 1)]
    calc (∑ k ∈ range (L + 1), (5 : ℝ) ^ k * 4 ^ (L - k) * 3 ^ L)
        = (∑ k ∈ range (L + 1), (5 : ℝ) ^ k * 4 ^ (L - k)) * 3 ^ L := by rw [sum_mul]
      _ ≤ 5 ^ (L + 1) * 3 ^ L := mul_le_mul_of_nonneg_right hs (by positivity)
      _ = 5 * 15 ^ L := by rw [pow_succ, show (15 : ℝ) = 5 * 3 by norm_num, mul_pow]; ring
  · have h := geom 5 3
    have hs : (∑ k ∈ range (L + 1), (5 : ℝ) ^ k * 3 ^ (L - k)) ≤ 5 ^ (L + 1) / 2 := by
      rw [le_div_iff₀ (by norm_num), show (2 : ℝ) = 5 - 3 by norm_num, h]
      linarith [pow_pos (show (0 : ℝ) < 3 by norm_num) (L + 1)]
    calc (∑ k ∈ range (L + 1), (5 : ℝ) ^ (L + k) * 3 ^ (L - k))
        = 5 ^ L * (∑ k ∈ range (L + 1), (5 : ℝ) ^ k * 3 ^ (L - k)) := by
          rw [mul_sum]; refine sum_congr rfl fun k _ => ?_; rw [pow_add]; ring
      _ ≤ 5 ^ L * (5 ^ (L + 1) / 2) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 5 / 2 * 25 ^ L := by
          rw [pow_succ, show (25 : ℝ) = 5 * 5 by norm_num, mul_pow]; ring

end ThinMatrixProducts

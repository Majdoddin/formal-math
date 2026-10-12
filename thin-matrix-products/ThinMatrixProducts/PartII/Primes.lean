import Statements
import ThinMatrixProducts.Util.Logs
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Associated

/-!
# Section 12: the two lemmas on primes
-/

namespace ThinMatrixProducts

open Finset

/-! ## Lemma 12.2 (averaging) -/

/-- A nonzero integer has at most `log_P |z|` distinct prime divisors `≥ P` in a set of primes:
their product divides `z` and is at least `P` to the number of them. -/
lemma card_prime_dvd_le (P : ℕ) (hP : 2 ≤ P) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ P ≤ p)
    (z : ℤ) (hz : z ≠ 0) (Zmax : ℝ) (hZ : (|z| : ℝ) ≤ Zmax) :
    ((s.filter fun p : ℕ => (p : ℤ) ∣ z).card : ℝ) ≤ Real.logb P Zmax := by
  set t := s.filter fun p : ℕ => (p : ℤ) ∣ z
  have hdvd : (∏ p ∈ t, p) ∣ z.natAbs := by
    apply Finset.prod_primes_dvd
    · intro p hp; exact (Nat.prime_iff.1 (hs p (mem_filter.1 hp).1).1)
    · intro p hp; exact Int.natCast_dvd.1 (mem_filter.1 hp).2
  have hle : P ^ t.card ≤ ∏ p ∈ t, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' fun p hp => (hs p (mem_filter.1 hp).1).2
  have hpos : 0 < z.natAbs := Int.natAbs_pos.2 hz
  have h1 : (P : ℝ) ^ t.card ≤ |(z : ℝ)| := by
    have := (hle.trans (Nat.le_of_dvd hpos hdvd))
    have h' : ((P ^ t.card : ℕ) : ℝ) ≤ (z.natAbs : ℝ) := by exact_mod_cast this
    rw [Nat.cast_pow] at h'
    rwa [Nat.cast_natAbs, Int.cast_abs] at h'
  have hP' : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz
  rw [Real.le_logb_iff_rpow_le hP' (by linarith)]
  rw [Real.rpow_natCast]
  linarith

theorem lemma_12_2 : Lemma_12_2 := by
  intro P Zmax m Pl' 𝓕 hP hZ hm hne hPl h𝓕
  -- for `z ∈ 𝓕` and `p ∈ Π'`: `mp ∣ z ↔ p ∣ z`
  have hiff : ∀ z ∈ 𝓕, ∀ p ∈ Pl', (((m * p : ℕ) : ℤ) ∣ z ↔ (p : ℤ) ∣ z) := by
    intro z hz p hp
    obtain ⟨hpp, -, hpm⟩ := hPl p hp
    have hcop : Nat.Coprime m p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpm))
    constructor
    · intro h; exact (dvd_trans (by push_cast; exact dvd_mul_left _ _) h)
    · intro h
      have hmz := (h𝓕 z hz).2.2
      push_cast
      exact IsCoprime.mul_dvd (Int.isCoprime_iff_gcd_eq_one.2 (by simpa [Int.gcd] using hcop)) hmz h
  have hsum : ((∑ p ∈ Pl', 𝓕.countP fun z => ((m * p : ℕ) : ℤ) ∣ z : ℕ) : ℝ)
      ≤ 𝓕.card * Real.logb P Zmax := by
    induction 𝓕 using Multiset.induction_on with
    | empty => simp
    | cons z 𝓕 ih =>
      have ih' := ih (fun z hz => h𝓕 z (Multiset.mem_cons_of_mem hz))
        (fun z hz p hp => hiff z (Multiset.mem_cons_of_mem hz) p hp)
      have hz := h𝓕 z (Multiset.mem_cons_self z 𝓕)
      have hsplit : (∑ p ∈ Pl', Multiset.countP (fun z' => ((m * p : ℕ) : ℤ) ∣ z') (z ::ₘ 𝓕))
          = (∑ p ∈ Pl', Multiset.countP (fun z' => ((m * p : ℕ) : ℤ) ∣ z') 𝓕)
            + (Pl'.filter fun p : ℕ => (p : ℤ) ∣ z).card := by
        rw [Finset.card_filter, ← sum_add_distrib]
        refine sum_congr rfl fun p hp => ?_
        rw [Multiset.countP_cons]
        congr 1
        exact if_congr (hiff z (Multiset.mem_cons_self z 𝓕) p hp) rfl rfl
      have hcount := card_prime_dvd_le P hP Pl' (fun p hp => ⟨(hPl p hp).1, (hPl p hp).2.1⟩) z
        hz.1 Zmax hz.2.1
      rw [hsplit, Nat.cast_add, Multiset.card_cons, Nat.cast_add, Nat.cast_one]
      linarith
  refine ⟨hsum, ?_⟩
  have hc : (0 : ℝ) < Pl'.card := by exact_mod_cast hne.card_pos
  have : (∑ p ∈ Pl', ((𝓕.countP fun z => ((m * p : ℕ) : ℤ) ∣ z : ℕ) : ℝ))
      ≤ ∑ _p ∈ Pl', (𝓕.card * Real.logb P Zmax / Pl'.card) := by
    rw [sum_const, nsmul_eq_mul, mul_div_cancel₀ _ hc.ne']
    push_cast at hsum ⊢
    exact hsum
  exact Finset.exists_le_of_sum_le hne this

/-! ## Lemma 12.1 -/

lemma card_primesIn (P : ℕ) :
    (primesIn P).card = Nat.count Nat.Prime (2 * P) - Nat.count Nat.Prime P := by
  rw [primesIn, Nat.count_eq_card_filter_range, Nat.count_eq_card_filter_range,
    ← Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega)))]
  congr 1
  ext p
  simp only [mem_filter, mem_Ico, mem_sdiff, mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3⟩, fun h => by have := h.1; omega⟩
  · rintro ⟨⟨h2, h3⟩, h4⟩; exact ⟨⟨by by_contra h; exact h4 ⟨by omega, h3⟩, h2⟩, h3⟩

theorem lemma_12_1 : Lemma_12_1 := by
  intro hRS P hP
  have hP' : (1024 : ℝ) ≤ P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := by linarith
  -- `π(2P) - π(P) ≤ #primes in [P, 2P)`
  have hcount : (Nat.primeCounting (2 * P) : ℝ) - Nat.primeCounting P ≤ (primesIn P).card := by
    rw [card_primesIn]
    have h2P : ¬ (2 * P).Prime := Nat.not_prime_mul (by norm_num) (by omega)
    have e1 : Nat.primeCounting (2 * P) = Nat.count Nat.Prime (2 * P) := by
      rw [Nat.primeCounting, Nat.primeCounting', Nat.count_succ, if_neg h2P, add_zero]
    have e2 : Nat.count Nat.Prime P ≤ Nat.primeCounting P := by
      rw [Nat.primeCounting, Nat.primeCounting']; exact Nat.count_monotone _ (by omega)
    have e3 : Nat.count Nat.Prime P ≤ Nat.count Nat.Prime (2 * P) :=
      Nat.count_monotone _ (by omega)
    rw [e1, Nat.cast_sub e3]
    have : (Nat.count Nat.Prime P : ℝ) ≤ Nat.primeCounting P := by exact_mod_cast e2
    linarith
  have hlow := hRS.1 (2 * P) (by linarith)
  have hup := hRS.2 P (by linarith)
  rw [show ⌊(2 * P : ℝ)⌋₊ = 2 * P by exact_mod_cast Nat.floor_natCast (2 * P)] at hlow
  rw [Nat.floor_natCast] at hup
  -- `ln(2P) ≤ 1.1 ln P`
  have hlogP : 10 * Real.log 2 ≤ Real.log P := by
    have e : Real.log ((2 : ℝ) ^ 10) = 10 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← e]; exact Real.log_le_log (by norm_num) (by norm_num; linarith)
  have hl2 : Real.log (2 * P) = Real.log 2 + Real.log P := Real.log_mul (by norm_num) hPpos.ne'
  have hlp : 0 < Real.log P := by have := log_two_gt; linarith
  have hl2' : Real.log (2 * P) ≤ 1.1 * Real.log P := by rw [hl2]; linarith
  have hl2pos : 0 < Real.log (2 * P) := by rw [hl2]; have := log_two_gt; linarith
  have hA : 2 * (P : ℝ) / (1.1 * Real.log P) ≤ 2 * P / Real.log (2 * P) :=
    div_le_div_of_nonneg_left (by positivity) hl2pos hl2'
  have hB : (P : ℝ) / (2 * Real.log P) ≤ 2 * P / (1.1 * Real.log P) - 1.25506 * P / Real.log P := by
    rw [div_sub_div _ _ (by positivity) hlp.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hPpos hlp]
  push_cast at hlow
  linarith

end ThinMatrixProducts

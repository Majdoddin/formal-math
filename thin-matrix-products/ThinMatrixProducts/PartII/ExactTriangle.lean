import ThinMatrixProducts.PartII.ThreeSum
import Mathlib.Data.Nat.Log

/-!
# Section 15: Exact Triangle and its all-edges version — correctness, halving, counts; Lemma 15.13
-/

namespace ThinMatrixProducts

open Finset

variable {nA nB nC h : ℕ}

lemma zcnt_valE_pos_iff (T : ETInst nA nB nC) (piece : Fin nC → Fin h)
    (x : Fin nA × Fin nB × Fin h) :
    0 < zcnt (valE T piece) x ↔ ∃ c, piece c = x.2.2 ∧ T.S x.1 x.2.1 c = 0 := by
  rw [zcnt, valE, Multiset.countP_pos]
  simp only [Multiset.mem_map, Finset.mem_val, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, h0⟩; exact ⟨c, hc, h0⟩
  · rintro ⟨c, hc, h0⟩; exact ⟨_, ⟨c, hc, rfl⟩, h0⟩

theorem lemma_15_9 : Lemma_15_9 := by
  intro nA nB nC h T piece M hM L
  rw [(lemma_13_10_abstract (valE T piece) M hM L univ).1]
  constructor
  · rintro ⟨x, -, hz⟩
    obtain ⟨c, -, h0⟩ := (zcnt_valE_pos_iff T piece x).1 hz
    exact ⟨x.1, x.2.1, c, h0⟩
  · rintro ⟨a, b, c, h0⟩
    exact ⟨(a, b, piece c), mem_univ _, (zcnt_valE_pos_iff T piece _).2 ⟨c, rfl, h0⟩⟩

/-- The weights `S(a, b, c)` are bounded by `3U`. -/
lemma abs_S_le (T : ETInst nA nB nC) (U : ℕ) (hab : ∀ a b, |T.wab a b| ≤ U)
    (hbc : ∀ b c, |T.wbc b c| ≤ U) (hac : ∀ a c, |T.wac a c| ≤ U) (a : Fin nA) (b : Fin nB)
    (c : Fin nC) : |T.S a b c| ≤ 3 * U := by
  unfold ETInst.S
  have h1 := hab a b; have h2 := hbc b c; have h3 := hac a c
  calc |T.wab a b + T.wbc b c + T.wac a c| ≤ |T.wab a b + T.wbc b c| + |T.wac a c| := abs_add_le _ _
    _ ≤ |T.wab a b| + |T.wbc b c| + |T.wac a c| := by gcongr; exact abs_add_le _ _
    _ ≤ 3 * U := by linarith

lemma valE_bound (T : ETInst nA nB nC) (piece : Fin nC → Fin h) (U : ℕ)
    (hab : ∀ a b, |T.wab a b| ≤ U) (hbc : ∀ b c, |T.wbc b c| ≤ U) (hac : ∀ a c, |T.wac a c| ≤ U)
    (x : Fin nA × Fin nB × Fin h) : ∀ v ∈ valE T piece x, (|v| : ℝ) ≤ 3 * U := by
  intro v hv
  simp only [valE, Multiset.mem_map, Finset.mem_val, mem_filter] at hv
  obtain ⟨c, -, rfl⟩ := hv
  exact_mod_cast abs_S_le T U hab hbc hac _ _ _

/-- `F_𝓘(1) ≤ σ |𝓘|`. -/
lemma FsumE_one_le (T : ETInst nA nB nC) (piece : Fin nC → Fin h) (σ : ℕ)
    (hσ : ∀ k, (univ.filter fun c => piece c = k).card ≤ σ) (S : Finset (Fin nA × Fin nB × Fin h)) :
    Fsum (valE T piece) S 1 ≤ σ * S.card := by
  rw [Fsum, card_eq_sum_ones, mul_sum]
  refine sum_le_sum fun x _ => ?_
  calc fcnt (valE T piece) 1 x ≤ (valE T piece x).card := Multiset.countP_le_card _ _
    _ = (univ.filter fun c => piece c = x.2.2).card := by rw [valE, Multiset.card_map, card_val]
    _ ≤ σ * 1 := by rw [mul_one]; exact hσ _

/-- `(4ζ/P)^r ≤ 1/A` from `P ≥ 4ζ A^{1/r}`. -/
lemma pow_le_inv_of_root {ζ P A : ℝ} {r : ℕ} (hζ : 0 < ζ) (hP : 0 < P) (hA : 0 < A) (hr : 1 ≤ r)
    (h : 4 * ζ * A ^ (1 / (r : ℝ)) ≤ P) : (4 * ζ / P) ^ r ≤ 1 / A := by
  have hB : (0 : ℝ) < A ^ (1 / (r : ℝ)) := by positivity
  have h4 : 4 * ζ / P ≤ 1 / A ^ (1 / (r : ℝ)) := by
    rw [div_le_div_iff₀ hP hB]; linarith
  calc (4 * ζ / P) ^ r ≤ (1 / A ^ (1 / (r : ℝ))) ^ r := pow_le_pow_left₀ (by positivity) h4 r
    _ = 1 / A := by
        have hr' : (r : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ r := by exact_mod_cast hr
                                     linarith
        rw [div_pow, one_pow, ← Real.rpow_natCast, ← Real.rpow_mul hA.le,
          show 1 / (r : ℝ) * r = 1 by field_simp, Real.rpow_one]

theorem lemma_15_8 : Lemma_15_8 := by
  intro nA nB nC h T piece U σ P r Pl S ps hU hab hbc hac hσ1 hσ hP hPl hcard hr hr1 hPb hlen hgr
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hZ : (2 : ℝ) ≤ 3 * U := by linarith
  have hg := lemma_13_9_greedy (valE T piece) S Pl P r (3 * U) ps hP hZ
    (fun x _ => valE_bound T piece U hab hbc hac x) hPl hcard hr hlen hgr
  have h1 := FsumE_one_le T piece σ hσ S
  have hσ' : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hl : 0 < Real.log (3 * U) := Real.log_pos (by linarith)
  have hκ := pow_le_inv_of_root hl hP0 (by positivity : (0 : ℝ) < 2 * σ) hr1 hPb
  calc (Fsum (valE T piece) S ps.prod : ℝ)
      ≤ Fsum (valE T piece) S 1 * (4 * Real.log (3 * U) / P) ^ r := hg
    _ ≤ (σ * S.card : ℕ) * (1 / (2 * (σ : ℝ))) :=
        mul_le_mul (by exact_mod_cast h1) hκ (by positivity) (by positivity)
    _ = S.card / 2 := by push_cast; field_simp

/-- Section 15.4: the number of distinct prime divisors `≥ P` of a nonzero integer of absolute
value at most `3U` is at most `ℓ = Nat.log P (3U)`, and `ℓ ≤ ln(3U)/ln P`. -/
theorem sec15_ell : Sec15_ell := by
  intro U P Pl v hU hP hPl hv0 hv
  set t := Pl.filter fun p : ℕ => (p : ℤ) ∣ v
  have hdvd : (∏ p ∈ t, p) ∣ v.natAbs := by
    apply Finset.prod_primes_dvd
    · intro p hp; exact (Nat.prime_iff.1 (hPl p (mem_filter.1 hp).1).1)
    · intro p hp; exact Int.natCast_dvd.1 (mem_filter.1 hp).2
  have hle : P ^ t.card ≤ ∏ p ∈ t, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod' fun p hp => (hPl p (mem_filter.1 hp).1).2
  have hpos : 0 < v.natAbs := Int.natAbs_pos.2 hv0
  have hv' : v.natAbs ≤ 3 * U := by
    have : (v.natAbs : ℤ) ≤ 3 * U := by rw [Int.natCast_natAbs]; exact_mod_cast hv
    exact_mod_cast this
  refine ⟨Nat.le_log_of_pow_le (by omega) (hle.trans ((Nat.le_of_dvd hpos hdvd).trans hv')), ?_⟩
  have hpow := Nat.pow_log_le_self P (show 3 * U ≠ 0 by omega)
  have hPr : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  rw [le_div_iff₀ (Real.log_pos hPr), ← Real.log_pow]
  have : ((P ^ Nat.log P (3 * U) : ℕ) : ℝ) ≤ ((3 * U : ℕ) : ℝ) := by exact_mod_cast hpow
  push_cast at this
  exact Real.log_le_log (by positivity) this

/-- The values of an incidence have at most `ℓ` prime divisors in a pool of primes `≥ P`. -/
lemma prime_divisors_le (T : ETInst nA nB nC) (piece : Fin nC → Fin h) (U P ℓ : ℕ) (hU : 1 ≤ U)
    (hab : ∀ a b, |T.wab a b| ≤ U) (hbc : ∀ b c, |T.wbc b c| ≤ U) (hac : ∀ a c, |T.wac a c| ≤ U)
    (hP : 2 ≤ P) (hℓ : Nat.log P (3 * U) ≤ ℓ) (Pl' : Finset ℕ)
    (hPl : ∀ p ∈ Pl', p.Prime ∧ P ≤ p) (x : Fin nA × Fin nB × Fin h) :
    ∀ v ∈ valE T piece x, v ≠ 0 → (Pl'.filter fun p : ℕ => (p : ℤ) ∣ v).card ≤ ℓ := by
  intro v hv hv0
  have hb : |v| ≤ 3 * U := by
    have := valE_bound T piece U hab hbc hac x v hv
    exact_mod_cast this
  exact le_trans (sec15_ell U P Pl' v hU hP hPl hv0 hb).1 hℓ

theorem lemma_15_12 : Lemma_15_12 := by
  intro nA nB nC h T piece U P ℓ M Pool hU hab hbc hac hP hℓ hMP L a b
  have habs := lemma_15_12_abstract (valE T piece) (fun x => (x.1, x.2.1)) M Pool ℓ
    (fun S => ⟨(hMP S).1, (hMP S).2.1, fun p hp => ⟨((hMP S).2.2 p hp).1, ((hMP S).2.2 p hp).2.2⟩,
      fun x _ => prime_divisors_le T piece U P ℓ hU hab hbc hac hP hℓ (Pool S)
        (fun p hp => ⟨((hMP S).2.2 p hp).1, ((hMP S).2.2 p hp).2.1⟩) x⟩) L univ (a, b)
  rw [habs]
  constructor
  · rintro ⟨x, -, hx, hz⟩
    obtain ⟨c, -, h0⟩ := (zcnt_valE_pos_iff T piece x).1 hz
    simp only [Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact ⟨c, h0⟩
  · rintro ⟨c, h0⟩
    exact ⟨(a, b, piece c), mem_univ _, rfl, (zcnt_valE_pos_iff T piece _).2 ⟨c, rfl, h0⟩⟩

theorem lemma_15_11_ET : Lemma_15_11_ET := by
  intro nA nB nC h T piece U σ P r ℓ Pl S ps hU hab hbc hac hσ1 hσ hP hPl hcard hr hr1 hℓ h8
    hPb hlen hgr
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hZ : (2 : ℝ) ≤ 3 * U := by linarith
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hPr : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  have hlogP : 0 < Real.log P := Real.log_pos hPr
  have hl : 0 < Real.log (3 * U) := Real.log_pos (by linarith)
  have hσ' : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  have hℓ' : (ℓ : ℝ) ≤ Real.log (3 * U) / Real.log P := by
    rw [hℓ]
    exact (sec15_ell U P ∅ 1 hU hP (by simp) one_ne_zero (by rw [abs_one]; omega)).2
  -- the `r - 1` greedy steps
  have hr' : ((r - 1 : ℕ) : ℝ) ≤ P / (4 * Real.log P) := by
    have : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
    linarith
  have hg := lemma_13_9_greedy (valE T piece) S Pl P (r - 1) (3 * U) ps hP hZ
    (fun x _ => valE_bound T piece U hab hbc hac x) hPl hcard hr' hlen hgr
  have h1 := FsumE_one_le T piece σ hσ S
  have hF : (Fsum (valE T piece) S ps.prod : ℝ)
      ≤ σ * S.card * (4 * Real.log (3 * U) / P) ^ (r - 1) := by
    calc (Fsum (valE T piece) S ps.prod : ℝ)
        ≤ Fsum (valE T piece) S 1 * (4 * Real.log (3 * U) / P) ^ (r - 1) := hg
      _ ≤ (σ * S.card : ℕ) * (4 * Real.log (3 * U) / P) ^ (r - 1) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast h1) (by positivity)
      _ = σ * S.card * (4 * Real.log (3 * U) / P) ^ (r - 1) := by push_cast; ring
  obtain ⟨hnd, hmem, -⟩ := hgr
  have hprimes : ∀ q ∈ ps, q.Prime := fun q hq => (hPl q (hmem q hq)).1
  -- the pool of the certification round
  set Pool := Pl.filter fun p => p ∉ ps with hPool
  have hPoolcard : (P : ℝ) / (4 * Real.log P) ≤ Pool.card := by
    have h1 : Pl.card ≤ Pool.card + ps.length := by
      have := Finset.card_filter_add_card_filter_not (s := Pl) (fun p => p ∉ ps)
      rw [← hPool] at this
      have h2 : (Pl.filter fun p => ¬ (p ∉ ps)).card ≤ ps.length := by
        calc (Pl.filter fun p => ¬ (p ∉ ps)).card ≤ ps.toFinset.card := by
              apply card_le_card
              intro p hp
              simp only [mem_filter, not_not] at hp
              exact List.mem_toFinset.2 hp.2
          _ ≤ ps.length := List.toFinset_card_le _
      omega
    have hlen' : (ps.length : ℝ) ≤ r := by rw [hlen]; exact_mod_cast Nat.sub_le r 1
    have : (Pl.card : ℝ) ≤ Pool.card + ps.length := by exact_mod_cast h1
    have e : (P : ℝ) / (2 * Real.log P) = P / (4 * Real.log P) + P / (4 * Real.log P) := by
      field_simp; ring
    linarith
  have hPoolne : Pool.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < Pool.card := lt_of_lt_of_le (by positivity) hPoolcard
    exact_mod_cast this
  have hPoolp : ∀ p ∈ Pool, p.Prime ∧ ¬ p ∣ ps.prod := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
    exact ⟨(hPl p hp1).1, not_dvd_prod_of_not_mem (hPl p hp1).1 ps hprimes hp2⟩
  have hκ := pow_le_inv_of_root hl hP0 (by positivity : (0 : ℝ) < 4 * σ) hr1 hPb
  exact lemma_15_11 (valE T piece) S ps.prod Pool ℓ r P σ (Real.log (3 * U))
    (one_le_prod_primes ps hprimes) hPoolne hPoolp hr1 hP hl (by positivity)
    (fun x _ => prime_divisors_le T piece U P ℓ hU hab hbc hac hP hℓ.symm.le Pool
      (fun p hp => ⟨(hPl p (mem_filter.1 hp).1).1, (hPl p (mem_filter.1 hp).1).2⟩) x)
    hF hPoolcard hℓ' h8 hκ

theorem lemma_15_5 : Lemma_15_5 := by
  intro nA nB nC T m _ Ck ϱ a b hϱ
  -- for each `c` there is exactly one `λ` with both edges iff `S(a,b,c) ≡ 0`
  rw [card_eq_sum_card_fiberwise (f := fun cl : Fin nC × ZMod m => cl.1) (t := Ck)
    (fun cl hcl => (mem_product.1 (mem_filter.1 hcl).1).1), card_filter]
  refine sum_congr rfl fun c hc => ?_
  have key : ((m : ℤ) ∣ T.S a b c) ↔
      ((T.wac a c : ℤ) : ZMod m) + ϱ = -((T.wbc b c : ℤ) : ZMod m) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← hϱ]
    unfold ETInst.S
    push_cast
    constructor <;> intro h <;> linear_combination h
  by_cases hS : (m : ℤ) ∣ T.S a b c
  · rw [if_pos hS, card_eq_one]
    refine ⟨(c, ((T.wac a c : ℤ) : ZMod m) + ϱ), ?_⟩
    ext ⟨c', l⟩
    simp only [mem_filter, mem_product, mem_univ, and_true, mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨-, h1, -⟩, rfl⟩; exact ⟨rfl, h1⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨⟨hc, rfl, (key.1 hS)⟩, rfl⟩
  · rw [if_neg hS, card_eq_zero, filter_eq_empty_iff]
    rintro ⟨c', l⟩ hcl hcc
    obtain ⟨-, h1, h2⟩ := mem_filter.1 hcl
    simp only at hcc h1 h2
    subst hcc
    exact hS (key.2 (h1.symm.trans h2))

theorem lemma_15_13_test : Lemma_15_13_test := by
  intro n X Y i j t hn
  constructor
  · rintro ⟨k, hk⟩
    exact le_trans (Finset.min'_le _ _ (mem_image.2 ⟨k, mem_univ _, rfl⟩)) (by omega)
  · intro h
    obtain ⟨k, -, hk⟩ := mem_image.1 (Finset.min'_mem (univ.image fun k => X i k + Y k j)
      (by simp [Finset.univ_nonempty_iff]; exact ⟨⟨0, hn⟩⟩))
    exact ⟨k, by omega⟩

theorem lemma_15_13_search : Lemma_15_13_search := by
  intro U Z hZ1 hZ2 step
  -- with an interval of at most `2^k` values containing `Z`, `k` rounds end at `[Z, Z]`
  have key : ∀ k : ℕ, ∀ lo hi : ℤ, lo ≤ Z → Z ≤ hi → hi - lo + 1 ≤ 2 ^ k →
      step^[k] (lo, hi) = (Z, Z) := by
    intro k
    induction k with
    | zero =>
      intro lo hi h1 h2 h3
      simp only [pow_zero] at h3
      simp only [Function.iterate_zero, id_eq, Prod.mk.injEq]
      constructor <;> omega
    | succ k ih =>
      intro lo hi h1 h2 h3
      rw [Function.iterate_succ_apply]
      have hpow : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := by ring
      by_cases ht : Z ≤ (lo + hi) / 2
      · have : step (lo, hi) = (lo, (lo + hi) / 2) := by simp only [step, ht, if_true]
        rw [this]
        apply ih lo _ h1 ht
        omega
      · have : step (lo, hi) = ((lo + hi) / 2 + 1, hi) := by simp only [step, ht, if_false]
        rw [this]
        apply ih _ hi (by omega) h2
        omega
  apply key _ _ _ hZ1 hZ2
  have := Nat.le_pow_clog (by norm_num : 1 < 2) (4 * U + 1)
  have : ((4 * U + 1 : ℕ) : ℤ) ≤ ((2 ^ Nat.clog 2 (4 * U + 1) : ℕ) : ℤ) := by exact_mod_cast this
  push_cast at this
  omega

end ThinMatrixProducts

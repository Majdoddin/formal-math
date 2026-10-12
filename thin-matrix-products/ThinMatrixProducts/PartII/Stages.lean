import ThinMatrixProducts.PartII.Primes

/-!
# The stages of Sections 13 and 15, abstractly

An item has a multiset of values; its count modulo `m` is the number of values divisible by `m`,
which is the number of true solutions (values `0`) plus the number of false positives (nonzero
values divisible by `m`). Everything in the halving, correctness and certification lemmas of the
paper uses only this decomposition, Lemma 12.2, and the definition of the stages.
-/

namespace ThinMatrixProducts

open Finset

variable {ι : Type}

/-- `cnt_m(x) = z(x) + f_m(x)`. -/
lemma cnt_eq (val : ι → Multiset ℤ) (m : ℕ) (x : ι) :
    cnt val m x = zcnt val x + fcnt val m x := by
  unfold cnt zcnt fcnt
  induction val x using Multiset.induction_on with
  | empty => simp
  | cons v s ih =>
    simp only [Multiset.countP_cons]
    by_cases h0 : v = 0
    · subst h0; simp [ih]; omega
    · by_cases hm : (m : ℤ) ∣ v <;> simp [h0, hm, ih] <;> omega

/-- `Σ(m) = Z + F(m)`, with `Z` independent of `m`. -/
lemma Csum_eq (val : ι → Multiset ℤ) (S : Finset ι) (m : ℕ) :
    Csum val S m = (∑ x ∈ S, zcnt val x) + Fsum val S m := by
  rw [Csum, Fsum, ← sum_add_distrib]
  exact sum_congr rfl fun x _ => cnt_eq val m x

/-- The multiset of the false positives of `S` modulo `m`. -/
def fpMultiset (val : ι → Multiset ℤ) (S : Finset ι) (m : ℕ) : Multiset ℤ :=
  ∑ x ∈ S, (val x).filter fun v => v ≠ 0 ∧ (m : ℤ) ∣ v

lemma card_fpMultiset (val : ι → Multiset ℤ) (S : Finset ι) (m : ℕ) :
    (fpMultiset val S m).card = Fsum val S m := by
  rw [fpMultiset, Multiset.card_sum, Fsum]
  refine sum_congr rfl fun x _ => ?_
  rw [fcnt, Multiset.countP_eq_card_filter]

lemma countP_finset_sum (q : ℤ → Prop) [DecidablePred q] (S : Finset ι) (f : ι → Multiset ℤ) :
    (∑ x ∈ S, f x).countP q = ∑ x ∈ S, (f x).countP q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [sum_insert ha, sum_insert ha, Multiset.countP_add, ih]

/-- The false positives modulo `mp` are those modulo `m` that `mp` divides. -/
lemma countP_fpMultiset (val : ι → Multiset ℤ) (S : Finset ι) (m p : ℕ) :
    (fpMultiset val S m).countP (fun z => ((m * p : ℕ) : ℤ) ∣ z) = Fsum val S (m * p) := by
  rw [fpMultiset, countP_finset_sum, Fsum]
  refine sum_congr rfl fun x _ => ?_
  rw [Multiset.countP_filter, fcnt]
  have hd : ∀ v : ℤ, ((m * p : ℕ) : ℤ) ∣ v → (m : ℤ) ∣ v :=
    fun v h => dvd_trans (by push_cast; exact dvd_mul_right _ _) h
  congr 1
  funext v
  apply propext
  have := hd v
  tauto

/-- A prime of the pool that was not chosen does not divide the product of the chosen ones. -/
lemma not_dvd_prod_of_not_mem {p : ℕ} (hp : p.Prime) (l : List ℕ) (hl : ∀ q ∈ l, q.Prime)
    (hpl : p ∉ l) : ¬ p ∣ l.prod := by
  intro h
  obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).dvd_prod_iff.1 h
  have := (Nat.prime_dvd_prime_iff_eq hp (hl q hq)).1 hpq
  exact hpl (this ▸ hq)

lemma one_le_prod_primes (l : List ℕ) (hl : ∀ q ∈ l, q.Prime) : 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons]
    have ha := (hl a (List.mem_cons_self)).one_lt
    have := ih (fun q hq => hl q (List.mem_cons_of_mem a hq))
    nlinarith

theorem lemma_13_9_greedy : Lemma_13_9_greedy := by
  intro ι val S Pl P r Zmax ps hP hZ hval hPl hcard hr hlen hgr
  obtain ⟨hnd, hmem, hmin⟩ := hgr
  have hPr : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  have hlogP : 0 < Real.log P := Real.log_pos hPr
  have hP0 : (0 : ℝ) < P := by linarith
  have hlZ : 0 < Real.log Zmax := Real.log_pos (by linarith)
  set κ : ℝ := 4 * Real.log Zmax / P with hκ
  have hκ0 : 0 ≤ κ := by positivity
  -- the claim after `l` steps
  suffices h : ∀ l, l ≤ r → (Fsum val S (ps.take l).prod : ℝ) ≤ Fsum val S 1 * κ ^ l by
    have := h r le_rfl
    rwa [show List.take r ps = ps by rw [← hlen, List.take_length]] at this
  intro l
  induction l with
  | zero => intro _; simp
  | succ l ih =>
    intro hl
    have hl' : l < ps.length := by omega
    set m := (ps.take l).prod with hm
    have hprimes : ∀ q ∈ ps.take l, q.Prime := fun q hq => (hPl q (hmem q (List.mem_of_mem_take hq))).1
    have hm1 : 1 ≤ m := one_le_prod_primes _ hprimes
    -- the pool of the step
    set pool := Pl.filter fun p => p ∉ ps.take l with hpool
    have hpoolcard : (P : ℝ) / (4 * Real.log P) ≤ pool.card := by
      have h1 : Pl.card ≤ pool.card + (ps.take l).length := by
        have := Finset.card_filter_add_card_filter_not (s := Pl) (fun p => p ∉ ps.take l)
        rw [← hpool] at this
        have h2 : (Pl.filter fun p => ¬ (p ∉ ps.take l)).card ≤ (ps.take l).length := by
          calc (Pl.filter fun p => ¬ (p ∉ ps.take l)).card ≤ (ps.take l).toFinset.card := by
                apply card_le_card
                intro p hp
                simp only [mem_filter, not_not] at hp
                exact List.mem_toFinset.2 hp.2
            _ ≤ (ps.take l).length := List.toFinset_card_le _
        omega
      have hlen' : ((ps.take l).length : ℝ) ≤ r := by
        rw [List.length_take]; exact_mod_cast (by omega : min l ps.length ≤ r)
      have : (Pl.card : ℝ) ≤ pool.card + (ps.take l).length := by exact_mod_cast h1
      have e : (P : ℝ) / (2 * Real.log P) = P / (4 * Real.log P) + P / (4 * Real.log P) := by
        field_simp; ring
      linarith
    have hpoolne : pool.Nonempty := by
      rw [← Finset.card_pos]
      have : (0 : ℝ) < pool.card := lt_of_lt_of_le (by positivity) hpoolcard
      exact_mod_cast this
    -- Lemma 12.2 on the false positives modulo `m`
    obtain ⟨-, p, hp, hpbound⟩ := lemma_12_2 P Zmax m pool (fpMultiset val S m) hP hZ hm1 hpoolne
      (fun p hp => by
        obtain ⟨hp1, hp2⟩ := mem_filter.1 hp
        exact ⟨(hPl p hp1).1, (hPl p hp1).2,
          not_dvd_prod_of_not_mem (hPl p hp1).1 _ hprimes hp2⟩)
      (fun z hz => by
        rw [fpMultiset, Multiset.mem_sum] at hz
        obtain ⟨x, hx, hz⟩ := hz
        rw [Multiset.mem_filter] at hz
        exact ⟨hz.2.1, hval x hx z hz.1, hz.2.2⟩)
    rw [countP_fpMultiset, card_fpMultiset] at hpbound
    -- the greedy prime does as well as `p`
    have hgreedy : Fsum val S (m * ps[l]) ≤ Fsum val S (m * p) := by
      have := hmin l hl' p (mem_filter.1 hp).1 (mem_filter.1 hp).2
      rw [← hm, Csum_eq, Csum_eq] at this
      omega
    have htake : (ps.take (l + 1)).prod = m * ps[l] := by
      rw [List.take_succ, List.getElem?_eq_getElem hl', Option.toList_some, List.prod_append,
        List.prod_singleton]
    rw [htake]
    -- `log_P Z_max / |pool| ≤ κ`
    have hfac : Real.logb P Zmax / pool.card ≤ κ := by
      have hpc : (0 : ℝ) < pool.card := lt_of_lt_of_le (by positivity) hpoolcard
      rw [div_le_iff₀ hpc, Real.logb, hκ]
      calc Real.log Zmax / Real.log P = 4 * Real.log Zmax / P * (P / (4 * Real.log P)) := by
            field_simp
        _ ≤ 4 * Real.log Zmax / P * pool.card := mul_le_mul_of_nonneg_left hpoolcard (by positivity)
    have hF0 : (0 : ℝ) ≤ Fsum val S m := Nat.cast_nonneg _
    calc (Fsum val S (m * ps[l]) : ℝ) ≤ Fsum val S (m * p) := by exact_mod_cast hgreedy
      _ ≤ Fsum val S m * Real.logb P Zmax / pool.card := hpbound
      _ = Fsum val S m * (Real.logb P Zmax / pool.card) := by ring
      _ ≤ Fsum val S m * κ := mul_le_mul_of_nonneg_left hfac hF0
      _ ≤ Fsum val S 1 * κ ^ l * κ := mul_le_mul_of_nonneg_right (ih (by omega)) hκ0
      _ = Fsum val S 1 * κ ^ (l + 1) := by ring

theorem lemma_13_9_stage : Lemma_13_9_stage := by
  intro ι val S M hF
  constructor
  · intro hC
    rw [Csum_eq] at hC
    by_contra hno
    push_neg at hno
    have : ∑ x ∈ S, zcnt val x = 0 := sum_eq_zero fun x hx => by have := hno x hx; omega
    rw [this] at hC
    push_cast at hC
    linarith
  · intro hC
    push_neg at hC
    calc ((S.filter fun x => 0 < cnt val M x).card : ℝ)
        ≤ Csum val S M := by
          have : (S.filter fun x => 0 < cnt val M x).card ≤ Csum val S M := by
            rw [Csum, card_eq_sum_ones, sum_filter]
            exact sum_le_sum fun x _ => by split_ifs with h <;> omega
          exact_mod_cast this
      _ ≤ S.card / 2 := hC

theorem lemma_13_10_abstract : Lemma_13_10_abstract := by
  intro ι val M hM k
  induction k with
  | zero =>
    intro S
    refine ⟨by simp [detect], fun _ => by simp [survivors]⟩
  | succ k ih =>
    intro S
    have hst := lemma_13_9_stage val S (M S) (hM S)
    have hkeep : (∃ x ∈ S, 0 < zcnt val x) ↔
        ∃ x ∈ S.filter (fun x => 0 < cnt val (M S) x), 0 < zcnt val x := by
      constructor
      · rintro ⟨x, hx, hz⟩
        refine ⟨x, mem_filter.2 ⟨hx, ?_⟩, hz⟩
        rw [cnt_eq]; omega
      · rintro ⟨x, hx, hz⟩; exact ⟨x, (mem_filter.1 hx).1, hz⟩
    constructor
    · simp only [detect]
      by_cases h0 : S.card = 0
      · rw [if_pos h0]
        rw [card_eq_zero] at h0
        simp [h0]
      · rw [if_neg h0]
        by_cases hC : (S.card : ℝ) / 2 < Csum val S (M S)
        · rw [if_pos hC]; simpa using hst.1 hC
        · rw [if_neg hC, (ih _).1, ← hkeep]
    · intro hcont
      have h0 := hcont 0 (by omega)
      simp only [survivors] at h0
      have hS' := hst.2 h0
      have hcont' : ∀ j < k, ¬ ((survivors val M j (S.filter fun x => 0 < cnt val (M S) x)).card : ℝ) / 2
          < Csum val (survivors val M j (S.filter fun x => 0 < cnt val (M S) x))
            (M (survivors val M j (S.filter fun x => 0 < cnt val (M S) x))) := by
        intro j hj
        have := hcont (j + 1) (by omega)
        simpa [survivors] using this
      have := (ih _).2 hcont'
      simp only [survivors]
      calc ((survivors val M k (S.filter fun x => 0 < cnt val (M S) x)).card : ℝ)
          ≤ (S.filter fun x => 0 < cnt val (M S) x).card / 2 ^ k := this
        _ ≤ (S.card / 2) / 2 ^ k := div_le_div_of_nonneg_right hS' (by positivity)
        _ = S.card / 2 ^ (k + 1) := by rw [pow_succ]; ring

/-! ## Certification (Section 15.4) -/

/-- `∑_{p ∈ Π'} f_{mp}(x) ≤ ℓ f_m(x)`. -/
lemma sum_fcnt_le (val : ι → Multiset ℤ) (m : ℕ) (Pl' : Finset ℕ) (ℓ : ℕ) (x : ι)
    (hPl : ∀ p ∈ Pl', p.Prime ∧ ¬ p ∣ m)
    (hℓ : ∀ v ∈ val x, v ≠ 0 → (Pl'.filter fun p : ℕ => (p : ℤ) ∣ v).card ≤ ℓ) :
    ∑ p ∈ Pl', fcnt val (m * p) x ≤ ℓ * fcnt val m x := by
  unfold fcnt
  have hiff : ∀ p ∈ Pl', ∀ v : ℤ, (m : ℤ) ∣ v → (((m * p : ℕ) : ℤ) ∣ v ↔ (p : ℤ) ∣ v) := by
    intro p hp v hmv
    obtain ⟨hpp, hpm⟩ := hPl p hp
    have hcop : Nat.Coprime m p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpp).2 hpm)
    constructor
    · intro h; exact dvd_trans (by push_cast; exact dvd_mul_left _ _) h
    · intro h
      push_cast
      exact IsCoprime.mul_dvd (Int.isCoprime_iff_gcd_eq_one.2 (by simpa [Int.gcd] using hcop)) hmv h
  revert hℓ
  induction val x using Multiset.induction_on with
  | empty => simp
  | cons v s ih =>
    intro hℓ
    have ih' := ih (fun w hw => hℓ w (Multiset.mem_cons_of_mem hw))
    rw [Multiset.countP_cons, sum_congr rfl (fun p _ => Multiset.countP_cons _ _ _),
      sum_add_distrib]
    by_cases h0 : v = 0
    · have e1 : (∑ p ∈ Pl', if v ≠ 0 ∧ ((m * p : ℕ) : ℤ) ∣ v then 1 else 0) = 0 :=
        sum_eq_zero fun p _ => if_neg (fun h => h.1 h0)
      have e2 : (if v ≠ 0 ∧ (m : ℤ) ∣ v then 1 else 0) = 0 := if_neg (fun h => h.1 h0)
      rw [e1, e2, add_zero, add_zero]; exact ih'
    · by_cases hm : (m : ℤ) ∣ v
      · have hv := hℓ v (Multiset.mem_cons_self v s) h0
        have e1 : (∑ p ∈ Pl', if v ≠ 0 ∧ ((m * p : ℕ) : ℤ) ∣ v then 1 else 0)
            = (Pl'.filter fun p : ℕ => (p : ℤ) ∣ v).card := by
          rw [card_filter]
          refine sum_congr rfl fun p hp => if_congr ?_ rfl rfl
          rw [hiff p hp v hm]; exact ⟨fun h => h.2, fun h => ⟨h0, h⟩⟩
        have e2 : (if v ≠ 0 ∧ (m : ℤ) ∣ v then 1 else 0) = 1 := if_pos ⟨h0, hm⟩
        rw [e1, e2, mul_add, mul_one]
        omega
      · have e1 : (∑ p ∈ Pl', if v ≠ 0 ∧ ((m * p : ℕ) : ℤ) ∣ v then 1 else 0) = 0 := by
          refine sum_eq_zero fun p _ => if_neg ?_
          rintro ⟨-, h⟩
          exact hm (dvd_trans (by push_cast; exact dvd_mul_right _ _) h)
        have e2 : (if v ≠ 0 ∧ (m : ℤ) ∣ v then 1 else 0) = 0 := if_neg (fun h => hm h.2)
        rw [e1, e2, add_zero, add_zero]; exact ih'

theorem lemma_15_10 : Lemma_15_10 := by
  intro ι val m Pl' ℓ x hm hne hPl hℓ
  -- `μ(x) = z(x) + min_p f_{mp}(x)`
  set fmin := Pl'.inf' hne (fun p => fcnt val (m * p) x) with hfmin
  have hmu : muCert val m Pl' x = zcnt val x + fmin := by
    rw [muCert, dif_pos hne]
    simp_rw [cnt_eq]
    rw [hfmin]
    apply le_antisymm
    · obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_inf' hne (fun p => fcnt val (m * p) x)
      calc Pl'.inf' hne (fun p => zcnt val x + fcnt val (m * p) x)
          ≤ zcnt val x + fcnt val (m * p) x := Finset.inf'_le _ hp
        _ = zcnt val x + Pl'.inf' hne (fun p => fcnt val (m * p) x) := by rw [hpe]
    · apply Finset.le_inf'
      intro p hp
      have := Finset.inf'_le (fun p => fcnt val (m * p) x) hp
      omega
  -- `min_p f_{mp}(x) |Π'| ≤ ℓ f_m(x)`
  have hminsum : fmin * Pl'.card ≤ ℓ * fcnt val m x := by
    calc fmin * Pl'.card = ∑ _p ∈ Pl', fmin := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ p ∈ Pl', fcnt val (m * p) x := sum_le_sum fun p hp => Finset.inf'_le _ hp
      _ ≤ ℓ * fcnt val m x := sum_fcnt_le val m Pl' ℓ x hPl hℓ
  have hcard : 0 < Pl'.card := hne.card_pos
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · unfold CertFalse at h; omega
  · unfold CertTrue at h
    by_contra hz
    push_neg at hz
    have hz0 : zcnt val x = 0 := by omega
    rw [hmu, hz0, zero_add, cnt_eq, hz0, zero_add] at h
    omega
  · obtain ⟨hF, hT⟩ := h
    unfold CertFalse at hF
    unfold CertTrue at hT
    push_neg at hT
    rw [hmu, cnt_eq] at hT
    rw [hmu] at hF
    -- `(z + fmin) |Π'| ≤ ℓ (z + f_m)`
    have h1 : ((zcnt val x + fmin) * Pl'.card : ℤ) ≤ ℓ * (zcnt val x + fcnt val m x) := by
      exact_mod_cast hT
    have h2 : (fmin * Pl'.card : ℤ) ≤ ℓ * fcnt val m x := by exact_mod_cast hminsum
    by_cases hz : zcnt val x = 0
    · rw [hz] at h1 hF
      have : 1 ≤ fmin := by omega
      push_cast at h1
      nlinarith
    · have hz1 : (1 : ℤ) ≤ zcnt val x := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hz
      push_cast at h1
      have hf0 : (0 : ℤ) ≤ fmin * Pl'.card := by positivity
      -- `z |Π'| ≤ ℓ z + ℓ f_m`, so `ℓ f_m ≥ z (|Π'| - ℓ) ≥ |Π'| - ℓ` or `|Π'| < ℓ`
      by_cases hc : (ℓ : ℤ) ≤ Pl'.card
      · nlinarith
      · push_neg at hc
        have : (0 : ℤ) ≤ ℓ * fcnt val m x := by positivity
        linarith

theorem lemma_15_11 : Lemma_15_11 := by
  intro ι val S m Pl' ℓ r P σ ζ hm hne hPl hr hP hζ hσ hℓv hF hcard hℓ h8 hpow
  have hPr : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  have hlogP : 0 < Real.log P := Real.log_pos hPr
  have hP0 : (0 : ℝ) < P := by linarith
  set U := S.filter fun x => Uncert val m Pl' ℓ x
  have hc0 : (0 : ℝ) < Pl'.card := by exact_mod_cast hne.card_pos
  -- `ℓ ≤ |Π'|/2`
  have hℓhalf : (ℓ : ℝ) ≤ Pl'.card / 2 := by
    calc (ℓ : ℝ) ≤ ζ / Real.log P := hℓ
      _ ≤ P / (8 * Real.log P) := by
          rw [div_le_div_iff₀ hlogP (by positivity)]; nlinarith
      _ = (P / (4 * Real.log P)) / 2 := by field_simp; ring
      _ ≤ Pl'.card / 2 := by linarith
  -- each uncertified item has `ℓ f_m(x) ≥ |Π'| - ℓ`
  have hU : ((U.card : ℝ)) * (Pl'.card - ℓ) ≤ ℓ * Fsum val S m := by
    have hx : ∀ x ∈ U, ((Pl'.card : ℝ) - ℓ) ≤ ℓ * fcnt val m x := by
      intro x hx
      obtain ⟨hxS, hxU⟩ := mem_filter.1 hx
      have := (lemma_15_10 val m Pl' ℓ x hm hne hPl (hℓv x hxS)).2.2 hxU
      exact_mod_cast this
    calc (U.card : ℝ) * (Pl'.card - ℓ) = ∑ _x ∈ U, ((Pl'.card : ℝ) - ℓ) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ U, (ℓ : ℝ) * fcnt val m x := sum_le_sum hx
      _ ≤ ∑ x ∈ S, (ℓ : ℝ) * fcnt val m x :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => by positivity
      _ = ℓ * Fsum val S m := by rw [Fsum, Nat.cast_sum, mul_sum]
  have hdiff : (Pl'.card : ℝ) / 2 ≤ Pl'.card - ℓ := by linarith
  have hdiff0 : (0 : ℝ) < Pl'.card - ℓ := by linarith
  have hratio : (ℓ : ℝ) / (Pl'.card - ℓ) ≤ 8 * ζ / P := by
    rw [div_le_iff₀ hdiff0]
    calc (ℓ : ℝ) ≤ ζ / Real.log P := hℓ
      _ = 8 * ζ / P * (P / (8 * Real.log P)) := by field_simp
      _ ≤ 8 * ζ / P * (Pl'.card / 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc (P : ℝ) / (8 * Real.log P) = (P / (4 * Real.log P)) / 2 := by field_simp; ring
            _ ≤ Pl'.card / 2 := by linarith
      _ ≤ 8 * ζ / P * (Pl'.card - ℓ) := mul_le_mul_of_nonneg_left hdiff (by positivity)
  have hUle : (U.card : ℝ) ≤ 8 * ζ / P * Fsum val S m := by
    calc (U.card : ℝ) ≤ ℓ * Fsum val S m / (Pl'.card - ℓ) := by rw [le_div_iff₀ hdiff0]; exact hU
      _ = (ℓ / (Pl'.card - ℓ)) * Fsum val S m := by ring
      _ ≤ 8 * ζ / P * Fsum val S m := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg _)
  rcases eq_or_lt_of_le hσ with hσ0 | hσ0
  · -- `σ = 0`: no false positives at all
    rw [← hσ0] at hF
    simp only [zero_mul] at hF
    have : (Fsum val S m : ℝ) = 0 := le_antisymm hF (Nat.cast_nonneg _)
    rw [this, mul_zero] at hUle
    have h0 : (0 : ℝ) ≤ S.card / 2 := by positivity
    linarith
  · calc (U.card : ℝ) ≤ 8 * ζ / P * Fsum val S m := hUle
      _ ≤ 8 * ζ / P * (σ * S.card * (4 * ζ / P) ^ (r - 1)) :=
          mul_le_mul_of_nonneg_left hF (by positivity)
      _ = 2 * σ * S.card * (4 * ζ / P) ^ r := by
          obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
          rw [Nat.add_sub_cancel, pow_succ]; ring
      _ ≤ 2 * σ * S.card * (1 / (4 * σ)) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = S.card / 2 := by field_simp; ring

theorem lemma_15_12_abstract : Lemma_15_12_abstract := by
  intro ι α _ val pair M Pool ℓ hyp
  suffices h : ∀ (k : ℕ) (S : Finset ι) (marked : Finset α) (a : α),
      a ∈ allEdges val pair M Pool ℓ k S marked ↔ a ∈ marked ∨ ∃ x ∈ S, pair x = a ∧ 0 < zcnt val x by
    intro k S a
    rw [h]; simp
  intro k
  induction k with
  | zero =>
    intro S marked a
    simp only [allEdges, mem_union, mem_image, mem_filter]
    constructor
    · rintro (h | ⟨x, ⟨hx, hz⟩, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, rfl, hz⟩
    · rintro (h | ⟨x, hx, rfl, hz⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, ⟨hx, hz⟩, rfl⟩
  | succ k ih =>
    intro S marked a
    obtain ⟨hm, hne, hPl, hℓ⟩ := hyp S
    have cert := fun x (hx : x ∈ S) => lemma_15_10 val (M S) (Pool S) ℓ x hm hne hPl (hℓ x hx)
    set marked' := marked ∪ (S.filter fun x => CertTrue val (M S) (Pool S) ℓ x).image pair
      with hmarked'
    have hmem' : ∀ b, b ∈ marked' ↔ b ∈ marked ∨
        ∃ y, (y ∈ S ∧ CertTrue val (M S) (Pool S) ℓ y) ∧ pair y = b := by
      intro b
      rw [hmarked', Finset.mem_union, Finset.mem_image]
      simp only [Finset.mem_filter]
    show a ∈ allEdges val pair M Pool ℓ k
      (S.filter fun x => Uncert val (M S) (Pool S) ℓ x ∧ pair x ∉ marked') marked' ↔ _
    rw [ih, hmem']
    constructor
    · rintro ((h | ⟨x, ⟨hx, hT⟩, rfl⟩) | ⟨x, hx, rfl, hz⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x, hx, rfl, by have := (cert x hx).2.1 hT; omega⟩
      · exact Or.inr ⟨x, (Finset.mem_filter.1 hx).1, rfl, hz⟩
    · rintro (h | ⟨x, hx, rfl, hz⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hT : CertTrue val (M S) (Pool S) ℓ x
        · exact Or.inl (Or.inr ⟨x, ⟨hx, hT⟩, rfl⟩)
        · have hF : ¬ CertFalse val (M S) (Pool S) x := fun hF => by
            have := (cert x hx).1 hF; omega
          by_cases hmk : pair x ∈ marked'
          · exact Or.inl ((hmem' _).1 hmk)
          · exact Or.inr ⟨x, Finset.mem_filter.2 ⟨hx, ⟨hF, hT⟩, hmk⟩, rfl, hz⟩

end ThinMatrixProducts

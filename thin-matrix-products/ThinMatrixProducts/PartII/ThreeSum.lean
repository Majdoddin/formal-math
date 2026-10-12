import ThinMatrixProducts.PartII.Stages
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Bitwise

/-!
# Section 13: 3SUM — correctness, the stage bound, the counts, the variants, the splitting
-/

namespace ThinMatrixProducts

open Finset

/-! ## Lemma 13.10 -/

lemma zcnt_val3_pos_iff {g : ℕ} (A : Finset ℕ) (grp : ℕ → Fin g) (q : ℕ × Fin g × Fin g) :
    0 < zcnt (val3 A grp) q ↔ ∃ b ∈ grpSet A grp q.2.1, ∃ c ∈ grpSet A grp q.2.2, q.1 + b = c := by
  rw [zcnt, val3, Multiset.countP_pos]
  simp only [Multiset.mem_map, Finset.mem_val, mem_product]
  constructor
  · rintro ⟨_, ⟨⟨b, c⟩, ⟨hb, hc⟩, rfl⟩, h⟩
    exact ⟨b, hb, c, hc, by omega⟩
  · rintro ⟨b, hb, c, hc, h⟩
    exact ⟨_, ⟨⟨b, c⟩, ⟨hb, hc⟩, rfl⟩, by push_cast [← h]; ring⟩

theorem lemma_13_10 : Lemma_13_10 := by
  intro g A grp R hcov M hM L
  rw [(lemma_13_10_abstract (val3 A grp) M hM L (probes A grp R)).1]
  constructor
  · rintro ⟨q, hq, hz⟩
    obtain ⟨b, hb, c, hc, h⟩ := (zcnt_val3_pos_iff A grp q).1 hz
    have hqA : q.1 ∈ A := (mem_product.1 (mem_filter.1 hq).1).1
    exact ⟨q.1, hqA, b, (mem_filter.1 hb).1, c, (mem_filter.1 hc).1, h⟩
  · rintro ⟨a, ha, b, hb, c, hc, h⟩
    refine ⟨(a, grp b, grp c), ?_, ?_⟩
    · exact mem_filter.2 ⟨mem_product.2 ⟨ha, mem_univ _⟩, hcov a ha b hb c hc h⟩
    · exact (zcnt_val3_pos_iff A grp _).2
        ⟨b, mem_filter.2 ⟨hb, rfl⟩, c, mem_filter.2 ⟨hc, rfl⟩, h⟩

/-! ## Lemma 13.9 for 3SUM -/

/-- `F_𝒫(1) ≤ |𝒫| σ²`. -/
lemma Fsum_one_le {g : ℕ} (A : Finset ℕ) (grp : ℕ → Fin g) (σ : ℕ)
    (hσ : ∀ i, (grpSet A grp i).card ≤ σ) (S : Finset (ℕ × Fin g × Fin g)) :
    Fsum (val3 A grp) S 1 ≤ S.card * σ ^ 2 := by
  rw [Fsum, card_eq_sum_ones, sum_mul]
  refine sum_le_sum fun q _ => ?_
  calc fcnt (val3 A grp) 1 q ≤ (val3 A grp q).card := Multiset.countP_le_card _ _
    _ = (grpSet A grp q.2.1).card * (grpSet A grp q.2.2).card := by
        rw [val3, Multiset.card_map, Finset.card_val, card_product]
    _ ≤ σ * σ := Nat.mul_le_mul (hσ _) (hσ _)
    _ = 1 * σ ^ 2 := by ring

theorem lemma_13_9_threeSum : Lemma_13_9_threeSum := by
  intro g A grp U σ P r Pl S ps hU hA hσ1 hσ hSA hP hPl hcard hr hPbound hr1 hlen hgr
  have hU' : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hZ : (2 : ℝ) ≤ 2 * U := by linarith
  -- the values are bounded by `2U`
  have hval : ∀ q ∈ S, ∀ v ∈ val3 A grp q, (|v| : ℝ) ≤ 2 * U := by
    intro q hq v hv
    simp only [val3, Multiset.mem_map, Finset.mem_val, mem_product] at hv
    obtain ⟨⟨b, c⟩, ⟨hb, hc⟩, rfl⟩ := hv
    have ha := hA q.1 (hSA q hq)
    have hb' := hA b (mem_filter.1 hb).1
    have hc' := hA c (mem_filter.1 hc).1
    have : |(q.1 : ℤ) + b - c| ≤ 2 * U := by
      rw [abs_le]; constructor <;> omega
    exact_mod_cast this
  have hg := lemma_13_9_greedy (val3 A grp) S Pl P r (2 * U) ps hP hZ hval hPl hcard hr hlen hgr
  have h1 := Fsum_one_le A grp σ hσ S
  have hσ' : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  have hPr : (1 : ℝ) < P := by exact_mod_cast (by omega : 1 < P)
  have hP0 : (0 : ℝ) < P := by linarith
  have hl : 0 < Real.log (2 * U) := Real.log_pos (by linarith)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr1
  -- `(4 ln(2U)/P)^r ≤ 1/(2σ²)`
  have hκ : (4 * Real.log (2 * U) / P) ^ r ≤ 1 / (2 * (σ : ℝ) ^ 2) := by
    have hB : (0 : ℝ) < (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) := by positivity
    have h4 : 4 * Real.log (2 * U) / P ≤ 1 / (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) := by
      rw [div_le_div_iff₀ hP0 hB]; linarith
    calc (4 * Real.log (2 * U) / P) ^ r ≤ (1 / (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ))) ^ r :=
          pow_le_pow_left₀ (by positivity) h4 r
      _ = 1 / (2 * (σ : ℝ) ^ 2) := by
          rw [div_pow, one_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          rw [show 1 / (r : ℝ) * r = 1 by field_simp, Real.rpow_one]
  calc (Fsum (val3 A grp) S ps.prod : ℝ) ≤ Fsum (val3 A grp) S 1 * (4 * Real.log (2 * U) / P) ^ r := hg
    _ ≤ (S.card * σ ^ 2 : ℕ) * (1 / (2 * (σ : ℝ) ^ 2)) := by
        apply mul_le_mul (by exact_mod_cast h1) hκ (by positivity) (by positivity)
    _ = S.card / 2 := by push_cast; field_simp

/-! ## Lemma 13.7 -/

/-- `∑_λ #{b : f b = λ} #{c : g c = λ} = #{(b, c) : f b = g c}`. -/
lemma sum_card_fibers {β γ : Type} [DecidableEq β] [DecidableEq γ] [Fintype γ]
    (s : Finset β) (t : Finset β) (f g : β → γ) :
    (∑ lam : γ, (s.filter fun b => f b = lam).card * (t.filter fun c => g c = lam).card)
      = ((s ×ˢ t).filter fun bc => f bc.1 = g bc.2).card := by
  rw [card_eq_sum_card_fiberwise (f := fun bc : β × β => f bc.1) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun lam _ => ?_
  rw [← card_product]
  congr 1
  ext ⟨b, c⟩
  simp only [mem_product, mem_filter]
  constructor
  · rintro ⟨⟨hb, h1⟩, hc, h2⟩; exact ⟨⟨⟨hb, hc⟩, by rw [h1, h2]⟩, h1⟩
  · rintro ⟨⟨⟨hb, hc⟩, h⟩, h1⟩; exact ⟨⟨hb, h1⟩, hc, by rw [← h, h1]⟩

lemma ceil_div_facts (ϱ T : ℕ) (hT : 1 ≤ T) :
    ϱ ≤ (ϱ + T - 1) / T * T ∧ (ϱ + T - 1) / T * T < ϱ + T := by
  have h := Nat.div_add_mod (ϱ + T - 1) T
  have hm := Nat.mod_lt (ϱ + T - 1) (by omega : 0 < T)
  rw [Nat.mul_comm] at h
  generalize (ϱ + T - 1) / T * T = P at h ⊢
  omega

theorem lemma_13_7 : Lemma_13_7 := by
  intro m T a _ Aj Ak hT hmT
  intro ϱ x y
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  have hϱ : ϱ < m := Nat.mod_lt a hm
  have hx1 : ϱ ≤ x * T := (ceil_div_facts ϱ T hT).1
  have hx2 : x * T < ϱ + T := (ceil_div_facts ϱ T hT).2
  have hxT : x ≤ T := by
    by_contra h
    push_neg at h
    have : (T + 1) * T ≤ x * T := Nat.mul_le_mul_right T h
    nlinarith
  have hxy : x * T = ϱ + y := by simp only [y]; omega
  refine ⟨hxT, by simp only [y]; omega, ?_, ?_⟩
  · rw [show ((x * T : ℕ) : ℤ) - y = (ϱ : ℤ) by rw [hxy]; push_cast; ring]
    simp only [ϱ]
    rw [Int.natCast_mod]
    exact Int.mod_modEq _ _
  · have key : ∀ b c : ℕ, (((b + x * T : ℕ) : ZMod m) = ((c + y : ℕ) : ZMod m) ↔
        (m : ℤ) ∣ (a : ℤ) + b - c) := by
      intro b c
      have ha : ((ϱ : ℕ) : ZMod m) = (a : ZMod m) := ZMod.natCast_mod a m
      rw [hxy, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ha]
      constructor <;> intro h <;> linear_combination h
    rw [sum_card_fibers]
    congr 1
    exact filter_congr fun bc _ => key bc.1 bc.2

/-! ## Lemma 13.5 -/

theorem lemma_13_5_ab : Lemma_13_5_ab := by
  intro U A B C hU hA hB hC S
  have hA' : ∀ a ∈ A, -U ≤ a ∧ a ≤ U := fun a ha => abs_le.1 (hA a ha)
  have hB' : ∀ b ∈ B, -U ≤ b ∧ b ≤ U := fun b hb => abs_le.1 (hB b hb)
  have hC' : ∀ c ∈ C, -U ≤ c ∧ c ≤ U := fun c hc => abs_le.1 (hC c hc)
  have memS : ∀ s, s ∈ S ↔ (∃ a ∈ A, a + 10 * U = s) ∨ (∃ b ∈ B, b + 30 * U = s) ∨
      (∃ c ∈ C, c + 40 * U = s) := by
    intro s; simp only [S, mem_union, mem_image, or_assoc]
  refine ⟨fun s hs => ?_, ⟨?_, ?_⟩, ?_⟩
  · rcases (memS s).1 hs with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, rfl⟩
    · have := hA' a ha; constructor <;> omega
    · have := hB' b hb; constructor <;> omega
    · have := hC' c hc; constructor <;> omega
  · rintro ⟨a, ha, b, hb, c, hc, h⟩
    exact ⟨a + 10 * U, (memS _).2 (Or.inl ⟨a, ha, rfl⟩), b + 30 * U,
      (memS _).2 (Or.inr (Or.inl ⟨b, hb, rfl⟩)), c + 40 * U,
      (memS _).2 (Or.inr (Or.inr ⟨c, hc, rfl⟩)), by rw [← h]; ring⟩
  · rintro ⟨x, hx, y, hy, z, hz, h⟩
    have rng : ∀ s ∈ S, (9 * U ≤ s ∧ s ≤ 11 * U ∧ s - 10 * U ∈ A) ∨
        (29 * U ≤ s ∧ s ≤ 31 * U ∧ s - 30 * U ∈ B) ∨ (39 * U ≤ s ∧ s ≤ 41 * U ∧ s - 40 * U ∈ C) := by
      intro s hs
      rcases (memS s).1 hs with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩ | ⟨c, hc, rfl⟩
      · have := hA' a ha; left; exact ⟨by omega, by omega, by simpa using ha⟩
      · have := hB' b hb; right; left; exact ⟨by omega, by omega, by simpa using hb⟩
      · have := hC' c hc; right; right; exact ⟨by omega, by omega, by simpa using hc⟩
    rcases rng x hx with ⟨hx1, hx2, hxA⟩ | ⟨hx1, hx2, hxB⟩ | ⟨hx1, hx2, hxC⟩ <;>
    rcases rng y hy with ⟨hy1, hy2, hyA⟩ | ⟨hy1, hy2, hyB⟩ | ⟨hy1, hy2, hyC⟩ <;>
    rcases rng z hz with ⟨hz1, hz2, hzA⟩ | ⟨hz1, hz2, hzB⟩ | ⟨hz1, hz2, hzC⟩
    all_goals first
      | (exfalso; omega)
      | exact ⟨x - 10 * U, hxA, y - 30 * U, hyB, z - 40 * U, hzC, by omega⟩
      | exact ⟨y - 10 * U, hyA, x - 30 * U, hxB, z - 40 * U, hzC, by omega⟩
  · constructor
    · rintro ⟨a, ha, b, hb, c, hc, h⟩
      exact ⟨a, ha, b, hb, -c, mem_image.2 ⟨c, hc, rfl⟩, by linarith⟩
    · rintro ⟨a, ha, b, hb, c', hc', h⟩
      obtain ⟨c, hc, rfl⟩ := mem_image.1 hc'
      exact ⟨a, ha, b, hb, c, hc, by linarith⟩

/-- Two different indices below `2^ℓ` differ at a bit below `ℓ`. -/
lemma exists_bit_ne {ℓ i j : ℕ} (hi : i < 2 ^ ℓ) (hj : j < 2 ^ ℓ) (hij : i ≠ j) :
    ∃ β < ℓ, Nat.testBit i β ≠ Nat.testBit j β := by
  by_contra h
  push_neg at h
  apply hij
  apply Nat.eq_of_testBit_eq
  intro β
  by_cases hβ : β < ℓ
  · exact h β hβ
  · push_neg at hβ
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi (Nat.pow_le_pow_right (by norm_num) hβ)),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hβ))]

theorem lemma_13_5_c : Lemma_13_5_c := by
  intro n ℓ x hn cls
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨i, j, k, hij, hjk, hik, h⟩
    have hi : (i : ℕ) < 2 ^ ℓ := lt_of_lt_of_le i.2 hn
    have hj : (j : ℕ) < 2 ^ ℓ := lt_of_lt_of_le j.2 hn
    have hk : (k : ℕ) < 2 ^ ℓ := lt_of_lt_of_le k.2 hn
    obtain ⟨β₁, hβ₁, h1⟩ := exists_bit_ne hi hj (fun e => hij (Fin.ext e))
    by_cases hki : Nat.testBit k β₁ = Nat.testBit i β₁
    · obtain ⟨β₂, hβ₂, h2⟩ := exists_bit_ne hi hk (fun e => hik (Fin.ext e))
      have hne : β₁ ≠ β₂ := by rintro rfl; exact h2 hki.symm
      refine ⟨β₁, hβ₁, β₂, hβ₂, hne, cls β₁ β₂ i, cls β₁ β₂ j, cls β₁ β₂ k, ?_, ?_, ?_, i, j, k,
        rfl, rfl, rfl, h⟩
      · simp only [cls, ne_eq, Prod.mk.injEq, not_and]; intro e; exact absurd e h1
      · simp only [cls, ne_eq, Prod.mk.injEq, not_and]; intro e; exact absurd (e.trans hki) h1.symm
      · simp only [cls, ne_eq, Prod.mk.injEq, not_and]; intro _; exact h2
    · have hkj : Nat.testBit k β₁ = Nat.testBit j β₁ := by
        cases h3 : Nat.testBit i β₁ <;> cases h4 : Nat.testBit j β₁ <;>
          cases h5 : Nat.testBit k β₁ <;> simp_all
      obtain ⟨β₂, hβ₂, h2⟩ := exists_bit_ne hj hk (fun e => hjk (Fin.ext e))
      have hne : β₁ ≠ β₂ := by rintro rfl; exact h2 hkj.symm
      refine ⟨β₁, hβ₁, β₂, hβ₂, hne, cls β₁ β₂ i, cls β₁ β₂ j, cls β₁ β₂ k, ?_, ?_, ?_, i, j, k,
        rfl, rfl, rfl, h⟩
      · simp only [cls, ne_eq, Prod.mk.injEq, not_and]; intro e; exact absurd e h1
      · simp only [cls, ne_eq, Prod.mk.injEq, not_and]; intro _; exact h2
      · simp only [cls, ne_eq, Prod.mk.injEq, not_and]; intro e; exact absurd (e.trans hkj) h1
  · rintro ⟨β₁, -, β₂, -, -, c₁, c₂, c₃, h12, h23, h13, i, j, k, hi, hj, hk, h⟩
    refine ⟨i, j, k, ?_, ?_, ?_, h⟩
    · rintro rfl; exact h12 (hi.symm.trans hj)
    · rintro rfl; exact h23 (hj.symm.trans hk)
    · rintro rfl; exact h13 (hi.symm.trans hk)
  · rw [card_product]
    have h1 : ((Finset.range ℓ ×ˢ Finset.range ℓ).filter fun p => p.1 ≠ p.2).card ≤ ℓ ^ 2 := by
      calc _ ≤ (Finset.range ℓ ×ˢ Finset.range ℓ).card := card_filter_le _ _
        _ = ℓ ^ 2 := by rw [card_product, card_range, sq]
    have h2 : ((univ : Finset ((Bool × Bool) × (Bool × Bool) × (Bool × Bool))).filter
        fun c => c.1 ≠ c.2.1 ∧ c.2.1 ≠ c.2.2 ∧ c.1 ≠ c.2.2).card = 24 := by decide
    rw [h2]
    nlinarith

/-! ## Lemma 13.6 -/

lemma bits_sum (B v : ℕ) (hv : v < 2 ^ B) :
    v = ∑ i ∈ range B, 2 ^ i * (if Nat.testBit v i then 1 else 0) := by
  induction B generalizing v with
  | zero => simp at hv; simp [hv]
  | succ B ih =>
    rw [Finset.sum_range_succ', pow_zero, one_mul]
    have h2 : v / 2 < 2 ^ B := by rw [pow_succ] at hv; omega
    have e : ∀ i ∈ range B, 2 ^ (i + 1) * (if Nat.testBit v (i + 1) then 1 else 0)
        = 2 * (2 ^ i * (if Nat.testBit (v / 2) i then 1 else 0)) := by
      intro i _
      rw [Nat.testBit_succ, pow_succ]; ring
    rw [sum_congr rfl e, ← mul_sum, ← ih (v / 2) h2, Nat.testBit_zero]
    by_cases h : v % 2 = 1 <;> simp [h] <;> omega

theorem lemma_13_6 : Lemma_13_6 := by
  intro n d B X Y hX hY bits
  have hb : ∀ v, v < 2 ^ B → v = ∑ i ∈ range B, 2 ^ i * bits i v := fun v hv => bits_sum B v hv
  refine ⟨fun I t => hb _ (hX I t), fun I J => ?_⟩
  rw [Matrix.mul_apply]
  calc ∑ t, X I t * Y t J
      = ∑ t, (∑ i ∈ range B, 2 ^ i * bits i (X I t)) * (∑ j ∈ range B, 2 ^ j * bits j (Y t J)) :=
        sum_congr rfl fun t _ => by rw [← hb _ (hX I t), ← hb _ (hY t J)]
    _ = ∑ t, ∑ i ∈ range B, ∑ j ∈ range B,
          2 ^ (i + j) * (bits i (X I t) * bits j (Y t J)) := by
        refine sum_congr rfl fun t _ => ?_
        rw [sum_mul_sum]
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [pow_add]; ring
    _ = ∑ i ∈ range B, ∑ j ∈ range B, ∑ t, 2 ^ (i + j) * (bits i (X I t) * bits j (Y t J)) := by
        rw [sum_comm]; refine sum_congr rfl fun i _ => ?_; rw [sum_comm]
    _ = _ := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
        rw [← mul_sum, Matrix.mul_apply]
        rfl

end ThinMatrixProducts

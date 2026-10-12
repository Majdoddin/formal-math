import XorLean.Reduction
import XorLean.ImprovedStages

/-!
# Improved 3XOR, §4.3–4.4 and Theorem II's correctness

the improved write-up §4.3 (the grouping hash `π`, the count `Z(π)` and its Walsh–Hadamard form,
blocks, probes, Lemma II.1), §4.4 (the instance `I(H, 𝒫)`, Lemma II.2, the binary splitting of
Lemma II.3), and the correctness of Theorem II (Lemma II.5 for the probes, the search version).
The lists are sets `S₁ S₂ S₃ : Finset (Vec d)` (step 0 / §4.2 removes repeated vectors).
-/

set_option linter.unusedSectionVars false

namespace Xor

/-- The counting version `#Lop`: the number of common neighbours of `a` and `b` in the middle
part (Definition 14 of arXiv:2610.06783). -/
noncomputable def LopInst.count {A B V : Type*} (I : LopInst A B V) (a : A) (b : B) : ℕ :=
  open Classical in (I.mid.filter fun m => I.adjA a m ∧ I.adjB m b).card

end Xor

namespace Xor.Improved
open Xor Finset

variable {d : ℕ}

/-! ### Helpers on `F₂^n` -/

theorem vadd_self {n : ℕ} (x : Vec n) : x + x = 0 :=
  funext fun i => by
    have : ∀ a : ZMod 2, a + a = 0 := by decide
    exact this (x i)

/-- `a ⊕ b ⊕ c = 0 ↔ c = a ⊕ b`. -/
theorem vsum_zero_iff {n : ℕ} (a b c : Vec n) : a + b + c = 0 ↔ c = a + b := by
  constructor
  · intro h
    calc c = (a + b + c) + (a + b) := by
          rw [add_comm (a + b) c, add_assoc, vadd_self, add_zero]
      _ = a + b := by rw [h, zero_add]
  · rintro rfl; exact vadd_self _

/-- `x = y ↔ x ⊕ y = 0`. -/
theorem veq_iff {n : ℕ} (x y : Vec n) : x = y ↔ x + y = 0 := by
  constructor
  · rintro rfl; exact vadd_self _
  · intro h
    have := (vsum_zero_iff 0 x y).1 (by rw [zero_add]; exact h)
    rw [zero_add] at this; exact this.symm

/-! ### `Z(π)` and the Walsh–Hadamard transform (§4.3) -/

/-- `Z(π)`: the triples of `S₁ × S₂ × S₃` that the linear map `π` sends to `0`. -/
def Zc (S₁ S₂ S₃ : Finset (Vec d)) {l : ℕ} (π : Vec d →ₗ[ZMod 2] Vec l) : ℕ :=
  ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => π (t.1 + t.2.1 + t.2.2) = 0).card

/-- `Z₀`: the solutions, `x₁ ⊕ x₂ ⊕ x₃ = 0`. -/
def Zsol (S₁ S₂ S₃ : Finset (Vec d)) : ℕ :=
  ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => t.1 + t.2.1 + t.2.2 = 0).card

/-- `Z₀ ≤ |S₁| |S₂|` (`x₁, x₂` determine `x₃`), so `Z₀ ≤ n²`. -/
theorem Zsol_le (S₁ S₂ S₃ : Finset (Vec d)) : Zsol S₁ S₂ S₃ ≤ S₁.card * S₂.card := by
  unfold Zsol
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1)) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at ht
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    exact ⟨ht.1.1, ht.1.2.1⟩
  · intro t ht t' ht' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht ht'
    simp only [Prod.mk.injEq] at h
    have h3 := (vsum_zero_iff _ _ _).1 ht.2
    have h3' := (vsum_zero_iff _ _ _).1 ht'.2
    exact Prod.ext h.1 (Prod.ext h.2 (by rw [h3, h3', h.1, h.2]))

/-- `c_i(β) = #{x ∈ S_i : π'(x) = β}`. -/
def cls (S : Finset (Vec d)) {l : ℕ} (π : Vec d →ₗ[ZMod 2] Vec l) (β : Vec l) : ℕ :=
  (S.filter fun x => π x = β).card

/-- The Walsh–Hadamard transform `ĉ(y) = Σ_β c(β) (-1)^{⟨y,β⟩}`. -/
def wht {l : ℕ} (c : Vec l → ℕ) (y : Vec l) : ℤ := ∑ β, (c β : ℤ) * chi y β

/-- `Z(π') = Σ_{β₁ ⊕ β₂ ⊕ β₃ = 0} c₁(β₁) c₂(β₂) c₃(β₃)` (§4.3, "Computing `Z`"). -/
theorem Zc_eq_sum_cls (S₁ S₂ S₃ : Finset (Vec d)) {l : ℕ} (π : Vec d →ₗ[ZMod 2] Vec l) :
    Zc S₁ S₂ S₃ π = ∑ β ∈ (univ : Finset (Vec l × Vec l × Vec l)).filter
      (fun β => β.1 + β.2.1 + β.2.2 = 0), cls S₁ π β.1 * cls S₂ π β.2.1 * cls S₃ π β.2.2 := by
  unfold Zc cls
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t => (π t.1, π t.2.1, π t.2.2))
    (t := (univ : Finset (Vec l × Vec l × Vec l)).filter (fun β => β.1 + β.2.1 + β.2.2 = 0))]
  · refine Finset.sum_congr rfl fun β hβ => ?_
    obtain ⟨β₁, β₂, β₃⟩ := β
    rw [mul_assoc, ← Finset.card_product, ← Finset.card_product]
    congr 1
    ext ⟨x₁, x₂, x₃⟩
    simp only [Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨h1, h2, h3⟩, -⟩, e1, e2, e3⟩
      exact ⟨⟨h1, e1⟩, ⟨h2, e2⟩, h3, e3⟩
    · rintro ⟨⟨h1, e1⟩, ⟨h2, e2⟩, h3, e3⟩
      refine ⟨⟨⟨h1, h2, h3⟩, ?_⟩, e1, e2, e3⟩
      rw [map_add, map_add, e1, e2, e3]
      exact (Finset.mem_filter.1 hβ).2
  · intro t ht
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    simp only [Finset.mem_coe, Finset.mem_filter] at ht
    rw [← map_add, ← map_add]
    exact ht.2

/-- `Z(π') = 2^{-l} Σ_y ĉ₁(y) ĉ₂(y) ĉ₃(y)`, multiplied out (§4.3, "Computing `Z`"). -/
theorem two_pow_mul_Zc (S₁ S₂ S₃ : Finset (Vec d)) {l : ℕ} (π : Vec d →ₗ[ZMod 2] Vec l) :
    (2 : ℤ) ^ l * Zc S₁ S₂ S₃ π =
      ∑ y, wht (cls S₁ π) y * wht (cls S₂ π) y * wht (cls S₃ π) y := by
  have hw : ∀ (S : Finset (Vec d)) y, wht (cls S π) y = ∑ x ∈ S, chi y (π x) := by
    intro S y
    rw [← Finset.sum_fiberwise S (fun x => π x) (fun x => chi y (π x))]
    unfold wht cls
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => chi y β)
      (fun x hx => by rw [(Finset.mem_filter.1 hx).2]), Finset.sum_const, nsmul_eq_mul]
  simp only [hw]
  have h1 : (2 : ℤ) ^ l * Zc S₁ S₂ S₃ π =
      ∑ t ∈ S₁ ×ˢ S₂ ×ˢ S₃, ∑ y, chi y (π (t.1 + t.2.1 + t.2.2)) := by
    unfold Zc
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [sum_chi_eq]
    split_ifs <;> simp
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_product, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  rw [Finset.sum_product, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x₂ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x₃ _ => ?_
  simp only [map_add, chi_add]

/-! ### The choice of `π` (§4.3) -/

/-- The family of Lemma 5 for `Z`: the triples with `x₁ ⊕ x₂ ⊕ x₃ ≠ 0`, weight `1`. -/
def tripFam (S₁ S₂ S₃ : Finset (Vec d)) : Finset (Vec d × Vec d × Vec d) :=
  (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => t.1 + t.2.1 + t.2.2 ≠ 0

/-- `Φ = Z − Z₀` (§4.3, "Choice of `π`"). -/
theorem surv_tripFam (S₁ S₂ S₃ : Finset (Vec d)) (rows : List (Vec d)) :
    surv (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1) rows =
      (Zc S₁ S₂ S₃ (rowsMap rows) : ℝ) - Zsol S₁ S₂ S₃ := by
  have hsplit : Zc S₁ S₂ S₃ (rowsMap rows) = ((tripFam S₁ S₂ S₃).filter fun t =>
      ∀ u ∈ rows, u ⬝ᵥ (t.1 + t.2.1 + t.2.2) = 0).card + Zsol S₁ S₂ S₃ := by
    unfold Zc Zsol tripFam
    rw [Finset.filter_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : t.1 + t.2.1 + t.2.2 = 0
    · simp [h]
    · rw [if_neg h, add_zero]
      exact if_congr (by rw [rowsMap_eq_zero_iff]; exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩)
        rfl rfl
  unfold surv
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hsplit]
  push_cast; ring

/-- Minimizing `Z` minimizes `Φ`. -/
theorem isGreedy_Zc_iff (S₁ S₂ S₃ : Finset (Vec d)) (E : Multiset (Vec d))
    (rows : List (Vec d)) :
    IsGreedy E (fun l => (Zc S₁ S₂ S₃ (rowsMap l) : ℝ)) rows ↔
      IsGreedy E (surv (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1)) rows := by
  have : (fun l => (Zc S₁ S₂ S₃ (rowsMap l) : ℝ)) = fun l =>
      surv (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1) l +
        (Zsol S₁ S₂ S₃ : ℝ) := by
    funext l
    rw [surv_tripFam]; ring
  rw [this, isGreedy_add_const]

/-- Lemma 5 for the greedy rows on `Z`: `Z(π) − Z₀ ≤ e 2^{-r} |S₁||S₂||S₃|` for `r` rows from
an `ε`-biased `E` with `0 ≤ ε ≤ 1/r`. -/
theorem Zc_greedy_le (S₁ S₂ S₃ : Finset (Vec d)) {ε : ℝ} {E : Multiset (Vec d)}
    (hE : IsBiased ε E) (hε0 : 0 ≤ ε) (rows : List (Vec d))
    (hg : IsGreedy E (fun l => (Zc S₁ S₂ S₃ (rowsMap l) : ℝ)) rows)
    (hr : 0 < rows.length) (hε : ε ≤ 1 / rows.length) :
    (Zc S₁ S₂ S₃ (rowsMap rows) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * (S₁.card * S₂.card * S₃.card) := by
  have hg' := (isGreedy_Zc_iff S₁ S₂ S₃ E rows).1 hg
  have hb := greedy_bound_exp hE hε0 (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2)
    (fun _ => 1) (fun j hj => (Finset.mem_filter.1 hj).2) (fun _ _ => zero_le_one) rows hg' hr hε
  rw [surv_tripFam, Finset.sum_const, nsmul_eq_mul, mul_one] at hb
  have hcard : ((tripFam S₁ S₂ S₃).card : ℝ) ≤ S₁.card * S₂.card * S₃.card := by
    have : (tripFam S₁ S₂ S₃).card ≤ S₁.card * S₂.card * S₃.card := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, Finset.card_product, mul_assoc]
    exact_mod_cast this
  exact hb.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

/-- §4.3, display after "Choice of `π`": with `k` greedy rows from the `(1/k)`-biased `E_k`,
lists of at most `n` elements and `n/σ ≤ 2^k`: `Z(π) − Z₀ ≤ eσn²` and `Z(π) ≤ (eσ+1)n²`. -/
theorem Zc_pi_le (S₁ S₂ S₃ : Finset (Vec d)) (n σ : ℕ) (hσ : 0 < σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (E : Multiset (Vec d)) (rows : List (Vec d)) (hk : 0 < rows.length)
    (hE : IsBiased (1 / (rows.length : ℝ)) E)
    (hg : IsGreedy E (fun l => (Zc S₁ S₂ S₃ (rowsMap l) : ℝ)) rows)
    (h2k : (n : ℝ) / σ ≤ 2 ^ rows.length) :
    (Zc S₁ S₂ S₃ (rowsMap rows) : ℝ) - Zsol S₁ S₂ S₃ ≤ Real.exp 1 * σ * n ^ 2 ∧
    (Zc S₁ S₂ S₃ (rowsMap rows) : ℝ) ≤ (Real.exp 1 * σ + 1) * n ^ 2 := by
  have hb := Zc_greedy_le S₁ S₂ S₃ hE (by positivity) rows hg hk le_rfl
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have c1 : (S₁.card : ℝ) ≤ n := by exact_mod_cast h₁
  have c2 : (S₂.card : ℝ) ≤ n := by exact_mod_cast h₂
  have c3 : (S₃.card : ℝ) ≤ n := by exact_mod_cast h₃
  have hprod : (S₁.card * S₂.card * S₃.card : ℝ) ≤ n * n * n := by
    apply mul_le_mul (mul_le_mul c1 c2 (Nat.cast_nonneg _) hn0) c3 (Nat.cast_nonneg _)
      (by positivity)
  have hpow : (2 : ℝ)⁻¹ ^ rows.length * n ≤ σ := by
    rw [div_le_iff₀ hσR] at h2k
    rw [inv_pow]
    rw [inv_mul_le_iff₀ (by positivity)]
    linarith
  have h1 : (Zc S₁ S₂ S₃ (rowsMap rows) : ℝ) - Zsol S₁ S₂ S₃ ≤ Real.exp 1 * σ * n ^ 2 := by
    calc _ ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * (S₁.card * S₂.card * S₃.card) := hb
      _ ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * (n * n * n) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = Real.exp 1 * ((2 : ℝ)⁻¹ ^ rows.length * n) * n ^ 2 := by ring
      _ ≤ Real.exp 1 * σ * n ^ 2 := by gcongr
  have hZ0 : (Zsol S₁ S₂ S₃ : ℝ) ≤ n ^ 2 := by
    have := Zsol_le S₁ S₂ S₃
    have : (Zsol S₁ S₂ S₃ : ℝ) ≤ S₁.card * S₂.card := by exact_mod_cast this
    nlinarith [Nat.cast_nonneg (α := ℝ) S₁.card, Nat.cast_nonneg (α := ℝ) S₂.card]
  refine ⟨h1, ?_⟩
  linarith

/-! ### Blocks and probes (§4.3) -/

/-- The blocks of one list: every class `G(β) = {x ∈ S : π x = β}` cut into at most
`⌈|G(β)|/σ⌉` blocks of at most `σ` elements, each element in exactly one block of its class. -/
structure Blocking (S : Finset (Vec d)) {k : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k) (σ : ℕ) where
  blocks : Vec k → Finset (Finset (Vec d))
  sub : ∀ β, ∀ b ∈ blocks β, b ⊆ S.filter fun x => π x = β
  card_le : ∀ β, ∀ b ∈ blocks β, b.card ≤ σ
  cover : ∀ β, ∀ x ∈ S.filter (fun x => π x = β), ∃! b, b ∈ blocks β ∧ x ∈ b
  count : ∀ β, (blocks β).card ≤ ((S.filter fun x => π x = β).card + σ - 1) / σ

/-- Blocks exist for every `σ ≥ 1`. -/
theorem Blocking.nonempty (S : Finset (Vec d)) {k : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k) (σ : ℕ)
    (hσ : 0 < σ) : Nonempty (Blocking S π σ) := by
  choose parts h1 h2 h3 using fun β => exists_cutting (S.filter fun x => π x = β) σ hσ
  exact ⟨⟨parts, fun β b hb => (h1 β b hb).1, fun β b hb => (h1 β b hb).2,
    fun β x hx => h2 β x hx, h3⟩⟩

/-- The labelled blocks `𝔅_i`: pairs `(label, block)`. -/
def Blocking.set {S : Finset (Vec d)} {k : ℕ} {π : Vec d →ₗ[ZMod 2] Vec k} {σ : ℕ}
    (B : Blocking S π σ) : Finset (Vec k × Finset (Vec d)) :=
  univ.filter fun p => p.2 ∈ B.blocks p.1

/-- Sums over the labelled blocks. -/
theorem Blocking.sum_set {S : Finset (Vec d)} {k : ℕ} {π : Vec d →ₗ[ZMod 2] Vec k} {σ : ℕ}
    (B : Blocking S π σ) {M : Type*} [AddCommMonoid M] (f : Vec k × Finset (Vec d) → M) :
    ∑ p ∈ B.set, f p = ∑ β, ∑ b ∈ B.blocks β, f (β, b) :=
  Finset.sum_finset_product _ _ _ fun p => by simp [Blocking.set]

/-- `Σ_β c(β) = |S|`. -/
theorem sum_cls (S : Finset (Vec d)) {l : ℕ} (π : Vec d →ₗ[ZMod 2] Vec l) :
    ∑ β, cls S π β = S.card :=
  (Finset.card_eq_sum_card_fiberwise (f := fun x => π x) (t := univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))).symm

/-- `s(β) ≤ 1 + c(β)/σ`. -/
theorem Blocking.card_blocks_le {S : Finset (Vec d)} {k : ℕ} {π : Vec d →ₗ[ZMod 2] Vec k}
    {σ : ℕ} (hσ : 0 < σ) (B : Blocking S π σ) (β : Vec k) :
    ((B.blocks β).card : ℝ) ≤ 1 + cls S π β / σ := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  refine (Nat.cast_le.2 (B.count β)).trans (Nat.cast_div_le.trans ?_)
  have : ((cls S π β + σ - 1 : ℕ) : ℝ) ≤ cls S π β + σ := by
    have : cls S π β + σ - 1 ≤ cls S π β + σ := by omega
    exact_mod_cast this
  unfold cls at this ⊢
  calc (((S.filter fun x => π x = β).card + σ - 1 : ℕ) : ℝ) / σ
      ≤ ((S.filter fun x => π x = β).card + σ) / σ := div_le_div_of_nonneg_right this hσR.le
    _ = 1 + (S.filter fun x => π x = β).card / σ := by field_simp; ring

/-- `|𝔅_i| ≤ 2^k + |S_i|/σ` (§4.3, "Blocks"). -/
theorem Blocking.card_set_le {S : Finset (Vec d)} {k : ℕ} {π : Vec d →ₗ[ZMod 2] Vec k} {σ : ℕ}
    (hσ : 0 < σ) (B : Blocking S π σ) : (B.set.card : ℝ) ≤ 2 ^ k + S.card / σ := by
  have hc : B.set.card = ∑ β, (B.blocks β).card := by
    rw [Finset.card_eq_sum_ones, B.sum_set]; simp
  rw [hc, Nat.cast_sum]
  calc ∑ β, ((B.blocks β).card : ℝ) ≤ ∑ β, (1 + cls S π β / σ : ℝ) :=
        Finset.sum_le_sum fun β _ => B.card_blocks_le hσ β
    _ = 2 ^ k + S.card / σ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Nat.cast_sum, sum_cls]
        simp [Finset.card_univ, ZMod.card]

/-- A probe `Q = (x₁; b₂, b₃)` with labelled blocks. -/
abbrev Probe (d k : ℕ) := Vec d × (Vec k × Finset (Vec d)) × (Vec k × Finset (Vec d))

/-- `𝒫₀`: the probes `(x₁; b₂, b₃)` with `label(b₃) = π(x₁) ⊕ label(b₂)`. -/
def probes (S₁ : Finset (Vec d)) {S₂ S₃ : Finset (Vec d)} {k : ℕ}
    (π : Vec d →ₗ[ZMod 2] Vec k) {σ : ℕ} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) :
    Finset (Probe d k) :=
  (S₁ ×ˢ B₂.set ×ˢ B₃.set).filter fun Q => Q.2.2.1 = π Q.1 + Q.2.1.1

/-- The probes as candidates: `Q = (x₁; b₂, b₃)` carries `x₁ ⊕ x₂ ⊕ x₃`, `(x₂,x₃) ∈ b₂ × b₃`.
So `cnt_H(Q)` and `z(Q)` are the text's. -/
def probeCands (d k : ℕ) : Cands (Probe d k) (Vec d × Vec d) d where
  fam Q := Q.2.1.2 ×ˢ Q.2.2.2
  vec Q p := Q.1 + p.1 + p.2

/-- `cnt_∅(Q) = |b₂||b₃| ≤ σ²` (§4.3). -/
theorem probe_card_fam_le (S₁ S₂ S₃ : Finset (Vec d)) {k : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k)
    {σ : ℕ} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) :
    ∀ Q ∈ probes S₁ π B₂ B₃, ((probeCands d k).fam Q).card ≤ σ ^ 2 := by
  intro Q hQ
  simp only [probes, Finset.mem_filter, Finset.mem_product] at hQ
  have h2 : Q.2.1.2 ∈ B₂.blocks Q.2.1.1 := (Finset.mem_filter.1 hQ.1.2.1).2
  have h3 : Q.2.2.2 ∈ B₃.blocks Q.2.2.1 := (Finset.mem_filter.1 hQ.1.2.2).2
  simp only [probeCands, Finset.card_product, sq]
  exact Nat.mul_le_mul (B₂.card_le _ _ h2) (B₃.card_le _ _ h3)

/-- Step 3's scan of a probe ("for every `x₂ ∈ b₂` test whether `x₁ ⊕ x₂ ∈ b₃`") succeeds iff
`z(Q) > 0`. -/
theorem probe_z_pos_iff {k : ℕ} (Q : Probe d k) :
    0 < (probeCands d k).z Q ↔ ∃ x₂ ∈ Q.2.1.2, Q.1 + x₂ ∈ Q.2.2.2 := by
  unfold Cands.z probeCands
  rw [Finset.card_pos]
  constructor
  · rintro ⟨⟨x₂, x₃⟩, hp⟩
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨x₂, hp.1.1, (vsum_zero_iff _ _ _).1 hp.2 ▸ hp.1.2⟩
  · rintro ⟨x₂, h2, h3⟩
    exact ⟨(x₂, Q.1 + x₂), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h2, h3⟩,
      (vsum_zero_iff _ _ _).2 rfl⟩⟩

/-- **Lemma II.1 (i)**: every solution lies in some probe. -/
theorem solution_in_probe (S₁ S₂ S₃ : Finset (Vec d)) {k : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k)
    {σ : ℕ} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    (x₁ x₂ x₃ : Vec d) (h₁ : x₁ ∈ S₁) (h₂ : x₂ ∈ S₂) (h₃ : x₃ ∈ S₃) (h0 : x₁ + x₂ + x₃ = 0) :
    ∃ Q ∈ probes S₁ π B₂ B₃, Q.1 = x₁ ∧ x₂ ∈ Q.2.1.2 ∧ x₃ ∈ Q.2.2.2 := by
  obtain ⟨b₂, ⟨hb₂, hx₂⟩, -⟩ := B₂.cover (π x₂) x₂ (Finset.mem_filter.2 ⟨h₂, rfl⟩)
  obtain ⟨b₃, ⟨hb₃, hx₃⟩, -⟩ := B₃.cover (π x₃) x₃ (Finset.mem_filter.2 ⟨h₃, rfl⟩)
  refine ⟨(x₁, (π x₂, b₂), (π x₃, b₃)), ?_, rfl, hx₂, hx₃⟩
  simp only [probes, Blocking.set, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
    true_and]
  refine ⟨⟨h₁, hb₂, hb₃⟩, ?_⟩
  rw [(vsum_zero_iff _ _ _).1 h0, map_add]

/-- **Lemma II.1 (i)**, second sentence: yes-instance iff `z(Q) > 0` for some `Q ∈ 𝒫₀`. -/
theorem exists_sol_iff_probe (S₁ S₂ S₃ : Finset (Vec d)) {k : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k)
    {σ : ℕ} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) :
    (∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) ↔
      ∃ Q ∈ probes S₁ π B₂ B₃, 0 < (probeCands d k).z Q := by
  constructor
  · rintro ⟨x₁, h₁, x₂, h₂, x₃, h₃, h0⟩
    obtain ⟨Q, hQ, e1, e2, e3⟩ := solution_in_probe S₁ S₂ S₃ π B₂ B₃ x₁ x₂ x₃ h₁ h₂ h₃ h0
    refine ⟨Q, hQ, (probe_z_pos_iff Q).2 ⟨x₂, e2, ?_⟩⟩
    rw [e1, ← (vsum_zero_iff _ _ _).1 h0]; exact e3
  · rintro ⟨Q, hQ, hz⟩
    obtain ⟨x₂, h2, h3⟩ := (probe_z_pos_iff Q).1 hz
    simp only [probes, Blocking.set, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at hQ
    have s2 := Finset.mem_filter.1 (B₂.sub _ _ hQ.1.2.1 h2)
    have s3 := Finset.mem_filter.1 (B₃.sub _ _ hQ.1.2.2 h3)
    exact ⟨Q.1, hQ.1.1, x₂, s2.1, Q.1 + x₂, s3.1, (vsum_zero_iff _ _ _).2 rfl⟩

/-- **Lemma II.1 (ii)**, the count: `|𝒫₀| = Σ_{x₁} Σ_β s₂(β) s₃(π(x₁) ⊕ β)`. -/
theorem probes_card_eq (S₁ S₂ S₃ : Finset (Vec d)) {k : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k)
    {σ : ℕ} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) :
    (probes S₁ π B₂ B₃).card =
      ∑ x₁ ∈ S₁, ∑ β, (B₂.blocks β).card * (B₃.blocks (π x₁ + β)).card := by
  unfold probes
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  rw [Finset.sum_product, B₂.sum_set]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hin : ∀ c : Vec k, ∑ p ∈ B₃.set, (if p.1 = c then 1 else 0) = (B₃.blocks c).card := by
    intro c
    rw [B₃.sum_set, Finset.sum_eq_single c]
    · simp
    · intro β' _ hβ'; simp [hβ']
    · simp
  simp only
  rw [Finset.sum_congr rfl (fun b _ => hin (π x₁ + β)), Finset.sum_const, smul_eq_mul]

/-- **Lemma II.1 (ii)**: `|𝒫₀| ≤ (4 + e + 1/σ) n²/σ ≤ 8n²/σ`, from the four facts named in
§3.2: the lists are sets of at most `n` elements, `σ ≥ 1`, `2^k < 2n/σ`, `Z(π) ≤ (eσ+1)n²`. -/
theorem probes_card_le (S₁ S₂ S₃ : Finset (Vec d)) {k : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k)
    (n σ : ℕ) (hσ : 0 < σ) (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (hk : (2 : ℝ) ^ k < 2 * n / σ) (hZ : (Zc S₁ S₂ S₃ π : ℝ) ≤ (Real.exp 1 * σ + 1) * n ^ 2) :
    ((probes S₁ π B₂ B₃).card : ℝ) ≤ (4 + Real.exp 1 + 1 / σ) * n ^ 2 / σ ∧
    ((probes S₁ π B₂ B₃).card : ℝ) ≤ 8 * n ^ 2 / σ := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hσ1 : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  -- the fibre of `x₁`
  have hfib : ∀ x₁, ∑ β, cls S₂ π β * cls S₃ π (π x₁ + β) =
      ((S₂ ×ˢ S₃).filter fun p => π (x₁ + p.1 + p.2) = 0).card := by
    intro x₁
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p => π p.1) (t := univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
    refine Finset.sum_congr rfl fun β _ => ?_
    unfold cls
    rw [← Finset.card_product]
    congr 1
    ext ⟨x₂, x₃⟩
    simp only [Finset.mem_filter, Finset.mem_product, map_add]
    constructor
    · rintro ⟨⟨h2, e⟩, h3, e3⟩
      refine ⟨⟨⟨h2, h3⟩, ?_⟩, e⟩
      rw [(vsum_zero_iff _ _ _).2]; rw [e3, e]
    · rintro ⟨⟨⟨h2, h3⟩, h0⟩, e⟩
      refine ⟨⟨h2, e⟩, h3, ?_⟩
      rw [(vsum_zero_iff _ _ _).1 h0, e]
  have hZsum : ∑ x₁ ∈ S₁, ∑ β, (cls S₂ π β * cls S₃ π (π x₁ + β) : ℝ) = Zc S₁ S₂ S₃ π := by
    have : Zc S₁ S₂ S₃ π = ∑ x₁ ∈ S₁, ((S₂ ×ˢ S₃).filter fun p => π (x₁ + p.1 + p.2) = 0).card := by
      unfold Zc
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun x₁ _ => ?_
      rw [Finset.card_filter]
    rw [this, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [← hfib]; push_cast; rfl
  have hS3 : ∀ x₁, ∑ β, (cls S₃ π (π x₁ + β) : ℝ) = S₃.card := by
    intro x₁
    rw [← sum_cls S₃ π, Nat.cast_sum]
    exact Equiv.sum_comp (Equiv.addLeft (π x₁)) (fun β => (cls S₃ π β : ℝ))
  have hS2 : ∑ β, (cls S₂ π β : ℝ) = S₂.card := by rw [← sum_cls S₂ π, Nat.cast_sum]
  have hcardK : ∑ _β : Vec k, (1 : ℝ) = 2 ^ k := by simp [Finset.card_univ, ZMod.card]
  have hmain : ((probes S₁ π B₂ B₃).card : ℝ) ≤
      S₁.card * 2 ^ k + S₁.card * ((S₂.card + S₃.card) / σ) + Zc S₁ S₂ S₃ π / σ ^ 2 := by
    rw [probes_card_eq, Nat.cast_sum]
    calc ∑ x₁ ∈ S₁, ((∑ β, (B₂.blocks β).card * (B₃.blocks (π x₁ + β)).card : ℕ) : ℝ)
        ≤ ∑ x₁ ∈ S₁, ∑ β, (1 + cls S₂ π β / σ) * (1 + cls S₃ π (π x₁ + β) / σ : ℝ) := by
          refine Finset.sum_le_sum fun x₁ _ => ?_
          push_cast
          refine Finset.sum_le_sum fun β _ => ?_
          exact mul_le_mul (B₂.card_blocks_le hσ β) (B₃.card_blocks_le hσ _)
            (Nat.cast_nonneg _) (by positivity)
      _ = ∑ x₁ ∈ S₁, (∑ _β : Vec k, (1 : ℝ) + (∑ β, (cls S₂ π β : ℝ)) / σ +
            (∑ β, (cls S₃ π (π x₁ + β) : ℝ)) / σ +
            (∑ β, (cls S₂ π β * cls S₃ π (π x₁ + β) : ℝ)) / σ ^ 2) := by
          refine Finset.sum_congr rfl fun x₁ _ => ?_
          rw [Finset.sum_div, Finset.sum_div, Finset.sum_div,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun β _ => ?_
          field_simp
          ring
      _ = ∑ x₁ ∈ S₁, (2 ^ k + (S₂.card : ℝ) / σ + (S₃.card : ℝ) / σ +
            (∑ β, (cls S₂ π β * cls S₃ π (π x₁ + β) : ℝ)) / σ ^ 2) := by
          refine Finset.sum_congr rfl fun x₁ _ => ?_
          rw [hcardK, hS2, hS3 x₁]
      _ = S₁.card * 2 ^ k + S₁.card * ((S₂.card + S₃.card) / σ) + Zc S₁ S₂ S₃ π / σ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
            ← Finset.sum_div S₁ _ ((σ : ℝ) ^ 2), hZsum]
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
  have c1 : (S₁.card : ℝ) ≤ n := by exact_mod_cast h₁
  have c2 : (S₂.card : ℝ) ≤ n := by exact_mod_cast h₂
  have c3 : (S₃.card : ℝ) ≤ n := by exact_mod_cast h₃
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have t1 : (S₁.card : ℝ) * 2 ^ k ≤ n * (2 * n / σ) :=
    mul_le_mul c1 hk.le (by positivity) hn0
  have t2 : (S₁.card : ℝ) * ((S₂.card + S₃.card) / σ) ≤ n * ((n + n) / σ) := by
    apply mul_le_mul c1 _ (by positivity) hn0
    exact div_le_div_of_nonneg_right (by linarith) hσR.le
  have t3 : (Zc S₁ S₂ S₃ π : ℝ) / σ ^ 2 ≤ (Real.exp 1 * σ + 1) * n ^ 2 / σ ^ 2 :=
    div_le_div_of_nonneg_right hZ (by positivity)
  have hfirst : ((probes S₁ π B₂ B₃).card : ℝ) ≤ (4 + Real.exp 1 + 1 / σ) * n ^ 2 / σ := by
    have : n * (2 * n / σ) + n * ((n + n) / σ) + (Real.exp 1 * σ + 1) * n ^ 2 / σ ^ 2 =
        (4 + Real.exp 1 + 1 / σ) * n ^ 2 / σ := by
      field_simp; ring
    linarith
  refine ⟨hfirst, hfirst.trans ?_⟩
  have he := Real.exp_one_lt_d9
  have hinv : 1 / (σ : ℝ) ≤ 1 := by rw [div_le_one hσR]; exact hσ1
  apply div_le_div_of_nonneg_right _ hσR.le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

/-! ### The instance `I(H, 𝒫)` (§4.4) -/

variable {l₁ l₂ : ℕ}

/-- `X[(b₂,u), w] = #{x₂ ∈ b₂ : H x₂ ⊕ (u,0) = w}`; the middle part is `F₂^l`, `l = l₁ + l₂`. -/
def matX (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (r : Finset (Vec d) × Vec l₁)
    (w : Vec (l₁ + l₂)) : ℕ :=
  (r.1.filter fun x => H x + Fin.append r.2 (0 : Vec l₂) = w).card

/-- `Y[w, (b₃,v)] = #{x₃ ∈ b₃ : H x₃ ⊕ (0,v) = w}`. -/
def matY (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (w : Vec (l₁ + l₂))
    (c : Finset (Vec d) × Vec l₂) : ℕ :=
  (c.1.filter fun x => H x + Fin.append (0 : Vec l₁) c.2 = w).card

/-- The position `((b₂,u),(b₃,v))` of a probe, `(u,v) := H x₁`. -/
def pos {k : ℕ} (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (Q : Probe d k) :
    (Finset (Vec d) × Vec l₁) × (Finset (Vec d) × Vec l₂) :=
  ((Q.2.1.2, fun i => H Q.1 (Fin.castAdd l₂ i)), (Q.2.2.2, fun i => H Q.1 (Fin.natAdd l₁ i)))

/-- **Lemma II.2 (counts)**: `(XY)` at the position of a probe is `cnt_H(Q)`. -/
theorem matXY_pos {k : ℕ} (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (Q : Probe d k) :
    ∑ w, matX H (pos H Q).1 w * matY H w (pos H Q).2 = (probeCands d k).cnt H Q := by
  set u : Vec l₁ := fun i => H Q.1 (Fin.castAdd l₂ i)
  set v : Vec l₂ := fun i => H Q.1 (Fin.natAdd l₁ i)
  have huv : Fin.append u (0 : Vec l₂) + Fin.append (0 : Vec l₁) v = H Q.1 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [u, Fin.append_left]
    · simp [v, Fin.append_right]
  unfold matX matY pos Cands.cnt probeCands
  simp only
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Vec d × Vec d => H p.1 + Fin.append u 0)
    (t := univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.card_product]
  congr 1
  ext ⟨x₂, x₃⟩
  simp only [Finset.mem_filter, Finset.mem_product]
  have key : H (Q.1 + x₂ + x₃) = 0 ↔ H x₂ + Fin.append u 0 = H x₃ + Fin.append 0 v := by
    rw [veq_iff (H x₂ + Fin.append u 0), map_add, map_add, ← huv]
    have : H x₂ + Fin.append u 0 + (H x₃ + Fin.append 0 v) =
        Fin.append u 0 + Fin.append 0 v + H x₂ + H x₃ := by abel
    rw [this]
  rw [key]
  constructor
  · rintro ⟨⟨h2, e2⟩, h3, e3⟩
    exact ⟨⟨⟨h2, h3⟩, e2.trans e3.symm⟩, e2⟩
  · rintro ⟨⟨⟨h2, h3⟩, e⟩, e'⟩
    exact ⟨⟨h2, e'⟩, h3, e.symm.trans e'⟩

/-- The entries of `X` and `Y` lie in `{0, …, σ}` when the blocks have at most `σ` elements. -/
theorem matX_le (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (r : Finset (Vec d) × Vec l₁)
    (w : Vec (l₁ + l₂)) : matX H r w ≤ r.1.card := Finset.card_filter_le _ _

theorem matY_le (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (w : Vec (l₁ + l₂))
    (c : Finset (Vec d) × Vec l₂) : matY H w c ≤ c.1.card := Finset.card_filter_le _ _

/-! ### Binary splitting (Lemma II.3, "Entries") -/

/-- The `i`-th binary digit. -/
def bit (i x : ℕ) : ℕ := x / 2 ^ i % 2

theorem sum_bits (B x : ℕ) (hx : x < 2 ^ B) : ∑ i ∈ range B, 2 ^ i * bit i x = x := by
  induction B generalizing x with
  | zero => simp at hx; simp [hx]
  | succ B ih =>
    rw [Finset.sum_range_succ']
    have hb : ∀ i, bit (i + 1) x = bit i (x / 2) := by
      intro i; unfold bit; rw [Nat.div_div_eq_div_mul, pow_succ']
    simp only [hb, pow_succ, mul_assoc]
    have : ∑ i ∈ range B, 2 ^ i * (2 * bit i (x / 2)) = 2 * ∑ i ∈ range B, 2 ^ i * bit i (x / 2) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, ih (x / 2) (by rw [pow_succ] at hx; omega)]
    unfold bit; simp; omega

/-- `XY = Σ_{i,j<B} 2^{i+j} X_i Y_j` for entries below `2^B` (bilinearity). -/
theorem matmul_bits {R K M : Type*} [Fintype M] (X : R → M → ℕ) (Y : M → K → ℕ) (B : ℕ)
    (r : R) (c : K) (hX : ∀ w, X r w < 2 ^ B) (hY : ∀ w, Y w c < 2 ^ B) :
    ∑ w, X r w * Y w c =
      ∑ i ∈ range B, ∑ j ∈ range B, 2 ^ (i + j) * ∑ w, bit i (X r w) * bit j (Y w c) := by
  have h1 : ∑ w, X r w * Y w c = ∑ w, ∑ i ∈ range B, ∑ j ∈ range B,
      (2 ^ i * bit i (X r w)) * (2 ^ j * bit j (Y w c)) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_mul_sum, sum_bits B _ (hX w), sum_bits B _ (hY w)]
  rw [h1]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

/-- The `0/1` instance of `#Lop` for the digit matrices `X_i`, `Y_j`, with middle part `M`. -/
def bitInst {R K M : Type*} [Fintype M] (X : R → M → ℕ) (Y : M → K → ℕ) (i j : ℕ)
    (W : Finset (R × K)) : LopInst R K M where
  mid := univ
  adjA r w := bit i (X r w) = 1
  adjB w c := bit j (Y w c) = 1
  W := W

/-- The oracle's answer on a digit instance is `Σ_w X_i Y_j`. -/
theorem bitInst_count {R K M : Type*} [Fintype M] (X : R → M → ℕ) (Y : M → K → ℕ) (i j : ℕ)
    (W : Finset (R × K)) (r : R) (c : K) :
    (bitInst X Y i j W).count r c = ∑ w, bit i (X r w) * bit j (Y w c) := by
  have h2 : ∀ x i, bit i x < 2 := fun x i => Nat.mod_lt _ (by norm_num)
  unfold LopInst.count bitInst
  simp only
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  have ha := h2 (X r w) i
  have hb := h2 (Y w c) j
  generalize bit i (X r w) = a at ha ⊢
  generalize bit j (Y w c) = b at hb ⊢
  interval_cases a <;> interval_cases b <;> simp

/-- **Lemmas II.2 and II.3 together**: `cnt_H(Q) = Σ_{i,j<B} 2^{i+j} · (the #Lop count of the
digit instance (i, j) at the position of Q)`, when blocks have at most `σ < 2^B` elements. This is
a count identity: the instances are indexed by the blocks themselves (not by `g'` numbered slots),
the query set `W` plays no role in the count, and the vertex numbers `N = g' 2^{⌈l/2⌉}`, `D = 2^l`
appear only in the inequalities of `ImprovedArith.lean`. The composition with numbered
instances, the parts of `W` and the parameters is `evalCalls_spec` and
`xor_direct_count_eval_params` in `ImprovedCallsProbes.lean`. -/
theorem cnt_eq_oracle {k : ℕ} (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (σ B : ℕ)
    (hB : σ < 2 ^ B) (W : Finset ((Finset (Vec d) × Vec l₁) × (Finset (Vec d) × Vec l₂)))
    (Q : Probe d k) (hb₂ : Q.2.1.2.card ≤ σ) (hb₃ : Q.2.2.2.card ≤ σ) :
    (probeCands d k).cnt H Q = ∑ i ∈ range B, ∑ j ∈ range B,
      2 ^ (i + j) * (bitInst (matX H) (matY H) i j W).count (pos H Q).1 (pos H Q).2 := by
  rw [← matXY_pos, matmul_bits _ _ B _ _ (fun w => (matX_le H _ w).trans_lt (by
      exact lt_of_le_of_lt hb₂ hB)) (fun w => (matY_le H w _).trans_lt (lt_of_le_of_lt hb₃ hB))]
  simp only [bitInst_count]

/-! ### Theorem II: correctness -/

/-- **Theorem II, correctness (Lemma II.5)**: for any linear `π`, any blocks of at most `σ`
elements, a `(1/q)`-biased `E` with `e 2^{-q} σ² ≤ 1/2`, any number `L` of stages, and rows
chosen greedily on `Σ = Σ_Q cnt_H(Q)` (the sums the oracle supplies, by `cnt_eq_oracle`; that
identity is a separate lemma, not composed here; the version with the rule greedy on the
oracle's sums is `xor_direct_count_correct_oracle` in `ImprovedCallsProbes.lean`), the algorithm of §4.5 answers YES iff the
instance has a solution. -/
theorem xor_direct_count_correct (S₁ S₂ S₃ : Finset (Vec d)) {k : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k)
    (σ q L : ℕ) (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    (E : Multiset (Vec d)) (hE : IsBiased (1 / (q : ℝ)) E) (hq : 0 < q)
    (hqσ : Real.exp 1 * (2 : ℝ)⁻¹ ^ q * (σ ^ 2 : ℕ) ≤ 1 / 2)
    (rowsOf : Finset (Probe d k) → List (Vec d)) (hrule : (probeCands d k).GreedyRule E q rowsOf) :
    (probeCands d k).run rowsOf L (probes S₁ π B₂ B₃) = true ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0 := by
  rw [(probeCands d k).run_iff E q (σ ^ 2) hE hq hqσ rowsOf hrule _
    (probe_card_fam_le S₁ S₂ S₃ π B₂ B₃) L]
  exact (exists_sol_iff_probe S₁ S₂ S₃ π B₂ B₃).symm

/-- **Theorem II, search version**: if a decision procedure `dec` answers, for every sublist `l`
of candidates for `x₁`, whether `l` (as a set) with `S₂, S₃` has a solution (Theorem II's
algorithm does, by `xor_direct_count_correct`), then `⌈log₂ |l|⌉` halvings return an `x₁ ∈ l` that lies
in a solution, whenever one exists. -/
theorem xor_direct_count_search (S₂ S₃ : Finset (Vec d)) (dec : List (Vec d) → Bool)
    (hdec : ∀ l : List (Vec d), dec l = true ↔ ∃ x₁ ∈ l, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0)
    (l : List (Vec d)) (hl : ∃ x₁ ∈ l, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) :
    ∃ x₁ ∈ l, findOne dec (Nat.clog 2 l.length) l = some x₁ ∧
      ∃ x₂ ∈ S₂, x₁ + x₂ ∈ S₃ := by
  obtain ⟨x₁, hx, hf, x₂, h₂, x₃, h₃, h0⟩ := findOne_spec dec
    (fun x₁ => ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) hdec _ l
    (Nat.le_pow_clog (by norm_num) _) hl
  exact ⟨x₁, hx, hf, x₂, h₂, (vsum_zero_iff _ _ _).1 h0 ▸ h₃⟩

end Xor.Improved

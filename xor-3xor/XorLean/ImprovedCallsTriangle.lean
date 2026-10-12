import XorLean.ImprovedCalls

/-!
# Improved 3XOR, Theorem III (§5): the oracle calls of Lemma III.1, built and composed

`ImprovedTriangle.lean` proves the count identity of the instance `J(H, k, ϱ, 𝒬)` (`J_count`),
the size of its middle part (`J_mid_card`), and the correctness of (a) and (b) of Theorem III
with the row rule greedy on `Σ_x cnt_H(x)`. `ImprovedArith.lean` proves the call conditions of
Lemma III.1 as free real inequalities. This file builds the calls and states the conditions on
them:

* `incClass`: the class `(k, ϱ)` of a set `𝓘` of incidences (the pairs `(a, b)` with
  `(a, b, k) ∈ 𝓘` and `H w(a, b) = ϱ`).
* `triCall`: one oracle call, `J(H, k, ϱ, 𝒬)` with sides `A`, `B` numbered into `Fin n` (padded
  with isolated vertices); its count does not depend on `𝒬` (`triCall_countAt_congr`).
* `lemmaIII1_calls`: Lemma III.1 for any chunk size `M`: the calls (one per chunk of each class),
  each `Lop(n, σ 2^r)` with at most `M` query pairs, at most `Σ_ϱ ⌈|class|/M⌉ ≤ 2^r + n²/M` calls
  per piece, every incidence in exactly one call, whose answer at its numbered pair is `cnt_H`.
* `lemmaIII1_calls_params`: the same with the parameters of §5: `D = σ 2^l ≤ n^ε`,
  `M = ⌊n²/√D⌋`, at most `2^l + 2√D` calls per piece. `triangle_pieces_exist`: the pieces.
* `incOracleCnt`, `incOracleTotal`, `runOracle`, `incOracleMu`, `aeStepOracle`, `aeRunOracle`:
  the algorithms of (a) and (b) reading every count from the oracle's answers, with the row rule
  greedy on the oracle's sums; `exact_xor_triangle_full_detect_oracle`,
  `exact_xor_triangle_full_allEdges_oracle`, `aeStep_halving_oracle` are the correctness and the
  halving for these.

The running times (`triangle_call_cost`, `triangle_pieces`) are not composed here.
-/

set_option linter.unusedSectionVars false

namespace Xor.Improved
open Xor Finset

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] {d : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-! ### (a) The classes and one call -/

/-- The class `(k, ϱ)` of a set `𝓘` of incidences: the pairs `(a, b)` of the incidences
`(a, b, k) ∈ 𝓘` with `H w(a, b) = ϱ` (Lemma III.1: "group the incidences by piece `k` and class
`ϱ`"). -/
def incClass (I : TriInst A B C d) {r : ℕ} (H : Vec d →ₗ[ZMod 2] Vec r)
    (𝓘 : Finset (A × B × κ)) (k : κ) (ϱ : Vec r) : Finset (A × B) :=
  (𝓘.filter fun x => x.2.2 = k ∧ H (I.wab x.1 x.2.1) = ϱ).image pairOf

theorem mem_incClass (I : TriInst A B C d) {r : ℕ} (H : Vec d →ₗ[ZMod 2] Vec r)
    (𝓘 : Finset (A × B × κ)) (k : κ) (ϱ : Vec r) (p : A × B) :
    p ∈ incClass I H 𝓘 k ϱ ↔ (p.1, p.2, k) ∈ 𝓘 ∧ H (I.wab p.1 p.2) = ϱ := by
  unfold incClass
  simp only [mem_image, mem_filter, pairOf]
  constructor
  · rintro ⟨x, ⟨hx, hk, hϱ⟩, rfl⟩
    subst hk
    exact ⟨hx, hϱ⟩
  · rintro ⟨hx, hϱ⟩
    exact ⟨(p.1, p.2, k), ⟨hx, rfl, hϱ⟩, rfl⟩

/-- A class lies in the class `W_ϱ` of all pairs (`classOf` of `Reduction.lean`). -/
theorem incClass_subset_classOf (I : TriInst A B C d) {r : ℕ} (H : Vec d →ₗ[ZMod 2] Vec r)
    (𝓘 : Finset (A × B × κ)) (k : κ) (ϱ : Vec r) : incClass I H 𝓘 k ϱ ⊆ classOf I H ϱ := by
  intro p hp
  simp only [classOf, mem_filter, mem_univ, true_and]
  exact ((mem_incClass I H 𝓘 k ϱ p).1 hp).2

/-- For a fixed piece the classes have at most `|A||B| ≤ n²` pairs together. -/
theorem sum_incClass_card_le (I : TriInst A B C d) {r : ℕ} (H : Vec d →ₗ[ZMod 2] Vec r)
    (𝓘 : Finset (A × B × κ)) (k : κ) (n : ℕ) (hA : Fintype.card A ≤ n)
    (hB : Fintype.card B ≤ n) : ∑ ϱ : Vec r, (incClass I H 𝓘 k ϱ).card ≤ n ^ 2 := by
  have hsum : ∑ ϱ : Vec r, (classOf I H ϱ).card = Fintype.card A * Fintype.card B := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun p : A × B => H (I.wab p.1 p.2))
      (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    rw [Finset.card_univ, Fintype.card_prod] at this
    rw [this]
    rfl
  calc ∑ ϱ : Vec r, (incClass I H 𝓘 k ϱ).card ≤ ∑ ϱ : Vec r, (classOf I H ϱ).card :=
        Finset.sum_le_sum fun ϱ _ => Finset.card_le_card (incClass_subset_classOf I H 𝓘 k ϱ)
    _ = Fintype.card A * Fintype.card B := hsum
    _ ≤ n * n := Nat.mul_le_mul hA hB
    _ = n ^ 2 := (sq n).symm

/-- **One oracle call** of Lemma III.1: the instance `J(H, k, ϱ, 𝒬)` (`redInst` with `H` for the
hash, the piece `C_k`, the query pairs `𝒬`), its sides `A` and `B` numbered into `Fin n` by the
canonical numberings and padded with isolated vertices. -/
noncomputable def triCall (I : TriInst A B C d) (pieces : κ → Finset C) {r : ℕ}
    (H : Vec d →ₗ[ZMod 2] Vec r) (n : ℕ) (k : κ) (ϱ : Vec r) (Qc : Finset (A × B)) :
    LopInst (Fin n) (Fin n) (C × Vec r) :=
  (redInst I H ϱ Qc (pieces k)).number univ univ (numbering univ) (numbering univ) n

/-- The oracle's count does not depend on the query pairs `𝒬` (only `W` changes). -/
theorem triCall_countAt_congr (I : TriInst A B C d) (pieces : κ → Finset C) {r : ℕ}
    (H : Vec d →ₗ[ZMod 2] Vec r) (n : ℕ) (k : κ) (ϱ : Vec r) (Qc Qc' : Finset (A × B))
    (i j : ℕ) :
    (triCall I pieces H n k ϱ Qc).countAt i j = (triCall I pieces H n k ϱ Qc').countAt i j :=
  LopInst.countAt_congr_W _ _ rfl rfl rfl i j

section call
variable (I : TriInst A B C d) (pieces : κ → Finset C) {r : ℕ} (H : Vec d →ₗ[ZMod 2] Vec r)
  {n : ℕ} (k : κ) (ϱ : Vec r) (Qc : Finset (A × B))

/-- `Lop(n, D)` for a call is `|C_k| 2^r ≤ D` (the sides have `n` vertices by construction). -/
theorem triCall_isLop (D : ℕ) :
    (triCall I pieces H n k ϱ Qc).IsLop n D ↔ (pieces k).card * 2 ^ r ≤ D := by
  unfold triCall
  rw [LopInst.number_isLop, J_mid_card]

variable {I pieces H k ϱ Qc}

theorem triCall_queries (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) :
    (triCall I pieces H n k ϱ Qc).queries =
      Qc.image fun p => (numbering univ p.1, numbering univ p.2) := by
  obtain ⟨-, hAN⟩ := numbering_spec (univ : Finset A) n (by rw [card_univ]; exact hA)
  obtain ⟨-, hBN⟩ := numbering_spec (univ : Finset B) n (by rw [card_univ]; exact hB)
  exact LopInst.number_queries (fun _ _ => mem_product.2 ⟨mem_univ _, mem_univ _⟩) hAN hBN

/-- A call has exactly `|𝒬|` query pairs. -/
theorem triCall_W_card (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) :
    (triCall I pieces H n k ϱ Qc).W.card = Qc.card := by
  obtain ⟨hAi, hAN⟩ := numbering_spec (univ : Finset A) n (by rw [card_univ]; exact hA)
  obtain ⟨hBi, hBN⟩ := numbering_spec (univ : Finset B) n (by rw [card_univ]; exact hB)
  exact LopInst.number_W_card hAi hBi (fun _ _ => mem_product.2 ⟨mem_univ _, mem_univ _⟩) hAN hBN

/-- **The count of a call** (`J_count` and `number_count`): for `H w(a, b) = ϱ`, the oracle's
`#Lop` answer at the numbered pair of `(a, b)` is `cnt_H(a, b, k)`. -/
theorem triCall_countAt (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (a : A) (b : B)
    (hab : H (I.wab a b) = ϱ) :
    (triCall I pieces H n k ϱ Qc).countAt (numbering univ a) (numbering univ b) =
      (incCands I pieces).cnt H (a, b, k) := by
  obtain ⟨hAi, hAN⟩ := numbering_spec (univ : Finset A) n (by rw [card_univ]; exact hA)
  obtain ⟨hBi, hBN⟩ := numbering_spec (univ : Finset B) n (by rw [card_univ]; exact hB)
  exact (LopInst.number_count hAi hBi hAN hBN (mem_univ a) (mem_univ b)).trans
    (J_count I H ϱ Qc pieces a b k hab)

/-- The detection answer of a call at a numbered pair: some `c ∈ C_k` with `H S(a,b,c) = 0`. -/
theorem triCall_acceptsAt (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (a : A) (b : B)
    (hab : H (I.wab a b) = ϱ) :
    (triCall I pieces H n k ϱ Qc).AcceptsAt (numbering univ a) (numbering univ b) ↔
      ∃ c ∈ pieces k, H (I.S a b c) = 0 := by
  obtain ⟨hAi, hAN⟩ := numbering_spec (univ : Finset A) n (by rw [card_univ]; exact hA)
  obtain ⟨hBi, hBN⟩ := numbering_spec (univ : Finset B) n (by rw [card_univ]; exact hB)
  exact (LopInst.number_accepts hAi hBi hAN hBN (mem_univ a) (mem_univ b)).trans
    (redInst_accepts_iff I H ϱ Qc (pieces k) a b hab)

end call

/-! ### (b) Lemma III.1 on the built calls, for any chunk size -/

/-- **Lemma III.1, the calls** (the counting part; the times are not composed). Parts `A`, `B` of
at most `n` vertices, pieces of at most `σ` vertices, any `H` with `r` rows, any set `𝓘` of
incidences, any chunk size `M > 0`. Cutting each class `(k, ϱ)` into chunks of at most `M` pairs
(`exists_cutting`) and making one call `triCall … k ϱ 𝒬` per chunk `𝒬` gives a set `calls` of
triples `(k, ϱ, 𝒬)` with:
* each chunk lies in its class and has at most `M` pairs; each call is `Lop(n, σ 2^r)` and has
  exactly `|𝒬|` query pairs;
* piece `k` has at most `Σ_ϱ ⌈|class(k,ϱ)|/M⌉ ≤ 2^r + n²/M` calls; in all at most
  `Σ_k Σ_ϱ ⌈|class(k,ϱ)|/M⌉ ≤ h (2^r + n²/M)` calls, `h` the number of pieces;
* every incidence `x = (a, b, k) ∈ 𝓘` lies in exactly one call (`c.1 = k`, `(a, b) ∈ 𝒬`); that
  call has `ϱ = H w(a, b)`, the numbered pair of `(a, b)` is one of its query pairs, and the
  oracle's count there is `cnt_H(x)`. -/
theorem lemmaIII1_calls (I : TriInst A B C d) (pieces : κ → Finset C) (n σ : ℕ)
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (hσ : ∀ k, (pieces k).card ≤ σ)
    {r : ℕ} (H : Vec d →ₗ[ZMod 2] Vec r) (𝓘 : Finset (A × B × κ)) (M : ℕ) (hM : 0 < M) :
    ∃ calls : Finset (κ × Vec r × Finset (A × B)),
      (∀ c ∈ calls, c.2.2 ⊆ incClass I H 𝓘 c.1 c.2.1 ∧ c.2.2.card ≤ M ∧
        (triCall I pieces H n c.1 c.2.1 c.2.2).IsLop n (σ * 2 ^ r) ∧
        (triCall I pieces H n c.1 c.2.1 c.2.2).W.card = c.2.2.card) ∧
      (∀ k, (calls.filter fun c => c.1 = k).card ≤
          ∑ ϱ : Vec r, ((incClass I H 𝓘 k ϱ).card + M - 1) / M) ∧
      (∀ k, ((calls.filter fun c => c.1 = k).card : ℝ) ≤ 2 ^ r + (n : ℝ) ^ 2 / M) ∧
      calls.card ≤ ∑ k : κ, ∑ ϱ : Vec r, ((incClass I H 𝓘 k ϱ).card + M - 1) / M ∧
      (calls.card : ℝ) ≤ Fintype.card κ * (2 ^ r + (n : ℝ) ^ 2 / M) ∧
      (∀ x ∈ 𝓘, ∃! c, c ∈ calls ∧ c.1 = x.2.2 ∧ pairOf x ∈ c.2.2) ∧
      (∀ x ∈ 𝓘, ∀ c ∈ calls, c.1 = x.2.2 → pairOf x ∈ c.2.2 →
        c.2.1 = H (I.wab x.1 x.2.1) ∧
        (numbering univ x.1, numbering univ x.2.1) ∈
          (triCall I pieces H n c.1 c.2.1 c.2.2).queries ∧
        (triCall I pieces H n c.1 c.2.1 c.2.2).countAt (numbering univ x.1)
          (numbering univ x.2.1) = (incCands I pieces).cnt H x) := by
  choose chunks hch1 hch2 hch3 using
    fun (k : κ) (ϱ : Vec r) => exists_cutting (incClass I H 𝓘 k ϱ) M hM
  let calls : Finset (κ × Vec r × Finset (A × B)) :=
    univ.biUnion fun k => univ.biUnion fun ϱ => (chunks k ϱ).image fun Q => (k, ϱ, Q)
  have hmem : ∀ c, c ∈ calls ↔ c.2.2 ∈ chunks c.1 c.2.1 := by
    rintro ⟨k, ϱ, Q⟩
    simp only [calls, mem_biUnion, mem_univ, true_and, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨k', ϱ', Q', hQ', rfl, rfl, rfl⟩
      exact hQ'
    · intro hQ
      exact ⟨k, ϱ, Q, hQ, rfl, rfl, rfl⟩
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  -- calls per piece
  have hk : ∀ k, (calls.filter fun c => c.1 = k).card ≤
      ∑ ϱ : Vec r, ((incClass I H 𝓘 k ϱ).card + M - 1) / M := by
    intro k
    have hsub : (calls.filter fun c => c.1 = k) ⊆
        univ.biUnion fun ϱ => (chunks k ϱ).image fun Q => (k, ϱ, Q) := by
      rintro ⟨k', ϱ, Q⟩ hc
      rw [mem_filter, hmem] at hc
      obtain ⟨hc, hk'⟩ := hc
      simp only at hc hk'
      subst hk'
      exact mem_biUnion.2 ⟨ϱ, mem_univ _, mem_image.2 ⟨Q, hc, rfl⟩⟩
    calc (calls.filter fun c => c.1 = k).card
        ≤ (univ.biUnion fun ϱ => (chunks k ϱ).image fun Q => (k, ϱ, Q)).card :=
          card_le_card hsub
      _ ≤ ∑ ϱ : Vec r, ((chunks k ϱ).image fun Q => (k, ϱ, Q)).card := card_biUnion_le
      _ ≤ ∑ ϱ : Vec r, ((incClass I H 𝓘 k ϱ).card + M - 1) / M :=
          sum_le_sum fun ϱ _ => card_image_le.trans (hch3 k ϱ)
  have hkR : ∀ k, ((calls.filter fun c => c.1 = k).card : ℝ) ≤ 2 ^ r + (n : ℝ) ^ 2 / M := by
    intro k
    have h1 := sum_ceil_div_le (univ : Finset (Vec r)) (fun ϱ => (incClass I H 𝓘 k ϱ).card) M hM
    have hcard : ((univ : Finset (Vec r)).card : ℝ) = 2 ^ r := by
      simp [Finset.card_univ, ZMod.card]
    have hs : (∑ ϱ : Vec r, ((incClass I H 𝓘 k ϱ).card : ℝ)) ≤ (n : ℝ) ^ 2 := by
      exact_mod_cast sum_incClass_card_le I H 𝓘 k n hA hB
    have h2 : (∑ ϱ : Vec r, ((incClass I H 𝓘 k ϱ).card : ℝ)) / M ≤ (n : ℝ) ^ 2 / M :=
      div_le_div_of_nonneg_right hs hMR.le
    have h3 : ((calls.filter fun c => c.1 = k).card : ℝ) ≤
        ((∑ ϱ : Vec r, ((incClass I H 𝓘 k ϱ).card + M - 1) / M : ℕ) : ℝ) := by
      exact_mod_cast hk k
    rw [hcard] at h1
    linarith
  have hfib : calls.card = ∑ k : κ, (calls.filter fun c => c.1 = k).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  refine ⟨calls, ?_, hk, hkR, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have hQ := (hmem c).1 hc
    refine ⟨(hch1 _ _ _ hQ).1, (hch1 _ _ _ hQ).2, ?_, triCall_W_card hA hB⟩
    rw [triCall_isLop]
    exact Nat.mul_le_mul_right _ (hσ _)
  · rw [hfib]
    exact sum_le_sum fun k _ => hk k
  · rw [hfib]
    push_cast
    calc ∑ k : κ, ((calls.filter fun c => c.1 = k).card : ℝ)
        ≤ ∑ _k : κ, (2 ^ r + (n : ℝ) ^ 2 / M) := sum_le_sum fun k _ => hkR k
      _ = Fintype.card κ * (2 ^ r + (n : ℝ) ^ 2 / M) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
  · intro x hx
    have hcl : pairOf x ∈ incClass I H 𝓘 x.2.2 (H (I.wab x.1 x.2.1)) :=
      (mem_incClass I H 𝓘 _ _ _).2 ⟨hx, rfl⟩
    obtain ⟨Q, ⟨hQ, hxQ⟩, huniq⟩ := hch2 x.2.2 (H (I.wab x.1 x.2.1)) (pairOf x) hcl
    refine ⟨(x.2.2, H (I.wab x.1 x.2.1), Q), ⟨(hmem _).2 hQ, rfl, hxQ⟩, ?_⟩
    rintro ⟨k', ϱ', Q'⟩ ⟨hc, hk', hxQ'⟩
    simp only at hk' hxQ'
    subst hk'
    have hc' := (hmem _).1 hc
    simp only at hc'
    have hϱ : ϱ' = H (I.wab x.1 x.2.1) :=
      ((mem_incClass I H 𝓘 _ _ _).1 ((hch1 _ _ Q' hc').1 hxQ')).2.symm
    subst hϱ
    rw [huniq Q' ⟨hc', hxQ'⟩]
  · intro x _ c hc hc1 hxc
    have hQ := (hmem c).1 hc
    have hϱ : c.2.1 = H (I.wab x.1 x.2.1) :=
      ((mem_incClass I H 𝓘 _ _ _).1 ((hch1 _ _ _ hQ).1 hxc)).2.symm
    refine ⟨hϱ, ?_, ?_⟩
    · rw [triCall_queries hA hB]
      exact mem_image.2 ⟨pairOf x, hxc, rfl⟩
    · rw [triCall_countAt hA hB x.1 x.2.1 hϱ.symm, hc1]

/-! ### (c) Lemma III.1 with the parameters of §5 -/

/-- **The pieces of §5**: for `1 ≤ σ ≤ n` and `|C| ≤ n`, `C` is cut into pairwise disjoint
pieces of at most `σ` vertices covering `C` (each vertex in exactly one piece), at most
`⌈n/σ⌉ ≤ 2n/σ` of them. Index a family by the pieces themselves (`κ := ↥P`,
`pieces := Subtype.val`, `Fintype.card κ = |P|`). -/
theorem triangle_pieces_exist (n σ : ℕ) (hC : Fintype.card C ≤ n) (hσ : 1 ≤ σ) (hσn : σ ≤ n) :
    ∃ P : Finset (Finset C), (∀ Y ∈ P, Y.card ≤ σ) ∧ (∀ c, ∃! Y, Y ∈ P ∧ c ∈ Y) ∧
      P.card ≤ (n + σ - 1) / σ ∧ (P.card : ℝ) ≤ 2 * n / σ := by
  obtain ⟨P, h1, h2, h3⟩ := exists_cutting (univ : Finset C) σ hσ
  have h3' : P.card ≤ (n + σ - 1) / σ := by
    rw [card_univ] at h3
    exact h3.trans (Nat.div_le_div_right (by omega))
  refine ⟨P, fun Y hY => (h1 Y hY).2, fun c => h2 c (mem_univ c), h3', ?_⟩
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hnσ : (σ : ℝ) ≤ n := by exact_mod_cast hσn
  have hdiv : (((n + σ - 1) / σ : ℕ) : ℝ) ≤ n / σ + 1 := by
    refine Nat.cast_div_le.trans ?_
    have : ((n + σ - 1 : ℕ) : ℝ) ≤ n + σ := by
      have : n + σ - 1 ≤ n + σ := by omega
      exact_mod_cast this
    calc ((n + σ - 1 : ℕ) : ℝ) / σ ≤ (n + σ) / σ := div_le_div_of_nonneg_right this hσR.le
      _ = n / σ + 1 := by rw [add_div, div_self hσR.ne']
  have h1n : (1 : ℝ) ≤ n / σ := by rw [le_div_iff₀ hσR]; linarith
  have : (2 : ℝ) * n / σ = 2 * (n / σ) := by ring
  calc (P.card : ℝ) ≤ (((n + σ - 1) / σ : ℕ) : ℝ) := by exact_mod_cast h3'
    _ ≤ 2 * n / σ := by linarith

/-- **Lemma III.1 with the parameters of §5** (style of `reduction_spec`). With `0 < ε ≤ 1`,
`Λ := 8e`, `σ := ⌊√(n^ε/Λ)⌋ ≥ 1`, `q := ⌈log₂(2eσ)⌉ + 1` (`triangle_params`), parts `A`, `B` of
at most `n` vertices, pieces of at most `σ` vertices, rows `rows` with `1 ≤ l := |rows| ≤ q`,
`H := rowsMap rows`, `D := σ 2^l`, `M := ⌊n²/√D⌋`, and any set `𝓘` of incidences:
`2 ≤ D ≤ n^ε`, `M > 0`, and there are calls (one per chunk of each class `(k, ϱ)`) with
* each call `Lop(n, D)` with at most `⌊n²/√D⌋` query pairs (exactly its chunk);
* at most `2^l + 2√D = 2^l + 2√(σ 2^l)` calls per piece, at most `h (2^l + 2√D)` in all for
  `h` pieces, and at most `(2n/σ)(2^l + 2√D)` when `h ≤ 2n/σ` (`triangle_pieces_exist`);
* every incidence in exactly one call, whose answer at its numbered pair is `cnt_H(x)`.
The cost of the calls (`triangle_call_cost`, `triangle_pieces`) is not composed. -/
theorem lemmaIII1_calls_params (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ)
    (I : TriInst A B C d) (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n)
    (pieces : κ → Finset C) (rows : List (Vec d)) (𝓘 : Finset (A × B × κ)) :
    let Λ := 8 * Real.exp 1
    let σ := ⌊Real.sqrt ((n : ℝ) ^ ε / Λ)⌋₊
    let q := ⌈Real.logb 2 (2 * Real.exp 1 * σ)⌉₊ + 1
    let D := σ * 2 ^ rows.length
    let M := ⌊(n : ℝ) ^ 2 / Real.sqrt D⌋₊
    1 ≤ σ → (∀ k, (pieces k).card ≤ σ) → 1 ≤ rows.length → rows.length ≤ q →
    2 ≤ D ∧ (D : ℝ) ≤ (n : ℝ) ^ ε ∧ 0 < M ∧
    ∃ calls : Finset (κ × Vec rows.length × Finset (A × B)),
      (∀ c ∈ calls, c.2.2 ⊆ incClass I (rowsMap rows) 𝓘 c.1 c.2.1 ∧
        (triCall I pieces (rowsMap rows) n c.1 c.2.1 c.2.2).IsLop n D ∧
        (triCall I pieces (rowsMap rows) n c.1 c.2.1 c.2.2).W.card = c.2.2.card ∧
        c.2.2.card ≤ ⌊(n : ℝ) ^ 2 / Real.sqrt D⌋₊) ∧
      (∀ k, ((calls.filter fun c => c.1 = k).card : ℝ) ≤ 2 ^ rows.length + 2 * Real.sqrt D) ∧
      ((calls.card : ℝ) ≤ Fintype.card κ * (2 ^ rows.length + 2 * Real.sqrt D)) ∧
      ((Fintype.card κ : ℝ) ≤ 2 * n / σ →
        (calls.card : ℝ) ≤ 2 * n / σ * (2 ^ rows.length + 2 * Real.sqrt D)) ∧
      (∀ x ∈ 𝓘, ∃! c, c ∈ calls ∧ c.1 = x.2.2 ∧ pairOf x ∈ c.2.2) ∧
      (∀ x ∈ 𝓘, ∀ c ∈ calls, c.1 = x.2.2 → pairOf x ∈ c.2.2 →
        c.2.1 = rowsMap rows (I.wab x.1 x.2.1) ∧
        (numbering univ x.1, numbering univ x.2.1) ∈
          (triCall I pieces (rowsMap rows) n c.1 c.2.1 c.2.2).queries ∧
        (triCall I pieces (rowsMap rows) n c.1 c.2.1 c.2.2).countAt (numbering univ x.1)
          (numbering univ x.2.1) = (incCands I pieces).cnt (rowsMap rows) x) := by
  dsimp only
  intro hσ1 hσ hl1 hlq
  obtain ⟨-, hqΛ, -, hΛσ, -, -⟩ := triangle_params ε hε n hσ1
  set σ := ⌊Real.sqrt ((n : ℝ) ^ ε / (8 * Real.exp 1))⌋₊ with hσdef
  set q := ⌈Real.logb 2 (2 * Real.exp 1 * σ)⌉₊ + 1 with hqdef
  set D := σ * 2 ^ rows.length with hDdef
  set M := ⌊(n : ℝ) ^ 2 / Real.sqrt D⌋₊ with hMdef
  have hσR : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  have h2l : (2 : ℝ) ^ rows.length ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hlq
  have hDR : (D : ℝ) = σ * 2 ^ rows.length := by rw [hDdef]; push_cast; ring
  have hDle : (D : ℝ) ≤ (n : ℝ) ^ ε := by
    calc (D : ℝ) = σ * 2 ^ rows.length := hDR
      _ ≤ σ * 2 ^ q := mul_le_mul_of_nonneg_left h2l (by linarith)
      _ ≤ σ * (8 * Real.exp 1 * σ) := mul_le_mul_of_nonneg_left hqΛ.le (by linarith)
      _ = 8 * Real.exp 1 * (σ : ℝ) ^ 2 := by ring
      _ ≤ (n : ℝ) ^ ε := hΛσ
  have hD2 : 2 ≤ D := by
    have := Nat.mul_le_mul hσ1 (Nat.pow_le_pow_right (show 0 < 2 by norm_num) hl1)
    simpa using this
  have hD2R : (2 : ℝ) ≤ D := by exact_mod_cast hD2
  have hn1 : (1 : ℝ) ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, Nat.cast_zero, Real.zero_rpow hε.ne'] at hDle
      linarith
    · exact_mod_cast h0
  have hnε : (n : ℝ) ^ ε ≤ n := by
    calc (n : ℝ) ^ ε ≤ (n : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hn1 hε1
      _ = n := Real.rpow_one _
  have hsD0 : 0 < Real.sqrt D := Real.sqrt_pos.2 (by linarith)
  have hsD : Real.sqrt D ≤ D := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hx1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 / Real.sqrt D := by
    rw [le_div_iff₀ hsD0]
    nlinarith
  have hMh : (n : ℝ) ^ 2 / Real.sqrt D / 2 ≤ M := floor_ge_half _ hx1
  have hMpos : 0 < M := by
    have : (0 : ℝ) < M := by linarith
    exact_mod_cast this
  have hMR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hnM : (n : ℝ) ^ 2 / M ≤ 2 * Real.sqrt D := by
    rw [div_le_iff₀ hMR]
    have hx : (n : ℝ) ^ 2 = (n : ℝ) ^ 2 / Real.sqrt D * Real.sqrt D := by field_simp
    have := mul_le_mul_of_nonneg_right (show (n : ℝ) ^ 2 / Real.sqrt D ≤ 2 * M by linarith)
      hsD0.le
    nlinarith
  obtain ⟨calls, h1, -, h3, -, h5, h6, h7⟩ :=
    lemmaIII1_calls I pieces n σ hA hB hσ (rowsMap rows) 𝓘 M hMpos
  have hper : (2 : ℝ) ^ rows.length + (n : ℝ) ^ 2 / M ≤ 2 ^ rows.length + 2 * Real.sqrt D := by
    linarith
  have hall : (calls.card : ℝ) ≤ Fintype.card κ * (2 ^ rows.length + 2 * Real.sqrt D) :=
    h5.trans (mul_le_mul_of_nonneg_left hper (Nat.cast_nonneg _))
  refine ⟨hD2, hDle, hMpos, calls, ?_, fun k => (h3 k).trans hper, hall, ?_, h6, h7⟩
  · intro c hc
    obtain ⟨hs, hM, hL, hW⟩ := h1 c hc
    exact ⟨hs, hL, hW, hM⟩
  · intro hκ
    exact hall.trans (mul_le_mul_of_nonneg_right hκ (by positivity))

/-! ### (d) The algorithms reading the oracle's answers -/

/-- The oracle's answer for an incidence `x = (a, b, k)` under the rows `rows`: the count of the
call `J(H, k, H w(a, b), {(a, b)})` at the numbered pair of `(a, b)`. By
`triCall_countAt_congr` it is the answer of every call of the class whose chunk contains
`(a, b)` (`incOracleCnt_eq_call`). -/
noncomputable def incOracleCnt (I : TriInst A B C d) (pieces : κ → Finset C) (n : ℕ)
    (rows : List (Vec d)) (x : A × B × κ) : ℕ :=
  (triCall I pieces (rowsMap rows) n x.2.2 (rowsMap rows (I.wab x.1 x.2.1)) {pairOf x}).countAt
    (numbering univ x.1) (numbering univ x.2.1)

/-- The oracle's answer is that of the call of any chunk of the class of `x`. -/
theorem incOracleCnt_eq_call (I : TriInst A B C d) (pieces : κ → Finset C) (n : ℕ)
    (rows : List (Vec d)) (x : A × B × κ) (Qc : Finset (A × B)) :
    incOracleCnt I pieces n rows x =
      (triCall I pieces (rowsMap rows) n x.2.2 (rowsMap rows (I.wab x.1 x.2.1)) Qc).countAt
        (numbering univ x.1) (numbering univ x.2.1) :=
  triCall_countAt_congr _ _ _ _ _ _ _ _ _ _

/-- With sides of at most `n` vertices, the oracle's answer is `cnt_H(x)`, for every `rows`. -/
theorem incOracleCnt_eq_cnt (I : TriInst A B C d) (pieces : κ → Finset C) {n : ℕ}
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (rows : List (Vec d))
    (x : A × B × κ) : incOracleCnt I pieces n rows x = (incCands I pieces).cnt (rowsMap rows) x :=
  triCall_countAt hA hB x.1 x.2.1 rfl

/-- The sum `Σ_{x ∈ 𝒫}` of the oracle's answers, as a function of the rows (what step 2(b)
minimizes). -/
noncomputable def incOracleTotal (I : TriInst A B C d) (pieces : κ → Finset C) (n : ℕ)
    (P : Finset (A × B × κ)) (rows : List (Vec d)) : ℝ :=
  ∑ x ∈ P, (incOracleCnt I pieces n rows x : ℝ)

theorem incOracleTotal_eq_total (I : TriInst A B C d) (pieces : κ → Finset C) {n : ℕ}
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (P : Finset (A × B × κ)) :
    incOracleTotal I pieces n P = (incCands I pieces).total P := by
  funext rows
  unfold incOracleTotal Cands.total
  simp only [incOracleCnt_eq_cnt I pieces hA hB]

/-- A row rule greedy on the oracle's sums is greedy on `Σ_x cnt_H(x)` (`GreedyRule`). -/
theorem greedyRule_oracle_iff (I : TriInst A B C d) (pieces : κ → Finset C) {n : ℕ}
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (E : Multiset (Vec d)) (q : ℕ)
    (rowsOf : Finset (A × B × κ) → List (Vec d)) :
    (∀ P, (rowsOf P).length = q ∧ IsGreedy E (incOracleTotal I pieces n P) (rowsOf P)) ↔
      (incCands I pieces).GreedyRule E q rowsOf := by
  simp only [Cands.GreedyRule, incOracleTotal_eq_total I pieces hA hB]

open Classical in
/-- The algorithm of (a) (§4.5 on incidences) with every count read from the oracle: the YES
exit `Σ_x (oracle answer) > |𝒫|/2` and the survivors `{x : oracle answer > 0}`; step 3 scans
`C_k` (`z`). -/
noncomputable def runOracle (I : TriInst A B C d) (pieces : κ → Finset C) (n : ℕ)
    (rowsOf : Finset (A × B × κ) → List (Vec d)) : ℕ → Finset (A × B × κ) → Bool
  | 0, P => decide (∃ x ∈ P, 0 < (incCands I pieces).z x)
  | t + 1, P =>
    if P.card = 0 then false
    else if P.card < 2 * ∑ x ∈ P, incOracleCnt I pieces n (rowsOf P) x then true
    else runOracle I pieces n rowsOf t (P.filter fun x => 0 < incOracleCnt I pieces n (rowsOf P) x)

/-- With sides of at most `n` vertices, `runOracle` is `run` on the incidences. -/
theorem runOracle_eq_run (I : TriInst A B C d) (pieces : κ → Finset C) {n : ℕ}
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n)
    (rowsOf : Finset (A × B × κ) → List (Vec d)) (t : ℕ) (P : Finset (A × B × κ)) :
    runOracle I pieces n rowsOf t P = (incCands I pieces).run rowsOf t P := by
  induction t generalizing P with
  | zero => simp only [runOracle, Cands.run]
  | succ t ih =>
    simp only [runOracle, Cands.run, Cands.exitYes, Cands.next,
      incOracleCnt_eq_cnt I pieces hA hB, ih]
    congr

/-- **Theorem III (a), correctness, on the oracle's answers**: the hypotheses of
`exact_xor_triangle_full_detect` with sides of at most `n` vertices, every count read from the
calls `triCall` (`runOracle`) and the rows greedy on the oracle's sums: YES iff there is a zero
triangle. -/
theorem exact_xor_triangle_full_detect_oracle (I : TriInst A B C d) (pieces : κ → Finset C)
    (hcover : ∀ c, ∃ k, c ∈ pieces k) (n σ q L : ℕ) (hA : Fintype.card A ≤ n)
    (hB : Fintype.card B ≤ n) (hσ : ∀ k, (pieces k).card ≤ σ)
    (E : Multiset (Vec d)) (hE : IsBiased (1 / (q : ℝ)) E) (hq : 0 < q)
    (hqσ : Real.exp 1 * (2 : ℝ)⁻¹ ^ q * σ ≤ 1 / 2)
    (rowsOf : Finset (A × B × κ) → List (Vec d))
    (hrule : ∀ P, (rowsOf P).length = q ∧ IsGreedy E (incOracleTotal I pieces n P) (rowsOf P)) :
    runOracle I pieces n rowsOf L univ = true ↔ I.HasZeroTriangle := by
  rw [runOracle_eq_run I pieces hA hB]
  exact exact_xor_triangle_full_detect I pieces hcover σ q L hσ E hE hq hqσ rowsOf
    ((greedyRule_oracle_iff I pieces hA hB E q rowsOf).1 hrule)

/-- `μ(x) = min_{u ∈ E}` of the oracle's answers under `(H, u)`. -/
noncomputable def incOracleMu (I : TriInst A B C d) (pieces : κ → Finset C) (n : ℕ)
    (E : Multiset (Vec d)) (H : List (Vec d)) (x : A × B × κ) : ℕ :=
  sInf {c | ∃ u ∈ E, incOracleCnt I pieces n (u :: H) x = c}

/-- The `μ` read from the oracle is `Cands.mu`. -/
theorem incOracleMu_eq_mu (I : TriInst A B C d) (pieces : κ → Finset C) {n : ℕ}
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (E : Multiset (Vec d))
    (H : List (Vec d)) (x : A × B × κ) :
    incOracleMu I pieces n E H x = (incCands I pieces).mu E H x := by
  unfold incOracleMu Cands.mu
  simp only [incOracleCnt_eq_cnt I pieces hA hB]

/-- Certified false, read from the oracle. -/
theorem certFalse_oracle_iff (I : TriInst A B C d) (pieces : κ → Finset C) {n : ℕ}
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (E : Multiset (Vec d))
    (H : List (Vec d)) (x : A × B × κ) :
    (incCands I pieces).CertFalse E H x ↔ incOracleMu I pieces n E H x = 0 := by
  rw [incOracleMu_eq_mu I pieces hA hB]
  rfl

/-- Certified true, read from the oracle. -/
theorem certTrue_oracle_iff (I : TriInst A B C d) (pieces : κ → Finset C) {n : ℕ}
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (β : ℝ) (E : Multiset (Vec d))
    (H : List (Vec d)) (x : A × B × κ) :
    (incCands I pieces).CertTrue β E H x ↔
      (1 + β) * (incOracleCnt I pieces n H x : ℝ) < 2 * (incOracleMu I pieces n E H x : ℝ) := by
  rw [incOracleMu_eq_mu I pieces hA hB, incOracleCnt_eq_cnt I pieces hA hB]
  rfl

open Classical in
/-- One stage of (b) with the certification read from the oracle (`incOracleCnt`,
`incOracleMu`); the rows `rowsOf ℐ` are given (greedy on the oracle's sums in
`aeStep_halving_oracle`). -/
noncomputable def aeStepOracle (I : TriInst A B C d) (pieces : κ → Finset C) (n : ℕ) (β : ℝ)
    (E : Multiset (Vec d)) (rowsOf : Finset (A × B × κ) → List (Vec d))
    (st : AEState A B κ) : AEState A B κ :=
  let H := rowsOf st.inc
  let marked' := st.marked ∪ (st.inc.filter fun x =>
    (1 + β) * (incOracleCnt I pieces n H x : ℝ) < 2 * (incOracleMu I pieces n E H x : ℝ)).image
      pairOf
  ⟨marked', st.inc.filter fun x => ¬ incOracleMu I pieces n E H x = 0 ∧
    ¬ (1 + β) * (incOracleCnt I pieces n H x : ℝ) < 2 * (incOracleMu I pieces n E H x : ℝ) ∧
    pairOf x ∉ marked'⟩

theorem aeStepOracle_eq (I : TriInst A B C d) (pieces : κ → Finset C) {n : ℕ}
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (β : ℝ) (E : Multiset (Vec d))
    (rowsOf : Finset (A × B × κ) → List (Vec d)) (st : AEState A B κ) :
    aeStepOracle I pieces n β E rowsOf st = aeStep I pieces β E rowsOf st := by
  have hm : ∀ p, p ∈ (aeStepOracle I pieces n β E rowsOf st).marked ↔
      p ∈ (aeStep I pieces β E rowsOf st).marked := by
    intro p
    simp only [aeStepOracle, aeStep, mem_union, mem_image, mem_filter,
      certTrue_oracle_iff I pieces hA hB]
  have hi : ∀ x, x ∈ (aeStepOracle I pieces n β E rowsOf st).inc ↔
      x ∈ (aeStep I pieces β E rowsOf st).inc := by
    intro x
    have := hm (pairOf x)
    simp only [aeStepOracle, aeStep, mem_filter] at this ⊢
    rw [this, certTrue_oracle_iff I pieces hA hB, certFalse_oracle_iff I pieces hA hB]
  have key : ∀ s t : AEState A B κ, s.marked = t.marked → s.inc = t.inc → s = t := by
    rintro ⟨_, _⟩ ⟨_, _⟩ h1 h2
    simp only at h1 h2
    subst h1 h2
    rfl
  exact key _ _ (Finset.ext hm) (Finset.ext hi)

/-- `L` stages of `aeStepOracle`. -/
noncomputable def aeRunOracle (I : TriInst A B C d) (pieces : κ → Finset C) (n : ℕ) (β : ℝ)
    (E : Multiset (Vec d)) (rowsOf : Finset (A × B × κ) → List (Vec d)) :
    ℕ → AEState A B κ → AEState A B κ
  | 0, st => st
  | t + 1, st => aeRunOracle I pieces n β E rowsOf t (aeStepOracle I pieces n β E rowsOf st)

theorem aeRunOracle_eq (I : TriInst A B C d) (pieces : κ → Finset C) {n : ℕ}
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n) (β : ℝ) (E : Multiset (Vec d))
    (rowsOf : Finset (A × B × κ) → List (Vec d)) (L : ℕ) (st : AEState A B κ) :
    aeRunOracle I pieces n β E rowsOf L st = aeRun I pieces β E rowsOf L st := by
  induction L generalizing st with
  | zero => rfl
  | succ L ih =>
    simp only [aeRunOracle, aeRun, aeStepOracle_eq I pieces hA hB, ih]

/-- **Theorem III (b), correctness, on the oracle's answers** (Lemma III.4): with sides of at
most `n` vertices and the certification read from the calls, after any number `L` of stages a
pair is answered YES iff it lies in a zero triangle (any row rule, any `β`-biased `E`). -/
theorem exact_xor_triangle_full_allEdges_oracle (I : TriInst A B C d) (pieces : κ → Finset C)
    (hcover : ∀ c, ∃ k, c ∈ pieces k) {n : ℕ} (hA : Fintype.card A ≤ n)
    (hB : Fintype.card B ≤ n) (β : ℝ) (E : Multiset (Vec d))
    (hE : IsBiased β E) (rowsOf : Finset (A × B × κ) → List (Vec d)) (L : ℕ) (a : A) (b : B) :
    (a, b) ∈ aeFinal I pieces (aeRunOracle I pieces n β E rowsOf L ⟨∅, univ⟩) ↔
      ∃ c, I.S a b c = 0 := by
  rw [aeRunOracle_eq I pieces hA hB]
  exact exact_xor_triangle_full_allEdges I pieces hcover β E hE rowsOf L a b

/-- **Lemma III.3 (halving) on the oracle's answers**: the stage `aeStepOracle` with `q − 1`
rows greedy on the oracle's sums (`q ≥ 2`, `(1/q)`-biased `E`, pieces of at most `σ` vertices,
`e 2^{-(q-1)} σ ≤ 1/2`, sides of at most `n` vertices) at least halves the incidences. -/
theorem aeStep_halving_oracle (I : TriInst A B C d) (pieces : κ → Finset C) (σ q : ℕ) {n : ℕ}
    (hA : Fintype.card A ≤ n) (hB : Fintype.card B ≤ n)
    (hσ : ∀ k, (pieces k).card ≤ σ) (E : Multiset (Vec d)) (hE : IsBiased (1 / (q : ℝ)) E)
    (hq : 2 ≤ q) (hqσ : Real.exp 1 * (2 : ℝ)⁻¹ ^ (q - 1) * σ ≤ 1 / 2)
    (rowsOf : Finset (A × B × κ) → List (Vec d))
    (hrule : ∀ P, (rowsOf P).length = q - 1 ∧
      IsGreedy E (incOracleTotal I pieces n P) (rowsOf P)) (st : AEState A B κ) :
    2 * (aeStepOracle I pieces n (1 / q) E rowsOf st).inc.card ≤ st.inc.card := by
  rw [aeStepOracle_eq I pieces hA hB]
  exact aeStep_halving I pieces σ q hσ E hE hq hqσ rowsOf
    ((greedyRule_oracle_iff I pieces hA hB E (q - 1) rowsOf).1 hrule) st

end Xor.Improved

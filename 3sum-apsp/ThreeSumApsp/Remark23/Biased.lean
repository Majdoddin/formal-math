/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Remark23.GF2Poly
public import ThreeSumApsp.Remark23.Count

/-!
# Remark 23 (3XOR): the explicit ε-biased multiset of Lemma 6

The note's Lemma 6 ([AGHP92, Proposition 3]): "Let ℓ, r ≥ 1 with ℓr ≥ 2, and let
μ := ⌈log(ℓr)⌉ ≥ 1. There is a multiset E_{ℓ,r} ⊆ F^ℓ of 4^μ < 4(ℓr)² vectors that is
(1/r)-biased".  The construction: for an irreducible `p` of degree `μ`, `GF(2^μ) = F[t]/(p)`; for
`x, y` in it, `ρ(x,y)_i = ⟨bin(x^i), bin(y)⟩`, `i = 0, …, ℓ−1`; `E` is the multiset of the `4^μ`
vectors `ρ(x,y)`.

Here the field elements are the coefficient vectors `Vec μ` (`bin` is the identity), `p` is
`polyOf q` with `μ = q.length` (file `GF2Poly`), and `x^i` is computed on lists by `powMod`, so
that a program that computes `powMod` cell by cell lists exactly `biasedSet q ℓ`:

* `rho q ℓ x y : Vec ℓ`, `rho_i = ⟨vecOf (powMod q x i), y⟩`; its list form is `rhoL`
  (`ofFn_rho`), with the list inner product `dotL`.
* `biasedSet q ℓ`: the multiset of `rho q ℓ x y` over all pairs `(x, y)` of `Vec μ`
  (`card_biasedSet`: `4^μ` elements).

Main results.

* `isBiased_biasedSet`: if `polyOf q` is irreducible, `biasedSet q ℓ` is `((ℓ−1)/2^μ)`-biased:
  the note's bound "(ℓ−1)2^μ/4^μ".  The proof is the note's: by linearity
  `⟨α, ρ(x,y)⟩ = ⟨bin(p_α(x)), y⟩` (`rho_dot`, `mk_polyV_w`); for `x` with `p_α(x) ≠ 0` the sum
  over `y` vanishes (`sum_chi_eq`), and the at most `ℓ−1` roots of `p_α` contribute `2^μ` each
  (`card_roots_le`).
* `remark_23_lemma_6`: for `ℓr ≥ 2`, `μ = ⌈log₂(ℓr)⌉` and an irreducible `polyOf q` with
  `q.length = μ`, `biasedSet q ℓ` is `(1/r)`-biased and has `4^μ < 4(ℓr)²` elements;
  `remark_23_lemma_6_exists`: such `q` exists.
* The two uses: `isBiased_theorem_8` (`ℓ = d′`, `r = ⌊log √D⌋`, the hypothesis of
  `Remark_23_theorem_8_false_positives`) and `isBiased_sec7` (`ℓ = d`, `r = k = kOf n`, the
  hypothesis of `Remark_23_lemma_12` and `Remark_23_lemma_13_goodStep`), each with the existence of
  its polynomial.
-/

@[expose] public section

namespace ThreeSumApsp.Remark23

open Polynomial

/-! ### Vectors and polynomials of degree `< μ` -/

/-- The first `μ` cells of a list as a vector (missing cells are `0`). -/
def vecOf {μ : ℕ} (l : List (ZMod 2)) : Vec μ := fun j => l.getD j 0

/-- The polynomial with coefficient vector `v`: `Σ_j v_j t^j`. -/
noncomputable def polyV {μ : ℕ} (v : Vec μ) : (ZMod 2)[X] := ∑ j : Fin μ, C (v j) * X ^ (j : ℕ)

theorem coeff_polyV {μ : ℕ} (v : Vec μ) (n : ℕ) :
    (polyV v).coeff n = if h : n < μ then v ⟨n, h⟩ else 0 := by
  simp only [polyV, finsetSum_coeff, coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e; exact hb (Fin.ext e.symm)
    · simp
  · refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; intro e; exact h (e ▸ j.2)

theorem degree_polyV_lt {μ : ℕ} (v : Vec μ) : (polyV v).degree < μ := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_polyV, dif_neg (by omega)]

theorem polyV_sub {μ : ℕ} (v w : Vec μ) : polyV (v - w) = polyV v - polyV w := by
  ext n; simp only [coeff_polyV, coeff_sub]; split_ifs <;> simp

theorem polyV_eq_zero_iff {μ : ℕ} (v : Vec μ) : polyV v = 0 ↔ v = 0 := by
  constructor
  · intro h; funext j
    have := congrArg (fun f => f.coeff j) h
    simpa [coeff_polyV, j.2] using this
  · rintro rfl; simp [polyV]

theorem polyV_sum {μ ℓ : ℕ} (α : Vec ℓ) (f : Fin ℓ → Vec μ) :
    polyV (∑ i, α i • f i) = ∑ i, C (α i) * polyV (f i) := by
  simp only [polyV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, C_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem polyV_vecOf {μ : ℕ} {l : List (ZMod 2)} (hl : l.length = μ) :
    polyV (vecOf l : Vec μ) = ofList l := by
  ext n
  rw [coeff_polyV, coeff_ofList]
  split_ifs with h
  · rfl
  · rw [getD_zero_of_ge (by omega)]

theorem ofList_ofFn {μ : ℕ} (x : Vec μ) : ofList (List.ofFn x) = polyV x := by
  ext n
  rw [coeff_polyV, coeff_ofList]
  split_ifs with h
  · rw [getD_zero_of_lt (by simpa using h)]; simp
  · rw [getD_zero_of_ge (by simp; omega)]

/-! ### The multiset -/

/-- `ρ(x,y)` of Lemma 6: "ρ(x,y)_i = ⟨bin(x^i), bin(y)⟩, i = 0, …, ℓ−1", with `x^i` modulo
`polyOf q` computed by `powMod` on the coefficient list of `x`. -/
def rho (q : List (ZMod 2)) (ℓ : ℕ) (x y : Vec q.length) : Vec ℓ :=
  fun i => (vecOf (powMod q (List.ofFn x) i) : Vec q.length) ⬝ᵥ y

/-- `E_{ℓ,r}` of Lemma 6: "the multiset of the 4^μ vectors ρ(x,y)", `x, y ∈ GF(2^μ)`, for the
field `F[t]/(polyOf q)`, `μ = q.length`. -/
def biasedSet (q : List (ZMod 2)) (ℓ : ℕ) : Multiset (Vec ℓ) :=
  (Finset.univ : Finset (Vec q.length × Vec q.length)).val.map fun xy => rho q ℓ xy.1 xy.2

theorem card_vec (μ : ℕ) : Fintype.card (Vec μ) = 2 ^ μ := by
  simp [ZMod.card]

theorem card_biasedSet (q : List (ZMod 2)) (ℓ : ℕ) : (biasedSet q ℓ).card = 4 ^ q.length := by
  simp only [biasedSet, Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_prod,
    card_vec, ← mul_pow]
  norm_num

/-- The inner product of two coefficient lists, `Σ_j a_j b_j` (the shorter length counts). -/
def dotL (a b : List (ZMod 2)) : ZMod 2 := (List.zipWith (· * ·) a b).sum

theorem dotL_cons (x y : ZMod 2) (a b : List (ZMod 2)) :
    dotL (x :: a) (y :: b) = x * y + dotL a b := by
  simp [dotL]

theorem dotL_eq_sum (a b : List (ZMod 2)) (μ : ℕ) (ha : a.length = μ) (hb : b.length = μ) :
    dotL a b = ∑ j ∈ Finset.range μ, a.getD j 0 * b.getD j 0 := by
  induction a generalizing b μ with
  | nil => subst ha; simp [dotL]
  | cons x a ih =>
    cases b with
    | nil => simp at ha hb; omega
    | cons y b =>
      subst ha
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hb
      rw [dotL_cons, ih b _ rfl hb, List.length_cons, Finset.sum_range_succ']
      simp [add_comm]

/-- `ρ(x,y)` as a list, as a program computes it: the `i`-th cell is `dotL (powMod q x i) y`. -/
def rhoL (q : List (ZMod 2)) (ℓ : ℕ) (x y : List (ZMod 2)) : List (ZMod 2) :=
  (List.range ℓ).map fun i => dotL (powMod q x i) y

theorem ofFn_rho (q : List (ZMod 2)) (ℓ : ℕ) (x y : Vec q.length) :
    List.ofFn (rho q ℓ x y) = rhoL q ℓ (List.ofFn x) (List.ofFn y) := by
  apply List.ext_getElem (by simp [rhoL])
  intro i h1 h2
  simp only [List.getElem_ofFn, rhoL, List.getElem_map, List.getElem_range, rho]
  rw [dotL_eq_sum _ _ q.length (length_powMod _ _ _) (by simp), dotProduct,
    ← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [getD_zero_of_lt (l := List.ofFn y) (by simp)]
  simp [vecOf]

/-- `ρ(x,y)` from its list form. -/
theorem rho_eq_vecOf_rhoL (q : List (ZMod 2)) (ℓ : ℕ) (x y : Vec q.length) :
    rho q ℓ x y = vecOf (rhoL q ℓ (List.ofFn x) (List.ofFn y)) := by
  funext i
  rw [vecOf, ← ofFn_rho, getD_zero_of_lt (by simp)]
  simp

/-! ### The bias -/

section Bias

variable (q : List (ZMod 2)) {ℓ : ℕ}

/-- The vector `bin(p_α(x)) = Σ_i α_i bin(x^i)`. -/
def wvec (α : Vec ℓ) (x : Vec q.length) : Vec q.length :=
  ∑ i : Fin ℓ, α i • (vecOf (powMod q (List.ofFn x) i) : Vec q.length)

/-- "By linearity, ⟨α, ρ(x,y)⟩ = ⟨bin(p_α(x)), bin(y)⟩." -/
theorem rho_dot (α : Vec ℓ) (x y : Vec q.length) : rho q ℓ x y ⬝ᵥ α = y ⬝ᵥ wvec q α x := by
  simp only [dotProduct, rho, wvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The field element of a vector, `x ↦ x mod p` in `F[t]/(polyOf q)`. -/
noncomputable def toK (x : Vec q.length) : AdjoinRoot (polyOf q) := AdjoinRoot.mk (polyOf q) (polyV x)

theorem toK_injective : Function.Injective (toK q) := by
  intro x y h
  rw [toK, toK, AdjoinRoot.mk_eq_mk, ← polyV_sub] at h
  rw [← sub_eq_zero, ← polyV_eq_zero_iff]
  exact eq_zero_of_polyOf_dvd (degree_polyV_lt _) h

theorem mk_polyV_w (α : Vec ℓ) (x : Vec q.length) :
    AdjoinRoot.mk (polyOf q) (polyV (wvec q α x)) = aeval (toK q x) (polyV α) := by
  rw [wvec, polyV_sum]
  simp only [polyV_vecOf (length_powMod _ _ _), map_sum, map_mul, mk_powMod, ofList_ofFn]
  simp only [polyV, map_sum, map_mul, aeval_C, aeval_X_pow, AdjoinRoot.mk_C,
    AdjoinRoot.algebraMap_eq, toK]

theorem wvec_eq_zero_iff (α : Vec ℓ) (x : Vec q.length) :
    wvec q α x = 0 ↔ aeval (toK q x) (polyV α) = 0 := by
  rw [← mk_polyV_w, AdjoinRoot.mk_eq_zero, ← polyV_eq_zero_iff]
  exact ⟨fun h => h ▸ dvd_zero _, eq_zero_of_polyOf_dvd (degree_polyV_lt _)⟩

/-- The character sum over `E`: `Σ_{x,y} (−1)^⟨ρ(x,y), α⟩ = 2^μ · #{x : p_α(x) = 0}`. -/
theorem sum_chi_rho (α : Vec ℓ) :
    ∑ xy : Vec q.length × Vec q.length, chi (rho q ℓ xy.1 xy.2) α =
      2 ^ q.length * (Finset.univ.filter fun x => aeval (toK q x) (polyV α) = 0).card := by
  rw [Fintype.sum_prod_type]
  have : ∀ x : Vec q.length, ∑ y, chi (rho q ℓ x y) α =
      if aeval (toK q x) (polyV α) = 0 then 2 ^ q.length else 0 := by
    intro x
    have h := sum_chi_eq (wvec q α x)
    simp only [chi] at h
    simp only [chi, rho_dot]
    rw [h]
    exact if_congr (wvec_eq_zero_iff q α x) rfl rfl
  simp only [this]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- "the at most ℓ−1 roots x of p_α": `p_α` is nonzero of degree `≤ ℓ − 1`. -/
theorem card_roots_le (hq : Irreducible (polyOf q)) {α : Vec ℓ} (hα : α ≠ 0) :
    (Finset.univ.filter fun x => aeval (toK q x) (polyV α) = 0).card ≤ ℓ - 1 := by
  have : Fact (Irreducible (polyOf q)) := ⟨hq⟩
  have hp : polyV α ≠ 0 := by rwa [Ne, polyV_eq_zero_iff]
  have hdeg : (polyV α).natDegree ≤ ℓ - 1 := by
    have := (natDegree_lt_iff_degree_lt hp).mpr (degree_polyV_lt α)
    omega
  set f := (polyV α).map (algebraMap (ZMod 2) (AdjoinRoot (polyOf q)))
  have hf : f ≠ 0 := Polynomial.map_ne_zero hp
  calc (Finset.univ.filter fun x => aeval (toK q x) (polyV α) = 0).card
      = ((Finset.univ.filter fun x => aeval (toK q x) (polyV α) = 0).image (toK q)).card :=
        (Finset.card_image_of_injective _ (toK_injective q)).symm
    _ ≤ f.roots.toFinset.card := by
        refine Finset.card_le_card fun z hz => ?_
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
        rw [Finset.mem_filter] at hx
        rw [Multiset.mem_toFinset, mem_roots hf, IsRoot.def, eval_map, ← aeval_def]
        exact hx.2
    _ ≤ f.roots.card := Multiset.toFinset_card_le _
    _ ≤ f.natDegree := card_roots' f
    _ = (polyV α).natDegree := natDegree_map _
    _ ≤ ℓ - 1 := hdeg

/-- **Lemma 6**, the bias: "Hence the bias is at most (ℓ−1)2^μ/4^μ", for `μ = q.length` and an
irreducible `polyOf q`. -/
theorem isBiased_biasedSet (hq : Irreducible (polyOf q)) (ℓ : ℕ) :
    IsBiased (((ℓ : ℝ) - 1) / 2 ^ q.length) (biasedSet q ℓ) := by
  refine ⟨?_, fun v hv => ?_⟩
  · rw [← Multiset.card_pos, card_biasedSet]; positivity
  have hℓ : 1 ≤ ℓ := by
    rcases Nat.eq_zero_or_pos ℓ with rfl | h
    · exact absurd (Subsingleton.elim v 0) hv
    · exact h
  have hsum : ((biasedSet q ℓ).map fun u => (chi u v : ℝ)).sum =
      ((∑ xy : Vec q.length × Vec q.length, chi (rho q ℓ xy.1 xy.2) v : ℤ) : ℝ) := by
    rw [biasedSet, Multiset.map_map, Int.cast_sum]
    rfl
  have hN := card_roots_le q hq hv
  set N := (Finset.univ.filter fun x => aeval (toK q x) (polyV v) = 0).card
  have hNr : (N : ℝ) ≤ (ℓ : ℝ) - 1 := by
    have : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by rw [Nat.cast_sub hℓ]; simp
    rw [← this]; exact_mod_cast hN
  rw [hsum, sum_chi_rho, card_biasedSet]
  push_cast
  rw [abs_of_nonneg (by positivity)]
  have h4 : (4 : ℝ) ^ q.length = 2 ^ q.length * 2 ^ q.length := by rw [← mul_pow]; norm_num
  rw [h4, div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_right₀ _ (by positivity), mul_comm]
  exact mul_le_mul_of_nonneg_right hNr (by positivity)

end Bias

/-- A larger bound: an `ε`-biased multiset is `ε'`-biased for `ε ≤ ε'`. -/
theorem IsBiased.mono {ℓ : ℕ} {ε ε' : ℝ} {E : Multiset (Vec ℓ)} (h : IsBiased ε E) (hε : ε ≤ ε') :
    IsBiased ε' E :=
  ⟨h.1, fun v hv => (h.2 v hv).trans (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))⟩

/-- **Lemma 6**: "(ℓ−1)2^μ/4^μ < ℓ/2^μ ≤ 1/r", for any `μ = q.length` with `ℓr ≤ 2^μ`. -/
theorem isBiased_biasedSet_inv {q : List (ZMod 2)} (hq : Irreducible (polyOf q)) {ℓ r : ℕ}
    (hr : 0 < r) (h : ℓ * r ≤ 2 ^ q.length) : IsBiased (1 / (r : ℝ)) (biasedSet q ℓ) := by
  refine (isBiased_biasedSet q hq ℓ).mono ?_
  rw [div_le_div_iff₀ (by positivity) (by exact_mod_cast hr), one_mul]
  have : ((ℓ * r : ℕ) : ℝ) ≤ ((2 ^ q.length : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at this
  nlinarith [(Nat.cast_pos.mpr hr : (0 : ℝ) < r)]

/-- **Lemma 6**: "Let ℓ, r ≥ 1 with ℓr ≥ 2, and let μ := ⌈log(ℓr)⌉ ≥ 1. There is a multiset
E_{ℓ,r} ⊆ F^ℓ of 4^μ < 4(ℓr)² vectors that is (1/r)-biased": for every irreducible `polyOf q` of
degree `μ` (the polynomial that the search finds, `remark_23_lemma_6_exists`), `biasedSet q ℓ`. -/
theorem remark_23_lemma_6 {ℓ r : ℕ} (hℓr : 2 ≤ ℓ * r) {q : List (ZMod 2)}
    (hlen : q.length = Nat.clog 2 (ℓ * r)) (hq : Irreducible (polyOf q)) :
    IsBiased (1 / (r : ℝ)) (biasedSet q ℓ) ∧ (biasedSet q ℓ).card = 4 ^ q.length ∧
      4 ^ q.length < 4 * (ℓ * r) ^ 2 := by
  have hr : 0 < r := Nat.pos_of_ne_zero (by rintro rfl; simp at hℓr)
  refine ⟨isBiased_biasedSet_inv hq hr (hlen ▸ Nat.le_pow_clog (by norm_num) _),
    card_biasedSet q ℓ, ?_⟩
  have hpos : 0 < Nat.clog 2 (ℓ * r) := Nat.clog_pos (by norm_num) (by omega)
  have hlt := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := ℓ * r) (by omega)
  have h2 : 2 ^ q.length < 2 * (ℓ * r) := by
    rw [hlen, ← Nat.succ_pred_eq_of_pos hpos, pow_succ]; omega
  calc 4 ^ q.length = (2 ^ q.length) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ < (2 * (ℓ * r)) ^ 2 := Nat.pow_lt_pow_left h2 (by norm_num)
    _ = 4 * (ℓ * r) ^ 2 := by ring

/-- **Lemma 6**, the search succeeds: for `ℓr ≥ 2` an irreducible `polyOf q` of degree
`μ = ⌈log₂(ℓr)⌉` exists. -/
theorem remark_23_lemma_6_exists {ℓ r : ℕ} (hℓr : 2 ≤ ℓ * r) :
    ∃ q : List (ZMod 2), q.length = Nat.clog 2 (ℓ * r) ∧ Irreducible (polyOf q) :=
  exists_irreducible_polyOf _ (Nat.clog_pos (by norm_num) (by omega))

/-! ### The two uses -/

/-- Theorem 8: `r := ⌊log √D⌋ ≥ 2` for `D ≥ 16`. -/
theorem two_le_log_sqrt {D : ℕ} (hD : 16 ≤ D) : 2 ≤ Nat.log 2 (Nat.sqrt D) := by
  have h4 : 4 ≤ Nat.sqrt D := Nat.le_sqrt.mpr (by omega)
  calc 2 = Nat.log 2 (2 ^ 2) := (Nat.log_pow (by norm_num) 2).symm
    _ ≤ Nat.log 2 (Nat.sqrt D) := Nat.log_mono_right (by norm_num; omega)

/-- Theorem 8: "the (1/r)-biased multiset E := E_{d′,r} of Lemma 6", `r = ⌊log √D⌋`, weights in
`F^{d′}`, `d′ ≥ 1`.  This is the hypothesis `IsBiased (1 / rows.length) E` of
`Remark_23_theorem_8_false_positives` with `rows.length = Nat.log 2 (Nat.sqrt D)`. -/
theorem isBiased_theorem_8 {d D : ℕ} (hd : 1 ≤ d) (hD : 16 ≤ D) {q : List (ZMod 2)}
    (hlen : q.length = Nat.clog 2 (d * Nat.log 2 (Nat.sqrt D))) (hq : Irreducible (polyOf q)) :
    IsBiased (1 / (Nat.log 2 (Nat.sqrt D) : ℝ)) (biasedSet q d) :=
  (remark_23_lemma_6 (by nlinarith [two_le_log_sqrt hD]) hlen hq).1

/-- Theorem 8: the polynomial for `E_{d′,r}` exists. -/
theorem exists_theorem_8 {d D : ℕ} (hd : 1 ≤ d) (hD : 16 ≤ D) :
    ∃ q : List (ZMod 2), q.length = Nat.clog 2 (d * Nat.log 2 (Nat.sqrt D)) ∧
      Irreducible (polyOf q) :=
  remark_23_lemma_6_exists (by nlinarith [two_le_log_sqrt hD])

/-- §7: `k = kOf n ≥ 4`. -/
theorem four_le_kOf (n : ℕ) : 4 ≤ kOf n := by
  unfold kOf; omega

/-- §7: "E := E_{d,k}, the (1/k)-biased multiset of Lemma 6", `k = kOf n`, vectors of `F^d`,
`d ≥ 1`.  This is the hypothesis `IsBiased (1 / (kOf n : ℝ)) E` of `Remark_23_lemma_12` and
`Remark_23_lemma_13_goodStep`. -/
theorem isBiased_sec7 {d : ℕ} (n : ℕ) (hd : 1 ≤ d) {q : List (ZMod 2)}
    (hlen : q.length = Nat.clog 2 (d * kOf n)) (hq : Irreducible (polyOf q)) :
    IsBiased (1 / (kOf n : ℝ)) (biasedSet q d) :=
  (remark_23_lemma_6 (by nlinarith [four_le_kOf n]) hlen hq).1

/-- §7: the polynomial for `E_{d,k}` exists. -/
theorem exists_sec7 {d : ℕ} (n : ℕ) (hd : 1 ≤ d) :
    ∃ q : List (ZMod 2), q.length = Nat.clog 2 (d * kOf n) ∧ Irreducible (polyOf q) :=
  remark_23_lemma_6_exists (by nlinarith [four_le_kOf n])

end ThreeSumApsp.Remark23

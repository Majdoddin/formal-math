/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Remark 23 (3XOR): polynomials over F₂ as coefficient lists

The note's Lemma 6 works in `GF(2^μ) = F[t]/(p)` for an irreducible polynomial `p` of degree `μ`,
found "by testing each of the 2^μ monic polynomials of degree μ for divisibility by each polynomial
of degree between 1 and μ/2".  This file supplies the arithmetic of that proof on coefficient lists
(bit rows), so that a program can compute it cell by cell, and its bridge to `Polynomial (ZMod 2)`.

Conventions.

* A coefficient list `l : List (ZMod 2)` is little-endian: `l[j]` is the coefficient of `t^j`.
  `ofList l` is the polynomial; `coeff_ofList`: its coefficient `j` is `l.getD j 0`.
* A monic polynomial of degree `μ` is given by its `μ` low coefficients `q`, the leading `1` being
  implicit: `polyOf q = t^μ + ofList q` with `μ = q.length` (`monic_polyOf`, `natDegree_polyOf`).
  Every monic polynomial is of this form (`polyOf_lowCoeffs`).
* An element of `F[t]/(polyOf q)` is a list of length `μ` (a polynomial of degree `< μ`).  The
  routines: `mulXMod q r` (multiplication by `t`, one conditional addition of `q`), `mulMod q x y`
  (Horner's rule over the coefficients of `y`), `powMod q x i` (`i` multiplications by `x`, starting
  from `oneL q`), `modL q a` (the remainder of an arbitrary list `a`).  Their specifications
  (`mk_mulXMod`, `mk_mulMod`, `mk_powMod`, `mk_modL`) are equalities in `AdjoinRoot (polyOf q)`, with
  the lengths (`length_mulXMod`, ...).

Main results.

* `dvd_iff_modL`: `polyOf q ∣ ofList a` iff `modL q a` is all zeros.
* `irreducible_polyOf_iff`: for `μ ≥ 1`, `polyOf q` is irreducible iff for every monic divisor
  candidate `polyOf d` of degree `1 ≤ d.length ≤ μ/2` the remainder `modL d (q ++ [1])` has a
  nonzero cell.  (`q ++ [1]` is the full coefficient list of `polyOf q`, `ofList_append_one`.)
* `exists_irreducible_polyOf`: an irreducible `polyOf q` with `q.length = μ` exists for each
  `μ ≥ 1` (the minimal polynomial of a primitive element of `GaloisField 2 μ`).
-/

@[expose] public section

namespace ThreeSumApsp.Remark23

open Polynomial

theorem getD_zero_of_lt {l : List (ZMod 2)} {j : ℕ} (h : j < l.length) : l.getD j 0 = l[j] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_zero_of_ge {l : List (ZMod 2)} {j : ℕ} (h : l.length ≤ j) : l.getD j 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ### Coefficient lists -/

/-- The polynomial with the coefficient list `l`, little-endian: `l = [a₀, a₁, …]` is
`a₀ + a₁ t + ⋯`. -/
noncomputable def ofList : List (ZMod 2) → (ZMod 2)[X]
  | [] => 0
  | a :: l => C a + X * ofList l

@[simp] theorem ofList_nil : ofList [] = 0 := rfl

@[simp] theorem ofList_cons (a : ZMod 2) (l : List (ZMod 2)) :
    ofList (a :: l) = C a + X * ofList l := rfl

theorem coeff_ofList (l : List (ZMod 2)) (j : ℕ) : (ofList l).coeff j = l.getD j 0 := by
  induction l generalizing j with
  | nil => simp
  | cons a l ih =>
    cases j with
    | zero => simp
    | succ j => simp [coeff_X_mul, ih, coeff_C_succ]

theorem degree_ofList_lt (l : List (ZMod 2)) : (ofList l).degree < l.length := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_ofList, getD_zero_of_ge hm]

theorem ofList_append (a b : List (ZMod 2)) :
    ofList (a ++ b) = ofList a + X ^ a.length * ofList b := by
  induction a with
  | nil => simp
  | cons x a ih => simp only [List.cons_append, ofList_cons, ih, List.length_cons]; ring

theorem ofList_replicate_zero (n : ℕ) : ofList (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem ofList_map_mul (c : ZMod 2) (l : List (ZMod 2)) :
    ofList (l.map (c * ·)) = C c * ofList l := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, ofList_cons, ih, C_mul]; ring

/-- Cell-wise addition (XOR) of two coefficient lists of the same length. -/
def vaddL (a b : List (ZMod 2)) : List (ZMod 2) := List.zipWith (· + ·) a b

theorem length_vaddL {a b : List (ZMod 2)} (h : a.length = b.length) :
    (vaddL a b).length = a.length := by
  simp [vaddL, h]

theorem ofList_vaddL {a b : List (ZMod 2)} (h : a.length = b.length) :
    ofList (vaddL a b) = ofList a + ofList b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [vaddL]
  | cons x a ih =>
    cases b with
    | nil => simp at h
    | cons y b =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have := ih h
      simp only [vaddL, List.zipWith_cons_cons, ofList_cons] at this ⊢
      rw [this, C_add]; ring

theorem eq_of_ofList_eq {a b : List (ZMod 2)} (hl : a.length = b.length)
    (h : ofList a = ofList b) : a = b := by
  apply List.ext_getElem hl
  intro j h1 h2
  have := congrArg (fun f => f.coeff j) h
  simp only [coeff_ofList] at this
  rwa [getD_zero_of_lt h1, getD_zero_of_lt h2] at this

theorem ofList_eq_zero_iff (l : List (ZMod 2)) : ofList l = 0 ↔ ∀ c ∈ l, c = 0 := by
  constructor
  · intro h c hc
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc
    have := congrArg (fun f => f.coeff j) h
    simp only [coeff_ofList, coeff_zero] at this
    rwa [getD_zero_of_lt hj] at this
  · intro h
    ext j
    rw [coeff_ofList, coeff_zero]
    rcases lt_or_ge j l.length with hj | hj
    · rw [getD_zero_of_lt hj]; exact h _ (List.getElem_mem hj)
    · rw [getD_zero_of_ge hj]

/-! ### Monic polynomials by their low coefficients -/

/-- The monic polynomial `t^μ + ofList q` of degree `μ = q.length`; `q` holds its low
coefficients. -/
noncomputable def polyOf (q : List (ZMod 2)) : (ZMod 2)[X] := X ^ q.length + ofList q

theorem degree_ofList_lt_degree_X_pow (q : List (ZMod 2)) :
    (ofList q).degree < (X ^ q.length : (ZMod 2)[X]).degree := by
  rw [degree_X_pow]; exact degree_ofList_lt q

theorem monic_polyOf (q : List (ZMod 2)) : (polyOf q).Monic :=
  (monic_X_pow _).add_of_left (degree_ofList_lt_degree_X_pow q)

theorem natDegree_polyOf (q : List (ZMod 2)) : (polyOf q).natDegree = q.length := by
  rw [polyOf, natDegree_add_eq_left_of_degree_lt (degree_ofList_lt_degree_X_pow q),
    natDegree_X_pow]

theorem polyOf_ne_zero (q : List (ZMod 2)) : polyOf q ≠ 0 := (monic_polyOf q).ne_zero

/-- The full coefficient list of `polyOf q` is `q ++ [1]`. -/
theorem ofList_append_one (q : List (ZMod 2)) : ofList (q ++ [1]) = polyOf q := by
  rw [ofList_append, polyOf]; simp; ring

/-- The `natDegree` low coefficients of a polynomial. -/
noncomputable def lowCoeffs (g : (ZMod 2)[X]) : List (ZMod 2) :=
  (List.range g.natDegree).map g.coeff

theorem length_lowCoeffs (g : (ZMod 2)[X]) : (lowCoeffs g).length = g.natDegree := by
  simp [lowCoeffs]

/-- Every monic polynomial is `polyOf` of its low coefficients. -/
theorem polyOf_lowCoeffs {g : (ZMod 2)[X]} (hg : g.Monic) : polyOf (lowCoeffs g) = g := by
  ext j
  rw [polyOf, coeff_add, coeff_X_pow, coeff_ofList, length_lowCoeffs]
  rcases lt_trichotomy j g.natDegree with hj | rfl | hj
  · rw [if_neg hj.ne, getD_zero_of_lt (by simpa [length_lowCoeffs] using hj)]
    simp [lowCoeffs]
  · rw [if_pos rfl, getD_zero_of_ge (by simp [length_lowCoeffs])]
    have := hg.coeff_natDegree
    rw [this]; simp
  · rw [if_neg hj.ne', getD_zero_of_ge (by simp [length_lowCoeffs]; omega),
      coeff_eq_zero_of_natDegree_lt hj]
    simp

/-- A polynomial of degree `< μ` that the monic `polyOf q` (of degree `μ`) divides is zero. -/
theorem eq_zero_of_polyOf_dvd {q : List (ZMod 2)} {f : (ZMod 2)[X]}
    (hf : f.degree < q.length) (h : polyOf q ∣ f) : f = 0 := by
  refine eq_zero_of_dvd_of_degree_lt h ?_
  rwa [degree_eq_natDegree (polyOf_ne_zero q), natDegree_polyOf]

/-- Two coefficient lists of length `μ = q.length` with the same class modulo `polyOf q` are
equal. -/
theorem eq_of_mk_eq {q a b : List (ZMod 2)} (ha : a.length = q.length) (hb : b.length = q.length)
    (h : AdjoinRoot.mk (polyOf q) (ofList a) = AdjoinRoot.mk (polyOf q) (ofList b)) : a = b := by
  rw [AdjoinRoot.mk_eq_mk] at h
  refine eq_of_ofList_eq (ha.trans hb.symm) (sub_eq_zero.mp (eq_zero_of_polyOf_dvd ?_ h))
  refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
  · simpa [ha] using degree_ofList_lt a
  · simpa [hb] using degree_ofList_lt b

/-! ### Arithmetic modulo `polyOf q` on lists of length `μ` -/

theorem two_eq_zero_poly : (2 : (ZMod 2)[X]) = 0 := by
  simpa using CharP.cast_eq_zero (ZMod 2)[X] 2

/-- Multiplication by `t` modulo `polyOf q`, on a list `r` of length `μ`: shift up by one cell and,
if the cell shifted out (the top coefficient `r[μ−1]`) is `1`, add `q` cell-wise. -/
def mulXMod (q r : List (ZMod 2)) : List (ZMod 2) :=
  List.zipWith (fun a b => a + r.getLastD 0 * b) (0 :: r.dropLast) q

theorem length_mulXMod {q r : List (ZMod 2)} (h : r.length = q.length) :
    (mulXMod q r).length = q.length := by
  rcases r.eq_nil_or_concat with rfl | ⟨r', t, rfl⟩
  · simp [mulXMod, ← h]
  rw [List.concat_eq_append] at h ⊢
  · simp [mulXMod] at h ⊢; omega

theorem ofList_mulXMod {q r : List (ZMod 2)} (h : r.length = q.length) :
    ofList (mulXMod q r) + C (r.getLastD 0) * polyOf q = X * ofList r := by
  rcases r.eq_nil_or_concat with rfl | ⟨r', t, rfl⟩
  · simp only [List.length_nil] at h
    rw [List.length_eq_zero_iff.mp h.symm]
    simp [mulXMod]
  rw [List.concat_eq_append] at h ⊢
  · have hz : List.zipWith (fun a b => a + (r' ++ [t]).getLastD 0 * b) (0 :: r') q =
        vaddL (0 :: r') (q.map (t * ·)) := by
      simp only [List.getLastD_eq_getLast?, List.getLast?_concat, Option.getD_some, vaddL]
      rw [List.zipWith_map_right]
    have hl : (0 :: r').length = (q.map (t * ·)).length := by simp at h ⊢; omega
    simp only [mulXMod, List.dropLast_concat]
    rw [hz, ofList_vaddL hl, ofList_map_mul, ofList_append, polyOf]
    simp only [List.getLastD_eq_getLast?, List.getLast?_concat, Option.getD_some, ofList_cons,
      ofList_nil, map_zero, zero_add, mul_zero, add_zero]
    simp only [List.length_append, List.length_cons, List.length_nil] at h
    rw [← h]
    linear_combination (C t * ofList q) * two_eq_zero_poly

theorem mk_mulXMod {q r : List (ZMod 2)} (h : r.length = q.length) :
    AdjoinRoot.mk (polyOf q) (ofList (mulXMod q r)) = AdjoinRoot.mk (polyOf q) (X * ofList r) := by
  rw [← ofList_mulXMod h, map_add, map_mul, AdjoinRoot.mk_self, mul_zero, add_zero]

/-- The list `1` of length `μ` (empty if `μ = 0`). -/
def oneL (q : List (ZMod 2)) : List (ZMod 2) :=
  match q.length with
  | 0 => []
  | n + 1 => 1 :: List.replicate n 0

theorem length_oneL (q : List (ZMod 2)) : (oneL q).length = q.length := by
  unfold oneL; split <;> simp_all

theorem mk_oneL (q : List (ZMod 2)) : AdjoinRoot.mk (polyOf q) (ofList (oneL q)) = 1 := by
  unfold oneL
  split
  · rename_i h
    rw [← map_one (AdjoinRoot.mk (polyOf q)), AdjoinRoot.mk_eq_mk]
    rw [polyOf, h, List.length_eq_zero_iff.mp h]
    simp
  · simp [ofList_replicate_zero]

/-- The product `x · y` modulo `polyOf q`, for `x` of length `μ`, by Horner's rule over the
coefficients of `y` from the top: `acc ← t · acc + y_j x`. -/
def mulMod (q x y : List (ZMod 2)) : List (ZMod 2) :=
  y.foldr (fun c acc => vaddL (mulXMod q acc) (x.map (c * ·))) (List.replicate q.length 0)

theorem length_mulMod {q x : List (ZMod 2)} (hx : x.length = q.length) (y : List (ZMod 2)) :
    (mulMod q x y).length = q.length := by
  induction y with
  | nil => simp [mulMod]
  | cons c y ih =>
    simp only [mulMod, List.foldr_cons] at ih ⊢
    rw [length_vaddL (by rw [length_mulXMod ih]; simp [hx]), length_mulXMod ih]

theorem mk_mulMod {q x : List (ZMod 2)} (hx : x.length = q.length) (y : List (ZMod 2)) :
    AdjoinRoot.mk (polyOf q) (ofList (mulMod q x y)) =
      AdjoinRoot.mk (polyOf q) (ofList x) * AdjoinRoot.mk (polyOf q) (ofList y) := by
  induction y with
  | nil => simp [mulMod, ofList_replicate_zero]
  | cons c y ih =>
    have hl := length_mulMod hx y
    simp only [mulMod, List.foldr_cons] at ih hl ⊢
    rw [ofList_vaddL (by rw [length_mulXMod hl]; simp [hx]), map_add, mk_mulXMod hl,
      ofList_map_mul, map_mul, map_mul, ih, ofList_cons]
    simp only [map_add, map_mul]
    ring

/-- `x^i` modulo `polyOf q`: `i` multiplications by `x`, starting from `oneL q`. -/
def powMod (q x : List (ZMod 2)) : ℕ → List (ZMod 2)
  | 0 => oneL q
  | i + 1 => mulMod q (powMod q x i) x

theorem length_powMod (q x : List (ZMod 2)) (i : ℕ) : (powMod q x i).length = q.length := by
  cases i with
  | zero => exact length_oneL q
  | succ i => exact length_mulMod (length_powMod q x i) x

theorem mk_powMod (q x : List (ZMod 2)) (i : ℕ) :
    AdjoinRoot.mk (polyOf q) (ofList (powMod q x i)) = AdjoinRoot.mk (polyOf q) (ofList x) ^ i := by
  induction i with
  | zero => exact mk_oneL q
  | succ i ih => rw [powMod, mk_mulMod (length_powMod q x i), ih, pow_succ]

/-- The remainder of an arbitrary coefficient list `a` modulo `polyOf q`, as a list of length
`μ`: `1 · a` by `mulMod`. -/
def modL (q a : List (ZMod 2)) : List (ZMod 2) := mulMod q (oneL q) a

theorem length_modL (q a : List (ZMod 2)) : (modL q a).length = q.length :=
  length_mulMod (length_oneL q) a

theorem mk_modL (q a : List (ZMod 2)) :
    AdjoinRoot.mk (polyOf q) (ofList (modL q a)) = AdjoinRoot.mk (polyOf q) (ofList a) := by
  rw [modL, mk_mulMod (length_oneL q), mk_oneL, one_mul]

/-- The remainder is that of polynomial division. -/
theorem ofList_modL (q a : List (ZMod 2)) : ofList (modL q a) = ofList a %ₘ polyOf q := by
  have hd : (ofList (modL q a)).degree < (polyOf q).degree := by
    rw [degree_eq_natDegree (polyOf_ne_zero q), natDegree_polyOf]
    simpa [length_modL] using degree_ofList_lt (modL q a)
  have h := mk_modL q a
  rw [AdjoinRoot.mk_eq_mk] at h
  obtain ⟨g, hg⟩ := h
  exact ((div_modByMonic_unique (-g) _ (monic_polyOf q)
    ⟨by linear_combination hg, hd⟩).2).symm

/-- **Trial division by one candidate**: `polyOf q ∣ ofList a` iff the remainder `modL q a` is all
zeros. -/
theorem dvd_iff_modL (q a : List (ZMod 2)) : polyOf q ∣ ofList a ↔ ∀ c ∈ modL q a, c = 0 := by
  rw [← ofList_eq_zero_iff, ofList_modL, modByMonic_eq_zero_iff_dvd (monic_polyOf q)]

/-! ### Irreducibility by trial division, and existence -/

/-- **Lemma 6**, "testing each of the 2^μ monic polynomials of degree μ for divisibility by each
polynomial of degree between 1 and μ/2": for `μ = q.length ≥ 1`, `polyOf q` is irreducible iff no
monic `polyOf d` with `1 ≤ d.length ≤ μ/2` divides it, that is, iff each remainder
`modL d (q ++ [1])` has a nonzero cell. -/
theorem irreducible_polyOf_iff (q : List (ZMod 2)) (hq : 1 ≤ q.length) :
    Irreducible (polyOf q) ↔
      ∀ d : List (ZMod 2), 1 ≤ d.length → d.length ≤ q.length / 2 →
        ∃ c ∈ modL d (q ++ [1]), c ≠ 0 := by
  have hu : ¬ IsUnit (polyOf q) := by
    intro h
    have := natDegree_eq_zero_of_isUnit h
    rw [natDegree_polyOf] at this; omega
  rw [irreducible_iff_lt_natDegree_lt (polyOf_ne_zero q) hu, natDegree_polyOf]
  constructor
  · intro H d h1 h2
    have := H (polyOf d) (monic_polyOf d) (by rw [natDegree_polyOf]; simp; omega)
    rw [← ofList_append_one q, dvd_iff_modL] at this
    push Not at this
    exact this
  · intro H g hg hdeg hdvd
    rw [Finset.mem_Ioc] at hdeg
    obtain ⟨c, hc, hc0⟩ := H (lowCoeffs g) (by rw [length_lowCoeffs]; omega)
      (by rw [length_lowCoeffs]; omega)
    rw [← polyOf_lowCoeffs hg, ← ofList_append_one q, dvd_iff_modL] at hdvd
    exact hc0 (hdvd c hc)

/-- **Lemma 6**, existence of the polynomial that the search finds: for every `μ ≥ 1` there is an
irreducible monic polynomial `polyOf q` of degree `μ = q.length` over F₂. -/
theorem exists_irreducible_polyOf (μ : ℕ) (hμ : 1 ≤ μ) :
    ∃ q : List (ZMod 2), q.length = μ ∧ Irreducible (polyOf q) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ZMod 2) (GaloisField 2 μ)
  have hint : IsIntegral (ZMod 2) α := IsIntegral.of_finite (ZMod 2) α
  have hdeg := (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod 2) α).mp hα
  rw [GaloisField.finrank 2 (by omega : μ ≠ 0)] at hdeg
  refine ⟨lowCoeffs (minpoly (ZMod 2) α), by rw [length_lowCoeffs, hdeg], ?_⟩
  rw [polyOf_lowCoeffs (minpoly.monic hint)]
  exact minpoly.irreducible hint

end ThreeSumApsp.Remark23

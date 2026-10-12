/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.TimeClaims.Sec3.Definitions

/-!
# Running-time claims of Remark 23 (3XOR), for an abstract notion of "solved in time T"

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

The note proves Remark 23 by the route of 3SUM: Exact-XOR-Triangle reduces to Lop (its Theorem 8,
the analogue of Theorem 17), so Exact-XOR-Triangle is solved in `O(N^{3−ε'})` time (its Theorem 9);
Convolution-3XOR reduces to Exact-XOR-Triangle (its Lemma 10 and Corollary 11); and 3XOR reduces
to Convolution-3XOR by the recursion of its Section 7.  The deductions between the running times are
those of `TimeClaims/Sec3/`, read for a second `DetTimeModel` whose fields `exactTriangle`,
`convolution3SUM` and `threeSum` are the three XOR problems.

## What the three fields mean for 3XOR

For the deductions of this folder the fields are bare predicates.  The interpretation for programs
(`xorModel`) reads them as follows, and the claims below are stated with this reading in mind.

* `M.exactTriangle T`: Exact-XOR-Triangle on `n` vertices per part, the weights being vectors of
  `F₂^{d'}` given as naturals at most `u` (so `d' ≤ log₂ u + 1`), in time `T n u`.
* `M.convolution3SUM T`: Convolution-3XOR (the note's Definition 1, three arrays with empty entries
  `⊥`) of size `N` (the length of each array), its non-empty entries naturals at most `u`, in time
  `T N u`.
* `M.threeSum T`: 3XOR on three lists of `n` vectors given as naturals at most `u`, in time `T n u`.

## Which claim shapes of the 3SUM route fit

* `Claim.CH20_Theorem_5_1` fits the note's Section 7 as it stands: the extra time is `O(n polylog n)`
  for each fixed `κ` (Lemma 15 times Lemma 13, plus removing repeated vectors and listing the
  ε-biased set), within `Õ(n^{3/2})`; the number of calls is `27 · 6 (log n)^{log₂ 27}`, which is
  polylogarithmic (`IsPowPolylog Num 0`; the factor 27 is a constant); all calls have the same size
  `N n = m = 2^k < 64n` (`IsPowPolylog N 1`); their entries are list elements, at most `n^κ`
  (`mag n = n^κ`, `κ' = κ`).  The claim lets everything depend on `κ`, so the factors `d ≤ κ log₂ n
  + 1` of the bit-by-bit vector operations are free.
* `Claim.VW13_Theorem_4_3` fits Lemma 10 with Corollary 11 as it stands: an array of size `N = 2^k`
  gives `2^{⌈k/2⌉} ≤ √(2N)` instances on `2^{⌈k/2⌉}` vertices per part (`O(√N)` both), whose weights
  `8v + flag` are at most `8u + 7 ≤ 15u` (`c = 15`), written in `O(N^{3/2})` time.
* `Claim.Theorem_17` does not fit Theorem 8.  Its additional time has the term `n^{ω+o(1)} D^{3/2}`
  for the choice of the prime, with a constant independent of `κ`.  The choice of the rows of the
  hash `h` costs, on a machine without bit operations, a polynomial in `d' ≤ κ log₂ n + 1` times
  `√D · MM(n)` (see `XorClaim.termSelect`), which no `κ`-free constant bounds.  So Theorem 8 has its
  own claim, `XorClaim.Theorem_8`, and the deduction to Theorem 9 and to the uniform bound is redone
  with a power `κ^p` (`TimeClaims/Remark23/Theorem9.lean`).
-/

@[expose] public section

namespace ThreeSumApsp

/-- **Theorem 8**, the term of the additional time for choosing the rows of the hash
`h : F₂^{d'} → F₂^r`, `2^r ∈ (√D/2, √D]`: "(d' log D)² √D M(N)" in the note, made generous:
`(κ log n)^p √D MM(n)`.

The cost of the selection on the light machine, where an inner product of two vectors of `d'` bits
costs `O(d')`, is about
`|E| · (N² d' + r · 2^{r+1} (MM(N) + N² r)) + |E| d' μ²`, with `|E| = 4^μ < 4 (d' r)²`,
`μ = ⌈log₂ (d' r)⌉`, `r ≤ log D ≤ log n` and `d' ≤ κ log₂ n + 1 ≤ 2 κ log n` (for `n ≥ 16`):
the bits `⟨u, w(e)⟩` for all candidates `u ∈ E` and all `3N²` edges, the `r |E|` counts of the note's
Lemma 7 (`2^q` products of `±1` matrices each), and the listing of `E` (the note's Lemma 6).  With
`MM(n) ≥ n² log n` the first two are at most a constant times `(κ log n)^6 √D MM(n)` and
`(κ log n)^5 √D MM(n)`, and the listing, with `μ² ≤ 4 d' r`, at most a constant times
`(κ log n)^8`; so `p = 8` covers all three.  The cubic power of `d'` in the first is why the
`κ²` of the note (`(d' log D)²`) is not enough here.  The exponent `p` is a parameter of
`XorClaim.Theorem_8`: the host that proves the claim chooses it, and every deduction below holds for
every `p ≥ 1`.  A power of `κ`
is harmless at the end, because Theorem 21(a) only uses bounds `u = n^{O(1)}` on the weights, where
`κ^p` is a constant. -/
noncomputable def XorClaim.termSelect (MM : ℕ → ℝ) (n D : ℕ) (κ : ℝ) (p : ℕ) : ℝ :=
  (κ * Real.log n) ^ p * Real.sqrt D * MM n

namespace XorClaim

/-- **Theorem 8** of the note, as a transfer claim: "Let 16 ≤ D ≤ N, let 1 ≤ g ≤ √D be an integer,
and let c' > 0 be a constant.  Exact-XOR-Triangle on N vertices per part with weights in F₂^{d'},
d' ≤ c' log N, reduces deterministically to at most 4Ng instances of Lop(N, D), each with at most
N²/√D query pairs, plus O(N³/g + N²Dg + (d' log D)² √D M(N)) additional time."

The shape is that of `Claim.Theorem_17`, with two changes.

* The weights are naturals at most `u ≤ n^κ`, so `d' ≤ κ log₂ n + 1`; on the light machine a XOR
  test costs `O(d')`, so the scans cost `O(κ n³ log n / g)`, the term `termScans` of Theorem 17
  (the note's `N³/g` is for a word RAM with bitwise operations).  Computing the labels `h(w(e))` of
  all edges, `O(n² r d')`, also fits this term.
* The term `termPrime` for the choice of the prime is replaced by `termSelect MM n D κ p` for the
  choice of the rows of `h`.

`C` does not depend on `κ`; the dependence on `κ` is explicit in the terms.  The term
`C n²/√D` next to `T` is the reading of the oracle's answers, as in Theorem 17. -/
def Theorem_8 (M : DetTimeModel) (MM : ℕ → ℝ) (D g : ℕ → ℕ) (p : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ → ℕ → ℕ → ℝ, M.lopDetect T →
    ∃ T' : ℕ → ℝ → ℝ, M.exactTriangle T' ∧
      ∀ (n : ℕ) (κ u : ℝ), 16 ≤ D n → D n ≤ n → 1 ≤ g n → (g n : ℝ) ≤ Real.sqrt (D n) → 1 ≤ κ →
        u ≤ (n : ℝ) ^ κ →
        T' n u ≤ 4 * (n : ℝ) * (g n : ℝ) *
            (T n (D n) (queryCap n (D n)) + C * ((n : ℝ) ^ 2 / Real.sqrt (D n))) +
          C * (termScans n (g n) κ + termSelect MM n (D n) κ p + termBuild n (D n) (g n))

/-- The bound that the proof of **Theorem 9** of the note yields from `XorClaim.Theorem_8` and
Corollary 16 when the dependence on `κ` is kept: one algorithm for Exact-XOR-Triangle that, for every
`n ≥ 16^18` and every `κ ≥ 1`, takes time at most `K κ^p n^{3−δ} (log n)^e` on weights at most
`n^κ`.  (`Claim.Theorem_19_explicit` is the case `p = 1`.) -/
def Theorem_9_explicit (M : DetTimeModel) (δ : ℝ) (e p : ℕ) : Prop :=
  ∃ (K : ℝ) (T : ℕ → ℝ → ℝ), M.exactTriangle T ∧
    ∀ (n : ℕ) (κ u : ℝ), 16 ^ 18 ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ ^ p * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e))

/-- The running time `K s^{3−δ} (log s + 1)^e (1 + log u)^p` for all sizes and all bounds on the
weights.  For `p = 2` it is `uniformTime` (`XorClaim.uniformTime_two`). -/
noncomputable def uniformTime (K δ : ℝ) (e p : ℕ) (s : ℕ) (u : ℝ) : ℝ :=
  K * ((s : ℝ) ^ (3 - δ) * (Real.log s + 1) ^ e * (1 + logU u) ^ p)

/-- With `p = 2` the time is the `uniformTime` of `Claim.ExactTriangleUniform`. -/
theorem uniformTime_two (K δ : ℝ) (e : ℕ) :
    XorClaim.uniformTime K δ e 2 = ThreeSumApsp.uniformTime K δ e := rfl

/-- Exact-XOR-Triangle is solved in time `K s^{3−δ} (log s + 1)^e (1 + log u)^p` for all numbers
`s ≥ 1` of vertices per part and all bounds `u ≥ 1` on the weights: `Claim.ExactTriangleUniform`
with the power `p` of `1 + log u` in place of 2. -/
def ExactTriangleUniform (M : DetTimeModel) (δ : ℝ) (e p : ℕ) : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ M.exactTriangle (XorClaim.uniformTime K δ e p)

/-- For `p = 2` the claim is `Claim.ExactTriangleUniform`. -/
theorem exactTriangleUniform_two_iff (M : DetTimeModel) (δ : ℝ) (e : ℕ) :
    ExactTriangleUniform M δ e 2 ↔ Claim.ExactTriangleUniform M δ e := Iff.rfl

end XorClaim

end ThreeSumApsp

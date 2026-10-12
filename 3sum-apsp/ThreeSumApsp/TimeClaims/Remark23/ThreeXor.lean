/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.TimeClaims.Remark23.Theorem9
public import ThreeSumApsp.TimeClaims.Sec3.Theorem21_22

/-!
# The main theorem of the note: 3XOR in `n^{2−ε'/2+o(1)}` time

This file is part of an unfinished proof of the running time of Remark 23 on the word RAM of
`EndStatement.lean`.  Runs A–C of the ten runs of its plan are done; the proof was then stopped by
the decision of the author, Ruhollah Majdoddin.  `EndStatement.Remark_23` is not proved.  The
mathematics of the note is proved in `ThreeSumApsp/Remark23/`, without its running time.

The note's proof of its main theorem composes the recursion of its Section 7 (3XOR to
polylogarithmically many Convolution-3XOR instances of size `m < 64n`), Corollary 11
(Convolution-3XOR of size `m` to `O(√m)` Exact-XOR-Triangle instances on `O(√m)` vertices per part)
and Theorem 9.  The first two are the claims `Claim.CH20_Theorem_5_1` and `Claim.VW13_Theorem_4_3`
of the 3SUM route, read for a model whose fields are the XOR problems (see
`TimeClaims/Remark23/Definitions.lean`), and `Theorem21a.of_CH20_VW13` composes them.  What is
new here is only that the bound for Exact-XOR-Triangle has the factor `(1 + log u)^p` in place of
`(1 + log u)²`; along `u = n^{O(1)}` it is a power of `log n`, so the composition is that of
`threeSum_of_uniform_theorem_21a` with `p` in place of 2.

`XorClaim.threeSum_of_claims` is the end of the chain, for every `M`: from Theorem 8, Corollary 16,
brute force, the two closure properties and the two reductions, 3XOR in `n^{2−ε'/2+o(1)}` time, and
so (`XorClaim.threeSum_bigO_of_claims`) in `O(n^a)` time for every `a > 2 − ε'/2 = 1.999125`, in
particular for `a = 1.9992`.
-/

@[expose] public section

namespace ThreeSumApsp

namespace XorClaim

/-- "Plug Theorem 9 into the reductions": with exponent `3 − δ` for Exact-XOR-Triangle, uniformly
in the size and with the factor `(1 + log u)^p`, the time for 3XOR is `n^{2−δ/2+o(1)}`.  This is
`threeSum_of_uniform_theorem_21a` with `p` in place of 2. -/
theorem threeSum_of_uniform_theorem_21a (M : DetTimeModel) {δ : ℝ} (e p : ℕ) (hδ1 : δ ≤ 1)
    (hu : XorClaim.ExactTriangleUniform M δ e p) (h21 : Claim.Theorem_21a M) :
    Claim.ThreeSumInLittleO M (2 - δ / 2) := by
  obtain ⟨K, -, hex⟩ := hu
  intro κ hκ
  obtain ⟨E, Num, mag, size, c', κ', hE, hNum, hsize, hpos, h⟩ := h21 κ hκ
  obtain ⟨T', hT', hb⟩ := h _ hex
  have hsizes := (isPowPolylog_rpow_mul_log_add_one_pow (3 - δ) e).isPowLittleO.comp hsize
    (by linarith) (by norm_num)
  have hwords := (((isPowPolylog_const 1).add
    (isPowPolylog_logU_of_le fun n hn => (hpos n hn).2)).pow p).isPowLittleO
  have htotal : IsPowLittleO
      (fun n => E n + Num n * XorClaim.uniformTime K δ e p (size n) (mag n)) (2 - δ / 2) :=
    (hE.mono (by linarith)).add
      ((hNum.mul ((hsizes.mul hwords).const_mul K)).mono (le_of_eq (by ring)))
  exact ⟨T', hT', htotal.upperPowLittleO.mono_left (Filter.eventually_atTop.2 ⟨1, hb⟩)⟩

/-- **The main theorem of the note**, as a deduction between running times: from Theorem 8 (with
Strassen's algorithm and the parameters `D = ⌊n^{1/18}⌋`, `g = ⌈D^{0.0315}⌉`), Corollary 16, brute
force, the two closure properties, the reduction of Section 7 (`Claim.CH20_Theorem_5_1`) and that of
Corollary 11 (`Claim.VW13_Theorem_4_3`): 3XOR on `n` vectors at most `n^κ` in
`n^{2−ε'/2+o(1)}` time, for every `κ`. -/
theorem threeSum_of_claims (M : DetTimeModel) {p : ℕ} (hp : 1 ≤ p)
    (h8 : XorClaim.Theorem_8 M strassen paramD₂₆ paramG₂₆ p) (h16 : Claim.Corollary_16 M)
    (hbf : Claim.BruteForce M) (hch : Closure.ChooseBySize M)
    (hmono : Closure.MonoExactTriangle M) (hCH : Claim.CH20_Theorem_5_1 M)
    (hVW : Claim.VW13_Theorem_4_3 M) : Claim.ThreeSumInLittleO M (2 - 0.00175 / 2) :=
  threeSum_of_uniform_theorem_21a M 1 p (by norm_num)
    (exactTriangleUniform_of_theorem_8 M hp h8 h16 hbf hch hmono)
    (Theorem21a.of_CH20_VW13 M hCH hVW)

/-- The main theorem of the note with an exponent: 3XOR in `O(n^a)` time for every
`a > 2 − ε'/2 = 1.999125`. -/
theorem threeSum_bigO_of_claims (M : DetTimeModel) {p : ℕ} (hp : 1 ≤ p)
    (h8 : XorClaim.Theorem_8 M strassen paramD₂₆ paramG₂₆ p) (h16 : Claim.Corollary_16 M)
    (hbf : Claim.BruteForce M) (hch : Closure.ChooseBySize M)
    (hmono : Closure.MonoExactTriangle M) (hCH : Claim.CH20_Theorem_5_1 M)
    (hVW : Claim.VW13_Theorem_4_3 M) {a : ℝ} (ha : 2 - 0.00175 / 2 < a) :
    Claim.SolvedAlongPow M.threeSum UpperBigOPow a :=
  (threeSum_of_claims M hp h8 h16 hbf hch hmono hCH hVW).mono fun _ hf => hf.upperBigOPow ha

/-- The exponent of Remark 23 as printed in the end statement: 3XOR in `O(n^{1.9992})` time,
since `2 − ε'/2 = 1.999125 < 1.9992`. -/
theorem threeSum_1_9992_of_claims (M : DetTimeModel) {p : ℕ} (hp : 1 ≤ p)
    (h8 : XorClaim.Theorem_8 M strassen paramD₂₆ paramG₂₆ p) (h16 : Claim.Corollary_16 M)
    (hbf : Claim.BruteForce M) (hch : Closure.ChooseBySize M)
    (hmono : Closure.MonoExactTriangle M) (hCH : Claim.CH20_Theorem_5_1 M)
    (hVW : Claim.VW13_Theorem_4_3 M) : Claim.SolvedAlongPow M.threeSum UpperBigOPow 1.9992 :=
  threeSum_bigO_of_claims M hp h8 h16 hbf hch hmono hCH hVW (by norm_num)

end XorClaim

end ThreeSumApsp

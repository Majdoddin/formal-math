/-
Statements of the paper «Thin matrix products up to D ≤ N^0.172 and lossless reductions for 3SUM,
Exact Triangle and APSP, with 3SUM over abelian groups and a dichotomy for coordinatewise problems»
(Ruhollah Majdoddin, 12 October 2026), in the paper's own numbering. This file states; it proves nothing. The proofs are in `ThinMatrixProducts/`, and `Checks.lean`
says, for every statement, that it holds.
-/
import Assumptions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Statements

Conventions.

* The paper's `H(x) = -x ln x - (1-x) ln(1-x)` is `H`. Logarithms are natural (`Real.log`);
  `log₂` is `Real.logb 2`. Powers with a real exponent are `Real.rpow` (written `^`).
* `D m = 4^m` (the padded inner dimension of Part I), `K L m = binom(L, m)`, `N0 L m = 4^(L-m)`.
* A number printed with an ellipsis, such as `0.17227…`, is stated as an enclosure between two
  decimals that agree with it to the printed digits.
* `NOTE` marks a place where the Lean text departs from the printed text.
-/

open Finset

namespace ThinMatrixProducts

/-! ## Part I: the numbers -/

section PartINumbers

/-- The entropy function `H(x) = -x ln x - (1-x) ln(1-x)` (Section 7, before (2)). -/
noncomputable def H (x : ℝ) : ℝ := -x * Real.log x - (1 - x) * Real.log (1 - x)

/-- `ε*_5 := ln 4/(5 ln 5)`, the limit of Part I (Section 1.1, Corollary 7.3). -/
noncomputable def epsStar5 : ℝ := Real.log 4 / (5 * Real.log 5)

/-- `ε*_10 := ln 4/(5 ln 10)`, the limit of [ZT] (its `ε*`; Section 1.1). -/
noncomputable def epsStar10 : ℝ := Real.log 4 / (5 * Real.log 10)

/-- The padded inner dimension `D = 4^m`, as a real number. -/
noncomputable def Dr (m : ℕ) : ℝ := (4 : ℝ) ^ m

/-- `K = binom(L, m)`. -/
def K (L m : ℕ) : ℕ := L.choose m

/-- `N₀ = 4^(L-m)`, the block size of Part I. -/
def N0 (L m : ℕ) : ℕ := 4 ^ (L - m)

/-- The decay rate `ρ = 4m/(L-m+1)` of Lemma 6.1. -/
noncomputable def rho (L m : ℕ) : ℝ := 4 * (m : ℝ) / ((L : ℝ) - (m : ℝ) + 1)

/-- `ρ_c := 4/(c-1)` (Corollary 7.3). -/
noncomputable def rhoC (c : ℝ) : ℝ := 4 / (c - 1)

/-- Equation (2): `Λ_c(γ) := (25/4)^c e^{-c H(1/c)} 4^{1+γ}`. -/
noncomputable def LambdaC (c γ : ℝ) : ℝ :=
  (25 / 4 : ℝ) ^ c * Real.exp (-c * H (1 / c)) * (4 : ℝ) ^ (1 + γ)

/-- Equation (2): `R'_c(γ) := ln 4/ln Λ_c(γ)`. -/
noncomputable def RPrime (c γ : ℝ) : ℝ := Real.log 4 / Real.log (LambdaC c γ)

/-- Corollary 7.3: `γ := θ log₂((c-1)/4)`. -/
noncomputable def gammaOf (c θ : ℝ) : ℝ := θ * Real.logb 2 ((c - 1) / 4)

/-- Corollary 7.3: `q := (H(θ) + θ ln 4)/ln 2`. -/
noncomputable def qOf (θ : ℝ) : ℝ := (H θ + θ * Real.log 4) / Real.log 2

/-- Section 4: `μ_k := ∏_{i=1}^{k} (1 - 2^{-i})`. -/
noncomputable def mu (k : ℕ) : ℝ := ∏ i ∈ range k, (1 - (2 : ℝ)⁻¹ ^ (i + 1))

/-- Section 4: `μ_∞ := lim_k μ_k`. The sequence decreases, so the limit is the infimum. -/
noncomputable def muInf : ℝ := ⨅ k : ℕ, mu k

/-- Corollary 9.1(a): `γ := log₂(27/8)/19`. -/
noncomputable def gammaA : ℝ := Real.logb 2 (27 / 8) / 19

/-- Corollary 9.1(a): `q := log₂(72^{1/19} · 19/18)`. -/
noncomputable def qA : ℝ := Real.logb 2 ((72 : ℝ) ^ ((1 : ℝ) / 19) * (19 / 18))

/-- Corollary 9.1(a): `Λ := Λ_{14.5}(γ)`. -/
noncomputable def LambdaA : ℝ := LambdaC 14.5 gammaA

/-- Corollary 9.1(b): `γ := log₂(21/8)/18`. -/
noncomputable def gammaB : ℝ := Real.logb 2 (21 / 8) / 18

/-- Corollary 9.1(b): `q := log₂(68^{1/18} · 18/17)`. -/
noncomputable def qB : ℝ := Real.logb 2 ((68 : ℝ) ^ ((1 : ℝ) / 18) * (18 / 17))

/-- Corollary 9.1(b): `Λ := Λ_{11.5}(γ)`. -/
noncomputable def LambdaB : ℝ := LambdaC 11.5 gammaB

/-- The number of levels `L := ⌈c m⌉` (proof of Corollary 7.3). -/
noncomputable def levelsOf (c : ℝ) (m : ℕ) : ℕ := ⌈c * (m : ℝ)⌉₊

/-- The switching order `t := ⌈2θm⌉` (Corollary 7.3). -/
noncomputable def switchOf (θ : ℝ) (m : ℕ) : ℕ := ⌈2 * θ * (m : ℝ)⌉₊

end PartINumbers

/-! ### Item: the threshold (abstract, Theorem A, Corollary 7.3, Proposition 8.1) -/

/-- Theorem A, Corollary 7.3: "`ε*_5 := ln 4/(5 ln 5) = 0.17227…`". -/
def Sec1_epsStar5_value : Prop := 0.17227 < epsStar5 ∧ epsStar5 < 0.17228

/-- Theorem A: "the threshold `N ≥ D^{1/ε}` may have any exponent `1/ε > 5 ln 5/ln 4 = 5.8048…`,
where the preprint's needs `1/ε > 5 ln 10/ln 4 = 8.3048…`". -/
def Theorem_A_thresholds : Prop :=
  1 / epsStar5 = 5 * Real.log 5 / Real.log 4 ∧
    5.8048 < 5 * Real.log 5 / Real.log 4 ∧ 5 * Real.log 5 / Real.log 4 < 5.8049 ∧
    1 / epsStar10 = 5 * Real.log 10 / Real.log 4 ∧
    8.3048 < 5 * Real.log 10 / Real.log 4 ∧ 5 * Real.log 10 / Real.log 4 < 8.3049

/-- Section 1.1: "`ε*_10 := ln 4/(5 ln 10) = 0.1204…`", and Proposition 8.1: "`0.12041`". -/
def Sec1_epsStar10_value : Prop := 0.12041 < epsStar10 ∧ epsStar10 < 0.12042

/-- Section 8: "The value `ε*_5 = 2 log 2/(5 log 5)` is the `α` of Coppersmith's theorem", and
Proposition 8.1: "Both limits have the form `ε*_R = 2 ln q₀/(R ln R)`" with `R = 10`, `q₀ = 4` and
`R = 5`, `q₀ = 2`. -/
def Proposition_8_1_form : Prop :=
  epsStar5 = 2 * Real.log 2 / (5 * Real.log 5) ∧
    epsStar10 = 2 * Real.log 4 / (10 * Real.log 10)

/-! ### Section 4: the constants `μ_k` and `μ_∞` -/

/-- Section 4: "`μ_k := ∏_{i=1}^{k} (1-2^{-i})`, the probability that a uniform `k × k` matrix over
`F₂` is invertible": a matrix is invertible exactly when its `k` columns are linearly independent,
and there are `2^{k²} μ_k` linearly independent `k`-tuples of vectors of `F₂^k`. -/
def Sec4_mu_probability : Prop :=
  ∀ k : ℕ, (Nat.card {s : Fin k → (Fin k → ZMod 2) // LinearIndependent (ZMod 2) s} : ℝ)
    = 2 ^ (k ^ 2) * mu k

/-- Section 4: "`μ_∞ := lim_k μ_k = 0.2887…`, so `μ_∞² = 0.08339…`; note `μ_k > μ_∞` for all
`k`", and Section 7, change (4): "`μ_∞^{-4} < 144`". -/
def Sec4_mu_values : Prop :=
  Filter.Tendsto mu Filter.atTop (nhds muInf) ∧ (∀ k, muInf < mu k) ∧
    0.2887 < muInf ∧ muInf < 0.2888 ∧ 0.08339 < muInf ^ 2 ∧ muInf ^ 2 < 0.08340 ∧
    1 / muInf ^ 4 < 144

/-- Equation (4): "`(25/4)/μ_∞² < 75`". -/
def Eq_4_constant : Prop := (25 / 4) / muInf ^ 2 < 75

/-! ### Corollary 7.3: the trade-off -/

/-- Corollary 7.3: "`γ := θ log₂((c-1)/4) > 0`" for `c > 5` and `θ > 0`. -/
def Corollary_7_3_gamma_pos : Prop :=
  ∀ c θ : ℝ, 5 < c → 0 < θ → 0 < gammaOf c θ

/-- Proof of Corollary 7.3, "Boxes": with `L := ⌈cm⌉` and `t := ⌈2θm⌉`, "`ρ < ρ_c` gives
`ρ^t ≤ ρ_c^{2θm} = D^{-γ}`, and `1/(1-ρ) < 1/(1-ρ_c)`". -/
def Corollary_7_3_boxes : Prop :=
  ∀ c θ : ℝ, 5 < c → 0 < θ → ∀ m : ℕ, 1 ≤ m →
    rho (levelsOf c m) m < rhoC c ∧ rhoC c < 1 ∧
      1 / (1 - rho (levelsOf c m) m) < 1 / (1 - rhoC c) ∧
      rho (levelsOf c m) m ^ switchOf θ m ≤ rhoC c ^ (2 * θ * m) ∧
      rhoC c ^ (2 * θ * m) = Dr m ^ (-gammaOf c θ)

/-- Proof of Corollary 7.3, "Queries": with `x := (1-θ)/θ`, "`4x > 1` because `θ < 0.8`, … so
`∑_{d ≤ t} binom(2m, d) 4^d ≤ (4x)^t (1+1/x)^{2m} ≤ 4x ((4x)^θ/(1-θ))^{2m} = 4x D^q`, using
`(4x)^θ/(1-θ) = 4^θ e^{H(θ)}`". -/
def Corollary_7_3_queries : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 0.8 → ∀ m : ℕ,
    1 < 4 * ((1 - θ) / θ) ∧
    (4 * ((1 - θ) / θ)) ^ θ / (1 - θ) = (4 : ℝ) ^ θ * Real.exp (H θ) ∧
    (∑ d ∈ range (switchOf θ m + 1), ((2 * m).choose d : ℝ) * 4 ^ d)
      ≤ 4 * ((1 - θ) / θ) * Dr m ^ qOf θ

/-- Equations (3) and (4): with `L := ⌈cm⌉`, `K_g ≥ μ_∞² K`, "the left-hand side of (3) is at most
`(25/4)/μ_∞² (cm+2) Λ_c(γ)^m`". -/
def Eq_4 : Prop :=
  ∀ c γ : ℝ, 5 < c → 0 ≤ γ → ∀ m : ℕ, 1 ≤ m → ∀ Kg : ℝ, muInf ^ 2 * K (levelsOf c m) m ≤ Kg →
    Dr m ^ γ * (25 : ℝ) ^ levelsOf c m / (Kg * N0 (levelsOf c m) m)
      ≤ (25 / 4) / muInf ^ 2 * (c * m + 2) * LambdaC c γ ^ m

/-- Proof of Corollary 7.3: "the condition `N ≥ K N₀` [follows from (3)] because
`25^L = (1+4)^{2L} ≥ binom(2L, 2m) 16^{L-m} ≥ K² N₀²`" (with `K_g ≤ K`). -/
def Corollary_7_3_tile_fit : Prop :=
  (∀ L m : ℕ, m ≤ L → ((K L m : ℝ) * N0 L m) ^ 2 ≤ (25 : ℝ) ^ L) ∧
  ∀ (L m : ℕ) (γ Kg N : ℝ), m ≤ L → 0 ≤ γ → 0 < Kg → Kg ≤ K L m →
    Dr m ^ γ * (25 : ℝ) ^ L / (Kg * N0 L m) ≤ N → (K L m : ℝ) * N0 L m ≤ N

/-- Equation (2), second form: `R'_c(γ) = ln 2/(c ln 5 - (c/2) H(1/c) - (c-1) ln 2 + γ ln 2)`, and
`ln Λ_c(γ) = 2c ln 5 - c H(1/c) - (c-1) ln 4 + γ ln 4`. -/
def Eq_2_forms : Prop :=
  ∀ c γ : ℝ, 1 < c →
    Real.log (LambdaC c γ) = 2 * c * Real.log 5 - c * H (1 / c) - (c - 1) * Real.log 4
        + γ * Real.log 4 ∧
    RPrime c γ = Real.log 2 /
      (c * Real.log 5 - c / 2 * H (1 / c) - (c - 1) * Real.log 2 + γ * Real.log 2)

/-- Proof of Corollary 7.3: "As `ε < R'_c(γ)` says `Λ_c(γ) < 4^{1/ε}`" (for `ε > 0`, `c ≥ 5`,
`γ ≥ 0`). -/
def Corollary_7_3_eps_iff : Prop :=
  ∀ c γ ε : ℝ, 5 ≤ c → 0 ≤ γ → 0 < ε → (ε < RPrime c γ ↔ LambdaC c γ < (4 : ℝ) ^ (1 / ε))

/-- Proof of Corollary 7.3: "(3) holds once `m` exceeds a constant depending on `c, θ, ε`": for
`ε < R'_c(γ)` there is `m₀` with `75 (cm+2) Λ_c(γ)^m ≤ N` whenever `m ≥ m₀` and
`N ≥ 4^{(m-1)/ε}`. -/
def Corollary_7_3_range : Prop :=
  ∀ c γ ε : ℝ, 5 ≤ c → 0 ≤ γ → 0 < ε → ε < RPrime c γ →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ N : ℝ, (4 : ℝ) ^ (((m : ℝ) - 1) / ε) ≤ N →
      75 * (c * m + 2) * LambdaC c γ ^ m ≤ N

/-- Proof of Corollary 7.3: "`d/dc (2c ln 5 - c H(1/c) - (c-1) ln 4) = ln(25(c-1)/(4c)) > 0`",
and "at `c = 5` the identity `H(1/5) + (4/5) ln 4 = ln 5` gives `10 ln 5 - 5 H(1/5) - 4 ln 4 =
5 ln 5`". -/
def Corollary_7_3_derivative : Prop :=
  (∀ c : ℝ, 1 < c →
    HasDerivAt (fun c => 2 * c * Real.log 5 - c * H (1 / c) - (c - 1) * Real.log 4)
      (Real.log (25 * (c - 1) / (4 * c))) c) ∧
  (∀ c : ℝ, 5 < c → 0 < Real.log (25 * (c - 1) / (4 * c))) ∧
  H (1 / 5) + 4 / 5 * Real.log 4 = Real.log 5 ∧
  10 * Real.log 5 - 5 * H (1 / 5) - 4 * Real.log 4 = 5 * Real.log 5

/-- Corollary 7.3: "Moreover `R'_c(0)` increases to `ε*_5 := ln 4/(5 ln 5)` as `c` decreases to
`5`." -/
def Corollary_7_3_limit : Prop :=
  StrictAntiOn (fun c => RPrime c 0) (Set.Ici 5) ∧ RPrime 5 0 = epsStar5 ∧
    Filter.Tendsto (fun c => RPrime c 0) (nhdsWithin 5 (Set.Ioi 5)) (nhds epsStar5)

/-- Proof of Theorem 7.4: "choose `c > 5` with `R'_c(0) > ε`, then `θ` small enough that
`q(θ) < q/2` … and `R'_c(γ(θ)) > ε`". The parameters exist, with `θ < 0.8` as Corollary 7.3
needs. -/
def Theorem_7_4_parameters : Prop :=
  ∀ ε q : ℝ, ε < epsStar5 → 0 < q →
    ∃ c θ : ℝ, 5 < c ∧ 0 < θ ∧ θ < 0.8 ∧ qOf θ < q / 2 ∧ ε < RPrime c (gammaOf c θ) ∧
      0 < gammaOf c θ

/-- Proposition 8.1: "The range of Corollary 7.3 is `ε < ε*_5`": `R'_c(γ) < ε*_5` for all `c > 5`,
`γ ≥ 0`, and every `ε < ε*_5` is below some `R'_c(0)`, `c > 5`; "the leaf count needs `c > R`":
`ρ_c < 1` exactly when `c > 5`. -/
def Proposition_8_1_range : Prop :=
  (∀ c γ : ℝ, 5 < c → 0 ≤ γ → RPrime c γ < epsStar5) ∧
  (∀ ε : ℝ, ε < epsStar5 → ∃ c : ℝ, 5 < c ∧ ε < RPrime c 0) ∧
  (∀ c : ℝ, 1 < c → (rhoC c < 1 ↔ 5 < c))

/-- Proof of Proposition 8.1: "`binom(5m, m) 4^{4m}`, the largest term of `(1+4)^{5m}`, is `5^{5m}`
up to polynomial factors", and the same for Schönhage's identity with `binom(10m, m) 9^{9m}` and
`10^{10m}`; and "`N ≥ 5^L = D^{1/ε*_5}`" at `L = 5m`. -/
def Proposition_8_1_terms : Prop :=
  (∀ m : ℕ, (5 : ℝ) ^ (5 * m) / (5 * m + 1) ≤ ((5 * m).choose m : ℝ) * 4 ^ (4 * m) ∧
      ((5 * m).choose m : ℝ) * 4 ^ (4 * m) ≤ (5 : ℝ) ^ (5 * m)) ∧
  (∀ m : ℕ, (10 : ℝ) ^ (10 * m) / (10 * m + 1) ≤ ((10 * m).choose m : ℝ) * 9 ^ (9 * m) ∧
      ((10 * m).choose m : ℝ) * 9 ^ (9 * m) ≤ (10 : ℝ) ^ (10 * m)) ∧
  (∀ m : ℕ, Dr m ^ (1 / epsStar5) = (5 : ℝ) ^ (5 * m))

/-! ### Corollary 9.1: the explicit instances -/

/-- Corollary 9.1(a), "Setting up": "Let `m := ⌈log₄ D⌉` and pad the inner dimension to
`4^m < 4D` … `N ≥ D^{18}` now reads `N ≥ 4^{18(m-1)}`." -/
def Corollary_9_1_setting_up : Prop :=
  ∀ D₀ : ℕ, 2 ≤ D₀ →
    1 ≤ ⌈Real.logb 4 D₀⌉₊ ∧ (D₀ : ℝ) ≤ 4 ^ ⌈Real.logb 4 D₀⌉₊ ∧
      (4 : ℝ) ^ ⌈Real.logb 4 D₀⌉₊ < 4 * D₀ ∧
      ∀ (a : ℕ) (N : ℝ), (D₀ : ℝ) ^ a ≤ N → (4 : ℝ) ^ (a * (⌈Real.logb 4 D₀⌉₊ - 1)) ≤ N

/-- Corollary 9.1(a): "`γ := log₂(27/8)/19 = 0.09236…`", "`q := log₂(72^{1/19}·19/18) =
0.40273…`", "`0.403 + 0.092 < 1/2`". -/
def Corollary_9_1_a_exponents : Prop :=
  0.09236 < gammaA ∧ gammaA < 0.09237 ∧ 0.40273 < qA ∧ qA < 0.40274 ∧
    (0.403 : ℝ) + 0.092 < 1 / 2 ∧ gammaA = gammaOf 14.5 (1 / 19) ∧ qA = qOf (1 / 19)

/-- Corollary 9.1(a): "`Λ := Λ_{14.5}(γ) = (25/4)^{14.5} e^{-14.5 H(1/14.5)}·4·(27/8)^{2/19} =
4.1456…·10^{10}`. The base `4^{18} = 6.8719…·10^{10}` … is larger than `Λ` by a factor of more than
`1.657`". -/
def Corollary_9_1_a_Lambda : Prop :=
  LambdaA = (25 / 4 : ℝ) ^ (14.5 : ℝ) * Real.exp (-14.5 * H (1 / 14.5)) * 4 * (27 / 8 : ℝ) ^ (2 / 19 : ℝ) ∧
  4.1456e10 < LambdaA ∧ LambdaA < 4.1457e10 ∧ (6.8719e10 : ℝ) < 4 ^ 18 ∧ (4 : ℝ) ^ 18 < 6.8720e10 ∧
    1.657 * LambdaA < 4 ^ 18

/-- Corollary 9.1(a): "the inequality holds whenever `1.657^m ≥ 4^{18}·75 (14.5m+2)`, which is
the case for all `m ≥ 72`". -/
def Corollary_9_1_a_threshold : Prop :=
  ∀ m : ℕ, 72 ≤ m → (4 : ℝ) ^ 18 * 75 * (14.5 * m + 2) ≤ 1.657 ^ m

/-- Corollary 9.1(a), "Encodings": for `m ≥ 72`, `L := ⌈14.5 m⌉` and `N ≥ 4^{18(m-1)}`, (3) holds,
and with it the condition `N ≥ K N₀` of Theorem 7.2. -/
def Corollary_9_1_a_encodings : Prop :=
  ∀ m : ℕ, 72 ≤ m → ∀ N Kg : ℝ, (4 : ℝ) ^ (18 * (m - 1)) ≤ N →
    muInf ^ 2 * K (levelsOf 14.5 m) m ≤ Kg → Kg ≤ K (levelsOf 14.5 m) m →
    Dr m ^ gammaA * (25 : ℝ) ^ levelsOf 14.5 m / (Kg * N0 (levelsOf 14.5 m) m) ≤ N ∧
      (K (levelsOf 14.5 m) m : ℝ) * N0 (levelsOf 14.5 m) m ≤ N

/-- Corollary 9.1(a), "Boxes": "`ρ = 4m/(L-m+1) < 4/13.5 = 8/27`, so `1/(1-ρ) < 27/19`, and since
`t ≥ 2m/19`, `ρ^t ≤ (8/27)^{2m/19} = D^{-γ}`". -/
def Corollary_9_1_a_boxes : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    rho (levelsOf 14.5 m) m < 8 / 27 ∧ 1 / (1 - rho (levelsOf 14.5 m) m) < 27 / 19 ∧
      rho (levelsOf 14.5 m) m ^ switchOf (1 / 19) m ≤ Dr m ^ (-gammaA)

/-- Corollary 9.1(a), "Queries": "`∑_{d=0}^{t} binom(2m,d) 4^d ≤ 72^t (19/18)^{2m} < 72 D^q`". -/
def Corollary_9_1_a_queries : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∑ d ∈ range (switchOf (1 / 19) m + 1), ((2 * m).choose d : ℝ) * 4 ^ d) < 72 * Dr m ^ qA

/-- Corollary 9.1(b): "`γ := log₂(21/8)/18 = 0.07735…`", "`q := log₂(68^{1/18}·18/17) = 0.42065…`",
"`0.077 < 0.07735` and `0.421 > 0.42065`, and `0.421 + 0.077 < 1/2`". -/
def Corollary_9_1_b_exponents : Prop :=
  0.07735 < gammaB ∧ gammaB < 0.07736 ∧ 0.42065 < qB ∧ qB < 0.42066 ∧
    (0.421 : ℝ) + 0.077 < 1 / 2 ∧ gammaB = gammaOf 11.5 (1 / 18) ∧ qB = qOf (1 / 18)

/-- Corollary 9.1(b): "`Λ := Λ_{11.5}(γ) = 2.1169…·10^8`, against `4^{14} = 2.6843…·10^8`, a
factor of more than `1.268`". -/
def Corollary_9_1_b_Lambda : Prop :=
  2.1169e8 < LambdaB ∧ LambdaB < 2.1170e8 ∧ (2.6843e8 : ℝ) < 4 ^ 14 ∧ (4 : ℝ) ^ 14 < 2.6844e8 ∧
    1.268 * LambdaB < 4 ^ 14

/-- Corollary 9.1(b): "(3) holds whenever `1.268^m ≥ 4^{14}·75 (11.5m+2)`, that is for all
`m ≥ 131`". -/
def Corollary_9_1_b_threshold : Prop :=
  ∀ m : ℕ, 131 ≤ m → (4 : ℝ) ^ 14 * 75 * (11.5 * m + 2) ≤ 1.268 ^ m

/-- Corollary 9.1(b), encodings: as `Corollary_9_1_a_encodings` with `L := ⌈11.5 m⌉`, `m ≥ 131`
and `N ≥ 4^{14(m-1)}`. -/
def Corollary_9_1_b_encodings : Prop :=
  ∀ m : ℕ, 131 ≤ m → ∀ N Kg : ℝ, (4 : ℝ) ^ (14 * (m - 1)) ≤ N →
    muInf ^ 2 * K (levelsOf 11.5 m) m ≤ Kg → Kg ≤ K (levelsOf 11.5 m) m →
    Dr m ^ gammaB * (25 : ℝ) ^ levelsOf 11.5 m / (Kg * N0 (levelsOf 11.5 m) m) ≤ N ∧
      (K (levelsOf 11.5 m) m : ℝ) * N0 (levelsOf 11.5 m) m ≤ N

/-- Corollary 9.1(b), boxes: "`ρ < 4/10.5 = 8/21`", and `ρ^t ≤ D^{-γ}` with `t := ⌈2m/18⌉`. -/
def Corollary_9_1_b_boxes : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    rho (levelsOf 11.5 m) m < 8 / 21 ∧ rho (levelsOf 11.5 m) m ^ switchOf (1 / 18) m ≤ Dr m ^ (-gammaB)

/-- Corollary 9.1(b), queries: "`x = 17`, `∑_{d ≤ t} binom(2m,d) 4^d < 68 D^q`". -/
def Corollary_9_1_b_queries : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∑ d ∈ range (switchOf (1 / 18) m + 1), ((2 * m).choose d : ℝ) * 4 ^ d) < 68 * Dr m ^ qB

/-- Corollary 9.1, "Conclusion": "Since `m = O(log D)` and the exponents `0.09236 - 0.092` and
`0.403 - q` are positive, these are `O(N²/D^{0.092})` and `O(D^{0.403})`" (and likewise in (b)):
`m³ D^{-γ} = O(D^{-0.092})` and `m D^q + m² = O(D^{0.403})`. -/
def Corollary_9_1_conclusion : Prop :=
  ∃ C : ℝ, ∀ m : ℕ,
    (m : ℝ) ^ 3 * Dr m ^ (-gammaA) ≤ C * Dr m ^ (-0.092 : ℝ) ∧
    (m : ℝ) * Dr m ^ qA + (m : ℝ) ^ 2 ≤ C * Dr m ^ (0.403 : ℝ) ∧
    (m : ℝ) ^ 3 * Dr m ^ (-gammaB) ≤ C * Dr m ^ (-0.077 : ℝ) ∧
    (m : ℝ) * Dr m ^ qB + (m : ℝ) ^ 2 ≤ C * Dr m ^ (0.421 : ℝ)

/-! ### Section 16 and the introduction: the exponents of the problems -/

/-- Corollary 16.1(a), its constant: "`ε'_I := 0.077/28 = 0.00275`", and the exponent:
"`O(n^{3-ε'_I} log n) ≤ O(n^{2.9973})`". -/
def Corollary_16_1_a_constant : Prop :=
  (0.077 : ℝ) / 28 = 0.00275 ∧ (3 : ℝ) - 0.00275 ≤ 2.9973

/-- Proof of Corollary 16.1(a): with `D := ⌊n^{1/14}⌋` and `g := ⌈D^{0.0385}⌉`: "`g ≤ √D`" (for
`D ≥ 4`; for `D = 2, 3` it fails, which the `O(·)` absorbs); "the `O(n D^{0.0385})` instances cost
`O(n²/D^{0.077})` each, so `O(n³ D^{-0.0385})` in all"; "`O(n^{log₂ 7} D^{3/2}) ≤ O(n^{2.92})`";
"`D ≥ n^{1/14}/2` gives `D^{-0.0385} ≤ 2 n^{-0.00275}`". -/
def Corollary_16_1_a_steps : Prop :=
  (∀ D : ℕ, 4 ≤ D → (⌈(D : ℝ) ^ (0.0385 : ℝ)⌉₊ : ℝ) ≤ Real.sqrt D) ∧
  (∀ n D : ℝ, 0 < n → 0 < D →
    n * D ^ (0.0385 : ℝ) * (n ^ 2 / D ^ (0.077 : ℝ)) = n ^ 3 * D ^ (-0.0385 : ℝ)) ∧
  (∀ n D : ℝ, 1 ≤ n → 0 < D → D ≤ n ^ ((1 : ℝ) / 14) →
    n ^ Real.logb 2 7 * D ^ (3 / 2 : ℝ) ≤ n ^ (2.92 : ℝ)) ∧
  (∀ n : ℝ, 1 ≤ n →
    ((⌊n ^ ((1 : ℝ) / 14)⌋₊ : ℕ) : ℝ) ≥ n ^ ((1 : ℝ) / 14) / 2 ∧
    ((⌊n ^ ((1 : ℝ) / 14)⌋₊ : ℕ) : ℝ) ^ (-0.0385 : ℝ) ≤ 2 * n ^ (-0.00275 : ℝ))

/-- Proof of Corollary 16.1(b): "`n^{3/2+o(1)} + n^{1/2+o(1)} (n^{1/2+o(1)})^{3-ε'_I} =
n^{2-ε'_I/2+o(1)}`" (the exponents), "`Õ(n²(n^{1/3})^{3-ε'_I}) = Õ(n^{3-ε'_I/3})`", and
"`2 - 0.001375 < 1.99863` and `3 - 0.000917 < 2.99909`". -/
def Corollary_16_1_b_exponents : Prop :=
  (∀ e : ℝ, 0 ≤ e → e ≤ 1 →
    max (3 / 2) (1 / 2 + 1 / 2 * (3 - e)) = 2 - e / 2 ∧ 2 + 1 / 3 * (3 - e) = 3 - e / 3) ∧
  (2 : ℝ) - 0.00275 / 2 < 1.99863 ∧ (3 : ℝ) - 0.00275 / 3 < 2.99909 ∧
  (0.00275 : ℝ) / 2 = 0.001375 ∧ (0.00275 : ℝ) / 3 < 0.000917

/-- Corollary 16.1(c), (d), the remark after it, and Remark 16.2: "`n^{2-0.0035+o(1)} =
n^{1.99650+o(1)}`", "`n^{3-0.0035+o(1)} = n^{2.99650+o(1)}`" (with `0.063/18 = 0.0035`),
"`n^{2-0.0055+o(1)} = n^{1.99450+o(1)}`", "`n^{2.99450+o(1)}`" (with `0.077/14 = 0.0055`);
"`εγ = 0.092/18 = 0.00511`, … `n^{1.99489+o(1)}` and `n^{2.99489+o(1)}`" (rounded up); and the
rate values `0.005652`, `0.005825` giving "`n^{1.99435}` and `n^{1.99418}`" and "`n^{2.99435}` and
`n^{2.99418}`" (rounded up). -/
def Corollary_16_1_cd_exponents : Prop :=
  (0.063 : ℝ) / 18 = 0.0035 ∧ (2 : ℝ) - 0.0035 = 1.99650 ∧ (3 : ℝ) - 0.0035 = 2.99650 ∧
  (0.077 : ℝ) / 14 = 0.0055 ∧ (2 : ℝ) - 0.0055 = 1.99450 ∧ (3 : ℝ) - 0.0055 = 2.99450 ∧
  (0.00511 : ℝ) < 0.092 / 18 ∧ (0.092 : ℝ) / 18 < 0.00512 ∧
  (2 : ℝ) - 0.092 / 18 ≤ 1.99489 ∧ 1.99488 < (2 : ℝ) - 0.092 / 18 ∧
  (3 : ℝ) - 0.092 / 18 ≤ 2.99489 ∧ 2.99488 < (3 : ℝ) - 0.092 / 18 ∧
  (2 : ℝ) - 0.005652 ≤ 1.99435 ∧ (2 : ℝ) - 0.005825 ≤ 1.99418 ∧
  (3 : ℝ) - 0.005652 ≤ 2.99435 ∧ (3 : ℝ) - 0.005825 ≤ 2.99418 ∧
  1.99434 < (2 : ℝ) - 0.005652 ∧ 1.99417 < (2 : ℝ) - 0.005825

/-- Section 1.3 and Table 2: "[the preprint's] own exponents for 3SUM and Exact Triangle,
recomputed as `2 - ε'/2` and `3 - ε'` with its `ε' = 0.00175`, are `1.99913` and `2.99825`", and
APSP `3 - ε'/3 = 2.99942` (Section 15.7), with `ε' = εγ/2` for `εγ = 0.0035`; the fractions kept,
`2 - ε'/2 = 2 - εγ/4`, `3 - ε' = 3 - εγ/2`, `3 - ε'/3 = 3 - εγ/6`. Rounded up in the last digit. -/
def Sec1_preprint_exponents : Prop :=
  (0.0035 : ℝ) / 2 = 0.00175 ∧
  (2 : ℝ) - 0.00175 / 2 ≤ 1.99913 ∧ 1.99912 < (2 : ℝ) - 0.00175 / 2 ∧
  (3 : ℝ) - 0.00175 = 2.99825 ∧
  (3 : ℝ) - 0.00175 / 3 ≤ 2.99942 ∧ 2.99941 < (3 : ℝ) - 0.00175 / 3 ∧
  ∀ e : ℝ, 2 - (e / 2) / 2 = 2 - e / 4 ∧ 3 - e / 2 = 3 - e / 2 ∧ 3 - (e / 2) / 3 = 3 - e / 6

/-- Section 13.7, the table: with `(ε, γ) = (1/18, 0.063)` the 3SUM exponent `2 - εγ + ε/r` is
"`n^{1.99836}`, `n^{1.99789}`, `n^{1.99720}`" for `r = 30, 40, 80` (rounded up in the last
digit), and "to beat `2 - εγ/4` one needs `ε/r < (3/4) εγ`, i.e. `r > 4/(3γ)`: `r ≥ 22` for
`γ = 0.063`". -/
def Sec13_7_table : Prop :=
  (2 : ℝ) - 0.0035 + (1 / 18) / 30 ≤ 1.99836 ∧ 1.99835 < (2 : ℝ) - 0.0035 + (1 / 18) / 30 ∧
  (2 : ℝ) - 0.0035 + (1 / 18) / 40 ≤ 1.99789 ∧ 1.99788 < (2 : ℝ) - 0.0035 + (1 / 18) / 40 ∧
  (2 : ℝ) - 0.0035 + (1 / 18) / 80 ≤ 1.99720 ∧ 1.99719 < (2 : ℝ) - 0.0035 + (1 / 18) / 80 ∧
  (∀ ε γ r : ℝ, 0 < ε → 0 < γ → 0 < r →
    (2 - ε * γ + ε / r < 2 - ε * γ / 4 ↔ 4 / (3 * γ) < r)) ∧
  (∀ r : ℕ, (4 / (3 * 0.063) : ℝ) < r ↔ 22 ≤ r)

/-- Section 15.7, the table: the Exact Triangle exponent `3 - εγ + ε/(2r)` is "`n^{2.99789}`,
`n^{2.99720}`, `n^{2.99685}`" for `r = 20, 40, 80`; "to beat … `3 - εγ/2` one needs
`ε/(2r) < εγ/2`, i.e. `r > 1/γ`: `r ≥ 16`"; "to beat the APSP exponent `3 - εγ/6` … one needs
`ε/(2r) < (5/6) εγ`, i.e. `r > 3/(5γ)`: `r ≥ 10`". -/
def Sec15_7_table : Prop :=
  (3 : ℝ) - 0.0035 + (1 / 18) / 40 ≤ 2.99789 ∧ 2.99788 < (3 : ℝ) - 0.0035 + (1 / 18) / 40 ∧
  (3 : ℝ) - 0.0035 + (1 / 18) / 80 ≤ 2.99720 ∧ 2.99719 < (3 : ℝ) - 0.0035 + (1 / 18) / 80 ∧
  (3 : ℝ) - 0.0035 + (1 / 18) / 160 ≤ 2.99685 ∧ 2.99684 < (3 : ℝ) - 0.0035 + (1 / 18) / 160 ∧
  (∀ ε γ r : ℝ, 0 < ε → 0 < γ → 0 < r →
    (3 - ε * γ + ε / (2 * r) < 3 - ε * γ / 2 ↔ 1 / γ < r) ∧
    (3 - ε * γ + ε / (2 * r) < 3 - ε * γ / 6 ↔ 3 / (5 * γ) < r)) ∧
  (∀ r : ℕ, (1 / 0.063 : ℝ) < r ↔ 16 ≤ r) ∧ (∀ r : ℕ, (3 / (5 * 0.063) : ℝ) < r ↔ 10 ≤ r)

/-- Sections 1.2, 13.7 and 15.7, "Constants": "`r = 40` gains about `n^{0.00124}` over the
preprint's `n^{1.99913}` (`1.999125 - 1.997889`) but pays `(ln n)^{44}`, which is larger until
`ln n ≈ 4.6·10^5`": with `g = 1.999125 - 1.997889`, `44 ln x > g x` at `x = ln n = 4.6·10^5` and
`<` at `4.7·10^5`; and for Exact Triangle "`r = 40` gains about `n^{0.00106}` … (`2.99825 -
2.9971944`) but pays an extra factor `(ln n)^{41}`, which is larger until `ln n ≈ 5.1·10^5`":
`41 ln x > g' x` at `5.0·10^5` and `<` at `5.2·10^5`. -/
def Sec13_7_crossing : Prop :=
  (1.999125 : ℝ) - 1.997889 = 0.001236 ∧
  0.001236 * 4.6e5 < 44 * Real.log 4.6e5 ∧ 44 * Real.log 4.7e5 < 0.001236 * 4.7e5 ∧
  (2.99825 : ℝ) - 2.9971944 = 0.0010556 ∧
  0.0010556 * 5.0e5 < 41 * Real.log 5.0e5 ∧ 41 * Real.log 5.2e5 < 0.0010556 * 5.2e5

/-- Section 10, after Corollary 10.1: "`2 - ε*_5 = 1.8277…` (rounded down as the preprint rounds
`2 - 0.1204 = 1.8796` to `1.87`)". -/
def Sec10_numbers : Prop :=
  1.8277 < 2 - epsStar5 ∧ 2 - epsStar5 < 1.8278 ∧ (2 : ℝ) - 0.1204 = 1.8796


/-! ## Part I: the tensor, the re-indexing maps and the squared run (Sections 3 to 6) -/

section PartIDefs

/-- Section 3: the left variables of the identity, `x₁, x₂, p₁, p₂`. Lean counts from 0, so the
paper's `x₁` is `XL.x 0` and its `p₂` is `XL.p 1`. In Section 5 these are the letters of an
`x`-string. -/
inductive XL : Type
  | x (i : Fin 2)
  | p (k : Fin 2)
  deriving DecidableEq, Fintype

/-- Section 3: the right variables `y₁, y₂, q`; the letters of a `y`-string. -/
inductive YL : Type
  | y (j : Fin 2)
  | q
  deriving DecidableEq, Fintype

/-- Section 3: the output variables `z₁₁, z₁₂, z₂₁, z₂₂, z₀`; the letters of a `z`-string. -/
inductive ZL : Type
  | z (i j : Fin 2)
  | z0
  deriving DecidableEq, Fintype

/-- Section 3: the five terms `P_ij` (`i, j ∈ {1,2}`) and `P₀`. -/
inductive Tm : Type
  | P (i j : Fin 2)
  | P0
  deriving DecidableEq, Fintype

/-- The coefficient of `p_k` in the entry `p̂_ij` of `p̂ = ((p₁, -p₂), (0, p₂))`. -/
def pHat : Fin 2 → Fin 2 → Fin 2 → ℤ
  | 0, 0, 0 => 1
  | 0, 1, 1 => -1
  | 1, 1, 1 => 1
  | _, _, _ => 0

/-- The coefficient of `q` in the entry `q̂_ij` of `q̂ = ((0, 0), (-q, q))`. -/
def qHat : Fin 2 → Fin 2 → ℤ
  | 1, 0 => -1
  | 1, 1 => 1
  | _, _ => 0

/-- Section 3: the left forms, `φ_{P_ij} = x_i + p̂_ij` and `φ_{P₀} = -(x₁ + x₂)`, as coefficient
vectors. -/
def phi : Tm → XL → ℤ
  | .P i _, .x i' => if i' = i then 1 else 0
  | .P i j, .p k => pHat i j k
  | .P0, .x _ => -1
  | .P0, .p _ => 0

/-- Section 3: the right forms, `ψ_{P_ij} = y_j + q̂_ij` and `ψ_{P₀} = y₁ + y₂`. -/
def psi : Tm → YL → ℤ
  | .P _ j, .y j' => if j' = j then 1 else 0
  | .P i j, .q => qHat i j
  | .P0, .y _ => 1
  | .P0, .q => 0

/-- Section 3: the output forms, `χ_{P_ij} = z_ij + z₀` and `χ_{P₀} = z₀`. -/
def chi : Tm → ZL → ℤ
  | .P i j, .z i' j' => if i' = i ∧ j' = j then 1 else 0
  | .P _ _, .z0 => 1
  | .P0, .z _ _ => 0
  | .P0, .z0 => 1

/-- The twelve variables of the identity, as the variables of a polynomial ring. -/
abbrev Var : Type := XL ⊕ YL ⊕ ZL

/-- Polynomials with integer coefficients in the twelve variables. -/
abbrev TriPoly : Type := MvPolynomial Var ℤ

/-- A left variable as a polynomial. -/
noncomputable def vX (s : XL) : TriPoly := MvPolynomial.X (Sum.inl s)
/-- A right variable as a polynomial. -/
noncomputable def vY (t : YL) : TriPoly := MvPolynomial.X (Sum.inr (Sum.inl t))
/-- An output variable as a polynomial. -/
noncomputable def vZ (z : ZL) : TriPoly := MvPolynomial.X (Sum.inr (Sum.inr z))

/-- The left linear form with coefficient vector `f`. -/
noncomputable def formX (f : XL → ℤ) : TriPoly := ∑ s, MvPolynomial.C (f s) * vX s
/-- The right linear form with coefficient vector `f`. -/
noncomputable def formY (f : YL → ℤ) : TriPoly := ∑ t, MvPolynomial.C (f t) * vY t
/-- The output linear form with coefficient vector `f`. -/
noncomputable def formZ (f : ZL → ℤ) : TriPoly := ∑ z, MvPolynomial.C (f z) * vZ z

/-- Section 3: `G := ∑_{i,j} x_i y_j z_ij + (p₁ y₁ + p₂ q) z₀`. -/
noncomputable def G : TriPoly :=
  ∑ i : Fin 2, ∑ j : Fin 2, vX (.x i) * vY (.y j) * vZ (.z i j)
    + (vX (.p 0) * vY (.y 0) + vX (.p 1) * vY .q) * vZ .z0

/-- Lemma 3.1, first form of `E`: `∑_{i,j} (x_i q̂_ij + p̂_ij y_j + p̂_ij q̂_ij) z_ij`. -/
noncomputable def E : TriPoly :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    (vX (.x i) * formY (fun t => if t = .q then qHat i j else 0)
      + formX (fun s => match s with | .p k => pHat i j k | .x _ => 0) * vY (.y j)
      + formX (fun s => match s with | .p k => pHat i j k | .x _ => 0)
          * formY (fun t => if t = .q then qHat i j else 0)) * vZ (.z i j)

/-- Lemma 3.1, second form of `E`:
`p₁y₁z₁₁ - p₂y₂z₁₂ + p₂y₂z₂₂ + p₂q z₂₂ - x₂q z₂₁ + x₂q z₂₂`. -/
noncomputable def Eexplicit : TriPoly :=
  vX (.p 0) * vY (.y 0) * vZ (.z 0 0) - vX (.p 1) * vY (.y 1) * vZ (.z 0 1)
    + vX (.p 1) * vY (.y 1) * vZ (.z 1 1) + vX (.p 1) * vY .q * vZ (.z 1 1)
    - vX (.x 1) * vY .q * vZ (.z 1 0) + vX (.x 1) * vY .q * vZ (.z 1 1)

/-- [ZT, eq. (3)] for this identity: `γ(s, t, z) := ∑_{λ contributing to z} φ_λ(s) ψ_λ(t)`, where
`λ` contributes to `z` if `χ_λ` contains `z`. Since every `χ_λ` has coefficients `0` and `1`, this
is the coefficient of `s t z` in `∑_λ φ_λ ψ_λ χ_λ = G + E`. -/
def gamma (s : XL) (t : YL) (z : ZL) : ℤ :=
  ∑ lam : Tm with chi lam z ≠ 0, phi lam s * psi lam t

/-- The monomials of `G`: `x_i y_j z_ij`, `p₁ y₁ z₀`, `p₂ q z₀`. -/
def IsGMonomial (s : XL) (t : YL) (z : ZL) : Prop :=
  (∃ i j : Fin 2, s = .x i ∧ t = .y j ∧ z = .z i j) ∨ (s = .p 0 ∧ t = .y 0 ∧ z = .z0) ∨
    (s = .p 1 ∧ t = .q ∧ z = .z0)

instance (s : XL) (t : YL) (z : ZL) : Decidable (IsGMonomial s t z) := by
  unfold IsGMonomial; infer_instance

/-- Remark 5.2: the weights of the left variables (`p₁` weight 2, `p₂` weight 1, `x_i` weight 0). -/
def wX : XL → ℕ
  | .p 0 => 2
  | .p 1 => 1
  | .x _ => 0

/-- Remark 5.2: the weights of the right variables (`q` weight 1, `y_j` weight 0). -/
def wY : YL → ℕ
  | .q => 1
  | .y _ => 0

/-- Remark 5.2: the weights of the outputs (`z_ij` weight 2, `z₀` weight 0). -/
def wZ : ZL → ℕ
  | .z _ _ => 2
  | .z0 => 0

/-! ### Section 4: re-indexing maps and good sets -/

/-- Section 4: `Γ[T] := ∑_{ℓ ∈ T} Γ_{·ℓ}`, the sum of the columns at `T`. -/
def colSum {r L : ℕ} (Γ : Matrix (Fin r) (Fin L) (ZMod 2)) (T : Finset (Fin L)) : Fin r → ZMod 2 :=
  ∑ ℓ ∈ T, fun i => Γ i ℓ

/-- Section 4: "A set `Q ⊆ [L]` of `m` levels is good if the columns of `Γ` at `Q` and the columns
of `Δ` at `[L] ∖ Q` are both bases." The columns at `Q` are `m` vectors of `F₂^m` and those at the
complement `L - m` vectors of `F₂^{L-m}`, so they are bases exactly if they are linearly
independent. -/
def Good {L m : ℕ} (Γ : Matrix (Fin m) (Fin L) (ZMod 2)) (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2))
    (Q : Finset (Fin L)) : Prop :=
  Q.card = m ∧ LinearIndependent (ZMod 2) (fun ℓ : Q => fun i => Γ i ℓ) ∧
    LinearIndependent (ZMod 2) (fun ℓ : (Qᶜ : Finset (Fin L)) => fun i => Δ i ℓ)

/-! ### Section 5: strings, arrays and the product of the runs -/

/-- An `x`-string: a string over `{x₁, x₂, p₁, p₂}`, of length `L`. -/
abbrev XStr (L : ℕ) : Type := Fin L → XL
/-- A `y`-string: a string over `{y₁, y₂, q}`. -/
abbrev YStr (L : ℕ) : Type := Fin L → YL
/-- A `z`-string: a string over the five output variables. -/
abbrev ZStr (L : ℕ) : Type := Fin L → ZL

/-- `Q(ξ)`: the levels where the `x`-string `ξ` has `p₁` or `p₂` (its inner set). -/
def QX {L : ℕ} (ξ : XStr L) : Finset (Fin L) := univ.filter fun ℓ => ∃ k, ξ ℓ = .p k
/-- `T(ξ)`: the levels where `ξ` has `p₂`. -/
def TX {L : ℕ} (ξ : XStr L) : Finset (Fin L) := univ.filter fun ℓ => ξ ℓ = .p 1
/-- `T(η)`: the levels where the `y`-string `η` has `q`. -/
def TY {L : ℕ} (η : YStr L) : Finset (Fin L) := univ.filter fun ℓ => η ℓ = .q
/-- `S(η)`: the levels where `η` has `y₂`. -/
def SY {L : ℕ} (η : YStr L) : Finset (Fin L) := univ.filter fun ℓ => η ℓ = .y 1
/-- `Q(ζ)`: the levels where the `z`-string `ζ` has `z₀`. -/
def QZ {L : ℕ} (ζ : ZStr L) : Finset (Fin L) := univ.filter fun ℓ => ζ ℓ = .z0
/-- `S(ζ)`: the levels where `ζ` has a letter `z_{i2}`. -/
def SZ {L : ℕ} (ζ : ZStr L) : Finset (Fin L) := univ.filter fun ℓ => ∃ i, ζ ℓ = .z i 1

/-- `ι(ξ)`: the index `i` of the letter `x_i` at every level outside the inner set; `0` at the
levels of the inner set.

NOTE. The paper takes `ι(ξ) ∈ {1,2}^{L-|Q(ξ)|}`, the indices in increasing order of the levels.
Here `ι(ξ)` is a function on all levels that is `0` on the inner set; restricted to the levels
outside `Q(ξ)` it is the paper's `ι(ξ)`, up to the order-preserving bijection between those levels
and `{1, …, L-|Q(ξ)|}`. Accordingly the rows of `X_Q` are indexed by `(Fin L → Fin 2) × F₂^{L-m}`,
of which the rows whose first component vanishes on `Q` are the paper's rows
(`Theorem_5_1_bijection`). -/
def iotaX {L : ℕ} (ξ : XStr L) : Fin L → Fin 2 := fun ℓ =>
  match ξ ℓ with
  | .x i => i
  | .p _ => 0

/-- `ι(ζ)`: the first index `i` of the letter `z_ij` at every level outside `Q(ζ)`; `0` on `Q(ζ)`
(NOTE at `iotaX`). -/
def iotaZ {L : ℕ} (ζ : ZStr L) : Fin L → Fin 2 := fun ℓ =>
  match ζ ℓ with
  | .z i _ => i
  | .z0 => 0

/-- A left string of the run, `u = u'u''`: an `x`-string (first half) and a `y`-string (second
half). -/
abbrev LeftStr (L : ℕ) : Type := XStr L × YStr L
/-- A right string `v = v'v''`: a `y`-string and an `x`-string. -/
abbrev RightStr (L : ℕ) : Type := YStr L × XStr L
/-- An output string `w = w'w''`: two `z`-strings. -/
abbrev OutStr (L : ℕ) : Type := ZStr L × ZStr L
/-- A leaf: a string of `2L` terms, `L` for each half. -/
abbrev Leaf (L : ℕ) : Type := (Fin L → Tm) × (Fin L → Tm)

/-- The rows of `X_Q`: `(ι, Δ-vector)` (NOTE at `iotaX`). -/
abbrev RowIdx (L m : ℕ) : Type := (Fin L → Fin 2) × (Fin (L - m) → ZMod 2)
/-- The columns of `X_Q`, which are the rows of `Y_Q`: `F₂^m × F₂^m`. -/
abbrev InIdx (m : ℕ) : Type := (Fin m → ZMod 2) × (Fin m → ZMod 2)
/-- The columns of `Y_Q`: `(Δ-vector, ι)`. -/
abbrev ColIdx (L m : ℕ) : Type := (Fin (L - m) → ZMod 2) × (Fin L → Fin 2)

/-- Section 5, the input array `a_s` of run `s`:
`a_s[u'u''] := X_{Q(u')}[(ι(u'), Δ[S(u'')]), (Γ[T(u')], Γ[T(u'')])]` if `Q(u') ∈ 𝒢` and
`|T(u'')| - |T(u')| = s`, and `0` otherwise. -/
def arrayA {L m : ℕ} (Γ : Matrix (Fin m) (Fin L) (ZMod 2)) (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2))
    (𝒢 : Finset (Finset (Fin L))) (X : Finset (Fin L) → Matrix (RowIdx L m) (InIdx m) ℤ) (s : ℤ) :
    LeftStr L → ℤ := fun u =>
  if QX u.1 ∈ 𝒢 ∧ ((TY u.2).card : ℤ) - (TX u.1).card = s then
    X (QX u.1) (iotaX u.1, colSum Δ (SY u.2)) (colSum Γ (TX u.1), colSum Γ (TY u.2))
  else 0

/-- Section 5, the input array `b_s` of run `s`:
`b_s[v'v''] := Y_{Q(v'')}[(Γ[T(v')], Γ[T(v'')]), (Δ[S(v')], ι(v''))]` if `Q(v'') ∈ 𝒢` and
`|T(v'')| - |T(v')| = s`, and `0` otherwise. -/
def arrayB {L m : ℕ} (Γ : Matrix (Fin m) (Fin L) (ZMod 2)) (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2))
    (𝒢 : Finset (Finset (Fin L))) (Y : Finset (Fin L) → Matrix (InIdx m) (ColIdx L m) ℤ) (s : ℤ) :
    RightStr L → ℤ := fun v =>
  if QX v.2 ∈ 𝒢 ∧ ((TX v.2).card : ℤ) - (TY v.1).card = s then
    Y (QX v.2) (colSum Γ (TY v.1), colSum Γ (TX v.2)) (colSum Δ (SY v.1), iotaX v.2)
  else 0

/-- [ZT, Section 2.3.2] with the identity of level `ℓ`: `Φ_τ(a) := ∑_u a[u] ∏_ℓ φ^{(ℓ)}_{τ_ℓ}(u_ℓ)`,
where the left form at a level of the first half is `φ` and at a level of the second half is `ψ`
(Section 5, "Per-level identities": left and right exchanged). -/
def PhiL {L : ℕ} (τ : Leaf L) (a : LeftStr L → ℤ) : ℤ :=
  ∑ u, a u * (∏ ℓ, phi (τ.1 ℓ) (u.1 ℓ)) * ∏ ℓ, psi (τ.2 ℓ) (u.2 ℓ)

/-- `Ψ_τ(b) := ∑_v b[v] ∏_ℓ ψ^{(ℓ)}_{τ_ℓ}(v_ℓ)`: `ψ` in the first half, `φ` in the second. -/
def PsiR {L : ℕ} (τ : Leaf L) (b : RightStr L → ℤ) : ℤ :=
  ∑ v, b v * (∏ ℓ, psi (τ.1 ℓ) (v.1 ℓ)) * ∏ ℓ, phi (τ.2 ℓ) (v.2 ℓ)

/-- "A leaf contributes to an output string `w` if `χ_{τ_ℓ}` contains `w_ℓ` at every level"; the
output forms are the same at all `2L` levels. -/
def Contributes {L : ℕ} (τ : Leaf L) (w : OutStr L) : Prop :=
  ∀ ℓ, chi (τ.1 ℓ) (w.1 ℓ) ≠ 0 ∧ chi (τ.2 ℓ) (w.2 ℓ) ≠ 0

instance {L : ℕ} (τ : Leaf L) (w : OutStr L) : Decidable (Contributes τ w) := by
  unfold Contributes; infer_instance

/-- [ZT, eq. (2)] on the `2L` levels: `Mult(a, b)[w] := ∑_{τ contributing to w} Φ_τ(a) Ψ_τ(b)`.

NOTE. [ZT] defines `Mult` by eq. (2) and proves in its Lemma 7 that the recursion `Full` returns
it; Section 5 says that Lemmas 7 and 8 with their proofs hold when the identity depends on the
level. Here `Mult` is eq. (2) with the per-level forms. Lemma 8 in this setting is proved
(`Lemma_8_squared`), and so is Lemma 7: the recursion `FullSq.run` on the `2L` levels returns
`Mult` and multiplies `Φ_τ(a)` by `Ψ_τ(b)` at the leaf `τ` (`Lemma_7_squared`). -/
def Mult {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (w : OutStr L) : ℤ :=
  ∑ τ : Leaf L with Contributes τ w, PhiL τ a * PsiR τ b

end PartIDefs

/-- The coefficient of the monomial `s t z` in `G + E` (Section 3, read off the displays of `G` and
of the second form of `E` in Lemma 3.1). -/
def gEcoef : XL → YL → ZL → ℤ
  | .x i, .y j, .z i' j' => if i = i' ∧ j = j' then 1 else 0
  | .p 0, .y 0, .z0 => 1
  | .p 1, .q, .z0 => 1
  | .p 0, .y 0, .z 0 0 => 1
  | .p 1, .y 1, .z 0 1 => -1
  | .p 1, .y 1, .z 1 1 => 1
  | .p 1, .q, .z 1 1 => 1
  | .x 1, .q, .z 1 0 => -1
  | .x 1, .q, .z 1 1 => 1
  | _, _, _ => 0

/-- Section 5: the number of symbols `P₀` of a string of terms. -/
def numP0 {L : ℕ} (τ : Fin L → Tm) : ℕ := (univ.filter fun ℓ => τ ℓ = .P0).card

/-- Section 6: "the order of a leaf is `2m` minus its number of `P₀`'s". -/
def order {L : ℕ} (m : ℕ) (τ : Leaf L) : ℤ := 2 * (m : ℤ) - (numP0 τ.1 + numP0 τ.2 : ℕ)

/-- Lemma 6.1(a): `α'_d := binom(2m, d) 4^d`. -/
def alpha' (m d : ℕ) : ℕ := (2 * m).choose d * 4 ^ d

/-- Section 6: `β_e := binom(L, m-e) 4^{L-m+e}`. -/
def beta (L m e : ℕ) : ℕ := L.choose (m - e) * 4 ^ (L - m + e)

/-- Lemma 6.1(b): `β'_d := ∑_{d₁+d₂=d, 0 ≤ d₁,d₂ ≤ m} β_{d₁} β_{d₂}`. -/
def beta' (L m d : ℕ) : ℕ :=
  ∑ p ∈ (antidiagonal d).filter (fun p : ℕ × ℕ => p.1 ≤ m ∧ p.2 ≤ m), beta L m p.1 * beta L m p.2

/-- [ZT, Section 2.4.3]: `Leaves(U)`, the leaves that contribute to some output string of `U`. -/
def Leaves {L : ℕ} (U : Finset (OutStr L)) : Finset (Leaf L) :=
  univ.filter fun τ => ∃ w ∈ U, Contributes τ w

/-! ### Section 3: the identity -/

/-- **Lemma 3.1**. "Summing over the five terms, `∑_λ φ_λ ψ_λ χ_λ = G + E`, where
`E := ∑_{i,j} (x_i q̂_ij + p̂_ij y_j + p̂_ij q̂_ij) z_ij = p₁y₁z₁₁ - p₂y₂z₁₂ + p₂y₂z₂₂ + p₂q z₂₂ -
x₂q z₂₁ + x₂q z₂₂`." An identity of polynomials with integer coefficients. -/
def Lemma_3_1 : Prop :=
  (∑ lam, formX (phi lam) * formY (psi lam) * formZ (chi lam)) = G + E ∧ E = Eexplicit

/-- Section 3 and Remark 5.2: `γ(s, t, z)` is the coefficient of the monomial `s t z` in `G + E`:
`G + E = ∑ γ(s,t,z) s t z`. -/
def Sec3_gamma_coeff : Prop :=
  G + E = ∑ s, ∑ t, ∑ z, MvPolynomial.C (gEcoef s t z) * vX s * vY t * vZ z ∧
    ∀ s t z, gamma s t z = gEcoef s t z

/-- Section 3, Coppersmith's construction as printed [Cop82, p. 467]: "`(a₁₁+x²a₁₂)(b₂₁+x²b₁₁)c₁₁ +
(a₁₁+x²a₁₃) b₃₁ (c₁₁-xc₂₁) + (a₁₁+x²a₂₂)(b₂₁-xb₁₂) c₁₂ + (a₁₁+x²a₂₃)(b₃₁+xb₁₂)(c₁₂+xc₂₁) -
a₁₁(b₂₁+b₃₁)(c₁₁+c₁₂) = x²(a₁₁b₁₁c₁₁ + a₁₁b₁₂c₂₁ + a₁₂b₂₁c₁₁ + a₁₃b₃₁c₁₁ + a₂₂b₂₁c₁₂ +
a₂₃b₃₁c₁₂) + x³P(a,b,c,x)`", with the polynomial `P` written out. -/
def Sec3_coppersmith : Prop :=
  ∀ {R : Type} [CommRing R] (a11 a12 a13 a22 a23 b11 b12 b21 b31 c11 c12 c21 x : R),
    (a11 + x ^ 2 * a12) * (b21 + x ^ 2 * b11) * c11 + (a11 + x ^ 2 * a13) * b31 * (c11 - x * c21)
      + (a11 + x ^ 2 * a22) * (b21 - x * b12) * c12
      + (a11 + x ^ 2 * a23) * (b31 + x * b12) * (c12 + x * c21) - a11 * (b21 + b31) * (c11 + c12)
    = x ^ 2 * (a11 * b11 * c11 + a11 * b12 * c21 + a12 * b21 * c11 + a13 * b31 * c11
        + a22 * b21 * c12 + a23 * b31 * c12)
      + x ^ 3 * (-(a22 * b12 * c12) + a23 * b12 * c12 - a13 * b31 * c21 + a23 * b31 * c21
        + x * (a12 * b11 * c11 + a23 * b12 * c21))

/-- Section 3: Lemma 3.1's forms "are Coppersmith's five terms at `x = 1`, in the order `P₁₁`,
`P₂₁`, `P₁₂`, `P₂₂`, `P₀`", with the renaming `x₁ := b₂₁`, `x₂ := b₃₁`, `p₁ := b₁₁`,
`p₂ := b₁₂`, `y₁ := c₁₁`, `y₂ := c₁₂`, `q := c₂₁`, `z₁₁ := a₁₂`, `z₂₁ := a₁₃`, `z₁₂ := a₂₂`,
`z₂₂ := a₂₃`, `z₀ := a₁₁`: `φ_λ ψ_λ χ_λ`, evaluated at these values, is the `λ`-th printed term
at `x = 1`. -/
def Sec3_coppersmith_terms : Prop :=
  ∀ {R : Type} [CommRing R] (a11 a12 a13 a22 a23 b11 b12 b21 b31 c11 c12 c21 : R),
    let sX : XL → R := fun s => match s with
      | .x i => ![b21, b31] i
      | .p k => ![b11, b12] k
    let sY : YL → R := fun t => match t with
      | .y j => ![c11, c12] j
      | .q => c21
    let sZ : ZL → R := fun z => match z with
      | .z i j => ![![a12, a22], ![a13, a23]] i j
      | .z0 => a11
    let term : Tm → R := fun lam => (∑ s, (phi lam s : R) * sX s) * (∑ t, (psi lam t : R) * sY t)
      * (∑ z, (chi lam z : R) * sZ z)
    term (.P 0 0) = (a11 + a12) * (b21 + b11) * c11 ∧
    term (.P 1 0) = (a11 + a13) * b31 * (c11 - c21) ∧
    term (.P 0 1) = (a11 + a22) * (b21 - b12) * c12 ∧
    term (.P 1 1) = (a11 + a23) * (b31 + b12) * (c12 + c21) ∧
    term .P0 = -(a11 * (b21 + b31) * (c11 + c12))

/-- Remark 5.2: "Every monomial of `G` has weight 2 and every monomial of `E` weight 3 or 4", and
the monomials of `G` have coefficient 1. -/
def Remark_5_2_weights : Prop :=
  ∀ s t z, gamma s t z ≠ 0 →
    (IsGMonomial s t z → gamma s t z = 1 ∧ wX s + wY t + wZ z = 2) ∧
    (¬ IsGMonomial s t z → wX s + wY t + wZ z = 3 ∨ wX s + wY t + wZ z = 4)


/-- Remark 5.2, the string weights: "In run `s` every nonzero left string has weight `2m+s`, every
nonzero right string weight `2m-s`, and every read output string weight `4(L-m)`; the total `4L`
forces weight 2 at every level." An `x`-string with `m` letters `p` weighs `2m - |T|`, a `y`-string
weighs `|T|`, a `z`-string with `m` letters `z₀` weighs `2(L-m)`; so in run `s`
(`|T(u'')| - |T(u')| = s = |T(v'')| - |T(v')|`) the left string `u'u''` weighs `2m+s`, the right
string `v'v''` weighs `2m-s`, and `w'w''` weighs `4(L-m)`; and `2L` level weights of at least 2
summing to `4L` are all 2. -/
def Remark_5_2_strings : Prop :=
  (∀ {L : ℕ} (ξ : XStr L), ∑ ℓ, wX (ξ ℓ) + (TX ξ).card = 2 * (QX ξ).card) ∧
  (∀ {L : ℕ} (η : YStr L), ∑ ℓ, wY (η ℓ) = (TY η).card) ∧
  (∀ {L : ℕ} (ζ : ZStr L), ∑ ℓ, wZ (ζ ℓ) + 2 * (QZ ζ).card = 2 * L) ∧
  (∀ {L m : ℕ} (s : ℤ) (u : LeftStr L) (v : RightStr L) (w : OutStr L),
    (QX u.1).card = m → (QX v.2).card = m → (QZ w.1).card = m → (QZ w.2).card = m →
    ((TY u.2).card : ℤ) - (TX u.1).card = s → ((TX v.2).card : ℤ) - (TY v.1).card = s →
    ((∑ ℓ, wX (u.1 ℓ) + ∑ ℓ, wY (u.2 ℓ) : ℕ) : ℤ) = 2 * m + s ∧
    ((∑ ℓ, wY (v.1 ℓ) + ∑ ℓ, wX (v.2 ℓ) : ℕ) : ℤ) = 2 * m - s ∧
    ∑ ℓ, wZ (w.1 ℓ) + ∑ ℓ, wZ (w.2 ℓ) = 4 * (L - m)) ∧
  (∀ {N : ℕ} (f : Fin N → ℕ), (∀ ℓ, 2 ≤ f ℓ) → ∑ ℓ, f ℓ = 2 * N → ∀ ℓ, f ℓ = 2)

/-! ### Section 4 -/

/-- Section 4: "Then `T ↦ Γ[T]` is a bijection from the subsets of `Q` onto `F₂^m`, and
`S ↦ Δ[S]` a bijection from the subsets of `[L] ∖ Q` onto `F₂^{L-m}`". -/
def Sec4_bijections : Prop :=
  ∀ {L m : ℕ} (Γ : Matrix (Fin m) (Fin L) (ZMod 2)) (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2))
    (Q : Finset (Fin L)), Good Γ Δ Q →
    Set.BijOn (colSum Γ) (Q.powerset : Set (Finset (Fin L))) Set.univ ∧
      Set.BijOn (colSum Δ) ((Qᶜ).powerset : Set (Finset (Fin L))) Set.univ

open scoped Classical in
/-- **Lemma 4.1**, the existence part: "There are a `Γ`-map and a `Δ`-map with at least
`μ_m μ_{L-m} binom(L, m) ≥ μ_∞² binom(L, m)` good sets."

NOTE. The second half of the lemma, that a deterministic algorithm finds them in
`binom(L,m)(2^m + 2^{L-m}) L^{O(1)}` operations (the method of conditional expectations), is about
an algorithm and its running time and is not stated. The existence is proved by averaging. -/
def Lemma_4_1 : Prop :=
  ∀ L m : ℕ, 1 ≤ m → m < L →
    ∃ (Γ : Matrix (Fin m) (Fin L) (ZMod 2)) (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2)),
      mu m * mu (L - m) * (L.choose m : ℝ) ≤ ((univ.powersetCard m).filter (Good Γ Δ)).card ∧
        muInf ^ 2 * (L.choose m : ℝ) ≤ mu m * mu (L - m) * (L.choose m : ℝ)

/-! ### Lemma 4.1: the method of conditional expectations

"Fix the columns of `Γ` one level at a time. When the columns at the levels `1, …, ℓ` are fixed
and `r` of them lie in `Q`, the columns of `Γ` at `Q` are a basis with conditional probability
`μ_{m-r}` if these `r` fixed columns are linearly independent, and `0` otherwise […]. Choosing at
each level the column, among the `2^m` values, that maximises it never decreases it, so the final
`Γ` is invertible at at least `μ_m binom(L, m)` sets. Then fix `Δ` in the same way, maximising the
sum of `Pr[Δ invertible at [L] ∖ Q]` over the sets `Q` at which `Γ` is invertible." Here the
columns of a `k × L` matrix are a function `Fin L → F₂^k`, a conditional probability is a number of
completions divided by `2^{k · #free levels}`, and the conditional expectation (times
`2^{k · #free levels}`) is `condCount`. The operation count is not formalized (running time). -/

/-- The completions of the columns `c` fixed at the levels `F`: the column assignments `d` that
agree with `c` on `F` and whose columns at `S` are linearly independent. -/
noncomputable def completions {k L : ℕ} (S F : Finset (Fin L)) (c : Fin L → Fin k → ZMod 2) : ℕ :=
  open Classical in
  (univ.filter fun d : Fin L → Fin k → ZMod 2 =>
    (∀ ℓ ∈ F, d ℓ = c ℓ) ∧ LinearIndependent (ZMod 2) (fun ℓ : S => d ℓ)).card

/-- The conditional expectation of the number of sets of `𝒮` at which the columns are a basis,
times `2^{k · #free levels}`. -/
noncomputable def condCount {k L : ℕ} (𝒮 : Finset (Finset (Fin L))) (F : Finset (Fin L))
    (c : Fin L → Fin k → ZMod 2) : ℕ :=
  ∑ S ∈ 𝒮, completions S F c

/-- The levels below `j` (`1, …, j` in the paper's numbering). -/
def below {L : ℕ} (j : ℕ) : Finset (Fin L) := univ.filter fun ℓ => (ℓ : ℕ) < j

/-- A matrix chosen greedily for the family `𝒮`: at every level its column maximises the
conditional expectation given its columns at the levels below ("ties arbitrarily"). -/
def IsGreedyMap {k L : ℕ} (𝒮 : Finset (Finset (Fin L))) (M : Matrix (Fin k) (Fin L) (ZMod 2)) :
    Prop :=
  ∀ ℓ : Fin L, ∀ v : Fin k → ZMod 2,
    condCount 𝒮 (below ((ℓ : ℕ) + 1)) (Function.update (fun ℓ' i => M i ℓ') ℓ v)
      ≤ condCount 𝒮 (below ((ℓ : ℕ) + 1)) (fun ℓ' i => M i ℓ')

open scoped Classical in
/-- **Lemma 4.1**, the conditional probability: with the columns fixed at the levels `F`, of
which `r` lie in `S` (`|S| = k`), "the columns at `S` are a basis with conditional probability
`μ_{k-r}` if these `r` fixed columns are linearly independent, and `0` otherwise". -/
def Lemma_4_1_condprob : Prop :=
  ∀ {k L : ℕ} (S F : Finset (Fin L)) (c : Fin L → Fin k → ZMod 2), S.card = k →
    (completions S F c : ℝ) / 2 ^ (k * Fᶜ.card)
      = if LinearIndependent (ZMod 2) (fun ℓ : (S ∩ F : Finset (Fin L)) => c ℓ)
        then mu (k - (S ∩ F).card) else 0

/-- **Lemma 4.1**, the averaging step: the conditional expectation is the sum over the `2^k`
values of the next column (so its maximum is at least the average). -/
def Lemma_4_1_mean : Prop :=
  ∀ {k L : ℕ} (𝒮 : Finset (Finset (Fin L))) (F : Finset (Fin L)) (c : Fin L → Fin k → ZMod 2)
    (x : Fin L), x ∉ F →
    condCount 𝒮 F c = ∑ v : Fin k → ZMod 2, condCount 𝒮 (insert x F) (Function.update c x v)

open scoped Classical in
/-- **Lemma 4.1**, one map: for a family `𝒮` of sets of `k` levels, a greedy matrix exists, and
every greedy matrix has linearly independent columns at at least `μ_k |𝒮|` sets of `𝒮`. -/
def Lemma_4_1_greedy : Prop :=
  ∀ {k L : ℕ} (𝒮 : Finset (Finset (Fin L))), (∀ S ∈ 𝒮, S.card = k) →
    (∃ M : Matrix (Fin k) (Fin L) (ZMod 2), IsGreedyMap 𝒮 M) ∧
    ∀ M : Matrix (Fin k) (Fin L) (ZMod 2), IsGreedyMap 𝒮 M →
      mu k * 𝒮.card
        ≤ (𝒮.filter fun S : Finset (Fin L) =>
          LinearIndependent (ZMod 2) (fun ℓ : S => fun i => M i ℓ.1)).card

open scoped Classical in
/-- **Lemma 4.1**, the deterministic construction: `Γ` greedy for all sets of `m` levels, then
`Δ` greedy for the complements of the sets at which `Γ` is invertible; both exist, and every such
pair has at least `μ_m μ_{L-m} binom(L, m)` good sets. -/
def Lemma_4_1_derand : Prop :=
  ∀ L m : ℕ, m ≤ L →
    (∃ Γ : Matrix (Fin m) (Fin L) (ZMod 2), IsGreedyMap (univ.powersetCard m) Γ) ∧
    ∀ Γ : Matrix (Fin m) (Fin L) (ZMod 2), IsGreedyMap (univ.powersetCard m) Γ →
      let 𝒮Δ := ((univ.powersetCard m).filter fun Q : Finset (Fin L) =>
        LinearIndependent (ZMod 2) (fun ℓ : Q => fun i => Γ i ℓ)).image compl
      (∃ Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2), IsGreedyMap 𝒮Δ Δ) ∧
      ∀ Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2), IsGreedyMap 𝒮Δ Δ →
        mu m * mu (L - m) * (L.choose m : ℝ) ≤ ((univ.powersetCard m).filter (Good Γ Δ)).card

/-! ### Section 5: the squared run -/

/-- [ZT, Lemma 8] for the squared run, whose identity depends on the level ("By [ZT, Lemma 8],
`Mult(a_s, b_s)[w]` is the sum over left strings `u` and right strings `v` of
`∏_ℓ γ_ℓ(u_ℓ, v_ℓ, w_ℓ) a_s[u] b_s[v]`"; at a level of the second half the left letter is a
`y`-letter, and `γ_ℓ(u_ℓ, v_ℓ, w_ℓ)` is `γ(v_ℓ, u_ℓ, w_ℓ)`, left and right exchanged). -/
def Lemma_8_squared : Prop :=
  ∀ {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ) (w : OutStr L),
    Mult a b w = ∑ u, ∑ v, (∏ ℓ, gamma (u.1 ℓ) (v.1 ℓ) (w.1 ℓ)) * (∏ ℓ, gamma (v.2 ℓ) (u.2 ℓ) (w.2 ℓ))
      * a u * b v

/-- **Theorem 5.1**, the identity. "For every output string `w = w'w''` with `Q(w'), Q(w'') ∈ 𝒢`,
`∑_{s=-m}^{m} Mult(a_s, b_s)[w] = (X_{Q(w')} Y_{Q(w'')})[(ι(w'), Δ[S(w'')]), (Δ[S(w')], ι(w''))]`."
Here `𝒢` is any family of good sets, and the `X_Q`, `Y_Q` are arbitrary. -/
def Theorem_5_1 : Prop :=
  ∀ {L m : ℕ} (Γ : Matrix (Fin m) (Fin L) (ZMod 2)) (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2))
    (𝒢 : Finset (Finset (Fin L))), (∀ Q ∈ 𝒢, Good Γ Δ Q) →
  ∀ (X : Finset (Fin L) → Matrix (RowIdx L m) (InIdx m) ℤ)
    (Y : Finset (Fin L) → Matrix (InIdx m) (ColIdx L m) ℤ) (w : OutStr L),
    QZ w.1 ∈ 𝒢 → QZ w.2 ∈ 𝒢 →
    ∑ s ∈ Finset.Icc (-(m : ℤ)) m, Mult (arrayA Γ Δ 𝒢 X s) (arrayB Γ Δ 𝒢 Y s) w
      = (X (QZ w.1) * Y (QZ w.2)) (iotaZ w.1, colSum Δ (SZ w.2)) (colSum Δ (SZ w.1), iotaZ w.2)

/-- **Theorem 5.1**, the bijection. "For fixed `Q_k, Q_{k'} ∈ 𝒢` the map from the output strings
`w` with `Q(w') = Q_k`, `Q(w'') = Q_{k'}` to the positions on the right is a bijection onto the
`N₀²` entries of `X_{Q_k} Y_{Q_{k'}}`." The entries are the positions whose `ι`-components vanish on
the inner sets (NOTE at `iotaX`); there are `N₀²` of them. -/
def Theorem_5_1_bijection : Prop :=
  ∀ {L m : ℕ} (Γ : Matrix (Fin m) (Fin L) (ZMod 2)) (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2))
    (Q' Q'' : Finset (Fin L)), Good Γ Δ Q' → Good Γ Δ Q'' →
    Set.BijOn (fun w : OutStr L => ((iotaZ w.1, colSum Δ (SZ w.2)), (colSum Δ (SZ w.1), iotaZ w.2)))
      {w | QZ w.1 = Q' ∧ QZ w.2 = Q''}
      {p : RowIdx L m × ColIdx L m | (∀ ℓ ∈ Q', p.1.1 ℓ = 0) ∧ (∀ ℓ ∈ Q'', p.2.2 ℓ = 0)} ∧
    (Finset.univ.filter (fun p : RowIdx L m × ColIdx L m =>
        (∀ ℓ ∈ Q', p.1.1 ℓ = 0) ∧ (∀ ℓ ∈ Q'', p.2.2 ℓ = 0))).card = N0 L m ^ 2

/-- The example after Theorem 5.1 (`L = 3`, `m = 1`, levels and indices counted from 0 in Lean):
"take `Γ = (1 1 1)` and `Δ = ((0 1 1), (1 0 1))`, for which all three sets `{1}, {2}, {3}` are
good. The output string `w` with `w' = z₂₁z₀z₁₂` and `w'' = z₀z₁₁z₂₂` has `Q(w') = {2}`,
`ι(w') = (2,1)`, `S(w') = {3}` and `Q(w'') = {1}`, `ι(w'') = (1,2)`, `S(w'') = {3}`. … the row
`((2,1),(1,1))` and the column `((1,1),(1,2))`"; the summand with `T' = {2}`, `T'' = {1}` has
`u = x₂p₂x₁ qy₁y₂`, `v = y₁qy₂ p₂x₁x₂`, lies in run `0`, has the coefficient `1` and the inner
index `((1),(1))`; the other three summands lie in the runs `0`, `1`, `-1`. -/
def Sec5_example : Prop :=
  let Γ : Matrix (Fin 1) (Fin 3) (ZMod 2) := !![1, 1, 1]
  let Δ : Matrix (Fin (3 - 1)) (Fin 3) (ZMod 2) := !![0, 1, 1; 1, 0, 1]
  let w : OutStr 3 := (![.z 1 0, .z0, .z 0 1], ![.z0, .z 0 0, .z 1 1])
  let run : LeftStr 3 → RightStr 3 → ℤ × ℤ := fun u v =>
    (((TY u.2).card : ℤ) - (TX u.1).card, ((TX v.2).card : ℤ) - (TY v.1).card)
  let coef : LeftStr 3 → RightStr 3 → ℤ := fun u v =>
    (∏ ℓ, gamma (u.1 ℓ) (v.1 ℓ) (w.1 ℓ)) * ∏ ℓ, gamma (v.2 ℓ) (u.2 ℓ) (w.2 ℓ)
  (Good Γ Δ {0} ∧ Good Γ Δ {1} ∧ Good Γ Δ {2}) ∧
  QZ w.1 = {1} ∧ iotaZ w.1 = ![1, 0, 0] ∧ SZ w.1 = {2} ∧
  QZ w.2 = {0} ∧ iotaZ w.2 = ![0, 0, 1] ∧ SZ w.2 = {2} ∧
  colSum Δ (SZ w.2) = ![1, 1] ∧ colSum Δ (SZ w.1) = ![1, 1] ∧
  (let u : LeftStr 3 := (![.x 1, .p 1, .x 0], ![.q, .y 0, .y 1])
   let v : RightStr 3 := (![.y 0, .q, .y 1], ![.p 1, .x 0, .x 1])
   run u v = (0, 0) ∧ coef u v = 1 ∧ (colSum Γ (TX u.1), colSum Γ (TY u.2)) = (![1], ![1])) ∧
  (let u : LeftStr 3 := (![.x 1, .p 0, .x 0], ![.y 0, .y 0, .y 1])
   let v : RightStr 3 := (![.y 0, .y 0, .y 1], ![.p 0, .x 0, .x 1])
   run u v = (0, 0) ∧ coef u v = 1 ∧ (colSum Γ (TX u.1), colSum Γ (TY u.2)) = (![0], ![0])) ∧
  (let u : LeftStr 3 := (![.x 1, .p 0, .x 0], ![.q, .y 0, .y 1])
   let v : RightStr 3 := (![.y 0, .y 0, .y 1], ![.p 1, .x 0, .x 1])
   run u v = (1, 1) ∧ coef u v = 1) ∧
  (let u : LeftStr 3 := (![.x 1, .p 1, .x 0], ![.y 0, .y 0, .y 1])
   let v : RightStr 3 := (![.y 0, .q, .y 1], ![.p 0, .x 0, .x 1])
   run u v = (-1, -1) ∧ coef u v = 1)

/-! ### Section 6: leaves -/

/-- **Lemma 6.1(a)**. "For every read output string `w` and every `0 ≤ d ≤ 2m`, exactly
`α'_d := binom(2m, d) 4^d` leaves of order `d` contribute to `w`." -/
def Lemma_6_1_a : Prop :=
  ∀ {L m : ℕ} (w : OutStr L), (QZ w.1).card = m → (QZ w.2).card = m → ∀ d : ℕ,
    (univ.filter fun τ : Leaf L => Contributes τ w ∧ order m τ = d).card = alpha' m d

/-- **Lemma 6.1(b)**, the count. "The leaves with at most `m` symbols `P₀` in each half and order
`d` number `β'_d`." -/
def Lemma_6_1_b_count : Prop :=
  ∀ {L m : ℕ}, m ≤ L → ∀ d : ℕ,
    (univ.filter fun τ : Leaf L => numP0 τ.1 ≤ m ∧ numP0 τ.2 ≤ m ∧ order m τ = d).card
      = beta' L m d

/-- **Lemma 6.1(b)**, the bound. "`β'_d ≤ (d+1) ρ^d β₀² ≤ (d+1) ρ^d M/μ_∞⁴`", with `β₀ = K N₀`,
`M = K_g² N₀²` and `K_g ≥ μ_∞² K` (and, from the proof, `β_e ≤ ρ^e β₀`). -/
def Lemma_6_1_b_bound : Prop :=
  ∀ {L m : ℕ}, 1 ≤ m → m ≤ L →
    beta L m 0 = K L m * N0 L m ∧
    (∀ e : ℕ, e ≤ m → (beta L m e : ℝ) ≤ rho L m ^ e * beta L m 0) ∧
    (∀ d : ℕ, (beta' L m d : ℝ) ≤ (d + 1) * rho L m ^ d * (beta L m 0 : ℝ) ^ 2) ∧
    ∀ Kg : ℝ, muInf ^ 2 * K L m ≤ Kg →
      (beta L m 0 : ℝ) ^ 2 ≤ Kg ^ 2 * (N0 L m : ℝ) ^ 2 / muInf ^ 4

/-- **Lemma 6.1(c)**. "For every set `U` of read output strings,
`|Leaves(U)| ≤ ∑_{d=0}^{2m} min{|U| α'_d, β'_d}`." -/
def Lemma_6_1_c : Prop :=
  ∀ {L m : ℕ}, m ≤ L → ∀ U : Finset (OutStr L), (∀ w ∈ U, (QZ w.1).card = m ∧ (QZ w.2).card = m) →
    (Leaves U).card ≤ ∑ d ∈ range (2 * m + 1), min (U.card * alpha' m d) (beta' L m d)

/-! ### Section 7: the counts of Theorem 7.2 -/

/-- Proof of Theorem 7.2, the boxes of a tile: with `L ≥ 5m`, "`ρ < 1`" and "at most
`(2m+1) ∑_{d ≥ t} β'_d ≤ (2m+1)² ρ^t M/(μ_∞⁴ (1-ρ))` per tile", where `M = K_g² N₀²` and
`K_g ≥ μ_∞² K`. -/
def Theorem_7_2_boxes : Prop :=
  ∀ L m t : ℕ, 1 ≤ m → 5 * m ≤ L → ∀ Kg : ℝ, muInf ^ 2 * K L m ≤ Kg →
    rho L m < 1 ∧
    ((2 * m + 1 : ℕ) : ℝ) * (∑ d ∈ Icc t (2 * m), (beta' L m d : ℝ))
      ≤ ((2 * m + 1 : ℕ) : ℝ) ^ 2 * (rho L m ^ t / (1 - rho L m)) * (Kg ^ 2 * (N0 L m : ℝ) ^ 2)
          / muInf ^ 4

/-- Proof of Theorem 7.2, the tiles and bands: "we first pad `N` to a multiple of `K_g N₀`, which
at most doubles it when `N ≥ K_g N₀`"; so there are at most `4N²/M` tiles (`M = K_g² N₀²`) and at
most `4N/(K_g N₀)` bands (left and right). -/
def Theorem_7_2_tiles : Prop :=
  ∀ N B : ℕ, 0 < B → B ≤ N →
    (⌈(N : ℝ) / B⌉₊ * B : ℝ) ≤ 2 * N ∧
    ((⌈(N : ℝ) / B⌉₊ : ℝ)) ^ 2 ≤ 4 * (N : ℝ) ^ 2 / (B : ℝ) ^ 2 ∧
    2 * (⌈(N : ℝ) / B⌉₊ : ℝ) ≤ 4 * N / B

/-- Proof of Theorem 7.2, the re-indexing maps: "`K(2^m + 2^{L-m}) L^{O(1)} ≤ N L^{O(1)}` since
`K 2^{L-m} ≤ K N₀ ≤ N`", and "`N ≥ N₀ = 4^{L-m} ≥ 2^L` gives `L ≤ log₂ N`" (for `L ≥ 2m`). -/
def Theorem_7_2_hash_cost : Prop :=
  ∀ L m N : ℕ, 2 * m ≤ L → K L m * N0 L m ≤ N →
    K L m * (2 ^ m + 2 ^ (L - m)) ≤ 2 * N ∧ 2 ^ L ≤ N0 L m ∧ (N0 L m ≤ N → 2 ^ L ≤ N)

/-- Section 7, change (7), word size: "since `N ≥ N₀ = 4^{L-m} ≥ 4^{4L/5}` we have
`25^L ≤ N^{2.91}`" (for `L ≥ 5m`), and Section 5: "at most `binom(L,m) 2^L 3^L ≤ 12^L` nonzero
entries". -/
def Sec7_word_size : Prop :=
  (∀ L m : ℕ, 5 * m ≤ L → ∀ N : ℝ, (4 : ℝ) ^ (L - m) ≤ N → (25 : ℝ) ^ L ≤ N ^ (2.91 : ℝ)) ∧
  (∀ L m : ℕ, L.choose m * 2 ^ L * 3 ^ L ≤ 12 ^ L)

/-- Section 5, "Encodings per band": "in the first half a left array has at most `4^{L-k} 3^L`
entries per vertex at depth `k`, and `∑_k 5^k 4^{L-k} 3^L = O(15^L)`; in the second half
`∑_k 5^{L+k} 3^{L-k} = O(25^L)`": `∑ ≤ 5·15^L` and `∑ ≤ (5/2)·25^L`. -/
def Sec5_encodings : Prop :=
  ∀ L : ℕ, (∑ k ∈ range (L + 1), (5 : ℝ) ^ k * 4 ^ (L - k) * 3 ^ L) ≤ 5 * 15 ^ L ∧
    (∑ k ∈ range (L + 1), (5 : ℝ) ^ (L + k) * 3 ^ (L - k)) ≤ 5 / 2 * 25 ^ L

/-! ## Part II: definitions -/

section PartIIDefs

/-- Section 12: the primes in `[P, 2P)`. -/
def primesIn (P : ℕ) : Finset ℕ := (Finset.Ico P (2 * P)).filter Nat.Prime

variable {ι : Type}

/-- Sections 13.3 and 15.1, abstractly. An item `x` (a probe of Section 13 or an incidence of
Section 15) has a multiset `val x` of integers: the numbers `a + b - c` over the pairs
`(b, c) ∈ A_j × A_k` of the probe `(a; j, k)`, or the weights `S(a, b, c)` over the vertices `c` of
the piece `C_k` of the incidence `(a, b, k)`. `cnt val m x` is `cnt_m(x)`, the number of values
divisible by `m`. -/
def cnt (val : ι → Multiset ℤ) (m : ℕ) (x : ι) : ℕ := (val x).countP fun v => (m : ℤ) ∣ v

/-- `Z(Q)`, `z(x)`: the number of values equal to `0` (the true solutions). -/
def zcnt (val : ι → Multiset ℤ) (x : ι) : ℕ := (val x).countP fun v => v = 0

/-- The false positives of `x` modulo `m`: the nonzero values divisible by `m` (`f_m(x)`). -/
def fcnt (val : ι → Multiset ℤ) (m : ℕ) (x : ι) : ℕ := (val x).countP fun v => v ≠ 0 ∧ (m : ℤ) ∣ v

/-- `Σ_t(m) := ∑_{x ∈ S} cnt_m(x)`, the count that the oracle supplies for the surviving items. -/
def Csum (val : ι → Multiset ℤ) (S : Finset ι) (m : ℕ) : ℕ := ∑ x ∈ S, cnt val m x

/-- `F_S(m)`: the number of false positives of the items of `S` modulo `m`. -/
def Fsum (val : ι → Multiset ℤ) (S : Finset ι) (m : ℕ) : ℕ := ∑ x ∈ S, fcnt val m x

/-- Step 2(b) of Sections 13.4 and 15.3, the modulus built prime by prime: a list `ps` of distinct
primes of the pool `Π` such that each `ps[l]` minimises `Σ_t(m p)`, `m` the product of the primes
chosen before, over the primes of the pool not chosen before ("ties arbitrarily": any minimiser). -/
def IsGreedy (val : ι → Multiset ℤ) (S : Finset ι) (Pl : Finset ℕ) (ps : List ℕ) : Prop :=
  ps.Nodup ∧ (∀ p ∈ ps, p ∈ Pl) ∧
    ∀ (l : ℕ) (hl : l < ps.length), ∀ p ∈ Pl, p ∉ ps.take l →
      Csum val S ((ps.take l).prod * ps[l]) ≤ Csum val S ((ps.take l).prod * p)

/-- The algorithm of Sections 13.4 and 15.3, its stages. `M S` is the modulus that stage builds
for the surviving set `S` (step 2(b)); with `k` stages left the run on `S` answers NO if `S = ∅`
(step 2(a)), YES if `Σ_t(M) > |S|/2` (step 2(c)), and continues with the items whose count modulo
`M` is positive (step 2(d)); with no stage left it scans (step 3): YES if some surviving item has a
true solution. -/
noncomputable def detect (val : ι → Multiset ℤ) (M : Finset ι → ℕ) : ℕ → Finset ι → Bool
  | 0, S => decide (∃ x ∈ S, 0 < zcnt val x)
  | k + 1, S =>
    if S.card = 0 then false
    else if (S.card : ℝ) / 2 < Csum val S (M S) then true
    else detect val M k (S.filter fun x => 0 < cnt val (M S) x)

/-- The surviving sets of `detect`: `survivors val M k S` is the set after `k` stages (assuming
the run did not answer before). -/
def survivors (val : ι → Multiset ℤ) (M : Finset ι → ℕ) : ℕ → Finset ι → Finset ι
  | 0, S => S
  | k + 1, S => survivors val M k (S.filter fun x => 0 < cnt val (M S) x)

/-- Section 15.4, the certification rule: with the base modulus `m` and the pool `Π'`,
`μ(x) := min_{p ∈ Π'} cnt_{mp}(x)`. -/
def muCert (val : ι → Multiset ℤ) (m : ℕ) (Pl' : Finset ℕ) (x : ι) : ℕ :=
  if h : Pl'.Nonempty then Pl'.inf' h (fun p => cnt val (m * p) x) else 0

/-- "certified false if `μ(x) = 0`". -/
def CertFalse (val : ι → Multiset ℤ) (m : ℕ) (Pl' : Finset ℕ) (x : ι) : Prop :=
  muCert val m Pl' x = 0

/-- "certified true if `μ(x) |Π'| > ℓ · cnt_m(x)`". -/
def CertTrue (val : ι → Multiset ℤ) (m : ℕ) (Pl' : Finset ℕ) (ℓ : ℕ) (x : ι) : Prop :=
  ℓ * cnt val m x < muCert val m Pl' x * Pl'.card

instance (val : ι → Multiset ℤ) (m : ℕ) (Pl' : Finset ℕ) (x : ι) :
    Decidable (CertFalse val m Pl' x) := by unfold CertFalse; infer_instance

instance (val : ι → Multiset ℤ) (m : ℕ) (Pl' : Finset ℕ) (ℓ : ℕ) (x : ι) :
    Decidable (CertTrue val m Pl' ℓ x) := by unfold CertTrue; infer_instance

/-- "uncertified otherwise". -/
def Uncert (val : ι → Multiset ℤ) (m : ℕ) (Pl' : Finset ℕ) (ℓ : ℕ) (x : ι) : Prop :=
  ¬ CertFalse val m Pl' x ∧ ¬ CertTrue val m Pl' ℓ x

instance (val : ι → Multiset ℤ) (m : ℕ) (Pl' : Finset ℕ) (ℓ : ℕ) (x : ι) :
    Decidable (Uncert val m Pl' ℓ x) := by unfold Uncert; infer_instance

/-- The algorithm of Section 15.4: every item belongs to a pair (`pair x`); `M S` and `Pool S` are
the base modulus after the `r - 1` greedy steps and the pool `Π'` of the certification round of the
stage on `S`; a stage marks the pairs of the certified-true items and keeps the uncertified items
whose pair is not marked; after the stages, the scans mark the pairs of the surviving items with a
true solution (step 3). The result is the set of pairs answered YES. -/
noncomputable def allEdges {α : Type} [DecidableEq α] (val : ι → Multiset ℤ) (pair : ι → α)
    (M : Finset ι → ℕ) (Pool : Finset ι → Finset ℕ) (ℓ : ℕ) : ℕ → Finset ι → Finset α → Finset α
  | 0, S, marked => marked ∪ (S.filter fun x => 0 < zcnt val x).image pair
  | k + 1, S, marked =>
    let marked' := marked ∪ (S.filter fun x => CertTrue val (M S) (Pool S) ℓ x).image pair
    allEdges val pair M Pool ℓ k
      (S.filter fun x => Uncert val (M S) (Pool S) ℓ x ∧ pair x ∉ marked') marked'

end PartIIDefs

/-! ## Part II: statements -/

/-! ### Section 12 -/

/-- **Lemma 12.1**. "For every integer `P ≥ 1024` the interval `[P, 2P)` contains at least
`P/(2 ln P)` primes", from the bounds of Rosser and Schoenfeld. -/
def Lemma_12_1 : Prop :=
  Assumptions.RosserSchoenfeld → ∀ P : ℕ, 1024 ≤ P → (P : ℝ) / (2 * Real.log P) ≤ (primesIn P).card

/-- **Lemma 12.2** (averaging). "Let `P ≥ 2`, `Z_max ≥ 2`, let `m ≥ 1` be an integer, and let `Π'`
be a nonempty set of primes `≥ P`, none dividing `m`. Let `𝓕` be a finite multiset of nonzero
integers `z` with `|z| ≤ Z_max`, each divisible by `m`. Then `∑_{p ∈ Π'} #{z ∈ 𝓕 : mp | z} ≤
|𝓕| · log_P Z_max`, so some `p ∈ Π'` satisfies `#{z ∈ 𝓕 : mp | z} ≤ |𝓕| log_P Z_max/|Π'|`." -/
def Lemma_12_2 : Prop :=
  ∀ (P : ℕ) (Zmax : ℝ) (m : ℕ) (Pl' : Finset ℕ) (𝓕 : Multiset ℤ),
    2 ≤ P → 2 ≤ Zmax → 1 ≤ m → Pl'.Nonempty → (∀ p ∈ Pl', p.Prime ∧ P ≤ p ∧ ¬ p ∣ m) →
    (∀ z ∈ 𝓕, z ≠ 0 ∧ (|z| : ℝ) ≤ Zmax ∧ (m : ℤ) ∣ z) →
    ((∑ p ∈ Pl', 𝓕.countP fun z => ((m * p : ℕ) : ℤ) ∣ z : ℕ) : ℝ) ≤ 𝓕.card * Real.logb P Zmax ∧
    ∃ p ∈ Pl', ((𝓕.countP fun z => ((m * p : ℕ) : ℤ) ∣ z : ℕ) : ℝ)
      ≤ 𝓕.card * Real.logb P Zmax / Pl'.card

/-! ### Sections 13 and 15: the stages, abstractly -/

/-- **Lemma 13.9 and Lemma 15.7**, the bound of one stage. If the values are bounded by
`Z_max ≥ 2`, the pool `Π` consists of primes `≥ P ≥ 2` and has at least `P/(2 ln P)` elements,
`r ≤ P/(4 ln P)`, and `ps` is a greedy choice of `r` primes, then "`F(m_l) ≤ F(m_{l-1}) ·
(ln Z_max/ln P) · (4 ln P/P)`" at each step, so `F(M) ≤ F(1) (4 ln Z_max/P)^r` for the modulus
`M = ∏ ps`. -/
def Lemma_13_9_greedy : Prop :=
  ∀ {ι : Type} (val : ι → Multiset ℤ) (S : Finset ι) (Pl : Finset ℕ) (P r : ℕ) (Zmax : ℝ)
    (ps : List ℕ),
    2 ≤ P → 2 ≤ Zmax → (∀ x ∈ S, ∀ v ∈ val x, (|v| : ℝ) ≤ Zmax) →
    (∀ p ∈ Pl, p.Prime ∧ P ≤ p) → (P : ℝ) / (2 * Real.log P) ≤ Pl.card →
    (r : ℝ) ≤ P / (4 * Real.log P) → ps.length = r → IsGreedy val S Pl ps →
    (Fsum val S ps.prod : ℝ) ≤ Fsum val S 1 * (4 * Real.log Zmax / P) ^ r

/-- **Lemma 13.9**, its conclusion, and the first part of the correctness lemmas: "if step 2(c)
answers YES then `Z > 0`, so the answer is correct; otherwise `|𝒫_t| ≤ |𝒫_{t-1}|/2`", whenever the
modulus `M` has `F(M) ≤ |S|/2`. -/
def Lemma_13_9_stage : Prop :=
  ∀ {ι : Type} (val : ι → Multiset ℤ) (S : Finset ι) (M : ℕ), (Fsum val S M : ℝ) ≤ S.card / 2 →
    ((S.card : ℝ) / 2 < Csum val S M → ∃ x ∈ S, 0 < zcnt val x) ∧
    (¬ (S.card : ℝ) / 2 < Csum val S M →
      ((S.filter fun x => 0 < cnt val M x).card : ℝ) ≤ S.card / 2)

/-- **Lemma 13.10 and Lemma 15.9**, abstractly. "The algorithm answers YES if and only if" some
item has a true solution, for every number of stages, whenever every stage's modulus has at most
`|S|/2` false positives; and the survivors after `k` stages number at most `|S₀|/2^k`. -/
def Lemma_13_10_abstract : Prop :=
  ∀ {ι : Type} (val : ι → Multiset ℤ) (M : Finset ι → ℕ),
    (∀ S : Finset ι, (Fsum val S (M S) : ℝ) ≤ S.card / 2) →
    ∀ (k : ℕ) (S : Finset ι),
      (detect val M k S = true ↔ ∃ x ∈ S, 0 < zcnt val x) ∧
      ((∀ j < k, ¬ ((survivors val M j S).card : ℝ) / 2
          < Csum val (survivors val M j S) (M (survivors val M j S))) →
        ((survivors val M k S).card : ℝ) ≤ S.card / 2 ^ k)

/-- **Lemma 15.10** (certification), abstractly. With a base modulus `m ≥ 1` and a pool `Π'` of
primes not dividing `m`, such that every nonzero value of `x` is divisible by at most `ℓ` primes
of `Π'`: "(i) a certified-false incidence `x` has `z(x) = 0`; (ii) a certified-true incidence `x`
has `z(x) ≥ 1`; (iii) an uncertified incidence `x` satisfies `ℓ f_m(x) ≥ |Π'| - ℓ`". -/
def Lemma_15_10 : Prop :=
  ∀ {ι : Type} (val : ι → Multiset ℤ) (m : ℕ) (Pl' : Finset ℕ) (ℓ : ℕ) (x : ι),
    1 ≤ m → Pl'.Nonempty → (∀ p ∈ Pl', p.Prime ∧ ¬ p ∣ m) →
    (∀ v ∈ val x, v ≠ 0 → (Pl'.filter fun p : ℕ => (p : ℤ) ∣ v).card ≤ ℓ) →
    (CertFalse val m Pl' x → zcnt val x = 0) ∧
    (CertTrue val m Pl' ℓ x → 1 ≤ zcnt val x) ∧
    (Uncert val m Pl' ℓ x → (Pl'.card : ℤ) - ℓ ≤ ℓ * fcnt val m x)

/-- **Lemma 15.11** (halving of all incidences), abstractly. If `F(m) ≤ σ |S| (4ζ/P)^{r-1}`, every
nonzero value is divisible by at most `ℓ` primes of the pool `Π'`, `|Π'| ≥ P/(4 ln P)`,
`ℓ ≤ ζ/ln P`, `P ≥ 8ζ` and `(4ζ/P)^r ≤ 1/(4σ)`, then the uncertified items number at most
`|S|/2`. -/
def Lemma_15_11 : Prop :=
  ∀ {ι : Type} (val : ι → Multiset ℤ) (S : Finset ι) (m : ℕ) (Pl' : Finset ℕ) (ℓ r P : ℕ)
    (σ ζ : ℝ),
    1 ≤ m → Pl'.Nonempty → (∀ p ∈ Pl', p.Prime ∧ ¬ p ∣ m) → 1 ≤ r → 2 ≤ P → 0 < ζ → 0 ≤ σ →
    (∀ x ∈ S, ∀ v ∈ val x, v ≠ 0 → (Pl'.filter fun p : ℕ => (p : ℤ) ∣ v).card ≤ ℓ) →
    (Fsum val S m : ℝ) ≤ σ * S.card * (4 * ζ / P) ^ (r - 1) →
    (P : ℝ) / (4 * Real.log P) ≤ Pl'.card → (ℓ : ℝ) ≤ ζ / Real.log P → 8 * ζ ≤ P →
    (4 * ζ / P) ^ r ≤ 1 / (4 * σ) →
    ((S.filter fun x => Uncert val m Pl' ℓ x).card : ℝ) ≤ S.card / 2

/-- **Lemma 15.12** (correctness of the all-edges algorithm), abstractly. "A pair `(a, b)` is
answered YES if and only if `S(a, b, c) = 0` for some `c ∈ C`": a pair is in the final marked set
exactly if one of its items has a true solution, whenever every stage's base modulus and pool
satisfy the hypotheses of the certification lemma. -/
def Lemma_15_12_abstract : Prop :=
  ∀ {ι α : Type} [DecidableEq α] (val : ι → Multiset ℤ) (pair : ι → α) (M : Finset ι → ℕ)
    (Pool : Finset ι → Finset ℕ) (ℓ : ℕ),
    (∀ S : Finset ι, 1 ≤ M S ∧ (Pool S).Nonempty ∧ (∀ p ∈ Pool S, p.Prime ∧ ¬ p ∣ M S) ∧
      ∀ x ∈ S, ∀ v ∈ val x, v ≠ 0 → ((Pool S).filter fun p : ℕ => (p : ℤ) ∣ v).card ≤ ℓ) →
    ∀ (k : ℕ) (S : Finset ι) (a : α),
      a ∈ allEdges val pair M Pool ℓ k S ∅ ↔ ∃ x ∈ S, pair x = a ∧ 0 < zcnt val x

/-! ### Section 13: 3SUM -/

section ThreeSumDefs

/-- **Definition 13.1** (3SUM, core form): "Given a set `A ⊆ [U]` of `n` integers, decide whether
there are `a, b, c ∈ A` (not necessarily distinct) with `a + b = c`." -/
def ThreeSumCore (A : Finset ℕ) : Prop := ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a + b = c

variable {g : ℕ}

/-- The group `A_i` of the self-reduction, `grp` giving the group of each element. -/
def grpSet (A : Finset ℕ) (grp : ℕ → Fin g) (i : Fin g) : Finset ℕ := A.filter fun a => grp a = i

/-- Section 13.3: "A probe is a triple `Q = (a; j, k)` such that `(i, j, k) ∈ R` for the group
`A_i ∋ a`"; `𝒫₀` is the set of all probes. -/
def probes (A : Finset ℕ) (grp : ℕ → Fin g) (R : Finset (Fin g × Fin g × Fin g)) :
    Finset (ℕ × Fin g × Fin g) :=
  (A ×ˢ univ).filter fun q => (grp q.1, q.2.1, q.2.2) ∈ R

/-- The values of a probe `(a; j, k)`: the numbers `a + b - c` over `(b, c) ∈ A_j × A_k`, so that
`cnt_m(Q) = #{(b, c) : a + b ≡ c (mod m)}` and `Z(Q) = #{(b, c) : a + b = c}`. -/
def val3 (A : Finset ℕ) (grp : ℕ → Fin g) (q : ℕ × Fin g × Fin g) : Multiset ℤ :=
  ((grpSet A grp q.2.1 ×ˢ grpSet A grp q.2.2).val).map fun bc => (q.1 : ℤ) + bc.1 - bc.2

end ThreeSumDefs

/-- **Lemma 13.10** (correctness of the 3SUM algorithm). "The algorithm answers YES if and only if
`A` is a yes-instance", for every partition and set of triples with the covering property of
[FKP24, Lemma 3.3] and every number `L` of stages, whenever every stage's modulus has at most
`|𝒫|/2` false positives (Lemma 13.9; `Lemma_13_9_threeSum`). -/
def Lemma_13_10 : Prop :=
  ∀ {g : ℕ} (A : Finset ℕ) (grp : ℕ → Fin g) (R : Finset (Fin g × Fin g × Fin g)),
    (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + b = c → (grp a, grp b, grp c) ∈ R) →
    ∀ M : Finset (ℕ × Fin g × Fin g) → ℕ,
      (∀ S, (Fsum (val3 A grp) S (M S) : ℝ) ≤ S.card / 2) →
      ∀ L : ℕ, (detect (val3 A grp) M L (probes A grp R) = true ↔ ThreeSumCore A)

/-- **Lemma 13.9** for 3SUM: with `A ⊆ [U]`, groups of at most `σ` elements, the pool `Π` of
primes in `[P, 2P)` with `|Π| ≥ P/(2 ln P)`, `r ≤ P/(4 ln P)` and `P ≥ 4 ln(2U) (2σ²)^{1/r}`,
every modulus built greedily from `r` primes has "`F_𝒫(M_t) ≤ |𝒫|/2`", for every set `𝒫` of
probes; the proof uses "`F_𝒫(1) ≤ ∑_Q cnt_1(Q) ≤ |𝒫| σ²`" and "`|a+b-c| ≤ 2U`". -/
def Lemma_13_9_threeSum : Prop :=
  ∀ {g : ℕ} (A : Finset ℕ) (grp : ℕ → Fin g) (U σ P r : ℕ) (Pl : Finset ℕ)
    (S : Finset (ℕ × Fin g × Fin g)) (ps : List ℕ),
    1 ≤ U → (∀ a ∈ A, 1 ≤ a ∧ a ≤ U) → 1 ≤ σ → (∀ i, (grpSet A grp i).card ≤ σ) →
    (∀ q ∈ S, q.1 ∈ A) → 2 ≤ P → (∀ p ∈ Pl, p.Prime ∧ P ≤ p) →
    (P : ℝ) / (2 * Real.log P) ≤ Pl.card → (r : ℝ) ≤ P / (4 * Real.log P) →
    4 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) ≤ P → 1 ≤ r →
    ps.length = r → IsGreedy (val3 A grp) S Pl ps →
    (Fsum (val3 A grp) S ps.prod : ℝ) ≤ S.card / 2

/-- **Lemma 13.7** (the counts). With `T ≥ 1`, `T² ≥ m`, `ϱ := a mod m`, `x := ⌈ϱ/T⌉` and
`y := xT - ϱ`: "`x ≤ T`, and `0 ≤ y < T`; and `xT - y ≡ a (mod m)`", and the entry of `XY` at
`π_m(Q) = ((j, x), (k, y))` is `cnt_m(Q)`, where `X[(j,x), λ] := #{b ∈ A_j : b + xT ≡ λ}` and
`Y[λ, (k,y)] := #{c ∈ A_k : c + y ≡ λ} (mod m)`; that is,
`∑_λ X[(j,x),λ] Y[λ,(k,y)] = #{(b, c) ∈ A_j × A_k : a + b ≡ c (mod m)}`. -/
def Lemma_13_7 : Prop :=
  ∀ (m T a : ℕ) [NeZero m] (Aj Ak : Finset ℕ), 1 ≤ T → m ≤ T ^ 2 →
    let ϱ := a % m
    let x := (ϱ + T - 1) / T
    let y := x * T - ϱ
    x ≤ T ∧ y < T ∧ ((x * T : ℕ) : ℤ) - y ≡ a [ZMOD m] ∧
    (∑ lam : ZMod m, (Aj.filter fun b => ((b + x * T : ℕ) : ZMod m) = lam).card
        * (Ak.filter fun c => ((c + y : ℕ) : ZMod m) = lam).card)
      = ((Aj ×ˢ Ak).filter fun bc => (m : ℤ) ∣ (a : ℤ) + bc.1 - bc.2).card

/-- **Lemma 13.5**(a), (b) (variants). "Three sets `A, B, C ⊆ [-U, U]`, question
`∃ a ∈ A, b ∈ B, c ∈ C : a + b = c`. Let `S := {a+10U} ∪ {b+30U} ∪ {c+40U} ⊆ [41U]`. Then the
instance is a yes-instance if and only if `S` is a yes-instance of Definition 13.1"; "(b) The
question `a + b + c = 0` is (a) with `C` replaced by `-C`". -/
def Lemma_13_5_ab : Prop :=
  ∀ (U : ℤ) (A B C : Finset ℤ), 1 ≤ U → (∀ a ∈ A, |a| ≤ U) → (∀ b ∈ B, |b| ≤ U) →
    (∀ c ∈ C, |c| ≤ U) →
    let S : Finset ℤ := A.image (· + 10 * U) ∪ B.image (· + 30 * U) ∪ C.image (· + 40 * U)
    (∀ s ∈ S, 1 ≤ s ∧ s ≤ 41 * U) ∧
    ((∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a + b = c) ↔ ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x + y = z) ∧
    ((∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a + b + c = 0) ↔ ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C.image Neg.neg, a + b = c)

/-- **Lemma 13.5**(c). "One list `x_0, …, x_{n-1}`, question: distinct `i, j, k` with
`x_i + x_j + x_k = 0`. Write the indices in binary with `ℓ := ⌈log₂ n⌉` bits. For two bit
positions `β₁ ≠ β₂`, let the class of `i` be its two bits at `β₁, β₂`, and for each injective
assignment of three classes to the roles `A, B, C` form the three-set instance … The list is a
yes-instance if and only if one of these … three-set instances (with `a + b + c = 0`) is", and
there are at most `24 ℓ²` of them (ordered pairs of bit positions times the `4·3·2` injective
assignments). Here `n ≤ 2^ℓ`. -/
def Lemma_13_5_c : Prop :=
  ∀ (n ℓ : ℕ) (x : Fin n → ℤ), n ≤ 2 ^ ℓ →
    let cls : ℕ → ℕ → Fin n → Bool × Bool := fun β₁ β₂ i => (Nat.testBit i β₁, Nat.testBit i β₂)
    ((∃ i j k : Fin n, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i + x j + x k = 0) ↔
      ∃ β₁ < ℓ, ∃ β₂ < ℓ, β₁ ≠ β₂ ∧ ∃ c₁ c₂ c₃ : Bool × Bool, c₁ ≠ c₂ ∧ c₂ ≠ c₃ ∧ c₁ ≠ c₃ ∧
        ∃ i j k : Fin n, cls β₁ β₂ i = c₁ ∧ cls β₁ β₂ j = c₂ ∧ cls β₁ β₂ k = c₃ ∧
          x i + x j + x k = 0) ∧
    (((Finset.range ℓ ×ˢ Finset.range ℓ).filter fun p => p.1 ≠ p.2) ×ˢ
      ((univ : Finset ((Bool × Bool) × (Bool × Bool) × (Bool × Bool))).filter
        fun c => c.1 ≠ c.2.1 ∧ c.2.1 ≠ c.2.2 ∧ c.1 ≠ c.2.2)).card ≤ 24 * ℓ ^ 2

/-- **Lemma 13.6** (binary splitting). "Write `X = ∑_{i<B} 2^i X_i` and `Y = ∑_{j<B} 2^j Y_j` with
`0/1` matrices. Then `(XY)[I, J] = ∑_{i,j<B} 2^{i+j} (X_i Y_j)[I, J]`", for `X`, `Y` with entries in
`{0, …, 2^B - 1}`, `X_i` the matrix of the bits `i` of the entries. -/
def Lemma_13_6 : Prop :=
  ∀ {n d : ℕ} (B : ℕ) (X : Matrix (Fin n) (Fin d) ℕ) (Y : Matrix (Fin d) (Fin n) ℕ),
    (∀ I t, X I t < 2 ^ B) → (∀ t J, Y t J < 2 ^ B) →
    let bits : ℕ → ℕ → ℕ := fun i v => if Nat.testBit v i then 1 else 0
    (∀ I t, X I t = ∑ i ∈ range B, 2 ^ i * bits i (X I t)) ∧
    ∀ I J, (X * Y) I J = ∑ i ∈ range B, ∑ j ∈ range B,
      2 ^ (i + j) * ((X.map (bits i)) * (Y.map (bits j))) I J

/-- Section 13.3, the parameters and equation (5). With `Λ_S := 2 (10 ln(2U))^r`,
`σ := ⌊√(n^ε/Λ_S)⌋`, `g := ⌈c₁ n/σ⌉` and `P := ⌈4 ln(2U) (2σ²)^{1/r}⌉`, under the assumptions on
large `n` that the proof uses (`σ ≥ 2`, `c₁ n/σ ≥ 1`, `(2σ²)^{1/r} ≥ 2`): "`½ √(n^ε/Λ_S) ≤ σ`,
`Λ_S σ² ≤ n^ε`, `g ≤ 2c₁ n/σ`, `(2P)^r ≤ Λ_S σ²`", with "`P ≤ 5 ln(2U) (2σ²)^{1/r}`"; and "since
`U ≤ n^ν` and `n ≥ 2`, `ln(2U) ≤ (ν+1) ln n`". -/
def Eq_13_5 : Prop :=
  ∀ (n U ε c₁ : ℝ) (r : ℕ), 0 < n → 1 ≤ U → 1 ≤ r → 0 < c₁ →
    let Λ := 2 * (10 * Real.log (2 * U)) ^ r
    let σ := ⌊Real.sqrt (n ^ ε / Λ)⌋₊
    let g := ⌈c₁ * n / σ⌉₊
    let P := ⌈4 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ))⌉₊
    2 ≤ σ → 1 ≤ c₁ * n / σ → 2 ≤ (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) →
    Real.sqrt (n ^ ε / Λ) / 2 ≤ σ ∧ Λ * (σ : ℝ) ^ 2 ≤ n ^ ε ∧ (g : ℝ) ≤ 2 * c₁ * n / σ ∧
      (P : ℝ) ≤ 5 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) ∧
      (2 * (P : ℝ)) ^ r ≤ Λ * (σ : ℝ) ^ 2

/-- Section 13.3: "`ln(2U) ≤ (ν+1) ln n`" for `1 ≤ U ≤ n^ν`, `n ≥ 2`, `ν ≥ 1`; Section 15.1:
"`ζ = ln(3U) ≤ (ν+2) ln n`" (as `ln 3 ≤ 2 ln 2`). -/
def Sec13_log_bounds : Prop :=
  ∀ (n U ν : ℝ), 2 ≤ n → 1 ≤ U → 1 ≤ ν → U ≤ n ^ ν →
    Real.log (2 * U) ≤ (ν + 1) * Real.log n ∧ Real.log (3 * U) ≤ (ν + 2) * Real.log n

/-- **Lemma 13.8**, its arithmetic. With `T ≥ 1`, `√m ≤ T < √m + 1`, `N := g(T+1)`, `D := m`:
"`g√D ≤ N ≤ 3g√D`"; "`D ≤ N^ε`" from `D ≤ Λ_S σ²`, `g ≥ n/σ` and `Λ_S σ² ≤ n^ε`; the cost of one
`0/1` instance, `(number of parts) · C N²/D^γ`, with at most `1 + 2c₂σ/√D` parts of
`⌊N²/√D⌋` positions for `|W| ≤ c₂ g² σ`, is at most `9 C (1 + 2c₂) Λ_S^{1-γ} g² σ^{2-2γ}`; and
"`D^{1+γ} ≤ N`, so `ND ≤ N²/D^γ`; and `|W| ≤ N²/√D ≤ N²/D^γ`".

The count `1 + 2c₂σ/√D` is the corrected text: the parts have `⌊N²/√D⌋`
positions, which is at least half of `N²/√D`. -/
def Lemma_13_8_arith : Prop :=
  (∀ (m g T : ℝ), 1 ≤ m → 0 ≤ g → Real.sqrt m ≤ T → T < Real.sqrt m + 1 →
    g * Real.sqrt m ≤ g * (T + 1) ∧ g * (T + 1) ≤ 3 * g * Real.sqrt m) ∧
  (∀ (n σ g Λ D N ε : ℝ), 0 < σ → 1 ≤ Λ → 1 ≤ D → 0 < ε → ε ≤ 1 / 2 → D ≤ Λ * σ ^ 2 →
    n / σ ≤ g → Λ * σ ^ 2 ≤ n ^ ε → g * Real.sqrt D ≤ N → 0 < n → D ≤ N ^ ε) ∧
  (∀ (σ g Λ D γ c₂ C W N : ℝ), 1 ≤ σ → 1 ≤ Λ → 1 ≤ D → 0 < γ → γ ≤ 1 / 2 → D ≤ Λ * σ ^ 2 →
    0 ≤ c₂ → 0 ≤ C → 0 ≤ g → g * Real.sqrt D ≤ N → N ≤ 3 * g * Real.sqrt D → 0 ≤ W →
    W ≤ c₂ * g ^ 2 * σ → 1 ≤ N ^ 2 / Real.sqrt D →
    (⌈W / ⌊N ^ 2 / Real.sqrt D⌋₊⌉₊ : ℝ) * (C * N ^ 2 / D ^ γ)
      ≤ (1 + 2 * c₂ * σ / Real.sqrt D) * (9 * C * g ^ 2 * D ^ (1 - γ)) ∧
    (1 + 2 * c₂ * σ / Real.sqrt D) * (9 * C * g ^ 2 * D ^ (1 - γ))
      ≤ 9 * C * (1 + 2 * c₂) * Λ ^ (1 - γ) * g ^ 2 * σ ^ (2 - 2 * γ)) ∧
  (∀ (N D ε γ : ℝ), 1 ≤ N → 1 ≤ D → 0 < ε → 0 ≤ γ → γ ≤ 1 / 2 → ε * (1 + γ) ≤ 1 → D ≤ N ^ ε →
    D ^ (1 + γ) ≤ N ∧ N * D ≤ N ^ 2 / D ^ γ ∧ N ^ 2 / Real.sqrt D ≤ N ^ 2 / D ^ γ)

/-- Section 13.6, equation (6): inserting "`g²σ^{2-2γ} ≤ 4c₁² n² σ^{-2γ} ≤ 4^{1+γ} c₁² Λ_S^γ
n^{2-εγ}`, `P ≤ 5 ln(2U)(2σ²)^{1/r} ≤ 10 ln(2U) n^{ε/r}`, `L, B ≤ log₂ n + 1`,
`Λ_S^{1-γ} Λ_S^γ = Λ_S = 2(10 ln(2U))^r` and `ln(2U) ≤ (ν+1) ln n`" into the cost of the stages
`L r P B² Λ_S^{1-γ} g² σ^{2-2γ}` gives "`T(n) = O(r n^{2-εγ+ε/r} (10(ν+1))^{r+1} (ln n)^{r+4})`"
with the constant `432 c₁²` (for `γ ≤ 1/2`). -/
def Eq_13_6 : Prop :=
  ∀ (n U ν ε γ c₁ σ g P L B : ℝ) (r : ℕ), 2 ≤ n → 1 ≤ U → 1 ≤ ν → U ≤ n ^ ν → 0 < ε →
    0 < γ → γ ≤ 1 / 2 → 0 < c₁ → 1 ≤ r → 1 ≤ σ →
    let Λ := 2 * (10 * Real.log (2 * U)) ^ r
    Real.sqrt (n ^ ε / Λ) / 2 ≤ σ → Λ * σ ^ 2 ≤ n ^ ε → 0 ≤ g → g ≤ 2 * c₁ * n / σ →
    0 ≤ P → P ≤ 5 * Real.log (2 * U) * (2 * σ ^ 2) ^ (1 / (r : ℝ)) →
    0 ≤ L → L ≤ Real.logb 2 n + 1 → 0 ≤ B → B ≤ Real.logb 2 n + 1 →
    L * r * P * B ^ 2 * Λ ^ (1 - γ) * g ^ 2 * σ ^ (2 - 2 * γ)
      ≤ 432 * c₁ ^ 2 * r * n ^ (2 - ε * γ + ε / r) * (10 * (ν + 1)) ^ (r + 1)
          * (Real.log n) ^ (r + 4)

/-- **Corollary 13.3** (one algorithm), the computation: with `r(n) := ⌈√(ln n/ln ln n)⌉`,
"`r (10(ν+1))^{r+1} (ln n)^{r+4} = exp(O(√(ln n ln ln n)))`" and
"`n^{ε/r} ≤ exp(ε √(ln n ln ln n))`", so the factor by which the bound of equation (6) exceeds
`n^{2-εγ}` is `exp(O(√(ln n ln ln n)))`. (The side conditions of the parameters for large `n` are
not stated.) -/
def Corollary_13_3_arith : Prop :=
  ∀ ν ε : ℝ, 1 ≤ ν → 0 < ε → ∃ C : ℝ, ∀ n : ℝ, Real.exp (Real.exp 1) ≤ n →
    let r := ⌈Real.sqrt (Real.log n / Real.log (Real.log n))⌉₊
    (r : ℝ) * (10 * (ν + 1)) ^ (r + 1) * (Real.log n) ^ (r + 4) * n ^ (ε / r)
      ≤ Real.exp (C * Real.sqrt (Real.log n * Real.log (Real.log n)))

/-- **Corollary 13.4**, its arithmetic: "in (a) and (b) one instance of at most `3n` integers with
universe `41U ≤ n^{ν+1} ≤ (3n)^{ν+1}` for `n ≥ 41`". -/
def Corollary_13_4_arith : Prop :=
  ∀ (n U ν : ℝ), 41 ≤ n → 0 ≤ ν → 0 ≤ U → U ≤ n ^ ν →
    41 * U ≤ n ^ (ν + 1) ∧ n ^ (ν + 1) ≤ (3 * n) ^ (ν + 1)

/-! ### Section 15: Exact Triangle, its all-edges version, the (min,+)-product and APSP -/

section ETDefs

/-- Section 15: an instance of Exact Triangle, a complete tripartite graph on parts `A`, `B`, `C`
(here `Fin nA`, `Fin nB`, `Fin nC`) with an integer weight on every edge. -/
structure ETInst (nA nB nC : ℕ) where
  wab : Fin nA → Fin nB → ℤ
  wbc : Fin nB → Fin nC → ℤ
  wac : Fin nA → Fin nC → ℤ

variable {nA nB nC h : ℕ}

/-- `S(a, b, c) := w(a, b) + w(b, c) + w(a, c)`. -/
def ETInst.S (T : ETInst nA nB nC) (a : Fin nA) (b : Fin nB) (c : Fin nC) : ℤ :=
  T.wab a b + T.wbc b c + T.wac a c

/-- Section 15.1: the values of an incidence `x = (a, b, k)`: the weights `S(a, b, c)` over the
vertices `c` of the piece `C_k` (`piece c` is the piece of `c`), so that
`cnt_m(x) = #{c ∈ C_k : S(a, b, c) ≡ 0 (mod m)}` and `z(x) = #{c ∈ C_k : S(a, b, c) = 0}`. -/
def valE (T : ETInst nA nB nC) (piece : Fin nC → Fin h) (x : Fin nA × Fin nB × Fin h) :
    Multiset ℤ :=
  ((univ.filter fun c => piece c = x.2.2).val).map fun c => T.S x.1 x.2.1 c

end ETDefs

/-- **Lemma 15.9** (correctness of the Exact Triangle algorithm). "The algorithm answers YES if and
only if the instance has a zero triangle", starting from all incidences `𝓘₀ = A × B × [h]`, for
every number of stages, whenever every stage's modulus has at most `|𝓘|/2` false positives
(Lemma 15.8, `Lemma_15_8`). -/
def Lemma_15_9 : Prop :=
  ∀ {nA nB nC h : ℕ} (T : ETInst nA nB nC) (piece : Fin nC → Fin h)
    (M : Finset (Fin nA × Fin nB × Fin h) → ℕ),
    (∀ S, (Fsum (valE T piece) S (M S) : ℝ) ≤ S.card / 2) →
    ∀ L : ℕ, (detect (valE T piece) M L univ = true ↔ ∃ a b c, T.S a b c = 0)

/-- **Lemma 15.8** (halving) and **Lemma 15.7** applied `r` times: with weights of absolute value at
most `U` (so `|S(a,b,c)| ≤ 3U`), pieces of at most `σ` vertices, the pool `Π` of primes `≥ P`
with `|Π| ≥ P/(2 ln P)`, `r ≤ P/(4 ln P)` and `P ≥ 4ζ (2σ)^{1/r}` for `ζ = ln(3U)`, every modulus
built greedily from `r` primes has "`F_𝓘(M_t) ≤ |𝓘|/2`"; the proof uses `F_𝓘(1) ≤ σ |𝓘|`. -/
def Lemma_15_8 : Prop :=
  ∀ {nA nB nC h : ℕ} (T : ETInst nA nB nC) (piece : Fin nC → Fin h) (U σ P r : ℕ)
    (Pl : Finset ℕ) (S : Finset (Fin nA × Fin nB × Fin h)) (ps : List ℕ),
    1 ≤ U → (∀ a b, |T.wab a b| ≤ U) → (∀ b c, |T.wbc b c| ≤ U) → (∀ a c, |T.wac a c| ≤ U) →
    1 ≤ σ → (∀ k, (univ.filter fun c => piece c = k).card ≤ σ) →
    2 ≤ P → (∀ p ∈ Pl, p.Prime ∧ P ≤ p) → (P : ℝ) / (2 * Real.log P) ≤ Pl.card →
    (r : ℝ) ≤ P / (4 * Real.log P) → 1 ≤ r →
    4 * Real.log (3 * U) * (2 * (σ : ℝ)) ^ (1 / (r : ℝ)) ≤ P →
    ps.length = r → IsGreedy (valE T piece) S Pl ps →
    (Fsum (valE T piece) S ps.prod : ℝ) ≤ S.card / 2

/-- **Lemma 15.11** (halving of all incidences) for Exact Triangle: after `r - 1` greedy steps
(the list `ps`) and the certification round with the pool `Π'` of the unused primes of `Π`, with
`ℓ` "the largest integer `l ≥ 0` with `P^l ≤ 3U`" (`Nat.log P (3U)`), and with `P ≥ 8ζ` and
`P ≥ 4ζ(4σ)^{1/r}` for `ζ = ln(3U)`: "`|𝓘_t| ≤ |𝓘_{t-1}|/2`". -/
def Lemma_15_11_ET : Prop :=
  ∀ {nA nB nC h : ℕ} (T : ETInst nA nB nC) (piece : Fin nC → Fin h) (U σ P r ℓ : ℕ)
    (Pl : Finset ℕ) (S : Finset (Fin nA × Fin nB × Fin h)) (ps : List ℕ),
    1 ≤ U → (∀ a b, |T.wab a b| ≤ U) → (∀ b c, |T.wbc b c| ≤ U) → (∀ a c, |T.wac a c| ≤ U) →
    1 ≤ σ → (∀ k, (univ.filter fun c => piece c = k).card ≤ σ) →
    2 ≤ P → (∀ p ∈ Pl, p.Prime ∧ P ≤ p) → (P : ℝ) / (2 * Real.log P) ≤ Pl.card →
    (r : ℝ) ≤ P / (4 * Real.log P) → 1 ≤ r → ℓ = Nat.log P (3 * U) →
    8 * Real.log (3 * U) ≤ P → 4 * Real.log (3 * U) * (4 * (σ : ℝ)) ^ (1 / (r : ℝ)) ≤ P →
    ps.length = r - 1 → IsGreedy (valE T piece) S Pl ps →
    ((S.filter fun x => Uncert (valE T piece) ps.prod (Pl.filter fun p => p ∉ ps) ℓ x).card : ℝ)
      ≤ S.card / 2

/-- **Lemma 15.12** (correctness of the all-edges algorithm). "A pair `(a, b)` is answered YES if
and only if `S(a, b, c) = 0` for some `c ∈ C`", for the base moduli and pools of the algorithm:
the base modulus of a stage is at least 1, the pool is a nonempty set of primes `≥ P` not dividing
it, and `ℓ` is at least "the largest integer `l ≥ 0` with `P^l ≤ 3U`" (`Nat.log P (3U)`). -/
def Lemma_15_12 : Prop :=
  ∀ {nA nB nC h : ℕ} (T : ETInst nA nB nC) (piece : Fin nC → Fin h) (U P ℓ : ℕ)
    (M : Finset (Fin nA × Fin nB × Fin h) → ℕ) (Pool : Finset (Fin nA × Fin nB × Fin h) → Finset ℕ),
    1 ≤ U → (∀ a b, |T.wab a b| ≤ U) → (∀ b c, |T.wbc b c| ≤ U) → (∀ a c, |T.wac a c| ≤ U) →
    2 ≤ P → Nat.log P (3 * U) ≤ ℓ →
    (∀ S, 1 ≤ M S ∧ (Pool S).Nonempty ∧ ∀ p ∈ Pool S, p.Prime ∧ P ≤ p ∧ ¬ p ∣ M S) →
    ∀ (L : ℕ) (a : Fin nA) (b : Fin nB),
      (a, b) ∈ allEdges (valE T piece) (fun x => (x.1, x.2.1)) M Pool ℓ L univ ∅ ↔
        ∃ c, T.S a b c = 0

/-- **Lemma 15.5** (the counts). In the instance `J(m, k, ϱ, 𝒬)`, with middle part `C_k × Z_m` and
the edges `a ∼ (c, λ) ⟺ λ ≡ w(a, c) + ϱ`, `(c, λ) ∼ b ⟺ λ ≡ -w(b, c) (mod m)`: for a pair with
`w(a, b) ≡ ϱ`, "the number of common neighbours of `a` and `b` … is `cnt_m(a, b, k)`". -/
def Lemma_15_5 : Prop :=
  ∀ {nA nB nC : ℕ} (T : ETInst nA nB nC) (m : ℕ) [NeZero m] (Ck : Finset (Fin nC)) (ϱ : ZMod m)
    (a : Fin nA) (b : Fin nB), ((T.wab a b : ℤ) : ZMod m) = ϱ →
    ((Ck ×ˢ (univ : Finset (ZMod m))).filter fun cl =>
        cl.2 = ((T.wac a cl.1 : ℤ) : ZMod m) + ϱ ∧ cl.2 = -((T.wbc b cl.1 : ℤ) : ZMod m)).card
      = (Ck.filter fun c => (m : ℤ) ∣ T.S a b c).card

/-- **Lemma 15.13**, the comparison. With `w(i, k) := X[i, k]`, `w(k, j) := Y[k, j]` and
`w(i, j) := -t - 1`: "The triangle `(i, k, j)` is negative if and only if `X[i,k] + Y[k,j] ≤ t`, so
the edge `(i, j)` lies in a negative triangle if and only if `Z[i, j] ≤ t`", where
`Z[i,j] = min_k (X[i,k] + Y[k,j])`. -/
def Lemma_15_13_test : Prop :=
  ∀ {n : ℕ} (X Y : Fin n → Fin n → ℤ) (i j : Fin n) (t : ℤ) (hn : 0 < n),
    (∃ k, X i k + Y k j + (-t - 1) < 0) ↔
      (univ.image fun k => X i k + Y k j).min' (by simp [Finset.univ_nonempty_iff]; exact ⟨⟨0, hn⟩⟩) ≤ t

/-- **Lemma 15.13**, the search. "Each round at least halves the number of values in every
interval, so after `⌈log₂(4U+1)⌉` rounds every interval is the single value `Z[i, j]`": the
interval `[lo, hi] ∋ Z` with `t := ⌊(lo+hi)/2⌋` becomes `[lo, t]` if `Z ≤ t` and `[t+1, hi]`
otherwise; started at `[-2U, 2U]`, after `⌈log₂(4U+1)⌉` rounds it is `[Z, Z]`. -/
def Lemma_15_13_search : Prop :=
  ∀ (U : ℕ) (Z : ℤ), -(2 * U : ℤ) ≤ Z → Z ≤ 2 * U →
    let step : ℤ × ℤ → ℤ × ℤ := fun I =>
      if Z ≤ (I.1 + I.2) / 2 then (I.1, (I.1 + I.2) / 2) else ((I.1 + I.2) / 2 + 1, I.2)
    step^[Nat.clog 2 (4 * U + 1)] (-(2 * U : ℤ), 2 * U) = (Z, Z)

/-- Section 15.6, Link 3: "Let `U'` bound the absolute values of the present weights … give every
missing edge the weight `3U' + 1`. A triangle with all three edges present then has weight `0` if
and only if its original weight is `t`; a triangle with a missing edge has weight at least
`3U' + 1 - 2U' > 0`." Here the weights of the asked part `A × C` are already shifted by `-t`. -/
def Sec15_link3 : Prop :=
  ∀ (U' : ℤ) (present : Fin 3 → Prop) [DecidablePred present] (w : Fin 3 → ℤ),
    0 ≤ U' → (∀ e, present e → |w e| ≤ U') →
    let w' : Fin 3 → ℤ := fun e => if present e then w e else 3 * U' + 1
    (w' 0 + w' 1 + w' 2 = 0 ↔ (∀ e, present e) ∧ w 0 + w 1 + w 2 = 0)

/-- Section 15.6, APSP, the encoding of `∞`: "Encode `∞` as `Ω := 3n^{ν+1} + 1`: a sum with at
least one term `Ω` is at least `Ω - n^{ν+1} > 2n^{ν+1}`, more than any sum of two finite
entries", and "`3n^{ν+1} + 1 ≤ n^{ν+2}` (for `n ≥ 4`)". -/
def Sec15_apsp_encoding : Prop :=
  (∀ (B x y : ℤ), 0 ≤ B → |x| ≤ B → |y| ≤ B →
    2 * B < (3 * B + 1) + x ∧ x + y ≤ 2 * B ∧ (3 * B + 1) + (3 * B + 1) > 2 * B) ∧
  (∀ (n ν : ℕ), 4 ≤ n → 3 * n ^ (ν + 1) + 1 ≤ n ^ (ν + 2))

/-- Section 15.1, the parameters and equation (7). With `ζ := ln(3U)`, `Λ_E := ξ(10ζ)^r`,
`σ := ⌊√(n^ε/Λ_E)⌋`, `P := ⌈4ζ(ξσ)^{1/r}⌉`, `h := ⌈|C|/σ⌉`, under the assumptions on large `n`
(`σ ≥ 2`, `(ξσ)^{1/r} ≥ 2`, `σ ≤ n`, `|C| ≤ n`): "`½√(n^ε/Λ_E) ≤ σ ≤ n^{ε/2}`,
`Λ_E σ² ≤ n^ε`, `h ≤ 2n/σ`, `(2P)^r ≤ Λ_E σ`, `P ≥ 8ζ`". -/
def Eq_15_7 : Prop :=
  ∀ (n U ε ξ Cc : ℝ) (r : ℕ), 1 ≤ n → 1 ≤ U → 0 < ε → 1 ≤ ξ → 1 ≤ r → 0 ≤ Cc → Cc ≤ n →
    let ζ := Real.log (3 * U)
    let Λ := ξ * (10 * ζ) ^ r
    let σ := ⌊Real.sqrt (n ^ ε / Λ)⌋₊
    let P := ⌈4 * ζ * (ξ * σ) ^ (1 / (r : ℝ))⌉₊
    let hh := ⌈Cc / σ⌉₊
    2 ≤ σ → 2 ≤ (ξ * σ) ^ (1 / (r : ℝ)) → (σ : ℝ) ≤ n →
    Real.sqrt (n ^ ε / Λ) / 2 ≤ σ ∧ (σ : ℝ) ≤ n ^ (ε / 2) ∧ Λ * (σ : ℝ) ^ 2 ≤ n ^ ε ∧
      (hh : ℝ) ≤ 2 * n / σ ∧ (2 * (P : ℝ)) ^ r ≤ Λ * σ ∧ 8 * ζ ≤ P

/-- Section 15.5, equation (8): the cost of the stages `L r P n³ Λ_E^{1-γ} σ^{-2γ}` is at most
`48 r n^{3-εγ+ε/(2r)} (10(ν+2))^{r+1} (ln n)^{r+2}` (inserting "`σ^{-2γ} ≤ 4^γ Λ_E^γ n^{-εγ}`,
`P ≤ 5ζ(ξσ)^{1/r} ≤ 20ζ n^{ε/(2r)}`, `L ≤ log₂ n + 1 ≤ 3 ln n`, `Λ_E ≤ 4(10ζ)^r`, and
`ζ ≤ (ν+2) ln n`"). -/
def Eq_15_8 : Prop :=
  ∀ (n U ν ε γ ξ σ P L : ℝ) (r : ℕ), 2 ≤ n → 1 ≤ U → 1 ≤ ν → U ≤ n ^ ν → 0 < ε → 0 < γ →
    γ ≤ 1 / 2 → 1 ≤ ξ → ξ ≤ 4 → 1 ≤ r → 1 ≤ σ →
    let ζ := Real.log (3 * U)
    let Λ := ξ * (10 * ζ) ^ r
    Real.sqrt (n ^ ε / Λ) / 2 ≤ σ → σ ≤ n ^ (ε / 2) →
    0 ≤ P → P ≤ 5 * ζ * (ξ * σ) ^ (1 / (r : ℝ)) → 0 ≤ L → L ≤ Real.logb 2 n + 1 →
    L * r * P * n ^ 3 * Λ ^ (1 - γ) * σ ^ (-(2 * γ))
      ≤ 48 * r * n ^ (3 - ε * γ + ε / (2 * r)) * (10 * (ν + 2)) ^ (r + 1) * (Real.log n) ^ (r + 2)

/-- **Corollary 15.3** (one algorithm), the computation: with the same `r(n)` as in Corollary 13.3,
`r (10(ν+2))^{r+1} (ln n)^{r+2} n^{ε/(2r)} = exp(O(√(ln n ln ln n)))`. -/
def Corollary_15_3_arith : Prop :=
  ∀ ν ε : ℝ, 1 ≤ ν → 0 < ε → ∃ C : ℝ, ∀ n : ℝ, Real.exp (Real.exp 1) ≤ n →
    let r := ⌈Real.sqrt (Real.log n / Real.log (Real.log n))⌉₊
    (r : ℝ) * (10 * (ν + 2)) ^ (r + 1) * (Real.log n) ^ (r + 2) * n ^ (ε / (2 * r))
      ≤ Real.exp (C * Real.sqrt (Real.log n * Real.log (Real.log n)))

/-- Section 15.4: "Let `ℓ` be the largest integer `l ≥ 0` with `P^l ≤ 3U` … Every nonzero integer
of absolute value at most `3U` has at most `ℓ` distinct prime divisors `≥ P`, and
`ℓ ≤ ζ/ln P`." -/
def Sec15_ell : Prop :=
  ∀ (U P : ℕ) (Pl : Finset ℕ) (v : ℤ), 1 ≤ U → 2 ≤ P → (∀ p ∈ Pl, p.Prime ∧ P ≤ p) → v ≠ 0 →
    |v| ≤ 3 * U →
    (Pl.filter fun p : ℕ => (p : ℤ) ∣ v).card ≤ Nat.log P (3 * U) ∧
    (Nat.log P (3 * U) : ℝ) ≤ Real.log (3 * U) / Real.log P

/-- **Lemma 15.6**, its arithmetic. "`D = σm ≤ Λ_E σ² ≤ n^ε`"; with `|W_{k,ϱ}|` summing to at most
`n²` over the `m` residues and chunks of `⌊n²/√D⌋ ≥ n²/(2√D)` pairs, "piece `k` needs at most
`m + 2√(σm)` calls"; "in both cases [the cost for the piece] is at most
`3C n² Λ_E^{1-γ} σ^{1-2γ}`"; and the bookkeeping "`|𝓘| ≤ hn² ≤ 2n³/σ ≤ 2n³σ^{-2γ}`",
"`hm ≤ 2nΛ_E ≤ n² ≤ n³σ^{-2γ}`". -/
def Lemma_15_6_arith : Prop :=
  (∀ (σ m Λ n ε : ℝ), 0 ≤ σ → m ≤ Λ * σ → Λ * σ ^ 2 ≤ n ^ ε → σ * m ≤ n ^ ε) ∧
  (∀ (m : ℕ) (w : Fin m → ℝ) (n D : ℝ), (∀ ϱ, 0 ≤ w ϱ) → ∑ ϱ, w ϱ ≤ n ^ 2 → 0 < D →
    1 ≤ n ^ 2 / Real.sqrt D →
    (∑ ϱ, (⌈w ϱ / ⌊n ^ 2 / Real.sqrt D⌋₊⌉₊ : ℝ)) ≤ m + 2 * Real.sqrt D) ∧
  (∀ (σ m Λ n γ C : ℝ), 1 ≤ σ → 2 ≤ m → m ≤ Λ * σ → 1 ≤ Λ → 0 < γ → γ ≤ 1 / 2 → 0 ≤ C →
    (m + 2 * Real.sqrt (σ * m)) * (C * n ^ 2 * (σ * m) ^ (-γ))
      ≤ 3 * C * n ^ 2 * Λ ^ (1 - γ) * σ ^ (1 - 2 * γ)) ∧
  (∀ (σ n γ : ℝ), 1 ≤ σ → σ ≤ n → 0 ≤ γ → γ ≤ 1 / 2 →
    2 * n ^ 3 / σ ≤ 2 * n ^ 3 * σ ^ (-(2 * γ)) ∧ n ^ 2 ≤ n ^ 3 * σ ^ (-(2 * γ)))

/-! ### Section 15.6: APSP by repeated squaring

The definitions of this part are copied from `3sum-apsp/PaperStatements.lean` (the formalization
of [ZT], Apache 2.0), where the same argument proves [ZT, Theorem 21(b)]'s repeated squaring. -/

section APSPDefs

/-- The (min,+)-product as a function, for matrices whose entries may be `+∞` (`⊤`): the minimum
over the empty set, and any sum with `+∞`, is `+∞`. -/
def minPlus {R : Type} [Add R] [LinearOrder R] {n m l : ℕ} (A : Matrix (Fin n) (Fin m) (WithTop R))
    (B : Matrix (Fin m) (Fin l) (WithTop R)) : Matrix (Fin n) (Fin l) (WithTop R) :=
  Matrix.of fun i j => Finset.univ.inf fun k => A i k + B k j

/-! A directed graph on the vertices `Fin n` with edge weights in `R` is a function
`w : Fin n → Fin n → WithTop R`: `w i j` is the weight of the edge from `i` to `j`, and `⊤` (that
is, `+∞`) if there is no such edge.  A walk that starts at `i` is given by the list of the vertices
it visits after `i`. -/

/-- The vertex at which the walk that starts at `i` and then visits `rest` ends. -/
def walkEnd {n : ℕ} : Fin n → List (Fin n) → Fin n
  | i, [] => i
  | _, j :: rest => walkEnd j rest

/-- The total weight of the walk that starts at `i` and then visits `rest`; it is `⊤` if one of its
edges is missing, and the empty walk has weight 0. -/
def walkWeight {R : Type} [Add R] [Zero R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Fin n → List (Fin n) → WithTop R
  | _, [] => 0
  | i, j :: rest => w i j + walkWeight w j rest

/-- Section 1 and Theorems 21 and 22: "no negative cycles".  Stated for closed walks, which is the
same thing: a closed walk decomposes into cycles. -/
def NoNegativeCycle {R : Type} [Add R] [Zero R] [LE R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Prop :=
  ∀ (i : Fin n) (rest : List (Fin n)), walkEnd i rest = i → 0 ≤ walkWeight w i rest

/-- **APSP**, Section 1: "compute the shortest-path distance between every pair of vertices".  `d i
j` is the least weight of a walk from `i` to `j`, and `⊤` if `j` cannot be reached from `i`. -/
def IsDistanceMatrix {R : Type} [Add R] [Zero R] [Preorder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) (d : Fin n → Fin n → WithTop R) : Prop :=
  ∀ i j, IsLeast {x | ∃ rest : List (Fin n), walkEnd i rest = j ∧ walkWeight w i rest = x} (d i j)

/-- Every edge weight of the directed graph has absolute value at most `U`. -/
def EdgeWeightsBoundedBy {R : Type} [Lattice R] [AddGroup R] {n : ℕ} (w : Fin n → Fin n → WithTop R)
    (U : R) : Prop :=
  ∀ (i j : Fin n) (x : R), w i j = (x : WithTop R) → |x| ≤ U

/-- The weight matrix of the graph, for the repeated squaring behind Theorem 21(b).  Its diagonal
entries are 0, without which repeated squaring would compute walks of exactly `2^t` edges. -/
def weightMatrix {R : Type} [Zero R] {n : ℕ} (w : Fin n → Fin n → WithTop R) :
    Matrix (Fin n) (Fin n) (WithTop R) :=
  Matrix.of fun i j => if i = j then 0 else w i j

/-- Repeated squaring, for Theorem 21(b): `minPlusSquares w t` is the weight matrix after `t`
squarings in the (min,+)-product. -/
def minPlusSquares {R : Type} [Add R] [Zero R] [LinearOrder R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R) : ℕ → Matrix (Fin n) (Fin n) (WithTop R)
  | 0 => weightMatrix w
  | t + 1 => minPlus (minPlusSquares w t) (minPlusSquares w t)


end APSPDefs

/-- Section 15.6, "APSP to the (min,+)-product": "`d_{2k} = d_k ⋆ d_k` in the (min,+) sense …
Since there are no negative cycles, deleting cycles from a walk does not increase its weight, so
… `d_k = d_{n-1}` is the distance matrix for `k ≥ n-1`. Hence `⌈log₂ n⌉` products … give APSP":
squaring the weight matrix `⌈log₂ n⌉` times in the (min,+)-product yields the distance matrix. -/
def Sec15_apsp_squaring : Prop :=
  ∀ {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R),
  NoNegativeCycle w → IsDistanceMatrix w (minPlusSquares w (Nat.clog 2 n))

/-- Section 15.6: "a finite `d_k(u, v)` is the weight of a path, of absolute value at most
`(n-1)n^ν < n^{ν+1}`": every finite entry of every matrix of the repeated squaring has absolute
value at most `nU` when the edge weights are bounded by `U` (with `U = n^ν`, at most `n^{ν+1}`). -/
def Sec15_apsp_entries : Prop :=
  ∀ {R : Type} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R] {n : ℕ}
    (w : Fin n → Fin n → WithTop R),
  NoNegativeCycle w →
  ∀ U : R, 0 ≤ U → EdgeWeightsBoundedBy w U →
  ∀ (t : ℕ) (i j : Fin n) (x : R), minPlusSquares w t i j = (x : WithTop R) → |x| ≤ n • U


/-- Section 15.6, APSP, one product with the integer encoding of `∞`: "Encode `∞` as
`Ω := 3n^{ν+1} + 1`: a sum with at least one term `Ω` is at least `Ω - n^{ν+1} > 2n^{ν+1}`, more
than any sum of two finite entries, so after each product the entries above `n^{ν+1}` are exactly
the infinite ones, and are reset to `Ω`." With `B` in place of `n^{ν+1}`: if the finite entries of
`X`, `Y` and of their `(min,+)`-product are at most `B` in absolute value, then the integer product
of the encodings (`untopD Ω`), with the entries above `B` reset to `Ω`, is the encoding of the
`(min,+)`-product. -/
def Sec15_apsp_step : Prop :=
  ∀ {n : ℕ} (B : ℤ) (X Y : Matrix (Fin n) (Fin n) (WithTop ℤ)), 0 ≤ B →
    (∀ i k (v : ℤ), X i k = v → |v| ≤ B) → (∀ k j (v : ℤ), Y k j = v → |v| ≤ B) →
    (∀ i j (v : ℤ), minPlus X Y i j = v → |v| ≤ B) →
    ∀ i j : Fin n,
      let P := Finset.univ.inf' ⟨i, Finset.mem_univ i⟩
        fun k => (X i k).untopD (3 * B + 1) + (Y k j).untopD (3 * B + 1)
      (if B < P then 3 * B + 1 else P) = (minPlus X Y i j).untopD (3 * B + 1)

/-! ### Section 14: the deterministic version of [KPP16] (Theorem 14.1), the arithmetic -/

/-- **Theorem 14.1**, the parameters of the proof. With `σ := ⌊n^{1-α}⌋`, `g := ⌈c₁ n/σ⌉`,
`Λ := 2(10(ν+1) ln n)^r` and `Λ_S := 2(10 ln(2U))^r`, for `n` large enough that `c₁ n/σ ≥ 1` and
`16 c₁² c₂ n^{1+α} ≤ n³`: "`Λ_S ≤ Λ`", "`P ≤ 5 ln(2U)(2σ²)^{1/r} ≤ 10(ν+1) n^{(2-2α)/r} ln n`",
"`u = m < (2P)^r ≤ Λ_S σ² ≤ Λσ² ≤ Λ n^{2-2α}`", "`N = g(2T+1) ≤ 10 c₁ √Λ n` with `T = ⌈√m⌉`",
"`s ≤ σ ≤ n^{1-α}`", "`q_S ≤ |𝒫₀| ≤ c₂ g² σ ≤ 8 c₁² c₂ n^{1+α}`", and
"`L := ⌈log₂(c₂ g² σ)⌉ ≤ 3 log₂ n`" with `|𝒫₀| ≤ 2^L`. -/
def Theorem_14_1_params : Prop :=
  ∀ (n U ν α c₁ c₂ P m : ℝ) (r : ℕ), 2 ≤ n → 1 ≤ U → 1 ≤ ν → U ≤ n ^ ν → 0 < α → α < 1 →
    0 < c₁ → 0 < c₂ → 1 ≤ r →
    let σ := ⌊n ^ (1 - α)⌋₊
    let g := ⌈c₁ * n / σ⌉₊
    let Λ := 2 * (10 * (ν + 1) * Real.log n) ^ r
    let ΛS := 2 * (10 * Real.log (2 * U)) ^ r
    1 ≤ c₁ * n / σ → 16 * c₁ ^ 2 * c₂ * n ^ (1 + α) ≤ n ^ 3 →
    ΛS ≤ Λ ∧
    (0 ≤ P → P ≤ 5 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ)) →
      P ≤ 10 * (ν + 1) * n ^ ((2 - 2 * α) / r) * Real.log n) ∧
    (ΛS * (σ : ℝ) ^ 2 ≤ Λ * n ^ (2 - 2 * α)) ∧
    (0 ≤ m → m < Λ * (σ : ℝ) ^ 2 →
      (g : ℝ) * (2 * ⌈Real.sqrt m⌉₊ + 1) ≤ 10 * c₁ * Real.sqrt Λ * n) ∧
    ((σ : ℝ) ≤ n ^ (1 - α)) ∧
    (c₂ * (g : ℝ) ^ 2 * σ ≤ 8 * c₁ ^ 2 * c₂ * n ^ (1 + α)) ∧
    (1 ≤ c₂ * (g : ℝ) ^ 2 * σ →
      (⌈Real.logb 2 (c₂ * (g : ℝ) ^ 2 * σ)⌉₊ : ℝ) ≤ 3 * Real.logb 2 n ∧
      c₂ * (g : ℝ) ^ 2 * σ ≤ 2 ^ ⌈Real.logb 2 (c₂ * (g : ℝ) ^ 2 * σ)⌉₊)

/-- **Theorem 14.1**, the arithmetic of the consequence. "The instances have the stated
parameters for `n' := Λ^{1/(2-2α)} n`": `Λ n^{2-2α} = n'^{2-2α}`, `√Λ n ≤ n'`,
`n^{1-α} ≤ n'^{1-α}`, `n^{1+α} ≤ n'^{1+α}`; "so each call takes
`O(n'^{2-η}) = O(Λ^{1/(1-α)} n^{2-η})` time"; "the time per call outside the oracle is
`O(Λ^{1/2} n^{2-η} log n)` because `η ≤ min(α, 1-α)`" (`n^{2-α}, n^{1+α} ≤ n^{2-η}` and
`√Λ ≤ Λ^{1/(1-α)}`); and `Λ^{1/(1-α)} = 2^{1/(1-α)} (10(ν+1))^{r/(1-α)} (ln n)^{r/(1-α)}`, the
power `r/(1-α)` of `log n` in the bound. -/
def Theorem_14_1_consequence : Prop :=
  ∀ (n ν α η : ℝ) (r : ℕ), 3 ≤ n → 1 ≤ ν → 0 < α → α < 1 → 0 ≤ η → η ≤ min α (1 - α) →
    1 ≤ r →
    let Λ := 2 * (10 * (ν + 1) * Real.log n) ^ r
    let n' := Λ ^ (1 / (2 - 2 * α)) * n
    Λ * n ^ (2 - 2 * α) = n' ^ (2 - 2 * α) ∧ Real.sqrt Λ * n ≤ n' ∧
    n ^ (1 - α) ≤ n' ^ (1 - α) ∧ n ^ (1 + α) ≤ n' ^ (1 + α) ∧
    n' ^ (2 - η) ≤ Λ ^ (1 / (1 - α)) * n ^ (2 - η) ∧
    n ^ (2 - α) ≤ n ^ (2 - η) ∧ n ^ (1 + α) ≤ n ^ (2 - η) ∧ Real.sqrt Λ ≤ Λ ^ (1 / (1 - α)) ∧
    Λ ^ (1 / (1 - α)) = 2 ^ (1 / (1 - α)) * (10 * (ν + 1)) ^ (r / (1 - α)) *
      (Real.log n) ^ (r / (1 - α))

/-- Link 2, "the detection version of the all-edges problem therefore suffices": the count of an
edge in the negative-triangle instance is a sum of the counts of the edge in the exact-triangle
instances of [CVX23, Lemma 9.2], "so an edge lies in a negative triangle if and only if it lies in
a triangle of target weight in at least one of the instances". -/
def Sec15_link2 : Prop :=
  ∀ {ι : Type} (s : Finset ι) (c : ι → ℕ) (cneg : ℕ), cneg = ∑ i ∈ s, c i →
    (0 < cneg ↔ ∃ i ∈ s, 0 < c i)


open Classical in
/-- Link 2 with [CVX23, Lemma 9.2] (`Assumptions.CVX23_Lemma_9_2`): "The counts are sums of
nonnegative counts, so an edge lies in a negative triangle if and only if it lies in a triangle of
target weight in at least one of the instances; the detection version of the all-edges problem
therefore suffices", with `O(log n)` instances on the same vertex set and targets `0` or `1`. -/
def Sec15_link2_detection : Prop :=
  Assumptions.CVX23_Lemma_9_2 →
  ∃ c : ℕ, ∀ (n : ℕ) (A B C : Finset (Fin n)) (w : Fin n → Fin n → ℤ),
    ∃ (I : ℕ) (wI : Fin I → Fin n → Fin n → Option ℤ) (t : Fin I → ℤ),
      I ≤ c * (Nat.log 2 n + 1) ∧ (∀ i, t i = 0 ∨ t i = 1) ∧
      ∀ a ∈ A, ∀ c' ∈ C,
        ((∃ b ∈ B, w a b + w b c' + w a c' < 0) ↔
          ∃ i, ∃ b ∈ B, ∃ x y z, wI i a b = some x ∧ wI i b c' = some y ∧ wI i a c' = some z ∧
            x + y + z = t i)

/-- **Corollary 10.1**, the arithmetic of the substitution `N = n`, `D = n^τ` into Corollary 9.1
(saving `γ`, query exponent `q`, range `N ≥ D^c`): `N² D^{-γ} = n^{2-γτ}`, `N D^q = n^{1+qτ}`, and
`N ≥ D^c` for `τ ≤ 1/c`; for Conjecture 5.12, the `n^{1-τ₂}` blocks of `t₂ = n^{τ₂}` rows with
`D = n^{τ₁}`: "`t₂ = n^{τ₂} ≥ n^{c τ₁} = D^c` when `τ₁ ≤ τ₂/c`", Phase 3 `n^{1-τ₂} t₂² D^{-γ} =
n^{1+τ₂-γτ₁}` and Phase 4 `t₂ D^q = n^{τ₂+qτ₁}`. (With `c = 18, 14`, `γ = 0.092, 0.077`,
`q = 0.403, 0.421`.) -/
def Corollary_10_1_arith : Prop :=
  ∀ (n τ τ₁ τ₂ γ q c : ℝ), 1 ≤ n → 0 < c →
    n ^ (2 : ℝ) * (n ^ τ) ^ (-γ) = n ^ (2 - γ * τ) ∧ n * (n ^ τ) ^ q = n ^ (1 + q * τ) ∧
    (τ ≤ 1 / c → 0 ≤ τ → (n ^ τ) ^ c ≤ n) ∧ (τ₁ ≤ τ₂ / c → 0 ≤ τ₁ → (n ^ τ₁) ^ c ≤ n ^ τ₂) ∧
    n ^ (1 - τ₂) * (n ^ τ₂) ^ (2 : ℝ) * (n ^ τ₁) ^ (-γ) = n ^ (1 + τ₂ - γ * τ₁) ∧
    n ^ τ₂ * (n ^ τ₁) ^ q = n ^ (τ₂ + q * τ₁)

/-! ### Proposition 10.3 (Conjecture 5.12 on a larger region; Remark 10.3 in earlier drafts)

Setting of [BNS19, Conjecture 5.12] as the paper recalls it: Phase 1 receives
`U ∈ {0,1}^{n×t₁}`, `N ∈ {0,1}^{n×n}`, `V ∈ {0,1}^{t₂×n}`, Phase 2 a list `I ∈ [n]^{t₁}`, Phase 3 a
list `J ∈ [n]^{t₂}`, Phase 4 a pair `(i, j)`, after which the Boolean entry `(U N_{I,J} V)_{i,j}` is
output. The lists may repeat indices. The statements below are the index identities on which the
two regions of the remark rest, and the arithmetic of their exponents. The data structure
(Corollaries 7.3, 9.1, Theorem 7.4) and the computational model are not formalized: as in
`Corollary_10_1_arith`, the data structure enters only through its parameters `c`, `γ`, `q`. -/

/-- The Boolean matrix product: entry `(i, j)` is true iff `A i b` and `B b j` for some `b`. -/
def boolMatMul {m k p : Type} [Fintype k] (A : Matrix m k Bool) (B : Matrix k p Bool) :
    Matrix m p Bool :=
  fun i j => decide (∃ b, A i b = true ∧ B b j = true)

/-- A Boolean matrix as a `0/1` matrix over `ℕ` (the paper computes over `ℤ` with `0/1` inputs;
over `ℕ` the products are the same numbers). -/
def natOf {m k : Type} (A : Matrix m k Bool) : Matrix m k ℕ := A.map Bool.toNat

/-- **Proposition 10.3**, the index identities, for Boolean matrices and lists `I`, `J` with repetitions.
The Boolean entry is `(U N_{I,J} V)_{i,j}` (the Boolean product is associative, first conjunct).
*First region*: with `X := U` and `Y := N_{I,[n]}` (row `a` of `Y` is row `I_a` of `N`), computed over
`ℕ`, "column `b` of `U N_{I,J}` is column `J_b` of `XY`, so `(U N_{I,J} V)_{i,j}` is `1` if and only if
`(XY)[i, J_b] > 0` and `V_{b,j} = 1` for some `b ≤ t₂`". *Second region*: with `X := N_{I,J}`,
`Y := V`, "`(U N_{I,J} V)_{i,j}` is `1` if and only if `U_{i,a} = 1` and `(XY)[a,j] > 0` for some
`a ≤ t₁`"; and cutting the columns of `V` into blocks (any map `σ` from a block's columns to `[n]`),
the product of `X` with a block is the block of `XY`. -/
def Remark_10_3_index : Prop :=
  ∀ (n t₁ t₂ : ℕ) (U : Matrix (Fin n) (Fin t₁) Bool) (N : Matrix (Fin n) (Fin n) Bool)
    (V : Matrix (Fin t₂) (Fin n) Bool) (I : Fin t₁ → Fin n) (J : Fin t₂ → Fin n),
    boolMatMul (boolMatMul U (N.submatrix I J)) V = boolMatMul U (boolMatMul (N.submatrix I J) V) ∧
    natOf U * (natOf N).submatrix I J = (natOf U * (natOf N).submatrix I id).submatrix id J ∧
    (∀ i j, boolMatMul (boolMatMul U (N.submatrix I J)) V i j = true ↔
      ∃ b, 0 < (natOf U * (natOf N).submatrix I id) i (J b) ∧ V b j = true) ∧
    (∀ i j, boolMatMul (boolMatMul U (N.submatrix I J)) V i j = true ↔
      ∃ a, U i a = true ∧ 0 < ((natOf N).submatrix I J * natOf V) a j) ∧
    (∀ (β : Type) (σ : β → Fin n),
      ((natOf N).submatrix I J * natOf V).submatrix id σ =
        (natOf N).submatrix I J * (natOf V).submatrix id σ)

/-- **Proposition 10.3**, the index identities over `ℕ` for arbitrary nonnegative entries (a
strengthening of `Remark_10_3_index`: the entries need not be `0/1`, and the entry of the triple
product is positive iff one of the `t₂`, resp. `t₁`, query conditions holds). -/
def Remark_10_3_index_nat : Prop :=
  ∀ (n t₁ t₂ : ℕ) (U : Matrix (Fin n) (Fin t₁) ℕ) (N : Matrix (Fin n) (Fin n) ℕ)
    (V : Matrix (Fin t₂) (Fin n) ℕ) (I : Fin t₁ → Fin n) (J : Fin t₂ → Fin n),
    U * N.submatrix I J = (U * N.submatrix I id).submatrix id J ∧
    (∀ i j, 0 < (U * N.submatrix I J * V) i j ↔ ∃ b, 0 < (U * N.submatrix I id) i (J b) ∧ 0 < V b j) ∧
    (∀ i j, 0 < (U * N.submatrix I J * V) i j ↔ ∃ a, 0 < U i a ∧ 0 < (N.submatrix I J * V) a j)

/-- **Proposition 10.3**, the arithmetic for general parameters of the data structure (range
`N ≥ D^c`, saving `γ > 0`, query exponent `q < 1`), with `t_k = n^{τ_k}`. *First region*
(`N = n`, `D = t₁`): `n ≥ t₁^c` for `τ₁ ≤ 1/c`; Phase 2 `n² D^{-γ} = n^{2-γτ₁} < n²`; Phase 4,
`t₂` queries, `t₂ D^q = n^{τ₂+qτ₁} < n^{τ₁+τ₂}`. *Second region* (`N = t₁`, `D = t₂`, `n/t₁`
blocks): `t₁ ≥ t₂^c` for `τ₂ ≤ τ₁/c`; Phase 3 `(n/t₁) t₁² D^{-γ} = n^{1+τ₁-γτ₂} < n^{1+τ₁}`;
Phase 4, `t₁` queries, `t₁ D^q = n^{τ₁+qτ₂} < n^{τ₁+τ₂}`. The strict inequalities are stated for
`n > 1`. NOTE: `n/t₁` is the real quotient (the paper does not round the number of blocks). -/
def Remark_10_3_general : Prop :=
  ∀ (n τ₁ τ₂ γ q c : ℝ), 1 ≤ n → 0 < c → 0 < γ → q < 1 →
    ((0 ≤ τ₁ → τ₁ ≤ 1 / c → (n ^ τ₁) ^ c ≤ n) ∧
      n ^ (2 : ℝ) * (n ^ τ₁) ^ (-γ) = n ^ (2 - γ * τ₁) ∧
      (0 < τ₁ → 1 < n → n ^ (2 - γ * τ₁) < n ^ (2 : ℝ)) ∧
      n ^ τ₂ * (n ^ τ₁) ^ q = n ^ (τ₂ + q * τ₁) ∧
      (0 < τ₁ → 1 < n → n ^ (τ₂ + q * τ₁) < n ^ (τ₁ + τ₂))) ∧
    ((0 ≤ τ₂ → τ₂ ≤ τ₁ / c → (n ^ τ₂) ^ c ≤ n ^ τ₁) ∧
      n / n ^ τ₁ * (n ^ τ₁) ^ (2 : ℝ) * (n ^ τ₂) ^ (-γ) = n ^ (1 + τ₁ - γ * τ₂) ∧
      (0 < τ₂ → 1 < n → n ^ (1 + τ₁ - γ * τ₂) < n ^ (1 + τ₁)) ∧
      n ^ τ₁ * (n ^ τ₂) ^ q = n ^ (τ₁ + q * τ₂) ∧
      (0 < τ₂ → 1 < n → n ^ (τ₁ + q * τ₂) < n ^ (τ₁ + τ₂)))

/-- **Proposition 10.3**, the explicit exponents, with Corollary 9.1(a)'s `c = 18`, `γ = 0.092`,
`q = 0.403`: "it fails for every `0 < τ₁ < 1/18` and every `0 < τ₂ < 1`: Phase 2 takes
`O(n^{2-0.092τ₁})` time, ..., Phase 4 takes `O(n^{τ₂+0.403τ₁})` time"; "it applies since
`n ≥ t₁^{18}` for `τ₁ < 1/18`"; "it also fails for every `0 < τ₂ < τ₁/18`: ... Phase 3 takes
`O(n^{1+τ₁-0.092τ₂})` time, and Phase 4 takes `O(n^{τ₁+0.403τ₂})` time"; "`t₁ ≥ t₂^{18}` for
`τ₂ < τ₁/18`"; "`(n/t₁)·O(t₁²/D^{0.092}) = O(n^{1+τ₁-0.092τ₂})`"; each exponent below the obvious
algorithm's (`2`, `τ₁+τ₂`, `1+τ₁`, `τ₁+τ₂`). -/
def Remark_10_3_arith : Prop :=
  ∀ (n τ₁ τ₂ : ℝ), 1 ≤ n →
    ((0 < τ₁ → τ₁ < 1 / 18 → (n ^ τ₁) ^ (18 : ℝ) ≤ n) ∧
      n ^ (2 : ℝ) * (n ^ τ₁) ^ (-0.092 : ℝ) = n ^ (2 - 0.092 * τ₁) ∧
      (0 < τ₁ → 2 - 0.092 * τ₁ < 2) ∧
      n ^ τ₂ * (n ^ τ₁) ^ (0.403 : ℝ) = n ^ (τ₂ + 0.403 * τ₁) ∧
      (0 < τ₁ → τ₂ + 0.403 * τ₁ < τ₁ + τ₂)) ∧
    ((0 < τ₂ → τ₂ < τ₁ / 18 → (n ^ τ₂) ^ (18 : ℝ) ≤ n ^ τ₁) ∧
      n / n ^ τ₁ * (n ^ τ₁) ^ (2 : ℝ) * (n ^ τ₂) ^ (-0.092 : ℝ) = n ^ (1 + τ₁ - 0.092 * τ₂) ∧
      (0 < τ₂ → 1 + τ₁ - 0.092 * τ₂ < 1 + τ₁) ∧
      n ^ τ₁ * (n ^ τ₂) ^ (0.403 : ℝ) = n ^ (τ₁ + 0.403 * τ₂) ∧
      (0 < τ₂ → τ₁ + 0.403 * τ₂ < τ₁ + τ₂))

/-- **Proposition 10.3**, the general thresholds: "For `τ₁ < ε*_5`, respectively `τ₂ < ε*_5 τ₁`, use
Corollary 7.3 as in the proof of Corollary 10.1, with `q = 1/2 < 1`" (there `c`, `θ` are chosen as in
Theorem 7.4, whose parameters are `Theorem_7_4_parameters`). In the first region `D = t₁ = n^{τ₁} ≤ N^ε`
with `N = n` and some `0 < ε < ε*_5` (namely `ε = τ₁`); in the second `D = t₂ = n^{τ₂} = N^ε` with
`N = t₁` and `ε = τ₂/τ₁ < ε*_5`; `D ≥ 2` once `n ≥ 2^{1/τ}`; and with `q = 1/2` and any saving
`γ > 0` the four exponents are below the obvious ones (`Remark_10_3_general` at `q = 1/2`). -/
def Remark_10_3_eps : Prop :=
  (∀ τ₁ : ℝ, 0 < τ₁ → τ₁ < epsStar5 →
    ∃ ε : ℝ, 0 < ε ∧ ε < epsStar5 ∧ ∀ n : ℝ, 1 ≤ n → n ^ τ₁ ≤ n ^ ε) ∧
  (∀ τ₁ τ₂ : ℝ, 0 < τ₁ → 0 < τ₂ → τ₂ < epsStar5 * τ₁ →
    ∃ ε : ℝ, 0 < ε ∧ ε < epsStar5 ∧ ∀ n : ℝ, 1 ≤ n → n ^ τ₂ = (n ^ τ₁) ^ ε) ∧
  (∀ τ n : ℝ, 0 < τ → (2 : ℝ) ^ (1 / τ) ≤ n → 2 ≤ n ^ τ) ∧
  (∀ n τ₁ τ₂ γ : ℝ, 1 < n → 0 < γ → 0 < τ₁ → 0 < τ₂ →
    n ^ (2 - γ * τ₁) < n ^ (2 : ℝ) ∧ n ^ (τ₂ + 1 / 2 * τ₁) < n ^ (τ₁ + τ₂) ∧
    n ^ (1 + τ₁ - γ * τ₂) < n ^ (1 + τ₁) ∧ n ^ (τ₁ + 1 / 2 * τ₂) < n ^ (τ₁ + τ₂))

/-- **Proposition 10.3**, the regions: "The region `τ₁ < ε*_5 τ₂` of Corollary 10.1 lies inside the first
of these" (for `τ₂ ≤ 1`; likewise `τ₁ < τ₂/18` inside `τ₁ < 1/18`); the explicit regions lie inside
the general ones; "the point `τ₁ + τ₂ ≈ 1.41` of the main bound of [BNS19] lies in neither, since it
would need `τ₂ > 1` or `τ₁ > 1`" (stated for `τ₁ + τ₂ ≥ 1.4`). -/
def Remark_10_3_regions : Prop :=
  (∀ τ₁ τ₂ : ℝ, τ₂ ≤ 1 → τ₁ < epsStar5 * τ₂ → τ₁ < epsStar5) ∧
  (∀ τ₁ τ₂ : ℝ, τ₂ ≤ 1 → τ₁ < τ₂ / 18 → τ₁ < 1 / 18) ∧
  (∀ τ₁ : ℝ, τ₁ < 1 / 18 → τ₁ < epsStar5) ∧
  (∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → τ₂ < τ₁ / 18 → τ₂ < epsStar5 * τ₁) ∧
  (∀ τ₁ τ₂ : ℝ, 0 ≤ τ₁ → 1.4 ≤ τ₁ + τ₂ →
    (τ₁ < epsStar5 → 1 < τ₂) ∧ (τ₂ < epsStar5 * τ₁ → 1 < τ₁)) ∧
  (∀ τ₁ τ₂ : ℝ, 0 < τ₁ → τ₁ ≤ 1 → τ₂ ≤ 1 → 1.4 ≤ τ₁ + τ₂ →
    ¬ τ₁ < epsStar5 ∧ ¬ τ₂ < epsStar5 * τ₁)

/-- **Section 8 of the paper, paragraph "The limit is Coppersmith's exponent"** (Remark 17.1 before 12 October 2026), the arithmetic: at `L = 5m`, `D = 4^m = 2^{2L/5} = 5^{αL}` with
`α = 2 log 2/(5 log 5)`; a tile has `N' ≤ K N₀ = binom(5m, m) 4^{4m} ≤ 5^{5m}` rows, so
"`D = 2^{2L/5} = 5^{αL} ≥ N'^α`". -/
def Remark_17_1_arith : Prop :=
  ∀ (m : ℕ) (N' : ℝ),
    let α := 2 * Real.log 2 / (5 * Real.log 5)
    let L := 5 * m
    (4 : ℝ) ^ m = (2 : ℝ) ^ (2 * (L : ℝ) / 5) ∧ (2 : ℝ) ^ (2 * (L : ℝ) / 5) = (5 : ℝ) ^ (α * L) ∧
    (L.choose m * 4 ^ (L - m) : ℝ) ≤ 5 ^ L ∧
    (0 ≤ N' → N' ≤ 5 ^ L → N' ^ α ≤ (2 : ℝ) ^ (2 * (L : ℝ) / 5))

/-! ### Sections 13 and 15: the parameters for large `n`, composed with the correctness lemmas

The paper assumes "`n ≥ n₀(ν, r, ε)` large enough" for the side conditions of the parameters
(Sections 13.3 and 15.1), and argues them for the growing `r = r(n)` of Corollaries 13.3 and 15.3
in one sentence. The statements below prove them uniformly for every `r` with `1 ≤ r ≤ r(n)`,
which covers both: a constant `r` satisfies `r ≤ r(n)` for large `n` (`Sec13_rOf_unbounded`), and
`r = r(n)` is the case of equality. -/

/-- `r(n) := ⌈√(ln n/ln ln n)⌉`, the number of primes per modulus in Corollaries 13.3 and 15.3. -/
noncomputable def rOf (n : ℝ) : ℕ := ⌈Real.sqrt (Real.log n / Real.log (Real.log n))⌉₊

/-- `r(n) → ∞`: for every `r` there is `n₀` with `r ≤ r(n)` for `n ≥ n₀`. -/
def Sec13_rOf_unbounded : Prop :=
  ∀ r : ℕ, ∃ n₀ : ℝ, ∀ n : ℝ, n₀ ≤ n → r ≤ rOf n

/-- Section 13.3 and the proof of Corollary 13.3, the side conditions: "We assume
`n ≥ n₀(ν, r, ε)` large enough that `σ ≥ 2`, `c₁ n/σ ≥ 1`, `P ≥ 1024` and `r ≤ P/(4 ln P)`", and
"`(2σ²)^{1/r} ≥ 2` for large `n`", for the parameters `Λ_S := 2(10 ln(2U))^r`,
`σ := ⌊√(n^ε/Λ_S)⌋`, `P := ⌈4 ln(2U)(2σ²)^{1/r}⌉`, uniformly in `1 ≤ U ≤ n^ν` and in
`1 ≤ r ≤ r(n)`. -/
def Sec13_side_conditions : Prop :=
  ∀ ν ε c₁ : ℝ, 1 ≤ ν → 0 < ε → ε ≤ 1 / 2 → 1 ≤ c₁ → ∃ n₀ : ℝ, ∀ (n U : ℝ) (r : ℕ),
    n₀ ≤ n → 1 ≤ U → U ≤ n ^ ν → 1 ≤ r → r ≤ rOf n →
    let Λ := 2 * (10 * Real.log (2 * U)) ^ r
    let σ := ⌊Real.sqrt (n ^ ε / Λ)⌋₊
    let P := ⌈4 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ))⌉₊
    2 ≤ σ ∧ 1 ≤ c₁ * n / σ ∧ 1024 ≤ P ∧ (r : ℝ) ≤ P / (4 * Real.log P) ∧
      2 ≤ (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ))

/-- Section 15.1 and the proof of Corollary 15.3, the side conditions: "We assume
`n ≥ n₀(ν, r, ε)` large enough that `σ ≥ 2`, `P ≥ 1024`, `r ≤ P/(4 ln P)`, `(ξσ)^{1/r} ≥ 2` and
`2nΛ_E ≤ n²`", with `σ ≤ n` (used for `h ≤ 2n/σ`), for `ζ := ln(3U)`, `Λ_E := ξ(10ζ)^r`,
`σ := ⌊√(n^ε/Λ_E)⌋`, `P := ⌈4ζ(ξσ)^{1/r}⌉`, uniformly in `1 ≤ U ≤ n^ν`, `1 ≤ ξ ≤ 4` (the paper
has `ξ ∈ {2, 4}`) and `1 ≤ r ≤ r(n)`. -/
def Sec15_side_conditions : Prop :=
  ∀ ν ε ξ : ℝ, 1 ≤ ν → 0 < ε → ε ≤ 1 / 2 → 1 ≤ ξ → ξ ≤ 4 → ∃ n₀ : ℝ, ∀ (n U : ℝ) (r : ℕ),
    n₀ ≤ n → 1 ≤ U → U ≤ n ^ ν → 1 ≤ r → r ≤ rOf n →
    let ζ := Real.log (3 * U)
    let Λ := ξ * (10 * ζ) ^ r
    let σ := ⌊Real.sqrt (n ^ ε / Λ)⌋₊
    let P := ⌈4 * ζ * (ξ * σ) ^ (1 / (r : ℝ))⌉₊
    2 ≤ σ ∧ 1024 ≤ P ∧ (r : ℝ) ≤ P / (4 * Real.log P) ∧ 2 ≤ (ξ * σ) ^ (1 / (r : ℝ)) ∧
      2 * n * Λ ≤ n ^ 2 ∧ (σ : ℝ) ≤ n

/-- Section 15.1: "split `C` into `h := ⌈|C|/σ⌉` pieces `C_1, …, C_h` of at most `σ` vertices
each". -/
def Sec15_pieces : Prop :=
  ∀ nC σ : ℕ, 1 ≤ σ → ∃ piece : Fin nC → Fin ((nC + σ - 1) / σ),
    ∀ k, (univ.filter fun c => piece c = k).card ≤ σ

/-- **Theorem 13.2 and Corollary 13.3, correctness with the parameters of Section 13.3.** For
`n ≥ n₀`, every `A ⊆ [U]` with `|A| ≤ n`, `U ≤ n^ν`, every `1 ≤ r ≤ r(n)` and every partition and
set of triples with the properties of [FKP24, Lemma 3.3] for `g := ⌈c₁ n/σ⌉ ≥ 1`: "every group
has at most `c₁ n/g ≤ σ` elements"; greedy moduli of `r`
primes from `Π`, the primes in `[P, 2P)`, exist for every set of probes; for every choice of them
("ties arbitrarily") every modulus has at most `|𝒫|/2` false positives (Lemma 13.9), every
candidate modulus `m p` of step 2(b) satisfies "`2 ≤ mp < (2P)^r ≤ Λ_S σ²`", so Lemma 13.8
applies to every evaluation, and the algorithm answers YES if and only if `A` is a yes-instance
(Lemma 13.10), for every number `L` of stages. The pool size comes from Lemma 12.1, so from
[RS62]. The halving is stated for the sets of probes, the only sets that the algorithm meets: a
set with a triple `(a; j, k)`, `a ∉ A`, may have values beyond `2U`. -/
def Theorem_13_2_correct : Prop :=
  Assumptions.RosserSchoenfeld →
  ∀ ν ε c₁ : ℝ, 1 ≤ ν → 0 < ε → ε ≤ 1 / 2 → 1 ≤ c₁ → ∃ n₀ : ℕ, ∀ (n U r : ℕ) (A : Finset ℕ),
    n₀ ≤ n → 1 ≤ U → (U : ℝ) ≤ (n : ℝ) ^ ν → 1 ≤ r → r ≤ rOf n →
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ U) → A.card ≤ n →
    let Λ : ℝ := 2 * (10 * Real.log (2 * U)) ^ r
    let σ := ⌊Real.sqrt ((n : ℝ) ^ ε / Λ)⌋₊
    let g := ⌈c₁ * n / σ⌉₊
    let P := ⌈4 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ))⌉₊
    1 ≤ g ∧ ∀ (grp : ℕ → Fin g) (R : Finset (Fin g × Fin g × Fin g)),
      (∀ i, ((grpSet A grp i).card : ℝ) ≤ c₁ * A.card / g) →
      (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + b = c → (grp a, grp b, grp c) ∈ R) →
      (∀ i, (grpSet A grp i).card ≤ σ) ∧
      (∀ S, ∃ ps : List ℕ, ps.length = r ∧ IsGreedy (val3 A grp) S (primesIn P) ps) ∧
      (∀ (ps : List ℕ), (∀ p ∈ ps, p ∈ primesIn P) → ∀ l < r, ∀ p ∈ primesIn P,
        2 ≤ (ps.take l).prod * p ∧ ((ps.take l).prod * p : ℝ) < (2 * P) ^ r ∧
          ((2 * P : ℕ) : ℝ) ^ r ≤ Λ * σ ^ 2) ∧
      ∀ M : Finset (ℕ × Fin g × Fin g) → ℕ,
        (∀ S, ∃ ps : List ℕ, ps.length = r ∧ IsGreedy (val3 A grp) S (primesIn P) ps ∧
          M S = ps.prod) →
        (∀ S ⊆ probes A grp R, (Fsum (val3 A grp) S (M S) : ℝ) ≤ S.card / 2) ∧
        ∀ L : ℕ, (detect (val3 A grp) M L (probes A grp R) = true ↔ ThreeSumCore A)

/-- **Theorem 13.2 with [FKP24, Lemma 3.3].** The partition and the triples of
`Theorem_13_2_correct` exist, by the cited lemma (with its constant `c₁`), and the algorithm on
them answers YES if and only if `A` is a yes-instance, for every greedy choice of the moduli. -/
def Theorem_13_2_FKP : Prop :=
  Assumptions.FKP_Lemma_3_3 → Assumptions.RosserSchoenfeld →
  ∀ ν ε : ℝ, 1 ≤ ν → 0 < ε → ε ≤ 1 / 2 → ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∃ n₀ : ℕ,
    ∀ (n U r : ℕ) (A : Finset ℕ),
    n₀ ≤ n → 1 ≤ U → (U : ℝ) ≤ (n : ℝ) ^ ν → 1 ≤ r → r ≤ rOf n →
    (∀ a ∈ A, 1 ≤ a ∧ a ≤ U) → A.card ≤ n →
    let Λ : ℝ := 2 * (10 * Real.log (2 * U)) ^ r
    let σ := ⌊Real.sqrt ((n : ℝ) ^ ε / Λ)⌋₊
    let g := ⌈(c₁ : ℝ) * n / σ⌉₊
    let P := ⌈4 * Real.log (2 * U) * (2 * (σ : ℝ) ^ 2) ^ (1 / (r : ℝ))⌉₊
    ∃ (grp : ℕ → Fin g) (R : Finset (Fin g × Fin g × Fin g)),
      (∀ i, (grpSet A grp i).card ≤ σ) ∧
      (∃ M : Finset (ℕ × Fin g × Fin g) → ℕ,
        ∀ S, ∃ ps : List ℕ, ps.length = r ∧ IsGreedy (val3 A grp) S (primesIn P) ps ∧
          M S = ps.prod) ∧
      ∀ M : Finset (ℕ × Fin g × Fin g) → ℕ,
        (∀ S, ∃ ps : List ℕ, ps.length = r ∧ IsGreedy (val3 A grp) S (primesIn P) ps ∧
          M S = ps.prod) →
        ∀ L : ℕ, (detect (val3 A grp) M L (probes A grp R) = true ↔ ThreeSumCore A)

/-- **Theorem 15.1 and Corollary 15.3 (Exact Triangle), correctness with the parameters of
Section 15.1** (`ξ = 2`). For `n ≥ n₀`, every instance with `|C| ≤ n` and weights of absolute
value at most `U ≤ n^ν`, every `1 ≤ r ≤ r(n)` and every split of `C` into pieces of at most `σ`
vertices: greedy moduli of `r` primes of `[P, 2P)` exist for every set of incidences; every
candidate modulus satisfies "`2 ≤ mp < (2P)^r ≤ Λ_E σ`", so Lemma 15.6 applies; and for every
greedy choice every modulus has at most `|𝓘|/2` false positives (Lemma 15.8) and the algorithm
answers YES if and only if the instance has a zero triangle (Lemma 15.9). -/
def Theorem_15_1_correct : Prop :=
  Assumptions.RosserSchoenfeld →
  ∀ ν ε : ℝ, 1 ≤ ν → 0 < ε → ε ≤ 1 / 2 → ∃ n₀ : ℕ,
    ∀ (n U r nA nB nC h : ℕ) (T : ETInst nA nB nC) (piece : Fin nC → Fin h),
    n₀ ≤ n → 1 ≤ U → (U : ℝ) ≤ (n : ℝ) ^ ν → 1 ≤ r → r ≤ rOf n → nC ≤ n →
    (∀ a b, |T.wab a b| ≤ U) → (∀ b c, |T.wbc b c| ≤ U) → (∀ a c, |T.wac a c| ≤ U) →
    let ζ := Real.log (3 * U)
    let Λ := 2 * (10 * ζ) ^ r
    let σ := ⌊Real.sqrt ((n : ℝ) ^ ε / Λ)⌋₊
    let P := ⌈4 * ζ * (2 * (σ : ℝ)) ^ (1 / (r : ℝ))⌉₊
    (∀ k, (univ.filter fun c => piece c = k).card ≤ σ) →
      (∀ S, ∃ ps : List ℕ, ps.length = r ∧ IsGreedy (valE T piece) S (primesIn P) ps) ∧
      (∀ (ps : List ℕ), (∀ p ∈ ps, p ∈ primesIn P) → ∀ l < r, ∀ p ∈ primesIn P,
        2 ≤ (ps.take l).prod * p ∧ ((ps.take l).prod * p : ℝ) < (2 * P) ^ r ∧
          ((2 * P : ℕ) : ℝ) ^ r ≤ Λ * σ) ∧
      ∀ M : Finset (Fin nA × Fin nB × Fin h) → ℕ,
        (∀ S, ∃ ps : List ℕ, ps.length = r ∧ IsGreedy (valE T piece) S (primesIn P) ps ∧
          M S = ps.prod) →
        (∀ S, (Fsum (valE T piece) S (M S) : ℝ) ≤ S.card / 2) ∧
        ∀ L : ℕ, (detect (valE T piece) M L univ = true ↔ ∃ a b c, T.S a b c = 0)

/-- **Theorem 15.2 and Corollary 15.3 (all-edges Exact Triangle), correctness with the parameters
of Section 15.1** (`ξ = 4`). As `Theorem_15_1_correct`, for the algorithm of Section 15.4: the base
modulus of a stage is the product of `r - 1` greedy primes and the pool `Π'` of the certification
round is the rest of `Π`; then `Π'` is nonempty, every candidate modulus satisfies
"`2 ≤ mp < (2P)^r ≤ Λ_E σ`", each stage keeps at most half of the incidences (Lemma 15.11), and a
pair `(a, b)` is answered YES if and only if `S(a, b, c) = 0` for some `c` (Lemma 15.12), with `ℓ`
"the largest integer `l ≥ 0` with `P^l ≤ 3U`". -/
def Theorem_15_2_correct : Prop :=
  Assumptions.RosserSchoenfeld →
  ∀ ν ε : ℝ, 1 ≤ ν → 0 < ε → ε ≤ 1 / 2 → ∃ n₀ : ℕ,
    ∀ (n U r nA nB nC h : ℕ) (T : ETInst nA nB nC) (piece : Fin nC → Fin h),
    n₀ ≤ n → 1 ≤ U → (U : ℝ) ≤ (n : ℝ) ^ ν → 1 ≤ r → r ≤ rOf n → nC ≤ n →
    (∀ a b, |T.wab a b| ≤ U) → (∀ b c, |T.wbc b c| ≤ U) → (∀ a c, |T.wac a c| ≤ U) →
    let ζ := Real.log (3 * U)
    let Λ := 4 * (10 * ζ) ^ r
    let σ := ⌊Real.sqrt ((n : ℝ) ^ ε / Λ)⌋₊
    let P := ⌈4 * ζ * (4 * (σ : ℝ)) ^ (1 / (r : ℝ))⌉₊
    let ℓ := Nat.log P (3 * U)
    (∀ k, (univ.filter fun c => piece c = k).card ≤ σ) →
      (∀ S, ∃ ps : List ℕ, ps.length = r - 1 ∧ IsGreedy (valE T piece) S (primesIn P) ps) ∧
      (∀ (ps : List ℕ), (∀ p ∈ ps, p ∈ primesIn P) → ∀ l < r, ∀ p ∈ primesIn P,
        2 ≤ (ps.take l).prod * p ∧ ((ps.take l).prod * p : ℝ) < (2 * P) ^ r ∧
          ((2 * P : ℕ) : ℝ) ^ r ≤ Λ * σ) ∧
      ∀ (M : Finset (Fin nA × Fin nB × Fin h) → ℕ)
        (Pool : Finset (Fin nA × Fin nB × Fin h) → Finset ℕ),
        (∀ S, ∃ ps : List ℕ, ps.length = r - 1 ∧ IsGreedy (valE T piece) S (primesIn P) ps ∧
          M S = ps.prod ∧ Pool S = (primesIn P).filter fun p => p ∉ ps) →
        (∀ S, (Pool S).Nonempty) ∧
        (∀ S : Finset (Fin nA × Fin nB × Fin h),
          ((S.filter fun x => Uncert (valE T piece) (M S) (Pool S) ℓ x).card : ℝ) ≤ S.card / 2) ∧
        ∀ (L : ℕ) (a : Fin nA) (b : Fin nB),
          ((a, b) ∈ allEdges (valE T piece) (fun x => (x.1, x.2.1)) M Pool ℓ L univ ∅ ↔
            ∃ c, T.S a b c = 0)

/-! ## Appendix A -/

/-! ### A.8 Vrana's partial product (Proposition A.11) -/

section VranaDefs

variable {R : Type} [CommRing R]

/-- The five terms of Vrana's border decomposition [Vra24, eq. (42)], as functions of the variables
`x = (x₁₁, x₁₂, x₂₁, x₂₂)`, `y`, `z` and of `ε`. -/
def vranaTerms (e x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22 : R) : Fin 5 → R
  | 0 => x12 * y12 * z12
  | 1 => -((x12 + e ^ 2 * x21) * (y12 + e ^ 2 * y21) * (z12 + e ^ 2 * z21))
  | 2 => e ^ 2 * x21 * (y12 + e * y11) * (z12 + e * z22)
  | 3 => e ^ 2 * (x12 + e * x22) * y21 * (z12 + e * z11)
  | 4 => e ^ 2 * (x12 + e * x11) * (y12 + e * y22) * z21

/-- `M_Λ := ∑_{(i,j,k) ∈ Λ} x_ij y_jk z_ki`, `Λ := [2]³ ∖ {(1,1,1), (2,2,2)}`. -/
def vranaM (x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22 : R) : R :=
  x11 * y12 * z21 + x12 * y21 * z11 + x12 * y22 * z21 + x21 * y11 * z12 + x21 * y12 * z22
    + x22 * y21 * z12

end VranaDefs

/-- Appendix A.8: "`τ₁ + ⋯ + τ₅ = ε³ M_Λ + O(ε⁴)` (expand)", with the remainder written out. -/
def Prop_A_11_identity : Prop :=
  ∀ {R : Type} [CommRing R] (e x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22 : R),
    ∑ i, vranaTerms e x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22 i
      = e ^ 3 * vranaM x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22
        + e ^ 4 * (-(e ^ 2 * x21 * y21 * z21) + x11 * y22 * z21 - x12 * y21 * z21
          + x21 * y11 * z22 - x21 * y12 * z21 - x21 * y21 * z12 + x22 * y21 * z11)

/-- Appendix A.8: "The substitution `x_ij ↦ y_ij ↦ z_ij ↦ x_ij` maps `M_Λ` to itself … and maps the
set of five terms to itself (`τ₃ ↦ τ₄ ↦ τ₅ ↦ τ₃`, and `τ₁`, `τ₂` fixed)". -/
def Prop_A_11_symmetry : Prop :=
  ∀ {R : Type} [CommRing R] (e x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22 : R),
    vranaM y11 y12 y21 y22 z11 z12 z21 z22 x11 x12 x21 x22
        = vranaM x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22 ∧
    let τ := vranaTerms e x11 x12 x21 x22 y11 y12 y21 y22 z11 z12 z21 z22
    let τσ := vranaTerms e y11 y12 y21 y22 z11 z12 z21 z22 x11 x12 x21 x22
    τσ 0 = τ 0 ∧ τσ 1 = τ 1 ∧ τσ 2 = τ 3 ∧ τσ 3 = τ 4 ∧ τσ 4 = τ 2

/-- The `x`-factor of the term `i` of Vrana's decomposition contains the output variable `o`
(outputs `0, 1, 2, 3` for `x₁₁, x₁₂, x₂₁, x₂₂`): `τ₁ ∋ x₁₂`; `τ₂ ∋ x₁₂, x₂₁`; `τ₃ ∋ x₂₁`;
`τ₄ ∋ x₁₂, x₂₂`; `τ₅ ∋ x₁₂, x₁₁`. -/
def vranaContains : Fin 5 → Fin 4 → Bool
  | 0, 1 => true
  | 1, 1 => true
  | 1, 2 => true
  | 2, 2 => true
  | 3, 1 => true
  | 3, 3 => true
  | 4, 1 => true
  | 4, 0 => true
  | _, _ => false

/-- **Proposition A.11**. "For every `L`, `m` and every set `W` of read output strings, the pruned
recursion of [ZT, Section 2.4.2] with decomposition (42) computes the products at at least
`|W| 2^{m/2-1} = |W| √D/2` leaves." Read output strings have an inner output (`x₁₂` or `x₂₁`) at
exactly `m` levels; the recursion computes the products at the leaves that contribute to a wanted
output (`Leaves(W)`). The proof gives `|W| (3/2)^m`, which is at least `|W| 2^{m/2-1}`; and with
`|W| = N²/√D = N² 2^{-m/2}` this is at least `N²/2`. -/
def Prop_A_11 : Prop :=
  ∀ (L m : ℕ) (W : Finset (Fin L → Fin 4)),
    (∀ w ∈ W, (Finset.univ.filter fun ℓ => w ℓ = 1 ∨ w ℓ = 2).card = m) →
    let leaves := Finset.univ.filter fun τ : Fin L → Fin 5 =>
      ∃ w ∈ W, ∀ ℓ, vranaContains (τ ℓ) (w ℓ) = true
    (W.card : ℝ) * (3 / 2) ^ m ≤ leaves.card ∧
    (W.card : ℝ) * 2 ^ ((m : ℝ) / 2 - 1) ≤ leaves.card ∧
    ∀ N : ℝ, (W.card : ℝ) = N ^ 2 * 2 ^ (-(m : ℝ) / 2) → N ^ 2 / 2 ≤ leaves.card

/-! ### A.3 The private-leaf inequality (Lemma A.1) -/

/-- **Lemma A.1**, the count. For a base identity whose terms `λ` have output forms that contain
(`contains λ o`) some of the outputs, `none` being `z₀` and `some o` the outer outputs: if `R₀`
terms are pure inner (they contain `z₀` and no outer output) and every outer output lies in at least
`R₁` terms that contain no other outer output, then "every selected output string `w` has at least
`R₀^m R₁^{L-m}` leaves that contribute to `w` and to no other selected output string" (selected:
`z₀` at exactly `m` levels). -/
def Lemma_A_1 : Prop :=
  ∀ {T O : Type} [Fintype T] [DecidableEq T] [Fintype O] [DecidableEq O]
    (contains : T → Option O → Prop) [∀ t o, Decidable (contains t o)] (R₀ R₁ L m : ℕ),
    R₀ ≤ (Finset.univ.filter fun t => contains t none ∧ ∀ o, ¬ contains t (some o)).card →
    (∀ o, R₁ ≤ (Finset.univ.filter fun t =>
      contains t (some o) ∧ ∀ o', o' ≠ o → ¬ contains t (some o')).card) →
    ∀ w : Fin L → Option O, (Finset.univ.filter fun ℓ => w ℓ = none).card = m →
      R₀ ^ m * R₁ ^ (L - m) ≤ (Finset.univ.filter fun τ : Fin L → T =>
        (∀ ℓ, contains (τ ℓ) (w ℓ)) ∧
        ∀ w' : Fin L → Option O, (Finset.univ.filter fun ℓ => w' ℓ = none).card = m →
          (∀ ℓ, contains (τ ℓ) (w' ℓ)) → w' = w).card

/-- **Lemma A.1**, the consequence: "with `|W| = N²/√D` wanted entries, `D = q₀^m`, the pruned
recursion computes the products at at least `N² D^{-1/2} R₀^m R₁^{L-m}` leaves, which is at least
`N²` unless `R₀² R₁^{2(c-1)} < q₀`" (`L = cm`, so `2(c-1) = 2(L-m)/m`). -/
def Lemma_A_1_consequence : Prop :=
  ∀ (N q₀ R₀ R₁ : ℝ) (m L : ℕ), 0 < N → 1 ≤ q₀ → 0 ≤ R₀ → 0 ≤ R₁ → 1 ≤ m → m ≤ L →
    N ^ 2 / Real.sqrt (q₀ ^ m) * (R₀ ^ m * R₁ ^ (L - m)) < N ^ 2 →
      R₀ ^ 2 * R₁ ^ (2 * ((L : ℝ) - m) / m) < q₀



/-- Appendix A.1, after the private-leaf condition: "When `R₀ ≥ 1` this excludes `R₁ ≥ 2` for every
inner length `q₀ ≤ 4^{c-1}`, and for `R₁ ≥ 1` it gives `R₀ < √q₀`" (the condition being
`R₀² R₁^{2(c-1)} < q₀`, with `c ≥ 1`). -/
def Sec_A_1_private_consequences : Prop :=
  ∀ (R₀ R₁ q₀ c : ℝ), 1 ≤ c → 0 ≤ R₀ → R₀ ^ 2 * R₁ ^ (2 * (c - 1)) < q₀ →
    (1 ≤ R₀ → 2 ≤ R₁ → ¬ q₀ ≤ 4 ^ (c - 1)) ∧ (1 ≤ R₁ → R₀ < Real.sqrt q₀)

/-! ### A.4 Exact identities with disjoint inner variables (Proposition A.2)

A trilinear form is given by its coefficients. The left variables are `x_i` (`Sum.inl i`, `i < k`)
and `p_s` (`Sum.inr s`, `s < q₀`), the right ones `y_j` and `q_s`, the outputs `z_ij`
(`some (i, j)`) and `z₀` (`none`). A decomposition with `R` terms is given by the coefficient vectors
`φ_t`, `ψ_t`, `χ_t` of its linear forms, over any field. -/

section ExactDefs

variable {K : Type} [Field K]

/-- The coefficients of `G(k, n, q₀) = ⟨k,1,n⟩ ⊕ ⟨1,q₀,1⟩ = ∑ x_i y_j z_ij + ∑_s p_s q_s z₀`. -/
def gTensor (k n q : ℕ) : (Fin k ⊕ Fin q) → (Fin n ⊕ Fin q) → Option (Fin k × Fin n) → K
  | .inl i, .inl j, some o => if o = (i, j) then 1 else 0
  | .inr s, .inr t, none => if s = t then 1 else 0
  | _, _, _ => 0

/-- The coefficients of `∑_t φ_t ψ_t χ_t`. -/
def decompTensor {R : ℕ} {Lv Rv O : Type} (φ : Fin R → Lv → K) (ψ : Fin R → Rv → K)
    (χ : Fin R → O → K) : Lv → Rv → O → K :=
  fun l r o => ∑ t, φ t l * ψ t r * χ t o

/-- The class of a left or right variable: `0` for `x_i`, `y_j`, `1` for `p_s`, `q_s`. -/
def varClass {m q : ℕ} : Fin m ⊕ Fin q → ℤ := Sum.elim (fun _ => 0) (fun _ => 1)

/-- The class of an output: `0` for `z_ij`, `1` for `z₀`. -/
def outClass {k n : ℕ} : Option (Fin k × Fin n) → ℤ
  | some _ => 0
  | none => 1

end ExactDefs

/-- "We call the error `E` … *harmless* if the directions of the monomials of `E` lie in one open
half-plane of `ℝ²`", the direction of `abz` being `(cl(a) - cl(z), cl(b) - cl(z))`. -/
def Harmless {K : Type} [Field K] {k n q : ℕ}
    (E : (Fin k ⊕ Fin q) → (Fin n ⊕ Fin q) → Option (Fin k × Fin n) → K) : Prop :=
  ∃ α β : ℝ, ∀ l r o, E l r o ≠ 0 →
    0 < α * ((varClass l - outClass o : ℤ) : ℝ) + β * ((varClass r - outClass o : ℤ) : ℝ)

/-- **Proposition A.2**. "Let `k, n ≥ 2` and let `∑_{λ=1}^R φ_λ ψ_λ χ_λ = G(k,n,q₀) + E` be an
exact identity with a harmless error `E`. Then `q₀ ≤ R - k - n`." Over any field. -/
def Prop_A_2 : Prop :=
  ∀ {K : Type} [Field K] (k n q R : ℕ) (φ : Fin R → Fin k ⊕ Fin q → K)
    (ψ : Fin R → Fin n ⊕ Fin q → K) (χ : Fin R → Option (Fin k × Fin n) → K),
    2 ≤ k → 2 ≤ n →
    Harmless (fun l r o => decompTensor φ ψ χ l r o - gTensor k n q l r o) →
    q + k + n ≤ R ∧ q ≤ R - k - n

/-! ### A.5 Border identities: the inductions of Propositions A.4, A.5 and Remarks A.6, A.7

Border rank is not defined here. The propositions are proved by induction from three facts about
the border ranks `brG k n q` of `G(k,n,q)` and `brS k n q'` of `S(k,n,q')`, which are hypotheses:
the flattening bounds of the proofs (independent slices), and the substitution step, which is
Lemma A.3 (border substitution with a solvable symmetry group, from [LM17] and Borel's fixed point
theorem) together with the paper's determination of the fixed lines and of the quotients
(`G/x₁ ≅ G(k-1,n,q)`, `G/p₁ ≅ G(k,n,q-1)`, `S/c ≅ G(k,n,q')`). What is checked is the induction and
the arithmetic of the consequences. -/

/-- **Proposition A.4**. "For `k, n ≥ 1` and `q₀ ≥ (k-1)(n-1)+1`, `R(G(k,n,q₀)) ≥ q₀+k+n-1`. Hence
a border identity with `R` terms for `G(k,n,q₀)` has `q₀ ≤ R-k-n+1`." Hypotheses: for `k = 1` the
`n + q₀` right slices; the `kn` output slices `x_iy_j`, and `kn + 1` with `∑ p_s q_s` when
`q₀ ≥ 1`; the substitution step `R(G(k,n,q)) ≥ 1 + min(R(G(k-1,n,q)), R(G(k,n,q-1)))` for
`k ≥ 2`, `q ≥ 1`. -/
def Prop_A_4 : Prop :=
  ∀ brG : ℕ → ℕ → ℕ → ℕ,
    (∀ n q, n + q ≤ brG 1 n q) →
    (∀ k n q, k * n ≤ brG k n q) → (∀ k n q, 1 ≤ q → k * n + 1 ≤ brG k n q) →
    (∀ k n q, 2 ≤ k → 1 ≤ q → 1 + min (brG (k - 1) n q) (brG k n (q - 1)) ≤ brG k n q) →
    (∀ k n q, 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q → q + k + n - 1 ≤ brG k n q) ∧
    (∀ k n q R, 1 ≤ k → 1 ≤ n → brG k n q ≤ R → q + k + n ≤ R + 1)

/-- **Proposition A.5**. "For `k, n ≥ 1` and `q₀' ≥ (k-1)(n-1)+1`, `R(S(k,n,q₀')) ≥ q₀'+k+n-1`.
Hence a border identity with `R` terms for `S(k,n,q₀')` has effective inner length
`q₀'+1 ≤ R-k-n+2`." Hypotheses: Proposition A.4's bound for `G`; for `k = 1` the `n + q₀'` right
slices; the `kn + 1` output slices `x_iy_j` and `∑ p_s q_s + c y₁`; the substitution step with the
three fixed lines `⟨x₁⟩`, `⟨p₁⟩`, `⟨c⟩`. -/
def Prop_A_5 : Prop :=
  ∀ brG brS : ℕ → ℕ → ℕ → ℕ,
    (∀ k n q, 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q → q + k + n - 1 ≤ brG k n q) →
    (∀ n q, n + q ≤ brS 1 n q) → (∀ k n q, k * n + 1 ≤ brS k n q) →
    (∀ k n q, 2 ≤ k → 1 ≤ q →
      1 + min (min (brS (k - 1) n q) (brS k n (q - 1))) (brG k n q) ≤ brS k n q) →
    (∀ k n q, 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q → q + k + n - 1 ≤ brS k n q) ∧
    (∀ k n q R, 1 ≤ k → 1 ≤ n → brS k n q ≤ R → (q + 1) + k + n ≤ R + 2)

/-- **Remark A.6** (a conditional improvement). "If `R(S(1,n,q₀')) ≥ n+q₀'+1` for all
`n, q₀' ≥ 1`, the same induction, with this base and with the outputs bound `kn+1 = q₀'+k+n-1` at
`q₀'-1 = (k-1)(n-1)`, gives `R(S(k,n,q₀')) ≥ q₀'+k+n` for `q₀' ≥ (k-1)(n-1)+1`, so one shared
variable gives effective inner length at most `R-k-n+1`." -/
def Remark_A_6 : Prop :=
  ∀ brG brS : ℕ → ℕ → ℕ → ℕ,
    (∀ k n q, 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q → q + k + n - 1 ≤ brG k n q) →
    (∀ n q, 1 ≤ n → 1 ≤ q → n + q + 1 ≤ brS 1 n q) → (∀ k n q, k * n + 1 ≤ brS k n q) →
    (∀ k n q, 2 ≤ k → 1 ≤ q →
      1 + min (min (brS (k - 1) n q) (brS k n (q - 1))) (brG k n q) ≤ brS k n q) →
    (∀ k n q, 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q → q + k + n ≤ brS k n q) ∧
    (∀ k n q R, 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q → brS k n q ≤ R →
      (q + 1) + k + n ≤ R + 1)

/-- **Remark A.7** (the cases `(2,2)`, `(2,3)`, `(3,3)`), the deduction. From the computed Koszul
bounds `R(S(2,2,2)) ≥ 6`, `R(S(2,3,3)) ≥ 8`, `R(S(2,3,5)) ≥ 10`, `R(S(2,2,3)) ≥ 7` (hypotheses: kind
C, computer calculations), Proposition A.4, the output bound `kn+1`, the substitution step and
"`S(k,n,q₀'-1) = S(k,n,q₀')/p_{q₀'}` and border rank does not increase under this map": "they give
`R(S(3,3,5)) ≥ 11` … Likewise `R(S(3,2,3)) ≥ 8` … these exclude with `kn+1` terms any effective
inner length beyond `(k-1)(n-1)+1` for `(k,n) = (2,2), (2,3), (3,3)`". -/
def Remark_A_7 : Prop :=
  ∀ brG brS : ℕ → ℕ → ℕ → ℕ,
    (∀ k n q, 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q → q + k + n - 1 ≤ brG k n q) →
    (∀ k n q, k * n + 1 ≤ brS k n q) →
    (∀ k n q, 2 ≤ k → 1 ≤ q →
      1 + min (min (brS (k - 1) n q) (brS k n (q - 1))) (brG k n q) ≤ brS k n q) →
    (∀ k n q, brS k n q ≤ brS k n (q + 1)) →
    6 ≤ brS 2 2 2 → 8 ≤ brS 2 3 3 → 10 ≤ brS 2 3 5 → 7 ≤ brS 2 2 3 →
    11 ≤ brS 3 3 5 ∧ 8 ≤ brS 3 2 3 ∧
    (∀ q, 2 ≤ q → 2 * 2 + 1 < brS 2 2 q) ∧
    (∀ q, 3 ≤ q → 2 * 3 + 1 < brS 2 3 q ∧ 3 * 2 + 1 < brS 3 2 q) ∧
    (∀ q, 5 ≤ q → 3 * 3 + 1 < brS 3 3 q)



/-! ### A.5, the fixed lines and the quotients of Propositions A.4 and A.5

The finite linear algebra of the proofs: the group `𝓑` fixes the tensor, its fixed lines in the
left space are `⟨x₁⟩`, `⟨p₁⟩` (and `⟨c⟩` for `S`), and the quotients are the smaller tensors. A
tensor is its coefficient array on finite index sets; a triple of matrices acts on the three
factors (`tAct`); the quotient by a line `⟨a⟩` of the left space is written on the same index set,
with the coordinate `c` where `a_c ≠ 0` eliminated (`quot0`), which is `T/a` composed with an
injective map, so it has the same border rank. Lemma A.3 itself (from [LM17] and Borel's fixed
point theorem) stays a hypothesis (`Lemma_A_3_form`), and so do "`𝓑` is connected and solvable"
(`Solv`) and the invariance of border rank under padding by zero slices. -/

section BorderLA

variable {K : Type} [Field K]

/-- The action of `(g_A, g_B, g_C)` on a tensor: `(g · T)[a', b', c'] =
∑ g_A[a', a] g_B[b', b] g_C[c', c] T[a, b, c]` (the matrices act on the basis vectors by their
columns). -/
def tAct {A B C : Type} [Fintype A] [Fintype B] [Fintype C] (gA : Matrix A A K)
    (gB : Matrix B B K) (gC : Matrix C C K) (T : A → B → C → K) : A → B → C → K :=
  fun a' b' c' => ∑ a, ∑ b, ∑ c, gA a' a * gB b' b * gC c' c * T a b c

/-- `T/a` on the left index set: with `c` a coordinate where `a_c ≠ 0`, the slice at `c` is
eliminated by `e_c ≡ -(1/a_c) ∑_{a' ≠ c} a_{a'} e_{a'}` modulo `a`. -/
noncomputable def quot0 {A B C : Type} [DecidableEq A] (T : A → B → C → K) (a : A → K) :
    A → B → C → K :=
  open Classical in
  if h : ∃ c, a c ≠ 0 then
    fun x b o => if x = h.choose then 0 else T x b o - a x / a h.choose * T h.choose b o
  else T

/-- `T'` on larger index sets, through injective maps of the indices (zero elsewhere). -/
noncomputable def tExtend {A' B' C' A B C : Type} (eA : A' → A) (eB : B' → B) (eC : C' → C)
    (T' : A' → B' → C' → K) : A → B → C → K :=
  open Classical in
  fun a b c => if h : (∃ a', eA a' = a) ∧ (∃ b', eB b' = b) ∧ (∃ c', eC c' = c) then
    T' h.1.choose h.2.1.choose h.2.2.choose else 0

/-- Upper triangular. -/
def UpperTri {m : ℕ} (U : Matrix (Fin m) (Fin m) K) : Prop := ∀ i j : Fin m, j < i → U i j = 0

/-- The action on the outputs: the inverse transpose of `U` on the first index of `z_ij`, times `v`
when `j = 1` (`y₁`), and `z₀` fixed. -/
noncomputable def outAct {k n : ℕ} (U : Matrix (Fin k) (Fin k) K) (v : K) :
    Matrix (Option (Fin k × Fin n)) (Option (Fin k × Fin n)) K
  | some (i', j'), some (i, j) => if j' = j then U⁻¹ i i' * (if (j : ℕ) = 0 then v else 1) else 0
  | none, none => 1
  | _, _ => 0

/-- The group of the proof of Proposition A.4: "pairs of invertible upper-triangular matrices
acting on `x₁, …, x_k` (with the inverse transpose on the first index of the `z_ij`) and on
`p₁, …, p_{q₀}` (with the inverse transpose on the `q_s`)". -/
def B_G (K : Type) [Field K] (k n q : ℕ) :
    Set (Matrix (Fin k ⊕ Fin q) (Fin k ⊕ Fin q) K × Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) K ×
      Matrix (Option (Fin k × Fin n)) (Option (Fin k × Fin n)) K) :=
  {g | ∃ (U : Matrix (Fin k) (Fin k) K) (W : Matrix (Fin q) (Fin q) K), UpperTri U ∧ UpperTri W ∧
    IsUnit U.det ∧ IsUnit W.det ∧
    g = (Matrix.fromBlocks U 0 0 W, Matrix.fromBlocks 1 0 0 (W⁻¹).transpose, outAct U 1)}

/-- `S(k, n, q₀') = ∑ x_i y_j z_ij + ∑_s p_s q_s z₀ + c y₁ z₀`; the left variables are the `x_i`,
the `p_s` and `c` (`Fin k ⊕ (Fin q ⊕ Unit)`), `y₁` is the right index `0`. -/
def sTensor (k n q : ℕ) : (Fin k ⊕ (Fin q ⊕ Unit)) → (Fin n ⊕ Fin q) → Option (Fin k × Fin n) → K
  | .inl i, .inl j, some o => if o = (i, j) then 1 else 0
  | .inr (.inl s), .inr t, none => if s = t then 1 else 0
  | .inr (.inr _), .inl j, none => if (j : ℕ) = 0 then 1 else 0
  | _, _, _ => 0

/-- The group of the proof of Proposition A.5: the changes of Proposition A.4 and "the scalings
`c ↦ vc`, `y₁ ↦ v⁻¹y₁`, `z_{i1} ↦ vz_{i1}` for all `i`". -/
def B_S (K : Type) [Field K] (k n q : ℕ) :
    Set (Matrix (Fin k ⊕ (Fin q ⊕ Unit)) (Fin k ⊕ (Fin q ⊕ Unit)) K ×
      Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) K ×
      Matrix (Option (Fin k × Fin n)) (Option (Fin k × Fin n)) K) :=
  {g | ∃ (U : Matrix (Fin k) (Fin k) K) (W : Matrix (Fin q) (Fin q) K) (v : K), UpperTri U ∧
    UpperTri W ∧ IsUnit U.det ∧ IsUnit W.det ∧ v ≠ 0 ∧
    g = (Matrix.fromBlocks U 0 0 (Matrix.fromBlocks W 0 0 (Matrix.diagonal fun _ => v)),
      Matrix.fromBlocks (Matrix.diagonal fun j : Fin n => if (j : ℕ) = 0 then v⁻¹ else 1) 0 0 (W⁻¹).transpose,
      outAct U v)}

/-- "A `𝓑`-fixed line": `⟨a⟩` with `g_A a ∈ ⟨a⟩` for every `g ∈ 𝓑`. -/
def FixedLine {A B C : Type} [Fintype A] (𝓑 : Set (Matrix A A K × Matrix B B K × Matrix C C K))
    (a : A → K) : Prop :=
  a ≠ 0 ∧ ∀ g ∈ 𝓑, ∃ l : K, g.1.mulVec a = l • a

end BorderLA

/-- Proposition A.4, the group: "The group `𝓑` … fixes `G(k, n, q₀)`". -/
def Prop_A_4_fixes : Prop :=
  ∀ (K : Type) [Field K] (k n q : ℕ), ∀ g ∈ B_G K k n q, tAct g.1 g.2.1 g.2.2 (gTensor k n q) = gTensor k n q

/-- Proposition A.4, the fixed lines: "the fixed lines are `⟨x₁⟩` and `⟨p₁⟩`" (for `k, q ≥ 1`, over
a field of characteristic `0`). -/
def Prop_A_4_lines : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (k n q : ℕ) (hk : 0 < k) (hq : 0 < q) (a : Fin k ⊕ Fin q → K),
    FixedLine (B_G K k n q) a ↔
      ∃ α : K, α ≠ 0 ∧ (a = α • (Pi.single (Sum.inl ⟨0, hk⟩) 1 : Fin k ⊕ Fin q → K) ∨
        a = α • (Pi.single (Sum.inr ⟨0, hq⟩) 1 : Fin k ⊕ Fin q → K))

/-- Proposition A.4, the quotients: "`G/x₁ ≅ G(k-1, n, q₀)` and `G/p₁ ≅ G(k, n, q₀-1)`", as
`G(k-1, n, q₀)` and `G(k, n, q₀-1)` padded by zero slices; the quotient does not depend on the
generator `α e_c` of a coordinate line. -/
def Prop_A_4_quotients : Prop :=
  ∀ (K : Type) [Field K] (k n q : ℕ),
    quot0 (gTensor (k + 1) n q) (Pi.single (Sum.inl 0) (1 : K) : Fin (k + 1) ⊕ Fin q → K)
      = tExtend (Sum.map Fin.succ id) id (Option.map (Prod.map Fin.succ id)) (gTensor k n q) ∧
    quot0 (gTensor k n (q + 1)) (Pi.single (Sum.inr 0) (1 : K) : Fin k ⊕ Fin (q + 1) → K)
      = tExtend (Sum.map id Fin.succ) (Sum.map id Fin.succ) id (gTensor k n q) ∧
    ∀ {A B C : Type} [DecidableEq A] (T : A → B → C → K) (c : A) (α : K), α ≠ 0 →
      quot0 T (α • (Pi.single c 1 : A → K)) = quot0 T (Pi.single c 1 : A → K)

/-- Proposition A.5, the group, the fixed lines `⟨x₁⟩`, `⟨p₁⟩`, `⟨c⟩` and the quotients
"`S/x₁ ≅ S(k-1, n, q₀')`, `S/p₁ ≅ S(k, n, q₀'-1)` and `S/c ≅ G(k, n, q₀')`". -/
def Prop_A_5_linalg : Prop :=
  ∀ (K : Type) [Field K],
    (∀ k n q, ∀ g ∈ B_S K k n q, tAct g.1 g.2.1 g.2.2 (sTensor k n q) = sTensor k n q) ∧
    (CharZero K → ∀ (k n q : ℕ) (hk : 0 < k) (hq : 0 < q) (a : Fin k ⊕ (Fin q ⊕ Unit) → K),
      FixedLine (B_S K k n q) a ↔
        ∃ α : K, α ≠ 0 ∧ (a = α • (Pi.single (Sum.inl ⟨0, hk⟩) 1 : Fin k ⊕ (Fin q ⊕ Unit) → K) ∨
          a = α • (Pi.single (Sum.inr (Sum.inl ⟨0, hq⟩)) 1 : Fin k ⊕ (Fin q ⊕ Unit) → K) ∨
          a = α • (Pi.single (Sum.inr (Sum.inr ())) 1 : Fin k ⊕ (Fin q ⊕ Unit) → K))) ∧
    (∀ k n q : ℕ,
      quot0 (sTensor (k + 1) n q)
          (Pi.single (Sum.inl 0) (1 : K) : Fin (k + 1) ⊕ (Fin q ⊕ Unit) → K)
        = tExtend (Sum.map Fin.succ id) id (Option.map (Prod.map Fin.succ id)) (sTensor k n q) ∧
      quot0 (sTensor k n (q + 1))
          (Pi.single (Sum.inr (Sum.inl 0)) (1 : K) : Fin k ⊕ (Fin (q + 1) ⊕ Unit) → K)
        = tExtend (Sum.map id (Sum.map Fin.succ id)) (Sum.map id Fin.succ) id (sTensor k n q) ∧
      quot0 (sTensor k n q) (Pi.single (Sum.inr (Sum.inr ())) (1 : K) : Fin k ⊕ (Fin q ⊕ Unit) → K)
        = tExtend (Sum.map id Sum.inl) id id (gTensor k n q))

/-- Lemma A.3, as a hypothesis on a border-rank function `br` and on a class `Solv` of groups
("connected solvable linear algebraic groups"): "Let `T ≠ 0` have `R(T) ≤ r`, and let `𝓑` be a
connected solvable linear algebraic group acting on `A`, `B` and `C` and fixing `T`. Then some
`𝓑`-fixed line `⟨a⟩ ⊆ A` has `R(T/a) ≤ r-1`", with `r = R(T)`. -/
def Lemma_A_3_form {K : Type} [Field K]
    (br : ∀ {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A], (A → B → C → K) → ℕ)
    (Solv : ∀ {A B C : Type}, Set (Matrix A A K × Matrix B B K × Matrix C C K) → Prop) : Prop :=
  ∀ {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A] (T : A → B → C → K)
    (𝓑 : Set (Matrix A A K × Matrix B B K × Matrix C C K)),
    Solv 𝓑 → (∀ g ∈ 𝓑, tAct g.1 g.2.1 g.2.2 T = T) → T ≠ 0 →
      ∃ a : A → K, FixedLine 𝓑 a ∧ br (quot0 T a) + 1 ≤ br T

/-- Border rank does not change when a tensor is padded by zero slices (written on larger index
sets through injective maps). -/
def BrPadInvariant {K : Type} [Field K]
    (br : ∀ {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A], (A → B → C → K) → ℕ) :
    Prop :=
  ∀ {A' B' C' A B C : Type} [Fintype A'] [Fintype B'] [Fintype C'] [DecidableEq A'] [Fintype A]
    [Fintype B] [Fintype C] [DecidableEq A] (eA : A' → A) (eB : B' → B) (eC : C' → C),
    Function.Injective eA → Function.Injective eB → Function.Injective eC →
    ∀ T' : A' → B' → C' → K, br (tExtend eA eB eC T') = br T'

/-- **Proposition A.4, composed**: from Lemma A.3 (`Lemma_A_3_form`), "`𝓑` is connected and
solvable", the invariance under padding and the flattening bounds of the proof, the bound
`R(G(k,n,q₀)) ≥ q₀+k+n-1` for `q₀ ≥ (k-1)(n-1)+1` and its consequence; the substitution step is
derived from the fixed lines and the quotients. -/
def Prop_A_4_composed : Prop :=
  ∀ (K : Type) [Field K] [CharZero K]
    (br : ∀ {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A], (A → B → C → K) → ℕ)
    (Solv : ∀ {A B C : Type}, Set (Matrix A A K × Matrix B B K × Matrix C C K) → Prop),
    Lemma_A_3_form br Solv → BrPadInvariant br → (∀ k n q, Solv (B_G K k n q)) →
    (∀ n q, n + q ≤ br (gTensor (K := K) 1 n q)) →
    (∀ k n q, k * n ≤ br (gTensor (K := K) k n q)) →
    (∀ k n q, 1 ≤ q → k * n + 1 ≤ br (gTensor (K := K) k n q)) →
    (∀ k n q, 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q → q + k + n - 1 ≤ br (gTensor (K := K) k n q)) ∧
    (∀ k n q R, 1 ≤ k → 1 ≤ n → br (gTensor (K := K) k n q) ≤ R → q + k + n ≤ R + 1)

/-- **Proposition A.5, composed**: as `Prop_A_4_composed`, with the three fixed lines of `S`; the
bound for `G` is Proposition A.4, composed. -/
def Prop_A_5_composed : Prop :=
  ∀ (K : Type) [Field K] [CharZero K]
    (br : ∀ {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [DecidableEq A], (A → B → C → K) → ℕ)
    (Solv : ∀ {A B C : Type}, Set (Matrix A A K × Matrix B B K × Matrix C C K) → Prop),
    Lemma_A_3_form br Solv → BrPadInvariant br → (∀ k n q, Solv (B_G K k n q)) →
    (∀ k n q, Solv (B_S K k n q)) →
    (∀ n q, n + q ≤ br (gTensor (K := K) 1 n q)) →
    (∀ k n q, k * n ≤ br (gTensor (K := K) k n q)) →
    (∀ k n q, 1 ≤ q → k * n + 1 ≤ br (gTensor (K := K) k n q)) →
    (∀ n q, n + q ≤ br (sTensor (K := K) 1 n q)) →
    (∀ k n q, k * n + 1 ≤ br (sTensor (K := K) k n q)) →
    (∀ k n q, 1 ≤ k → 1 ≤ n → (k - 1) * (n - 1) + 1 ≤ q → q + k + n - 1 ≤ br (sTensor (K := K) k n q)) ∧
    (∀ k n q R, 1 ≤ k → 1 ≤ n → br (sTensor (K := K) k n q) ≤ R → (q + 1) + k + n ≤ R + 2)

/-! ### A.6 At most one shared variable (Lemma A.8, Theorem A.9)

Linear forms in the entries of `X` are vectors indexed by the entries `IX`, those in the entries of
`Y` vectors indexed by `IY`; the entry `X[ρ,t]` is the variable `ex (ρ, t)` and `Y[t,σ]` is
`ey (t, σ)`, for injective `ex`, `ey`. A bilinear form `∑ α_ι β_ι` is the matrix
`∑ α_ι β_ιᵀ`. -/

section SharedDefs

variable {K : Type} [Field K] {IX IY Rows Inner Cols : Type} [DecidableEq IX] [DecidableEq IY]

/-- The bilinear form `∑_{t ∈ Θ} X[ρ,t] Y[t,σ]` of an entry `(ρ,σ)` and a block `Θ`. -/
def blockForm (ex : Rows × Inner → IX) (ey : Inner × Cols → IY) (ρ : Rows) (σ : Cols)
    (Θ : Finset Inner) : Matrix IX IY K :=
  ∑ t ∈ Θ, Matrix.vecMulVec (Pi.single (ex (ρ, t)) 1) (Pi.single (ey (t, σ)) 1)

end SharedDefs

/-- **Lemma A.8**. "Let `o = ∑_ι a[v_ι] b[w_ι]` be a correct single output with entry and block
`((ρ,σ),Θ)`. (A) The forms `a[v_ι]` span `span{X[ρ,t] : t ∈ Θ}` and the forms `b[w_ι]` span
`span{Y[t,σ] : t ∈ Θ}`; in particular each of them is nonzero. (B) The forms `a[v_ι]` are linearly
independent, and if `∑_ι a[v_ι] β_ι = ∑_ι a[v_ι] β'_ι` for linear forms `β_ι, β'_ι` in the entries
of `Y`, then `β_ι = β'_ι` for every `ι`. (C) The forms `b[w_ι]` are linearly independent." The
`D` inner indices are the elements of `ι`, and `|Θ| = D`. -/
def Lemma_A_8 : Prop :=
  ∀ {K : Type} [Field K] {IX IY Rows Inner Cols ι : Type} [Fintype IX] [Fintype IY]
    [DecidableEq IX] [DecidableEq IY] [DecidableEq Inner] [Fintype ι]
    (ex : Rows × Inner → IX) (ey : Inner × Cols → IY), Function.Injective ex →
    Function.Injective ey → ∀ (a : ι → IX → K) (b : ι → IY → K) (ρ : Rows) (σ : Cols)
    (Θ : Finset Inner), Θ.card = Fintype.card ι →
    ∑ κ, Matrix.vecMulVec (a κ) (b κ) = blockForm ex ey ρ σ Θ →
    Submodule.span K (Set.range a) =
        Submodule.span K ((fun t => (Pi.single (ex (ρ, t)) 1 : IX → K)) '' ↑Θ) ∧
      Submodule.span K (Set.range b) =
        Submodule.span K ((fun t => (Pi.single (ey (t, σ)) 1 : IY → K)) '' ↑Θ) ∧
      (∀ κ, a κ ≠ 0) ∧ (∀ κ, b κ ≠ 0) ∧ LinearIndependent K a ∧
      (∀ β β' : ι → IY → K, ∑ κ, Matrix.vecMulVec (a κ) (β κ) = ∑ κ, Matrix.vecMulVec (a κ) (β' κ) →
        β = β') ∧
      LinearIndependent K b

/-- A run of a base identity whose inner form is a sum of disjoint letter pairs (Section A.6).
The left letters form the type `AL`, among them the outer ones `xo i` (`i : OL`); likewise on
the right; the letter pairs `u_r v_r` of `F` are `(lp r, rp r)`, `r : Pr`, with distinct left and
distinct right letters (`lp`, `rp` injective). The arrays `a`, `b` give a linear form in the entries
of `X`, resp. `Y`, for every left, resp. right, string of `L` letters. -/
structure SharedRun (K : Type) [Field K] (IX IY : Type) (L : ℕ) where
  AL : Type
  AR : Type
  OL : Type
  OR : Type
  Pr : Type
  [fintypePr : Fintype Pr]
  [decPr : DecidableEq Pr]
  xo : OL → AL
  yo : OR → AR
  lp : Pr → AL
  rp : Pr → AR
  lp_inj : Function.Injective lp
  rp_inj : Function.Injective rp
  a : (Fin L → AL) → IX → K
  b : (Fin L → AR) → IY → K

attribute [instance] SharedRun.fintypePr SharedRun.decPr

namespace SharedRun

variable {K : Type} [Field K] {IX IY : Type} {L : ℕ} (run : SharedRun K IX IY L)

/-- The left string `v_ι` of an output `(Q, I, J)` at the inner index `ι`: the left letter of the
pair `ι_ℓ` on `Q`, the outer letter `I_ℓ` elsewhere. (`I` is read only outside `Q`.) -/
def leftStr (Q : Finset (Fin L)) (I : Fin L → run.OL) (ι : ↥Q → run.Pr) : Fin L → run.AL :=
  fun ℓ => if h : ℓ ∈ Q then run.lp (ι ⟨ℓ, h⟩) else run.xo (I ℓ)

/-- The right string `w_ι`. -/
def rightStr (Q : Finset (Fin L)) (J : Fin L → run.OR) (ι : ↥Q → run.Pr) : Fin L → run.AR :=
  fun ℓ => if h : ℓ ∈ Q then run.rp (ι ⟨ℓ, h⟩) else run.yo (J ℓ)

/-- "Reading the coefficient of the output string in `T^{⊗L}` level by level, the run computes
`o = ∑_ι a[v_ι] b[w_ι]`", as a bilinear form in the entries of `X` and `Y`.

NOTE. This formula is the paper's description of the output; it is the definition here. -/
def output (Q : Finset (Fin L)) (I : Fin L → run.OL) (J : Fin L → run.OR) : Matrix IX IY K :=
  ∑ ι : ↥Q → run.Pr, Matrix.vecMulVec (run.a (run.leftStr Q I ι)) (run.b (run.rightStr Q J ι))

/-- `o = (Q, I, J)` is a correct single output with entry `(ρ, σ)` and block `Θ`:
`o = ∑_{t∈Θ} X[ρ,t] Y[t,σ]` with `|Θ| = D`, the number of inner indices. -/
def CorrectSingle {Rows Inner Cols : Type} [DecidableEq IX] [DecidableEq IY]
    (ex : Rows × Inner → IX) (ey : Inner × Cols → IY) (Q : Finset (Fin L)) (I : Fin L → run.OL)
    (J : Fin L → run.OR) (ρ : Rows) (σ : Cols) (Θ : Finset Inner) : Prop :=
  Θ.card = Fintype.card (↥Q → run.Pr) ∧ run.output Q I J = blockForm ex ey ρ σ Θ

end SharedRun

/-- **Theorem A.9**. "Consider a run as above whose products are indexed by a family of inner sets
of size `m` with at least two members, and in which every output `(Q,I,J)`, `Q` in the family and
`I, J` arbitrary, is a correct single output of a distinct entry and block. (a) No two right
variables are shared (and, by symmetry, no two left variables). This part does not use that the
entries and blocks are distinct. (b) If, moreover, for every entry the blocks of the outputs that
compute it are pairwise disjoint, then no left and right variable are both shared."

A right variable is shared if it is an outer letter `yo j` and the right letter `rp r` of a pair.
The hypothesis of (b) is used in the form: two outputs of the products `Q`, `Q'` that compute the
same entry with overlapping blocks have `Q = Q'` (outputs of distinct products are distinct). The
alphabets of outer letters are nonempty (`k, n ≥ 1`). -/
def Theorem_A_9 : Prop :=
  ∀ {K : Type} [Field K] {IX IY Rows Inner Cols : Type} [Fintype IX] [Fintype IY]
    [DecidableEq IX] [DecidableEq IY] [DecidableEq Inner] {L m : ℕ} (run : SharedRun K IX IY L)
    (ex : Rows × Inner → IX) (ey : Inner × Cols → IY), Function.Injective ex →
    Function.Injective ey → Nonempty run.OL → Nonempty run.OR →
    ∀ 𝒬 : Finset (Finset (Fin L)), (∀ Q ∈ 𝒬, Q.card = m) → 1 < 𝒬.card →
    (∀ Q ∈ 𝒬, ∀ I J, ∃ ρ σ Θ, run.CorrectSingle ex ey Q I J ρ σ Θ) →
    -- (a), right
    (∀ r₁ r₂ : run.Pr, r₁ ≠ r₂ → ¬ ((∃ j, run.rp r₁ = run.yo j) ∧ (∃ j, run.rp r₂ = run.yo j))) ∧
    -- (a), left
    (∀ r₁ r₂ : run.Pr, r₁ ≠ r₂ → ¬ ((∃ i, run.lp r₁ = run.xo i) ∧ (∃ i, run.lp r₂ = run.xo i))) ∧
    -- (b)
    ((∀ Q ∈ 𝒬, ∀ Q' ∈ 𝒬, ∀ I J I' J' ρ σ Θ Θ', run.CorrectSingle ex ey Q I J ρ σ Θ →
        run.CorrectSingle ex ey Q' I' J' ρ σ Θ' → (Θ ∩ Θ').Nonempty → Q = Q') →
      ∀ r₁ r₂ : run.Pr, ¬ ((∃ i, run.lp r₁ = run.xo i) ∧ (∃ j, run.rp r₂ = run.yo j)))

/-! ### A.7 The normal form of the inner form (Lemma A.10)

The left space is `K^a`, the right space `K^b`, over any field `K`; the inner form `F` is the
matrix of its coefficients (`F i j` the coefficient of the `i`-th left and the `j`-th right
variable), so `F = ∑_r u_r ⊗ v_r` is `F = ∑_r u_r v_rᵀ`. Its left and right supports are the
column and the row space, and its rank is `F.rank`. `X` and `Y` are arbitrary subspaces (the paper's
`X`, `Y` are spanned by the outer variables). -/

/-- **Lemma A.10**, the decomposition. "In [the new bases] `F = ∑_{r=1}^{q₀} u_r ⊗ v_r` with distinct
basis vectors `u_1, …, u_{q₀}` and distinct basis vectors `v_1, …, v_{q₀}`; exactly `s_A` of the
`u_r` lie in `X` and exactly `s_B` of the `v_r` lie in `Y`." Stated intrinsically: the `u_r` are
independent, those of `S_A` lie in `X` and the others span a space meeting `X` only in `0` (so that,
by `Lemma_A_10_basis`, they extend to a basis whose first `dim X` vectors are a basis of `X`), and
likewise on the right; `|S_A| = s_A = dim(𝓛(F) ∩ X)` and `|S_B| = s_B = dim(𝓡(F) ∩ Y)`. -/
def Lemma_A_10 : Prop :=
  ∀ {K : Type} [Field K] {a b : ℕ} (F : Matrix (Fin a) (Fin b) K) (X : Submodule K (Fin a → K))
    (Y : Submodule K (Fin b → K)),
    ∃ (ι : Type) (_ : Fintype ι) (u : ι → Fin a → K) (v : ι → Fin b → K) (SA SB : Set ι),
      Fintype.card ι = F.rank ∧ LinearIndependent K u ∧ LinearIndependent K v ∧
      F = ∑ r, Matrix.vecMulVec (u r) (v r) ∧
      (∀ r ∈ SA, u r ∈ X) ∧ Disjoint (Submodule.span K (u '' SAᶜ)) X ∧
      (∀ r ∈ SB, v r ∈ Y) ∧ Disjoint (Submodule.span K (v '' SBᶜ)) Y ∧
      Nat.card SA = Module.finrank K ↥(LinearMap.range F.mulVecLin ⊓ X) ∧
      Nat.card SB = Module.finrank K ↥(LinearMap.range F.transpose.mulVecLin ⊓ Y)

/-- **Lemma A.10**, the bases. "So `{a_r : r ∈ T_V}` extends to a basis of `X`, which together with
`{a_r : r ∉ T_V}` is linearly independent and extends to a basis of the left space": an independent
family whose members in `S` lie in `X` and whose other members span a space meeting `X` only in `0`
is part of a basis `P` of `K^a` whose first `dim X` vectors lie in `X` (hence are a basis of `X`)
and whose other vectors do not; the change to `P` maps `X` to itself. -/
def Lemma_A_10_basis : Prop :=
  ∀ {K : Type} [Field K] {a : ℕ} {ι : Type} [Fintype ι] (u : ι → Fin a → K) (S : Set ι)
    (X : Submodule K (Fin a → K)),
    LinearIndependent K u → (∀ r ∈ S, u r ∈ X) → Disjoint (Submodule.span K (u '' Sᶜ)) X →
    ∃ (P : Module.Basis (Fin a) K (Fin a → K)) (σ : ι ↪ Fin a),
      (∀ r, P (σ r) = u r) ∧ (∀ i : Fin a, P i ∈ X ↔ (i : ℕ) < Module.finrank K X) ∧
      (∀ r, (σ r : ℕ) < Module.finrank K X ↔ r ∈ S)

/-! ### Section 7: balanced boxes (Lemma 7.1)

The `2L` levels are flattened to `Fin (L + L)`, the first half below the second (`Fin.append`):
"The levels are ordered `1, …, 2L`, the first half below the second, and *lower* in
[ZT, Lemmas 27-29] refers to this order" (Section 7, change (10)). The definitions follow
[ZT, Section 4.2] and its formalization in `3sum-apsp`, with the five terms of Lemma 3.1. -/

namespace Sq

open Finset

variable {N : ℕ}

/-- A leaf on `N` levels. -/
abbrev FLeaf (N : ℕ) : Type := Fin N → Tm
/-- An output string on `N` levels. -/
abbrev FOut (N : ℕ) : Type := Fin N → ZL

/-- The flattened leaf `τ = τ'τ''`. -/
def flatLeaf {L : ℕ} (τ : Leaf L) : FLeaf (L + L) := Fin.append τ.1 τ.2
/-- The flattened output string `w = w'w''`. -/
def flatOut {L : ℕ} (w : OutStr L) : FOut (L + L) := Fin.append w.1 w.2

/-- A leaf contributes to an output string if `χ_{τ_ℓ}` contains `w_ℓ` at every level. -/
def Contrib (τ : FLeaf N) (w : FOut N) : Prop := ∀ ℓ, chi (τ ℓ) (w ℓ) ≠ 0

instance (τ : FLeaf N) (w : FOut N) : Decidable (Contrib τ w) := by unfold Contrib; infer_instance

/-- `Q(w)`, the levels with `z₀`. -/
def innerSet (w : FOut N) : Finset (Fin N) := univ.filter fun ℓ => w ℓ = .z0

/-- The levels at which a leaf has `P₀`. -/
def P0Levels (τ : FLeaf N) : Finset (Fin N) := univ.filter fun ℓ => τ ℓ = .P0

/-- The order of a leaf for `M = 2m` inner levels: `M` minus its number of `P₀`'s. -/
def order (M : ℕ) (τ : FLeaf N) : ℤ := (M : ℤ) - ((P0Levels τ).card : ℤ)

/-- The term of the private leaf at an output letter: `P_ij` for `z_ij`, `P₀` for `z₀`. -/
def privTerm : ZL → Tm
  | .z i j => .P i j
  | .z0 => .P0

/-- The symbols of a cube: the five terms and a star. -/
inductive CSym : Type
  | term (t : Tm)
  | star
  deriving DecidableEq, Fintype

/-- A cube: a string of symbols. -/
abbrev Cube (N : ℕ) : Type := Fin N → CSym

/-- `τ` is a leaf of `π`: at every level `π` has a star or the term of `τ`. -/
def Cube.HasLeaf (π : Cube N) (τ : FLeaf N) : Prop := ∀ ℓ, π ℓ = .star ∨ π ℓ = .term (τ ℓ)

instance (π : Cube N) (τ : FLeaf N) : Decidable (Cube.HasLeaf π τ) := by
  unfold Cube.HasLeaf; infer_instance

/-- The leaves of a cube. -/
def Cube.leaves (π : Cube N) : Finset (FLeaf N) := univ.filter fun τ => Cube.HasLeaf π τ
/-- The star levels of a cube. -/
def Cube.starLevels (π : Cube N) : Finset (Fin N) := univ.filter fun ℓ => π ℓ = .star
/-- The levels at which a cube has `P₀`. -/
def Cube.P0Levels (π : Cube N) : Finset (Fin N) := univ.filter fun ℓ => π ℓ = .term .P0
/-- The value of a cube for the products `g` at the leaves: `val(π) = ∑_{τ leaf of π} g(τ)`. -/
def Cube.val (g : FLeaf N → ℤ) (π : Cube N) : ℤ := ∑ τ ∈ Cube.leaves π, g τ

/-- The levels of the first half. -/
def half1 (L : ℕ) : Finset (Fin (L + L)) := univ.filter fun ℓ => (ℓ : ℕ) < L

/-- Section 7: "A box is a cube `π` on the `2L` levels such that (i) at most `2m - t` of its
symbols are `P₀` or stars, (ii) every star is at a lower level than every `P₀`, and (iii) at most
`m` of its symbols in each half are `P₀` or stars." -/
def IsBox (L m t : ℕ) (π : Cube (L + L)) : Prop :=
  (Cube.starLevels π).card + (Cube.P0Levels π).card ≤ 2 * m - t ∧
  (∀ ℓ ∈ Cube.starLevels π, ∀ ℓ' ∈ Cube.P0Levels π, ℓ < ℓ') ∧
  ((Cube.starLevels π ∪ Cube.P0Levels π) ∩ half1 L).card ≤ m ∧
  ((Cube.starLevels π ∪ Cube.P0Levels π) \ half1 L).card ≤ m

instance (L m t : ℕ) (π : Cube (L + L)) : Decidable (IsBox L m t π) := by
  unfold IsBox; infer_instance

/-- The boxes. -/
def boxes (L m t : ℕ) : Finset (Cube (L + L)) := univ.filter fun π => IsBox L m t π

/-- The `k` lowest levels of `S`. -/
def lowest (k : ℕ) (S : Finset (Fin N)) : Finset (Fin N) :=
  S.filter fun ℓ => (S.filter fun ℓ' => ℓ' < ℓ).card < k

/-- [ZT, Section 4.2]: `V := Z ∪ {the M - t - |Z| lowest levels of Q ∖ Z}`. -/
def Vof (M t : ℕ) (Q Z : Finset (Fin N)) : Finset (Fin N) := Z ∪ lowest (M - t - Z.card) (Q \ Z)

/-- [ZT, Section 4.2]: `F_V := {ℓ ∈ Q : ℓ < min(Q ∖ V)}`. -/
def FV (Q V : Finset (Fin N)) : Finset (Fin N) := Q.filter fun ℓ => ∀ ℓ' ∈ Q \ V, ℓ < ℓ'

/-- [ZT, Section 4.2], `𝓑_V`: the cubes with stars at `F_V`, `P₀` at `V ∖ F_V`, one of the four
terms `P_ij` at `Q ∖ V`, and the private term of `w` outside `Q`. -/
def BV (w : FOut N) (V : Finset (Fin N)) : Finset (Cube N) :=
  univ.filter fun π => ∀ ℓ,
    (ℓ ∈ FV (innerSet w) V → π ℓ = .star) ∧
    (ℓ ∈ V \ FV (innerSet w) V → π ℓ = .term .P0) ∧
    (ℓ ∈ innerSet w \ V → ∃ i j, π ℓ = .term (.P i j)) ∧
    (ℓ ∉ innerSet w → π ℓ = .term (privTerm (w ℓ)))

/-- The sets `V ⊆ Q` with `|V| = M - t`. -/
def Vsets (M t : ℕ) (w : FOut N) : Finset (Finset (Fin N)) := (innerSet w).powersetCard (M - t)

/-- The leaves of order below `t` contributing to `w`. -/
def lowLeaves (M t : ℕ) (w : FOut N) : Finset (FLeaf N) :=
  univ.filter fun τ => Contrib τ w ∧ order M τ < (t : ℤ)

/-- Replacing the symbol at level `ℓ` by the term `λ`. -/
def Cube.replace (π : Cube N) (ℓ : Fin N) (lam : Tm) : Cube N := Function.update π ℓ (.term lam)

end Sq

/-- **Lemma 7.1(a)**. "Lemmas 27 and 28 of [ZT] hold verbatim for every read output string `w`,
with `Q = Q(w)`, `m` replaced by `2m`, nine by four, and the products `Π(τ)`: the entry of `w` is
the sum of the `∑_{d<t} α'_d` products `Π(τ)` at the leaves of order below `t` in its cube and of the
values of its `α'_t` boxes, every leaf of order at least `t` of the cube lying in exactly one of
them"; and "the boxes of an output string `w` satisfy (iii)". For an arbitrary function `g` of the
leaves in place of the products. -/
def Lemma_7_1_a : Prop :=
  ∀ {L m t : ℕ}, t ≤ 2 * m → ∀ w : OutStr L, (QZ w.1).card = m → (QZ w.2).card = m →
    let W := Sq.flatOut w
    (∀ τ : Sq.FLeaf (L + L), (Sq.Contrib τ W ∧ (t : ℤ) ≤ Sq.order (2 * m) τ) ↔
      ∃ π ∈ (Sq.Vsets (2 * m) t W).biUnion (Sq.BV W), τ ∈ Sq.Cube.leaves π) ∧
    (∀ τ : Sq.FLeaf (L + L), Sq.Contrib τ W → (t : ℤ) ≤ Sq.order (2 * m) τ →
      ∃! π : Sq.Cube (L + L), π ∈ (Sq.Vsets (2 * m) t W).biUnion (Sq.BV W) ∧
        τ ∈ Sq.Cube.leaves π) ∧
    (∀ g : Sq.FLeaf (L + L) → ℤ,
      ∑ τ : Sq.FLeaf (L + L) with Sq.Contrib τ W, g τ
        = ∑ τ ∈ Sq.lowLeaves (2 * m) t W, g τ
          + ∑ V ∈ Sq.Vsets (2 * m) t W, ∑ π ∈ Sq.BV W V, Sq.Cube.val g π) ∧
    (Sq.lowLeaves (2 * m) t W).card = ∑ d ∈ range t, alpha' m d ∧
    ((Sq.Vsets (2 * m) t W).biUnion (Sq.BV W)).card = alpha' m t ∧
    (∀ V ∈ Sq.Vsets (2 * m) t W, ∀ π ∈ Sq.BV W V, Sq.IsBox L m t π)

/-- Lemma 7.1(a), the link with Theorem 5.1: "every read entry of a tile is `∑_τ Π(τ)` over the
leaves `τ` contributing to its output string `w`", with `Π(τ) = ∑_s Φ_τ(a_s) Ψ_τ(b_s)`; the
contributing leaves are the flattened leaves that contribute to the flattened `w`. -/
def Lemma_7_1_a_link : Prop :=
  ∀ {L m : ℕ} (a : ℤ → LeftStr L → ℤ) (b : ℤ → RightStr L → ℤ) (w : OutStr L),
    (∑ s ∈ Icc (-(m : ℤ)) m, Mult (a s) (b s) w
      = ∑ τ : Leaf L with Contributes τ w, ∑ s ∈ Icc (-(m : ℤ)) m, PhiL τ (a s) * PsiR τ (b s)) ∧
    (∀ τ : Leaf L, Contributes τ w ↔ Sq.Contrib (Sq.flatLeaf τ) (Sq.flatOut w)) ∧
    (∀ τ : Leaf L, order m τ = Sq.order (2 * m) (Sq.flatLeaf τ))

/-- **Lemma 7.1(b)**, the count. "There are at most `(2m+1) ∑_{d=t}^{2m} β'_d` boxes." -/
def Lemma_7_1_b_count : Prop :=
  ∀ L m t : ℕ, m ≤ L → t ≤ 2 * m →
    (Sq.boxes L m t).card ≤ (2 * m + 1) * ∑ d ∈ Icc t (2 * m), beta' L m d

/-- **Lemma 7.1(b)**, the dynamic program. "In the dynamic program, replacing the highest star of a
box by a term keeps (i) and (ii) …, and keeps (iii) … So the program never leaves the boxes, and
each value is the sum of five values computed before." -/
def Lemma_7_1_b_dp : Prop :=
  ∀ {L m t : ℕ} (π : Sq.Cube (L + L)) (hne : (Sq.Cube.starLevels π).Nonempty),
    Sq.IsBox L m t π →
    (∀ lam : Tm, Sq.IsBox L m t (Sq.Cube.replace π ((Sq.Cube.starLevels π).max' hne) lam) ∧
      (Sq.Cube.starLevels (Sq.Cube.replace π ((Sq.Cube.starLevels π).max' hne) lam)).card + 1
        = (Sq.Cube.starLevels π).card) ∧
    ∀ g : Sq.FLeaf (L + L) → ℤ, Sq.Cube.val g π
      = ∑ lam : Tm, Sq.Cube.val g (Sq.Cube.replace π ((Sq.Cube.starLevels π).max' hne) lam)

/-! ### [ZT, Lemma 7] on the `2L` levels, with the identity of each level

Section 5, "Per-level identities": "The proofs of Lemmas 7 and 8 of [ZT] treat one level at a time
and take the slices at a level over that level's alphabet (four left letters in the first half
below, three in the second), which is all they need. So these lemmas with their proofs, the
recursion `Full` of [ZT, Section 2.3.1], the leaves, the encodings and `Mult` are unchanged if the
identity used at level `ℓ` depends on `ℓ`." The recursion is written for one half (`FullHalf`),
with the forms `f`, `g` of that half and a continuation `base` for the levels below it; the
`2L` levels are the first half with the second half as its continuation (`FullSq.run`). -/

section FullSq

/-- Step (2) of `Full` at the first level of a half, with the forms `f` of that half:
`A_λ := ∑_s f_λ(s) a_s`, where `a_s` is the slice of `a` at the letter `s`; `A` carries the levels
below the half. -/
def encStep {α A : Type} [Fintype α] (f : Tm → α → ℤ) {n : ℕ} (lam : Tm)
    (a : (Fin (n + 1) → α) × A → ℤ) : (Fin n → α) × A → ℤ :=
  fun u => ∑ s, f lam s * a (Fin.cons s u.1, u.2)

/-- [ZT, Section 2.4.1], the encoding: the steps (2) along the levels of a half, at the terms of
`τ`; the result is an array on the levels below the half. -/
def encHalf {α A : Type} [Fintype α] (f : Tm → α → ℤ) :
    (n : ℕ) → ((Fin n → α) × A → ℤ) → (Fin n → Tm) → A → ℤ
  | 0, a, _ => fun x => a (Fin.elim0, x)
  | n + 1, a, τ => encHalf f n (encStep f (τ 0) a) (Fin.tail τ)

/-- The encoding of a left array at the leaf `τ` on the `2L` levels: the steps (2) at the levels
`1, …, L` with the forms `φ`, then at `L+1, …, 2L` with `ψ` (left and right exchanged). -/
def encodeL {L : ℕ} (a : LeftStr L → ℤ) (τ : Leaf L) : ℤ :=
  encHalf psi L (fun p : YStr L × Unit => encHalf phi L a τ.1 p.1) τ.2 ()

/-- The encoding of a right array: `ψ` in the first half, `φ` in the second. -/
def encodeR {L : ℕ} (b : RightStr L → ℤ) (τ : Leaf L) : ℤ :=
  encHalf phi L (fun p : XStr L × Unit => encHalf psi L b τ.1 p.1) τ.2 ()

/-- Step (4) of `Full`: "Return the array `c` whose slices are `c_{z_ij} := C_{P_ij}` and
`c_{z₀} := ∑_λ C_λ`"; the output forms are the same at every level. -/
def decodeStep {X : Type} (C : Tm → X → ℤ) (z : ZL) (x : X) : ℤ :=
  match z with
  | .z i j => C (.P i j) x
  | .z0 => ∑ lam, C lam x

/-- The recursion `Full` of [ZT, Section 2.3.1] on one half, with the forms `f` (left) and `g`
(right) of its levels and the continuation `base` for the levels below it. As upstream's
`Full.run`, it returns the array and, for every leaf, the two numbers multiplied there. -/
def FullHalf {α β A B O Lf : Type} [Fintype α] [Fintype β] (f : Tm → α → ℤ) (g : Tm → β → ℤ)
    (base : (A → ℤ) → (B → ℤ) → (O → ℤ) × (Lf → ℤ × ℤ)) :
    (n : ℕ) → ((Fin n → α) × A → ℤ) → ((Fin n → β) × B → ℤ) →
      ((Fin n → ZL) × O → ℤ) × ((Fin n → Tm) × Lf → ℤ × ℤ)
  | 0, a, b =>
    ((fun w => (base (fun x => a (Fin.elim0, x)) (fun y => b (Fin.elim0, y))).1 w.2),
     (fun τ => (base (fun x => a (Fin.elim0, x)) (fun y => b (Fin.elim0, y))).2 τ.2))
  | n + 1, a, b =>
    ((fun w => decodeStep (fun lam x => (FullHalf f g base n (encStep f lam a) (encStep g lam b)).1 x)
        (w.1 0) (Fin.tail w.1, w.2)),
     (fun τ => (FullHalf f g base n (encStep f (τ.1 0) a) (encStep g (τ.1 0) b)).2
        (Fin.tail τ.1, τ.2)))

/-- `Full` on the `2L` levels: the first half (forms `φ` left, `ψ` right), continued by the second
half (forms `ψ` left, `φ` right), which ends in step (1), "return the number `ab`". -/
def FullSq.run (L : ℕ) (a : LeftStr L → ℤ) (b : RightStr L → ℤ) :
    (OutStr L → ℤ) × (Leaf L → ℤ × ℤ) :=
  FullHalf phi psi
    (fun (a2 : YStr L → ℤ) (b2 : XStr L → ℤ) =>
      ((fun w2 => (FullHalf psi phi
          (fun (a0 : Unit → ℤ) (b0 : Unit → ℤ) =>
            ((fun _ : Unit => a0 () * b0 ()), (fun _ : Unit => (a0 (), b0 ()))))
          L (fun p => a2 p.1) (fun p => b2 p.1)).1 (w2, ())),
       (fun τ2 => (FullHalf psi phi
          (fun (a0 : Unit → ℤ) (b0 : Unit → ℤ) =>
            ((fun _ : Unit => a0 () * b0 ()), (fun _ : Unit => (a0 (), b0 ()))))
          L (fun p => a2 p.1) (fun p => b2 p.1)).2 (τ2, ()))))
    L a b

end FullSq

/-- **[ZT, Lemma 7] on the `2L` levels**, with the identity of each level (Section 5): "At the leaf
`τ`, `Full(a, b)` multiplies `Φ_τ(a)` by `Ψ_τ(b)`, and it returns `Mult(a, b)`"; and the encodings
of [ZT, Section 2.4.1] are `Φ_τ(a)` and `Ψ_τ(b)`. Ported from `3sum-apsp`
(`ThreeSumApsp/Sec2/Lemma7_8.lean`, `lemma_7`). -/
def Lemma_7_squared : Prop :=
  ∀ {L : ℕ} (a : LeftStr L → ℤ) (b : RightStr L → ℤ),
    (∀ τ : Leaf L, (FullSq.run L a b).2 τ = (PhiL τ a, PsiR τ b)) ∧
    (FullSq.run L a b).1 = Mult a b ∧
    ∀ τ : Leaf L, encodeL a τ = PhiL τ a ∧ encodeR b τ = PsiR τ b

/-! ### Theorem 7.2: the tiling and the query

Section 5, "The tiling": "Let `X ∈ ℤ^{N×D}` and `Y ∈ ℤ^{D×N}`, and index the columns of `X` and
the rows of `Y` by `F₂^m × F₂^m` through a fixed bijection. Cut `X` into row blocks of `N₀` rows,
each indexed by `{1,2}^{L-m} × F₂^{L-m}`, and group `K_g` consecutive row blocks into a row band,
the `k`-th block of a band playing the role of `X_{Q_k}`. Cut `Y` in the same way […] we first pad
`N` to a multiple of `K_g N₀`." Row `n` of `X` lies in band `n / (K_g N₀)`, block
`(n / N₀) mod K_g`, at row `n mod N₀` of the block; a row beyond `N` is a zero row (the padding).
The rows of a block are labelled by a bijection `eRow k` onto the rows of `X_{Q_k}` that are
entries of the block product (NOTE at `iotaX`), any bijection, and likewise the columns. -/

/-- The rows of `X_Q` that are entries of the block product: `ι` vanishes on `Q`. -/
abbrev BRow (L m : ℕ) (Q : Finset (Fin L)) : Type := {r : RowIdx L m // ∀ ℓ ∈ Q, r.1 ℓ = 0}

/-- The columns of `Y_Q` that are entries of the block product. -/
abbrev BCol (L m : ℕ) (Q : Finset (Fin L)) : Type := {c : ColIdx L m // ∀ ℓ ∈ Q, c.2 ℓ = 0}

/-- The block `X_Q` of the row band `b` (zero for a set `Q` that is not in the list, and at the
rows outside `BRow`): the entry at the row label `r` of block `k`, `Q = Q_k`, is the entry of `X`
in row `(b K_g + k) N₀ + i`, `i` the row of `r` in the block, and `0` beyond `N` (padding). -/
noncomputable def tileX {N L m Kg : ℕ} (X : Matrix (Fin N) (Fin (4 ^ m)) ℤ)
    (eD : Fin (4 ^ m) ≃ InIdx m) (𝒬 : Fin Kg → Finset (Fin L))
    (eRow : ∀ k, Fin (N0 L m) ≃ BRow L m (𝒬 k)) (b : ℕ) :
    Finset (Fin L) → Matrix (RowIdx L m) (InIdx m) ℤ := fun Q r c =>
  open Classical in
  if h : ∃ k, 𝒬 k = Q ∧ ∀ ℓ ∈ Q, r.1 ℓ = 0 then
    if hn : (b * Kg + h.choose) * N0 L m
        + ((eRow h.choose).symm ⟨r, fun ℓ hℓ => h.choose_spec.2 ℓ (h.choose_spec.1 ▸ hℓ)⟩ : ℕ)
        < N then
      X ⟨_, hn⟩ (eD.symm c)
    else 0
  else 0

/-- The block `Y_Q` of the column band `b`, in the same way. -/
noncomputable def tileY {N L m Kg : ℕ} (Y : Matrix (Fin (4 ^ m)) (Fin N) ℤ)
    (eD : Fin (4 ^ m) ≃ InIdx m) (𝒬 : Fin Kg → Finset (Fin L))
    (eCol : ∀ k, Fin (N0 L m) ≃ BCol L m (𝒬 k)) (b : ℕ) :
    Finset (Fin L) → Matrix (InIdx m) (ColIdx L m) ℤ := fun Q r c =>
  open Classical in
  if h : ∃ k, 𝒬 k = Q ∧ ∀ ℓ ∈ Q, c.2 ℓ = 0 then
    if hn : (b * Kg + h.choose) * N0 L m
        + ((eCol h.choose).symm ⟨c, fun ℓ hℓ => h.choose_spec.2 ℓ (h.choose_spec.1 ▸ hℓ)⟩ : ℕ)
        < N then
      Y (eD.symm r) ⟨_, hn⟩
    else 0
  else 0

/-- Change (5) of Section 7: "with the inverses of the columns of `Δ` at `[L] ∖ Q`": the set
`S ⊆ [L] ∖ Q` with `Δ[S] = δ` (unique when `Q` is good; `∅` if there is none). -/
noncomputable def DeltaInv {L m : ℕ} (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2))
    (Q : Finset (Fin L)) (δ : Fin (L - m) → ZMod 2) : Finset (Fin L) :=
  open Classical in if h : ∃ S ⊆ Qᶜ, colSum Δ S = δ then h.choose else ∅

/-- The `z`-string with inner set `Q`, the indices `ι` outside `Q` and the set `S` of the levels
with a letter `z_{i2}`. -/
def zString {L : ℕ} (Q S : Finset (Fin L)) (ι : Fin L → Fin 2) : ZStr L := fun ℓ =>
  if ℓ ∈ Q then .z0 else .z (ι ℓ) (if ℓ ∈ S then 1 else 0)

/-- Back from the `2L` flattened levels to the two halves. -/
def Sq.unflatLeaf {L : ℕ} (τ : Sq.FLeaf (L + L)) : Leaf L :=
  (fun ℓ => τ (Fin.castAdd L ℓ), fun ℓ => τ (Fin.natAdd L ℓ))

/-- **The query of Theorem 7.2.** "Query: locate the tile, the pair `(Q_k, Q_{k'})` and the output
string with change (5) […]; then add the `∑_{d<t} α'_d` products `Π(τ)` and the `α'_t` box values
of Lemma 7.1(a)." Here the row `I` lies in band `I / (K_g N₀)`, block `k = (I / N₀) mod K_g`, at
the label `(ι', δ'') = eRow k (I mod N₀)`, and the column `J` likewise at `(δ', ι'')`; "the row of
`I` in its block gives `(ι(w'), Δ[S(w'')])` and the column of `J` gives `(Δ[S(w')], ι(w''))`", so
`w' = zString Q_k (Δ⁻¹ δ') ι'` and `w'' = zString Q_{k'} (Δ⁻¹ δ'') ι''`. The arrays are those of
the two bands (Section 5), `Π(τ) = ∑_s Φ_τ(a_s) Ψ_τ(b_s)` is read from the encodings, and a box's
value is the sum of `Π` over its leaves (the dynamic program computes it, `Lemma_7_1_b_dp`). -/
noncomputable def query {N L m Kg : ℕ} (hKg : 0 < Kg) (t : ℕ)
    (Γ : Matrix (Fin m) (Fin L) (ZMod 2)) (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2))
    (𝒬 : Fin Kg → Finset (Fin L)) (eD : Fin (4 ^ m) ≃ InIdx m)
    (eRow : ∀ k, Fin (N0 L m) ≃ BRow L m (𝒬 k)) (eCol : ∀ k, Fin (N0 L m) ≃ BCol L m (𝒬 k))
    (X : Matrix (Fin N) (Fin (4 ^ m)) ℤ) (Y : Matrix (Fin (4 ^ m)) (Fin N) ℤ) (I J : Fin N) : ℤ :=
  let hN0 : 0 < N0 L m := pow_pos (by norm_num) (L - m)
  let k : Fin Kg := ⟨((I : ℕ) / N0 L m) % Kg, Nat.mod_lt _ hKg⟩
  let k' : Fin Kg := ⟨((J : ℕ) / N0 L m) % Kg, Nat.mod_lt _ hKg⟩
  let r := (eRow k ⟨(I : ℕ) % N0 L m, Nat.mod_lt _ hN0⟩).1
  let c := (eCol k' ⟨(J : ℕ) % N0 L m, Nat.mod_lt _ hN0⟩).1
  let w : OutStr L := (zString (𝒬 k) (DeltaInv Δ (𝒬 k) c.1) r.1,
    zString (𝒬 k') (DeltaInv Δ (𝒬 k') r.2) c.2)
  let 𝒢 := univ.image 𝒬
  let A := tileX X eD 𝒬 eRow ((I : ℕ) / (Kg * N0 L m))
  let B := tileY Y eD 𝒬 eCol ((J : ℕ) / (Kg * N0 L m))
  let g : Sq.FLeaf (L + L) → ℤ := fun τ => ∑ s ∈ Icc (-(m : ℤ)) m,
    encodeL (arrayA Γ Δ 𝒢 A s) (Sq.unflatLeaf τ) * encodeR (arrayB Γ Δ 𝒢 B s) (Sq.unflatLeaf τ)
  ∑ τ ∈ Sq.lowLeaves (2 * m) t (Sq.flatOut w), g τ
    + ∑ V ∈ Sq.Vsets (2 * m) t (Sq.flatOut w), ∑ π ∈ Sq.BV (Sq.flatOut w) V, Sq.Cube.val g π

/-- **Theorem 7.2, correctness of the query**: "any single entry `(XY)[I, J]` can be computed";
"Correctness is Lemma 7.1(a) with Theorem 5.1". For every list of distinct good sets
`Q_1, …, Q_{K_g}`, every switching order `t ≤ 2m`, all labellings of the inner dimension and of the
rows and columns of the blocks, and all integer matrices `X ∈ ℤ^{N×4^m}`, `Y ∈ ℤ^{4^m×N}`, the query
returns `(XY)[I, J]` at every position. -/
def Theorem_7_2_query : Prop :=
  ∀ {N L m Kg : ℕ} (hKg : 0 < Kg) (t : ℕ), t ≤ 2 * m →
  ∀ (Γ : Matrix (Fin m) (Fin L) (ZMod 2)) (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2))
    (𝒬 : Fin Kg → Finset (Fin L)), Function.Injective 𝒬 → (∀ k, Good Γ Δ (𝒬 k)) →
  ∀ (eD : Fin (4 ^ m) ≃ InIdx m) (eRow : ∀ k, Fin (N0 L m) ≃ BRow L m (𝒬 k))
    (eCol : ∀ k, Fin (N0 L m) ≃ BCol L m (𝒬 k))
    (X : Matrix (Fin N) (Fin (4 ^ m)) ℤ) (Y : Matrix (Fin (4 ^ m)) (Fin N) ℤ) (I J : Fin N),
    query hKg t Γ Δ 𝒬 eD eRow eCol X Y I J = (X * Y) I J

/-- The labellings of Theorem 7.2 exist: for a good set `Q` the rows of a block number
`N₀ = 4^{L-m}`, and so do its columns; the inner dimension `D = 4^m` is `|F₂^m × F₂^m|`. -/
def Theorem_7_2_labels : Prop :=
  ∀ {L m : ℕ} (Γ : Matrix (Fin m) (Fin L) (ZMod 2)) (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2))
    (Q : Finset (Fin L)), Good Γ Δ Q →
    Nonempty (Fin (N0 L m) ≃ BRow L m Q) ∧ Nonempty (Fin (N0 L m) ≃ BCol L m Q) ∧
    Nonempty (Fin (4 ^ m) ≃ InIdx m)

/-! ## Full products and the general leaf-count lemma (auxiliary results)

The labels Lemma U, Lemmas L1–L3, Theorem L, Lemma 1 and Theorem 2 are those of the working notes
in which these results were first written, not items of the paper; the section "Thin full
products in the paper" below says which of them are items of the paper's Appendix A.9.

Generic setting. A run of the framework of [ZT, Section 2] uses a base identity (a sum of `R`
trilinear terms) at `L` levels; a *leaf* is a string of `L` terms and an *output string* a string
of `L` outputs, and a leaf contributes to an output string if at every level the output form of its
term contains that level's output. Below, the leaves form any finite type `T`, the selected output
strings any type `E`, and `A τ ⊆ E` is the set of selected output strings to which `τ`
contributes, so that `s(τ) = |A τ|`. For a set `W` of wanted output strings, `fpLeaves A W` is
`Leaves(W)` of [ZT, Section 2.4.2], the set of leaves that contribute to some string of `W`; by
[ZT, Lemma 10] the pruned recursion visits exactly these leaves (`FP_Lemma_10`, at the end of this
file). -/

section FullProduct

open scoped Classical in
/-- `Leaves(W)`: the leaves that contribute to at least one wanted output string. -/
noncomputable def fpLeaves {T E : Type} [Fintype T] (A : T → Finset E) (W : Finset E) :
    Finset T :=
  univ.filter fun τ => ∃ e ∈ W, e ∈ A τ

open scoped Classical in
/-- **(U)**, the upper bound for every `W` (the argument of [ZT, Lemma 11] for any identity and any
partition of the leaves into classes `x`): if every wanted output string has at most `α x` leaves
of class `x` contributing to it (so `α x` may be the maximum over output strings, the paper's
`α'_d`), and class `x` has `β_x` leaves, then `|Leaves(W)| ≤ ∑_x min(|W| α_x, β_x)`. -/
def FP_U : Prop :=
  ∀ {T E X : Type} [Fintype T] [Fintype X] (A : T → Finset E) (cls : T → X) (W : Finset E)
    (α : X → ℕ), (∀ x, ∀ e ∈ W, (univ.filter fun τ => cls τ = x ∧ e ∈ A τ).card ≤ α x) →
    (fpLeaves A W).card ≤ ∑ x, min (W.card * α x) (univ.filter fun τ => cls τ = x).card

/-- **(L)**, Bernoulli selection: if every selected output string is wanted independently with
probability `p`, the expected number of visited leaves is `∑_τ (1 - (1-p)^{s(τ)})`. Stated as the
finite sum over all `W ⊆ E` with weights `p^{|W|} (1-p)^{|E|-|W|}` (an identity of polynomials
in `p`). -/
def FP_L_bernoulli : Prop :=
  ∀ {T E : Type} [Fintype T] [Fintype E] (A : T → Finset E) (p : ℝ),
    ∑ W : Finset E, p ^ W.card * (1 - p) ^ (Fintype.card E - W.card) * ((fpLeaves A W).card : ℝ)
      = ∑ τ, (1 - (1 - p) ^ (A τ).card)

/-- **(L)**, fixed size: summed over all sets `W` of exactly `w` selected output strings, the number
of visited leaves is `∑_τ (binom(|E|, w) - binom(|E| - s(τ), w))` (a leaf is missed exactly when
`W` avoids its `s(τ)` output strings). -/
def FP_L_uniform : Prop :=
  ∀ {T E : Type} [Fintype T] [Fintype E] (A : T → Finset E) (w : ℕ),
    ∑ W ∈ (univ : Finset E).powersetCard w, (fpLeaves A W).card
      = ∑ τ, ((Fintype.card E).choose w - (Fintype.card E - (A τ).card).choose w)

/-- **(L)**, the hypergeometric step: `binom(n-s, w) ≤ binom(n, w) (1 - w/n)^s` for `s ≤ n`, so a
uniform `w`-set misses `s` given strings with probability at most `(1-ρ)^s`, `ρ = w/n`. -/
def FP_choose_ratio : Prop :=
  ∀ n s w : ℕ, s ≤ n → ((n - s).choose w : ℝ) ≤ (n.choose w : ℝ) * (1 - (w : ℝ) / n) ^ s

/-- **(L)**, the real inequality: `1 - (1-p)^s ≥ (1 - 1/e) min(1, p s)` for `p ∈ [0,1]`, `s ∈ ℕ`;
and the converse `1 - (1-p)^s ≤ min(1, p s)` (Bernoulli's inequality). -/
def FP_one_sub_pow : Prop :=
  ∀ (p : ℝ) (s : ℕ), 0 ≤ p → p ≤ 1 →
    (1 - Real.exp (-1)) * min 1 (p * s) ≤ 1 - (1 - p) ^ s ∧ 1 - (1 - p) ^ s ≤ min 1 (p * s)

/-- **(L)**, the average over the uniform `w`-sets: with `ρ = w/|E|` and the leaf-count model
`V = ∑_τ min(1, ρ s(τ))`, the average number of visited leaves lies between `(1 - 1/e) V` and
`V`. -/
def FP_L_average : Prop :=
  ∀ {T E : Type} [Fintype T] [Fintype E] (A : T → Finset E) (w : ℕ), w ≤ Fintype.card E →
    (1 - Real.exp (-1)) * ∑ τ, min 1 ((w : ℝ) / Fintype.card E * (A τ).card)
        ≤ (∑ W ∈ (univ : Finset E).powersetCard w, ((fpLeaves A W).card : ℝ))
          / (Fintype.card E).choose w ∧
      (∑ W ∈ (univ : Finset E).powersetCard w, ((fpLeaves A W).card : ℝ))
          / (Fintype.card E).choose w
        ≤ ∑ τ, min 1 ((w : ℝ) / Fintype.card E * (A τ).card)

/-- **(L)**, the consequence used for exclusions: for every size `w ≤ |E|` some set `W` of exactly
`w` selected output strings has `|Leaves(W)| ≥ (1 - 1/e) ∑_τ min(1, ρ s(τ))`, `ρ = w/|E|`. -/
def FP_L_exists : Prop :=
  ∀ {T E : Type} [Fintype T] [Fintype E] (A : T → Finset E) (w : ℕ), w ≤ Fintype.card E →
    ∃ W : Finset E, W.card = w ∧
      (1 - Real.exp (-1)) * ∑ τ, min 1 ((w : ℝ) / Fintype.card E * (A τ).card)
        ≤ (fpLeaves A W).card

open scoped Classical in
/-- The contribution relation of the `L`-th power of a base identity whose term `l` has output
support `S l` among `n` outputs, all output strings selected (a single-type run): the leaf
`τ ∈ [R]^L` contributes to `w ∈ [n]^L` iff `w_ℓ ∈ S(τ_ℓ)` at every level. -/
noncomputable def fpPowA {R n L : ℕ} (S : Fin R → Finset (Fin n)) (τ : Fin L → Fin R) :
    Finset (Fin L → Fin n) :=
  univ.filter fun w => ∀ ℓ, w ℓ ∈ S (τ ℓ)

/-- For the `L`-th power, `s(τ) = ∏_ℓ |S(τ_ℓ)|`, and (L) gives, for every `w ≤ n^L`, a set `W` of
exactly `w` output strings with `|Leaves(W)| ≥ (1 - 1/e) ∑_τ min(1, (w/n^L) ∏_ℓ |S(τ_ℓ)|)`. -/
def FP_power_lower : Prop :=
  ∀ (R n L : ℕ) (S : Fin R → Finset (Fin n)),
    (∀ τ : Fin L → Fin R, (fpPowA S τ).card = ∏ ℓ, (S (τ ℓ)).card) ∧
    ∀ w : ℕ, w ≤ n ^ L → ∃ W : Finset (Fin L → Fin n), W.card = w ∧
      (1 - Real.exp (-1)) * ∑ τ : Fin L → Fin R,
          min 1 ((w : ℝ) / (n : ℝ) ^ L * ∏ ℓ, ((S (τ ℓ)).card : ℝ))
        ≤ (fpLeaves (fpPowA S) W).card

/-- The matrix multiplication tensor `⟨o₁, b, o₂⟩ = ∑_{i,j,c} x_{ij} y_{jc} z_{ic}` as its array of
coefficients: left variables `x_{ij}` indexed by `Fin o₁ × Fin b`, right variables `y_{jc}` by
`Fin b × Fin o₂`, outputs `z_{ic}` by `Fin o₁ × Fin o₂`. -/
def mmTensor (K : Type) [Zero K] [One K] (o₁ b o₂ : ℕ) (a : Fin o₁ × Fin b)
    (y : Fin b × Fin o₂) (z : Fin o₁ × Fin o₂) : K :=
  if a.1 = z.1 ∧ a.2 = y.1 ∧ y.2 = z.2 then 1 else 0

/-- A decomposition of `⟨o₁, b, o₂⟩` into `R` rank-one trilinear terms `u_l ⊗ v_l ⊗ w_l`, read with
`w` as the output factor. -/
def IsMMDecomp {K : Type} [Field K] {o₁ b o₂ R : ℕ} (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K) : Prop :=
  ∀ a y z, ∑ l, u l a * v l y * w l z = mmTensor K o₁ b o₂ a y z

open scoped Classical in
/-- The output support `S_l = supp w_l`. -/
noncomputable def outSupp {K : Type} [Zero K] {o₁ o₂ : ℕ} (w : Fin o₁ × Fin o₂ → K) :
    Finset (Fin o₁ × Fin o₂) :=
  univ.filter fun z => w z ≠ 0

/-- The `y`-flattening of `⟨o₁, b, o₂⟩` restricted to a set `P` of outputs: rows the right
variables `y_{jc}`, columns the pairs (left variable, output in `P`). -/
def yFlat (K : Type) [Zero K] [One K] (o₁ b o₂ : ℕ) (P : Finset (Fin o₁ × Fin o₂)) :
    Matrix (Fin b × Fin o₂) ((Fin o₁ × Fin b) × P) K :=
  fun y q => mmTensor K o₁ b o₂ q.1 y q.2

open scoped Classical in
/-- **Lemma 1, the restriction step**: restricted to a set `P` of outputs, a
decomposition keeps only the terms whose output support meets `P`, and their number is at least the
rank of the `y`-flattening of `⟨o₁, b, o₂⟩|_P`; over any field. -/
def FP_restrict_rank : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → ∀ P : Finset (Fin o₁ × Fin o₂),
      (yFlat K o₁ b o₂ P).rank ≤ (univ.filter fun l => ∃ z ∈ P, w l z ≠ 0).card

/-- **Lemma 1, the transversal step**: if `P` has exactly one output in every column `c`, the
`y`-flattening of `⟨o₁, b, o₂⟩|_P` has rank `b o₂` (the images of the `y_{jc}` are distinct basis
tensors); over any field. -/
def FP_transversal_rank : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ : ℕ) (P : Finset (Fin o₁ × Fin o₂)),
    (∀ c : Fin o₂, ∃! i : Fin o₁, (i, c) ∈ P) → (yFlat K o₁ b o₂ P).rank = b * o₂

/-- **Lemma 1** (capped covering): every decomposition of `⟨o₁, b, o₂⟩` over any field
satisfies `∑_l min(|S_l|, k) ≥ b n`, `n = o₁ o₂`, `k = min(o₁, o₂)`. -/
def FP_Lemma_1 : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → b * (o₁ * o₂) ≤ ∑ l, min (outSupp (w l)).card (min o₁ o₂)

open scoped Classical in
/-- The `z`-flattening bound used by Theorem 2: for `b ≥ 1`, at least `n = o₁ o₂` terms have a
nonzero output factor (so `R ≥ n` after dropping the terms with `w_l = 0`); over any field. -/
def FP_rank_ge_n : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → 1 ≤ b → o₁ * o₂ ≤ (univ.filter fun l => w l ≠ 0).card

/-- **Theorem 2, the inequality**: for integers `b, k ≥ 1` with `k ≤ b` or
`k^{2(b-1)} ≥ b^{k-1}`, every finite family `S_l ≥ 1` with `R ≥ n` members and
`∑_l min(S_l, k) ≥ b n` has `∑_l S_l^t ≥ n b^{t/2}` for all real `t ∈ [0, 1]`. (The thin case is
`b < k`; the case `k ≤ b` is included.) -/
def FP_Theorem_2_ineq : Prop :=
  ∀ (b k n R : ℕ) (S : Fin R → ℕ), 1 ≤ b → 1 ≤ k → (k ≤ b ∨ b ^ (k - 1) ≤ k ^ (2 * (b - 1))) →
    (∀ l, 1 ≤ S l) → n ≤ R → b * n ≤ ∑ l, min (S l) k →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (n : ℝ) * (b : ℝ) ^ (t / 2) ≤ ∑ l, ((S l : ℕ) : ℝ) ^ t

open scoped Classical in
/-- **Theorem 2**, composed with Lemma 1 and `FP_rank_ge_n`: every decomposition of
`⟨o₁, b, o₂⟩`, `b ≥ 1`, over any field, with `k = min(o₁, o₂)` satisfying `k ≤ b` or
`k^{2(b-1)} ≥ b^{k-1}`, has `∑_l |S_l|^t ≥ n b^{t/2}` for all `t ∈ [0, 1]`, the sum over the terms
with `w_l ≠ 0`. (Taking logarithms: `Γ = min_t [ln ∑ S^t - (t/2) ln b] - ln n ≥ 0`.) -/
def FP_Theorem_2 : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → 1 ≤ b →
    (min o₁ o₂ ≤ b ∨ b ^ (min o₁ o₂ - 1) ≤ (min o₁ o₂) ^ (2 * (b - 1))) →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2)
        ≤ ∑ l ∈ univ.filter (fun l => w l ≠ 0), ((outSupp (w l)).card : ℝ) ^ t

/-- The 81 distinct thin shapes `(o₁, b, o₂)`, `o₁ ≤ o₂`, `b < o₁`, among the 96 thin rotations of
the 145 decompositions of Appendix A.1 (list extracted from
the data files of the 145 decompositions). -/
def fpShapes145 : List (ℕ × ℕ × ℕ) :=
  [(3,2,3), (3,2,4), (3,2,5), (4,2,4), (3,2,6), (4,2,5), (4,2,6), (5,2,5), (4,2,7), (5,2,6),
   (4,2,8), (6,2,6), (4,3,4), (4,3,5), (4,3,6), (5,3,5), (4,3,7), (5,3,6), (4,3,8), (5,3,7),
   (6,3,6), (4,3,11), (5,3,9), (9,3,11), (5,4,5), (5,4,6), (6,4,6), (5,4,9), (5,4,10), (5,4,11),
   (9,4,10), (9,4,11), (11,4,11), (11,4,12), (6,5,6), (7,5,9), (7,5,10), (8,5,9), (7,5,11),
   (8,5,10), (9,5,9), (8,5,11), (9,5,10), (9,5,11), (9,5,12), (7,6,9), (7,6,10), (7,6,11),
   (8,6,10), (9,6,9), (8,6,11), (9,6,10), (9,6,11), (8,7,9), (8,7,10), (9,7,9), (8,7,11),
   (9,7,10), (8,7,12), (9,7,11), (10,7,10), (9,7,12), (10,7,11), (11,7,11), (9,8,10), (9,8,11),
   (10,8,10), (9,8,12), (10,8,11), (10,8,12), (11,8,11), (11,8,12), (10,9,10), (10,9,11),
   (10,9,12), (11,9,11), (11,9,12), (11,10,11), (11,10,12), (12,10,12), (12,11,12)]

/-- The thin shapes of the 145 satisfy Theorem 2's condition: the list has 81 distinct shapes, each
with `o₁ ≤ o₂`, `2 ≤ b < o₁` and `o₁^{2(b-1)} ≥ b^{o₁-1}` (`k = o₁`). -/
def FP_shapes_145 : Prop :=
  fpShapes145.length = 81 ∧ fpShapes145.Nodup ∧
    ∀ s ∈ fpShapes145, s.1 ≤ s.2.2 ∧ 2 ≤ s.2.1 ∧ s.2.1 < s.1 ∧
      s.2.1 ^ (s.1 - 1) ≤ s.1 ^ (2 * (s.2.1 - 1))

open scoped Classical in
/-- **The 145, thin rotations**: for every shape of
`fpShapes145`, in either orientation, every decomposition over any field (of any rank, not only the
one found) has `∑_l |S_l|^t ≥ n b^{t/2}` for all `t ∈ [0, 1]`, i.e. `Γ ≥ 0`. -/
def FP_145_thin : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ),
    ((o₁, b, o₂) ∈ fpShapes145 ∨ (o₂, b, o₁) ∈ fpShapes145) →
    ∀ (u : Fin R → Fin o₁ × Fin b → K) (v : Fin R → Fin b × Fin o₂ → K)
      (w : Fin R → Fin o₁ × Fin o₂ → K), IsMMDecomp u v w →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2)
        ≤ ∑ l ∈ univ.filter (fun l => w l ≠ 0), ((outSupp (w l)).card : ℝ) ^ t

/-- **The squared run** (Section 5 of the paper) for a single-type full product: the second half
uses the same terms with left and right exchanged, so the output factors, and with them the
relation "contributes to", are those of the first half; the run is the `2L`-th power in the sense of
`fpPowA` (with `L + L` levels, so `FP_power_lower` applies to it as it stands), with `D = b^{2L}`.
Read as a base with terms `(l, l')`, output supports of sizes `S_l S_{l'}` among `n²` outputs and
inner dimension `b²`, the test of Theorem 2 is unchanged:
`∑_{l,l'} (S_l S_{l'})^t = (∑_l S_l^t)²`, so `∑_l S_l^t ≥ n b^{t/2}` gives
`∑_{l,l'} (S_l S_{l'})^t ≥ n² (b²)^{t/2}`. -/
def FP_squared : Prop :=
  ∀ (R n b : ℕ) (S : Fin R → ℕ) (t : ℝ), 0 ≤ t →
    (∑ l, ∑ l', (((S l * S l' : ℕ) : ℝ)) ^ t = (∑ l, ((S l : ℕ) : ℝ) ^ t) ^ 2) ∧
    ((n : ℝ) * (b : ℝ) ^ (t / 2) ≤ ∑ l, ((S l : ℕ) : ℝ) ^ t →
      ((n * n : ℕ) : ℝ) * ((b * b : ℕ) : ℝ) ^ (t / 2) ≤ ∑ l, ∑ l', (((S l * S l' : ℕ) : ℝ)) ^ t)

end FullProduct

/-! ## Thin full products: the open region (auxiliary results)

The labels Lemmas 3–6 and Theorem 2' are those of the working notes in which these results were
first written, not items of the paper; the next section says which of them are items of the
paper's Appendix A.9. Notation of the section `FullProduct`: `(u, v, w)` is a decomposition of
`⟨o₁, b, o₂⟩` with `R` terms (`IsMMDecomp`), an output is `e = (i, c)`, `S_l = outSupp (w l)`,
`n = o₁ o₂`. `A_i = span{x_{i1}, …, x_{ib}}` is the space of left coefficient vectors that use only
row `i`, `Y_c = span{y_{1c}, …, y_{bc}}` the space of right coefficient vectors that use only
column `c`. -/

section FullProductOpen

open scoped Classical in
/-- The coverers of an output `e`: the terms with `w_l(e) ≠ 0`. Their number is `r_e`. -/
noncomputable def fpCov {K : Type} [Zero K] {R o₁ o₂ : ℕ} (w : Fin R → Fin o₁ × Fin o₂ → K)
    (e : Fin o₁ × Fin o₂) : Finset (Fin R) :=
  univ.filter fun l => w l e ≠ 0

/-- A term with left factor `u` and right factor `v` is *local* to the output `e = (i, c)`:
`u ≠ 0` lies in `A_i` (its coefficients outside row `i` vanish) and `v ≠ 0` lies in `Y_c` (its
coefficients outside column `c` vanish). -/
def fpLocal {K : Type} [Zero K] {o₁ b o₂ : ℕ} (u : Fin o₁ × Fin b → K) (v : Fin b × Fin o₂ → K)
    (e : Fin o₁ × Fin o₂) : Prop :=
  u ≠ 0 ∧ v ≠ 0 ∧ (∀ a : Fin o₁ × Fin b, a.1 ≠ e.1 → u a = 0) ∧
    (∀ y : Fin b × Fin o₂, y.2 ≠ e.2 → v y = 0)

/-- **Lemma 3** (tight outputs; any field): if the output `e` is covered by
exactly `b` terms (`r_e = b`, "tight"), then every term covering `e` is local to `e`. -/
def FP_Lemma_3 : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → ∀ e : Fin o₁ × Fin o₂, (fpCov w e).card = b →
      ∀ l ∈ fpCov w e, fpLocal (u l) (v l) e

/-- **Lemma 3**, second part: a term is local to at most one output (`A_i ∩ A_{i'} = 0` for
`i ≠ i'`, `Y_c ∩ Y_{c'} = 0` for `c ≠ c'`, and `u, v ≠ 0`). -/
def FP_local_unique : Prop :=
  ∀ (K : Type) [Zero K] (o₁ b o₂ : ℕ) (u : Fin o₁ × Fin b → K) (v : Fin b × Fin o₂ → K)
    (e e' : Fin o₁ × Fin o₂), fpLocal u v e → fpLocal u v e' → e = e'

open scoped Classical in
/-- **Lemma 3**, the count: the coverers of distinct tight outputs are distinct, so
`R ≥ #{l : w_l ≠ 0} ≥ b · #(tight outputs)`. -/
def FP_Lemma_3_count : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w →
      b * (univ.filter fun e : Fin o₁ × Fin o₂ => (fpCov w e).card = b).card
        ≤ (univ.filter fun l => w l ≠ 0).card

/-- **Lemma 3**, the strengthened consequence: if every output is
tight, every term has at most one output in its support. -/
def FP_Lemma_3_all_tight : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → (∀ e : Fin o₁ × Fin o₂, (fpCov w e).card = b) →
      ∀ l, (outSupp (w l)).card ≤ 1

open scoped Classical in
/-- **Lemma 6** (rank lower bound by substitution; any field): for
`o₁, b, o₂ ≥ 1`, every decomposition of `⟨o₁, b, o₂⟩` has at least
`o₁ o₂ + (b - 1) max(o₁, o₂)` terms with `w_l ≠ 0`. -/
def FP_Lemma_6 : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → 1 ≤ o₁ → 1 ≤ b → 1 ≤ o₂ →
      o₁ * o₂ + (b - 1) * max o₁ o₂ ≤ (univ.filter fun l => w l ≠ 0).card

/-- A *forest* of the bipartite row/column graph of the output grid (output `(i, c)` = edge from row
`i` to column `c`): every nonempty subset `G ⊆ F` has an output that is alone in its row in `G` or
alone in its column in `G` (an edge at a vertex of degree 1). This is the hereditary-leaf
characterisation of acyclic edge sets: a cycle has no such edge, and every nonempty acyclic edge
set has a leaf. -/
def fpForest {o₁ o₂ : ℕ} (F : Finset (Fin o₁ × Fin o₂)) : Prop :=
  ∀ G ⊆ F, G.Nonempty → ∃ e ∈ G,
    (∀ e' ∈ G, e'.1 = e.1 → e' = e) ∨ (∀ e' ∈ G, e'.2 = e.2 → e' = e)

open scoped Classical in
/-- **Lemma 4** (forest cap; any field): for every forest `F` of outputs at least
`b |F|` terms meet `F`. -/
def FP_Lemma_4 : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → ∀ F : Finset (Fin o₁ × Fin o₂), fpForest F →
      b * F.card ≤ (univ.filter fun l => ∃ z ∈ F, w l z ≠ 0).card

open scoped Classical in
/-- The double star with centre row `r` and centre column `s`: row `r` together with column `s`.
These are the translates of one spanning tree of `K_{o₁,o₂}` under the cyclic shifts of rows and
columns. -/
noncomputable def fpStar {o₁ o₂ : ℕ} (r : Fin o₁) (s : Fin o₂) : Finset (Fin o₁ × Fin o₂) :=
  univ.filter fun z => z.1 = r ∨ z.2 = s

open scoped Classical in
/-- The family used for the averaging in Lemma 4: every double star is a forest with
`o₁ + o₂ - 1` outputs (a spanning tree), and every output lies in exactly `o₁ + o₂ - 1` of the
`o₁ o₂` double stars. -/
def FP_star : Prop :=
  ∀ (o₁ o₂ : ℕ),
    (∀ (r : Fin o₁) (s : Fin o₂), fpForest (fpStar r s) ∧ (fpStar r s).card = o₁ + o₂ - 1) ∧
    ∀ z : Fin o₁ × Fin o₂,
      (univ.filter fun q : Fin o₁ × Fin o₂ => z ∈ fpStar q.1 q.2).card = o₁ + o₂ - 1

/-- `m* = n / (o₁ + o₂ - 1)`, the cap of Lemma 4's averaged form. -/
noncomputable def fpMstar (o₁ o₂ : ℕ) : ℝ := (o₁ : ℝ) * o₂ / ((o₁ : ℝ) + o₂ - 1)

/-- **Lemma 4**, averaged (any field): every decomposition of `⟨o₁, b, o₂⟩`
satisfies `∑_l min(|S_l|, m*) ≥ b n`, `m* = n/(o₁ + o₂ - 1)`. (Averaged over the double stars
instead of a uniformly random spanning tree; the inequality is the same.) -/
def FP_Lemma_4_avg : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w →
      (b : ℝ) * ((o₁ : ℝ) * o₂) ≤ ∑ l, min ((outSupp (w l)).card : ℝ) (fpMstar o₁ o₂)

/-- `A_i = span{x_{i1}, …, x_{ib}}` in the space of left coefficient vectors. -/
def fpRowSpace (K : Type) [Field K] (o₁ b : ℕ) (i : Fin o₁) : Submodule K (Fin o₁ × Fin b → K) :=
  Submodule.span K (Set.range fun j : Fin b => Pi.single (i, j) (1 : K))

/-- `Y_c = span{y_{1c}, …, y_{bc}}` in the space of right coefficient vectors. -/
def fpColSpace (K : Type) [Field K] (b o₂ : ℕ) (c : Fin o₂) : Submodule K (Fin b × Fin o₂ → K) :=
  Submodule.span K (Set.range fun j : Fin b => Pi.single (j, c) (1 : K))

/-- **Lemma 5 (a)** (any field). For every output `e = (i, c)` let
`U_e = span{u_l : l covers e}`, `V_e = span{v_l : l covers e}`. Then `A_i ⊆ U_e`, `Y_c ⊆ V_e`,
`dim A_i = dim Y_c = b`, and `dim U_e + dim V_e ≤ r_e + b`, i.e. `r_e ≥ b + d_A(e) + d_B(e)` with
`d_A(e) = dim U_e - b = dim(U_e / A_i)` and `d_B(e) = dim V_e - b`. Also `r_e ≥ b + 1` as soon as one coverer
of `e` is not local to `e` (if it has `u_l = 0` or `v_l = 0`, because the other coverers alone
give the rank-`b` slice). -/
def FP_Lemma_5a : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → ∀ e : Fin o₁ × Fin o₂,
      fpRowSpace K o₁ b e.1 ≤ Submodule.span K (u '' ↑(fpCov w e)) ∧
      fpColSpace K b o₂ e.2 ≤ Submodule.span K (v '' ↑(fpCov w e)) ∧
      Module.finrank K (fpRowSpace K o₁ b e.1) = b ∧ Module.finrank K (fpColSpace K b o₂ e.2) = b ∧
      Module.finrank K (Submodule.span K (u '' ↑(fpCov w e)))
          + Module.finrank K (Submodule.span K (v '' ↑(fpCov w e))) ≤ (fpCov w e).card + b ∧
      ((∃ l ∈ fpCov w e, ¬ fpLocal (u l) (v l) e) → b + 1 ≤ (fpCov w e).card)

open scoped Classical in
/-- `G_W = span{u_l ⊗ w_l|_W : l meets W}`, as vectors indexed by (left variable, output), with
the output coordinate restricted to `W`. -/
noncomputable def fpGW {K : Type} [Field K] {R o₁ b o₂ : ℕ} (u : Fin R → Fin o₁ × Fin b → K)
    (w : Fin R → Fin o₁ × Fin o₂ → K) (W : Finset (Fin o₁ × Fin o₂)) :
    Submodule K ((Fin o₁ × Fin b) × (Fin o₁ × Fin o₂) → K) :=
  Submodule.span K ((fun l q => if q.2 ∈ W then u l q.1 * w l q.2 else 0) ''
    {l | ∃ z ∈ W, w l z ≠ 0})

open scoped Classical in
/-- `G_0 = ∑_{e ∈ W} A_{i(e)} ⊗ z_e`: spanned by the basis vectors `x_{i(e) j} ⊗ z_e`, `e ∈ W`. -/
noncomputable def fpG0 (K : Type) [Field K] (o₁ b : ℕ) {o₂ : ℕ} (W : Finset (Fin o₁ × Fin o₂)) :
    Submodule K ((Fin o₁ × Fin b) × (Fin o₁ × Fin o₂) → K) :=
  Submodule.span K ((fun q => Pi.single q (1 : K)) ''
    {q : (Fin o₁ × Fin b) × (Fin o₁ × Fin o₂) | q.2 ∈ W ∧ q.1.1 = q.2.1})

open scoped Classical in
/-- **Lemma 5 (b)** (any field). For a set `W` of outputs with at most one output
in every column: `G_0 ⊆ G_W`, `dim G_0 = b|W|`, the number of terms meeting `W` is at least
`dim G_W = b|W| + dim(G_W / G_0)`, and `dim G_W ≥ b|W| + #{e ∈ W : some term meets W only at e and
has u_l ∉ A_{i(e)}}`. -/
def FP_Lemma_5b : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → ∀ W : Finset (Fin o₁ × Fin o₂),
      (∀ e ∈ W, ∀ e' ∈ W, e.2 = e'.2 → e = e') →
      fpG0 K o₁ b W ≤ fpGW u w W ∧ Module.finrank K (fpG0 K o₁ b W) = b * W.card ∧
      Module.finrank K (fpGW u w W) ≤ (univ.filter fun l => ∃ z ∈ W, w l z ≠ 0).card ∧
      b * W.card + (W.filter fun e => ∃ l, w l e ≠ 0 ∧ (∀ z ∈ W, w l z ≠ 0 → z = e) ∧
          ∃ a : Fin o₁ × Fin b, a.1 ≠ e.1 ∧ u l a ≠ 0).card
        ≤ Module.finrank K (fpGW u w W)

open scoped Classical in
/-- **Lemma 5 (b)**, summed over a partition of the grid into `o₁` (resp. `o₂`) sets with one
output per column (resp. row): `∑_l min(|S_l|, o₁) ≥ b n + |E_A|` and
`∑_l min(|S_l|, o₂) ≥ b n + |E_B|`, where `E_A` (`E_B`) is the set of outputs `e` covered by a
singleton term (`S_l = {e}`) whose left (right) factor is not in `A_{i(e)}` (`Y_{c(e)}`). -/
def FP_Lemma_5b_sum : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w →
      b * (o₁ * o₂) + (univ.filter fun e : Fin o₁ × Fin o₂ => ∃ l, outSupp (w l) = {e} ∧
          ∃ a : Fin o₁ × Fin b, a.1 ≠ e.1 ∧ u l a ≠ 0).card
        ≤ ∑ l, min (outSupp (w l)).card o₁ ∧
      b * (o₁ * o₂) + (univ.filter fun e : Fin o₁ × Fin o₂ => ∃ l, outSupp (w l) = {e} ∧
          ∃ y : Fin b × Fin o₂, y.2 ≠ e.2 ∧ v l y ≠ 0).card
        ≤ ∑ l, min (outSupp (w l)).card o₂

open scoped Classical in
/-- **Lemma 5 (c)** (any field). Let `λ_e` be the number of coverers of `e` local to
`e`, and `D` the set of terms with `w_l ≠ 0` that are not pure singletons (a pure singleton has
`S_l = {e}` and is local to `e`); these are the terms nonlocal at some output they cover. Then `|D| ≥ #{e : λ_e < b}`, and `∑_e λ_e ≤ #{l : w_l ≠ 0} ≤ R`. -/
def FP_Lemma_5c : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w →
      (univ.filter fun e : Fin o₁ × Fin o₂ =>
          ((fpCov w e).filter fun l => fpLocal (u l) (v l) e).card < b).card
        ≤ (univ.filter fun l => w l ≠ 0 ∧ ¬ ∃ e, outSupp (w l) = {e} ∧ fpLocal (u l) (v l) e).card ∧
      ∑ e : Fin o₁ × Fin o₂, ((fpCov w e).filter fun l => fpLocal (u l) (v l) e).card
        ≤ (univ.filter fun l => w l ≠ 0).card

/-- The chord coefficient `c = (m^t - 1)/(m - 1)` of Theorems 2 and 2'. -/
noncomputable def fpC (m t : ℝ) : ℝ := (m ^ t - 1) / (m - 1)

/-- **Theorem 2', the inequality**: for real `m > 1`, a family `S_l ≥ 1` with
`R ≥ ρ n` members and `∑_l min(S_l, m) ≥ b n`, and `t ∈ [0, 1]` with
`(1 - c) ρ + c b ≥ b^{t/2}`, `c = (m^t - 1)/(m - 1)`, has `∑_l S_l^t ≥ n b^{t/2}` (two-point
inequality `s^t ≥ (1 - c) + c min(s, m)`). -/
def FP_Theorem_2p_ineq : Prop :=
  ∀ (n R : ℕ) (S : Fin R → ℕ) (b m ρ : ℝ), 1 < m → (∀ l, 1 ≤ S l) → ρ * n ≤ R →
    b * n ≤ ∑ l, min ((S l : ℕ) : ℝ) m →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → b ^ (t / 2) ≤ (1 - fpC m t) * ρ + fpC m t * b →
      (n : ℝ) * b ^ (t / 2) ≤ ∑ l, ((S l : ℕ) : ℝ) ^ t

open scoped Classical in
/-- **Theorem 2'**, composed with Lemmas 4 and 6: let `1 ≤ b < o₁ ≤ o₂`,
`m* = n/(o₁ + o₂ - 1)`, `ρ = 1 + (b - 1)/o₁`. For every `t ∈ [0, 1]` with
`(1 - c) ρ + c b ≥ b^{t/2}`, `c = (m*^t - 1)/(m* - 1)`, every decomposition of `⟨o₁, b, o₂⟩`
over any field has `∑_l |S_l|^t ≥ n b^{t/2}`, the sum over the terms with `w_l ≠ 0`. (If the
condition holds for all `t ∈ [0, 1]`, then `Γ ≥ 0`.) -/
def FP_Theorem_2p : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → 1 ≤ b → b < o₁ → o₁ ≤ o₂ →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (b : ℝ) ^ (t / 2) ≤ (1 - fpC (fpMstar o₁ o₂) t) * (1 + ((b : ℝ) - 1) / o₁)
          + fpC (fpMstar o₁ o₂) t * b →
      ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2)
        ≤ ∑ l ∈ univ.filter (fun l => w l ≠ 0), ((outSupp (w l)).card : ℝ) ^ t

/-- **Theorem 2'**, the clean sufficient condition: for real `b ≥ 1`, `m > 1`,
`ρ ≥ 1`, if `m ≤ b` or `m^{2(b-1)} ≥ b^{m-1}`, then `(1 - c) ρ + c b ≥ b^{t/2}` for every
`t ∈ [0, 1]`, `c = (m^t - 1)/(m - 1)`. -/
def FP_Theorem_2p_clean : Prop :=
  ∀ (b m ρ : ℝ), 1 ≤ b → 1 < m → 1 ≤ ρ → (m ≤ b ∨ b ^ (m - 1) ≤ m ^ (2 * (b - 1))) →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → b ^ (t / 2) ≤ (1 - fpC m t) * ρ + fpC m t * b

/-- The clean condition for `m* = n/d`, `d = o₁ + o₂ - 1`, cleared of denominators:
`m* ≤ b` iff `n ≤ b d`, and `m*^{2(b-1)} ≥ b^{m*-1}` iff `b^{n-d} d^{2(b-1)d} ≤ n^{2(b-1)d}`. -/
def fpCleanNat (o₁ b o₂ : ℕ) : Prop :=
  o₁ * o₂ ≤ b * (o₁ + o₂ - 1) ∨
    b ^ (o₁ * o₂ - (o₁ + o₂ - 1)) * (o₁ + o₂ - 1) ^ (2 * (b - 1) * (o₁ + o₂ - 1))
      ≤ (o₁ * o₂) ^ (2 * (b - 1) * (o₁ + o₂ - 1))

open scoped Classical in
/-- **Theorem 2'** with the clean condition: if `1 ≤ b < o₁ ≤ o₂` and `fpCleanNat o₁ b o₂`, every
decomposition of `⟨o₁, b, o₂⟩` over any field has `∑_l |S_l|^t ≥ n b^{t/2}` for all `t ∈ [0, 1]`
(sum over the terms with `w_l ≠ 0`), so `Γ ≥ 0`. -/
def FP_Theorem_2p_nat : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → 1 ≤ b → b < o₁ → o₁ ≤ o₂ → fpCleanNat o₁ b o₂ →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2)
        ≤ ∑ l ∈ univ.filter (fun l => w l ≠ 0), ((outSupp (w l)).card : ℝ) ^ t

/-- The clean condition holds for the squares `⟨k, b, k⟩`, `b < k ≤ K_b`, with
`K_b = 12, 17, 22, 27, 32, 37` for `b = 2, …, 7`, and fails at `k = K_b + 1`. -/
def FP_clean_squares : Prop :=
  ∀ p ∈ [(2, 12), (3, 17), (4, 22), (5, 27), (6, 32), (7, 37)],
    (∀ k, p.1 < k → k ≤ p.2 → fpCleanNat k p.1 k) ∧ ¬ fpCleanNat (p.2 + 1) p.1 (p.2 + 1)

open scoped Classical in
/-- The shapes `⟨7,2,7⟩, …, ⟨12,2,12⟩, ⟨10,3,10⟩, ⟨12,4,12⟩`, are
excluded: every decomposition over any field has `∑_l |S_l|^t ≥ n b^{t/2}` for all `t ∈ [0, 1]`. -/
def FP_open_shapes : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ),
    (o₁, b, o₂) ∈ [(7, 2, 7), (8, 2, 8), (9, 2, 9), (10, 2, 10), (11, 2, 11), (12, 2, 12),
      (10, 3, 10), (12, 4, 12)] →
    ∀ (u : Fin R → Fin o₁ × Fin b → K) (v : Fin R → Fin b × Fin o₂ → K)
      (w : Fin R → Fin o₁ × Fin o₂ → K), IsMMDecomp u v w →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2)
        ≤ ∑ l ∈ univ.filter (fun l => w l ≠ 0), ((outSupp (w l)).card : ℝ) ^ t

open scoped Classical in
/-- The crude value bound: for `b ≥ 1`, every
decomposition and every `t ∈ [0, 1]` has `ln ∑_l |S_l|^t - (t/2) ln b - ln n ≥ -(ln b)/2` (from
`∑ S^t ≥ #{l : w_l ≠ 0} ≥ n`). Hence `Γ ≥ -(ln b)/2` and `γ = -Γ/ln b ≤ 1/2`. -/
def FP_value_crude : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → 1 ≤ b → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      -(Real.log b) / 2 ≤ Real.log (∑ l ∈ univ.filter (fun l => w l ≠ 0),
          ((outSupp (w l)).card : ℝ) ^ t) - t / 2 * Real.log b - Real.log ((o₁ : ℝ) * o₂)

end FullProductOpen

/-! ## Thin full products in the paper: Appendix A.9

The paper's Appendix A.9 (`\label{a:sec:full}`) writes up the results above. Lemma A.12 is
`FP_L_average`/`FP_L_exists`, Lemma A.15 is `FP_Lemma_4` (a) and `FP_Lemma_4_avg` (b) (the paper's
translates of "first row + first column" under `ℤ_{o₁} × ℤ_{o₂}` are the double stars `fpStar`),
Lemma A.16 is `FP_Lemma_6`, Corollary A.18 is `FP_145_thin` with `FP_squared`. Below: Proposition
A.17 in the paper's form, Lemma A.13 (method of types), and the mathematical part of Theorem A.14. -/

section FullProductPaper

open scoped Classical in
/-- **Proposition A.17** (criterion): let `o₁, o₂ ≥ 2`, `b ≥ 1`, `f = n/(o₁+o₂-1)`, `κ = min(o₁,o₂)`,
`r = 1 + (b-1)/κ`, `c_t = (f^t - 1)/(f - 1)`. In each of the cases (i) `f ≤ b`,
(ii) `f^{2(b-1)} ≥ b^{f-1}`, (iii) `(1 - c_t) r + c_t b ≥ b^{t/2}` for every `t ∈ [0,1]`, every
decomposition of `⟨o₁, b, o₂⟩` over any field has `∑_l S_l^t ≥ n b^{t/2}` for every `t ∈ [0,1]`
(sum over the terms with `w_l ≠ 0`). -/
def FP_Prop_A_17 : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K),
    IsMMDecomp u v w → 2 ≤ o₁ → 2 ≤ o₂ → 1 ≤ b →
    (fpMstar o₁ o₂ ≤ b ∨ (b : ℝ) ^ (fpMstar o₁ o₂ - 1) ≤ fpMstar o₁ o₂ ^ (2 * ((b : ℝ) - 1)) ∨
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (b : ℝ) ^ (t / 2) ≤ (1 - fpC (fpMstar o₁ o₂) t) * (1 + ((b : ℝ) - 1) / (min o₁ o₂ : ℕ))
          + fpC (fpMstar o₁ o₂) t * b) →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2)
        ≤ ∑ l ∈ univ.filter (fun l => w l ≠ 0), ((outSupp (w l)).card : ℝ) ^ t

/-- **Proposition A.17**, last sentence: case (i) holds whenever `κ ≤ b`, and case (ii) whenever
`κ^{2(b-1)} ≥ b^{κ-1}` (integers). -/
def FP_Prop_A_17_kappa : Prop :=
  ∀ o₁ b o₂ : ℕ, 2 ≤ o₁ → 2 ≤ o₂ → 1 ≤ b →
    (min o₁ o₂ ≤ b → fpMstar o₁ o₂ ≤ b) ∧
    (b ^ (min o₁ o₂ - 1) ≤ (min o₁ o₂) ^ (2 * (b - 1)) →
      (b : ℝ) ^ (fpMstar o₁ o₂ - 1) ≤ fpMstar o₁ o₂ ^ (2 * ((b : ℝ) - 1)))

/-- The leaf count of Lemma A.13: `V_L = ∑_{τ ∈ [R]^L} min{1, β^{-L} ∏_ℓ S_{τ_ℓ}}`. -/
noncomputable def fpVL {R : ℕ} (S : Fin R → ℕ) (β : ℝ) (L : ℕ) : ℝ :=
  ∑ τ : Fin L → Fin R, min 1 ((∏ ℓ, (S (τ ℓ) : ℝ)) / β ^ L)

/-- `F(t) = ln ∑_l S_l^t - t ln β` of Lemma A.13. -/
noncomputable def fpF {R : ℕ} (S : Fin R → ℕ) (β t : ℝ) : ℝ :=
  Real.log (∑ l, (S l : ℝ) ^ t) - t * Real.log β

/-- **Lemma A.13** (method of types), quantitative form: for integers `S_1, …, S_R ≥ 1`
(`R ≥ 1`) and `β > 0`: `V_L ≤ e^{L F(t)}` for every `t ∈ [0,1]`; and there are `t₀ ∈ [0,1]` and a
constant `C` with `ln V_L ≥ L F(t₀) - C √L - ln 2` for every `L ≥ 1`. -/
def FP_Lemma_A_13_bounds : Prop :=
  ∀ (R : ℕ) (S : Fin R → ℕ) (β : ℝ), 1 ≤ R → (∀ l, 1 ≤ S l) → 0 < β →
    (∀ (L : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 → fpVL S β L ≤ Real.exp (L * fpF S β t)) ∧
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ ≤ 1 ∧ ∃ C : ℝ, ∀ L : ℕ, 1 ≤ L →
      (L : ℝ) * fpF S β t₀ - C * Real.sqrt L - Real.log 2 ≤ Real.log (fpVL S β L)

/-- **Lemma A.13**: `F` attains its minimum `F*` on `[0,1]` at some `t₀`, and
`(1/L) ln V_L → F*` as `L → ∞`. -/
def FP_Lemma_A_13 : Prop :=
  ∀ (R : ℕ) (S : Fin R → ℕ) (β : ℝ), 1 ≤ R → (∀ l, 1 ≤ S l) → 0 < β →
    ∃ t₀ : ℝ, 0 ≤ t₀ ∧ t₀ ≤ 1 ∧ (∀ t : ℝ, 0 ≤ t → t ≤ 1 → fpF S β t₀ ≤ fpF S β t) ∧
      Filter.Tendsto (fun L : ℕ => Real.log (fpVL S β L) / L) Filter.atTop
        (nhds (fpF S β t₀))

/-- **Theorem A.14**, the tiling: if `o₁^L` and `o₂^L` divide `N`, the `N × N` entries are tiled
by `(N/o₁^L)(N/o₂^L) = N²/n^L` runs, and (runs) × (output strings `[n]^L` of a run) is in bijection
with the entries. -/
def FP_Thm_A_14_tiling : Prop :=
  ∀ o₁ o₂ L N : ℕ, o₁ ^ L ∣ N → o₂ ^ L ∣ N →
    (N / o₁ ^ L) * (N / o₂ ^ L) * (o₁ * o₂) ^ L = N * N ∧
    Nonempty ((Fin (N / o₁ ^ L) × Fin (N / o₂ ^ L)) × (Fin L → Fin o₁ × Fin o₂) ≃ Fin N × Fin N)

/-- **Theorem A.14**, the size of `W`: `w = ⌈N²/√D⌉`, `D = b^L`, satisfies `w ≤ N²` and
`ρ = w/N² ≥ b^{-L/2}`. -/
def FP_Thm_A_14_rho : Prop :=
  ∀ b L N : ℕ, 1 ≤ b → 1 ≤ N →
    ⌈((N * N : ℕ) : ℝ) / Real.sqrt ((b : ℝ) ^ L)⌉₊ ≤ N * N ∧
    (b : ℝ) ^ (-(L : ℝ) / 2) ≤ (⌈((N * N : ℕ) : ℝ) / Real.sqrt ((b : ℝ) ^ L)⌉₊ : ℝ) / (N * N : ℕ)

open scoped Classical in
/-- The contribution relation of the tiled run (Theorem A.14): a leaf is a run `p` and a string
`τ ∈ [R]^L` of terms, an entry is a run `p'` and an output string `ω ∈ [n]^L`, and the leaf
contributes to the entry iff `p' = p` and `ω_ℓ ∈ Z_{τ_ℓ}` at every level. -/
noncomputable def fpRunA {P o₁ o₂ R L : ℕ} (Z : Fin R → Finset (Fin o₁ × Fin o₂))
    (x : Fin P × (Fin L → Fin R)) : Finset (Fin P × (Fin L → Fin o₁ × Fin o₂)) :=
  univ.filter fun y => y.1 = x.1 ∧ ∀ ℓ, y.2 ℓ ∈ Z (x.2 ℓ)

/-- **Theorem A.14**, the leaf count of the tiled run: with `P` runs and `ρ ≥ β^{-L}`,
`V = ∑_{leaves} min{1, ρ s(τ)} ≥ P · V_L`, where `s(τ) = ∏_ℓ |Z_{τ_ℓ}|` is the number of
entries the leaf contributes to. -/
def FP_Thm_A_14_V : Prop :=
  ∀ (P o₁ o₂ R L : ℕ) (Z : Fin R → Finset (Fin o₁ × Fin o₂)) (ρ β : ℝ), 0 < β → β⁻¹ ^ L ≤ ρ →
    (∀ x : Fin P × (Fin L → Fin R), (fpRunA Z x).card = ∏ ℓ, (Z (x.2 ℓ)).card) ∧
    (P : ℝ) * fpVL (fun l => (Z l).card) β L
      ≤ ∑ x : Fin P × (Fin L → Fin R), min 1 (ρ * (fpRunA Z x).card)

/-- **Theorem A.14** (the mathematical part): let the output supports `Z_l` of the terms be
nonempty and satisfy `Γ ≥ 0`, i.e. `∑_l |Z_l|^t ≥ n b^{t/2}` for every `t ∈ [0,1]`, `b ≥ 1`. Then
there is `δ_L → 0`, depending only on the supports and `b`, such that for every `L` and every `N`
with `o₁^L, o₂^L ∣ N`, `N ≥ 1`, some set `W` of exactly `⌈N²/√(b^L)⌉` entries of the tiled run has
`|Leaves(W)| ≥ (1-1/e) N² e^{-δ_L L}`. (That the pruned recursion of each run visits exactly the
leaves of `Leaves(W)` in that run is the preprint's Lemma 10, `FP_Lemma_10`.) -/
def FP_Thm_A_14 : Prop :=
  ∀ (o₁ o₂ b R : ℕ) (Z : Fin R → Finset (Fin o₁ × Fin o₂)), 1 ≤ b → 1 ≤ R →
    (∀ l, (Z l).Nonempty) →
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2) ≤ ∑ l, ((Z l).card : ℝ) ^ t) →
    ∃ δ : ℕ → ℝ, Filter.Tendsto δ Filter.atTop (nhds 0) ∧
      ∀ L N : ℕ, o₁ ^ L ∣ N → o₂ ^ L ∣ N → 1 ≤ N →
        ∃ W : Finset (Fin (N / o₁ ^ L * (N / o₂ ^ L)) × (Fin L → Fin o₁ × Fin o₂)),
          W.card = ⌈((N * N : ℕ) : ℝ) / Real.sqrt ((b : ℝ) ^ L)⌉₊ ∧
          (1 - Real.exp (-1)) * ((N * N : ℕ) : ℝ) * Real.exp (-(δ L * L))
            ≤ (fpLeaves (fpRunA Z) W).card

/-- **Theorem A.14**, the last sentence, for `b ≥ 2`: under the hypotheses of `FP_Thm_A_14`, for
every `γ > 0` there are `L` and `N` (with `o₁^L, o₂^L ∣ N`) and a set `W` of exactly `⌈N²/√D⌉`
entries, `D = b^L`, with `|Leaves(W)| > N²/D^γ`: no `γ > 0` bounds the leaf count by `N²/D^γ` for
every such `W`. (For `b = 1` the sentence is false: `D = 1`.) -/
def FP_Thm_A_14_no_saving : Prop :=
  ∀ (o₁ o₂ b R : ℕ) (Z : Fin R → Finset (Fin o₁ × Fin o₂)), 2 ≤ b → 1 ≤ R →
    (∀ l, (Z l).Nonempty) →
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 → ((o₁ * o₂ : ℕ) : ℝ) * (b : ℝ) ^ (t / 2) ≤ ∑ l, ((Z l).card : ℝ) ^ t) →
    ∀ γ : ℝ, 0 < γ → ∃ L N : ℕ, o₁ ^ L ∣ N ∧ o₂ ^ L ∣ N ∧ 1 ≤ N ∧
      ∃ W : Finset (Fin (N / o₁ ^ L * (N / o₂ ^ L)) × (Fin L → Fin o₁ × Fin o₂)),
        W.card = ⌈((N * N : ℕ) : ℝ) / Real.sqrt ((b : ℝ) ^ L)⌉₊ ∧
        ((N * N : ℕ) : ℝ) / ((b : ℝ) ^ L) ^ γ < (fpLeaves (fpRunA Z) W).card

/-- **Corollary A.18**, end to end for the thin shapes: for every shape of `fpShapes145`, in either
orientation, every decomposition over any field (terms with `w_l = 0` dropped, as in the paper)
gives no saving in the leaf count of the tiled run: for every `γ > 0` some admissible `L, N` and
some `W` of exactly `⌈N²/√D⌉` entries have `|Leaves(W)| > N²/D^γ`. -/
def FP_Cor_A_18 : Prop :=
  ∀ (K : Type) [Field K] (o₁ b o₂ R : ℕ),
    ((o₁, b, o₂) ∈ fpShapes145 ∨ (o₂, b, o₁) ∈ fpShapes145) →
    ∀ (u : Fin R → Fin o₁ × Fin b → K) (v : Fin R → Fin b × Fin o₂ → K)
      (w : Fin R → Fin o₁ × Fin o₂ → K), IsMMDecomp u v w → (∀ l, w l ≠ 0) →
    ∀ γ : ℝ, 0 < γ → ∃ L N : ℕ, o₁ ^ L ∣ N ∧ o₂ ^ L ∣ N ∧ 1 ≤ N ∧
      ∃ W : Finset (Fin (N / o₁ ^ L * (N / o₂ ^ L)) × (Fin L → Fin o₁ × Fin o₂)),
        W.card = ⌈((N * N : ℕ) : ℝ) / Real.sqrt ((b : ℝ) ^ L)⌉₊ ∧
        ((N * N : ℕ) : ℝ) / ((b : ℝ) ^ L) ^ γ
          < (fpLeaves (fpRunA (fun l => outSupp (w l))) W).card

end FullProductPaper

/-! ## [ZT, Section 2.4.2 and Lemma 10]: the pruned recursion

The paper uses [ZT, Lemma 10] twice. In Part I (Section 6): "The pruned recursion of the preprint's
Section 2.4.2 and its Lemma 10 apply verbatim on the `2L` levels, with `Π(τ)` returned at a leaf."
In Appendix A.9: "The pruned recursion of the preprint's Section 2.4.2 is defined for every identity
(its step (2) forms the set passed to a term from the sets of the outputs the term contributes to),
and the proof of the preprint's Lemma 10 applies verbatim: for a set `W` of wanted entries it
visits exactly `Leaves(W)` […] and computes one product at each of them."

So the recursion is written once, for any identity: the terms form a finite type `T`, the output
letters a finite type `Z`, and `R λ z` says that the output form of the term `λ` contains `z` (the
same at every level, as in both uses). A leaf on `n` levels is `Fin n → T` and an output string
`Fin n → Z`. Step (1) returns a number `g τ` given at the leaf (in [ZT] `Φ_τ(a) Ψ_τ(b)`, read from
the encodings; in Part I `Π(τ) = ∑_s Φ_τ(a_s) Ψ_τ(b_s)`). The definitions follow `3sum-apsp`
(`PaperStatements.lean`, Section 2.4.2, Apache 2.0, Anthropic PBC), with Schönhage's identity
replaced by `R`. -/

namespace Pr

section Defs

variable {T Z : Type} [Fintype T] [Fintype Z] [DecidableEq Z]

/-- [ZT, Section 2.3.2]: the leaf `τ` contributes to the output string `w` if the output form of
`τ_ℓ` contains `w_ℓ` at every level. -/
def Contrib (R : T → Z → Prop) {n : ℕ} (τ : Fin n → T) (w : Fin n → Z) : Prop := ∀ ℓ, R (τ ℓ) (w ℓ)

instance (R : T → Z → Prop) [DecidableRel R] {n : ℕ} (τ : Fin n → T) (w : Fin n → Z) :
    Decidable (Contrib R τ w) := by
  unfold Contrib; infer_instance

/-- [ZT, Section 2.4.2]: "For a set U of output strings of length L, we write Leaves(U) for the set
of leaves that contribute to some output string of U." -/
def Leaves (R : T → Z → Prop) [DecidableRel R] {n : ℕ} (U : Finset (Fin n → Z)) :
    Finset (Fin n → T) :=
  univ.filter fun τ => ∃ w ∈ U, Contrib R τ w

/-- [ZT, Section 2.4.2]: "the slice S_z is the set of output strings w' with z w' ∈ S". -/
def sliceSet {n : ℕ} (S : Finset (Fin (n + 1) → Z)) (z : Z) : Finset (Fin n → Z) :=
  univ.filter fun w' => (Fin.cons z w' : Fin (n + 1) → Z) ∈ S

/-- [ZT, Section 2.4.2], step (2) of `Pruned`: "let S_λ be the union of the slices S_z over the z
to which λ contributes". -/
def childSet (R : T → Z → Prop) [DecidableRel R] {n : ℕ} (S : Finset (Fin (n + 1) → Z)) (lam : T) :
    Finset (Fin n → Z) :=
  (univ.filter fun z => R lam z).biUnion fun z => sliceSet S z

/-- An array on `S`, written as a function on all output strings that is `0` outside `S`. -/
def restrictTo {n : ℕ} (S : Finset (Fin n → Z)) (c : (Fin n → Z) → ℤ) : (Fin n → Z) → ℤ :=
  fun w => if w ∈ S then c w else 0

end Defs

/-- A call of `Pruned`: the vertex `τ₁⋯τ_k` at which it is made (its depth `k` and the string of
terms) and the set passed to it (the length of its strings and the set). -/
structure Call (T Z : Type) where
  vertex : Σ k, Fin k → T
  passed : Σ n, Finset (Fin n → Z)

/-- The same call seen from one level higher: the vertex `τ₁⋯τ_k` below the child `λ` is the vertex
`λ τ₁⋯τ_k`. -/
def Call.under {T Z : Type} (lam : T) (c : Call T Z) : Call T Z where
  vertex := ⟨c.vertex.1 + 1, (Fin.cons lam c.vertex.2 : Fin (c.vertex.1 + 1) → T)⟩
  passed := c.passed

section Run

variable {T Z : Type} [Fintype T] [Fintype Z] [DecidableEq Z]

/-- [ZT, Section 2.4.2]: "Pruned_{τ₁⋯τ_k}(S), for a set S of output strings of length L - k, returns
the array returned by the vertex τ₁⋯τ_k of Full, restricted to the strings in S: (1) If k = L, then
look up Φ_τ(a) and Ψ_τ(b) from the precomputed encodings (Section 2.4.1) and return Φ_τ(a) Ψ_τ(b)
for the leaf τ = τ₁⋯τ_L. (2) For each term λ […], let S_λ be the union of the slices S_z over the z
to which λ contributes […]. (3) For each term λ […] with S_λ ≠ ∅, compute
C_λ := Pruned_{τ₁⋯τ_k λ}(S_λ), an array on S_λ. (4) Return the array c on S whose slices are
c_{z_ij} := C_{P_ij} and c_{z₀} := ∑_λ C_λ, restricted to S_{z_ij} and to S_{z₀}."

For any identity, step (4) is `c_z := ∑_{λ contributing to z} C_λ` (for Schönhage's identity this is
the printed step). Here `n = L - k`; `g τ'` is the number of step (1) at the leaf `τ₁⋯τ_k τ'`, so the
child `λ` receives `τ' ↦ g (λ τ')`. The second component records every call made, this one
included, with the set passed to it; a term with `S_λ = ∅` makes no call and its `C_λ` is written
as the zero array (step (4) reads it only on `S_λ`). -/
def run (R : T → Z → Prop) [DecidableRel R] :
    (n : ℕ) → ((Fin n → T) → ℤ) → Finset (Fin n → Z) → ((Fin n → Z) → ℤ) × Multiset (Call T Z)
  | 0, g, S => (restrictTo S fun _ => g Fin.elim0, {⟨⟨0, Fin.elim0⟩, ⟨0, S⟩⟩})
  | n + 1, g, S =>
    let C : T → ((Fin n → Z) → ℤ) × Multiset (Call T Z) := fun lam =>
      if (childSet R S lam).Nonempty then
        run R n (fun τ' => g (Fin.cons lam τ')) (childSet R S lam)
      else (0, 0)
    (restrictTo S fun w => ∑ lam ∈ univ.filter (fun lam => R lam (w 0)), (C lam).1 (Fin.tail w),
      ⟨⟨0, Fin.elim0⟩, ⟨n + 1, S⟩⟩ ::ₘ univ.val.bind fun lam => (C lam).2.map (Call.under lam))

/-- The array that `Pruned(S)` returns. -/
def Pruned (R : T → Z → Prop) [DecidableRel R] (n : ℕ) (g : (Fin n → T) → ℤ)
    (S : Finset (Fin n → Z)) : (Fin n → Z) → ℤ :=
  (run R n g S).1

/-- All the calls that `Pruned(S)` makes, itself included, each with the set passed to it. -/
def calls (R : T → Z → Prop) [DecidableRel R] (n : ℕ) (g : (Fin n → T) → ℤ)
    (S : Finset (Fin n → Z)) : Multiset (Call T Z) :=
  (run R n g S).2

/-- The leaves that `Pruned(U)`, called at the root, visits: the vertices at depth `L` among its
calls. -/
def Visits (R : T → Z → Prop) [DecidableRel R] (L : ℕ) (g : (Fin L → T) → ℤ)
    (U : Finset (Fin L → Z)) (τ : Fin L → T) : Prop :=
  ∃ c ∈ calls R L g U, c.vertex = ⟨L, τ⟩

/-- The total size of the sets passed to the calls that `Pruned(U)` makes. -/
def totalSize (R : T → Z → Prop) [DecidableRel R] (L : ℕ) (g : (Fin L → T) → ℤ)
    (U : Finset (Fin L → Z)) : ℕ :=
  ((calls R L g U).map fun c => c.passed.2.card).sum

end Run

/-- The contribution relation of the identity of Part I (Lemma 3.1), the same at all `2L` levels:
the output form `χ_λ` contains `z`. -/
def chiRel (lam : Tm) (z : ZL) : Prop := chi lam z ≠ 0

instance : DecidableRel chiRel := fun lam z => by unfold chiRel; infer_instance

/-- The contribution relation of a decomposition with output supports `Z_l` (Appendix A.9): the
term `l` contributes to the output `z` iff `z ∈ Z_l`. -/
def suppRel {R O : Type} (Zs : R → Finset O) (l : R) (z : O) : Prop := z ∈ Zs l

instance {R O : Type} (Zs : R → Finset O) [DecidableEq O] : DecidableRel (suppRel Zs) :=
  fun l z => by unfold suppRel; infer_instance

end Pr

/-- **[ZT, Lemma 10]**, for any identity. "Let a and b be input arrays, and let U be a set of output
strings of length L. Called at the root, Pruned(U) returns Mult(a, b) restricted to U. The leaves it
visits are exactly those of Leaves(U), and the sets passed to the calls it makes have total size at
most (L+1) |Leaves(U)|." With the numbers `g τ` of step (1) in place of `Φ_τ(a) Ψ_τ(b)`, `Mult` is
`w ↦ ∑_{τ contributing to w} g τ` ([ZT, eq. (2)]).

NOTE. Two hypotheses are not in [ZT]. (i) `0 < L ∨ U ≠ ∅` in the second claim: for `L = 0`,
`U = ∅` the root is a leaf and is visited, while `Leaves(∅) = ∅`. (ii) The third claim assumes an
injective choice `p` of a term contributing to each output letter (for Schönhage's identity and for
the identity of Lemma 3.1, `P_ij` for `z_ij` and `P₀` for `z₀`): the proof injects each set passed
into leaves by the private leaf, and without such a choice the bound can fail (one term contributing
to two letters). -/
def Lemma_10_generic : Prop :=
  ∀ {T Z : Type} [Fintype T] [Fintype Z] [DecidableEq Z] (R : T → Z → Prop) [DecidableRel R]
    {L : ℕ} (g : (Fin L → T) → ℤ) (U : Finset (Fin L → Z)),
    Pr.Pruned R L g U
        = (fun w => if w ∈ U then ∑ τ ∈ univ.filter (fun τ => Pr.Contrib R τ w), g τ else 0) ∧
    (0 < L ∨ U.Nonempty → ∀ τ : Fin L → T, Pr.Visits R L g U τ ↔ τ ∈ Pr.Leaves R U) ∧
    ∀ p : Z → T, Function.Injective p → (∀ z, R (p z) z) →
      Pr.totalSize R L g U ≤ (L + 1) * (Pr.Leaves R U).card

/-- **[ZT, Lemma 10] on the `2L` levels** (Section 6): "The pruned recursion of the preprint's
Section 2.4.2 and its Lemma 10 apply verbatim on the `2L` levels, with `Π(τ)` returned at a leaf."
For the arrays `a_s`, `b_s` of the runs `s ∈ [-m, m]` and a set `U` of read output strings of a
tile, the recursion on the flattened levels `1, …, 2L` (the first half below the second), called on
the flattened strings of `U`, with `Π(τ) = ∑_s Φ_τ(a_s) Ψ_τ(b_s)` computed from the encodings of
[ZT, Section 2.4.1] (`encodeL`, `encodeR`) at the leaf `τ`: returns `∑_s Mult(a_s, b_s)[w]` at every
`w ∈ U` and `0` elsewhere; visits exactly the leaves of `Leaves(U)`; and passes sets of total size at
most `(2L + 1) |Leaves(U)|` (the `L + 1` depths of [ZT] become `2L + 1`). -/
def Lemma_10_squared : Prop :=
  ∀ {L m : ℕ} (a : ℤ → LeftStr L → ℤ) (b : ℤ → RightStr L → ℤ) (U : Finset (OutStr L)),
    let g : Sq.FLeaf (L + L) → ℤ := fun τ => ∑ s ∈ Icc (-(m : ℤ)) m,
      encodeL (a s) (Sq.unflatLeaf τ) * encodeR (b s) (Sq.unflatLeaf τ)
    (∀ w : OutStr L, Pr.Pruned Pr.chiRel (L + L) g (U.image Sq.flatOut) (Sq.flatOut w)
        = if w ∈ U then ∑ s ∈ Icc (-(m : ℤ)) m, Mult (a s) (b s) w else 0) ∧
    (0 < L ∨ U.Nonempty → ∀ τ : Leaf L,
      Pr.Visits Pr.chiRel (L + L) g (U.image Sq.flatOut) (Sq.flatLeaf τ) ↔ τ ∈ Leaves U) ∧
    Pr.totalSize Pr.chiRel (L + L) g (U.image Sq.flatOut) ≤ (2 * L + 1) * (Leaves U).card

/-- **[ZT, Lemma 10] for the tiled run of Theorem A.14** (Appendix A.9): "for a set `W` of wanted
entries it visits exactly `Leaves(W)`, the leaves contributing to an output string of `W`, and
computes one product at each of them." For a decomposition with output supports `Z_l` at `L`
levels, a set `W` of wanted entries of the `P` runs and a run `p`, the pruned recursion of run `p`,
called on the output strings of `W` in run `p`, with any numbers `g` at the leaves: returns at each
wanted string the sum of `g` over the leaves contributing to it (`0` elsewhere), and visits the leaf
`τ` exactly if `(p, τ) ∈ Leaves(W)` for the contribution relation `fpRunA` of Theorem A.14. -/
def FP_Lemma_10 : Prop :=
  ∀ {P o₁ o₂ R L : ℕ} (Zs : Fin R → Finset (Fin o₁ × Fin o₂))
    (W : Finset (Fin P × (Fin L → Fin o₁ × Fin o₂))) (p : Fin P) (g : (Fin L → Fin R) → ℤ),
    let Wp : Finset (Fin L → Fin o₁ × Fin o₂) := univ.filter fun ω => (p, ω) ∈ W
    (∀ ω, Pr.Pruned (Pr.suppRel Zs) L g Wp ω = if (p, ω) ∈ W then
        ∑ τ ∈ univ.filter (fun τ => ∀ ℓ, ω ℓ ∈ Zs (τ ℓ)), g τ else 0) ∧
    (0 < L ∨ Wp.Nonempty → ∀ τ : Fin L → Fin R,
      Pr.Visits (Pr.suppRel Zs) L g Wp τ ↔ (p, τ) ∈ fpLeaves (fpRunA Zs) W)

end ThinMatrixProducts

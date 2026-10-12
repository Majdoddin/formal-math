/-
Results that the paper takes from the literature, each as a proposition, with its reference and a
quotation. A theorem that uses one of them takes it as a hypothesis; none is an axiom.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ThinMatrixProducts.Assumptions

open Finset

/-- **[RS62, Corollary 1]** (J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions
of prime numbers, Illinois J. Math. 6 (1962)), as quoted in the proof of Lemma 12.1: "`π(x) > x/ln x`
for `x ≥ 17` and `π(x) < 1.25506 x/ln x` for `x > 1`". Here `π(x)` is the number of primes `≤ x`,
`Nat.primeCounting ⌊x⌋₊`. -/
def RosserSchoenfeld : Prop :=
  (∀ x : ℝ, 17 ≤ x → x / Real.log x < (Nat.primeCounting ⌊x⌋₊ : ℝ)) ∧
  (∀ x : ℝ, 1 < x → (Nat.primeCounting ⌊x⌋₊ : ℝ) < 1.25506 * x / Real.log x)

/-- **[FKP24, Lemma 3.3]** (N. Fischer, P. Kaliciak, A. Polak, Deterministic 3SUM-hardness, ITCS
2024, arXiv 2310.12913v2, pp. 8–9), the part that the paper uses: "Let `A ⊆ [U]` be a set of size
`n`, and let `g ≥ 1`. We can deterministically construct a partition of `A` into subsets
`A_1, …, A_g`, and a set of triples `R ⊆ [g]^3` of size `O(g²)` such that: Each set `A_i` has size
`O(n/g)` […]. For all triples `a, b, c ∈ A` with `a + b = c`, there is some `(i, j, k) ∈ R` with
`a ∈ A_i`, `b ∈ A_j`, `c ∈ A_k`." With the constants of its proof, `c₁, c₂ ≥ 1` such that
`|A_i| ≤ c₁ n/g` and `|R| ≤ c₂ g²` (Section 13.1 of the paper). The partition is given by the
group `grp a` of each element; `a = b` is allowed (Section 13.1). The interval property, the
running time `Õ(n + g²)` and the construction are not used here and not stated. -/
def FKP_Lemma_3_3 : Prop :=
  ∃ c₁ c₂ : ℕ, 1 ≤ c₁ ∧ 1 ≤ c₂ ∧
    ∀ (U : ℕ) (A : Finset ℕ), (∀ a ∈ A, 1 ≤ a ∧ a ≤ U) → ∀ g : ℕ, 1 ≤ g →
      ∃ (grp : ℕ → Fin g) (R : Finset (Fin g × Fin g × Fin g)),
        (∀ i : Fin g, ((A.filter fun a => grp a = i).card : ℝ) ≤ c₁ * A.card / g) ∧
        (R.card : ℝ) ≤ c₂ * (g : ℝ) ^ 2 ∧
        ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a + b = c → (grp a, grp b, grp c) ∈ R

open Classical in
/-- **[CVX23, Lemma 9.2]** (T. M. Chan, V. Vassilevska Williams, Y. Xu, Fredman's trick meets
dominance product: fine-grained complexity of unweighted APSP, 3SUM counting, and more, STOC 2023,
arXiv:2303.14572v1, p. 35), quoted in Section 15.6 (Link 2): "Given a #AE-Neg-Tri instance on an
`n`-node tripartite graph `G` with node partitions `A`, `B`, and `C` and with edge weights in
`[±n^{O(1)}]`, we can reduce it to `O(log n)` instances of #AE-Exact-Tri on graphs with the same
vertex set and with edge weights in `[±n^{O(1)}]` deterministically in `Õ(n²)` time. Furthermore,
the count for an edge in the original #AE-Neg-Tri instance can be written as a sum of the count for
the corresponding edge among the #AE-Exact-Tri instances (if this edge does not exist in a certain
instance, then the count is simply 0)." The paper's reading of the proof adds: the instances have
target values `0` or `1`, and no vertices are added.

Only the counting identity enters the mathematics checked here (`Sec15_link2`: a sum of counts is
positive iff one count is); the reduction itself is an algorithm, with a running time, and is not
stated. This proposition records the identity for a fixed instance: there are `O(log n)` many
exact-triangle instances on the same vertex set, given by their weights (`none` for a missing
edge) and targets `t ∈ {0, 1}`, such that every edge's negative-triangle count is the sum of its
exact-triangle counts. -/
def CVX23_Lemma_9_2 : Prop :=
  ∃ c : ℕ, ∀ (n : ℕ) (A B C : Finset (Fin n)) (w : Fin n → Fin n → ℤ),
    ∃ (I : ℕ) (wI : Fin I → Fin n → Fin n → Option ℤ) (t : Fin I → ℤ),
      I ≤ c * (Nat.log 2 n + 1) ∧ (∀ i, t i = 0 ∨ t i = 1) ∧
      ∀ a ∈ A, ∀ c' ∈ C,
        ((B.filter fun b => w a b + w b c' + w a c' < 0).card : ℤ)
          = ∑ i, ((B.filter fun b => ∃ x y z, wI i a b = some x ∧ wI i b c' = some y ∧
              wI i a c' = some z ∧ x + y + z = t i).card : ℤ)

end ThinMatrixProducts.Assumptions

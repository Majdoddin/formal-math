# A Lean check of the mathematics of "Thin matrix products up to D ≤ N^0.172", Parts I and II and Appendix A

This folder is a Lean 4 project (Lean v4.33.1, Mathlib v4.33.1) that states items of the paper
*Thin matrix products up to D ≤ N^0.172 and lossless reductions for 3SUM, Exact Triangle and APSP,
with 3SUM over abelian groups and a dichotomy for coordinatewise problems* by Ruhollah Majdoddin
(12 October 2026, 130 pages) in the paper's numbering and proves them. It covers the paper outside
Sections 18–21 (Section 22.2 of the paper); Section 18 (3XOR) is formalised in
[`../xor-3xor`](../xor-3xor), Sections 19–21 (groups, coordinatewise problems, triangle
versions) in [`../groups`](../groups). The aim is reasonable confidence that the paper's mathematics has no mistakes, not a
formal validation of everything: running times on a machine are not formalized (only the counts and
the arithmetic of the bounds), statements of the preprint [ZT] = arXiv:2610.06783v1 and of the
other cited works are taken as given, and computer calculations stay with the paper's scripts.

All item numbers in this README and in the docstrings are those of the paper of 12 October 2026.
A few Lean names keep the number an item had in earlier drafts; the tables give the current item
for each: `Remark_10_3_*` is Proposition 10.3, `Remark_17_1_arith` is the paragraph "The limit is
Coppersmith's exponent" of Section 8, and the `FP_*` names of the last two tables are mapped there
to the items of Appendix A.9.

## Layout

| File | What it holds |
|---|---|
| `Statements.lean` | the statements, as propositions named after the paper's items (`Corollary_9_1_a_Lambda`, `Theorem_5_1`, ...), with the definitions that they use; a `NOTE` in a docstring marks a departure from the printed text |
| `Assumptions.lean` | the results taken from the literature, each a proposition with its reference and a quotation; a theorem that uses one takes it as a hypothesis (none is an axiom) |
| `ThinMatrixProducts/` | the proofs |
| `Checks.lean` | one line per statement, `theorem x : X := ...`, naming its proof (written by `scripts/gen_checks.py`) |

`#print axioms` of every theorem in `Checks.lean` shows only `propext`, `Classical.choice` and
`Quot.sound`.

Code adapted from the formalization of [ZT] in `../3sum-apsp` (Apache 2.0, Anthropic PBC; each
of these files says so in its header): `ThinMatrixProducts/Util/LogBounds.lean` (the enclosure of
logarithms by their series), `ThinMatrixProducts/Util/Choose.lean` (binomial bounds),
`ThinMatrixProducts/PartII/RepeatedSquaring.lean` (APSP by repeated squaring), and parts of
`ThinMatrixProducts/PartI/Boxes.lean` ([ZT, Lemmas 27–29]), `ThinMatrixProducts/PartI/Query.lean`
([ZT, Lemma 7]), `ThinMatrixProducts/PartI/Pruned.lean` ([ZT, Lemma 10]) and of `Statements.lean`
(the definitions of the APSP part); `exp_H_div_le_choose` in
`ThinMatrixProducts/Numerics/Corollary73.lean` follows `exp_entropy_div_le_choose` there. The project
does not depend on `../3sum-apsp`: every statement of [ZT] that the paper uses is specialised there
to Schönhage's identity, so none can be imported, and a path dependency would rebuild that project
whenever its working tree changes.

## Build

    lake build

## Status of the items

"Proved" means proved in Lean from the definitions in `Statements.lean`, with no hypothesis beyond
those printed in the statement.

| Item of the paper | Lean name | Status |
|---|---|---|
| Theorem A, abstract: `1/ε*_5 = 5 ln 5/ln 4 = 5.8048…`, `5 ln 10/ln 4 = 8.3048…` | `Theorem_A_thresholds` | proved |
| `ε*_5 = 0.17227…`, `ε*_10 = 0.12041…` | `Sec1_epsStar5_value`, `Sec1_epsStar10_value` | proved |
| Proposition 8.1: the form `2 ln q₀/(R ln R)`; the range `ε < ε*_5`; `c > 5`; the binomial terms at `c = 5` (and `c = 10` for [ZT]); `D^{1/ε*_5} = 5^{5m}` | `Proposition_8_1_form`, `Proposition_8_1_range`, `Proposition_8_1_terms` | proved |
| Section 4: `μ_k` as a probability; `μ_∞ = 0.2887…`, `μ_∞² = 0.08339…`, `μ_k > μ_∞`, `μ_∞^{-4} < 144` | `Sec4_mu_probability`, `Sec4_mu_values` | proved |
| Equation (2): the two forms of `R'_c(γ)` | `Eq_2_forms` | proved |
| Equations (3), (4): the encoding bound, and `(25/4)/μ_∞² < 75` | `Eq_4`, `Eq_4_constant` | proved |
| Corollary 7.3: `γ > 0`; the boxes `ρ^t ≤ D^{-γ}`; the queries `∑ ≤ 4x D^q`; `N ≥ K N₀`; `ε < R'_c(γ)` iff `Λ < 4^{1/ε}`; (3) for large `m`; the derivative; `R'_c(0)` decreasing with limit `ε*_5` | `Corollary_7_3_gamma_pos`, `_boxes`, `_queries`, `_tile_fit`, `_eps_iff`, `_range`, `_derivative`, `_limit` | proved |
| Theorem 7.4: the choice of `c` and `θ` | `Theorem_7_4_parameters` | proved |
| Corollary 9.1(a), (b): setting up; `γ`, `q`, `Λ` with their digits; the thresholds `m ≥ 72`, `m ≥ 131`; the encodings, boxes and queries; the conclusion | `Corollary_9_1_setting_up`, `Corollary_9_1_a_exponents`, `_a_Lambda`, `_a_threshold`, `_a_encodings`, `_a_boxes`, `_a_queries`, and the same for `b`, `Corollary_9_1_conclusion` | proved |
| Corollary 16.1(a)–(d), the remark after it, Remark 16.2 (arithmetic), the preprint's exponents (Section 1.3), the tables of Sections 13.7 and 15.7, the crossing points `ln n ≈ 4.6·10^5`, `5.1·10^5`, `2 - ε*_5 = 1.8277…` | `Corollary_16_1_a_constant`, `_a_steps`, `_b_exponents`, `_cd_exponents`, `Sec1_preprint_exponents`, `Sec13_7_table`, `Sec15_7_table`, `Sec13_7_crossing`, `Sec10_numbers` | proved |
| Lemma 3.1: the identity `∑ φ_λ ψ_λ χ_λ = G + E` and the two forms of `E` | `Lemma_3_1` | proved (`ring`) |
| Section 3: `γ(s,t,z)` is the coefficient of `s t z` in `G + E`; Coppersmith's construction as printed in [Cop82, p. 467], with its `x³P` written out | `Sec3_gamma_coeff`, `Sec3_coppersmith` | proved |
| Section 3: Lemma 3.1's forms are Coppersmith's five terms at `x = 1`, in the order `P₁₁, P₂₁, P₁₂, P₂₂, P₀`, after the renaming | `Sec3_coppersmith_terms` | proved (`ring`) |
| Remark 5.2: the weights (monomials of `G` weight 2 with coefficient 1, of `E` weight 3 or 4) | `Remark_5_2_weights` | proved (`decide`) |
| Remark 5.2: the string weights in run `s` (left `2m+s`, right `2m-s`, outputs `4(L-m)`) and the forcing of weight 2 at every level | `Remark_5_2_strings` | proved |
| Section 4: `T ↦ Γ[T]` and `S ↦ Δ[S]` are bijections on good sets | `Sec4_bijections` | proved |
| Lemma 4.1: maps with at least `μ_m μ_{L-m} binom(L,m) ≥ μ_∞² binom(L,m)` good sets exist | `Lemma_4_1` | proved (existence, by averaging; the deterministic construction: next row) |
| Lemma 4.1, the deterministic construction by conditional expectations: the conditional probability `μ_{m-r}` (or `0`) with `r` fixed columns in `Q`; the conditional expectation is the sum over the next column; a greedy map exists and has at least `μ_k |𝒮|` invertible sets; `Γ` then `Δ` greedy give at least `μ_m μ_{L-m} binom(L, m)` good sets | `Lemma_4_1_condprob`, `Lemma_4_1_mean`, `Lemma_4_1_greedy`, `Lemma_4_1_derand` | proved (the operation count is not formalized: running time) |
| [ZT, Lemma 8] on the `2L` levels with the per-level identity | `Lemma_8_squared` | proved |
| Theorem 5.1: the `2m+1` runs compute `X_{Q(w')} Y_{Q(w'')}` at the stated position; the bijection onto the `N₀²` entries | `Theorem_5_1`, `Theorem_5_1_bijection` | proved, for every family of good sets and all matrices `X_Q`, `Y_Q` |
| The example after Theorem 5.1 (`L = 3`, `m = 1`) | `Sec5_example` | proved (`decide`) |
| Lemma 6.1(a), (b), (c) | `Lemma_6_1_a`, `Lemma_6_1_b_count`, `Lemma_6_1_b_bound`, `Lemma_6_1_c` | proved |
| Lemma 7.1(a): [ZT, Lemmas 27, 28] on the `2L` levels (four terms `P_ij`): the leaves of order at least `t` of an output's cube are those of its boxes, each in exactly one; the entry is the sum of the `∑_{d<t} α'_d` low products and the values of the `α'_t` boxes; the boxes satisfy (iii); the link with Theorem 5.1's `∑_s Mult` | `Lemma_7_1_a`, `Lemma_7_1_a_link` | proved (ported from `3sum-apsp/ThreeSumApsp/Sec4`) |
| Lemma 7.1(b): at most `(2m+1) ∑_{d=t}^{2m} β'_d` boxes; the dynamic program stays in the boxes, each value the sum of five | `Lemma_7_1_b_count`, `Lemma_7_1_b_dp` | proved |
| Theorem 7.2: the boxes per tile, the tiles and bands after padding, the cost of the re-indexing maps and `L ≤ log₂ N`, the word size `25^L ≤ N^{2.91}` and `12^L`; Section 5: the encoding sums `O(15^L)`, `O(25^L)` | `Theorem_7_2_boxes`, `_tiles`, `_hash_cost`, `Sec7_word_size`, `Sec5_encodings` | proved |
| [ZT, Lemma 7] on the `2L` levels with the identity of each level: the recursion `Full` (first half with `φ`, `ψ`, second half exchanged) multiplies `Φ_τ(a)` by `Ψ_τ(b)` at every leaf and returns `Mult(a, b)`; the encodings of [ZT, Section 2.4.1] are `Φ_τ(a)`, `Ψ_τ(b)` | `Lemma_7_squared` | proved (ported from `3sum-apsp/ThreeSumApsp/Sec2/Lemma7_8.lean`) |
| [ZT, Lemma 10] (the pruned recursion of [ZT, Section 2.4.2]), for any identity: called on `U` it returns at each string of `U` the sum of the leaf numbers over the contributing leaves (`0` elsewhere), visits exactly `Leaves(U)`, and passes sets of total size at most `(L+1)|Leaves(U)|`; on the `2L` levels of Section 6 with `Π(τ)` at a leaf (values `∑_s Mult(a_s, b_s)`, visits `Leaves(U)`, total size `≤ (2L+1)|Leaves(U)|`); for one run of the tiled product of Theorem A.14 (visits exactly the leaves of `Leaves(W)` of that run) | `Lemma_10_generic`, `Lemma_10_squared`, `FP_Lemma_10` | proved (ported from `3sum-apsp/ThreeSumApsp/Sec2/Lemma10.lean`); hypotheses not in [ZT]: `0 < L ∨ U ≠ ∅` for the visited leaves, and for the total size an injective choice of a contributing term per output letter (`P_ij` for `z_ij`, `P₀` for `z₀` in Part I); not used for the generic identity of A.9, which uses only the visited leaves |
| Theorem 7.2, correctness of the query: with the tiling (bands of `K_g` blocks of `N₀` rows, padding by zero rows), any labelling of the block rows and columns and of the inner dimension, the output string located by inverting `Δ` at `[L] ∖ Q` (change (5)), the encodings and the box values, "any single entry `(XY)[I, J]` can be computed": the query returns `(XY)[I, J]` for all integer matrices; the labellings exist | `Theorem_7_2_query`, `Theorem_7_2_labels` | proved |
| Lemma 12.1 | `Lemma_12_1` | proved from [RS62, Corollary 1] (`Assumptions.RosserSchoenfeld`) |
| Lemma 12.2 (averaging) | `Lemma_12_2` | proved |
| The stages of Sections 13 and 15 in the abstract: greedy halving (Lemmas 13.9, 15.7), one stage (Lemma 13.9), correctness and survivors (Lemmas 13.10, 15.9), certification (Lemma 15.10), halving of all incidences (Lemma 15.11), correctness of the all-edges algorithm (Lemma 15.12) | `Lemma_13_9_greedy`, `Lemma_13_9_stage`, `Lemma_13_10_abstract`, `Lemma_15_10`, `Lemma_15_11`, `Lemma_15_12_abstract` | proved; every choice of a minimising prime ("ties arbitrarily") is covered |
| Lemma 13.10 and Lemma 13.9 for the probes of 3SUM | `Lemma_13_10`, `Lemma_13_9_threeSum` | proved, for every partition and set of triples with the covering property of [FKP24, Lemma 3.3] |
| Lemma 13.7 (the counts), Lemma 13.5 (variants a, b, c, with the count `24ℓ²`), Lemma 13.6 (binary splitting) | `Lemma_13_7`, `Lemma_13_5_ab`, `Lemma_13_5_c`, `Lemma_13_6` | proved |
| Section 13.3, equation (5) and `ln(2U) ≤ (ν+1) ln n`; Lemma 13.8 (arithmetic); equation (6); Corollary 13.3 (the `exp(O(√(ln n ln ln n)))` computation); Corollary 13.4 (arithmetic) | `Eq_13_5`, `Sec13_log_bounds`, `Lemma_13_8_arith`, `Eq_13_6`, `Corollary_13_3_arith`, `Corollary_13_4_arith` | proved (side conditions "for large `n`" are hypotheses) |
| Lemmas 15.5, 15.8, 15.9, 15.11, 15.12 for the incidences of Exact Triangle; the bound `ℓ` of Section 15.4; Lemma 15.6 (arithmetic) | `Lemma_15_5`, `Lemma_15_8`, `Lemma_15_9`, `Lemma_15_11_ET`, `Lemma_15_12`, `Sec15_ell`, `Lemma_15_6_arith` | proved |
| Lemma 15.13 (the test and the binary search), Link 3, the encoding of `∞`, APSP by repeated squaring and the bound on the entries | `Lemma_15_13_test`, `Lemma_15_13_search`, `Sec15_link3`, `Sec15_apsp_encoding`, `Sec15_apsp_squaring`, `Sec15_apsp_entries` | proved (the repeated squaring is copied from `3sum-apsp`, where it proves [ZT, Theorem 21(b)]'s step) |
| Equations (7), (8), Corollary 15.3 (computation) | `Eq_15_7`, `Eq_15_8`, `Corollary_15_3_arith` | proved |
| Sections 13.3 and 15.1, the side conditions "for `n ≥ n₀` large enough" (`σ ≥ 2`, `c₁n/σ ≥ 1`, `P ≥ 1024`, `r ≤ P/(4 ln P)`, `(2σ²)^{1/r} ≥ 2`, resp. `(ξσ)^{1/r} ≥ 2`, `2nΛ_E ≤ n²`, `σ ≤ n`), uniformly for `1 ≤ U ≤ n^ν` and `1 ≤ r ≤ r(n) = ⌈√(ln n/ln ln n)⌉` (so for constant `r` and for Corollaries 13.3, 15.3); `r(n) → ∞`; the split of `C` into pieces | `Sec13_side_conditions`, `Sec15_side_conditions`, `Sec13_rOf_unbounded`, `Sec15_pieces` | proved |
| Theorems 13.2, 15.1, 15.2 and Corollaries 13.3, 15.3, correctness with the paper's parameters: for `n ≥ n₀`, greedy moduli exist, every candidate modulus has `2 ≤ mp < (2P)^r ≤ Λσ²` (resp. `Λ_E σ`), every greedy choice halves (Lemmas 13.9, 15.8, 15.11), and the algorithm's answer is correct (Lemmas 13.10, 15.9, 15.12); for 3SUM also with the partition of [FKP24, Lemma 3.3] | `Theorem_13_2_correct`, `Theorem_13_2_FKP`, `Theorem_15_1_correct`, `Theorem_15_2_correct` | proved from [RS62] (and [FKP24, Lemma 3.3] for `Theorem_13_2_FKP`) |
| Link 2 with [CVX23, Lemma 9.2]: an edge lies in a negative triangle iff it lies in a triangle of target weight in one of the `O(log n)` instances | `Sec15_link2_detection` | proved from [CVX23, Lemma 9.2] (`Assumptions.CVX23_Lemma_9_2`, its counting identity) |
| Section 15.6, APSP: one product with `∞` encoded as `Ω = 3B + 1` and the entries above `B` reset to `Ω` is the encoding of the `(min,+)`-product | `Sec15_apsp_step` | proved |
| Link 2: "the detection version suffices" (a sum of counts is positive iff one count is) | `Sec15_link2` | proved; [CVX23, Lemma 9.2] itself is not stated (it enters no proof here) |
| Theorem 14.1 (deterministic KPP): the parameter bounds of the proof (`Λ_S ≤ Λ`, `P`, `u ≤ Λ n^{2-2α}`, `N ≤ 10c₁√Λ n`, `s ≤ n^{1-α}`, `q_S ≤ 8c₁²c₂ n^{1+α}`, `L ≤ 3 log₂ n`, `|𝒫₀| ≤ 2^L`) and the rescaling `n' = Λ^{1/(2-2α)} n` of the consequence | `Theorem_14_1_params`, `Theorem_14_1_consequence` | proved (side conditions "for large `n`" are hypotheses) |
| Corollary 10.1: the substitution `D = n^τ` into the exponents, and `t₂ ≥ D^c` for `τ₁ ≤ τ₂/c` | `Corollary_10_1_arith` | proved |
| Proposition 10.3 (called Remark 10.3 in earlier drafts; Conjecture 5.12 on a larger region): the index identities for Boolean `U`, `N`, `V` and lists `I`, `J` with repetitions (the Boolean entry `(U N_{I,J} V)_{i,j}` is true iff `(U N_{I,[n]})[i, J_b] > 0` and `V_{b,j}` for some `b`, iff `U_{i,a}` and `(N_{I,J} V)[a, j] > 0` for some `a`; column `b` of `U N_{I,J}` is column `J_b` of `U N_{I,[n]}`; blocks of columns of `V`), also over `ℕ` with arbitrary entries; the exponent arithmetic of both regions for general `c`, `γ > 0`, `q < 1` and with `18`, `0.092`, `0.403` (thresholds `n ≥ t₁^18`, `t₁ ≥ t₂^18`, Phase 2, 3, 4 exponents below the obvious ones); the general thresholds (`ε = τ₁`, resp. `ε = τ₂/τ₁ < ε*_5`, `D ≥ 2` for large `n`, `q = 1/2`); the regions (`τ₁ < ε*_5 τ₂` inside `τ₁ < ε*_5` for `τ₂ ≤ 1`; `τ₁ + τ₂ ≥ 1.4` in neither for `0 < τ₁ ≤ 1`, `τ₂ ≤ 1`) | `Remark_10_3_index`, `Remark_10_3_index_nat`, `Remark_10_3_general`, `Remark_10_3_arith`, `Remark_10_3_eps`, `Remark_10_3_regions` | index identities and exponent arithmetic proved; the data structure (Corollaries 7.3, 9.1, Theorem 7.4), the computational model of [BNS19] and the running times are not formalized (as for Corollary 10.1, the data structure enters only through its parameters `c`, `γ`, `q`) |
| Section 8 of the paper, paragraph "The limit is Coppersmith's exponent" (Remark 17.1 before 12 October 2026): `D = 4^m = 2^{2L/5} = 5^{αL} ≥ N'^α` at `L = 5m` | `Remark_17_1_arith` | proved |

### Appendix A

| Item of the paper | Lean name | Status |
|---|---|---|
| Lemma A.1 (private leaves): `R₀^m R₁^{L-m}` leaves per selected output contribute to it alone; the consequence `R₀² R₁^{2(c-1)} < q₀` | `Lemma_A_1`, `Lemma_A_1_consequence` | proved |
| Appendix A.1: the private-leaf condition excludes `R₁ ≥ 2` for `q₀ ≤ 4^{c-1}` when `R₀ ≥ 1`, and gives `R₀ < √q₀` for `R₁ ≥ 1` | `Sec_A_1_private_consequences` | proved |
| Proposition A.2 (exact identities, harmless error): `q₀ ≤ R - k - n` for `k, n ≥ 2`, over any field | `Prop_A_2` | proved |
| Lemma A.3 (border substitution with a solvable symmetry group, from [LM17] and Borel's fixed point theorem) | — | not formalized (border rank, algebraic groups); enters Propositions A.4, A.5 as the substitution-step hypothesis |
| Propositions A.4, A.5, Remarks A.6, A.7: the inductions and the consequences (`q₀ ≤ R-k-n+1`; effective inner length `≤ R-k-n+2`; the conditional `≤ R-k-n+1`; `R(S(3,3,5)) ≥ 11`, `R(S(3,2,3)) ≥ 8` and the exclusions for `(2,2), (2,3), (3,3)`) | `Prop_A_4`, `Prop_A_5`, `Remark_A_6`, `Remark_A_7` | proved from hypotheses on abstract border-rank functions: the flattening bounds (independent slices), the substitution step (Lemma A.3 with the paper's fixed lines and quotients), and for Remark A.7 the Koszul bounds (computer calculations) and monotonicity under `S(k,n,q)/p_q` |
| Propositions A.4, A.5, the finite linear algebra of the substitution step: the group `𝓑` (upper-triangular changes, and for `S` the scalings `c ↦ vc`, `y₁ ↦ v⁻¹y₁`, `z_{i1} ↦ vz_{i1}`) fixes `G(k,n,q₀)` and `S(k,n,q₀')`; its fixed lines in the left space are `⟨x₁⟩`, `⟨p₁⟩` (and `⟨c⟩`), over any field of characteristic 0; the quotients are `G(k-1,n,q₀)`, `G(k,n,q₀-1)`, `S(k-1,n,q₀')`, `S(k,n,q₀'-1)`, `G(k,n,q₀')` padded by zero slices | `Prop_A_4_fixes`, `Prop_A_4_lines`, `Prop_A_4_quotients`, `Prop_A_5_linalg` | proved |
| Propositions A.4, A.5 composed: from Lemma A.3, "`𝓑` is connected and solvable", the invariance of border rank under padding and the flattening bounds (hypotheses on an abstract border-rank function), the bounds of the propositions; the substitution step is derived | `Prop_A_4_composed`, `Prop_A_5_composed` | proved from these hypotheses (Lemma A.3 is not formalized) |
| Lemma A.8 (A)–(C): spans, independence and cancellation for a correct single output | `Lemma_A_8` | proved |
| Theorem A.9 (a) no two shared right, and no two shared left, variables; (b) with disjoint blocks per entry, no shared left and right variable | `Theorem_A_9` | proved, for a run modelled by `SharedRun` (the output `∑_ι a[v_ι] b[w_ι]` is the definition); hypothesis (b) in the weaker form "overlapping blocks of one entry come from the same product" |
| Lemma A.10 (normal form of the inner form): the decomposition with `s_A`, `s_B` letters in `X`, `Y`; the bases of the two spaces | `Lemma_A_10`, `Lemma_A_10_basis` | proved, for arbitrary subspaces `X`, `Y` and any field |
| Proposition A.11 (Vrana): the border identity `τ₁+…+τ₅ = ε³ M_Λ + O(ε⁴)`, the cyclic symmetry, and the leaf bound (in fact `|W| (3/2)^m ≥ |W| 2^{m/2-1}`, so `≥ N²/2`) | `Prop_A_11_identity`, `Prop_A_11_symmetry`, `Prop_A_11` | proved (`ring` for the identity) |

### Appendix A.9: thin full products

| Item of the paper | Lean name | Status |
|---|---|---|
| Lemma A.12: the average of `|Leaves(W)|` over the sets `W` of exactly `w` outputs lies between `(1-1/e)V` and `V`, and some `W` with `|W| = w` has `|Leaves(W)| ≥ (1-1/e)V` | `FP_L_average`, `FP_L_exists` (with the auxiliary `FP_L_bernoulli`, `FP_L_uniform`, `FP_choose_ratio`, `FP_one_sub_pow`, below) | proved |
| Lemma A.13: `F` attains its minimum `F*` on `[0,1]` and `(1/L) ln V_L → F*`; quantitatively `V_L ≤ e^{L F(t)}` and `ln V_L ≥ L F(t₀) - C√L - ln 2` | `FP_Lemma_A_13`, `FP_Lemma_A_13_bounds` | proved, by a different proof (a tilted product measure and Chebyshev's inequality instead of the method of types) |
| Theorem A.14 for the preprint's run: the tiling, `w = ⌈N²/√D⌉ ≤ N²` and `ρ ≥ b^{-L/2}`, `V ≥ (N²/n^L) V_L`, and under `Γ ≥ 0` some `W` with `|W| = w` and `|Leaves(W)| ≥ (1-1/e) N² e^{-δ_L L}`, `δ_L → 0` | `FP_Thm_A_14_tiling`, `FP_Thm_A_14_rho`, `FP_Thm_A_14_V`, `FP_Thm_A_14` | proved for the preprint's run (the preprint's Lemma 10, `Leaves(W)` = the visited leaves, is `FP_Lemma_10`); the squared-run case is not formalized |
| Theorem A.14, last sentence, for `b ≥ 2` (for every `γ > 0` some `W` has `|Leaves(W)| > N²/D^γ`); the statement is false for `b = 1`, where `D = 1` | `FP_Thm_A_14_no_saving` | proved, for the preprint's run |
| Lemma A.15 (forest bound, any field): (a) at least `b|F|` terms meet every forest `F`; (b) `∑_l min(|S_l|, f) ≥ bν`, `f = ν/(o₁+o₂-1)`; the double stars are spanning trees, each output in `o₁+o₂-1` of them | `FP_Lemma_4` (a), `FP_Lemma_4_avg` (b), `FP_star` | proved (averaged over the double stars, the paper's translates of "first row + first column") |
| Lemma A.16 (rank bound, any field): at least `o₁o₂ + (b-1) max(o₁, o₂)` terms with `w_l ≠ 0`, for `o₁, b, o₂ ≥ 1` | `FP_Lemma_6` | proved |
| Proposition A.17 (criterion, cases (i)–(iii), any `o₁, o₂ ≥ 2`, `r = 1 + (b-1)/κ`) and its last sentence | `FP_Prop_A_17`, `FP_Prop_A_17_kappa` | proved |
| Corollary A.18: every decomposition of the 81 thin shapes among the rotations of the 145, either orientation, any field, gives no saving in the leaf count of the preprint's run; for the squared run, `∑_{l,l'} (S_l S_{l'})^t = (∑ S^t)²` (the test is unchanged) | `FP_Cor_A_18` (with `FP_shapes_145`, `FP_145_thin`), `FP_squared` | proved for the preprint's run; that the 81 shapes are the thin rotations of the 145 published decompositions is an extraction from their data files, not checked in Lean |

### Auxiliary results on full products (not items of the paper)

These were proved on the way to Appendix A.9. Their labels (Lemma U, Lemma 1, Theorem 2, Lemmas 3 and 5, Theorem 2') are those of the working notes in which they were first written; they are not items of the paper.

| Statement | Lean name | Status |
|---|---|---|
| Lemma U: for any identity, any partition of the leaves into classes and every wanted set `W`, `|Leaves(W)| ≤ ∑_x min(|W| α_x, β_x)` | `FP_U` | proved |
| Lemmas L1–L3: the Bernoulli expectation `∑_τ (1-(1-p)^{s(τ)})`; the count over uniform `w`-sets; `binom(n-s,w) ≤ binom(n,w)(1-w/n)^s`; `(1-1/e) min(1,ps) ≤ 1-(1-p)^s ≤ min(1,ps)` (the steps of Lemma A.12) | `FP_L_bernoulli`, `FP_L_uniform`, `FP_choose_ratio`, `FP_one_sub_pow` | proved |
| The `L`-th power: `s(τ) = ∏_ℓ |S(τ_ℓ)|` and Lemma A.12 for it | `FP_power_lower` | proved |
| Lemma 1 (capped covering, any field): the restriction step (rank of the `y`-flattening of `⟨o₁,b,o₂⟩|_P` ≤ number of terms whose output support meets `P`), the transversal step (rank `b o₂`), `∑_l min(|S_l|, k) ≥ b n`; and `R ≥ n` (terms with `w_l ≠ 0`) | `FP_restrict_rank`, `FP_transversal_rank`, `FP_Lemma_1`, `FP_rank_ge_n` | proved |
| Theorem 2: the inequality for families `S_l ≥ 1` (`k ≤ b` or `k^{2(b-1)} ≥ b^{k-1}`), and composed with Lemma 1 for every decomposition over any field | `FP_Theorem_2_ineq`, `FP_Theorem_2` | proved |
| Lemma 3 (tight outputs, any field): every coverer of an output with `r_e = b` is local to it (`u_l ≠ 0` in `A_i`, `v_l ≠ 0` in `Y_c`); a term is local to at most one output; `#{l : w_l ≠ 0} ≥ b · #tight`; if every output is tight, every `|S_l| ≤ 1` | `FP_Lemma_3`, `FP_local_unique`, `FP_Lemma_3_count`, `FP_Lemma_3_all_tight` | proved |
| Lemma 5 (a)–(c) (nonlocal coverers, any field): `A_i ⊆ U_e`, `Y_c ⊆ V_e`, `dim U_e + dim V_e ≤ r_e + b`, `r_e ≥ b+1` if a coverer is not local; for `W` with one output per column `G₀ ⊆ G_W`, `dim G₀ = b|W|`, `dim G_W ≤ #terms meeting W`, `dim G_W ≥ b|W| + #isolated nonlocal`; `∑ min(S_l,o₁) ≥ bn + |E_A|`, `∑ min(S_l,o₂) ≥ bn + |E_B|`; `|D| ≥ #{e : λ_e < b}`, `∑ λ_e ≤ R` | `FP_Lemma_5a`, `FP_Lemma_5b`, `FP_Lemma_5b_sum`, `FP_Lemma_5c` | proved |
| Theorem 2': the two-point inequality for families; composed with Lemmas A.15 and A.16 for every decomposition (per `t`); the clean sufficient condition `m ≤ b` or `m^{2(b-1)} ≥ b^{m-1}`; its integer form for `m* = n/d` | `FP_Theorem_2p_ineq`, `FP_Theorem_2p`, `FP_Theorem_2p_clean`, `FP_Theorem_2p_nat` | proved |
| The clean condition covers `⟨k,b,k⟩` for `b < k ≤ 12, 17, 22, 27, 32, 37` (`b = 2..7`) and fails at the next `k`; `⟨7,2,7⟩..⟨12,2,12⟩, ⟨10,3,10⟩, ⟨12,4,12⟩` excluded for every decomposition; crude bound `ln ∑ S^t - (t/2) ln b - ln n ≥ -(ln b)/2` (so `γ ≤ 1/2`) | `FP_clean_squares`, `FP_open_shapes`, `FP_value_crude` | proved (`decide +kernel` for the integer checks) |

## Not formalized, and why

Section 22.2 of the paper refers to this list. Every item of Parts I and II and of Appendix A that
is not in the tables above, or is there only in part, is one of the following.

* Running times on a machine: Theorem 7.2's assembly of the running time, Theorem 7.4,
  Corollaries 7.3, 9.1, 10.1, Proposition 10.3, Theorems 13.2, 14.1, 15.1, 15.2 and Corollaries
  13.3, 13.4, 15.3, 15.4 as running-time statements, Lemmas 13.8 and 15.6 as costs, and the
  computational model of [BNS19] in Section 10; their counts, their correctness and the
  arithmetic of their bounds are proved (tables above).
* Of [ZT, Lemma 10] (proved: `Lemma_10_generic`, `Lemma_10_squared`, `FP_Lemma_10`), the cost of
  a call (`O(L|S|)` operations, [ZT, Section 2.4.4]) is a running time and is not formalized.
* Lemma 4.1's operation count (running time); the method of conditional expectations itself is
  proved (`Lemma_4_1_derand`).
* The statements of the preprint [ZT] and of the other cited works are taken as given: Lemma 2.2
  (`Hyp(1/18, 0.063)` from [ZT, Corollary 26]) and the hypothesis `Hyp(ε, γ)` itself, which is a
  running-time statement; [FKP24, Lemma 3.3], [RS62, Corollary 1] and [CVX23, Lemma 9.2], which
  enter as hypotheses (`Assumptions.lean`); and, for Corollary 16.1(a) and (b), the re-run of
  [ZT, Theorems 17, 19, 21] with the new constants, of which only the arithmetic is checked.
* Theorem 14.1 (the deterministic version of [KPP16]): only the parameter arithmetic of its proof
  is formalized (`Theorem_14_1_params`, `Theorem_14_1_consequence`); the encoding of the 3SUM
  instances as counting offline Set Disjointness instances is not, and the lower bound
  `η ≤ min(α, 1-α)` is an adversary argument about algorithms (its arithmetic use,
  `n^{2-α}, n^{1+α} ≤ n^{2-η}`, is proved).
* Corollary 15.4: its links are proved one by one (Lemma 15.13, Link 2 from [CVX23, Lemma 9.2],
  Link 3, the encoding of `∞`, one encoded product, the repeated squaring and the bound on the
  entries); the composition of the encoded products over the `⌈log₂ n⌉` squarings into one
  statement is not written. [CVX23, Lemma 9.2] as a reduction (an algorithm with a running time) is
  not formalized; its counting identity is `Assumptions.CVX23_Lemma_9_2`, and the deduction that
  detection suffices is proved from it.
* Border rank: Proposition 3.2 (border rank of G(2,2,2) > 5, computer-assisted by weak border
  apolarity [BB21]; the computation is the ancillary script `border_apolarity.py`), and Lemma A.3
  (border substitution with a solvable group), that the groups of the proofs are connected and
  solvable, the flattening bounds and the invariance of border rank under padding: border rank
  and Borel's fixed point theorem are not available in Mathlib in a usable form. In
  Propositions A.4 and A.5 they are hypotheses of `Prop_A_4_composed`, `Prop_A_5_composed` (the
  fixed lines and the quotients are proved).
* Theorem A.9 is proved for a run modelled by `SharedRun`; the derivation of its output formula
  from `T^{⊗L}` is not formalized.
* Appendix A.9: the squared-run case of Theorem A.14 (and so Corollary A.18 for the squared run,
  beyond the identity `FP_squared`), the numerical paragraphs, and the extraction of the 81 thin
  shapes from the data files of the 145 decompositions.
* Computer-assisted and numerical results: rate values, Table 4, the scores and exclusions of
  Section 11 and Appendix A.1, the Koszul flattening ranks of Remarks A.6 and A.7 (hypotheses of
  `Remark_A_6`, `Remark_A_7`), the 145 decompositions, the support patterns of Vrana's tensor, and
  the numerical probe after Proposition 3.2. These are the ancillary scripts of the paper.

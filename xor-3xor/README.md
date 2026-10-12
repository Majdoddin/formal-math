# A Lean check of the mathematics of Section 18 (3XOR) of "Thin matrix products up to D ≤ N^0.172"

This folder is a Lean 4 project (Lean v4.33.1, Mathlib v4.33.1; library and package name
`XorLean`) that proves the mathematics of Section 18 of the paper *Thin matrix products up to
D ≤ N^0.172 and lossless reductions for 3SUM, Exact Triangle and APSP, with 3SUM over abelian
groups and a dichotomy for coordinatewise problems* by Ruhollah Majdoddin (12 October 2026), and
the mathematics of the route for 3XOR that the preprint's Remark 23 sketches (the entries marked †
in Table 1 of the paper). Item numbers below are those of the paper; [ZT] is the preprint of Alman
and Vassilevska Williams, arXiv:2610.06783v1.

The aim is the correctness and the counts of the reductions. No running time is formalized: the
hypothesis `Hyp(ε, γ)` of the paper is a statement about running times, so it enters no Lean
statement. The algorithm that the reductions call is represented by the exact answers it must
return (`LopInst.count`, the number of common neighbours, for the counting version, and
`LopInst.Accepts` for the detection version).

## Build and guarantee

    lake build

builds the root `XorLean.lean`, which imports every file except `Smoke.lean` (a set-up check).
No file contains `sorry`, `admit`, `axiom` or `native_decide`, and `#print axioms` of the main
theorems shows only `propext`, `Classical.choice` and `Quot.sound`.

## Names and numbering in the Lean files

The Lean files were written against two working write-ups that are not published; their docstrings
keep the labels of those write-ups. This table gives the paper's item for each label.

| Label in the Lean files | Item of the paper |
|---|---|
| "the improved write-up", Theorem II, §4.2–§4.4 | Theorem 18.2 (counting algorithm), Section 18.2 (parameters, groups, blocks, probes, the instance `I(H, 𝒫)`) |
| Theorem I′, §3.2 | Theorem 18.3 (one detection call), Section 18.4 |
| Theorem III, §5 | Theorem 18.4 (Exact-XOR-Triangle and its all-edges version), Section 18.5 |
| Lemma II.1, II.2, II.3 | Lemmas 18.11, 18.12, 18.13 |
| §4.5–§4.7, Lemma II.4, Lemma II.5 | Section 18.3 (the stages), Lemmas 18.14, 18.15 |
| Lemma III.1 | the count of the calls in Section 18.5 (at most `2^l + 2√(σ2^l)` calls per piece) |
| Lemma III.2, Lemma III.3 | Lemma 18.16 (i)–(iii), and (iv) |
| Lemma III.4 | the correctness of the all-edges algorithm (the paragraph after Lemma 18.16) |
| §1, exponents | Corollary 18.5 and Table 1 |
| Theorem I (a)–(c), §3.1 | the remark's route (not written out in the paper; Table 1, entries †) |
| "the note", Definition 2 | Definition 18.6 (biased multiset) |
| the note's Lemmas 4, 5, 6, 7 | Lemmas 18.7, 18.8, 18.9, 18.10 |
| the note's Theorem 8 | the analogue over F₂ of [ZT, Theorem 17]: Exact-XOR-Triangle to Lop |
| the note's Lemma 10, Corollary 11 | the analogue over F₂ of [ZT, Theorem 21(a)]: Convolution-3XOR to Exact-XOR-Triangle |
| the note's Lemmas 12, 13, 14 | the analogue over F₂ of the reduction of Chan and He [CH20]: 3XOR to Convolution-3XOR (hash, recursion tree, correctness) |
| T1–T7 in file headers | the targets of the formalisation plan of the note: T1, T2 = Lemmas 4, 5; T4 = Lemma 7; T5 = Theorem 8; T6 = Lemma 10 and Corollary 11; T7 = Lemmas 12–14 |
| X1–X3 | conventions: vectors are `Fin ℓ → ZMod 2` (`Vec ℓ`); biased sets are multisets; rows are a list, newest first, so the text's `(H, u)` is `u :: H` |

## What is formalized

### Section 18 (Theorems 18.2, 18.3, 18.4)

| Item of the paper | Lean names (namespace `Xor` or `Xor.Improved`) | File |
|---|---|---|
| Lemma 18.7 (one row) | `select_average`, `select_exists` | `Basic.lean` |
| Lemma 18.8 (rows chosen one at a time) | `greedy_bound`, `greedy_bound_exp`, `greedyRows`, `isGreedy_greedyRows` | `Basic.lean` |
| Lemma 18.9 (explicit biased set, [AGHP92]) | a hypothesis (`IsBiased`) here; the construction is proved in `../3sum-apsp/ThreeSumApsp/Remark23/Biased.lean` (`remark_23_lemma_6`), which these files do not import | — |
| Lemma 18.10 (Walsh–Hadamard count) | `two_pow_mul_Zc`, `Zc_eq_sum_cls`; `sum_chi_eq`, `count_formula` | `ImprovedProbes.lean`, `Count.lean` |
| Lemma 18.11 (probes) | `solution_in_probe`, `exists_sol_iff_probe`, `probes_card_le` | `ImprovedProbes.lean` |
| Lemma 18.12 (the counts) | `matXY_pos` | `ImprovedProbes.lean` |
| Lemma 18.13 (shape of one evaluation) | binary splitting `matmul_bits`, `bitInst_count`, `cnt_eq_oracle`; on the built calls `evalCalls_spec`, `xor_direct_count_eval_params`; the cost as an inequality `eval_cost`, `parts_le` | `ImprovedProbes.lean`, `ImprovedCallsProbes.lean`, `ImprovedArith.lean` |
| Lemma 18.14 (halving) | `Cands.halving` | `ImprovedStages.lean` |
| Lemma 18.15 (correctness) | `Cands.run_iff`, `xor_direct_count_correct` | `ImprovedStages.lean`, `ImprovedProbes.lean` |
| Theorem 18.2, correctness | `xor_direct_count_correct`, and with the rows chosen greedily on the called algorithm's answers `xor_direct_count_correct_oracle` | `ImprovedProbes.lean`, `ImprovedCallsProbes.lean` |
| Theorem 18.3, correctness, the one call and the failed scans | `xor_direct_detection_correct`, `xor_direct_detection_correct_num`, `xor_direct_detection_call`, `failed_scans_le`, `oneHash_bounds`, `F_probes_eq` | `ImprovedOneHash.lean`, `ImprovedCallsOneHash.lean` |
| Theorem 18.4 (a), (b), correctness | `exact_xor_triangle_full_detect`, `exact_xor_triangle_full_allEdges`, and on the answers of the calls `exact_xor_triangle_full_detect_oracle`, `exact_xor_triangle_full_allEdges_oracle` | `ImprovedTriangle.lean`, `ImprovedCallsTriangle.lean` |
| Lemma 18.16 (i)–(iv) | `Cands.certFalse_z`, `Cands.certTrue_z`, `Cands.uncert_fp`, `aeStep_halving`, `aeStep_halving_oracle` | `ImprovedTriangle.lean`, `ImprovedCallsTriangle.lean` |
| the calls of Section 18.5 | `lemmaIII1_calls`, `lemmaIII1_calls_params`, `triangle_pieces_exist`, `J_count`, `J_mid_card` | `ImprovedCallsTriangle.lean`, `ImprovedTriangle.lean` |
| the parameter inequalities | `staged_params`, `staged_params'`, `oneHash_params`, `triangle_params`, `ceil_logb_spec` | `ImprovedArith.lean` |
| Corollary 18.5 (exponents) | `exponents_cor91b`, `exponents_cor16`, `exponents_absorbed` (the polylogarithmic factors absorbed into `1.99451`, `1.99726`, `1.99651`, `1.99826`, `2.99451`, as `IsBigO`) | `ImprovedArith.lean` |

Every call that the three algorithms make is proved legal on the instance that is actually built:
`LopInst.number` renumbers an instance into `Fin N` (unused vertices isolated, the padding), with
the same counts, answers and number of query pairs (`number_count`, `number_accepts`,
`number_W_card`), and the calls are instances of `Lop(N, D)` with `D ≤ N^ε` and at most `⌊N²/√D⌋`
query pairs (the bound of Lemma 18.13). The sums formed from the answers of the calls equal the
true sums (`oracleTotal_eq_total`), so the rows chosen from them are greedy rows of Lemma 18.8.

### The remark's route (Table 1, entries †)

| Item | Lean names (namespace `Xor`) | File |
|---|---|---|
| the analogue of [ZT, Theorem 17] (the note's Theorem 8): at most `4Ng` instances of `Lop(N, D)`, each with at most `⌊N²/√D⌋` query pairs, a zero triangle exists iff some instance accepts a pair whose piece holds one; the false positives `F(h) < 2eN³/√D` for the greedy rows; failed scans at most the false positives | `reduction_spec`, `false_positives_le`, `failedScans_card_le` | `Reduction.lean` |
| the analogue of [ZT, Theorem 21(a)] (the note's Lemma 10 and Corollary 11) | `conv_iff`, `convEquiv`, `emb_sum_eq_zero_iff`, `convHasSol_pad_iff` | `Conv.lean` |
| the analogue of [CH20] (the note's Lemmas 12–14) | `kOf_spec`, `hash_bound`, `card_nodeAt_le`, `count_le_of_inner`, `tree_card_le`, `solve_iff` | `Recursion.lean` |
| Theorem I (a): the parameter block composed with the analogue of [ZT, Theorem 17] | `partI_params`, `exact_xor_triangle_half_reduction` | `ImprovedArith.lean`, `ImprovedTriangle.lean` |
| the exponents `1.99863` (with Corollary 9.1(b)) and `1.999125`, printed `1.9992` (with [ZT, Corollary 26]) | `partI_exponents`, `partI_absorb`, `exponents_cor91b`, `exponents_cor16` | `ImprovedArith.lean` |

The explicit construction of the biased sets of [AGHP92], with its bias bound, and a second copy
of the remark's route, stated item by item, are in [`../3sum-apsp`](../3sum-apsp)
(`ThreeSumApsp/Remark23/`, and the section "Remark 23 (3XOR)" of `PaperStatements.lean`).

## What is not formalized

* Every running time: the hypothesis `Hyp(ε, γ)`, the cost of the calls (proved only as separate
  inequalities, `eval_cost`, `triangle_call_cost`, `triangle_pieces`, not composed with the
  correctness), the scans and listings, and the polylogarithmic factors. The counts of evaluations
  (`stage_evals_le`, `triangle_evals_le`) take the size of the biased set as a hypothesis.
* Lemma 18.9: the biased sets are a hypothesis (`IsBiased`), see above.
* Lemma 18.16 (iv) is stated for one stage; its chaining over the `L` stages, which only the cost
  uses, is not stated.
* The search version of Theorem 18.2 is stated for an abstract decision procedure (`findOne_spec`,
  `xor_direct_count_search`); its link with `xor_direct_count_correct` and the binary search for
  `x₂` are not stated.
* Of Corollary 18.5, the absorption of `(log n)^6` into `2.99651` (with [ZT, Corollary 26]) is not
  stated; the value `2.9965` is (`exponents_cor16`). For the remark's route, the absorption of
  `(log n)^{log₂ 27}` into `1.9992` is not stated here.
* Theorem I (b), (c) of the remark's route as running times, and the remarks and the comparison
  with the literature (Sections 18.6, 18.7).

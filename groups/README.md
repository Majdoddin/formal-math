# A Lean check of the mathematics of Sections 19–21 of "Thin matrix products up to D ≤ N^0.172"

This folder is a Lean 4 project (Lean v4.33.1, Mathlib v4.33.1; library and package name
`GroupLean`) that states and proves items of Sections 19–21 of the paper *Thin matrix products up
to D ≤ N^0.172 and lossless reductions for 3SUM, Exact Triangle and APSP, with 3SUM over abelian
groups and a dichotomy for coordinatewise problems* by Ruhollah Majdoddin (12 October 2026): 3SUM
over finite abelian groups (Section 19), the dichotomy for coordinatewise problems (Section 20)
and the triangle versions (Section 21). Item numbers below are those of the paper. The other
sections are formalised in [`../thin-matrix-products`](../thin-matrix-products) (Parts I and II,
Appendix A) and [`../xor-3xor`](../xor-3xor) (Section 18, the case `F₂^d`, from which several
files here are generalised).

The aim is the correctness and the counts of the reductions, and the classifications. No running
time is formalized. As for Section 18, the detection and counting algorithms that the reductions
call are represented by the exact answers they must return: a probe is flagged iff the support
instance has a common neighbour at its position (`OneHash.oneHashYes`), and a count is the number
of common neighbours.

## Build and guarantee

    lake build

builds the root `GroupLean.lean`, which imports every file. No file contains `sorry`, `admit`,
`axiom` or `native_decide`, and `#print axioms` of the main theorems below shows only `propext`,
`Classical.choice` and `Quot.sound` (some of them use fewer). The finite checks of Theorems 20.11
and 20.12 and of Proposition 20.14(c) are certificates (equation systems, gadgets, exhaustive
searches) verified by Lean's kernel with `decide +kernel`; the certificate tables were generated
by a script that is not part of this repository, and the kernel checks every entry, so the script
need not be trusted. `Functional3.lean` takes about five minutes (twenty kernel checks of 1000
maps each).

## Names and numbering in the Lean files

The Lean files were written against working notes whose labels the file headers and docstrings
partly keep. The paper's items for them are:

| Label in the Lean files | Item of the paper |
|---|---|
| Lemma 1, Lemma 2 (`Select.lean`) | Lemmas 19.2 (one row), 19.3 (rows chosen one at a time) |
| Lemma 3 (powering) | Lemma 19.4 |
| Theorem A (`OneHash.lean`, `FpBounds.lean`) | Theorem 19.8 (`F_p^d`, one detection call), with Lemmas 19.6 and 19.7 |
| Proposition C | Proposition 19.13 |
| Lemma G1, Theorem G, Case L, Case H, (F1), (F2) | Section 19.6: Lemmas 19.3 and 19.22 in abstract form, Theorem 19.17, Lemma 19.21, Lemma 19.24, Lemma 19.18 |
| Theorem D, Theorem E (`Boolean.lean`, `Functional3.lean`) | Theorems 20.11 and 20.12 (together Theorem H of the introduction) |
| Proposition F (`Latin.lean`) | Proposition 20.14 |
| §2, §3, §5, §6 | Sections 19.1–19.2, 19.3–19.4, 19.5, 19.6 |
| `g:thm:G`, `g:lem:partL`, … | the labels of the paper's source: Theorem 19.17, Lemma 19.21, … |

## What is formalized

All theorems are in the namespace `GroupLean` or one of its sub-namespaces (`OneHash`, `ExpP2`,
`CaseL`, `FpBounds`, `ExpP2Split`, `ExpP2Reduce`, `TheoremG`, `Fp`).

### Section 19: 3SUM over finite abelian groups

| Item of the paper | Lean names | File |
|---|---|---|
| Lemma 19.2 (one row) | `select_average`, `select_exists` | `Select.lean` |
| Lemma 19.3 (rows chosen one at a time) | `greedy_bound`, `greedy_bound_exp`, `greedy_bound_exp_drop`; abstract form `ExpP2.G1_step`, `ExpP2.G1_iterate` | `Select.lean`, `ExpP2.lean` |
| Lemma 19.4 (the powering construction over `F_p`) | `powSet_isValBiased`, `exists_valBiased` (the listing time is not formalized) | `Powering.lean` |
| Lemma 19.5, the identity over `ℂ` | `fourier_count`, `Fp.Zrows_fourier` | `Fourier.lean`, `FpProbes.lean` |
| Lemma 19.6 (probes and the instance) | `OneHash.triple_in_probe`, `solution_in_probe`, `exists_sol_iff_probe`, `probes_card_le`, `matXY_pos`, `flagged_iff`, `failed_scans_le`, `F_probes_eq` | `OneHash.lean` |
| Lemma 19.7, correctness | `OneHash.detection_correct` | `OneHash.lean` |
| Theorem 19.8, correctness and counts | `OneHash.detection_correct`; `FpBounds.theoremA_counts`, `theoremA_F`, `theoremA_probes`, `fp_prefix_bounds` | `OneHash.lean`, `FpBounds.lean` |
| Theorem 19.9, correctness and counts | `Fp.fp_count_correct`, `Fp.fp_count_correct_oracle` (rows greedy on the sums formed from the answers), `Fp.Cands.halving`, `Fp.Cands.run_iff`, `Fp.probes_card_le_greedy`, `Fp.Zrows_pi_le`, `Fp.probe_cnt_eq_oracle` (binary splitting), `Fp.qParam_spec`, `Fp.kParam_spec`; search version `Fp.findOne_spec` | `FpProbes.lean`, `FpStages.lean` |
| Proposition 19.13, except its last sentence | `obstruction`, `hyp_of_nsmul` (case (1)), `hyp_of_coprime` (case (2)) | `Obstruction.lean` |
| Lemma 19.18 (the two facts) | `ExpP2.F1`, `ExpP2.F1_lift`, `ExpP2.F2` | `ExpP2.lean` |
| Lemma 19.19 (survival), except its last sentence | `pair_survival`, `CaseL.rate_typeI`, `CaseL.rate_typeII`, `CaseL.rate_fst` | `Select.lean`, `ExpP2L.lean` |
| Lemma 19.20 (a light list) | `ExpP2.TI_light_le`, `ExpP2.light_triples_le`, `ExpP2Split.caseL_light₁`, `caseL_light₂`, `caseL_light₃` | `ExpP2.lean`, `ExpP2Split.lean` |
| Lemma 19.21 (Case L) | `CaseL.caseL`, `TheoremG.caseL_run` | `ExpP2L.lean`, `ExpP2Main.lean` |
| Lemma 19.22 (potential) | `CaseL.potential_avg`, `CaseL.Psi_greedy_le`; the choice by computable counts `CaseL.costL_eq`, `isGreedyL_costL_iff` | `ExpP2L.lean`, `ExpP2LZ.lean` |
| Lemma 19.23 (three heavy lists) | `ExpP2Split.TI_le_of_caseH`, `ExpP2.TI_classes_lt` | `ExpP2Split.lean`, `ExpP2.lean` |
| Lemma 19.24 (choosing the rows, Case H) | `FpBounds.partH_choice`, `partH_bounds`, `Sp_eq_Zc`, `caseH`, `TheoremG.caseH_run` (by the exact greedy choice, with `2e` in place of `e(2+e)`; the estimator, a device for the running time, is not formalized) | `FpBounds.lean`, `ExpP2Main.lean` |
| Theorem 19.17, correctness and counts | `TheoremG.theoremG`, `TheoremG.theoremG_group`: every solution lies in exactly one of the `7 + (⌊log₂ n⌋+1)³` sub-instances (`ExpP2Split.subInst_partition`, `exists_sol_iff_subInst`), each falls under Case L or Case H (`subInst_cases`) and is answered correctly with one detection call, with the bounds on the false positives; the reduction of `∏ ℤ_{m_i}`, `m_i ∣ p²`, to `ℤ_{p²}^r` (`ExpP2Reduce.exists_triple_iff_embedP2`, `card_image_embedP2`) | `ExpP2Main.lean`, `ExpP2Split.lean`, `ExpP2Reduce.lean` |

### Section 20: coordinatewise problems

| Item of the paper | Lean names | File |
|---|---|---|
| Lemma 20.3, one direction of (a) | `representable_of_system` | `Coord.lean` |
| Lemma 20.4 (algorithms from representations) | `prob_iff_threeSum`, `threeSum_iff_baseB`, `sum_mul_pow_eq_zero_iff` | `Coord.lean` |
| Lemma 20.8 (a gadget gives a reduction from Orthogonal Vectors), gadgets of every size | `Gadget.ov_iff_prob` (size 1), `GadgetT.ov_iff_prob`, `GadgetT.card_list_le` (the hypothesis OVH and the running time stay informal) | `Coord.lean`, `GadgetSize.lean` |
| Lemma 20.9 (representable ⇒ no gadget), gadgets of every size | `not_hasGadget_of_rep` (size 1), `not_hasGadgetOfSize_of_rep` | `Coord.lean`, `GadgetSize.lean` |
| Theorem 20.11 (the Boolean dichotomy) | `boolean_dichotomy`, `boolean_not_both`, `boolean_rep_iff`, `xorRel_rep`, `sumRel_rep`, `xorRel_not_rep`, `sumRel_not_rep`; certificates `boolCheck_eq` | `Boolean.lean` |
| Theorem 20.12 (functional relations over three letters) | `functional3_dichotomy`, `functional3_not_both`, `functional3_rep_iff`; certificates `fun3Chunk_0` … `fun3Chunk_19` over all `3^9 = 19683` maps | `Functional3.lean` |
| Proposition 20.14(b) (the `ℤ₄` square) | `z4Rel_rep`, `z4Rel_order4`, `z4Rel_not_rep_exp2`, `z4Rel_not_rep_torsionFree`, `z4Rel_not_rep_zmod`, `z4Rel_not_hasGadget`, `z4Rel_not_hasGadgetOfSize` | `Latin.lean`, `GadgetSize.lean` |
| Proposition 20.14(c) (the loop `L5`) | `l5Rel_not_rep`, `l5Rel_not_hasGadget`, `l5Rel_not_hasGadgetOfSize` | `Latin.lean`, `GadgetSize.lean` |
| Proposition 20.14(d) | `hasGadgetSome_iff_hasGadget`, `hasGadget_iff_restriction` | `GadgetSize.lean` |

### Section 21: triangle versions

| Item of the paper | Lean names | File |
|---|---|---|
| Theorem 21.3, correctness of the detection and all-edges versions | `Fp.exact_triangle_Fp_detect`, `exact_triangle_Fp_detect_params`, `exact_triangle_Fp_allEdges`; the instance `Fp.TriInst.J`, `J_count`, `J_mid_card`; the certification `Fp.Cands.certFalse_z`, `certTrue_z`, `uncert_fp`; the halving of the incidences `Fp.aeStep_halving`, chained over the stages `Fp.aeRun_card_le`, `aeRun_card_le_params`; parameters `Fp.params_q_exists`, `params_bounds`, `params_card_Gamma` | `FpTriangle.lean` |

Hypotheses beyond the paper's are minor and are stated in the docstrings: for example `0 < p` where
the paper has a prime `p`, bounds with `≤` where the paper has `<` (equal only for `n = 0`), and a
`q` with `p^{q−2} < 2eσ ≤ p^{q−1}` in place of the paper's `q = ⌈log_p(2eσ)⌉ + 1`.

## What is not formalized

* Every running time, and with it the legality of the calls: the size of the instances that are
  called (`N`, the numbered vertex sets) and `D ≤ N^ε`, `D^{1+γ} ≤ N`; here the calls are
  represented by their exact answers on instances indexed by blocks, and Lean proves the bound
  `|W| ≤ N²/√D` on the query set. The listing time of Lemma 19.4 and the "Cost" paragraphs.
* The arithmetic that turns `ε` and `γ` into the parameters (`q`, `σ`, `D`, `g`, `κ`, `k′`): the
  parameters enter as hypotheses (`TheoremG.Params`); the separate lemmas `ExpP2Reduce.exists_kappa`,
  `exists_kprime`, `q_le_kappa` and `exists_valBiased` are not composed into one theorem.
* Lemma 19.5's exact evaluation in `ℤ[X]/(X^m − 1)` (only the identity over `ℂ` is proved).
* Lemma 19.7's bound on the number of calls and its time; Theorem 19.8 and 19.9 as running times.
* Proposition 19.10, Theorem 19.11, Corollaries 19.12, 19.14 (for `ℤ₄^d` the per-homomorphism
  inequality `z4_obstruction` is proved) and 19.25, the last sentence of Proposition 19.13 (every
  non-elementary group falls under case (1) or (2)), and the last sentence of Lemma 19.19.
* Lemma 20.3 except one direction of (a), Corollary 20.5, Lemma 20.10 in general (only the two
  instances `ℤ₄` and `L5`, at every gadget size), Lemma 20.13 in general (only the instance
  `z4Rel_order4`), Proposition 20.14(a), (e) and (f), Proposition 20.15, and the orbit counts of
  Tables 6, 8 and 9, which rest on the computations of Section 20.6 (the ancillary scripts
  `q2_boolean.py`, `q2_functional3.py`, `q2_latin.py`, `q2_functional4.py`).
* Of Section 21: Lemma 21.2 (one evaluation), Propositions 21.4, 21.6, 21.9, 21.10, 21.11, 21.18,
  Theorem 21.5, Corollaries 21.7, 21.15, Lemmas 21.14, 21.16, Theorem 21.17, and Theorem 21.3 as a
  running time.
* Remarks, definitions, examples and open problems, which make no claim beyond the items above.

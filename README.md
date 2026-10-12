# Majdoddin/formal-math: Lean checks of "Thin matrix products up to D ≤ N^0.172"

This fork of [anthropics/formal-math](https://github.com/anthropics/formal-math) adds three Lean 4
projects (Lean v4.33.1, Mathlib v4.33.1) and an addition to `3sum-apsp/`. They accompany the paper
*Thin matrix products up to D ≤ N^0.172 and lossless reductions for 3SUM, Exact Triangle and APSP,
with 3SUM over abelian groups and a dichotomy for coordinatewise problems* by Ruhollah Majdoddin
(12 October 2026), whose Section 22.2 describes them. The paper builds on the preprint of Alman and
Vassilevska Williams (arXiv:2610.06783) that `3sum-apsp/` formalises.

| Project | What it checks |
|---|---|
| [`thin-matrix-products/`](thin-matrix-products/) | the mathematics of the paper outside Sections 18–21: the matrix theorem of Part I, the reductions of Part II, and Appendix A |
| [`xor-3xor/`](xor-3xor/) | Section 18 (3XOR), and the route for 3XOR that the preprint's Remark 23 sketches |
| [`groups/`](groups/) | Sections 19–21: 3SUM over finite abelian groups, the dichotomy for coordinatewise problems, the triangle versions |
| [`3sum-apsp/`](3sum-apsp/) (addition) | `ThreeSumApsp/Remark23/`: the remark's route for 3XOR item by item, with an explicit construction of the biased sets of Alon, Goldreich, Håstad and Peralta; and the statement `Remark_23` in `EndStatement.lean` (its running time), which is not proved (see that project's README) |

Each project's README lists, item by item in the paper's numbering, what is proved and what is not.
No file of the three new projects contains `sorry`, and their theorems depend on no axiom beyond
Lean's three standard ones (`propext`, `Classical.choice`, `Quot.sound`). Running times are not
formalised: the projects prove the identities, the counts, the correctness of the reductions and
the arithmetic of the constants and exponents, not that an algorithm runs within a time bound.
Results of the preprint and of other cited works enter as stated hypotheses. Build each project
from inside its folder with `lake build`.

Some files of `thin-matrix-products/` are adapted from `3sum-apsp/` (Apache 2.0, Anthropic PBC);
their headers and the README of `thin-matrix-products/` say which. The files added in this fork are
released, like the rest of the repository, under the Apache-2.0 licence in `LICENSE`.

---

# formal-math

Machine-checked Lean 4 formalizations published by Anthropic. Each subdirectory is a self-contained Lake project with its own toolchain pin, README and build instructions; build from inside the subdirectory. Projects follow the layout of the [Palomar](https://palomar-registry.org/) submission template (`Challenge.lean` / `Solution.lean` / `comparator.json` / `formalization.yaml` at the project root) and are submitted to Palomar with the subdirectory as the selected project; the licence file Palomar reads is this repository's root `LICENSE`.

| Project | Statement | Lean / Mathlib |
|---|---|---|
| [`zeta23/`](zeta23/) | More than two thirds of the zeros of the Riemann zeta function are simple and on the critical line (Alpöge–Furman, arXiv:2608.13637) | `leanprover/lean4:v4.33.0-rc2` / Mathlib `v4.33.0-rc2` |
| [`3sum-apsp/`](3sum-apsp/) | Programs of a word RAM solve 3SUM in O(n^1.9992) steps and the (min,+)-product and APSP in O(n^2.99942) steps, on integers of polynomial size; also bounds for Exact Triangle and Zero-Weight k-Clique, and further results of the paper, item by item (Alman–Vassilevska Williams, arXiv:2610.06783) | `leanprover/lean4:v4.33.1` / Mathlib `v4.33.1` |

## CI

Pull requests and pushes to `main` run [`.github/workflows/lean-projects.yml`](.github/workflows/lean-projects.yml) on each project folder whose files changed, and only on those; a change confined to CI configuration or documentation (`.github/`, this README, ...) verifies nothing, and a full run of every project is started manually from the Actions tab (`workflow_dispatch`, projects = `all`). The `verify` job runs on the runner label in the repository/organization variable `LEAN_CI_RUNNER` when it is set (e.g. a GitHub larger runner such as `ubuntu-latest-16-cores`), otherwise on `ubuntu-latest`. Pull-request runs reuse the project's previous Lake build for the same toolchain and manifest (only changed modules are rebuilt); merges to `main` and manual runs build from scratch. A project passes when `lake build` succeeds on its pinned toolchain with no `sorry` outside the trusted comparator statement files (`Challenge.lean`, `Challenge/<Topic>.lean`), and when the [Palomar registry](https://github.com/PalomarRegistry)'s acceptance check — [`leanprover/comparator`](https://github.com/leanprover/comparator) with a toolchain-matched `lean4export`, the independent `nanoda` kernel and the `landrun` sandbox, at the registry's tool pins — prints `Your solution is okay!` for every comparator configuration the project declares ([`.github/scripts/comparator-check.sh`](.github/scripts/comparator-check.sh); run it locally with `cd <project> && bash ../.github/scripts/comparator-check.sh`).

To add a project: create a top-level directory with `lakefile.toml` (or `lakefile.lean`), `lean-toolchain`, `lake-manifest.json`, a Mathlib-only `Challenge` module stating the headline theorems, a `Solution` module proving them from the library, and at least one comparator configuration (`comparator.json` next to the lakefile, or `comparator/config*.json`); add a row to the table above.

## License

Apache-2.0 — see [LICENSE](LICENSE). Individual projects may carry additional NOTICE files.

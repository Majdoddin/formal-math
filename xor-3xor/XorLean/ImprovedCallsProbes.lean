import XorLean.ImprovedCalls

/-!
# Improved 3XOR, Theorem II: the oracle's calls on the built instances

the improved write-up §4.4 (Lemma II.3, "the instance `I(H, 𝒫)` and one evaluation") and §4.5–4.6
(the algorithm and its correctness), stated on the instances that the algorithm builds, with
numbered vertices (`ImprovedCalls.lean`):

* `evalCall`: the digit instance `(i, j)` of `I(H, 𝒫)` with query part `Wp`, numbered into
  `Fin (g' 2^{l₁})`: one call of the `#Lop` oracle. Its counts do not depend on `Wp`
  (`evalCall_countAt_congr_W`).
* `evalCalls_spec` (Lemma II.3, generic in `g'` and the part size `M`): the positions of a set
  `𝒫 ⊆ 𝒫₀` are cut into at most `⌈|W|/M⌉` parts of at most `M` positions; for every part and
  every digit pair the call is an instance of `Lop(g' 2^{l₁}, 2^{l₁+l₂})` whose query set has
  exactly the part's size; every probe's position lies in exactly one part, its numbered position
  is a query of that part's calls, and `cnt_H(Q)` is the binary recombination of the `B²` answers
  there.
* `xor_direct_count_eval_params` (Lemma II.3 with the parameters of §4.2): `2 ≤ D`, `D ≤ N^ε`,
  `n/σ ≤ N`, `|𝒫| ≤ 8n²/σ`, and the parts have `M = ⌊N²/√D⌋` and number at most `1 + 2σ/√D`.
* `oracleCnt`, `oracleTotal` (the counts and the sum `Σ(H)` the algorithm reads from the oracle),
  `oracleCnt_eq_cnt`, `oracleTotal_eq_total`, `oracle_exitYes_iff`, `oracle_next_eq`,
  `Cands.run_congr`, `oracleRun` (the algorithm of §4.5 reading every count from the oracle),
  `oracleRun_eq_run`, and the composition `xor_direct_count_correct_oracle`: Theorem II's
  correctness when the rows are chosen greedily on the oracle's sums.

What is not composed here: the running time (no machine model), and the choice of the rows of
`π` and of the blocks (they are hypotheses, as in `Zc_pi_le`).
-/

set_option linter.unusedSectionVars false

namespace Xor.Improved

open Xor Finset

variable {d : ℕ}

/-! ### One call: a digit instance of `I(H, 𝒫)` with a query part, numbered -/

section generic

variable {S₁ S₂ S₃ : Finset (Vec d)} {k : ℕ} {π : Vec d →ₗ[ZMod 2] Vec k} {σ : ℕ} {l₁ l₂ : ℕ}

/-- One oracle call of Lemma II.3: the digit instance `(i, j)` (`X_i`, `Y_j`) of `I(H, 𝒫)` with
query part `Wp`, its vertices numbered into `Fin (g' 2^{l₁})` (`probeNum`). -/
noncomputable def evalCall (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' : ℕ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (i j : ℕ)
    (Wp : Finset ((Finset (Vec d) × Vec l₁) × (Finset (Vec d) × Vec l₂))) :
    LopInst (Fin (g' * 2 ^ l₁)) (Fin (g' * 2 ^ l₁)) (Vec (l₁ + l₂)) :=
  probeNum B₂ B₃ g' (bitInst (matX H) (matY H) i j Wp)

/-- The oracle's answers on a call do not depend on its query part. -/
theorem evalCall_countAt_congr_W (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' : ℕ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (i j : ℕ)
    (Wp Wp' : Finset ((Finset (Vec d) × Vec l₁) × (Finset (Vec d) × Vec l₂))) (a b : ℕ) :
    (evalCall B₂ B₃ g' H i j Wp).countAt a b = (evalCall B₂ B₃ g' H i j Wp').countAt a b :=
  LopInst.countAt_congr_W _ _ rfl rfl rfl a b

/-- The blocks of a probe of `𝒫₀` have at most `σ` elements. -/
theorem probe_blocks_card_le (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) {Q : Probe d k}
    (hQ : Q ∈ probes S₁ π B₂ B₃) : Q.2.1.2.card ≤ σ ∧ Q.2.2.2.card ≤ σ := by
  simp only [probes, Finset.mem_filter, Finset.mem_product] at hQ
  exact ⟨B₂.card_le _ _ (Finset.mem_filter.1 hQ.1.2.1).2,
    B₃.card_le _ _ (Finset.mem_filter.1 hQ.1.2.2).2⟩

/-- Every call is an instance of `Lop(g' 2^{l₁}, 2^{l₁+l₂})`: `N = g' 2^{l₁}` numbered vertices
per side, middle part `F₂^{l₁+l₂}`. -/
theorem evalCall_isLop (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' : ℕ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (i j : ℕ)
    (Wp : Finset ((Finset (Vec d) × Vec l₁) × (Finset (Vec d) × Vec l₂))) :
    (evalCall B₂ B₃ g' H i j Wp).IsLop (g' * 2 ^ l₁) (2 ^ (l₁ + l₂)) := by
  unfold evalCall probeNum
  rw [LopInst.number_isLop]
  simp [bitInst, Finset.card_univ, ZMod.card, Fintype.card_fin]

/-- The facts on one call at a probe of `𝒫₀` (`l₂ ≤ l₁`, at most `g'` blocks per list): the
query set has `|Wp|` elements when `Wp` consists of positions of probes of `𝒫₀`; the numbered
position of a probe whose position is in `Wp` is a query; and `cnt_H(Q)` is the recombination
`Σ_{i,j<B} 2^{i+j}` of the answers at its numbered position (blocks of `σ < 2^B` elements). -/
theorem evalCall_spec (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B : ℕ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (hl : l₂ ≤ l₁) (hB : σ < 2 ^ B)
    (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g') :
    (∀ (i j : ℕ) (Wp : Finset ((Finset (Vec d) × Vec l₁) × (Finset (Vec d) × Vec l₂))),
      Wp ⊆ (probes S₁ π B₂ B₃).image (pos H) →
      (evalCall B₂ B₃ g' H i j Wp).W.card = Wp.card ∧
      ∀ Q ∈ probes S₁ π B₂ B₃, pos H Q ∈ Wp →
        posNum B₂ B₃ H Q ∈ (evalCall B₂ B₃ g' H i j Wp).queries) ∧
    (∀ Q ∈ probes S₁ π B₂ B₃,
      ∀ Wp : Finset ((Finset (Vec d) × Vec l₁) × (Finset (Vec d) × Vec l₂)),
      (probeCands d k).cnt H Q = ∑ i ∈ range B, ∑ j ∈ range B,
        2 ^ (i + j) * (evalCall B₂ B₃ g' H i j Wp).countAt (posNum B₂ B₃ H Q).1
          (posNum B₂ B₃ H Q).2) := by
  refine ⟨fun i j Wp hWp => ?_, fun Q hQ Wp => ?_⟩
  · have hW : (bitInst (matX H) (matY H) i j Wp).W ⊆ leftVerts B₂ l₁ ×ˢ rightVerts B₃ l₂ :=
      hWp.trans (pos_image_subset B₂ B₃ H subset_rfl)
    obtain ⟨hq, hc⟩ := (probeNum_spec (S₁ := S₁) B₂ B₃ g' hg₂ hg₃ hl
      (bitInst (matX H) (matY H) i j Wp) H).2.2 hW
    refine ⟨hc, fun Q _ hQW => ?_⟩
    unfold evalCall
    rw [hq]
    exact Finset.mem_image.2 ⟨pos H Q, hQW, rfl⟩
  · obtain ⟨hb₂, hb₃⟩ := probe_blocks_card_le B₂ B₃ hQ
    rw [cnt_eq_oracle H σ B hB Wp Q hb₂ hb₃]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    unfold evalCall
    rw [((probeNum_spec (S₁ := S₁) B₂ B₃ g' hg₂ hg₃ hl (bitInst (matX H) (matY H) i j Wp) H).2.1 Q hQ).1]

/-- **Lemma II.3 on the built calls** (generic in `g'` and in the part size `M > 0`): for linear
`H : F₂^d → F₂^{l₁+l₂}` with `l₂ ≤ l₁`, blocks of at most `σ < 2^B` elements, at most `g'` blocks
per list and `𝒫 ⊆ 𝒫₀`, the positions `W = pos_H(𝒫)` are cut (`exists_cutting`) into parts with:
at most `⌈|W|/M⌉` parts; each part is a subset of `W` with at most `M` positions; for each part
and all digits `i, j`, the call `evalCall … i j Wp` is an instance of `Lop(g' 2^{l₁}, 2^{l₁+l₂})`
with exactly `|Wp|` query pairs; every probe's position lies in exactly one part; for that part
the probe's numbered position is a query of all its calls, and `cnt_H(Q)` is
`Σ_{i,j<B} 2^{i+j}` times the answers there. The size conditions `D ≤ N^ε`, `M = ⌊N²/√D⌋` and the
number of parts with the parameters of §4.2 are `xor_direct_count_eval_params`. -/
theorem evalCalls_spec (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B M : ℕ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (hl : l₂ ≤ l₁) (hB : σ < 2 ^ B)
    (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g')
    (P : Finset (Probe d k)) (hP : P ⊆ probes S₁ π B₂ B₃) (hM : 0 < M) :
    ∃ parts : Finset (Finset ((Finset (Vec d) × Vec l₁) × (Finset (Vec d) × Vec l₂))),
      parts.card ≤ ((P.image (pos H)).card + M - 1) / M ∧
      (∀ Wp ∈ parts, Wp ⊆ P.image (pos H) ∧ Wp.card ≤ M ∧
        ∀ i j, (evalCall B₂ B₃ g' H i j Wp).IsLop (g' * 2 ^ l₁) (2 ^ (l₁ + l₂)) ∧
          (evalCall B₂ B₃ g' H i j Wp).W.card = Wp.card) ∧
      (∀ Q ∈ P, ∃! Wp, Wp ∈ parts ∧ pos H Q ∈ Wp) ∧
      (∀ Q ∈ P, ∀ Wp ∈ parts, pos H Q ∈ Wp →
        (∀ i j, posNum B₂ B₃ H Q ∈ (evalCall B₂ B₃ g' H i j Wp).queries) ∧
        (probeCands d k).cnt H Q = ∑ i ∈ range B, ∑ j ∈ range B,
          2 ^ (i + j) * (evalCall B₂ B₃ g' H i j Wp).countAt (posNum B₂ B₃ H Q).1
            (posNum B₂ B₃ H Q).2) := by
  obtain ⟨parts, h1, h2, h3⟩ := exists_cutting (P.image (pos H)) M hM
  obtain ⟨hW, hcnt⟩ := evalCall_spec (S₁ := S₁) B₂ B₃ g' B H hl hB hg₂ hg₃
  have hsub : ∀ Wp ∈ parts, Wp ⊆ (probes S₁ π B₂ B₃).image (pos H) := fun Wp hWp =>
    (h1 Wp hWp).1.trans (Finset.image_subset_image hP)
  refine ⟨parts, h3, fun Wp hWp => ⟨(h1 Wp hWp).1, (h1 Wp hWp).2, fun i j =>
    ⟨evalCall_isLop B₂ B₃ g' H i j Wp, (hW i j Wp (hsub Wp hWp)).1⟩⟩,
    fun Q hQ => h2 _ (Finset.mem_image_of_mem _ hQ), fun Q hQ Wp hWp hQW =>
    ⟨fun i j => (hW i j Wp (hsub Wp hWp)).2 Q (hP hQ) hQW, hcnt Q (hP hQ) Wp⟩⟩

end generic

/-! ### Lemma II.3 with the parameters of §4.2 -/

/-- **Lemma II.3 on the built calls, with the parameters of §4.2** (in the style of
`reduction_spec`). Parameters: `0 < ε ≤ 1/2`, `Λ = 4e`, `σ = ⌊√(n^ε/Λ)⌋`, `q = ⌈log₂(2eσ²)⌉`,
`g' = ⌈3n/σ⌉`, `B = ⌈log₂(σ+1)⌉`, with `σ ≥ 1` and `n/σ ≥ 2` (the text's `n ≥ n₀`); lists of at
most `n` elements; `π` given by `⌈log₂(n/σ)⌉` rows chosen greedily for `Z` from a
`(1/k)`-biased `E_k` (as in `Zc_pi_le`); blocks of at most `σ` elements for `π`; a row list
`rows` with `1 ≤ l := |rows| ≤ q` (the map `H` being built, any prefix of a stage); `𝒫 ⊆ 𝒫₀`.
With `H = splitMap rows`, `N = g' 2^{⌈l/2⌉}`, `D = 2^l`, `M = ⌊N²/√D⌋`: `2 ≤ D`, `D ≤ N^ε`,
`n/σ ≤ N`, `M > 0`, `|𝒫| ≤ 8n²/σ`, `σ < 2^B`, at most `g'` blocks per list; and the positions
of `𝒫` are cut into at most `⌈|W|/M⌉ ≤ 1 + 2σ/√D` parts of at most `M` positions, each part's
`B²` calls are instances of `Lop(N, D)` with as many query pairs as the part, every probe's
position lies in exactly one part, its numbered position is a query of that part's calls, and
`cnt_H(Q)` (for `H = rowsMap rows`) is the recombination of the answers there.
Not `n ≤ N`: for a map with few rows (`D < σ²`) `N` can be below `n`; the text uses only
`n/σ ≤ N` (§4.7 (iv)). The running time is not formalized. -/
theorem xor_direct_count_eval_params (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (n σ q g' B : ℕ)
    (hσ : σ = ⌊Real.sqrt ((n : ℝ) ^ ε / (4 * Real.exp 1))⌋₊)
    (hq : q = ⌈Real.logb 2 (2 * Real.exp 1 * (σ : ℝ) ^ 2)⌉₊)
    (hg' : g' = ⌈3 * (n : ℝ) / σ⌉₊) (hB : B = Nat.clog 2 (σ + 1))
    (hσ1 : 1 ≤ σ) (hnσ : 2 ≤ (n : ℝ) / σ)
    (S₁ S₂ S₃ : Finset (Vec d)) (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (Ek : Multiset (Vec d)) (πrows : List (Vec d))
    (hk : πrows.length = ⌈Real.logb 2 ((n : ℝ) / σ)⌉₊)
    (hEk : IsBiased (1 / (πrows.length : ℝ)) Ek)
    (hgk : IsGreedy Ek (fun l => (Zc S₁ S₂ S₃ (rowsMap l) : ℝ)) πrows)
    (B₂ : Blocking S₂ (rowsMap πrows) σ) (B₃ : Blocking S₃ (rowsMap πrows) σ)
    (rows : List (Vec d)) (hl1 : 1 ≤ rows.length) (hlq : rows.length ≤ q)
    (P : Finset (Probe d πrows.length)) (hP : P ⊆ probes S₁ (rowsMap πrows) B₂ B₃) :
    let H := splitMap rows
    let N : ℕ := g' * 2 ^ ((rows.length + 1) / 2)
    let D : ℕ := 2 ^ rows.length
    let M := ⌊(N : ℝ) ^ 2 / Real.sqrt (D : ℝ)⌋₊
    2 ≤ D ∧ (D : ℝ) ≤ (N : ℝ) ^ ε ∧ (n : ℝ) / σ ≤ N ∧ 0 < M ∧
    (P.card : ℝ) ≤ 8 * (n : ℝ) ^ 2 / σ ∧ σ < 2 ^ B ∧ B₂.set.card ≤ g' ∧ B₃.set.card ≤ g' ∧
    ∃ parts : Finset (Finset ((Finset (Vec d) × Vec ((rows.length + 1) / 2)) ×
        (Finset (Vec d) × Vec (rows.length / 2)))),
      parts.card ≤ ((P.image (pos H)).card + M - 1) / M ∧
      (parts.card : ℝ) ≤ 1 + 2 * σ / Real.sqrt (D : ℝ) ∧
      (∀ Wp ∈ parts, Wp ⊆ P.image (pos H) ∧ Wp.card ≤ M ∧
        ∀ i j, (evalCall B₂ B₃ g' H i j Wp).IsLop N D ∧
          (evalCall B₂ B₃ g' H i j Wp).W.card = Wp.card) ∧
      (∀ Q ∈ P, ∃! Wp, Wp ∈ parts ∧ pos H Q ∈ Wp) ∧
      (∀ Q ∈ P, ∀ Wp ∈ parts, pos H Q ∈ Wp →
        (∀ i j, posNum B₂ B₃ H Q ∈ (evalCall B₂ B₃ g' H i j Wp).queries) ∧
        (probeCands d πrows.length).cnt (rowsMap rows) Q = ∑ i ∈ range B, ∑ j ∈ range B,
          2 ^ (i + j) * (evalCall B₂ B₃ g' H i j Wp).countAt (posNum B₂ B₃ H Q).1
            (posNum B₂ B₃ H Q).2) := by
  intro H N D M
  -- the parameters of §4.2
  have hsp := staged_params ε hε n
  dsimp only at hsp
  rw [← hσ, ← hq] at hsp
  obtain ⟨hqΛ, hΛn, -, -, -, -⟩ := hsp hσ1
  have hsp' := staged_params' n σ hσ1 hnσ
  dsimp only at hsp'
  rw [← hk, ← hg', ← hB] at hsp'
  obtain ⟨h2k, h2k', hk1, hg'lo, hg'hi, hblk, hσB, -⟩ := hsp'
  have he := Real.exp_one_gt_d9
  have hσR : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  have hσ0 : 0 < σ := hσ1
  have hσn : (σ : ℝ) ≤ n := by
    have := (le_div_iff₀ (by linarith : (0 : ℝ) < σ)).1 hnσ
    linarith
  -- at most `g'` blocks per list
  have hset : ∀ {S : Finset (Vec d)} (Bl : Blocking S (rowsMap πrows) σ), S.card ≤ n →
      Bl.set.card ≤ g' := by
    intro S Bl hS
    have h1 := Bl.card_set_le hσ0
    have h2 : (S.card : ℝ) / σ ≤ n / σ :=
      div_le_div_of_nonneg_right (by exact_mod_cast hS) (by linarith)
    have : (Bl.set.card : ℝ) < g' := by linarith
    exact_mod_cast this.le
  have hg₂ := hset B₂ h₂
  have hg₃ := hset B₃ h₃
  -- `|𝒫| ≤ |𝒫₀| ≤ 8n²/σ` (Lemma II.1 (ii))
  have hZ := (Zc_pi_le S₁ S₂ S₃ n σ hσ0 h₁ h₂ h₃ Ek πrows hk1 hEk hgk h2k).2
  have hP0 := (probes_card_le S₁ S₂ S₃ (rowsMap πrows) n σ hσ0 B₂ B₃ h₁ h₂ h₃ h2k' hZ).2
  have hPc : (P.card : ℝ) ≤ 8 * (n : ℝ) ^ 2 / σ :=
    le_trans (by exact_mod_cast Finset.card_le_card hP) hP0
  -- `N` and `D`
  have hDR : (D : ℝ) = (2 : ℝ) ^ rows.length := by
    show ((2 ^ rows.length : ℕ) : ℝ) = _
    push_cast; ring
  have hNR : (N : ℝ) = g' * (2 : ℝ) ^ ((rows.length + 1) / 2) := by
    show ((g' * 2 ^ ((rows.length + 1) / 2) : ℕ) : ℝ) = _
    push_cast; ring
  have hD1 : (1 : ℝ) ≤ D := by rw [hDR]; exact one_le_pow₀ (by norm_num)
  have hDΛ : (D : ℝ) < 4 * Real.exp 1 * (σ : ℝ) ^ 2 := by
    rw [hDR]
    exact lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) hlq) hqΛ
  obtain ⟨hhalf1, hhalf2⟩ := two_pow_half rows.length
  have hNlo : (g' : ℝ) * Real.sqrt D ≤ N := by
    rw [hNR, hDR]; exact mul_le_mul_of_nonneg_left hhalf1 (Nat.cast_nonneg _)
  have hNhi : (N : ℝ) ^ 2 ≤ 2 * (g' : ℝ) ^ 2 * D := by
    rw [hNR, hDR]
    calc ((g' : ℝ) * (2 : ℝ) ^ ((rows.length + 1) / 2)) ^ 2
        = (g' : ℝ) ^ 2 * ((2 : ℝ) ^ ((rows.length + 1) / 2)) ^ 2 := by ring
      _ ≤ (g' : ℝ) ^ 2 * (2 * 2 ^ rows.length) :=
          mul_le_mul_of_nonneg_left hhalf2 (by positivity)
      _ = 2 * (g' : ℝ) ^ 2 * 2 ^ rows.length := by ring
  obtain ⟨hDN, h9, -, -, -⟩ := eval_cost ε (1 / 4) (4 * Real.exp 1) hε hε2 (by norm_num)
    (by norm_num) (by linarith) n σ g' N D hσR hσn hD1 hDΛ hΛn hg'lo hg'hi hNlo hNhi
  have hW : (((P.image (pos H)).card : ℕ) : ℝ) ≤ 8 * (n : ℝ) ^ 2 / σ :=
    le_trans (by exact_mod_cast Finset.card_image_le) hPc
  obtain ⟨hM, hparts⟩ := parts_le n σ N D hσR hσn hD1 h9 _ hW
  have hD2 : 2 ≤ D := by
    show 2 ≤ 2 ^ rows.length
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ rows.length := Nat.pow_le_pow_right (by norm_num) hl1
  have hnN : (n : ℝ) / σ ≤ N := by
    rw [hNR]
    have h1 : (n : ℝ) / σ ≤ 3 * n / σ :=
      div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by linarith)
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ ((rows.length + 1) / 2) := one_le_pow₀ (by norm_num)
    have h3 : (g' : ℝ) ≤ g' * (2 : ℝ) ^ ((rows.length + 1) / 2) :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) h2
    linarith
  -- Lemma II.3, generic
  obtain ⟨parts, hp1, hp2, hp3, hp4⟩ := evalCalls_spec (S₁ := S₁) B₂ B₃ g' B M H (by omega)
    hσB hg₂ hg₃ P hP hM
  refine ⟨hD2, hDN, hnN, hM, hPc, hσB, hg₂, hg₃, parts, hp1,
    (Nat.cast_le.2 hp1).trans hparts, fun Wp hWp => ⟨(hp2 Wp hWp).1, (hp2 Wp hWp).2.1,
      fun i j => ⟨?_, ((hp2 Wp hWp).2.2 i j).2⟩⟩, hp3, fun Q hQ Wp hWp hQW =>
    ⟨(hp4 Q hQ Wp hWp hQW).1, by rw [← cnt_splitMap]; exact (hp4 Q hQ Wp hWp hQW).2⟩⟩
  obtain ⟨a, b, c⟩ := ((hp2 Wp hWp).2.2 i j).1
  refine ⟨a, b, c.trans (le_of_eq ?_)⟩
  show 2 ^ ((rows.length + 1) / 2 + rows.length / 2) = 2 ^ rows.length
  congr 1
  omega

/-! ### `run` depends only on the row rule on subsets of `𝒫₀` -/

/-- The algorithm's answer from `𝒫₀` depends on the row rule only through its values on subsets
of `𝒫₀` (every `𝒫_t` is one). -/
theorem Cands.run_congr {X ι : Type*} (C : Cands X ι d) (rowsOf rowsOf' : Finset X → List (Vec d))
    (L : ℕ) (P₀ : Finset X) (h : ∀ P ⊆ P₀, rowsOf P = rowsOf' P) :
    C.run rowsOf L P₀ = C.run rowsOf' L P₀ := by
  induction L generalizing P₀ with
  | zero => rfl
  | succ L ih =>
    unfold Cands.run
    rw [h P₀ subset_rfl]
    congr 2
    exact ih _ fun P hP => h P (hP.trans (Finset.filter_subset _ _))

/-! ### The counts and sums the algorithm reads from the oracle -/

section oracle

variable {S₁ S₂ S₃ : Finset (Vec d)} {k : ℕ} {π : Vec d →ₗ[ZMod 2] Vec k} {σ : ℕ}

/-- The count of a probe read from the oracle: the binary recombination
`Σ_{i,j<B} 2^{i+j} (answer of call (i,j) at the probe's numbered position)` of the `B²` digit
calls of `I(H, 𝒫)` with query part `Wp`, for `H = splitMap rows`. -/
noncomputable def oracleCnt (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B : ℕ)
    (rows : List (Vec d))
    (Wp : Finset ((Finset (Vec d) × Vec ((rows.length + 1) / 2)) ×
      (Finset (Vec d) × Vec (rows.length / 2)))) (Q : Probe d k) : ℕ :=
  ∑ i ∈ range B, ∑ j ∈ range B, 2 ^ (i + j) *
    (evalCall B₂ B₃ g' (splitMap rows) i j Wp).countAt (posNum B₂ B₃ (splitMap rows) Q).1
      (posNum B₂ B₃ (splitMap rows) Q).2

/-- The sum `Σ(H) = Σ_{Q ∈ 𝒫} cnt_H(Q)` that step 2(b) forms from the oracle's answers, as a
function of the rows `H` (query set: all positions of `𝒫`). -/
noncomputable def oracleTotal (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B : ℕ)
    (P : Finset (Probe d k)) (rows : List (Vec d)) : ℝ :=
  ∑ Q ∈ P, (oracleCnt B₂ B₃ g' B rows (P.image (pos (splitMap rows))) Q : ℝ)

/-- The oracle count does not depend on the query part. -/
theorem oracleCnt_congr_W (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B : ℕ)
    (rows : List (Vec d))
    (Wp Wp' : Finset ((Finset (Vec d) × Vec ((rows.length + 1) / 2)) ×
      (Finset (Vec d) × Vec (rows.length / 2)))) (Q : Probe d k) :
    oracleCnt B₂ B₃ g' B rows Wp Q = oracleCnt B₂ B₃ g' B rows Wp' Q := by
  unfold oracleCnt
  simp only [evalCall_countAt_congr_W B₂ B₃ g' (splitMap rows) _ _ Wp Wp']

/-- **Lemmas II.2 and II.3 composed with the rows**: for every row list (any length), the count
read from the oracle at a probe of `𝒫₀` is `cnt_H(Q)` for `H = rowsMap rows`, when the blocks
have at most `σ < 2^B` elements and each list has at most `g'` blocks. -/
theorem oracleCnt_eq_cnt (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B : ℕ)
    (hB : σ < 2 ^ B) (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g') (rows : List (Vec d))
    (Wp : Finset ((Finset (Vec d) × Vec ((rows.length + 1) / 2)) ×
      (Finset (Vec d) × Vec (rows.length / 2)))) {Q : Probe d k}
    (hQ : Q ∈ probes S₁ π B₂ B₃) :
    oracleCnt B₂ B₃ g' B rows Wp Q = (probeCands d k).cnt (rowsMap rows) Q := by
  rw [← cnt_splitMap]
  exact ((evalCall_spec (S₁ := S₁) B₂ B₃ g' B (splitMap rows) (by omega) hB hg₂ hg₃).2
    Q hQ Wp).symm

/-- **The sums**: for `𝒫 ⊆ 𝒫₀`, the sum formed from the oracle's answers is `Σ(H)` of
`ImprovedStages.lean` (`Cands.total`), as functions of the rows. -/
theorem oracleTotal_eq_total (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B : ℕ)
    (hB : σ < 2 ^ B) (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g')
    {P : Finset (Probe d k)} (hP : P ⊆ probes S₁ π B₂ B₃) :
    oracleTotal B₂ B₃ g' B P = (probeCands d k).total P := by
  funext rows
  unfold oracleTotal Cands.total
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [oracleCnt_eq_cnt B₂ B₃ g' B hB hg₂ hg₃ rows _ (hP hQ)]

/-- **Step 2(c) from the oracle's answers** is the YES exit `exitYes`. -/
theorem oracle_exitYes_iff (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B : ℕ)
    (hB : σ < 2 ^ B) (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g')
    {P : Finset (Probe d k)} (hP : P ⊆ probes S₁ π B₂ B₃) (rows : List (Vec d)) :
    P.card < 2 * ∑ Q ∈ P, oracleCnt B₂ B₃ g' B rows (P.image (pos (splitMap rows))) Q ↔
      (probeCands d k).exitYes P (rowsMap rows) := by
  unfold Cands.exitYes
  rw [Finset.sum_congr rfl fun Q hQ => oracleCnt_eq_cnt B₂ B₃ g' B hB hg₂ hg₃ rows _ (hP hQ)]

/-- **Step 2(d) from the oracle's answers** is the survivor set `next`. -/
theorem oracle_next_eq (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B : ℕ)
    (hB : σ < 2 ^ B) (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g')
    {P : Finset (Probe d k)} (hP : P ⊆ probes S₁ π B₂ B₃) (rows : List (Vec d)) :
    P.filter (fun Q => 0 < oracleCnt B₂ B₃ g' B rows (P.image (pos (splitMap rows))) Q) =
      (probeCands d k).next P (rowsMap rows) := by
  unfold Cands.next
  exact Finset.filter_congr fun Q hQ => by
    rw [oracleCnt_eq_cnt B₂ B₃ g' B hB hg₂ hg₃ rows _ (hP hQ)]

open Classical in
/-- The algorithm of §4.5 with every count read from the oracle: step 2(c) compares
`Σ_Q oracleCnt` with `|𝒫|/2`, step 2(d) keeps the probes with a positive oracle count, step 3
scans. The rows `rowsOf 𝒫` of a stage are an argument (step 2(b)). -/
noncomputable def oracleRun (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B : ℕ)
    (rowsOf : Finset (Probe d k) → List (Vec d)) : ℕ → Finset (Probe d k) → Bool
  | 0, P => decide (∃ Q ∈ P, 0 < (probeCands d k).z Q)
  | t + 1, P =>
    if P.card = 0 then false
    else if P.card < 2 * ∑ Q ∈ P, oracleCnt B₂ B₃ g' B (rowsOf P)
        (P.image (pos (splitMap (rowsOf P)))) Q then true
    else oracleRun B₂ B₃ g' B rowsOf t
      (P.filter fun Q => 0 < oracleCnt B₂ B₃ g' B (rowsOf P)
        (P.image (pos (splitMap (rowsOf P)))) Q)

/-- From any `𝒫 ⊆ 𝒫₀`, the algorithm reading the oracle is the algorithm `run` of
`ImprovedStages.lean`. -/
theorem oracleRun_eq_run (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' B : ℕ)
    (hB : σ < 2 ^ B) (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g')
    (rowsOf : Finset (Probe d k) → List (Vec d)) (L : ℕ) (P : Finset (Probe d k))
    (hP : P ⊆ probes S₁ π B₂ B₃) :
    oracleRun B₂ B₃ g' B rowsOf L P = (probeCands d k).run rowsOf L P := by
  induction L generalizing P with
  | zero => rfl
  | succ L ih =>
    unfold oracleRun Cands.run
    rw [oracle_next_eq B₂ B₃ g' B hB hg₂ hg₃ hP,
      ih ((probeCands d k).next P (rowsMap (rowsOf P))) ((Finset.filter_subset _ _).trans hP)]
    have he := oracle_exitYes_iff B₂ B₃ g' B hB hg₂ hg₃ hP (rowsOf P)
    by_cases h0 : P.card = 0
    · rw [if_pos h0, if_pos h0]
    rw [if_neg h0, if_neg h0]
    by_cases hx : (probeCands d k).exitYes P (rowsMap (rowsOf P))
    · rw [if_pos (he.2 hx), if_pos hx]
    · rw [if_neg (fun h => hx (he.1 h)), if_neg hx]

end oracle

/-! ### Theorem II's correctness with the rows chosen on the oracle's sums -/

/-- **Theorem II, correctness, composed with the oracle (Lemmas II.2–II.5)**: as
`xor_direct_count_correct`, but step 2(b) is greedy on the sums `oracleTotal` formed from the
oracle's answers (`B²` digit calls per evaluation, `σ < 2^B`, at most `g'` blocks per list), and
this is required only for the sets `𝒫 ⊆ 𝒫₀` that the algorithm meets. The algorithm (`run`, or
`oracleRun`, which also reads steps 2(c), 2(d) from the oracle) answers YES iff the instance has a
solution. The call conditions (`Lop(N, D)`, `D ≤ N^ε`, the parts of `W`) are
`xor_direct_count_eval_params`; the running time is not formalized. -/
theorem xor_direct_count_correct_oracle (S₁ S₂ S₃ : Finset (Vec d)) {k : ℕ}
    (π : Vec d →ₗ[ZMod 2] Vec k) (σ q L g' B : ℕ) (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    (E : Multiset (Vec d)) (hE : IsBiased (1 / (q : ℝ)) E) (hq : 0 < q)
    (hqσ : Real.exp 1 * (2 : ℝ)⁻¹ ^ q * (σ ^ 2 : ℕ) ≤ 1 / 2)
    (hB : σ < 2 ^ B) (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g')
    (rowsOf : Finset (Probe d k) → List (Vec d))
    (hrule : ∀ P ⊆ probes S₁ π B₂ B₃,
      (rowsOf P).length = q ∧ IsGreedy E (oracleTotal B₂ B₃ g' B P) (rowsOf P)) :
    ((probeCands d k).run rowsOf L (probes S₁ π B₂ B₃) = true ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) ∧
    (oracleRun B₂ B₃ g' B rowsOf L (probes S₁ π B₂ B₃) = true ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) := by
  classical
  let rowsOf' : Finset (Probe d k) → List (Vec d) := fun P =>
    if P ⊆ probes S₁ π B₂ B₃ then rowsOf P else greedyRows E ((probeCands d k).total P) q
  have hrule' : (probeCands d k).GreedyRule E q rowsOf' := by
    intro P
    by_cases hP : P ⊆ probes S₁ π B₂ B₃
    · simp only [rowsOf', if_pos hP]
      obtain ⟨h1, h2⟩ := hrule P hP
      rw [oracleTotal_eq_total B₂ B₃ g' B hB hg₂ hg₃ hP] at h2
      exact ⟨h1, h2⟩
    · simp only [rowsOf', if_neg hP]
      exact (probeCands d k).greedyRule_greedyRows E hE.1 q P
  have hcongr : (probeCands d k).run rowsOf L (probes S₁ π B₂ B₃) =
      (probeCands d k).run rowsOf' L (probes S₁ π B₂ B₃) :=
    Cands.run_congr _ _ _ L _ fun P hP => by simp only [rowsOf', if_pos hP]
  have hmain : (probeCands d k).run rowsOf L (probes S₁ π B₂ B₃) = true ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0 := by
    rw [hcongr]
    exact xor_direct_count_correct S₁ S₂ S₃ π σ q L B₂ B₃ E hE hq hqσ rowsOf' hrule'
  refine ⟨hmain, ?_⟩
  rw [oracleRun_eq_run B₂ B₃ g' B hB hg₂ hg₃ rowsOf L _ subset_rfl]
  exact hmain

end Xor.Improved

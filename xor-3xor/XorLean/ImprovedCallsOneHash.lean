import XorLean.ImprovedCalls

/-!
# Improved 3XOR, Theorem I′ (§3.2): the one detection call on the built instance

the improved write-up §3.2, steps 3–4 and "The call", stated on the instance the algorithm builds,
with numbered vertices (`ImprovedCalls.lean`):

* `detectCall`: the support instance `I(H, 𝒫)` (`X' = [X > 0]`, `Y' = [Y > 0]`, query set the
  positions of `𝒫`), numbered into `Fin (g' 2^{l₁})`: the one call of the detection oracle.
* `oneHashYesNum`: the algorithm's answer read from that call (`AcceptsAt` at the numbered
  position of a probe), followed by the scan of step 4.
* `detectCall_spec` (generic): the call is an instance of `Lop(g' 2^{l₁}, 2^{l₁+l₂})`, its query
  set has `|pos_H(𝒫)|` elements, every probe's numbered position is a query, and the answer
  there is `cnt_H(Q) > 0`. `xor_direct_detection_correct_num`: the numbered algorithm answers YES
  iff a solution exists.
* `xor_direct_detection_call`: the same with the parameters of §3.2 (`oneHash_params`): `k ≥ 1`
  (proved from `n ≥ 2^{1/ε}`), `2 ≤ D`, `D ≤ N^ε`, the call is `Lop(N, D)`, `|W| ≤ 8n²/σ <
  N²/√D`, so one call suffices.

The running time is not formalized.
-/

set_option linter.unusedSectionVars false

namespace Xor.Improved

open Xor Finset

variable {d : ℕ}

section generic

variable {S₁ S₂ S₃ : Finset (Vec d)} {k : ℕ} {π : Vec d →ₗ[ZMod 2] Vec k} {σ : ℕ} {l₁ l₂ : ℕ}

/-- The one call of Theorem I′ (step 3): the support instance of `I(H, 𝒫)` with query set the
positions of `𝒫`, numbered into `Fin (g' 2^{l₁})`. -/
noncomputable def detectCall (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' : ℕ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (P : Finset (Probe d k)) :
    LopInst (Fin (g' * 2 ^ l₁)) (Fin (g' * 2 ^ l₁)) (Vec (l₁ + l₂)) :=
  probeNum B₂ B₃ g' (suppInst (matX H) (matY H) (P.image (pos H)))

/-- The answer of Theorem I′'s algorithm read from the numbered call: some probe of `𝒫₀` is
answered positively at its numbered position, and its scan (step 4) finds a solution. -/
def oneHashYesNum (S₁ S₂ S₃ : Finset (Vec d)) (π : Vec d →ₗ[ZMod 2] Vec k)
    (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' : ℕ) (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) :
    Prop :=
  ∃ Q ∈ probes S₁ π B₂ B₃,
    (detectCall B₂ B₃ g' H (probes S₁ π B₂ B₃)).AcceptsAt (posNum B₂ B₃ H Q).1
      (posNum B₂ B₃ H Q).2 ∧ ∃ x₂ ∈ Q.2.1.2, Q.1 + x₂ ∈ Q.2.2.2

/-- **The call of Theorem I′** (generic; `l₂ ≤ l₁`, at most `g'` blocks per list, `𝒫 ⊆ 𝒫₀`):
the call is an instance of `Lop(g' 2^{l₁}, 2^{l₁+l₂})`; its query set has `|pos_H(𝒫)|`
elements; the numbered position of every probe of `𝒫` is a query; and for every probe of `𝒫₀`
the answer at its numbered position is `cnt_H(Q) > 0` (Lemma II.2 with supports). -/
theorem detectCall_spec (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' : ℕ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (hl : l₂ ≤ l₁)
    (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g')
    (P : Finset (Probe d k)) (hP : P ⊆ probes S₁ π B₂ B₃) :
    (detectCall B₂ B₃ g' H P).IsLop (g' * 2 ^ l₁) (2 ^ (l₁ + l₂)) ∧
    (detectCall B₂ B₃ g' H P).W.card = (P.image (pos H)).card ∧
    (∀ Q ∈ P, posNum B₂ B₃ H Q ∈ (detectCall B₂ B₃ g' H P).queries) ∧
    (∀ Q ∈ probes S₁ π B₂ B₃,
      ((detectCall B₂ B₃ g' H P).AcceptsAt (posNum B₂ B₃ H Q).1 (posNum B₂ B₃ H Q).2 ↔
        0 < (probeCands d k).cnt H Q)) := by
  have spec := probeNum_spec (S₁ := S₁) B₂ B₃ g' hg₂ hg₃ hl
    (suppInst (matX H) (matY H) (P.image (pos H))) H
  have hW : (suppInst (matX H) (matY H) (P.image (pos H))).W ⊆
      leftVerts B₂ l₁ ×ˢ rightVerts B₃ l₂ := pos_image_subset B₂ B₃ H hP
  obtain ⟨hq, hc⟩ := spec.2.2 hW
  refine ⟨(spec.1 _).2 ?_, hc, fun Q hQ => ?_, fun Q hQ => ?_⟩
  · simp [suppInst, Finset.card_univ, ZMod.card, Fintype.card_fin]
  · unfold detectCall
    rw [hq]
    exact Finset.mem_image.2 ⟨pos H Q, Finset.mem_image_of_mem _ hQ, rfl⟩
  · exact (spec.2.1 Q hQ).2.trans (flagged_iff H _ Q)

/-- The numbered algorithm gives the same answer as `oneHashYes` (answers at positions). -/
theorem oneHashYesNum_iff (S₁ S₂ S₃ : Finset (Vec d)) (π : Vec d →ₗ[ZMod 2] Vec k)
    (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' : ℕ) (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂))
    (hl : l₂ ≤ l₁) (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g') :
    oneHashYesNum S₁ S₂ S₃ π B₂ B₃ g' H ↔ oneHashYes S₁ S₂ S₃ π B₂ B₃ H := by
  have hans := (detectCall_spec (S₁ := S₁) B₂ B₃ g' H hl hg₂ hg₃ _ subset_rfl).2.2.2
  unfold oneHashYesNum oneHashYes
  refine exists_congr fun Q => ?_
  constructor
  · rintro ⟨hQ, ha, hs⟩
    exact ⟨hQ, (flagged_iff H _ Q).2 ((hans Q hQ).1 ha), hs⟩
  · rintro ⟨hQ, ha, hs⟩
    exact ⟨hQ, (hans Q hQ).2 ((flagged_iff H _ Q).1 ha), hs⟩

/-- **Theorem I′, correctness, on the numbered call**: for every linear `π`, blocks, at most `g'`
blocks per list and `H` with `l₂ ≤ l₁`, the algorithm reading the one numbered detection call
answers YES iff the instance has a solution. -/
theorem xor_direct_detection_correct_num (S₁ S₂ S₃ : Finset (Vec d))
    (π : Vec d →ₗ[ZMod 2] Vec k) (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' : ℕ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (hl : l₂ ≤ l₁)
    (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g') :
    oneHashYesNum S₁ S₂ S₃ π B₂ B₃ g' H ↔ ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0 :=
  (oneHashYesNum_iff S₁ S₂ S₃ π B₂ B₃ g' H hl hg₂ hg₃).trans
    (xor_direct_detection_correct S₁ S₂ S₃ π B₂ B₃ H)

end generic

/-! ### The call with the parameters of §3.2 -/

/-- **Theorem I′, the one call with the parameters of §3.2** (in the style of `reduction_spec`).
Parameters (`oneHash_params`): `0 < ε, γ ≤ 1/2`, `q = ⌊ε log₂ n⌋`, `D = 2^q`, `g = ⌈D^{γ/2}⌉`,
`σ = ⌊√(D/g)⌋`, `k = ⌈log₂(n/σ)⌉`, `g' = ⌈3n/σ⌉`, `N = g' 2^{⌈q/2⌉}`, and `n ≥ 2^{1/ε}`. Lists
of at most `n` elements; `k + q` rows chosen greedily for `Z` from a `(1/(k+q))`-biased `E`
(as in `oneHash_bounds`), `π` the `k` first-chosen rows (`rows.drop q`), `H` the `q` last-chosen
(`splitMap (rows.take q)`); blocks of at most `σ` elements for `π`. Then: `k ≥ 1` (from the
parameters), `2 ≤ D`, `D ≤ N^ε`, at most `g'` blocks per list, `|𝒫₀| ≤ 8n²/σ`; the one call is an
instance of `Lop(N, D)` whose query set has `|pos_H(𝒫₀)| ≤ N²/√D` elements; every probe's
numbered position is a query and the answer there is `cnt_H(Q) > 0` for `H = rowsMap (rows.take
q)`; and the algorithm reading the call answers YES iff a solution exists. -/
theorem xor_direct_detection_call (ε γ : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hγ : 0 < γ)
    (hγ2 : γ ≤ 1 / 2) (n q D g σ k g' : ℕ)
    (hq : q = ⌊ε * Real.logb 2 n⌋₊) (hD : D = 2 ^ q) (hg : g = ⌈(D : ℝ) ^ (γ / 2)⌉₊)
    (hσ : σ = ⌊Real.sqrt ((D : ℝ) / g)⌋₊) (hk : k = ⌈Real.logb 2 ((n : ℝ) / σ)⌉₊)
    (hg' : g' = ⌈3 * (n : ℝ) / σ⌉₊) (hn : (2 : ℝ) ^ (1 / ε) ≤ n)
    (S₁ S₂ S₃ : Finset (Vec d)) (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (E : Multiset (Vec d)) (rows : List (Vec d)) (hlen : rows.length = k + q)
    (hE : IsBiased (1 / (rows.length : ℝ)) E)
    (hgr : IsGreedy E (fun l => (Zc S₁ S₂ S₃ (rowsMap l) : ℝ)) rows)
    (B₂ : Blocking S₂ (rowsMap (rows.drop q)) σ) (B₃ : Blocking S₃ (rowsMap (rows.drop q)) σ) :
    let H := splitMap (rows.take q)
    let N : ℕ := g' * 2 ^ ((q + 1) / 2)
    let C := detectCall B₂ B₃ g' H (probes S₁ (rowsMap (rows.drop q)) B₂ B₃)
    1 ≤ k ∧ 2 ≤ D ∧ (D : ℝ) ≤ (N : ℝ) ^ ε ∧ B₂.set.card ≤ g' ∧ B₃.set.card ≤ g' ∧
    ((probes S₁ (rowsMap (rows.drop q)) B₂ B₃).card : ℝ) ≤ 8 * (n : ℝ) ^ 2 / σ ∧
    C.IsLop N D ∧
    C.W.card = ((probes S₁ (rowsMap (rows.drop q)) B₂ B₃).image (pos H)).card ∧
    (C.W.card : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt D ∧
    (∀ Q ∈ probes S₁ (rowsMap (rows.drop q)) B₂ B₃,
      posNum B₂ B₃ H Q ∈ C.queries ∧
      (C.AcceptsAt (posNum B₂ B₃ H Q).1 (posNum B₂ B₃ H Q).2 ↔
        0 < (probeCands d (rows.drop q).length).cnt (rowsMap (rows.take q)) Q)) ∧
    (oneHashYesNum S₁ S₂ S₃ (rowsMap (rows.drop q)) B₂ B₃ g' H ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) := by
  intro H N C
  -- the parameters of §3.2
  have hop := oneHash_params ε γ hε hε2 hγ hγ2 n hn
  dsimp only at hop
  rw [← hq] at hop
  rw [← hD] at hop
  rw [← hg] at hop
  rw [← hσ] at hop
  rw [← hg'] at hop
  obtain ⟨hq1, -, hDn, -, -, hσ1, hσD, -, -, hnσ1, -, hDN, h9, -⟩ := hop
  have hσR : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  have hσ0 : 0 < σ := hσ1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  -- `k ≥ 1`: `σ² ≤ D ≤ n^ε ≤ n` and `n ≥ 4` give `σ < n`
  have hε1 : (2 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  have hn4 : (4 : ℝ) ≤ n := by
    have : (2 : ℝ) ^ (2 : ℝ) ≤ (2 : ℝ) ^ (1 / ε) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hε1
    rw [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num] at this
    linarith
  have hσ2 : (σ : ℝ) ^ 2 ≤ n := by
    have h1 : (σ : ℝ) ^ 2 ≤ D := by
      have := pow_le_pow_left₀ (by linarith) hσD 2
      rwa [Real.sq_sqrt (Nat.cast_nonneg _)] at this
    have h2 : (n : ℝ) ^ ε ≤ n := by
      have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ n)
        (by linarith : ε ≤ 1)
      rwa [Real.rpow_one] at this
    linarith
  have hσn : (σ : ℝ) < n := by nlinarith
  have hnσ : (1 : ℝ) < n / σ := by rw [one_lt_div (by linarith)]; exact hσn
  have hk1 : 1 ≤ k := by
    rw [hk]; exact Nat.ceil_pos.2 (Real.logb_pos (by norm_num) hnσ)
  obtain ⟨h2k, h2k'⟩ := ceil_logb_spec _ hnσ1
  rw [← hk] at h2k h2k'
  -- the row lists
  have hdrop : (rows.drop q).length = k := by rw [List.length_drop]; omega
  have htake : (rows.take q).length = q := by rw [List.length_take]; omega
  have hlt : q < rows.length := by omega
  have hZ := (oneHash_bounds S₁ S₂ S₃ n σ q hσ0 h₁ h₂ h₃ E rows hq1 hlt hE hgr
    (by rw [show rows.length - q = k by omega]; exact h2k)).2.1
  have h2kd : (2 : ℝ) ^ (rows.drop q).length < 2 * n / σ := by
    rw [hdrop, show (2 : ℝ) * n / σ = 2 * (n / σ) by ring]; exact h2k'
  have hP0 := (probes_card_le S₁ S₂ S₃ (rowsMap (rows.drop q)) n σ hσ0 B₂ B₃ h₁ h₂ h₃ h2kd hZ).2
  -- at most `g'` blocks per list
  have hset : ∀ {S : Finset (Vec d)} (Bl : Blocking S (rowsMap (rows.drop q)) σ), S.card ≤ n →
      Bl.set.card ≤ g' := by
    intro S Bl hS
    have h1 := Bl.card_set_le hσ0
    have h2 : (S.card : ℝ) / σ ≤ n / σ :=
      div_le_div_of_nonneg_right (by exact_mod_cast hS) (by linarith)
    have h3 : (3 : ℝ) * n / σ ≤ g' := by rw [hg']; exact Nat.le_ceil _
    have h4 : (2 : ℝ) ^ (rows.drop q).length + n / σ < 3 * n / σ := by
      have : (2 : ℝ) * n / σ + n / σ = 3 * n / σ := by ring
      linarith
    have : (Bl.set.card : ℝ) < g' := by linarith
    exact_mod_cast this.le
  have hg₂ := hset B₂ h₂
  have hg₃ := hset B₃ h₃
  -- the generic facts on the call
  obtain ⟨hlop, hWc, hqs, hans⟩ := detectCall_spec (S₁ := S₁) B₂ B₃ g' H (by omega) hg₂ hg₃
    (probes S₁ (rowsMap (rows.drop q)) B₂ B₃) subset_rfl
  have hD2 : 2 ≤ D := by
    rw [hD]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq1
  have hWle : (C.W.card : ℝ) ≤ (N : ℝ) ^ 2 / Real.sqrt D := by
    have h1 : (C.W.card : ℝ) ≤ (probes S₁ (rowsMap (rows.drop q)) B₂ B₃).card := by
      rw [hWc]; exact_mod_cast Finset.card_image_le
    have h2 : 8 * (n : ℝ) ^ 2 / σ ≤ 9 * n ^ 2 / σ :=
      div_le_div_of_nonneg_right (by nlinarith) (by linarith)
    linarith
  refine ⟨hk1, hD2, hDN, hg₂, hg₃, hP0, ?_, hWc, hWle, fun Q hQ => ⟨hqs Q hQ, ?_⟩,
    xor_direct_detection_correct_num S₁ S₂ S₃ _ B₂ B₃ g' H (by omega) hg₂ hg₃⟩
  · obtain ⟨a, b, c⟩ := hlop
    have e : g' * 2 ^ (((rows.take q).length + 1) / 2) = N := by
      show _ = g' * 2 ^ ((q + 1) / 2); rw [htake]
    refine ⟨a.trans e, b.trans e, c.trans (le_of_eq ?_)⟩
    rw [hD, ← rows_split, htake]
  · rw [← cnt_splitMap]; exact hans Q hQ

end Xor.Improved

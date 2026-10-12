import GroupLean.ExpP2L
import GroupLean.FpBounds
import GroupLean.ExpP2Split
import GroupLean.ExpP2Reduce

/-!
# Theorem 19.17 (exponent `p²`, Theorem G): correctness and counts, composed

The paper's Section 19.6 ("exponent p²"). The oracle is represented by its exact answer
(`OneHash.oneHashYes`: a probe is flagged iff the support instance accepts its position, and a
flagged probe is scanned); running times are not formalised.

* `LRun`, `HRun`: one run of the Case-L / Case-H algorithm on a sub-instance: greedy rows
  (residue rows and pair rows for Case L, lifted rows for Case H), blockings for `π`,
  representatives. Runs exist (`LRun.nonempty`, `HRun.nonempty`).
* `caseL_run`, `caseH_run`: every run answers YES iff the sub-instance has a solution, makes one
  detection call (`|W| ≤ N²/√D` with `N = g′p^{q₁}`, `g′ = ⌈(p+5)n/σ⌉`, `q₁ = ⌈q/2⌉`), and has
  `F ≤ e(3e+1)σn²/D` (Case L) or `F ≤ e(2+e)σn²/D` (Case H) false positives and at most
  `(p+1)n/σ ≤ g′` blocks per list.
* `theoremG`: the sub-instances number `7 + (⌊log₂ n⌋+1)³`, every triple lies in exactly one,
  each is in Case L or Case H, and the algorithm (one run per sub-instance, OR of the answers)
  answers YES iff a solution exists.
* `theoremG_group`: the same for lists in `∏ ℤ_{m_i}`, `m_i ∣ p²`, through the injective
  embedding into `ℤ_{p²}^r`.
-/

set_option linter.unusedSectionVars false

namespace GroupLean
namespace TheoremG

open Finset ExpP2 OneHash CaseL FpBounds ExpP2Split ExpP2Reduce

variable {p : ℕ} [Fact p.Prime] {d : ℕ}

/-- A sub-instance: three lists of `R^d`. -/
abbrev Sub (p d : ℕ) := Finset (Vp p d) × Finset (Vp p d) × Finset (Vp p d)

/-- The block slots `g′ = ⌈(p+5)n/σ⌉`. -/
noncomputable def gslots (p n σ : ℕ) : ℕ := ⌈((p : ℝ) + 5) * n / σ⌉₊

/-- `N = g′ p^{q₁}`, `q₁ = ⌈q/2⌉`: the number of vertices per side. -/
noncomputable def Nverts (p n σ q : ℕ) : ℝ := (gslots p n σ : ℝ) * (p : ℝ) ^ ((q + 1) / 2)

/-! ### Case L runs -/

/-- One run of the Case-L algorithm on `U`. -/
structure LRun (U : Sub p d) (σ k q : ℕ) (E : Multiset (VecP p d)) where
  rs : List (VecP p d)
  prs : List (VecP p d × VecP p d)
  hrs : rs.length = k + q
  hgr : IsGreedy E (survII U.1 U.2.1 U.2.2) rs
  hprs : prs.length = q
  hgp : IsGreedyL (E ×ˢ E) (Psi U.1 U.2.1 U.2.2 rs q) prs
  B₂ : Blocking U.2.1 (piLL (rs.drop q) prs) σ
  B₃ : Blocking U.2.2 (piLL (rs.drop q) prs) σ
  zr : Finset (Vp p d) → Vp p d

theorem LRun.nonempty (U : Sub p d) (σ k q : ℕ) (hσ : 0 < σ) (E : Multiset (VecP p d))
    (hE : E ≠ 0) : Nonempty (LRun U σ k q E) := by
  set rs := greedyRows E (survII U.1 U.2.1 U.2.2) (k + q)
  have hEE : E ×ˢ E ≠ 0 := by
    intro h
    have := congrArg Multiset.card h
    rw [Multiset.card_product, Multiset.card_zero] at this
    have hE0 : 0 < E.card := Multiset.card_pos.mpr hE
    exact (Nat.mul_pos hE0 hE0).ne' this
  obtain ⟨prs, hl, hg⟩ := exists_isGreedyL (E ×ˢ E) hEE (Psi U.1 U.2.1 U.2.2 rs q) q
  exact ⟨⟨rs, prs, greedyRows_length _ _ _, isGreedy_greedyRows E hE _ _, hl, hg,
    Classical.choice (Blocking.exists _ _ σ hσ), Classical.choice (Blocking.exists _ _ σ hσ),
    fun _ => 0⟩⟩

/-- The answer of a Case-L run: the exact answer of the one detection call, followed by the
scans (`oneHashYes`). -/
def LRun.yes {U : Sub p d} {σ k q : ℕ} {E : Multiset (VecP p d)} (r : LRun U σ k q E) : Prop :=
  oneHashYes U.1 r.B₂ r.B₃ (KLL (r.rs.drop q) r.prs) r.zr Finset.univ

/-- The query positions `W` of a Case-L run. -/
def LRun.W {U : Sub p d} {σ k q : ℕ} {E : Multiset (VecP p d)} (r : LRun U σ k q E) :=
  (probes U.1 r.B₂ r.B₃).image (posn (KLL (r.rs.drop q) r.prs) r.zr)

/-! ### Case H runs -/

/-- One run of the Case-H algorithm on `U` (with `k′` grouping rows). -/
structure HRun (U : Sub p d) (σ k q : ℕ) (E : Multiset (VecP p d)) where
  rows : List (VecP p d)
  hlen : rows.length = k + q
  hg : IsGreedy E (Sp U.1 U.2.1 U.2.2) rows
  B₂ : Blocking U.2.1 (piHL (rows.drop q)) σ
  B₃ : Blocking U.2.2 (piHL (rows.drop q)) σ
  zr : Finset (Vp p d) → Vp p d

theorem HRun.nonempty (U : Sub p d) (σ k q : ℕ) (hσ : 0 < σ) (E : Multiset (VecP p d))
    (hE : E ≠ 0) : Nonempty (HRun U σ k q E) :=
  ⟨⟨greedyRows E (Sp U.1 U.2.1 U.2.2) (k + q), greedyRows_length _ _ _,
    isGreedy_greedyRows E hE _ _, Classical.choice (Blocking.exists _ _ σ hσ),
    Classical.choice (Blocking.exists _ _ σ hσ), fun _ => 0⟩⟩

def HRun.yes {U : Sub p d} {σ k q : ℕ} {E : Multiset (VecP p d)} (r : HRun U σ k q E) : Prop :=
  oneHashYes U.1 r.B₂ r.B₃ (piHL r.rows) r.zr Finset.univ

def HRun.W {U : Sub p d} {σ k q : ℕ} {E : Multiset (VecP p d)} (r : HRun U σ k q E) :=
  (probes U.1 r.B₂ r.B₃).image (posn (piHL r.rows) r.zr)

/-! ### The parameters -/

/-- The parameters of Theorem 19.17 that the proofs use: `1 ≤ σ ≤ n`, `q ≥ 1`, `σ² ≤ D = p^q`,
`n/σ ≤ p^{k+q} < pn/σ` (`κ = k + q`), and `E` `β₀`-value-biased with `β₀ = 1/(2r₀)`,
`r₀ = ⌈log_p n⌉ + q + 1`. -/
structure Params (p d n σ k q : ℕ) (E : Multiset (VecP p d)) : Prop where
  hσ : 1 ≤ σ
  hσn : σ ≤ n
  hq : 1 ≤ q
  hσD : (σ : ℝ) ^ 2 ≤ (p : ℝ) ^ q
  hκ : (n : ℝ) / σ ≤ (p : ℝ) ^ (k + q)
  hκ' : (p : ℝ) ^ (k + q) < p * n / σ
  hE : IsValBiased (beta0 p n q) E

theorem gslots_ge (p n σ : ℕ) : ((p : ℝ) + 5) * n / σ ≤ gslots p n σ := Nat.le_ceil _

theorem q_le_two_q₁ (q : ℕ) : q ≤ 2 * ((q + 1) / 2) := by omega

/-! ### Lemma 19.21 for a run -/

theorem card_W_le {G P M₁ M₂ : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup P]
    [DecidableEq P] [AddCommGroup M₁] [AddCommGroup M₂] [DecidableEq M₁] [DecidableEq M₂]
    {S₁ S₂ S₃ : Finset G} {π : G →+ P} {σ : ℕ} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    (K : G →+ M₁ × M₂) (zr : Finset G → G) :
    ((probes S₁ B₂ B₃).image (posn K zr)).card ≤ (probes S₁ B₂ B₃).card :=
  Finset.card_image_le

/-- **Lemma 19.21 (Case L) for a run**: correct, one call, `F ≤ e(3e+1)σn²/D`, at most
`(p+1)n/σ` blocks per list. -/
theorem caseL_run (U : Sub p d) (n σ k q : ℕ) (E : Multiset (VecP p d))
    (hP : Params p d n σ k q E) (h₁ : U.1.card ≤ n) (h₂ : U.2.1.card ≤ n) (h₃ : U.2.2.card ≤ n)
    (hL : CaseL n σ U) (r : LRun U σ k q E) :
    (r.yes ↔ ∃ x₁ ∈ U.1, ∃ x₂ ∈ U.2.1, ∃ x₃ ∈ U.2.2, x₁ + x₂ + x₃ = 0) ∧
    (r.W.card : ℝ) ≤ Nverts p n σ q ^ 2 / Real.sqrt ((p : ℝ) ^ q) ∧
    (F (probes U.1 r.B₂ r.B₃) (KLL (r.rs.drop q) r.prs) : ℝ) ≤
      Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2 / (p : ℝ) ^ q ∧
    (r.B₂.blocks.card : ℝ) ≤ gslots p n σ ∧ (r.B₃.blocks.card : ℝ) ≤ gslots p n σ := by
  have hσ0 : 0 < σ := hP.hσ
  have hq0 : 0 < q := hP.hq
  have hTI : ((TIset U.1 U.2.1 U.2.2).card : ℝ) ≤ σ * n ^ 2 := by
    have h : (TIset U.1 U.2.1 U.2.2).card ≤ σ * n ^ 2 := hL
    exact_mod_cast h
  have hβ : beta0 p n q ≤ 1 / ((k : ℝ) + q) := by
    have := beta0_le_inv_kappa (q := q) (Fact.out : p.Prime).two_le hP.hσ hP.hκ' (by omega)
    push_cast at this
    exact this
  obtain ⟨hc, -, hF, -, hN, hb₂, hb₃⟩ := caseL U.1 U.2.1 U.2.2 n σ k q hσ0 hq0 h₁ h₂ h₃ hTI
    hP.hκ hP.hκ' hP.hσD hP.hE (beta0_nonneg p n q) hβ (two_q_beta0_le_one p n q)
    r.rs r.hrs r.hgr r.prs r.hprs r.hgp r.B₂ r.B₃ r.zr
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ0
  have hg := gslots_ge p n σ
  have hpn : (p : ℝ) * n / σ + n / σ ≤ ((p : ℝ) + 5) * n / σ := by
    rw [← add_div, div_le_div_iff_of_pos_right hσR]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  have he : ((p : ℝ) + 1) * n / σ = p * n / σ + n / σ := by ring
  refine ⟨hc, ?_, hF, by linarith, by linarith⟩
  refine (Nat.cast_le.2 (card_W_le r.B₂ r.B₃ _ r.zr)).trans ?_
  exact hN _ _ hg (q_le_two_q₁ q)

/-! ### Lemma 19.24 and Case H's instance for a run -/

/-- **Case H for a run** (with `s ≤ n`, `σ < 2s`, `s/σ ≤ p^{k′} < ps/σ`): correct, one call,
`F ≤ e(2+e)σn²/D`, at most `(p+1)n/σ` blocks per list. -/
theorem caseH_run (U : Sub p d) (n σ k q s k' : ℕ) (E : Multiset (VecP p d))
    (hP : Params p d n σ k q E) (h₁ : U.1.card ≤ n) (h₂ : U.2.1.card ≤ n) (h₃ : U.2.2.card ≤ n)
    (hTI : TI U.1 U.2.1 U.2.2 ≤ 2 * s * n ^ 2)
    (hs₂ : ∀ x ∈ U.2.1, s ≤ (cls U.2.1 x).card) (hs₃ : ∀ x ∈ U.2.2, s ≤ (cls U.2.2 x).card)
    (hsn : s ≤ n) (hsk : (s : ℝ) / σ ≤ (p : ℝ) ^ k') (hsk' : (p : ℝ) ^ k' < p * s / σ)
    (r : HRun U σ k' q E) :
    (r.yes ↔ ∃ x₁ ∈ U.1, ∃ x₂ ∈ U.2.1, ∃ x₃ ∈ U.2.2, x₁ + x₂ + x₃ = 0) ∧
    (∀ j ≤ r.rows.length, Sp U.1 U.2.1 U.2.2 (r.rows.drop j) ≤
      Real.exp 1 * (2 + Real.exp 1) * (1 / (p : ℝ) ^ (r.rows.length - j)) * s * n ^ 2) ∧
    (r.W.card : ℝ) ≤ Nverts p n σ q ^ 2 / Real.sqrt ((p : ℝ) ^ q) ∧
    (F (probes U.1 r.B₂ r.B₃) (piHL r.rows) : ℝ) ≤
      Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2 / (p : ℝ) ^ q ∧
    (r.B₂.blocks.card : ℝ) ≤ gslots p n σ ∧ (r.B₃.blocks.card : ℝ) ≤ gslots p n σ := by
  have hσ0 : 0 < σ := hP.hσ
  have hβ : beta0 p n q ≤ 1 / ((k' : ℝ) + q) := by
    have := beta0_le_inv_kprime_add_q (Fact.out : p.Prime).two_le hP.hσ hsn hsk' hP.hq
    push_cast at this
    exact this
  obtain ⟨hc, hT, -, hF, -, hN, hb₂, hb₃⟩ := caseH U.1 U.2.1 U.2.2 n σ s k' q hσ0 h₁ h₂ h₃ hTI
    hs₂ hs₃ hP.hσD hsk hsk' hP.hE.isKerBiased (beta0_nonneg p n q) hβ r.rows r.hlen r.hg
    r.B₂ r.B₃ r.zr
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ0
  have hg := gslots_ge p n σ
  have hpn : ((p : ℝ) + 1) * n / σ ≤ ((p : ℝ) + 5) * n / σ := by
    rw [div_le_div_iff_of_pos_right hσR]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  refine ⟨hc, hT, ?_, hF, by linarith, by linarith⟩
  refine (Nat.cast_le.2 (card_W_le r.B₂ r.B₃ _ r.zr)).trans ?_
  exact hN _ _ hg (q_le_two_q₁ q)

/-! ### The whole algorithm -/

/-- The Case-H parameters of a sub-instance: `s′ = min(s, n)` and `k′` with
`s′/σ ≤ p^{k′} < ps′/σ`. -/
theorem caseH_params (U : Sub p d) (n σ s : ℕ) (_hn : 1 ≤ n) (hσ : 1 ≤ σ) (hσn : σ ≤ n)
    (h₁ : U.1.card ≤ n) (h₂ : U.2.1.card ≤ n) (h₃ : U.2.2.card ≤ n) (hH : CaseH σ s U) :
    ∃ s' k' : ℕ, s' ≤ n ∧ TI U.1 U.2.1 U.2.2 ≤ 2 * s' * n ^ 2 ∧
      (∀ x ∈ U.2.1, s' ≤ (cls U.2.1 x).card) ∧ (∀ x ∈ U.2.2, s' ≤ (cls U.2.2 x).card) ∧
      (s' : ℝ) / σ ≤ (p : ℝ) ^ k' ∧ (p : ℝ) ^ k' < p * s' / σ := by
  obtain ⟨-, hσs, -, hs₂, hs₃, -⟩ := id hH
  have hσs' : σ < 2 * min s n := by
    rcases le_total s n with h | h
    · rw [min_eq_left h]; exact hσs
    · rw [min_eq_right h]; omega
  obtain ⟨k', -, hk1, hk2⟩ := exists_kprime (Fact.out : p.Prime).two_le hσ hσs'
  refine ⟨min s n, k', min_le_right _ _, ?_, fun x hx => (min_le_left _ _).trans (hs₂ x hx),
    fun x hx => (min_le_left _ _).trans (hs₃ x hx), hk1, hk2⟩
  rcases le_total s n with h | h
  · rw [min_eq_left h]; exact TI_le_of_caseH hH h₁ h₂ h₃
  · rw [min_eq_right h]
    have hT : TI U.1 U.2.1 U.2.2 ≤ U.1.card * U.2.1.card * U.2.2.card := by
      unfold TI
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, Finset.card_product, mul_assoc]
    calc TI U.1 U.2.1 U.2.2 ≤ U.1.card * U.2.1.card * U.2.2.card := hT
      _ ≤ n * n * n := Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) h₃
      _ ≤ 2 * n * n ^ 2 := by nlinarith

/-- The Case-H parameters that the proof needs for `k′`: some `s ≤ n` with `T_I ≤ 2sn²`, every
class of lists 2 and 3 of at least `s` elements, and `s/σ ≤ p^{k′} < ps/σ`. -/
def HGood (U : Sub p d) (n σ k' : ℕ) : Prop :=
  ∃ s : ℕ, s ≤ n ∧ TI U.1 U.2.1 U.2.2 ≤ 2 * s * n ^ 2 ∧
    (∀ x ∈ U.2.1, s ≤ (cls U.2.1 x).card) ∧ (∀ x ∈ U.2.2, s ≤ (cls U.2.2 x).card) ∧
    (s : ℝ) / σ ≤ (p : ℝ) ^ k' ∧ (p : ℝ) ^ k' < p * s / σ

/-- The number `k′` of grouping rows of Case H (a fixed choice satisfying `HGood` when one
exists; by `caseH_params` one exists for every Case-H sub-instance). -/
noncomputable def kH (U : Sub p d) (n σ : ℕ) : ℕ := Classical.epsilon (HGood U n σ)

/-- The answer of the algorithm on one sub-instance: a Case-L run if Case L holds, otherwise a
Case-H run with `k′ = kH U n σ` (fixed choices of the runs). -/
noncomputable def answer (U : Sub p d) (n σ k q : ℕ) (E : Multiset (VecP p d)) (hσ : 0 < σ)
    (hE : E ≠ 0) : Prop := by
  classical
  exact if CaseL n σ U then (Classical.choice (LRun.nonempty U σ k q hσ E hE)).yes
    else (Classical.choice (HRun.nonempty U σ (kH U n σ) q hσ E hE)).yes

/-- **Theorem 19.17 (exponent `p²`), correctness and counts.** For lists `S₁ S₂ S₃ ⊆ R^d`
of at most `n ≥ 1` elements and the parameters of `Params`:
(a) there are `7 + (⌊log₂ n⌋+1)³` sub-instances, every triple lies in exactly one of them, and
each is in Case L (`T_I ≤ σn²`) or in Case H;
(b) every Case-L run and every Case-H run (with `k′` as in `caseH_params`) on a sub-instance
answers YES iff the sub-instance has a solution, with one detection call (`|W| ≤ N²/√D`) and
`F ≤ e(3e+1)σn²/D`, resp. `F ≤ e(2+e)σn²/D`;
(c) the algorithm answers YES (some sub-instance answers YES) iff a solution exists. -/
theorem theoremG (S₁ S₂ S₃ : Finset (Vp p d)) (n σ k q : ℕ) (E : Multiset (VecP p d))
    (hP : Params p d n σ k q E) (hn : 1 ≤ n)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n) :
    (subInst S₁ S₂ S₃ σ n).length = 7 + (Nat.log 2 n + 1) ^ 3 ∧
    (∀ t ∈ S₁ ×ˢ S₂ ×ˢ S₃, ∃! i : Fin (subInst S₁ S₂ S₃ σ n).length,
      t ∈ ((subInst S₁ S₂ S₃ σ n).get i).1 ×ˢ ((subInst S₁ S₂ S₃ σ n).get i).2.1 ×ˢ
        ((subInst S₁ S₂ S₃ σ n).get i).2.2) ∧
    (∀ U ∈ subInst S₁ S₂ S₃ σ n,
      (CaseL n σ U ∧ ∀ r : LRun U σ k q E,
        (r.yes ↔ ∃ x₁ ∈ U.1, ∃ x₂ ∈ U.2.1, ∃ x₃ ∈ U.2.2, x₁ + x₂ + x₃ = 0) ∧
        (r.W.card : ℝ) ≤ Nverts p n σ q ^ 2 / Real.sqrt ((p : ℝ) ^ q) ∧
        (F (probes U.1 r.B₂ r.B₃) (KLL (r.rs.drop q) r.prs) : ℝ) ≤
          Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2 / (p : ℝ) ^ q) ∨
      (∃ s k' : ℕ, s ≤ n ∧ (s : ℝ) / σ ≤ (p : ℝ) ^ k' ∧ (p : ℝ) ^ k' < p * s / σ ∧
        ∀ r : HRun U σ k' q E,
        (r.yes ↔ ∃ x₁ ∈ U.1, ∃ x₂ ∈ U.2.1, ∃ x₃ ∈ U.2.2, x₁ + x₂ + x₃ = 0) ∧
        (r.W.card : ℝ) ≤ Nverts p n σ q ^ 2 / Real.sqrt ((p : ℝ) ^ q) ∧
        (F (probes U.1 r.B₂ r.B₃) (piHL r.rows) : ℝ) ≤
          Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2 / (p : ℝ) ^ q)) ∧
    ((∃ U ∈ subInst S₁ S₂ S₃ σ n, answer U n σ k q E hP.hσ hP.hE.1) ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) := by
  have hσ0 : 0 < σ := hP.hσ
  have hcards : ∀ U ∈ subInst S₁ S₂ S₃ σ n, U.1.card ≤ n ∧ U.2.1.card ≤ n ∧ U.2.2.card ≤ n := by
    intro U hU
    obtain ⟨s₁, s₂, s₃⟩ := subInst_sub U hU
    exact ⟨(Finset.card_le_card s₁).trans h₁, (Finset.card_le_card s₂).trans h₂,
      (Finset.card_le_card s₃).trans h₃⟩
  -- (b) for every sub-instance
  have hb : ∀ U ∈ subInst S₁ S₂ S₃ σ n,
      (CaseL n σ U ∧ ∀ r : LRun U σ k q E,
        (r.yes ↔ ∃ x₁ ∈ U.1, ∃ x₂ ∈ U.2.1, ∃ x₃ ∈ U.2.2, x₁ + x₂ + x₃ = 0) ∧
        (r.W.card : ℝ) ≤ Nverts p n σ q ^ 2 / Real.sqrt ((p : ℝ) ^ q) ∧
        (F (probes U.1 r.B₂ r.B₃) (KLL (r.rs.drop q) r.prs) : ℝ) ≤
          Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2 / (p : ℝ) ^ q) ∨
      (∃ s k' : ℕ, s ≤ n ∧ (s : ℝ) / σ ≤ (p : ℝ) ^ k' ∧ (p : ℝ) ^ k' < p * s / σ ∧
        ∀ r : HRun U σ k' q E,
        (r.yes ↔ ∃ x₁ ∈ U.1, ∃ x₂ ∈ U.2.1, ∃ x₃ ∈ U.2.2, x₁ + x₂ + x₃ = 0) ∧
        (r.W.card : ℝ) ≤ Nverts p n σ q ^ 2 / Real.sqrt ((p : ℝ) ^ q) ∧
        (F (probes U.1 r.B₂ r.B₃) (piHL r.rows) : ℝ) ≤
          Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2 / (p : ℝ) ^ q) := by
    intro U hU
    obtain ⟨c₁, c₂, c₃⟩ := hcards U hU
    rcases subInst_cases hσ0 h₁ h₂ h₃ U hU with hL | ⟨s, hH⟩
    · refine Or.inl ⟨hL, fun r => ?_⟩
      obtain ⟨a, b, c, -, -⟩ := caseL_run U n σ k q E hP c₁ c₂ c₃ hL r
      exact ⟨a, b, c⟩
    · obtain ⟨s', k', hs'n, hTI, hs₂, hs₃, hk1, hk2⟩ :=
        caseH_params U n σ s hn hP.hσ hP.hσn c₁ c₂ c₃ hH
      refine Or.inr ⟨s', k', hs'n, hk1, hk2, fun r => ?_⟩
      obtain ⟨a, -, b, c, -, -⟩ := caseH_run U n σ k q s' k' E hP c₁ c₂ c₃ hTI hs₂ hs₃ hs'n
        hk1 hk2 r
      exact ⟨a, b, c⟩
  refine ⟨subInst_length, fun t ht => subInst_partition h₁ h₂ h₃ t ht, hb, ?_⟩
  -- (c)
  have hU : ∀ U ∈ subInst S₁ S₂ S₃ σ n, (answer U n σ k q E hP.hσ hP.hE.1 ↔
      ∃ x₁ ∈ U.1, ∃ x₂ ∈ U.2.1, ∃ x₃ ∈ U.2.2, x₁ + x₂ + x₃ = 0) := by
    intro U hUm
    obtain ⟨c₁, c₂, c₃⟩ := hcards U hUm
    unfold answer
    split_ifs with hL
    · exact (caseL_run U n σ k q E hP c₁ c₂ c₃ hL _).1
    · rcases subInst_cases hσ0 h₁ h₂ h₃ U hUm with hL' | ⟨s, hH⟩
      · exact absurd hL' hL
      obtain ⟨s', k', hs'n, hTI, hs₂, hs₃, hk1, hk2⟩ :=
        caseH_params U n σ s hn hP.hσ hP.hσn c₁ c₂ c₃ hH
      have hgood : HGood U n σ (kH U n σ) :=
        Classical.epsilon_spec (p := HGood U n σ) ⟨k', s', hs'n, hTI, hs₂, hs₃, hk1, hk2⟩
      obtain ⟨s'', hs''n, hTI', hs₂', hs₃', hk1', hk2'⟩ := hgood
      exact (caseH_run U n σ k q s'' (kH U n σ) E hP c₁ c₂ c₃ hTI' hs₂' hs₃' hs''n hk1' hk2'
        _).1
  constructor
  · rintro ⟨U, hUm, hy⟩
    exact (exists_sol_iff_subInst h₁ h₂ h₃).2 ⟨U, hUm, (hU U hUm).1 hy⟩
  · intro hsol
    obtain ⟨U, hUm, hs⟩ := (exists_sol_iff_subInst (σ := σ) h₁ h₂ h₃).1 hsol
    exact ⟨U, hUm, (hU U hUm).2 hs⟩

/-- **Theorem 19.17 for a group given as `∏ ℤ_{m_i}`, `m_i ∣ p²`** (reduction step): the
embedding into `ℤ_{p²}^r` is injective, keeps the list sizes, and preserves and reflects
solutions; so `theoremG` applied to the images decides the original instance. -/
theorem theoremG_group {r : ℕ} {m : Fin r → ℕ} (hm : ∀ i, m i ∣ p ^ 2)
    (S₁ S₂ S₃ : Finset ((i : Fin r) → ZMod (m i))) (n σ k q : ℕ) (E : Multiset (VecP p r))
    (hP : Params p r n σ k q E) (hn : 1 ≤ n)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n) :
    ((∃ U ∈ subInst (S₁.image (embed (p ^ 2) hm)) (S₂.image (embed (p ^ 2) hm))
        (S₃.image (embed (p ^ 2) hm)) σ n, answer U n σ k q E hP.hσ hP.hE.1) ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) := by
  have hp : p.Prime := Fact.out
  rw [exists_triple_iff_embedP2 hp hm]
  exact (theoremG _ _ _ n σ k q E hP hn (by rwa [card_image_embedP2 hp hm])
    (by rwa [card_image_embedP2 hp hm]) (by rwa [card_image_embedP2 hp hm])).2.2.2

end TheoremG
end GroupLean

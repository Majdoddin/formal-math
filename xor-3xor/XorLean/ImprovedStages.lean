import XorLean.Basic

/-!
# Improved 3XOR (the improved write-up; see the README): the staged algorithm

The algorithm of §4.5 and its analysis (Lemmas II.4 and II.5) depend on the probes only through
two facts: every probe `Q` carries a finite family of vectors (`x₁ ⊕ x₂ ⊕ x₃` for
`(x₂, x₃) ∈ b₂ × b₃`), and `cnt_H(Q)` counts the members that `H` sends to `0`. The same holds
for the incidences `(a, b, k)` of §5 (the vectors `S(a, b, c)`, `c ∈ C_k`). This file states and
proves the stages once for such *candidates*; `ImprovedProbes.lean` and `ImprovedTriangle.lean`
instantiate them.

Conventions as in the rest of `XorLean`: rows are a list,
newest first, so the text's `(H, u)` (the rows of `H` followed by `u`) is `u :: H`.
-/

set_option linter.unusedSectionVars false

namespace Xor.Improved
open Xor Finset

/-- Candidates (the probes of §4.3, the incidences of §5): each candidate `x` carries a finite
family `fam x` of indices and a vector `vec x j` for each index. -/
structure Cands (X ι : Type*) (d : ℕ) where
  fam : X → Finset ι
  vec : X → ι → Vec d

namespace Cands
variable {X ι : Type*} {d : ℕ} (C : Cands X ι d)

/-- `cnt_H(x)`: the members of the family of `x` that `H` sends to `0`. -/
def cnt {m : ℕ} (H : Vec d →ₗ[ZMod 2] Vec m) (x : X) : ℕ :=
  ((C.fam x).filter fun j => H (C.vec x j) = 0).card

/-- `z(x)`: the members of the family of `x` that are `0` (the solutions in `x`). -/
def z (x : X) : ℕ := ((C.fam x).filter fun j => C.vec x j = 0).card

/-- `f_H(x)`: the false positives of `x` under `H`. -/
def fp {m : ℕ} (H : Vec d →ₗ[ZMod 2] Vec m) (x : X) : ℕ :=
  ((C.fam x).filter fun j => C.vec x j ≠ 0 ∧ H (C.vec x j) = 0).card

/-- `F_𝒫(H)`: the false positives over a set of candidates. -/
def F {m : ℕ} (P : Finset X) (H : Vec d →ₗ[ZMod 2] Vec m) : ℕ := ∑ x ∈ P, C.fp H x

/-- `Σ(H) = Σ_{x ∈ 𝒫} cnt_H(x)` as a function of the rows: the quantity that step 2(b)
minimizes (the oracle supplies it, Lemma II.2). -/
noncomputable def total (P : Finset X) (rows : List (Vec d)) : ℝ :=
  ∑ x ∈ P, (C.cnt (rowsMap rows) x : ℝ)

/-- The family of Lemma 5 for a set `𝒫`: the members with nonzero vector, weight `1`. -/
def fpFam (P : Finset X) : Finset (Σ _ : X, ι) :=
  (P.sigma fun x => C.fam x).filter fun p => C.vec p.1 p.2 ≠ 0

/-- The YES exit of step 2(c): `Σ_{x ∈ 𝒫} cnt_H(x) > |𝒫|/2`. -/
def exitYes {m : ℕ} (P : Finset X) (H : Vec d →ₗ[ZMod 2] Vec m) : Prop :=
  P.card < 2 * ∑ x ∈ P, C.cnt H x

/-- Step 2(d): the survivors `{x ∈ 𝒫 : cnt_H(x) > 0}`. -/
def next {m : ℕ} (P : Finset X) (H : Vec d →ₗ[ZMod 2] Vec m) : Finset X :=
  P.filter fun x => 0 < C.cnt H x

/-- The row rule of step 2(b): for every set `𝒫`, `rowsOf 𝒫` has `q` rows, each chosen from `E`
minimizing `Σ` given the earlier ones (ties broken arbitrarily). -/
def GreedyRule (E : Multiset (Vec d)) (q : ℕ) (rowsOf : Finset X → List (Vec d)) : Prop :=
  ∀ P, (rowsOf P).length = q ∧ IsGreedy E (C.total P) (rowsOf P)

open Classical in
/-- The algorithm of §4.5 with `t` stages left: `run rowsOf L 𝒫₀` is its answer. Step 2(a) is the
first test, 2(c) the second, 2(d) the recursive call; with no stage left, step 3 scans every
surviving candidate for a solution. -/
noncomputable def run (rowsOf : Finset X → List (Vec d)) : ℕ → Finset X → Bool
  | 0, P => decide (∃ x ∈ P, 0 < C.z x)
  | t + 1, P =>
    if P.card = 0 then false
    else if C.exitYes P (rowsMap (rowsOf P)) then true
    else run rowsOf t (C.next P (rowsMap (rowsOf P)))

/-- The survivor sets `𝒫_t` of the stages. -/
noncomputable def Pseq (rowsOf : Finset X → List (Vec d)) (P₀ : Finset X) : ℕ → Finset X
  | 0 => P₀
  | t + 1 => C.next (Pseq rowsOf P₀ t) (rowsMap (rowsOf (Pseq rowsOf P₀ t)))

/-! ### Counts -/

theorem cnt_eq_fp_add_z {m : ℕ} (H : Vec d →ₗ[ZMod 2] Vec m) (x : X) :
    C.cnt H x = C.fp H x + C.z x := by
  unfold cnt fp z
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : C.vec x j = 0 <;> simp [h]

theorem z_le_cnt {m : ℕ} (H : Vec d →ₗ[ZMod 2] Vec m) (x : X) : C.z x ≤ C.cnt H x := by
  rw [C.cnt_eq_fp_add_z H x]; omega

/-- `Σ_{x∈𝒫} cnt_H(x) = F_𝒫(H) + Z_𝒫`, and `Z_𝒫` does not depend on `H` (§4.6). -/
theorem sum_cnt_eq {m : ℕ} (P : Finset X) (H : Vec d →ₗ[ZMod 2] Vec m) :
    ∑ x ∈ P, C.cnt H x = C.F P H + ∑ x ∈ P, C.z x := by
  simp only [F, C.cnt_eq_fp_add_z, Finset.sum_add_distrib]

/-- `F_𝒫(∅) ≤ Σ_{x∈𝒫} |fam x|`. -/
theorem F_le_sum_card {m : ℕ} (P : Finset X) (H : Vec d →ₗ[ZMod 2] Vec m) :
    C.F P H ≤ ∑ x ∈ P, (C.fam x).card :=
  Finset.sum_le_sum fun _ _ => Finset.card_filter_le _ _

/-- The `Φ` of Lemma 5 for the family `fpFam 𝒫` is `F_𝒫`. -/
theorem surv_fpFam (P : Finset X) (rows : List (Vec d)) :
    surv (C.fpFam P) (fun p => C.vec p.1 p.2) (fun _ => 1) rows = C.F P (rowsMap rows) := by
  unfold surv fpFam F fp
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter]
  norm_cast
  rw [Finset.card_filter, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [rowsMap_eq_zero_iff]

/-- Minimizing `Σ` is minimizing `Φ = F_𝒫` (§4.6, proof of Lemma II.4). -/
theorem isGreedy_total_iff (E : Multiset (Vec d)) (P : Finset X) (rows : List (Vec d)) :
    IsGreedy E (C.total P) rows ↔
      IsGreedy E (surv (C.fpFam P) (fun p => C.vec p.1 p.2) (fun _ => 1)) rows := by
  have : C.total P = fun l => surv (C.fpFam P) (fun p => C.vec p.1 p.2) (fun _ => 1) l +
      ((∑ x ∈ P, C.z x : ℕ) : ℝ) := by
    funext l
    rw [surv_fpFam, total]
    have := C.sum_cnt_eq P (rowsMap l)
    rw [← Nat.cast_add, ← this]
    push_cast; rfl
  rw [this, isGreedy_add_const]

/-! ### Lemma II.4 (halving) -/

/-- **Lemma II.4**, for candidates whose families have at most `M` members (`M = σ²` for
probes): if the `q` rows are greedy for `Σ` from a `(1/q)`-biased `E` and `e 2^{-q} M ≤ 1/2`,
then `F_𝒫(H) ≤ |𝒫|/2`; a YES exit is correct; otherwise `|𝒫_t| ≤ |𝒫|/2`. -/
theorem halving (E : Multiset (Vec d)) (q M : ℕ) (hE : IsBiased (1 / (q : ℝ)) E) (hq : 0 < q)
    (hqM : Real.exp 1 * (2 : ℝ)⁻¹ ^ q * M ≤ 1 / 2)
    (P : Finset X) (hM : ∀ x ∈ P, (C.fam x).card ≤ M)
    (rows : List (Vec d)) (hlen : rows.length = q) (hg : IsGreedy E (C.total P) rows) :
    (C.F P (rowsMap rows) : ℝ) ≤ P.card / 2 ∧
    (C.exitYes P (rowsMap rows) → ∃ x ∈ P, 0 < C.z x) ∧
    (¬ C.exitYes P (rowsMap rows) → 2 * (C.next P (rowsMap rows)).card ≤ P.card) := by
  have hg' := (C.isGreedy_total_iff E P rows).1 hg
  have hpos : 0 < rows.length := hlen ▸ hq
  have hb := greedy_bound_exp hE (by positivity) (C.fpFam P) (fun p => C.vec p.1 p.2)
    (fun _ => 1) (fun j hj => (Finset.mem_filter.1 hj).2) (fun _ _ => zero_le_one) rows hg'
    hpos (by rw [hlen])
  rw [surv_fpFam, Finset.sum_const, nsmul_eq_mul, mul_one] at hb
  have hpow : (2 : ℝ)⁻¹ ^ rows.length = (2 : ℝ)⁻¹ ^ q := by rw [hlen]
  rw [hpow] at hb
  have hcard : (C.fpFam P).card ≤ P.card * M := by
    calc (C.fpFam P).card ≤ (P.sigma fun x => C.fam x).card := Finset.card_filter_le _ _
      _ = ∑ x ∈ P, (C.fam x).card := Finset.card_sigma _ _
      _ ≤ ∑ _x ∈ P, M := Finset.sum_le_sum hM
      _ = P.card * M := by rw [Finset.sum_const, smul_eq_mul]
  have hcardR : ((C.fpFam P).card : ℝ) ≤ P.card * M := by exact_mod_cast hcard
  have hF : (C.F P (rowsMap rows) : ℝ) ≤ P.card / 2 := by
    have h0 : 0 ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ q := by positivity
    calc (C.F P (rowsMap rows) : ℝ) ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ q * (C.fpFam P).card := hb
      _ ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ q * (P.card * M) := mul_le_mul_of_nonneg_left hcardR h0
      _ = (Real.exp 1 * (2 : ℝ)⁻¹ ^ q * M) * P.card := by ring
      _ ≤ 1 / 2 * P.card := mul_le_mul_of_nonneg_right hqM (Nat.cast_nonneg _)
      _ = P.card / 2 := by ring
  have hsum := C.sum_cnt_eq P (rowsMap rows)
  refine ⟨hF, ?_, ?_⟩
  · intro hex
    unfold exitYes at hex
    by_contra hno
    push Not at hno
    have hz : ∑ x ∈ P, C.z x = 0 :=
      Finset.sum_eq_zero fun x hx => Nat.le_zero.1 (hno x hx)
    rw [hz, add_zero] at hsum
    rw [hsum] at hex
    have : (P.card : ℝ) < 2 * (C.F P (rowsMap rows) : ℝ) := by exact_mod_cast hex
    linarith
  · intro hex
    unfold exitYes at hex
    push Not at hex
    have hnext : (C.next P (rowsMap rows)).card ≤ ∑ x ∈ P, C.cnt (rowsMap rows) x := by
      calc (C.next P (rowsMap rows)).card = ∑ _x ∈ C.next P (rowsMap rows), 1 := by simp
        _ ≤ ∑ x ∈ C.next P (rowsMap rows), C.cnt (rowsMap rows) x :=
            Finset.sum_le_sum fun x hx => (Finset.mem_filter.1 hx).2
        _ ≤ ∑ x ∈ P, C.cnt (rowsMap rows) x :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega

/-! ### Lemma II.5 (correctness) and the stage sizes -/

/-- **Lemma II.5**, abstract form: the algorithm answers YES if and only if some candidate of
`𝒫₀` contains a solution, for every number `L` of stages. -/
theorem run_iff (E : Multiset (Vec d)) (q M : ℕ) (hE : IsBiased (1 / (q : ℝ)) E) (hq : 0 < q)
    (hqM : Real.exp 1 * (2 : ℝ)⁻¹ ^ q * M ≤ 1 / 2)
    (rowsOf : Finset X → List (Vec d)) (hrule : C.GreedyRule E q rowsOf)
    (P₀ : Finset X) (hM : ∀ x ∈ P₀, (C.fam x).card ≤ M) (L : ℕ) :
    C.run rowsOf L P₀ = true ↔ ∃ x ∈ P₀, 0 < C.z x := by
  induction L generalizing P₀ with
  | zero => simp [run]
  | succ L ih =>
    obtain ⟨hlen, hg⟩ := hrule P₀
    have hh := C.halving E q M hE hq hqM P₀ hM (rowsOf P₀) hlen hg
    unfold run
    by_cases h0 : P₀.card = 0
    · rw [if_pos h0]
      rw [Finset.card_eq_zero] at h0
      simp [h0]
    rw [if_neg h0]
    by_cases hex : C.exitYes P₀ (rowsMap (rowsOf P₀))
    · rw [if_pos hex]
      simpa using hh.2.1 hex
    rw [if_neg hex]
    rw [ih (C.next P₀ (rowsMap (rowsOf P₀)))
      (fun x hx => hM x (Finset.mem_filter.1 hx).1)]
    constructor
    · rintro ⟨x, hx, hz⟩
      exact ⟨x, (Finset.mem_filter.1 hx).1, hz⟩
    · rintro ⟨x, hx, hz⟩
      exact ⟨x, Finset.mem_filter.2 ⟨hx, lt_of_lt_of_le hz (C.z_le_cnt _ x)⟩, hz⟩

/-- The halving across stages (cost item (iii)): as long as no stage exits with YES,
`2^t |𝒫_t| ≤ |𝒫₀|`. This needs neither the bias nor the greedy choice: the survivors carry a
positive count each, and a stage without YES exit has `Σ cnt ≤ |𝒫|/2`. The greedy choice from the
biased set serves the soundness of the YES exit (`halving`, used by `run_iff`). -/
theorem Pseq_card_le (rowsOf : Finset X → List (Vec d)) (P₀ : Finset X) (t : ℕ)
    (hno : ∀ s < t, ¬ C.exitYes (C.Pseq rowsOf P₀ s) (rowsMap (rowsOf (C.Pseq rowsOf P₀ s)))) :
    2 ^ t * (C.Pseq rowsOf P₀ t).card ≤ P₀.card := by
  have hnext : ∀ (P : Finset X) {m : ℕ} (H : Vec d →ₗ[ZMod 2] Vec m), ¬ C.exitYes P H →
      2 * (C.next P H).card ≤ P.card := by
    intro P m H hex
    unfold exitYes at hex
    push Not at hex
    have : (C.next P H).card ≤ ∑ x ∈ P, C.cnt H x := by
      calc (C.next P H).card = ∑ _x ∈ C.next P H, 1 := by simp
        _ ≤ ∑ x ∈ C.next P H, C.cnt H x :=
            Finset.sum_le_sum fun x hx => (Finset.mem_filter.1 hx).2
        _ ≤ ∑ x ∈ P, C.cnt H x := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega
  induction t with
  | zero => simp [Pseq]
  | succ t ih =>
    have ih := ih fun s hs => hno s (by omega)
    have h2 := hnext _ _ (hno t (by omega))
    have : C.Pseq rowsOf P₀ (t + 1) =
        C.next (C.Pseq rowsOf P₀ t) (rowsMap (rowsOf (C.Pseq rowsOf P₀ t))) := rfl
    rw [this, pow_succ]
    calc 2 ^ t * 2 * (C.next (C.Pseq rowsOf P₀ t) (rowsMap (rowsOf (C.Pseq rowsOf P₀ t)))).card
        = 2 ^ t * (2 * (C.next (C.Pseq rowsOf P₀ t)
            (rowsMap (rowsOf (C.Pseq rowsOf P₀ t)))).card) := by ring
      _ ≤ 2 ^ t * (C.Pseq rowsOf P₀ t).card := Nat.mul_le_mul_left _ h2
      _ ≤ P₀.card := ih

/-- When no stage exits early, the answer is the scan of `𝒫_L` (step 3). -/
theorem run_eq_scan (rowsOf : Finset X → List (Vec d)) (P₀ : Finset X) (L : ℕ)
    (hno : ∀ s < L, (C.Pseq rowsOf P₀ s).card ≠ 0 ∧
      ¬ C.exitYes (C.Pseq rowsOf P₀ s) (rowsMap (rowsOf (C.Pseq rowsOf P₀ s)))) :
    C.run rowsOf L P₀ = true ↔ ∃ x ∈ C.Pseq rowsOf P₀ L, 0 < C.z x := by
  have hshift : ∀ (P : Finset X) (t : ℕ), C.Pseq rowsOf P (t + 1) =
      C.Pseq rowsOf (C.next P (rowsMap (rowsOf P))) t := by
    intro P t
    induction t with
    | zero => rfl
    | succ t ih =>
      change C.next (C.Pseq rowsOf P (t + 1)) (rowsMap (rowsOf (C.Pseq rowsOf P (t + 1)))) = _
      rw [ih]; rfl
  induction L generalizing P₀ with
  | zero => simp [run, Pseq]
  | succ L ih =>
    have h0 : P₀.card ≠ 0 := (hno 0 (by omega)).1
    have hex : ¬ C.exitYes P₀ (rowsMap (rowsOf P₀)) := (hno 0 (by omega)).2
    unfold run
    rw [if_neg h0, if_neg hex, hshift]
    refine ih _ fun s hs => ?_
    rw [← hshift]
    exact hno (s + 1) (by omega)

/-- The row rule is satisfiable: the argmin recursion `greedyRows` of `Basic.lean`. -/
theorem greedyRule_greedyRows (E : Multiset (Vec d)) (hE : E ≠ 0) (q : ℕ) :
    C.GreedyRule E q (fun P => greedyRows E (C.total P) q) :=
  fun _ => ⟨greedyRows_length _ _ _, isGreedy_greedyRows E hE _ _⟩

end Cands

/-! ### The search version (§4.7) -/

/-- Keep a half that answers YES: `findOne dec f l` halves the list `f` times. -/
def findOne {α : Type*} (dec : List α → Bool) : ℕ → List α → Option α
  | 0, l => l.head?
  | f + 1, l =>
    if l.length ≤ 1 then l.head?
    else if dec (l.take (l.length / 2)) then findOne dec f (l.take (l.length / 2))
    else findOne dec f (l.drop (l.length / 2))

/-- The search version: if `dec` answers, for every list, whether it contains a good element
(for 3XOR: a vector `x₁` that lies in a solution), then `f ≥ ⌈log₂ |l|⌉` halvings, one call of
`dec` each, return a good element of `l` when there is one. -/
theorem findOne_spec {α : Type*} (dec : List α → Bool) (good : α → Prop)
    (hdec : ∀ l, dec l = true ↔ ∃ x ∈ l, good x) (f : ℕ) (l : List α) (hf : l.length ≤ 2 ^ f)
    (hl : ∃ x ∈ l, good x) : ∃ x ∈ l, findOne dec f l = some x ∧ good x := by
  induction f generalizing l with
  | zero =>
    obtain ⟨x, hx, hgx⟩ := hl
    match l, hf, hx with
    | [a], _, hx =>
      rw [List.mem_singleton] at hx
      subst hx
      exact ⟨x, List.mem_singleton_self _, rfl, hgx⟩
    | a :: b :: t, hf, _ => simp at hf
  | succ f ih =>
    unfold findOne
    by_cases h1 : l.length ≤ 1
    · rw [if_pos h1]
      obtain ⟨x, hx, hgx⟩ := hl
      match l, h1, hx with
      | [a], _, hx =>
        rw [List.mem_singleton] at hx
        subst hx
        exact ⟨x, List.mem_singleton_self _, rfl, hgx⟩
      | a :: b :: t, h1, _ => simp at h1
    rw [if_neg h1]
    have hlen2 : l.length / 2 ≤ 2 ^ f := by rw [pow_succ] at hf; omega
    by_cases hd : dec (l.take (l.length / 2)) = true
    · rw [if_pos hd]
      obtain ⟨x, hx, hfx, hgx⟩ := ih (l.take (l.length / 2))
        (by rw [List.length_take]; omega) ((hdec _).1 hd)
      exact ⟨x, List.mem_of_mem_take hx, hfx, hgx⟩
    · rw [if_neg hd]
      have hnot : ¬ ∃ x ∈ l.take (l.length / 2), good x := fun h => hd ((hdec _).2 h)
      have hdrop : ∃ x ∈ l.drop (l.length / 2), good x := by
        obtain ⟨x, hx, hgx⟩ := hl
        rw [← List.take_append_drop (l.length / 2) l, List.mem_append] at hx
        rcases hx with hx | hx
        · exact absurd ⟨x, hx, hgx⟩ hnot
        · exact ⟨x, hx, hgx⟩
      obtain ⟨x, hx, hfx, hgx⟩ := ih (l.drop (l.length / 2))
        (by rw [List.length_drop]; rw [pow_succ] at hf; omega) hdrop
      exact ⟨x, List.mem_of_mem_drop hx, hfx, hgx⟩

end Xor.Improved

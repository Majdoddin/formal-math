import XorLean.ImprovedProbes
import XorLean.ImprovedArith

/-!
# Improved 3XOR, Theorem III (§5): Exact-XOR-Triangle and its all-edges version

Pieces `C_k` of `C` are a family `pieces : κ → Finset C`; an incidence is `(a, b, k)`; its
family is `C_k` with the vectors `S(a, b, c)`. The instance `J(H, k, ϱ, 𝒬)` is the instance
`redInst` of `Reduction.lean` (the note's Theorem 8 instance) with `H` for the hash.
-/

set_option linter.unusedSectionVars false

namespace Xor.Improved
open Xor Finset

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] {d : ℕ} {κ : Type*} [Fintype κ]

/-- The incidences as candidates: `(a, b, k)` carries `S(a, b, c)`, `c ∈ C_k`. So `cnt_H`,
`z`, `f_H` are the text's. -/
def incCands (I : TriInst A B C d) (pieces : κ → Finset C) : Cands (A × B × κ) C d where
  fam x := pieces x.2.2
  vec x c := I.S x.1 x.2.1 c

/-- The middle part of `J(H, k, ϱ, 𝒬)` has `|C_k| 2^l ≤ σ 2^l = D` vertices. -/
theorem J_mid_card (I : TriInst A B C d) {r : ℕ} (H : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r)
    (Q : Finset (A × B)) (P : Finset C) :
    (redInst I H ϱ Q P).mid.card = P.card * 2 ^ r := by
  simp [redInst, Finset.card_univ, ZMod.card]

/-- **§5, the instance `J`**: for a pair with `H w(a,b) = ϱ`, the number of common neighbours
is `cnt_H(a, b, k) = #{c ∈ C_k : H S(a,b,c) = 0}` (for each such `c` exactly one `λ` works). -/
theorem J_count (I : TriInst A B C d) {r : ℕ} (H : Vec d →ₗ[ZMod 2] Vec r) (ϱ : Vec r)
    (Q : Finset (A × B)) (pieces : κ → Finset C) (a : A) (b : B) (k : κ)
    (hab : H (I.wab a b) = ϱ) :
    (redInst I H ϱ Q (pieces k)).count a b = (incCands I pieces).cnt H (a, b, k) := by
  unfold LopInst.count Cands.cnt incCands redInst
  simp only
  have hinj : Function.Injective fun c : C => (c, H (I.wbc b c)) :=
    fun c c' h => (Prod.mk.inj h).1
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext ⟨c, w⟩
  have key : H (I.wac a c) + ϱ = H (I.wbc b c) ↔ H (I.S a b c) = 0 := by
    rw [veq_iff, TriInst.S, map_add, map_add, ← hab]
    have : H (I.wac a c) + H (I.wab a b) + H (I.wbc b c) =
        H (I.wab a b) + H (I.wbc b c) + H (I.wac a c) := by abel
    rw [this]
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨hc, h1, h2⟩
    exact ⟨c, ⟨hc, key.1 (h1.symm.trans h2)⟩, rfl, h2.symm⟩
  · rintro ⟨c', ⟨hc, h0⟩, rfl, rfl⟩
    exact ⟨hc, (key.2 h0).symm, rfl⟩

/-- **Theorem III (a), correctness**: the algorithm of §4.5 on the incidences
`ℐ₀ = A × B × [h]` (pieces covering `C`, of at most `σ` vertices; `(1/q)`-biased `E` with
`e 2^{-q} σ ≤ 1/2`; rows greedy on `Σ_x cnt_H(x)`, which the instances `J` supply by `J_count`)
answers YES iff there is a zero triangle. -/
theorem exact_xor_triangle_full_detect (I : TriInst A B C d) (pieces : κ → Finset C)
    (hcover : ∀ c, ∃ k, c ∈ pieces k) (σ q L : ℕ) (hσ : ∀ k, (pieces k).card ≤ σ)
    (E : Multiset (Vec d)) (hE : IsBiased (1 / (q : ℝ)) E) (hq : 0 < q)
    (hqσ : Real.exp 1 * (2 : ℝ)⁻¹ ^ q * σ ≤ 1 / 2)
    (rowsOf : Finset (A × B × κ) → List (Vec d))
    (hrule : (incCands I pieces).GreedyRule E q rowsOf) :
    (incCands I pieces).run rowsOf L univ = true ↔ I.HasZeroTriangle := by
  rw [(incCands I pieces).run_iff E q σ hE hq hqσ rowsOf hrule univ (fun x _ => hσ x.2.2) L]
  constructor
  · rintro ⟨x, -, hz⟩
    obtain ⟨c, hc⟩ := Finset.card_pos.1 hz
    exact ⟨x.1, x.2.1, c, (Finset.mem_filter.1 hc).2⟩
  · rintro ⟨a, b, c, h0⟩
    obtain ⟨k, hk⟩ := hcover c
    exact ⟨(a, b, k), Finset.mem_univ _, Finset.card_pos.2 ⟨c, Finset.mem_filter.2 ⟨hk, h0⟩⟩⟩

/-! ### (b) All-edges: certification -/

namespace Cands
variable {X ι : Type*} (Cs : Cands X ι d)

/-- `μ(x) = min_{u ∈ E} cnt_{(H,u)}(x)`. -/
noncomputable def mu (E : Multiset (Vec d)) (H : List (Vec d)) (x : X) : ℕ :=
  sInf {c | ∃ u ∈ E, Cs.cnt (rowsMap (u :: H)) x = c}

/-- Certified false: `μ(x) = 0`. -/
def CertFalse (E : Multiset (Vec d)) (H : List (Vec d)) (x : X) : Prop := Cs.mu E H x = 0

/-- Certified true: `2μ(x) > (1+β) cnt_H(x)`. -/
def CertTrue (β : ℝ) (E : Multiset (Vec d)) (H : List (Vec d)) (x : X) : Prop :=
  (1 + β) * (Cs.cnt (rowsMap H) x : ℝ) < 2 * (Cs.mu E H x : ℝ)

theorem mu_mem (E : Multiset (Vec d)) (hE : E ≠ 0) (H : List (Vec d)) (x : X) :
    ∃ u ∈ E, Cs.cnt (rowsMap (u :: H)) x = Cs.mu E H x := by
  obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero hE
  exact Nat.sInf_mem (s := {c | ∃ u ∈ E, Cs.cnt (rowsMap (u :: H)) x = c}) ⟨_, u, hu, rfl⟩

theorem mu_le (E : Multiset (Vec d)) (H : List (Vec d)) (x : X) (u : Vec d) (hu : u ∈ E) :
    Cs.mu E H x ≤ Cs.cnt (rowsMap (u :: H)) x :=
  Nat.sInf_le ⟨u, hu, rfl⟩

/-- A new row can only remove false positives. -/
theorem fp_cons_le (u : Vec d) (H : List (Vec d)) (x : X) :
    Cs.fp (rowsMap (u :: H)) x ≤ Cs.fp (rowsMap H) x := by
  unfold fp
  refine Finset.card_le_card fun j hj => ?_
  rw [Finset.mem_filter, rowsMap_eq_zero_iff] at hj ⊢
  exact ⟨hj.1, hj.2.1, fun w hw => hj.2.2 w (List.mem_cons_of_mem _ hw)⟩

/-- `f_{(H,u)}(x)` as the sum of Lemma 4 over the false positives under `H`. -/
theorem fp_cons_eq (u : Vec d) (H : List (Vec d)) (x : X) :
    (Cs.fp (rowsMap (u :: H)) x : ℝ) = ∑ j ∈ ((Cs.fam x).filter fun j =>
      Cs.vec x j ≠ 0 ∧ rowsMap H (Cs.vec x j) = 0) with u ⬝ᵥ Cs.vec x j = 0, (1 : ℝ) := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter]
  unfold fp
  congr 2
  apply Finset.filter_congr
  intro j _
  simp only [rowsMap_eq_zero_iff, List.mem_cons, forall_eq_or_imp]
  tauto

/-- **Lemma III.2 (i)**: a certified-false `x` has `z(x) = 0`. -/
theorem certFalse_z (β : ℝ) (E : Multiset (Vec d)) (hE : IsBiased β E) (H : List (Vec d))
    (x : X) (h : Cs.CertFalse E H x) : Cs.z x = 0 := by
  obtain ⟨u, hu, hc⟩ := Cs.mu_mem E hE.1 H x
  unfold CertFalse at h
  have := Cs.z_le_cnt (rowsMap (u :: H)) x
  omega

/-- **Lemma III.2 (ii)**: a certified-true `x` has `z(x) ≥ 1`. -/
theorem certTrue_z (β : ℝ) (E : Multiset (Vec d)) (hE : IsBiased β E) (H : List (Vec d))
    (x : X) (h : Cs.CertTrue β E H x) : 1 ≤ Cs.z x := by
  by_contra hz
  have hz0 : Cs.z x = 0 := by omega
  obtain ⟨u, hu, hsel⟩ := select_exists hE ((Cs.fam x).filter fun j =>
    Cs.vec x j ≠ 0 ∧ rowsMap H (Cs.vec x j) = 0) (Cs.vec x) (fun _ => 1)
    (fun j hj => (Finset.mem_filter.1 hj).2.1) (fun _ _ => zero_le_one)
  rw [← fp_cons_eq] at hsel
  have hfpH : (∑ j ∈ (Cs.fam x).filter (fun j => Cs.vec x j ≠ 0 ∧ rowsMap H (Cs.vec x j) = 0),
      (1 : ℝ)) = Cs.fp (rowsMap H) x := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]; rfl
  rw [hfpH] at hsel
  have hmu := Cs.mu_le E H x u hu
  have e1 := Cs.cnt_eq_fp_add_z (rowsMap (u :: H)) x
  have e2 := Cs.cnt_eq_fp_add_z (rowsMap H) x
  rw [hz0, add_zero] at e1 e2
  unfold CertTrue at h
  rw [e2] at h
  have : (Cs.mu E H x : ℝ) ≤ Cs.fp (rowsMap (u :: H)) x := by exact_mod_cast hmu.trans e1.le
  linarith

/-- **Lemma III.2 (iii)**: an uncertified `x` has `f_H(x) ≥ 1` (needs `β < 1`). -/
theorem uncert_fp (β : ℝ) (hβ : β < 1) (E : Multiset (Vec d)) (hE : IsBiased β E)
    (H : List (Vec d)) (x : X) (h1 : ¬ Cs.CertFalse E H x) (h2 : ¬ Cs.CertTrue β E H x) :
    1 ≤ Cs.fp (rowsMap H) x := by
  by_contra hf
  have hf0 : Cs.fp (rowsMap H) x = 0 := by omega
  have hall : ∀ u, Cs.cnt (rowsMap (u :: H)) x = Cs.z x := by
    intro u
    have := Cs.fp_cons_le u H x
    rw [Cs.cnt_eq_fp_add_z]; omega
  obtain ⟨u, hu, hc⟩ := Cs.mu_mem E hE.1 H x
  rw [hall] at hc
  have hcH : Cs.cnt (rowsMap H) x = Cs.z x := by rw [Cs.cnt_eq_fp_add_z, hf0, zero_add]
  rcases Nat.eq_zero_or_pos (Cs.z x) with h0 | hpos
  · exact h1 (by unfold CertFalse; omega)
  · apply h2
    unfold CertTrue
    rw [hcH, ← hc]
    have : (0 : ℝ) < Cs.z x := by exact_mod_cast hpos
    nlinarith

end Cands

/-- The state of the all-edges algorithm: the marked pairs and the incidences `ℐ_t`. -/
structure AEState (A B κ : Type*) where
  marked : Finset (A × B)
  inc : Finset (A × B × κ)

/-- The pair of an incidence. -/
def pairOf (x : A × B × κ) : A × B := (x.1, x.2.1)

open Classical in
/-- One stage of (b): `q − 1` greedy rows `H := rowsOf ℐ`, the certification round over `E`,
the marks, and `ℐ_t` := the uncertified incidences whose pair is not marked. -/
noncomputable def aeStep (I : TriInst A B C d) (pieces : κ → Finset C) (β : ℝ)
    (E : Multiset (Vec d)) (rowsOf : Finset (A × B × κ) → List (Vec d))
    (st : AEState A B κ) : AEState A B κ :=
  let H := rowsOf st.inc
  let marked' := st.marked ∪
    (st.inc.filter fun x => (incCands I pieces).CertTrue β E H x).image pairOf
  ⟨marked', st.inc.filter fun x => ¬ (incCands I pieces).CertFalse E H x ∧
    ¬ (incCands I pieces).CertTrue β E H x ∧ pairOf x ∉ marked'⟩

/-- `L` stages. -/
noncomputable def aeRun (I : TriInst A B C d) (pieces : κ → Finset C) (β : ℝ)
    (E : Multiset (Vec d)) (rowsOf : Finset (A × B × κ) → List (Vec d)) :
    ℕ → AEState A B κ → AEState A B κ
  | 0, st => st
  | t + 1, st => aeRun I pieces β E rowsOf t (aeStep I pieces β E rowsOf st)

open Classical in
/-- After the stages: scan `C_k` for every surviving incidence and mark its pair on success. -/
noncomputable def aeFinal (I : TriInst A B C d) (pieces : κ → Finset C)
    (st : AEState A B κ) : Finset (A × B) :=
  st.marked ∪ (st.inc.filter fun x => ∃ c ∈ pieces x.2.2, I.S x.1 x.2.1 c = 0).image pairOf

/-- **Lemma III.3 (halving)**: with `q − 1` rows greedy on `Σ_x cnt_H(x)` over `ℐ` (on the oracle's sums:
`aeStep_halving_oracle` in `ImprovedCallsTriangle.lean`) from a
`(1/q)`-biased `E` (`q ≥ 2`; the text has `q ≥ 3`), pieces of at most `σ` vertices and
`e 2^{-(q-1)} σ ≤ 1/2`:
`|ℐ_t| ≤ |ℐ_{t-1}|/2`. -/
theorem aeStep_halving (I : TriInst A B C d) (pieces : κ → Finset C) (σ q : ℕ)
    (hσ : ∀ k, (pieces k).card ≤ σ) (E : Multiset (Vec d)) (hE : IsBiased (1 / (q : ℝ)) E)
    (hq : 2 ≤ q) (hqσ : Real.exp 1 * (2 : ℝ)⁻¹ ^ (q - 1) * σ ≤ 1 / 2)
    (rowsOf : Finset (A × B × κ) → List (Vec d))
    (hrule : (incCands I pieces).GreedyRule E (q - 1) rowsOf) (st : AEState A B κ) :
    2 * (aeStep I pieces (1 / q) E rowsOf st).inc.card ≤ st.inc.card := by
  set Cs := incCands I pieces
  set P := st.inc
  set H := rowsOf P
  obtain ⟨hlen, hg⟩ := hrule P
  have hβ : (1 / (q : ℝ)) < 1 := by
    rw [div_lt_one (by positivity)]; exact_mod_cast (show 1 < q by omega)
  -- the survivors are uncertified, hence carry a false positive
  have hsub : (aeStep I pieces (1 / q) E rowsOf st).inc ⊆
      P.filter fun x => 1 ≤ Cs.fp (rowsMap H) x := by
    intro x hx
    simp only [aeStep, Finset.mem_filter] at hx
    exact Finset.mem_filter.2 ⟨hx.1, Cs.uncert_fp (1 / q) hβ E hE H x hx.2.1 hx.2.2.1⟩
  have hcard : (P.filter fun x => 1 ≤ Cs.fp (rowsMap H) x).card ≤ Cs.F P (rowsMap H) := by
    calc (P.filter fun x => 1 ≤ Cs.fp (rowsMap H) x).card
        = ∑ _x ∈ P.filter (fun x => 1 ≤ Cs.fp (rowsMap H) x), 1 := by simp
      _ ≤ ∑ x ∈ P.filter (fun x => 1 ≤ Cs.fp (rowsMap H) x), Cs.fp (rowsMap H) x :=
          Finset.sum_le_sum fun x hx => (Finset.mem_filter.1 hx).2
      _ ≤ Cs.F P (rowsMap H) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- Lemma 5 with `q - 1` rows
  have hg' := (Cs.isGreedy_total_iff E P H).1 hg
  have hb := greedy_bound hE (Cs.fpFam P) (fun p => Cs.vec p.1 p.2) (fun _ => 1)
    (fun j hj => (Finset.mem_filter.1 hj).2) (fun _ _ => zero_le_one) H hg'
  rw [Cs.surv_fpFam, Finset.sum_const, nsmul_eq_mul, mul_one] at hb
  have hlenR : (2 : ℝ)⁻¹ ^ H.length = (2 : ℝ)⁻¹ ^ (q - 1) := by rw [hlen]
  have hfam : ((Cs.fpFam P).card : ℝ) ≤ σ * P.card := by
    have : (Cs.fpFam P).card ≤ P.card * σ := by
      calc (Cs.fpFam P).card ≤ (P.sigma fun x => Cs.fam x).card := Finset.card_filter_le _ _
        _ = ∑ x ∈ P, (Cs.fam x).card := Finset.card_sigma _ _
        _ ≤ ∑ _x ∈ P, σ := Finset.sum_le_sum fun x _ => hσ x.2.2
        _ = P.card * σ := by rw [Finset.sum_const, smul_eq_mul]
    have : ((Cs.fpFam P).card : ℝ) ≤ P.card * σ := by exact_mod_cast this
    linarith
  have hpow : ((1 + 1 / (q : ℝ)) / 2) ^ H.length ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ (q - 1) := by
    rw [hlen, div_eq_mul_inv, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have h1 : (1 : ℝ) ≤ 1 + 1 / q := le_add_of_nonneg_right (by positivity)
    exact (pow_le_pow_right₀ h1 (Nat.sub_le q 1)).trans (one_add_inv_pow_le_exp q (by omega))
  have hF : (Cs.F P (rowsMap H) : ℝ) ≤ P.card / 2 := by
    calc (Cs.F P (rowsMap H) : ℝ) ≤ ((1 + 1 / (q : ℝ)) / 2) ^ H.length * (Cs.fpFam P).card := hb
      _ ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ (q - 1) * (σ * P.card) :=
          mul_le_mul hpow hfam (Nat.cast_nonneg _) (by positivity)
      _ = (Real.exp 1 * (2 : ℝ)⁻¹ ^ (q - 1) * σ) * P.card := by ring
      _ ≤ 1 / 2 * P.card := mul_le_mul_of_nonneg_right hqσ (Nat.cast_nonneg _)
      _ = P.card / 2 := by ring
  have h1 := Finset.card_le_card hsub
  have : (((aeStep I pieces (1 / q) E rowsOf st).inc.card : ℕ) : ℝ) ≤ P.card / 2 :=
    (Nat.cast_le.2 (h1.trans hcard)).trans hF
  have : (2 * (aeStep I pieces (1 / q) E rowsOf st).inc.card : ℝ) ≤ P.card := by linarith
  exact_mod_cast this

/-- **Lemma III.4 (correctness) and Theorem III (b)**: starting from no marks and all
incidences, after any number `L` of stages a pair is answered YES iff it lies in a zero
triangle (pieces covering `C`; any `β`-biased `E`; any row rule; `β < 1` is not needed). -/
theorem exact_xor_triangle_full_allEdges (I : TriInst A B C d) (pieces : κ → Finset C)
    (hcover : ∀ c, ∃ k, c ∈ pieces k) (β : ℝ) (E : Multiset (Vec d))
    (hE : IsBiased β E) (rowsOf : Finset (A × B × κ) → List (Vec d)) (L : ℕ) (a : A) (b : B) :
    (a, b) ∈ aeFinal I pieces (aeRun I pieces β E rowsOf L ⟨∅, univ⟩) ↔
      ∃ c, I.S a b c = 0 := by
  set Cs := incCands I pieces
  let Inv : AEState A B κ → Prop := fun st =>
    (∀ p ∈ st.marked, ∃ c, I.S p.1 p.2 c = 0) ∧
    (∀ a b c k, c ∈ pieces k → I.S a b c = 0 → (a, b) ∈ st.marked ∨ (a, b, k) ∈ st.inc)
  have hstep : ∀ st, Inv st → Inv (aeStep I pieces β E rowsOf st) := by
    rintro st ⟨hm, hz⟩
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [aeStep, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hp
      rcases hp with hp | ⟨x, ⟨-, hx⟩, rfl⟩
      · exact hm p hp
      · have := Cs.certTrue_z β E hE _ x hx
        obtain ⟨c, hc⟩ := Finset.card_pos.1 this
        exact ⟨c, (Finset.mem_filter.1 hc).2⟩
    · intro a b c k hc h0
      have hzpos : 1 ≤ Cs.z (a, b, k) :=
        Finset.card_pos.2 ⟨c, Finset.mem_filter.2 ⟨hc, h0⟩⟩
      rcases hz a b c k hc h0 with h | h
      · left
        simp only [aeStep, Finset.mem_union]
        exact Or.inl h
      · have hnf : ¬ Cs.CertFalse E (rowsOf st.inc) (a, b, k) := fun hf => by
          have := Cs.certFalse_z β E hE _ _ hf; omega
        by_cases ht : Cs.CertTrue β E (rowsOf st.inc) (a, b, k)
        · left
          simp only [aeStep, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
          exact Or.inr ⟨(a, b, k), ⟨h, ht⟩, rfl⟩
        · by_cases hmk : (a, b) ∈ (aeStep I pieces β E rowsOf st).marked
          · exact Or.inl hmk
          · right
            simp only [aeStep, Finset.mem_filter]
            exact ⟨h, hnf, ht, hmk⟩
  have hrun : ∀ L st, Inv st → Inv (aeRun I pieces β E rowsOf L st) := by
    intro L
    induction L with
    | zero => intro st h; exact h
    | succ L ih => intro st h; exact ih _ (hstep st h)
  have h0 : Inv ⟨∅, univ⟩ := ⟨by simp, fun a b c k _ _ => Or.inr (Finset.mem_univ _)⟩
  obtain ⟨hm, hz⟩ := hrun L _ h0
  constructor
  · intro hab
    simp only [aeFinal, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hab
    rcases hab with hab | ⟨x, ⟨-, c, -, hc⟩, hx⟩
    · exact hm _ hab
    · simp only [pairOf, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    obtain ⟨k, hk⟩ := hcover c
    simp only [aeFinal, Finset.mem_union, Finset.mem_image, Finset.mem_filter]
    rcases hz a b c k hk hc with h | h
    · exact Or.inl h
    · exact Or.inr ⟨(a, b, k), ⟨h, c, hk, hc⟩, rfl⟩

/-! ### Theorem I (a): the parameter block feeds the note's Theorem 8 -/

/-- **Theorem I (a), as a reduction**: with `D := ⌊N^ε⌋`, `g := ⌈D^{γ/2}⌉` and `N ≥ 16^{1/ε}`
(`0 < ε, γ ≤ 1/2`), the note's Theorem 8 (`reduction_spec`) applies: Exact-XOR-Triangle on `N`
vertices per part reduces to at most `4Ng` instances of `Lop(N, D)`, each with at most
`⌊N²/√D⌋` query pairs, with `D ≤ N^ε` (so `Hyp^det(ε, γ)` applies to each), and a zero triangle
exists iff some instance accepts a pair whose piece holds one. The times are not formalized. -/
theorem exact_xor_triangle_half_reduction (ε γ : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hγ : 0 < γ)
    (hγ2 : γ ≤ 1 / 2) (I : TriInst A B C d) (N : ℕ)
    (hA : Fintype.card A = N) (hB : Fintype.card B = N) (hC : Fintype.card C = N)
    (hN : (16 : ℝ) ^ (1 / ε) ≤ N) (rows : List (Vec d))
    (hlen : rows.length = Nat.log 2 (Nat.sqrt ⌊(N : ℝ) ^ ε⌋₊)) :
    let D := ⌊(N : ℝ) ^ ε⌋₊
    let g := ⌈(D : ℝ) ^ (γ / 2)⌉₊
    let h := rowsMap rows
    (D : ℝ) ≤ (N : ℝ) ^ ε ∧
    ∃ inst : Finset (RedIndex A B C rows.length),
      (∀ J ∈ inst, J.Q ⊆ classOf I h J.ϱ ∧
        (redInst I h J.ϱ J.Q J.P).IsLop N D ∧ J.Q.card ≤ ⌊(N : ℝ) ^ 2 / Real.sqrt D⌋₊) ∧
      inst.card ≤ 4 * N * g ∧
      (∀ J ∈ inst, ∀ J' ∈ inst, J.P ≠ J'.P → Disjoint J.P J'.P) ∧
      (∀ J ∈ inst, ∀ p : A × B, ∃! J' ∈ inst, J'.P = J.P ∧ p ∈ J'.Q) ∧
      (I.HasZeroTriangle ↔
        ∃ J ∈ inst, ∃ p ∈ J.Q, (redInst I h J.ϱ J.Q J.P).Accepts p.1 p.2 ∧
          ∃ c ∈ J.P, I.S p.1 p.2 c = 0) := by
  intro D g h
  obtain ⟨h16, hDN, hDε, hg1, -, hgs, -⟩ := partI_params ε γ hε hε2 hγ hγ2 N hN
  exact ⟨hDε, reduction_spec I N D g hA hB hC h16 hDN hg1 hgs rows hlen⟩

end Xor.Improved

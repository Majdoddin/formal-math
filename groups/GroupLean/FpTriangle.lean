import GroupLean.FpStages
import GroupLean.OneHash

/-!
# Exact Triangle over `F_p^{d'}` and its all-edges version (Theorem 21.3 of the paper)

Port of XorLean's `ImprovedTriangle.lean` (the case `p = 2`, Theorem 5.x "Exact-XOR-Triangle")
to `F_p`. Correctness and the counts the bound rests on; no running times. The oracle is
represented by its exact answer: the counts `cnt_H(x)`, which the instance `J(H, k, ϱ, 𝒬)`
supplies (`TriInst.J_count`).

Pieces `C_k` of `C` are a family `pieces : κ → Finset C`; an incidence is `(a, b, k)`; its family
is `C_k` with the vectors `S(a, b, c)` (`incCands`). The staged algorithm (`Cands.run`) and its
halving lemma are those of `FpStages.lean`.

Changes from `p = 2`, as listed in the proof of Theorem 21.3:
* the edge `(c, λ) ∼ b` of `J` is `λ = −H(w(b, c))` (over `F_2` the sign is invisible);
* the certified-true test is `p μ(x) > (1+β) cnt_H(x)` (rate `(1+β)/p` of Lemma 19.2);
* (iii) uses `p ≥ 2 > 1 + β`;
* the parameters satisfy `p^{q-2} < 2eσ ≤ p^{q-1}`.
-/

set_option linter.unusedSectionVars false

namespace GroupLean
namespace Fp
open Finset

/-- An instance of Exact Triangle over `F_p^d` (Definition 21.1 with `G = F_p^d`): weights on the
edges of the complete tripartite graph on `A, B, C`. -/
structure TriInst (A B C : Type*) (p d : ℕ) where
  wab : A → B → VecP p d
  wbc : B → C → VecP p d
  wac : A → C → VecP p d

namespace TriInst
variable {A B C : Type*} {p d : ℕ}

/-- `S(a, b, c) = w(a, b) + w(b, c) + w(a, c)`. -/
def S (I : TriInst A B C p d) (a : A) (b : B) (c : C) : VecP p d :=
  I.wab a b + I.wbc b c + I.wac a c

/-- Some triangle has `S(a, b, c) = 0`. -/
def HasZeroTriangle (I : TriInst A B C p d) : Prop := ∃ a b c, I.S a b c = 0

end TriInst

/-- The `#Lop` answer of a `Lop` instance for the pair `(a, b)`: the number of common
neighbours in the middle part. -/
noncomputable def commonNbrCount {A B V : Type*} (J : OneHash.LopInst A B V) (a : A) (b : B) :
    ℕ :=
  open Classical in (J.mid.filter fun m => J.adjA a m ∧ J.adjB m b).card

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] {p d : ℕ} {κ : Type*} [Fintype κ]

/-- The incidences as candidates (Section 21.1, "Pieces, counts and the instance for a
homomorphism"): `(a, b, k)` carries `S(a, b, c)`, `c ∈ C_k`. So `cnt_H`, `z`, `f_H` are the
text's. -/
def incCands (I : TriInst A B C p d) (pieces : κ → Finset C) : Cands (A × B × κ) C p d where
  fam x := pieces x.2.2
  vec x c := I.S x.1 x.2.1 c

namespace TriInst

/-- **The instance `J(H, k, ϱ, 𝒬)`** of `#Lop` (Section 21.1, with `Γ = F_p^r`): sides `A`,
`B`, middle part `C_k × Γ`, wanted set `𝒬`, edges `a ∼ (c, λ)` iff `λ = H(w(a, c)) + ϱ` and
`(c, λ) ∼ b` iff `λ = −H(w(b, c))`. -/
def J [NeZero p] (I : TriInst A B C p d) {r : ℕ} (H : VecP p d →ₗ[ZMod p] VecP p r)
    (ϱ : VecP p r) (Q : Finset (A × B)) (P : Finset C) : OneHash.LopInst A B (C × VecP p r) where
  mid := P ×ˢ Finset.univ
  adjA a m := m.2 = H (I.wac a m.1) + ϱ
  adjB m b := m.2 = -H (I.wbc b m.1)
  W := Q

/-- The middle part of `J(H, k, ϱ, 𝒬)` has `|C_k| p^r` vertices (`D = σ|Γ|` for `|C_k| ≤ σ`). -/
theorem J_mid_card [NeZero p] (I : TriInst A B C p d) {r : ℕ}
    (H : VecP p d →ₗ[ZMod p] VecP p r) (ϱ : VecP p r) (Q : Finset (A × B)) (P : Finset C) :
    (I.J H ϱ Q P).mid.card = P.card * p ^ r := by
  simp [J, Finset.card_univ, ZMod.card]

/-- **Section 21.1, the count of `J`**: for a pair with `H(w(a, b)) = ϱ`, the number of common
neighbours of `a` and `b` in `J(H, k, ϱ, 𝒬)` is `cnt_H(a, b, k) = #{c ∈ C_k : H(S(a,b,c)) = 0}`
(for each such `c` exactly one `λ` works). -/
theorem J_count [NeZero p] (I : TriInst A B C p d) {r : ℕ} (H : VecP p d →ₗ[ZMod p] VecP p r)
    (ϱ : VecP p r) (Q : Finset (A × B)) (pieces : κ → Finset C) (a : A) (b : B) (k : κ)
    (hab : H (I.wab a b) = ϱ) :
    commonNbrCount (I.J H ϱ Q (pieces k)) a b = (incCands I pieces).cnt H (a, b, k) := by
  unfold commonNbrCount Cands.cnt incCands J
  simp only
  have hinj : Function.Injective fun c : C => (c, -H (I.wbc b c)) :=
    fun c c' h => (Prod.mk.inj h).1
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext ⟨c, w⟩
  have key : H (I.wac a c) + ϱ = -H (I.wbc b c) ↔ H (I.S a b c) = 0 := by
    rw [eq_neg_iff_add_eq_zero, TriInst.S, map_add, map_add, ← hab]
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

end TriInst

/-- **Theorem 21.3, detection (correctness)**: the staged algorithm on the incidences
`ℐ₀ = A × B × [h]` (pieces covering `C`, of at most `σ` vertices; a `(1/q)`-kernel-biased `E`
with `e p^{-q} σ ≤ 1/2`; `q` rows per stage, each greedy on `Σ_x cnt_H(x)`, which the instances
`J` supply by `TriInst.J_count`) answers YES iff there is a zero triangle, for any number `L` of
stages. -/
theorem exact_triangle_Fp_detect (I : TriInst A B C p d) (pieces : κ → Finset C)
    (hcover : ∀ c, ∃ k, c ∈ pieces k) (σ q L : ℕ) (hσ : ∀ k, (pieces k).card ≤ σ)
    (E : Multiset (VecP p d)) (hE : IsKerBiased (1 / (q : ℝ)) E) (hq : 0 < q)
    (hqσ : Real.exp 1 * (1 / (p : ℝ) ^ q) * σ ≤ 1 / 2)
    (rowsOf : Finset (A × B × κ) → List (VecP p d))
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

/-! ### All edges: the certification (i)–(iv) of the proof of Theorem 21.3 -/

namespace Cands
variable {X ι : Type*} (Cs : Cands X ι p d)

/-- `μ(x) = min_{u ∈ E} cnt_{(H,u)}(x)`. -/
noncomputable def mu (E : Multiset (VecP p d)) (H : List (VecP p d)) (x : X) : ℕ :=
  sInf {c | ∃ u ∈ E, Cs.cnt (rowsMap (u :: H)) x = c}

/-- Certified false: `μ(x) = 0`. -/
def CertFalse (E : Multiset (VecP p d)) (H : List (VecP p d)) (x : X) : Prop := Cs.mu E H x = 0

/-- Certified true: `p μ(x) > (1+β) cnt_H(x)`. -/
def CertTrue (β : ℝ) (E : Multiset (VecP p d)) (H : List (VecP p d)) (x : X) : Prop :=
  (1 + β) * (Cs.cnt (rowsMap H) x : ℝ) < (p : ℝ) * (Cs.mu E H x : ℝ)

theorem mu_mem (E : Multiset (VecP p d)) (hE : E ≠ 0) (H : List (VecP p d)) (x : X) :
    ∃ u ∈ E, Cs.cnt (rowsMap (u :: H)) x = Cs.mu E H x := by
  obtain ⟨u, hu⟩ := Multiset.exists_mem_of_ne_zero hE
  exact Nat.sInf_mem (s := {c | ∃ u ∈ E, Cs.cnt (rowsMap (u :: H)) x = c}) ⟨_, u, hu, rfl⟩

theorem mu_le (E : Multiset (VecP p d)) (H : List (VecP p d)) (x : X) (u : VecP p d)
    (hu : u ∈ E) : Cs.mu E H x ≤ Cs.cnt (rowsMap (u :: H)) x :=
  Nat.sInf_le ⟨u, hu, rfl⟩

/-- A new row can only remove false positives. -/
theorem fp_cons_le (u : VecP p d) (H : List (VecP p d)) (x : X) :
    Cs.fp (rowsMap (u :: H)) x ≤ Cs.fp (rowsMap H) x := by
  unfold fp
  refine Finset.card_le_card fun j hj => ?_
  rw [Finset.mem_filter, rowsMap_eq_zero_iff] at hj ⊢
  exact ⟨hj.1, hj.2.1, fun w hw => hj.2.2 w (List.mem_cons_of_mem _ hw)⟩

/-- (ii) of the proof: the false positives of `x` under `(H, u)` are its false positives `c`
under `H` with `⟨u, S(a,b,c)⟩ = 0` (the sum of Lemma 19.2). -/
theorem fp_cons_eq (u : VecP p d) (H : List (VecP p d)) (x : X) :
    (Cs.fp (rowsMap (u :: H)) x : ℝ) = ∑ j ∈ ((Cs.fam x).filter fun j =>
      Cs.vec x j ≠ 0 ∧ rowsMap H (Cs.vec x j) = 0) with u ⬝ᵥ Cs.vec x j = 0, (1 : ℝ) := by
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter]
  unfold fp
  congr 2
  apply Finset.filter_congr
  intro j _
  simp only [rowsMap_eq_zero_iff, List.mem_cons, forall_eq_or_imp]
  tauto

/-- **Theorem 21.3, all edges, (i)**: `μ(x) ≥ z(x)`, so a certified-false `x` has `z(x) = 0`. -/
theorem certFalse_z (β : ℝ) (E : Multiset (VecP p d)) (hE : IsKerBiased β E)
    (H : List (VecP p d)) (x : X) (h : Cs.CertFalse E H x) : Cs.z x = 0 := by
  obtain ⟨u, hu, hc⟩ := Cs.mu_mem E hE.1 H x
  unfold CertFalse at h
  have := Cs.z_le_cnt (rowsMap (u :: H)) x
  omega

/-- **Theorem 21.3, all edges, (ii)**: a certified-true `x` (`p μ(x) > (1+β) cnt_H(x)`) has
`z(x) ≥ 1`; by Lemma 19.2 some `u ∈ E` keeps at most `(1+β)/p · f_H(x)` false positives. -/
theorem certTrue_z (β : ℝ) (hp : 0 < p) (E : Multiset (VecP p d)) (hE : IsKerBiased β E)
    (H : List (VecP p d)) (x : X) (h : Cs.CertTrue β E H x) : 1 ≤ Cs.z x := by
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
  have hmu' : (Cs.mu E H x : ℝ) ≤ Cs.fp (rowsMap (u :: H)) x := by
    exact_mod_cast hmu.trans e1.le
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hmul := mul_le_mul_of_nonneg_left (hmu'.trans hsel) hp'.le
  have hk : (p : ℝ) * ((1 + β) / p * (Cs.fp (rowsMap H) x : ℝ)) =
      (1 + β) * (Cs.fp (rowsMap H) x : ℝ) := by
    field_simp
  linarith

/-- **Theorem 21.3, all edges, (iii)**: an uncertified `x` has `f_H(x) ≥ 1` (needs `β < 1` and
`p ≥ 2`, the text's `p ≥ 2 > 1 + β`). -/
theorem uncert_fp (β : ℝ) (hβ : β < 1) (hp : 2 ≤ p) (E : Multiset (VecP p d))
    (hE : IsKerBiased β E) (H : List (VecP p d)) (x : X) (h1 : ¬ Cs.CertFalse E H x)
    (h2 : ¬ Cs.CertTrue β E H x) : 1 ≤ Cs.fp (rowsMap H) x := by
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
    have hz : (0 : ℝ) < Cs.z x := by exact_mod_cast hpos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have : 1 + β < (p : ℝ) := by linarith
    exact mul_lt_mul_of_pos_right this hz

end Cands

/-- The state of the all-edges algorithm: the marked pairs and the incidences `ℐ_t`. -/
structure AEState (A B κ : Type*) where
  marked : Finset (A × B)
  inc : Finset (A × B × κ)

/-- The pair of an incidence. -/
def pairOf (x : A × B × κ) : A × B := (x.1, x.2.1)

open Classical in
/-- One stage of the all-edges algorithm of Theorem 21.3: `q − 1` greedy rows `H := rowsOf ℐ`,
the certification round over `E`, the marks, and `ℐ_t` := the uncertified incidences whose pair
is not marked. -/
noncomputable def aeStep (I : TriInst A B C p d) (pieces : κ → Finset C) (β : ℝ)
    (E : Multiset (VecP p d)) (rowsOf : Finset (A × B × κ) → List (VecP p d))
    (st : AEState A B κ) : AEState A B κ :=
  let H := rowsOf st.inc
  let marked' := st.marked ∪
    (st.inc.filter fun x => (incCands I pieces).CertTrue β E H x).image pairOf
  ⟨marked', st.inc.filter fun x => ¬ (incCands I pieces).CertFalse E H x ∧
    ¬ (incCands I pieces).CertTrue β E H x ∧ pairOf x ∉ marked'⟩

/-- `L` stages. -/
noncomputable def aeRun (I : TriInst A B C p d) (pieces : κ → Finset C) (β : ℝ)
    (E : Multiset (VecP p d)) (rowsOf : Finset (A × B × κ) → List (VecP p d)) :
    ℕ → AEState A B κ → AEState A B κ
  | 0, st => st
  | t + 1, st => aeRun I pieces β E rowsOf t (aeStep I pieces β E rowsOf st)

open Classical in
/-- After the stages: scan `C_k` for every surviving incidence and mark its pair on success. -/
noncomputable def aeFinal (I : TriInst A B C p d) (pieces : κ → Finset C)
    (st : AEState A B κ) : Finset (A × B) :=
  st.marked ∪ (st.inc.filter fun x => ∃ c ∈ pieces x.2.2, I.S x.1 x.2.1 c = 0).image pairOf

/-- **Theorem 21.3, all edges, (iv) (halving)**: with `q − 1 ≥ 1` rows greedy on
`Σ_x cnt_H(x)` over `ℐ` from a `(1/q)`-kernel-biased `E` (Lemma 19.3 needs `1/q ≤ 1/(q−1)`),
pieces of at most `σ` vertices, `p ≥ 2` and `e p^{-(q-1)} σ ≤ 1/2`:
`|ℐ_t| ≤ F_ℐ(H) ≤ |ℐ_{t-1}|/2`. -/
theorem aeStep_halving (I : TriInst A B C p d) (pieces : κ → Finset C) (σ q : ℕ)
    (hσ : ∀ k, (pieces k).card ≤ σ) (E : Multiset (VecP p d))
    (hE : IsKerBiased (1 / (q : ℝ)) E) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hqσ : Real.exp 1 * (1 / (p : ℝ) ^ (q - 1)) * σ ≤ 1 / 2)
    (rowsOf : Finset (A × B × κ) → List (VecP p d))
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
    exact Finset.mem_filter.2 ⟨hx.1, Cs.uncert_fp (1 / q) hβ hp E hE H x hx.2.1 hx.2.2.1⟩
  have hcard : (P.filter fun x => 1 ≤ Cs.fp (rowsMap H) x).card ≤ Cs.F P (rowsMap H) := by
    calc (P.filter fun x => 1 ≤ Cs.fp (rowsMap H) x).card
        = ∑ _x ∈ P.filter (fun x => 1 ≤ Cs.fp (rowsMap H) x), 1 := by simp
      _ ≤ ∑ x ∈ P.filter (fun x => 1 ≤ Cs.fp (rowsMap H) x), Cs.fp (rowsMap H) x :=
          Finset.sum_le_sum fun x hx => (Finset.mem_filter.1 hx).2
      _ ≤ Cs.F P (rowsMap H) := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  -- Lemma 19.3 with `q - 1` rows
  have hβr : 1 / (q : ℝ) ≤ 1 / (H.length : ℝ) := by
    rw [hlen]
    apply one_div_le_one_div_of_le
    · exact_mod_cast (show 0 < q - 1 by omega)
    · exact_mod_cast Nat.sub_le q 1
  have hb := Cs.F_greedy_le E (1 / (q : ℝ)) hE (by positivity) σ P (fun x _ => hσ x.2.2) H
    (by rw [hlen]; omega) hβr hg
  have hpow : (1 / (p : ℝ) ^ H.length) = 1 / (p : ℝ) ^ (q - 1) := by rw [hlen]
  rw [hpow] at hb
  have hF : (Cs.F P (rowsMap H) : ℝ) ≤ P.card / 2 := by
    calc (Cs.F P (rowsMap H) : ℝ) ≤ Real.exp 1 * (1 / (p : ℝ) ^ (q - 1)) * σ * P.card := hb
      _ ≤ 1 / 2 * P.card := mul_le_mul_of_nonneg_right hqσ (Nat.cast_nonneg _)
      _ = P.card / 2 := by ring
  have h1 := Finset.card_le_card hsub
  have : (((aeStep I pieces (1 / q) E rowsOf st).inc.card : ℕ) : ℝ) ≤ P.card / 2 :=
    (Nat.cast_le.2 (h1.trans hcard)).trans hF
  have : (2 * (aeStep I pieces (1 / q) E rowsOf st).inc.card : ℝ) ≤ P.card := by linarith
  exact_mod_cast this

/-- The halving chained over the stages (left implicit in the text): `2^t |ℐ_t| ≤ |ℐ_0|`. -/
theorem aeRun_card_le (I : TriInst A B C p d) (pieces : κ → Finset C) (σ q : ℕ)
    (hσ : ∀ k, (pieces k).card ≤ σ) (E : Multiset (VecP p d))
    (hE : IsKerBiased (1 / (q : ℝ)) E) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hqσ : Real.exp 1 * (1 / (p : ℝ) ^ (q - 1)) * σ ≤ 1 / 2)
    (rowsOf : Finset (A × B × κ) → List (VecP p d))
    (hrule : (incCands I pieces).GreedyRule E (q - 1) rowsOf) (t : ℕ) (st : AEState A B κ) :
    2 ^ t * (aeRun I pieces (1 / q) E rowsOf t st).inc.card ≤ st.inc.card := by
  induction t generalizing st with
  | zero => simp [aeRun]
  | succ t ih =>
    have h1 := ih (aeStep I pieces (1 / q) E rowsOf st)
    have h2 := aeStep_halving I pieces σ q hσ E hE hp hq hqσ rowsOf hrule st
    change 2 ^ (t + 1) * (aeRun I pieces (1 / q) E rowsOf t
      (aeStep I pieces (1 / q) E rowsOf st)).inc.card ≤ st.inc.card
    rw [pow_succ]
    calc 2 ^ t * 2 * (aeRun I pieces (1 / q) E rowsOf t
          (aeStep I pieces (1 / q) E rowsOf st)).inc.card
        = 2 * (2 ^ t * (aeRun I pieces (1 / q) E rowsOf t
          (aeStep I pieces (1 / q) E rowsOf st)).inc.card) := by ring
      _ ≤ 2 * (aeStep I pieces (1 / q) E rowsOf st).inc.card := Nat.mul_le_mul_left _ h1
      _ ≤ st.inc.card := h2

/-- **Theorem 21.3, all edges (correctness, as in Lemma e:lem:correctB)**: starting from no
marks and all incidences, after any number `L` of stages a pair is answered YES iff it lies in a
zero triangle (pieces covering `C`; any `β`-kernel-biased `E`; any row rule; `p > 0`; neither
the greedy choice nor `β < 1` is needed). -/
theorem exact_triangle_Fp_allEdges (I : TriInst A B C p d) (pieces : κ → Finset C)
    (hcover : ∀ c, ∃ k, c ∈ pieces k) (hp : 0 < p) (β : ℝ) (E : Multiset (VecP p d))
    (hE : IsKerBiased β E) (rowsOf : Finset (A × B × κ) → List (VecP p d)) (L : ℕ)
    (a : A) (b : B) :
    (a, b) ∈ aeFinal I pieces (aeRun I pieces β E rowsOf L ⟨∅, univ⟩) ↔
      ∃ c, I.S a b c = 0 := by
  set Cs := incCands I pieces
  let Inv : AEState A B κ → Prop := fun st =>
    (∀ pr ∈ st.marked, ∃ c, I.S pr.1 pr.2 c = 0) ∧
    (∀ a b c k, c ∈ pieces k → I.S a b c = 0 → (a, b) ∈ st.marked ∨ (a, b, k) ∈ st.inc)
  have hstep : ∀ st, Inv st → Inv (aeStep I pieces β E rowsOf st) := by
    rintro st ⟨hm, hz⟩
    refine ⟨?_, ?_⟩
    · intro pr hpr
      simp only [aeStep, Finset.mem_union, Finset.mem_image, Finset.mem_filter] at hpr
      rcases hpr with hpr | ⟨x, ⟨-, hx⟩, rfl⟩
      · exact hm pr hpr
      · have := Cs.certTrue_z β hp E hE _ x hx
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

/-! ### Parameters (proof of Theorem 21.3, "Parameters") -/

/-- A `q` with `p^{q-2} < 2eσ ≤ p^{q-1}` exists for `p ≥ 2`, `σ ≥ 1` (the text's
`q = ⌈log_p(2eσ)⌉ + 1`; here `q − 1` is the least `m` with `2eσ ≤ p^m`). -/
theorem params_q_exists (p : ℕ) (hp : 2 ≤ p) (σ : ℝ) (hσ : 1 ≤ σ) :
    ∃ q : ℕ, 2 ≤ q ∧ (p : ℝ) ^ (q - 2) < 2 * Real.exp 1 * σ ∧
      2 * Real.exp 1 * σ ≤ (p : ℝ) ^ (q - 1) := by
  classical
  have h1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hex : ∃ m : ℕ, 2 * Real.exp 1 * σ ≤ (p : ℝ) ^ m :=
    (pow_unbounded_of_one_lt (2 * Real.exp 1 * σ) h1).imp fun _ h => h.le
  have hy1 : 1 < 2 * Real.exp 1 * σ := by
    have he : 1 < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
    nlinarith
  set m := Nat.find hex with hmdef
  have hm : 2 * Real.exp 1 * σ ≤ (p : ℝ) ^ m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h
    rw [h, pow_zero] at hm
    linarith
  refine ⟨m + 1, by omega, ?_, by simpa using hm⟩
  have hmin := Nat.find_min hex (show m - 1 < m by omega)
  rw [show m + 1 - 2 = m - 1 by omega]
  exact lt_of_not_ge hmin

/-- **Theorem 21.3, "Parameters"**: from `p^{q-2} < 2eσ ≤ p^{q-1}` (`p ≥ 2`, `q ≥ 2`, `σ ≥ 0`):
`p^q < 2ep²σ = Λσ`; `e p^{-q} σ ≤ 1/(2p) ≤ 1/4` (the detection bound); and
`e p^{-(q-1)} σ ≤ 1/2` (the all-edges bound, `p^{q-1} ≥ 2eσ`). -/
theorem params_bounds (p q : ℕ) (σ : ℝ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hlo : (p : ℝ) ^ (q - 2) < 2 * Real.exp 1 * σ)
    (hhi : 2 * Real.exp 1 * σ ≤ (p : ℝ) ^ (q - 1)) :
    (p : ℝ) ^ q < 2 * Real.exp 1 * (p : ℝ) ^ 2 * σ ∧
    Real.exp 1 * (1 / (p : ℝ) ^ q) * σ ≤ 1 / (2 * p) ∧
    1 / (2 * (p : ℝ)) ≤ 1 / 4 ∧
    Real.exp 1 * (1 / (p : ℝ) ^ (q - 1)) * σ ≤ 1 / 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hP1 : (0 : ℝ) < (p : ℝ) ^ (q - 1) := by positivity
  have hPq : (p : ℝ) ^ q = p * (p : ℝ) ^ (q - 1) := by
    rw [← pow_succ']; congr 1; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (p : ℝ) ^ q = (p : ℝ) ^ (q - 2) * (p : ℝ) ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [this]
    have h2 : (0 : ℝ) < (p : ℝ) ^ 2 := by positivity
    have := mul_lt_mul_of_pos_right hlo h2
    linarith
  · have hrw : Real.exp 1 * (1 / (p : ℝ) ^ q) * σ =
        (2 * Real.exp 1 * σ) * (1 / (p : ℝ) ^ q) * (1 / 2) := by ring
    have hle : (2 * Real.exp 1 * σ) * (1 / (p : ℝ) ^ q) ≤
        (p : ℝ) ^ (q - 1) * (1 / (p : ℝ) ^ q) :=
      mul_le_mul_of_nonneg_right hhi (by positivity)
    have heq : (p : ℝ) ^ (q - 1) * (1 / (p : ℝ) ^ q) = 1 / p := by
      rw [hPq]; field_simp
    have heq2 : 1 / (2 * (p : ℝ)) = 1 / p * (1 / 2) := by ring
    rw [hrw, heq2]
    nlinarith
  · apply one_div_le_one_div_of_le (by norm_num)
    linarith
  · have hrw : Real.exp 1 * (1 / (p : ℝ) ^ (q - 1)) * σ =
        (2 * Real.exp 1 * σ) * (1 / (p : ℝ) ^ (q - 1)) * (1 / 2) := by ring
    have hle : (2 * Real.exp 1 * σ) * (1 / (p : ℝ) ^ (q - 1)) ≤
        (p : ℝ) ^ (q - 1) * (1 / (p : ℝ) ^ (q - 1)) :=
      mul_le_mul_of_nonneg_right hhi (by positivity)
    have heq : (p : ℝ) ^ (q - 1) * (1 / (p : ℝ) ^ (q - 1)) = 1 := by
      field_simp
    rw [hrw]
    nlinarith

/-- For `1 ≤ l ≤ q` rows, `|Γ| = p^l ≤ p^q < Λσ` with `Λ = 2ep²` (the hypothesis
`|Γ| ≤ Λσ` of Lemma 21.2). -/
theorem params_card_Gamma (p q l : ℕ) (σ : ℝ) (hp : 2 ≤ p) (hq : 2 ≤ q) (hl : l ≤ q)
    (hlo : (p : ℝ) ^ (q - 2) < 2 * Real.exp 1 * σ)
    (hhi : 2 * Real.exp 1 * σ ≤ (p : ℝ) ^ (q - 1)) :
    (p : ℝ) ^ l < 2 * Real.exp 1 * (p : ℝ) ^ 2 * σ := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
  exact lt_of_le_of_lt (pow_le_pow_right₀ h1 hl) (params_bounds p q σ hp hq hlo hhi).1

/-- **Theorem 21.3, detection with the text's parameters**: `q` with `p^{q-2} < 2eσ ≤ p^{q-1}`,
`E` `(1/q)`-kernel-biased; then the staged algorithm is correct. -/
theorem exact_triangle_Fp_detect_params (I : TriInst A B C p d) (pieces : κ → Finset C)
    (hcover : ∀ c, ∃ k, c ∈ pieces k) (σ q L : ℕ) (hσ : ∀ k, (pieces k).card ≤ σ)
    (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hlo : (p : ℝ) ^ (q - 2) < 2 * Real.exp 1 * σ)
    (hhi : 2 * Real.exp 1 * σ ≤ (p : ℝ) ^ (q - 1))
    (E : Multiset (VecP p d)) (hE : IsKerBiased (1 / (q : ℝ)) E)
    (rowsOf : Finset (A × B × κ) → List (VecP p d))
    (hrule : (incCands I pieces).GreedyRule E q rowsOf) :
    (incCands I pieces).run rowsOf L univ = true ↔ I.HasZeroTriangle := by
  obtain ⟨-, h2, h3, -⟩ := params_bounds p q σ hp hq hlo hhi
  exact exact_triangle_Fp_detect I pieces hcover σ q L hσ E hE (by omega)
    (by linarith) rowsOf hrule

/-- **Theorem 21.3, all-edges halving with the text's parameters**: `q − 1` greedy rows per
stage give `2^t |ℐ_t| ≤ |ℐ_0|`. -/
theorem aeRun_card_le_params (I : TriInst A B C p d) (pieces : κ → Finset C) (σ q : ℕ)
    (hσ : ∀ k, (pieces k).card ≤ σ) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (hlo : (p : ℝ) ^ (q - 2) < 2 * Real.exp 1 * σ)
    (hhi : 2 * Real.exp 1 * σ ≤ (p : ℝ) ^ (q - 1))
    (E : Multiset (VecP p d)) (hE : IsKerBiased (1 / (q : ℝ)) E)
    (rowsOf : Finset (A × B × κ) → List (VecP p d))
    (hrule : (incCands I pieces).GreedyRule E (q - 1) rowsOf) (t : ℕ) (st : AEState A B κ) :
    2 ^ t * (aeRun I pieces (1 / q) E rowsOf t st).inc.card ≤ st.inc.card :=
  aeRun_card_le I pieces σ q hσ E hE hp hq (params_bounds p q σ hp hq hlo hhi).2.2.2
    rowsOf hrule t st

end Fp
end GroupLean

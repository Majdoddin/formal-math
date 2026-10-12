import GroupLean.FpStages
import GroupLean.OneHash
import GroupLean.Fourier

/-!
# Theorem 19.9 of the paper: the counting-oracle algorithm for 3SUM over `F_p^d`

Port of XorLean's `ImprovedProbes.lean` (the case `p = 2`). Correctness and the counts the bound
of Theorem 19.9 rests on; no running times. The counting oracle `#Lop` is represented by its exact
answer (`lopCount`), as in XorLean.

* the probes as candidates of the staged algorithm (`probeCands`), with `cnt` and `z` those of
  `OneHash` (Lemma 19.6);
* the choice of `π` (rows greedy on `Z` from a `(1/k)`-kernel-biased `E_k`): `Z(π) ≤ (eσ+1)n²`;
* the number of probes `|𝒫₀| ≤ (p+2+e+1/σ) n²/σ ≤ (p+6) n²/σ` and of blocks;
* the instance `I(H, 𝒫)` and its counts, with binary splitting of the entries;
* correctness of the algorithm (`fp_count_correct`, `fp_count_correct_oracle`);
* the parameters `q`, `k` ("Parameters" in the proof of Theorem 19.9).

The lists are sets `S₁ S₂ S₃ : Finset (VecP p d)` (repeated vectors removed).
-/

set_option linter.unusedSectionVars false

namespace GroupLean
namespace Fp
open Finset

variable {p d : ℕ}

/-! ### The probes as candidates -/

/-- The probes `Q = (x₁; b₂, b₃)` of Section 19.2 as candidates of the staged algorithm: `Q`
carries `x₁ + x₂ + x₃` for `(x₂, x₃) ∈ b₂ × b₃`. -/
def probeCands (p d : ℕ) : Cands (OneHash.Probe (VecP p d)) (VecP p d × VecP p d) p d where
  fam Q := Q.2.1 ×ˢ Q.2.2
  vec Q pr := Q.1 + pr.1 + pr.2

/-- `cnt_H(Q)` of the staged algorithm is `cnt_K(Q)` of Lemma 19.6 for `K = H`. -/
theorem probeCands_cnt {m : ℕ} (H : VecP p d →ₗ[ZMod p] VecP p m)
    (Q : OneHash.Probe (VecP p d)) :
    (probeCands p d).cnt H Q = OneHash.cnt H.toAddMonoidHom Q := rfl

/-- `z(Q)` of the staged algorithm is `z(Q)` of Lemma 19.6. -/
theorem probeCands_z (Q : OneHash.Probe (VecP p d)) : (probeCands p d).z Q = OneHash.z Q := rfl

/-- `cnt_∅(Q) = |b₂||b₃| ≤ σ²` for the probes of blocks of at most `σ` elements. -/
theorem probe_card_fam_le {P : Type*} [AddCommGroup P] [DecidableEq P]
    {S₁ S₂ S₃ : Finset (VecP p d)} {π : VecP p d →+ P} {σ : ℕ}
    (B₂ : OneHash.Blocking S₂ π σ) (B₃ : OneHash.Blocking S₃ π σ) :
    ∀ Q ∈ OneHash.probes S₁ B₂ B₃, ((probeCands p d).fam Q).card ≤ σ ^ 2 := by
  intro Q hQ
  have h := (OneHash.mem_probes.1 hQ).1
  simp only [probeCands, Finset.card_product, sq]
  exact Nat.mul_le_mul (B₂.card_le _ h.2.1) (B₃.card_le _ h.2.2)

/-! ### The choice of `π` -/

/-- `Z(H)` for the linear map with rows `rows`: the triples `τ ∈ S₁ × S₂ × S₃` with
`H(v(τ)) = 0`. It is `OneHash.Zc` for `K = rowsMap rows`; the algorithm evaluates it by the
Fourier identity of Lemma 19.5 (`Zrows_fourier`, from `GroupLean.fourier_count`). The exact
evaluation of that identity in `ℤ[X]/(X^m − 1)` is not formalised. -/
def Zrows (S₁ S₂ S₃ : Finset (VecP p d)) (rows : List (VecP p d)) : ℕ :=
  OneHash.Zc S₁ S₂ S₃ (rowsMap rows).toAddMonoidHom

/-- **Lemma 19.5** (the identity) for `K = rowsMap rows`, `Γ = F_p^l`:
`|Γ| Z(K) = Σ_ψ ĉ₁(ψ) ĉ₂(ψ) ĉ₃(ψ)`. -/
theorem Zrows_fourier [NeZero p] (S₁ S₂ S₃ : Finset (VecP p d)) (rows : List (VecP p d)) :
    (Fintype.card (VecP p rows.length) : ℂ) * (Zrows S₁ S₂ S₃ rows : ℂ) =
      ∑ ψ : AddChar (VecP p rows.length) ℂ,
        (∑ x ∈ S₁, ψ (rowsMap rows x)) * (∑ x ∈ S₂, ψ (rowsMap rows x)) *
          (∑ x ∈ S₃, ψ (rowsMap rows x)) := by
  rw [← fourier_count]
  congr 2
  unfold Zrows OneHash.Zc
  congr 1
  refine Finset.filter_congr fun t _ => ?_
  change rowsMap rows (t.1 + t.2.1 + t.2.2) = 0 ↔ _
  rw [map_add, map_add]

/-- The family of Lemma 19.3 for `Z`: the triples with `v(τ) ≠ 0`, weight `1`. -/
def tripFam (S₁ S₂ S₃ : Finset (VecP p d)) : Finset (VecP p d × VecP p d × VecP p d) :=
  (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => t.1 + t.2.1 + t.2.2 ≠ 0

/-- `Φ = Z − Z₀` (proof of Theorem 19.8, "The hash"). -/
theorem surv_tripFam (S₁ S₂ S₃ : Finset (VecP p d)) (rows : List (VecP p d)) :
    surv (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1) rows =
      (Zrows S₁ S₂ S₃ rows : ℝ) - OneHash.Zsol S₁ S₂ S₃ := by
  have hsplit : Zrows S₁ S₂ S₃ rows = ((tripFam S₁ S₂ S₃).filter fun t =>
      ∀ u ∈ rows, u ⬝ᵥ (t.1 + t.2.1 + t.2.2) = 0).card + OneHash.Zsol S₁ S₂ S₃ := by
    unfold Zrows OneHash.Zc OneHash.Zsol tripFam
    rw [Finset.filter_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h : t.1 + t.2.1 + t.2.2 = 0
    · simp [h]
    · rw [if_neg h, add_zero]
      refine if_congr ?_ rfl rfl
      change rowsMap rows (t.1 + t.2.1 + t.2.2) = 0 ↔ _
      rw [rowsMap_eq_zero_iff]
      exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
  unfold surv
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hsplit]
  push_cast; ring

/-- Minimising `Z` minimises `Φ`. -/
theorem isGreedy_Zrows_iff (S₁ S₂ S₃ : Finset (VecP p d)) (E : Multiset (VecP p d))
    (rows : List (VecP p d)) :
    IsGreedy E (fun l => (Zrows S₁ S₂ S₃ l : ℝ)) rows ↔
      IsGreedy E (surv (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1)) rows := by
  have : (fun l => (Zrows S₁ S₂ S₃ l : ℝ)) = fun l =>
      surv (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1) l +
        (OneHash.Zsol S₁ S₂ S₃ : ℝ) := by
    funext l
    rw [surv_tripFam]; ring
  rw [this, isGreedy_add_const]

/-- Lemmas 19.2 and 19.3 for the rows greedy on `Z`: `Z(π) − Z₀ ≤ e p^{-r} |S₁||S₂||S₃|` for
`r ≥ 1` rows from an `ε`-kernel-biased `E` with `0 ≤ ε ≤ 1/r`. -/
theorem Zrows_greedy_le (S₁ S₂ S₃ : Finset (VecP p d)) {ε : ℝ} {E : Multiset (VecP p d)}
    (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε) (rows : List (VecP p d))
    (hg : IsGreedy E (fun l => (Zrows S₁ S₂ S₃ l : ℝ)) rows)
    (hr : 0 < rows.length) (hε : ε ≤ 1 / rows.length) :
    (Zrows S₁ S₂ S₃ rows : ℝ) - OneHash.Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * (1 / (p : ℝ) ^ rows.length) * (S₁.card * S₂.card * S₃.card) := by
  have hg' := (isGreedy_Zrows_iff S₁ S₂ S₃ E rows).1 hg
  have hb := greedy_bound_exp hE hε0 (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2)
    (fun _ => 1) (fun j hj => (Finset.mem_filter.1 hj).2) (fun _ _ => zero_le_one) rows hg' hr hε
  rw [surv_tripFam, Finset.sum_const, nsmul_eq_mul, mul_one] at hb
  have hcard : ((tripFam S₁ S₂ S₃).card : ℝ) ≤ S₁.card * S₂.card * S₃.card := by
    have : (tripFam S₁ S₂ S₃).card ≤ S₁.card * S₂.card * S₃.card := by
      refine (Finset.card_filter_le _ _).trans ?_
      rw [Finset.card_product, Finset.card_product, mul_assoc]
    exact_mod_cast this
  exact hb.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

/-- **`Z(π) ≤ (eσ+1)n²`** (proof of Theorem 19.9, "Groups, blocks and probes", via Theorem 19.8,
"The hash"): with `k ≥ 1` rows greedy on `Z` from the `(1/k)`-kernel-biased `E_k`, lists of at
most `n` elements and `n/σ ≤ p^k`: `Z(π) − Z₀ ≤ eσn²` and `Z(π) ≤ (eσ+1)n²`. -/
theorem Zrows_pi_le (S₁ S₂ S₃ : Finset (VecP p d)) (n σ : ℕ) (hp : 0 < p) (hσ : 0 < σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (E : Multiset (VecP p d)) (rows : List (VecP p d)) (hk : 0 < rows.length)
    (hE : IsKerBiased (1 / (rows.length : ℝ)) E)
    (hg : IsGreedy E (fun l => (Zrows S₁ S₂ S₃ l : ℝ)) rows)
    (hpk : (n : ℝ) / σ ≤ (p : ℝ) ^ rows.length) :
    (Zrows S₁ S₂ S₃ rows : ℝ) - OneHash.Zsol S₁ S₂ S₃ ≤ Real.exp 1 * σ * n ^ 2 ∧
    (Zrows S₁ S₂ S₃ rows : ℝ) ≤ (Real.exp 1 * σ + 1) * n ^ 2 := by
  have hb := Zrows_greedy_le S₁ S₂ S₃ hE (by positivity) rows hg hk le_rfl
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpk0 : (0 : ℝ) < (p : ℝ) ^ rows.length := by positivity
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have c1 : (S₁.card : ℝ) ≤ n := by exact_mod_cast h₁
  have c2 : (S₂.card : ℝ) ≤ n := by exact_mod_cast h₂
  have c3 : (S₃.card : ℝ) ≤ n := by exact_mod_cast h₃
  have hprod : (S₁.card * S₂.card * S₃.card : ℝ) ≤ n * n * n := by
    apply mul_le_mul (mul_le_mul c1 c2 (Nat.cast_nonneg _) hn0) c3 (Nat.cast_nonneg _)
      (by positivity)
  have hpow : 1 / (p : ℝ) ^ rows.length * n ≤ σ := by
    rw [div_le_iff₀ hσR] at hpk
    rw [one_div, inv_mul_le_iff₀ hpk0]
    linarith
  have h1 : (Zrows S₁ S₂ S₃ rows : ℝ) - OneHash.Zsol S₁ S₂ S₃ ≤ Real.exp 1 * σ * n ^ 2 := by
    calc _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ rows.length) * (S₁.card * S₂.card * S₃.card) := hb
      _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ rows.length) * (n * n * n) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = Real.exp 1 * (1 / (p : ℝ) ^ rows.length * n) * n ^ 2 := by ring
      _ ≤ Real.exp 1 * σ * n ^ 2 := by gcongr
  have hZ0 : (OneHash.Zsol S₁ S₂ S₃ : ℝ) ≤ n ^ 2 := by
    have := OneHash.Zsol_le S₁ S₂ S₃
    have : (OneHash.Zsol S₁ S₂ S₃ : ℝ) ≤ S₁.card * S₂.card := by exact_mod_cast this
    nlinarith [Nat.cast_nonneg (α := ℝ) S₁.card, Nat.cast_nonneg (α := ℝ) S₂.card]
  refine ⟨h1, ?_⟩
  linarith

/-! ### The numbers of blocks and probes -/

/-- A linear `π : F_p^d → F_p^k` has at most `p^k` nonempty classes on any list. -/
theorem card_image_le_pow [NeZero p] (S : Finset (VecP p d)) {k : ℕ}
    (π : VecP p d →ₗ[ZMod p] VecP p k) : ((S.image π.toAddMonoidHom).card : ℝ) ≤ (p : ℝ) ^ k := by
  have h := Finset.card_le_univ (S.image π.toAddMonoidHom)
  have h2 : Fintype.card (VecP p k) = p ^ k := by simp [VecP, ZMod.card]
  rw [h2] at h
  exact_mod_cast h

/-- **Blocks** (proof of Theorem 19.9, "Groups, blocks and probes"): a list of at most `n`
elements has at most `p^k + n/σ` blocks. -/
theorem blocks_card_le [NeZero p] (S : Finset (VecP p d)) {k : ℕ}
    (π : VecP p d →ₗ[ZMod p] VecP p k) (n σ : ℕ) (hσ : 0 < σ) (hS : S.card ≤ n)
    (B : OneHash.Blocking S π.toAddMonoidHom σ) :
    (B.blocks.card : ℝ) ≤ (p : ℝ) ^ k + n / σ := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have h := B.card_le' hσ
  have h1 := card_image_le_pow S π
  have h2 : (S.card : ℝ) / σ ≤ n / σ :=
    div_le_div_of_nonneg_right (by exact_mod_cast hS) hσR.le
  linarith

/-- **The number of probes** (proof of Theorem 19.9, "Groups, blocks and probes", from
Lemma 19.6(ii)): with lists of at most `n` elements, `σ ≥ 1`, `p^k ≤ pn/σ` and
`Z(π) ≤ (eσ+1)n²`, `|𝒫₀| ≤ (p+2+e+1/σ) n²/σ ≤ (p+6) n²/σ`. -/
theorem probes_card_le_fp [NeZero p] (S₁ S₂ S₃ : Finset (VecP p d)) {k : ℕ}
    (π : VecP p d →ₗ[ZMod p] VecP p k) (n σ : ℕ) (hσ : 0 < σ)
    (B₂ : OneHash.Blocking S₂ π.toAddMonoidHom σ) (B₃ : OneHash.Blocking S₃ π.toAddMonoidHom σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (hk : (p : ℝ) ^ k ≤ p * n / σ)
    (hZ : (OneHash.Zc S₁ S₂ S₃ π.toAddMonoidHom : ℝ) ≤ (Real.exp 1 * σ + 1) * n ^ 2) :
    ((OneHash.probes S₁ B₂ B₃).card : ℝ) ≤ (p + 2 + Real.exp 1 + 1 / σ) * n ^ 2 / σ ∧
    ((OneHash.probes S₁ B₂ B₃).card : ℝ) ≤ (p + 6) * n ^ 2 / σ := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hσ1 : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  have hmain := OneHash.probes_card_le (S₁ := S₁) hσ B₂ B₃
  have hC := card_image_le_pow S₂ π
  have c1 : (S₁.card : ℝ) ≤ n := by exact_mod_cast h₁
  have c2 : (S₂.card : ℝ) ≤ n := by exact_mod_cast h₂
  have c3 : (S₃.card : ℝ) ≤ n := by exact_mod_cast h₃
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have t1 : (S₁.card : ℝ) * (S₂.image π.toAddMonoidHom).card ≤ n * (p * n / σ) :=
    mul_le_mul c1 (hC.trans hk) (Nat.cast_nonneg _) hn0
  have t2 : (S₁.card : ℝ) * ((S₂.card + S₃.card) / σ) ≤ n * ((n + n) / σ) := by
    apply mul_le_mul c1 _ (by positivity) hn0
    exact div_le_div_of_nonneg_right (by linarith) hσR.le
  have t3 : (OneHash.Zc S₁ S₂ S₃ π.toAddMonoidHom : ℝ) / σ ^ 2 ≤
      (Real.exp 1 * σ + 1) * n ^ 2 / σ ^ 2 :=
    div_le_div_of_nonneg_right hZ (by positivity)
  have hfirst : ((OneHash.probes S₁ B₂ B₃).card : ℝ) ≤
      (p + 2 + Real.exp 1 + 1 / σ) * n ^ 2 / σ := by
    have : n * (p * n / σ) + n * ((n + n) / σ) + (Real.exp 1 * σ + 1) * n ^ 2 / σ ^ 2 =
        ((p : ℝ) + 2 + Real.exp 1 + 1 / σ) * n ^ 2 / σ := by
      field_simp; ring
    linarith
  refine ⟨hfirst, hfirst.trans ?_⟩
  have he := Real.exp_one_lt_d9
  have hinv : 1 / (σ : ℝ) ≤ 1 := by rw [div_le_one hσR]; exact hσ1
  apply div_le_div_of_nonneg_right _ hσR.le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  linarith

/-- The probe count for `π` chosen as in the paper: `k ≥ 1` rows greedy on `Z` from a
`(1/k)`-kernel-biased `E_k`, `n/σ ≤ p^k ≤ pn/σ`: `|𝒫₀| ≤ (p+6) n²/σ`. -/
theorem probes_card_le_greedy [NeZero p] (S₁ S₂ S₃ : Finset (VecP p d)) (n σ : ℕ) (hσ : 0 < σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (E : Multiset (VecP p d)) (rows : List (VecP p d)) (hk : 0 < rows.length)
    (hE : IsKerBiased (1 / (rows.length : ℝ)) E)
    (hg : IsGreedy E (fun l => (Zrows S₁ S₂ S₃ l : ℝ)) rows)
    (hpk : (n : ℝ) / σ ≤ (p : ℝ) ^ rows.length) (hpk' : (p : ℝ) ^ rows.length ≤ p * n / σ)
    (B₂ : OneHash.Blocking S₂ (rowsMap rows).toAddMonoidHom σ)
    (B₃ : OneHash.Blocking S₃ (rowsMap rows).toAddMonoidHom σ) :
    ((OneHash.probes S₁ B₂ B₃).card : ℝ) ≤ (p + 6) * n ^ 2 / σ :=
  (probes_card_le_fp S₁ S₂ S₃ (rowsMap rows) n σ hσ B₂ B₃ h₁ h₂ h₃ hpk'
    (Zrows_pi_le S₁ S₂ S₃ n σ (Nat.pos_of_ne_zero (NeZero.ne p)) hσ h₁ h₂ h₃ E rows hk hE hg
      hpk).2).2

/-! ### The instance `I(H, 𝒫)` and its counts -/

/-- The split map `K = (H_{<l₁}, H_{≥l₁}) : F_p^d → F_p^{l₁'} × F_p^{l₂'}` of the rows of `H`
(the first `l₁` rows and the rest); the paper takes `l₁ = ⌈l/2⌉`. Its kernel is that of `H`. -/
def splitK (rows : List (VecP p d)) (l₁ : ℕ) :
    VecP p d →+ VecP p (rows.take l₁).length × VecP p (rows.drop l₁).length :=
  ((rowsMap (rows.take l₁)).prod (rowsMap (rows.drop l₁))).toAddMonoidHom

theorem splitK_eq_zero_iff (rows : List (VecP p d)) (l₁ : ℕ) (x : VecP p d) :
    splitK rows l₁ x = 0 ↔ rowsMap rows x = 0 := by
  rw [rowsMap_eq_zero_iff]
  have : splitK rows l₁ x = (rowsMap (rows.take l₁) x, rowsMap (rows.drop l₁) x) := rfl
  rw [this, Prod.mk_eq_zero, rowsMap_eq_zero_iff, rowsMap_eq_zero_iff]
  constructor
  · rintro ⟨h1, h2⟩ u hu
    rw [← List.take_append_drop l₁ rows, List.mem_append] at hu
    rcases hu with hu | hu
    · exact h1 u hu
    · exact h2 u hu
  · intro h
    exact ⟨fun u hu => h u (List.mem_of_mem_take hu), fun u hu => h u (List.mem_of_mem_drop hu)⟩

/-- `cnt_K(Q) = cnt_H(Q)` for the split map. -/
theorem cnt_splitK (rows : List (VecP p d)) (l₁ : ℕ) (Q : OneHash.Probe (VecP p d)) :
    OneHash.cnt (splitK rows l₁) Q = (probeCands p d).cnt (rowsMap rows) Q := by
  dsimp only [OneHash.cnt, Cands.cnt, probeCands]
  congr 1
  exact Finset.filter_congr fun pr _ => splitK_eq_zero_iff rows l₁ _

/-- **The instance and its counts** (proof of Theorem 19.9; Lemma 19.6(iii)): the entry of `XY`
at the position of a probe `Q` is `cnt_H(Q)`. Middle part `F_p^{l₁'} × F_p^{l₂'}`; `zr` picks
block representatives, and `zr = 0` gives the instance of Theorem 19.9 with the representatives
dropped (`matX_zero_rep`, `matY_zero_rep`). -/
theorem probe_matXY [NeZero p] (rows : List (VecP p d)) (l₁ : ℕ)
    (zr : Finset (VecP p d) → VecP p d) (Q : OneHash.Probe (VecP p d)) :
    ∑ w, OneHash.matX (splitK rows l₁) zr (OneHash.posn (splitK rows l₁) zr Q).1 w *
      OneHash.matY (splitK rows l₁) zr w (OneHash.posn (splitK rows l₁) zr Q).2 =
      (probeCands p d).cnt (rowsMap rows) Q := by
  rw [OneHash.matXY_pos_univ, cnt_splitK]

/-- With the representatives dropped, `X[(b₂,u),λ] = #{x₂ ∈ b₂ : K x₂ + (u,0) = λ}`. -/
theorem matX_zero_rep {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [DecidableEq M₁]
    [DecidableEq M₂] (K : VecP p d →+ M₁ × M₂) (r : Finset (VecP p d) × M₁) (w : M₁ × M₂) :
    OneHash.matX K (fun _ => 0) r w = (r.1.filter fun x => K x + (r.2, 0) = w).card := by
  unfold OneHash.matX
  simp only [map_zero, sub_zero]

/-- With the representatives dropped, `Y[λ,(b₃,v)] = #{x₃ ∈ b₃ : −K x₃ − (0,v) = λ}`. -/
theorem matY_zero_rep {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [DecidableEq M₁]
    [DecidableEq M₂] (K : VecP p d →+ M₁ × M₂) (w : M₁ × M₂) (c : Finset (VecP p d) × M₂) :
    OneHash.matY K (fun _ => 0) w c = (c.1.filter fun x => -K x - (0, c.2) = w).card := by
  unfold OneHash.matY
  simp only [map_zero, sub_zero]

/-! ### Binary splitting (Lemma s:lem:split, as used in Theorem 19.9) -/

/-- The counting version `#Lop`: the number of common neighbours of `a` and `b` in the middle
part. -/
noncomputable def lopCount {A B V : Type*} (I : OneHash.LopInst A B V) (a : A) (b : B) : ℕ :=
  open Classical in (I.mid.filter fun m => I.adjA a m ∧ I.adjB m b).card

/-- The `i`-th binary digit. -/
def binDigit (i x : ℕ) : ℕ := x / 2 ^ i % 2

theorem sum_binDigits (B x : ℕ) (hx : x < 2 ^ B) :
    ∑ i ∈ range B, 2 ^ i * binDigit i x = x := by
  induction B generalizing x with
  | zero => simp at hx; simp [hx]
  | succ B ih =>
    rw [Finset.sum_range_succ']
    have hb : ∀ i, binDigit (i + 1) x = binDigit i (x / 2) := by
      intro i; unfold binDigit; rw [Nat.div_div_eq_div_mul, pow_succ']
    simp only [hb, pow_succ, mul_assoc]
    have : ∑ i ∈ range B, 2 ^ i * (2 * binDigit i (x / 2)) =
        2 * ∑ i ∈ range B, 2 ^ i * binDigit i (x / 2) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [this, ih (x / 2) (by rw [pow_succ] at hx; omega)]
    unfold binDigit; simp; omega

/-- `XY = Σ_{i,j<B} 2^{i+j} X_i Y_j` for entries below `2^B`. -/
theorem matmul_binDigits {R K M : Type*} [Fintype M] (X : R → M → ℕ) (Y : M → K → ℕ) (B : ℕ)
    (r : R) (c : K) (hX : ∀ w, X r w < 2 ^ B) (hY : ∀ w, Y w c < 2 ^ B) :
    ∑ w, X r w * Y w c =
      ∑ i ∈ range B, ∑ j ∈ range B, 2 ^ (i + j) *
        ∑ w, binDigit i (X r w) * binDigit j (Y w c) := by
  have h1 : ∑ w, X r w * Y w c = ∑ w, ∑ i ∈ range B, ∑ j ∈ range B,
      (2 ^ i * binDigit i (X r w)) * (2 ^ j * binDigit j (Y w c)) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Finset.sum_mul_sum, sum_binDigits B _ (hX w), sum_binDigits B _ (hY w)]
  rw [h1]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  ring

/-- The `0/1` instance of `#Lop` for the digit matrices `X_i`, `Y_j`, with middle part `M`. -/
def digitInst {R K M : Type*} [Fintype M] (X : R → M → ℕ) (Y : M → K → ℕ) (i j : ℕ)
    (W : Finset (R × K)) : OneHash.LopInst R K M where
  mid := univ
  adjA r w := binDigit i (X r w) = 1
  adjB w c := binDigit j (Y w c) = 1
  W := W

/-- The oracle's answer on a digit instance is `Σ_w X_i Y_j`. -/
theorem digitInst_count {R K M : Type*} [Fintype M] (X : R → M → ℕ) (Y : M → K → ℕ) (i j : ℕ)
    (W : Finset (R × K)) (r : R) (c : K) :
    lopCount (digitInst X Y i j W) r c = ∑ w, binDigit i (X r w) * binDigit j (Y w c) := by
  have h2 : ∀ x i, binDigit i x < 2 := fun x i => Nat.mod_lt _ (by norm_num)
  unfold lopCount digitInst
  simp only
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun w _ => ?_
  have ha := h2 (X r w) i
  have hb := h2 (Y w c) j
  generalize binDigit i (X r w) = a at ha ⊢
  generalize binDigit j (Y w c) = b at hb ⊢
  interval_cases a <;> interval_cases b <;> simp

/-- **The instance and its counts with binary splitting** (proof of Theorem 19.9, "The instance
and its counts" and "Shape and cost of one evaluation"): when the blocks of `Q` have at most
`σ < 2^B` elements, `cnt_H(Q) = Σ_{i,j<B} 2^{i+j}` times the `#Lop` answer of the `0/1` digit
instance `(i, j)` at the position of `Q`. The query set `W` plays no role in the count. -/
theorem probe_cnt_eq_oracle [NeZero p] (rows : List (VecP p d)) (l₁ : ℕ)
    (zr : Finset (VecP p d) → VecP p d) (σ B : ℕ) (hB : σ < 2 ^ B)
    (W : Finset ((Finset (VecP p d) × VecP p (rows.take l₁).length) ×
      (Finset (VecP p d) × VecP p (rows.drop l₁).length)))
    (Q : OneHash.Probe (VecP p d)) (hb₂ : Q.2.1.card ≤ σ) (hb₃ : Q.2.2.card ≤ σ) :
    (probeCands p d).cnt (rowsMap rows) Q = ∑ i ∈ range B, ∑ j ∈ range B, 2 ^ (i + j) *
      lopCount (digitInst (OneHash.matX (splitK rows l₁) zr) (OneHash.matY (splitK rows l₁) zr)
        i j W) (OneHash.posn (splitK rows l₁) zr Q).1 (OneHash.posn (splitK rows l₁) zr Q).2 := by
  rw [← probe_matXY rows l₁ zr Q, matmul_binDigits (OneHash.matX (splitK rows l₁) zr)
    (OneHash.matY (splitK rows l₁) zr) B (OneHash.posn (splitK rows l₁) zr Q).1
    (OneHash.posn (splitK rows l₁) zr Q).2
    (fun w => (OneHash.matX_le (splitK rows l₁) zr (OneHash.posn (splitK rows l₁) zr Q).1
      w).trans_lt (lt_of_le_of_lt hb₂ hB))
    (fun w => (OneHash.matY_le (splitK rows l₁) zr w
      (OneHash.posn (splitK rows l₁) zr Q).2).trans_lt (lt_of_le_of_lt hb₃ hB))]
  simp only [digitInst_count]

/-! ### Correctness -/

/-- **Theorem 19.9, correctness** (Lemma x:lem:correct with the halving lemma over `F_p`): for
any homomorphism `π`, any blocks of at most `σ` elements, a `(1/q)`-kernel-biased `E` with
`e p^{-q} σ² ≤ 1/2`, `q ≥ 1`, any number `L` of stages and any rule choosing the rows greedily
on `Σ = Σ_Q cnt_H(Q)`, the staged algorithm answers YES iff a solution exists. -/
theorem fp_count_correct {P : Type*} [AddCommGroup P] [DecidableEq P]
    (S₁ S₂ S₃ : Finset (VecP p d)) (π : VecP p d →+ P)
    (σ q L : ℕ) (B₂ : OneHash.Blocking S₂ π σ) (B₃ : OneHash.Blocking S₃ π σ)
    (E : Multiset (VecP p d)) (hE : IsKerBiased (1 / (q : ℝ)) E) (hq : 0 < q)
    (hqσ : Real.exp 1 * (1 / (p : ℝ) ^ q) * (σ : ℝ) ^ 2 ≤ 1 / 2)
    (rowsOf : Finset (OneHash.Probe (VecP p d)) → List (VecP p d))
    (hrule : (probeCands p d).GreedyRule E q rowsOf) :
    (probeCands p d).run rowsOf L (OneHash.probes S₁ B₂ B₃) = true ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0 := by
  rw [(probeCands p d).run_iff E q (σ ^ 2) hE hq (by push_cast; exact hqσ) rowsOf hrule _
    (probe_card_fam_le (S₁ := S₁) B₂ B₃) L]
  exact (OneHash.exists_sol_iff_probe B₂ B₃).symm

/-- `Σ_{Q ∈ 𝒫}` of the oracle's answers, `cnt_H(Q) = Σ_{i,j<B} 2^{i+j} · #Lop(digit instance)`,
for the split `l₁ = ⌈l/2⌉` of the rows and the positions of `𝒫` as query set. -/
noncomputable def oracleTotal [NeZero p] (zr : Finset (VecP p d) → VecP p d) (B : ℕ)
    (Ps : Finset (OneHash.Probe (VecP p d))) (rows : List (VecP p d)) : ℝ :=
  ∑ Q ∈ Ps, ((∑ i ∈ range B, ∑ j ∈ range B, 2 ^ (i + j) *
    lopCount (digitInst (OneHash.matX (splitK rows ((rows.length + 1) / 2)) zr)
      (OneHash.matY (splitK rows ((rows.length + 1) / 2)) zr) i j
      (Ps.image (OneHash.posn (splitK rows ((rows.length + 1) / 2)) zr)))
      (OneHash.posn (splitK rows ((rows.length + 1) / 2)) zr Q).1
      (OneHash.posn (splitK rows ((rows.length + 1) / 2)) zr Q).2 : ℕ) : ℝ)

/-- The oracle's sums are `Σ`, for probes with blocks of at most `σ < 2^B` elements. -/
theorem oracleTotal_eq_total [NeZero p] (zr : Finset (VecP p d) → VecP p d) (σ B : ℕ)
    (hB : σ < 2 ^ B) (Ps : Finset (OneHash.Probe (VecP p d)))
    (hPs : ∀ Q ∈ Ps, Q.2.1.card ≤ σ ∧ Q.2.2.card ≤ σ) :
    oracleTotal zr B Ps = (probeCands p d).total Ps := by
  funext rows
  unfold oracleTotal Cands.total
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [probe_cnt_eq_oracle rows ((rows.length + 1) / 2) zr σ B hB
    (Ps.image (OneHash.posn (splitK rows ((rows.length + 1) / 2)) zr)) Q (hPs Q hQ).1
    (hPs Q hQ).2]

/-- **Theorem 19.9, correctness, with the rows greedy on the oracle's sums**: the rule needs to
be greedy on `oracleTotal` only for the sets of probes the algorithm meets (subsets of `𝒫₀`). -/
theorem fp_count_correct_oracle [NeZero p] {P : Type*} [AddCommGroup P] [DecidableEq P]
    (S₁ S₂ S₃ : Finset (VecP p d)) (π : VecP p d →+ P)
    (σ q L : ℕ) (B₂ : OneHash.Blocking S₂ π σ) (B₃ : OneHash.Blocking S₃ π σ)
    (E : Multiset (VecP p d)) (hE : IsKerBiased (1 / (q : ℝ)) E) (hq : 0 < q)
    (hqσ : Real.exp 1 * (1 / (p : ℝ) ^ q) * (σ : ℝ) ^ 2 ≤ 1 / 2)
    (zr : Finset (VecP p d) → VecP p d) (B : ℕ) (hB : σ < 2 ^ B)
    (rowsOf : Finset (OneHash.Probe (VecP p d)) → List (VecP p d))
    (hrule : ∀ Ps ⊆ OneHash.probes S₁ B₂ B₃,
      (rowsOf Ps).length = q ∧ IsGreedy E (oracleTotal zr B Ps) (rowsOf Ps)) :
    (probeCands p d).run rowsOf L (OneHash.probes S₁ B₂ B₃) = true ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0 := by
  classical
  let rowsOf' : Finset (OneHash.Probe (VecP p d)) → List (VecP p d) := fun Ps =>
    if Ps ⊆ OneHash.probes S₁ B₂ B₃ then rowsOf Ps
    else greedyRows E ((probeCands p d).total Ps) q
  have hrule' : (probeCands p d).GreedyRule E q rowsOf' := by
    intro Ps
    by_cases h : Ps ⊆ OneHash.probes S₁ B₂ B₃
    · have e : rowsOf' Ps = rowsOf Ps := if_pos h
      rw [e]
      obtain ⟨hl, hg⟩ := hrule Ps h
      have hT : oracleTotal zr B Ps = (probeCands p d).total Ps :=
        oracleTotal_eq_total zr σ B hB Ps fun Q hQ => by
          have hm := (OneHash.mem_probes.1 (h hQ)).1
          exact ⟨B₂.card_le _ hm.2.1, B₃.card_le _ hm.2.2⟩
      rw [← hT]
      exact ⟨hl, hg⟩
    · have e : rowsOf' Ps = greedyRows E ((probeCands p d).total Ps) q := if_neg h
      rw [e]
      exact (probeCands p d).greedyRule_greedyRows E hE.1 q Ps
  rw [(probeCands p d).run_congr rowsOf rowsOf' (OneHash.probes S₁ B₂ B₃)
    (fun Ps hPs => (if_pos hPs).symm) L]
  exact fp_count_correct S₁ S₂ S₃ π σ q L B₂ B₃ E hE hq hqσ rowsOf' hrule'

/-! ### Parameters (proof of Theorem 19.9, "Parameters") -/

theorem exists_pow_ge (p : ℕ) (hp : 1 < p) (x : ℝ) : ∃ q : ℕ, x ≤ (p : ℝ) ^ q := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt x (by exact_mod_cast hp : (1 : ℝ) < p)
  exact ⟨q, hq.le⟩

/-- `q := ⌈log_p(2eσ²)⌉`, the least `q` with `p^q ≥ 2eσ²`. -/
noncomputable def qParam (p σ : ℕ) (hp : 1 < p) : ℕ :=
  Nat.find (exists_pow_ge p hp (2 * Real.exp 1 * σ ^ 2))

/-- `k := ⌈log_p(n/σ)⌉`, the least `k` with `p^k ≥ n/σ`. -/
noncomputable def kParam (p n σ : ℕ) (hp : 1 < p) : ℕ :=
  Nat.find (exists_pow_ge p hp ((n : ℝ) / σ))

/-- From `p^{q-1} < x ≤ p^q`, `q ≥ 1`: `p^q < p x`. -/
theorem pow_lt_mul_of_min (p q : ℕ) (hp : 1 < p) (hq : 1 ≤ q) (x : ℝ)
    (hmin : (p : ℝ) ^ (q - 1) < x) : (p : ℝ) ^ q < p * x := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpq : (p : ℝ) ^ q = p * p ^ (q - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpq]
  exact mul_lt_mul_of_pos_left hmin hpR

/-- **Parameters, `q`**: for `σ ≥ 1`, `q ≥ 1`, `2eσ² ≤ p^q < Λσ²` with `Λ = 2ep`, and
`e p^{-q} σ² ≤ 1/2` (the hypothesis of `fp_count_correct`). -/
theorem qParam_spec (p σ : ℕ) (hp : 1 < p) (hσ : 0 < σ) :
    1 ≤ qParam p σ hp ∧ 2 * Real.exp 1 * σ ^ 2 ≤ (p : ℝ) ^ qParam p σ hp ∧
    (p : ℝ) ^ qParam p σ hp < 2 * Real.exp 1 * p * σ ^ 2 ∧
    Real.exp 1 * (1 / (p : ℝ) ^ qParam p σ hp) * (σ : ℝ) ^ 2 ≤ 1 / 2 := by
  have hσ1 : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  have hσ2 : (1 : ℝ) ≤ (σ : ℝ) ^ 2 := by nlinarith
  have hed := Real.exp_one_gt_d9
  have he : (1 : ℝ) < 2 * Real.exp 1 * σ ^ 2 := by nlinarith
  have hs := Nat.find_spec (exists_pow_ge p hp (2 * Real.exp 1 * σ ^ 2))
  have h1 : 1 ≤ qParam p σ hp := by
    by_contra h0
    have h0' : qParam p σ hp = 0 := by omega
    unfold qParam at h0'
    rw [h0', pow_zero] at hs
    linarith
  have hm := Nat.find_min (exists_pow_ge p hp (2 * Real.exp 1 * σ ^ 2))
    (m := qParam p σ hp - 1) (by unfold qParam at h1 ⊢; omega)
  have hmin : (p : ℝ) ^ (qParam p σ hp - 1) < 2 * Real.exp 1 * σ ^ 2 := lt_of_not_ge hm
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hpos : (0 : ℝ) < (p : ℝ) ^ qParam p σ hp := by positivity
  refine ⟨h1, hs, ?_, ?_⟩
  · calc (p : ℝ) ^ qParam p σ hp < p * (2 * Real.exp 1 * σ ^ 2) :=
          pow_lt_mul_of_min p _ hp h1 _ hmin
      _ = 2 * Real.exp 1 * p * σ ^ 2 := by ring
  · have hs' : 2 * Real.exp 1 * σ ^ 2 ≤ (p : ℝ) ^ qParam p σ hp := hs
    rw [show Real.exp 1 * (1 / (p : ℝ) ^ qParam p σ hp) * (σ : ℝ) ^ 2 =
      (Real.exp 1 * σ ^ 2) / (p : ℝ) ^ qParam p σ hp by ring, div_le_iff₀ hpos]
    linarith

/-- **Parameters, `k`**: for `σ < n`, `k ≥ 1` and `n/σ ≤ p^k < pn/σ`. -/
theorem kParam_spec (p n σ : ℕ) (hp : 1 < p) (hσ : 0 < σ) (hσn : σ < n) :
    1 ≤ kParam p n σ hp ∧ (n : ℝ) / σ ≤ (p : ℝ) ^ kParam p n σ hp ∧
    (p : ℝ) ^ kParam p n σ hp < p * n / σ := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hn1 : (1 : ℝ) < n / σ := by
    rw [one_lt_div hσR]; exact_mod_cast hσn
  have hs := Nat.find_spec (exists_pow_ge p hp ((n : ℝ) / σ))
  have h1 : 1 ≤ kParam p n σ hp := by
    by_contra h0
    have h0' : kParam p n σ hp = 0 := by omega
    unfold kParam at h0'
    rw [h0', pow_zero] at hs
    linarith
  have hm := Nat.find_min (exists_pow_ge p hp ((n : ℝ) / σ))
    (m := kParam p n σ hp - 1) (by unfold kParam at h1 ⊢; omega)
  have hmin : (p : ℝ) ^ (kParam p n σ hp - 1) < n / σ := lt_of_not_ge hm
  refine ⟨h1, hs, ?_⟩
  calc (p : ℝ) ^ kParam p n σ hp < p * (n / σ) := pow_lt_mul_of_min p _ hp h1 _ hmin
    _ = p * n / σ := by ring

end Fp
end GroupLean

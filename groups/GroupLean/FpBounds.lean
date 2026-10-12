import GroupLean.Select
import GroupLean.OneHash
import GroupLean.ExpP2

/-!
# Theorem A over `F_p^d`: the hash bounds and the counts

The paper's Theorem 19.8 (Theorem A here; its proof's "The hash" and "Counts") and Lemma 19.24
(Part H of Theorem 19.17, the choice of the rows).

The rows `u₁, …, u_{k+q}` are chosen one at a time from a kernel-biased multiset `E`, each
minimising the global count `Z` of the map formed by the rows so far and the candidate
(`Zrows`). Rows are stored newest first (as in `Select.lean`): the list `rows` of length `k + q`
has the `q` last-chosen rows (the map `H`) in front of the `k` first-chosen rows `rows.drop q`
(the map `π`).

* `rowsMap m rows : F_p^d →+ F_p^m`, `x ↦ (⟨rows[i], x⟩)_{i<m}` (`0` past the end of the list);
  its kernel is `{x : ⟨u, x⟩ = 0 for all u ∈ rows}` when `rows.length ≤ m`.
* `surv_tripFam`, `isGreedy_Zc_iff`: `Z(rows) − Z₀` is the surviving weight of the family of the
  nonzero sums `x₁ + x₂ + x₃` (weight `1` each); minimising `Z` is minimising this weight.
* `fp_prefix_le`, `fp_prefix_bounds`: Lemma 2 for every prefix.
* `theoremA_counts`, `theoremA_F`, `theoremA_probes`: the bounds of "The hash" and "Counts".
* Part H: `Sp` (`S′_t`), `Sp_eq_card`, `Sp_eq_Zc`, `isGreedy_Sp_iff`, `partH_choice`,
  `partH_bounds`.
-/

set_option linter.unusedSectionVars false

namespace GroupLean
namespace FpBounds

open Finset OneHash

variable {p d : ℕ}

/-! ### The map of a list of rows -/

/-- The map of a row list into `F_p^m`: coordinate `i` is `⟨rows[i], x⟩` (`0` past the end). -/
def rowsMap (m : ℕ) (rows : List (VecP p d)) : VecP p d →+ VecP p m where
  toFun x i := (rows.getD i 0) ⬝ᵥ x
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp [dotProduct_add]

theorem rowsMap_apply (m : ℕ) (rows : List (VecP p d)) (x : VecP p d) (i : Fin m) :
    rowsMap m rows x i = (rows.getD i 0) ⬝ᵥ x := rfl

/-- The kernel of `rowsMap`: all rows send `x` to `0`. -/
theorem rowsMap_eq_zero_iff (m : ℕ) (rows : List (VecP p d)) (h : rows.length ≤ m)
    (x : VecP p d) : rowsMap m rows x = 0 ↔ ∀ u ∈ rows, u ⬝ᵥ x = 0 := by
  constructor
  · intro hx u hu
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
    have h2 : (rows.getD i 0) ⬝ᵥ x = 0 := congrFun hx ⟨i, by omega⟩
    rwa [List.getD_eq_getElem _ _ hi] at h2
  · intro hx
    funext i
    rw [rowsMap_apply]
    by_cases hi : (i : ℕ) < rows.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hx _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]; exact zero_dotProduct x

/-! ### `Z − Z₀` as a surviving weight -/

/-- The family of Lemma 2 for `Z`: the triples with `x₁ + x₂ + x₃ ≠ 0`, weight `1`. -/
def tripFam (S₁ S₂ S₃ : Finset (VecP p d)) : Finset (VecP p d × VecP p d × VecP p d) :=
  (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => t.1 + t.2.1 + t.2.2 ≠ 0

/-- **`Φ = Z − Z₀`**: the surviving weight of the nonzero sums under the rows is
`Z(rows) − Z₀`, for the map `rowsMap m rows` of any width `m ≥ |rows|`. -/
theorem surv_tripFam (S₁ S₂ S₃ : Finset (VecP p d)) (m : ℕ) (rows : List (VecP p d))
    (h : rows.length ≤ m) :
    surv (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1) rows =
      (Zc S₁ S₂ S₃ (rowsMap m rows) : ℝ) - Zsol S₁ S₂ S₃ := by
  have hsplit : Zc S₁ S₂ S₃ (rowsMap m rows) = ((tripFam S₁ S₂ S₃).filter fun t =>
      ∀ u ∈ rows, u ⬝ᵥ (t.1 + t.2.1 + t.2.2) = 0).card + Zsol S₁ S₂ S₃ := by
    unfold Zc Zsol tripFam
    rw [Finset.filter_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h0 : t.1 + t.2.1 + t.2.2 = 0
    · simp [h0]
    · rw [if_neg h0, add_zero]
      exact if_congr (by rw [rowsMap_eq_zero_iff m rows h]
                         exact ⟨fun h' => ⟨h0, h'⟩, fun h' => h'.2⟩) rfl rfl
  unfold surv
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hsplit]
  push_cast; ring

/-- The greedy cost: `Z` of the map formed by the rows (newest first). -/
noncomputable def Zrows (S₁ S₂ S₃ : Finset (VecP p d)) (l : List (VecP p d)) : ℝ :=
  Zc S₁ S₂ S₃ (rowsMap l.length l)

/-- **Minimising `Z` is minimising the surviving weight.** -/
theorem isGreedy_Zc_iff (S₁ S₂ S₃ : Finset (VecP p d)) (E : Multiset (VecP p d))
    (rows : List (VecP p d)) :
    IsGreedy E (Zrows S₁ S₂ S₃) rows ↔
      IsGreedy E (surv (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1)) rows := by
  have : Zrows S₁ S₂ S₃ = fun l =>
      surv (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2) (fun _ => 1) l +
        (Zsol S₁ S₂ S₃ : ℝ) := by
    funext l
    rw [surv_tripFam S₁ S₂ S₃ l.length l le_rfl, Zrows]; ring
  rw [this, isGreedy_add_const]

theorem card_tripFam_le (S₁ S₂ S₃ : Finset (VecP p d)) :
    ((tripFam S₁ S₂ S₃).card : ℝ) ≤ (S₁.card : ℝ) * S₂.card * S₃.card := by
  have : (tripFam S₁ S₂ S₃).card ≤ S₁.card * S₂.card * S₃.card := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_product, Finset.card_product, mul_assoc]
  exact_mod_cast this

/-! ### Lemma 2 for the prefixes -/

/-- **Lemma 2 for every prefix of the greedy sequence**: for the first `|rows| − j` rows
(`rows.drop j`), `Z − Z₀ ≤ e p^{−(|rows|−j)} |S₁||S₂||S₃|`. -/
theorem fp_prefix_le (S₁ S₂ S₃ : Finset (VecP p d)) {ε : ℝ} {E : Multiset (VecP p d)}
    (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε) (rows : List (VecP p d))
    (hg : IsGreedy E (Zrows S₁ S₂ S₃) rows) (hε : ε ≤ 1 / rows.length) (j : ℕ)
    (hj : j < rows.length) :
    (Zc S₁ S₂ S₃ (rowsMap (rows.length - j) (rows.drop j)) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * (1 / (p : ℝ) ^ (rows.length - j)) * ((S₁.card : ℝ) * S₂.card * S₃.card) := by
  have hlen : (rows.drop j).length = rows.length - j := List.length_drop ..
  have hg' := (isGreedy_Zc_iff S₁ S₂ S₃ E rows).1 hg
  have hb := greedy_bound_exp_drop hE hε0 (tripFam S₁ S₂ S₃) (fun t => t.1 + t.2.1 + t.2.2)
    (fun _ => 1) (fun j hj => (Finset.mem_filter.1 hj).2) (fun _ _ => zero_le_one) rows hg' j
    (by omega) hε
  rw [surv_tripFam S₁ S₂ S₃ (rows.length - j) _ hlen.le, Finset.sum_const, nsmul_eq_mul,
    mul_one, hlen] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (card_tripFam_le S₁ S₂ S₃) (by positivity))

/-- **"The hash"**, raw form: `|rows| = k + q`, `π` = the first `k` rows (`rows.drop q`), all
rows for `(π, H)`: `Z(π) − Z₀ ≤ e p^{−k} |S₁||S₂||S₃|` and
`Z((π,H)) − Z₀ ≤ e p^{−(k+q)} |S₁||S₂||S₃|`. -/
theorem fp_prefix_bounds (S₁ S₂ S₃ : Finset (VecP p d)) {ε : ℝ} {E : Multiset (VecP p d)}
    (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε) (k q : ℕ) (rows : List (VecP p d))
    (hlen : rows.length = k + q) (hk : 0 < k) (hε : ε ≤ 1 / ((k : ℝ) + q))
    (hg : IsGreedy E (Zrows S₁ S₂ S₃) rows) :
    (Zc S₁ S₂ S₃ (rowsMap k (rows.drop q)) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * (1 / (p : ℝ) ^ k) * ((S₁.card : ℝ) * S₂.card * S₃.card) ∧
    (Zc S₁ S₂ S₃ (rowsMap (k + q) rows) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * (1 / (p : ℝ) ^ (k + q)) * ((S₁.card : ℝ) * S₂.card * S₃.card) := by
  have hε' : ε ≤ 1 / (rows.length : ℝ) := by rw [hlen]; push_cast; exact hε
  have h1 := fp_prefix_le S₁ S₂ S₃ hE hε0 rows hg hε' q (by omega)
  have h2 := fp_prefix_le S₁ S₂ S₃ hE hε0 rows hg hε' 0 (by omega)
  have e1 : rows.length - q = k := by omega
  rw [e1] at h1
  rw [Nat.sub_zero, List.drop_zero, hlen] at h2
  exact ⟨h1, h2⟩

/-! ### Theorem A: the hash and the counts -/

section theoremA
variable [Fact p.Prime]

/-- **Theorem A, "The hash"**: with `|S_i| ≤ n`, `σ ≥ 1`, `n/σ ≤ p^k`, `k + q` greedy rows from an
`ε`-kernel-biased `E` with `ε ≤ 1/(k+q)`, `π` the first `k` rows:
`Z(π) − Z₀ ≤ eσn²`, `Z(π) ≤ (eσ+1)n²`, `F := Z((π,H)) − Z₀ ≤ eσn²/p^q`. -/
theorem theoremA_counts (S₁ S₂ S₃ : Finset (VecP p d)) (n σ k q : ℕ) (hσ : 0 < σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    {ε : ℝ} {E : Multiset (VecP p d)} (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / ((k : ℝ) + q)) (rows : List (VecP p d)) (hlen : rows.length = k + q)
    (hk : 0 < k) (hg : IsGreedy E (Zrows S₁ S₂ S₃) rows) (hpk : (n : ℝ) / σ ≤ (p : ℝ) ^ k) :
    (Zc S₁ S₂ S₃ (rowsMap k (rows.drop q)) : ℝ) - Zsol S₁ S₂ S₃ ≤ Real.exp 1 * σ * n ^ 2 ∧
    (Zc S₁ S₂ S₃ (rowsMap k (rows.drop q)) : ℝ) ≤ (Real.exp 1 * σ + 1) * n ^ 2 ∧
    (Zc S₁ S₂ S₃ (rowsMap (k + q) rows) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * σ * n ^ 2 / (p : ℝ) ^ q := by
  obtain ⟨h1, h2⟩ := fp_prefix_bounds S₁ S₂ S₃ hE hε0 k q rows hlen hk hε hg
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpk0 : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hp0 k
  have hpq0 : (0 : ℝ) < (p : ℝ) ^ q := pow_pos hp0 q
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have c1 : (S₁.card : ℝ) ≤ n := by exact_mod_cast h₁
  have c2 : (S₂.card : ℝ) ≤ n := by exact_mod_cast h₂
  have c3 : (S₃.card : ℝ) ≤ n := by exact_mod_cast h₃
  have hprod : (S₁.card : ℝ) * S₂.card * S₃.card ≤ n ^ 3 := by
    have := mul_le_mul (mul_le_mul c1 c2 (Nat.cast_nonneg _) hn0) c3 (Nat.cast_nonneg _)
      (by positivity)
    nlinarith
  have hx : 1 / (p : ℝ) ^ k * n ≤ σ := by
    rw [div_le_iff₀ hσR] at hpk
    rw [one_div, inv_mul_le_iff₀ hpk0]; linarith
  have hA : (Zc S₁ S₂ S₃ (rowsMap k (rows.drop q)) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * σ * n ^ 2 := by
    calc _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ k) * ((S₁.card : ℝ) * S₂.card * S₃.card) := h1
      _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ k) * n ^ 3 := by gcongr
      _ = Real.exp 1 * (1 / (p : ℝ) ^ k * n) * n ^ 2 := by ring
      _ ≤ Real.exp 1 * σ * n ^ 2 := by gcongr
  have hZ0 : (Zsol S₁ S₂ S₃ : ℝ) ≤ n ^ 2 := by
    have : (Zsol S₁ S₂ S₃ : ℝ) ≤ S₁.card * S₂.card := by exact_mod_cast Zsol_le S₁ S₂ S₃
    nlinarith [Nat.cast_nonneg (α := ℝ) S₁.card, Nat.cast_nonneg (α := ℝ) S₂.card]
  refine ⟨hA, by linarith, ?_⟩
  calc _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ (k + q)) * ((S₁.card : ℝ) * S₂.card * S₃.card) := h2
    _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ (k + q)) * n ^ 3 := by gcongr
    _ = Real.exp 1 * (1 / (p : ℝ) ^ k * n) * n ^ 2 / (p : ℝ) ^ q := by
        rw [pow_add]; field_simp
    _ ≤ Real.exp 1 * σ * n ^ 2 / (p : ℝ) ^ q := by gcongr

/-- The kernel of all rows lies in the kernel of the first `k` rows: `π` factors through
`(π, H)`. -/
theorem rowsMap_factor (k q : ℕ) (rows : List (VecP p d)) (hlen : rows.length = k + q)
    (x : VecP p d) (hx : rowsMap (k + q) rows x = 0) : rowsMap k (rows.drop q) x = 0 := by
  rw [rowsMap_eq_zero_iff _ _ hlen.le] at hx
  rw [rowsMap_eq_zero_iff _ _ (by rw [List.length_drop]; omega)]
  exact fun u hu => hx u (List.mem_of_mem_drop hu)

/-- **Theorem A, false positives over the probes**: `F = Σ_{Q∈𝒫₀} (cnt − z) ≤ eσn²/p^q`. -/
theorem theoremA_F (S₁ S₂ S₃ : Finset (VecP p d)) (n σ k q : ℕ) (hσ : 0 < σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    {ε : ℝ} {E : Multiset (VecP p d)} (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / ((k : ℝ) + q)) (rows : List (VecP p d)) (hlen : rows.length = k + q)
    (hk : 0 < k) (hg : IsGreedy E (Zrows S₁ S₂ S₃) rows) (hpk : (n : ℝ) / σ ≤ (p : ℝ) ^ k)
    (B₂ : Blocking S₂ (rowsMap k (rows.drop q)) σ) (B₃ : Blocking S₃ (rowsMap k (rows.drop q)) σ) :
    (F (probes S₁ B₂ B₃) (rowsMap (k + q) rows) : ℝ) ≤ Real.exp 1 * σ * n ^ 2 / (p : ℝ) ^ q := by
  have e := F_probes_eq (S₁ := S₁) B₂ B₃ (rowsMap (k + q) rows) (rowsMap_factor k q rows hlen)
  have e' := congrArg (Int.cast : ℤ → ℝ) e
  push_cast at e'
  rw [e']
  exact (theoremA_counts S₁ S₂ S₃ n σ k q hσ h₁ h₂ h₃ hE hε0 hε rows hlen hk hg hpk).2.2

/-- **Theorem A, "Counts"**: with moreover `p^k < p n/σ`, the probes number at most
`(p + 2 + e + 1/σ) n²/σ` (via `probes_card_le` and `N₂ ≤ p^k`). -/
theorem theoremA_probes (S₁ S₂ S₃ : Finset (VecP p d)) (n σ k q : ℕ) (hσ : 0 < σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    {ε : ℝ} {E : Multiset (VecP p d)} (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / ((k : ℝ) + q)) (rows : List (VecP p d)) (hlen : rows.length = k + q)
    (hk : 0 < k) (hg : IsGreedy E (Zrows S₁ S₂ S₃) rows) (hpk : (n : ℝ) / σ ≤ (p : ℝ) ^ k)
    (hpk' : (p : ℝ) ^ k < p * n / σ)
    (B₂ : Blocking S₂ (rowsMap k (rows.drop q)) σ) (B₃ : Blocking S₃ (rowsMap k (rows.drop q)) σ) :
    ((probes S₁ B₂ B₃).card : ℝ) ≤ (p + 2 + Real.exp 1 + 1 / σ) * n ^ 2 / σ := by
  have hP := probes_card_le (S₁ := S₁) hσ B₂ B₃
  obtain ⟨-, hB, -⟩ :=
    theoremA_counts S₁ S₂ S₃ n σ k q hσ h₁ h₂ h₃ hE hε0 hε rows hlen hk hg hpk
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have c1 : (S₁.card : ℝ) ≤ n := by exact_mod_cast h₁
  have c2 : (S₂.card : ℝ) ≤ n := by exact_mod_cast h₂
  have c3 : (S₃.card : ℝ) ≤ n := by exact_mod_cast h₃
  have hN : ((S₂.image (rowsMap k (rows.drop q))).card : ℝ) ≤ (p : ℝ) ^ k := by
    have : (S₂.image (rowsMap k (rows.drop q))).card ≤ Fintype.card (VecP p k) :=
      Finset.card_le_univ _
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin] at this
    exact_mod_cast this
  have t1 : (S₁.card : ℝ) * (S₂.image (rowsMap k (rows.drop q))).card ≤ n * (p * n / σ) :=
    mul_le_mul c1 (hN.trans hpk'.le) (Nat.cast_nonneg _) hn0
  have t2 : (S₁.card : ℝ) * ((S₂.card + S₃.card) / σ) ≤ n * ((n + n) / σ) := by
    gcongr
  have t3 : (Zc S₁ S₂ S₃ (rowsMap k (rows.drop q)) : ℝ) / σ ^ 2 ≤
      (Real.exp 1 * σ + 1) * n ^ 2 / σ ^ 2 := by gcongr
  calc ((probes S₁ B₂ B₃).card : ℝ)
      ≤ n * (p * n / σ) + n * ((n + n) / σ) + (Real.exp 1 * σ + 1) * n ^ 2 / σ ^ 2 := by
        linarith
    _ = (p + 2 + Real.exp 1 + 1 / σ) * n ^ 2 / σ := by field_simp; ring

end theoremA

/-! ### Section 19.6.3, Part H, "Choice" -/

section partH
open ExpP2
variable [Fact p.Prime]

/-- The type-I triples of Part H: `v̄ = 0`, `v ≠ 0`, with `v = x₁ + x₂ + x₃`. -/
def tripI (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) :
    Finset ((Fin d → ZMod (p ^ 2)) × (Fin d → ZMod (p ^ 2)) × (Fin d → ZMod (p ^ 2))) :=
  (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t =>
    residue (t.1 + t.2.1 + t.2.2) = 0 ∧ t.1 + t.2.1 + t.2.2 ≠ 0

/-- For `v ∈ pR^d ∖ {0}`, `v/p ≠ 0`. -/
theorem divp_ne_zero (v : Fin d → ZMod (p ^ 2)) (hres : residue v = 0) (hv : v ≠ 0) :
    ExpP2.divp v ≠ 0 := by
  intro h
  apply hv
  rw [eq_p_smul_lift_divp v hres, h, lift_zero, smul_zero]

/-- `S′(rows)`: the type-I triples with `⟨a, v/p⟩ = 0` for every row `a` (the surviving weight of
the family `{v/p : type I}`, weight `1`). -/
noncomputable def Sp (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (rows : List (VecP p d)) : ℝ :=
  surv (tripI S₁ S₂ S₃) (fun t => ExpP2.divp (t.1 + t.2.1 + t.2.2)) (fun _ => 1) rows

/-- By (F1), `S′` counts the type-I triples that all lifted rows `lift a` send to `0`. -/
theorem Sp_eq_card (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (rows : List (VecP p d)) :
    Sp S₁ S₂ S₃ rows = ((tripI S₁ S₂ S₃).filter fun t =>
      ∀ a ∈ rows, lift a ⬝ᵥ (t.1 + t.2.1 + t.2.2) = 0).card := by
  have key : ∀ t ∈ tripI S₁ S₂ S₃,
      (∀ a ∈ rows, a ⬝ᵥ ExpP2.divp (t.1 + t.2.1 + t.2.2) = 0) ↔
        ∀ a ∈ rows, lift a ⬝ᵥ (t.1 + t.2.1 + t.2.2) = 0 :=
    fun t ht => forall₂_congr fun a _ => (F1_lift a _ (Finset.mem_filter.1 ht).2.1).symm
  have h := congrArg Finset.card (Finset.filter_congr key)
  unfold Sp surv
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  norm_cast

/-- The kernel of Part H's `π = piH (rows)`: `x̄ = 0` and `⟨lift a, x⟩ = 0` for every row. -/
theorem piH_eq_zero_iff (rows : List (VecP p d)) (x : Fin d → ZMod (p ^ 2)) :
    piH (fun i : Fin rows.length => rows.get i) x = 0 ↔
      residue x = 0 ∧ ∀ a ∈ rows, lift a ⬝ᵥ x = 0 := by
  change (residue x, fun i : Fin rows.length => lift (rows.get i) ⬝ᵥ x) = 0 ↔ _
  have h : (fun i : Fin rows.length => lift (rows.get i) ⬝ᵥ x) = 0 ↔
      ∀ a ∈ rows, lift a ⬝ᵥ x = 0 := by
    rw [funext_iff]
    exact ⟨fun h a ha => by
      obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ha
      exact h i, fun h i => h _ (List.mem_iff_get.2 ⟨i, rfl⟩)⟩
  rw [Prod.ext_iff]
  exact and_congr Iff.rfl h

/-- **Part H: `Z(π) − Z₀ = S′`** for `π = piH (rows)` (`π` contains the residue, so only type-I
triples and solutions survive it). -/
theorem Sp_eq_Zc (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (rows : List (VecP p d)) :
    Sp S₁ S₂ S₃ rows =
      (Zc S₁ S₂ S₃ (piH (fun i : Fin rows.length => rows.get i)) : ℝ) - Zsol S₁ S₂ S₃ := by
  have hsplit : Zc S₁ S₂ S₃ (piH (fun i : Fin rows.length => rows.get i)) =
      ((tripI S₁ S₂ S₃).filter fun t =>
        ∀ a ∈ rows, a ⬝ᵥ ExpP2.divp (t.1 + t.2.1 + t.2.2) = 0).card + Zsol S₁ S₂ S₃ := by
    unfold Zc Zsol tripI
    rw [Finset.filter_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h0 : t.1 + t.2.1 + t.2.2 = 0
    · simp [h0]
    · rw [if_neg h0, add_zero]
      refine if_congr ?_ rfl rfl
      rw [piH_eq_zero_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, h0⟩, fun a ha => (F1_lift a _ h1).1 (h2 a ha)⟩
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, fun a ha => (F1_lift a _ h1).2 (h2 a ha)⟩
  unfold Sp surv
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hsplit]
  push_cast; ring

/-- Minimising `Z(π)` (π = residue and the lifted rows) is minimising `S′`. -/
theorem isGreedy_Sp_iff (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (E : Multiset (VecP p d))
    (rows : List (VecP p d)) :
    IsGreedy E (fun l => (Zc S₁ S₂ S₃ (piH (fun i : Fin l.length => l.get i)) : ℝ)) rows ↔
      IsGreedy E (Sp S₁ S₂ S₃) rows := by
  have : (fun l : List (VecP p d) =>
      (Zc S₁ S₂ S₃ (piH (fun i : Fin l.length => l.get i)) : ℝ)) =
      fun l => Sp S₁ S₂ S₃ l + (Zsol S₁ S₂ S₃ : ℝ) := by
    funext l
    rw [Sp_eq_Zc]; ring
  rw [this, isGreedy_add_const]

/-- **Part H, "Choice"**: rows `a_i` (rows `lift a_i`, `b = 0`) chosen greedily for `S′` from an
`ε`-kernel-biased `E`, `ε ≤ 1/|rows|`: for every prefix (the first `|rows| − j` rows),
`S′ ≤ e p^{−(|rows|−j)} T_I`. -/
theorem partH_choice (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) {ε : ℝ}
    {E : Multiset (VecP p d)} (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε) (rows : List (VecP p d))
    (hg : IsGreedy E (Sp S₁ S₂ S₃) rows) (hε : ε ≤ 1 / rows.length) (j : ℕ)
    (hj : j < rows.length) :
    Sp S₁ S₂ S₃ (rows.drop j) ≤
      Real.exp 1 * (1 / (p : ℝ) ^ (rows.length - j)) * (tripI S₁ S₂ S₃).card := by
  have hlen : (rows.drop j).length = rows.length - j := List.length_drop ..
  have hb := greedy_bound_exp_drop hE hε0 (tripI S₁ S₂ S₃)
    (fun t => ExpP2.divp (t.1 + t.2.1 + t.2.2)) (fun _ => 1)
    (fun t ht => divp_ne_zero _ (Finset.mem_filter.1 ht).2.1 (Finset.mem_filter.1 ht).2.2)
    (fun _ _ => zero_le_one) rows hg j (by omega) hε
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, hlen] at hb
  exact hb

/-- `T_I ≤ 2s|S₁||S₂|` when every residue class of `S₃` has fewer than `2s` elements. -/
theorem card_tripI_le (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (s : ℕ)
    (h : ∀ x ∈ S₃, (S₃.filter fun y => residue y = residue x).card < 2 * s) :
    (tripI S₁ S₂ S₃).card ≤ 2 * s * S₁.card * S₂.card := by
  refine le_trans (Finset.card_le_card ?_) (TI_classes_lt residue S₁ S₂ S₃ s h)
  intro t ht
  obtain ⟨hm, h1, -⟩ := Finset.mem_filter.1 ht
  refine Finset.mem_filter.2 ⟨hm, ?_⟩
  rw [← residue_add, ← residue_add]
  exact h1

/-- **Part H, the two bounds**: `k′ + q` greedy rows (`|rows| = k′ + q`, `π` = the first `k′`),
`ε ≤ 1/(k′+q)`, classes of `S₃` below `2s`, `|S_i| ≤ n`, `s/σ ≤ p^{k′}`:
`Z(π) − Z₀ = S′_{k′} ≤ 2eσn²` and `F = S′_{k′+q} ≤ 2eσn²/p^q`. -/
theorem partH_bounds (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (n σ s k q : ℕ) (hσ : 0 < σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n)
    (hcls : ∀ x ∈ S₃, (S₃.filter fun y => residue y = residue x).card < 2 * s)
    {ε : ℝ} {E : Multiset (VecP p d)} (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / ((k : ℝ) + q)) (rows : List (VecP p d)) (hlen : rows.length = k + q)
    (hg : IsGreedy E (Sp S₁ S₂ S₃) rows) (hsk : (s : ℝ) / σ ≤ (p : ℝ) ^ k) (hkq : 0 < k + q) :
    Sp S₁ S₂ S₃ (rows.drop q) ≤ 2 * Real.exp 1 * σ * n ^ 2 ∧
    Sp S₁ S₂ S₃ rows ≤ 2 * Real.exp 1 * σ * n ^ 2 / (p : ℝ) ^ q := by
  have hε' : ε ≤ 1 / (rows.length : ℝ) := by rw [hlen]; push_cast; exact hε
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpk0 : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hp0 k
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have c1 : (S₁.card : ℝ) ≤ n := by exact_mod_cast h₁
  have c2 : (S₂.card : ℝ) ≤ n := by exact_mod_cast h₂
  have hT : ((tripI S₁ S₂ S₃).card : ℝ) ≤ 2 * s * n ^ 2 := by
    have := card_tripI_le S₁ S₂ S₃ s hcls
    have h' : ((tripI S₁ S₂ S₃).card : ℝ) ≤ 2 * s * S₁.card * S₂.card := by exact_mod_cast this
    have : (S₁.card : ℝ) * S₂.card ≤ n * n := mul_le_mul c1 c2 (Nat.cast_nonneg _) hn0
    nlinarith [Nat.cast_nonneg (α := ℝ) s]
  have hx : 1 / (p : ℝ) ^ k * s ≤ σ := by
    rw [div_le_iff₀ hσR] at hsk
    rw [one_div, inv_mul_le_iff₀ hpk0]; linarith
  -- the empty-prefix case `k = 0` is covered by `S′ ≤ T_I`
  have hSp_le : ∀ l, Sp S₁ S₂ S₃ l ≤ (tripI S₁ S₂ S₃).card := by
    intro l
    unfold Sp surv
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_filter_le _ _
  have hfirst : Sp S₁ S₂ S₃ (rows.drop q) ≤
      Real.exp 1 * (1 / (p : ℝ) ^ k) * (tripI S₁ S₂ S₃).card := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp only [pow_zero, div_one, mul_one]
      have := Real.add_one_le_exp 1
      have h0 : (0 : ℝ) ≤ (tripI S₁ S₂ S₃).card := Nat.cast_nonneg _
      nlinarith [hSp_le (rows.drop q)]
    · have h := partH_choice S₁ S₂ S₃ hE hε0 rows hg hε' q (by omega)
      rwa [show rows.length - q = k by omega] at h
  have hall : Sp S₁ S₂ S₃ rows ≤
      Real.exp 1 * (1 / (p : ℝ) ^ (k + q)) * (tripI S₁ S₂ S₃).card := by
    have h := partH_choice S₁ S₂ S₃ hE hε0 rows hg hε' 0 (by omega)
    rwa [Nat.sub_zero, List.drop_zero, hlen] at h
  constructor
  · calc _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ k) * (tripI S₁ S₂ S₃).card := hfirst
      _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ k) * (2 * s * n ^ 2) := by gcongr
      _ = 2 * Real.exp 1 * (1 / (p : ℝ) ^ k * s) * n ^ 2 := by ring
      _ ≤ 2 * Real.exp 1 * σ * n ^ 2 := by gcongr
  · calc _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ (k + q)) * (tripI S₁ S₂ S₃).card := hall
      _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ (k + q)) * (2 * s * n ^ 2) := by gcongr
      _ = 2 * Real.exp 1 * (1 / (p : ℝ) ^ k * s) * n ^ 2 / (p : ℝ) ^ q := by
          rw [pow_add]; field_simp
      _ ≤ 2 * Real.exp 1 * σ * n ^ 2 / (p : ℝ) ^ q := by gcongr

/-- Part H's maps from a row list: `π` of the rows `l` (residue and `⟨lift a, x⟩`). -/
def piHL (l : List (VecP p d)) := piH (p := p) (d := d) (fun i : Fin l.length => l.get i)

/-- A list whose residue classes all have at least `s` elements has at most `|S|/s` classes. -/
theorem card_image_residue_mul_le (S : Finset (Fin d → ZMod (p ^ 2))) (s : ℕ)
    (h : ∀ x ∈ S, s ≤ (S.filter fun y => residue y = residue x).card) :
    (S.image residue).card * s ≤ S.card := by
  calc (S.image residue).card * s = ∑ _r ∈ S.image residue, s := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ r ∈ S.image residue, (S.filter fun y => residue y = r).card :=
        Finset.sum_le_sum fun r hr => by
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
          exact h x hx
    _ = S.card := (Finset.card_eq_sum_card_image residue S).symm

set_option maxHeartbeats 1000000 in
/-- **Lemma 19.24 and Case H's instance, correctness and counts.** Lists of at most `n`
elements; `T_I ≤ 2sn²` (Lemma 19.23); every residue class of lists 2 and 3 has at least `s`
elements; `σ ≥ 1`, `σ² ≤ D = p^q`; `s/σ ≤ p^{k′} < ps/σ`; rows `a_i` (`|rows| = k′+q`,
newest first) chosen greedily for `S′ = 𝖳_t` from a `β`-kernel-biased `E`, `β ≤ 1/(k′+q)`;
`π` = the first `k′` rows with the residue, `K` = all rows with the residue (it has the same
kernel as `(π, H)`); any blockings for `π`. Then
(i) the one-call algorithm answers YES iff a solution exists;
(ii) `𝖳_t ≤ e(2+e)p^{−t}sn²` for every `t ≤ k′+q` (the first `t` rows);
(iii) `Z(π) − Z₀ ≤ e(2+e)σn²` and `F ≤ e(2+e)σn²/D`;
(iv) `|𝒫₀| ≤ (p+16)n²/σ`, and `|𝒫₀| ≤ N²/√D` for `N = g′p^{q₁}`, `g′ ≥ (p+5)n/σ`, `q ≤ 2q₁`;
(v) lists 2 and 3 have at most `(p+1)n/σ` blocks. -/
theorem caseH (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (n σ s k q : ℕ) (hσ : 0 < σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (hTI : ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => residue (t.1 + t.2.1 + t.2.2) = 0).card ≤
      2 * s * n ^ 2)
    (hs₂ : ∀ x ∈ S₂, s ≤ (S₂.filter fun y => residue y = residue x).card)
    (hs₃ : ∀ x ∈ S₃, s ≤ (S₃.filter fun y => residue y = residue x).card)
    (hσD : (σ : ℝ) ^ 2 ≤ (p : ℝ) ^ q)
    (hsk : (s : ℝ) / σ ≤ (p : ℝ) ^ k) (hsk' : (p : ℝ) ^ k < p * s / σ)
    {ε : ℝ} {E : Multiset (VecP p d)} (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / ((k : ℝ) + q)) (rows : List (VecP p d)) (hlen : rows.length = k + q)
    (hg : IsGreedy E (Sp S₁ S₂ S₃) rows)
    (B₂ : Blocking S₂ (piHL (rows.drop q)) σ) (B₃ : Blocking S₃ (piHL (rows.drop q)) σ)
    (zr : Finset (Fin d → ZMod (p ^ 2)) → Fin d → ZMod (p ^ 2)) :
    (oneHashYes S₁ B₂ B₃ (piHL rows) zr Finset.univ ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) ∧
    (∀ j ≤ rows.length, Sp S₁ S₂ S₃ (rows.drop j) ≤
      Real.exp 1 * (2 + Real.exp 1) * (1 / (p : ℝ) ^ (rows.length - j)) * s * n ^ 2) ∧
    (Zc S₁ S₂ S₃ (piHL (rows.drop q)) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2 ∧
    (F (probes S₁ B₂ B₃) (piHL rows) : ℝ) ≤
      Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2 / (p : ℝ) ^ q ∧
    ((probes S₁ B₂ B₃).card : ℝ) ≤ (p + 16) * n ^ 2 / σ ∧
    (∀ g' q₁ : ℕ, ((p : ℝ) + 5) * n / σ ≤ g' → q ≤ 2 * q₁ →
      ((probes S₁ B₂ B₃).card : ℝ) ≤ ((g' : ℝ) * (p : ℝ) ^ q₁) ^ 2 / Real.sqrt ((p : ℝ) ^ q)) ∧
    (B₂.blocks.card : ℝ) ≤ (p + 1) * n / σ ∧ (B₃.blocks.card : ℝ) ≤ (p + 1) * n / σ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hσ1 : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hD : (0 : ℝ) < (p : ℝ) ^ q := pow_pos hp q
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hp k
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hε' : ε ≤ 1 / (rows.length : ℝ) := by rw [hlen]; push_cast; exact hε
  have c1 : (S₁.card : ℝ) ≤ n := by exact_mod_cast h₁
  have c2 : (S₂.card : ℝ) ≤ n := by exact_mod_cast h₂
  have c3 : (S₃.card : ℝ) ≤ n := by exact_mod_cast h₃
  -- `T_I` and `S′ ≤ T_I`
  have hT : ((tripI S₁ S₂ S₃).card : ℝ) ≤ 2 * s * n ^ 2 := by
    have hsub : tripI S₁ S₂ S₃ ⊆ (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t =>
        residue (t.1 + t.2.1 + t.2.2) = 0 := by
      intro t ht
      obtain ⟨hm, h1, -⟩ := Finset.mem_filter.1 ht
      exact Finset.mem_filter.2 ⟨hm, h1⟩
    have := (Finset.card_le_card hsub).trans hTI
    exact_mod_cast this
  have hSp_le : ∀ l, Sp S₁ S₂ S₃ l ≤ (tripI S₁ S₂ S₃).card := by
    intro l
    unfold Sp surv
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_filter_le _ _
  have hee : 2 * Real.exp 1 ≤ Real.exp 1 * (2 + Real.exp 1) := by nlinarith
  -- (ii)
  have hii : ∀ j ≤ rows.length, Sp S₁ S₂ S₃ (rows.drop j) ≤
      Real.exp 1 * (2 + Real.exp 1) * (1 / (p : ℝ) ^ (rows.length - j)) * s * n ^ 2 := by
    intro j hj
    have hpj : (0 : ℝ) < 1 / (p : ℝ) ^ (rows.length - j) := by positivity
    have hbase : Sp S₁ S₂ S₃ (rows.drop j) ≤
        Real.exp 1 * (1 / (p : ℝ) ^ (rows.length - j)) * (tripI S₁ S₂ S₃).card := by
      rcases Nat.lt_or_ge j rows.length with hlt | hge
      · exact partH_choice S₁ S₂ S₃ hE hε0 rows hg hε' j hlt
      · have hj' : j = rows.length := le_antisymm hj hge
        subst hj'
        rw [Nat.sub_self, pow_zero, div_one, mul_one]
        have := hSp_le (rows.drop rows.length)
        have h0 : (0 : ℝ) ≤ (tripI S₁ S₂ S₃).card := Nat.cast_nonneg _
        nlinarith
    calc Sp S₁ S₂ S₃ (rows.drop j)
        ≤ Real.exp 1 * (1 / (p : ℝ) ^ (rows.length - j)) * (tripI S₁ S₂ S₃).card := hbase
      _ ≤ Real.exp 1 * (1 / (p : ℝ) ^ (rows.length - j)) * (2 * s * n ^ 2) := by gcongr
      _ = 2 * Real.exp 1 * (1 / (p : ℝ) ^ (rows.length - j)) * s * n ^ 2 := by ring
      _ ≤ Real.exp 1 * (2 + Real.exp 1) * (1 / (p : ℝ) ^ (rows.length - j)) * s * n ^ 2 := by
          gcongr
  -- (iii)
  have hx : 1 / (p : ℝ) ^ k * s ≤ σ := by
    rw [div_le_iff₀ hσR] at hsk
    rw [one_div, inv_mul_le_iff₀ hpk]; linarith
  have hZπ : (Zc S₁ S₂ S₃ (piHL (rows.drop q)) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2 := by
    have e := Sp_eq_Zc S₁ S₂ S₃ (rows.drop q)
    have h := hii q (by omega)
    rw [show rows.length - q = k by omega] at h
    unfold piHL
    rw [← e]
    refine h.trans ?_
    calc Real.exp 1 * (2 + Real.exp 1) * (1 / (p : ℝ) ^ k) * s * n ^ 2
        = Real.exp 1 * (2 + Real.exp 1) * (1 / (p : ℝ) ^ k * s) * n ^ 2 := by ring
      _ ≤ Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2 := by gcongr
  have hfactor : ∀ x, piHL rows x = 0 → piHL (rows.drop q) x = 0 := by
    intro x hx0
    unfold piHL at hx0 ⊢
    rw [piH_eq_zero_iff] at hx0 ⊢
    exact ⟨hx0.1, fun a ha => hx0.2 a (List.mem_of_mem_drop ha)⟩
  have hF : (F (probes S₁ B₂ B₃) (piHL rows) : ℝ) ≤
      Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2 / (p : ℝ) ^ q := by
    have e := F_probes_eq (S₁ := S₁) B₂ B₃ (piHL rows) hfactor
    have e' := congrArg (Int.cast : ℤ → ℝ) e
    push_cast at e'
    rw [e']
    have e2 := Sp_eq_Zc S₁ S₂ S₃ rows
    unfold piHL
    rw [← e2]
    have h := hii 0 (Nat.zero_le _)
    rw [Nat.sub_zero, List.drop_zero, hlen] at h
    refine h.trans ?_
    rw [le_div_iff₀ hD]
    calc Real.exp 1 * (2 + Real.exp 1) * (1 / (p : ℝ) ^ (k + q)) * s * n ^ 2 * (p : ℝ) ^ q
        = Real.exp 1 * (2 + Real.exp 1) * (1 / (p : ℝ) ^ k * s) * n ^ 2 := by
          rw [pow_add]; field_simp
      _ ≤ Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2 := by gcongr
  -- the nonempty `π`-classes of lists 2 and 3
  have hN : ∀ S : Finset (Fin d → ZMod (p ^ 2)), S.card ≤ n →
      (∀ x ∈ S, s ≤ (S.filter fun y => residue y = residue x).card) →
      ((S.image (piHL (rows.drop q))).card : ℝ) ≤ p * n / σ := by
    intro S hS hcl
    have himg : S.image (piHL (rows.drop q)) = S.image fun x =>
        (residue x, fun i : Fin (rows.drop q).length => lift ((rows.drop q).get i) ⬝ᵥ x) := rfl
    have hk : (rows.drop q).length = k := by rw [List.length_drop]; omega
    have h1 : (S.image (piHL (rows.drop q))).card ≤ (S.image residue).card * p ^ k := by
      calc (S.image (piHL (rows.drop q))).card
          ≤ (S.image residue).card * p ^ (rows.drop q).length := by
            rw [himg]; exact classes_card_le S _
        _ = (S.image residue).card * p ^ k := by rw [hk]
    have h2 := card_image_residue_mul_le S s hcl
    have h1' : ((S.image (piHL (rows.drop q))).card : ℝ) ≤ (S.image residue).card * (p : ℝ) ^ k := by
      exact_mod_cast h1
    have h2' : ((S.image residue).card : ℝ) * s ≤ n := by
      have : (S.image residue).card * s ≤ n := h2.trans hS
      exact_mod_cast this
    have hR0 : (0 : ℝ) ≤ (S.image residue).card := Nat.cast_nonneg _
    calc ((S.image (piHL (rows.drop q))).card : ℝ)
        ≤ (S.image residue).card * (p : ℝ) ^ k := h1'
      _ ≤ (S.image residue).card * (p * s / σ) := by gcongr
      _ = p * ((S.image residue).card * s) / σ := by ring
      _ ≤ p * n / σ := by gcongr
  -- (iv)
  have hP := probes_card_le (S₁ := S₁) hσ B₂ B₃
  have hZ0 : (Zsol S₁ S₂ S₃ : ℝ) ≤ n ^ 2 := by
    have : (Zsol S₁ S₂ S₃ : ℝ) ≤ S₁.card * S₂.card := by exact_mod_cast Zsol_le S₁ S₂ S₃
    nlinarith [Nat.cast_nonneg (α := ℝ) S₁.card, Nat.cast_nonneg (α := ℝ) S₂.card]
  have t1 : (S₁.card : ℝ) * (S₂.image (piHL (rows.drop q))).card ≤ n * (p * n / σ) :=
    mul_le_mul c1 (hN S₂ h₂ hs₂) (Nat.cast_nonneg _) hn0
  have t2 : (S₁.card : ℝ) * ((S₂.card + S₃.card) / σ) ≤ n * ((n + n) / σ) := by gcongr
  have t3 : (Zc S₁ S₂ S₃ (piHL (rows.drop q)) : ℝ) / σ ^ 2 ≤
      (1 + Real.exp 1 * (2 + Real.exp 1)) * n ^ 2 / σ := by
    have hZ : (Zc S₁ S₂ S₃ (piHL (rows.drop q)) : ℝ) ≤
        n ^ 2 + Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2 := by linarith
    have hn2 : (0 : ℝ) ≤ n ^ 2 := by positivity
    have hσσ : (σ : ℝ) ≤ σ ^ 2 := by nlinarith
    calc (Zc S₁ S₂ S₃ (piHL (rows.drop q)) : ℝ) / σ ^ 2
        ≤ (n ^ 2 + Real.exp 1 * (2 + Real.exp 1) * σ * n ^ 2) / σ ^ 2 :=
          div_le_div_of_nonneg_right hZ (by positivity)
      _ = n ^ 2 / σ ^ 2 + Real.exp 1 * (2 + Real.exp 1) * n ^ 2 / σ := by
          rw [add_div]; congr 1; rw [div_eq_div_iff (by positivity) hσR.ne']; ring
      _ ≤ n ^ 2 / σ + Real.exp 1 * (2 + Real.exp 1) * n ^ 2 / σ := by
          have := div_le_div_of_nonneg_left hn2 hσR hσσ
          linarith
      _ = (1 + Real.exp 1 * (2 + Real.exp 1)) * n ^ 2 / σ := by ring
  have hPle : ((probes S₁ B₂ B₃).card : ℝ) ≤
      (p + 3 + Real.exp 1 * (2 + Real.exp 1)) * n ^ 2 / σ := by
    have : n * (p * n / σ) + n * ((n + n) / σ) +
        (1 + Real.exp 1 * (2 + Real.exp 1)) * n ^ 2 / σ =
        (p + 3 + Real.exp 1 * (2 + Real.exp 1)) * n ^ 2 / σ := by
      field_simp; ring
    linarith
  have hn2σ : (0 : ℝ) ≤ n ^ 2 / σ := by positivity
  have hP16 : ((probes S₁ B₂ B₃).card : ℝ) ≤ (p + 16) * n ^ 2 / σ := by
    refine hPle.trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hn2σ
    have h := Real.exp_one_lt_d9
    nlinarith
  refine ⟨detection_correct_univ B₂ B₃ _ zr, hii, hZπ, hF, hP16, ?_, ?_, ?_⟩
  · intro g' q₁ hg' hq₁
    have hsqrt : (σ : ℝ) ≤ Real.sqrt ((p : ℝ) ^ q) := Real.le_sqrt_of_sq_le hσD
    have hs0' : (0 : ℝ) < Real.sqrt ((p : ℝ) ^ q) := Real.sqrt_pos.2 hD
    have hpq₁ : (p : ℝ) ^ q ≤ ((p : ℝ) ^ q₁) ^ 2 := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    have hA : ((p : ℝ) + 5) ^ 2 * n ^ 2 / σ ≤ ((g' : ℝ) * (p : ℝ) ^ q₁) ^ 2 /
        Real.sqrt ((p : ℝ) ^ q) := by
      rw [le_div_iff₀ hs0']
      have hgg : (((p : ℝ) + 5) * n / σ) ^ 2 ≤ (g' : ℝ) ^ 2 := by
        have : 0 ≤ ((p : ℝ) + 5) * n / σ := by positivity
        nlinarith
      have hsq : Real.sqrt ((p : ℝ) ^ q) * Real.sqrt ((p : ℝ) ^ q) = (p : ℝ) ^ q :=
        Real.mul_self_sqrt hD.le
      calc ((p : ℝ) + 5) ^ 2 * n ^ 2 / σ * Real.sqrt ((p : ℝ) ^ q)
          = (((p : ℝ) + 5) * n / σ) ^ 2 * (σ * Real.sqrt ((p : ℝ) ^ q)) := by
            field_simp
        _ ≤ (g' : ℝ) ^ 2 * (Real.sqrt ((p : ℝ) ^ q) * Real.sqrt ((p : ℝ) ^ q)) := by
            gcongr
        _ = (g' : ℝ) ^ 2 * (p : ℝ) ^ q := by rw [hsq]
        _ ≤ (g' : ℝ) ^ 2 * ((p : ℝ) ^ q₁) ^ 2 := by gcongr
        _ = ((g' : ℝ) * (p : ℝ) ^ q₁) ^ 2 := by ring
    refine le_trans ?_ hA
    refine hP16.trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hn2σ
    nlinarith
  · have hb := B₂.card_le' hσ
    have hc := hN S₂ h₂ hs₂
    have hs : (S₂.card : ℝ) / σ ≤ n / σ := div_le_div_of_nonneg_right c2 hσR.le
    have he' : ((p : ℝ) + 1) * n / σ = p * n / σ + n / σ := by ring
    linarith
  · have hb := B₃.card_le' hσ
    have hc := hN S₃ h₃ hs₃
    have hs : (S₃.card : ℝ) / σ ≤ n / σ := div_le_div_of_nonneg_right c3 hσR.le
    have he' : ((p : ℝ) + 1) * n / σ = p * n / σ + n / σ := by ring
    linarith

end partH

end FpBounds
end GroupLean

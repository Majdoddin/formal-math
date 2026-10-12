import XorLean.ImprovedProbes

/-!
# Improved 3XOR, Theorem I′ (§3.2): one hash, one detection call, non-adaptive

The rows `u₁, …, u_{k+q}` are chosen one at a time from a `(1/(k+q))`-biased `E`, each
minimizing the global count `Z` of the map formed so far (no oracle: `Z` is a XOR-convolution,
`two_pow_mul_Zc`). With rows newest first (X3), the list `rows` of length `k+q` has the `q`
last-chosen rows `rows.take q` (the map `H`) in front of the `k` first-chosen rows
`rows.drop q` (the map `π`).
-/

set_option linter.unusedSectionVars false

namespace Xor.Improved
open Xor Finset

variable {d : ℕ}

/-- A greedy sequence stays greedy when its newest rows are dropped (its prefixes in the text's
order). -/
theorem isGreedy_drop {ℓ : ℕ} (E : Multiset (Vec ℓ)) (f : List (Vec ℓ) → ℝ) (rows : List (Vec ℓ))
    (hg : IsGreedy E f rows) (j : ℕ) : IsGreedy E f (rows.drop j) := by
  induction j generalizing rows with
  | zero => simpa using hg
  | succ j ih =>
    cases rows with
    | nil => trivial
    | cons u rs => exact ih rs hg.1

/-- A bias bound can be loosened. -/
theorem isBiased_mono {ℓ : ℕ} {ε ε' : ℝ} {E : Multiset (Vec ℓ)} (hE : IsBiased ε E)
    (h : ε ≤ ε') : IsBiased ε' E :=
  ⟨hE.1, fun v hv => (hE.2 v hv).trans
    (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))⟩

/-- A block is determined by its label and any of its elements. -/
theorem Blocking.unique {S : Finset (Vec d)} {k : ℕ} {π : Vec d →ₗ[ZMod 2] Vec k} {σ : ℕ}
    (B : Blocking S π σ) {β β' : Vec k} {b b' : Finset (Vec d)} {x : Vec d}
    (hb : b ∈ B.blocks β) (hb' : b' ∈ B.blocks β') (hx : x ∈ b) (hx' : x ∈ b') :
    β = β' ∧ b = b' := by
  have e := (Finset.mem_filter.1 (B.sub _ _ hb hx)).2
  have e' := (Finset.mem_filter.1 (B.sub _ _ hb' hx')).2
  have hββ : β = β' := e.symm.trans e'
  subst hββ
  exact ⟨rfl, (B.cover β x (B.sub _ _ hb hx)).unique ⟨hb, hx⟩ ⟨hb', hx'⟩⟩

/-- `(1 + 1/(k+q))^k ≤ e` for every prefix length `k ≤ k + q`. -/
theorem one_add_inv_pow_le_exp' (r j : ℕ) (hr : 0 < r) (hj : j ≤ r) :
    (1 + 1 / (r : ℝ)) ^ j ≤ Real.exp 1 :=
  (pow_le_pow_right₀ (by have : (0 : ℝ) ≤ 1 / r := by positivity
                         linarith) hj).trans (one_add_inv_pow_le_exp r hr)

/-- **"The hash"** of Theorem I′: Lemma 5 for every prefix of the greedy sequence. For the first
`m` rows (`0 < m ≤ k + q`): `Z − Z₀ ≤ e 2^{-m} |S₁||S₂||S₃|`. With `m = k` this bounds `Z(π)`,
with `m = k + q` it bounds `F = Z((π,H)) − Z₀`. -/
theorem oneHash_prefix_le (S₁ S₂ S₃ : Finset (Vec d)) (E : Multiset (Vec d))
    (rows : List (Vec d)) (hE : IsBiased (1 / (rows.length : ℝ)) E)
    (hg : IsGreedy E (fun l => (Zc S₁ S₂ S₃ (rowsMap l) : ℝ)) rows) (j : ℕ)
    (hj : j < rows.length) :
    (Zc S₁ S₂ S₃ (rowsMap (rows.drop j)) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * (2 : ℝ)⁻¹ ^ (rows.length - j) * (S₁.card * S₂.card * S₃.card) := by
  have hlen : (rows.drop j).length = rows.length - j := List.length_drop ..
  have hpos : 0 < (rows.drop j).length := by omega
  have hb := Zc_greedy_le S₁ S₂ S₃ hE (by positivity) (rows.drop j) (isGreedy_drop E _ rows hg j)
    hpos (by
      rw [hlen]
      have : (0 : ℝ) < (rows.length - j : ℕ) := by exact_mod_cast (show 0 < rows.length - j by omega)
      have h2 : ((rows.length - j : ℕ) : ℝ) ≤ rows.length := by exact_mod_cast Nat.sub_le _ _
      exact one_div_le_one_div_of_le this h2)
  have hp : (2 : ℝ)⁻¹ ^ (rows.drop j).length = (2 : ℝ)⁻¹ ^ (rows.length - j) := by rw [hlen]
  rw [hp] at hb
  exact hb

/-- Every triple with `π(s) = 0` lies in exactly one probe, so `Σ_{Q∈𝒫₀} cnt_H(Q)` is the
number of triples that both `π` and `H` send to `0`. -/
theorem sum_cnt_probes (S₁ S₂ S₃ : Finset (Vec d)) {k m : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k)
    {σ : ℕ} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (H : Vec d →ₗ[ZMod 2] Vec m) :
    ∑ Q ∈ probes S₁ π B₂ B₃, (probeCands d k).cnt H Q =
      ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t =>
        π (t.1 + t.2.1 + t.2.2) = 0 ∧ H (t.1 + t.2.1 + t.2.2) = 0).card := by
  have hlhs : ∑ Q ∈ probes S₁ π B₂ B₃, (probeCands d k).cnt H Q =
      ((probes S₁ π B₂ B₃).sigma fun Q => ((probeCands d k).fam Q).filter
        fun p => H ((probeCands d k).vec Q p) = 0).card := by
    rw [Finset.card_sigma]; rfl
  rw [hlhs]
  refine Finset.card_bij (fun a _ => (a.1.1, a.2.1, a.2.2)) ?_ ?_ ?_
  · rintro ⟨⟨x₁, ⟨β₂, b₂⟩, ⟨β₃, b₃⟩⟩, x₂, x₃⟩ ha
    rw [Finset.mem_sigma] at ha
    obtain ⟨hQ, hp⟩ := ha
    rw [Finset.mem_filter] at hp
    simp only [probeCands, Finset.mem_product] at hp
    simp only [probes, Blocking.set, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at hQ
    obtain ⟨⟨h1, hb2, hb3⟩, hlab⟩ := hQ
    obtain ⟨⟨h2, h3⟩, hH⟩ := hp
    have s2 := Finset.mem_filter.1 (B₂.sub _ _ hb2 h2)
    have s3 := Finset.mem_filter.1 (B₃.sub _ _ hb3 h3)
    simp only [Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨h1, s2.1, s3.1⟩, ?_, hH⟩
    rw [map_add, map_add, s2.2, s3.2, hlab]
    exact vadd_self _
  · rintro ⟨⟨x₁, ⟨β₂, b₂⟩, ⟨β₃, b₃⟩⟩, x₂, x₃⟩ ha ⟨⟨x₁', ⟨β₂', b₂'⟩, ⟨β₃', b₃'⟩⟩, x₂', x₃'⟩ ha' h
    rw [Finset.mem_sigma] at ha ha'
    obtain ⟨hQ, hp⟩ := ha
    obtain ⟨hQ', hp'⟩ := ha'
    rw [Finset.mem_filter] at hp hp'
    simp only [probeCands, Finset.mem_product] at hp hp'
    simp only [probes, Blocking.set, Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      true_and] at hQ hQ'
    simp only [Prod.mk.injEq] at h
    obtain ⟨e1, e2, e3⟩ := h
    subst e1 e2 e3
    obtain ⟨r2, r2'⟩ := B₂.unique hQ.1.2.1 hQ'.1.2.1 hp.1.1 hp'.1.1
    obtain ⟨r3, r3'⟩ := B₃.unique hQ.1.2.2 hQ'.1.2.2 hp.1.2 hp'.1.2
    subst r2 r2' r3 r3'
    rfl
  · rintro ⟨x₁, x₂, x₃⟩ ht
    simp only [Finset.mem_filter, Finset.mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, hπ, hH⟩ := ht
    obtain ⟨b₂, ⟨hb₂, hx₂⟩, -⟩ := B₂.cover (π x₂) x₂ (Finset.mem_filter.2 ⟨h2, rfl⟩)
    obtain ⟨b₃, ⟨hb₃, hx₃⟩, -⟩ := B₃.cover (π x₃) x₃ (Finset.mem_filter.2 ⟨h3, rfl⟩)
    refine ⟨⟨(x₁, (π x₂, b₂), (π x₃, b₃)), x₂, x₃⟩, ?_, rfl⟩
    rw [Finset.mem_sigma, Finset.mem_filter]
    simp only [probeCands, Finset.mem_product, probes, Blocking.set, Finset.mem_filter,
      Finset.mem_univ, true_and]
    refine ⟨⟨⟨h1, hb₂, hb₃⟩, ?_⟩, ⟨hx₂, hx₃⟩, hH⟩
    rw [map_add, map_add] at hπ
    exact (vsum_zero_iff _ _ _).1 hπ

/-- `Σ_{Q∈𝒫₀} z(Q) = Z₀`. -/
theorem sum_z_probes (S₁ S₂ S₃ : Finset (Vec d)) {k : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k)
    {σ : ℕ} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) :
    ∑ Q ∈ probes S₁ π B₂ B₃, (probeCands d k).z Q = Zsol S₁ S₂ S₃ := by
  have : ∀ Q, (probeCands d k).z Q = (probeCands d k).cnt (LinearMap.id) Q := fun Q => rfl
  simp only [this]
  rw [sum_cnt_probes]
  unfold Zsol
  congr 1
  apply Finset.filter_congr
  intro t _
  simp only [LinearMap.id_apply]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h; exact ⟨by rw [h, map_zero], h⟩

/-- With `π = rowsMap πrows` and `H = rowsMap Hrows`, `(π, H)` is `rowsMap (Hrows ++ πrows)`, and
the false positives over all probes are `F = Z((π,H)) − Z₀` (§3.2, after the display). -/
theorem F_probes_eq (S₁ S₂ S₃ : Finset (Vec d)) (πrows Hrows : List (Vec d)) {σ : ℕ}
    (B₂ : Blocking S₂ (rowsMap πrows) σ) (B₃ : Blocking S₃ (rowsMap πrows) σ) :
    ((probeCands d πrows.length).F (probes S₁ (rowsMap πrows) B₂ B₃) (rowsMap Hrows) : ℝ) =
      (Zc S₁ S₂ S₃ (rowsMap (Hrows ++ πrows)) : ℝ) - Zsol S₁ S₂ S₃ := by
  have h1 := (probeCands d πrows.length).sum_cnt_eq (probes S₁ (rowsMap πrows) B₂ B₃)
    (rowsMap Hrows)
  rw [sum_cnt_probes, sum_z_probes] at h1
  have h2 : ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => rowsMap πrows (t.1 + t.2.1 + t.2.2) = 0 ∧
      rowsMap Hrows (t.1 + t.2.1 + t.2.2) = 0).card = Zc S₁ S₂ S₃ (rowsMap (Hrows ++ πrows)) := by
    unfold Zc
    congr 1
    apply Finset.filter_congr
    intro t _
    simp only [rowsMap_eq_zero_iff, List.mem_append]
    constructor
    · rintro ⟨ha, hb⟩ u (hu | hu)
      · exact hb u hu
      · exact ha u hu
    · intro h; exact ⟨fun u hu => h u (Or.inr hu), fun u hu => h u (Or.inl hu)⟩
  rw [h2] at h1
  rw [h1]; push_cast; ring

/-- The support instance of step 3 (`X' = [X > 0]`, `Y' = [Y > 0]`) for the detection oracle. -/
def suppInst {R K M : Type*} [Fintype M] (X : R → M → ℕ) (Y : M → K → ℕ)
    (W : Finset (R × K)) : LopInst R K M where
  mid := univ
  adjA r w := 0 < X r w
  adjB w c := 0 < Y w c
  W := W

/-- `(X'Y') > 0` iff `(XY) > 0`. -/
theorem suppInst_accepts {R K M : Type*} [Fintype M] (X : R → M → ℕ) (Y : M → K → ℕ)
    (W : Finset (R × K)) (r : R) (c : K) :
    (suppInst X Y W).Accepts r c ↔ 0 < ∑ w, X r w * Y w c := by
  rw [Finset.sum_pos_iff]
  simp only [LopInst.Accepts, suppInst, Finset.mem_univ, true_and,
    Nat.pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

/-- A probe is flagged by the detection oracle iff `cnt_H(Q) > 0` (Lemma II.2). -/
theorem flagged_iff {k l₁ l₂ : ℕ} (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂))
    (W : Finset ((Finset (Vec d) × Vec l₁) × (Finset (Vec d) × Vec l₂))) (Q : Probe d k) :
    (suppInst (matX H) (matY H) W).Accepts (pos H Q).1 (pos H Q).2 ↔
      0 < (probeCands d k).cnt H Q := by
  rw [suppInst_accepts, matXY_pos]

/-- The answer of Theorem I′'s algorithm: some probe is flagged by the one detection call and
its scan (step 4) finds a solution. -/
def oneHashYes (S₁ S₂ S₃ : Finset (Vec d)) {k l₁ l₂ : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k) {σ : ℕ}
    (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) : Prop :=
  ∃ Q ∈ probes S₁ π B₂ B₃,
    (suppInst (matX H) (matY H) ((probes S₁ π B₂ B₃).image (pos H))).Accepts
      (pos H Q).1 (pos H Q).2 ∧ ∃ x₂ ∈ Q.2.1.2, Q.1 + x₂ ∈ Q.2.2.2

/-- **Theorem I′, correctness**: for every linear `π`, blocks and `H` (with at least one row
or not), the algorithm answers YES iff the instance has a solution; a NO is correct and a
returned triple is a solution. -/
theorem xor_direct_detection_correct (S₁ S₂ S₃ : Finset (Vec d)) {k l₁ l₂ : ℕ} (π : Vec d →ₗ[ZMod 2] Vec k)
    {σ : ℕ} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) :
    oneHashYes S₁ S₂ S₃ π B₂ B₃ H ↔ ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0 := by
  rw [exists_sol_iff_probe S₁ S₂ S₃ π B₂ B₃]
  unfold oneHashYes
  constructor
  · rintro ⟨Q, hQ, -, hs⟩
    exact ⟨Q, hQ, (probe_z_pos_iff Q).2 hs⟩
  · rintro ⟨Q, hQ, hz⟩
    refine ⟨Q, hQ, (flagged_iff H _ Q).2 (lt_of_lt_of_le hz ((probeCands d k).z_le_cnt H Q)),
      (probe_z_pos_iff Q).1 hz⟩

/-- **Theorem I′, "Scans"**: the flagged probes without a solution are at most `F` (each holds a
false positive). -/
theorem failed_scans_le {k m : ℕ} (P : Finset (Probe d k)) (H : Vec d →ₗ[ZMod 2] Vec m) :
    (P.filter fun Q => 0 < (probeCands d k).cnt H Q ∧ (probeCands d k).z Q = 0).card ≤
      (probeCands d k).F P H := by
  calc (P.filter fun Q => 0 < (probeCands d k).cnt H Q ∧ (probeCands d k).z Q = 0).card
      = ∑ _Q ∈ P.filter (fun Q => 0 < (probeCands d k).cnt H Q ∧ (probeCands d k).z Q = 0), 1 := by
        simp
    _ ≤ ∑ Q ∈ P.filter (fun Q => 0 < (probeCands d k).cnt H Q ∧ (probeCands d k).z Q = 0),
          (probeCands d k).fp H Q := by
        refine Finset.sum_le_sum fun Q hQ => ?_
        have h := (Finset.mem_filter.1 hQ).2
        have e := (probeCands d k).cnt_eq_fp_add_z H Q
        omega
    _ ≤ (probeCands d k).F P H := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- **Theorem I′, the bounds of "The hash"** together: with `k + q` greedy rows (`k, q ≥ 1`)
from a `(1/(k+q))`-biased `E`, lists of at most `n` elements and `n/σ ≤ 2^k`:
`Z(π) − Z₀ ≤ eσn²`, `Z(π) ≤ (eσ+1)n²`, and `F = Z((π,H)) − Z₀ ≤ e 2^{-(k+q)} n³ ≤ eσn²/2^q`. -/
theorem oneHash_bounds (S₁ S₂ S₃ : Finset (Vec d)) (n σ q : ℕ) (hσ : 0 < σ)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (E : Multiset (Vec d)) (rows : List (Vec d)) (hq : 0 < q) (hk : q < rows.length)
    (hE : IsBiased (1 / (rows.length : ℝ)) E)
    (hg : IsGreedy E (fun l => (Zc S₁ S₂ S₃ (rowsMap l) : ℝ)) rows)
    (h2k : (n : ℝ) / σ ≤ 2 ^ (rows.length - q)) :
    (Zc S₁ S₂ S₃ (rowsMap (rows.drop q)) : ℝ) - Zsol S₁ S₂ S₃ ≤ Real.exp 1 * σ * n ^ 2 ∧
    (Zc S₁ S₂ S₃ (rowsMap (rows.drop q)) : ℝ) ≤ (Real.exp 1 * σ + 1) * n ^ 2 ∧
    (Zc S₁ S₂ S₃ (rowsMap rows) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * n ^ 3 ∧
    (Zc S₁ S₂ S₃ (rowsMap rows) : ℝ) - Zsol S₁ S₂ S₃ ≤ Real.exp 1 * σ * n ^ 2 / 2 ^ q := by
  have hlen : (rows.drop q).length = rows.length - q := List.length_drop ..
  have hpos : 0 < (rows.drop q).length := by omega
  have hE' : IsBiased (1 / ((rows.drop q).length : ℝ)) E := by
    refine isBiased_mono hE ?_
    rw [hlen]
    have : (0 : ℝ) < (rows.length - q : ℕ) := by exact_mod_cast (show 0 < rows.length - q by omega)
    have h2 : ((rows.length - q : ℕ) : ℝ) ≤ rows.length := by exact_mod_cast Nat.sub_le _ _
    exact one_div_le_one_div_of_le this h2
  obtain ⟨hA, hB⟩ := Zc_pi_le S₁ S₂ S₃ n σ hσ h₁ h₂ h₃ E (rows.drop q) hpos hE'
    (isGreedy_drop E _ rows hg q) (by rw [hlen]; exact h2k)
  have hfull := oneHash_prefix_le S₁ S₂ S₃ E rows hE hg 0 (by omega)
  simp only [Nat.sub_zero] at hfull
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have c1 : (S₁.card : ℝ) ≤ n := by exact_mod_cast h₁
  have c2 : (S₂.card : ℝ) ≤ n := by exact_mod_cast h₂
  have c3 : (S₃.card : ℝ) ≤ n := by exact_mod_cast h₃
  have hprod : (S₁.card * S₂.card * S₃.card : ℝ) ≤ n ^ 3 := by
    have := mul_le_mul (mul_le_mul c1 c2 (Nat.cast_nonneg _) hn0) c3 (Nat.cast_nonneg _)
      (by positivity)
    nlinarith
  have h3 : (Zc S₁ S₂ S₃ (rowsMap rows) : ℝ) - Zsol S₁ S₂ S₃ ≤
      Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * n ^ 3 :=
    hfull.trans (mul_le_mul_of_nonneg_left hprod (by positivity))
  refine ⟨hA, hB, h3, h3.trans_eq' ?_ |>.trans ?_⟩
  · rfl
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hsplit : rows.length = (rows.length - q) + q := by omega
  have hpow : (2 : ℝ)⁻¹ ^ (rows.length - q) * n ≤ σ := by
    rw [div_le_iff₀ hσR] at h2k
    rw [inv_pow, inv_mul_le_iff₀ (by positivity)]
    linarith
  calc Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * n ^ 3
      = Real.exp 1 * ((2 : ℝ)⁻¹ ^ (rows.length - q) * n) * n ^ 2 / 2 ^ q := by
        rw [hsplit, pow_add]
        simp only [Nat.add_sub_cancel, inv_pow]
        field_simp
    _ ≤ Real.exp 1 * σ * n ^ 2 / 2 ^ q := by gcongr

end Xor.Improved

import Mathlib

/-!
# Theorem A over an arbitrary abelian group: correctness and counts

The paper's Section 19.3 (Lemmas 19.6 and 19.7; "Correctness"), Theorem 19.8 ("The hash",
"Counts") and the instance of Section 19.6 (Theorem 19.17, "Instance": middle part `K(ker π)`, representatives `z_b`).

Everything is stated for an arbitrary additive commutative group `G` (with decidable equality),
three lists `S₁ S₂ S₃ : Finset G` (step (0) removes repeated vectors), a grouping homomorphism
`π : G →+ P` and a hash homomorphism `K : G →+ R`. Where `π` has to factor through `K` (the
probes then partition the triples with `K(sum) = 0`) this is the hypothesis
`hKπ : ∀ x, K x = 0 → π x = 0`.

Generalized from XorLean's `ImprovedProbes.lean` / `ImprovedOneHash.lean` (there: `G = F₂^d`,
linear maps). Differences: blocks are not indexed by a label type (the label space `P` may be
infinite); a blocking carries a label function with `π x = label b` for `x ∈ b`, and blocks are
nonempty. The probe condition is `π x₁ + label b₂ + label b₃ = 0`; a scan looks up `-(x₁ + x₂)`.
-/

set_option linter.unusedSectionVars false

namespace GroupLean
namespace OneHash

open Finset

/-! ### Cutting a finite set into small parts -/

/-- A finite set is cut into at most `⌈|X|/L⌉` nonempty parts of at most `L` elements, every
element in exactly one part (XorLean `exists_cutting`, plus nonemptiness of the parts). -/
theorem exists_cutting {α : Type*} [DecidableEq α] (X : Finset α) (L : ℕ) (hL : 0 < L) :
    ∃ parts : Finset (Finset α), (∀ Y ∈ parts, Y ⊆ X ∧ Y.card ≤ L ∧ Y.Nonempty) ∧
      (∀ x ∈ X, ∃! Y, Y ∈ parts ∧ x ∈ Y) ∧ parts.card ≤ (X.card + L - 1) / L := by
  induction X using Finset.strongInduction with
  | H X ih =>
  rcases X.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, by simp, by simp, by simp⟩
  obtain ⟨Y, hYX, hYc⟩ := Finset.exists_subset_card_eq (min_le_right L X.card)
  have hYne : Y.Nonempty := Finset.card_pos.1 (by rw [hYc]; exact lt_min hL hne.card_pos)
  obtain ⟨parts, h1, h2, h3⟩ := ih _ (Finset.sdiff_ssubset hYX hYne)
  refine ⟨insert Y parts, ?_, ?_, ?_⟩
  · intro Z hZ
    rcases Finset.mem_insert.1 hZ with rfl | hZ
    · exact ⟨hYX, hYc ▸ min_le_left _ _, hYne⟩
    · exact ⟨(h1 Z hZ).1.trans Finset.sdiff_subset, (h1 Z hZ).2.1, (h1 Z hZ).2.2⟩
  · intro x hx
    by_cases hxY : x ∈ Y
    · refine ⟨Y, ⟨Finset.mem_insert_self _ _, hxY⟩, ?_⟩
      rintro Z ⟨hZ, hxZ⟩
      rcases Finset.mem_insert.1 hZ with rfl | hZ
      · rfl
      · exact absurd hxY (Finset.mem_sdiff.1 ((h1 Z hZ).1 hxZ)).2
    · obtain ⟨Z, ⟨hZ, hxZ⟩, huniq⟩ := h2 x (Finset.mem_sdiff.2 ⟨hx, hxY⟩)
      refine ⟨Z, ⟨Finset.mem_insert_of_mem hZ, hxZ⟩, ?_⟩
      rintro W ⟨hW, hxW⟩
      rcases Finset.mem_insert.1 hW with rfl | hW
      · exact absurd hxW hxY
      · exact huniq W ⟨hW, hxW⟩
  · rw [Finset.card_sdiff_of_subset hYX, hYc] at h3
    have hn := hne.card_pos
    refine (Finset.card_insert_le _ _).trans ?_
    rcases le_total L X.card with hLX | hXL
    · rw [min_eq_left hLX] at h3
      have : X.card + L - 1 = (X.card - L + L - 1) + L := by omega
      rw [this, Nat.add_div_right _ hL]
      omega
    · rw [min_eq_right hXL] at h3
      have h0 : (X.card - X.card + L - 1) / L = 0 := Nat.div_eq_of_lt (by omega)
      rw [h0] at h3
      have : 1 ≤ (X.card + L - 1) / L := (Nat.le_div_iff_mul_le hL).2 (by omega)
      omega

variable {G P R : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup P] [DecidableEq P]
  [AddCommGroup R] [DecidableEq R]

/-- `a + b + c = 0 ↔ c = -(a + b)`. -/
theorem sum3_eq_zero_iff (a b c : G) : a + b + c = 0 ↔ c = -(a + b) :=
  ⟨eq_neg_of_add_eq_zero_right, by rintro rfl; exact add_neg_cancel _⟩

/-! ### `Z(K)` and `Z₀` -/

/-- `Z(K)`: the triples of `S₁ × S₂ × S₃` with `K(x₁ + x₂ + x₃) = 0`. -/
def Zc (S₁ S₂ S₃ : Finset G) (K : G →+ R) : ℕ :=
  ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => K (t.1 + t.2.1 + t.2.2) = 0).card

/-- `Z₀`: the solutions, `x₁ + x₂ + x₃ = 0`. -/
def Zsol (S₁ S₂ S₃ : Finset G) : ℕ :=
  ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => t.1 + t.2.1 + t.2.2 = 0).card

/-- `Z₀ ≤ |S₁| |S₂|` (`x₁, x₂` determine `x₃`). -/
theorem Zsol_le (S₁ S₂ S₃ : Finset G) : Zsol S₁ S₂ S₃ ≤ S₁.card * S₂.card := by
  unfold Zsol
  rw [← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.1)) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at ht
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe]
    exact ⟨ht.1.1, ht.1.2.1⟩
  · intro t ht t' ht' h
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht ht'
    simp only [Prod.mk.injEq] at h
    have h3 := (sum3_eq_zero_iff _ _ _).1 ht.2
    have h3' := (sum3_eq_zero_iff _ _ _).1 ht'.2
    exact Prod.ext h.1 (Prod.ext h.2 (by rw [h3, h3', h.1, h.2]))

/-- `Z(id) = Z₀`. -/
theorem Zc_id (S₁ S₂ S₃ : Finset G) : Zc S₁ S₂ S₃ (AddMonoidHom.id G) = Zsol S₁ S₂ S₃ := rfl

/-! ### Blocks -/

/-- A blocking of the list `S` with respect to `π` with block size `σ`: nonempty, pairwise
disjoint blocks (every element of `S` in exactly one block) covering `S`, each inside one
`π`-class (`π x = label b` for `x ∈ b`), each of at most `σ` elements, and the class with label
`c` cut into at most `⌈|class c|/σ⌉` blocks. -/
structure Blocking (S : Finset G) (π : G →+ P) (σ : ℕ) where
  blocks : Finset (Finset G)
  label : Finset G → P
  sub : ∀ b ∈ blocks, b ⊆ S
  nonempty : ∀ b ∈ blocks, b.Nonempty
  label_spec : ∀ b ∈ blocks, ∀ x ∈ b, π x = label b
  card_le : ∀ b ∈ blocks, b.card ≤ σ
  cover : ∀ x ∈ S, ∃! b, b ∈ blocks ∧ x ∈ b
  count : ∀ c, (blocks.filter fun b => label b = c).card ≤
    ((S.filter fun x => π x = c).card + σ - 1) / σ

/-- Blockings exist for every `σ ≥ 1`. -/
theorem Blocking.exists (S : Finset G) (π : G →+ P) (σ : ℕ) (hσ : 0 < σ) :
    Nonempty (Blocking S π σ) := by
  choose parts h1 h2 h3 using fun c : P => exists_cutting (S.filter fun x => π x = c) σ hσ
  let lab : Finset G → P := fun b => if h : b.Nonempty then π h.choose else 0
  have hlab : ∀ c, ∀ b ∈ parts c, lab b = c := by
    intro c b hb
    have hne := (h1 c b hb).2.2
    simp only [lab, dif_pos hne]
    exact (Finset.mem_filter.1 ((h1 c b hb).1 hne.choose_spec)).2
  refine ⟨⟨(S.image π).biUnion parts, lab, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro b hb
    obtain ⟨c, -, hbc⟩ := Finset.mem_biUnion.1 hb
    exact (h1 c b hbc).1.trans (Finset.filter_subset _ _)
  · intro b hb
    obtain ⟨c, -, hbc⟩ := Finset.mem_biUnion.1 hb
    exact (h1 c b hbc).2.2
  · intro b hb x hx
    obtain ⟨c, -, hbc⟩ := Finset.mem_biUnion.1 hb
    rw [hlab c b hbc]
    exact (Finset.mem_filter.1 ((h1 c b hbc).1 hx)).2
  · intro b hb
    obtain ⟨c, -, hbc⟩ := Finset.mem_biUnion.1 hb
    exact (h1 c b hbc).2.1
  · intro x hx
    obtain ⟨b, ⟨hb, hxb⟩, hu⟩ := h2 (π x) x (Finset.mem_filter.2 ⟨hx, rfl⟩)
    refine ⟨b, ⟨Finset.mem_biUnion.2 ⟨π x, Finset.mem_image_of_mem _ hx, hb⟩, hxb⟩, ?_⟩
    rintro b' ⟨hb', hxb'⟩
    obtain ⟨c, -, hbc⟩ := Finset.mem_biUnion.1 hb'
    have : c = π x := ((Finset.mem_filter.1 ((h1 c b' hbc).1 hxb')).2).symm
    subst this
    exact hu b' ⟨hbc, hxb'⟩
  · intro c
    have : ((S.image π).biUnion parts).filter (fun b => lab b = c) ⊆ parts c := by
      intro b hb
      obtain ⟨hb, hl⟩ := Finset.mem_filter.1 hb
      obtain ⟨c', -, hbc⟩ := Finset.mem_biUnion.1 hb
      rw [hlab c' b hbc] at hl
      subst hl
      exact hbc
    exact (Finset.card_le_card this).trans (h3 c)

section blocking
variable {S : Finset G} {π : G →+ P} {σ : ℕ}

/-- A block is determined by any of its elements. -/
theorem Blocking.unique (B : Blocking S π σ) {b b' : Finset G} {x : G}
    (hb : b ∈ B.blocks) (hb' : b' ∈ B.blocks) (hx : x ∈ b) (hx' : x ∈ b') : b = b' :=
  (B.cover x (B.sub b hb hx)).unique ⟨hb, hx⟩ ⟨hb', hx'⟩

/-- The label of a block lies among the classes of `S`. -/
theorem Blocking.label_mem (B : Blocking S π σ) {b : Finset G} (hb : b ∈ B.blocks) :
    B.label b ∈ S.image π := by
  obtain ⟨x, hx⟩ := B.nonempty b hb
  rw [← B.label_spec b hb x hx]
  exact Finset.mem_image_of_mem _ (B.sub b hb hx)

/-- `c(β) = #{x ∈ S : π x = β}`, the size of a class. -/
def cls (S : Finset G) (π : G →+ P) (β : P) : ℕ := (S.filter fun x => π x = β).card

/-- `s(β)`: the number of blocks with label `β`. -/
def Blocking.s (B : Blocking S π σ) (β : P) : ℕ := (B.blocks.filter fun b => B.label b = β).card

/-- `s(β) ≤ 1 + c(β)/σ`. -/
theorem Blocking.s_le (hσ : 0 < σ) (B : Blocking S π σ) (β : P) :
    (B.s β : ℝ) ≤ 1 + cls S π β / σ := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  refine (Nat.cast_le.2 (B.count β)).trans (Nat.cast_div_le.trans ?_)
  have : ((cls S π β + σ - 1 : ℕ) : ℝ) ≤ cls S π β + σ := by
    have : cls S π β + σ - 1 ≤ cls S π β + σ := by omega
    exact_mod_cast this
  unfold cls at this ⊢
  calc (((S.filter fun x => π x = β).card + σ - 1 : ℕ) : ℝ) / σ
      ≤ ((S.filter fun x => π x = β).card + σ) / σ := div_le_div_of_nonneg_right this hσR.le
    _ = 1 + (S.filter fun x => π x = β).card / σ := by field_simp; ring

/-- Sums over the blocks of a function of the label, grouped by the classes of `S`. -/
theorem Blocking.sum_label {M : Type*} [AddCommMonoid M] (B : Blocking S π σ) (f : P → M) :
    ∑ b ∈ B.blocks, f (B.label b) = ∑ β ∈ S.image π, B.s β • f β := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := B.label) (t := S.image π)
    (fun b hb => B.label_mem hb)]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f β) (fun b hb => by rw [(Finset.mem_filter.1 hb).2]),
    Finset.sum_const]
  rfl

/-- The number of blocks: `|𝔅| ≤ N + |S|/σ`, `N` the number of nonempty classes of `S`. -/
theorem Blocking.card_le' (hσ : 0 < σ) (B : Blocking S π σ) :
    (B.blocks.card : ℝ) ≤ (S.image π).card + S.card / σ := by
  have h := B.sum_label (M := ℕ) (fun _ => 1)
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [h, Nat.cast_sum]
  calc ∑ β ∈ S.image π, (B.s β : ℝ) ≤ ∑ β ∈ S.image π, (1 + cls S π β / σ : ℝ) :=
        Finset.sum_le_sum fun β _ => B.s_le hσ β
    _ = (S.image π).card + (∑ β ∈ S.image π, (cls S π β : ℝ)) / σ := by
        rw [Finset.sum_add_distrib, Finset.sum_div]; simp
    _ = (S.image π).card + S.card / σ := by
        congr 2
        rw [← Nat.cast_sum]
        congr 1
        exact (Finset.card_eq_sum_card_fiberwise (f := fun x => π x)
          (fun x hx => Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hx)))).symm

end blocking

/-- `Σ_{γ ∈ T} c(γ) ≤ |S|` for any finite set `T` of labels. -/
theorem sum_cls_le (S : Finset G) (π : G →+ P) (T : Finset P) :
    ∑ γ ∈ T, cls S π γ ≤ S.card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := fun x => π x)
    (s := S.filter fun x => π x ∈ T) (t := T)
    (fun x hx => Finset.mem_coe.2 (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2)
  have e : ∀ γ ∈ T, ((S.filter fun x => π x ∈ T).filter fun x => π x = γ) =
      S.filter fun x => π x = γ := by
    intro γ hγ
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hγ⟩, h2⟩
  unfold cls
  rw [Finset.sum_congr rfl (fun γ hγ => (congrArg Finset.card (e γ hγ)).symm), ← h]
  exact Finset.card_filter_le _ _

/-! ### Probes -/

/-- A probe `Q = (x₁; b₂, b₃)`. -/
abbrev Probe (G : Type*) := G × Finset G × Finset G

section probes
variable {S₂ S₃ : Finset G} {π : G →+ P} {σ : ℕ}

/-- `𝒫₀`: the probes `(x₁; b₂, b₃)`, `x₁ ∈ S₁`, `b_i` a block of `S_i`, with
`π x₁ + label b₂ + label b₃ = 0`. -/
def probes (S₁ : Finset G) (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) : Finset (Probe G) :=
  (S₁ ×ˢ B₂.blocks ×ˢ B₃.blocks).filter fun Q => π Q.1 + B₂.label Q.2.1 + B₃.label Q.2.2 = 0

theorem mem_probes {S₁ : Finset G} {B₂ : Blocking S₂ π σ} {B₃ : Blocking S₃ π σ} {Q : Probe G} :
    Q ∈ probes S₁ B₂ B₃ ↔ (Q.1 ∈ S₁ ∧ Q.2.1 ∈ B₂.blocks ∧ Q.2.2 ∈ B₃.blocks) ∧
      π Q.1 + B₂.label Q.2.1 + B₃.label Q.2.2 = 0 := by
  simp [probes, Finset.mem_product]

end probes

/-- `cnt_K(Q)`: the pairs `(x₂, x₃) ∈ b₂ × b₃` with `K(x₁ + x₂ + x₃) = 0`. -/
def cnt (K : G →+ R) (Q : Probe G) : ℕ :=
  ((Q.2.1 ×ˢ Q.2.2).filter fun p => K (Q.1 + p.1 + p.2) = 0).card

/-- `z(Q)`: the solutions in the probe. -/
def z (Q : Probe G) : ℕ := ((Q.2.1 ×ˢ Q.2.2).filter fun p => Q.1 + p.1 + p.2 = 0).card

/-- `f_K(Q)`: the false positives of the probe under `K`. -/
def fp (K : G →+ R) (Q : Probe G) : ℕ :=
  ((Q.2.1 ×ˢ Q.2.2).filter fun p => Q.1 + p.1 + p.2 ≠ 0 ∧ K (Q.1 + p.1 + p.2) = 0).card

/-- `F = Σ_{Q ∈ 𝒫} f_K(Q)`. -/
def F (Ps : Finset (Probe G)) (K : G →+ R) : ℕ := ∑ Q ∈ Ps, fp K Q

theorem cnt_eq_fp_add_z (K : G →+ R) (Q : Probe G) : cnt K Q = fp K Q + z Q := by
  unfold cnt fp z
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : Q.1 + p.1 + p.2 = 0 <;> simp [h]

theorem z_le_cnt (K : G →+ R) (Q : Probe G) : z Q ≤ cnt K Q := by
  rw [cnt_eq_fp_add_z]; omega

/-- The scan of a probe ("for each `x₂ ∈ b₂` look up `-(x₁ + x₂)` in `b₃`") succeeds iff
`z(Q) > 0`. -/
theorem z_pos_iff (Q : Probe G) : 0 < z Q ↔ ∃ x₂ ∈ Q.2.1, -(Q.1 + x₂) ∈ Q.2.2 := by
  unfold z
  rw [Finset.card_pos]
  constructor
  · rintro ⟨⟨x₂, x₃⟩, hp⟩
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    exact ⟨x₂, hp.1.1, (sum3_eq_zero_iff _ _ _).1 hp.2 ▸ hp.1.2⟩
  · rintro ⟨x₂, h2, h3⟩
    exact ⟨(x₂, -(Q.1 + x₂)), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨h2, h3⟩,
      (sum3_eq_zero_iff _ _ _).2 rfl⟩⟩

section probes2
variable {S₁ S₂ S₃ : Finset G} {π : G →+ P} {σ : ℕ}

/-- Every triple with `π(x₁ + x₂ + x₃) = 0` lies in a probe: `(x₁; block of x₂, block of x₃)`. -/
theorem triple_in_probe (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    {x₁ x₂ x₃ : G} (h₁ : x₁ ∈ S₁) (h₂ : x₂ ∈ S₂) (h₃ : x₃ ∈ S₃) (h0 : π (x₁ + x₂ + x₃) = 0) :
    ∃ Q ∈ probes S₁ B₂ B₃, Q.1 = x₁ ∧ x₂ ∈ Q.2.1 ∧ x₃ ∈ Q.2.2 := by
  obtain ⟨b₂, ⟨hb₂, hx₂⟩, -⟩ := B₂.cover x₂ h₂
  obtain ⟨b₃, ⟨hb₃, hx₃⟩, -⟩ := B₃.cover x₃ h₃
  refine ⟨(x₁, b₂, b₃), mem_probes.2 ⟨⟨h₁, hb₂, hb₃⟩, ?_⟩, rfl, hx₂, hx₃⟩
  rw [← B₂.label_spec b₂ hb₂ x₂ hx₂, ← B₃.label_spec b₃ hb₃ x₃ hx₃, ← map_add, ← map_add]
  exact h0

/-- **Correctness, first part** (Lemma II.1 (i)): every solution lies in some probe. -/
theorem solution_in_probe (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    {x₁ x₂ x₃ : G} (h₁ : x₁ ∈ S₁) (h₂ : x₂ ∈ S₂) (h₃ : x₃ ∈ S₃) (h0 : x₁ + x₂ + x₃ = 0) :
    ∃ Q ∈ probes S₁ B₂ B₃, Q.1 = x₁ ∧ x₂ ∈ Q.2.1 ∧ x₃ ∈ Q.2.2 :=
  triple_in_probe B₂ B₃ h₁ h₂ h₃ (by rw [h0, map_zero])

/-- The members of a probe lie in the lists. -/
theorem probe_mem {B₂ : Blocking S₂ π σ} {B₃ : Blocking S₃ π σ} {Q : Probe G}
    (hQ : Q ∈ probes S₁ B₂ B₃) {x₂ x₃ : G} (h2 : x₂ ∈ Q.2.1) (h3 : x₃ ∈ Q.2.2) :
    Q.1 ∈ S₁ ∧ x₂ ∈ S₂ ∧ x₃ ∈ S₃ := by
  have hQ' := (mem_probes.1 hQ).1
  exact ⟨hQ'.1, B₂.sub _ hQ'.2.1 h2, B₃.sub _ hQ'.2.2 h3⟩

/-- The triples of a probe have `π(x₁ + x₂ + x₃) = 0`. -/
theorem probe_pi_zero {B₂ : Blocking S₂ π σ} {B₃ : Blocking S₃ π σ} {Q : Probe G}
    (hQ : Q ∈ probes S₁ B₂ B₃) {x₂ x₃ : G} (h2 : x₂ ∈ Q.2.1) (h3 : x₃ ∈ Q.2.2) :
    π (Q.1 + x₂ + x₃) = 0 := by
  have hQ' := mem_probes.1 hQ
  rw [map_add, map_add, B₂.label_spec _ hQ'.1.2.1 x₂ h2, B₃.label_spec _ hQ'.1.2.2 x₃ h3]
  exact hQ'.2

/-- **Correctness** (Lemma II.1 (i), second sentence): a solution exists iff `z(Q) > 0` for some
probe. -/
theorem exists_sol_iff_probe (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) :
    (∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) ↔
      ∃ Q ∈ probes S₁ B₂ B₃, 0 < z Q := by
  constructor
  · rintro ⟨x₁, h₁, x₂, h₂, x₃, h₃, h0⟩
    obtain ⟨Q, hQ, e1, e2, e3⟩ := solution_in_probe B₂ B₃ h₁ h₂ h₃ h0
    refine ⟨Q, hQ, (z_pos_iff Q).2 ⟨x₂, e2, ?_⟩⟩
    rw [e1, ← (sum3_eq_zero_iff _ _ _).1 h0]; exact e3
  · rintro ⟨Q, hQ, hz⟩
    obtain ⟨x₂, h2, h3⟩ := (z_pos_iff Q).1 hz
    obtain ⟨m1, m2, m3⟩ := probe_mem hQ h2 h3
    exact ⟨Q.1, m1, x₂, m2, -(Q.1 + x₂), m3, (sum3_eq_zero_iff _ _ _).2 rfl⟩

/-- **"Every triple with `π(sum) = 0` lies in exactly one probe"**: `Σ_{Q ∈ 𝒫₀} cnt_K(Q)` is the
number of triples that both `π` and `K` send to `0`. -/
theorem sum_cnt_probes' (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (K : G →+ R) :
    ∑ Q ∈ probes S₁ B₂ B₃, cnt K Q =
      ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t =>
        π (t.1 + t.2.1 + t.2.2) = 0 ∧ K (t.1 + t.2.1 + t.2.2) = 0).card := by
  have hlhs : ∑ Q ∈ probes S₁ B₂ B₃, cnt K Q =
      ((probes S₁ B₂ B₃).sigma fun Q => (Q.2.1 ×ˢ Q.2.2).filter
        fun p => K (Q.1 + p.1 + p.2) = 0).card := by
    rw [Finset.card_sigma]; rfl
  rw [hlhs]
  refine Finset.card_bij (fun a _ => (a.1.1, a.2.1, a.2.2)) ?_ ?_ ?_
  · rintro ⟨⟨x₁, b₂, b₃⟩, x₂, x₃⟩ ha
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product] at ha
    obtain ⟨hQ, ⟨h2, h3⟩, hK⟩ := ha
    obtain ⟨m1, m2, m3⟩ := probe_mem hQ h2 h3
    simp only [Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨m1, m2, m3⟩, probe_pi_zero hQ h2 h3, hK⟩
  · rintro ⟨⟨x₁, b₂, b₃⟩, x₂, x₃⟩ ha ⟨⟨x₁', b₂', b₃'⟩, x₂', x₃'⟩ ha' h
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product] at ha ha'
    simp only [Prod.mk.injEq] at h
    obtain ⟨e1, e2, e3⟩ := h
    subst e1 e2 e3
    have q := (mem_probes.1 ha.1).1
    have q' := (mem_probes.1 ha'.1).1
    have r2 := B₂.unique q.2.1 q'.2.1 ha.2.1.1 ha'.2.1.1
    have r3 := B₃.unique q.2.2 q'.2.2 ha.2.1.2 ha'.2.1.2
    subst r2 r3
    rfl
  · rintro ⟨x₁, x₂, x₃⟩ ht
    simp only [Finset.mem_filter, Finset.mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, hπ, hK⟩ := ht
    obtain ⟨Q, hQ, e1, e2, e3⟩ := triple_in_probe B₂ B₃ h1 h2 h3 hπ
    refine ⟨⟨Q, x₂, x₃⟩, ?_, by subst e1; rfl⟩
    rw [Finset.mem_sigma, Finset.mem_filter, Finset.mem_product]
    exact ⟨hQ, ⟨e2, e3⟩, by rw [e1]; exact hK⟩

/-- **`Σ_{Q ∈ 𝒫₀} cnt_K(Q) = Z(K)`** when `π` factors through `K` (`K x = 0 → π x = 0`). -/
theorem sum_cnt_probes (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (K : G →+ R)
    (hKπ : ∀ x, K x = 0 → π x = 0) :
    ∑ Q ∈ probes S₁ B₂ B₃, cnt K Q = Zc S₁ S₂ S₃ K := by
  rw [sum_cnt_probes']
  unfold Zc
  congr 1
  exact Finset.filter_congr fun t _ => ⟨fun h => h.2, fun h => ⟨hKπ _ h, h⟩⟩

/-- `Σ_{Q ∈ 𝒫₀} z(Q) = Z₀`. -/
theorem sum_z_probes (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) :
    ∑ Q ∈ probes S₁ B₂ B₃, z Q = Zsol S₁ S₂ S₃ := by
  have : ∀ Q : Probe G, z Q = cnt (AddMonoidHom.id G) Q := fun Q => rfl
  simp only [this]
  exact sum_cnt_probes B₂ B₃ _ (fun x hx => by simp only [AddMonoidHom.id_apply] at hx; simp [hx])

/-- **`F = Σ_{Q ∈ 𝒫₀} (cnt_K(Q) − z(Q)) = Z(K) − Z₀`** (π factoring through `K`). -/
theorem F_probes_eq (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (K : G →+ R)
    (hKπ : ∀ x, K x = 0 → π x = 0) :
    (F (probes S₁ B₂ B₃) K : ℤ) = Zc S₁ S₂ S₃ K - Zsol S₁ S₂ S₃ := by
  have h : ∑ Q ∈ probes S₁ B₂ B₃, cnt K Q =
      F (probes S₁ B₂ B₃) K + ∑ Q ∈ probes S₁ B₂ B₃, z Q := by
    unfold F
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun Q _ => cnt_eq_fp_add_z K Q
  rw [sum_cnt_probes B₂ B₃ K hKπ, sum_z_probes] at h
  rw [h]; push_cast; ring

/-- `Σ_{Q ∈ 𝒫₀} (cnt_K(Q) − z(Q)) = Z(K) − Z₀` in the form of a sum of differences. -/
theorem sum_cnt_sub_z (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (K : G →+ R)
    (hKπ : ∀ x, K x = 0 → π x = 0) :
    ∑ Q ∈ probes S₁ B₂ B₃, ((cnt K Q : ℤ) - z Q) = Zc S₁ S₂ S₃ K - Zsol S₁ S₂ S₃ := by
  rw [← F_probes_eq B₂ B₃ K hKπ, F, Nat.cast_sum]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [cnt_eq_fp_add_z]; push_cast; ring

end probes2

/-- **"Scans"**: the flagged probes (`cnt_K > 0`) without a solution are at most `F`. -/
theorem failed_scans_le (Ps : Finset (Probe G)) (K : G →+ R) :
    (Ps.filter fun Q => 0 < cnt K Q ∧ z Q = 0).card ≤ F Ps K := by
  calc (Ps.filter fun Q => 0 < cnt K Q ∧ z Q = 0).card
      = ∑ _Q ∈ Ps.filter (fun Q => 0 < cnt K Q ∧ z Q = 0), 1 := by simp
    _ ≤ ∑ Q ∈ Ps.filter (fun Q => 0 < cnt K Q ∧ z Q = 0), fp K Q := by
        refine Finset.sum_le_sum fun Q hQ => ?_
        have h := (Finset.mem_filter.1 hQ).2
        have e := cnt_eq_fp_add_z K Q
        omega
    _ ≤ F Ps K := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-! ### The number of probes -/

section count
variable {S₁ S₂ S₃ : Finset G} {π : G →+ P} {σ : ℕ}

/-- `|𝒫₀| = Σ_{x₁} Σ_{b₂} s₃(−(π x₁ + label b₂))`. -/
theorem probes_card_eq (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) :
    (probes S₁ B₂ B₃).card =
      ∑ x₁ ∈ S₁, ∑ b₂ ∈ B₂.blocks, B₃.s (-(π x₁ + B₂.label b₂)) := by
  unfold probes
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun b₂ _ => ?_
  rw [← Finset.card_filter]
  unfold Blocking.s
  congr 1
  exact Finset.filter_congr fun b₃ _ => sum3_eq_zero_iff _ _ _

/-- **Counts**: `|𝒫₀| ≤ |S₁| N₂ + |S₁|(|S₂| + |S₃|)/σ + Z(π)/σ²`, where `N₂` is the number of
nonempty `π`-classes of `S₂`. -/
theorem probes_card_le (hσ : 0 < σ) (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) :
    ((probes S₁ B₂ B₃).card : ℝ) ≤
      S₁.card * (S₂.image π).card + S₁.card * ((S₂.card + S₃.card) / σ) +
        Zc S₁ S₂ S₃ π / σ ^ 2 := by
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  set C₂ := S₂.image π with hC₂
  -- the fibre of `x₁` in `Z(π)`
  have hfib : ∀ x₁, ∑ β ∈ C₂, cls S₂ π β * cls S₃ π (-(π x₁ + β)) =
      ((S₂ ×ˢ S₃).filter fun p => π (x₁ + p.1 + p.2) = 0).card := by
    intro x₁
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p => π p.1) (t := C₂)
      (fun p hp => Finset.mem_coe.2 (Finset.mem_image_of_mem _
        (Finset.mem_product.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).1).1))]
    refine Finset.sum_congr rfl fun β _ => ?_
    unfold cls
    rw [← Finset.card_product]
    congr 1
    ext ⟨x₂, x₃⟩
    simp only [Finset.mem_filter, Finset.mem_product, map_add]
    constructor
    · rintro ⟨⟨h2, e⟩, h3, e3⟩
      refine ⟨⟨⟨h2, h3⟩, ?_⟩, e⟩
      rw [e3, e]; exact add_neg_cancel _
    · rintro ⟨⟨⟨h2, h3⟩, h0⟩, e⟩
      refine ⟨⟨h2, e⟩, h3, ?_⟩
      rw [← e]; exact (sum3_eq_zero_iff _ _ _).1 h0
  have hZsum : ∑ x₁ ∈ S₁, ∑ β ∈ C₂, (cls S₂ π β * cls S₃ π (-(π x₁ + β)) : ℝ) =
      Zc S₁ S₂ S₃ π := by
    have : Zc S₁ S₂ S₃ π =
        ∑ x₁ ∈ S₁, ((S₂ ×ˢ S₃).filter fun p => π (x₁ + p.1 + p.2) = 0).card := by
      unfold Zc
      rw [Finset.card_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun x₁ _ => ?_
      rw [Finset.card_filter, Finset.sum_product]
    rw [this, Nat.cast_sum]
    refine Finset.sum_congr rfl fun x₁ _ => ?_
    rw [← hfib]; push_cast; rfl
  have hS3 : ∀ x₁, ∑ β ∈ C₂, (cls S₃ π (-(π x₁ + β)) : ℝ) ≤ S₃.card := by
    intro x₁
    have hinj : Set.InjOn (fun β => -(π x₁ + β)) (C₂ : Set P) := by
      intro a _ b _ h
      simpa using h
    rw [← Finset.sum_image (f := fun γ => (cls S₃ π γ : ℝ)) hinj, ← Nat.cast_sum]
    exact_mod_cast sum_cls_le S₃ π _
  have hS2 : ∑ β ∈ C₂, (cls S₂ π β : ℝ) = S₂.card := by
    rw [← Nat.cast_sum]
    congr 1
    exact (Finset.card_eq_sum_card_fiberwise (f := fun x => π x)
      (fun x hx => Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_coe.1 hx)))).symm
  have hmain : ∀ x₁, (∑ b₂ ∈ B₂.blocks, (B₃.s (-(π x₁ + B₂.label b₂)) : ℝ)) ≤
      C₂.card + S₂.card / σ + S₃.card / σ +
        (∑ β ∈ C₂, (cls S₂ π β * cls S₃ π (-(π x₁ + β)) : ℝ)) / σ ^ 2 := by
    intro x₁
    rw [B₂.sum_label (M := ℝ) (fun β => (B₃.s (-(π x₁ + β)) : ℝ))]
    simp only [nsmul_eq_mul]
    calc ∑ β ∈ C₂, (B₂.s β : ℝ) * B₃.s (-(π x₁ + β))
        ≤ ∑ β ∈ C₂, (1 + cls S₂ π β / σ) * (1 + cls S₃ π (-(π x₁ + β)) / σ : ℝ) :=
          Finset.sum_le_sum fun β _ => mul_le_mul (B₂.s_le hσ β) (B₃.s_le hσ _)
            (Nat.cast_nonneg _) (by positivity)
      _ = ∑ _β ∈ C₂, (1 : ℝ) + (∑ β ∈ C₂, (cls S₂ π β : ℝ)) / σ +
            (∑ β ∈ C₂, (cls S₃ π (-(π x₁ + β)) : ℝ)) / σ +
            (∑ β ∈ C₂, (cls S₂ π β * cls S₃ π (-(π x₁ + β)) : ℝ)) / σ ^ 2 := by
          rw [Finset.sum_div, Finset.sum_div, Finset.sum_div,
            ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun β _ => ?_
          field_simp
          ring
      _ ≤ C₂.card + S₂.card / σ + S₃.card / σ +
            (∑ β ∈ C₂, (cls S₂ π β * cls S₃ π (-(π x₁ + β)) : ℝ)) / σ ^ 2 := by
          rw [hS2]
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          gcongr
          exact hS3 x₁
  rw [probes_card_eq, Nat.cast_sum]
  calc ∑ x₁ ∈ S₁, ((∑ b₂ ∈ B₂.blocks, B₃.s (-(π x₁ + B₂.label b₂)) : ℕ) : ℝ)
      ≤ ∑ x₁ ∈ S₁, (C₂.card + S₂.card / σ + S₃.card / σ +
          (∑ β ∈ C₂, (cls S₂ π β * cls S₃ π (-(π x₁ + β)) : ℝ)) / σ ^ 2) := by
        refine Finset.sum_le_sum fun x₁ _ => ?_
        push_cast
        exact hmain x₁
    _ = S₁.card * C₂.card + S₁.card * ((S₂.card + S₃.card) / σ) + Zc S₁ S₂ S₃ π / σ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.sum_div S₁ _ ((σ : ℝ) ^ 2), hZsum]
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring

end count

/-! ### The Lop instance with split middle part (Section 19.6, "Instance") -/

/-- A `Lop` instance: middle part `mid`, adjacencies, query pairs `W` (as in XorLean). -/
structure LopInst (A B V : Type*) where
  mid : Finset V
  adjA : A → V → Prop
  adjB : V → B → Prop
  W : Finset (A × B)

/-- The answer for a query pair: a common neighbour in the middle part. -/
def LopInst.Accepts {A B V : Type*} (I : LopInst A B V) (a : A) (b : B) : Prop :=
  ∃ m ∈ I.mid, I.adjA a m ∧ I.adjB m b

/-- The support instance (`X' = [X > 0]`, `Y' = [Y > 0]`) with middle part `T`. -/
def suppInst {A B V : Type*} (X : A → V → ℕ) (Y : V → B → ℕ) (T : Finset V)
    (W : Finset (A × B)) : LopInst A B V where
  mid := T
  adjA r w := 0 < X r w
  adjB w c := 0 < Y w c
  W := W

/-- `(X'Y') > 0` iff `(XY) > 0`. -/
theorem suppInst_accepts {A B V : Type*} (X : A → V → ℕ) (Y : V → B → ℕ) (T : Finset V)
    (W : Finset (A × B)) (r : A) (c : B) :
    (suppInst X Y T W).Accepts r c ↔ 0 < ∑ w ∈ T, X r w * Y w c := by
  rw [Finset.sum_pos_iff]
  simp only [LopInst.Accepts, suppInst, Nat.pos_iff_ne_zero, ne_eq, mul_eq_zero, not_or]

section inst
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [DecidableEq M₁] [DecidableEq M₂]

/-- `X[(b₂, μ₁), λ] = #{x₂ ∈ b₂ : K x₂ − K z_{b₂} + (μ₁, 0) = λ}`; `zr` picks the
representatives `z_b`. -/
def matX (K : G →+ M₁ × M₂) (zr : Finset G → G) (r : Finset G × M₁) (w : M₁ × M₂) : ℕ :=
  (r.1.filter fun x => K x - K (zr r.1) + (r.2, 0) = w).card

/-- `Y[λ, (b₃, μ₂)] = #{x₃ ∈ b₃ : −(K x₃ − K z_{b₃}) − (0, μ₂) = λ}`. -/
def matY (K : G →+ M₁ × M₂) (zr : Finset G → G) (w : M₁ × M₂) (c : Finset G × M₂) : ℕ :=
  (c.1.filter fun x => -(K x - K (zr c.1)) - (0, c.2) = w).card

/-- `(μ₁, μ₂) := K x₁ + K z_{b₂} + K z_{b₃}`. -/
def mu (K : G →+ M₁ × M₂) (zr : Finset G → G) (Q : Probe G) : M₁ × M₂ :=
  K Q.1 + K (zr Q.2.1) + K (zr Q.2.2)

/-- The position `((b₂, μ₁), (b₃, μ₂))` of a probe. -/
def posn (K : G →+ M₁ × M₂) (zr : Finset G → G) (Q : Probe G) :
    (Finset G × M₁) × (Finset G × M₂) :=
  ((Q.2.1, (mu K zr Q).1), (Q.2.2, (mu K zr Q).2))

/-- The left value `K x₂ − K z_{b₂} + (μ₁, 0)` and the right value `−(K x₃ − K z_{b₃}) − (0, μ₂)`
agree iff `K(x₁ + x₂ + x₃) = 0`. -/
theorem lr_eq_iff (K : G →+ M₁ × M₂) (zr : Finset G → G) (Q : Probe G) (x₂ x₃ : G) :
    K x₂ - K (zr Q.2.1) + ((mu K zr Q).1, 0) = -(K x₃ - K (zr Q.2.2)) - (0, (mu K zr Q).2) ↔
      K (Q.1 + x₂ + x₃) = 0 := by
  set μ := mu K zr Q with hμdef
  have hμ : ((μ.1, 0) : M₁ × M₂) + (0, μ.2) = μ := Prod.ext (by simp) (by simp)
  rw [← sub_eq_zero]
  have e : K x₂ - K (zr Q.2.1) + (μ.1, 0) - (-(K x₃ - K (zr Q.2.2)) - (0, μ.2)) =
      K (Q.1 + x₂ + x₃) := by
    calc _ = K x₂ + K x₃ - K (zr Q.2.1) - K (zr Q.2.2) + (((μ.1, 0) : M₁ × M₂) + (0, μ.2)) := by
          abel
      _ = K x₂ + K x₃ - K (zr Q.2.1) - K (zr Q.2.2) + μ := by rw [hμ]
      _ = K (Q.1 + x₂ + x₃) := by
          rw [hμdef, mu, map_add, map_add]; abel
  rw [e]

/-- **Lemma II.2 for the split instance**: `(XY)` at the position of a probe is `cnt_K(Q)`; the
sum over `λ` runs over any finite set `T` containing the left values of the probe (for instance
`univ` when `M₁ × M₂` is finite). -/
theorem matXY_pos (K : G →+ M₁ × M₂) (zr : Finset G → G) (Q : Probe G) (T : Finset (M₁ × M₂))
    (hT : ∀ x₂ ∈ Q.2.1, K x₂ - K (zr Q.2.1) + ((mu K zr Q).1, 0) ∈ T) :
    ∑ w ∈ T, matX K zr (posn K zr Q).1 w * matY K zr w (posn K zr Q).2 = cnt K Q := by
  unfold matX matY posn cnt
  simp only
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun p : G × G => K p.1 - K (zr Q.2.1) + ((mu K zr Q).1, 0)) (t := T)
    (fun p hp => Finset.mem_coe.2 (hT p.1
      (Finset.mem_product.1 (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).1).1))]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.card_product]
  congr 1
  ext ⟨x₂, x₃⟩
  simp only [Finset.mem_filter, Finset.mem_product]
  rw [← lr_eq_iff K zr Q x₂ x₃]
  constructor
  · rintro ⟨⟨h2, e2⟩, h3, e3⟩
    exact ⟨⟨⟨h2, h3⟩, e2.trans e3.symm⟩, e2⟩
  · rintro ⟨⟨⟨h2, h3⟩, e⟩, e'⟩
    exact ⟨⟨h2, e'⟩, h3, e.symm.trans e'⟩

/-- The `Fintype` form: the sum over the whole middle part `M₁ × M₂`. -/
theorem matXY_pos_univ [Fintype M₁] [Fintype M₂] (K : G →+ M₁ × M₂) (zr : Finset G → G)
    (Q : Probe G) :
    ∑ w, matX K zr (posn K zr Q).1 w * matY K zr w (posn K zr Q).2 = cnt K Q :=
  matXY_pos K zr Q Finset.univ (fun _ _ => Finset.mem_univ _)

/-- The entries of `X` and `Y` are at most the block sizes. -/
theorem matX_le (K : G →+ M₁ × M₂) (zr : Finset G → G) (r : Finset G × M₁) (w : M₁ × M₂) :
    matX K zr r w ≤ r.1.card := Finset.card_filter_le _ _

theorem matY_le (K : G →+ M₁ × M₂) (zr : Finset G → G) (w : M₁ × M₂) (c : Finset G × M₂) :
    matY K zr w c ≤ c.1.card := Finset.card_filter_le _ _

/-- **The support version**: the probe's position is answered positively by the `0/1` instance
iff `cnt_K(Q) > 0`. -/
theorem flagged_iff (K : G →+ M₁ × M₂) (zr : Finset G → G) (T : Finset (M₁ × M₂))
    (W : Finset ((Finset G × M₁) × (Finset G × M₂))) (Q : Probe G)
    (hT : ∀ x₂ ∈ Q.2.1, K x₂ - K (zr Q.2.1) + ((mu K zr Q).1, 0) ∈ T) :
    (suppInst (matX K zr) (matY K zr) T W).Accepts (posn K zr Q).1 (posn K zr Q).2 ↔
      0 < cnt K Q := by
  rw [suppInst_accepts, matXY_pos K zr Q T hT]

section mid
variable {S₁ S₂ S₃ : Finset G} {π : G →+ P} {σ : ℕ}

/-- **The middle part is `K(ker π)`**: with representatives `z_b ∈ b`, for a probe and
`x₂ ∈ b₂`, `x₃ ∈ b₃`, the differences `K x₂ − K z_{b₂}`, `K x₃ − K z_{b₃}` and the position
`(μ₁, μ₂)` lie in `(ker π).map K`. -/
theorem mem_mid (K : G →+ M₁ × M₂) (zr : Finset G → G) {B₂ : Blocking S₂ π σ}
    {B₃ : Blocking S₃ π σ} (hz₂ : ∀ b ∈ B₂.blocks, zr b ∈ b) (hz₃ : ∀ b ∈ B₃.blocks, zr b ∈ b)
    {Q : Probe G} (hQ : Q ∈ probes S₁ B₂ B₃) :
    (∀ x₂ ∈ Q.2.1, K x₂ - K (zr Q.2.1) ∈ π.ker.map K) ∧
    (∀ x₃ ∈ Q.2.2, K x₃ - K (zr Q.2.2) ∈ π.ker.map K) ∧
    mu K zr Q ∈ π.ker.map K := by
  have hQ' := mem_probes.1 hQ
  have l2 := B₂.label_spec _ hQ'.1.2.1
  have l3 := B₃.label_spec _ hQ'.1.2.2
  have z2 := hz₂ _ hQ'.1.2.1
  have z3 := hz₃ _ hQ'.1.2.2
  refine ⟨fun x₂ h2 => ⟨x₂ - zr Q.2.1, ?_, by simp⟩, fun x₃ h3 => ⟨x₃ - zr Q.2.2, ?_, by simp⟩,
    ⟨Q.1 + zr Q.2.1 + zr Q.2.2, ?_, by simp [mu]⟩⟩
  · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, l2 _ h2, l2 _ z2, sub_self]
  · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, l3 _ h3, l3 _ z3, sub_self]
  · rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_add, map_add, l2 _ z2, l3 _ z3]
    exact hQ'.2

/-- The answer of the algorithm: some probe is flagged by the one detection call and its scan
finds a solution. -/
def oneHashYes (S₁ : Finset G) (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    (K : G →+ M₁ × M₂) (zr : Finset G → G) (T : Finset (M₁ × M₂)) : Prop :=
  ∃ Q ∈ probes S₁ B₂ B₃,
    (suppInst (matX K zr) (matY K zr) T ((probes S₁ B₂ B₃).image (posn K zr))).Accepts
      (posn K zr Q).1 (posn K zr Q).2 ∧ ∃ x₂ ∈ Q.2.1, -(Q.1 + x₂) ∈ Q.2.2

/-- **Theorem A, correctness** (for every abelian `G`, all homomorphisms `π`, `K`, any blocking,
any representatives, and a middle part `T` containing the left values of the probes): the
algorithm answers YES iff the instance has a solution; a NO is correct and a returned triple is a
solution. -/
theorem detection_correct (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (K : G →+ M₁ × M₂)
    (zr : Finset G → G) (T : Finset (M₁ × M₂))
    (hT : ∀ Q ∈ probes S₁ B₂ B₃, ∀ x₂ ∈ Q.2.1, K x₂ - K (zr Q.2.1) + ((mu K zr Q).1, 0) ∈ T) :
    oneHashYes S₁ B₂ B₃ K zr T ↔ ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0 := by
  rw [exists_sol_iff_probe B₂ B₃]
  unfold oneHashYes
  constructor
  · rintro ⟨Q, hQ, -, hs⟩
    exact ⟨Q, hQ, (z_pos_iff Q).2 hs⟩
  · rintro ⟨Q, hQ, hz⟩
    exact ⟨Q, hQ, (flagged_iff K zr T _ Q (hT Q hQ)).2 (lt_of_lt_of_le hz (z_le_cnt K Q)),
      (z_pos_iff Q).1 hz⟩

/-- **Theorem A, correctness**, `Fintype` middle part `T = univ`. -/
theorem detection_correct_univ [Fintype M₁] [Fintype M₂] (B₂ : Blocking S₂ π σ)
    (B₃ : Blocking S₃ π σ) (K : G →+ M₁ × M₂) (zr : Finset G → G) :
    oneHashYes S₁ B₂ B₃ K zr Finset.univ ↔ ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0 :=
  detection_correct B₂ B₃ K zr _ (fun _ _ _ _ => Finset.mem_univ _)

/-- The scans made by the algorithm that fail are at most `F = Z(K) − Z₀` (π factoring
through `K`). -/
theorem failed_scans_le_Z (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (K : G →+ M₁ × M₂)
    (hKπ : ∀ x, K x = 0 → π x = 0) :
    (((probes S₁ B₂ B₃).filter fun Q => 0 < cnt K Q ∧ z Q = 0).card : ℤ) ≤
      Zc S₁ S₂ S₃ K - Zsol S₁ S₂ S₃ := by
  rw [← F_probes_eq B₂ B₃ K hKπ]
  exact_mod_cast failed_scans_le _ K

end mid
end inst

end OneHash
end GroupLean

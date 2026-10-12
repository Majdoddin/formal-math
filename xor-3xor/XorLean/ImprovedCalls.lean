import XorLean.ImprovedOneHash
import XorLean.ImprovedTriangle

/-!
# Improved 3XOR: the oracle's instances with numbered vertices

The instances of the improved write-up (`I(H, 𝒫)` of §4.4, `J(H, k, ϱ, 𝒬)` of §5) are defined in
`ImprovedProbes.lean` and `Reduction.lean` on the natural vertex sets: blocks of vectors times
`F₂^{l₁}`, or the parts `A`, `B` themselves. The hypothesis `Hyp(ε, γ)` speaks of instances of
`#Lop(N, D)`, with exactly `N` vertices per side. This file supplies the passage:

* `LopInst.number`: the same instance on the vertex sets `Fin N`, through numberings
  `ea : A → ℕ`, `eb : B → ℕ` that are injective on given vertex sets `SA`, `SB` and below `N`.
  The vertices outside the image are isolated (the padding of the text). The middle part is
  unchanged.
* `LopInst.countAt`, `LopInst.AcceptsAt`, `LopInst.queries`: the oracle's answer at a numbered
  position, and the numbered query pairs.
* `number_count`, `number_accepts`, `number_queries`, `number_W_card`, `number_isLop`: the counts,
  the answers and the query sets are those of the original instance, and the conditions of
  `Lop(N, D)` reduce to the size of the middle part.
* `Finset.numbering`: a canonical numbering of a finite set, by `Finset.equivFin`.
* For the probes: `leftVerts`, `rightVerts` (the blocks of lists 2 and 3 times `F₂^{l₁}`,
  `F₂^{l₂}`), `probeNum` (an instance on these vertex sets, numbered into `Fin (g' 2^{l₁})`),
  `posNum` (the numbered position of a probe).
* `splitMap`: the map with rows `rows`, its target `F₂^{|rows|}` written as
  `F₂^{⌈l/2⌉} × F₂^{⌊l/2⌋}`, so that `matX`, `matY`, `pos` apply to a row list of any length.
-/

set_option linter.unusedSectionVars false

namespace Xor

open Finset

/-! ### A canonical numbering of a finite set -/

open Classical in
/-- The numbering of `s` by `Finset.equivFin`; `0` outside `s`. -/
noncomputable def numbering {α : Type*} (s : Finset α) (a : α) : ℕ :=
  if h : a ∈ s then (s.equivFin ⟨a, h⟩ : ℕ) else 0

theorem numbering_lt {α : Type*} (s : Finset α) {a : α} (ha : a ∈ s) :
    numbering s a < s.card := by
  classical
  unfold numbering
  rw [dif_pos ha]
  exact (s.equivFin ⟨a, ha⟩).isLt

theorem numbering_injOn {α : Type*} (s : Finset α) : Set.InjOn (numbering s) s := by
  classical
  intro a ha b hb h
  unfold numbering at h
  rw [dif_pos (Finset.mem_coe.1 ha), dif_pos (Finset.mem_coe.1 hb)] at h
  have := s.equivFin.injective (Fin.ext h)
  exact congrArg Subtype.val this

namespace LopInst

variable {A B V : Type*}

/-- The instance with numbered vertices: left vertex `i : Fin N` is the `a ∈ SA` with
`ea a = i` (if any), right vertex `j` the `b ∈ SB` with `eb b = j`; the other vertices are
isolated. The middle part is that of `I`; the query pairs are the numbered query pairs of `I`. -/
noncomputable def number (I : LopInst A B V) (SA : Finset A) (SB : Finset B)
    (ea : A → ℕ) (eb : B → ℕ) (N : ℕ) : LopInst (Fin N) (Fin N) V where
  mid := I.mid
  adjA i m := ∃ a ∈ SA, ea a = i.val ∧ I.adjA a m
  adjB m j := ∃ b ∈ SB, eb b = j.val ∧ I.adjB m b
  W := open Classical in
    univ.filter fun p => ∃ x ∈ I.W, ea x.1 = p.1.val ∧ eb x.2 = p.2.val

/-- The oracle's `#Lop` answer at row `i`, column `j` of an instance on `Fin N` (`0` outside). -/
noncomputable def countAt {N : ℕ} (J : LopInst (Fin N) (Fin N) V) (i j : ℕ) : ℕ :=
  if h : i < N ∧ j < N then J.count ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- The oracle's `Lop` answer at row `i`, column `j`. -/
def AcceptsAt {N : ℕ} (J : LopInst (Fin N) (Fin N) V) (i j : ℕ) : Prop :=
  ∃ h : i < N ∧ j < N, J.Accepts ⟨i, h.1⟩ ⟨j, h.2⟩

/-- The query pairs of an instance on `Fin N`, as pairs of numbers. -/
def queries {N : ℕ} (J : LopInst (Fin N) (Fin N) V) : Finset (ℕ × ℕ) :=
  J.W.image fun p => (p.1.val, p.2.val)

theorem queries_card {N : ℕ} (J : LopInst (Fin N) (Fin N) V) : J.queries.card = J.W.card :=
  Finset.card_image_of_injective _ fun p p' h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)

section number

variable (I : LopInst A B V) (SA : Finset A) (SB : Finset B) (ea : A → ℕ) (eb : B → ℕ) (N : ℕ)

/-- `Lop(N, D)` for the numbered instance is the bound on the middle part. -/
theorem number_isLop (D : ℕ) : (I.number SA SB ea eb N).IsLop N D ↔ I.mid.card ≤ D := by
  simp [IsLop, number]

theorem number_mid : (I.number SA SB ea eb N).mid = I.mid := rfl

variable {I SA SB ea eb N}

/-- At numbered positions the adjacency is that of `I`. -/
theorem number_adjA (hA : Set.InjOn ea SA) {a : A} (ha : a ∈ SA) (i : Fin N) (hi : ea a = i.val)
    (m : V) : (I.number SA SB ea eb N).adjA i m ↔ I.adjA a m := by
  constructor
  · rintro ⟨a', ha', he, h⟩
    rwa [hA (Finset.mem_coe.2 ha') (Finset.mem_coe.2 ha) (he.trans hi.symm)] at h
  · intro h; exact ⟨a, ha, hi, h⟩

theorem number_adjB (hB : Set.InjOn eb SB) {b : B} (hb : b ∈ SB) (j : Fin N) (hj : eb b = j.val)
    (m : V) : (I.number SA SB ea eb N).adjB m j ↔ I.adjB m b := by
  constructor
  · rintro ⟨b', hb', he, h⟩
    rwa [hB (Finset.mem_coe.2 hb') (Finset.mem_coe.2 hb) (he.trans hj.symm)] at h
  · intro h; exact ⟨b, hb, hj, h⟩

/-- **The counts**: the oracle's answer at the numbered position of `(a, b)` is `#Lop(a, b)`
of the original instance. -/
theorem number_count (hA : Set.InjOn ea SA) (hB : Set.InjOn eb SB)
    (hAN : ∀ a ∈ SA, ea a < N) (hBN : ∀ b ∈ SB, eb b < N) {a : A} {b : B}
    (ha : a ∈ SA) (hb : b ∈ SB) :
    (I.number SA SB ea eb N).countAt (ea a) (eb b) = I.count a b := by
  classical
  unfold countAt
  rw [dif_pos ⟨hAN a ha, hBN b hb⟩]
  unfold LopInst.count
  rw [number_mid]
  congr 1
  apply Finset.filter_congr
  intro m _
  rw [number_adjA hA ha ⟨ea a, hAN a ha⟩ rfl, number_adjB hB hb ⟨eb b, hBN b hb⟩ rfl]

/-- **The answers** of the detection oracle at numbered positions. -/
theorem number_accepts (hA : Set.InjOn ea SA) (hB : Set.InjOn eb SB)
    (hAN : ∀ a ∈ SA, ea a < N) (hBN : ∀ b ∈ SB, eb b < N) {a : A} {b : B}
    (ha : a ∈ SA) (hb : b ∈ SB) :
    (I.number SA SB ea eb N).AcceptsAt (ea a) (eb b) ↔ I.Accepts a b := by
  constructor
  · intro hx
    obtain ⟨hh, hx⟩ := hx
    obtain ⟨m, hm, h12⟩ := hx
    obtain ⟨h1, h2⟩ := h12
    exact ⟨m, hm, (number_adjA hA ha ⟨ea a, hAN a ha⟩ rfl m).1 h1,
      (number_adjB hB hb ⟨eb b, hBN b hb⟩ rfl m).1 h2⟩
  · rintro ⟨m, hm, h1, h2⟩
    exact ⟨⟨hAN a ha, hBN b hb⟩, m, hm, (number_adjA hA ha ⟨ea a, hAN a ha⟩ rfl m).2 h1,
      (number_adjB hB hb ⟨eb b, hBN b hb⟩ rfl m).2 h2⟩

/-- **The query pairs**: the numbered query pairs are exactly the images of those of `I`. -/
theorem number_queries (hW : I.W ⊆ SA ×ˢ SB)
    (hAN : ∀ a ∈ SA, ea a < N) (hBN : ∀ b ∈ SB, eb b < N) :
    (I.number SA SB ea eb N).queries = I.W.image fun x => (ea x.1, eb x.2) := by
  classical
  ext ⟨i, j⟩
  simp only [queries, number, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, ⟨x, hx, h1, h2⟩, he⟩
    refine ⟨x, hx, ?_⟩
    rw [h1, h2]; exact he
  · rintro ⟨x, hx, he⟩
    have hab := Finset.mem_product.1 (hW hx)
    exact ⟨(⟨ea x.1, hAN _ hab.1⟩, ⟨eb x.2, hBN _ hab.2⟩), ⟨x, hx, rfl, rfl⟩, he⟩

theorem mem_number_queries (hW : I.W ⊆ SA ×ˢ SB)
    (hAN : ∀ a ∈ SA, ea a < N) (hBN : ∀ b ∈ SB, eb b < N) {a : A} {b : B} (hab : (a, b) ∈ I.W) :
    (ea a, eb b) ∈ (I.number SA SB ea eb N).queries := by
  rw [number_queries hW hAN hBN]
  exact Finset.mem_image.2 ⟨(a, b), hab, rfl⟩

/-- **The number of query pairs** is unchanged. -/
theorem number_W_card (hA : Set.InjOn ea SA) (hB : Set.InjOn eb SB) (hW : I.W ⊆ SA ×ˢ SB)
    (hAN : ∀ a ∈ SA, ea a < N) (hBN : ∀ b ∈ SB, eb b < N) :
    (I.number SA SB ea eb N).W.card = I.W.card := by
  rw [← queries_card, number_queries hW hAN hBN]
  apply Finset.card_image_of_injOn
  intro x hx y hy h
  simp only [Prod.mk.injEq] at h
  have hx' := Finset.mem_product.1 (hW (Finset.mem_coe.1 hx))
  have hy' := Finset.mem_product.1 (hW (Finset.mem_coe.1 hy))
  exact Prod.ext (hA (Finset.mem_coe.2 hx'.1) (Finset.mem_coe.2 hy'.1) h.1)
    (hB (Finset.mem_coe.2 hx'.2) (Finset.mem_coe.2 hy'.2) h.2)

/-- The count does not depend on the query pairs. -/
theorem countAt_congr_W {N : ℕ} (J J' : LopInst (Fin N) (Fin N) V) (hmid : J.mid = J'.mid)
    (hA : J.adjA = J'.adjA) (hB : J.adjB = J'.adjB) (i j : ℕ) : J.countAt i j = J'.countAt i j := by
  cases J; cases J'
  simp only at hmid hA hB
  subst hmid hA hB
  rfl

end number

end LopInst

/-- With the canonical numbering of a vertex set of at most `N` elements: injective, below `N`. -/
theorem numbering_spec {α : Type*} (s : Finset α) (N : ℕ) (hN : s.card ≤ N) :
    Set.InjOn (numbering s) s ∧ ∀ a ∈ s, numbering s a < N :=
  ⟨numbering_injOn s, fun _ ha => (numbering_lt s ha).trans_le hN⟩

end Xor

namespace Xor.Improved

open Xor Finset

variable {d : ℕ}

/-! ### Linear maps: the target of a row list, split in two halves -/

/-- `|rows| = ⌈|rows|/2⌉ + ⌊|rows|/2⌋`. -/
theorem rows_split (rows : List (Vec d)) :
    rows.length = (rows.length + 1) / 2 + rows.length / 2 := by omega

/-- Renumbering the coordinates along `m = m'`. -/
noncomputable def castVec {m m' : ℕ} (h : m = m') : Vec m ≃ₗ[ZMod 2] Vec m' :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) (finCongr h.symm)

/-- The map with rows `rows`, its target `F₂^l` written as `F₂^{⌈l/2⌉} × F₂^{⌊l/2⌋}` (§4.4). -/
noncomputable def splitMap (rows : List (Vec d)) :
    Vec d →ₗ[ZMod 2] Vec ((rows.length + 1) / 2 + rows.length / 2) :=
  (castVec (rows_split rows)).toLinearMap ∘ₗ rowsMap rows

theorem splitMap_eq_zero_iff (rows : List (Vec d)) (x : Vec d) :
    splitMap rows x = 0 ↔ rowsMap rows x = 0 := by
  unfold splitMap
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  exact (castVec (rows_split rows)).map_eq_zero_iff

/-- `cnt_H` depends only on the kernel of `H`. -/
theorem Cands.cnt_congr {X ι : Type*} (C : Cands X ι d) {m m' : ℕ} (H : Vec d →ₗ[ZMod 2] Vec m)
    (H' : Vec d →ₗ[ZMod 2] Vec m') (hH : ∀ v, H v = 0 ↔ H' v = 0) (x : X) :
    C.cnt H x = C.cnt H' x := by
  unfold Cands.cnt
  congr 1
  exact Finset.filter_congr fun j _ => hH _

theorem cnt_splitMap {X ι : Type*} (C : Cands X ι d) (rows : List (Vec d)) (x : X) :
    C.cnt (splitMap rows) x = C.cnt (rowsMap rows) x :=
  C.cnt_congr _ _ (splitMap_eq_zero_iff rows) x

/-! ### The vertices of `I(H, 𝒫)` and their numbering -/

variable {S₁ S₂ S₃ : Finset (Vec d)} {k : ℕ} {π : Vec d →ₗ[ZMod 2] Vec k} {σ : ℕ}

/-- The left vertices `(b₂, u)` of `I(H, 𝒫)`: a block of list 2 and `u ∈ F₂^{l₁}`. -/
def leftVerts (B₂ : Blocking S₂ π σ) (l₁ : ℕ) : Finset (Finset (Vec d) × Vec l₁) :=
  (B₂.set.image Prod.snd) ×ˢ univ

/-- The right vertices `(b₃, v)`: a block of list 3 and `v ∈ F₂^{l₂}`. -/
def rightVerts (B₃ : Blocking S₃ π σ) (l₂ : ℕ) : Finset (Finset (Vec d) × Vec l₂) :=
  (B₃.set.image Prod.snd) ×ˢ univ

theorem leftVerts_card_le (B₂ : Blocking S₂ π σ) (l₁ g' : ℕ) (hg : B₂.set.card ≤ g') :
    (leftVerts B₂ l₁).card ≤ g' * 2 ^ l₁ := by
  unfold leftVerts
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  exact Nat.mul_le_mul_right _ (Finset.card_image_le.trans hg)

theorem rightVerts_card_le (B₃ : Blocking S₃ π σ) {l₁ l₂ : ℕ} (hl : l₂ ≤ l₁) (g' : ℕ)
    (hg : B₃.set.card ≤ g') : (rightVerts B₃ l₂).card ≤ g' * 2 ^ l₁ := by
  unfold rightVerts
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  exact Nat.mul_le_mul (Finset.card_image_le.trans hg) (Nat.pow_le_pow_right (by norm_num) hl)

variable {l₁ l₂ : ℕ}

/-- The position of a probe of `𝒫₀` is a pair of vertices of `I(H, 𝒫)`. -/
theorem pos_mem_verts (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) {Q : Probe d k} (hQ : Q ∈ probes S₁ π B₂ B₃) :
    (pos H Q).1 ∈ leftVerts B₂ l₁ ∧ (pos H Q).2 ∈ rightVerts B₃ l₂ := by
  simp only [probes, Finset.mem_filter, Finset.mem_product] at hQ
  refine ⟨Finset.mem_product.2 ⟨Finset.mem_image.2 ⟨Q.2.1, hQ.1.2.1, rfl⟩, Finset.mem_univ _⟩,
    Finset.mem_product.2 ⟨Finset.mem_image.2 ⟨Q.2.2, hQ.1.2.2, rfl⟩, Finset.mem_univ _⟩⟩

/-- The positions of a set of probes of `𝒫₀` lie in the vertex sets. -/
theorem pos_image_subset (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) {P : Finset (Probe d k)}
    (hP : P ⊆ probes S₁ π B₂ B₃) :
    P.image (pos H) ⊆ leftVerts B₂ l₁ ×ˢ rightVerts B₃ l₂ := by
  intro x hx
  obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 hx
  exact Finset.mem_product.2 (pos_mem_verts B₂ B₃ H (hP hQ))

/-- An instance on the vertices `(b₂, u)`, `(b₃, v)`, numbered into `Fin (g' 2^{l₁})`: the
`N = g' 2^{l₁}` of §4.4, the `g'` block slots of each list padded with isolated vertices. -/
noncomputable def probeNum {V : Type*} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' : ℕ)
    (I : LopInst (Finset (Vec d) × Vec l₁) (Finset (Vec d) × Vec l₂) V) :
    LopInst (Fin (g' * 2 ^ l₁)) (Fin (g' * 2 ^ l₁)) V :=
  I.number (leftVerts B₂ l₁) (rightVerts B₃ l₂) (numbering (leftVerts B₂ l₁))
    (numbering (rightVerts B₃ l₂)) (g' * 2 ^ l₁)

/-- The numbered position of a probe. -/
noncomputable def posNum (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) (Q : Probe d k) : ℕ × ℕ :=
  (numbering (leftVerts B₂ l₁) (pos H Q).1, numbering (rightVerts B₃ l₂) (pos H Q).2)

/-- The facts on `probeNum`: `Lop(g' 2^{l₁}, D)` iff the middle part has at most `D` vertices;
for a probe of `𝒫₀`, the count and the answer at its numbered position are those at its
position; the numbered query pairs are the numbered positions of the query pairs, and as many.
Needs at most `g'` blocks per list and `l₂ ≤ l₁`. -/
theorem probeNum_spec {V : Type*} (B₂ : Blocking S₂ π σ) (B₃ : Blocking S₃ π σ) (g' : ℕ)
    (hg₂ : B₂.set.card ≤ g') (hg₃ : B₃.set.card ≤ g') (hl : l₂ ≤ l₁)
    (I : LopInst (Finset (Vec d) × Vec l₁) (Finset (Vec d) × Vec l₂) V)
    (H : Vec d →ₗ[ZMod 2] Vec (l₁ + l₂)) :
    (∀ D, (probeNum B₂ B₃ g' I).IsLop (g' * 2 ^ l₁) D ↔ I.mid.card ≤ D) ∧
    (∀ Q ∈ probes S₁ π B₂ B₃,
      (probeNum B₂ B₃ g' I).countAt (posNum B₂ B₃ H Q).1 (posNum B₂ B₃ H Q).2 =
        I.count (pos H Q).1 (pos H Q).2 ∧
      ((probeNum B₂ B₃ g' I).AcceptsAt (posNum B₂ B₃ H Q).1 (posNum B₂ B₃ H Q).2 ↔
        I.Accepts (pos H Q).1 (pos H Q).2)) ∧
    (I.W ⊆ leftVerts B₂ l₁ ×ˢ rightVerts B₃ l₂ →
      (probeNum B₂ B₃ g' I).queries = I.W.image (fun x =>
        (numbering (leftVerts B₂ l₁) x.1, numbering (rightVerts B₃ l₂) x.2)) ∧
      (probeNum B₂ B₃ g' I).W.card = I.W.card) := by
  obtain ⟨hA, hAN⟩ := numbering_spec _ _ (leftVerts_card_le B₂ l₁ g' hg₂)
  obtain ⟨hB, hBN⟩ := numbering_spec _ _ (rightVerts_card_le B₃ hl g' hg₃)
  unfold probeNum posNum
  refine ⟨fun D => LopInst.number_isLop _ _ _ _ _ _ D, fun Q hQ => ?_, fun hW => ?_⟩
  · obtain ⟨h1, h2⟩ := pos_mem_verts B₂ B₃ H hQ
    exact ⟨LopInst.number_count hA hB hAN hBN h1 h2, LopInst.number_accepts hA hB hAN hBN h1 h2⟩
  · exact ⟨LopInst.number_queries hW hAN hBN, LopInst.number_W_card hA hB hW hAN hBN⟩

end Xor.Improved

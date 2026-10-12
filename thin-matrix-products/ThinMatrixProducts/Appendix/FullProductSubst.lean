import ThinMatrixProducts.Appendix.FullProductLemma1
/-! # Thin full products: the substitution method, and Lemma 6

`fp_subst` is the substitution step in linear-algebra form. Let `Y₀` be a set of coordinates and
suppose the restrictions `p_l = v_l|_{Y₀}` of a family of vectors span `K^{Y₀}`. Choose `|Y₀|` of
them forming a basis (indices `S`), and let `π x = x - ∑_{k ∈ S} coord_k(x|_{Y₀}) v_k`. Then `π` is
linear, kills every `v_k` with `k ∈ S`, and fixes every vector vanishing on `Y₀`. Applied to a
decomposition, `π` on one factor gives a decomposition of the image of the tensor in which the `|Y₀|`
terms of `S` vanish: this is "substituting the variables of `Y₀` by linear forms in the others".

Lemma 6. For `⟨o₁, b+1, o₂⟩`, take `Y₀ = {x_{i,b+1}}` (`o₁` coordinates). The slices of the tensor
along these variables have disjoint output supports, so the `u_l|_{Y₀}` span `K^{o₁}`. After `π`,
restricting to the right variables `y_{j c}`, `j ≤ b` (setting `y_{b+1, ·} = 0`), the tensor becomes
`⟨o₁, b, o₂⟩`, with `o₁` fewer terms. Induction down to `b = 1`, where `R ≥ n` (`fp_rank_ge_n`).
The bound with `o₂` follows by transposing. -/
namespace ThinMatrixProducts

open Finset

section FullProductSubst

variable {K : Type} [Field K]

/-- The substitution step. -/
lemma fp_subst {ι Y : Type} [Fintype ι] [Fintype Y] [DecidableEq Y] (Y₀ : Finset Y)
    (v : ι → Y → K)
    (hspan : ∀ y₀ ∈ Y₀, ∃ g : ι → K, ∀ y ∈ Y₀, ∑ l, g l * v l y = if y = y₀ then 1 else 0) :
    ∃ S : Finset ι, S.card = Y₀.card ∧ ∃ π : (Y → K) →ₗ[K] (Y → K),
      (∀ l ∈ S, π (v l) = 0) ∧ ∀ x : Y → K, (∀ y ∈ Y₀, x y = 0) → π x = x := by
  classical
  let r : (Y → K) →ₗ[K] (Y₀ → K) := LinearMap.funLeft K K (Subtype.val : Y₀ → Y)
  let p : ι → Y₀ → K := fun l => r (v l)
  have hr : ∀ x y₀, r x y₀ = x y₀ := fun _ _ => rfl
  -- the `p l` span `K^{Y₀}`
  have htop : ⊤ ≤ Submodule.span K (Set.range p) := by
    intro q _
    have hsingle : ∀ y₀ : Y₀, (Pi.single y₀ (1 : K) : Y₀ → K) ∈ Submodule.span K (Set.range p) := by
      intro y₀
      obtain ⟨g, hg⟩ := hspan y₀ y₀.2
      have : (Pi.single y₀ (1 : K) : Y₀ → K) = ∑ l, g l • p l := by
        funext y
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul, p, hr]
        rw [hg y y.2, Pi.single_apply]
        simp
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    have hq : q = ∑ y₀ : Y₀, q y₀ • (Pi.single y₀ (1 : K) : Y₀ → K) := by
      funext y
      rw [Finset.sum_apply]
      simp [Pi.single_apply]
    rw [hq]
    exact Submodule.sum_mem _ fun y₀ _ => Submodule.smul_mem _ _ (hsingle y₀)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K p
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let B : Module.Basis κ K (Y₀ → K) := Module.Basis.mk hli (by rw [hsp]; exact htop)
  have hcard : Fintype.card κ = Y₀.card := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  refine ⟨univ.map ⟨a, ha⟩, by rw [card_map, card_univ, hcard], ?_⟩
  let π : (Y → K) →ₗ[K] (Y → K) :=
    LinearMap.id - ∑ k, ((B.coord k).comp r).smulRight (v (a k))
  refine ⟨π, ?_, ?_⟩
  · intro l hl
    obtain ⟨m, -, rfl⟩ := Finset.mem_map.1 hl
    have hpm : r (v (a m)) = B m := by rw [Module.Basis.mk_apply]; rfl
    simp only [π, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
      LinearMap.smulRight_apply, LinearMap.comp_apply, Function.Embedding.coeFn_mk]
    rw [hpm]
    simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    rw [Finset.sum_eq_single m (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
    simp
  · intro x hx
    have hrx : r x = 0 := by funext y; exact hx y y.2
    simp [π, hrx]

/-- A sum over a subtype equals the sum over all indices if the summand vanishes outside it. -/
lemma fp_sum_subtype {ι M : Type} [Fintype ι] [AddCommMonoid M] (p : ι → Prop) [DecidablePred p]
    (f : ι → M) (h : ∀ l, ¬ p l → f l = 0) : ∑ l : {l // p l}, f l = ∑ l, f l := by
  rw [← Finset.sum_subtype (univ.filter p) (by simp) f]
  exact Finset.sum_filter_of_ne fun l _ hl => by_contra fun hp => hl (h l hp)

/-- A decomposition of `⟨o₁, b, o₂⟩` indexed by any finite type. -/
def IsMMDecomp' {ι : Type} [Fintype ι] {o₁ b o₂ : ℕ} (u : ι → Fin o₁ × Fin b → K)
    (v : ι → Fin b × Fin o₂ → K) (w : ι → Fin o₁ × Fin o₂ → K) : Prop :=
  ∀ a y z, ∑ l, u l a * v l y * w l z = mmTensor K o₁ b o₂ a y z

open scoped Classical in
/-- The terms with `w_l ≠ 0` alone form a decomposition. -/
lemma fp_restrict_nonzero {o₁ b o₂ R : ℕ} {u : Fin R → Fin o₁ × Fin b → K}
    {v : Fin R → Fin b × Fin o₂ → K} {w : Fin R → Fin o₁ × Fin o₂ → K} (hd : IsMMDecomp u v w) :
    IsMMDecomp' (ι := {l // w l ≠ 0}) (fun l => u l) (fun l => v l) (fun l => w l) := by
  classical
  intro a y z
  rw [← hd a y z]
  exact fp_sum_subtype (fun l => w l ≠ 0) (fun l => u l a * v l y * w l z)
    fun l hl => by rw [not_not.1 hl]; simp

/-- Transposing a decomposition of `⟨o₁, b, o₂⟩` gives one of `⟨o₂, b, o₁⟩`. -/
lemma fp_transpose {ι : Type} [Fintype ι] {o₁ b o₂ : ℕ} {u : ι → Fin o₁ × Fin b → K}
    {v : ι → Fin b × Fin o₂ → K} {w : ι → Fin o₁ × Fin o₂ → K} (hd : IsMMDecomp' u v w) :
    IsMMDecomp' (fun l (a : Fin o₂ × Fin b) => v l (a.2, a.1))
      (fun l (y : Fin b × Fin o₁) => u l (y.2, y.1)) (fun l (z : Fin o₂ × Fin o₁) => w l (z.2, z.1)) := by
  intro a y z
  have := hd (y.2, y.1) (a.2, a.1) (z.2, z.1)
  simp only [mmTensor] at this ⊢
  rw [show (∑ l, v l (a.2, a.1) * u l (y.2, y.1) * w l (z.2, z.1))
      = ∑ l, u l (y.2, y.1) * v l (a.2, a.1) * w l (z.2, z.1) from
      Finset.sum_congr rfl fun l _ => by ring, this]
  split_ifs with hA hB hB
  · rfl
  · exact absurd ⟨hA.2.2, hA.2.1.symm, hA.1⟩ hB
  · exact absurd ⟨hB.2.2, hB.2.1.symm, hB.1⟩ hA
  · rfl

/-- `R ≥ n` for a decomposition indexed by any finite type (from `fp_rank_ge_n`). -/
lemma fp_card_ge_n {ι : Type} [Fintype ι] {o₁ b o₂ : ℕ} {u : ι → Fin o₁ × Fin b → K}
    {v : ι → Fin b × Fin o₂ → K} {w : ι → Fin o₁ × Fin o₂ → K} (hd : IsMMDecomp' u v w)
    (hb : 1 ≤ b) : o₁ * o₂ ≤ Fintype.card ι := by
  classical
  set e := Fintype.equivFin ι
  have hd' : IsMMDecomp (fun l => u (e.symm l)) (fun l => v (e.symm l)) (fun l => w (e.symm l)) := by
    intro a y z
    rw [← hd a y z]
    exact Equiv.sum_comp e.symm (fun l => u l a * v l y * w l z)
  refine (fp_rank_ge_n K o₁ b o₂ _ _ _ _ hd' hb).trans ?_
  exact (Finset.card_le_univ _).trans (by simp)

open scoped Classical in
/-- One substitution step of Lemma 6: from `⟨o₁, b+1, o₂⟩` to `⟨o₁, b, o₂⟩`, killing `o₁` terms. -/
lemma fp_lemma6_step {ι : Type} [Fintype ι] {o₁ b o₂ : ℕ} (ho₂ : 1 ≤ o₂)
    {u : ι → Fin o₁ × Fin (b + 1) → K} {v : ι → Fin (b + 1) × Fin o₂ → K}
    {w : ι → Fin o₁ × Fin o₂ → K} (hd : IsMMDecomp' u v w) :
    ∃ S : Finset ι, S.card = o₁ ∧ ∃ (u' : {l // l ∉ S} → Fin o₁ × Fin b → K)
      (v' : {l // l ∉ S} → Fin b × Fin o₂ → K) (w' : {l // l ∉ S} → Fin o₁ × Fin o₂ → K),
      IsMMDecomp' u' v' w' := by
  classical
  set X₀ : Finset (Fin o₁ × Fin (b + 1)) := univ.filter fun a => a.2 = Fin.last b
  have hX₀ : X₀.card = o₁ := by
    rw [show X₀ = (univ : Finset (Fin o₁)) ×ˢ {Fin.last b} by
      ext ⟨i, j⟩; simp only [X₀, mem_filter, mem_univ, true_and, mem_product, mem_singleton]]
    simp
  have hspan : ∀ a₀ ∈ X₀, ∃ g : ι → K, ∀ a ∈ X₀,
      ∑ l, g l * u l a = if a = a₀ then 1 else 0 := by
    intro a₀ ha₀
    refine ⟨fun l => v l (Fin.last b, ⟨0, ho₂⟩) * w l (a₀.1, ⟨0, ho₂⟩), fun a ha => ?_⟩
    have h := hd a (Fin.last b, ⟨0, ho₂⟩) (a₀.1, ⟨0, ho₂⟩)
    simp only [X₀, Finset.mem_filter, Finset.mem_univ, true_and] at ha ha₀
    rw [show (∑ l, v l (Fin.last b, ⟨0, ho₂⟩) * w l (a₀.1, ⟨0, ho₂⟩) * u l a)
        = ∑ l, u l a * v l (Fin.last b, ⟨0, ho₂⟩) * w l (a₀.1, ⟨0, ho₂⟩) from
        Finset.sum_congr rfl fun l _ => by ring, h]
    simp only [mmTensor, ha, and_true]
    by_cases h1 : a.1 = a₀.1
    · simp [h1, Prod.ext_iff, ha, ha₀]
    · simp [h1, Prod.ext_iff]
  obtain ⟨S, hS, π, hπS, hπfix⟩ := fp_subst X₀ u hspan
  refine ⟨S, hS.trans hX₀, fun l a => π (u l) (a.1, a.2.castSucc),
    fun l y => v l (y.1.castSucc, y.2), fun l z => w l z, ?_⟩
  intro a y z
  -- the sum over `l ∉ S` equals the sum over all `l`, since `π u_l = 0` for `l ∈ S`
  have hall : ∑ l : {l // l ∉ S}, π (u l) (a.1, a.2.castSucc) * v l (y.1.castSucc, y.2) * w l z
      = ∑ l, π (u l) (a.1, a.2.castSucc) * v l (y.1.castSucc, y.2) * w l z := by
    exact fp_sum_subtype (fun l => l ∉ S)
      (fun l => π (u l) (a.1, a.2.castSucc) * v l (y.1.castSucc, y.2) * w l z)
      fun l hl => by rw [hπS l (not_not.1 hl)]; simp
  rw [hall]
  set T : Fin o₁ × Fin (b + 1) → K := fun a' => mmTensor K o₁ (b + 1) o₂ a' (y.1.castSucc, y.2) z
  have hT : T = ∑ l, (v l (y.1.castSucc, y.2) * w l z) • u l := by
    funext a'
    rw [Finset.sum_apply]
    simp only [T, Pi.smul_apply, smul_eq_mul, ← hd a' (y.1.castSucc, y.2) z]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hπT : π T = T := by
    refine hπfix T fun a' ha' => ?_
    simp only [X₀, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
    simp only [T, mmTensor, ha']
    rw [if_neg]
    rintro ⟨-, h, -⟩
    exact Fin.castSucc_ne_last _ h.symm
  have := congrFun hπT (a.1, a.2.castSucc)
  rw [hT, map_sum] at this
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
  rw [show (∑ l, π (u l) (a.1, a.2.castSucc) * v l (y.1.castSucc, y.2) * w l z)
      = ∑ l, v l (y.1.castSucc, y.2) * w l z * π (u l) (a.1, a.2.castSucc) from
      Finset.sum_congr rfl fun l _ => by ring, this]
  rw [show (∑ l, v l (y.1.castSucc, y.2) * w l z * u l (a.1, a.2.castSucc))
      = ∑ l, u l (a.1, a.2.castSucc) * v l (y.1.castSucc, y.2) * w l z from
      Finset.sum_congr rfl fun l _ => by ring, hd]
  simp only [mmTensor, Fin.castSucc_inj]

/-- Lemma 6 with `o₁`, for decompositions indexed by any finite type. -/
lemma fp_lemma6_o₁ (o₁ o₂ : ℕ) (ho₂ : 1 ≤ o₂) :
    ∀ b : ℕ, 1 ≤ b → ∀ (ι : Type) [Fintype ι] (u : ι → Fin o₁ × Fin b → K)
      (v : ι → Fin b × Fin o₂ → K) (w : ι → Fin o₁ × Fin o₂ → K),
      IsMMDecomp' u v w → o₁ * o₂ + (b - 1) * o₁ ≤ Fintype.card ι := by
  intro b hb
  induction b, hb using Nat.le_induction with
  | base =>
    intro ι _ u v w hd
    simpa using fp_card_ge_n hd le_rfl
  | succ b hb ih =>
    intro ι _ u v w hd
    classical
    obtain ⟨S, hS, u', v', w', hd'⟩ := fp_lemma6_step ho₂ hd
    have h := ih {l // l ∉ S} u' v' w' hd'
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hS] at h
    have hSle : o₁ ≤ Fintype.card ι := by
      rw [← hS]; exact Finset.card_le_univ S
    have : (b + 1 - 1) * o₁ = (b - 1) * o₁ + o₁ := by
      obtain ⟨b', rfl⟩ := Nat.exists_eq_add_of_le hb
      simp; ring
    omega

open scoped Classical in
theorem fp_Lemma_6 : FP_Lemma_6 := by
  intro K _ o₁ b o₂ R u v w hd ho₁ hb ho₂
  have hd' := fp_restrict_nonzero hd
  have hcard : Fintype.card {l // w l ≠ 0} = (univ.filter fun l => w l ≠ 0).card :=
    Fintype.card_subtype _
  have h1 := fp_lemma6_o₁ o₁ o₂ ho₂ b hb {l // w l ≠ 0} _ _ _ hd'
  have h2 := fp_lemma6_o₁ o₂ o₁ ho₁ b hb {l // w l ≠ 0} _ _ _ (fp_transpose hd')
  rw [hcard] at h1 h2
  rcases le_total o₁ o₂ with h | h
  · rw [max_eq_right h, mul_comm o₁ o₂]; exact h2
  · rw [max_eq_left h]; exact h1

end FullProductSubst

end ThinMatrixProducts

import Statements
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finiteness

/-!
# Lemma A.10: the normal form of the inner form

The proof follows the paper's. Write `F = ∑_r U_r ⊗ V'_r` with a basis `U` of the left support
`𝓛 = 𝓛(F)` (the column space) and coordinates `V'`. The coordinate space `E = K^{q₀}` stands for
`𝓛^*`: a basis `g` of `E` with dual basis `g^*` gives `F = ∑_x U(g_x) ⊗ V'(g^*_x)`. The basis `g`
is chosen adapted to two subspaces of `E`, `V₀ = U⁻¹(X)` (the paper's `V = 𝓛 ∩ X`) and
`Z = W₀^⊥`, where `W₀ = V'⁻¹(Y) ⊆ E^*` (the paper's `W'`): a basis of `V₀ ∩ Z`, extended to a basis
of `V₀` and to one of `Z`, the union extended to a basis of `E`. The bases `P`, `Q` of
the whole spaces are obtained in `lemma_A_10_basis`.
-/

namespace ThinMatrixProducts

open Module Submodule

section General

variable {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E]

/-- Two disjoint subsets of an independent set span disjoint subspaces. -/
lemma disjoint_span_of_subset {s A B : Set E} (hs : LinearIndepOn K id s) (hA : A ⊆ s)
    (hB : B ⊆ s) (hAB : Disjoint A B) : Disjoint (span K A) (span K B) :=
  ((linearIndepOn_id_union_iff hAB).1 (hs.mono (Set.union_subset hA hB))).2.2

/-- The members of `S` span `span(u) ∩ X` when they lie in `X` and the others span a space
meeting `X` only in `0`. -/
lemma span_image_eq_inf {ι : Type} {u : ι → E} (S : Set ι) (X : Submodule K E)
    (h1 : ∀ r ∈ S, u r ∈ X) (h2 : Disjoint (span K (u '' Sᶜ)) X) :
    span K (u '' S) = span K (Set.range u) ⊓ X := by
  have hSX : span K (u '' S) ≤ X := span_le.2 (by rintro _ ⟨r, hr, rfl⟩; exact h1 r hr)
  apply le_antisymm
  · exact le_inf (span_mono (Set.image_subset_range _ _)) hSX
  · intro x hx
    obtain ⟨hx, hX⟩ := mem_inf.1 hx
    have hrange : Set.range u = u '' S ∪ u '' Sᶜ := by
      rw [← Set.image_union, Set.union_compl_self, Set.image_univ]
    rw [hrange, span_union, mem_sup] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := hx
    have hzX : z ∈ X := by simpa using X.sub_mem hX (hSX hy)
    rw [(disjoint_def.1 h2) z hz hzX, add_zero]
    exact hy

lemma card_eq_finrank_inf {ι : Type} [Fintype ι] {u : ι → E} (hu : LinearIndependent K u)
    (S : Set ι) (X : Submodule K E) (h1 : ∀ r ∈ S, u r ∈ X)
    (h2 : Disjoint (span K (u '' Sᶜ)) X) :
    Nat.card S = finrank K ↥(span K (Set.range u) ⊓ X) := by
  classical
  rw [← span_image_eq_inf S X h1 h2, Set.image_eq_range, Nat.card_eq_fintype_card]
  exact (finrank_span_eq_card (hu.comp (Subtype.val : S → ι) Subtype.val_injective)).symm

/-- A family of `dim W` vectors whose span contains `W` is independent and spans `W`. -/
lemma indep_of_le {ι : Type} [Fintype ι] (u : ι → E) (W : Submodule K E) [FiniteDimensional K W]
    (hW : W ≤ span K (Set.range u)) (hc : Fintype.card ι ≤ finrank K W) :
    LinearIndependent K u ∧ span K (Set.range u) = W := by
  have : FiniteDimensional K (span K (Set.range u)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range u)
  have h1 := finrank_range_le_card (R := K) u
  have h2 := Submodule.finrank_mono hW
  have h3 : Set.finrank K (Set.range u) = finrank K (span K (Set.range u)) := rfl
  refine ⟨linearIndependent_iff_card_eq_finrank_span.2 (by omega),
    (eq_of_le_of_finrank_eq hW (by omega)).symm⟩

/-- A basis adapted to two subspaces. -/
lemma adapted [FiniteDimensional K E] (V0 Z : Submodule K E) :
    ∃ s s1 s2 : Set E, LinearIndepOn K id s ∧ span K s = ⊤ ∧ s1 ⊆ s ∧ s2 ⊆ s ∧
      s1 ⊆ V0 ∧ V0 ≤ span K s1 ∧ s2 ⊆ Z ∧ Z ≤ span K s2 := by
  have h0 := linearIndepOn_empty K (id : E → E)
  have hI : (∅ : Set E) ⊆ ((V0 ⊓ Z : Submodule K E) : Set E) := Set.empty_subset _
  set s0 := h0.extend hI
  have hs0 : LinearIndepOn K id s0 := h0.linearIndepOn_extend hI
  have hs0I : s0 ⊆ ((V0 ⊓ Z : Submodule K E) : Set E) := h0.extend_subset hI
  have hIs0 : ((V0 ⊓ Z : Submodule K E) : Set E) ⊆ span K s0 := h0.subset_span_extend hI
  have hs0V : s0 ⊆ V0 := fun x hx => (mem_inf.1 (hs0I hx)).1
  have hs0Z : s0 ⊆ Z := fun x hx => (mem_inf.1 (hs0I hx)).2
  set s1 := hs0.extend hs0V
  have hs1 : LinearIndepOn K id s1 := hs0.linearIndepOn_extend hs0V
  have hs01 : s0 ⊆ s1 := hs0.subset_extend hs0V
  have hs1V : s1 ⊆ V0 := hs0.extend_subset hs0V
  have hVs1 : (V0 : Set E) ⊆ span K s1 := hs0.subset_span_extend hs0V
  set s2 := hs0.extend hs0Z
  have hs2 : LinearIndepOn K id s2 := hs0.linearIndepOn_extend hs0Z
  have hs02 : s0 ⊆ s2 := hs0.subset_extend hs0Z
  have hs2Z : s2 ⊆ Z := hs0.extend_subset hs0Z
  have hZs2 : (Z : Set E) ⊆ span K s2 := hs0.subset_span_extend hs0Z
  have hdisj : Disjoint (span K s1) (span K (s2 \ s0)) := by
    rw [disjoint_def]
    intro x hx1 hx2
    have hxV : x ∈ V0 := span_le.2 hs1V hx1
    have hxZ : x ∈ Z := span_le.2 (Set.sdiff_subset.trans hs2Z) hx2
    have hx0 : x ∈ span K s0 := hIs0 (mem_inf.2 ⟨hxV, hxZ⟩)
    exact disjoint_def.1 (disjoint_span_of_subset hs2 hs02 Set.sdiff_subset Set.disjoint_sdiff_right)
      x hx0 hx2
  have h12 : LinearIndepOn K id (s1 ∪ (s2 \ s0)) :=
    hs1.id_union (hs2.mono Set.sdiff_subset) hdisj
  have heq : s1 ∪ (s2 \ s0) = s1 ∪ s2 := by
    ext x
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr h.1
    · rintro (h | h)
      · exact Or.inl h
      · by_cases h0 : x ∈ s0
        · exact Or.inl (hs01 h0)
        · exact Or.inr ⟨h, h0⟩
  rw [heq] at h12
  have hsub : s1 ∪ s2 ⊆ (Set.univ : Set E) := Set.subset_univ _
  refine ⟨h12.extend hsub, s1, s2, h12.linearIndepOn_extend hsub, ?_,
    Set.subset_union_left.trans (h12.subset_extend hsub),
    Set.subset_union_right.trans (h12.subset_extend hsub), hs1V, hVs1, hs2Z, hZs2⟩
  rw [eq_top_iff]
  intro x _
  exact h12.subset_span_extend hsub (Set.mem_univ x)

end General

/-- The linear map `E^* → B`, `φ ↦ ∑_r φ(e_r) V'_r`. -/
def vdual {K : Type} [Field K] {q : ℕ} {B : Type} [AddCommGroup B] [Module K B] (V' : Fin q → B) :
    Module.Dual K (Fin q → K) →ₗ[K] B where
  toFun φ := ∑ r, φ (Pi.single r 1) • V' r
  map_add' φ ψ := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c φ := by simp [Finset.smul_sum, smul_smul]

lemma vdual_apply {K : Type} [Field K] {q : ℕ} {B : Type} [AddCommGroup B] [Module K B]
    (V' : Fin q → B) (φ : Module.Dual K (Fin q → K)) :
    vdual V' φ = ∑ r, φ (Pi.single r 1) • V' r := rfl

lemma mulVec_sum_vecMulVec {K : Type} [Field K] {IA IB ι : Type} [Fintype IB] [Fintype ι]
    (u : ι → IA → K) (v : ι → IB → K) (y : IB → K) :
    Matrix.mulVec (∑ x, Matrix.vecMulVec (u x) (v x)) y = ∑ x, dotProduct (v x) y • u x := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.vecMulVec_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun j _ => by ring

lemma transpose_sum_vecMulVec {K : Type} [Field K] {IA IB ι : Type} [Fintype ι]
    (u : ι → IA → K) (v : ι → IB → K) :
    Matrix.transpose (∑ x, Matrix.vecMulVec (u x) (v x)) = ∑ x, Matrix.vecMulVec (v x) (u x) := by
  ext i j
  simp [Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm]

theorem lemma_A_10 : Lemma_A_10 := by
  intro K _ a b F X Y
  classical
  set q := F.rank with hq
  set LF := LinearMap.range F.mulVecLin with hLF
  let bL : Basis (Fin q) K LF := Module.finBasisOfFinrankEq K LF rfl
  let U : Fin q → (Fin a → K) := fun r => (bL r : Fin a → K)
  let col : Fin b → LF := fun j => ⟨F.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  let V' : Fin q → (Fin b → K) := fun r j => bL.repr (col j) r
  have hF : ∀ i j, F i j = ∑ r, U r i * V' r j := by
    intro i j
    have h := congrArg (fun x : LF => (x : Fin a → K) i) (bL.sum_repr (col j))
    have hcolval : ((col j : LF) : Fin a → K) = F.mulVecLin (Pi.single j 1) := rfl
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    rw [hcolval, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h
    have hc : F.col j i = F i j := rfl
    rw [← hc, ← h]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _
  let Ulin : (Fin q → K) →ₗ[K] (Fin a → K) := Fintype.linearCombination K U
  let Vd := vdual (K := K) V'
  let V0 : Submodule K (Fin q → K) := X.comap Ulin
  let W0 : Submodule K (Module.Dual K (Fin q → K)) := Y.comap Vd
  let Z : Submodule K (Fin q → K) := W0.dualCoannihilator
  obtain ⟨s, s1, s2, hs, hspan, hs1, hs2, hs1V, hVs1, hs2Z, hZs2⟩ := adapted V0 Z
  have hli : LinearIndependent K (fun x : s => (x : Fin q → K)) := hs.linearIndependent
  have hsp : ⊤ ≤ span K (Set.range (fun x : s => (x : Fin q → K))) := by
    rw [Subtype.range_coe, hspan]
  let g : Basis s K (Fin q → K) := Basis.mk hli hsp
  have hg : ∀ x : s, g x = x := fun x => Basis.mk_apply hli hsp x
  let _ : Fintype s := FiniteDimensional.fintypeBasisIndex g
  let u : s → (Fin a → K) := fun x => Ulin x
  let v : s → (Fin b → K) := fun x => Vd (g.coord x)
  -- the decomposition
  have key : ∀ r r', ∑ x : s, (x : Fin q → K) r * g.repr (Pi.single r' 1) x
      = if r = r' then 1 else 0 := by
    intro r r'
    have := congrFun (g.sum_repr (Pi.single r' 1)) r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hg, Pi.single_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hdecomp : F = ∑ x, Matrix.vecMulVec (u x) (v x) := by
    ext i j
    rw [hF, Matrix.sum_apply]
    simp only [u, v, Ulin, Vd, vdual_apply, Fintype.linearCombination_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Basis.coord_apply, Matrix.vecMulVec_apply]
    have e1 : ∀ x : s, (∑ r, (x : Fin q → K) r * U r i) *
        (∑ r', g.repr (Pi.single r' 1) x * V' r' j)
        = ∑ r, ∑ r', U r i * V' r' j * ((x : Fin q → K) r * g.repr (Pi.single r' 1) x) := by
      intro x
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => by ring
    rw [Finset.sum_congr rfl fun x _ => e1 x, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, key]
    simp
  -- the number of terms
  have hcard : Fintype.card s = q := by
    rw [← Module.finrank_eq_card_basis g, Module.finrank_fin_fun]
  -- independence and the supports
  have hLFle : LF ≤ span K (Set.range u) := by
    rintro _ ⟨y, rfl⟩
    rw [Matrix.mulVecLin_apply, hdecomp, mulVec_sum_vecMulVec]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (subset_span ⟨x, rfl⟩)
  obtain ⟨hu, hspu⟩ := indep_of_le u LF hLFle (by rw [hcard]; rfl)
  set RF := LinearMap.range F.transpose.mulVecLin with hRF
  have hRFle : RF ≤ span K (Set.range v) := by
    rintro _ ⟨y, rfl⟩
    rw [Matrix.mulVecLin_apply, hdecomp, transpose_sum_vecMulVec, mulVec_sum_vecMulVec]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (subset_span ⟨x, rfl⟩)
  have hRFrank : finrank K RF = q := Matrix.rank_transpose F
  obtain ⟨hv, hspv⟩ := indep_of_le v RF hRFle (by rw [hcard, hRFrank])
  -- the left side
  have hA1 : ∀ x ∈ {x : s | (x : Fin q → K) ∈ s1}, u x ∈ X := fun x hx => hs1V hx
  have hA2 : Disjoint (span K (u '' {x : s | (x : Fin q → K) ∈ s1}ᶜ)) X := by
    rw [disjoint_def]
    intro y hy hyX
    have himg : u '' {x : s | (x : Fin q → K) ∈ s1}ᶜ =
        Ulin '' (Subtype.val '' {x : s | (x : Fin q → K) ∈ s1}ᶜ) := by
      rw [Set.image_image]
    rw [himg, Submodule.span_image] at hy
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.1 hy
    have hcV : c ∈ span K s1 := hVs1 (show c ∈ V0 from hyX)
    have hcs : c ∈ span K (s \ s1) := by
      refine span_mono ?_ hc
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    rw [disjoint_def.1 (disjoint_span_of_subset hs hs1 Set.sdiff_subset
      Set.disjoint_sdiff_right) c hcV hcs, map_zero]
  -- the right side
  have hW0 : W0 = Z.dualAnnihilator := (Subspace.dualCoannihilator_dualAnnihilator_eq).symm
  have hB1 : ∀ x ∈ {x : s | (x : Fin q → K) ∉ s2}, v x ∈ Y := by
    intro x hx
    show g.coord x ∈ W0
    rw [hW0, mem_dualAnnihilator]
    intro z hz
    have hle : span K s2 ≤ LinearMap.ker (g.coord x) := by
      rw [span_le]
      intro y hy
      show g.coord x y = 0
      have : y = g ⟨y, hs2 hy⟩ := (hg ⟨y, hs2 hy⟩).symm
      rw [this, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg]
      intro h
      exact hx (h ▸ hy)
    exact hle (hZs2 hz)
  have hB2 : Disjoint (span K (v '' {x : s | (x : Fin q → K) ∉ s2}ᶜ)) Y := by
    rw [disjoint_def]
    intro y hy hyY
    have himg : v '' {x : s | (x : Fin q → K) ∉ s2}ᶜ =
        Vd '' (g.coord '' {x : s | (x : Fin q → K) ∉ s2}ᶜ) := by
      rw [Set.image_image]
    rw [himg, Submodule.span_image] at hy
    obtain ⟨φ, hφ, rfl⟩ := Submodule.mem_map.1 hy
    have hφW : φ ∈ W0 := hyY
    have hφ0 : φ = 0 := by
      apply g.ext
      intro x
      rw [LinearMap.zero_apply]
      by_cases hx : (x : Fin q → K) ∈ s2
      · have hxZ : (g x) ∈ Z := by rw [hg]; exact hs2Z hx
        exact (mem_dualCoannihilator _).1 hxZ φ hφW
      · have hle : span K (g.coord '' {x : s | (x : Fin q → K) ∉ s2}ᶜ) ≤
            LinearMap.ker (Module.Dual.eval K (Fin q → K) (g x)) := by
          rw [span_le]
          rintro _ ⟨x', hx', rfl⟩
          show g.coord x' (g x) = 0
          rw [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, if_neg]
          intro h
          exact hx (h ▸ (by simpa using hx'))
        exact hle hφ
    rw [hφ0, map_zero]
  refine ⟨s, inferInstance, u, v, {x : s | (x : Fin q → K) ∈ s1},
    {x : s | (x : Fin q → K) ∉ s2}, hcard, hu, hv, hdecomp, hA1, hA2, hB1, hB2, ?_, ?_⟩
  · rw [card_eq_finrank_inf hu _ X hA1 hA2, hspu]
  · rw [card_eq_finrank_inf hv _ Y hB1 hB2, hspv]

theorem lemma_A_10_basis : Lemma_A_10_basis := by
  intro K _ a ι _ u S X hu h1 h2
  classical
  set kX := finrank K X with hkX
  have hS : LinearIndepOn K id (u '' S) := (hu.linearIndepOn S).id_image
  have hSc : LinearIndepOn K id (u '' Sᶜ) := (hu.linearIndepOn Sᶜ).id_image
  have hSX : u '' S ⊆ X := by rintro _ ⟨r, hr, rfl⟩; exact h1 r hr
  set bX := hS.extend hSX
  have hbX : LinearIndepOn K id bX := hS.linearIndepOn_extend hSX
  have hSbX : u '' S ⊆ bX := hS.subset_extend hSX
  have hbXX : bX ⊆ X := hS.extend_subset hSX
  have hXbX : (X : Set (Fin a → K)) ⊆ span K bX := hS.subset_span_extend hSX
  have hspanX : span K bX = X := le_antisymm (span_le.2 hbXX) hXbX
  have hdis : Disjoint (span K bX) (span K (u '' Sᶜ)) := by rw [hspanX]; exact h2.symm
  have hT : LinearIndepOn K id (bX ∪ u '' Sᶜ) := hbX.id_union hSc hdis
  have hsub : bX ∪ u '' Sᶜ ⊆ (Set.univ : Set (Fin a → K)) := Set.subset_univ _
  set bA := hT.extend hsub
  have hbA : LinearIndepOn K id bA := hT.linearIndepOn_extend hsub
  have hTbA : bX ∪ u '' Sᶜ ⊆ bA := hT.subset_extend hsub
  have hbXA : bX ⊆ bA := Set.subset_union_left.trans hTbA
  have hli : LinearIndependent K (fun x : bA => (x : Fin a → K)) := hbA.linearIndependent
  have hsp : ⊤ ≤ span K (Set.range (fun x : bA => (x : Fin a → K))) := by
    rw [Subtype.range_coe]
    intro x _
    exact hT.subset_span_extend hsub (Set.mem_univ x)
  let gA : Basis bA K (Fin a → K) := Basis.mk hli hsp
  have hgA : ∀ x : bA, gA x = x := fun x => Basis.mk_apply hli hsp x
  let _ : Fintype bA := FiniteDimensional.fintypeBasisIndex gA
  let _ : Fintype bX := Set.fintypeSubset bA hbXA
  have hcardA : Fintype.card bA = a := by
    rw [← Module.finrank_eq_card_basis gA, Module.finrank_fin_fun]
  have hcardX : Fintype.card bX = kX := by
    rw [hkX, ← hspanX, finrank_span_set_eq_card hbX, Set.toFinset_card]
  let e0 : bX ⊕ (bA \ bX : Set (Fin a → K)) ≃ bA := Equiv.Set.sumDiffSubset hbXA
  have hcardR : Fintype.card (bA \ bX : Set (Fin a → K)) = a - kX := by
    have := Fintype.card_congr e0
    rw [Fintype.card_sum, hcardA, hcardX] at this
    omega
  have hka : kX + (a - kX) = a := by
    have := Submodule.finrank_le X
    rw [Module.finrank_fin_fun] at this
    omega
  let eX : Fin kX ≃ bX := (Fintype.equivFinOfCardEq hcardX).symm
  let eR : Fin (a - kX) ≃ (bA \ bX : Set (Fin a → K)) := (Fintype.equivFinOfCardEq hcardR).symm
  let e1 : Fin (kX + (a - kX)) ≃ bA := finSumFinEquiv.symm.trans ((Equiv.sumCongr eX eR).trans e0)
  let e : Fin a ≃ bA := (finCongr hka.symm).trans e1
  let P : Basis (Fin a) K (Fin a → K) := gA.reindex e.symm
  have hP : ∀ i, P i = (e i : Fin a → K) := by
    intro i
    simp only [P, Basis.reindex_apply, Equiv.symm_symm, hgA]
  -- membership in `X`
  have hnot : ∀ x ∈ bA \ bX, x ∉ X := by
    intro x hx hxX
    have h := (hbX.notMem_span_iff_id (a := x)).2
      ⟨hbA.mono (Set.insert_subset hx.1 hbXA), hx.2⟩
    exact h (hXbX hxX)
  have hmemX : ∀ i : Fin a, P i ∈ X ↔ (i : ℕ) < kX := by
    intro i
    rw [hP]
    obtain ⟨i', rfl⟩ : ∃ i' : Fin (kX + (a - kX)), (finCongr hka) i' = i :=
      ⟨(finCongr hka).symm i, by simp⟩
    have he : e ((finCongr hka) i') = e1 i' := by simp [e]
    rw [he]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i'
    · simp only [e1, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd, Equiv.sumCongr_apply,
        Sum.map_inl, e0, Equiv.Set.sumDiffSubset_apply_inl, Set.coe_inclusion, finCongr_apply,
        Fin.val_cast, Fin.val_castAdd]
      exact ⟨fun _ => j.isLt, fun _ => hbXX (eX j).2⟩
    · simp only [e1, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumCongr_apply,
        Sum.map_inr, e0, Equiv.Set.sumDiffSubset_apply_inr, Set.coe_inclusion, finCongr_apply,
        Fin.val_cast, Fin.val_natAdd]
      exact ⟨fun h => absurd h (hnot _ (eR j).2), fun h => by omega⟩
  -- the members of the family
  have hmem : ∀ r, u r ∈ bA := by
    intro r
    by_cases hr : r ∈ S
    · exact hbXA (hSbX ⟨r, hr, rfl⟩)
    · exact hTbA (Or.inr ⟨r, hr, rfl⟩)
  let σ : ι ↪ Fin a := ⟨fun r => e.symm ⟨u r, hmem r⟩, fun r r' h => by
    have := congrArg (fun x : bA => (x : Fin a → K)) (e.symm.injective h)
    exact hu.injective this⟩
  have hPσ : ∀ r, P (σ r) = u r := by
    intro r
    rw [hP]
    show ((e (e.symm ⟨u r, hmem r⟩) : bA) : Fin a → K) = u r
    rw [Equiv.apply_symm_apply]
  have huX : ∀ r, u r ∈ X ↔ r ∈ S := by
    intro r
    refine ⟨fun hX => ?_, h1 r⟩
    by_contra hr
    exact hu.ne_zero r (disjoint_def.1 h2 _ (subset_span ⟨r, hr, rfl⟩) hX)
  refine ⟨P, σ, hPσ, hmemX, fun r => ?_⟩
  rw [← hmemX, hPσ, huX]

end ThinMatrixProducts

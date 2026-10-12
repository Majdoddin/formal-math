import ThinMatrixProducts.Appendix.FullProductTight
import ThinMatrixProducts.Appendix.FullProductSubst
/-! # Thin full products: Lemma 5 (nonlocal coverers)

(a) The slice `B_e = ∑_{l covers e} w_l(e) u_l v_lᵀ = M_U M_V` (inner dimension `r_e`) has rank
`b`. Sylvester's inequality `rank M_U + rank M_V ≤ rank(M_U M_V) + r_e` (proved here from
rank–nullity, `fp_sylvester`) gives `dim U_e + dim V_e ≤ b + r_e`. The columns of `B_e` are the
basis vectors of `A_i`, so `A_i ⊆ U_e`; likewise `Y_c ⊆ V_e`. If a coverer is zero on one side,
`B_e` is a sum of `r_e - 1` rank-one matrices; if it leaves `A_i` (or `Y_c`), `dim U_e > b`.

(b) The `y`-flattening of `⟨o₁,b,o₂⟩|_W` maps `y_{jc}` to `x_{i(c) j} ⊗ z_{(i(c),c)}` (one output of
`W` per column), and equals `∑_l v_l ⊗ g_l` with `g_l = u_l ⊗ w_l|_W`; so the basis vectors of `G₀`
lie in `G_W`. A term meeting `W` only at `e` with `u_l(a) ≠ 0`, `a` outside row `i(e)`, gives a
vector `g_l` that is nonzero at the coordinate `(a, e)`, where all basis vectors of `G₀` and all
other such vectors vanish; so these vectors together with the basis of `G₀` are independent.
Summed over the rows of the grid (each row has one output per column): `∑_l min(|S_l|, o₁) ≥ b n +
|E_A|`; the column version by transposition.

(c) For `e` with fewer than `b` local coverers, `N_e = B_e - (local part)` is nonzero (the local
part has rank `< b`), lies in the block `A_i ⊗ Y_c`, and is a combination of the `u_l v_lᵀ` with `l`
not a pure singleton. Nonzero matrices in disjoint blocks are independent. -/
namespace ThinMatrixProducts

open Finset

section FullProductNonlocal

variable {K : Type} [Field K]

/-- A linearly independent family inside a subspace `P` has at most `dim P` members. -/
lemma fp_card_le_finrank {ι V : Type} [Fintype ι] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {f : ι → V} (hf : LinearIndependent K f) (P : Submodule K V)
    (h : ∀ i, f i ∈ P) : Fintype.card ι ≤ Module.finrank K P := by
  rw [← finrank_span_eq_card hf]
  exact Submodule.finrank_mono (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact h i))

/-- Sylvester's rank inequality: `rank A + rank B ≤ rank (A B) + n` for `A : m × n`, `B : n × p`. -/
lemma fp_sylvester {m n p : Type} [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
    [DecidableEq p] (A : Matrix m n K) (B : Matrix n p K) :
    A.rank + B.rank ≤ (A * B).rank + Fintype.card n := by
  set f := A.mulVecLin
  set g := B.mulVecLin
  set h := f.domRestrict (LinearMap.range g)
  have hAB : (A * B).rank = Module.finrank K (LinearMap.range h) := by
    rw [Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_domRestrict]
  have h1 := LinearMap.finrank_range_add_finrank_ker h
  have h3 : Module.finrank K (LinearMap.ker h) ≤ Module.finrank K (LinearMap.ker f) := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := LinearMap.codRestrict (LinearMap.ker f)
        ((LinearMap.range g).subtype ∘ₗ (LinearMap.ker h).subtype) fun c =>
          LinearMap.mem_ker.2 (by
            simp only [LinearMap.comp_apply, Submodule.subtype_apply]
            have := LinearMap.mem_ker.1 c.2
            rwa [LinearMap.domRestrict_apply] at this)) ?_
    intro x y hxy
    have := congrArg Subtype.val hxy
    simp only [LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply] at this
    exact Subtype.ext (Subtype.ext this)
  have h4 := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fintype_fun_eq_card] at h4
  have hB : B.rank = Module.finrank K (LinearMap.range g) := rfl
  have hA : A.rank = Module.finrank K (LinearMap.range f) := rfl
  omega

/-- The basis vectors `x_{ij}`, `j < b`, are independent. -/
lemma fp_single_li {o₁ b : ℕ} (i : Fin o₁) :
    LinearIndependent K (fun j : Fin b => (Pi.single (i, j) (1 : K) : Fin o₁ × Fin b → K)) := by
  have := (Pi.basisFun K (Fin o₁ × Fin b)).linearIndependent.comp (fun j : Fin b => (i, j))
    (fun j j' h => by simpa using h)
  convert this using 1
  funext j
  simp [Pi.basisFun_apply]

lemma fp_single_li' {b o₂ : ℕ} (c : Fin o₂) :
    LinearIndependent K (fun j : Fin b => (Pi.single (j, c) (1 : K) : Fin b × Fin o₂ → K)) := by
  have := (Pi.basisFun K (Fin b × Fin o₂)).linearIndependent.comp (fun j : Fin b => (j, c))
    (fun j j' h => by simpa using h)
  convert this using 1
  funext j
  simp [Pi.basisFun_apply]

/-- The rows of the slice `B_e` along the left variables of row `e.1`: a matrix of rank `b`. -/
lemma fp_slice_rank_ge {o₁ b o₂ : ℕ} (e : Fin o₁ × Fin o₂) :
    b ≤ (Matrix.of fun (j : Fin b) (y : Fin b × Fin o₂) => mmTensor K o₁ b o₂ (e.1, j) y e).rank := by
  classical
  have := card_le_rank_of_select
    (Matrix.of fun (j : Fin b) (y : Fin b × Fin o₂) => mmTensor K o₁ b o₂ (e.1, j) y e)
    (fun j => (j, e.2)) (by
      intro j j'
      simp only [Matrix.of_apply, mmTensor, true_and, and_true])
  simpa using this

theorem fp_Lemma_5a : FP_Lemma_5a := by
  classical
  intro K _ o₁ b o₂ R u v w hd e
  set C := fpCov w e
  set U := Submodule.span K (u '' ↑C)
  set V := Submodule.span K (v '' ↑C)
  have hsumU : ∀ f : Fin R → K, (∀ l, w l e = 0 → f l = 0) → ∑ l, f l • u l ∈ U := by
    intro f hf
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : w l e = 0
    · rw [hf l hl, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, by simp [C, fpCov, hl], rfl⟩)
  have hsumV : ∀ f : Fin R → K, (∀ l, w l e = 0 → f l = 0) → ∑ l, f l • v l ∈ V := by
    intro f hf
    refine Submodule.sum_mem _ fun l _ => ?_
    by_cases hl : w l e = 0
    · rw [hf l hl, zero_smul]; exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, by simp [C, fpCov, hl], rfl⟩)
  have hA : fpRowSpace K o₁ b e.1 ≤ U := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have : (Pi.single (e.1, j) (1 : K) : Fin o₁ × Fin b → K)
        = ∑ l, (v l (j, e.2) * w l e) • u l := by
      funext a
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (∑ l, v l (j, e.2) * w l e * u l a) = ∑ l, u l a * v l (j, e.2) * w l e from
        Finset.sum_congr rfl fun l _ => by ring, hd]
      simp only [mmTensor, Pi.single_apply]
      exact if_congr (by simp [Prod.ext_iff]) rfl rfl
    show (Pi.single (e.1, j) (1 : K) : Fin o₁ × Fin b → K) ∈ U
    rw [this]
    exact hsumU _ fun l hl => by rw [hl, mul_zero]
  have hY : fpColSpace K b o₂ e.2 ≤ V := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have : (Pi.single (j, e.2) (1 : K) : Fin b × Fin o₂ → K)
        = ∑ l, (u l (e.1, j) * w l e) • v l := by
      funext y
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [show (∑ l, u l (e.1, j) * w l e * v l y) = ∑ l, u l (e.1, j) * v l y * w l e from
        Finset.sum_congr rfl fun l _ => by ring, hd]
      simp only [mmTensor, Pi.single_apply]
      exact if_congr (by simp [Prod.ext_iff, eq_comm]) rfl rfl
    show (Pi.single (j, e.2) (1 : K) : Fin b × Fin o₂ → K) ∈ V
    rw [this]
    exact hsumV _ fun l hl => by rw [hl, mul_zero]
  have hdA : Module.finrank K (fpRowSpace K o₁ b e.1) = b := by
    unfold fpRowSpace
    rw [finrank_span_eq_card (fp_single_li e.1), Fintype.card_fin]
  have hdY : Module.finrank K (fpColSpace K b o₂ e.2) = b := by
    unfold fpColSpace
    rw [finrank_span_eq_card (fp_single_li' e.2), Fintype.card_fin]
  -- Sylvester
  let MU : Matrix (Fin o₁ × Fin b) C K := fun a l => u l a
  let MV : Matrix C (Fin b × Fin o₂) K := fun l y => w l e * v l y
  have hMU : MU.rank = Module.finrank K U := by
    rw [Matrix.rank_eq_finrank_span_cols]
    have : Set.range MU.col = u '' ↑C := by
      ext x
      constructor
      · rintro ⟨l, rfl⟩; exact ⟨l, l.2, rfl⟩
      · rintro ⟨l, hl, rfl⟩; exact ⟨⟨l, hl⟩, rfl⟩
    rw [this]
  have hMV : MV.rank = Module.finrank K V := by
    rw [Matrix.rank_eq_finrank_span_row]
    have : Submodule.span K (Set.range MV.row) = V := by
      refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨l, rfl⟩
        have : MV.row l = w l e • v l := by funext y; rfl
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, l.2, rfl⟩)
      · rintro _ ⟨l, hl, rfl⟩
        have hw : w l e ≠ 0 := by simpa [C, fpCov] using hl
        have : v l = (w l e)⁻¹ • MV.row ⟨l, hl⟩ := by
          funext y; simp [MV, Matrix.row, hw]
        rw [this]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩)
    rw [this]
  have hprod : (MU * MV).rank ≤ b := by
    have := rank_le_of_sum (MU * MV) (univ : Finset (Fin b))
      (fun j a => (Pi.single (e.1, j) (1 : K) : Fin o₁ × Fin b → K) a)
      (fun j y => (Pi.single (j, e.2) (1 : K) : Fin b × Fin o₂ → K) y) (by
        intro a y
        rw [Matrix.mul_apply]
        rw [show (∑ l : C, MU a l * MV l y) = ∑ l : C, u l a * v l y * w l e from
          Finset.sum_congr rfl fun l _ => by simp only [MU, MV]; ring, fp_sum_cov hd e a y]
        simp only [mmTensor, Pi.single_apply, Prod.ext_iff]
        by_cases h1 : a.1 = e.1
        · by_cases h3 : y.2 = e.2
          · simp [h1, h3, eq_comm]
          · simp [h3]
        · simp [h1])
    simpa using this
  have hsyl := fp_sylvester MU MV
  rw [hMU, hMV, Fintype.card_coe] at hsyl
  have hdim : Module.finrank K U + Module.finrank K V ≤ C.card + b := by omega
  refine ⟨hA, hY, hdA, hdY, hdim, ?_⟩
  -- a coverer that is not local
  rintro ⟨l₀, hl₀, hnl⟩
  have hVb : b ≤ Module.finrank K V := hdY.symm.le.trans (Submodule.finrank_mono hY)
  have hUb : b ≤ Module.finrank K U := hdA.symm.le.trans (Submodule.finrank_mono hA)
  unfold fpLocal at hnl
  by_cases hz : u l₀ = 0 ∨ v l₀ = 0
  · -- the slice is a sum of `r_e - 1` rank-one matrices
    have hle := rank_le_of_sum
      (Matrix.of fun (j : Fin b) (y : Fin b × Fin o₂) => mmTensor K o₁ b o₂ (e.1, j) y e)
      (C.erase l₀) (fun l j => u l (e.1, j) * w l e) (fun l y => v l y) (by
        intro j y
        simp only [Matrix.of_apply]
        rw [← hd]
        rw [Finset.sum_erase C (by rcases hz with h | h <;> simp [h])]
        rw [show C = univ.filter fun l => w l e ≠ 0 from rfl]
        rw [Finset.sum_filter_of_ne fun l _ h => by
          intro hw; exact h (by rw [hw]; ring)]
        exact Finset.sum_congr rfl fun l _ => by ring)
    have := (fp_slice_rank_ge (K := K) (b := b) e).trans hle
    rw [Finset.card_erase_of_mem hl₀] at this
    have : 1 ≤ C.card := Finset.card_pos.2 ⟨l₀, hl₀⟩
    omega
  · push Not at hz
    obtain ⟨hu0, hv0⟩ := hz
    have hnl' : ¬ ((∀ a : Fin o₁ × Fin b, a.1 ≠ e.1 → u l₀ a = 0) ∧
        ∀ y : Fin b × Fin o₂, y.2 ≠ e.2 → v l₀ y = 0) := fun h => hnl ⟨hu0, hv0, h.1, h.2⟩
    by_cases hua : ∀ a : Fin o₁ × Fin b, a.1 ≠ e.1 → u l₀ a = 0
    · -- `v l₀ ∉ Y_c`, so `dim V > b`
      have hvy : ¬ ∀ y : Fin b × Fin o₂, y.2 ≠ e.2 → v l₀ y = 0 := fun h => hnl' ⟨hua, h⟩
      push Not at hvy
      obtain ⟨y₀, hy₀, hvy₀⟩ := hvy
      have hlt : fpColSpace K b o₂ e.2 < V := by
        refine SetLike.lt_iff_le_and_exists.2 ⟨hY, v l₀,
          Submodule.subset_span ⟨l₀, hl₀, rfl⟩, fun hmem => hvy₀ ?_⟩
        have hker : fpColSpace K b o₂ e.2 ≤ LinearMap.ker (LinearMap.proj (R := K)
            (φ := fun _ : Fin b × Fin o₂ => K) y₀) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨j, rfl⟩
          simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_proj, Function.eval,
            Pi.single_apply, Prod.ext_iff]
          simp [hy₀]
        simpa using hker hmem
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    · push Not at hua
      obtain ⟨a₀, ha₀, hua₀⟩ := hua
      have hlt : fpRowSpace K o₁ b e.1 < U := by
        refine SetLike.lt_iff_le_and_exists.2 ⟨hA, u l₀,
          Submodule.subset_span ⟨l₀, hl₀, rfl⟩, fun hmem => hua₀ ?_⟩
        have hker : fpRowSpace K o₁ b e.1 ≤ LinearMap.ker (LinearMap.proj (R := K)
            (φ := fun _ : Fin o₁ × Fin b => K) a₀) := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨j, rfl⟩
          simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_proj, Function.eval,
            Pi.single_apply, Prod.ext_iff]
          simp [ha₀]
        simpa using hker hmem
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega

theorem fp_Lemma_5c : FP_Lemma_5c := by
  classical
  intro K _ o₁ b o₂ R u v w hd
  set lam : Fin o₁ × Fin o₂ → Finset (Fin R) :=
    fun e => (fpCov w e).filter fun l => fpLocal (u l) (v l) e
  refine ⟨?_, ?_⟩
  · set D := univ.filter fun l => w l ≠ 0 ∧ ¬ ∃ e, outSupp (w l) = {e} ∧ fpLocal (u l) (v l) e
    set E := univ.filter fun e : Fin o₁ × Fin o₂ => (lam e).card < b
    let M : Fin R → (Fin o₁ × Fin b → Fin b × Fin o₂ → K) := fun l a y => u l a * v l y
    let nl : Fin o₁ × Fin o₂ → Finset (Fin R) :=
      fun e => (fpCov w e).filter fun l => ¬ fpLocal (u l) (v l) e
    let N : E → (Fin o₁ × Fin b → Fin b × Fin o₂ → K) :=
      fun e a y => ∑ l ∈ nl e.1, w l e.1 * (u l a * v l y)
    -- the slice is the local part plus `N e`
    have hsplit : ∀ (e : Fin o₁ × Fin o₂) a y, mmTensor K o₁ b o₂ a y e
        = ∑ l ∈ lam e, w l e * (u l a * v l y) + ∑ l ∈ nl e, w l e * (u l a * v l y) := by
      intro e a y
      rw [Finset.sum_filter_add_sum_filter_not, ← hd a y e]
      rw [show (fpCov w e) = univ.filter fun l => w l e ≠ 0 from rfl]
      rw [Finset.sum_filter_of_ne fun l _ h => by intro hw; exact h (by rw [hw]; ring)]
      exact Finset.sum_congr rfl fun l _ => by ring
    have hsupp : ∀ (e : E) a y, N e a y ≠ 0 → a.1 = e.1.1 ∧ y.2 = e.1.2 := by
      intro e a y hN
      by_contra hc
      apply hN
      have hloc : ∑ l ∈ lam e.1, w l e.1 * (u l a * v l y) = 0 := by
        refine Finset.sum_eq_zero fun l hl => ?_
        obtain ⟨-, -, hA, hY⟩ := (Finset.mem_filter.1 hl).2
        by_cases h1 : a.1 = e.1.1
        · rw [hY y fun h2 => hc ⟨h1, h2⟩]; ring
        · rw [hA a h1]; ring
      have hT : mmTensor K o₁ b o₂ a y e.1 = 0 := by
        simp only [mmTensor]
        rw [if_neg]
        rintro ⟨h1, -, h3⟩
        exact hc ⟨h1, h3⟩
      have := hsplit e.1 a y
      rw [hT, hloc, zero_add] at this
      exact this.symm
    have hne : ∀ e : E, N e ≠ 0 := by
      intro e hN
      have hcard : (lam e.1).card < b := (Finset.mem_filter.1 e.2).2
      have hle := rank_le_of_sum
        (Matrix.of fun (j : Fin b) (y : Fin b × Fin o₂) => mmTensor K o₁ b o₂ (e.1.1, j) y e.1)
        (lam e.1) (fun l j => w l e.1 * u l (e.1.1, j)) (fun l y => v l y) (by
          intro j y
          simp only [Matrix.of_apply]
          rw [hsplit e.1 (e.1.1, j) y]
          have : ∑ l ∈ nl e.1, w l e.1 * (u l (e.1.1, j) * v l y) = 0 :=
            congrFun (congrFun hN (e.1.1, j)) y
          rw [this, add_zero]
          exact Finset.sum_congr rfl fun l _ => by ring)
      have := (fp_slice_rank_ge (K := K) (b := b) e.1).trans hle
      omega
    have hmem : ∀ e : E, N e ∈ Submodule.span K (M '' ↑D) := by
      intro e
      have : N e = ∑ l ∈ nl e.1, w l e.1 • M l := by
        funext a y
        simp only [N, M, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      refine Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, ?_, rfl⟩)
      obtain ⟨hcov, hnl⟩ := Finset.mem_filter.1 hl
      simp only [D, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      refine ⟨fun h0 => (Finset.mem_filter.1 hcov).2 (by rw [h0]; rfl), ?_⟩
      rintro ⟨e', he', hloc⟩
      have : e.1 ∈ outSupp (w l) := by simpa [outSupp, fpCov] using hcov
      rw [he', Finset.mem_singleton] at this
      exact hnl (this ▸ hloc)
    have hli : LinearIndependent K N := by
      refine Fintype.linearIndependent_iff.2 fun c hc e => ?_
      obtain ⟨a, ha⟩ := Function.ne_iff.1 (hne e)
      obtain ⟨y, hy⟩ := Function.ne_iff.1 ha
      have h0 := congrFun (congrFun hc a) y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
      rw [Finset.sum_eq_single e (fun e' _ he' => by
        by_cases h : N e' a y = 0
        · rw [h, mul_zero]
        · exfalso
          obtain ⟨h1, h2⟩ := hsupp e' a y h
          obtain ⟨h1', h2'⟩ := hsupp e a y hy
          exact he' (Subtype.ext (Prod.ext (h1.symm.trans h1') (h2.symm.trans h2'))))
        (by simp)] at h0
      exact (mul_eq_zero.1 h0).resolve_right hy
    have h1 := fp_card_le_finrank hli _ hmem
    rw [Fintype.card_coe] at h1
    refine h1.trans ?_
    rw [show M '' ↑D = ↑(D.image M) by simp]
    exact (finrank_span_finset_le_card _).trans Finset.card_image_le
  · have hdisj : ((univ : Finset (Fin o₁ × Fin o₂)) : Set (Fin o₁ × Fin o₂)).PairwiseDisjoint lam := by
      intro e _ e' _ hne
      refine Finset.disjoint_left.2 fun l hl hl' => hne ?_
      exact fp_local_unique K o₁ b o₂ (u l) (v l) e e' (Finset.mem_filter.1 hl).2
        (Finset.mem_filter.1 hl').2
    rw [← Finset.card_biUnion hdisj]
    refine Finset.card_le_card fun l hl => ?_
    obtain ⟨e, -, hl⟩ := Finset.mem_biUnion.1 hl
    have := (Finset.mem_filter.1 hl).1
    simp only [fpCov, Finset.mem_filter, Finset.mem_univ, true_and] at this ⊢
    exact fun h => this (by rw [h]; rfl)

theorem fp_Lemma_5b : FP_Lemma_5b := by
  classical
  intro K _ o₁ b o₂ R u v w hd W hW
  set g : Fin R → (Fin o₁ × Fin b) × (Fin o₁ × Fin o₂) → K :=
    fun l q => if q.2 ∈ W then u l q.1 * w l q.2 else 0
  set meet := univ.filter fun l => ∃ z ∈ W, w l z ≠ 0
  have hgen : ∀ l, g l ∈ fpGW u w W := by
    intro l
    by_cases hl : ∃ z ∈ W, w l z ≠ 0
    · exact Submodule.subset_span ⟨l, hl, rfl⟩
    · have : g l = 0 := by
        funext q
        simp only [g, Pi.zero_apply]
        split_ifs with hq
        · push Not at hl
          rw [hl q.2 hq, mul_zero]
        · rfl
      rw [this]; exact Submodule.zero_mem _
  let f : Fin b × W → (Fin o₁ × Fin b) × (Fin o₁ × Fin o₂) → K :=
    fun p => Pi.single ((p.2.1.1, p.1), p.2.1) 1
  have hf_li : LinearIndependent K f := by
    have := (Pi.basisFun K ((Fin o₁ × Fin b) × (Fin o₁ × Fin o₂))).linearIndependent.comp
      (fun p : Fin b × W => ((p.2.1.1, p.1), p.2.1)) (by
        rintro ⟨j, e⟩ ⟨j', e'⟩ h
        simp only [Prod.mk.injEq] at h
        exact Prod.ext h.1.2 (Subtype.ext h.2))
    convert this using 1
    funext p
    simp [f, Pi.basisFun_apply]
  have hG0 : fpG0 K o₁ b W = Submodule.span K (Set.range f) := by
    unfold fpG0
    congr 1
    ext x
    constructor
    · rintro ⟨q, ⟨hq2, hq1⟩, rfl⟩
      refine ⟨(q.1.2, ⟨q.2, hq2⟩), ?_⟩
      simp only [f]
      congr 1
      exact Prod.ext (Prod.ext hq1.symm rfl) rfl
    · rintro ⟨p, rfl⟩
      exact ⟨((p.2.1.1, p.1), p.2.1), ⟨p.2.2, rfl⟩, rfl⟩
  have hfmem : ∀ p, f p ∈ fpGW u w W := by
    intro p
    have : f p = ∑ l, v l (p.1, p.2.1.2) • g l := by
      funext q
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, g, f]
      by_cases hq : q.2 ∈ W
      · simp only [hq, if_true]
        rw [show (∑ l, v l (p.1, p.2.1.2) * (u l q.1 * w l q.2))
            = ∑ l, u l q.1 * v l (p.1, p.2.1.2) * w l q.2 from
            Finset.sum_congr rfl fun l _ => by ring, hd]
        simp only [mmTensor, Pi.single_apply]
        refine if_congr ?_ rfl rfl
        constructor
        · intro h
          rw [h]
          exact ⟨rfl, rfl, rfl⟩
        · rintro ⟨h1, h2, h3⟩
          have : q.2 = p.2.1 := hW _ hq _ p.2.2 h3.symm
          exact Prod.ext (Prod.ext (h1.trans (congrArg Prod.fst this)) h2) this
      · simp only [hq, if_false, mul_zero, Finset.sum_const_zero]
        rw [Pi.single_apply, if_neg]
        intro h
        exact hq (h ▸ p.2.2)
    rw [this]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hgen l)
  have hG0le : fpG0 K o₁ b W ≤ fpGW u w W := by
    rw [hG0]
    exact Submodule.span_le.2 (by rintro _ ⟨p, rfl⟩; exact hfmem p)
  have hdG0 : Module.finrank K (fpG0 K o₁ b W) = b * W.card := by
    rw [hG0, finrank_span_eq_card hf_li]
    simp
  have hdGW : Module.finrank K (fpGW u w W) ≤ meet.card := by
    unfold fpGW
    rw [show (g '' {l | ∃ z ∈ W, w l z ≠ 0}) = ↑(meet.image g) by
      ext x; simp [meet]]
    exact (finrank_span_finset_le_card _).trans Finset.card_image_le
  refine ⟨hG0le, hdG0, hdGW, ?_⟩
  -- the isolated nonlocal terms
  set E' := W.filter fun e => ∃ l, w l e ≠ 0 ∧ (∀ z ∈ W, w l z ≠ 0 → z = e) ∧
    ∃ a : Fin o₁ × Fin b, a.1 ≠ e.1 ∧ u l a ≠ 0
  have hE' : ∀ e : E', ∃ l, w l e.1 ≠ 0 ∧ (∀ z ∈ W, w l z ≠ 0 → z = e.1) ∧
      ∃ a : Fin o₁ × Fin b, a.1 ≠ e.1.1 ∧ u l a ≠ 0 := fun e => (Finset.mem_filter.1 e.2).2
  choose L hL1 hL2 A hA1 hA2 using hE'
  let F : (Fin b × W) ⊕ E' → (Fin o₁ × Fin b) × (Fin o₁ × Fin o₂) → K :=
    Sum.elim f fun e => g (L e)
  have hFmem : ∀ i, F i ∈ fpGW u w W := by
    rintro (p | e)
    · exact hfmem p
    · exact hgen _
  have hFli : LinearIndependent K F := by
    refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    rw [Fintype.sum_sum_type] at hc
    simp only [F, Sum.elim_inl, Sum.elim_inr] at hc
    have hinr : ∀ e : E', c (Sum.inr e) = 0 := by
      intro e
      have he : e.1 ∈ W := (Finset.mem_filter.1 e.2).1
      have h0 := congrFun hc (A e, e.1)
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
      have hf0 : ∀ p, f p (A e, e.1) = 0 := by
        intro p
        simp only [f, Pi.single_apply]
        rw [if_neg]
        intro h
        apply hA1 e
        have := congrArg (fun q => q.1.1) h
        have h2 := congrArg (fun q => q.2) h
        simp only at this h2
        rw [this, h2]
      simp only [hf0, mul_zero, Finset.sum_const_zero, zero_add] at h0
      rw [Finset.sum_eq_single e (fun e' _ he' => by
        simp only [g, he, if_true]
        by_cases hw : w (L e') e.1 = 0
        · rw [hw]; ring
        · exfalso; exact he' (Subtype.ext (hL2 e' e.1 he hw).symm)) (by simp)] at h0
      simp only [g, he, if_true] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exfalso
        rcases mul_eq_zero.1 h with h' | h'
        · exact hA2 e h'
        · exact hL1 e h'
    simp only [hinr, zero_smul, Finset.sum_const_zero, add_zero] at hc
    have hinl := Fintype.linearIndependent_iff.1 hf_li (fun p => c (Sum.inl p)) hc
    rintro (p | e)
    · exact hinl p
    · exact hinr e
  have := fp_card_le_finrank hFli _ hFmem
  rwa [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe,
    Fintype.card_coe] at this

/-- An output support is the singleton `{e}` iff `w(e) ≠ 0` and `w` vanishes elsewhere. -/
lemma fp_outSupp_eq_singleton {o₁ o₂ : ℕ} (x : Fin o₁ × Fin o₂ → K) (e : Fin o₁ × Fin o₂) :
    outSupp x = {e} ↔ x e ≠ 0 ∧ ∀ z, x z ≠ 0 → z = e := by
  classical
  rw [Finset.eq_singleton_iff_unique_mem]
  simp [outSupp]

open scoped Classical in
/-- Lemma 5 (b) summed over the rows of the grid. -/
lemma fp_5b_rows (o₁ b o₂ R : ℕ) (u : Fin R → Fin o₁ × Fin b → K)
    (v : Fin R → Fin b × Fin o₂ → K) (w : Fin R → Fin o₁ × Fin o₂ → K) (hd : IsMMDecomp u v w) :
    b * (o₁ * o₂) + (univ.filter fun e : Fin o₁ × Fin o₂ => ∃ l, outSupp (w l) = {e} ∧
        ∃ a : Fin o₁ × Fin b, a.1 ≠ e.1 ∧ u l a ≠ 0).card
      ≤ ∑ l, min (outSupp (w l)).card o₁ := by
  set EA := univ.filter fun e : Fin o₁ × Fin o₂ => ∃ l, outSupp (w l) = {e} ∧
    ∃ a : Fin o₁ × Fin b, a.1 ≠ e.1 ∧ u l a ≠ 0
  set Wr : Fin o₁ → Finset (Fin o₁ × Fin o₂) := fun r => univ.filter fun z => z.1 = r
  have hrow : ∀ r, b * o₂ + (EA.filter fun e => e.1 = r).card
      ≤ (univ.filter fun l => ∃ z ∈ Wr r, w l z ≠ 0).card := by
    intro r
    obtain ⟨-, -, h3, h4⟩ := fp_Lemma_5b K o₁ b o₂ R u v w hd (Wr r) (by
      intro e he e' he' hc
      simp only [Wr, Finset.mem_filter, Finset.mem_univ, true_and] at he he'
      exact Prod.ext (he.trans he'.symm) hc)
    have hWr : (Wr r).card = o₂ := by
      rw [show Wr r = ({r} : Finset (Fin o₁)) ×ˢ (univ : Finset (Fin o₂)) by
        ext ⟨i, c⟩; simp [Wr, eq_comm]]
      simp
    have hsub : (EA.filter fun e => e.1 = r) ⊆ ((Wr r).filter fun e => ∃ l, w l e ≠ 0 ∧
        (∀ z ∈ Wr r, w l z ≠ 0 → z = e) ∧ ∃ a : Fin o₁ × Fin b, a.1 ≠ e.1 ∧ u l a ≠ 0) := by
      intro e he
      simp only [EA, Finset.mem_filter, Finset.mem_univ, true_and] at he
      obtain ⟨⟨l, hl, a, ha1, ha2⟩, her⟩ := he
      rw [fp_outSupp_eq_singleton] at hl
      simp only [Wr, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨her, l, hl.1, fun z _ hz => hl.2 z hz, a, ha1, ha2⟩
    rw [hWr] at h4
    exact (Nat.add_le_add_left (Finset.card_le_card hsub) _).trans (h4.trans h3)
  have hEA : EA.card = ∑ r : Fin o₁, (EA.filter fun e => e.1 = r).card :=
    Finset.card_eq_sum_card_fiberwise (fun e _ => Finset.mem_univ e.1)
  calc b * (o₁ * o₂) + EA.card
      = ∑ r : Fin o₁, (b * o₂ + (EA.filter fun e => e.1 = r).card) := by
        rw [Finset.sum_add_distrib, ← hEA]; simp; ring
    _ ≤ ∑ r, (univ.filter fun l => ∃ z ∈ Wr r, w l z ≠ 0).card :=
        Finset.sum_le_sum fun r _ => hrow r
    _ = ∑ l, (univ.filter fun r => ∃ z ∈ Wr r, w l z ≠ 0).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ l, min (outSupp (w l)).card o₁ := by
        refine Finset.sum_le_sum fun l _ => le_min ?_ ?_
        · refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (f := Prod.fst))
          intro r hr
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Wr] at hr
          obtain ⟨z, hz, hw⟩ := hr
          exact Finset.mem_image.2 ⟨z, by simp [outSupp, hw], hz⟩
        · exact le_trans (Finset.card_le_univ _) (by simp)

theorem fp_Lemma_5b_sum : FP_Lemma_5b_sum := by
  classical
  intro K _ o₁ b o₂ R u v w hd
  refine ⟨fp_5b_rows o₁ b o₂ R u v w hd, ?_⟩
  -- transpose
  have hd' : IsMMDecomp (fun l (a : Fin o₂ × Fin b) => v l (a.2, a.1))
      (fun l (y : Fin b × Fin o₁) => u l (y.2, y.1))
      (fun l (z : Fin o₂ × Fin o₁) => w l (z.2, z.1)) := fp_transpose (ι := Fin R) hd
  have key := fp_5b_rows o₂ b o₁ R _ _ _ hd'
  have hcardS : ∀ l, (outSupp (fun z : Fin o₂ × Fin o₁ => w l (z.2, z.1))).card
      = (outSupp (w l)).card := by
    intro l
    refine Finset.card_bij (fun z _ => (z.2, z.1)) ?_ ?_ ?_
    · intro z hz; simpa [outSupp] using hz
    · intro z _ z' _ hzz; simp only [Prod.mk.injEq] at hzz; exact Prod.ext hzz.2 hzz.1
    · intro z hz; exact ⟨(z.2, z.1), by simpa [outSupp] using hz, rfl⟩
  have hcardE : (univ.filter fun e : Fin o₂ × Fin o₁ =>
        ∃ l, outSupp (fun z : Fin o₂ × Fin o₁ => w l (z.2, z.1)) = {e} ∧
        ∃ a : Fin o₂ × Fin b, a.1 ≠ e.1 ∧ v l (a.2, a.1) ≠ 0).card
      = (univ.filter fun e : Fin o₁ × Fin o₂ => ∃ l, outSupp (w l) = {e} ∧
        ∃ y : Fin b × Fin o₂, y.2 ≠ e.2 ∧ v l y ≠ 0).card := by
    refine Finset.card_bij (fun e _ => (e.2, e.1)) ?_ ?_ ?_
    · intro e he
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, fp_outSupp_eq_singleton] at he ⊢
      obtain ⟨l, ⟨h1, h2⟩, a, ha1, ha2⟩ := he
      refine ⟨l, ⟨h1, fun z hz => ?_⟩, (a.2, a.1), ha1, ha2⟩
      have := h2 (z.2, z.1) hz
      rw [← this]
    · intro e _ e' _ h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · intro e he
      refine ⟨(e.2, e.1), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, fp_outSupp_eq_singleton] at he ⊢
      obtain ⟨l, ⟨h1, h2⟩, y, hy1, hy2⟩ := he
      refine ⟨l, ⟨h1, fun z hz => ?_⟩, (y.2, y.1), hy1, hy2⟩
      have := h2 (z.2, z.1) hz
      rw [← this]
  rw [hcardE, Finset.sum_congr rfl fun l _ => by rw [hcardS l], mul_comm o₂ o₁] at key
  exact key

end FullProductNonlocal

end ThinMatrixProducts

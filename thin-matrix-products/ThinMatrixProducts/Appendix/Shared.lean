import Statements
import ThinMatrixProducts.Appendix.Normal

/-!
# Lemma A.8 and Theorem A.9: at most one shared variable

Lemma A.8 is the rank argument: the bilinear form `∑_{t∈Θ} X[ρ,t] Y[t,σ]` has rank `D = |Θ|`, its
column space is spanned by the `D` variables `X[ρ,t]` and lies in the span of the `D` forms
`a[v_ι]`, which are therefore independent and span it (`decomp_span`); likewise on the right.

Theorem A.9 follows the paper's proof, with the strings chosen as simply as possible: in (a) all
right strings read `y₁` except one letter `y₂` at a level `ℓ ∈ Q' ∖ Q`; in (b) the left string reads
`x₁` everywhere. The left half of (a) is the right half for the transposed run.
-/

namespace ThinMatrixProducts

open Module Submodule Finset

variable {K : Type} [Field K]

/-! ### Lemma A.8 -/

/-- The core of Lemma A.8: if `∑_ι a_ι b_ιᵀ = ∑_t e_t f_tᵀ` with independent `e_t` and dual `f_t`
(`f_t · f_{t'} = [t = t']`), and there are at most as many `ι` as `t`, then the `a_ι` are
independent and span the span of the `e_t`. -/
lemma decomp_span {IA IB ι κ : Type} [Fintype IA] [Fintype IB] [Fintype ι] [Fintype κ]
    [DecidableEq κ] (a : ι → IA → K) (b : ι → IB → K) (e : κ → IA → K) (f : κ → IB → K)
    (h : ∑ x, Matrix.vecMulVec (a x) (b x) = ∑ t, Matrix.vecMulVec (e t) (f t))
    (he : LinearIndependent K e) (hf : ∀ t t', dotProduct (f t) (f t') = if t = t' then 1 else 0)
    (hc : Fintype.card ι ≤ Fintype.card κ) :
    LinearIndependent K a ∧ span K (Set.range a) = span K (Set.range e) := by
  have hle : span K (Set.range e) ≤ span K (Set.range a) := by
    rw [span_le]
    rintro _ ⟨t, rfl⟩
    have h1 : Matrix.mulVec (∑ t, Matrix.vecMulVec (e t) (f t)) (f t) = e t := by
      rw [mulVec_sum_vecMulVec]
      simp_rw [hf]
      simp
    rw [← h1, ← h, mulVec_sum_vecMulVec]
    exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (subset_span ⟨x, rfl⟩)
  exact indep_of_le a _ hle (by rw [finrank_span_eq_card he]; exact hc)

/-- The vectors of a span of standard basis vectors `e_{g t}`, `t ∈ S`, vanish outside `g(S)`. -/
lemma eq_zero_of_mem_span_single {I α : Type} [DecidableEq I] (g : α → I) (S : Set α)
    {v : I → K} (hv : v ∈ span K ((fun t => (Pi.single (g t) 1 : I → K)) '' S)) (i : I)
    (hi : ∀ t ∈ S, g t ≠ i) : v i = 0 := by
  let P : Submodule K (I → K) :=
    { carrier := {v | ∀ i, (∀ t ∈ S, g t ≠ i) → v i = 0}
      add_mem' := fun {v w} hv hw i hi => by simp [hv i hi, hw i hi]
      zero_mem' := fun i _ => rfl
      smul_mem' := fun c v hv i hi => by simp [hv i hi] }
  have hle : span K ((fun t => (Pi.single (g t) 1 : I → K)) '' S) ≤ P := by
    rw [span_le]
    rintro _ ⟨t, ht, rfl⟩ i hi
    simp [Ne.symm (hi t ht)]
  exact hle hv i hi

/-- A nonzero vector in two spans of standard basis vectors meets both index sets. -/
lemma common_of_mem_span_single {I α : Type} [DecidableEq I] (g : α → I) (S S' : Set α)
    {v : I → K} (hv0 : v ≠ 0) (hv : v ∈ span K ((fun t => (Pi.single (g t) 1 : I → K)) '' S))
    (hv' : v ∈ span K ((fun t => (Pi.single (g t) 1 : I → K)) '' S')) :
    ∃ t ∈ S, ∃ t' ∈ S', g t = g t' := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hv0
  by_contra hno
  push Not at hno
  by_cases h : ∃ t ∈ S, g t = i
  · obtain ⟨t, ht, rfl⟩ := h
    exact hi (eq_zero_of_mem_span_single g S' hv' _ fun t' ht' he => hno t ht t' ht' he.symm)
  · push Not at h
    exact hi (eq_zero_of_mem_span_single g S hv i h)

lemma dot_single {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α] (g : α → I)
    (hg : Function.Injective g) (t t' : α) :
    dotProduct (Pi.single (g t) 1 : I → K) (Pi.single (g t') 1) = if t = t' then 1 else 0 := by
  rw [dotProduct_single, mul_one, Pi.single_apply]
  by_cases h : t = t'
  · subst h; simp
  · rw [if_neg (fun h' => h (hg h'.symm)), if_neg h]

lemma blockForm_eq {IX IY Rows Inner Cols : Type} [DecidableEq IX] [DecidableEq IY]
    (ex : Rows × Inner → IX) (ey : Inner × Cols → IY) (ρ : Rows) (σ : Cols) (Θ : Finset Inner) :
    (blockForm ex ey ρ σ Θ : Matrix IX IY K) = ∑ t : Θ,
      Matrix.vecMulVec (Pi.single (ex (ρ, t)) 1) (Pi.single (ey (t, σ)) 1) :=
  (Finset.sum_coe_sort Θ _).symm

theorem lemma_A_8 : Lemma_A_8 := by
  intro K _ IX IY Rows Inner Cols ι _ _ _ _ _ _ ex ey hex hey a b ρ σ Θ hΘ hsum
  classical
  let eX : Θ → IX → K := fun t => Pi.single (ex (ρ, t)) 1
  let eY : Θ → IY → K := fun t => Pi.single (ey (t, σ)) 1
  have hinjX : Function.Injective fun t : Θ => ex (ρ, t) :=
    fun t t' h => Subtype.ext (congrArg Prod.snd (hex h))
  have hinjY : Function.Injective fun t : Θ => ey (t, σ) :=
    fun t t' h => Subtype.ext (congrArg Prod.fst (hey h))
  have hX : LinearIndependent K eX := by
    have := (Pi.basisFun K IX).linearIndependent.comp _ hinjX
    convert this using 1
    funext t
    simp [eX, Pi.basisFun_apply]
  have hY : LinearIndependent K eY := by
    have := (Pi.basisFun K IY).linearIndependent.comp _ hinjY
    convert this using 1
    funext t
    simp [eY, Pi.basisFun_apply]
  have hcard : Fintype.card ι ≤ Fintype.card Θ := by rw [Fintype.card_coe, hΘ]
  have hM : ∑ κ, Matrix.vecMulVec (a κ) (b κ) = ∑ t, Matrix.vecMulVec (eX t) (eY t) := by
    rw [hsum, blockForm_eq]
  have hMt : ∑ κ, Matrix.vecMulVec (b κ) (a κ) = ∑ t, Matrix.vecMulVec (eY t) (eX t) := by
    have := congrArg Matrix.transpose hM
    rwa [transpose_sum_vecMulVec, transpose_sum_vecMulVec] at this
  obtain ⟨ha, hspa⟩ := decomp_span a b eX eY hM hX
    (fun t t' => dot_single (fun t : Θ => ey (t, σ)) hinjY t t') hcard
  obtain ⟨hb, hspb⟩ := decomp_span b a eY eX hMt hY
    (fun t t' => dot_single (fun t : Θ => ex (ρ, t)) hinjX t t') hcard
  have himX : Set.range eX = (fun t => (Pi.single (ex (ρ, t)) 1 : IX → K)) '' ↑Θ := by
    ext v; simp [eX]
  have himY : Set.range eY = (fun t => (Pi.single (ey (t, σ)) 1 : IY → K)) '' ↑Θ := by
    ext v; simp [eY]
  refine ⟨by rw [hspa, himX], by rw [hspb, himY], fun κ => ha.ne_zero κ, fun κ => hb.ne_zero κ,
    ha, fun β β' hββ => ?_, hb⟩
  funext κ j
  have hcol : ∀ γ : ι → IY → K, (fun i => (∑ κ, Matrix.vecMulVec (a κ) (γ κ)) i j) =
      ∑ κ, γ κ j • a κ := by
    intro γ
    funext i
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply, Finset.sum_apply, mul_comm]
  have h1 := congrArg (fun M : Matrix IX IY K => fun i => M i j) hββ
  simp only [hcol] at h1
  have h2 : ∑ κ, (β κ j - β' κ j) • a κ = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, h1, sub_self]
  have := Fintype.linearIndependent_iff.1 ha _ h2 κ
  exact sub_eq_zero.1 this

/-! ### Theorem A.9 -/

namespace SharedRun

variable {IX IY : Type} {L : ℕ}

/-- The run with left and right exchanged. -/
def transposeRun (run : SharedRun K IX IY L) : SharedRun K IY IX L where
  AL := run.AR
  AR := run.AL
  OL := run.OR
  OR := run.OL
  Pr := run.Pr
  xo := run.yo
  yo := run.xo
  lp := run.rp
  rp := run.lp
  lp_inj := run.rp_inj
  rp_inj := run.lp_inj
  a := run.b
  b := run.a

lemma output_transposeRun (run : SharedRun K IX IY L) (Q : Finset (Fin L)) (I : Fin L → run.OL)
    (J : Fin L → run.OR) :
    run.transposeRun.output Q J I = Matrix.transpose (run.output Q I J) := by
  unfold SharedRun.output
  rw [transpose_sum_vecMulVec]
  rfl

end SharedRun

lemma blockForm_transpose {IX IY Rows Inner Cols : Type} [DecidableEq IX] [DecidableEq IY]
    (ex : Rows × Inner → IX) (ey : Inner × Cols → IY) (ρ : Rows) (σ : Cols) (Θ : Finset Inner) :
    (blockForm (fun p : Cols × Inner => ey (p.2, p.1)) (fun p : Inner × Rows => ex (p.2, p.1))
      σ ρ Θ : Matrix IY IX K) = Matrix.transpose (blockForm ex ey ρ σ Θ) := by
  ext i j
  simp [blockForm, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm]

lemma correctSingle_transposeRun {IX IY Rows Inner Cols : Type} [DecidableEq IX] [DecidableEq IY]
    {L : ℕ} (run : SharedRun K IX IY L) (ex : Rows × Inner → IX) (ey : Inner × Cols → IY)
    (Q : Finset (Fin L)) (I : Fin L → run.OL) (J : Fin L → run.OR) (ρ : Rows) (σ : Cols)
    (Θ : Finset Inner) :
    run.transposeRun.CorrectSingle (fun p : Cols × Inner => ey (p.2, p.1))
        (fun p : Inner × Rows => ex (p.2, p.1)) Q J I σ ρ Θ ↔
      run.CorrectSingle ex ey Q I J ρ σ Θ := by
  unfold SharedRun.CorrectSingle
  rw [SharedRun.output_transposeRun, blockForm_transpose]
  exact and_congr Iff.rfl ⟨fun h => Matrix.transpose_injective h, fun h => by rw [h]⟩

/-- Two different inner sets of the same size: a level of the second outside the first. -/
lemma exists_two {L m : ℕ} (𝒬 : Finset (Finset (Fin L))) (hcard : ∀ Q ∈ 𝒬, Q.card = m)
    (htwo : 1 < 𝒬.card) : ∃ Q ∈ 𝒬, ∃ Q' ∈ 𝒬, Q ≠ Q' ∧ ∃ ℓ ∈ Q', ℓ ∉ Q := by
  obtain ⟨Q, hQ, Q', hQ', hne⟩ := Finset.one_lt_card.1 htwo
  refine ⟨Q, hQ, Q', hQ', hne, ?_⟩
  by_contra h
  push Not at h
  exact hne (Finset.eq_of_subset_of_card_le h (by rw [hcard Q hQ, hcard Q' hQ'])).symm

/-- The two spans of Lemma A.8 (A) for the same family give the same entry row and block. -/
lemma row_block_eq {IX Rows Inner : Type} [DecidableEq IX] (ex : Rows × Inner → IX)
    (hex : Function.Injective ex) (ρ₁ ρ₂ : Rows) (Θ₁ Θ₂ : Finset Inner) (hne : Θ₁.Nonempty)
    (h : span K ((fun t => (Pi.single (ex (ρ₁, t)) 1 : IX → K)) '' ↑Θ₁) =
      span K ((fun t => (Pi.single (ex (ρ₂, t)) 1 : IX → K)) '' ↑Θ₂)) :
    ρ₁ = ρ₂ ∧ Θ₁ = Θ₂ := by
  classical
  have key : ∀ (ρ ρ' : Rows) (Θ Θ' : Finset Inner),
      span K ((fun t => (Pi.single (ex (ρ, t)) 1 : IX → K)) '' ↑Θ) =
        span K ((fun t => (Pi.single (ex (ρ', t)) 1 : IX → K)) '' ↑Θ') →
      ∀ t ∈ Θ, ρ = ρ' ∧ t ∈ Θ' := by
    intro ρ ρ' Θ Θ' h t ht
    have hmem : (Pi.single (ex (ρ, t)) 1 : IX → K) ∈
        span K ((fun t => (Pi.single (ex (ρ', t)) 1 : IX → K)) '' ↑Θ') := by
      rw [← h]
      exact subset_span ⟨t, ht, rfl⟩
    by_contra hno
    have hz := eq_zero_of_mem_span_single (fun t => ex (ρ', t)) ↑Θ' hmem (ex (ρ, t))
      (fun t' ht' he => hno (by
        have := hex he
        simp only [Prod.mk.injEq] at this
        exact ⟨this.1.symm, this.2 ▸ ht'⟩))
    simp at hz
  obtain ⟨t, ht⟩ := hne
  refine ⟨(key _ _ _ _ h t ht).1, Finset.Subset.antisymm (fun t ht => (key _ _ _ _ h t ht).2)
    (fun t ht => (key _ _ _ _ h.symm t ht).2)⟩

/-- Theorem A.9 (a), the right side. -/
lemma shared_right {IX IY Rows Inner Cols : Type} [Fintype IX] [Fintype IY] [DecidableEq IX]
    [DecidableEq IY] [DecidableEq Inner] {L m : ℕ} (run : SharedRun K IX IY L)
    (ex : Rows × Inner → IX) (ey : Inner × Cols → IY) (hex : Function.Injective ex)
    (hey : Function.Injective ey) (hOL : Nonempty run.OL) (𝒬 : Finset (Finset (Fin L)))
    (hcard : ∀ Q ∈ 𝒬, Q.card = m) (htwo : 1 < 𝒬.card)
    (hcs : ∀ Q ∈ 𝒬, ∀ I J, ∃ ρ σ Θ, run.CorrectSingle ex ey Q I J ρ σ Θ) :
    ∀ r₁ r₂ : run.Pr, r₁ ≠ r₂ → ¬ ((∃ j, run.rp r₁ = run.yo j) ∧ (∃ j, run.rp r₂ = run.yo j)) := by
  classical
  rintro r₁ r₂ hne ⟨⟨j₁, hj₁⟩, ⟨j₂, hj₂⟩⟩
  obtain ⟨Q, hQ, Q', hQ', -, ℓ, hℓQ', hℓQ⟩ := exists_two 𝒬 hcard htwo
  let I₀ : Fin L → run.OL := fun _ => Classical.choice hOL
  let J₀ : Fin L → run.OR := fun _ => j₁
  let J₂ : Fin L → run.OR := Function.update J₀ ℓ j₂
  let ι₁ : ↥Q' → run.Pr := fun _ => r₁
  let ι₂ : ↥Q' → run.Pr := fun x => if (x : Fin L) = ℓ then r₂ else r₁
  let κ : ↥Q → run.Pr := fun _ => r₁
  have hw₁ : run.rightStr Q' J₀ ι₁ = run.rightStr Q J₀ κ := by
    funext ℓ'
    simp only [SharedRun.rightStr]
    split_ifs <;> simp [ι₁, κ, J₀, hj₁]
  have hw₂ : run.rightStr Q' J₀ ι₂ = run.rightStr Q J₂ κ := by
    funext ℓ'
    simp only [SharedRun.rightStr]
    by_cases h : ℓ' = ℓ
    · subst h
      rw [dif_pos hℓQ', dif_neg hℓQ]
      simp [ι₂, J₂, hj₂]
    · split_ifs <;> simp [ι₂, κ, J₂, J₀, h, hj₁]
  obtain ⟨ρ', σ', Θ', hc'⟩ := hcs Q' hQ' I₀ J₀
  obtain ⟨ρ₁, σ₁, Θ₁, hc₁⟩ := hcs Q hQ I₀ J₀
  obtain ⟨ρ₂, σ₂, Θ₂, hc₂⟩ := hcs Q hQ I₀ J₂
  obtain ⟨-, hB', -, hB'0, -, -, hB'ind⟩ := lemma_A_8 ex ey hex hey _ _ ρ' σ' Θ' hc'.1 hc'.2
  obtain ⟨hA₁, hB₁, -, -, -, hcancel, -⟩ := lemma_A_8 ex ey hex hey _ _ ρ₁ σ₁ Θ₁ hc₁.1 hc₁.2
  obtain ⟨hA₂, hB₂, -, -, -, -, -⟩ := lemma_A_8 ex ey hex hey _ _ ρ₂ σ₂ Θ₂ hc₂.1 hc₂.2
  -- the columns: `σ₁ = σ' = σ₂`
  have hcol : ∀ (Jx : Fin L → run.OR) (σx : Cols) (Θx : Finset Inner),
      span K (Set.range fun ι => run.b (run.rightStr Q Jx ι)) =
        span K ((fun t => (Pi.single (ey (t, σx)) 1 : IY → K)) '' ↑Θx) →
      ∀ ι', run.rightStr Q' J₀ ι' = run.rightStr Q Jx κ → σx = σ' := by
    intro Jx σx Θx hB ι' hw
    have hv0 := hB'0 ι'
    have hmem' : run.b (run.rightStr Q' J₀ ι') ∈
        span K ((fun t => (Pi.single (ey (t, σ')) 1 : IY → K)) '' ↑Θ') := by
      rw [← hB']
      exact subset_span ⟨ι', rfl⟩
    have hmem : run.b (run.rightStr Q' J₀ ι') ∈
        span K ((fun t => (Pi.single (ey (t, σx)) 1 : IY → K)) '' ↑Θx) := by
      rw [← hB, hw]
      exact subset_span ⟨κ, rfl⟩
    -- both spans are spans of standard basis vectors `e_{ey p}`
    have hmem1 : run.b (run.rightStr Q' J₀ ι') ∈
        span K ((fun p => (Pi.single (ey p) 1 : IY → K)) '' ((fun t => (t, σx)) '' ↑Θx)) := by
      rw [Set.image_image]; exact hmem
    have hmem2 : run.b (run.rightStr Q' J₀ ι') ∈
        span K ((fun p => (Pi.single (ey p) 1 : IY → K)) '' ((fun t => (t, σ')) '' ↑Θ')) := by
      rw [Set.image_image]; exact hmem'
    obtain ⟨_, ⟨t, -, rfl⟩, _, ⟨t', -, rfl⟩, he⟩ :=
      common_of_mem_span_single ey _ _ hv0 hmem1 hmem2
    exact congrArg Prod.snd (hey he)
  have hσ₁ := hcol J₀ σ₁ Θ₁ hB₁ ι₁ hw₁
  have hσ₂ := hcol J₂ σ₂ Θ₂ hB₂ ι₂ hw₂
  -- the rows and blocks: the left strings of `o₁` and `o₂` coincide
  have hne₁ : Θ₁.Nonempty := by
    rw [← Finset.card_pos, hc₁.1]
    exact Fintype.card_pos_iff.2 ⟨κ⟩
  obtain ⟨hρ, hΘ⟩ := row_block_eq ex hex ρ₁ ρ₂ Θ₁ Θ₂ hne₁ (hA₁.symm.trans hA₂)
  have heq : run.output Q I₀ J₀ = run.output Q I₀ J₂ := by
    rw [hc₁.2, hc₂.2, hρ, hΘ, hσ₁, hσ₂]
  have hb := hcancel _ _ heq
  have h12 : run.b (run.rightStr Q' J₀ ι₁) = run.b (run.rightStr Q' J₀ ι₂) := by
    rw [hw₁, hw₂]
    exact congrFun hb κ
  have := congrFun (hB'ind.injective h12) ⟨ℓ, hℓQ'⟩
  simp only [ι₁, ι₂, if_pos rfl] at this
  exact hne this

/-- Theorem A.9 (b). -/
lemma shared_both {IX IY Rows Inner Cols : Type} [Fintype IX] [Fintype IY] [DecidableEq IX]
    [DecidableEq IY] [DecidableEq Inner] {L m : ℕ} (run : SharedRun K IX IY L)
    (ex : Rows × Inner → IX) (ey : Inner × Cols → IY) (hex : Function.Injective ex)
    (hey : Function.Injective ey) (𝒬 : Finset (Finset (Fin L)))
    (hcard : ∀ Q ∈ 𝒬, Q.card = m) (htwo : 1 < 𝒬.card)
    (hcs : ∀ Q ∈ 𝒬, ∀ I J, ∃ ρ σ Θ, run.CorrectSingle ex ey Q I J ρ σ Θ)
    (hdisj : ∀ Q ∈ 𝒬, ∀ Q' ∈ 𝒬, ∀ I J I' J' ρ σ Θ Θ', run.CorrectSingle ex ey Q I J ρ σ Θ →
        run.CorrectSingle ex ey Q' I' J' ρ σ Θ' → (Θ ∩ Θ').Nonempty → Q = Q') :
    ∀ r₁ r₂ : run.Pr, ¬ ((∃ i, run.lp r₁ = run.xo i) ∧ (∃ j, run.rp r₂ = run.yo j)) := by
  classical
  rintro r₁ r₂ ⟨⟨i₁, hi₁⟩, ⟨j₁, hj₁⟩⟩
  obtain ⟨Q, hQ, Q', hQ', hQQ', -⟩ := exists_two 𝒬 hcard htwo
  let I' : Fin L → run.OL := fun _ => i₁
  let J' : Fin L → run.OR := fun _ => j₁
  let ιA : ↥Q' → run.Pr := fun _ => r₁
  let ιB : ↥Q' → run.Pr := fun x => if (x : Fin L) ∈ Q then r₁ else r₂
  let κv : ↥Q → run.Pr := fun _ => r₁
  let κw : ↥Q → run.Pr := fun x => if (x : Fin L) ∈ Q' then r₁ else r₂
  have hv : run.leftStr Q' I' ιA = run.leftStr Q I' κv := by
    funext ℓ'
    simp only [SharedRun.leftStr]
    split_ifs <;> simp [ιA, κv, I', hi₁]
  have hw : run.rightStr Q' J' ιB = run.rightStr Q J' κw := by
    funext ℓ'
    simp only [SharedRun.rightStr]
    by_cases h1 : ℓ' ∈ Q <;> by_cases h2 : ℓ' ∈ Q' <;> simp [h1, h2, ιB, κw, J', hj₁]
  obtain ⟨ρ', σ', Θ', hc'⟩ := hcs Q' hQ' I' J'
  obtain ⟨ρQ, σQ, ΘQ, hcQ⟩ := hcs Q hQ I' J'
  obtain ⟨hA', hB', hA'0, hB'0, -, -, -⟩ := lemma_A_8 ex ey hex hey _ _ ρ' σ' Θ' hc'.1 hc'.2
  obtain ⟨hAQ, hBQ, -, -, -, -, -⟩ := lemma_A_8 ex ey hex hey _ _ ρQ σQ ΘQ hcQ.1 hcQ.2
  -- the left string `v`: the same row, overlapping blocks
  have hmv' : run.a (run.leftStr Q' I' ιA) ∈
      span K ((fun p => (Pi.single (ex p) 1 : IX → K)) '' ((fun t => (ρ', t)) '' ↑Θ')) := by
    rw [Set.image_image, ← hA']
    exact subset_span ⟨ιA, rfl⟩
  have hmvQ : run.a (run.leftStr Q' I' ιA) ∈
      span K ((fun p => (Pi.single (ex p) 1 : IX → K)) '' ((fun t => (ρQ, t)) '' ↑ΘQ)) := by
    rw [Set.image_image, ← hAQ, hv]
    exact subset_span ⟨κv, rfl⟩
  obtain ⟨_, ⟨t, ht, rfl⟩, _, ⟨t', ht', rfl⟩, he⟩ :=
    common_of_mem_span_single ex _ _ (hA'0 ιA) hmv' hmvQ
  have he' := hex he
  simp only [Prod.mk.injEq] at he'
  obtain ⟨hρ, htt⟩ := he'
  -- the right string `w`: the same column
  have hmw' : run.b (run.rightStr Q' J' ιB) ∈
      span K ((fun p => (Pi.single (ey p) 1 : IY → K)) '' ((fun t => (t, σ')) '' ↑Θ')) := by
    rw [Set.image_image, ← hB']
    exact subset_span ⟨ιB, rfl⟩
  have hmwQ : run.b (run.rightStr Q' J' ιB) ∈
      span K ((fun p => (Pi.single (ey p) 1 : IY → K)) '' ((fun t => (t, σQ)) '' ↑ΘQ)) := by
    rw [Set.image_image, ← hBQ, hw]
    exact subset_span ⟨κw, rfl⟩
  obtain ⟨_, ⟨s, -, rfl⟩, _, ⟨s', -, rfl⟩, hse⟩ :=
    common_of_mem_span_single ey _ _ (hB'0 ιB) hmw' hmwQ
  have hσ : σ' = σQ := congrArg Prod.snd (hey hse)
  rw [hρ, hσ] at hc'
  exact hQQ' (hdisj Q hQ Q' hQ' I' J' I' J' ρQ σQ ΘQ Θ' hcQ hc'
    ⟨t, Finset.mem_inter.2 ⟨htt ▸ ht', ht⟩⟩)

theorem theorem_A_9 : Theorem_A_9 := by
  intro K _ IX IY Rows Inner Cols _ _ _ _ _ L m run ex ey hex hey hOL hOR 𝒬 hcard htwo hcs
  refine ⟨shared_right run ex ey hex hey hOL 𝒬 hcard htwo hcs, ?_,
    shared_both run ex ey hex hey 𝒬 hcard htwo hcs⟩
  have hex' : Function.Injective fun p : Cols × Inner => ey (p.2, p.1) := fun p p' h => by
    have := hey h
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.2 this.1
  have hey' : Function.Injective fun p : Inner × Rows => ex (p.2, p.1) := fun p p' h => by
    have := hex h
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.2 this.1
  exact shared_right run.transposeRun _ _ hex' hey' hOR 𝒬 hcard htwo
    (fun Q hQ J I => by
      obtain ⟨ρ, σ, Θ, h⟩ := hcs Q hQ I J
      exact ⟨σ, ρ, Θ, (correctSingle_transposeRun run ex ey Q I J ρ σ Θ).2 h⟩)

end ThinMatrixProducts

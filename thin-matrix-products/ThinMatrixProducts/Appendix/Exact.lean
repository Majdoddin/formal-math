import Statements
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.FieldTheory.Finiteness

/-!
# Proposition A.2: exact identities with a harmless error

The proof is the paper's. The signs of the normal `(α, β)` of the half-plane decide which error
monomials vanish (`α ≤ 0`: none with `p` and `y` on an outer output; `β ≤ 0`: none with `x` and
`q` there; `α, β > 0`: no error on `z₀`), and in every case the monomials of direction `(0,0)` are
those of `G`. The paper's three cases become two lemmas:

* `caseII` ("no monomial with `p` and `y`", which also covers "errors only on `z₀`", see below):
  the substitution argument. The vectors `(φ_λ(p_s))_λ` are independent (`T'_{p_s}` has `z₀`-part
  `q_s z₀`), so `q₀` terms `S` can be chosen on which they form an invertible matrix
  (`selection`); combining `x_a` with the `p_s` to vanish on `S` leaves `kn` independent output
  slices `x_a y_j` decomposed by the `R - q₀` other terms.
* `caseI` ("errors only on outer outputs"): the rank argument with `Λ₀`, `r_x`, `r_y`
  (`rank_bound`), and the quotient argument (`quot_bound`), used twice.

The case "errors only on `z₀`" needs no change of variables here: the substitution argument only
reads the outer outputs, on which `T' = G` in that case. The paper's change of variables reduces it
to `G` itself, which is the same argument applied to `G`; both give `R ≥ kn + q₀`.
-/

namespace ThinMatrixProducts

open Module Submodule Finset

variable {K : Type} [Field K]

/-! ### Tools -/

/-- An independent family in the span of `N` vectors has at most `N` members (the flattening
bound). -/
lemma card_le_of_mem_span {M ι κ : Type} [AddCommGroup M] [Module K M] [Fintype ι] [Fintype κ]
    {f : ι → M} (hf : LinearIndependent K f) (w : κ → M)
    (h : ∀ i, f i ∈ span K (Set.range w)) : Fintype.card ι ≤ Fintype.card κ := by
  have h1 : span K (Set.range f) ≤ span K (Set.range w) :=
    span_le.2 (by rintro _ ⟨i, rfl⟩; exact h i)
  have : FiniteDimensional K (span K (Set.range w)) :=
    FiniteDimensional.span_of_finite K (Set.finite_range w)
  calc Fintype.card ι = finrank K (span K (Set.range f)) := (finrank_span_eq_card hf).symm
    _ ≤ finrank K (span K (Set.range w)) := Submodule.finrank_mono h1
    _ ≤ Fintype.card κ := finrank_range_le_card w

/-- "The `q₀ × R` matrix `(φ_λ(p_s))` has rank `q₀`; choose terms `λ_1, …, λ_{q₀}` at which its
columns form an invertible matrix": for `q` independent vectors `P_s ∈ K^R` there are `q`
coordinates `S` on which every vector is a combination of the `P_s`. -/
lemma selection {q R : ℕ} (P : Fin q → Fin R → K) (hP : LinearIndependent K P) :
    ∃ S : Finset (Fin R), S.card = q ∧
      ∀ y : Fin R → K, ∃ c : Fin q → K, ∀ t ∈ S, y t = ∑ s, c s * P s t := by
  classical
  let ρ : (Fin q → K) →ₗ[K] (Fin R → K) := Fintype.linearCombination K P
  have hρ : Function.Injective ρ := hP.fintypeLinearCombination_injective
  have hρapp : ∀ c t, ρ c t = ∑ s, c s * P s t := by
    intro c t
    simp [ρ, Fintype.linearCombination_apply, Finset.sum_apply]
  let f : Fin R → Module.Dual K (Fin q → K) := fun t => (LinearMap.proj t) ∘ₗ ρ
  have hf : ∀ t c, f t c = ρ c t := fun t c => rfl
  have hspan : span K (Set.range f) = ⊤ := by
    have hco : (span K (Set.range f)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      rw [mem_dualCoannihilator] at hc
      have h0 : ρ c = 0 := by
        funext t
        exact hc (f t) (subset_span ⟨t, rfl⟩)
      rw [mem_bot]
      exact hρ (h0.trans (map_zero ρ).symm)
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := span K (Set.range f))
    rw [hco, Submodule.dualAnnihilator_bot] at this
    exact this.symm
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent K (Set.range f)
  rw [hspan] at hbspan
  let gb : Basis b K (Module.Dual K (Fin q → K)) :=
    Basis.mk hbind (by rw [Subtype.range_coe, hbspan])
  let _ : Fintype b := FiniteDimensional.fintypeBasisIndex gb
  have hcardb : Fintype.card b = q := by
    rw [← Module.finrank_eq_card_basis gb, Subspace.dual_finrank_eq, Module.finrank_fin_fun]
  choose g hg using fun x : b => hbsub x.2
  have ginj : Function.Injective g := fun x y h => Subtype.ext (by rw [← hg x, ← hg y, h])
  let S : Finset (Fin R) := univ.image g
  have hS : S.card = q := by rw [card_image_of_injective _ ginj, card_univ, hcardb]
  let res : (Fin q → K) →ₗ[K] (S → K) := LinearMap.pi fun t : S => f t
  have hinj : Function.Injective res := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro c hc
    rw [LinearMap.mem_ker] at hc
    have h1 : ∀ x ∈ b, x c = 0 := by
      intro x hx
      have := congrFun hc ⟨g ⟨x, hx⟩, mem_image_of_mem _ (mem_univ _)⟩
      simp only [res, LinearMap.pi_apply, Pi.zero_apply] at this
      rw [hg] at this
      exact this
    have h2 : ∀ φ : Module.Dual K (Fin q → K), φ c = 0 := by
      intro φ
      have hφ : φ ∈ span K b := by rw [hbspan]; trivial
      have hle : span K b ≤ LinearMap.ker (Module.Dual.eval K (Fin q → K) c) :=
        span_le.2 fun x hx => by simp [h1 x hx]
      have := hle hφ
      simpa using this
    rw [mem_bot]
    exact (Module.forall_dual_apply_eq_zero_iff K c).1 h2
  have hsurj : Function.Surjective res := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinj
    rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, Fintype.card_coe, hS]
  refine ⟨S, hS, fun y => ?_⟩
  obtain ⟨c, hc⟩ := hsurj (fun t => y t)
  refine ⟨c, fun t ht => ?_⟩
  have := congrFun hc ⟨t, ht⟩
  simp only [res, LinearMap.pi_apply] at this
  rw [← this, hf, hρapp]

/-! ### The substitution argument -/

/-- The case "no monomial with `p` and `y`" (and "errors only on `z₀`"): `R ≥ kn + q₀`. The
hypotheses are the coefficients of `T'` that the argument reads: `p_s q_t z₀`, `x_a y_j z_o`
(direction `(0,0)`, so those of `G`) and `p_s y_j z_o` on the outer outputs (zero). -/
lemma caseII {k n q R : ℕ} (φ : Fin R → Fin k ⊕ Fin q → K) (ψ : Fin R → Fin n ⊕ Fin q → K)
    (χ : Fin R → Option (Fin k × Fin n) → K)
    (h1 : ∀ s t, decompTensor φ ψ χ (.inr s) (.inr t) none = if s = t then 1 else 0)
    (h2 : ∀ a j o, decompTensor φ ψ χ (.inl a) (.inl j) (some o) = if o = (a, j) then 1 else 0)
    (h3 : ∀ s j o, decompTensor φ ψ χ (.inr s) (.inl j) (some o) = 0) :
    k * n + q ≤ R := by
  classical
  -- the vectors `(φ_λ(p_s))_λ` are independent
  let P : Fin q → Fin R → K := fun s t => φ t (.inr s)
  have hP : LinearIndependent K P := by
    rw [Fintype.linearIndependent_iff]
    intro β hβ s
    have h0 : ∀ t, ∑ s', β s' * φ t (.inr s') = 0 := by
      intro t
      have := congrFun hβ t
      simpa [P, Finset.sum_apply] using this
    have key : ∑ t, (∑ s', β s' * φ t (.inr s')) * ψ t (.inr s) * χ t none = β s := by
      calc ∑ t, (∑ s', β s' * φ t (.inr s')) * ψ t (.inr s) * χ t none
          = ∑ s', β s' * decompTensor φ ψ χ (.inr s') (.inr s) none := by
            simp only [decompTensor, Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = β s := by simp [h1]
    rw [← key]
    simp [h0]
  obtain ⟨S, hS, hsol⟩ := selection P hP
  choose c hc using fun a : Fin k => hsol (fun t => - φ t (.inl a))
  -- `x_a + ∑_s c_{as} p_s` vanishes at the terms of `S`
  let φ' : Fin R → Fin k → K := fun t a => φ t (.inl a) + ∑ s, c a s * φ t (.inr s)
  have hφ'0 : ∀ t ∈ S, φ' t = 0 := by
    intro t ht
    funext a
    have := hc a t ht
    simp only [φ', Pi.zero_apply, P] at this ⊢
    rw [← this]
    ring
  let w : Fin R → Matrix (Fin k) (Fin n) K :=
    fun t => Matrix.vecMulVec (φ' t) (fun j => ψ t (.inl j))
  -- the output slices are the `kn` matrices `x_a y_j`
  have hM : ∀ o : Fin k × Fin n, ∑ t, χ t (some o) • w t = Matrix.single o.1 o.2 1 := by
    intro o
    ext a j
    have hterm : ∀ t, χ t (some o) * (φ' t a * ψ t (.inl j)) =
        φ t (.inl a) * ψ t (.inl j) * χ t (some o) +
          ∑ s, c a s * (φ t (.inr s) * ψ t (.inl j) * χ t (some o)) := by
      intro t
      simp only [φ', add_mul, mul_add, Finset.sum_mul, Finset.mul_sum]
      congr 1
      · ring
      · exact Finset.sum_congr rfl fun s _ => by ring
    have e : ∑ t, χ t (some o) * (φ' t a * ψ t (.inl j))
        = decompTensor φ ψ χ (.inl a) (.inl j) (some o) +
          ∑ s, c a s * decompTensor φ ψ χ (.inr s) (.inl j) (some o) := by
      rw [Finset.sum_congr rfl fun t _ => hterm t, Finset.sum_add_distrib, Finset.sum_comm]
      simp only [decompTensor, Finset.mul_sum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, w, Matrix.vecMulVec_apply, smul_eq_mul]
    rw [e, h2]
    simp only [h3, mul_zero, Finset.sum_const_zero, add_zero, Matrix.single_apply]
    by_cases h : o.1 = a ∧ o.2 = j
    · rw [if_pos h, if_pos (Prod.ext h.1 h.2)]
    · rw [if_neg h, if_neg]
      rintro rfl
      exact h ⟨rfl, rfl⟩
  have hmem : ∀ o : Fin k × Fin n, Matrix.single o.1 o.2 (1 : K) ∈
      span K (Set.range (fun t : ↥(Sᶜ) => w t)) := by
    intro o
    rw [← hM o, ← Finset.sum_compl_add_sum S]
    have hS0 : ∑ t ∈ S, χ t (some o) • w t = 0 :=
      Finset.sum_eq_zero fun t ht => by simp [w, hφ'0 t ht]
    rw [hS0, add_zero]
    exact Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (subset_span ⟨⟨t, ht⟩, rfl⟩)
  have hind : LinearIndependent K (fun o : Fin k × Fin n => Matrix.single o.1 o.2 (1 : K)) := by
    have := (Matrix.stdBasis K (Fin k) (Fin n)).linearIndependent
    convert this using 1
    funext o
    rw [Matrix.stdBasis_eq_single]
  have hcard := card_le_of_mem_span hind _ hmem
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe, card_compl,
    Fintype.card_fin, hS] at hcard
  have hqR : q ≤ R := by
    rw [← hS]
    exact (card_le_univ S).trans (by simp)
  omega

/-! ### The case "errors only on outer outputs" -/

/-- "Map the span of the `x_i` onto its quotient by `span{X_λ : λ ∈ Λ₀}`. The terms of `Λ₀`
vanish, and the other `R - |Λ₀|` terms decompose the image of `⟨k,1,n⟩`, whose output slices
`x̄_i y_j` span a space of dimension `(k - r_x) n`; so `R - |Λ₀| ≥ (k - r_x) n`." -/
lemma quot_bound {k n R : ℕ} (X : Fin R → Fin k → K) (Y : Fin R → Fin n → K)
    (χo : Fin R → Fin k × Fin n → K) (Λ0 : Finset (Fin R))
    (hid : ∀ a j o, ∑ t, X t a * Y t j * χo t o = if o = (a, j) then 1 else 0) :
    (k - finrank K (span K (X '' ↑Λ0))) * n ≤ R - Λ0.card := by
  classical
  set W := span K (X '' ↑Λ0) with hW
  let π := W.mkQ
  have hdk : finrank K ((Fin k → K) ⧸ W) = k - finrank K W := by
    have := Submodule.finrank_quotient_add_finrank W
    rw [Module.finrank_fin_fun] at this
    omega
  set d := finrank K ((Fin k → K) ⧸ W) with hd
  let bQ : Basis (Fin d) K ((Fin k → K) ⧸ W) := Module.finBasisOfFinrankEq K _ rfl
  let B := Pi.basis (fun _ : Fin n => bQ)
  let w : ↥(Λ0ᶜ) → (Fin n → (Fin k → K) ⧸ W) := fun t j => Y t j • π (X t)
  have hX0 : ∀ t ∈ Λ0, π (X t) = 0 := fun t ht =>
    (Submodule.Quotient.mk_eq_zero W).2 (subset_span ⟨t, ht, rfl⟩)
  -- the image of the output slice `z_aj`
  have hvec : ∀ (a : Fin k) (j j' : Fin n),
      (∑ t, (χo t (a, j) * Y t j') • X t) = if j' = j then Pi.single a 1 else 0 := by
    intro a j j'
    funext a''
    have := hid a'' j' (a, j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [show (∑ t, χo t (a, j) * Y t j' * X t a'') = ∑ t, X t a'' * Y t j' * χo t (a, j) from
      Finset.sum_congr rfl fun t _ => by ring, this]
    by_cases hj : j' = j
    · subst hj
      by_cases ha : a'' = a
      · subst ha; simp
      · simp [Prod.ext_iff, ha, Ne.symm ha]
    · simp [Prod.ext_iff, hj, Ne.symm hj]
  have hsingle : ∀ (a : Fin k) (j : Fin n),
      Pi.single j (π (Pi.single a 1)) ∈ span K (Set.range w) := by
    intro a j
    have e : (Pi.single j (π (Pi.single a 1)) : Fin n → (Fin k → K) ⧸ W) =
        ∑ t, χo t (a, j) • (fun j' => Y t j' • π (X t)) := by
      funext j'
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_smul]
      rw [show ∑ t, (χo t (a, j) * Y t j') • π (X t) = π (∑ t, (χo t (a, j) * Y t j') • X t) by
        simp [map_sum, map_smul], hvec]
      by_cases hj : j' = j
      · subst hj; simp
      · simp [hj]
    rw [e, ← Finset.sum_compl_add_sum Λ0]
    have hS0 : ∑ t ∈ Λ0, χo t (a, j) • (fun j' => Y t j' • π (X t)) = 0 :=
      Finset.sum_eq_zero fun t ht => by
        funext j'
        simp [hX0 t ht]
    rw [hS0, add_zero]
    exact Submodule.sum_mem _ fun t ht => Submodule.smul_mem _ _ (subset_span ⟨⟨t, ht⟩, rfl⟩)
  have hB : ∀ ji, B ji ∈ span K (Set.range w) := by
    rintro ⟨j, i⟩
    rw [Pi.basis_apply]
    obtain ⟨x, hx⟩ := W.mkQ_surjective (bQ i)
    have hxs : x = ∑ a, x a • (Pi.single a 1 : Fin k → K) := by
      funext a'
      simp [Finset.sum_apply, Pi.single_apply]
    have e : (Pi.single j (bQ i) : Fin n → (Fin k → K) ⧸ W) =
        ∑ a, x a • Pi.single j (π (Pi.single a 1)) := by
      rw [← hx]
      conv_lhs => rw [hxs]
      rw [show (Pi.single j (W.mkQ (∑ a, x a • (Pi.single a 1 : Fin k → K))) :
          Fin n → (Fin k → K) ⧸ W) = LinearMap.single K (fun _ : Fin n => (Fin k → K) ⧸ W) j
            (W.mkQ (∑ a, x a • (Pi.single a 1 : Fin k → K))) from rfl]
      simp only [map_sum, map_smul, LinearMap.single_apply]
      rfl
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hsingle a j)
  have hcard := card_le_of_mem_span B.linearIndependent w hB
  rw [Fintype.card_sigma, Finset.sum_const, card_univ, Fintype.card_fin, Fintype.card_fin,
    smul_eq_mul, Fintype.card_coe, card_compl, Fintype.card_fin] at hcard
  rw [← hdk, mul_comm]
  exact hcard

open scoped Classical in
lemma sum_filter_none {k n q R : ℕ} (φ : Fin R → Fin k ⊕ Fin q → K) (ψ : Fin R → Fin n ⊕ Fin q → K)
    (χ : Fin R → Option (Fin k × Fin n) → K) (l : Fin k ⊕ Fin q) (r : Fin n ⊕ Fin q) :
    ∑ t ∈ univ.filter (fun t => χ t none ≠ 0), φ t l * ψ t r * χ t none
      = decompTensor φ ψ χ l r none := by
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with h
  · rfl
  · rw [not_not] at h
    rw [h, mul_zero]

open scoped Classical in
/-- "`r_x + r_y + q₀ ≤ |Λ₀|`", where `Λ₀` is the set of terms whose output form contains `z₀`, and
`r_x`, `r_y` are the dimensions of the spans of their outer parts `X_λ`, `Y_λ`. The coefficient
of `z₀` in `T'` is `∑ p_s q_s`. -/
lemma rank_bound {k n q R : ℕ} (φ : Fin R → Fin k ⊕ Fin q → K) (ψ : Fin R → Fin n ⊕ Fin q → K)
    (χ : Fin R → Option (Fin k × Fin n) → K)
    (hz0 : ∀ l r, decompTensor φ ψ χ l r none = gTensor k n q l r none) :
    finrank K (span K ((fun t a => φ t (.inl a)) '' ↑(univ.filter fun t => χ t none ≠ 0))) +
      finrank K (span K ((fun t j => ψ t (.inl j)) '' ↑(univ.filter fun t => χ t none ≠ 0))) + q
      ≤ (univ.filter fun t => χ t none ≠ 0).card := by
  classical
  set Λ0 := univ.filter fun t => χ t none ≠ 0 with hΛ0
  set X : Fin R → Fin k → K := fun t a => φ t (.inl a) with hX
  set Y : Fin R → Fin n → K := fun t j => ψ t (.inl j) with hY
  have hsum : ∀ l r, ∑ t : Λ0, φ t l * ψ t r * χ t none = decompTensor φ ψ χ l r none := by
    intro l r
    rw [Finset.sum_coe_sort Λ0 (fun t => φ t l * ψ t r * χ t none)]
    exact sum_filter_none φ ψ χ l r
  let Vt : (Λ0 → K) →ₗ[K] (Fin n ⊕ Fin q → K) := Fintype.linearCombination K (fun t : Λ0 => ψ t)
  have hVt : ∀ z r, Vt z r = ∑ t : Λ0, z t * ψ t r := by
    intro z r
    simp [Vt, Fintype.linearCombination_apply, Finset.sum_apply]
  -- the rows of `U_x` lie in the kernel of `Vᵀ`
  let u : Fin k → (Λ0 → K) := fun a t => χ t none * φ t (.inl a)
  have hu : ∀ a, u a ∈ LinearMap.ker Vt := by
    intro a
    rw [LinearMap.mem_ker]
    funext r
    rw [hVt, Pi.zero_apply]
    have := hsum (.inl a) r
    rw [hz0] at this
    rw [show ∑ t : Λ0, u a t * ψ t r = ∑ t : Λ0, φ t (.inl a) * ψ t r * χ t none from
      Finset.sum_congr rfl fun t _ => by simp only [u]; ring, this]
    cases r <;> rfl
  -- `rank U_x = r_x`
  have hrx : finrank K (span K (Set.range u)) = finrank K (span K (X '' ↑Λ0)) := by
    let A : Matrix Λ0 (Fin k) K := fun t a => χ t none * φ t (.inl a)
    have h1 : span K (Set.range u) = LinearMap.range A.mulVecLin := by
      rw [Matrix.range_mulVecLin]
      rfl
    have h2 : span K (Set.range (Matrix.transpose A).col) = span K (X '' ↑Λ0) := by
      apply le_antisymm
      · rw [span_le]
        rintro _ ⟨t, rfl⟩
        have : (Matrix.transpose A).col t = χ t none • X t := by
          funext a
          rfl
        rw [this]
        exact smul_mem _ _ (subset_span ⟨t, t.2, rfl⟩)
      · rw [span_le]
        rintro _ ⟨t, ht, rfl⟩
        have hc : χ t none ≠ 0 := (mem_filter.1 ht).2
        have : X t = (χ t none)⁻¹ • (Matrix.transpose A).col ⟨t, ht⟩ := by
          funext a
          simp only [Pi.smul_apply, smul_eq_mul]
          show φ t (.inl a) = (χ t none)⁻¹ * (χ t none * φ t (.inl a))
          rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
        rw [this]
        exact smul_mem _ _ (subset_span ⟨⟨t, ht⟩, rfl⟩)
    rw [h1, ← h2, ← Matrix.range_mulVecLin]
    exact (Matrix.rank_transpose A).symm
  have hker : finrank K (span K (Set.range u)) ≤ finrank K (LinearMap.ker Vt) :=
    Submodule.finrank_mono (span_le.2 (by rintro _ ⟨a, rfl⟩; exact hu a))
  have hrn := LinearMap.finrank_range_add_finrank_ker Vt
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at hrn
  -- `rank V ≥ r_y + q₀`
  let ρ : (Fin n ⊕ Fin q → K) →ₗ[K] (Fin n → K) := LinearMap.funLeft K K Sum.inl
  let f := ρ.domRestrict (LinearMap.range Vt)
  have hrange : finrank K (LinearMap.range f) = finrank K (span K (Y '' ↑Λ0)) := by
    rw [LinearMap.range_domRestrict, ← LinearMap.range_comp]
    have hc : ρ ∘ₗ Vt = Fintype.linearCombination K (fun t : Λ0 => Y t) := by
      refine LinearMap.ext fun z => funext fun j => ?_
      simp [ρ, Vt, LinearMap.funLeft_apply, Fintype.linearCombination_apply, Finset.sum_apply, Y]
    have hset : Set.range (fun t : Λ0 => Y t) = Y '' ↑Λ0 := by
      ext v
      simp
    rw [hc, Fintype.range_linearCombination, hset]
  let u' : Fin q → (Λ0 → K) := fun s t => χ t none * φ t (.inr s)
  have hg : ∀ s, Vt (u' s) = Pi.single (Sum.inr s) 1 := by
    intro s
    funext r
    rw [hVt, show ∑ t : Λ0, u' s t * ψ t r = ∑ t : Λ0, φ t (.inr s) * ψ t r * χ t none from
      Finset.sum_congr rfl fun t _ => by simp only [u']; ring, hsum, hz0]
    cases r with
    | inl j => simp [gTensor]
    | inr t => simp [gTensor, Pi.single_apply, eq_comm]
  have hgk : ∀ s, (⟨Vt (u' s), LinearMap.mem_range_self _ _⟩ : LinearMap.range Vt) ∈
      LinearMap.ker f := by
    intro s
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply]
    simp only [hg]
    funext j
    simp [ρ, LinearMap.funLeft_apply]
  let gk : Fin q → LinearMap.ker f := fun s => ⟨_, hgk s⟩
  have hgind : LinearIndependent K gk := by
    apply LinearIndependent.of_comp ((LinearMap.range Vt).subtype ∘ₗ (LinearMap.ker f).subtype)
    have : ((LinearMap.range Vt).subtype ∘ₗ (LinearMap.ker f).subtype) ∘ gk =
        fun s => (Pi.basisFun K (Fin n ⊕ Fin q)) (Sum.inr s) := by
      funext s
      simp [gk, hg, Pi.basisFun_apply]
    rw [this]
    exact (Pi.basisFun K (Fin n ⊕ Fin q)).linearIndependent.comp Sum.inr Sum.inr_injective
  have hq : q ≤ finrank K (LinearMap.ker f) := by
    have := hgind.fintype_card_le_finrank
    rwa [Fintype.card_fin] at this
  have hrn2 := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn2
  rw [hrx] at hker
  omega

open scoped Classical in
/-- The case "errors only on outer outputs": `R ≥ q₀ + k + n`. -/
lemma caseI {k n q R : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ n) (φ : Fin R → Fin k ⊕ Fin q → K)
    (ψ : Fin R → Fin n ⊕ Fin q → K) (χ : Fin R → Option (Fin k × Fin n) → K)
    (hz0 : ∀ l r, decompTensor φ ψ χ l r none = gTensor k n q l r none)
    (h2 : ∀ a j o, decompTensor φ ψ χ (.inl a) (.inl j) (some o) = if o = (a, j) then 1 else 0) :
    q + k + n ≤ R := by
  classical
  have hi := rank_bound φ ψ χ hz0
  set Λ0 := univ.filter fun t => χ t none ≠ 0 with hΛ0
  have hii := quot_bound (fun t a => φ t (.inl a)) (fun t j => ψ t (.inl j))
    (fun t o => χ t (some o)) Λ0 (fun a j o => h2 a j o)
  have hiii := quot_bound (fun t j => ψ t (.inl j)) (fun t a => φ t (.inl a))
    (fun t o => χ t (some (o.2, o.1))) Λ0 (by
      intro j a o
      have := h2 a j (o.2, o.1)
      simp only [decompTensor] at this
      rw [show ∑ t, ψ t (.inl j) * φ t (.inl a) * χ t (some (o.2, o.1))
          = ∑ t, φ t (.inl a) * ψ t (.inl j) * χ t (some (o.2, o.1)) from
        Finset.sum_congr rfl fun _ _ => by ring, this]
      by_cases h : o = (j, a)
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        apply h
        obtain ⟨o1, o2⟩ := o
        simp only [Prod.mk.injEq] at h' ⊢
        exact ⟨h'.2, h'.1⟩)
  set rx := finrank K (span K ((fun t a => φ t (.inl a)) '' (↑Λ0 : Set (Fin R)))) with hrxdef
  set ry := finrank K (span K ((fun t j => ψ t (.inl j)) '' (↑Λ0 : Set (Fin R)))) with hrydef
  have hrx : rx ≤ k := by
    have := Submodule.finrank_le (span K ((fun t a => φ t (.inl a)) '' (↑Λ0 : Set (Fin R))))
    rwa [Module.finrank_fin_fun] at this
  have hry : ry ≤ n := by
    have := Submodule.finrank_le (span K ((fun t j => ψ t (.inl j)) '' (↑Λ0 : Set (Fin R))))
    rwa [Module.finrank_fin_fun] at this
  have hΛ : Λ0.card ≤ R := (card_le_univ _).trans (by simp)
  have key : (k - rx) + (n - ry) ≤ R - Λ0.card := by
    rcases le_total (k - rx) (n - ry) with h | h
    · have : 2 * (n - ry) ≤ (n - ry) * k := by nlinarith
      omega
    · have : 2 * (k - rx) ≤ (k - rx) * n := by nlinarith
      omega
  omega

/-! ### Proposition A.2 -/

theorem prop_A_2 : Prop_A_2 := by
  intro K _ k n q R φ ψ χ hk hn ⟨α, β, hαβ⟩
  have hzero : ∀ l r o, α * ((varClass l - outClass o : ℤ) : ℝ) +
      β * ((varClass r - outClass o : ℤ) : ℝ) ≤ 0 →
      decompTensor φ ψ χ l r o = gTensor k n q l r o := by
    intro l r o h
    by_contra hne
    exact absurd (hαβ l r o (sub_ne_zero.2 hne)) (not_lt.2 h)
  have h1 : ∀ s t, decompTensor φ ψ χ (.inr s) (.inr t) none = if s = t then 1 else 0 := by
    intro s t
    rw [hzero _ _ _ (by simp [varClass, outClass])]
    rfl
  have h2 : ∀ a j o, decompTensor φ ψ χ (.inl a) (.inl j) (some o) =
      if o = (a, j) then 1 else 0 := by
    intro a j o
    rw [hzero _ _ _ (by simp [varClass, outClass])]
    rfl
  have hkn : k + n ≤ k * n := by nlinarith
  suffices h : q + k + n ≤ R from ⟨h, by omega⟩
  rcases le_or_gt α 0 with hα | hα
  · -- no monomial with `p` and `y` on an outer output
    have h3 : ∀ s j o, decompTensor φ ψ χ (.inr s) (.inl j) (some o) = 0 := by
      intro s j o
      rw [hzero _ _ _ (by simp [varClass, outClass]; linarith)]
      rfl
    have := caseII φ ψ χ h1 h2 h3
    omega
  rcases le_or_gt β 0 with hβ | hβ
  · -- no monomial with `x` and `q` on an outer output: the mirror image
    have h3 : ∀ a s o, decompTensor φ ψ χ (.inl a) (.inr s) (some o) = 0 := by
      intro a s o
      rw [hzero _ _ _ (by simp [varClass, outClass]; linarith)]
      rfl
    have := caseII (k := n) (n := k) ψ φ (fun t o => χ t (o.map Prod.swap))
      (fun s t => by
        have := h1 t s
        simp only [decompTensor, Option.map_none] at this ⊢
        rw [show ∑ u, ψ u (.inr s) * φ u (.inr t) * χ u none
            = ∑ u, φ u (.inr t) * ψ u (.inr s) * χ u none from
          Finset.sum_congr rfl fun _ _ => by ring, this]
        simp [eq_comm])
      (fun j a o => by
        have := h2 a j o.swap
        simp only [decompTensor, Option.map_some] at this ⊢
        rw [show ∑ u, ψ u (.inl j) * φ u (.inl a) * χ u (some o.swap)
            = ∑ u, φ u (.inl a) * ψ u (.inl j) * χ u (some o.swap) from
          Finset.sum_congr rfl fun _ _ => by ring, this]
        obtain ⟨o1, o2⟩ := o
        simp only [Prod.swap_prod_mk, Prod.mk.injEq]
        by_cases h : o2 = a ∧ o1 = j
        · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
        · rw [if_neg h, if_neg fun h' => h ⟨h'.2, h'.1⟩])
      (fun s a o => by
        have := h3 a s o.swap
        simp only [decompTensor, Option.map_some] at this ⊢
        rw [show ∑ u, ψ u (.inr s) * φ u (.inl a) * χ u (some o.swap)
            = ∑ u, φ u (.inl a) * ψ u (.inr s) * χ u (some o.swap) from
          Finset.sum_congr rfl fun _ _ => by ring, this])
    rw [mul_comm] at this
    omega
  · -- errors only on outer outputs
    have hz0 : ∀ l r, decompTensor φ ψ χ l r none = gTensor k n q l r none := by
      intro l r
      apply hzero
      cases l <;> cases r <;> simp [varClass, outClass] <;> linarith
    exact caseI hk hn φ ψ χ hz0 h2

end ThinMatrixProducts

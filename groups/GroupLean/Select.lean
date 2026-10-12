import Mathlib

/-!
# The one-row and greedy lemmas over `F_p` (Lemmas 19.2 and 19.3 of the paper)

Lemma 1 (`select_average`, `select_exists`), Lemma 2 (`greedy_bound`, `greedy_bound_exp`), the
whole space as a 0-value-biased set (`isValBiased_univ`), and the pair-row survival bound of the
"value bias" paragraph of Section 19.6 (`pair_survival`). Adapted from `XorLean/Basic.lean` (the case `p = 2`).
-/

namespace GroupLean

/-- `F_p^d`. -/
abbrev VecP (p d : ℕ) := Fin d → ZMod p

/-- ε-value-biased multiset: every value `s` of every nonzero functional `⟨·, v⟩` is taken by at
most `(1+ε)|E|/p` rows. -/
def IsValBiased {p d : ℕ} (ε : ℝ) (E : Multiset (VecP p d)) : Prop :=
  E ≠ 0 ∧ ∀ v : VecP p d, v ≠ 0 → ∀ s : ZMod p,
    ((E.filter (fun u => u ⬝ᵥ v = s)).card : ℝ) ≤ (1 + ε) / p * E.card

/-- ε-kernel-biased multiset: the value `0` only. -/
def IsKerBiased {p d : ℕ} (ε : ℝ) (E : Multiset (VecP p d)) : Prop :=
  E ≠ 0 ∧ ∀ v : VecP p d, v ≠ 0 →
    ((E.filter (fun u => u ⬝ᵥ v = 0)).card : ℝ) ≤ (1 + ε) / p * E.card

theorem IsValBiased.isKerBiased {p d : ℕ} {ε : ℝ} {E : Multiset (VecP p d)}
    (h : IsValBiased ε E) : IsKerBiased ε E :=
  ⟨h.1, fun v hv => h.2 v hv 0⟩

theorem IsValBiased.mono {p d : ℕ} {ε ε' : ℝ} {E : Multiset (VecP p d)}
    (h : IsValBiased ε E) (hε : ε ≤ ε') : IsValBiased ε' E := by
  refine ⟨h.1, fun v hv s => (h.2 v hv s).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- The surviving weight `Φ`: the weight of the `v_j` that every row sends to `0`. -/
noncomputable def surv {p d : ℕ} {ι : Type*} (s : Finset ι) (v : ι → VecP p d) (ω : ι → ℝ)
    (rows : List (VecP p d)) : ℝ :=
  ∑ j ∈ s with ∀ u ∈ rows, u ⬝ᵥ v j = 0, ω j

/-- `rows` (newest first) was chosen greedily from `E` for the cost `f`. -/
def IsGreedy {p d : ℕ} (E : Multiset (VecP p d)) (f : List (VecP p d) → ℝ) :
    List (VecP p d) → Prop
  | [] => True
  | u :: rows => IsGreedy E f rows ∧ u ∈ E ∧ ∀ u' ∈ E, f (u :: rows) ≤ f (u' :: rows)

/-- The rows chosen before a greedy row are greedy (prefix in time = suffix of the list). -/
theorem IsGreedy.drop {p d : ℕ} {E : Multiset (VecP p d)} {f : List (VecP p d) → ℝ} :
    ∀ (rows : List (VecP p d)) (k : ℕ), IsGreedy E f rows → IsGreedy E f (rows.drop k)
  | [], k, _ => by simp [IsGreedy]
  | _ :: _, 0, h => h
  | _ :: rows, k + 1, h => IsGreedy.drop rows k h.1

/-! ### Lemma 1 -/

lemma sum_map_ite_const {α : Type*} (E : Multiset α) (P : α → Prop) [DecidablePred P] (c : ℝ) :
    (E.map fun u => if P u then c else 0).sum = (E.filter P).card * c := by
  induction E using Multiset.induction_on with
  | empty => simp
  | cons a E ih =>
    by_cases h : P a
    · simp [Multiset.filter_cons_of_pos _ h, h, ih]; ring
    · simp [Multiset.filter_cons_of_neg _ h, h, ih]

/-- The constant `(1+ε)/p` of a kernel-biased set is nonnegative (when some nonzero vector
exists). -/
lemma IsKerBiased.const_nonneg {p d : ℕ} {ε : ℝ} {E : Multiset (VecP p d)}
    (hE : IsKerBiased ε E) {v : VecP p d} (hv : v ≠ 0) : 0 ≤ (1 + ε) / p := by
  have h1 := hE.2 v hv
  have hpos : (0 : ℝ) < E.card := by exact_mod_cast Multiset.card_pos.mpr hE.1
  have := le_trans (Nat.cast_nonneg _) h1
  exact nonneg_of_mul_nonneg_left this hpos

theorem select_average {p d : ℕ} {ι : Type*} {ε : ℝ} {E : Multiset (VecP p d)}
    (hE : IsKerBiased ε E) (s : Finset ι) (v : ι → VecP p d) (ω : ι → ℝ)
    (hv : ∀ j ∈ s, v j ≠ 0) (hω : ∀ j ∈ s, 0 ≤ ω j) :
    (E.map fun u => ∑ j ∈ s with u ⬝ᵥ v j = 0, ω j).sum
      ≤ E.card * ((1 + ε) / p * ∑ j ∈ s, ω j) := by
  calc (E.map fun u => ∑ j ∈ s with u ⬝ᵥ v j = 0, ω j).sum
      = (E.map fun u => ∑ j ∈ s, (if u ⬝ᵥ v j = 0 then ω j else 0)).sum := by
        congr 1
        apply Multiset.map_congr rfl
        intro u _
        rw [Finset.sum_filter]
    _ = ∑ j ∈ s, (E.map fun u => if u ⬝ᵥ v j = 0 then ω j else 0).sum :=
        Multiset.sum_map_sum_map E s.val
    _ = ∑ j ∈ s, ((E.filter fun u => u ⬝ᵥ v j = 0).card : ℝ) * ω j := by
        apply Finset.sum_congr rfl
        intro j _
        exact sum_map_ite_const E _ _
    _ ≤ ∑ j ∈ s, (1 + ε) / p * E.card * ω j := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_right (hE.2 _ (hv j hj)) (hω j hj)
    _ = E.card * ((1 + ε) / p * ∑ j ∈ s, ω j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

theorem select_exists {p d : ℕ} {ι : Type*} {ε : ℝ} {E : Multiset (VecP p d)}
    (hE : IsKerBiased ε E) (s : Finset ι) (v : ι → VecP p d) (ω : ι → ℝ)
    (hv : ∀ j ∈ s, v j ≠ 0) (hω : ∀ j ∈ s, 0 ≤ ω j) :
    ∃ u ∈ E, ∑ j ∈ s with u ⬝ᵥ v j = 0, ω j ≤ (1 + ε) / p * ∑ j ∈ s, ω j := by
  set g : VecP p d → ℝ := fun u => ∑ j ∈ s with u ⬝ᵥ v j = 0, ω j with hg
  have hne : E.toFinset.Nonempty := Multiset.toFinset_nonempty.mpr hE.1
  obtain ⟨u0, hu0, hmin⟩ := Finset.exists_min_image E.toFinset g hne
  refine ⟨u0, Multiset.mem_toFinset.mp hu0, ?_⟩
  have hsum := select_average hE s v ω hv hω
  have hle : E.card • g u0 ≤ (E.map g).sum :=
    Multiset.card_nsmul_le_sum (fun x hx => by
      obtain ⟨u, hu, rfl⟩ := Multiset.mem_map.mp hx
      exact hmin u (Multiset.mem_toFinset.mpr hu)) |>.trans_eq' (by rw [Multiset.card_map])
  rw [nsmul_eq_mul] at hle
  have hpos : (0 : ℝ) < E.card := by
    exact_mod_cast Multiset.card_pos.mpr hE.1
  have : (E.card : ℝ) * g u0 ≤ E.card * ((1 + ε) / p * ∑ j ∈ s, ω j) := le_trans hle hsum
  exact le_of_mul_le_mul_left this hpos

/-! ### Fibers of a surjective homomorphism onto `ZMod p` -/

/-- Every fiber of a surjective additive homomorphism `G → ZMod p` has `|G|/p` elements. -/
theorem card_fiber_mul_eq {p : ℕ} [NeZero p] {G : Type*} [AddGroup G] [Fintype G]
    (f : G →+ ZMod p) (hf : Function.Surjective f) (s : ZMod p) :
    (Finset.univ.filter fun g => f g = s).card * p = Fintype.card G := by
  classical
  have hfib : ∀ t : ZMod p, (Finset.univ.filter fun g => f g = t).card
      = (Finset.univ.filter fun g => f g = s).card := fun t =>
    AddMonoidHom.card_fiber_eq_of_mem_range f (hf t) (hf s)
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl (fun t _ => hfib t), Finset.sum_const, Finset.card_univ, ZMod.card,
    smul_eq_mul, mul_comm]

/-- The whole space is 0-value-biased (for `d ≥ 1`). -/
theorem isValBiased_univ (p d : ℕ) [Fact p.Prime] :
    IsValBiased 0 (Finset.univ : Finset (VecP p d)).val := by
  refine ⟨?_, ?_⟩
  · intro h
    have : (Finset.univ : Finset (VecP p d)) = ∅ := Finset.val_eq_zero.mp h
    exact Finset.univ_nonempty.ne_empty this
  · intro v hv s
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      exact hv (funext h)
    let f : VecP p d →+ ZMod p :=
      { toFun := fun u => u ⬝ᵥ v
        map_zero' := zero_dotProduct v
        map_add' := fun a b => add_dotProduct a b v }
    have hf : Function.Surjective f := by
      intro t
      refine ⟨Pi.single i (t / v i), ?_⟩
      change Pi.single i (t / v i) ⬝ᵥ v = t
      rw [single_dotProduct]
      field_simp
    have hc := card_fiber_mul_eq f hf s
    have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    have hfil : ((Finset.univ : Finset (VecP p d)).val.filter (fun u => u ⬝ᵥ v = s)).card
        = (Finset.univ.filter fun g => f g = s).card := rfl
    rw [hfil, Finset.card_val, Finset.card_univ, add_zero, one_div_mul_eq_div,
      le_div_iff₀ hp]
    exact_mod_cast hc.le

/-! ### Lemma 2 -/

/-- Some minimizer of `g` over `E` (an arbitrary vector, `0`, when `E = 0`). -/
noncomputable def argminOn {p d : ℕ} (E : Multiset (VecP p d)) (g : VecP p d → ℝ) : VecP p d :=
  if h : E ≠ 0 then
    Classical.choose (Finset.exists_min_image E.toFinset g (Multiset.toFinset_nonempty.mpr h))
  else 0

theorem argminOn_spec {p d : ℕ} (E : Multiset (VecP p d)) (hE : E ≠ 0) (g : VecP p d → ℝ) :
    argminOn E g ∈ E ∧ ∀ u' ∈ E, g (argminOn E g) ≤ g u' := by
  unfold argminOn
  rw [dif_pos hE]
  have h := Classical.choose_spec
    (Finset.exists_min_image E.toFinset g (Multiset.toFinset_nonempty.mpr hE))
  exact ⟨Multiset.mem_toFinset.mp h.1, fun u' hu' => h.2 u' (Multiset.mem_toFinset.mpr hu')⟩

/-- The greedy choice as a function: `r` rows, each an argmin over `E`. -/
noncomputable def greedyRows {p d : ℕ} (E : Multiset (VecP p d)) (f : List (VecP p d) → ℝ) :
    ℕ → List (VecP p d)
  | 0 => []
  | r + 1 => argminOn E (fun u => f (u :: greedyRows E f r)) :: greedyRows E f r

theorem greedyRows_length {p d : ℕ} (E : Multiset (VecP p d)) (f : List (VecP p d) → ℝ)
    (r : ℕ) : (greedyRows E f r).length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [greedyRows, ih]

theorem isGreedy_greedyRows {p d : ℕ} (E : Multiset (VecP p d)) (hE : E ≠ 0)
    (f : List (VecP p d) → ℝ) (r : ℕ) : IsGreedy E f (greedyRows E f r) := by
  induction r with
  | zero => trivial
  | succ r ih =>
    exact ⟨ih, (argminOn_spec E hE (fun u => f (u :: greedyRows E f r))).1,
      (argminOn_spec E hE (fun u => f (u :: greedyRows E f r))).2⟩

/-- Greedy choice for a cost that differs by a constant is the same choice. -/
theorem isGreedy_add_const {p d : ℕ} (E : Multiset (VecP p d)) (f : List (VecP p d) → ℝ)
    (c : ℝ) (rows : List (VecP p d)) :
    IsGreedy E (fun l => f l + c) rows ↔ IsGreedy E f rows := by
  induction rows with
  | nil => simp [IsGreedy]
  | cons u rows ih => simp [IsGreedy, ih]

private lemma surv_cons {p d : ℕ} {ι : Type*} (s : Finset ι) (v : ι → VecP p d) (ω : ι → ℝ)
    (u : VecP p d) (rows : List (VecP p d)) :
    surv s v ω (u :: rows)
      = ∑ j ∈ s.filter (fun j => ∀ x ∈ rows, x ⬝ᵥ v j = 0) with u ⬝ᵥ v j = 0, ω j := by
  unfold surv
  rw [Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp [and_comm]

theorem greedy_bound {p d : ℕ} {ι : Type*} {ε : ℝ} {E : Multiset (VecP p d)}
    (hE : IsKerBiased ε E) (s : Finset ι) (v : ι → VecP p d) (ω : ι → ℝ)
    (hv : ∀ j ∈ s, v j ≠ 0) (hω : ∀ j ∈ s, 0 ≤ ω j)
    (rows : List (VecP p d)) (hg : IsGreedy E (surv s v ω) rows) :
    surv s v ω rows ≤ ((1 + ε) / p) ^ rows.length * ∑ j ∈ s, ω j := by
  rcases s.eq_empty_or_nonempty with hs | ⟨j0, hj0⟩
  · subst hs
    simp [surv]
  have hc : 0 ≤ (1 + ε) / p := hE.const_nonneg (hv j0 hj0)
  induction rows with
  | nil => simp [surv]
  | cons u rows ih =>
    obtain ⟨hg', -, hmin⟩ := hg
    have ih := ih hg'
    set P : ι → Prop := fun j => ∀ x ∈ rows, x ⬝ᵥ v j = 0
    obtain ⟨u', hu', hsel⟩ := select_exists hE (s.filter P) v ω
      (fun j hj => hv j (Finset.mem_filter.mp hj).1)
      (fun j hj => hω j (Finset.mem_filter.mp hj).1)
    rw [← surv_cons] at hsel
    have hrows : surv s v ω rows = ∑ j ∈ s.filter P, ω j := rfl
    rw [← hrows] at hsel
    calc surv s v ω (u :: rows) ≤ surv s v ω (u' :: rows) := hmin u' hu'
      _ ≤ (1 + ε) / p * surv s v ω rows := hsel
      _ ≤ (1 + ε) / p * (((1 + ε) / p) ^ rows.length * ∑ j ∈ s, ω j) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = ((1 + ε) / p) ^ (u :: rows).length * ∑ j ∈ s, ω j := by
          rw [List.length_cons, pow_succ]; ring

theorem one_add_inv_pow_le_exp (r : ℕ) (hr : 0 < r) : (1 + 1 / (r : ℝ)) ^ r ≤ Real.exp 1 := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : 1 + 1 / (r : ℝ) ≤ Real.exp (1 / r) := by
    have := Real.add_one_le_exp (1 / (r : ℝ)); linarith
  have h0 : 0 ≤ 1 + 1 / (r : ℝ) := by positivity
  calc (1 + 1 / (r : ℝ)) ^ r ≤ Real.exp (1 / r) ^ r := pow_le_pow_left₀ h0 h1 r
    _ = Real.exp (r * (1 / r)) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp 1 := by rw [mul_one_div_cancel hr']

theorem greedy_bound_exp {p d : ℕ} {ι : Type*} {ε : ℝ} {E : Multiset (VecP p d)}
    (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε) (s : Finset ι) (v : ι → VecP p d) (ω : ι → ℝ)
    (hv : ∀ j ∈ s, v j ≠ 0) (hω : ∀ j ∈ s, 0 ≤ ω j)
    (rows : List (VecP p d)) (hg : IsGreedy E (surv s v ω) rows)
    (hr : 0 < rows.length) (hε : ε ≤ 1 / rows.length) :
    surv s v ω rows ≤ Real.exp 1 * (1 / (p : ℝ) ^ rows.length) * ∑ j ∈ s, ω j := by
  have hb := greedy_bound hE s v ω hv hω rows hg
  have hS : 0 ≤ ∑ j ∈ s, ω j := Finset.sum_nonneg hω
  set r := rows.length
  have hpow : ((1 + ε) / p) ^ r ≤ Real.exp 1 * (1 / (p : ℝ) ^ r) := by
    rw [div_pow, div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (1 + ε) ^ r ≤ (1 + 1 / (r : ℝ)) ^ r :=
          pow_le_pow_left₀ (by linarith) (by linarith) r
      _ ≤ Real.exp 1 := one_add_inv_pow_le_exp r hr
  exact le_trans hb (mul_le_mul_of_nonneg_right hpow hS)

/-- Lemma 2 for every prefix (in time) of a greedy sequence: the last `rows.length - k` rows. -/
theorem greedy_bound_exp_drop {p d : ℕ} {ι : Type*} {ε : ℝ} {E : Multiset (VecP p d)}
    (hE : IsKerBiased ε E) (hε0 : 0 ≤ ε) (s : Finset ι) (v : ι → VecP p d) (ω : ι → ℝ)
    (hv : ∀ j ∈ s, v j ≠ 0) (hω : ∀ j ∈ s, 0 ≤ ω j)
    (rows : List (VecP p d)) (hg : IsGreedy E (surv s v ω) rows) (k : ℕ)
    (hr : 0 < (rows.drop k).length) (hε : ε ≤ 1 / rows.length) :
    surv s v ω (rows.drop k)
      ≤ Real.exp 1 * (1 / (p : ℝ) ^ (rows.drop k).length) * ∑ j ∈ s, ω j := by
  refine greedy_bound_exp hE hε0 s v ω hv hω _ (hg.drop rows k) hr (hε.trans ?_)
  apply one_div_le_one_div_of_le (by exact_mod_cast hr)
  exact_mod_cast (show (rows.drop k).length ≤ rows.length by rw [List.length_drop]; omega)

/-! ### Pair rows (Section 19.6, value bias) -/

lemma card_filter_product {α β : Type*} (E₁ : Multiset α) (E₂ : Multiset β)
    (P : α × β → Prop) [DecidablePred P] :
    ((E₁ ×ˢ E₂).filter P).card = (E₁.map fun a => (E₂.filter fun b => P (a, b)).card).sum := by
  induction E₁ using Multiset.induction_on with
  | empty => simp
  | cons a E ih =>
    rw [Multiset.cons_product, Multiset.filter_add, Multiset.card_add, ih, Multiset.map_cons,
      Multiset.sum_cons, Multiset.filter_map, Multiset.card_map]
    rfl

/-- For pair rows `(a, b) ∈ E₁ × E₂` and a target value `c a` depending on `a`: at most a fraction
`((1+ε)/p)²` of the pairs have `⟨a, v⟩ = 0` and `⟨b, v⟩ = c a`. -/
theorem pair_survival {p d : ℕ} {ε : ℝ} {E₁ E₂ : Multiset (VecP p d)}
    (h₁ : IsValBiased ε E₁) (h₂ : IsValBiased ε E₂) {v : VecP p d} (hv : v ≠ 0)
    (c : VecP p d → ZMod p) :
    (((E₁ ×ˢ E₂).filter fun ab => ab.1 ⬝ᵥ v = 0 ∧ ab.2 ⬝ᵥ v = c ab.1).card : ℝ)
      ≤ ((1 + ε) / p) ^ 2 * E₁.card * E₂.card := by
  rw [card_filter_product, Nat.cast_multiset_sum, Multiset.map_map]
  have hc : 0 ≤ (1 + ε) / p := h₁.isKerBiased.const_nonneg hv
  calc ((E₁.map ((Nat.cast : ℕ → ℝ) ∘ fun a =>
          (E₂.filter fun b => a ⬝ᵥ v = 0 ∧ b ⬝ᵥ v = c a).card))).sum
      ≤ (E₁.map fun a => if a ⬝ᵥ v = 0 then (1 + ε) / p * E₂.card else 0).sum := by
        apply Multiset.sum_map_le_sum_map
        intro a _
        simp only [Function.comp]
        split_ifs with ha
        · simpa [ha] using h₂.2 v hv (c a)
        · simp [ha]
    _ = (E₁.filter fun a => a ⬝ᵥ v = 0).card * ((1 + ε) / p * E₂.card) :=
        sum_map_ite_const _ _ _
    _ ≤ (1 + ε) / p * E₁.card * ((1 + ε) / p * E₂.card) :=
        mul_le_mul_of_nonneg_right (h₁.2 v hv 0) (by positivity)
    _ = ((1 + ε) / p) ^ 2 * E₁.card * E₂.card := by ring

end GroupLean

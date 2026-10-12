import XorLean.Defs

/-!
# T1 and T2 of the 3-XOR note: `rowsMap`'s zero set, Lemma 4 (`lem:select`),
Lemma 5 (`lem:greedy`)
-/

namespace Xor

/-! ### 2.0 -/

theorem rowsMap_eq_zero_iff {ℓ : ℕ} (rows : List (Vec ℓ)) (x : Vec ℓ) :
    rowsMap rows x = 0 ↔ ∀ u ∈ rows, u ⬝ᵥ x = 0 := by
  unfold rowsMap
  rw [Matrix.mulVecLin_apply, funext_iff]
  simp only [Pi.zero_apply, Matrix.mulVec, Matrix.of_apply]
  constructor
  · intro h u hu
    obtain ⟨i, rfl⟩ := List.get_of_mem hu
    exact h i
  · intro h i
    exact h _ (List.get_mem rows i)

/-! ### 2.1 -/

theorem select_average {ℓ : ℕ} {ι : Type*} {ε : ℝ} {E : Multiset (Vec ℓ)}
    (hE : IsBiased ε E) (s : Finset ι) (v : ι → Vec ℓ) (ω : ι → ℝ)
    (hv : ∀ j ∈ s, v j ≠ 0) (hω : ∀ j ∈ s, 0 ≤ ω j) :
    (E.map fun u => ∑ j ∈ s with u ⬝ᵥ v j = 0, ω j).sum
      ≤ E.card * ((1 + ε) / 2 * ∑ j ∈ s, ω j) := by
  calc (E.map fun u => ∑ j ∈ s with u ⬝ᵥ v j = 0, ω j).sum
      = (E.map fun u => ∑ j ∈ s, (ω j / 2 + ω j / 2 * (chi u (v j) : ℝ))).sum := by
        congr 1
        apply Multiset.map_congr rfl
        intro u _
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro j _
        unfold chi
        split_ifs <;> push_cast <;> ring
    _ = ∑ j ∈ s, (E.map fun u => ω j / 2 + ω j / 2 * (chi u (v j) : ℝ)).sum :=
        Multiset.sum_map_sum_map E s.val
    _ = ∑ j ∈ s, (E.card * (ω j / 2) + ω j / 2 * (E.map fun u => (chi u (v j) : ℝ)).sum) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Multiset.sum_map_add, Multiset.sum_map_mul_left]
        simp [mul_comm]
    _ ≤ ∑ j ∈ s, (E.card * (ω j / 2) + ω j / 2 * (ε * E.card)) := by
        apply Finset.sum_le_sum
        intro j hj
        have h1 := hE.2 _ (hv j hj)
        have h2 : 0 ≤ ω j / 2 := by linarith [hω j hj]
        have := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) h1) h2
        linarith
    _ = E.card * ((1 + ε) / 2 * ∑ j ∈ s, ω j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

theorem select_exists {ℓ : ℕ} {ι : Type*} {ε : ℝ} {E : Multiset (Vec ℓ)}
    (hE : IsBiased ε E) (s : Finset ι) (v : ι → Vec ℓ) (ω : ι → ℝ)
    (hv : ∀ j ∈ s, v j ≠ 0) (hω : ∀ j ∈ s, 0 ≤ ω j) :
    ∃ u ∈ E, ∑ j ∈ s with u ⬝ᵥ v j = 0, ω j ≤ (1 + ε) / 2 * ∑ j ∈ s, ω j := by
  set g : Vec ℓ → ℝ := fun u => ∑ j ∈ s with u ⬝ᵥ v j = 0, ω j with hg
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
  have : (E.card : ℝ) * g u0 ≤ E.card * ((1 + ε) / 2 * ∑ j ∈ s, ω j) := le_trans hle hsum
  exact le_of_mul_le_mul_left this hpos

private lemma zmod2_eq_one_of_ne_zero : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide

/-- The full space is 0-biased (the note's remark after Definition 2). -/
theorem isBiased_univ (ℓ : ℕ) : IsBiased 0 (Finset.univ : Finset (Vec ℓ)).val := by
  refine ⟨?_, ?_⟩
  · intro h
    have : (Finset.univ : Finset (Vec ℓ)) = ∅ := Finset.val_eq_zero.mp h
    exact Finset.univ_nonempty.ne_empty this
  · intro w hw
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (funext h)
    have hwi : w i = 1 := zmod2_eq_one_of_ne_zero _ hi
    have hsum : ∑ u : Vec ℓ, (chi u w : ℝ) = 0 := by
      refine Finset.sum_involution (fun u _ => u + Pi.single i 1) ?_ ?_ (by simp) ?_
      · intro u _
        have hd : (u + Pi.single i 1) ⬝ᵥ w = u ⬝ᵥ w + 1 := by
          rw [add_dotProduct, single_dotProduct, hwi, one_mul]
        unfold chi
        rw [hd]
        generalize u ⬝ᵥ w = a
        rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl
        · simp
        · rw [(by decide : (1 : ZMod 2) + 1 = 0)]; norm_num
      · intro u _ _ h
        have : (Pi.single i (1 : ZMod 2) : Vec ℓ) = 0 := by
          simpa using congrArg (· - u) h
        have := congrFun this i
        simp at this
      · intro u _
        rw [add_assoc]
        have : (Pi.single i (1 : ZMod 2) : Vec ℓ) + Pi.single i 1 = 0 := by
          rw [← Pi.single_add]
          simp [(by decide : (1 : ZMod 2) + 1 = 0)]
        rw [this, add_zero]
    have : ((Finset.univ : Finset (Vec ℓ)).val.map fun u => (chi u w : ℝ)).sum = 0 := hsum
    rw [this]
    simp

/-! ### 2.2 -/

/-- Greedy choice for a cost that differs by a constant is the same choice. -/
theorem isGreedy_add_const {ℓ : ℕ} (E : Multiset (Vec ℓ)) (f : List (Vec ℓ) → ℝ) (c : ℝ)
    (rows : List (Vec ℓ)) :
    IsGreedy E (fun l => f l + c) rows ↔ IsGreedy E f rows := by
  induction rows with
  | nil => simp [IsGreedy]
  | cons u rows ih => simp [IsGreedy, ih]

/-- Some minimizer of `g` over `E` (an arbitrary vector, `0`, when `E = 0`). -/
noncomputable def argminOn {ℓ : ℕ} (E : Multiset (Vec ℓ)) (g : Vec ℓ → ℝ) : Vec ℓ :=
  if h : E ≠ 0 then
    Classical.choose (Finset.exists_min_image E.toFinset g (Multiset.toFinset_nonempty.mpr h))
  else 0

theorem argminOn_spec {ℓ : ℕ} (E : Multiset (Vec ℓ)) (hE : E ≠ 0) (g : Vec ℓ → ℝ) :
    argminOn E g ∈ E ∧ ∀ u' ∈ E, g (argminOn E g) ≤ g u' := by
  unfold argminOn
  rw [dif_pos hE]
  have h := Classical.choose_spec
    (Finset.exists_min_image E.toFinset g (Multiset.toFinset_nonempty.mpr hE))
  exact ⟨Multiset.mem_toFinset.mp h.1, fun u' hu' => h.2 u' (Multiset.mem_toFinset.mpr hu')⟩

/-- The greedy choice as a function: `r` rows, each an argmin over `E`. -/
noncomputable def greedyRows {ℓ : ℕ} (E : Multiset (Vec ℓ)) (f : List (Vec ℓ) → ℝ) :
    ℕ → List (Vec ℓ)
  | 0 => []
  | r + 1 => argminOn E (fun u => f (u :: greedyRows E f r)) :: greedyRows E f r

theorem greedyRows_length {ℓ : ℕ} (E : Multiset (Vec ℓ)) (f : List (Vec ℓ) → ℝ) (r : ℕ) :
    (greedyRows E f r).length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp [greedyRows, ih]

theorem isGreedy_greedyRows {ℓ : ℕ} (E : Multiset (Vec ℓ)) (hE : E ≠ 0)
    (f : List (Vec ℓ) → ℝ) (r : ℕ) : IsGreedy E f (greedyRows E f r) := by
  induction r with
  | zero => trivial
  | succ r ih =>
    exact ⟨ih, (argminOn_spec E hE (fun u => f (u :: greedyRows E f r))).1,
      (argminOn_spec E hE (fun u => f (u :: greedyRows E f r))).2⟩

private lemma surv_cons {ℓ : ℕ} {ι : Type*} (s : Finset ι) (v : ι → Vec ℓ) (ω : ι → ℝ)
    (u : Vec ℓ) (rows : List (Vec ℓ)) :
    surv s v ω (u :: rows)
      = ∑ j ∈ s.filter (fun j => ∀ x ∈ rows, x ⬝ᵥ v j = 0) with u ⬝ᵥ v j = 0, ω j := by
  unfold surv
  rw [Finset.filter_filter]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext j
  simp [and_comm]

theorem greedy_bound {ℓ : ℕ} {ι : Type*} {ε : ℝ} {E : Multiset (Vec ℓ)}
    (hE : IsBiased ε E) (s : Finset ι) (v : ι → Vec ℓ) (ω : ι → ℝ)
    (hv : ∀ j ∈ s, v j ≠ 0) (hω : ∀ j ∈ s, 0 ≤ ω j)
    (rows : List (Vec ℓ)) (hg : IsGreedy E (surv s v ω) rows) :
    surv s v ω rows ≤ ((1 + ε) / 2) ^ rows.length * ∑ j ∈ s, ω j := by
  rcases s.eq_empty_or_nonempty with hs | ⟨j0, hj0⟩
  · subst hs
    simp [surv]
  -- `ε ≥ 0`, since some `v j` is nonzero
  have hε : 0 ≤ ε := by
    have h1 := hE.2 _ (hv j0 hj0)
    have hpos : (0 : ℝ) < E.card := by exact_mod_cast Multiset.card_pos.mpr hE.1
    have := le_trans (abs_nonneg _) h1
    exact nonneg_of_mul_nonneg_left this hpos
  have hc : 0 ≤ (1 + ε) / 2 := by linarith
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
      _ ≤ (1 + ε) / 2 * surv s v ω rows := hsel
      _ ≤ (1 + ε) / 2 * (((1 + ε) / 2) ^ rows.length * ∑ j ∈ s, ω j) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = ((1 + ε) / 2) ^ (u :: rows).length * ∑ j ∈ s, ω j := by
          rw [List.length_cons, pow_succ]; ring

theorem one_add_inv_pow_le_exp (r : ℕ) (hr : 0 < r) : (1 + 1 / (r : ℝ)) ^ r ≤ Real.exp 1 := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : 1 + 1 / (r : ℝ) ≤ Real.exp (1 / r) := by
    have := Real.add_one_le_exp (1 / (r : ℝ)); linarith
  have h0 : 0 ≤ 1 + 1 / (r : ℝ) := by positivity
  calc (1 + 1 / (r : ℝ)) ^ r ≤ Real.exp (1 / r) ^ r := pow_le_pow_left₀ h0 h1 r
    _ = Real.exp (r * (1 / r)) := (Real.exp_nat_mul _ _).symm
    _ = Real.exp 1 := by rw [mul_one_div_cancel hr']

theorem greedy_bound_exp {ℓ : ℕ} {ι : Type*} {ε : ℝ} {E : Multiset (Vec ℓ)}
    (hE : IsBiased ε E) (hε0 : 0 ≤ ε) (s : Finset ι) (v : ι → Vec ℓ) (ω : ι → ℝ)
    (hv : ∀ j ∈ s, v j ≠ 0) (hω : ∀ j ∈ s, 0 ≤ ω j)
    (rows : List (Vec ℓ)) (hg : IsGreedy E (surv s v ω) rows)
    (hr : 0 < rows.length) (hε : ε ≤ 1 / rows.length) :
    surv s v ω rows ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ rows.length * ∑ j ∈ s, ω j := by
  have hb := greedy_bound hE s v ω hv hω rows hg
  have hS : 0 ≤ ∑ j ∈ s, ω j := Finset.sum_nonneg hω
  set r := rows.length
  have hpow : ((1 + ε) / 2) ^ r ≤ Real.exp 1 * (2 : ℝ)⁻¹ ^ r := by
    rw [div_eq_mul_inv, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (1 + ε) ^ r ≤ (1 + 1 / (r : ℝ)) ^ r :=
          pow_le_pow_left₀ (by linarith) (by linarith) r
      _ ≤ Real.exp 1 := one_add_inv_pow_le_exp r hr
  exact le_trans hb (mul_le_mul_of_nonneg_right hpow hS)

end Xor

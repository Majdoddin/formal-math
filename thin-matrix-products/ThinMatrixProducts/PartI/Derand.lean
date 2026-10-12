import ThinMatrixProducts.PartI.HashCount

/-!
# Lemma 4.1, the method of conditional expectations

* The conditional count (`completions_eq`): with the columns fixed at the levels `F`, of which
  `r` lie in `S`, the completions whose columns at `S` are linearly independent number
  `2^{k · |F^c ∖ S|} ∏_{i=r}^{k-1} (2^k - 2^i)` if the `r` fixed columns at `S` are independent, and
  `0` otherwise. By induction on the free levels: a free level outside `S` takes any of `2^k`
  columns; a free level `x ∈ S` must avoid the span of the `r` fixed columns at `S`
  (`linearIndepOn_insert`), which has `2^r` elements. Divided by `2^{k |F^c|}` this is `μ_{k-r}`.
* The averaging step (`Lemma_4_1_mean`): the completions split by the column at a free level.
* The greedy choice (`Lemma_4_1_greedy`): `C_j ≤ 2^k C_{j+1}` for the conditional counts along the
  levels, so the final count is at least `C_0 / 2^{kL} = μ_k |𝒮|`.
-/

namespace ThinMatrixProducts

open Finset

variable {k L : ℕ}

/-- The completions split by the column at a free level `x`. -/
lemma completions_split (S F : Finset (Fin L)) (c : Fin L → Fin k → ZMod 2) (x : Fin L)
    (hx : x ∉ F) :
    completions S F c = ∑ v : Fin k → ZMod 2, completions S (insert x F) (Function.update c x v) := by
  classical
  unfold completions
  rw [card_eq_sum_card_fiberwise (f := fun d : Fin L → Fin k → ZMod 2 => d x) (t := univ)
    (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun v _ => ?_
  congr 1
  ext d
  simp only [mem_filter, mem_univ, true_and, mem_insert, forall_eq_or_imp]
  constructor
  · rintro ⟨⟨hF, hli⟩, hv⟩
    refine ⟨⟨by rw [hv, Function.update_self], fun ℓ hℓ => ?_⟩, hli⟩
    rw [Function.update_of_ne (fun h : ℓ = x => hx (h ▸ hℓ))]; exact hF ℓ hℓ
  · rintro ⟨⟨hv, hF⟩, hli⟩
    refine ⟨⟨fun ℓ hℓ => ?_, hli⟩, by rw [hv, Function.update_self]⟩
    have := hF ℓ hℓ
    rwa [Function.update_of_ne (fun h : ℓ = x => hx (h ▸ hℓ))] at this

theorem lemma_4_1_mean : Lemma_4_1_mean := by
  intro k L 𝒮 F c x hx
  unfold condCount
  rw [sum_comm]
  exact sum_congr rfl fun S _ => completions_split S F c x hx

/-- Linear independence at `insert x T` (as a family indexed by the finite set). -/
lemma li_insert_iff (T : Finset (Fin L)) (x : Fin L) (hx : x ∉ T) (d : Fin L → Fin k → ZMod 2) :
    LinearIndependent (ZMod 2) (fun ℓ : (insert x T : Finset (Fin L)) => d ℓ)
      ↔ LinearIndependent (ZMod 2) (fun ℓ : T => d ℓ)
        ∧ d x ∉ Submodule.span (ZMod 2) (Set.range fun ℓ : T => d ℓ) := by
  show LinearIndepOn (ZMod 2) d ↑(insert x T) ↔ LinearIndepOn (ZMod 2) d ↑T ∧ _
  rw [Finset.coe_insert, linearIndepOn_insert (by simpa using hx), Set.image_eq_range]
  exact Iff.rfl

open Classical in
/-- The vectors outside the span of `r` independent vectors of `F₂^k` number `2^k - 2^r`. -/
lemma card_not_mem_span (T : Finset (Fin L)) (c : Fin L → Fin k → ZMod 2)
    (hli : LinearIndependent (ZMod 2) (fun ℓ : T => c ℓ)) :
    (univ.filter fun v : Fin k → ZMod 2 =>
        v ∉ Submodule.span (ZMod 2) (Set.range fun ℓ : T => c ℓ)).card = 2 ^ k - 2 ^ T.card := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := Submodule.span (ZMod 2) (Set.range fun ℓ : T => c ℓ)
  have hW : (univ.filter fun v : Fin k → ZMod 2 => v ∈ W).card = 2 ^ T.card := by
    rw [← Fintype.card_subtype]
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
    rw [finrank_span_eq_card hli, ZMod.card, Fintype.card_coe] at h1
    rw [← h1]
    try exact Fintype.card_congr (Equiv.refl _)
  rw [filter_not, card_sdiff_of_subset (filter_subset _ _), hW, card_univ, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]

open Classical in
/-- The conditional count, in integers. -/
lemma completions_eq (S : Finset (Fin L)) (hS : S.card = k) :
    ∀ (n : ℕ) (F : Finset (Fin L)) (c : Fin L → Fin k → ZMod 2), Fᶜ.card = n →
      completions S F c
        = if LinearIndependent (ZMod 2) (fun ℓ : (S ∩ F : Finset (Fin L)) => c ℓ)
          then 2 ^ (k * (Fᶜ \ S).card) * ∏ i ∈ Ico (S ∩ F).card k, (2 ^ k - 2 ^ i) else 0 := by
  classical
  intro n
  induction n with
  | zero =>
    intro F c hF
    have hFu : F = univ := by
      rw [card_eq_zero, compl_eq_empty_iff] at hF; exact hF
    subst hFu
    rw [inter_univ, compl_univ, empty_sdiff, card_empty, mul_zero, pow_zero, one_mul, hS,
      Ico_self, prod_empty]
    unfold completions
    split_ifs with h
    · rw [card_eq_one]
      refine ⟨c, ?_⟩
      ext d
      simp only [mem_filter, mem_univ, true_and, mem_singleton, forall_const]
      constructor
      · rintro ⟨hd, -⟩; exact funext hd
      · rintro rfl; exact ⟨fun _ => rfl, h⟩
    · rw [card_eq_zero, filter_eq_empty_iff]
      rintro d - ⟨hd, hli⟩
      apply h
      have : d = c := funext fun ℓ => hd ℓ (mem_univ ℓ)
      rwa [this] at hli
  | succ n ih =>
    intro F c hF
    obtain ⟨x, hxF⟩ := card_pos.1 (by omega : 0 < Fᶜ.card)
    have hx : x ∉ F := mem_compl.1 hxF
    have hcard : (insert x F)ᶜ.card = n := by
      rw [compl_insert, card_erase_of_mem hxF, hF]; rfl
    rw [completions_split S F c x hx]
    simp only [ih (insert x F) _ hcard]
    by_cases hxS : x ∈ S
    · -- a free level of `S`: the new column must avoid the span of the fixed ones
      have hxSF : x ∉ S ∩ F := fun h => hx (mem_inter.1 h).2
      have e1 : S ∩ insert x F = insert x (S ∩ F) := inter_insert_of_mem hxS
      have e2 : (insert x F)ᶜ \ S = Fᶜ \ S := by
        ext ℓ; simp only [mem_sdiff, mem_compl, mem_insert, not_or]
        constructor
        · rintro ⟨⟨-, h⟩, h'⟩; exact ⟨h, h'⟩
        · rintro ⟨h, h'⟩; exact ⟨⟨fun e => h' (e ▸ hxS), h⟩, h'⟩
      have hr : (S ∩ F).card < k := by
        rw [← hS]
        exact card_lt_card ⟨inter_subset_left, fun h => hxSF (h hxS)⟩
      have hLI : ∀ v : Fin k → ZMod 2,
          LinearIndependent (ZMod 2)
              (fun ℓ : (S ∩ insert x F : Finset (Fin L)) => Function.update c x v ℓ)
            ↔ LinearIndependent (ZMod 2) (fun ℓ : (S ∩ F : Finset (Fin L)) => c ℓ)
              ∧ v ∉ Submodule.span (ZMod 2)
                (Set.range fun ℓ : (S ∩ F : Finset (Fin L)) => c ℓ) := by
        intro v
        rw [e1, li_insert_iff (S ∩ F) x hxSF, Function.update_self]
        have : (fun ℓ : (S ∩ F : Finset (Fin L)) => Function.update c x v ℓ)
            = fun ℓ : (S ∩ F : Finset (Fin L)) => c ℓ := by
          funext ℓ
          exact Function.update_of_ne (fun h : (ℓ : Fin L) = x => hxSF (h ▸ ℓ.2)) v c
        rw [this]
      simp only [hLI]
      simp only [e1, e2, card_insert_of_notMem hxSF]
      by_cases hli : LinearIndependent (ZMod 2) (fun ℓ : (S ∩ F : Finset (Fin L)) => c ℓ)
      · simp only [hli, true_and, if_true]
        rw [← sum_filter, sum_const, card_not_mem_span (S ∩ F) c hli, smul_eq_mul,
          prod_eq_prod_Ico_succ_bot hr]
        ring
      · simp [hli]
    · -- a free level outside `S`: any column
      have e1 : S ∩ insert x F = S ∩ F := inter_insert_of_notMem hxS
      have hxc : x ∈ Fᶜ \ S := mem_sdiff.2 ⟨hxF, hxS⟩
      have e2 : ((insert x F)ᶜ \ S).card + 1 = (Fᶜ \ S).card := by
        rw [compl_insert, erase_sdiff_comm, card_erase_of_mem hxc]
        have := card_pos.2 ⟨x, hxc⟩
        omega
      have hLI : ∀ v : Fin k → ZMod 2,
          LinearIndependent (ZMod 2)
              (fun ℓ : (S ∩ insert x F : Finset (Fin L)) => Function.update c x v ℓ)
            ↔ LinearIndependent (ZMod 2) (fun ℓ : (S ∩ F : Finset (Fin L)) => c ℓ) := by
        intro v
        rw [e1]
        have : (fun ℓ : (S ∩ F : Finset (Fin L)) => Function.update c x v ℓ)
            = fun ℓ : (S ∩ F : Finset (Fin L)) => c ℓ := by
          funext ℓ
          exact Function.update_of_ne
            (fun h : (ℓ : Fin L) = x => hxS (h ▸ (mem_inter.1 ℓ.2).1)) v c
        rw [this]
      simp only [hLI]
      simp only [e1, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card,
        smul_eq_mul]
      rw [← e2]
      split_ifs
      · rw [mul_add, mul_one, pow_add]; ring
      · simp

/-- `∏_{i=r}^{k-1} (2^k - 2^i) = 2^{k(k-r)} μ_{k-r}`. -/
lemma prod_Ico_eq_mu (r : ℕ) (hr : r ≤ k) :
    (∏ i ∈ Ico r k, ((2 : ℝ) ^ k - 2 ^ i)) = 2 ^ (k * (k - r)) * mu (k - r) := by
  have h := prod_two_pow_sub (k - r)
  rw [Fin.prod_univ_eq_prod_range (fun i => (2 : ℝ) ^ (k - r) - 2 ^ i) (k - r)] at h
  have e : ∀ j : ℕ, (2 : ℝ) ^ k - 2 ^ (r + j) = 2 ^ r * (2 ^ (k - r) - 2 ^ j) := by
    intro j
    rw [mul_sub, ← pow_add, ← pow_add, Nat.add_sub_cancel' hr]
  rw [prod_Ico_eq_prod_range, prod_congr rfl (fun j _ => e j), prod_mul_distrib, prod_const,
    card_range, h, ← mul_assoc, ← pow_mul, ← pow_add]
  congr 2
  rw [sq, ← add_mul, Nat.add_sub_cancel' hr]

theorem lemma_4_1_condprob : Lemma_4_1_condprob := by
  intro k L S F c hS
  rw [completions_eq S hS _ F c rfl]
  have hr : (S ∩ F).card ≤ k := hS ▸ card_le_card inter_subset_left
  have hsplit : Fᶜ.card = (Fᶜ \ S).card + (k - (S ∩ F).card) := by
    have h1 : (Fᶜ ∩ S).card + (Fᶜ \ S).card = Fᶜ.card := card_inter_add_card_sdiff _ _
    have h2 : (S ∩ F).card + (S \ F).card = S.card := card_inter_add_card_sdiff _ _
    have h3 : Fᶜ ∩ S = S \ F := by ext; simp [and_comm]
    rw [h3] at h1
    omega
  split_ifs with h
  · push_cast
    have : ∀ i ∈ Ico (S ∩ F).card k, (((2 ^ k - 2 ^ i : ℕ)) : ℝ) = (2 : ℝ) ^ k - 2 ^ i := by
      intro i hi
      rw [Nat.cast_sub (Nat.pow_le_pow_right (by norm_num) (mem_Ico.1 hi).2.le)]
      push_cast; rfl
    rw [prod_congr rfl this, prod_Ico_eq_mu _ hr, hsplit, mul_add, pow_add]
    field_simp
  · simp

theorem lemma_4_1_greedy : Lemma_4_1_greedy := by
  intro k L 𝒮 h𝒮
  classical
  -- `condCount` depends only on the fixed columns
  have hcongr : ∀ (F : Finset (Fin L)) (c c' : Fin L → Fin k → ZMod 2),
      (∀ ℓ ∈ F, c ℓ = c' ℓ) → condCount 𝒮 F c = condCount 𝒮 F c' := by
    intro F c c' h
    unfold condCount completions
    refine sum_congr rfl fun S _ => ?_
    congr 1
    ext d
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hd, hli⟩; exact ⟨fun ℓ hℓ => (hd ℓ hℓ).trans (h ℓ hℓ), hli⟩
    · rintro ⟨hd, hli⟩; exact ⟨fun ℓ hℓ => (hd ℓ hℓ).trans (h ℓ hℓ).symm, hli⟩
  have hbelow : ∀ j (hj : j < L), insert (⟨j, hj⟩ : Fin L) (below j) = below (j + 1) := by
    intro j hj; ext ℓ
    simp only [below, mem_insert, mem_filter, mem_univ, true_and, Fin.ext_iff]
    omega
  have hnot : ∀ j (hj : j < L), (⟨j, hj⟩ : Fin L) ∉ below j := by
    intro j hj; simp [below]
  refine ⟨?_, fun M hM => ?_⟩
  · -- a greedy matrix exists: choose the maximising column level by level
    have build : ∀ j ≤ L, ∃ c : Fin L → Fin k → ZMod 2, ∀ ℓ : Fin L, (ℓ : ℕ) < j →
        ∀ v, condCount 𝒮 (below ((ℓ : ℕ) + 1)) (Function.update c ℓ v)
          ≤ condCount 𝒮 (below ((ℓ : ℕ) + 1)) c := by
      intro j
      induction j with
      | zero => intro _; exact ⟨fun _ _ => 0, fun ℓ h => absurd h (Nat.not_lt_zero _)⟩
      | succ j ih =>
        intro hj
        obtain ⟨c, hc⟩ := ih (by omega)
        set x : Fin L := ⟨j, by omega⟩
        obtain ⟨v₀, -, hv₀⟩ := Finset.exists_max_image univ
          (fun v => condCount 𝒮 (below (j + 1)) (Function.update c x v)) univ_nonempty
        refine ⟨Function.update c x v₀, fun ℓ hℓ v => ?_⟩
        by_cases hℓx : (ℓ : ℕ) < j
        · have hagree : ∀ c₁ : Fin L → Fin k → ZMod 2,
              ∀ ℓ' ∈ below ((ℓ : ℕ) + 1), Function.update c₁ x v₀ ℓ' = c₁ ℓ' := by
            intro c₁ ℓ' hℓ'
            apply Function.update_of_ne
            intro e
            simp only [below, mem_filter, mem_univ, true_and] at hℓ'
            rw [e] at hℓ'
            simp [x] at hℓ'
            omega
          have e1 := hcongr _ _ _ (hagree c)
          have e2 : condCount 𝒮 (below ((ℓ : ℕ) + 1))
              (Function.update (Function.update c x v₀) ℓ v)
              = condCount 𝒮 (below ((ℓ : ℕ) + 1)) (Function.update c ℓ v) := by
            apply hcongr
            intro ℓ' hℓ'
            by_cases h : ℓ' = ℓ
            · subst h; simp
            · rw [Function.update_of_ne h, Function.update_of_ne h]
              exact hagree c ℓ' hℓ'
          rw [e1, e2]
          exact hc ℓ hℓx v
        · have hℓeq : ℓ = x := Fin.ext (by simp [x]; omega)
          subst hℓeq
          rw [Function.update_idem]
          exact hv₀ v (mem_univ v)
    obtain ⟨c, hc⟩ := build L le_rfl
    exact ⟨Matrix.of fun i ℓ => c ℓ i, fun ℓ v => hc ℓ ℓ.2 v⟩
  · -- the telescoping `C_j ≤ 2^k C_{j+1}`
    set cM : Fin L → Fin k → ZMod 2 := fun ℓ i => M i ℓ with hcM
    have hstep : ∀ j (hj : j < L),
        condCount 𝒮 (below j) cM ≤ 2 ^ k * condCount 𝒮 (below (j + 1)) cM := by
      intro j hj
      rw [lemma_4_1_mean 𝒮 (below j) cM ⟨j, hj⟩ (hnot j hj), hbelow j hj]
      calc ∑ v : Fin k → ZMod 2, condCount 𝒮 (below (j + 1)) (Function.update cM ⟨j, hj⟩ v)
          ≤ ∑ _v : Fin k → ZMod 2, condCount 𝒮 (below (j + 1)) cM :=
            sum_le_sum fun v _ => hM ⟨j, hj⟩ v
        _ = 2 ^ k * condCount 𝒮 (below (j + 1)) cM := by
            rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, smul_eq_mul]
    have htel : ∀ j ≤ L, condCount 𝒮 (below 0) cM ≤ 2 ^ (k * j) * condCount 𝒮 (below j) cM := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        calc condCount 𝒮 (below 0) cM ≤ 2 ^ (k * j) * condCount 𝒮 (below j) cM := ih (by omega)
          _ ≤ 2 ^ (k * j) * (2 ^ k * condCount 𝒮 (below (j + 1)) cM) :=
              Nat.mul_le_mul_left _ (hstep j (by omega))
          _ = 2 ^ (k * (j + 1)) * condCount 𝒮 (below (j + 1)) cM := by ring
    have h0 : below 0 = (∅ : Finset (Fin L)) := by ext; simp [below]
    have hL : below L = (univ : Finset (Fin L)) := by ext ℓ; simp [below, ℓ.2]
    -- `C_0 = |𝒮| 2^{kL} μ_k`
    have hC0 : (condCount 𝒮 (below 0) cM : ℝ) = 𝒮.card * (2 ^ (k * L) * mu k) := by
      rw [h0, condCount, Nat.cast_sum, ← nsmul_eq_mul, ← sum_const]
      refine sum_congr rfl fun S hS => ?_
      have := lemma_4_1_condprob S ∅ cM (h𝒮 S hS)
      rw [inter_empty, compl_empty, card_univ, Fintype.card_fin, card_empty, Nat.sub_zero] at this
      have hli : LinearIndependent (ZMod 2) (fun ℓ : (∅ : Finset (Fin L)) => cM ℓ) :=
        linearIndependent_empty_type
      rw [if_pos hli, div_eq_iff (by positivity)] at this
      rw [this]; ring
    -- `C_L` is the number of sets of `𝒮` at which `M` is invertible
    have hCL : condCount 𝒮 (below L) cM
        = (𝒮.filter fun S : Finset (Fin L) =>
            LinearIndependent (ZMod 2) (fun ℓ : S => fun i => M i ℓ.1)).card := by
      rw [hL, condCount, card_filter]
      refine sum_congr rfl fun S hS => ?_
      rw [completions_eq S (h𝒮 S hS) 0 univ cM (by simp), inter_univ]
      simp only [compl_univ, empty_sdiff, card_empty, mul_zero, pow_zero, one_mul, h𝒮 S hS,
        Ico_self, prod_empty]
      rfl
    have h := htel L le_rfl
    have h' : (condCount 𝒮 (below 0) cM : ℝ) ≤ 2 ^ (k * L) * condCount 𝒮 (below L) cM := by
      exact_mod_cast h
    rw [hC0, hCL] at h'
    have hpos : (0 : ℝ) < 2 ^ (k * L) := by positivity
    nlinarith

theorem lemma_4_1_derand : Lemma_4_1_derand := by
  intro L m hmL
  have hG := @lemma_4_1_greedy m L (univ.powersetCard m) (fun S hS => (mem_powersetCard.1 hS).2)
  refine ⟨hG.1, fun Γ hΓ => ?_⟩
  classical
  set 𝒢Γ := (univ.powersetCard m).filter fun Q : Finset (Fin L) =>
    LinearIndependent (ZMod 2) (fun ℓ : Q => fun i => Γ i ℓ.1) with h𝒢Γ
  have hΓc := hG.2 Γ hΓ
  rw [card_powersetCard, card_univ, Fintype.card_fin] at hΓc
  have hcomp : ∀ S ∈ 𝒢Γ.image compl, S.card = L - m := by
    intro S hS
    obtain ⟨Q, hQ, rfl⟩ := mem_image.1 hS
    rw [card_compl, Fintype.card_fin, (mem_powersetCard.1 (mem_filter.1 hQ).1).2]
  have hD := @lemma_4_1_greedy (L - m) L (𝒢Γ.image compl) hcomp
  refine ⟨hD.1, fun Δ hΔ => ?_⟩
  have hΔc := hD.2 Δ hΔ
  rw [card_image_of_injective _ compl_injective] at hΔc
  -- the good sets are the sets of `𝒢Γ` at whose complement `Δ` is invertible
  have hgood : ((𝒢Γ.image compl).filter fun S : Finset (Fin L) =>
      LinearIndependent (ZMod 2) (fun ℓ : S => fun i => Δ i ℓ.1)).card
      = ((univ.powersetCard m).filter (Good Γ Δ)).card := by
    rw [filter_image, card_image_of_injective _ compl_injective, h𝒢Γ, filter_filter]
    congr 1
    refine filter_congr fun Q hQ => ?_
    simp only [Function.comp, Good, (mem_powersetCard.1 hQ).2, true_and]
  rw [hgood] at hΔc
  calc mu m * mu (L - m) * (L.choose m : ℝ) = mu (L - m) * (mu m * L.choose m) := by ring
    _ ≤ mu (L - m) * 𝒢Γ.card := by
        apply mul_le_mul_of_nonneg_left hΓc
        have := mu_pos (L - m); linarith
    _ ≤ _ := hΔc

end ThinMatrixProducts

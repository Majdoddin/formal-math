import ThinMatrixProducts.Appendix.FullProductSubst
/-! # Thin full products: Lemma 4 (forest cap) and its averaged form

Leaf peeling. Let `F` be a forest and `e = (i, c) ∈ F` alone in its column `c` (the row case is
symmetric). The slices of `⟨o₁,b,o₂⟩|_F` along `y_{1c}, …, y_{bc}` are `x_{ij} ⊗ z_e`, so the
restrictions of the `v_l` to these `b` coordinates span `K^b`, and `fp_subst` kills `b` terms by a
linear map `π` on the right factor that fixes every vector without `y_{·c}`-part. For an output
`z ∈ F - e` the slice `T(a, ·, z)` has no `y_{·c}`-part (`z` is not in column `c`), so the new
family is a decomposition of `⟨o₁,b,o₂⟩|_{F - e}`. Induction on `|F|`.

Averaging (the hint of the task). Instead of a uniformly random spanning tree of `K_{o₁,o₂}` we
average over the `n` double stars `fpStar r s` (row `r` plus column `s`), which are the translates
of one spanning tree under the cyclic shifts of rows and columns. Each has `d = o₁ + o₂ - 1`
outputs, and each output lies in exactly `d` of them. Summing Lemma 4 over the double stars:
`b d n ≤ ∑_l #{stars meeting S_l} ≤ ∑_l min(n, d |S_l|)`; dividing by `d` gives
`∑_l min(|S_l|, n/d) ≥ b n`, the same inequality as with random spanning trees. -/
namespace ThinMatrixProducts

open Finset

section FullProductForest

variable {K : Type} [Field K]

lemma fp_forest_subset {o₁ o₂ : ℕ} {F F' : Finset (Fin o₁ × Fin o₂)} (h : fpForest F)
    (hF : F' ⊆ F) : fpForest F' := fun G hG hne => h G (hG.trans hF) hne

open scoped Classical in
/-- Leaf peeling, for families indexed by any finite type that decompose `⟨o₁,b,o₂⟩|_F`. -/
lemma fp_forest_aux {o₁ b o₂ : ℕ} : ∀ (n : ℕ) (F : Finset (Fin o₁ × Fin o₂)), F.card = n →
    fpForest F → ∀ (ι : Type) [Fintype ι] (u : ι → Fin o₁ × Fin b → K)
    (v : ι → Fin b × Fin o₂ → K) (w : ι → Fin o₁ × Fin o₂ → K),
    (∀ a y, ∀ z ∈ F, ∑ l, u l a * v l y * w l z = mmTensor K o₁ b o₂ a y z) →
    b * F.card ≤ Fintype.card ι := by
  intro n
  induction n with
  | zero => intro F hF _ ι _ u v w _; simp [hF]
  | succ n ih =>
    intro F hF hfor ι _ u v w hd
    have hne : F.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨e, he, hleaf⟩ := hfor F subset_rfl hne
    set F' := F.erase e
    have hF' : F'.card = n := by rw [Finset.card_erase_of_mem he]; omega
    have hfor' : fpForest F' := fp_forest_subset hfor (Finset.erase_subset e F)
    rcases hleaf with hrow | hcol
    · -- `e` alone in its row: substitute the left variables `x_{e.1, ·}`
      set X₀ : Finset (Fin o₁ × Fin b) := univ.filter fun a => a.1 = e.1
      have hX₀ : X₀.card = b := by
        rw [show X₀ = ({e.1} : Finset (Fin o₁)) ×ˢ (univ : Finset (Fin b)) by
          ext ⟨i, j⟩; simp only [X₀, mem_filter, mem_univ, true_and, mem_product, mem_singleton,
            and_true]]
        simp
      have hspan : ∀ a₀ ∈ X₀, ∃ g : ι → K, ∀ a ∈ X₀,
          ∑ l, g l * u l a = if a = a₀ then 1 else 0 := by
        intro a₀ ha₀
        refine ⟨fun l => v l (a₀.2, e.2) * w l e, fun a ha => ?_⟩
        simp only [X₀, Finset.mem_filter, Finset.mem_univ, true_and] at ha ha₀
        rw [show (∑ l, v l (a₀.2, e.2) * w l e * u l a)
            = ∑ l, u l a * v l (a₀.2, e.2) * w l e from
            Finset.sum_congr rfl fun l _ => by ring, hd a _ e he]
        simp only [mmTensor, ha, true_and, and_true]
        by_cases h2 : a.2 = a₀.2
        · simp [h2, Prod.ext_iff, ha, ha₀]
        · simp [h2, Prod.ext_iff]
      obtain ⟨S, hS, π, hπS, hπfix⟩ := fp_subst X₀ u hspan
      have hd' : ∀ a y, ∀ z ∈ F', ∑ l : {l // l ∉ S}, π (u l) a * v l y * w l z
          = mmTensor K o₁ b o₂ a y z := by
        intro a y z hz
        have hzF : z ∈ F := Finset.mem_of_mem_erase hz
        have hze : z ≠ e := Finset.ne_of_mem_erase hz
        rw [fp_sum_subtype (fun l => l ∉ S) (fun l => π (u l) a * v l y * w l z)
          fun l hl => by rw [hπS l (not_not.1 hl)]; simp]
        set T : Fin o₁ × Fin b → K := fun a' => mmTensor K o₁ b o₂ a' y z
        have hT : T = ∑ l, (v l y * w l z) • u l := by
          funext a'
          rw [Finset.sum_apply]
          simp only [T, Pi.smul_apply, smul_eq_mul, ← hd a' y z hzF]
          exact Finset.sum_congr rfl fun l _ => by ring
        have hπT : π T = T := by
          refine hπfix T fun a' ha' => ?_
          simp only [X₀, Finset.mem_filter, Finset.mem_univ, true_and] at ha'
          simp only [T, mmTensor]
          rw [if_neg]
          rintro ⟨h1, -, -⟩
          exact hze (hrow z hzF (h1.symm.trans ha'))
        have := congrFun hπT a
        rw [hT, map_sum] at this
        simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        rw [show (∑ l, π (u l) a * v l y * w l z) = ∑ l, v l y * w l z * π (u l) a from
          Finset.sum_congr rfl fun l _ => by ring, this]
        rw [show (∑ l, v l y * w l z * u l a) = ∑ l, u l a * v l y * w l z from
          Finset.sum_congr rfl fun l _ => by ring, hd a y z hzF]
      have h := ih F' hF' hfor' {l // l ∉ S} (fun l => π (u l)) (fun l => v l) (fun l => w l) hd'
      rw [Fintype.card_subtype_compl, Fintype.card_coe, hS, hX₀, hF'] at h
      have hSle : b ≤ Fintype.card ι := by rw [← hX₀, ← hS]; exact Finset.card_le_univ S
      rw [hF, Nat.mul_succ]
      omega
    · -- `e` alone in its column: substitute the right variables `y_{·, e.2}`
      set Y₀ : Finset (Fin b × Fin o₂) := univ.filter fun y => y.2 = e.2
      have hY₀ : Y₀.card = b := by
        rw [show Y₀ = (univ : Finset (Fin b)) ×ˢ ({e.2} : Finset (Fin o₂)) by
          ext ⟨j, c⟩; simp only [Y₀, mem_filter, mem_univ, true_and, mem_product, mem_singleton]]
        simp
      have hspan : ∀ y₀ ∈ Y₀, ∃ g : ι → K, ∀ y ∈ Y₀,
          ∑ l, g l * v l y = if y = y₀ then 1 else 0 := by
        intro y₀ hy₀
        refine ⟨fun l => u l (e.1, y₀.1) * w l e, fun y hy => ?_⟩
        simp only [Y₀, Finset.mem_filter, Finset.mem_univ, true_and] at hy hy₀
        rw [show (∑ l, u l (e.1, y₀.1) * w l e * v l y)
            = ∑ l, u l (e.1, y₀.1) * v l y * w l e from
            Finset.sum_congr rfl fun l _ => by ring, hd _ y e he]
        simp only [mmTensor, hy, true_and, and_true]
        by_cases h2 : y₀.1 = y.1
        · simp [h2, Prod.ext_iff, hy, hy₀]
        · simp [h2, Prod.ext_iff, Ne.symm h2]
      obtain ⟨S, hS, π, hπS, hπfix⟩ := fp_subst Y₀ v hspan
      have hd' : ∀ a y, ∀ z ∈ F', ∑ l : {l // l ∉ S}, u l a * π (v l) y * w l z
          = mmTensor K o₁ b o₂ a y z := by
        intro a y z hz
        have hzF : z ∈ F := Finset.mem_of_mem_erase hz
        have hze : z ≠ e := Finset.ne_of_mem_erase hz
        rw [fp_sum_subtype (fun l => l ∉ S) (fun l => u l a * π (v l) y * w l z)
          fun l hl => by rw [hπS l (not_not.1 hl)]; simp]
        set T : Fin b × Fin o₂ → K := fun y' => mmTensor K o₁ b o₂ a y' z
        have hT : T = ∑ l, (u l a * w l z) • v l := by
          funext y'
          rw [Finset.sum_apply]
          simp only [T, Pi.smul_apply, smul_eq_mul, ← hd a y' z hzF]
          exact Finset.sum_congr rfl fun l _ => by ring
        have hπT : π T = T := by
          refine hπfix T fun y' hy' => ?_
          simp only [Y₀, Finset.mem_filter, Finset.mem_univ, true_and] at hy'
          simp only [T, mmTensor]
          rw [if_neg]
          rintro ⟨-, -, h3⟩
          exact hze (hcol z hzF (h3.symm.trans hy'))
        have := congrFun hπT y
        rw [hT, map_sum] at this
        simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        rw [show (∑ l, u l a * π (v l) y * w l z) = ∑ l, u l a * w l z * π (v l) y from
          Finset.sum_congr rfl fun l _ => by ring, this]
        rw [show (∑ l, u l a * w l z * v l y) = ∑ l, u l a * v l y * w l z from
          Finset.sum_congr rfl fun l _ => by ring, hd a y z hzF]
      have h := ih F' hF' hfor' {l // l ∉ S} (fun l => u l) (fun l => π (v l)) (fun l => w l) hd'
      rw [Fintype.card_subtype_compl, Fintype.card_coe, hS, hY₀, hF'] at h
      have hSle : b ≤ Fintype.card ι := by rw [← hY₀, ← hS]; exact Finset.card_le_univ S
      rw [hF, Nat.mul_succ]
      omega

theorem fp_Lemma_4 : FP_Lemma_4 := by
  classical
  intro K _ o₁ b o₂ R u v w hd F hF
  have h := fp_forest_aux F.card F rfl hF {l // ∃ z ∈ F, w l z ≠ 0}
    (fun l => u l) (fun l => v l) (fun l => w l) (fun a y z hz => by
      rw [← hd a y z]
      exact fp_sum_subtype (fun l => ∃ z ∈ F, w l z ≠ 0) (fun l => u l a * v l y * w l z)
        fun l hl => by
          push Not at hl
          rw [hl z hz]; simp)
  rwa [Fintype.card_subtype] at h

/-- The double star has `o₁ + o₂ - 1` outputs. -/
lemma fp_star_card {o₁ o₂ : ℕ} (r : Fin o₁) (s : Fin o₂) : (fpStar r s).card = o₁ + o₂ - 1 := by
  classical
  have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin o₁ × Fin o₂)))
    (fun z => z.1 = r ∨ z.2 = s)
  have h2 : (univ.filter fun z : Fin o₁ × Fin o₂ => ¬ (z.1 = r ∨ z.2 = s))
      = (univ.erase r) ×ˢ (univ.erase s) := by
    ext ⟨i, c⟩; simp
  rw [h2, Finset.card_product, Finset.card_erase_of_mem (mem_univ _),
    Finset.card_erase_of_mem (mem_univ _), card_univ, card_univ, card_univ, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin] at h1
  have ho₁ : 0 < o₁ := Fin.pos r
  have ho₂ : 0 < o₂ := Fin.pos s
  obtain ⟨a, rfl⟩ : ∃ a, o₁ = a + 1 := ⟨o₁ - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, o₂ = c + 1 := ⟨o₂ - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1
  rw [show (a + 1) * (c + 1) = a * c + a + c + 1 by ring] at h1
  unfold fpStar
  generalize a * c = m at h1
  omega

theorem fp_star : FP_star := by
  classical
  intro o₁ o₂
  refine ⟨fun r s => ⟨?_, fp_star_card r s⟩, fun z => ?_⟩
  · intro G hG hne
    by_cases h : ∃ e ∈ G, e.1 ≠ r
    · obtain ⟨e, he, her⟩ := h
      have hes : e.2 = s := by
        have := hG he; simp [fpStar] at this; tauto
      refine ⟨e, he, Or.inl fun e' he' h1 => ?_⟩
      have : e'.2 = s := by
        have := hG he'; simp [fpStar] at this; rcases this with h | h
        · exact absurd (h1.symm.trans h) her
        · exact h
      exact Prod.ext h1 (this.trans hes.symm)
    · push Not at h
      obtain ⟨e, he⟩ := hne
      exact ⟨e, he, Or.inr fun e' he' h2 => Prod.ext ((h e' he').trans (h e he).symm) h2⟩
  · rw [← fp_star_card z.1 z.2]
    congr 1
    ext q
    simp [fpStar, eq_comm]

theorem fp_Lemma_4_avg : FP_Lemma_4_avg := by
  classical
  intro K _ o₁ b o₂ R u v w hd
  rcases Nat.eq_zero_or_pos o₁ with h₁ | h₁
  · subst h₁
    simp only [Nat.cast_zero, zero_mul, mul_zero, fpMstar, zero_div]
    exact Finset.sum_nonneg fun l _ => le_min (Nat.cast_nonneg _) le_rfl
  rcases Nat.eq_zero_or_pos o₂ with h₂ | h₂
  · subst h₂
    simp only [Nat.cast_zero, mul_zero, fpMstar, zero_div]
    exact Finset.sum_nonneg fun l _ => le_min (Nat.cast_nonneg _) le_rfl
  set d := o₁ + o₂ - 1 with hd_def
  have hdpos : 0 < d := by omega
  -- Lemma 4 on every double star, summed
  have hstar : ∀ q : Fin o₁ × Fin o₂,
      b * d ≤ (univ.filter fun l => ∃ z ∈ fpStar q.1 q.2, w l z ≠ 0).card := by
    intro q
    have h := fp_Lemma_4 K o₁ b o₂ R u v w hd _ ((fp_star o₁ o₂).1 q.1 q.2).1
    rwa [fp_star_card, ← hd_def] at h
  have hper : ∀ l, (univ.filter fun q : Fin o₁ × Fin o₂ =>
      ∃ z ∈ fpStar q.1 q.2, w l z ≠ 0).card ≤ min (o₁ * o₂) ((outSupp (w l)).card * d) := by
    intro l
    refine le_min ((Finset.card_le_univ _).trans (by simp)) ?_
    calc _ ≤ ((outSupp (w l)).biUnion fun z =>
          univ.filter fun q : Fin o₁ × Fin o₂ => z ∈ fpStar q.1 q.2).card := by
          refine Finset.card_le_card fun q hq => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          obtain ⟨z, hz, hw⟩ := hq
          exact Finset.mem_biUnion.2 ⟨z, by simp [outSupp, hw], by simp [hz]⟩
      _ ≤ ∑ z ∈ outSupp (w l), (univ.filter fun q : Fin o₁ × Fin o₂ =>
          z ∈ fpStar q.1 q.2).card := Finset.card_biUnion_le
      _ = (outSupp (w l)).card * d := by
          rw [Finset.sum_congr rfl fun z _ => ((fp_star o₁ o₂).2 z).trans hd_def.symm]; simp
  have hnat : b * d * (o₁ * o₂) ≤ ∑ l, min (o₁ * o₂) ((outSupp (w l)).card * d) := by
    calc b * d * (o₁ * o₂) = ∑ _q : Fin o₁ × Fin o₂, b * d := by simp; ring
      _ ≤ ∑ q : Fin o₁ × Fin o₂, (univ.filter fun l => ∃ z ∈ fpStar q.1 q.2, w l z ≠ 0).card :=
          Finset.sum_le_sum fun q _ => hstar q
      _ = ∑ l, (univ.filter fun q : Fin o₁ × Fin o₂ => ∃ z ∈ fpStar q.1 q.2, w l z ≠ 0).card := by
          simp only [Finset.card_filter]; exact Finset.sum_comm
      _ ≤ _ := Finset.sum_le_sum fun l _ => hper l
  have hdR : (0 : ℝ) < d := by exact_mod_cast hdpos
  have hdR' : ((o₁ : ℝ) + o₂ - 1) = d := by
    rw [hd_def, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hreal : (b : ℝ) * d * ((o₁ : ℝ) * o₂)
      ≤ ∑ l, min ((o₁ : ℝ) * o₂) (((outSupp (w l)).card : ℝ) * d) := by
    exact_mod_cast hnat
  unfold fpMstar
  rw [hdR']
  have : ∀ l, min (((outSupp (w l)).card : ℝ)) ((o₁ : ℝ) * o₂ / d)
      = min ((o₁ : ℝ) * o₂) (((outSupp (w l)).card : ℝ) * d) / d := by
    intro l
    rw [eq_div_iff hdR.ne', min_mul_of_nonneg _ _ hdR.le, div_mul_cancel₀ _ hdR.ne', min_comm]
  rw [Finset.sum_congr rfl fun l _ => this l, ← Finset.sum_div, le_div_iff₀ hdR]
  linarith

end FullProductForest

end ThinMatrixProducts

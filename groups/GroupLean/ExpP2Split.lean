import GroupLean.ExpP2

/-!
# Theorem G (exponent `p²`): the top-level case split

The paper's Theorem 19.17 ("exponent p²"): "Step 1: light and heavy", Lemma 19.20 ("a light list"),
"Bucketing" of Case H, Lemma 19.23 ("three heavy lists"), "Total".

Every triple of `S₁ × S₂ × S₃` (hence every solution) lies in exactly one of the
`7 + (⌊log₂ n⌋ + 1)^3` sub-instances of `subInst` (`subInst_length`, `subInst_partition`,
`exists_sol_iff_subInst`), and each sub-instance satisfies the hypothesis of Case L
(`T_I ≤ σ n²`) or the data of Case H (`subInst_cases`); in Case H, `T_I ≤ 2 s_min n²`
(`TI_le_of_caseH`).
-/

set_option linter.unusedSectionVars false

namespace GroupLean
namespace ExpP2Split

open Finset ExpP2

variable {p : ℕ} [hp : Fact p.Prime] {d : ℕ}

/-- The residue class `C(x̄) = {y ∈ S : ȳ = x̄}` of `x` in the list `S`. -/
def cls (S : Finset (Fin d → ZMod (p ^ 2))) (x : Fin d → ZMod (p ^ 2)) :
    Finset (Fin d → ZMod (p ^ 2)) :=
  S.filter fun y => residue y = residue x

/-- `T_I`: the number of triples whose sum has residue `0`. -/
def TI (U₁ U₂ U₃ : Finset (Fin d → ZMod (p ^ 2))) : ℕ :=
  ((U₁ ×ˢ U₂ ×ˢ U₃).filter fun t => residue (t.1 + t.2.1 + t.2.2) = 0).card

/-- The hypothesis of Lemma "Case L" (`g:lem:partL`): `T_I ≤ σ n²`. -/
def CaseL (n σ : ℕ) (U : Finset (Fin d → ZMod (p ^ 2)) × Finset (Fin d → ZMod (p ^ 2)) ×
    Finset (Fin d → ZMod (p ^ 2))) : Prop :=
  TI U.1 U.2.1 U.2.2 ≤ σ * n ^ 2

/-- The data of Case H with `s = s_min`: every class has at least `s` elements, `σ < 2s`, and one
list (the one achieving `s_min`) has all classes of fewer than `2s` elements. -/
def CaseH (σ s : ℕ) (U : Finset (Fin d → ZMod (p ^ 2)) × Finset (Fin d → ZMod (p ^ 2)) ×
    Finset (Fin d → ZMod (p ^ 2))) : Prop :=
  0 < s ∧ σ < 2 * s ∧ (∀ x ∈ U.1, s ≤ (cls U.1 x).card) ∧ (∀ x ∈ U.2.1, s ≤ (cls U.2.1 x).card) ∧
  (∀ x ∈ U.2.2, s ≤ (cls U.2.2 x).card) ∧
  ((∀ x ∈ U.1, (cls U.1 x).card < 2 * s) ∨ (∀ x ∈ U.2.1, (cls U.2.1 x).card < 2 * s) ∨
   (∀ x ∈ U.2.2, (cls U.2.2 x).card < 2 * s))

/-- The heavy part `H = {x ∈ S : |C(x̄)| ≥ σ}` (complement of `light residue S σ` in `S`). -/
def heavy (S : Finset (Fin d → ZMod (p ^ 2))) (σ : ℕ) : Finset (Fin d → ZMod (p ^ 2)) :=
  S.filter fun x => σ ≤ (cls S x).card

/-- The bucket `B_j`: heavy elements whose class has between `2^j` and `2^{j+1} − 1` elements
(i.e. `⌊log₂ |C(x̄)|⌋ = j`). -/
def bucket (S : Finset (Fin d → ZMod (p ^ 2))) (σ j : ℕ) : Finset (Fin d → ZMod (p ^ 2)) :=
  (heavy S σ).filter fun x => Nat.log 2 (cls S x).card = j

/-- The 7 sub-instances `(U₁, U₂, U₃)`, `U_i ∈ {L_i, H_i}`, not all heavy. -/
def lightHeavy (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (σ : ℕ) :
    List (Finset (Fin d → ZMod (p ^ 2)) × Finset (Fin d → ZMod (p ^ 2)) ×
      Finset (Fin d → ZMod (p ^ 2))) :=
  [(light residue S₁ σ, light residue S₂ σ, light residue S₃ σ),
   (light residue S₁ σ, light residue S₂ σ, heavy S₃ σ),
   (light residue S₁ σ, heavy S₂ σ, light residue S₃ σ),
   (light residue S₁ σ, heavy S₂ σ, heavy S₃ σ),
   (heavy S₁ σ, light residue S₂ σ, light residue S₃ σ),
   (heavy S₁ σ, light residue S₂ σ, heavy S₃ σ),
   (heavy S₁ σ, heavy S₂ σ, light residue S₃ σ)]

/-- The bucket indices `j ∈ {0, …, ⌊log₂ n⌋}`. -/
def idx (n : ℕ) : List ℕ := List.range (Nat.log 2 n + 1)

/-- The `(⌊log₂ n⌋ + 1)^3` bucket sub-instances `(B_{1,j₁}, B_{2,j₂}, B_{3,j₃})`. -/
def buckets (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (σ n : ℕ) :
    List (Finset (Fin d → ZMod (p ^ 2)) × Finset (Fin d → ZMod (p ^ 2)) ×
      Finset (Fin d → ZMod (p ^ 2))) :=
  (idx n ×ˢ idx n ×ˢ idx n).map fun j => (bucket S₁ σ j.1, bucket S₂ σ j.2.1, bucket S₃ σ j.2.2)

/-- All sub-instances: the 7 with a light list, then the buckets. -/
def subInst (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (σ n : ℕ) :
    List (Finset (Fin d → ZMod (p ^ 2)) × Finset (Fin d → ZMod (p ^ 2)) ×
      Finset (Fin d → ZMod (p ^ 2))) :=
  lightHeavy S₁ S₂ S₃ σ ++ buckets S₁ S₂ S₃ σ n

/-! ### Basic facts -/

section basic
variable {S : Finset (Fin d → ZMod (p ^ 2))} {σ j : ℕ} {x : Fin d → ZMod (p ^ 2)}

theorem mem_light : x ∈ light residue S σ ↔ x ∈ S ∧ (cls S x).card < σ := Finset.mem_filter

theorem mem_heavy : x ∈ heavy S σ ↔ x ∈ S ∧ σ ≤ (cls S x).card := Finset.mem_filter

theorem mem_bucket : x ∈ bucket S σ j ↔ x ∈ heavy S σ ∧ Nat.log 2 (cls S x).card = j :=
  Finset.mem_filter

theorem light_sub : light residue S σ ⊆ S := Finset.filter_subset _ _

theorem heavy_sub : heavy S σ ⊆ S := Finset.filter_subset _ _

theorem bucket_sub_heavy : bucket S σ j ⊆ heavy S σ := Finset.filter_subset _ _

theorem bucket_sub : bucket S σ j ⊆ S := bucket_sub_heavy.trans heavy_sub

theorem mem_light_iff_not_heavy (hx : x ∈ S) : x ∈ light residue S σ ↔ x ∉ heavy S σ := by
  rw [mem_light, mem_heavy]
  simp only [hx, true_and, not_le]

theorem self_mem_cls (hx : x ∈ S) : x ∈ cls S x := Finset.mem_filter.2 ⟨hx, rfl⟩

theorem cls_card_le : (cls S x).card ≤ S.card := Finset.card_filter_le _ _

/-- The class depends only on the residue. -/
theorem cls_eq_of_residue {y : Fin d → ZMod (p ^ 2)} (h : residue y = residue x) :
    cls S y = cls S x := by
  simp only [cls, h]

/-- Heaviness and the bucket index are properties of the residue class: the class of `x` in its
bucket is its full class in `S`. -/
theorem cls_bucket (hx : x ∈ bucket S σ j) : cls (bucket S σ j) x = cls S x := by
  ext y
  simp only [cls, Finset.mem_filter]
  constructor
  · rintro ⟨hy, e⟩
    exact ⟨bucket_sub hy, e⟩
  · rintro ⟨hy, e⟩
    refine ⟨?_, e⟩
    have hc : cls S y = cls S x := cls_eq_of_residue e
    rw [mem_bucket, mem_heavy] at hx ⊢
    rw [hc]
    exact ⟨⟨hy, hx.1.2⟩, hx.2⟩

/-- In a bucket `B_j`, every class (a full class of `S`) has at least `σ` elements and between
`2^j` and `2^{j+1} − 1` elements. -/
theorem bucket_bounds (hx : x ∈ bucket S σ j) :
    σ ≤ (cls (bucket S σ j) x).card ∧ 2 ^ j ≤ (cls (bucket S σ j) x).card ∧
      (cls (bucket S σ j) x).card < 2 * 2 ^ j := by
  rw [cls_bucket hx]
  have hx' := hx
  rw [mem_bucket, mem_heavy] at hx'
  obtain ⟨⟨hxS, hσ⟩, hlog⟩ := hx'
  have hc : (cls S x).card ≠ 0 := Finset.card_ne_zero.2 ⟨x, self_mem_cls hxS⟩
  refine ⟨hσ, ?_, ?_⟩
  · have := Nat.pow_log_le_self 2 hc
    rwa [hlog] at this
  · have h1 : (cls S x).card < 2 ^ (j + 1) := by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (cls S x).card
      rwa [hlog] at this
    have h2 : (2 : ℕ) ^ (j + 1) = 2 * 2 ^ j := by ring
    omega

end basic

/-! ### Permuting the lists in `T_I` -/

section perm
variable (U₁ U₂ U₃ : Finset (Fin d → ZMod (p ^ 2)))

theorem TI_rot : TI U₁ U₂ U₃ ≤ TI U₂ U₃ U₁ := by
  unfold TI
  refine Finset.card_le_card_of_injOn (fun t => (t.2.1, t.2.2, t.1)) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at ht ⊢
    refine ⟨⟨ht.1.2.1, ht.1.2.2, ht.1.1⟩, ?_⟩
    rw [show t.2.1 + t.2.2 + t.1 = t.1 + t.2.1 + t.2.2 by abel]
    exact ht.2
  · intro t _ t' _ e
    simp only [Prod.mk.injEq] at e
    exact Prod.ext e.2.2 (Prod.ext e.1 e.2.1)

theorem TI_swap : TI U₁ U₂ U₃ ≤ TI U₁ U₃ U₂ := by
  unfold TI
  refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.2, t.2.1)) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at ht ⊢
    refine ⟨⟨ht.1.1, ht.1.2.2, ht.1.2.1⟩, ?_⟩
    rw [show t.1 + t.2.2 + t.2.1 = t.1 + t.2.1 + t.2.2 by abel]
    exact ht.2
  · intro t _ t' _ e
    simp only [Prod.mk.injEq] at e
    exact Prod.ext e.1 (Prod.ext e.2.2 e.2.1)

end perm

/-! ### Case L for the 7 sub-instances with a light list (Lemma "a light list") -/

theorem mul_bound {a b n σ : ℕ} (ha : a ≤ n) (hb : b ≤ n) : a * b * (σ - 1) ≤ σ * n ^ 2 :=
  calc a * b * (σ - 1) ≤ n * n * σ := Nat.mul_le_mul (Nat.mul_le_mul ha hb) (Nat.sub_le _ _)
    _ = σ * n ^ 2 := by ring

section caseL
variable {n σ : ℕ} {S U₁ U₂ U₃ : Finset (Fin d → ZMod (p ^ 2))}

theorem caseL_light₃ (h₁ : U₁.card ≤ n) (h₂ : U₂.card ≤ n) :
    CaseL n σ (U₁, U₂, light residue S σ) := by
  unfold CaseL
  exact (TI_light_le U₁ U₂ S σ).trans (mul_bound h₁ h₂)

theorem caseL_light₁ (h₂ : U₂.card ≤ n) (h₃ : U₃.card ≤ n) :
    CaseL n σ (light residue S σ, U₂, U₃) := by
  unfold CaseL
  exact (TI_rot _ U₂ U₃).trans ((TI_light_le U₂ U₃ S σ).trans (mul_bound h₂ h₃))

theorem caseL_light₂ (h₁ : U₁.card ≤ n) (h₃ : U₃.card ≤ n) :
    CaseL n σ (U₁, light residue S σ, U₃) := by
  unfold CaseL
  exact (TI_swap U₁ _ U₃).trans ((TI_light_le U₁ U₃ S σ).trans (mul_bound h₁ h₃))

theorem card_light_le (h : S.card ≤ n) : (light residue S σ).card ≤ n :=
  (Finset.card_le_card light_sub).trans h

theorem card_heavy_le (h : S.card ≤ n) : (heavy S σ).card ≤ n :=
  (Finset.card_le_card heavy_sub).trans h

end caseL

/-! ### Case H (Bucketing, Lemma "three heavy lists") -/

section caseH
variable {σ : ℕ}

/-- If every class of `U_i` has between `a_i` and `2a_i − 1` elements and `σ < 2a_i`, then
`(U₁, U₂, U₃)` is in Case H with `s = min a_i`. -/
theorem caseH_of_bounds {a₁ a₂ a₃ : ℕ} {U₁ U₂ U₃ : Finset (Fin d → ZMod (p ^ 2))}
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hσ₁ : σ < 2 * a₁) (hσ₂ : σ < 2 * a₂) (hσ₃ : σ < 2 * a₃)
    (h₁ : ∀ x ∈ U₁, a₁ ≤ (cls U₁ x).card ∧ (cls U₁ x).card < 2 * a₁)
    (h₂ : ∀ x ∈ U₂, a₂ ≤ (cls U₂ x).card ∧ (cls U₂ x).card < 2 * a₂)
    (h₃ : ∀ x ∈ U₃, a₃ ≤ (cls U₃ x).card ∧ (cls U₃ x).card < 2 * a₃) :
    CaseH σ (min a₁ (min a₂ a₃)) (U₁, U₂, U₃) := by
  have m1 : min a₁ (min a₂ a₃) ≤ a₁ := min_le_left _ _
  have m2 : min a₁ (min a₂ a₃) ≤ a₂ := (min_le_right _ _).trans (min_le_left _ _)
  have m3 : min a₁ (min a₂ a₃) ≤ a₃ := (min_le_right _ _).trans (min_le_right _ _)
  unfold CaseH
  refine ⟨lt_min ha₁ (lt_min ha₂ ha₃), ?_, fun x hx => m1.trans (h₁ x hx).1,
    fun x hx => m2.trans (h₂ x hx).1, fun x hx => m3.trans (h₃ x hx).1, ?_⟩
  · rcases min_choice a₁ (min a₂ a₃) with h | h
    · rw [h]; exact hσ₁
    · rcases min_choice a₂ a₃ with h' | h' <;> rw [h, h'] <;> assumption
  · rcases min_choice a₁ (min a₂ a₃) with h | h
    · exact Or.inl fun x hx => by rw [h]; exact (h₁ x hx).2
    · rcases min_choice a₂ a₃ with h' | h'
      · exact Or.inr (Or.inl fun x hx => by rw [h, h']; exact (h₂ x hx).2)
      · exact Or.inr (Or.inr fun x hx => by rw [h, h']; exact (h₃ x hx).2)

/-- A bucket sub-instance is in Case L (if a bucket is empty, `T_I = 0`) or in Case H with
`s = min_i 2^{j_i}`. -/
theorem bucket_cases (n : ℕ) (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (j₁ j₂ j₃ : ℕ) :
    CaseL n σ (bucket S₁ σ j₁, bucket S₂ σ j₂, bucket S₃ σ j₃) ∨
      ∃ s, CaseH σ s (bucket S₁ σ j₁, bucket S₂ σ j₂, bucket S₃ σ j₃) := by
  rcases (bucket S₁ σ j₁).eq_empty_or_nonempty with e | ⟨x₁, hx₁⟩
  · left; unfold CaseL TI; simp [e]
  rcases (bucket S₂ σ j₂).eq_empty_or_nonempty with e | ⟨x₂, hx₂⟩
  · left; unfold CaseL TI; simp [e]
  rcases (bucket S₃ σ j₃).eq_empty_or_nonempty with e | ⟨x₃, hx₃⟩
  · left; unfold CaseL TI; simp [e]
  right
  exact ⟨_, caseH_of_bounds (pow_pos two_pos j₁) (pow_pos two_pos j₂) (pow_pos two_pos j₃)
    (lt_of_le_of_lt (bucket_bounds hx₁).1 (bucket_bounds hx₁).2.2)
    (lt_of_le_of_lt (bucket_bounds hx₂).1 (bucket_bounds hx₂).2.2)
    (lt_of_le_of_lt (bucket_bounds hx₃).1 (bucket_bounds hx₃).2.2)
    (fun x hx => (bucket_bounds hx).2) (fun x hx => (bucket_bounds hx).2)
    (fun x hx => (bucket_bounds hx).2)⟩

/-- `T_I < 2s|U₁||U₂|` when every class of `U₃` has fewer than `2s` elements. -/
theorem TI_le_of_cls_lt {s : ℕ} {U₁ U₂ U₃ : Finset (Fin d → ZMod (p ^ 2))}
    (h : ∀ x ∈ U₃, (cls U₃ x).card < 2 * s) : TI U₁ U₂ U₃ ≤ 2 * s * U₁.card * U₂.card := by
  have := TI_classes_lt (residue (p := p) (d := d)) U₁ U₂ U₃ s h
  simpa only [TI, residue_add] using this

theorem bound2 {a b n s : ℕ} (ha : a ≤ n) (hb : b ≤ n) : 2 * s * a * b ≤ 2 * s * n ^ 2 :=
  calc 2 * s * a * b ≤ 2 * s * n * n := Nat.mul_le_mul (Nat.mul_le_mul le_rfl ha) hb
    _ = 2 * s * n ^ 2 := by ring

/-- **Lemma "three heavy lists"** (`g:lem:heavyTI`), in the form `T_I ≤ 2 s n²`. -/
theorem TI_le_of_caseH {n s : ℕ}
    {U : Finset (Fin d → ZMod (p ^ 2)) × Finset (Fin d → ZMod (p ^ 2)) ×
      Finset (Fin d → ZMod (p ^ 2))}
    (hH : CaseH σ s U) (h₁ : U.1.card ≤ n) (h₂ : U.2.1.card ≤ n) (h₃ : U.2.2.card ≤ n) :
    TI U.1 U.2.1 U.2.2 ≤ 2 * s * n ^ 2 := by
  unfold CaseH at hH
  obtain ⟨-, -, -, -, -, h | h | h⟩ := hH
  · exact (TI_rot _ _ _).trans ((TI_le_of_cls_lt h).trans (bound2 h₂ h₃))
  · exact (TI_swap _ _ _).trans ((TI_le_of_cls_lt h).trans (bound2 h₁ h₃))
  · exact (TI_le_of_cls_lt h).trans (bound2 h₁ h₂)

end caseH

/-! ### The partition -/

/-- A list in which exactly one entry satisfies `P` has exactly one index whose entry does. -/
theorem existsUnique_of_countP_eq_one {β : Type*} (P : β → Prop) [DecidablePred P] :
    ∀ l : List β, l.countP (fun b => decide (P b)) = 1 → ∃! i : Fin l.length, P (l.get i)
  | [], h => by simp at h
  | a :: l, h => by
    rw [List.countP_cons] at h
    by_cases ha : P a
    · rw [if_pos (decide_eq_true ha)] at h
      have h0 : ∀ b ∈ l, ¬ P b := fun b hb hPb => by
        have := List.countP_eq_zero.1 (show l.countP (fun b => decide (P b)) = 0 by omega) b hb
        exact this (decide_eq_true hPb)
      refine ⟨⟨0, by simp⟩, ha, ?_⟩
      rintro ⟨_ | k, hk⟩ hi
      · rfl
      · exact absurd hi (h0 _ (List.get_mem l ⟨k, by simpa using hk⟩))
    · rw [if_neg (by simpa using ha)] at h
      obtain ⟨⟨k, hk⟩, hP, huniq⟩ := existsUnique_of_countP_eq_one P l (by omega)
      refine ⟨⟨k + 1, by simpa using hk⟩, hP, ?_⟩
      rintro ⟨_ | k', hk'⟩ hi
      · exact absurd hi ha
      · have := huniq ⟨k', by simpa using hk'⟩ hi
        simp only [Fin.mk.injEq] at this
        subst this
        rfl

section partition
variable {S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))} {σ n : ℕ}

theorem subInst_length : (subInst S₁ S₂ S₃ σ n).length = 7 + (Nat.log 2 n + 1) ^ 3 := by
  simp only [subInst, lightHeavy, buckets, idx, List.length_append, List.length_map,
    List.length_product, List.length_range, List.length_cons, List.length_nil]
  ring

theorem subInst_sub : ∀ U ∈ subInst S₁ S₂ S₃ σ n, U.1 ⊆ S₁ ∧ U.2.1 ⊆ S₂ ∧ U.2.2 ⊆ S₃ := by
  intro U hU
  simp only [subInst, lightHeavy, buckets, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hU
  rcases hU with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨j, -, rfl⟩ <;>
    refine ⟨?_, ?_, ?_⟩ <;>
    first | exact light_sub | exact heavy_sub | exact bucket_sub

/-- The bucket sub-instances containing `t`: exactly one if all three members are heavy, none
otherwise. Here `|S_i| ≤ n` gives `⌊log₂ |C(x̄)|⌋ ≤ ⌊log₂ n⌋`. -/
theorem countP_buckets (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (t : (Fin d → ZMod (p ^ 2)) × (Fin d → ZMod (p ^ 2)) × (Fin d → ZMod (p ^ 2))) :
    (buckets S₁ S₂ S₃ σ n).countP (fun U => decide (t ∈ U.1 ×ˢ U.2.1 ×ˢ U.2.2)) =
      if t.1 ∈ heavy S₁ σ ∧ t.2.1 ∈ heavy S₂ σ ∧ t.2.2 ∈ heavy S₃ σ then 1 else 0 := by
  rw [buckets, List.countP_map]
  split_ifs with hH
  · obtain ⟨g1, g2, g3⟩ := hH
    have hlog : ∀ (S : Finset (Fin d → ZMod (p ^ 2))) (x : Fin d → ZMod (p ^ 2)),
        S.card ≤ n → Nat.log 2 (cls S x).card ∈ idx n := fun S x hS => by
      rw [idx, List.mem_range]
      exact Nat.lt_succ_of_le (Nat.log_mono_right (cls_card_le.trans hS))
    have hmem : (Nat.log 2 (cls S₁ t.1).card, Nat.log 2 (cls S₂ t.2.1).card,
        Nat.log 2 (cls S₃ t.2.2).card) ∈ idx n ×ˢ idx n ×ˢ idx n := by
      rw [List.mem_product, List.mem_product]
      exact ⟨hlog _ _ h₁, hlog _ _ h₂, hlog _ _ h₃⟩
    have hnd : (idx n ×ˢ idx n ×ˢ idx n).Nodup :=
      List.nodup_range.product (List.nodup_range.product List.nodup_range)
    rw [List.countP_congr (q := fun j => j == (Nat.log 2 (cls S₁ t.1).card,
      Nat.log 2 (cls S₂ t.2.1).card, Nat.log 2 (cls S₃ t.2.2).card)) ?_]
    · exact List.count_eq_one_of_mem hnd hmem
    · rintro ⟨j1, j2, j3⟩ _
      simp only [Function.comp_apply, decide_eq_true_eq, Finset.mem_product, mem_bucket,
        beq_iff_eq, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨-, rfl⟩, ⟨-, rfl⟩, ⟨-, rfl⟩⟩
        exact ⟨rfl, rfl, rfl⟩
      · rintro ⟨rfl, rfl, rfl⟩
        exact ⟨⟨g1, rfl⟩, ⟨g2, rfl⟩, ⟨g3, rfl⟩⟩
  · rw [List.countP_eq_zero]
    intro j _ hj
    simp only [Function.comp_apply, decide_eq_true_eq, Finset.mem_product] at hj
    exact hH ⟨bucket_sub_heavy hj.1, bucket_sub_heavy hj.2.1, bucket_sub_heavy hj.2.2⟩

theorem countP_subInst (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    {t : (Fin d → ZMod (p ^ 2)) × (Fin d → ZMod (p ^ 2)) × (Fin d → ZMod (p ^ 2))}
    (ht : t ∈ S₁ ×ˢ S₂ ×ˢ S₃) :
    (subInst S₁ S₂ S₃ σ n).countP (fun U => decide (t ∈ U.1 ×ˢ U.2.1 ×ˢ U.2.2)) = 1 := by
  rw [subInst, List.countP_append, countP_buckets h₁ h₂ h₃ t]
  simp only [Finset.mem_product] at ht
  have e1 := mem_light_iff_not_heavy (σ := σ) ht.1
  have e2 := mem_light_iff_not_heavy (σ := σ) ht.2.1
  have e3 := mem_light_iff_not_heavy (σ := σ) ht.2.2
  by_cases g1 : t.1 ∈ heavy S₁ σ <;> by_cases g2 : t.2.1 ∈ heavy S₂ σ <;>
    by_cases g3 : t.2.2 ∈ heavy S₃ σ <;>
    simp [lightHeavy, Finset.mem_product, e1, e2, e3, g1, g2, g3]

/-- **Partition**: every triple of `S₁ × S₂ × S₃` lies in exactly one sub-instance. -/
theorem subInst_partition (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (t : (Fin d → ZMod (p ^ 2)) × (Fin d → ZMod (p ^ 2)) × (Fin d → ZMod (p ^ 2)))
    (ht : t ∈ S₁ ×ˢ S₂ ×ˢ S₃) :
    ∃! i : Fin (subInst S₁ S₂ S₃ σ n).length,
      t ∈ ((subInst S₁ S₂ S₃ σ n).get i).1 ×ˢ ((subInst S₁ S₂ S₃ σ n).get i).2.1 ×ˢ
        ((subInst S₁ S₂ S₃ σ n).get i).2.2 :=
  existsUnique_of_countP_eq_one
    (fun U : Finset (Fin d → ZMod (p ^ 2)) × Finset (Fin d → ZMod (p ^ 2)) ×
      Finset (Fin d → ZMod (p ^ 2)) => t ∈ U.1 ×ˢ U.2.1 ×ˢ U.2.2) _
    (countP_subInst h₁ h₂ h₃ ht)

/-- Every solution lies in a sub-instance, and a solution of a sub-instance is one of
`(S₁, S₂, S₃)`. -/
theorem exists_sol_iff_subInst (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n) :
    (∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) ↔
      ∃ U ∈ subInst S₁ S₂ S₃ σ n, ∃ x₁ ∈ U.1, ∃ x₂ ∈ U.2.1, ∃ x₃ ∈ U.2.2, x₁ + x₂ + x₃ = 0 := by
  constructor
  · rintro ⟨x₁, hx₁, x₂, hx₂, x₃, hx₃, hs⟩
    have ht : (x₁, x₂, x₃) ∈ S₁ ×ˢ S₂ ×ˢ S₃ :=
      Finset.mem_product.2 ⟨hx₁, Finset.mem_product.2 ⟨hx₂, hx₃⟩⟩
    obtain ⟨i, hi, -⟩ := subInst_partition (σ := σ) h₁ h₂ h₃ _ ht
    simp only [Finset.mem_product] at hi
    exact ⟨_, List.get_mem _ i, x₁, hi.1, x₂, hi.2.1, x₃, hi.2.2, hs⟩
  · rintro ⟨U, hU, x₁, hx₁, x₂, hx₂, x₃, hx₃, hs⟩
    obtain ⟨s₁, s₂, s₃⟩ := subInst_sub U hU
    exact ⟨x₁, s₁ hx₁, x₂, s₂ hx₂, x₃, s₃ hx₃, hs⟩

/-- **Each sub-instance is in Case L or in Case H** (Lemma "a light list" for the 7, Bucketing for
the others). The hypothesis `0 < σ` of the paper is not needed. -/
theorem subInst_cases (_hσ : 0 < σ) (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n) :
    ∀ U ∈ subInst S₁ S₂ S₃ σ n, CaseL n σ U ∨ ∃ s, CaseH σ s U := by
  intro U hU
  simp only [subInst, lightHeavy, buckets, List.mem_append, List.mem_cons, List.mem_map,
    List.not_mem_nil, or_false] at hU
  rcases hU with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨⟨j₁, j₂, j₃⟩, -, rfl⟩
  · exact Or.inl (caseL_light₁ (card_light_le h₂) (card_light_le h₃))
  · exact Or.inl (caseL_light₁ (card_light_le h₂) (card_heavy_le h₃))
  · exact Or.inl (caseL_light₁ (card_heavy_le h₂) (card_light_le h₃))
  · exact Or.inl (caseL_light₁ (card_heavy_le h₂) (card_heavy_le h₃))
  · exact Or.inl (caseL_light₂ (card_heavy_le h₁) (card_light_le h₃))
  · exact Or.inl (caseL_light₂ (card_heavy_le h₁) (card_heavy_le h₃))
  · exact Or.inl (caseL_light₃ (card_heavy_le h₁) (card_heavy_le h₂))
  · exact bucket_cases n S₁ S₂ S₃ j₁ j₂ j₃

end partition

end ExpP2Split
end GroupLean

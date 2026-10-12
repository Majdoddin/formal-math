import GroupLean.Boolean
import GroupLean.Latin

/-!
# OV gadgets of any size (paper: Definition 20.7, Lemmas 20.8, 20.9, Proposition 20.14(d))

A gadget of size `t` uses `t` coordinates of `Prob(P)` per coordinate of OV: maps
`f i ℓ : Bool → α` (`i : Fin 3` position, `ℓ : Fin t`), constant at `C`-positions, such that the
conjunction over `ℓ` of `P (f 0 ℓ β₀) (f 1 ℓ β₁) (f 2 ℓ β₂)` is exactly the target relation.

* `GadgetT.ov_iff_prob` (Lemma 20.8): OV in dimension `d` is equivalent to `Prob P` on the image
  lists in dimension `d * t`, each list no larger than `A`, `B` or `1`.
* `not_hasGadgetOfSize_of_rep` (Lemma 20.9): a representable relation has no gadget of any size.
* `hasGadgetSome_iff_hasGadget`, `hasGadget_iff_restriction` (Proposition 20.14(d)): a gadget of
  some size exists iff one of size 1 exists iff some Boolean restriction is not representable.
-/

namespace GroupLean

universe u v w

variable {α : Type u}

/-- An OV gadget of size `t`. -/
structure GadgetT (α : Type u) (t : ℕ) where
  side : Fin 3 → Side
  f : Fin 3 → Fin t → Bool → α

/-- Validity of a gadget of size `t` for `P`. -/
def GadgetT.Valid {t : ℕ} (g : GadgetT α t) (P : α → α → α → Prop) : Prop :=
  (∃ i, g.side i = .A) ∧ (∃ i, g.side i = .B) ∧
    (∀ i ℓ, g.side i = .C → g.f i ℓ false = g.f i ℓ true) ∧
    ∀ u : Fin 3 → Bool,
      (∀ ℓ, P (g.f 0 ℓ (u 0)) (g.f 1 ℓ (u 1)) (g.f 2 ℓ (u 2))) ↔ Target g.side u

/-- `P` has an OV gadget of size `t`. -/
def HasGadgetOfSize (P : α → α → α → Prop) (t : ℕ) : Prop := ∃ g : GadgetT α t, g.Valid P

/-! ### Lemma 20.8: the reduction -/

section Reduction

variable {t : ℕ}

/-- The encoding `F_i(w)` of a vector `w ∈ {0,1}^d`: coordinate `(j, ℓ)` (as `Fin (d * t)`)
carries `f i ℓ (w j)`. -/
def GadgetT.enc (g : GadgetT α t) (i : Fin 3) {d : ℕ} (w : Fin d → Bool) : Fin (d * t) → α :=
  fun k => g.f i (finProdFinEquiv.symm k).2 (w (finProdFinEquiv.symm k).1)

variable [DecidableEq α]

/-- The list at position `i`. -/
def GadgetT.list (g : GadgetT α t) (i : Fin 3) {d : ℕ} (A B : Finset (Fin d → Bool)) :
    Finset (Fin (d * t) → α) :=
  match g.side i with
  | .A => A.image (g.enc i)
  | .B => B.image (g.enc i)
  | .C => {g.enc i fun _ => false}

lemma GadgetT.card_list_le (g : GadgetT α t) (i : Fin 3) {d : ℕ} (A B : Finset (Fin d → Bool)) :
    (g.list i A B).card ≤ max A.card (max B.card 1) := by
  unfold GadgetT.list
  split
  · exact (Finset.card_image_le).trans (le_max_left _ _)
  · exact (Finset.card_image_le).trans ((le_max_left _ _).trans (le_max_right _ _))
  · rw [Finset.card_singleton]; exact (le_max_right _ _).trans (le_max_right _ _)

lemma GadgetT.mem_list {g : GadgetT α t} {i : Fin 3} {d : ℕ} {A B : Finset (Fin d → Bool)}
    {x : Fin (d * t) → α} (hx : x ∈ g.list i A B) :
    ∃ v : Fin d → Bool, (g.side i = .A → v ∈ A) ∧ (g.side i = .B → v ∈ B) ∧ x = g.enc i v := by
  unfold GadgetT.list at hx
  split at hx
  next h =>
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨v, fun _ => hv, fun h' => by simp [h] at h', rfl⟩
  next h =>
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨v, fun h' => by simp [h] at h', fun _ => hv, rfl⟩
  next h =>
    rw [Finset.mem_singleton] at hx
    exact ⟨fun _ => false, fun h' => by simp [h] at h', fun h' => by simp [h] at h', hx⟩

lemma GadgetT.mem_list_of {g : GadgetT α t} {i : Fin 3} {d : ℕ} {A B : Finset (Fin d → Bool)}
    (v : Fin d → Bool) (hA : g.side i = .A → v ∈ A) (hB : g.side i = .B → v ∈ B)
    (hC : g.side i = .C → v = fun _ => false) : g.enc i v ∈ g.list i A B := by
  unfold GadgetT.list
  split
  next h => exact Finset.mem_image.2 ⟨v, hA h, rfl⟩
  next h => exact Finset.mem_image.2 ⟨v, hB h, rfl⟩
  next h => rw [hC h]; exact Finset.mem_singleton.2 rfl

/-- **Lemma 20.8 (the reduction).** For a valid gadget of size `t`, OV on `A, B ⊆ {0,1}^d` holds
iff `Prob P` holds on the three image lists in dimension `d * t` (exact correspondence; with
`GadgetT.card_list_le` the lists are no longer than `A`, `B` or `1`). Under OVH this gives the
stated lower bound; the hypothesis and the running time are not formalised. -/
theorem GadgetT.ov_iff_prob {g : GadgetT α t} {P : α → α → α → Prop} (hg : g.Valid P) {d : ℕ}
    (A B : Finset (Fin d → Bool)) :
    OV A B ↔ Prob P (g.list 0 A B) (g.list 1 A B) (g.list 2 A B) := by
  obtain ⟨⟨i₀, hi₀⟩, ⟨i₁, hi₁⟩, -, hv⟩ := hg
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    let V : Fin 3 → Fin d → Bool := fun i => pick (g.side i) a b (fun _ => false)
    have hmem : ∀ i, g.enc i (V i) ∈ g.list i A B := by
      intro i
      refine GadgetT.mem_list_of _ (fun h => ?_) (fun h => ?_) (fun h => ?_) <;>
        simp only [V, h, pick_A, pick_B, pick_C] <;> assumption
    refine ⟨_, hmem 0, _, hmem 1, _, hmem 2, fun k => ?_⟩
    have ht : Target g.side fun i => V i (finProdFinEquiv.symm k).1 := by
      refine ⟨a (finProdFinEquiv.symm k).1, b (finProdFinEquiv.symm k).1,
        hab _, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩ <;> simp [V, h]
    exact (hv _).2 ht (finProdFinEquiv.symm k).2
  · rintro ⟨x₀, h₀, x₁, h₁, x₂, h₂, hP⟩
    obtain ⟨v₀, hA₀, hB₀, rfl⟩ := GadgetT.mem_list h₀
    obtain ⟨v₁, hA₁, hB₁, rfl⟩ := GadgetT.mem_list h₁
    obtain ⟨v₂, hA₂, hB₂, rfl⟩ := GadgetT.mem_list h₂
    let V : Fin 3 → Fin d → Bool := ![v₀, v₁, v₂]
    have hA : ∀ i, g.side i = .A → V i ∈ A := by
      intro i; fin_cases i
      exacts [hA₀, hA₁, hA₂]
    have hB : ∀ i, g.side i = .B → V i ∈ B := by
      intro i; fin_cases i
      exacts [hB₀, hB₁, hB₂]
    refine ⟨V i₀, hA i₀ hi₀, V i₁, hB i₁ hi₁, fun j => ?_⟩
    have hk : ∀ ℓ, P (g.f 0 ℓ (v₀ j)) (g.f 1 ℓ (v₁ j)) (g.f 2 ℓ (v₂ j)) := by
      intro ℓ
      have := hP (finProdFinEquiv (j, ℓ))
      simp only [GadgetT.enc, Equiv.symm_apply_apply] at this
      exact this
    obtain ⟨a, b, hab, hag⟩ := (hv fun i => V i j).1 hk
    have e1 : V i₀ j = a := (hag i₀).1 hi₀
    have e2 : V i₁ j = b := (hag i₁).2 hi₁
    rw [e1, e2]
    exact hab

end Reduction

/-! ### Lemma 20.9 and Proposition 20.14(d) -/

/-- Representability is preserved by substituting maps in each position. -/
theorem RepresentableOver.comp {β : Type w} {A : Type v} [AddCommGroup A]
    {Q : α → α → α → Prop} (h : RepresentableOver A Q) (c₁ c₂ c₃ : β → α) :
    RepresentableOver A (fun a b c => Q (c₁ a) (c₂ b) (c₃ c)) := by
  obtain ⟨φ₁, φ₂, φ₃, t, h⟩ := h
  exact ⟨φ₁ ∘ c₁, φ₂ ∘ c₂, φ₃ ∘ c₃, t, fun a b c => h _ _ _⟩

/-- A conjunction of representable relations is representable over the product group. -/
theorem representable_forall {ι : Type*} {A : ι → Type v} [∀ l, AddCommGroup (A l)]
    {Q : ι → α → α → α → Prop} (h : ∀ l, RepresentableOver (A l) (Q l)) :
    RepresentableOver (∀ l, A l) (fun a b c => ∀ l, Q l a b c) := by
  choose φ₁ φ₂ φ₃ t hφ using h
  refine ⟨fun a l => φ₁ l a, fun b l => φ₂ l b, fun c l => φ₃ l c, t, fun a b c => ?_⟩
  simp only [hφ]
  exact ⟨fun H => funext fun l => H l, fun H l => congrFun H l⟩

/-- The target relation does not depend on the bits at `C`-positions. -/
lemma target_congr {s : Fin 3 → Side} {u u' : Fin 3 → Bool} (h : ∀ i, s i ≠ .C → u i = u' i) :
    Target s u ↔ Target s u' := by
  have key : ∀ a b, Agrees s a b u ↔ Agrees s a b u' := by
    intro a b
    refine forall_congr' fun i => ?_
    cases hs : s i with
    | A => rw [h i (by rw [hs]; decide)]
    | B => rw [h i (by rw [hs]; decide)]
    | C => simp
  simp only [Target, key]

/-- The target relation `T_θ ⊆ {0,1}³` of a side assignment is not representable. -/
theorem target_not_rep {s : Fin 3 → Side} (hA : ∃ i, s i = .A) (hB : ∃ i, s i = .B)
    {A : Type v} [AddCommGroup A] : ¬ RepresentableOver A (fun a b c => Target s ![a, b, c]) := by
  intro hr
  apply not_hasGadget_of_rep hr
  refine ⟨⟨s, fun i x => if s i = .C then false else x⟩, hA, hB, fun i hi => ?_, ?_⟩
  · change s i = .C at hi
    simp [hi]
  intro u
  apply target_congr
  intro i hi
  have hv : (![if s 0 = .C then false else u 0, if s 1 = .C then false else u 1,
      if s 2 = .C then false else u 2] : Fin 3 → Bool) = fun j => if s j = .C then false else u j := by
    funext j; fin_cases j <;> rfl
  change (![if s 0 = .C then false else u 0, if s 1 = .C then false else u 1,
      if s 2 = .C then false else u 2] : Fin 3 → Bool) i = u i
  rw [hv]
  simp [hi]

/-- If every conjunct of a gadget of size `t` is representable (over its own group), the gadget
cannot be valid: the conjunction, which is the target relation, would be representable over the
product. -/
theorem GadgetT.not_valid_of_conjuncts {t : ℕ} (g : GadgetT α t) (P : α → α → α → Prop)
    {A : Fin t → Type v} [∀ l, AddCommGroup (A l)]
    (h : ∀ l, RepresentableOver (A l) (fun a b c => P (g.f 0 l a) (g.f 1 l b) (g.f 2 l c))) :
    ¬ g.Valid P := by
  rintro ⟨hA, hB, -, hv⟩
  have hr := representable_forall h
  exact target_not_rep hA hB (hr.of_iff fun a b c => hv ![a, b, c])

/-- **Lemma 20.9 (full strength).** A relation representable over an abelian group has no OV
gadget of any size. -/
theorem not_hasGadgetOfSize_of_rep {A : Type v} [AddCommGroup A] {P : α → α → α → Prop}
    (hP : RepresentableOver A P) (t : ℕ) : ¬ HasGadgetOfSize P t := by
  rintro ⟨g, hg⟩
  exact g.not_valid_of_conjuncts P (A := fun _ => A) (fun l => hP.comp _ _ _) hg

/-- A gadget of size 1 is a gadget of size 1 in the sense of `GadgetT`. -/
theorem hasGadgetOfSize_one_of_hasGadget {P : α → α → α → Prop} (h : HasGadget P) :
    HasGadgetOfSize P 1 := by
  obtain ⟨g, hA, hB, hC, hv⟩ := h
  refine ⟨⟨g.side, fun i _ => g.f i⟩, hA, hB, fun i _ hi => hC i hi, fun u => ?_⟩
  rw [← hv u]
  exact ⟨fun H => H 0, fun H _ => H⟩

/-- Every map `Bool → α` factors through an injective map `Fin 2 → α` (two letters needed). -/
lemma factor_bool [Nontrivial α] (w : Bool → α) :
    ∃ v : Fin 2 → α, Function.Injective v ∧ ∃ c : Bool → Fin 2, ∀ b, w b = v (c b) := by
  by_cases h : w false = w true
  · obtain ⟨y, hy⟩ := exists_ne (w false)
    refine ⟨![w false, y], ?_, fun _ => 0, fun b => ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    · cases b
      · rfl
      · exact h.symm
  · refine ⟨![w false, w true], ?_, fun b => if b then 1 else 0, fun b => ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    · cases b <;> rfl

/-- The Boolean restrictions of `P`: substitute two letters per position. -/
def restrict (P : α → α → α → Prop) (v : Fin 3 → Fin 2 → α) : Fin 2 → Fin 2 → Fin 2 → Prop :=
  fun a b c => P (v 0 a) (v 1 b) (v 2 c)

/-- If every Boolean restriction (injective substitutions) is representable, `P` has no gadget
of any size. -/
theorem no_gadget_of_restrictions_rep [Nontrivial α] {P : α → α → α → Prop}
    (h : ∀ v : Fin 3 → Fin 2 → α, (∀ i, Function.Injective (v i)) →
      ∃ (A : Type) (_ : AddCommGroup A), RepresentableOver A (restrict P v))
    (t : ℕ) : ¬ HasGadgetOfSize P t := by
  rintro ⟨g, hg⟩
  have hall : ∀ l : Fin t, ∃ (A : Type) (_ : AddCommGroup A),
      RepresentableOver A (fun a b c => P (g.f 0 l a) (g.f 1 l b) (g.f 2 l c)) := by
    intro l
    choose v hv c hc using fun i => factor_bool (g.f i l)
    obtain ⟨A, _, hA⟩ := h v hv
    refine ⟨A, inferInstance, (hA.comp (c 0) (c 1) (c 2)).of_iff fun a b d => ?_⟩
    simp only [restrict, ← hc]
  choose A inst hrep using hall
  exact g.not_valid_of_conjuncts P hrep hg

/-- **Proposition 20.14(d), first equivalence.** A gadget of some size exists iff one of size
1 exists. -/
theorem hasGadgetSome_iff_hasGadget [Nontrivial α] (P : α → α → α → Prop) :
    (∃ t, HasGadgetOfSize P t) ↔ HasGadget P := by
  constructor
  · rintro ⟨t, ht⟩
    by_contra hn
    refine no_gadget_of_restrictions_rep (fun v _ => ?_) t ht
    by_contra hr
    apply hn
    have hgq : HasGadget (restrict P v) := by
      by_contra hq
      exact hr ((boolean_rep_iff _).2 hq)
    obtain ⟨g, hA, hB, hC, hv⟩ := hgq
    exact ⟨⟨g.side, fun i b => v i (g.f i b)⟩, hA, hB, fun i hi => by simp [hC i hi], hv⟩
  · intro h
    exact ⟨1, hasGadgetOfSize_one_of_hasGadget h⟩

/-- **Proposition 20.14(d), second equivalence.** `P` has a gadget of size 1 iff some Boolean
restriction of `P` (injective substitution of two letters in each position) is not
representable over any abelian group. -/
theorem hasGadget_iff_restriction [Nontrivial α] (P : α → α → α → Prop) :
    HasGadget P ↔ ∃ v : Fin 3 → Fin 2 → α, (∀ i, Function.Injective (v i)) ∧
      ¬ ∃ (A : Type) (_ : AddCommGroup A), RepresentableOver A (restrict P v) := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    exact no_gadget_of_restrictions_rep hn 1 (hasGadgetOfSize_one_of_hasGadget h)
  · rintro ⟨v, -, hr⟩
    have hgq : HasGadget (restrict P v) := by
      by_contra hq
      exact hr ((boolean_rep_iff _).2 hq)
    obtain ⟨g, hA, hB, hC, hv⟩ := hgq
    exact ⟨⟨g.side, fun i b => v i (g.f i b)⟩, hA, hB, fun i hi => by simp [hC i hi], hv⟩

/-- **Proposition 20.14(b), (c), any size.** The `Z₄` square (by Lemma 20.9) and the loop `L5`
(by its size-1 search and (d)) have no OV gadget of any size. -/
theorem z4Rel_not_hasGadgetOfSize (t : ℕ) : ¬ HasGadgetOfSize z4Rel t :=
  not_hasGadgetOfSize_of_rep z4Rel_rep t

theorem l5Rel_not_hasGadgetOfSize (t : ℕ) : ¬ HasGadgetOfSize l5Rel t := fun h =>
  l5Rel_not_hasGadget ((hasGadgetSome_iff_hasGadget l5Rel).1 ⟨t, h⟩)

end GroupLean

import Mathlib

/-!
# Coordinatewise problems, representability over abelian groups, one-coordinate OV gadgets

For a relation `P` on an alphabet `α`, `Prob P S₁ S₂ S₃` asks for `xᵢ ∈ Sᵢ` (vectors in `α^d`)
with `P (x₁ j) (x₂ j) (x₃ j)` for every coordinate `j`.

* `RepresentableOver A P`: `P a b c ↔ φ₁ a + φ₂ b + φ₃ c = t` for maps `φᵢ : α → A`.
  Then `Prob P` is 3SUM over `A^d` with target `(t,…,t)` (`prob_iff_threeSum`).
  A system of equations over `A` gives a representation over `Fin k → A`
  (`representable_of_system`).
* `Gadget`: a one-coordinate OV gadget (each position reads a bit of `a`, a bit of `b`, or a
  constant, through a map `Bool → α`). `Gadget.ov_iff_prob`: OV ↔ Prob on the image lists.
  `not_hasGadget_of_rep`: a representable relation has no gadget.
* No-carry base-`B` encoding: `sum_mul_pow_eq_zero_iff`, `threeSum_iff_baseB`.
* Kernel-checkable certificates (Bool checkers proved sound) used by the classification files:
  `checkSys` (equation systems over `ℤ` or `ZMod m`), `checkG` (gadgets), `checkAll`.
-/

namespace GroupLean

universe u v

section Basic

variable {α : Type u}

/-- The coordinatewise problem: some `xᵢ ∈ Sᵢ` satisfy `P` in every coordinate. -/
def Prob (P : α → α → α → Prop) {d : ℕ} (S₁ S₂ S₃ : Finset (Fin d → α)) : Prop :=
  ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, ∀ j, P (x₁ j) (x₂ j) (x₃ j)

/-- `P` is representable over the additive commutative group `A`. -/
def RepresentableOver (A : Type v) [AddCommGroup A] (P : α → α → α → Prop) : Prop :=
  ∃ φ₁ φ₂ φ₃ : α → A, ∃ t : A, ∀ a b c, P a b c ↔ φ₁ a + φ₂ b + φ₃ c = t

/-- Orthogonal vectors: some `a ∈ A`, `b ∈ B` have no common `true` coordinate. -/
def OV {d : ℕ} (A B : Finset (Fin d → Bool)) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, ∀ j, ¬(a j = true ∧ b j = true)

/-- `Prob P` is 3SUM over `A^d` with target `(t, …, t)` on the coordinatewise images. -/
theorem prob_iff_threeSum {A : Type v} [AddCommGroup A] [DecidableEq A]
    {P : α → α → α → Prop} {φ₁ φ₂ φ₃ : α → A} {t : A}
    (h : ∀ a b c, P a b c ↔ φ₁ a + φ₂ b + φ₃ c = t) {d : ℕ} (S₁ S₂ S₃ : Finset (Fin d → α)) :
    Prob P S₁ S₂ S₃ ↔
      ∃ y₁ ∈ S₁.image (fun x => φ₁ ∘ x), ∃ y₂ ∈ S₂.image (fun x => φ₂ ∘ x),
        ∃ y₃ ∈ S₃.image (fun x => φ₃ ∘ x), y₁ + y₂ + y₃ = fun _ => t := by
  constructor
  · rintro ⟨x₁, h₁, x₂, h₂, x₃, h₃, hP⟩
    exact ⟨_, Finset.mem_image_of_mem _ h₁, _, Finset.mem_image_of_mem _ h₂, _,
      Finset.mem_image_of_mem _ h₃, funext fun j => (h _ _ _).1 (hP j)⟩
  · rintro ⟨y₁, hy₁, y₂, hy₂, y₃, hy₃, hs⟩
    obtain ⟨x₁, h₁, rfl⟩ := Finset.mem_image.1 hy₁
    obtain ⟨x₂, h₂, rfl⟩ := Finset.mem_image.1 hy₂
    obtain ⟨x₃, h₃, rfl⟩ := Finset.mem_image.1 hy₃
    exact ⟨x₁, h₁, x₂, h₂, x₃, h₃, fun j => (h _ _ _).2 (congrFun hs j)⟩

/-- A system of `k` equations over `A` gives a representation over `Fin k → A`. -/
theorem representable_of_system {A : Type v} [AddCommGroup A] {P : α → α → α → Prop} {k : ℕ}
    (α₁ α₂ α₃ : Fin k → α → A) (t : Fin k → A)
    (h : ∀ a b c, P a b c ↔ ∀ i, α₁ i a + α₂ i b + α₃ i c = t i) :
    RepresentableOver (Fin k → A) P :=
  ⟨fun a i => α₁ i a, fun b i => α₂ i b, fun c i => α₃ i c, t, fun a b c => by
    rw [h]; exact ⟨fun H => funext H, fun H i => congrFun H i⟩⟩

/-- Representability transfers along equality of relations (convenience). -/
theorem RepresentableOver.of_iff {A : Type v} [AddCommGroup A] {P Q : α → α → α → Prop}
    (hPQ : ∀ a b c, P a b c ↔ Q a b c) (h : RepresentableOver A P) : RepresentableOver A Q := by
  obtain ⟨φ₁, φ₂, φ₃, t, h⟩ := h
  exact ⟨φ₁, φ₂, φ₃, t, fun a b c => (hPQ a b c).symm.trans (h a b c)⟩

end Basic

/-! ## One-coordinate OV gadgets -/

/-- Which input a position of a gadget reads: a bit of `a ∈ A`, a bit of `b ∈ B`, or nothing
(constant). -/
inductive Side | A | B | C
  deriving DecidableEq, Repr

/-- `pick s a b c` is `a`, `b` or `c` according to the side `s`. -/
def pick {β : Sort*} (s : Side) (a b c : β) : β :=
  match s with
  | .A => a
  | .B => b
  | .C => c

def Side.idx : Side → ℕ
  | .A => 0
  | .B => 1
  | .C => 2

lemma Side.idx_lt (s : Side) : s.idx < 3 := by cases s <;> decide

def sideOfNat : ℕ → Side
  | 0 => .A
  | 1 => .B
  | _ => .C

@[simp] lemma pick_A {β : Sort*} (a b c : β) : pick .A a b c = a := rfl
@[simp] lemma pick_B {β : Sort*} (a b c : β) : pick .B a b c = b := rfl
@[simp] lemma pick_C {β : Sort*} (a b c : β) : pick .C a b c = c := rfl

/-- A one-coordinate gadget: a side for each of the three positions and a map `Bool → α` per
position (for side `C` the map must be constant). A *slice* has sides a permutation of
`A, B, C`; an *identification* has one of `A`, `B` on two positions (two vectors of the same list
are read there, and validity forces their bits to agree). -/
structure Gadget (α : Type u) where
  side : Fin 3 → Side
  f : Fin 3 → Bool → α

/-- The bit assignment `u` (one bit per position) agrees with `a` on the `A`-positions and with
`b` on the `B`-positions. -/
def Agrees (s : Fin 3 → Side) (a b : Bool) (u : Fin 3 → Bool) : Prop :=
  ∀ i, (s i = .A → u i = a) ∧ (s i = .B → u i = b)

/-- The target relation of a gadget: the `A`-bits are equal (to `a`), the `B`-bits are equal (to
`b`), and `¬(a ∧ b)`. -/
def Target (s : Fin 3 → Side) (u : Fin 3 → Bool) : Prop :=
  ∃ a b : Bool, ¬(a = true ∧ b = true) ∧ Agrees s a b u

/-- Correctness of a one-coordinate gadget for `P`: both `A` and `B` are read, constant positions
have constant maps, and `P` on the images is exactly the target relation. For a slice with the
constant at position 3 this says `P (f₁ a) (f₂ b) c₀ ↔ ¬(a ∧ b)`; for an identification with
positions 2, 3 reading `b, b'` it says `P (f₁ a) (f₂ b) (f₃ b') ↔ b = b' ∧ ¬(a ∧ b)`. -/
def Gadget.Valid {α : Type u} (g : Gadget α) (P : α → α → α → Prop) : Prop :=
  (∃ i, g.side i = .A) ∧ (∃ i, g.side i = .B) ∧ (∀ i, g.side i = .C → g.f i false = g.f i true) ∧
    ∀ u : Fin 3 → Bool, P (g.f 0 (u 0)) (g.f 1 (u 1)) (g.f 2 (u 2)) ↔ Target g.side u

/-- `P` has a one-coordinate OV gadget. -/
def HasGadget {α : Type u} (P : α → α → α → Prop) : Prop := ∃ g : Gadget α, g.Valid P

theorem HasGadget.of_iff {α : Type u} {P Q : α → α → α → Prop}
    (hPQ : ∀ a b c, P a b c ↔ Q a b c) (h : HasGadget P) : HasGadget Q := by
  obtain ⟨g, h1, h2, h3, h4⟩ := h
  exact ⟨g, h1, h2, h3, fun u => (hPQ _ _ _).symm.trans (h4 u)⟩

section GadgetLists

variable {α : Type u} [DecidableEq α]

/-- The list at position `i` built from the OV lists `A`, `B`. -/
def Gadget.list (g : Gadget α) (i : Fin 3) {d : ℕ} (A B : Finset (Fin d → Bool)) :
    Finset (Fin d → α) :=
  match g.side i with
  | .A => A.image (fun a j => g.f i (a j))
  | .B => B.image (fun b j => g.f i (b j))
  | .C => {fun _ => g.f i false}

lemma Gadget.mem_list {g : Gadget α} {i : Fin 3} {d : ℕ} {A B : Finset (Fin d → Bool)}
    {x : Fin d → α} (hx : x ∈ g.list i A B) :
    ∃ v : Fin d → Bool, (g.side i = .A → v ∈ A) ∧ (g.side i = .B → v ∈ B) ∧
      x = fun j => g.f i (v j) := by
  unfold Gadget.list at hx
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

lemma Gadget.mem_list_of {g : Gadget α} {i : Fin 3} {d : ℕ} {A B : Finset (Fin d → Bool)}
    (v : Fin d → Bool) (hA : g.side i = .A → v ∈ A) (hB : g.side i = .B → v ∈ B)
    (hC : g.side i = .C → v = fun _ => false) : (fun j => g.f i (v j)) ∈ g.list i A B := by
  unfold Gadget.list
  split
  next h => exact Finset.mem_image.2 ⟨v, hA h, rfl⟩
  next h => exact Finset.mem_image.2 ⟨v, hB h, rfl⟩
  next h => rw [hC h]; exact Finset.mem_singleton.2 rfl

/-- **Gadget correctness.** For a valid gadget, OV on `A, B` holds iff `Prob P` holds on the
three image lists (exact correspondence, every dimension `d`). This covers slices with the
constant in any position and identifications with the doubled side in any two positions. -/
theorem Gadget.ov_iff_prob {g : Gadget α} {P : α → α → α → Prop} (hg : g.Valid P) {d : ℕ}
    (A B : Finset (Fin d → Bool)) :
    OV A B ↔ Prob P (g.list 0 A B) (g.list 1 A B) (g.list 2 A B) := by
  obtain ⟨⟨i₀, hi₀⟩, ⟨i₁, hi₁⟩, -, hv⟩ := hg
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    let V : Fin 3 → Fin d → Bool := fun i => pick (g.side i) a b (fun _ => false)
    have hmem : ∀ i, (fun j => g.f i (V i j)) ∈ g.list i A B := by
      intro i
      refine Gadget.mem_list_of _ (fun h => ?_) (fun h => ?_) (fun h => ?_) <;>
        simp only [V, h, pick_A, pick_B, pick_C] <;> assumption
    refine ⟨_, hmem 0, _, hmem 1, _, hmem 2, fun j => (hv fun i => V i j).2 ?_⟩
    refine ⟨a j, b j, hab j, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩ <;> simp [V, h]
  · rintro ⟨x₀, h₀, x₁, h₁, x₂, h₂, hP⟩
    obtain ⟨v₀, hA₀, hB₀, rfl⟩ := Gadget.mem_list h₀
    obtain ⟨v₁, hA₁, hB₁, rfl⟩ := Gadget.mem_list h₁
    obtain ⟨v₂, hA₂, hB₂, rfl⟩ := Gadget.mem_list h₂
    let V : Fin 3 → Fin d → Bool := ![v₀, v₁, v₂]
    have hA : ∀ i, g.side i = .A → V i ∈ A := by
      intro i; fin_cases i
      exacts [hA₀, hA₁, hA₂]
    have hB : ∀ i, g.side i = .B → V i ∈ B := by
      intro i; fin_cases i
      exacts [hB₀, hB₁, hB₂]
    refine ⟨V i₀, hA i₀ hi₀, V i₁, hB i₁ hi₁, fun j => ?_⟩
    obtain ⟨a, b, hab, hag⟩ := (hv fun i => V i j).1 (hP j)
    have e1 : V i₀ j = a := (hag i₀).1 hi₀
    have e2 : V i₁ j = b := (hag i₁).2 hi₁
    rw [e1, e2]
    exact hab

end GadgetLists

section Exclusive

variable {α : Type u}

private lemma pick_lin {A : Type v} [AddCommGroup A] (s : Side) (ψ : Bool → A) :
    ψ (pick s true true false) =
      ψ (pick s true false false) + ψ (pick s false true false) - ψ (pick s false false false) := by
  cases s <;> simp

/-- **Exclusivity.** No relation representable over an abelian group has a one-coordinate OV
gadget: substituting the gadget maps gives a representation `α(a) + β(b) + γ = t ↔ ¬(a ∧ b)` of
the OV relation on bits, and `(0,0), (0,1), (1,0)` then force `(1,1)`. -/
theorem Gadget.not_valid_of_rep {A : Type v} [AddCommGroup A] {P : α → α → α → Prop}
    (hP : RepresentableOver A P) (g : Gadget α) : ¬ g.Valid P := by
  rintro ⟨⟨i₀, hi₀⟩, ⟨i₁, hi₁⟩, -, hv⟩
  obtain ⟨φ₁, φ₂, φ₃, t, hφ⟩ := hP
  let u : Bool → Bool → Fin 3 → Bool := fun a b i => pick (g.side i) a b false
  have key : ∀ a b, Target g.side (u a b) ↔ ¬(a = true ∧ b = true) := by
    intro a b
    constructor
    · rintro ⟨a', b', hn, hag⟩
      have e1 := (hag i₀).1 hi₀
      have e2 := (hag i₁).2 hi₁
      simp only [u, hi₀, hi₁, pick_A, pick_B] at e1 e2
      rw [e1, e2]; exact hn
    · intro h
      exact ⟨a, b, h, fun i => ⟨fun hA => by simp [u, hA], fun hB => by simp [u, hB]⟩⟩
  let S : Bool → Bool → A := fun a b =>
    φ₁ (g.f 0 (u a b 0)) + φ₂ (g.f 1 (u a b 1)) + φ₃ (g.f 2 (u a b 2))
  have hS : ∀ a b, S a b = t ↔ ¬(a = true ∧ b = true) := fun a b =>
    (hφ _ _ _).symm.trans ((hv _).trans (key a b))
  have h00 := (hS false false).2 (by simp)
  have h01 := (hS false true).2 (by simp)
  have h10 := (hS true false).2 (by simp)
  have l0 := pick_lin (g.side 0) (fun x => φ₁ (g.f 0 x))
  have l1 := pick_lin (g.side 1) (fun x => φ₂ (g.f 1 x))
  have l2 := pick_lin (g.side 2) (fun x => φ₃ (g.f 2 x))
  apply (hS true true).1 _ ⟨rfl, rfl⟩
  simp only [S, u] at h00 h01 h10 ⊢
  rw [l0, l1, l2]
  calc _ = (φ₁ (g.f 0 (pick (g.side 0) true false false)) +
          φ₂ (g.f 1 (pick (g.side 1) true false false)) +
          φ₃ (g.f 2 (pick (g.side 2) true false false))) +
        (φ₁ (g.f 0 (pick (g.side 0) false true false)) +
          φ₂ (g.f 1 (pick (g.side 1) false true false)) +
          φ₃ (g.f 2 (pick (g.side 2) false true false))) -
        (φ₁ (g.f 0 (pick (g.side 0) false false false)) +
          φ₂ (g.f 1 (pick (g.side 1) false false false)) +
          φ₃ (g.f 2 (pick (g.side 2) false false false))) := by abel
    _ = t := by rw [h00, h01, h10]; abel

theorem not_hasGadget_of_rep {A : Type v} [AddCommGroup A] {P : α → α → α → Prop}
    (hP : RepresentableOver A P) : ¬ HasGadget P :=
  fun ⟨g, hg⟩ => Gadget.not_valid_of_rep hP g hg

end Exclusive

/-! ## No-carry base-`B` encoding -/

/-- If every `|w j| < B / 2`, the base-`B` number `Σ w j B^j` vanishes only for `w = 0`. -/
theorem sum_mul_pow_eq_zero_iff {d : ℕ} {B : ℤ} (w : Fin d → ℤ) (hw : ∀ j, 2 * |w j| < B) :
    ∑ j, w j * B ^ (j : ℕ) = 0 ↔ ∀ j, w j = 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hB : 0 < B := by have := hw 0; have := abs_nonneg (w 0); linarith
    have hrest : ∑ j : Fin d, w j.succ * B ^ ((j.succ : Fin (d + 1)) : ℕ) =
        B * ∑ j : Fin d, w j.succ * B ^ (j : ℕ) := by
      rw [Finset.mul_sum]; congr 1; ext j; simp only [Fin.val_succ, pow_succ]; ring
    rw [Fin.sum_univ_succ, hrest, Fin.forall_fin_succ]
    simp only [Fin.val_zero, pow_zero, mul_one]
    have ih' := ih (fun j => w j.succ) (fun j => hw j.succ)
    constructor
    · intro h
      have h0 : w 0 = 0 := by
        obtain ⟨k, hk⟩ : B ∣ w 0 := ⟨-∑ j : Fin d, w j.succ * B ^ (j : ℕ), by linarith⟩
        have h1 := hw 0
        rw [hk, abs_mul, abs_of_pos hB] at h1
        have hk1 : |k| < 1 := by nlinarith [abs_nonneg k]
        have : k = 0 := by rw [abs_lt] at hk1; omega
        rw [hk, this, mul_zero]
      refine ⟨h0, ih'.1 ?_⟩
      rw [h0, zero_add] at h
      exact (mul_eq_zero.1 h).resolve_left hB.ne'
    · rintro ⟨h0, hs⟩
      rw [h0, ih'.2 hs]; simp

/-- The base-`B` number of an integer vector. -/
def baseB {d : ℕ} (B : ℤ) (x : Fin d → ℤ) : ℤ := ∑ j, x j * B ^ (j : ℕ)

/-- **3SUM over `ℤ^d` is integer 3SUM with one target.** For entries bounded by `M` and
`B > 8M`, `x₁ + x₂ + x₃ = t` coordinatewise iff the base-`B` numbers satisfy
`X₁ + X₂ + X₃ = T`. -/
theorem threeSum_iff_baseB {d : ℕ} {B M : ℤ} (hB : 8 * M < B) (x₁ x₂ x₃ t : Fin d → ℤ)
    (h₁ : ∀ j, |x₁ j| ≤ M) (h₂ : ∀ j, |x₂ j| ≤ M) (h₃ : ∀ j, |x₃ j| ≤ M)
    (ht : ∀ j, |t j| ≤ M) :
    x₁ + x₂ + x₃ = t ↔ baseB B x₁ + baseB B x₂ + baseB B x₃ = baseB B t := by
  have hw : ∀ j, 2 * |x₁ j + x₂ j + x₃ j - t j| < B := by
    intro j
    have a1 := abs_le.1 (h₁ j); have a2 := abs_le.1 (h₂ j)
    have a3 := abs_le.1 (h₃ j); have a4 := abs_le.1 (ht j)
    have : |x₁ j + x₂ j + x₃ j - t j| ≤ 4 * M := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have key := sum_mul_pow_eq_zero_iff _ hw
  have hsum : ∑ j, (x₁ j + x₂ j + x₃ j - t j) * B ^ (j : ℕ) =
      baseB B x₁ + baseB B x₂ + baseB B x₃ - baseB B t := by
    simp only [baseB, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    congr 1; ext j; ring
  rw [hsum, sub_eq_zero] at key
  rw [key, funext_iff]
  simp only [Pi.add_apply, sub_eq_zero]

/-! ## Kernel-checkable certificates

Relations on `Fin n` are given by Boolean functions on `ℕ` (`NRel`). The checkers below are
`Bool`-valued (`decide` of explicit propositions with small quantifiers) and proved sound, so a
whole classification is one `decide +kernel` (kernel reduction, no extra axioms). -/

/-- The relation on `Fin n` given by a Boolean function on `ℕ`. -/
def NRel (n : ℕ) (P : ℕ → ℕ → ℕ → Bool) : Fin n → Fin n → Fin n → Prop :=
  fun a b c => P a b c = true

/-- An equation system: each equation `(w₁, w₂, w₃, t)` reads `w₁[a] + w₂[b] + w₃[c] = t`. -/
abbrev Sys := List (List ℤ × List ℤ × List ℤ × ℤ)

/-- All equations of `sys` hold at `(a, b, c)` modulo `m` (`m = 0`: over `ℤ`). -/
def SysHolds (m : ℕ) (sys : Sys) (a b c : ℕ) : Prop :=
  ∀ e ∈ sys, (e.1.getD a 0 + e.2.1.getD b 0 + e.2.2.1.getD c 0 - e.2.2.2) % (m : ℤ) = 0

instance (m : ℕ) (sys : Sys) (a b c : ℕ) : Decidable (SysHolds m sys a b c) := by
  unfold SysHolds; infer_instance

/-- The system `sys` modulo `m` cuts out exactly `P` on `{0..n-1}³`. -/
def checkSys (n m : ℕ) (P : ℕ → ℕ → ℕ → Bool) (sys : Sys) : Bool :=
  decide (∀ a < n, ∀ b < n, ∀ c < n, (P a b c = true ↔ SysHolds m sys a b c))

private lemma zmod_sum_eq_iff (m : ℕ) (x y z t : ℤ) :
    ((x : ZMod m) + (y : ZMod m) + (z : ZMod m) = (t : ZMod m)) ↔ (x + y + z - t) % (m : ℤ) = 0 := by
  rw [← Int.dvd_iff_emod_eq_zero, ← ZMod.intCast_zmod_eq_zero_iff_dvd, ← sub_eq_zero]
  push_cast; rfl

theorem rep_of_checkSys {n m : ℕ} {P : ℕ → ℕ → ℕ → Bool} {sys : Sys}
    (h : checkSys n m P sys = true) : RepresentableOver (Fin sys.length → ZMod m) (NRel n P) := by
  have h' := of_decide_eq_true h
  refine representable_of_system (fun i a => ((sys[i].1.getD a 0 : ℤ) : ZMod m))
    (fun i b => ((sys[i].2.1.getD b 0 : ℤ) : ZMod m))
    (fun i c => ((sys[i].2.2.1.getD c 0 : ℤ) : ZMod m)) (fun i => ((sys[i].2.2.2 : ℤ) : ZMod m)) ?_
  intro a b c
  rw [NRel, h' a a.2 b b.2 c c.2, SysHolds, List.forall_mem_iff_getElem]
  simp only [zmod_sum_eq_iff]
  exact ⟨fun H i => H i i.2, fun H i hi => H ⟨i, hi⟩⟩

/-- Bool version of `Target` (sides and bits given position by position). -/
def targetB (s₀ s₁ s₂ : Side) (u₀ u₁ u₂ : Bool) : Bool :=
  [(false, false), (false, true), (true, false)].any fun p =>
    pick s₀ (u₀ == p.1) (u₀ == p.2) true && pick s₁ (u₁ == p.1) (u₁ == p.2) true &&
      pick s₂ (u₂ == p.1) (u₂ == p.2) true

lemma target_iff (s : Fin 3 → Side) (u₀ u₁ u₂ : Bool) :
    Target s ![u₀, u₁, u₂] ↔ targetB (s 0) (s 1) (s 2) u₀ u₁ u₂ = true := by
  have hf : ∀ (Q : Fin 3 → Prop), (∀ i, Q i) ↔ Q 0 ∧ Q 1 ∧ Q 2 := fun Q =>
    ⟨fun h => ⟨h 0, h 1, h 2⟩, fun h i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2]⟩
  simp only [Target, Agrees, hf]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  generalize s 0 = s₀; generalize s 1 = s₁; generalize s 2 = s₂
  cases s₀ <;> cases s₁ <;> cases s₂ <;> cases u₀ <;> cases u₁ <;> cases u₂ <;> decide

/-- The validity conditions of a gadget with sides `s` and maps `f i false = x i`,
`f i true = y i` (values in `{0..n-1}`), as an explicit proposition with small quantifiers. -/
def CheckP (n : ℕ) (P : ℕ → ℕ → ℕ → Bool) (s : Fin 3 → Side) (x y : Fin 3 → ℕ) : Prop :=
  (s 0 = .A ∨ s 1 = .A ∨ s 2 = .A) ∧ (s 0 = .B ∨ s 1 = .B ∨ s 2 = .B) ∧
  (s 0 = .C → x 0 = y 0) ∧ (s 1 = .C → x 1 = y 1) ∧ (s 2 = .C → x 2 = y 2) ∧
  (x 0 < n ∧ y 0 < n) ∧ (x 1 < n ∧ y 1 < n) ∧ (x 2 < n ∧ y 2 < n) ∧
  ∀ u₀ u₁ u₂ : Bool, P (cond u₀ (y 0) (x 0)) (cond u₁ (y 1) (x 1)) (cond u₂ (y 2) (x 2)) =
    targetB (s 0) (s 1) (s 2) u₀ u₁ u₂

instance (n : ℕ) (P : ℕ → ℕ → ℕ → Bool) (s : Fin 3 → Side) (x y : Fin 3 → ℕ) :
    Decidable (CheckP n P s x y) := by
  unfold CheckP; infer_instance

/-- Gadget checker. -/
def checkG (n : ℕ) (P : ℕ → ℕ → ℕ → Bool) (s : Fin 3 → Side) (x y : Fin 3 → ℕ) : Bool :=
  decide (CheckP n P s x y)

private lemma fin3_exists (Q : Fin 3 → Prop) : (∃ i, Q i) ↔ Q 0 ∨ Q 1 ∨ Q 2 :=
  ⟨fun ⟨i, h⟩ => by fin_cases i <;> simp_all, fun h => by
    rcases h with h | h | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]⟩

private lemma fin3_forall (Q : Fin 3 → Prop) : (∀ i, Q i) ↔ Q 0 ∧ Q 1 ∧ Q 2 :=
  ⟨fun h => ⟨h 0, h 1, h 2⟩, fun h i => by fin_cases i <;> simp [h.1, h.2.1, h.2.2]⟩

private lemma val_cond {n : ℕ} (f : Bool → Fin n) (u : Bool) :
    (f u).val = cond u (f true).val (f false).val := by cases u <;> rfl

/-- The checker accepts exactly the valid gadgets (values read off as natural numbers). -/
theorem checkP_iff_valid {n : ℕ} (P : ℕ → ℕ → ℕ → Bool) (g : Gadget (Fin n)) :
    CheckP n P g.side (fun i => (g.f i false).val) (fun i => (g.f i true).val) ↔
      g.Valid (NRel n P) := by
  unfold CheckP Gadget.Valid
  rw [fin3_exists, fin3_exists, fin3_forall (fun i => g.side i = .C → g.f i false = g.f i true)]
  simp only [Fin.val_inj, Fin.isLt, and_self, true_and]
  apply and_congr_right; intro _; apply and_congr_right; intro _
  rw [and_assoc, and_assoc]
  apply and_congr_right; intro _; apply and_congr_right; intro _; apply and_congr_right; intro _
  constructor
  · intro H u
    have hu : u = ![u 0, u 1, u 2] := by funext i; fin_cases i <;> rfl
    rw [hu, target_iff, NRel]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [val_cond (g.f 0), val_cond (g.f 1), val_cond (g.f 2), H]
  · intro H u₀ u₁ u₂
    have := H ![u₀, u₁, u₂]
    rw [target_iff, NRel] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons] at this
    rw [val_cond (g.f 0), val_cond (g.f 1), val_cond (g.f 2)] at this
    exact Bool.eq_iff_iff.2 this

theorem hasGadget_of_checkG {n : ℕ} {P : ℕ → ℕ → ℕ → Bool} {s : Fin 3 → Side} {x y : Fin 3 → ℕ}
    (h : checkG n P s x y = true) : HasGadget (NRel n P) := by
  have h' := of_decide_eq_true h
  have hx : ∀ i, x i < n := by
    intro i; fin_cases i
    exacts [h'.2.2.2.2.2.1.1, h'.2.2.2.2.2.2.1.1, h'.2.2.2.2.2.2.2.1.1]
  have hy : ∀ i, y i < n := by
    intro i; fin_cases i
    exacts [h'.2.2.2.2.2.1.2, h'.2.2.2.2.2.2.1.2, h'.2.2.2.2.2.2.2.1.2]
  let g : Gadget (Fin n) := ⟨s, fun i b => cond b ⟨y i, hy i⟩ ⟨x i, hx i⟩⟩
  exact ⟨g, (checkP_iff_valid P g).1 h'⟩

/-- Both `A` and `B` occur among the sides. -/
def sidesOK (s₀ s₁ s₂ : Side) : Bool :=
  (s₀ == .A || s₁ == .A || s₂ == .A) && (s₀ == .B || s₁ == .B || s₂ == .B)

/-- One bit pattern of the gadget condition. -/
def okU (P : ℕ → ℕ → ℕ → Bool) (s : Fin 3 → Side) (x y : Fin 3 → ℕ) (u₀ u₁ u₂ : Bool) : Bool :=
  P (cond u₀ (y 0) (x 0)) (cond u₁ (y 1) (x 1)) (cond u₂ (y 2) (x 2)) ==
    targetB (s 0) (s 1) (s 2) u₀ u₁ u₂

/-- Exhaustive gadget search with pruning: the values `f i false` are chosen first and the bit
pattern `000` is tested, then `f 0 true` (pattern `100`), then `f 1 true` (`010`, `110`), then
`f 2 true` (full check). -/
def noGadgetB (n : ℕ) (P : ℕ → ℕ → ℕ → Bool) : Bool :=
  (List.range 3).all fun a₀ => (List.range 3).all fun a₁ => (List.range 3).all fun a₂ =>
    !sidesOK (sideOfNat a₀) (sideOfNat a₁) (sideOfNat a₂) ||
    (List.range n).all fun x₀ => (List.range n).all fun x₁ => (List.range n).all fun x₂ =>
      !okU P ![sideOfNat a₀, sideOfNat a₁, sideOfNat a₂] ![x₀, x₁, x₂] ![x₀, x₁, x₂]
        false false false ||
      (List.range n).all fun y₀ =>
        !okU P ![sideOfNat a₀, sideOfNat a₁, sideOfNat a₂] ![x₀, x₁, x₂] ![y₀, x₁, x₂]
          true false false ||
        (List.range n).all fun y₁ =>
          !(okU P ![sideOfNat a₀, sideOfNat a₁, sideOfNat a₂] ![x₀, x₁, x₂] ![y₀, y₁, x₂]
              false true false &&
            okU P ![sideOfNat a₀, sideOfNat a₁, sideOfNat a₂] ![x₀, x₁, x₂] ![y₀, y₁, x₂]
              true true false) ||
          (List.range n).all fun y₂ =>
            !checkG n P ![sideOfNat a₀, sideOfNat a₁, sideOfNat a₂] ![x₀, x₁, x₂] ![y₀, y₁, y₂]

theorem not_hasGadget_of_noGadgetB {n : ℕ} {P : ℕ → ℕ → ℕ → Bool} (h : noGadgetB n P = true) :
    ¬ HasGadget (NRel n P) := by
  rintro ⟨g, hg⟩
  have hc := (checkP_iff_valid P g).2 hg
  have hs : ∀ s : Side, sideOfNat s.idx = s := by intro s; cases s <;> rfl
  have hc' : CheckP n P ![sideOfNat (g.side 0).idx, sideOfNat (g.side 1).idx,
      sideOfNat (g.side 2).idx] ![(g.f 0 false).val, (g.f 1 false).val, (g.f 2 false).val]
      ![(g.f 0 true).val, (g.f 1 true).val, (g.f 2 true).val] := by
    rw [hs, hs, hs]; exact hc
  have hok : sidesOK (sideOfNat (g.side 0).idx) (sideOfNat (g.side 1).idx)
      (sideOfNat (g.side 2).idx) = true := by
    simp only [sidesOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc]
    exact ⟨hc'.1, hc'.2.1⟩
  have H := hc'.2.2.2.2.2.2.2.2
  simp only [noGadgetB, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', Bool.and_eq_false_iff] at h
  have h1 := (h _ (g.side 0).idx_lt _ (g.side 1).idx_lt _ (g.side 2).idx_lt).resolve_left
    (by rw [hok]; decide)
  have h2 := (h1 _ (g.f 0 false).2 _ (g.f 1 false).2 _ (g.f 2 false).2).resolve_left
    (by simp only [okU, beq_iff_eq, Bool.not_eq_false]; exact H false false false)
  have h3 := (h2 _ (g.f 0 true).2).resolve_left
    (by simp only [okU, beq_iff_eq, Bool.not_eq_false]; exact H true false false)
  have h4 := (h3 _ (g.f 1 true).2).resolve_left (by
    simp only [okU, beq_iff_eq, Bool.not_eq_false, not_or]
    exact ⟨H false true false, H true true false⟩)
  have := h4 _ (g.f 2 true).2
  rw [checkG, decide_eq_false_iff_not] at this
  exact this hc'

/-! ### Whole tables of certificates -/

/-- All words of length `k` over `{0..n-1}`, in lexicographic order (as `itertools.product`). -/
def words (n : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => (List.range n).flatMap fun x => (words n k).map (x :: ·)

theorem mem_words {n k : ℕ} {w : List ℕ} : w ∈ words n k ↔ w.length = k ∧ ∀ x ∈ w, x < n := by
  induction k generalizing w with
  | zero =>
    simp only [words, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 h
  | succ k ih =>
    simp only [words, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨x, hx, v, hv, rfl⟩
      obtain ⟨h1, h2⟩ := ih.1 hv
      refine ⟨by simp [h1], ?_⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      exacts [hx, h2 y hy]
    · rintro ⟨h1, h2⟩
      cases w with
      | nil => simp at h1
      | cons x v =>
        refine ⟨x, h2 x (by simp), v, ih.2 ⟨by simpa using h1, fun y hy => h2 y (by simp [hy])⟩, rfl⟩

/-- Decoding of a gadget code `s + 27 * (x₀ + n y₀ + n² x₁ + n³ y₁ + n⁴ x₂ + n⁵ y₂)`,
`s = 9 s₀ + 3 s₁ + s₂` (`0 = A`, `1 = B`, `2 = C`). -/
def decSides (code : ℕ) : Fin 3 → Side :=
  ![sideOfNat (code % 27 / 9), sideOfNat (code % 27 / 3 % 3), sideOfNat (code % 3)]

def decX (n code : ℕ) : Fin 3 → ℕ :=
  ![code / 27 % n, code / 27 / n ^ 2 % n, code / 27 / n ^ 4 % n]

def decY (n code : ℕ) : Fin 3 → ℕ :=
  ![code / 27 / n % n, code / 27 / n ^ 3 % n, code / 27 / n ^ 5 % n]

/-- The property established for every relation of a classification: representable over
`Fin k → ZMod m` for a modulus `m ∈ ms` (`ZMod 0 = ℤ`), or a one-coordinate OV gadget. -/
def Good (ms : List ℕ) {n : ℕ} (P : Fin n → Fin n → Fin n → Prop) : Prop :=
  (∃ m ∈ ms, ∃ k, RepresentableOver (Fin k → ZMod m) P) ∨ HasGadget P

/-- Digit `j` (base 32, offset 16) of a packed equation system, as an integer in `[-16, 15]`. -/
def digitZ (code j : ℕ) : ℤ := ((code / 32 ^ j % 32 : ℕ) : ℤ) - 16

/-- A packed equation `w₁ (n digits), w₂ (n digits), w₃ (n digits), t`. -/
def decEqn (n code : ℕ) : List ℤ × List ℤ × List ℤ × ℤ :=
  ((List.range n).map fun i => digitZ code i, (List.range n).map fun i => digitZ code (n + i),
    (List.range n).map fun i => digitZ code (2 * n + i), digitZ code (3 * n))

/-- A packed system of `k` equations, `3n+1` digits each. -/
def decSys (n k code : ℕ) : Sys :=
  (List.range k).map fun e => decEqn n (code / 32 ^ ((3 * n + 1) * e))

/-- One table entry: `0` means "look up the equation system for word index `i` in `reps`",
`c + 1` means "gadget with code `c`". -/
def certOK (n : ℕ) (ms : List ℕ) (P : ℕ → ℕ → ℕ → Bool) (reps : List (ℕ × ℕ × ℕ × ℕ))
    (i c : ℕ) : Bool :=
  if c = 0 then
    match reps.lookup i with
    | some (m, k, code) => ms.contains m && checkSys n m P (decSys n k code)
    | none => false
  else checkG n P (decSides (c - 1)) (decX n (c - 1)) (decY n (c - 1))

theorem good_of_certOK {n : ℕ} {ms : List ℕ} {P : ℕ → ℕ → ℕ → Bool} {reps : List (ℕ × ℕ × ℕ × ℕ)}
    {i c : ℕ} (h : certOK n ms P reps i c = true) : Good ms (NRel n P) := by
  unfold certOK at h
  split_ifs at h
  · split at h
    · rename_i m k code _
      simp only [Bool.and_eq_true, List.contains_iff_mem] at h
      exact Or.inl ⟨m, h.1, _, rep_of_checkSys h.2⟩
    · exact absurd h (by simp)
  · exact Or.inr (hasGadget_of_checkG h)

/-- Walk through the word list and the packed table (`base`-ary digits, least significant
first) together. -/
def checkAll (n base : ℕ) (ms : List ℕ) (rel : List ℕ → ℕ → ℕ → ℕ → Bool)
    (reps : List (ℕ × ℕ × ℕ × ℕ)) : ℕ → List (List ℕ) → ℕ → Bool
  | _, [], _ => true
  | i, w :: ws, T => certOK n ms (rel w) reps i (T % base) && checkAll n base ms rel reps (i + 1) ws (T / base)

theorem good_of_checkAll {n base : ℕ} {ms : List ℕ} {rel : List ℕ → ℕ → ℕ → ℕ → Bool}
    {reps : List (ℕ × ℕ × ℕ × ℕ)} {i : ℕ} {ws : List (List ℕ)} {T : ℕ}
    (h : checkAll n base ms rel reps i ws T = true) : ∀ w ∈ ws, Good ms (NRel n (rel w)) := by
  induction ws generalizing i T with
  | nil => simp
  | cons w ws ih =>
    simp only [checkAll, Bool.and_eq_true] at h
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    exacts [good_of_certOK h.1, ih h.2 v hv]

/-- Representable over `ℤ^k` for some `k`. -/
def RepZ {α : Type u} (P : α → α → α → Prop) : Prop := ∃ k, RepresentableOver (Fin k → ℤ) P

/-- Representable over `(ZMod p)^k` for some `k`. -/
def RepMod (p : ℕ) {α : Type u} (P : α → α → α → Prop) : Prop :=
  ∃ k, RepresentableOver (Fin k → ZMod p) P

theorem good_cases {n : ℕ} {P : Fin n → Fin n → Fin n → Prop} (h : Good [0, 2, 3] P) :
    (RepZ P ∨ RepMod 2 P ∨ RepMod 3 P) ∨ HasGadget P := by
  rcases h with ⟨m, hm, k, hk⟩ | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    exacts [Or.inl (Or.inl ⟨k, hk⟩), Or.inl (Or.inr (Or.inl ⟨k, hk⟩)),
      Or.inl (Or.inr (Or.inr ⟨k, hk⟩))]
  · exact Or.inr h

/-- From a classification certificate: representable over some abelian group iff no gadget. -/
theorem rep_iff_not_hasGadget_of_good {ms : List ℕ} {n : ℕ} {P : Fin n → Fin n → Fin n → Prop}
    (h : Good ms P) :
    (∃ (A : Type) (_ : AddCommGroup A), RepresentableOver A P) ↔ ¬ HasGadget P := by
  constructor
  · rintro ⟨A, _, hA⟩
    exact not_hasGadget_of_rep hA
  · intro hn
    rcases h with ⟨m, -, k, hk⟩ | h
    exacts [⟨_, inferInstance, hk⟩, absurd h hn]

end GroupLean

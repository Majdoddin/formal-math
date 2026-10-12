import XorLean.Defs

/-!
# T6: Lemma 10 (`lem:conv`) and Corollary 11 (`cor:conv`)
-/

namespace Xor

/-- Characteristic 2 in `ZMod 2`. -/
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

/-- Characteristic 2 in `Vec k`. -/
theorem vec_add_self {k : ℕ} (x : Vec k) : x + x = 0 := by
  funext i
  exact zmod2_add_self (x i)

/-- Transport along an additive equivalence of index groups (used for
`Vec (k₁ + k₁) ≃+ Vec k₁ × Vec k₁` and `Vec (k + 1) ≃+ Vec k × ZMod 2`). -/
theorem convHasSol_congr {ι ι' : Type*} [Add ι] [Add ι'] {d : ℕ} (e : ι ≃+ ι')
    (A B C : ι' → Option (Vec d)) :
    ConvHasSol (A ∘ e) (B ∘ e) (C ∘ e) ↔ ConvHasSol A B C := by
  constructor
  · rintro ⟨i, j, a, b, c, hA, hB, hC, h⟩
    refine ⟨e i, e j, a, b, c, hA, hB, ?_, h⟩
    rw [← map_add]
    exact hC
  · rintro ⟨i, j, a, b, c, hA, hB, hC, h⟩
    refine ⟨e.symm i, e.symm j, a, b, c, ?_, ?_, ?_, h⟩
    · simpa using hA
    · simpa using hB
    · simpa [map_add] using hC

def splitEquiv (k₁ : ℕ) : Vec (k₁ + k₁) ≃+ Vec k₁ × Vec k₁ where
  toFun v := (fun i => v (Fin.castAdd k₁ i), fun i => v (Fin.natAdd k₁ i))
  invFun p := Fin.append p.1 p.2
  left_inv v := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  right_inv p := by
    ext i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  map_add' x y := rfl

def snocEquiv (k : ℕ) : Vec (k + 1) ≃+ Vec k × ZMod 2 where
  toFun v := (Fin.init v, v (Fin.last k))
  invFun p := Fin.snoc p.1 p.2
  left_inv v := by
    simp
  right_inv p := by
    ext i
    · simp
    · simp
  map_add' x y := rfl

/-- The embedding of entries with the three flags. -/
def flagA : Vec 3 := Pi.single 0 1
def flagB : Vec 3 := Pi.single 1 1
def flagC : Vec 3 := Pi.single 2 1
def emb {d : ℕ} (f : Vec 3) : Option (Vec d) → Vec (d + 3)
  | some v => Fin.append v 0
  | none => Fin.append 0 f

theorem fin_append_add {m n : ℕ} (a b : Fin m → ZMod 2) (c e : Fin n → ZMod 2) :
    Fin.append a c + Fin.append b e = Fin.append (a + b) (c + e) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem fin_append_eq_zero {m n : ℕ} (a : Fin m → ZMod 2) (c : Fin n → ZMod 2) :
    Fin.append a c = 0 ↔ a = 0 ∧ c = 0 := by
  constructor
  · intro h
    constructor
    · funext i
      have := congrFun h (Fin.castAdd n i)
      simpa using this
    · funext i
      have := congrFun h (Fin.natAdd m i)
      simpa using this
  · rintro ⟨rfl, rfl⟩
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem emb_sum_eq_zero_iff {d : ℕ} (x y z : Option (Vec d)) :
    emb flagA x + emb flagB y + emb flagC z = 0 ↔
      ∃ a b c, x = some a ∧ y = some b ∧ z = some c ∧ a + b + c = 0 := by
  cases x <;> cases y <;> cases z <;>
    simp only [emb, fin_append_add, fin_append_eq_zero, reduceCtorEq, false_and, exists_false,
      Option.some.injEq, exists_and_left, exists_eq_left', iff_false, and_false, not_and,
      add_zero, zero_add, and_true] <;> first | decide | (intro _; decide)

/-- The instance for `j₂`; parts `X, Y, Z` are each `Vec k₁` (indices `i₁`, `i₂`, `s₁`). -/
def convInst {k₁ d : ℕ} (A B C : Vec k₁ × Vec k₁ → Option (Vec d)) (j₂ : Vec k₁) :
    TriInst (Vec k₁) (Vec k₁) (Vec k₁) (d + 3) where
  wab i₁ i₂ := emb flagA (A (i₁, i₂))
  wbc i₂ s₁ := emb flagC (C (s₁, i₂ + j₂))
  wac i₁ s₁ := emb flagB (B (s₁ + i₁, j₂))

/-- The bijection `(j₂, i₁, i₂, s₁) ↦ (i, j)`. -/
def convEquiv (k₁ : ℕ) :
    Vec k₁ × Vec k₁ × Vec k₁ × Vec k₁ ≃ (Vec k₁ × Vec k₁) × (Vec k₁ × Vec k₁) where
  toFun t := ((t.2.1, t.2.2.1), (t.2.2.2 + t.2.1, t.1))
  invFun p := (p.2.2, p.1.1, p.1.2, p.1.1 + p.2.1)
  left_inv t := by
    obtain ⟨j₂, i₁, i₂, s₁⟩ := t
    simp only [Prod.mk.injEq, true_and]
    rw [add_left_comm, vec_add_self, add_zero]
  right_inv p := by
    obtain ⟨⟨a, b⟩, ⟨c, e⟩⟩ := p
    simp only [Prod.mk.injEq, true_and, and_true]
    rw [add_comm a c, add_assoc, vec_add_self, add_zero]

theorem convEquiv_add (k₁ : ℕ) (t : Vec k₁ × Vec k₁ × Vec k₁ × Vec k₁) :
    (convEquiv k₁ t).1 + (convEquiv k₁ t).2 = (t.2.2.2, t.2.2.1 + t.1) := by
  obtain ⟨j₂, i₁, i₂, s₁⟩ := t
  simp only [convEquiv, Equiv.coe_fn_mk, Prod.mk_add_mk, Prod.mk.injEq, and_true]
  rw [add_left_comm, vec_add_self, add_zero]

theorem convInst_S {k₁ d : ℕ} (A B C : Vec k₁ × Vec k₁ → Option (Vec d))
    (t : Vec k₁ × Vec k₁ × Vec k₁ × Vec k₁) :
    (convInst A B C t.1).S t.2.1 t.2.2.1 t.2.2.2 =
      emb flagA (A (convEquiv k₁ t).1) + emb flagB (B (convEquiv k₁ t).2) +
      emb flagC (C ((convEquiv k₁ t).1 + (convEquiv k₁ t).2)) := by
  rw [convEquiv_add]
  obtain ⟨j₂, i₁, i₂, s₁⟩ := t
  simp only [TriInst.S, convInst, convEquiv, Equiv.coe_fn_mk]
  abel

/-- Lemma 10: a solution exists iff one of the `N = 2^{k₁}` instances has a zero triangle. -/
theorem conv_iff {k₁ d : ℕ} (A B C : Vec k₁ × Vec k₁ → Option (Vec d)) :
    ConvHasSol A B C ↔ ∃ j₂, (convInst A B C j₂).HasZeroTriangle := by
  have key : ∀ t : Vec k₁ × Vec k₁ × Vec k₁ × Vec k₁,
      (convInst A B C t.1).S t.2.1 t.2.2.1 t.2.2.2 = 0 ↔
        ∃ a b c, A (convEquiv k₁ t).1 = some a ∧ B (convEquiv k₁ t).2 = some b ∧
          C ((convEquiv k₁ t).1 + (convEquiv k₁ t).2) = some c ∧ a + b + c = 0 := by
    intro t
    rw [convInst_S, emb_sum_eq_zero_iff]
  constructor
  · rintro ⟨i, j, h⟩
    set t := (convEquiv k₁).symm (i, j) with ht
    have hij : convEquiv k₁ t = (i, j) := by simp [ht]
    refine ⟨t.1, t.2.1, t.2.2.1, t.2.2.2, (key t).2 ?_⟩
    rw [hij]
    exact h
  · rintro ⟨j₂, i₁, i₂, s₁, h⟩
    have := (key (j₂, i₁, i₂, s₁)).1 h
    exact ⟨_, _, this⟩

/-- Corollary 11, odd `k`: padding with empty entries. -/
def pad {k d : ℕ} (A : Vec k → Option (Vec d)) : Vec k × ZMod 2 → Option (Vec d) :=
  fun p => if p.2 = 0 then A p.1 else none

theorem convHasSol_pad_iff {k d : ℕ} (A B C : Vec k → Option (Vec d)) :
    ConvHasSol (pad A) (pad B) (pad C) ↔ ConvHasSol A B C := by
  constructor
  · rintro ⟨p, q, a, b, c, hA, hB, hC, h⟩
    have hp : p.2 = 0 := by
      by_contra hne
      simp [pad, hne] at hA
    have hq : q.2 = 0 := by
      by_contra hne
      simp [pad, hne] at hB
    simp only [pad, hp, if_true] at hA
    simp only [pad, hq, if_true] at hB
    simp only [pad, Prod.snd_add, hp, hq, add_zero, if_true, Prod.fst_add] at hC
    exact ⟨p.1, q.1, a, b, c, hA, hB, hC, h⟩
  · rintro ⟨i, j, a, b, c, hA, hB, hC, h⟩
    refine ⟨(i, 0), (j, 0), a, b, c, ?_, ?_, ?_, h⟩
    · simpa [pad] using hA
    · simpa [pad] using hB
    · simpa [pad] using hC

end Xor

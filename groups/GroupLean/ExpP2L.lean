import GroupLean.Select
import GroupLean.OneHash
import GroupLean.ExpP2

/-!
# Theorem G (exponent `p²`), Case L: Lemmas 19.21 and 19.22 of the paper

Lists `S₁ S₂ S₃` of `R^d`, `R = ZMod (p²)`, with `T_I ≤ σn²` (few triples with `v̄ = 0`).

* Residue rows `rs` (newest first, `|rs| = k + q`), chosen greedily for the type-II family
  `{v̄}`: `ρ` is the map of the first `k` rows (`rs.drop q`), `ρ''` that of the last `q`
  (`rs.take q`). Bounds (19.eq:resrows): `resrows_bounds`.
* Pair rows `prs` (newest first, `|prs| = q`) from `E × E`, chosen greedily for the potential
  `Ψ_t = p^t Y_t + D p^t S_t + p^{2t} A_t` (`Psi`). Lemma 19.22 (`potential_avg`): the average of
  `Ψ_{t+1}` over the candidates is at most `(1+β)² Ψ_t`, from kernel bias, (F1), (F2) and
  `pair_survival`.
* Lemma 19.21 (`caseL`): the algorithm (OneHash's probes and one detection call, the oracle
  represented by its exact answer `oneHashYes`) answers YES iff a solution exists;
  `Z(π) ≤ (1+e+3e²)σn²`, `F ≤ e(3e+1)σn²/D`, `|𝒫₀| ≤ (p+28)n²/σ ≤ N²/√D` (one call suffices),
  every list has fewer than `(p+1)n/σ ≤ g'` blocks.
-/

set_option linter.unusedSectionVars false

namespace GroupLean
namespace CaseL

open Finset ExpP2 OneHash

/-! ### Generic greedy choice from a multiset of candidates -/

section greedy
variable {α : Type*}

/-- `l` (newest first) was chosen greedily from the candidates `C` for the cost `f`. -/
def IsGreedyL (C : Multiset α) (f : List α → ℝ) : List α → Prop
  | [] => True
  | c :: l => IsGreedyL C f l ∧ c ∈ C ∧ ∀ c' ∈ C, f (c :: l) ≤ f (c' :: l)

/-- Greedy sequences of every length exist. -/
theorem exists_isGreedyL (C : Multiset α) (hC : C ≠ 0) (f : List α → ℝ) (r : ℕ) :
    ∃ l : List α, l.length = r ∧ IsGreedyL C f l := by
  classical
  induction r with
  | zero => exact ⟨[], rfl, trivial⟩
  | succ r ih =>
    obtain ⟨l, hl, hg⟩ := ih
    obtain ⟨c, hc, hmin⟩ := Finset.exists_min_image C.toFinset (fun c => f (c :: l))
      (Multiset.toFinset_nonempty.mpr hC)
    exact ⟨c :: l, by simp [hl], hg, Multiset.mem_toFinset.mp hc,
      fun c' hc' => hmin c' (Multiset.mem_toFinset.mpr hc')⟩

/-- A greedy step is at most the average over the candidates. -/
theorem IsGreedyL.le_avg {C : Multiset α} (_hC : C ≠ 0) {f : List α → ℝ} {c : α} {l : List α}
    (h : IsGreedyL C f (c :: l)) :
    (C.card : ℝ) * f (c :: l) ≤ (C.map fun c' => f (c' :: l)).sum := by
  have := Multiset.card_nsmul_le_sum (s := C.map fun c' => f (c' :: l)) (a := f (c :: l))
    (fun x hx => by
      obtain ⟨c', hc', rfl⟩ := Multiset.mem_map.1 hx
      exact h.2.2 c' hc')
  rw [Multiset.card_map, nsmul_eq_mul] at this
  exact this

/-- **Lemma 19.3 in multiset form**: if the average of `f(c :: l)` is always at most `θ f(l)`,
a greedy sequence has `f(l) ≤ θ^{|l|} f([])`. -/
theorem IsGreedyL.le_pow {C : Multiset α} (hC : C ≠ 0) {f : List α → ℝ} {θ : ℝ} (hθ : 0 ≤ θ)
    (havg : ∀ l, (C.map fun c => f (c :: l)).sum ≤ C.card * (θ * f l)) :
    ∀ l, IsGreedyL C f l → f l ≤ θ ^ l.length * f []
  | [], _ => by simp
  | c :: l, h => by
    have hpos : (0 : ℝ) < C.card := by exact_mod_cast Multiset.card_pos.mpr hC
    have h1 : f (c :: l) ≤ θ * f l :=
      le_of_mul_le_mul_left ((h.le_avg hC).trans (havg l)) hpos
    have ih := IsGreedyL.le_pow hC hθ havg l h.1
    calc f (c :: l) ≤ θ * f l := h1
      _ ≤ θ * (θ ^ l.length * f []) := mul_le_mul_of_nonneg_left ih hθ
      _ = θ ^ (c :: l).length * f [] := by rw [List.length_cons, pow_succ]; ring

end greedy

/-! ### Counting the survivors of a list of candidates -/

section cnt
variable {α β : Type*}

/-- The items of `J` that every candidate of `l` keeps. -/
def cntL (J : Finset β) (P : β → α → Prop) [∀ t c, Decidable (P t c)] (l : List α) : ℕ :=
  (J.filter fun t => ∀ c ∈ l, P t c).card

theorem cntL_nil (J : Finset β) (P : β → α → Prop) [∀ t c, Decidable (P t c)] :
    cntL J P [] = J.card := by
  unfold cntL
  congr 1
  ext t
  simp

theorem cntL_cons (J : Finset β) (P : β → α → Prop) [∀ t c, Decidable (P t c)] (c : α)
    (l : List α) :
    cntL J P (c :: l) = ((J.filter fun t => ∀ c ∈ l, P t c).filter fun t => P t c).card := by
  unfold cntL
  congr 1
  ext t
  simp only [Finset.mem_filter, List.forall_mem_cons]
  tauto

theorem sum_card_filter_swap (C : Multiset α) (J : Finset β) (P : β → α → Prop)
    [∀ t c, Decidable (P t c)] :
    (C.map fun c => ((J.filter fun t => P t c).card : ℝ)).sum =
      ∑ t ∈ J, ((C.filter (P t)).card : ℝ) := by
  have h1 : ∀ c, ((J.filter fun t => P t c).card : ℝ) = ∑ t ∈ J, if P t c then (1 : ℝ) else 0 := by
    intro c
    rw [Finset.card_filter, Nat.cast_sum]
    exact Finset.sum_congr rfl fun t _ => by split_ifs <;> simp
  simp only [h1]
  calc (C.map fun c => ∑ t ∈ J, if P t c then (1 : ℝ) else 0).sum
      = ∑ t ∈ J, (C.map fun c => if P t c then (1 : ℝ) else 0).sum :=
        Multiset.sum_map_sum_map C J.val
    _ = ∑ t ∈ J, ((C.filter (P t)).card : ℝ) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [sum_map_ite_const C (P t) 1, mul_one]

/-- **The averaging step**: if every item still kept by `l` is kept by at most a fraction `ρ`
of the candidates, the average over the candidates `c` of `cntL (c :: l)` is at most
`ρ · cntL l`. -/
theorem avg_cntL_le (C : Multiset α) (J : Finset β) (P : β → α → Prop)
    [∀ t c, Decidable (P t c)] (l : List α) (ρ : ℝ)
    (h : ∀ t ∈ J, (∀ c ∈ l, P t c) → ((C.filter (P t)).card : ℝ) ≤ ρ * C.card) :
    (C.map fun c => (cntL J P (c :: l) : ℝ)).sum ≤ ρ * C.card * cntL J P l := by
  simp only [cntL_cons]
  rw [sum_card_filter_swap]
  unfold cntL
  calc ∑ t ∈ J.filter (fun t => ∀ c ∈ l, P t c), ((C.filter (P t)).card : ℝ)
      ≤ ∑ t ∈ J.filter (fun t => ∀ c ∈ l, P t c), ρ * C.card :=
        Finset.sum_le_sum fun t ht =>
          h t (Finset.mem_filter.1 ht).1 (Finset.mem_filter.1 ht).2
    _ = ρ * C.card * (J.filter fun t => ∀ c ∈ l, P t c).card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end cnt

theorem forall_get_iff {α : Type*} (l : List α) (P : α → Prop) :
    (∀ i : Fin l.length, P (l.get i)) ↔ ∀ a ∈ l, P a :=
  ⟨fun h a ha => by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.1 ha
    exact h i,
   fun h i => h _ (List.mem_iff_get.2 ⟨i, rfl⟩)⟩

/-! ### The setting -/

variable {p : ℕ} [Fact p.Prime] {d : ℕ}

/-- `R^d`, `R = ZMod (p²)`. -/
abbrev Vp (p d : ℕ) := Fin d → ZMod (p ^ 2)

/-- Triples. -/
abbrev Trip (p d : ℕ) := Vp p d × Vp p d × Vp p d

section sets
variable (S₁ S₂ S₃ : Finset (Vp p d))

/-- The triples with `v̄ = 0` (type I and solutions); `T_I` is its size. -/
def TIset : Finset (Trip p d) :=
  (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => residue (t.1 + t.2.1 + t.2.2) = 0

/-- The type-II triples, `v̄ ≠ 0`. -/
def typeII : Finset (Trip p d) :=
  (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => residue (t.1 + t.2.1 + t.2.2) ≠ 0

variable (rs : List (VecP p d)) (q : ℕ)

/-- `𝖸`-items: type II with `ρ(v̄) = 0`. -/
def JY : Finset (Trip p d) :=
  (typeII S₁ S₂ S₃).filter fun t => ∀ r ∈ rs.drop q, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0

/-- `𝖲`-items: `v ≠ 0`, `ρ(v̄) = ρ''(v̄) = 0`. -/
def JS : Finset (Trip p d) :=
  (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t =>
    t.1 + t.2.1 + t.2.2 ≠ 0 ∧ ∀ r ∈ rs, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0

/-- `𝖠`-items: type II with `ρ(v̄) = 0`, `ρ''(v̄) ≠ 0`. -/
def JA : Finset (Trip p d) :=
  (typeII S₁ S₂ S₃).filter fun t =>
    (∀ r ∈ rs.drop q, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0) ∧
      ¬ ∀ r ∈ rs.take q, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0

end sets

/-- A pair row `(a, b)` keeps a `𝖸`-item iff `⟨a, v̄⟩ = 0`. -/
abbrev PY (t : Trip p d) (c : VecP p d × VecP p d) : Prop :=
  c.1 ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0

/-- A pair row `(a, b)` keeps an `𝖲`- or `𝖠`-item iff `⟨u, v⟩ = 0`, `u = lift a + p lift b`. -/
abbrev PK (t : Trip p d) (c : VecP p d × VecP p d) : Prop :=
  pairRow c.1 c.2 ⬝ᵥ (t.1 + t.2.1 + t.2.2) = 0

/-- **The potential** `Ψ_t = p^t 𝖸_t + D p^t 𝖲_t + p^{2t} 𝖠_t`, `D = p^q`, `t = |l|`. -/
noncomputable def Psi (S₁ S₂ S₃ : Finset (Vp p d)) (rs : List (VecP p d)) (q : ℕ)
    (l : List (VecP p d × VecP p d)) : ℝ :=
  (p : ℝ) ^ l.length * cntL (JY S₁ S₂ S₃ rs q) PY l +
    (p : ℝ) ^ q * (p : ℝ) ^ l.length * cntL (JS S₁ S₂ S₃ rs) PK l +
    (p : ℝ) ^ (2 * l.length) * cntL (JA S₁ S₂ S₃ rs q) PK l

/-! ### Survival rates (Lemma 19.19) for one pair row from `E × E` -/

section rates
variable {β : ℝ} {E : Multiset (VecP p d)}

theorem card_filter_fst (E : Multiset (VecP p d)) (w : VecP p d) :
    (((E ×ˢ E).filter fun c => c.1 ⬝ᵥ w = 0).card : ℝ) =
      (E.filter fun a => a ⬝ᵥ w = 0).card * E.card := by
  have h1 : ∀ a : VecP p d, (E.filter fun b : VecP p d => (a, b).1 ⬝ᵥ w = 0).card =
      if a ⬝ᵥ w = 0 then E.card else 0 := by
    intro a
    by_cases h : a ⬝ᵥ w = 0 <;> simp [h]
  rw [card_filter_product]
  simp only [h1]
  rw [Nat.cast_multiset_sum, Multiset.map_map]
  have : ((Nat.cast : ℕ → ℝ) ∘ fun a : VecP p d => if a ⬝ᵥ w = 0 then E.card else 0) =
      fun a => if a ⬝ᵥ w = 0 then (E.card : ℝ) else 0 := by
    funext a
    simp only [Function.comp]
    split_ifs <;> simp
  rw [this, sum_map_ite_const]

/-- One coordinate killed: fraction `≤ (1+β)/p` of `E × E` (kernel bias, `w ≠ 0`). -/
theorem rate_fst (hE : IsValBiased β E) {w : VecP p d} (hw : w ≠ 0) :
    (((E ×ˢ E).filter fun c => c.1 ⬝ᵥ w = 0).card : ℝ) ≤ (1 + β) / p * (E ×ˢ E).card := by
  rw [card_filter_fst, Multiset.card_product, Nat.cast_mul]
  have := hE.2 w hw 0
  calc ((E.filter fun a => a ⬝ᵥ w = 0).card : ℝ) * E.card
      ≤ (1 + β) / p * E.card * E.card := mul_le_mul_of_nonneg_right this (Nat.cast_nonneg _)
    _ = (1 + β) / p * (E.card * E.card) := by ring

/-- Type II and a pair row: fraction `≤ ((1+β)/p)²` (Lemma 19.19 via (F2) and value bias). -/
theorem rate_typeII (hE : IsValBiased β E) (v : Vp p d) (hv : residue v ≠ 0) :
    (((E ×ˢ E).filter fun c => pairRow c.1 c.2 ⬝ᵥ v = 0).card : ℝ) ≤
      ((1 + β) / p) ^ 2 * (E ×ˢ E).card := by
  have heq : ((E ×ˢ E).filter fun c => pairRow c.1 c.2 ⬝ᵥ v = 0) =
      (E ×ˢ E).filter fun c => c.1 ⬝ᵥ residue v = 0 ∧ c.2 ⬝ᵥ residue v = -c0 c.1 v := by
    refine Multiset.filter_congr fun c _ => ?_
    constructor
    · intro h
      have h1 := pairRow_dot_zero_imp c.1 c.2 v h
      exact ⟨h1, (F2 c.1 c.2 v h1).1 h⟩
    · rintro ⟨h1, h2⟩
      exact (F2 c.1 c.2 v h1).2 h2
  rw [heq, Multiset.card_product, Nat.cast_mul, ← mul_assoc]
  exact pair_survival hE hE hv (fun a => -c0 a v)

/-- Type I (`v̄ = 0`, `v ≠ 0`) and a pair row: fraction `≤ (1+β)/p` ((F1), `v/p ≠ 0`). -/
theorem rate_typeI (hE : IsValBiased β E) (v : Vp p d) (hres : residue v = 0) (hv : v ≠ 0) :
    (((E ×ˢ E).filter fun c => pairRow c.1 c.2 ⬝ᵥ v = 0).card : ℝ) ≤
      (1 + β) / p * (E ×ˢ E).card := by
  have heq : ((E ×ˢ E).filter fun c => pairRow c.1 c.2 ⬝ᵥ v = 0) =
      (E ×ˢ E).filter fun c => c.1 ⬝ᵥ ExpP2.divp v = 0 :=
    Multiset.filter_congr fun c _ => F1 c.1 c.2 v hres
  rw [heq]
  refine rate_fst hE ?_
  intro h
  apply hv
  rw [eq_p_smul_lift_divp v hres, h, lift_zero, smul_zero]

end rates

/-! ### Lemma 19.22: the potential -/

section potential
variable (S₁ S₂ S₃ : Finset (Vp p d)) (rs : List (VecP p d)) (q : ℕ)

theorem cntL_nonneg {α β : Type*} (J : Finset β) (P : β → α → Prop) [∀ t c, Decidable (P t c)]
    (l : List α) : (0 : ℝ) ≤ cntL J P l := Nat.cast_nonneg _

/-- **Lemma 19.22**: for every list `l` of earlier pair rows, the average of `Ψ_{t+1}` over the
candidates `(a, b) ∈ E × E` is at most `(1+β)² Ψ_t` (`E` `β`-value-biased, `0 ≤ β ≤ 1`). -/
theorem potential_avg {β : ℝ} {E : Multiset (VecP p d)} (hE : IsValBiased β E) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (l : List (VecP p d × VecP p d)) :
    ((E ×ˢ E).map fun c => Psi S₁ S₂ S₃ rs q (c :: l)).sum ≤
      (E ×ˢ E).card * ((1 + β) ^ 2 * Psi S₁ S₂ S₃ rs q l) := by
  set C := E ×ˢ E with hCdef
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  set ρ := (1 + β) / p with hρdef
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef, div_le_one hp]
    have : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
    linarith
  have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith
  -- the three averaging steps
  have hY := avg_cntL_le C (JY S₁ S₂ S₃ rs q) PY l ρ (fun t ht _ => by
    have hII : residue (t.1 + t.2.1 + t.2.2) ≠ 0 :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).2
    exact rate_fst hE hII)
  have hS := avg_cntL_le C (JS S₁ S₂ S₃ rs) PK l ρ (fun t ht _ => by
    have hv : t.1 + t.2.1 + t.2.2 ≠ 0 := (Finset.mem_filter.1 ht).2.1
    by_cases hres : residue (t.1 + t.2.1 + t.2.2) = 0
    · exact rate_typeI hE _ hres hv
    · exact (rate_typeII hE _ hres).trans
        (mul_le_mul_of_nonneg_right hρ2 (Nat.cast_nonneg _)))
  have hA := avg_cntL_le C (JA S₁ S₂ S₃ rs q) PK l (ρ ^ 2) (fun t ht _ => by
    have hII : residue (t.1 + t.2.1 + t.2.2) ≠ 0 :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 ht).1).2
    exact rate_typeII hE _ hII)
  set Y := (cntL (JY S₁ S₂ S₃ rs q) PY l : ℝ)
  set S := (cntL (JS S₁ S₂ S₃ rs) PK l : ℝ)
  set A := (cntL (JA S₁ S₂ S₃ rs q) PK l : ℝ)
  have hY0 : 0 ≤ Y := Nat.cast_nonneg _
  have hS0 : 0 ≤ S := Nat.cast_nonneg _
  have hA0 : 0 ≤ A := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ C.card := Nat.cast_nonneg _
  set t := l.length
  have hsum : (C.map fun c => Psi S₁ S₂ S₃ rs q (c :: l)).sum =
      (p : ℝ) ^ (t + 1) * (C.map fun c => (cntL (JY S₁ S₂ S₃ rs q) PY (c :: l) : ℝ)).sum +
      (p : ℝ) ^ q * (p : ℝ) ^ (t + 1) *
        (C.map fun c => (cntL (JS S₁ S₂ S₃ rs) PK (c :: l) : ℝ)).sum +
      (p : ℝ) ^ (2 * (t + 1)) * (C.map fun c => (cntL (JA S₁ S₂ S₃ rs q) PK (c :: l) : ℝ)).sum := by
    simp only [Psi, List.length_cons]
    rw [Multiset.sum_map_add, Multiset.sum_map_add, Multiset.sum_map_mul_left,
      Multiset.sum_map_mul_left, Multiset.sum_map_mul_left]
  rw [hsum]
  have hpt : (0 : ℝ) ≤ (p : ℝ) ^ (t + 1) := by positivity
  have hpq : (0 : ℝ) ≤ (p : ℝ) ^ q := by positivity
  have hp2 : (0 : ℝ) ≤ (p : ℝ) ^ (2 * (t + 1)) := by positivity
  have key : (1 + β) ≤ (1 + β) ^ 2 := by nlinarith
  calc _ ≤ (p : ℝ) ^ (t + 1) * (ρ * C.card * Y) + (p : ℝ) ^ q * (p : ℝ) ^ (t + 1) *
          (ρ * C.card * S) + (p : ℝ) ^ (2 * (t + 1)) * (ρ ^ 2 * C.card * A) := by
        gcongr
    _ = C.card * ((1 + β) * ((p : ℝ) ^ t * Y) + (1 + β) * ((p : ℝ) ^ q * (p : ℝ) ^ t * S) +
          (1 + β) ^ 2 * ((p : ℝ) ^ (2 * t) * A)) := by
        rw [hρdef]
        have hp0 : (p : ℝ) ≠ 0 := hp.ne'
        rw [show 2 * (t + 1) = 2 * t + 2 by ring, pow_add, pow_succ]
        field_simp
        ring
    _ ≤ C.card * ((1 + β) ^ 2 * Psi S₁ S₂ S₃ rs q l) := by
        apply mul_le_mul_of_nonneg_left _ hC0
        have e1 : 0 ≤ (p : ℝ) ^ t * Y := by positivity
        have e2 : 0 ≤ (p : ℝ) ^ q * (p : ℝ) ^ t * S := by positivity
        have e3 : 0 ≤ (p : ℝ) ^ (2 * t) * A := by positivity
        have : Psi S₁ S₂ S₃ rs q l = (p : ℝ) ^ t * Y + (p : ℝ) ^ q * (p : ℝ) ^ t * S +
            (p : ℝ) ^ (2 * t) * A := rfl
        rw [this]
        nlinarith [mul_le_mul_of_nonneg_right key e1, mul_le_mul_of_nonneg_right key e2]

/-- `Ψ` of greedy pair rows: `Ψ_t ≤ (1+β)^{2t} Ψ_0`, and `≤ e Ψ_0` when `2tβ ≤ 1`. -/
theorem Psi_greedy_le {β : ℝ} {E : Multiset (VecP p d)} (hE : IsValBiased β E) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (prs : List (VecP p d × VecP p d))
    (hg : IsGreedyL (E ×ˢ E) (Psi S₁ S₂ S₃ rs q) prs) (hβq : 2 * prs.length * β ≤ 1) :
    Psi S₁ S₂ S₃ rs q prs ≤ Real.exp 1 * Psi S₁ S₂ S₃ rs q [] := by
  have hC : E ×ˢ E ≠ 0 := by
    intro h
    have := congrArg Multiset.card h
    rw [Multiset.card_product, Multiset.card_zero] at this
    have hE0 : 0 < E.card := Multiset.card_pos.mpr hE.1
    exact (Nat.mul_pos hE0 hE0).ne' this
  have h := IsGreedyL.le_pow hC (by positivity) (potential_avg S₁ S₂ S₃ rs q hE hβ0 hβ1) prs hg
  have hΨ0 : 0 ≤ Psi S₁ S₂ S₃ rs q [] := by
    unfold Psi; positivity
  calc _ ≤ ((1 + β) ^ 2) ^ prs.length * Psi S₁ S₂ S₃ rs q [] := h
    _ ≤ Real.exp 1 * Psi S₁ S₂ S₃ rs q [] :=
        mul_le_mul_of_nonneg_right (one_add_sq_pow_le_exp β _ hβ0 hβq) hΨ0

end potential

/-! ### Residue rows and the initial value of `Ψ` -/

section initial
variable (S₁ S₂ S₃ : Finset (Vp p d))

theorem card_triples_le (n : ℕ) (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n) :
    ((S₁ ×ˢ S₂ ×ˢ S₃).card : ℝ) ≤ (n : ℝ) ^ 3 := by
  have : (S₁ ×ˢ S₂ ×ˢ S₃).card ≤ n ^ 3 := by
    rw [Finset.card_product, Finset.card_product, pow_three]
    exact Nat.mul_le_mul h₁ (Nat.mul_le_mul h₂ h₃)
  exact_mod_cast this

/-- The type-II family for the residue rows: vector `v̄`, weight `1`. -/
noncomputable def survII (rows : List (VecP p d)) : ℝ :=
  surv (typeII S₁ S₂ S₃) (fun t => residue (t.1 + t.2.1 + t.2.2)) (fun _ => 1) rows

theorem survII_eq (rows : List (VecP p d)) :
    survII S₁ S₂ S₃ rows = ((typeII S₁ S₂ S₃).filter fun t =>
      ∀ r ∈ rows, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0).card := by
  unfold survII surv
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_congr_decidable]

/-- Lemma 19.3 for the residue rows, every prefix: the first `|rs| − j` rows leave at most
`e p^{−(|rs|−j)} n³` type-II triples. -/
theorem survII_prefix_le {β : ℝ} {E : Multiset (VecP p d)} (hE : IsValBiased β E) (hβ0 : 0 ≤ β)
    (n : ℕ) (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (rs : List (VecP p d)) (hg : IsGreedy E (survII S₁ S₂ S₃) rs) (hβ : β ≤ 1 / rs.length)
    (j : ℕ) (_hj : j ≤ rs.length) :
    survII S₁ S₂ S₃ (rs.drop j) ≤ Real.exp 1 * (1 / (p : ℝ) ^ (rs.length - j)) * (n : ℝ) ^ 3 := by
  have hcard : ((typeII S₁ S₂ S₃).card : ℝ) ≤ (n : ℝ) ^ 3 :=
    le_trans (by exact_mod_cast Finset.card_filter_le _ _) (card_triples_le S₁ S₂ S₃ n h₁ h₂ h₃)
  have hlen : (rs.drop j).length = rs.length - j := List.length_drop ..
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rcases Nat.eq_zero_or_pos (rs.length - j) with h0 | hpos
  · rw [h0, pow_zero, div_one, mul_one, survII_eq]
    have : (((typeII S₁ S₂ S₃).filter fun t =>
        ∀ r ∈ rs.drop j, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0).card : ℝ) ≤
        (typeII S₁ S₂ S₃).card := by exact_mod_cast Finset.card_filter_le _ _
    have hn : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    nlinarith
  · have hb := greedy_bound_exp_drop hE.isKerBiased hβ0 (typeII S₁ S₂ S₃)
      (fun t => residue (t.1 + t.2.1 + t.2.2)) (fun _ => 1)
      (fun t ht => (Finset.mem_filter.1 ht).2) (fun _ _ => zero_le_one) rs hg j
      (by omega) hβ
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hlen] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left hcard (by positivity))

/-- **Display (19.resrows)**: with `|rs| = k + q`, `n/σ ≤ p^{k+q}`:
`#{type II : ρ(v̄) = 0} ≤ eσDn²` and `#{type II : ρ(v̄) = ρ''(v̄) = 0} ≤ eσn²`. -/
theorem resrows_bounds {β : ℝ} {E : Multiset (VecP p d)} (hE : IsValBiased β E) (hβ0 : 0 ≤ β)
    (n σ k q : ℕ) (hσ : 0 < σ) (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (rs : List (VecP p d)) (hlen : rs.length = k + q) (hg : IsGreedy E (survII S₁ S₂ S₃) rs)
    (hβ : β ≤ 1 / ((k : ℝ) + q)) (hnk : (n : ℝ) / σ ≤ (p : ℝ) ^ (k + q)) :
    survII S₁ S₂ S₃ (rs.drop q) ≤ Real.exp 1 * σ * (p : ℝ) ^ q * n ^ 2 ∧
    survII S₁ S₂ S₃ rs ≤ Real.exp 1 * σ * n ^ 2 := by
  have hβ' : β ≤ 1 / (rs.length : ℝ) := by rw [hlen]; push_cast; exact hβ
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn' : (n : ℝ) ≤ σ * ((p : ℝ) ^ k * (p : ℝ) ^ q) := by
    rw [div_le_iff₀ hσR, pow_add] at hnk; linarith
  have h1 := survII_prefix_le S₁ S₂ S₃ hE hβ0 n h₁ h₂ h₃ rs hg hβ' q (by omega)
  have h2 := survII_prefix_le S₁ S₂ S₃ hE hβ0 n h₁ h₂ h₃ rs hg hβ' 0 (by omega)
  rw [show rs.length - q = k by omega] at h1
  rw [Nat.sub_zero, List.drop_zero, hlen] at h2
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hpk : (0 : ℝ) < (p : ℝ) ^ k := pow_pos hp k
  have hpq : (0 : ℝ) < (p : ℝ) ^ q := pow_pos hp q
  constructor
  · refine h1.trans ?_
    have : 1 / (p : ℝ) ^ k * n ≤ σ * (p : ℝ) ^ q := by
      rw [one_div, inv_mul_le_iff₀ hpk]; nlinarith
    calc Real.exp 1 * (1 / (p : ℝ) ^ k) * (n : ℝ) ^ 3
        = Real.exp 1 * (1 / (p : ℝ) ^ k * n) * n ^ 2 := by ring
      _ ≤ Real.exp 1 * (σ * (p : ℝ) ^ q) * n ^ 2 := by gcongr
      _ = Real.exp 1 * σ * (p : ℝ) ^ q * n ^ 2 := by ring
  · refine h2.trans ?_
    have : 1 / (p : ℝ) ^ (k + q) * n ≤ σ := by
      rw [one_div, inv_mul_le_iff₀ (by positivity), pow_add]; nlinarith
    calc Real.exp 1 * (1 / (p : ℝ) ^ (k + q)) * (n : ℝ) ^ 3
        = Real.exp 1 * (1 / (p : ℝ) ^ (k + q) * n) * n ^ 2 := by ring
      _ ≤ Real.exp 1 * σ * n ^ 2 := by gcongr

/-- **"The bounds", `t = 0`**: `Ψ₀ ≤ D(3eσn² + T_I)`. -/
theorem Psi_nil_le {β : ℝ} {E : Multiset (VecP p d)} (hE : IsValBiased β E) (hβ0 : 0 ≤ β)
    (n σ k q : ℕ) (hσ : 0 < σ) (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (rs : List (VecP p d)) (hlen : rs.length = k + q) (hg : IsGreedy E (survII S₁ S₂ S₃) rs)
    (hβ : β ≤ 1 / ((k : ℝ) + q)) (hnk : (n : ℝ) / σ ≤ (p : ℝ) ^ (k + q)) :
    Psi S₁ S₂ S₃ rs q [] ≤
      (p : ℝ) ^ q * (3 * Real.exp 1 * σ * n ^ 2 + (TIset S₁ S₂ S₃).card) := by
  obtain ⟨hY, hYS⟩ := resrows_bounds S₁ S₂ S₃ hE hβ0 n σ k q hσ h₁ h₂ h₃ rs hlen hg hβ hnk
  rw [survII_eq] at hY hYS
  have hY0 : (cntL (JY S₁ S₂ S₃ rs q) PY [] : ℝ) ≤ Real.exp 1 * σ * (p : ℝ) ^ q * n ^ 2 := by
    rw [cntL_nil]; exact hY
  have hA0 : (cntL (JA S₁ S₂ S₃ rs q) PK [] : ℝ) ≤ Real.exp 1 * σ * (p : ℝ) ^ q * n ^ 2 := by
    rw [cntL_nil]
    refine le_trans ?_ hY
    have : JA S₁ S₂ S₃ rs q ⊆ JY S₁ S₂ S₃ rs q := by
      intro t ht
      obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 ht
      exact Finset.mem_filter.2 ⟨h1, h2⟩
    exact_mod_cast Finset.card_le_card this
  have hS0 : (cntL (JS S₁ S₂ S₃ rs) PK [] : ℝ) ≤
      (TIset S₁ S₂ S₃).card + Real.exp 1 * σ * n ^ 2 := by
    rw [cntL_nil]
    have hsub : JS S₁ S₂ S₃ rs ⊆ TIset S₁ S₂ S₃ ∪ (typeII S₁ S₂ S₃).filter fun t =>
        ∀ r ∈ rs, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0 := by
      intro t ht
      obtain ⟨hm, -, hr⟩ := Finset.mem_filter.1 ht
      by_cases h : residue (t.1 + t.2.1 + t.2.2) = 0
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hm, h⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hm, h⟩, hr⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have h' : ((JS S₁ S₂ S₃ rs).card : ℝ) ≤ (TIset S₁ S₂ S₃).card +
        (((typeII S₁ S₂ S₃).filter fun t =>
          ∀ r ∈ rs, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0).card : ℝ) := by exact_mod_cast this
    linarith
  have hpq : (0 : ℝ) < (p : ℝ) ^ q := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) q
  unfold Psi
  simp only [List.length_nil, pow_zero, mul_zero, one_mul, mul_one]
  nlinarith

end initial

/-! ### The maps `π`, `K` of Case L and their kernels -/

section maps

/-- `π` of Case L from the row lists: `ρ` = `rs.drop q`, low digits from `prs`. -/
def piLL (rr : List (VecP p d)) (prs : List (VecP p d × VecP p d)) :=
  piL (p := p) (d := d) (fun i : Fin rr.length => rr.get i) (fun i : Fin prs.length => (prs.get i).1)

/-- `K` of Case L from the row lists. -/
def KLL (rr : List (VecP p d)) (prs : List (VecP p d × VecP p d)) :=
  KL (p := p) (d := d) (fun i : Fin rr.length => rr.get i) (fun i : Fin prs.length => (prs.get i).1)
    (fun i : Fin prs.length => (prs.get i).2)

theorem piLL_eq_zero_iff (rr : List (VecP p d)) (prs : List (VecP p d × VecP p d)) (x : Vp p d) :
    piLL rr prs x = 0 ↔
      (∀ r ∈ rr, r ⬝ᵥ residue x = 0) ∧ ∀ c ∈ prs, c.1 ⬝ᵥ residue x = 0 := by
  change ((fun i : Fin rr.length => rr.get i ⬝ᵥ residue x),
    (fun i : Fin prs.length => (prs.get i).1 ⬝ᵥ residue x)) = 0 ↔ _
  rw [Prod.ext_iff, funext_iff, funext_iff]
  exact and_congr (forall_get_iff rr (fun r => r ⬝ᵥ residue x = 0))
    (forall_get_iff prs (fun c => c.1 ⬝ᵥ residue x = 0))

theorem KLL_eq_zero_iff (rr : List (VecP p d)) (prs : List (VecP p d × VecP p d)) (x : Vp p d) :
    KLL rr prs x = 0 ↔
      (∀ r ∈ rr, r ⬝ᵥ residue x = 0) ∧ ∀ c ∈ prs, pairRow c.1 c.2 ⬝ᵥ x = 0 := by
  change ((fun i : Fin rr.length => rr.get i ⬝ᵥ residue x),
    (fun i : Fin prs.length => pairRow (prs.get i).1 (prs.get i).2 ⬝ᵥ x)) = 0 ↔ _
  rw [Prod.ext_iff, funext_iff, funext_iff]
  exact and_congr (forall_get_iff rr (fun r => r ⬝ᵥ residue x = 0))
    (forall_get_iff prs (fun c => pairRow c.1 c.2 ⬝ᵥ x = 0))

theorem KLL_factor (rr : List (VecP p d)) (prs : List (VecP p d × VecP p d)) (x : Vp p d)
    (h : KLL rr prs x = 0) : piLL rr prs x = 0 :=
  KL_factor _ _ _ x h

variable (S₁ S₂ S₃ : Finset (Vp p d))

/-- **`Z(π) ≤ T_I + 𝖸_q`.** -/
theorem Zc_piLL_le (rs : List (VecP p d)) (q : ℕ) (prs : List (VecP p d × VecP p d)) :
    Zc S₁ S₂ S₃ (piLL (rs.drop q) prs) ≤
      (TIset S₁ S₂ S₃).card + cntL (JY S₁ S₂ S₃ rs q) PY prs := by
  unfold Zc cntL
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro t ht
  obtain ⟨hm, h0⟩ := Finset.mem_filter.1 ht
  obtain ⟨hr, ha⟩ := (piLL_eq_zero_iff _ _ _).1 h0
  by_cases h : residue (t.1 + t.2.1 + t.2.2) = 0
  · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hm, h⟩)
  · apply Finset.mem_union_right
    simp only [JY, typeII, Finset.mem_filter]
    exact ⟨⟨⟨hm, h⟩, hr⟩, ha⟩

/-- **`F = Z(K) − Z₀ ≤ 𝖲_q + 𝖠_q`** (`F` the false positives of Lemma 19.6(iv)). -/
theorem Zc_KLL_sub_le (rs : List (VecP p d)) (q : ℕ) (prs : List (VecP p d × VecP p d)) :
    (Zc S₁ S₂ S₃ (KLL (rs.drop q) prs) : ℝ) - Zsol S₁ S₂ S₃ ≤
      cntL (JS S₁ S₂ S₃ rs) PK prs + cntL (JA S₁ S₂ S₃ rs q) PK prs := by
  set K := KLL (p := p) (rs.drop q) prs
  set Tk := (S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => K (t.1 + t.2.1 + t.2.2) = 0
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Tk) (fun t => t.1 + t.2.1 + t.2.2 = 0)
  have hsol : (Tk.filter fun t => t.1 + t.2.1 + t.2.2 = 0).card = Zsol S₁ S₂ S₃ := by
    unfold Zsol
    congr 1
    ext t
    simp only [Tk, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hm, -⟩, h⟩; exact ⟨hm, h⟩
    · rintro ⟨hm, h⟩; exact ⟨⟨hm, by rw [h, map_zero]⟩, h⟩
  have hrest : (Tk.filter fun t => ¬ t.1 + t.2.1 + t.2.2 = 0).card ≤
      cntL (JS S₁ S₂ S₃ rs) PK prs + cntL (JA S₁ S₂ S₃ rs q) PK prs := by
    unfold cntL
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro t ht
    obtain ⟨⟨hm, hK⟩, hv⟩ := by simpa only [Tk, Finset.mem_filter] using ht
    obtain ⟨hr, hu⟩ := (KLL_eq_zero_iff _ _ _).1 hK
    by_cases htake : ∀ r ∈ rs.take q, r ⬝ᵥ residue (t.1 + t.2.1 + t.2.2) = 0
    · apply Finset.mem_union_left
      simp only [JS, Finset.mem_filter]
      refine ⟨⟨hm, hv, ?_⟩, hu⟩
      intro r hrm
      rw [← List.take_append_drop q rs, List.mem_append] at hrm
      rcases hrm with h | h
      · exact htake r h
      · exact hr r h
    · have hres : residue (t.1 + t.2.1 + t.2.2) ≠ 0 := by
        intro h0
        apply htake
        intro r _
        rw [h0, dotProduct_zero]
      apply Finset.mem_union_right
      simp only [JA, typeII, Finset.mem_filter]
      exact ⟨⟨⟨hm, hres⟩, hr, htake⟩, hu⟩
  have hZ : Zc S₁ S₂ S₃ K = Tk.card := rfl
  rw [hZ, ← hsplit, hsol]
  push_cast
  have : ((Tk.filter fun t => ¬ t.1 + t.2.1 + t.2.2 = 0).card : ℝ) ≤
      cntL (JS S₁ S₂ S₃ rs) PK prs + cntL (JA S₁ S₂ S₃ rs q) PK prs := by exact_mod_cast hrest
  linarith

end maps

/-! ### Lemma 19.21 -/

/-- `e + 3e² < 25`. -/
theorem e_add_three_e_sq_lt : Real.exp 1 + 3 * Real.exp 1 ^ 2 < 25 := by
  have h := Real.exp_one_lt_d9
  have h0 : 0 < Real.exp 1 := Real.exp_pos 1
  nlinarith

set_option maxHeartbeats 1000000 in
/-- **Lemma 19.21 (Case L), correctness and counts.** Lists of at most `n` elements with
`T_I ≤ σn²`; `n/σ ≤ p^{k+q} < pn/σ`, `σ² ≤ D = p^q`, `q ≥ 1`; `E` `β`-value-biased with
`0 ≤ β`, `β ≤ 1/(k+q)`, `2qβ ≤ 1`; residue rows `rs` (`|rs| = k+q`) greedy for the type-II
count, pair rows `prs` (`|prs| = q`) greedy for `Ψ`; `π`, `K` as in the paper; any blockings of
lists 2, 3 for `π` with block size `σ`, any representatives. Then
(i) the one-call algorithm answers YES iff a solution exists;
(ii) `Z(π) ≤ (1+e+3e²)σn²`;
(iii) the false positives `F ≤ e(3e+1)σn²/D`;
(iv) `|𝒫₀| ≤ (p+28)n²/σ`, and `|𝒫₀| ≤ N²/√D` for `N = g'p^{q₁}` whenever `g' ≥ (p+5)n/σ`
and `q ≤ 2q₁` (so `J = 1`: one call);
(v) each of lists 2, 3 has fewer than `(p+1)n/σ` blocks. -/
theorem caseL (S₁ S₂ S₃ : Finset (Vp p d)) (n σ k q : ℕ) (hσ : 0 < σ) (hq : 0 < q)
    (h₁ : S₁.card ≤ n) (h₂ : S₂.card ≤ n) (h₃ : S₃.card ≤ n)
    (hTI : ((TIset S₁ S₂ S₃).card : ℝ) ≤ σ * n ^ 2)
    (hnk : (n : ℝ) / σ ≤ (p : ℝ) ^ (k + q)) (hnk' : (p : ℝ) ^ (k + q) < p * n / σ)
    (hσD : (σ : ℝ) ^ 2 ≤ (p : ℝ) ^ q)
    {β : ℝ} {E : Multiset (VecP p d)} (hE : IsValBiased β E) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / ((k : ℝ) + q)) (hβq : 2 * q * β ≤ 1)
    (rs : List (VecP p d)) (hrs : rs.length = k + q) (hgr : IsGreedy E (survII S₁ S₂ S₃) rs)
    (prs : List (VecP p d × VecP p d)) (hprs : prs.length = q)
    (hgp : IsGreedyL (E ×ˢ E) (Psi S₁ S₂ S₃ rs q) prs)
    (B₂ : Blocking S₂ (piLL (rs.drop q) prs) σ) (B₃ : Blocking S₃ (piLL (rs.drop q) prs) σ)
    (zr : Finset (Vp p d) → Vp p d) :
    (oneHashYes S₁ B₂ B₃ (KLL (rs.drop q) prs) zr Finset.univ ↔
      ∃ x₁ ∈ S₁, ∃ x₂ ∈ S₂, ∃ x₃ ∈ S₃, x₁ + x₂ + x₃ = 0) ∧
    (Zc S₁ S₂ S₃ (piLL (rs.drop q) prs) : ℝ) ≤
      (1 + Real.exp 1 + 3 * Real.exp 1 ^ 2) * σ * n ^ 2 ∧
    (F (probes S₁ B₂ B₃) (KLL (rs.drop q) prs) : ℝ) ≤
      Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2 / (p : ℝ) ^ q ∧
    ((probes S₁ B₂ B₃).card : ℝ) ≤ (p + 28) * n ^ 2 / σ ∧
    (∀ g' q₁ : ℕ, ((p : ℝ) + 5) * n / σ ≤ g' → q ≤ 2 * q₁ →
      ((probes S₁ B₂ B₃).card : ℝ) ≤ ((g' : ℝ) * (p : ℝ) ^ q₁) ^ 2 / Real.sqrt ((p : ℝ) ^ q)) ∧
    (B₂.blocks.card : ℝ) < (p + 1) * n / σ ∧ (B₃.blocks.card : ℝ) < (p + 1) * n / σ := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hσ1 : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hD : (0 : ℝ) < (p : ℝ) ^ q := pow_pos hp q
  have hβ1 : β ≤ 1 := by
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith
  have hβq' : 2 * prs.length * β ≤ 1 := by rw [hprs]; exact hβq
  -- the potential at the end
  have hΨq := Psi_greedy_le S₁ S₂ S₃ rs q hE hβ0 hβ1 prs hgp hβq'
  have hΨ0 := Psi_nil_le S₁ S₂ S₃ hE hβ0 n σ k q hσ h₁ h₂ h₃ rs hrs hgr hβ hnk
  have hZπ0 : (Zc S₁ S₂ S₃ (piLL (rs.drop q) prs) : ℝ) ≤
      (TIset S₁ S₂ S₃).card + (cntL (JY S₁ S₂ S₃ rs q) PY prs : ℝ) := by
    exact_mod_cast Zc_piLL_le S₁ S₂ S₃ rs q prs
  set Y := (cntL (JY S₁ S₂ S₃ rs q) PY prs : ℝ)
  set S := (cntL (JS S₁ S₂ S₃ rs) PK prs : ℝ)
  set A := (cntL (JA S₁ S₂ S₃ rs q) PK prs : ℝ)
  have hPsi : Psi S₁ S₂ S₃ rs q prs =
      (p : ℝ) ^ q * Y + (p : ℝ) ^ q * (p : ℝ) ^ q * S + (p : ℝ) ^ (2 * q) * A := by
    unfold Psi; rw [hprs]
  obtain ⟨hYb, -, -, hTY⟩ := partL_final p q ((p : ℝ) ^ q) σ n (Psi S₁ S₂ S₃ rs q [])
    (Psi S₁ S₂ S₃ rs q prs) (TIset S₁ S₂ S₃).card Y S A hD rfl hΨq
    (by nlinarith) hTI hPsi (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  -- (ii)
  have hZπ : (Zc S₁ S₂ S₃ (piLL (rs.drop q) prs) : ℝ) ≤
      (1 + Real.exp 1 + 3 * Real.exp 1 ^ 2) * σ * n ^ 2 := by
    linarith
  -- (iii)
  have hSA : S + A ≤ Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2 / (p : ℝ) ^ q := by
    rw [le_div_iff₀ hD]
    have hY0 : 0 ≤ Y := Nat.cast_nonneg _
    have hS0 : 0 ≤ S := Nat.cast_nonneg _
    have hA0 : 0 ≤ A := Nat.cast_nonneg _
    have hp2q : (p : ℝ) ^ (2 * q) = (p : ℝ) ^ q * (p : ℝ) ^ q := by rw [two_mul, pow_add]
    have hupper : Psi S₁ S₂ S₃ rs q prs ≤
        (p : ℝ) ^ q * (Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2) := by
      have : Psi S₁ S₂ S₃ rs q [] ≤ (p : ℝ) ^ q * ((3 * Real.exp 1 + 1) * σ * n ^ 2) := by
        refine hΨ0.trans (mul_le_mul_of_nonneg_left ?_ hD.le)
        nlinarith
      nlinarith
    rw [hPsi, hp2q] at hupper
    have hDY : 0 ≤ (p : ℝ) ^ q * Y := by positivity
    have : (p : ℝ) ^ q * ((S + A) * (p : ℝ) ^ q) ≤
        (p : ℝ) ^ q * (Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left this hD
  have hF : (F (probes S₁ B₂ B₃) (KLL (rs.drop q) prs) : ℝ) ≤
      Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2 / (p : ℝ) ^ q := by
    have e := F_probes_eq (S₁ := S₁) B₂ B₃ (KLL (rs.drop q) prs) (KLL_factor _ _)
    have e' := congrArg (Int.cast : ℤ → ℝ) e
    push_cast at e'
    rw [e']
    exact (Zc_KLL_sub_le S₁ S₂ S₃ rs q prs).trans hSA
  -- (iv)
  have hN₂ : ∀ S : Finset (Vp p d),
      ((S.image (piLL (rs.drop q) prs)).card : ℝ) ≤ (p : ℝ) ^ (k + q) := by
    intro S
    have h := Finset.card_le_univ (S.image (piLL (p := p) (rs.drop q) prs))
    have hc : Fintype.card ((Fin (rs.drop q).length → ZMod p) × (Fin prs.length → ZMod p)) =
        p ^ (k + q) := by
      rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin,
        Fintype.card_fin, List.length_drop, hrs, hprs, ← pow_add,
        show k + q - q + q = k + q by omega]
    rw [hc] at h
    exact_mod_cast h
  have c1 : (S₁.card : ℝ) ≤ n := by exact_mod_cast h₁
  have c2 : (S₂.card : ℝ) ≤ n := by exact_mod_cast h₂
  have c3 : (S₃.card : ℝ) ≤ n := by exact_mod_cast h₃
  have hP := probes_card_le (S₁ := S₁) hσ B₂ B₃
  have t1 : (S₁.card : ℝ) * (S₂.image (piLL (rs.drop q) prs)).card ≤ n * (p * n / σ) :=
    mul_le_mul c1 ((hN₂ S₂).trans hnk'.le) (Nat.cast_nonneg _) hn0
  have t2 : (S₁.card : ℝ) * ((S₂.card + S₃.card) / σ) ≤ n * ((n + n) / σ) := by gcongr
  have t3 : (Zc S₁ S₂ S₃ (piLL (rs.drop q) prs) : ℝ) / σ ^ 2 ≤
      (1 + Real.exp 1 + 3 * Real.exp 1 ^ 2) * n ^ 2 / σ := by
    calc (Zc S₁ S₂ S₃ (piLL (rs.drop q) prs) : ℝ) / σ ^ 2
        ≤ (1 + Real.exp 1 + 3 * Real.exp 1 ^ 2) * σ * n ^ 2 / σ ^ 2 :=
          div_le_div_of_nonneg_right hZπ (by positivity)
      _ = (1 + Real.exp 1 + 3 * Real.exp 1 ^ 2) * n ^ 2 / σ := by
          rw [div_eq_div_iff (by positivity) hσR.ne']; ring
  have hPle : ((probes S₁ B₂ B₃).card : ℝ) ≤
      (p + 3 + Real.exp 1 + 3 * Real.exp 1 ^ 2) * n ^ 2 / σ := by
    have : n * (p * n / σ) + n * ((n + n) / σ) +
        (1 + Real.exp 1 + 3 * Real.exp 1 ^ 2) * n ^ 2 / σ =
        (p + 3 + Real.exp 1 + 3 * Real.exp 1 ^ 2) * n ^ 2 / σ := by
      field_simp; ring
    linarith
  have h25 := e_add_three_e_sq_lt
  have hn2σ : (0 : ℝ) ≤ n ^ 2 / σ := by positivity
  have hP28 : ((probes S₁ B₂ B₃).card : ℝ) ≤ (p + 28) * n ^ 2 / σ := by
    refine hPle.trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) hn2σ
  refine ⟨detection_correct_univ B₂ B₃ _ zr, hZπ, hF, ?_, ?_, ?_, ?_⟩
  · exact hP28
  · intro g' q₁ hg' hq₁
    have hsqrt : (σ : ℝ) ≤ Real.sqrt ((p : ℝ) ^ q) := Real.le_sqrt_of_sq_le hσD
    have hs0 : (0 : ℝ) < Real.sqrt ((p : ℝ) ^ q) := Real.sqrt_pos.2 hD
    have hpq₁ : (p : ℝ) ^ q ≤ ((p : ℝ) ^ q₁) ^ 2 := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by linarith) (by omega)
    have hg0 : (0 : ℝ) ≤ g' := Nat.cast_nonneg _
    have hA : ((p : ℝ) + 5) ^ 2 * n ^ 2 / σ ≤ ((g' : ℝ) * (p : ℝ) ^ q₁) ^ 2 /
        Real.sqrt ((p : ℝ) ^ q) := by
      rw [le_div_iff₀ hs0]
      have hgg : (((p : ℝ) + 5) * n / σ) ^ 2 ≤ (g' : ℝ) ^ 2 := by
        have : 0 ≤ ((p : ℝ) + 5) * n / σ := by positivity
        nlinarith
      have hsq : Real.sqrt ((p : ℝ) ^ q) * Real.sqrt ((p : ℝ) ^ q) = (p : ℝ) ^ q :=
        Real.mul_self_sqrt hD.le
      calc ((p : ℝ) + 5) ^ 2 * n ^ 2 / σ * Real.sqrt ((p : ℝ) ^ q)
          = (((p : ℝ) + 5) * n / σ) ^ 2 * (σ * Real.sqrt ((p : ℝ) ^ q)) := by
            field_simp
        _ ≤ (g' : ℝ) ^ 2 * (Real.sqrt ((p : ℝ) ^ q) * Real.sqrt ((p : ℝ) ^ q)) := by
            gcongr
        _ = (g' : ℝ) ^ 2 * (p : ℝ) ^ q := by rw [hsq]
        _ ≤ (g' : ℝ) ^ 2 * ((p : ℝ) ^ q₁) ^ 2 := by gcongr
        _ = ((g' : ℝ) * (p : ℝ) ^ q₁) ^ 2 := by ring
    refine le_trans ?_ hA
    refine hP28.trans ?_
    rw [mul_div_assoc, mul_div_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hn2σ
    nlinarith
  · have hb := B₂.card_le' hσ
    have hc := (hN₂ S₂).trans_lt hnk'
    have hs : (S₂.card : ℝ) / σ ≤ n / σ := div_le_div_of_nonneg_right c2 hσR.le
    have he' : ((p : ℝ) + 1) * n / σ = p * n / σ + n / σ := by ring
    linarith
  · have hb := B₃.card_le' hσ
    have hc := (hN₂ S₃).trans_lt hnk'
    have hs : (S₃.card : ℝ) / σ ≤ n / σ := div_le_div_of_nonneg_right c3 hσR.le
    have he' : ((p : ℝ) + 1) * n / σ = p * n / σ + n / σ := by ring
    linarith

end CaseL
end GroupLean

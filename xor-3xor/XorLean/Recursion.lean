import XorLean.Basic
import XorLean.Conv

/-!
# T7: Lemmas 12, 13, 14 (`lem:hash`, `lem:tree`, `lem:correct`) and the parameters of §7
-/

namespace Xor

variable {d : ℕ}

/-- Three lists, as sets. -/
abbrev Lists (d : ℕ) := Fin 3 → Finset (Vec d)

def HasSol3 (T : Lists d) : Prop :=
  ∃ x₁ ∈ T 0, ∃ x₂ ∈ T 1, ∃ x₃ ∈ T 2, x₁ + x₂ + x₃ = 0

-- parameters
/-- `k`: the least even integer `≥ log₂ n + 4`; for natural `n ≥ 2` this is the least even
integer `≥ ⌈log₂ n⌉ + 4`. -/
def kOf (n : ℕ) : ℕ := 2 * ((Nat.clog 2 n + 5) / 2)

theorem kOf_spec (n : ℕ) (hn : 2 ≤ n) :
    Even (kOf n) ∧ Real.logb 2 n + 4 ≤ kOf n ∧
    (∀ k' : ℕ, Even k' → Real.logb 2 n + 4 ≤ k' → kOf n ≤ k') ∧
    16 * n ≤ 2 ^ kOf n ∧ 2 ^ kOf n < 64 * n := by
  set c := Nat.clog 2 n with hc
  have hc1 : 1 ≤ c := Nat.clog_pos (by norm_num) hn
  have hup : n ≤ 2 ^ c := Nat.le_pow_clog (by norm_num) n
  obtain ⟨c', hc'⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have hlow : 2 ^ c' < n := by
    have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := n) (by omega)
    rwa [← hc, hc', Nat.pred_succ] at this
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog_up : Real.logb 2 n ≤ c := by
    have h : (n : ℝ) ≤ 2 ^ c := by exact_mod_cast hup
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hn0 h
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
  have hlog_low : (c' : ℝ) < Real.logb 2 n := by
    have h : ((2 : ℝ) ^ c') < n := by exact_mod_cast hlow
    have := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) h
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
  have hk : c + 4 ≤ kOf n ∧ kOf n ≤ c + 5 := by unfold kOf; omega
  refine ⟨by unfold kOf; exact even_two_mul _, ?_, ?_, ?_, ?_⟩
  · have : ((c + 4 : ℕ) : ℝ) ≤ kOf n := by exact_mod_cast hk.1
    push_cast at this
    linarith
  · rintro k' ⟨r, hr⟩ hk'
    have h1 : ((c' + 4 : ℕ) : ℝ) < k' := by push_cast; linarith
    have h2 : c' + 4 < k' := by exact_mod_cast h1
    unfold kOf
    omega
  · calc 16 * n ≤ 16 * 2 ^ c := Nat.mul_le_mul_left 16 hup
      _ = 2 ^ (c + 4) := by rw [pow_add]; ring
      _ ≤ 2 ^ kOf n := Nat.pow_le_pow_right (by norm_num) hk.1
  · calc 2 ^ kOf n ≤ 2 ^ (c + 5) := Nat.pow_le_pow_right (by norm_num) hk.2
      _ = 64 * 2 ^ c' := by rw [hc', pow_add, pow_add]; ring
      _ < 64 * n := by omega

/-- In `Vec k`, `a + b = 0 ↔ a = b`. -/
theorem vec_add_eq_zero_iff {k : ℕ} (a b : Vec k) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    calc a = a + (b + b) := by rw [vec_add_self, add_zero]
      _ = (a + b) + b := (add_assoc a b b).symm
      _ = b := by rw [h, zero_add]
  · rintro rfl; exact vec_add_self a

-- buckets and bad elements, for any map `h`
def bucket {k : ℕ} (h : Vec d →ₗ[ZMod 2] Vec k) (T : Finset (Vec d)) (β : Vec k) :
    Finset (Vec d) := T.filter fun x => h x = β

def bad {k : ℕ} (h : Vec d →ₗ[ZMod 2] Vec k) (T : Finset (Vec d)) : Finset (Vec d) :=
  T.filter fun x => 3 < (bucket h T (h x)).card

/-- Colliding ordered pairs `P_i(H)`. -/
def collisions {k : ℕ} (h : Vec d →ₗ[ZMod 2] Vec k) (T : Finset (Vec d)) : ℕ :=
  (T.offDiag.filter fun p => h p.1 = h p.2).card

theorem three_mul_bad_le {k : ℕ} (h : Vec d →ₗ[ZMod 2] Vec k) (T : Finset (Vec d)) :
    3 * (bad h T).card ≤ collisions h T := by
  classical
  set s : Finset (Σ _ : Vec d, Vec d) :=
    (bad h T).sigma fun x => (bucket h T (h x)).erase x with hs
  have h1 : 3 * (bad h T).card ≤ s.card := by
    rw [hs, Finset.card_sigma, mul_comm, ← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    have hxb : x ∈ bucket h T (h x) :=
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, rfl⟩
    rw [Finset.card_erase_of_mem hxb]
    omega
  refine le_trans h1 (Finset.card_le_card_of_injOn (fun q => (q.1, q.2)) ?_ ?_)
  · rintro ⟨x, y⟩ hq
    rw [Finset.mem_coe, hs, Finset.mem_sigma, Finset.mem_erase] at hq
    obtain ⟨hxb, hyx, hyb⟩ := hq
    have hxT := (Finset.mem_filter.mp hxb).1
    obtain ⟨hyT, hy⟩ := Finset.mem_filter.mp hyb
    show (x, y) ∈ (T.offDiag.filter fun p => h p.1 = h p.2)
    exact Finset.mem_filter.mpr ⟨Finset.mem_offDiag.mpr ⟨hxT, hyT, fun e => hyx e.symm⟩, hy.symm⟩
  · rintro ⟨x, y⟩ _ ⟨x', y'⟩ _ e
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl

-- the hash of step (H): Lemma 5 on the differences of each list, weights 1/|T_i|²
/-- The family: ordered pairs `(i, (x, y))`, `x ≠ y` in `T i`. -/
def pairFamily (T : Lists d) : Finset (Σ _ : Fin 3, Vec d × Vec d) :=
  Finset.univ.sigma fun i => (T i).offDiag

def pairVec : (Σ _ : Fin 3, Vec d × Vec d) → Vec d := fun p => p.2.1 + p.2.2
noncomputable def pairWeight (T : Lists d) : (Σ _ : Fin 3, Vec d × Vec d) → ℝ :=
  fun p => 1 / ((T p.1).card : ℝ) ^ 2

theorem rowsMap_eq_iff {ℓ : ℕ} (rows : List (Vec ℓ)) (x y : Vec ℓ) :
    (∀ u ∈ rows, u ⬝ᵥ (x + y) = 0) ↔ rowsMap rows x = rowsMap rows y := by
  rw [← rowsMap_eq_zero_iff, map_add, vec_add_eq_zero_iff]

/-- The potential `Φ(H) = Σ_i P_i(H)/|T_i|²` equals Lemma 5's `surv`. -/
theorem surv_pairFamily (T : Lists d) (rows : List (Vec d)) :
    surv (pairFamily T) pairVec (pairWeight T) rows =
      ∑ i, (collisions (rowsMap rows) (T i) : ℝ) / ((T i).card : ℝ) ^ 2 := by
  classical
  unfold surv pairFamily
  rw [Finset.sum_filter, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [collisions, Finset.natCast_card_filter, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [pairVec, pairWeight, rowsMap_eq_iff]
  split_ifs <;> simp

/-- The hash of step (H) at node `T`: the greedy rows for the potential. -/
noncomputable def hashOf (E : Multiset (Vec d)) (k : ℕ) (T : Lists d) : List (Vec d) :=
  greedyRows E (surv (pairFamily T) pairVec (pairWeight T)) k

/-- `Σ ω ≤ 3`: each list contributes `|T_i|(|T_i| − 1)/|T_i|² ≤ 1`. -/
theorem sum_pairWeight_le (T : Lists d) : ∑ j ∈ pairFamily T, pairWeight T j ≤ 3 := by
  unfold pairFamily
  rw [Finset.sum_sigma]
  have : ∀ i : Fin 3, ∑ p ∈ (T i).offDiag, pairWeight T ⟨i, p⟩ ≤ 1 := by
    intro i
    simp only [pairWeight, Finset.sum_const, nsmul_eq_mul, Finset.offDiag_card]
    rcases Nat.eq_zero_or_pos (T i).card with h0 | hpos
    · simp [h0]
    · have hc : (0 : ℝ) < (T i).card := by exact_mod_cast hpos
      rw [mul_one_div, div_le_one (by positivity)]
      have : (T i).card * (T i).card - (T i).card ≤ (T i).card ^ 2 := by
        rw [sq]; exact Nat.sub_le _ _
      exact_mod_cast this
  calc ∑ i : Fin 3, ∑ p ∈ (T i).offDiag, pairWeight T ⟨i, p⟩ ≤ ∑ _i : Fin 3, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => this i
    _ = 3 := by simp

/-- Lemma 12. -/
theorem hash_bound (E : Multiset (Vec d)) (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hE : IsBiased (1 / (k : ℝ)) E) (T : Lists d) (i : Fin 3) :
    let h := rowsMap (hashOf E k T)
    (collisions h (T i) : ℝ) ≤ 3 * Real.exp 1 * ((T i).card : ℝ) ^ 2 / 2 ^ k ∧
    ((bad h (T i)).card : ℝ) ≤ Real.exp 1 * ((T i).card : ℝ) ^ 2 / 2 ^ k ∧
    (16 * n ≤ 2 ^ k → ((bad h (T i)).card : ℝ) ≤ ((T i).card : ℝ) ^ 2 / (2 * n)) := by
  dsimp only
  have hlen : (hashOf E k T).length = k := greedyRows_length _ _ _
  have hg : IsGreedy E (surv (pairFamily T) pairVec (pairWeight T)) (hashOf E k T) :=
    isGreedy_greedyRows E hE.1 _ k
  have hv : ∀ j ∈ pairFamily T, pairVec j ≠ 0 := by
    rintro ⟨i, x, y⟩ hj
    simp only [pairFamily, Finset.mem_sigma, Finset.mem_univ, true_and,
      Finset.mem_offDiag] at hj
    simp only [pairVec, ne_eq, vec_add_eq_zero_iff]
    exact hj.2.2
  have hω : ∀ j ∈ pairFamily T, 0 ≤ pairWeight T j := fun j _ => by
    unfold pairWeight; positivity
  have hb := greedy_bound_exp hE (by positivity) (pairFamily T) pairVec (pairWeight T) hv hω
    (hashOf E k T) hg (by rw [hlen]; exact hk) (by rw [hlen])
  have hpow : (2 : ℝ)⁻¹ ^ (hashOf E k T).length = ((2 : ℝ) ^ k)⁻¹ := by rw [hlen, inv_pow]
  rw [surv_pairFamily, hpow] at hb
  set h := rowsMap (hashOf E k T)
  have hsum := sum_pairWeight_le T
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hb' : ∑ i, (collisions h (T i) : ℝ) / ((T i).card : ℝ) ^ 2 ≤
      3 * Real.exp 1 / 2 ^ k := by
    refine le_trans hb ?_
    rw [mul_comm (3 : ℝ), mul_div_assoc, div_eq_mul_inv (3 : ℝ)]
    have : 0 ≤ Real.exp 1 * ((2 : ℝ) ^ k)⁻¹ := by positivity
    calc Real.exp 1 * ((2 : ℝ) ^ k)⁻¹ * ∑ j ∈ pairFamily T, pairWeight T j
        ≤ Real.exp 1 * ((2 : ℝ) ^ k)⁻¹ * 3 := mul_le_mul_of_nonneg_left hsum this
      _ = Real.exp 1 * (3 * ((2 : ℝ) ^ k)⁻¹) := by ring
  have hi : (collisions h (T i) : ℝ) / ((T i).card : ℝ) ^ 2 ≤ 3 * Real.exp 1 / 2 ^ k :=
    le_trans (Finset.single_le_sum (f := fun i => (collisions h (T i) : ℝ) /
      ((T i).card : ℝ) ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)) hb'
  have h1 : (collisions h (T i) : ℝ) ≤ 3 * Real.exp 1 * ((T i).card : ℝ) ^ 2 / 2 ^ k := by
    rcases Nat.eq_zero_or_pos (T i).card with h0 | hpos
    · have : T i = ∅ := Finset.card_eq_zero.mp h0
      simp [collisions, this]
    · have hc : (0 : ℝ) < ((T i).card : ℝ) ^ 2 := by positivity
      rw [div_le_iff₀ hc] at hi
      calc (collisions h (T i) : ℝ) ≤ 3 * Real.exp 1 / 2 ^ k * ((T i).card : ℝ) ^ 2 := hi
        _ = 3 * Real.exp 1 * ((T i).card : ℝ) ^ 2 / 2 ^ k := by ring
  have h3 : (3 * (bad h (T i)).card : ℝ) ≤ collisions h (T i) := by
    exact_mod_cast three_mul_bad_le h (T i)
  have h2 : ((bad h (T i)).card : ℝ) ≤ Real.exp 1 * ((T i).card : ℝ) ^ 2 / 2 ^ k := by
    have : 3 * Real.exp 1 * ((T i).card : ℝ) ^ 2 / 2 ^ k =
        3 * (Real.exp 1 * ((T i).card : ℝ) ^ 2 / 2 ^ k) := by ring
    linarith
  refine ⟨h1, h2, fun h16 => le_trans h2 ?_⟩
  have h16' : (16 * n : ℝ) ≤ 2 ^ k := by exact_mod_cast h16
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have he8 : Real.exp 1 ≤ 8 := by have := Real.exp_one_lt_d9; norm_num at this; linarith
  rw [div_le_div_iff₀ h2k (by positivity)]
  have hc2 : 0 ≤ ((T i).card : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h16' hc2, mul_le_mul_of_nonneg_right he8 hc2,
    mul_nonneg hc2 hn'.le]

-- the rank instances of step (C)
/-- The `ρ`-th element (`ρ : Fin 3`, rank `ρ + 1`) of a bucket in a fixed enumeration, if the
bucket is not overfull. -/
noncomputable def rankEntry {k : ℕ} (h : Vec d →ₗ[ZMod 2] Vec k) (T : Finset (Vec d))
    (ρ : Fin 3) (β : Vec k) : Option (Vec d) :=
  if (bucket h T β).card ≤ 3 then (bucket h T β).toList[(ρ : ℕ)]? else none

theorem rankEntry_sound {k : ℕ} (h : Vec d →ₗ[ZMod 2] Vec k) (T : Finset (Vec d))
    (ρ : Fin 3) (β : Vec k) (x : Vec d) (hx : rankEntry h T ρ β = some x) :
    x ∈ T ∧ h x = β := by
  unfold rankEntry at hx
  split_ifs at hx with hc
  have hm : x ∈ (bucket h T β).toList := List.mem_of_getElem? hx
  exact Finset.mem_filter.mp (Finset.mem_toList.mp hm)

theorem rankEntry_complete {k : ℕ} (h : Vec d →ₗ[ZMod 2] Vec k) (T : Finset (Vec d))
    (x : Vec d) (hx : x ∈ T) (hgood : x ∉ bad h T) :
    ∃ ρ : Fin 3, rankEntry h T ρ (h x) = some x := by
  have hc : (bucket h T (h x)).card ≤ 3 := by
    by_contra hc
    exact hgood (Finset.mem_filter.mpr ⟨hx, by omega⟩)
  have hm : x ∈ (bucket h T (h x)).toList :=
    Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨hx, rfl⟩)
  have hlt := List.idxOf_lt_length_iff.mpr hm
  rw [Finset.length_toList] at hlt
  refine ⟨⟨List.idxOf x (bucket h T (h x)).toList, by omega⟩, ?_⟩
  unfold rankEntry
  rw [if_pos hc]
  exact List.getElem?_idxOf hm

-- the procedure, with the hash given as a function of the node
/-- `Solve` with fuel: a leaf (some list has at most 2 elements, or the fuel is spent) answers
by the exact test `HasSol3` (the note's leaf test by binary search); an inner node answers yes
if one of the 27 rank instances has a solution or one of the three children answers yes. -/
noncomputable def solve (hash : Lists d → List (Vec d)) : ℕ → Lists d → Prop
  | 0, T => HasSol3 T
  | f + 1, T =>
    if ∃ i, (T i).card ≤ 2 then HasSol3 T else
      (∃ ρ : Fin 3 × Fin 3 × Fin 3,
        ConvHasSol (rankEntry (rowsMap (hash T)) (T 0) ρ.1)
                   (rankEntry (rowsMap (hash T)) (T 1) ρ.2.1)
                   (rankEntry (rowsMap (hash T)) (T 2) ρ.2.2)) ∨
      ∃ i, solve hash f (Function.update T i (bad (rowsMap (hash T)) (T i)))

theorem hasSol3_mono {T T' : Lists d} (hT : ∀ i, T' i ⊆ T i) (h : HasSol3 T') : HasSol3 T := by
  obtain ⟨x₁, h₁, x₂, h₂, x₃, h₃, hs⟩ := h
  exact ⟨x₁, hT 0 h₁, x₂, hT 1 h₂, x₃, hT 2 h₃, hs⟩

theorem hasSol3_update_bad {k : ℕ} (h : Vec d →ₗ[ZMod 2] Vec k) (T : Lists d) (i : Fin 3)
    (x : Fin 3 → Vec d) (hx : ∀ j, x j ∈ T j) (hi : x i ∈ bad h (T i))
    (hs : x 0 + x 1 + x 2 = 0) :
    HasSol3 (Function.update T i (bad h (T i))) := by
  have hmem : ∀ j, x j ∈ Function.update T i (bad h (T i)) j := by
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hi
    · rw [Function.update_of_ne hj]; exact hx j
  exact ⟨x 0, hmem 0, x 1, hmem 1, x 2, hmem 2, hs⟩

/-- Lemma 14: correct for every hash and every fuel. -/
theorem solve_iff (hash : Lists d → List (Vec d)) (f : ℕ) (T : Lists d) :
    solve hash f T ↔ HasSol3 T := by
  induction f generalizing T with
  | zero => exact Iff.rfl
  | succ f ih =>
    rw [solve]
    split_ifs with hleaf
    · exact Iff.rfl
    set h := rowsMap (hash T)
    constructor
    · rintro (⟨ρ, i, j, a, b, c, ha, hb, hc, habc⟩ | ⟨i, hi⟩)
      · exact ⟨a, (rankEntry_sound h _ _ _ a ha).1, b, (rankEntry_sound h _ _ _ b hb).1,
          c, (rankEntry_sound h _ _ _ c hc).1, habc⟩
      · refine hasSol3_mono (fun j => ?_) ((ih _).mp hi)
        by_cases hj : j = i
        · subst hj; rw [Function.update_self]; exact Finset.filter_subset _ _
        · rw [Function.update_of_ne hj]
    · rintro ⟨x₁, h₁, x₂, h₂, x₃, h₃, hs⟩
      set x : Fin 3 → Vec d := ![x₁, x₂, x₃] with hxdef
      have hx : ∀ j, x j ∈ T j := by
        intro j; fin_cases j
        · exact h₁
        · exact h₂
        · exact h₃
      have hs' : x 0 + x 1 + x 2 = 0 := hs
      by_cases hb : ∃ i, x i ∈ bad h (T i)
      · obtain ⟨i, hi⟩ := hb
        exact Or.inr ⟨i, (ih _).mpr (hasSol3_update_bad h T i x hx hi hs')⟩
      · push Not at hb
        obtain ⟨ρ₀, e₀⟩ := rankEntry_complete h (T 0) x₁ h₁ (hb 0)
        obtain ⟨ρ₁, e₁⟩ := rankEntry_complete h (T 1) x₂ h₂ (hb 1)
        obtain ⟨ρ₂, e₂⟩ := rankEntry_complete h (T 2) x₃ h₃ (hb 2)
        have h3 : x₃ = x₁ + x₂ := ((vec_add_eq_zero_iff _ _).mp hs).symm
        refine Or.inl ⟨(ρ₀, ρ₁, ρ₂), h x₁, h x₂, x₁, x₂, x₃, e₀, e₁, ?_, hs⟩
        rw [← map_add, ← h3]
        exact e₂

-- the recursion tree (Lemma 13), for the greedy hash
/-- The node reached from the root `S` along a path of child indices (head = last step). -/
noncomputable def nodeAt (step : Lists d → Fin 3 → Finset (Vec d)) (S : Lists d) :
    List (Fin 3) → Lists d
  | [] => S
  | i :: p => Function.update (nodeAt step S p) i (step (nodeAt step S p) i)

def IsInner (T : Lists d) : Prop := ∀ i, 3 ≤ (T i).card

/-- A path is in the tree if every node strictly above its end is inner. -/
def InTree (step : Lists d → Fin 3 → Finset (Vec d)) (S : Lists d) : List (Fin 3) → Prop
  | [] => True
  | i :: p => InTree step S p ∧ IsInner (nodeAt step S p)

def dSeq : ℕ → ℕ
  | 0 => 1
  | r + 1 => 2 * dSeq r ^ 2

theorem dSeq_eq (r : ℕ) : dSeq r = 2 ^ (2 ^ r - 1) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [dSeq, ih, ← pow_mul, ← pow_succ']
    congr 1
    have := Nat.one_le_two_pow (n := r)
    rw [pow_succ]
    omega

theorem dSeq_pos (r : ℕ) : 0 < dSeq r := by
  rw [dSeq_eq]; positivity

theorem dSeq_mono : Monotone dSeq := by
  refine monotone_nat_of_le_succ fun r => ?_
  rw [dSeq_eq, dSeq_eq]
  exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le_sub_right
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ r)) 1)

/-- Hypothesis of Lemma 13: a step that keeps subsets and satisfies `|bad| ≤ |T|²/(2n)`. -/
def GoodStep (n : ℕ) (step : Lists d → Fin 3 → Finset (Vec d)) : Prop :=
  ∀ T i, step T i ⊆ T i ∧ ((step T i).card : ℝ) ≤ ((T i).card : ℝ) ^ 2 / (2 * n)

theorem card_nodeAt_le (n : ℕ) (hn : 2 ≤ n) (step : Lists d → Fin 3 → Finset (Vec d))
    (hstep : GoodStep n step) (S : Lists d) (hS : ∀ i, (S i).card ≤ n)
    (p : List (Fin 3)) (i : Fin 3) :
    ((nodeAt step S p i).card : ℝ) ≤ n / dSeq (p.count i) := by
  induction p generalizing i with
  | nil =>
    simp only [nodeAt, List.count_nil, dSeq, Nat.cast_one, div_one]
    exact_mod_cast hS i
  | cons j p ih =>
    simp only [nodeAt]
    by_cases hij : i = j
    · subst hij
      rw [Function.update_self, List.count_cons_self]
      have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have hd : (0 : ℝ) < dSeq (p.count i) := by exact_mod_cast dSeq_pos _
      have h1 := (hstep (nodeAt step S p) i).2
      have h2 : ((nodeAt step S p i).card : ℝ) ^ 2 ≤ ((n : ℝ) / dSeq (p.count i)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (ih i) 2
      refine le_trans h1 (le_trans (div_le_div_of_nonneg_right h2 (by positivity)) ?_)
      rw [dSeq]
      push_cast
      apply le_of_eq
      field_simp
    · rw [Function.update_of_ne hij, List.count_cons_of_ne (Ne.symm hij)]
      exact ih i

theorem count_le_of_inner (n : ℕ) (hn : 2 ≤ n) (step : Lists d → Fin 3 → Finset (Vec d))
    (hstep : GoodStep n step) (S : Lists d) (hS : ∀ i, (S i).card ≤ n)
    (p : List (Fin 3)) (hp : IsInner (nodeAt step S p)) (i : Fin 3) :
    p.count i ≤ Nat.log 2 (Nat.log 2 n) := by
  set L := Nat.log 2 n with hL
  set R := Nat.log 2 L with hR
  by_contra hc
  push Not at hc
  have h1 := card_nodeAt_le n hn step hstep S hS p i
  have h3 : (3 : ℝ) ≤ (nodeAt step S p i).card := by exact_mod_cast hp i
  have hd : (0 : ℝ) < dSeq (p.count i) := by exact_mod_cast dSeq_pos _
  have h4 : (3 * dSeq (p.count i) : ℝ) ≤ n := by
    have := le_trans h3 h1
    rwa [le_div_iff₀ hd] at this
  have h4' : 3 * dSeq (p.count i) ≤ n := by exact_mod_cast h4
  have h5 : dSeq (R + 1) ≤ dSeq (p.count i) := dSeq_mono hc
  have h6 : L < 2 ^ (R + 1) := Nat.lt_pow_succ_log_self (by norm_num) L
  have h7 : 2 ^ L ≤ dSeq (R + 1) := by
    rw [dSeq_eq]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have h8 : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  rw [pow_succ] at h8
  omega

theorem length_eq_count_sum (p : List (Fin 3)) :
    p.length = p.count 0 + p.count 1 + p.count 2 := by
  induction p with
  | nil => rfl
  | cons j p ih =>
    fin_cases j <;> simp [ih] <;> omega

/-- Inner nodes have depth at most `3R`, so `solve` with fuel `3R + 1` never stops for lack
of fuel at an inner node. -/
theorem length_le_of_inner (n : ℕ) (hn : 2 ≤ n) (step : Lists d → Fin 3 → Finset (Vec d))
    (hstep : GoodStep n step) (S : Lists d) (hS : ∀ i, (S i).card ≤ n)
    (p : List (Fin 3)) (hp : IsInner (nodeAt step S p)) :
    p.length ≤ 3 * Nat.log 2 (Nat.log 2 n) := by
  have h0 := count_le_of_inner n hn step hstep S hS p hp 0
  have h1 := count_le_of_inner n hn step hstep S hS p hp 1
  have h2 := count_le_of_inner n hn step hstep S hS p hp 2
  rw [length_eq_count_sum]
  omega

/-- Every path in the tree has length at most `3R + 1`, `R = ⌊log log n⌋`; the tree is the
finset of such paths. -/
theorem length_le_of_inTree (n : ℕ) (hn : 2 ≤ n) (step : Lists d → Fin 3 → Finset (Vec d))
    (hstep : GoodStep n step) (S : Lists d) (hS : ∀ i, (S i).card ≤ n)
    (p : List (Fin 3)) (hp : InTree step S p) :
    p.length ≤ 3 * Nat.log 2 (Nat.log 2 n) + 1 := by
  cases p with
  | nil => simp
  | cons i q =>
    have := length_le_of_inner n hn step hstep S hS q hp.2
    simp only [List.length_cons]
    omega

noncomputable def tree (n : ℕ) (step : Lists d → Fin 3 → Finset (Vec d)) (S : Lists d) :
    Finset (List (Fin 3)) :=
  open Classical in
  ((Finset.range (3 * Nat.log 2 (Nat.log 2 n) + 2)).biUnion fun j =>
    (Finset.univ : Finset (Fin j → Fin 3)).image List.ofFn).filter (InTree step S)

/-- Lists of length `< m` lie in the finset of `List.ofFn`'s of lengths `< m`. -/
theorem mem_ofFn_range (m : ℕ) (p : List (Fin 3)) (hp : p.length < m) :
    p ∈ (Finset.range m).biUnion fun j =>
      (Finset.univ : Finset (Fin j → Fin 3)).image List.ofFn := by
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨p.length, hp, p.get, List.ofFn_get p⟩

theorem mem_tree_iff (n : ℕ) (hn : 2 ≤ n) (step : Lists d → Fin 3 → Finset (Vec d))
    (hstep : GoodStep n step) (S : Lists d) (hS : ∀ i, (S i).card ≤ n) (p : List (Fin 3)) :
    p ∈ tree n step S ↔ InTree step S p := by
  unfold tree
  simp only [Finset.mem_filter]
  refine ⟨fun h => h.2, fun h => ⟨mem_ofFn_range _ p ?_, h⟩⟩
  have := length_le_of_inTree n hn step hstep S hS p h
  omega

theorem card_ofFn_range (m : ℕ) :
    2 * ((Finset.range m).biUnion fun j =>
      (Finset.univ : Finset (Fin j → Fin 3)).image List.ofFn).card + 1 ≤ 3 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert]
    have h1 := Finset.card_union_le ((Finset.univ : Finset (Fin m → Fin 3)).image List.ofFn)
      ((Finset.range m).biUnion fun j => (Finset.univ : Finset (Fin j → Fin 3)).image List.ofFn)
    have h2 : ((Finset.univ : Finset (Fin m → Fin 3)).image List.ofFn).card ≤ 3 ^ m := by
      refine le_trans Finset.card_image_le ?_
      simp
    rw [pow_succ]
    omega

theorem tree_card_le (n : ℕ) (hn : 2 ≤ n) (step : Lists d → Fin 3 → Finset (Vec d))
    (hstep : GoodStep n step) (S : Lists d) (hS : ∀ i, (S i).card ≤ n) :
    ((tree n step S).card : ℝ) ≤ 1 + 9 / 2 * 27 ^ Nat.log 2 (Nat.log 2 n) := by
  classical
  set R := Nat.log 2 (Nat.log 2 n)
  set Q := (Finset.range (3 * R + 1)).biUnion fun j =>
      (Finset.univ : Finset (Fin j → Fin 3)).image List.ofFn
  have hsub : tree n step S ⊆
      insert ([] : List (Fin 3)) ((Finset.univ ×ˢ Q).image fun q : Fin 3 × List (Fin 3) => q.1 :: q.2) := by
    intro p hp
    rw [mem_tree_iff n hn step hstep S hS] at hp
    rw [Finset.mem_insert, Finset.mem_image]
    cases p with
    | nil => exact Or.inl rfl
    | cons i q =>
      right
      have := length_le_of_inner n hn step hstep S hS q hp.2
      exact ⟨(i, q), Finset.mem_product.mpr ⟨Finset.mem_univ _,
        mem_ofFn_range _ q (by omega)⟩, rfl⟩
  have hc : (tree n step S).card ≤ 1 + 3 * Q.card := by
    refine le_trans (Finset.card_le_card hsub) (le_trans (Finset.card_insert_le _ _) ?_)
    have h1 := Finset.card_image_le (s := (Finset.univ : Finset (Fin 3)) ×ˢ Q)
      (f := fun q : Fin 3 × List (Fin 3) => q.1 :: q.2)
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hQ : 2 * Q.card + 1 ≤ 3 ^ (3 * R + 1) := card_ofFn_range (3 * R + 1)
  have h27 : (3 : ℕ) ^ (3 * R + 1) = 3 * 27 ^ R := by
    rw [pow_succ, pow_mul]; norm_num; ring
  rw [h27] at hQ
  have hN : 2 * (tree n step S).card ≤ 2 + 9 * 27 ^ R := by omega
  have hR : (2 * (tree n step S).card : ℝ) ≤ 2 + 9 * 27 ^ R := by exact_mod_cast hN
  linarith

/-- The real comparison, stated separately. -/
theorem tree_bound_real (n : ℕ) (hn : 2 ≤ n) :
    1 + 9 / 2 * (27 : ℝ) ^ Nat.log 2 (Nat.log 2 n) ≤ 6 * Real.logb 2 n ^ Real.logb 2 27 := by
  set L := Nat.log 2 n with hL
  set R := Nat.log 2 L with hR
  have hL1 : 1 ≤ L := Nat.log_pos (by norm_num) hn
  have hx : (L : ℝ) ≤ Real.logb 2 n := by
    have := Real.natLog_le_logb n 2; exact_mod_cast this
  have h2R : ((2 : ℝ) ^ R) ≤ L := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : L ≠ 0)
  have hx1 : (1 : ℝ) ≤ Real.logb 2 n := le_trans (by exact_mod_cast hL1) hx
  have hl27 : 0 ≤ Real.logb 2 27 := Real.logb_nonneg (by norm_num) (by norm_num)
  have h27 : (27 : ℝ) ^ R = ((2 : ℝ) ^ R) ^ Real.logb 2 27 := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  have hle : (27 : ℝ) ^ R ≤ Real.logb 2 n ^ Real.logb 2 27 := by
    rw [h27]
    exact Real.rpow_le_rpow (by positivity) (le_trans h2R hx) hl27
  have hX : 1 ≤ Real.logb 2 n ^ Real.logb 2 27 := Real.one_le_rpow hx1 hl27
  linarith

/-- The greedy hash gives a good step (Lemma 12 feeding Lemma 13). -/
theorem goodStep_greedy (E : Multiset (Vec d)) (n : ℕ) (hn : 2 ≤ n)
    (hE : IsBiased (1 / (kOf n : ℝ)) E) :
    GoodStep n (fun T i => bad (rowsMap (hashOf E (kOf n) T)) (T i)) := by
  intro T i
  have hk : 0 < kOf n := by unfold kOf; omega
  refine ⟨Finset.filter_subset _ _, ?_⟩
  exact (hash_bound E (kOf n) n hk (by omega) hE T i).2.2 (kOf_spec n hn).2.2.2.1

end Xor

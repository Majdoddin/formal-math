import Mathlib

/-!
# Theorem G (groups of exponent `p²`): the combinatorial core

Section 19.6 of the paper. Here `R = ZMod (p^2)`, vectors are `Fin d → ZMod (p^2)`, `p` prime.

* `residue` (reduction mod `p`, coordinatewise), `lift` (entries in `{0, …, p−1}`), `divp`
  (`v/p` for `v ∈ pR^d`), pair rows `pairRow a b = lift a + p • lift b`;
* the two facts (F1) `F1` and (F2) `F2`, with the explicit `c₀ = c0 a v`;
* the middle part `K(ker π)` of Part L (`midL_card`) and of Part H (`midH_card`): at most `p^q`
  elements, every `K`-coordinate in `pR`;
* heavy and light: `light_triples_le` (and the light list in position 1 or 2), Part H's
  `TI_classes_lt`, and the number of nonempty classes of `(residue, k′ more coordinates)`
  (`classes_card_le`);
* Lemma G1 in abstract form (`G1_avg`, `exists_le_avg`, `G1_step`, `G1_iterate`,
  `one_add_sq_pow_le_exp`);
* the final arithmetic of Part L (`partL_final`).
-/

set_option linter.unusedSectionVars false

namespace GroupLean
namespace ExpP2

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

instance neZero_p : NeZero p := ⟨hp.out.ne_zero⟩
instance neZero_sq : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.out.ne_zero⟩

/-! ### Scalars: reduction, lift, division by `p` -/

/-- Reduction `ZMod (p^2) → ZMod p`. -/
def red (p : ℕ) : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)

theorem red_apply (x : ZMod (p ^ 2)) : red p x = (x.val : ZMod p) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  exact map_natCast _ _

theorem red_eq_zero_iff (x : ZMod (p ^ 2)) : red p x = 0 ↔ p ∣ x.val := by
  rw [red_apply, ZMod.natCast_eq_zero_iff]

/-- `lift a ∈ {0, …, p−1} ⊆ ZMod (p^2)`. -/
def lift1 (a : ZMod p) : ZMod (p ^ 2) := (a.val : ZMod (p ^ 2))

theorem red_lift1 (a : ZMod p) : red p (lift1 a) = a := by
  rw [lift1, map_natCast, ZMod.natCast_zmod_val]

theorem lift1_zero : lift1 (0 : ZMod p) = 0 := by simp [lift1]

/-- `x / p` for `x ∈ pR`: `⌊val x / p⌋ mod p`. -/
def sdivp (x : ZMod (p ^ 2)) : ZMod p := ((x.val / p : ℕ) : ZMod p)

/-- If `x ≡ 0 mod p` then `x = p · lift(x/p)`. -/
theorem eq_p_mul (x : ZMod (p ^ 2)) (h : red p x = 0) :
    x = (p : ZMod (p ^ 2)) * lift1 (sdivp x) := by
  rw [red_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  have hp0 : 0 < p := hp.out.pos
  have hlt : x.val < p ^ 2 := ZMod.val_lt x
  have hm_lt : m < p := by
    by_contra hc
    push Not at hc
    rw [hm, pow_two] at hlt
    nlinarith [Nat.mul_le_mul_left p hc]
  have hdiv : x.val / p = m := by rw [hm, Nat.mul_div_cancel_left m hp0]
  rw [sdivp, hdiv, lift1, ZMod.val_natCast, Nat.mod_eq_of_lt hm_lt, ← Nat.cast_mul, ← hm,
    ZMod.natCast_zmod_val]

/-- `p · x = 0` in `ZMod (p^2)` iff `x ≡ 0 mod p`. -/
theorem p_mul_eq_zero_iff (x : ZMod (p ^ 2)) : (p : ZMod (p ^ 2)) * x = 0 ↔ red p x = 0 := by
  rw [red_eq_zero_iff]
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
  have key : ∀ n : ℕ, p ^ 2 ∣ p * n ↔ p ∣ n := fun n => by
    rw [pow_two]; exact Nat.mul_dvd_mul_iff_left hp.out.pos
  exact key _

theorem pp_zero : (p : ZMod (p ^ 2)) * p = 0 := by
  rw [← Nat.cast_mul, ← pow_two, ZMod.natCast_self]

/-! ### Vectors -/

variable {d : ℕ}

/-- The residue `x̄ ∈ F_p^d`. -/
def residue (v : Fin d → ZMod (p ^ 2)) : Fin d → ZMod p := fun j => red p (v j)

theorem residue_add (x y : Fin d → ZMod (p ^ 2)) : residue (x + y) = residue x + residue y :=
  funext fun _ => map_add (red p) _ _

theorem residue_sub (x y : Fin d → ZMod (p ^ 2)) : residue (x - y) = residue x - residue y :=
  funext fun _ => map_sub (red p) _ _

theorem residue_zero : residue (0 : Fin d → ZMod (p ^ 2)) = 0 :=
  funext fun _ => map_zero (red p)

/-- The residue as a homomorphism. -/
def residueHom : (Fin d → ZMod (p ^ 2)) →+ (Fin d → ZMod p) where
  toFun := residue
  map_zero' := residue_zero
  map_add' := residue_add

theorem residueHom_apply (x : Fin d → ZMod (p ^ 2)) : residueHom x = residue x := rfl

/-- `lift a`, coordinatewise. -/
def lift (a : Fin d → ZMod p) : Fin d → ZMod (p ^ 2) := fun j => lift1 (a j)

theorem residue_lift (a : Fin d → ZMod p) : residue (lift a) = a :=
  funext fun j => red_lift1 (a j)

theorem lift_zero : lift (0 : Fin d → ZMod p) = 0 := funext fun _ => lift1_zero

/-- `v / p` coordinatewise. -/
def divp (v : Fin d → ZMod (p ^ 2)) : Fin d → ZMod p := fun j => sdivp (v j)

/-- For `v ∈ pR^d`, `v = p · lift(v/p)`. -/
theorem eq_p_smul_lift_divp (v : Fin d → ZMod (p ^ 2)) (hv : residue v = 0) :
    v = (p : ZMod (p ^ 2)) • lift (divp v) :=
  funext fun j => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact eq_p_mul (v j) (congrFun hv j)

theorem red_dot (x y : Fin d → ZMod (p ^ 2)) : red p (x ⬝ᵥ y) = residue x ⬝ᵥ residue y :=
  RingHom.map_dotProduct (red p) x y

/-- The pair row `u = lift a + p · lift b`. -/
def pairRow (a b : Fin d → ZMod p) : Fin d → ZMod (p ^ 2) := lift a + p • lift b

theorem residue_pairRow (a b : Fin d → ZMod p) : residue (pairRow a b) = a := by
  funext j
  show red p (lift1 (a j) + (p • lift b) j) = a j
  rw [Pi.smul_apply, map_add, map_nsmul, red_lift1, nsmul_eq_mul, ZMod.natCast_self, zero_mul,
    add_zero]

theorem pairRow_zero (a : Fin d → ZMod p) : pairRow a 0 = lift a := by
  simp [pairRow, lift_zero]

/-- The low digit of a pair row: `⟨u, x⟩ mod p = ⟨a, x̄⟩`. -/
theorem red_pairRow_dot (a b : Fin d → ZMod p) (x : Fin d → ZMod (p ^ 2)) :
    red p (pairRow a b ⬝ᵥ x) = a ⬝ᵥ residue x := by
  rw [red_dot, residue_pairRow]

/-- **(F1)** If `v ∈ pR^d`, then `⟨u, v⟩ = 0` iff `⟨a, v/p⟩ = 0`; the part `b` plays no role. -/
theorem F1 (a b : Fin d → ZMod p) (v : Fin d → ZMod (p ^ 2)) (hv : residue v = 0) :
    pairRow a b ⬝ᵥ v = 0 ↔ a ⬝ᵥ divp v = 0 := by
  have e : pairRow a b ⬝ᵥ v = (p : ZMod (p ^ 2)) * (lift a ⬝ᵥ lift (divp v)) := by
    conv_lhs => rw [eq_p_smul_lift_divp v hv]
    rw [dotProduct_smul, smul_eq_mul, pairRow, add_dotProduct, smul_dotProduct, nsmul_eq_mul,
      mul_add, ← mul_assoc, pp_zero, zero_mul, add_zero]
  rw [e, p_mul_eq_zero_iff, red_dot, residue_lift, residue_lift]

/-- (F1) with `b = 0` (the rows `lift a` of Part H). -/
theorem F1_lift (a : Fin d → ZMod p) (v : Fin d → ZMod (p ^ 2)) (hv : residue v = 0) :
    lift a ⬝ᵥ v = 0 ↔ a ⬝ᵥ divp v = 0 := by
  rw [← pairRow_zero]; exact F1 a 0 v hv

/-- `c₀(a, v) := ⟨lift a, v⟩ / p` (meaningful when `⟨a, v̄⟩ = 0`). -/
def c0 (a : Fin d → ZMod p) (v : Fin d → ZMod (p ^ 2)) : ZMod p := sdivp (lift a ⬝ᵥ v)

/-- `⟨lift a, v⟩ = p · c₀(a, v)` when `⟨a, v̄⟩ = 0`. -/
theorem lift_dot_eq (a : Fin d → ZMod p) (v : Fin d → ZMod (p ^ 2)) (h : a ⬝ᵥ residue v = 0) :
    lift a ⬝ᵥ v = (p : ZMod (p ^ 2)) * lift1 (c0 a v) :=
  eq_p_mul _ (by rw [red_dot, residue_lift]; exact h)

/-- **(F2)** If `⟨a, v̄⟩ = 0`, then `⟨u, v⟩ = 0` iff `⟨b, v̄⟩ = −c₀(a, v)`. -/
theorem F2 (a b : Fin d → ZMod p) (v : Fin d → ZMod (p ^ 2)) (h : a ⬝ᵥ residue v = 0) :
    pairRow a b ⬝ᵥ v = 0 ↔ b ⬝ᵥ residue v = -c0 a v := by
  have e : pairRow a b ⬝ᵥ v = (p : ZMod (p ^ 2)) * (lift1 (c0 a v) + lift b ⬝ᵥ v) := by
    rw [pairRow, add_dotProduct, smul_dotProduct, nsmul_eq_mul, lift_dot_eq a v h, mul_add]
  rw [e, p_mul_eq_zero_iff, map_add, red_lift1, red_dot, residue_lift]
  constructor <;> intro h' <;> linear_combination h'

/-- A pair row kills `v` only if `⟨a, v̄⟩ = 0` (the low digit). -/
theorem pairRow_dot_zero_imp (a b : Fin d → ZMod p) (v : Fin d → ZMod (p ^ 2))
    (h : pairRow a b ⬝ᵥ v = 0) : a ⬝ᵥ residue v = 0 := by
  rw [← red_pairRow_dot a b, h, map_zero]

/-! ### The middle part `K(ker π)` -/

/-- A subgroup of `A × (Fin q → ZMod (p^2))` whose elements have first component `0` and all
other coordinates in `pR` has at most `p^q` elements. -/
theorem card_le_of_red_zero {A : Type*} [AddCommGroup A] {q : ℕ}
    (H : AddSubgroup (A × (Fin q → ZMod (p ^ 2))))
    (h : ∀ y ∈ H, y.1 = 0 ∧ ∀ i, red p (y.2 i) = 0) : Nat.card H ≤ p ^ q := by
  have hinj : Function.Injective (fun y : H => fun i => sdivp (y.1.2 i)) := by
    intro y y' e
    obtain ⟨h1, h2⟩ := h y y.2
    obtain ⟨h1', h2'⟩ := h y' y'.2
    apply Subtype.ext
    refine Prod.ext (h1.trans h1'.symm) (funext fun i => ?_)
    have e' : sdivp (y.1.2 i) = sdivp (y'.1.2 i) := congrFun e i
    calc y.1.2 i = (p : ZMod (p ^ 2)) * lift1 (sdivp (y.1.2 i)) := eq_p_mul _ (h2 i)
      _ = (p : ZMod (p ^ 2)) * lift1 (sdivp (y'.1.2 i)) := by rw [e']
      _ = y'.1.2 i := (eq_p_mul _ (h2' i)).symm
  calc Nat.card H ≤ Nat.card (Fin q → ZMod p) := Nat.card_le_card_of_injective _ hinj
    _ = p ^ q := by rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]

section partL
variable {k q : ℕ}

/-- Part L: `π(x) = (ρ(x̄), (⟨a_i, x̄⟩)_{i ≤ q})` with residue rows `r` and the low digits `a`. -/
def piL (r : Fin k → Fin d → ZMod p) (a : Fin q → Fin d → ZMod p) :
    (Fin d → ZMod (p ^ 2)) →+ (Fin k → ZMod p) × (Fin q → ZMod p) where
  toFun x := (fun i => r i ⬝ᵥ residue x, fun i => a i ⬝ᵥ residue x)
  map_zero' := by simp only [residue_zero, dotProduct_zero]; rfl
  map_add' x y := by simp only [residue_add, dotProduct_add]; rfl

/-- Part L: `K(x) = (ρ(x̄), (⟨u_i, x⟩)_{i ≤ q})`, `u_i = lift a_i + p · lift b_i`. -/
def KL (r : Fin k → Fin d → ZMod p) (a b : Fin q → Fin d → ZMod p) :
    (Fin d → ZMod (p ^ 2)) →+ (Fin k → ZMod p) × (Fin q → ZMod (p ^ 2)) where
  toFun x := (fun i => r i ⬝ᵥ residue x, fun i => pairRow (a i) (b i) ⬝ᵥ x)
  map_zero' := by simp only [residue_zero, dotProduct_zero]; rfl
  map_add' x y := by simp only [residue_add, dotProduct_add]; rfl

/-- `π` is `K` followed by reduction: `K x = 0 → π x = 0`. -/
theorem KL_factor (r : Fin k → Fin d → ZMod p) (a b : Fin q → Fin d → ZMod p)
    (x : Fin d → ZMod (p ^ 2)) (h : KL r a b x = 0) : piL r a x = 0 := by
  have h1 : (fun i => r i ⬝ᵥ residue x) = 0 := congrArg Prod.fst h
  have h2 : (fun i => pairRow (a i) (b i) ⬝ᵥ x) = 0 := congrArg Prod.snd h
  refine Prod.ext h1 (funext fun i => ?_)
  exact pairRow_dot_zero_imp (a i) (b i) x (congrFun h2 i)

/-- On `ker π`, the `ρ`-part of `K` is `0` and every other coordinate of `K` lies in `pR`. -/
theorem KL_of_piL_zero (r : Fin k → Fin d → ZMod p) (a b : Fin q → Fin d → ZMod p)
    (x : Fin d → ZMod (p ^ 2)) (h : piL r a x = 0) :
    (KL r a b x).1 = 0 ∧ ∀ i, red p ((KL r a b x).2 i) = 0 := by
  have h1 : (fun i => r i ⬝ᵥ residue x) = 0 := congrArg Prod.fst h
  have h2 : (fun i => a i ⬝ᵥ residue x) = 0 := congrArg Prod.snd h
  refine ⟨h1, fun i => ?_⟩
  change red p (pairRow (a i) (b i) ⬝ᵥ x) = 0
  rw [red_pairRow_dot]
  exact congrFun h2 i

/-- The same, in the form "`K`-coordinate `= p · c`". -/
theorem KL_coord_mem_pR (r : Fin k → Fin d → ZMod p) (a b : Fin q → Fin d → ZMod p)
    (x : Fin d → ZMod (p ^ 2)) (h : piL r a x = 0) (i : Fin q) :
    ∃ c : ZMod p, (KL r a b x).2 i = (p : ZMod (p ^ 2)) * lift1 c :=
  ⟨_, eq_p_mul _ ((KL_of_piL_zero r a b x h).2 i)⟩

/-- **The middle part of Part L**: `|K(ker π)| ≤ p^q = D`. -/
theorem midL_card (r : Fin k → Fin d → ZMod p) (a b : Fin q → Fin d → ZMod p) :
    Nat.card ((piL r a).ker.map (KL r a b)) ≤ p ^ q := by
  refine card_le_of_red_zero _ fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 hy
  exact KL_of_piL_zero r a b x hx

end partL

section partH
variable {k q : ℕ}

/-- Part H: `π(x) = (x̄, (⟨lift a′_i, x⟩)_{i ≤ k′})`. -/
def piH (a' : Fin k → Fin d → ZMod p) :
    (Fin d → ZMod (p ^ 2)) →+ (Fin d → ZMod p) × (Fin k → ZMod (p ^ 2)) where
  toFun x := (residue x, fun i => lift (a' i) ⬝ᵥ x)
  map_zero' := by simp only [residue_zero, dotProduct_zero]; rfl
  map_add' x y := by simp only [residue_add, dotProduct_add]; rfl

/-- Part H: `K = (π, (⟨lift a_i, x⟩)_{i ≤ q})`. -/
def KH (a' : Fin k → Fin d → ZMod p) (a : Fin q → Fin d → ZMod p) :
    (Fin d → ZMod (p ^ 2)) →+ ((Fin d → ZMod p) × (Fin k → ZMod (p ^ 2))) × (Fin q → ZMod (p ^ 2))
    where
  toFun x := (piH a' x, fun i => lift (a i) ⬝ᵥ x)
  map_zero' := by simp only [map_zero, dotProduct_zero]; rfl
  map_add' x y := by simp only [map_add, dotProduct_add]; rfl

theorem KH_factor (a' : Fin k → Fin d → ZMod p) (a : Fin q → Fin d → ZMod p)
    (x : Fin d → ZMod (p ^ 2)) (h : KH a' a x = 0) : piH a' x = 0 :=
  congrArg Prod.fst h

/-- **The middle part of Part H**: `|K(ker π)| ≤ p^q`. -/
theorem midH_card (a' : Fin k → Fin d → ZMod p) (a : Fin q → Fin d → ZMod p) :
    Nat.card ((piH a').ker.map (KH a' a)) ≤ p ^ q := by
  refine card_le_of_red_zero _ fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.1 hy
  have hx' : piH a' x = 0 := hx
  have hres : residue x = 0 := congrArg Prod.fst hx'
  refine ⟨hx', fun i => ?_⟩
  change red p (lift (a i) ⬝ᵥ x) = 0
  rw [red_dot, residue_lift, hres, dotProduct_zero]

end partH

/-- **Part H, "Instance and costs"**: the nonempty classes of `x ↦ (x̄, (⟨lift a_i, x⟩)_{i<k′})`
number at most (nonempty residue classes) `· p^{k′}`: within a residue class the extra
coordinates lie in one coset of `(pR)^{k′}`. -/
theorem classes_card_le {k : ℕ} (S : Finset (Fin d → ZMod (p ^ 2)))
    (a : Fin k → Fin d → ZMod p) :
    (S.image fun x => (residue x, fun i => lift (a i) ⬝ᵥ x)).card ≤
      (S.image residue).card * p ^ k := by
  set F : (Fin d → ZMod (p ^ 2)) → (Fin d → ZMod p) × (Fin k → ZMod (p ^ 2)) :=
    fun x => (residue x, fun i => lift (a i) ⬝ᵥ x) with hF
  have hsub : S.image F ⊆
      (S.image residue).biUnion (fun r => (S.filter fun x => residue x = r).image F) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact Finset.mem_biUnion.2 ⟨residue x, Finset.mem_image_of_mem _ hx,
      Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hx, rfl⟩)⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  calc ∑ r ∈ S.image residue, ((S.filter fun x => residue x = r).image F).card
      ≤ ∑ _r ∈ S.image residue, p ^ k := by
        refine Finset.sum_le_sum fun r hr => ?_
        obtain ⟨x₀, -, rfl⟩ := Finset.mem_image.1 hr
        have hred : ∀ x, residue x = residue x₀ → ∀ i, red p ((F x).2 i - (F x₀).2 i) = 0 := by
          intro x hx i
          simp only [hF]
          rw [← dotProduct_sub, red_dot, residue_lift, residue_sub, hx, sub_self, dotProduct_zero]
        calc ((S.filter fun x => residue x = residue x₀).image F).card
            ≤ (Finset.univ : Finset (Fin k → ZMod p)).card := by
              refine Finset.card_le_card_of_injOn
                (fun y => fun i => sdivp (y.2 i - (F x₀).2 i))
                (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_
              intro y hy y' hy' e
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
              obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy')
              have hx1 := (Finset.mem_filter.1 hx).2
              have hx1' := (Finset.mem_filter.1 hx').2
              refine Prod.ext (by simp only [hF]; rw [hx1, hx1']) (funext fun i => ?_)
              have e' : sdivp ((F x).2 i - (F x₀).2 i) = sdivp ((F x').2 i - (F x₀).2 i) :=
                congrFun e i
              have : (F x).2 i - (F x₀).2 i = (F x').2 i - (F x₀).2 i := by
                calc (F x).2 i - (F x₀).2 i
                    = (p : ZMod (p ^ 2)) * lift1 (sdivp ((F x).2 i - (F x₀).2 i)) :=
                      eq_p_mul _ (hred x hx1 i)
                  _ = (p : ZMod (p ^ 2)) * lift1 (sdivp ((F x').2 i - (F x₀).2 i)) := by
                      rw [e']
                  _ = (F x').2 i - (F x₀).2 i := (eq_p_mul _ (hred x' hx1' i)).symm
              exact sub_left_inj.1 this
          _ = p ^ k := by
              rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    _ = (S.image residue).card * p ^ k := by rw [Finset.sum_const, smul_eq_mul]

/-! ### Heavy and light -/

section heavyLight
variable {α Q : Type*} [DecidableEq α] [AddCommGroup Q] [DecidableEq Q]

/-- If every class `{y ∈ S₃ : res y = res x}` of the third list has fewer than `m` elements, then
at most `|S₁||S₂|(m − 1)` triples have `res x₁ + res x₂ + res x₃ = 0` (for each choice of the
other two members, `res x₃` is determined). -/
theorem triples_le_of_classes_lt (res : α → Q) (S₁ S₂ S₃ : Finset α) (m : ℕ)
    (h : ∀ x ∈ S₃, (S₃.filter fun y => res y = res x).card < m) :
    ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => res t.1 + res t.2.1 + res t.2.2 = 0).card ≤
      S₁.card * S₂.card * (m - 1) := by
  rw [Finset.card_filter, Finset.sum_product]
  calc ∑ x₁ ∈ S₁, ∑ y ∈ S₂ ×ˢ S₃, (if res (x₁, y).1 + res (x₁, y).2.1 + res (x₁, y).2.2 = 0
          then 1 else 0)
      ≤ ∑ _x₁ ∈ S₁, S₂.card * (m - 1) := by
        refine Finset.sum_le_sum fun x₁ _ => ?_
        rw [Finset.sum_product]
        calc ∑ x₂ ∈ S₂, ∑ x₃ ∈ S₃, (if res (x₁, x₂, x₃).1 + res (x₁, x₂, x₃).2.1 +
                res (x₁, x₂, x₃).2.2 = 0 then 1 else 0)
            ≤ ∑ _x₂ ∈ S₂, (m - 1) := by
              refine Finset.sum_le_sum fun x₂ _ => ?_
              rw [← Finset.card_filter]
              rcases (S₃.filter fun x₃ => res (x₁, x₂, x₃).1 + res (x₁, x₂, x₃).2.1 +
                  res (x₁, x₂, x₃).2.2 = 0).eq_empty_or_nonempty with he | ⟨y, hy⟩
              · rw [he]; simp
              · have hy' := Finset.mem_filter.1 hy
                have hsub : (S₃.filter fun x₃ => res (x₁, x₂, x₃).1 + res (x₁, x₂, x₃).2.1 +
                    res (x₁, x₂, x₃).2.2 = 0) ⊆ S₃.filter fun x => res x = res y := by
                  intro x hx
                  have hx' := Finset.mem_filter.1 hx
                  refine Finset.mem_filter.2 ⟨hx'.1, ?_⟩
                  rw [eq_neg_of_add_eq_zero_right hx'.2, eq_neg_of_add_eq_zero_right hy'.2]
                have h1 := h y hy'.1
                have h2 := Finset.card_le_card hsub
                omega
          _ = S₂.card * (m - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ = S₁.card * S₂.card * (m - 1) := by rw [Finset.sum_const, smul_eq_mul, mul_assoc]

/-- The light part `L = {x ∈ S : |{y ∈ S : res y = res x}| < σ}` of a list. -/
def light (res : α → Q) (S : Finset α) (σ : ℕ) : Finset α :=
  S.filter fun x => (S.filter fun y => res y = res x).card < σ

/-- **Step 1, light list in position 3**: `#{(x₁, x₂, x₃) ∈ S₁ × S₂ × L₃ : res sum = 0} ≤
|S₁||S₂|(σ − 1)`. -/
theorem light_triples_le (res : α → Q) (S₁ S₂ S₃ : Finset α) (σ : ℕ) :
    ((S₁ ×ˢ S₂ ×ˢ light res S₃ σ).filter fun t => res t.1 + res t.2.1 + res t.2.2 = 0).card ≤
      S₁.card * S₂.card * (σ - 1) := by
  refine triples_le_of_classes_lt res S₁ S₂ _ σ fun x hx => ?_
  refine lt_of_le_of_lt (Finset.card_le_card ?_) (Finset.mem_filter.1 hx).2
  exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)

/-- Light list in position 1. -/
theorem light_triples_le₁ (res : α → Q) (S₁ S₂ S₃ : Finset α) (σ : ℕ) :
    ((light res S₁ σ ×ˢ S₂ ×ˢ S₃).filter fun t => res t.1 + res t.2.1 + res t.2.2 = 0).card ≤
      S₂.card * S₃.card * (σ - 1) := by
  refine le_trans ?_ (light_triples_le res S₂ S₃ S₁ σ)
  refine Finset.card_le_card_of_injOn (fun t => (t.2.1, t.2.2, t.1)) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product]
    refine ⟨⟨ht.1.2.1, ht.1.2.2, ht.1.1⟩, ?_⟩
    rw [← ht.2]; abel
  · intro t _ t' _ e
    simp only [Prod.mk.injEq] at e
    exact Prod.ext e.2.2 (Prod.ext e.1 e.2.1)

/-- Light list in position 2. -/
theorem light_triples_le₂ (res : α → Q) (S₁ S₂ S₃ : Finset α) (σ : ℕ) :
    ((S₁ ×ˢ light res S₂ σ ×ˢ S₃).filter fun t => res t.1 + res t.2.1 + res t.2.2 = 0).card ≤
      S₁.card * S₃.card * (σ - 1) := by
  refine le_trans ?_ (light_triples_le res S₁ S₃ S₂ σ)
  refine Finset.card_le_card_of_injOn (fun t => (t.1, t.2.2, t.2.1)) ?_ ?_
  · intro t ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at ht
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product]
    refine ⟨⟨ht.1.1, ht.1.2.2, ht.1.2.1⟩, ?_⟩
    rw [← ht.2]; abel
  · intro t _ t' _ e
    simp only [Prod.mk.injEq] at e
    exact Prod.ext e.1 (Prod.ext e.2.2 e.2.1)

/-- **Part H, `T_I ≤ 2 s |S₁||S₂|`**: if every class of `S₃` has fewer than `2s` elements. -/
theorem TI_classes_lt (res : α → Q) (S₁ S₂ S₃ : Finset α) (s : ℕ)
    (h : ∀ x ∈ S₃, (S₃.filter fun y => res y = res x).card < 2 * s) :
    ((S₁ ×ˢ S₂ ×ˢ S₃).filter fun t => res t.1 + res t.2.1 + res t.2.2 = 0).card ≤
      2 * s * S₁.card * S₂.card := by
  refine (triples_le_of_classes_lt res S₁ S₂ S₃ (2 * s) h).trans ?_
  calc S₁.card * S₂.card * (2 * s - 1) ≤ S₁.card * S₂.card * (2 * s) :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = 2 * s * S₁.card * S₂.card := by ring

end heavyLight

/-- **Step 1 for the residue**: with `L₃` the light part of `S₃` (classes mod `pG` of fewer than
`σ` elements), `T_I = #{t ∈ S₁ × S₂ × L₃ : (x₁ + x₂ + x₃)‾ = 0} ≤ |S₁||S₂|(σ − 1)`. -/
theorem TI_light_le (S₁ S₂ S₃ : Finset (Fin d → ZMod (p ^ 2))) (σ : ℕ) :
    ((S₁ ×ˢ S₂ ×ˢ light residue S₃ σ).filter fun t =>
      residue (t.1 + t.2.1 + t.2.2) = 0).card ≤ S₁.card * S₂.card * (σ - 1) := by
  have := light_triples_le (residue (p := p) (d := d)) S₁ S₂ S₃ σ
  simpa only [residue_add] using this

/-! ### Lemma G1 in abstract form -/

section G1
variable {ι κ : Type*}

/-- **Lemma G1 (one step, averaged)**: items `j ∈ J` with old-survival `old j`, new survival
`new j c` for each candidate `c ∈ C`, new weights `w′_j ≥ 0`; if for every item the fraction of
candidates under which it survives is at most `ρ_j [old_j]`, and `w′_j ρ_j ≤ θ w_j` for the old
survivors, then the average over the candidates of the new potential is at most `θ` times the
old one. (In the text `θ = (1+ε₀)²`.) -/
theorem G1_avg (J : Finset ι) (C : Finset κ) (old : ι → Prop) [DecidablePred old]
    (new : ι → κ → Prop) [∀ j c, Decidable (new j c)] (w w' ρ : ι → ℝ) (θ : ℝ)
    (hw' : ∀ j ∈ J, 0 ≤ w' j)
    (hρ : ∀ j ∈ J, (∑ c ∈ C, if new j c then (1 : ℝ) else 0) / C.card ≤
      ρ j * (if old j then 1 else 0))
    (hθ : ∀ j ∈ J, old j → w' j * ρ j ≤ θ * w j) :
    (∑ c ∈ C, ∑ j ∈ J, if new j c then w' j else 0) / C.card ≤
      θ * ∑ j ∈ J, if old j then w j else 0 := by
  rw [Finset.sum_comm, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have e : (∑ c ∈ C, if new j c then w' j else 0) / C.card =
      w' j * ((∑ c ∈ C, if new j c then (1 : ℝ) else 0) / C.card) := by
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs <;> simp
  rw [e]
  calc w' j * ((∑ c ∈ C, if new j c then (1 : ℝ) else 0) / C.card)
      ≤ w' j * (ρ j * (if old j then 1 else 0)) := mul_le_mul_of_nonneg_left (hρ j hj) (hw' j hj)
    _ ≤ θ * (if old j then w j else 0) := by
        by_cases ho : old j
        · simp only [ho, if_true, mul_one]; exact hθ j hj ho
        · simp [ho]

/-- Some candidate achieves at most the average. -/
theorem exists_le_avg (C : Finset κ) (hC : C.Nonempty) (f : κ → ℝ) :
    ∃ c ∈ C, f c ≤ (∑ c ∈ C, f c) / C.card := by
  apply Finset.exists_le_of_sum_le hC
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : (C.card : ℝ) ≠ 0 := by
    have := hC.card_pos
    positivity
  rw [mul_div_cancel₀ _ hc]

/-- **Lemma G1, the greedy step**: a candidate minimizing the new potential gives
`Ψ_{t+1} ≤ θ Ψ_t`. -/
theorem G1_step (J : Finset ι) (C : Finset κ) (hC : C.Nonempty) (old : ι → Prop)
    [DecidablePred old] (new : ι → κ → Prop) [∀ j c, Decidable (new j c)] (w w' ρ : ι → ℝ)
    (θ : ℝ) (hw' : ∀ j ∈ J, 0 ≤ w' j)
    (hρ : ∀ j ∈ J, (∑ c ∈ C, if new j c then (1 : ℝ) else 0) / C.card ≤
      ρ j * (if old j then 1 else 0))
    (hθ : ∀ j ∈ J, old j → w' j * ρ j ≤ θ * w j) (Ψ Ψ' : ℝ)
    (hΨ : Ψ = ∑ j ∈ J, if old j then w j else 0)
    (hmin : ∀ c ∈ C, Ψ' ≤ ∑ j ∈ J, if new j c then w' j else 0) :
    Ψ' ≤ θ * Ψ := by
  obtain ⟨c, hc, hle⟩ := exists_le_avg C hC (fun c => ∑ j ∈ J, if new j c then w' j else 0)
  rw [hΨ]
  exact (hmin c hc).trans (hle.trans (G1_avg J C old new w w' ρ θ hw' hρ hθ))

/-- **Iteration**: `Ψ_{t+1} ≤ θ Ψ_t` for `t < q` gives `Ψ_q ≤ θ^q Ψ_0`. -/
theorem G1_iterate (Ψ : ℕ → ℝ) (θ : ℝ) (hθ : 0 ≤ θ) (q : ℕ)
    (h : ∀ t < q, Ψ (t + 1) ≤ θ * Ψ t) : Ψ q ≤ θ ^ q * Ψ 0 := by
  induction q with
  | zero => simp
  | succ n ih =>
    calc Ψ (n + 1) ≤ θ * Ψ n := h n (Nat.lt_succ_self n)
      _ ≤ θ * (θ ^ n * Ψ 0) :=
          mul_le_mul_of_nonneg_left (ih fun t ht => h t (Nat.lt_succ_of_lt ht)) hθ
      _ = θ ^ (n + 1) * Ψ 0 := by ring

/-- `((1+ε)²)^q = (1+ε)^{2q} ≤ e` when `0 ≤ ε` and `2qε ≤ 1`. -/
theorem one_add_sq_pow_le_exp (ε : ℝ) (q : ℕ) (hε0 : 0 ≤ ε) (hε : 2 * q * ε ≤ 1) :
    ((1 + ε) ^ 2) ^ q ≤ Real.exp 1 := by
  calc ((1 + ε) ^ 2) ^ q = (1 + ε) ^ (2 * q) := by rw [← pow_mul]
    _ ≤ (Real.exp ε) ^ (2 * q) :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp ε]) _
    _ = Real.exp ((2 * q : ℕ) * ε) := (Real.exp_nat_mul ε (2 * q)).symm
    _ ≤ Real.exp 1 := Real.exp_le_exp.2 (by push_cast; linarith)

/-- **Lemma G1 iterated**: `Ψ_q ≤ (1+ε)^{2q} Ψ_0 ≤ e Ψ_0` (`Ψ_0 ≥ 0`, `2qε ≤ 1`). -/
theorem G1_iterate_exp (Ψ : ℕ → ℝ) (ε : ℝ) (q : ℕ) (hε0 : 0 ≤ ε) (hε : 2 * q * ε ≤ 1)
    (hΨ0 : 0 ≤ Ψ 0) (h : ∀ t < q, Ψ (t + 1) ≤ (1 + ε) ^ 2 * Ψ t) :
    Ψ q ≤ Real.exp 1 * Ψ 0 :=
  (G1_iterate Ψ _ (by positivity) q h).trans
    (mul_le_mul_of_nonneg_right (one_add_sq_pow_le_exp ε q hε0 hε) hΨ0)

end G1

/-! ### The final arithmetic of Part L -/

/-- **Part L, "Final values"**: from `p^q = D`, `Ψ_q ≤ e Ψ₀`, `Ψ₀ ≤ D(3eσn² + T_I)`,
`T_I ≤ σn²` and `Ψ_q = p^q Y + D p^q Ŝ + p^{2q} Â` with `Y, Ŝ, Â ≥ 0`:
`Y ≤ e(3e+1)σn²`, `Ŝ ≤ e(3e+1)σn²/D`, `Â + Ŝ ≤ 2e(3e+1)σn²/D`, and
`Z(π) = T_I + Y ≤ (1 + 3e² + e)σn²`. -/
theorem partL_final (p q : ℕ) (D σ n Ψ₀ Ψq TI Y S A : ℝ) (hD : 0 < D) (hpq : (p : ℝ) ^ q = D)
    (hq : Ψq ≤ Real.exp 1 * Ψ₀) (h0 : Ψ₀ ≤ D * (3 * Real.exp 1 * σ * n ^ 2 + TI))
    (hTI : TI ≤ σ * n ^ 2)
    (hΨ : Ψq = (p : ℝ) ^ q * Y + D * (p : ℝ) ^ q * S + (p : ℝ) ^ (2 * q) * A)
    (hY : 0 ≤ Y) (hS : 0 ≤ S) (hA : 0 ≤ A) :
    Y ≤ Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2 ∧
    S ≤ Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2 / D ∧
    A + S ≤ 2 * Real.exp 1 * (3 * Real.exp 1 + 1) * σ * n ^ 2 / D ∧
    TI + Y ≤ (1 + 3 * Real.exp 1 ^ 2 + Real.exp 1) * σ * n ^ 2 := by
  set e := Real.exp 1 with he_def
  have he : 0 < e := Real.exp_pos 1
  have hΨ' : Ψq = D * Y + D * D * S + D ^ 2 * A := by
    rw [hΨ, pow_mul', hpq]
  set B := (3 * e + 1) * σ * n ^ 2 with hB_def
  have h0' : Ψ₀ ≤ D * B := by
    refine h0.trans (mul_le_mul_of_nonneg_left ?_ hD.le)
    rw [hB_def]; linarith
  have hB : D * Y + D * D * S + D ^ 2 * A ≤ D * (e * B) := by
    rw [← hΨ']
    calc Ψq ≤ e * Ψ₀ := hq
      _ ≤ e * (D * B) := mul_le_mul_of_nonneg_left h0' he.le
      _ = D * (e * B) := by ring
  have t0 : 0 ≤ D * Y := by positivity
  have t1 : 0 ≤ D * D * S := by positivity
  have t2 : 0 ≤ D ^ 2 * A := by positivity
  have hYB : Y ≤ e * B := le_of_mul_le_mul_left (by linarith) hD
  have hSB : S * D ≤ e * B := le_of_mul_le_mul_left (by nlinarith) hD
  have hASB : (A + S) * D ≤ 2 * (e * B) := le_of_mul_le_mul_left (by nlinarith) hD
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Y ≤ e * B := hYB
      _ = e * (3 * e + 1) * σ * n ^ 2 := by rw [hB_def]; ring
  · rw [le_div_iff₀ hD]
    calc S * D ≤ e * B := hSB
      _ = e * (3 * e + 1) * σ * n ^ 2 := by rw [hB_def]; ring
  · rw [le_div_iff₀ hD]
    calc (A + S) * D ≤ 2 * (e * B) := hASB
      _ = 2 * e * (3 * e + 1) * σ * n ^ 2 := by rw [hB_def]; ring
  · have : e * B = (3 * e ^ 2 + e) * σ * n ^ 2 := by rw [hB_def]; ring
    nlinarith

end ExpP2
end GroupLean

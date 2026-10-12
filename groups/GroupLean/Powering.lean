import GroupLean.Select

/-!
# The powering construction (Lemma 19.4 of the paper, in the value-bias form of Section 19.6)

For a finite field `K ⊇ F_p` with `|K| = q = p^m`, the multiset of rows
`(Tr(β α^j))_{j<d}`, `(α, β) ∈ K × K`, is `(p(d−1)/q)`-value-biased (`powSet_isValBiased`), and for
every `d, r ≥ 1` there is a `(1/r)`-value-biased multiset of at most `p⁴d²r²` rows
(`exists_valBiased`).
-/

namespace GroupLean

open Polynomial

section Powering

variable (p : ℕ) [Fact p.Prime] (d : ℕ) (K : Type*) [Field K] [Fintype K] [Algebra (ZMod p) K]

/-- The row `(Tr(β α^j))_{j<d}`. -/
noncomputable def powRow (α β : K) : VecP p d :=
  fun j => Algebra.trace (ZMod p) K (β * α ^ (j : ℕ))

/-- The multiset `E_{d,m}` of all `powRow α β`, `(α, β) ∈ K × K`. -/
noncomputable def powSet : Multiset (VecP p d) :=
  (Finset.univ : Finset (K × K)).val.map fun ab => powRow p d K ab.1 ab.2

variable {p d K}

/-- `f_v = Σ_j v_j X^j`, mapped to `K[X]`. -/
noncomputable def fPoly (v : VecP p d) : K[X] :=
  ∑ j : Fin d, C (algebraMap (ZMod p) K (v j)) * X ^ (j : ℕ)

omit [Fintype K] in
lemma powRow_dot (α β : K) (v : VecP p d) :
    powRow p d K α β ⬝ᵥ v = Algebra.trace (ZMod p) K (β * (fPoly v).eval α) := by
  simp only [dotProduct, powRow, fPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X,
    Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [show β * (algebraMap (ZMod p) K (v j) * α ^ (j : ℕ)) = v j • (β * α ^ (j : ℕ)) by
    rw [Algebra.smul_def]; ring, LinearMap.map_smul, smul_eq_mul, mul_comm]

omit [Fintype K] in
lemma fPoly_coeff (v : VecP p d) (i : Fin d) :
    (fPoly (K := K) v).coeff i = algebraMap (ZMod p) K (v i) := by
  simp only [fPoly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : (i : ℕ) ≠ j := fun h => hj (Fin.ext h).symm
    simp [this]
  · simp

omit [Fintype K] in
lemma fPoly_ne_zero {v : VecP p d} (hv : v ≠ 0) : fPoly (K := K) v ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  intro h0
  have := fPoly_coeff (K := K) v i
  rw [h0, coeff_zero] at this
  exact hi ((algebraMap (ZMod p) K).injective (by rw [← this, map_zero]))

omit [Fintype K] in
lemma fPoly_natDegree_le (v : VecP p d) : (fPoly (K := K) v).natDegree ≤ d - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro j _
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

lemma card_zeros_le [DecidableEq K] (g : K[X]) (hg : g ≠ 0) :
    (Finset.univ.filter fun α => g.eval α = 0).card ≤ g.natDegree := by
  calc _ ≤ g.roots.toFinset.card := by
        apply Finset.card_le_card
        intro α hα
        simp only [Finset.mem_filter] at hα
        simp [Multiset.mem_toFinset, mem_roots hg, hα.2]
    _ ≤ g.roots.card := Multiset.toFinset_card_le _
    _ ≤ g.natDegree := card_roots' g

/-- For `c ≠ 0`, `β ↦ Tr(β c)` takes every value `s` exactly `|K|/p` times. -/
lemma card_trace_fiber [DecidableEq K] {c : K} (hc : c ≠ 0) (s : ZMod p) :
    (Finset.univ.filter fun β : K => Algebra.trace (ZMod p) K (β * c) = s).card * p
      = Fintype.card K := by
  let f : K →+ ZMod p :=
    (Algebra.trace (ZMod p) K).toAddMonoidHom.comp (AddMonoidHom.mulRight c)
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨x, hx⟩ := Algebra.trace_surjective (ZMod p) K t
    refine ⟨x / c, ?_⟩
    change Algebra.trace (ZMod p) K (x / c * c) = t
    rw [div_mul_cancel₀ x hc, hx]
  exact card_fiber_mul_eq f hf s

variable (p d K) in
/-- Lemma 3, value-bias form: `E_{d,m}` is `(p(d−1)/q)`-value-biased, `q = p^m = |K|`. -/
theorem powSet_isValBiased (m : ℕ) (hd : 1 ≤ d) (hK : Fintype.card K = p ^ m) :
    IsValBiased ((p : ℝ) * ((d : ℝ) - 1) / (p : ℝ) ^ m) (powSet p d K) := by
  classical
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨?_, ?_⟩
  · simpa [powSet] using (Finset.univ_nonempty (α := K × K)).ne_empty
  · intro v hv s
    set g : K[X] := fPoly v with hg
    set q : ℕ := Fintype.card K with hq
    have hcard : (powSet p d K).card = q * q := by
      simp [powSet, q]
    have hfil : ((powSet p d K).filter fun u => u ⬝ᵥ v = s).card
        = ∑ α : K, (Finset.univ.filter fun β : K =>
            Algebra.trace (ZMod p) K (β * g.eval α) = s).card := by
      rw [powSet, Multiset.filter_map, Multiset.card_map]
      change (Finset.univ.filter _).card = _
      rw [Finset.card_filter, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro α _
      rw [Finset.card_filter]
      apply Finset.sum_congr rfl
      intro β _
      simp only [Function.comp, powRow_dot, hg]
    have key : ∀ α : K, ((Finset.univ.filter fun β : K =>
        Algebra.trace (ZMod p) K (β * g.eval α) = s).card : ℝ)
          ≤ (q : ℝ) / p + if g.eval α = 0 then (q : ℝ) else 0 := by
      intro α
      by_cases h0 : g.eval α = 0
      · rw [if_pos h0]
        have : ((Finset.univ.filter fun β : K =>
            Algebra.trace (ZMod p) K (β * g.eval α) = s).card : ℝ) ≤ q := by
          exact_mod_cast (Finset.card_filter_le _ _).trans (by simp [q])
        have : (0 : ℝ) ≤ q / p := by positivity
        linarith
      · rw [if_neg h0, add_zero, le_div_iff₀ hp]
        exact_mod_cast (card_trace_fiber h0 s).le
    have hroots : ((Finset.univ.filter fun α : K => g.eval α = 0).card : ℝ) ≤ (d : ℝ) - 1 := by
      have h1 := (card_zeros_le g (fPoly_ne_zero hv)).trans (fPoly_natDegree_le (K := K) v)
      have h2 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
      rw [← h2]; exact_mod_cast h1
    rw [hfil, hcard, Nat.cast_sum]
    calc ∑ α : K, ((Finset.univ.filter fun β : K =>
            Algebra.trace (ZMod p) K (β * g.eval α) = s).card : ℝ)
        ≤ ∑ α : K, ((q : ℝ) / p + if g.eval α = 0 then (q : ℝ) else 0) :=
          Finset.sum_le_sum fun α _ => key α
      _ = q * ((q : ℝ) / p) + (Finset.univ.filter fun α : K => g.eval α = 0).card * q := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite, Finset.sum_const,
            Finset.sum_const_zero, add_zero, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ]
      _ ≤ q * ((q : ℝ) / p) + ((d : ℝ) - 1) * q := by
          have : (0 : ℝ) ≤ q := Nat.cast_nonneg _
          nlinarith
      _ = (1 + (p : ℝ) * ((d : ℝ) - 1) / (p : ℝ) ^ m) / p * ((q * q : ℕ) : ℝ) := by
          have hqm : (q : ℝ) = (p : ℝ) ^ m := by exact_mod_cast hK
          push_cast
          rw [hqm]
          field_simp

end Powering

/-- For every prime `p` and `d, r ≥ 1` there is a `(1/r)`-value-biased multiset of rows of
`F_p^d` with at most `p⁴d²r²` elements. -/
theorem exists_valBiased (p : ℕ) [Fact p.Prime] (d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) :
    ∃ E : Multiset (VecP p d), IsValBiased (1 / (r : ℝ)) E ∧ E.card ≤ p ^ 4 * d ^ 2 * r ^ 2 := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  set N := p * d * r with hN
  have hN2 : 2 ≤ N := by
    calc 2 ≤ p := hp2
      _ = p * 1 * 1 := by ring
      _ ≤ N := Nat.mul_le_mul (Nat.mul_le_mul le_rfl hd) hr
  have hex : ∃ m, N ≤ p ^ m := ⟨N, (Nat.lt_pow_self (by omega)).le⟩
  classical
  set m := Nat.find hex with hm
  have hNm : N ≤ p ^ m := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hNm
    omega
  have hlt : p ^ (m - 1) < N := by
    have := Nat.find_min hex (show m - 1 < m by omega)
    omega
  have hpm : p ^ m < p * N := by
    calc p ^ m = p * p ^ (m - 1) := by
          rw [← pow_succ']; congr 1; omega
      _ < p * N := Nat.mul_lt_mul_of_pos_left hlt (by omega)
  let K := GaloisField p m
  let _ : Fintype K := Fintype.ofFinite K
  have hK : Fintype.card K = p ^ m := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p m hm0
  refine ⟨powSet p d K, (powSet_isValBiased p d K m hd hK).mono ?_, ?_⟩
  · -- `p(d−1)/p^m ≤ 1/r` because `p(d−1)r ≤ N ≤ p^m`
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
    have hpm0 : (0 : ℝ) < (p : ℝ) ^ m := by positivity
    rw [div_le_div_iff₀ hpm0 hr0, one_mul]
    have h1 : ((p * d * r : ℕ) : ℝ) ≤ ((p ^ m : ℕ) : ℝ) := by exact_mod_cast hNm
    push_cast at h1
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    nlinarith
  · have hc : (powSet p d K).card = p ^ m * p ^ m := by
      simp [powSet, hK]
    rw [hc]
    have h1 : p ^ m ≤ p * p * d * r := by
      have := hpm.le; rw [hN] at this; linarith [this]
    calc p ^ m * p ^ m ≤ (p * p * d * r) * (p * p * d * r) := Nat.mul_le_mul h1 h1
      _ = p ^ 4 * d ^ 2 * r ^ 2 := by ring

end GroupLean

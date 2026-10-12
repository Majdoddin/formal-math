import ThinMatrixProducts.PartI.Boxes
import ThinMatrixProducts.PartI.Bijection

/-!
# [ZT, Lemma 7] on the `2L` levels, and the query of Theorem 7.2

Lemma 7 is ported from `3sum-apsp` (`ThreeSumApsp/Sec2/Lemma7_8.lean`, Apache 2.0, Anthropic PBC):
there it is proved for Schönhage's identity at every level; here the recursion runs over one half
with that half's forms (`FullHalf`), so the proof is the same induction with the alphabet and the
forms of the half. `encF f τ a` is upstream's `encodeWith` with the levels below the half carried
along.

The query (Theorem 7.2) is the composition: the decomposition of `I` and `J` into band, block and
label (the tiling), the output string found by inverting `Δ` (change (5)), Lemma 7.1(a) (the entry
is the low-order leaf products plus the box values), the flattening of the leaves, the leaf-sum
link, Lemma 7 (the encodings are `Φ_τ`, `Ψ_τ`), Theorem 5.1 and the definition of the blocks.
-/

namespace ThinMatrixProducts

open Finset

/-! ## Lemma 7 on one half -/

section Half

variable {α A : Type} [Fintype α]

/-- `∑_u a[u, x] ∏_ℓ f_{τ_ℓ}(u_ℓ)`: the number at the leaf `τ` of the half, as an array on the
levels below (upstream's `encodeWith`). -/
def encF (f : Tm → α → ℤ) {n : ℕ} (τ : Fin n → Tm) (a : (Fin n → α) × A → ℤ) : A → ℤ :=
  fun x => ∑ u, a (u, x) * ∏ ℓ, f (τ ℓ) (u ℓ)

/-- A sum over the strings of length `n + 1` splits by the first letter (upstream). -/
lemma sum_strings_succ' {γ : Type} [Fintype γ] {n : ℕ} (F : (Fin (n + 1) → γ) → ℤ) :
    ∑ u, F u = ∑ s, ∑ u', F (Fin.cons s u') := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv fun _ => γ) _ _ fun _ => rfl).symm

lemma encF_zero (f : Tm → α → ℤ) (τ : Fin 0 → Tm) (a : (Fin 0 → α) × A → ℤ) :
    encF f τ a = fun x => a (Fin.elim0, x) := by
  funext x
  simp [encF, Subsingleton.elim (default : Fin 0 → α) Fin.elim0]

/-- "`Φ_{λτ'}(a) = Φ_{τ'}(A_λ)`" (proof of [ZT, Lemma 7]). -/
lemma encF_cons (f : Tm → α → ℤ) {n : ℕ} (lam : Tm) (τ' : Fin n → Tm)
    (a : (Fin (n + 1) → α) × A → ℤ) :
    encF f (Fin.cons lam τ' : Fin (n + 1) → Tm) a = encF f τ' (encStep f lam a) := by
  funext x
  simp only [encF, encStep, sum_strings_succ', Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun u' _ => sum_congr rfl fun s _ => by ring

/-- The encoding recursion computes `encF`. -/
lemma encHalf_eq (f : Tm → α → ℤ) :
    ∀ (n : ℕ) (a : (Fin n → α) × A → ℤ) (τ : Fin n → Tm), encHalf f n a τ = encF f τ a := by
  intro n
  induction n with
  | zero => intro a τ; rw [encF_zero]; rfl
  | succ n ih =>
    intro a τ
    show encHalf f n (encStep f (τ 0) a) (Fin.tail τ) = _
    rw [ih, ← encF_cons, Fin.cons_self_tail]

end Half

/-- Every term contributes to `z₀`. -/
lemma chi_z0 (lam : Tm) : chi lam .z0 = 1 := by cases lam <;> rfl

/-- Step (4) of `Full`, as read in the proof of [ZT, Lemma 7]:
`c[z w'] = ∑_{λ contributing to z} C_λ[w']`. -/
lemma decodeStep_eq {X : Type} (C : Tm → X → ℤ) (z : ZL) (x : X) :
    decodeStep C z x = ∑ lam : Tm with chi lam z ≠ 0, C lam x := by
  cases z with
  | z i j =>
    rw [sum_filter, Fintype.sum_eq_single (Tm.P i j)]
    · simp [decodeStep, chi]
    · intro lam hlam
      cases lam with
      | P i' j' =>
        have : ¬ (i = i' ∧ j = j') := fun h => hlam (by rw [h.1, h.2])
        simp [chi, this]
      | P0 => simp [chi]
  | z0 => simp [decodeStep, chi_z0]

/-- The leaves contributing to `z w'` are the `λτ'` with `λ` contributing to `z` and `τ'` to `w'`
(upstream's `Leaf.sum_contributes_succ`). -/
lemma sum_contrib_succ {n : ℕ} (w : Fin (n + 1) → ZL) (F : (Fin (n + 1) → Tm) → ℤ) :
    ∑ τ : Fin (n + 1) → Tm with ∀ ℓ, chi (τ ℓ) (w ℓ) ≠ 0, F τ
      = ∑ lam : Tm with chi lam (w 0) ≠ 0,
          ∑ τ' : Fin n → Tm with ∀ ℓ, chi (τ' ℓ) (Fin.tail w ℓ) ≠ 0, F (Fin.cons lam τ') := by
  rw [sum_filter, sum_strings_succ'
    (fun τ : Fin (n + 1) → Tm => if ∀ ℓ, chi (τ ℓ) (w ℓ) ≠ 0 then F τ else (0 : ℤ)), sum_filter]
  refine sum_congr rfl fun lam _ => ?_
  rw [sum_filter]
  by_cases h : chi lam (w 0) ≠ 0
  · rw [if_pos h]
    refine sum_congr rfl fun τ' _ => ?_
    have hiff : (∀ ℓ, chi ((Fin.cons lam τ' : Fin (n + 1) → Tm) ℓ) (w ℓ) ≠ 0)
        ↔ ∀ ℓ, chi (τ' ℓ) (Fin.tail w ℓ) ≠ 0 := by
      rw [Fin.forall_fin_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
      exact ⟨fun hh => hh.2, fun hh => ⟨h, hh⟩⟩
    by_cases h' : ∀ ℓ, chi (τ' ℓ) (Fin.tail w ℓ) ≠ 0
    · rw [if_pos (hiff.2 h'), if_pos h']
    · rw [if_neg (fun hh => h' (hiff.1 hh)), if_neg h']
  · rw [if_neg h]
    refine sum_eq_zero fun τ' _ => ?_
    have : ¬ ∀ ℓ, chi ((Fin.cons lam τ' : Fin (n + 1) → Tm) ℓ) (w ℓ) ≠ 0 :=
      fun hh => h (by simpa using hh 0)
    rw [if_neg this]

section FullHalfLemmas

variable {α β A B O Lf : Type} [Fintype α] [Fintype β] (f : Tm → α → ℤ) (g : Tm → β → ℤ)
  (base : (A → ℤ) → (B → ℤ) → (O → ℤ) × (Lf → ℤ × ℤ))

/-- [ZT, Lemma 7], first half, on one half: at the leaf `τ`, `Full` hands the continuation the
encodings at `τ`. -/
lemma FullHalf_snd : ∀ (n : ℕ) (a : (Fin n → α) × A → ℤ) (b : (Fin n → β) × B → ℤ)
    (τ : Fin n → Tm) (lf : Lf),
    (FullHalf f g base n a b).2 (τ, lf) = (base (encF f τ a) (encF g τ b)).2 lf := by
  intro n
  induction n with
  | zero => intro a b τ lf; rw [encF_zero, encF_zero]; rfl
  | succ n ih =>
    intro a b τ lf
    show (FullHalf f g base n (encStep f (τ 0) a) (encStep g (τ 0) b)).2 (Fin.tail τ, lf) = _
    rw [ih, ← encF_cons, ← encF_cons, Fin.cons_self_tail]

/-- [ZT, Lemma 7], second half, on one half: `Full` returns the sum over the contributing leaves of
the half. -/
lemma FullHalf_fst : ∀ (n : ℕ) (a : (Fin n → α) × A → ℤ) (b : (Fin n → β) × B → ℤ)
    (w : Fin n → ZL) (o : O),
    (FullHalf f g base n a b).1 (w, o)
      = ∑ τ : Fin n → Tm with ∀ ℓ, chi (τ ℓ) (w ℓ) ≠ 0, (base (encF f τ a) (encF g τ b)).1 o := by
  intro n
  induction n with
  | zero =>
    intro a b w o
    rw [sum_filter, Fintype.sum_unique]
    simp only [IsEmpty.forall_iff, if_true]
    rw [encF_zero, encF_zero]
    try rfl
  | succ n ih =>
    intro a b w o
    show decodeStep (fun lam x => (FullHalf f g base n (encStep f lam a) (encStep g lam b)).1 x)
      (w 0) (Fin.tail w, o) = _
    rw [decodeStep_eq, sum_contrib_succ]
    refine sum_congr rfl fun lam _ => ?_
    rw [ih]
    simp only [encF_cons]

end FullHalfLemmas

/-- The nested encoding of the two halves is the sum over the strings of both halves. -/
lemma encF_nested {α β : Type} [Fintype α] [Fintype β] (f : Tm → α → ℤ) (g : Tm → β → ℤ)
    {n n' : ℕ} (τ1 : Fin n → Tm) (τ2 : Fin n' → Tm) (a : (Fin n → α) × (Fin n' → β) → ℤ) :
    encF g τ2 (fun p : (Fin n' → β) × Unit => encF f τ1 a p.1) ()
      = ∑ u, a u * (∏ ℓ, f (τ1 ℓ) (u.1 ℓ)) * ∏ ℓ, g (τ2 ℓ) (u.2 ℓ) := by
  simp only [encF, sum_mul]
  rw [Fintype.sum_prod_type, sum_comm]
  all_goals exact sum_congr rfl fun u1 _ => sum_congr rfl fun u2 _ => by ring

theorem lemma_7_squared : Lemma_7_squared := by
  intro L a b
  have hL : ∀ τ : Leaf L,
      encF psi τ.2 (fun p : YStr L × Unit => encF phi τ.1 a p.1) () = PhiL τ a := fun τ =>
    encF_nested phi psi τ.1 τ.2 a
  have hR : ∀ τ : Leaf L,
      encF phi τ.2 (fun p : XStr L × Unit => encF psi τ.1 b p.1) () = PsiR τ b := fun τ =>
    encF_nested psi phi τ.1 τ.2 b
  refine ⟨fun τ => ?_, ?_, fun τ => ⟨?_, ?_⟩⟩
  · rw [show τ = (τ.1, τ.2) from rfl, FullSq.run, FullHalf_snd]
    simp only
    rw [FullHalf_snd]
    exact Prod.ext (hL τ) (hR τ)
  · funext w
    rw [show w = (w.1, w.2) from rfl, FullSq.run, FullHalf_fst]
    simp only [Mult]
    rw [sum_filter, sum_filter, Fintype.sum_prod_type]
    refine sum_congr rfl fun τ1 _ => ?_
    by_cases h1 : ∀ ℓ, chi (τ1 ℓ) (w.1 ℓ) ≠ 0
    · rw [if_pos h1, FullHalf_fst, sum_filter]
      refine sum_congr rfl fun τ2 _ => ?_
      by_cases h2 : ∀ ℓ, chi (τ2 ℓ) (w.2 ℓ) ≠ 0
      · have hc : Contributes (τ1, τ2) (w.1, w.2) := fun ℓ => ⟨h1 ℓ, h2 ℓ⟩
        rw [if_pos h2, if_pos hc]
        exact congrArg₂ (· * ·) (hL (τ1, τ2)) (hR (τ1, τ2))
      · have hc : ¬ Contributes (τ1, τ2) (w.1, w.2) := fun h => h2 fun ℓ => (h ℓ).2
        rw [if_neg h2, if_neg hc]
    · rw [if_neg h1]
      symm
      refine sum_eq_zero fun τ2 _ => ?_
      have hc : ¬ Contributes (τ1, τ2) (w.1, w.2) := fun h => h1 fun ℓ => (h ℓ).1
      rw [if_neg hc]
  · rw [encodeL, encHalf_eq]
    simp only [encHalf_eq]
    exact hL τ
  · rw [encodeR, encHalf_eq]
    simp only [encHalf_eq]
    exact hR τ

/-! ## The query of Theorem 7.2 -/

lemma unflat_flat {L : ℕ} (τ : Leaf L) : Sq.unflatLeaf (Sq.flatLeaf τ) = τ := by
  unfold Sq.unflatLeaf Sq.flatLeaf
  exact Prod.ext (funext fun ℓ => Fin.append_left τ.1 τ.2 ℓ)
    (funext fun ℓ => Fin.append_right τ.1 τ.2 ℓ)

/-- Change (5): for a good set the inverse of `Δ` at `[L] ∖ Q` exists. -/
lemma DeltaInv_spec {L m : ℕ} {Γ : Matrix (Fin m) (Fin L) (ZMod 2)}
    {Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2)} {Q : Finset (Fin L)} (hQ : Good Γ Δ Q)
    (δ : Fin (L - m) → ZMod 2) :
    DeltaInv Δ Q δ ⊆ Qᶜ ∧ colSum Δ (DeltaInv Δ Q δ) = δ := by
  have hcard : (Qᶜ).card = L - m := by rw [card_compl, Fintype.card_fin, hQ.1]
  have hex : ∃ S ⊆ Qᶜ, colSum Δ S = δ := by
    obtain ⟨S, hS, hSδ⟩ := (colSum_bijOn Δ Qᶜ hcard hQ.2.2).surjOn (Set.mem_univ δ)
    exact ⟨S, Finset.mem_powerset.1 (Finset.mem_coe.1 hS), hSδ⟩
  classical
  unfold DeltaInv
  rw [dif_pos hex]
  exact hex.choose_spec

lemma zString_eq_mkZ {L : ℕ} (Q S : Finset (Fin L)) (ι : Fin L → Fin 2) :
    zString Q S ι = mkZ Q S ι := rfl

/-- An entry read through a label: a row index that equals `I` reads row `I`. -/
lemma dite_eq_of_eq {N : ℕ} (n : ℕ) (I : Fin N) (h : n = I) (F : Fin N → ℤ) :
    (if hn : n < N then F ⟨n, hn⟩ else 0) = F I := by
  subst h; simp

/-- The tiling: `I` is row `I mod N₀` of block `(I / N₀) mod K_g` of band `I / (K_g N₀)`. -/
lemma tile_decomp (I Kg n0 : ℕ) :
    (I / (Kg * n0) * Kg + (I / n0) % Kg) * n0 + I % n0 = I := by
  rw [mul_comm Kg n0, ← Nat.div_div_eq_div_mul, Nat.div_add_mod', Nat.div_add_mod']

lemma tileX_apply {N L m Kg : ℕ} (X : Matrix (Fin N) (Fin (4 ^ m)) ℤ)
    (eD : Fin (4 ^ m) ≃ InIdx m) (𝒬 : Fin Kg → Finset (Fin L)) (hinj : Function.Injective 𝒬)
    (eRow : ∀ k, Fin (N0 L m) ≃ BRow L m (𝒬 k)) (b : ℕ) (k : Fin Kg) (i : Fin (N0 L m))
    (x : InIdx m) :
    tileX X eD 𝒬 eRow b (𝒬 k) (eRow k i).1 x
      = if hn : (b * Kg + k) * N0 L m + i < N then X ⟨_, hn⟩ (eD.symm x) else 0 := by
  classical
  have h : ∃ k₀, 𝒬 k₀ = 𝒬 k ∧ ∀ ℓ ∈ 𝒬 k, (eRow k i).1.1 ℓ = 0 := ⟨k, rfl, (eRow k i).2⟩
  have key : ∀ (k₀ : Fin Kg) (hk : 𝒬 k₀ = 𝒬 k) (pf : ∀ ℓ ∈ 𝒬 k₀, (eRow k i).1.1 ℓ = 0),
      (b * Kg + k₀) * N0 L m + ((eRow k₀).symm ⟨(eRow k i).1, pf⟩ : ℕ)
        = (b * Kg + k) * N0 L m + i := by
    intro k₀ hk pf
    obtain rfl := hinj hk
    simp
  unfold tileX
  rw [dif_pos h]
  simp only [key _ h.choose_spec.1]

lemma tileY_apply {N L m Kg : ℕ} (Y : Matrix (Fin (4 ^ m)) (Fin N) ℤ)
    (eD : Fin (4 ^ m) ≃ InIdx m) (𝒬 : Fin Kg → Finset (Fin L)) (hinj : Function.Injective 𝒬)
    (eCol : ∀ k, Fin (N0 L m) ≃ BCol L m (𝒬 k)) (b : ℕ) (k : Fin Kg) (j : Fin (N0 L m))
    (x : InIdx m) :
    tileY Y eD 𝒬 eCol b (𝒬 k) x (eCol k j).1
      = if hn : (b * Kg + k) * N0 L m + j < N then Y (eD.symm x) ⟨_, hn⟩ else 0 := by
  classical
  have h : ∃ k₀, 𝒬 k₀ = 𝒬 k ∧ ∀ ℓ ∈ 𝒬 k, (eCol k j).1.2 ℓ = 0 := ⟨k, rfl, (eCol k j).2⟩
  have key : ∀ (k₀ : Fin Kg) (hk : 𝒬 k₀ = 𝒬 k) (pf : ∀ ℓ ∈ 𝒬 k₀, (eCol k j).1.2 ℓ = 0),
      (b * Kg + k₀) * N0 L m + ((eCol k₀).symm ⟨(eCol k j).1, pf⟩ : ℕ)
        = (b * Kg + k) * N0 L m + j := by
    intro k₀ hk pf
    obtain rfl := hinj hk
    simp
  unfold tileY
  rw [dif_pos h]
  simp only [key _ h.choose_spec.1]

/-- The core of the query: for a read output string `w`, the low-order leaf products plus the box
values (Lemma 7.1(a)) are the sum over the contributing leaves (flattening), which is
`∑_s Mult(a_s, b_s)[w]` (the link and Lemma 7: the encodings are `Φ_τ`, `Ψ_τ`), which is the entry
of `X_{Q(w')} Y_{Q(w'')}` (Theorem 5.1). -/
lemma query_core {L m t : ℕ} (ht : t ≤ 2 * m) (Γ : Matrix (Fin m) (Fin L) (ZMod 2))
    (Δ : Matrix (Fin (L - m)) (Fin L) (ZMod 2)) (𝒢 : Finset (Finset (Fin L)))
    (hG : ∀ Q ∈ 𝒢, Good Γ Δ Q) (A : Finset (Fin L) → Matrix (RowIdx L m) (InIdx m) ℤ)
    (B : Finset (Fin L) → Matrix (InIdx m) (ColIdx L m) ℤ) (w : OutStr L) (h1 : QZ w.1 ∈ 𝒢)
    (h2 : QZ w.2 ∈ 𝒢) (g : Sq.FLeaf (L + L) → ℤ)
    (hg : ∀ τ, g τ = ∑ s ∈ Icc (-(m : ℤ)) m, encodeL (arrayA Γ Δ 𝒢 A s) (Sq.unflatLeaf τ)
      * encodeR (arrayB Γ Δ 𝒢 B s) (Sq.unflatLeaf τ)) :
    ∑ τ ∈ Sq.lowLeaves (2 * m) t (Sq.flatOut w), g τ
        + ∑ V ∈ Sq.Vsets (2 * m) t (Sq.flatOut w), ∑ π ∈ Sq.BV (Sq.flatOut w) V, Sq.Cube.val g π
      = (A (QZ w.1) * B (QZ w.2)) (iotaZ w.1, colSum Δ (SZ w.2)) (colSum Δ (SZ w.1), iotaZ w.2) := by
  have hc1 : (QZ w.1).card = m := (hG _ h1).1
  have hc2 : (QZ w.2).card = m := (hG _ h2).1
  have H := lemma_7_1_a ht w hc1 hc2
  dsimp only at H
  rw [← H.2.2.1 g, ← theorem_5_1 Γ Δ 𝒢 hG A B w h1 h2,
    (lemma_7_1_a_link (m := m) (fun s => arrayA Γ Δ 𝒢 A s) (fun s => arrayB Γ Δ 𝒢 B s) w).1,
    sum_filter, sum_filter, ← Equiv.sum_comp (Sq.flatEquiv L)]
  refine sum_congr rfl fun τ _ => ?_
  rw [Sq.flatEquiv_apply]
  by_cases hτ : Contributes τ w
  · rw [if_pos ((Sq.contrib_flat τ w).1 hτ), if_pos hτ, hg, unflat_flat]
    refine sum_congr rfl fun s _ => ?_
    rw [((lemma_7_squared (arrayA Γ Δ 𝒢 A s) (arrayB Γ Δ 𝒢 B s)).2.2 τ).1,
      ((lemma_7_squared (arrayA Γ Δ 𝒢 A s) (arrayB Γ Δ 𝒢 B s)).2.2 τ).2]
  · rw [if_neg (fun h => hτ ((Sq.contrib_flat τ w).2 h)), if_neg hτ]

theorem theorem_7_2_query : Theorem_7_2_query := by
  intro N L m Kg hKg t ht Γ Δ 𝒬 hinj hgood eD eRow eCol X Y I J
  have hN0 : 0 < N0 L m := pow_pos (by norm_num) (L - m)
  set k : Fin Kg := ⟨((I : ℕ) / N0 L m) % Kg, Nat.mod_lt _ hKg⟩ with hk
  set k' : Fin Kg := ⟨((J : ℕ) / N0 L m) % Kg, Nat.mod_lt _ hKg⟩ with hk'
  set i : Fin (N0 L m) := ⟨(I : ℕ) % N0 L m, Nat.mod_lt _ hN0⟩ with hi
  set j : Fin (N0 L m) := ⟨(J : ℕ) % N0 L m, Nat.mod_lt _ hN0⟩ with hj
  set r := (eRow k i).1 with hr
  set c := (eCol k' j).1 with hc
  set w : OutStr L := (zString (𝒬 k) (DeltaInv Δ (𝒬 k) c.1) r.1,
    zString (𝒬 k') (DeltaInv Δ (𝒬 k') r.2) c.2) with hw
  set 𝒢 := univ.image 𝒬 with h𝒢
  set A := tileX X eD 𝒬 eRow ((I : ℕ) / (Kg * N0 L m)) with hA
  set B := tileY Y eD 𝒬 eCol ((J : ℕ) / (Kg * N0 L m)) with hB
  have hG : ∀ Q ∈ 𝒢, Good Γ Δ Q := by
    intro Q hQ
    obtain ⟨k₀, -, rfl⟩ := mem_image.1 hQ
    exact hgood k₀
  have hS1 := DeltaInv_spec (hgood k) c.1
  have hS2 := DeltaInv_spec (hgood k') r.2
  have hq1 : QZ w.1 = 𝒬 k := QZ_mkZ _ _ _
  have hq2 : QZ w.2 = 𝒬 k' := QZ_mkZ _ _ _
  have hι1 : iotaZ w.1 = r.1 := iotaZ_mkZ _ _ _ (eRow k i).2
  have hι2 : iotaZ w.2 = c.2 := iotaZ_mkZ _ _ _ (eCol k' j).2
  have hs1 : SZ w.1 = DeltaInv Δ (𝒬 k) c.1 := SZ_mkZ _ _ _ hS1.1
  have hs2 : SZ w.2 = DeltaInv Δ (𝒬 k') r.2 := SZ_mkZ _ _ _ hS2.1
  have h1 : QZ w.1 ∈ 𝒢 := by rw [hq1]; exact mem_image_of_mem _ (mem_univ _)
  have h2 : QZ w.2 ∈ 𝒢 := by rw [hq2]; exact mem_image_of_mem _ (mem_univ _)
  have key := query_core ht Γ Δ 𝒢 hG A B w h1 h2 _ (fun _ => rfl)
  unfold query
  dsimp only
  rw [key, hq1, hq2, hι1, hι2, hs1, hs2, hS1.2, hS2.2, Matrix.mul_apply, Matrix.mul_apply,
    ← Equiv.sum_comp eD.symm]
  refine sum_congr rfl fun x _ => ?_
  have eA : A (𝒬 k) (r.1, r.2) x = X I (eD.symm x) := by
    rw [hA, show ((r.1, r.2) : RowIdx L m) = (eRow k i).1 from rfl,
      tileX_apply X eD 𝒬 hinj eRow _ k i]
    exact dite_eq_of_eq _ I (tile_decomp I Kg (N0 L m)) (fun I => X I (eD.symm x))
  have eB : B (𝒬 k') x (c.1, c.2) = Y (eD.symm x) J := by
    rw [hB, show ((c.1, c.2) : ColIdx L m) = (eCol k' j).1 from rfl,
      tileY_apply Y eD 𝒬 hinj eCol _ k' j]
    exact dite_eq_of_eq _ J (tile_decomp J Kg (N0 L m)) (fun J => Y (eD.symm x) J)
  rw [eA, eB]

theorem theorem_7_2_labels : Theorem_7_2_labels := by
  intro L m Γ Δ Q hQ
  have hm : L - Q.card = L - m := by rw [hQ.1]
  have hrow : Fintype.card (BRow L m Q) = N0 L m := by
    rw [Fintype.card_subtype, show (univ.filter fun r : RowIdx L m => ∀ ℓ ∈ Q, r.1 ℓ = 0)
        = (univ.filter fun ι : Fin L → Fin 2 => ∀ ℓ ∈ Q, ι ℓ = 0) ×ˢ univ by ext; simp,
      card_product, card_masked, card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, hm,
      N0, ← mul_pow]
    norm_num
  have hcol : Fintype.card (BCol L m Q) = N0 L m := by
    rw [Fintype.card_subtype, show (univ.filter fun c : ColIdx L m => ∀ ℓ ∈ Q, c.2 ℓ = 0)
        = univ ×ˢ (univ.filter fun ι : Fin L → Fin 2 => ∀ ℓ ∈ Q, ι ℓ = 0) by ext; simp,
      card_product, card_masked, card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card, hm,
      N0, ← mul_pow]
    norm_num
  have hin : Fintype.card (InIdx m) = 4 ^ m := by
    simp [InIdx, Fintype.card_prod, Fintype.card_fun, ZMod.card, ← mul_pow]
  refine ⟨⟨(Fintype.equivFinOfCardEq hrow).symm⟩, ⟨(Fintype.equivFinOfCardEq hcol).symm⟩,
    ⟨(Fintype.equivFinOfCardEq hin).symm⟩⟩

end ThinMatrixProducts

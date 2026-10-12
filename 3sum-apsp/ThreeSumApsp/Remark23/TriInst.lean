/-
Copyright (c) 2026 Ruhollah Majdoddin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements

/-!
# Remark 23 (3XOR): Exact-XOR-Triangle with parts of any finite types

The proofs of the note's Lemma 7 and Theorem 8 are written for an instance `TriInst A B C d` whose
three parts are arbitrary finite types.  The statements are about a `TriangleInstance (Vec d) n`,
whose parts are `Fin n`; `TriInst.ofTriangleInstance` turns the one into the other, with the same
weights, and the lemmas of this file say that `S`, `HasZeroTriangle` and `Z` agree.
-/

@[expose] public section

namespace ThreeSumApsp.Remark23

/-- An instance of Exact-XOR-Triangle with parts `A`, `B`, `C`: weights in `F^d` on the edges of
the complete tripartite graph. -/
structure TriInst (A B C : Type*) (d : ℕ) where
  /-- The weight `w(a,b)`. -/
  wab : A → B → Vec d
  /-- The weight `w(b,c)`. -/
  wbc : B → C → Vec d
  /-- The weight `w(a,c)`. -/
  wac : A → C → Vec d

namespace TriInst

variable {A B C : Type*} {d : ℕ}

/-- `S(a,b,c) := w(a,b) ⊕ w(b,c) ⊕ w(a,c)`. -/
def S (I : TriInst A B C d) (a : A) (b : B) (c : C) : Vec d := I.wab a b + I.wbc b c + I.wac a c

/-- There is a zero triangle. -/
def HasZeroTriangle (I : TriInst A B C d) : Prop := ∃ a b c, I.S a b c = 0

/-- `Z(G)`: the triples that the linear map `G` sends to zero. -/
noncomputable def Z [Fintype A] [Fintype B] [Fintype C] {q : ℕ} (I : TriInst A B C d)
    (G : Vec d →ₗ[ZMod 2] Vec q) : ℕ :=
  open Classical in
  (Finset.univ.filter fun t : A × B × C => G (I.S t.1 t.2.1 t.2.2) = 0).card

/-- The instance `T`, with its parts `Fin n`. -/
def ofTriangleInstance {n : ℕ} (T : TriangleInstance (Vec d) n) : TriInst (Fin n) (Fin n) (Fin n) d where
  wab := T.wAB
  wbc := T.wBC
  wac := T.wAC

variable {n : ℕ} (T : TriangleInstance (Vec d) n)

@[simp] theorem S_ofTriangleInstance (a b c : Fin n) : (ofTriangleInstance T).S a b c = T.S a b c :=
  rfl

theorem hasZeroTriangle_ofTriangleInstance :
    (ofTriangleInstance T).HasZeroTriangle ↔ T.HasZeroTriangle :=
  Iff.rfl

theorem Z_ofTriangleInstance {q : ℕ} (G : Vec d →ₗ[ZMod 2] Vec q) :
    (ofTriangleInstance T).Z G = Remark23.Z T G := by
  unfold Z Remark23.Z
  congr 1

end TriInst

end ThreeSumApsp.Remark23

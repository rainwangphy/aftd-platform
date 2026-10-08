import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSelection
import AFTD.Kb.Tcs.CslibGoodSelection
import AFTD.Kb.Tcs.CslibInfVSet
import AFTD.Kb.Tcs.CslibGoodSelectionSeq

/-!
# Cslib.goodSelection_seq_prop

Topic: combinatorics   Node: 854197d29576

Provenance: formalization of a published result. Source: CSLib, `Cslib.goodSelection_seq_prop`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At every step, the `goodSelection_seq` makes a good selection and there are always infinitely many vertices remaining to be selected.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {Vertex Color : Type*} [Finite Color] (color : Finset Vertex → Color) in
variable [Infinite Vertex] in
/-- At every step, the `goodSelection_seq` makes a good selection and there are always infinitely many vertices remaining to be selected. -/
lemma Cslib.goodSelection_seq_prop (n : ℕ) :
    ∃ ivs : InfVSet Vertex, GoodSelection color ivs (goodSelection_seq color n) ∧
      (ivs.set = ⋂ m < n, (goodSelection_seq color m).vs.set) := by
  induction n
  case zero =>
    use (InfVSet.mk univ infinite_univ)
    simp
    grind [goodSelection_seq]
  case succ n h_ind =>
    obtain ⟨_, _, h_eq⟩ := h_ind
    use (goodSelection_seq color n).vs
    constructor
    · grind [goodSelection_seq]
    · have h1 (m : ℕ) : m < n + 1 ↔ m < n ∨ m = n := by grind
      simp [h1, iInter_or, iInter_inter_distrib, ← h_eq]
      grind [GoodSelection]

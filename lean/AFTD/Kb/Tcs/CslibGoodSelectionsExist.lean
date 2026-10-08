import AFTD.Prelude
import AFTD.Kb.Tcs.CslibInfVSet
import AFTD.Kb.Tcs.CslibSelection
import AFTD.Kb.Tcs.CslibGoodSelectionSeq
import AFTD.Kb.Tcs.CslibGoodSelection
import AFTD.Kb.Tcs.CslibGoodSelectionSeqProp

/-!
# Cslib.good_selections_exist

Topic: combinatorics   Node: 8a69396032c3

Provenance: formalization of a published result. Source: CSLib, `Cslib.good_selections_exist`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

There exist an infinite sequence `vs` of vertex sets, an infinite sequence `v` of vertices, and an infinite sequence `c` of colors such that each `vs n` is a subset of the intersection of all previous `vs m`s, each `v n` belongs to the intersection of all previous `vs m`s but not to `vs n`, and the edges between `v n` and all vertices in `vs n` has the same color `c n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {Vertex Color : Type*} [Finite Color] (color : Finset Vertex → Color) in
variable [Infinite Vertex] in
open scoped Classical in
/-- There exist an infinite sequence `vs` of vertex sets, an infinite sequence `v` of vertices, and an infinite sequence `c` of colors such that each `vs n` is a subset of the intersection of all previous `vs m`s, each `v n` belongs to the intersection of all previous `vs m`s but not to `vs n`, and the edges between `v n` and all vertices in `vs n` has the same color `c n`. -/
lemma Cslib.good_selections_exist :
    ∃ vs : ℕ → Set Vertex, ∃ v : ℕ → Vertex, ∃ c : ℕ → Color,
    ∀ n, vs n ⊆ (⋂ m < n, vs m) ∧ v n ∈ (⋂ m < n, vs m) \ (vs n) ∧
      ∀ u ∈ vs n, color {v n, u} = c n := by
  use (fun k ↦ (goodSelection_seq color k).vs.set)
  use (fun k ↦ (goodSelection_seq color k).v)
  use (fun k ↦ (goodSelection_seq color k).c)
  intro n
  obtain ⟨ivs, h_ivs, h_eq⟩ := goodSelection_seq_prop color n
  rw [← h_eq]
  exact h_ivs

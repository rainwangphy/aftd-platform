import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSelection
import AFTD.Kb.Tcs.CslibGoodSelection
import AFTD.Kb.Tcs.CslibGoodSelectionExists
import AFTD.Kb.Tcs.CslibInfVSet

/-!
# Cslib.goodSelection_seq

Topic: combinatorics   Node: 91a268275766

Provenance: formalization of a published result. Source: CSLib, `Cslib.goodSelection_seq`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Starting from the infinite set of all vertices, inductively make an infinite sequence of good selections.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {Vertex Color : Type*} [Finite Color] (color : Finset Vertex → Color) in
variable [Infinite Vertex] in
/-- Starting from the infinite set of all vertices, inductively make an infinite sequence of good selections. -/
noncomputable def Cslib.goodSelection_seq : ℕ → Selection Vertex Color
  | 0 => Classical.choose (goodSelection_exists color (InfVSet.mk univ infinite_univ))
  | n + 1 => Classical.choose (goodSelection_exists color (goodSelection_seq n).vs)

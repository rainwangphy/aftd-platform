import AFTD.Prelude
import AFTD.Kb.Tcs.CslibInfVSet
import AFTD.Kb.Tcs.CslibSelection

/-!
# Cslib.GoodSelection

Topic: combinatorics   Node: 0f8eaf90efb9

Provenance: formalization of a published result. Source: CSLib, `Cslib.GoodSelection`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A "good selection" `S` selects an infinite subset `S.vs` of an infinite vertex set `ivs` and a distinguished vertex `S.v` in `ivs` but not in `S.vs`, and makes sure that the edges between `S.v` and all vertices in `S.vs` have the same color `S.c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {Vertex Color : Type*} [Finite Color] (color : Finset Vertex → Color) in
open scoped Classical in
/-- A "good selection" `S` selects an infinite subset `S.vs` of an infinite vertex set `ivs` and a distinguished vertex `S.v` in `ivs` but not in `S.vs`, and makes sure that the edges between `S.v` and all vertices in `S.vs` have the same color `S.c`. -/
def Cslib.GoodSelection (ivs : InfVSet Vertex) (S : Selection Vertex Color) : Prop :=
  S.vs.set ⊆ ivs.set ∧ S.v ∈ ivs.set \ S.vs.set ∧ ∀ u ∈ S.vs.set, color {S.v, u} = S.c

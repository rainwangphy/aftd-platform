import AFTD.Prelude
import AFTD.Kb.Tcs.CslibInfVSet
import AFTD.Kb.Tcs.CslibSelection
import AFTD.Kb.Tcs.CslibGoodSelection
import AFTD.Kb.Tcs.CslibInfinitePigeonholePrinciple

/-!
# Cslib.goodSelection_exists

Topic: combinatorics   Node: f05dc1999e0f

Provenance: formalization of a published result. Source: CSLib, `Cslib.goodSelection_exists`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given any infinite vertex set, a good selection from it always exists.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
variable {Vertex Color : Type*} [Finite Color] (color : Finset Vertex → Color) in
/-- Given any infinite vertex set, a good selection from it always exists. -/
lemma Cslib.goodSelection_exists (ivs : InfVSet Vertex) :
    ∃ S : Selection Vertex Color, GoodSelection color ivs S := by
  classical
  obtain ⟨v, h_v⟩ := Set.Infinite.nonempty ivs.inf
  let f u := color {v, u}
  obtain ⟨c, vs, h_inf, h_vs, h_col⟩ := infinite_pigeonhole_principle f <|
    Set.Infinite.sdiff ivs.inf (finite_singleton v)
  simp only [subset_sdiff] at h_vs
  let ivs' := InfVSet.mk vs h_inf
  use {vs := ivs', v := v, c := c}
  grind [GoodSelection]

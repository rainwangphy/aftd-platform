import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceEqOfApply
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat

/-!
# Space.vadd_transitive

Topic: classical_mechanics   Node: 8d753a9a9154

Provenance: formalization of a published result. Source: Physlib, `Space.vadd_transitive`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.vadd_transitive
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma Space.vadd_transitive {d} (s1 s2 : Space d) :
    ∃ v : EuclideanSpace ℝ (Fin d), v +ᵥ s1 = s2 := by
  use WithLp.toLp 2 fun i => s2 i - s1 i
  ext i
  simp

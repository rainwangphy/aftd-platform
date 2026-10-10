import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat

/-!
# Space.instVAddEuclideanSpaceRealFin

Topic: classical_mechanics   Node: 4f1b95806155

Provenance: formalization of a published result. Source: Physlib, `Space.instVAddEuclideanSpaceRealFin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.instVAddEuclideanSpaceRealFin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
noncomputable instance Space.instVAddEuclideanSpaceRealFin : VAdd (EuclideanSpace ℝ (Fin d)) (Space d) where
  vadd v s := ⟨fun i => v i + s.val i⟩

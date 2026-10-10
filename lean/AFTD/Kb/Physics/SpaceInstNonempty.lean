import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal

/-!
# Space.instNonempty

Topic: classical_mechanics   Node: 3d7c7319feaf

Provenance: formalization of a published result. Source: Physlib, `Space.instNonempty`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.instNonempty
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Space.instNonempty {d} : Nonempty (Space d) := Nonempty.intro
  ⟨fun _ => Classical.choice instNonemptyOfInhabited⟩

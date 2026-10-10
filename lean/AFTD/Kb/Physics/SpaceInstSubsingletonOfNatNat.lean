import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceEqOfApply
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty

/-!
# Space.instSubsingletonOfNatNat

Topic: classical_mechanics   Node: 60f0e11b8a32

Provenance: formalization of a published result. Source: Physlib, `Space.instSubsingletonOfNatNat`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.instSubsingletonOfNatNat
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Space.instSubsingletonOfNatNat : Subsingleton (Space 0) := Subsingleton.intro <| fun _ _ =>
  eq_of_apply <| fun i => Fin.elim0 i

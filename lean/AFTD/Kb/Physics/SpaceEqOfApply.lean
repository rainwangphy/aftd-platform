import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceEqOfVal
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal

/-!
# Space.eq_of_apply

Topic: classical_mechanics   Node: 7f9e28474c54

Provenance: formalization of a published result. Source: Physlib, `Space.eq_of_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.eq_of_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[ext]
lemma Space.eq_of_apply {d} {p q : Space d}
    (h : ∀ i : Fin d, p i = q i) : p = q := by
  apply eq_of_val
  funext i
  exact h i

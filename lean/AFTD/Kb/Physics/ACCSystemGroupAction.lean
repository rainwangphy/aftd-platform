import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# ACCSystemGroupAction

Topic: quantum_field_theory   Node: ca3e0db8bc52

Provenance: formalization of a published result. Source: Physlib, `ACCSystemGroupAction`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/GroupActions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of a group action on a system of charges is defined as a representation on the vector spaces of charges under which the anomaly equations are invariant.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type of a group action on a system of charges is defined as a representation on the vector spaces of charges under which the anomaly equations are invariant. -/
structure ACCSystemGroupAction (χ : ACCSystem) where
  /-- The underlying type of the group. -/
  group : Type
  /-- An instance given the `group` component the structure of a `Group`. -/
  groupInst : Group group
  /-- The representation of group acting on the vector space of charges. -/
  rep : Representation ℚ group χ.Charges
  /-- The invariance of the linear ACCs under the group action. -/
  linearInvariant : ∀ i g S, χ.linearACCs i (rep g S) = χ.linearACCs i S
  /-- The invariance of the quadratic ACCs under the group action. -/
  quadInvariant : ∀ i g S, (χ.quadraticACCs i) (rep g S) = (χ.quadraticACCs i) S
  /-- The invariance of the cubic ACC under the group action. -/
  cubicInvariant : ∀ g S, χ.cubicACC (rep g S) = χ.cubicACC S

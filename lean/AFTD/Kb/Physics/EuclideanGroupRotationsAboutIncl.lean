import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAbout
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.RotationsAbout.incl

Topic: classical_mechanics   Node: 38604ed608ca

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.RotationsAbout.incl`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of rotations about `p` into the Euclidean group.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- The inclusion of rotations about `p` into the Euclidean group. -/
noncomputable def EuclideanGroup.RotationsAbout.incl : RotationsAbout p →* EuclideanGroup n :=
  (RotationsAbout p).subtype

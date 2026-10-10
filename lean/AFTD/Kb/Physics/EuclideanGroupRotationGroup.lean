import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupSpecialEuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOriginStabilizer
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.RotationGroup

Topic: classical_mechanics   Node: 2c8dce07ae0d

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.RotationGroup`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Rotation Group is the subgroup of E(n) consisting of rotations about the origin: elements with `det = 1` (orientation-preserving) and `translation = 0` (origin-fixing).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Rotation Group is the subgroup of E(n) consisting of rotations about the origin: elements with `det = 1` (orientation-preserving) and `translation = 0` (origin-fixing). -/
noncomputable def EuclideanGroup.RotationGroup (n : ℕ) : Subgroup (EuclideanGroup n) :=
  SpecialEuclideanGroup n ⊓ OriginStabilizer n

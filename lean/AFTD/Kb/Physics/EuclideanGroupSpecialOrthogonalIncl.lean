import AFTD.Prelude

/-!
# EuclideanGroup.specialOrthogonal.incl

Topic: classical_mechanics   Node: 82e29a92e023

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.specialOrthogonal.incl`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Rotations are members of special orthogonal groups and can be viewed as members of orthogonal groups.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- Rotations are members of special orthogonal groups and can be viewed as members of orthogonal groups. -/
def EuclideanGroup.specialOrthogonal.incl (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ →* Matrix.orthogonalGroup (Fin n) ℝ :=
  Submonoid.inclusion Matrix.specialUnitaryGroup_le_unitaryGroup

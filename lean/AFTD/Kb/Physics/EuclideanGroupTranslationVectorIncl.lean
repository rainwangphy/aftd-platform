import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.translationVector.incl

Topic: classical_mechanics   Node: 53c9563873fe

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.translationVector.incl`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MonoidHom including a translation vector into the Euclidean Group.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- MonoidHom including a translation vector into the Euclidean Group. -/
def EuclideanGroup.translationVector.incl (n : ℕ) :
    Multiplicative (EuclideanSpace ℝ (Fin n)) →* EuclideanGroup n where
  toFun v := ⟨v.toAdd, 1⟩
  map_one' := by rfl
  map_mul' x y := by
    refine EuclideanGroup.ext ?_ ?_
    · show Multiplicative.toAdd (x * y) =
        Multiplicative.toAdd x +
          (1 : Matrix.orthogonalGroup (Fin n) ℝ) • Multiplicative.toAdd y
      simp
    · show 1 = 1 * 1
      simp [mul_one]

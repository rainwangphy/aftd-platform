import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.BiLinearSymmMapSmul1
import AFTD.Kb.Physics.BiLinearSymmMapSmul2
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun

/-!
# BiLinearSymm.toHomogeneousQuad

Topic: classical_mechanics   Node: 243e367fdf27

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.toHomogeneousQuad`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The homogeneous quadratic equation obtainable from a bilinear function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BiLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
/-- The homogeneous quadratic equation obtainable from a bilinear function. -/
@[simps!]
def BiLinearSymm.toHomogeneousQuad {V : Type} [AddCommMonoid V] [Module ℚ V]
    (τ : BiLinearSymm V) : HomogeneousQuadratic V where
  toFun S := τ S S
  map_smul' a S := by
    simp only [τ.map_smul₁, τ.map_smul₂, smul_eq_mul]
    grind

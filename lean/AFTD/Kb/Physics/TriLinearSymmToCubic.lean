import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmMapSmul1
import AFTD.Kb.Physics.TriLinearSymmMapSmul2
import AFTD.Kb.Physics.TriLinearSymmMapSmul3
import AFTD.Kb.Physics.HomogeneousCubicInstFun

/-!
# TriLinearSymm.toCubic

Topic: classical_mechanics   Node: 0aa3fcfc9fe0

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.toCubic`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The homogeneous cubic equation obtainable from a symmetric trilinear function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
/-- The homogeneous cubic equation obtainable from a symmetric trilinear function. -/
@[simps!]
def TriLinearSymm.toCubic {charges : Type} [AddCommMonoid charges] [Module ℚ charges]
    (τ : TriLinearSymm charges) : HomogeneousCubic charges where
  toFun S := τ S S S
  map_smul' a S := by
    simp only [smul_eq_mul]
    rw [τ.map_smul₁, τ.map_smul₂, τ.map_smul₃]
    grind

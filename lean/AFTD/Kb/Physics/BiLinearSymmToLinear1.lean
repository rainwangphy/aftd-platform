import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.BiLinearSymmMapSmul1
import AFTD.Kb.Physics.BiLinearSymmMapAdd1

/-!
# BiLinearSymm.toLinear₁

Topic: classical_mechanics   Node: c8a55fd68b9d

Provenance: formalization of a published result. Source: Physlib, `BiLinearSymm.toLinear₁`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixing the second input vectors, the resulting linear map.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BiLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
/-- Fixing the second input vectors, the resulting linear map. -/
def BiLinearSymm.toLinear₁ (f : BiLinearSymm V) (T : V) : V →ₗ[ℚ] ℚ where
  toFun S := f S T
  map_add' S1 S2 := map_add₁ f S1 S2 T
  map_smul' a S := by simp [f.map_smul₁]

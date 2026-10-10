import AFTD.Prelude
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmMapSmul1
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmMapAdd1

/-!
# TriLinearSymm.toLinear₁

Topic: classical_mechanics   Node: 7dd379e3db20

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm.toLinear₁`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixing the second and third input vectors, the resulting linear map.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TriLinearSymm in
open BigOperators in
variable {V : Type} [AddCommMonoid V] [Module ℚ V] in
/-- Fixing the second and third input vectors, the resulting linear map. -/
def TriLinearSymm.toLinear₁ (f : TriLinearSymm V) (T L : V) : V →ₗ[ℚ] ℚ where
  toFun S := f S T L
  map_add' S1 S2 := map_add₁ f S1 S2 T L
  map_smul' a S := by
    simp only [f.map_smul₁]
    rfl

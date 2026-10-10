import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SU2OfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6UnitaryOfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6UnitaryOfRootCoe

/-!
# StandardModel.gaugeGroupℤ₆SU2OfRoot_toEuclideanLin_apply

Topic: quantum_field_theory   Node: d08495936d61

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₆SU2OfRoot_toEuclideanLin_apply`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.gaugeGroupℤ₆SU2OfRoot_toEuclideanLin_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
lemma StandardModel.gaugeGroupℤ₆SU2OfRoot_toEuclideanLin_apply (α : rootsOfUnity 6 ℂ)
    (v : EuclideanSpace ℂ (Fin 2)) :
    (gaugeGroupℤ₆SU2OfRoot α).1.toEuclideanLin v = star ((α : ℂˣ) : ℂ) ^ 3 • v := by
  simp [gaugeGroupℤ₆SU2OfRoot, Matrix.scalar_apply, toLpLin_apply]

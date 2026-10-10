import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6SU3OfRoot

/-!
# StandardModel.gaugeGroupℤ₆SU3OfRoot_eq_mul_id

Topic: quantum_field_theory   Node: e079abdbfab8

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₆SU3OfRoot_eq_mul_id`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.gaugeGroupℤ₆SU3OfRoot_eq_mul_id
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
lemma StandardModel.gaugeGroupℤ₆SU3OfRoot_eq_mul_id (α : rootsOfUnity 6 ℂ) :
    (gaugeGroupℤ₆SU3OfRoot α).1 = ((α : ℂˣ) : ℂ) ^ 2 • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gaugeGroupℤ₆SU3OfRoot]

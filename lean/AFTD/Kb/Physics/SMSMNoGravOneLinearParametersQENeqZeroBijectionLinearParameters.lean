import AFTD.Prelude
import AFTD.Kb.Physics.SMSMNoGravOneLinearParameters
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZero
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroToLinearParameters
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroTolinearParametersQNeqZero
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroExt
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersExt

/-!
# SM.SMNoGrav.One.linearParametersQENeqZero.bijectionLinearParameters

Topic: quantum_field_theory   Node: f0ba558d2045

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParametersQENeqZero.bijectionLinearParameters`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A bijection between the type `linearParametersQENeqZero` and linear parameters with `Q'` and `E'` non-zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- A bijection between the type `linearParametersQENeqZero` and linear parameters with `Q'` and `E'` non-zero. -/
@[simps!]
def SM.SMNoGrav.One.linearParametersQENeqZero.bijectionLinearParameters :
    linearParametersQENeqZero ≃ {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0} where
  toFun := toLinearParameters
  invFun := tolinearParametersQNeqZero
  left_inv S := by
    have hvw := S.hvw
    have hQ := S.hx
    apply linearParametersQENeqZero.ext
    · rfl
    · simp only [tolinearParametersQNeqZero_v, toLinearParameters_coe_Y, toLinearParameters_coe_Q',
      toLinearParameters_coe_E']
      field_simp
      ring
    · simp only [tolinearParametersQNeqZero_w, toLinearParameters_coe_Y, toLinearParameters_coe_Q',
        toLinearParameters_coe_E']
      field_simp
      ring
  right_inv S := by
    apply Subtype.ext
    have hQ := S.2.1
    have hE := S.2.2
    apply linearParameters.ext
    · rfl
    · simp only [ne_eq, toLinearParameters_coe_Y, tolinearParametersQNeqZero_x,
      tolinearParametersQNeqZero_v, tolinearParametersQNeqZero_w]
      field_simp
      ring_nf
      field_simp [hQ, hE]
    · simp only [ne_eq, toLinearParameters_coe_E', tolinearParametersQNeqZero_x,
      tolinearParametersQNeqZero_v, tolinearParametersQNeqZero_w]
      field_simp
      ring_nf
      field_simp [hQ, hE]

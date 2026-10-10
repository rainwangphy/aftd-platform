import AFTD.Prelude
import AFTD.Kb.Physics.SMSMNoGravOneLinearParameters
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZero
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroToLinearParameters
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirStarComp
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolAccQuadAlpha1Alpha2Zero

/-!
# SM.SMNoGrav.One.linearParametersQENeqZero.tolinearParametersQNeqZero

Topic: quantum_field_theory   Node: ccd5d00ff4cd

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParametersQENeqZero.tolinearParametersQNeqZero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A map from `linearParameters` to `linearParametersQENeqZero` in the special case when `Q'` and `E'` of the linear parameters are non-zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- A map from `linearParameters` to `linearParametersQENeqZero` in the special case when `Q'` and `E'` of the linear parameters are non-zero. -/
@[simps!]
def SM.SMNoGrav.One.linearParametersQENeqZero.tolinearParametersQNeqZero (S : {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0}) :
    linearParametersQENeqZero :=
  ⟨S.1.Q', - (3 * S.1.Q' + S.1.Y) / S.1.E', - (3 * S.1.Q' - S.1.Y)/ S.1.E', S.2.1,
    by
      simp only [ne_eq, neg_add_rev, neg_sub]
      field_simp
      ring_nf
      simp only [neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, or_false]
      simpa using S.2⟩

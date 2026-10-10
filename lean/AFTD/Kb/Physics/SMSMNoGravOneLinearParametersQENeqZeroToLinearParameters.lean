import AFTD.Prelude
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZero
import AFTD.Kb.Physics.SMSMNoGravOneLinearParameters
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirStarComp
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolAccQuadAlpha1Alpha2Zero

/-!
# SM.SMNoGrav.One.linearParametersQENeqZero.toLinearParameters

Topic: quantum_field_theory   Node: 3592a4ed348c

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParametersQENeqZero.toLinearParameters`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A map from `linearParametersQENeqZero` to `linearParameters`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- A map from `linearParametersQENeqZero` to `linearParameters`. -/
@[simps!]
def SM.SMNoGrav.One.linearParametersQENeqZero.toLinearParameters (S : linearParametersQENeqZero) :
    {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0} :=
  ⟨⟨S.x, 3 * S.x * (S.v - S.w) / (S.v + S.w), - 6 * S.x / (S.v + S.w)⟩,
    by
      apply And.intro S.hx
      simp only [neg_mul, ne_eq, div_eq_zero_iff, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
        false_or]
      rw [not_or]
      exact And.intro S.hx S.hvw⟩

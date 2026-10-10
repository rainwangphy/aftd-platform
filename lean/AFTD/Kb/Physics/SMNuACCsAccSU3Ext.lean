import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMNuACCsAccSU3
import AFTD.Kb.Physics.SMNuChargesQ
import AFTD.Kb.Physics.SMNuChargesU
import AFTD.Kb.Physics.SMNuChargesD
import AFTD.Kb.Physics.SMNuACCsAccSU3Decomp
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# SMνACCs.accSU3_ext

Topic: quantum_field_theory   Node: 3845ef914935

Provenance: formalization of a published result. Source: Physlib, `SMνACCs.accSU3_ext`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Extensionality lemma for `accSU3`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνACCs in
open Nat in
open BigOperators in
open SMνCharges in
variable {n : ℕ} in
/-- Extensionality lemma for `accSU3`. -/
lemma SMνACCs.accSU3_ext {S T : (SMνCharges n).Charges}
    (hj : ∀ (j : Fin 6), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU3 S = accSU3 T := by
  rw [accSU3_decomp, accSU3_decomp]
  repeat rw [hj]

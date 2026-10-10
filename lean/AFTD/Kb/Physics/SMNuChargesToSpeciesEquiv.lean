import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMνCharges.toSpeciesEquiv

Topic: quantum_field_theory   Node: 4ff82b61a818

Provenance: formalization of a published result. Source: Physlib, `SMνCharges.toSpeciesEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An equivalence between `(SMνCharges n).charges` and `(Fin 6 → Fin n → ℚ)` splitting the charges into species.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
variable {n : ℕ} in
/-- An equivalence between `(SMνCharges n).charges` and `(Fin 6 → Fin n → ℚ)` splitting the charges into species. -/
@[simps!]
def SMνCharges.toSpeciesEquiv : (SMνCharges n).Charges ≃ (Fin 6 → Fin n → ℚ) :=
  ((Equiv.curry _ _ _).symm.trans ((@finProdFinEquiv 6 n).arrowCongr (Equiv.refl ℚ))).symm

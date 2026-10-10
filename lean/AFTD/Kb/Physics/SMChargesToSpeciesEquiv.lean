import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMCharges.toSpeciesEquiv

Topic: quantum_field_theory   Node: b25e48c8dcdd

Provenance: formalization of a published result. Source: Physlib, `SMCharges.toSpeciesEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An equivalence between the set `(SMCharges n).charges` and the set `(Fin 5 → Fin n → ℚ)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
variable {n : ℕ} in
/-- An equivalence between the set `(SMCharges n).charges` and the set `(Fin 5 → Fin n → ℚ)`. -/
@[simps!]
def SMCharges.toSpeciesEquiv : (SMCharges n).Charges ≃ (Fin 5 → Fin (SMSpecies n).numberCharges → ℚ) :=
  ((Equiv.curry _ _ _).symm.trans ((@finProdFinEquiv 5
    (SMSpecies n).numberCharges).arrowCongr (Equiv.refl ℚ))).symm

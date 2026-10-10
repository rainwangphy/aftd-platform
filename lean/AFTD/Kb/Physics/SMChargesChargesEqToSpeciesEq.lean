import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMCharges.charges_eq_toSpecies_eq

Topic: quantum_field_theory   Node: 701433ef1ca5

Provenance: formalization of a published result. Source: Physlib, `SMCharges.charges_eq_toSpecies_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMCharges.charges_eq_toSpecies_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open Nat in
open BigOperators in
variable {n : ℕ} in
lemma SMCharges.charges_eq_toSpecies_eq (S T : (SMCharges n).Charges) :
    S = T ↔ ∀ i, toSpecies i S = toSpecies i T := by
  refine Iff.intro (fun a i => congrArg (⇑(toSpecies i)) a) (fun h => ?_)
  apply toSpeciesEquiv.injective
  exact (Set.eqOn_univ (toSpeciesEquiv S) (toSpeciesEquiv T)).mp fun ⦃x⦄ _ => h x

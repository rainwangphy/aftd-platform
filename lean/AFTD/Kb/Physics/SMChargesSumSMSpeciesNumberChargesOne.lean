import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMCharges.sum_SMSpecies_numberCharges_one

Topic: quantum_field_theory   Node: 05bdee012cbd

Provenance: formalization of a published result. Source: Physlib, `SMCharges.sum_SMSpecies_numberCharges_one`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMCharges.sum_SMSpecies_numberCharges_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
lemma SMCharges.sum_SMSpecies_numberCharges_one {M} [AddCommMonoid M]
    (f : Fin (SMSpecies 1).numberCharges → M) :
    ∑ i, f i = f ⟨0, by simp⟩ := by
  change ∑ (i : Fin 1), f i = _
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
  rfl

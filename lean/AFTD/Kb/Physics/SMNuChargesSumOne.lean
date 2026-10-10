import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMνCharges.sum_one

Topic: quantum_field_theory   Node: eda0f050b3e3

Provenance: formalization of a published result. Source: Physlib, `SMνCharges.sum_one`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMνCharges.sum_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
lemma SMνCharges.sum_one  [AddCommMonoid M] (f : Fin (SMνSpecies 1).numberCharges → M) :
    ∑ i, f i = f ⟨0, by simp⟩ := by
  change  ∑ (i : Fin 1), f i = _
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton]
  rfl

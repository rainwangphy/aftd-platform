import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMCharges.sum_MSSMSpecies_numberCharges_eq_expand

Topic: quantum_field_theory   Node: f4aa3c237e8f

Provenance: formalization of a published result. Source: Physlib, `MSSMCharges.sum_MSSMSpecies_numberCharges_eq_expand`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMCharges.sum_MSSMSpecies_numberCharges_eq_expand
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
lemma MSSMCharges.sum_MSSMSpecies_numberCharges_eq_expand [AddCommMonoid M]
    (f : Fin MSSMSpecies.numberCharges → M) :
    ∑ i, f i = f ⟨0, by simp⟩ + f ⟨1, by simp⟩ + f ⟨2, by simp⟩ := Fin.sum_univ_three f

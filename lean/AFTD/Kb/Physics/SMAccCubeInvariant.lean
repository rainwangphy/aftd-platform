import AFTD.Prelude
import AFTD.Kb.Physics.SMPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.SMInstGroupPermGroup
import AFTD.Kb.Physics.SMRepCharges
import AFTD.Kb.Physics.SMACCsAccCubeExt
import AFTD.Kb.Physics.SMToSpeciesSumInvariant
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SM.accCube_invariant

Topic: quantum_field_theory   Node: 05c0a24f3cf6

Provenance: formalization of a published result. Source: Physlib, `SM.accCube_invariant`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The cubic anomaly equation is invariant under family permutations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SM in
open Nat in
open Finset in
open SMCharges in
open SMACCs in
open BigOperators in
variable {n : ℕ} in
/-- The cubic anomaly equation is invariant under family permutations. -/
lemma SM.accCube_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accCube (repCharges f S) = accCube S :=
  accCube_ext (toSpecies_sum_invariant 3 f S)

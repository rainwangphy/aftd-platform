import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.MSSMChargesToSpecies
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.GameTheoryEconomics.MatrixGameToStrategicGame

/-!
# MSSMACC.B₃AsCharge

Topic: quantum_field_theory   Node: 44b490e16ade

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.B₃AsCharge`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/B3.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`B₃` is the charge which is $B-L$ in all families, but with the third family of the opposite sign.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
/-- `B₃` is the charge which is $B-L$ in all families, but with the third family of the opposite sign. -/
def MSSMACC.B₃AsCharge : MSSMACC.Charges := toSpecies.symm
  ⟨fun s => fun i =>
    match s, i with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => - 1
    | 1, 0 => - 1
    | 1, 1 => - 1
    | 1, 2 => 1
    | 2, 0 => - 1
    | 2, 1 => - 1
    | 2, 2 => 1
    | 3, 0 => - 3
    | 3, 1 => - 3
    | 3, 2 => 3
    | 4, 0 => 3
    | 4, 1 => 3
    | 4, 2 => - 3
    | 5, 0 => 3
    | 5, 1 => 3
    | 5, 2 => - 3,
  fun s =>
    match s with
    | 0 => -3
    | 1 => 3⟩

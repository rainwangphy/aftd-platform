import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismVCGMechanism

/-!
# MultipleParameterMechanism.VCGTransferMechanism

Topic: mechanism_design   Node: 2f7a4b36e9ae

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.VCGTransferMechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The underlying transfer mechanism of `VCGMechanism`. This is the object to which the generic definitions in `Transfer.lean`, such as `isQuasiLinearDSIC` and `isQuasiLinearExPostIR`, are applied.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MultipleParameterMechanism in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- The underlying transfer mechanism of `VCGMechanism`. This is the object to which the generic definitions in `Transfer.lean`, such as `isQuasiLinearDSIC` and `isQuasiLinearExPostIR`, are applied. -/
noncomputable def MultipleParameterMechanism.VCGTransferMechanism :
    MechanismWithTransfers I (fun _ => Valuation A ℝ) A ℝ where
  allocationRule := (VCGMechanism : MultipleParameterMechanism I A ℝ ℝ).allocationRule
  paymentRule := (VCGMechanism : MultipleParameterMechanism I A ℝ ℝ).paymentRule
